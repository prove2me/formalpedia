-- Prove2me | solution 1 for syracuse_descends_range_1244440_1246440
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:12.214195+00:00
-- url     : https://prove2.me/submissions/e1260a1f-6c96-4265-a319-687810318ef6

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


theorem B1867781 : Blo 1244440 1867781 := bbase (se 4 (by rfl) ⟨175104, by rfl⟩ : syracuseStep 1867781 = 350209) (by norm_num)
theorem B1400845 : Blo 1244440 1400845 := bbase (se 3 (by rfl) ⟨262658, by rfl⟩ : syracuseStep 1400845 = 525317) (by norm_num)
theorem B1867805 : Blo 1244440 1867805 := bbase (se 3 (by rfl) ⟨350213, by rfl⟩ : syracuseStep 1867805 = 700427) (by norm_num)
theorem B2990125 : Blo 1244440 2990125 := bbase (se 3 (by rfl) ⟨560648, by rfl⟩ : syracuseStep 2990125 = 1121297) (by norm_num)
theorem B1400881 : Blo 1244440 1400881 := bbase (se 2 (by rfl) ⟨525330, by rfl⟩ : syracuseStep 1400881 = 1050661) (by norm_num)
theorem B4202549 : Blo 1244440 4202549 := bbase (se 5 (by rfl) ⟨196994, by rfl⟩ : syracuseStep 4202549 = 393989) (by norm_num)
theorem B2801717 : Blo 1244440 2801717 := bbase (se 5 (by rfl) ⟨131330, by rfl⟩ : syracuseStep 2801717 = 262661) (by norm_num)
theorem B1867829 : Blo 1244440 1867829 := bbase (se 5 (by rfl) ⟨87554, by rfl⟩ : syracuseStep 1867829 = 175109) (by norm_num)
theorem B1867853 : Blo 1244440 1867853 := bbase (se 3 (by rfl) ⟨350222, by rfl⟩ : syracuseStep 1867853 = 700445) (by norm_num)
theorem B1400917 : Blo 1244440 1400917 := bbase (se 8 (by rfl) ⟨8208, by rfl⟩ : syracuseStep 1400917 = 16417) (by norm_num)
theorem B1867877 : Blo 1244440 1867877 := bbase (se 4 (by rfl) ⟨175113, by rfl⟩ : syracuseStep 1867877 = 350227) (by norm_num)
theorem B1400953 : Blo 1244440 1400953 := bbase (se 2 (by rfl) ⟨525357, by rfl⟩ : syracuseStep 1400953 = 1050715) (by norm_num)
theorem B2801789 : Blo 1244440 2801789 := bbase (se 3 (by rfl) ⟨525335, by rfl⟩ : syracuseStep 2801789 = 1050671) (by norm_num)
theorem B1867901 : Blo 1244440 1867901 := bbase (se 3 (by rfl) ⟨350231, by rfl⟩ : syracuseStep 1867901 = 700463) (by norm_num)
theorem B1867925 : Blo 1244440 1867925 := bbase (se 6 (by rfl) ⟨43779, by rfl⟩ : syracuseStep 1867925 = 87559) (by norm_num)
theorem B1400989 : Blo 1244440 1400989 := bbase (se 3 (by rfl) ⟨262685, by rfl⟩ : syracuseStep 1400989 = 525371) (by norm_num)
theorem B1867949 : Blo 1244440 1867949 := bbase (se 3 (by rfl) ⟨350240, by rfl⟩ : syracuseStep 1867949 = 700481) (by norm_num)
theorem B1401025 : Blo 1244440 1401025 := bbase (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) (by norm_num)
theorem B2801861 : Blo 1244440 2801861 := bbase (se 4 (by rfl) ⟨262674, by rfl⟩ : syracuseStep 2801861 = 525349) (by norm_num)
theorem B1867973 : Blo 1244440 1867973 := bbase (se 4 (by rfl) ⟨175122, by rfl⟩ : syracuseStep 1867973 = 350245) (by norm_num)
theorem B1867997 : Blo 1244440 1867997 := bbase (se 3 (by rfl) ⟨350249, by rfl⟩ : syracuseStep 1867997 = 700499) (by norm_num)
theorem B1401061 : Blo 1244440 1401061 := bbase (se 4 (by rfl) ⟨131349, by rfl⟩ : syracuseStep 1401061 = 262699) (by norm_num)
theorem B1868021 : Blo 1244440 1868021 := bbase (se 5 (by rfl) ⟨87563, by rfl⟩ : syracuseStep 1868021 = 175127) (by norm_num)
theorem B1401097 : Blo 1244440 1401097 := bbase (se 2 (by rfl) ⟨525411, by rfl⟩ : syracuseStep 1401097 = 1050823) (by norm_num)
theorem B2801933 : Blo 1244440 2801933 := bbase (se 3 (by rfl) ⟨525362, by rfl⟩ : syracuseStep 2801933 = 1050725) (by norm_num)
theorem B1868045 : Blo 1244440 1868045 := bbase (se 3 (by rfl) ⟨350258, by rfl⟩ : syracuseStep 1868045 = 700517) (by norm_num)
theorem B6308117 : Blo 1244440 6308117 := bbase (se 6 (by rfl) ⟨147846, by rfl⟩ : syracuseStep 6308117 = 295693) (by norm_num)
theorem B2130205 : Blo 1244440 2130205 := bbase (se 3 (by rfl) ⟨399413, by rfl⟩ : syracuseStep 2130205 = 798827) (by norm_num)
theorem B1868069 : Blo 1244440 1868069 := bbase (se 4 (by rfl) ⟨175131, by rfl⟩ : syracuseStep 1868069 = 350263) (by norm_num)
theorem B1401133 : Blo 1244440 1401133 := bbase (se 3 (by rfl) ⟨262712, by rfl⟩ : syracuseStep 1401133 = 525425) (by norm_num)
theorem B1868093 : Blo 1244440 1868093 := bbase (se 3 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 1868093 = 700535) (by norm_num)
theorem B1401169 : Blo 1244440 1401169 := bbase (se 2 (by rfl) ⟨525438, by rfl⟩ : syracuseStep 1401169 = 1050877) (by norm_num)
theorem B2802005 : Blo 1244440 2802005 := bbase (se 10 (by rfl) ⟨4104, by rfl⟩ : syracuseStep 2802005 = 8209) (by norm_num)
theorem B1868117 : Blo 1244440 1868117 := bbase (se 10 (by rfl) ⟨2736, by rfl⟩ : syracuseStep 1868117 = 5473) (by norm_num)
theorem B3154261 : Blo 1244440 3154261 := bbase (se 10 (by rfl) ⟨4620, by rfl⟩ : syracuseStep 3154261 = 9241) (by norm_num)
theorem B5390693 : Blo 1244440 5390693 := bbase (se 4 (by rfl) ⟨505377, by rfl⟩ : syracuseStep 5390693 = 1010755) (by norm_num)
theorem B1868141 : Blo 1244440 1868141 := bbase (se 3 (by rfl) ⟨350276, by rfl⟩ : syracuseStep 1868141 = 700553) (by norm_num)
theorem B1401205 : Blo 1244440 1401205 := bbase (se 5 (by rfl) ⟨65681, by rfl⟩ : syracuseStep 1401205 = 131363) (by norm_num)
theorem B1868165 : Blo 1244440 1868165 := bbase (se 4 (by rfl) ⟨175140, by rfl⟩ : syracuseStep 1868165 = 350281) (by norm_num)
theorem B1401241 : Blo 1244440 1401241 := bbase (se 2 (by rfl) ⟨525465, by rfl⟩ : syracuseStep 1401241 = 1050931) (by norm_num)
theorem B2802077 : Blo 1244440 2802077 := bbase (se 3 (by rfl) ⟨525389, by rfl⟩ : syracuseStep 2802077 = 1050779) (by norm_num)
theorem B1868189 : Blo 1244440 1868189 := bbase (se 3 (by rfl) ⟨350285, by rfl⟩ : syracuseStep 1868189 = 700571) (by norm_num)
theorem B2130349 : Blo 1244440 2130349 := bbase (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) (by norm_num)
theorem B1868213 : Blo 1244440 1868213 := bbase (se 5 (by rfl) ⟨87572, by rfl⟩ : syracuseStep 1868213 = 175145) (by norm_num)
theorem B1401277 : Blo 1244440 1401277 := bbase (se 3 (by rfl) ⟨262739, by rfl⟩ : syracuseStep 1401277 = 525479) (by norm_num)
theorem B3154373 : Blo 1244440 3154373 := bbase (se 4 (by rfl) ⟨295722, by rfl⟩ : syracuseStep 3154373 = 591445) (by norm_num)
theorem B1868237 : Blo 1244440 1868237 := bbase (se 3 (by rfl) ⟨350294, by rfl⟩ : syracuseStep 1868237 = 700589) (by norm_num)
theorem B1401313 : Blo 1244440 1401313 := bbase (se 2 (by rfl) ⟨525492, by rfl⟩ : syracuseStep 1401313 = 1050985) (by norm_num)
theorem B4202981 : Blo 1244440 4202981 := bbase (se 4 (by rfl) ⟨394029, by rfl⟩ : syracuseStep 4202981 = 788059) (by norm_num)
theorem B2802149 : Blo 1244440 2802149 := bbase (se 4 (by rfl) ⟨262701, by rfl⟩ : syracuseStep 2802149 = 525403) (by norm_num)
theorem B1868261 : Blo 1244440 1868261 := bbase (se 4 (by rfl) ⟨175149, by rfl⟩ : syracuseStep 1868261 = 350299) (by norm_num)
theorem B1868285 : Blo 1244440 1868285 := bbase (se 3 (by rfl) ⟨350303, by rfl⟩ : syracuseStep 1868285 = 700607) (by norm_num)
theorem B5677573 : Blo 1244440 5677573 := bbase (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) (by norm_num)
theorem B1401349 : Blo 1244440 1401349 := bbase (se 4 (by rfl) ⟨131376, by rfl⟩ : syracuseStep 1401349 = 262753) (by norm_num)
theorem B5677589 : Blo 1244440 5677589 := bbase (se 6 (by rfl) ⟨133068, by rfl⟩ : syracuseStep 5677589 = 266137) (by norm_num)
theorem B1868309 : Blo 1244440 1868309 := bbase (se 6 (by rfl) ⟨43788, by rfl⟩ : syracuseStep 1868309 = 87577) (by norm_num)
theorem B1401385 : Blo 1244440 1401385 := bbase (se 2 (by rfl) ⟨525519, by rfl⟩ : syracuseStep 1401385 = 1051039) (by norm_num)
theorem B2802221 : Blo 1244440 2802221 := bbase (se 3 (by rfl) ⟨525416, by rfl⟩ : syracuseStep 2802221 = 1050833) (by norm_num)
theorem B1868333 : Blo 1244440 1868333 := bbase (se 3 (by rfl) ⟨350312, by rfl⟩ : syracuseStep 1868333 = 700625) (by norm_num)
theorem B11960885 : Blo 1244440 11960885 := bbase (se 5 (by rfl) ⟨560666, by rfl⟩ : syracuseStep 11960885 = 1121333) (by norm_num)
theorem B1868357 : Blo 1244440 1868357 := bbase (se 4 (by rfl) ⟨175158, by rfl⟩ : syracuseStep 1868357 = 350317) (by norm_num)
theorem B1401421 : Blo 1244440 1401421 := bbase (se 3 (by rfl) ⟨262766, by rfl⟩ : syracuseStep 1401421 = 525533) (by norm_num)
theorem B1868381 : Blo 1244440 1868381 := bbase (se 3 (by rfl) ⟨350321, by rfl⟩ : syracuseStep 1868381 = 700643) (by norm_num)
theorem B1401457 : Blo 1244440 1401457 := bbase (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) (by norm_num)
theorem B2802293 : Blo 1244440 2802293 := bbase (se 5 (by rfl) ⟨131357, by rfl⟩ : syracuseStep 2802293 = 262715) (by norm_num)
theorem B1868405 : Blo 1244440 1868405 := bbase (se 5 (by rfl) ⟨87581, by rfl⟩ : syracuseStep 1868405 = 175163) (by norm_num)
theorem B4727429 : Blo 1244440 4727429 := bbase (se 4 (by rfl) ⟨443196, by rfl⟩ : syracuseStep 4727429 = 886393) (by norm_num)
theorem B3154565 : Blo 1244440 3154565 := bbase (se 4 (by rfl) ⟨295740, by rfl⟩ : syracuseStep 3154565 = 591481) (by norm_num)
theorem B1868429 : Blo 1244440 1868429 := bbase (se 3 (by rfl) ⟨350330, by rfl⟩ : syracuseStep 1868429 = 700661) (by norm_num)
theorem B1401493 : Blo 1244440 1401493 := bbase (se 6 (by rfl) ⟨32847, by rfl⟩ : syracuseStep 1401493 = 65695) (by norm_num)
theorem B1868453 : Blo 1244440 1868453 := bbase (se 4 (by rfl) ⟨175167, by rfl⟩ : syracuseStep 1868453 = 350335) (by norm_num)
theorem B6300341 : Blo 1244440 6300341 := bbase (se 5 (by rfl) ⟨295328, by rfl⟩ : syracuseStep 6300341 = 590657) (by norm_num)
theorem B1401529 : Blo 1244440 1401529 := bbase (se 2 (by rfl) ⟨525573, by rfl⟩ : syracuseStep 1401529 = 1051147) (by norm_num)
theorem B2802365 : Blo 1244440 2802365 := bbase (se 3 (by rfl) ⟨525443, by rfl⟩ : syracuseStep 2802365 = 1050887) (by norm_num)
theorem B1868477 : Blo 1244440 1868477 := bbase (se 3 (by rfl) ⟨350339, by rfl⟩ : syracuseStep 1868477 = 700679) (by norm_num)
theorem B1868501 : Blo 1244440 1868501 := bbase (se 7 (by rfl) ⟨21896, by rfl⟩ : syracuseStep 1868501 = 43793) (by norm_num)
theorem B1401565 : Blo 1244440 1401565 := bbase (se 3 (by rfl) ⟨262793, by rfl⟩ : syracuseStep 1401565 = 525587) (by norm_num)
theorem B1868525 : Blo 1244440 1868525 := bbase (se 3 (by rfl) ⟨350348, by rfl⟩ : syracuseStep 1868525 = 700697) (by norm_num)
theorem B2990837 : Blo 1244440 2990837 := bbase (se 5 (by rfl) ⟨140195, by rfl⟩ : syracuseStep 2990837 = 280391) (by norm_num)
theorem B1401601 : Blo 1244440 1401601 := bbase (se 2 (by rfl) ⟨525600, by rfl⟩ : syracuseStep 1401601 = 1051201) (by norm_num)
theorem B2802437 : Blo 1244440 2802437 := bbase (se 4 (by rfl) ⟨262728, by rfl⟩ : syracuseStep 2802437 = 525457) (by norm_num)
theorem B1868549 : Blo 1244440 1868549 := bbase (se 4 (by rfl) ⟨175176, by rfl⟩ : syracuseStep 1868549 = 350353) (by norm_num)
theorem B1868573 : Blo 1244440 1868573 := bbase (se 3 (by rfl) ⟨350357, by rfl⟩ : syracuseStep 1868573 = 700715) (by norm_num)
theorem B1401637 : Blo 1244440 1401637 := bbase (se 4 (by rfl) ⟨131403, by rfl⟩ : syracuseStep 1401637 = 262807) (by norm_num)
theorem B1868597 : Blo 1244440 1868597 := bbase (se 5 (by rfl) ⟨87590, by rfl⟩ : syracuseStep 1868597 = 175181) (by norm_num)
theorem B2769733 : Blo 1244440 2769733 := bbase (se 4 (by rfl) ⟨259662, by rfl⟩ : syracuseStep 2769733 = 519325) (by norm_num)
theorem B1401673 : Blo 1244440 1401673 := bbase (se 2 (by rfl) ⟨525627, by rfl⟩ : syracuseStep 1401673 = 1051255) (by norm_num)
theorem B2802509 : Blo 1244440 2802509 := bbase (se 3 (by rfl) ⟨525470, by rfl⟩ : syracuseStep 2802509 = 1050941) (by norm_num)
theorem B1868621 : Blo 1244440 1868621 := bbase (se 3 (by rfl) ⟨350366, by rfl⟩ : syracuseStep 1868621 = 700733) (by norm_num)
theorem B1868645 : Blo 1244440 1868645 := bbase (se 4 (by rfl) ⟨175185, by rfl⟩ : syracuseStep 1868645 = 350371) (by norm_num)
theorem B2245477 : Blo 1244440 2245477 := bbase (se 4 (by rfl) ⟨210513, by rfl⟩ : syracuseStep 2245477 = 421027) (by norm_num)
theorem B1401709 : Blo 1244440 1401709 := bbase (se 3 (by rfl) ⟨262820, by rfl⟩ : syracuseStep 1401709 = 525641) (by norm_num)
theorem B1868669 : Blo 1244440 1868669 := bbase (se 3 (by rfl) ⟨350375, by rfl⟩ : syracuseStep 1868669 = 700751) (by norm_num)
theorem B1598341 : Blo 1244440 1598341 := bbase (se 4 (by rfl) ⟨149844, by rfl⟩ : syracuseStep 1598341 = 299689) (by norm_num)
theorem B1401745 : Blo 1244440 1401745 := bbase (se 2 (by rfl) ⟨525654, by rfl⟩ : syracuseStep 1401745 = 1051309) (by norm_num)
theorem B4203413 : Blo 1244440 4203413 := bbase (se 6 (by rfl) ⟨98517, by rfl⟩ : syracuseStep 4203413 = 197035) (by norm_num)
theorem B2802581 : Blo 1244440 2802581 := bbase (se 6 (by rfl) ⟨65685, by rfl⟩ : syracuseStep 2802581 = 131371) (by norm_num)
theorem B3990421 : Blo 1244440 3990421 := bbase (se 6 (by rfl) ⟨93525, by rfl⟩ : syracuseStep 3990421 = 187051) (by norm_num)
theorem B1868693 : Blo 1244440 1868693 := bbase (se 6 (by rfl) ⟨43797, by rfl⟩ : syracuseStep 1868693 = 87595) (by norm_num)
theorem B4727717 : Blo 1244440 4727717 := bbase (se 4 (by rfl) ⟨443223, by rfl⟩ : syracuseStep 4727717 = 886447) (by norm_num)
theorem B1868717 : Blo 1244440 1868717 := bbase (se 3 (by rfl) ⟨350384, by rfl⟩ : syracuseStep 1868717 = 700769) (by norm_num)
theorem B7095221 : Blo 1244440 7095221 := bbase (se 5 (by rfl) ⟨332588, by rfl⟩ : syracuseStep 7095221 = 665177) (by norm_num)
theorem B1401781 : Blo 1244440 1401781 := bbase (se 5 (by rfl) ⟨65708, by rfl⟩ : syracuseStep 1401781 = 131417) (by norm_num)
theorem B1868741 : Blo 1244440 1868741 := bbase (se 4 (by rfl) ⟨175194, by rfl⟩ : syracuseStep 1868741 = 350389) (by norm_num)
theorem B5317589 : Blo 1244440 5317589 := bbase (se 7 (by rfl) ⟨62315, by rfl⟩ : syracuseStep 5317589 = 124631) (by norm_num)
theorem B1401817 : Blo 1244440 1401817 := bbase (se 2 (by rfl) ⟨525681, by rfl⟩ : syracuseStep 1401817 = 1051363) (by norm_num)
theorem B2802653 : Blo 1244440 2802653 := bbase (se 3 (by rfl) ⟨525497, by rfl⟩ : syracuseStep 2802653 = 1050995) (by norm_num)
theorem B1868765 : Blo 1244440 1868765 := bbase (se 3 (by rfl) ⟨350393, by rfl⟩ : syracuseStep 1868765 = 700787) (by norm_num)
theorem B3154909 : Blo 1244440 3154909 := bbase (se 3 (by rfl) ⟨591545, by rfl⟩ : syracuseStep 3154909 = 1183091) (by norm_num)
theorem B1868789 : Blo 1244440 1868789 := bbase (se 5 (by rfl) ⟨87599, by rfl⟩ : syracuseStep 1868789 = 175199) (by norm_num)
theorem B1401853 : Blo 1244440 1401853 := bbase (se 3 (by rfl) ⟨262847, by rfl⟩ : syracuseStep 1401853 = 525695) (by norm_num)
theorem B1868813 : Blo 1244440 1868813 := bbase (se 3 (by rfl) ⟨350402, by rfl⟩ : syracuseStep 1868813 = 700805) (by norm_num)
theorem B1401889 : Blo 1244440 1401889 := bbase (se 2 (by rfl) ⟨525708, by rfl⟩ : syracuseStep 1401889 = 1051417) (by norm_num)
theorem B2802725 : Blo 1244440 2802725 := bbase (se 4 (by rfl) ⟨262755, by rfl⟩ : syracuseStep 2802725 = 525511) (by norm_num)
theorem B1868837 : Blo 1244440 1868837 := bbase (se 4 (by rfl) ⟨175203, by rfl⟩ : syracuseStep 1868837 = 350407) (by norm_num)
theorem B1868861 : Blo 1244440 1868861 := bbase (se 3 (by rfl) ⟨350411, by rfl⟩ : syracuseStep 1868861 = 700823) (by norm_num)
theorem B1401925 : Blo 1244440 1401925 := bbase (se 4 (by rfl) ⟨131430, by rfl⟩ : syracuseStep 1401925 = 262861) (by norm_num)
theorem B3155021 : Blo 1244440 3155021 := bbase (se 3 (by rfl) ⟨591566, by rfl⟩ : syracuseStep 3155021 = 1183133) (by norm_num)
theorem B1868885 : Blo 1244440 1868885 := bbase (se 8 (by rfl) ⟨10950, by rfl⟩ : syracuseStep 1868885 = 21901) (by norm_num)
theorem B1401961 : Blo 1244440 1401961 := bbase (se 2 (by rfl) ⟨525735, by rfl⟩ : syracuseStep 1401961 = 1051471) (by norm_num)
theorem B1705069 : Blo 1244440 1705069 := bbase (se 3 (by rfl) ⟨319700, by rfl⟩ : syracuseStep 1705069 = 639401) (by norm_num)
theorem B2802797 : Blo 1244440 2802797 := bbase (se 3 (by rfl) ⟨525524, by rfl⟩ : syracuseStep 2802797 = 1051049) (by norm_num)
theorem B1868909 : Blo 1244440 1868909 := bbase (se 3 (by rfl) ⟨350420, by rfl⟩ : syracuseStep 1868909 = 700841) (by norm_num)
theorem B1868933 : Blo 1244440 1868933 := bbase (se 4 (by rfl) ⟨175212, by rfl⟩ : syracuseStep 1868933 = 350425) (by norm_num)
theorem B5121157 : Blo 1244440 5121157 := bbase (se 4 (by rfl) ⟨480108, by rfl⟩ : syracuseStep 5121157 = 960217) (by norm_num)
theorem B1401997 : Blo 1244440 1401997 := bbase (se 3 (by rfl) ⟨262874, by rfl⟩ : syracuseStep 1401997 = 525749) (by norm_num)
theorem B1868957 : Blo 1244440 1868957 := bbase (se 3 (by rfl) ⟨350429, by rfl⟩ : syracuseStep 1868957 = 700859) (by norm_num)
theorem B1402033 : Blo 1244440 1402033 := bbase (se 2 (by rfl) ⟨525762, by rfl⟩ : syracuseStep 1402033 = 1051525) (by norm_num)
theorem B2802869 : Blo 1244440 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B1868981 : Blo 1244440 1868981 := bbase (se 5 (by rfl) ⟨87608, by rfl⟩ : syracuseStep 1868981 = 175217) (by norm_num)
theorem B3597493 : Blo 1244440 3597493 := bbase (se 5 (by rfl) ⟨168632, by rfl⟩ : syracuseStep 3597493 = 337265) (by norm_num)
theorem B1869005 : Blo 1244440 1869005 := bbase (se 3 (by rfl) ⟨350438, by rfl⟩ : syracuseStep 1869005 = 700877) (by norm_num)
theorem B1402069 : Blo 1244440 1402069 := bbase (se 7 (by rfl) ⟨16430, by rfl⟩ : syracuseStep 1402069 = 32861) (by norm_num)
theorem B1869029 : Blo 1244440 1869029 := bbase (se 4 (by rfl) ⟨175221, by rfl⟩ : syracuseStep 1869029 = 350443) (by norm_num)
theorem B1402105 : Blo 1244440 1402105 := bbase (se 2 (by rfl) ⟨525789, by rfl⟩ : syracuseStep 1402105 = 1051579) (by norm_num)
theorem B2802941 : Blo 1244440 2802941 := bbase (se 3 (by rfl) ⟨525551, by rfl⟩ : syracuseStep 2802941 = 1051103) (by norm_num)
theorem B1869053 : Blo 1244440 1869053 := bbase (se 3 (by rfl) ⟨350447, by rfl⟩ : syracuseStep 1869053 = 700895) (by norm_num)
theorem B1869077 : Blo 1244440 1869077 := bbase (se 6 (by rfl) ⟨43806, by rfl⟩ : syracuseStep 1869077 = 87613) (by norm_num)
theorem B3196189 : Blo 1244440 3196189 := bbase (se 3 (by rfl) ⟨599285, by rfl⟩ : syracuseStep 3196189 = 1198571) (by norm_num)
theorem B1402141 : Blo 1244440 1402141 := bbase (se 3 (by rfl) ⟨262901, by rfl⟩ : syracuseStep 1402141 = 525803) (by norm_num)
theorem B5047589 : Blo 1244440 5047589 := bbase (se 4 (by rfl) ⟨473211, by rfl⟩ : syracuseStep 5047589 = 946423) (by norm_num)
theorem B1869101 : Blo 1244440 1869101 := bbase (se 3 (by rfl) ⟨350456, by rfl⟩ : syracuseStep 1869101 = 700913) (by norm_num)
theorem B1402177 : Blo 1244440 1402177 := bbase (se 2 (by rfl) ⟨525816, by rfl⟩ : syracuseStep 1402177 = 1051633) (by norm_num)
theorem B4203845 : Blo 1244440 4203845 := bbase (se 4 (by rfl) ⟨394110, by rfl⟩ : syracuseStep 4203845 = 788221) (by norm_num)
theorem B2803013 : Blo 1244440 2803013 := bbase (se 4 (by rfl) ⟨262782, by rfl⟩ : syracuseStep 2803013 = 525565) (by norm_num)
theorem B1869125 : Blo 1244440 1869125 := bbase (se 4 (by rfl) ⟨175230, by rfl⟩ : syracuseStep 1869125 = 350461) (by norm_num)
theorem B2524493 : Blo 1244440 2524493 := bbase (se 3 (by rfl) ⟨473342, by rfl⟩ : syracuseStep 2524493 = 946685) (by norm_num)
theorem B1869149 : Blo 1244440 1869149 := bbase (se 3 (by rfl) ⟨350465, by rfl⟩ : syracuseStep 1869149 = 700931) (by norm_num)
theorem B1402213 : Blo 1244440 1402213 := bbase (se 4 (by rfl) ⟨131457, by rfl⟩ : syracuseStep 1402213 = 262915) (by norm_num)
theorem B6735221 : Blo 1244440 6735221 := bbase (se 5 (by rfl) ⟨315713, by rfl⟩ : syracuseStep 6735221 = 631427) (by norm_num)
theorem B1869173 : Blo 1244440 1869173 := bbase (se 5 (by rfl) ⟨87617, by rfl⟩ : syracuseStep 1869173 = 175235) (by norm_num)
theorem B1664381 : Blo 1244440 1664381 := bbase (se 3 (by rfl) ⟨312071, by rfl⟩ : syracuseStep 1664381 = 624143) (by norm_num)
theorem B2803085 : Blo 1244440 2803085 := bbase (se 3 (by rfl) ⟨525578, by rfl⟩ : syracuseStep 2803085 = 1051157) (by norm_num)
theorem B1869197 : Blo 1244440 1869197 := bbase (se 3 (by rfl) ⟨350474, by rfl⟩ : syracuseStep 1869197 = 700949) (by norm_num)
theorem B2991509 : Blo 1244440 2991509 := bbase (se 6 (by rfl) ⟨70113, by rfl⟩ : syracuseStep 2991509 = 140227) (by norm_num)
theorem B1869221 : Blo 1244440 1869221 := bbase (se 4 (by rfl) ⟨175239, by rfl⟩ : syracuseStep 1869221 = 350479) (by norm_num)
theorem B1869245 : Blo 1244440 1869245 := bbase (se 3 (by rfl) ⟨350483, by rfl⟩ : syracuseStep 1869245 = 700967) (by norm_num)
theorem B2803157 : Blo 1244440 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B1869269 : Blo 1244440 1869269 := bbase (se 7 (by rfl) ⟨21905, by rfl⟩ : syracuseStep 1869269 = 43811) (by norm_num)
theorem B1869293 : Blo 1244440 1869293 := bbase (se 3 (by rfl) ⟨350492, by rfl⟩ : syracuseStep 1869293 = 700985) (by norm_num)
theorem B1869317 : Blo 1244440 1869317 := bbase (se 4 (by rfl) ⟨175248, by rfl⟩ : syracuseStep 1869317 = 350497) (by norm_num)
theorem B2803229 : Blo 1244440 2803229 := bbase (se 3 (by rfl) ⟨525605, by rfl⟩ : syracuseStep 2803229 = 1051211) (by norm_num)
theorem B1869341 : Blo 1244440 1869341 := bbase (se 3 (by rfl) ⟨350501, by rfl⟩ : syracuseStep 1869341 = 701003) (by norm_num)
theorem B6309413 : Blo 1244440 6309413 := bbase (se 4 (by rfl) ⟨591507, by rfl⟩ : syracuseStep 6309413 = 1183015) (by norm_num)
theorem B1869365 : Blo 1244440 1869365 := bbase (se 5 (by rfl) ⟨87626, by rfl⟩ : syracuseStep 1869365 = 175253) (by norm_num)
theorem B1869389 : Blo 1244440 1869389 := bbase (se 3 (by rfl) ⟨350510, by rfl⟩ : syracuseStep 1869389 = 701021) (by norm_num)
theorem B1558117 : Blo 1244440 1558117 := bbase (se 4 (by rfl) ⟨146073, by rfl⟩ : syracuseStep 1558117 = 292147) (by norm_num)
theorem B2803301 : Blo 1244440 2803301 := bbase (se 4 (by rfl) ⟨262809, by rfl⟩ : syracuseStep 2803301 = 525619) (by norm_num)
theorem B1869413 : Blo 1244440 1869413 := bbase (se 4 (by rfl) ⟨175257, by rfl⟩ : syracuseStep 1869413 = 350515) (by norm_num)
theorem B1869437 : Blo 1244440 1869437 := bbase (se 3 (by rfl) ⟨350519, by rfl⟩ : syracuseStep 1869437 = 701039) (by norm_num)
theorem B1869461 : Blo 1244440 1869461 := bbase (se 6 (by rfl) ⟨43815, by rfl⟩ : syracuseStep 1869461 = 87631) (by norm_num)
theorem B2803373 : Blo 1244440 2803373 := bbase (se 3 (by rfl) ⟨525632, by rfl⟩ : syracuseStep 2803373 = 1051265) (by norm_num)
theorem B1869485 : Blo 1244440 1869485 := bbase (se 3 (by rfl) ⟨350528, by rfl⟩ : syracuseStep 1869485 = 701057) (by norm_num)
theorem B1869509 : Blo 1244440 1869509 := bbase (se 4 (by rfl) ⟨175266, by rfl⟩ : syracuseStep 1869509 = 350533) (by norm_num)
theorem B1869533 : Blo 1244440 1869533 := bbase (se 3 (by rfl) ⟨350537, by rfl⟩ : syracuseStep 1869533 = 701075) (by norm_num)
theorem B5981941 : Blo 1244440 5981941 := bbase (se 5 (by rfl) ⟨280403, by rfl⟩ : syracuseStep 5981941 = 560807) (by norm_num)
theorem B7571189 : Blo 1244440 7571189 := bbase (se 5 (by rfl) ⟨354899, by rfl⟩ : syracuseStep 7571189 = 709799) (by norm_num)
theorem B4204277 : Blo 1244440 4204277 := bbase (se 5 (by rfl) ⟨197075, by rfl⟩ : syracuseStep 4204277 = 394151) (by norm_num)
theorem B2803445 : Blo 1244440 2803445 := bbase (se 5 (by rfl) ⟨131411, by rfl⟩ : syracuseStep 2803445 = 262823) (by norm_num)
theorem B1869557 : Blo 1244440 1869557 := bbase (se 5 (by rfl) ⟨87635, by rfl⟩ : syracuseStep 1869557 = 175271) (by norm_num)
theorem B1869581 : Blo 1244440 1869581 := bbase (se 3 (by rfl) ⟨350546, by rfl⟩ : syracuseStep 1869581 = 701093) (by norm_num)
theorem B1869605 : Blo 1244440 1869605 := bbase (se 4 (by rfl) ⟨175275, by rfl⟩ : syracuseStep 1869605 = 350551) (by norm_num)
theorem B2803517 : Blo 1244440 2803517 := bbase (se 3 (by rfl) ⟨525659, by rfl⟩ : syracuseStep 2803517 = 1051319) (by norm_num)
theorem B1869629 : Blo 1244440 1869629 := bbase (se 3 (by rfl) ⟨350555, by rfl⟩ : syracuseStep 1869629 = 701111) (by norm_num)
theorem B1869653 : Blo 1244440 1869653 := bbase (se 9 (by rfl) ⟨5477, by rfl⟩ : syracuseStep 1869653 = 10955) (by norm_num)
theorem B2697061 : Blo 1244440 2697061 := bbase (se 4 (by rfl) ⟨252849, by rfl⟩ : syracuseStep 2697061 = 505699) (by norm_num)
theorem B2803589 : Blo 1244440 2803589 := bbase (se 4 (by rfl) ⟨262836, by rfl⟩ : syracuseStep 2803589 = 525673) (by norm_num)
theorem B1517449 : Blo 1244440 1517449 := bbase (se 2 (by rfl) ⟨569043, by rfl⟩ : syracuseStep 1517449 = 1138087) (by norm_num)
theorem B6301637 : Blo 1244440 6301637 := bbase (se 4 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 6301637 = 1181557) (by norm_num)
theorem B5392325 : Blo 1244440 5392325 := bbase (se 4 (by rfl) ⟨505530, by rfl⟩ : syracuseStep 5392325 = 1011061) (by norm_num)
theorem B2803661 : Blo 1244440 2803661 := bbase (se 3 (by rfl) ⟨525686, by rfl⟩ : syracuseStep 2803661 = 1051373) (by norm_num)
theorem B2803733 : Blo 1244440 2803733 := bbase (se 6 (by rfl) ⟨65712, by rfl⟩ : syracuseStep 2803733 = 131425) (by norm_num)
theorem B4491301 : Blo 1244440 4491301 := bbase (se 4 (by rfl) ⟨421059, by rfl⟩ : syracuseStep 4491301 = 842119) (by norm_num)
theorem B4728901 : Blo 1244440 4728901 := bbase (se 4 (by rfl) ⟨443334, by rfl⟩ : syracuseStep 4728901 = 886669) (by norm_num)
theorem B2803805 : Blo 1244440 2803805 := bbase (se 3 (by rfl) ⟨525713, by rfl⟩ : syracuseStep 2803805 = 1051427) (by norm_num)
theorem B1329269 : Blo 1244440 1329269 := bbase (se 5 (by rfl) ⟨62309, by rfl⟩ : syracuseStep 1329269 = 124619) (by norm_num)
theorem B1575065 : Blo 1244440 1575065 := bbase (se 2 (by rfl) ⟨590649, by rfl⟩ : syracuseStep 1575065 = 1181299) (by norm_num)
theorem B4204709 : Blo 1244440 4204709 := bbase (se 4 (by rfl) ⟨394191, by rfl⟩ : syracuseStep 4204709 = 788383) (by norm_num)
theorem B2803877 : Blo 1244440 2803877 := bbase (se 4 (by rfl) ⟨262863, by rfl⟩ : syracuseStep 2803877 = 525727) (by norm_num)
theorem B1329329 : Blo 1244440 1329329 := bbase (se 2 (by rfl) ⟨498498, by rfl⟩ : syracuseStep 1329329 = 996997) (by norm_num)
theorem B3549365 : Blo 1244440 3549365 := bbase (se 5 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 3549365 = 332753) (by norm_num)
theorem B1575121 : Blo 1244440 1575121 := bbase (se 2 (by rfl) ⟨590670, by rfl⟩ : syracuseStep 1575121 = 1181341) (by norm_num)
theorem B3991781 : Blo 1244440 3991781 := bbase (se 4 (by rfl) ⟨374229, by rfl⟩ : syracuseStep 3991781 = 748459) (by norm_num)
theorem B2803949 : Blo 1244440 2803949 := bbase (se 3 (by rfl) ⟨525740, by rfl⟩ : syracuseStep 2803949 = 1051481) (by norm_num)
theorem B1575217 : Blo 1244440 1575217 := bbase (se 2 (by rfl) ⟨590706, by rfl⟩ : syracuseStep 1575217 = 1181413) (by norm_num)
theorem B1329457 : Blo 1244440 1329457 := bbase (se 2 (by rfl) ⟨498546, by rfl⟩ : syracuseStep 1329457 = 997093) (by norm_num)
theorem B2804021 : Blo 1244440 2804021 := bbase (se 5 (by rfl) ⟨131438, by rfl⟩ : syracuseStep 2804021 = 262877) (by norm_num)
theorem B4729205 : Blo 1244440 4729205 := bbase (se 5 (by rfl) ⟨221681, by rfl⟩ : syracuseStep 4729205 = 443363) (by norm_num)
theorem B2804093 : Blo 1244440 2804093 := bbase (se 3 (by rfl) ⟨525767, by rfl⟩ : syracuseStep 2804093 = 1051535) (by norm_num)
theorem B2804165 : Blo 1244440 2804165 := bbase (se 4 (by rfl) ⟨262890, by rfl⟩ : syracuseStep 2804165 = 525781) (by norm_num)
theorem B1575389 : Blo 1244440 1575389 := bbase (se 3 (by rfl) ⟨295385, by rfl⟩ : syracuseStep 1575389 = 590771) (by norm_num)
theorem B4491749 : Blo 1244440 4491749 := bbase (se 4 (by rfl) ⟨421101, by rfl⟩ : syracuseStep 4491749 = 842203) (by norm_num)
theorem B5048821 : Blo 1244440 5048821 := bbase (se 5 (by rfl) ⟨236663, by rfl⟩ : syracuseStep 5048821 = 473327) (by norm_num)
theorem B2804237 : Blo 1244440 2804237 := bbase (se 3 (by rfl) ⟨525794, by rfl⟩ : syracuseStep 2804237 = 1051589) (by norm_num)
theorem B1575445 : Blo 1244440 1575445 := bbase (se 6 (by rfl) ⟨36924, by rfl⟩ : syracuseStep 1575445 = 73849) (by norm_num)
theorem B4262453 : Blo 1244440 4262453 := bbase (se 5 (by rfl) ⟨199802, by rfl⟩ : syracuseStep 4262453 = 399605) (by norm_num)
theorem B4205141 : Blo 1244440 4205141 := bbase (se 8 (by rfl) ⟨24639, by rfl⟩ : syracuseStep 4205141 = 49279) (by norm_num)
theorem B2804309 : Blo 1244440 2804309 := bbase (se 8 (by rfl) ⟨16431, by rfl⟩ : syracuseStep 2804309 = 32863) (by norm_num)
theorem B1575541 : Blo 1244440 1575541 := bbase (se 5 (by rfl) ⟨73853, by rfl⟩ : syracuseStep 1575541 = 147707) (by norm_num)
theorem B1772165 : Blo 1244440 1772165 := bbase (se 4 (by rfl) ⟨166140, by rfl⟩ : syracuseStep 1772165 = 332281) (by norm_num)
theorem B2878109 : Blo 1244440 2878109 := bbase (se 3 (by rfl) ⟨539645, by rfl⟩ : syracuseStep 2878109 = 1079291) (by norm_num)
theorem B2804381 : Blo 1244440 2804381 := bbase (se 3 (by rfl) ⟨525821, by rfl⟩ : syracuseStep 2804381 = 1051643) (by norm_num)
theorem B1419977 : Blo 1244440 1419977 := bbase (se 2 (by rfl) ⟨532491, by rfl⟩ : syracuseStep 1419977 = 1064983) (by norm_num)
theorem B2804453 : Blo 1244440 2804453 := bbase (se 4 (by rfl) ⟨262917, by rfl⟩ : syracuseStep 2804453 = 525835) (by norm_num)
theorem B1329901 : Blo 1244440 1329901 := bbase (se 3 (by rfl) ⟨249356, by rfl⟩ : syracuseStep 1329901 = 498713) (by norm_num)
theorem B1575713 : Blo 1244440 1575713 := bbase (se 2 (by rfl) ⟨590892, by rfl⟩ : syracuseStep 1575713 = 1181785) (by norm_num)
theorem B2100053 : Blo 1244440 2100053 := bbase (se 9 (by rfl) ⟨6152, by rfl⟩ : syracuseStep 2100053 = 12305) (by norm_num)
theorem B1575769 : Blo 1244440 1575769 := bbase (se 2 (by rfl) ⟨590913, by rfl⟩ : syracuseStep 1575769 = 1181827) (by norm_num)
theorem B1993565 : Blo 1244440 1993565 := bbase (se 3 (by rfl) ⟨373793, by rfl⟩ : syracuseStep 1993565 = 747587) (by norm_num)
theorem B1330021 : Blo 1244440 1330021 := bbase (se 4 (by rfl) ⟨124689, by rfl⟩ : syracuseStep 1330021 = 249379) (by norm_num)
theorem B4549541 : Blo 1244440 4549541 := bbase (se 4 (by rfl) ⟨426519, by rfl⟩ : syracuseStep 4549541 = 853039) (by norm_num)
theorem B1575865 : Blo 1244440 1575865 := bbase (se 2 (by rfl) ⟨590949, by rfl⟩ : syracuseStep 1575865 = 1181899) (by norm_num)
theorem B2100181 : Blo 1244440 2100181 := bbase (se 7 (by rfl) ⟨24611, by rfl⟩ : syracuseStep 2100181 = 49223) (by norm_num)
theorem B4205573 : Blo 1244440 4205573 := bbase (se 4 (by rfl) ⟨394272, by rfl⟩ : syracuseStep 4205573 = 788545) (by norm_num)
theorem B2100269 : Blo 1244440 2100269 := bbase (se 3 (by rfl) ⟨393800, by rfl⟩ : syracuseStep 2100269 = 787601) (by norm_num)
theorem B1330273 : Blo 1244440 1330273 := bbase (se 2 (by rfl) ⟨498852, by rfl⟩ : syracuseStep 1330273 = 997705) (by norm_num)
theorem B1576037 : Blo 1244440 1576037 := bbase (se 4 (by rfl) ⟨147753, by rfl⟩ : syracuseStep 1576037 = 295507) (by norm_num)
theorem B1330277 : Blo 1244440 1330277 := bbase (se 4 (by rfl) ⟨124713, by rfl⟩ : syracuseStep 1330277 = 249427) (by norm_num)
theorem B2993269 : Blo 1244440 2993269 := bbase (se 5 (by rfl) ⟨140309, by rfl⟩ : syracuseStep 2993269 = 280619) (by norm_num)
theorem B1576093 : Blo 1244440 1576093 := bbase (se 3 (by rfl) ⟨295517, by rfl⟩ : syracuseStep 1576093 = 591035) (by norm_num)
theorem B2100397 : Blo 1244440 2100397 := bbase (se 3 (by rfl) ⟨393824, by rfl⟩ : syracuseStep 2100397 = 787649) (by norm_num)
theorem B6302933 : Blo 1244440 6302933 := bbase (se 7 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 6302933 = 147725) (by norm_num)
theorem B2526421 : Blo 1244440 2526421 := bbase (se 7 (by rfl) ⟨29606, by rfl⟩ : syracuseStep 2526421 = 59213) (by norm_num)
theorem B3788005 : Blo 1244440 3788005 := bbase (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) (by norm_num)
theorem B2362621 : Blo 1244440 2362621 := bbase (se 3 (by rfl) ⟨442991, by rfl⟩ : syracuseStep 2362621 = 885983) (by norm_num)
theorem B1576189 : Blo 1244440 1576189 := bbase (se 3 (by rfl) ⟨295535, by rfl⟩ : syracuseStep 1576189 = 591071) (by norm_num)
theorem B2100485 : Blo 1244440 2100485 := bbase (se 4 (by rfl) ⟨196920, by rfl⟩ : syracuseStep 2100485 = 393841) (by norm_num)
theorem B2100613 : Blo 1244440 2100613 := bbase (se 4 (by rfl) ⟨196932, by rfl⟩ : syracuseStep 2100613 = 393865) (by norm_num)
theorem B2362765 : Blo 1244440 2362765 := bbase (se 3 (by rfl) ⟨443018, by rfl⟩ : syracuseStep 2362765 = 886037) (by norm_num)
theorem B2395541 : Blo 1244440 2395541 := bbase (se 6 (by rfl) ⟨56145, by rfl⟩ : syracuseStep 2395541 = 112291) (by norm_num)
theorem B1576361 : Blo 1244440 1576361 := bbase (se 2 (by rfl) ⟨591135, by rfl⟩ : syracuseStep 1576361 = 1182271) (by norm_num)
theorem B4206005 : Blo 1244440 4206005 := bbase (se 5 (by rfl) ⟨197156, by rfl⟩ : syracuseStep 4206005 = 394313) (by norm_num)
theorem B1682893 : Blo 1244440 1682893 := bbase (se 3 (by rfl) ⟨315542, by rfl⟩ : syracuseStep 1682893 = 631085) (by norm_num)
theorem B2100701 : Blo 1244440 2100701 := bbase (se 3 (by rfl) ⟨393881, by rfl⟩ : syracuseStep 2100701 = 787763) (by norm_num)
theorem B1576417 : Blo 1244440 1576417 := bbase (se 2 (by rfl) ⟨591156, by rfl⟩ : syracuseStep 1576417 = 1182313) (by norm_num)
theorem B1994237 : Blo 1244440 1994237 := bbase (se 3 (by rfl) ⟨373919, by rfl⟩ : syracuseStep 1994237 = 747839) (by norm_num)
theorem B2362925 : Blo 1244440 2362925 := bbase (se 3 (by rfl) ⟨443048, by rfl⟩ : syracuseStep 2362925 = 886097) (by norm_num)
theorem B1576513 : Blo 1244440 1576513 := bbase (se 2 (by rfl) ⟨591192, by rfl⟩ : syracuseStep 1576513 = 1182385) (by norm_num)
theorem B2100829 : Blo 1244440 2100829 := bbase (se 3 (by rfl) ⟨393905, by rfl⟩ : syracuseStep 2100829 = 787811) (by norm_num)
theorem B5049989 : Blo 1244440 5049989 := bbase (se 4 (by rfl) ⟨473436, by rfl⟩ : syracuseStep 5049989 = 946873) (by norm_num)
theorem B1330841 : Blo 1244440 1330841 := bbase (se 2 (by rfl) ⟨499065, by rfl⟩ : syracuseStep 1330841 = 998131) (by norm_num)
theorem B1683109 : Blo 1244440 1683109 := bbase (se 4 (by rfl) ⟨157791, by rfl⟩ : syracuseStep 1683109 = 315583) (by norm_num)
theorem B2526893 : Blo 1244440 2526893 := bbase (se 3 (by rfl) ⟨473792, by rfl⟩ : syracuseStep 2526893 = 947585) (by norm_num)
theorem B2100917 : Blo 1244440 2100917 := bbase (se 5 (by rfl) ⟨98480, by rfl⟩ : syracuseStep 2100917 = 196961) (by norm_num)
theorem B2363069 : Blo 1244440 2363069 := bbase (se 3 (by rfl) ⟨443075, by rfl⟩ : syracuseStep 2363069 = 886151) (by norm_num)
theorem B2559709 : Blo 1244440 2559709 := bbase (se 3 (by rfl) ⟨479945, by rfl⟩ : syracuseStep 2559709 = 959891) (by norm_num)
theorem B2993885 : Blo 1244440 2993885 := bbase (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) (by norm_num)
theorem B1576685 : Blo 1244440 1576685 := bbase (se 3 (by rfl) ⟨295628, by rfl⟩ : syracuseStep 1576685 = 591257) (by norm_num)
theorem B1576741 : Blo 1244440 1576741 := bbase (se 4 (by rfl) ⟨147819, by rfl⟩ : syracuseStep 1576741 = 295639) (by norm_num)
theorem B2101045 : Blo 1244440 2101045 := bbase (se 5 (by rfl) ⟨98486, by rfl⟩ : syracuseStep 2101045 = 196973) (by norm_num)
theorem B2879293 : Blo 1244440 2879293 := bbase (se 3 (by rfl) ⟨539867, by rfl⟩ : syracuseStep 2879293 = 1079735) (by norm_num)
theorem B1331029 : Blo 1244440 1331029 := bbase (se 9 (by rfl) ⟨3899, by rfl⟩ : syracuseStep 1331029 = 7799) (by norm_num)
theorem B4206437 : Blo 1244440 4206437 := bbase (se 4 (by rfl) ⟨394353, by rfl⟩ : syracuseStep 4206437 = 788707) (by norm_num)
theorem B1576837 : Blo 1244440 1576837 := bbase (se 4 (by rfl) ⟨147828, by rfl⟩ : syracuseStep 1576837 = 295657) (by norm_num)
theorem B2101133 : Blo 1244440 2101133 := bbase (se 3 (by rfl) ⟨393962, by rfl⟩ : syracuseStep 2101133 = 787925) (by norm_num)
theorem B2658197 : Blo 1244440 2658197 := bbase (se 6 (by rfl) ⟨62301, by rfl⟩ : syracuseStep 2658197 = 124603) (by norm_num)
theorem B2363357 : Blo 1244440 2363357 := bbase (se 3 (by rfl) ⟨443129, by rfl⟩ : syracuseStep 2363357 = 886259) (by norm_num)
theorem B1994749 : Blo 1244440 1994749 := bbase (se 3 (by rfl) ⟨374015, by rfl⟩ : syracuseStep 1994749 = 748031) (by norm_num)
theorem B2101261 : Blo 1244440 2101261 := bbase (se 3 (by rfl) ⟨393986, by rfl⟩ : syracuseStep 2101261 = 787973) (by norm_num)
theorem B1773589 : Blo 1244440 1773589 := bbase (se 6 (by rfl) ⟨41568, by rfl⟩ : syracuseStep 1773589 = 83137) (by norm_num)
theorem B1577009 : Blo 1244440 1577009 := bbase (se 2 (by rfl) ⟨591378, by rfl⟩ : syracuseStep 1577009 = 1182757) (by norm_num)
theorem B2101349 : Blo 1244440 2101349 := bbase (se 4 (by rfl) ⟨197001, by rfl⟩ : syracuseStep 2101349 = 394003) (by norm_num)
theorem B1577065 : Blo 1244440 1577065 := bbase (se 2 (by rfl) ⟨591399, by rfl⟩ : syracuseStep 1577065 = 1182799) (by norm_num)
theorem B2363509 : Blo 1244440 2363509 := bbase (se 5 (by rfl) ⟨110789, by rfl⟩ : syracuseStep 2363509 = 221579) (by norm_num)
theorem B1577161 : Blo 1244440 1577161 := bbase (se 2 (by rfl) ⟨591435, by rfl⟩ : syracuseStep 1577161 = 1182871) (by norm_num)
theorem B3150029 : Blo 1244440 3150029 := bbase (se 3 (by rfl) ⟨590630, by rfl⟩ : syracuseStep 3150029 = 1181261) (by norm_num)
theorem B2101477 : Blo 1244440 2101477 := bbase (se 4 (by rfl) ⟨197013, by rfl⟩ : syracuseStep 2101477 = 394027) (by norm_num)
theorem B2101565 : Blo 1244440 2101565 := bbase (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) (by norm_num)
theorem B1577333 : Blo 1244440 1577333 := bbase (se 5 (by rfl) ⟨73937, by rfl⟩ : syracuseStep 1577333 = 147875) (by norm_num)
theorem B2363813 : Blo 1244440 2363813 := bbase (se 4 (by rfl) ⟨221607, by rfl⟩ : syracuseStep 2363813 = 443215) (by norm_num)
theorem B1798573 : Blo 1244440 1798573 := bbase (se 3 (by rfl) ⟨337232, by rfl⟩ : syracuseStep 1798573 = 674465) (by norm_num)
theorem B1577389 : Blo 1244440 1577389 := bbase (se 3 (by rfl) ⟨295760, by rfl⟩ : syracuseStep 1577389 = 591521) (by norm_num)
theorem B4731317 : Blo 1244440 4731317 := bbase (se 5 (by rfl) ⟨221780, by rfl⟩ : syracuseStep 4731317 = 443561) (by norm_num)
theorem B1495481 : Blo 1244440 1495481 := bbase (se 2 (by rfl) ⟨560805, by rfl⟩ : syracuseStep 1495481 = 1121611) (by norm_num)
theorem B2101693 : Blo 1244440 2101693 := bbase (se 3 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 2101693 = 788135) (by norm_num)
theorem B1995205 : Blo 1244440 1995205 := bbase (se 4 (by rfl) ⟨187050, by rfl⟩ : syracuseStep 1995205 = 374101) (by norm_num)
theorem B15364565 : Blo 1244440 15364565 := bbase (se 7 (by rfl) ⟨180053, by rfl⟩ : syracuseStep 15364565 = 360107) (by norm_num)
theorem B2994653 : Blo 1244440 2994653 := bbase (se 3 (by rfl) ⟨561497, by rfl⟩ : syracuseStep 2994653 = 1122995) (by norm_num)
theorem B6304229 : Blo 1244440 6304229 := bbase (se 4 (by rfl) ⟨591021, by rfl⟩ : syracuseStep 6304229 = 1182043) (by norm_num)
theorem B2994661 : Blo 1244440 2994661 := bbase (se 4 (by rfl) ⟨280749, by rfl⟩ : syracuseStep 2994661 = 561499) (by norm_num)
theorem B1683973 : Blo 1244440 1683973 := bbase (se 4 (by rfl) ⟨157872, by rfl⟩ : syracuseStep 1683973 = 315745) (by norm_num)
theorem B1577485 : Blo 1244440 1577485 := bbase (se 3 (by rfl) ⟨295778, by rfl⟩ : syracuseStep 1577485 = 591557) (by norm_num)
theorem B2101781 : Blo 1244440 2101781 := bbase (se 6 (by rfl) ⟨49260, by rfl⟩ : syracuseStep 2101781 = 98521) (by norm_num)
theorem B3150373 : Blo 1244440 3150373 := bbase (se 4 (by rfl) ⟨295347, by rfl⟩ : syracuseStep 3150373 = 590695) (by norm_num)
theorem B1495597 : Blo 1244440 1495597 := bbase (se 3 (by rfl) ⟨280424, by rfl⟩ : syracuseStep 1495597 = 560849) (by norm_num)
theorem B1774181 : Blo 1244440 1774181 := bbase (se 4 (by rfl) ⟨166329, by rfl⟩ : syracuseStep 1774181 = 332659) (by norm_num)
theorem B3150485 : Blo 1244440 3150485 := bbase (se 6 (by rfl) ⟨73839, by rfl⟩ : syracuseStep 3150485 = 147679) (by norm_num)
theorem B2101909 : Blo 1244440 2101909 := bbase (se 6 (by rfl) ⟨49263, by rfl⟩ : syracuseStep 2101909 = 98527) (by norm_num)
theorem B1774261 : Blo 1244440 1774261 := bbase (se 5 (by rfl) ⟨83168, by rfl⟩ : syracuseStep 1774261 = 166337) (by norm_num)
theorem B4731605 : Blo 1244440 4731605 := bbase (se 7 (by rfl) ⟨55448, by rfl⟩ : syracuseStep 4731605 = 110897) (by norm_num)
theorem B2101997 : Blo 1244440 2101997 := bbase (se 3 (by rfl) ⟨394124, by rfl⟩ : syracuseStep 2101997 = 788249) (by norm_num)
theorem B1495793 : Blo 1244440 1495793 := bbase (se 2 (by rfl) ⟨560922, by rfl⟩ : syracuseStep 1495793 = 1121845) (by norm_num)
theorem B2659085 : Blo 1244440 2659085 := bbase (se 3 (by rfl) ⟨498578, by rfl⟩ : syracuseStep 2659085 = 997157) (by norm_num)
theorem B21279509 : Blo 1244440 21279509 := bbase (se 6 (by rfl) ⟨498738, by rfl⟩ : syracuseStep 21279509 = 997477) (by norm_num)
theorem B1774381 : Blo 1244440 1774381 := bbase (se 3 (by rfl) ⟨332696, by rfl⟩ : syracuseStep 1774381 = 665393) (by norm_num)
theorem B3150677 : Blo 1244440 3150677 := bbase (se 9 (by rfl) ⟨9230, by rfl⟩ : syracuseStep 3150677 = 18461) (by norm_num)
theorem B2102125 : Blo 1244440 2102125 := bbase (se 3 (by rfl) ⟨394148, by rfl⟩ : syracuseStep 2102125 = 788297) (by norm_num)
theorem B2659205 : Blo 1244440 2659205 := bbase (se 4 (by rfl) ⟨249300, by rfl⟩ : syracuseStep 2659205 = 498601) (by norm_num)
theorem B1774477 : Blo 1244440 1774477 := bbase (se 3 (by rfl) ⟨332714, by rfl⟩ : syracuseStep 1774477 = 665429) (by norm_num)
theorem B2102213 : Blo 1244440 2102213 := bbase (se 4 (by rfl) ⟨197082, by rfl⟩ : syracuseStep 2102213 = 394165) (by norm_num)
theorem B2102341 : Blo 1244440 2102341 := bbase (se 4 (by rfl) ⟨197094, by rfl⟩ : syracuseStep 2102341 = 394189) (by norm_num)
theorem B1995877 : Blo 1244440 1995877 := bbase (se 4 (by rfl) ⟨187113, by rfl⟩ : syracuseStep 1995877 = 374227) (by norm_num)
theorem B5321861 : Blo 1244440 5321861 := bbase (se 4 (by rfl) ⟨498924, by rfl⟩ : syracuseStep 5321861 = 997849) (by norm_num)
theorem B2364565 : Blo 1244440 2364565 := bbase (se 6 (by rfl) ⟨55419, by rfl⟩ : syracuseStep 2364565 = 110839) (by norm_num)
theorem B2102429 : Blo 1244440 2102429 := bbase (se 3 (by rfl) ⟨394205, by rfl⟩ : syracuseStep 2102429 = 788411) (by norm_num)
theorem B3151021 : Blo 1244440 3151021 := bbase (se 3 (by rfl) ⟨590816, by rfl⟩ : syracuseStep 3151021 = 1181633) (by norm_num)
theorem B1496341 : Blo 1244440 1496341 := bbase (se 6 (by rfl) ⟨35070, by rfl⟩ : syracuseStep 1496341 = 70141) (by norm_num)
theorem B3151133 : Blo 1244440 3151133 := bbase (se 3 (by rfl) ⟨590837, by rfl⟩ : syracuseStep 3151133 = 1181675) (by norm_num)
theorem B2102557 : Blo 1244440 2102557 := bbase (se 3 (by rfl) ⟨394229, by rfl⟩ : syracuseStep 2102557 = 788459) (by norm_num)
theorem B2364709 : Blo 1244440 2364709 := bbase (se 4 (by rfl) ⟨221691, by rfl⟩ : syracuseStep 2364709 = 443383) (by norm_num)
theorem B9721205 : Blo 1244440 9721205 := bbase (se 5 (by rfl) ⟨455681, by rfl⟩ : syracuseStep 9721205 = 911363) (by norm_num)
theorem B2102645 : Blo 1244440 2102645 := bbase (se 5 (by rfl) ⟨98561, by rfl⟩ : syracuseStep 2102645 = 197123) (by norm_num)
theorem B1496485 : Blo 1244440 1496485 := bbase (se 4 (by rfl) ⟨140295, by rfl⟩ : syracuseStep 1496485 = 280591) (by norm_num)
theorem B2364869 : Blo 1244440 2364869 := bbase (se 4 (by rfl) ⟨221706, by rfl⟩ : syracuseStep 2364869 = 443413) (by norm_num)
theorem B3151325 : Blo 1244440 3151325 := bbase (se 3 (by rfl) ⟨590873, by rfl⟩ : syracuseStep 3151325 = 1181747) (by norm_num)
theorem B3364325 : Blo 1244440 3364325 := bbase (se 4 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 3364325 = 630811) (by norm_num)
theorem B2102773 : Blo 1244440 2102773 := bbase (se 5 (by rfl) ⟨98567, by rfl⟩ : syracuseStep 2102773 = 197135) (by norm_num)
theorem B2659837 : Blo 1244440 2659837 := bbase (se 3 (by rfl) ⟨498719, by rfl⟩ : syracuseStep 2659837 = 997439) (by norm_num)
theorem B1996301 : Blo 1244440 1996301 := bbase (se 3 (by rfl) ⟨374306, by rfl⟩ : syracuseStep 1996301 = 748613) (by norm_num)
theorem B2102861 : Blo 1244440 2102861 := bbase (se 3 (by rfl) ⟨394286, by rfl⟩ : syracuseStep 2102861 = 788573) (by norm_num)
theorem B3544661 : Blo 1244440 3544661 := bbase (se 8 (by rfl) ⟨20769, by rfl⟩ : syracuseStep 3544661 = 41539) (by norm_num)
theorem B2365013 : Blo 1244440 2365013 := bbase (se 8 (by rfl) ⟨13857, by rfl⟩ : syracuseStep 2365013 = 27715) (by norm_num)
theorem B2102989 : Blo 1244440 2102989 := bbase (se 3 (by rfl) ⟨394310, by rfl⟩ : syracuseStep 2102989 = 788621) (by norm_num)
theorem B6305525 : Blo 1244440 6305525 := bbase (se 5 (by rfl) ⟨295571, by rfl⟩ : syracuseStep 6305525 = 591143) (by norm_num)
theorem B2103077 : Blo 1244440 2103077 := bbase (se 4 (by rfl) ⟨197163, by rfl⟩ : syracuseStep 2103077 = 394327) (by norm_num)
theorem B3151669 : Blo 1244440 3151669 := bbase (se 5 (by rfl) ⟨147734, by rfl⟩ : syracuseStep 3151669 = 295469) (by norm_num)
theorem B2840437 : Blo 1244440 2840437 := bbase (se 5 (by rfl) ⟨133145, by rfl⟩ : syracuseStep 2840437 = 266291) (by norm_num)
theorem B2365301 : Blo 1244440 2365301 := bbase (se 5 (by rfl) ⟨110873, by rfl⟩ : syracuseStep 2365301 = 221747) (by norm_num)
theorem B3151781 : Blo 1244440 3151781 := bbase (se 4 (by rfl) ⟨295479, by rfl⟩ : syracuseStep 3151781 = 590959) (by norm_num)
theorem B2103205 : Blo 1244440 2103205 := bbase (se 4 (by rfl) ⟨197175, by rfl⟩ : syracuseStep 2103205 = 394351) (by norm_num)
theorem B4200389 : Blo 1244440 4200389 := bbase (se 4 (by rfl) ⟨393786, by rfl⟩ : syracuseStep 4200389 = 787573) (by norm_num)
theorem B3987397 : Blo 1244440 3987397 := bbase (se 4 (by rfl) ⟨373818, by rfl⟩ : syracuseStep 3987397 = 747637) (by norm_num)
theorem B2398189 : Blo 1244440 2398189 := bbase (se 3 (by rfl) ⟨449660, by rfl⟩ : syracuseStep 2398189 = 899321) (by norm_num)
theorem B11974645 : Blo 1244440 11974645 := bbase (se 5 (by rfl) ⟨561311, by rfl⟩ : syracuseStep 11974645 = 1122623) (by norm_num)
theorem B2103293 : Blo 1244440 2103293 := bbase (se 3 (by rfl) ⟨394367, by rfl⟩ : syracuseStep 2103293 = 788735) (by norm_num)
theorem B2365453 : Blo 1244440 2365453 := bbase (se 3 (by rfl) ⟨443522, by rfl⟩ : syracuseStep 2365453 = 887045) (by norm_num)
theorem B5986325 : Blo 1244440 5986325 := bbase (se 6 (by rfl) ⟨140304, by rfl⟩ : syracuseStep 5986325 = 280609) (by norm_num)
theorem B4790341 : Blo 1244440 4790341 := bbase (se 4 (by rfl) ⟨449094, by rfl⟩ : syracuseStep 4790341 = 898189) (by norm_num)
theorem B3151973 : Blo 1244440 3151973 := bbase (se 4 (by rfl) ⟨295497, by rfl⟩ : syracuseStep 3151973 = 590995) (by norm_num)
theorem B3545333 : Blo 1244440 3545333 := bbase (se 5 (by rfl) ⟨166187, by rfl⟩ : syracuseStep 3545333 = 332375) (by norm_num)
theorem B4725013 : Blo 1244440 4725013 := bbase (se 6 (by rfl) ⟨110742, by rfl⟩ : syracuseStep 4725013 = 221485) (by norm_num)
theorem B9459989 : Blo 1244440 9459989 := bbase (se 6 (by rfl) ⟨221718, by rfl⟩ : syracuseStep 9459989 = 443437) (by norm_num)
theorem B2365757 : Blo 1244440 2365757 := bbase (se 3 (by rfl) ⟨443579, by rfl⟩ : syracuseStep 2365757 = 887159) (by norm_num)
theorem B4200821 : Blo 1244440 4200821 := bbase (se 5 (by rfl) ⟨196913, by rfl⟩ : syracuseStep 4200821 = 393827) (by norm_num)
theorem B2660725 : Blo 1244440 2660725 := bbase (se 5 (by rfl) ⟨124721, by rfl⟩ : syracuseStep 2660725 = 249443) (by norm_num)
theorem B7985557 : Blo 1244440 7985557 := bbase (se 6 (by rfl) ⟨187161, by rfl⟩ : syracuseStep 7985557 = 374323) (by norm_num)
theorem B2800061 : Blo 1244440 2800061 := bbase (se 3 (by rfl) ⟨525011, by rfl⟩ : syracuseStep 2800061 = 1050023) (by norm_num)
theorem B3152317 : Blo 1244440 3152317 := bbase (se 3 (by rfl) ⟨591059, by rfl⟩ : syracuseStep 3152317 = 1182119) (by norm_num)
theorem B2660845 : Blo 1244440 2660845 := bbase (se 3 (by rfl) ⟨498908, by rfl⟩ : syracuseStep 2660845 = 997817) (by norm_num)
theorem B4487669 : Blo 1244440 4487669 := bbase (se 5 (by rfl) ⟨210359, by rfl⟩ : syracuseStep 4487669 = 420719) (by norm_num)
theorem B2800133 : Blo 1244440 2800133 := bbase (se 4 (by rfl) ⟨262512, by rfl⟩ : syracuseStep 2800133 = 525025) (by norm_num)
theorem B3152429 : Blo 1244440 3152429 := bbase (se 3 (by rfl) ⟨591080, by rfl⟩ : syracuseStep 3152429 = 1182161) (by norm_num)
theorem B1366589 : Blo 1244440 1366589 := bbase (se 3 (by rfl) ⟨256235, by rfl⟩ : syracuseStep 1366589 = 512471) (by norm_num)
theorem B4725317 : Blo 1244440 4725317 := bbase (se 4 (by rfl) ⟨442998, by rfl⟩ : syracuseStep 4725317 = 885997) (by norm_num)
theorem B3693125 : Blo 1244440 3693125 := bbase (se 4 (by rfl) ⟨346230, by rfl⟩ : syracuseStep 3693125 = 692461) (by norm_num)
theorem B2800205 : Blo 1244440 2800205 := bbase (se 3 (by rfl) ⟨525038, by rfl⟩ : syracuseStep 2800205 = 1050077) (by norm_num)
theorem B2800277 : Blo 1244440 2800277 := bbase (se 6 (by rfl) ⟨65631, by rfl⟩ : syracuseStep 2800277 = 131263) (by norm_num)
theorem B3545765 : Blo 1244440 3545765 := bbase (se 4 (by rfl) ⟨332415, by rfl⟩ : syracuseStep 3545765 = 664831) (by norm_num)
theorem B9452213 : Blo 1244440 9452213 := bbase (se 5 (by rfl) ⟨443072, by rfl⟩ : syracuseStep 9452213 = 886145) (by norm_num)
theorem B2800349 : Blo 1244440 2800349 := bbase (se 3 (by rfl) ⟨525065, by rfl⟩ : syracuseStep 2800349 = 1050131) (by norm_num)
theorem B3152621 : Blo 1244440 3152621 := bbase (se 3 (by rfl) ⟨591116, by rfl⟩ : syracuseStep 3152621 = 1182233) (by norm_num)
theorem B2661101 : Blo 1244440 2661101 := bbase (se 3 (by rfl) ⟨498956, by rfl⟩ : syracuseStep 2661101 = 997913) (by norm_num)
theorem B3365621 : Blo 1244440 3365621 := bbase (se 5 (by rfl) ⟨157763, by rfl⟩ : syracuseStep 3365621 = 315527) (by norm_num)
theorem B4487957 : Blo 1244440 4487957 := bbase (se 6 (by rfl) ⟨105186, by rfl⟩ : syracuseStep 4487957 = 210373) (by norm_num)
theorem B2800421 : Blo 1244440 2800421 := bbase (se 4 (by rfl) ⟨262539, by rfl⟩ : syracuseStep 2800421 = 525079) (by norm_num)
theorem B4201253 : Blo 1244440 4201253 := bbase (se 4 (by rfl) ⟨393867, by rfl⟩ : syracuseStep 4201253 = 787735) (by norm_num)
theorem B2841413 : Blo 1244440 2841413 := bbase (se 4 (by rfl) ⟨266382, by rfl⟩ : syracuseStep 2841413 = 532765) (by norm_num)
theorem B2800493 : Blo 1244440 2800493 := bbase (se 3 (by rfl) ⟨525092, by rfl⟩ : syracuseStep 2800493 = 1050185) (by norm_num)
theorem B5323637 : Blo 1244440 5323637 := bbase (se 5 (by rfl) ⟨249545, by rfl⟩ : syracuseStep 5323637 = 499091) (by norm_num)
theorem B4488101 : Blo 1244440 4488101 := bbase (se 4 (by rfl) ⟨420759, by rfl⟩ : syracuseStep 4488101 = 841519) (by norm_num)
theorem B1866677 : Blo 1244440 1866677 := bbase (se 5 (by rfl) ⟨87500, by rfl⟩ : syracuseStep 1866677 = 175001) (by norm_num)
theorem B2800565 : Blo 1244440 2800565 := bbase (se 5 (by rfl) ⟨131276, by rfl⟩ : syracuseStep 2800565 = 262553) (by norm_num)
theorem B2694077 : Blo 1244440 2694077 := bbase (se 3 (by rfl) ⟨505139, by rfl⟩ : syracuseStep 2694077 = 1010279) (by norm_num)
theorem B1866701 : Blo 1244440 1866701 := bbase (se 3 (by rfl) ⟨350006, by rfl⟩ : syracuseStep 1866701 = 700013) (by norm_num)
theorem B1866725 : Blo 1244440 1866725 := bbase (se 4 (by rfl) ⟨175005, by rfl⟩ : syracuseStep 1866725 = 350011) (by norm_num)
theorem B2128877 : Blo 1244440 2128877 := bbase (se 3 (by rfl) ⟨399164, by rfl⟩ : syracuseStep 2128877 = 798329) (by norm_num)
theorem B1866749 : Blo 1244440 1866749 := bbase (se 3 (by rfl) ⟨350015, by rfl⟩ : syracuseStep 1866749 = 700031) (by norm_num)
theorem B2800637 : Blo 1244440 2800637 := bbase (se 3 (by rfl) ⟨525119, by rfl⟩ : syracuseStep 2800637 = 1050239) (by norm_num)
theorem B6306821 : Blo 1244440 6306821 := bbase (se 4 (by rfl) ⟨591264, by rfl⟩ : syracuseStep 6306821 = 1182529) (by norm_num)
theorem B2841605 : Blo 1244440 2841605 := bbase (se 4 (by rfl) ⟨266400, by rfl⟩ : syracuseStep 2841605 = 532801) (by norm_num)
theorem B1866773 : Blo 1244440 1866773 := bbase (se 6 (by rfl) ⟨43752, by rfl⟩ : syracuseStep 1866773 = 87505) (by norm_num)
theorem B8526869 : Blo 1244440 8526869 := bbase (se 6 (by rfl) ⟨199848, by rfl⟩ : syracuseStep 8526869 = 399697) (by norm_num)
theorem B1866797 : Blo 1244440 1866797 := bbase (se 3 (by rfl) ⟨350024, by rfl⟩ : syracuseStep 1866797 = 700049) (by norm_num)
theorem B1866821 : Blo 1244440 1866821 := bbase (se 4 (by rfl) ⟨175014, by rfl⟩ : syracuseStep 1866821 = 350029) (by norm_num)
theorem B2800709 : Blo 1244440 2800709 := bbase (se 4 (by rfl) ⟨262566, by rfl⟩ : syracuseStep 2800709 = 525133) (by norm_num)
theorem B3152965 : Blo 1244440 3152965 := bbase (se 4 (by rfl) ⟨295590, by rfl⟩ : syracuseStep 3152965 = 591181) (by norm_num)
theorem B3988565 : Blo 1244440 3988565 := bbase (se 8 (by rfl) ⟨23370, by rfl⟩ : syracuseStep 3988565 = 46741) (by norm_num)
theorem B1866845 : Blo 1244440 1866845 := bbase (se 3 (by rfl) ⟨350033, by rfl⟩ : syracuseStep 1866845 = 700067) (by norm_num)
theorem B5323877 : Blo 1244440 5323877 := bbase (se 4 (by rfl) ⟨499113, by rfl⟩ : syracuseStep 5323877 = 998227) (by norm_num)
theorem B1866869 : Blo 1244440 1866869 := bbase (se 5 (by rfl) ⟨87509, by rfl⟩ : syracuseStep 1866869 = 175019) (by norm_num)
theorem B1866893 : Blo 1244440 1866893 := bbase (se 3 (by rfl) ⟨350042, by rfl⟩ : syracuseStep 1866893 = 700085) (by norm_num)
theorem B2800781 : Blo 1244440 2800781 := bbase (se 3 (by rfl) ⟨525146, by rfl⟩ : syracuseStep 2800781 = 1050293) (by norm_num)
theorem B2694293 : Blo 1244440 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B1866917 : Blo 1244440 1866917 := bbase (se 4 (by rfl) ⟨175023, by rfl⟩ : syracuseStep 1866917 = 350047) (by norm_num)
theorem B3153077 : Blo 1244440 3153077 := bbase (se 5 (by rfl) ⟨147800, by rfl⟩ : syracuseStep 3153077 = 295601) (by norm_num)
theorem B1866941 : Blo 1244440 1866941 := bbase (se 3 (by rfl) ⟨350051, by rfl⟩ : syracuseStep 1866941 = 700103) (by norm_num)
theorem B1400017 : Blo 1244440 1400017 := bbase (se 2 (by rfl) ⟨525006, by rfl⟩ : syracuseStep 1400017 = 1050013) (by norm_num)
theorem B1866965 : Blo 1244440 1866965 := bbase (se 7 (by rfl) ⟨21878, by rfl⟩ : syracuseStep 1866965 = 43757) (by norm_num)
theorem B2800853 : Blo 1244440 2800853 := bbase (se 7 (by rfl) ⟨32822, by rfl⟩ : syracuseStep 2800853 = 65645) (by norm_num)
theorem B4201685 : Blo 1244440 4201685 := bbase (se 7 (by rfl) ⟨49238, by rfl⟩ : syracuseStep 4201685 = 98477) (by norm_num)
theorem B5315813 : Blo 1244440 5315813 := bbase (se 4 (by rfl) ⟨498357, by rfl⟩ : syracuseStep 5315813 = 996715) (by norm_num)
theorem B2129125 : Blo 1244440 2129125 := bbase (se 4 (by rfl) ⟨199605, by rfl⟩ : syracuseStep 2129125 = 399211) (by norm_num)
theorem B1866989 : Blo 1244440 1866989 := bbase (se 3 (by rfl) ⟨350060, by rfl⟩ : syracuseStep 1866989 = 700121) (by norm_num)
theorem B1400053 : Blo 1244440 1400053 := bbase (se 5 (by rfl) ⟨65627, by rfl⟩ : syracuseStep 1400053 = 131255) (by norm_num)
theorem B1867013 : Blo 1244440 1867013 := bbase (se 4 (by rfl) ⟨175032, by rfl⟩ : syracuseStep 1867013 = 350065) (by norm_num)
theorem B14187797 : Blo 1244440 14187797 := bbase (se 6 (by rfl) ⟨332526, by rfl⟩ : syracuseStep 14187797 = 665053) (by norm_num)
theorem B1400089 : Blo 1244440 1400089 := bbase (se 2 (by rfl) ⟨525033, by rfl⟩ : syracuseStep 1400089 = 1050067) (by norm_num)
theorem B1867037 : Blo 1244440 1867037 := bbase (se 3 (by rfl) ⟨350069, by rfl⟩ : syracuseStep 1867037 = 700139) (by norm_num)
theorem B2800925 : Blo 1244440 2800925 := bbase (se 3 (by rfl) ⟨525173, by rfl⟩ : syracuseStep 2800925 = 1050347) (by norm_num)
theorem B1867061 : Blo 1244440 1867061 := bbase (se 5 (by rfl) ⟨87518, by rfl⟩ : syracuseStep 1867061 = 175037) (by norm_num)
theorem B1400125 : Blo 1244440 1400125 := bbase (se 3 (by rfl) ⟨262523, by rfl⟩ : syracuseStep 1400125 = 525047) (by norm_num)
theorem B1867085 : Blo 1244440 1867085 := bbase (se 3 (by rfl) ⟨350078, by rfl⟩ : syracuseStep 1867085 = 700157) (by norm_num)
theorem B1400161 : Blo 1244440 1400161 := bbase (se 2 (by rfl) ⟨525060, by rfl⟩ : syracuseStep 1400161 = 1050121) (by norm_num)
theorem B1867109 : Blo 1244440 1867109 := bbase (se 4 (by rfl) ⟨175041, by rfl⟩ : syracuseStep 1867109 = 350083) (by norm_num)
theorem B2800997 : Blo 1244440 2800997 := bbase (se 4 (by rfl) ⟨262593, by rfl⟩ : syracuseStep 2800997 = 525187) (by norm_num)
theorem B3153269 : Blo 1244440 3153269 := bbase (se 5 (by rfl) ⟨147809, by rfl⟩ : syracuseStep 3153269 = 295619) (by norm_num)
theorem B1867133 : Blo 1244440 1867133 := bbase (se 3 (by rfl) ⟨350087, by rfl⟩ : syracuseStep 1867133 = 700175) (by norm_num)
theorem B1400197 : Blo 1244440 1400197 := bbase (se 4 (by rfl) ⟨131268, by rfl⟩ : syracuseStep 1400197 = 262537) (by norm_num)
theorem B1867157 : Blo 1244440 1867157 := bbase (se 6 (by rfl) ⟨43761, by rfl⟩ : syracuseStep 1867157 = 87523) (by norm_num)
theorem B3546517 : Blo 1244440 3546517 := bbase (se 6 (by rfl) ⟨83121, by rfl⟩ : syracuseStep 3546517 = 166243) (by norm_num)
theorem B1400233 : Blo 1244440 1400233 := bbase (se 2 (by rfl) ⟨525087, by rfl⟩ : syracuseStep 1400233 = 1050175) (by norm_num)
theorem B1867181 : Blo 1244440 1867181 := bbase (se 3 (by rfl) ⟨350096, by rfl⟩ : syracuseStep 1867181 = 700193) (by norm_num)
theorem B2801069 : Blo 1244440 2801069 := bbase (se 3 (by rfl) ⟨525200, by rfl⟩ : syracuseStep 2801069 = 1050401) (by norm_num)
theorem B2244029 : Blo 1244440 2244029 := bbase (se 3 (by rfl) ⟨420755, by rfl⟩ : syracuseStep 2244029 = 841511) (by norm_num)
theorem B1867205 : Blo 1244440 1867205 := bbase (se 4 (by rfl) ⟨175050, by rfl⟩ : syracuseStep 1867205 = 350101) (by norm_num)
theorem B1400269 : Blo 1244440 1400269 := bbase (se 3 (by rfl) ⟨262550, by rfl⟩ : syracuseStep 1400269 = 525101) (by norm_num)
theorem B1867229 : Blo 1244440 1867229 := bbase (se 3 (by rfl) ⟨350105, by rfl⟩ : syracuseStep 1867229 = 700211) (by norm_num)
theorem B1400305 : Blo 1244440 1400305 := bbase (se 2 (by rfl) ⟨525114, by rfl⟩ : syracuseStep 1400305 = 1050229) (by norm_num)
theorem B1867253 : Blo 1244440 1867253 := bbase (se 5 (by rfl) ⟨87527, by rfl⟩ : syracuseStep 1867253 = 175055) (by norm_num)
theorem B2801141 : Blo 1244440 2801141 := bbase (se 5 (by rfl) ⟨131303, by rfl⟩ : syracuseStep 2801141 = 262607) (by norm_num)
theorem B1867277 : Blo 1244440 1867277 := bbase (se 3 (by rfl) ⟨350114, by rfl⟩ : syracuseStep 1867277 = 700229) (by norm_num)
theorem B1400341 : Blo 1244440 1400341 := bbase (se 6 (by rfl) ⟨32820, by rfl⟩ : syracuseStep 1400341 = 65641) (by norm_num)
theorem B1867301 : Blo 1244440 1867301 := bbase (se 4 (by rfl) ⟨175059, by rfl⟩ : syracuseStep 1867301 = 350119) (by norm_num)
theorem B1400377 : Blo 1244440 1400377 := bbase (se 2 (by rfl) ⟨525141, by rfl⟩ : syracuseStep 1400377 = 1050283) (by norm_num)
theorem B1867325 : Blo 1244440 1867325 := bbase (se 3 (by rfl) ⟨350123, by rfl⟩ : syracuseStep 1867325 = 700247) (by norm_num)
theorem B2801213 : Blo 1244440 2801213 := bbase (se 3 (by rfl) ⟨525227, by rfl⟩ : syracuseStep 2801213 = 1050455) (by norm_num)
theorem B1867349 : Blo 1244440 1867349 := bbase (se 8 (by rfl) ⟨10941, by rfl⟩ : syracuseStep 1867349 = 21883) (by norm_num)
theorem B1400413 : Blo 1244440 1400413 := bbase (se 3 (by rfl) ⟨262577, by rfl⟩ : syracuseStep 1400413 = 525155) (by norm_num)
theorem B2661989 : Blo 1244440 2661989 := bbase (se 4 (by rfl) ⟨249561, by rfl⟩ : syracuseStep 2661989 = 499123) (by norm_num)
theorem B1867373 : Blo 1244440 1867373 := bbase (se 3 (by rfl) ⟨350132, by rfl⟩ : syracuseStep 1867373 = 700265) (by norm_num)
theorem B1400449 : Blo 1244440 1400449 := bbase (se 2 (by rfl) ⟨525168, by rfl⟩ : syracuseStep 1400449 = 1050337) (by norm_num)
theorem B1867397 : Blo 1244440 1867397 := bbase (se 4 (by rfl) ⟨175068, by rfl⟩ : syracuseStep 1867397 = 350137) (by norm_num)
theorem B2801285 : Blo 1244440 2801285 := bbase (se 4 (by rfl) ⟨262620, by rfl⟩ : syracuseStep 2801285 = 525241) (by norm_num)
theorem B4202117 : Blo 1244440 4202117 := bbase (se 4 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 4202117 = 787897) (by norm_num)
theorem B1867421 : Blo 1244440 1867421 := bbase (se 3 (by rfl) ⟨350141, by rfl⟩ : syracuseStep 1867421 = 700283) (by norm_num)
theorem B1400485 : Blo 1244440 1400485 := bbase (se 4 (by rfl) ⟨131295, by rfl⟩ : syracuseStep 1400485 = 262591) (by norm_num)
theorem B1867445 : Blo 1244440 1867445 := bbase (se 5 (by rfl) ⟨87536, by rfl⟩ : syracuseStep 1867445 = 175073) (by norm_num)
theorem B2694845 : Blo 1244440 2694845 := bbase (se 3 (by rfl) ⟨505283, by rfl⟩ : syracuseStep 2694845 = 1010567) (by norm_num)
theorem B1400521 : Blo 1244440 1400521 := bbase (se 2 (by rfl) ⟨525195, by rfl⟩ : syracuseStep 1400521 = 1050391) (by norm_num)
theorem B1867469 : Blo 1244440 1867469 := bbase (se 3 (by rfl) ⟨350150, by rfl⟩ : syracuseStep 1867469 = 700301) (by norm_num)
theorem B2801357 : Blo 1244440 2801357 := bbase (se 3 (by rfl) ⟨525254, by rfl⟩ : syracuseStep 2801357 = 1050509) (by norm_num)
theorem B3153613 : Blo 1244440 3153613 := bbase (se 3 (by rfl) ⟨591302, by rfl⟩ : syracuseStep 3153613 = 1182605) (by norm_num)
theorem B1867493 : Blo 1244440 1867493 := bbase (se 4 (by rfl) ⟨175077, by rfl⟩ : syracuseStep 1867493 = 350155) (by norm_num)
theorem B1400557 : Blo 1244440 1400557 := bbase (se 3 (by rfl) ⟨262604, by rfl⟩ : syracuseStep 1400557 = 525209) (by norm_num)
theorem B1867517 : Blo 1244440 1867517 := bbase (se 3 (by rfl) ⟨350159, by rfl⟩ : syracuseStep 1867517 = 700319) (by norm_num)
theorem B1400593 : Blo 1244440 1400593 := bbase (se 2 (by rfl) ⟨525222, by rfl⟩ : syracuseStep 1400593 = 1050445) (by norm_num)
theorem B1867541 : Blo 1244440 1867541 := bbase (se 6 (by rfl) ⟨43770, by rfl⟩ : syracuseStep 1867541 = 87541) (by norm_num)
theorem B2801429 : Blo 1244440 2801429 := bbase (se 6 (by rfl) ⟨65658, by rfl⟩ : syracuseStep 2801429 = 131317) (by norm_num)
theorem B1867565 : Blo 1244440 1867565 := bbase (se 3 (by rfl) ⟨350168, by rfl⟩ : syracuseStep 1867565 = 700337) (by norm_num)
theorem B1400629 : Blo 1244440 1400629 := bbase (se 5 (by rfl) ⟨65654, by rfl⟩ : syracuseStep 1400629 = 131309) (by norm_num)
theorem B3153725 : Blo 1244440 3153725 := bbase (se 3 (by rfl) ⟨591323, by rfl⟩ : syracuseStep 3153725 = 1182647) (by norm_num)
theorem B1892165 : Blo 1244440 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B1867589 : Blo 1244440 1867589 := bbase (se 4 (by rfl) ⟨175086, by rfl⟩ : syracuseStep 1867589 = 350173) (by norm_num)
theorem B1400665 : Blo 1244440 1400665 := bbase (se 2 (by rfl) ⟨525249, by rfl⟩ : syracuseStep 1400665 = 1050499) (by norm_num)
theorem B1867613 : Blo 1244440 1867613 := bbase (se 3 (by rfl) ⟨350177, by rfl⟩ : syracuseStep 1867613 = 700355) (by norm_num)
theorem B2801501 : Blo 1244440 2801501 := bbase (se 3 (by rfl) ⟨525281, by rfl⟩ : syracuseStep 2801501 = 1050563) (by norm_num)
theorem B8085365 : Blo 1244440 8085365 := bbase (se 5 (by rfl) ⟨379001, by rfl⟩ : syracuseStep 8085365 = 758003) (by norm_num)
theorem B1867637 : Blo 1244440 1867637 := bbase (se 5 (by rfl) ⟨87545, by rfl⟩ : syracuseStep 1867637 = 175091) (by norm_num)
theorem B1400701 : Blo 1244440 1400701 := bbase (se 3 (by rfl) ⟨262631, by rfl⟩ : syracuseStep 1400701 = 525263) (by norm_num)
theorem B1867661 : Blo 1244440 1867661 := bbase (se 3 (by rfl) ⟨350186, by rfl⟩ : syracuseStep 1867661 = 700373) (by norm_num)
theorem B1400737 : Blo 1244440 1400737 := bbase (se 2 (by rfl) ⟨525276, by rfl⟩ : syracuseStep 1400737 = 1050553) (by norm_num)
theorem B1867685 : Blo 1244440 1867685 := bbase (se 4 (by rfl) ⟨175095, by rfl⟩ : syracuseStep 1867685 = 350191) (by norm_num)
theorem B2801573 : Blo 1244440 2801573 := bbase (se 4 (by rfl) ⟨262647, by rfl⟩ : syracuseStep 2801573 = 525295) (by norm_num)
theorem B1867709 : Blo 1244440 1867709 := bbase (se 3 (by rfl) ⟨350195, by rfl⟩ : syracuseStep 1867709 = 700391) (by norm_num)
theorem B1400773 : Blo 1244440 1400773 := bbase (se 4 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 1400773 = 262645) (by norm_num)
theorem B1867733 : Blo 1244440 1867733 := bbase (se 7 (by rfl) ⟨21887, by rfl⟩ : syracuseStep 1867733 = 43775) (by norm_num)
theorem B1400809 : Blo 1244440 1400809 := bbase (se 2 (by rfl) ⟨525303, by rfl⟩ : syracuseStep 1400809 = 1050607) (by norm_num)
theorem B1867757 : Blo 1244440 1867757 := bbase (se 3 (by rfl) ⟨350204, by rfl⟩ : syracuseStep 1867757 = 700409) (by norm_num)
theorem B2801645 : Blo 1244440 2801645 := bbase (se 3 (by rfl) ⟨525308, by rfl⟩ : syracuseStep 2801645 = 1050617) (by norm_num)
theorem B3153917 : Blo 1244440 3153917 := bbase (se 3 (by rfl) ⟨591359, by rfl⟩ : syracuseStep 3153917 = 1182719) (by norm_num)
theorem B1245187 : Blo 1244440 1245187 := bstep (se 1 (by rfl) ⟨933890, by rfl⟩ : syracuseStep 1245187 = 1867781) B1867781
theorem B2801681 : Blo 1244440 2801681 := bstep (se 2 (by rfl) ⟨1050630, by rfl⟩ : syracuseStep 2801681 = 2101261) B2101261
theorem B1867793 : Blo 1244440 1867793 := bstep (se 2 (by rfl) ⟨700422, by rfl⟩ : syracuseStep 1867793 = 1400845) B1400845
theorem B1245203 : Blo 1244440 1245203 := bstep (se 1 (by rfl) ⟨933902, by rfl⟩ : syracuseStep 1245203 = 1867805) B1867805
theorem B3153937 : Blo 1244440 3153937 := bstep (se 2 (by rfl) ⟨1182726, by rfl⟩ : syracuseStep 3153937 = 2365453) B2365453
theorem B2801699 : Blo 1244440 2801699 := bstep (se 1 (by rfl) ⟨2101274, by rfl⟩ : syracuseStep 2801699 = 4202549) B4202549
theorem B1867811 : Blo 1244440 1867811 := bstep (se 1 (by rfl) ⟨1400858, by rfl⟩ : syracuseStep 1867811 = 2801717) B2801717
theorem B1245219 : Blo 1244440 1245219 := bstep (se 1 (by rfl) ⟨933914, by rfl⟩ : syracuseStep 1245219 = 1867829) B1867829
theorem B5988401 : Blo 1244440 5988401 := bstep (se 2 (by rfl) ⟨2245650, by rfl⟩ : syracuseStep 5988401 = 4491301) B4491301
theorem B1245235 : Blo 1244440 1245235 := bstep (se 1 (by rfl) ⟨933926, by rfl⟩ : syracuseStep 1245235 = 1867853) B1867853
theorem B1867841 : Blo 1244440 1867841 := bstep (se 2 (by rfl) ⟨700440, by rfl⟩ : syracuseStep 1867841 = 1400881) B1400881
theorem B1245251 : Blo 1244440 1245251 := bstep (se 1 (by rfl) ⟨933938, by rfl⟩ : syracuseStep 1245251 = 1867877) B1867877
theorem B1400899 : Blo 1244440 1400899 := bstep (se 1 (by rfl) ⟨1050674, by rfl⟩ : syracuseStep 1400899 = 2101349) B2101349
theorem B1867859 : Blo 1244440 1867859 := bstep (se 1 (by rfl) ⟨1400894, by rfl⟩ : syracuseStep 1867859 = 2801789) B2801789
theorem B1245267 : Blo 1244440 1245267 := bstep (se 1 (by rfl) ⟨933950, by rfl⟩ : syracuseStep 1245267 = 1867901) B1867901
theorem B1245283 : Blo 1244440 1245283 := bstep (se 1 (by rfl) ⟨933962, by rfl⟩ : syracuseStep 1245283 = 1867925) B1867925
theorem B1867889 : Blo 1244440 1867889 := bstep (se 2 (by rfl) ⟨700458, by rfl⟩ : syracuseStep 1867889 = 1400917) B1400917
theorem B1245299 : Blo 1244440 1245299 := bstep (se 1 (by rfl) ⟨933974, by rfl⟩ : syracuseStep 1245299 = 1867949) B1867949
theorem B1867907 : Blo 1244440 1867907 := bstep (se 1 (by rfl) ⟨1400930, by rfl⟩ : syracuseStep 1867907 = 2801861) B2801861
theorem B1245315 : Blo 1244440 1245315 := bstep (se 1 (by rfl) ⟨933986, by rfl⟩ : syracuseStep 1245315 = 1867973) B1867973
theorem B1245331 : Blo 1244440 1245331 := bstep (se 1 (by rfl) ⟨933998, by rfl⟩ : syracuseStep 1245331 = 1867997) B1867997
theorem B1867937 : Blo 1244440 1867937 := bstep (se 2 (by rfl) ⟨700476, by rfl⟩ : syracuseStep 1867937 = 1400953) B1400953
theorem B1245347 : Blo 1244440 1245347 := bstep (se 1 (by rfl) ⟨934010, by rfl⟩ : syracuseStep 1245347 = 1868021) B1868021
theorem B1867955 : Blo 1244440 1867955 := bstep (se 1 (by rfl) ⟨1400966, by rfl⟩ : syracuseStep 1867955 = 2801933) B2801933
theorem B1245363 : Blo 1244440 1245363 := bstep (se 1 (by rfl) ⟨934022, by rfl⟩ : syracuseStep 1245363 = 1868045) B1868045
theorem B1245379 : Blo 1244440 1245379 := bstep (se 1 (by rfl) ⟨934034, by rfl⟩ : syracuseStep 1245379 = 1868069) B1868069
theorem B1867985 : Blo 1244440 1867985 := bstep (se 2 (by rfl) ⟨700494, by rfl⟩ : syracuseStep 1867985 = 1400989) B1400989
theorem B1401043 : Blo 1244440 1401043 := bstep (se 1 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 1401043 = 2101565) B2101565
theorem B1245395 : Blo 1244440 1245395 := bstep (se 1 (by rfl) ⟨934046, by rfl⟩ : syracuseStep 1245395 = 1868093) B1868093
theorem B1868003 : Blo 1244440 1868003 := bstep (se 1 (by rfl) ⟨1401002, by rfl⟩ : syracuseStep 1868003 = 2802005) B2802005
theorem B1245411 : Blo 1244440 1245411 := bstep (se 1 (by rfl) ⟨934058, by rfl⟩ : syracuseStep 1245411 = 1868117) B1868117
theorem B1245427 : Blo 1244440 1245427 := bstep (se 1 (by rfl) ⟨934070, by rfl⟩ : syracuseStep 1245427 = 1868141) B1868141
theorem B1868033 : Blo 1244440 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B1245443 : Blo 1244440 1245443 := bstep (se 1 (by rfl) ⟨934082, by rfl⟩ : syracuseStep 1245443 = 1868165) B1868165
theorem B4202765 : Blo 1244440 4202765 := bstep (se 3 (by rfl) ⟨788018, by rfl⟩ : syracuseStep 4202765 = 1576037) B1576037
theorem B3547405 : Blo 1244440 3547405 := bstep (se 3 (by rfl) ⟨665138, by rfl⟩ : syracuseStep 3547405 = 1330277) B1330277
theorem B1868051 : Blo 1244440 1868051 := bstep (se 1 (by rfl) ⟨1401038, by rfl⟩ : syracuseStep 1868051 = 2802077) B2802077
theorem B1245459 : Blo 1244440 1245459 := bstep (se 1 (by rfl) ⟨934094, by rfl⟩ : syracuseStep 1245459 = 1868189) B1868189
theorem B1245475 : Blo 1244440 1245475 := bstep (se 1 (by rfl) ⟨934106, by rfl⟩ : syracuseStep 1245475 = 1868213) B1868213
theorem B3154211 : Blo 1244440 3154211 := bstep (se 1 (by rfl) ⟨2365658, by rfl⟩ : syracuseStep 3154211 = 4731317) B4731317
theorem B2801969 : Blo 1244440 2801969 := bstep (se 2 (by rfl) ⟨1050738, by rfl⟩ : syracuseStep 2801969 = 2101477) B2101477
theorem B1868081 : Blo 1244440 1868081 := bstep (se 2 (by rfl) ⟨700530, by rfl⟩ : syracuseStep 1868081 = 1401061) B1401061
theorem B1245491 : Blo 1244440 1245491 := bstep (se 1 (by rfl) ⟨934118, by rfl⟩ : syracuseStep 1245491 = 1868237) B1868237
theorem B4202819 : Blo 1244440 4202819 := bstep (se 1 (by rfl) ⟨3152114, by rfl⟩ : syracuseStep 4202819 = 6304229) B6304229
theorem B2801987 : Blo 1244440 2801987 := bstep (se 1 (by rfl) ⟨2101490, by rfl⟩ : syracuseStep 2801987 = 4202981) B4202981
theorem B1868099 : Blo 1244440 1868099 := bstep (se 1 (by rfl) ⟨1401074, by rfl⟩ : syracuseStep 1868099 = 2802149) B2802149
theorem B1245507 : Blo 1244440 1245507 := bstep (se 1 (by rfl) ⟨934130, by rfl⟩ : syracuseStep 1245507 = 1868261) B1868261
theorem B1245523 : Blo 1244440 1245523 := bstep (se 1 (by rfl) ⟨934142, by rfl⟩ : syracuseStep 1245523 = 1868285) B1868285
theorem B1868129 : Blo 1244440 1868129 := bstep (se 2 (by rfl) ⟨700548, by rfl⟩ : syracuseStep 1868129 = 1401097) B1401097
theorem B3785059 : Blo 1244440 3785059 := bstep (se 1 (by rfl) ⟨2838794, by rfl⟩ : syracuseStep 3785059 = 5677589) B5677589
theorem B1401187 : Blo 1244440 1401187 := bstep (se 1 (by rfl) ⟨1050890, by rfl⟩ : syracuseStep 1401187 = 2101781) B2101781
theorem B1245539 : Blo 1244440 1245539 := bstep (se 1 (by rfl) ⟨934154, by rfl⟩ : syracuseStep 1245539 = 1868309) B1868309
theorem B6300017 : Blo 1244440 6300017 := bstep (se 2 (by rfl) ⟨2362506, by rfl⟩ : syracuseStep 6300017 = 4725013) B4725013
theorem B1868147 : Blo 1244440 1868147 := bstep (se 1 (by rfl) ⟨1401110, by rfl⟩ : syracuseStep 1868147 = 2802221) B2802221
theorem B1245555 : Blo 1244440 1245555 := bstep (se 1 (by rfl) ⟨934166, by rfl⟩ : syracuseStep 1245555 = 1868333) B1868333
theorem B1245571 : Blo 1244440 1245571 := bstep (se 1 (by rfl) ⟨934178, by rfl⟩ : syracuseStep 1245571 = 1868357) B1868357
theorem B1868177 : Blo 1244440 1868177 := bstep (se 2 (by rfl) ⟨700566, by rfl⟩ : syracuseStep 1868177 = 1401133) B1401133
theorem B1245587 : Blo 1244440 1245587 := bstep (se 1 (by rfl) ⟨934190, by rfl⟩ : syracuseStep 1245587 = 1868381) B1868381
theorem B1868195 : Blo 1244440 1868195 := bstep (se 1 (by rfl) ⟨1401146, by rfl⟩ : syracuseStep 1868195 = 2802293) B2802293
theorem B1245603 : Blo 1244440 1245603 := bstep (se 1 (by rfl) ⟨934202, by rfl⟩ : syracuseStep 1245603 = 1868405) B1868405
theorem B1245619 : Blo 1244440 1245619 := bstep (se 1 (by rfl) ⟨934214, by rfl⟩ : syracuseStep 1245619 = 1868429) B1868429
theorem B1868225 : Blo 1244440 1868225 := bstep (se 2 (by rfl) ⟨700584, by rfl⟩ : syracuseStep 1868225 = 1401169) B1401169
theorem B1245635 : Blo 1244440 1245635 := bstep (se 1 (by rfl) ⟨934226, by rfl⟩ : syracuseStep 1245635 = 1868453) B1868453
theorem B1868243 : Blo 1244440 1868243 := bstep (se 1 (by rfl) ⟨1401182, by rfl⟩ : syracuseStep 1868243 = 2802365) B2802365
theorem B1245651 : Blo 1244440 1245651 := bstep (se 1 (by rfl) ⟨934238, by rfl⟩ : syracuseStep 1245651 = 1868477) B1868477
theorem B1245667 : Blo 1244440 1245667 := bstep (se 1 (by rfl) ⟨934250, by rfl⟩ : syracuseStep 1245667 = 1868501) B1868501
theorem B3154403 : Blo 1244440 3154403 := bstep (se 1 (by rfl) ⟨2365802, by rfl⟩ : syracuseStep 3154403 = 4731605) B4731605
theorem B1868273 : Blo 1244440 1868273 := bstep (se 2 (by rfl) ⟨700602, by rfl⟩ : syracuseStep 1868273 = 1401205) B1401205
theorem B3547633 : Blo 1244440 3547633 := bstep (se 2 (by rfl) ⟨1330362, by rfl⟩ : syracuseStep 3547633 = 2660725) B2660725
theorem B1401331 : Blo 1244440 1401331 := bstep (se 1 (by rfl) ⟨1050998, by rfl⟩ : syracuseStep 1401331 = 2101997) B2101997
theorem B1245683 : Blo 1244440 1245683 := bstep (se 1 (by rfl) ⟨934262, by rfl⟩ : syracuseStep 1245683 = 1868525) B1868525
theorem B1868291 : Blo 1244440 1868291 := bstep (se 1 (by rfl) ⟨1401218, by rfl⟩ : syracuseStep 1868291 = 2802437) B2802437
theorem B1245699 : Blo 1244440 1245699 := bstep (se 1 (by rfl) ⟨934274, by rfl⟩ : syracuseStep 1245699 = 1868549) B1868549
theorem B7094789 : Blo 1244440 7094789 := bstep (se 4 (by rfl) ⟨665136, by rfl⟩ : syracuseStep 7094789 = 1330273) B1330273
theorem B1245715 : Blo 1244440 1245715 := bstep (se 1 (by rfl) ⟨934286, by rfl⟩ : syracuseStep 1245715 = 1868573) B1868573
theorem B1868321 : Blo 1244440 1868321 := bstep (se 2 (by rfl) ⟨700620, by rfl⟩ : syracuseStep 1868321 = 1401241) B1401241
theorem B1245731 : Blo 1244440 1245731 := bstep (se 1 (by rfl) ⟨934298, by rfl⟩ : syracuseStep 1245731 = 1868597) B1868597
theorem B1868339 : Blo 1244440 1868339 := bstep (se 1 (by rfl) ⟨1401254, by rfl⟩ : syracuseStep 1868339 = 2802509) B2802509
theorem B1245747 : Blo 1244440 1245747 := bstep (se 1 (by rfl) ⟨934310, by rfl⟩ : syracuseStep 1245747 = 1868621) B1868621
theorem B1245763 : Blo 1244440 1245763 := bstep (se 1 (by rfl) ⟨934322, by rfl⟩ : syracuseStep 1245763 = 1868645) B1868645
theorem B9093701 : Blo 1244440 9093701 := bstep (se 4 (by rfl) ⟨852534, by rfl⟩ : syracuseStep 9093701 = 1705069) B1705069
theorem B4203089 : Blo 1244440 4203089 := bstep (se 2 (by rfl) ⟨1576158, by rfl⟩ : syracuseStep 4203089 = 3152317) B3152317
theorem B2802257 : Blo 1244440 2802257 := bstep (se 2 (by rfl) ⟨1050846, by rfl⟩ : syracuseStep 2802257 = 2101693) B2101693
theorem B1868369 : Blo 1244440 1868369 := bstep (se 2 (by rfl) ⟨700638, by rfl⟩ : syracuseStep 1868369 = 1401277) B1401277
theorem B1245779 : Blo 1244440 1245779 := bstep (se 1 (by rfl) ⟨934334, by rfl⟩ : syracuseStep 1245779 = 1868669) B1868669
theorem B2802275 : Blo 1244440 2802275 := bstep (se 1 (by rfl) ⟨2101706, by rfl⟩ : syracuseStep 2802275 = 4203413) B4203413
theorem B1868387 : Blo 1244440 1868387 := bstep (se 1 (by rfl) ⟨1401290, by rfl⟩ : syracuseStep 1868387 = 2802581) B2802581
theorem B1245795 : Blo 1244440 1245795 := bstep (se 1 (by rfl) ⟨934346, by rfl⟩ : syracuseStep 1245795 = 1868693) B1868693
theorem B1245811 : Blo 1244440 1245811 := bstep (se 1 (by rfl) ⟨934358, by rfl⟩ : syracuseStep 1245811 = 1868717) B1868717
theorem B1868417 : Blo 1244440 1868417 := bstep (se 2 (by rfl) ⟨700656, by rfl⟩ : syracuseStep 1868417 = 1401313) B1401313
theorem B1401475 : Blo 1244440 1401475 := bstep (se 1 (by rfl) ⟨1051106, by rfl⟩ : syracuseStep 1401475 = 2102213) B2102213
theorem B1245827 : Blo 1244440 1245827 := bstep (se 1 (by rfl) ⟨934370, by rfl⟩ : syracuseStep 1245827 = 1868741) B1868741
theorem B3547793 : Blo 1244440 3547793 := bstep (se 2 (by rfl) ⟨1330422, by rfl⟩ : syracuseStep 3547793 = 2660845) B2660845
theorem B1868435 : Blo 1244440 1868435 := bstep (se 1 (by rfl) ⟨1401326, by rfl⟩ : syracuseStep 1868435 = 2802653) B2802653
theorem B1245843 : Blo 1244440 1245843 := bstep (se 1 (by rfl) ⟨934382, by rfl⟩ : syracuseStep 1245843 = 1868765) B1868765
theorem B1245859 : Blo 1244440 1245859 := bstep (se 1 (by rfl) ⟨934394, by rfl⟩ : syracuseStep 1245859 = 1868789) B1868789
theorem B7570097 : Blo 1244440 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B1868465 : Blo 1244440 1868465 := bstep (se 2 (by rfl) ⟨700674, by rfl⟩ : syracuseStep 1868465 = 1401349) B1401349
theorem B1245875 : Blo 1244440 1245875 := bstep (se 1 (by rfl) ⟨934406, by rfl⟩ : syracuseStep 1245875 = 1868813) B1868813
theorem B1868483 : Blo 1244440 1868483 := bstep (se 1 (by rfl) ⟨1401362, by rfl⟩ : syracuseStep 1868483 = 2802725) B2802725
theorem B1245891 : Blo 1244440 1245891 := bstep (se 1 (by rfl) ⟨934418, by rfl⟩ : syracuseStep 1245891 = 1868837) B1868837
theorem B1245907 : Blo 1244440 1245907 := bstep (se 1 (by rfl) ⟨934430, by rfl⟩ : syracuseStep 1245907 = 1868861) B1868861
theorem B1868513 : Blo 1244440 1868513 := bstep (se 2 (by rfl) ⟨700692, by rfl⟩ : syracuseStep 1868513 = 1401385) B1401385
theorem B1245923 : Blo 1244440 1245923 := bstep (se 1 (by rfl) ⟨934442, by rfl⟩ : syracuseStep 1245923 = 1868885) B1868885
theorem B1868531 : Blo 1244440 1868531 := bstep (se 1 (by rfl) ⟨1401398, by rfl⟩ : syracuseStep 1868531 = 2802797) B2802797
theorem B1245939 : Blo 1244440 1245939 := bstep (se 1 (by rfl) ⟨934454, by rfl⟩ : syracuseStep 1245939 = 1868909) B1868909
theorem B3547907 : Blo 1244440 3547907 := bstep (se 1 (by rfl) ⟨2660930, by rfl⟩ : syracuseStep 3547907 = 5321861) B5321861
theorem B1245955 : Blo 1244440 1245955 := bstep (se 1 (by rfl) ⟨934466, by rfl⟩ : syracuseStep 1245955 = 1868933) B1868933
theorem B1868561 : Blo 1244440 1868561 := bstep (se 2 (by rfl) ⟨700710, by rfl⟩ : syracuseStep 1868561 = 1401421) B1401421
theorem B1401619 : Blo 1244440 1401619 := bstep (se 1 (by rfl) ⟨1051214, by rfl⟩ : syracuseStep 1401619 = 2102429) B2102429
theorem B1245971 : Blo 1244440 1245971 := bstep (se 1 (by rfl) ⟨934478, by rfl⟩ : syracuseStep 1245971 = 1868957) B1868957
theorem B1868579 : Blo 1244440 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B1245987 : Blo 1244440 1245987 := bstep (se 1 (by rfl) ⟨934490, by rfl⟩ : syracuseStep 1245987 = 1868981) B1868981
theorem B1246003 : Blo 1244440 1246003 := bstep (se 1 (by rfl) ⟨934502, by rfl⟩ : syracuseStep 1246003 = 1869005) B1869005
theorem B1868609 : Blo 1244440 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B1246019 : Blo 1244440 1246019 := bstep (se 1 (by rfl) ⟨934514, by rfl⟩ : syracuseStep 1246019 = 1869029) B1869029
theorem B1868627 : Blo 1244440 1868627 := bstep (se 1 (by rfl) ⟨1401470, by rfl⟩ : syracuseStep 1868627 = 2802941) B2802941
theorem B1246035 : Blo 1244440 1246035 := bstep (se 1 (by rfl) ⟨934526, by rfl⟩ : syracuseStep 1246035 = 1869053) B1869053
theorem B1246051 : Blo 1244440 1246051 := bstep (se 1 (by rfl) ⟨934538, by rfl⟩ : syracuseStep 1246051 = 1869077) B1869077
theorem B2802545 : Blo 1244440 2802545 := bstep (se 2 (by rfl) ⟨1050954, by rfl⟩ : syracuseStep 2802545 = 2101909) B2101909
theorem B1868657 : Blo 1244440 1868657 := bstep (se 2 (by rfl) ⟨700746, by rfl⟩ : syracuseStep 1868657 = 1401493) B1401493
theorem B1246067 : Blo 1244440 1246067 := bstep (se 1 (by rfl) ⟨934550, by rfl⟩ : syracuseStep 1246067 = 1869101) B1869101
theorem B2802563 : Blo 1244440 2802563 := bstep (se 1 (by rfl) ⟨2101922, by rfl⟩ : syracuseStep 2802563 = 4203845) B4203845
theorem B1868675 : Blo 1244440 1868675 := bstep (se 1 (by rfl) ⟨1401506, by rfl⟩ : syracuseStep 1868675 = 2803013) B2803013
theorem B1246083 : Blo 1244440 1246083 := bstep (se 1 (by rfl) ⟨934562, by rfl⟩ : syracuseStep 1246083 = 1869125) B1869125
theorem B1246099 : Blo 1244440 1246099 := bstep (se 1 (by rfl) ⟨934574, by rfl⟩ : syracuseStep 1246099 = 1869149) B1869149
theorem B1868705 : Blo 1244440 1868705 := bstep (se 2 (by rfl) ⟨700764, by rfl⟩ : syracuseStep 1868705 = 1401529) B1401529
theorem B4490147 : Blo 1244440 4490147 := bstep (se 1 (by rfl) ⟨3367610, by rfl⟩ : syracuseStep 4490147 = 6735221) B6735221
theorem B6480803 : Blo 1244440 6480803 := bstep (se 1 (by rfl) ⟨4860602, by rfl⟩ : syracuseStep 6480803 = 9721205) B9721205
theorem B1401763 : Blo 1244440 1401763 := bstep (se 1 (by rfl) ⟨1051322, by rfl⟩ : syracuseStep 1401763 = 2102645) B2102645
theorem B1246115 : Blo 1244440 1246115 := bstep (se 1 (by rfl) ⟨934586, by rfl⟩ : syracuseStep 1246115 = 1869173) B1869173
theorem B1868723 : Blo 1244440 1868723 := bstep (se 1 (by rfl) ⟨1401542, by rfl⟩ : syracuseStep 1868723 = 2803085) B2803085
theorem B1246131 : Blo 1244440 1246131 := bstep (se 1 (by rfl) ⟨934598, by rfl⟩ : syracuseStep 1246131 = 1869197) B1869197
theorem B1246147 : Blo 1244440 1246147 := bstep (se 1 (by rfl) ⟨934610, by rfl⟩ : syracuseStep 1246147 = 1869221) B1869221
theorem B1868753 : Blo 1244440 1868753 := bstep (se 2 (by rfl) ⟨700782, by rfl⟩ : syracuseStep 1868753 = 1401565) B1401565
theorem B1246163 : Blo 1244440 1246163 := bstep (se 1 (by rfl) ⟨934622, by rfl⟩ : syracuseStep 1246163 = 1869245) B1869245
theorem B1868771 : Blo 1244440 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B1246179 : Blo 1244440 1246179 := bstep (se 1 (by rfl) ⟨934634, by rfl⟩ : syracuseStep 1246179 = 1869269) B1869269
theorem B1246195 : Blo 1244440 1246195 := bstep (se 1 (by rfl) ⟨934646, by rfl⟩ : syracuseStep 1246195 = 1869293) B1869293
theorem B1868801 : Blo 1244440 1868801 := bstep (se 2 (by rfl) ⟨700800, by rfl⟩ : syracuseStep 1868801 = 1401601) B1401601
theorem B1246211 : Blo 1244440 1246211 := bstep (se 1 (by rfl) ⟨934658, by rfl⟩ : syracuseStep 1246211 = 1869317) B1869317
theorem B1868819 : Blo 1244440 1868819 := bstep (se 1 (by rfl) ⟨1401614, by rfl⟩ : syracuseStep 1868819 = 2803229) B2803229
theorem B1246227 : Blo 1244440 1246227 := bstep (se 1 (by rfl) ⟨934670, by rfl⟩ : syracuseStep 1246227 = 1869341) B1869341
theorem B1246243 : Blo 1244440 1246243 := bstep (se 1 (by rfl) ⟨934682, by rfl⟩ : syracuseStep 1246243 = 1869365) B1869365
theorem B1868849 : Blo 1244440 1868849 := bstep (se 2 (by rfl) ⟨700818, by rfl⟩ : syracuseStep 1868849 = 1401637) B1401637
theorem B1401907 : Blo 1244440 1401907 := bstep (se 1 (by rfl) ⟨1051430, by rfl⟩ : syracuseStep 1401907 = 2102861) B2102861
theorem B57500725 : Blo 1244440 57500725 := bstep (se 5 (by rfl) ⟨2695346, by rfl⟩ : syracuseStep 57500725 = 5390693) B5390693
theorem B1246259 : Blo 1244440 1246259 := bstep (se 1 (by rfl) ⟨934694, by rfl⟩ : syracuseStep 1246259 = 1869389) B1869389
theorem B1868867 : Blo 1244440 1868867 := bstep (se 1 (by rfl) ⟨1401650, by rfl⟩ : syracuseStep 1868867 = 2803301) B2803301
theorem B1246275 : Blo 1244440 1246275 := bstep (se 1 (by rfl) ⟨934706, by rfl⟩ : syracuseStep 1246275 = 1869413) B1869413
theorem B1246291 : Blo 1244440 1246291 := bstep (se 1 (by rfl) ⟨934718, by rfl⟩ : syracuseStep 1246291 = 1869437) B1869437
theorem B1868897 : Blo 1244440 1868897 := bstep (se 2 (by rfl) ⟨700836, by rfl⟩ : syracuseStep 1868897 = 1401673) B1401673
theorem B1246307 : Blo 1244440 1246307 := bstep (se 1 (by rfl) ⟨934730, by rfl⟩ : syracuseStep 1246307 = 1869461) B1869461
theorem B4203629 : Blo 1244440 4203629 := bstep (se 3 (by rfl) ⟨788180, by rfl⟩ : syracuseStep 4203629 = 1576361) B1576361
theorem B1868915 : Blo 1244440 1868915 := bstep (se 1 (by rfl) ⟨1401686, by rfl⟩ : syracuseStep 1868915 = 2803373) B2803373
theorem B1246323 : Blo 1244440 1246323 := bstep (se 1 (by rfl) ⟨934742, by rfl⟩ : syracuseStep 1246323 = 1869485) B1869485
theorem B1246339 : Blo 1244440 1246339 := bstep (se 1 (by rfl) ⟨934754, by rfl⟩ : syracuseStep 1246339 = 1869509) B1869509
theorem B2802833 : Blo 1244440 2802833 := bstep (se 2 (by rfl) ⟨1051062, by rfl⟩ : syracuseStep 2802833 = 2102125) B2102125
theorem B1868945 : Blo 1244440 1868945 := bstep (se 2 (by rfl) ⟨700854, by rfl⟩ : syracuseStep 1868945 = 1401709) B1401709
theorem B1246355 : Blo 1244440 1246355 := bstep (se 1 (by rfl) ⟨934766, by rfl⟩ : syracuseStep 1246355 = 1869533) B1869533
theorem B4203683 : Blo 1244440 4203683 := bstep (se 1 (by rfl) ⟨3152762, by rfl⟩ : syracuseStep 4203683 = 6305525) B6305525
theorem B2802851 : Blo 1244440 2802851 := bstep (se 1 (by rfl) ⟨2102138, by rfl⟩ : syracuseStep 2802851 = 4204277) B4204277
theorem B1868963 : Blo 1244440 1868963 := bstep (se 1 (by rfl) ⟨1401722, by rfl⟩ : syracuseStep 1868963 = 2803445) B2803445
theorem B1246371 : Blo 1244440 1246371 := bstep (se 1 (by rfl) ⟨934778, by rfl⟩ : syracuseStep 1246371 = 1869557) B1869557
theorem B2131121 : Blo 1244440 2131121 := bstep (se 2 (by rfl) ⟨799170, by rfl⟩ : syracuseStep 2131121 = 1598341) B1598341
theorem B1246387 : Blo 1244440 1246387 := bstep (se 1 (by rfl) ⟨934790, by rfl⟩ : syracuseStep 1246387 = 1869581) B1869581
theorem B1868993 : Blo 1244440 1868993 := bstep (se 2 (by rfl) ⟨700872, by rfl⟩ : syracuseStep 1868993 = 1401745) B1401745
theorem B1402051 : Blo 1244440 1402051 := bstep (se 1 (by rfl) ⟨1051538, by rfl⟩ : syracuseStep 1402051 = 2103077) B2103077
theorem B1246403 : Blo 1244440 1246403 := bstep (se 1 (by rfl) ⟨934802, by rfl⟩ : syracuseStep 1246403 = 1869605) B1869605
theorem B1869011 : Blo 1244440 1869011 := bstep (se 1 (by rfl) ⟨1401758, by rfl⟩ : syracuseStep 1869011 = 2803517) B2803517
theorem B1246419 : Blo 1244440 1246419 := bstep (se 1 (by rfl) ⟨934814, by rfl⟩ : syracuseStep 1246419 = 1869629) B1869629
theorem B1246435 : Blo 1244440 1246435 := bstep (se 1 (by rfl) ⟨934826, by rfl⟩ : syracuseStep 1246435 = 1869653) B1869653
theorem B1869041 : Blo 1244440 1869041 := bstep (se 2 (by rfl) ⟨700890, by rfl⟩ : syracuseStep 1869041 = 1401781) B1401781
theorem B1869059 : Blo 1244440 1869059 := bstep (se 1 (by rfl) ⟨1401794, by rfl⟩ : syracuseStep 1869059 = 2803589) B2803589
theorem B1869089 : Blo 1244440 1869089 := bstep (se 2 (by rfl) ⟨700908, by rfl⟩ : syracuseStep 1869089 = 1401817) B1401817
theorem B1869107 : Blo 1244440 1869107 := bstep (se 1 (by rfl) ⟨1401830, by rfl⟩ : syracuseStep 1869107 = 2803661) B2803661
theorem B1869137 : Blo 1244440 1869137 := bstep (se 2 (by rfl) ⟨700926, by rfl⟩ : syracuseStep 1869137 = 1401853) B1401853
theorem B1402195 : Blo 1244440 1402195 := bstep (se 1 (by rfl) ⟨1051646, by rfl⟩ : syracuseStep 1402195 = 2103293) B2103293
theorem B3990883 : Blo 1244440 3990883 := bstep (se 1 (by rfl) ⟨2993162, by rfl⟩ : syracuseStep 3990883 = 5986325) B5986325
theorem B1869155 : Blo 1244440 1869155 := bstep (se 1 (by rfl) ⟨1401866, by rfl⟩ : syracuseStep 1869155 = 2803733) B2803733
theorem B1869185 : Blo 1244440 1869185 := bstep (se 2 (by rfl) ⟨700944, by rfl⟩ : syracuseStep 1869185 = 1401889) B1401889
theorem B1869203 : Blo 1244440 1869203 := bstep (se 1 (by rfl) ⟨1401902, by rfl⟩ : syracuseStep 1869203 = 2803805) B2803805
theorem B4203953 : Blo 1244440 4203953 := bstep (se 2 (by rfl) ⟨1576482, by rfl⟩ : syracuseStep 4203953 = 3152965) B3152965
theorem B2803121 : Blo 1244440 2803121 := bstep (se 2 (by rfl) ⟨1051170, by rfl⟩ : syracuseStep 2803121 = 2102341) B2102341
theorem B1869233 : Blo 1244440 1869233 := bstep (se 2 (by rfl) ⟨700962, by rfl⟩ : syracuseStep 1869233 = 1401925) B1401925
theorem B2803139 : Blo 1244440 2803139 := bstep (se 1 (by rfl) ⟨2102354, by rfl⟩ : syracuseStep 2803139 = 4204709) B4204709
theorem B1869251 : Blo 1244440 1869251 := bstep (se 1 (by rfl) ⟨1401938, by rfl⟩ : syracuseStep 1869251 = 2803877) B2803877
theorem B1869281 : Blo 1244440 1869281 := bstep (se 2 (by rfl) ⟨700980, by rfl⟩ : syracuseStep 1869281 = 1401961) B1401961
theorem B3991025 : Blo 1244440 3991025 := bstep (se 2 (by rfl) ⟨1496634, by rfl⟩ : syracuseStep 3991025 = 2993269) B2993269
theorem B1869299 : Blo 1244440 1869299 := bstep (se 1 (by rfl) ⟨1401974, by rfl⟩ : syracuseStep 1869299 = 2803949) B2803949
theorem B1869329 : Blo 1244440 1869329 := bstep (se 2 (by rfl) ⟨700998, by rfl⟩ : syracuseStep 1869329 = 1401997) B1401997
theorem B1869347 : Blo 1244440 1869347 := bstep (se 1 (by rfl) ⟨1402010, by rfl⟩ : syracuseStep 1869347 = 2804021) B2804021
theorem B1869377 : Blo 1244440 1869377 := bstep (se 2 (by rfl) ⟨701016, by rfl⟩ : syracuseStep 1869377 = 1402033) B1402033
theorem B1869395 : Blo 1244440 1869395 := bstep (se 1 (by rfl) ⟨1402046, by rfl⟩ : syracuseStep 1869395 = 2804093) B2804093
theorem B3368561 : Blo 1244440 3368561 := bstep (se 2 (by rfl) ⟨1263210, by rfl⟩ : syracuseStep 3368561 = 2526421) B2526421
theorem B1869425 : Blo 1244440 1869425 := bstep (se 2 (by rfl) ⟨701034, by rfl⟩ : syracuseStep 1869425 = 1402069) B1402069
theorem B1869443 : Blo 1244440 1869443 := bstep (se 1 (by rfl) ⟨1402082, by rfl⟩ : syracuseStep 1869443 = 2804165) B2804165
theorem B1869473 : Blo 1244440 1869473 := bstep (se 2 (by rfl) ⟨701052, by rfl⟩ : syracuseStep 1869473 = 1402105) B1402105
theorem B2991779 : Blo 1244440 2991779 := bstep (se 1 (by rfl) ⟨2243834, by rfl⟩ : syracuseStep 2991779 = 4487669) B4487669
theorem B1869491 : Blo 1244440 1869491 := bstep (se 1 (by rfl) ⟨1402118, by rfl⟩ : syracuseStep 1869491 = 2804237) B2804237
theorem B14771909 : Blo 1244440 14771909 := bstep (se 4 (by rfl) ⟨1384866, by rfl⟩ : syracuseStep 14771909 = 2769733) B2769733
theorem B4261585 : Blo 1244440 4261585 := bstep (se 2 (by rfl) ⟨1598094, by rfl⟩ : syracuseStep 4261585 = 3196189) B3196189
theorem B2803409 : Blo 1244440 2803409 := bstep (se 2 (by rfl) ⟨1051278, by rfl⟩ : syracuseStep 2803409 = 2102557) B2102557
theorem B1869521 : Blo 1244440 1869521 := bstep (se 2 (by rfl) ⟨701070, by rfl⟩ : syracuseStep 1869521 = 1402141) B1402141
theorem B2803427 : Blo 1244440 2803427 := bstep (se 1 (by rfl) ⟨2102570, by rfl⟩ : syracuseStep 2803427 = 4205141) B4205141
theorem B1869539 : Blo 1244440 1869539 := bstep (se 1 (by rfl) ⟨1402154, by rfl⟩ : syracuseStep 1869539 = 2804309) B2804309
theorem B3548909 : Blo 1244440 3548909 := bstep (se 3 (by rfl) ⟨665420, by rfl⟩ : syracuseStep 3548909 = 1330841) B1330841
theorem B1869569 : Blo 1244440 1869569 := bstep (se 2 (by rfl) ⟨701088, by rfl⟩ : syracuseStep 1869569 = 1402177) B1402177
theorem B1918739 : Blo 1244440 1918739 := bstep (se 1 (by rfl) ⟨1439054, by rfl⟩ : syracuseStep 1918739 = 2878109) B2878109
theorem B1869587 : Blo 1244440 1869587 := bstep (se 1 (by rfl) ⟨1402190, by rfl⟩ : syracuseStep 1869587 = 2804381) B2804381
theorem B6301475 : Blo 1244440 6301475 := bstep (se 1 (by rfl) ⟨4726106, by rfl⟩ : syracuseStep 6301475 = 9452213) B9452213
theorem B1869617 : Blo 1244440 1869617 := bstep (se 2 (by rfl) ⟨701106, by rfl⟩ : syracuseStep 1869617 = 1402213) B1402213
theorem B1869635 : Blo 1244440 1869635 := bstep (se 1 (by rfl) ⟨1402226, by rfl⟩ : syracuseStep 1869635 = 2804453) B2804453
theorem B2991971 : Blo 1244440 2991971 := bstep (se 1 (by rfl) ⟨2243978, by rfl⟩ : syracuseStep 2991971 = 4487957) B4487957
theorem B3786605 : Blo 1244440 3786605 := bstep (se 3 (by rfl) ⟨709988, by rfl⟩ : syracuseStep 3786605 = 1419977) B1419977
theorem B4728689 : Blo 1244440 4728689 := bstep (se 2 (by rfl) ⟨1773258, by rfl⟩ : syracuseStep 4728689 = 3546517) B3546517
theorem B1329043 : Blo 1244440 1329043 := bstep (se 1 (by rfl) ⟨996782, by rfl⟩ : syracuseStep 1329043 = 1993565) B1993565
theorem B3549091 : Blo 1244440 3549091 := bstep (se 1 (by rfl) ⟨2661818, by rfl⟩ : syracuseStep 3549091 = 5323637) B5323637
theorem B2992067 : Blo 1244440 2992067 := bstep (se 1 (by rfl) ⟨2244050, by rfl⟩ : syracuseStep 2992067 = 4488101) B4488101
theorem B4204493 : Blo 1244440 4204493 := bstep (se 3 (by rfl) ⟨788342, by rfl⟩ : syracuseStep 4204493 = 1576685) B1576685
theorem B1796051 : Blo 1244440 1796051 := bstep (se 1 (by rfl) ⟨1347038, by rfl⟩ : syracuseStep 1796051 = 2694077) B2694077
theorem B2803697 : Blo 1244440 2803697 := bstep (se 2 (by rfl) ⟨1051386, by rfl⟩ : syracuseStep 2803697 = 2102773) B2102773
theorem B1419251 : Blo 1244440 1419251 := bstep (se 1 (by rfl) ⟨1064438, by rfl⟩ : syracuseStep 1419251 = 2128877) B2128877
theorem B4204547 : Blo 1244440 4204547 := bstep (se 1 (by rfl) ⟨3153410, by rfl⟩ : syracuseStep 4204547 = 6306821) B6306821
theorem B1894403 : Blo 1244440 1894403 := bstep (se 1 (by rfl) ⟨1420802, by rfl⟩ : syracuseStep 1894403 = 2841605) B2841605
theorem B2803715 : Blo 1244440 2803715 := bstep (se 1 (by rfl) ⟨2102786, by rfl⟩ : syracuseStep 2803715 = 4205573) B4205573
theorem B3549251 : Blo 1244440 3549251 := bstep (se 1 (by rfl) ⟨2661938, by rfl⟩ : syracuseStep 3549251 = 5323877) B5323877
theorem B9463877 : Blo 1244440 9463877 := bstep (se 4 (by rfl) ⟨887238, by rfl⟩ : syracuseStep 9463877 = 1774477) B1774477
theorem B1796195 : Blo 1244440 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B7981253 : Blo 1244440 7981253 := bstep (se 4 (by rfl) ⟨748242, by rfl⟩ : syracuseStep 7981253 = 1496485) B1496485
theorem B4204817 : Blo 1244440 4204817 := bstep (se 2 (by rfl) ⟨1576806, by rfl⟩ : syracuseStep 4204817 = 3153613) B3153613
theorem B2803985 : Blo 1244440 2803985 := bstep (se 2 (by rfl) ⟨1051494, by rfl⟩ : syracuseStep 2803985 = 2102989) B2102989
theorem B2804003 : Blo 1244440 2804003 := bstep (se 1 (by rfl) ⟨2103002, by rfl⟩ : syracuseStep 2804003 = 4206005) B4206005
theorem B1329491 : Blo 1244440 1329491 := bstep (se 1 (by rfl) ⟨997118, by rfl⟩ : syracuseStep 1329491 = 1994237) B1994237
theorem B1575283 : Blo 1244440 1575283 := bstep (se 1 (by rfl) ⟨1181462, by rfl⟩ : syracuseStep 1575283 = 2362925) B2362925
theorem B1575379 : Blo 1244440 1575379 := bstep (se 1 (by rfl) ⟨1181534, by rfl⟩ : syracuseStep 1575379 = 2363069) B2363069
theorem B1796563 : Blo 1244440 1796563 := bstep (se 1 (by rfl) ⟨1347422, by rfl⟩ : syracuseStep 1796563 = 2694845) B2694845
theorem B3787249 : Blo 1244440 3787249 := bstep (se 2 (by rfl) ⟨1420218, by rfl⟩ : syracuseStep 3787249 = 2840437) B2840437
theorem B2804273 : Blo 1244440 2804273 := bstep (se 2 (by rfl) ⟨1051602, by rfl⟩ : syracuseStep 2804273 = 2103205) B2103205
theorem B2804291 : Blo 1244440 2804291 := bstep (se 1 (by rfl) ⟨2103218, by rfl⟩ : syracuseStep 2804291 = 4206437) B4206437
theorem B6302285 : Blo 1244440 6302285 := bstep (se 3 (by rfl) ⟨1181678, by rfl⟩ : syracuseStep 6302285 = 2363357) B2363357
theorem B1772131 : Blo 1244440 1772131 := bstep (se 1 (by rfl) ⟨1329098, by rfl⟩ : syracuseStep 1772131 = 2658197) B2658197
theorem B3197585 : Blo 1244440 3197585 := bstep (se 2 (by rfl) ⟨1199094, by rfl⟩ : syracuseStep 3197585 = 2398189) B2398189
theorem B8981189 : Blo 1244440 8981189 := bstep (se 4 (by rfl) ⟨841986, by rfl⟩ : syracuseStep 8981189 = 1683973) B1683973
theorem B4205357 : Blo 1244440 4205357 := bstep (se 3 (by rfl) ⟨788504, by rfl⟩ : syracuseStep 4205357 = 1577009) B1577009
theorem B2100019 : Blo 1244440 2100019 := bstep (se 1 (by rfl) ⟨1575014, by rfl⟩ : syracuseStep 2100019 = 3150029) B3150029
theorem B4205411 : Blo 1244440 4205411 := bstep (se 1 (by rfl) ⟨3154058, by rfl⟩ : syracuseStep 4205411 = 6308117) B6308117
theorem B2100161 : Blo 1244440 2100161 := bstep (se 2 (by rfl) ⟨787560, by rfl⟩ : syracuseStep 2100161 = 1575121) B1575121
theorem B1575875 : Blo 1244440 1575875 := bstep (se 1 (by rfl) ⟨1181906, by rfl⟩ : syracuseStep 1575875 = 2363813) B2363813
theorem B10243043 : Blo 1244440 10243043 := bstep (se 1 (by rfl) ⟨7682282, by rfl⟩ : syracuseStep 10243043 = 15364565) B15364565
theorem B7973923 : Blo 1244440 7973923 := bstep (se 1 (by rfl) ⟨5980442, by rfl⟩ : syracuseStep 7973923 = 11960885) B11960885
theorem B2100289 : Blo 1244440 2100289 := bstep (se 2 (by rfl) ⟨787608, by rfl⟩ : syracuseStep 2100289 = 1575217) B1575217
theorem B1772609 : Blo 1244440 1772609 := bstep (se 2 (by rfl) ⟨664728, by rfl⟩ : syracuseStep 1772609 = 1329457) B1329457
theorem B2100323 : Blo 1244440 2100323 := bstep (se 1 (by rfl) ⟨1575242, by rfl⟩ : syracuseStep 2100323 = 3150485) B3150485
theorem B4205681 : Blo 1244440 4205681 := bstep (se 2 (by rfl) ⟨1577130, by rfl⟩ : syracuseStep 4205681 = 3154261) B3154261
theorem B1993891 : Blo 1244440 1993891 := bstep (se 1 (by rfl) ⟨1495418, by rfl⟩ : syracuseStep 1993891 = 2990837) B2990837
theorem B1772723 : Blo 1244440 1772723 := bstep (se 1 (by rfl) ⟨1329542, by rfl⟩ : syracuseStep 1772723 = 2659085) B2659085
theorem B2100451 : Blo 1244440 2100451 := bstep (se 1 (by rfl) ⟨1575338, by rfl⟩ : syracuseStep 2100451 = 3150677) B3150677
theorem B1772803 : Blo 1244440 1772803 := bstep (se 1 (by rfl) ⟨1329602, by rfl⟩ : syracuseStep 1772803 = 2659205) B2659205
theorem B4730147 : Blo 1244440 4730147 := bstep (se 1 (by rfl) ⟨3547610, by rfl⟩ : syracuseStep 4730147 = 7095221) B7095221
theorem B2100593 : Blo 1244440 2100593 := bstep (se 2 (by rfl) ⟨787722, by rfl⟩ : syracuseStep 2100593 = 1575445) B1575445
theorem B1994129 : Blo 1244440 1994129 := bstep (se 2 (by rfl) ⟨747798, by rfl⟩ : syracuseStep 1994129 = 1495597) B1495597
theorem B2100721 : Blo 1244440 2100721 := bstep (se 2 (by rfl) ⟨787770, by rfl⟩ : syracuseStep 2100721 = 1575541) B1575541
theorem B2100755 : Blo 1244440 2100755 := bstep (se 1 (by rfl) ⟨1575566, by rfl⟩ : syracuseStep 2100755 = 3151133) B3151133
theorem B1994339 : Blo 1244440 1994339 := bstep (se 1 (by rfl) ⟨1495754, by rfl⟩ : syracuseStep 1994339 = 2991509) B2991509
theorem B1576579 : Blo 1244440 1576579 := bstep (se 1 (by rfl) ⟨1182434, by rfl⟩ : syracuseStep 1576579 = 2364869) B2364869
theorem B4206221 : Blo 1244440 4206221 := bstep (se 3 (by rfl) ⟨788666, by rfl⟩ : syracuseStep 4206221 = 1577333) B1577333
theorem B2100883 : Blo 1244440 2100883 := bstep (se 1 (by rfl) ⟨1575662, by rfl⟩ : syracuseStep 2100883 = 3151325) B3151325
theorem B1330867 : Blo 1244440 1330867 := bstep (se 1 (by rfl) ⟨998150, by rfl⟩ : syracuseStep 1330867 = 1996301) B1996301
theorem B4206275 : Blo 1244440 4206275 := bstep (se 1 (by rfl) ⟨3154706, by rfl⟩ : syracuseStep 4206275 = 6309413) B6309413
theorem B2363107 : Blo 1244440 2363107 := bstep (se 1 (by rfl) ⟨1772330, by rfl⟩ : syracuseStep 2363107 = 3544661) B3544661
theorem B1576675 : Blo 1244440 1576675 := bstep (se 1 (by rfl) ⟨1182506, by rfl⟩ : syracuseStep 1576675 = 2365013) B2365013
theorem B2101025 : Blo 1244440 2101025 := bstep (se 2 (by rfl) ⟨787884, by rfl⟩ : syracuseStep 2101025 = 1575769) B1575769
theorem B1773361 : Blo 1244440 1773361 := bstep (se 2 (by rfl) ⟨665010, by rfl⟩ : syracuseStep 1773361 = 1330021) B1330021
theorem B2993969 : Blo 1244440 2993969 := bstep (se 2 (by rfl) ⟨1122738, by rfl⟩ : syracuseStep 2993969 = 2245477) B2245477
theorem B5984077 : Blo 1244440 5984077 := bstep (se 3 (by rfl) ⟨1122014, by rfl⟩ : syracuseStep 5984077 = 2244029) B2244029
theorem B5320561 : Blo 1244440 5320561 := bstep (se 2 (by rfl) ⟨1995210, by rfl⟩ : syracuseStep 5320561 = 3990421) B3990421
theorem B2101153 : Blo 1244440 2101153 := bstep (se 2 (by rfl) ⟨787932, by rfl⟩ : syracuseStep 2101153 = 1575865) B1575865
theorem B2101187 : Blo 1244440 2101187 := bstep (se 1 (by rfl) ⟨1575890, by rfl⟩ : syracuseStep 2101187 = 3151781) B3151781
theorem B4206545 : Blo 1244440 4206545 := bstep (se 2 (by rfl) ⟨1577454, by rfl⟩ : syracuseStep 4206545 = 3154909) B3154909
theorem B2101315 : Blo 1244440 2101315 := bstep (se 1 (by rfl) ⟨1575986, by rfl⟩ : syracuseStep 2101315 = 3151973) B3151973
theorem B2363555 : Blo 1244440 2363555 := bstep (se 1 (by rfl) ⟨1772666, by rfl⟩ : syracuseStep 2363555 = 3545333) B3545333
theorem B6828209 : Blo 1244440 6828209 := bstep (se 2 (by rfl) ⟨2560578, by rfl⟩ : syracuseStep 6828209 = 5121157) B5121157
theorem B2101457 : Blo 1244440 2101457 := bstep (se 2 (by rfl) ⟨788046, by rfl⟩ : syracuseStep 2101457 = 1576093) B1576093
theorem B1577171 : Blo 1244440 1577171 := bstep (se 1 (by rfl) ⟨1182878, by rfl⟩ : syracuseStep 1577171 = 2365757) B2365757
theorem B4796657 : Blo 1244440 4796657 := bstep (se 2 (by rfl) ⟨1798746, by rfl⟩ : syracuseStep 4796657 = 3597493) B3597493
theorem B4731149 : Blo 1244440 4731149 := bstep (se 3 (by rfl) ⟨887090, by rfl⟩ : syracuseStep 4731149 = 1774181) B1774181
theorem B7098637 : Blo 1244440 7098637 := bstep (se 3 (by rfl) ⟨1330994, by rfl⟩ : syracuseStep 7098637 = 2661989) B2661989
theorem B2838833 : Blo 1244440 2838833 := bstep (se 2 (by rfl) ⟨1064562, by rfl⟩ : syracuseStep 2838833 = 2129125) B2129125
theorem B5050673 : Blo 1244440 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B2994499 : Blo 1244440 2994499 := bstep (se 1 (by rfl) ⟨2245874, by rfl⟩ : syracuseStep 2994499 = 4491749) B4491749
theorem B3150161 : Blo 1244440 3150161 := bstep (se 2 (by rfl) ⟨1181310, by rfl⟩ : syracuseStep 3150161 = 2362621) B2362621
theorem B2101585 : Blo 1244440 2101585 := bstep (se 2 (by rfl) ⟨788094, by rfl⟩ : syracuseStep 2101585 = 1576189) B1576189
theorem B1995121 : Blo 1244440 1995121 := bstep (se 2 (by rfl) ⟨748170, by rfl⟩ : syracuseStep 1995121 = 1496341) B1496341
theorem B2101619 : Blo 1244440 2101619 := bstep (se 1 (by rfl) ⟨1576214, by rfl⟩ : syracuseStep 2101619 = 3152429) B3152429
theorem B3150211 : Blo 1244440 3150211 := bstep (se 1 (by rfl) ⟨2362658, by rfl⟩ : syracuseStep 3150211 = 4725317) B4725317
theorem B2462083 : Blo 1244440 2462083 := bstep (se 1 (by rfl) ⟨1846562, by rfl⟩ : syracuseStep 2462083 = 3693125) B3693125
theorem B2363843 : Blo 1244440 2363843 := bstep (se 1 (by rfl) ⟨1772882, by rfl⟩ : syracuseStep 2363843 = 3545765) B3545765
theorem B2101747 : Blo 1244440 2101747 := bstep (se 1 (by rfl) ⟨1576310, by rfl⟩ : syracuseStep 2101747 = 3152621) B3152621
theorem B1774067 : Blo 1244440 1774067 := bstep (se 1 (by rfl) ⟨1330550, by rfl⟩ : syracuseStep 1774067 = 2661101) B2661101
theorem B3150353 : Blo 1244440 3150353 := bstep (se 2 (by rfl) ⟨1181382, by rfl⟩ : syracuseStep 3150353 = 2362765) B2362765
theorem B2101889 : Blo 1244440 2101889 := bstep (se 2 (by rfl) ⟨788208, by rfl⟩ : syracuseStep 2101889 = 1576417) B1576417
theorem B20189837 : Blo 1244440 20189837 := bstep (se 3 (by rfl) ⟨3785594, by rfl⟩ : syracuseStep 20189837 = 7571189) B7571189
theorem B2659043 : Blo 1244440 2659043 := bstep (se 1 (by rfl) ⟨1994282, by rfl⟩ : syracuseStep 2659043 = 3988565) B3988565
theorem B2102017 : Blo 1244440 2102017 := bstep (se 2 (by rfl) ⟨788256, by rfl⟩ : syracuseStep 2102017 = 1576513) B1576513
theorem B2102051 : Blo 1244440 2102051 := bstep (se 1 (by rfl) ⟨1576538, by rfl⟩ : syracuseStep 2102051 = 3153077) B3153077
theorem B2077489 : Blo 1244440 2077489 := bstep (se 2 (by rfl) ⟨779058, by rfl⟩ : syracuseStep 2077489 = 1558117) B1558117
theorem B3543875 : Blo 1244440 3543875 := bstep (se 1 (by rfl) ⟨2657906, by rfl⟩ : syracuseStep 3543875 = 5315813) B5315813
theorem B9458531 : Blo 1244440 9458531 := bstep (se 1 (by rfl) ⟨7093898, by rfl⟩ : syracuseStep 9458531 = 14187797) B14187797
theorem B2102179 : Blo 1244440 2102179 := bstep (se 1 (by rfl) ⟨1576634, by rfl⟩ : syracuseStep 2102179 = 3153269) B3153269
theorem B3412945 : Blo 1244440 3412945 := bstep (se 2 (by rfl) ⟨1279854, by rfl⟩ : syracuseStep 3412945 = 2559709) B2559709
theorem B7975921 : Blo 1244440 7975921 := bstep (se 2 (by rfl) ⟨2990970, by rfl⟩ : syracuseStep 7975921 = 5981941) B5981941
theorem B2102321 : Blo 1244440 2102321 := bstep (se 2 (by rfl) ⟨788370, by rfl⟩ : syracuseStep 2102321 = 1576741) B1576741
theorem B3839057 : Blo 1244440 3839057 := bstep (se 2 (by rfl) ⟨1439646, by rfl⟩ : syracuseStep 3839057 = 2879293) B2879293
theorem B1774705 : Blo 1244440 1774705 := bstep (se 2 (by rfl) ⟨665514, by rfl⟩ : syracuseStep 1774705 = 1331029) B1331029
theorem B1684595 : Blo 1244440 1684595 := bstep (se 1 (by rfl) ⟨1263446, by rfl⟩ : syracuseStep 1684595 = 2526893) B2526893
theorem B1995923 : Blo 1244440 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B2102449 : Blo 1244440 2102449 := bstep (se 2 (by rfl) ⟨788418, by rfl⟩ : syracuseStep 2102449 = 1576837) B1576837
theorem B15971525 : Blo 1244440 15971525 := bstep (se 4 (by rfl) ⟨1497330, by rfl⟩ : syracuseStep 15971525 = 2994661) B2994661
theorem B2102483 : Blo 1244440 2102483 := bstep (se 1 (by rfl) ⟨1576862, by rfl⟩ : syracuseStep 2102483 = 3153725) B3153725
theorem B10638661 : Blo 1244440 10638661 := bstep (se 4 (by rfl) ⟨997374, by rfl⟩ : syracuseStep 10638661 = 1994749) B1994749
theorem B2102611 : Blo 1244440 2102611 := bstep (se 1 (by rfl) ⟨1576958, by rfl⟩ : syracuseStep 2102611 = 3153917) B3153917
theorem B2364785 : Blo 1244440 2364785 := bstep (se 2 (by rfl) ⟨886794, by rfl⟩ : syracuseStep 2364785 = 1773589) B1773589
theorem B3986833 : Blo 1244440 3986833 := bstep (se 2 (by rfl) ⟨1495062, by rfl⟩ : syracuseStep 3986833 = 2990125) B2990125
theorem B6387121 : Blo 1244440 6387121 := bstep (se 2 (by rfl) ⟨2395170, by rfl⟩ : syracuseStep 6387121 = 4790341) B4790341
theorem B6305201 : Blo 1244440 6305201 := bstep (se 2 (by rfl) ⟨2364450, by rfl⟩ : syracuseStep 6305201 = 4728901) B4728901
theorem B2102753 : Blo 1244440 2102753 := bstep (se 2 (by rfl) ⟨788532, by rfl⟩ : syracuseStep 2102753 = 1577065) B1577065
theorem B3151345 : Blo 1244440 3151345 := bstep (se 2 (by rfl) ⟨1181754, by rfl⟩ : syracuseStep 3151345 = 2363509) B2363509
theorem B2102881 : Blo 1244440 2102881 := bstep (se 2 (by rfl) ⟨788580, by rfl⟩ : syracuseStep 2102881 = 1577161) B1577161
theorem B2102915 : Blo 1244440 2102915 := bstep (se 1 (by rfl) ⟨1577186, by rfl⟩ : syracuseStep 2102915 = 3154373) B3154373
theorem B3544717 : Blo 1244440 3544717 := bstep (se 3 (by rfl) ⟨664634, by rfl⟩ : syracuseStep 3544717 = 1329269) B1329269
theorem B1996435 : Blo 1244440 1996435 := bstep (se 1 (by rfl) ⟨1497326, by rfl⟩ : syracuseStep 1996435 = 2994653) B2994653
theorem B2840273 : Blo 1244440 2840273 := bstep (se 2 (by rfl) ⟨1065102, by rfl⟩ : syracuseStep 2840273 = 2130205) B2130205
theorem B4200173 : Blo 1244440 4200173 := bstep (se 3 (by rfl) ⟨787532, by rfl⟩ : syracuseStep 4200173 = 1575065) B1575065
theorem B3151619 : Blo 1244440 3151619 := bstep (se 1 (by rfl) ⟨2363714, by rfl⟩ : syracuseStep 3151619 = 4727429) B4727429
theorem B2103043 : Blo 1244440 2103043 := bstep (se 1 (by rfl) ⟨1577282, by rfl⟩ : syracuseStep 2103043 = 3154565) B3154565
theorem B4200227 : Blo 1244440 4200227 := bstep (se 1 (by rfl) ⟨3150170, by rfl⟩ : syracuseStep 4200227 = 6300341) B6300341
theorem B3544877 : Blo 1244440 3544877 := bstep (se 3 (by rfl) ⟨664664, by rfl⟩ : syracuseStep 3544877 = 1329329) B1329329
theorem B14186339 : Blo 1244440 14186339 := bstep (se 1 (by rfl) ⟨10639754, by rfl⟩ : syracuseStep 14186339 = 21279509) B21279509
theorem B10647409 : Blo 1244440 10647409 := bstep (se 2 (by rfl) ⟨3992778, by rfl⟩ : syracuseStep 10647409 = 7985557) B7985557
theorem B2840465 : Blo 1244440 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B2398097 : Blo 1244440 2398097 := bstep (se 2 (by rfl) ⟨899286, by rfl⟩ : syracuseStep 2398097 = 1798573) B1798573
theorem B2103185 : Blo 1244440 2103185 := bstep (se 2 (by rfl) ⟨788694, by rfl⟩ : syracuseStep 2103185 = 1577389) B1577389
theorem B2660273 : Blo 1244440 2660273 := bstep (se 2 (by rfl) ⟨997602, by rfl⟩ : syracuseStep 2660273 = 1995205) B1995205
theorem B3151811 : Blo 1244440 3151811 := bstep (se 1 (by rfl) ⟨2363858, by rfl⟩ : syracuseStep 3151811 = 4727717) B4727717
theorem B3545059 : Blo 1244440 3545059 := bstep (se 1 (by rfl) ⟨2658794, by rfl⟩ : syracuseStep 3545059 = 5317589) B5317589
theorem B6731761 : Blo 1244440 6731761 := bstep (se 2 (by rfl) ⟨2524410, by rfl⟩ : syracuseStep 6731761 = 5048821) B5048821
theorem B2103313 : Blo 1244440 2103313 := bstep (se 2 (by rfl) ⟨788742, by rfl⟩ : syracuseStep 2103313 = 1577485) B1577485
theorem B4200497 : Blo 1244440 4200497 := bstep (se 2 (by rfl) ⟨1575186, by rfl⟩ : syracuseStep 4200497 = 3150373) B3150373
theorem B2103347 : Blo 1244440 2103347 := bstep (se 1 (by rfl) ⟨1577510, by rfl⟩ : syracuseStep 2103347 = 3155021) B3155021
theorem B20183093 : Blo 1244440 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B3365059 : Blo 1244440 3365059 := bstep (se 1 (by rfl) ⟨2523794, by rfl⟩ : syracuseStep 3365059 = 5047589) B5047589
theorem B6731981 : Blo 1244440 6731981 := bstep (se 3 (by rfl) ⟨1262246, by rfl⟩ : syracuseStep 6731981 = 2524493) B2524493
theorem B2365681 : Blo 1244440 2365681 := bstep (se 2 (by rfl) ⟨887130, by rfl⟩ : syracuseStep 2365681 = 1774261) B1774261
theorem B2242883 : Blo 1244440 2242883 := bstep (se 1 (by rfl) ⟨1682162, by rfl⟩ : syracuseStep 2242883 = 3364325) B3364325
theorem B4438349 : Blo 1244440 4438349 := bstep (se 3 (by rfl) ⟨832190, by rfl⟩ : syracuseStep 4438349 = 1664381) B1664381
theorem B6388109 : Blo 1244440 6388109 := bstep (se 3 (by rfl) ⟨1197770, by rfl⟩ : syracuseStep 6388109 = 2395541) B2395541
theorem B2365841 : Blo 1244440 2365841 := bstep (se 2 (by rfl) ⟨887190, by rfl⟩ : syracuseStep 2365841 = 1774381) B1774381
theorem B3987949 : Blo 1244440 3987949 := bstep (se 3 (by rfl) ⟨747740, by rfl⟩ : syracuseStep 3987949 = 1495481) B1495481
theorem B7092805 : Blo 1244440 7092805 := bstep (se 4 (by rfl) ⟨664950, by rfl⟩ : syracuseStep 7092805 = 1329901) B1329901
theorem B4201037 : Blo 1244440 4201037 := bstep (se 3 (by rfl) ⟨787694, by rfl⟩ : syracuseStep 4201037 = 1575389) B1575389
theorem B2800241 : Blo 1244440 2800241 := bstep (se 2 (by rfl) ⟨1050090, by rfl⟩ : syracuseStep 2800241 = 2100181) B2100181
theorem B2800259 : Blo 1244440 2800259 := bstep (se 1 (by rfl) ⟨2100194, by rfl⟩ : syracuseStep 2800259 = 4200389) B4200389
theorem B4201091 : Blo 1244440 4201091 := bstep (se 1 (by rfl) ⟨3150818, by rfl⟩ : syracuseStep 4201091 = 6301637) B6301637
theorem B3594883 : Blo 1244440 3594883 := bstep (se 1 (by rfl) ⟨2696162, by rfl⟩ : syracuseStep 3594883 = 5392325) B5392325
theorem B2366243 : Blo 1244440 2366243 := bstep (se 1 (by rfl) ⟨1774682, by rfl⟩ : syracuseStep 2366243 = 3549365) B3549365
theorem B2661169 : Blo 1244440 2661169 := bstep (se 2 (by rfl) ⟨997938, by rfl⟩ : syracuseStep 2661169 = 1995877) B1995877
theorem B2661187 : Blo 1244440 2661187 := bstep (se 1 (by rfl) ⟨1995890, by rfl⟩ : syracuseStep 2661187 = 3991781) B3991781
theorem B3644237 : Blo 1244440 3644237 := bstep (se 3 (by rfl) ⟨683294, by rfl⟩ : syracuseStep 3644237 = 1366589) B1366589
theorem B6306659 : Blo 1244440 6306659 := bstep (se 1 (by rfl) ⟨4729994, by rfl⟩ : syracuseStep 6306659 = 9459989) B9459989
theorem B3152753 : Blo 1244440 3152753 := bstep (se 2 (by rfl) ⟨1182282, by rfl⟩ : syracuseStep 3152753 = 2364565) B2364565
theorem B2800529 : Blo 1244440 2800529 := bstep (se 2 (by rfl) ⟨1050198, by rfl⟩ : syracuseStep 2800529 = 2100397) B2100397
theorem B4201361 : Blo 1244440 4201361 := bstep (se 2 (by rfl) ⟨1575510, by rfl⟩ : syracuseStep 4201361 = 3151021) B3151021
theorem B2800547 : Blo 1244440 2800547 := bstep (se 1 (by rfl) ⟨2100410, by rfl⟩ : syracuseStep 2800547 = 4200821) B4200821
theorem B3152803 : Blo 1244440 3152803 := bstep (se 1 (by rfl) ⟨2364602, by rfl⟩ : syracuseStep 3152803 = 4729205) B4729205
theorem B1866689 : Blo 1244440 1866689 := bstep (se 2 (by rfl) ⟨700008, by rfl⟩ : syracuseStep 1866689 = 1400017) B1400017
theorem B1866707 : Blo 1244440 1866707 := bstep (se 1 (by rfl) ⟨1400030, by rfl⟩ : syracuseStep 1866707 = 2800061) B2800061
theorem B1866737 : Blo 1244440 1866737 := bstep (se 2 (by rfl) ⟨700026, by rfl⟩ : syracuseStep 1866737 = 1400053) B1400053
theorem B1866755 : Blo 1244440 1866755 := bstep (se 1 (by rfl) ⟨1400066, by rfl⟩ : syracuseStep 1866755 = 2800133) B2800133
theorem B4725773 : Blo 1244440 4725773 := bstep (se 3 (by rfl) ⟨886082, by rfl⟩ : syracuseStep 4725773 = 1772165) B1772165
theorem B1866785 : Blo 1244440 1866785 := bstep (se 2 (by rfl) ⟨700044, by rfl⟩ : syracuseStep 1866785 = 1400089) B1400089
theorem B2841635 : Blo 1244440 2841635 := bstep (se 1 (by rfl) ⟨2131226, by rfl⟩ : syracuseStep 2841635 = 4262453) B4262453
theorem B3152945 : Blo 1244440 3152945 := bstep (se 2 (by rfl) ⟨1182354, by rfl⟩ : syracuseStep 3152945 = 2364709) B2364709
theorem B1866803 : Blo 1244440 1866803 := bstep (se 1 (by rfl) ⟨1400102, by rfl⟩ : syracuseStep 1866803 = 2800205) B2800205
theorem B1866833 : Blo 1244440 1866833 := bstep (se 2 (by rfl) ⟨700062, by rfl⟩ : syracuseStep 1866833 = 1400125) B1400125
theorem B1866851 : Blo 1244440 1866851 := bstep (se 1 (by rfl) ⟨1400138, by rfl⟩ : syracuseStep 1866851 = 2800277) B2800277
theorem B1866881 : Blo 1244440 1866881 := bstep (se 2 (by rfl) ⟨700080, by rfl⟩ : syracuseStep 1866881 = 1400161) B1400161
theorem B1866899 : Blo 1244440 1866899 := bstep (se 1 (by rfl) ⟨1400174, by rfl⟩ : syracuseStep 1866899 = 2800349) B2800349
theorem B2243747 : Blo 1244440 2243747 := bstep (se 1 (by rfl) ⟨1682810, by rfl⟩ : syracuseStep 2243747 = 3365621) B3365621
theorem B1866929 : Blo 1244440 1866929 := bstep (se 2 (by rfl) ⟨700098, by rfl⟩ : syracuseStep 1866929 = 1400197) B1400197
theorem B2800817 : Blo 1244440 2800817 := bstep (se 2 (by rfl) ⟨1050306, by rfl⟩ : syracuseStep 2800817 = 2100613) B2100613
theorem B1866947 : Blo 1244440 1866947 := bstep (se 1 (by rfl) ⟨1400210, by rfl⟩ : syracuseStep 1866947 = 2800421) B2800421
theorem B2800835 : Blo 1244440 2800835 := bstep (se 1 (by rfl) ⟨2100626, by rfl⟩ : syracuseStep 2800835 = 4201253) B4201253
theorem B1866977 : Blo 1244440 1866977 := bstep (se 2 (by rfl) ⟨700116, by rfl⟩ : syracuseStep 1866977 = 1400233) B1400233
theorem B1400035 : Blo 1244440 1400035 := bstep (se 1 (by rfl) ⟨1050026, by rfl⟩ : syracuseStep 1400035 = 2100053) B2100053
theorem B1866995 : Blo 1244440 1866995 := bstep (se 1 (by rfl) ⟨1400246, by rfl⟩ : syracuseStep 1866995 = 2800493) B2800493
theorem B1867025 : Blo 1244440 1867025 := bstep (se 2 (by rfl) ⟨700134, by rfl⟩ : syracuseStep 1867025 = 1400269) B1400269
theorem B2243857 : Blo 1244440 2243857 := bstep (se 2 (by rfl) ⟨841446, by rfl⟩ : syracuseStep 2243857 = 1682893) B1682893
theorem B1244451 : Blo 1244440 1244451 := bstep (se 1 (by rfl) ⟨933338, by rfl⟩ : syracuseStep 1244451 = 1866677) B1866677
theorem B1867043 : Blo 1244440 1867043 := bstep (se 1 (by rfl) ⟨1400282, by rfl⟩ : syracuseStep 1867043 = 2800565) B2800565
theorem B3988781 : Blo 1244440 3988781 := bstep (se 3 (by rfl) ⟨747896, by rfl⟩ : syracuseStep 3988781 = 1495793) B1495793
theorem B1244467 : Blo 1244440 1244467 := bstep (se 1 (by rfl) ⟨933350, by rfl⟩ : syracuseStep 1244467 = 1866701) B1866701
theorem B1867073 : Blo 1244440 1867073 := bstep (se 2 (by rfl) ⟨700152, by rfl⟩ : syracuseStep 1867073 = 1400305) B1400305
theorem B1244483 : Blo 1244440 1244483 := bstep (se 1 (by rfl) ⟨933362, by rfl⟩ : syracuseStep 1244483 = 1866725) B1866725
theorem B3546449 : Blo 1244440 3546449 := bstep (se 2 (by rfl) ⟨1329918, by rfl⟩ : syracuseStep 3546449 = 2659837) B2659837
theorem B1244499 : Blo 1244440 1244499 := bstep (se 1 (by rfl) ⟨933374, by rfl⟩ : syracuseStep 1244499 = 1866749) B1866749
theorem B1867091 : Blo 1244440 1867091 := bstep (se 1 (by rfl) ⟨1400318, by rfl⟩ : syracuseStep 1867091 = 2800637) B2800637
theorem B1244515 : Blo 1244440 1244515 := bstep (se 1 (by rfl) ⟨933386, by rfl⟩ : syracuseStep 1244515 = 1866773) B1866773
theorem B5684579 : Blo 1244440 5684579 := bstep (se 1 (by rfl) ⟨4263434, by rfl⟩ : syracuseStep 5684579 = 8526869) B8526869
theorem B1867121 : Blo 1244440 1867121 := bstep (se 2 (by rfl) ⟨700170, by rfl⟩ : syracuseStep 1867121 = 1400341) B1400341
theorem B1244531 : Blo 1244440 1244531 := bstep (se 1 (by rfl) ⟨933398, by rfl⟩ : syracuseStep 1244531 = 1866797) B1866797
theorem B1400179 : Blo 1244440 1400179 := bstep (se 1 (by rfl) ⟨1050134, by rfl⟩ : syracuseStep 1400179 = 2100269) B2100269
theorem B1244547 : Blo 1244440 1244547 := bstep (se 1 (by rfl) ⟨933410, by rfl⟩ : syracuseStep 1244547 = 1866821) B1866821
theorem B1867139 : Blo 1244440 1867139 := bstep (se 1 (by rfl) ⟨1400354, by rfl⟩ : syracuseStep 1867139 = 2800709) B2800709
theorem B1244563 : Blo 1244440 1244563 := bstep (se 1 (by rfl) ⟨933422, by rfl⟩ : syracuseStep 1244563 = 1866845) B1866845
theorem B1867169 : Blo 1244440 1867169 := bstep (se 2 (by rfl) ⟨700188, by rfl⟩ : syracuseStep 1867169 = 1400377) B1400377
theorem B1244579 : Blo 1244440 1244579 := bstep (se 1 (by rfl) ⟨933434, by rfl⟩ : syracuseStep 1244579 = 1866869) B1866869
theorem B4201901 : Blo 1244440 4201901 := bstep (se 3 (by rfl) ⟨787856, by rfl⟩ : syracuseStep 4201901 = 1575713) B1575713
theorem B1244595 : Blo 1244440 1244595 := bstep (se 1 (by rfl) ⟨933446, by rfl⟩ : syracuseStep 1244595 = 1866893) B1866893
theorem B1867187 : Blo 1244440 1867187 := bstep (se 1 (by rfl) ⟨1400390, by rfl⟩ : syracuseStep 1867187 = 2800781) B2800781
theorem B1244611 : Blo 1244440 1244611 := bstep (se 1 (by rfl) ⟨933458, by rfl⟩ : syracuseStep 1244611 = 1866917) B1866917
theorem B1867217 : Blo 1244440 1867217 := bstep (se 2 (by rfl) ⟨700206, by rfl⟩ : syracuseStep 1867217 = 1400413) B1400413
theorem B2801105 : Blo 1244440 2801105 := bstep (se 2 (by rfl) ⟨1050414, by rfl⟩ : syracuseStep 2801105 = 2100829) B2100829
theorem B1244627 : Blo 1244440 1244627 := bstep (se 1 (by rfl) ⟨933470, by rfl⟩ : syracuseStep 1244627 = 1866941) B1866941
theorem B1244643 : Blo 1244440 1244643 := bstep (se 1 (by rfl) ⟨933482, by rfl⟩ : syracuseStep 1244643 = 1866965) B1866965
theorem B1867235 : Blo 1244440 1867235 := bstep (se 1 (by rfl) ⟨1400426, by rfl⟩ : syracuseStep 1867235 = 2800853) B2800853
theorem B2801123 : Blo 1244440 2801123 := bstep (se 1 (by rfl) ⟨2100842, by rfl⟩ : syracuseStep 2801123 = 4201685) B4201685
theorem B4201955 : Blo 1244440 4201955 := bstep (se 1 (by rfl) ⟨3151466, by rfl⟩ : syracuseStep 4201955 = 6302933) B6302933
theorem B1244659 : Blo 1244440 1244659 := bstep (se 1 (by rfl) ⟨933494, by rfl⟩ : syracuseStep 1244659 = 1866989) B1866989
theorem B1867265 : Blo 1244440 1867265 := bstep (se 2 (by rfl) ⟨700224, by rfl⟩ : syracuseStep 1867265 = 1400449) B1400449
theorem B1244675 : Blo 1244440 1244675 := bstep (se 1 (by rfl) ⟨933506, by rfl⟩ : syracuseStep 1244675 = 1867013) B1867013
theorem B1400323 : Blo 1244440 1400323 := bstep (se 1 (by rfl) ⟨1050242, by rfl⟩ : syracuseStep 1400323 = 2100485) B2100485
theorem B7577101 : Blo 1244440 7577101 := bstep (se 3 (by rfl) ⟨1420706, by rfl⟩ : syracuseStep 7577101 = 2841413) B2841413
theorem B1244691 : Blo 1244440 1244691 := bstep (se 1 (by rfl) ⟨933518, by rfl⟩ : syracuseStep 1244691 = 1867037) B1867037
theorem B1867283 : Blo 1244440 1867283 := bstep (se 1 (by rfl) ⟨1400462, by rfl⟩ : syracuseStep 1867283 = 2800925) B2800925
theorem B1244707 : Blo 1244440 1244707 := bstep (se 1 (by rfl) ⟨933530, by rfl⟩ : syracuseStep 1244707 = 1867061) B1867061
theorem B1867313 : Blo 1244440 1867313 := bstep (se 2 (by rfl) ⟨700242, by rfl⟩ : syracuseStep 1867313 = 1400485) B1400485
theorem B2244145 : Blo 1244440 2244145 := bstep (se 2 (by rfl) ⟨841554, by rfl⟩ : syracuseStep 2244145 = 1683109) B1683109
theorem B1244723 : Blo 1244440 1244723 := bstep (se 1 (by rfl) ⟨933542, by rfl⟩ : syracuseStep 1244723 = 1867085) B1867085
theorem B1244739 : Blo 1244440 1244739 := bstep (se 1 (by rfl) ⟨933554, by rfl⟩ : syracuseStep 1244739 = 1867109) B1867109
theorem B1867331 : Blo 1244440 1867331 := bstep (se 1 (by rfl) ⟨1400498, by rfl⟩ : syracuseStep 1867331 = 2800997) B2800997
theorem B1244755 : Blo 1244440 1244755 := bstep (se 1 (by rfl) ⟨933566, by rfl⟩ : syracuseStep 1244755 = 1867133) B1867133
theorem B1867361 : Blo 1244440 1867361 := bstep (se 2 (by rfl) ⟨700260, by rfl⟩ : syracuseStep 1867361 = 1400521) B1400521
theorem B1244771 : Blo 1244440 1244771 := bstep (se 1 (by rfl) ⟨933578, by rfl⟩ : syracuseStep 1244771 = 1867157) B1867157
theorem B1244787 : Blo 1244440 1244787 := bstep (se 1 (by rfl) ⟨933590, by rfl⟩ : syracuseStep 1244787 = 1867181) B1867181
theorem B1867379 : Blo 1244440 1867379 := bstep (se 1 (by rfl) ⟨1400534, by rfl⟩ : syracuseStep 1867379 = 2801069) B2801069
theorem B1244803 : Blo 1244440 1244803 := bstep (se 1 (by rfl) ⟨933602, by rfl⟩ : syracuseStep 1244803 = 1867205) B1867205
theorem B6307469 : Blo 1244440 6307469 := bstep (se 3 (by rfl) ⟨1182650, by rfl⟩ : syracuseStep 6307469 = 2365301) B2365301
theorem B1867409 : Blo 1244440 1867409 := bstep (se 2 (by rfl) ⟨700278, by rfl⟩ : syracuseStep 1867409 = 1400557) B1400557
theorem B1244819 : Blo 1244440 1244819 := bstep (se 1 (by rfl) ⟨933614, by rfl⟩ : syracuseStep 1244819 = 1867229) B1867229
theorem B1400467 : Blo 1244440 1400467 := bstep (se 1 (by rfl) ⟨1050350, by rfl⟩ : syracuseStep 1400467 = 2100701) B2100701
theorem B1244835 : Blo 1244440 1244835 := bstep (se 1 (by rfl) ⟨933626, by rfl⟩ : syracuseStep 1244835 = 1867253) B1867253
theorem B1867427 : Blo 1244440 1867427 := bstep (se 1 (by rfl) ⟨1400570, by rfl⟩ : syracuseStep 1867427 = 2801141) B2801141
theorem B1244851 : Blo 1244440 1244851 := bstep (se 1 (by rfl) ⟨933638, by rfl⟩ : syracuseStep 1244851 = 1867277) B1867277
theorem B1867457 : Blo 1244440 1867457 := bstep (se 2 (by rfl) ⟨700296, by rfl⟩ : syracuseStep 1867457 = 1400593) B1400593
theorem B1244867 : Blo 1244440 1244867 := bstep (se 1 (by rfl) ⟨933650, by rfl⟩ : syracuseStep 1244867 = 1867301) B1867301
theorem B1244883 : Blo 1244440 1244883 := bstep (se 1 (by rfl) ⟨933662, by rfl⟩ : syracuseStep 1244883 = 1867325) B1867325
theorem B1867475 : Blo 1244440 1867475 := bstep (se 1 (by rfl) ⟨1400606, by rfl⟩ : syracuseStep 1867475 = 2801213) B2801213
theorem B1244899 : Blo 1244440 1244899 := bstep (se 1 (by rfl) ⟨933674, by rfl⟩ : syracuseStep 1244899 = 1867349) B1867349
theorem B1867505 : Blo 1244440 1867505 := bstep (se 2 (by rfl) ⟨700314, by rfl⟩ : syracuseStep 1867505 = 1400629) B1400629
theorem B2801393 : Blo 1244440 2801393 := bstep (se 2 (by rfl) ⟨1050522, by rfl⟩ : syracuseStep 2801393 = 2101045) B2101045
theorem B1244915 : Blo 1244440 1244915 := bstep (se 1 (by rfl) ⟨933686, by rfl⟩ : syracuseStep 1244915 = 1867373) B1867373
theorem B4202225 : Blo 1244440 4202225 := bstep (se 2 (by rfl) ⟨1575834, by rfl⟩ : syracuseStep 4202225 = 3151669) B3151669
theorem B1244931 : Blo 1244440 1244931 := bstep (se 1 (by rfl) ⟨933698, by rfl⟩ : syracuseStep 1244931 = 1867397) B1867397
theorem B1867523 : Blo 1244440 1867523 := bstep (se 1 (by rfl) ⟨1400642, by rfl⟩ : syracuseStep 1867523 = 2801285) B2801285
theorem B2801411 : Blo 1244440 2801411 := bstep (se 1 (by rfl) ⟨2101058, by rfl⟩ : syracuseStep 2801411 = 4202117) B4202117
theorem B3366659 : Blo 1244440 3366659 := bstep (se 1 (by rfl) ⟨2524994, by rfl⟩ : syracuseStep 3366659 = 5049989) B5049989
theorem B12132109 : Blo 1244440 12132109 := bstep (se 3 (by rfl) ⟨2274770, by rfl⟩ : syracuseStep 12132109 = 4549541) B4549541
theorem B1244947 : Blo 1244440 1244947 := bstep (se 1 (by rfl) ⟨933710, by rfl⟩ : syracuseStep 1244947 = 1867421) B1867421
theorem B1867553 : Blo 1244440 1867553 := bstep (se 2 (by rfl) ⟨700332, by rfl⟩ : syracuseStep 1867553 = 1400665) B1400665
theorem B1244963 : Blo 1244440 1244963 := bstep (se 1 (by rfl) ⟨933722, by rfl⟩ : syracuseStep 1244963 = 1867445) B1867445
theorem B1400611 : Blo 1244440 1400611 := bstep (se 1 (by rfl) ⟨1050458, by rfl⟩ : syracuseStep 1400611 = 2100917) B2100917
theorem B3596081 : Blo 1244440 3596081 := bstep (se 2 (by rfl) ⟨1348530, by rfl⟩ : syracuseStep 3596081 = 2697061) B2697061
theorem B1244979 : Blo 1244440 1244979 := bstep (se 1 (by rfl) ⟨933734, by rfl⟩ : syracuseStep 1244979 = 1867469) B1867469
theorem B1867571 : Blo 1244440 1867571 := bstep (se 1 (by rfl) ⟨1400678, by rfl⟩ : syracuseStep 1867571 = 2801357) B2801357
theorem B1244995 : Blo 1244440 1244995 := bstep (se 1 (by rfl) ⟨933746, by rfl⟩ : syracuseStep 1244995 = 1867493) B1867493
theorem B1867601 : Blo 1244440 1867601 := bstep (se 2 (by rfl) ⟨700350, by rfl⟩ : syracuseStep 1867601 = 1400701) B1400701
theorem B1245011 : Blo 1244440 1245011 := bstep (se 1 (by rfl) ⟨933758, by rfl⟩ : syracuseStep 1245011 = 1867517) B1867517
theorem B2023265 : Blo 1244440 2023265 := bstep (se 2 (by rfl) ⟨758724, by rfl⟩ : syracuseStep 2023265 = 1517449) B1517449
theorem B1245027 : Blo 1244440 1245027 := bstep (se 1 (by rfl) ⟨933770, by rfl⟩ : syracuseStep 1245027 = 1867541) B1867541
theorem B1867619 : Blo 1244440 1867619 := bstep (se 1 (by rfl) ⟨1400714, by rfl⟩ : syracuseStep 1867619 = 2801429) B2801429
theorem B1245043 : Blo 1244440 1245043 := bstep (se 1 (by rfl) ⟨933782, by rfl⟩ : syracuseStep 1245043 = 1867565) B1867565
theorem B1867649 : Blo 1244440 1867649 := bstep (se 2 (by rfl) ⟨700368, by rfl⟩ : syracuseStep 1867649 = 1400737) B1400737
theorem B1245059 : Blo 1244440 1245059 := bstep (se 1 (by rfl) ⟨933794, by rfl⟩ : syracuseStep 1245059 = 1867589) B1867589
theorem B1245075 : Blo 1244440 1245075 := bstep (se 1 (by rfl) ⟨933806, by rfl⟩ : syracuseStep 1245075 = 1867613) B1867613
theorem B1867667 : Blo 1244440 1867667 := bstep (se 1 (by rfl) ⟨1400750, by rfl⟩ : syracuseStep 1867667 = 2801501) B2801501
theorem B5390243 : Blo 1244440 5390243 := bstep (se 1 (by rfl) ⟨4042682, by rfl⟩ : syracuseStep 5390243 = 8085365) B8085365
theorem B1245091 : Blo 1244440 1245091 := bstep (se 1 (by rfl) ⟨933818, by rfl⟩ : syracuseStep 1245091 = 1867637) B1867637
theorem B5316529 : Blo 1244440 5316529 := bstep (se 2 (by rfl) ⟨1993698, by rfl⟩ : syracuseStep 5316529 = 3987397) B3987397
theorem B1867697 : Blo 1244440 1867697 := bstep (se 2 (by rfl) ⟨700386, by rfl⟩ : syracuseStep 1867697 = 1400773) B1400773
theorem B1245107 : Blo 1244440 1245107 := bstep (se 1 (by rfl) ⟨933830, by rfl⟩ : syracuseStep 1245107 = 1867661) B1867661
theorem B1400755 : Blo 1244440 1400755 := bstep (se 1 (by rfl) ⟨1050566, by rfl⟩ : syracuseStep 1400755 = 2101133) B2101133
theorem B1245123 : Blo 1244440 1245123 := bstep (se 1 (by rfl) ⟨933842, by rfl⟩ : syracuseStep 1245123 = 1867685) B1867685
theorem B1867715 : Blo 1244440 1867715 := bstep (se 1 (by rfl) ⟨1400786, by rfl⟩ : syracuseStep 1867715 = 2801573) B2801573
theorem B1245139 : Blo 1244440 1245139 := bstep (se 1 (by rfl) ⟨933854, by rfl⟩ : syracuseStep 1245139 = 1867709) B1867709
theorem B1867745 : Blo 1244440 1867745 := bstep (se 2 (by rfl) ⟨700404, by rfl⟩ : syracuseStep 1867745 = 1400809) B1400809
theorem B1245155 : Blo 1244440 1245155 := bstep (se 1 (by rfl) ⟨933866, by rfl⟩ : syracuseStep 1245155 = 1867733) B1867733
theorem B15966193 : Blo 1244440 15966193 := bstep (se 2 (by rfl) ⟨5987322, by rfl⟩ : syracuseStep 15966193 = 11974645) B11974645
theorem B1245171 : Blo 1244440 1245171 := bstep (se 1 (by rfl) ⟨933878, by rfl⟩ : syracuseStep 1245171 = 1867757) B1867757
theorem B1867763 : Blo 1244440 1867763 := bstep (se 1 (by rfl) ⟨1400822, by rfl⟩ : syracuseStep 1867763 = 2801645) B2801645
theorem B1867787 : Blo 1244440 1867787 := bstep (se 1 (by rfl) ⟨1400840, by rfl⟩ : syracuseStep 1867787 = 2801681) B2801681
theorem B1245195 : Blo 1244440 1245195 := bstep (se 1 (by rfl) ⟨933896, by rfl⟩ : syracuseStep 1245195 = 1867793) B1867793
theorem B1867799 : Blo 1244440 1867799 := bstep (se 1 (by rfl) ⟨1400849, by rfl⟩ : syracuseStep 1867799 = 2801699) B2801699
theorem B1245207 : Blo 1244440 1245207 := bstep (se 1 (by rfl) ⟨933905, by rfl⟩ : syracuseStep 1245207 = 1867811) B1867811
theorem B1245227 : Blo 1244440 1245227 := bstep (se 1 (by rfl) ⟨933920, by rfl⟩ : syracuseStep 1245227 = 1867841) B1867841
theorem B1245239 : Blo 1244440 1245239 := bstep (se 1 (by rfl) ⟨933929, by rfl⟩ : syracuseStep 1245239 = 1867859) B1867859
theorem B1245259 : Blo 1244440 1245259 := bstep (se 1 (by rfl) ⟨933944, by rfl⟩ : syracuseStep 1245259 = 1867889) B1867889
theorem B1245271 : Blo 1244440 1245271 := bstep (se 1 (by rfl) ⟨933953, by rfl⟩ : syracuseStep 1245271 = 1867907) B1867907
theorem B2801753 : Blo 1244440 2801753 := bstep (se 2 (by rfl) ⟨1050657, by rfl⟩ : syracuseStep 2801753 = 2101315) B2101315
theorem B1867865 : Blo 1244440 1867865 := bstep (se 2 (by rfl) ⟨700449, by rfl⟩ : syracuseStep 1867865 = 1400899) B1400899
theorem B1245291 : Blo 1244440 1245291 := bstep (se 1 (by rfl) ⟨933968, by rfl⟩ : syracuseStep 1245291 = 1867937) B1867937
theorem B1245303 : Blo 1244440 1245303 := bstep (se 1 (by rfl) ⟨933977, by rfl⟩ : syracuseStep 1245303 = 1867955) B1867955
theorem B1400971 : Blo 1244440 1400971 := bstep (se 1 (by rfl) ⟨1050728, by rfl⟩ : syracuseStep 1400971 = 2101457) B2101457
theorem B1245323 : Blo 1244440 1245323 := bstep (se 1 (by rfl) ⟨933992, by rfl⟩ : syracuseStep 1245323 = 1867985) B1867985
theorem B1245335 : Blo 1244440 1245335 := bstep (se 1 (by rfl) ⟨934001, by rfl⟩ : syracuseStep 1245335 = 1868003) B1868003
theorem B1245355 : Blo 1244440 1245355 := bstep (se 1 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 1245355 = 1868033) B1868033
theorem B4726957 : Blo 1244440 4726957 := bstep (se 3 (by rfl) ⟨886304, by rfl⟩ : syracuseStep 4726957 = 1772609) B1772609
theorem B2801843 : Blo 1244440 2801843 := bstep (se 1 (by rfl) ⟨2101382, by rfl⟩ : syracuseStep 2801843 = 4202765) B4202765
theorem B3154099 : Blo 1244440 3154099 := bstep (se 1 (by rfl) ⟨2365574, by rfl⟩ : syracuseStep 3154099 = 4731149) B4731149
theorem B1245367 : Blo 1244440 1245367 := bstep (se 1 (by rfl) ⟨934025, by rfl⟩ : syracuseStep 1245367 = 1868051) B1868051
theorem B1892555 : Blo 1244440 1892555 := bstep (se 1 (by rfl) ⟨1419416, by rfl⟩ : syracuseStep 1892555 = 2838833) B2838833
theorem B1867979 : Blo 1244440 1867979 := bstep (se 1 (by rfl) ⟨1400984, by rfl⟩ : syracuseStep 1867979 = 2801969) B2801969
theorem B1245387 : Blo 1244440 1245387 := bstep (se 1 (by rfl) ⟨934040, by rfl⟩ : syracuseStep 1245387 = 1868081) B1868081
theorem B3367115 : Blo 1244440 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B2801879 : Blo 1244440 2801879 := bstep (se 1 (by rfl) ⟨2101409, by rfl⟩ : syracuseStep 2801879 = 4202819) B4202819
theorem B1867991 : Blo 1244440 1867991 := bstep (se 1 (by rfl) ⟨1400993, by rfl⟩ : syracuseStep 1867991 = 2801987) B2801987
theorem B1245399 : Blo 1244440 1245399 := bstep (se 1 (by rfl) ⟨934049, by rfl⟩ : syracuseStep 1245399 = 1868099) B1868099
theorem B1245419 : Blo 1244440 1245419 := bstep (se 1 (by rfl) ⟨934064, by rfl⟩ : syracuseStep 1245419 = 1868129) B1868129
theorem B1401079 : Blo 1244440 1401079 := bstep (se 1 (by rfl) ⟨1050809, by rfl⟩ : syracuseStep 1401079 = 2101619) B2101619
theorem B1245431 : Blo 1244440 1245431 := bstep (se 1 (by rfl) ⟨934073, by rfl⟩ : syracuseStep 1245431 = 1868147) B1868147
theorem B1245451 : Blo 1244440 1245451 := bstep (se 1 (by rfl) ⟨934088, by rfl⟩ : syracuseStep 1245451 = 1868177) B1868177
theorem B1245463 : Blo 1244440 1245463 := bstep (se 1 (by rfl) ⟨934097, by rfl⟩ : syracuseStep 1245463 = 1868195) B1868195
theorem B1868057 : Blo 1244440 1868057 := bstep (se 2 (by rfl) ⟨700521, by rfl⟩ : syracuseStep 1868057 = 1401043) B1401043
theorem B1245483 : Blo 1244440 1245483 := bstep (se 1 (by rfl) ⟨934112, by rfl⟩ : syracuseStep 1245483 = 1868225) B1868225
theorem B1245495 : Blo 1244440 1245495 := bstep (se 1 (by rfl) ⟨934121, by rfl⟩ : syracuseStep 1245495 = 1868243) B1868243
theorem B3154241 : Blo 1244440 3154241 := bstep (se 2 (by rfl) ⟨1182840, by rfl⟩ : syracuseStep 3154241 = 2365681) B2365681
theorem B1245515 : Blo 1244440 1245515 := bstep (se 1 (by rfl) ⟨934136, by rfl⟩ : syracuseStep 1245515 = 1868273) B1868273
theorem B1245527 : Blo 1244440 1245527 := bstep (se 1 (by rfl) ⟨934145, by rfl⟩ : syracuseStep 1245527 = 1868291) B1868291
theorem B1245547 : Blo 1244440 1245547 := bstep (se 1 (by rfl) ⟨934160, by rfl⟩ : syracuseStep 1245547 = 1868321) B1868321
theorem B1245559 : Blo 1244440 1245559 := bstep (se 1 (by rfl) ⟨934169, by rfl⟩ : syracuseStep 1245559 = 1868339) B1868339
theorem B6062467 : Blo 1244440 6062467 := bstep (se 1 (by rfl) ⟨4546850, by rfl⟩ : syracuseStep 6062467 = 9093701) B9093701
theorem B2802059 : Blo 1244440 2802059 := bstep (se 1 (by rfl) ⟨2101544, by rfl⟩ : syracuseStep 2802059 = 4203089) B4203089
theorem B1868171 : Blo 1244440 1868171 := bstep (se 1 (by rfl) ⟨1401128, by rfl⟩ : syracuseStep 1868171 = 2802257) B2802257
theorem B1245579 : Blo 1244440 1245579 := bstep (se 1 (by rfl) ⟨934184, by rfl⟩ : syracuseStep 1245579 = 1868369) B1868369
theorem B1868183 : Blo 1244440 1868183 := bstep (se 1 (by rfl) ⟨1401137, by rfl⟩ : syracuseStep 1868183 = 2802275) B2802275
theorem B1245591 : Blo 1244440 1245591 := bstep (se 1 (by rfl) ⟨934193, by rfl⟩ : syracuseStep 1245591 = 1868387) B1868387
theorem B1401259 : Blo 1244440 1401259 := bstep (se 1 (by rfl) ⟨1050944, by rfl⟩ : syracuseStep 1401259 = 2101889) B2101889
theorem B1245611 : Blo 1244440 1245611 := bstep (se 1 (by rfl) ⟨934208, by rfl⟩ : syracuseStep 1245611 = 1868417) B1868417
theorem B13459891 : Blo 1244440 13459891 := bstep (se 1 (by rfl) ⟨10094918, by rfl⟩ : syracuseStep 13459891 = 20189837) B20189837
theorem B1245623 : Blo 1244440 1245623 := bstep (se 1 (by rfl) ⟨934217, by rfl⟩ : syracuseStep 1245623 = 1868435) B1868435
theorem B2802113 : Blo 1244440 2802113 := bstep (se 2 (by rfl) ⟨1050792, by rfl⟩ : syracuseStep 2802113 = 2101585) B2101585
theorem B5046731 : Blo 1244440 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B1245643 : Blo 1244440 1245643 := bstep (se 1 (by rfl) ⟨934232, by rfl⟩ : syracuseStep 1245643 = 1868465) B1868465
theorem B1245655 : Blo 1244440 1245655 := bstep (se 1 (by rfl) ⟨934241, by rfl⟩ : syracuseStep 1245655 = 1868483) B1868483
theorem B1868249 : Blo 1244440 1868249 := bstep (se 2 (by rfl) ⟨700593, by rfl⟩ : syracuseStep 1868249 = 1401187) B1401187
theorem B4727261 : Blo 1244440 4727261 := bstep (se 3 (by rfl) ⟨886361, by rfl⟩ : syracuseStep 4727261 = 1772723) B1772723
theorem B1245675 : Blo 1244440 1245675 := bstep (se 1 (by rfl) ⟨934256, by rfl⟩ : syracuseStep 1245675 = 1868513) B1868513
theorem B1245687 : Blo 1244440 1245687 := bstep (se 1 (by rfl) ⟨934265, by rfl⟩ : syracuseStep 1245687 = 1868531) B1868531
theorem B1245707 : Blo 1244440 1245707 := bstep (se 1 (by rfl) ⟨934280, by rfl⟩ : syracuseStep 1245707 = 1868561) B1868561
theorem B1401367 : Blo 1244440 1401367 := bstep (se 1 (by rfl) ⟨1051025, by rfl⟩ : syracuseStep 1401367 = 2102051) B2102051
theorem B1245719 : Blo 1244440 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B1245739 : Blo 1244440 1245739 := bstep (se 1 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 1245739 = 1868609) B1868609
theorem B1245751 : Blo 1244440 1245751 := bstep (se 1 (by rfl) ⟨934313, by rfl⟩ : syracuseStep 1245751 = 1868627) B1868627
theorem B1868363 : Blo 1244440 1868363 := bstep (se 1 (by rfl) ⟨1401272, by rfl⟩ : syracuseStep 1868363 = 2802545) B2802545
theorem B1245771 : Blo 1244440 1245771 := bstep (se 1 (by rfl) ⟨934328, by rfl⟩ : syracuseStep 1245771 = 1868657) B1868657
theorem B1868375 : Blo 1244440 1868375 := bstep (se 1 (by rfl) ⟨1401281, by rfl⟩ : syracuseStep 1868375 = 2802563) B2802563
theorem B1245783 : Blo 1244440 1245783 := bstep (se 1 (by rfl) ⟨934337, by rfl⟩ : syracuseStep 1245783 = 1868675) B1868675
theorem B1245803 : Blo 1244440 1245803 := bstep (se 1 (by rfl) ⟨934352, by rfl⟩ : syracuseStep 1245803 = 1868705) B1868705
theorem B1245815 : Blo 1244440 1245815 := bstep (se 1 (by rfl) ⟨934361, by rfl⟩ : syracuseStep 1245815 = 1868723) B1868723
theorem B1245835 : Blo 1244440 1245835 := bstep (se 1 (by rfl) ⟨934376, by rfl⟩ : syracuseStep 1245835 = 1868753) B1868753
theorem B5317265 : Blo 1244440 5317265 := bstep (se 2 (by rfl) ⟨1993974, by rfl⟩ : syracuseStep 5317265 = 3987949) B3987949
theorem B1245847 : Blo 1244440 1245847 := bstep (se 1 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 1245847 = 1868771) B1868771
theorem B2802329 : Blo 1244440 2802329 := bstep (se 2 (by rfl) ⟨1050873, by rfl⟩ : syracuseStep 2802329 = 2101747) B2101747
theorem B1868441 : Blo 1244440 1868441 := bstep (se 2 (by rfl) ⟨700665, by rfl⟩ : syracuseStep 1868441 = 1401331) B1401331
theorem B1245867 : Blo 1244440 1245867 := bstep (se 1 (by rfl) ⟨934400, by rfl⟩ : syracuseStep 1245867 = 1868801) B1868801
theorem B1245879 : Blo 1244440 1245879 := bstep (se 1 (by rfl) ⟨934409, by rfl⟩ : syracuseStep 1245879 = 1868819) B1868819
theorem B1401547 : Blo 1244440 1401547 := bstep (se 1 (by rfl) ⟨1051160, by rfl⟩ : syracuseStep 1401547 = 2102321) B2102321
theorem B1245899 : Blo 1244440 1245899 := bstep (se 1 (by rfl) ⟨934424, by rfl⟩ : syracuseStep 1245899 = 1868849) B1868849
theorem B1245911 : Blo 1244440 1245911 := bstep (se 1 (by rfl) ⟨934433, by rfl⟩ : syracuseStep 1245911 = 1868867) B1868867
theorem B1245931 : Blo 1244440 1245931 := bstep (se 1 (by rfl) ⟨934448, by rfl⟩ : syracuseStep 1245931 = 1868897) B1868897
theorem B2802419 : Blo 1244440 2802419 := bstep (se 1 (by rfl) ⟨2101814, by rfl⟩ : syracuseStep 2802419 = 4203629) B4203629
theorem B1245943 : Blo 1244440 1245943 := bstep (se 1 (by rfl) ⟨934457, by rfl⟩ : syracuseStep 1245943 = 1868915) B1868915
theorem B1868555 : Blo 1244440 1868555 := bstep (se 1 (by rfl) ⟨1401416, by rfl⟩ : syracuseStep 1868555 = 2802833) B2802833
theorem B1245963 : Blo 1244440 1245963 := bstep (se 1 (by rfl) ⟨934472, by rfl⟩ : syracuseStep 1245963 = 1868945) B1868945
theorem B2802455 : Blo 1244440 2802455 := bstep (se 1 (by rfl) ⟨2101841, by rfl⟩ : syracuseStep 2802455 = 4203683) B4203683
theorem B1868567 : Blo 1244440 1868567 := bstep (se 1 (by rfl) ⟨1401425, by rfl⟩ : syracuseStep 1868567 = 2802851) B2802851
theorem B1245975 : Blo 1244440 1245975 := bstep (se 1 (by rfl) ⟨934481, by rfl⟩ : syracuseStep 1245975 = 1868963) B1868963
theorem B1245995 : Blo 1244440 1245995 := bstep (se 1 (by rfl) ⟨934496, by rfl⟩ : syracuseStep 1245995 = 1868993) B1868993
theorem B1401655 : Blo 1244440 1401655 := bstep (se 1 (by rfl) ⟨1051241, by rfl⟩ : syracuseStep 1401655 = 2102483) B2102483
theorem B1246007 : Blo 1244440 1246007 := bstep (se 1 (by rfl) ⟨934505, by rfl⟩ : syracuseStep 1246007 = 1869011) B1869011
theorem B1246027 : Blo 1244440 1246027 := bstep (se 1 (by rfl) ⟨934520, by rfl⟩ : syracuseStep 1246027 = 1869041) B1869041
theorem B1246039 : Blo 1244440 1246039 := bstep (se 1 (by rfl) ⟨934529, by rfl⟩ : syracuseStep 1246039 = 1869059) B1869059
theorem B4793177 : Blo 1244440 4793177 := bstep (se 2 (by rfl) ⟨1797441, by rfl⟩ : syracuseStep 4793177 = 3594883) B3594883
theorem B1868633 : Blo 1244440 1868633 := bstep (se 2 (by rfl) ⟨700737, by rfl⟩ : syracuseStep 1868633 = 1401475) B1401475
theorem B1246059 : Blo 1244440 1246059 := bstep (se 1 (by rfl) ⟨934544, by rfl⟩ : syracuseStep 1246059 = 1869089) B1869089
theorem B1246071 : Blo 1244440 1246071 := bstep (se 1 (by rfl) ⟨934553, by rfl⟩ : syracuseStep 1246071 = 1869107) B1869107
theorem B1246091 : Blo 1244440 1246091 := bstep (se 1 (by rfl) ⟨934568, by rfl⟩ : syracuseStep 1246091 = 1869137) B1869137
theorem B1246103 : Blo 1244440 1246103 := bstep (se 1 (by rfl) ⟨934577, by rfl⟩ : syracuseStep 1246103 = 1869155) B1869155
theorem B1246123 : Blo 1244440 1246123 := bstep (se 1 (by rfl) ⟨934592, by rfl⟩ : syracuseStep 1246123 = 1869185) B1869185
theorem B1246135 : Blo 1244440 1246135 := bstep (se 1 (by rfl) ⟨934601, by rfl⟩ : syracuseStep 1246135 = 1869203) B1869203
theorem B4203467 : Blo 1244440 4203467 := bstep (se 1 (by rfl) ⟨3152600, by rfl⟩ : syracuseStep 4203467 = 6305201) B6305201
theorem B2802635 : Blo 1244440 2802635 := bstep (se 1 (by rfl) ⟨2101976, by rfl⟩ : syracuseStep 2802635 = 4203953) B4203953
theorem B1868747 : Blo 1244440 1868747 := bstep (se 1 (by rfl) ⟨1401560, by rfl⟩ : syracuseStep 1868747 = 2803121) B2803121
theorem B1246155 : Blo 1244440 1246155 := bstep (se 1 (by rfl) ⟨934616, by rfl⟩ : syracuseStep 1246155 = 1869233) B1869233
theorem B1868759 : Blo 1244440 1868759 := bstep (se 1 (by rfl) ⟨1401569, by rfl⟩ : syracuseStep 1868759 = 2803139) B2803139
theorem B1246167 : Blo 1244440 1246167 := bstep (se 1 (by rfl) ⟨934625, by rfl⟩ : syracuseStep 1246167 = 1869251) B1869251
theorem B1401835 : Blo 1244440 1401835 := bstep (se 1 (by rfl) ⟨1051376, by rfl⟩ : syracuseStep 1401835 = 2102753) B2102753
theorem B1246187 : Blo 1244440 1246187 := bstep (se 1 (by rfl) ⟨934640, by rfl⟩ : syracuseStep 1246187 = 1869281) B1869281
theorem B1246199 : Blo 1244440 1246199 := bstep (se 1 (by rfl) ⟨934649, by rfl⟩ : syracuseStep 1246199 = 1869299) B1869299
theorem B2802689 : Blo 1244440 2802689 := bstep (se 2 (by rfl) ⟨1051008, by rfl⟩ : syracuseStep 2802689 = 2102017) B2102017
theorem B1246219 : Blo 1244440 1246219 := bstep (se 1 (by rfl) ⟨934664, by rfl⟩ : syracuseStep 1246219 = 1869329) B1869329
theorem B1246231 : Blo 1244440 1246231 := bstep (se 1 (by rfl) ⟨934673, by rfl⟩ : syracuseStep 1246231 = 1869347) B1869347
theorem B1868825 : Blo 1244440 1868825 := bstep (se 2 (by rfl) ⟨700809, by rfl⟩ : syracuseStep 1868825 = 1401619) B1401619
theorem B1246251 : Blo 1244440 1246251 := bstep (se 1 (by rfl) ⟨934688, by rfl⟩ : syracuseStep 1246251 = 1869377) B1869377
theorem B1246263 : Blo 1244440 1246263 := bstep (se 1 (by rfl) ⟨934697, by rfl⟩ : syracuseStep 1246263 = 1869395) B1869395
theorem B2769985 : Blo 1244440 2769985 := bstep (se 2 (by rfl) ⟨1038744, by rfl⟩ : syracuseStep 2769985 = 2077489) B2077489
theorem B3548225 : Blo 1244440 3548225 := bstep (se 2 (by rfl) ⟨1330584, by rfl⟩ : syracuseStep 3548225 = 2661169) B2661169
theorem B1246283 : Blo 1244440 1246283 := bstep (se 1 (by rfl) ⟨934712, by rfl⟩ : syracuseStep 1246283 = 1869425) B1869425
theorem B1401943 : Blo 1244440 1401943 := bstep (se 1 (by rfl) ⟨1051457, by rfl⟩ : syracuseStep 1401943 = 2102915) B2102915
theorem B1246295 : Blo 1244440 1246295 := bstep (se 1 (by rfl) ⟨934721, by rfl⟩ : syracuseStep 1246295 = 1869443) B1869443
theorem B3548249 : Blo 1244440 3548249 := bstep (se 2 (by rfl) ⟨1330593, by rfl⟩ : syracuseStep 3548249 = 2661187) B2661187
theorem B1246315 : Blo 1244440 1246315 := bstep (se 1 (by rfl) ⟨934736, by rfl⟩ : syracuseStep 1246315 = 1869473) B1869473
theorem B1246327 : Blo 1244440 1246327 := bstep (se 1 (by rfl) ⟨934745, by rfl⟩ : syracuseStep 1246327 = 1869491) B1869491
theorem B9847939 : Blo 1244440 9847939 := bstep (se 1 (by rfl) ⟨7385954, by rfl⟩ : syracuseStep 9847939 = 14771909) B14771909
theorem B1893515 : Blo 1244440 1893515 := bstep (se 1 (by rfl) ⟨1420136, by rfl⟩ : syracuseStep 1893515 = 2840273) B2840273
theorem B1868939 : Blo 1244440 1868939 := bstep (se 1 (by rfl) ⟨1401704, by rfl⟩ : syracuseStep 1868939 = 2803409) B2803409
theorem B1246347 : Blo 1244440 1246347 := bstep (se 1 (by rfl) ⟨934760, by rfl⟩ : syracuseStep 1246347 = 1869521) B1869521
theorem B1868951 : Blo 1244440 1868951 := bstep (se 1 (by rfl) ⟨1401713, by rfl⟩ : syracuseStep 1868951 = 2803427) B2803427
theorem B1246359 : Blo 1244440 1246359 := bstep (se 1 (by rfl) ⟨934769, by rfl⟩ : syracuseStep 1246359 = 1869539) B1869539
theorem B1246379 : Blo 1244440 1246379 := bstep (se 1 (by rfl) ⟨934784, by rfl⟩ : syracuseStep 1246379 = 1869569) B1869569
theorem B1279159 : Blo 1244440 1279159 := bstep (se 1 (by rfl) ⟨959369, by rfl⟩ : syracuseStep 1279159 = 1918739) B1918739
theorem B1246391 : Blo 1244440 1246391 := bstep (se 1 (by rfl) ⟨934793, by rfl⟩ : syracuseStep 1246391 = 1869587) B1869587
theorem B1246411 : Blo 1244440 1246411 := bstep (se 1 (by rfl) ⟨934808, by rfl⟩ : syracuseStep 1246411 = 1869617) B1869617
theorem B1246423 : Blo 1244440 1246423 := bstep (se 1 (by rfl) ⟨934817, by rfl⟩ : syracuseStep 1246423 = 1869635) B1869635
theorem B4203737 : Blo 1244440 4203737 := bstep (se 2 (by rfl) ⟨1576401, by rfl⟩ : syracuseStep 4203737 = 3152803) B3152803
theorem B2802905 : Blo 1244440 2802905 := bstep (se 2 (by rfl) ⟨1051089, by rfl⟩ : syracuseStep 2802905 = 2102179) B2102179
theorem B1869017 : Blo 1244440 1869017 := bstep (se 2 (by rfl) ⟨700881, by rfl⟩ : syracuseStep 1869017 = 1401763) B1401763
theorem B2524403 : Blo 1244440 2524403 := bstep (se 1 (by rfl) ⟨1893302, by rfl⟩ : syracuseStep 2524403 = 3786605) B3786605
theorem B1402123 : Blo 1244440 1402123 := bstep (se 1 (by rfl) ⟨1051592, by rfl⟩ : syracuseStep 1402123 = 2103185) B2103185
theorem B2802995 : Blo 1244440 2802995 := bstep (se 1 (by rfl) ⟨2102246, by rfl⟩ : syracuseStep 2802995 = 4204493) B4204493
theorem B10634561 : Blo 1244440 10634561 := bstep (se 2 (by rfl) ⟨3987960, by rfl⟩ : syracuseStep 10634561 = 7975921) B7975921
theorem B1869131 : Blo 1244440 1869131 := bstep (se 1 (by rfl) ⟨1401848, by rfl⟩ : syracuseStep 1869131 = 2803697) B2803697
theorem B2803031 : Blo 1244440 2803031 := bstep (se 1 (by rfl) ⟨2102273, by rfl⟩ : syracuseStep 2803031 = 4204547) B4204547
theorem B1262935 : Blo 1244440 1262935 := bstep (se 1 (by rfl) ⟨947201, by rfl⟩ : syracuseStep 1262935 = 1894403) B1894403
theorem B1869143 : Blo 1244440 1869143 := bstep (se 1 (by rfl) ⟨1401857, by rfl⟩ : syracuseStep 1869143 = 2803715) B2803715
theorem B1402231 : Blo 1244440 1402231 := bstep (se 1 (by rfl) ⟨1051673, by rfl⟩ : syracuseStep 1402231 = 2103347) B2103347
theorem B6309251 : Blo 1244440 6309251 := bstep (se 1 (by rfl) ⟨4731938, by rfl⟩ : syracuseStep 6309251 = 9463877) B9463877
theorem B1869209 : Blo 1244440 1869209 := bstep (se 2 (by rfl) ⟨700953, by rfl⟩ : syracuseStep 1869209 = 1401907) B1401907
theorem B2803211 : Blo 1244440 2803211 := bstep (se 1 (by rfl) ⟨2102408, by rfl⟩ : syracuseStep 2803211 = 4204817) B4204817
theorem B1869323 : Blo 1244440 1869323 := bstep (se 1 (by rfl) ⟨1401992, by rfl⟩ : syracuseStep 1869323 = 2803985) B2803985
theorem B1869335 : Blo 1244440 1869335 := bstep (se 1 (by rfl) ⟨1402001, by rfl⟩ : syracuseStep 1869335 = 2804003) B2804003
theorem B2958899 : Blo 1244440 2958899 := bstep (se 1 (by rfl) ⟨2219174, by rfl⟩ : syracuseStep 2958899 = 4438349) B4438349
theorem B2803265 : Blo 1244440 2803265 := bstep (se 2 (by rfl) ⟨1051224, by rfl⟩ : syracuseStep 2803265 = 2102449) B2102449
theorem B1869401 : Blo 1244440 1869401 := bstep (se 2 (by rfl) ⟨701025, by rfl⟩ : syracuseStep 1869401 = 1402051) B1402051
theorem B5318237 : Blo 1244440 5318237 := bstep (se 3 (by rfl) ⟨997169, by rfl⟩ : syracuseStep 5318237 = 1994339) B1994339
theorem B2991809 : Blo 1244440 2991809 := bstep (se 2 (by rfl) ⟨1121928, by rfl⟩ : syracuseStep 2991809 = 2243857) B2243857
theorem B1869515 : Blo 1244440 1869515 := bstep (se 1 (by rfl) ⟨1402136, by rfl⟩ : syracuseStep 1869515 = 2804273) B2804273
theorem B1869527 : Blo 1244440 1869527 := bstep (se 1 (by rfl) ⟨1402145, by rfl⟩ : syracuseStep 1869527 = 2804291) B2804291
theorem B2131723 : Blo 1244440 2131723 := bstep (se 1 (by rfl) ⟨1598792, by rfl⟩ : syracuseStep 2131723 = 3197585) B3197585
theorem B2803481 : Blo 1244440 2803481 := bstep (se 2 (by rfl) ⟨1051305, by rfl⟩ : syracuseStep 2803481 = 2102611) B2102611
theorem B1869593 : Blo 1244440 1869593 := bstep (se 2 (by rfl) ⟨701097, by rfl⟩ : syracuseStep 1869593 = 1402195) B1402195
theorem B20186981 : Blo 1244440 20186981 := bstep (se 4 (by rfl) ⟨1892529, by rfl⟩ : syracuseStep 20186981 = 3785059) B3785059
theorem B2803571 : Blo 1244440 2803571 := bstep (se 1 (by rfl) ⟨2102678, by rfl⟩ : syracuseStep 2803571 = 4205357) B4205357
theorem B4204439 : Blo 1244440 4204439 := bstep (se 1 (by rfl) ⟨3153329, by rfl⟩ : syracuseStep 4204439 = 6306659) B6306659
theorem B2803607 : Blo 1244440 2803607 := bstep (se 1 (by rfl) ⟨2102705, by rfl⟩ : syracuseStep 2803607 = 4205411) B4205411
theorem B10102801 : Blo 1244440 10102801 := bstep (se 2 (by rfl) ⟨3788550, by rfl⟩ : syracuseStep 10102801 = 7577101) B7577101
theorem B1894423 : Blo 1244440 1894423 := bstep (se 1 (by rfl) ⟨1420817, by rfl⟩ : syracuseStep 1894423 = 2841635) B2841635
theorem B2992193 : Blo 1244440 2992193 := bstep (se 2 (by rfl) ⟨1122072, by rfl⟩ : syracuseStep 2992193 = 2244145) B2244145
theorem B2803787 : Blo 1244440 2803787 := bstep (se 1 (by rfl) ⟨2102840, by rfl⟩ : syracuseStep 2803787 = 4205681) B4205681
theorem B2803841 : Blo 1244440 2803841 := bstep (se 2 (by rfl) ⟨1051440, by rfl⟩ : syracuseStep 2803841 = 2102881) B2102881
theorem B9717965 : Blo 1244440 9717965 := bstep (se 3 (by rfl) ⟨1822118, by rfl⟩ : syracuseStep 9717965 = 3644237) B3644237
theorem B1329419 : Blo 1244440 1329419 := bstep (se 1 (by rfl) ⟨997064, by rfl⟩ : syracuseStep 1329419 = 1994129) B1994129
theorem B2804057 : Blo 1244440 2804057 := bstep (se 2 (by rfl) ⟨1051521, by rfl⟩ : syracuseStep 2804057 = 2103043) B2103043
theorem B4204979 : Blo 1244440 4204979 := bstep (se 1 (by rfl) ⟨3153734, by rfl⟩ : syracuseStep 4204979 = 6307469) B6307469
theorem B2804147 : Blo 1244440 2804147 := bstep (se 1 (by rfl) ⟨2103110, by rfl⟩ : syracuseStep 2804147 = 4206221) B4206221
theorem B2804183 : Blo 1244440 2804183 := bstep (se 1 (by rfl) ⟨2103137, by rfl⟩ : syracuseStep 2804183 = 4206275) B4206275
theorem B1772057 : Blo 1244440 1772057 := bstep (se 2 (by rfl) ⟨664521, by rfl⟩ : syracuseStep 1772057 = 1329043) B1329043
theorem B7088705 : Blo 1244440 7088705 := bstep (se 2 (by rfl) ⟨2658264, by rfl⟩ : syracuseStep 7088705 = 5316529) B5316529
theorem B2804363 : Blo 1244440 2804363 := bstep (se 1 (by rfl) ⟨2103272, by rfl⟩ : syracuseStep 2804363 = 4206545) B4206545
theorem B4205249 : Blo 1244440 4205249 := bstep (se 2 (by rfl) ⟨1576968, by rfl⟩ : syracuseStep 4205249 = 3153937) B3153937
theorem B2804417 : Blo 1244440 2804417 := bstep (se 2 (by rfl) ⟨1051656, by rfl⟩ : syracuseStep 2804417 = 2103313) B2103313
theorem B3992267 : Blo 1244440 3992267 := bstep (se 1 (by rfl) ⟨2994200, by rfl⟩ : syracuseStep 3992267 = 5988401) B5988401
theorem B1575703 : Blo 1244440 1575703 := bstep (se 1 (by rfl) ⟨1181777, by rfl⟩ : syracuseStep 1575703 = 2363555) B2363555
theorem B3197771 : Blo 1244440 3197771 := bstep (se 1 (by rfl) ⟨2398328, by rfl⟩ : syracuseStep 3197771 = 4796657) B4796657
theorem B2100107 : Blo 1244440 2100107 := bstep (se 1 (by rfl) ⟨1575080, by rfl⟩ : syracuseStep 2100107 = 3150161) B3150161
theorem B4492253 : Blo 1244440 4492253 := bstep (se 3 (by rfl) ⟨842297, by rfl⟩ : syracuseStep 4492253 = 1684595) B1684595
theorem B4729859 : Blo 1244440 4729859 := bstep (se 1 (by rfl) ⟨3547394, by rfl⟩ : syracuseStep 4729859 = 7094789) B7094789
theorem B2100235 : Blo 1244440 2100235 := bstep (se 1 (by rfl) ⟨1575176, by rfl⟩ : syracuseStep 2100235 = 3150353) B3150353
theorem B4729873 : Blo 1244440 4729873 := bstep (se 2 (by rfl) ⟨1773702, by rfl⟩ : syracuseStep 4729873 = 3547405) B3547405
theorem B9464849 : Blo 1244440 9464849 := bstep (se 2 (by rfl) ⟨3549318, by rfl⟩ : syracuseStep 9464849 = 7098637) B7098637
theorem B3992665 : Blo 1244440 3992665 := bstep (se 2 (by rfl) ⟨1497249, by rfl⟩ : syracuseStep 3992665 = 2994499) B2994499
theorem B5983325 : Blo 1244440 5983325 := bstep (se 3 (by rfl) ⟨1121873, by rfl⟩ : syracuseStep 5983325 = 2243747) B2243747
theorem B1772695 : Blo 1244440 1772695 := bstep (se 1 (by rfl) ⟨1329521, by rfl⟩ : syracuseStep 1772695 = 2659043) B2659043
theorem B2100377 : Blo 1244440 2100377 := bstep (se 2 (by rfl) ⟨787641, by rfl⟩ : syracuseStep 2100377 = 1575283) B1575283
theorem B38358197 : Blo 1244440 38358197 := bstep (se 5 (by rfl) ⟨1798040, by rfl⟩ : syracuseStep 38358197 = 3596081) B3596081
theorem B2362583 : Blo 1244440 2362583 := bstep (se 1 (by rfl) ⟨1771937, by rfl⟩ : syracuseStep 2362583 = 3543875) B3543875
theorem B4205789 : Blo 1244440 4205789 := bstep (se 3 (by rfl) ⟨788585, by rfl⟩ : syracuseStep 4205789 = 1577171) B1577171
theorem B2993431 : Blo 1244440 2993431 := bstep (se 1 (by rfl) ⟨2245073, by rfl⟩ : syracuseStep 2993431 = 4490147) B4490147
theorem B4320535 : Blo 1244440 4320535 := bstep (se 1 (by rfl) ⟨3240401, by rfl⟩ : syracuseStep 4320535 = 6480803) B6480803
theorem B2100505 : Blo 1244440 2100505 := bstep (se 2 (by rfl) ⟨787689, by rfl⟩ : syracuseStep 2100505 = 1575379) B1575379
theorem B2395417 : Blo 1244440 2395417 := bstep (se 2 (by rfl) ⟨898281, by rfl⟩ : syracuseStep 2395417 = 1796563) B1796563
theorem B5049665 : Blo 1244440 5049665 := bstep (se 2 (by rfl) ⟨1893624, by rfl⟩ : syracuseStep 5049665 = 3787249) B3787249
theorem B4730177 : Blo 1244440 4730177 := bstep (se 2 (by rfl) ⟨1773816, by rfl⟩ : syracuseStep 4730177 = 3547633) B3547633
theorem B2559371 : Blo 1244440 2559371 := bstep (se 1 (by rfl) ⟨1919528, by rfl⟩ : syracuseStep 2559371 = 3839057) B3839057
theorem B9457073 : Blo 1244440 9457073 := bstep (se 2 (by rfl) ⟨3546402, by rfl⟩ : syracuseStep 9457073 = 7092805) B7092805
theorem B1330615 : Blo 1244440 1330615 := bstep (se 1 (by rfl) ⟨997961, by rfl⟩ : syracuseStep 1330615 = 1995923) B1995923
theorem B1420747 : Blo 1244440 1420747 := bstep (se 1 (by rfl) ⟨1065560, by rfl⟩ : syracuseStep 1420747 = 2131121) B2131121
theorem B2362841 : Blo 1244440 2362841 := bstep (se 2 (by rfl) ⟨886065, by rfl⟩ : syracuseStep 2362841 = 1772131) B1772131
theorem B1576523 : Blo 1244440 1576523 := bstep (se 1 (by rfl) ⟨1182392, by rfl⟩ : syracuseStep 1576523 = 2364785) B2364785
theorem B1994519 : Blo 1244440 1994519 := bstep (se 1 (by rfl) ⟨1495889, by rfl⟩ : syracuseStep 1994519 = 2991779) B2991779
theorem B2101079 : Blo 1244440 2101079 := bstep (se 1 (by rfl) ⟨1575809, by rfl⟩ : syracuseStep 2101079 = 3151619) B3151619
theorem B6303581 : Blo 1244440 6303581 := bstep (se 3 (by rfl) ⟨1181921, by rfl⟩ : syracuseStep 6303581 = 2363843) B2363843
theorem B2363251 : Blo 1244440 2363251 := bstep (se 1 (by rfl) ⟨1772438, by rfl⟩ : syracuseStep 2363251 = 3544877) B3544877
theorem B1994647 : Blo 1244440 1994647 := bstep (se 1 (by rfl) ⟨1495985, by rfl⟩ : syracuseStep 1994647 = 2991971) B2991971
theorem B9457559 : Blo 1244440 9457559 := bstep (se 1 (by rfl) ⟨7093169, by rfl⟩ : syracuseStep 9457559 = 14186339) B14186339
theorem B4550593 : Blo 1244440 4550593 := bstep (se 2 (by rfl) ⟨1706472, by rfl⟩ : syracuseStep 4550593 = 3412945) B3412945
theorem B1773515 : Blo 1244440 1773515 := bstep (se 1 (by rfl) ⟨1330136, by rfl⟩ : syracuseStep 1773515 = 2660273) B2660273
theorem B2101207 : Blo 1244440 2101207 := bstep (se 1 (by rfl) ⟨1575905, by rfl⟩ : syracuseStep 2101207 = 3151811) B3151811
theorem B1994711 : Blo 1244440 1994711 := bstep (se 1 (by rfl) ⟨1496033, by rfl⟩ : syracuseStep 1994711 = 2992067) B2992067
theorem B4730845 : Blo 1244440 4730845 := bstep (se 3 (by rfl) ⟨887033, by rfl⟩ : syracuseStep 4730845 = 1774067) B1774067
theorem B13455395 : Blo 1244440 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B5320835 : Blo 1244440 5320835 := bstep (se 1 (by rfl) ⟨3990626, by rfl⟩ : syracuseStep 5320835 = 7981253) B7981253
theorem B1495255 : Blo 1244440 1495255 := bstep (se 1 (by rfl) ⟨1121441, by rfl⟩ : syracuseStep 1495255 = 2242883) B2242883
theorem B2658521 : Blo 1244440 2658521 := bstep (se 2 (by rfl) ⟨996945, by rfl⟩ : syracuseStep 2658521 = 1993891) B1993891
theorem B1577227 : Blo 1244440 1577227 := bstep (se 1 (by rfl) ⟨1182920, by rfl⟩ : syracuseStep 1577227 = 2365841) B2365841
theorem B8982829 : Blo 1244440 8982829 := bstep (se 3 (by rfl) ⟨1684280, by rfl⟩ : syracuseStep 8982829 = 3368561) B3368561
theorem B2363737 : Blo 1244440 2363737 := bstep (se 2 (by rfl) ⟨886401, by rfl⟩ : syracuseStep 2363737 = 1772803) B1772803
theorem B14184881 : Blo 1244440 14184881 := bstep (se 2 (by rfl) ⟨5319330, by rfl⟩ : syracuseStep 14184881 = 10638661) B10638661
theorem B5321177 : Blo 1244440 5321177 := bstep (se 2 (by rfl) ⟨1995441, by rfl⟩ : syracuseStep 5321177 = 3990883) B3990883
theorem B1577495 : Blo 1244440 1577495 := bstep (se 1 (by rfl) ⟨1183121, by rfl⟩ : syracuseStep 1577495 = 2366243) B2366243
theorem B8516161 : Blo 1244440 8516161 := bstep (se 2 (by rfl) ⟨3193560, by rfl⟩ : syracuseStep 8516161 = 6387121) B6387121
theorem B2101835 : Blo 1244440 2101835 := bstep (se 1 (by rfl) ⟨1576376, by rfl⟩ : syracuseStep 2101835 = 3152753) B3152753
theorem B6828695 : Blo 1244440 6828695 := bstep (se 1 (by rfl) ⟨5121521, by rfl⟩ : syracuseStep 6828695 = 10243043) B10243043
theorem B3150515 : Blo 1244440 3150515 := bstep (se 1 (by rfl) ⟨2362886, by rfl⟩ : syracuseStep 3150515 = 4725773) B4725773
theorem B2101963 : Blo 1244440 2101963 := bstep (se 1 (by rfl) ⟨1576472, by rfl⟩ : syracuseStep 2101963 = 3152945) B3152945
theorem B7983917 : Blo 1244440 7983917 := bstep (se 3 (by rfl) ⟨1496984, by rfl⟩ : syracuseStep 7983917 = 2993969) B2993969
theorem B2102105 : Blo 1244440 2102105 := bstep (se 2 (by rfl) ⟨788289, by rfl⟩ : syracuseStep 2102105 = 1576579) B1576579
theorem B2659187 : Blo 1244440 2659187 := bstep (se 1 (by rfl) ⟨1994390, by rfl⟩ : syracuseStep 2659187 = 3988781) B3988781
theorem B2364299 : Blo 1244440 2364299 := bstep (se 1 (by rfl) ⟨1773224, by rfl⟩ : syracuseStep 2364299 = 3546449) B3546449
theorem B3789719 : Blo 1244440 3789719 := bstep (se 1 (by rfl) ⟨2842289, by rfl⟩ : syracuseStep 3789719 = 5684579) B5684579
theorem B1774489 : Blo 1244440 1774489 := bstep (se 2 (by rfl) ⟨665433, by rfl⟩ : syracuseStep 1774489 = 1330867) B1330867
theorem B5395373 : Blo 1244440 5395373 := bstep (se 3 (by rfl) ⟨1011632, by rfl⟩ : syracuseStep 5395373 = 2023265) B2023265
theorem B5682113 : Blo 1244440 5682113 := bstep (se 2 (by rfl) ⟨2130792, by rfl⟩ : syracuseStep 5682113 = 4261585) B4261585
theorem B3150809 : Blo 1244440 3150809 := bstep (se 2 (by rfl) ⟨1181553, by rfl⟩ : syracuseStep 3150809 = 2363107) B2363107
theorem B2102233 : Blo 1244440 2102233 := bstep (se 2 (by rfl) ⟨788337, by rfl⟩ : syracuseStep 2102233 = 1576675) B1576675
theorem B16176145 : Blo 1244440 16176145 := bstep (se 2 (by rfl) ⟨6066054, by rfl⟩ : syracuseStep 16176145 = 12132109) B12132109
theorem B7574573 : Blo 1244440 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B6394925 : Blo 1244440 6394925 := bstep (se 3 (by rfl) ⟨1199048, by rfl⟩ : syracuseStep 6394925 = 2398097) B2398097
theorem B2364481 : Blo 1244440 2364481 := bstep (se 2 (by rfl) ⟨886680, by rfl⟩ : syracuseStep 2364481 = 1773361) B1773361
theorem B4789469 : Blo 1244440 4789469 := bstep (se 3 (by rfl) ⟨898025, by rfl⟩ : syracuseStep 4789469 = 1796051) B1796051
theorem B4732121 : Blo 1244440 4732121 := bstep (se 2 (by rfl) ⟨1774545, by rfl⟩ : syracuseStep 4732121 = 3549091) B3549091
theorem B3593495 : Blo 1244440 3593495 := bstep (se 1 (by rfl) ⟨2695121, by rfl⟩ : syracuseStep 3593495 = 5390243) B5390243
theorem B8975681 : Blo 1244440 8975681 := bstep (se 2 (by rfl) ⟨3365880, by rfl⟩ : syracuseStep 8975681 = 6731761) B6731761
theorem B21288257 : Blo 1244440 21288257 := bstep (se 2 (by rfl) ⟨7983096, by rfl⟩ : syracuseStep 21288257 = 15966193) B15966193
theorem B4552139 : Blo 1244440 4552139 := bstep (se 1 (by rfl) ⟨3414104, by rfl⟩ : syracuseStep 4552139 = 6828209) B6828209
theorem B2102807 : Blo 1244440 2102807 := bstep (se 1 (by rfl) ⟨1577105, by rfl⟩ : syracuseStep 2102807 = 3154211) B3154211
theorem B4200011 : Blo 1244440 4200011 := bstep (se 1 (by rfl) ⟨3150008, by rfl⟩ : syracuseStep 4200011 = 6300017) B6300017
theorem B4486745 : Blo 1244440 4486745 := bstep (se 2 (by rfl) ⟨1682529, by rfl⟩ : syracuseStep 4486745 = 3365059) B3365059
theorem B4789853 : Blo 1244440 4789853 := bstep (se 3 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 4789853 = 1796195) B1796195
theorem B2102935 : Blo 1244440 2102935 := bstep (se 1 (by rfl) ⟨1577201, by rfl⟩ : syracuseStep 2102935 = 3154403) B3154403
theorem B2365195 : Blo 1244440 2365195 := bstep (se 1 (by rfl) ⟨1773896, by rfl⟩ : syracuseStep 2365195 = 3547793) B3547793
theorem B2365271 : Blo 1244440 2365271 := bstep (se 1 (by rfl) ⟨1773953, by rfl⟩ : syracuseStep 2365271 = 3547907) B3547907
theorem B4200281 : Blo 1244440 4200281 := bstep (se 2 (by rfl) ⟨1575105, by rfl⟩ : syracuseStep 4200281 = 3150211) B3150211
theorem B6305687 : Blo 1244440 6305687 := bstep (se 1 (by rfl) ⟨4729265, by rfl⟩ : syracuseStep 6305687 = 9458531) B9458531
theorem B10647683 : Blo 1244440 10647683 := bstep (se 1 (by rfl) ⟨7985762, by rfl⟩ : syracuseStep 10647683 = 15971525) B15971525
theorem B3545309 : Blo 1244440 3545309 := bstep (se 3 (by rfl) ⟨664745, by rfl⟩ : syracuseStep 3545309 = 1329491) B1329491
theorem B2660683 : Blo 1244440 2660683 := bstep (se 1 (by rfl) ⟨1995512, by rfl⟩ : syracuseStep 2660683 = 3991025) B3991025
theorem B2800025 : Blo 1244440 2800025 := bstep (se 2 (by rfl) ⟨1050009, by rfl⟩ : syracuseStep 2800025 = 2100019) B2100019
theorem B2800115 : Blo 1244440 2800115 := bstep (se 1 (by rfl) ⟨2100086, by rfl⟩ : syracuseStep 2800115 = 4200173) B4200173
theorem B2365939 : Blo 1244440 2365939 := bstep (se 1 (by rfl) ⟨1774454, by rfl⟩ : syracuseStep 2365939 = 3548909) B3548909
theorem B2800151 : Blo 1244440 2800151 := bstep (se 1 (by rfl) ⟨2100113, by rfl⟩ : syracuseStep 2800151 = 4200227) B4200227
theorem B4200983 : Blo 1244440 4200983 := bstep (se 1 (by rfl) ⟨3150737, by rfl⟩ : syracuseStep 4200983 = 6301475) B6301475
theorem B3152459 : Blo 1244440 3152459 := bstep (se 1 (by rfl) ⟨2364344, by rfl⟩ : syracuseStep 3152459 = 4728689) B4728689
theorem B2800331 : Blo 1244440 2800331 := bstep (se 1 (by rfl) ⟨2100248, by rfl⟩ : syracuseStep 2800331 = 4200497) B4200497
theorem B2366167 : Blo 1244440 2366167 := bstep (se 1 (by rfl) ⟨1774625, by rfl⟩ : syracuseStep 2366167 = 3549251) B3549251
theorem B10631897 : Blo 1244440 10631897 := bstep (se 2 (by rfl) ⟨3986961, by rfl⟩ : syracuseStep 10631897 = 7973923) B7973923
theorem B76667633 : Blo 1244440 76667633 := bstep (se 2 (by rfl) ⟨28750362, by rfl⟩ : syracuseStep 76667633 = 57500725) B57500725
theorem B2800385 : Blo 1244440 2800385 := bstep (se 2 (by rfl) ⟨1050144, by rfl⟩ : syracuseStep 2800385 = 2100289) B2100289
theorem B4487987 : Blo 1244440 4487987 := bstep (se 1 (by rfl) ⟨3365990, by rfl⟩ : syracuseStep 4487987 = 6731981) B6731981
theorem B2366273 : Blo 1244440 2366273 := bstep (se 2 (by rfl) ⟨887352, by rfl⟩ : syracuseStep 2366273 = 1774705) B1774705
theorem B4258739 : Blo 1244440 4258739 := bstep (se 1 (by rfl) ⟨3194054, by rfl⟩ : syracuseStep 4258739 = 6388109) B6388109
theorem B1866713 : Blo 1244440 1866713 := bstep (se 2 (by rfl) ⟨700017, by rfl⟩ : syracuseStep 1866713 = 1400035) B1400035
theorem B2800601 : Blo 1244440 2800601 := bstep (se 2 (by rfl) ⟨1050225, by rfl⟩ : syracuseStep 2800601 = 2100451) B2100451
theorem B2800691 : Blo 1244440 2800691 := bstep (se 1 (by rfl) ⟨2100518, by rfl⟩ : syracuseStep 2800691 = 4201037) B4201037
theorem B4201523 : Blo 1244440 4201523 := bstep (se 1 (by rfl) ⟨3151142, by rfl⟩ : syracuseStep 4201523 = 6302285) B6302285
theorem B1866827 : Blo 1244440 1866827 := bstep (se 1 (by rfl) ⟨1400120, by rfl⟩ : syracuseStep 1866827 = 2800241) B2800241
theorem B1866839 : Blo 1244440 1866839 := bstep (se 1 (by rfl) ⟨1400129, by rfl⟩ : syracuseStep 1866839 = 2800259) B2800259
theorem B2800727 : Blo 1244440 2800727 := bstep (se 1 (by rfl) ⟨2100545, by rfl⟩ : syracuseStep 2800727 = 4201091) B4201091
theorem B5987459 : Blo 1244440 5987459 := bstep (se 1 (by rfl) ⟨4490594, by rfl⟩ : syracuseStep 5987459 = 8981189) B8981189
theorem B1866905 : Blo 1244440 1866905 := bstep (se 2 (by rfl) ⟨700089, by rfl⟩ : syracuseStep 1866905 = 1400179) B1400179
theorem B5315777 : Blo 1244440 5315777 := bstep (se 2 (by rfl) ⟨1993416, by rfl⟩ : syracuseStep 5315777 = 3986833) B3986833
theorem B10640645 : Blo 1244440 10640645 := bstep (se 4 (by rfl) ⟨997560, by rfl⟩ : syracuseStep 10640645 = 1995121) B1995121
theorem B1867019 : Blo 1244440 1867019 := bstep (se 1 (by rfl) ⟨1400264, by rfl⟩ : syracuseStep 1867019 = 2800529) B2800529
theorem B2800907 : Blo 1244440 2800907 := bstep (se 1 (by rfl) ⟨2100680, by rfl⟩ : syracuseStep 2800907 = 4201361) B4201361
theorem B1867031 : Blo 1244440 1867031 := bstep (se 1 (by rfl) ⟨1400273, by rfl⟩ : syracuseStep 1867031 = 2800547) B2800547
theorem B1244459 : Blo 1244440 1244459 := bstep (se 1 (by rfl) ⟨933344, by rfl⟩ : syracuseStep 1244459 = 1866689) B1866689
theorem B1400107 : Blo 1244440 1400107 := bstep (se 1 (by rfl) ⟨1050080, by rfl⟩ : syracuseStep 1400107 = 2100161) B2100161
theorem B1244471 : Blo 1244440 1244471 := bstep (se 1 (by rfl) ⟨933353, by rfl⟩ : syracuseStep 1244471 = 1866707) B1866707
theorem B2800961 : Blo 1244440 2800961 := bstep (se 2 (by rfl) ⟨1050360, by rfl⟩ : syracuseStep 2800961 = 2100721) B2100721
theorem B4201793 : Blo 1244440 4201793 := bstep (se 2 (by rfl) ⟨1575672, by rfl⟩ : syracuseStep 4201793 = 3151345) B3151345
theorem B1244491 : Blo 1244440 1244491 := bstep (se 1 (by rfl) ⟨933368, by rfl⟩ : syracuseStep 1244491 = 1866737) B1866737
theorem B1244503 : Blo 1244440 1244503 := bstep (se 1 (by rfl) ⟨933377, by rfl⟩ : syracuseStep 1244503 = 1866755) B1866755
theorem B1867097 : Blo 1244440 1867097 := bstep (se 2 (by rfl) ⟨700161, by rfl⟩ : syracuseStep 1867097 = 1400323) B1400323
theorem B13131109 : Blo 1244440 13131109 := bstep (se 4 (by rfl) ⟨1231041, by rfl⟩ : syracuseStep 13131109 = 2462083) B2462083
theorem B1244523 : Blo 1244440 1244523 := bstep (se 1 (by rfl) ⟨933392, by rfl⟩ : syracuseStep 1244523 = 1866785) B1866785
theorem B1244535 : Blo 1244440 1244535 := bstep (se 1 (by rfl) ⟨933401, by rfl⟩ : syracuseStep 1244535 = 1866803) B1866803
theorem B1244555 : Blo 1244440 1244555 := bstep (se 1 (by rfl) ⟨933416, by rfl⟩ : syracuseStep 1244555 = 1866833) B1866833
theorem B1244567 : Blo 1244440 1244567 := bstep (se 1 (by rfl) ⟨933425, by rfl⟩ : syracuseStep 1244567 = 1866851) B1866851
theorem B1400215 : Blo 1244440 1400215 := bstep (se 1 (by rfl) ⟨1050161, by rfl⟩ : syracuseStep 1400215 = 2100323) B2100323
theorem B1244587 : Blo 1244440 1244587 := bstep (se 1 (by rfl) ⟨933440, by rfl⟩ : syracuseStep 1244587 = 1866881) B1866881
theorem B1244599 : Blo 1244440 1244599 := bstep (se 1 (by rfl) ⟨933449, by rfl⟩ : syracuseStep 1244599 = 1866899) B1866899
theorem B1244619 : Blo 1244440 1244619 := bstep (se 1 (by rfl) ⟨933464, by rfl⟩ : syracuseStep 1244619 = 1866929) B1866929
theorem B1867211 : Blo 1244440 1867211 := bstep (se 1 (by rfl) ⟨1400408, by rfl⟩ : syracuseStep 1867211 = 2800817) B2800817
theorem B1244631 : Blo 1244440 1244631 := bstep (se 1 (by rfl) ⟨933473, by rfl⟩ : syracuseStep 1244631 = 1866947) B1866947
theorem B1867223 : Blo 1244440 1867223 := bstep (se 1 (by rfl) ⟨1400417, by rfl⟩ : syracuseStep 1867223 = 2800835) B2800835
theorem B1244651 : Blo 1244440 1244651 := bstep (se 1 (by rfl) ⟨933488, by rfl⟩ : syracuseStep 1244651 = 1866977) B1866977
theorem B1244663 : Blo 1244440 1244663 := bstep (se 1 (by rfl) ⟨933497, by rfl⟩ : syracuseStep 1244663 = 1866995) B1866995
theorem B1244683 : Blo 1244440 1244683 := bstep (se 1 (by rfl) ⟨933512, by rfl⟩ : syracuseStep 1244683 = 1867025) B1867025
theorem B4726289 : Blo 1244440 4726289 := bstep (se 2 (by rfl) ⟨1772358, by rfl⟩ : syracuseStep 4726289 = 3544717) B3544717
theorem B1244695 : Blo 1244440 1244695 := bstep (se 1 (by rfl) ⟨933521, by rfl⟩ : syracuseStep 1244695 = 1867043) B1867043
theorem B3153431 : Blo 1244440 3153431 := bstep (se 1 (by rfl) ⟨2365073, by rfl⟩ : syracuseStep 3153431 = 4730147) B4730147
theorem B1867289 : Blo 1244440 1867289 := bstep (se 2 (by rfl) ⟨700233, by rfl⟩ : syracuseStep 1867289 = 1400467) B1400467
theorem B2801177 : Blo 1244440 2801177 := bstep (se 2 (by rfl) ⟨1050441, by rfl⟩ : syracuseStep 2801177 = 2100883) B2100883
theorem B2661913 : Blo 1244440 2661913 := bstep (se 2 (by rfl) ⟨998217, by rfl⟩ : syracuseStep 2661913 = 1996435) B1996435
theorem B1244715 : Blo 1244440 1244715 := bstep (se 1 (by rfl) ⟨933536, by rfl⟩ : syracuseStep 1244715 = 1867073) B1867073
theorem B1244727 : Blo 1244440 1244727 := bstep (se 1 (by rfl) ⟨933545, by rfl⟩ : syracuseStep 1244727 = 1867091) B1867091
theorem B1244747 : Blo 1244440 1244747 := bstep (se 1 (by rfl) ⟨933560, by rfl⟩ : syracuseStep 1244747 = 1867121) B1867121
theorem B1400395 : Blo 1244440 1400395 := bstep (se 1 (by rfl) ⟨1050296, by rfl⟩ : syracuseStep 1400395 = 2100593) B2100593
theorem B1244759 : Blo 1244440 1244759 := bstep (se 1 (by rfl) ⟨933569, by rfl⟩ : syracuseStep 1244759 = 1867139) B1867139
theorem B1244779 : Blo 1244440 1244779 := bstep (se 1 (by rfl) ⟨933584, by rfl⟩ : syracuseStep 1244779 = 1867169) B1867169
theorem B2801267 : Blo 1244440 2801267 := bstep (se 1 (by rfl) ⟨2100950, by rfl⟩ : syracuseStep 2801267 = 4201901) B4201901
theorem B1244791 : Blo 1244440 1244791 := bstep (se 1 (by rfl) ⟨933593, by rfl⟩ : syracuseStep 1244791 = 1867187) B1867187
theorem B1244811 : Blo 1244440 1244811 := bstep (se 1 (by rfl) ⟨933608, by rfl⟩ : syracuseStep 1244811 = 1867217) B1867217
theorem B1867403 : Blo 1244440 1867403 := bstep (se 1 (by rfl) ⟨1400552, by rfl⟩ : syracuseStep 1867403 = 2801105) B2801105
theorem B1244823 : Blo 1244440 1244823 := bstep (se 1 (by rfl) ⟨933617, by rfl⟩ : syracuseStep 1244823 = 1867235) B1867235
theorem B1867415 : Blo 1244440 1867415 := bstep (se 1 (by rfl) ⟨1400561, by rfl⟩ : syracuseStep 1867415 = 2801123) B2801123
theorem B2801303 : Blo 1244440 2801303 := bstep (se 1 (by rfl) ⟨2100977, by rfl⟩ : syracuseStep 2801303 = 4201955) B4201955
theorem B1244843 : Blo 1244440 1244843 := bstep (se 1 (by rfl) ⟨933632, by rfl⟩ : syracuseStep 1244843 = 1867265) B1867265
theorem B1244855 : Blo 1244440 1244855 := bstep (se 1 (by rfl) ⟨933641, by rfl⟩ : syracuseStep 1244855 = 1867283) B1867283
theorem B1400503 : Blo 1244440 1400503 := bstep (se 1 (by rfl) ⟨1050377, by rfl⟩ : syracuseStep 1400503 = 2100755) B2100755
theorem B1244875 : Blo 1244440 1244875 := bstep (se 1 (by rfl) ⟨933656, by rfl⟩ : syracuseStep 1244875 = 1867313) B1867313
theorem B1244887 : Blo 1244440 1244887 := bstep (se 1 (by rfl) ⟨933665, by rfl⟩ : syracuseStep 1244887 = 1867331) B1867331
theorem B1867481 : Blo 1244440 1867481 := bstep (se 2 (by rfl) ⟨700305, by rfl⟩ : syracuseStep 1867481 = 1400611) B1400611
theorem B1244907 : Blo 1244440 1244907 := bstep (se 1 (by rfl) ⟨933680, by rfl⟩ : syracuseStep 1244907 = 1867361) B1867361
theorem B1244919 : Blo 1244440 1244919 := bstep (se 1 (by rfl) ⟨933689, by rfl⟩ : syracuseStep 1244919 = 1867379) B1867379
theorem B1244939 : Blo 1244440 1244939 := bstep (se 1 (by rfl) ⟨933704, by rfl⟩ : syracuseStep 1244939 = 1867409) B1867409
theorem B7978769 : Blo 1244440 7978769 := bstep (se 2 (by rfl) ⟨2992038, by rfl⟩ : syracuseStep 7978769 = 5984077) B5984077
theorem B1244951 : Blo 1244440 1244951 := bstep (se 1 (by rfl) ⟨933713, by rfl⟩ : syracuseStep 1244951 = 1867427) B1867427
theorem B1244971 : Blo 1244440 1244971 := bstep (se 1 (by rfl) ⟨933728, by rfl⟩ : syracuseStep 1244971 = 1867457) B1867457
theorem B1244983 : Blo 1244440 1244983 := bstep (se 1 (by rfl) ⟨933737, by rfl⟩ : syracuseStep 1244983 = 1867475) B1867475
theorem B7094081 : Blo 1244440 7094081 := bstep (se 2 (by rfl) ⟨2660280, by rfl⟩ : syracuseStep 7094081 = 5320561) B5320561
theorem B14196545 : Blo 1244440 14196545 := bstep (se 2 (by rfl) ⟨5323704, by rfl⟩ : syracuseStep 14196545 = 10647409) B10647409
theorem B1245003 : Blo 1244440 1245003 := bstep (se 1 (by rfl) ⟨933752, by rfl⟩ : syracuseStep 1245003 = 1867505) B1867505
theorem B1867595 : Blo 1244440 1867595 := bstep (se 1 (by rfl) ⟨1400696, by rfl⟩ : syracuseStep 1867595 = 2801393) B2801393
theorem B2801483 : Blo 1244440 2801483 := bstep (se 1 (by rfl) ⟨2101112, by rfl⟩ : syracuseStep 2801483 = 4202225) B4202225
theorem B1245015 : Blo 1244440 1245015 := bstep (se 1 (by rfl) ⟨933761, by rfl⟩ : syracuseStep 1245015 = 1867523) B1867523
theorem B1867607 : Blo 1244440 1867607 := bstep (se 1 (by rfl) ⟨1400705, by rfl⟩ : syracuseStep 1867607 = 2801411) B2801411
theorem B2244439 : Blo 1244440 2244439 := bstep (se 1 (by rfl) ⟨1683329, by rfl⟩ : syracuseStep 2244439 = 3366659) B3366659
theorem B4202333 : Blo 1244440 4202333 := bstep (se 3 (by rfl) ⟨787937, by rfl⟩ : syracuseStep 4202333 = 1575875) B1575875
theorem B1245035 : Blo 1244440 1245035 := bstep (se 1 (by rfl) ⟨933776, by rfl⟩ : syracuseStep 1245035 = 1867553) B1867553
theorem B1400683 : Blo 1244440 1400683 := bstep (se 1 (by rfl) ⟨1050512, by rfl⟩ : syracuseStep 1400683 = 2101025) B2101025
theorem B15138677 : Blo 1244440 15138677 := bstep (se 5 (by rfl) ⟨709625, by rfl⟩ : syracuseStep 15138677 = 1419251) B1419251
theorem B1245047 : Blo 1244440 1245047 := bstep (se 1 (by rfl) ⟨933785, by rfl⟩ : syracuseStep 1245047 = 1867571) B1867571
theorem B2801537 : Blo 1244440 2801537 := bstep (se 2 (by rfl) ⟨1050576, by rfl⟩ : syracuseStep 2801537 = 2101153) B2101153
theorem B1245067 : Blo 1244440 1245067 := bstep (se 1 (by rfl) ⟨933800, by rfl⟩ : syracuseStep 1245067 = 1867601) B1867601
theorem B1245079 : Blo 1244440 1245079 := bstep (se 1 (by rfl) ⟨933809, by rfl⟩ : syracuseStep 1245079 = 1867619) B1867619
theorem B1867673 : Blo 1244440 1867673 := bstep (se 2 (by rfl) ⟨700377, by rfl⟩ : syracuseStep 1867673 = 1400755) B1400755
theorem B1245099 : Blo 1244440 1245099 := bstep (se 1 (by rfl) ⟨933824, by rfl⟩ : syracuseStep 1245099 = 1867649) B1867649
theorem B1245111 : Blo 1244440 1245111 := bstep (se 1 (by rfl) ⟨933833, by rfl⟩ : syracuseStep 1245111 = 1867667) B1867667
theorem B1245131 : Blo 1244440 1245131 := bstep (se 1 (by rfl) ⟨933848, by rfl⟩ : syracuseStep 1245131 = 1867697) B1867697
theorem B1245143 : Blo 1244440 1245143 := bstep (se 1 (by rfl) ⟨933857, by rfl⟩ : syracuseStep 1245143 = 1867715) B1867715
theorem B4726745 : Blo 1244440 4726745 := bstep (se 2 (by rfl) ⟨1772529, by rfl⟩ : syracuseStep 4726745 = 3545059) B3545059
theorem B1400791 : Blo 1244440 1400791 := bstep (se 1 (by rfl) ⟨1050593, by rfl⟩ : syracuseStep 1400791 = 2101187) B2101187
theorem B1245163 : Blo 1244440 1245163 := bstep (se 1 (by rfl) ⟨933872, by rfl⟩ : syracuseStep 1245163 = 1867745) B1867745
theorem B1245175 : Blo 1244440 1245175 := bstep (se 1 (by rfl) ⟨933881, by rfl⟩ : syracuseStep 1245175 = 1867763) B1867763
theorem B1245191 : Blo 1244440 1245191 := bstep (se 1 (by rfl) ⟨933893, by rfl⟩ : syracuseStep 1245191 = 1867787) B1867787
theorem B1245199 : Blo 1244440 1245199 := bstep (se 1 (by rfl) ⟨933899, by rfl⟩ : syracuseStep 1245199 = 1867799) B1867799
theorem B8970263 : Blo 1244440 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B1867835 : Blo 1244440 1867835 := bstep (se 1 (by rfl) ⟨1400876, by rfl⟩ : syracuseStep 1867835 = 2801753) B2801753
theorem B1245243 : Blo 1244440 1245243 := bstep (se 1 (by rfl) ⟨933932, by rfl⟩ : syracuseStep 1245243 = 1867865) B1867865
theorem B3547223 : Blo 1244440 3547223 := bstep (se 1 (by rfl) ⟨2660417, by rfl⟩ : syracuseStep 3547223 = 5320835) B5320835
theorem B1867895 : Blo 1244440 1867895 := bstep (se 1 (by rfl) ⟨1400921, by rfl⟩ : syracuseStep 1867895 = 2801843) B2801843
theorem B1261703 : Blo 1244440 1261703 := bstep (se 1 (by rfl) ⟨946277, by rfl⟩ : syracuseStep 1261703 = 1892555) B1892555
theorem B1245319 : Blo 1244440 1245319 := bstep (se 1 (by rfl) ⟨933989, by rfl⟩ : syracuseStep 1245319 = 1867979) B1867979
theorem B2244743 : Blo 1244440 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B1867919 : Blo 1244440 1867919 := bstep (se 1 (by rfl) ⟨1400939, by rfl⟩ : syracuseStep 1867919 = 2801879) B2801879
theorem B1245327 : Blo 1244440 1245327 := bstep (se 1 (by rfl) ⟨933995, by rfl⟩ : syracuseStep 1245327 = 1867991) B1867991
theorem B9461933 : Blo 1244440 9461933 := bstep (se 3 (by rfl) ⟨1774112, by rfl⟩ : syracuseStep 9461933 = 3548225) B3548225
theorem B1867961 : Blo 1244440 1867961 := bstep (se 2 (by rfl) ⟨700485, by rfl⟩ : syracuseStep 1867961 = 1400971) B1400971
theorem B1245371 : Blo 1244440 1245371 := bstep (se 1 (by rfl) ⟨934028, by rfl⟩ : syracuseStep 1245371 = 1868057) B1868057
theorem B1868039 : Blo 1244440 1868039 := bstep (se 1 (by rfl) ⟨1401029, by rfl⟩ : syracuseStep 1868039 = 2802059) B2802059
theorem B1245447 : Blo 1244440 1245447 := bstep (se 1 (by rfl) ⟨934085, by rfl⟩ : syracuseStep 1245447 = 1868171) B1868171
theorem B1245455 : Blo 1244440 1245455 := bstep (se 1 (by rfl) ⟨934091, by rfl⟩ : syracuseStep 1245455 = 1868183) B1868183
theorem B1868075 : Blo 1244440 1868075 := bstep (se 1 (by rfl) ⟨1401056, by rfl⟩ : syracuseStep 1868075 = 2802113) B2802113
theorem B1245499 : Blo 1244440 1245499 := bstep (se 1 (by rfl) ⟨934124, by rfl⟩ : syracuseStep 1245499 = 1868249) B1868249
theorem B3547451 : Blo 1244440 3547451 := bstep (se 1 (by rfl) ⟨2660588, by rfl⟩ : syracuseStep 3547451 = 5321177) B5321177
theorem B1868105 : Blo 1244440 1868105 := bstep (se 2 (by rfl) ⟨700539, by rfl⟩ : syracuseStep 1868105 = 1401079) B1401079
theorem B15966557 : Blo 1244440 15966557 := bstep (se 3 (by rfl) ⟨2993729, by rfl⟩ : syracuseStep 15966557 = 5987459) B5987459
theorem B1401223 : Blo 1244440 1401223 := bstep (se 1 (by rfl) ⟨1050917, by rfl⟩ : syracuseStep 1401223 = 2101835) B2101835
theorem B1245575 : Blo 1244440 1245575 := bstep (se 1 (by rfl) ⟨934181, by rfl⟩ : syracuseStep 1245575 = 1868363) B1868363
theorem B1245583 : Blo 1244440 1245583 := bstep (se 1 (by rfl) ⟨934187, by rfl⟩ : syracuseStep 1245583 = 1868375) B1868375
theorem B3547577 : Blo 1244440 3547577 := bstep (se 2 (by rfl) ⟨1330341, by rfl⟩ : syracuseStep 3547577 = 2660683) B2660683
theorem B1868219 : Blo 1244440 1868219 := bstep (se 1 (by rfl) ⟨1401164, by rfl⟩ : syracuseStep 1868219 = 2802329) B2802329
theorem B1245627 : Blo 1244440 1245627 := bstep (se 1 (by rfl) ⟨934220, by rfl⟩ : syracuseStep 1245627 = 1868441) B1868441
theorem B1868279 : Blo 1244440 1868279 := bstep (se 1 (by rfl) ⟨1401209, by rfl⟩ : syracuseStep 1868279 = 2802419) B2802419
theorem B1245703 : Blo 1244440 1245703 := bstep (se 1 (by rfl) ⟨934277, by rfl⟩ : syracuseStep 1245703 = 1868555) B1868555
theorem B1868303 : Blo 1244440 1868303 := bstep (se 1 (by rfl) ⟨1401227, by rfl⟩ : syracuseStep 1868303 = 2802455) B2802455
theorem B1245711 : Blo 1244440 1245711 := bstep (se 1 (by rfl) ⟨934283, by rfl⟩ : syracuseStep 1245711 = 1868567) B1868567
theorem B1868345 : Blo 1244440 1868345 := bstep (se 2 (by rfl) ⟨700629, by rfl⟩ : syracuseStep 1868345 = 1401259) B1401259
theorem B3195451 : Blo 1244440 3195451 := bstep (se 1 (by rfl) ⟨2396588, by rfl⟩ : syracuseStep 3195451 = 4793177) B4793177
theorem B1401403 : Blo 1244440 1401403 := bstep (se 1 (by rfl) ⟨1051052, by rfl⟩ : syracuseStep 1401403 = 2102105) B2102105
theorem B1245755 : Blo 1244440 1245755 := bstep (se 1 (by rfl) ⟨934316, by rfl⟩ : syracuseStep 1245755 = 1868633) B1868633
theorem B9454157 : Blo 1244440 9454157 := bstep (se 3 (by rfl) ⟨1772654, by rfl⟩ : syracuseStep 9454157 = 3545309) B3545309
theorem B3596915 : Blo 1244440 3596915 := bstep (se 1 (by rfl) ⟨2697686, by rfl⟩ : syracuseStep 3596915 = 5395373) B5395373
theorem B2802311 : Blo 1244440 2802311 := bstep (se 1 (by rfl) ⟨2101733, by rfl⟩ : syracuseStep 2802311 = 4203467) B4203467
theorem B1868423 : Blo 1244440 1868423 := bstep (se 1 (by rfl) ⟨1401317, by rfl⟩ : syracuseStep 1868423 = 2802635) B2802635
theorem B1245831 : Blo 1244440 1245831 := bstep (se 1 (by rfl) ⟨934373, by rfl⟩ : syracuseStep 1245831 = 1868747) B1868747
theorem B1245839 : Blo 1244440 1245839 := bstep (se 1 (by rfl) ⟨934379, by rfl⟩ : syracuseStep 1245839 = 1868759) B1868759
theorem B3154585 : Blo 1244440 3154585 := bstep (se 2 (by rfl) ⟨1182969, by rfl⟩ : syracuseStep 3154585 = 2365939) B2365939
theorem B1868459 : Blo 1244440 1868459 := bstep (se 1 (by rfl) ⟨1401344, by rfl⟩ : syracuseStep 1868459 = 2802689) B2802689
theorem B1245883 : Blo 1244440 1245883 := bstep (se 1 (by rfl) ⟨934412, by rfl⟩ : syracuseStep 1245883 = 1868825) B1868825
theorem B1868489 : Blo 1244440 1868489 := bstep (se 2 (by rfl) ⟨700683, by rfl⟩ : syracuseStep 1868489 = 1401367) B1401367
theorem B1245959 : Blo 1244440 1245959 := bstep (se 1 (by rfl) ⟨934469, by rfl⟩ : syracuseStep 1245959 = 1868939) B1868939
theorem B1245967 : Blo 1244440 1245967 := bstep (se 1 (by rfl) ⟨934475, by rfl⟩ : syracuseStep 1245967 = 1868951) B1868951
theorem B2802491 : Blo 1244440 2802491 := bstep (se 1 (by rfl) ⟨2101868, by rfl⟩ : syracuseStep 2802491 = 4203737) B4203737
theorem B1868603 : Blo 1244440 1868603 := bstep (se 1 (by rfl) ⟨1401452, by rfl⟩ : syracuseStep 1868603 = 2802905) B2802905
theorem B1246011 : Blo 1244440 1246011 := bstep (se 1 (by rfl) ⟨934508, by rfl⟩ : syracuseStep 1246011 = 1869017) B1869017
theorem B3154747 : Blo 1244440 3154747 := bstep (se 1 (by rfl) ⟨2366060, by rfl⟩ : syracuseStep 3154747 = 4732121) B4732121
theorem B1868663 : Blo 1244440 1868663 := bstep (se 1 (by rfl) ⟨1401497, by rfl⟩ : syracuseStep 1868663 = 2802995) B2802995
theorem B1246087 : Blo 1244440 1246087 := bstep (se 1 (by rfl) ⟨934565, by rfl⟩ : syracuseStep 1246087 = 1869131) B1869131
theorem B1868687 : Blo 1244440 1868687 := bstep (se 1 (by rfl) ⟨1401515, by rfl⟩ : syracuseStep 1868687 = 2803031) B2803031
theorem B1246095 : Blo 1244440 1246095 := bstep (se 1 (by rfl) ⟨934571, by rfl⟩ : syracuseStep 1246095 = 1869143) B1869143
theorem B2802617 : Blo 1244440 2802617 := bstep (se 2 (by rfl) ⟨1050981, by rfl⟩ : syracuseStep 2802617 = 2101963) B2101963
theorem B1868729 : Blo 1244440 1868729 := bstep (se 2 (by rfl) ⟨700773, by rfl⟩ : syracuseStep 1868729 = 1401547) B1401547
theorem B1246139 : Blo 1244440 1246139 := bstep (se 1 (by rfl) ⟨934604, by rfl⟩ : syracuseStep 1246139 = 1869209) B1869209
theorem B3154889 : Blo 1244440 3154889 := bstep (se 2 (by rfl) ⟨1183083, by rfl⟩ : syracuseStep 3154889 = 2366167) B2366167
theorem B1868807 : Blo 1244440 1868807 := bstep (se 1 (by rfl) ⟨1401605, by rfl⟩ : syracuseStep 1868807 = 2803211) B2803211
theorem B1246215 : Blo 1244440 1246215 := bstep (se 1 (by rfl) ⟨934661, by rfl⟩ : syracuseStep 1246215 = 1869323) B1869323
theorem B1401871 : Blo 1244440 1401871 := bstep (se 1 (by rfl) ⟨1051403, by rfl⟩ : syracuseStep 1401871 = 2102807) B2102807
theorem B1246223 : Blo 1244440 1246223 := bstep (se 1 (by rfl) ⟨934667, by rfl⟩ : syracuseStep 1246223 = 1869335) B1869335
theorem B6824989 : Blo 1244440 6824989 := bstep (se 3 (by rfl) ⟨1279685, by rfl⟩ : syracuseStep 6824989 = 2559371) B2559371
theorem B1868843 : Blo 1244440 1868843 := bstep (se 1 (by rfl) ⟨1401632, by rfl⟩ : syracuseStep 1868843 = 2803265) B2803265
theorem B2991163 : Blo 1244440 2991163 := bstep (se 1 (by rfl) ⟨2243372, by rfl⟩ : syracuseStep 2991163 = 4486745) B4486745
theorem B1246267 : Blo 1244440 1246267 := bstep (se 1 (by rfl) ⟨934700, by rfl⟩ : syracuseStep 1246267 = 1869401) B1869401
theorem B1868873 : Blo 1244440 1868873 := bstep (se 2 (by rfl) ⟨700827, by rfl⟩ : syracuseStep 1868873 = 1401655) B1401655
theorem B1246343 : Blo 1244440 1246343 := bstep (se 1 (by rfl) ⟨934757, by rfl⟩ : syracuseStep 1246343 = 1869515) B1869515
theorem B1246351 : Blo 1244440 1246351 := bstep (se 1 (by rfl) ⟨934763, by rfl⟩ : syracuseStep 1246351 = 1869527) B1869527
theorem B1868987 : Blo 1244440 1868987 := bstep (se 1 (by rfl) ⟨1401740, by rfl⟩ : syracuseStep 1868987 = 2803481) B2803481
theorem B1246395 : Blo 1244440 1246395 := bstep (se 1 (by rfl) ⟨934796, by rfl⟩ : syracuseStep 1246395 = 1869593) B1869593
theorem B1869047 : Blo 1244440 1869047 := bstep (se 1 (by rfl) ⟨1401785, by rfl⟩ : syracuseStep 1869047 = 2803571) B2803571
theorem B4203791 : Blo 1244440 4203791 := bstep (se 1 (by rfl) ⟨3152843, by rfl⟩ : syracuseStep 4203791 = 6305687) B6305687
theorem B2802959 : Blo 1244440 2802959 := bstep (se 1 (by rfl) ⟨2102219, by rfl⟩ : syracuseStep 2802959 = 4204439) B4204439
theorem B1869071 : Blo 1244440 1869071 := bstep (se 1 (by rfl) ⟨1401803, by rfl⟩ : syracuseStep 1869071 = 2803607) B2803607
theorem B2802977 : Blo 1244440 2802977 := bstep (se 2 (by rfl) ⟨1051116, by rfl⟩ : syracuseStep 2802977 = 2102233) B2102233
theorem B1869113 : Blo 1244440 1869113 := bstep (se 2 (by rfl) ⟨700917, by rfl⟩ : syracuseStep 1869113 = 1401835) B1401835
theorem B1869191 : Blo 1244440 1869191 := bstep (se 1 (by rfl) ⟨1401893, by rfl⟩ : syracuseStep 1869191 = 2803787) B2803787
theorem B1869227 : Blo 1244440 1869227 := bstep (se 1 (by rfl) ⟨1401920, by rfl⟩ : syracuseStep 1869227 = 2803841) B2803841
theorem B1869257 : Blo 1244440 1869257 := bstep (se 2 (by rfl) ⟨700971, by rfl⟩ : syracuseStep 1869257 = 1401943) B1401943
theorem B4204061 : Blo 1244440 4204061 := bstep (se 3 (by rfl) ⟨788261, by rfl⟩ : syracuseStep 4204061 = 1576523) B1576523
theorem B1869371 : Blo 1244440 1869371 := bstep (se 1 (by rfl) ⟨1402028, by rfl⟩ : syracuseStep 1869371 = 2804057) B2804057
theorem B47908421 : Blo 1244440 47908421 := bstep (se 4 (by rfl) ⟨4491414, by rfl⟩ : syracuseStep 47908421 = 8982829) B8982829
theorem B14181965 : Blo 1244440 14181965 := bstep (se 3 (by rfl) ⟨2659118, by rfl⟩ : syracuseStep 14181965 = 5318237) B5318237
theorem B2803319 : Blo 1244440 2803319 := bstep (se 1 (by rfl) ⟨2102489, by rfl⟩ : syracuseStep 2803319 = 4204979) B4204979
theorem B1869431 : Blo 1244440 1869431 := bstep (se 1 (by rfl) ⟨1402073, by rfl⟩ : syracuseStep 1869431 = 2804147) B2804147
theorem B1869455 : Blo 1244440 1869455 := bstep (se 1 (by rfl) ⟨1402091, by rfl⟩ : syracuseStep 1869455 = 2804183) B2804183
theorem B1869497 : Blo 1244440 1869497 := bstep (se 2 (by rfl) ⟨701061, by rfl⟩ : syracuseStep 1869497 = 1402123) B1402123
theorem B3991241 : Blo 1244440 3991241 := bstep (se 2 (by rfl) ⟨1496715, by rfl⟩ : syracuseStep 3991241 = 2993431) B2993431
theorem B5760713 : Blo 1244440 5760713 := bstep (se 2 (by rfl) ⟨2160267, by rfl⟩ : syracuseStep 5760713 = 4320535) B4320535
theorem B1869575 : Blo 1244440 1869575 := bstep (se 1 (by rfl) ⟨1402181, by rfl⟩ : syracuseStep 1869575 = 2804363) B2804363
theorem B11970341 : Blo 1244440 11970341 := bstep (se 4 (by rfl) ⟨1122219, by rfl⟩ : syracuseStep 11970341 = 2244439) B2244439
theorem B6735653 : Blo 1244440 6735653 := bstep (se 4 (by rfl) ⟨631467, by rfl⟩ : syracuseStep 6735653 = 1262935) B1262935
theorem B2803499 : Blo 1244440 2803499 := bstep (se 1 (by rfl) ⟨2102624, by rfl⟩ : syracuseStep 2803499 = 4205249) B4205249
theorem B1869611 : Blo 1244440 1869611 := bstep (se 1 (by rfl) ⟨1402208, by rfl⟩ : syracuseStep 1869611 = 2804417) B2804417
theorem B17508145 : Blo 1244440 17508145 := bstep (se 2 (by rfl) ⟨6565554, by rfl⟩ : syracuseStep 17508145 = 13131109) B13131109
theorem B7087931 : Blo 1244440 7087931 := bstep (se 1 (by rfl) ⟨5315948, by rfl⟩ : syracuseStep 7087931 = 10631897) B10631897
theorem B1869641 : Blo 1244440 1869641 := bstep (se 2 (by rfl) ⟨701115, by rfl⟩ : syracuseStep 1869641 = 1402231) B1402231
theorem B51111755 : Blo 1244440 51111755 := bstep (se 1 (by rfl) ⟨38333816, by rfl⟩ : syracuseStep 51111755 = 76667633) B76667633
theorem B2991991 : Blo 1244440 2991991 := bstep (se 1 (by rfl) ⟨2243993, by rfl⟩ : syracuseStep 2991991 = 4487987) B4487987
theorem B2131847 : Blo 1244440 2131847 := bstep (se 1 (by rfl) ⟨1598885, by rfl⟩ : syracuseStep 2131847 = 3197771) B3197771
theorem B6309899 : Blo 1244440 6309899 := bstep (se 1 (by rfl) ⟨4732424, by rfl⟩ : syracuseStep 6309899 = 9464849) B9464849
theorem B3549217 : Blo 1244440 3549217 := bstep (se 2 (by rfl) ⟨1330956, by rfl⟩ : syracuseStep 3549217 = 2661913) B2661913
theorem B1575055 : Blo 1244440 1575055 := bstep (se 1 (by rfl) ⟨1181291, by rfl⟩ : syracuseStep 1575055 = 2362583) B2362583
theorem B2803859 : Blo 1244440 2803859 := bstep (se 1 (by rfl) ⟨2102894, by rfl⟩ : syracuseStep 2803859 = 4205789) B4205789
theorem B6310061 : Blo 1244440 6310061 := bstep (se 3 (by rfl) ⟨1183136, by rfl⟩ : syracuseStep 6310061 = 2366273) B2366273
theorem B2803913 : Blo 1244440 2803913 := bstep (se 2 (by rfl) ⟨1051467, by rfl⟩ : syracuseStep 2803913 = 2102935) B2102935
theorem B1575227 : Blo 1244440 1575227 := bstep (se 1 (by rfl) ⟨1181420, by rfl⟩ : syracuseStep 1575227 = 2362841) B2362841
theorem B5319179 : Blo 1244440 5319179 := bstep (se 1 (by rfl) ⟨3989384, by rfl⟩ : syracuseStep 5319179 = 7978769) B7978769
theorem B1329679 : Blo 1244440 1329679 := bstep (se 1 (by rfl) ⟨997259, by rfl⟩ : syracuseStep 1329679 = 1994519) B1994519
theorem B4729373 : Blo 1244440 4729373 := bstep (se 3 (by rfl) ⟨886757, by rfl⟩ : syracuseStep 4729373 = 1773515) B1773515
theorem B4729387 : Blo 1244440 4729387 := bstep (se 1 (by rfl) ⟨3547040, by rfl⟩ : syracuseStep 4729387 = 7094081) B7094081
theorem B9464363 : Blo 1244440 9464363 := bstep (se 1 (by rfl) ⟨7098272, by rfl⟩ : syracuseStep 9464363 = 14196545) B14196545
theorem B5319229 : Blo 1244440 5319229 := bstep (se 3 (by rfl) ⟨997355, by rfl⟩ : syracuseStep 5319229 = 1994711) B1994711
theorem B13470401 : Blo 1244440 13470401 := bstep (se 2 (by rfl) ⟨5051400, by rfl⟩ : syracuseStep 13470401 = 10102801) B10102801
theorem B2525897 : Blo 1244440 2525897 := bstep (se 2 (by rfl) ⟨947211, by rfl⟩ : syracuseStep 2525897 = 1894423) B1894423
theorem B6302609 : Blo 1244440 6302609 := bstep (se 2 (by rfl) ⟨2363478, by rfl⟩ : syracuseStep 6302609 = 4726957) B4726957
theorem B4205465 : Blo 1244440 4205465 := bstep (se 2 (by rfl) ⟨1577049, by rfl⟩ : syracuseStep 4205465 = 3154099) B3154099
theorem B1993673 : Blo 1244440 1993673 := bstep (se 2 (by rfl) ⟨747627, by rfl⟩ : syracuseStep 1993673 = 1495255) B1495255
theorem B9456587 : Blo 1244440 9456587 := bstep (se 1 (by rfl) ⟨7092440, by rfl⟩ : syracuseStep 9456587 = 14184881) B14184881
theorem B45419525 : Blo 1244440 45419525 := bstep (se 4 (by rfl) ⟨4258080, by rfl⟩ : syracuseStep 45419525 = 8516161) B8516161
theorem B5049373 : Blo 1244440 5049373 := bstep (se 3 (by rfl) ⟨946757, by rfl⟩ : syracuseStep 5049373 = 1893515) B1893515
theorem B2100343 : Blo 1244440 2100343 := bstep (se 1 (by rfl) ⟨1575257, by rfl⟩ : syracuseStep 2100343 = 3150515) B3150515
theorem B7089389 : Blo 1244440 7089389 := bstep (se 3 (by rfl) ⟨1329260, by rfl⟩ : syracuseStep 7089389 = 2658521) B2658521
theorem B1576199 : Blo 1244440 1576199 := bstep (se 1 (by rfl) ⟨1182149, by rfl⟩ : syracuseStep 1576199 = 2364299) B2364299
theorem B2526479 : Blo 1244440 2526479 := bstep (se 1 (by rfl) ⟨1894859, by rfl⟩ : syracuseStep 2526479 = 3789719) B3789719
theorem B3788075 : Blo 1244440 3788075 := bstep (se 1 (by rfl) ⟨2841056, by rfl⟩ : syracuseStep 3788075 = 5682113) B5682113
theorem B2100539 : Blo 1244440 2100539 := bstep (se 1 (by rfl) ⟨1575404, by rfl⟩ : syracuseStep 2100539 = 3150809) B3150809
theorem B5049715 : Blo 1244440 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B4263283 : Blo 1244440 4263283 := bstep (se 1 (by rfl) ⟨3197462, by rfl⟩ : syracuseStep 4263283 = 6394925) B6394925
theorem B2395663 : Blo 1244440 2395663 := bstep (se 1 (by rfl) ⟨1796747, by rfl⟩ : syracuseStep 2395663 = 3593495) B3593495
theorem B5983787 : Blo 1244440 5983787 := bstep (se 1 (by rfl) ⟨4487840, by rfl⟩ : syracuseStep 5983787 = 8975681) B8975681
theorem B7089707 : Blo 1244440 7089707 := bstep (se 1 (by rfl) ⟨5317280, by rfl⟩ : syracuseStep 7089707 = 10634561) B10634561
theorem B14192171 : Blo 1244440 14192171 := bstep (se 1 (by rfl) ⟨10644128, by rfl⟩ : syracuseStep 14192171 = 21288257) B21288257
theorem B4206167 : Blo 1244440 4206167 := bstep (se 1 (by rfl) ⟨3154625, by rfl⟩ : syracuseStep 4206167 = 6309251) B6309251
theorem B2100937 : Blo 1244440 2100937 := bstep (se 2 (by rfl) ⟨787851, by rfl⟩ : syracuseStep 2100937 = 1575703) B1575703
theorem B1994539 : Blo 1244440 1994539 := bstep (se 1 (by rfl) ⟨1495904, by rfl⟩ : syracuseStep 1994539 = 2991809) B2991809
theorem B1576847 : Blo 1244440 1576847 := bstep (se 1 (by rfl) ⟨1182635, by rfl⟩ : syracuseStep 1576847 = 2365271) B2365271
theorem B1994795 : Blo 1244440 1994795 := bstep (se 1 (by rfl) ⟨1496096, by rfl⟩ : syracuseStep 1994795 = 2992193) B2992193
theorem B4206653 : Blo 1244440 4206653 := bstep (se 3 (by rfl) ⟨788747, by rfl⟩ : syracuseStep 4206653 = 1577495) B1577495
theorem B7098455 : Blo 1244440 7098455 := bstep (se 1 (by rfl) ⟨5323841, by rfl⟩ : syracuseStep 7098455 = 10647683) B10647683
theorem B2363593 : Blo 1244440 2363593 := bstep (se 2 (by rfl) ⟨886347, by rfl⟩ : syracuseStep 2363593 = 1772695) B1772695
theorem B2101639 : Blo 1244440 2101639 := bstep (se 1 (by rfl) ⟨1576229, by rfl⟩ : syracuseStep 2101639 = 3152459) B3152459
theorem B1774153 : Blo 1244440 1774153 := bstep (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) B1330615
theorem B2839159 : Blo 1244440 2839159 := bstep (se 1 (by rfl) ⟨2129369, by rfl⟩ : syracuseStep 2839159 = 4258739) B4258739
theorem B2994835 : Blo 1244440 2994835 := bstep (se 1 (by rfl) ⟨2246126, by rfl⟩ : syracuseStep 2994835 = 4492253) B4492253
theorem B25572131 : Blo 1244440 25572131 := bstep (se 1 (by rfl) ⟨19179098, by rfl⟩ : syracuseStep 25572131 = 38358197) B38358197
theorem B3543851 : Blo 1244440 3543851 := bstep (se 1 (by rfl) ⟨2657888, by rfl⟩ : syracuseStep 3543851 = 5315777) B5315777
theorem B6304715 : Blo 1244440 6304715 := bstep (se 1 (by rfl) ⟨4728536, by rfl⟩ : syracuseStep 6304715 = 9457073) B9457073
theorem B7091165 : Blo 1244440 7091165 := bstep (se 3 (by rfl) ⟨1329593, by rfl⟩ : syracuseStep 7091165 = 2659187) B2659187
theorem B3150859 : Blo 1244440 3150859 := bstep (se 1 (by rfl) ⟨2363144, by rfl⟩ : syracuseStep 3150859 = 4726289) B4726289
theorem B2102287 : Blo 1244440 2102287 := bstep (se 1 (by rfl) ⟨1576715, by rfl⟩ : syracuseStep 2102287 = 3153431) B3153431
theorem B2842297 : Blo 1244440 2842297 := bstep (se 2 (by rfl) ⟨1065861, by rfl⟩ : syracuseStep 2842297 = 2131723) B2131723
theorem B3151001 : Blo 1244440 3151001 := bstep (se 2 (by rfl) ⟨1181625, by rfl⟩ : syracuseStep 3151001 = 2363251) B2363251
theorem B2659529 : Blo 1244440 2659529 := bstep (se 2 (by rfl) ⟨997323, by rfl⟩ : syracuseStep 2659529 = 1994647) B1994647
theorem B6067457 : Blo 1244440 6067457 := bstep (se 2 (by rfl) ⟨2275296, by rfl⟩ : syracuseStep 6067457 = 4550593) B4550593
theorem B6305039 : Blo 1244440 6305039 := bstep (se 1 (by rfl) ⟨4728779, by rfl⟩ : syracuseStep 6305039 = 9457559) B9457559
theorem B3151163 : Blo 1244440 3151163 := bstep (se 1 (by rfl) ⟨2363372, by rfl⟩ : syracuseStep 3151163 = 4726745) B4726745
theorem B2102827 : Blo 1244440 2102827 := bstep (se 1 (by rfl) ⟨1577120, by rfl⟩ : syracuseStep 2102827 = 3154241) B3154241
theorem B3364487 : Blo 1244440 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B3151507 : Blo 1244440 3151507 := bstep (se 1 (by rfl) ⟨2363630, by rfl⟩ : syracuseStep 3151507 = 4727261) B4727261
theorem B2102969 : Blo 1244440 2102969 := bstep (se 2 (by rfl) ⟨788613, by rfl⟩ : syracuseStep 2102969 = 1577227) B1577227
theorem B3544843 : Blo 1244440 3544843 := bstep (se 1 (by rfl) ⟨2658632, by rfl⟩ : syracuseStep 3544843 = 5317265) B5317265
theorem B4552463 : Blo 1244440 4552463 := bstep (se 1 (by rfl) ⟨3414347, by rfl⟩ : syracuseStep 4552463 = 6828695) B6828695
theorem B3151649 : Blo 1244440 3151649 := bstep (se 2 (by rfl) ⟨1181868, by rfl⟩ : syracuseStep 3151649 = 2363737) B2363737
theorem B8083289 : Blo 1244440 8083289 := bstep (se 2 (by rfl) ⟨3031233, by rfl⟩ : syracuseStep 8083289 = 6062467) B6062467
theorem B5322611 : Blo 1244440 5322611 := bstep (se 1 (by rfl) ⟨3991958, by rfl⟩ : syracuseStep 5322611 = 7983917) B7983917
theorem B31561589 : Blo 1244440 31561589 := bstep (se 5 (by rfl) ⟨1479449, by rfl⟩ : syracuseStep 31561589 = 2958899) B2958899
theorem B17946521 : Blo 1244440 17946521 := bstep (se 2 (by rfl) ⟨6729945, by rfl⟩ : syracuseStep 17946521 = 13459891) B13459891
theorem B6731741 : Blo 1244440 6731741 := bstep (se 3 (by rfl) ⟨1262201, by rfl⟩ : syracuseStep 6731741 = 2524403) B2524403
theorem B3545117 : Blo 1244440 3545117 := bstep (se 3 (by rfl) ⟨664709, by rfl⟩ : syracuseStep 3545117 = 1329419) B1329419
theorem B2365499 : Blo 1244440 2365499 := bstep (se 1 (by rfl) ⟨1774124, by rfl⟩ : syracuseStep 2365499 = 3548249) B3548249
theorem B3192979 : Blo 1244440 3192979 := bstep (se 1 (by rfl) ⟨2394734, by rfl⟩ : syracuseStep 3192979 = 4789469) B4789469
theorem B6822181 : Blo 1244440 6822181 := bstep (se 4 (by rfl) ⟨639579, by rfl⟩ : syracuseStep 6822181 = 1279159) B1279159
theorem B2800007 : Blo 1244440 2800007 := bstep (se 1 (by rfl) ⟨2100005, by rfl⟩ : syracuseStep 2800007 = 4200011) B4200011
theorem B3193235 : Blo 1244440 3193235 := bstep (se 1 (by rfl) ⟨2394926, by rfl⟩ : syracuseStep 3193235 = 4789853) B4789853
theorem B12139037 : Blo 1244440 12139037 := bstep (se 3 (by rfl) ⟨2276069, by rfl⟩ : syracuseStep 12139037 = 4552139) B4552139
theorem B2365985 : Blo 1244440 2365985 := bstep (se 2 (by rfl) ⟨887244, by rfl⟩ : syracuseStep 2365985 = 1774489) B1774489
theorem B2800187 : Blo 1244440 2800187 := bstep (se 1 (by rfl) ⟨2100140, by rfl⟩ : syracuseStep 2800187 = 4200281) B4200281
theorem B13457987 : Blo 1244440 13457987 := bstep (se 1 (by rfl) ⟨10093490, by rfl⟩ : syracuseStep 13457987 = 20186981) B20186981
theorem B2800313 : Blo 1244440 2800313 := bstep (se 2 (by rfl) ⟨1050117, by rfl⟩ : syracuseStep 2800313 = 2100235) B2100235
theorem B21568193 : Blo 1244440 21568193 := bstep (se 2 (by rfl) ⟨8088072, by rfl⟩ : syracuseStep 21568193 = 16176145) B16176145
theorem B6306497 : Blo 1244440 6306497 := bstep (se 2 (by rfl) ⟨2364936, by rfl⟩ : syracuseStep 6306497 = 4729873) B4729873
theorem B4725485 : Blo 1244440 4725485 := bstep (se 3 (by rfl) ⟨886028, by rfl⟩ : syracuseStep 4725485 = 1772057) B1772057
theorem B3693313 : Blo 1244440 3693313 := bstep (se 2 (by rfl) ⟨1384992, by rfl⟩ : syracuseStep 3693313 = 2769985) B2769985
theorem B3152641 : Blo 1244440 3152641 := bstep (se 2 (by rfl) ⟨1182240, by rfl⟩ : syracuseStep 3152641 = 2364481) B2364481
theorem B5323553 : Blo 1244440 5323553 := bstep (se 2 (by rfl) ⟨1996332, by rfl⟩ : syracuseStep 5323553 = 3992665) B3992665
theorem B6478643 : Blo 1244440 6478643 := bstep (se 1 (by rfl) ⟨4858982, by rfl⟩ : syracuseStep 6478643 = 9717965) B9717965
theorem B13130585 : Blo 1244440 13130585 := bstep (se 2 (by rfl) ⟨4923969, by rfl⟩ : syracuseStep 13130585 = 9847939) B9847939
theorem B1866683 : Blo 1244440 1866683 := bstep (se 1 (by rfl) ⟨1400012, by rfl⟩ : syracuseStep 1866683 = 2800025) B2800025
theorem B1866743 : Blo 1244440 1866743 := bstep (se 1 (by rfl) ⟨1400057, by rfl⟩ : syracuseStep 1866743 = 2800115) B2800115
theorem B1866767 : Blo 1244440 1866767 := bstep (se 1 (by rfl) ⟨1400075, by rfl⟩ : syracuseStep 1866767 = 2800151) B2800151
theorem B2800655 : Blo 1244440 2800655 := bstep (se 1 (by rfl) ⟨2100491, by rfl⟩ : syracuseStep 2800655 = 4200983) B4200983
theorem B2800673 : Blo 1244440 2800673 := bstep (se 2 (by rfl) ⟨1050252, by rfl⟩ : syracuseStep 2800673 = 2100505) B2100505
theorem B3193889 : Blo 1244440 3193889 := bstep (se 2 (by rfl) ⟨1197708, by rfl⟩ : syracuseStep 3193889 = 2395417) B2395417
theorem B4725803 : Blo 1244440 4725803 := bstep (se 1 (by rfl) ⟨3544352, by rfl⟩ : syracuseStep 4725803 = 7088705) B7088705
theorem B1866809 : Blo 1244440 1866809 := bstep (se 2 (by rfl) ⟨700053, by rfl⟩ : syracuseStep 1866809 = 1400107) B1400107
theorem B1866887 : Blo 1244440 1866887 := bstep (se 1 (by rfl) ⟨1400165, by rfl⟩ : syracuseStep 1866887 = 2800331) B2800331
theorem B2661511 : Blo 1244440 2661511 := bstep (se 1 (by rfl) ⟨1996133, by rfl⟩ : syracuseStep 2661511 = 3992267) B3992267
theorem B1866923 : Blo 1244440 1866923 := bstep (se 1 (by rfl) ⟨1400192, by rfl⟩ : syracuseStep 1866923 = 2800385) B2800385
theorem B1866953 : Blo 1244440 1866953 := bstep (se 2 (by rfl) ⟨700107, by rfl⟩ : syracuseStep 1866953 = 1400215) B1400215
theorem B1400071 : Blo 1244440 1400071 := bstep (se 1 (by rfl) ⟨1050053, by rfl⟩ : syracuseStep 1400071 = 2100107) B2100107
theorem B1244475 : Blo 1244440 1244475 := bstep (se 1 (by rfl) ⟨933356, by rfl⟩ : syracuseStep 1244475 = 1866713) B1866713
theorem B1867067 : Blo 1244440 1867067 := bstep (se 1 (by rfl) ⟨1400300, by rfl⟩ : syracuseStep 1867067 = 2800601) B2800601
theorem B3153239 : Blo 1244440 3153239 := bstep (se 1 (by rfl) ⟨2364929, by rfl⟩ : syracuseStep 3153239 = 4729859) B4729859
theorem B1867127 : Blo 1244440 1867127 := bstep (se 1 (by rfl) ⟨1400345, by rfl⟩ : syracuseStep 1867127 = 2800691) B2800691
theorem B2801015 : Blo 1244440 2801015 := bstep (se 1 (by rfl) ⟨2100761, by rfl⟩ : syracuseStep 2801015 = 4201523) B4201523
theorem B1244551 : Blo 1244440 1244551 := bstep (se 1 (by rfl) ⟨933413, by rfl⟩ : syracuseStep 1244551 = 1866827) B1866827
theorem B1244559 : Blo 1244440 1244559 := bstep (se 1 (by rfl) ⟨933419, by rfl⟩ : syracuseStep 1244559 = 1866839) B1866839
theorem B1867151 : Blo 1244440 1867151 := bstep (se 1 (by rfl) ⟨1400363, by rfl⟩ : syracuseStep 1867151 = 2800727) B2800727
theorem B3988883 : Blo 1244440 3988883 := bstep (se 1 (by rfl) ⟨2991662, by rfl⟩ : syracuseStep 3988883 = 5983325) B5983325
theorem B1867193 : Blo 1244440 1867193 := bstep (se 2 (by rfl) ⟨700197, by rfl⟩ : syracuseStep 1867193 = 1400395) B1400395
theorem B1244603 : Blo 1244440 1244603 := bstep (se 1 (by rfl) ⟨933452, by rfl⟩ : syracuseStep 1244603 = 1866905) B1866905
theorem B1400251 : Blo 1244440 1400251 := bstep (se 1 (by rfl) ⟨1050188, by rfl⟩ : syracuseStep 1400251 = 2100377) B2100377
theorem B7093763 : Blo 1244440 7093763 := bstep (se 1 (by rfl) ⟨5320322, by rfl⟩ : syracuseStep 7093763 = 10640645) B10640645
theorem B1244679 : Blo 1244440 1244679 := bstep (se 1 (by rfl) ⟨933509, by rfl⟩ : syracuseStep 1244679 = 1867019) B1867019
theorem B1867271 : Blo 1244440 1867271 := bstep (se 1 (by rfl) ⟨1400453, by rfl⟩ : syracuseStep 1867271 = 2800907) B2800907
theorem B1244687 : Blo 1244440 1244687 := bstep (se 1 (by rfl) ⟨933515, by rfl⟩ : syracuseStep 1244687 = 1867031) B1867031
theorem B1867307 : Blo 1244440 1867307 := bstep (se 1 (by rfl) ⟨1400480, by rfl⟩ : syracuseStep 1867307 = 2800961) B2800961
theorem B2801195 : Blo 1244440 2801195 := bstep (se 1 (by rfl) ⟨2100896, by rfl⟩ : syracuseStep 2801195 = 4201793) B4201793
theorem B3366443 : Blo 1244440 3366443 := bstep (se 1 (by rfl) ⟨2524832, by rfl⟩ : syracuseStep 3366443 = 5049665) B5049665
theorem B3153451 : Blo 1244440 3153451 := bstep (se 1 (by rfl) ⟨2365088, by rfl⟩ : syracuseStep 3153451 = 4730177) B4730177
theorem B1244731 : Blo 1244440 1244731 := bstep (se 1 (by rfl) ⟨933548, by rfl⟩ : syracuseStep 1244731 = 1867097) B1867097
theorem B1867337 : Blo 1244440 1867337 := bstep (se 2 (by rfl) ⟨700251, by rfl⟩ : syracuseStep 1867337 = 1400503) B1400503
theorem B1244807 : Blo 1244440 1244807 := bstep (se 1 (by rfl) ⟨933605, by rfl⟩ : syracuseStep 1244807 = 1867211) B1867211
theorem B1244815 : Blo 1244440 1244815 := bstep (se 1 (by rfl) ⟨933611, by rfl⟩ : syracuseStep 1244815 = 1867223) B1867223
theorem B3153593 : Blo 1244440 3153593 := bstep (se 2 (by rfl) ⟨1182597, by rfl⟩ : syracuseStep 3153593 = 2365195) B2365195
theorem B1244859 : Blo 1244440 1244859 := bstep (se 1 (by rfl) ⟨933644, by rfl⟩ : syracuseStep 1244859 = 1867289) B1867289
theorem B1867451 : Blo 1244440 1867451 := bstep (se 1 (by rfl) ⟨1400588, by rfl⟩ : syracuseStep 1867451 = 2801177) B2801177
theorem B7577317 : Blo 1244440 7577317 := bstep (se 4 (by rfl) ⟨710373, by rfl⟩ : syracuseStep 7577317 = 1420747) B1420747
theorem B1867511 : Blo 1244440 1867511 := bstep (se 1 (by rfl) ⟨1400633, by rfl⟩ : syracuseStep 1867511 = 2801267) B2801267
theorem B1244935 : Blo 1244440 1244935 := bstep (se 1 (by rfl) ⟨933701, by rfl⟩ : syracuseStep 1244935 = 1867403) B1867403
theorem B1244943 : Blo 1244440 1244943 := bstep (se 1 (by rfl) ⟨933707, by rfl⟩ : syracuseStep 1244943 = 1867415) B1867415
theorem B1867535 : Blo 1244440 1867535 := bstep (se 1 (by rfl) ⟨1400651, by rfl⟩ : syracuseStep 1867535 = 2801303) B2801303
theorem B1867577 : Blo 1244440 1867577 := bstep (se 2 (by rfl) ⟨700341, by rfl⟩ : syracuseStep 1867577 = 1400683) B1400683
theorem B1244987 : Blo 1244440 1244987 := bstep (se 1 (by rfl) ⟨933740, by rfl⟩ : syracuseStep 1244987 = 1867481) B1867481
theorem B1245063 : Blo 1244440 1245063 := bstep (se 1 (by rfl) ⟨933797, by rfl⟩ : syracuseStep 1245063 = 1867595) B1867595
theorem B1867655 : Blo 1244440 1867655 := bstep (se 1 (by rfl) ⟨1400741, by rfl⟩ : syracuseStep 1867655 = 2801483) B2801483
theorem B1245071 : Blo 1244440 1245071 := bstep (se 1 (by rfl) ⟨933803, by rfl⟩ : syracuseStep 1245071 = 1867607) B1867607
theorem B1400719 : Blo 1244440 1400719 := bstep (se 1 (by rfl) ⟨1050539, by rfl⟩ : syracuseStep 1400719 = 2101079) B2101079
theorem B4202387 : Blo 1244440 4202387 := bstep (se 1 (by rfl) ⟨3151790, by rfl⟩ : syracuseStep 4202387 = 6303581) B6303581
theorem B2801555 : Blo 1244440 2801555 := bstep (se 1 (by rfl) ⟨2101166, by rfl⟩ : syracuseStep 2801555 = 4202333) B4202333
theorem B10092451 : Blo 1244440 10092451 := bstep (se 1 (by rfl) ⟨7569338, by rfl⟩ : syracuseStep 10092451 = 15138677) B15138677
theorem B1867691 : Blo 1244440 1867691 := bstep (se 1 (by rfl) ⟨1400768, by rfl⟩ : syracuseStep 1867691 = 2801537) B2801537
theorem B1245115 : Blo 1244440 1245115 := bstep (se 1 (by rfl) ⟨933836, by rfl⟩ : syracuseStep 1245115 = 1867673) B1867673
theorem B1867721 : Blo 1244440 1867721 := bstep (se 2 (by rfl) ⟨700395, by rfl⟩ : syracuseStep 1867721 = 1400791) B1400791
theorem B2801609 : Blo 1244440 2801609 := bstep (se 2 (by rfl) ⟨1050603, by rfl⟩ : syracuseStep 2801609 = 2101207) B2101207
theorem B6307793 : Blo 1244440 6307793 := bstep (se 2 (by rfl) ⟨2365422, by rfl⟩ : syracuseStep 6307793 = 4730845) B4730845
theorem B5980175 : Blo 1244440 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B1245223 : Blo 1244440 1245223 := bstep (se 1 (by rfl) ⟨933917, by rfl⟩ : syracuseStep 1245223 = 1867835) B1867835
theorem B1245263 : Blo 1244440 1245263 := bstep (se 1 (by rfl) ⟨933947, by rfl⟩ : syracuseStep 1245263 = 1867895) B1867895
theorem B1245279 : Blo 1244440 1245279 := bstep (se 1 (by rfl) ⟨933959, by rfl⟩ : syracuseStep 1245279 = 1867919) B1867919
theorem B6307955 : Blo 1244440 6307955 := bstep (se 1 (by rfl) ⟨4730966, by rfl⟩ : syracuseStep 6307955 = 9461933) B9461933
theorem B1245307 : Blo 1244440 1245307 := bstep (se 1 (by rfl) ⟨933980, by rfl⟩ : syracuseStep 1245307 = 1867961) B1867961
theorem B1245359 : Blo 1244440 1245359 := bstep (se 1 (by rfl) ⟨934019, by rfl⟩ : syracuseStep 1245359 = 1868039) B1868039
theorem B1245383 : Blo 1244440 1245383 := bstep (se 1 (by rfl) ⟨934037, by rfl⟩ : syracuseStep 1245383 = 1868075) B1868075
theorem B1245403 : Blo 1244440 1245403 := bstep (se 1 (by rfl) ⟨934052, by rfl⟩ : syracuseStep 1245403 = 1868105) B1868105
theorem B1245479 : Blo 1244440 1245479 := bstep (se 1 (by rfl) ⟨934109, by rfl⟩ : syracuseStep 1245479 = 1868219) B1868219
theorem B1245519 : Blo 1244440 1245519 := bstep (se 1 (by rfl) ⟨934139, by rfl⟩ : syracuseStep 1245519 = 1868279) B1868279
theorem B1245535 : Blo 1244440 1245535 := bstep (se 1 (by rfl) ⟨934151, by rfl⟩ : syracuseStep 1245535 = 1868303) B1868303
theorem B1245563 : Blo 1244440 1245563 := bstep (se 1 (by rfl) ⟨934172, by rfl⟩ : syracuseStep 1245563 = 1868345) B1868345
theorem B1868207 : Blo 1244440 1868207 := bstep (se 1 (by rfl) ⟨1401155, by rfl⟩ : syracuseStep 1868207 = 2802311) B2802311
theorem B1245615 : Blo 1244440 1245615 := bstep (se 1 (by rfl) ⟨934211, by rfl⟩ : syracuseStep 1245615 = 1868423) B1868423
theorem B1245639 : Blo 1244440 1245639 := bstep (se 1 (by rfl) ⟨934229, by rfl⟩ : syracuseStep 1245639 = 1868459) B1868459
theorem B1245659 : Blo 1244440 1245659 := bstep (se 1 (by rfl) ⟨934244, by rfl⟩ : syracuseStep 1245659 = 1868489) B1868489
theorem B2802185 : Blo 1244440 2802185 := bstep (se 2 (by rfl) ⟨1050819, by rfl⟩ : syracuseStep 2802185 = 2101639) B2101639
theorem B1868297 : Blo 1244440 1868297 := bstep (se 2 (by rfl) ⟨700611, by rfl⟩ : syracuseStep 1868297 = 1401223) B1401223
theorem B17048087 : Blo 1244440 17048087 := bstep (se 1 (by rfl) ⟨12786065, by rfl⟩ : syracuseStep 17048087 = 25572131) B25572131
theorem B1868327 : Blo 1244440 1868327 := bstep (se 1 (by rfl) ⟨1401245, by rfl⟩ : syracuseStep 1868327 = 2802491) B2802491
theorem B1245735 : Blo 1244440 1245735 := bstep (se 1 (by rfl) ⟨934301, by rfl⟩ : syracuseStep 1245735 = 1868603) B1868603
theorem B1245775 : Blo 1244440 1245775 := bstep (se 1 (by rfl) ⟨934331, by rfl⟩ : syracuseStep 1245775 = 1868663) B1868663
theorem B1245791 : Blo 1244440 1245791 := bstep (se 1 (by rfl) ⟨934343, by rfl⟩ : syracuseStep 1245791 = 1868687) B1868687
theorem B1868411 : Blo 1244440 1868411 := bstep (se 1 (by rfl) ⟨1401308, by rfl⟩ : syracuseStep 1868411 = 2802617) B2802617
theorem B1245819 : Blo 1244440 1245819 := bstep (se 1 (by rfl) ⟨934364, by rfl⟩ : syracuseStep 1245819 = 1868729) B1868729
theorem B4203143 : Blo 1244440 4203143 := bstep (se 1 (by rfl) ⟨3152357, by rfl⟩ : syracuseStep 4203143 = 6304715) B6304715
theorem B4727443 : Blo 1244440 4727443 := bstep (se 1 (by rfl) ⟨3545582, by rfl⟩ : syracuseStep 4727443 = 7091165) B7091165
theorem B1245871 : Blo 1244440 1245871 := bstep (se 1 (by rfl) ⟨934403, by rfl⟩ : syracuseStep 1245871 = 1868807) B1868807
theorem B4203197 : Blo 1244440 4203197 := bstep (se 3 (by rfl) ⟨788099, by rfl⟩ : syracuseStep 4203197 = 1576199) B1576199
theorem B1245895 : Blo 1244440 1245895 := bstep (se 1 (by rfl) ⟨934421, by rfl⟩ : syracuseStep 1245895 = 1868843) B1868843
theorem B1245915 : Blo 1244440 1245915 := bstep (se 1 (by rfl) ⟨934436, by rfl⟩ : syracuseStep 1245915 = 1868873) B1868873
theorem B4260601 : Blo 1244440 4260601 := bstep (se 2 (by rfl) ⟨1597725, by rfl⟩ : syracuseStep 4260601 = 3195451) B3195451
theorem B1868537 : Blo 1244440 1868537 := bstep (se 2 (by rfl) ⟨700701, by rfl⟩ : syracuseStep 1868537 = 1401403) B1401403
theorem B1245991 : Blo 1244440 1245991 := bstep (se 1 (by rfl) ⟨934493, by rfl⟩ : syracuseStep 1245991 = 1868987) B1868987
theorem B3785545 : Blo 1244440 3785545 := bstep (se 2 (by rfl) ⟨1419579, by rfl⟩ : syracuseStep 3785545 = 2839159) B2839159
theorem B1246031 : Blo 1244440 1246031 := bstep (se 1 (by rfl) ⟨934523, by rfl⟩ : syracuseStep 1246031 = 1869047) B1869047
theorem B4203359 : Blo 1244440 4203359 := bstep (se 1 (by rfl) ⟨3152519, by rfl⟩ : syracuseStep 4203359 = 6305039) B6305039
theorem B2802527 : Blo 1244440 2802527 := bstep (se 1 (by rfl) ⟨2101895, by rfl⟩ : syracuseStep 2802527 = 4203791) B4203791
theorem B1868639 : Blo 1244440 1868639 := bstep (se 1 (by rfl) ⟨1401479, by rfl⟩ : syracuseStep 1868639 = 2802959) B2802959
theorem B1246047 : Blo 1244440 1246047 := bstep (se 1 (by rfl) ⟨934535, by rfl⟩ : syracuseStep 1246047 = 1869071) B1869071
theorem B1868651 : Blo 1244440 1868651 := bstep (se 1 (by rfl) ⟨1401488, by rfl⟩ : syracuseStep 1868651 = 2802977) B2802977
theorem B1246075 : Blo 1244440 1246075 := bstep (se 1 (by rfl) ⟨934556, by rfl⟩ : syracuseStep 1246075 = 1869113) B1869113
theorem B1246127 : Blo 1244440 1246127 := bstep (se 1 (by rfl) ⟨934595, by rfl⟩ : syracuseStep 1246127 = 1869191) B1869191
theorem B1246151 : Blo 1244440 1246151 := bstep (se 1 (by rfl) ⟨934613, by rfl⟩ : syracuseStep 1246151 = 1869227) B1869227
theorem B1246171 : Blo 1244440 1246171 := bstep (se 1 (by rfl) ⟨934628, by rfl⟩ : syracuseStep 1246171 = 1869257) B1869257
theorem B4203521 : Blo 1244440 4203521 := bstep (se 2 (by rfl) ⟨1576320, by rfl⟩ : syracuseStep 4203521 = 3152641) B3152641
theorem B2802707 : Blo 1244440 2802707 := bstep (se 1 (by rfl) ⟨2102030, by rfl⟩ : syracuseStep 2802707 = 4204061) B4204061
theorem B1246247 : Blo 1244440 1246247 := bstep (se 1 (by rfl) ⟨934685, by rfl⟩ : syracuseStep 1246247 = 1869371) B1869371
theorem B9454643 : Blo 1244440 9454643 := bstep (se 1 (by rfl) ⟨7090982, by rfl⟩ : syracuseStep 9454643 = 14181965) B14181965
theorem B1868879 : Blo 1244440 1868879 := bstep (se 1 (by rfl) ⟨1401659, by rfl⟩ : syracuseStep 1868879 = 2803319) B2803319
theorem B1246287 : Blo 1244440 1246287 := bstep (se 1 (by rfl) ⟨934715, by rfl⟩ : syracuseStep 1246287 = 1869431) B1869431
theorem B1246303 : Blo 1244440 1246303 := bstep (se 1 (by rfl) ⟨934727, by rfl⟩ : syracuseStep 1246303 = 1869455) B1869455
theorem B1401979 : Blo 1244440 1401979 := bstep (se 1 (by rfl) ⟨1051484, by rfl⟩ : syracuseStep 1401979 = 2102969) B2102969
theorem B1246331 : Blo 1244440 1246331 := bstep (se 1 (by rfl) ⟨934748, by rfl⟩ : syracuseStep 1246331 = 1869497) B1869497
theorem B1246383 : Blo 1244440 1246383 := bstep (se 1 (by rfl) ⟨934787, by rfl⟩ : syracuseStep 1246383 = 1869575) B1869575
theorem B7980227 : Blo 1244440 7980227 := bstep (se 1 (by rfl) ⟨5985170, by rfl⟩ : syracuseStep 7980227 = 11970341) B11970341
theorem B4490435 : Blo 1244440 4490435 := bstep (se 1 (by rfl) ⟨3367826, by rfl⟩ : syracuseStep 4490435 = 6735653) B6735653
theorem B40412357 : Blo 1244440 40412357 := bstep (se 4 (by rfl) ⟨3788658, by rfl⟩ : syracuseStep 40412357 = 7577317) B7577317
theorem B1868999 : Blo 1244440 1868999 := bstep (se 1 (by rfl) ⟨1401749, by rfl⟩ : syracuseStep 1868999 = 2803499) B2803499
theorem B1246407 : Blo 1244440 1246407 := bstep (se 1 (by rfl) ⟨934805, by rfl⟩ : syracuseStep 1246407 = 1869611) B1869611
theorem B1246427 : Blo 1244440 1246427 := bstep (se 1 (by rfl) ⟨934820, by rfl⟩ : syracuseStep 1246427 = 1869641) B1869641
theorem B2803049 : Blo 1244440 2803049 := bstep (se 2 (by rfl) ⟨1051143, by rfl⟩ : syracuseStep 2803049 = 2102287) B2102287
theorem B1869161 : Blo 1244440 1869161 := bstep (se 2 (by rfl) ⟨700935, by rfl⟩ : syracuseStep 1869161 = 1401871) B1401871
theorem B1869239 : Blo 1244440 1869239 := bstep (se 1 (by rfl) ⟨1401929, by rfl⟩ : syracuseStep 1869239 = 2803859) B2803859
theorem B1869275 : Blo 1244440 1869275 := bstep (se 1 (by rfl) ⟨1401956, by rfl⟩ : syracuseStep 1869275 = 2803913) B2803913
theorem B3548681 : Blo 1244440 3548681 := bstep (se 2 (by rfl) ⟨1330755, by rfl⟩ : syracuseStep 3548681 = 2661511) B2661511
theorem B6309575 : Blo 1244440 6309575 := bstep (se 1 (by rfl) ⟨4732181, by rfl⟩ : syracuseStep 6309575 = 9464363) B9464363
theorem B8971991 : Blo 1244440 8971991 := bstep (se 1 (by rfl) ⟨6728993, by rfl⟩ : syracuseStep 8971991 = 13457987) B13457987
theorem B14378795 : Blo 1244440 14378795 := bstep (se 1 (by rfl) ⟨10784096, by rfl⟩ : syracuseStep 14378795 = 21568193) B21568193
theorem B4204331 : Blo 1244440 4204331 := bstep (se 1 (by rfl) ⟨3153248, by rfl⟩ : syracuseStep 4204331 = 6306497) B6306497
theorem B8980267 : Blo 1244440 8980267 := bstep (se 1 (by rfl) ⟨6735200, by rfl⟩ : syracuseStep 8980267 = 13470401) B13470401
theorem B3549035 : Blo 1244440 3549035 := bstep (se 1 (by rfl) ⟨2661776, by rfl⟩ : syracuseStep 3549035 = 5323553) B5323553
theorem B10643309 : Blo 1244440 10643309 := bstep (se 3 (by rfl) ⟨1995620, by rfl⟩ : syracuseStep 10643309 = 3991241) B3991241
theorem B4319095 : Blo 1244440 4319095 := bstep (se 1 (by rfl) ⟨3239321, by rfl⟩ : syracuseStep 4319095 = 6478643) B6478643
theorem B2803643 : Blo 1244440 2803643 := bstep (se 1 (by rfl) ⟨2102732, by rfl⟩ : syracuseStep 2803643 = 4205465) B4205465
theorem B30279683 : Blo 1244440 30279683 := bstep (se 1 (by rfl) ⟨22709762, by rfl⟩ : syracuseStep 30279683 = 45419525) B45419525
theorem B4204601 : Blo 1244440 4204601 := bstep (se 2 (by rfl) ⟨1576725, by rfl⟩ : syracuseStep 4204601 = 3153451) B3153451
theorem B2803769 : Blo 1244440 2803769 := bstep (se 2 (by rfl) ⟨1051413, by rfl⟩ : syracuseStep 2803769 = 2102827) B2102827
theorem B2525383 : Blo 1244440 2525383 := bstep (se 1 (by rfl) ⟨1894037, by rfl⟩ : syracuseStep 2525383 = 3788075) B3788075
theorem B4729175 : Blo 1244440 4729175 := bstep (se 1 (by rfl) ⟨3546881, by rfl⟩ : syracuseStep 4729175 = 7093763) B7093763
theorem B4204925 : Blo 1244440 4204925 := bstep (se 3 (by rfl) ⟨788423, by rfl⟩ : syracuseStep 4204925 = 1576847) B1576847
theorem B2804111 : Blo 1244440 2804111 := bstep (se 1 (by rfl) ⟨2103083, by rfl⟩ : syracuseStep 2804111 = 4206167) B4206167
theorem B4205195 : Blo 1244440 4205195 := bstep (se 1 (by rfl) ⟨3153896, by rfl⟩ : syracuseStep 4205195 = 6307793) B6307793
theorem B1329863 : Blo 1244440 1329863 := bstep (se 1 (by rfl) ⟨997397, by rfl⟩ : syracuseStep 1329863 = 1994795) B1994795
theorem B2804435 : Blo 1244440 2804435 := bstep (se 1 (by rfl) ⟨2103326, by rfl⟩ : syracuseStep 2804435 = 4206653) B4206653
theorem B2100073 : Blo 1244440 2100073 := bstep (se 2 (by rfl) ⟨787527, by rfl⟩ : syracuseStep 2100073 = 1575055) B1575055
theorem B10644371 : Blo 1244440 10644371 := bstep (se 1 (by rfl) ⟨7983278, by rfl⟩ : syracuseStep 10644371 = 15966557) B15966557
theorem B9096241 : Blo 1244440 9096241 := bstep (se 2 (by rfl) ⟨3411090, by rfl⟩ : syracuseStep 9096241 = 6822181) B6822181
theorem B6302771 : Blo 1244440 6302771 := bstep (se 1 (by rfl) ⟨4727078, by rfl⟩ : syracuseStep 6302771 = 9454157) B9454157
theorem B2100667 : Blo 1244440 2100667 := bstep (se 1 (by rfl) ⟨1575500, by rfl⟩ : syracuseStep 2100667 = 3151001) B3151001
theorem B1773019 : Blo 1244440 1773019 := bstep (se 1 (by rfl) ⟨1329764, by rfl⟩ : syracuseStep 1773019 = 2659529) B2659529
theorem B3993113 : Blo 1244440 3993113 := bstep (se 2 (by rfl) ⟨1497417, by rfl⟩ : syracuseStep 3993113 = 2994835) B2994835
theorem B4206113 : Blo 1244440 4206113 := bstep (se 2 (by rfl) ⟨1577292, by rfl⟩ : syracuseStep 4206113 = 3154585) B3154585
theorem B2100775 : Blo 1244440 2100775 := bstep (se 1 (by rfl) ⟨1575581, by rfl⟩ : syracuseStep 2100775 = 3151163) B3151163
theorem B15158917 : Blo 1244440 15158917 := bstep (se 4 (by rfl) ⟨1421148, by rfl⟩ : syracuseStep 15158917 = 2842297) B2842297
theorem B10637021 : Blo 1244440 10637021 := bstep (se 3 (by rfl) ⟨1994441, by rfl⟩ : syracuseStep 10637021 = 3988883) B3988883
theorem B4206329 : Blo 1244440 4206329 := bstep (se 2 (by rfl) ⟨1577373, by rfl⟩ : syracuseStep 4206329 = 3154747) B3154747
theorem B2101099 : Blo 1244440 2101099 := bstep (se 1 (by rfl) ⟨1575824, by rfl⟩ : syracuseStep 2101099 = 3151649) B3151649
theorem B34074503 : Blo 1244440 34074503 := bstep (se 1 (by rfl) ⟨25555877, by rfl⟩ : syracuseStep 34074503 = 51111755) B51111755
theorem B21041059 : Blo 1244440 21041059 := bstep (se 1 (by rfl) ⟨15780794, by rfl⟩ : syracuseStep 21041059 = 31561589) B31561589
theorem B1421231 : Blo 1244440 1421231 := bstep (se 1 (by rfl) ⟨1065923, by rfl⟩ : syracuseStep 1421231 = 2131847) B2131847
theorem B11964347 : Blo 1244440 11964347 := bstep (se 1 (by rfl) ⟨8973260, by rfl⟩ : syracuseStep 11964347 = 17946521) B17946521
theorem B19697669 : Blo 1244440 19697669 := bstep (se 4 (by rfl) ⟨1846656, by rfl⟩ : syracuseStep 19697669 = 3693313) B3693313
theorem B4206599 : Blo 1244440 4206599 := bstep (se 1 (by rfl) ⟨3154949, by rfl⟩ : syracuseStep 4206599 = 6309899) B6309899
theorem B2363411 : Blo 1244440 2363411 := bstep (se 1 (by rfl) ⟨1772558, by rfl⟩ : syracuseStep 2363411 = 3545117) B3545117
theorem B1576999 : Blo 1244440 1576999 := bstep (se 1 (by rfl) ⟨1182749, by rfl⟩ : syracuseStep 1576999 = 2365499) B2365499
theorem B4206707 : Blo 1244440 4206707 := bstep (se 1 (by rfl) ⟨3155030, by rfl⟩ : syracuseStep 4206707 = 6310061) B6310061
theorem B1577323 : Blo 1244440 1577323 := bstep (se 1 (by rfl) ⟨1182992, by rfl⟩ : syracuseStep 1577323 = 2365985) B2365985
theorem B1683931 : Blo 1244440 1683931 := bstep (se 1 (by rfl) ⟨1262948, by rfl⟩ : syracuseStep 1683931 = 2525897) B2525897
theorem B3150323 : Blo 1244440 3150323 := bstep (se 1 (by rfl) ⟨2362742, by rfl⟩ : syracuseStep 3150323 = 4725485) B4725485
theorem B8753723 : Blo 1244440 8753723 := bstep (se 1 (by rfl) ⟨6565292, by rfl⟩ : syracuseStep 8753723 = 13130585) B13130585
theorem B22737509 : Blo 1244440 22737509 := bstep (se 4 (by rfl) ⟨2131641, by rfl⟩ : syracuseStep 22737509 = 4263283) B4263283
theorem B6304391 : Blo 1244440 6304391 := bstep (se 1 (by rfl) ⟨4728293, by rfl⟩ : syracuseStep 6304391 = 9456587) B9456587
theorem B3150535 : Blo 1244440 3150535 := bstep (se 1 (by rfl) ⟨2362901, by rfl⟩ : syracuseStep 3150535 = 4725803) B4725803
theorem B9450269 : Blo 1244440 9450269 := bstep (se 3 (by rfl) ⟨1771925, by rfl⟩ : syracuseStep 9450269 = 3543851) B3543851
theorem B1684319 : Blo 1244440 1684319 := bstep (se 1 (by rfl) ⟨1263239, by rfl⟩ : syracuseStep 1684319 = 2526479) B2526479
theorem B2102159 : Blo 1244440 2102159 := bstep (se 1 (by rfl) ⟨1576619, by rfl⟩ : syracuseStep 2102159 = 3153239) B3153239
theorem B14193629 : Blo 1244440 14193629 := bstep (se 3 (by rfl) ⟨2661305, by rfl⟩ : syracuseStep 14193629 = 5322611) B5322611
theorem B2659385 : Blo 1244440 2659385 := bstep (se 2 (by rfl) ⟨997269, by rfl⟩ : syracuseStep 2659385 = 1994539) B1994539
theorem B23344193 : Blo 1244440 23344193 := bstep (se 2 (by rfl) ⟨8754072, by rfl⟩ : syracuseStep 23344193 = 17508145) B17508145
theorem B2102395 : Blo 1244440 2102395 := bstep (se 1 (by rfl) ⟨1576796, by rfl⟩ : syracuseStep 2102395 = 3153593) B3153593
theorem B13456601 : Blo 1244440 13456601 := bstep (se 2 (by rfl) ⟨5046225, by rfl⟩ : syracuseStep 13456601 = 10092451) B10092451
theorem B4732289 : Blo 1244440 4732289 := bstep (se 2 (by rfl) ⟨1774608, by rfl⟩ : syracuseStep 4732289 = 3549217) B3549217
theorem B2364815 : Blo 1244440 2364815 := bstep (se 1 (by rfl) ⟨1773611, by rfl⟩ : syracuseStep 2364815 = 3547223) B3547223
theorem B4732303 : Blo 1244440 4732303 := bstep (se 1 (by rfl) ⟨3549227, by rfl⟩ : syracuseStep 4732303 = 7098455) B7098455
theorem B12776869 : Blo 1244440 12776869 := bstep (se 4 (by rfl) ⟨1197831, by rfl⟩ : syracuseStep 12776869 = 2395663) B2395663
theorem B7091621 : Blo 1244440 7091621 := bstep (se 4 (by rfl) ⟨664839, by rfl⟩ : syracuseStep 7091621 = 1329679) B1329679
theorem B8517037 : Blo 1244440 8517037 := bstep (se 3 (by rfl) ⟨1596944, by rfl⟩ : syracuseStep 8517037 = 3193889) B3193889
theorem B1496495 : Blo 1244440 1496495 := bstep (se 1 (by rfl) ⟨1122371, by rfl⟩ : syracuseStep 1496495 = 2244743) B2244743
theorem B4257305 : Blo 1244440 4257305 := bstep (se 2 (by rfl) ⟨1596489, by rfl⟩ : syracuseStep 4257305 = 3192979) B3192979
theorem B2364967 : Blo 1244440 2364967 := bstep (se 1 (by rfl) ⟨1773725, by rfl⟩ : syracuseStep 2364967 = 3547451) B3547451
theorem B3151457 : Blo 1244440 3151457 := bstep (se 2 (by rfl) ⟨1181796, by rfl⟩ : syracuseStep 3151457 = 2363593) B2363593
theorem B2365051 : Blo 1244440 2365051 := bstep (se 1 (by rfl) ⟨1773788, by rfl⟩ : syracuseStep 2365051 = 3547577) B3547577
theorem B3364541 : Blo 1244440 3364541 := bstep (se 3 (by rfl) ⟨630851, by rfl⟩ : syracuseStep 3364541 = 1261703) B1261703
theorem B2397943 : Blo 1244440 2397943 := bstep (se 1 (by rfl) ⟨1798457, by rfl⟩ : syracuseStep 2397943 = 3596915) B3596915
theorem B2103259 : Blo 1244440 2103259 := bstep (se 1 (by rfl) ⟨1577444, by rfl⟩ : syracuseStep 2103259 = 3154889) B3154889
theorem B6305849 : Blo 1244440 6305849 := bstep (se 2 (by rfl) ⟨2364693, by rfl⟩ : syracuseStep 6305849 = 4729387) B4729387
theorem B7092305 : Blo 1244440 7092305 := bstep (se 2 (by rfl) ⟨2659614, by rfl⟩ : syracuseStep 7092305 = 5319229) B5319229
theorem B2365537 : Blo 1244440 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B4200605 : Blo 1244440 4200605 := bstep (se 3 (by rfl) ⟨787613, by rfl⟩ : syracuseStep 4200605 = 1575227) B1575227
theorem B4044971 : Blo 1244440 4044971 := bstep (se 1 (by rfl) ⟨3033728, by rfl⟩ : syracuseStep 4044971 = 6067457) B6067457
theorem B31938947 : Blo 1244440 31938947 := bstep (se 1 (by rfl) ⟨23954210, by rfl⟩ : syracuseStep 31938947 = 47908421) B47908421
theorem B2242991 : Blo 1244440 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B3840475 : Blo 1244440 3840475 := bstep (se 1 (by rfl) ⟨2880356, by rfl⟩ : syracuseStep 3840475 = 5760713) B5760713
theorem B4725287 : Blo 1244440 4725287 := bstep (se 1 (by rfl) ⟨3543965, by rfl⟩ : syracuseStep 4725287 = 7087931) B7087931
theorem B5388859 : Blo 1244440 5388859 := bstep (se 1 (by rfl) ⟨4041644, by rfl⟩ : syracuseStep 5388859 = 8083289) B8083289
theorem B4487827 : Blo 1244440 4487827 := bstep (se 1 (by rfl) ⟨3365870, by rfl⟩ : syracuseStep 4487827 = 6731741) B6731741
theorem B4201145 : Blo 1244440 4201145 := bstep (se 2 (by rfl) ⟨1575429, by rfl⟩ : syracuseStep 4201145 = 3150859) B3150859
theorem B6732497 : Blo 1244440 6732497 := bstep (se 2 (by rfl) ⟨2524686, by rfl⟩ : syracuseStep 6732497 = 5049373) B5049373
theorem B9099985 : Blo 1244440 9099985 := bstep (se 2 (by rfl) ⟨3412494, by rfl⟩ : syracuseStep 9099985 = 6824989) B6824989
theorem B3988217 : Blo 1244440 3988217 := bstep (se 2 (by rfl) ⟨1495581, by rfl⟩ : syracuseStep 3988217 = 2991163) B2991163
theorem B2800457 : Blo 1244440 2800457 := bstep (se 2 (by rfl) ⟨1050171, by rfl⟩ : syracuseStep 2800457 = 2100343) B2100343
theorem B1866671 : Blo 1244440 1866671 := bstep (se 1 (by rfl) ⟨1400003, by rfl⟩ : syracuseStep 1866671 = 2800007) B2800007
theorem B2128823 : Blo 1244440 2128823 := bstep (se 1 (by rfl) ⟨1596617, by rfl⟩ : syracuseStep 2128823 = 3193235) B3193235
theorem B3546119 : Blo 1244440 3546119 := bstep (se 1 (by rfl) ⟨2659589, by rfl⟩ : syracuseStep 3546119 = 5319179) B5319179
theorem B1866761 : Blo 1244440 1866761 := bstep (se 2 (by rfl) ⟨700035, by rfl⟩ : syracuseStep 1866761 = 1400071) B1400071
theorem B3152915 : Blo 1244440 3152915 := bstep (se 1 (by rfl) ⟨2364686, by rfl⟩ : syracuseStep 3152915 = 4729373) B4729373
theorem B8092691 : Blo 1244440 8092691 := bstep (se 1 (by rfl) ⟨6069518, by rfl⟩ : syracuseStep 8092691 = 12139037) B12139037
theorem B1866791 : Blo 1244440 1866791 := bstep (se 1 (by rfl) ⟨1400093, by rfl⟩ : syracuseStep 1866791 = 2800187) B2800187
theorem B1866875 : Blo 1244440 1866875 := bstep (se 1 (by rfl) ⟨1400156, by rfl⟩ : syracuseStep 1866875 = 2800313) B2800313
theorem B6732953 : Blo 1244440 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B9461447 : Blo 1244440 9461447 := bstep (se 1 (by rfl) ⟨7096085, by rfl⟩ : syracuseStep 9461447 = 14192171) B14192171
theorem B1867001 : Blo 1244440 1867001 := bstep (se 2 (by rfl) ⟨700125, by rfl⟩ : syracuseStep 1867001 = 1400251) B1400251
theorem B4201739 : Blo 1244440 4201739 := bstep (se 1 (by rfl) ⟨3151304, by rfl⟩ : syracuseStep 4201739 = 6302609) B6302609
theorem B1244455 : Blo 1244440 1244455 := bstep (se 1 (by rfl) ⟨933341, by rfl⟩ : syracuseStep 1244455 = 1866683) B1866683
theorem B1244495 : Blo 1244440 1244495 := bstep (se 1 (by rfl) ⟨933371, by rfl⟩ : syracuseStep 1244495 = 1866743) B1866743
theorem B1244511 : Blo 1244440 1244511 := bstep (se 1 (by rfl) ⟨933383, by rfl⟩ : syracuseStep 1244511 = 1866767) B1866767
theorem B1867103 : Blo 1244440 1867103 := bstep (se 1 (by rfl) ⟨1400327, by rfl⟩ : syracuseStep 1867103 = 2800655) B2800655
theorem B1867115 : Blo 1244440 1867115 := bstep (se 1 (by rfl) ⟨1400336, by rfl⟩ : syracuseStep 1867115 = 2800673) B2800673
theorem B1244539 : Blo 1244440 1244539 := bstep (se 1 (by rfl) ⟨933404, by rfl⟩ : syracuseStep 1244539 = 1866809) B1866809
theorem B12139901 : Blo 1244440 12139901 := bstep (se 3 (by rfl) ⟨2276231, by rfl⟩ : syracuseStep 12139901 = 4552463) B4552463
theorem B1244591 : Blo 1244440 1244591 := bstep (se 1 (by rfl) ⟨933443, by rfl⟩ : syracuseStep 1244591 = 1866887) B1866887
theorem B1244615 : Blo 1244440 1244615 := bstep (se 1 (by rfl) ⟨933461, by rfl⟩ : syracuseStep 1244615 = 1866923) B1866923
theorem B1244635 : Blo 1244440 1244635 := bstep (se 1 (by rfl) ⟨933476, by rfl⟩ : syracuseStep 1244635 = 1866953) B1866953
theorem B4726259 : Blo 1244440 4726259 := bstep (se 1 (by rfl) ⟨3544694, by rfl⟩ : syracuseStep 4726259 = 7089389) B7089389
theorem B4202009 : Blo 1244440 4202009 := bstep (se 2 (by rfl) ⟨1575753, by rfl⟩ : syracuseStep 4202009 = 3151507) B3151507
theorem B1244711 : Blo 1244440 1244711 := bstep (se 1 (by rfl) ⟨933533, by rfl⟩ : syracuseStep 1244711 = 1867067) B1867067
theorem B1400359 : Blo 1244440 1400359 := bstep (se 1 (by rfl) ⟨1050269, by rfl⟩ : syracuseStep 1400359 = 2100539) B2100539
theorem B1244751 : Blo 1244440 1244751 := bstep (se 1 (by rfl) ⟨933563, by rfl⟩ : syracuseStep 1244751 = 1867127) B1867127
theorem B1867343 : Blo 1244440 1867343 := bstep (se 1 (by rfl) ⟨1400507, by rfl⟩ : syracuseStep 1867343 = 2801015) B2801015
theorem B1244767 : Blo 1244440 1244767 := bstep (se 1 (by rfl) ⟨933575, by rfl⟩ : syracuseStep 1244767 = 1867151) B1867151
theorem B2801249 : Blo 1244440 2801249 := bstep (se 2 (by rfl) ⟨1050468, by rfl⟩ : syracuseStep 2801249 = 2100937) B2100937
theorem B1244795 : Blo 1244440 1244795 := bstep (se 1 (by rfl) ⟨933596, by rfl⟩ : syracuseStep 1244795 = 1867193) B1867193
theorem B1244847 : Blo 1244440 1244847 := bstep (se 1 (by rfl) ⟨933635, by rfl⟩ : syracuseStep 1244847 = 1867271) B1867271
theorem B4726457 : Blo 1244440 4726457 := bstep (se 2 (by rfl) ⟨1772421, by rfl⟩ : syracuseStep 4726457 = 3544843) B3544843
theorem B3989191 : Blo 1244440 3989191 := bstep (se 1 (by rfl) ⟨2991893, by rfl⟩ : syracuseStep 3989191 = 5983787) B5983787
theorem B4726471 : Blo 1244440 4726471 := bstep (se 1 (by rfl) ⟨3544853, by rfl⟩ : syracuseStep 4726471 = 7089707) B7089707
theorem B1244871 : Blo 1244440 1244871 := bstep (se 1 (by rfl) ⟨933653, by rfl⟩ : syracuseStep 1244871 = 1867307) B1867307
theorem B1867463 : Blo 1244440 1867463 := bstep (se 1 (by rfl) ⟨1400597, by rfl⟩ : syracuseStep 1867463 = 2801195) B2801195
theorem B2244295 : Blo 1244440 2244295 := bstep (se 1 (by rfl) ⟨1683221, by rfl⟩ : syracuseStep 2244295 = 3366443) B3366443
theorem B1244891 : Blo 1244440 1244891 := bstep (se 1 (by rfl) ⟨933668, by rfl⟩ : syracuseStep 1244891 = 1867337) B1867337
theorem B1244967 : Blo 1244440 1244967 := bstep (se 1 (by rfl) ⟨933725, by rfl⟩ : syracuseStep 1244967 = 1867451) B1867451
theorem B3989321 : Blo 1244440 3989321 := bstep (se 2 (by rfl) ⟨1495995, by rfl⟩ : syracuseStep 3989321 = 2991991) B2991991
theorem B1245007 : Blo 1244440 1245007 := bstep (se 1 (by rfl) ⟨933755, by rfl⟩ : syracuseStep 1245007 = 1867511) B1867511
theorem B1245023 : Blo 1244440 1245023 := bstep (se 1 (by rfl) ⟨933767, by rfl⟩ : syracuseStep 1245023 = 1867535) B1867535
theorem B1867625 : Blo 1244440 1867625 := bstep (se 2 (by rfl) ⟨700359, by rfl⟩ : syracuseStep 1867625 = 1400719) B1400719
theorem B5316461 : Blo 1244440 5316461 := bstep (se 3 (by rfl) ⟨996836, by rfl⟩ : syracuseStep 5316461 = 1993673) B1993673
theorem B1245051 : Blo 1244440 1245051 := bstep (se 1 (by rfl) ⟨933788, by rfl⟩ : syracuseStep 1245051 = 1867577) B1867577
theorem B1245103 : Blo 1244440 1245103 := bstep (se 1 (by rfl) ⟨933827, by rfl⟩ : syracuseStep 1245103 = 1867655) B1867655
theorem B1867703 : Blo 1244440 1867703 := bstep (se 1 (by rfl) ⟨1400777, by rfl⟩ : syracuseStep 1867703 = 2801555) B2801555
theorem B2801591 : Blo 1244440 2801591 := bstep (se 1 (by rfl) ⟨2101193, by rfl⟩ : syracuseStep 2801591 = 4202387) B4202387
theorem B1245127 : Blo 1244440 1245127 := bstep (se 1 (by rfl) ⟨933845, by rfl⟩ : syracuseStep 1245127 = 1867691) B1867691
theorem B1245147 : Blo 1244440 1245147 := bstep (se 1 (by rfl) ⟨933860, by rfl⟩ : syracuseStep 1245147 = 1867721) B1867721
theorem B1867739 : Blo 1244440 1867739 := bstep (se 1 (by rfl) ⟨1400804, by rfl⟩ : syracuseStep 1867739 = 2801609) B2801609
theorem B13131779 : Blo 1244440 13131779 := bstep (se 1 (by rfl) ⟨9848834, by rfl⟩ : syracuseStep 13131779 = 19697669) B19697669
theorem B3154049 : Blo 1244440 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B3367177 : Blo 1244440 3367177 := bstep (se 2 (by rfl) ⟨1262691, by rfl⟩ : syracuseStep 3367177 = 2525383) B2525383
theorem B1245471 : Blo 1244440 1245471 := bstep (se 1 (by rfl) ⟨934103, by rfl⟩ : syracuseStep 1245471 = 1868207) B1868207
theorem B1868123 : Blo 1244440 1868123 := bstep (se 1 (by rfl) ⟨1401092, by rfl⟩ : syracuseStep 1868123 = 2802185) B2802185
theorem B1245531 : Blo 1244440 1245531 := bstep (se 1 (by rfl) ⟨934148, by rfl⟩ : syracuseStep 1245531 = 1868297) B1868297
theorem B1245551 : Blo 1244440 1245551 := bstep (se 1 (by rfl) ⟨934163, by rfl⟩ : syracuseStep 1245551 = 1868327) B1868327
theorem B1245607 : Blo 1244440 1245607 := bstep (se 1 (by rfl) ⟨934205, by rfl⟩ : syracuseStep 1245607 = 1868411) B1868411
theorem B4202927 : Blo 1244440 4202927 := bstep (se 1 (by rfl) ⟨3152195, by rfl⟩ : syracuseStep 4202927 = 6304391) B6304391
theorem B2802095 : Blo 1244440 2802095 := bstep (se 1 (by rfl) ⟨2101571, by rfl⟩ : syracuseStep 2802095 = 4203143) B4203143
theorem B2802131 : Blo 1244440 2802131 := bstep (se 1 (by rfl) ⟨2101598, by rfl⟩ : syracuseStep 2802131 = 4203197) B4203197
theorem B1245691 : Blo 1244440 1245691 := bstep (se 1 (by rfl) ⟨934268, by rfl⟩ : syracuseStep 1245691 = 1868537) B1868537
theorem B6300179 : Blo 1244440 6300179 := bstep (se 1 (by rfl) ⟨4725134, by rfl⟩ : syracuseStep 6300179 = 9450269) B9450269
theorem B2802239 : Blo 1244440 2802239 := bstep (se 1 (by rfl) ⟨2101679, by rfl⟩ : syracuseStep 2802239 = 4203359) B4203359
theorem B1868351 : Blo 1244440 1868351 := bstep (se 1 (by rfl) ⟨1401263, by rfl⟩ : syracuseStep 1868351 = 2802527) B2802527
theorem B1245759 : Blo 1244440 1245759 := bstep (se 1 (by rfl) ⟨934319, by rfl⟩ : syracuseStep 1245759 = 1868639) B1868639
theorem B1245767 : Blo 1244440 1245767 := bstep (se 1 (by rfl) ⟨934325, by rfl⟩ : syracuseStep 1245767 = 1868651) B1868651
theorem B1401439 : Blo 1244440 1401439 := bstep (se 1 (by rfl) ⟨1051079, by rfl⟩ : syracuseStep 1401439 = 2102159) B2102159
theorem B5120633 : Blo 1244440 5120633 := bstep (se 2 (by rfl) ⟨1920237, by rfl⟩ : syracuseStep 5120633 = 3840475) B3840475
theorem B2245241 : Blo 1244440 2245241 := bstep (se 2 (by rfl) ⟨841965, by rfl⟩ : syracuseStep 2245241 = 1683931) B1683931
theorem B9462419 : Blo 1244440 9462419 := bstep (se 1 (by rfl) ⟨7096814, by rfl⟩ : syracuseStep 9462419 = 14193629) B14193629
theorem B2802347 : Blo 1244440 2802347 := bstep (se 1 (by rfl) ⟨2101760, by rfl⟩ : syracuseStep 2802347 = 4203521) B4203521
theorem B1868471 : Blo 1244440 1868471 := bstep (se 1 (by rfl) ⟨1401353, by rfl⟩ : syracuseStep 1868471 = 2802707) B2802707
theorem B1245919 : Blo 1244440 1245919 := bstep (se 1 (by rfl) ⟨934439, by rfl⟩ : syracuseStep 1245919 = 1868879) B1868879
theorem B7185145 : Blo 1244440 7185145 := bstep (se 2 (by rfl) ⟨2694429, by rfl⟩ : syracuseStep 7185145 = 5388859) B5388859
theorem B1245999 : Blo 1244440 1245999 := bstep (se 1 (by rfl) ⟨934499, by rfl⟩ : syracuseStep 1245999 = 1868999) B1868999
theorem B8971067 : Blo 1244440 8971067 := bstep (se 1 (by rfl) ⟨6728300, by rfl⟩ : syracuseStep 8971067 = 13456601) B13456601
theorem B1868699 : Blo 1244440 1868699 := bstep (se 1 (by rfl) ⟨1401524, by rfl⟩ : syracuseStep 1868699 = 2803049) B2803049
theorem B1246107 : Blo 1244440 1246107 := bstep (se 1 (by rfl) ⟨934580, by rfl⟩ : syracuseStep 1246107 = 1869161) B1869161
theorem B3154859 : Blo 1244440 3154859 := bstep (se 1 (by rfl) ⟨2366144, by rfl⟩ : syracuseStep 3154859 = 4732289) B4732289
theorem B12133313 : Blo 1244440 12133313 := bstep (se 2 (by rfl) ⟨4549992, by rfl⟩ : syracuseStep 12133313 = 9099985) B9099985
theorem B4727747 : Blo 1244440 4727747 := bstep (se 1 (by rfl) ⟨3545810, by rfl⟩ : syracuseStep 4727747 = 7091621) B7091621
theorem B1246159 : Blo 1244440 1246159 := bstep (se 1 (by rfl) ⟨934619, by rfl⟩ : syracuseStep 1246159 = 1869239) B1869239
theorem B1246183 : Blo 1244440 1246183 := bstep (se 1 (by rfl) ⟨934637, by rfl⟩ : syracuseStep 1246183 = 1869275) B1869275
theorem B17966069 : Blo 1244440 17966069 := bstep (se 5 (by rfl) ⟨842159, by rfl⟩ : syracuseStep 17966069 = 1684319) B1684319
theorem B5981309 : Blo 1244440 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B3990653 : Blo 1244440 3990653 := bstep (se 3 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 3990653 = 1496495) B1496495
theorem B5981327 : Blo 1244440 5981327 := bstep (se 1 (by rfl) ⟨4485995, by rfl⟩ : syracuseStep 5981327 = 8971991) B8971991
theorem B9585863 : Blo 1244440 9585863 := bstep (se 1 (by rfl) ⟨7189397, by rfl⟩ : syracuseStep 9585863 = 14378795) B14378795
theorem B2802887 : Blo 1244440 2802887 := bstep (se 1 (by rfl) ⟨2102165, by rfl⟩ : syracuseStep 2802887 = 4204331) B4204331
theorem B7095539 : Blo 1244440 7095539 := bstep (se 1 (by rfl) ⟨5321654, by rfl⟩ : syracuseStep 7095539 = 10643309) B10643309
theorem B12789029 : Blo 1244440 12789029 := bstep (se 4 (by rfl) ⟨1198971, by rfl⟩ : syracuseStep 12789029 = 2397943) B2397943
theorem B1869095 : Blo 1244440 1869095 := bstep (se 1 (by rfl) ⟨1401821, by rfl⟩ : syracuseStep 1869095 = 2803643) B2803643
theorem B20186455 : Blo 1244440 20186455 := bstep (se 1 (by rfl) ⟨15139841, by rfl⟩ : syracuseStep 20186455 = 30279683) B30279683
theorem B4203899 : Blo 1244440 4203899 := bstep (se 1 (by rfl) ⟨3152924, by rfl⟩ : syracuseStep 4203899 = 6305849) B6305849
theorem B2803067 : Blo 1244440 2803067 := bstep (se 1 (by rfl) ⟨2102300, by rfl⟩ : syracuseStep 2803067 = 4204601) B4204601
theorem B1869179 : Blo 1244440 1869179 := bstep (se 1 (by rfl) ⟨1401884, by rfl⟩ : syracuseStep 1869179 = 2803769) B2803769
theorem B4728203 : Blo 1244440 4728203 := bstep (se 1 (by rfl) ⟨3546152, by rfl⟩ : syracuseStep 4728203 = 7092305) B7092305
theorem B2696647 : Blo 1244440 2696647 := bstep (se 1 (by rfl) ⟨2022485, by rfl⟩ : syracuseStep 2696647 = 4044971) B4044971
theorem B2803193 : Blo 1244440 2803193 := bstep (se 2 (by rfl) ⟨1051197, by rfl⟩ : syracuseStep 2803193 = 2102395) B2102395
theorem B1869305 : Blo 1244440 1869305 := bstep (se 2 (by rfl) ⟨700989, by rfl⟩ : syracuseStep 1869305 = 1401979) B1401979
theorem B2803283 : Blo 1244440 2803283 := bstep (se 1 (by rfl) ⟨2102462, by rfl⟩ : syracuseStep 2803283 = 4204925) B4204925
theorem B21292631 : Blo 1244440 21292631 := bstep (se 1 (by rfl) ⟨15969473, by rfl⟩ : syracuseStep 21292631 = 31938947) B31938947
theorem B1869407 : Blo 1244440 1869407 := bstep (se 1 (by rfl) ⟨1402055, by rfl⟩ : syracuseStep 1869407 = 2804111) B2804111
theorem B2803463 : Blo 1244440 2803463 := bstep (se 1 (by rfl) ⟨2102597, by rfl⟩ : syracuseStep 2803463 = 4205195) B4205195
theorem B1869623 : Blo 1244440 1869623 := bstep (se 1 (by rfl) ⟨1402217, by rfl⟩ : syracuseStep 1869623 = 2804435) B2804435
theorem B6309737 : Blo 1244440 6309737 := bstep (se 2 (by rfl) ⟨2366151, by rfl⟩ : syracuseStep 6309737 = 4732303) B4732303
theorem B11356049 : Blo 1244440 11356049 := bstep (se 2 (by rfl) ⟨4258518, by rfl⟩ : syracuseStep 11356049 = 8517037) B8517037
theorem B7096247 : Blo 1244440 7096247 := bstep (se 1 (by rfl) ⟨5322185, by rfl⟩ : syracuseStep 7096247 = 10644371) B10644371
theorem B1419215 : Blo 1244440 1419215 := bstep (se 1 (by rfl) ⟨1064411, by rfl⟩ : syracuseStep 1419215 = 2128823) B2128823
theorem B10635245 : Blo 1244440 10635245 := bstep (se 3 (by rfl) ⟨1994108, by rfl⟩ : syracuseStep 10635245 = 3988217) B3988217
theorem B20211889 : Blo 1244440 20211889 := bstep (se 2 (by rfl) ⟨7579458, by rfl⟩ : syracuseStep 20211889 = 15158917) B15158917
theorem B6301961 : Blo 1244440 6301961 := bstep (se 2 (by rfl) ⟨2363235, by rfl⟩ : syracuseStep 6301961 = 4726471) B4726471
theorem B5318921 : Blo 1244440 5318921 := bstep (se 2 (by rfl) ⟨1994595, by rfl⟩ : syracuseStep 5318921 = 3989191) B3989191
theorem B2992393 : Blo 1244440 2992393 := bstep (se 2 (by rfl) ⟨1122147, by rfl⟩ : syracuseStep 2992393 = 2244295) B2244295
theorem B2804075 : Blo 1244440 2804075 := bstep (se 1 (by rfl) ⟨2103056, by rfl⟩ : syracuseStep 2804075 = 4206113) B4206113
theorem B9456101 : Blo 1244440 9456101 := bstep (se 4 (by rfl) ⟨886509, by rfl⟩ : syracuseStep 9456101 = 1773019) B1773019
theorem B2804219 : Blo 1244440 2804219 := bstep (se 1 (by rfl) ⟨2103164, by rfl⟩ : syracuseStep 2804219 = 4206329) B4206329
theorem B2804345 : Blo 1244440 2804345 := bstep (se 2 (by rfl) ⟨1051629, by rfl⟩ : syracuseStep 2804345 = 2103259) B2103259
theorem B2804399 : Blo 1244440 2804399 := bstep (se 1 (by rfl) ⟨2103299, by rfl⟩ : syracuseStep 2804399 = 4206599) B4206599
theorem B1575607 : Blo 1244440 1575607 := bstep (se 1 (by rfl) ⟨1181705, by rfl⟩ : syracuseStep 1575607 = 2363411) B2363411
theorem B4205303 : Blo 1244440 4205303 := bstep (se 1 (by rfl) ⟨3153977, by rfl⟩ : syracuseStep 4205303 = 6307955) B6307955
theorem B2804471 : Blo 1244440 2804471 := bstep (se 1 (by rfl) ⟨2103353, by rfl⟩ : syracuseStep 2804471 = 4206707) B4206707
theorem B2100215 : Blo 1244440 2100215 := bstep (se 1 (by rfl) ⟨1575161, by rfl⟩ : syracuseStep 2100215 = 3150323) B3150323
theorem B11365391 : Blo 1244440 11365391 := bstep (se 1 (by rfl) ⟨8524043, by rfl⟩ : syracuseStep 11365391 = 17048087) B17048087
theorem B5835815 : Blo 1244440 5835815 := bstep (se 1 (by rfl) ⟨4376861, by rfl⟩ : syracuseStep 5835815 = 8753723) B8753723
theorem B15158339 : Blo 1244440 15158339 := bstep (se 1 (by rfl) ⟨11368754, by rfl⟩ : syracuseStep 15158339 = 22737509) B22737509
theorem B6303095 : Blo 1244440 6303095 := bstep (se 1 (by rfl) ⟨4727321, by rfl⟩ : syracuseStep 6303095 = 9454643) B9454643
theorem B1772923 : Blo 1244440 1772923 := bstep (se 1 (by rfl) ⟨1329692, by rfl⟩ : syracuseStep 1772923 = 2659385) B2659385
theorem B5320151 : Blo 1244440 5320151 := bstep (se 1 (by rfl) ⟨3990113, by rfl⟩ : syracuseStep 5320151 = 7980227) B7980227
theorem B5983769 : Blo 1244440 5983769 := bstep (se 2 (by rfl) ⟨2243913, by rfl⟩ : syracuseStep 5983769 = 4487827) B4487827
theorem B6303257 : Blo 1244440 6303257 := bstep (se 2 (by rfl) ⟨2363721, by rfl⟩ : syracuseStep 6303257 = 4727443) B4727443
theorem B5680801 : Blo 1244440 5680801 := bstep (se 2 (by rfl) ⟨2130300, by rfl⟩ : syracuseStep 5680801 = 4260601) B4260601
theorem B2838203 : Blo 1244440 2838203 := bstep (se 1 (by rfl) ⟨2128652, by rfl⟩ : syracuseStep 2838203 = 4257305) B4257305
theorem B2100971 : Blo 1244440 2100971 := bstep (se 1 (by rfl) ⟨1575728, by rfl⟩ : syracuseStep 2100971 = 3151457) B3151457
theorem B4206383 : Blo 1244440 4206383 := bstep (se 1 (by rfl) ⟨3154787, by rfl⟩ : syracuseStep 4206383 = 6309575) B6309575
theorem B12128321 : Blo 1244440 12128321 := bstep (se 2 (by rfl) ⟨4548120, by rfl⟩ : syracuseStep 12128321 = 9096241) B9096241
theorem B3150191 : Blo 1244440 3150191 := bstep (se 1 (by rfl) ⟨2362643, by rfl⟩ : syracuseStep 3150191 = 4725287) B4725287
theorem B20189573 : Blo 1244440 20189573 := bstep (se 4 (by rfl) ⟨1892772, by rfl⟩ : syracuseStep 20189573 = 3785545) B3785545
theorem B15159797 : Blo 1244440 15159797 := bstep (se 5 (by rfl) ⟨710615, by rfl⟩ : syracuseStep 15159797 = 1421231) B1421231
theorem B17953325 : Blo 1244440 17953325 := bstep (se 3 (by rfl) ⟨3366248, by rfl⟩ : syracuseStep 17953325 = 6732497) B6732497
theorem B17035825 : Blo 1244440 17035825 := bstep (se 2 (by rfl) ⟨6388434, by rfl⟩ : syracuseStep 17035825 = 12776869) B12776869
theorem B2364079 : Blo 1244440 2364079 := bstep (se 1 (by rfl) ⟨1773059, by rfl⟩ : syracuseStep 2364079 = 3546119) B3546119
theorem B2101943 : Blo 1244440 2101943 := bstep (se 1 (by rfl) ⟨1576457, by rfl⟩ : syracuseStep 2101943 = 3152915) B3152915
theorem B5395127 : Blo 1244440 5395127 := bstep (se 1 (by rfl) ⟨4046345, by rfl⟩ : syracuseStep 5395127 = 8092691) B8092691
theorem B3150839 : Blo 1244440 3150839 := bstep (se 1 (by rfl) ⟨2363129, by rfl⟩ : syracuseStep 3150839 = 4726259) B4726259
theorem B11973689 : Blo 1244440 11973689 := bstep (se 2 (by rfl) ⟨4490133, by rfl⟩ : syracuseStep 11973689 = 8980267) B8980267
theorem B3150971 : Blo 1244440 3150971 := bstep (se 1 (by rfl) ⟨2363228, by rfl⟩ : syracuseStep 3150971 = 4726457) B4726457
theorem B7091347 : Blo 1244440 7091347 := bstep (se 1 (by rfl) ⟨5318510, by rfl⟩ : syracuseStep 7091347 = 10637021) B10637021
theorem B28054745 : Blo 1244440 28054745 := bstep (se 2 (by rfl) ⟨10520529, by rfl⟩ : syracuseStep 28054745 = 21041059) B21041059
theorem B2659547 : Blo 1244440 2659547 := bstep (se 1 (by rfl) ⟨1994660, by rfl⟩ : syracuseStep 2659547 = 3989321) B3989321
theorem B3544307 : Blo 1244440 3544307 := bstep (se 1 (by rfl) ⟨2658230, by rfl⟩ : syracuseStep 3544307 = 5316461) B5316461
theorem B7976231 : Blo 1244440 7976231 := bstep (se 1 (by rfl) ⟨5982173, by rfl⟩ : syracuseStep 7976231 = 11964347) B11964347
theorem B3986783 : Blo 1244440 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B2102665 : Blo 1244440 2102665 := bstep (se 2 (by rfl) ⟨788499, by rfl⟩ : syracuseStep 2102665 = 1576999) B1576999
theorem B2103097 : Blo 1244440 2103097 := bstep (se 2 (by rfl) ⟨788661, by rfl⟩ : syracuseStep 2103097 = 1577323) B1577323
theorem B11974493 : Blo 1244440 11974493 := bstep (se 3 (by rfl) ⟨2245217, by rfl⟩ : syracuseStep 11974493 = 4490435) B4490435
theorem B15562795 : Blo 1244440 15562795 := bstep (se 1 (by rfl) ⟨11672096, by rfl⟩ : syracuseStep 15562795 = 23344193) B23344193
theorem B26941571 : Blo 1244440 26941571 := bstep (se 1 (by rfl) ⟨20206178, by rfl⟩ : syracuseStep 26941571 = 40412357) B40412357
theorem B4200713 : Blo 1244440 4200713 := bstep (se 2 (by rfl) ⟨1575267, by rfl⟩ : syracuseStep 4200713 = 3150535) B3150535
theorem B2365787 : Blo 1244440 2365787 := bstep (se 1 (by rfl) ⟨1774340, by rfl⟩ : syracuseStep 2365787 = 3548681) B3548681
theorem B6306173 : Blo 1244440 6306173 := bstep (se 3 (by rfl) ⟨1182407, by rfl⟩ : syracuseStep 6306173 = 2364815) B2364815
theorem B2243027 : Blo 1244440 2243027 := bstep (se 1 (by rfl) ⟨1682270, by rfl⟩ : syracuseStep 2243027 = 3364541) B3364541
theorem B2800097 : Blo 1244440 2800097 := bstep (se 2 (by rfl) ⟨1050036, by rfl⟩ : syracuseStep 2800097 = 2100073) B2100073
theorem B2366023 : Blo 1244440 2366023 := bstep (se 1 (by rfl) ⟨1774517, by rfl⟩ : syracuseStep 2366023 = 3549035) B3549035
theorem B2800403 : Blo 1244440 2800403 := bstep (se 1 (by rfl) ⟨2100302, by rfl⟩ : syracuseStep 2800403 = 4200605) B4200605
theorem B3152783 : Blo 1244440 3152783 := bstep (se 1 (by rfl) ⟨2364587, by rfl⟩ : syracuseStep 3152783 = 4729175) B4729175
theorem B2800763 : Blo 1244440 2800763 := bstep (se 1 (by rfl) ⟨2100572, by rfl⟩ : syracuseStep 2800763 = 4201145) B4201145
theorem B3546301 : Blo 1244440 3546301 := bstep (se 3 (by rfl) ⟨664931, by rfl⟩ : syracuseStep 3546301 = 1329863) B1329863
theorem B1866971 : Blo 1244440 1866971 := bstep (se 1 (by rfl) ⟨1400228, by rfl⟩ : syracuseStep 1866971 = 2800457) B2800457
theorem B2800889 : Blo 1244440 2800889 := bstep (se 2 (by rfl) ⟨1050333, by rfl⟩ : syracuseStep 2800889 = 2100667) B2100667
theorem B1244447 : Blo 1244440 1244447 := bstep (se 1 (by rfl) ⟨933335, by rfl⟩ : syracuseStep 1244447 = 1866671) B1866671
theorem B1244507 : Blo 1244440 1244507 := bstep (se 1 (by rfl) ⟨933380, by rfl⟩ : syracuseStep 1244507 = 1866761) B1866761
theorem B1244527 : Blo 1244440 1244527 := bstep (se 1 (by rfl) ⟨933395, by rfl⟩ : syracuseStep 1244527 = 1866791) B1866791
theorem B4201847 : Blo 1244440 4201847 := bstep (se 1 (by rfl) ⟨3151385, by rfl⟩ : syracuseStep 4201847 = 6302771) B6302771
theorem B1867145 : Blo 1244440 1867145 := bstep (se 2 (by rfl) ⟨700179, by rfl⟩ : syracuseStep 1867145 = 1400359) B1400359
theorem B2801033 : Blo 1244440 2801033 := bstep (se 2 (by rfl) ⟨1050387, by rfl⟩ : syracuseStep 2801033 = 2100775) B2100775
theorem B3153289 : Blo 1244440 3153289 := bstep (se 2 (by rfl) ⟨1182483, by rfl⟩ : syracuseStep 3153289 = 2364967) B2364967
theorem B1244583 : Blo 1244440 1244583 := bstep (se 1 (by rfl) ⟨933437, by rfl⟩ : syracuseStep 1244583 = 1866875) B1866875
theorem B4488635 : Blo 1244440 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B3153401 : Blo 1244440 3153401 := bstep (se 2 (by rfl) ⟨1182525, by rfl⟩ : syracuseStep 3153401 = 2365051) B2365051
theorem B1244667 : Blo 1244440 1244667 := bstep (se 1 (by rfl) ⟨933500, by rfl⟩ : syracuseStep 1244667 = 1867001) B1867001
theorem B2801159 : Blo 1244440 2801159 := bstep (se 1 (by rfl) ⟨2100869, by rfl⟩ : syracuseStep 2801159 = 4201739) B4201739
theorem B1244735 : Blo 1244440 1244735 := bstep (se 1 (by rfl) ⟨933551, by rfl⟩ : syracuseStep 1244735 = 1867103) B1867103
theorem B1244743 : Blo 1244440 1244743 := bstep (se 1 (by rfl) ⟨933557, by rfl⟩ : syracuseStep 1244743 = 1867115) B1867115
theorem B8093267 : Blo 1244440 8093267 := bstep (se 1 (by rfl) ⟨6069950, by rfl⟩ : syracuseStep 8093267 = 12139901) B12139901
theorem B2662075 : Blo 1244440 2662075 := bstep (se 1 (by rfl) ⟨1996556, by rfl⟩ : syracuseStep 2662075 = 3993113) B3993113
theorem B2801339 : Blo 1244440 2801339 := bstep (se 1 (by rfl) ⟨2101004, by rfl⟩ : syracuseStep 2801339 = 4202009) B4202009
theorem B1244895 : Blo 1244440 1244895 := bstep (se 1 (by rfl) ⟨933671, by rfl⟩ : syracuseStep 1244895 = 1867343) B1867343
theorem B1867499 : Blo 1244440 1867499 := bstep (se 1 (by rfl) ⟨1400624, by rfl⟩ : syracuseStep 1867499 = 2801249) B2801249
theorem B1244975 : Blo 1244440 1244975 := bstep (se 1 (by rfl) ⟨933731, by rfl⟩ : syracuseStep 1244975 = 1867463) B1867463
theorem B6307631 : Blo 1244440 6307631 := bstep (se 1 (by rfl) ⟨4730723, by rfl⟩ : syracuseStep 6307631 = 9461447) B9461447
theorem B2801465 : Blo 1244440 2801465 := bstep (se 2 (by rfl) ⟨1050549, by rfl⟩ : syracuseStep 2801465 = 2101099) B2101099
theorem B5758793 : Blo 1244440 5758793 := bstep (se 2 (by rfl) ⟨2159547, by rfl⟩ : syracuseStep 5758793 = 4319095) B4319095
theorem B1245083 : Blo 1244440 1245083 := bstep (se 1 (by rfl) ⟨933812, by rfl⟩ : syracuseStep 1245083 = 1867625) B1867625
theorem B22716335 : Blo 1244440 22716335 := bstep (se 1 (by rfl) ⟨17037251, by rfl⟩ : syracuseStep 22716335 = 34074503) B34074503
theorem B1245135 : Blo 1244440 1245135 := bstep (se 1 (by rfl) ⟨933851, by rfl⟩ : syracuseStep 1245135 = 1867703) B1867703
theorem B1867727 : Blo 1244440 1867727 := bstep (se 1 (by rfl) ⟨1400795, by rfl⟩ : syracuseStep 1867727 = 2801591) B2801591
theorem B1245159 : Blo 1244440 1245159 := bstep (se 1 (by rfl) ⟨933869, by rfl⟩ : syracuseStep 1245159 = 1867739) B1867739
theorem B8085547 : Blo 1244440 8085547 := bstep (se 1 (by rfl) ⟨6064160, by rfl⟩ : syracuseStep 8085547 = 12128321) B12128321
theorem B20750393 : Blo 1244440 20750393 := bstep (se 2 (by rfl) ⟨7781397, by rfl⟩ : syracuseStep 20750393 = 15562795) B15562795
theorem B1245415 : Blo 1244440 1245415 := bstep (se 1 (by rfl) ⟨934061, by rfl⟩ : syracuseStep 1245415 = 1868123) B1868123
theorem B13459715 : Blo 1244440 13459715 := bstep (se 1 (by rfl) ⟨10094786, by rfl⟩ : syracuseStep 13459715 = 20189573) B20189573
theorem B2801951 : Blo 1244440 2801951 := bstep (se 1 (by rfl) ⟨2101463, by rfl⟩ : syracuseStep 2801951 = 4202927) B4202927
theorem B1868063 : Blo 1244440 1868063 := bstep (se 1 (by rfl) ⟨1401047, by rfl⟩ : syracuseStep 1868063 = 2802095) B2802095
theorem B1868087 : Blo 1244440 1868087 := bstep (se 1 (by rfl) ⟨1401065, by rfl⟩ : syracuseStep 1868087 = 2802131) B2802131
theorem B11968883 : Blo 1244440 11968883 := bstep (se 1 (by rfl) ⟨8976662, by rfl⟩ : syracuseStep 11968883 = 17953325) B17953325
theorem B1868159 : Blo 1244440 1868159 := bstep (se 1 (by rfl) ⟨1401119, by rfl⟩ : syracuseStep 1868159 = 2802239) B2802239
theorem B1245567 : Blo 1244440 1245567 := bstep (se 1 (by rfl) ⟨934175, by rfl⟩ : syracuseStep 1245567 = 1868351) B1868351
theorem B6308279 : Blo 1244440 6308279 := bstep (se 1 (by rfl) ⟨4731209, by rfl⟩ : syracuseStep 6308279 = 9462419) B9462419
theorem B1868231 : Blo 1244440 1868231 := bstep (se 1 (by rfl) ⟨1401173, by rfl⟩ : syracuseStep 1868231 = 2802347) B2802347
theorem B1401295 : Blo 1244440 1401295 := bstep (se 1 (by rfl) ⟨1050971, by rfl⟩ : syracuseStep 1401295 = 2101943) B2101943
theorem B1245647 : Blo 1244440 1245647 := bstep (se 1 (by rfl) ⟨934235, by rfl⟩ : syracuseStep 1245647 = 1868471) B1868471
theorem B5980711 : Blo 1244440 5980711 := bstep (se 1 (by rfl) ⟨4485533, by rfl⟩ : syracuseStep 5980711 = 8971067) B8971067
theorem B1245799 : Blo 1244440 1245799 := bstep (se 1 (by rfl) ⟨934349, by rfl⟩ : syracuseStep 1245799 = 1868699) B1868699
theorem B11977379 : Blo 1244440 11977379 := bstep (se 1 (by rfl) ⟨8983034, by rfl⟩ : syracuseStep 11977379 = 17966069) B17966069
theorem B3154697 : Blo 1244440 3154697 := bstep (se 2 (by rfl) ⟨1183011, by rfl⟩ : syracuseStep 3154697 = 2366023) B2366023
theorem B34104077 : Blo 1244440 34104077 := bstep (se 3 (by rfl) ⟨6394514, by rfl⟩ : syracuseStep 34104077 = 12789029) B12789029
theorem B1868585 : Blo 1244440 1868585 := bstep (se 2 (by rfl) ⟨700719, by rfl⟩ : syracuseStep 1868585 = 1401439) B1401439
theorem B6390575 : Blo 1244440 6390575 := bstep (se 1 (by rfl) ⟨4792931, by rfl⟩ : syracuseStep 6390575 = 9585863) B9585863
theorem B1868591 : Blo 1244440 1868591 := bstep (se 1 (by rfl) ⟨1401443, by rfl⟩ : syracuseStep 1868591 = 2802887) B2802887
theorem B18703163 : Blo 1244440 18703163 := bstep (se 1 (by rfl) ⟨14027372, by rfl⟩ : syracuseStep 18703163 = 28054745) B28054745
theorem B5317487 : Blo 1244440 5317487 := bstep (se 1 (by rfl) ⟨3988115, by rfl⟩ : syracuseStep 5317487 = 7976231) B7976231
theorem B1246063 : Blo 1244440 1246063 := bstep (se 1 (by rfl) ⟨934547, by rfl⟩ : syracuseStep 1246063 = 1869095) B1869095
theorem B6308765 : Blo 1244440 6308765 := bstep (se 3 (by rfl) ⟨1182893, by rfl⟩ : syracuseStep 6308765 = 2365787) B2365787
theorem B2802599 : Blo 1244440 2802599 := bstep (se 1 (by rfl) ⟨2101949, by rfl⟩ : syracuseStep 2802599 = 4203899) B4203899
theorem B1868711 : Blo 1244440 1868711 := bstep (se 1 (by rfl) ⟨1401533, by rfl⟩ : syracuseStep 1868711 = 2803067) B2803067
theorem B1246119 : Blo 1244440 1246119 := bstep (se 1 (by rfl) ⟨934589, by rfl⟩ : syracuseStep 1246119 = 1869179) B1869179
theorem B1868795 : Blo 1244440 1868795 := bstep (se 1 (by rfl) ⟨1401596, by rfl⟩ : syracuseStep 1868795 = 2803193) B2803193
theorem B1246203 : Blo 1244440 1246203 := bstep (se 1 (by rfl) ⟨934652, by rfl⟩ : syracuseStep 1246203 = 1869305) B1869305
theorem B1868855 : Blo 1244440 1868855 := bstep (se 1 (by rfl) ⟨1401641, by rfl⟩ : syracuseStep 1868855 = 2803283) B2803283
theorem B1246271 : Blo 1244440 1246271 := bstep (se 1 (by rfl) ⟨934703, by rfl⟩ : syracuseStep 1246271 = 1869407) B1869407
theorem B11969693 : Blo 1244440 11969693 := bstep (se 3 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 11969693 = 4488635) B4488635
theorem B1868975 : Blo 1244440 1868975 := bstep (se 1 (by rfl) ⟨1401731, by rfl⟩ : syracuseStep 1868975 = 2803463) B2803463
theorem B1246415 : Blo 1244440 1246415 := bstep (se 1 (by rfl) ⟨934811, by rfl⟩ : syracuseStep 1246415 = 1869623) B1869623
theorem B15959429 : Blo 1244440 15959429 := bstep (se 4 (by rfl) ⟨1496196, by rfl⟩ : syracuseStep 15959429 = 2992393) B2992393
theorem B17958277 : Blo 1244440 17958277 := bstep (se 4 (by rfl) ⟨1683588, by rfl⟩ : syracuseStep 17958277 = 3367177) B3367177
theorem B9455129 : Blo 1244440 9455129 := bstep (se 2 (by rfl) ⟨3545673, by rfl⟩ : syracuseStep 9455129 = 7091347) B7091347
theorem B1869383 : Blo 1244440 1869383 := bstep (se 1 (by rfl) ⟨1402037, by rfl⟩ : syracuseStep 1869383 = 2804075) B2804075
theorem B4728401 : Blo 1244440 4728401 := bstep (se 2 (by rfl) ⟨1773150, by rfl⟩ : syracuseStep 4728401 = 3546301) B3546301
theorem B4204115 : Blo 1244440 4204115 := bstep (se 1 (by rfl) ⟨3153086, by rfl⟩ : syracuseStep 4204115 = 6306173) B6306173
theorem B1869479 : Blo 1244440 1869479 := bstep (se 1 (by rfl) ⟨1402109, by rfl⟩ : syracuseStep 1869479 = 2804219) B2804219
theorem B1869563 : Blo 1244440 1869563 := bstep (se 1 (by rfl) ⟨1402172, by rfl⟩ : syracuseStep 1869563 = 2804345) B2804345
theorem B1869599 : Blo 1244440 1869599 := bstep (se 1 (by rfl) ⟨1402199, by rfl⟩ : syracuseStep 1869599 = 2804399) B2804399
theorem B14387005 : Blo 1244440 14387005 := bstep (se 3 (by rfl) ⟨2697563, by rfl⟩ : syracuseStep 14387005 = 5395127) B5395127
theorem B2803535 : Blo 1244440 2803535 := bstep (se 1 (by rfl) ⟨2102651, by rfl⟩ : syracuseStep 2803535 = 4205303) B4205303
theorem B1869647 : Blo 1244440 1869647 := bstep (se 1 (by rfl) ⟨1402235, by rfl⟩ : syracuseStep 1869647 = 2804471) B2804471
theorem B4204385 : Blo 1244440 4204385 := bstep (se 2 (by rfl) ⟨1576644, by rfl⟩ : syracuseStep 4204385 = 3153289) B3153289
theorem B2803553 : Blo 1244440 2803553 := bstep (se 2 (by rfl) ⟨1051332, by rfl⟩ : syracuseStep 2803553 = 2102665) B2102665
theorem B3549433 : Blo 1244440 3549433 := bstep (se 2 (by rfl) ⟨1331037, by rfl⟩ : syracuseStep 3549433 = 2662075) B2662075
theorem B2804129 : Blo 1244440 2804129 := bstep (se 2 (by rfl) ⟨1051548, by rfl⟩ : syracuseStep 2804129 = 2103097) B2103097
theorem B4205087 : Blo 1244440 4205087 := bstep (se 1 (by rfl) ⟨3153815, by rfl⟩ : syracuseStep 4205087 = 6307631) B6307631
theorem B2804255 : Blo 1244440 2804255 := bstep (se 1 (by rfl) ⟨2103191, by rfl⟩ : syracuseStep 2804255 = 4206383) B4206383
theorem B2100127 : Blo 1244440 2100127 := bstep (se 1 (by rfl) ⟨1575095, by rfl⟩ : syracuseStep 2100127 = 3150191) B3150191
theorem B8088875 : Blo 1244440 8088875 := bstep (se 1 (by rfl) ⟨6066656, by rfl⟩ : syracuseStep 8088875 = 12133313) B12133313
theorem B2100559 : Blo 1244440 2100559 := bstep (se 1 (by rfl) ⟨1575419, by rfl⟩ : syracuseStep 2100559 = 3150839) B3150839
theorem B7982459 : Blo 1244440 7982459 := bstep (se 1 (by rfl) ⟨5986844, by rfl⟩ : syracuseStep 7982459 = 11973689) B11973689
theorem B2100647 : Blo 1244440 2100647 := bstep (se 1 (by rfl) ⟨1575485, by rfl⟩ : syracuseStep 2100647 = 3150971) B3150971
theorem B1773031 : Blo 1244440 1773031 := bstep (se 1 (by rfl) ⟨1329773, by rfl⟩ : syracuseStep 1773031 = 2659547) B2659547
theorem B2362871 : Blo 1244440 2362871 := bstep (se 1 (by rfl) ⟨1772153, by rfl⟩ : syracuseStep 2362871 = 3544307) B3544307
theorem B4730359 : Blo 1244440 4730359 := bstep (se 1 (by rfl) ⟨3547769, by rfl⟩ : syracuseStep 4730359 = 7095539) B7095539
theorem B2657855 : Blo 1244440 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B2100809 : Blo 1244440 2100809 := bstep (se 2 (by rfl) ⟨787803, by rfl⟩ : syracuseStep 2100809 = 1575607) B1575607
theorem B9580193 : Blo 1244440 9580193 := bstep (se 2 (by rfl) ⟨3592572, by rfl⟩ : syracuseStep 9580193 = 7185145) B7185145
theorem B7982995 : Blo 1244440 7982995 := bstep (se 1 (by rfl) ⟨5987246, by rfl⟩ : syracuseStep 7982995 = 11974493) B11974493
theorem B4206491 : Blo 1244440 4206491 := bstep (se 1 (by rfl) ⟨3154868, by rfl⟩ : syracuseStep 4206491 = 6309737) B6309737
theorem B4730831 : Blo 1244440 4730831 := bstep (se 1 (by rfl) ⟨3548123, by rfl⟩ : syracuseStep 4730831 = 7096247) B7096247
theorem B7090163 : Blo 1244440 7090163 := bstep (se 1 (by rfl) ⟨5317622, by rfl⟩ : syracuseStep 7090163 = 10635245) B10635245
theorem B17961047 : Blo 1244440 17961047 := bstep (se 1 (by rfl) ⟨13470785, by rfl⟩ : syracuseStep 17961047 = 26941571) B26941571
theorem B1495351 : Blo 1244440 1495351 := bstep (se 1 (by rfl) ⟨1121513, by rfl⟩ : syracuseStep 1495351 = 2243027) B2243027
theorem B6304067 : Blo 1244440 6304067 := bstep (se 1 (by rfl) ⟨4728050, by rfl⟩ : syracuseStep 6304067 = 9456101) B9456101
theorem B26915273 : Blo 1244440 26915273 := bstep (se 2 (by rfl) ⟨10093227, by rfl⟩ : syracuseStep 26915273 = 20186455) B20186455
theorem B2363897 : Blo 1244440 2363897 := bstep (se 2 (by rfl) ⟨886461, by rfl⟩ : syracuseStep 2363897 = 1772923) B1772923
theorem B2101855 : Blo 1244440 2101855 := bstep (se 1 (by rfl) ⟨1576391, by rfl⟩ : syracuseStep 2101855 = 3152783) B3152783
theorem B10105559 : Blo 1244440 10105559 := bstep (se 1 (by rfl) ⟨7579169, by rfl⟩ : syracuseStep 10105559 = 15158339) B15158339
theorem B7574401 : Blo 1244440 7574401 := bstep (se 2 (by rfl) ⟨2840400, by rfl⟩ : syracuseStep 7574401 = 5680801) B5680801
theorem B2102267 : Blo 1244440 2102267 := bstep (se 1 (by rfl) ⟨1576700, by rfl⟩ : syracuseStep 2102267 = 3153401) B3153401
theorem B30282797 : Blo 1244440 30282797 := bstep (se 3 (by rfl) ⟨5678024, by rfl⟩ : syracuseStep 30282797 = 11356049) B11356049
theorem B5395511 : Blo 1244440 5395511 := bstep (se 1 (by rfl) ⟨4046633, by rfl⟩ : syracuseStep 5395511 = 8093267) B8093267
theorem B60576893 : Blo 1244440 60576893 := bstep (se 3 (by rfl) ⟨11358167, by rfl⟩ : syracuseStep 60576893 = 22716335) B22716335
theorem B3839195 : Blo 1244440 3839195 := bstep (se 1 (by rfl) ⟨2879396, by rfl⟩ : syracuseStep 3839195 = 5758793) B5758793
theorem B35018077 : Blo 1244440 35018077 := bstep (se 3 (by rfl) ⟨6565889, by rfl⟩ : syracuseStep 35018077 = 13131779) B13131779
theorem B30307709 : Blo 1244440 30307709 := bstep (se 3 (by rfl) ⟨5682695, by rfl⟩ : syracuseStep 30307709 = 11365391) B11365391
theorem B2102699 : Blo 1244440 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B26949185 : Blo 1244440 26949185 := bstep (se 2 (by rfl) ⟨10105944, by rfl⟩ : syracuseStep 26949185 = 20211889) B20211889
theorem B10106531 : Blo 1244440 10106531 := bstep (se 1 (by rfl) ⟨7579898, by rfl⟩ : syracuseStep 10106531 = 15159797) B15159797
theorem B4200119 : Blo 1244440 4200119 := bstep (se 1 (by rfl) ⟨3150089, by rfl⟩ : syracuseStep 4200119 = 6300179) B6300179
theorem B3413755 : Blo 1244440 3413755 := bstep (se 1 (by rfl) ⟨2560316, by rfl⟩ : syracuseStep 3413755 = 5120633) B5120633
theorem B1496827 : Blo 1244440 1496827 := bstep (se 1 (by rfl) ⟨1122620, by rfl⟩ : syracuseStep 1496827 = 2245241) B2245241
theorem B2103239 : Blo 1244440 2103239 := bstep (se 1 (by rfl) ⟨1577429, by rfl⟩ : syracuseStep 2103239 = 3154859) B3154859
theorem B3151831 : Blo 1244440 3151831 := bstep (se 1 (by rfl) ⟨2363873, by rfl⟩ : syracuseStep 3151831 = 4727747) B4727747
theorem B22714433 : Blo 1244440 22714433 := bstep (se 2 (by rfl) ⟨8517912, by rfl⟩ : syracuseStep 22714433 = 17035825) B17035825
theorem B3987539 : Blo 1244440 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B2660435 : Blo 1244440 2660435 := bstep (se 1 (by rfl) ⟨1995326, by rfl⟩ : syracuseStep 2660435 = 3990653) B3990653
theorem B3987551 : Blo 1244440 3987551 := bstep (se 1 (by rfl) ⟨2990663, by rfl⟩ : syracuseStep 3987551 = 5981327) B5981327
theorem B3152105 : Blo 1244440 3152105 := bstep (se 2 (by rfl) ⟨1182039, by rfl⟩ : syracuseStep 3152105 = 2364079) B2364079
theorem B3152135 : Blo 1244440 3152135 := bstep (se 1 (by rfl) ⟨2364101, by rfl⟩ : syracuseStep 3152135 = 4728203) B4728203
theorem B14195087 : Blo 1244440 14195087 := bstep (se 1 (by rfl) ⟨10646315, by rfl⟩ : syracuseStep 14195087 = 21292631) B21292631
theorem B2800475 : Blo 1244440 2800475 := bstep (se 1 (by rfl) ⟨2100356, by rfl⟩ : syracuseStep 2800475 = 4200713) B4200713
theorem B4201307 : Blo 1244440 4201307 := bstep (se 1 (by rfl) ⟨3150980, by rfl⟩ : syracuseStep 4201307 = 6301961) B6301961
theorem B3545947 : Blo 1244440 3545947 := bstep (se 1 (by rfl) ⟨2659460, by rfl⟩ : syracuseStep 3545947 = 5318921) B5318921
theorem B1866731 : Blo 1244440 1866731 := bstep (se 1 (by rfl) ⟨1400048, by rfl⟩ : syracuseStep 1866731 = 2800097) B2800097
theorem B1866935 : Blo 1244440 1866935 := bstep (se 1 (by rfl) ⟨1400201, by rfl⟩ : syracuseStep 1866935 = 2800403) B2800403
theorem B3595529 : Blo 1244440 3595529 := bstep (se 2 (by rfl) ⟨1348323, by rfl⟩ : syracuseStep 3595529 = 2696647) B2696647
theorem B1400143 : Blo 1244440 1400143 := bstep (se 1 (by rfl) ⟨1050107, by rfl⟩ : syracuseStep 1400143 = 2100215) B2100215
theorem B3890543 : Blo 1244440 3890543 := bstep (se 1 (by rfl) ⟨2917907, by rfl⟩ : syracuseStep 3890543 = 5835815) B5835815
theorem B1867175 : Blo 1244440 1867175 := bstep (se 1 (by rfl) ⟨1400381, by rfl⟩ : syracuseStep 1867175 = 2800763) B2800763
theorem B1244647 : Blo 1244440 1244647 := bstep (se 1 (by rfl) ⟨933485, by rfl⟩ : syracuseStep 1244647 = 1866971) B1866971
theorem B1867259 : Blo 1244440 1867259 := bstep (se 1 (by rfl) ⟨1400444, by rfl⟩ : syracuseStep 1867259 = 2800889) B2800889
theorem B2801231 : Blo 1244440 2801231 := bstep (se 1 (by rfl) ⟨2100923, by rfl⟩ : syracuseStep 2801231 = 4201847) B4201847
theorem B4202063 : Blo 1244440 4202063 := bstep (se 1 (by rfl) ⟨3151547, by rfl⟩ : syracuseStep 4202063 = 6303095) B6303095
theorem B1244763 : Blo 1244440 1244763 := bstep (se 1 (by rfl) ⟨933572, by rfl⟩ : syracuseStep 1244763 = 1867145) B1867145
theorem B1867355 : Blo 1244440 1867355 := bstep (se 1 (by rfl) ⟨1400516, by rfl⟩ : syracuseStep 1867355 = 2801033) B2801033
theorem B3546767 : Blo 1244440 3546767 := bstep (se 1 (by rfl) ⟨2660075, by rfl⟩ : syracuseStep 3546767 = 5320151) B5320151
theorem B1867439 : Blo 1244440 1867439 := bstep (se 1 (by rfl) ⟨1400579, by rfl⟩ : syracuseStep 1867439 = 2801159) B2801159
theorem B3989179 : Blo 1244440 3989179 := bstep (se 1 (by rfl) ⟨2991884, by rfl⟩ : syracuseStep 3989179 = 5983769) B5983769
theorem B4202171 : Blo 1244440 4202171 := bstep (se 1 (by rfl) ⟨3151628, by rfl⟩ : syracuseStep 4202171 = 6303257) B6303257
theorem B1892135 : Blo 1244440 1892135 := bstep (se 1 (by rfl) ⟨1419101, by rfl⟩ : syracuseStep 1892135 = 2838203) B2838203
theorem B1867559 : Blo 1244440 1867559 := bstep (se 1 (by rfl) ⟨1400669, by rfl⟩ : syracuseStep 1867559 = 2801339) B2801339
theorem B1244999 : Blo 1244440 1244999 := bstep (se 1 (by rfl) ⟨933749, by rfl⟩ : syracuseStep 1244999 = 1867499) B1867499
theorem B1400647 : Blo 1244440 1400647 := bstep (se 1 (by rfl) ⟨1050485, by rfl⟩ : syracuseStep 1400647 = 2100971) B2100971
theorem B1867643 : Blo 1244440 1867643 := bstep (se 1 (by rfl) ⟨1400732, by rfl⟩ : syracuseStep 1867643 = 2801465) B2801465
theorem B3784573 : Blo 1244440 3784573 := bstep (se 3 (by rfl) ⟨709607, by rfl⟩ : syracuseStep 3784573 = 1419215) B1419215
theorem B1245151 : Blo 1244440 1245151 := bstep (se 1 (by rfl) ⟨933863, by rfl⟩ : syracuseStep 1245151 = 1867727) B1867727
theorem B1867967 : Blo 1244440 1867967 := bstep (se 1 (by rfl) ⟨1400975, by rfl⟩ : syracuseStep 1867967 = 2801951) B2801951
theorem B1245375 : Blo 1244440 1245375 := bstep (se 1 (by rfl) ⟨934031, by rfl⟩ : syracuseStep 1245375 = 1868063) B1868063
theorem B1245391 : Blo 1244440 1245391 := bstep (se 1 (by rfl) ⟨934043, by rfl⟩ : syracuseStep 1245391 = 1868087) B1868087
theorem B4726775 : Blo 1244440 4726775 := bstep (se 1 (by rfl) ⟨3545081, by rfl⟩ : syracuseStep 4726775 = 7090163) B7090163
theorem B4202711 : Blo 1244440 4202711 := bstep (se 1 (by rfl) ⟨3152033, by rfl⟩ : syracuseStep 4202711 = 6304067) B6304067
theorem B43122917 : Blo 1244440 43122917 := bstep (se 4 (by rfl) ⟨4042773, by rfl⟩ : syracuseStep 43122917 = 8085547) B8085547
theorem B7979255 : Blo 1244440 7979255 := bstep (se 1 (by rfl) ⟨5984441, by rfl⟩ : syracuseStep 7979255 = 11968883) B11968883
theorem B1245439 : Blo 1244440 1245439 := bstep (se 1 (by rfl) ⟨934079, by rfl⟩ : syracuseStep 1245439 = 1868159) B1868159
theorem B1245487 : Blo 1244440 1245487 := bstep (se 1 (by rfl) ⟨934115, by rfl⟩ : syracuseStep 1245487 = 1868231) B1868231
theorem B4260383 : Blo 1244440 4260383 := bstep (se 1 (by rfl) ⟨3195287, by rfl⟩ : syracuseStep 4260383 = 6390575) B6390575
theorem B1245723 : Blo 1244440 1245723 := bstep (se 1 (by rfl) ⟨934292, by rfl⟩ : syracuseStep 1245723 = 1868585) B1868585
theorem B1245727 : Blo 1244440 1245727 := bstep (se 1 (by rfl) ⟨934295, by rfl⟩ : syracuseStep 1245727 = 1868591) B1868591
theorem B1868393 : Blo 1244440 1868393 := bstep (se 2 (by rfl) ⟨700647, by rfl⟩ : syracuseStep 1868393 = 1401295) B1401295
theorem B1868399 : Blo 1244440 1868399 := bstep (se 1 (by rfl) ⟨1401299, by rfl⟩ : syracuseStep 1868399 = 2802599) B2802599
theorem B1245807 : Blo 1244440 1245807 := bstep (se 1 (by rfl) ⟨934355, by rfl⟩ : syracuseStep 1245807 = 1868711) B1868711
theorem B1401511 : Blo 1244440 1401511 := bstep (se 1 (by rfl) ⟨1051133, by rfl⟩ : syracuseStep 1401511 = 2102267) B2102267
theorem B1245863 : Blo 1244440 1245863 := bstep (se 1 (by rfl) ⟨934397, by rfl⟩ : syracuseStep 1245863 = 1868795) B1868795
theorem B1245903 : Blo 1244440 1245903 := bstep (se 1 (by rfl) ⟨934427, by rfl⟩ : syracuseStep 1245903 = 1868855) B1868855
theorem B3597007 : Blo 1244440 3597007 := bstep (se 1 (by rfl) ⟨2697755, by rfl⟩ : syracuseStep 3597007 = 5395511) B5395511
theorem B7979795 : Blo 1244440 7979795 := bstep (se 1 (by rfl) ⟨5984846, by rfl⟩ : syracuseStep 7979795 = 11969693) B11969693
theorem B1245983 : Blo 1244440 1245983 := bstep (se 1 (by rfl) ⟨934487, by rfl⟩ : syracuseStep 1245983 = 1868975) B1868975
theorem B2802473 : Blo 1244440 2802473 := bstep (se 2 (by rfl) ⟨1050927, by rfl⟩ : syracuseStep 2802473 = 2101855) B2101855
theorem B1401799 : Blo 1244440 1401799 := bstep (se 1 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 1401799 = 2102699) B2102699
theorem B17966123 : Blo 1244440 17966123 := bstep (se 1 (by rfl) ⟨13474592, by rfl⟩ : syracuseStep 17966123 = 26949185) B26949185
theorem B1246255 : Blo 1244440 1246255 := bstep (se 1 (by rfl) ⟨934691, by rfl⟩ : syracuseStep 1246255 = 1869383) B1869383
theorem B2802743 : Blo 1244440 2802743 := bstep (se 1 (by rfl) ⟨2102057, by rfl⟩ : syracuseStep 2802743 = 4204115) B4204115
theorem B1246319 : Blo 1244440 1246319 := bstep (se 1 (by rfl) ⟨934739, by rfl⟩ : syracuseStep 1246319 = 1869479) B1869479
theorem B4727929 : Blo 1244440 4727929 := bstep (se 2 (by rfl) ⟨1772973, by rfl⟩ : syracuseStep 4727929 = 3545947) B3545947
theorem B1246375 : Blo 1244440 1246375 := bstep (se 1 (by rfl) ⟨934781, by rfl⟩ : syracuseStep 1246375 = 1869563) B1869563
theorem B1246399 : Blo 1244440 1246399 := bstep (se 1 (by rfl) ⟨934799, by rfl⟩ : syracuseStep 1246399 = 1869599) B1869599
theorem B1869023 : Blo 1244440 1869023 := bstep (se 1 (by rfl) ⟨1401767, by rfl⟩ : syracuseStep 1869023 = 2803535) B2803535
theorem B1246431 : Blo 1244440 1246431 := bstep (se 1 (by rfl) ⟨934823, by rfl⟩ : syracuseStep 1246431 = 1869647) B1869647
theorem B2802923 : Blo 1244440 2802923 := bstep (se 1 (by rfl) ⟨2102192, by rfl⟩ : syracuseStep 2802923 = 4204385) B4204385
theorem B1869035 : Blo 1244440 1869035 := bstep (se 1 (by rfl) ⟨1401776, by rfl⟩ : syracuseStep 1869035 = 2803553) B2803553
theorem B1402159 : Blo 1244440 1402159 := bstep (se 1 (by rfl) ⟨1051619, by rfl⟩ : syracuseStep 1402159 = 2103239) B2103239
theorem B6300989 : Blo 1244440 6300989 := bstep (se 3 (by rfl) ⟨1181435, by rfl⟩ : syracuseStep 6300989 = 2362871) B2362871
theorem B9463391 : Blo 1244440 9463391 := bstep (se 1 (by rfl) ⟨7097543, by rfl⟩ : syracuseStep 9463391 = 14195087) B14195087
theorem B1869419 : Blo 1244440 1869419 := bstep (se 1 (by rfl) ⟨1402064, by rfl⟩ : syracuseStep 1869419 = 2804129) B2804129
theorem B2803391 : Blo 1244440 2803391 := bstep (se 1 (by rfl) ⟨2102543, by rfl⟩ : syracuseStep 2803391 = 4205087) B4205087
theorem B1869503 : Blo 1244440 1869503 := bstep (se 1 (by rfl) ⟨1402127, by rfl⟩ : syracuseStep 1869503 = 2804255) B2804255
theorem B49875101 : Blo 1244440 49875101 := bstep (se 3 (by rfl) ⟨9351581, by rfl⟩ : syracuseStep 49875101 = 18703163) B18703163
theorem B5392583 : Blo 1244440 5392583 := bstep (se 1 (by rfl) ⟨4044437, by rfl⟩ : syracuseStep 5392583 = 8088875) B8088875
theorem B5318905 : Blo 1244440 5318905 := bstep (se 2 (by rfl) ⟨1994589, by rfl⟩ : syracuseStep 5318905 = 3989179) B3989179
theorem B1771903 : Blo 1244440 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B10643993 : Blo 1244440 10643993 := bstep (se 2 (by rfl) ⟨3991497, by rfl⟩ : syracuseStep 10643993 = 7982995) B7982995
theorem B2804327 : Blo 1244440 2804327 := bstep (se 1 (by rfl) ⟨2103245, by rfl⟩ : syracuseStep 2804327 = 4206491) B4206491
theorem B8973143 : Blo 1244440 8973143 := bstep (se 1 (by rfl) ⟨6729857, by rfl⟩ : syracuseStep 8973143 = 13459715) B13459715
theorem B4205519 : Blo 1244440 4205519 := bstep (se 1 (by rfl) ⟨3154139, by rfl⟩ : syracuseStep 4205519 = 6308279) B6308279
theorem B17943515 : Blo 1244440 17943515 := bstep (se 1 (by rfl) ⟨13457636, by rfl⟩ : syracuseStep 17943515 = 26915273) B26915273
theorem B1575931 : Blo 1244440 1575931 := bstep (se 1 (by rfl) ⟨1181948, by rfl⟩ : syracuseStep 1575931 = 2363897) B2363897
theorem B6737039 : Blo 1244440 6737039 := bstep (se 1 (by rfl) ⟨5052779, by rfl⟩ : syracuseStep 6737039 = 10105559) B10105559
theorem B22736051 : Blo 1244440 22736051 := bstep (se 1 (by rfl) ⟨17052038, by rfl⟩ : syracuseStep 22736051 = 34104077) B34104077
theorem B4205843 : Blo 1244440 4205843 := bstep (se 1 (by rfl) ⟨3154382, by rfl⟩ : syracuseStep 4205843 = 6308765) B6308765
theorem B20188531 : Blo 1244440 20188531 := bstep (se 1 (by rfl) ⟨15141398, by rfl⟩ : syracuseStep 20188531 = 30282797) B30282797
theorem B7974281 : Blo 1244440 7974281 := bstep (se 2 (by rfl) ⟨2990355, by rfl⟩ : syracuseStep 7974281 = 5980711) B5980711
theorem B20205139 : Blo 1244440 20205139 := bstep (se 1 (by rfl) ⟨15153854, by rfl⟩ : syracuseStep 20205139 = 30307709) B30307709
theorem B6303419 : Blo 1244440 6303419 := bstep (se 1 (by rfl) ⟨4727564, by rfl⟩ : syracuseStep 6303419 = 9455129) B9455129
theorem B6737687 : Blo 1244440 6737687 := bstep (se 1 (by rfl) ⟨5053265, by rfl⟩ : syracuseStep 6737687 = 10106531) B10106531
theorem B18206693 : Blo 1244440 18206693 := bstep (se 4 (by rfl) ⟨1706877, by rfl⟩ : syracuseStep 18206693 = 3413755) B3413755
theorem B15142955 : Blo 1244440 15142955 := bstep (se 1 (by rfl) ⟨11357216, by rfl⟩ : syracuseStep 15142955 = 22714433) B22714433
theorem B2658359 : Blo 1244440 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B1773623 : Blo 1244440 1773623 := bstep (se 1 (by rfl) ⟨1330217, by rfl⟩ : syracuseStep 1773623 = 2660435) B2660435
theorem B2658367 : Blo 1244440 2658367 := bstep (se 1 (by rfl) ⟨1993775, by rfl⟩ : syracuseStep 2658367 = 3987551) B3987551
theorem B2101403 : Blo 1244440 2101403 := bstep (se 1 (by rfl) ⟨1576052, by rfl⟩ : syracuseStep 2101403 = 3152105) B3152105
theorem B2101423 : Blo 1244440 2101423 := bstep (se 1 (by rfl) ⟨1576067, by rfl⟩ : syracuseStep 2101423 = 3152135) B3152135
theorem B7975205 : Blo 1244440 7975205 := bstep (se 4 (by rfl) ⟨747675, by rfl⟩ : syracuseStep 7975205 = 1495351) B1495351
theorem B9458045 : Blo 1244440 9458045 := bstep (se 3 (by rfl) ⟨1773383, by rfl⟩ : syracuseStep 9458045 = 3546767) B3546767
theorem B46690769 : Blo 1244440 46690769 := bstep (se 2 (by rfl) ⟨17509038, by rfl⟩ : syracuseStep 46690769 = 35018077) B35018077
theorem B2364041 : Blo 1244440 2364041 := bstep (se 2 (by rfl) ⟨886515, by rfl⟩ : syracuseStep 2364041 = 1773031) B1773031
theorem B2397019 : Blo 1244440 2397019 := bstep (se 1 (by rfl) ⟨1797764, by rfl⟩ : syracuseStep 2397019 = 3595529) B3595529
theorem B5321639 : Blo 1244440 5321639 := bstep (se 1 (by rfl) ⟨3991229, by rfl⟩ : syracuseStep 5321639 = 7982459) B7982459
theorem B1995769 : Blo 1244440 1995769 := bstep (se 2 (by rfl) ⟨748413, by rfl⟩ : syracuseStep 1995769 = 1496827) B1496827
theorem B19182673 : Blo 1244440 19182673 := bstep (se 2 (by rfl) ⟨7193502, by rfl⟩ : syracuseStep 19182673 = 14387005) B14387005
theorem B6386795 : Blo 1244440 6386795 := bstep (se 1 (by rfl) ⟨4790096, by rfl⟩ : syracuseStep 6386795 = 9580193) B9580193
theorem B13833595 : Blo 1244440 13833595 := bstep (se 1 (by rfl) ⟨10375196, by rfl⟩ : syracuseStep 13833595 = 20750393) B20750393
theorem B11974031 : Blo 1244440 11974031 := bstep (se 1 (by rfl) ⟨8980523, by rfl⟩ : syracuseStep 11974031 = 17961047) B17961047
theorem B4732577 : Blo 1244440 4732577 := bstep (se 2 (by rfl) ⟨1774716, by rfl⟩ : syracuseStep 4732577 = 3549433) B3549433
theorem B7984919 : Blo 1244440 7984919 := bstep (se 1 (by rfl) ⟨5988689, by rfl⟩ : syracuseStep 7984919 = 11977379) B11977379
theorem B2103131 : Blo 1244440 2103131 := bstep (se 1 (by rfl) ⟨1577348, by rfl⟩ : syracuseStep 2103131 = 3154697) B3154697
theorem B10237853 : Blo 1244440 10237853 := bstep (se 3 (by rfl) ⟨1919597, by rfl⟩ : syracuseStep 10237853 = 3839195) B3839195
theorem B3544991 : Blo 1244440 3544991 := bstep (se 1 (by rfl) ⟨2658743, by rfl⟩ : syracuseStep 3544991 = 5317487) B5317487
theorem B40384595 : Blo 1244440 40384595 := bstep (se 1 (by rfl) ⟨30288446, by rfl⟩ : syracuseStep 40384595 = 60576893) B60576893
theorem B10639619 : Blo 1244440 10639619 := bstep (se 1 (by rfl) ⟨7979714, by rfl⟩ : syracuseStep 10639619 = 15959429) B15959429
theorem B3152267 : Blo 1244440 3152267 := bstep (se 1 (by rfl) ⟨2364200, by rfl⟩ : syracuseStep 3152267 = 4728401) B4728401
theorem B2800079 : Blo 1244440 2800079 := bstep (se 1 (by rfl) ⟨2100059, by rfl⟩ : syracuseStep 2800079 = 4200119) B4200119
theorem B41499125 : Blo 1244440 41499125 := bstep (se 5 (by rfl) ⟨1945271, by rfl⟩ : syracuseStep 41499125 = 3890543) B3890543
theorem B10099201 : Blo 1244440 10099201 := bstep (se 2 (by rfl) ⟨3787200, by rfl⟩ : syracuseStep 10099201 = 7574401) B7574401
theorem B2800169 : Blo 1244440 2800169 := bstep (se 2 (by rfl) ⟨1050063, by rfl⟩ : syracuseStep 2800169 = 2100127) B2100127
theorem B1866857 : Blo 1244440 1866857 := bstep (se 2 (by rfl) ⟨700071, by rfl⟩ : syracuseStep 1866857 = 1400143) B1400143
theorem B2800745 : Blo 1244440 2800745 := bstep (se 2 (by rfl) ⟨1050279, by rfl⟩ : syracuseStep 2800745 = 2100559) B2100559
theorem B23944369 : Blo 1244440 23944369 := bstep (se 2 (by rfl) ⟨8979138, by rfl⟩ : syracuseStep 23944369 = 17958277) B17958277
theorem B1866983 : Blo 1244440 1866983 := bstep (se 1 (by rfl) ⟨1400237, by rfl⟩ : syracuseStep 1866983 = 2800475) B2800475
theorem B2800871 : Blo 1244440 2800871 := bstep (se 1 (by rfl) ⟨2100653, by rfl⟩ : syracuseStep 2800871 = 4201307) B4201307
theorem B1244487 : Blo 1244440 1244487 := bstep (se 1 (by rfl) ⟨933365, by rfl⟩ : syracuseStep 1244487 = 1866731) B1866731
theorem B6307145 : Blo 1244440 6307145 := bstep (se 2 (by rfl) ⟨2365179, by rfl⟩ : syracuseStep 6307145 = 4730359) B4730359
theorem B1244623 : Blo 1244440 1244623 := bstep (se 1 (by rfl) ⟨933467, by rfl⟩ : syracuseStep 1244623 = 1866935) B1866935
theorem B1244783 : Blo 1244440 1244783 := bstep (se 1 (by rfl) ⟨933587, by rfl⟩ : syracuseStep 1244783 = 1867175) B1867175
theorem B1400431 : Blo 1244440 1400431 := bstep (se 1 (by rfl) ⟨1050323, by rfl⟩ : syracuseStep 1400431 = 2100647) B2100647
theorem B1244839 : Blo 1244440 1244839 := bstep (se 1 (by rfl) ⟨933629, by rfl⟩ : syracuseStep 1244839 = 1867259) B1867259
theorem B1400539 : Blo 1244440 1400539 := bstep (se 1 (by rfl) ⟨1050404, by rfl⟩ : syracuseStep 1400539 = 2100809) B2100809
theorem B1867487 : Blo 1244440 1867487 := bstep (se 1 (by rfl) ⟨1400615, by rfl⟩ : syracuseStep 1867487 = 2801231) B2801231
theorem B2801375 : Blo 1244440 2801375 := bstep (se 1 (by rfl) ⟨2101031, by rfl⟩ : syracuseStep 2801375 = 4202063) B4202063
theorem B1244903 : Blo 1244440 1244903 := bstep (se 1 (by rfl) ⟨933677, by rfl⟩ : syracuseStep 1244903 = 1867355) B1867355
theorem B1867529 : Blo 1244440 1867529 := bstep (se 2 (by rfl) ⟨700323, by rfl⟩ : syracuseStep 1867529 = 1400647) B1400647
theorem B1244959 : Blo 1244440 1244959 := bstep (se 1 (by rfl) ⟨933719, by rfl⟩ : syracuseStep 1244959 = 1867439) B1867439
theorem B2801447 : Blo 1244440 2801447 := bstep (se 1 (by rfl) ⟨2101085, by rfl⟩ : syracuseStep 2801447 = 4202171) B4202171
theorem B5046097 : Blo 1244440 5046097 := bstep (se 2 (by rfl) ⟨1892286, by rfl⟩ : syracuseStep 5046097 = 3784573) B3784573
theorem B1261423 : Blo 1244440 1261423 := bstep (se 1 (by rfl) ⟨946067, by rfl⟩ : syracuseStep 1261423 = 1892135) B1892135
theorem B1245039 : Blo 1244440 1245039 := bstep (se 1 (by rfl) ⟨933779, by rfl⟩ : syracuseStep 1245039 = 1867559) B1867559
theorem B1245095 : Blo 1244440 1245095 := bstep (se 1 (by rfl) ⟨933821, by rfl⟩ : syracuseStep 1245095 = 1867643) B1867643
theorem B4202441 : Blo 1244440 4202441 := bstep (se 2 (by rfl) ⟨1575915, by rfl⟩ : syracuseStep 4202441 = 3151831) B3151831
theorem B3153887 : Blo 1244440 3153887 := bstep (se 1 (by rfl) ⟨2365415, by rfl⟩ : syracuseStep 3153887 = 4730831) B4730831
theorem B1400935 : Blo 1244440 1400935 := bstep (se 1 (by rfl) ⟨1050701, by rfl⟩ : syracuseStep 1400935 = 2101403) B2101403
theorem B1245311 : Blo 1244440 1245311 := bstep (se 1 (by rfl) ⟨933983, by rfl⟩ : syracuseStep 1245311 = 1867967) B1867967
theorem B2801807 : Blo 1244440 2801807 := bstep (se 1 (by rfl) ⟨2101355, by rfl⟩ : syracuseStep 2801807 = 4202711) B4202711
theorem B5316803 : Blo 1244440 5316803 := bstep (se 1 (by rfl) ⟨3987602, by rfl⟩ : syracuseStep 5316803 = 7975205) B7975205
theorem B2801897 : Blo 1244440 2801897 := bstep (se 2 (by rfl) ⟨1050711, by rfl⟩ : syracuseStep 2801897 = 2101423) B2101423
theorem B1245595 : Blo 1244440 1245595 := bstep (se 1 (by rfl) ⟨934196, by rfl⟩ : syracuseStep 1245595 = 1868393) B1868393
theorem B1245599 : Blo 1244440 1245599 := bstep (se 1 (by rfl) ⟨934199, by rfl⟩ : syracuseStep 1245599 = 1868399) B1868399
theorem B1868315 : Blo 1244440 1868315 := bstep (se 1 (by rfl) ⟨1401236, by rfl⟩ : syracuseStep 1868315 = 2802473) B2802473
theorem B3547759 : Blo 1244440 3547759 := bstep (se 1 (by rfl) ⟨2660819, by rfl⟩ : syracuseStep 3547759 = 5321639) B5321639
theorem B11977415 : Blo 1244440 11977415 := bstep (se 1 (by rfl) ⟨8983061, by rfl⟩ : syracuseStep 11977415 = 17966123) B17966123
theorem B1868495 : Blo 1244440 1868495 := bstep (se 1 (by rfl) ⟨1401371, by rfl⟩ : syracuseStep 1868495 = 2802743) B2802743
theorem B1246015 : Blo 1244440 1246015 := bstep (se 1 (by rfl) ⟨934511, by rfl⟩ : syracuseStep 1246015 = 1869023) B1869023
theorem B1868615 : Blo 1244440 1868615 := bstep (se 1 (by rfl) ⟨1401461, by rfl⟩ : syracuseStep 1868615 = 2802923) B2802923
theorem B1246023 : Blo 1244440 1246023 := bstep (se 1 (by rfl) ⟨934517, by rfl⟩ : syracuseStep 1246023 = 1869035) B1869035
theorem B1868681 : Blo 1244440 1868681 := bstep (se 2 (by rfl) ⟨700755, by rfl⟩ : syracuseStep 1868681 = 1401511) B1401511
theorem B6308927 : Blo 1244440 6308927 := bstep (se 1 (by rfl) ⟨4731695, by rfl⟩ : syracuseStep 6308927 = 9463391) B9463391
theorem B1246279 : Blo 1244440 1246279 := bstep (se 1 (by rfl) ⟨934709, by rfl⟩ : syracuseStep 1246279 = 1869419) B1869419
theorem B3155051 : Blo 1244440 3155051 := bstep (se 1 (by rfl) ⟨2366288, by rfl⟩ : syracuseStep 3155051 = 4732577) B4732577
theorem B3196025 : Blo 1244440 3196025 := bstep (se 2 (by rfl) ⟨1198509, by rfl⟩ : syracuseStep 3196025 = 2397019) B2397019
theorem B1868927 : Blo 1244440 1868927 := bstep (se 1 (by rfl) ⟨1401695, by rfl⟩ : syracuseStep 1868927 = 2803391) B2803391
theorem B1246335 : Blo 1244440 1246335 := bstep (se 1 (by rfl) ⟨934751, by rfl⟩ : syracuseStep 1246335 = 1869503) B1869503
theorem B1402087 : Blo 1244440 1402087 := bstep (se 1 (by rfl) ⟨1051565, by rfl⟩ : syracuseStep 1402087 = 2103131) B2103131
theorem B1869065 : Blo 1244440 1869065 := bstep (se 2 (by rfl) ⟨700899, by rfl⟩ : syracuseStep 1869065 = 1401799) B1401799
theorem B6825235 : Blo 1244440 6825235 := bstep (se 1 (by rfl) ⟨5118926, by rfl⟩ : syracuseStep 6825235 = 10237853) B10237853
theorem B25576897 : Blo 1244440 25576897 := bstep (se 2 (by rfl) ⟨9591336, by rfl⟩ : syracuseStep 25576897 = 19182673) B19182673
theorem B31925825 : Blo 1244440 31925825 := bstep (se 2 (by rfl) ⟨11972184, by rfl⟩ : syracuseStep 31925825 = 23944369) B23944369
theorem B27666083 : Blo 1244440 27666083 := bstep (se 1 (by rfl) ⟨20749562, by rfl⟩ : syracuseStep 27666083 = 41499125) B41499125
theorem B7095995 : Blo 1244440 7095995 := bstep (se 1 (by rfl) ⟨5321996, by rfl⟩ : syracuseStep 7095995 = 10643993) B10643993
theorem B1869545 : Blo 1244440 1869545 := bstep (se 2 (by rfl) ⟨701079, by rfl⟩ : syracuseStep 1869545 = 1402159) B1402159
theorem B1869551 : Blo 1244440 1869551 := bstep (se 1 (by rfl) ⟨1402163, by rfl⟩ : syracuseStep 1869551 = 2804327) B2804327
theorem B5982095 : Blo 1244440 5982095 := bstep (se 1 (by rfl) ⟨4486571, by rfl⟩ : syracuseStep 5982095 = 8973143) B8973143
theorem B6727589 : Blo 1244440 6727589 := bstep (se 4 (by rfl) ⟨630711, by rfl⟩ : syracuseStep 6727589 = 1261423) B1261423
theorem B2803679 : Blo 1244440 2803679 := bstep (se 1 (by rfl) ⟨2102759, by rfl⟩ : syracuseStep 2803679 = 4205519) B4205519
theorem B11962343 : Blo 1244440 11962343 := bstep (se 1 (by rfl) ⟨8971757, by rfl⟩ : syracuseStep 11962343 = 17943515) B17943515
theorem B4491359 : Blo 1244440 4491359 := bstep (se 1 (by rfl) ⟨3368519, by rfl⟩ : syracuseStep 4491359 = 6737039) B6737039
theorem B15157367 : Blo 1244440 15157367 := bstep (se 1 (by rfl) ⟨11368025, by rfl⟩ : syracuseStep 15157367 = 22736051) B22736051
theorem B2803895 : Blo 1244440 2803895 := bstep (se 1 (by rfl) ⟨2102921, by rfl⟩ : syracuseStep 2803895 = 4205843) B4205843
theorem B4204763 : Blo 1244440 4204763 := bstep (se 1 (by rfl) ⟨3153572, by rfl⟩ : syracuseStep 4204763 = 6307145) B6307145
theorem B6728129 : Blo 1244440 6728129 := bstep (se 2 (by rfl) ⟨2523048, by rfl⟩ : syracuseStep 6728129 = 5046097) B5046097
theorem B4491791 : Blo 1244440 4491791 := bstep (se 1 (by rfl) ⟨3368843, by rfl⟩ : syracuseStep 4491791 = 6737687) B6737687
theorem B40381213 : Blo 1244440 40381213 := bstep (se 3 (by rfl) ⟨7571477, by rfl⟩ : syracuseStep 40381213 = 15142955) B15142955
theorem B7088957 : Blo 1244440 7088957 := bstep (se 3 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 7088957 = 2658359) B2658359
theorem B4729661 : Blo 1244440 4729661 := bstep (se 3 (by rfl) ⟨886811, by rfl⟩ : syracuseStep 4729661 = 1773623) B1773623
theorem B28748611 : Blo 1244440 28748611 := bstep (se 1 (by rfl) ⟨21561458, by rfl⟩ : syracuseStep 28748611 = 43122917) B43122917
theorem B5319503 : Blo 1244440 5319503 := bstep (se 1 (by rfl) ⟨3989627, by rfl⟩ : syracuseStep 5319503 = 7979255) B7979255
theorem B1576027 : Blo 1244440 1576027 := bstep (se 1 (by rfl) ⟨1182020, by rfl⟩ : syracuseStep 1576027 = 2364041) B2364041
theorem B2362537 : Blo 1244440 2362537 := bstep (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) B1771903
theorem B5319863 : Blo 1244440 5319863 := bstep (se 1 (by rfl) ⟨3989897, by rfl⟩ : syracuseStep 5319863 = 7979795) B7979795
theorem B7982687 : Blo 1244440 7982687 := bstep (se 1 (by rfl) ⟨5987015, by rfl⟩ : syracuseStep 7982687 = 11974031) B11974031
theorem B4796009 : Blo 1244440 4796009 := bstep (se 2 (by rfl) ⟨1798503, by rfl⟩ : syracuseStep 4796009 = 3597007) B3597007
theorem B2363327 : Blo 1244440 2363327 := bstep (se 1 (by rfl) ⟨1772495, by rfl⟩ : syracuseStep 2363327 = 3544991) B3544991
theorem B2101241 : Blo 1244440 2101241 := bstep (se 2 (by rfl) ⟨787965, by rfl⟩ : syracuseStep 2101241 = 1575931) B1575931
theorem B26923063 : Blo 1244440 26923063 := bstep (se 1 (by rfl) ⟨20192297, by rfl⟩ : syracuseStep 26923063 = 40384595) B40384595
theorem B6303905 : Blo 1244440 6303905 := bstep (se 2 (by rfl) ⟨2363964, by rfl⟩ : syracuseStep 6303905 = 4727929) B4727929
theorem B2101511 : Blo 1244440 2101511 := bstep (se 1 (by rfl) ⟨1576133, by rfl⟩ : syracuseStep 2101511 = 3152267) B3152267
theorem B18444793 : Blo 1244440 18444793 := bstep (se 2 (by rfl) ⟨6916797, by rfl⟩ : syracuseStep 18444793 = 13833595) B13833595
theorem B26940185 : Blo 1244440 26940185 := bstep (se 2 (by rfl) ⟨10102569, by rfl⟩ : syracuseStep 26940185 = 20205139) B20205139
theorem B2102591 : Blo 1244440 2102591 := bstep (se 1 (by rfl) ⟨1576943, by rfl⟩ : syracuseStep 2102591 = 3153887) B3153887
theorem B12137795 : Blo 1244440 12137795 := bstep (se 1 (by rfl) ⟨9103346, by rfl⟩ : syracuseStep 12137795 = 18206693) B18206693
theorem B3151183 : Blo 1244440 3151183 := bstep (se 1 (by rfl) ⟨2363387, by rfl⟩ : syracuseStep 3151183 = 4726775) B4726775
theorem B3544489 : Blo 1244440 3544489 := bstep (se 2 (by rfl) ⟨1329183, by rfl⟩ : syracuseStep 3544489 = 2658367) B2658367
theorem B6305363 : Blo 1244440 6305363 := bstep (se 1 (by rfl) ⟨4729022, by rfl⟩ : syracuseStep 6305363 = 9458045) B9458045
theorem B31127179 : Blo 1244440 31127179 := bstep (se 1 (by rfl) ⟨23345384, by rfl⟩ : syracuseStep 31127179 = 46690769) B46690769
theorem B7091873 : Blo 1244440 7091873 := bstep (se 2 (by rfl) ⟨2659452, by rfl⟩ : syracuseStep 7091873 = 5318905) B5318905
theorem B2840255 : Blo 1244440 2840255 := bstep (se 1 (by rfl) ⟨2130191, by rfl⟩ : syracuseStep 2840255 = 4260383) B4260383
theorem B13465601 : Blo 1244440 13465601 := bstep (se 2 (by rfl) ⟨5049600, by rfl⟩ : syracuseStep 13465601 = 10099201) B10099201
theorem B4257863 : Blo 1244440 4257863 := bstep (se 1 (by rfl) ⟨3193397, by rfl⟩ : syracuseStep 4257863 = 6386795) B6386795
theorem B4200659 : Blo 1244440 4200659 := bstep (se 1 (by rfl) ⟨3150494, by rfl⟩ : syracuseStep 4200659 = 6300989) B6300989
theorem B5323279 : Blo 1244440 5323279 := bstep (se 1 (by rfl) ⟨3992459, by rfl⟩ : syracuseStep 5323279 = 7984919) B7984919
theorem B2661025 : Blo 1244440 2661025 := bstep (se 2 (by rfl) ⟨997884, by rfl⟩ : syracuseStep 2661025 = 1995769) B1995769
theorem B33250067 : Blo 1244440 33250067 := bstep (se 1 (by rfl) ⟨24937550, by rfl⟩ : syracuseStep 33250067 = 49875101) B49875101
theorem B3595055 : Blo 1244440 3595055 := bstep (se 1 (by rfl) ⟨2696291, by rfl⟩ : syracuseStep 3595055 = 5392583) B5392583
theorem B7093079 : Blo 1244440 7093079 := bstep (se 1 (by rfl) ⟨5319809, by rfl⟩ : syracuseStep 7093079 = 10639619) B10639619
theorem B1866719 : Blo 1244440 1866719 := bstep (se 1 (by rfl) ⟨1400039, by rfl⟩ : syracuseStep 1866719 = 2800079) B2800079
theorem B1866779 : Blo 1244440 1866779 := bstep (se 1 (by rfl) ⟨1400084, by rfl⟩ : syracuseStep 1866779 = 2800169) B2800169
theorem B26918041 : Blo 1244440 26918041 := bstep (se 2 (by rfl) ⟨10094265, by rfl⟩ : syracuseStep 26918041 = 20188531) B20188531
theorem B1244571 : Blo 1244440 1244571 := bstep (se 1 (by rfl) ⟨933428, by rfl⟩ : syracuseStep 1244571 = 1866857) B1866857
theorem B1867163 : Blo 1244440 1867163 := bstep (se 1 (by rfl) ⟨1400372, by rfl⟩ : syracuseStep 1867163 = 2800745) B2800745
theorem B1867241 : Blo 1244440 1867241 := bstep (se 2 (by rfl) ⟨700215, by rfl⟩ : syracuseStep 1867241 = 1400431) B1400431
theorem B1244655 : Blo 1244440 1244655 := bstep (se 1 (by rfl) ⟨933491, by rfl⟩ : syracuseStep 1244655 = 1866983) B1866983
theorem B1867247 : Blo 1244440 1867247 := bstep (se 1 (by rfl) ⟨1400435, by rfl⟩ : syracuseStep 1867247 = 2800871) B2800871
theorem B5316187 : Blo 1244440 5316187 := bstep (se 1 (by rfl) ⟨3987140, by rfl⟩ : syracuseStep 5316187 = 7974281) B7974281
theorem B1867385 : Blo 1244440 1867385 := bstep (se 2 (by rfl) ⟨700269, by rfl⟩ : syracuseStep 1867385 = 1400539) B1400539
theorem B4202279 : Blo 1244440 4202279 := bstep (se 1 (by rfl) ⟨3151709, by rfl⟩ : syracuseStep 4202279 = 6303419) B6303419
theorem B1244991 : Blo 1244440 1244991 := bstep (se 1 (by rfl) ⟨933743, by rfl⟩ : syracuseStep 1244991 = 1867487) B1867487
theorem B1867583 : Blo 1244440 1867583 := bstep (se 1 (by rfl) ⟨1400687, by rfl⟩ : syracuseStep 1867583 = 2801375) B2801375
theorem B1245019 : Blo 1244440 1245019 := bstep (se 1 (by rfl) ⟨933764, by rfl⟩ : syracuseStep 1245019 = 1867529) B1867529
theorem B1867631 : Blo 1244440 1867631 := bstep (se 1 (by rfl) ⟨1400723, by rfl⟩ : syracuseStep 1867631 = 2801447) B2801447
theorem B2801627 : Blo 1244440 2801627 := bstep (se 1 (by rfl) ⟨2101220, by rfl⟩ : syracuseStep 2801627 = 4202441) B4202441
theorem B35897417 : Blo 1244440 35897417 := bstep (se 2 (by rfl) ⟨13461531, by rfl⟩ : syracuseStep 35897417 = 26923063) B26923063
theorem B1867871 : Blo 1244440 1867871 := bstep (se 1 (by rfl) ⟨1400903, by rfl⟩ : syracuseStep 1867871 = 2801807) B2801807
theorem B4202603 : Blo 1244440 4202603 := bstep (se 1 (by rfl) ⟨3151952, by rfl⟩ : syracuseStep 4202603 = 6303905) B6303905
theorem B1867913 : Blo 1244440 1867913 := bstep (se 2 (by rfl) ⟨700467, by rfl⟩ : syracuseStep 1867913 = 1400935) B1400935
theorem B1867931 : Blo 1244440 1867931 := bstep (se 1 (by rfl) ⟨1400948, by rfl⟩ : syracuseStep 1867931 = 2801897) B2801897
theorem B1401007 : Blo 1244440 1401007 := bstep (se 1 (by rfl) ⟨1050755, by rfl⟩ : syracuseStep 1401007 = 2101511) B2101511
theorem B1245543 : Blo 1244440 1245543 := bstep (se 1 (by rfl) ⟨934157, by rfl⟩ : syracuseStep 1245543 = 1868315) B1868315
theorem B1245663 : Blo 1244440 1245663 := bstep (se 1 (by rfl) ⟨934247, by rfl⟩ : syracuseStep 1245663 = 1868495) B1868495
theorem B38347253 : Blo 1244440 38347253 := bstep (se 5 (by rfl) ⟨1797527, by rfl⟩ : syracuseStep 38347253 = 3595055) B3595055
theorem B1245743 : Blo 1244440 1245743 := bstep (se 1 (by rfl) ⟨934307, by rfl⟩ : syracuseStep 1245743 = 1868615) B1868615
theorem B1245787 : Blo 1244440 1245787 := bstep (se 1 (by rfl) ⟨934340, by rfl⟩ : syracuseStep 1245787 = 1868681) B1868681
theorem B24593057 : Blo 1244440 24593057 := bstep (se 2 (by rfl) ⟨9222396, by rfl⟩ : syracuseStep 24593057 = 18444793) B18444793
theorem B2130683 : Blo 1244440 2130683 := bstep (se 1 (by rfl) ⟨1598012, by rfl⟩ : syracuseStep 2130683 = 3196025) B3196025
theorem B1245951 : Blo 1244440 1245951 := bstep (se 1 (by rfl) ⟨934463, by rfl⟩ : syracuseStep 1245951 = 1868927) B1868927
theorem B1246043 : Blo 1244440 1246043 := bstep (se 1 (by rfl) ⟨934532, by rfl⟩ : syracuseStep 1246043 = 1869065) B1869065
theorem B1401727 : Blo 1244440 1401727 := bstep (se 1 (by rfl) ⟨1051295, by rfl⟩ : syracuseStep 1401727 = 2102591) B2102591
theorem B3548033 : Blo 1244440 3548033 := bstep (se 2 (by rfl) ⟨1330512, by rfl⟩ : syracuseStep 3548033 = 2661025) B2661025
theorem B21283883 : Blo 1244440 21283883 := bstep (se 1 (by rfl) ⟨15962912, by rfl⟩ : syracuseStep 21283883 = 31925825) B31925825
theorem B4203575 : Blo 1244440 4203575 := bstep (se 1 (by rfl) ⟨3152681, by rfl⟩ : syracuseStep 4203575 = 6305363) B6305363
theorem B38331481 : Blo 1244440 38331481 := bstep (se 2 (by rfl) ⟨14374305, by rfl⟩ : syracuseStep 38331481 = 28748611) B28748611
theorem B4727915 : Blo 1244440 4727915 := bstep (se 1 (by rfl) ⟨3545936, by rfl⟩ : syracuseStep 4727915 = 7091873) B7091873
theorem B1893503 : Blo 1244440 1893503 := bstep (se 1 (by rfl) ⟨1420127, by rfl⟩ : syracuseStep 1893503 = 2840255) B2840255
theorem B1246363 : Blo 1244440 1246363 := bstep (se 1 (by rfl) ⟨934772, by rfl⟩ : syracuseStep 1246363 = 1869545) B1869545
theorem B1246367 : Blo 1244440 1246367 := bstep (se 1 (by rfl) ⟨934775, by rfl⟩ : syracuseStep 1246367 = 1869551) B1869551
theorem B1869119 : Blo 1244440 1869119 := bstep (se 1 (by rfl) ⟨1401839, by rfl⟩ : syracuseStep 1869119 = 2803679) B2803679
theorem B1869263 : Blo 1244440 1869263 := bstep (se 1 (by rfl) ⟨1401947, by rfl⟩ : syracuseStep 1869263 = 2803895) B2803895
theorem B2803175 : Blo 1244440 2803175 := bstep (se 1 (by rfl) ⟨2102381, by rfl⟩ : syracuseStep 2803175 = 4204763) B4204763
theorem B35890721 : Blo 1244440 35890721 := bstep (se 2 (by rfl) ⟨13459020, by rfl⟩ : syracuseStep 35890721 = 26918041) B26918041
theorem B1869449 : Blo 1244440 1869449 := bstep (se 2 (by rfl) ⟨701043, by rfl⟩ : syracuseStep 1869449 = 1402087) B1402087
theorem B4728719 : Blo 1244440 4728719 := bstep (se 1 (by rfl) ⟨3546539, by rfl⟩ : syracuseStep 4728719 = 7093079) B7093079
theorem B7088249 : Blo 1244440 7088249 := bstep (se 2 (by rfl) ⟨2658093, by rfl⟩ : syracuseStep 7088249 = 5316187) B5316187
theorem B41502905 : Blo 1244440 41502905 := bstep (se 2 (by rfl) ⟨15563589, by rfl⟩ : syracuseStep 41502905 = 31127179) B31127179
theorem B3197339 : Blo 1244440 3197339 := bstep (se 1 (by rfl) ⟨2398004, by rfl⟩ : syracuseStep 3197339 = 4796009) B4796009
theorem B1575551 : Blo 1244440 1575551 := bstep (se 1 (by rfl) ⟨1181663, by rfl⟩ : syracuseStep 1575551 = 2363327) B2363327
theorem B17960123 : Blo 1244440 17960123 := bstep (se 1 (by rfl) ⟨13470092, by rfl⟩ : syracuseStep 17960123 = 26940185) B26940185
theorem B7097705 : Blo 1244440 7097705 := bstep (se 2 (by rfl) ⟨2661639, by rfl⟩ : syracuseStep 7097705 = 5323279) B5323279
theorem B4205951 : Blo 1244440 4205951 := bstep (se 1 (by rfl) ⟨3154463, by rfl⟩ : syracuseStep 4205951 = 6308927) B6308927
theorem B4730345 : Blo 1244440 4730345 := bstep (se 2 (by rfl) ⟨1773879, by rfl⟩ : syracuseStep 4730345 = 3547759) B3547759
theorem B53841617 : Blo 1244440 53841617 := bstep (se 2 (by rfl) ⟨20190606, by rfl⟩ : syracuseStep 53841617 = 40381213) B40381213
theorem B4730663 : Blo 1244440 4730663 := bstep (se 1 (by rfl) ⟨3547997, by rfl⟩ : syracuseStep 4730663 = 7095995) B7095995
theorem B4485059 : Blo 1244440 4485059 := bstep (se 1 (by rfl) ⟨3363794, by rfl⟩ : syracuseStep 4485059 = 6727589) B6727589
theorem B2838575 : Blo 1244440 2838575 := bstep (se 1 (by rfl) ⟨2128931, by rfl⟩ : syracuseStep 2838575 = 4257863) B4257863
theorem B2994239 : Blo 1244440 2994239 := bstep (se 1 (by rfl) ⟨2245679, by rfl⟩ : syracuseStep 2994239 = 4491359) B4491359
theorem B10104911 : Blo 1244440 10104911 := bstep (se 1 (by rfl) ⟨7578683, by rfl⟩ : syracuseStep 10104911 = 15157367) B15157367
theorem B2101369 : Blo 1244440 2101369 := bstep (se 2 (by rfl) ⟨788013, by rfl⟩ : syracuseStep 2101369 = 1576027) B1576027
theorem B3150049 : Blo 1244440 3150049 := bstep (se 2 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 3150049 = 2362537) B2362537
theorem B4485419 : Blo 1244440 4485419 := bstep (se 1 (by rfl) ⟨3364064, by rfl⟩ : syracuseStep 4485419 = 6728129) B6728129
theorem B2994527 : Blo 1244440 2994527 := bstep (se 1 (by rfl) ⟨2245895, by rfl⟩ : syracuseStep 2994527 = 4491791) B4491791
theorem B5321791 : Blo 1244440 5321791 := bstep (se 1 (by rfl) ⟨3991343, by rfl⟩ : syracuseStep 5321791 = 7982687) B7982687
theorem B3544535 : Blo 1244440 3544535 := bstep (se 1 (by rfl) ⟨2658401, by rfl⟩ : syracuseStep 3544535 = 5316803) B5316803
theorem B7984943 : Blo 1244440 7984943 := bstep (se 1 (by rfl) ⟨5988707, by rfl⟩ : syracuseStep 7984943 = 11977415) B11977415
theorem B2103367 : Blo 1244440 2103367 := bstep (se 1 (by rfl) ⟨1577525, by rfl⟩ : syracuseStep 2103367 = 3155051) B3155051
theorem B8091863 : Blo 1244440 8091863 := bstep (se 1 (by rfl) ⟨6068897, by rfl⟩ : syracuseStep 8091863 = 12137795) B12137795
theorem B3988063 : Blo 1244440 3988063 := bstep (se 1 (by rfl) ⟨2991047, by rfl⟩ : syracuseStep 3988063 = 5982095) B5982095
theorem B8977067 : Blo 1244440 8977067 := bstep (se 1 (by rfl) ⟨6732800, by rfl⟩ : syracuseStep 8977067 = 13465601) B13465601
theorem B2800439 : Blo 1244440 2800439 := bstep (se 1 (by rfl) ⟨2100329, by rfl⟩ : syracuseStep 2800439 = 4200659) B4200659
theorem B9100313 : Blo 1244440 9100313 := bstep (se 2 (by rfl) ⟨3412617, by rfl⟩ : syracuseStep 9100313 = 6825235) B6825235
theorem B73776221 : Blo 1244440 73776221 := bstep (se 3 (by rfl) ⟨13833041, by rfl⟩ : syracuseStep 73776221 = 27666083) B27666083
theorem B4201577 : Blo 1244440 4201577 := bstep (se 2 (by rfl) ⟨1575591, by rfl⟩ : syracuseStep 4201577 = 3151183) B3151183
theorem B22166711 : Blo 1244440 22166711 := bstep (se 1 (by rfl) ⟨16625033, by rfl⟩ : syracuseStep 22166711 = 33250067) B33250067
theorem B4725971 : Blo 1244440 4725971 := bstep (se 1 (by rfl) ⟨3544478, by rfl⟩ : syracuseStep 4725971 = 7088957) B7088957
theorem B3153107 : Blo 1244440 3153107 := bstep (se 1 (by rfl) ⟨2364830, by rfl⟩ : syracuseStep 3153107 = 4729661) B4729661
theorem B3546335 : Blo 1244440 3546335 := bstep (se 1 (by rfl) ⟨2659751, by rfl⟩ : syracuseStep 3546335 = 5319503) B5319503
theorem B4725985 : Blo 1244440 4725985 := bstep (se 2 (by rfl) ⟨1772244, by rfl⟩ : syracuseStep 4725985 = 3544489) B3544489
theorem B34102529 : Blo 1244440 34102529 := bstep (se 2 (by rfl) ⟨12788448, by rfl⟩ : syracuseStep 34102529 = 25576897) B25576897
theorem B1244479 : Blo 1244440 1244479 := bstep (se 1 (by rfl) ⟨933359, by rfl⟩ : syracuseStep 1244479 = 1866719) B1866719
theorem B1244519 : Blo 1244440 1244519 := bstep (se 1 (by rfl) ⟨933389, by rfl⟩ : syracuseStep 1244519 = 1866779) B1866779
theorem B3546575 : Blo 1244440 3546575 := bstep (se 1 (by rfl) ⟨2659931, by rfl⟩ : syracuseStep 3546575 = 5319863) B5319863
theorem B1244775 : Blo 1244440 1244775 := bstep (se 1 (by rfl) ⟨933581, by rfl⟩ : syracuseStep 1244775 = 1867163) B1867163
theorem B1244827 : Blo 1244440 1244827 := bstep (se 1 (by rfl) ⟨933620, by rfl⟩ : syracuseStep 1244827 = 1867241) B1867241
theorem B1244831 : Blo 1244440 1244831 := bstep (se 1 (by rfl) ⟨933623, by rfl⟩ : syracuseStep 1244831 = 1867247) B1867247
theorem B1244923 : Blo 1244440 1244923 := bstep (se 1 (by rfl) ⟨933692, by rfl⟩ : syracuseStep 1244923 = 1867385) B1867385
theorem B2801519 : Blo 1244440 2801519 := bstep (se 1 (by rfl) ⟨2101139, by rfl⟩ : syracuseStep 2801519 = 4202279) B4202279
theorem B1245055 : Blo 1244440 1245055 := bstep (se 1 (by rfl) ⟨933791, by rfl⟩ : syracuseStep 1245055 = 1867583) B1867583
theorem B1245087 : Blo 1244440 1245087 := bstep (se 1 (by rfl) ⟨933815, by rfl⟩ : syracuseStep 1245087 = 1867631) B1867631
theorem B31899581 : Blo 1244440 31899581 := bstep (se 3 (by rfl) ⟨5981171, by rfl⟩ : syracuseStep 31899581 = 11962343) B11962343
theorem B1867751 : Blo 1244440 1867751 := bstep (se 1 (by rfl) ⟨1400813, by rfl⟩ : syracuseStep 1867751 = 2801627) B2801627
theorem B1400827 : Blo 1244440 1400827 := bstep (se 1 (by rfl) ⟨1050620, by rfl⟩ : syracuseStep 1400827 = 2101241) B2101241
theorem B1892383 : Blo 1244440 1892383 := bstep (se 1 (by rfl) ⟨1419287, by rfl⟩ : syracuseStep 1892383 = 2838575) B2838575
theorem B1245247 : Blo 1244440 1245247 := bstep (se 1 (by rfl) ⟨933935, by rfl⟩ : syracuseStep 1245247 = 1867871) B1867871
theorem B2801735 : Blo 1244440 2801735 := bstep (se 1 (by rfl) ⟨2101301, by rfl⟩ : syracuseStep 2801735 = 4202603) B4202603
theorem B1245275 : Blo 1244440 1245275 := bstep (se 1 (by rfl) ⟨933956, by rfl⟩ : syracuseStep 1245275 = 1867913) B1867913
theorem B1245287 : Blo 1244440 1245287 := bstep (se 1 (by rfl) ⟨933965, by rfl⟩ : syracuseStep 1245287 = 1867931) B1867931
theorem B2801825 : Blo 1244440 2801825 := bstep (se 2 (by rfl) ⟨1050684, by rfl⟩ : syracuseStep 2801825 = 2101369) B2101369
theorem B2990279 : Blo 1244440 2990279 := bstep (se 1 (by rfl) ⟨2242709, by rfl⟩ : syracuseStep 2990279 = 4485419) B4485419
theorem B1868009 : Blo 1244440 1868009 := bstep (se 2 (by rfl) ⟨700503, by rfl⟩ : syracuseStep 1868009 = 1401007) B1401007
theorem B14189255 : Blo 1244440 14189255 := bstep (se 1 (by rfl) ⟨10641941, by rfl⟩ : syracuseStep 14189255 = 21283883) B21283883
theorem B2802383 : Blo 1244440 2802383 := bstep (se 1 (by rfl) ⟨2101787, by rfl⟩ : syracuseStep 2802383 = 4203575) B4203575
theorem B1262335 : Blo 1244440 1262335 := bstep (se 1 (by rfl) ⟨946751, by rfl⟩ : syracuseStep 1262335 = 1893503) B1893503
theorem B5317417 : Blo 1244440 5317417 := bstep (se 2 (by rfl) ⟨1994031, by rfl⟩ : syracuseStep 5317417 = 3988063) B3988063
theorem B1246079 : Blo 1244440 1246079 := bstep (se 1 (by rfl) ⟨934559, by rfl⟩ : syracuseStep 1246079 = 1869119) B1869119
theorem B1246175 : Blo 1244440 1246175 := bstep (se 1 (by rfl) ⟨934631, by rfl⟩ : syracuseStep 1246175 = 1869263) B1869263
theorem B1868783 : Blo 1244440 1868783 := bstep (se 1 (by rfl) ⟨1401587, by rfl⟩ : syracuseStep 1868783 = 2803175) B2803175
theorem B1246299 : Blo 1244440 1246299 := bstep (se 1 (by rfl) ⟨934724, by rfl⟩ : syracuseStep 1246299 = 1869449) B1869449
theorem B1868969 : Blo 1244440 1868969 := bstep (se 2 (by rfl) ⟨700863, by rfl⟩ : syracuseStep 1868969 = 1401727) B1401727
theorem B7095721 : Blo 1244440 7095721 := bstep (se 2 (by rfl) ⟨2660895, by rfl⟩ : syracuseStep 7095721 = 5321791) B5321791
theorem B2131559 : Blo 1244440 2131559 := bstep (se 1 (by rfl) ⟨1598669, by rfl⟩ : syracuseStep 2131559 = 3197339) B3197339
theorem B6301313 : Blo 1244440 6301313 := bstep (se 2 (by rfl) ⟨2362992, by rfl⟩ : syracuseStep 6301313 = 4725985) B4725985
theorem B22735019 : Blo 1244440 22735019 := bstep (se 1 (by rfl) ⟨17051264, by rfl⟩ : syracuseStep 22735019 = 34102529) B34102529
theorem B2803967 : Blo 1244440 2803967 := bstep (se 1 (by rfl) ⟨2102975, by rfl⟩ : syracuseStep 2803967 = 4205951) B4205951
theorem B23931611 : Blo 1244440 23931611 := bstep (se 1 (by rfl) ⟨17948708, by rfl⟩ : syracuseStep 23931611 = 35897417) B35897417
theorem B6736607 : Blo 1244440 6736607 := bstep (se 1 (by rfl) ⟨5052455, by rfl⟩ : syracuseStep 6736607 = 10104911) B10104911
theorem B2804489 : Blo 1244440 2804489 := bstep (se 2 (by rfl) ⟨1051683, by rfl⟩ : syracuseStep 2804489 = 2103367) B2103367
theorem B16395371 : Blo 1244440 16395371 := bstep (se 1 (by rfl) ⟨12296528, by rfl⟩ : syracuseStep 16395371 = 24593057) B24593057
theorem B2363023 : Blo 1244440 2363023 := bstep (se 1 (by rfl) ⟨1772267, by rfl⟩ : syracuseStep 2363023 = 3544535) B3544535
theorem B27668603 : Blo 1244440 27668603 := bstep (se 1 (by rfl) ⟨20751452, by rfl⟩ : syracuseStep 27668603 = 41502905) B41502905
theorem B5394575 : Blo 1244440 5394575 := bstep (se 1 (by rfl) ⟨4045931, by rfl⟩ : syracuseStep 5394575 = 8091863) B8091863
theorem B5984711 : Blo 1244440 5984711 := bstep (se 1 (by rfl) ⟨4488533, by rfl⟩ : syracuseStep 5984711 = 8977067) B8977067
theorem B5681821 : Blo 1244440 5681821 := bstep (se 3 (by rfl) ⟨1065341, by rfl⟩ : syracuseStep 5681821 = 2130683) B2130683
theorem B6066875 : Blo 1244440 6066875 := bstep (se 1 (by rfl) ⟨4550156, by rfl⟩ : syracuseStep 6066875 = 9100313) B9100313
theorem B11973415 : Blo 1244440 11973415 := bstep (se 1 (by rfl) ⟨8980061, by rfl⟩ : syracuseStep 11973415 = 17960123) B17960123
theorem B3150647 : Blo 1244440 3150647 := bstep (se 1 (by rfl) ⟨2362985, by rfl⟩ : syracuseStep 3150647 = 4725971) B4725971
theorem B2102071 : Blo 1244440 2102071 := bstep (se 1 (by rfl) ⟨1576553, by rfl⟩ : syracuseStep 2102071 = 3153107) B3153107
theorem B2364223 : Blo 1244440 2364223 := bstep (se 1 (by rfl) ⟨1773167, by rfl⟩ : syracuseStep 2364223 = 3546335) B3546335
theorem B4731803 : Blo 1244440 4731803 := bstep (se 1 (by rfl) ⟨3548852, by rfl⟩ : syracuseStep 4731803 = 7097705) B7097705
theorem B2364383 : Blo 1244440 2364383 := bstep (se 1 (by rfl) ⟨1773287, by rfl⟩ : syracuseStep 2364383 = 3546575) B3546575
theorem B35894411 : Blo 1244440 35894411 := bstep (se 1 (by rfl) ⟨26920808, by rfl⟩ : syracuseStep 35894411 = 53841617) B53841617
theorem B1996159 : Blo 1244440 1996159 := bstep (se 1 (by rfl) ⟨1497119, by rfl⟩ : syracuseStep 1996159 = 2994239) B2994239
theorem B4200065 : Blo 1244440 4200065 := bstep (se 2 (by rfl) ⟨1575024, by rfl⟩ : syracuseStep 4200065 = 3150049) B3150049
theorem B25564835 : Blo 1244440 25564835 := bstep (se 1 (by rfl) ⟨19173626, by rfl⟩ : syracuseStep 25564835 = 38347253) B38347253
theorem B2365355 : Blo 1244440 2365355 := bstep (se 1 (by rfl) ⟨1774016, by rfl⟩ : syracuseStep 2365355 = 3548033) B3548033
theorem B3151943 : Blo 1244440 3151943 := bstep (se 1 (by rfl) ⟨2363957, by rfl⟩ : syracuseStep 3151943 = 4727915) B4727915
theorem B7985405 : Blo 1244440 7985405 := bstep (se 3 (by rfl) ⟨1497263, by rfl⟩ : syracuseStep 7985405 = 2994527) B2994527
theorem B786946357 : Blo 1244440 786946357 := bstep (se 5 (by rfl) ⟨36888110, by rfl⟩ : syracuseStep 786946357 = 73776221) B73776221
theorem B23927147 : Blo 1244440 23927147 := bstep (se 1 (by rfl) ⟨17945360, by rfl⟩ : syracuseStep 23927147 = 35890721) B35890721
theorem B5323295 : Blo 1244440 5323295 := bstep (se 1 (by rfl) ⟨3992471, by rfl⟩ : syracuseStep 5323295 = 7984943) B7984943
theorem B3152479 : Blo 1244440 3152479 := bstep (se 1 (by rfl) ⟨2364359, by rfl⟩ : syracuseStep 3152479 = 4728719) B4728719
theorem B4725499 : Blo 1244440 4725499 := bstep (se 1 (by rfl) ⟨3544124, by rfl⟩ : syracuseStep 4725499 = 7088249) B7088249
theorem B51108641 : Blo 1244440 51108641 := bstep (se 2 (by rfl) ⟨19165740, by rfl⟩ : syracuseStep 51108641 = 38331481) B38331481
theorem B4201469 : Blo 1244440 4201469 := bstep (se 3 (by rfl) ⟨787775, by rfl⟩ : syracuseStep 4201469 = 1575551) B1575551
theorem B1866959 : Blo 1244440 1866959 := bstep (se 1 (by rfl) ⟨1400219, by rfl⟩ : syracuseStep 1866959 = 2800439) B2800439
theorem B2801051 : Blo 1244440 2801051 := bstep (se 1 (by rfl) ⟨2100788, by rfl⟩ : syracuseStep 2801051 = 4201577) B4201577
theorem B14777807 : Blo 1244440 14777807 := bstep (se 1 (by rfl) ⟨11083355, by rfl⟩ : syracuseStep 14777807 = 22166711) B22166711
theorem B3153563 : Blo 1244440 3153563 := bstep (se 1 (by rfl) ⟨2365172, by rfl⟩ : syracuseStep 3153563 = 4730345) B4730345
theorem B3153775 : Blo 1244440 3153775 := bstep (se 1 (by rfl) ⟨2365331, by rfl⟩ : syracuseStep 3153775 = 4730663) B4730663
theorem B1867679 : Blo 1244440 1867679 := bstep (se 1 (by rfl) ⟨1400759, by rfl⟩ : syracuseStep 1867679 = 2801519) B2801519
theorem B21266387 : Blo 1244440 21266387 := bstep (se 1 (by rfl) ⟨15949790, by rfl⟩ : syracuseStep 21266387 = 31899581) B31899581
theorem B2990039 : Blo 1244440 2990039 := bstep (se 1 (by rfl) ⟨2242529, by rfl⟩ : syracuseStep 2990039 = 4485059) B4485059
theorem B1245167 : Blo 1244440 1245167 := bstep (se 1 (by rfl) ⟨933875, by rfl⟩ : syracuseStep 1245167 = 1867751) B1867751
theorem B1867769 : Blo 1244440 1867769 := bstep (se 2 (by rfl) ⟨700413, by rfl⟩ : syracuseStep 1867769 = 1400827) B1400827
theorem B1867823 : Blo 1244440 1867823 := bstep (se 1 (by rfl) ⟨1400867, by rfl⟩ : syracuseStep 1867823 = 2801735) B2801735
theorem B3596383 : Blo 1244440 3596383 := bstep (se 1 (by rfl) ⟨2697287, by rfl⟩ : syracuseStep 3596383 = 5394575) B5394575
theorem B1867883 : Blo 1244440 1867883 := bstep (se 1 (by rfl) ⟨1400912, by rfl⟩ : syracuseStep 1867883 = 2801825) B2801825
theorem B1245339 : Blo 1244440 1245339 := bstep (se 1 (by rfl) ⟨934004, by rfl⟩ : syracuseStep 1245339 = 1868009) B1868009
theorem B10092709 : Blo 1244440 10092709 := bstep (se 4 (by rfl) ⟨946191, by rfl⟩ : syracuseStep 10092709 = 1892383) B1892383
theorem B3989807 : Blo 1244440 3989807 := bstep (se 1 (by rfl) ⟨2992355, by rfl⟩ : syracuseStep 3989807 = 5984711) B5984711
theorem B1868255 : Blo 1244440 1868255 := bstep (se 1 (by rfl) ⟨1401191, by rfl⟩ : syracuseStep 1868255 = 2802383) B2802383
theorem B3154535 : Blo 1244440 3154535 := bstep (se 1 (by rfl) ⟨2365901, by rfl⟩ : syracuseStep 3154535 = 4731803) B4731803
theorem B1245855 : Blo 1244440 1245855 := bstep (se 1 (by rfl) ⟨934391, by rfl⟩ : syracuseStep 1245855 = 1868783) B1868783
theorem B23929607 : Blo 1244440 23929607 := bstep (se 1 (by rfl) ⟨17947205, by rfl⟩ : syracuseStep 23929607 = 35894411) B35894411
theorem B1245979 : Blo 1244440 1245979 := bstep (se 1 (by rfl) ⟨934484, by rfl⟩ : syracuseStep 1245979 = 1868969) B1868969
theorem B4203305 : Blo 1244440 4203305 := bstep (se 2 (by rfl) ⟨1576239, by rfl⟩ : syracuseStep 4203305 = 3152479) B3152479
theorem B6300665 : Blo 1244440 6300665 := bstep (se 2 (by rfl) ⟨2362749, by rfl⟩ : syracuseStep 6300665 = 4725499) B4725499
theorem B2802761 : Blo 1244440 2802761 := bstep (se 2 (by rfl) ⟨1051035, by rfl⟩ : syracuseStep 2802761 = 2102071) B2102071
theorem B1869311 : Blo 1244440 1869311 := bstep (se 1 (by rfl) ⟨1401983, by rfl⟩ : syracuseStep 1869311 = 2803967) B2803967
theorem B15951431 : Blo 1244440 15951431 := bstep (se 1 (by rfl) ⟨11963573, by rfl⟩ : syracuseStep 15951431 = 23927147) B23927147
theorem B3548863 : Blo 1244440 3548863 := bstep (se 1 (by rfl) ⟨2661647, by rfl⟩ : syracuseStep 3548863 = 5323295) B5323295
theorem B4491071 : Blo 1244440 4491071 := bstep (se 1 (by rfl) ⟨3368303, by rfl⟩ : syracuseStep 4491071 = 6736607) B6736607
theorem B1869659 : Blo 1244440 1869659 := bstep (se 1 (by rfl) ⟨1402244, by rfl⟩ : syracuseStep 1869659 = 2804489) B2804489
theorem B34072427 : Blo 1244440 34072427 := bstep (se 1 (by rfl) ⟨25554320, by rfl⟩ : syracuseStep 34072427 = 51108641) B51108641
theorem B10930247 : Blo 1244440 10930247 := bstep (se 1 (by rfl) ⟨8197685, by rfl⟩ : syracuseStep 10930247 = 16395371) B16395371
theorem B4205033 : Blo 1244440 4205033 := bstep (se 2 (by rfl) ⟨1576887, by rfl⟩ : syracuseStep 4205033 = 3153775) B3153775
theorem B7973437 : Blo 1244440 7973437 := bstep (se 3 (by rfl) ⟨1495019, by rfl⟩ : syracuseStep 7973437 = 2990039) B2990039
theorem B1993519 : Blo 1244440 1993519 := bstep (se 1 (by rfl) ⟨1495139, by rfl⟩ : syracuseStep 1993519 = 2990279) B2990279
theorem B2100431 : Blo 1244440 2100431 := bstep (se 1 (by rfl) ⟨1575323, by rfl⟩ : syracuseStep 2100431 = 3150647) B3150647
theorem B1576255 : Blo 1244440 1576255 := bstep (se 1 (by rfl) ⟨1182191, by rfl⟩ : syracuseStep 1576255 = 2364383) B2364383
theorem B1683113 : Blo 1244440 1683113 := bstep (se 2 (by rfl) ⟨631167, by rfl⟩ : syracuseStep 1683113 = 1262335) B1262335
theorem B7089889 : Blo 1244440 7089889 := bstep (se 2 (by rfl) ⟨2658708, by rfl⟩ : syracuseStep 7089889 = 5317417) B5317417
theorem B1421039 : Blo 1244440 1421039 := bstep (se 1 (by rfl) ⟨1065779, by rfl⟩ : syracuseStep 1421039 = 2131559) B2131559
theorem B17043223 : Blo 1244440 17043223 := bstep (se 1 (by rfl) ⟨12782417, by rfl⟩ : syracuseStep 17043223 = 25564835) B25564835
theorem B39407485 : Blo 1244440 39407485 := bstep (se 3 (by rfl) ⟨7388903, by rfl⟩ : syracuseStep 39407485 = 14777807) B14777807
theorem B1576903 : Blo 1244440 1576903 := bstep (se 1 (by rfl) ⟨1182677, by rfl⟩ : syracuseStep 1576903 = 2365355) B2365355
theorem B2101295 : Blo 1244440 2101295 := bstep (se 1 (by rfl) ⟨1575971, by rfl⟩ : syracuseStep 2101295 = 3151943) B3151943
theorem B15954407 : Blo 1244440 15954407 := bstep (se 1 (by rfl) ⟨11965805, by rfl⟩ : syracuseStep 15954407 = 23931611) B23931611
theorem B3150697 : Blo 1244440 3150697 := bstep (se 2 (by rfl) ⟨1181511, by rfl⟩ : syracuseStep 3150697 = 2363023) B2363023
theorem B2102375 : Blo 1244440 2102375 := bstep (se 1 (by rfl) ⟨1576781, by rfl⟩ : syracuseStep 2102375 = 3153563) B3153563
theorem B14177591 : Blo 1244440 14177591 := bstep (se 1 (by rfl) ⟨10633193, by rfl⟩ : syracuseStep 14177591 = 21266387) B21266387
theorem B18445735 : Blo 1244440 18445735 := bstep (se 1 (by rfl) ⟨13834301, by rfl⟩ : syracuseStep 18445735 = 27668603) B27668603
theorem B1049261809 : Blo 1244440 1049261809 := bstep (se 2 (by rfl) ⟨393473178, by rfl⟩ : syracuseStep 1049261809 = 786946357) B786946357
theorem B60626717 : Blo 1244440 60626717 := bstep (se 3 (by rfl) ⟨11367509, by rfl⟩ : syracuseStep 60626717 = 22735019) B22735019
theorem B4044583 : Blo 1244440 4044583 := bstep (se 1 (by rfl) ⟨3033437, by rfl⟩ : syracuseStep 4044583 = 6066875) B6066875
theorem B9459503 : Blo 1244440 9459503 := bstep (se 1 (by rfl) ⟨7094627, by rfl⟩ : syracuseStep 9459503 = 14189255) B14189255
theorem B1245179 : Blo 1244440 1245179 := bstep (se 1 (by rfl) ⟨933884, by rfl⟩ : syracuseStep 1245179 = 1867769) B1867769
theorem B7575761 : Blo 1244440 7575761 := bstep (se 2 (by rfl) ⟨2840910, by rfl⟩ : syracuseStep 7575761 = 5681821) B5681821
theorem B15964553 : Blo 1244440 15964553 := bstep (se 2 (by rfl) ⟨5986707, by rfl⟩ : syracuseStep 15964553 = 11973415) B11973415
theorem B3152297 : Blo 1244440 3152297 := bstep (se 2 (by rfl) ⟨1182111, by rfl⟩ : syracuseStep 3152297 = 2364223) B2364223
theorem B2800043 : Blo 1244440 2800043 := bstep (se 1 (by rfl) ⟨2100032, by rfl⟩ : syracuseStep 2800043 = 4200065) B4200065
theorem B4200875 : Blo 1244440 4200875 := bstep (se 1 (by rfl) ⟨3150656, by rfl⟩ : syracuseStep 4200875 = 6301313) B6301313
theorem B5323603 : Blo 1244440 5323603 := bstep (se 1 (by rfl) ⟨3992702, by rfl⟩ : syracuseStep 5323603 = 7985405) B7985405
theorem B2661545 : Blo 1244440 2661545 := bstep (se 2 (by rfl) ⟨998079, by rfl⟩ : syracuseStep 2661545 = 1996159) B1996159
theorem B9460961 : Blo 1244440 9460961 := bstep (se 2 (by rfl) ⟨3547860, by rfl⟩ : syracuseStep 9460961 = 7095721) B7095721
theorem B2800979 : Blo 1244440 2800979 := bstep (se 1 (by rfl) ⟨2100734, by rfl⟩ : syracuseStep 2800979 = 4201469) B4201469
theorem B1244639 : Blo 1244440 1244639 := bstep (se 1 (by rfl) ⟨933479, by rfl⟩ : syracuseStep 1244639 = 1866959) B1866959
theorem B1867367 : Blo 1244440 1867367 := bstep (se 1 (by rfl) ⟨1400525, by rfl⟩ : syracuseStep 1867367 = 2801051) B2801051
theorem B1245119 : Blo 1244440 1245119 := bstep (se 1 (by rfl) ⟨933839, by rfl⟩ : syracuseStep 1245119 = 1867679) B1867679
theorem B1400863 : Blo 1244440 1400863 := bstep (se 1 (by rfl) ⟨1050647, by rfl⟩ : syracuseStep 1400863 = 2101295) B2101295
theorem B1245215 : Blo 1244440 1245215 := bstep (se 1 (by rfl) ⟨933911, by rfl⟩ : syracuseStep 1245215 = 1867823) B1867823
theorem B1245255 : Blo 1244440 1245255 := bstep (se 1 (by rfl) ⟨933941, by rfl⟩ : syracuseStep 1245255 = 1867883) B1867883
theorem B1245503 : Blo 1244440 1245503 := bstep (se 1 (by rfl) ⟨934127, by rfl⟩ : syracuseStep 1245503 = 1868255) B1868255
theorem B2802203 : Blo 1244440 2802203 := bstep (se 1 (by rfl) ⟨2101652, by rfl⟩ : syracuseStep 2802203 = 4203305) B4203305
theorem B1868507 : Blo 1244440 1868507 := bstep (se 1 (by rfl) ⟨1401380, by rfl⟩ : syracuseStep 1868507 = 2802761) B2802761
theorem B1401583 : Blo 1244440 1401583 := bstep (se 1 (by rfl) ⟨1051187, by rfl⟩ : syracuseStep 1401583 = 2102375) B2102375
theorem B1246207 : Blo 1244440 1246207 := bstep (se 1 (by rfl) ⟨934655, by rfl⟩ : syracuseStep 1246207 = 1869311) B1869311
theorem B10634287 : Blo 1244440 10634287 := bstep (se 1 (by rfl) ⟨7975715, by rfl⟩ : syracuseStep 10634287 = 15951431) B15951431
theorem B1246439 : Blo 1244440 1246439 := bstep (se 1 (by rfl) ⟨934829, by rfl⟩ : syracuseStep 1246439 = 1869659) B1869659
theorem B10643035 : Blo 1244440 10643035 := bstep (se 1 (by rfl) ⟨7982276, by rfl⟩ : syracuseStep 10643035 = 15964553) B15964553
theorem B2803355 : Blo 1244440 2803355 := bstep (se 1 (by rfl) ⟨2102516, by rfl⟩ : syracuseStep 2803355 = 4205033) B4205033
theorem B90859805 : Blo 1244440 90859805 := bstep (se 3 (by rfl) ⟨17036213, by rfl⟩ : syracuseStep 90859805 = 34072427) B34072427
theorem B1399015745 : Blo 1244440 1399015745 := bstep (se 2 (by rfl) ⟨524630904, by rfl⟩ : syracuseStep 1399015745 = 1049261809) B1049261809
theorem B5392777 : Blo 1244440 5392777 := bstep (se 2 (by rfl) ⟨2022291, by rfl⟩ : syracuseStep 5392777 = 4044583) B4044583
theorem B10636271 : Blo 1244440 10636271 := bstep (se 1 (by rfl) ⟨7977203, by rfl⟩ : syracuseStep 10636271 = 15954407) B15954407
theorem B7097453 : Blo 1244440 7097453 := bstep (se 3 (by rfl) ⟨1330772, by rfl⟩ : syracuseStep 7097453 = 2661545) B2661545
theorem B19180709 : Blo 1244440 19180709 := bstep (se 4 (by rfl) ⟨1798191, by rfl⟩ : syracuseStep 19180709 = 3596383) B3596383
theorem B15953071 : Blo 1244440 15953071 := bstep (se 1 (by rfl) ⟨11964803, by rfl⟩ : syracuseStep 15953071 = 23929607) B23929607
theorem B2658025 : Blo 1244440 2658025 := bstep (se 2 (by rfl) ⟨996759, by rfl⟩ : syracuseStep 2658025 = 1993519) B1993519
theorem B7098137 : Blo 1244440 7098137 := bstep (se 2 (by rfl) ⟨2661801, by rfl⟩ : syracuseStep 7098137 = 5323603) B5323603
theorem B2994047 : Blo 1244440 2994047 := bstep (se 1 (by rfl) ⟨2245535, by rfl⟩ : syracuseStep 2994047 = 4491071) B4491071
theorem B7286831 : Blo 1244440 7286831 := bstep (se 1 (by rfl) ⟨5465123, by rfl⟩ : syracuseStep 7286831 = 10930247) B10930247
theorem B5050507 : Blo 1244440 5050507 := bstep (se 1 (by rfl) ⟨3787880, by rfl⟩ : syracuseStep 5050507 = 7575761) B7575761
theorem B2101531 : Blo 1244440 2101531 := bstep (se 1 (by rfl) ⟨1576148, by rfl⟩ : syracuseStep 2101531 = 3152297) B3152297
theorem B2101673 : Blo 1244440 2101673 := bstep (se 2 (by rfl) ⟨788127, by rfl⟩ : syracuseStep 2101673 = 1576255) B1576255
theorem B3789437 : Blo 1244440 3789437 := bstep (se 3 (by rfl) ⟨710519, by rfl⟩ : syracuseStep 3789437 = 1421039) B1421039
theorem B4731817 : Blo 1244440 4731817 := bstep (se 2 (by rfl) ⟨1774431, by rfl⟩ : syracuseStep 4731817 = 3548863) B3548863
theorem B2102537 : Blo 1244440 2102537 := bstep (se 2 (by rfl) ⟨788451, by rfl⟩ : syracuseStep 2102537 = 1576903) B1576903
theorem B2659871 : Blo 1244440 2659871 := bstep (se 1 (by rfl) ⟨1994903, by rfl⟩ : syracuseStep 2659871 = 3989807) B3989807
theorem B13456945 : Blo 1244440 13456945 := bstep (se 2 (by rfl) ⟨5046354, by rfl⟩ : syracuseStep 13456945 = 10092709) B10092709
theorem B2103023 : Blo 1244440 2103023 := bstep (se 1 (by rfl) ⟨1577267, by rfl⟩ : syracuseStep 2103023 = 3154535) B3154535
theorem B4200443 : Blo 1244440 4200443 := bstep (se 1 (by rfl) ⟨3150332, by rfl⟩ : syracuseStep 4200443 = 6300665) B6300665
theorem B10631249 : Blo 1244440 10631249 := bstep (se 2 (by rfl) ⟨3986718, by rfl⟩ : syracuseStep 10631249 = 7973437) B7973437
theorem B9451727 : Blo 1244440 9451727 := bstep (se 1 (by rfl) ⟨7088795, by rfl⟩ : syracuseStep 9451727 = 14177591) B14177591
theorem B4200929 : Blo 1244440 4200929 := bstep (se 2 (by rfl) ⟨1575348, by rfl⟩ : syracuseStep 4200929 = 3150697) B3150697
theorem B40417811 : Blo 1244440 40417811 := bstep (se 1 (by rfl) ⟨30313358, by rfl⟩ : syracuseStep 40417811 = 60626717) B60626717
theorem B6306335 : Blo 1244440 6306335 := bstep (se 1 (by rfl) ⟨4729751, by rfl⟩ : syracuseStep 6306335 = 9459503) B9459503
theorem B1866695 : Blo 1244440 1866695 := bstep (se 1 (by rfl) ⟨1400021, by rfl⟩ : syracuseStep 1866695 = 2800043) B2800043
theorem B2800583 : Blo 1244440 2800583 := bstep (se 1 (by rfl) ⟨2100437, by rfl⟩ : syracuseStep 2800583 = 4200875) B4200875
theorem B4488301 : Blo 1244440 4488301 := bstep (se 3 (by rfl) ⟨841556, by rfl⟩ : syracuseStep 4488301 = 1683113) B1683113
theorem B1400287 : Blo 1244440 1400287 := bstep (se 1 (by rfl) ⟨1050215, by rfl⟩ : syracuseStep 1400287 = 2100431) B2100431
theorem B6307307 : Blo 1244440 6307307 := bstep (se 1 (by rfl) ⟨4730480, by rfl⟩ : syracuseStep 6307307 = 9460961) B9460961
theorem B98377253 : Blo 1244440 98377253 := bstep (se 4 (by rfl) ⟨9222867, by rfl⟩ : syracuseStep 98377253 = 18445735) B18445735
theorem B1867319 : Blo 1244440 1867319 := bstep (se 1 (by rfl) ⟨1400489, by rfl⟩ : syracuseStep 1867319 = 2800979) B2800979
theorem B9453185 : Blo 1244440 9453185 := bstep (se 2 (by rfl) ⟨3544944, by rfl⟩ : syracuseStep 9453185 = 7089889) B7089889
theorem B22724297 : Blo 1244440 22724297 := bstep (se 2 (by rfl) ⟨8521611, by rfl⟩ : syracuseStep 22724297 = 17043223) B17043223
theorem B1244911 : Blo 1244440 1244911 := bstep (se 1 (by rfl) ⟨933683, by rfl⟩ : syracuseStep 1244911 = 1867367) B1867367
theorem B52543313 : Blo 1244440 52543313 := bstep (se 2 (by rfl) ⟨19703742, by rfl⟩ : syracuseStep 52543313 = 39407485) B39407485
theorem B4857887 : Blo 1244440 4857887 := bstep (se 1 (by rfl) ⟨3643415, by rfl⟩ : syracuseStep 4857887 = 7286831) B7286831
theorem B1867817 : Blo 1244440 1867817 := bstep (se 2 (by rfl) ⟨700431, by rfl⟩ : syracuseStep 1867817 = 1400863) B1400863
theorem B6734009 : Blo 1244440 6734009 := bstep (se 2 (by rfl) ⟨2525253, by rfl⟩ : syracuseStep 6734009 = 5050507) B5050507
theorem B1401115 : Blo 1244440 1401115 := bstep (se 1 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 1401115 = 2101673) B2101673
theorem B1868135 : Blo 1244440 1868135 := bstep (se 1 (by rfl) ⟨1401101, by rfl⟩ : syracuseStep 1868135 = 2802203) B2802203
theorem B2802041 : Blo 1244440 2802041 := bstep (se 2 (by rfl) ⟨1050765, by rfl⟩ : syracuseStep 2802041 = 2101531) B2101531
theorem B1245671 : Blo 1244440 1245671 := bstep (se 1 (by rfl) ⟨934253, by rfl⟩ : syracuseStep 1245671 = 1868507) B1868507
theorem B23937605 : Blo 1244440 23937605 := bstep (se 4 (by rfl) ⟨2244150, by rfl⟩ : syracuseStep 23937605 = 4488301) B4488301
theorem B1401691 : Blo 1244440 1401691 := bstep (se 1 (by rfl) ⟨1051268, by rfl⟩ : syracuseStep 1401691 = 2102537) B2102537
theorem B1868777 : Blo 1244440 1868777 := bstep (se 2 (by rfl) ⟨700791, by rfl⟩ : syracuseStep 1868777 = 1401583) B1401583
theorem B1868903 : Blo 1244440 1868903 := bstep (se 1 (by rfl) ⟨1401677, by rfl⟩ : syracuseStep 1868903 = 2803355) B2803355
theorem B1402015 : Blo 1244440 1402015 := bstep (se 1 (by rfl) ⟨1051511, by rfl⟩ : syracuseStep 1402015 = 2103023) B2103023
theorem B6309089 : Blo 1244440 6309089 := bstep (se 2 (by rfl) ⟨2365908, by rfl⟩ : syracuseStep 6309089 = 4731817) B4731817
theorem B7087499 : Blo 1244440 7087499 := bstep (se 1 (by rfl) ⟨5315624, by rfl⟩ : syracuseStep 7087499 = 10631249) B10631249
theorem B6301151 : Blo 1244440 6301151 := bstep (se 1 (by rfl) ⟨4725863, by rfl⟩ : syracuseStep 6301151 = 9451727) B9451727
theorem B60573203 : Blo 1244440 60573203 := bstep (se 1 (by rfl) ⟨45429902, by rfl⟩ : syracuseStep 60573203 = 90859805) B90859805
theorem B932677163 : Blo 1244440 932677163 := bstep (se 1 (by rfl) ⟨699507872, by rfl⟩ : syracuseStep 932677163 = 1399015745) B1399015745
theorem B26945207 : Blo 1244440 26945207 := bstep (se 1 (by rfl) ⟨20208905, by rfl⟩ : syracuseStep 26945207 = 40417811) B40417811
theorem B4204223 : Blo 1244440 4204223 := bstep (se 1 (by rfl) ⟨3153167, by rfl⟩ : syracuseStep 4204223 = 6306335) B6306335
theorem B17942593 : Blo 1244440 17942593 := bstep (se 2 (by rfl) ⟨6728472, by rfl⟩ : syracuseStep 17942593 = 13456945) B13456945
theorem B14190713 : Blo 1244440 14190713 := bstep (se 2 (by rfl) ⟨5321517, by rfl⟩ : syracuseStep 14190713 = 10643035) B10643035
theorem B4204871 : Blo 1244440 4204871 := bstep (se 1 (by rfl) ⟨3153653, by rfl⟩ : syracuseStep 4204871 = 6307307) B6307307
theorem B6302123 : Blo 1244440 6302123 := bstep (se 1 (by rfl) ⟨4726592, by rfl⟩ : syracuseStep 6302123 = 9453185) B9453185
theorem B15149531 : Blo 1244440 15149531 := bstep (se 1 (by rfl) ⟨11362148, by rfl⟩ : syracuseStep 15149531 = 22724297) B22724297
theorem B1773247 : Blo 1244440 1773247 := bstep (se 1 (by rfl) ⟨1329935, by rfl⟩ : syracuseStep 1773247 = 2659871) B2659871
theorem B14176133 : Blo 1244440 14176133 := bstep (se 4 (by rfl) ⟨1329012, by rfl⟩ : syracuseStep 14176133 = 2658025) B2658025
theorem B21270761 : Blo 1244440 21270761 := bstep (se 2 (by rfl) ⟨7976535, by rfl⟩ : syracuseStep 21270761 = 15953071) B15953071
theorem B10105165 : Blo 1244440 10105165 := bstep (se 3 (by rfl) ⟨1894718, by rfl⟩ : syracuseStep 10105165 = 3789437) B3789437
theorem B7090847 : Blo 1244440 7090847 := bstep (se 1 (by rfl) ⟨5318135, by rfl⟩ : syracuseStep 7090847 = 10636271) B10636271
theorem B4731635 : Blo 1244440 4731635 := bstep (se 1 (by rfl) ⟨3548726, by rfl⟩ : syracuseStep 4731635 = 7097453) B7097453
theorem B4732091 : Blo 1244440 4732091 := bstep (se 1 (by rfl) ⟨3549068, by rfl⟩ : syracuseStep 4732091 = 7098137) B7098137
theorem B1996031 : Blo 1244440 1996031 := bstep (se 1 (by rfl) ⟨1497023, by rfl⟩ : syracuseStep 1996031 = 2994047) B2994047
theorem B7190369 : Blo 1244440 7190369 := bstep (se 2 (by rfl) ⟨2696388, by rfl⟩ : syracuseStep 7190369 = 5392777) B5392777
theorem B2800295 : Blo 1244440 2800295 := bstep (se 1 (by rfl) ⟨2100221, by rfl⟩ : syracuseStep 2800295 = 4200443) B4200443
theorem B14179049 : Blo 1244440 14179049 := bstep (se 2 (by rfl) ⟨5317143, by rfl⟩ : syracuseStep 14179049 = 10634287) B10634287
theorem B2800619 : Blo 1244440 2800619 := bstep (se 1 (by rfl) ⟨2100464, by rfl⟩ : syracuseStep 2800619 = 4200929) B4200929
theorem B1867049 : Blo 1244440 1867049 := bstep (se 2 (by rfl) ⟨700143, by rfl⟩ : syracuseStep 1867049 = 1400287) B1400287
theorem B1244463 : Blo 1244440 1244463 := bstep (se 1 (by rfl) ⟨933347, by rfl⟩ : syracuseStep 1244463 = 1866695) B1866695
theorem B1867055 : Blo 1244440 1867055 := bstep (se 1 (by rfl) ⟨1400291, by rfl⟩ : syracuseStep 1867055 = 2800583) B2800583
theorem B12787139 : Blo 1244440 12787139 := bstep (se 1 (by rfl) ⟨9590354, by rfl⟩ : syracuseStep 12787139 = 19180709) B19180709
theorem B65584835 : Blo 1244440 65584835 := bstep (se 1 (by rfl) ⟨49188626, by rfl⟩ : syracuseStep 65584835 = 98377253) B98377253
theorem B1244879 : Blo 1244440 1244879 := bstep (se 1 (by rfl) ⟨933659, by rfl⟩ : syracuseStep 1244879 = 1867319) B1867319
theorem B35028875 : Blo 1244440 35028875 := bstep (se 1 (by rfl) ⟨26271656, by rfl⟩ : syracuseStep 35028875 = 52543313) B52543313
theorem B1245211 : Blo 1244440 1245211 := bstep (se 1 (by rfl) ⟨933908, by rfl⟩ : syracuseStep 1245211 = 1867817) B1867817
theorem B4489339 : Blo 1244440 4489339 := bstep (se 1 (by rfl) ⟨3367004, by rfl⟩ : syracuseStep 4489339 = 6734009) B6734009
theorem B14180507 : Blo 1244440 14180507 := bstep (se 1 (by rfl) ⟨10635380, by rfl⟩ : syracuseStep 14180507 = 21270761) B21270761
theorem B1245423 : Blo 1244440 1245423 := bstep (se 1 (by rfl) ⟨934067, by rfl⟩ : syracuseStep 1245423 = 1868135) B1868135
theorem B1868027 : Blo 1244440 1868027 := bstep (se 1 (by rfl) ⟨1401020, by rfl⟩ : syracuseStep 1868027 = 2802041) B2802041
theorem B1868153 : Blo 1244440 1868153 := bstep (se 2 (by rfl) ⟨700557, by rfl⟩ : syracuseStep 1868153 = 1401115) B1401115
theorem B15958403 : Blo 1244440 15958403 := bstep (se 1 (by rfl) ⟨11968802, by rfl⟩ : syracuseStep 15958403 = 23937605) B23937605
theorem B4727231 : Blo 1244440 4727231 := bstep (se 1 (by rfl) ⟨3545423, by rfl⟩ : syracuseStep 4727231 = 7090847) B7090847
theorem B3154423 : Blo 1244440 3154423 := bstep (se 1 (by rfl) ⟨2365817, by rfl⟩ : syracuseStep 3154423 = 4731635) B4731635
theorem B1245851 : Blo 1244440 1245851 := bstep (se 1 (by rfl) ⟨934388, by rfl⟩ : syracuseStep 1245851 = 1868777) B1868777
theorem B1245935 : Blo 1244440 1245935 := bstep (se 1 (by rfl) ⟨934451, by rfl⟩ : syracuseStep 1245935 = 1868903) B1868903
theorem B3154727 : Blo 1244440 3154727 := bstep (se 1 (by rfl) ⟨2366045, by rfl⟩ : syracuseStep 3154727 = 4732091) B4732091
theorem B1868921 : Blo 1244440 1868921 := bstep (se 2 (by rfl) ⟨700845, by rfl⟩ : syracuseStep 1868921 = 1401691) B1401691
theorem B2802815 : Blo 1244440 2802815 := bstep (se 1 (by rfl) ⟨2102111, by rfl⟩ : syracuseStep 2802815 = 4204223) B4204223
theorem B4793579 : Blo 1244440 4793579 := bstep (se 1 (by rfl) ⟨3595184, by rfl⟩ : syracuseStep 4793579 = 7190369) B7190369
theorem B1869353 : Blo 1244440 1869353 := bstep (se 2 (by rfl) ⟨701007, by rfl⟩ : syracuseStep 1869353 = 1402015) B1402015
theorem B2803247 : Blo 1244440 2803247 := bstep (se 1 (by rfl) ⟨2102435, by rfl⟩ : syracuseStep 2803247 = 4204871) B4204871
theorem B43723223 : Blo 1244440 43723223 := bstep (se 1 (by rfl) ⟨32792417, by rfl⟩ : syracuseStep 43723223 = 65584835) B65584835
theorem B3238591 : Blo 1244440 3238591 := bstep (se 1 (by rfl) ⟨2428943, by rfl⟩ : syracuseStep 3238591 = 4857887) B4857887
theorem B23923457 : Blo 1244440 23923457 := bstep (se 2 (by rfl) ⟨8971296, by rfl⟩ : syracuseStep 23923457 = 17942593) B17942593
theorem B4206059 : Blo 1244440 4206059 := bstep (se 1 (by rfl) ⟨3154544, by rfl⟩ : syracuseStep 4206059 = 6309089) B6309089
theorem B1330687 : Blo 1244440 1330687 := bstep (se 1 (by rfl) ⟨998015, by rfl⟩ : syracuseStep 1330687 = 1996031) B1996031
theorem B40382135 : Blo 1244440 40382135 := bstep (se 1 (by rfl) ⟨30286601, by rfl⟩ : syracuseStep 40382135 = 60573203) B60573203
theorem B621784775 : Blo 1244440 621784775 := bstep (se 1 (by rfl) ⟨466338581, by rfl⟩ : syracuseStep 621784775 = 932677163) B932677163
theorem B2364329 : Blo 1244440 2364329 := bstep (se 2 (by rfl) ⟨886623, by rfl⟩ : syracuseStep 2364329 = 1773247) B1773247
theorem B8524759 : Blo 1244440 8524759 := bstep (se 1 (by rfl) ⟨6393569, by rfl⟩ : syracuseStep 8524759 = 12787139) B12787139
theorem B93410333 : Blo 1244440 93410333 := bstep (se 3 (by rfl) ⟨17514437, by rfl⟩ : syracuseStep 93410333 = 35028875) B35028875
theorem B9450755 : Blo 1244440 9450755 := bstep (se 1 (by rfl) ⟨7088066, by rfl⟩ : syracuseStep 9450755 = 14176133) B14176133
theorem B13473553 : Blo 1244440 13473553 := bstep (se 2 (by rfl) ⟨5052582, by rfl⟩ : syracuseStep 13473553 = 10105165) B10105165
theorem B4724999 : Blo 1244440 4724999 := bstep (se 1 (by rfl) ⟨3543749, by rfl⟩ : syracuseStep 4724999 = 7087499) B7087499
theorem B4200767 : Blo 1244440 4200767 := bstep (se 1 (by rfl) ⟨3150575, by rfl⟩ : syracuseStep 4200767 = 6301151) B6301151
theorem B17963471 : Blo 1244440 17963471 := bstep (se 1 (by rfl) ⟨13472603, by rfl⟩ : syracuseStep 17963471 = 26945207) B26945207
theorem B9460475 : Blo 1244440 9460475 := bstep (se 1 (by rfl) ⟨7095356, by rfl⟩ : syracuseStep 9460475 = 14190713) B14190713
theorem B4201415 : Blo 1244440 4201415 := bstep (se 1 (by rfl) ⟨3151061, by rfl⟩ : syracuseStep 4201415 = 6302123) B6302123
theorem B10099687 : Blo 1244440 10099687 := bstep (se 1 (by rfl) ⟨7574765, by rfl⟩ : syracuseStep 10099687 = 15149531) B15149531
theorem B1866863 : Blo 1244440 1866863 := bstep (se 1 (by rfl) ⟨1400147, by rfl⟩ : syracuseStep 1866863 = 2800295) B2800295
theorem B9452699 : Blo 1244440 9452699 := bstep (se 1 (by rfl) ⟨7089524, by rfl⟩ : syracuseStep 9452699 = 14179049) B14179049
theorem B1867079 : Blo 1244440 1867079 := bstep (se 1 (by rfl) ⟨1400309, by rfl⟩ : syracuseStep 1867079 = 2800619) B2800619
theorem B1244699 : Blo 1244440 1244699 := bstep (se 1 (by rfl) ⟨933524, by rfl⟩ : syracuseStep 1244699 = 1867049) B1867049
theorem B1244703 : Blo 1244440 1244703 := bstep (se 1 (by rfl) ⟨933527, by rfl⟩ : syracuseStep 1244703 = 1867055) B1867055
theorem B9453671 : Blo 1244440 9453671 := bstep (se 1 (by rfl) ⟨7090253, by rfl⟩ : syracuseStep 9453671 = 14180507) B14180507
theorem B1245351 : Blo 1244440 1245351 := bstep (se 1 (by rfl) ⟨934013, by rfl⟩ : syracuseStep 1245351 = 1868027) B1868027
theorem B1245435 : Blo 1244440 1245435 := bstep (se 1 (by rfl) ⟨934076, by rfl⟩ : syracuseStep 1245435 = 1868153) B1868153
theorem B1245947 : Blo 1244440 1245947 := bstep (se 1 (by rfl) ⟨934460, by rfl⟩ : syracuseStep 1245947 = 1868921) B1868921
theorem B1868543 : Blo 1244440 1868543 := bstep (se 1 (by rfl) ⟨1401407, by rfl⟩ : syracuseStep 1868543 = 2802815) B2802815
theorem B3195719 : Blo 1244440 3195719 := bstep (se 1 (by rfl) ⟨2396789, by rfl⟩ : syracuseStep 3195719 = 4793579) B4793579
theorem B6300503 : Blo 1244440 6300503 := bstep (se 1 (by rfl) ⟨4725377, by rfl⟩ : syracuseStep 6300503 = 9450755) B9450755
theorem B4318121 : Blo 1244440 4318121 := bstep (se 2 (by rfl) ⟨1619295, by rfl⟩ : syracuseStep 4318121 = 3238591) B3238591
theorem B1246235 : Blo 1244440 1246235 := bstep (se 1 (by rfl) ⟨934676, by rfl⟩ : syracuseStep 1246235 = 1869353) B1869353
theorem B1868831 : Blo 1244440 1868831 := bstep (se 1 (by rfl) ⟨1401623, by rfl⟩ : syracuseStep 1868831 = 2803247) B2803247
theorem B29148815 : Blo 1244440 29148815 := bstep (se 1 (by rfl) ⟨21861611, by rfl⟩ : syracuseStep 29148815 = 43723223) B43723223
theorem B6301799 : Blo 1244440 6301799 := bstep (se 1 (by rfl) ⟨4726349, by rfl⟩ : syracuseStep 6301799 = 9452699) B9452699
theorem B2804039 : Blo 1244440 2804039 := bstep (se 1 (by rfl) ⟨2103029, by rfl⟩ : syracuseStep 2804039 = 4206059) B4206059
theorem B26921423 : Blo 1244440 26921423 := bstep (se 1 (by rfl) ⟨20191067, by rfl⟩ : syracuseStep 26921423 = 40382135) B40382135
theorem B7096997 : Blo 1244440 7096997 := bstep (se 4 (by rfl) ⟨665343, by rfl⟩ : syracuseStep 7096997 = 1330687) B1330687
theorem B4205897 : Blo 1244440 4205897 := bstep (se 2 (by rfl) ⟨1577211, by rfl⟩ : syracuseStep 4205897 = 3154423) B3154423
theorem B11366345 : Blo 1244440 11366345 := bstep (se 2 (by rfl) ⟨4262379, by rfl⟩ : syracuseStep 11366345 = 8524759) B8524759
theorem B3149999 : Blo 1244440 3149999 := bstep (se 1 (by rfl) ⟨2362499, by rfl⟩ : syracuseStep 3149999 = 4724999) B4724999
theorem B6304877 : Blo 1244440 6304877 := bstep (se 3 (by rfl) ⟨1182164, by rfl⟩ : syracuseStep 6304877 = 2364329) B2364329
theorem B5985785 : Blo 1244440 5985785 := bstep (se 2 (by rfl) ⟨2244669, by rfl⟩ : syracuseStep 5985785 = 4489339) B4489339
theorem B10638935 : Blo 1244440 10638935 := bstep (se 1 (by rfl) ⟨7979201, by rfl⟩ : syracuseStep 10638935 = 15958403) B15958403
theorem B3151487 : Blo 1244440 3151487 := bstep (se 1 (by rfl) ⟨2363615, by rfl⟩ : syracuseStep 3151487 = 4727231) B4727231
theorem B2103151 : Blo 1244440 2103151 := bstep (se 1 (by rfl) ⟨1577363, by rfl⟩ : syracuseStep 2103151 = 3154727) B3154727
theorem B62273555 : Blo 1244440 62273555 := bstep (se 1 (by rfl) ⟨46705166, by rfl⟩ : syracuseStep 62273555 = 93410333) B93410333
theorem B13466249 : Blo 1244440 13466249 := bstep (se 2 (by rfl) ⟨5049843, by rfl⟩ : syracuseStep 13466249 = 10099687) B10099687
theorem B2800511 : Blo 1244440 2800511 := bstep (se 1 (by rfl) ⟨2100383, by rfl⟩ : syracuseStep 2800511 = 4200767) B4200767
theorem B11975647 : Blo 1244440 11975647 := bstep (se 1 (by rfl) ⟨8981735, by rfl⟩ : syracuseStep 11975647 = 17963471) B17963471
theorem B6306983 : Blo 1244440 6306983 := bstep (se 1 (by rfl) ⟨4730237, by rfl⟩ : syracuseStep 6306983 = 9460475) B9460475
theorem B15948971 : Blo 1244440 15948971 := bstep (se 1 (by rfl) ⟨11961728, by rfl⟩ : syracuseStep 15948971 = 23923457) B23923457
theorem B2800943 : Blo 1244440 2800943 := bstep (se 1 (by rfl) ⟨2100707, by rfl⟩ : syracuseStep 2800943 = 4201415) B4201415
theorem B1244575 : Blo 1244440 1244575 := bstep (se 1 (by rfl) ⟨933431, by rfl⟩ : syracuseStep 1244575 = 1866863) B1866863
theorem B1244719 : Blo 1244440 1244719 := bstep (se 1 (by rfl) ⟨933539, by rfl⟩ : syracuseStep 1244719 = 1867079) B1867079
theorem B17964737 : Blo 1244440 17964737 := bstep (se 2 (by rfl) ⟨6736776, by rfl⟩ : syracuseStep 17964737 = 13473553) B13473553
theorem B414523183 : Blo 1244440 414523183 := bstep (se 1 (by rfl) ⟨310892387, by rfl⟩ : syracuseStep 414523183 = 621784775) B621784775
theorem B1245695 : Blo 1244440 1245695 := bstep (se 1 (by rfl) ⟨934271, by rfl⟩ : syracuseStep 1245695 = 1868543) B1868543
theorem B2130479 : Blo 1244440 2130479 := bstep (se 1 (by rfl) ⟨1597859, by rfl⟩ : syracuseStep 2130479 = 3195719) B3195719
theorem B1245887 : Blo 1244440 1245887 := bstep (se 1 (by rfl) ⟨934415, by rfl⟩ : syracuseStep 1245887 = 1868831) B1868831
theorem B4203251 : Blo 1244440 4203251 := bstep (se 1 (by rfl) ⟨3152438, by rfl⟩ : syracuseStep 4203251 = 6304877) B6304877
theorem B19432543 : Blo 1244440 19432543 := bstep (se 1 (by rfl) ⟨14574407, by rfl⟩ : syracuseStep 19432543 = 29148815) B29148815
theorem B15967529 : Blo 1244440 15967529 := bstep (se 2 (by rfl) ⟨5987823, by rfl⟩ : syracuseStep 15967529 = 11975647) B11975647
theorem B1869359 : Blo 1244440 1869359 := bstep (se 1 (by rfl) ⟨1402019, by rfl⟩ : syracuseStep 1869359 = 2804039) B2804039
theorem B4204655 : Blo 1244440 4204655 := bstep (se 1 (by rfl) ⟨3153491, by rfl⟩ : syracuseStep 4204655 = 6306983) B6306983
theorem B2803931 : Blo 1244440 2803931 := bstep (se 1 (by rfl) ⟨2102948, by rfl⟩ : syracuseStep 2803931 = 4205897) B4205897
theorem B2804201 : Blo 1244440 2804201 := bstep (se 2 (by rfl) ⟨1051575, by rfl⟩ : syracuseStep 2804201 = 2103151) B2103151
theorem B6302447 : Blo 1244440 6302447 := bstep (se 1 (by rfl) ⟨4726835, by rfl⟩ : syracuseStep 6302447 = 9453671) B9453671
theorem B2099999 : Blo 1244440 2099999 := bstep (se 1 (by rfl) ⟨1574999, by rfl⟩ : syracuseStep 2099999 = 3149999) B3149999
theorem B2878747 : Blo 1244440 2878747 := bstep (se 1 (by rfl) ⟨2159060, by rfl⟩ : syracuseStep 2878747 = 4318121) B4318121
theorem B2100991 : Blo 1244440 2100991 := bstep (se 1 (by rfl) ⟨1575743, by rfl⟩ : syracuseStep 2100991 = 3151487) B3151487
theorem B15962093 : Blo 1244440 15962093 := bstep (se 3 (by rfl) ⟨2992892, by rfl⟩ : syracuseStep 15962093 = 5985785) B5985785
theorem B4731331 : Blo 1244440 4731331 := bstep (se 1 (by rfl) ⟨3548498, by rfl⟩ : syracuseStep 4731331 = 7096997) B7096997
theorem B4200335 : Blo 1244440 4200335 := bstep (se 1 (by rfl) ⟨3150251, by rfl⟩ : syracuseStep 4200335 = 6300503) B6300503
theorem B7092623 : Blo 1244440 7092623 := bstep (se 1 (by rfl) ⟨5319467, by rfl⟩ : syracuseStep 7092623 = 10638935) B10638935
theorem B41515703 : Blo 1244440 41515703 := bstep (se 1 (by rfl) ⟨31136777, by rfl⟩ : syracuseStep 41515703 = 62273555) B62273555
theorem B4201199 : Blo 1244440 4201199 := bstep (se 1 (by rfl) ⟨3150899, by rfl⟩ : syracuseStep 4201199 = 6301799) B6301799
theorem B17947615 : Blo 1244440 17947615 := bstep (se 1 (by rfl) ⟨13460711, by rfl⟩ : syracuseStep 17947615 = 26921423) B26921423
theorem B8977499 : Blo 1244440 8977499 := bstep (se 1 (by rfl) ⟨6733124, by rfl⟩ : syracuseStep 8977499 = 13466249) B13466249
theorem B1867007 : Blo 1244440 1867007 := bstep (se 1 (by rfl) ⟨1400255, by rfl⟩ : syracuseStep 1867007 = 2800511) B2800511
theorem B10632647 : Blo 1244440 10632647 := bstep (se 1 (by rfl) ⟨7974485, by rfl⟩ : syracuseStep 10632647 = 15948971) B15948971
theorem B1867295 : Blo 1244440 1867295 := bstep (se 1 (by rfl) ⟨1400471, by rfl⟩ : syracuseStep 1867295 = 2800943) B2800943
theorem B552697577 : Blo 1244440 552697577 := bstep (se 2 (by rfl) ⟨207261591, by rfl⟩ : syracuseStep 552697577 = 414523183) B414523183
theorem B11976491 : Blo 1244440 11976491 := bstep (se 1 (by rfl) ⟨8982368, by rfl⟩ : syracuseStep 11976491 = 17964737) B17964737
theorem B7577563 : Blo 1244440 7577563 := bstep (se 1 (by rfl) ⟨5683172, by rfl⟩ : syracuseStep 7577563 = 11366345) B11366345
theorem B2802167 : Blo 1244440 2802167 := bstep (se 1 (by rfl) ⟨2101625, by rfl⟩ : syracuseStep 2802167 = 4203251) B4203251
theorem B6308441 : Blo 1244440 6308441 := bstep (se 2 (by rfl) ⟨2365665, by rfl⟩ : syracuseStep 6308441 = 4731331) B4731331
theorem B1246239 : Blo 1244440 1246239 := bstep (se 1 (by rfl) ⟨934679, by rfl⟩ : syracuseStep 1246239 = 1869359) B1869359
theorem B23930153 : Blo 1244440 23930153 := bstep (se 2 (by rfl) ⟨8973807, by rfl⟩ : syracuseStep 23930153 = 17947615) B17947615
theorem B2803103 : Blo 1244440 2803103 := bstep (se 1 (by rfl) ⟨2102327, by rfl⟩ : syracuseStep 2803103 = 4204655) B4204655
theorem B15353317 : Blo 1244440 15353317 := bstep (se 4 (by rfl) ⟨1439373, by rfl⟩ : syracuseStep 15353317 = 2878747) B2878747
theorem B1869287 : Blo 1244440 1869287 := bstep (se 1 (by rfl) ⟨1401965, by rfl⟩ : syracuseStep 1869287 = 2803931) B2803931
theorem B4728415 : Blo 1244440 4728415 := bstep (se 1 (by rfl) ⟨3546311, by rfl⟩ : syracuseStep 4728415 = 7092623) B7092623
theorem B1869467 : Blo 1244440 1869467 := bstep (se 1 (by rfl) ⟨1402100, by rfl⟩ : syracuseStep 1869467 = 2804201) B2804201
theorem B7088431 : Blo 1244440 7088431 := bstep (se 1 (by rfl) ⟨5316323, by rfl⟩ : syracuseStep 7088431 = 10632647) B10632647
theorem B10103417 : Blo 1244440 10103417 := bstep (se 2 (by rfl) ⟨3788781, by rfl⟩ : syracuseStep 10103417 = 7577563) B7577563
theorem B1420319 : Blo 1244440 1420319 := bstep (se 1 (by rfl) ⟨1065239, by rfl⟩ : syracuseStep 1420319 = 2130479) B2130479
theorem B10645019 : Blo 1244440 10645019 := bstep (se 1 (by rfl) ⟨7983764, by rfl⟩ : syracuseStep 10645019 = 15967529) B15967529
theorem B27677135 : Blo 1244440 27677135 := bstep (se 1 (by rfl) ⟨20757851, by rfl⟩ : syracuseStep 27677135 = 41515703) B41515703
theorem B5984999 : Blo 1244440 5984999 := bstep (se 1 (by rfl) ⟨4488749, by rfl⟩ : syracuseStep 5984999 = 8977499) B8977499
theorem B368465051 : Blo 1244440 368465051 := bstep (se 1 (by rfl) ⟨276348788, by rfl⟩ : syracuseStep 368465051 = 552697577) B552697577
theorem B7984327 : Blo 1244440 7984327 := bstep (se 1 (by rfl) ⟨5988245, by rfl⟩ : syracuseStep 7984327 = 11976491) B11976491
theorem B2800223 : Blo 1244440 2800223 := bstep (se 1 (by rfl) ⟨2100167, by rfl⟩ : syracuseStep 2800223 = 4200335) B4200335
theorem B25910057 : Blo 1244440 25910057 := bstep (se 2 (by rfl) ⟨9716271, by rfl⟩ : syracuseStep 25910057 = 19432543) B19432543
theorem B2800799 : Blo 1244440 2800799 := bstep (se 1 (by rfl) ⟨2100599, by rfl⟩ : syracuseStep 2800799 = 4201199) B4201199
theorem B4201631 : Blo 1244440 4201631 := bstep (se 1 (by rfl) ⟨3151223, by rfl⟩ : syracuseStep 4201631 = 6302447) B6302447
theorem B1399999 : Blo 1244440 1399999 := bstep (se 1 (by rfl) ⟨1049999, by rfl⟩ : syracuseStep 1399999 = 2099999) B2099999
theorem B1244671 : Blo 1244440 1244671 := bstep (se 1 (by rfl) ⟨933503, by rfl⟩ : syracuseStep 1244671 = 1867007) B1867007
theorem B2801321 : Blo 1244440 2801321 := bstep (se 2 (by rfl) ⟨1050495, by rfl⟩ : syracuseStep 2801321 = 2100991) B2100991
theorem B1244863 : Blo 1244440 1244863 := bstep (se 1 (by rfl) ⟨933647, by rfl⟩ : syracuseStep 1244863 = 1867295) B1867295
theorem B10641395 : Blo 1244440 10641395 := bstep (se 1 (by rfl) ⟨7981046, by rfl⟩ : syracuseStep 10641395 = 15962093) B15962093
theorem B1868111 : Blo 1244440 1868111 := bstep (se 1 (by rfl) ⟨1401083, by rfl⟩ : syracuseStep 1868111 = 2802167) B2802167
theorem B7094263 : Blo 1244440 7094263 := bstep (se 1 (by rfl) ⟨5320697, by rfl⟩ : syracuseStep 7094263 = 10641395) B10641395
theorem B3989999 : Blo 1244440 3989999 := bstep (se 1 (by rfl) ⟨2992499, by rfl⟩ : syracuseStep 3989999 = 5984999) B5984999
theorem B1868735 : Blo 1244440 1868735 := bstep (se 1 (by rfl) ⟨1401551, by rfl⟩ : syracuseStep 1868735 = 2803103) B2803103
theorem B1246191 : Blo 1244440 1246191 := bstep (se 1 (by rfl) ⟨934643, by rfl⟩ : syracuseStep 1246191 = 1869287) B1869287
theorem B1246311 : Blo 1244440 1246311 := bstep (se 1 (by rfl) ⟨934733, by rfl⟩ : syracuseStep 1246311 = 1869467) B1869467
theorem B6735611 : Blo 1244440 6735611 := bstep (se 1 (by rfl) ⟨5051708, by rfl⟩ : syracuseStep 6735611 = 10103417) B10103417
theorem B7096679 : Blo 1244440 7096679 := bstep (se 1 (by rfl) ⟨5322509, by rfl⟩ : syracuseStep 7096679 = 10645019) B10645019
theorem B3787517 : Blo 1244440 3787517 := bstep (se 3 (by rfl) ⟨710159, by rfl⟩ : syracuseStep 3787517 = 1420319) B1420319
theorem B18451423 : Blo 1244440 18451423 := bstep (se 1 (by rfl) ⟨13838567, by rfl⟩ : syracuseStep 18451423 = 27677135) B27677135
theorem B4205627 : Blo 1244440 4205627 := bstep (se 1 (by rfl) ⟨3154220, by rfl⟩ : syracuseStep 4205627 = 6308441) B6308441
theorem B15953435 : Blo 1244440 15953435 := bstep (se 1 (by rfl) ⟨11965076, by rfl⟩ : syracuseStep 15953435 = 23930153) B23930153
theorem B10645769 : Blo 1244440 10645769 := bstep (se 2 (by rfl) ⟨3992163, by rfl⟩ : syracuseStep 10645769 = 7984327) B7984327
theorem B17273371 : Blo 1244440 17273371 := bstep (se 1 (by rfl) ⟨12955028, by rfl⟩ : syracuseStep 17273371 = 25910057) B25910057
theorem B6304553 : Blo 1244440 6304553 := bstep (se 2 (by rfl) ⟨2364207, by rfl⟩ : syracuseStep 6304553 = 4728415) B4728415
theorem B81884357 : Blo 1244440 81884357 := bstep (se 4 (by rfl) ⟨7676658, by rfl⟩ : syracuseStep 81884357 = 15353317) B15353317
theorem B9451241 : Blo 1244440 9451241 := bstep (se 2 (by rfl) ⟨3544215, by rfl⟩ : syracuseStep 9451241 = 7088431) B7088431
theorem B245643367 : Blo 1244440 245643367 := bstep (se 1 (by rfl) ⟨184232525, by rfl⟩ : syracuseStep 245643367 = 368465051) B368465051
theorem B1866665 : Blo 1244440 1866665 := bstep (se 2 (by rfl) ⟨699999, by rfl⟩ : syracuseStep 1866665 = 1399999) B1399999
theorem B1866815 : Blo 1244440 1866815 := bstep (se 1 (by rfl) ⟨1400111, by rfl⟩ : syracuseStep 1866815 = 2800223) B2800223
theorem B1867199 : Blo 1244440 1867199 := bstep (se 1 (by rfl) ⟨1400399, by rfl⟩ : syracuseStep 1867199 = 2800799) B2800799
theorem B2801087 : Blo 1244440 2801087 := bstep (se 1 (by rfl) ⟨2100815, by rfl⟩ : syracuseStep 2801087 = 4201631) B4201631
theorem B1867547 : Blo 1244440 1867547 := bstep (se 1 (by rfl) ⟨1400660, by rfl⟩ : syracuseStep 1867547 = 2801321) B2801321
theorem B327524489 : Blo 1244440 327524489 := bstep (se 2 (by rfl) ⟨122821683, by rfl⟩ : syracuseStep 327524489 = 245643367) B245643367
theorem B1245407 : Blo 1244440 1245407 := bstep (se 1 (by rfl) ⟨934055, by rfl⟩ : syracuseStep 1245407 = 1868111) B1868111
theorem B4203035 : Blo 1244440 4203035 := bstep (se 1 (by rfl) ⟨3152276, by rfl⟩ : syracuseStep 4203035 = 6304553) B6304553
theorem B1245823 : Blo 1244440 1245823 := bstep (se 1 (by rfl) ⟨934367, by rfl⟩ : syracuseStep 1245823 = 1868735) B1868735
theorem B6300827 : Blo 1244440 6300827 := bstep (se 1 (by rfl) ⟨4725620, by rfl⟩ : syracuseStep 6300827 = 9451241) B9451241
theorem B4490407 : Blo 1244440 4490407 := bstep (se 1 (by rfl) ⟨3367805, by rfl⟩ : syracuseStep 4490407 = 6735611) B6735611
theorem B24601897 : Blo 1244440 24601897 := bstep (se 2 (by rfl) ⟨9225711, by rfl⟩ : syracuseStep 24601897 = 18451423) B18451423
theorem B2803751 : Blo 1244440 2803751 := bstep (se 1 (by rfl) ⟨2102813, by rfl⟩ : syracuseStep 2803751 = 4205627) B4205627
theorem B10635623 : Blo 1244440 10635623 := bstep (se 1 (by rfl) ⟨7976717, by rfl⟩ : syracuseStep 10635623 = 15953435) B15953435
theorem B7097179 : Blo 1244440 7097179 := bstep (se 1 (by rfl) ⟨5322884, by rfl⟩ : syracuseStep 7097179 = 10645769) B10645769
theorem B23031161 : Blo 1244440 23031161 := bstep (se 2 (by rfl) ⟨8636685, by rfl⟩ : syracuseStep 23031161 = 17273371) B17273371
theorem B4731119 : Blo 1244440 4731119 := bstep (se 1 (by rfl) ⟨3548339, by rfl⟩ : syracuseStep 4731119 = 7096679) B7096679
theorem B9459017 : Blo 1244440 9459017 := bstep (se 2 (by rfl) ⟨3547131, by rfl⟩ : syracuseStep 9459017 = 7094263) B7094263
theorem B54589571 : Blo 1244440 54589571 := bstep (se 1 (by rfl) ⟨40942178, by rfl⟩ : syracuseStep 54589571 = 81884357) B81884357
theorem B10639997 : Blo 1244440 10639997 := bstep (se 3 (by rfl) ⟨1994999, by rfl⟩ : syracuseStep 10639997 = 3989999) B3989999
theorem B1244443 : Blo 1244440 1244443 := bstep (se 1 (by rfl) ⟨933332, by rfl⟩ : syracuseStep 1244443 = 1866665) B1866665
theorem B10100045 : Blo 1244440 10100045 := bstep (se 3 (by rfl) ⟨1893758, by rfl⟩ : syracuseStep 10100045 = 3787517) B3787517
theorem B1244543 : Blo 1244440 1244543 := bstep (se 1 (by rfl) ⟨933407, by rfl⟩ : syracuseStep 1244543 = 1866815) B1866815
theorem B1244799 : Blo 1244440 1244799 := bstep (se 1 (by rfl) ⟨933599, by rfl⟩ : syracuseStep 1244799 = 1867199) B1867199
theorem B1867391 : Blo 1244440 1867391 := bstep (se 1 (by rfl) ⟨1400543, by rfl⟩ : syracuseStep 1867391 = 2801087) B2801087
theorem B1245031 : Blo 1244440 1245031 := bstep (se 1 (by rfl) ⟨933773, by rfl⟩ : syracuseStep 1245031 = 1867547) B1867547
theorem B218349659 : Blo 1244440 218349659 := bstep (se 1 (by rfl) ⟨163762244, by rfl⟩ : syracuseStep 218349659 = 327524489) B327524489
theorem B2802023 : Blo 1244440 2802023 := bstep (se 1 (by rfl) ⟨2101517, by rfl⟩ : syracuseStep 2802023 = 4203035) B4203035
theorem B3154079 : Blo 1244440 3154079 := bstep (se 1 (by rfl) ⟨2365559, by rfl⟩ : syracuseStep 3154079 = 4731119) B4731119
theorem B9462905 : Blo 1244440 9462905 := bstep (se 2 (by rfl) ⟨3548589, by rfl⟩ : syracuseStep 9462905 = 7097179) B7097179
theorem B1869167 : Blo 1244440 1869167 := bstep (se 1 (by rfl) ⟨1401875, by rfl⟩ : syracuseStep 1869167 = 2803751) B2803751
theorem B32802529 : Blo 1244440 32802529 := bstep (se 2 (by rfl) ⟨12300948, by rfl⟩ : syracuseStep 32802529 = 24601897) B24601897
theorem B15354107 : Blo 1244440 15354107 := bstep (se 1 (by rfl) ⟨11515580, by rfl⟩ : syracuseStep 15354107 = 23031161) B23031161
theorem B36393047 : Blo 1244440 36393047 := bstep (se 1 (by rfl) ⟨27294785, by rfl⟩ : syracuseStep 36393047 = 54589571) B54589571
theorem B7090415 : Blo 1244440 7090415 := bstep (se 1 (by rfl) ⟨5317811, by rfl⟩ : syracuseStep 7090415 = 10635623) B10635623
theorem B4200551 : Blo 1244440 4200551 := bstep (se 1 (by rfl) ⟨3150413, by rfl⟩ : syracuseStep 4200551 = 6300827) B6300827
theorem B6306011 : Blo 1244440 6306011 := bstep (se 1 (by rfl) ⟨4729508, by rfl⟩ : syracuseStep 6306011 = 9459017) B9459017
theorem B5987209 : Blo 1244440 5987209 := bstep (se 2 (by rfl) ⟨2245203, by rfl⟩ : syracuseStep 5987209 = 4490407) B4490407
theorem B7093331 : Blo 1244440 7093331 := bstep (se 1 (by rfl) ⟨5319998, by rfl⟩ : syracuseStep 7093331 = 10639997) B10639997
theorem B6733363 : Blo 1244440 6733363 := bstep (se 1 (by rfl) ⟨5050022, by rfl⟩ : syracuseStep 6733363 = 10100045) B10100045
theorem B1244927 : Blo 1244440 1244927 := bstep (se 1 (by rfl) ⟨933695, by rfl⟩ : syracuseStep 1244927 = 1867391) B1867391
theorem B4726943 : Blo 1244440 4726943 := bstep (se 1 (by rfl) ⟨3545207, by rfl⟩ : syracuseStep 4726943 = 7090415) B7090415
theorem B1868015 : Blo 1244440 1868015 := bstep (se 1 (by rfl) ⟨1401011, by rfl⟩ : syracuseStep 1868015 = 2802023) B2802023
theorem B6308603 : Blo 1244440 6308603 := bstep (se 1 (by rfl) ⟨4731452, by rfl⟩ : syracuseStep 6308603 = 9462905) B9462905
theorem B1246111 : Blo 1244440 1246111 := bstep (se 1 (by rfl) ⟨934583, by rfl⟩ : syracuseStep 1246111 = 1869167) B1869167
theorem B4204007 : Blo 1244440 4204007 := bstep (se 1 (by rfl) ⟨3153005, by rfl⟩ : syracuseStep 4204007 = 6306011) B6306011
theorem B4728887 : Blo 1244440 4728887 := bstep (se 1 (by rfl) ⟨3546665, by rfl⟩ : syracuseStep 4728887 = 7093331) B7093331
theorem B145566439 : Blo 1244440 145566439 := bstep (se 1 (by rfl) ⟨109174829, by rfl⟩ : syracuseStep 145566439 = 218349659) B218349659
theorem B7982945 : Blo 1244440 7982945 := bstep (se 2 (by rfl) ⟨2993604, by rfl⟩ : syracuseStep 7982945 = 5987209) B5987209
theorem B10236071 : Blo 1244440 10236071 := bstep (se 1 (by rfl) ⟨7677053, by rfl⟩ : syracuseStep 10236071 = 15354107) B15354107
theorem B24262031 : Blo 1244440 24262031 := bstep (se 1 (by rfl) ⟨18196523, by rfl⟩ : syracuseStep 24262031 = 36393047) B36393047
theorem B2102719 : Blo 1244440 2102719 := bstep (se 1 (by rfl) ⟨1577039, by rfl⟩ : syracuseStep 2102719 = 3154079) B3154079
theorem B2800367 : Blo 1244440 2800367 := bstep (se 1 (by rfl) ⟨2100275, by rfl⟩ : syracuseStep 2800367 = 4200551) B4200551
theorem B8977817 : Blo 1244440 8977817 := bstep (se 2 (by rfl) ⟨3366681, by rfl⟩ : syracuseStep 8977817 = 6733363) B6733363
theorem B43736705 : Blo 1244440 43736705 := bstep (se 2 (by rfl) ⟨16401264, by rfl⟩ : syracuseStep 43736705 = 32802529) B32802529
theorem B1245343 : Blo 1244440 1245343 := bstep (se 1 (by rfl) ⟨934007, by rfl⟩ : syracuseStep 1245343 = 1868015) B1868015
theorem B27296189 : Blo 1244440 27296189 := bstep (se 3 (by rfl) ⟨5118035, by rfl⟩ : syracuseStep 27296189 = 10236071) B10236071
theorem B2802671 : Blo 1244440 2802671 := bstep (se 1 (by rfl) ⟨2102003, by rfl⟩ : syracuseStep 2802671 = 4204007) B4204007
theorem B2803625 : Blo 1244440 2803625 := bstep (se 2 (by rfl) ⟨1051359, by rfl⟩ : syracuseStep 2803625 = 2102719) B2102719
theorem B29157803 : Blo 1244440 29157803 := bstep (se 1 (by rfl) ⟨21868352, by rfl⟩ : syracuseStep 29157803 = 43736705) B43736705
theorem B4205735 : Blo 1244440 4205735 := bstep (se 1 (by rfl) ⟨3154301, by rfl⟩ : syracuseStep 4205735 = 6308603) B6308603
theorem B16174687 : Blo 1244440 16174687 := bstep (se 1 (by rfl) ⟨12131015, by rfl⟩ : syracuseStep 16174687 = 24262031) B24262031
theorem B5985211 : Blo 1244440 5985211 := bstep (se 1 (by rfl) ⟨4488908, by rfl⟩ : syracuseStep 5985211 = 8977817) B8977817
theorem B5321963 : Blo 1244440 5321963 := bstep (se 1 (by rfl) ⟨3991472, by rfl⟩ : syracuseStep 5321963 = 7982945) B7982945
theorem B3151295 : Blo 1244440 3151295 := bstep (se 1 (by rfl) ⟨2363471, by rfl⟩ : syracuseStep 3151295 = 4726943) B4726943
theorem B776354341 : Blo 1244440 776354341 := bstep (se 4 (by rfl) ⟨72783219, by rfl⟩ : syracuseStep 776354341 = 145566439) B145566439
theorem B3152591 : Blo 1244440 3152591 := bstep (se 1 (by rfl) ⟨2364443, by rfl⟩ : syracuseStep 3152591 = 4728887) B4728887
theorem B1866911 : Blo 1244440 1866911 := bstep (se 1 (by rfl) ⟨1400183, by rfl⟩ : syracuseStep 1866911 = 2800367) B2800367
theorem B1868447 : Blo 1244440 1868447 := bstep (se 1 (by rfl) ⟨1401335, by rfl⟩ : syracuseStep 1868447 = 2802671) B2802671
theorem B3547975 : Blo 1244440 3547975 := bstep (se 1 (by rfl) ⟨2660981, by rfl⟩ : syracuseStep 3547975 = 5321963) B5321963
theorem B7980281 : Blo 1244440 7980281 := bstep (se 2 (by rfl) ⟨2992605, by rfl⟩ : syracuseStep 7980281 = 5985211) B5985211
theorem B1869083 : Blo 1244440 1869083 := bstep (se 1 (by rfl) ⟨1401812, by rfl⟩ : syracuseStep 1869083 = 2803625) B2803625
theorem B2803823 : Blo 1244440 2803823 := bstep (se 1 (by rfl) ⟨2102867, by rfl⟩ : syracuseStep 2803823 = 4205735) B4205735
theorem B18197459 : Blo 1244440 18197459 := bstep (se 1 (by rfl) ⟨13648094, by rfl⟩ : syracuseStep 18197459 = 27296189) B27296189
theorem B2100863 : Blo 1244440 2100863 := bstep (se 1 (by rfl) ⟨1575647, by rfl⟩ : syracuseStep 2100863 = 3151295) B3151295
theorem B2101727 : Blo 1244440 2101727 := bstep (se 1 (by rfl) ⟨1576295, by rfl⟩ : syracuseStep 2101727 = 3152591) B3152591
theorem B21566249 : Blo 1244440 21566249 := bstep (se 2 (by rfl) ⟨8087343, by rfl⟩ : syracuseStep 21566249 = 16174687) B16174687
theorem B1035139121 : Blo 1244440 1035139121 := bstep (se 2 (by rfl) ⟨388177170, by rfl⟩ : syracuseStep 1035139121 = 776354341) B776354341
theorem B19438535 : Blo 1244440 19438535 := bstep (se 1 (by rfl) ⟨14578901, by rfl⟩ : syracuseStep 19438535 = 29157803) B29157803
theorem B1244607 : Blo 1244440 1244607 := bstep (se 1 (by rfl) ⟨933455, by rfl⟩ : syracuseStep 1244607 = 1866911) B1866911
theorem B1401151 : Blo 1244440 1401151 := bstep (se 1 (by rfl) ⟨1050863, by rfl⟩ : syracuseStep 1401151 = 2101727) B2101727
theorem B1245631 : Blo 1244440 1245631 := bstep (se 1 (by rfl) ⟨934223, by rfl⟩ : syracuseStep 1245631 = 1868447) B1868447
theorem B14377499 : Blo 1244440 14377499 := bstep (se 1 (by rfl) ⟨10783124, by rfl⟩ : syracuseStep 14377499 = 21566249) B21566249
theorem B1246055 : Blo 1244440 1246055 := bstep (se 1 (by rfl) ⟨934541, by rfl⟩ : syracuseStep 1246055 = 1869083) B1869083
theorem B1869215 : Blo 1244440 1869215 := bstep (se 1 (by rfl) ⟨1401911, by rfl⟩ : syracuseStep 1869215 = 2803823) B2803823
theorem B5320187 : Blo 1244440 5320187 := bstep (se 1 (by rfl) ⟨3990140, by rfl⟩ : syracuseStep 5320187 = 7980281) B7980281
theorem B4730633 : Blo 1244440 4730633 := bstep (se 2 (by rfl) ⟨1773987, by rfl⟩ : syracuseStep 4730633 = 3547975) B3547975
theorem B690092747 : Blo 1244440 690092747 := bstep (se 1 (by rfl) ⟨517569560, by rfl⟩ : syracuseStep 690092747 = 1035139121) B1035139121
theorem B12959023 : Blo 1244440 12959023 := bstep (se 1 (by rfl) ⟨9719267, by rfl⟩ : syracuseStep 12959023 = 19438535) B19438535
theorem B12131639 : Blo 1244440 12131639 := bstep (se 1 (by rfl) ⟨9098729, by rfl⟩ : syracuseStep 12131639 = 18197459) B18197459
theorem B1400575 : Blo 1244440 1400575 := bstep (se 1 (by rfl) ⟨1050431, by rfl⟩ : syracuseStep 1400575 = 2100863) B2100863
theorem B9584999 : Blo 1244440 9584999 := bstep (se 1 (by rfl) ⟨7188749, by rfl⟩ : syracuseStep 9584999 = 14377499) B14377499
theorem B1868201 : Blo 1244440 1868201 := bstep (se 2 (by rfl) ⟨700575, by rfl⟩ : syracuseStep 1868201 = 1401151) B1401151
theorem B1246143 : Blo 1244440 1246143 := bstep (se 1 (by rfl) ⟨934607, by rfl⟩ : syracuseStep 1246143 = 1869215) B1869215
theorem B17278697 : Blo 1244440 17278697 := bstep (se 2 (by rfl) ⟨6479511, by rfl⟩ : syracuseStep 17278697 = 12959023) B12959023
theorem B8087759 : Blo 1244440 8087759 := bstep (se 1 (by rfl) ⟨6065819, by rfl⟩ : syracuseStep 8087759 = 12131639) B12131639
theorem B460061831 : Blo 1244440 460061831 := bstep (se 1 (by rfl) ⟨345046373, by rfl⟩ : syracuseStep 460061831 = 690092747) B690092747
theorem B3546791 : Blo 1244440 3546791 := bstep (se 1 (by rfl) ⟨2660093, by rfl⟩ : syracuseStep 3546791 = 5320187) B5320187
theorem B1867433 : Blo 1244440 1867433 := bstep (se 2 (by rfl) ⟨700287, by rfl⟩ : syracuseStep 1867433 = 1400575) B1400575
theorem B3153755 : Blo 1244440 3153755 := bstep (se 1 (by rfl) ⟨2365316, by rfl⟩ : syracuseStep 3153755 = 4730633) B4730633
theorem B6389999 : Blo 1244440 6389999 := bstep (se 1 (by rfl) ⟨4792499, by rfl⟩ : syracuseStep 6389999 = 9584999) B9584999
theorem B1245467 : Blo 1244440 1245467 := bstep (se 1 (by rfl) ⟨934100, by rfl⟩ : syracuseStep 1245467 = 1868201) B1868201
theorem B11519131 : Blo 1244440 11519131 := bstep (se 1 (by rfl) ⟨8639348, by rfl⟩ : syracuseStep 11519131 = 17278697) B17278697
theorem B5391839 : Blo 1244440 5391839 := bstep (se 1 (by rfl) ⟨4043879, by rfl⟩ : syracuseStep 5391839 = 8087759) B8087759
theorem B2364527 : Blo 1244440 2364527 := bstep (se 1 (by rfl) ⟨1773395, by rfl⟩ : syracuseStep 2364527 = 3546791) B3546791
theorem B2102503 : Blo 1244440 2102503 := bstep (se 1 (by rfl) ⟨1576877, by rfl⟩ : syracuseStep 2102503 = 3153755) B3153755
theorem B306707887 : Blo 1244440 306707887 := bstep (se 1 (by rfl) ⟨230030915, by rfl⟩ : syracuseStep 306707887 = 460061831) B460061831
theorem B1244955 : Blo 1244440 1244955 := bstep (se 1 (by rfl) ⟨933716, by rfl⟩ : syracuseStep 1244955 = 1867433) B1867433
theorem B4259999 : Blo 1244440 4259999 := bstep (se 1 (by rfl) ⟨3194999, by rfl⟩ : syracuseStep 4259999 = 6389999) B6389999
theorem B2803337 : Blo 1244440 2803337 := bstep (se 2 (by rfl) ⟨1051251, by rfl⟩ : syracuseStep 2803337 = 2102503) B2102503
theorem B1576351 : Blo 1244440 1576351 := bstep (se 1 (by rfl) ⟨1182263, by rfl⟩ : syracuseStep 1576351 = 2364527) B2364527
theorem B3594559 : Blo 1244440 3594559 := bstep (se 1 (by rfl) ⟨2695919, by rfl⟩ : syracuseStep 3594559 = 5391839) B5391839
theorem B15358841 : Blo 1244440 15358841 := bstep (se 2 (by rfl) ⟨5759565, by rfl⟩ : syracuseStep 15358841 = 11519131) B11519131
theorem B408943849 : Blo 1244440 408943849 := bstep (se 2 (by rfl) ⟨153353943, by rfl⟩ : syracuseStep 408943849 = 306707887) B306707887
theorem B4792745 : Blo 1244440 4792745 := bstep (se 2 (by rfl) ⟨1797279, by rfl⟩ : syracuseStep 4792745 = 3594559) B3594559
theorem B1868891 : Blo 1244440 1868891 := bstep (se 1 (by rfl) ⟨1401668, by rfl⟩ : syracuseStep 1868891 = 2803337) B2803337
theorem B2101801 : Blo 1244440 2101801 := bstep (se 2 (by rfl) ⟨788175, by rfl⟩ : syracuseStep 2101801 = 1576351) B1576351
theorem B11359997 : Blo 1244440 11359997 := bstep (se 3 (by rfl) ⟨2129999, by rfl⟩ : syracuseStep 11359997 = 4259999) B4259999
theorem B545258465 : Blo 1244440 545258465 := bstep (se 2 (by rfl) ⟨204471924, by rfl⟩ : syracuseStep 545258465 = 408943849) B408943849
theorem B10239227 : Blo 1244440 10239227 := bstep (se 1 (by rfl) ⟨7679420, by rfl⟩ : syracuseStep 10239227 = 15358841) B15358841
theorem B3195163 : Blo 1244440 3195163 := bstep (se 1 (by rfl) ⟨2396372, by rfl⟩ : syracuseStep 3195163 = 4792745) B4792745
theorem B2802401 : Blo 1244440 2802401 := bstep (se 2 (by rfl) ⟨1050900, by rfl⟩ : syracuseStep 2802401 = 2101801) B2101801
theorem B1245927 : Blo 1244440 1245927 := bstep (se 1 (by rfl) ⟨934445, by rfl⟩ : syracuseStep 1245927 = 1868891) B1868891
theorem B363505643 : Blo 1244440 363505643 := bstep (se 1 (by rfl) ⟨272629232, by rfl⟩ : syracuseStep 363505643 = 545258465) B545258465
theorem B6826151 : Blo 1244440 6826151 := bstep (se 1 (by rfl) ⟨5119613, by rfl⟩ : syracuseStep 6826151 = 10239227) B10239227
theorem B7573331 : Blo 1244440 7573331 := bstep (se 1 (by rfl) ⟨5679998, by rfl⟩ : syracuseStep 7573331 = 11359997) B11359997
theorem B4260217 : Blo 1244440 4260217 := bstep (se 2 (by rfl) ⟨1597581, by rfl⟩ : syracuseStep 4260217 = 3195163) B3195163
theorem B18203069 : Blo 1244440 18203069 := bstep (se 3 (by rfl) ⟨3413075, by rfl⟩ : syracuseStep 18203069 = 6826151) B6826151
theorem B1868267 : Blo 1244440 1868267 := bstep (se 1 (by rfl) ⟨1401200, by rfl⟩ : syracuseStep 1868267 = 2802401) B2802401
theorem B242337095 : Blo 1244440 242337095 := bstep (se 1 (by rfl) ⟨181752821, by rfl⟩ : syracuseStep 242337095 = 363505643) B363505643
theorem B5048887 : Blo 1244440 5048887 := bstep (se 1 (by rfl) ⟨3786665, by rfl⟩ : syracuseStep 5048887 = 7573331) B7573331
theorem B1245511 : Blo 1244440 1245511 := bstep (se 1 (by rfl) ⟨934133, by rfl⟩ : syracuseStep 1245511 = 1868267) B1868267
theorem B12135379 : Blo 1244440 12135379 := bstep (se 1 (by rfl) ⟨9101534, by rfl⟩ : syracuseStep 12135379 = 18203069) B18203069
theorem B5680289 : Blo 1244440 5680289 := bstep (se 2 (by rfl) ⟨2130108, by rfl⟩ : syracuseStep 5680289 = 4260217) B4260217
theorem B161558063 : Blo 1244440 161558063 := bstep (se 1 (by rfl) ⟨121168547, by rfl⟩ : syracuseStep 161558063 = 242337095) B242337095
theorem B6731849 : Blo 1244440 6731849 := bstep (se 2 (by rfl) ⟨2524443, by rfl⟩ : syracuseStep 6731849 = 5048887) B5048887
theorem B16180505 : Blo 1244440 16180505 := bstep (se 2 (by rfl) ⟨6067689, by rfl⟩ : syracuseStep 16180505 = 12135379) B12135379
theorem B3786859 : Blo 1244440 3786859 := bstep (se 1 (by rfl) ⟨2840144, by rfl⟩ : syracuseStep 3786859 = 5680289) B5680289
theorem B107705375 : Blo 1244440 107705375 := bstep (se 1 (by rfl) ⟨80779031, by rfl⟩ : syracuseStep 107705375 = 161558063) B161558063
theorem B4487899 : Blo 1244440 4487899 := bstep (se 1 (by rfl) ⟨3365924, by rfl⟩ : syracuseStep 4487899 = 6731849) B6731849
theorem B71803583 : Blo 1244440 71803583 := bstep (se 1 (by rfl) ⟨53852687, by rfl⟩ : syracuseStep 71803583 = 107705375) B107705375
theorem B5049145 : Blo 1244440 5049145 := bstep (se 2 (by rfl) ⟨1893429, by rfl⟩ : syracuseStep 5049145 = 3786859) B3786859
theorem B5983865 : Blo 1244440 5983865 := bstep (se 2 (by rfl) ⟨2243949, by rfl⟩ : syracuseStep 5983865 = 4487899) B4487899
theorem B10787003 : Blo 1244440 10787003 := bstep (se 1 (by rfl) ⟨8090252, by rfl⟩ : syracuseStep 10787003 = 16180505) B16180505
theorem B26928773 : Blo 1244440 26928773 := bstep (se 4 (by rfl) ⟨2524572, by rfl⟩ : syracuseStep 26928773 = 5049145) B5049145
theorem B47869055 : Blo 1244440 47869055 := bstep (se 1 (by rfl) ⟨35901791, by rfl⟩ : syracuseStep 47869055 = 71803583) B71803583
theorem B7191335 : Blo 1244440 7191335 := bstep (se 1 (by rfl) ⟨5393501, by rfl⟩ : syracuseStep 7191335 = 10787003) B10787003
theorem B3989243 : Blo 1244440 3989243 := bstep (se 1 (by rfl) ⟨2991932, by rfl⟩ : syracuseStep 3989243 = 5983865) B5983865
theorem B4794223 : Blo 1244440 4794223 := bstep (se 1 (by rfl) ⟨3595667, by rfl⟩ : syracuseStep 4794223 = 7191335) B7191335
theorem B17952515 : Blo 1244440 17952515 := bstep (se 1 (by rfl) ⟨13464386, by rfl⟩ : syracuseStep 17952515 = 26928773) B26928773
theorem B31912703 : Blo 1244440 31912703 := bstep (se 1 (by rfl) ⟨23934527, by rfl⟩ : syracuseStep 31912703 = 47869055) B47869055
theorem B2659495 : Blo 1244440 2659495 := bstep (se 1 (by rfl) ⟨1994621, by rfl⟩ : syracuseStep 2659495 = 3989243) B3989243
theorem B21275135 : Blo 1244440 21275135 := bstep (se 1 (by rfl) ⟨15956351, by rfl⟩ : syracuseStep 21275135 = 31912703) B31912703
theorem B6392297 : Blo 1244440 6392297 := bstep (se 2 (by rfl) ⟨2397111, by rfl⟩ : syracuseStep 6392297 = 4794223) B4794223
theorem B3545993 : Blo 1244440 3545993 := bstep (se 2 (by rfl) ⟨1329747, by rfl⟩ : syracuseStep 3545993 = 2659495) B2659495
theorem B11968343 : Blo 1244440 11968343 := bstep (se 1 (by rfl) ⟨8976257, by rfl⟩ : syracuseStep 11968343 = 17952515) B17952515
theorem B4261531 : Blo 1244440 4261531 := bstep (se 1 (by rfl) ⟨3196148, by rfl⟩ : syracuseStep 4261531 = 6392297) B6392297
theorem B14183423 : Blo 1244440 14183423 := bstep (se 1 (by rfl) ⟨10637567, by rfl⟩ : syracuseStep 14183423 = 21275135) B21275135
theorem B2363995 : Blo 1244440 2363995 := bstep (se 1 (by rfl) ⟨1772996, by rfl⟩ : syracuseStep 2363995 = 3545993) B3545993
theorem B7978895 : Blo 1244440 7978895 := bstep (se 1 (by rfl) ⟨5984171, by rfl⟩ : syracuseStep 7978895 = 11968343) B11968343
theorem B9455615 : Blo 1244440 9455615 := bstep (se 1 (by rfl) ⟨7091711, by rfl⟩ : syracuseStep 9455615 = 14183423) B14183423
theorem B5319263 : Blo 1244440 5319263 := bstep (se 1 (by rfl) ⟨3989447, by rfl⟩ : syracuseStep 5319263 = 7978895) B7978895
theorem B5682041 : Blo 1244440 5682041 := bstep (se 2 (by rfl) ⟨2130765, by rfl⟩ : syracuseStep 5682041 = 4261531) B4261531
theorem B3151993 : Blo 1244440 3151993 := bstep (se 2 (by rfl) ⟨1181997, by rfl⟩ : syracuseStep 3151993 = 2363995) B2363995
theorem B4202657 : Blo 1244440 4202657 := bstep (se 2 (by rfl) ⟨1575996, by rfl⟩ : syracuseStep 4202657 = 3151993) B3151993
theorem B3788027 : Blo 1244440 3788027 := bstep (se 1 (by rfl) ⟨2841020, by rfl⟩ : syracuseStep 3788027 = 5682041) B5682041
theorem B6303743 : Blo 1244440 6303743 := bstep (se 1 (by rfl) ⟨4727807, by rfl⟩ : syracuseStep 6303743 = 9455615) B9455615
theorem B3546175 : Blo 1244440 3546175 := bstep (se 1 (by rfl) ⟨2659631, by rfl⟩ : syracuseStep 3546175 = 5319263) B5319263
theorem B2801771 : Blo 1244440 2801771 := bstep (se 1 (by rfl) ⟨2101328, by rfl⟩ : syracuseStep 2801771 = 4202657) B4202657
theorem B4728233 : Blo 1244440 4728233 := bstep (se 2 (by rfl) ⟨1773087, by rfl⟩ : syracuseStep 4728233 = 3546175) B3546175
theorem B2525351 : Blo 1244440 2525351 := bstep (se 1 (by rfl) ⟨1894013, by rfl⟩ : syracuseStep 2525351 = 3788027) B3788027
theorem B4202495 : Blo 1244440 4202495 := bstep (se 1 (by rfl) ⟨3151871, by rfl⟩ : syracuseStep 4202495 = 6303743) B6303743
theorem B1867847 : Blo 1244440 1867847 := bstep (se 1 (by rfl) ⟨1400885, by rfl⟩ : syracuseStep 1867847 = 2801771) B2801771
theorem B6734269 : Blo 1244440 6734269 := bstep (se 3 (by rfl) ⟨1262675, by rfl⟩ : syracuseStep 6734269 = 2525351) B2525351
theorem B2801663 : Blo 1244440 2801663 := bstep (se 1 (by rfl) ⟨2101247, by rfl⟩ : syracuseStep 2801663 = 4202495) B4202495
theorem B3152155 : Blo 1244440 3152155 := bstep (se 1 (by rfl) ⟨2364116, by rfl⟩ : syracuseStep 3152155 = 4728233) B4728233
theorem B1245231 : Blo 1244440 1245231 := bstep (se 1 (by rfl) ⟨933923, by rfl⟩ : syracuseStep 1245231 = 1867847) B1867847
theorem B4202873 : Blo 1244440 4202873 := bstep (se 2 (by rfl) ⟨1576077, by rfl⟩ : syracuseStep 4202873 = 3152155) B3152155
theorem B8979025 : Blo 1244440 8979025 := bstep (se 2 (by rfl) ⟨3367134, by rfl⟩ : syracuseStep 8979025 = 6734269) B6734269
theorem B1867775 : Blo 1244440 1867775 := bstep (se 1 (by rfl) ⟨1400831, by rfl⟩ : syracuseStep 1867775 = 2801663) B2801663
theorem B2801915 : Blo 1244440 2801915 := bstep (se 1 (by rfl) ⟨2101436, by rfl⟩ : syracuseStep 2801915 = 4202873) B4202873
theorem B11972033 : Blo 1244440 11972033 := bstep (se 2 (by rfl) ⟨4489512, by rfl⟩ : syracuseStep 11972033 = 8979025) B8979025
theorem B1245183 : Blo 1244440 1245183 := bstep (se 1 (by rfl) ⟨933887, by rfl⟩ : syracuseStep 1245183 = 1867775) B1867775
theorem B1867943 : Blo 1244440 1867943 := bstep (se 1 (by rfl) ⟨1400957, by rfl⟩ : syracuseStep 1867943 = 2801915) B2801915
theorem B7981355 : Blo 1244440 7981355 := bstep (se 1 (by rfl) ⟨5986016, by rfl⟩ : syracuseStep 7981355 = 11972033) B11972033
theorem B1245295 : Blo 1244440 1245295 := bstep (se 1 (by rfl) ⟨933971, by rfl⟩ : syracuseStep 1245295 = 1867943) B1867943
theorem B5320903 : Blo 1244440 5320903 := bstep (se 1 (by rfl) ⟨3990677, by rfl⟩ : syracuseStep 5320903 = 7981355) B7981355
theorem B7094537 : Blo 1244440 7094537 := bstep (se 2 (by rfl) ⟨2660451, by rfl⟩ : syracuseStep 7094537 = 5320903) B5320903
theorem B4729691 : Blo 1244440 4729691 := bstep (se 1 (by rfl) ⟨3547268, by rfl⟩ : syracuseStep 4729691 = 7094537) B7094537
theorem B3153127 : Blo 1244440 3153127 := bstep (se 1 (by rfl) ⟨2364845, by rfl⟩ : syracuseStep 3153127 = 4729691) B4729691
theorem B4204169 : Blo 1244440 4204169 := bstep (se 2 (by rfl) ⟨1576563, by rfl⟩ : syracuseStep 4204169 = 3153127) B3153127
theorem B2802779 : Blo 1244440 2802779 := bstep (se 1 (by rfl) ⟨2102084, by rfl⟩ : syracuseStep 2802779 = 4204169) B4204169
theorem B1868519 : Blo 1244440 1868519 := bstep (se 1 (by rfl) ⟨1401389, by rfl⟩ : syracuseStep 1868519 = 2802779) B2802779
theorem B1245679 : Blo 1244440 1245679 := bstep (se 1 (by rfl) ⟨934259, by rfl⟩ : syracuseStep 1245679 = 1868519) B1868519

theorem C0 (j : ℕ) (h1 : 311110 ≤ j) (h2 : j ≤ 311609) : Blo 1244440 (4 * j + 3) := by
  interval_cases j
  · exact B1244443
  · exact B1244447
  · exact B1244451
  · exact B1244455
  · exact B1244459
  · exact B1244463
  · exact B1244467
  · exact B1244471
  · exact B1244475
  · exact B1244479
  · exact B1244483
  · exact B1244487
  · exact B1244491
  · exact B1244495
  · exact B1244499
  · exact B1244503
  · exact B1244507
  · exact B1244511
  · exact B1244515
  · exact B1244519
  · exact B1244523
  · exact B1244527
  · exact B1244531
  · exact B1244535
  · exact B1244539
  · exact B1244543
  · exact B1244547
  · exact B1244551
  · exact B1244555
  · exact B1244559
  · exact B1244563
  · exact B1244567
  · exact B1244571
  · exact B1244575
  · exact B1244579
  · exact B1244583
  · exact B1244587
  · exact B1244591
  · exact B1244595
  · exact B1244599
  · exact B1244603
  · exact B1244607
  · exact B1244611
  · exact B1244615
  · exact B1244619
  · exact B1244623
  · exact B1244627
  · exact B1244631
  · exact B1244635
  · exact B1244639
  · exact B1244643
  · exact B1244647
  · exact B1244651
  · exact B1244655
  · exact B1244659
  · exact B1244663
  · exact B1244667
  · exact B1244671
  · exact B1244675
  · exact B1244679
  · exact B1244683
  · exact B1244687
  · exact B1244691
  · exact B1244695
  · exact B1244699
  · exact B1244703
  · exact B1244707
  · exact B1244711
  · exact B1244715
  · exact B1244719
  · exact B1244723
  · exact B1244727
  · exact B1244731
  · exact B1244735
  · exact B1244739
  · exact B1244743
  · exact B1244747
  · exact B1244751
  · exact B1244755
  · exact B1244759
  · exact B1244763
  · exact B1244767
  · exact B1244771
  · exact B1244775
  · exact B1244779
  · exact B1244783
  · exact B1244787
  · exact B1244791
  · exact B1244795
  · exact B1244799
  · exact B1244803
  · exact B1244807
  · exact B1244811
  · exact B1244815
  · exact B1244819
  · exact B1244823
  · exact B1244827
  · exact B1244831
  · exact B1244835
  · exact B1244839
  · exact B1244843
  · exact B1244847
  · exact B1244851
  · exact B1244855
  · exact B1244859
  · exact B1244863
  · exact B1244867
  · exact B1244871
  · exact B1244875
  · exact B1244879
  · exact B1244883
  · exact B1244887
  · exact B1244891
  · exact B1244895
  · exact B1244899
  · exact B1244903
  · exact B1244907
  · exact B1244911
  · exact B1244915
  · exact B1244919
  · exact B1244923
  · exact B1244927
  · exact B1244931
  · exact B1244935
  · exact B1244939
  · exact B1244943
  · exact B1244947
  · exact B1244951
  · exact B1244955
  · exact B1244959
  · exact B1244963
  · exact B1244967
  · exact B1244971
  · exact B1244975
  · exact B1244979
  · exact B1244983
  · exact B1244987
  · exact B1244991
  · exact B1244995
  · exact B1244999
  · exact B1245003
  · exact B1245007
  · exact B1245011
  · exact B1245015
  · exact B1245019
  · exact B1245023
  · exact B1245027
  · exact B1245031
  · exact B1245035
  · exact B1245039
  · exact B1245043
  · exact B1245047
  · exact B1245051
  · exact B1245055
  · exact B1245059
  · exact B1245063
  · exact B1245067
  · exact B1245071
  · exact B1245075
  · exact B1245079
  · exact B1245083
  · exact B1245087
  · exact B1245091
  · exact B1245095
  · exact B1245099
  · exact B1245103
  · exact B1245107
  · exact B1245111
  · exact B1245115
  · exact B1245119
  · exact B1245123
  · exact B1245127
  · exact B1245131
  · exact B1245135
  · exact B1245139
  · exact B1245143
  · exact B1245147
  · exact B1245151
  · exact B1245155
  · exact B1245159
  · exact B1245163
  · exact B1245167
  · exact B1245171
  · exact B1245175
  · exact B1245179
  · exact B1245183
  · exact B1245187
  · exact B1245191
  · exact B1245195
  · exact B1245199
  · exact B1245203
  · exact B1245207
  · exact B1245211
  · exact B1245215
  · exact B1245219
  · exact B1245223
  · exact B1245227
  · exact B1245231
  · exact B1245235
  · exact B1245239
  · exact B1245243
  · exact B1245247
  · exact B1245251
  · exact B1245255
  · exact B1245259
  · exact B1245263
  · exact B1245267
  · exact B1245271
  · exact B1245275
  · exact B1245279
  · exact B1245283
  · exact B1245287
  · exact B1245291
  · exact B1245295
  · exact B1245299
  · exact B1245303
  · exact B1245307
  · exact B1245311
  · exact B1245315
  · exact B1245319
  · exact B1245323
  · exact B1245327
  · exact B1245331
  · exact B1245335
  · exact B1245339
  · exact B1245343
  · exact B1245347
  · exact B1245351
  · exact B1245355
  · exact B1245359
  · exact B1245363
  · exact B1245367
  · exact B1245371
  · exact B1245375
  · exact B1245379
  · exact B1245383
  · exact B1245387
  · exact B1245391
  · exact B1245395
  · exact B1245399
  · exact B1245403
  · exact B1245407
  · exact B1245411
  · exact B1245415
  · exact B1245419
  · exact B1245423
  · exact B1245427
  · exact B1245431
  · exact B1245435
  · exact B1245439
  · exact B1245443
  · exact B1245447
  · exact B1245451
  · exact B1245455
  · exact B1245459
  · exact B1245463
  · exact B1245467
  · exact B1245471
  · exact B1245475
  · exact B1245479
  · exact B1245483
  · exact B1245487
  · exact B1245491
  · exact B1245495
  · exact B1245499
  · exact B1245503
  · exact B1245507
  · exact B1245511
  · exact B1245515
  · exact B1245519
  · exact B1245523
  · exact B1245527
  · exact B1245531
  · exact B1245535
  · exact B1245539
  · exact B1245543
  · exact B1245547
  · exact B1245551
  · exact B1245555
  · exact B1245559
  · exact B1245563
  · exact B1245567
  · exact B1245571
  · exact B1245575
  · exact B1245579
  · exact B1245583
  · exact B1245587
  · exact B1245591
  · exact B1245595
  · exact B1245599
  · exact B1245603
  · exact B1245607
  · exact B1245611
  · exact B1245615
  · exact B1245619
  · exact B1245623
  · exact B1245627
  · exact B1245631
  · exact B1245635
  · exact B1245639
  · exact B1245643
  · exact B1245647
  · exact B1245651
  · exact B1245655
  · exact B1245659
  · exact B1245663
  · exact B1245667
  · exact B1245671
  · exact B1245675
  · exact B1245679
  · exact B1245683
  · exact B1245687
  · exact B1245691
  · exact B1245695
  · exact B1245699
  · exact B1245703
  · exact B1245707
  · exact B1245711
  · exact B1245715
  · exact B1245719
  · exact B1245723
  · exact B1245727
  · exact B1245731
  · exact B1245735
  · exact B1245739
  · exact B1245743
  · exact B1245747
  · exact B1245751
  · exact B1245755
  · exact B1245759
  · exact B1245763
  · exact B1245767
  · exact B1245771
  · exact B1245775
  · exact B1245779
  · exact B1245783
  · exact B1245787
  · exact B1245791
  · exact B1245795
  · exact B1245799
  · exact B1245803
  · exact B1245807
  · exact B1245811
  · exact B1245815
  · exact B1245819
  · exact B1245823
  · exact B1245827
  · exact B1245831
  · exact B1245835
  · exact B1245839
  · exact B1245843
  · exact B1245847
  · exact B1245851
  · exact B1245855
  · exact B1245859
  · exact B1245863
  · exact B1245867
  · exact B1245871
  · exact B1245875
  · exact B1245879
  · exact B1245883
  · exact B1245887
  · exact B1245891
  · exact B1245895
  · exact B1245899
  · exact B1245903
  · exact B1245907
  · exact B1245911
  · exact B1245915
  · exact B1245919
  · exact B1245923
  · exact B1245927
  · exact B1245931
  · exact B1245935
  · exact B1245939
  · exact B1245943
  · exact B1245947
  · exact B1245951
  · exact B1245955
  · exact B1245959
  · exact B1245963
  · exact B1245967
  · exact B1245971
  · exact B1245975
  · exact B1245979
  · exact B1245983
  · exact B1245987
  · exact B1245991
  · exact B1245995
  · exact B1245999
  · exact B1246003
  · exact B1246007
  · exact B1246011
  · exact B1246015
  · exact B1246019
  · exact B1246023
  · exact B1246027
  · exact B1246031
  · exact B1246035
  · exact B1246039
  · exact B1246043
  · exact B1246047
  · exact B1246051
  · exact B1246055
  · exact B1246059
  · exact B1246063
  · exact B1246067
  · exact B1246071
  · exact B1246075
  · exact B1246079
  · exact B1246083
  · exact B1246087
  · exact B1246091
  · exact B1246095
  · exact B1246099
  · exact B1246103
  · exact B1246107
  · exact B1246111
  · exact B1246115
  · exact B1246119
  · exact B1246123
  · exact B1246127
  · exact B1246131
  · exact B1246135
  · exact B1246139
  · exact B1246143
  · exact B1246147
  · exact B1246151
  · exact B1246155
  · exact B1246159
  · exact B1246163
  · exact B1246167
  · exact B1246171
  · exact B1246175
  · exact B1246179
  · exact B1246183
  · exact B1246187
  · exact B1246191
  · exact B1246195
  · exact B1246199
  · exact B1246203
  · exact B1246207
  · exact B1246211
  · exact B1246215
  · exact B1246219
  · exact B1246223
  · exact B1246227
  · exact B1246231
  · exact B1246235
  · exact B1246239
  · exact B1246243
  · exact B1246247
  · exact B1246251
  · exact B1246255
  · exact B1246259
  · exact B1246263
  · exact B1246267
  · exact B1246271
  · exact B1246275
  · exact B1246279
  · exact B1246283
  · exact B1246287
  · exact B1246291
  · exact B1246295
  · exact B1246299
  · exact B1246303
  · exact B1246307
  · exact B1246311
  · exact B1246315
  · exact B1246319
  · exact B1246323
  · exact B1246327
  · exact B1246331
  · exact B1246335
  · exact B1246339
  · exact B1246343
  · exact B1246347
  · exact B1246351
  · exact B1246355
  · exact B1246359
  · exact B1246363
  · exact B1246367
  · exact B1246371
  · exact B1246375
  · exact B1246379
  · exact B1246383
  · exact B1246387
  · exact B1246391
  · exact B1246395
  · exact B1246399
  · exact B1246403
  · exact B1246407
  · exact B1246411
  · exact B1246415
  · exact B1246419
  · exact B1246423
  · exact B1246427
  · exact B1246431
  · exact B1246435
  · exact B1246439

theorem solution (m : ℕ) (hlo : 1244440 ≤ m) (hhi : m ≤ 1246440) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 311110 ≤ j := by omega
    have hj2 : j ≤ 311609 := by omega
    have hb : Blo 1244440 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
