-- Prove2me | solution 1 for syracuse_descends_range_1277957_1279957
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:31.823178+00:00
-- url     : https://prove2.me/submissions/294161eb-d4e8-4c85-936d-eb975906169e

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


theorem B1916957 : Blo 1277957 1916957 := bbase (se 3 (by rfl) ⟨359429, by rfl⟩ : syracuseStep 1916957 = 718859) (by norm_num)
theorem B2875445 : Blo 1277957 2875445 := bbase (se 5 (by rfl) ⟨134786, by rfl⟩ : syracuseStep 2875445 = 269573) (by norm_num)
theorem B1916981 : Blo 1277957 1916981 := bbase (se 5 (by rfl) ⟨89858, by rfl⟩ : syracuseStep 1916981 = 179717) (by norm_num)
theorem B3235909 : Blo 1277957 3235909 := bbase (se 4 (by rfl) ⟨303366, by rfl⟩ : syracuseStep 3235909 = 606733) (by norm_num)
theorem B3457093 : Blo 1277957 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B1917005 : Blo 1277957 1917005 := bbase (se 3 (by rfl) ⟨359438, by rfl⟩ : syracuseStep 1917005 = 718877) (by norm_num)
theorem B1917029 : Blo 1277957 1917029 := bbase (se 4 (by rfl) ⟨179721, by rfl⟩ : syracuseStep 1917029 = 359443) (by norm_num)
theorem B7774325 : Blo 1277957 7774325 := bbase (se 5 (by rfl) ⟨364421, by rfl⟩ : syracuseStep 7774325 = 728843) (by norm_num)
theorem B2875517 : Blo 1277957 2875517 := bbase (se 3 (by rfl) ⟨539159, by rfl⟩ : syracuseStep 2875517 = 1078319) (by norm_num)
theorem B1917053 : Blo 1277957 1917053 := bbase (se 3 (by rfl) ⟨359447, by rfl⟩ : syracuseStep 1917053 = 718895) (by norm_num)
theorem B1917077 : Blo 1277957 1917077 := bbase (se 6 (by rfl) ⟨44931, by rfl⟩ : syracuseStep 1917077 = 89863) (by norm_num)
theorem B1917101 : Blo 1277957 1917101 := bbase (se 3 (by rfl) ⟨359456, by rfl⟩ : syracuseStep 1917101 = 718913) (by norm_num)
theorem B3236021 : Blo 1277957 3236021 := bbase (se 5 (by rfl) ⟨151688, by rfl⟩ : syracuseStep 3236021 = 303377) (by norm_num)
theorem B2875589 : Blo 1277957 2875589 := bbase (se 4 (by rfl) ⟨269586, by rfl⟩ : syracuseStep 2875589 = 539173) (by norm_num)
theorem B1917125 : Blo 1277957 1917125 := bbase (se 4 (by rfl) ⟨179730, by rfl⟩ : syracuseStep 1917125 = 359461) (by norm_num)
theorem B1917149 : Blo 1277957 1917149 := bbase (se 3 (by rfl) ⟨359465, by rfl⟩ : syracuseStep 1917149 = 718931) (by norm_num)
theorem B1917173 : Blo 1277957 1917173 := bbase (se 5 (by rfl) ⟨89867, by rfl⟩ : syracuseStep 1917173 = 179735) (by norm_num)
theorem B4153589 : Blo 1277957 4153589 := bbase (se 5 (by rfl) ⟨194699, by rfl⟩ : syracuseStep 4153589 = 389399) (by norm_num)
theorem B2875661 : Blo 1277957 2875661 := bbase (se 3 (by rfl) ⟨539186, by rfl⟩ : syracuseStep 2875661 = 1078373) (by norm_num)
theorem B1917197 : Blo 1277957 1917197 := bbase (se 3 (by rfl) ⟨359474, by rfl⟩ : syracuseStep 1917197 = 718949) (by norm_num)
theorem B4317461 : Blo 1277957 4317461 := bbase (se 6 (by rfl) ⟨101190, by rfl⟩ : syracuseStep 4317461 = 202381) (by norm_num)
theorem B1917221 : Blo 1277957 1917221 := bbase (se 4 (by rfl) ⟨179739, by rfl⟩ : syracuseStep 1917221 = 359479) (by norm_num)
theorem B3506485 : Blo 1277957 3506485 := bbase (se 5 (by rfl) ⟨164366, by rfl⟩ : syracuseStep 3506485 = 328733) (by norm_num)
theorem B1917245 : Blo 1277957 1917245 := bbase (se 3 (by rfl) ⟨359483, by rfl⟩ : syracuseStep 1917245 = 718967) (by norm_num)
theorem B2875733 : Blo 1277957 2875733 := bbase (se 10 (by rfl) ⟨4212, by rfl⟩ : syracuseStep 2875733 = 8425) (by norm_num)
theorem B1917269 : Blo 1277957 1917269 := bbase (se 10 (by rfl) ⟨2808, by rfl⟩ : syracuseStep 1917269 = 5617) (by norm_num)
theorem B1917293 : Blo 1277957 1917293 := bbase (se 3 (by rfl) ⟨359492, by rfl⟩ : syracuseStep 1917293 = 718985) (by norm_num)
theorem B2048365 : Blo 1277957 2048365 := bbase (se 3 (by rfl) ⟨384068, by rfl⟩ : syracuseStep 2048365 = 768137) (by norm_num)
theorem B3236213 : Blo 1277957 3236213 := bbase (se 5 (by rfl) ⟨151697, by rfl⟩ : syracuseStep 3236213 = 303395) (by norm_num)
theorem B1917317 : Blo 1277957 1917317 := bbase (se 4 (by rfl) ⟨179748, by rfl⟩ : syracuseStep 1917317 = 359497) (by norm_num)
theorem B2875805 : Blo 1277957 2875805 := bbase (se 3 (by rfl) ⟨539213, by rfl⟩ : syracuseStep 2875805 = 1078427) (by norm_num)
theorem B1917341 : Blo 1277957 1917341 := bbase (se 3 (by rfl) ⟨359501, by rfl⟩ : syracuseStep 1917341 = 719003) (by norm_num)
theorem B1917365 : Blo 1277957 1917365 := bbase (se 5 (by rfl) ⟨89876, by rfl⟩ : syracuseStep 1917365 = 179753) (by norm_num)
theorem B1917389 : Blo 1277957 1917389 := bbase (se 3 (by rfl) ⟨359510, by rfl⟩ : syracuseStep 1917389 = 719021) (by norm_num)
theorem B2875877 : Blo 1277957 2875877 := bbase (se 4 (by rfl) ⟨269613, by rfl⟩ : syracuseStep 2875877 = 539227) (by norm_num)
theorem B1917413 : Blo 1277957 1917413 := bbase (se 4 (by rfl) ⟨179757, by rfl⟩ : syracuseStep 1917413 = 359515) (by norm_num)
theorem B1917437 : Blo 1277957 1917437 := bbase (se 3 (by rfl) ⟨359519, by rfl⟩ : syracuseStep 1917437 = 719039) (by norm_num)
theorem B1917461 : Blo 1277957 1917461 := bbase (se 6 (by rfl) ⟨44940, by rfl⟩ : syracuseStep 1917461 = 89881) (by norm_num)
theorem B2875949 : Blo 1277957 2875949 := bbase (se 3 (by rfl) ⟨539240, by rfl⟩ : syracuseStep 2875949 = 1078481) (by norm_num)
theorem B1917485 : Blo 1277957 1917485 := bbase (se 3 (by rfl) ⟨359528, by rfl⟩ : syracuseStep 1917485 = 719057) (by norm_num)
theorem B1917509 : Blo 1277957 1917509 := bbase (se 4 (by rfl) ⟨179766, by rfl⟩ : syracuseStep 1917509 = 359533) (by norm_num)
theorem B1917533 : Blo 1277957 1917533 := bbase (se 3 (by rfl) ⟨359537, by rfl⟩ : syracuseStep 1917533 = 719075) (by norm_num)
theorem B2876021 : Blo 1277957 2876021 := bbase (se 5 (by rfl) ⟨134813, by rfl⟩ : syracuseStep 2876021 = 269627) (by norm_num)
theorem B1917557 : Blo 1277957 1917557 := bbase (se 5 (by rfl) ⟨89885, by rfl⟩ : syracuseStep 1917557 = 179771) (by norm_num)
theorem B1917581 : Blo 1277957 1917581 := bbase (se 3 (by rfl) ⟨359546, by rfl⟩ : syracuseStep 1917581 = 719093) (by norm_num)
theorem B1917605 : Blo 1277957 1917605 := bbase (se 4 (by rfl) ⟨179775, by rfl⟩ : syracuseStep 1917605 = 359551) (by norm_num)
theorem B2876093 : Blo 1277957 2876093 := bbase (se 3 (by rfl) ⟨539267, by rfl⟩ : syracuseStep 2876093 = 1078535) (by norm_num)
theorem B1917629 : Blo 1277957 1917629 := bbase (se 3 (by rfl) ⟨359555, by rfl⟩ : syracuseStep 1917629 = 719111) (by norm_num)
theorem B3072701 : Blo 1277957 3072701 := bbase (se 3 (by rfl) ⟨576131, by rfl⟩ : syracuseStep 3072701 = 1152263) (by norm_num)
theorem B4317893 : Blo 1277957 4317893 := bbase (se 4 (by rfl) ⟨404802, by rfl⟩ : syracuseStep 4317893 = 809605) (by norm_num)
theorem B3236557 : Blo 1277957 3236557 := bbase (se 3 (by rfl) ⟨606854, by rfl⟩ : syracuseStep 3236557 = 1213709) (by norm_num)
theorem B1917653 : Blo 1277957 1917653 := bbase (se 7 (by rfl) ⟨22472, by rfl⟩ : syracuseStep 1917653 = 44945) (by norm_num)
theorem B23347925 : Blo 1277957 23347925 := bbase (se 7 (by rfl) ⟨273608, by rfl⟩ : syracuseStep 23347925 = 547217) (by norm_num)
theorem B1917677 : Blo 1277957 1917677 := bbase (se 3 (by rfl) ⟨359564, by rfl⟩ : syracuseStep 1917677 = 719129) (by norm_num)
theorem B4096757 : Blo 1277957 4096757 := bbase (se 5 (by rfl) ⟨192035, by rfl⟩ : syracuseStep 4096757 = 384071) (by norm_num)
theorem B2876165 : Blo 1277957 2876165 := bbase (se 4 (by rfl) ⟨269640, by rfl⟩ : syracuseStep 2876165 = 539281) (by norm_num)
theorem B1917701 : Blo 1277957 1917701 := bbase (se 4 (by rfl) ⟨179784, by rfl⟩ : syracuseStep 1917701 = 359569) (by norm_num)
theorem B2048789 : Blo 1277957 2048789 := bbase (se 6 (by rfl) ⟨48018, by rfl⟩ : syracuseStep 2048789 = 96037) (by norm_num)
theorem B1917725 : Blo 1277957 1917725 := bbase (se 3 (by rfl) ⟨359573, by rfl⟩ : syracuseStep 1917725 = 719147) (by norm_num)
theorem B1917749 : Blo 1277957 1917749 := bbase (se 5 (by rfl) ⟨89894, by rfl⟩ : syracuseStep 1917749 = 179789) (by norm_num)
theorem B3236669 : Blo 1277957 3236669 := bbase (se 3 (by rfl) ⟨606875, by rfl⟩ : syracuseStep 3236669 = 1213751) (by norm_num)
theorem B2876237 : Blo 1277957 2876237 := bbase (se 3 (by rfl) ⟨539294, by rfl⟩ : syracuseStep 2876237 = 1078589) (by norm_num)
theorem B1917773 : Blo 1277957 1917773 := bbase (se 3 (by rfl) ⟨359582, by rfl⟩ : syracuseStep 1917773 = 719165) (by norm_num)
theorem B1917797 : Blo 1277957 1917797 := bbase (se 4 (by rfl) ⟨179793, by rfl⟩ : syracuseStep 1917797 = 359587) (by norm_num)
theorem B9716597 : Blo 1277957 9716597 := bbase (se 5 (by rfl) ⟨455465, by rfl⟩ : syracuseStep 9716597 = 910931) (by norm_num)
theorem B1917821 : Blo 1277957 1917821 := bbase (se 3 (by rfl) ⟨359591, by rfl⟩ : syracuseStep 1917821 = 719183) (by norm_num)
theorem B2876309 : Blo 1277957 2876309 := bbase (se 6 (by rfl) ⟨67413, by rfl⟩ : syracuseStep 2876309 = 134827) (by norm_num)
theorem B1917845 : Blo 1277957 1917845 := bbase (se 6 (by rfl) ⟨44949, by rfl⟩ : syracuseStep 1917845 = 89899) (by norm_num)
theorem B1917869 : Blo 1277957 1917869 := bbase (se 3 (by rfl) ⟨359600, by rfl⟩ : syracuseStep 1917869 = 719201) (by norm_num)
theorem B1917893 : Blo 1277957 1917893 := bbase (se 4 (by rfl) ⟨179802, by rfl⟩ : syracuseStep 1917893 = 359605) (by norm_num)
theorem B2876381 : Blo 1277957 2876381 := bbase (se 3 (by rfl) ⟨539321, by rfl⟩ : syracuseStep 2876381 = 1078643) (by norm_num)
theorem B1917917 : Blo 1277957 1917917 := bbase (se 3 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 1917917 = 719219) (by norm_num)
theorem B1557469 : Blo 1277957 1557469 := bbase (se 3 (by rfl) ⟨292025, by rfl⟩ : syracuseStep 1557469 = 584051) (by norm_num)
theorem B3326957 : Blo 1277957 3326957 := bbase (se 3 (by rfl) ⟨623804, by rfl⟩ : syracuseStep 3326957 = 1247609) (by norm_num)
theorem B1917941 : Blo 1277957 1917941 := bbase (se 5 (by rfl) ⟨89903, by rfl⟩ : syracuseStep 1917941 = 179807) (by norm_num)
theorem B3236861 : Blo 1277957 3236861 := bbase (se 3 (by rfl) ⟨606911, by rfl⟩ : syracuseStep 3236861 = 1213823) (by norm_num)
theorem B6472709 : Blo 1277957 6472709 := bbase (se 4 (by rfl) ⟨606816, by rfl⟩ : syracuseStep 6472709 = 1213633) (by norm_num)
theorem B1917965 : Blo 1277957 1917965 := bbase (se 3 (by rfl) ⟨359618, by rfl⟩ : syracuseStep 1917965 = 719237) (by norm_num)
theorem B2876453 : Blo 1277957 2876453 := bbase (se 4 (by rfl) ⟨269667, by rfl⟩ : syracuseStep 2876453 = 539335) (by norm_num)
theorem B1917989 : Blo 1277957 1917989 := bbase (se 4 (by rfl) ⟨179811, by rfl⟩ : syracuseStep 1917989 = 359623) (by norm_num)
theorem B2049077 : Blo 1277957 2049077 := bbase (se 5 (by rfl) ⟨96050, by rfl⟩ : syracuseStep 2049077 = 192101) (by norm_num)
theorem B1918013 : Blo 1277957 1918013 := bbase (se 3 (by rfl) ⟨359627, by rfl⟩ : syracuseStep 1918013 = 719255) (by norm_num)
theorem B1295437 : Blo 1277957 1295437 := bbase (se 3 (by rfl) ⟨242894, by rfl⟩ : syracuseStep 1295437 = 485789) (by norm_num)
theorem B1918037 : Blo 1277957 1918037 := bbase (se 8 (by rfl) ⟨11238, by rfl⟩ : syracuseStep 1918037 = 22477) (by norm_num)
theorem B2876525 : Blo 1277957 2876525 := bbase (se 3 (by rfl) ⟨539348, by rfl⟩ : syracuseStep 2876525 = 1078697) (by norm_num)
theorem B1918061 : Blo 1277957 1918061 := bbase (se 3 (by rfl) ⟨359636, by rfl⟩ : syracuseStep 1918061 = 719273) (by norm_num)
theorem B4318325 : Blo 1277957 4318325 := bbase (se 5 (by rfl) ⟨202421, by rfl⟩ : syracuseStep 4318325 = 404843) (by norm_num)
theorem B1918085 : Blo 1277957 1918085 := bbase (se 4 (by rfl) ⟨179820, by rfl⟩ : syracuseStep 1918085 = 359641) (by norm_num)
theorem B1918109 : Blo 1277957 1918109 := bbase (se 3 (by rfl) ⟨359645, by rfl⟩ : syracuseStep 1918109 = 719291) (by norm_num)
theorem B2876597 : Blo 1277957 2876597 := bbase (se 5 (by rfl) ⟨134840, by rfl⟩ : syracuseStep 2876597 = 269681) (by norm_num)
theorem B1918133 : Blo 1277957 1918133 := bbase (se 5 (by rfl) ⟨89912, by rfl⟩ : syracuseStep 1918133 = 179825) (by norm_num)
theorem B2335925 : Blo 1277957 2335925 := bbase (se 5 (by rfl) ⟨109496, by rfl⟩ : syracuseStep 2335925 = 218993) (by norm_num)
theorem B1918157 : Blo 1277957 1918157 := bbase (se 3 (by rfl) ⟨359654, by rfl⟩ : syracuseStep 1918157 = 719309) (by norm_num)
theorem B1918181 : Blo 1277957 1918181 := bbase (se 4 (by rfl) ⟨179829, by rfl⟩ : syracuseStep 1918181 = 359659) (by norm_num)
theorem B2876669 : Blo 1277957 2876669 := bbase (se 3 (by rfl) ⟨539375, by rfl⟩ : syracuseStep 2876669 = 1078751) (by norm_num)
theorem B1918205 : Blo 1277957 1918205 := bbase (se 3 (by rfl) ⟨359663, by rfl⟩ : syracuseStep 1918205 = 719327) (by norm_num)
theorem B9708821 : Blo 1277957 9708821 := bbase (se 6 (by rfl) ⟨227550, by rfl⟩ : syracuseStep 9708821 = 455101) (by norm_num)
theorem B1918229 : Blo 1277957 1918229 := bbase (se 6 (by rfl) ⟨44958, by rfl⟩ : syracuseStep 1918229 = 89917) (by norm_num)
theorem B1918253 : Blo 1277957 1918253 := bbase (se 3 (by rfl) ⟨359672, by rfl⟩ : syracuseStep 1918253 = 719345) (by norm_num)
theorem B2876741 : Blo 1277957 2876741 := bbase (se 4 (by rfl) ⟨269694, by rfl⟩ : syracuseStep 2876741 = 539389) (by norm_num)
theorem B1918277 : Blo 1277957 1918277 := bbase (se 4 (by rfl) ⟨179838, by rfl⟩ : syracuseStep 1918277 = 359677) (by norm_num)
theorem B3237205 : Blo 1277957 3237205 := bbase (se 12 (by rfl) ⟨1185, by rfl⟩ : syracuseStep 3237205 = 2371) (by norm_num)
theorem B7996757 : Blo 1277957 7996757 := bbase (se 12 (by rfl) ⟨2928, by rfl⟩ : syracuseStep 7996757 = 5857) (by norm_num)
theorem B1918301 : Blo 1277957 1918301 := bbase (se 3 (by rfl) ⟨359681, by rfl⟩ : syracuseStep 1918301 = 719363) (by norm_num)
theorem B1918325 : Blo 1277957 1918325 := bbase (se 5 (by rfl) ⟨89921, by rfl⟩ : syracuseStep 1918325 = 179843) (by norm_num)
theorem B2876813 : Blo 1277957 2876813 := bbase (se 3 (by rfl) ⟨539402, by rfl⟩ : syracuseStep 2876813 = 1078805) (by norm_num)
theorem B1918349 : Blo 1277957 1918349 := bbase (se 3 (by rfl) ⟨359690, by rfl⟩ : syracuseStep 1918349 = 719381) (by norm_num)
theorem B1918373 : Blo 1277957 1918373 := bbase (se 4 (by rfl) ⟨179847, by rfl⟩ : syracuseStep 1918373 = 359695) (by norm_num)
theorem B1918397 : Blo 1277957 1918397 := bbase (se 3 (by rfl) ⟨359699, by rfl⟩ : syracuseStep 1918397 = 719399) (by norm_num)
theorem B3237317 : Blo 1277957 3237317 := bbase (se 4 (by rfl) ⟨303498, by rfl⟩ : syracuseStep 3237317 = 606997) (by norm_num)
theorem B2876885 : Blo 1277957 2876885 := bbase (se 7 (by rfl) ⟨33713, by rfl⟩ : syracuseStep 2876885 = 67427) (by norm_num)
theorem B1918421 : Blo 1277957 1918421 := bbase (se 7 (by rfl) ⟨22481, by rfl⟩ : syracuseStep 1918421 = 44963) (by norm_num)
theorem B1918445 : Blo 1277957 1918445 := bbase (se 3 (by rfl) ⟨359708, by rfl⟩ : syracuseStep 1918445 = 719417) (by norm_num)
theorem B1918469 : Blo 1277957 1918469 := bbase (se 4 (by rfl) ⟨179856, by rfl⟩ : syracuseStep 1918469 = 359713) (by norm_num)
theorem B2336261 : Blo 1277957 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B2876957 : Blo 1277957 2876957 := bbase (se 3 (by rfl) ⟨539429, by rfl⟩ : syracuseStep 2876957 = 1078859) (by norm_num)
theorem B1918493 : Blo 1277957 1918493 := bbase (se 3 (by rfl) ⟨359717, by rfl⟩ : syracuseStep 1918493 = 719435) (by norm_num)
theorem B4318757 : Blo 1277957 4318757 := bbase (se 4 (by rfl) ⟨404883, by rfl⟩ : syracuseStep 4318757 = 809767) (by norm_num)
theorem B3114541 : Blo 1277957 3114541 := bbase (se 3 (by rfl) ⟨583976, by rfl⟩ : syracuseStep 3114541 = 1167953) (by norm_num)
theorem B1918517 : Blo 1277957 1918517 := bbase (se 5 (by rfl) ⟨89930, by rfl⟩ : syracuseStep 1918517 = 179861) (by norm_num)
theorem B1918541 : Blo 1277957 1918541 := bbase (se 3 (by rfl) ⟨359726, by rfl⟩ : syracuseStep 1918541 = 719453) (by norm_num)
theorem B1820245 : Blo 1277957 1820245 := bbase (se 8 (by rfl) ⟨10665, by rfl⟩ : syracuseStep 1820245 = 21331) (by norm_num)
theorem B2877029 : Blo 1277957 2877029 := bbase (se 4 (by rfl) ⟨269721, by rfl⟩ : syracuseStep 2877029 = 539443) (by norm_num)
theorem B1918565 : Blo 1277957 1918565 := bbase (se 4 (by rfl) ⟨179865, by rfl⟩ : syracuseStep 1918565 = 359731) (by norm_num)
theorem B1918589 : Blo 1277957 1918589 := bbase (se 3 (by rfl) ⟨359735, by rfl⟩ : syracuseStep 1918589 = 719471) (by norm_num)
theorem B1296001 : Blo 1277957 1296001 := bbase (se 2 (by rfl) ⟨486000, by rfl⟩ : syracuseStep 1296001 = 972001) (by norm_num)
theorem B3237509 : Blo 1277957 3237509 := bbase (se 4 (by rfl) ⟨303516, by rfl⟩ : syracuseStep 3237509 = 607033) (by norm_num)
theorem B1918613 : Blo 1277957 1918613 := bbase (se 6 (by rfl) ⟨44967, by rfl⟩ : syracuseStep 1918613 = 89935) (by norm_num)
theorem B2877101 : Blo 1277957 2877101 := bbase (se 3 (by rfl) ⟨539456, by rfl⟩ : syracuseStep 2877101 = 1078913) (by norm_num)
theorem B1918637 : Blo 1277957 1918637 := bbase (se 3 (by rfl) ⟨359744, by rfl⟩ : syracuseStep 1918637 = 719489) (by norm_num)
theorem B1918661 : Blo 1277957 1918661 := bbase (se 4 (by rfl) ⟨179874, by rfl⟩ : syracuseStep 1918661 = 359749) (by norm_num)
theorem B1918685 : Blo 1277957 1918685 := bbase (se 3 (by rfl) ⟨359753, by rfl⟩ : syracuseStep 1918685 = 719507) (by norm_num)
theorem B4859621 : Blo 1277957 4859621 := bbase (se 4 (by rfl) ⟨455589, by rfl⟩ : syracuseStep 4859621 = 911179) (by norm_num)
theorem B2877173 : Blo 1277957 2877173 := bbase (se 5 (by rfl) ⟨134867, by rfl⟩ : syracuseStep 2877173 = 269735) (by norm_num)
theorem B1918709 : Blo 1277957 1918709 := bbase (se 5 (by rfl) ⟨89939, by rfl⟩ : syracuseStep 1918709 = 179879) (by norm_num)
theorem B1918733 : Blo 1277957 1918733 := bbase (se 3 (by rfl) ⟨359762, by rfl⟩ : syracuseStep 1918733 = 719525) (by norm_num)
theorem B1918757 : Blo 1277957 1918757 := bbase (se 4 (by rfl) ⟨179883, by rfl⟩ : syracuseStep 1918757 = 359767) (by norm_num)
theorem B2877245 : Blo 1277957 2877245 := bbase (se 3 (by rfl) ⟨539483, by rfl⟩ : syracuseStep 2877245 = 1078967) (by norm_num)
theorem B1918781 : Blo 1277957 1918781 := bbase (se 3 (by rfl) ⟨359771, by rfl⟩ : syracuseStep 1918781 = 719543) (by norm_num)
theorem B1918805 : Blo 1277957 1918805 := bbase (se 9 (by rfl) ⟨5621, by rfl⟩ : syracuseStep 1918805 = 11243) (by norm_num)
theorem B2049877 : Blo 1277957 2049877 := bbase (se 9 (by rfl) ⟨6005, by rfl⟩ : syracuseStep 2049877 = 12011) (by norm_num)
theorem B2729821 : Blo 1277957 2729821 := bbase (se 3 (by rfl) ⟨511841, by rfl⟩ : syracuseStep 2729821 = 1023683) (by norm_num)
theorem B1918829 : Blo 1277957 1918829 := bbase (se 3 (by rfl) ⟨359780, by rfl⟩ : syracuseStep 1918829 = 719561) (by norm_num)
theorem B2877317 : Blo 1277957 2877317 := bbase (se 4 (by rfl) ⟨269748, by rfl⟩ : syracuseStep 2877317 = 539497) (by norm_num)
theorem B1918853 : Blo 1277957 1918853 := bbase (se 4 (by rfl) ⟨179892, by rfl⟩ : syracuseStep 1918853 = 359785) (by norm_num)
theorem B2426773 : Blo 1277957 2426773 := bbase (se 6 (by rfl) ⟨56877, by rfl⟩ : syracuseStep 2426773 = 113755) (by norm_num)
theorem B1918877 : Blo 1277957 1918877 := bbase (se 3 (by rfl) ⟨359789, by rfl⟩ : syracuseStep 1918877 = 719579) (by norm_num)
theorem B2770861 : Blo 1277957 2770861 := bbase (se 3 (by rfl) ⟨519536, by rfl⟩ : syracuseStep 2770861 = 1039073) (by norm_num)
theorem B1918901 : Blo 1277957 1918901 := bbase (se 5 (by rfl) ⟨89948, by rfl⟩ : syracuseStep 1918901 = 179897) (by norm_num)
theorem B1296329 : Blo 1277957 1296329 := bbase (se 2 (by rfl) ⟨486123, by rfl⟩ : syracuseStep 1296329 = 972247) (by norm_num)
theorem B2877389 : Blo 1277957 2877389 := bbase (se 3 (by rfl) ⟨539510, by rfl⟩ : syracuseStep 2877389 = 1079021) (by norm_num)
theorem B1918925 : Blo 1277957 1918925 := bbase (se 3 (by rfl) ⟨359798, by rfl⟩ : syracuseStep 1918925 = 719597) (by norm_num)
theorem B4319189 : Blo 1277957 4319189 := bbase (se 7 (by rfl) ⟨50615, by rfl⟩ : syracuseStep 4319189 = 101231) (by norm_num)
theorem B3237853 : Blo 1277957 3237853 := bbase (se 3 (by rfl) ⟨607097, by rfl⟩ : syracuseStep 3237853 = 1214195) (by norm_num)
theorem B4605925 : Blo 1277957 4605925 := bbase (se 4 (by rfl) ⟨431805, by rfl⟩ : syracuseStep 4605925 = 863611) (by norm_num)
theorem B1918949 : Blo 1277957 1918949 := bbase (se 4 (by rfl) ⟨179901, by rfl⟩ : syracuseStep 1918949 = 359803) (by norm_num)
theorem B1918973 : Blo 1277957 1918973 := bbase (se 3 (by rfl) ⟨359807, by rfl⟩ : syracuseStep 1918973 = 719615) (by norm_num)
theorem B2156557 : Blo 1277957 2156557 := bbase (se 3 (by rfl) ⟨404354, by rfl⟩ : syracuseStep 2156557 = 808709) (by norm_num)
theorem B1640461 : Blo 1277957 1640461 := bbase (se 3 (by rfl) ⟨307586, by rfl⟩ : syracuseStep 1640461 = 615173) (by norm_num)
theorem B2877461 : Blo 1277957 2877461 := bbase (se 6 (by rfl) ⟨67440, by rfl⟩ : syracuseStep 2877461 = 134881) (by norm_num)
theorem B13125653 : Blo 1277957 13125653 := bbase (se 6 (by rfl) ⟨307632, by rfl⟩ : syracuseStep 13125653 = 615265) (by norm_num)
theorem B1918997 : Blo 1277957 1918997 := bbase (se 6 (by rfl) ⟨44976, by rfl⟩ : syracuseStep 1918997 = 89953) (by norm_num)
theorem B5466133 : Blo 1277957 5466133 := bbase (se 6 (by rfl) ⟨128112, by rfl⟩ : syracuseStep 5466133 = 256225) (by norm_num)
theorem B2426917 : Blo 1277957 2426917 := bbase (se 4 (by rfl) ⟨227523, by rfl⟩ : syracuseStep 2426917 = 455047) (by norm_num)
theorem B1919021 : Blo 1277957 1919021 := bbase (se 3 (by rfl) ⟨359816, by rfl⟩ : syracuseStep 1919021 = 719633) (by norm_num)
theorem B1640497 : Blo 1277957 1640497 := bbase (se 2 (by rfl) ⟨615186, by rfl⟩ : syracuseStep 1640497 = 1230373) (by norm_num)
theorem B1919045 : Blo 1277957 1919045 := bbase (se 4 (by rfl) ⟨179910, by rfl⟩ : syracuseStep 1919045 = 359821) (by norm_num)
theorem B3237965 : Blo 1277957 3237965 := bbase (se 3 (by rfl) ⟨607118, by rfl⟩ : syracuseStep 3237965 = 1214237) (by norm_num)
theorem B3074125 : Blo 1277957 3074125 := bbase (se 3 (by rfl) ⟨576398, by rfl⟩ : syracuseStep 3074125 = 1152797) (by norm_num)
theorem B2877533 : Blo 1277957 2877533 := bbase (se 3 (by rfl) ⟨539537, by rfl⟩ : syracuseStep 2877533 = 1079075) (by norm_num)
theorem B1919069 : Blo 1277957 1919069 := bbase (se 3 (by rfl) ⟨359825, by rfl⟩ : syracuseStep 1919069 = 719651) (by norm_num)
theorem B2156645 : Blo 1277957 2156645 := bbase (se 4 (by rfl) ⟨202185, by rfl⟩ : syracuseStep 2156645 = 404371) (by norm_num)
theorem B5187685 : Blo 1277957 5187685 := bbase (se 4 (by rfl) ⟨486345, by rfl⟩ : syracuseStep 5187685 = 972691) (by norm_num)
theorem B1919093 : Blo 1277957 1919093 := bbase (se 5 (by rfl) ⟨89957, by rfl⟩ : syracuseStep 1919093 = 179915) (by norm_num)
theorem B4606085 : Blo 1277957 4606085 := bbase (se 4 (by rfl) ⟨431820, by rfl⟩ : syracuseStep 4606085 = 863641) (by norm_num)
theorem B1919117 : Blo 1277957 1919117 := bbase (se 3 (by rfl) ⟨359834, by rfl⟩ : syracuseStep 1919117 = 719669) (by norm_num)
theorem B1820837 : Blo 1277957 1820837 := bbase (se 4 (by rfl) ⟨170703, by rfl⟩ : syracuseStep 1820837 = 341407) (by norm_num)
theorem B2877605 : Blo 1277957 2877605 := bbase (se 4 (by rfl) ⟨269775, by rfl⟩ : syracuseStep 2877605 = 539551) (by norm_num)
theorem B1919141 : Blo 1277957 1919141 := bbase (se 4 (by rfl) ⟨179919, by rfl⟩ : syracuseStep 1919141 = 359839) (by norm_num)
theorem B1919165 : Blo 1277957 1919165 := bbase (se 3 (by rfl) ⟨359843, by rfl⟩ : syracuseStep 1919165 = 719687) (by norm_num)
theorem B2427077 : Blo 1277957 2427077 := bbase (se 4 (by rfl) ⟨227538, by rfl⟩ : syracuseStep 2427077 = 455077) (by norm_num)
theorem B20728021 : Blo 1277957 20728021 := bbase (se 7 (by rfl) ⟨242906, by rfl⟩ : syracuseStep 20728021 = 485813) (by norm_num)
theorem B1919189 : Blo 1277957 1919189 := bbase (se 7 (by rfl) ⟨22490, by rfl⟩ : syracuseStep 1919189 = 44981) (by norm_num)
theorem B2156773 : Blo 1277957 2156773 := bbase (se 4 (by rfl) ⟨202197, by rfl⟩ : syracuseStep 2156773 = 404395) (by norm_num)
theorem B2877677 : Blo 1277957 2877677 := bbase (se 3 (by rfl) ⟨539564, by rfl⟩ : syracuseStep 2877677 = 1079129) (by norm_num)
theorem B1919213 : Blo 1277957 1919213 := bbase (se 3 (by rfl) ⟨359852, by rfl⟩ : syracuseStep 1919213 = 719705) (by norm_num)
theorem B6310133 : Blo 1277957 6310133 := bbase (se 5 (by rfl) ⟨295787, by rfl⟩ : syracuseStep 6310133 = 591575) (by norm_num)
theorem B1820917 : Blo 1277957 1820917 := bbase (se 5 (by rfl) ⟨85355, by rfl⟩ : syracuseStep 1820917 = 170711) (by norm_num)
theorem B2459909 : Blo 1277957 2459909 := bbase (se 4 (by rfl) ⟨230616, by rfl⟩ : syracuseStep 2459909 = 461233) (by norm_num)
theorem B1943813 : Blo 1277957 1943813 := bbase (se 4 (by rfl) ⟨182232, by rfl⟩ : syracuseStep 1943813 = 364465) (by norm_num)
theorem B1919237 : Blo 1277957 1919237 := bbase (se 4 (by rfl) ⟨179928, by rfl⟩ : syracuseStep 1919237 = 359857) (by norm_num)
theorem B3238157 : Blo 1277957 3238157 := bbase (se 3 (by rfl) ⟨607154, by rfl⟩ : syracuseStep 3238157 = 1214309) (by norm_num)
theorem B6474005 : Blo 1277957 6474005 := bbase (se 6 (by rfl) ⟨151734, by rfl⟩ : syracuseStep 6474005 = 303469) (by norm_num)
theorem B1919261 : Blo 1277957 1919261 := bbase (se 3 (by rfl) ⟨359861, by rfl⟩ : syracuseStep 1919261 = 719723) (by norm_num)
theorem B1640749 : Blo 1277957 1640749 := bbase (se 3 (by rfl) ⟨307640, by rfl⟩ : syracuseStep 1640749 = 615281) (by norm_num)
theorem B2877749 : Blo 1277957 2877749 := bbase (se 5 (by rfl) ⟨134894, by rfl⟩ : syracuseStep 2877749 = 269789) (by norm_num)
theorem B1919285 : Blo 1277957 1919285 := bbase (se 5 (by rfl) ⟨89966, by rfl⟩ : syracuseStep 1919285 = 179933) (by norm_num)
theorem B2156861 : Blo 1277957 2156861 := bbase (se 3 (by rfl) ⟨404411, by rfl⟩ : syracuseStep 2156861 = 808823) (by norm_num)
theorem B1919309 : Blo 1277957 1919309 := bbase (se 3 (by rfl) ⟨359870, by rfl⟩ : syracuseStep 1919309 = 719741) (by norm_num)
theorem B2427221 : Blo 1277957 2427221 := bbase (se 10 (by rfl) ⟨3555, by rfl⟩ : syracuseStep 2427221 = 7111) (by norm_num)
theorem B1919333 : Blo 1277957 1919333 := bbase (se 4 (by rfl) ⟨179937, by rfl⟩ : syracuseStep 1919333 = 359875) (by norm_num)
theorem B1821037 : Blo 1277957 1821037 := bbase (se 3 (by rfl) ⟨341444, by rfl⟩ : syracuseStep 1821037 = 682889) (by norm_num)
theorem B2877821 : Blo 1277957 2877821 := bbase (se 3 (by rfl) ⟨539591, by rfl⟩ : syracuseStep 2877821 = 1079183) (by norm_num)
theorem B1919357 : Blo 1277957 1919357 := bbase (se 3 (by rfl) ⟨359879, by rfl⟩ : syracuseStep 1919357 = 719759) (by norm_num)
theorem B4319621 : Blo 1277957 4319621 := bbase (se 4 (by rfl) ⟨404964, by rfl⟩ : syracuseStep 4319621 = 809929) (by norm_num)
theorem B2591117 : Blo 1277957 2591117 := bbase (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) (by norm_num)
theorem B8751509 : Blo 1277957 8751509 := bbase (se 6 (by rfl) ⟨205113, by rfl⟩ : syracuseStep 8751509 = 410227) (by norm_num)
theorem B1919381 : Blo 1277957 1919381 := bbase (se 6 (by rfl) ⟨44985, by rfl⟩ : syracuseStep 1919381 = 89971) (by norm_num)
theorem B1919405 : Blo 1277957 1919405 := bbase (se 3 (by rfl) ⟨359888, by rfl⟩ : syracuseStep 1919405 = 719777) (by norm_num)
theorem B2156989 : Blo 1277957 2156989 := bbase (se 3 (by rfl) ⟨404435, by rfl⟩ : syracuseStep 2156989 = 808871) (by norm_num)
theorem B2877893 : Blo 1277957 2877893 := bbase (se 4 (by rfl) ⟨269802, by rfl⟩ : syracuseStep 2877893 = 539605) (by norm_num)
theorem B1919429 : Blo 1277957 1919429 := bbase (se 4 (by rfl) ⟨179946, by rfl⟩ : syracuseStep 1919429 = 359893) (by norm_num)
theorem B1821133 : Blo 1277957 1821133 := bbase (se 3 (by rfl) ⟨341462, by rfl⟩ : syracuseStep 1821133 = 682925) (by norm_num)
theorem B1919453 : Blo 1277957 1919453 := bbase (se 3 (by rfl) ⟨359897, by rfl⟩ : syracuseStep 1919453 = 719795) (by norm_num)
theorem B3459557 : Blo 1277957 3459557 := bbase (se 4 (by rfl) ⟨324333, by rfl⟩ : syracuseStep 3459557 = 648667) (by norm_num)
theorem B1919477 : Blo 1277957 1919477 := bbase (se 5 (by rfl) ⟨89975, by rfl⟩ : syracuseStep 1919477 = 179951) (by norm_num)
theorem B2877965 : Blo 1277957 2877965 := bbase (se 3 (by rfl) ⟨539618, by rfl⟩ : syracuseStep 2877965 = 1079237) (by norm_num)
theorem B1919501 : Blo 1277957 1919501 := bbase (se 3 (by rfl) ⟨359906, by rfl⟩ : syracuseStep 1919501 = 719813) (by norm_num)
theorem B3639829 : Blo 1277957 3639829 := bbase (se 6 (by rfl) ⟨85308, by rfl⟩ : syracuseStep 3639829 = 170617) (by norm_num)
theorem B2157077 : Blo 1277957 2157077 := bbase (se 6 (by rfl) ⟨50556, by rfl⟩ : syracuseStep 2157077 = 101113) (by norm_num)
theorem B1296929 : Blo 1277957 1296929 := bbase (se 2 (by rfl) ⟨486348, by rfl⟩ : syracuseStep 1296929 = 972697) (by norm_num)
theorem B1919525 : Blo 1277957 1919525 := bbase (se 4 (by rfl) ⟨179955, by rfl⟩ : syracuseStep 1919525 = 359911) (by norm_num)
theorem B1919549 : Blo 1277957 1919549 := bbase (se 3 (by rfl) ⟨359915, by rfl⟩ : syracuseStep 1919549 = 719831) (by norm_num)
theorem B2878037 : Blo 1277957 2878037 := bbase (se 8 (by rfl) ⟨16863, by rfl⟩ : syracuseStep 2878037 = 33727) (by norm_num)
theorem B1919573 : Blo 1277957 1919573 := bbase (se 8 (by rfl) ⟨11247, by rfl⟩ : syracuseStep 1919573 = 22495) (by norm_num)
theorem B3238501 : Blo 1277957 3238501 := bbase (se 4 (by rfl) ⟨303609, by rfl⟩ : syracuseStep 3238501 = 607219) (by norm_num)
theorem B1919597 : Blo 1277957 1919597 := bbase (se 3 (by rfl) ⟨359924, by rfl⟩ : syracuseStep 1919597 = 719849) (by norm_num)
theorem B2427509 : Blo 1277957 2427509 := bbase (se 5 (by rfl) ⟨113789, by rfl⟩ : syracuseStep 2427509 = 227579) (by norm_num)
theorem B6564469 : Blo 1277957 6564469 := bbase (se 5 (by rfl) ⟨307709, by rfl⟩ : syracuseStep 6564469 = 615419) (by norm_num)
theorem B1919621 : Blo 1277957 1919621 := bbase (se 4 (by rfl) ⟨179964, by rfl⟩ : syracuseStep 1919621 = 359929) (by norm_num)
theorem B2157205 : Blo 1277957 2157205 := bbase (se 6 (by rfl) ⟨50559, by rfl⟩ : syracuseStep 2157205 = 101119) (by norm_num)
theorem B2878109 : Blo 1277957 2878109 := bbase (se 3 (by rfl) ⟨539645, by rfl⟩ : syracuseStep 2878109 = 1079291) (by norm_num)
theorem B1919645 : Blo 1277957 1919645 := bbase (se 3 (by rfl) ⟨359933, by rfl⟩ : syracuseStep 1919645 = 719867) (by norm_num)
theorem B1919669 : Blo 1277957 1919669 := bbase (se 5 (by rfl) ⟨89984, by rfl⟩ : syracuseStep 1919669 = 179969) (by norm_num)
theorem B1919693 : Blo 1277957 1919693 := bbase (se 3 (by rfl) ⟨359942, by rfl⟩ : syracuseStep 1919693 = 719885) (by norm_num)
theorem B2730709 : Blo 1277957 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B3238613 : Blo 1277957 3238613 := bbase (se 7 (by rfl) ⟨37952, by rfl⟩ : syracuseStep 3238613 = 75905) (by norm_num)
theorem B2878181 : Blo 1277957 2878181 := bbase (se 4 (by rfl) ⟨269829, by rfl⟩ : syracuseStep 2878181 = 539659) (by norm_num)
theorem B1919717 : Blo 1277957 1919717 := bbase (se 4 (by rfl) ⟨179973, by rfl⟩ : syracuseStep 1919717 = 359947) (by norm_num)
theorem B2157293 : Blo 1277957 2157293 := bbase (se 3 (by rfl) ⟨404492, by rfl⟩ : syracuseStep 2157293 = 808985) (by norm_num)
theorem B3074797 : Blo 1277957 3074797 := bbase (se 3 (by rfl) ⟨576524, by rfl⟩ : syracuseStep 3074797 = 1153049) (by norm_num)
theorem B1919741 : Blo 1277957 1919741 := bbase (se 3 (by rfl) ⟨359951, by rfl⟩ : syracuseStep 1919741 = 719903) (by norm_num)
theorem B3328765 : Blo 1277957 3328765 := bbase (se 3 (by rfl) ⟨624143, by rfl⟩ : syracuseStep 3328765 = 1248287) (by norm_num)
theorem B2427661 : Blo 1277957 2427661 := bbase (se 3 (by rfl) ⟨455186, by rfl⟩ : syracuseStep 2427661 = 910373) (by norm_num)
theorem B1919765 : Blo 1277957 1919765 := bbase (se 6 (by rfl) ⟨44994, by rfl⟩ : syracuseStep 1919765 = 89989) (by norm_num)
theorem B2878253 : Blo 1277957 2878253 := bbase (se 3 (by rfl) ⟨539672, by rfl⟩ : syracuseStep 2878253 = 1079345) (by norm_num)
theorem B1919789 : Blo 1277957 1919789 := bbase (se 3 (by rfl) ⟨359960, by rfl⟩ : syracuseStep 1919789 = 719921) (by norm_num)
theorem B1919813 : Blo 1277957 1919813 := bbase (se 4 (by rfl) ⟨179982, by rfl⟩ : syracuseStep 1919813 = 359965) (by norm_num)
theorem B2730829 : Blo 1277957 2730829 := bbase (se 3 (by rfl) ⟨512030, by rfl⟩ : syracuseStep 2730829 = 1024061) (by norm_num)
theorem B1919837 : Blo 1277957 1919837 := bbase (se 3 (by rfl) ⟨359969, by rfl⟩ : syracuseStep 1919837 = 719939) (by norm_num)
theorem B2157421 : Blo 1277957 2157421 := bbase (se 3 (by rfl) ⟨404516, by rfl⟩ : syracuseStep 2157421 = 809033) (by norm_num)
theorem B2878325 : Blo 1277957 2878325 := bbase (se 5 (by rfl) ⟨134921, by rfl⟩ : syracuseStep 2878325 = 269843) (by norm_num)
theorem B1919861 : Blo 1277957 1919861 := bbase (se 5 (by rfl) ⟨89993, by rfl⟩ : syracuseStep 1919861 = 179987) (by norm_num)
theorem B1919885 : Blo 1277957 1919885 := bbase (se 3 (by rfl) ⟨359978, by rfl⟩ : syracuseStep 1919885 = 719957) (by norm_num)
theorem B3238805 : Blo 1277957 3238805 := bbase (se 6 (by rfl) ⟨75909, by rfl⟩ : syracuseStep 3238805 = 151819) (by norm_num)
theorem B4377509 : Blo 1277957 4377509 := bbase (se 4 (by rfl) ⟨410391, by rfl⟩ : syracuseStep 4377509 = 820783) (by norm_num)
theorem B1919909 : Blo 1277957 1919909 := bbase (se 4 (by rfl) ⟨179991, by rfl⟩ : syracuseStep 1919909 = 359983) (by norm_num)
theorem B2878397 : Blo 1277957 2878397 := bbase (se 3 (by rfl) ⟨539699, by rfl⟩ : syracuseStep 2878397 = 1079399) (by norm_num)
theorem B1821629 : Blo 1277957 1821629 := bbase (se 3 (by rfl) ⟨341555, by rfl⟩ : syracuseStep 1821629 = 683111) (by norm_num)
theorem B1919933 : Blo 1277957 1919933 := bbase (se 3 (by rfl) ⟨359987, by rfl⟩ : syracuseStep 1919933 = 719975) (by norm_num)
theorem B2157509 : Blo 1277957 2157509 := bbase (se 4 (by rfl) ⟨202266, by rfl⟩ : syracuseStep 2157509 = 404533) (by norm_num)
theorem B1313749 : Blo 1277957 1313749 := bbase (se 7 (by rfl) ⟨15395, by rfl⟩ : syracuseStep 1313749 = 30791) (by norm_num)
theorem B3075029 : Blo 1277957 3075029 := bbase (se 7 (by rfl) ⟨36035, by rfl⟩ : syracuseStep 3075029 = 72071) (by norm_num)
theorem B2878469 : Blo 1277957 2878469 := bbase (se 4 (by rfl) ⟨269856, by rfl⟩ : syracuseStep 2878469 = 539713) (by norm_num)
theorem B3075077 : Blo 1277957 3075077 := bbase (se 4 (by rfl) ⟨288288, by rfl⟩ : syracuseStep 3075077 = 576577) (by norm_num)
theorem B2305045 : Blo 1277957 2305045 := bbase (se 6 (by rfl) ⟨54024, by rfl⟩ : syracuseStep 2305045 = 108049) (by norm_num)
theorem B2427965 : Blo 1277957 2427965 := bbase (se 3 (by rfl) ⟨455243, by rfl⟩ : syracuseStep 2427965 = 910487) (by norm_num)
theorem B2591813 : Blo 1277957 2591813 := bbase (se 4 (by rfl) ⟨242982, by rfl⟩ : syracuseStep 2591813 = 485965) (by norm_num)
theorem B2157637 : Blo 1277957 2157637 := bbase (se 4 (by rfl) ⟨202278, by rfl⟩ : syracuseStep 2157637 = 404557) (by norm_num)
theorem B2731085 : Blo 1277957 2731085 := bbase (se 3 (by rfl) ⟨512078, by rfl⟩ : syracuseStep 2731085 = 1024157) (by norm_num)
theorem B2878541 : Blo 1277957 2878541 := bbase (se 3 (by rfl) ⟨539726, by rfl⟩ : syracuseStep 2878541 = 1079453) (by norm_num)
theorem B2878613 : Blo 1277957 2878613 := bbase (se 6 (by rfl) ⟨67467, by rfl⟩ : syracuseStep 2878613 = 134935) (by norm_num)
theorem B2157725 : Blo 1277957 2157725 := bbase (se 3 (by rfl) ⟨404573, by rfl⟩ : syracuseStep 2157725 = 809147) (by norm_num)
theorem B2878685 : Blo 1277957 2878685 := bbase (se 3 (by rfl) ⟨539753, by rfl⟩ : syracuseStep 2878685 = 1079507) (by norm_num)
theorem B3239149 : Blo 1277957 3239149 := bbase (se 3 (by rfl) ⟨607340, by rfl⟩ : syracuseStep 3239149 = 1214681) (by norm_num)
theorem B2157853 : Blo 1277957 2157853 := bbase (se 3 (by rfl) ⟨404597, by rfl⟩ : syracuseStep 2157853 = 809195) (by norm_num)
theorem B2878757 : Blo 1277957 2878757 := bbase (se 4 (by rfl) ⟨269883, by rfl⟩ : syracuseStep 2878757 = 539767) (by norm_num)
theorem B2305349 : Blo 1277957 2305349 := bbase (se 4 (by rfl) ⟨216126, by rfl⟩ : syracuseStep 2305349 = 432253) (by norm_num)
theorem B3239261 : Blo 1277957 3239261 := bbase (se 3 (by rfl) ⟨607361, by rfl⟩ : syracuseStep 3239261 = 1214723) (by norm_num)
theorem B2878829 : Blo 1277957 2878829 := bbase (se 3 (by rfl) ⟨539780, by rfl⟩ : syracuseStep 2878829 = 1079561) (by norm_num)
theorem B2157941 : Blo 1277957 2157941 := bbase (se 5 (by rfl) ⟨101153, by rfl⟩ : syracuseStep 2157941 = 202307) (by norm_num)
theorem B5328293 : Blo 1277957 5328293 := bbase (se 4 (by rfl) ⟨499527, by rfl⟩ : syracuseStep 5328293 = 999055) (by norm_num)
theorem B8195509 : Blo 1277957 8195509 := bbase (se 5 (by rfl) ⟨384164, by rfl⟩ : syracuseStep 8195509 = 768329) (by norm_num)
theorem B2878901 : Blo 1277957 2878901 := bbase (se 5 (by rfl) ⟨134948, by rfl⟩ : syracuseStep 2878901 = 269897) (by norm_num)
theorem B1822181 : Blo 1277957 1822181 := bbase (se 4 (by rfl) ⟨170829, by rfl⟩ : syracuseStep 1822181 = 341659) (by norm_num)
theorem B2158069 : Blo 1277957 2158069 := bbase (se 5 (by rfl) ⟨101159, by rfl⟩ : syracuseStep 2158069 = 202319) (by norm_num)
theorem B2878973 : Blo 1277957 2878973 := bbase (se 3 (by rfl) ⟨539807, by rfl⟩ : syracuseStep 2878973 = 1079615) (by norm_num)
theorem B3501589 : Blo 1277957 3501589 := bbase (se 6 (by rfl) ⟨82068, by rfl⟩ : syracuseStep 3501589 = 164137) (by norm_num)
theorem B3239453 : Blo 1277957 3239453 := bbase (se 3 (by rfl) ⟨607397, by rfl⟩ : syracuseStep 3239453 = 1214795) (by norm_num)
theorem B6475301 : Blo 1277957 6475301 := bbase (se 4 (by rfl) ⟨607059, by rfl⟩ : syracuseStep 6475301 = 1214119) (by norm_num)
theorem B4853317 : Blo 1277957 4853317 := bbase (se 4 (by rfl) ⟨454998, by rfl⟩ : syracuseStep 4853317 = 909997) (by norm_num)
theorem B2879045 : Blo 1277957 2879045 := bbase (se 4 (by rfl) ⟨269910, by rfl⟩ : syracuseStep 2879045 = 539821) (by norm_num)
theorem B2158157 : Blo 1277957 2158157 := bbase (se 3 (by rfl) ⟨404654, by rfl⟩ : syracuseStep 2158157 = 809309) (by norm_num)
theorem B1617509 : Blo 1277957 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B2879117 : Blo 1277957 2879117 := bbase (se 3 (by rfl) ⟨539834, by rfl⟩ : syracuseStep 2879117 = 1079669) (by norm_num)
theorem B1617565 : Blo 1277957 1617565 := bbase (se 3 (by rfl) ⟨303293, by rfl⟩ : syracuseStep 1617565 = 606587) (by norm_num)
theorem B2158285 : Blo 1277957 2158285 := bbase (se 3 (by rfl) ⟨404678, by rfl⟩ : syracuseStep 2158285 = 809357) (by norm_num)
theorem B2879189 : Blo 1277957 2879189 := bbase (se 7 (by rfl) ⟨33740, by rfl⟩ : syracuseStep 2879189 = 67481) (by norm_num)
theorem B1617661 : Blo 1277957 1617661 := bbase (se 3 (by rfl) ⟨303311, by rfl⟩ : syracuseStep 1617661 = 606623) (by norm_num)
theorem B14561045 : Blo 1277957 14561045 := bbase (se 6 (by rfl) ⟨341274, by rfl⟩ : syracuseStep 14561045 = 682549) (by norm_num)
theorem B2879261 : Blo 1277957 2879261 := bbase (se 3 (by rfl) ⟨539861, by rfl⟩ : syracuseStep 2879261 = 1079723) (by norm_num)
theorem B2158373 : Blo 1277957 2158373 := bbase (se 4 (by rfl) ⟨202347, by rfl⟩ : syracuseStep 2158373 = 404695) (by norm_num)
theorem B2428717 : Blo 1277957 2428717 := bbase (se 3 (by rfl) ⟨455384, by rfl⟩ : syracuseStep 2428717 = 910769) (by norm_num)
theorem B4378421 : Blo 1277957 4378421 := bbase (se 5 (by rfl) ⟨205238, by rfl⟩ : syracuseStep 4378421 = 410477) (by norm_num)
theorem B2879333 : Blo 1277957 2879333 := bbase (se 4 (by rfl) ⟨269937, by rfl⟩ : syracuseStep 2879333 = 539875) (by norm_num)
theorem B4853621 : Blo 1277957 4853621 := bbase (se 5 (by rfl) ⟨227513, by rfl⟩ : syracuseStep 4853621 = 455027) (by norm_num)
theorem B1535861 : Blo 1277957 1535861 := bbase (se 5 (by rfl) ⟨71993, by rfl⟩ : syracuseStep 1535861 = 143987) (by norm_num)
theorem B3239797 : Blo 1277957 3239797 := bbase (se 5 (by rfl) ⟨151865, by rfl⟩ : syracuseStep 3239797 = 303731) (by norm_num)
theorem B2158501 : Blo 1277957 2158501 := bbase (se 4 (by rfl) ⟨202359, by rfl⟩ : syracuseStep 2158501 = 404719) (by norm_num)
theorem B1617833 : Blo 1277957 1617833 := bbase (se 2 (by rfl) ⟨606687, by rfl⟩ : syracuseStep 1617833 = 1213375) (by norm_num)
theorem B2879405 : Blo 1277957 2879405 := bbase (se 3 (by rfl) ⟨539888, by rfl⟩ : syracuseStep 2879405 = 1079777) (by norm_num)
theorem B2428861 : Blo 1277957 2428861 := bbase (se 3 (by rfl) ⟨455411, by rfl⟩ : syracuseStep 2428861 = 910823) (by norm_num)
theorem B2731973 : Blo 1277957 2731973 := bbase (se 4 (by rfl) ⟨256122, by rfl⟩ : syracuseStep 2731973 = 512245) (by norm_num)
theorem B3280861 : Blo 1277957 3280861 := bbase (se 3 (by rfl) ⟨615161, by rfl⟩ : syracuseStep 3280861 = 1230323) (by norm_num)
theorem B1617889 : Blo 1277957 1617889 := bbase (se 2 (by rfl) ⟨606708, by rfl⟩ : syracuseStep 1617889 = 1213417) (by norm_num)
theorem B2879477 : Blo 1277957 2879477 := bbase (se 5 (by rfl) ⟨134975, by rfl⟩ : syracuseStep 2879477 = 269951) (by norm_num)
theorem B2158589 : Blo 1277957 2158589 := bbase (se 3 (by rfl) ⟨404735, by rfl⟩ : syracuseStep 2158589 = 809471) (by norm_num)
theorem B1437709 : Blo 1277957 1437709 := bbase (se 3 (by rfl) ⟨269570, by rfl⟩ : syracuseStep 1437709 = 539141) (by norm_num)
theorem B1437745 : Blo 1277957 1437745 := bbase (se 2 (by rfl) ⟨539154, by rfl⟩ : syracuseStep 1437745 = 1078309) (by norm_num)
theorem B4313141 : Blo 1277957 4313141 := bbase (se 5 (by rfl) ⟨202178, by rfl⟩ : syracuseStep 4313141 = 404357) (by norm_num)
theorem B2879549 : Blo 1277957 2879549 := bbase (se 3 (by rfl) ⟨539915, by rfl⟩ : syracuseStep 2879549 = 1079831) (by norm_num)
theorem B1617985 : Blo 1277957 1617985 := bbase (se 2 (by rfl) ⟨606744, by rfl⟩ : syracuseStep 1617985 = 1213489) (by norm_num)
theorem B4100165 : Blo 1277957 4100165 := bbase (se 4 (by rfl) ⟨384390, by rfl⟩ : syracuseStep 4100165 = 768781) (by norm_num)
theorem B1437781 : Blo 1277957 1437781 := bbase (se 8 (by rfl) ⟨8424, by rfl⟩ : syracuseStep 1437781 = 16849) (by norm_num)
theorem B2429021 : Blo 1277957 2429021 := bbase (se 3 (by rfl) ⟨455441, by rfl⟩ : syracuseStep 2429021 = 910883) (by norm_num)
theorem B1437817 : Blo 1277957 1437817 := bbase (se 2 (by rfl) ⟨539181, by rfl⟩ : syracuseStep 1437817 = 1078363) (by norm_num)
theorem B2158717 : Blo 1277957 2158717 := bbase (se 3 (by rfl) ⟨404759, by rfl⟩ : syracuseStep 2158717 = 809519) (by norm_num)
theorem B2879621 : Blo 1277957 2879621 := bbase (se 4 (by rfl) ⟨269964, by rfl⟩ : syracuseStep 2879621 = 539929) (by norm_num)
theorem B1437853 : Blo 1277957 1437853 := bbase (se 3 (by rfl) ⟨269597, by rfl⟩ : syracuseStep 1437853 = 539195) (by norm_num)
theorem B2732213 : Blo 1277957 2732213 := bbase (se 5 (by rfl) ⟨128072, by rfl⟩ : syracuseStep 2732213 = 256145) (by norm_num)
theorem B1437889 : Blo 1277957 1437889 := bbase (se 2 (by rfl) ⟨539208, by rfl⟩ : syracuseStep 1437889 = 1078417) (by norm_num)
theorem B1536193 : Blo 1277957 1536193 := bbase (se 2 (by rfl) ⟨576072, by rfl⟩ : syracuseStep 1536193 = 1152145) (by norm_num)
theorem B2879693 : Blo 1277957 2879693 := bbase (se 3 (by rfl) ⟨539942, by rfl⟩ : syracuseStep 2879693 = 1079885) (by norm_num)
theorem B2158805 : Blo 1277957 2158805 := bbase (se 7 (by rfl) ⟨25298, by rfl⟩ : syracuseStep 2158805 = 50597) (by norm_num)
theorem B1437925 : Blo 1277957 1437925 := bbase (se 4 (by rfl) ⟨134805, by rfl⟩ : syracuseStep 1437925 = 269611) (by norm_num)
theorem B6148325 : Blo 1277957 6148325 := bbase (se 4 (by rfl) ⟨576405, by rfl⟩ : syracuseStep 6148325 = 1152811) (by norm_num)
theorem B1618157 : Blo 1277957 1618157 := bbase (se 3 (by rfl) ⟨303404, by rfl⟩ : syracuseStep 1618157 = 606809) (by norm_num)
theorem B2429165 : Blo 1277957 2429165 := bbase (se 3 (by rfl) ⟨455468, by rfl⟩ : syracuseStep 2429165 = 910937) (by norm_num)
theorem B4608245 : Blo 1277957 4608245 := bbase (se 5 (by rfl) ⟨216011, by rfl⟩ : syracuseStep 4608245 = 432023) (by norm_num)
theorem B1437961 : Blo 1277957 1437961 := bbase (se 2 (by rfl) ⟨539235, by rfl⟩ : syracuseStep 1437961 = 1078471) (by norm_num)
theorem B12144917 : Blo 1277957 12144917 := bbase (se 6 (by rfl) ⟨284646, by rfl⟩ : syracuseStep 12144917 = 569293) (by norm_num)
theorem B6918421 : Blo 1277957 6918421 := bbase (se 6 (by rfl) ⟨162150, by rfl⟩ : syracuseStep 6918421 = 324301) (by norm_num)
theorem B2879765 : Blo 1277957 2879765 := bbase (se 6 (by rfl) ⟨67494, by rfl⟩ : syracuseStep 2879765 = 134989) (by norm_num)
theorem B1618213 : Blo 1277957 1618213 := bbase (se 4 (by rfl) ⟨151707, by rfl⟩ : syracuseStep 1618213 = 303415) (by norm_num)
theorem B1437997 : Blo 1277957 1437997 := bbase (se 3 (by rfl) ⟨269624, by rfl⟩ : syracuseStep 1437997 = 539249) (by norm_num)
theorem B1438033 : Blo 1277957 1438033 := bbase (se 2 (by rfl) ⟨539262, by rfl⟩ : syracuseStep 1438033 = 1078525) (by norm_num)
theorem B2158933 : Blo 1277957 2158933 := bbase (se 10 (by rfl) ⟨3162, by rfl⟩ : syracuseStep 2158933 = 6325) (by norm_num)
theorem B2462045 : Blo 1277957 2462045 := bbase (se 3 (by rfl) ⟨461633, by rfl⟩ : syracuseStep 2462045 = 923267) (by norm_num)
theorem B2879837 : Blo 1277957 2879837 := bbase (se 3 (by rfl) ⟨539969, by rfl⟩ : syracuseStep 2879837 = 1079939) (by norm_num)
theorem B1438069 : Blo 1277957 1438069 := bbase (se 5 (by rfl) ⟨67409, by rfl⟩ : syracuseStep 1438069 = 134819) (by norm_num)
theorem B1618309 : Blo 1277957 1618309 := bbase (se 4 (by rfl) ⟨151716, by rfl⟩ : syracuseStep 1618309 = 303433) (by norm_num)
theorem B1438105 : Blo 1277957 1438105 := bbase (se 2 (by rfl) ⟨539289, by rfl⟩ : syracuseStep 1438105 = 1078579) (by norm_num)
theorem B2077085 : Blo 1277957 2077085 := bbase (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) (by norm_num)
theorem B2159021 : Blo 1277957 2159021 := bbase (se 3 (by rfl) ⟨404816, by rfl⟩ : syracuseStep 2159021 = 809633) (by norm_num)
theorem B1438141 : Blo 1277957 1438141 := bbase (se 3 (by rfl) ⟨269651, by rfl⟩ : syracuseStep 1438141 = 539303) (by norm_num)
theorem B1438177 : Blo 1277957 1438177 := bbase (se 2 (by rfl) ⟨539316, by rfl⟩ : syracuseStep 1438177 = 1078633) (by norm_num)
theorem B4313573 : Blo 1277957 4313573 := bbase (se 4 (by rfl) ⟨404397, by rfl⟩ : syracuseStep 4313573 = 808795) (by norm_num)
theorem B1438213 : Blo 1277957 1438213 := bbase (se 4 (by rfl) ⟨134832, by rfl⟩ : syracuseStep 1438213 = 269665) (by norm_num)
theorem B2429453 : Blo 1277957 2429453 := bbase (se 3 (by rfl) ⟨455522, by rfl⟩ : syracuseStep 2429453 = 911045) (by norm_num)
theorem B4608533 : Blo 1277957 4608533 := bbase (se 6 (by rfl) ⟨108012, by rfl⟩ : syracuseStep 4608533 = 216025) (by norm_num)
theorem B1438249 : Blo 1277957 1438249 := bbase (se 2 (by rfl) ⟨539343, by rfl⟩ : syracuseStep 1438249 = 1078687) (by norm_num)
theorem B2159149 : Blo 1277957 2159149 := bbase (se 3 (by rfl) ⟨404840, by rfl⟩ : syracuseStep 2159149 = 809681) (by norm_num)
theorem B1618481 : Blo 1277957 1618481 := bbase (se 2 (by rfl) ⟨606930, by rfl⟩ : syracuseStep 1618481 = 1213861) (by norm_num)
theorem B1438285 : Blo 1277957 1438285 := bbase (se 3 (by rfl) ⟨269678, by rfl⟩ : syracuseStep 1438285 = 539357) (by norm_num)
theorem B1618537 : Blo 1277957 1618537 := bbase (se 2 (by rfl) ⟨606951, by rfl⟩ : syracuseStep 1618537 = 1213903) (by norm_num)
theorem B1438321 : Blo 1277957 1438321 := bbase (se 2 (by rfl) ⟨539370, by rfl⟩ : syracuseStep 1438321 = 1078741) (by norm_num)
theorem B2159237 : Blo 1277957 2159237 := bbase (se 4 (by rfl) ⟨202428, by rfl⟩ : syracuseStep 2159237 = 404857) (by norm_num)
theorem B1438357 : Blo 1277957 1438357 := bbase (se 6 (by rfl) ⟨33711, by rfl⟩ : syracuseStep 1438357 = 67423) (by norm_num)
theorem B2429605 : Blo 1277957 2429605 := bbase (se 4 (by rfl) ⟨227775, by rfl⟩ : syracuseStep 2429605 = 455551) (by norm_num)
theorem B2732717 : Blo 1277957 2732717 := bbase (se 3 (by rfl) ⟨512384, by rfl⟩ : syracuseStep 2732717 = 1024769) (by norm_num)
theorem B2732725 : Blo 1277957 2732725 := bbase (se 5 (by rfl) ⟨128096, by rfl⟩ : syracuseStep 2732725 = 256193) (by norm_num)
theorem B1438393 : Blo 1277957 1438393 := bbase (se 2 (by rfl) ⟨539397, by rfl⟩ : syracuseStep 1438393 = 1078795) (by norm_num)
theorem B1618633 : Blo 1277957 1618633 := bbase (se 2 (by rfl) ⟨606987, by rfl⟩ : syracuseStep 1618633 = 1213975) (by norm_num)
theorem B1438429 : Blo 1277957 1438429 := bbase (se 3 (by rfl) ⟨269705, by rfl⟩ : syracuseStep 1438429 = 539411) (by norm_num)
theorem B1438465 : Blo 1277957 1438465 := bbase (se 2 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 1438465 = 1078849) (by norm_num)
theorem B2159365 : Blo 1277957 2159365 := bbase (se 4 (by rfl) ⟨202440, by rfl⟩ : syracuseStep 2159365 = 404881) (by norm_num)
theorem B1438501 : Blo 1277957 1438501 := bbase (se 4 (by rfl) ⟨134859, by rfl⟩ : syracuseStep 1438501 = 269719) (by norm_num)
theorem B6476597 : Blo 1277957 6476597 := bbase (se 5 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 6476597 = 607181) (by norm_num)
theorem B1438537 : Blo 1277957 1438537 := bbase (se 2 (by rfl) ⟨539451, by rfl⟩ : syracuseStep 1438537 = 1078903) (by norm_num)
theorem B2159453 : Blo 1277957 2159453 := bbase (se 3 (by rfl) ⟨404897, by rfl⟩ : syracuseStep 2159453 = 809795) (by norm_num)
theorem B1438573 : Blo 1277957 1438573 := bbase (se 3 (by rfl) ⟨269732, by rfl⟩ : syracuseStep 1438573 = 539465) (by norm_num)
theorem B1618805 : Blo 1277957 1618805 := bbase (se 5 (by rfl) ⟨75881, by rfl⟩ : syracuseStep 1618805 = 151763) (by norm_num)
theorem B1536889 : Blo 1277957 1536889 := bbase (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) (by norm_num)
theorem B1438609 : Blo 1277957 1438609 := bbase (se 2 (by rfl) ⟨539478, by rfl⟩ : syracuseStep 1438609 = 1078957) (by norm_num)
theorem B4314005 : Blo 1277957 4314005 := bbase (se 6 (by rfl) ⟨101109, by rfl⟩ : syracuseStep 4314005 = 202219) (by norm_num)
theorem B1364893 : Blo 1277957 1364893 := bbase (se 3 (by rfl) ⟨255917, by rfl⟩ : syracuseStep 1364893 = 511835) (by norm_num)
theorem B1536937 : Blo 1277957 1536937 := bbase (se 2 (by rfl) ⟨576351, by rfl⟩ : syracuseStep 1536937 = 1152703) (by norm_num)
theorem B1618861 : Blo 1277957 1618861 := bbase (se 3 (by rfl) ⟨303536, by rfl⟩ : syracuseStep 1618861 = 607073) (by norm_num)
theorem B1438645 : Blo 1277957 1438645 := bbase (se 5 (by rfl) ⟨67436, by rfl⟩ : syracuseStep 1438645 = 134873) (by norm_num)
theorem B2429909 : Blo 1277957 2429909 := bbase (se 7 (by rfl) ⟨28475, by rfl⟩ : syracuseStep 2429909 = 56951) (by norm_num)
theorem B1438681 : Blo 1277957 1438681 := bbase (se 2 (by rfl) ⟨539505, by rfl⟩ : syracuseStep 1438681 = 1079011) (by norm_num)
theorem B2159581 : Blo 1277957 2159581 := bbase (se 3 (by rfl) ⟨404921, by rfl⟩ : syracuseStep 2159581 = 809843) (by norm_num)
theorem B1438717 : Blo 1277957 1438717 := bbase (se 3 (by rfl) ⟨269759, by rfl⟩ : syracuseStep 1438717 = 539519) (by norm_num)
theorem B1618957 : Blo 1277957 1618957 := bbase (se 3 (by rfl) ⟨303554, by rfl⟩ : syracuseStep 1618957 = 607109) (by norm_num)
theorem B1365013 : Blo 1277957 1365013 := bbase (se 6 (by rfl) ⟨31992, by rfl⟩ : syracuseStep 1365013 = 63985) (by norm_num)
theorem B1438753 : Blo 1277957 1438753 := bbase (se 2 (by rfl) ⟨539532, by rfl⟩ : syracuseStep 1438753 = 1079065) (by norm_num)
theorem B2159669 : Blo 1277957 2159669 := bbase (se 5 (by rfl) ⟨101234, by rfl⟩ : syracuseStep 2159669 = 202469) (by norm_num)
theorem B1438789 : Blo 1277957 1438789 := bbase (se 4 (by rfl) ⟨134886, by rfl⟩ : syracuseStep 1438789 = 269773) (by norm_num)
theorem B1438825 : Blo 1277957 1438825 := bbase (se 2 (by rfl) ⟨539559, by rfl⟩ : syracuseStep 1438825 = 1079119) (by norm_num)
theorem B1438861 : Blo 1277957 1438861 := bbase (se 3 (by rfl) ⟨269786, by rfl⟩ : syracuseStep 1438861 = 539573) (by norm_num)
theorem B1438897 : Blo 1277957 1438897 := bbase (se 2 (by rfl) ⟨539586, by rfl⟩ : syracuseStep 1438897 = 1079173) (by norm_num)
theorem B7779509 : Blo 1277957 7779509 := bbase (se 5 (by rfl) ⟨364664, by rfl⟩ : syracuseStep 7779509 = 729329) (by norm_num)
theorem B2159797 : Blo 1277957 2159797 := bbase (se 5 (by rfl) ⟨101240, by rfl⟩ : syracuseStep 2159797 = 202481) (by norm_num)
theorem B1619129 : Blo 1277957 1619129 := bbase (se 2 (by rfl) ⟨607173, by rfl⟩ : syracuseStep 1619129 = 1214347) (by norm_num)
theorem B1438933 : Blo 1277957 1438933 := bbase (se 7 (by rfl) ⟨16862, by rfl⟩ : syracuseStep 1438933 = 33725) (by norm_num)
theorem B1619185 : Blo 1277957 1619185 := bbase (se 2 (by rfl) ⟨607194, by rfl⟩ : syracuseStep 1619185 = 1214389) (by norm_num)
theorem B1438969 : Blo 1277957 1438969 := bbase (se 2 (by rfl) ⟨539613, by rfl⟩ : syracuseStep 1438969 = 1079227) (by norm_num)
theorem B2159885 : Blo 1277957 2159885 := bbase (se 3 (by rfl) ⟨404978, by rfl⟩ : syracuseStep 2159885 = 809957) (by norm_num)
theorem B1365265 : Blo 1277957 1365265 := bbase (se 2 (by rfl) ⟨511974, by rfl⟩ : syracuseStep 1365265 = 1023949) (by norm_num)
theorem B1365269 : Blo 1277957 1365269 := bbase (se 6 (by rfl) ⟨31998, by rfl⟩ : syracuseStep 1365269 = 63997) (by norm_num)
theorem B1439005 : Blo 1277957 1439005 := bbase (se 3 (by rfl) ⟨269813, by rfl⟩ : syracuseStep 1439005 = 539627) (by norm_num)
theorem B3642677 : Blo 1277957 3642677 := bbase (se 5 (by rfl) ⟨170750, by rfl⟩ : syracuseStep 3642677 = 341501) (by norm_num)
theorem B2594101 : Blo 1277957 2594101 := bbase (se 5 (by rfl) ⟨121598, by rfl⟩ : syracuseStep 2594101 = 243197) (by norm_num)
theorem B1439041 : Blo 1277957 1439041 := bbase (se 2 (by rfl) ⟨539640, by rfl⟩ : syracuseStep 1439041 = 1079281) (by norm_num)
theorem B4314437 : Blo 1277957 4314437 := bbase (se 4 (by rfl) ⟨404478, by rfl⟩ : syracuseStep 4314437 = 808957) (by norm_num)
theorem B3372365 : Blo 1277957 3372365 := bbase (se 3 (by rfl) ⟨632318, by rfl⟩ : syracuseStep 3372365 = 1264637) (by norm_num)
theorem B1619281 : Blo 1277957 1619281 := bbase (se 2 (by rfl) ⟨607230, by rfl⟩ : syracuseStep 1619281 = 1214461) (by norm_num)
theorem B12285269 : Blo 1277957 12285269 := bbase (se 13 (by rfl) ⟨2249, by rfl⟩ : syracuseStep 12285269 = 4499) (by norm_num)
theorem B1439077 : Blo 1277957 1439077 := bbase (se 4 (by rfl) ⟨134913, by rfl⟩ : syracuseStep 1439077 = 269827) (by norm_num)
theorem B1439113 : Blo 1277957 1439113 := bbase (se 2 (by rfl) ⟨539667, by rfl⟩ : syracuseStep 1439113 = 1079335) (by norm_num)
theorem B1439149 : Blo 1277957 1439149 := bbase (se 3 (by rfl) ⟨269840, by rfl⟩ : syracuseStep 1439149 = 539681) (by norm_num)
theorem B1439185 : Blo 1277957 1439185 := bbase (se 2 (by rfl) ⟨539694, by rfl⟩ : syracuseStep 1439185 = 1079389) (by norm_num)
theorem B1439221 : Blo 1277957 1439221 := bbase (se 5 (by rfl) ⟨67463, by rfl⟩ : syracuseStep 1439221 = 134927) (by norm_num)
theorem B1619453 : Blo 1277957 1619453 := bbase (se 3 (by rfl) ⟨303647, by rfl⟩ : syracuseStep 1619453 = 607295) (by norm_num)
theorem B1439257 : Blo 1277957 1439257 := bbase (se 2 (by rfl) ⟨539721, by rfl⟩ : syracuseStep 1439257 = 1079443) (by norm_num)
theorem B1619509 : Blo 1277957 1619509 := bbase (se 5 (by rfl) ⟨75914, by rfl⟩ : syracuseStep 1619509 = 151829) (by norm_num)
theorem B1439293 : Blo 1277957 1439293 := bbase (se 3 (by rfl) ⟨269867, by rfl⟩ : syracuseStep 1439293 = 539735) (by norm_num)
theorem B1439329 : Blo 1277957 1439329 := bbase (se 2 (by rfl) ⟨539748, by rfl⟩ : syracuseStep 1439329 = 1079497) (by norm_num)
theorem B6141541 : Blo 1277957 6141541 := bbase (se 4 (by rfl) ⟨575769, by rfl⟩ : syracuseStep 6141541 = 1151539) (by norm_num)
theorem B3282565 : Blo 1277957 3282565 := bbase (se 4 (by rfl) ⟨307740, by rfl⟩ : syracuseStep 3282565 = 615481) (by norm_num)
theorem B1439365 : Blo 1277957 1439365 := bbase (se 4 (by rfl) ⟨134940, by rfl⟩ : syracuseStep 1439365 = 269881) (by norm_num)
theorem B5060245 : Blo 1277957 5060245 := bbase (se 6 (by rfl) ⟨118599, by rfl⟩ : syracuseStep 5060245 = 237199) (by norm_num)
theorem B1619605 : Blo 1277957 1619605 := bbase (se 6 (by rfl) ⟨37959, by rfl⟩ : syracuseStep 1619605 = 75919) (by norm_num)
theorem B1439401 : Blo 1277957 1439401 := bbase (se 2 (by rfl) ⟨539775, by rfl⟩ : syracuseStep 1439401 = 1079551) (by norm_num)
theorem B1439437 : Blo 1277957 1439437 := bbase (se 3 (by rfl) ⟨269894, by rfl⟩ : syracuseStep 1439437 = 539789) (by norm_num)
theorem B1439473 : Blo 1277957 1439473 := bbase (se 2 (by rfl) ⟨539802, by rfl⟩ : syracuseStep 1439473 = 1079605) (by norm_num)
theorem B4314869 : Blo 1277957 4314869 := bbase (se 5 (by rfl) ⟨202259, by rfl⟩ : syracuseStep 4314869 = 404519) (by norm_num)
theorem B1439509 : Blo 1277957 1439509 := bbase (se 6 (by rfl) ⟨33738, by rfl⟩ : syracuseStep 1439509 = 67477) (by norm_num)
theorem B1439545 : Blo 1277957 1439545 := bbase (se 2 (by rfl) ⟨539829, by rfl⟩ : syracuseStep 1439545 = 1079659) (by norm_num)
theorem B1619777 : Blo 1277957 1619777 := bbase (se 2 (by rfl) ⟨607416, by rfl⟩ : syracuseStep 1619777 = 1214833) (by norm_num)
theorem B5461829 : Blo 1277957 5461829 := bbase (se 4 (by rfl) ⟨512046, by rfl⟩ : syracuseStep 5461829 = 1024093) (by norm_num)
theorem B1365833 : Blo 1277957 1365833 := bbase (se 2 (by rfl) ⟨512187, by rfl⟩ : syracuseStep 1365833 = 1024375) (by norm_num)
theorem B1439581 : Blo 1277957 1439581 := bbase (se 3 (by rfl) ⟨269921, by rfl⟩ : syracuseStep 1439581 = 539843) (by norm_num)
theorem B1619833 : Blo 1277957 1619833 := bbase (se 2 (by rfl) ⟨607437, by rfl⟩ : syracuseStep 1619833 = 1214875) (by norm_num)
theorem B1439617 : Blo 1277957 1439617 := bbase (se 2 (by rfl) ⟨539856, by rfl⟩ : syracuseStep 1439617 = 1079713) (by norm_num)
theorem B1439653 : Blo 1277957 1439653 := bbase (se 4 (by rfl) ⟨134967, by rfl⟩ : syracuseStep 1439653 = 269935) (by norm_num)
theorem B4855733 : Blo 1277957 4855733 := bbase (se 5 (by rfl) ⟨227612, by rfl⟩ : syracuseStep 4855733 = 455225) (by norm_num)
theorem B1439689 : Blo 1277957 1439689 := bbase (se 2 (by rfl) ⟨539883, by rfl⟩ : syracuseStep 1439689 = 1079767) (by norm_num)
theorem B3282893 : Blo 1277957 3282893 := bbase (se 3 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 3282893 = 1231085) (by norm_num)
theorem B1619929 : Blo 1277957 1619929 := bbase (se 2 (by rfl) ⟨607473, by rfl⟩ : syracuseStep 1619929 = 1214947) (by norm_num)
theorem B1439725 : Blo 1277957 1439725 := bbase (se 3 (by rfl) ⟨269948, by rfl⟩ : syracuseStep 1439725 = 539897) (by norm_num)
theorem B1366021 : Blo 1277957 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B1439761 : Blo 1277957 1439761 := bbase (se 2 (by rfl) ⟨539910, by rfl⟩ : syracuseStep 1439761 = 1079821) (by norm_num)
theorem B8755253 : Blo 1277957 8755253 := bbase (se 5 (by rfl) ⟨410402, by rfl⟩ : syracuseStep 8755253 = 820805) (by norm_num)
theorem B1439797 : Blo 1277957 1439797 := bbase (se 5 (by rfl) ⟨67490, by rfl⟩ : syracuseStep 1439797 = 134981) (by norm_num)
theorem B6477893 : Blo 1277957 6477893 := bbase (se 4 (by rfl) ⟨607302, by rfl⟩ : syracuseStep 6477893 = 1214605) (by norm_num)
theorem B1439833 : Blo 1277957 1439833 := bbase (se 2 (by rfl) ⟨539937, by rfl⟩ : syracuseStep 1439833 = 1079875) (by norm_num)
theorem B1439869 : Blo 1277957 1439869 := bbase (se 3 (by rfl) ⟨269975, by rfl⟩ : syracuseStep 1439869 = 539951) (by norm_num)
theorem B1439905 : Blo 1277957 1439905 := bbase (se 2 (by rfl) ⟨539964, by rfl⟩ : syracuseStep 1439905 = 1079929) (by norm_num)
theorem B4315301 : Blo 1277957 4315301 := bbase (se 4 (by rfl) ⟨404559, by rfl⟩ : syracuseStep 4315301 = 809119) (by norm_num)
theorem B10934453 : Blo 1277957 10934453 := bbase (se 5 (by rfl) ⟨512552, by rfl⟩ : syracuseStep 10934453 = 1025105) (by norm_num)
theorem B1439941 : Blo 1277957 1439941 := bbase (se 4 (by rfl) ⟨134994, by rfl⟩ : syracuseStep 1439941 = 269989) (by norm_num)
theorem B4856021 : Blo 1277957 4856021 := bbase (se 7 (by rfl) ⟨56906, by rfl⟩ : syracuseStep 4856021 = 113813) (by norm_num)
theorem B3643861 : Blo 1277957 3643861 := bbase (se 7 (by rfl) ⟨42701, by rfl⟩ : syracuseStep 3643861 = 85403) (by norm_num)
theorem B6470117 : Blo 1277957 6470117 := bbase (se 4 (by rfl) ⟨606573, by rfl⟩ : syracuseStep 6470117 = 1213147) (by norm_num)
theorem B2914861 : Blo 1277957 2914861 := bbase (se 3 (by rfl) ⟨546536, by rfl⟩ : syracuseStep 2914861 = 1093073) (by norm_num)
theorem B4315733 : Blo 1277957 4315733 := bbase (se 8 (by rfl) ⟨25287, by rfl⟩ : syracuseStep 4315733 = 50575) (by norm_num)
theorem B3644021 : Blo 1277957 3644021 := bbase (se 5 (by rfl) ⟨170813, by rfl⟩ : syracuseStep 3644021 = 341627) (by norm_num)
theorem B13130581 : Blo 1277957 13130581 := bbase (se 9 (by rfl) ⟨38468, by rfl⟩ : syracuseStep 13130581 = 76937) (by norm_num)
theorem B3644261 : Blo 1277957 3644261 := bbase (se 4 (by rfl) ⟨341649, by rfl⟩ : syracuseStep 3644261 = 683299) (by norm_num)
theorem B3070925 : Blo 1277957 3070925 := bbase (se 3 (by rfl) ⟨575798, by rfl⟩ : syracuseStep 3070925 = 1151597) (by norm_num)
theorem B4316165 : Blo 1277957 4316165 := bbase (se 4 (by rfl) ⟨404640, by rfl⟩ : syracuseStep 4316165 = 809281) (by norm_num)
theorem B2366477 : Blo 1277957 2366477 := bbase (se 3 (by rfl) ⟨443714, by rfl⟩ : syracuseStep 2366477 = 887429) (by norm_num)
theorem B1727525 : Blo 1277957 1727525 := bbase (se 4 (by rfl) ⟨161955, by rfl⟩ : syracuseStep 1727525 = 323911) (by norm_num)
theorem B3644453 : Blo 1277957 3644453 := bbase (se 4 (by rfl) ⟨341667, by rfl⟩ : syracuseStep 3644453 = 683335) (by norm_num)
theorem B3234917 : Blo 1277957 3234917 := bbase (se 4 (by rfl) ⟨303273, by rfl⟩ : syracuseStep 3234917 = 606547) (by norm_num)
theorem B3071125 : Blo 1277957 3071125 := bbase (se 6 (by rfl) ⟨71979, by rfl⟩ : syracuseStep 3071125 = 143959) (by norm_num)
theorem B7281845 : Blo 1277957 7281845 := bbase (se 5 (by rfl) ⟨341336, by rfl⟩ : syracuseStep 7281845 = 682673) (by norm_num)
theorem B9215221 : Blo 1277957 9215221 := bbase (se 5 (by rfl) ⟨431963, by rfl⟩ : syracuseStep 9215221 = 863927) (by norm_num)
theorem B2047237 : Blo 1277957 2047237 := bbase (se 4 (by rfl) ⟨191928, by rfl⟩ : syracuseStep 2047237 = 383857) (by norm_num)
theorem B1727789 : Blo 1277957 1727789 := bbase (se 3 (by rfl) ⟨323960, by rfl⟩ : syracuseStep 1727789 = 647921) (by norm_num)
theorem B6479189 : Blo 1277957 6479189 := bbase (se 11 (by rfl) ⟨4745, by rfl⟩ : syracuseStep 6479189 = 9491) (by norm_num)
theorem B4857205 : Blo 1277957 4857205 := bbase (se 5 (by rfl) ⟨227681, by rfl⟩ : syracuseStep 4857205 = 455363) (by norm_num)
theorem B4095397 : Blo 1277957 4095397 := bbase (se 4 (by rfl) ⟨383943, by rfl⟩ : syracuseStep 4095397 = 767887) (by norm_num)
theorem B4316597 : Blo 1277957 4316597 := bbase (se 5 (by rfl) ⟨202340, by rfl⟩ : syracuseStep 4316597 = 404681) (by norm_num)
theorem B3235261 : Blo 1277957 3235261 := bbase (se 3 (by rfl) ⟨606611, by rfl⟩ : syracuseStep 3235261 = 1213223) (by norm_num)
theorem B1727941 : Blo 1277957 1727941 := bbase (se 4 (by rfl) ⟨161994, by rfl⟩ : syracuseStep 1727941 = 323989) (by norm_num)
theorem B21839381 : Blo 1277957 21839381 := bbase (se 6 (by rfl) ⟨511860, by rfl⟩ : syracuseStep 21839381 = 1023721) (by norm_num)
theorem B3939877 : Blo 1277957 3939877 := bbase (se 4 (by rfl) ⟨369363, by rfl⟩ : syracuseStep 3939877 = 738727) (by norm_num)
theorem B3235373 : Blo 1277957 3235373 := bbase (se 3 (by rfl) ⟨606632, by rfl⟩ : syracuseStep 3235373 = 1213265) (by norm_num)
theorem B5463605 : Blo 1277957 5463605 := bbase (se 5 (by rfl) ⟨256106, by rfl⟩ : syracuseStep 5463605 = 512213) (by norm_num)
theorem B4857509 : Blo 1277957 4857509 := bbase (se 4 (by rfl) ⟨455391, by rfl⟩ : syracuseStep 4857509 = 910783) (by norm_num)
theorem B2047693 : Blo 1277957 2047693 := bbase (se 3 (by rfl) ⟨383942, by rfl⟩ : syracuseStep 2047693 = 767885) (by norm_num)
theorem B3235565 : Blo 1277957 3235565 := bbase (se 3 (by rfl) ⟨606668, by rfl⟩ : syracuseStep 3235565 = 1213337) (by norm_num)
theorem B6471413 : Blo 1277957 6471413 := bbase (se 5 (by rfl) ⟨303347, by rfl⟩ : syracuseStep 6471413 = 606695) (by norm_num)
theorem B5463845 : Blo 1277957 5463845 := bbase (se 4 (by rfl) ⟨512235, by rfl⟩ : syracuseStep 5463845 = 1024471) (by norm_num)
theorem B3890981 : Blo 1277957 3890981 := bbase (se 4 (by rfl) ⟨364779, by rfl⟩ : syracuseStep 3890981 = 729559) (by norm_num)
theorem B4317029 : Blo 1277957 4317029 := bbase (se 4 (by rfl) ⟨404721, by rfl⟩ : syracuseStep 4317029 = 809443) (by norm_num)
theorem B1458041 : Blo 1277957 1458041 := bbase (se 2 (by rfl) ⟨546765, by rfl⟩ : syracuseStep 1458041 = 1093531) (by norm_num)
theorem B4734965 : Blo 1277957 4734965 := bbase (se 5 (by rfl) ⟨221951, by rfl⟩ : syracuseStep 4734965 = 443903) (by norm_num)
theorem B2875409 : Blo 1277957 2875409 := bstep (se 2 (by rfl) ⟨1078278, by rfl⟩ : syracuseStep 2875409 = 2156557) B2156557
theorem B1916945 : Blo 1277957 1916945 := bstep (se 2 (by rfl) ⟨718854, by rfl⟩ : syracuseStep 1916945 = 1437709) B1437709
theorem B1277971 : Blo 1277957 1277971 := bstep (se 1 (by rfl) ⟨958478, by rfl⟩ : syracuseStep 1277971 = 1916957) B1916957
theorem B2187281 : Blo 1277957 2187281 := bstep (se 2 (by rfl) ⟨820230, by rfl⟩ : syracuseStep 2187281 = 1640461) B1640461
theorem B2875427 : Blo 1277957 2875427 := bstep (se 1 (by rfl) ⟨2156570, by rfl⟩ : syracuseStep 2875427 = 4313141) B4313141
theorem B1916963 : Blo 1277957 1916963 := bstep (se 1 (by rfl) ⟨1437722, by rfl⟩ : syracuseStep 1916963 = 2875445) B2875445
theorem B1277987 : Blo 1277957 1277987 := bstep (se 1 (by rfl) ⟨958490, by rfl⟩ : syracuseStep 1277987 = 1916981) B1916981
theorem B3235889 : Blo 1277957 3235889 := bstep (se 2 (by rfl) ⟨1213458, by rfl⟩ : syracuseStep 3235889 = 2426917) B2426917
theorem B1278003 : Blo 1277957 1278003 := bstep (se 1 (by rfl) ⟨958502, by rfl⟩ : syracuseStep 1278003 = 1917005) B1917005
theorem B1916993 : Blo 1277957 1916993 := bstep (se 2 (by rfl) ⟨718872, by rfl⟩ : syracuseStep 1916993 = 1437745) B1437745
theorem B1278019 : Blo 1277957 1278019 := bstep (se 1 (by rfl) ⟨958514, by rfl⟩ : syracuseStep 1278019 = 1917029) B1917029
theorem B2187329 : Blo 1277957 2187329 := bstep (se 2 (by rfl) ⟨820248, by rfl⟩ : syracuseStep 2187329 = 1640497) B1640497
theorem B1917011 : Blo 1277957 1917011 := bstep (se 1 (by rfl) ⟨1437758, by rfl⟩ : syracuseStep 1917011 = 2875517) B2875517
theorem B1278035 : Blo 1277957 1278035 := bstep (se 1 (by rfl) ⟨958526, by rfl⟩ : syracuseStep 1278035 = 1917053) B1917053
theorem B1278051 : Blo 1277957 1278051 := bstep (se 1 (by rfl) ⟨958538, by rfl⟩ : syracuseStep 1278051 = 1917077) B1917077
theorem B1917041 : Blo 1277957 1917041 := bstep (se 2 (by rfl) ⟨718890, by rfl⟩ : syracuseStep 1917041 = 1437781) B1437781
theorem B1278067 : Blo 1277957 1278067 := bstep (se 1 (by rfl) ⟨958550, by rfl⟩ : syracuseStep 1278067 = 1917101) B1917101
theorem B1917059 : Blo 1277957 1917059 := bstep (se 1 (by rfl) ⟨1437794, by rfl⟩ : syracuseStep 1917059 = 2875589) B2875589
theorem B1278083 : Blo 1277957 1278083 := bstep (se 1 (by rfl) ⟨958562, by rfl⟩ : syracuseStep 1278083 = 1917125) B1917125
theorem B5464205 : Blo 1277957 5464205 := bstep (se 3 (by rfl) ⟨1024538, by rfl⟩ : syracuseStep 5464205 = 2049077) B2049077
theorem B1278099 : Blo 1277957 1278099 := bstep (se 1 (by rfl) ⟨958574, by rfl⟩ : syracuseStep 1278099 = 1917149) B1917149
theorem B1917089 : Blo 1277957 1917089 := bstep (se 2 (by rfl) ⟨718908, by rfl⟩ : syracuseStep 1917089 = 1437817) B1437817
theorem B1278115 : Blo 1277957 1278115 := bstep (se 1 (by rfl) ⟨958586, by rfl⟩ : syracuseStep 1278115 = 1917173) B1917173
theorem B3072163 : Blo 1277957 3072163 := bstep (se 1 (by rfl) ⟨2304122, by rfl⟩ : syracuseStep 3072163 = 4608245) B4608245
theorem B2769059 : Blo 1277957 2769059 := bstep (se 1 (by rfl) ⟨2076794, by rfl⟩ : syracuseStep 2769059 = 4153589) B4153589
theorem B1917107 : Blo 1277957 1917107 := bstep (se 1 (by rfl) ⟨1437830, by rfl⟩ : syracuseStep 1917107 = 2875661) B2875661
theorem B1278131 : Blo 1277957 1278131 := bstep (se 1 (by rfl) ⟨958598, by rfl⟩ : syracuseStep 1278131 = 1917197) B1917197
theorem B1278147 : Blo 1277957 1278147 := bstep (se 1 (by rfl) ⟨958610, by rfl⟩ : syracuseStep 1278147 = 1917221) B1917221
theorem B1917137 : Blo 1277957 1917137 := bstep (se 2 (by rfl) ⟨718926, by rfl⟩ : syracuseStep 1917137 = 1437853) B1437853
theorem B1278163 : Blo 1277957 1278163 := bstep (se 1 (by rfl) ⟨958622, by rfl⟩ : syracuseStep 1278163 = 1917245) B1917245
theorem B1917155 : Blo 1277957 1917155 := bstep (se 1 (by rfl) ⟨1437866, by rfl⟩ : syracuseStep 1917155 = 2875733) B2875733
theorem B1278179 : Blo 1277957 1278179 := bstep (se 1 (by rfl) ⟨958634, by rfl⟩ : syracuseStep 1278179 = 1917269) B1917269
theorem B1278195 : Blo 1277957 1278195 := bstep (se 1 (by rfl) ⟨958646, by rfl⟩ : syracuseStep 1278195 = 1917293) B1917293
theorem B1917185 : Blo 1277957 1917185 := bstep (se 2 (by rfl) ⟨718944, by rfl⟩ : syracuseStep 1917185 = 1437889) B1437889
theorem B2048257 : Blo 1277957 2048257 := bstep (se 2 (by rfl) ⟨768096, by rfl⟩ : syracuseStep 2048257 = 1536193) B1536193
theorem B1278211 : Blo 1277957 1278211 := bstep (se 1 (by rfl) ⟨958658, by rfl⟩ : syracuseStep 1278211 = 1917317) B1917317
theorem B1917203 : Blo 1277957 1917203 := bstep (se 1 (by rfl) ⟨1437902, by rfl⟩ : syracuseStep 1917203 = 2875805) B2875805
theorem B1278227 : Blo 1277957 1278227 := bstep (se 1 (by rfl) ⟨958670, by rfl⟩ : syracuseStep 1278227 = 1917341) B1917341
theorem B1278243 : Blo 1277957 1278243 := bstep (se 1 (by rfl) ⟨958682, by rfl⟩ : syracuseStep 1278243 = 1917365) B1917365
theorem B2875697 : Blo 1277957 2875697 := bstep (se 2 (by rfl) ⟨1078386, by rfl⟩ : syracuseStep 2875697 = 2156773) B2156773
theorem B1917233 : Blo 1277957 1917233 := bstep (se 2 (by rfl) ⟨718962, by rfl⟩ : syracuseStep 1917233 = 1437925) B1437925
theorem B1278259 : Blo 1277957 1278259 := bstep (se 1 (by rfl) ⟨958694, by rfl⟩ : syracuseStep 1278259 = 1917389) B1917389
theorem B2875715 : Blo 1277957 2875715 := bstep (se 1 (by rfl) ⟨2156786, by rfl⟩ : syracuseStep 2875715 = 4313573) B4313573
theorem B1917251 : Blo 1277957 1917251 := bstep (se 1 (by rfl) ⟨1437938, by rfl⟩ : syracuseStep 1917251 = 2875877) B2875877
theorem B1278275 : Blo 1277957 1278275 := bstep (se 1 (by rfl) ⟨958706, by rfl⟩ : syracuseStep 1278275 = 1917413) B1917413
theorem B1278291 : Blo 1277957 1278291 := bstep (se 1 (by rfl) ⟨958718, by rfl⟩ : syracuseStep 1278291 = 1917437) B1917437
theorem B1917281 : Blo 1277957 1917281 := bstep (se 2 (by rfl) ⟨718980, by rfl⟩ : syracuseStep 1917281 = 1437961) B1437961
theorem B1278307 : Blo 1277957 1278307 := bstep (se 1 (by rfl) ⟨958730, by rfl⟩ : syracuseStep 1278307 = 1917461) B1917461
theorem B9224561 : Blo 1277957 9224561 := bstep (se 2 (by rfl) ⟨3459210, by rfl⟩ : syracuseStep 9224561 = 6918421) B6918421
theorem B1917299 : Blo 1277957 1917299 := bstep (se 1 (by rfl) ⟨1437974, by rfl⟩ : syracuseStep 1917299 = 2875949) B2875949
theorem B1278323 : Blo 1277957 1278323 := bstep (se 1 (by rfl) ⟨958742, by rfl⟩ : syracuseStep 1278323 = 1917485) B1917485
theorem B1278339 : Blo 1277957 1278339 := bstep (se 1 (by rfl) ⟨958754, by rfl⟩ : syracuseStep 1278339 = 1917509) B1917509
theorem B1917329 : Blo 1277957 1917329 := bstep (se 2 (by rfl) ⟨718998, by rfl⟩ : syracuseStep 1917329 = 1437997) B1437997
theorem B2187665 : Blo 1277957 2187665 := bstep (se 2 (by rfl) ⟨820374, by rfl⟩ : syracuseStep 2187665 = 1640749) B1640749
theorem B1278355 : Blo 1277957 1278355 := bstep (se 1 (by rfl) ⟨958766, by rfl⟩ : syracuseStep 1278355 = 1917533) B1917533
theorem B1917347 : Blo 1277957 1917347 := bstep (se 1 (by rfl) ⟨1438010, by rfl⟩ : syracuseStep 1917347 = 2876021) B2876021
theorem B1278371 : Blo 1277957 1278371 := bstep (se 1 (by rfl) ⟨958778, by rfl⟩ : syracuseStep 1278371 = 1917557) B1917557
theorem B1278387 : Blo 1277957 1278387 := bstep (se 1 (by rfl) ⟨958790, by rfl⟩ : syracuseStep 1278387 = 1917581) B1917581
theorem B1917377 : Blo 1277957 1917377 := bstep (se 2 (by rfl) ⟨719016, by rfl⟩ : syracuseStep 1917377 = 1438033) B1438033
theorem B1278403 : Blo 1277957 1278403 := bstep (se 1 (by rfl) ⟨958802, by rfl⟩ : syracuseStep 1278403 = 1917605) B1917605
theorem B1917395 : Blo 1277957 1917395 := bstep (se 1 (by rfl) ⟨1438046, by rfl⟩ : syracuseStep 1917395 = 2876093) B2876093
theorem B1278419 : Blo 1277957 1278419 := bstep (se 1 (by rfl) ⟨958814, by rfl⟩ : syracuseStep 1278419 = 1917629) B1917629
theorem B1278435 : Blo 1277957 1278435 := bstep (se 1 (by rfl) ⟨958826, by rfl⟩ : syracuseStep 1278435 = 1917653) B1917653
theorem B15565283 : Blo 1277957 15565283 := bstep (se 1 (by rfl) ⟨11673962, by rfl⟩ : syracuseStep 15565283 = 23347925) B23347925
theorem B4317677 : Blo 1277957 4317677 := bstep (se 3 (by rfl) ⟨809564, by rfl⟩ : syracuseStep 4317677 = 1619129) B1619129
theorem B1917425 : Blo 1277957 1917425 := bstep (se 2 (by rfl) ⟨719034, by rfl⟩ : syracuseStep 1917425 = 1438069) B1438069
theorem B1278451 : Blo 1277957 1278451 := bstep (se 1 (by rfl) ⟨958838, by rfl⟩ : syracuseStep 1278451 = 1917677) B1917677
theorem B1917443 : Blo 1277957 1917443 := bstep (se 1 (by rfl) ⟨1438082, by rfl⟩ : syracuseStep 1917443 = 2876165) B2876165
theorem B1278467 : Blo 1277957 1278467 := bstep (se 1 (by rfl) ⟨958850, by rfl⟩ : syracuseStep 1278467 = 1917701) B1917701
theorem B1278483 : Blo 1277957 1278483 := bstep (se 1 (by rfl) ⟨958862, by rfl⟩ : syracuseStep 1278483 = 1917725) B1917725
theorem B1917473 : Blo 1277957 1917473 := bstep (se 2 (by rfl) ⟨719052, by rfl⟩ : syracuseStep 1917473 = 1438105) B1438105
theorem B1278499 : Blo 1277957 1278499 := bstep (se 1 (by rfl) ⟨958874, by rfl⟩ : syracuseStep 1278499 = 1917749) B1917749
theorem B4317731 : Blo 1277957 4317731 := bstep (se 1 (by rfl) ⟨3238298, by rfl⟩ : syracuseStep 4317731 = 6476597) B6476597
theorem B1917491 : Blo 1277957 1917491 := bstep (se 1 (by rfl) ⟨1438118, by rfl⟩ : syracuseStep 1917491 = 2876237) B2876237
theorem B1278515 : Blo 1277957 1278515 := bstep (se 1 (by rfl) ⟨958886, by rfl⟩ : syracuseStep 1278515 = 1917773) B1917773
theorem B1278531 : Blo 1277957 1278531 := bstep (se 1 (by rfl) ⟨958898, by rfl⟩ : syracuseStep 1278531 = 1917797) B1917797
theorem B2875985 : Blo 1277957 2875985 := bstep (se 2 (by rfl) ⟨1078494, by rfl⟩ : syracuseStep 2875985 = 2156989) B2156989
theorem B1917521 : Blo 1277957 1917521 := bstep (se 2 (by rfl) ⟨719070, by rfl⟩ : syracuseStep 1917521 = 1438141) B1438141
theorem B1278547 : Blo 1277957 1278547 := bstep (se 1 (by rfl) ⟨958910, by rfl⟩ : syracuseStep 1278547 = 1917821) B1917821
theorem B2876003 : Blo 1277957 2876003 := bstep (se 1 (by rfl) ⟨2157002, by rfl⟩ : syracuseStep 2876003 = 4314005) B4314005
theorem B1917539 : Blo 1277957 1917539 := bstep (se 1 (by rfl) ⟨1438154, by rfl⟩ : syracuseStep 1917539 = 2876309) B2876309
theorem B1278563 : Blo 1277957 1278563 := bstep (se 1 (by rfl) ⟨958922, by rfl⟩ : syracuseStep 1278563 = 1917845) B1917845
theorem B4858481 : Blo 1277957 4858481 := bstep (se 2 (by rfl) ⟨1821930, by rfl⟩ : syracuseStep 4858481 = 3643861) B3643861
theorem B1278579 : Blo 1277957 1278579 := bstep (se 1 (by rfl) ⟨958934, by rfl⟩ : syracuseStep 1278579 = 1917869) B1917869
theorem B1917569 : Blo 1277957 1917569 := bstep (se 2 (by rfl) ⟨719088, by rfl⟩ : syracuseStep 1917569 = 1438177) B1438177
theorem B1278595 : Blo 1277957 1278595 := bstep (se 1 (by rfl) ⟨958946, by rfl⟩ : syracuseStep 1278595 = 1917893) B1917893
theorem B1917587 : Blo 1277957 1917587 := bstep (se 1 (by rfl) ⟨1438190, by rfl⟩ : syracuseStep 1917587 = 2876381) B2876381
theorem B1278611 : Blo 1277957 1278611 := bstep (se 1 (by rfl) ⟨958958, by rfl⟩ : syracuseStep 1278611 = 1917917) B1917917
theorem B1278627 : Blo 1277957 1278627 := bstep (se 1 (by rfl) ⟨958970, by rfl⟩ : syracuseStep 1278627 = 1917941) B1917941
theorem B1917617 : Blo 1277957 1917617 := bstep (se 2 (by rfl) ⟨719106, by rfl⟩ : syracuseStep 1917617 = 1438213) B1438213
theorem B1278643 : Blo 1277957 1278643 := bstep (se 1 (by rfl) ⟨958982, by rfl⟩ : syracuseStep 1278643 = 1917965) B1917965
theorem B1917635 : Blo 1277957 1917635 := bstep (se 1 (by rfl) ⟨1438226, by rfl⟩ : syracuseStep 1917635 = 2876453) B2876453
theorem B1278659 : Blo 1277957 1278659 := bstep (se 1 (by rfl) ⟨958994, by rfl⟩ : syracuseStep 1278659 = 1917989) B1917989
theorem B1278675 : Blo 1277957 1278675 := bstep (se 1 (by rfl) ⟨959006, by rfl⟩ : syracuseStep 1278675 = 1918013) B1918013
theorem B1917665 : Blo 1277957 1917665 := bstep (se 2 (by rfl) ⟨719124, by rfl⟩ : syracuseStep 1917665 = 1438249) B1438249
theorem B1278691 : Blo 1277957 1278691 := bstep (se 1 (by rfl) ⟨959018, by rfl⟩ : syracuseStep 1278691 = 1918037) B1918037
theorem B1917683 : Blo 1277957 1917683 := bstep (se 1 (by rfl) ⟨1438262, by rfl⟩ : syracuseStep 1917683 = 2876525) B2876525
theorem B1278707 : Blo 1277957 1278707 := bstep (se 1 (by rfl) ⟨959030, by rfl⟩ : syracuseStep 1278707 = 1918061) B1918061
theorem B1278723 : Blo 1277957 1278723 := bstep (se 1 (by rfl) ⟨959042, by rfl⟩ : syracuseStep 1278723 = 1918085) B1918085
theorem B1917713 : Blo 1277957 1917713 := bstep (se 2 (by rfl) ⟨719142, by rfl⟩ : syracuseStep 1917713 = 1438285) B1438285
theorem B1278739 : Blo 1277957 1278739 := bstep (se 1 (by rfl) ⟨959054, by rfl⟩ : syracuseStep 1278739 = 1918109) B1918109
theorem B1917731 : Blo 1277957 1917731 := bstep (se 1 (by rfl) ⟨1438298, by rfl⟩ : syracuseStep 1917731 = 2876597) B2876597
theorem B1278755 : Blo 1277957 1278755 := bstep (se 1 (by rfl) ⟨959066, by rfl⟩ : syracuseStep 1278755 = 1918133) B1918133
theorem B5186339 : Blo 1277957 5186339 := bstep (se 1 (by rfl) ⟨3889754, by rfl⟩ : syracuseStep 5186339 = 7779509) B7779509
theorem B4318001 : Blo 1277957 4318001 := bstep (se 2 (by rfl) ⟨1619250, by rfl⟩ : syracuseStep 4318001 = 3238501) B3238501
theorem B1278771 : Blo 1277957 1278771 := bstep (se 1 (by rfl) ⟨959078, by rfl⟩ : syracuseStep 1278771 = 1918157) B1918157
theorem B1917761 : Blo 1277957 1917761 := bstep (se 2 (by rfl) ⟨719160, by rfl⟩ : syracuseStep 1917761 = 1438321) B1438321
theorem B1278787 : Blo 1277957 1278787 := bstep (se 1 (by rfl) ⟨959090, by rfl⟩ : syracuseStep 1278787 = 1918181) B1918181
theorem B1917779 : Blo 1277957 1917779 := bstep (se 1 (by rfl) ⟨1438334, by rfl⟩ : syracuseStep 1917779 = 2876669) B2876669
theorem B1278803 : Blo 1277957 1278803 := bstep (se 1 (by rfl) ⟨959102, by rfl⟩ : syracuseStep 1278803 = 1918205) B1918205
theorem B6472547 : Blo 1277957 6472547 := bstep (se 1 (by rfl) ⟨4854410, by rfl⟩ : syracuseStep 6472547 = 9708821) B9708821
theorem B1278819 : Blo 1277957 1278819 := bstep (se 1 (by rfl) ⟨959114, by rfl⟩ : syracuseStep 1278819 = 1918229) B1918229
theorem B2876273 : Blo 1277957 2876273 := bstep (se 2 (by rfl) ⟨1078602, by rfl⟩ : syracuseStep 2876273 = 2157205) B2157205
theorem B1917809 : Blo 1277957 1917809 := bstep (se 2 (by rfl) ⟨719178, by rfl⟩ : syracuseStep 1917809 = 1438357) B1438357
theorem B1278835 : Blo 1277957 1278835 := bstep (se 1 (by rfl) ⟨959126, by rfl⟩ : syracuseStep 1278835 = 1918253) B1918253
theorem B2876291 : Blo 1277957 2876291 := bstep (se 1 (by rfl) ⟨2157218, by rfl⟩ : syracuseStep 2876291 = 4314437) B4314437
theorem B1917827 : Blo 1277957 1917827 := bstep (se 1 (by rfl) ⟨1438370, by rfl⟩ : syracuseStep 1917827 = 2876741) B2876741
theorem B1278851 : Blo 1277957 1278851 := bstep (se 1 (by rfl) ⟨959138, by rfl⟩ : syracuseStep 1278851 = 1918277) B1918277
theorem B1278867 : Blo 1277957 1278867 := bstep (se 1 (by rfl) ⟨959150, by rfl⟩ : syracuseStep 1278867 = 1918301) B1918301
theorem B1917857 : Blo 1277957 1917857 := bstep (se 2 (by rfl) ⟨719196, by rfl⟩ : syracuseStep 1917857 = 1438393) B1438393
theorem B1278883 : Blo 1277957 1278883 := bstep (se 1 (by rfl) ⟨959162, by rfl⟩ : syracuseStep 1278883 = 1918325) B1918325
theorem B1917875 : Blo 1277957 1917875 := bstep (se 1 (by rfl) ⟨1438406, by rfl⟩ : syracuseStep 1917875 = 2876813) B2876813
theorem B1278899 : Blo 1277957 1278899 := bstep (se 1 (by rfl) ⟨959174, by rfl⟩ : syracuseStep 1278899 = 1918349) B1918349
theorem B1278915 : Blo 1277957 1278915 := bstep (se 1 (by rfl) ⟨959186, by rfl⟩ : syracuseStep 1278915 = 1918373) B1918373
theorem B1917905 : Blo 1277957 1917905 := bstep (se 2 (by rfl) ⟨719214, by rfl⟩ : syracuseStep 1917905 = 1438429) B1438429
theorem B1278931 : Blo 1277957 1278931 := bstep (se 1 (by rfl) ⟨959198, by rfl⟩ : syracuseStep 1278931 = 1918397) B1918397
theorem B1917923 : Blo 1277957 1917923 := bstep (se 1 (by rfl) ⟨1438442, by rfl⟩ : syracuseStep 1917923 = 2876885) B2876885
theorem B1278947 : Blo 1277957 1278947 := bstep (se 1 (by rfl) ⟨959210, by rfl⟩ : syracuseStep 1278947 = 1918421) B1918421
theorem B1278963 : Blo 1277957 1278963 := bstep (se 1 (by rfl) ⟨959222, by rfl⟩ : syracuseStep 1278963 = 1918445) B1918445
theorem B1917953 : Blo 1277957 1917953 := bstep (se 2 (by rfl) ⟨719232, by rfl⟩ : syracuseStep 1917953 = 1438465) B1438465
theorem B1278979 : Blo 1277957 1278979 := bstep (se 1 (by rfl) ⟨959234, by rfl⟩ : syracuseStep 1278979 = 1918469) B1918469
theorem B3236881 : Blo 1277957 3236881 := bstep (se 2 (by rfl) ⟨1213830, by rfl⟩ : syracuseStep 3236881 = 2427661) B2427661
theorem B1917971 : Blo 1277957 1917971 := bstep (se 1 (by rfl) ⟨1438478, by rfl⟩ : syracuseStep 1917971 = 2876957) B2876957
theorem B1278995 : Blo 1277957 1278995 := bstep (se 1 (by rfl) ⟨959246, by rfl⟩ : syracuseStep 1278995 = 1918493) B1918493
theorem B1279011 : Blo 1277957 1279011 := bstep (se 1 (by rfl) ⟨959258, by rfl⟩ : syracuseStep 1279011 = 1918517) B1918517
theorem B1918001 : Blo 1277957 1918001 := bstep (se 2 (by rfl) ⟨719250, by rfl⟩ : syracuseStep 1918001 = 1438501) B1438501
theorem B1279027 : Blo 1277957 1279027 := bstep (se 1 (by rfl) ⟨959270, by rfl⟩ : syracuseStep 1279027 = 1918541) B1918541
theorem B1918019 : Blo 1277957 1918019 := bstep (se 1 (by rfl) ⟨1438514, by rfl⟩ : syracuseStep 1918019 = 2877029) B2877029
theorem B1279043 : Blo 1277957 1279043 := bstep (se 1 (by rfl) ⟨959282, by rfl⟩ : syracuseStep 1279043 = 1918565) B1918565
theorem B5538893 : Blo 1277957 5538893 := bstep (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) B2077085
theorem B1279059 : Blo 1277957 1279059 := bstep (se 1 (by rfl) ⟨959294, by rfl⟩ : syracuseStep 1279059 = 1918589) B1918589
theorem B1918049 : Blo 1277957 1918049 := bstep (se 2 (by rfl) ⟨719268, by rfl⟩ : syracuseStep 1918049 = 1438537) B1438537
theorem B1279075 : Blo 1277957 1279075 := bstep (se 1 (by rfl) ⟨959306, by rfl⟩ : syracuseStep 1279075 = 1918613) B1918613
theorem B17507441 : Blo 1277957 17507441 := bstep (se 2 (by rfl) ⟨6565290, by rfl⟩ : syracuseStep 17507441 = 13130581) B13130581
theorem B1918067 : Blo 1277957 1918067 := bstep (se 1 (by rfl) ⟨1438550, by rfl⟩ : syracuseStep 1918067 = 2877101) B2877101
theorem B1279091 : Blo 1277957 1279091 := bstep (se 1 (by rfl) ⟨959318, by rfl⟩ : syracuseStep 1279091 = 1918637) B1918637
theorem B1279107 : Blo 1277957 1279107 := bstep (se 1 (by rfl) ⟨959330, by rfl⟩ : syracuseStep 1279107 = 1918661) B1918661
theorem B2876561 : Blo 1277957 2876561 := bstep (se 2 (by rfl) ⟨1078710, by rfl⟩ : syracuseStep 2876561 = 2157421) B2157421
theorem B1918097 : Blo 1277957 1918097 := bstep (se 2 (by rfl) ⟨719286, by rfl⟩ : syracuseStep 1918097 = 1438573) B1438573
theorem B1279123 : Blo 1277957 1279123 := bstep (se 1 (by rfl) ⟨959342, by rfl⟩ : syracuseStep 1279123 = 1918685) B1918685
theorem B2049185 : Blo 1277957 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B2876579 : Blo 1277957 2876579 := bstep (se 1 (by rfl) ⟨2157434, by rfl⟩ : syracuseStep 2876579 = 4314869) B4314869
theorem B1918115 : Blo 1277957 1918115 := bstep (se 1 (by rfl) ⟨1438586, by rfl⟩ : syracuseStep 1918115 = 2877173) B2877173
theorem B1279139 : Blo 1277957 1279139 := bstep (se 1 (by rfl) ⟨959354, by rfl⟩ : syracuseStep 1279139 = 1918709) B1918709
theorem B1279155 : Blo 1277957 1279155 := bstep (se 1 (by rfl) ⟨959366, by rfl⟩ : syracuseStep 1279155 = 1918733) B1918733
theorem B1918145 : Blo 1277957 1918145 := bstep (se 2 (by rfl) ⟨719304, by rfl⟩ : syracuseStep 1918145 = 1438609) B1438609
theorem B1279171 : Blo 1277957 1279171 := bstep (se 1 (by rfl) ⟨959378, by rfl⟩ : syracuseStep 1279171 = 1918757) B1918757
theorem B1918163 : Blo 1277957 1918163 := bstep (se 1 (by rfl) ⟨1438622, by rfl⟩ : syracuseStep 1918163 = 2877245) B2877245
theorem B1279187 : Blo 1277957 1279187 := bstep (se 1 (by rfl) ⟨959390, by rfl⟩ : syracuseStep 1279187 = 1918781) B1918781
theorem B1279203 : Blo 1277957 1279203 := bstep (se 1 (by rfl) ⟨959402, by rfl⟩ : syracuseStep 1279203 = 1918805) B1918805
theorem B1918193 : Blo 1277957 1918193 := bstep (se 2 (by rfl) ⟨719322, by rfl⟩ : syracuseStep 1918193 = 1438645) B1438645
theorem B1279219 : Blo 1277957 1279219 := bstep (se 1 (by rfl) ⟨959414, by rfl⟩ : syracuseStep 1279219 = 1918829) B1918829
theorem B1918211 : Blo 1277957 1918211 := bstep (se 1 (by rfl) ⟨1438658, by rfl⟩ : syracuseStep 1918211 = 2877317) B2877317
theorem B1279235 : Blo 1277957 1279235 := bstep (se 1 (by rfl) ⟨959426, by rfl⟩ : syracuseStep 1279235 = 1918853) B1918853
theorem B4859149 : Blo 1277957 4859149 := bstep (se 3 (by rfl) ⟨911090, by rfl⟩ : syracuseStep 4859149 = 1822181) B1822181
theorem B9225485 : Blo 1277957 9225485 := bstep (se 3 (by rfl) ⟨1729778, by rfl⟩ : syracuseStep 9225485 = 3459557) B3459557
theorem B1279251 : Blo 1277957 1279251 := bstep (se 1 (by rfl) ⟨959438, by rfl⟩ : syracuseStep 1279251 = 1918877) B1918877
theorem B1918241 : Blo 1277957 1918241 := bstep (se 2 (by rfl) ⟨719340, by rfl⟩ : syracuseStep 1918241 = 1438681) B1438681
theorem B3237155 : Blo 1277957 3237155 := bstep (se 1 (by rfl) ⟨2427866, by rfl⟩ : syracuseStep 3237155 = 4855733) B4855733
theorem B1279267 : Blo 1277957 1279267 := bstep (se 1 (by rfl) ⟨959450, by rfl⟩ : syracuseStep 1279267 = 1918901) B1918901
theorem B1918259 : Blo 1277957 1918259 := bstep (se 1 (by rfl) ⟨1438694, by rfl⟩ : syracuseStep 1918259 = 2877389) B2877389
theorem B1279283 : Blo 1277957 1279283 := bstep (se 1 (by rfl) ⟨959462, by rfl⟩ : syracuseStep 1279283 = 1918925) B1918925
theorem B2188595 : Blo 1277957 2188595 := bstep (se 1 (by rfl) ⟨1641446, by rfl⟩ : syracuseStep 2188595 = 3282893) B3282893
theorem B1279299 : Blo 1277957 1279299 := bstep (se 1 (by rfl) ⟨959474, by rfl⟩ : syracuseStep 1279299 = 1918949) B1918949
theorem B17753413 : Blo 1277957 17753413 := bstep (se 4 (by rfl) ⟨1664382, by rfl⟩ : syracuseStep 17753413 = 3328765) B3328765
theorem B4318541 : Blo 1277957 4318541 := bstep (se 3 (by rfl) ⟨809726, by rfl⟩ : syracuseStep 4318541 = 1619453) B1619453
theorem B1918289 : Blo 1277957 1918289 := bstep (se 2 (by rfl) ⟨719358, by rfl⟩ : syracuseStep 1918289 = 1438717) B1438717
theorem B1279315 : Blo 1277957 1279315 := bstep (se 1 (by rfl) ⟨959486, by rfl⟩ : syracuseStep 1279315 = 1918973) B1918973
theorem B1918307 : Blo 1277957 1918307 := bstep (se 1 (by rfl) ⟨1438730, by rfl⟩ : syracuseStep 1918307 = 2877461) B2877461
theorem B8750435 : Blo 1277957 8750435 := bstep (se 1 (by rfl) ⟨6562826, by rfl⟩ : syracuseStep 8750435 = 13125653) B13125653
theorem B1279331 : Blo 1277957 1279331 := bstep (se 1 (by rfl) ⟨959498, by rfl⟩ : syracuseStep 1279331 = 1918997) B1918997
theorem B1820017 : Blo 1277957 1820017 := bstep (se 2 (by rfl) ⟨682506, by rfl⟩ : syracuseStep 1820017 = 1365013) B1365013
theorem B3073393 : Blo 1277957 3073393 := bstep (se 2 (by rfl) ⟨1152522, by rfl⟩ : syracuseStep 3073393 = 2305045) B2305045
theorem B1279347 : Blo 1277957 1279347 := bstep (se 1 (by rfl) ⟨959510, by rfl⟩ : syracuseStep 1279347 = 1919021) B1919021
theorem B1918337 : Blo 1277957 1918337 := bstep (se 2 (by rfl) ⟨719376, by rfl⟩ : syracuseStep 1918337 = 1438753) B1438753
theorem B1279363 : Blo 1277957 1279363 := bstep (se 1 (by rfl) ⟨959522, by rfl⟩ : syracuseStep 1279363 = 1919045) B1919045
theorem B4318595 : Blo 1277957 4318595 := bstep (se 1 (by rfl) ⟨3238946, by rfl⟩ : syracuseStep 4318595 = 6477893) B6477893
theorem B12289421 : Blo 1277957 12289421 := bstep (se 3 (by rfl) ⟨2304266, by rfl⟩ : syracuseStep 12289421 = 4608533) B4608533
theorem B1918355 : Blo 1277957 1918355 := bstep (se 1 (by rfl) ⟨1438766, by rfl⟩ : syracuseStep 1918355 = 2877533) B2877533
theorem B1279379 : Blo 1277957 1279379 := bstep (se 1 (by rfl) ⟨959534, by rfl⟩ : syracuseStep 1279379 = 1919069) B1919069
theorem B1279395 : Blo 1277957 1279395 := bstep (se 1 (by rfl) ⟨959546, by rfl⟩ : syracuseStep 1279395 = 1919093) B1919093
theorem B3458477 : Blo 1277957 3458477 := bstep (se 3 (by rfl) ⟨648464, by rfl⟩ : syracuseStep 3458477 = 1296929) B1296929
theorem B2876849 : Blo 1277957 2876849 := bstep (se 2 (by rfl) ⟨1078818, by rfl⟩ : syracuseStep 2876849 = 2157637) B2157637
theorem B1918385 : Blo 1277957 1918385 := bstep (se 2 (by rfl) ⟨719394, by rfl⟩ : syracuseStep 1918385 = 1438789) B1438789
theorem B1279411 : Blo 1277957 1279411 := bstep (se 1 (by rfl) ⟨959558, by rfl⟩ : syracuseStep 1279411 = 1919117) B1919117
theorem B2876867 : Blo 1277957 2876867 := bstep (se 1 (by rfl) ⟨2157650, by rfl⟩ : syracuseStep 2876867 = 4315301) B4315301
theorem B1918403 : Blo 1277957 1918403 := bstep (se 1 (by rfl) ⟨1438802, by rfl⟩ : syracuseStep 1918403 = 2877605) B2877605
theorem B1279427 : Blo 1277957 1279427 := bstep (se 1 (by rfl) ⟨959570, by rfl⟩ : syracuseStep 1279427 = 1919141) B1919141
theorem B1279443 : Blo 1277957 1279443 := bstep (se 1 (by rfl) ⟨959582, by rfl⟩ : syracuseStep 1279443 = 1919165) B1919165
theorem B1918433 : Blo 1277957 1918433 := bstep (se 2 (by rfl) ⟨719412, by rfl⟩ : syracuseStep 1918433 = 1438825) B1438825
theorem B3237347 : Blo 1277957 3237347 := bstep (se 1 (by rfl) ⟨2428010, by rfl⟩ : syracuseStep 3237347 = 4856021) B4856021
theorem B1279459 : Blo 1277957 1279459 := bstep (se 1 (by rfl) ⟨959594, by rfl⟩ : syracuseStep 1279459 = 1919189) B1919189
theorem B1918451 : Blo 1277957 1918451 := bstep (se 1 (by rfl) ⟨1438838, by rfl⟩ : syracuseStep 1918451 = 2877677) B2877677
theorem B1279475 : Blo 1277957 1279475 := bstep (se 1 (by rfl) ⟨959606, by rfl⟩ : syracuseStep 1279475 = 1919213) B1919213
theorem B1639939 : Blo 1277957 1639939 := bstep (se 1 (by rfl) ⟨1229954, by rfl⟩ : syracuseStep 1639939 = 2459909) B2459909
theorem B1295875 : Blo 1277957 1295875 := bstep (se 1 (by rfl) ⟨971906, by rfl⟩ : syracuseStep 1295875 = 1943813) B1943813
theorem B1279491 : Blo 1277957 1279491 := bstep (se 1 (by rfl) ⟨959618, by rfl⟩ : syracuseStep 1279491 = 1919237) B1919237
theorem B1918481 : Blo 1277957 1918481 := bstep (se 2 (by rfl) ⟨719430, by rfl⟩ : syracuseStep 1918481 = 1438861) B1438861
theorem B1279507 : Blo 1277957 1279507 := bstep (se 1 (by rfl) ⟨959630, by rfl⟩ : syracuseStep 1279507 = 1919261) B1919261
theorem B1918499 : Blo 1277957 1918499 := bstep (se 1 (by rfl) ⟨1438874, by rfl⟩ : syracuseStep 1918499 = 2877749) B2877749
theorem B1279523 : Blo 1277957 1279523 := bstep (se 1 (by rfl) ⟨959642, by rfl⟩ : syracuseStep 1279523 = 1919285) B1919285
theorem B1279539 : Blo 1277957 1279539 := bstep (se 1 (by rfl) ⟨959654, by rfl⟩ : syracuseStep 1279539 = 1919309) B1919309
theorem B1918529 : Blo 1277957 1918529 := bstep (se 2 (by rfl) ⟨719448, by rfl⟩ : syracuseStep 1918529 = 1438897) B1438897
theorem B1279555 : Blo 1277957 1279555 := bstep (se 1 (by rfl) ⟨959666, by rfl⟩ : syracuseStep 1279555 = 1919333) B1919333
theorem B1918547 : Blo 1277957 1918547 := bstep (se 1 (by rfl) ⟨1438910, by rfl⟩ : syracuseStep 1918547 = 2877821) B2877821
theorem B1279571 : Blo 1277957 1279571 := bstep (se 1 (by rfl) ⟨959678, by rfl⟩ : syracuseStep 1279571 = 1919357) B1919357
theorem B5834339 : Blo 1277957 5834339 := bstep (se 1 (by rfl) ⟨4375754, by rfl⟩ : syracuseStep 5834339 = 8751509) B8751509
theorem B1279587 : Blo 1277957 1279587 := bstep (se 1 (by rfl) ⟨959690, by rfl⟩ : syracuseStep 1279587 = 1919381) B1919381
theorem B1918577 : Blo 1277957 1918577 := bstep (se 2 (by rfl) ⟨719466, by rfl⟩ : syracuseStep 1918577 = 1438933) B1438933
theorem B1279603 : Blo 1277957 1279603 := bstep (se 1 (by rfl) ⟨959702, by rfl⟩ : syracuseStep 1279603 = 1919405) B1919405
theorem B1918595 : Blo 1277957 1918595 := bstep (se 1 (by rfl) ⟨1438946, by rfl⟩ : syracuseStep 1918595 = 2877893) B2877893
theorem B1279619 : Blo 1277957 1279619 := bstep (se 1 (by rfl) ⟨959714, by rfl⟩ : syracuseStep 1279619 = 1919429) B1919429
theorem B6473357 : Blo 1277957 6473357 := bstep (se 3 (by rfl) ⟨1213754, by rfl⟩ : syracuseStep 6473357 = 2427509) B2427509
theorem B4318865 : Blo 1277957 4318865 := bstep (se 2 (by rfl) ⟨1619574, by rfl⟩ : syracuseStep 4318865 = 3239149) B3239149
theorem B1279635 : Blo 1277957 1279635 := bstep (se 1 (by rfl) ⟨959726, by rfl⟩ : syracuseStep 1279635 = 1919453) B1919453
theorem B1918625 : Blo 1277957 1918625 := bstep (se 2 (by rfl) ⟨719484, by rfl⟩ : syracuseStep 1918625 = 1438969) B1438969
theorem B1279651 : Blo 1277957 1279651 := bstep (se 1 (by rfl) ⟨959738, by rfl⟩ : syracuseStep 1279651 = 1919477) B1919477
theorem B1918643 : Blo 1277957 1918643 := bstep (se 1 (by rfl) ⟨1438982, by rfl⟩ : syracuseStep 1918643 = 2877965) B2877965
theorem B1279667 : Blo 1277957 1279667 := bstep (se 1 (by rfl) ⟨959750, by rfl⟩ : syracuseStep 1279667 = 1919501) B1919501
theorem B1279683 : Blo 1277957 1279683 := bstep (se 1 (by rfl) ⟨959762, by rfl⟩ : syracuseStep 1279683 = 1919525) B1919525
theorem B2877137 : Blo 1277957 2877137 := bstep (se 2 (by rfl) ⟨1078926, by rfl⟩ : syracuseStep 2877137 = 2157853) B2157853
theorem B1918673 : Blo 1277957 1918673 := bstep (se 2 (by rfl) ⟨719502, by rfl⟩ : syracuseStep 1918673 = 1439005) B1439005
theorem B1279699 : Blo 1277957 1279699 := bstep (se 1 (by rfl) ⟨959774, by rfl⟩ : syracuseStep 1279699 = 1919549) B1919549
theorem B2877155 : Blo 1277957 2877155 := bstep (se 1 (by rfl) ⟨2157866, by rfl⟩ : syracuseStep 2877155 = 4315733) B4315733
theorem B1918691 : Blo 1277957 1918691 := bstep (se 1 (by rfl) ⟨1439018, by rfl⟩ : syracuseStep 1918691 = 2878037) B2878037
theorem B1279715 : Blo 1277957 1279715 := bstep (se 1 (by rfl) ⟨959786, by rfl⟩ : syracuseStep 1279715 = 1919573) B1919573
theorem B3458801 : Blo 1277957 3458801 := bstep (se 2 (by rfl) ⟨1297050, by rfl⟩ : syracuseStep 3458801 = 2594101) B2594101
theorem B1279731 : Blo 1277957 1279731 := bstep (se 1 (by rfl) ⟨959798, by rfl⟩ : syracuseStep 1279731 = 1919597) B1919597
theorem B1918721 : Blo 1277957 1918721 := bstep (se 2 (by rfl) ⟨719520, by rfl⟩ : syracuseStep 1918721 = 1439041) B1439041
theorem B1279747 : Blo 1277957 1279747 := bstep (se 1 (by rfl) ⟨959810, by rfl⟩ : syracuseStep 1279747 = 1919621) B1919621
theorem B1918739 : Blo 1277957 1918739 := bstep (se 1 (by rfl) ⟨1439054, by rfl⟩ : syracuseStep 1918739 = 2878109) B2878109
theorem B1279763 : Blo 1277957 1279763 := bstep (se 1 (by rfl) ⟨959822, by rfl⟩ : syracuseStep 1279763 = 1919645) B1919645
theorem B1279779 : Blo 1277957 1279779 := bstep (se 1 (by rfl) ⟨959834, by rfl⟩ : syracuseStep 1279779 = 1919669) B1919669
theorem B1918769 : Blo 1277957 1918769 := bstep (se 2 (by rfl) ⟨719538, by rfl⟩ : syracuseStep 1918769 = 1439077) B1439077
theorem B1279795 : Blo 1277957 1279795 := bstep (se 1 (by rfl) ⟨959846, by rfl⟩ : syracuseStep 1279795 = 1919693) B1919693
theorem B1918787 : Blo 1277957 1918787 := bstep (se 1 (by rfl) ⟨1439090, by rfl⟩ : syracuseStep 1918787 = 2878181) B2878181
theorem B1279811 : Blo 1277957 1279811 := bstep (se 1 (by rfl) ⟨959858, by rfl⟩ : syracuseStep 1279811 = 1919717) B1919717
theorem B8193869 : Blo 1277957 8193869 := bstep (se 3 (by rfl) ⟨1536350, by rfl⟩ : syracuseStep 8193869 = 3072701) B3072701
theorem B1279827 : Blo 1277957 1279827 := bstep (se 1 (by rfl) ⟨959870, by rfl⟩ : syracuseStep 1279827 = 1919741) B1919741
theorem B1918817 : Blo 1277957 1918817 := bstep (se 2 (by rfl) ⟨719556, by rfl⟩ : syracuseStep 1918817 = 1439113) B1439113
theorem B1279843 : Blo 1277957 1279843 := bstep (se 1 (by rfl) ⟨959882, by rfl⟩ : syracuseStep 1279843 = 1919765) B1919765
theorem B1918835 : Blo 1277957 1918835 := bstep (se 1 (by rfl) ⟨1439126, by rfl⟩ : syracuseStep 1918835 = 2878253) B2878253
theorem B1279859 : Blo 1277957 1279859 := bstep (se 1 (by rfl) ⟨959894, by rfl⟩ : syracuseStep 1279859 = 1919789) B1919789
theorem B1279875 : Blo 1277957 1279875 := bstep (se 1 (by rfl) ⟨959906, by rfl⟩ : syracuseStep 1279875 = 1919813) B1919813
theorem B1918865 : Blo 1277957 1918865 := bstep (se 2 (by rfl) ⟨719574, by rfl⟩ : syracuseStep 1918865 = 1439149) B1439149
theorem B1279891 : Blo 1277957 1279891 := bstep (se 1 (by rfl) ⟨959918, by rfl⟩ : syracuseStep 1279891 = 1919837) B1919837
theorem B1918883 : Blo 1277957 1918883 := bstep (se 1 (by rfl) ⟨1439162, by rfl⟩ : syracuseStep 1918883 = 2878325) B2878325
theorem B1279907 : Blo 1277957 1279907 := bstep (se 1 (by rfl) ⟨959930, by rfl⟩ : syracuseStep 1279907 = 1919861) B1919861
theorem B2303921 : Blo 1277957 2303921 := bstep (se 2 (by rfl) ⟨863970, by rfl⟩ : syracuseStep 2303921 = 1727941) B1727941
theorem B1279923 : Blo 1277957 1279923 := bstep (se 1 (by rfl) ⟨959942, by rfl⟩ : syracuseStep 1279923 = 1919885) B1919885
theorem B1918913 : Blo 1277957 1918913 := bstep (se 2 (by rfl) ⟨719592, by rfl⟩ : syracuseStep 1918913 = 1439185) B1439185
theorem B2918339 : Blo 1277957 2918339 := bstep (se 1 (by rfl) ⟨2188754, by rfl⟩ : syracuseStep 2918339 = 4377509) B4377509
theorem B1279939 : Blo 1277957 1279939 := bstep (se 1 (by rfl) ⟨959954, by rfl⟩ : syracuseStep 1279939 = 1919909) B1919909
theorem B1918931 : Blo 1277957 1918931 := bstep (se 1 (by rfl) ⟨1439198, by rfl⟩ : syracuseStep 1918931 = 2878397) B2878397
theorem B1279955 : Blo 1277957 1279955 := bstep (se 1 (by rfl) ⟨959966, by rfl⟩ : syracuseStep 1279955 = 1919933) B1919933
theorem B2050019 : Blo 1277957 2050019 := bstep (se 1 (by rfl) ⟨1537514, by rfl⟩ : syracuseStep 2050019 = 3075029) B3075029
theorem B2877425 : Blo 1277957 2877425 := bstep (se 2 (by rfl) ⟨1079034, by rfl⟩ : syracuseStep 2877425 = 2158069) B2158069
theorem B1918961 : Blo 1277957 1918961 := bstep (se 2 (by rfl) ⟨719610, by rfl⟩ : syracuseStep 1918961 = 1439221) B1439221
theorem B2877443 : Blo 1277957 2877443 := bstep (se 1 (by rfl) ⟨2158082, by rfl⟩ : syracuseStep 2877443 = 4316165) B4316165
theorem B1918979 : Blo 1277957 1918979 := bstep (se 1 (by rfl) ⟨1439234, by rfl⟩ : syracuseStep 1918979 = 2878469) B2878469
theorem B2050051 : Blo 1277957 2050051 := bstep (se 1 (by rfl) ⟨1537538, by rfl⟩ : syracuseStep 2050051 = 3075077) B3075077
theorem B1919009 : Blo 1277957 1919009 := bstep (se 2 (by rfl) ⟨719628, by rfl⟩ : syracuseStep 1919009 = 1439257) B1439257
theorem B5253169 : Blo 1277957 5253169 := bstep (se 2 (by rfl) ⟨1969938, by rfl⟩ : syracuseStep 5253169 = 3939877) B3939877
theorem B1820723 : Blo 1277957 1820723 := bstep (se 1 (by rfl) ⟨1365542, by rfl⟩ : syracuseStep 1820723 = 2731085) B2731085
theorem B1919027 : Blo 1277957 1919027 := bstep (se 1 (by rfl) ⟨1439270, by rfl⟩ : syracuseStep 1919027 = 2878541) B2878541
theorem B2156611 : Blo 1277957 2156611 := bstep (se 1 (by rfl) ⟨1617458, by rfl⟩ : syracuseStep 2156611 = 3234917) B3234917
theorem B1919057 : Blo 1277957 1919057 := bstep (se 2 (by rfl) ⟨719646, by rfl⟩ : syracuseStep 1919057 = 1439293) B1439293
theorem B1919075 : Blo 1277957 1919075 := bstep (se 1 (by rfl) ⟨1439306, by rfl⟩ : syracuseStep 1919075 = 2878613) B2878613
theorem B2426993 : Blo 1277957 2426993 := bstep (se 2 (by rfl) ⟨910122, by rfl⟩ : syracuseStep 2426993 = 1820245) B1820245
theorem B1919105 : Blo 1277957 1919105 := bstep (se 2 (by rfl) ⟨719664, by rfl⟩ : syracuseStep 1919105 = 1439329) B1439329
theorem B1919123 : Blo 1277957 1919123 := bstep (se 1 (by rfl) ⟨1439342, by rfl⟩ : syracuseStep 1919123 = 2878685) B2878685
theorem B4319405 : Blo 1277957 4319405 := bstep (se 3 (by rfl) ⟨809888, by rfl⟩ : syracuseStep 4319405 = 1619777) B1619777
theorem B4376753 : Blo 1277957 4376753 := bstep (se 2 (by rfl) ⟨1641282, by rfl⟩ : syracuseStep 4376753 = 3282565) B3282565
theorem B1919153 : Blo 1277957 1919153 := bstep (se 2 (by rfl) ⟨719682, by rfl⟩ : syracuseStep 1919153 = 1439365) B1439365
theorem B1919171 : Blo 1277957 1919171 := bstep (se 1 (by rfl) ⟨1439378, by rfl⟩ : syracuseStep 1919171 = 2878757) B2878757
theorem B2156753 : Blo 1277957 2156753 := bstep (se 2 (by rfl) ⟨808782, by rfl⟩ : syracuseStep 2156753 = 1617565) B1617565
theorem B1919201 : Blo 1277957 1919201 := bstep (se 2 (by rfl) ⟨719700, by rfl⟩ : syracuseStep 1919201 = 1439401) B1439401
theorem B4319459 : Blo 1277957 4319459 := bstep (se 1 (by rfl) ⟨3239594, by rfl⟩ : syracuseStep 4319459 = 6479189) B6479189
theorem B1919219 : Blo 1277957 1919219 := bstep (se 1 (by rfl) ⟨1439414, by rfl⟩ : syracuseStep 1919219 = 2878829) B2878829
theorem B2730257 : Blo 1277957 2730257 := bstep (se 2 (by rfl) ⟨1023846, by rfl⟩ : syracuseStep 2730257 = 2047693) B2047693
theorem B2877713 : Blo 1277957 2877713 := bstep (se 2 (by rfl) ⟨1079142, by rfl⟩ : syracuseStep 2877713 = 2158285) B2158285
theorem B1919249 : Blo 1277957 1919249 := bstep (se 2 (by rfl) ⟨719718, by rfl⟩ : syracuseStep 1919249 = 1439437) B1439437
theorem B2877731 : Blo 1277957 2877731 := bstep (se 1 (by rfl) ⟨2158298, by rfl⟩ : syracuseStep 2877731 = 4316597) B4316597
theorem B1919267 : Blo 1277957 1919267 := bstep (se 1 (by rfl) ⟨1439450, by rfl⟩ : syracuseStep 1919267 = 2878901) B2878901
theorem B1919297 : Blo 1277957 1919297 := bstep (se 2 (by rfl) ⟨719736, by rfl⟩ : syracuseStep 1919297 = 1439473) B1439473
theorem B2156881 : Blo 1277957 2156881 := bstep (se 2 (by rfl) ⟨808830, by rfl⟩ : syracuseStep 2156881 = 1617661) B1617661
theorem B1919315 : Blo 1277957 1919315 := bstep (se 1 (by rfl) ⟨1439486, by rfl⟩ : syracuseStep 1919315 = 2878973) B2878973
theorem B14559587 : Blo 1277957 14559587 := bstep (se 1 (by rfl) ⟨10919690, by rfl⟩ : syracuseStep 14559587 = 21839381) B21839381
theorem B1919345 : Blo 1277957 1919345 := bstep (se 2 (by rfl) ⟨719754, by rfl⟩ : syracuseStep 1919345 = 1439509) B1439509
theorem B2156915 : Blo 1277957 2156915 := bstep (se 1 (by rfl) ⟨1617686, by rfl⟩ : syracuseStep 2156915 = 3235373) B3235373
theorem B1919363 : Blo 1277957 1919363 := bstep (se 1 (by rfl) ⟨1439522, by rfl⟩ : syracuseStep 1919363 = 2879045) B2879045
theorem B3238289 : Blo 1277957 3238289 := bstep (se 2 (by rfl) ⟨1214358, by rfl⟩ : syracuseStep 3238289 = 2428717) B2428717
theorem B1919393 : Blo 1277957 1919393 := bstep (se 2 (by rfl) ⟨719772, by rfl⟩ : syracuseStep 1919393 = 1439545) B1439545
theorem B1919411 : Blo 1277957 1919411 := bstep (se 1 (by rfl) ⟨1439558, by rfl⟩ : syracuseStep 1919411 = 2879117) B2879117
theorem B3238339 : Blo 1277957 3238339 := bstep (se 1 (by rfl) ⟨2428754, by rfl⟩ : syracuseStep 3238339 = 4857509) B4857509
theorem B7006661 : Blo 1277957 7006661 := bstep (se 4 (by rfl) ⟨656874, by rfl⟩ : syracuseStep 7006661 = 1313749) B1313749
theorem B3639761 : Blo 1277957 3639761 := bstep (se 2 (by rfl) ⟨1364910, by rfl⟩ : syracuseStep 3639761 = 2729821) B2729821
theorem B1919441 : Blo 1277957 1919441 := bstep (se 2 (by rfl) ⟨719790, by rfl⟩ : syracuseStep 1919441 = 1439581) B1439581
theorem B1919459 : Blo 1277957 1919459 := bstep (se 1 (by rfl) ⟨1439594, by rfl⟩ : syracuseStep 1919459 = 2879189) B2879189
theorem B4319729 : Blo 1277957 4319729 := bstep (se 2 (by rfl) ⟨1619898, by rfl⟩ : syracuseStep 4319729 = 3239797) B3239797
theorem B2157043 : Blo 1277957 2157043 := bstep (se 1 (by rfl) ⟨1617782, by rfl⟩ : syracuseStep 2157043 = 3235565) B3235565
theorem B1919489 : Blo 1277957 1919489 := bstep (se 2 (by rfl) ⟨719808, by rfl⟩ : syracuseStep 1919489 = 1439617) B1439617
theorem B7285261 : Blo 1277957 7285261 := bstep (se 3 (by rfl) ⟨1365986, by rfl⟩ : syracuseStep 7285261 = 2731973) B2731973
theorem B1919507 : Blo 1277957 1919507 := bstep (se 1 (by rfl) ⟨1439630, by rfl⟩ : syracuseStep 1919507 = 2879261) B2879261
theorem B2918947 : Blo 1277957 2918947 := bstep (se 1 (by rfl) ⟨2189210, by rfl⟩ : syracuseStep 2918947 = 4378421) B4378421
theorem B2878001 : Blo 1277957 2878001 := bstep (se 2 (by rfl) ⟨1079250, by rfl⟩ : syracuseStep 2878001 = 2158501) B2158501
theorem B1919537 : Blo 1277957 1919537 := bstep (se 2 (by rfl) ⟨719826, by rfl⟩ : syracuseStep 1919537 = 1439653) B1439653
theorem B2878019 : Blo 1277957 2878019 := bstep (se 1 (by rfl) ⟨2158514, by rfl⟩ : syracuseStep 2878019 = 4317029) B4317029
theorem B1919555 : Blo 1277957 1919555 := bstep (se 1 (by rfl) ⟨1439666, by rfl⟩ : syracuseStep 1919555 = 2879333) B2879333
theorem B3238481 : Blo 1277957 3238481 := bstep (se 2 (by rfl) ⟨1214430, by rfl⟩ : syracuseStep 3238481 = 2428861) B2428861
theorem B1919585 : Blo 1277957 1919585 := bstep (se 2 (by rfl) ⟨719844, by rfl⟩ : syracuseStep 1919585 = 1439689) B1439689
theorem B1919603 : Blo 1277957 1919603 := bstep (se 1 (by rfl) ⟨1439702, by rfl⟩ : syracuseStep 1919603 = 2879405) B2879405
theorem B2157185 : Blo 1277957 2157185 := bstep (se 2 (by rfl) ⟨808944, by rfl⟩ : syracuseStep 2157185 = 1617889) B1617889
theorem B1919633 : Blo 1277957 1919633 := bstep (se 2 (by rfl) ⟨719862, by rfl⟩ : syracuseStep 1919633 = 1439725) B1439725
theorem B3156643 : Blo 1277957 3156643 := bstep (se 1 (by rfl) ⟨2367482, by rfl⟩ : syracuseStep 3156643 = 4734965) B4734965
theorem B1919651 : Blo 1277957 1919651 := bstep (se 1 (by rfl) ⟨1439738, by rfl⟩ : syracuseStep 1919651 = 2879477) B2879477
theorem B1821361 : Blo 1277957 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B1919681 : Blo 1277957 1919681 := bstep (se 2 (by rfl) ⟨719880, by rfl⟩ : syracuseStep 1919681 = 1439761) B1439761
theorem B1919699 : Blo 1277957 1919699 := bstep (se 1 (by rfl) ⟨1439774, by rfl⟩ : syracuseStep 1919699 = 2879549) B2879549
theorem B1919729 : Blo 1277957 1919729 := bstep (se 2 (by rfl) ⟨719898, by rfl⟩ : syracuseStep 1919729 = 1439797) B1439797
theorem B2157313 : Blo 1277957 2157313 := bstep (se 2 (by rfl) ⟨808992, by rfl⟩ : syracuseStep 2157313 = 1617985) B1617985
theorem B1919747 : Blo 1277957 1919747 := bstep (se 1 (by rfl) ⟨1439810, by rfl⟩ : syracuseStep 1919747 = 2879621) B2879621
theorem B4606733 : Blo 1277957 4606733 := bstep (se 3 (by rfl) ⟨863762, by rfl⟩ : syracuseStep 4606733 = 1727525) B1727525
theorem B9718541 : Blo 1277957 9718541 := bstep (se 3 (by rfl) ⟨1822226, by rfl⟩ : syracuseStep 9718541 = 3644453) B3644453
theorem B4098833 : Blo 1277957 4098833 := bstep (se 2 (by rfl) ⟨1537062, by rfl⟩ : syracuseStep 4098833 = 3074125) B3074125
theorem B1919777 : Blo 1277957 1919777 := bstep (se 2 (by rfl) ⟨719916, by rfl⟩ : syracuseStep 1919777 = 1439833) B1439833
theorem B2157347 : Blo 1277957 2157347 := bstep (se 1 (by rfl) ⟨1618010, by rfl⟩ : syracuseStep 2157347 = 3236021) B3236021
theorem B1821475 : Blo 1277957 1821475 := bstep (se 1 (by rfl) ⟨1366106, by rfl⟩ : syracuseStep 1821475 = 2732213) B2732213
theorem B6916913 : Blo 1277957 6916913 := bstep (se 2 (by rfl) ⟨2593842, by rfl⟩ : syracuseStep 6916913 = 5187685) B5187685
theorem B1919795 : Blo 1277957 1919795 := bstep (se 1 (by rfl) ⟨1439846, by rfl⟩ : syracuseStep 1919795 = 2879693) B2879693
theorem B4098883 : Blo 1277957 4098883 := bstep (se 1 (by rfl) ⟨3074162, by rfl⟩ : syracuseStep 4098883 = 6148325) B6148325
theorem B2878289 : Blo 1277957 2878289 := bstep (se 2 (by rfl) ⟨1079358, by rfl⟩ : syracuseStep 2878289 = 2158717) B2158717
theorem B1919825 : Blo 1277957 1919825 := bstep (se 2 (by rfl) ⟨719934, by rfl⟩ : syracuseStep 1919825 = 1439869) B1439869
theorem B8096611 : Blo 1277957 8096611 := bstep (se 1 (by rfl) ⟨6072458, by rfl⟩ : syracuseStep 8096611 = 12144917) B12144917
theorem B2878307 : Blo 1277957 2878307 := bstep (se 1 (by rfl) ⟨2158730, by rfl⟩ : syracuseStep 2878307 = 4317461) B4317461
theorem B1919843 : Blo 1277957 1919843 := bstep (se 1 (by rfl) ⟨1439882, by rfl⟩ : syracuseStep 1919843 = 2879765) B2879765
theorem B1919873 : Blo 1277957 1919873 := bstep (se 2 (by rfl) ⟨719952, by rfl⟩ : syracuseStep 1919873 = 1439905) B1439905
theorem B1919891 : Blo 1277957 1919891 := bstep (se 1 (by rfl) ⟨1439918, by rfl⟩ : syracuseStep 1919891 = 2879837) B2879837
theorem B2157475 : Blo 1277957 2157475 := bstep (se 1 (by rfl) ⟨1618106, by rfl⟩ : syracuseStep 2157475 = 3236213) B3236213
theorem B1919921 : Blo 1277957 1919921 := bstep (se 2 (by rfl) ⟨719970, by rfl⟩ : syracuseStep 1919921 = 1439941) B1439941
theorem B2427889 : Blo 1277957 2427889 := bstep (se 2 (by rfl) ⟨910458, by rfl⟩ : syracuseStep 2427889 = 1820917) B1820917
theorem B2157617 : Blo 1277957 2157617 := bstep (se 2 (by rfl) ⟨809106, by rfl⟩ : syracuseStep 2157617 = 1618213) B1618213
theorem B2878577 : Blo 1277957 2878577 := bstep (se 2 (by rfl) ⟨1079466, by rfl⟩ : syracuseStep 2878577 = 2158933) B2158933
theorem B2878595 : Blo 1277957 2878595 := bstep (se 1 (by rfl) ⟨2158946, by rfl⟩ : syracuseStep 2878595 = 4317893) B4317893
theorem B6229133 : Blo 1277957 6229133 := bstep (se 3 (by rfl) ⟨1167962, by rfl⟩ : syracuseStep 6229133 = 2335925) B2335925
theorem B2731153 : Blo 1277957 2731153 := bstep (se 2 (by rfl) ⟨1024182, by rfl⟩ : syracuseStep 2731153 = 2048365) B2048365
theorem B2428049 : Blo 1277957 2428049 := bstep (se 2 (by rfl) ⟨910518, by rfl⟩ : syracuseStep 2428049 = 1821037) B1821037
theorem B2731171 : Blo 1277957 2731171 := bstep (se 1 (by rfl) ⟨2048378, by rfl⟩ : syracuseStep 2731171 = 4096757) B4096757
theorem B2157745 : Blo 1277957 2157745 := bstep (se 2 (by rfl) ⟨809154, by rfl⟩ : syracuseStep 2157745 = 1618309) B1618309
theorem B2157779 : Blo 1277957 2157779 := bstep (se 1 (by rfl) ⟨1618334, by rfl⟩ : syracuseStep 2157779 = 3236669) B3236669
theorem B2157907 : Blo 1277957 2157907 := bstep (se 1 (by rfl) ⟨1618430, by rfl⟩ : syracuseStep 2157907 = 3236861) B3236861
theorem B4853105 : Blo 1277957 4853105 := bstep (se 2 (by rfl) ⟨1819914, by rfl⟩ : syracuseStep 4853105 = 3639829) B3639829
theorem B3640717 : Blo 1277957 3640717 := bstep (se 3 (by rfl) ⟨682634, by rfl⟩ : syracuseStep 3640717 = 1365269) B1365269
theorem B3886481 : Blo 1277957 3886481 := bstep (se 2 (by rfl) ⟨1457430, by rfl⟩ : syracuseStep 3886481 = 2914861) B2914861
theorem B2878865 : Blo 1277957 2878865 := bstep (se 2 (by rfl) ⟨1079574, by rfl⟩ : syracuseStep 2878865 = 2159149) B2159149
theorem B2878883 : Blo 1277957 2878883 := bstep (se 1 (by rfl) ⟨2159162, by rfl⟩ : syracuseStep 2878883 = 4318325) B4318325
theorem B16379333 : Blo 1277957 16379333 := bstep (se 4 (by rfl) ⟨1535562, by rfl⟩ : syracuseStep 16379333 = 3071125) B3071125
theorem B4607437 : Blo 1277957 4607437 := bstep (se 3 (by rfl) ⟨863894, by rfl⟩ : syracuseStep 4607437 = 1727789) B1727789
theorem B2158049 : Blo 1277957 2158049 := bstep (se 2 (by rfl) ⟨809268, by rfl⟩ : syracuseStep 2158049 = 1618537) B1618537
theorem B8752625 : Blo 1277957 8752625 := bstep (se 2 (by rfl) ⟨3282234, by rfl⟩ : syracuseStep 8752625 = 6564469) B6564469
theorem B2428451 : Blo 1277957 2428451 := bstep (se 1 (by rfl) ⟨1821338, by rfl⟩ : syracuseStep 2428451 = 3642677) B3642677
theorem B3239473 : Blo 1277957 3239473 := bstep (se 2 (by rfl) ⟨1214802, by rfl⟩ : syracuseStep 3239473 = 2429605) B2429605
theorem B85298741 : Blo 1277957 85298741 := bstep (se 5 (by rfl) ⟨3998378, by rfl⟩ : syracuseStep 85298741 = 7996757) B7996757
theorem B2158177 : Blo 1277957 2158177 := bstep (se 2 (by rfl) ⟨809316, by rfl⟩ : syracuseStep 2158177 = 1618633) B1618633
theorem B3640945 : Blo 1277957 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B2158211 : Blo 1277957 2158211 := bstep (se 1 (by rfl) ⟨1618658, by rfl⟩ : syracuseStep 2158211 = 3237317) B3237317
theorem B4099729 : Blo 1277957 4099729 := bstep (se 2 (by rfl) ⟨1537398, by rfl⟩ : syracuseStep 4099729 = 3074797) B3074797
theorem B2879153 : Blo 1277957 2879153 := bstep (se 2 (by rfl) ⟨1079682, by rfl⟩ : syracuseStep 2879153 = 2159365) B2159365
theorem B2879171 : Blo 1277957 2879171 := bstep (se 1 (by rfl) ⟨2159378, by rfl⟩ : syracuseStep 2879171 = 4318757) B4318757
theorem B2158339 : Blo 1277957 2158339 := bstep (se 1 (by rfl) ⟨1618754, by rfl⟩ : syracuseStep 2158339 = 3237509) B3237509
theorem B3641105 : Blo 1277957 3641105 := bstep (se 2 (by rfl) ⟨1365414, by rfl⟩ : syracuseStep 3641105 = 2730829) B2730829
theorem B3239747 : Blo 1277957 3239747 := bstep (se 1 (by rfl) ⟨2429810, by rfl⟩ : syracuseStep 3239747 = 4859621) B4859621
theorem B3641219 : Blo 1277957 3641219 := bstep (se 1 (by rfl) ⟨2730914, by rfl⟩ : syracuseStep 3641219 = 5461829) B5461829
theorem B2158481 : Blo 1277957 2158481 := bstep (se 2 (by rfl) ⟨809430, by rfl⟩ : syracuseStep 2158481 = 1618861) B1618861
theorem B2076625 : Blo 1277957 2076625 := bstep (se 2 (by rfl) ⟨778734, by rfl⟩ : syracuseStep 2076625 = 1557469) B1557469
theorem B2879441 : Blo 1277957 2879441 := bstep (se 2 (by rfl) ⟨1079790, by rfl⟩ : syracuseStep 2879441 = 2159581) B2159581
theorem B2879459 : Blo 1277957 2879459 := bstep (se 1 (by rfl) ⟨2159594, by rfl⟩ : syracuseStep 2879459 = 4319189) B4319189
theorem B6230029 : Blo 1277957 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B2158609 : Blo 1277957 2158609 := bstep (se 2 (by rfl) ⟨809478, by rfl⟩ : syracuseStep 2158609 = 1618957) B1618957
theorem B5836835 : Blo 1277957 5836835 := bstep (se 1 (by rfl) ⟨4377626, by rfl⟩ : syracuseStep 5836835 = 8755253) B8755253
theorem B2158643 : Blo 1277957 2158643 := bstep (se 1 (by rfl) ⟨1618982, by rfl⟩ : syracuseStep 2158643 = 3237965) B3237965
theorem B1437763 : Blo 1277957 1437763 := bstep (se 1 (by rfl) ⟨1078322, by rfl⟩ : syracuseStep 1437763 = 2156645) B2156645
theorem B1618051 : Blo 1277957 1618051 := bstep (se 1 (by rfl) ⟨1213538, by rfl⟩ : syracuseStep 1618051 = 2427077) B2427077
theorem B4206755 : Blo 1277957 4206755 := bstep (se 1 (by rfl) ⟨3155066, by rfl⟩ : syracuseStep 4206755 = 6310133) B6310133
theorem B2158771 : Blo 1277957 2158771 := bstep (se 1 (by rfl) ⟨1619078, by rfl⟩ : syracuseStep 2158771 = 3238157) B3238157
theorem B1437907 : Blo 1277957 1437907 := bstep (se 1 (by rfl) ⟨1078430, by rfl⟩ : syracuseStep 1437907 = 2156861) B2156861
theorem B1618147 : Blo 1277957 1618147 := bstep (se 1 (by rfl) ⟨1213610, by rfl⟩ : syracuseStep 1618147 = 2427221) B2427221
theorem B2879729 : Blo 1277957 2879729 := bstep (se 2 (by rfl) ⟨1079898, by rfl⟩ : syracuseStep 2879729 = 2159797) B2159797
theorem B2879747 : Blo 1277957 2879747 := bstep (se 1 (by rfl) ⟨2159810, by rfl⟩ : syracuseStep 2879747 = 4319621) B4319621
theorem B4313357 : Blo 1277957 4313357 := bstep (se 3 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 4313357 = 1617509) B1617509
theorem B2158913 : Blo 1277957 2158913 := bstep (se 2 (by rfl) ⟨809592, by rfl⟩ : syracuseStep 2158913 = 1619185) B1619185
theorem B4313411 : Blo 1277957 4313411 := bstep (se 1 (by rfl) ⟨3235058, by rfl⟩ : syracuseStep 4313411 = 6470117) B6470117
theorem B1438051 : Blo 1277957 1438051 := bstep (se 1 (by rfl) ⟨1078538, by rfl⟩ : syracuseStep 1438051 = 2157077) B2157077
theorem B2429347 : Blo 1277957 2429347 := bstep (se 1 (by rfl) ⟨1822010, by rfl⟩ : syracuseStep 2429347 = 3644021) B3644021
theorem B2159041 : Blo 1277957 2159041 := bstep (se 2 (by rfl) ⟨809640, by rfl⟩ : syracuseStep 2159041 = 1619281) B1619281
theorem B10932677 : Blo 1277957 10932677 := bstep (se 4 (by rfl) ⟨1024938, by rfl⟩ : syracuseStep 10932677 = 2049877) B2049877
theorem B7287245 : Blo 1277957 7287245 := bstep (se 3 (by rfl) ⟨1366358, by rfl⟩ : syracuseStep 7287245 = 2732717) B2732717
theorem B2159075 : Blo 1277957 2159075 := bstep (se 1 (by rfl) ⟨1619306, by rfl⟩ : syracuseStep 2159075 = 3238613) B3238613
theorem B6476273 : Blo 1277957 6476273 := bstep (se 2 (by rfl) ⟨2428602, by rfl⟩ : syracuseStep 6476273 = 4857205) B4857205
theorem B1438195 : Blo 1277957 1438195 := bstep (se 1 (by rfl) ⟨1078646, by rfl⟩ : syracuseStep 1438195 = 2157293) B2157293
theorem B5460529 : Blo 1277957 5460529 := bstep (se 2 (by rfl) ⟨2047698, by rfl⟩ : syracuseStep 5460529 = 4095397) B4095397
theorem B2429507 : Blo 1277957 2429507 := bstep (se 1 (by rfl) ⟨1822130, by rfl⟩ : syracuseStep 2429507 = 3644261) B3644261
theorem B4313681 : Blo 1277957 4313681 := bstep (se 2 (by rfl) ⟨1617630, by rfl⟩ : syracuseStep 4313681 = 3235261) B3235261
theorem B2159203 : Blo 1277957 2159203 := bstep (se 1 (by rfl) ⟨1619402, by rfl⟩ : syracuseStep 2159203 = 3238805) B3238805
theorem B1438339 : Blo 1277957 1438339 := bstep (se 1 (by rfl) ⟨1078754, by rfl⟩ : syracuseStep 1438339 = 2157509) B2157509
theorem B1577651 : Blo 1277957 1577651 := bstep (se 1 (by rfl) ⟨1183238, by rfl⟩ : syracuseStep 1577651 = 2366477) B2366477
theorem B1618643 : Blo 1277957 1618643 := bstep (se 1 (by rfl) ⟨1213982, by rfl⟩ : syracuseStep 1618643 = 2427965) B2427965
theorem B2159345 : Blo 1277957 2159345 := bstep (se 2 (by rfl) ⟨809754, by rfl⟩ : syracuseStep 2159345 = 1619509) B1619509
theorem B1438483 : Blo 1277957 1438483 := bstep (se 1 (by rfl) ⟨1078862, by rfl⟩ : syracuseStep 1438483 = 2157725) B2157725
theorem B4854563 : Blo 1277957 4854563 := bstep (se 1 (by rfl) ⟨3640922, by rfl⟩ : syracuseStep 4854563 = 7281845) B7281845
theorem B8188721 : Blo 1277957 8188721 := bstep (se 2 (by rfl) ⟨3070770, by rfl⟩ : syracuseStep 8188721 = 6141541) B6141541
theorem B7279429 : Blo 1277957 7279429 := bstep (se 4 (by rfl) ⟨682446, by rfl⟩ : syracuseStep 7279429 = 1364893) B1364893
theorem B3642221 : Blo 1277957 3642221 := bstep (se 3 (by rfl) ⟨682916, by rfl⟩ : syracuseStep 3642221 = 1365833) B1365833
theorem B6746993 : Blo 1277957 6746993 := bstep (se 2 (by rfl) ⟨2530122, by rfl⟩ : syracuseStep 6746993 = 5060245) B5060245
theorem B2159473 : Blo 1277957 2159473 := bstep (se 2 (by rfl) ⟨809802, by rfl⟩ : syracuseStep 2159473 = 1619605) B1619605
theorem B1536899 : Blo 1277957 1536899 := bstep (se 1 (by rfl) ⟨1152674, by rfl⟩ : syracuseStep 1536899 = 2305349) B2305349
theorem B8196997 : Blo 1277957 8196997 := bstep (se 4 (by rfl) ⟨768468, by rfl⟩ : syracuseStep 8196997 = 1536937) B1536937
theorem B2159507 : Blo 1277957 2159507 := bstep (se 1 (by rfl) ⟨1619630, by rfl⟩ : syracuseStep 2159507 = 3239261) B3239261
theorem B1438627 : Blo 1277957 1438627 := bstep (se 1 (by rfl) ⟨1078970, by rfl⟩ : syracuseStep 1438627 = 2157941) B2157941
theorem B3888109 : Blo 1277957 3888109 := bstep (se 3 (by rfl) ⟨729020, by rfl⟩ : syracuseStep 3888109 = 1458041) B1458041
theorem B2159635 : Blo 1277957 2159635 := bstep (se 1 (by rfl) ⟨1619726, by rfl⟩ : syracuseStep 2159635 = 3239453) B3239453
theorem B3642403 : Blo 1277957 3642403 := bstep (se 1 (by rfl) ⟨2731802, by rfl⟩ : syracuseStep 3642403 = 5463605) B5463605
theorem B1438771 : Blo 1277957 1438771 := bstep (se 1 (by rfl) ⟨1079078, by rfl⟩ : syracuseStep 1438771 = 2158157) B2158157
theorem B9712709 : Blo 1277957 9712709 := bstep (se 4 (by rfl) ⟨910566, by rfl⟩ : syracuseStep 9712709 = 1821133) B1821133
theorem B4314221 : Blo 1277957 4314221 := bstep (se 3 (by rfl) ⟨808916, by rfl⟩ : syracuseStep 4314221 = 1617833) B1617833
theorem B2159777 : Blo 1277957 2159777 := bstep (se 2 (by rfl) ⟨809916, by rfl⟩ : syracuseStep 2159777 = 1619833) B1619833
theorem B4314275 : Blo 1277957 4314275 := bstep (se 1 (by rfl) ⟨3235706, by rfl⟩ : syracuseStep 4314275 = 6471413) B6471413
theorem B1438915 : Blo 1277957 1438915 := bstep (se 1 (by rfl) ⟨1079186, by rfl⟩ : syracuseStep 1438915 = 2158373) B2158373
theorem B3642563 : Blo 1277957 3642563 := bstep (se 1 (by rfl) ⟨2731922, by rfl⟩ : syracuseStep 3642563 = 5463845) B5463845
theorem B2593987 : Blo 1277957 2593987 := bstep (se 1 (by rfl) ⟨1945490, by rfl⟩ : syracuseStep 2593987 = 3890981) B3890981
theorem B2159905 : Blo 1277957 2159905 := bstep (se 2 (by rfl) ⟨809964, by rfl⟩ : syracuseStep 2159905 = 1619929) B1619929
theorem B6141233 : Blo 1277957 6141233 := bstep (se 2 (by rfl) ⟨2302962, by rfl⟩ : syracuseStep 6141233 = 4605925) B4605925
theorem B1439059 : Blo 1277957 1439059 := bstep (se 1 (by rfl) ⟨1079294, by rfl⟩ : syracuseStep 1439059 = 2158589) B2158589
theorem B7288177 : Blo 1277957 7288177 := bstep (se 2 (by rfl) ⟨2733066, by rfl⟩ : syracuseStep 7288177 = 5466133) B5466133
theorem B2733443 : Blo 1277957 2733443 := bstep (se 1 (by rfl) ⟨2050082, by rfl⟩ : syracuseStep 2733443 = 4100165) B4100165
theorem B1619347 : Blo 1277957 1619347 := bstep (se 1 (by rfl) ⟨1214510, by rfl⟩ : syracuseStep 1619347 = 2429021) B2429021
theorem B5182883 : Blo 1277957 5182883 := bstep (se 1 (by rfl) ⟨3887162, by rfl⟩ : syracuseStep 5182883 = 7774325) B7774325
theorem B4314545 : Blo 1277957 4314545 := bstep (se 2 (by rfl) ⟨1617954, by rfl⟩ : syracuseStep 4314545 = 3235909) B3235909
theorem B4609457 : Blo 1277957 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B1439203 : Blo 1277957 1439203 := bstep (se 1 (by rfl) ⟨1079402, by rfl⟩ : syracuseStep 1439203 = 2158805) B2158805
theorem B1619443 : Blo 1277957 1619443 := bstep (se 1 (by rfl) ⟨1214582, by rfl⟩ : syracuseStep 1619443 = 2429165) B2429165
theorem B6911501 : Blo 1277957 6911501 := bstep (se 3 (by rfl) ⟨1295906, by rfl⟩ : syracuseStep 6911501 = 2591813) B2591813
theorem B27637361 : Blo 1277957 27637361 := bstep (se 2 (by rfl) ⟨10364010, by rfl⟩ : syracuseStep 27637361 = 20728021) B20728021
theorem B1439347 : Blo 1277957 1439347 := bstep (se 1 (by rfl) ⟨1079510, by rfl⟩ : syracuseStep 1439347 = 2159021) B2159021
theorem B4675313 : Blo 1277957 4675313 := bstep (se 2 (by rfl) ⟨1753242, by rfl⟩ : syracuseStep 4675313 = 3506485) B3506485
theorem B1439491 : Blo 1277957 1439491 := bstep (se 1 (by rfl) ⟨1079618, by rfl⟩ : syracuseStep 1439491 = 2159237) B2159237
theorem B4855565 : Blo 1277957 4855565 := bstep (se 3 (by rfl) ⟨910418, by rfl⟩ : syracuseStep 4855565 = 1820837) B1820837
theorem B1365859 : Blo 1277957 1365859 := bstep (se 1 (by rfl) ⟨1024394, by rfl⟩ : syracuseStep 1365859 = 2048789) B2048789
theorem B1439635 : Blo 1277957 1439635 := bstep (se 1 (by rfl) ⟨1079726, by rfl⟩ : syracuseStep 1439635 = 2159453) B2159453
theorem B6477731 : Blo 1277957 6477731 := bstep (se 1 (by rfl) ⟨4858298, by rfl⟩ : syracuseStep 6477731 = 9716597) B9716597
theorem B4315085 : Blo 1277957 4315085 := bstep (se 3 (by rfl) ⟨809078, by rfl⟩ : syracuseStep 4315085 = 1618157) B1618157
theorem B1619939 : Blo 1277957 1619939 := bstep (se 1 (by rfl) ⟨1214954, by rfl⟩ : syracuseStep 1619939 = 2429909) B2429909
theorem B2217971 : Blo 1277957 2217971 := bstep (se 1 (by rfl) ⟨1663478, by rfl⟩ : syracuseStep 2217971 = 3326957) B3326957
theorem B4315139 : Blo 1277957 4315139 := bstep (se 1 (by rfl) ⟨3236354, by rfl⟩ : syracuseStep 4315139 = 6472709) B6472709
theorem B1439779 : Blo 1277957 1439779 := bstep (se 1 (by rfl) ⟨1079834, by rfl⟩ : syracuseStep 1439779 = 2159669) B2159669
theorem B1439923 : Blo 1277957 1439923 := bstep (se 1 (by rfl) ⟨1079942, by rfl⟩ : syracuseStep 1439923 = 2159885) B2159885
theorem B8992973 : Blo 1277957 8992973 := bstep (se 3 (by rfl) ⟨1686182, by rfl⟩ : syracuseStep 8992973 = 3372365) B3372365
theorem B8190179 : Blo 1277957 8190179 := bstep (se 1 (by rfl) ⟨6142634, by rfl⟩ : syracuseStep 8190179 = 12285269) B12285269
theorem B3643633 : Blo 1277957 3643633 := bstep (se 2 (by rfl) ⟨1366362, by rfl⟩ : syracuseStep 3643633 = 2732725) B2732725
theorem B4315409 : Blo 1277957 4315409 := bstep (se 2 (by rfl) ⟨1618278, by rfl⟩ : syracuseStep 4315409 = 3236557) B3236557
theorem B26261813 : Blo 1277957 26261813 := bstep (se 5 (by rfl) ⟨1231022, by rfl⟩ : syracuseStep 26261813 = 2462045) B2462045
theorem B10918597 : Blo 1277957 10918597 := bstep (se 4 (by rfl) ⟨1023618, by rfl⟩ : syracuseStep 10918597 = 2047237) B2047237
theorem B6478541 : Blo 1277957 6478541 := bstep (se 3 (by rfl) ⟨1214726, by rfl⟩ : syracuseStep 6478541 = 2429453) B2429453
theorem B3070723 : Blo 1277957 3070723 := bstep (se 1 (by rfl) ⟨2303042, by rfl⟩ : syracuseStep 3070723 = 4606085) B4606085
theorem B7281413 : Blo 1277957 7281413 := bstep (se 4 (by rfl) ⟨682632, by rfl⟩ : syracuseStep 7281413 = 1365265) B1365265
theorem B1727249 : Blo 1277957 1727249 := bstep (se 2 (by rfl) ⟨647718, by rfl⟩ : syracuseStep 1727249 = 1295437) B1295437
theorem B7289635 : Blo 1277957 7289635 := bstep (se 1 (by rfl) ⟨5467226, by rfl⟩ : syracuseStep 7289635 = 10934453) B10934453
theorem B4315949 : Blo 1277957 4315949 := bstep (se 3 (by rfl) ⟨809240, by rfl⟩ : syracuseStep 4315949 = 1618481) B1618481
theorem B4316003 : Blo 1277957 4316003 := bstep (se 1 (by rfl) ⟨3237002, by rfl⟩ : syracuseStep 4316003 = 6474005) B6474005
theorem B1727411 : Blo 1277957 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B12286961 : Blo 1277957 12286961 := bstep (se 2 (by rfl) ⟨4607610, by rfl⟩ : syracuseStep 12286961 = 9215221) B9215221
theorem B56835125 : Blo 1277957 56835125 := bstep (se 5 (by rfl) ⟨2664146, by rfl⟩ : syracuseStep 56835125 = 5328293) B5328293
theorem B4316273 : Blo 1277957 4316273 := bstep (se 2 (by rfl) ⟨1618602, by rfl⟩ : syracuseStep 4316273 = 3237205) B3237205
theorem B10927345 : Blo 1277957 10927345 := bstep (se 2 (by rfl) ⟨4097754, by rfl⟩ : syracuseStep 10927345 = 8195509) B8195509
theorem B2047283 : Blo 1277957 2047283 := bstep (se 1 (by rfl) ⟨1535462, by rfl⟩ : syracuseStep 2047283 = 3070925) B3070925
theorem B4668785 : Blo 1277957 4668785 := bstep (se 2 (by rfl) ⟨1750794, by rfl⟩ : syracuseStep 4668785 = 3501589) B3501589
theorem B4152721 : Blo 1277957 4152721 := bstep (se 2 (by rfl) ⟨1557270, by rfl⟩ : syracuseStep 4152721 = 3114541) B3114541
theorem B6471089 : Blo 1277957 6471089 := bstep (se 2 (by rfl) ⟨2426658, by rfl⟩ : syracuseStep 6471089 = 4853317) B4853317
theorem B1728001 : Blo 1277957 1728001 := bstep (se 2 (by rfl) ⟨648000, by rfl⟩ : syracuseStep 1728001 = 1296001) B1296001
theorem B4095629 : Blo 1277957 4095629 := bstep (se 3 (by rfl) ⟨767930, by rfl⟩ : syracuseStep 4095629 = 1535861) B1535861
theorem B4316813 : Blo 1277957 4316813 := bstep (se 3 (by rfl) ⟨809402, by rfl⟩ : syracuseStep 4316813 = 1618805) B1618805
theorem B4316867 : Blo 1277957 4316867 := bstep (se 1 (by rfl) ⟨3237650, by rfl⟩ : syracuseStep 4316867 = 6475301) B6475301
theorem B4857677 : Blo 1277957 4857677 := bstep (se 3 (by rfl) ⟨910814, by rfl⟩ : syracuseStep 4857677 = 1821629) B1821629
theorem B9707363 : Blo 1277957 9707363 := bstep (se 1 (by rfl) ⟨7280522, by rfl⟩ : syracuseStep 9707363 = 14561045) B14561045
theorem B3456877 : Blo 1277957 3456877 := bstep (se 3 (by rfl) ⟨648164, by rfl⟩ : syracuseStep 3456877 = 1296329) B1296329
theorem B3235697 : Blo 1277957 3235697 := bstep (se 2 (by rfl) ⟨1213386, by rfl⟩ : syracuseStep 3235697 = 2426773) B2426773
theorem B3694481 : Blo 1277957 3694481 := bstep (se 2 (by rfl) ⟨1385430, by rfl⟩ : syracuseStep 3694481 = 2770861) B2770861
theorem B3235747 : Blo 1277957 3235747 := bstep (se 1 (by rfl) ⟨2426810, by rfl⟩ : syracuseStep 3235747 = 4853621) B4853621
theorem B4374481 : Blo 1277957 4374481 := bstep (se 2 (by rfl) ⟨1640430, by rfl⟩ : syracuseStep 4374481 = 3280861) B3280861
theorem B4317137 : Blo 1277957 4317137 := bstep (se 2 (by rfl) ⟨1618926, by rfl⟩ : syracuseStep 4317137 = 3237853) B3237853
theorem B1277963 : Blo 1277957 1277963 := bstep (se 1 (by rfl) ⟨958472, by rfl⟩ : syracuseStep 1277963 = 1916945) B1916945
theorem B1916939 : Blo 1277957 1916939 := bstep (se 1 (by rfl) ⟨1437704, by rfl⟩ : syracuseStep 1916939 = 2875409) B2875409
theorem B8306705 : Blo 1277957 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B1277975 : Blo 1277957 1277975 := bstep (se 1 (by rfl) ⟨958481, by rfl⟩ : syracuseStep 1277975 = 1916963) B1916963
theorem B1916951 : Blo 1277957 1916951 := bstep (se 1 (by rfl) ⟨1437713, by rfl⟩ : syracuseStep 1916951 = 2875427) B2875427
theorem B3891223 : Blo 1277957 3891223 := bstep (se 1 (by rfl) ⟨2918417, by rfl⟩ : syracuseStep 3891223 = 5836835) B5836835
theorem B1277995 : Blo 1277957 1277995 := bstep (se 1 (by rfl) ⟨958496, by rfl⟩ : syracuseStep 1277995 = 1916993) B1916993
theorem B5832749 : Blo 1277957 5832749 := bstep (se 3 (by rfl) ⟨1093640, by rfl⟩ : syracuseStep 5832749 = 2187281) B2187281
theorem B1278007 : Blo 1277957 1278007 := bstep (se 1 (by rfl) ⟨958505, by rfl⟩ : syracuseStep 1278007 = 1917011) B1917011
theorem B7004225 : Blo 1277957 7004225 := bstep (se 2 (by rfl) ⟨2626584, by rfl⟩ : syracuseStep 7004225 = 5253169) B5253169
theorem B1278027 : Blo 1277957 1278027 := bstep (se 1 (by rfl) ⟨958520, by rfl⟩ : syracuseStep 1278027 = 1917041) B1917041
theorem B1278039 : Blo 1277957 1278039 := bstep (se 1 (by rfl) ⟨958529, by rfl⟩ : syracuseStep 1278039 = 1917059) B1917059
theorem B2875481 : Blo 1277957 2875481 := bstep (se 2 (by rfl) ⟨1078305, by rfl⟩ : syracuseStep 2875481 = 2156611) B2156611
theorem B1917017 : Blo 1277957 1917017 := bstep (se 2 (by rfl) ⟨718881, by rfl⟩ : syracuseStep 1917017 = 1437763) B1437763
theorem B1278059 : Blo 1277957 1278059 := bstep (se 1 (by rfl) ⟨958544, by rfl⟩ : syracuseStep 1278059 = 1917089) B1917089
theorem B1278071 : Blo 1277957 1278071 := bstep (se 1 (by rfl) ⟨958553, by rfl⟩ : syracuseStep 1278071 = 1917107) B1917107
theorem B1278091 : Blo 1277957 1278091 := bstep (se 1 (by rfl) ⟨958568, by rfl⟩ : syracuseStep 1278091 = 1917137) B1917137
theorem B1278103 : Blo 1277957 1278103 := bstep (se 1 (by rfl) ⟨958577, by rfl⟩ : syracuseStep 1278103 = 1917155) B1917155
theorem B1278123 : Blo 1277957 1278123 := bstep (se 1 (by rfl) ⟨958592, by rfl⟩ : syracuseStep 1278123 = 1917185) B1917185
theorem B2875571 : Blo 1277957 2875571 := bstep (se 1 (by rfl) ⟨2156678, by rfl⟩ : syracuseStep 2875571 = 4313357) B4313357
theorem B1278135 : Blo 1277957 1278135 := bstep (se 1 (by rfl) ⟨958601, by rfl⟩ : syracuseStep 1278135 = 1917203) B1917203
theorem B1917131 : Blo 1277957 1917131 := bstep (se 1 (by rfl) ⟨1437848, by rfl⟩ : syracuseStep 1917131 = 2875697) B2875697
theorem B1278155 : Blo 1277957 1278155 := bstep (se 1 (by rfl) ⟨958616, by rfl⟩ : syracuseStep 1278155 = 1917233) B1917233
theorem B2875607 : Blo 1277957 2875607 := bstep (se 1 (by rfl) ⟨2156705, by rfl⟩ : syracuseStep 2875607 = 4313411) B4313411
theorem B1917143 : Blo 1277957 1917143 := bstep (se 1 (by rfl) ⟨1437857, by rfl⟩ : syracuseStep 1917143 = 2875715) B2875715
theorem B1278167 : Blo 1277957 1278167 := bstep (se 1 (by rfl) ⟨958625, by rfl⟩ : syracuseStep 1278167 = 1917251) B1917251
theorem B4096217 : Blo 1277957 4096217 := bstep (se 2 (by rfl) ⟨1536081, by rfl⟩ : syracuseStep 4096217 = 3072163) B3072163
theorem B1278187 : Blo 1277957 1278187 := bstep (se 1 (by rfl) ⟨958640, by rfl⟩ : syracuseStep 1278187 = 1917281) B1917281
theorem B1278199 : Blo 1277957 1278199 := bstep (se 1 (by rfl) ⟨958649, by rfl⟩ : syracuseStep 1278199 = 1917299) B1917299
theorem B1278219 : Blo 1277957 1278219 := bstep (se 1 (by rfl) ⟨958664, by rfl⟩ : syracuseStep 1278219 = 1917329) B1917329
theorem B1458443 : Blo 1277957 1458443 := bstep (se 1 (by rfl) ⟨1093832, by rfl⟩ : syracuseStep 1458443 = 2187665) B2187665
theorem B1278231 : Blo 1277957 1278231 := bstep (se 1 (by rfl) ⟨958673, by rfl⟩ : syracuseStep 1278231 = 1917347) B1917347
theorem B1917209 : Blo 1277957 1917209 := bstep (se 2 (by rfl) ⟨718953, by rfl⟩ : syracuseStep 1917209 = 1437907) B1437907
theorem B1278251 : Blo 1277957 1278251 := bstep (se 1 (by rfl) ⟨958688, by rfl⟩ : syracuseStep 1278251 = 1917377) B1917377
theorem B4858163 : Blo 1277957 4858163 := bstep (se 1 (by rfl) ⟨3643622, by rfl⟩ : syracuseStep 4858163 = 7287245) B7287245
theorem B1278263 : Blo 1277957 1278263 := bstep (se 1 (by rfl) ⟨958697, by rfl⟩ : syracuseStep 1278263 = 1917395) B1917395
theorem B4858177 : Blo 1277957 4858177 := bstep (se 2 (by rfl) ⟨1821816, by rfl⟩ : syracuseStep 4858177 = 3643633) B3643633
theorem B1278283 : Blo 1277957 1278283 := bstep (se 1 (by rfl) ⟨958712, by rfl⟩ : syracuseStep 1278283 = 1917425) B1917425
theorem B4317515 : Blo 1277957 4317515 := bstep (se 1 (by rfl) ⟨3238136, by rfl⟩ : syracuseStep 4317515 = 6476273) B6476273
theorem B1278295 : Blo 1277957 1278295 := bstep (se 1 (by rfl) ⟨958721, by rfl⟩ : syracuseStep 1278295 = 1917443) B1917443
theorem B1278315 : Blo 1277957 1278315 := bstep (se 1 (by rfl) ⟨958736, by rfl⟩ : syracuseStep 1278315 = 1917473) B1917473
theorem B1278327 : Blo 1277957 1278327 := bstep (se 1 (by rfl) ⟨958745, by rfl⟩ : syracuseStep 1278327 = 1917491) B1917491
theorem B2875787 : Blo 1277957 2875787 := bstep (se 1 (by rfl) ⟨2156840, by rfl⟩ : syracuseStep 2875787 = 4313681) B4313681
theorem B1917323 : Blo 1277957 1917323 := bstep (se 1 (by rfl) ⟨1437992, by rfl⟩ : syracuseStep 1917323 = 2875985) B2875985
theorem B1278347 : Blo 1277957 1278347 := bstep (se 1 (by rfl) ⟨958760, by rfl⟩ : syracuseStep 1278347 = 1917521) B1917521
theorem B1917335 : Blo 1277957 1917335 := bstep (se 1 (by rfl) ⟨1438001, by rfl⟩ : syracuseStep 1917335 = 2876003) B2876003
theorem B1278359 : Blo 1277957 1278359 := bstep (se 1 (by rfl) ⟨958769, by rfl⟩ : syracuseStep 1278359 = 1917539) B1917539
theorem B1278379 : Blo 1277957 1278379 := bstep (se 1 (by rfl) ⟨958784, by rfl⟩ : syracuseStep 1278379 = 1917569) B1917569
theorem B5464493 : Blo 1277957 5464493 := bstep (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) B2049185
theorem B1278391 : Blo 1277957 1278391 := bstep (se 1 (by rfl) ⟨958793, by rfl⟩ : syracuseStep 1278391 = 1917587) B1917587
theorem B2875841 : Blo 1277957 2875841 := bstep (se 2 (by rfl) ⟨1078440, by rfl⟩ : syracuseStep 2875841 = 2156881) B2156881
theorem B1278411 : Blo 1277957 1278411 := bstep (se 1 (by rfl) ⟨958808, by rfl⟩ : syracuseStep 1278411 = 1917617) B1917617
theorem B1278423 : Blo 1277957 1278423 := bstep (se 1 (by rfl) ⟨958817, by rfl⟩ : syracuseStep 1278423 = 1917635) B1917635
theorem B1917401 : Blo 1277957 1917401 := bstep (se 2 (by rfl) ⟨719025, by rfl⟩ : syracuseStep 1917401 = 1438051) B1438051
theorem B1278443 : Blo 1277957 1278443 := bstep (se 1 (by rfl) ⟨958832, by rfl⟩ : syracuseStep 1278443 = 1917665) B1917665
theorem B1278455 : Blo 1277957 1278455 := bstep (se 1 (by rfl) ⟨958841, by rfl⟩ : syracuseStep 1278455 = 1917683) B1917683
theorem B1278475 : Blo 1277957 1278475 := bstep (se 1 (by rfl) ⟨958856, by rfl⟩ : syracuseStep 1278475 = 1917713) B1917713
theorem B1278487 : Blo 1277957 1278487 := bstep (se 1 (by rfl) ⟨958865, by rfl⟩ : syracuseStep 1278487 = 1917731) B1917731
theorem B3236375 : Blo 1277957 3236375 := bstep (se 1 (by rfl) ⟨2427281, by rfl⟩ : syracuseStep 3236375 = 4854563) B4854563
theorem B3457559 : Blo 1277957 3457559 := bstep (se 1 (by rfl) ⟨2593169, by rfl⟩ : syracuseStep 3457559 = 5186339) B5186339
theorem B1278507 : Blo 1277957 1278507 := bstep (se 1 (by rfl) ⟨958880, by rfl⟩ : syracuseStep 1278507 = 1917761) B1917761
theorem B1278519 : Blo 1277957 1278519 := bstep (se 1 (by rfl) ⟨958889, by rfl⟩ : syracuseStep 1278519 = 1917779) B1917779
theorem B1917515 : Blo 1277957 1917515 := bstep (se 1 (by rfl) ⟨1438136, by rfl⟩ : syracuseStep 1917515 = 2876273) B2876273
theorem B1278539 : Blo 1277957 1278539 := bstep (se 1 (by rfl) ⟨958904, by rfl⟩ : syracuseStep 1278539 = 1917809) B1917809
theorem B4497995 : Blo 1277957 4497995 := bstep (se 1 (by rfl) ⟨3373496, by rfl⟩ : syracuseStep 4497995 = 6746993) B6746993
theorem B1917527 : Blo 1277957 1917527 := bstep (se 1 (by rfl) ⟨1438145, by rfl⟩ : syracuseStep 1917527 = 2876291) B2876291
theorem B1278551 : Blo 1277957 1278551 := bstep (se 1 (by rfl) ⟨958913, by rfl⟩ : syracuseStep 1278551 = 1917827) B1917827
theorem B4317785 : Blo 1277957 4317785 := bstep (se 2 (by rfl) ⟨1619169, by rfl⟩ : syracuseStep 4317785 = 3238339) B3238339
theorem B1278571 : Blo 1277957 1278571 := bstep (se 1 (by rfl) ⟨958928, by rfl⟩ : syracuseStep 1278571 = 1917857) B1917857
theorem B1278583 : Blo 1277957 1278583 := bstep (se 1 (by rfl) ⟨958937, by rfl⟩ : syracuseStep 1278583 = 1917875) B1917875
theorem B1278603 : Blo 1277957 1278603 := bstep (se 1 (by rfl) ⟨958952, by rfl⟩ : syracuseStep 1278603 = 1917905) B1917905
theorem B1278615 : Blo 1277957 1278615 := bstep (se 1 (by rfl) ⟨958961, by rfl⟩ : syracuseStep 1278615 = 1917923) B1917923
theorem B2876057 : Blo 1277957 2876057 := bstep (se 2 (by rfl) ⟨1078521, by rfl⟩ : syracuseStep 2876057 = 2157043) B2157043
theorem B1917593 : Blo 1277957 1917593 := bstep (se 2 (by rfl) ⟨719097, by rfl⟩ : syracuseStep 1917593 = 1438195) B1438195
theorem B1278635 : Blo 1277957 1278635 := bstep (se 1 (by rfl) ⟨958976, by rfl⟩ : syracuseStep 1278635 = 1917953) B1917953
theorem B23331509 : Blo 1277957 23331509 := bstep (se 5 (by rfl) ⟨1093664, by rfl⟩ : syracuseStep 23331509 = 2187329) B2187329
theorem B1278647 : Blo 1277957 1278647 := bstep (se 1 (by rfl) ⟨958985, by rfl⟩ : syracuseStep 1278647 = 1917971) B1917971
theorem B1278667 : Blo 1277957 1278667 := bstep (se 1 (by rfl) ⟨959000, by rfl⟩ : syracuseStep 1278667 = 1918001) B1918001
theorem B1278679 : Blo 1277957 1278679 := bstep (se 1 (by rfl) ⟨959009, by rfl⟩ : syracuseStep 1278679 = 1918019) B1918019
theorem B3891929 : Blo 1277957 3891929 := bstep (se 2 (by rfl) ⟨1459473, by rfl⟩ : syracuseStep 3891929 = 2918947) B2918947
theorem B1278699 : Blo 1277957 1278699 := bstep (se 1 (by rfl) ⟨959024, by rfl⟩ : syracuseStep 1278699 = 1918049) B1918049
theorem B2876147 : Blo 1277957 2876147 := bstep (se 1 (by rfl) ⟨2157110, by rfl⟩ : syracuseStep 2876147 = 4314221) B4314221
theorem B1278711 : Blo 1277957 1278711 := bstep (se 1 (by rfl) ⟨959033, by rfl⟩ : syracuseStep 1278711 = 1918067) B1918067
theorem B1917707 : Blo 1277957 1917707 := bstep (se 1 (by rfl) ⟨1438280, by rfl⟩ : syracuseStep 1917707 = 2876561) B2876561
theorem B1278731 : Blo 1277957 1278731 := bstep (se 1 (by rfl) ⟨959048, by rfl⟩ : syracuseStep 1278731 = 1918097) B1918097
theorem B2876183 : Blo 1277957 2876183 := bstep (se 1 (by rfl) ⟨2157137, by rfl⟩ : syracuseStep 2876183 = 4314275) B4314275
theorem B1917719 : Blo 1277957 1917719 := bstep (se 1 (by rfl) ⟨1438289, by rfl⟩ : syracuseStep 1917719 = 2876579) B2876579
theorem B1278743 : Blo 1277957 1278743 := bstep (se 1 (by rfl) ⟨959057, by rfl⟩ : syracuseStep 1278743 = 1918115) B1918115
theorem B1278763 : Blo 1277957 1278763 := bstep (se 1 (by rfl) ⟨959072, by rfl⟩ : syracuseStep 1278763 = 1918145) B1918145
theorem B59081525 : Blo 1277957 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B1278775 : Blo 1277957 1278775 := bstep (se 1 (by rfl) ⟨959081, by rfl⟩ : syracuseStep 1278775 = 1918163) B1918163
theorem B1278795 : Blo 1277957 1278795 := bstep (se 1 (by rfl) ⟨959096, by rfl⟩ : syracuseStep 1278795 = 1918193) B1918193
theorem B1278807 : Blo 1277957 1278807 := bstep (se 1 (by rfl) ⟨959105, by rfl⟩ : syracuseStep 1278807 = 1918211) B1918211
theorem B1917785 : Blo 1277957 1917785 := bstep (se 2 (by rfl) ⟨719169, by rfl⟩ : syracuseStep 1917785 = 1438339) B1438339
theorem B1278827 : Blo 1277957 1278827 := bstep (se 1 (by rfl) ⟨959120, by rfl⟩ : syracuseStep 1278827 = 1918241) B1918241
theorem B1278839 : Blo 1277957 1278839 := bstep (se 1 (by rfl) ⟨959129, by rfl⟩ : syracuseStep 1278839 = 1918259) B1918259
theorem B1459063 : Blo 1277957 1459063 := bstep (se 1 (by rfl) ⟨1094297, by rfl⟩ : syracuseStep 1459063 = 2188595) B2188595
theorem B1278859 : Blo 1277957 1278859 := bstep (se 1 (by rfl) ⟨959144, by rfl⟩ : syracuseStep 1278859 = 1918289) B1918289
theorem B1278871 : Blo 1277957 1278871 := bstep (se 1 (by rfl) ⟨959153, by rfl⟩ : syracuseStep 1278871 = 1918307) B1918307
theorem B1278891 : Blo 1277957 1278891 := bstep (se 1 (by rfl) ⟨959168, by rfl⟩ : syracuseStep 1278891 = 1918337) B1918337
theorem B14558129 : Blo 1277957 14558129 := bstep (se 2 (by rfl) ⟨5459298, by rfl⟩ : syracuseStep 14558129 = 10918597) B10918597
theorem B8192947 : Blo 1277957 8192947 := bstep (se 1 (by rfl) ⟨6144710, by rfl⟩ : syracuseStep 8192947 = 12289421) B12289421
theorem B1278903 : Blo 1277957 1278903 := bstep (se 1 (by rfl) ⟨959177, by rfl⟩ : syracuseStep 1278903 = 1918355) B1918355
theorem B2876363 : Blo 1277957 2876363 := bstep (se 1 (by rfl) ⟨2157272, by rfl⟩ : syracuseStep 2876363 = 4314545) B4314545
theorem B1917899 : Blo 1277957 1917899 := bstep (se 1 (by rfl) ⟨1438424, by rfl⟩ : syracuseStep 1917899 = 2876849) B2876849
theorem B1278923 : Blo 1277957 1278923 := bstep (se 1 (by rfl) ⟨959192, by rfl⟩ : syracuseStep 1278923 = 1918385) B1918385
theorem B3072971 : Blo 1277957 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B1917911 : Blo 1277957 1917911 := bstep (se 1 (by rfl) ⟨1438433, by rfl⟩ : syracuseStep 1917911 = 2876867) B2876867
theorem B1278935 : Blo 1277957 1278935 := bstep (se 1 (by rfl) ⟨959201, by rfl⟩ : syracuseStep 1278935 = 1918403) B1918403
theorem B1278955 : Blo 1277957 1278955 := bstep (se 1 (by rfl) ⟨959216, by rfl⟩ : syracuseStep 1278955 = 1918433) B1918433
theorem B1278967 : Blo 1277957 1278967 := bstep (se 1 (by rfl) ⟨959225, by rfl⟩ : syracuseStep 1278967 = 1918451) B1918451
theorem B2876417 : Blo 1277957 2876417 := bstep (se 2 (by rfl) ⟨1078656, by rfl⟩ : syracuseStep 2876417 = 2157313) B2157313
theorem B1278987 : Blo 1277957 1278987 := bstep (se 1 (by rfl) ⟨959240, by rfl⟩ : syracuseStep 1278987 = 1918481) B1918481
theorem B1278999 : Blo 1277957 1278999 := bstep (se 1 (by rfl) ⟨959249, by rfl⟩ : syracuseStep 1278999 = 1918499) B1918499
theorem B1917977 : Blo 1277957 1917977 := bstep (se 2 (by rfl) ⟨719241, by rfl⟩ : syracuseStep 1917977 = 1438483) B1438483
theorem B1279019 : Blo 1277957 1279019 := bstep (se 1 (by rfl) ⟨959264, by rfl⟩ : syracuseStep 1279019 = 1918529) B1918529
theorem B10363949 : Blo 1277957 10363949 := bstep (se 3 (by rfl) ⟨1943240, by rfl⟩ : syracuseStep 10363949 = 3886481) B3886481
theorem B1279031 : Blo 1277957 1279031 := bstep (se 1 (by rfl) ⟨959273, by rfl⟩ : syracuseStep 1279031 = 1918547) B1918547
theorem B18424907 : Blo 1277957 18424907 := bstep (se 1 (by rfl) ⟨13818680, by rfl⟩ : syracuseStep 18424907 = 27637361) B27637361
theorem B1279051 : Blo 1277957 1279051 := bstep (se 1 (by rfl) ⟨959288, by rfl⟩ : syracuseStep 1279051 = 1918577) B1918577
theorem B1279063 : Blo 1277957 1279063 := bstep (se 1 (by rfl) ⟨959297, by rfl⟩ : syracuseStep 1279063 = 1918595) B1918595
theorem B5465177 : Blo 1277957 5465177 := bstep (se 2 (by rfl) ⟨2049441, by rfl⟩ : syracuseStep 5465177 = 4098883) B4098883
theorem B1279083 : Blo 1277957 1279083 := bstep (se 1 (by rfl) ⟨959312, by rfl⟩ : syracuseStep 1279083 = 1918625) B1918625
theorem B1279095 : Blo 1277957 1279095 := bstep (se 1 (by rfl) ⟨959321, by rfl⟩ : syracuseStep 1279095 = 1918643) B1918643
theorem B1918091 : Blo 1277957 1918091 := bstep (se 1 (by rfl) ⟨1438568, by rfl⟩ : syracuseStep 1918091 = 2877137) B2877137
theorem B1279115 : Blo 1277957 1279115 := bstep (se 1 (by rfl) ⟨959336, by rfl⟩ : syracuseStep 1279115 = 1918673) B1918673
theorem B1918103 : Blo 1277957 1918103 := bstep (se 1 (by rfl) ⟨1438577, by rfl⟩ : syracuseStep 1918103 = 2877155) B2877155
theorem B1279127 : Blo 1277957 1279127 := bstep (se 1 (by rfl) ⟨959345, by rfl⟩ : syracuseStep 1279127 = 1918691) B1918691
theorem B1279147 : Blo 1277957 1279147 := bstep (se 1 (by rfl) ⟨959360, by rfl⟩ : syracuseStep 1279147 = 1918721) B1918721
theorem B10929329 : Blo 1277957 10929329 := bstep (se 2 (by rfl) ⟨4098498, by rfl⟩ : syracuseStep 10929329 = 8196997) B8196997
theorem B3237043 : Blo 1277957 3237043 := bstep (se 1 (by rfl) ⟨2427782, by rfl⟩ : syracuseStep 3237043 = 4855565) B4855565
theorem B1279159 : Blo 1277957 1279159 := bstep (se 1 (by rfl) ⟨959369, by rfl⟩ : syracuseStep 1279159 = 1918739) B1918739
theorem B1279179 : Blo 1277957 1279179 := bstep (se 1 (by rfl) ⟨959384, by rfl⟩ : syracuseStep 1279179 = 1918769) B1918769
theorem B1279191 : Blo 1277957 1279191 := bstep (se 1 (by rfl) ⟨959393, by rfl⟩ : syracuseStep 1279191 = 1918787) B1918787
theorem B2876633 : Blo 1277957 2876633 := bstep (se 2 (by rfl) ⟨1078737, by rfl⟩ : syracuseStep 2876633 = 2157475) B2157475
theorem B1918169 : Blo 1277957 1918169 := bstep (se 2 (by rfl) ⟨719313, by rfl⟩ : syracuseStep 1918169 = 1438627) B1438627
theorem B1279211 : Blo 1277957 1279211 := bstep (se 1 (by rfl) ⟨959408, by rfl⟩ : syracuseStep 1279211 = 1918817) B1918817
theorem B1279223 : Blo 1277957 1279223 := bstep (se 1 (by rfl) ⟨959417, by rfl⟩ : syracuseStep 1279223 = 1918835) B1918835
theorem B1279243 : Blo 1277957 1279243 := bstep (se 1 (by rfl) ⟨959432, by rfl⟩ : syracuseStep 1279243 = 1918865) B1918865
theorem B1279255 : Blo 1277957 1279255 := bstep (se 1 (by rfl) ⟨959441, by rfl⟩ : syracuseStep 1279255 = 1918883) B1918883
theorem B4318487 : Blo 1277957 4318487 := bstep (se 1 (by rfl) ⟨3238865, by rfl⟩ : syracuseStep 4318487 = 6477731) B6477731
theorem B1279275 : Blo 1277957 1279275 := bstep (se 1 (by rfl) ⟨959456, by rfl⟩ : syracuseStep 1279275 = 1918913) B1918913
theorem B2876723 : Blo 1277957 2876723 := bstep (se 1 (by rfl) ⟨2157542, by rfl⟩ : syracuseStep 2876723 = 4315085) B4315085
theorem B1279287 : Blo 1277957 1279287 := bstep (se 1 (by rfl) ⟨959465, by rfl⟩ : syracuseStep 1279287 = 1918931) B1918931
theorem B3237185 : Blo 1277957 3237185 := bstep (se 2 (by rfl) ⟨1213944, by rfl⟩ : syracuseStep 3237185 = 2427889) B2427889
theorem B1918283 : Blo 1277957 1918283 := bstep (se 1 (by rfl) ⟨1438712, by rfl⟩ : syracuseStep 1918283 = 2877425) B2877425
theorem B1279307 : Blo 1277957 1279307 := bstep (se 1 (by rfl) ⟨959480, by rfl⟩ : syracuseStep 1279307 = 1918961) B1918961
theorem B2876759 : Blo 1277957 2876759 := bstep (se 1 (by rfl) ⟨2157569, by rfl⟩ : syracuseStep 2876759 = 4315139) B4315139
theorem B1918295 : Blo 1277957 1918295 := bstep (se 1 (by rfl) ⟨1438721, by rfl⟩ : syracuseStep 1918295 = 2877443) B2877443
theorem B1279319 : Blo 1277957 1279319 := bstep (se 1 (by rfl) ⟨959489, by rfl⟩ : syracuseStep 1279319 = 1918979) B1918979
theorem B1279339 : Blo 1277957 1279339 := bstep (se 1 (by rfl) ⟨959504, by rfl⟩ : syracuseStep 1279339 = 1919009) B1919009
theorem B1279351 : Blo 1277957 1279351 := bstep (se 1 (by rfl) ⟨959513, by rfl⟩ : syracuseStep 1279351 = 1919027) B1919027
theorem B1279371 : Blo 1277957 1279371 := bstep (se 1 (by rfl) ⟨959528, by rfl⟩ : syracuseStep 1279371 = 1919057) B1919057
theorem B1279383 : Blo 1277957 1279383 := bstep (se 1 (by rfl) ⟨959537, by rfl⟩ : syracuseStep 1279383 = 1919075) B1919075
theorem B1918361 : Blo 1277957 1918361 := bstep (se 2 (by rfl) ⟨719385, by rfl⟩ : syracuseStep 1918361 = 1438771) B1438771
theorem B1279403 : Blo 1277957 1279403 := bstep (se 1 (by rfl) ⟨959552, by rfl⟩ : syracuseStep 1279403 = 1919105) B1919105
theorem B1279415 : Blo 1277957 1279415 := bstep (se 1 (by rfl) ⟨959561, by rfl⟩ : syracuseStep 1279415 = 1919123) B1919123
theorem B2917835 : Blo 1277957 2917835 := bstep (se 1 (by rfl) ⟨2188376, by rfl⟩ : syracuseStep 2917835 = 4376753) B4376753
theorem B1279435 : Blo 1277957 1279435 := bstep (se 1 (by rfl) ⟨959576, by rfl⟩ : syracuseStep 1279435 = 1919153) B1919153
theorem B1279447 : Blo 1277957 1279447 := bstep (se 1 (by rfl) ⟨959585, by rfl⟩ : syracuseStep 1279447 = 1919171) B1919171
theorem B1279467 : Blo 1277957 1279467 := bstep (se 1 (by rfl) ⟨959600, by rfl⟩ : syracuseStep 1279467 = 1919201) B1919201
theorem B1279479 : Blo 1277957 1279479 := bstep (se 1 (by rfl) ⟨959609, by rfl⟩ : syracuseStep 1279479 = 1919219) B1919219
theorem B1820171 : Blo 1277957 1820171 := bstep (se 1 (by rfl) ⟨1365128, by rfl⟩ : syracuseStep 1820171 = 2730257) B2730257
theorem B2876939 : Blo 1277957 2876939 := bstep (se 1 (by rfl) ⟨2157704, by rfl⟩ : syracuseStep 2876939 = 4315409) B4315409
theorem B1918475 : Blo 1277957 1918475 := bstep (se 1 (by rfl) ⟨1438856, by rfl⟩ : syracuseStep 1918475 = 2877713) B2877713
theorem B1279499 : Blo 1277957 1279499 := bstep (se 1 (by rfl) ⟨959624, by rfl⟩ : syracuseStep 1279499 = 1919249) B1919249
theorem B1918487 : Blo 1277957 1918487 := bstep (se 1 (by rfl) ⟨1438865, by rfl⟩ : syracuseStep 1918487 = 2877731) B2877731
theorem B1279511 : Blo 1277957 1279511 := bstep (se 1 (by rfl) ⟨959633, by rfl⟩ : syracuseStep 1279511 = 1919267) B1919267
theorem B17507875 : Blo 1277957 17507875 := bstep (se 1 (by rfl) ⟨13130906, by rfl⟩ : syracuseStep 17507875 = 26261813) B26261813
theorem B1279531 : Blo 1277957 1279531 := bstep (se 1 (by rfl) ⟨959648, by rfl⟩ : syracuseStep 1279531 = 1919297) B1919297
theorem B1279543 : Blo 1277957 1279543 := bstep (se 1 (by rfl) ⟨959657, by rfl⟩ : syracuseStep 1279543 = 1919315) B1919315
theorem B2876993 : Blo 1277957 2876993 := bstep (se 2 (by rfl) ⟨1078872, by rfl⟩ : syracuseStep 2876993 = 2157745) B2157745
theorem B1279563 : Blo 1277957 1279563 := bstep (se 1 (by rfl) ⟨959672, by rfl⟩ : syracuseStep 1279563 = 1919345) B1919345
theorem B1279575 : Blo 1277957 1279575 := bstep (se 1 (by rfl) ⟨959681, by rfl⟩ : syracuseStep 1279575 = 1919363) B1919363
theorem B1918553 : Blo 1277957 1918553 := bstep (se 2 (by rfl) ⟨719457, by rfl⟩ : syracuseStep 1918553 = 1438915) B1438915
theorem B1279595 : Blo 1277957 1279595 := bstep (se 1 (by rfl) ⟨959696, by rfl⟩ : syracuseStep 1279595 = 1919393) B1919393
theorem B1279607 : Blo 1277957 1279607 := bstep (se 1 (by rfl) ⟨959705, by rfl⟩ : syracuseStep 1279607 = 1919411) B1919411
theorem B4671107 : Blo 1277957 4671107 := bstep (se 1 (by rfl) ⟨3503330, by rfl⟩ : syracuseStep 4671107 = 7006661) B7006661
theorem B2426507 : Blo 1277957 2426507 := bstep (se 1 (by rfl) ⟨1819880, by rfl⟩ : syracuseStep 2426507 = 3639761) B3639761
theorem B1279627 : Blo 1277957 1279627 := bstep (se 1 (by rfl) ⟨959720, by rfl⟩ : syracuseStep 1279627 = 1919441) B1919441
theorem B1279639 : Blo 1277957 1279639 := bstep (se 1 (by rfl) ⟨959729, by rfl⟩ : syracuseStep 1279639 = 1919459) B1919459
theorem B1279659 : Blo 1277957 1279659 := bstep (se 1 (by rfl) ⟨959744, by rfl⟩ : syracuseStep 1279659 = 1919489) B1919489
theorem B1279671 : Blo 1277957 1279671 := bstep (se 1 (by rfl) ⟨959753, by rfl⟩ : syracuseStep 1279671 = 1919507) B1919507
theorem B1918667 : Blo 1277957 1918667 := bstep (se 1 (by rfl) ⟨1439000, by rfl⟩ : syracuseStep 1918667 = 2878001) B2878001
theorem B1279691 : Blo 1277957 1279691 := bstep (se 1 (by rfl) ⟨959768, by rfl⟩ : syracuseStep 1279691 = 1919537) B1919537
theorem B1918679 : Blo 1277957 1918679 := bstep (se 1 (by rfl) ⟨1439009, by rfl⟩ : syracuseStep 1918679 = 2878019) B2878019
theorem B1279703 : Blo 1277957 1279703 := bstep (se 1 (by rfl) ⟨959777, by rfl⟩ : syracuseStep 1279703 = 1919555) B1919555
theorem B1279723 : Blo 1277957 1279723 := bstep (se 1 (by rfl) ⟨959792, by rfl⟩ : syracuseStep 1279723 = 1919585) B1919585
theorem B1279735 : Blo 1277957 1279735 := bstep (se 1 (by rfl) ⟨959801, by rfl⟩ : syracuseStep 1279735 = 1919603) B1919603
theorem B1279755 : Blo 1277957 1279755 := bstep (se 1 (by rfl) ⟨959816, by rfl⟩ : syracuseStep 1279755 = 1919633) B1919633
theorem B1279767 : Blo 1277957 1279767 := bstep (se 1 (by rfl) ⟨959825, by rfl⟩ : syracuseStep 1279767 = 1919651) B1919651
theorem B2877209 : Blo 1277957 2877209 := bstep (se 2 (by rfl) ⟨1078953, by rfl⟩ : syracuseStep 2877209 = 2157907) B2157907
theorem B1918745 : Blo 1277957 1918745 := bstep (se 2 (by rfl) ⟨719529, by rfl⟩ : syracuseStep 1918745 = 1439059) B1439059
theorem B1279787 : Blo 1277957 1279787 := bstep (se 1 (by rfl) ⟨959840, by rfl⟩ : syracuseStep 1279787 = 1919681) B1919681
theorem B4319027 : Blo 1277957 4319027 := bstep (se 1 (by rfl) ⟨3239270, by rfl⟩ : syracuseStep 4319027 = 6478541) B6478541
theorem B1279799 : Blo 1277957 1279799 := bstep (se 1 (by rfl) ⟨959849, by rfl⟩ : syracuseStep 1279799 = 1919699) B1919699
theorem B2426689 : Blo 1277957 2426689 := bstep (se 2 (by rfl) ⟨910008, by rfl⟩ : syracuseStep 2426689 = 1820017) B1820017
theorem B9717569 : Blo 1277957 9717569 := bstep (se 2 (by rfl) ⟨3644088, by rfl⟩ : syracuseStep 9717569 = 7288177) B7288177
theorem B1279819 : Blo 1277957 1279819 := bstep (se 1 (by rfl) ⟨959864, by rfl⟩ : syracuseStep 1279819 = 1919729) B1919729
theorem B1279831 : Blo 1277957 1279831 := bstep (se 1 (by rfl) ⟨959873, by rfl⟩ : syracuseStep 1279831 = 1919747) B1919747
theorem B1279851 : Blo 1277957 1279851 := bstep (se 1 (by rfl) ⟨959888, by rfl⟩ : syracuseStep 1279851 = 1919777) B1919777
theorem B2877299 : Blo 1277957 2877299 := bstep (se 1 (by rfl) ⟨2157974, by rfl⟩ : syracuseStep 2877299 = 4315949) B4315949
theorem B18425717 : Blo 1277957 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B1279863 : Blo 1277957 1279863 := bstep (se 1 (by rfl) ⟨959897, by rfl⟩ : syracuseStep 1279863 = 1919795) B1919795
theorem B1918859 : Blo 1277957 1918859 := bstep (se 1 (by rfl) ⟨1439144, by rfl⟩ : syracuseStep 1918859 = 2878289) B2878289
theorem B1279883 : Blo 1277957 1279883 := bstep (se 1 (by rfl) ⟨959912, by rfl⟩ : syracuseStep 1279883 = 1919825) B1919825
theorem B2877335 : Blo 1277957 2877335 := bstep (se 1 (by rfl) ⟨2158001, by rfl⟩ : syracuseStep 2877335 = 4316003) B4316003
theorem B1918871 : Blo 1277957 1918871 := bstep (se 1 (by rfl) ⟨1439153, by rfl⟩ : syracuseStep 1918871 = 2878307) B2878307
theorem B1279895 : Blo 1277957 1279895 := bstep (se 1 (by rfl) ⟨959921, by rfl⟩ : syracuseStep 1279895 = 1919843) B1919843
theorem B1279915 : Blo 1277957 1279915 := bstep (se 1 (by rfl) ⟨959936, by rfl⟩ : syracuseStep 1279915 = 1919873) B1919873
theorem B1279927 : Blo 1277957 1279927 := bstep (se 1 (by rfl) ⟨959945, by rfl⟩ : syracuseStep 1279927 = 1919891) B1919891
theorem B1279947 : Blo 1277957 1279947 := bstep (se 1 (by rfl) ⟨959960, by rfl⟩ : syracuseStep 1279947 = 1919921) B1919921
theorem B1918937 : Blo 1277957 1918937 := bstep (se 2 (by rfl) ⟨719601, by rfl⟩ : syracuseStep 1918937 = 1439203) B1439203
theorem B2304001 : Blo 1277957 2304001 := bstep (se 2 (by rfl) ⟨864000, by rfl⟩ : syracuseStep 2304001 = 1728001) B1728001
theorem B37890083 : Blo 1277957 37890083 := bstep (se 1 (by rfl) ⟨28417562, by rfl⟩ : syracuseStep 37890083 = 56835125) B56835125
theorem B4605997 : Blo 1277957 4605997 := bstep (se 3 (by rfl) ⟨863624, by rfl⟩ : syracuseStep 4605997 = 1727249) B1727249
theorem B4319297 : Blo 1277957 4319297 := bstep (se 2 (by rfl) ⟨1619736, by rfl⟩ : syracuseStep 4319297 = 3239473) B3239473
theorem B2877515 : Blo 1277957 2877515 := bstep (se 1 (by rfl) ⟨2158136, by rfl⟩ : syracuseStep 2877515 = 4316273) B4316273
theorem B1919051 : Blo 1277957 1919051 := bstep (se 1 (by rfl) ⟨1439288, by rfl⟩ : syracuseStep 1919051 = 2878577) B2878577
theorem B1919063 : Blo 1277957 1919063 := bstep (se 1 (by rfl) ⟨1439297, by rfl⟩ : syracuseStep 1919063 = 2878595) B2878595
theorem B2877569 : Blo 1277957 2877569 := bstep (se 2 (by rfl) ⟨1079088, by rfl⟩ : syracuseStep 2877569 = 2158177) B2158177
theorem B1919129 : Blo 1277957 1919129 := bstep (se 2 (by rfl) ⟨719673, by rfl⟩ : syracuseStep 1919129 = 1439347) B1439347
theorem B5466305 : Blo 1277957 5466305 := bstep (se 2 (by rfl) ⟨2049864, by rfl⟩ : syracuseStep 5466305 = 4099729) B4099729
theorem B1919243 : Blo 1277957 1919243 := bstep (se 1 (by rfl) ⟨1439432, by rfl⟩ : syracuseStep 1919243 = 2878865) B2878865
theorem B1919255 : Blo 1277957 1919255 := bstep (se 1 (by rfl) ⟨1439441, by rfl⟩ : syracuseStep 1919255 = 2878883) B2878883
theorem B5835083 : Blo 1277957 5835083 := bstep (se 1 (by rfl) ⟨4376312, by rfl⟩ : syracuseStep 5835083 = 8752625) B8752625
theorem B2877785 : Blo 1277957 2877785 := bstep (se 2 (by rfl) ⟨1079169, by rfl⟩ : syracuseStep 2877785 = 2158339) B2158339
theorem B1919321 : Blo 1277957 1919321 := bstep (se 2 (by rfl) ⟨719745, by rfl⟩ : syracuseStep 1919321 = 1439491) B1439491
theorem B4098397 : Blo 1277957 4098397 := bstep (se 3 (by rfl) ⟨768449, by rfl⟩ : syracuseStep 4098397 = 1536899) B1536899
theorem B2730419 : Blo 1277957 2730419 := bstep (se 1 (by rfl) ⟨2047814, by rfl⟩ : syracuseStep 2730419 = 4095629) B4095629
theorem B2877875 : Blo 1277957 2877875 := bstep (se 1 (by rfl) ⟨2158406, by rfl⟩ : syracuseStep 2877875 = 4316813) B4316813
theorem B1919435 : Blo 1277957 1919435 := bstep (se 1 (by rfl) ⟨1439576, by rfl⟩ : syracuseStep 1919435 = 2879153) B2879153
theorem B2877911 : Blo 1277957 2877911 := bstep (se 1 (by rfl) ⟨2158433, by rfl⟩ : syracuseStep 2877911 = 4316867) B4316867
theorem B1919447 : Blo 1277957 1919447 := bstep (se 1 (by rfl) ⟨1439585, by rfl⟩ : syracuseStep 1919447 = 2879171) B2879171
theorem B1821145 : Blo 1277957 1821145 := bstep (se 2 (by rfl) ⟨682929, by rfl⟩ : syracuseStep 1821145 = 1365859) B1365859
theorem B2427403 : Blo 1277957 2427403 := bstep (se 1 (by rfl) ⟨1820552, by rfl⟩ : syracuseStep 2427403 = 3641105) B3641105
theorem B1919513 : Blo 1277957 1919513 := bstep (se 2 (by rfl) ⟨719817, by rfl⟩ : syracuseStep 1919513 = 1439635) B1439635
theorem B3238451 : Blo 1277957 3238451 := bstep (se 1 (by rfl) ⟨2428838, by rfl⟩ : syracuseStep 3238451 = 4857677) B4857677
theorem B2157131 : Blo 1277957 2157131 := bstep (se 1 (by rfl) ⟨1617848, by rfl⟩ : syracuseStep 2157131 = 3235697) B3235697
theorem B2427479 : Blo 1277957 2427479 := bstep (se 1 (by rfl) ⟨1820609, by rfl⟩ : syracuseStep 2427479 = 3641219) B3641219
theorem B4319837 : Blo 1277957 4319837 := bstep (se 3 (by rfl) ⟨809969, by rfl⟩ : syracuseStep 4319837 = 1619939) B1619939
theorem B2878091 : Blo 1277957 2878091 := bstep (se 1 (by rfl) ⟨2158568, by rfl⟩ : syracuseStep 2878091 = 4317137) B4317137
theorem B1919627 : Blo 1277957 1919627 := bstep (se 1 (by rfl) ⟨1439720, by rfl⟩ : syracuseStep 1919627 = 2879441) B2879441
theorem B1919639 : Blo 1277957 1919639 := bstep (se 1 (by rfl) ⟨1439729, by rfl⟩ : syracuseStep 1919639 = 2879459) B2879459
theorem B2878145 : Blo 1277957 2878145 := bstep (se 2 (by rfl) ⟨1079304, by rfl⟩ : syracuseStep 2878145 = 2158609) B2158609
theorem B2157259 : Blo 1277957 2157259 := bstep (se 1 (by rfl) ⟨1617944, by rfl⟩ : syracuseStep 2157259 = 3235889) B3235889
theorem B1919705 : Blo 1277957 1919705 := bstep (se 2 (by rfl) ⟨719889, by rfl⟩ : syracuseStep 1919705 = 1439779) B1439779
theorem B2804503 : Blo 1277957 2804503 := bstep (se 1 (by rfl) ⟨2103377, by rfl⟩ : syracuseStep 2804503 = 4206755) B4206755
theorem B1846039 : Blo 1277957 1846039 := bstep (se 1 (by rfl) ⟨1384529, by rfl⟩ : syracuseStep 1846039 = 2769059) B2769059
theorem B1919819 : Blo 1277957 1919819 := bstep (se 1 (by rfl) ⟨1439864, by rfl⟩ : syracuseStep 1919819 = 2879729) B2879729
theorem B1919831 : Blo 1277957 1919831 := bstep (se 1 (by rfl) ⟨1439873, by rfl⟩ : syracuseStep 1919831 = 2879747) B2879747
theorem B2157401 : Blo 1277957 2157401 := bstep (se 2 (by rfl) ⟨809025, by rfl⟩ : syracuseStep 2157401 = 1618051) B1618051
theorem B2878361 : Blo 1277957 2878361 := bstep (se 2 (by rfl) ⟨1079385, by rfl⟩ : syracuseStep 2878361 = 2158771) B2158771
theorem B1919897 : Blo 1277957 1919897 := bstep (se 2 (by rfl) ⟨719961, by rfl⟩ : syracuseStep 1919897 = 1439923) B1439923
theorem B2157529 : Blo 1277957 2157529 := bstep (se 2 (by rfl) ⟨809073, by rfl⟩ : syracuseStep 2157529 = 1618147) B1618147
theorem B2878451 : Blo 1277957 2878451 := bstep (se 1 (by rfl) ⟨2158838, by rfl⟩ : syracuseStep 2878451 = 4317677) B4317677
theorem B2731009 : Blo 1277957 2731009 := bstep (se 2 (by rfl) ⟨1024128, by rfl⟩ : syracuseStep 2731009 = 2048257) B2048257
theorem B2878487 : Blo 1277957 2878487 := bstep (se 1 (by rfl) ⟨2158865, by rfl⟩ : syracuseStep 2878487 = 4317731) B4317731
theorem B3238987 : Blo 1277957 3238987 := bstep (se 1 (by rfl) ⟨2429240, by rfl⟩ : syracuseStep 3238987 = 4858481) B4858481
theorem B5459147 : Blo 1277957 5459147 := bstep (se 1 (by rfl) ⟨4094360, by rfl⟩ : syracuseStep 5459147 = 8188721) B8188721
theorem B2878667 : Blo 1277957 2878667 := bstep (se 1 (by rfl) ⟨2159000, by rfl⟩ : syracuseStep 2878667 = 4318001) B4318001
theorem B3239129 : Blo 1277957 3239129 := bstep (se 2 (by rfl) ⟨1214673, by rfl⟩ : syracuseStep 3239129 = 2429347) B2429347
theorem B2428147 : Blo 1277957 2428147 := bstep (se 1 (by rfl) ⟨1821110, by rfl⟩ : syracuseStep 2428147 = 3642221) B3642221
theorem B2878721 : Blo 1277957 2878721 := bstep (se 2 (by rfl) ⟨1079520, by rfl⟩ : syracuseStep 2878721 = 2159041) B2159041
theorem B6475139 : Blo 1277957 6475139 := bstep (se 1 (by rfl) ⟨4856354, by rfl⟩ : syracuseStep 6475139 = 9712709) B9712709
theorem B2428375 : Blo 1277957 2428375 := bstep (se 1 (by rfl) ⟨1821281, by rfl⟩ : syracuseStep 2428375 = 3642563) B3642563
theorem B2878937 : Blo 1277957 2878937 := bstep (se 2 (by rfl) ⟨1079601, by rfl⟩ : syracuseStep 2878937 = 2159203) B2159203
theorem B2158103 : Blo 1277957 2158103 := bstep (se 1 (by rfl) ⟨1618577, by rfl⟩ : syracuseStep 2158103 = 3237155) B3237155
theorem B2879027 : Blo 1277957 2879027 := bstep (se 1 (by rfl) ⟨2159270, by rfl⟩ : syracuseStep 2879027 = 4318541) B4318541
theorem B2428481 : Blo 1277957 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B2879063 : Blo 1277957 2879063 := bstep (se 1 (by rfl) ⟨2159297, by rfl⟩ : syracuseStep 2879063 = 4318595) B4318595
theorem B1822295 : Blo 1277957 1822295 := bstep (se 1 (by rfl) ⟨1366721, by rfl⟩ : syracuseStep 1822295 = 2733443) B2733443
theorem B23334493 : Blo 1277957 23334493 := bstep (se 3 (by rfl) ⟨4375217, by rfl⟩ : syracuseStep 23334493 = 8750435) B8750435
theorem B2305651 : Blo 1277957 2305651 := bstep (se 1 (by rfl) ⟨1729238, by rfl⟩ : syracuseStep 2305651 = 3458477) B3458477
theorem B2158231 : Blo 1277957 2158231 := bstep (se 1 (by rfl) ⟨1618673, by rfl⟩ : syracuseStep 2158231 = 3237347) B3237347
theorem B2428633 : Blo 1277957 2428633 := bstep (se 2 (by rfl) ⟨910737, by rfl⟩ : syracuseStep 2428633 = 1821475) B1821475
theorem B9719513 : Blo 1277957 9719513 := bstep (se 2 (by rfl) ⟨3644817, by rfl⟩ : syracuseStep 9719513 = 7289635) B7289635
theorem B2879243 : Blo 1277957 2879243 := bstep (se 1 (by rfl) ⟨2159432, by rfl⟩ : syracuseStep 2879243 = 4318865) B4318865
theorem B2879297 : Blo 1277957 2879297 := bstep (se 2 (by rfl) ⟨1079736, by rfl⟩ : syracuseStep 2879297 = 2159473) B2159473
theorem B3116875 : Blo 1277957 3116875 := bstep (se 1 (by rfl) ⟨2337656, by rfl⟩ : syracuseStep 3116875 = 4675313) B4675313
theorem B1945559 : Blo 1277957 1945559 := bstep (se 1 (by rfl) ⟨1459169, by rfl⟩ : syracuseStep 1945559 = 2918339) B2918339
theorem B1478647 : Blo 1277957 1478647 := bstep (se 1 (by rfl) ⟨1108985, by rfl⟩ : syracuseStep 1478647 = 2217971) B2217971
theorem B2879513 : Blo 1277957 2879513 := bstep (se 2 (by rfl) ⟨1079817, by rfl⟩ : syracuseStep 2879513 = 2159635) B2159635
theorem B1617995 : Blo 1277957 1617995 := bstep (se 1 (by rfl) ⟨1213496, by rfl⟩ : syracuseStep 1617995 = 2426993) B2426993
theorem B2879603 : Blo 1277957 2879603 := bstep (se 1 (by rfl) ⟨2159702, by rfl⟩ : syracuseStep 2879603 = 4319405) B4319405
theorem B1437835 : Blo 1277957 1437835 := bstep (se 1 (by rfl) ⟨1078376, by rfl⟩ : syracuseStep 1437835 = 2156753) B2156753
theorem B5460119 : Blo 1277957 5460119 := bstep (se 1 (by rfl) ⟨4095089, by rfl⟩ : syracuseStep 5460119 = 8190179) B8190179
theorem B2879639 : Blo 1277957 2879639 := bstep (se 1 (by rfl) ⟨2159729, by rfl⟩ : syracuseStep 2879639 = 4319459) B4319459
theorem B3641537 : Blo 1277957 3641537 := bstep (se 2 (by rfl) ⟨1365576, by rfl⟩ : syracuseStep 3641537 = 2731153) B2731153
theorem B3641561 : Blo 1277957 3641561 := bstep (se 2 (by rfl) ⟨1365585, by rfl⟩ : syracuseStep 3641561 = 2731171) B2731171
theorem B1437943 : Blo 1277957 1437943 := bstep (se 1 (by rfl) ⟨1078457, by rfl⟩ : syracuseStep 1437943 = 2156915) B2156915
theorem B2158859 : Blo 1277957 2158859 := bstep (se 1 (by rfl) ⟨1619144, by rfl⟩ : syracuseStep 2158859 = 3238289) B3238289
theorem B14569793 : Blo 1277957 14569793 := bstep (se 2 (by rfl) ⟨5463672, by rfl⟩ : syracuseStep 14569793 = 10927345) B10927345
theorem B2879819 : Blo 1277957 2879819 := bstep (se 1 (by rfl) ⟨2159864, by rfl⟩ : syracuseStep 2879819 = 4319729) B4319729
theorem B2879873 : Blo 1277957 2879873 := bstep (se 2 (by rfl) ⟨1079952, by rfl⟩ : syracuseStep 2879873 = 2159905) B2159905
theorem B2158987 : Blo 1277957 2158987 := bstep (se 1 (by rfl) ⟨1619240, by rfl⟩ : syracuseStep 2158987 = 3238481) B3238481
theorem B1438123 : Blo 1277957 1438123 := bstep (se 1 (by rfl) ⟨1078592, by rfl⟩ : syracuseStep 1438123 = 2157185) B2157185
theorem B23671217 : Blo 1277957 23671217 := bstep (se 2 (by rfl) ⟨8876706, by rfl⟩ : syracuseStep 23671217 = 17753413) B17753413
theorem B4207069 : Blo 1277957 4207069 := bstep (se 3 (by rfl) ⟨788825, by rfl⟩ : syracuseStep 4207069 = 1577651) B1577651
theorem B4854275 : Blo 1277957 4854275 := bstep (se 1 (by rfl) ⟨3640706, by rfl⟩ : syracuseStep 4854275 = 7281413) B7281413
theorem B2732555 : Blo 1277957 2732555 := bstep (se 1 (by rfl) ⟨2049416, by rfl⟩ : syracuseStep 2732555 = 4098833) B4098833
theorem B4854289 : Blo 1277957 4854289 := bstep (se 2 (by rfl) ⟨1820358, by rfl⟩ : syracuseStep 4854289 = 3640717) B3640717
theorem B1438231 : Blo 1277957 1438231 := bstep (se 1 (by rfl) ⟨1078673, by rfl⟩ : syracuseStep 1438231 = 2157347) B2157347
theorem B2159129 : Blo 1277957 2159129 := bstep (se 2 (by rfl) ⟨809673, by rfl⟩ : syracuseStep 2159129 = 1619347) B1619347
theorem B2159257 : Blo 1277957 2159257 := bstep (se 2 (by rfl) ⟨809721, by rfl⟩ : syracuseStep 2159257 = 1619443) B1619443
theorem B1438411 : Blo 1277957 1438411 := bstep (se 1 (by rfl) ⟨1078808, by rfl⟩ : syracuseStep 1438411 = 2157617) B2157617
theorem B12284621 : Blo 1277957 12284621 := bstep (se 3 (by rfl) ⟨2303366, by rfl⟩ : syracuseStep 12284621 = 4606733) B4606733
theorem B1618699 : Blo 1277957 1618699 := bstep (se 1 (by rfl) ⟨1214024, by rfl⟩ : syracuseStep 1618699 = 2428049) B2428049
theorem B1438519 : Blo 1277957 1438519 := bstep (se 1 (by rfl) ⟨1078889, by rfl⟩ : syracuseStep 1438519 = 2157779) B2157779
theorem B4854593 : Blo 1277957 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B1364855 : Blo 1277957 1364855 := bstep (se 1 (by rfl) ⟨1023641, by rfl⟩ : syracuseStep 1364855 = 2047283) B2047283
theorem B4314059 : Blo 1277957 4314059 := bstep (se 1 (by rfl) ⟨3235544, by rfl⟩ : syracuseStep 4314059 = 6471089) B6471089
theorem B1438699 : Blo 1277957 1438699 := bstep (se 1 (by rfl) ⟨1079024, by rfl⟩ : syracuseStep 1438699 = 2158049) B2158049
theorem B1618967 : Blo 1277957 1618967 := bstep (se 1 (by rfl) ⟨1214225, by rfl⟩ : syracuseStep 1618967 = 2428451) B2428451
theorem B56865827 : Blo 1277957 56865827 := bstep (se 1 (by rfl) ⟨42649370, by rfl⟩ : syracuseStep 56865827 = 85298741) B85298741
theorem B1438807 : Blo 1277957 1438807 := bstep (se 1 (by rfl) ⟨1079105, by rfl⟩ : syracuseStep 1438807 = 2158211) B2158211
theorem B4609169 : Blo 1277957 4609169 := bstep (se 2 (by rfl) ⟨1728438, by rfl⟩ : syracuseStep 4609169 = 3456877) B3456877
theorem B2159831 : Blo 1277957 2159831 := bstep (se 1 (by rfl) ⟨1619873, by rfl⟩ : syracuseStep 2159831 = 3239747) B3239747
theorem B4314329 : Blo 1277957 4314329 := bstep (se 2 (by rfl) ⟨1617873, by rfl⟩ : syracuseStep 4314329 = 3235747) B3235747
theorem B1438987 : Blo 1277957 1438987 := bstep (se 1 (by rfl) ⟨1079240, by rfl⟩ : syracuseStep 1438987 = 2158481) B2158481
theorem B2462987 : Blo 1277957 2462987 := bstep (se 1 (by rfl) ⟨1847240, by rfl⟩ : syracuseStep 2462987 = 3694481) B3694481
theorem B2733401 : Blo 1277957 2733401 := bstep (se 2 (by rfl) ⟨1025025, by rfl⟩ : syracuseStep 2733401 = 2050051) B2050051
theorem B1439095 : Blo 1277957 1439095 := bstep (se 1 (by rfl) ⟨1079321, by rfl⟩ : syracuseStep 1439095 = 2158643) B2158643
theorem B3642803 : Blo 1277957 3642803 := bstep (se 1 (by rfl) ⟨2732102, by rfl⟩ : syracuseStep 3642803 = 5464205) B5464205
theorem B4855261 : Blo 1277957 4855261 := bstep (se 3 (by rfl) ⟨910361, by rfl⟩ : syracuseStep 4855261 = 1820723) B1820723
theorem B1439275 : Blo 1277957 1439275 := bstep (se 1 (by rfl) ⟨1079456, by rfl⟩ : syracuseStep 1439275 = 2158913) B2158913
theorem B7288451 : Blo 1277957 7288451 := bstep (se 1 (by rfl) ⟨5466338, by rfl⟩ : syracuseStep 7288451 = 10932677) B10932677
theorem B1439383 : Blo 1277957 1439383 := bstep (se 1 (by rfl) ⟨1079537, by rfl⟩ : syracuseStep 1439383 = 2159075) B2159075
theorem B10376855 : Blo 1277957 10376855 := bstep (se 1 (by rfl) ⟨7782641, by rfl⟩ : syracuseStep 10376855 = 15565283) B15565283
theorem B1619671 : Blo 1277957 1619671 := bstep (se 1 (by rfl) ⟨1214753, by rfl⟩ : syracuseStep 1619671 = 2429507) B2429507
theorem B1439563 : Blo 1277957 1439563 := bstep (se 1 (by rfl) ⟨1079672, by rfl⟩ : syracuseStep 1439563 = 2159345) B2159345
theorem B4315031 : Blo 1277957 4315031 := bstep (se 1 (by rfl) ⟨3236273, by rfl⟩ : syracuseStep 4315031 = 6472547) B6472547
theorem B1439671 : Blo 1277957 1439671 := bstep (se 1 (by rfl) ⟨1079753, by rfl⟩ : syracuseStep 1439671 = 2159507) B2159507
theorem B9713681 : Blo 1277957 9713681 := bstep (se 2 (by rfl) ⟨3642630, by rfl⟩ : syracuseStep 9713681 = 7285261) B7285261
theorem B7280705 : Blo 1277957 7280705 := bstep (se 2 (by rfl) ⟨2730264, by rfl⟩ : syracuseStep 7280705 = 5460529) B5460529
theorem B11671627 : Blo 1277957 11671627 := bstep (se 1 (by rfl) ⟨8753720, by rfl⟩ : syracuseStep 11671627 = 17507441) B17507441
theorem B1439851 : Blo 1277957 1439851 := bstep (se 1 (by rfl) ⟨1079888, by rfl⟩ : syracuseStep 1439851 = 2159777) B2159777
theorem B6150323 : Blo 1277957 6150323 := bstep (se 1 (by rfl) ⟨4612742, by rfl⟩ : syracuseStep 6150323 = 9225485) B9225485
theorem B4094155 : Blo 1277957 4094155 := bstep (se 1 (by rfl) ⟨3070616, by rfl⟩ : syracuseStep 4094155 = 6141233) B6141233
theorem B4208857 : Blo 1277957 4208857 := bstep (se 2 (by rfl) ⟨1578321, by rfl⟩ : syracuseStep 4208857 = 3156643) B3156643
theorem B3455255 : Blo 1277957 3455255 := bstep (se 1 (by rfl) ⟨2591441, by rfl⟩ : syracuseStep 3455255 = 5182883) B5182883
theorem B24598829 : Blo 1277957 24598829 := bstep (se 3 (by rfl) ⟨4612280, by rfl⟩ : syracuseStep 24598829 = 9224561) B9224561
theorem B4094297 : Blo 1277957 4094297 := bstep (se 2 (by rfl) ⟨1535361, by rfl⟩ : syracuseStep 4094297 = 3070723) B3070723
theorem B13834597 : Blo 1277957 13834597 := bstep (se 4 (by rfl) ⟨1296993, by rfl⟩ : syracuseStep 13834597 = 2593987) B2593987
theorem B3889559 : Blo 1277957 3889559 := bstep (se 1 (by rfl) ⟨2917169, by rfl⟩ : syracuseStep 3889559 = 5834339) B5834339
theorem B9705905 : Blo 1277957 9705905 := bstep (se 2 (by rfl) ⟨3639714, by rfl⟩ : syracuseStep 9705905 = 7279429) B7279429
theorem B4315571 : Blo 1277957 4315571 := bstep (se 1 (by rfl) ⟨3236678, by rfl⟩ : syracuseStep 4315571 = 6473357) B6473357
theorem B10795481 : Blo 1277957 10795481 := bstep (se 2 (by rfl) ⟨4048305, by rfl⟩ : syracuseStep 10795481 = 8096611) B8096611
theorem B5462579 : Blo 1277957 5462579 := bstep (se 1 (by rfl) ⟨4096934, by rfl⟩ : syracuseStep 5462579 = 8193869) B8193869
theorem B5184145 : Blo 1277957 5184145 := bstep (se 2 (by rfl) ⟨1944054, by rfl⟩ : syracuseStep 5184145 = 3888109) B3888109
theorem B1366679 : Blo 1277957 1366679 := bstep (se 1 (by rfl) ⟨1025009, by rfl⟩ : syracuseStep 1366679 = 2050019) B2050019
theorem B4315841 : Blo 1277957 4315841 := bstep (se 2 (by rfl) ⟨1618440, by rfl⟩ : syracuseStep 4315841 = 3236881) B3236881
theorem B18430669 : Blo 1277957 18430669 := bstep (se 3 (by rfl) ⟨3455750, by rfl⟩ : syracuseStep 18430669 = 6911501) B6911501
theorem B4856537 : Blo 1277957 4856537 := bstep (se 2 (by rfl) ⟨1821201, by rfl⟩ : syracuseStep 4856537 = 3642403) B3642403
theorem B5995315 : Blo 1277957 5995315 := bstep (se 1 (by rfl) ⟨4496486, by rfl⟩ : syracuseStep 5995315 = 8992973) B8992973
theorem B9706391 : Blo 1277957 9706391 := bstep (se 1 (by rfl) ⟨7279793, by rfl⟩ : syracuseStep 9706391 = 14559587) B14559587
theorem B6478865 : Blo 1277957 6478865 := bstep (se 2 (by rfl) ⟨2429574, by rfl⟩ : syracuseStep 6478865 = 4859149) B4859149
theorem B6479027 : Blo 1277957 6479027 := bstep (se 1 (by rfl) ⟨4859270, by rfl⟩ : syracuseStep 6479027 = 9718541) B9718541
theorem B5536961 : Blo 1277957 5536961 := bstep (se 2 (by rfl) ⟨2076360, by rfl⟩ : syracuseStep 5536961 = 4152721) B4152721
theorem B4611275 : Blo 1277957 4611275 := bstep (se 1 (by rfl) ⟨3458456, by rfl⟩ : syracuseStep 4611275 = 6916913) B6916913
theorem B4316381 : Blo 1277957 4316381 := bstep (se 3 (by rfl) ⟨809321, by rfl⟩ : syracuseStep 4316381 = 1618643) B1618643
theorem B16391429 : Blo 1277957 16391429 := bstep (se 4 (by rfl) ⟨1536696, by rfl⟩ : syracuseStep 16391429 = 3073393) B3073393
theorem B6143249 : Blo 1277957 6143249 := bstep (se 2 (by rfl) ⟨2303718, by rfl⟩ : syracuseStep 6143249 = 4607437) B4607437
theorem B9223469 : Blo 1277957 9223469 := bstep (se 3 (by rfl) ⟨1729400, by rfl⟩ : syracuseStep 9223469 = 3458801) B3458801
theorem B8191307 : Blo 1277957 8191307 := bstep (se 1 (by rfl) ⟨6143480, by rfl⟩ : syracuseStep 8191307 = 12286961) B12286961
theorem B2186585 : Blo 1277957 2186585 := bstep (se 2 (by rfl) ⟨819969, by rfl⟩ : syracuseStep 2186585 = 1639939) B1639939
theorem B1727833 : Blo 1277957 1727833 := bstep (se 2 (by rfl) ⟨647937, by rfl⟩ : syracuseStep 1727833 = 1295875) B1295875
theorem B4152755 : Blo 1277957 4152755 := bstep (se 1 (by rfl) ⟨3114566, by rfl⟩ : syracuseStep 4152755 = 6229133) B6229133
theorem B3112523 : Blo 1277957 3112523 := bstep (se 1 (by rfl) ⟨2334392, by rfl⟩ : syracuseStep 3112523 = 4668785) B4668785
theorem B3235403 : Blo 1277957 3235403 := bstep (se 1 (by rfl) ⟨2426552, by rfl⟩ : syracuseStep 3235403 = 4853105) B4853105
theorem B10919555 : Blo 1277957 10919555 := bstep (se 1 (by rfl) ⟨8189666, by rfl⟩ : syracuseStep 10919555 = 16379333) B16379333
theorem B6143789 : Blo 1277957 6143789 := bstep (se 3 (by rfl) ⟨1151960, by rfl⟩ : syracuseStep 6143789 = 2303921) B2303921
theorem B6471575 : Blo 1277957 6471575 := bstep (se 1 (by rfl) ⟨4853681, by rfl⟩ : syracuseStep 6471575 = 9707363) B9707363
theorem B5832641 : Blo 1277957 5832641 := bstep (se 2 (by rfl) ⟨2187240, by rfl⟩ : syracuseStep 5832641 = 4374481) B4374481
theorem B2768833 : Blo 1277957 2768833 := bstep (se 2 (by rfl) ⟨1038312, by rfl⟩ : syracuseStep 2768833 = 2076625) B2076625
theorem B3072001 : Blo 1277957 3072001 := bstep (se 2 (by rfl) ⟨1152000, by rfl⟩ : syracuseStep 3072001 = 2304001) B2304001
theorem B1277959 : Blo 1277957 1277959 := bstep (se 1 (by rfl) ⟨958469, by rfl⟩ : syracuseStep 1277959 = 1916939) B1916939
theorem B5537803 : Blo 1277957 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B1277967 : Blo 1277957 1277967 := bstep (se 1 (by rfl) ⟨958475, by rfl⟩ : syracuseStep 1277967 = 1916951) B1916951
theorem B4669483 : Blo 1277957 4669483 := bstep (se 1 (by rfl) ⟨3502112, by rfl⟩ : syracuseStep 4669483 = 7004225) B7004225
theorem B1916987 : Blo 1277957 1916987 := bstep (se 1 (by rfl) ⟨1437740, by rfl⟩ : syracuseStep 1916987 = 2875481) B2875481
theorem B1278011 : Blo 1277957 1278011 := bstep (se 1 (by rfl) ⟨958508, by rfl⟩ : syracuseStep 1278011 = 1917017) B1917017
theorem B4317245 : Blo 1277957 4317245 := bstep (se 3 (by rfl) ⟨809483, by rfl⟩ : syracuseStep 4317245 = 1618967) B1618967
theorem B1917047 : Blo 1277957 1917047 := bstep (se 1 (by rfl) ⟨1437785, by rfl⟩ : syracuseStep 1917047 = 2875571) B2875571
theorem B1278087 : Blo 1277957 1278087 := bstep (se 1 (by rfl) ⟨958565, by rfl⟩ : syracuseStep 1278087 = 1917131) B1917131
theorem B1917071 : Blo 1277957 1917071 := bstep (se 1 (by rfl) ⟨1437803, by rfl⟩ : syracuseStep 1917071 = 2875607) B2875607
theorem B1278095 : Blo 1277957 1278095 := bstep (se 1 (by rfl) ⟨958571, by rfl⟩ : syracuseStep 1278095 = 1917143) B1917143
theorem B1917113 : Blo 1277957 1917113 := bstep (se 2 (by rfl) ⟨718917, by rfl⟩ : syracuseStep 1917113 = 1437835) B1437835
theorem B1278139 : Blo 1277957 1278139 := bstep (se 1 (by rfl) ⟨958604, by rfl⟩ : syracuseStep 1278139 = 1917209) B1917209
theorem B1917191 : Blo 1277957 1917191 := bstep (se 1 (by rfl) ⟨1437893, by rfl⟩ : syracuseStep 1917191 = 2875787) B2875787
theorem B1278215 : Blo 1277957 1278215 := bstep (se 1 (by rfl) ⟨958661, by rfl⟩ : syracuseStep 1278215 = 1917323) B1917323
theorem B1278223 : Blo 1277957 1278223 := bstep (se 1 (by rfl) ⟨958667, by rfl⟩ : syracuseStep 1278223 = 1917335) B1917335
theorem B1917227 : Blo 1277957 1917227 := bstep (se 1 (by rfl) ⟨1437920, by rfl⟩ : syracuseStep 1917227 = 2875841) B2875841
theorem B1278267 : Blo 1277957 1278267 := bstep (se 1 (by rfl) ⟨958700, by rfl⟩ : syracuseStep 1278267 = 1917401) B1917401
theorem B1917257 : Blo 1277957 1917257 := bstep (se 2 (by rfl) ⟨718971, by rfl⟩ : syracuseStep 1917257 = 1437943) B1437943
theorem B3236183 : Blo 1277957 3236183 := bstep (se 1 (by rfl) ⟨2427137, by rfl⟩ : syracuseStep 3236183 = 4854275) B4854275
theorem B1278343 : Blo 1277957 1278343 := bstep (se 1 (by rfl) ⟨958757, by rfl⟩ : syracuseStep 1278343 = 1917515) B1917515
theorem B2998663 : Blo 1277957 2998663 := bstep (se 1 (by rfl) ⟨2248997, by rfl⟩ : syracuseStep 2998663 = 4497995) B4497995
theorem B1278351 : Blo 1277957 1278351 := bstep (se 1 (by rfl) ⟨958763, by rfl⟩ : syracuseStep 1278351 = 1917527) B1917527
theorem B1917371 : Blo 1277957 1917371 := bstep (se 1 (by rfl) ⟨1438028, by rfl⟩ : syracuseStep 1917371 = 2876057) B2876057
theorem B1278395 : Blo 1277957 1278395 := bstep (se 1 (by rfl) ⟨958796, by rfl⟩ : syracuseStep 1278395 = 1917593) B1917593
theorem B5464529 : Blo 1277957 5464529 := bstep (se 2 (by rfl) ⟨2049198, by rfl⟩ : syracuseStep 5464529 = 4098397) B4098397
theorem B1917431 : Blo 1277957 1917431 := bstep (se 1 (by rfl) ⟨1438073, by rfl⟩ : syracuseStep 1917431 = 2876147) B2876147
theorem B1278471 : Blo 1277957 1278471 := bstep (se 1 (by rfl) ⟨958853, by rfl⟩ : syracuseStep 1278471 = 1917707) B1917707
theorem B1917455 : Blo 1277957 1917455 := bstep (se 1 (by rfl) ⟨1438091, by rfl⟩ : syracuseStep 1917455 = 2876183) B2876183
theorem B1278479 : Blo 1277957 1278479 := bstep (se 1 (by rfl) ⟨958859, by rfl⟩ : syracuseStep 1278479 = 1917719) B1917719
theorem B39387683 : Blo 1277957 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B3236395 : Blo 1277957 3236395 := bstep (se 1 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 3236395 = 4854593) B4854593
theorem B1917497 : Blo 1277957 1917497 := bstep (se 2 (by rfl) ⟨719061, by rfl⟩ : syracuseStep 1917497 = 1438123) B1438123
theorem B1278523 : Blo 1277957 1278523 := bstep (se 1 (by rfl) ⟨958892, by rfl⟩ : syracuseStep 1278523 = 1917785) B1917785
theorem B2876039 : Blo 1277957 2876039 := bstep (se 1 (by rfl) ⟨2157029, by rfl⟩ : syracuseStep 2876039 = 4314059) B4314059
theorem B1917575 : Blo 1277957 1917575 := bstep (se 1 (by rfl) ⟨1438181, by rfl⟩ : syracuseStep 1917575 = 2876363) B2876363
theorem B1278599 : Blo 1277957 1278599 := bstep (se 1 (by rfl) ⟨958949, by rfl⟩ : syracuseStep 1278599 = 1917899) B1917899
theorem B2048647 : Blo 1277957 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B1278607 : Blo 1277957 1278607 := bstep (se 1 (by rfl) ⟨958955, by rfl⟩ : syracuseStep 1278607 = 1917911) B1917911
theorem B1917611 : Blo 1277957 1917611 := bstep (se 1 (by rfl) ⟨1438208, by rfl⟩ : syracuseStep 1917611 = 2876417) B2876417
theorem B3236537 : Blo 1277957 3236537 := bstep (se 2 (by rfl) ⟨1213701, by rfl⟩ : syracuseStep 3236537 = 2427403) B2427403
theorem B1278651 : Blo 1277957 1278651 := bstep (se 1 (by rfl) ⟨958988, by rfl⟩ : syracuseStep 1278651 = 1917977) B1917977
theorem B6472385 : Blo 1277957 6472385 := bstep (se 2 (by rfl) ⟨2427144, by rfl⟩ : syracuseStep 6472385 = 4854289) B4854289
theorem B1917641 : Blo 1277957 1917641 := bstep (se 2 (by rfl) ⟨719115, by rfl⟩ : syracuseStep 1917641 = 1438231) B1438231
theorem B27648773 : Blo 1277957 27648773 := bstep (se 4 (by rfl) ⟨2592072, by rfl⟩ : syracuseStep 27648773 = 5184145) B5184145
theorem B1278727 : Blo 1277957 1278727 := bstep (se 1 (by rfl) ⟨959045, by rfl⟩ : syracuseStep 1278727 = 1918091) B1918091
theorem B3072779 : Blo 1277957 3072779 := bstep (se 1 (by rfl) ⟨2304584, by rfl⟩ : syracuseStep 3072779 = 4609169) B4609169
theorem B1278735 : Blo 1277957 1278735 := bstep (se 1 (by rfl) ⟨959051, by rfl⟩ : syracuseStep 1278735 = 1918103) B1918103
theorem B2876219 : Blo 1277957 2876219 := bstep (se 1 (by rfl) ⟨2157164, by rfl⟩ : syracuseStep 2876219 = 4314329) B4314329
theorem B1917755 : Blo 1277957 1917755 := bstep (se 1 (by rfl) ⟨1438316, by rfl⟩ : syracuseStep 1917755 = 2876633) B2876633
theorem B1278779 : Blo 1277957 1278779 := bstep (se 1 (by rfl) ⟨959084, by rfl⟩ : syracuseStep 1278779 = 1918169) B1918169
theorem B1917815 : Blo 1277957 1917815 := bstep (se 1 (by rfl) ⟨1438361, by rfl⟩ : syracuseStep 1917815 = 2876723) B2876723
theorem B1278855 : Blo 1277957 1278855 := bstep (se 1 (by rfl) ⟨959141, by rfl⟩ : syracuseStep 1278855 = 1918283) B1918283
theorem B1917839 : Blo 1277957 1917839 := bstep (se 1 (by rfl) ⟨1438379, by rfl⟩ : syracuseStep 1917839 = 2876759) B2876759
theorem B1278863 : Blo 1277957 1278863 := bstep (se 1 (by rfl) ⟨959147, by rfl⟩ : syracuseStep 1278863 = 1918295) B1918295
theorem B2876345 : Blo 1277957 2876345 := bstep (se 2 (by rfl) ⟨1078629, by rfl⟩ : syracuseStep 2876345 = 2157259) B2157259
theorem B1917881 : Blo 1277957 1917881 := bstep (se 2 (by rfl) ⟨719205, by rfl⟩ : syracuseStep 1917881 = 1438411) B1438411
theorem B1278907 : Blo 1277957 1278907 := bstep (se 1 (by rfl) ⟨959180, by rfl⟩ : syracuseStep 1278907 = 1918361) B1918361
theorem B1917959 : Blo 1277957 1917959 := bstep (se 1 (by rfl) ⟨1438469, by rfl⟩ : syracuseStep 1917959 = 2876939) B2876939
theorem B1278983 : Blo 1277957 1278983 := bstep (se 1 (by rfl) ⟨959237, by rfl⟩ : syracuseStep 1278983 = 1918475) B1918475
theorem B1278991 : Blo 1277957 1278991 := bstep (se 1 (by rfl) ⟨959243, by rfl⟩ : syracuseStep 1278991 = 1918487) B1918487
theorem B1917995 : Blo 1277957 1917995 := bstep (se 1 (by rfl) ⟨1438496, by rfl⟩ : syracuseStep 1917995 = 2876993) B2876993
theorem B1279035 : Blo 1277957 1279035 := bstep (se 1 (by rfl) ⟨959276, by rfl⟩ : syracuseStep 1279035 = 1918553) B1918553
theorem B10372157 : Blo 1277957 10372157 := bstep (se 3 (by rfl) ⟨1944779, by rfl⟩ : syracuseStep 10372157 = 3889559) B3889559
theorem B1918025 : Blo 1277957 1918025 := bstep (se 2 (by rfl) ⟨719259, by rfl⟩ : syracuseStep 1918025 = 1438519) B1438519
theorem B3114071 : Blo 1277957 3114071 := bstep (se 1 (by rfl) ⟨2335553, by rfl⟩ : syracuseStep 3114071 = 4671107) B4671107
theorem B4858967 : Blo 1277957 4858967 := bstep (se 1 (by rfl) ⟨3644225, by rfl⟩ : syracuseStep 4858967 = 7288451) B7288451
theorem B22447237 : Blo 1277957 22447237 := bstep (se 4 (by rfl) ⟨2104428, by rfl⟩ : syracuseStep 22447237 = 4208857) B4208857
theorem B1279111 : Blo 1277957 1279111 := bstep (se 1 (by rfl) ⟨959333, by rfl⟩ : syracuseStep 1279111 = 1918667) B1918667
theorem B1279119 : Blo 1277957 1279119 := bstep (se 1 (by rfl) ⟨959339, by rfl⟩ : syracuseStep 1279119 = 1918679) B1918679
theorem B1918139 : Blo 1277957 1918139 := bstep (se 1 (by rfl) ⟨1438604, by rfl⟩ : syracuseStep 1918139 = 2877209) B2877209
theorem B1279163 : Blo 1277957 1279163 := bstep (se 1 (by rfl) ⟨959372, by rfl⟩ : syracuseStep 1279163 = 1918745) B1918745
theorem B1918199 : Blo 1277957 1918199 := bstep (se 1 (by rfl) ⟨1438649, by rfl⟩ : syracuseStep 1918199 = 2877299) B2877299
theorem B1279239 : Blo 1277957 1279239 := bstep (se 1 (by rfl) ⟨959429, by rfl⟩ : syracuseStep 1279239 = 1918859) B1918859
theorem B2876687 : Blo 1277957 2876687 := bstep (se 1 (by rfl) ⟨2157515, by rfl⟩ : syracuseStep 2876687 = 4315031) B4315031
theorem B1918223 : Blo 1277957 1918223 := bstep (se 1 (by rfl) ⟨1438667, by rfl⟩ : syracuseStep 1918223 = 2877335) B2877335
theorem B1279247 : Blo 1277957 1279247 := bstep (se 1 (by rfl) ⟨959435, by rfl⟩ : syracuseStep 1279247 = 1918871) B1918871
theorem B2876705 : Blo 1277957 2876705 := bstep (se 2 (by rfl) ⟨1078764, by rfl⟩ : syracuseStep 2876705 = 2157529) B2157529
theorem B1918265 : Blo 1277957 1918265 := bstep (se 2 (by rfl) ⟨719349, by rfl⟩ : syracuseStep 1918265 = 1438699) B1438699
theorem B1279291 : Blo 1277957 1279291 := bstep (se 1 (by rfl) ⟨959468, by rfl⟩ : syracuseStep 1279291 = 1918937) B1918937
theorem B1918343 : Blo 1277957 1918343 := bstep (se 1 (by rfl) ⟨1438757, by rfl⟩ : syracuseStep 1918343 = 2877515) B2877515
theorem B1279367 : Blo 1277957 1279367 := bstep (se 1 (by rfl) ⟨959525, by rfl⟩ : syracuseStep 1279367 = 1919051) B1919051
theorem B1279375 : Blo 1277957 1279375 := bstep (se 1 (by rfl) ⟨959531, by rfl⟩ : syracuseStep 1279375 = 1919063) B1919063
theorem B1918379 : Blo 1277957 1918379 := bstep (se 1 (by rfl) ⟨1438784, by rfl⟩ : syracuseStep 1918379 = 2877569) B2877569
theorem B4318649 : Blo 1277957 4318649 := bstep (se 2 (by rfl) ⟨1619493, by rfl⟩ : syracuseStep 4318649 = 3238987) B3238987
theorem B1279419 : Blo 1277957 1279419 := bstep (se 1 (by rfl) ⟨959564, by rfl⟩ : syracuseStep 1279419 = 1919129) B1919129
theorem B1918409 : Blo 1277957 1918409 := bstep (se 2 (by rfl) ⟨719403, by rfl⟩ : syracuseStep 1918409 = 1438807) B1438807
theorem B14566877 : Blo 1277957 14566877 := bstep (se 3 (by rfl) ⟨2731289, by rfl⟩ : syracuseStep 14566877 = 5462579) B5462579
theorem B1279495 : Blo 1277957 1279495 := bstep (se 1 (by rfl) ⟨959621, by rfl⟩ : syracuseStep 1279495 = 1919243) B1919243
theorem B1279503 : Blo 1277957 1279503 := bstep (se 1 (by rfl) ⟨959627, by rfl⟩ : syracuseStep 1279503 = 1919255) B1919255
theorem B2729531 : Blo 1277957 2729531 := bstep (se 1 (by rfl) ⟨2047148, by rfl⟩ : syracuseStep 2729531 = 4094297) B4094297
theorem B1918523 : Blo 1277957 1918523 := bstep (se 1 (by rfl) ⟨1438892, by rfl⟩ : syracuseStep 1918523 = 2877785) B2877785
theorem B1279547 : Blo 1277957 1279547 := bstep (se 1 (by rfl) ⟨959660, by rfl⟩ : syracuseStep 1279547 = 1919321) B1919321
theorem B4859453 : Blo 1277957 4859453 := bstep (se 3 (by rfl) ⟨911147, by rfl⟩ : syracuseStep 4859453 = 1822295) B1822295
theorem B1820279 : Blo 1277957 1820279 := bstep (se 1 (by rfl) ⟨1365209, by rfl⟩ : syracuseStep 1820279 = 2730419) B2730419
theorem B2877047 : Blo 1277957 2877047 := bstep (se 1 (by rfl) ⟨2157785, by rfl⟩ : syracuseStep 2877047 = 4315571) B4315571
theorem B1918583 : Blo 1277957 1918583 := bstep (se 1 (by rfl) ⟨1438937, by rfl⟩ : syracuseStep 1918583 = 2877875) B2877875
theorem B1279623 : Blo 1277957 1279623 := bstep (se 1 (by rfl) ⟨959717, by rfl⟩ : syracuseStep 1279623 = 1919435) B1919435
theorem B1918607 : Blo 1277957 1918607 := bstep (se 1 (by rfl) ⟨1438955, by rfl⟩ : syracuseStep 1918607 = 2877911) B2877911
theorem B1279631 : Blo 1277957 1279631 := bstep (se 1 (by rfl) ⟨959723, by rfl⟩ : syracuseStep 1279631 = 1919447) B1919447
theorem B3237529 : Blo 1277957 3237529 := bstep (se 2 (by rfl) ⟨1214073, by rfl⟩ : syracuseStep 3237529 = 2428147) B2428147
theorem B1918649 : Blo 1277957 1918649 := bstep (se 2 (by rfl) ⟨719493, by rfl⟩ : syracuseStep 1918649 = 1438987) B1438987
theorem B1279675 : Blo 1277957 1279675 := bstep (se 1 (by rfl) ⟨959756, by rfl⟩ : syracuseStep 1279675 = 1919513) B1919513
theorem B1918727 : Blo 1277957 1918727 := bstep (se 1 (by rfl) ⟨1439045, by rfl⟩ : syracuseStep 1918727 = 2878091) B2878091
theorem B1279751 : Blo 1277957 1279751 := bstep (se 1 (by rfl) ⟨959813, by rfl⟩ : syracuseStep 1279751 = 1919627) B1919627
theorem B1279759 : Blo 1277957 1279759 := bstep (se 1 (by rfl) ⟨959819, by rfl⟩ : syracuseStep 1279759 = 1919639) B1919639
theorem B2303777 : Blo 1277957 2303777 := bstep (se 2 (by rfl) ⟨863916, by rfl⟩ : syracuseStep 2303777 = 1727833) B1727833
theorem B2877227 : Blo 1277957 2877227 := bstep (se 1 (by rfl) ⟨2157920, by rfl⟩ : syracuseStep 2877227 = 4315841) B4315841
theorem B1918763 : Blo 1277957 1918763 := bstep (se 1 (by rfl) ⟨1439072, by rfl⟩ : syracuseStep 1918763 = 2878145) B2878145
theorem B3237691 : Blo 1277957 3237691 := bstep (se 1 (by rfl) ⟨2428268, by rfl⟩ : syracuseStep 3237691 = 4856537) B4856537
theorem B1279803 : Blo 1277957 1279803 := bstep (se 1 (by rfl) ⟨959852, by rfl⟩ : syracuseStep 1279803 = 1919705) B1919705
theorem B1918793 : Blo 1277957 1918793 := bstep (se 2 (by rfl) ⟨719547, by rfl⟩ : syracuseStep 1918793 = 1439095) B1439095
theorem B1279879 : Blo 1277957 1279879 := bstep (se 1 (by rfl) ⟨959909, by rfl⟩ : syracuseStep 1279879 = 1919819) B1919819
theorem B1279887 : Blo 1277957 1279887 := bstep (se 1 (by rfl) ⟨959915, by rfl⟩ : syracuseStep 1279887 = 1919831) B1919831
theorem B1918907 : Blo 1277957 1918907 := bstep (se 1 (by rfl) ⟨1439180, by rfl⟩ : syracuseStep 1918907 = 2878361) B2878361
theorem B1279931 : Blo 1277957 1279931 := bstep (se 1 (by rfl) ⟨959948, by rfl⟩ : syracuseStep 1279931 = 1919897) B1919897
theorem B3237833 : Blo 1277957 3237833 := bstep (se 2 (by rfl) ⟨1214187, by rfl⟩ : syracuseStep 3237833 = 2428375) B2428375
theorem B6473681 : Blo 1277957 6473681 := bstep (se 2 (by rfl) ⟨2427630, by rfl⟩ : syracuseStep 6473681 = 4855261) B4855261
theorem B1918967 : Blo 1277957 1918967 := bstep (se 1 (by rfl) ⟨1439225, by rfl⟩ : syracuseStep 1918967 = 2878451) B2878451
theorem B4319243 : Blo 1277957 4319243 := bstep (se 1 (by rfl) ⟨3239432, by rfl⟩ : syracuseStep 4319243 = 6478865) B6478865
theorem B1918991 : Blo 1277957 1918991 := bstep (se 1 (by rfl) ⟨1439243, by rfl⟩ : syracuseStep 1918991 = 2878487) B2878487
theorem B1919033 : Blo 1277957 1919033 := bstep (se 2 (by rfl) ⟨719637, by rfl⟩ : syracuseStep 1919033 = 1439275) B1439275
theorem B4319351 : Blo 1277957 4319351 := bstep (se 1 (by rfl) ⟨3239513, by rfl⟩ : syracuseStep 4319351 = 6479027) B6479027
theorem B3639431 : Blo 1277957 3639431 := bstep (se 1 (by rfl) ⟨2729573, by rfl⟩ : syracuseStep 3639431 = 5459147) B5459147
theorem B1919111 : Blo 1277957 1919111 := bstep (se 1 (by rfl) ⟨1439333, by rfl⟩ : syracuseStep 1919111 = 2878667) B2878667
theorem B3074183 : Blo 1277957 3074183 := bstep (se 1 (by rfl) ⟨2305637, by rfl⟩ : syracuseStep 3074183 = 4611275) B4611275
theorem B2877587 : Blo 1277957 2877587 := bstep (se 1 (by rfl) ⟨2158190, by rfl⟩ : syracuseStep 2877587 = 4316381) B4316381
theorem B3074201 : Blo 1277957 3074201 := bstep (se 2 (by rfl) ⟨1152825, by rfl⟩ : syracuseStep 3074201 = 2305651) B2305651
theorem B1919147 : Blo 1277957 1919147 := bstep (se 1 (by rfl) ⟨1439360, by rfl⟩ : syracuseStep 1919147 = 2878721) B2878721
theorem B2877641 : Blo 1277957 2877641 := bstep (se 2 (by rfl) ⟨1079115, by rfl⟩ : syracuseStep 2877641 = 2158231) B2158231
theorem B1919177 : Blo 1277957 1919177 := bstep (se 2 (by rfl) ⟨719691, by rfl⟩ : syracuseStep 1919177 = 1439383) B1439383
theorem B3238177 : Blo 1277957 3238177 := bstep (se 2 (by rfl) ⟨1214316, by rfl⟩ : syracuseStep 3238177 = 2428633) B2428633
theorem B1919291 : Blo 1277957 1919291 := bstep (se 1 (by rfl) ⟨1439468, by rfl⟩ : syracuseStep 1919291 = 2878937) B2878937
theorem B3639613 : Blo 1277957 3639613 := bstep (se 3 (by rfl) ⟨682427, by rfl⟩ : syracuseStep 3639613 = 1364855) B1364855
theorem B1919351 : Blo 1277957 1919351 := bstep (se 1 (by rfl) ⟨1439513, by rfl⟩ : syracuseStep 1919351 = 2879027) B2879027
theorem B2075015 : Blo 1277957 2075015 := bstep (se 1 (by rfl) ⟨1556261, by rfl⟩ : syracuseStep 2075015 = 3112523) B3112523
theorem B2156935 : Blo 1277957 2156935 := bstep (se 1 (by rfl) ⟨1617701, by rfl⟩ : syracuseStep 2156935 = 3235403) B3235403
theorem B1919375 : Blo 1277957 1919375 := bstep (se 1 (by rfl) ⟨1439531, by rfl⟩ : syracuseStep 1919375 = 2879063) B2879063
theorem B1919417 : Blo 1277957 1919417 := bstep (se 2 (by rfl) ⟨719781, by rfl⟩ : syracuseStep 1919417 = 1439563) B1439563
theorem B4155833 : Blo 1277957 4155833 := bstep (se 2 (by rfl) ⟨1558437, by rfl⟩ : syracuseStep 4155833 = 3116875) B3116875
theorem B1919495 : Blo 1277957 1919495 := bstep (se 1 (by rfl) ⟨1439621, by rfl⟩ : syracuseStep 1919495 = 2879243) B2879243
theorem B1919531 : Blo 1277957 1919531 := bstep (se 1 (by rfl) ⟨1439648, by rfl⟩ : syracuseStep 1919531 = 2879297) B2879297
theorem B5188157 : Blo 1277957 5188157 := bstep (se 3 (by rfl) ⟨972779, by rfl⟩ : syracuseStep 5188157 = 1945559) B1945559
theorem B1919561 : Blo 1277957 1919561 := bstep (se 2 (by rfl) ⟨719835, by rfl⟩ : syracuseStep 1919561 = 1439671) B1439671
theorem B1919675 : Blo 1277957 1919675 := bstep (se 1 (by rfl) ⟨1439756, by rfl⟩ : syracuseStep 1919675 = 2879513) B2879513
theorem B5188297 : Blo 1277957 5188297 := bstep (se 2 (by rfl) ⟨1945611, by rfl⟩ : syracuseStep 5188297 = 3891223) B3891223
theorem B1919735 : Blo 1277957 1919735 := bstep (se 1 (by rfl) ⟨1439801, by rfl⟩ : syracuseStep 1919735 = 2879603) B2879603
theorem B3640079 : Blo 1277957 3640079 := bstep (se 1 (by rfl) ⟨2730059, by rfl⟩ : syracuseStep 3640079 = 5460119) B5460119
theorem B1919759 : Blo 1277957 1919759 := bstep (se 1 (by rfl) ⟨1439819, by rfl⟩ : syracuseStep 1919759 = 2879639) B2879639
theorem B1919801 : Blo 1277957 1919801 := bstep (se 2 (by rfl) ⟨719925, by rfl⟩ : syracuseStep 1919801 = 1439851) B1439851
theorem B2427707 : Blo 1277957 2427707 := bstep (se 1 (by rfl) ⟨1820780, by rfl⟩ : syracuseStep 2427707 = 3641561) B3641561
theorem B3238775 : Blo 1277957 3238775 := bstep (se 1 (by rfl) ⟨2429081, by rfl⟩ : syracuseStep 3238775 = 4858163) B4858163
theorem B2878343 : Blo 1277957 2878343 := bstep (se 1 (by rfl) ⟨2158757, by rfl⟩ : syracuseStep 2878343 = 4317515) B4317515
theorem B1919879 : Blo 1277957 1919879 := bstep (se 1 (by rfl) ⟨1439909, by rfl⟩ : syracuseStep 1919879 = 2879819) B2879819
theorem B1919915 : Blo 1277957 1919915 := bstep (se 1 (by rfl) ⟨1439936, by rfl⟩ : syracuseStep 1919915 = 2879873) B2879873
theorem B5458873 : Blo 1277957 5458873 := bstep (se 2 (by rfl) ⟨2047077, by rfl⟩ : syracuseStep 5458873 = 4094155) B4094155
theorem B1821703 : Blo 1277957 1821703 := bstep (se 1 (by rfl) ⟨1366277, by rfl⟩ : syracuseStep 1821703 = 2732555) B2732555
theorem B2157583 : Blo 1277957 2157583 := bstep (se 1 (by rfl) ⟨1618187, by rfl⟩ : syracuseStep 2157583 = 3236375) B3236375
theorem B2305039 : Blo 1277957 2305039 := bstep (se 1 (by rfl) ⟨1728779, by rfl⟩ : syracuseStep 2305039 = 3457559) B3457559
theorem B2878523 : Blo 1277957 2878523 := bstep (se 1 (by rfl) ⟨2158892, by rfl⟩ : syracuseStep 2878523 = 4317785) B4317785
theorem B9710765 : Blo 1277957 9710765 := bstep (se 3 (by rfl) ⟨1820768, by rfl⟩ : syracuseStep 9710765 = 3641537) B3641537
theorem B2878649 : Blo 1277957 2878649 := bstep (se 2 (by rfl) ⟨1079493, by rfl⟩ : syracuseStep 2878649 = 2158987) B2158987
theorem B10923245 : Blo 1277957 10923245 := bstep (se 3 (by rfl) ⟨2048108, by rfl⟩ : syracuseStep 10923245 = 4096217) B4096217
theorem B2428193 : Blo 1277957 2428193 := bstep (se 2 (by rfl) ⟨910572, by rfl⟩ : syracuseStep 2428193 = 1821145) B1821145
theorem B6909299 : Blo 1277957 6909299 := bstep (se 1 (by rfl) ⟨5181974, by rfl⟩ : syracuseStep 6909299 = 10363949) B10363949
theorem B12283271 : Blo 1277957 12283271 := bstep (se 1 (by rfl) ⟨9212453, by rfl⟩ : syracuseStep 12283271 = 18424907) B18424907
theorem B7286219 : Blo 1277957 7286219 := bstep (se 1 (by rfl) ⟨5464664, by rfl⟩ : syracuseStep 7286219 = 10929329) B10929329
theorem B2878991 : Blo 1277957 2878991 := bstep (se 1 (by rfl) ⟨2159243, by rfl⟩ : syracuseStep 2878991 = 4318487) B4318487
theorem B15560221 : Blo 1277957 15560221 := bstep (se 3 (by rfl) ⟨2917541, by rfl⟩ : syracuseStep 15560221 = 5835083) B5835083
theorem B2879009 : Blo 1277957 2879009 := bstep (se 2 (by rfl) ⟨1079628, by rfl⟩ : syracuseStep 2879009 = 2159257) B2159257
theorem B2158123 : Blo 1277957 2158123 := bstep (se 1 (by rfl) ⟨1618592, by rfl⟩ : syracuseStep 2158123 = 3237185) B3237185
theorem B1822267 : Blo 1277957 1822267 := bstep (se 1 (by rfl) ⟨1366700, by rfl⟩ : syracuseStep 1822267 = 2733401) B2733401
theorem B2428535 : Blo 1277957 2428535 := bstep (se 1 (by rfl) ⟨1821401, by rfl⟩ : syracuseStep 2428535 = 3642803) B3642803
theorem B1945223 : Blo 1277957 1945223 := bstep (se 1 (by rfl) ⟨1458917, by rfl⟩ : syracuseStep 1945223 = 2917835) B2917835
theorem B2158265 : Blo 1277957 2158265 := bstep (se 2 (by rfl) ⟨809349, by rfl⟩ : syracuseStep 2158265 = 1618699) B1618699
theorem B3739337 : Blo 1277957 3739337 := bstep (se 2 (by rfl) ⟨1402251, by rfl⟩ : syracuseStep 3739337 = 2804503) B2804503
theorem B2461385 : Blo 1277957 2461385 := bstep (se 2 (by rfl) ⟨923019, by rfl⟩ : syracuseStep 2461385 = 1846039) B1846039
theorem B1617671 : Blo 1277957 1617671 := bstep (se 1 (by rfl) ⟨1213253, by rfl⟩ : syracuseStep 1617671 = 2426507) B2426507
theorem B6917903 : Blo 1277957 6917903 := bstep (se 1 (by rfl) ⟨5188427, by rfl⟩ : syracuseStep 6917903 = 10376855) B10376855
theorem B63123245 : Blo 1277957 63123245 := bstep (se 3 (by rfl) ⟨11835608, by rfl⟩ : syracuseStep 63123245 = 23671217) B23671217
theorem B2879351 : Blo 1277957 2879351 := bstep (se 1 (by rfl) ⟨2159513, by rfl⟩ : syracuseStep 2879351 = 4319027) B4319027
theorem B10923929 : Blo 1277957 10923929 := bstep (se 2 (by rfl) ⟨4096473, by rfl⟩ : syracuseStep 10923929 = 8192947) B8192947
theorem B12283811 : Blo 1277957 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B3641345 : Blo 1277957 3641345 := bstep (se 2 (by rfl) ⟨1365504, by rfl⟩ : syracuseStep 3641345 = 2731009) B2731009
theorem B6475787 : Blo 1277957 6475787 := bstep (se 1 (by rfl) ⟨4856840, by rfl⟩ : syracuseStep 6475787 = 9713681) B9713681
theorem B25260055 : Blo 1277957 25260055 := bstep (se 1 (by rfl) ⟨18945041, by rfl⟩ : syracuseStep 25260055 = 37890083) B37890083
theorem B4853789 : Blo 1277957 4853789 := bstep (se 3 (by rfl) ⟨910085, by rfl⟩ : syracuseStep 4853789 = 1820171) B1820171
theorem B4853803 : Blo 1277957 4853803 := bstep (se 1 (by rfl) ⟨3640352, by rfl⟩ : syracuseStep 4853803 = 7280705) B7280705
theorem B2879531 : Blo 1277957 2879531 := bstep (se 1 (by rfl) ⟨2159648, by rfl⟩ : syracuseStep 2879531 = 4319297) B4319297
theorem B4100215 : Blo 1277957 4100215 := bstep (se 1 (by rfl) ⟨3075161, by rfl⟩ : syracuseStep 4100215 = 6150323) B6150323
theorem B6475949 : Blo 1277957 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B7196987 : Blo 1277957 7196987 := bstep (se 1 (by rfl) ⟨5397740, by rfl⟩ : syracuseStep 7196987 = 10795481) B10795481
theorem B2158967 : Blo 1277957 2158967 := bstep (se 1 (by rfl) ⟨1619225, by rfl⟩ : syracuseStep 2158967 = 3238451) B3238451
theorem B1438087 : Blo 1277957 1438087 := bstep (se 1 (by rfl) ⟨1078565, by rfl⟩ : syracuseStep 1438087 = 2157131) B2157131
theorem B1618319 : Blo 1277957 1618319 := bstep (se 1 (by rfl) ⟨1213739, by rfl⟩ : syracuseStep 1618319 = 2427479) B2427479
theorem B2879891 : Blo 1277957 2879891 := bstep (se 1 (by rfl) ⟨2159918, by rfl⟩ : syracuseStep 2879891 = 4319837) B4319837
theorem B1438267 : Blo 1277957 1438267 := bstep (se 1 (by rfl) ⟨1078700, by rfl⟩ : syracuseStep 1438267 = 2157401) B2157401
theorem B23343833 : Blo 1277957 23343833 := bstep (se 2 (by rfl) ⟨8753937, by rfl⟩ : syracuseStep 23343833 = 17507875) B17507875
theorem B3691307 : Blo 1277957 3691307 := bstep (se 1 (by rfl) ⟨2768480, by rfl⟩ : syracuseStep 3691307 = 5536961) B5536961
theorem B2159419 : Blo 1277957 2159419 := bstep (se 1 (by rfl) ⟨1619564, by rfl⟩ : syracuseStep 2159419 = 3239129) B3239129
theorem B6148979 : Blo 1277957 6148979 := bstep (se 1 (by rfl) ⟨4611734, by rfl⟩ : syracuseStep 6148979 = 9223469) B9223469
theorem B5460871 : Blo 1277957 5460871 := bstep (se 1 (by rfl) ⟨4095653, by rfl⟩ : syracuseStep 5460871 = 8191307) B8191307
theorem B2159561 : Blo 1277957 2159561 := bstep (se 2 (by rfl) ⟨809835, by rfl⟩ : syracuseStep 2159561 = 1619671) B1619671
theorem B1438735 : Blo 1277957 1438735 := bstep (se 1 (by rfl) ⟨1079051, by rfl⟩ : syracuseStep 1438735 = 2158103) B2158103
theorem B7279703 : Blo 1277957 7279703 := bstep (se 1 (by rfl) ⟨5459777, by rfl⟩ : syracuseStep 7279703 = 10919555) B10919555
theorem B3691777 : Blo 1277957 3691777 := bstep (se 2 (by rfl) ⟨1384416, by rfl⟩ : syracuseStep 3691777 = 2768833) B2768833
theorem B4314383 : Blo 1277957 4314383 := bstep (se 1 (by rfl) ⟨3235787, by rfl⟩ : syracuseStep 4314383 = 6471575) B6471575
theorem B7886117 : Blo 1277957 7886117 := bstep (se 4 (by rfl) ⟨739323, by rfl⟩ : syracuseStep 7886117 = 1478647) B1478647
theorem B3888427 : Blo 1277957 3888427 := bstep (se 1 (by rfl) ⟨2916320, by rfl⟩ : syracuseStep 3888427 = 5832641) B5832641
theorem B3888499 : Blo 1277957 3888499 := bstep (se 1 (by rfl) ⟨2916374, by rfl⟩ : syracuseStep 3888499 = 5832749) B5832749
theorem B6141329 : Blo 1277957 6141329 := bstep (se 2 (by rfl) ⟨2302998, by rfl⟩ : syracuseStep 6141329 = 4605997) B4605997
theorem B15562169 : Blo 1277957 15562169 := bstep (se 2 (by rfl) ⟨5835813, by rfl⟩ : syracuseStep 15562169 = 11671627) B11671627
theorem B1439239 : Blo 1277957 1439239 := bstep (se 1 (by rfl) ⟨1079429, by rfl⟩ : syracuseStep 1439239 = 2158859) B2158859
theorem B4314653 : Blo 1277957 4314653 := bstep (se 3 (by rfl) ⟨808997, by rfl⟩ : syracuseStep 4314653 = 1617995) B1617995
theorem B9713195 : Blo 1277957 9713195 := bstep (se 1 (by rfl) ⟨7284896, by rfl⟩ : syracuseStep 9713195 = 14569793) B14569793
theorem B3642995 : Blo 1277957 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B1439419 : Blo 1277957 1439419 := bstep (se 1 (by rfl) ⟨1079564, by rfl⟩ : syracuseStep 1439419 = 2159129) B2159129
theorem B6477569 : Blo 1277957 6477569 := bstep (se 2 (by rfl) ⟨2429088, by rfl⟩ : syracuseStep 6477569 = 4858177) B4858177
theorem B15554339 : Blo 1277957 15554339 := bstep (se 1 (by rfl) ⟨11665754, by rfl⟩ : syracuseStep 15554339 = 23331509) B23331509
theorem B18446129 : Blo 1277957 18446129 := bstep (se 2 (by rfl) ⟨6917298, by rfl⟩ : syracuseStep 18446129 = 13834597) B13834597
theorem B8189747 : Blo 1277957 8189747 := bstep (se 1 (by rfl) ⟨6142310, by rfl⟩ : syracuseStep 8189747 = 12284621) B12284621
theorem B9705419 : Blo 1277957 9705419 := bstep (se 1 (by rfl) ⟨7279064, by rfl⟩ : syracuseStep 9705419 = 14558129) B14558129
theorem B5609425 : Blo 1277957 5609425 := bstep (se 2 (by rfl) ⟨2103534, by rfl⟩ : syracuseStep 5609425 = 4207069) B4207069
theorem B37910551 : Blo 1277957 37910551 := bstep (se 1 (by rfl) ⟨28432913, by rfl⟩ : syracuseStep 37910551 = 56865827) B56865827
theorem B3889181 : Blo 1277957 3889181 := bstep (se 3 (by rfl) ⟨729221, by rfl⟩ : syracuseStep 3889181 = 1458443) B1458443
theorem B6567965 : Blo 1277957 6567965 := bstep (se 3 (by rfl) ⟨1231493, by rfl⟩ : syracuseStep 6567965 = 2462987) B2462987
theorem B16381997 : Blo 1277957 16381997 := bstep (se 3 (by rfl) ⟨3071624, by rfl⟩ : syracuseStep 16381997 = 6143249) B6143249
theorem B3643451 : Blo 1277957 3643451 := bstep (se 1 (by rfl) ⟨2732588, by rfl⟩ : syracuseStep 3643451 = 5465177) B5465177
theorem B9214013 : Blo 1277957 9214013 := bstep (se 3 (by rfl) ⟨1727627, by rfl⟩ : syracuseStep 9214013 = 3455255) B3455255
theorem B1439887 : Blo 1277957 1439887 := bstep (se 1 (by rfl) ⟨1079915, by rfl⟩ : syracuseStep 1439887 = 2159831) B2159831
theorem B24574225 : Blo 1277957 24574225 := bstep (se 2 (by rfl) ⟨9215334, by rfl⟩ : syracuseStep 24574225 = 18430669) B18430669
theorem B7993753 : Blo 1277957 7993753 := bstep (se 2 (by rfl) ⟨2997657, by rfl⟩ : syracuseStep 7993753 = 5995315) B5995315
theorem B6478379 : Blo 1277957 6478379 := bstep (se 1 (by rfl) ⟨4858784, by rfl⟩ : syracuseStep 6478379 = 9717569) B9717569
theorem B3644203 : Blo 1277957 3644203 := bstep (se 1 (by rfl) ⟨2733152, by rfl⟩ : syracuseStep 3644203 = 5466305) B5466305
theorem B16399219 : Blo 1277957 16399219 := bstep (se 1 (by rfl) ⟨12299414, by rfl⟩ : syracuseStep 16399219 = 24598829) B24598829
theorem B4316057 : Blo 1277957 4316057 := bstep (se 2 (by rfl) ⟨1618521, by rfl⟩ : syracuseStep 4316057 = 3237043) B3237043
theorem B6470603 : Blo 1277957 6470603 := bstep (se 1 (by rfl) ⟨4852952, by rfl⟩ : syracuseStep 6470603 = 9705905) B9705905
theorem B3644477 : Blo 1277957 3644477 := bstep (se 3 (by rfl) ⟨683339, by rfl⟩ : syracuseStep 3644477 = 1366679) B1366679
theorem B10378477 : Blo 1277957 10378477 := bstep (se 3 (by rfl) ⟨1945964, by rfl⟩ : syracuseStep 10378477 = 3891929) B3891929
theorem B6470927 : Blo 1277957 6470927 := bstep (se 1 (by rfl) ⟨4853195, by rfl⟩ : syracuseStep 6470927 = 9706391) B9706391
theorem B7781669 : Blo 1277957 7781669 := bstep (se 4 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 7781669 = 1459063) B1459063
theorem B31112657 : Blo 1277957 31112657 := bstep (se 2 (by rfl) ⟨11667246, by rfl⟩ : syracuseStep 31112657 = 23334493) B23334493
theorem B10927619 : Blo 1277957 10927619 := bstep (se 1 (by rfl) ⟨8195714, by rfl⟩ : syracuseStep 10927619 = 16391429) B16391429
theorem B1457723 : Blo 1277957 1457723 := bstep (se 1 (by rfl) ⟨1093292, by rfl⟩ : syracuseStep 1457723 = 2186585) B2186585
theorem B4316759 : Blo 1277957 4316759 := bstep (se 1 (by rfl) ⟨3237569, by rfl⟩ : syracuseStep 4316759 = 6475139) B6475139
theorem B2768503 : Blo 1277957 2768503 := bstep (se 1 (by rfl) ⟨2076377, by rfl⟩ : syracuseStep 2768503 = 4152755) B4152755
theorem B3235585 : Blo 1277957 3235585 := bstep (se 2 (by rfl) ⟨1213344, by rfl⟩ : syracuseStep 3235585 = 2426689) B2426689
theorem B6479675 : Blo 1277957 6479675 := bstep (se 1 (by rfl) ⟨4859756, by rfl⟩ : syracuseStep 6479675 = 9719513) B9719513
theorem B4095859 : Blo 1277957 4095859 := bstep (se 1 (by rfl) ⟨3071894, by rfl⟩ : syracuseStep 4095859 = 6143789) B6143789
theorem B4096001 : Blo 1277957 4096001 := bstep (se 2 (by rfl) ⟨1536000, by rfl⟩ : syracuseStep 4096001 = 3072001) B3072001
theorem B4317191 : Blo 1277957 4317191 := bstep (se 1 (by rfl) ⟨3237893, by rfl⟩ : syracuseStep 4317191 = 6475787) B6475787
theorem B3235859 : Blo 1277957 3235859 := bstep (se 1 (by rfl) ⟨2426894, by rfl⟩ : syracuseStep 3235859 = 4853789) B4853789
theorem B1277991 : Blo 1277957 1277991 := bstep (se 1 (by rfl) ⟨958493, by rfl⟩ : syracuseStep 1277991 = 1916987) B1916987
theorem B6225977 : Blo 1277957 6225977 := bstep (se 2 (by rfl) ⟨2334741, by rfl⟩ : syracuseStep 6225977 = 4669483) B4669483
theorem B6471737 : Blo 1277957 6471737 := bstep (se 2 (by rfl) ⟨2426901, by rfl⟩ : syracuseStep 6471737 = 4853803) B4853803
theorem B10371149 : Blo 1277957 10371149 := bstep (se 3 (by rfl) ⟨1944590, by rfl⟩ : syracuseStep 10371149 = 3889181) B3889181
theorem B1278031 : Blo 1277957 1278031 := bstep (se 1 (by rfl) ⟨958523, by rfl⟩ : syracuseStep 1278031 = 1917047) B1917047
theorem B1278047 : Blo 1277957 1278047 := bstep (se 1 (by rfl) ⟨958535, by rfl⟩ : syracuseStep 1278047 = 1917071) B1917071
theorem B4317299 : Blo 1277957 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B1278075 : Blo 1277957 1278075 := bstep (se 1 (by rfl) ⟨958556, by rfl⟩ : syracuseStep 1278075 = 1917113) B1917113
theorem B63971477 : Blo 1277957 63971477 := bstep (se 6 (by rfl) ⟨1499331, by rfl⟩ : syracuseStep 63971477 = 2998663) B2998663
theorem B1278127 : Blo 1277957 1278127 := bstep (se 1 (by rfl) ⟨958595, by rfl⟩ : syracuseStep 1278127 = 1917191) B1917191
theorem B1278151 : Blo 1277957 1278151 := bstep (se 1 (by rfl) ⟨958613, by rfl⟩ : syracuseStep 1278151 = 1917227) B1917227
theorem B1278171 : Blo 1277957 1278171 := bstep (se 1 (by rfl) ⟨958628, by rfl⟩ : syracuseStep 1278171 = 1917257) B1917257
theorem B1278247 : Blo 1277957 1278247 := bstep (se 1 (by rfl) ⟨958685, by rfl⟩ : syracuseStep 1278247 = 1917371) B1917371
theorem B1278287 : Blo 1277957 1278287 := bstep (se 1 (by rfl) ⟨958715, by rfl⟩ : syracuseStep 1278287 = 1917431) B1917431
theorem B1278303 : Blo 1277957 1278303 := bstep (se 1 (by rfl) ⟨958727, by rfl⟩ : syracuseStep 1278303 = 1917455) B1917455
theorem B1278331 : Blo 1277957 1278331 := bstep (se 1 (by rfl) ⟨958748, by rfl⟩ : syracuseStep 1278331 = 1917497) B1917497
theorem B4317569 : Blo 1277957 4317569 := bstep (se 2 (by rfl) ⟨1619088, by rfl⟩ : syracuseStep 4317569 = 3238177) B3238177
theorem B1917359 : Blo 1277957 1917359 := bstep (se 1 (by rfl) ⟨1438019, by rfl⟩ : syracuseStep 1917359 = 2876039) B2876039
theorem B1278383 : Blo 1277957 1278383 := bstep (se 1 (by rfl) ⟨958787, by rfl⟩ : syracuseStep 1278383 = 1917575) B1917575
theorem B1278407 : Blo 1277957 1278407 := bstep (se 1 (by rfl) ⟨958805, by rfl⟩ : syracuseStep 1278407 = 1917611) B1917611
theorem B1278427 : Blo 1277957 1278427 := bstep (se 1 (by rfl) ⟨958820, by rfl⟩ : syracuseStep 1278427 = 1917641) B1917641
theorem B18432515 : Blo 1277957 18432515 := bstep (se 1 (by rfl) ⟨13824386, by rfl⟩ : syracuseStep 18432515 = 27648773) B27648773
theorem B2875913 : Blo 1277957 2875913 := bstep (se 2 (by rfl) ⟨1078467, by rfl⟩ : syracuseStep 2875913 = 2156935) B2156935
theorem B1917449 : Blo 1277957 1917449 := bstep (se 2 (by rfl) ⟨719043, by rfl⟩ : syracuseStep 1917449 = 1438087) B1438087
theorem B2048519 : Blo 1277957 2048519 := bstep (se 1 (by rfl) ⟨1536389, by rfl⟩ : syracuseStep 2048519 = 3072779) B3072779
theorem B170533397 : Blo 1277957 170533397 := bstep (se 6 (by rfl) ⟨3996876, by rfl⟩ : syracuseStep 170533397 = 7993753) B7993753
theorem B1917479 : Blo 1277957 1917479 := bstep (se 1 (by rfl) ⟨1438109, by rfl⟩ : syracuseStep 1917479 = 2876219) B2876219
theorem B1278503 : Blo 1277957 1278503 := bstep (se 1 (by rfl) ⟨958877, by rfl⟩ : syracuseStep 1278503 = 1917755) B1917755
theorem B1278543 : Blo 1277957 1278543 := bstep (se 1 (by rfl) ⟨958907, by rfl⟩ : syracuseStep 1278543 = 1917815) B1917815
theorem B1278559 : Blo 1277957 1278559 := bstep (se 1 (by rfl) ⟨958919, by rfl⟩ : syracuseStep 1278559 = 1917839) B1917839
theorem B1917563 : Blo 1277957 1917563 := bstep (se 1 (by rfl) ⟨1438172, by rfl⟩ : syracuseStep 1917563 = 2876345) B2876345
theorem B1278587 : Blo 1277957 1278587 := bstep (se 1 (by rfl) ⟨958940, by rfl⟩ : syracuseStep 1278587 = 1917881) B1917881
theorem B1278639 : Blo 1277957 1278639 := bstep (se 1 (by rfl) ⟨958979, by rfl⟩ : syracuseStep 1278639 = 1917959) B1917959
theorem B1278663 : Blo 1277957 1278663 := bstep (se 1 (by rfl) ⟨958997, by rfl⟩ : syracuseStep 1278663 = 1917995) B1917995
theorem B6914771 : Blo 1277957 6914771 := bstep (se 1 (by rfl) ⟨5186078, by rfl⟩ : syracuseStep 6914771 = 10372157) B10372157
theorem B1278683 : Blo 1277957 1278683 := bstep (se 1 (by rfl) ⟨959012, by rfl⟩ : syracuseStep 1278683 = 1918025) B1918025
theorem B1917689 : Blo 1277957 1917689 := bstep (se 2 (by rfl) ⟨719133, by rfl⟩ : syracuseStep 1917689 = 1438267) B1438267
theorem B21029645 : Blo 1277957 21029645 := bstep (se 3 (by rfl) ⟨3943058, by rfl⟩ : syracuseStep 21029645 = 7886117) B7886117
theorem B1278759 : Blo 1277957 1278759 := bstep (se 1 (by rfl) ⟨959069, by rfl⟩ : syracuseStep 1278759 = 1918139) B1918139
theorem B1278799 : Blo 1277957 1278799 := bstep (se 1 (by rfl) ⟨959099, by rfl⟩ : syracuseStep 1278799 = 1918199) B1918199
theorem B2876255 : Blo 1277957 2876255 := bstep (se 1 (by rfl) ⟨2157191, by rfl⟩ : syracuseStep 2876255 = 4314383) B4314383
theorem B1917791 : Blo 1277957 1917791 := bstep (se 1 (by rfl) ⟨1438343, by rfl⟩ : syracuseStep 1917791 = 2876687) B2876687
theorem B1278815 : Blo 1277957 1278815 := bstep (se 1 (by rfl) ⟨959111, by rfl⟩ : syracuseStep 1278815 = 1918223) B1918223
theorem B1917803 : Blo 1277957 1917803 := bstep (se 1 (by rfl) ⟨1438352, by rfl⟩ : syracuseStep 1917803 = 2876705) B2876705
theorem B1278843 : Blo 1277957 1278843 := bstep (se 1 (by rfl) ⟨959132, by rfl⟩ : syracuseStep 1278843 = 1918265) B1918265
theorem B1278895 : Blo 1277957 1278895 := bstep (se 1 (by rfl) ⟨959171, by rfl⟩ : syracuseStep 1278895 = 1918343) B1918343
theorem B1278919 : Blo 1277957 1278919 := bstep (se 1 (by rfl) ⟨959189, by rfl⟩ : syracuseStep 1278919 = 1918379) B1918379
theorem B1278939 : Blo 1277957 1278939 := bstep (se 1 (by rfl) ⟨959204, by rfl⟩ : syracuseStep 1278939 = 1918409) B1918409
theorem B2876435 : Blo 1277957 2876435 := bstep (se 1 (by rfl) ⟨2157326, by rfl⟩ : syracuseStep 2876435 = 4314653) B4314653
theorem B1819687 : Blo 1277957 1819687 := bstep (se 1 (by rfl) ⟨1364765, by rfl⟩ : syracuseStep 1819687 = 2729531) B2729531
theorem B1279015 : Blo 1277957 1279015 := bstep (se 1 (by rfl) ⟨959261, by rfl⟩ : syracuseStep 1279015 = 1918523) B1918523
theorem B4858937 : Blo 1277957 4858937 := bstep (se 2 (by rfl) ⟨1822101, by rfl⟩ : syracuseStep 4858937 = 3644203) B3644203
theorem B1918031 : Blo 1277957 1918031 := bstep (se 1 (by rfl) ⟨1438523, by rfl⟩ : syracuseStep 1918031 = 2877047) B2877047
theorem B1279055 : Blo 1277957 1279055 := bstep (se 1 (by rfl) ⟨959291, by rfl⟩ : syracuseStep 1279055 = 1918583) B1918583
theorem B1279071 : Blo 1277957 1279071 := bstep (se 1 (by rfl) ⟨959303, by rfl⟩ : syracuseStep 1279071 = 1918607) B1918607
theorem B1279099 : Blo 1277957 1279099 := bstep (se 1 (by rfl) ⟨959324, by rfl⟩ : syracuseStep 1279099 = 1918649) B1918649
theorem B21865625 : Blo 1277957 21865625 := bstep (se 2 (by rfl) ⟨8199609, by rfl⟩ : syracuseStep 21865625 = 16399219) B16399219
theorem B4318379 : Blo 1277957 4318379 := bstep (se 1 (by rfl) ⟨3238784, by rfl⟩ : syracuseStep 4318379 = 6477569) B6477569
theorem B1279151 : Blo 1277957 1279151 := bstep (se 1 (by rfl) ⟨959363, by rfl⟩ : syracuseStep 1279151 = 1918727) B1918727
theorem B1918151 : Blo 1277957 1918151 := bstep (se 1 (by rfl) ⟨1438613, by rfl⟩ : syracuseStep 1918151 = 2877227) B2877227
theorem B1279175 : Blo 1277957 1279175 := bstep (se 1 (by rfl) ⟨959381, by rfl⟩ : syracuseStep 1279175 = 1918763) B1918763
theorem B12297419 : Blo 1277957 12297419 := bstep (se 1 (by rfl) ⟨9223064, by rfl⟩ : syracuseStep 12297419 = 18446129) B18446129
theorem B1279195 : Blo 1277957 1279195 := bstep (se 1 (by rfl) ⟨959396, by rfl⟩ : syracuseStep 1279195 = 1918793) B1918793
theorem B1279271 : Blo 1277957 1279271 := bstep (se 1 (by rfl) ⟨959453, by rfl⟩ : syracuseStep 1279271 = 1918907) B1918907
theorem B1279311 : Blo 1277957 1279311 := bstep (se 1 (by rfl) ⟨959483, by rfl⟩ : syracuseStep 1279311 = 1918967) B1918967
theorem B1279327 : Blo 1277957 1279327 := bstep (se 1 (by rfl) ⟨959495, by rfl⟩ : syracuseStep 1279327 = 1918991) B1918991
theorem B2876777 : Blo 1277957 2876777 := bstep (se 2 (by rfl) ⟨1078791, by rfl⟩ : syracuseStep 2876777 = 2157583) B2157583
theorem B1918313 : Blo 1277957 1918313 := bstep (se 2 (by rfl) ⟨719367, by rfl⟩ : syracuseStep 1918313 = 1438735) B1438735
theorem B3073385 : Blo 1277957 3073385 := bstep (se 2 (by rfl) ⟨1152519, by rfl⟩ : syracuseStep 3073385 = 2305039) B2305039
theorem B10921331 : Blo 1277957 10921331 := bstep (se 1 (by rfl) ⟨8190998, by rfl⟩ : syracuseStep 10921331 = 16381997) B16381997
theorem B1279355 : Blo 1277957 1279355 := bstep (se 1 (by rfl) ⟨959516, by rfl⟩ : syracuseStep 1279355 = 1919033) B1919033
theorem B2426287 : Blo 1277957 2426287 := bstep (se 1 (by rfl) ⟨1819715, by rfl⟩ : syracuseStep 2426287 = 3639431) B3639431
theorem B1279407 : Blo 1277957 1279407 := bstep (se 1 (by rfl) ⟨959555, by rfl⟩ : syracuseStep 1279407 = 1919111) B1919111
theorem B2049455 : Blo 1277957 2049455 := bstep (se 1 (by rfl) ⟨1537091, by rfl⟩ : syracuseStep 2049455 = 3074183) B3074183
theorem B1918391 : Blo 1277957 1918391 := bstep (se 1 (by rfl) ⟨1438793, by rfl⟩ : syracuseStep 1918391 = 2877587) B2877587
theorem B2049467 : Blo 1277957 2049467 := bstep (se 1 (by rfl) ⟨1537100, by rfl⟩ : syracuseStep 2049467 = 3074201) B3074201
theorem B1279431 : Blo 1277957 1279431 := bstep (se 1 (by rfl) ⟨959573, by rfl⟩ : syracuseStep 1279431 = 1919147) B1919147
theorem B1918427 : Blo 1277957 1918427 := bstep (se 1 (by rfl) ⟨1438820, by rfl⟩ : syracuseStep 1918427 = 2877641) B2877641
theorem B1279451 : Blo 1277957 1279451 := bstep (se 1 (by rfl) ⟨959588, by rfl⟩ : syracuseStep 1279451 = 1919177) B1919177
theorem B1279527 : Blo 1277957 1279527 := bstep (se 1 (by rfl) ⟨959645, by rfl⟩ : syracuseStep 1279527 = 1919291) B1919291
theorem B1279567 : Blo 1277957 1279567 := bstep (se 1 (by rfl) ⟨959675, by rfl⟩ : syracuseStep 1279567 = 1919351) B1919351
theorem B1279583 : Blo 1277957 1279583 := bstep (se 1 (by rfl) ⟨959687, by rfl⟩ : syracuseStep 1279583 = 1919375) B1919375
theorem B1279611 : Blo 1277957 1279611 := bstep (se 1 (by rfl) ⟨959708, by rfl⟩ : syracuseStep 1279611 = 1919417) B1919417
theorem B13837969 : Blo 1277957 13837969 := bstep (se 2 (by rfl) ⟨5189238, by rfl⟩ : syracuseStep 13837969 = 10378477) B10378477
theorem B1279663 : Blo 1277957 1279663 := bstep (se 1 (by rfl) ⟨959747, by rfl⟩ : syracuseStep 1279663 = 1919495) B1919495
theorem B4318919 : Blo 1277957 4318919 := bstep (se 1 (by rfl) ⟨3239189, by rfl⟩ : syracuseStep 4318919 = 6478379) B6478379
theorem B1279687 : Blo 1277957 1279687 := bstep (se 1 (by rfl) ⟨959765, by rfl⟩ : syracuseStep 1279687 = 1919531) B1919531
theorem B3458771 : Blo 1277957 3458771 := bstep (se 1 (by rfl) ⟨2594078, by rfl⟩ : syracuseStep 3458771 = 5188157) B5188157
theorem B1279707 : Blo 1277957 1279707 := bstep (se 1 (by rfl) ⟨959780, by rfl⟩ : syracuseStep 1279707 = 1919561) B1919561
theorem B1279783 : Blo 1277957 1279783 := bstep (se 1 (by rfl) ⟨959837, by rfl⟩ : syracuseStep 1279783 = 1919675) B1919675
theorem B1279823 : Blo 1277957 1279823 := bstep (se 1 (by rfl) ⟨959867, by rfl⟩ : syracuseStep 1279823 = 1919735) B1919735
theorem B1279839 : Blo 1277957 1279839 := bstep (se 1 (by rfl) ⟨959879, by rfl⟩ : syracuseStep 1279839 = 1919759) B1919759
theorem B6563693 : Blo 1277957 6563693 := bstep (se 3 (by rfl) ⟨1230692, by rfl⟩ : syracuseStep 6563693 = 2461385) B2461385
theorem B1279867 : Blo 1277957 1279867 := bstep (se 1 (by rfl) ⟨959900, by rfl⟩ : syracuseStep 1279867 = 1919801) B1919801
theorem B1918895 : Blo 1277957 1918895 := bstep (se 1 (by rfl) ⟨1439171, by rfl⟩ : syracuseStep 1918895 = 2878343) B2878343
theorem B1279919 : Blo 1277957 1279919 := bstep (se 1 (by rfl) ⟨959939, by rfl⟩ : syracuseStep 1279919 = 1919879) B1919879
theorem B2877371 : Blo 1277957 2877371 := bstep (se 1 (by rfl) ⟨2158028, by rfl⟩ : syracuseStep 2877371 = 4316057) B4316057
theorem B1279943 : Blo 1277957 1279943 := bstep (se 1 (by rfl) ⟨959957, by rfl⟩ : syracuseStep 1279943 = 1919915) B1919915
theorem B1918985 : Blo 1277957 1918985 := bstep (se 2 (by rfl) ⟨719619, by rfl⟩ : syracuseStep 1918985 = 1439239) B1439239
theorem B1919015 : Blo 1277957 1919015 := bstep (se 1 (by rfl) ⟨1439261, by rfl⟩ : syracuseStep 1919015 = 2878523) B2878523
theorem B2877497 : Blo 1277957 2877497 := bstep (se 2 (by rfl) ⟨1079061, by rfl⟩ : syracuseStep 2877497 = 2158123) B2158123
theorem B6473843 : Blo 1277957 6473843 := bstep (se 1 (by rfl) ⟨4855382, by rfl⟩ : syracuseStep 6473843 = 9710765) B9710765
theorem B1919099 : Blo 1277957 1919099 := bstep (se 1 (by rfl) ⟨1439324, by rfl⟩ : syracuseStep 1919099 = 2878649) B2878649
theorem B5187779 : Blo 1277957 5187779 := bstep (se 1 (by rfl) ⟨3890834, by rfl⟩ : syracuseStep 5187779 = 7781669) B7781669
theorem B4606199 : Blo 1277957 4606199 := bstep (se 1 (by rfl) ⟨3454649, by rfl⟩ : syracuseStep 4606199 = 6909299) B6909299
theorem B1919225 : Blo 1277957 1919225 := bstep (se 2 (by rfl) ⟨719709, by rfl⟩ : syracuseStep 1919225 = 1439419) B1439419
theorem B7285079 : Blo 1277957 7285079 := bstep (se 1 (by rfl) ⟨5463809, by rfl⟩ : syracuseStep 7285079 = 10927619) B10927619
theorem B1919327 : Blo 1277957 1919327 := bstep (se 1 (by rfl) ⟨1439495, by rfl⟩ : syracuseStep 1919327 = 2878991) B2878991
theorem B1919339 : Blo 1277957 1919339 := bstep (se 1 (by rfl) ⟨1439504, by rfl⟩ : syracuseStep 1919339 = 2879009) B2879009
theorem B2877839 : Blo 1277957 2877839 := bstep (se 1 (by rfl) ⟨2158379, by rfl⟩ : syracuseStep 2877839 = 4316759) B4316759
theorem B1296815 : Blo 1277957 1296815 := bstep (se 1 (by rfl) ⟨972611, by rfl⟩ : syracuseStep 1296815 = 1945223) B1945223
theorem B2492891 : Blo 1277957 2492891 := bstep (se 1 (by rfl) ⟨1869668, by rfl⟩ : syracuseStep 2492891 = 3739337) B3739337
theorem B4319783 : Blo 1277957 4319783 := bstep (se 1 (by rfl) ⟨3239837, by rfl⟩ : syracuseStep 4319783 = 6479675) B6479675
theorem B1919567 : Blo 1277957 1919567 := bstep (se 1 (by rfl) ⟨1439675, by rfl⟩ : syracuseStep 1919567 = 2879351) B2879351
theorem B2427563 : Blo 1277957 2427563 := bstep (se 1 (by rfl) ⟨1820672, by rfl⟩ : syracuseStep 2427563 = 3641345) B3641345
theorem B7383737 : Blo 1277957 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B1919687 : Blo 1277957 1919687 := bstep (se 1 (by rfl) ⟨1439765, by rfl⟩ : syracuseStep 1919687 = 2879531) B2879531
theorem B50547401 : Blo 1277957 50547401 := bstep (se 2 (by rfl) ⟨18955275, by rfl⟩ : syracuseStep 50547401 = 37910551) B37910551
theorem B2878163 : Blo 1277957 2878163 := bstep (se 1 (by rfl) ⟨2158622, by rfl⟩ : syracuseStep 2878163 = 4317245) B4317245
theorem B478874389 : Blo 1277957 478874389 := bstep (se 6 (by rfl) ⟨11223618, by rfl⟩ : syracuseStep 478874389 = 22447237) B22447237
theorem B134720293 : Blo 1277957 134720293 := bstep (se 4 (by rfl) ⟨12630027, by rfl⟩ : syracuseStep 134720293 = 25260055) B25260055
theorem B5466953 : Blo 1277957 5466953 := bstep (se 2 (by rfl) ⟨2050107, by rfl⟩ : syracuseStep 5466953 = 4100215) B4100215
theorem B1919849 : Blo 1277957 1919849 := bstep (se 2 (by rfl) ⟨719943, by rfl⟩ : syracuseStep 1919849 = 1439887) B1439887
theorem B2157455 : Blo 1277957 2157455 := bstep (se 1 (by rfl) ⟨1618091, by rfl⟩ : syracuseStep 2157455 = 3236183) B3236183
theorem B1919927 : Blo 1277957 1919927 := bstep (se 1 (by rfl) ⟨1439945, by rfl⟩ : syracuseStep 1919927 = 2879891) B2879891
theorem B26258455 : Blo 1277957 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B4852817 : Blo 1277957 4852817 := bstep (se 2 (by rfl) ⟨1819806, by rfl⟩ : syracuseStep 4852817 = 3639613) B3639613
theorem B2157691 : Blo 1277957 2157691 := bstep (se 1 (by rfl) ⟨1618268, by rfl⟩ : syracuseStep 2157691 = 3236537) B3236537
theorem B2460871 : Blo 1277957 2460871 := bstep (se 1 (by rfl) ⟨1845653, by rfl⟩ : syracuseStep 2460871 = 3691307) B3691307
theorem B4099319 : Blo 1277957 4099319 := bstep (se 1 (by rfl) ⟨3074489, by rfl⟩ : syracuseStep 4099319 = 6148979) B6148979
theorem B4853135 : Blo 1277957 4853135 := bstep (se 1 (by rfl) ⟨3639851, by rfl⟩ : syracuseStep 4853135 = 7279703) B7279703
theorem B2076047 : Blo 1277957 2076047 := bstep (se 1 (by rfl) ⟨1557035, by rfl⟩ : syracuseStep 2076047 = 3114071) B3114071
theorem B3239311 : Blo 1277957 3239311 := bstep (se 1 (by rfl) ⟨2429483, by rfl⟩ : syracuseStep 3239311 = 4858967) B4858967
theorem B2731529 : Blo 1277957 2731529 := bstep (se 2 (by rfl) ⟨1024323, by rfl⟩ : syracuseStep 2731529 = 2048647) B2048647
theorem B6917729 : Blo 1277957 6917729 := bstep (se 2 (by rfl) ⟨2594148, by rfl⟩ : syracuseStep 6917729 = 5188297) B5188297
theorem B10374779 : Blo 1277957 10374779 := bstep (se 1 (by rfl) ⟨7781084, by rfl⟩ : syracuseStep 10374779 = 15562169) B15562169
theorem B2879099 : Blo 1277957 2879099 := bstep (se 1 (by rfl) ⟨2159324, by rfl⟩ : syracuseStep 2879099 = 4318649) B4318649
theorem B9711251 : Blo 1277957 9711251 := bstep (se 1 (by rfl) ⟨7283438, by rfl⟩ : syracuseStep 9711251 = 14566877) B14566877
theorem B5533373 : Blo 1277957 5533373 := bstep (se 3 (by rfl) ⟨1037507, by rfl⟩ : syracuseStep 5533373 = 2075015) B2075015
theorem B6475463 : Blo 1277957 6475463 := bstep (se 1 (by rfl) ⟨4856597, by rfl⟩ : syracuseStep 6475463 = 9713195) B9713195
theorem B3239635 : Blo 1277957 3239635 := bstep (se 1 (by rfl) ⟨2429726, by rfl⟩ : syracuseStep 3239635 = 4859453) B4859453
theorem B2879225 : Blo 1277957 2879225 := bstep (se 2 (by rfl) ⟨1079709, by rfl⟩ : syracuseStep 2879225 = 2159419) B2159419
theorem B1535851 : Blo 1277957 1535851 := bstep (se 1 (by rfl) ⟨1151888, by rfl⟩ : syracuseStep 1535851 = 2303777) B2303777
theorem B5459831 : Blo 1277957 5459831 := bstep (se 1 (by rfl) ⟨4094873, by rfl⟩ : syracuseStep 5459831 = 8189747) B8189747
theorem B7278497 : Blo 1277957 7278497 := bstep (se 2 (by rfl) ⟨2729436, by rfl⟩ : syracuseStep 7278497 = 5458873) B5458873
theorem B2158555 : Blo 1277957 2158555 := bstep (se 1 (by rfl) ⟨1618916, by rfl⟩ : syracuseStep 2158555 = 3237833) B3237833
theorem B2879495 : Blo 1277957 2879495 := bstep (se 1 (by rfl) ⟨2159621, by rfl⟩ : syracuseStep 2879495 = 4319243) B4319243
theorem B2428937 : Blo 1277957 2428937 := bstep (se 2 (by rfl) ⟨910851, by rfl⟩ : syracuseStep 2428937 = 1821703) B1821703
theorem B4378643 : Blo 1277957 4378643 := bstep (se 1 (by rfl) ⟨3283982, by rfl⟩ : syracuseStep 4378643 = 6567965) B6567965
theorem B2428967 : Blo 1277957 2428967 := bstep (se 1 (by rfl) ⟨1821725, by rfl⟩ : syracuseStep 2428967 = 3643451) B3643451
theorem B2879567 : Blo 1277957 2879567 := bstep (se 1 (by rfl) ⟨2159675, by rfl⟩ : syracuseStep 2879567 = 4319351) B4319351
theorem B3887261 : Blo 1277957 3887261 := bstep (se 3 (by rfl) ⟨728861, by rfl⟩ : syracuseStep 3887261 = 1457723) B1457723
theorem B4854077 : Blo 1277957 4854077 := bstep (se 3 (by rfl) ⟨910139, by rfl⟩ : syracuseStep 4854077 = 1820279) B1820279
theorem B1618471 : Blo 1277957 1618471 := bstep (se 1 (by rfl) ⟨1213853, by rfl⟩ : syracuseStep 1618471 = 2427707) B2427707
theorem B2159183 : Blo 1277957 2159183 := bstep (se 1 (by rfl) ⟨1619387, by rfl⟩ : syracuseStep 2159183 = 3238775) B3238775
theorem B4313735 : Blo 1277957 4313735 := bstep (se 1 (by rfl) ⟨3235301, by rfl⟩ : syracuseStep 4313735 = 6470603) B6470603
theorem B4313789 : Blo 1277957 4313789 := bstep (se 3 (by rfl) ⟨808835, by rfl⟩ : syracuseStep 4313789 = 1617671) B1617671
theorem B20746961 : Blo 1277957 20746961 := bstep (se 2 (by rfl) ⟨7780110, by rfl⟩ : syracuseStep 20746961 = 15560221) B15560221
theorem B2429651 : Blo 1277957 2429651 := bstep (se 1 (by rfl) ⟨1822238, by rfl⟩ : syracuseStep 2429651 = 3644477) B3644477
theorem B2429689 : Blo 1277957 2429689 := bstep (se 2 (by rfl) ⟨911133, by rfl⟩ : syracuseStep 2429689 = 1822267) B1822267
theorem B3691337 : Blo 1277957 3691337 := bstep (se 2 (by rfl) ⟨1384251, by rfl⟩ : syracuseStep 3691337 = 2768503) B2768503
theorem B4313951 : Blo 1277957 4313951 := bstep (se 1 (by rfl) ⟨3235463, by rfl⟩ : syracuseStep 4313951 = 6470927) B6470927
theorem B1618795 : Blo 1277957 1618795 := bstep (se 1 (by rfl) ⟨1214096, by rfl⟩ : syracuseStep 1618795 = 2428193) B2428193
theorem B8188847 : Blo 1277957 8188847 := bstep (se 1 (by rfl) ⟨6141635, by rfl⟩ : syracuseStep 8188847 = 12283271) B12283271
theorem B4314113 : Blo 1277957 4314113 := bstep (se 2 (by rfl) ⟨1617792, by rfl⟩ : syracuseStep 4314113 = 3235585) B3235585
theorem B1619023 : Blo 1277957 1619023 := bstep (se 1 (by rfl) ⟨1214267, by rfl⟩ : syracuseStep 1619023 = 2428535) B2428535
theorem B1438843 : Blo 1277957 1438843 := bstep (se 1 (by rfl) ⟨1079132, by rfl⟩ : syracuseStep 1438843 = 2158265) B2158265
theorem B5461145 : Blo 1277957 5461145 := bstep (se 2 (by rfl) ⟨2047929, by rfl⟩ : syracuseStep 5461145 = 4095859) B4095859
theorem B8189207 : Blo 1277957 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B4797991 : Blo 1277957 4797991 := bstep (se 1 (by rfl) ⟨3598493, by rfl⟩ : syracuseStep 4797991 = 7196987) B7196987
theorem B1439311 : Blo 1277957 1439311 := bstep (se 1 (by rfl) ⟨1079483, by rfl⟩ : syracuseStep 1439311 = 2158967) B2158967
theorem B3643019 : Blo 1277957 3643019 := bstep (se 1 (by rfl) ⟨2732264, by rfl⟩ : syracuseStep 3643019 = 5464529) B5464529
theorem B32765633 : Blo 1277957 32765633 := bstep (se 2 (by rfl) ⟨12287112, by rfl⟩ : syracuseStep 32765633 = 24574225) B24574225
theorem B4314923 : Blo 1277957 4314923 := bstep (se 1 (by rfl) ⟨3236192, by rfl⟩ : syracuseStep 4314923 = 6472385) B6472385
theorem B1439707 : Blo 1277957 1439707 := bstep (se 1 (by rfl) ⟨1079780, by rfl⟩ : syracuseStep 1439707 = 2159561) B2159561
theorem B4315193 : Blo 1277957 4315193 := bstep (se 2 (by rfl) ⟨1618197, by rfl⟩ : syracuseStep 4315193 = 3236395) B3236395
theorem B4094219 : Blo 1277957 4094219 := bstep (se 1 (by rfl) ⟨3070664, by rfl⟩ : syracuseStep 4094219 = 6141329) B6141329
theorem B4315517 : Blo 1277957 4315517 := bstep (se 3 (by rfl) ⟨809159, by rfl⟩ : syracuseStep 4315517 = 1618319) B1618319
theorem B11082221 : Blo 1277957 11082221 := bstep (se 3 (by rfl) ⟨2077916, by rfl⟩ : syracuseStep 11082221 = 4155833) B4155833
theorem B7281161 : Blo 1277957 7281161 := bstep (se 2 (by rfl) ⟨2730435, by rfl⟩ : syracuseStep 7281161 = 5460871) B5460871
theorem B10369559 : Blo 1277957 10369559 := bstep (se 1 (by rfl) ⟨7777169, by rfl⟩ : syracuseStep 10369559 = 15554339) B15554339
theorem B6470279 : Blo 1277957 6470279 := bstep (se 1 (by rfl) ⟨4852709, by rfl⟩ : syracuseStep 6470279 = 9705419) B9705419
theorem B4315787 : Blo 1277957 4315787 := bstep (se 1 (by rfl) ⟨3236840, by rfl⟩ : syracuseStep 4315787 = 6473681) B6473681
theorem B6142675 : Blo 1277957 6142675 := bstep (se 1 (by rfl) ⟨4607006, by rfl⟩ : syracuseStep 6142675 = 9214013) B9214013
theorem B9714653 : Blo 1277957 9714653 := bstep (se 3 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 9714653 = 3642995) B3642995
theorem B4922369 : Blo 1277957 4922369 := bstep (se 2 (by rfl) ⟨1845888, by rfl⟩ : syracuseStep 4922369 = 3691777) B3691777
theorem B5184569 : Blo 1277957 5184569 := bstep (se 2 (by rfl) ⟨1944213, by rfl⟩ : syracuseStep 5184569 = 3888427) B3888427
theorem B5184665 : Blo 1277957 5184665 := bstep (se 2 (by rfl) ⟨1944249, by rfl⟩ : syracuseStep 5184665 = 3888499) B3888499
theorem B62250221 : Blo 1277957 62250221 := bstep (se 3 (by rfl) ⟨11671916, by rfl⟩ : syracuseStep 62250221 = 23343833) B23343833
theorem B9706877 : Blo 1277957 9706877 := bstep (se 3 (by rfl) ⟨1820039, by rfl⟩ : syracuseStep 9706877 = 3640079) B3640079
theorem B7282163 : Blo 1277957 7282163 := bstep (se 1 (by rfl) ⟨5461622, by rfl⟩ : syracuseStep 7282163 = 10923245) B10923245
theorem B4316705 : Blo 1277957 4316705 := bstep (se 2 (by rfl) ⟨1618764, by rfl⟩ : syracuseStep 4316705 = 3237529) B3237529
theorem B4857479 : Blo 1277957 4857479 := bstep (se 1 (by rfl) ⟨3643109, by rfl⟩ : syracuseStep 4857479 = 7286219) B7286219
theorem B20741771 : Blo 1277957 20741771 := bstep (se 1 (by rfl) ⟨15556328, by rfl⟩ : syracuseStep 20741771 = 31112657) B31112657
theorem B4316921 : Blo 1277957 4316921 := bstep (se 2 (by rfl) ⟨1618845, by rfl⟩ : syracuseStep 4316921 = 3237691) B3237691
theorem B4611935 : Blo 1277957 4611935 := bstep (se 1 (by rfl) ⟨3458951, by rfl⟩ : syracuseStep 4611935 = 6917903) B6917903
theorem B42082163 : Blo 1277957 42082163 := bstep (se 1 (by rfl) ⟨31561622, by rfl⟩ : syracuseStep 42082163 = 63123245) B63123245
theorem B7282619 : Blo 1277957 7282619 := bstep (se 1 (by rfl) ⟨5461964, by rfl⟩ : syracuseStep 7282619 = 10923929) B10923929
theorem B7479233 : Blo 1277957 7479233 := bstep (se 2 (by rfl) ⟨2804712, by rfl⟩ : syracuseStep 7479233 = 5609425) B5609425
theorem B6914099 : Blo 1277957 6914099 := bstep (se 1 (by rfl) ⟨5185574, by rfl⟩ : syracuseStep 6914099 = 10371149) B10371149
theorem B42647651 : Blo 1277957 42647651 := bstep (se 1 (by rfl) ⟨31985738, by rfl⟩ : syracuseStep 42647651 = 63971477) B63971477
theorem B3236051 : Blo 1277957 3236051 := bstep (se 1 (by rfl) ⟨2427038, by rfl⟩ : syracuseStep 3236051 = 4854077) B4854077
theorem B1278239 : Blo 1277957 1278239 := bstep (se 1 (by rfl) ⟨958679, by rfl⟩ : syracuseStep 1278239 = 1917359) B1917359
theorem B12288343 : Blo 1277957 12288343 := bstep (se 1 (by rfl) ⟨9216257, by rfl⟩ : syracuseStep 12288343 = 18432515) B18432515
theorem B1917275 : Blo 1277957 1917275 := bstep (se 1 (by rfl) ⟨1437956, by rfl⟩ : syracuseStep 1917275 = 2875913) B2875913
theorem B1278299 : Blo 1277957 1278299 := bstep (se 1 (by rfl) ⟨958724, by rfl⟩ : syracuseStep 1278299 = 1917449) B1917449
theorem B1278319 : Blo 1277957 1278319 := bstep (se 1 (by rfl) ⟨958739, by rfl⟩ : syracuseStep 1278319 = 1917479) B1917479
theorem B1278375 : Blo 1277957 1278375 := bstep (se 1 (by rfl) ⟨958781, by rfl⟩ : syracuseStep 1278375 = 1917563) B1917563
theorem B2875823 : Blo 1277957 2875823 := bstep (se 1 (by rfl) ⟨2156867, by rfl⟩ : syracuseStep 2875823 = 4313735) B4313735
theorem B2875859 : Blo 1277957 2875859 := bstep (se 1 (by rfl) ⟨2156894, by rfl⟩ : syracuseStep 2875859 = 4313789) B4313789
theorem B1278459 : Blo 1277957 1278459 := bstep (se 1 (by rfl) ⟨958844, by rfl⟩ : syracuseStep 1278459 = 1917689) B1917689
theorem B2875967 : Blo 1277957 2875967 := bstep (se 1 (by rfl) ⟨2156975, by rfl⟩ : syracuseStep 2875967 = 4313951) B4313951
theorem B1917503 : Blo 1277957 1917503 := bstep (se 1 (by rfl) ⟨1438127, by rfl⟩ : syracuseStep 1917503 = 2876255) B2876255
theorem B1278527 : Blo 1277957 1278527 := bstep (se 1 (by rfl) ⟨958895, by rfl⟩ : syracuseStep 1278527 = 1917791) B1917791
theorem B1278535 : Blo 1277957 1278535 := bstep (se 1 (by rfl) ⟨958901, by rfl⟩ : syracuseStep 1278535 = 1917803) B1917803
theorem B2876075 : Blo 1277957 2876075 := bstep (se 1 (by rfl) ⟨2157056, by rfl⟩ : syracuseStep 2876075 = 4314113) B4314113
theorem B1917623 : Blo 1277957 1917623 := bstep (se 1 (by rfl) ⟨1438217, by rfl⟩ : syracuseStep 1917623 = 2876435) B2876435
theorem B1278687 : Blo 1277957 1278687 := bstep (se 1 (by rfl) ⟨959015, by rfl⟩ : syracuseStep 1278687 = 1918031) B1918031
theorem B1278767 : Blo 1277957 1278767 := bstep (se 1 (by rfl) ⟨959075, by rfl⟩ : syracuseStep 1278767 = 1918151) B1918151
theorem B1917851 : Blo 1277957 1917851 := bstep (se 1 (by rfl) ⟨1438388, by rfl⟩ : syracuseStep 1917851 = 2876777) B2876777
theorem B1278875 : Blo 1277957 1278875 := bstep (se 1 (by rfl) ⟨959156, by rfl⟩ : syracuseStep 1278875 = 1918313) B1918313
theorem B2048923 : Blo 1277957 2048923 := bstep (se 1 (by rfl) ⟨1536692, by rfl⟩ : syracuseStep 2048923 = 3073385) B3073385
theorem B1278927 : Blo 1277957 1278927 := bstep (se 1 (by rfl) ⟨959195, by rfl⟩ : syracuseStep 1278927 = 1918391) B1918391
theorem B1278951 : Blo 1277957 1278951 := bstep (se 1 (by rfl) ⟨959213, by rfl⟩ : syracuseStep 1278951 = 1918427) B1918427
theorem B179627057 : Blo 1277957 179627057 := bstep (se 2 (by rfl) ⟨67360146, by rfl⟩ : syracuseStep 179627057 = 134720293) B134720293
theorem B5465245 : Blo 1277957 5465245 := bstep (se 3 (by rfl) ⟨1024733, by rfl⟩ : syracuseStep 5465245 = 2049467) B2049467
theorem B2876615 : Blo 1277957 2876615 := bstep (se 1 (by rfl) ⟨2157461, by rfl⟩ : syracuseStep 2876615 = 4314923) B4314923
theorem B4375795 : Blo 1277957 4375795 := bstep (se 1 (by rfl) ⟨3281846, by rfl⟩ : syracuseStep 4375795 = 6563693) B6563693
theorem B1279263 : Blo 1277957 1279263 := bstep (se 1 (by rfl) ⟨959447, by rfl⟩ : syracuseStep 1279263 = 1918895) B1918895
theorem B1918247 : Blo 1277957 1918247 := bstep (se 1 (by rfl) ⟨1438685, by rfl⟩ : syracuseStep 1918247 = 2877371) B2877371
theorem B1279323 : Blo 1277957 1279323 := bstep (se 1 (by rfl) ⟨959492, by rfl⟩ : syracuseStep 1279323 = 1918985) B1918985
theorem B7284077 : Blo 1277957 7284077 := bstep (se 3 (by rfl) ⟨1365764, by rfl⟩ : syracuseStep 7284077 = 2731529) B2731529
theorem B1279343 : Blo 1277957 1279343 := bstep (se 1 (by rfl) ⟨959507, by rfl⟩ : syracuseStep 1279343 = 1919015) B1919015
theorem B2876795 : Blo 1277957 2876795 := bstep (se 1 (by rfl) ⟨2157596, by rfl⟩ : syracuseStep 2876795 = 4315193) B4315193
theorem B1918331 : Blo 1277957 1918331 := bstep (se 1 (by rfl) ⟨1438748, by rfl⟩ : syracuseStep 1918331 = 2877497) B2877497
theorem B2426249 : Blo 1277957 2426249 := bstep (se 2 (by rfl) ⟨909843, by rfl⟩ : syracuseStep 2426249 = 1819687) B1819687
theorem B454755725 : Blo 1277957 454755725 := bstep (se 3 (by rfl) ⟨85266698, by rfl⟩ : syracuseStep 454755725 = 170533397) B170533397
theorem B1279399 : Blo 1277957 1279399 := bstep (se 1 (by rfl) ⟨959549, by rfl⟩ : syracuseStep 1279399 = 1919099) B1919099
theorem B3458519 : Blo 1277957 3458519 := bstep (se 1 (by rfl) ⟨2593889, by rfl⟩ : syracuseStep 3458519 = 5187779) B5187779
theorem B2876921 : Blo 1277957 2876921 := bstep (se 2 (by rfl) ⟨1078845, by rfl⟩ : syracuseStep 2876921 = 2157691) B2157691
theorem B1918457 : Blo 1277957 1918457 := bstep (se 2 (by rfl) ⟨719421, by rfl⟩ : syracuseStep 1918457 = 1438843) B1438843
theorem B1279483 : Blo 1277957 1279483 := bstep (se 1 (by rfl) ⟨959612, by rfl⟩ : syracuseStep 1279483 = 1919225) B1919225
theorem B2729479 : Blo 1277957 2729479 := bstep (se 1 (by rfl) ⟨2047109, by rfl⟩ : syracuseStep 2729479 = 4094219) B4094219
theorem B1279551 : Blo 1277957 1279551 := bstep (se 1 (by rfl) ⟨959663, by rfl⟩ : syracuseStep 1279551 = 1919327) B1919327
theorem B1279559 : Blo 1277957 1279559 := bstep (se 1 (by rfl) ⟨959669, by rfl⟩ : syracuseStep 1279559 = 1919339) B1919339
theorem B2877011 : Blo 1277957 2877011 := bstep (se 1 (by rfl) ⟨2157758, by rfl⟩ : syracuseStep 2877011 = 4315517) B4315517
theorem B1918559 : Blo 1277957 1918559 := bstep (se 1 (by rfl) ⟨1438919, by rfl⟩ : syracuseStep 1918559 = 2877839) B2877839
theorem B1279711 : Blo 1277957 1279711 := bstep (se 1 (by rfl) ⟨959783, by rfl⟩ : syracuseStep 1279711 = 1919567) B1919567
theorem B2877191 : Blo 1277957 2877191 := bstep (se 1 (by rfl) ⟨2157893, by rfl⟩ : syracuseStep 2877191 = 4315787) B4315787
theorem B1279791 : Blo 1277957 1279791 := bstep (se 1 (by rfl) ⟨959843, by rfl⟩ : syracuseStep 1279791 = 1919687) B1919687
theorem B1918775 : Blo 1277957 1918775 := bstep (se 1 (by rfl) ⟨1439081, by rfl⟩ : syracuseStep 1918775 = 2878163) B2878163
theorem B4319081 : Blo 1277957 4319081 := bstep (se 2 (by rfl) ⟨1619655, by rfl⟩ : syracuseStep 4319081 = 3239311) B3239311
theorem B1279899 : Blo 1277957 1279899 := bstep (se 1 (by rfl) ⟨959924, by rfl⟩ : syracuseStep 1279899 = 1919849) B1919849
theorem B1279951 : Blo 1277957 1279951 := bstep (se 1 (by rfl) ⟨959963, by rfl⟩ : syracuseStep 1279951 = 1919927) B1919927
theorem B1919081 : Blo 1277957 1919081 := bstep (se 2 (by rfl) ⟨719655, by rfl⟩ : syracuseStep 1919081 = 1439311) B1439311
theorem B18450625 : Blo 1277957 18450625 := bstep (se 2 (by rfl) ⟨6918984, by rfl⟩ : syracuseStep 18450625 = 13837969) B13837969
theorem B12298493 : Blo 1277957 12298493 := bstep (se 3 (by rfl) ⟨2305967, by rfl⟩ : syracuseStep 12298493 = 4611935) B4611935
theorem B4319513 : Blo 1277957 4319513 := bstep (se 2 (by rfl) ⟨1619817, by rfl⟩ : syracuseStep 4319513 = 3239635) B3239635
theorem B2877803 : Blo 1277957 2877803 := bstep (se 1 (by rfl) ⟨2158352, by rfl⟩ : syracuseStep 2877803 = 4316705) B4316705
theorem B6916519 : Blo 1277957 6916519 := bstep (se 1 (by rfl) ⟨5187389, by rfl⟩ : syracuseStep 6916519 = 10374779) B10374779
theorem B1919399 : Blo 1277957 1919399 := bstep (se 1 (by rfl) ⟨1439549, by rfl⟩ : syracuseStep 1919399 = 2879099) B2879099
theorem B3238319 : Blo 1277957 3238319 := bstep (se 1 (by rfl) ⟨2428739, by rfl⟩ : syracuseStep 3238319 = 4857479) B4857479
theorem B6474167 : Blo 1277957 6474167 := bstep (se 1 (by rfl) ⟨4855625, by rfl⟩ : syracuseStep 6474167 = 9711251) B9711251
theorem B3688915 : Blo 1277957 3688915 := bstep (se 1 (by rfl) ⟨2766686, by rfl⟩ : syracuseStep 3688915 = 5533373) B5533373
theorem B2877947 : Blo 1277957 2877947 := bstep (se 1 (by rfl) ⟨2158460, by rfl⟩ : syracuseStep 2877947 = 4316921) B4316921
theorem B1919483 : Blo 1277957 1919483 := bstep (se 1 (by rfl) ⟨1439612, by rfl⟩ : syracuseStep 1919483 = 2879225) B2879225
theorem B3639887 : Blo 1277957 3639887 := bstep (se 1 (by rfl) ⟨2729915, by rfl⟩ : syracuseStep 3639887 = 5459831) B5459831
theorem B4852331 : Blo 1277957 4852331 := bstep (se 1 (by rfl) ⟨3639248, by rfl⟩ : syracuseStep 4852331 = 7278497) B7278497
theorem B2878073 : Blo 1277957 2878073 := bstep (se 2 (by rfl) ⟨1079277, by rfl⟩ : syracuseStep 2878073 = 2158555) B2158555
theorem B1919609 : Blo 1277957 1919609 := bstep (se 2 (by rfl) ⟨719853, by rfl⟩ : syracuseStep 1919609 = 1439707) B1439707
theorem B2730667 : Blo 1277957 2730667 := bstep (se 1 (by rfl) ⟨2048000, by rfl⟩ : syracuseStep 2730667 = 4096001) B4096001
theorem B2878127 : Blo 1277957 2878127 := bstep (se 1 (by rfl) ⟨2158595, by rfl⟩ : syracuseStep 2878127 = 4317191) B4317191
theorem B1919663 : Blo 1277957 1919663 := bstep (se 1 (by rfl) ⟨1439747, by rfl⟩ : syracuseStep 1919663 = 2879495) B2879495
theorem B2157239 : Blo 1277957 2157239 := bstep (se 1 (by rfl) ⟨1617929, by rfl⟩ : syracuseStep 2157239 = 3235859) B3235859
theorem B2919095 : Blo 1277957 2919095 := bstep (se 1 (by rfl) ⟨2189321, by rfl⟩ : syracuseStep 2919095 = 4378643) B4378643
theorem B1919711 : Blo 1277957 1919711 := bstep (se 1 (by rfl) ⟨1439783, by rfl⟩ : syracuseStep 1919711 = 2879567) B2879567
theorem B2878199 : Blo 1277957 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B2591507 : Blo 1277957 2591507 := bstep (se 1 (by rfl) ⟨1943630, by rfl⟩ : syracuseStep 2591507 = 3887261) B3887261
theorem B2878379 : Blo 1277957 2878379 := bstep (se 1 (by rfl) ⟨2158784, by rfl⟩ : syracuseStep 2878379 = 4317569) B4317569
theorem B13831307 : Blo 1277957 13831307 := bstep (se 1 (by rfl) ⟨10373480, by rfl⟩ : syracuseStep 13831307 = 20746961) B20746961
theorem B14019763 : Blo 1277957 14019763 := bstep (se 1 (by rfl) ⟨10514822, by rfl⟩ : syracuseStep 14019763 = 21029645) B21029645
theorem B5459231 : Blo 1277957 5459231 := bstep (se 1 (by rfl) ⟨4094423, by rfl⟩ : syracuseStep 5459231 = 8188847) B8188847
theorem B3239291 : Blo 1277957 3239291 := bstep (se 1 (by rfl) ⟨2429468, by rfl⟩ : syracuseStep 3239291 = 4858937) B4858937
theorem B2157961 : Blo 1277957 2157961 := bstep (se 2 (by rfl) ⟨809235, by rfl⟩ : syracuseStep 2157961 = 1618471) B1618471
theorem B3640763 : Blo 1277957 3640763 := bstep (se 1 (by rfl) ⟨2730572, by rfl⟩ : syracuseStep 3640763 = 5461145) B5461145
theorem B14577083 : Blo 1277957 14577083 := bstep (se 1 (by rfl) ⟨10932812, by rfl⟩ : syracuseStep 14577083 = 21865625) B21865625
theorem B2878919 : Blo 1277957 2878919 := bstep (se 1 (by rfl) ⟨2159189, by rfl⟩ : syracuseStep 2878919 = 4318379) B4318379
theorem B5459471 : Blo 1277957 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B3239585 : Blo 1277957 3239585 := bstep (se 2 (by rfl) ⟨1214844, by rfl⟩ : syracuseStep 3239585 = 2429689) B2429689
theorem B2428679 : Blo 1277957 2428679 := bstep (se 1 (by rfl) ⟨1821509, by rfl⟩ : syracuseStep 2428679 = 3643019) B3643019
theorem B21843755 : Blo 1277957 21843755 := bstep (se 1 (by rfl) ⟨16382816, by rfl⟩ : syracuseStep 21843755 = 32765633) B32765633
theorem B2879279 : Blo 1277957 2879279 := bstep (se 1 (by rfl) ⟨2159459, by rfl⟩ : syracuseStep 2879279 = 4318919) B4318919
theorem B2305847 : Blo 1277957 2305847 := bstep (se 1 (by rfl) ⟨1729385, by rfl⟩ : syracuseStep 2305847 = 3458771) B3458771
theorem B2158393 : Blo 1277957 2158393 := bstep (se 2 (by rfl) ⟨809397, by rfl⟩ : syracuseStep 2158393 = 1618795) B1618795
theorem B2158697 : Blo 1277957 2158697 := bstep (se 2 (by rfl) ⟨809511, by rfl⟩ : syracuseStep 2158697 = 1619023) B1619023
theorem B3281161 : Blo 1277957 3281161 := bstep (se 2 (by rfl) ⟨1230435, by rfl⟩ : syracuseStep 3281161 = 2460871) B2460871
theorem B4854107 : Blo 1277957 4854107 := bstep (se 1 (by rfl) ⟨3640580, by rfl⟩ : syracuseStep 4854107 = 7281161) B7281161
theorem B2879855 : Blo 1277957 2879855 := bstep (se 1 (by rfl) ⟨2159891, by rfl⟩ : syracuseStep 2879855 = 4319783) B4319783
theorem B4313519 : Blo 1277957 4313519 := bstep (se 1 (by rfl) ⟨3235139, by rfl⟩ : syracuseStep 4313519 = 6470279) B6470279
theorem B1618375 : Blo 1277957 1618375 := bstep (se 1 (by rfl) ⟨1213781, by rfl⟩ : syracuseStep 1618375 = 2427563) B2427563
theorem B33698267 : Blo 1277957 33698267 := bstep (se 1 (by rfl) ⟨25273700, by rfl⟩ : syracuseStep 33698267 = 50547401) B50547401
theorem B13832693 : Blo 1277957 13832693 := bstep (se 5 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 13832693 = 1296815) B1296815
theorem B1438303 : Blo 1277957 1438303 := bstep (se 1 (by rfl) ⟨1078727, by rfl⟩ : syracuseStep 1438303 = 2157455) B2157455
theorem B6476435 : Blo 1277957 6476435 := bstep (se 1 (by rfl) ⟨4857326, by rfl⟩ : syracuseStep 6476435 = 9714653) B9714653
theorem B3281579 : Blo 1277957 3281579 := bstep (se 1 (by rfl) ⟨2461184, by rfl⟩ : syracuseStep 3281579 = 4922369) B4922369
theorem B2732879 : Blo 1277957 2732879 := bstep (se 1 (by rfl) ⟨2049659, by rfl⟩ : syracuseStep 2732879 = 4099319) B4099319
theorem B9843565 : Blo 1277957 9843565 := bstep (se 3 (by rfl) ⟨1845668, by rfl⟩ : syracuseStep 9843565 = 3691337) B3691337
theorem B14578541 : Blo 1277957 14578541 := bstep (se 3 (by rfl) ⟨2733476, by rfl⟩ : syracuseStep 14578541 = 5466953) B5466953
theorem B4854775 : Blo 1277957 4854775 := bstep (se 1 (by rfl) ⟨3641081, by rfl⟩ : syracuseStep 4854775 = 7282163) B7282163
theorem B28054775 : Blo 1277957 28054775 := bstep (se 1 (by rfl) ⟨21041081, by rfl⟩ : syracuseStep 28054775 = 42082163) B42082163
theorem B4855079 : Blo 1277957 4855079 := bstep (se 1 (by rfl) ⟨3641309, by rfl⟩ : syracuseStep 4855079 = 7282619) B7282619
theorem B4986155 : Blo 1277957 4986155 := bstep (se 1 (by rfl) ⟨3739616, by rfl⟩ : syracuseStep 4986155 = 7479233) B7479233
theorem B1619291 : Blo 1277957 1619291 := bstep (se 1 (by rfl) ⟨1214468, by rfl⟩ : syracuseStep 1619291 = 2428937) B2428937
theorem B4150651 : Blo 1277957 4150651 := bstep (se 1 (by rfl) ⟨3112988, by rfl⟩ : syracuseStep 4150651 = 6225977) B6225977
theorem B4314491 : Blo 1277957 4314491 := bstep (se 1 (by rfl) ⟨3235868, by rfl⟩ : syracuseStep 4314491 = 6471737) B6471737
theorem B6477245 : Blo 1277957 6477245 := bstep (se 3 (by rfl) ⟨1214483, by rfl⟩ : syracuseStep 6477245 = 2428967) B2428967
theorem B1365679 : Blo 1277957 1365679 := bstep (se 1 (by rfl) ⟨1024259, by rfl⟩ : syracuseStep 1365679 = 2048519) B2048519
theorem B1439455 : Blo 1277957 1439455 := bstep (se 1 (by rfl) ⟨1079591, by rfl⟩ : syracuseStep 1439455 = 2159183) B2159183
theorem B4609847 : Blo 1277957 4609847 := bstep (se 1 (by rfl) ⟨3457385, by rfl⟩ : syracuseStep 4609847 = 6914771) B6914771
theorem B1619767 : Blo 1277957 1619767 := bstep (se 1 (by rfl) ⟨1214825, by rfl⟩ : syracuseStep 1619767 = 2429651) B2429651
theorem B8198279 : Blo 1277957 8198279 := bstep (se 1 (by rfl) ⟨6148709, by rfl⟩ : syracuseStep 8198279 = 12297419) B12297419
theorem B7280887 : Blo 1277957 7280887 := bstep (se 1 (by rfl) ⟨5460665, by rfl⟩ : syracuseStep 7280887 = 10921331) B10921331
theorem B8190233 : Blo 1277957 8190233 := bstep (se 2 (by rfl) ⟨3071337, by rfl⟩ : syracuseStep 8190233 = 6142675) B6142675
theorem B1366303 : Blo 1277957 1366303 := bstep (se 1 (by rfl) ⟨1024727, by rfl⟩ : syracuseStep 1366303 = 2049455) B2049455
theorem B638499185 : Blo 1277957 638499185 := bstep (se 2 (by rfl) ⟨239437194, by rfl⟩ : syracuseStep 638499185 = 478874389) B478874389
theorem B35011273 : Blo 1277957 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B4315895 : Blo 1277957 4315895 := bstep (se 1 (by rfl) ⟨3236921, by rfl⟩ : syracuseStep 4315895 = 6473843) B6473843
theorem B3070799 : Blo 1277957 3070799 := bstep (se 1 (by rfl) ⟨2303099, by rfl⟩ : syracuseStep 3070799 = 4606199) B4606199
theorem B4856719 : Blo 1277957 4856719 := bstep (se 1 (by rfl) ⟨3642539, by rfl⟩ : syracuseStep 4856719 = 7285079) B7285079
theorem B18447277 : Blo 1277957 18447277 := bstep (se 3 (by rfl) ⟨3458864, by rfl⟩ : syracuseStep 18447277 = 6917729) B6917729
theorem B7388147 : Blo 1277957 7388147 := bstep (se 1 (by rfl) ⟨5541110, by rfl⟩ : syracuseStep 7388147 = 11082221) B11082221
theorem B6913039 : Blo 1277957 6913039 := bstep (se 1 (by rfl) ⟨5184779, by rfl⟩ : syracuseStep 6913039 = 10369559) B10369559
theorem B4922491 : Blo 1277957 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B8191205 : Blo 1277957 8191205 := bstep (se 4 (by rfl) ⟨767925, by rfl⟩ : syracuseStep 8191205 = 1535851) B1535851
theorem B3235049 : Blo 1277957 3235049 := bstep (se 2 (by rfl) ⟨1213143, by rfl⟩ : syracuseStep 3235049 = 2426287) B2426287
theorem B3456379 : Blo 1277957 3456379 := bstep (se 1 (by rfl) ⟨2592284, by rfl⟩ : syracuseStep 3456379 = 5184569) B5184569
theorem B6397321 : Blo 1277957 6397321 := bstep (se 2 (by rfl) ⟨2398995, by rfl⟩ : syracuseStep 6397321 = 4797991) B4797991
theorem B3235211 : Blo 1277957 3235211 := bstep (se 1 (by rfl) ⟨2426408, by rfl⟩ : syracuseStep 3235211 = 4852817) B4852817
theorem B3456443 : Blo 1277957 3456443 := bstep (se 1 (by rfl) ⟨2592332, by rfl⟩ : syracuseStep 3456443 = 5184665) B5184665
theorem B41500147 : Blo 1277957 41500147 := bstep (se 1 (by rfl) ⟨31125110, by rfl⟩ : syracuseStep 41500147 = 62250221) B62250221
theorem B6471251 : Blo 1277957 6471251 := bstep (se 1 (by rfl) ⟨4853438, by rfl⟩ : syracuseStep 6471251 = 9706877) B9706877
theorem B3235423 : Blo 1277957 3235423 := bstep (se 1 (by rfl) ⟨2426567, by rfl⟩ : syracuseStep 3235423 = 4853135) B4853135
theorem B1384031 : Blo 1277957 1384031 := bstep (se 1 (by rfl) ⟨1038023, by rfl⟩ : syracuseStep 1384031 = 2076047) B2076047
theorem B26590837 : Blo 1277957 26590837 := bstep (se 5 (by rfl) ⟨1246445, by rfl⟩ : syracuseStep 26590837 = 2492891) B2492891
theorem B13827847 : Blo 1277957 13827847 := bstep (se 1 (by rfl) ⟨10370885, by rfl⟩ : syracuseStep 13827847 = 20741771) B20741771
theorem B4316975 : Blo 1277957 4316975 := bstep (se 1 (by rfl) ⟨3237731, by rfl⟩ : syracuseStep 4316975 = 6475463) B6475463
theorem B1278183 : Blo 1277957 1278183 := bstep (se 1 (by rfl) ⟨958637, by rfl⟩ : syracuseStep 1278183 = 1917275) B1917275
theorem B3236071 : Blo 1277957 3236071 := bstep (se 1 (by rfl) ⟨2427053, by rfl⟩ : syracuseStep 3236071 = 4854107) B4854107
theorem B24600833 : Blo 1277957 24600833 := bstep (se 2 (by rfl) ⟨9225312, by rfl⟩ : syracuseStep 24600833 = 18450625) B18450625
theorem B2875679 : Blo 1277957 2875679 := bstep (se 1 (by rfl) ⟨2156759, by rfl⟩ : syracuseStep 2875679 = 4313519) B4313519
theorem B1917215 : Blo 1277957 1917215 := bstep (se 1 (by rfl) ⟨1437911, by rfl⟩ : syracuseStep 1917215 = 2875823) B2875823
theorem B1917239 : Blo 1277957 1917239 := bstep (se 1 (by rfl) ⟨1437929, by rfl⟩ : syracuseStep 1917239 = 2875859) B2875859
theorem B9707849 : Blo 1277957 9707849 := bstep (se 2 (by rfl) ⟨3640443, by rfl⟩ : syracuseStep 9707849 = 7280887) B7280887
theorem B4374881 : Blo 1277957 4374881 := bstep (se 2 (by rfl) ⟨1640580, by rfl⟩ : syracuseStep 4374881 = 3281161) B3281161
theorem B1917311 : Blo 1277957 1917311 := bstep (se 1 (by rfl) ⟨1437983, by rfl⟩ : syracuseStep 1917311 = 2875967) B2875967
theorem B1278335 : Blo 1277957 1278335 := bstep (se 1 (by rfl) ⟨958751, by rfl⟩ : syracuseStep 1278335 = 1917503) B1917503
theorem B4317623 : Blo 1277957 4317623 := bstep (se 1 (by rfl) ⟨3238217, by rfl⟩ : syracuseStep 4317623 = 6476435) B6476435
theorem B1917383 : Blo 1277957 1917383 := bstep (se 1 (by rfl) ⟨1438037, by rfl⟩ : syracuseStep 1917383 = 2876075) B2876075
theorem B16384457 : Blo 1277957 16384457 := bstep (se 2 (by rfl) ⟨6144171, by rfl⟩ : syracuseStep 16384457 = 12288343) B12288343
theorem B2187719 : Blo 1277957 2187719 := bstep (se 1 (by rfl) ⟨1640789, by rfl⟩ : syracuseStep 2187719 = 3281579) B3281579
theorem B1278415 : Blo 1277957 1278415 := bstep (se 1 (by rfl) ⟨958811, by rfl⟩ : syracuseStep 1278415 = 1917623) B1917623
theorem B1278567 : Blo 1277957 1278567 := bstep (se 1 (by rfl) ⟨958925, by rfl⟩ : syracuseStep 1278567 = 1917851) B1917851
theorem B119751371 : Blo 1277957 119751371 := bstep (se 1 (by rfl) ⟨89813528, by rfl⟩ : syracuseStep 119751371 = 179627057) B179627057
theorem B13296413 : Blo 1277957 13296413 := bstep (se 3 (by rfl) ⟨2493077, by rfl⟩ : syracuseStep 13296413 = 4986155) B4986155
theorem B1917737 : Blo 1277957 1917737 := bstep (se 2 (by rfl) ⟨719151, by rfl⟩ : syracuseStep 1917737 = 1438303) B1438303
theorem B1917743 : Blo 1277957 1917743 := bstep (se 1 (by rfl) ⟨1438307, by rfl⟩ : syracuseStep 1917743 = 2876615) B2876615
theorem B18703183 : Blo 1277957 18703183 := bstep (se 1 (by rfl) ⟨14027387, by rfl⟩ : syracuseStep 18703183 = 28054775) B28054775
theorem B3236719 : Blo 1277957 3236719 := bstep (se 1 (by rfl) ⟨2427539, by rfl⟩ : syracuseStep 3236719 = 4855079) B4855079
theorem B1278831 : Blo 1277957 1278831 := bstep (se 1 (by rfl) ⟨959123, by rfl⟩ : syracuseStep 1278831 = 1918247) B1918247
theorem B4318109 : Blo 1277957 4318109 := bstep (se 3 (by rfl) ⟨809645, by rfl⟩ : syracuseStep 4318109 = 1619291) B1619291
theorem B7283621 : Blo 1277957 7283621 := bstep (se 4 (by rfl) ⟨682839, by rfl⟩ : syracuseStep 7283621 = 1365679) B1365679
theorem B2876327 : Blo 1277957 2876327 := bstep (se 1 (by rfl) ⟨2157245, by rfl⟩ : syracuseStep 2876327 = 4314491) B4314491
theorem B1917863 : Blo 1277957 1917863 := bstep (se 1 (by rfl) ⟨1438397, by rfl⟩ : syracuseStep 1917863 = 2876795) B2876795
theorem B1278887 : Blo 1277957 1278887 := bstep (se 1 (by rfl) ⟨959165, by rfl⟩ : syracuseStep 1278887 = 1918331) B1918331
theorem B303170483 : Blo 1277957 303170483 := bstep (se 1 (by rfl) ⟨227377862, by rfl⟩ : syracuseStep 303170483 = 454755725) B454755725
theorem B4318163 : Blo 1277957 4318163 := bstep (se 1 (by rfl) ⟨3238622, by rfl⟩ : syracuseStep 4318163 = 6477245) B6477245
theorem B1917947 : Blo 1277957 1917947 := bstep (se 1 (by rfl) ⟨1438460, by rfl⟩ : syracuseStep 1917947 = 2876921) B2876921
theorem B1278971 : Blo 1277957 1278971 := bstep (se 1 (by rfl) ⟨959228, by rfl⟩ : syracuseStep 1278971 = 1918457) B1918457
theorem B1918007 : Blo 1277957 1918007 := bstep (se 1 (by rfl) ⟨1438505, by rfl⟩ : syracuseStep 1918007 = 2877011) B2877011
theorem B1279039 : Blo 1277957 1279039 := bstep (se 1 (by rfl) ⟨959279, by rfl⟩ : syracuseStep 1279039 = 1918559) B1918559
theorem B13124753 : Blo 1277957 13124753 := bstep (se 2 (by rfl) ⟨4921782, by rfl⟩ : syracuseStep 13124753 = 9843565) B9843565
theorem B1918127 : Blo 1277957 1918127 := bstep (se 1 (by rfl) ⟨1438595, by rfl⟩ : syracuseStep 1918127 = 2877191) B2877191
theorem B3073231 : Blo 1277957 3073231 := bstep (se 1 (by rfl) ⟨2304923, by rfl⟩ : syracuseStep 3073231 = 4609847) B4609847
theorem B1279183 : Blo 1277957 1279183 := bstep (se 1 (by rfl) ⟨959387, by rfl⟩ : syracuseStep 1279183 = 1918775) B1918775
theorem B6473033 : Blo 1277957 6473033 := bstep (se 2 (by rfl) ⟨2427387, by rfl⟩ : syracuseStep 6473033 = 4854775) B4854775
theorem B9217385 : Blo 1277957 9217385 := bstep (se 2 (by rfl) ⟨3456519, by rfl⟩ : syracuseStep 9217385 = 6913039) B6913039
theorem B1279387 : Blo 1277957 1279387 := bstep (se 1 (by rfl) ⟨959540, by rfl⟩ : syracuseStep 1279387 = 1919081) B1919081
theorem B5465519 : Blo 1277957 5465519 := bstep (se 1 (by rfl) ⟨4099139, by rfl⟩ : syracuseStep 5465519 = 8198279) B8198279
theorem B6563321 : Blo 1277957 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B1918535 : Blo 1277957 1918535 := bstep (se 1 (by rfl) ⟨1438901, by rfl⟩ : syracuseStep 1918535 = 2877803) B2877803
theorem B425666123 : Blo 1277957 425666123 := bstep (se 1 (by rfl) ⟨319249592, by rfl⟩ : syracuseStep 425666123 = 638499185) B638499185
theorem B1279599 : Blo 1277957 1279599 := bstep (se 1 (by rfl) ⟨959699, by rfl⟩ : syracuseStep 1279599 = 1919399) B1919399
theorem B5834393 : Blo 1277957 5834393 := bstep (se 2 (by rfl) ⟨2187897, by rfl⟩ : syracuseStep 5834393 = 4375795) B4375795
theorem B1918631 : Blo 1277957 1918631 := bstep (se 1 (by rfl) ⟨1438973, by rfl⟩ : syracuseStep 1918631 = 2877947) B2877947
theorem B1279655 : Blo 1277957 1279655 := bstep (se 1 (by rfl) ⟨959741, by rfl⟩ : syracuseStep 1279655 = 1919483) B1919483
theorem B2426591 : Blo 1277957 2426591 := bstep (se 1 (by rfl) ⟨1819943, by rfl⟩ : syracuseStep 2426591 = 3639887) B3639887
theorem B1918715 : Blo 1277957 1918715 := bstep (se 1 (by rfl) ⟨1439036, by rfl⟩ : syracuseStep 1918715 = 2878073) B2878073
theorem B1279739 : Blo 1277957 1279739 := bstep (se 1 (by rfl) ⟨959804, by rfl⟩ : syracuseStep 1279739 = 1919609) B1919609
theorem B1918751 : Blo 1277957 1918751 := bstep (se 1 (by rfl) ⟨1439063, by rfl⟩ : syracuseStep 1918751 = 2878127) B2878127
theorem B1279775 : Blo 1277957 1279775 := bstep (se 1 (by rfl) ⟨959831, by rfl⟩ : syracuseStep 1279775 = 1919663) B1919663
theorem B1279807 : Blo 1277957 1279807 := bstep (se 1 (by rfl) ⟨959855, by rfl⟩ : syracuseStep 1279807 = 1919711) B1919711
theorem B2877263 : Blo 1277957 2877263 := bstep (se 1 (by rfl) ⟨2157947, by rfl⟩ : syracuseStep 2877263 = 4315895) B4315895
theorem B1918799 : Blo 1277957 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B8529761 : Blo 1277957 8529761 := bstep (se 2 (by rfl) ⟨3198660, by rfl⟩ : syracuseStep 8529761 = 6397321) B6397321
theorem B2877281 : Blo 1277957 2877281 := bstep (se 2 (by rfl) ⟨1078980, by rfl⟩ : syracuseStep 2877281 = 2157961) B2157961
theorem B1918919 : Blo 1277957 1918919 := bstep (se 1 (by rfl) ⟨1439189, by rfl⟩ : syracuseStep 1918919 = 2878379) B2878379
theorem B4925431 : Blo 1277957 4925431 := bstep (se 1 (by rfl) ⟨3694073, by rfl⟩ : syracuseStep 4925431 = 7388147) B7388147
theorem B3639305 : Blo 1277957 3639305 := bstep (se 2 (by rfl) ⟨1364739, by rfl⟩ : syracuseStep 3639305 = 2729479) B2729479
theorem B2156699 : Blo 1277957 2156699 := bstep (se 1 (by rfl) ⟨1617524, by rfl⟩ : syracuseStep 2156699 = 3235049) B3235049
theorem B3639487 : Blo 1277957 3639487 := bstep (se 1 (by rfl) ⟨2729615, by rfl⟩ : syracuseStep 3639487 = 5459231) B5459231
theorem B2156807 : Blo 1277957 2156807 := bstep (se 1 (by rfl) ⟨1617605, by rfl⟩ : syracuseStep 2156807 = 3235211) B3235211
theorem B2427175 : Blo 1277957 2427175 := bstep (se 1 (by rfl) ⟨1820381, by rfl⟩ : syracuseStep 2427175 = 3640763) B3640763
theorem B2304295 : Blo 1277957 2304295 := bstep (se 1 (by rfl) ⟨1728221, by rfl⟩ : syracuseStep 2304295 = 3456443) B3456443
theorem B1919273 : Blo 1277957 1919273 := bstep (se 2 (by rfl) ⟨719727, by rfl⟩ : syracuseStep 1919273 = 1439455) B1439455
theorem B9718055 : Blo 1277957 9718055 := bstep (se 1 (by rfl) ⟨7288541, by rfl⟩ : syracuseStep 9718055 = 14577083) B14577083
theorem B1919279 : Blo 1277957 1919279 := bstep (se 1 (by rfl) ⟨1439459, by rfl⟩ : syracuseStep 1919279 = 2878919) B2878919
theorem B3639647 : Blo 1277957 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B2877857 : Blo 1277957 2877857 := bstep (se 2 (by rfl) ⟨1079196, by rfl⟩ : syracuseStep 2877857 = 2158393) B2158393
theorem B2877983 : Blo 1277957 2877983 := bstep (se 1 (by rfl) ⟨2158487, by rfl⟩ : syracuseStep 2877983 = 4316975) B4316975
theorem B1919519 : Blo 1277957 1919519 := bstep (se 1 (by rfl) ⟨1439639, by rfl⟩ : syracuseStep 1919519 = 2879279) B2879279
theorem B2157367 : Blo 1277957 2157367 := bstep (se 1 (by rfl) ⟨1618025, by rfl⟩ : syracuseStep 2157367 = 3236051) B3236051
theorem B1919903 : Blo 1277957 1919903 := bstep (se 1 (by rfl) ⟨1439927, by rfl⟩ : syracuseStep 1919903 = 2879855) B2879855
theorem B22465511 : Blo 1277957 22465511 := bstep (se 1 (by rfl) ⟨16849133, by rfl⟩ : syracuseStep 22465511 = 33698267) B33698267
theorem B1821737 : Blo 1277957 1821737 := bstep (se 2 (by rfl) ⟨683151, by rfl⟩ : syracuseStep 1821737 = 1366303) B1366303
theorem B9719027 : Blo 1277957 9719027 := bstep (se 1 (by rfl) ⟨7289270, by rfl⟩ : syracuseStep 9719027 = 14578541) B14578541
theorem B2157833 : Blo 1277957 2157833 := bstep (se 2 (by rfl) ⟨809187, by rfl⟩ : syracuseStep 2157833 = 1618375) B1618375
theorem B4918553 : Blo 1277957 4918553 := bstep (se 2 (by rfl) ⟨1844457, by rfl⟩ : syracuseStep 4918553 = 3688915) B3688915
theorem B3640889 : Blo 1277957 3640889 := bstep (se 2 (by rfl) ⟨1365333, by rfl⟩ : syracuseStep 3640889 = 2730667) B2730667
theorem B1617499 : Blo 1277957 1617499 := bstep (se 1 (by rfl) ⟨1213124, by rfl⟩ : syracuseStep 1617499 = 2426249) B2426249
theorem B46681697 : Blo 1277957 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B2305679 : Blo 1277957 2305679 := bstep (se 1 (by rfl) ⟨1729259, by rfl⟩ : syracuseStep 2305679 = 3458519) B3458519
theorem B6475625 : Blo 1277957 6475625 := bstep (se 2 (by rfl) ⟨2428359, by rfl⟩ : syracuseStep 6475625 = 4856719) B4856719
theorem B2731897 : Blo 1277957 2731897 := bstep (se 2 (by rfl) ⟨1024461, by rfl⟩ : syracuseStep 2731897 = 2048923) B2048923
theorem B24596369 : Blo 1277957 24596369 := bstep (se 2 (by rfl) ⟨9223638, by rfl⟩ : syracuseStep 24596369 = 18447277) B18447277
theorem B2879387 : Blo 1277957 2879387 := bstep (se 1 (by rfl) ⟨2159540, by rfl⟩ : syracuseStep 2879387 = 4319081) B4319081
theorem B5460155 : Blo 1277957 5460155 := bstep (se 1 (by rfl) ⟨4095116, by rfl⟩ : syracuseStep 5460155 = 8190233) B8190233
theorem B2879675 : Blo 1277957 2879675 := bstep (se 1 (by rfl) ⟨2159756, by rfl⟩ : syracuseStep 2879675 = 4319513) B4319513
theorem B7286993 : Blo 1277957 7286993 := bstep (se 2 (by rfl) ⟨2732622, by rfl⟩ : syracuseStep 7286993 = 5465245) B5465245
theorem B3690749 : Blo 1277957 3690749 := bstep (se 3 (by rfl) ⟨692015, by rfl⟩ : syracuseStep 3690749 = 1384031) B1384031
theorem B2158879 : Blo 1277957 2158879 := bstep (se 1 (by rfl) ⟨1619159, by rfl⟩ : syracuseStep 2158879 = 3238319) B3238319
theorem B1438159 : Blo 1277957 1438159 := bstep (se 1 (by rfl) ⟨1078619, by rfl⟩ : syracuseStep 1438159 = 2157239) B2157239
theorem B1946063 : Blo 1277957 1946063 := bstep (se 1 (by rfl) ⟨1459547, by rfl⟩ : syracuseStep 1946063 = 2919095) B2919095
theorem B5534201 : Blo 1277957 5534201 := bstep (se 2 (by rfl) ⟨2075325, by rfl⟩ : syracuseStep 5534201 = 4150651) B4150651
theorem B4608505 : Blo 1277957 4608505 := bstep (se 2 (by rfl) ⟨1728189, by rfl⟩ : syracuseStep 4608505 = 3456379) B3456379
theorem B55333529 : Blo 1277957 55333529 := bstep (se 2 (by rfl) ⟨20750073, by rfl⟩ : syracuseStep 55333529 = 41500147) B41500147
theorem B9220871 : Blo 1277957 9220871 := bstep (se 1 (by rfl) ⟨6915653, by rfl⟩ : syracuseStep 9220871 = 13831307) B13831307
theorem B4313897 : Blo 1277957 4313897 := bstep (se 2 (by rfl) ⟨1617711, by rfl⟩ : syracuseStep 4313897 = 3235423) B3235423
theorem B5460803 : Blo 1277957 5460803 := bstep (se 1 (by rfl) ⟨4095602, by rfl⟩ : syracuseStep 5460803 = 8191205) B8191205
theorem B7287677 : Blo 1277957 7287677 := bstep (se 3 (by rfl) ⟨1366439, by rfl⟩ : syracuseStep 7287677 = 2732879) B2732879
theorem B2159527 : Blo 1277957 2159527 := bstep (se 1 (by rfl) ⟨1619645, by rfl⟩ : syracuseStep 2159527 = 3239291) B3239291
theorem B18437129 : Blo 1277957 18437129 := bstep (se 2 (by rfl) ⟨6913923, by rfl⟩ : syracuseStep 18437129 = 13827847) B13827847
theorem B4314167 : Blo 1277957 4314167 := bstep (se 1 (by rfl) ⟨3235625, by rfl⟩ : syracuseStep 4314167 = 6471251) B6471251
theorem B2159689 : Blo 1277957 2159689 := bstep (se 2 (by rfl) ⟨809883, by rfl⟩ : syracuseStep 2159689 = 1619767) B1619767
theorem B2159723 : Blo 1277957 2159723 := bstep (se 1 (by rfl) ⟨1619792, by rfl⟩ : syracuseStep 2159723 = 3239585) B3239585
theorem B1619119 : Blo 1277957 1619119 := bstep (se 1 (by rfl) ⟨1214339, by rfl⟩ : syracuseStep 1619119 = 2428679) B2428679
theorem B14562503 : Blo 1277957 14562503 := bstep (se 1 (by rfl) ⟨10921877, by rfl⟩ : syracuseStep 14562503 = 21843755) B21843755
theorem B1537231 : Blo 1277957 1537231 := bstep (se 1 (by rfl) ⟨1152923, by rfl⟩ : syracuseStep 1537231 = 2305847) B2305847
theorem B4609399 : Blo 1277957 4609399 := bstep (se 1 (by rfl) ⟨3457049, by rfl⟩ : syracuseStep 4609399 = 6914099) B6914099
theorem B28431767 : Blo 1277957 28431767 := bstep (se 1 (by rfl) ⟨21323825, by rfl⟩ : syracuseStep 28431767 = 42647651) B42647651
theorem B1439131 : Blo 1277957 1439131 := bstep (se 1 (by rfl) ⟨1079348, by rfl⟩ : syracuseStep 1439131 = 2158697) B2158697
theorem B9221795 : Blo 1277957 9221795 := bstep (se 1 (by rfl) ⟨6916346, by rfl⟩ : syracuseStep 9221795 = 13832693) B13832693
theorem B9222025 : Blo 1277957 9222025 := bstep (se 2 (by rfl) ⟨3458259, by rfl⟩ : syracuseStep 9222025 = 6916519) B6916519
theorem B4856051 : Blo 1277957 4856051 := bstep (se 1 (by rfl) ⟨3642038, by rfl⟩ : syracuseStep 4856051 = 7284077) B7284077
theorem B8198995 : Blo 1277957 8198995 := bstep (se 1 (by rfl) ⟨6149246, by rfl⟩ : syracuseStep 8198995 = 12298493) B12298493
theorem B18693017 : Blo 1277957 18693017 := bstep (se 2 (by rfl) ⟨7009881, by rfl⟩ : syracuseStep 18693017 = 14019763) B14019763
theorem B4316111 : Blo 1277957 4316111 := bstep (se 1 (by rfl) ⟨3237083, by rfl⟩ : syracuseStep 4316111 = 6474167) B6474167
theorem B3234887 : Blo 1277957 3234887 := bstep (se 1 (by rfl) ⟨2426165, by rfl⟩ : syracuseStep 3234887 = 4852331) B4852331
theorem B1727671 : Blo 1277957 1727671 := bstep (se 1 (by rfl) ⟨1295753, by rfl⟩ : syracuseStep 1727671 = 2591507) B2591507
theorem B2047199 : Blo 1277957 2047199 := bstep (se 1 (by rfl) ⟨1535399, by rfl⟩ : syracuseStep 2047199 = 3070799) B3070799
theorem B35454449 : Blo 1277957 35454449 := bstep (se 2 (by rfl) ⟨13295418, by rfl⟩ : syracuseStep 35454449 = 26590837) B26590837
theorem B4857965 : Blo 1277957 4857965 := bstep (se 3 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 4857965 = 1821737) B1821737
theorem B4857995 : Blo 1277957 4857995 := bstep (se 1 (by rfl) ⟨3643496, by rfl⟩ : syracuseStep 4857995 = 7286993) B7286993
theorem B16400555 : Blo 1277957 16400555 := bstep (se 1 (by rfl) ⟨12300416, by rfl⟩ : syracuseStep 16400555 = 24600833) B24600833
theorem B1917119 : Blo 1277957 1917119 := bstep (se 1 (by rfl) ⟨1437839, by rfl⟩ : syracuseStep 1917119 = 2875679) B2875679
theorem B1278143 : Blo 1277957 1278143 := bstep (se 1 (by rfl) ⟨958607, by rfl⟩ : syracuseStep 1278143 = 1917215) B1917215
theorem B1278159 : Blo 1277957 1278159 := bstep (se 1 (by rfl) ⟨958619, by rfl⟩ : syracuseStep 1278159 = 1917239) B1917239
theorem B6471899 : Blo 1277957 6471899 := bstep (se 1 (by rfl) ⟨4853924, by rfl⟩ : syracuseStep 6471899 = 9707849) B9707849
theorem B2916587 : Blo 1277957 2916587 := bstep (se 1 (by rfl) ⟨2187440, by rfl⟩ : syracuseStep 2916587 = 4374881) B4374881
theorem B1278207 : Blo 1277957 1278207 := bstep (se 1 (by rfl) ⟨958655, by rfl⟩ : syracuseStep 1278207 = 1917311) B1917311
theorem B1278255 : Blo 1277957 1278255 := bstep (se 1 (by rfl) ⟨958691, by rfl⟩ : syracuseStep 1278255 = 1917383) B1917383
theorem B1458479 : Blo 1277957 1458479 := bstep (se 1 (by rfl) ⟨1093859, by rfl⟩ : syracuseStep 1458479 = 2187719) B2187719
theorem B3236233 : Blo 1277957 3236233 := bstep (se 2 (by rfl) ⟨1213587, by rfl⟩ : syracuseStep 3236233 = 2427175) B2427175
theorem B36889019 : Blo 1277957 36889019 := bstep (se 1 (by rfl) ⟨27666764, by rfl⟩ : syracuseStep 36889019 = 55333529) B55333529
theorem B2875931 : Blo 1277957 2875931 := bstep (se 1 (by rfl) ⟨2156948, by rfl⟩ : syracuseStep 2875931 = 4313897) B4313897
theorem B1278491 : Blo 1277957 1278491 := bstep (se 1 (by rfl) ⟨958868, by rfl⟩ : syracuseStep 1278491 = 1917737) B1917737
theorem B1278495 : Blo 1277957 1278495 := bstep (se 1 (by rfl) ⟨958871, by rfl⟩ : syracuseStep 1278495 = 1917743) B1917743
theorem B4858451 : Blo 1277957 4858451 := bstep (se 1 (by rfl) ⟨3643838, by rfl⟩ : syracuseStep 4858451 = 7287677) B7287677
theorem B1917545 : Blo 1277957 1917545 := bstep (se 2 (by rfl) ⟨719079, by rfl⟩ : syracuseStep 1917545 = 1438159) B1438159
theorem B1917551 : Blo 1277957 1917551 := bstep (se 1 (by rfl) ⟨1438163, by rfl⟩ : syracuseStep 1917551 = 2876327) B2876327
theorem B1278575 : Blo 1277957 1278575 := bstep (se 1 (by rfl) ⟨958931, by rfl⟩ : syracuseStep 1278575 = 1917863) B1917863
theorem B6144673 : Blo 1277957 6144673 := bstep (se 2 (by rfl) ⟨2304252, by rfl⟩ : syracuseStep 6144673 = 4608505) B4608505
theorem B1278631 : Blo 1277957 1278631 := bstep (se 1 (by rfl) ⟨958973, by rfl⟩ : syracuseStep 1278631 = 1917947) B1917947
theorem B2876111 : Blo 1277957 2876111 := bstep (se 1 (by rfl) ⟨2157083, by rfl⟩ : syracuseStep 2876111 = 4314167) B4314167
theorem B1278671 : Blo 1277957 1278671 := bstep (se 1 (by rfl) ⟨959003, by rfl⟩ : syracuseStep 1278671 = 1918007) B1918007
theorem B8749835 : Blo 1277957 8749835 := bstep (se 1 (by rfl) ⟨6562376, by rfl⟩ : syracuseStep 8749835 = 13124753) B13124753
theorem B1278751 : Blo 1277957 1278751 := bstep (se 1 (by rfl) ⟨959063, by rfl⟩ : syracuseStep 1278751 = 1918127) B1918127
theorem B9708335 : Blo 1277957 9708335 := bstep (se 1 (by rfl) ⟨7281251, by rfl⟩ : syracuseStep 9708335 = 14562503) B14562503
theorem B6144923 : Blo 1277957 6144923 := bstep (se 1 (by rfl) ⟨4608692, by rfl⟩ : syracuseStep 6144923 = 9217385) B9217385
theorem B4375547 : Blo 1277957 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B1279023 : Blo 1277957 1279023 := bstep (se 1 (by rfl) ⟨959267, by rfl⟩ : syracuseStep 1279023 = 1918535) B1918535
theorem B75818045 : Blo 1277957 75818045 := bstep (se 3 (by rfl) ⟨14215883, by rfl⟩ : syracuseStep 75818045 = 28431767) B28431767
theorem B2876489 : Blo 1277957 2876489 := bstep (se 2 (by rfl) ⟨1078683, by rfl⟩ : syracuseStep 2876489 = 2157367) B2157367
theorem B24937577 : Blo 1277957 24937577 := bstep (se 2 (by rfl) ⟨9351591, by rfl⟩ : syracuseStep 24937577 = 18703183) B18703183
theorem B1279087 : Blo 1277957 1279087 := bstep (se 1 (by rfl) ⟨959315, by rfl⟩ : syracuseStep 1279087 = 1918631) B1918631
theorem B1279143 : Blo 1277957 1279143 := bstep (se 1 (by rfl) ⟨959357, by rfl⟩ : syracuseStep 1279143 = 1918715) B1918715
theorem B1279167 : Blo 1277957 1279167 := bstep (se 1 (by rfl) ⟨959375, by rfl⟩ : syracuseStep 1279167 = 1918751) B1918751
theorem B1918175 : Blo 1277957 1918175 := bstep (se 1 (by rfl) ⟨1438631, by rfl⟩ : syracuseStep 1918175 = 2877263) B2877263
theorem B1279199 : Blo 1277957 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B5686507 : Blo 1277957 5686507 := bstep (se 1 (by rfl) ⟨4264880, by rfl⟩ : syracuseStep 5686507 = 8529761) B8529761
theorem B1918187 : Blo 1277957 1918187 := bstep (se 1 (by rfl) ⟨1438640, by rfl⟩ : syracuseStep 1918187 = 2877281) B2877281
theorem B1279279 : Blo 1277957 1279279 := bstep (se 1 (by rfl) ⟨959459, by rfl⟩ : syracuseStep 1279279 = 1918919) B1918919
theorem B2426203 : Blo 1277957 2426203 := bstep (se 1 (by rfl) ⟨1819652, by rfl⟩ : syracuseStep 2426203 = 3639305) B3639305
theorem B3237367 : Blo 1277957 3237367 := bstep (se 1 (by rfl) ⟨2428025, by rfl⟩ : syracuseStep 3237367 = 4856051) B4856051
theorem B1279515 : Blo 1277957 1279515 := bstep (se 1 (by rfl) ⟨959636, by rfl⟩ : syracuseStep 1279515 = 1919273) B1919273
theorem B1279519 : Blo 1277957 1279519 := bstep (se 1 (by rfl) ⟨959639, by rfl⟩ : syracuseStep 1279519 = 1919279) B1919279
theorem B12289573 : Blo 1277957 12289573 := bstep (se 4 (by rfl) ⟨1152147, by rfl⟩ : syracuseStep 12289573 = 2304295) B2304295
theorem B2426431 : Blo 1277957 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B2303561 : Blo 1277957 2303561 := bstep (se 2 (by rfl) ⟨863835, by rfl⟩ : syracuseStep 2303561 = 1727671) B1727671
theorem B4097641 : Blo 1277957 4097641 := bstep (se 2 (by rfl) ⟨1536615, by rfl⟩ : syracuseStep 4097641 = 3073231) B3073231
theorem B1918571 : Blo 1277957 1918571 := bstep (se 1 (by rfl) ⟨1438928, by rfl⟩ : syracuseStep 1918571 = 2877857) B2877857
theorem B2049641 : Blo 1277957 2049641 := bstep (se 2 (by rfl) ⟨768615, by rfl⟩ : syracuseStep 2049641 = 1537231) B1537231
theorem B1918655 : Blo 1277957 1918655 := bstep (se 1 (by rfl) ⟨1438991, by rfl⟩ : syracuseStep 1918655 = 2877983) B2877983
theorem B1279679 : Blo 1277957 1279679 := bstep (se 1 (by rfl) ⟨959759, by rfl⟩ : syracuseStep 1279679 = 1919519) B1919519
theorem B6145865 : Blo 1277957 6145865 := bstep (se 2 (by rfl) ⟨2304699, by rfl⟩ : syracuseStep 6145865 = 4609399) B4609399
theorem B1918841 : Blo 1277957 1918841 := bstep (se 2 (by rfl) ⟨719565, by rfl⟩ : syracuseStep 1918841 = 1439131) B1439131
theorem B12462011 : Blo 1277957 12462011 := bstep (se 1 (by rfl) ⟨9346508, by rfl⟩ : syracuseStep 12462011 = 18693017) B18693017
theorem B1279935 : Blo 1277957 1279935 := bstep (se 1 (by rfl) ⟨959951, by rfl⟩ : syracuseStep 1279935 = 1919903) B1919903
theorem B2877407 : Blo 1277957 2877407 := bstep (se 1 (by rfl) ⟨2158055, by rfl⟩ : syracuseStep 2877407 = 4316111) B4316111
theorem B14977007 : Blo 1277957 14977007 := bstep (se 1 (by rfl) ⟨11232755, by rfl⟩ : syracuseStep 14977007 = 22465511) B22465511
theorem B2156591 : Blo 1277957 2156591 := bstep (se 1 (by rfl) ⟨1617443, by rfl⟩ : syracuseStep 2156591 = 3234887) B3234887
theorem B35457101 : Blo 1277957 35457101 := bstep (se 3 (by rfl) ⟨6648206, by rfl⟩ : syracuseStep 35457101 = 13296413) B13296413
theorem B2156665 : Blo 1277957 2156665 := bstep (se 2 (by rfl) ⟨808749, by rfl⟩ : syracuseStep 2156665 = 1617499) B1617499
theorem B3279035 : Blo 1277957 3279035 := bstep (se 1 (by rfl) ⟨2459276, by rfl⟩ : syracuseStep 3279035 = 4918553) B4918553
theorem B23636299 : Blo 1277957 23636299 := bstep (se 1 (by rfl) ⟨17727224, by rfl⟩ : syracuseStep 23636299 = 35454449) B35454449
theorem B2427259 : Blo 1277957 2427259 := bstep (se 1 (by rfl) ⟨1820444, by rfl⟩ : syracuseStep 2427259 = 3640889) B3640889
theorem B808454621 : Blo 1277957 808454621 := bstep (se 3 (by rfl) ⟨151585241, by rfl⟩ : syracuseStep 808454621 = 303170483) B303170483
theorem B1919591 : Blo 1277957 1919591 := bstep (se 1 (by rfl) ⟨1439693, by rfl⟩ : syracuseStep 1919591 = 2879387) B2879387
theorem B3640103 : Blo 1277957 3640103 := bstep (se 1 (by rfl) ⟨2730077, by rfl⟩ : syracuseStep 3640103 = 5460155) B5460155
theorem B1919783 : Blo 1277957 1919783 := bstep (se 1 (by rfl) ⟨1439837, by rfl⟩ : syracuseStep 1919783 = 2879675) B2879675
theorem B2460499 : Blo 1277957 2460499 := bstep (se 1 (by rfl) ⟨1845374, by rfl⟩ : syracuseStep 2460499 = 3690749) B3690749
theorem B4852649 : Blo 1277957 4852649 := bstep (se 2 (by rfl) ⟨1819743, by rfl⟩ : syracuseStep 4852649 = 3639487) B3639487
theorem B2878415 : Blo 1277957 2878415 := bstep (se 1 (by rfl) ⟨2158811, by rfl⟩ : syracuseStep 2878415 = 4317623) B4317623
theorem B10922971 : Blo 1277957 10922971 := bstep (se 1 (by rfl) ⟨8192228, by rfl⟩ : syracuseStep 10922971 = 16384457) B16384457
theorem B2878505 : Blo 1277957 2878505 := bstep (se 2 (by rfl) ⟨1079439, by rfl⟩ : syracuseStep 2878505 = 2158879) B2158879
theorem B79834247 : Blo 1277957 79834247 := bstep (se 1 (by rfl) ⟨59875685, by rfl⟩ : syracuseStep 79834247 = 119751371) B119751371
theorem B6147247 : Blo 1277957 6147247 := bstep (se 1 (by rfl) ⟨4610435, by rfl⟩ : syracuseStep 6147247 = 9220871) B9220871
theorem B3640535 : Blo 1277957 3640535 := bstep (se 1 (by rfl) ⟨2730401, by rfl⟩ : syracuseStep 3640535 = 5460803) B5460803
theorem B5459197 : Blo 1277957 5459197 := bstep (se 3 (by rfl) ⟨1023599, by rfl⟩ : syracuseStep 5459197 = 2047199) B2047199
theorem B2878739 : Blo 1277957 2878739 := bstep (se 1 (by rfl) ⟨2159054, by rfl⟩ : syracuseStep 2878739 = 4318109) B4318109
theorem B2878775 : Blo 1277957 2878775 := bstep (se 1 (by rfl) ⟨2159081, by rfl⟩ : syracuseStep 2878775 = 4318163) B4318163
theorem B12291419 : Blo 1277957 12291419 := bstep (se 1 (by rfl) ⟨9218564, by rfl⟩ : syracuseStep 12291419 = 18437129) B18437129
theorem B6147863 : Blo 1277957 6147863 := bstep (se 1 (by rfl) ⟨4610897, by rfl⟩ : syracuseStep 6147863 = 9221795) B9221795
theorem B10931993 : Blo 1277957 10931993 := bstep (se 2 (by rfl) ⟨4099497, by rfl⟩ : syracuseStep 10931993 = 8198995) B8198995
theorem B1617727 : Blo 1277957 1617727 := bstep (se 1 (by rfl) ⟨1213295, by rfl⟩ : syracuseStep 1617727 = 2426591) B2426591
theorem B5189501 : Blo 1277957 5189501 := bstep (se 3 (by rfl) ⟨973031, by rfl⟩ : syracuseStep 5189501 = 1946063) B1946063
theorem B2879369 : Blo 1277957 2879369 := bstep (se 2 (by rfl) ⟨1079763, by rfl⟩ : syracuseStep 2879369 = 2159527) B2159527
theorem B14757869 : Blo 1277957 14757869 := bstep (se 3 (by rfl) ⟨2767100, by rfl⟩ : syracuseStep 14757869 = 5534201) B5534201
theorem B2879585 : Blo 1277957 2879585 := bstep (se 2 (by rfl) ⟨1079844, by rfl⟩ : syracuseStep 2879585 = 2159689) B2159689
theorem B1437799 : Blo 1277957 1437799 := bstep (se 1 (by rfl) ⟨1078349, by rfl⟩ : syracuseStep 1437799 = 2156699) B2156699
theorem B1437871 : Blo 1277957 1437871 := bstep (se 1 (by rfl) ⟨1078403, by rfl⟩ : syracuseStep 1437871 = 2156807) B2156807
theorem B2158825 : Blo 1277957 2158825 := bstep (se 2 (by rfl) ⟨809559, by rfl⟩ : syracuseStep 2158825 = 1619119) B1619119
theorem B6148477 : Blo 1277957 6148477 := bstep (se 3 (by rfl) ⟨1152839, by rfl⟩ : syracuseStep 6148477 = 2305679) B2305679
theorem B1438555 : Blo 1277957 1438555 := bstep (se 1 (by rfl) ⟨1078916, by rfl⟩ : syracuseStep 1438555 = 2157833) B2157833
theorem B3642529 : Blo 1277957 3642529 := bstep (se 2 (by rfl) ⟨1365948, by rfl⟩ : syracuseStep 3642529 = 2731897) B2731897
theorem B16397579 : Blo 1277957 16397579 := bstep (se 1 (by rfl) ⟨12298184, by rfl⟩ : syracuseStep 16397579 = 24596369) B24596369
theorem B6567241 : Blo 1277957 6567241 := bstep (se 2 (by rfl) ⟨2462715, by rfl⟩ : syracuseStep 6567241 = 4925431) B4925431
theorem B4314761 : Blo 1277957 4314761 := bstep (se 2 (by rfl) ⟨1618035, by rfl⟩ : syracuseStep 4314761 = 3236071) B3236071
theorem B4855747 : Blo 1277957 4855747 := bstep (se 1 (by rfl) ⟨3641810, by rfl⟩ : syracuseStep 4855747 = 7283621) B7283621
theorem B1439815 : Blo 1277957 1439815 := bstep (se 1 (by rfl) ⟨1079861, by rfl⟩ : syracuseStep 1439815 = 2159723) B2159723
theorem B4315355 : Blo 1277957 4315355 := bstep (se 1 (by rfl) ⟨3236516, by rfl⟩ : syracuseStep 4315355 = 6473033) B6473033
theorem B3643679 : Blo 1277957 3643679 := bstep (se 1 (by rfl) ⟨2732759, by rfl⟩ : syracuseStep 3643679 = 5465519) B5465519
theorem B283777415 : Blo 1277957 283777415 := bstep (se 1 (by rfl) ⟨212833061, by rfl⟩ : syracuseStep 283777415 = 425666123) B425666123
theorem B3889595 : Blo 1277957 3889595 := bstep (se 1 (by rfl) ⟨2917196, by rfl⟩ : syracuseStep 3889595 = 5834393) B5834393
theorem B4315625 : Blo 1277957 4315625 := bstep (se 2 (by rfl) ⟨1618359, by rfl⟩ : syracuseStep 4315625 = 3236719) B3236719
theorem B6478703 : Blo 1277957 6478703 := bstep (se 1 (by rfl) ⟨4859027, by rfl⟩ : syracuseStep 6478703 = 9718055) B9718055
theorem B6479351 : Blo 1277957 6479351 := bstep (se 1 (by rfl) ⟨4859513, by rfl⟩ : syracuseStep 6479351 = 9719027) B9719027
theorem B31121131 : Blo 1277957 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B12296033 : Blo 1277957 12296033 := bstep (se 2 (by rfl) ⟨4611012, by rfl⟩ : syracuseStep 12296033 = 9222025) B9222025
theorem B4317083 : Blo 1277957 4317083 := bstep (se 1 (by rfl) ⟨3237812, by rfl⟩ : syracuseStep 4317083 = 6475625) B6475625
theorem B1278079 : Blo 1277957 1278079 := bstep (se 1 (by rfl) ⟨958559, by rfl⟩ : syracuseStep 1278079 = 1917119) B1917119
theorem B1917065 : Blo 1277957 1917065 := bstep (se 2 (by rfl) ⟨718899, by rfl⟩ : syracuseStep 1917065 = 1437799) B1437799
theorem B2875553 : Blo 1277957 2875553 := bstep (se 2 (by rfl) ⟨1078332, by rfl⟩ : syracuseStep 2875553 = 2156665) B2156665
theorem B1917161 : Blo 1277957 1917161 := bstep (se 2 (by rfl) ⟨718935, by rfl⟩ : syracuseStep 1917161 = 1437871) B1437871
theorem B24592679 : Blo 1277957 24592679 := bstep (se 1 (by rfl) ⟨18444509, by rfl⟩ : syracuseStep 24592679 = 36889019) B36889019
theorem B1917287 : Blo 1277957 1917287 := bstep (se 1 (by rfl) ⟨1437965, by rfl⟩ : syracuseStep 1917287 = 2875931) B2875931
theorem B1278363 : Blo 1277957 1278363 := bstep (se 1 (by rfl) ⟨958772, by rfl⟩ : syracuseStep 1278363 = 1917545) B1917545
theorem B1278367 : Blo 1277957 1278367 := bstep (se 1 (by rfl) ⟨958775, by rfl⟩ : syracuseStep 1278367 = 1917551) B1917551
theorem B31515065 : Blo 1277957 31515065 := bstep (se 2 (by rfl) ⟨11818149, by rfl⟩ : syracuseStep 31515065 = 23636299) B23636299
theorem B1917407 : Blo 1277957 1917407 := bstep (se 1 (by rfl) ⟨1438055, by rfl⟩ : syracuseStep 1917407 = 2876111) B2876111
theorem B3236345 : Blo 1277957 3236345 := bstep (se 2 (by rfl) ⟨1213629, by rfl⟩ : syracuseStep 3236345 = 2427259) B2427259
theorem B5833223 : Blo 1277957 5833223 := bstep (se 1 (by rfl) ⟨4374917, by rfl⟩ : syracuseStep 5833223 = 8749835) B8749835
theorem B6472223 : Blo 1277957 6472223 := bstep (se 1 (by rfl) ⟨4854167, by rfl⟩ : syracuseStep 6472223 = 9708335) B9708335
theorem B2917031 : Blo 1277957 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B1917659 : Blo 1277957 1917659 := bstep (se 1 (by rfl) ⟨1438244, by rfl⟩ : syracuseStep 1917659 = 2876489) B2876489
theorem B1278783 : Blo 1277957 1278783 := bstep (se 1 (by rfl) ⟨959087, by rfl⟩ : syracuseStep 1278783 = 1918175) B1918175
theorem B1278791 : Blo 1277957 1278791 := bstep (se 1 (by rfl) ⟨959093, by rfl⟩ : syracuseStep 1278791 = 1918187) B1918187
theorem B8192897 : Blo 1277957 8192897 := bstep (se 2 (by rfl) ⟨3072336, by rfl⟩ : syracuseStep 8192897 = 6144673) B6144673
theorem B1279047 : Blo 1277957 1279047 := bstep (se 1 (by rfl) ⟨959285, by rfl⟩ : syracuseStep 1279047 = 1918571) B1918571
theorem B2876507 : Blo 1277957 2876507 := bstep (se 1 (by rfl) ⟨2157380, by rfl⟩ : syracuseStep 2876507 = 4314761) B4314761
theorem B1918073 : Blo 1277957 1918073 := bstep (se 2 (by rfl) ⟨719277, by rfl⟩ : syracuseStep 1918073 = 1438555) B1438555
theorem B1279103 : Blo 1277957 1279103 := bstep (se 1 (by rfl) ⟨959327, by rfl⟩ : syracuseStep 1279103 = 1918655) B1918655
theorem B4097243 : Blo 1277957 4097243 := bstep (se 1 (by rfl) ⟨3072932, by rfl⟩ : syracuseStep 4097243 = 6145865) B6145865
theorem B1279227 : Blo 1277957 1279227 := bstep (se 1 (by rfl) ⟨959420, by rfl⟩ : syracuseStep 1279227 = 1918841) B1918841
theorem B8308007 : Blo 1277957 8308007 := bstep (se 1 (by rfl) ⟨6231005, by rfl⟩ : syracuseStep 8308007 = 12462011) B12462011
theorem B1918271 : Blo 1277957 1918271 := bstep (se 1 (by rfl) ⟨1438703, by rfl⟩ : syracuseStep 1918271 = 2877407) B2877407
theorem B2876903 : Blo 1277957 2876903 := bstep (se 1 (by rfl) ⟨2157677, by rfl⟩ : syracuseStep 2876903 = 4315355) B4315355
theorem B538969747 : Blo 1277957 538969747 := bstep (se 1 (by rfl) ⟨404227310, by rfl⟩ : syracuseStep 538969747 = 808454621) B808454621
theorem B2877083 : Blo 1277957 2877083 := bstep (se 1 (by rfl) ⟨2157812, by rfl⟩ : syracuseStep 2877083 = 4315625) B4315625
theorem B1279727 : Blo 1277957 1279727 := bstep (se 1 (by rfl) ⟨959795, by rfl⟩ : syracuseStep 1279727 = 1919591) B1919591
theorem B2426735 : Blo 1277957 2426735 := bstep (se 1 (by rfl) ⟨1820051, by rfl⟩ : syracuseStep 2426735 = 3640103) B3640103
theorem B1279855 : Blo 1277957 1279855 := bstep (se 1 (by rfl) ⟨959891, by rfl⟩ : syracuseStep 1279855 = 1919783) B1919783
theorem B4319135 : Blo 1277957 4319135 := bstep (se 1 (by rfl) ⟨3239351, by rfl⟩ : syracuseStep 4319135 = 6478703) B6478703
theorem B1918943 : Blo 1277957 1918943 := bstep (se 1 (by rfl) ⟨1439207, by rfl⟩ : syracuseStep 1918943 = 2878415) B2878415
theorem B1919003 : Blo 1277957 1919003 := bstep (se 1 (by rfl) ⟨1439252, by rfl⟩ : syracuseStep 1919003 = 2878505) B2878505
theorem B16386097 : Blo 1277957 16386097 := bstep (se 2 (by rfl) ⟨6144786, by rfl⟩ : syracuseStep 16386097 = 12289573) B12289573
theorem B2427023 : Blo 1277957 2427023 := bstep (se 1 (by rfl) ⟨1820267, by rfl⟩ : syracuseStep 2427023 = 3640535) B3640535
theorem B1919159 : Blo 1277957 1919159 := bstep (se 1 (by rfl) ⟨1439369, by rfl⟩ : syracuseStep 1919159 = 2878739) B2878739
theorem B1919183 : Blo 1277957 1919183 := bstep (se 1 (by rfl) ⟨1439387, by rfl⟩ : syracuseStep 1919183 = 2878775) B2878775
theorem B8194279 : Blo 1277957 8194279 := bstep (se 1 (by rfl) ⟨6145709, by rfl⟩ : syracuseStep 8194279 = 12291419) B12291419
theorem B41494841 : Blo 1277957 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B4319567 : Blo 1277957 4319567 := bstep (se 1 (by rfl) ⟨3239675, by rfl⟩ : syracuseStep 4319567 = 6479351) B6479351
theorem B16386461 : Blo 1277957 16386461 := bstep (se 3 (by rfl) ⟨3072461, by rfl⟩ : syracuseStep 16386461 = 6144923) B6144923
theorem B2156969 : Blo 1277957 2156969 := bstep (se 2 (by rfl) ⟨808863, by rfl⟩ : syracuseStep 2156969 = 1617727) B1617727
theorem B4098575 : Blo 1277957 4098575 := bstep (se 1 (by rfl) ⟨3073931, by rfl⟩ : syracuseStep 4098575 = 6147863) B6147863
theorem B3459667 : Blo 1277957 3459667 := bstep (se 1 (by rfl) ⟨2594750, by rfl⟩ : syracuseStep 3459667 = 5189501) B5189501
theorem B6474329 : Blo 1277957 6474329 := bstep (se 2 (by rfl) ⟨2427873, by rfl⟩ : syracuseStep 6474329 = 4855747) B4855747
theorem B1919579 : Blo 1277957 1919579 := bstep (se 1 (by rfl) ⟨1439684, by rfl⟩ : syracuseStep 1919579 = 2879369) B2879369
theorem B2878055 : Blo 1277957 2878055 := bstep (se 1 (by rfl) ⟨2158541, by rfl⟩ : syracuseStep 2878055 = 4317083) B4317083
theorem B1919723 : Blo 1277957 1919723 := bstep (se 1 (by rfl) ⟨1439792, by rfl⟩ : syracuseStep 1919723 = 2879585) B2879585
theorem B3238643 : Blo 1277957 3238643 := bstep (se 1 (by rfl) ⟨2428982, by rfl⟩ : syracuseStep 3238643 = 4857965) B4857965
theorem B3238663 : Blo 1277957 3238663 := bstep (se 1 (by rfl) ⟨2428997, by rfl⟩ : syracuseStep 3238663 = 4857995) B4857995
theorem B1919753 : Blo 1277957 1919753 := bstep (se 2 (by rfl) ⟨719907, by rfl⟩ : syracuseStep 1919753 = 1439815) B1439815
theorem B202181453 : Blo 1277957 202181453 := bstep (se 3 (by rfl) ⟨37909022, by rfl⟩ : syracuseStep 202181453 = 75818045) B75818045
theorem B2878433 : Blo 1277957 2878433 := bstep (se 2 (by rfl) ⟨1079412, by rfl⟩ : syracuseStep 2878433 = 2158825) B2158825
theorem B3238967 : Blo 1277957 3238967 := bstep (se 1 (by rfl) ⟨2429225, by rfl⟩ : syracuseStep 3238967 = 4858451) B4858451
theorem B7777565 : Blo 1277957 7777565 := bstep (se 3 (by rfl) ⟨1458293, by rfl⟩ : syracuseStep 7777565 = 2916587) B2916587
theorem B16625051 : Blo 1277957 16625051 := bstep (se 1 (by rfl) ⟨12468788, by rfl⟩ : syracuseStep 16625051 = 24937577) B24937577
theorem B10931719 : Blo 1277957 10931719 := bstep (se 1 (by rfl) ⟨8198789, by rfl⟩ : syracuseStep 10931719 = 16397579) B16397579
theorem B1535707 : Blo 1277957 1535707 := bstep (se 1 (by rfl) ⟨1151780, by rfl⟩ : syracuseStep 1535707 = 2303561) B2303561
theorem B1437727 : Blo 1277957 1437727 := bstep (se 1 (by rfl) ⟨1078295, by rfl⟩ : syracuseStep 1437727 = 2156591) B2156591
theorem B23638067 : Blo 1277957 23638067 := bstep (se 1 (by rfl) ⟨17728550, by rfl⟩ : syracuseStep 23638067 = 35457101) B35457101
theorem B2429119 : Blo 1277957 2429119 := bstep (se 1 (by rfl) ⟨1821839, by rfl⟩ : syracuseStep 2429119 = 3643679) B3643679
theorem B8196329 : Blo 1277957 8196329 := bstep (se 2 (by rfl) ⟨3073623, by rfl⟩ : syracuseStep 8196329 = 6147247) B6147247
theorem B2593063 : Blo 1277957 2593063 := bstep (se 1 (by rfl) ⟨1944797, by rfl⟩ : syracuseStep 2593063 = 3889595) B3889595
theorem B7582009 : Blo 1277957 7582009 := bstep (se 2 (by rfl) ⟨2843253, by rfl⟩ : syracuseStep 7582009 = 5686507) B5686507
theorem B7278929 : Blo 1277957 7278929 := bstep (se 2 (by rfl) ⟨2729598, by rfl⟩ : syracuseStep 7278929 = 5459197) B5459197
theorem B7287995 : Blo 1277957 7287995 := bstep (se 1 (by rfl) ⟨5465996, by rfl⟩ : syracuseStep 7287995 = 10931993) B10931993
theorem B8197355 : Blo 1277957 8197355 := bstep (se 1 (by rfl) ⟨6148016, by rfl⟩ : syracuseStep 8197355 = 12296033) B12296033
theorem B10933703 : Blo 1277957 10933703 := bstep (se 1 (by rfl) ⟨8200277, by rfl⟩ : syracuseStep 10933703 = 16400555) B16400555
theorem B4314599 : Blo 1277957 4314599 := bstep (se 1 (by rfl) ⟨3235949, by rfl⟩ : syracuseStep 4314599 = 6471899) B6471899
theorem B4314977 : Blo 1277957 4314977 := bstep (se 2 (by rfl) ⟨1618116, by rfl⟩ : syracuseStep 4314977 = 3236233) B3236233
theorem B3889277 : Blo 1277957 3889277 := bstep (se 3 (by rfl) ⟨729239, by rfl⟩ : syracuseStep 3889277 = 1458479) B1458479
theorem B1366427 : Blo 1277957 1366427 := bstep (se 1 (by rfl) ⟨1024820, by rfl⟩ : syracuseStep 1366427 = 2049641) B2049641
theorem B14563961 : Blo 1277957 14563961 := bstep (se 2 (by rfl) ⟨5461485, by rfl⟩ : syracuseStep 14563961 = 10922971) B10922971
theorem B9984671 : Blo 1277957 9984671 := bstep (se 1 (by rfl) ⟨7488503, by rfl⟩ : syracuseStep 9984671 = 14977007) B14977007
theorem B2186023 : Blo 1277957 2186023 := bstep (se 1 (by rfl) ⟨1639517, by rfl⟩ : syracuseStep 2186023 = 3279035) B3279035
theorem B4856705 : Blo 1277957 4856705 := bstep (se 2 (by rfl) ⟨1821264, by rfl⟩ : syracuseStep 4856705 = 3642529) B3642529
theorem B189184943 : Blo 1277957 189184943 := bstep (se 1 (by rfl) ⟨141888707, by rfl⟩ : syracuseStep 189184943 = 283777415) B283777415
theorem B8756321 : Blo 1277957 8756321 := bstep (se 2 (by rfl) ⟨3283620, by rfl⟩ : syracuseStep 8756321 = 6567241) B6567241
theorem B13122661 : Blo 1277957 13122661 := bstep (se 4 (by rfl) ⟨1230249, by rfl⟩ : syracuseStep 13122661 = 2460499) B2460499
theorem B3234937 : Blo 1277957 3234937 := bstep (se 2 (by rfl) ⟨1213101, by rfl⟩ : syracuseStep 3234937 = 2426203) B2426203
theorem B3235099 : Blo 1277957 3235099 := bstep (se 1 (by rfl) ⟨2426324, by rfl⟩ : syracuseStep 3235099 = 4852649) B4852649
theorem B32791877 : Blo 1277957 32791877 := bstep (se 4 (by rfl) ⟨3074238, by rfl⟩ : syracuseStep 32791877 = 6148477) B6148477
theorem B4316489 : Blo 1277957 4316489 := bstep (se 2 (by rfl) ⟨1618683, by rfl⟩ : syracuseStep 4316489 = 3237367) B3237367
theorem B3235241 : Blo 1277957 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B53222831 : Blo 1277957 53222831 := bstep (se 1 (by rfl) ⟨39917123, by rfl⟩ : syracuseStep 53222831 = 79834247) B79834247
theorem B5463521 : Blo 1277957 5463521 := bstep (se 2 (by rfl) ⟨2048820, by rfl⟩ : syracuseStep 5463521 = 4097641) B4097641
theorem B9838579 : Blo 1277957 9838579 := bstep (se 1 (by rfl) ⟨7378934, by rfl⟩ : syracuseStep 9838579 = 14757869) B14757869
theorem B1916969 : Blo 1277957 1916969 := bstep (se 2 (by rfl) ⟨718863, by rfl⟩ : syracuseStep 1916969 = 1437727) B1437727
theorem B21848129 : Blo 1277957 21848129 := bstep (se 2 (by rfl) ⟨8193048, by rfl⟩ : syracuseStep 21848129 = 16386097) B16386097
theorem B1278043 : Blo 1277957 1278043 := bstep (se 1 (by rfl) ⟨958532, by rfl⟩ : syracuseStep 1278043 = 1917065) B1917065
theorem B1917035 : Blo 1277957 1917035 := bstep (se 1 (by rfl) ⟨1437776, by rfl⟩ : syracuseStep 1917035 = 2875553) B2875553
theorem B1278107 : Blo 1277957 1278107 := bstep (se 1 (by rfl) ⟨958580, by rfl⟩ : syracuseStep 1278107 = 1917161) B1917161
theorem B1278191 : Blo 1277957 1278191 := bstep (se 1 (by rfl) ⟨958643, by rfl⟩ : syracuseStep 1278191 = 1917287) B1917287
theorem B1278271 : Blo 1277957 1278271 := bstep (se 1 (by rfl) ⟨958703, by rfl⟩ : syracuseStep 1278271 = 1917407) B1917407
theorem B6472061 : Blo 1277957 6472061 := bstep (se 3 (by rfl) ⟨1213511, by rfl⟩ : syracuseStep 6472061 = 2427023) B2427023
theorem B3457417 : Blo 1277957 3457417 := bstep (se 2 (by rfl) ⟨1296531, by rfl⟩ : syracuseStep 3457417 = 2593063) B2593063
theorem B10109345 : Blo 1277957 10109345 := bstep (se 2 (by rfl) ⟨3791004, by rfl⟩ : syracuseStep 10109345 = 7582009) B7582009
theorem B1278439 : Blo 1277957 1278439 := bstep (se 1 (by rfl) ⟨958829, by rfl⟩ : syracuseStep 1278439 = 1917659) B1917659
theorem B21856877 : Blo 1277957 21856877 := bstep (se 3 (by rfl) ⟨4098164, by rfl⟩ : syracuseStep 21856877 = 8196329) B8196329
theorem B1917671 : Blo 1277957 1917671 := bstep (se 1 (by rfl) ⟨1438253, by rfl⟩ : syracuseStep 1917671 = 2876507) B2876507
theorem B1278715 : Blo 1277957 1278715 := bstep (se 1 (by rfl) ⟨959036, by rfl⟩ : syracuseStep 1278715 = 1918073) B1918073
theorem B4612889 : Blo 1277957 4612889 := bstep (se 2 (by rfl) ⟨1729833, by rfl⟩ : syracuseStep 4612889 = 3459667) B3459667
theorem B4858663 : Blo 1277957 4858663 := bstep (se 1 (by rfl) ⟨3643997, by rfl⟩ : syracuseStep 4858663 = 7287995) B7287995
theorem B5464903 : Blo 1277957 5464903 := bstep (se 1 (by rfl) ⟨4098677, by rfl⟩ : syracuseStep 5464903 = 8197355) B8197355
theorem B5538671 : Blo 1277957 5538671 := bstep (se 1 (by rfl) ⟨4154003, by rfl⟩ : syracuseStep 5538671 = 8308007) B8308007
theorem B1278847 : Blo 1277957 1278847 := bstep (se 1 (by rfl) ⟨959135, by rfl⟩ : syracuseStep 1278847 = 1918271) B1918271
theorem B2876399 : Blo 1277957 2876399 := bstep (se 1 (by rfl) ⟨2157299, by rfl⟩ : syracuseStep 2876399 = 4314599) B4314599
theorem B1917935 : Blo 1277957 1917935 := bstep (se 1 (by rfl) ⟨1438451, by rfl⟩ : syracuseStep 1917935 = 2876903) B2876903
theorem B4318217 : Blo 1277957 4318217 := bstep (se 2 (by rfl) ⟨1619331, by rfl⟩ : syracuseStep 4318217 = 3238663) B3238663
theorem B1918055 : Blo 1277957 1918055 := bstep (se 1 (by rfl) ⟨1438541, by rfl⟩ : syracuseStep 1918055 = 2877083) B2877083
theorem B2876651 : Blo 1277957 2876651 := bstep (se 1 (by rfl) ⟨2157488, by rfl⟩ : syracuseStep 2876651 = 4314977) B4314977
theorem B1279295 : Blo 1277957 1279295 := bstep (se 1 (by rfl) ⟨959471, by rfl⟩ : syracuseStep 1279295 = 1918943) B1918943
theorem B1279335 : Blo 1277957 1279335 := bstep (se 1 (by rfl) ⟨959501, by rfl⟩ : syracuseStep 1279335 = 1919003) B1919003
theorem B1279439 : Blo 1277957 1279439 := bstep (se 1 (by rfl) ⟨959579, by rfl⟩ : syracuseStep 1279439 = 1919159) B1919159
theorem B1279455 : Blo 1277957 1279455 := bstep (se 1 (by rfl) ⟨959591, by rfl⟩ : syracuseStep 1279455 = 1919183) B1919183
theorem B1279719 : Blo 1277957 1279719 := bstep (se 1 (by rfl) ⟨959789, by rfl⟩ : syracuseStep 1279719 = 1919579) B1919579
theorem B1918703 : Blo 1277957 1918703 := bstep (se 1 (by rfl) ⟨1439027, by rfl⟩ : syracuseStep 1918703 = 2878055) B2878055
theorem B9709307 : Blo 1277957 9709307 := bstep (se 1 (by rfl) ⟨7281980, by rfl⟩ : syracuseStep 9709307 = 14563961) B14563961
theorem B1279815 : Blo 1277957 1279815 := bstep (se 1 (by rfl) ⟨959861, by rfl⟩ : syracuseStep 1279815 = 1919723) B1919723
theorem B1279835 : Blo 1277957 1279835 := bstep (se 1 (by rfl) ⟨959876, by rfl⟩ : syracuseStep 1279835 = 1919753) B1919753
theorem B3237803 : Blo 1277957 3237803 := bstep (se 1 (by rfl) ⟨2428352, by rfl⟩ : syracuseStep 3237803 = 4856705) B4856705
theorem B1918955 : Blo 1277957 1918955 := bstep (se 1 (by rfl) ⟨1439216, by rfl⟩ : syracuseStep 1918955 = 2878433) B2878433
theorem B14575625 : Blo 1277957 14575625 := bstep (se 2 (by rfl) ⟨5465859, by rfl⟩ : syracuseStep 14575625 = 10931719) B10931719
theorem B2877659 : Blo 1277957 2877659 := bstep (se 1 (by rfl) ⟨2158244, by rfl⟩ : syracuseStep 2877659 = 4316489) B4316489
theorem B2156827 : Blo 1277957 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B35481887 : Blo 1277957 35481887 := bstep (se 1 (by rfl) ⟨26611415, by rfl⟩ : syracuseStep 35481887 = 53222831) B53222831
theorem B13118105 : Blo 1277957 13118105 := bstep (se 2 (by rfl) ⟨4919289, by rfl⟩ : syracuseStep 13118105 = 9838579) B9838579
theorem B16395119 : Blo 1277957 16395119 := bstep (se 1 (by rfl) ⟨12296339, by rfl⟩ : syracuseStep 16395119 = 24592679) B24592679
theorem B4852619 : Blo 1277957 4852619 := bstep (se 1 (by rfl) ⟨3639464, by rfl⟩ : syracuseStep 4852619 = 7278929) B7278929
theorem B3238825 : Blo 1277957 3238825 := bstep (se 2 (by rfl) ⟨1214559, by rfl⟩ : syracuseStep 3238825 = 2429119) B2429119
theorem B23350189 : Blo 1277957 23350189 := bstep (se 3 (by rfl) ⟨4378160, by rfl⟩ : syracuseStep 23350189 = 8756321) B8756321
theorem B2157563 : Blo 1277957 2157563 := bstep (se 1 (by rfl) ⟨1618172, by rfl⟩ : syracuseStep 2157563 = 3236345) B3236345
theorem B2731495 : Blo 1277957 2731495 := bstep (se 1 (by rfl) ⟨2048621, by rfl⟩ : syracuseStep 2731495 = 4097243) B4097243
theorem B1617823 : Blo 1277957 1617823 := bstep (se 1 (by rfl) ⟨1213367, by rfl⟩ : syracuseStep 1617823 = 2426735) B2426735
theorem B2879423 : Blo 1277957 2879423 := bstep (se 1 (by rfl) ⟨2159567, by rfl⟩ : syracuseStep 2879423 = 4319135) B4319135
theorem B2592851 : Blo 1277957 2592851 := bstep (se 1 (by rfl) ⟨1944638, by rfl⟩ : syracuseStep 2592851 = 3889277) B3889277
theorem B4313249 : Blo 1277957 4313249 := bstep (se 2 (by rfl) ⟨1617468, by rfl⟩ : syracuseStep 4313249 = 3234937) B3234937
theorem B2879711 : Blo 1277957 2879711 := bstep (se 1 (by rfl) ⟨2159783, by rfl⟩ : syracuseStep 2879711 = 4319567) B4319567
theorem B10924307 : Blo 1277957 10924307 := bstep (se 1 (by rfl) ⟨8193230, by rfl⟩ : syracuseStep 10924307 = 16386461) B16386461
theorem B1437979 : Blo 1277957 1437979 := bstep (se 1 (by rfl) ⟨1078484, by rfl⟩ : syracuseStep 1437979 = 2156969) B2156969
theorem B2732383 : Blo 1277957 2732383 := bstep (se 1 (by rfl) ⟨2049287, by rfl⟩ : syracuseStep 2732383 = 4098575) B4098575
theorem B4313465 : Blo 1277957 4313465 := bstep (se 2 (by rfl) ⟨1617549, by rfl⟩ : syracuseStep 4313465 = 3235099) B3235099
theorem B7778749 : Blo 1277957 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B6656447 : Blo 1277957 6656447 := bstep (se 1 (by rfl) ⟨4992335, by rfl⟩ : syracuseStep 6656447 = 9984671) B9984671
theorem B2159095 : Blo 1277957 2159095 := bstep (se 1 (by rfl) ⟨1619321, by rfl⟩ : syracuseStep 2159095 = 3238643) B3238643
theorem B134787635 : Blo 1277957 134787635 := bstep (se 1 (by rfl) ⟨101090726, by rfl⟩ : syracuseStep 134787635 = 202181453) B202181453
theorem B2159311 : Blo 1277957 2159311 := bstep (se 1 (by rfl) ⟨1619483, by rfl⟩ : syracuseStep 2159311 = 3238967) B3238967
theorem B21861251 : Blo 1277957 21861251 := bstep (se 1 (by rfl) ⟨16395938, by rfl⟩ : syracuseStep 21861251 = 32791877) B32791877
theorem B3642347 : Blo 1277957 3642347 := bstep (se 1 (by rfl) ⟨2731760, by rfl⟩ : syracuseStep 3642347 = 5463521) B5463521
theorem B504493181 : Blo 1277957 504493181 := bstep (se 3 (by rfl) ⟨94592471, by rfl⟩ : syracuseStep 504493181 = 189184943) B189184943
theorem B15758711 : Blo 1277957 15758711 := bstep (se 1 (by rfl) ⟨11819033, by rfl⟩ : syracuseStep 15758711 = 23638067) B23638067
theorem B21010043 : Blo 1277957 21010043 := bstep (se 1 (by rfl) ⟨15757532, by rfl⟩ : syracuseStep 21010043 = 31515065) B31515065
theorem B10925705 : Blo 1277957 10925705 := bstep (se 2 (by rfl) ⟨4097139, by rfl⟩ : syracuseStep 10925705 = 8194279) B8194279
theorem B3888815 : Blo 1277957 3888815 := bstep (se 1 (by rfl) ⟨2916611, by rfl⟩ : syracuseStep 3888815 = 5833223) B5833223
theorem B4314815 : Blo 1277957 4314815 := bstep (se 1 (by rfl) ⟨3236111, by rfl⟩ : syracuseStep 4314815 = 6472223) B6472223
theorem B5461931 : Blo 1277957 5461931 := bstep (se 1 (by rfl) ⟨4096448, by rfl⟩ : syracuseStep 5461931 = 8192897) B8192897
theorem B7289135 : Blo 1277957 7289135 := bstep (se 1 (by rfl) ⟨5466851, by rfl⟩ : syracuseStep 7289135 = 10933703) B10933703
theorem B2914697 : Blo 1277957 2914697 := bstep (se 2 (by rfl) ⟨1093011, by rfl⟩ : syracuseStep 2914697 = 2186023) B2186023
theorem B3643805 : Blo 1277957 3643805 := bstep (se 3 (by rfl) ⟨683213, by rfl⟩ : syracuseStep 3643805 = 1366427) B1366427
theorem B17496881 : Blo 1277957 17496881 := bstep (se 2 (by rfl) ⟨6561330, by rfl⟩ : syracuseStep 17496881 = 13122661) B13122661
theorem B27663227 : Blo 1277957 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B4316219 : Blo 1277957 4316219 := bstep (se 1 (by rfl) ⟨3237164, by rfl⟩ : syracuseStep 4316219 = 6474329) B6474329
theorem B5185043 : Blo 1277957 5185043 := bstep (se 1 (by rfl) ⟨3888782, by rfl⟩ : syracuseStep 5185043 = 7777565) B7777565
theorem B718626329 : Blo 1277957 718626329 := bstep (se 2 (by rfl) ⟨269484873, by rfl⟩ : syracuseStep 718626329 = 538969747) B538969747
theorem B11083367 : Blo 1277957 11083367 := bstep (se 1 (by rfl) ⟨8312525, by rfl⟩ : syracuseStep 11083367 = 16625051) B16625051
theorem B2047609 : Blo 1277957 2047609 := bstep (se 2 (by rfl) ⟨767853, by rfl⟩ : syracuseStep 2047609 = 1535707) B1535707
theorem B1277979 : Blo 1277957 1277979 := bstep (se 1 (by rfl) ⟨958484, by rfl⟩ : syracuseStep 1277979 = 1916969) B1916969
theorem B14565419 : Blo 1277957 14565419 := bstep (se 1 (by rfl) ⟨10924064, by rfl⟩ : syracuseStep 14565419 = 21848129) B21848129
theorem B1278023 : Blo 1277957 1278023 := bstep (se 1 (by rfl) ⟨958517, by rfl⟩ : syracuseStep 1278023 = 1917035) B1917035
theorem B2875499 : Blo 1277957 2875499 := bstep (se 1 (by rfl) ⟨2156624, by rfl⟩ : syracuseStep 2875499 = 4313249) B4313249
theorem B7282871 : Blo 1277957 7282871 := bstep (se 1 (by rfl) ⟨5462153, by rfl⟩ : syracuseStep 7282871 = 10924307) B10924307
theorem B6914269 : Blo 1277957 6914269 := bstep (se 3 (by rfl) ⟨1296425, by rfl⟩ : syracuseStep 6914269 = 2592851) B2592851
theorem B2875643 : Blo 1277957 2875643 := bstep (se 1 (by rfl) ⟨2156732, by rfl⟩ : syracuseStep 2875643 = 4313465) B4313465
theorem B2875769 : Blo 1277957 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B1917305 : Blo 1277957 1917305 := bstep (se 2 (by rfl) ⟨718989, by rfl⟩ : syracuseStep 1917305 = 1437979) B1437979
theorem B89858423 : Blo 1277957 89858423 := bstep (se 1 (by rfl) ⟨67393817, by rfl⟩ : syracuseStep 89858423 = 134787635) B134787635
theorem B1278447 : Blo 1277957 1278447 := bstep (se 1 (by rfl) ⟨958835, by rfl⟩ : syracuseStep 1278447 = 1917671) B1917671
theorem B10371665 : Blo 1277957 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B14574167 : Blo 1277957 14574167 := bstep (se 1 (by rfl) ⟨10930625, by rfl⟩ : syracuseStep 14574167 = 21861251) B21861251
theorem B10920581 : Blo 1277957 10920581 := bstep (se 4 (by rfl) ⟨1023804, by rfl⟩ : syracuseStep 10920581 = 2047609) B2047609
theorem B1917599 : Blo 1277957 1917599 := bstep (se 1 (by rfl) ⟨1438199, by rfl⟩ : syracuseStep 1917599 = 2876399) B2876399
theorem B1278623 : Blo 1277957 1278623 := bstep (se 1 (by rfl) ⟨958967, by rfl⟩ : syracuseStep 1278623 = 1917935) B1917935
theorem B1278703 : Blo 1277957 1278703 := bstep (se 1 (by rfl) ⟨959027, by rfl⟩ : syracuseStep 1278703 = 1918055) B1918055
theorem B1917767 : Blo 1277957 1917767 := bstep (se 1 (by rfl) ⟨1438325, by rfl⟩ : syracuseStep 1917767 = 2876651) B2876651
theorem B7283803 : Blo 1277957 7283803 := bstep (se 1 (by rfl) ⟨5462852, by rfl⟩ : syracuseStep 7283803 = 10925705) B10925705
theorem B2876543 : Blo 1277957 2876543 := bstep (se 1 (by rfl) ⟨2157407, by rfl⟩ : syracuseStep 2876543 = 4314815) B4314815
theorem B1279135 : Blo 1277957 1279135 := bstep (se 1 (by rfl) ⟨959351, by rfl⟩ : syracuseStep 1279135 = 1918703) B1918703
theorem B6472871 : Blo 1277957 6472871 := bstep (se 1 (by rfl) ⟨4854653, by rfl⟩ : syracuseStep 6472871 = 9709307) B9709307
theorem B4318433 : Blo 1277957 4318433 := bstep (se 2 (by rfl) ⟨1619412, by rfl⟩ : syracuseStep 4318433 = 3238825) B3238825
theorem B1279303 : Blo 1277957 1279303 := bstep (se 1 (by rfl) ⟨959477, by rfl⟩ : syracuseStep 1279303 = 1918955) B1918955
theorem B9717083 : Blo 1277957 9717083 := bstep (se 1 (by rfl) ⟨7287812, by rfl⟩ : syracuseStep 9717083 = 14575625) B14575625
theorem B1918439 : Blo 1277957 1918439 := bstep (se 1 (by rfl) ⟨1438829, by rfl⟩ : syracuseStep 1918439 = 2877659) B2877659
theorem B4859423 : Blo 1277957 4859423 := bstep (se 1 (by rfl) ⟨3644567, by rfl⟩ : syracuseStep 4859423 = 7289135) B7289135
theorem B1943131 : Blo 1277957 1943131 := bstep (se 1 (by rfl) ⟨1457348, by rfl⟩ : syracuseStep 1943131 = 2914697) B2914697
theorem B10930079 : Blo 1277957 10930079 := bstep (se 1 (by rfl) ⟨8197559, by rfl⟩ : syracuseStep 10930079 = 16395119) B16395119
theorem B18442151 : Blo 1277957 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B2877479 : Blo 1277957 2877479 := bstep (se 1 (by rfl) ⟨2158109, by rfl⟩ : syracuseStep 2877479 = 4316219) B4316219
theorem B2157097 : Blo 1277957 2157097 := bstep (se 2 (by rfl) ⟨808911, by rfl⟩ : syracuseStep 2157097 = 1617823) B1617823
theorem B1919615 : Blo 1277957 1919615 := bstep (se 1 (by rfl) ⟨1439711, by rfl⟩ : syracuseStep 1919615 = 2879423) B2879423
theorem B1919807 : Blo 1277957 1919807 := bstep (se 1 (by rfl) ⟨1439855, by rfl⟩ : syracuseStep 1919807 = 2879711) B2879711
theorem B3075259 : Blo 1277957 3075259 := bstep (se 1 (by rfl) ⟨2306444, by rfl⟩ : syracuseStep 3075259 = 4612889) B4612889
theorem B2428231 : Blo 1277957 2428231 := bstep (se 1 (by rfl) ⟨1821173, by rfl⟩ : syracuseStep 2428231 = 3642347) B3642347
theorem B2878793 : Blo 1277957 2878793 := bstep (se 2 (by rfl) ⟨1079547, by rfl⟩ : syracuseStep 2878793 = 2159095) B2159095
theorem B2878811 : Blo 1277957 2878811 := bstep (se 1 (by rfl) ⟨2159108, by rfl⟩ : syracuseStep 2878811 = 4318217) B4318217
theorem B10505807 : Blo 1277957 10505807 := bstep (se 1 (by rfl) ⟨7879355, by rfl⟩ : syracuseStep 10505807 = 15758711) B15758711
theorem B2879081 : Blo 1277957 2879081 := bstep (se 2 (by rfl) ⟨1079655, by rfl⟩ : syracuseStep 2879081 = 2159311) B2159311
theorem B7286537 : Blo 1277957 7286537 := bstep (se 2 (by rfl) ⟨2732451, by rfl⟩ : syracuseStep 7286537 = 5464903) B5464903
theorem B31133585 : Blo 1277957 31133585 := bstep (se 2 (by rfl) ⟨11675094, by rfl⟩ : syracuseStep 31133585 = 23350189) B23350189
theorem B3641287 : Blo 1277957 3641287 := bstep (se 1 (by rfl) ⟨2730965, by rfl⟩ : syracuseStep 3641287 = 5461931) B5461931
theorem B2158535 : Blo 1277957 2158535 := bstep (se 1 (by rfl) ⟨1618901, by rfl⟩ : syracuseStep 2158535 = 3237803) B3237803
theorem B23654591 : Blo 1277957 23654591 := bstep (se 1 (by rfl) ⟨17740943, by rfl⟩ : syracuseStep 23654591 = 35481887) B35481887
theorem B2429203 : Blo 1277957 2429203 := bstep (se 1 (by rfl) ⟨1821902, by rfl⟩ : syracuseStep 2429203 = 3643805) B3643805
theorem B8745403 : Blo 1277957 8745403 := bstep (se 1 (by rfl) ⟨6559052, by rfl⟩ : syracuseStep 8745403 = 13118105) B13118105
theorem B41480693 : Blo 1277957 41480693 := bstep (se 5 (by rfl) ⟨1944407, by rfl⟩ : syracuseStep 41480693 = 3888815) B3888815
theorem B3641993 : Blo 1277957 3641993 := bstep (se 2 (by rfl) ⟨1365747, by rfl⟩ : syracuseStep 3641993 = 2731495) B2731495
theorem B1438375 : Blo 1277957 1438375 := bstep (se 1 (by rfl) ⟨1078781, by rfl⟩ : syracuseStep 1438375 = 2157563) B2157563
theorem B4314707 : Blo 1277957 4314707 := bstep (se 1 (by rfl) ⟨3236030, by rfl⟩ : syracuseStep 4314707 = 6472061) B6472061
theorem B4437631 : Blo 1277957 4437631 := bstep (se 1 (by rfl) ⟨3328223, by rfl⟩ : syracuseStep 4437631 = 6656447) B6656447
theorem B14571251 : Blo 1277957 14571251 := bstep (se 1 (by rfl) ⟨10928438, by rfl⟩ : syracuseStep 14571251 = 21856877) B21856877
theorem B4609889 : Blo 1277957 4609889 := bstep (se 2 (by rfl) ⟨1728708, by rfl⟩ : syracuseStep 4609889 = 3457417) B3457417
theorem B3692447 : Blo 1277957 3692447 := bstep (se 1 (by rfl) ⟨2769335, by rfl⟩ : syracuseStep 3692447 = 5538671) B5538671
theorem B336328787 : Blo 1277957 336328787 := bstep (se 1 (by rfl) ⟨252246590, by rfl⟩ : syracuseStep 336328787 = 504493181) B504493181
theorem B6478217 : Blo 1277957 6478217 := bstep (se 2 (by rfl) ⟨2429331, by rfl⟩ : syracuseStep 6478217 = 4858663) B4858663
theorem B14006695 : Blo 1277957 14006695 := bstep (se 1 (by rfl) ⟨10505021, by rfl⟩ : syracuseStep 14006695 = 21010043) B21010043
theorem B26958253 : Blo 1277957 26958253 := bstep (se 3 (by rfl) ⟨5054672, by rfl⟩ : syracuseStep 26958253 = 10109345) B10109345
theorem B14572709 : Blo 1277957 14572709 := bstep (se 4 (by rfl) ⟨1366191, by rfl⟩ : syracuseStep 14572709 = 2732383) B2732383
theorem B11664587 : Blo 1277957 11664587 := bstep (se 1 (by rfl) ⟨8748440, by rfl⟩ : syracuseStep 11664587 = 17496881) B17496881
theorem B3235079 : Blo 1277957 3235079 := bstep (se 1 (by rfl) ⟨2426309, by rfl⟩ : syracuseStep 3235079 = 4852619) B4852619
theorem B3456695 : Blo 1277957 3456695 := bstep (se 1 (by rfl) ⟨2592521, by rfl⟩ : syracuseStep 3456695 = 5185043) B5185043
theorem B479084219 : Blo 1277957 479084219 := bstep (se 1 (by rfl) ⟨359313164, by rfl⟩ : syracuseStep 479084219 = 718626329) B718626329
theorem B7388911 : Blo 1277957 7388911 := bstep (se 1 (by rfl) ⟨5541683, by rfl⟩ : syracuseStep 7388911 = 11083367) B11083367
theorem B1916999 : Blo 1277957 1916999 := bstep (se 1 (by rfl) ⟨1437749, by rfl⟩ : syracuseStep 1916999 = 2875499) B2875499
theorem B15769727 : Blo 1277957 15769727 := bstep (se 1 (by rfl) ⟨11827295, by rfl⟩ : syracuseStep 15769727 = 23654591) B23654591
theorem B1917095 : Blo 1277957 1917095 := bstep (se 1 (by rfl) ⟨1437821, by rfl⟩ : syracuseStep 1917095 = 2875643) B2875643
theorem B1917179 : Blo 1277957 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B1278203 : Blo 1277957 1278203 := bstep (se 1 (by rfl) ⟨958652, by rfl⟩ : syracuseStep 1278203 = 1917305) B1917305
theorem B9716111 : Blo 1277957 9716111 := bstep (se 1 (by rfl) ⟨7287083, by rfl⟩ : syracuseStep 9716111 = 14574167) B14574167
theorem B1278399 : Blo 1277957 1278399 := bstep (se 1 (by rfl) ⟨958799, by rfl⟩ : syracuseStep 1278399 = 1917599) B1917599
theorem B31105565 : Blo 1277957 31105565 := bstep (se 3 (by rfl) ⟨5832293, by rfl⟩ : syracuseStep 31105565 = 11664587) B11664587
theorem B1278511 : Blo 1277957 1278511 := bstep (se 1 (by rfl) ⟨958883, by rfl⟩ : syracuseStep 1278511 = 1917767) B1917767
theorem B23667365 : Blo 1277957 23667365 := bstep (se 4 (by rfl) ⟨2218815, by rfl⟩ : syracuseStep 23667365 = 4437631) B4437631
theorem B2876129 : Blo 1277957 2876129 := bstep (se 2 (by rfl) ⟨1078548, by rfl⟩ : syracuseStep 2876129 = 2157097) B2157097
theorem B1917695 : Blo 1277957 1917695 := bstep (se 1 (by rfl) ⟨1438271, by rfl⟩ : syracuseStep 1917695 = 2876543) B2876543
theorem B1917833 : Blo 1277957 1917833 := bstep (se 2 (by rfl) ⟨719187, by rfl⟩ : syracuseStep 1917833 = 1438375) B1438375
theorem B1278959 : Blo 1277957 1278959 := bstep (se 1 (by rfl) ⟨959219, by rfl⟩ : syracuseStep 1278959 = 1918439) B1918439
theorem B2876471 : Blo 1277957 2876471 := bstep (se 1 (by rfl) ⟨2157353, by rfl⟩ : syracuseStep 2876471 = 4314707) B4314707
theorem B3073259 : Blo 1277957 3073259 := bstep (se 1 (by rfl) ⟨2304944, by rfl⟩ : syracuseStep 3073259 = 4609889) B4609889
theorem B1918319 : Blo 1277957 1918319 := bstep (se 1 (by rfl) ⟨1438739, by rfl⟩ : syracuseStep 1918319 = 2877479) B2877479
theorem B27657773 : Blo 1277957 27657773 := bstep (se 3 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 27657773 = 10371665) B10371665
theorem B4318811 : Blo 1277957 4318811 := bstep (se 1 (by rfl) ⟨3239108, by rfl⟩ : syracuseStep 4318811 = 6478217) B6478217
theorem B1279743 : Blo 1277957 1279743 := bstep (se 1 (by rfl) ⟨959807, by rfl⟩ : syracuseStep 1279743 = 1919615) B1919615
theorem B3237641 : Blo 1277957 3237641 := bstep (se 2 (by rfl) ⟨1214115, by rfl⟩ : syracuseStep 3237641 = 2428231) B2428231
theorem B1279871 : Blo 1277957 1279871 := bstep (se 1 (by rfl) ⟨959903, by rfl⟩ : syracuseStep 1279871 = 1919807) B1919807
theorem B2590841 : Blo 1277957 2590841 := bstep (se 2 (by rfl) ⟨971565, by rfl⟩ : syracuseStep 2590841 = 1943131) B1943131
theorem B2156719 : Blo 1277957 2156719 := bstep (se 1 (by rfl) ⟨1617539, by rfl⟩ : syracuseStep 2156719 = 3235079) B3235079
theorem B1919195 : Blo 1277957 1919195 := bstep (se 1 (by rfl) ⟨1439396, by rfl⟩ : syracuseStep 1919195 = 2878793) B2878793
theorem B1919207 : Blo 1277957 1919207 := bstep (se 1 (by rfl) ⟨1439405, by rfl⟩ : syracuseStep 1919207 = 2878811) B2878811
theorem B1919387 : Blo 1277957 1919387 := bstep (se 1 (by rfl) ⟨1439540, by rfl⟩ : syracuseStep 1919387 = 2879081) B2879081
theorem B2304463 : Blo 1277957 2304463 := bstep (se 1 (by rfl) ⟨1728347, by rfl⟩ : syracuseStep 2304463 = 3456695) B3456695
theorem B9710279 : Blo 1277957 9710279 := bstep (se 1 (by rfl) ⟨7282709, by rfl⟩ : syracuseStep 9710279 = 14565419) B14565419
theorem B9219025 : Blo 1277957 9219025 := bstep (se 2 (by rfl) ⟨3457134, by rfl⟩ : syracuseStep 9219025 = 6914269) B6914269
theorem B3238937 : Blo 1277957 3238937 := bstep (se 2 (by rfl) ⟨1214601, by rfl⟩ : syracuseStep 3238937 = 2429203) B2429203
theorem B2427995 : Blo 1277957 2427995 := bstep (se 1 (by rfl) ⟨1820996, by rfl⟩ : syracuseStep 2427995 = 3641993) B3641993
theorem B11660537 : Blo 1277957 11660537 := bstep (se 2 (by rfl) ⟨4372701, by rfl⟩ : syracuseStep 11660537 = 8745403) B8745403
theorem B2878955 : Blo 1277957 2878955 := bstep (se 1 (by rfl) ⟨2159216, by rfl⟩ : syracuseStep 2878955 = 4318433) B4318433
theorem B3239615 : Blo 1277957 3239615 := bstep (se 1 (by rfl) ⟨2429711, by rfl⟩ : syracuseStep 3239615 = 4859423) B4859423
theorem B2461631 : Blo 1277957 2461631 := bstep (se 1 (by rfl) ⟨1846223, by rfl⟩ : syracuseStep 2461631 = 3692447) B3692447
theorem B7286719 : Blo 1277957 7286719 := bstep (se 1 (by rfl) ⟨5465039, by rfl⟩ : syracuseStep 7286719 = 10930079) B10930079
theorem B224219191 : Blo 1277957 224219191 := bstep (se 1 (by rfl) ⟨168164393, by rfl⟩ : syracuseStep 224219191 = 336328787) B336328787
theorem B9711737 : Blo 1277957 9711737 := bstep (se 2 (by rfl) ⟨3641901, by rfl⟩ : syracuseStep 9711737 = 7283803) B7283803
theorem B4100345 : Blo 1277957 4100345 := bstep (se 2 (by rfl) ⟨1537629, by rfl⟩ : syracuseStep 4100345 = 3075259) B3075259
theorem B9851881 : Blo 1277957 9851881 := bstep (se 2 (by rfl) ⟨3694455, by rfl⟩ : syracuseStep 9851881 = 7388911) B7388911
theorem B83022893 : Blo 1277957 83022893 := bstep (se 3 (by rfl) ⟨15566792, by rfl⟩ : syracuseStep 83022893 = 31133585) B31133585
theorem B4855049 : Blo 1277957 4855049 := bstep (se 2 (by rfl) ⟨1820643, by rfl⟩ : syracuseStep 4855049 = 3641287) B3641287
theorem B1439023 : Blo 1277957 1439023 := bstep (se 1 (by rfl) ⟨1079267, by rfl⟩ : syracuseStep 1439023 = 2158535) B2158535
theorem B4855247 : Blo 1277957 4855247 := bstep (se 1 (by rfl) ⟨3641435, by rfl⟩ : syracuseStep 4855247 = 7282871) B7282871
theorem B27653795 : Blo 1277957 27653795 := bstep (se 1 (by rfl) ⟨20740346, by rfl⟩ : syracuseStep 27653795 = 41480693) B41480693
theorem B7280387 : Blo 1277957 7280387 := bstep (se 1 (by rfl) ⟨5460290, by rfl⟩ : syracuseStep 7280387 = 10920581) B10920581
theorem B18675593 : Blo 1277957 18675593 := bstep (se 2 (by rfl) ⟨7003347, by rfl⟩ : syracuseStep 18675593 = 14006695) B14006695
theorem B35944337 : Blo 1277957 35944337 := bstep (se 2 (by rfl) ⟨13479126, by rfl⟩ : syracuseStep 35944337 = 26958253) B26958253
theorem B4315247 : Blo 1277957 4315247 := bstep (se 1 (by rfl) ⟨3236435, by rfl⟩ : syracuseStep 4315247 = 6472871) B6472871
theorem B6478055 : Blo 1277957 6478055 := bstep (se 1 (by rfl) ⟨4858541, by rfl⟩ : syracuseStep 6478055 = 9717083) B9717083
theorem B239622461 : Blo 1277957 239622461 := bstep (se 3 (by rfl) ⟨44929211, by rfl⟩ : syracuseStep 239622461 = 89858423) B89858423
theorem B9714167 : Blo 1277957 9714167 := bstep (se 1 (by rfl) ⟨7285625, by rfl⟩ : syracuseStep 9714167 = 14571251) B14571251
theorem B12294767 : Blo 1277957 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B9715139 : Blo 1277957 9715139 := bstep (se 1 (by rfl) ⟨7286354, by rfl⟩ : syracuseStep 9715139 = 14572709) B14572709
theorem B7003871 : Blo 1277957 7003871 := bstep (se 1 (by rfl) ⟨5252903, by rfl⟩ : syracuseStep 7003871 = 10505807) B10505807
theorem B319389479 : Blo 1277957 319389479 := bstep (se 1 (by rfl) ⟨239542109, by rfl⟩ : syracuseStep 319389479 = 479084219) B479084219
theorem B4857691 : Blo 1277957 4857691 := bstep (se 1 (by rfl) ⟨3643268, by rfl⟩ : syracuseStep 4857691 = 7286537) B7286537
theorem B1277999 : Blo 1277957 1277999 := bstep (se 1 (by rfl) ⟨958499, by rfl⟩ : syracuseStep 1277999 = 1916999) B1916999
theorem B298958921 : Blo 1277957 298958921 := bstep (se 2 (by rfl) ⟨112109595, by rfl⟩ : syracuseStep 298958921 = 224219191) B224219191
theorem B1278063 : Blo 1277957 1278063 := bstep (se 1 (by rfl) ⟨958547, by rfl⟩ : syracuseStep 1278063 = 1917095) B1917095
theorem B1278119 : Blo 1277957 1278119 := bstep (se 1 (by rfl) ⟨958589, by rfl⟩ : syracuseStep 1278119 = 1917179) B1917179
theorem B2875625 : Blo 1277957 2875625 := bstep (se 2 (by rfl) ⟨1078359, by rfl⟩ : syracuseStep 2875625 = 2156719) B2156719
theorem B15778243 : Blo 1277957 15778243 := bstep (se 1 (by rfl) ⟨11833682, by rfl⟩ : syracuseStep 15778243 = 23667365) B23667365
theorem B1917419 : Blo 1277957 1917419 := bstep (se 1 (by rfl) ⟨1438064, by rfl⟩ : syracuseStep 1917419 = 2876129) B2876129
theorem B1278463 : Blo 1277957 1278463 := bstep (se 1 (by rfl) ⟨958847, by rfl⟩ : syracuseStep 1278463 = 1917695) B1917695
theorem B1278555 : Blo 1277957 1278555 := bstep (se 1 (by rfl) ⟨958916, by rfl⟩ : syracuseStep 1278555 = 1917833) B1917833
theorem B3072617 : Blo 1277957 3072617 := bstep (se 2 (by rfl) ⟨1152231, by rfl⟩ : syracuseStep 3072617 = 2304463) B2304463
theorem B1917647 : Blo 1277957 1917647 := bstep (se 1 (by rfl) ⟨1438235, by rfl⟩ : syracuseStep 1917647 = 2876471) B2876471
theorem B3236699 : Blo 1277957 3236699 := bstep (se 1 (by rfl) ⟨2427524, by rfl⟩ : syracuseStep 3236699 = 4855049) B4855049
theorem B1278879 : Blo 1277957 1278879 := bstep (se 1 (by rfl) ⟨959159, by rfl⟩ : syracuseStep 1278879 = 1918319) B1918319
theorem B3236831 : Blo 1277957 3236831 := bstep (se 1 (by rfl) ⟨2427623, by rfl⟩ : syracuseStep 3236831 = 4855247) B4855247
theorem B2876831 : Blo 1277957 2876831 := bstep (se 1 (by rfl) ⟨2157623, by rfl⟩ : syracuseStep 2876831 = 4315247) B4315247
theorem B1279463 : Blo 1277957 1279463 := bstep (se 1 (by rfl) ⟨959597, by rfl⟩ : syracuseStep 1279463 = 1919195) B1919195
theorem B1279471 : Blo 1277957 1279471 := bstep (se 1 (by rfl) ⟨959603, by rfl⟩ : syracuseStep 1279471 = 1919207) B1919207
theorem B4318703 : Blo 1277957 4318703 := bstep (se 1 (by rfl) ⟨3239027, by rfl⟩ : syracuseStep 4318703 = 6478055) B6478055
theorem B1279591 : Blo 1277957 1279591 := bstep (se 1 (by rfl) ⟨959693, by rfl⟩ : syracuseStep 1279591 = 1919387) B1919387
theorem B1918697 : Blo 1277957 1918697 := bstep (se 2 (by rfl) ⟨719511, by rfl⟩ : syracuseStep 1918697 = 1439023) B1439023
theorem B6473519 : Blo 1277957 6473519 := bstep (se 1 (by rfl) ⟨4855139, by rfl⟩ : syracuseStep 6473519 = 9710279) B9710279
theorem B1919303 : Blo 1277957 1919303 := bstep (se 1 (by rfl) ⟨1439477, by rfl⟩ : syracuseStep 1919303 = 2878955) B2878955
theorem B6564349 : Blo 1277957 6564349 := bstep (se 3 (by rfl) ⟨1230815, by rfl⟩ : syracuseStep 6564349 = 2461631) B2461631
theorem B6474491 : Blo 1277957 6474491 := bstep (se 1 (by rfl) ⟨4855868, by rfl⟩ : syracuseStep 6474491 = 9711737) B9711737
theorem B10513151 : Blo 1277957 10513151 := bstep (se 1 (by rfl) ⟨7884863, by rfl⟩ : syracuseStep 10513151 = 15769727) B15769727
theorem B6474653 : Blo 1277957 6474653 := bstep (se 3 (by rfl) ⟨1213997, by rfl⟩ : syracuseStep 6474653 = 2427995) B2427995
theorem B20737043 : Blo 1277957 20737043 := bstep (se 1 (by rfl) ⟨15552782, by rfl⟩ : syracuseStep 20737043 = 31105565) B31105565
theorem B8195357 : Blo 1277957 8195357 := bstep (se 3 (by rfl) ⟨1536629, by rfl⟩ : syracuseStep 8195357 = 3073259) B3073259
theorem B55348595 : Blo 1277957 55348595 := bstep (se 1 (by rfl) ⟨41511446, by rfl⟩ : syracuseStep 55348595 = 83022893) B83022893
theorem B2879207 : Blo 1277957 2879207 := bstep (se 1 (by rfl) ⟨2159405, by rfl⟩ : syracuseStep 2879207 = 4318811) B4318811
theorem B18435863 : Blo 1277957 18435863 := bstep (se 1 (by rfl) ⟨13826897, by rfl⟩ : syracuseStep 18435863 = 27653795) B27653795
theorem B4853591 : Blo 1277957 4853591 := bstep (se 1 (by rfl) ⟨3640193, by rfl⟩ : syracuseStep 4853591 = 7280387) B7280387
theorem B2158427 : Blo 1277957 2158427 := bstep (se 1 (by rfl) ⟨1618820, by rfl⟩ : syracuseStep 2158427 = 3237641) B3237641
theorem B13135841 : Blo 1277957 13135841 := bstep (se 2 (by rfl) ⟨4925940, by rfl⟩ : syracuseStep 13135841 = 9851881) B9851881
theorem B159748307 : Blo 1277957 159748307 := bstep (se 1 (by rfl) ⟨119811230, by rfl⟩ : syracuseStep 159748307 = 239622461) B239622461
theorem B6476111 : Blo 1277957 6476111 := bstep (se 1 (by rfl) ⟨4857083, by rfl⟩ : syracuseStep 6476111 = 9714167) B9714167
theorem B8196511 : Blo 1277957 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B2159291 : Blo 1277957 2159291 := bstep (se 1 (by rfl) ⟨1619468, by rfl⟩ : syracuseStep 2159291 = 3238937) B3238937
theorem B6476759 : Blo 1277957 6476759 := bstep (se 1 (by rfl) ⟨4857569, by rfl⟩ : syracuseStep 6476759 = 9715139) B9715139
theorem B95851565 : Blo 1277957 95851565 := bstep (se 3 (by rfl) ⟨17972168, by rfl⟩ : syracuseStep 95851565 = 35944337) B35944337
theorem B6476921 : Blo 1277957 6476921 := bstep (se 2 (by rfl) ⟨2428845, by rfl⟩ : syracuseStep 6476921 = 4857691) B4857691
theorem B2159743 : Blo 1277957 2159743 := bstep (se 1 (by rfl) ⟨1619807, by rfl⟩ : syracuseStep 2159743 = 3239615) B3239615
theorem B2733563 : Blo 1277957 2733563 := bstep (se 1 (by rfl) ⟨2050172, by rfl⟩ : syracuseStep 2733563 = 4100345) B4100345
theorem B6477407 : Blo 1277957 6477407 := bstep (se 1 (by rfl) ⟨4858055, by rfl⟩ : syracuseStep 6477407 = 9716111) B9716111
theorem B31094765 : Blo 1277957 31094765 := bstep (se 3 (by rfl) ⟨5830268, by rfl⟩ : syracuseStep 31094765 = 11660537) B11660537
theorem B18438515 : Blo 1277957 18438515 := bstep (se 1 (by rfl) ⟨13828886, by rfl⟩ : syracuseStep 18438515 = 27657773) B27657773
theorem B12450395 : Blo 1277957 12450395 := bstep (se 1 (by rfl) ⟨9337796, by rfl⟩ : syracuseStep 12450395 = 18675593) B18675593
theorem B1727227 : Blo 1277957 1727227 := bstep (se 1 (by rfl) ⟨1295420, by rfl⟩ : syracuseStep 1727227 = 2590841) B2590841
theorem B49168133 : Blo 1277957 49168133 := bstep (se 4 (by rfl) ⟨4609512, by rfl⟩ : syracuseStep 49168133 = 9219025) B9219025
theorem B4669247 : Blo 1277957 4669247 := bstep (se 1 (by rfl) ⟨3501935, by rfl⟩ : syracuseStep 4669247 = 7003871) B7003871
theorem B212926319 : Blo 1277957 212926319 := bstep (se 1 (by rfl) ⟨159694739, by rfl⟩ : syracuseStep 212926319 = 319389479) B319389479
theorem B9715625 : Blo 1277957 9715625 := bstep (se 2 (by rfl) ⟨3643359, by rfl⟩ : syracuseStep 9715625 = 7286719) B7286719
theorem B1917083 : Blo 1277957 1917083 := bstep (se 1 (by rfl) ⟨1437812, by rfl⟩ : syracuseStep 1917083 = 2875625) B2875625
theorem B4317407 : Blo 1277957 4317407 := bstep (se 1 (by rfl) ⟨3238055, by rfl⟩ : syracuseStep 4317407 = 6476111) B6476111
theorem B1278279 : Blo 1277957 1278279 := bstep (se 1 (by rfl) ⟨958709, by rfl⟩ : syracuseStep 1278279 = 1917419) B1917419
theorem B2048411 : Blo 1277957 2048411 := bstep (se 1 (by rfl) ⟨1536308, by rfl⟩ : syracuseStep 2048411 = 3072617) B3072617
theorem B1278431 : Blo 1277957 1278431 := bstep (se 1 (by rfl) ⟨958823, by rfl⟩ : syracuseStep 1278431 = 1917647) B1917647
theorem B10928681 : Blo 1277957 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B21037657 : Blo 1277957 21037657 := bstep (se 2 (by rfl) ⟨7889121, by rfl⟩ : syracuseStep 21037657 = 15778243) B15778243
theorem B4317839 : Blo 1277957 4317839 := bstep (se 1 (by rfl) ⟨3238379, by rfl⟩ : syracuseStep 4317839 = 6476759) B6476759
theorem B4317947 : Blo 1277957 4317947 := bstep (se 1 (by rfl) ⟨3238460, by rfl⟩ : syracuseStep 4317947 = 6476921) B6476921
theorem B1917887 : Blo 1277957 1917887 := bstep (se 1 (by rfl) ⟨1438415, by rfl⟩ : syracuseStep 1917887 = 2876831) B2876831
theorem B4318271 : Blo 1277957 4318271 := bstep (se 1 (by rfl) ⟨3238703, by rfl⟩ : syracuseStep 4318271 = 6477407) B6477407
theorem B1279131 : Blo 1277957 1279131 := bstep (se 1 (by rfl) ⟨959348, by rfl⟩ : syracuseStep 1279131 = 1918697) B1918697
theorem B1279535 : Blo 1277957 1279535 := bstep (se 1 (by rfl) ⟨959651, by rfl⟩ : syracuseStep 1279535 = 1919303) B1919303
theorem B36899063 : Blo 1277957 36899063 := bstep (se 1 (by rfl) ⟨27674297, by rfl⟩ : syracuseStep 36899063 = 55348595) B55348595
theorem B1919471 : Blo 1277957 1919471 := bstep (se 1 (by rfl) ⟨1439603, by rfl⟩ : syracuseStep 1919471 = 2879207) B2879207
theorem B32778755 : Blo 1277957 32778755 := bstep (se 1 (by rfl) ⟨24584066, by rfl⟩ : syracuseStep 32778755 = 49168133) B49168133
theorem B12290575 : Blo 1277957 12290575 := bstep (se 1 (by rfl) ⟨9217931, by rfl⟩ : syracuseStep 12290575 = 18435863) B18435863
theorem B199305947 : Blo 1277957 199305947 := bstep (se 1 (by rfl) ⟨149479460, by rfl⟩ : syracuseStep 199305947 = 298958921) B298958921
theorem B106498871 : Blo 1277957 106498871 := bstep (se 1 (by rfl) ⟨79874153, by rfl⟩ : syracuseStep 106498871 = 159748307) B159748307
theorem B2157799 : Blo 1277957 2157799 := bstep (se 1 (by rfl) ⟨1618349, by rfl⟩ : syracuseStep 2157799 = 3236699) B3236699
theorem B2157887 : Blo 1277957 2157887 := bstep (se 1 (by rfl) ⟨1618415, by rfl⟩ : syracuseStep 2157887 = 3236831) B3236831
theorem B8752465 : Blo 1277957 8752465 := bstep (se 2 (by rfl) ⟨3282174, by rfl⟩ : syracuseStep 8752465 = 6564349) B6564349
theorem B63901043 : Blo 1277957 63901043 := bstep (se 1 (by rfl) ⟨47925782, by rfl⟩ : syracuseStep 63901043 = 95851565) B95851565
theorem B2879135 : Blo 1277957 2879135 := bstep (se 1 (by rfl) ⟨2159351, by rfl⟩ : syracuseStep 2879135 = 4318703) B4318703
theorem B1822375 : Blo 1277957 1822375 := bstep (se 1 (by rfl) ⟨1366781, by rfl⟩ : syracuseStep 1822375 = 2733563) B2733563
theorem B9211877 : Blo 1277957 9211877 := bstep (se 4 (by rfl) ⟨863613, by rfl⟩ : syracuseStep 9211877 = 1727227) B1727227
theorem B20729843 : Blo 1277957 20729843 := bstep (se 1 (by rfl) ⟨15547382, by rfl⟩ : syracuseStep 20729843 = 31094765) B31094765
theorem B2879657 : Blo 1277957 2879657 := bstep (se 2 (by rfl) ⟨1079871, by rfl⟩ : syracuseStep 2879657 = 2159743) B2159743
theorem B12292343 : Blo 1277957 12292343 := bstep (se 1 (by rfl) ⟨9219257, by rfl⟩ : syracuseStep 12292343 = 18438515) B18438515
theorem B7008767 : Blo 1277957 7008767 := bstep (se 1 (by rfl) ⟨5256575, by rfl⟩ : syracuseStep 7008767 = 10513151) B10513151
theorem B13824695 : Blo 1277957 13824695 := bstep (se 1 (by rfl) ⟨10368521, by rfl⟩ : syracuseStep 13824695 = 20737043) B20737043
theorem B1438951 : Blo 1277957 1438951 := bstep (se 1 (by rfl) ⟨1079213, by rfl⟩ : syracuseStep 1438951 = 2158427) B2158427
theorem B6477083 : Blo 1277957 6477083 := bstep (se 1 (by rfl) ⟨4857812, by rfl⟩ : syracuseStep 6477083 = 9715625) B9715625
theorem B1439527 : Blo 1277957 1439527 := bstep (se 1 (by rfl) ⟨1079645, by rfl⟩ : syracuseStep 1439527 = 2159291) B2159291
theorem B4315679 : Blo 1277957 4315679 := bstep (se 1 (by rfl) ⟨3236759, by rfl⟩ : syracuseStep 4315679 = 6473519) B6473519
theorem B33201053 : Blo 1277957 33201053 := bstep (se 3 (by rfl) ⟨6225197, by rfl⟩ : syracuseStep 33201053 = 12450395) B12450395
theorem B4316327 : Blo 1277957 4316327 := bstep (se 1 (by rfl) ⟨3237245, by rfl⟩ : syracuseStep 4316327 = 6474491) B6474491
theorem B4316435 : Blo 1277957 4316435 := bstep (se 1 (by rfl) ⟨3237326, by rfl⟩ : syracuseStep 4316435 = 6474653) B6474653
theorem B5463571 : Blo 1277957 5463571 := bstep (se 1 (by rfl) ⟨4097678, by rfl⟩ : syracuseStep 5463571 = 8195357) B8195357
theorem B3112831 : Blo 1277957 3112831 := bstep (se 1 (by rfl) ⟨2334623, by rfl⟩ : syracuseStep 3112831 = 4669247) B4669247
theorem B3235727 : Blo 1277957 3235727 := bstep (se 1 (by rfl) ⟨2426795, by rfl⟩ : syracuseStep 3235727 = 4853591) B4853591
theorem B141950879 : Blo 1277957 141950879 := bstep (se 1 (by rfl) ⟨106463159, by rfl⟩ : syracuseStep 141950879 = 212926319) B212926319
theorem B8757227 : Blo 1277957 8757227 := bstep (se 1 (by rfl) ⟨6567920, by rfl⟩ : syracuseStep 8757227 = 13135841) B13135841
theorem B1278055 : Blo 1277957 1278055 := bstep (se 1 (by rfl) ⟨958541, by rfl⟩ : syracuseStep 1278055 = 1917083) B1917083
theorem B9216463 : Blo 1277957 9216463 := bstep (se 1 (by rfl) ⟨6912347, by rfl⟩ : syracuseStep 9216463 = 13824695) B13824695
theorem B1278591 : Blo 1277957 1278591 := bstep (se 1 (by rfl) ⟨958943, by rfl⟩ : syracuseStep 1278591 = 1917887) B1917887
theorem B28050209 : Blo 1277957 28050209 := bstep (se 2 (by rfl) ⟨10518828, by rfl⟩ : syracuseStep 28050209 = 21037657) B21037657
theorem B4318055 : Blo 1277957 4318055 := bstep (se 1 (by rfl) ⟨3238541, by rfl⟩ : syracuseStep 4318055 = 6477083) B6477083
theorem B2877065 : Blo 1277957 2877065 := bstep (se 2 (by rfl) ⟨1078899, by rfl⟩ : syracuseStep 2877065 = 2157799) B2157799
theorem B1918601 : Blo 1277957 1918601 := bstep (se 2 (by rfl) ⟨719475, by rfl⟩ : syracuseStep 1918601 = 1438951) B1438951
theorem B1279647 : Blo 1277957 1279647 := bstep (se 1 (by rfl) ⟨959735, by rfl⟩ : syracuseStep 1279647 = 1919471) B1919471
theorem B2877119 : Blo 1277957 2877119 := bstep (se 1 (by rfl) ⟨2157839, by rfl⟩ : syracuseStep 2877119 = 4315679) B4315679
theorem B7284761 : Blo 1277957 7284761 := bstep (se 2 (by rfl) ⟨2731785, by rfl⟩ : syracuseStep 7284761 = 5463571) B5463571
theorem B2877551 : Blo 1277957 2877551 := bstep (se 1 (by rfl) ⟨2158163, by rfl⟩ : syracuseStep 2877551 = 4316327) B4316327
theorem B2877623 : Blo 1277957 2877623 := bstep (se 1 (by rfl) ⟨2158217, by rfl⟩ : syracuseStep 2877623 = 4316435) B4316435
theorem B42600695 : Blo 1277957 42600695 := bstep (se 1 (by rfl) ⟨31950521, by rfl⟩ : syracuseStep 42600695 = 63901043) B63901043
theorem B1919369 : Blo 1277957 1919369 := bstep (se 2 (by rfl) ⟨719763, by rfl⟩ : syracuseStep 1919369 = 1439527) B1439527
theorem B1919423 : Blo 1277957 1919423 := bstep (se 1 (by rfl) ⟨1439567, by rfl⟩ : syracuseStep 1919423 = 2879135) B2879135
theorem B2157151 : Blo 1277957 2157151 := bstep (se 1 (by rfl) ⟨1617863, by rfl⟩ : syracuseStep 2157151 = 3235727) B3235727
theorem B1919771 : Blo 1277957 1919771 := bstep (se 1 (by rfl) ⟨1439828, by rfl⟩ : syracuseStep 1919771 = 2879657) B2879657
theorem B2878271 : Blo 1277957 2878271 := bstep (se 1 (by rfl) ⟨2158703, by rfl⟩ : syracuseStep 2878271 = 4317407) B4317407
theorem B8194895 : Blo 1277957 8194895 := bstep (se 1 (by rfl) ⟨6146171, by rfl⟩ : syracuseStep 8194895 = 12292343) B12292343
theorem B4672511 : Blo 1277957 4672511 := bstep (se 1 (by rfl) ⟨3504383, by rfl⟩ : syracuseStep 4672511 = 7008767) B7008767
theorem B7285787 : Blo 1277957 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B2878559 : Blo 1277957 2878559 := bstep (se 1 (by rfl) ⟨2158919, by rfl⟩ : syracuseStep 2878559 = 4317839) B4317839
theorem B2878631 : Blo 1277957 2878631 := bstep (se 1 (by rfl) ⟨2158973, by rfl⟩ : syracuseStep 2878631 = 4317947) B4317947
theorem B16387433 : Blo 1277957 16387433 := bstep (se 2 (by rfl) ⟨6145287, by rfl⟩ : syracuseStep 16387433 = 12290575) B12290575
theorem B2878847 : Blo 1277957 2878847 := bstep (se 1 (by rfl) ⟨2159135, by rfl⟩ : syracuseStep 2878847 = 4318271) B4318271
theorem B21852503 : Blo 1277957 21852503 := bstep (se 1 (by rfl) ⟨16389377, by rfl⟩ : syracuseStep 21852503 = 32778755) B32778755
theorem B11669953 : Blo 1277957 11669953 := bstep (se 2 (by rfl) ⟨4376232, by rfl⟩ : syracuseStep 11669953 = 8752465) B8752465
theorem B132870631 : Blo 1277957 132870631 := bstep (se 1 (by rfl) ⟨99652973, by rfl⟩ : syracuseStep 132870631 = 199305947) B199305947
theorem B16601765 : Blo 1277957 16601765 := bstep (se 4 (by rfl) ⟨1556415, by rfl⟩ : syracuseStep 16601765 = 3112831) B3112831
theorem B1438591 : Blo 1277957 1438591 := bstep (se 1 (by rfl) ⟨1078943, by rfl⟩ : syracuseStep 1438591 = 2157887) B2157887
theorem B2429833 : Blo 1277957 2429833 := bstep (se 2 (by rfl) ⟨911187, by rfl⟩ : syracuseStep 2429833 = 1822375) B1822375
theorem B6141251 : Blo 1277957 6141251 := bstep (se 1 (by rfl) ⟨4605938, by rfl⟩ : syracuseStep 6141251 = 9211877) B9211877
theorem B5838151 : Blo 1277957 5838151 := bstep (se 1 (by rfl) ⟨4378613, by rfl⟩ : syracuseStep 5838151 = 8757227) B8757227
theorem B1365607 : Blo 1277957 1365607 := bstep (se 1 (by rfl) ⟨1024205, by rfl⟩ : syracuseStep 1365607 = 2048411) B2048411
theorem B24599375 : Blo 1277957 24599375 := bstep (se 1 (by rfl) ⟨18449531, by rfl⟩ : syracuseStep 24599375 = 36899063) B36899063
theorem B70999247 : Blo 1277957 70999247 := bstep (se 1 (by rfl) ⟨53249435, by rfl⟩ : syracuseStep 70999247 = 106498871) B106498871
theorem B22134035 : Blo 1277957 22134035 := bstep (se 1 (by rfl) ⟨16600526, by rfl⟩ : syracuseStep 22134035 = 33201053) B33201053
theorem B94633919 : Blo 1277957 94633919 := bstep (se 1 (by rfl) ⟨70975439, by rfl⟩ : syracuseStep 94633919 = 141950879) B141950879
theorem B13819895 : Blo 1277957 13819895 := bstep (se 1 (by rfl) ⟨10364921, by rfl⟩ : syracuseStep 13819895 = 20729843) B20729843
theorem B12288617 : Blo 1277957 12288617 := bstep (se 2 (by rfl) ⟨4608231, by rfl⟩ : syracuseStep 12288617 = 9216463) B9216463
theorem B177160841 : Blo 1277957 177160841 := bstep (se 2 (by rfl) ⟨66435315, by rfl⟩ : syracuseStep 177160841 = 132870631) B132870631
theorem B2876201 : Blo 1277957 2876201 := bstep (se 2 (by rfl) ⟨1078575, by rfl⟩ : syracuseStep 2876201 = 2157151) B2157151
theorem B1918043 : Blo 1277957 1918043 := bstep (se 1 (by rfl) ⟨1438532, by rfl⟩ : syracuseStep 1918043 = 2877065) B2877065
theorem B1279067 : Blo 1277957 1279067 := bstep (se 1 (by rfl) ⟨959300, by rfl⟩ : syracuseStep 1279067 = 1918601) B1918601
theorem B1918079 : Blo 1277957 1918079 := bstep (se 1 (by rfl) ⟨1438559, by rfl⟩ : syracuseStep 1918079 = 2877119) B2877119
theorem B1918121 : Blo 1277957 1918121 := bstep (se 2 (by rfl) ⟨719295, by rfl⟩ : syracuseStep 1918121 = 1438591) B1438591
theorem B1918367 : Blo 1277957 1918367 := bstep (se 1 (by rfl) ⟨1438775, by rfl⟩ : syracuseStep 1918367 = 2877551) B2877551
theorem B1918415 : Blo 1277957 1918415 := bstep (se 1 (by rfl) ⟨1438811, by rfl⟩ : syracuseStep 1918415 = 2877623) B2877623
theorem B1279579 : Blo 1277957 1279579 := bstep (se 1 (by rfl) ⟨959684, by rfl⟩ : syracuseStep 1279579 = 1919369) B1919369
theorem B1279615 : Blo 1277957 1279615 := bstep (se 1 (by rfl) ⟨959711, by rfl⟩ : syracuseStep 1279615 = 1919423) B1919423
theorem B7784201 : Blo 1277957 7784201 := bstep (se 2 (by rfl) ⟨2919075, by rfl⟩ : syracuseStep 7784201 = 5838151) B5838151
theorem B44271373 : Blo 1277957 44271373 := bstep (se 3 (by rfl) ⟨8300882, by rfl⟩ : syracuseStep 44271373 = 16601765) B16601765
theorem B1279847 : Blo 1277957 1279847 := bstep (se 1 (by rfl) ⟨959885, by rfl⟩ : syracuseStep 1279847 = 1919771) B1919771
theorem B1918847 : Blo 1277957 1918847 := bstep (se 1 (by rfl) ⟨1439135, by rfl⟩ : syracuseStep 1918847 = 2878271) B2878271
theorem B3115007 : Blo 1277957 3115007 := bstep (se 1 (by rfl) ⟨2336255, by rfl⟩ : syracuseStep 3115007 = 4672511) B4672511
theorem B1919039 : Blo 1277957 1919039 := bstep (se 1 (by rfl) ⟨1439279, by rfl⟩ : syracuseStep 1919039 = 2878559) B2878559
theorem B1919087 : Blo 1277957 1919087 := bstep (se 1 (by rfl) ⟨1439315, by rfl⟩ : syracuseStep 1919087 = 2878631) B2878631
theorem B1820809 : Blo 1277957 1820809 := bstep (se 2 (by rfl) ⟨682803, by rfl⟩ : syracuseStep 1820809 = 1365607) B1365607
theorem B14756023 : Blo 1277957 14756023 := bstep (se 1 (by rfl) ⟨11067017, by rfl⟩ : syracuseStep 14756023 = 22134035) B22134035
theorem B1919231 : Blo 1277957 1919231 := bstep (se 1 (by rfl) ⟨1439423, by rfl⟩ : syracuseStep 1919231 = 2878847) B2878847
theorem B63089279 : Blo 1277957 63089279 := bstep (se 1 (by rfl) ⟨47316959, by rfl⟩ : syracuseStep 63089279 = 94633919) B94633919
theorem B14568335 : Blo 1277957 14568335 := bstep (se 1 (by rfl) ⟨10926251, by rfl⟩ : syracuseStep 14568335 = 21852503) B21852503
theorem B2878703 : Blo 1277957 2878703 := bstep (se 1 (by rfl) ⟨2159027, by rfl⟩ : syracuseStep 2878703 = 4318055) B4318055
theorem B15559937 : Blo 1277957 15559937 := bstep (se 2 (by rfl) ⟨5834976, by rfl⟩ : syracuseStep 15559937 = 11669953) B11669953
theorem B113601853 : Blo 1277957 113601853 := bstep (se 3 (by rfl) ⟨21300347, by rfl⟩ : syracuseStep 113601853 = 42600695) B42600695
theorem B3239777 : Blo 1277957 3239777 := bstep (se 2 (by rfl) ⟨1214916, by rfl⟩ : syracuseStep 3239777 = 2429833) B2429833
theorem B10924955 : Blo 1277957 10924955 := bstep (se 1 (by rfl) ⟨8193716, by rfl⟩ : syracuseStep 10924955 = 16387433) B16387433
theorem B9213263 : Blo 1277957 9213263 := bstep (se 1 (by rfl) ⟨6909947, by rfl⟩ : syracuseStep 9213263 = 13819895) B13819895
theorem B18700139 : Blo 1277957 18700139 := bstep (se 1 (by rfl) ⟨14025104, by rfl⟩ : syracuseStep 18700139 = 28050209) B28050209
theorem B4094167 : Blo 1277957 4094167 := bstep (se 1 (by rfl) ⟨3070625, by rfl⟩ : syracuseStep 4094167 = 6141251) B6141251
theorem B4856507 : Blo 1277957 4856507 := bstep (se 1 (by rfl) ⟨3642380, by rfl⟩ : syracuseStep 4856507 = 7284761) B7284761
theorem B5463263 : Blo 1277957 5463263 := bstep (se 1 (by rfl) ⟨4097447, by rfl⟩ : syracuseStep 5463263 = 8194895) B8194895
theorem B16399583 : Blo 1277957 16399583 := bstep (se 1 (by rfl) ⟨12299687, by rfl⟩ : syracuseStep 16399583 = 24599375) B24599375
theorem B4857191 : Blo 1277957 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B47332831 : Blo 1277957 47332831 := bstep (se 1 (by rfl) ⟨35499623, by rfl⟩ : syracuseStep 47332831 = 70999247) B70999247
theorem B8192411 : Blo 1277957 8192411 := bstep (se 1 (by rfl) ⟨6144308, by rfl⟩ : syracuseStep 8192411 = 12288617) B12288617
theorem B1917467 : Blo 1277957 1917467 := bstep (se 1 (by rfl) ⟨1438100, by rfl⟩ : syracuseStep 1917467 = 2876201) B2876201
theorem B7283303 : Blo 1277957 7283303 := bstep (se 1 (by rfl) ⟨5462477, by rfl⟩ : syracuseStep 7283303 = 10924955) B10924955
theorem B1278695 : Blo 1277957 1278695 := bstep (se 1 (by rfl) ⟨959021, by rfl⟩ : syracuseStep 1278695 = 1918043) B1918043
theorem B1278719 : Blo 1277957 1278719 := bstep (se 1 (by rfl) ⟨959039, by rfl⟩ : syracuseStep 1278719 = 1918079) B1918079
theorem B1278747 : Blo 1277957 1278747 := bstep (se 1 (by rfl) ⟨959060, by rfl⟩ : syracuseStep 1278747 = 1918121) B1918121
theorem B1278911 : Blo 1277957 1278911 := bstep (se 1 (by rfl) ⟨959183, by rfl⟩ : syracuseStep 1278911 = 1918367) B1918367
theorem B1278943 : Blo 1277957 1278943 := bstep (se 1 (by rfl) ⟨959207, by rfl⟩ : syracuseStep 1278943 = 1918415) B1918415
theorem B1279231 : Blo 1277957 1279231 := bstep (se 1 (by rfl) ⟨959423, by rfl⟩ : syracuseStep 1279231 = 1918847) B1918847
theorem B1279359 : Blo 1277957 1279359 := bstep (se 1 (by rfl) ⟨959519, by rfl⟩ : syracuseStep 1279359 = 1919039) B1919039
theorem B1279391 : Blo 1277957 1279391 := bstep (se 1 (by rfl) ⟨959543, by rfl⟩ : syracuseStep 1279391 = 1919087) B1919087
theorem B1279487 : Blo 1277957 1279487 := bstep (se 1 (by rfl) ⟨959615, by rfl⟩ : syracuseStep 1279487 = 1919231) B1919231
theorem B42059519 : Blo 1277957 42059519 := bstep (se 1 (by rfl) ⟨31544639, by rfl⟩ : syracuseStep 42059519 = 63089279) B63089279
theorem B3237671 : Blo 1277957 3237671 := bstep (se 1 (by rfl) ⟨2428253, by rfl⟩ : syracuseStep 3237671 = 4856507) B4856507
theorem B1919135 : Blo 1277957 1919135 := bstep (se 1 (by rfl) ⟨1439351, by rfl⟩ : syracuseStep 1919135 = 2878703) B2878703
theorem B10373291 : Blo 1277957 10373291 := bstep (se 1 (by rfl) ⟨7779968, by rfl⟩ : syracuseStep 10373291 = 15559937) B15559937
theorem B3238127 : Blo 1277957 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B2427745 : Blo 1277957 2427745 := bstep (se 2 (by rfl) ⟨910404, by rfl⟩ : syracuseStep 2427745 = 1820809) B1820809
theorem B5458889 : Blo 1277957 5458889 := bstep (se 2 (by rfl) ⟨2047083, by rfl⟩ : syracuseStep 5458889 = 4094167) B4094167
theorem B118107227 : Blo 1277957 118107227 := bstep (se 1 (by rfl) ⟨88580420, by rfl⟩ : syracuseStep 118107227 = 177160841) B177160841
theorem B5189467 : Blo 1277957 5189467 := bstep (se 1 (by rfl) ⟨3892100, by rfl⟩ : syracuseStep 5189467 = 7784201) B7784201
theorem B2076671 : Blo 1277957 2076671 := bstep (se 1 (by rfl) ⟨1557503, by rfl⟩ : syracuseStep 2076671 = 3115007) B3115007
theorem B9712223 : Blo 1277957 9712223 := bstep (se 1 (by rfl) ⟨7284167, by rfl⟩ : syracuseStep 9712223 = 14568335) B14568335
theorem B3642175 : Blo 1277957 3642175 := bstep (se 1 (by rfl) ⟨2731631, by rfl⟩ : syracuseStep 3642175 = 5463263) B5463263
theorem B10933055 : Blo 1277957 10933055 := bstep (se 1 (by rfl) ⟨8199791, by rfl⟩ : syracuseStep 10933055 = 16399583) B16399583
theorem B59028497 : Blo 1277957 59028497 := bstep (se 2 (by rfl) ⟨22135686, by rfl⟩ : syracuseStep 59028497 = 44271373) B44271373
theorem B2159851 : Blo 1277957 2159851 := bstep (se 1 (by rfl) ⟨1619888, by rfl⟩ : syracuseStep 2159851 = 3239777) B3239777
theorem B19674697 : Blo 1277957 19674697 := bstep (se 2 (by rfl) ⟨7378011, by rfl⟩ : syracuseStep 19674697 = 14756023) B14756023
theorem B6142175 : Blo 1277957 6142175 := bstep (se 1 (by rfl) ⟨4606631, by rfl⟩ : syracuseStep 6142175 = 9213263) B9213263
theorem B12466759 : Blo 1277957 12466759 := bstep (se 1 (by rfl) ⟨9350069, by rfl⟩ : syracuseStep 12466759 = 18700139) B18700139
theorem B151469137 : Blo 1277957 151469137 := bstep (se 2 (by rfl) ⟨56800926, by rfl⟩ : syracuseStep 151469137 = 113601853) B113601853
theorem B63110441 : Blo 1277957 63110441 := bstep (se 2 (by rfl) ⟨23666415, by rfl⟩ : syracuseStep 63110441 = 47332831) B47332831
theorem B1278311 : Blo 1277957 1278311 := bstep (se 1 (by rfl) ⟨958733, by rfl⟩ : syracuseStep 1278311 = 1917467) B1917467
theorem B16622345 : Blo 1277957 16622345 := bstep (se 2 (by rfl) ⟨6233379, by rfl⟩ : syracuseStep 16622345 = 12466759) B12466759
theorem B3236993 : Blo 1277957 3236993 := bstep (se 2 (by rfl) ⟨1213872, by rfl⟩ : syracuseStep 3236993 = 2427745) B2427745
theorem B1279423 : Blo 1277957 1279423 := bstep (se 1 (by rfl) ⟨959567, by rfl⟩ : syracuseStep 1279423 = 1919135) B1919135
theorem B201958849 : Blo 1277957 201958849 := bstep (se 2 (by rfl) ⟨75734568, by rfl⟩ : syracuseStep 201958849 = 151469137) B151469137
theorem B6915527 : Blo 1277957 6915527 := bstep (se 1 (by rfl) ⟨5186645, by rfl⟩ : syracuseStep 6915527 = 10373291) B10373291
theorem B3639259 : Blo 1277957 3639259 := bstep (se 1 (by rfl) ⟨2729444, by rfl⟩ : syracuseStep 3639259 = 5458889) B5458889
theorem B26232929 : Blo 1277957 26232929 := bstep (se 2 (by rfl) ⟨9837348, by rfl⟩ : syracuseStep 26232929 = 19674697) B19674697
theorem B6474815 : Blo 1277957 6474815 := bstep (se 1 (by rfl) ⟨4856111, by rfl⟩ : syracuseStep 6474815 = 9712223) B9712223
theorem B2158447 : Blo 1277957 2158447 := bstep (se 1 (by rfl) ⟨1618835, by rfl⟩ : syracuseStep 2158447 = 3237671) B3237671
theorem B2158751 : Blo 1277957 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B2879801 : Blo 1277957 2879801 := bstep (se 2 (by rfl) ⟨1079925, by rfl⟩ : syracuseStep 2879801 = 2159851) B2159851
theorem B78738151 : Blo 1277957 78738151 := bstep (se 1 (by rfl) ⟨59053613, by rfl⟩ : syracuseStep 78738151 = 118107227) B118107227
theorem B6919289 : Blo 1277957 6919289 := bstep (se 2 (by rfl) ⟨2594733, by rfl⟩ : syracuseStep 6919289 = 5189467) B5189467
theorem B5461607 : Blo 1277957 5461607 := bstep (se 1 (by rfl) ⟨4096205, by rfl⟩ : syracuseStep 5461607 = 8192411) B8192411
theorem B4855535 : Blo 1277957 4855535 := bstep (se 1 (by rfl) ⟨3641651, by rfl⟩ : syracuseStep 4855535 = 7283303) B7283303
theorem B7288703 : Blo 1277957 7288703 := bstep (se 1 (by rfl) ⟨5466527, by rfl⟩ : syracuseStep 7288703 = 10933055) B10933055
theorem B39352331 : Blo 1277957 39352331 := bstep (se 1 (by rfl) ⟨29514248, by rfl⟩ : syracuseStep 39352331 = 59028497) B59028497
theorem B4856233 : Blo 1277957 4856233 := bstep (se 2 (by rfl) ⟨1821087, by rfl⟩ : syracuseStep 4856233 = 3642175) B3642175
theorem B28039679 : Blo 1277957 28039679 := bstep (se 1 (by rfl) ⟨21029759, by rfl⟩ : syracuseStep 28039679 = 42059519) B42059519
theorem B4094783 : Blo 1277957 4094783 := bstep (se 1 (by rfl) ⟨3071087, by rfl⟩ : syracuseStep 4094783 = 6142175) B6142175
theorem B42073627 : Blo 1277957 42073627 := bstep (se 1 (by rfl) ⟨31555220, by rfl⟩ : syracuseStep 42073627 = 63110441) B63110441
theorem B1384447 : Blo 1277957 1384447 := bstep (se 1 (by rfl) ⟨1038335, by rfl⟩ : syracuseStep 1384447 = 2076671) B2076671
theorem B4612859 : Blo 1277957 4612859 := bstep (se 1 (by rfl) ⟨3459644, by rfl⟩ : syracuseStep 4612859 = 6919289) B6919289
theorem B3237023 : Blo 1277957 3237023 := bstep (se 1 (by rfl) ⟨2427767, by rfl⟩ : syracuseStep 3237023 = 4855535) B4855535
theorem B4859135 : Blo 1277957 4859135 := bstep (se 1 (by rfl) ⟨3644351, by rfl⟩ : syracuseStep 4859135 = 7288703) B7288703
theorem B2729855 : Blo 1277957 2729855 := bstep (se 1 (by rfl) ⟨2047391, by rfl⟩ : syracuseStep 2729855 = 4094783) B4094783
theorem B2877929 : Blo 1277957 2877929 := bstep (se 2 (by rfl) ⟨1079223, by rfl⟩ : syracuseStep 2877929 = 2158447) B2158447
theorem B4852345 : Blo 1277957 4852345 := bstep (se 2 (by rfl) ⟨1819629, by rfl⟩ : syracuseStep 4852345 = 3639259) B3639259
theorem B1845929 : Blo 1277957 1845929 := bstep (se 2 (by rfl) ⟨692223, by rfl⟩ : syracuseStep 1845929 = 1384447) B1384447
theorem B1919867 : Blo 1277957 1919867 := bstep (se 1 (by rfl) ⟨1439900, by rfl⟩ : syracuseStep 1919867 = 2879801) B2879801
theorem B6474977 : Blo 1277957 6474977 := bstep (se 2 (by rfl) ⟨2428116, by rfl⟩ : syracuseStep 6474977 = 4856233) B4856233
theorem B2157995 : Blo 1277957 2157995 := bstep (se 1 (by rfl) ⟨1618496, by rfl⟩ : syracuseStep 2157995 = 3236993) B3236993
theorem B104984201 : Blo 1277957 104984201 := bstep (se 2 (by rfl) ⟨39369075, by rfl⟩ : syracuseStep 104984201 = 78738151) B78738151
theorem B3641071 : Blo 1277957 3641071 := bstep (se 1 (by rfl) ⟨2730803, by rfl⟩ : syracuseStep 3641071 = 5461607) B5461607
theorem B26234887 : Blo 1277957 26234887 := bstep (se 1 (by rfl) ⟨19676165, by rfl⟩ : syracuseStep 26234887 = 39352331) B39352331
theorem B1439167 : Blo 1277957 1439167 := bstep (se 1 (by rfl) ⟨1079375, by rfl⟩ : syracuseStep 1439167 = 2158751) B2158751
theorem B4610351 : Blo 1277957 4610351 := bstep (se 1 (by rfl) ⟨3457763, by rfl⟩ : syracuseStep 4610351 = 6915527) B6915527
theorem B17488619 : Blo 1277957 17488619 := bstep (se 1 (by rfl) ⟨13116464, by rfl⟩ : syracuseStep 17488619 = 26232929) B26232929
theorem B18693119 : Blo 1277957 18693119 := bstep (se 1 (by rfl) ⟨14019839, by rfl⟩ : syracuseStep 18693119 = 28039679) B28039679
theorem B269278465 : Blo 1277957 269278465 := bstep (se 2 (by rfl) ⟨100979424, by rfl⟩ : syracuseStep 269278465 = 201958849) B201958849
theorem B44326253 : Blo 1277957 44326253 := bstep (se 3 (by rfl) ⟨8311172, by rfl⟩ : syracuseStep 44326253 = 16622345) B16622345
theorem B56098169 : Blo 1277957 56098169 := bstep (se 2 (by rfl) ⟨21036813, by rfl⟩ : syracuseStep 56098169 = 42073627) B42073627
theorem B4316543 : Blo 1277957 4316543 := bstep (se 1 (by rfl) ⟨3237407, by rfl⟩ : syracuseStep 4316543 = 6474815) B6474815
theorem B34979849 : Blo 1277957 34979849 := bstep (se 2 (by rfl) ⟨13117443, by rfl⟩ : syracuseStep 34979849 = 26234887) B26234887
theorem B1819903 : Blo 1277957 1819903 := bstep (se 1 (by rfl) ⟨1364927, by rfl⟩ : syracuseStep 1819903 = 2729855) B2729855
theorem B3073567 : Blo 1277957 3073567 := bstep (se 1 (by rfl) ⟨2305175, by rfl⟩ : syracuseStep 3073567 = 4610351) B4610351
theorem B1918619 : Blo 1277957 1918619 := bstep (se 1 (by rfl) ⟨1438964, by rfl⟩ : syracuseStep 1918619 = 2877929) B2877929
theorem B11659079 : Blo 1277957 11659079 := bstep (se 1 (by rfl) ⟨8744309, by rfl⟩ : syracuseStep 11659079 = 17488619) B17488619
theorem B1279911 : Blo 1277957 1279911 := bstep (se 1 (by rfl) ⟨959933, by rfl⟩ : syracuseStep 1279911 = 1919867) B1919867
theorem B1918889 : Blo 1277957 1918889 := bstep (se 2 (by rfl) ⟨719583, by rfl⟩ : syracuseStep 1918889 = 1439167) B1439167
theorem B12462079 : Blo 1277957 12462079 := bstep (se 1 (by rfl) ⟨9346559, by rfl⟩ : syracuseStep 12462079 = 18693119) B18693119
theorem B29550835 : Blo 1277957 29550835 := bstep (se 1 (by rfl) ⟨22163126, by rfl⟩ : syracuseStep 29550835 = 44326253) B44326253
theorem B37398779 : Blo 1277957 37398779 := bstep (se 1 (by rfl) ⟨28049084, by rfl⟩ : syracuseStep 37398779 = 56098169) B56098169
theorem B2877695 : Blo 1277957 2877695 := bstep (se 1 (by rfl) ⟨2158271, by rfl⟩ : syracuseStep 2877695 = 4316543) B4316543
theorem B3075239 : Blo 1277957 3075239 := bstep (se 1 (by rfl) ⟨2306429, by rfl⟩ : syracuseStep 3075239 = 4612859) B4612859
theorem B2158015 : Blo 1277957 2158015 := bstep (se 1 (by rfl) ⟨1618511, by rfl⟩ : syracuseStep 2158015 = 3237023) B3237023
theorem B3239423 : Blo 1277957 3239423 := bstep (se 1 (by rfl) ⟨2429567, by rfl⟩ : syracuseStep 3239423 = 4859135) B4859135
theorem B1438663 : Blo 1277957 1438663 := bstep (se 1 (by rfl) ⟨1078997, by rfl⟩ : syracuseStep 1438663 = 2157995) B2157995
theorem B4854761 : Blo 1277957 4854761 := bstep (se 2 (by rfl) ⟨1820535, by rfl⟩ : syracuseStep 4854761 = 3641071) B3641071
theorem B69989467 : Blo 1277957 69989467 := bstep (se 1 (by rfl) ⟨52492100, by rfl⟩ : syracuseStep 69989467 = 104984201) B104984201
theorem B6469793 : Blo 1277957 6469793 := bstep (se 2 (by rfl) ⟨2426172, by rfl⟩ : syracuseStep 6469793 = 4852345) B4852345
theorem B359037953 : Blo 1277957 359037953 := bstep (se 2 (by rfl) ⟨134639232, by rfl⟩ : syracuseStep 359037953 = 269278465) B269278465
theorem B4922477 : Blo 1277957 4922477 := bstep (se 3 (by rfl) ⟨922964, by rfl⟩ : syracuseStep 4922477 = 1845929) B1845929
theorem B4316651 : Blo 1277957 4316651 := bstep (se 1 (by rfl) ⟨3237488, by rfl⟩ : syracuseStep 4316651 = 6474977) B6474977
theorem B3236507 : Blo 1277957 3236507 := bstep (se 1 (by rfl) ⟨2427380, by rfl⟩ : syracuseStep 3236507 = 4854761) B4854761
theorem B1279079 : Blo 1277957 1279079 := bstep (se 1 (by rfl) ⟨959309, by rfl⟩ : syracuseStep 1279079 = 1918619) B1918619
theorem B1918217 : Blo 1277957 1918217 := bstep (se 2 (by rfl) ⟨719331, by rfl⟩ : syracuseStep 1918217 = 1438663) B1438663
theorem B1279259 : Blo 1277957 1279259 := bstep (se 1 (by rfl) ⟨959444, by rfl⟩ : syracuseStep 1279259 = 1918889) B1918889
theorem B1918463 : Blo 1277957 1918463 := bstep (se 1 (by rfl) ⟨1438847, by rfl⟩ : syracuseStep 1918463 = 2877695) B2877695
theorem B2426537 : Blo 1277957 2426537 := bstep (se 2 (by rfl) ⟨909951, by rfl⟩ : syracuseStep 2426537 = 1819903) B1819903
theorem B2877353 : Blo 1277957 2877353 := bstep (se 2 (by rfl) ⟨1079007, by rfl⟩ : syracuseStep 2877353 = 2158015) B2158015
theorem B4098089 : Blo 1277957 4098089 := bstep (se 2 (by rfl) ⟨1536783, by rfl⟩ : syracuseStep 4098089 = 3073567) B3073567
theorem B2050159 : Blo 1277957 2050159 := bstep (se 1 (by rfl) ⟨1537619, by rfl⟩ : syracuseStep 2050159 = 3075239) B3075239
theorem B2877767 : Blo 1277957 2877767 := bstep (se 1 (by rfl) ⟨2158325, by rfl⟩ : syracuseStep 2877767 = 4316651) B4316651
theorem B16616105 : Blo 1277957 16616105 := bstep (se 2 (by rfl) ⟨6231039, by rfl⟩ : syracuseStep 16616105 = 12462079) B12462079
theorem B4313195 : Blo 1277957 4313195 := bstep (se 1 (by rfl) ⟨3234896, by rfl⟩ : syracuseStep 4313195 = 6469793) B6469793
theorem B93319289 : Blo 1277957 93319289 := bstep (se 2 (by rfl) ⟨34994733, by rfl⟩ : syracuseStep 93319289 = 69989467) B69989467
theorem B24932519 : Blo 1277957 24932519 := bstep (se 1 (by rfl) ⟨18699389, by rfl⟩ : syracuseStep 24932519 = 37398779) B37398779
theorem B239358635 : Blo 1277957 239358635 := bstep (se 1 (by rfl) ⟨179518976, by rfl⟩ : syracuseStep 239358635 = 359037953) B359037953
theorem B3281651 : Blo 1277957 3281651 := bstep (se 1 (by rfl) ⟨2461238, by rfl⟩ : syracuseStep 3281651 = 4922477) B4922477
theorem B2159615 : Blo 1277957 2159615 := bstep (se 1 (by rfl) ⟨1619711, by rfl⟩ : syracuseStep 2159615 = 3239423) B3239423
theorem B23319899 : Blo 1277957 23319899 := bstep (se 1 (by rfl) ⟨17489924, by rfl⟩ : syracuseStep 23319899 = 34979849) B34979849
theorem B39401113 : Blo 1277957 39401113 := bstep (se 2 (by rfl) ⟨14775417, by rfl⟩ : syracuseStep 39401113 = 29550835) B29550835
theorem B7772719 : Blo 1277957 7772719 := bstep (se 1 (by rfl) ⟨5829539, by rfl⟩ : syracuseStep 7772719 = 11659079) B11659079
theorem B2875463 : Blo 1277957 2875463 := bstep (se 1 (by rfl) ⟨2156597, by rfl⟩ : syracuseStep 2875463 = 4313195) B4313195
theorem B16621679 : Blo 1277957 16621679 := bstep (se 1 (by rfl) ⟨12466259, by rfl⟩ : syracuseStep 16621679 = 24932519) B24932519
theorem B159572423 : Blo 1277957 159572423 := bstep (se 1 (by rfl) ⟨119679317, by rfl⟩ : syracuseStep 159572423 = 239358635) B239358635
theorem B2187767 : Blo 1277957 2187767 := bstep (se 1 (by rfl) ⟨1640825, by rfl⟩ : syracuseStep 2187767 = 3281651) B3281651
theorem B10363625 : Blo 1277957 10363625 := bstep (se 2 (by rfl) ⟨3886359, by rfl⟩ : syracuseStep 10363625 = 7772719) B7772719
theorem B1278811 : Blo 1277957 1278811 := bstep (se 1 (by rfl) ⟨959108, by rfl⟩ : syracuseStep 1278811 = 1918217) B1918217
theorem B1278975 : Blo 1277957 1278975 := bstep (se 1 (by rfl) ⟨959231, by rfl⟩ : syracuseStep 1278975 = 1918463) B1918463
theorem B1918235 : Blo 1277957 1918235 := bstep (se 1 (by rfl) ⟨1438676, by rfl⟩ : syracuseStep 1918235 = 2877353) B2877353
theorem B1918511 : Blo 1277957 1918511 := bstep (se 1 (by rfl) ⟨1438883, by rfl⟩ : syracuseStep 1918511 = 2877767) B2877767
theorem B11077403 : Blo 1277957 11077403 := bstep (se 1 (by rfl) ⟨8308052, by rfl⟩ : syracuseStep 11077403 = 16616105) B16616105
theorem B62212859 : Blo 1277957 62212859 := bstep (se 1 (by rfl) ⟨46659644, by rfl⟩ : syracuseStep 62212859 = 93319289) B93319289
theorem B2157671 : Blo 1277957 2157671 := bstep (se 1 (by rfl) ⟨1618253, by rfl⟩ : syracuseStep 2157671 = 3236507) B3236507
theorem B2732059 : Blo 1277957 2732059 := bstep (se 1 (by rfl) ⟨2049044, by rfl⟩ : syracuseStep 2732059 = 4098089) B4098089
theorem B2733545 : Blo 1277957 2733545 := bstep (se 2 (by rfl) ⟨1025079, by rfl⟩ : syracuseStep 2733545 = 2050159) B2050159
theorem B1439743 : Blo 1277957 1439743 := bstep (se 1 (by rfl) ⟨1079807, by rfl⟩ : syracuseStep 1439743 = 2159615) B2159615
theorem B15546599 : Blo 1277957 15546599 := bstep (se 1 (by rfl) ⟨11659949, by rfl⟩ : syracuseStep 15546599 = 23319899) B23319899
theorem B6470765 : Blo 1277957 6470765 := bstep (se 3 (by rfl) ⟨1213268, by rfl⟩ : syracuseStep 6470765 = 2426537) B2426537
theorem B52534817 : Blo 1277957 52534817 := bstep (se 2 (by rfl) ⟨19700556, by rfl⟩ : syracuseStep 52534817 = 39401113) B39401113
theorem B1916975 : Blo 1277957 1916975 := bstep (se 1 (by rfl) ⟨1437731, by rfl⟩ : syracuseStep 1916975 = 2875463) B2875463
theorem B106381615 : Blo 1277957 106381615 := bstep (se 1 (by rfl) ⟨79786211, by rfl⟩ : syracuseStep 106381615 = 159572423) B159572423
theorem B1278823 : Blo 1277957 1278823 := bstep (se 1 (by rfl) ⟨959117, by rfl⟩ : syracuseStep 1278823 = 1918235) B1918235
theorem B1279007 : Blo 1277957 1279007 := bstep (se 1 (by rfl) ⟨959255, by rfl⟩ : syracuseStep 1279007 = 1918511) B1918511
theorem B5834045 : Blo 1277957 5834045 := bstep (se 3 (by rfl) ⟨1093883, by rfl⟩ : syracuseStep 5834045 = 2187767) B2187767
theorem B10364399 : Blo 1277957 10364399 := bstep (se 1 (by rfl) ⟨7773299, by rfl⟩ : syracuseStep 10364399 = 15546599) B15546599
theorem B35023211 : Blo 1277957 35023211 := bstep (se 1 (by rfl) ⟨26267408, by rfl⟩ : syracuseStep 35023211 = 52534817) B52534817
theorem B1919657 : Blo 1277957 1919657 := bstep (se 2 (by rfl) ⟨719871, by rfl⟩ : syracuseStep 1919657 = 1439743) B1439743
theorem B6909083 : Blo 1277957 6909083 := bstep (se 1 (by rfl) ⟨5181812, by rfl⟩ : syracuseStep 6909083 = 10363625) B10363625
theorem B1438447 : Blo 1277957 1438447 := bstep (se 1 (by rfl) ⟨1078835, by rfl⟩ : syracuseStep 1438447 = 2157671) B2157671
theorem B4313843 : Blo 1277957 4313843 := bstep (se 1 (by rfl) ⟨3235382, by rfl⟩ : syracuseStep 4313843 = 6470765) B6470765
theorem B3642745 : Blo 1277957 3642745 := bstep (se 2 (by rfl) ⟨1366029, by rfl⟩ : syracuseStep 3642745 = 2732059) B2732059
theorem B11081119 : Blo 1277957 11081119 := bstep (se 1 (by rfl) ⟨8310839, by rfl⟩ : syracuseStep 11081119 = 16621679) B16621679
theorem B7289453 : Blo 1277957 7289453 := bstep (se 3 (by rfl) ⟨1366772, by rfl⟩ : syracuseStep 7289453 = 2733545) B2733545
theorem B41475239 : Blo 1277957 41475239 := bstep (se 1 (by rfl) ⟨31106429, by rfl⟩ : syracuseStep 41475239 = 62212859) B62212859
theorem B29539741 : Blo 1277957 29539741 := bstep (se 3 (by rfl) ⟨5538701, by rfl⟩ : syracuseStep 29539741 = 11077403) B11077403
theorem B1277983 : Blo 1277957 1277983 := bstep (se 1 (by rfl) ⟨958487, by rfl⟩ : syracuseStep 1277983 = 1916975) B1916975
theorem B2875895 : Blo 1277957 2875895 := bstep (se 1 (by rfl) ⟨2156921, by rfl⟩ : syracuseStep 2875895 = 4313843) B4313843
theorem B15557453 : Blo 1277957 15557453 := bstep (se 3 (by rfl) ⟨2917022, by rfl⟩ : syracuseStep 15557453 = 5834045) B5834045
theorem B1917929 : Blo 1277957 1917929 := bstep (se 2 (by rfl) ⟨719223, by rfl⟩ : syracuseStep 1917929 = 1438447) B1438447
theorem B23348807 : Blo 1277957 23348807 := bstep (se 1 (by rfl) ⟨17511605, by rfl⟩ : syracuseStep 23348807 = 35023211) B35023211
theorem B4859635 : Blo 1277957 4859635 := bstep (se 1 (by rfl) ⟨3644726, by rfl⟩ : syracuseStep 4859635 = 7289453) B7289453
theorem B1279771 : Blo 1277957 1279771 := bstep (se 1 (by rfl) ⟨959828, by rfl⟩ : syracuseStep 1279771 = 1919657) B1919657
theorem B4606055 : Blo 1277957 4606055 := bstep (se 1 (by rfl) ⟨3454541, by rfl⟩ : syracuseStep 4606055 = 6909083) B6909083
theorem B27650159 : Blo 1277957 27650159 := bstep (se 1 (by rfl) ⟨20737619, by rfl⟩ : syracuseStep 27650159 = 41475239) B41475239
theorem B6909599 : Blo 1277957 6909599 := bstep (se 1 (by rfl) ⟨5182199, by rfl⟩ : syracuseStep 6909599 = 10364399) B10364399
theorem B14774825 : Blo 1277957 14774825 := bstep (se 2 (by rfl) ⟨5540559, by rfl⟩ : syracuseStep 14774825 = 11081119) B11081119
theorem B141842153 : Blo 1277957 141842153 := bstep (se 2 (by rfl) ⟨53190807, by rfl⟩ : syracuseStep 141842153 = 106381615) B106381615
theorem B4856993 : Blo 1277957 4856993 := bstep (se 2 (by rfl) ⟨1821372, by rfl⟩ : syracuseStep 4856993 = 3642745) B3642745
theorem B39386321 : Blo 1277957 39386321 := bstep (se 2 (by rfl) ⟨14769870, by rfl⟩ : syracuseStep 39386321 = 29539741) B29539741
theorem B1917263 : Blo 1277957 1917263 := bstep (se 1 (by rfl) ⟨1437947, by rfl⟩ : syracuseStep 1917263 = 2875895) B2875895
theorem B10371635 : Blo 1277957 10371635 := bstep (se 1 (by rfl) ⟨7778726, by rfl⟩ : syracuseStep 10371635 = 15557453) B15557453
theorem B1278619 : Blo 1277957 1278619 := bstep (se 1 (by rfl) ⟨958964, by rfl⟩ : syracuseStep 1278619 = 1917929) B1917929
theorem B15565871 : Blo 1277957 15565871 := bstep (se 1 (by rfl) ⟨11674403, by rfl⟩ : syracuseStep 15565871 = 23348807) B23348807
theorem B94561435 : Blo 1277957 94561435 := bstep (se 1 (by rfl) ⟨70921076, by rfl⟩ : syracuseStep 94561435 = 141842153) B141842153
theorem B18433439 : Blo 1277957 18433439 := bstep (se 1 (by rfl) ⟨13825079, by rfl⟩ : syracuseStep 18433439 = 27650159) B27650159
theorem B3237995 : Blo 1277957 3237995 := bstep (se 1 (by rfl) ⟨2428496, by rfl⟩ : syracuseStep 3237995 = 4856993) B4856993
theorem B26257547 : Blo 1277957 26257547 := bstep (se 1 (by rfl) ⟨19693160, by rfl⟩ : syracuseStep 26257547 = 39386321) B39386321
theorem B4606399 : Blo 1277957 4606399 := bstep (se 1 (by rfl) ⟨3454799, by rfl⟩ : syracuseStep 4606399 = 6909599) B6909599
theorem B9849883 : Blo 1277957 9849883 := bstep (se 1 (by rfl) ⟨7387412, by rfl⟩ : syracuseStep 9849883 = 14774825) B14774825
theorem B3070703 : Blo 1277957 3070703 := bstep (se 1 (by rfl) ⟨2303027, by rfl⟩ : syracuseStep 3070703 = 4606055) B4606055
theorem B6479513 : Blo 1277957 6479513 := bstep (se 2 (by rfl) ⟨2429817, by rfl⟩ : syracuseStep 6479513 = 4859635) B4859635
theorem B1278175 : Blo 1277957 1278175 := bstep (se 1 (by rfl) ⟨958631, by rfl⟩ : syracuseStep 1278175 = 1917263) B1917263
theorem B6914423 : Blo 1277957 6914423 := bstep (se 1 (by rfl) ⟨5185817, by rfl⟩ : syracuseStep 6914423 = 10371635) B10371635
theorem B12288959 : Blo 1277957 12288959 := bstep (se 1 (by rfl) ⟨9216719, by rfl⟩ : syracuseStep 12288959 = 18433439) B18433439
theorem B13133177 : Blo 1277957 13133177 := bstep (se 2 (by rfl) ⟨4924941, by rfl⟩ : syracuseStep 13133177 = 9849883) B9849883
theorem B4319675 : Blo 1277957 4319675 := bstep (se 1 (by rfl) ⟨3239756, by rfl⟩ : syracuseStep 4319675 = 6479513) B6479513
theorem B504327653 : Blo 1277957 504327653 := bstep (se 4 (by rfl) ⟨47280717, by rfl⟩ : syracuseStep 504327653 = 94561435) B94561435
theorem B2158663 : Blo 1277957 2158663 := bstep (se 1 (by rfl) ⟨1618997, by rfl⟩ : syracuseStep 2158663 = 3237995) B3237995
theorem B10377247 : Blo 1277957 10377247 := bstep (se 1 (by rfl) ⟨7782935, by rfl⟩ : syracuseStep 10377247 = 15565871) B15565871
theorem B17505031 : Blo 1277957 17505031 := bstep (se 1 (by rfl) ⟨13128773, by rfl⟩ : syracuseStep 17505031 = 26257547) B26257547
theorem B2047135 : Blo 1277957 2047135 := bstep (se 1 (by rfl) ⟨1535351, by rfl⟩ : syracuseStep 2047135 = 3070703) B3070703
theorem B24567461 : Blo 1277957 24567461 := bstep (se 4 (by rfl) ⟨2303199, by rfl⟩ : syracuseStep 24567461 = 4606399) B4606399
theorem B13836329 : Blo 1277957 13836329 := bstep (se 2 (by rfl) ⟨5188623, by rfl⟩ : syracuseStep 13836329 = 10377247) B10377247
theorem B8192639 : Blo 1277957 8192639 := bstep (se 1 (by rfl) ⟨6144479, by rfl⟩ : syracuseStep 8192639 = 12288959) B12288959
theorem B23340041 : Blo 1277957 23340041 := bstep (se 2 (by rfl) ⟨8752515, by rfl⟩ : syracuseStep 23340041 = 17505031) B17505031
theorem B2729513 : Blo 1277957 2729513 := bstep (se 2 (by rfl) ⟨1023567, by rfl⟩ : syracuseStep 2729513 = 2047135) B2047135
theorem B336218435 : Blo 1277957 336218435 := bstep (se 1 (by rfl) ⟨252163826, by rfl⟩ : syracuseStep 336218435 = 504327653) B504327653
theorem B16378307 : Blo 1277957 16378307 := bstep (se 1 (by rfl) ⟨12283730, by rfl⟩ : syracuseStep 16378307 = 24567461) B24567461
theorem B2878217 : Blo 1277957 2878217 := bstep (se 2 (by rfl) ⟨1079331, by rfl⟩ : syracuseStep 2878217 = 2158663) B2158663
theorem B2879783 : Blo 1277957 2879783 := bstep (se 1 (by rfl) ⟨2159837, by rfl⟩ : syracuseStep 2879783 = 4319675) B4319675
theorem B8755451 : Blo 1277957 8755451 := bstep (se 1 (by rfl) ⟨6566588, by rfl⟩ : syracuseStep 8755451 = 13133177) B13133177
theorem B18438461 : Blo 1277957 18438461 := bstep (se 3 (by rfl) ⟨3457211, by rfl⟩ : syracuseStep 18438461 = 6914423) B6914423
theorem B9224219 : Blo 1277957 9224219 := bstep (se 1 (by rfl) ⟨6918164, by rfl⟩ : syracuseStep 9224219 = 13836329) B13836329
theorem B1819675 : Blo 1277957 1819675 := bstep (se 1 (by rfl) ⟨1364756, by rfl⟩ : syracuseStep 1819675 = 2729513) B2729513
theorem B1918811 : Blo 1277957 1918811 := bstep (se 1 (by rfl) ⟨1439108, by rfl⟩ : syracuseStep 1918811 = 2878217) B2878217
theorem B1919855 : Blo 1277957 1919855 := bstep (se 1 (by rfl) ⟨1439891, by rfl⟩ : syracuseStep 1919855 = 2879783) B2879783
theorem B15560027 : Blo 1277957 15560027 := bstep (se 1 (by rfl) ⟨11670020, by rfl⟩ : syracuseStep 15560027 = 23340041) B23340041
theorem B5836967 : Blo 1277957 5836967 := bstep (se 1 (by rfl) ⟨4377725, by rfl⟩ : syracuseStep 5836967 = 8755451) B8755451
theorem B12292307 : Blo 1277957 12292307 := bstep (se 1 (by rfl) ⟨9219230, by rfl⟩ : syracuseStep 12292307 = 18438461) B18438461
theorem B224145623 : Blo 1277957 224145623 := bstep (se 1 (by rfl) ⟨168109217, by rfl⟩ : syracuseStep 224145623 = 336218435) B336218435
theorem B5461759 : Blo 1277957 5461759 := bstep (se 1 (by rfl) ⟨4096319, by rfl⟩ : syracuseStep 5461759 = 8192639) B8192639
theorem B10918871 : Blo 1277957 10918871 := bstep (se 1 (by rfl) ⟨8189153, by rfl⟩ : syracuseStep 10918871 = 16378307) B16378307
theorem B3891311 : Blo 1277957 3891311 := bstep (se 1 (by rfl) ⟨2918483, by rfl⟩ : syracuseStep 3891311 = 5836967) B5836967
theorem B149430415 : Blo 1277957 149430415 := bstep (se 1 (by rfl) ⟨112072811, by rfl⟩ : syracuseStep 149430415 = 224145623) B224145623
theorem B1279207 : Blo 1277957 1279207 := bstep (se 1 (by rfl) ⟨959405, by rfl⟩ : syracuseStep 1279207 = 1918811) B1918811
theorem B1279903 : Blo 1277957 1279903 := bstep (se 1 (by rfl) ⟨959927, by rfl⟩ : syracuseStep 1279903 = 1919855) B1919855
theorem B10373351 : Blo 1277957 10373351 := bstep (se 1 (by rfl) ⟨7780013, by rfl⟩ : syracuseStep 10373351 = 15560027) B15560027
theorem B8194871 : Blo 1277957 8194871 := bstep (se 1 (by rfl) ⟨6146153, by rfl⟩ : syracuseStep 8194871 = 12292307) B12292307
theorem B7279247 : Blo 1277957 7279247 := bstep (se 1 (by rfl) ⟨5459435, by rfl⟩ : syracuseStep 7279247 = 10918871) B10918871
theorem B6149479 : Blo 1277957 6149479 := bstep (se 1 (by rfl) ⟨4612109, by rfl⟩ : syracuseStep 6149479 = 9224219) B9224219
theorem B9704933 : Blo 1277957 9704933 := bstep (se 4 (by rfl) ⟨909837, by rfl⟩ : syracuseStep 9704933 = 1819675) B1819675
theorem B7282345 : Blo 1277957 7282345 := bstep (se 2 (by rfl) ⟨2730879, by rfl⟩ : syracuseStep 7282345 = 5461759) B5461759
theorem B9709793 : Blo 1277957 9709793 := bstep (se 2 (by rfl) ⟨3641172, by rfl⟩ : syracuseStep 9709793 = 7282345) B7282345
theorem B199240553 : Blo 1277957 199240553 := bstep (se 2 (by rfl) ⟨74715207, by rfl⟩ : syracuseStep 199240553 = 149430415) B149430415
theorem B4852831 : Blo 1277957 4852831 := bstep (se 1 (by rfl) ⟨3639623, by rfl⟩ : syracuseStep 4852831 = 7279247) B7279247
theorem B2594207 : Blo 1277957 2594207 := bstep (se 1 (by rfl) ⟨1945655, by rfl⟩ : syracuseStep 2594207 = 3891311) B3891311
theorem B27662269 : Blo 1277957 27662269 := bstep (se 3 (by rfl) ⟨5186675, by rfl⟩ : syracuseStep 27662269 = 10373351) B10373351
theorem B6469955 : Blo 1277957 6469955 := bstep (se 1 (by rfl) ⟨4852466, by rfl⟩ : syracuseStep 6469955 = 9704933) B9704933
theorem B8199305 : Blo 1277957 8199305 := bstep (se 2 (by rfl) ⟨3074739, by rfl⟩ : syracuseStep 8199305 = 6149479) B6149479
theorem B5463247 : Blo 1277957 5463247 := bstep (se 1 (by rfl) ⟨4097435, by rfl⟩ : syracuseStep 5463247 = 8194871) B8194871
theorem B6473195 : Blo 1277957 6473195 := bstep (se 1 (by rfl) ⟨4854896, by rfl⟩ : syracuseStep 6473195 = 9709793) B9709793
theorem B7284329 : Blo 1277957 7284329 := bstep (se 2 (by rfl) ⟨2731623, by rfl⟩ : syracuseStep 7284329 = 5463247) B5463247
theorem B132827035 : Blo 1277957 132827035 := bstep (se 1 (by rfl) ⟨99620276, by rfl⟩ : syracuseStep 132827035 = 199240553) B199240553
theorem B5466203 : Blo 1277957 5466203 := bstep (se 1 (by rfl) ⟨4099652, by rfl⟩ : syracuseStep 5466203 = 8199305) B8199305
theorem B36883025 : Blo 1277957 36883025 := bstep (se 2 (by rfl) ⟨13831134, by rfl⟩ : syracuseStep 36883025 = 27662269) B27662269
theorem B6917885 : Blo 1277957 6917885 := bstep (se 3 (by rfl) ⟨1297103, by rfl⟩ : syracuseStep 6917885 = 2594207) B2594207
theorem B4313303 : Blo 1277957 4313303 := bstep (se 1 (by rfl) ⟨3234977, by rfl⟩ : syracuseStep 4313303 = 6469955) B6469955
theorem B6470441 : Blo 1277957 6470441 := bstep (se 2 (by rfl) ⟨2426415, by rfl⟩ : syracuseStep 6470441 = 4852831) B4852831
theorem B2875535 : Blo 1277957 2875535 := bstep (se 1 (by rfl) ⟨2156651, by rfl⟩ : syracuseStep 2875535 = 4313303) B4313303
theorem B24588683 : Blo 1277957 24588683 := bstep (se 1 (by rfl) ⟨18441512, by rfl⟩ : syracuseStep 24588683 = 36883025) B36883025
theorem B4313627 : Blo 1277957 4313627 := bstep (se 1 (by rfl) ⟨3235220, by rfl⟩ : syracuseStep 4313627 = 6470441) B6470441
theorem B4315463 : Blo 1277957 4315463 := bstep (se 1 (by rfl) ⟨3236597, by rfl⟩ : syracuseStep 4315463 = 6473195) B6473195
theorem B4856219 : Blo 1277957 4856219 := bstep (se 1 (by rfl) ⟨3642164, by rfl⟩ : syracuseStep 4856219 = 7284329) B7284329
theorem B3644135 : Blo 1277957 3644135 := bstep (se 1 (by rfl) ⟨2733101, by rfl⟩ : syracuseStep 3644135 = 5466203) B5466203
theorem B4611923 : Blo 1277957 4611923 := bstep (se 1 (by rfl) ⟨3458942, by rfl⟩ : syracuseStep 4611923 = 6917885) B6917885
theorem B177102713 : Blo 1277957 177102713 := bstep (se 2 (by rfl) ⟨66413517, by rfl⟩ : syracuseStep 177102713 = 132827035) B132827035
theorem B1917023 : Blo 1277957 1917023 := bstep (se 1 (by rfl) ⟨1437767, by rfl⟩ : syracuseStep 1917023 = 2875535) B2875535
theorem B16392455 : Blo 1277957 16392455 := bstep (se 1 (by rfl) ⟨12294341, by rfl⟩ : syracuseStep 16392455 = 24588683) B24588683
theorem B2875751 : Blo 1277957 2875751 := bstep (se 1 (by rfl) ⟨2156813, by rfl⟩ : syracuseStep 2875751 = 4313627) B4313627
theorem B2876975 : Blo 1277957 2876975 := bstep (se 1 (by rfl) ⟨2157731, by rfl⟩ : syracuseStep 2876975 = 4315463) B4315463
theorem B3237479 : Blo 1277957 3237479 := bstep (se 1 (by rfl) ⟨2428109, by rfl⟩ : syracuseStep 3237479 = 4856219) B4856219
theorem B3074615 : Blo 1277957 3074615 := bstep (se 1 (by rfl) ⟨2305961, by rfl⟩ : syracuseStep 3074615 = 4611923) B4611923
theorem B2429423 : Blo 1277957 2429423 := bstep (se 1 (by rfl) ⟨1822067, by rfl⟩ : syracuseStep 2429423 = 3644135) B3644135
theorem B118068475 : Blo 1277957 118068475 := bstep (se 1 (by rfl) ⟨88551356, by rfl⟩ : syracuseStep 118068475 = 177102713) B177102713
theorem B1278015 : Blo 1277957 1278015 := bstep (se 1 (by rfl) ⟨958511, by rfl⟩ : syracuseStep 1278015 = 1917023) B1917023
theorem B10928303 : Blo 1277957 10928303 := bstep (se 1 (by rfl) ⟨8196227, by rfl⟩ : syracuseStep 10928303 = 16392455) B16392455
theorem B1917167 : Blo 1277957 1917167 := bstep (se 1 (by rfl) ⟨1437875, by rfl⟩ : syracuseStep 1917167 = 2875751) B2875751
theorem B1917983 : Blo 1277957 1917983 := bstep (se 1 (by rfl) ⟨1438487, by rfl⟩ : syracuseStep 1917983 = 2876975) B2876975
theorem B2049743 : Blo 1277957 2049743 := bstep (se 1 (by rfl) ⟨1537307, by rfl⟩ : syracuseStep 2049743 = 3074615) B3074615
theorem B2158319 : Blo 1277957 2158319 := bstep (se 1 (by rfl) ⟨1618739, by rfl⟩ : syracuseStep 2158319 = 3237479) B3237479
theorem B1619615 : Blo 1277957 1619615 := bstep (se 1 (by rfl) ⟨1214711, by rfl⟩ : syracuseStep 1619615 = 2429423) B2429423
theorem B157424633 : Blo 1277957 157424633 := bstep (se 2 (by rfl) ⟨59034237, by rfl⟩ : syracuseStep 157424633 = 118068475) B118068475
theorem B1278111 : Blo 1277957 1278111 := bstep (se 1 (by rfl) ⟨958583, by rfl⟩ : syracuseStep 1278111 = 1917167) B1917167
theorem B1278655 : Blo 1277957 1278655 := bstep (se 1 (by rfl) ⟨958991, by rfl⟩ : syracuseStep 1278655 = 1917983) B1917983
theorem B4318973 : Blo 1277957 4318973 := bstep (se 3 (by rfl) ⟨809807, by rfl⟩ : syracuseStep 4318973 = 1619615) B1619615
theorem B5465981 : Blo 1277957 5465981 := bstep (se 3 (by rfl) ⟨1024871, by rfl⟩ : syracuseStep 5465981 = 2049743) B2049743
theorem B104949755 : Blo 1277957 104949755 := bstep (se 1 (by rfl) ⟨78712316, by rfl⟩ : syracuseStep 104949755 = 157424633) B157424633
theorem B7285535 : Blo 1277957 7285535 := bstep (se 1 (by rfl) ⟨5464151, by rfl⟩ : syracuseStep 7285535 = 10928303) B10928303
theorem B1438879 : Blo 1277957 1438879 := bstep (se 1 (by rfl) ⟨1079159, by rfl⟩ : syracuseStep 1438879 = 2158319) B2158319
theorem B1918505 : Blo 1277957 1918505 := bstep (se 2 (by rfl) ⟨719439, by rfl⟩ : syracuseStep 1918505 = 1438879) B1438879
theorem B2879315 : Blo 1277957 2879315 := bstep (se 1 (by rfl) ⟨2159486, by rfl⟩ : syracuseStep 2879315 = 4318973) B4318973
theorem B3643987 : Blo 1277957 3643987 := bstep (se 1 (by rfl) ⟨2732990, by rfl⟩ : syracuseStep 3643987 = 5465981) B5465981
theorem B69966503 : Blo 1277957 69966503 := bstep (se 1 (by rfl) ⟨52474877, by rfl⟩ : syracuseStep 69966503 = 104949755) B104949755
theorem B4857023 : Blo 1277957 4857023 := bstep (se 1 (by rfl) ⟨3642767, by rfl⟩ : syracuseStep 4857023 = 7285535) B7285535
theorem B4858649 : Blo 1277957 4858649 := bstep (se 2 (by rfl) ⟨1821993, by rfl⟩ : syracuseStep 4858649 = 3643987) B3643987
theorem B1279003 : Blo 1277957 1279003 := bstep (se 1 (by rfl) ⟨959252, by rfl⟩ : syracuseStep 1279003 = 1918505) B1918505
theorem B3238015 : Blo 1277957 3238015 := bstep (se 1 (by rfl) ⟨2428511, by rfl⟩ : syracuseStep 3238015 = 4857023) B4857023
theorem B1919543 : Blo 1277957 1919543 := bstep (se 1 (by rfl) ⟨1439657, by rfl⟩ : syracuseStep 1919543 = 2879315) B2879315
theorem B46644335 : Blo 1277957 46644335 := bstep (se 1 (by rfl) ⟨34983251, by rfl⟩ : syracuseStep 46644335 = 69966503) B69966503
theorem B4317353 : Blo 1277957 4317353 := bstep (se 2 (by rfl) ⟨1619007, by rfl⟩ : syracuseStep 4317353 = 3238015) B3238015
theorem B1279695 : Blo 1277957 1279695 := bstep (se 1 (by rfl) ⟨959771, by rfl⟩ : syracuseStep 1279695 = 1919543) B1919543
theorem B3239099 : Blo 1277957 3239099 := bstep (se 1 (by rfl) ⟨2429324, by rfl⟩ : syracuseStep 3239099 = 4858649) B4858649
theorem B31096223 : Blo 1277957 31096223 := bstep (se 1 (by rfl) ⟨23322167, by rfl⟩ : syracuseStep 31096223 = 46644335) B46644335
theorem B2878235 : Blo 1277957 2878235 := bstep (se 1 (by rfl) ⟨2158676, by rfl⟩ : syracuseStep 2878235 = 4317353) B4317353
theorem B2159399 : Blo 1277957 2159399 := bstep (se 1 (by rfl) ⟨1619549, by rfl⟩ : syracuseStep 2159399 = 3239099) B3239099
theorem B20730815 : Blo 1277957 20730815 := bstep (se 1 (by rfl) ⟨15548111, by rfl⟩ : syracuseStep 20730815 = 31096223) B31096223
theorem B13820543 : Blo 1277957 13820543 := bstep (se 1 (by rfl) ⟨10365407, by rfl⟩ : syracuseStep 13820543 = 20730815) B20730815
theorem B1918823 : Blo 1277957 1918823 := bstep (se 1 (by rfl) ⟨1439117, by rfl⟩ : syracuseStep 1918823 = 2878235) B2878235
theorem B1439599 : Blo 1277957 1439599 := bstep (se 1 (by rfl) ⟨1079699, by rfl⟩ : syracuseStep 1439599 = 2159399) B2159399
theorem B1279215 : Blo 1277957 1279215 := bstep (se 1 (by rfl) ⟨959411, by rfl⟩ : syracuseStep 1279215 = 1918823) B1918823
theorem B1919465 : Blo 1277957 1919465 := bstep (se 2 (by rfl) ⟨719799, by rfl⟩ : syracuseStep 1919465 = 1439599) B1439599
theorem B9213695 : Blo 1277957 9213695 := bstep (se 1 (by rfl) ⟨6910271, by rfl⟩ : syracuseStep 9213695 = 13820543) B13820543
theorem B1279643 : Blo 1277957 1279643 := bstep (se 1 (by rfl) ⟨959732, by rfl⟩ : syracuseStep 1279643 = 1919465) B1919465
theorem B6142463 : Blo 1277957 6142463 := bstep (se 1 (by rfl) ⟨4606847, by rfl⟩ : syracuseStep 6142463 = 9213695) B9213695
theorem B4094975 : Blo 1277957 4094975 := bstep (se 1 (by rfl) ⟨3071231, by rfl⟩ : syracuseStep 4094975 = 6142463) B6142463
theorem B10919933 : Blo 1277957 10919933 := bstep (se 3 (by rfl) ⟨2047487, by rfl⟩ : syracuseStep 10919933 = 4094975) B4094975
theorem B7279955 : Blo 1277957 7279955 := bstep (se 1 (by rfl) ⟨5459966, by rfl⟩ : syracuseStep 7279955 = 10919933) B10919933
theorem B4853303 : Blo 1277957 4853303 := bstep (se 1 (by rfl) ⟨3639977, by rfl⟩ : syracuseStep 4853303 = 7279955) B7279955
theorem B3235535 : Blo 1277957 3235535 := bstep (se 1 (by rfl) ⟨2426651, by rfl⟩ : syracuseStep 3235535 = 4853303) B4853303
theorem B2157023 : Blo 1277957 2157023 := bstep (se 1 (by rfl) ⟨1617767, by rfl⟩ : syracuseStep 2157023 = 3235535) B3235535
theorem B1438015 : Blo 1277957 1438015 := bstep (se 1 (by rfl) ⟨1078511, by rfl⟩ : syracuseStep 1438015 = 2157023) B2157023
theorem B1917353 : Blo 1277957 1917353 := bstep (se 2 (by rfl) ⟨719007, by rfl⟩ : syracuseStep 1917353 = 1438015) B1438015
theorem B1278235 : Blo 1277957 1278235 := bstep (se 1 (by rfl) ⟨958676, by rfl⟩ : syracuseStep 1278235 = 1917353) B1917353

theorem C0 (j : ℕ) (h1 : 319489 ≤ j) (h2 : j ≤ 319988) : Blo 1277957 (4 * j + 3) := by
  interval_cases j
  · exact B1277959
  · exact B1277963
  · exact B1277967
  · exact B1277971
  · exact B1277975
  · exact B1277979
  · exact B1277983
  · exact B1277987
  · exact B1277991
  · exact B1277995
  · exact B1277999
  · exact B1278003
  · exact B1278007
  · exact B1278011
  · exact B1278015
  · exact B1278019
  · exact B1278023
  · exact B1278027
  · exact B1278031
  · exact B1278035
  · exact B1278039
  · exact B1278043
  · exact B1278047
  · exact B1278051
  · exact B1278055
  · exact B1278059
  · exact B1278063
  · exact B1278067
  · exact B1278071
  · exact B1278075
  · exact B1278079
  · exact B1278083
  · exact B1278087
  · exact B1278091
  · exact B1278095
  · exact B1278099
  · exact B1278103
  · exact B1278107
  · exact B1278111
  · exact B1278115
  · exact B1278119
  · exact B1278123
  · exact B1278127
  · exact B1278131
  · exact B1278135
  · exact B1278139
  · exact B1278143
  · exact B1278147
  · exact B1278151
  · exact B1278155
  · exact B1278159
  · exact B1278163
  · exact B1278167
  · exact B1278171
  · exact B1278175
  · exact B1278179
  · exact B1278183
  · exact B1278187
  · exact B1278191
  · exact B1278195
  · exact B1278199
  · exact B1278203
  · exact B1278207
  · exact B1278211
  · exact B1278215
  · exact B1278219
  · exact B1278223
  · exact B1278227
  · exact B1278231
  · exact B1278235
  · exact B1278239
  · exact B1278243
  · exact B1278247
  · exact B1278251
  · exact B1278255
  · exact B1278259
  · exact B1278263
  · exact B1278267
  · exact B1278271
  · exact B1278275
  · exact B1278279
  · exact B1278283
  · exact B1278287
  · exact B1278291
  · exact B1278295
  · exact B1278299
  · exact B1278303
  · exact B1278307
  · exact B1278311
  · exact B1278315
  · exact B1278319
  · exact B1278323
  · exact B1278327
  · exact B1278331
  · exact B1278335
  · exact B1278339
  · exact B1278343
  · exact B1278347
  · exact B1278351
  · exact B1278355
  · exact B1278359
  · exact B1278363
  · exact B1278367
  · exact B1278371
  · exact B1278375
  · exact B1278379
  · exact B1278383
  · exact B1278387
  · exact B1278391
  · exact B1278395
  · exact B1278399
  · exact B1278403
  · exact B1278407
  · exact B1278411
  · exact B1278415
  · exact B1278419
  · exact B1278423
  · exact B1278427
  · exact B1278431
  · exact B1278435
  · exact B1278439
  · exact B1278443
  · exact B1278447
  · exact B1278451
  · exact B1278455
  · exact B1278459
  · exact B1278463
  · exact B1278467
  · exact B1278471
  · exact B1278475
  · exact B1278479
  · exact B1278483
  · exact B1278487
  · exact B1278491
  · exact B1278495
  · exact B1278499
  · exact B1278503
  · exact B1278507
  · exact B1278511
  · exact B1278515
  · exact B1278519
  · exact B1278523
  · exact B1278527
  · exact B1278531
  · exact B1278535
  · exact B1278539
  · exact B1278543
  · exact B1278547
  · exact B1278551
  · exact B1278555
  · exact B1278559
  · exact B1278563
  · exact B1278567
  · exact B1278571
  · exact B1278575
  · exact B1278579
  · exact B1278583
  · exact B1278587
  · exact B1278591
  · exact B1278595
  · exact B1278599
  · exact B1278603
  · exact B1278607
  · exact B1278611
  · exact B1278615
  · exact B1278619
  · exact B1278623
  · exact B1278627
  · exact B1278631
  · exact B1278635
  · exact B1278639
  · exact B1278643
  · exact B1278647
  · exact B1278651
  · exact B1278655
  · exact B1278659
  · exact B1278663
  · exact B1278667
  · exact B1278671
  · exact B1278675
  · exact B1278679
  · exact B1278683
  · exact B1278687
  · exact B1278691
  · exact B1278695
  · exact B1278699
  · exact B1278703
  · exact B1278707
  · exact B1278711
  · exact B1278715
  · exact B1278719
  · exact B1278723
  · exact B1278727
  · exact B1278731
  · exact B1278735
  · exact B1278739
  · exact B1278743
  · exact B1278747
  · exact B1278751
  · exact B1278755
  · exact B1278759
  · exact B1278763
  · exact B1278767
  · exact B1278771
  · exact B1278775
  · exact B1278779
  · exact B1278783
  · exact B1278787
  · exact B1278791
  · exact B1278795
  · exact B1278799
  · exact B1278803
  · exact B1278807
  · exact B1278811
  · exact B1278815
  · exact B1278819
  · exact B1278823
  · exact B1278827
  · exact B1278831
  · exact B1278835
  · exact B1278839
  · exact B1278843
  · exact B1278847
  · exact B1278851
  · exact B1278855
  · exact B1278859
  · exact B1278863
  · exact B1278867
  · exact B1278871
  · exact B1278875
  · exact B1278879
  · exact B1278883
  · exact B1278887
  · exact B1278891
  · exact B1278895
  · exact B1278899
  · exact B1278903
  · exact B1278907
  · exact B1278911
  · exact B1278915
  · exact B1278919
  · exact B1278923
  · exact B1278927
  · exact B1278931
  · exact B1278935
  · exact B1278939
  · exact B1278943
  · exact B1278947
  · exact B1278951
  · exact B1278955
  · exact B1278959
  · exact B1278963
  · exact B1278967
  · exact B1278971
  · exact B1278975
  · exact B1278979
  · exact B1278983
  · exact B1278987
  · exact B1278991
  · exact B1278995
  · exact B1278999
  · exact B1279003
  · exact B1279007
  · exact B1279011
  · exact B1279015
  · exact B1279019
  · exact B1279023
  · exact B1279027
  · exact B1279031
  · exact B1279035
  · exact B1279039
  · exact B1279043
  · exact B1279047
  · exact B1279051
  · exact B1279055
  · exact B1279059
  · exact B1279063
  · exact B1279067
  · exact B1279071
  · exact B1279075
  · exact B1279079
  · exact B1279083
  · exact B1279087
  · exact B1279091
  · exact B1279095
  · exact B1279099
  · exact B1279103
  · exact B1279107
  · exact B1279111
  · exact B1279115
  · exact B1279119
  · exact B1279123
  · exact B1279127
  · exact B1279131
  · exact B1279135
  · exact B1279139
  · exact B1279143
  · exact B1279147
  · exact B1279151
  · exact B1279155
  · exact B1279159
  · exact B1279163
  · exact B1279167
  · exact B1279171
  · exact B1279175
  · exact B1279179
  · exact B1279183
  · exact B1279187
  · exact B1279191
  · exact B1279195
  · exact B1279199
  · exact B1279203
  · exact B1279207
  · exact B1279211
  · exact B1279215
  · exact B1279219
  · exact B1279223
  · exact B1279227
  · exact B1279231
  · exact B1279235
  · exact B1279239
  · exact B1279243
  · exact B1279247
  · exact B1279251
  · exact B1279255
  · exact B1279259
  · exact B1279263
  · exact B1279267
  · exact B1279271
  · exact B1279275
  · exact B1279279
  · exact B1279283
  · exact B1279287
  · exact B1279291
  · exact B1279295
  · exact B1279299
  · exact B1279303
  · exact B1279307
  · exact B1279311
  · exact B1279315
  · exact B1279319
  · exact B1279323
  · exact B1279327
  · exact B1279331
  · exact B1279335
  · exact B1279339
  · exact B1279343
  · exact B1279347
  · exact B1279351
  · exact B1279355
  · exact B1279359
  · exact B1279363
  · exact B1279367
  · exact B1279371
  · exact B1279375
  · exact B1279379
  · exact B1279383
  · exact B1279387
  · exact B1279391
  · exact B1279395
  · exact B1279399
  · exact B1279403
  · exact B1279407
  · exact B1279411
  · exact B1279415
  · exact B1279419
  · exact B1279423
  · exact B1279427
  · exact B1279431
  · exact B1279435
  · exact B1279439
  · exact B1279443
  · exact B1279447
  · exact B1279451
  · exact B1279455
  · exact B1279459
  · exact B1279463
  · exact B1279467
  · exact B1279471
  · exact B1279475
  · exact B1279479
  · exact B1279483
  · exact B1279487
  · exact B1279491
  · exact B1279495
  · exact B1279499
  · exact B1279503
  · exact B1279507
  · exact B1279511
  · exact B1279515
  · exact B1279519
  · exact B1279523
  · exact B1279527
  · exact B1279531
  · exact B1279535
  · exact B1279539
  · exact B1279543
  · exact B1279547
  · exact B1279551
  · exact B1279555
  · exact B1279559
  · exact B1279563
  · exact B1279567
  · exact B1279571
  · exact B1279575
  · exact B1279579
  · exact B1279583
  · exact B1279587
  · exact B1279591
  · exact B1279595
  · exact B1279599
  · exact B1279603
  · exact B1279607
  · exact B1279611
  · exact B1279615
  · exact B1279619
  · exact B1279623
  · exact B1279627
  · exact B1279631
  · exact B1279635
  · exact B1279639
  · exact B1279643
  · exact B1279647
  · exact B1279651
  · exact B1279655
  · exact B1279659
  · exact B1279663
  · exact B1279667
  · exact B1279671
  · exact B1279675
  · exact B1279679
  · exact B1279683
  · exact B1279687
  · exact B1279691
  · exact B1279695
  · exact B1279699
  · exact B1279703
  · exact B1279707
  · exact B1279711
  · exact B1279715
  · exact B1279719
  · exact B1279723
  · exact B1279727
  · exact B1279731
  · exact B1279735
  · exact B1279739
  · exact B1279743
  · exact B1279747
  · exact B1279751
  · exact B1279755
  · exact B1279759
  · exact B1279763
  · exact B1279767
  · exact B1279771
  · exact B1279775
  · exact B1279779
  · exact B1279783
  · exact B1279787
  · exact B1279791
  · exact B1279795
  · exact B1279799
  · exact B1279803
  · exact B1279807
  · exact B1279811
  · exact B1279815
  · exact B1279819
  · exact B1279823
  · exact B1279827
  · exact B1279831
  · exact B1279835
  · exact B1279839
  · exact B1279843
  · exact B1279847
  · exact B1279851
  · exact B1279855
  · exact B1279859
  · exact B1279863
  · exact B1279867
  · exact B1279871
  · exact B1279875
  · exact B1279879
  · exact B1279883
  · exact B1279887
  · exact B1279891
  · exact B1279895
  · exact B1279899
  · exact B1279903
  · exact B1279907
  · exact B1279911
  · exact B1279915
  · exact B1279919
  · exact B1279923
  · exact B1279927
  · exact B1279931
  · exact B1279935
  · exact B1279939
  · exact B1279943
  · exact B1279947
  · exact B1279951
  · exact B1279955

theorem solution (m : ℕ) (hlo : 1277957 ≤ m) (hhi : m ≤ 1279957) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 319489 ≤ j := by omega
    have hj2 : j ≤ 319988 := by omega
    have hb : Blo 1277957 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
