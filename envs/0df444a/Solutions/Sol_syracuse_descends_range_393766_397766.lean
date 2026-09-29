-- Prove2me | solution 1 for syracuse_descends_range_393766_397766
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:46.760607+00:00
-- url     : https://prove2.me/submissions/bd74de2a-cd33-4f9c-a2a0-26b9b6704556

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


theorem B753725 : Blo 393766 753725 := bbase (se 3 (by rfl) ⟨141323, by rfl⟩ : syracuseStep 753725 = 282647) (by norm_num)
theorem B1998917 : Blo 393766 1998917 := bbase (se 4 (by rfl) ⟨187398, by rfl⟩ : syracuseStep 1998917 = 374797) (by norm_num)
theorem B753877 : Blo 393766 753877 := bbase (se 7 (by rfl) ⟨8834, by rfl⟩ : syracuseStep 753877 = 17669) (by norm_num)
theorem B2162933 : Blo 393766 2162933 := bbase (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) (by norm_num)
theorem B688493 : Blo 393766 688493 := bbase (se 3 (by rfl) ⟨129092, by rfl⟩ : syracuseStep 688493 = 258185) (by norm_num)
theorem B754181 : Blo 393766 754181 := bbase (se 4 (by rfl) ⟨70704, by rfl⟩ : syracuseStep 754181 = 141409) (by norm_num)
theorem B1901141 : Blo 393766 1901141 := bbase (se 8 (by rfl) ⟨11139, by rfl⟩ : syracuseStep 1901141 = 22279) (by norm_num)
theorem B1508165 : Blo 393766 1508165 := bbase (se 4 (by rfl) ⟨141390, by rfl⟩ : syracuseStep 1508165 = 282781) (by norm_num)
theorem B590669 : Blo 393766 590669 := bbase (se 3 (by rfl) ⟨110750, by rfl⟩ : syracuseStep 590669 = 221501) (by norm_num)
theorem B590693 : Blo 393766 590693 := bbase (se 4 (by rfl) ⟨55377, by rfl⟩ : syracuseStep 590693 = 110755) (by norm_num)
theorem B590717 : Blo 393766 590717 := bbase (se 3 (by rfl) ⟨110759, by rfl⟩ : syracuseStep 590717 = 221519) (by norm_num)
theorem B590741 : Blo 393766 590741 := bbase (se 6 (by rfl) ⟨13845, by rfl⟩ : syracuseStep 590741 = 27691) (by norm_num)
theorem B951205 : Blo 393766 951205 := bbase (se 4 (by rfl) ⟨89175, by rfl⟩ : syracuseStep 951205 = 178351) (by norm_num)
theorem B590765 : Blo 393766 590765 := bbase (se 3 (by rfl) ⟨110768, by rfl⟩ : syracuseStep 590765 = 221537) (by norm_num)
theorem B852925 : Blo 393766 852925 := bbase (se 3 (by rfl) ⟨159923, by rfl⟩ : syracuseStep 852925 = 319847) (by norm_num)
theorem B590789 : Blo 393766 590789 := bbase (se 4 (by rfl) ⟨55386, by rfl⟩ : syracuseStep 590789 = 110773) (by norm_num)
theorem B590813 : Blo 393766 590813 := bbase (se 3 (by rfl) ⟨110777, by rfl⟩ : syracuseStep 590813 = 221555) (by norm_num)
theorem B590837 : Blo 393766 590837 := bbase (se 5 (by rfl) ⟨27695, by rfl⟩ : syracuseStep 590837 = 55391) (by norm_num)
theorem B590861 : Blo 393766 590861 := bbase (se 3 (by rfl) ⟨110786, by rfl⟩ : syracuseStep 590861 = 221573) (by norm_num)
theorem B590885 : Blo 393766 590885 := bbase (se 4 (by rfl) ⟨55395, by rfl⟩ : syracuseStep 590885 = 110791) (by norm_num)
theorem B3376181 : Blo 393766 3376181 := bbase (se 5 (by rfl) ⟨158258, by rfl⟩ : syracuseStep 3376181 = 316517) (by norm_num)
theorem B590909 : Blo 393766 590909 := bbase (se 3 (by rfl) ⟨110795, by rfl⟩ : syracuseStep 590909 = 221591) (by norm_num)
theorem B590933 : Blo 393766 590933 := bbase (se 8 (by rfl) ⟨3462, by rfl⟩ : syracuseStep 590933 = 6925) (by norm_num)
theorem B1508453 : Blo 393766 1508453 := bbase (se 4 (by rfl) ⟨141417, by rfl⟩ : syracuseStep 1508453 = 282835) (by norm_num)
theorem B590957 : Blo 393766 590957 := bbase (se 3 (by rfl) ⟨110804, by rfl⟩ : syracuseStep 590957 = 221609) (by norm_num)
theorem B590981 : Blo 393766 590981 := bbase (se 4 (by rfl) ⟨55404, by rfl⟩ : syracuseStep 590981 = 110809) (by norm_num)
theorem B591005 : Blo 393766 591005 := bbase (se 3 (by rfl) ⟨110813, by rfl⟩ : syracuseStep 591005 = 221627) (by norm_num)
theorem B591029 : Blo 393766 591029 := bbase (se 5 (by rfl) ⟨27704, by rfl⟩ : syracuseStep 591029 = 55409) (by norm_num)
theorem B722117 : Blo 393766 722117 := bbase (se 4 (by rfl) ⟨67698, by rfl⟩ : syracuseStep 722117 = 135397) (by norm_num)
theorem B591053 : Blo 393766 591053 := bbase (se 3 (by rfl) ⟨110822, by rfl⟩ : syracuseStep 591053 = 221645) (by norm_num)
theorem B591077 : Blo 393766 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B754933 : Blo 393766 754933 := bbase (se 5 (by rfl) ⟨35387, by rfl⟩ : syracuseStep 754933 = 70775) (by norm_num)
theorem B886013 : Blo 393766 886013 := bbase (se 3 (by rfl) ⟨166127, by rfl⟩ : syracuseStep 886013 = 332255) (by norm_num)
theorem B591101 : Blo 393766 591101 := bbase (se 3 (by rfl) ⟨110831, by rfl⟩ : syracuseStep 591101 = 221663) (by norm_num)
theorem B591125 : Blo 393766 591125 := bbase (se 6 (by rfl) ⟨13854, by rfl⟩ : syracuseStep 591125 = 27709) (by norm_num)
theorem B1803541 : Blo 393766 1803541 := bbase (se 6 (by rfl) ⟨42270, by rfl⟩ : syracuseStep 1803541 = 84541) (by norm_num)
theorem B591149 : Blo 393766 591149 := bbase (se 3 (by rfl) ⟨110840, by rfl⟩ : syracuseStep 591149 = 221681) (by norm_num)
theorem B886085 : Blo 393766 886085 := bbase (se 4 (by rfl) ⟨83070, by rfl⟩ : syracuseStep 886085 = 166141) (by norm_num)
theorem B591173 : Blo 393766 591173 := bbase (se 4 (by rfl) ⟨55422, by rfl⟩ : syracuseStep 591173 = 110845) (by norm_num)
theorem B2000213 : Blo 393766 2000213 := bbase (se 12 (by rfl) ⟨732, by rfl⟩ : syracuseStep 2000213 = 1465) (by norm_num)
theorem B591197 : Blo 393766 591197 := bbase (se 3 (by rfl) ⟨110849, by rfl⟩ : syracuseStep 591197 = 221699) (by norm_num)
theorem B591221 : Blo 393766 591221 := bbase (se 5 (by rfl) ⟨27713, by rfl⟩ : syracuseStep 591221 = 55427) (by norm_num)
theorem B755077 : Blo 393766 755077 := bbase (se 4 (by rfl) ⟨70788, by rfl⟩ : syracuseStep 755077 = 141577) (by norm_num)
theorem B886157 : Blo 393766 886157 := bbase (se 3 (by rfl) ⟨166154, by rfl⟩ : syracuseStep 886157 = 332309) (by norm_num)
theorem B591245 : Blo 393766 591245 := bbase (se 3 (by rfl) ⟨110858, by rfl⟩ : syracuseStep 591245 = 221717) (by norm_num)
theorem B591269 : Blo 393766 591269 := bbase (se 4 (by rfl) ⟨55431, by rfl⟩ : syracuseStep 591269 = 110863) (by norm_num)
theorem B951725 : Blo 393766 951725 := bbase (se 3 (by rfl) ⟨178448, by rfl⟩ : syracuseStep 951725 = 356897) (by norm_num)
theorem B591293 : Blo 393766 591293 := bbase (se 3 (by rfl) ⟨110867, by rfl⟩ : syracuseStep 591293 = 221735) (by norm_num)
theorem B886229 : Blo 393766 886229 := bbase (se 7 (by rfl) ⟨10385, by rfl⟩ : syracuseStep 886229 = 20771) (by norm_num)
theorem B591317 : Blo 393766 591317 := bbase (se 7 (by rfl) ⟨6929, by rfl⟩ : syracuseStep 591317 = 13859) (by norm_num)
theorem B1705445 : Blo 393766 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B591341 : Blo 393766 591341 := bbase (se 3 (by rfl) ⟨110876, by rfl⟩ : syracuseStep 591341 = 221753) (by norm_num)
theorem B1934837 : Blo 393766 1934837 := bbase (se 5 (by rfl) ⟨90695, by rfl⟩ : syracuseStep 1934837 = 181391) (by norm_num)
theorem B591365 : Blo 393766 591365 := bbase (se 4 (by rfl) ⟨55440, by rfl⟩ : syracuseStep 591365 = 110881) (by norm_num)
theorem B951821 : Blo 393766 951821 := bbase (se 3 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 951821 = 356933) (by norm_num)
theorem B886301 : Blo 393766 886301 := bbase (se 3 (by rfl) ⟨166181, by rfl⟩ : syracuseStep 886301 = 332363) (by norm_num)
theorem B591389 : Blo 393766 591389 := bbase (se 3 (by rfl) ⟨110885, by rfl⟩ : syracuseStep 591389 = 221771) (by norm_num)
theorem B591413 : Blo 393766 591413 := bbase (se 5 (by rfl) ⟨27722, by rfl⟩ : syracuseStep 591413 = 55445) (by norm_num)
theorem B591437 : Blo 393766 591437 := bbase (se 3 (by rfl) ⟨110894, by rfl⟩ : syracuseStep 591437 = 221789) (by norm_num)
theorem B886373 : Blo 393766 886373 := bbase (se 4 (by rfl) ⟨83097, by rfl⟩ : syracuseStep 886373 = 166195) (by norm_num)
theorem B591461 : Blo 393766 591461 := bbase (se 4 (by rfl) ⟨55449, by rfl⟩ : syracuseStep 591461 = 110899) (by norm_num)
theorem B591485 : Blo 393766 591485 := bbase (se 3 (by rfl) ⟨110903, by rfl⟩ : syracuseStep 591485 = 221807) (by norm_num)
theorem B591509 : Blo 393766 591509 := bbase (se 6 (by rfl) ⟨13863, by rfl⟩ : syracuseStep 591509 = 27727) (by norm_num)
theorem B886445 : Blo 393766 886445 := bbase (se 3 (by rfl) ⟨166208, by rfl⟩ : syracuseStep 886445 = 332417) (by norm_num)
theorem B591533 : Blo 393766 591533 := bbase (se 3 (by rfl) ⟨110912, by rfl⟩ : syracuseStep 591533 = 221825) (by norm_num)
theorem B591557 : Blo 393766 591557 := bbase (se 4 (by rfl) ⟨55458, by rfl⟩ : syracuseStep 591557 = 110917) (by norm_num)
theorem B591581 : Blo 393766 591581 := bbase (se 3 (by rfl) ⟨110921, by rfl⟩ : syracuseStep 591581 = 221843) (by norm_num)
theorem B886517 : Blo 393766 886517 := bbase (se 5 (by rfl) ⟨41555, by rfl⟩ : syracuseStep 886517 = 83111) (by norm_num)
theorem B591605 : Blo 393766 591605 := bbase (se 5 (by rfl) ⟨27731, by rfl⟩ : syracuseStep 591605 = 55463) (by norm_num)
theorem B591629 : Blo 393766 591629 := bbase (se 3 (by rfl) ⟨110930, by rfl⟩ : syracuseStep 591629 = 221861) (by norm_num)
theorem B591653 : Blo 393766 591653 := bbase (se 4 (by rfl) ⟨55467, by rfl⟩ : syracuseStep 591653 = 110935) (by norm_num)
theorem B886589 : Blo 393766 886589 := bbase (se 3 (by rfl) ⟨166235, by rfl⟩ : syracuseStep 886589 = 332471) (by norm_num)
theorem B591677 : Blo 393766 591677 := bbase (se 3 (by rfl) ⟨110939, by rfl⟩ : syracuseStep 591677 = 221879) (by norm_num)
theorem B591701 : Blo 393766 591701 := bbase (se 9 (by rfl) ⟨1733, by rfl⟩ : syracuseStep 591701 = 3467) (by norm_num)
theorem B591725 : Blo 393766 591725 := bbase (se 3 (by rfl) ⟨110948, by rfl⟩ : syracuseStep 591725 = 221897) (by norm_num)
theorem B1083253 : Blo 393766 1083253 := bbase (se 5 (by rfl) ⟨50777, by rfl⟩ : syracuseStep 1083253 = 101555) (by norm_num)
theorem B886661 : Blo 393766 886661 := bbase (se 4 (by rfl) ⟨83124, by rfl⟩ : syracuseStep 886661 = 166249) (by norm_num)
theorem B591749 : Blo 393766 591749 := bbase (se 4 (by rfl) ⟨55476, by rfl⟩ : syracuseStep 591749 = 110953) (by norm_num)
theorem B1902485 : Blo 393766 1902485 := bbase (se 6 (by rfl) ⟨44589, by rfl⟩ : syracuseStep 1902485 = 89179) (by norm_num)
theorem B591773 : Blo 393766 591773 := bbase (se 3 (by rfl) ⟨110957, by rfl⟩ : syracuseStep 591773 = 221915) (by norm_num)
theorem B591797 : Blo 393766 591797 := bbase (se 5 (by rfl) ⟨27740, by rfl⟩ : syracuseStep 591797 = 55481) (by norm_num)
theorem B2754485 : Blo 393766 2754485 := bbase (se 5 (by rfl) ⟨129116, by rfl⟩ : syracuseStep 2754485 = 258233) (by norm_num)
theorem B886733 : Blo 393766 886733 := bbase (se 3 (by rfl) ⟨166262, by rfl⟩ : syracuseStep 886733 = 332525) (by norm_num)
theorem B591821 : Blo 393766 591821 := bbase (se 3 (by rfl) ⟨110966, by rfl⟩ : syracuseStep 591821 = 221933) (by norm_num)
theorem B591845 : Blo 393766 591845 := bbase (se 4 (by rfl) ⟨55485, by rfl⟩ : syracuseStep 591845 = 110971) (by norm_num)
theorem B3803125 : Blo 393766 3803125 := bbase (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) (by norm_num)
theorem B591869 : Blo 393766 591869 := bbase (se 3 (by rfl) ⟨110975, by rfl⟩ : syracuseStep 591869 = 221951) (by norm_num)
theorem B886805 : Blo 393766 886805 := bbase (se 6 (by rfl) ⟨20784, by rfl⟩ : syracuseStep 886805 = 41569) (by norm_num)
theorem B4261909 : Blo 393766 4261909 := bbase (se 6 (by rfl) ⟨99888, by rfl⟩ : syracuseStep 4261909 = 199777) (by norm_num)
theorem B591893 : Blo 393766 591893 := bbase (se 6 (by rfl) ⟨13872, by rfl⟩ : syracuseStep 591893 = 27745) (by norm_num)
theorem B591917 : Blo 393766 591917 := bbase (se 3 (by rfl) ⟨110984, by rfl⟩ : syracuseStep 591917 = 221969) (by norm_num)
theorem B591941 : Blo 393766 591941 := bbase (se 4 (by rfl) ⟨55494, by rfl⟩ : syracuseStep 591941 = 110989) (by norm_num)
theorem B886877 : Blo 393766 886877 := bbase (se 3 (by rfl) ⟨166289, by rfl⟩ : syracuseStep 886877 = 332579) (by norm_num)
theorem B591965 : Blo 393766 591965 := bbase (se 3 (by rfl) ⟨110993, by rfl⟩ : syracuseStep 591965 = 221987) (by norm_num)
theorem B1935461 : Blo 393766 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B591989 : Blo 393766 591989 := bbase (se 5 (by rfl) ⟨27749, by rfl⟩ : syracuseStep 591989 = 55499) (by norm_num)
theorem B592013 : Blo 393766 592013 := bbase (se 3 (by rfl) ⟨111002, by rfl⟩ : syracuseStep 592013 = 222005) (by norm_num)
theorem B886949 : Blo 393766 886949 := bbase (se 4 (by rfl) ⟨83151, by rfl⟩ : syracuseStep 886949 = 166303) (by norm_num)
theorem B592037 : Blo 393766 592037 := bbase (se 4 (by rfl) ⟨55503, by rfl⟩ : syracuseStep 592037 = 111007) (by norm_num)
theorem B592061 : Blo 393766 592061 := bbase (se 3 (by rfl) ⟨111011, by rfl⟩ : syracuseStep 592061 = 222023) (by norm_num)
theorem B592085 : Blo 393766 592085 := bbase (se 7 (by rfl) ⟨6938, by rfl⟩ : syracuseStep 592085 = 13877) (by norm_num)
theorem B887021 : Blo 393766 887021 := bbase (se 3 (by rfl) ⟨166316, by rfl⟩ : syracuseStep 887021 = 332633) (by norm_num)
theorem B592109 : Blo 393766 592109 := bbase (se 3 (by rfl) ⟨111020, by rfl⟩ : syracuseStep 592109 = 222041) (by norm_num)
theorem B592133 : Blo 393766 592133 := bbase (se 4 (by rfl) ⟨55512, by rfl⟩ : syracuseStep 592133 = 111025) (by norm_num)
theorem B1509637 : Blo 393766 1509637 := bbase (se 4 (by rfl) ⟨141528, by rfl⟩ : syracuseStep 1509637 = 283057) (by norm_num)
theorem B592157 : Blo 393766 592157 := bbase (se 3 (by rfl) ⟨111029, by rfl⟩ : syracuseStep 592157 = 222059) (by norm_num)
theorem B887093 : Blo 393766 887093 := bbase (se 5 (by rfl) ⟨41582, by rfl⟩ : syracuseStep 887093 = 83165) (by norm_num)
theorem B592181 : Blo 393766 592181 := bbase (se 5 (by rfl) ⟨27758, by rfl⟩ : syracuseStep 592181 = 55517) (by norm_num)
theorem B1706309 : Blo 393766 1706309 := bbase (se 4 (by rfl) ⟨159966, by rfl⟩ : syracuseStep 1706309 = 319933) (by norm_num)
theorem B592205 : Blo 393766 592205 := bbase (se 3 (by rfl) ⟨111038, by rfl⟩ : syracuseStep 592205 = 222077) (by norm_num)
theorem B592229 : Blo 393766 592229 := bbase (se 4 (by rfl) ⟨55521, by rfl⟩ : syracuseStep 592229 = 111043) (by norm_num)
theorem B887165 : Blo 393766 887165 := bbase (se 3 (by rfl) ⟨166343, by rfl⟩ : syracuseStep 887165 = 332687) (by norm_num)
theorem B592253 : Blo 393766 592253 := bbase (se 3 (by rfl) ⟨111047, by rfl⟩ : syracuseStep 592253 = 222095) (by norm_num)
theorem B592277 : Blo 393766 592277 := bbase (se 6 (by rfl) ⟨13881, by rfl⟩ : syracuseStep 592277 = 27763) (by norm_num)
theorem B592301 : Blo 393766 592301 := bbase (se 3 (by rfl) ⟨111056, by rfl⟩ : syracuseStep 592301 = 222113) (by norm_num)
theorem B854453 : Blo 393766 854453 := bbase (se 5 (by rfl) ⟨40052, by rfl⟩ : syracuseStep 854453 = 80105) (by norm_num)
theorem B887237 : Blo 393766 887237 := bbase (se 4 (by rfl) ⟨83178, by rfl⟩ : syracuseStep 887237 = 166357) (by norm_num)
theorem B592325 : Blo 393766 592325 := bbase (se 4 (by rfl) ⟨55530, by rfl⟩ : syracuseStep 592325 = 111061) (by norm_num)
theorem B592349 : Blo 393766 592349 := bbase (se 3 (by rfl) ⟨111065, by rfl⟩ : syracuseStep 592349 = 222131) (by norm_num)
theorem B592373 : Blo 393766 592373 := bbase (se 5 (by rfl) ⟨27767, by rfl⟩ : syracuseStep 592373 = 55535) (by norm_num)
theorem B887309 : Blo 393766 887309 := bbase (se 3 (by rfl) ⟨166370, by rfl⟩ : syracuseStep 887309 = 332741) (by norm_num)
theorem B592397 : Blo 393766 592397 := bbase (se 3 (by rfl) ⟨111074, by rfl⟩ : syracuseStep 592397 = 222149) (by norm_num)
theorem B592421 : Blo 393766 592421 := bbase (se 4 (by rfl) ⟨55539, by rfl⟩ : syracuseStep 592421 = 111079) (by norm_num)
theorem B1509941 : Blo 393766 1509941 := bbase (se 5 (by rfl) ⟨70778, by rfl⟩ : syracuseStep 1509941 = 141557) (by norm_num)
theorem B592445 : Blo 393766 592445 := bbase (se 3 (by rfl) ⟨111083, by rfl⟩ : syracuseStep 592445 = 222167) (by norm_num)
theorem B887381 : Blo 393766 887381 := bbase (se 8 (by rfl) ⟨5199, by rfl⟩ : syracuseStep 887381 = 10399) (by norm_num)
theorem B592469 : Blo 393766 592469 := bbase (se 8 (by rfl) ⟨3471, by rfl⟩ : syracuseStep 592469 = 6943) (by norm_num)
theorem B2001509 : Blo 393766 2001509 := bbase (se 4 (by rfl) ⟨187641, by rfl⟩ : syracuseStep 2001509 = 375283) (by norm_num)
theorem B592493 : Blo 393766 592493 := bbase (se 3 (by rfl) ⟨111092, by rfl⟩ : syracuseStep 592493 = 222185) (by norm_num)
theorem B592517 : Blo 393766 592517 := bbase (se 4 (by rfl) ⟨55548, by rfl⟩ : syracuseStep 592517 = 111097) (by norm_num)
theorem B887453 : Blo 393766 887453 := bbase (se 3 (by rfl) ⟨166397, by rfl⟩ : syracuseStep 887453 = 332795) (by norm_num)
theorem B592541 : Blo 393766 592541 := bbase (se 3 (by rfl) ⟨111101, by rfl⟩ : syracuseStep 592541 = 222203) (by norm_num)
theorem B592565 : Blo 393766 592565 := bbase (se 5 (by rfl) ⟨27776, by rfl⟩ : syracuseStep 592565 = 55553) (by norm_num)
theorem B592589 : Blo 393766 592589 := bbase (se 3 (by rfl) ⟨111110, by rfl⟩ : syracuseStep 592589 = 222221) (by norm_num)
theorem B887525 : Blo 393766 887525 := bbase (se 4 (by rfl) ⟨83205, by rfl⟩ : syracuseStep 887525 = 166411) (by norm_num)
theorem B592613 : Blo 393766 592613 := bbase (se 4 (by rfl) ⟨55557, by rfl⟩ : syracuseStep 592613 = 111115) (by norm_num)
theorem B592637 : Blo 393766 592637 := bbase (se 3 (by rfl) ⟨111119, by rfl⟩ : syracuseStep 592637 = 222239) (by norm_num)
theorem B592661 : Blo 393766 592661 := bbase (se 6 (by rfl) ⟨13890, by rfl⟩ : syracuseStep 592661 = 27781) (by norm_num)
theorem B887597 : Blo 393766 887597 := bbase (se 3 (by rfl) ⟨166424, by rfl⟩ : syracuseStep 887597 = 332849) (by norm_num)
theorem B592685 : Blo 393766 592685 := bbase (se 3 (by rfl) ⟨111128, by rfl⟩ : syracuseStep 592685 = 222257) (by norm_num)
theorem B592709 : Blo 393766 592709 := bbase (se 4 (by rfl) ⟨55566, by rfl⟩ : syracuseStep 592709 = 111133) (by norm_num)
theorem B953165 : Blo 393766 953165 := bbase (se 3 (by rfl) ⟨178718, by rfl⟩ : syracuseStep 953165 = 357437) (by norm_num)
theorem B592733 : Blo 393766 592733 := bbase (se 3 (by rfl) ⟨111137, by rfl⟩ : syracuseStep 592733 = 222275) (by norm_num)
theorem B887669 : Blo 393766 887669 := bbase (se 5 (by rfl) ⟨41609, by rfl⟩ : syracuseStep 887669 = 83219) (by norm_num)
theorem B592757 : Blo 393766 592757 := bbase (se 5 (by rfl) ⟨27785, by rfl⟩ : syracuseStep 592757 = 55571) (by norm_num)
theorem B592781 : Blo 393766 592781 := bbase (se 3 (by rfl) ⟨111146, by rfl⟩ : syracuseStep 592781 = 222293) (by norm_num)
theorem B592805 : Blo 393766 592805 := bbase (se 4 (by rfl) ⟨55575, by rfl⟩ : syracuseStep 592805 = 111151) (by norm_num)
theorem B887741 : Blo 393766 887741 := bbase (se 3 (by rfl) ⟨166451, by rfl⟩ : syracuseStep 887741 = 332903) (by norm_num)
theorem B592829 : Blo 393766 592829 := bbase (se 3 (by rfl) ⟨111155, by rfl⟩ : syracuseStep 592829 = 222311) (by norm_num)
theorem B592853 : Blo 393766 592853 := bbase (se 7 (by rfl) ⟨6947, by rfl⟩ : syracuseStep 592853 = 13895) (by norm_num)
theorem B592877 : Blo 393766 592877 := bbase (se 3 (by rfl) ⟨111164, by rfl⟩ : syracuseStep 592877 = 222329) (by norm_num)
theorem B887813 : Blo 393766 887813 := bbase (se 4 (by rfl) ⟨83232, by rfl⟩ : syracuseStep 887813 = 166465) (by norm_num)
theorem B592901 : Blo 393766 592901 := bbase (se 4 (by rfl) ⟨55584, by rfl⟩ : syracuseStep 592901 = 111169) (by norm_num)
theorem B592925 : Blo 393766 592925 := bbase (se 3 (by rfl) ⟨111173, by rfl⟩ : syracuseStep 592925 = 222347) (by norm_num)
theorem B592949 : Blo 393766 592949 := bbase (se 5 (by rfl) ⟨27794, by rfl⟩ : syracuseStep 592949 = 55589) (by norm_num)
theorem B887885 : Blo 393766 887885 := bbase (se 3 (by rfl) ⟨166478, by rfl⟩ : syracuseStep 887885 = 332957) (by norm_num)
theorem B592973 : Blo 393766 592973 := bbase (se 3 (by rfl) ⟨111182, by rfl⟩ : syracuseStep 592973 = 222365) (by norm_num)
theorem B592997 : Blo 393766 592997 := bbase (se 4 (by rfl) ⟨55593, by rfl⟩ : syracuseStep 592997 = 111187) (by norm_num)
theorem B593021 : Blo 393766 593021 := bbase (se 3 (by rfl) ⟨111191, by rfl⟩ : syracuseStep 593021 = 222383) (by norm_num)
theorem B887957 : Blo 393766 887957 := bbase (se 6 (by rfl) ⟨20811, by rfl⟩ : syracuseStep 887957 = 41623) (by norm_num)
theorem B593045 : Blo 393766 593045 := bbase (se 6 (by rfl) ⟨13899, by rfl⟩ : syracuseStep 593045 = 27799) (by norm_num)
theorem B593069 : Blo 393766 593069 := bbase (se 3 (by rfl) ⟨111200, by rfl⟩ : syracuseStep 593069 = 222401) (by norm_num)
theorem B593093 : Blo 393766 593093 := bbase (se 4 (by rfl) ⟨55602, by rfl⟩ : syracuseStep 593093 = 111205) (by norm_num)
theorem B888029 : Blo 393766 888029 := bbase (se 3 (by rfl) ⟨166505, by rfl⟩ : syracuseStep 888029 = 333011) (by norm_num)
theorem B593117 : Blo 393766 593117 := bbase (se 3 (by rfl) ⟨111209, by rfl⟩ : syracuseStep 593117 = 222419) (by norm_num)
theorem B593141 : Blo 393766 593141 := bbase (se 5 (by rfl) ⟨27803, by rfl⟩ : syracuseStep 593141 = 55607) (by norm_num)
theorem B593165 : Blo 393766 593165 := bbase (se 3 (by rfl) ⟨111218, by rfl⟩ : syracuseStep 593165 = 222437) (by norm_num)
theorem B888101 : Blo 393766 888101 := bbase (se 4 (by rfl) ⟨83259, by rfl⟩ : syracuseStep 888101 = 166519) (by norm_num)
theorem B593189 : Blo 393766 593189 := bbase (se 4 (by rfl) ⟨55611, by rfl⟩ : syracuseStep 593189 = 111223) (by norm_num)
theorem B593213 : Blo 393766 593213 := bbase (se 3 (by rfl) ⟨111227, by rfl⟩ : syracuseStep 593213 = 222455) (by norm_num)
theorem B593237 : Blo 393766 593237 := bbase (se 11 (by rfl) ⟨434, by rfl⟩ : syracuseStep 593237 = 869) (by norm_num)
theorem B888173 : Blo 393766 888173 := bbase (se 3 (by rfl) ⟨166532, by rfl⟩ : syracuseStep 888173 = 333065) (by norm_num)
theorem B593261 : Blo 393766 593261 := bbase (se 3 (by rfl) ⟨111236, by rfl⟩ : syracuseStep 593261 = 222473) (by norm_num)
theorem B593285 : Blo 393766 593285 := bbase (se 4 (by rfl) ⟨55620, by rfl⟩ : syracuseStep 593285 = 111241) (by norm_num)
theorem B593309 : Blo 393766 593309 := bbase (se 3 (by rfl) ⟨111245, by rfl⟩ : syracuseStep 593309 = 222491) (by norm_num)
theorem B888245 : Blo 393766 888245 := bbase (se 5 (by rfl) ⟨41636, by rfl⟩ : syracuseStep 888245 = 83273) (by norm_num)
theorem B593333 : Blo 393766 593333 := bbase (se 5 (by rfl) ⟨27812, by rfl⟩ : syracuseStep 593333 = 55625) (by norm_num)
theorem B593357 : Blo 393766 593357 := bbase (se 3 (by rfl) ⟨111254, by rfl⟩ : syracuseStep 593357 = 222509) (by norm_num)
theorem B593381 : Blo 393766 593381 := bbase (se 4 (by rfl) ⟨55629, by rfl⟩ : syracuseStep 593381 = 111259) (by norm_num)
theorem B888317 : Blo 393766 888317 := bbase (se 3 (by rfl) ⟨166559, by rfl⟩ : syracuseStep 888317 = 333119) (by norm_num)
theorem B593405 : Blo 393766 593405 := bbase (se 3 (by rfl) ⟨111263, by rfl⟩ : syracuseStep 593405 = 222527) (by norm_num)
theorem B593429 : Blo 393766 593429 := bbase (se 6 (by rfl) ⟨13908, by rfl⟩ : syracuseStep 593429 = 27817) (by norm_num)
theorem B593453 : Blo 393766 593453 := bbase (se 3 (by rfl) ⟨111272, by rfl⟩ : syracuseStep 593453 = 222545) (by norm_num)
theorem B888389 : Blo 393766 888389 := bbase (se 4 (by rfl) ⟨83286, by rfl⟩ : syracuseStep 888389 = 166573) (by norm_num)
theorem B593477 : Blo 393766 593477 := bbase (se 4 (by rfl) ⟨55638, by rfl⟩ : syracuseStep 593477 = 111277) (by norm_num)
theorem B2526805 : Blo 393766 2526805 := bbase (se 8 (by rfl) ⟨14805, by rfl⟩ : syracuseStep 2526805 = 29611) (by norm_num)
theorem B593501 : Blo 393766 593501 := bbase (se 3 (by rfl) ⟨111281, by rfl⟩ : syracuseStep 593501 = 222563) (by norm_num)
theorem B593525 : Blo 393766 593525 := bbase (se 5 (by rfl) ⟨27821, by rfl⟩ : syracuseStep 593525 = 55643) (by norm_num)
theorem B888461 : Blo 393766 888461 := bbase (se 3 (by rfl) ⟨166586, by rfl⟩ : syracuseStep 888461 = 333173) (by norm_num)
theorem B593549 : Blo 393766 593549 := bbase (se 3 (by rfl) ⟨111290, by rfl⟩ : syracuseStep 593549 = 222581) (by norm_num)
theorem B593573 : Blo 393766 593573 := bbase (se 4 (by rfl) ⟨55647, by rfl⟩ : syracuseStep 593573 = 111295) (by norm_num)
theorem B593597 : Blo 393766 593597 := bbase (se 3 (by rfl) ⟨111299, by rfl⟩ : syracuseStep 593597 = 222599) (by norm_num)
theorem B888533 : Blo 393766 888533 := bbase (se 7 (by rfl) ⟨10412, by rfl⟩ : syracuseStep 888533 = 20825) (by norm_num)
theorem B593621 : Blo 393766 593621 := bbase (se 7 (by rfl) ⟨6956, by rfl⟩ : syracuseStep 593621 = 13913) (by norm_num)
theorem B593645 : Blo 393766 593645 := bbase (se 3 (by rfl) ⟨111308, by rfl⟩ : syracuseStep 593645 = 222617) (by norm_num)
theorem B593669 : Blo 393766 593669 := bbase (se 4 (by rfl) ⟨55656, by rfl⟩ : syracuseStep 593669 = 111313) (by norm_num)
theorem B888605 : Blo 393766 888605 := bbase (se 3 (by rfl) ⟨166613, by rfl⟩ : syracuseStep 888605 = 333227) (by norm_num)
theorem B593693 : Blo 393766 593693 := bbase (se 3 (by rfl) ⟨111317, by rfl⟩ : syracuseStep 593693 = 222635) (by norm_num)
theorem B593717 : Blo 393766 593717 := bbase (se 5 (by rfl) ⟨27830, by rfl⟩ : syracuseStep 593717 = 55661) (by norm_num)
theorem B1609541 : Blo 393766 1609541 := bbase (se 4 (by rfl) ⟨150894, by rfl⟩ : syracuseStep 1609541 = 301789) (by norm_num)
theorem B593741 : Blo 393766 593741 := bbase (se 3 (by rfl) ⟨111326, by rfl⟩ : syracuseStep 593741 = 222653) (by norm_num)
theorem B888677 : Blo 393766 888677 := bbase (se 4 (by rfl) ⟨83313, by rfl⟩ : syracuseStep 888677 = 166627) (by norm_num)
theorem B593765 : Blo 393766 593765 := bbase (se 4 (by rfl) ⟨55665, by rfl⟩ : syracuseStep 593765 = 111331) (by norm_num)
theorem B1904485 : Blo 393766 1904485 := bbase (se 4 (by rfl) ⟨178545, by rfl⟩ : syracuseStep 1904485 = 357091) (by norm_num)
theorem B2002805 : Blo 393766 2002805 := bbase (se 5 (by rfl) ⟨93881, by rfl⟩ : syracuseStep 2002805 = 187763) (by norm_num)
theorem B593789 : Blo 393766 593789 := bbase (se 3 (by rfl) ⟨111335, by rfl⟩ : syracuseStep 593789 = 222671) (by norm_num)
theorem B593813 : Blo 393766 593813 := bbase (se 6 (by rfl) ⟨13917, by rfl⟩ : syracuseStep 593813 = 27835) (by norm_num)
theorem B888749 : Blo 393766 888749 := bbase (se 3 (by rfl) ⟨166640, by rfl⟩ : syracuseStep 888749 = 333281) (by norm_num)
theorem B593837 : Blo 393766 593837 := bbase (se 3 (by rfl) ⟨111344, by rfl⟩ : syracuseStep 593837 = 222689) (by norm_num)
theorem B593861 : Blo 393766 593861 := bbase (se 4 (by rfl) ⟨55674, by rfl⟩ : syracuseStep 593861 = 111349) (by norm_num)
theorem B3379157 : Blo 393766 3379157 := bbase (se 7 (by rfl) ⟨39599, by rfl⟩ : syracuseStep 3379157 = 79199) (by norm_num)
theorem B593885 : Blo 393766 593885 := bbase (se 3 (by rfl) ⟨111353, by rfl⟩ : syracuseStep 593885 = 222707) (by norm_num)
theorem B561125 : Blo 393766 561125 := bbase (se 4 (by rfl) ⟨52605, by rfl⟩ : syracuseStep 561125 = 105211) (by norm_num)
theorem B888821 : Blo 393766 888821 := bbase (se 5 (by rfl) ⟨41663, by rfl⟩ : syracuseStep 888821 = 83327) (by norm_num)
theorem B593909 : Blo 393766 593909 := bbase (se 5 (by rfl) ⟨27839, by rfl⟩ : syracuseStep 593909 = 55679) (by norm_num)
theorem B593933 : Blo 393766 593933 := bbase (se 3 (by rfl) ⟨111362, by rfl⟩ : syracuseStep 593933 = 222725) (by norm_num)
theorem B593957 : Blo 393766 593957 := bbase (se 4 (by rfl) ⟨55683, by rfl⟩ : syracuseStep 593957 = 111367) (by norm_num)
theorem B561205 : Blo 393766 561205 := bbase (se 5 (by rfl) ⟨26306, by rfl⟩ : syracuseStep 561205 = 52613) (by norm_num)
theorem B888893 : Blo 393766 888893 := bbase (se 3 (by rfl) ⟨166667, by rfl⟩ : syracuseStep 888893 = 333335) (by norm_num)
theorem B593981 : Blo 393766 593981 := bbase (se 3 (by rfl) ⟨111371, by rfl⟩ : syracuseStep 593981 = 222743) (by norm_num)
theorem B594005 : Blo 393766 594005 := bbase (se 8 (by rfl) ⟨3480, by rfl⟩ : syracuseStep 594005 = 6961) (by norm_num)
theorem B594029 : Blo 393766 594029 := bbase (se 3 (by rfl) ⟨111380, by rfl⟩ : syracuseStep 594029 = 222761) (by norm_num)
theorem B888965 : Blo 393766 888965 := bbase (se 4 (by rfl) ⟨83340, by rfl⟩ : syracuseStep 888965 = 166681) (by norm_num)
theorem B594053 : Blo 393766 594053 := bbase (se 4 (by rfl) ⟨55692, by rfl⟩ : syracuseStep 594053 = 111385) (by norm_num)
theorem B594077 : Blo 393766 594077 := bbase (se 3 (by rfl) ⟨111389, by rfl⟩ : syracuseStep 594077 = 222779) (by norm_num)
theorem B561325 : Blo 393766 561325 := bbase (se 3 (by rfl) ⟨105248, by rfl⟩ : syracuseStep 561325 = 210497) (by norm_num)
theorem B1020077 : Blo 393766 1020077 := bbase (se 3 (by rfl) ⟨191264, by rfl⟩ : syracuseStep 1020077 = 382529) (by norm_num)
theorem B594101 : Blo 393766 594101 := bbase (se 5 (by rfl) ⟨27848, by rfl⟩ : syracuseStep 594101 = 55697) (by norm_num)
theorem B889037 : Blo 393766 889037 := bbase (se 3 (by rfl) ⟨166694, by rfl⟩ : syracuseStep 889037 = 333389) (by norm_num)
theorem B594125 : Blo 393766 594125 := bbase (se 3 (by rfl) ⟨111398, by rfl⟩ : syracuseStep 594125 = 222797) (by norm_num)
theorem B594149 : Blo 393766 594149 := bbase (se 4 (by rfl) ⟨55701, by rfl⟩ : syracuseStep 594149 = 111403) (by norm_num)
theorem B594173 : Blo 393766 594173 := bbase (se 3 (by rfl) ⟨111407, by rfl⟩ : syracuseStep 594173 = 222815) (by norm_num)
theorem B561421 : Blo 393766 561421 := bbase (se 3 (by rfl) ⟨105266, by rfl⟩ : syracuseStep 561421 = 210533) (by norm_num)
theorem B889109 : Blo 393766 889109 := bbase (se 6 (by rfl) ⟨20838, by rfl⟩ : syracuseStep 889109 = 41677) (by norm_num)
theorem B594197 : Blo 393766 594197 := bbase (se 6 (by rfl) ⟨13926, by rfl⟩ : syracuseStep 594197 = 27853) (by norm_num)
theorem B594221 : Blo 393766 594221 := bbase (se 3 (by rfl) ⟨111416, by rfl⟩ : syracuseStep 594221 = 222833) (by norm_num)
theorem B594245 : Blo 393766 594245 := bbase (se 4 (by rfl) ⟨55710, by rfl⟩ : syracuseStep 594245 = 111421) (by norm_num)
theorem B889181 : Blo 393766 889181 := bbase (se 3 (by rfl) ⟨166721, by rfl⟩ : syracuseStep 889181 = 333443) (by norm_num)
theorem B594269 : Blo 393766 594269 := bbase (se 3 (by rfl) ⟨111425, by rfl⟩ : syracuseStep 594269 = 222851) (by norm_num)
theorem B594293 : Blo 393766 594293 := bbase (se 5 (by rfl) ⟨27857, by rfl⟩ : syracuseStep 594293 = 55715) (by norm_num)
theorem B594317 : Blo 393766 594317 := bbase (se 3 (by rfl) ⟨111434, by rfl⟩ : syracuseStep 594317 = 222869) (by norm_num)
theorem B889253 : Blo 393766 889253 := bbase (se 4 (by rfl) ⟨83367, by rfl⟩ : syracuseStep 889253 = 166735) (by norm_num)
theorem B594341 : Blo 393766 594341 := bbase (se 4 (by rfl) ⟨55719, by rfl⟩ : syracuseStep 594341 = 111439) (by norm_num)
theorem B594365 : Blo 393766 594365 := bbase (se 3 (by rfl) ⟨111443, by rfl⟩ : syracuseStep 594365 = 222887) (by norm_num)
theorem B594389 : Blo 393766 594389 := bbase (se 7 (by rfl) ⟨6965, by rfl⟩ : syracuseStep 594389 = 13931) (by norm_num)
theorem B430553 : Blo 393766 430553 := bbase (se 2 (by rfl) ⟨161457, by rfl⟩ : syracuseStep 430553 = 322915) (by norm_num)
theorem B725477 : Blo 393766 725477 := bbase (se 4 (by rfl) ⟨68013, by rfl⟩ : syracuseStep 725477 = 136027) (by norm_num)
theorem B889325 : Blo 393766 889325 := bbase (se 3 (by rfl) ⟨166748, by rfl⟩ : syracuseStep 889325 = 333497) (by norm_num)
theorem B594413 : Blo 393766 594413 := bbase (se 3 (by rfl) ⟨111452, by rfl⟩ : syracuseStep 594413 = 222905) (by norm_num)
theorem B1282565 : Blo 393766 1282565 := bbase (se 4 (by rfl) ⟨120240, by rfl⟩ : syracuseStep 1282565 = 240481) (by norm_num)
theorem B594437 : Blo 393766 594437 := bbase (se 4 (by rfl) ⟨55728, by rfl⟩ : syracuseStep 594437 = 111457) (by norm_num)
theorem B594461 : Blo 393766 594461 := bbase (se 3 (by rfl) ⟨111461, by rfl⟩ : syracuseStep 594461 = 222923) (by norm_num)
theorem B889397 : Blo 393766 889397 := bbase (se 5 (by rfl) ⟨41690, by rfl⟩ : syracuseStep 889397 = 83381) (by norm_num)
theorem B594485 : Blo 393766 594485 := bbase (se 5 (by rfl) ⟨27866, by rfl⟩ : syracuseStep 594485 = 55733) (by norm_num)
theorem B594509 : Blo 393766 594509 := bbase (se 3 (by rfl) ⟨111470, by rfl⟩ : syracuseStep 594509 = 222941) (by norm_num)
theorem B1282645 : Blo 393766 1282645 := bbase (se 8 (by rfl) ⟨7515, by rfl⟩ : syracuseStep 1282645 = 15031) (by norm_num)
theorem B594533 : Blo 393766 594533 := bbase (se 4 (by rfl) ⟨55737, by rfl⟩ : syracuseStep 594533 = 111475) (by norm_num)
theorem B889469 : Blo 393766 889469 := bbase (se 3 (by rfl) ⟨166775, by rfl⟩ : syracuseStep 889469 = 333551) (by norm_num)
theorem B594557 : Blo 393766 594557 := bbase (se 3 (by rfl) ⟨111479, by rfl⟩ : syracuseStep 594557 = 222959) (by norm_num)
theorem B594581 : Blo 393766 594581 := bbase (se 6 (by rfl) ⟨13935, by rfl⟩ : syracuseStep 594581 = 27871) (by norm_num)
theorem B594605 : Blo 393766 594605 := bbase (se 3 (by rfl) ⟨111488, by rfl⟩ : syracuseStep 594605 = 222977) (by norm_num)
theorem B889541 : Blo 393766 889541 := bbase (se 4 (by rfl) ⟨83394, by rfl⟩ : syracuseStep 889541 = 166789) (by norm_num)
theorem B594629 : Blo 393766 594629 := bbase (se 4 (by rfl) ⟨55746, by rfl⟩ : syracuseStep 594629 = 111493) (by norm_num)
theorem B594653 : Blo 393766 594653 := bbase (se 3 (by rfl) ⟨111497, by rfl⟩ : syracuseStep 594653 = 222995) (by norm_num)
theorem B594677 : Blo 393766 594677 := bbase (se 5 (by rfl) ⟨27875, by rfl⟩ : syracuseStep 594677 = 55751) (by norm_num)
theorem B561917 : Blo 393766 561917 := bbase (se 3 (by rfl) ⟨105359, by rfl⟩ : syracuseStep 561917 = 210719) (by norm_num)
theorem B889613 : Blo 393766 889613 := bbase (se 3 (by rfl) ⟨166802, by rfl⟩ : syracuseStep 889613 = 333605) (by norm_num)
theorem B594701 : Blo 393766 594701 := bbase (se 3 (by rfl) ⟨111506, by rfl⟩ : syracuseStep 594701 = 223013) (by norm_num)
theorem B3805973 : Blo 393766 3805973 := bbase (se 6 (by rfl) ⟨89202, by rfl⟩ : syracuseStep 3805973 = 178405) (by norm_num)
theorem B955165 : Blo 393766 955165 := bbase (se 3 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 955165 = 358187) (by norm_num)
theorem B594725 : Blo 393766 594725 := bbase (se 4 (by rfl) ⟨55755, by rfl⟩ : syracuseStep 594725 = 111511) (by norm_num)
theorem B594749 : Blo 393766 594749 := bbase (se 3 (by rfl) ⟨111515, by rfl⟩ : syracuseStep 594749 = 223031) (by norm_num)
theorem B889685 : Blo 393766 889685 := bbase (se 9 (by rfl) ⟨2606, by rfl⟩ : syracuseStep 889685 = 5213) (by norm_num)
theorem B594773 : Blo 393766 594773 := bbase (se 9 (by rfl) ⟨1742, by rfl⟩ : syracuseStep 594773 = 3485) (by norm_num)
theorem B594797 : Blo 393766 594797 := bbase (se 3 (by rfl) ⟨111524, by rfl⟩ : syracuseStep 594797 = 223049) (by norm_num)
theorem B594821 : Blo 393766 594821 := bbase (se 4 (by rfl) ⟨55764, by rfl⟩ : syracuseStep 594821 = 111529) (by norm_num)
theorem B889757 : Blo 393766 889757 := bbase (se 3 (by rfl) ⟨166829, by rfl⟩ : syracuseStep 889757 = 333659) (by norm_num)
theorem B594845 : Blo 393766 594845 := bbase (se 3 (by rfl) ⟨111533, by rfl⟩ : syracuseStep 594845 = 223067) (by norm_num)
theorem B955309 : Blo 393766 955309 := bbase (se 3 (by rfl) ⟨179120, by rfl⟩ : syracuseStep 955309 = 358241) (by norm_num)
theorem B594869 : Blo 393766 594869 := bbase (se 5 (by rfl) ⟨27884, by rfl⟩ : syracuseStep 594869 = 55769) (by norm_num)
theorem B594893 : Blo 393766 594893 := bbase (se 3 (by rfl) ⟨111542, by rfl⟩ : syracuseStep 594893 = 223085) (by norm_num)
theorem B889829 : Blo 393766 889829 := bbase (se 4 (by rfl) ⟨83421, by rfl⟩ : syracuseStep 889829 = 166843) (by norm_num)
theorem B594917 : Blo 393766 594917 := bbase (se 4 (by rfl) ⟨55773, by rfl⟩ : syracuseStep 594917 = 111547) (by norm_num)
theorem B594941 : Blo 393766 594941 := bbase (se 3 (by rfl) ⟨111551, by rfl⟩ : syracuseStep 594941 = 223103) (by norm_num)
theorem B3052565 : Blo 393766 3052565 := bbase (se 6 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 3052565 = 143089) (by norm_num)
theorem B594965 : Blo 393766 594965 := bbase (se 6 (by rfl) ⟨13944, by rfl⟩ : syracuseStep 594965 = 27889) (by norm_num)
theorem B889901 : Blo 393766 889901 := bbase (se 3 (by rfl) ⟨166856, by rfl⟩ : syracuseStep 889901 = 333713) (by norm_num)
theorem B594989 : Blo 393766 594989 := bbase (se 3 (by rfl) ⟨111560, by rfl⟩ : syracuseStep 594989 = 223121) (by norm_num)
theorem B595013 : Blo 393766 595013 := bbase (se 4 (by rfl) ⟨55782, by rfl⟩ : syracuseStep 595013 = 111565) (by norm_num)
theorem B595037 : Blo 393766 595037 := bbase (se 3 (by rfl) ⟨111569, by rfl⟩ : syracuseStep 595037 = 223139) (by norm_num)
theorem B889973 : Blo 393766 889973 := bbase (se 5 (by rfl) ⟨41717, by rfl⟩ : syracuseStep 889973 = 83435) (by norm_num)
theorem B595061 : Blo 393766 595061 := bbase (se 5 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 595061 = 55787) (by norm_num)
theorem B2004101 : Blo 393766 2004101 := bbase (se 4 (by rfl) ⟨187884, by rfl⟩ : syracuseStep 2004101 = 375769) (by norm_num)
theorem B595085 : Blo 393766 595085 := bbase (se 3 (by rfl) ⟨111578, by rfl⟩ : syracuseStep 595085 = 223157) (by norm_num)
theorem B595109 : Blo 393766 595109 := bbase (se 4 (by rfl) ⟨55791, by rfl⟩ : syracuseStep 595109 = 111583) (by norm_num)
theorem B890045 : Blo 393766 890045 := bbase (se 3 (by rfl) ⟨166883, by rfl⟩ : syracuseStep 890045 = 333767) (by norm_num)
theorem B595133 : Blo 393766 595133 := bbase (se 3 (by rfl) ⟨111587, by rfl⟩ : syracuseStep 595133 = 223175) (by norm_num)
theorem B595157 : Blo 393766 595157 := bbase (se 7 (by rfl) ⟨6974, by rfl⟩ : syracuseStep 595157 = 13949) (by norm_num)
theorem B595181 : Blo 393766 595181 := bbase (se 3 (by rfl) ⟨111596, by rfl⟩ : syracuseStep 595181 = 223193) (by norm_num)
theorem B890117 : Blo 393766 890117 := bbase (se 4 (by rfl) ⟨83448, by rfl⟩ : syracuseStep 890117 = 166897) (by norm_num)
theorem B595205 : Blo 393766 595205 := bbase (se 4 (by rfl) ⟨55800, by rfl⟩ : syracuseStep 595205 = 111601) (by norm_num)
theorem B595229 : Blo 393766 595229 := bbase (se 3 (by rfl) ⟨111605, by rfl⟩ : syracuseStep 595229 = 223211) (by norm_num)
theorem B562469 : Blo 393766 562469 := bbase (se 4 (by rfl) ⟨52731, by rfl⟩ : syracuseStep 562469 = 105463) (by norm_num)
theorem B595253 : Blo 393766 595253 := bbase (se 5 (by rfl) ⟨27902, by rfl⟩ : syracuseStep 595253 = 55805) (by norm_num)
theorem B890189 : Blo 393766 890189 := bbase (se 3 (by rfl) ⟨166910, by rfl⟩ : syracuseStep 890189 = 333821) (by norm_num)
theorem B595277 : Blo 393766 595277 := bbase (se 3 (by rfl) ⟨111614, by rfl⟩ : syracuseStep 595277 = 223229) (by norm_num)
theorem B595301 : Blo 393766 595301 := bbase (se 4 (by rfl) ⟨55809, by rfl⟩ : syracuseStep 595301 = 111619) (by norm_num)
theorem B595325 : Blo 393766 595325 := bbase (se 3 (by rfl) ⟨111623, by rfl⟩ : syracuseStep 595325 = 223247) (by norm_num)
theorem B890261 : Blo 393766 890261 := bbase (se 6 (by rfl) ⟨20865, by rfl⟩ : syracuseStep 890261 = 41731) (by norm_num)
theorem B595349 : Blo 393766 595349 := bbase (se 6 (by rfl) ⟨13953, by rfl⟩ : syracuseStep 595349 = 27907) (by norm_num)
theorem B595373 : Blo 393766 595373 := bbase (se 3 (by rfl) ⟨111632, by rfl⟩ : syracuseStep 595373 = 223265) (by norm_num)
theorem B595397 : Blo 393766 595397 := bbase (se 4 (by rfl) ⟨55818, by rfl⟩ : syracuseStep 595397 = 111637) (by norm_num)
theorem B890333 : Blo 393766 890333 := bbase (se 3 (by rfl) ⟨166937, by rfl⟩ : syracuseStep 890333 = 333875) (by norm_num)
theorem B595421 : Blo 393766 595421 := bbase (se 3 (by rfl) ⟨111641, by rfl⟩ : syracuseStep 595421 = 223283) (by norm_num)
theorem B595445 : Blo 393766 595445 := bbase (se 5 (by rfl) ⟨27911, by rfl⟩ : syracuseStep 595445 = 55823) (by norm_num)
theorem B595469 : Blo 393766 595469 := bbase (se 3 (by rfl) ⟨111650, by rfl⟩ : syracuseStep 595469 = 223301) (by norm_num)
theorem B890405 : Blo 393766 890405 := bbase (se 4 (by rfl) ⟨83475, by rfl⟩ : syracuseStep 890405 = 166951) (by norm_num)
theorem B595493 : Blo 393766 595493 := bbase (se 4 (by rfl) ⟨55827, by rfl⟩ : syracuseStep 595493 = 111655) (by norm_num)
theorem B595517 : Blo 393766 595517 := bbase (se 3 (by rfl) ⟨111659, by rfl⟩ : syracuseStep 595517 = 223319) (by norm_num)
theorem B595541 : Blo 393766 595541 := bbase (se 8 (by rfl) ⟨3489, by rfl⟩ : syracuseStep 595541 = 6979) (by norm_num)
theorem B890477 : Blo 393766 890477 := bbase (se 3 (by rfl) ⟨166964, by rfl⟩ : syracuseStep 890477 = 333929) (by norm_num)
theorem B595565 : Blo 393766 595565 := bbase (se 3 (by rfl) ⟨111668, by rfl⟩ : syracuseStep 595565 = 223337) (by norm_num)
theorem B595589 : Blo 393766 595589 := bbase (se 4 (by rfl) ⟨55836, by rfl⟩ : syracuseStep 595589 = 111673) (by norm_num)
theorem B595613 : Blo 393766 595613 := bbase (se 3 (by rfl) ⟨111677, by rfl⟩ : syracuseStep 595613 = 223355) (by norm_num)
theorem B890549 : Blo 393766 890549 := bbase (se 5 (by rfl) ⟨41744, by rfl⟩ : syracuseStep 890549 = 83489) (by norm_num)
theorem B595637 : Blo 393766 595637 := bbase (se 5 (by rfl) ⟨27920, by rfl⟩ : syracuseStep 595637 = 55841) (by norm_num)
theorem B595661 : Blo 393766 595661 := bbase (se 3 (by rfl) ⟨111686, by rfl⟩ : syracuseStep 595661 = 223373) (by norm_num)
theorem B595685 : Blo 393766 595685 := bbase (se 4 (by rfl) ⟨55845, by rfl⟩ : syracuseStep 595685 = 111691) (by norm_num)
theorem B890621 : Blo 393766 890621 := bbase (se 3 (by rfl) ⟨166991, by rfl⟩ : syracuseStep 890621 = 333983) (by norm_num)
theorem B595709 : Blo 393766 595709 := bbase (se 3 (by rfl) ⟨111695, by rfl⟩ : syracuseStep 595709 = 223391) (by norm_num)
theorem B595733 : Blo 393766 595733 := bbase (se 6 (by rfl) ⟨13962, by rfl⟩ : syracuseStep 595733 = 27925) (by norm_num)
theorem B595757 : Blo 393766 595757 := bbase (se 3 (by rfl) ⟨111704, by rfl⟩ : syracuseStep 595757 = 223409) (by norm_num)
theorem B890693 : Blo 393766 890693 := bbase (se 4 (by rfl) ⟨83502, by rfl⟩ : syracuseStep 890693 = 167005) (by norm_num)
theorem B595781 : Blo 393766 595781 := bbase (se 4 (by rfl) ⟨55854, by rfl⟩ : syracuseStep 595781 = 111709) (by norm_num)
theorem B595805 : Blo 393766 595805 := bbase (se 3 (by rfl) ⟨111713, by rfl⟩ : syracuseStep 595805 = 223427) (by norm_num)
theorem B595829 : Blo 393766 595829 := bbase (se 5 (by rfl) ⟨27929, by rfl⟩ : syracuseStep 595829 = 55859) (by norm_num)
theorem B890765 : Blo 393766 890765 := bbase (se 3 (by rfl) ⟨167018, by rfl⟩ : syracuseStep 890765 = 334037) (by norm_num)
theorem B595853 : Blo 393766 595853 := bbase (se 3 (by rfl) ⟨111722, by rfl⟩ : syracuseStep 595853 = 223445) (by norm_num)
theorem B595877 : Blo 393766 595877 := bbase (se 4 (by rfl) ⟨55863, by rfl⟩ : syracuseStep 595877 = 111727) (by norm_num)
theorem B595901 : Blo 393766 595901 := bbase (se 3 (by rfl) ⟨111731, by rfl⟩ : syracuseStep 595901 = 223463) (by norm_num)
theorem B890837 : Blo 393766 890837 := bbase (se 7 (by rfl) ⟨10439, by rfl⟩ : syracuseStep 890837 = 20879) (by norm_num)
theorem B595925 : Blo 393766 595925 := bbase (se 7 (by rfl) ⟨6983, by rfl⟩ : syracuseStep 595925 = 13967) (by norm_num)
theorem B595949 : Blo 393766 595949 := bbase (se 3 (by rfl) ⟨111740, by rfl⟩ : syracuseStep 595949 = 223481) (by norm_num)
theorem B595973 : Blo 393766 595973 := bbase (se 4 (by rfl) ⟨55872, by rfl⟩ : syracuseStep 595973 = 111745) (by norm_num)
theorem B563221 : Blo 393766 563221 := bbase (se 6 (by rfl) ⟨13200, by rfl⟩ : syracuseStep 563221 = 26401) (by norm_num)
theorem B890909 : Blo 393766 890909 := bbase (se 3 (by rfl) ⟨167045, by rfl⟩ : syracuseStep 890909 = 334091) (by norm_num)
theorem B595997 : Blo 393766 595997 := bbase (se 3 (by rfl) ⟨111749, by rfl⟩ : syracuseStep 595997 = 223499) (by norm_num)
theorem B596021 : Blo 393766 596021 := bbase (se 5 (by rfl) ⟨27938, by rfl⟩ : syracuseStep 596021 = 55877) (by norm_num)
theorem B596045 : Blo 393766 596045 := bbase (se 3 (by rfl) ⟨111758, by rfl⟩ : syracuseStep 596045 = 223517) (by norm_num)
theorem B890981 : Blo 393766 890981 := bbase (se 4 (by rfl) ⟨83529, by rfl⟩ : syracuseStep 890981 = 167059) (by norm_num)
theorem B596069 : Blo 393766 596069 := bbase (se 4 (by rfl) ⟨55881, by rfl⟩ : syracuseStep 596069 = 111763) (by norm_num)
theorem B596093 : Blo 393766 596093 := bbase (se 3 (by rfl) ⟨111767, by rfl⟩ : syracuseStep 596093 = 223535) (by norm_num)
theorem B596117 : Blo 393766 596117 := bbase (se 6 (by rfl) ⟨13971, by rfl⟩ : syracuseStep 596117 = 27943) (by norm_num)
theorem B891053 : Blo 393766 891053 := bbase (se 3 (by rfl) ⟨167072, by rfl⟩ : syracuseStep 891053 = 334145) (by norm_num)
theorem B596141 : Blo 393766 596141 := bbase (se 3 (by rfl) ⟨111776, by rfl⟩ : syracuseStep 596141 = 223553) (by norm_num)
theorem B1808581 : Blo 393766 1808581 := bbase (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) (by norm_num)
theorem B596165 : Blo 393766 596165 := bbase (se 4 (by rfl) ⟨55890, by rfl⟩ : syracuseStep 596165 = 111781) (by norm_num)
theorem B596189 : Blo 393766 596189 := bbase (se 3 (by rfl) ⟨111785, by rfl⟩ : syracuseStep 596189 = 223571) (by norm_num)
theorem B891125 : Blo 393766 891125 := bbase (se 5 (by rfl) ⟨41771, by rfl⟩ : syracuseStep 891125 = 83543) (by norm_num)
theorem B596213 : Blo 393766 596213 := bbase (se 5 (by rfl) ⟨27947, by rfl⟩ : syracuseStep 596213 = 55895) (by norm_num)
theorem B596237 : Blo 393766 596237 := bbase (se 3 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 596237 = 223589) (by norm_num)
theorem B596261 : Blo 393766 596261 := bbase (se 4 (by rfl) ⟨55899, by rfl⟩ : syracuseStep 596261 = 111799) (by norm_num)
theorem B891197 : Blo 393766 891197 := bbase (se 3 (by rfl) ⟨167099, by rfl⟩ : syracuseStep 891197 = 334199) (by norm_num)
theorem B596285 : Blo 393766 596285 := bbase (se 3 (by rfl) ⟨111803, by rfl⟩ : syracuseStep 596285 = 223607) (by norm_num)
theorem B596309 : Blo 393766 596309 := bbase (se 10 (by rfl) ⟨873, by rfl⟩ : syracuseStep 596309 = 1747) (by norm_num)
theorem B399713 : Blo 393766 399713 := bbase (se 2 (by rfl) ⟨149892, by rfl⟩ : syracuseStep 399713 = 299785) (by norm_num)
theorem B596333 : Blo 393766 596333 := bbase (se 3 (by rfl) ⟨111812, by rfl⟩ : syracuseStep 596333 = 223625) (by norm_num)
theorem B891269 : Blo 393766 891269 := bbase (se 4 (by rfl) ⟨83556, by rfl⟩ : syracuseStep 891269 = 167113) (by norm_num)
theorem B596357 : Blo 393766 596357 := bbase (se 4 (by rfl) ⟨55908, by rfl⟩ : syracuseStep 596357 = 111817) (by norm_num)
theorem B2005397 : Blo 393766 2005397 := bbase (se 6 (by rfl) ⟨47001, by rfl⟩ : syracuseStep 2005397 = 94003) (by norm_num)
theorem B596381 : Blo 393766 596381 := bbase (se 3 (by rfl) ⟨111821, by rfl⟩ : syracuseStep 596381 = 223643) (by norm_num)
theorem B596405 : Blo 393766 596405 := bbase (se 5 (by rfl) ⟨27956, by rfl⟩ : syracuseStep 596405 = 55913) (by norm_num)
theorem B1612229 : Blo 393766 1612229 := bbase (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) (by norm_num)
theorem B891341 : Blo 393766 891341 := bbase (se 3 (by rfl) ⟨167126, by rfl⟩ : syracuseStep 891341 = 334253) (by norm_num)
theorem B596429 : Blo 393766 596429 := bbase (se 3 (by rfl) ⟨111830, by rfl⟩ : syracuseStep 596429 = 223661) (by norm_num)
theorem B596453 : Blo 393766 596453 := bbase (se 4 (by rfl) ⟨55917, by rfl⟩ : syracuseStep 596453 = 111835) (by norm_num)
theorem B596477 : Blo 393766 596477 := bbase (se 3 (by rfl) ⟨111839, by rfl⟩ : syracuseStep 596477 = 223679) (by norm_num)
theorem B891413 : Blo 393766 891413 := bbase (se 6 (by rfl) ⟨20892, by rfl⟩ : syracuseStep 891413 = 41785) (by norm_num)
theorem B596501 : Blo 393766 596501 := bbase (se 6 (by rfl) ⟨13980, by rfl⟩ : syracuseStep 596501 = 27961) (by norm_num)
theorem B596525 : Blo 393766 596525 := bbase (se 3 (by rfl) ⟨111848, by rfl⟩ : syracuseStep 596525 = 223697) (by norm_num)
theorem B596549 : Blo 393766 596549 := bbase (se 4 (by rfl) ⟨55926, by rfl⟩ : syracuseStep 596549 = 111853) (by norm_num)
theorem B891485 : Blo 393766 891485 := bbase (se 3 (by rfl) ⟨167153, by rfl⟩ : syracuseStep 891485 = 334307) (by norm_num)
theorem B596573 : Blo 393766 596573 := bbase (se 3 (by rfl) ⟨111857, by rfl⟩ : syracuseStep 596573 = 223715) (by norm_num)
theorem B596597 : Blo 393766 596597 := bbase (se 5 (by rfl) ⟨27965, by rfl⟩ : syracuseStep 596597 = 55931) (by norm_num)
theorem B596621 : Blo 393766 596621 := bbase (se 3 (by rfl) ⟨111866, by rfl⟩ : syracuseStep 596621 = 223733) (by norm_num)
theorem B891557 : Blo 393766 891557 := bbase (se 4 (by rfl) ⟨83583, by rfl⟩ : syracuseStep 891557 = 167167) (by norm_num)
theorem B596645 : Blo 393766 596645 := bbase (se 4 (by rfl) ⟨55935, by rfl⟩ : syracuseStep 596645 = 111871) (by norm_num)
theorem B498413 : Blo 393766 498413 := bbase (se 3 (by rfl) ⟨93452, by rfl⟩ : syracuseStep 498413 = 186905) (by norm_num)
theorem B891629 : Blo 393766 891629 := bbase (se 3 (by rfl) ⟨167180, by rfl⟩ : syracuseStep 891629 = 334361) (by norm_num)
theorem B498469 : Blo 393766 498469 := bbase (se 4 (by rfl) ⟨46731, by rfl⟩ : syracuseStep 498469 = 93463) (by norm_num)
theorem B564013 : Blo 393766 564013 := bbase (se 3 (by rfl) ⟨105752, by rfl⟩ : syracuseStep 564013 = 211505) (by norm_num)
theorem B891701 : Blo 393766 891701 := bbase (se 5 (by rfl) ⟨41798, by rfl⟩ : syracuseStep 891701 = 83597) (by norm_num)
theorem B891773 : Blo 393766 891773 := bbase (se 3 (by rfl) ⟨167207, by rfl⟩ : syracuseStep 891773 = 334415) (by norm_num)
theorem B498565 : Blo 393766 498565 := bbase (se 4 (by rfl) ⟨46740, by rfl⟩ : syracuseStep 498565 = 93481) (by norm_num)
theorem B400297 : Blo 393766 400297 := bbase (se 2 (by rfl) ⟨150111, by rfl⟩ : syracuseStep 400297 = 300223) (by norm_num)
theorem B891845 : Blo 393766 891845 := bbase (se 4 (by rfl) ⟨83610, by rfl⟩ : syracuseStep 891845 = 167221) (by norm_num)
theorem B891917 : Blo 393766 891917 := bbase (se 3 (by rfl) ⟨167234, by rfl⟩ : syracuseStep 891917 = 334469) (by norm_num)
theorem B498737 : Blo 393766 498737 := bbase (se 2 (by rfl) ⟨187026, by rfl⟩ : syracuseStep 498737 = 374053) (by norm_num)
theorem B891989 : Blo 393766 891989 := bbase (se 8 (by rfl) ⟨5226, by rfl⟩ : syracuseStep 891989 = 10453) (by norm_num)
theorem B498793 : Blo 393766 498793 := bbase (se 2 (by rfl) ⟨187047, by rfl⟩ : syracuseStep 498793 = 374095) (by norm_num)
theorem B564349 : Blo 393766 564349 := bbase (se 3 (by rfl) ⟨105815, by rfl⟩ : syracuseStep 564349 = 211631) (by norm_num)
theorem B892061 : Blo 393766 892061 := bbase (se 3 (by rfl) ⟨167261, by rfl⟩ : syracuseStep 892061 = 334523) (by norm_num)
theorem B498889 : Blo 393766 498889 := bbase (se 2 (by rfl) ⟨187083, by rfl⟩ : syracuseStep 498889 = 374167) (by norm_num)
theorem B892133 : Blo 393766 892133 := bbase (se 4 (by rfl) ⟨83637, by rfl⟩ : syracuseStep 892133 = 167275) (by norm_num)
theorem B892205 : Blo 393766 892205 := bbase (se 3 (by rfl) ⟨167288, by rfl⟩ : syracuseStep 892205 = 334577) (by norm_num)
theorem B564565 : Blo 393766 564565 := bbase (se 11 (by rfl) ⟨413, by rfl⟩ : syracuseStep 564565 = 827) (by norm_num)
theorem B499061 : Blo 393766 499061 := bbase (se 5 (by rfl) ⟨23393, by rfl⟩ : syracuseStep 499061 = 46787) (by norm_num)
theorem B892277 : Blo 393766 892277 := bbase (se 5 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 892277 = 83651) (by norm_num)
theorem B499117 : Blo 393766 499117 := bbase (se 3 (by rfl) ⟨93584, by rfl⟩ : syracuseStep 499117 = 187169) (by norm_num)
theorem B892349 : Blo 393766 892349 := bbase (se 3 (by rfl) ⟨167315, by rfl⟩ : syracuseStep 892349 = 334631) (by norm_num)
theorem B892421 : Blo 393766 892421 := bbase (se 4 (by rfl) ⟨83664, by rfl⟩ : syracuseStep 892421 = 167329) (by norm_num)
theorem B499213 : Blo 393766 499213 := bbase (se 3 (by rfl) ⟨93602, by rfl⟩ : syracuseStep 499213 = 187205) (by norm_num)
theorem B892493 : Blo 393766 892493 := bbase (se 3 (by rfl) ⟨167342, by rfl⟩ : syracuseStep 892493 = 334685) (by norm_num)
theorem B892565 : Blo 393766 892565 := bbase (se 6 (by rfl) ⟨20919, by rfl⟩ : syracuseStep 892565 = 41839) (by norm_num)
theorem B2006693 : Blo 393766 2006693 := bbase (se 4 (by rfl) ⟨188127, by rfl⟩ : syracuseStep 2006693 = 376255) (by norm_num)
theorem B499385 : Blo 393766 499385 := bbase (se 2 (by rfl) ⟨187269, by rfl⟩ : syracuseStep 499385 = 374539) (by norm_num)
theorem B564941 : Blo 393766 564941 := bbase (se 3 (by rfl) ⟨105926, by rfl⟩ : syracuseStep 564941 = 211853) (by norm_num)
theorem B892637 : Blo 393766 892637 := bbase (se 3 (by rfl) ⟨167369, by rfl⟩ : syracuseStep 892637 = 334739) (by norm_num)
theorem B499441 : Blo 393766 499441 := bbase (se 2 (by rfl) ⟨187290, by rfl⟩ : syracuseStep 499441 = 374581) (by norm_num)
theorem B892709 : Blo 393766 892709 := bbase (se 4 (by rfl) ⟨83691, by rfl⟩ : syracuseStep 892709 = 167383) (by norm_num)
theorem B499537 : Blo 393766 499537 := bbase (se 2 (by rfl) ⟨187326, by rfl⟩ : syracuseStep 499537 = 374653) (by norm_num)
theorem B4530005 : Blo 393766 4530005 := bbase (se 9 (by rfl) ⟨13271, by rfl⟩ : syracuseStep 4530005 = 26543) (by norm_num)
theorem B892781 : Blo 393766 892781 := bbase (se 3 (by rfl) ⟨167396, by rfl⟩ : syracuseStep 892781 = 334793) (by norm_num)
theorem B2039701 : Blo 393766 2039701 := bbase (se 6 (by rfl) ⟨47805, by rfl⟩ : syracuseStep 2039701 = 95611) (by norm_num)
theorem B1089445 : Blo 393766 1089445 := bbase (se 4 (by rfl) ⟨102135, by rfl⟩ : syracuseStep 1089445 = 204271) (by norm_num)
theorem B892853 : Blo 393766 892853 := bbase (se 5 (by rfl) ⟨41852, by rfl⟩ : syracuseStep 892853 = 83705) (by norm_num)
theorem B2400245 : Blo 393766 2400245 := bbase (se 5 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 2400245 = 225023) (by norm_num)
theorem B892925 : Blo 393766 892925 := bbase (se 3 (by rfl) ⟨167423, by rfl⟩ : syracuseStep 892925 = 334847) (by norm_num)
theorem B499709 : Blo 393766 499709 := bbase (se 3 (by rfl) ⟨93695, by rfl⟩ : syracuseStep 499709 = 187391) (by norm_num)
theorem B499765 : Blo 393766 499765 := bbase (se 5 (by rfl) ⟨23426, by rfl⟩ : syracuseStep 499765 = 46853) (by norm_num)
theorem B892997 : Blo 393766 892997 := bbase (se 4 (by rfl) ⟨83718, by rfl⟩ : syracuseStep 892997 = 167437) (by norm_num)
theorem B1351781 : Blo 393766 1351781 := bbase (se 4 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 1351781 = 253459) (by norm_num)
theorem B893069 : Blo 393766 893069 := bbase (se 3 (by rfl) ⟨167450, by rfl⟩ : syracuseStep 893069 = 334901) (by norm_num)
theorem B499861 : Blo 393766 499861 := bbase (se 6 (by rfl) ⟨11715, by rfl⟩ : syracuseStep 499861 = 23431) (by norm_num)
theorem B893141 : Blo 393766 893141 := bbase (se 7 (by rfl) ⟨10466, by rfl⟩ : syracuseStep 893141 = 20933) (by norm_num)
theorem B2990357 : Blo 393766 2990357 := bbase (se 6 (by rfl) ⟨70086, by rfl⟩ : syracuseStep 2990357 = 140173) (by norm_num)
theorem B893213 : Blo 393766 893213 := bbase (se 3 (by rfl) ⟨167477, by rfl⟩ : syracuseStep 893213 = 334955) (by norm_num)
theorem B500033 : Blo 393766 500033 := bbase (se 2 (by rfl) ⟨187512, by rfl⟩ : syracuseStep 500033 = 375025) (by norm_num)
theorem B893285 : Blo 393766 893285 := bbase (se 4 (by rfl) ⟨83745, by rfl⟩ : syracuseStep 893285 = 167491) (by norm_num)
theorem B500089 : Blo 393766 500089 := bbase (se 2 (by rfl) ⟨187533, by rfl⟩ : syracuseStep 500089 = 375067) (by norm_num)
theorem B401809 : Blo 393766 401809 := bbase (se 2 (by rfl) ⟨150678, by rfl⟩ : syracuseStep 401809 = 301357) (by norm_num)
theorem B631189 : Blo 393766 631189 := bbase (se 6 (by rfl) ⟨14793, by rfl⟩ : syracuseStep 631189 = 29587) (by norm_num)
theorem B893357 : Blo 393766 893357 := bbase (se 3 (by rfl) ⟨167504, by rfl⟩ : syracuseStep 893357 = 335009) (by norm_num)
theorem B401857 : Blo 393766 401857 := bbase (se 2 (by rfl) ⟨150696, by rfl⟩ : syracuseStep 401857 = 301393) (by norm_num)
theorem B500185 : Blo 393766 500185 := bbase (se 2 (by rfl) ⟨187569, by rfl⟩ : syracuseStep 500185 = 375139) (by norm_num)
theorem B893429 : Blo 393766 893429 := bbase (se 5 (by rfl) ⟨41879, by rfl⟩ : syracuseStep 893429 = 83759) (by norm_num)
theorem B893501 : Blo 393766 893501 := bbase (se 3 (by rfl) ⟨167531, by rfl⟩ : syracuseStep 893501 = 335063) (by norm_num)
theorem B500357 : Blo 393766 500357 := bbase (se 4 (by rfl) ⟨46908, by rfl⟩ : syracuseStep 500357 = 93817) (by norm_num)
theorem B893573 : Blo 393766 893573 := bbase (se 4 (by rfl) ⟨83772, by rfl⟩ : syracuseStep 893573 = 167545) (by norm_num)
theorem B500413 : Blo 393766 500413 := bbase (se 3 (by rfl) ⟨93827, by rfl⟩ : syracuseStep 500413 = 187655) (by norm_num)
theorem B1516229 : Blo 393766 1516229 := bbase (se 4 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 1516229 = 284293) (by norm_num)
theorem B893645 : Blo 393766 893645 := bbase (se 3 (by rfl) ⟨167558, by rfl⟩ : syracuseStep 893645 = 335117) (by norm_num)
theorem B402149 : Blo 393766 402149 := bbase (se 4 (by rfl) ⟨37701, by rfl⟩ : syracuseStep 402149 = 75403) (by norm_num)
theorem B893717 : Blo 393766 893717 := bbase (se 6 (by rfl) ⟨20946, by rfl⟩ : syracuseStep 893717 = 41893) (by norm_num)
theorem B500509 : Blo 393766 500509 := bbase (se 3 (by rfl) ⟨93845, by rfl⟩ : syracuseStep 500509 = 187691) (by norm_num)
theorem B631613 : Blo 393766 631613 := bbase (se 3 (by rfl) ⟨118427, by rfl⟩ : syracuseStep 631613 = 236855) (by norm_num)
theorem B893789 : Blo 393766 893789 := bbase (se 3 (by rfl) ⟨167585, by rfl⟩ : syracuseStep 893789 = 335171) (by norm_num)
theorem B893861 : Blo 393766 893861 := bbase (se 4 (by rfl) ⟨83799, by rfl⟩ : syracuseStep 893861 = 167599) (by norm_num)
theorem B1123253 : Blo 393766 1123253 := bbase (se 5 (by rfl) ⟨52652, by rfl⟩ : syracuseStep 1123253 = 105305) (by norm_num)
theorem B2007989 : Blo 393766 2007989 := bbase (se 5 (by rfl) ⟨94124, by rfl⟩ : syracuseStep 2007989 = 188249) (by norm_num)
theorem B664517 : Blo 393766 664517 := bbase (se 4 (by rfl) ⟨62298, by rfl⟩ : syracuseStep 664517 = 124597) (by norm_num)
theorem B500681 : Blo 393766 500681 := bbase (se 2 (by rfl) ⟨187755, by rfl⟩ : syracuseStep 500681 = 375511) (by norm_num)
theorem B402409 : Blo 393766 402409 := bbase (se 2 (by rfl) ⟨150903, by rfl⟩ : syracuseStep 402409 = 301807) (by norm_num)
theorem B893933 : Blo 393766 893933 := bbase (se 3 (by rfl) ⟨167612, by rfl⟩ : syracuseStep 893933 = 335225) (by norm_num)
theorem B500737 : Blo 393766 500737 := bbase (se 2 (by rfl) ⟨187776, by rfl⟩ : syracuseStep 500737 = 375553) (by norm_num)
theorem B894005 : Blo 393766 894005 := bbase (se 5 (by rfl) ⟨41906, by rfl⟩ : syracuseStep 894005 = 83813) (by norm_num)
theorem B664645 : Blo 393766 664645 := bbase (se 4 (by rfl) ⟨62310, by rfl⟩ : syracuseStep 664645 = 124621) (by norm_num)
theorem B631901 : Blo 393766 631901 := bbase (se 3 (by rfl) ⟨118481, by rfl⟩ : syracuseStep 631901 = 236963) (by norm_num)
theorem B500833 : Blo 393766 500833 := bbase (se 2 (by rfl) ⟨187812, by rfl⟩ : syracuseStep 500833 = 375625) (by norm_num)
theorem B894077 : Blo 393766 894077 := bbase (se 3 (by rfl) ⟨167639, by rfl⟩ : syracuseStep 894077 = 335279) (by norm_num)
theorem B664733 : Blo 393766 664733 := bbase (se 3 (by rfl) ⟨124637, by rfl⟩ : syracuseStep 664733 = 249275) (by norm_num)
theorem B894149 : Blo 393766 894149 := bbase (se 4 (by rfl) ⟨83826, by rfl⟩ : syracuseStep 894149 = 167653) (by norm_num)
theorem B1352933 : Blo 393766 1352933 := bbase (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) (by norm_num)
theorem B501005 : Blo 393766 501005 := bbase (se 3 (by rfl) ⟨93938, by rfl⟩ : syracuseStep 501005 = 187877) (by norm_num)
theorem B894221 : Blo 393766 894221 := bbase (se 3 (by rfl) ⟨167666, by rfl⟩ : syracuseStep 894221 = 335333) (by norm_num)
theorem B664861 : Blo 393766 664861 := bbase (se 3 (by rfl) ⟨124661, by rfl⟩ : syracuseStep 664861 = 249323) (by norm_num)
theorem B501061 : Blo 393766 501061 := bbase (se 4 (by rfl) ⟨46974, by rfl⟩ : syracuseStep 501061 = 93949) (by norm_num)
theorem B599381 : Blo 393766 599381 := bbase (se 12 (by rfl) ⟨219, by rfl⟩ : syracuseStep 599381 = 439) (by norm_num)
theorem B894293 : Blo 393766 894293 := bbase (se 12 (by rfl) ⟨327, by rfl⟩ : syracuseStep 894293 = 655) (by norm_num)
theorem B599405 : Blo 393766 599405 := bbase (se 3 (by rfl) ⟨112388, by rfl⟩ : syracuseStep 599405 = 224777) (by norm_num)
theorem B664949 : Blo 393766 664949 := bbase (se 5 (by rfl) ⟨31169, by rfl⟩ : syracuseStep 664949 = 62339) (by norm_num)
theorem B599429 : Blo 393766 599429 := bbase (se 4 (by rfl) ⟨56196, by rfl⟩ : syracuseStep 599429 = 112393) (by norm_num)
theorem B894365 : Blo 393766 894365 := bbase (se 3 (by rfl) ⟨167693, by rfl⟩ : syracuseStep 894365 = 335387) (by norm_num)
theorem B501157 : Blo 393766 501157 := bbase (se 4 (by rfl) ⟨46983, by rfl⟩ : syracuseStep 501157 = 93967) (by norm_num)
theorem B533989 : Blo 393766 533989 := bbase (se 4 (by rfl) ⟨50061, by rfl⟩ : syracuseStep 533989 = 100123) (by norm_num)
theorem B894437 : Blo 393766 894437 := bbase (se 4 (by rfl) ⟨83853, by rfl⟩ : syracuseStep 894437 = 167707) (by norm_num)
theorem B665077 : Blo 393766 665077 := bbase (se 5 (by rfl) ⟨31175, by rfl⟩ : syracuseStep 665077 = 62351) (by norm_num)
theorem B894509 : Blo 393766 894509 := bbase (se 3 (by rfl) ⟨167720, by rfl⟩ : syracuseStep 894509 = 335441) (by norm_num)
theorem B402989 : Blo 393766 402989 := bbase (se 3 (by rfl) ⟨75560, by rfl⟩ : syracuseStep 402989 = 151121) (by norm_num)
theorem B665165 : Blo 393766 665165 := bbase (se 3 (by rfl) ⟨124718, by rfl⟩ : syracuseStep 665165 = 249437) (by norm_num)
theorem B501329 : Blo 393766 501329 := bbase (se 2 (by rfl) ⟨187998, by rfl⟩ : syracuseStep 501329 = 375997) (by norm_num)
theorem B894581 : Blo 393766 894581 := bbase (se 5 (by rfl) ⟨41933, by rfl⟩ : syracuseStep 894581 = 83867) (by norm_num)
theorem B1910405 : Blo 393766 1910405 := bbase (se 4 (by rfl) ⟨179100, by rfl⟩ : syracuseStep 1910405 = 358201) (by norm_num)
theorem B501385 : Blo 393766 501385 := bbase (se 2 (by rfl) ⟨188019, by rfl⟩ : syracuseStep 501385 = 376039) (by norm_num)
theorem B534205 : Blo 393766 534205 := bbase (se 3 (by rfl) ⟨100163, by rfl⟩ : syracuseStep 534205 = 200327) (by norm_num)
theorem B894653 : Blo 393766 894653 := bbase (se 3 (by rfl) ⟨167747, by rfl⟩ : syracuseStep 894653 = 335495) (by norm_num)
theorem B665293 : Blo 393766 665293 := bbase (se 3 (by rfl) ⟨124742, by rfl⟩ : syracuseStep 665293 = 249485) (by norm_num)
theorem B7186133 : Blo 393766 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B501481 : Blo 393766 501481 := bbase (se 2 (by rfl) ⟨188055, by rfl⟩ : syracuseStep 501481 = 376111) (by norm_num)
theorem B894725 : Blo 393766 894725 := bbase (se 4 (by rfl) ⟨83880, by rfl⟩ : syracuseStep 894725 = 167761) (by norm_num)
theorem B665381 : Blo 393766 665381 := bbase (se 4 (by rfl) ⟨62379, by rfl⟩ : syracuseStep 665381 = 124759) (by norm_num)
theorem B894797 : Blo 393766 894797 := bbase (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) (by norm_num)
theorem B632701 : Blo 393766 632701 := bbase (se 3 (by rfl) ⟨118631, by rfl⟩ : syracuseStep 632701 = 237263) (by norm_num)
theorem B501653 : Blo 393766 501653 := bbase (se 6 (by rfl) ⟨11757, by rfl⟩ : syracuseStep 501653 = 23515) (by norm_num)
theorem B894869 : Blo 393766 894869 := bbase (se 6 (by rfl) ⟨20973, by rfl⟩ : syracuseStep 894869 = 41947) (by norm_num)
theorem B665509 : Blo 393766 665509 := bbase (se 4 (by rfl) ⟨62391, by rfl⟩ : syracuseStep 665509 = 124783) (by norm_num)
theorem B501709 : Blo 393766 501709 := bbase (se 3 (by rfl) ⟨94070, by rfl⟩ : syracuseStep 501709 = 188141) (by norm_num)
theorem B894941 : Blo 393766 894941 := bbase (se 3 (by rfl) ⟨167801, by rfl⟩ : syracuseStep 894941 = 335603) (by norm_num)
theorem B665597 : Blo 393766 665597 := bbase (se 3 (by rfl) ⟨124799, by rfl⟩ : syracuseStep 665597 = 249599) (by norm_num)
theorem B501805 : Blo 393766 501805 := bbase (se 3 (by rfl) ⟨94088, by rfl⟩ : syracuseStep 501805 = 188177) (by norm_num)
theorem B1124437 : Blo 393766 1124437 := bbase (se 8 (by rfl) ⟨6588, by rfl⟩ : syracuseStep 1124437 = 13177) (by norm_num)
theorem B665725 : Blo 393766 665725 := bbase (se 3 (by rfl) ⟨124823, by rfl⟩ : syracuseStep 665725 = 249647) (by norm_num)
theorem B2009285 : Blo 393766 2009285 := bbase (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) (by norm_num)
theorem B665813 : Blo 393766 665813 := bbase (se 7 (by rfl) ⟨7802, by rfl⟩ : syracuseStep 665813 = 15605) (by norm_num)
theorem B501977 : Blo 393766 501977 := bbase (se 2 (by rfl) ⟨188241, by rfl⟩ : syracuseStep 501977 = 376483) (by norm_num)
theorem B1124597 : Blo 393766 1124597 := bbase (se 5 (by rfl) ⟨52715, by rfl⟩ : syracuseStep 1124597 = 105431) (by norm_num)
theorem B502033 : Blo 393766 502033 := bbase (se 2 (by rfl) ⟨188262, by rfl⟩ : syracuseStep 502033 = 376525) (by norm_num)
theorem B665941 : Blo 393766 665941 := bbase (se 10 (by rfl) ⟨975, by rfl⟩ : syracuseStep 665941 = 1951) (by norm_num)
theorem B502129 : Blo 393766 502129 := bbase (se 2 (by rfl) ⟨188298, by rfl⟩ : syracuseStep 502129 = 376597) (by norm_num)
theorem B633253 : Blo 393766 633253 := bbase (se 4 (by rfl) ⟨59367, by rfl⟩ : syracuseStep 633253 = 118735) (by norm_num)
theorem B666029 : Blo 393766 666029 := bbase (se 3 (by rfl) ⟨124880, by rfl⟩ : syracuseStep 666029 = 249761) (by norm_num)
theorem B1124837 : Blo 393766 1124837 := bbase (se 4 (by rfl) ⟨105453, by rfl⟩ : syracuseStep 1124837 = 210907) (by norm_num)
theorem B2599445 : Blo 393766 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B502301 : Blo 393766 502301 := bbase (se 3 (by rfl) ⟨94181, by rfl⟩ : syracuseStep 502301 = 188363) (by norm_num)
theorem B666157 : Blo 393766 666157 := bbase (se 3 (by rfl) ⟨124904, by rfl⟩ : syracuseStep 666157 = 249809) (by norm_num)
theorem B502357 : Blo 393766 502357 := bbase (se 8 (by rfl) ⟨2943, by rfl⟩ : syracuseStep 502357 = 5887) (by norm_num)
theorem B666245 : Blo 393766 666245 := bbase (se 4 (by rfl) ⟨62460, by rfl⟩ : syracuseStep 666245 = 124921) (by norm_num)
theorem B1125029 : Blo 393766 1125029 := bbase (se 4 (by rfl) ⟨105471, by rfl⟩ : syracuseStep 1125029 = 210943) (by norm_num)
theorem B633509 : Blo 393766 633509 := bbase (se 4 (by rfl) ⟨59391, by rfl⟩ : syracuseStep 633509 = 118783) (by norm_num)
theorem B502453 : Blo 393766 502453 := bbase (se 5 (by rfl) ⟨23552, by rfl⟩ : syracuseStep 502453 = 47105) (by norm_num)
theorem B666373 : Blo 393766 666373 := bbase (se 4 (by rfl) ⟨62472, by rfl⟩ : syracuseStep 666373 = 124945) (by norm_num)
theorem B600853 : Blo 393766 600853 := bbase (se 6 (by rfl) ⟨14082, by rfl⟩ : syracuseStep 600853 = 28165) (by norm_num)
theorem B2534165 : Blo 393766 2534165 := bbase (se 6 (by rfl) ⟨59394, by rfl⟩ : syracuseStep 2534165 = 118789) (by norm_num)
theorem B666461 : Blo 393766 666461 := bbase (se 3 (by rfl) ⟨124961, by rfl⟩ : syracuseStep 666461 = 249923) (by norm_num)
theorem B502625 : Blo 393766 502625 := bbase (se 2 (by rfl) ⟨188484, by rfl⟩ : syracuseStep 502625 = 376969) (by norm_num)
theorem B4107125 : Blo 393766 4107125 := bbase (se 5 (by rfl) ⟨192521, by rfl⟩ : syracuseStep 4107125 = 385043) (by norm_num)
theorem B502681 : Blo 393766 502681 := bbase (se 2 (by rfl) ⟨188505, by rfl⟩ : syracuseStep 502681 = 377011) (by norm_num)
theorem B666589 : Blo 393766 666589 := bbase (se 3 (by rfl) ⟨124985, by rfl⟩ : syracuseStep 666589 = 249971) (by norm_num)
theorem B502777 : Blo 393766 502777 := bbase (se 2 (by rfl) ⟨188541, by rfl⟩ : syracuseStep 502777 = 377083) (by norm_num)
theorem B666677 : Blo 393766 666677 := bbase (se 5 (by rfl) ⟨31250, by rfl⟩ : syracuseStep 666677 = 62501) (by norm_num)
theorem B601157 : Blo 393766 601157 := bbase (se 4 (by rfl) ⟨56358, by rfl⟩ : syracuseStep 601157 = 112717) (by norm_num)
theorem B601229 : Blo 393766 601229 := bbase (se 3 (by rfl) ⟨112730, by rfl⟩ : syracuseStep 601229 = 225461) (by norm_num)
theorem B502949 : Blo 393766 502949 := bbase (se 4 (by rfl) ⟨47151, by rfl⟩ : syracuseStep 502949 = 94303) (by norm_num)
theorem B666805 : Blo 393766 666805 := bbase (se 5 (by rfl) ⟨31256, by rfl⟩ : syracuseStep 666805 = 62513) (by norm_num)
theorem B503005 : Blo 393766 503005 := bbase (se 3 (by rfl) ⟨94313, by rfl⟩ : syracuseStep 503005 = 188627) (by norm_num)
theorem B3222773 : Blo 393766 3222773 := bbase (se 5 (by rfl) ⟨151067, by rfl⟩ : syracuseStep 3222773 = 302135) (by norm_num)
theorem B1682693 : Blo 393766 1682693 := bbase (se 4 (by rfl) ⟨157752, by rfl⟩ : syracuseStep 1682693 = 315505) (by norm_num)
theorem B666893 : Blo 393766 666893 := bbase (se 3 (by rfl) ⟨125042, by rfl⟩ : syracuseStep 666893 = 250085) (by norm_num)
theorem B535853 : Blo 393766 535853 := bbase (se 3 (by rfl) ⟨100472, by rfl⟩ : syracuseStep 535853 = 200945) (by norm_num)
theorem B503101 : Blo 393766 503101 := bbase (se 3 (by rfl) ⟨94331, by rfl⟩ : syracuseStep 503101 = 188663) (by norm_num)
theorem B634213 : Blo 393766 634213 := bbase (se 4 (by rfl) ⟨59457, by rfl⟩ : syracuseStep 634213 = 118915) (by norm_num)
theorem B667021 : Blo 393766 667021 := bbase (se 3 (by rfl) ⟨125066, by rfl⟩ : syracuseStep 667021 = 250133) (by norm_num)
theorem B536005 : Blo 393766 536005 := bbase (se 4 (by rfl) ⟨50250, by rfl⟩ : syracuseStep 536005 = 100501) (by norm_num)
theorem B2010581 : Blo 393766 2010581 := bbase (se 7 (by rfl) ⟨23561, by rfl⟩ : syracuseStep 2010581 = 47123) (by norm_num)
theorem B667109 : Blo 393766 667109 := bbase (se 4 (by rfl) ⟨62541, by rfl⟩ : syracuseStep 667109 = 125083) (by norm_num)
theorem B503273 : Blo 393766 503273 := bbase (se 2 (by rfl) ⟨188727, by rfl⟩ : syracuseStep 503273 = 377455) (by norm_num)
theorem B503329 : Blo 393766 503329 := bbase (se 2 (by rfl) ⟨188748, by rfl⟩ : syracuseStep 503329 = 377497) (by norm_num)
theorem B667237 : Blo 393766 667237 := bbase (se 4 (by rfl) ⟨62553, by rfl⟩ : syracuseStep 667237 = 125107) (by norm_num)
theorem B470641 : Blo 393766 470641 := bbase (se 2 (by rfl) ⟨176490, by rfl⟩ : syracuseStep 470641 = 352981) (by norm_num)
theorem B1126021 : Blo 393766 1126021 := bbase (se 4 (by rfl) ⟨105564, by rfl⟩ : syracuseStep 1126021 = 211129) (by norm_num)
theorem B1814197 : Blo 393766 1814197 := bbase (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) (by norm_num)
theorem B667325 : Blo 393766 667325 := bbase (se 3 (by rfl) ⟨125123, by rfl⟩ : syracuseStep 667325 = 250247) (by norm_num)
theorem B536285 : Blo 393766 536285 := bbase (se 3 (by rfl) ⟨100553, by rfl⟩ : syracuseStep 536285 = 201107) (by norm_num)
theorem B3092213 : Blo 393766 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B634637 : Blo 393766 634637 := bbase (se 3 (by rfl) ⟨118994, by rfl⟩ : syracuseStep 634637 = 237989) (by norm_num)
theorem B798517 : Blo 393766 798517 := bbase (se 5 (by rfl) ⟨37430, by rfl⟩ : syracuseStep 798517 = 74861) (by norm_num)
theorem B667453 : Blo 393766 667453 := bbase (se 3 (by rfl) ⟨125147, by rfl⟩ : syracuseStep 667453 = 250295) (by norm_num)
theorem B667541 : Blo 393766 667541 := bbase (se 6 (by rfl) ⟨15645, by rfl⟩ : syracuseStep 667541 = 31291) (by norm_num)
theorem B667669 : Blo 393766 667669 := bbase (se 6 (by rfl) ⟨15648, by rfl⟩ : syracuseStep 667669 = 31297) (by norm_num)
theorem B602149 : Blo 393766 602149 := bbase (se 4 (by rfl) ⟨56451, by rfl⟩ : syracuseStep 602149 = 112903) (by norm_num)
theorem B634925 : Blo 393766 634925 := bbase (se 3 (by rfl) ⟨119048, by rfl⟩ : syracuseStep 634925 = 238097) (by norm_num)
theorem B667757 : Blo 393766 667757 := bbase (se 3 (by rfl) ⟨125204, by rfl⟩ : syracuseStep 667757 = 250409) (by norm_num)
theorem B667885 : Blo 393766 667885 := bbase (se 3 (by rfl) ⟨125228, by rfl⟩ : syracuseStep 667885 = 250457) (by norm_num)
theorem B635149 : Blo 393766 635149 := bbase (se 3 (by rfl) ⟨119090, by rfl⟩ : syracuseStep 635149 = 238181) (by norm_num)
theorem B667973 : Blo 393766 667973 := bbase (se 4 (by rfl) ⟨62622, by rfl⟩ : syracuseStep 667973 = 125245) (by norm_num)
theorem B668101 : Blo 393766 668101 := bbase (se 4 (by rfl) ⟨62634, by rfl⟩ : syracuseStep 668101 = 125269) (by norm_num)
theorem B1290725 : Blo 393766 1290725 := bbase (se 4 (by rfl) ⟨121005, by rfl⟩ : syracuseStep 1290725 = 242011) (by norm_num)
theorem B668189 : Blo 393766 668189 := bbase (se 3 (by rfl) ⟨125285, by rfl⟩ : syracuseStep 668189 = 250571) (by norm_num)
theorem B668317 : Blo 393766 668317 := bbase (se 3 (by rfl) ⟨125309, by rfl⟩ : syracuseStep 668317 = 250619) (by norm_num)
theorem B1127125 : Blo 393766 1127125 := bbase (se 7 (by rfl) ⟨13208, by rfl⟩ : syracuseStep 1127125 = 26417) (by norm_num)
theorem B2011877 : Blo 393766 2011877 := bbase (se 4 (by rfl) ⟨188613, by rfl⟩ : syracuseStep 2011877 = 377227) (by norm_num)
theorem B668405 : Blo 393766 668405 := bbase (se 5 (by rfl) ⟨31331, by rfl⟩ : syracuseStep 668405 = 62663) (by norm_num)
theorem B668533 : Blo 393766 668533 := bbase (se 5 (by rfl) ⟨31337, by rfl⟩ : syracuseStep 668533 = 62675) (by norm_num)
theorem B5714837 : Blo 393766 5714837 := bbase (se 6 (by rfl) ⟨133941, by rfl⟩ : syracuseStep 5714837 = 267883) (by norm_num)
theorem B668621 : Blo 393766 668621 := bbase (se 3 (by rfl) ⟨125366, by rfl⟩ : syracuseStep 668621 = 250733) (by norm_num)
theorem B1029077 : Blo 393766 1029077 := bbase (se 7 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 1029077 = 24119) (by norm_num)
theorem B1684469 : Blo 393766 1684469 := bbase (se 5 (by rfl) ⟨78959, by rfl⟩ : syracuseStep 1684469 = 157919) (by norm_num)
theorem B668749 : Blo 393766 668749 := bbase (se 3 (by rfl) ⟨125390, by rfl⟩ : syracuseStep 668749 = 250781) (by norm_num)
theorem B668837 : Blo 393766 668837 := bbase (se 4 (by rfl) ⟨62703, by rfl⟩ : syracuseStep 668837 = 125407) (by norm_num)
theorem B1684709 : Blo 393766 1684709 := bbase (se 4 (by rfl) ⟨157941, by rfl⟩ : syracuseStep 1684709 = 315883) (by norm_num)
theorem B1422629 : Blo 393766 1422629 := bbase (se 4 (by rfl) ⟨133371, by rfl⟩ : syracuseStep 1422629 = 266743) (by norm_num)
theorem B668965 : Blo 393766 668965 := bbase (se 4 (by rfl) ⟨62715, by rfl⟩ : syracuseStep 668965 = 125431) (by norm_num)
theorem B996725 : Blo 393766 996725 := bbase (se 5 (by rfl) ⟨46721, by rfl⟩ : syracuseStep 996725 = 93443) (by norm_num)
theorem B636277 : Blo 393766 636277 := bbase (se 5 (by rfl) ⟨29825, by rfl⟩ : syracuseStep 636277 = 59651) (by norm_num)
theorem B669053 : Blo 393766 669053 := bbase (se 3 (by rfl) ⟨125447, by rfl⟩ : syracuseStep 669053 = 250895) (by norm_num)
theorem B669181 : Blo 393766 669181 := bbase (se 3 (by rfl) ⟨125471, by rfl⟩ : syracuseStep 669181 = 250943) (by norm_num)
theorem B669269 : Blo 393766 669269 := bbase (se 8 (by rfl) ⟨3921, by rfl⟩ : syracuseStep 669269 = 7843) (by norm_num)
theorem B997069 : Blo 393766 997069 := bbase (se 3 (by rfl) ⟨186950, by rfl⟩ : syracuseStep 997069 = 373901) (by norm_num)
theorem B669397 : Blo 393766 669397 := bbase (se 7 (by rfl) ⟨7844, by rfl⟩ : syracuseStep 669397 = 15689) (by norm_num)
theorem B669485 : Blo 393766 669485 := bbase (se 3 (by rfl) ⟨125528, by rfl⟩ : syracuseStep 669485 = 251057) (by norm_num)
theorem B636725 : Blo 393766 636725 := bbase (se 5 (by rfl) ⟨29846, by rfl⟩ : syracuseStep 636725 = 59693) (by norm_num)
theorem B997181 : Blo 393766 997181 := bbase (se 3 (by rfl) ⟨186971, by rfl⟩ : syracuseStep 997181 = 373943) (by norm_num)
theorem B2537365 : Blo 393766 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B669613 : Blo 393766 669613 := bbase (se 3 (by rfl) ⟨125552, by rfl⟩ : syracuseStep 669613 = 251105) (by norm_num)
theorem B1718261 : Blo 393766 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B2013173 : Blo 393766 2013173 := bbase (se 5 (by rfl) ⟨94367, by rfl⟩ : syracuseStep 2013173 = 188735) (by norm_num)
theorem B997373 : Blo 393766 997373 := bbase (se 3 (by rfl) ⟨187007, by rfl⟩ : syracuseStep 997373 = 374015) (by norm_num)
theorem B669701 : Blo 393766 669701 := bbase (se 4 (by rfl) ⟨62784, by rfl⟩ : syracuseStep 669701 = 125569) (by norm_num)
theorem B4110421 : Blo 393766 4110421 := bbase (se 8 (by rfl) ⟨24084, by rfl⟩ : syracuseStep 4110421 = 48169) (by norm_num)
theorem B669829 : Blo 393766 669829 := bbase (se 4 (by rfl) ⟨62796, by rfl⟩ : syracuseStep 669829 = 125593) (by norm_num)
theorem B1128629 : Blo 393766 1128629 := bbase (se 5 (by rfl) ⟨52904, by rfl⟩ : syracuseStep 1128629 = 105809) (by norm_num)
theorem B407737 : Blo 393766 407737 := bbase (se 2 (by rfl) ⟨152901, by rfl⟩ : syracuseStep 407737 = 305803) (by norm_num)
theorem B669917 : Blo 393766 669917 := bbase (se 3 (by rfl) ⟨125609, by rfl⟩ : syracuseStep 669917 = 251219) (by norm_num)
theorem B899381 : Blo 393766 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B997717 : Blo 393766 997717 := bbase (se 10 (by rfl) ⟨1461, by rfl⟩ : syracuseStep 997717 = 2923) (by norm_num)
theorem B670045 : Blo 393766 670045 := bbase (se 3 (by rfl) ⟨125633, by rfl⟩ : syracuseStep 670045 = 251267) (by norm_num)
theorem B506261 : Blo 393766 506261 := bbase (se 6 (by rfl) ⟨11865, by rfl⟩ : syracuseStep 506261 = 23731) (by norm_num)
theorem B2242997 : Blo 393766 2242997 := bbase (se 5 (by rfl) ⟨105140, by rfl⟩ : syracuseStep 2242997 = 210281) (by norm_num)
theorem B670133 : Blo 393766 670133 := bbase (se 5 (by rfl) ⟨31412, by rfl⟩ : syracuseStep 670133 = 62825) (by norm_num)
theorem B997829 : Blo 393766 997829 := bbase (se 4 (by rfl) ⟨93546, by rfl⟩ : syracuseStep 997829 = 187093) (by norm_num)
theorem B670261 : Blo 393766 670261 := bbase (se 5 (by rfl) ⟨31418, by rfl⟩ : syracuseStep 670261 = 62837) (by norm_num)
theorem B998021 : Blo 393766 998021 := bbase (se 4 (by rfl) ⟨93564, by rfl⟩ : syracuseStep 998021 = 187129) (by norm_num)
theorem B670349 : Blo 393766 670349 := bbase (se 3 (by rfl) ⟨125690, by rfl⟩ : syracuseStep 670349 = 251381) (by norm_num)
theorem B670477 : Blo 393766 670477 := bbase (se 3 (by rfl) ⟨125714, by rfl⟩ : syracuseStep 670477 = 251429) (by norm_num)
theorem B1424213 : Blo 393766 1424213 := bbase (se 9 (by rfl) ⟨4172, by rfl⟩ : syracuseStep 1424213 = 8345) (by norm_num)
theorem B4078421 : Blo 393766 4078421 := bbase (se 9 (by rfl) ⟨11948, by rfl⟩ : syracuseStep 4078421 = 23897) (by norm_num)
theorem B670565 : Blo 393766 670565 := bbase (se 4 (by rfl) ⟨62865, by rfl⟩ : syracuseStep 670565 = 125731) (by norm_num)
theorem B474017 : Blo 393766 474017 := bbase (se 2 (by rfl) ⟨177756, by rfl⟩ : syracuseStep 474017 = 355513) (by norm_num)
theorem B998365 : Blo 393766 998365 := bbase (se 3 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 998365 = 374387) (by norm_num)
theorem B670693 : Blo 393766 670693 := bbase (se 4 (by rfl) ⟨62877, by rfl⟩ : syracuseStep 670693 = 125755) (by norm_num)
theorem B670781 : Blo 393766 670781 := bbase (se 3 (by rfl) ⟨125771, by rfl⟩ : syracuseStep 670781 = 251543) (by norm_num)
theorem B998477 : Blo 393766 998477 := bbase (se 3 (by rfl) ⟨187214, by rfl⟩ : syracuseStep 998477 = 374429) (by norm_num)
theorem B965773 : Blo 393766 965773 := bbase (se 3 (by rfl) ⟨181082, by rfl⟩ : syracuseStep 965773 = 362165) (by norm_num)
theorem B670909 : Blo 393766 670909 := bbase (se 3 (by rfl) ⟨125795, by rfl⟩ : syracuseStep 670909 = 251591) (by norm_num)
theorem B474349 : Blo 393766 474349 := bbase (se 3 (by rfl) ⟨88940, by rfl⟩ : syracuseStep 474349 = 177881) (by norm_num)
theorem B998669 : Blo 393766 998669 := bbase (se 3 (by rfl) ⟨187250, by rfl⟩ : syracuseStep 998669 = 374501) (by norm_num)
theorem B670997 : Blo 393766 670997 := bbase (se 6 (by rfl) ⟨15726, by rfl⟩ : syracuseStep 670997 = 31453) (by norm_num)
theorem B539965 : Blo 393766 539965 := bbase (se 3 (by rfl) ⟨101243, by rfl⟩ : syracuseStep 539965 = 202487) (by norm_num)
theorem B671125 : Blo 393766 671125 := bbase (se 6 (by rfl) ⟨15729, by rfl⟩ : syracuseStep 671125 = 31459) (by norm_num)
theorem B1686997 : Blo 393766 1686997 := bbase (se 7 (by rfl) ⟨19769, by rfl⟩ : syracuseStep 1686997 = 39539) (by norm_num)
theorem B671213 : Blo 393766 671213 := bbase (se 3 (by rfl) ⟨125852, by rfl⟩ : syracuseStep 671213 = 251705) (by norm_num)
theorem B999013 : Blo 393766 999013 := bbase (se 4 (by rfl) ⟨93657, by rfl⟩ : syracuseStep 999013 = 187315) (by norm_num)
theorem B573053 : Blo 393766 573053 := bbase (se 3 (by rfl) ⟨107447, by rfl⟩ : syracuseStep 573053 = 214895) (by norm_num)
theorem B999125 : Blo 393766 999125 := bbase (se 7 (by rfl) ⟨11708, by rfl⟩ : syracuseStep 999125 = 23417) (by norm_num)
theorem B1130213 : Blo 393766 1130213 := bbase (se 4 (by rfl) ⟨105957, by rfl⟩ : syracuseStep 1130213 = 211915) (by norm_num)
theorem B802541 : Blo 393766 802541 := bbase (se 3 (by rfl) ⟨150476, by rfl⟩ : syracuseStep 802541 = 300953) (by norm_num)
theorem B507709 : Blo 393766 507709 := bbase (se 3 (by rfl) ⟨95195, by rfl⟩ : syracuseStep 507709 = 190391) (by norm_num)
theorem B2998133 : Blo 393766 2998133 := bbase (se 5 (by rfl) ⟨140537, by rfl⟩ : syracuseStep 2998133 = 281075) (by norm_num)
theorem B999317 : Blo 393766 999317 := bbase (se 6 (by rfl) ⟨23421, by rfl⟩ : syracuseStep 999317 = 46843) (by norm_num)
theorem B475237 : Blo 393766 475237 := bbase (se 4 (by rfl) ⟨44553, by rfl⟩ : syracuseStep 475237 = 89107) (by norm_num)
theorem B999661 : Blo 393766 999661 := bbase (se 3 (by rfl) ⟨187436, by rfl⟩ : syracuseStep 999661 = 374873) (by norm_num)
theorem B999773 : Blo 393766 999773 := bbase (se 3 (by rfl) ⟨187457, by rfl⟩ : syracuseStep 999773 = 374915) (by norm_num)
theorem B1130885 : Blo 393766 1130885 := bbase (se 4 (by rfl) ⟨106020, by rfl⟩ : syracuseStep 1130885 = 212041) (by norm_num)
theorem B999965 : Blo 393766 999965 := bbase (se 3 (by rfl) ⟨187493, by rfl⟩ : syracuseStep 999965 = 374987) (by norm_num)
theorem B442993 : Blo 393766 442993 := bbase (se 2 (by rfl) ⟨166122, by rfl⟩ : syracuseStep 442993 = 332245) (by norm_num)
theorem B443029 : Blo 393766 443029 := bbase (se 6 (by rfl) ⟨10383, by rfl⟩ : syracuseStep 443029 = 20767) (by norm_num)
theorem B443065 : Blo 393766 443065 := bbase (se 2 (by rfl) ⟨166149, by rfl⟩ : syracuseStep 443065 = 332299) (by norm_num)
theorem B443101 : Blo 393766 443101 := bbase (se 3 (by rfl) ⟨83081, by rfl⟩ : syracuseStep 443101 = 166163) (by norm_num)
theorem B443137 : Blo 393766 443137 := bbase (se 2 (by rfl) ⟨166176, by rfl⟩ : syracuseStep 443137 = 332353) (by norm_num)
theorem B443173 : Blo 393766 443173 := bbase (se 4 (by rfl) ⟨41547, by rfl⟩ : syracuseStep 443173 = 83095) (by norm_num)
theorem B1131317 : Blo 393766 1131317 := bbase (se 5 (by rfl) ⟨53030, by rfl⟩ : syracuseStep 1131317 = 106061) (by norm_num)
theorem B1262405 : Blo 393766 1262405 := bbase (se 4 (by rfl) ⟨118350, by rfl⟩ : syracuseStep 1262405 = 236701) (by norm_num)
theorem B443209 : Blo 393766 443209 := bbase (se 2 (by rfl) ⟨166203, by rfl⟩ : syracuseStep 443209 = 332407) (by norm_num)
theorem B443245 : Blo 393766 443245 := bbase (se 3 (by rfl) ⟨83108, by rfl⟩ : syracuseStep 443245 = 166217) (by norm_num)
theorem B1000309 : Blo 393766 1000309 := bbase (se 5 (by rfl) ⟨46889, by rfl⟩ : syracuseStep 1000309 = 93779) (by norm_num)
theorem B443281 : Blo 393766 443281 := bbase (se 2 (by rfl) ⟨166230, by rfl⟩ : syracuseStep 443281 = 332461) (by norm_num)
theorem B1688485 : Blo 393766 1688485 := bbase (se 4 (by rfl) ⟨158295, by rfl⟩ : syracuseStep 1688485 = 316591) (by norm_num)
theorem B443317 : Blo 393766 443317 := bbase (se 5 (by rfl) ⟨20780, by rfl⟩ : syracuseStep 443317 = 41561) (by norm_num)
theorem B1688501 : Blo 393766 1688501 := bbase (se 5 (by rfl) ⟨79148, by rfl⟩ : syracuseStep 1688501 = 158297) (by norm_num)
theorem B443353 : Blo 393766 443353 := bbase (se 2 (by rfl) ⟨166257, by rfl⟩ : syracuseStep 443353 = 332515) (by norm_num)
theorem B1000421 : Blo 393766 1000421 := bbase (se 4 (by rfl) ⟨93789, by rfl⟩ : syracuseStep 1000421 = 187579) (by norm_num)
theorem B443389 : Blo 393766 443389 := bbase (se 3 (by rfl) ⟨83135, by rfl⟩ : syracuseStep 443389 = 166271) (by norm_num)
theorem B443425 : Blo 393766 443425 := bbase (se 2 (by rfl) ⟨166284, by rfl⟩ : syracuseStep 443425 = 332569) (by norm_num)
theorem B443461 : Blo 393766 443461 := bbase (se 4 (by rfl) ⟨41574, by rfl⟩ : syracuseStep 443461 = 83149) (by norm_num)
theorem B803909 : Blo 393766 803909 := bbase (se 4 (by rfl) ⟨75366, by rfl⟩ : syracuseStep 803909 = 150733) (by norm_num)
theorem B443497 : Blo 393766 443497 := bbase (se 2 (by rfl) ⟨166311, by rfl⟩ : syracuseStep 443497 = 332623) (by norm_num)
theorem B476285 : Blo 393766 476285 := bbase (se 3 (by rfl) ⟨89303, by rfl⟩ : syracuseStep 476285 = 178607) (by norm_num)
theorem B443533 : Blo 393766 443533 := bbase (se 3 (by rfl) ⟨83162, by rfl⟩ : syracuseStep 443533 = 166325) (by norm_num)
theorem B1000613 : Blo 393766 1000613 := bbase (se 4 (by rfl) ⟨93807, by rfl⟩ : syracuseStep 1000613 = 187615) (by norm_num)
theorem B443569 : Blo 393766 443569 := bbase (se 2 (by rfl) ⟨166338, by rfl⟩ : syracuseStep 443569 = 332677) (by norm_num)
theorem B443605 : Blo 393766 443605 := bbase (se 7 (by rfl) ⟨5198, by rfl⟩ : syracuseStep 443605 = 10397) (by norm_num)
theorem B443641 : Blo 393766 443641 := bbase (se 2 (by rfl) ⟨166365, by rfl⟩ : syracuseStep 443641 = 332731) (by norm_num)
theorem B443677 : Blo 393766 443677 := bbase (se 3 (by rfl) ⟨83189, by rfl⟩ : syracuseStep 443677 = 166379) (by norm_num)
theorem B443713 : Blo 393766 443713 := bbase (se 2 (by rfl) ⟨166392, by rfl⟩ : syracuseStep 443713 = 332785) (by norm_num)
theorem B443749 : Blo 393766 443749 := bbase (se 4 (by rfl) ⟨41601, by rfl⟩ : syracuseStep 443749 = 83203) (by norm_num)
theorem B443785 : Blo 393766 443785 := bbase (se 2 (by rfl) ⟨166419, by rfl⟩ : syracuseStep 443785 = 332839) (by norm_num)
theorem B443821 : Blo 393766 443821 := bbase (se 3 (by rfl) ⟨83216, by rfl⟩ : syracuseStep 443821 = 166433) (by norm_num)
theorem B443857 : Blo 393766 443857 := bbase (se 2 (by rfl) ⟨166446, by rfl⟩ : syracuseStep 443857 = 332893) (by norm_num)
theorem B476641 : Blo 393766 476641 := bbase (se 2 (by rfl) ⟨178740, by rfl⟩ : syracuseStep 476641 = 357481) (by norm_num)
theorem B443893 : Blo 393766 443893 := bbase (se 5 (by rfl) ⟨20807, by rfl⟩ : syracuseStep 443893 = 41615) (by norm_num)
theorem B1000957 : Blo 393766 1000957 := bbase (se 3 (by rfl) ⟨187679, by rfl⟩ : syracuseStep 1000957 = 375359) (by norm_num)
theorem B1066517 : Blo 393766 1066517 := bbase (se 6 (by rfl) ⟨24996, by rfl⟩ : syracuseStep 1066517 = 49993) (by norm_num)
theorem B443929 : Blo 393766 443929 := bbase (se 2 (by rfl) ⟨166473, by rfl⟩ : syracuseStep 443929 = 332947) (by norm_num)
theorem B1132069 : Blo 393766 1132069 := bbase (se 4 (by rfl) ⟨106131, by rfl⟩ : syracuseStep 1132069 = 212263) (by norm_num)
theorem B443965 : Blo 393766 443965 := bbase (se 3 (by rfl) ⟨83243, by rfl⟩ : syracuseStep 443965 = 166487) (by norm_num)
theorem B444001 : Blo 393766 444001 := bbase (se 2 (by rfl) ⟨166500, by rfl⟩ : syracuseStep 444001 = 333001) (by norm_num)
theorem B1001069 : Blo 393766 1001069 := bbase (se 3 (by rfl) ⟨187700, by rfl⟩ : syracuseStep 1001069 = 375401) (by norm_num)
theorem B444037 : Blo 393766 444037 := bbase (se 4 (by rfl) ⟨41628, by rfl⟩ : syracuseStep 444037 = 83257) (by norm_num)
theorem B476833 : Blo 393766 476833 := bbase (se 2 (by rfl) ⟨178812, by rfl⟩ : syracuseStep 476833 = 357625) (by norm_num)
theorem B444073 : Blo 393766 444073 := bbase (se 2 (by rfl) ⟨166527, by rfl⟩ : syracuseStep 444073 = 333055) (by norm_num)
theorem B444109 : Blo 393766 444109 := bbase (se 3 (by rfl) ⟨83270, by rfl⟩ : syracuseStep 444109 = 166541) (by norm_num)
theorem B444145 : Blo 393766 444145 := bbase (se 2 (by rfl) ⟨166554, by rfl⟩ : syracuseStep 444145 = 333109) (by norm_num)
theorem B3786517 : Blo 393766 3786517 := bbase (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) (by norm_num)
theorem B444181 : Blo 393766 444181 := bbase (se 6 (by rfl) ⟨10410, by rfl⟩ : syracuseStep 444181 = 20821) (by norm_num)
theorem B1001261 : Blo 393766 1001261 := bbase (se 3 (by rfl) ⟨187736, by rfl⟩ : syracuseStep 1001261 = 375473) (by norm_num)
theorem B476977 : Blo 393766 476977 := bbase (se 2 (by rfl) ⟨178866, by rfl⟩ : syracuseStep 476977 = 357733) (by norm_num)
theorem B444217 : Blo 393766 444217 := bbase (se 2 (by rfl) ⟨166581, by rfl⟩ : syracuseStep 444217 = 333163) (by norm_num)
theorem B444253 : Blo 393766 444253 := bbase (se 3 (by rfl) ⟨83297, by rfl⟩ : syracuseStep 444253 = 166595) (by norm_num)
theorem B444289 : Blo 393766 444289 := bbase (se 2 (by rfl) ⟨166608, by rfl⟩ : syracuseStep 444289 = 333217) (by norm_num)
theorem B444325 : Blo 393766 444325 := bbase (se 4 (by rfl) ⟨41655, by rfl⟩ : syracuseStep 444325 = 83311) (by norm_num)
theorem B1066949 : Blo 393766 1066949 := bbase (se 4 (by rfl) ⟨100026, by rfl⟩ : syracuseStep 1066949 = 200053) (by norm_num)
theorem B444361 : Blo 393766 444361 := bbase (se 2 (by rfl) ⟨166635, by rfl⟩ : syracuseStep 444361 = 333271) (by norm_num)
theorem B444397 : Blo 393766 444397 := bbase (se 3 (by rfl) ⟨83324, by rfl⟩ : syracuseStep 444397 = 166649) (by norm_num)
theorem B444433 : Blo 393766 444433 := bbase (se 2 (by rfl) ⟨166662, by rfl⟩ : syracuseStep 444433 = 333325) (by norm_num)
theorem B444469 : Blo 393766 444469 := bbase (se 5 (by rfl) ⟨20834, by rfl⟩ : syracuseStep 444469 = 41669) (by norm_num)
theorem B1198165 : Blo 393766 1198165 := bbase (se 8 (by rfl) ⟨7020, by rfl⟩ : syracuseStep 1198165 = 14041) (by norm_num)
theorem B444505 : Blo 393766 444505 := bbase (se 2 (by rfl) ⟨166689, by rfl⟩ : syracuseStep 444505 = 333379) (by norm_num)
theorem B1427557 : Blo 393766 1427557 := bbase (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) (by norm_num)
theorem B444541 : Blo 393766 444541 := bbase (se 3 (by rfl) ⟨83351, by rfl⟩ : syracuseStep 444541 = 166703) (by norm_num)
theorem B1001605 : Blo 393766 1001605 := bbase (se 4 (by rfl) ⟨93900, by rfl⟩ : syracuseStep 1001605 = 187801) (by norm_num)
theorem B444577 : Blo 393766 444577 := bbase (se 2 (by rfl) ⟨166716, by rfl⟩ : syracuseStep 444577 = 333433) (by norm_num)
theorem B1329317 : Blo 393766 1329317 := bbase (se 4 (by rfl) ⟨124623, by rfl⟩ : syracuseStep 1329317 = 249247) (by norm_num)
theorem B444613 : Blo 393766 444613 := bbase (se 4 (by rfl) ⟨41682, by rfl⟩ : syracuseStep 444613 = 83365) (by norm_num)
theorem B444649 : Blo 393766 444649 := bbase (se 2 (by rfl) ⟨166743, by rfl⟩ : syracuseStep 444649 = 333487) (by norm_num)
theorem B1001717 : Blo 393766 1001717 := bbase (se 5 (by rfl) ⟨46955, by rfl⟩ : syracuseStep 1001717 = 93911) (by norm_num)
theorem B1427701 : Blo 393766 1427701 := bbase (se 5 (by rfl) ⟨66923, by rfl⟩ : syracuseStep 1427701 = 133847) (by norm_num)
theorem B444685 : Blo 393766 444685 := bbase (se 3 (by rfl) ⟨83378, by rfl⟩ : syracuseStep 444685 = 166757) (by norm_num)
theorem B444721 : Blo 393766 444721 := bbase (se 2 (by rfl) ⟨166770, by rfl⟩ : syracuseStep 444721 = 333541) (by norm_num)
theorem B444757 : Blo 393766 444757 := bbase (se 10 (by rfl) ⟨651, by rfl⟩ : syracuseStep 444757 = 1303) (by norm_num)
theorem B444793 : Blo 393766 444793 := bbase (se 2 (by rfl) ⟨166797, by rfl⟩ : syracuseStep 444793 = 333595) (by norm_num)
theorem B1198469 : Blo 393766 1198469 := bbase (se 4 (by rfl) ⟨112356, by rfl⟩ : syracuseStep 1198469 = 224713) (by norm_num)
theorem B444829 : Blo 393766 444829 := bbase (se 3 (by rfl) ⟨83405, by rfl⟩ : syracuseStep 444829 = 166811) (by norm_num)
theorem B1001909 : Blo 393766 1001909 := bbase (se 5 (by rfl) ⟨46964, by rfl⟩ : syracuseStep 1001909 = 93929) (by norm_num)
theorem B2574773 : Blo 393766 2574773 := bbase (se 5 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 2574773 = 241385) (by norm_num)
theorem B444865 : Blo 393766 444865 := bbase (se 2 (by rfl) ⟨166824, by rfl⟩ : syracuseStep 444865 = 333649) (by norm_num)
theorem B444901 : Blo 393766 444901 := bbase (se 4 (by rfl) ⟨41709, by rfl⟩ : syracuseStep 444901 = 83419) (by norm_num)
theorem B444937 : Blo 393766 444937 := bbase (se 2 (by rfl) ⟨166851, by rfl⟩ : syracuseStep 444937 = 333703) (by norm_num)
theorem B444973 : Blo 393766 444973 := bbase (se 3 (by rfl) ⟨83432, by rfl⟩ : syracuseStep 444973 = 166865) (by norm_num)
theorem B445009 : Blo 393766 445009 := bbase (se 2 (by rfl) ⟨166878, by rfl⟩ : syracuseStep 445009 = 333757) (by norm_num)
theorem B1329749 : Blo 393766 1329749 := bbase (se 8 (by rfl) ⟨7791, by rfl⟩ : syracuseStep 1329749 = 15583) (by norm_num)
theorem B445045 : Blo 393766 445045 := bbase (se 5 (by rfl) ⟨20861, by rfl⟩ : syracuseStep 445045 = 41723) (by norm_num)
theorem B445081 : Blo 393766 445081 := bbase (se 2 (by rfl) ⟨166905, by rfl⟩ : syracuseStep 445081 = 333811) (by norm_num)
theorem B445117 : Blo 393766 445117 := bbase (se 3 (by rfl) ⟨83459, by rfl⟩ : syracuseStep 445117 = 166919) (by norm_num)
theorem B805565 : Blo 393766 805565 := bbase (se 3 (by rfl) ⟨151043, by rfl⟩ : syracuseStep 805565 = 302087) (by norm_num)
theorem B445153 : Blo 393766 445153 := bbase (se 2 (by rfl) ⟨166932, by rfl⟩ : syracuseStep 445153 = 333865) (by norm_num)
theorem B445189 : Blo 393766 445189 := bbase (se 4 (by rfl) ⟨41736, by rfl⟩ : syracuseStep 445189 = 83473) (by norm_num)
theorem B1002253 : Blo 393766 1002253 := bbase (se 3 (by rfl) ⟨187922, by rfl⟩ : syracuseStep 1002253 = 375845) (by norm_num)
theorem B445225 : Blo 393766 445225 := bbase (se 2 (by rfl) ⟨166959, by rfl⟩ : syracuseStep 445225 = 333919) (by norm_num)
theorem B445261 : Blo 393766 445261 := bbase (se 3 (by rfl) ⟨83486, by rfl⟩ : syracuseStep 445261 = 166973) (by norm_num)
theorem B445297 : Blo 393766 445297 := bbase (se 2 (by rfl) ⟨166986, by rfl⟩ : syracuseStep 445297 = 333973) (by norm_num)
theorem B1002365 : Blo 393766 1002365 := bbase (se 3 (by rfl) ⟨187943, by rfl⟩ : syracuseStep 1002365 = 375887) (by norm_num)
theorem B445333 : Blo 393766 445333 := bbase (se 6 (by rfl) ⟨10437, by rfl⟩ : syracuseStep 445333 = 20875) (by norm_num)
theorem B445369 : Blo 393766 445369 := bbase (se 2 (by rfl) ⟨167013, by rfl⟩ : syracuseStep 445369 = 334027) (by norm_num)
theorem B445405 : Blo 393766 445405 := bbase (se 3 (by rfl) ⟨83513, by rfl⟩ : syracuseStep 445405 = 167027) (by norm_num)
theorem B445441 : Blo 393766 445441 := bbase (se 2 (by rfl) ⟨167040, by rfl⟩ : syracuseStep 445441 = 334081) (by norm_num)
theorem B1330181 : Blo 393766 1330181 := bbase (se 4 (by rfl) ⟨124704, by rfl⟩ : syracuseStep 1330181 = 249409) (by norm_num)
theorem B445477 : Blo 393766 445477 := bbase (se 4 (by rfl) ⟨41763, by rfl⟩ : syracuseStep 445477 = 83527) (by norm_num)
theorem B1002557 : Blo 393766 1002557 := bbase (se 3 (by rfl) ⟨187979, by rfl⟩ : syracuseStep 1002557 = 375959) (by norm_num)
theorem B445513 : Blo 393766 445513 := bbase (se 2 (by rfl) ⟨167067, by rfl⟩ : syracuseStep 445513 = 334135) (by norm_num)
theorem B445549 : Blo 393766 445549 := bbase (se 3 (by rfl) ⟨83540, by rfl⟩ : syracuseStep 445549 = 167081) (by norm_num)
theorem B1690757 : Blo 393766 1690757 := bbase (se 4 (by rfl) ⟨158508, by rfl⟩ : syracuseStep 1690757 = 317017) (by norm_num)
theorem B445585 : Blo 393766 445585 := bbase (se 2 (by rfl) ⟨167094, by rfl⟩ : syracuseStep 445585 = 334189) (by norm_num)
theorem B445621 : Blo 393766 445621 := bbase (se 5 (by rfl) ⟨20888, by rfl⟩ : syracuseStep 445621 = 41777) (by norm_num)
theorem B445657 : Blo 393766 445657 := bbase (se 2 (by rfl) ⟨167121, by rfl⟩ : syracuseStep 445657 = 334243) (by norm_num)
theorem B445693 : Blo 393766 445693 := bbase (se 3 (by rfl) ⟨83567, by rfl⟩ : syracuseStep 445693 = 167135) (by norm_num)
theorem B445729 : Blo 393766 445729 := bbase (se 2 (by rfl) ⟨167148, by rfl⟩ : syracuseStep 445729 = 334297) (by norm_num)
theorem B2149685 : Blo 393766 2149685 := bbase (se 5 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 2149685 = 201533) (by norm_num)
theorem B445765 : Blo 393766 445765 := bbase (se 4 (by rfl) ⟨41790, by rfl⟩ : syracuseStep 445765 = 83581) (by norm_num)
theorem B445801 : Blo 393766 445801 := bbase (se 2 (by rfl) ⟨167175, by rfl⟩ : syracuseStep 445801 = 334351) (by norm_num)
theorem B445837 : Blo 393766 445837 := bbase (se 3 (by rfl) ⟨83594, by rfl⟩ : syracuseStep 445837 = 167189) (by norm_num)
theorem B1002901 : Blo 393766 1002901 := bbase (se 6 (by rfl) ⟨23505, by rfl⟩ : syracuseStep 1002901 = 47011) (by norm_num)
theorem B445873 : Blo 393766 445873 := bbase (se 2 (by rfl) ⟨167202, by rfl⟩ : syracuseStep 445873 = 334405) (by norm_num)
theorem B1330613 : Blo 393766 1330613 := bbase (se 5 (by rfl) ⟨62372, by rfl⟩ : syracuseStep 1330613 = 124745) (by norm_num)
theorem B445909 : Blo 393766 445909 := bbase (se 7 (by rfl) ⟨5225, by rfl⟩ : syracuseStep 445909 = 10451) (by norm_num)
theorem B445945 : Blo 393766 445945 := bbase (se 2 (by rfl) ⟨167229, by rfl⟩ : syracuseStep 445945 = 334459) (by norm_num)
theorem B1003013 : Blo 393766 1003013 := bbase (se 4 (by rfl) ⟨94032, by rfl⟩ : syracuseStep 1003013 = 188065) (by norm_num)
theorem B445981 : Blo 393766 445981 := bbase (se 3 (by rfl) ⟨83621, by rfl⟩ : syracuseStep 445981 = 167243) (by norm_num)
theorem B446017 : Blo 393766 446017 := bbase (se 2 (by rfl) ⟨167256, by rfl⟩ : syracuseStep 446017 = 334513) (by norm_num)
theorem B446053 : Blo 393766 446053 := bbase (se 4 (by rfl) ⟨41817, by rfl⟩ : syracuseStep 446053 = 83635) (by norm_num)
theorem B446089 : Blo 393766 446089 := bbase (se 2 (by rfl) ⟨167283, by rfl⟩ : syracuseStep 446089 = 334567) (by norm_num)
theorem B446125 : Blo 393766 446125 := bbase (se 3 (by rfl) ⟨83648, by rfl⟩ : syracuseStep 446125 = 167297) (by norm_num)
theorem B1003205 : Blo 393766 1003205 := bbase (se 4 (by rfl) ⟨94050, by rfl⟩ : syracuseStep 1003205 = 188101) (by norm_num)
theorem B446161 : Blo 393766 446161 := bbase (se 2 (by rfl) ⟨167310, by rfl⟩ : syracuseStep 446161 = 334621) (by norm_num)
theorem B446197 : Blo 393766 446197 := bbase (se 5 (by rfl) ⟨20915, by rfl⟩ : syracuseStep 446197 = 41831) (by norm_num)
theorem B3395317 : Blo 393766 3395317 := bbase (se 5 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 3395317 = 318311) (by norm_num)
theorem B446233 : Blo 393766 446233 := bbase (se 2 (by rfl) ⟨167337, by rfl⟩ : syracuseStep 446233 = 334675) (by norm_num)
theorem B2543413 : Blo 393766 2543413 := bbase (se 5 (by rfl) ⟨119222, by rfl⟩ : syracuseStep 2543413 = 238445) (by norm_num)
theorem B446269 : Blo 393766 446269 := bbase (se 3 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 446269 = 167351) (by norm_num)
theorem B446305 : Blo 393766 446305 := bbase (se 2 (by rfl) ⟨167364, by rfl⟩ : syracuseStep 446305 = 334729) (by norm_num)
theorem B1331045 : Blo 393766 1331045 := bbase (se 4 (by rfl) ⟨124785, by rfl⟩ : syracuseStep 1331045 = 249571) (by norm_num)
theorem B1560421 : Blo 393766 1560421 := bbase (se 4 (by rfl) ⟨146289, by rfl⟩ : syracuseStep 1560421 = 292579) (by norm_num)
theorem B446341 : Blo 393766 446341 := bbase (se 4 (by rfl) ⟨41844, by rfl⟩ : syracuseStep 446341 = 83689) (by norm_num)
theorem B446377 : Blo 393766 446377 := bbase (se 2 (by rfl) ⟨167391, by rfl⟩ : syracuseStep 446377 = 334783) (by norm_num)
theorem B446413 : Blo 393766 446413 := bbase (se 3 (by rfl) ⟨83702, by rfl⟩ : syracuseStep 446413 = 167405) (by norm_num)
theorem B446449 : Blo 393766 446449 := bbase (se 2 (by rfl) ⟨167418, by rfl⟩ : syracuseStep 446449 = 334837) (by norm_num)
theorem B2543605 : Blo 393766 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B446485 : Blo 393766 446485 := bbase (se 6 (by rfl) ⟨10464, by rfl⟩ : syracuseStep 446485 = 20929) (by norm_num)
theorem B1003549 : Blo 393766 1003549 := bbase (se 3 (by rfl) ⟨188165, by rfl⟩ : syracuseStep 1003549 = 376331) (by norm_num)
theorem B577573 : Blo 393766 577573 := bbase (se 4 (by rfl) ⟨54147, by rfl⟩ : syracuseStep 577573 = 108295) (by norm_num)
theorem B446521 : Blo 393766 446521 := bbase (se 2 (by rfl) ⟨167445, by rfl⟩ : syracuseStep 446521 = 334891) (by norm_num)
theorem B446557 : Blo 393766 446557 := bbase (se 3 (by rfl) ⟨83729, by rfl⟩ : syracuseStep 446557 = 167459) (by norm_num)
theorem B446593 : Blo 393766 446593 := bbase (se 2 (by rfl) ⟨167472, by rfl⟩ : syracuseStep 446593 = 334945) (by norm_num)
theorem B1003661 : Blo 393766 1003661 := bbase (se 3 (by rfl) ⟨188186, by rfl⟩ : syracuseStep 1003661 = 376373) (by norm_num)
theorem B1265813 : Blo 393766 1265813 := bbase (se 6 (by rfl) ⟨29667, by rfl⟩ : syracuseStep 1265813 = 59335) (by norm_num)
theorem B446629 : Blo 393766 446629 := bbase (se 4 (by rfl) ⟨41871, by rfl⟩ : syracuseStep 446629 = 83743) (by norm_num)
theorem B446665 : Blo 393766 446665 := bbase (se 2 (by rfl) ⟨167499, by rfl⟩ : syracuseStep 446665 = 334999) (by norm_num)
theorem B446701 : Blo 393766 446701 := bbase (se 3 (by rfl) ⟨83756, by rfl⟩ : syracuseStep 446701 = 167513) (by norm_num)
theorem B446737 : Blo 393766 446737 := bbase (se 2 (by rfl) ⟨167526, by rfl⟩ : syracuseStep 446737 = 335053) (by norm_num)
theorem B1331477 : Blo 393766 1331477 := bbase (se 6 (by rfl) ⟨31206, by rfl⟩ : syracuseStep 1331477 = 62413) (by norm_num)
theorem B446773 : Blo 393766 446773 := bbase (se 5 (by rfl) ⟨20942, by rfl⟩ : syracuseStep 446773 = 41885) (by norm_num)
theorem B1003853 : Blo 393766 1003853 := bbase (se 3 (by rfl) ⟨188222, by rfl⟩ : syracuseStep 1003853 = 376445) (by norm_num)
theorem B446809 : Blo 393766 446809 := bbase (se 2 (by rfl) ⟨167553, by rfl⟩ : syracuseStep 446809 = 335107) (by norm_num)
theorem B446845 : Blo 393766 446845 := bbase (se 3 (by rfl) ⟨83783, by rfl⟩ : syracuseStep 446845 = 167567) (by norm_num)
theorem B446881 : Blo 393766 446881 := bbase (se 2 (by rfl) ⟨167580, by rfl⟩ : syracuseStep 446881 = 335161) (by norm_num)
theorem B446917 : Blo 393766 446917 := bbase (se 4 (by rfl) ⟨41898, by rfl⟩ : syracuseStep 446917 = 83797) (by norm_num)
theorem B446953 : Blo 393766 446953 := bbase (se 2 (by rfl) ⟨167607, by rfl⟩ : syracuseStep 446953 = 335215) (by norm_num)
theorem B446989 : Blo 393766 446989 := bbase (se 3 (by rfl) ⟨83810, by rfl⟩ : syracuseStep 446989 = 167621) (by norm_num)
theorem B676397 : Blo 393766 676397 := bbase (se 3 (by rfl) ⟨126824, by rfl⟩ : syracuseStep 676397 = 253649) (by norm_num)
theorem B447025 : Blo 393766 447025 := bbase (se 2 (by rfl) ⟨167634, by rfl⟩ : syracuseStep 447025 = 335269) (by norm_num)
theorem B1921589 : Blo 393766 1921589 := bbase (se 5 (by rfl) ⟨90074, by rfl⟩ : syracuseStep 1921589 = 180149) (by norm_num)
theorem B1462853 : Blo 393766 1462853 := bbase (se 4 (by rfl) ⟨137142, by rfl⟩ : syracuseStep 1462853 = 274285) (by norm_num)
theorem B447061 : Blo 393766 447061 := bbase (se 8 (by rfl) ⟨2619, by rfl⟩ : syracuseStep 447061 = 5239) (by norm_num)
theorem B447097 : Blo 393766 447097 := bbase (se 2 (by rfl) ⟨167661, by rfl⟩ : syracuseStep 447097 = 335323) (by norm_num)
theorem B447133 : Blo 393766 447133 := bbase (se 3 (by rfl) ⟨83837, by rfl⟩ : syracuseStep 447133 = 167675) (by norm_num)
theorem B1004197 : Blo 393766 1004197 := bbase (se 4 (by rfl) ⟨94143, by rfl⟩ : syracuseStep 1004197 = 188287) (by norm_num)
theorem B447169 : Blo 393766 447169 := bbase (se 2 (by rfl) ⟨167688, by rfl⟩ : syracuseStep 447169 = 335377) (by norm_num)
theorem B1331909 : Blo 393766 1331909 := bbase (se 4 (by rfl) ⟨124866, by rfl⟩ : syracuseStep 1331909 = 249733) (by norm_num)
theorem B447205 : Blo 393766 447205 := bbase (se 4 (by rfl) ⟨41925, by rfl⟩ : syracuseStep 447205 = 83851) (by norm_num)
theorem B1200901 : Blo 393766 1200901 := bbase (se 4 (by rfl) ⟨112584, by rfl⟩ : syracuseStep 1200901 = 225169) (by norm_num)
theorem B447241 : Blo 393766 447241 := bbase (se 2 (by rfl) ⟨167715, by rfl⟩ : syracuseStep 447241 = 335431) (by norm_num)
theorem B1004309 : Blo 393766 1004309 := bbase (se 6 (by rfl) ⟨23538, by rfl⟩ : syracuseStep 1004309 = 47077) (by norm_num)
theorem B447277 : Blo 393766 447277 := bbase (se 3 (by rfl) ⟨83864, by rfl⟩ : syracuseStep 447277 = 167729) (by norm_num)
theorem B447313 : Blo 393766 447313 := bbase (se 2 (by rfl) ⟨167742, by rfl⟩ : syracuseStep 447313 = 335485) (by norm_num)
theorem B447349 : Blo 393766 447349 := bbase (se 5 (by rfl) ⟨20969, by rfl⟩ : syracuseStep 447349 = 41939) (by norm_num)
theorem B447385 : Blo 393766 447385 := bbase (se 2 (by rfl) ⟨167769, by rfl⟩ : syracuseStep 447385 = 335539) (by norm_num)
theorem B906149 : Blo 393766 906149 := bbase (se 4 (by rfl) ⟨84951, by rfl⟩ : syracuseStep 906149 = 169903) (by norm_num)
theorem B447421 : Blo 393766 447421 := bbase (se 3 (by rfl) ⟨83891, by rfl⟩ : syracuseStep 447421 = 167783) (by norm_num)
theorem B1004501 : Blo 393766 1004501 := bbase (se 7 (by rfl) ⟨11771, by rfl⟩ : syracuseStep 1004501 = 23543) (by norm_num)
theorem B447457 : Blo 393766 447457 := bbase (se 2 (by rfl) ⟨167796, by rfl⟩ : syracuseStep 447457 = 335593) (by norm_num)
theorem B1332341 : Blo 393766 1332341 := bbase (se 5 (by rfl) ⟨62453, by rfl⟩ : syracuseStep 1332341 = 124907) (by norm_num)
theorem B3855637 : Blo 393766 3855637 := bbase (se 6 (by rfl) ⟨90366, by rfl⟩ : syracuseStep 3855637 = 180733) (by norm_num)
theorem B1004845 : Blo 393766 1004845 := bbase (se 3 (by rfl) ⟨188408, by rfl⟩ : syracuseStep 1004845 = 376817) (by norm_num)
theorem B1267093 : Blo 393766 1267093 := bbase (se 6 (by rfl) ⟨29697, by rfl⟩ : syracuseStep 1267093 = 59395) (by norm_num)
theorem B1004957 : Blo 393766 1004957 := bbase (se 3 (by rfl) ⟨188429, by rfl⟩ : syracuseStep 1004957 = 376859) (by norm_num)
theorem B644525 : Blo 393766 644525 := bbase (se 3 (by rfl) ⟨120848, by rfl⟩ : syracuseStep 644525 = 241697) (by norm_num)
theorem B841141 : Blo 393766 841141 := bbase (se 5 (by rfl) ⟨39428, by rfl⟩ : syracuseStep 841141 = 78857) (by norm_num)
theorem B1496501 : Blo 393766 1496501 := bbase (se 5 (by rfl) ⟨70148, by rfl⟩ : syracuseStep 1496501 = 140297) (by norm_num)
theorem B1332773 : Blo 393766 1332773 := bbase (se 4 (by rfl) ⟨124947, by rfl⟩ : syracuseStep 1332773 = 249895) (by norm_num)
theorem B841261 : Blo 393766 841261 := bbase (se 3 (by rfl) ⟨157736, by rfl⟩ : syracuseStep 841261 = 315473) (by norm_num)
theorem B1005149 : Blo 393766 1005149 := bbase (se 3 (by rfl) ⟨188465, by rfl⟩ : syracuseStep 1005149 = 376931) (by norm_num)
theorem B3397301 : Blo 393766 3397301 := bbase (se 5 (by rfl) ⟨159248, by rfl⟩ : syracuseStep 3397301 = 318497) (by norm_num)
theorem B1496789 : Blo 393766 1496789 := bbase (se 7 (by rfl) ⟨17540, by rfl⟩ : syracuseStep 1496789 = 35081) (by norm_num)
theorem B841517 : Blo 393766 841517 := bbase (se 3 (by rfl) ⟨157784, by rfl⟩ : syracuseStep 841517 = 315569) (by norm_num)
theorem B1005493 : Blo 393766 1005493 := bbase (se 5 (by rfl) ⟨47132, by rfl⟩ : syracuseStep 1005493 = 94265) (by norm_num)
theorem B1333205 : Blo 393766 1333205 := bbase (se 7 (by rfl) ⟨15623, by rfl⟩ : syracuseStep 1333205 = 31247) (by norm_num)
theorem B1005605 : Blo 393766 1005605 := bbase (se 4 (by rfl) ⟨94275, by rfl⟩ : syracuseStep 1005605 = 188551) (by norm_num)
theorem B2021429 : Blo 393766 2021429 := bbase (se 5 (by rfl) ⟨94754, by rfl⟩ : syracuseStep 2021429 = 189509) (by norm_num)
theorem B1005797 : Blo 393766 1005797 := bbase (se 4 (by rfl) ⟨94293, by rfl⟩ : syracuseStep 1005797 = 188587) (by norm_num)
theorem B2251061 : Blo 393766 2251061 := bbase (se 5 (by rfl) ⟨105518, by rfl⟩ : syracuseStep 2251061 = 211037) (by norm_num)
theorem B1333637 : Blo 393766 1333637 := bbase (se 4 (by rfl) ⟨125028, by rfl⟩ : syracuseStep 1333637 = 250057) (by norm_num)
theorem B1006141 : Blo 393766 1006141 := bbase (se 3 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 1006141 = 377303) (by norm_num)
theorem B2546261 : Blo 393766 2546261 := bbase (se 8 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 2546261 = 29839) (by norm_num)
theorem B842405 : Blo 393766 842405 := bbase (se 4 (by rfl) ⟨78975, by rfl⟩ : syracuseStep 842405 = 157951) (by norm_num)
theorem B940709 : Blo 393766 940709 := bbase (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) (by norm_num)
theorem B1006253 : Blo 393766 1006253 := bbase (se 3 (by rfl) ⟨188672, by rfl⟩ : syracuseStep 1006253 = 377345) (by norm_num)
theorem B1268453 : Blo 393766 1268453 := bbase (se 4 (by rfl) ⟨118917, by rfl⟩ : syracuseStep 1268453 = 237835) (by norm_num)
theorem B1334069 : Blo 393766 1334069 := bbase (se 5 (by rfl) ⟨62534, by rfl⟩ : syracuseStep 1334069 = 125069) (by norm_num)
theorem B1268581 : Blo 393766 1268581 := bbase (se 4 (by rfl) ⟨118929, by rfl⟩ : syracuseStep 1268581 = 237859) (by norm_num)
theorem B1006445 : Blo 393766 1006445 := bbase (se 3 (by rfl) ⟨188708, by rfl⟩ : syracuseStep 1006445 = 377417) (by norm_num)
theorem B1497973 : Blo 393766 1497973 := bbase (se 5 (by rfl) ⟨70217, by rfl⟩ : syracuseStep 1497973 = 140435) (by norm_num)
theorem B842645 : Blo 393766 842645 := bbase (se 6 (by rfl) ⟨19749, by rfl⟩ : syracuseStep 842645 = 39499) (by norm_num)
theorem B1694789 : Blo 393766 1694789 := bbase (se 4 (by rfl) ⟨158886, by rfl⟩ : syracuseStep 1694789 = 317773) (by norm_num)
theorem B1268837 : Blo 393766 1268837 := bbase (se 4 (by rfl) ⟨118953, by rfl⟩ : syracuseStep 1268837 = 237907) (by norm_num)
theorem B973973 : Blo 393766 973973 := bbase (se 6 (by rfl) ⟨22827, by rfl⟩ : syracuseStep 973973 = 45655) (by norm_num)
theorem B1498277 : Blo 393766 1498277 := bbase (se 4 (by rfl) ⟨140463, by rfl⟩ : syracuseStep 1498277 = 280927) (by norm_num)
theorem B1006789 : Blo 393766 1006789 := bbase (se 4 (by rfl) ⟨94386, by rfl⟩ : syracuseStep 1006789 = 188773) (by norm_num)
theorem B1334501 : Blo 393766 1334501 := bbase (se 4 (by rfl) ⟨125109, by rfl⟩ : syracuseStep 1334501 = 250219) (by norm_num)
theorem B711949 : Blo 393766 711949 := bbase (se 3 (by rfl) ⟨133490, by rfl⟩ : syracuseStep 711949 = 266981) (by norm_num)
theorem B5692693 : Blo 393766 5692693 := bbase (se 6 (by rfl) ⟨133422, by rfl⟩ : syracuseStep 5692693 = 266845) (by norm_num)
theorem B449845 : Blo 393766 449845 := bbase (se 5 (by rfl) ⟨21086, by rfl⟩ : syracuseStep 449845 = 42173) (by norm_num)
theorem B843149 : Blo 393766 843149 := bbase (se 3 (by rfl) ⟨158090, by rfl⟩ : syracuseStep 843149 = 316181) (by norm_num)
theorem B843157 : Blo 393766 843157 := bbase (se 6 (by rfl) ⟨19761, by rfl⟩ : syracuseStep 843157 = 39523) (by norm_num)
theorem B2252245 : Blo 393766 2252245 := bbase (se 7 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 2252245 = 52787) (by norm_num)
theorem B3005909 : Blo 393766 3005909 := bbase (se 7 (by rfl) ⟨35225, by rfl⟩ : syracuseStep 3005909 = 70451) (by norm_num)
theorem B1334933 : Blo 393766 1334933 := bbase (se 6 (by rfl) ⟨31287, by rfl⟩ : syracuseStep 1334933 = 62575) (by norm_num)
theorem B4284053 : Blo 393766 4284053 := bbase (se 6 (by rfl) ⟨100407, by rfl⟩ : syracuseStep 4284053 = 200815) (by norm_num)
theorem B483017 : Blo 393766 483017 := bbase (se 2 (by rfl) ⟨181131, by rfl⟩ : syracuseStep 483017 = 362263) (by norm_num)
theorem B515977 : Blo 393766 515977 := bbase (se 2 (by rfl) ⟨193491, by rfl⟩ : syracuseStep 515977 = 386983) (by norm_num)
theorem B1892261 : Blo 393766 1892261 := bbase (se 4 (by rfl) ⟨177399, by rfl⟩ : syracuseStep 1892261 = 354799) (by norm_num)
theorem B1335365 : Blo 393766 1335365 := bbase (se 4 (by rfl) ⟨125190, by rfl⟩ : syracuseStep 1335365 = 250381) (by norm_num)
theorem B713029 : Blo 393766 713029 := bbase (se 4 (by rfl) ⟨66846, by rfl⟩ : syracuseStep 713029 = 133693) (by norm_num)
theorem B5431637 : Blo 393766 5431637 := bbase (se 10 (by rfl) ⟨7956, by rfl⟩ : syracuseStep 5431637 = 15913) (by norm_num)
theorem B713117 : Blo 393766 713117 := bbase (se 3 (by rfl) ⟨133709, by rfl⟩ : syracuseStep 713117 = 267419) (by norm_num)
theorem B713173 : Blo 393766 713173 := bbase (se 7 (by rfl) ⟨8357, by rfl⟩ : syracuseStep 713173 = 16715) (by norm_num)
theorem B1335797 : Blo 393766 1335797 := bbase (se 5 (by rfl) ⟨62615, by rfl⟩ : syracuseStep 1335797 = 125231) (by norm_num)
theorem B844285 : Blo 393766 844285 := bbase (se 3 (by rfl) ⟨158303, by rfl⟩ : syracuseStep 844285 = 316607) (by norm_num)
theorem B1696565 : Blo 393766 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B844661 : Blo 393766 844661 := bbase (se 5 (by rfl) ⟨39593, by rfl⟩ : syracuseStep 844661 = 79187) (by norm_num)
theorem B1336229 : Blo 393766 1336229 := bbase (se 4 (by rfl) ⟨125271, by rfl⟩ : syracuseStep 1336229 = 250543) (by norm_num)
theorem B1500389 : Blo 393766 1500389 := bbase (se 4 (by rfl) ⟨140661, by rfl⟩ : syracuseStep 1500389 = 281323) (by norm_num)
theorem B1336661 : Blo 393766 1336661 := bbase (se 12 (by rfl) ⟨489, by rfl⟩ : syracuseStep 1336661 = 979) (by norm_num)
theorem B2254229 : Blo 393766 2254229 := bbase (se 6 (by rfl) ⟨52833, by rfl⟩ : syracuseStep 2254229 = 105667) (by norm_num)
theorem B1271285 : Blo 393766 1271285 := bbase (se 5 (by rfl) ⟨59591, by rfl⟩ : syracuseStep 1271285 = 119183) (by norm_num)
theorem B1500677 : Blo 393766 1500677 := bbase (se 4 (by rfl) ⟨140688, by rfl⟩ : syracuseStep 1500677 = 281377) (by norm_num)
theorem B648901 : Blo 393766 648901 := bbase (se 4 (by rfl) ⟨60834, by rfl⟩ : syracuseStep 648901 = 121669) (by norm_num)
theorem B1337093 : Blo 393766 1337093 := bbase (se 4 (by rfl) ⟨125352, by rfl⟩ : syracuseStep 1337093 = 250705) (by norm_num)
theorem B1173253 : Blo 393766 1173253 := bbase (se 4 (by rfl) ⟨109992, by rfl⟩ : syracuseStep 1173253 = 219985) (by norm_num)
theorem B1697557 : Blo 393766 1697557 := bbase (se 6 (by rfl) ⟨39786, by rfl⟩ : syracuseStep 1697557 = 79573) (by norm_num)
theorem B1206085 : Blo 393766 1206085 := bbase (se 4 (by rfl) ⟨113070, by rfl⟩ : syracuseStep 1206085 = 226141) (by norm_num)
theorem B714701 : Blo 393766 714701 := bbase (se 3 (by rfl) ⟨134006, by rfl⟩ : syracuseStep 714701 = 268013) (by norm_num)
theorem B747605 : Blo 393766 747605 := bbase (se 8 (by rfl) ⟨4380, by rfl⟩ : syracuseStep 747605 = 8761) (by norm_num)
theorem B911477 : Blo 393766 911477 := bbase (se 5 (by rfl) ⟨42725, by rfl⟩ : syracuseStep 911477 = 85451) (by norm_num)
theorem B1337525 : Blo 393766 1337525 := bbase (se 5 (by rfl) ⟨62696, by rfl⟩ : syracuseStep 1337525 = 125393) (by norm_num)
theorem B747893 : Blo 393766 747893 := bbase (se 5 (by rfl) ⟨35057, by rfl⟩ : syracuseStep 747893 = 70115) (by norm_num)
theorem B846301 : Blo 393766 846301 := bbase (se 3 (by rfl) ⟨158681, by rfl⟩ : syracuseStep 846301 = 317363) (by norm_num)
theorem B748045 : Blo 393766 748045 := bbase (se 3 (by rfl) ⟨140258, by rfl⟩ : syracuseStep 748045 = 280517) (by norm_num)
theorem B1337957 : Blo 393766 1337957 := bbase (se 4 (by rfl) ⟨125433, by rfl⟩ : syracuseStep 1337957 = 250867) (by norm_num)
theorem B1501861 : Blo 393766 1501861 := bbase (se 4 (by rfl) ⟨140799, by rfl⟩ : syracuseStep 1501861 = 281599) (by norm_num)
theorem B453313 : Blo 393766 453313 := bbase (se 2 (by rfl) ⟨169992, by rfl⟩ : syracuseStep 453313 = 339985) (by norm_num)
theorem B1272629 : Blo 393766 1272629 := bbase (se 5 (by rfl) ⟨59654, by rfl⟩ : syracuseStep 1272629 = 119309) (by norm_num)
theorem B748349 : Blo 393766 748349 := bbase (se 3 (by rfl) ⟨140315, by rfl⟩ : syracuseStep 748349 = 280631) (by norm_num)
theorem B3206101 : Blo 393766 3206101 := bbase (se 7 (by rfl) ⟨37571, by rfl⟩ : syracuseStep 3206101 = 75143) (by norm_num)
theorem B1502165 : Blo 393766 1502165 := bbase (se 7 (by rfl) ⟨17603, by rfl⟩ : syracuseStep 1502165 = 35207) (by norm_num)
theorem B1993733 : Blo 393766 1993733 := bbase (se 4 (by rfl) ⟨186912, by rfl⟩ : syracuseStep 1993733 = 373825) (by norm_num)
theorem B1338389 : Blo 393766 1338389 := bbase (se 6 (by rfl) ⟨31368, by rfl⟩ : syracuseStep 1338389 = 62737) (by norm_num)
theorem B421049 : Blo 393766 421049 := bbase (se 2 (by rfl) ⟨157893, by rfl⟩ : syracuseStep 421049 = 315787) (by norm_num)
theorem B716021 : Blo 393766 716021 := bbase (se 5 (by rfl) ⟨33563, by rfl⟩ : syracuseStep 716021 = 67127) (by norm_num)
theorem B847189 : Blo 393766 847189 := bbase (se 11 (by rfl) ⟨620, by rfl⟩ : syracuseStep 847189 = 1241) (by norm_num)
theorem B421237 : Blo 393766 421237 := bbase (se 5 (by rfl) ⟨19745, by rfl⟩ : syracuseStep 421237 = 39491) (by norm_num)
theorem B1338821 : Blo 393766 1338821 := bbase (se 4 (by rfl) ⟨125514, by rfl⟩ : syracuseStep 1338821 = 251029) (by norm_num)
theorem B749101 : Blo 393766 749101 := bbase (se 3 (by rfl) ⟨140456, by rfl⟩ : syracuseStep 749101 = 280913) (by norm_num)
theorem B2256437 : Blo 393766 2256437 := bbase (se 5 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 2256437 = 211541) (by norm_num)
theorem B749245 : Blo 393766 749245 := bbase (se 3 (by rfl) ⟨140483, by rfl⟩ : syracuseStep 749245 = 280967) (by norm_num)
theorem B913189 : Blo 393766 913189 := bbase (se 4 (by rfl) ⟨85611, by rfl⟩ : syracuseStep 913189 = 171223) (by norm_num)
theorem B847685 : Blo 393766 847685 := bbase (se 4 (by rfl) ⟨79470, by rfl⟩ : syracuseStep 847685 = 158941) (by norm_num)
theorem B749405 : Blo 393766 749405 := bbase (se 3 (by rfl) ⟨140513, by rfl⟩ : syracuseStep 749405 = 281027) (by norm_num)
theorem B1339253 : Blo 393766 1339253 := bbase (se 5 (by rfl) ⟨62777, by rfl⟩ : syracuseStep 1339253 = 125555) (by norm_num)
theorem B1699717 : Blo 393766 1699717 := bbase (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) (by norm_num)
theorem B749549 : Blo 393766 749549 := bbase (se 3 (by rfl) ⟨140540, by rfl⟩ : syracuseStep 749549 = 281081) (by norm_num)
theorem B1929205 : Blo 393766 1929205 := bbase (se 5 (by rfl) ⟨90431, by rfl⟩ : syracuseStep 1929205 = 180863) (by norm_num)
theorem B946237 : Blo 393766 946237 := bbase (se 3 (by rfl) ⟨177419, by rfl⟩ : syracuseStep 946237 = 354839) (by norm_num)
theorem B422057 : Blo 393766 422057 := bbase (se 2 (by rfl) ⟨158271, by rfl⟩ : syracuseStep 422057 = 316543) (by norm_num)
theorem B749837 : Blo 393766 749837 := bbase (se 3 (by rfl) ⟨140594, by rfl⟩ : syracuseStep 749837 = 281189) (by norm_num)
theorem B1995029 : Blo 393766 1995029 := bbase (se 6 (by rfl) ⟨46758, by rfl⟩ : syracuseStep 1995029 = 93517) (by norm_num)
theorem B1339685 : Blo 393766 1339685 := bbase (se 4 (by rfl) ⟨125595, by rfl⟩ : syracuseStep 1339685 = 251191) (by norm_num)
theorem B1012133 : Blo 393766 1012133 := bbase (se 4 (by rfl) ⟨94887, by rfl⟩ : syracuseStep 1012133 = 189775) (by norm_num)
theorem B749989 : Blo 393766 749989 := bbase (se 4 (by rfl) ⟨70311, by rfl⟩ : syracuseStep 749989 = 140623) (by norm_num)
theorem B1896949 : Blo 393766 1896949 := bbase (se 5 (by rfl) ⟨88919, by rfl⟩ : syracuseStep 1896949 = 177839) (by norm_num)
theorem B422501 : Blo 393766 422501 := bbase (se 4 (by rfl) ⟨39609, by rfl⟩ : syracuseStep 422501 = 79219) (by norm_num)
theorem B946853 : Blo 393766 946853 := bbase (se 4 (by rfl) ⟨88767, by rfl⟩ : syracuseStep 946853 = 177535) (by norm_num)
theorem B848549 : Blo 393766 848549 := bbase (se 4 (by rfl) ⟨79551, by rfl⟩ : syracuseStep 848549 = 159103) (by norm_num)
theorem B750293 : Blo 393766 750293 := bbase (se 7 (by rfl) ⟨8792, by rfl⟩ : syracuseStep 750293 = 17585) (by norm_num)
theorem B1340117 : Blo 393766 1340117 := bbase (se 7 (by rfl) ⟨15704, by rfl⟩ : syracuseStep 1340117 = 31409) (by norm_num)
theorem B488197 : Blo 393766 488197 := bbase (se 4 (by rfl) ⟨45768, by rfl⟩ : syracuseStep 488197 = 91537) (by norm_num)
theorem B2028325 : Blo 393766 2028325 := bbase (se 4 (by rfl) ⟨190155, by rfl⟩ : syracuseStep 2028325 = 380311) (by norm_num)
theorem B848693 : Blo 393766 848693 := bbase (se 5 (by rfl) ⟨39782, by rfl⟩ : syracuseStep 848693 = 79565) (by norm_num)
theorem B422749 : Blo 393766 422749 := bbase (se 3 (by rfl) ⟨79265, by rfl⟩ : syracuseStep 422749 = 158531) (by norm_num)
theorem B1504277 : Blo 393766 1504277 := bbase (se 6 (by rfl) ⟨35256, by rfl⟩ : syracuseStep 1504277 = 70513) (by norm_num)
theorem B1340549 : Blo 393766 1340549 := bbase (se 4 (by rfl) ⟨125676, by rfl⟩ : syracuseStep 1340549 = 251353) (by norm_num)
theorem B423181 : Blo 393766 423181 := bbase (se 3 (by rfl) ⟨79346, by rfl⟩ : syracuseStep 423181 = 158693) (by norm_num)
theorem B1504565 : Blo 393766 1504565 := bbase (se 5 (by rfl) ⟨70526, by rfl⟩ : syracuseStep 1504565 = 141053) (by norm_num)
theorem B423253 : Blo 393766 423253 := bbase (se 13 (by rfl) ⟨77, by rfl⟩ : syracuseStep 423253 = 155) (by norm_num)
theorem B3437909 : Blo 393766 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B947621 : Blo 393766 947621 := bbase (se 4 (by rfl) ⟨88839, by rfl⟩ : syracuseStep 947621 = 177679) (by norm_num)
theorem B947629 : Blo 393766 947629 := bbase (se 3 (by rfl) ⟨177680, by rfl⟩ : syracuseStep 947629 = 355361) (by norm_num)
theorem B751045 : Blo 393766 751045 := bbase (se 4 (by rfl) ⟨70410, by rfl⟩ : syracuseStep 751045 = 140821) (by norm_num)
theorem B849437 : Blo 393766 849437 := bbase (se 3 (by rfl) ⟨159269, by rfl⟩ : syracuseStep 849437 = 318539) (by norm_num)
theorem B1996325 : Blo 393766 1996325 := bbase (se 4 (by rfl) ⟨187155, by rfl⟩ : syracuseStep 1996325 = 374311) (by norm_num)
theorem B1340981 : Blo 393766 1340981 := bbase (se 5 (by rfl) ⟨62858, by rfl⟩ : syracuseStep 1340981 = 125717) (by norm_num)
theorem B751189 : Blo 393766 751189 := bbase (se 8 (by rfl) ⟨4401, by rfl⟩ : syracuseStep 751189 = 8803) (by norm_num)
theorem B2717333 : Blo 393766 2717333 := bbase (se 6 (by rfl) ⟨63687, by rfl⟩ : syracuseStep 2717333 = 127375) (by norm_num)
theorem B423625 : Blo 393766 423625 := bbase (se 2 (by rfl) ⟨158859, by rfl⟩ : syracuseStep 423625 = 317719) (by norm_num)
theorem B751349 : Blo 393766 751349 := bbase (se 5 (by rfl) ⟨35219, by rfl⟩ : syracuseStep 751349 = 70439) (by norm_num)
theorem B751493 : Blo 393766 751493 := bbase (se 4 (by rfl) ⟨70452, by rfl⟩ : syracuseStep 751493 = 140905) (by norm_num)
theorem B1341413 : Blo 393766 1341413 := bbase (se 4 (by rfl) ⟨125757, by rfl⟩ : syracuseStep 1341413 = 251515) (by norm_num)
theorem B489461 : Blo 393766 489461 := bbase (se 5 (by rfl) ⟨22943, by rfl⟩ : syracuseStep 489461 = 45887) (by norm_num)
theorem B424001 : Blo 393766 424001 := bbase (se 2 (by rfl) ⟨159000, by rfl⟩ : syracuseStep 424001 = 318001) (by norm_num)
theorem B424073 : Blo 393766 424073 := bbase (se 2 (by rfl) ⟨159027, by rfl⟩ : syracuseStep 424073 = 318055) (by norm_num)
theorem B751781 : Blo 393766 751781 := bbase (se 4 (by rfl) ⟨70479, by rfl⟩ : syracuseStep 751781 = 140959) (by norm_num)
theorem B948437 : Blo 393766 948437 := bbase (se 7 (by rfl) ⟨11114, by rfl⟩ : syracuseStep 948437 = 22229) (by norm_num)
theorem B751933 : Blo 393766 751933 := bbase (se 3 (by rfl) ⟨140987, by rfl⟩ : syracuseStep 751933 = 281975) (by norm_num)
theorem B424261 : Blo 393766 424261 := bbase (se 4 (by rfl) ⟨39774, by rfl⟩ : syracuseStep 424261 = 79549) (by norm_num)
theorem B1374581 : Blo 393766 1374581 := bbase (se 5 (by rfl) ⟨64433, by rfl⟩ : syracuseStep 1374581 = 128867) (by norm_num)
theorem B1341845 : Blo 393766 1341845 := bbase (se 6 (by rfl) ⟨31449, by rfl⟩ : syracuseStep 1341845 = 62899) (by norm_num)
theorem B1505749 : Blo 393766 1505749 := bbase (se 7 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 1505749 = 35291) (by norm_num)
theorem B424445 : Blo 393766 424445 := bbase (se 3 (by rfl) ⟨79583, by rfl⟩ : syracuseStep 424445 = 159167) (by norm_num)
theorem B752237 : Blo 393766 752237 := bbase (se 3 (by rfl) ⟨141044, by rfl⟩ : syracuseStep 752237 = 282089) (by norm_num)
theorem B490093 : Blo 393766 490093 := bbase (se 3 (by rfl) ⟨91892, by rfl⟩ : syracuseStep 490093 = 183785) (by norm_num)
theorem B457445 : Blo 393766 457445 := bbase (se 4 (by rfl) ⟨42885, by rfl⟩ : syracuseStep 457445 = 85771) (by norm_num)
theorem B1506053 : Blo 393766 1506053 := bbase (se 4 (by rfl) ⟨141192, by rfl⟩ : syracuseStep 1506053 = 282385) (by norm_num)
theorem B1997621 : Blo 393766 1997621 := bbase (se 5 (by rfl) ⟨93638, by rfl⟩ : syracuseStep 1997621 = 187277) (by norm_num)
theorem B1342277 : Blo 393766 1342277 := bbase (se 4 (by rfl) ⟨125838, by rfl⟩ : syracuseStep 1342277 = 251677) (by norm_num)
theorem B687109 : Blo 393766 687109 := bbase (se 4 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 687109 = 128833) (by norm_num)
theorem B3013685 : Blo 393766 3013685 := bbase (se 5 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 3013685 = 282533) (by norm_num)
theorem B752989 : Blo 393766 752989 := bbase (se 3 (by rfl) ⟨141185, by rfl⟩ : syracuseStep 752989 = 282371) (by norm_num)
theorem B3210677 : Blo 393766 3210677 := bbase (se 5 (by rfl) ⟨150500, by rfl⟩ : syracuseStep 3210677 = 301001) (by norm_num)
theorem B753133 : Blo 393766 753133 := bbase (se 3 (by rfl) ⟨141212, by rfl⟩ : syracuseStep 753133 = 282425) (by norm_num)
theorem B753293 : Blo 393766 753293 := bbase (se 3 (by rfl) ⟨141242, by rfl⟩ : syracuseStep 753293 = 282485) (by norm_num)
theorem B3210965 : Blo 393766 3210965 := bbase (se 7 (by rfl) ⟨37628, by rfl⟩ : syracuseStep 3210965 = 75257) (by norm_num)
theorem B753437 : Blo 393766 753437 := bbase (se 3 (by rfl) ⟨141269, by rfl⟩ : syracuseStep 753437 = 282539) (by norm_num)
theorem B1441955 : Blo 393766 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B458995 : Blo 393766 458995 := bstep (se 1 (by rfl) ⟨344246, by rfl⟩ : syracuseStep 458995 = 688493) B688493
theorem B753923 : Blo 393766 753923 := bstep (se 1 (by rfl) ⟨565442, by rfl⟩ : syracuseStep 753923 = 1130885) B1130885
theorem B950705 : Blo 393766 950705 := bstep (se 2 (by rfl) ⟨356514, by rfl⟩ : syracuseStep 950705 = 713029) B713029
theorem B754211 : Blo 393766 754211 := bstep (se 1 (by rfl) ⟨565658, by rfl⟩ : syracuseStep 754211 = 1131317) B1131317
theorem B393779 : Blo 393766 393779 := bstep (se 1 (by rfl) ⟨295334, by rfl⟩ : syracuseStep 393779 = 590669) B590669
theorem B393795 : Blo 393766 393795 := bstep (se 1 (by rfl) ⟨295346, by rfl⟩ : syracuseStep 393795 = 590693) B590693
theorem B393811 : Blo 393766 393811 := bstep (se 1 (by rfl) ⟨295358, by rfl⟩ : syracuseStep 393811 = 590717) B590717
theorem B393827 : Blo 393766 393827 := bstep (se 1 (by rfl) ⟨295370, by rfl⟩ : syracuseStep 393827 = 590741) B590741
theorem B950897 : Blo 393766 950897 := bstep (se 2 (by rfl) ⟨356586, by rfl⟩ : syracuseStep 950897 = 713173) B713173
theorem B393843 : Blo 393766 393843 := bstep (se 1 (by rfl) ⟨295382, by rfl⟩ : syracuseStep 393843 = 590765) B590765
theorem B393859 : Blo 393766 393859 := bstep (se 1 (by rfl) ⟨295394, by rfl⟩ : syracuseStep 393859 = 590789) B590789
theorem B393875 : Blo 393766 393875 := bstep (se 1 (by rfl) ⟨295406, by rfl⟩ : syracuseStep 393875 = 590813) B590813
theorem B393891 : Blo 393766 393891 := bstep (se 1 (by rfl) ⟨295418, by rfl⟩ : syracuseStep 393891 = 590837) B590837
theorem B393907 : Blo 393766 393907 := bstep (se 1 (by rfl) ⟨295430, by rfl⟩ : syracuseStep 393907 = 590861) B590861
theorem B393923 : Blo 393766 393923 := bstep (se 1 (by rfl) ⟨295442, by rfl⟩ : syracuseStep 393923 = 590885) B590885
theorem B1999565 : Blo 393766 1999565 := bstep (se 3 (by rfl) ⟨374918, by rfl⟩ : syracuseStep 1999565 = 749837) B749837
theorem B393939 : Blo 393766 393939 := bstep (se 1 (by rfl) ⟨295454, by rfl⟩ : syracuseStep 393939 = 590909) B590909
theorem B393955 : Blo 393766 393955 := bstep (se 1 (by rfl) ⟨295466, by rfl⟩ : syracuseStep 393955 = 590933) B590933
theorem B393971 : Blo 393766 393971 := bstep (se 1 (by rfl) ⟨295478, by rfl⟩ : syracuseStep 393971 = 590957) B590957
theorem B393987 : Blo 393766 393987 := bstep (se 1 (by rfl) ⟨295490, by rfl⟩ : syracuseStep 393987 = 590981) B590981
theorem B394003 : Blo 393766 394003 := bstep (se 1 (by rfl) ⟨295502, by rfl⟩ : syracuseStep 394003 = 591005) B591005
theorem B12321557 : Blo 393766 12321557 := bstep (se 6 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 12321557 = 577573) B577573
theorem B394019 : Blo 393766 394019 := bstep (se 1 (by rfl) ⟨295514, by rfl⟩ : syracuseStep 394019 = 591029) B591029
theorem B394035 : Blo 393766 394035 := bstep (se 1 (by rfl) ⟨295526, by rfl⟩ : syracuseStep 394035 = 591053) B591053
theorem B590657 : Blo 393766 590657 := bstep (se 2 (by rfl) ⟨221496, by rfl⟩ : syracuseStep 590657 = 442993) B442993
theorem B394051 : Blo 393766 394051 := bstep (se 1 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 394051 = 591077) B591077
theorem B590675 : Blo 393766 590675 := bstep (se 1 (by rfl) ⟨443006, by rfl⟩ : syracuseStep 590675 = 886013) B886013
theorem B394067 : Blo 393766 394067 := bstep (se 1 (by rfl) ⟨295550, by rfl⟩ : syracuseStep 394067 = 591101) B591101
theorem B394083 : Blo 393766 394083 := bstep (se 1 (by rfl) ⟨295562, by rfl⟩ : syracuseStep 394083 = 591125) B591125
theorem B590705 : Blo 393766 590705 := bstep (se 2 (by rfl) ⟨221514, by rfl⟩ : syracuseStep 590705 = 443029) B443029
theorem B394099 : Blo 393766 394099 := bstep (se 1 (by rfl) ⟨295574, by rfl⟩ : syracuseStep 394099 = 591149) B591149
theorem B590723 : Blo 393766 590723 := bstep (se 1 (by rfl) ⟨443042, by rfl⟩ : syracuseStep 590723 = 886085) B886085
theorem B394115 : Blo 393766 394115 := bstep (se 1 (by rfl) ⟨295586, by rfl⟩ : syracuseStep 394115 = 591173) B591173
theorem B14484365 : Blo 393766 14484365 := bstep (se 3 (by rfl) ⟨2715818, by rfl⟩ : syracuseStep 14484365 = 5431637) B5431637
theorem B394131 : Blo 393766 394131 := bstep (se 1 (by rfl) ⟨295598, by rfl⟩ : syracuseStep 394131 = 591197) B591197
theorem B590753 : Blo 393766 590753 := bstep (se 2 (by rfl) ⟨221532, by rfl⟩ : syracuseStep 590753 = 443065) B443065
theorem B394147 : Blo 393766 394147 := bstep (se 1 (by rfl) ⟨295610, by rfl⟩ : syracuseStep 394147 = 591221) B591221
theorem B590771 : Blo 393766 590771 := bstep (se 1 (by rfl) ⟨443078, by rfl⟩ : syracuseStep 590771 = 886157) B886157
theorem B394163 : Blo 393766 394163 := bstep (se 1 (by rfl) ⟨295622, by rfl⟩ : syracuseStep 394163 = 591245) B591245
theorem B394179 : Blo 393766 394179 := bstep (se 1 (by rfl) ⟨295634, by rfl⟩ : syracuseStep 394179 = 591269) B591269
theorem B590801 : Blo 393766 590801 := bstep (se 2 (by rfl) ⟨221550, by rfl⟩ : syracuseStep 590801 = 443101) B443101
theorem B394195 : Blo 393766 394195 := bstep (se 1 (by rfl) ⟨295646, by rfl⟩ : syracuseStep 394195 = 591293) B591293
theorem B590819 : Blo 393766 590819 := bstep (se 1 (by rfl) ⟨443114, by rfl⟩ : syracuseStep 590819 = 886229) B886229
theorem B394211 : Blo 393766 394211 := bstep (se 1 (by rfl) ⟨295658, by rfl⟩ : syracuseStep 394211 = 591317) B591317
theorem B394227 : Blo 393766 394227 := bstep (se 1 (by rfl) ⟨295670, by rfl⟩ : syracuseStep 394227 = 591341) B591341
theorem B590849 : Blo 393766 590849 := bstep (se 2 (by rfl) ⟨221568, by rfl⟩ : syracuseStep 590849 = 443137) B443137
theorem B394243 : Blo 393766 394243 := bstep (se 1 (by rfl) ⟨295682, by rfl⟩ : syracuseStep 394243 = 591365) B591365
theorem B590867 : Blo 393766 590867 := bstep (se 1 (by rfl) ⟨443150, by rfl⟩ : syracuseStep 590867 = 886301) B886301
theorem B394259 : Blo 393766 394259 := bstep (se 1 (by rfl) ⟨295694, by rfl⟩ : syracuseStep 394259 = 591389) B591389
theorem B394275 : Blo 393766 394275 := bstep (se 1 (by rfl) ⟨295706, by rfl⟩ : syracuseStep 394275 = 591413) B591413
theorem B590897 : Blo 393766 590897 := bstep (se 2 (by rfl) ⟨221586, by rfl⟩ : syracuseStep 590897 = 443173) B443173
theorem B394291 : Blo 393766 394291 := bstep (se 1 (by rfl) ⟨295718, by rfl⟩ : syracuseStep 394291 = 591437) B591437
theorem B590915 : Blo 393766 590915 := bstep (se 1 (by rfl) ⟨443186, by rfl⟩ : syracuseStep 590915 = 886373) B886373
theorem B394307 : Blo 393766 394307 := bstep (se 1 (by rfl) ⟨295730, by rfl⟩ : syracuseStep 394307 = 591461) B591461
theorem B394323 : Blo 393766 394323 := bstep (se 1 (by rfl) ⟨295742, by rfl⟩ : syracuseStep 394323 = 591485) B591485
theorem B590945 : Blo 393766 590945 := bstep (se 2 (by rfl) ⟨221604, by rfl⟩ : syracuseStep 590945 = 443209) B443209
theorem B394339 : Blo 393766 394339 := bstep (se 1 (by rfl) ⟨295754, by rfl⟩ : syracuseStep 394339 = 591509) B591509
theorem B590963 : Blo 393766 590963 := bstep (se 1 (by rfl) ⟨443222, by rfl⟩ : syracuseStep 590963 = 886445) B886445
theorem B394355 : Blo 393766 394355 := bstep (se 1 (by rfl) ⟨295766, by rfl⟩ : syracuseStep 394355 = 591533) B591533
theorem B394371 : Blo 393766 394371 := bstep (se 1 (by rfl) ⟨295778, by rfl⟩ : syracuseStep 394371 = 591557) B591557
theorem B590993 : Blo 393766 590993 := bstep (se 2 (by rfl) ⟨221622, by rfl⟩ : syracuseStep 590993 = 443245) B443245
theorem B394387 : Blo 393766 394387 := bstep (se 1 (by rfl) ⟨295790, by rfl⟩ : syracuseStep 394387 = 591581) B591581
theorem B591011 : Blo 393766 591011 := bstep (se 1 (by rfl) ⟨443258, by rfl⟩ : syracuseStep 591011 = 886517) B886517
theorem B394403 : Blo 393766 394403 := bstep (se 1 (by rfl) ⟨295802, by rfl⟩ : syracuseStep 394403 = 591605) B591605
theorem B394419 : Blo 393766 394419 := bstep (se 1 (by rfl) ⟨295814, by rfl⟩ : syracuseStep 394419 = 591629) B591629
theorem B591041 : Blo 393766 591041 := bstep (se 2 (by rfl) ⟨221640, by rfl⟩ : syracuseStep 591041 = 443281) B443281
theorem B394435 : Blo 393766 394435 := bstep (se 1 (by rfl) ⟨295826, by rfl⟩ : syracuseStep 394435 = 591653) B591653
theorem B394451 : Blo 393766 394451 := bstep (se 1 (by rfl) ⟨295838, by rfl⟩ : syracuseStep 394451 = 591677) B591677
theorem B591059 : Blo 393766 591059 := bstep (se 1 (by rfl) ⟨443294, by rfl⟩ : syracuseStep 591059 = 886589) B886589
theorem B394467 : Blo 393766 394467 := bstep (se 1 (by rfl) ⟨295850, by rfl⟩ : syracuseStep 394467 = 591701) B591701
theorem B591089 : Blo 393766 591089 := bstep (se 2 (by rfl) ⟨221658, by rfl⟩ : syracuseStep 591089 = 443317) B443317
theorem B1148141 : Blo 393766 1148141 := bstep (se 3 (by rfl) ⟨215276, by rfl⟩ : syracuseStep 1148141 = 430553) B430553
theorem B394483 : Blo 393766 394483 := bstep (se 1 (by rfl) ⟨295862, by rfl⟩ : syracuseStep 394483 = 591725) B591725
theorem B591107 : Blo 393766 591107 := bstep (se 1 (by rfl) ⟨443330, by rfl⟩ : syracuseStep 591107 = 886661) B886661
theorem B394499 : Blo 393766 394499 := bstep (se 1 (by rfl) ⟨295874, by rfl⟩ : syracuseStep 394499 = 591749) B591749
theorem B1934605 : Blo 393766 1934605 := bstep (se 3 (by rfl) ⟨362738, by rfl⟩ : syracuseStep 1934605 = 725477) B725477
theorem B394515 : Blo 393766 394515 := bstep (se 1 (by rfl) ⟨295886, by rfl⟩ : syracuseStep 394515 = 591773) B591773
theorem B591137 : Blo 393766 591137 := bstep (se 2 (by rfl) ⟨221676, by rfl⟩ : syracuseStep 591137 = 443353) B443353
theorem B394531 : Blo 393766 394531 := bstep (se 1 (by rfl) ⟨295898, by rfl⟩ : syracuseStep 394531 = 591797) B591797
theorem B1836323 : Blo 393766 1836323 := bstep (se 1 (by rfl) ⟨1377242, by rfl⟩ : syracuseStep 1836323 = 2754485) B2754485
theorem B591155 : Blo 393766 591155 := bstep (se 1 (by rfl) ⟨443366, by rfl⟩ : syracuseStep 591155 = 886733) B886733
theorem B394547 : Blo 393766 394547 := bstep (se 1 (by rfl) ⟨295910, by rfl⟩ : syracuseStep 394547 = 591821) B591821
theorem B394563 : Blo 393766 394563 := bstep (se 1 (by rfl) ⟨295922, by rfl⟩ : syracuseStep 394563 = 591845) B591845
theorem B591185 : Blo 393766 591185 := bstep (se 2 (by rfl) ⟨221694, by rfl⟩ : syracuseStep 591185 = 443389) B443389
theorem B394579 : Blo 393766 394579 := bstep (se 1 (by rfl) ⟨295934, by rfl⟩ : syracuseStep 394579 = 591869) B591869
theorem B591203 : Blo 393766 591203 := bstep (se 1 (by rfl) ⟨443402, by rfl⟩ : syracuseStep 591203 = 886805) B886805
theorem B394595 : Blo 393766 394595 := bstep (se 1 (by rfl) ⟨295946, by rfl⟩ : syracuseStep 394595 = 591893) B591893
theorem B394611 : Blo 393766 394611 := bstep (se 1 (by rfl) ⟨295958, by rfl⟩ : syracuseStep 394611 = 591917) B591917
theorem B591233 : Blo 393766 591233 := bstep (se 2 (by rfl) ⟨221712, by rfl⟩ : syracuseStep 591233 = 443425) B443425
theorem B394627 : Blo 393766 394627 := bstep (se 1 (by rfl) ⟨295970, by rfl⟩ : syracuseStep 394627 = 591941) B591941
theorem B591251 : Blo 393766 591251 := bstep (se 1 (by rfl) ⟨443438, by rfl⟩ : syracuseStep 591251 = 886877) B886877
theorem B394643 : Blo 393766 394643 := bstep (se 1 (by rfl) ⟨295982, by rfl⟩ : syracuseStep 394643 = 591965) B591965
theorem B394659 : Blo 393766 394659 := bstep (se 1 (by rfl) ⟨295994, by rfl⟩ : syracuseStep 394659 = 591989) B591989
theorem B886193 : Blo 393766 886193 := bstep (se 2 (by rfl) ⟨332322, by rfl⟩ : syracuseStep 886193 = 664645) B664645
theorem B591281 : Blo 393766 591281 := bstep (se 2 (by rfl) ⟨221730, by rfl⟩ : syracuseStep 591281 = 443461) B443461
theorem B394675 : Blo 393766 394675 := bstep (se 1 (by rfl) ⟨296006, by rfl⟩ : syracuseStep 394675 = 592013) B592013
theorem B886211 : Blo 393766 886211 := bstep (se 1 (by rfl) ⟨664658, by rfl⟩ : syracuseStep 886211 = 1329317) B1329317
theorem B591299 : Blo 393766 591299 := bstep (se 1 (by rfl) ⟨443474, by rfl⟩ : syracuseStep 591299 = 886949) B886949
theorem B394691 : Blo 393766 394691 := bstep (se 1 (by rfl) ⟨296018, by rfl⟩ : syracuseStep 394691 = 592037) B592037
theorem B1803725 : Blo 393766 1803725 := bstep (se 3 (by rfl) ⟨338198, by rfl⟩ : syracuseStep 1803725 = 676397) B676397
theorem B394707 : Blo 393766 394707 := bstep (se 1 (by rfl) ⟨296030, by rfl⟩ : syracuseStep 394707 = 592061) B592061
theorem B591329 : Blo 393766 591329 := bstep (se 2 (by rfl) ⟨221748, by rfl⟩ : syracuseStep 591329 = 443497) B443497
theorem B394723 : Blo 393766 394723 := bstep (se 1 (by rfl) ⟨296042, by rfl⟩ : syracuseStep 394723 = 592085) B592085
theorem B591347 : Blo 393766 591347 := bstep (se 1 (by rfl) ⟨443510, by rfl⟩ : syracuseStep 591347 = 887021) B887021
theorem B394739 : Blo 393766 394739 := bstep (se 1 (by rfl) ⟨296054, by rfl⟩ : syracuseStep 394739 = 592109) B592109
theorem B394755 : Blo 393766 394755 := bstep (se 1 (by rfl) ⟨296066, by rfl⟩ : syracuseStep 394755 = 592133) B592133
theorem B591377 : Blo 393766 591377 := bstep (se 2 (by rfl) ⟨221766, by rfl⟩ : syracuseStep 591377 = 443533) B443533
theorem B394771 : Blo 393766 394771 := bstep (se 1 (by rfl) ⟨296078, by rfl⟩ : syracuseStep 394771 = 592157) B592157
theorem B591395 : Blo 393766 591395 := bstep (se 1 (by rfl) ⟨443546, by rfl⟩ : syracuseStep 591395 = 887093) B887093
theorem B394787 : Blo 393766 394787 := bstep (se 1 (by rfl) ⟨296090, by rfl⟩ : syracuseStep 394787 = 592181) B592181
theorem B394803 : Blo 393766 394803 := bstep (se 1 (by rfl) ⟨296102, by rfl⟩ : syracuseStep 394803 = 592205) B592205
theorem B591425 : Blo 393766 591425 := bstep (se 2 (by rfl) ⟨221784, by rfl⟩ : syracuseStep 591425 = 443569) B443569
theorem B394819 : Blo 393766 394819 := bstep (se 1 (by rfl) ⟨296114, by rfl⟩ : syracuseStep 394819 = 592229) B592229
theorem B591443 : Blo 393766 591443 := bstep (se 1 (by rfl) ⟨443582, by rfl⟩ : syracuseStep 591443 = 887165) B887165
theorem B394835 : Blo 393766 394835 := bstep (se 1 (by rfl) ⟨296126, by rfl⟩ : syracuseStep 394835 = 592253) B592253
theorem B394851 : Blo 393766 394851 := bstep (se 1 (by rfl) ⟨296138, by rfl⟩ : syracuseStep 394851 = 592277) B592277
theorem B591473 : Blo 393766 591473 := bstep (se 2 (by rfl) ⟨221802, by rfl⟩ : syracuseStep 591473 = 443605) B443605
theorem B394867 : Blo 393766 394867 := bstep (se 1 (by rfl) ⟨296150, by rfl⟩ : syracuseStep 394867 = 592301) B592301
theorem B591491 : Blo 393766 591491 := bstep (se 1 (by rfl) ⟨443618, by rfl⟩ : syracuseStep 591491 = 887237) B887237
theorem B394883 : Blo 393766 394883 := bstep (se 1 (by rfl) ⟨296162, by rfl⟩ : syracuseStep 394883 = 592325) B592325
theorem B394899 : Blo 393766 394899 := bstep (se 1 (by rfl) ⟨296174, by rfl⟩ : syracuseStep 394899 = 592349) B592349
theorem B591521 : Blo 393766 591521 := bstep (se 2 (by rfl) ⟨221820, by rfl⟩ : syracuseStep 591521 = 443641) B443641
theorem B394915 : Blo 393766 394915 := bstep (se 1 (by rfl) ⟨296186, by rfl⟩ : syracuseStep 394915 = 592373) B592373
theorem B591539 : Blo 393766 591539 := bstep (se 1 (by rfl) ⟨443654, by rfl⟩ : syracuseStep 591539 = 887309) B887309
theorem B394931 : Blo 393766 394931 := bstep (se 1 (by rfl) ⟨296198, by rfl⟩ : syracuseStep 394931 = 592397) B592397
theorem B394947 : Blo 393766 394947 := bstep (se 1 (by rfl) ⟨296210, by rfl⟩ : syracuseStep 394947 = 592421) B592421
theorem B2262725 : Blo 393766 2262725 := bstep (se 4 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 2262725 = 424261) B424261
theorem B886481 : Blo 393766 886481 := bstep (se 2 (by rfl) ⟨332430, by rfl⟩ : syracuseStep 886481 = 664861) B664861
theorem B591569 : Blo 393766 591569 := bstep (se 2 (by rfl) ⟨221838, by rfl⟩ : syracuseStep 591569 = 443677) B443677
theorem B394963 : Blo 393766 394963 := bstep (se 1 (by rfl) ⟨296222, by rfl⟩ : syracuseStep 394963 = 592445) B592445
theorem B886499 : Blo 393766 886499 := bstep (se 1 (by rfl) ⟨664874, by rfl⟩ : syracuseStep 886499 = 1329749) B1329749
theorem B591587 : Blo 393766 591587 := bstep (se 1 (by rfl) ⟨443690, by rfl⟩ : syracuseStep 591587 = 887381) B887381
theorem B394979 : Blo 393766 394979 := bstep (se 1 (by rfl) ⟨296234, by rfl⟩ : syracuseStep 394979 = 592469) B592469
theorem B394995 : Blo 393766 394995 := bstep (se 1 (by rfl) ⟨296246, by rfl⟩ : syracuseStep 394995 = 592493) B592493
theorem B591617 : Blo 393766 591617 := bstep (se 2 (by rfl) ⟨221856, by rfl⟩ : syracuseStep 591617 = 443713) B443713
theorem B395011 : Blo 393766 395011 := bstep (se 1 (by rfl) ⟨296258, by rfl⟩ : syracuseStep 395011 = 592517) B592517
theorem B591635 : Blo 393766 591635 := bstep (se 1 (by rfl) ⟨443726, by rfl⟩ : syracuseStep 591635 = 887453) B887453
theorem B395027 : Blo 393766 395027 := bstep (se 1 (by rfl) ⟨296270, by rfl⟩ : syracuseStep 395027 = 592541) B592541
theorem B395043 : Blo 393766 395043 := bstep (se 1 (by rfl) ⟨296282, by rfl⟩ : syracuseStep 395043 = 592565) B592565
theorem B591665 : Blo 393766 591665 := bstep (se 2 (by rfl) ⟨221874, by rfl⟩ : syracuseStep 591665 = 443749) B443749
theorem B395059 : Blo 393766 395059 := bstep (se 1 (by rfl) ⟨296294, by rfl⟩ : syracuseStep 395059 = 592589) B592589
theorem B591683 : Blo 393766 591683 := bstep (se 1 (by rfl) ⟨443762, by rfl⟩ : syracuseStep 591683 = 887525) B887525
theorem B395075 : Blo 393766 395075 := bstep (se 1 (by rfl) ⟨296306, by rfl⟩ : syracuseStep 395075 = 592613) B592613
theorem B395091 : Blo 393766 395091 := bstep (se 1 (by rfl) ⟨296318, by rfl⟩ : syracuseStep 395091 = 592637) B592637
theorem B591713 : Blo 393766 591713 := bstep (se 2 (by rfl) ⟨221892, by rfl⟩ : syracuseStep 591713 = 443785) B443785
theorem B395107 : Blo 393766 395107 := bstep (se 1 (by rfl) ⟨296330, by rfl⟩ : syracuseStep 395107 = 592661) B592661
theorem B591731 : Blo 393766 591731 := bstep (se 1 (by rfl) ⟨443798, by rfl⟩ : syracuseStep 591731 = 887597) B887597
theorem B395123 : Blo 393766 395123 := bstep (se 1 (by rfl) ⟨296342, by rfl⟩ : syracuseStep 395123 = 592685) B592685
theorem B395139 : Blo 393766 395139 := bstep (se 1 (by rfl) ⟨296354, by rfl⟩ : syracuseStep 395139 = 592709) B592709
theorem B591761 : Blo 393766 591761 := bstep (se 2 (by rfl) ⟨221910, by rfl⟩ : syracuseStep 591761 = 443821) B443821
theorem B395155 : Blo 393766 395155 := bstep (se 1 (by rfl) ⟨296366, by rfl⟩ : syracuseStep 395155 = 592733) B592733
theorem B591779 : Blo 393766 591779 := bstep (se 1 (by rfl) ⟨443834, by rfl⟩ : syracuseStep 591779 = 887669) B887669
theorem B395171 : Blo 393766 395171 := bstep (se 1 (by rfl) ⟨296378, by rfl⟩ : syracuseStep 395171 = 592757) B592757
theorem B395187 : Blo 393766 395187 := bstep (se 1 (by rfl) ⟨296390, by rfl⟩ : syracuseStep 395187 = 592781) B592781
theorem B591809 : Blo 393766 591809 := bstep (se 2 (by rfl) ⟨221928, by rfl⟩ : syracuseStep 591809 = 443857) B443857
theorem B395203 : Blo 393766 395203 := bstep (se 1 (by rfl) ⟨296402, by rfl⟩ : syracuseStep 395203 = 592805) B592805
theorem B591827 : Blo 393766 591827 := bstep (se 1 (by rfl) ⟨443870, by rfl⟩ : syracuseStep 591827 = 887741) B887741
theorem B395219 : Blo 393766 395219 := bstep (se 1 (by rfl) ⟨296414, by rfl⟩ : syracuseStep 395219 = 592829) B592829
theorem B395235 : Blo 393766 395235 := bstep (se 1 (by rfl) ⟨296426, by rfl⟩ : syracuseStep 395235 = 592853) B592853
theorem B886769 : Blo 393766 886769 := bstep (se 2 (by rfl) ⟨332538, by rfl⟩ : syracuseStep 886769 = 665077) B665077
theorem B591857 : Blo 393766 591857 := bstep (se 2 (by rfl) ⟨221946, by rfl⟩ : syracuseStep 591857 = 443893) B443893
theorem B395251 : Blo 393766 395251 := bstep (se 1 (by rfl) ⟨296438, by rfl⟩ : syracuseStep 395251 = 592877) B592877
theorem B886787 : Blo 393766 886787 := bstep (se 1 (by rfl) ⟨665090, by rfl⟩ : syracuseStep 886787 = 1330181) B1330181
theorem B591875 : Blo 393766 591875 := bstep (se 1 (by rfl) ⟨443906, by rfl⟩ : syracuseStep 591875 = 887813) B887813
theorem B395267 : Blo 393766 395267 := bstep (se 1 (by rfl) ⟨296450, by rfl⟩ : syracuseStep 395267 = 592901) B592901
theorem B395283 : Blo 393766 395283 := bstep (se 1 (by rfl) ⟨296462, by rfl⟩ : syracuseStep 395283 = 592925) B592925
theorem B591905 : Blo 393766 591905 := bstep (se 2 (by rfl) ⟨221964, by rfl⟩ : syracuseStep 591905 = 443929) B443929
theorem B395299 : Blo 393766 395299 := bstep (se 1 (by rfl) ⟨296474, by rfl⟩ : syracuseStep 395299 = 592949) B592949
theorem B1509425 : Blo 393766 1509425 := bstep (se 2 (by rfl) ⟨566034, by rfl⟩ : syracuseStep 1509425 = 1132069) B1132069
theorem B591923 : Blo 393766 591923 := bstep (se 1 (by rfl) ⟨443942, by rfl⟩ : syracuseStep 591923 = 887885) B887885
theorem B395315 : Blo 393766 395315 := bstep (se 1 (by rfl) ⟨296486, by rfl⟩ : syracuseStep 395315 = 592973) B592973
theorem B395331 : Blo 393766 395331 := bstep (se 1 (by rfl) ⟨296498, by rfl⟩ : syracuseStep 395331 = 592997) B592997
theorem B591953 : Blo 393766 591953 := bstep (se 2 (by rfl) ⟨221982, by rfl⟩ : syracuseStep 591953 = 443965) B443965
theorem B395347 : Blo 393766 395347 := bstep (se 1 (by rfl) ⟨296510, by rfl⟩ : syracuseStep 395347 = 593021) B593021
theorem B591971 : Blo 393766 591971 := bstep (se 1 (by rfl) ⟨443978, by rfl⟩ : syracuseStep 591971 = 887957) B887957
theorem B395363 : Blo 393766 395363 := bstep (se 1 (by rfl) ⟨296522, by rfl⟩ : syracuseStep 395363 = 593045) B593045
theorem B395379 : Blo 393766 395379 := bstep (se 1 (by rfl) ⟨296534, by rfl⟩ : syracuseStep 395379 = 593069) B593069
theorem B592001 : Blo 393766 592001 := bstep (se 2 (by rfl) ⟨222000, by rfl⟩ : syracuseStep 592001 = 444001) B444001
theorem B395395 : Blo 393766 395395 := bstep (se 1 (by rfl) ⟨296546, by rfl⟩ : syracuseStep 395395 = 593093) B593093
theorem B4524173 : Blo 393766 4524173 := bstep (se 3 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 4524173 = 1696565) B1696565
theorem B592019 : Blo 393766 592019 := bstep (se 1 (by rfl) ⟨444014, by rfl⟩ : syracuseStep 592019 = 888029) B888029
theorem B395411 : Blo 393766 395411 := bstep (se 1 (by rfl) ⟨296558, by rfl⟩ : syracuseStep 395411 = 593117) B593117
theorem B395427 : Blo 393766 395427 := bstep (se 1 (by rfl) ⟨296570, by rfl⟩ : syracuseStep 395427 = 593141) B593141
theorem B592049 : Blo 393766 592049 := bstep (se 2 (by rfl) ⟨222018, by rfl⟩ : syracuseStep 592049 = 444037) B444037
theorem B395443 : Blo 393766 395443 := bstep (se 1 (by rfl) ⟨296582, by rfl⟩ : syracuseStep 395443 = 593165) B593165
theorem B592067 : Blo 393766 592067 := bstep (se 1 (by rfl) ⟨444050, by rfl⟩ : syracuseStep 592067 = 888101) B888101
theorem B395459 : Blo 393766 395459 := bstep (se 1 (by rfl) ⟨296594, by rfl⟩ : syracuseStep 395459 = 593189) B593189
theorem B395475 : Blo 393766 395475 := bstep (se 1 (by rfl) ⟨296606, by rfl⟩ : syracuseStep 395475 = 593213) B593213
theorem B592097 : Blo 393766 592097 := bstep (se 2 (by rfl) ⟨222036, by rfl⟩ : syracuseStep 592097 = 444073) B444073
theorem B395491 : Blo 393766 395491 := bstep (se 1 (by rfl) ⟨296618, by rfl⟩ : syracuseStep 395491 = 593237) B593237
theorem B592115 : Blo 393766 592115 := bstep (se 1 (by rfl) ⟨444086, by rfl⟩ : syracuseStep 592115 = 888173) B888173
theorem B395507 : Blo 393766 395507 := bstep (se 1 (by rfl) ⟨296630, by rfl⟩ : syracuseStep 395507 = 593261) B593261
theorem B395523 : Blo 393766 395523 := bstep (se 1 (by rfl) ⟨296642, by rfl⟩ : syracuseStep 395523 = 593285) B593285
theorem B887057 : Blo 393766 887057 := bstep (se 2 (by rfl) ⟨332646, by rfl⟩ : syracuseStep 887057 = 665293) B665293
theorem B592145 : Blo 393766 592145 := bstep (se 2 (by rfl) ⟨222054, by rfl⟩ : syracuseStep 592145 = 444109) B444109
theorem B395539 : Blo 393766 395539 := bstep (se 1 (by rfl) ⟨296654, by rfl⟩ : syracuseStep 395539 = 593309) B593309
theorem B10455317 : Blo 393766 10455317 := bstep (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) B490093
theorem B887075 : Blo 393766 887075 := bstep (se 1 (by rfl) ⟨665306, by rfl⟩ : syracuseStep 887075 = 1330613) B1330613
theorem B592163 : Blo 393766 592163 := bstep (se 1 (by rfl) ⟨444122, by rfl⟩ : syracuseStep 592163 = 888245) B888245
theorem B395555 : Blo 393766 395555 := bstep (se 1 (by rfl) ⟨296666, by rfl⟩ : syracuseStep 395555 = 593333) B593333
theorem B395571 : Blo 393766 395571 := bstep (se 1 (by rfl) ⟨296678, by rfl⟩ : syracuseStep 395571 = 593357) B593357
theorem B592193 : Blo 393766 592193 := bstep (se 2 (by rfl) ⟨222072, by rfl⟩ : syracuseStep 592193 = 444145) B444145
theorem B395587 : Blo 393766 395587 := bstep (se 1 (by rfl) ⟨296690, by rfl⟩ : syracuseStep 395587 = 593381) B593381
theorem B592211 : Blo 393766 592211 := bstep (se 1 (by rfl) ⟨444158, by rfl⟩ : syracuseStep 592211 = 888317) B888317
theorem B395603 : Blo 393766 395603 := bstep (se 1 (by rfl) ⟨296702, by rfl⟩ : syracuseStep 395603 = 593405) B593405
theorem B395619 : Blo 393766 395619 := bstep (se 1 (by rfl) ⟨296714, by rfl⟩ : syracuseStep 395619 = 593429) B593429
theorem B5048689 : Blo 393766 5048689 := bstep (se 2 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 5048689 = 3786517) B3786517
theorem B592241 : Blo 393766 592241 := bstep (se 2 (by rfl) ⟨222090, by rfl⟩ : syracuseStep 592241 = 444181) B444181
theorem B395635 : Blo 393766 395635 := bstep (se 1 (by rfl) ⟨296726, by rfl⟩ : syracuseStep 395635 = 593453) B593453
theorem B2263409 : Blo 393766 2263409 := bstep (se 2 (by rfl) ⟨848778, by rfl⟩ : syracuseStep 2263409 = 1697557) B1697557
theorem B592259 : Blo 393766 592259 := bstep (se 1 (by rfl) ⟨444194, by rfl⟩ : syracuseStep 592259 = 888389) B888389
theorem B395651 : Blo 393766 395651 := bstep (se 1 (by rfl) ⟨296738, by rfl⟩ : syracuseStep 395651 = 593477) B593477
theorem B395667 : Blo 393766 395667 := bstep (se 1 (by rfl) ⟨296750, by rfl⟩ : syracuseStep 395667 = 593501) B593501
theorem B592289 : Blo 393766 592289 := bstep (se 2 (by rfl) ⟨222108, by rfl⟩ : syracuseStep 592289 = 444217) B444217
theorem B395683 : Blo 393766 395683 := bstep (se 1 (by rfl) ⟨296762, by rfl⟩ : syracuseStep 395683 = 593525) B593525
theorem B1608113 : Blo 393766 1608113 := bstep (se 2 (by rfl) ⟨603042, by rfl⟩ : syracuseStep 1608113 = 1206085) B1206085
theorem B592307 : Blo 393766 592307 := bstep (se 1 (by rfl) ⟨444230, by rfl⟩ : syracuseStep 592307 = 888461) B888461
theorem B395699 : Blo 393766 395699 := bstep (se 1 (by rfl) ⟨296774, by rfl⟩ : syracuseStep 395699 = 593549) B593549
theorem B395715 : Blo 393766 395715 := bstep (se 1 (by rfl) ⟨296786, by rfl⟩ : syracuseStep 395715 = 593573) B593573
theorem B592337 : Blo 393766 592337 := bstep (se 2 (by rfl) ⟨222126, by rfl⟩ : syracuseStep 592337 = 444253) B444253
theorem B395731 : Blo 393766 395731 := bstep (se 1 (by rfl) ⟨296798, by rfl⟩ : syracuseStep 395731 = 593597) B593597
theorem B592355 : Blo 393766 592355 := bstep (se 1 (by rfl) ⟨444266, by rfl⟩ : syracuseStep 592355 = 888533) B888533
theorem B395747 : Blo 393766 395747 := bstep (se 1 (by rfl) ⟨296810, by rfl⟩ : syracuseStep 395747 = 593621) B593621
theorem B1444337 : Blo 393766 1444337 := bstep (se 2 (by rfl) ⟨541626, by rfl⟩ : syracuseStep 1444337 = 1083253) B1083253
theorem B395763 : Blo 393766 395763 := bstep (se 1 (by rfl) ⟨296822, by rfl⟩ : syracuseStep 395763 = 593645) B593645
theorem B592385 : Blo 393766 592385 := bstep (se 2 (by rfl) ⟨222144, by rfl⟩ : syracuseStep 592385 = 444289) B444289
theorem B395779 : Blo 393766 395779 := bstep (se 1 (by rfl) ⟨296834, by rfl⟩ : syracuseStep 395779 = 593669) B593669
theorem B592403 : Blo 393766 592403 := bstep (se 1 (by rfl) ⟨444302, by rfl⟩ : syracuseStep 592403 = 888605) B888605
theorem B395795 : Blo 393766 395795 := bstep (se 1 (by rfl) ⟨296846, by rfl⟩ : syracuseStep 395795 = 593693) B593693
theorem B395811 : Blo 393766 395811 := bstep (se 1 (by rfl) ⟨296858, by rfl⟩ : syracuseStep 395811 = 593717) B593717
theorem B887345 : Blo 393766 887345 := bstep (se 2 (by rfl) ⟨332754, by rfl⟩ : syracuseStep 887345 = 665509) B665509
theorem B592433 : Blo 393766 592433 := bstep (se 2 (by rfl) ⟨222162, by rfl⟩ : syracuseStep 592433 = 444325) B444325
theorem B395827 : Blo 393766 395827 := bstep (se 1 (by rfl) ⟨296870, by rfl⟩ : syracuseStep 395827 = 593741) B593741
theorem B887363 : Blo 393766 887363 := bstep (se 1 (by rfl) ⟨665522, by rfl⟩ : syracuseStep 887363 = 1331045) B1331045
theorem B592451 : Blo 393766 592451 := bstep (se 1 (by rfl) ⟨444338, by rfl⟩ : syracuseStep 592451 = 888677) B888677
theorem B395843 : Blo 393766 395843 := bstep (se 1 (by rfl) ⟨296882, by rfl⟩ : syracuseStep 395843 = 593765) B593765
theorem B395859 : Blo 393766 395859 := bstep (se 1 (by rfl) ⟨296894, by rfl⟩ : syracuseStep 395859 = 593789) B593789
theorem B592481 : Blo 393766 592481 := bstep (se 2 (by rfl) ⟨222180, by rfl⟩ : syracuseStep 592481 = 444361) B444361
theorem B395875 : Blo 393766 395875 := bstep (se 1 (by rfl) ⟨296906, by rfl⟩ : syracuseStep 395875 = 593813) B593813
theorem B592499 : Blo 393766 592499 := bstep (se 1 (by rfl) ⟨444374, by rfl⟩ : syracuseStep 592499 = 888749) B888749
theorem B395891 : Blo 393766 395891 := bstep (se 1 (by rfl) ⟨296918, by rfl⟩ : syracuseStep 395891 = 593837) B593837
theorem B395907 : Blo 393766 395907 := bstep (se 1 (by rfl) ⟨296930, by rfl⟩ : syracuseStep 395907 = 593861) B593861
theorem B592529 : Blo 393766 592529 := bstep (se 2 (by rfl) ⟨222198, by rfl⟩ : syracuseStep 592529 = 444397) B444397
theorem B395923 : Blo 393766 395923 := bstep (se 1 (by rfl) ⟨296942, by rfl⟩ : syracuseStep 395923 = 593885) B593885
theorem B592547 : Blo 393766 592547 := bstep (se 1 (by rfl) ⟨444410, by rfl⟩ : syracuseStep 592547 = 888821) B888821
theorem B395939 : Blo 393766 395939 := bstep (se 1 (by rfl) ⟨296954, by rfl⟩ : syracuseStep 395939 = 593909) B593909
theorem B395955 : Blo 393766 395955 := bstep (se 1 (by rfl) ⟨296966, by rfl⟩ : syracuseStep 395955 = 593933) B593933
theorem B592577 : Blo 393766 592577 := bstep (se 2 (by rfl) ⟨222216, by rfl⟩ : syracuseStep 592577 = 444433) B444433
theorem B395971 : Blo 393766 395971 := bstep (se 1 (by rfl) ⟨296978, by rfl⟩ : syracuseStep 395971 = 593957) B593957
theorem B592595 : Blo 393766 592595 := bstep (se 1 (by rfl) ⟨444446, by rfl⟩ : syracuseStep 592595 = 888893) B888893
theorem B395987 : Blo 393766 395987 := bstep (se 1 (by rfl) ⟨296990, by rfl⟩ : syracuseStep 395987 = 593981) B593981
theorem B396003 : Blo 393766 396003 := bstep (se 1 (by rfl) ⟨297002, by rfl⟩ : syracuseStep 396003 = 594005) B594005
theorem B592625 : Blo 393766 592625 := bstep (se 2 (by rfl) ⟨222234, by rfl⟩ : syracuseStep 592625 = 444469) B444469
theorem B396019 : Blo 393766 396019 := bstep (se 1 (by rfl) ⟨297014, by rfl⟩ : syracuseStep 396019 = 594029) B594029
theorem B592643 : Blo 393766 592643 := bstep (se 1 (by rfl) ⟨444482, by rfl⟩ : syracuseStep 592643 = 888965) B888965
theorem B396035 : Blo 393766 396035 := bstep (se 1 (by rfl) ⟨297026, by rfl⟩ : syracuseStep 396035 = 594053) B594053
theorem B396051 : Blo 393766 396051 := bstep (se 1 (by rfl) ⟨297038, by rfl⟩ : syracuseStep 396051 = 594077) B594077
theorem B592673 : Blo 393766 592673 := bstep (se 2 (by rfl) ⟨222252, by rfl⟩ : syracuseStep 592673 = 444505) B444505
theorem B396067 : Blo 393766 396067 := bstep (se 1 (by rfl) ⟨297050, by rfl⟩ : syracuseStep 396067 = 594101) B594101
theorem B1903409 : Blo 393766 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B592691 : Blo 393766 592691 := bstep (se 1 (by rfl) ⟨444518, by rfl⟩ : syracuseStep 592691 = 889037) B889037
theorem B396083 : Blo 393766 396083 := bstep (se 1 (by rfl) ⟨297062, by rfl⟩ : syracuseStep 396083 = 594125) B594125
theorem B396099 : Blo 393766 396099 := bstep (se 1 (by rfl) ⟨297074, by rfl⟩ : syracuseStep 396099 = 594149) B594149
theorem B887633 : Blo 393766 887633 := bstep (se 2 (by rfl) ⟨332862, by rfl⟩ : syracuseStep 887633 = 665725) B665725
theorem B592721 : Blo 393766 592721 := bstep (se 2 (by rfl) ⟨222270, by rfl⟩ : syracuseStep 592721 = 444541) B444541
theorem B396115 : Blo 393766 396115 := bstep (se 1 (by rfl) ⟨297086, by rfl⟩ : syracuseStep 396115 = 594173) B594173
theorem B887651 : Blo 393766 887651 := bstep (se 1 (by rfl) ⟨665738, by rfl⟩ : syracuseStep 887651 = 1331477) B1331477
theorem B592739 : Blo 393766 592739 := bstep (se 1 (by rfl) ⟨444554, by rfl⟩ : syracuseStep 592739 = 889109) B889109
theorem B396131 : Blo 393766 396131 := bstep (se 1 (by rfl) ⟨297098, by rfl⟩ : syracuseStep 396131 = 594197) B594197
theorem B396147 : Blo 393766 396147 := bstep (se 1 (by rfl) ⟨297110, by rfl⟩ : syracuseStep 396147 = 594221) B594221
theorem B592769 : Blo 393766 592769 := bstep (se 2 (by rfl) ⟨222288, by rfl⟩ : syracuseStep 592769 = 444577) B444577
theorem B396163 : Blo 393766 396163 := bstep (se 1 (by rfl) ⟨297122, by rfl⟩ : syracuseStep 396163 = 594245) B594245
theorem B592787 : Blo 393766 592787 := bstep (se 1 (by rfl) ⟨444590, by rfl⟩ : syracuseStep 592787 = 889181) B889181
theorem B396179 : Blo 393766 396179 := bstep (se 1 (by rfl) ⟨297134, by rfl⟩ : syracuseStep 396179 = 594269) B594269
theorem B396195 : Blo 393766 396195 := bstep (se 1 (by rfl) ⟨297146, by rfl⟩ : syracuseStep 396195 = 594293) B594293
theorem B592817 : Blo 393766 592817 := bstep (se 2 (by rfl) ⟨222306, by rfl⟩ : syracuseStep 592817 = 444613) B444613
theorem B396211 : Blo 393766 396211 := bstep (se 1 (by rfl) ⟨297158, by rfl⟩ : syracuseStep 396211 = 594317) B594317
theorem B592835 : Blo 393766 592835 := bstep (se 1 (by rfl) ⟨444626, by rfl⟩ : syracuseStep 592835 = 889253) B889253
theorem B396227 : Blo 393766 396227 := bstep (se 1 (by rfl) ⟨297170, by rfl⟩ : syracuseStep 396227 = 594341) B594341
theorem B396243 : Blo 393766 396243 := bstep (se 1 (by rfl) ⟨297182, by rfl⟩ : syracuseStep 396243 = 594365) B594365
theorem B592865 : Blo 393766 592865 := bstep (se 2 (by rfl) ⟨222324, by rfl⟩ : syracuseStep 592865 = 444649) B444649
theorem B396259 : Blo 393766 396259 := bstep (se 1 (by rfl) ⟨297194, by rfl⟩ : syracuseStep 396259 = 594389) B594389
theorem B1903601 : Blo 393766 1903601 := bstep (se 2 (by rfl) ⟨713850, by rfl⟩ : syracuseStep 1903601 = 1427701) B1427701
theorem B592883 : Blo 393766 592883 := bstep (se 1 (by rfl) ⟨444662, by rfl⟩ : syracuseStep 592883 = 889325) B889325
theorem B396275 : Blo 393766 396275 := bstep (se 1 (by rfl) ⟨297206, by rfl⟩ : syracuseStep 396275 = 594413) B594413
theorem B855043 : Blo 393766 855043 := bstep (se 1 (by rfl) ⟨641282, by rfl⟩ : syracuseStep 855043 = 1282565) B1282565
theorem B396291 : Blo 393766 396291 := bstep (se 1 (by rfl) ⟨297218, by rfl⟩ : syracuseStep 396291 = 594437) B594437
theorem B592913 : Blo 393766 592913 := bstep (se 2 (by rfl) ⟨222342, by rfl⟩ : syracuseStep 592913 = 444685) B444685
theorem B396307 : Blo 393766 396307 := bstep (se 1 (by rfl) ⟨297230, by rfl⟩ : syracuseStep 396307 = 594461) B594461
theorem B1281059 : Blo 393766 1281059 := bstep (se 1 (by rfl) ⟨960794, by rfl⟩ : syracuseStep 1281059 = 1921589) B1921589
theorem B592931 : Blo 393766 592931 := bstep (se 1 (by rfl) ⟨444698, by rfl⟩ : syracuseStep 592931 = 889397) B889397
theorem B396323 : Blo 393766 396323 := bstep (se 1 (by rfl) ⟨297242, by rfl⟩ : syracuseStep 396323 = 594485) B594485
theorem B396339 : Blo 393766 396339 := bstep (se 1 (by rfl) ⟨297254, by rfl⟩ : syracuseStep 396339 = 594509) B594509
theorem B592961 : Blo 393766 592961 := bstep (se 2 (by rfl) ⟨222360, by rfl⟩ : syracuseStep 592961 = 444721) B444721
theorem B396355 : Blo 393766 396355 := bstep (se 1 (by rfl) ⟨297266, by rfl⟩ : syracuseStep 396355 = 594533) B594533
theorem B592979 : Blo 393766 592979 := bstep (se 1 (by rfl) ⟨444734, by rfl⟩ : syracuseStep 592979 = 889469) B889469
theorem B396371 : Blo 393766 396371 := bstep (se 1 (by rfl) ⟨297278, by rfl⟩ : syracuseStep 396371 = 594557) B594557
theorem B396387 : Blo 393766 396387 := bstep (se 1 (by rfl) ⟨297290, by rfl⟩ : syracuseStep 396387 = 594581) B594581
theorem B887921 : Blo 393766 887921 := bstep (se 2 (by rfl) ⟨332970, by rfl⟩ : syracuseStep 887921 = 665941) B665941
theorem B593009 : Blo 393766 593009 := bstep (se 2 (by rfl) ⟨222378, by rfl⟩ : syracuseStep 593009 = 444757) B444757
theorem B396403 : Blo 393766 396403 := bstep (se 1 (by rfl) ⟨297302, by rfl⟩ : syracuseStep 396403 = 594605) B594605
theorem B887939 : Blo 393766 887939 := bstep (se 1 (by rfl) ⟨665954, by rfl⟩ : syracuseStep 887939 = 1331909) B1331909
theorem B593027 : Blo 393766 593027 := bstep (se 1 (by rfl) ⟨444770, by rfl⟩ : syracuseStep 593027 = 889541) B889541
theorem B396419 : Blo 393766 396419 := bstep (se 1 (by rfl) ⟨297314, by rfl⟩ : syracuseStep 396419 = 594629) B594629
theorem B396435 : Blo 393766 396435 := bstep (se 1 (by rfl) ⟨297326, by rfl⟩ : syracuseStep 396435 = 594653) B594653
theorem B593057 : Blo 393766 593057 := bstep (se 2 (by rfl) ⟨222396, by rfl⟩ : syracuseStep 593057 = 444793) B444793
theorem B396451 : Blo 393766 396451 := bstep (se 1 (by rfl) ⟨297338, by rfl⟩ : syracuseStep 396451 = 594677) B594677
theorem B593075 : Blo 393766 593075 := bstep (se 1 (by rfl) ⟨444806, by rfl⟩ : syracuseStep 593075 = 889613) B889613
theorem B396467 : Blo 393766 396467 := bstep (se 1 (by rfl) ⟨297350, by rfl⟩ : syracuseStep 396467 = 594701) B594701
theorem B396483 : Blo 393766 396483 := bstep (se 1 (by rfl) ⟨297362, by rfl⟩ : syracuseStep 396483 = 594725) B594725
theorem B593105 : Blo 393766 593105 := bstep (se 2 (by rfl) ⟨222414, by rfl⟩ : syracuseStep 593105 = 444829) B444829
theorem B396499 : Blo 393766 396499 := bstep (se 1 (by rfl) ⟨297374, by rfl⟩ : syracuseStep 396499 = 594749) B594749
theorem B593123 : Blo 393766 593123 := bstep (se 1 (by rfl) ⟨444842, by rfl⟩ : syracuseStep 593123 = 889685) B889685
theorem B396515 : Blo 393766 396515 := bstep (se 1 (by rfl) ⟨297386, by rfl⟩ : syracuseStep 396515 = 594773) B594773
theorem B396531 : Blo 393766 396531 := bstep (se 1 (by rfl) ⟨297398, by rfl⟩ : syracuseStep 396531 = 594797) B594797
theorem B593153 : Blo 393766 593153 := bstep (se 2 (by rfl) ⟨222432, by rfl⟩ : syracuseStep 593153 = 444865) B444865
theorem B396547 : Blo 393766 396547 := bstep (se 1 (by rfl) ⟨297410, by rfl⟩ : syracuseStep 396547 = 594821) B594821
theorem B593171 : Blo 393766 593171 := bstep (se 1 (by rfl) ⟨444878, by rfl⟩ : syracuseStep 593171 = 889757) B889757
theorem B396563 : Blo 393766 396563 := bstep (se 1 (by rfl) ⟨297422, by rfl⟩ : syracuseStep 396563 = 594845) B594845
theorem B396579 : Blo 393766 396579 := bstep (se 1 (by rfl) ⟨297434, by rfl⟩ : syracuseStep 396579 = 594869) B594869
theorem B593201 : Blo 393766 593201 := bstep (se 2 (by rfl) ⟨222450, by rfl⟩ : syracuseStep 593201 = 444901) B444901
theorem B396595 : Blo 393766 396595 := bstep (se 1 (by rfl) ⟨297446, by rfl⟩ : syracuseStep 396595 = 594893) B594893
theorem B593219 : Blo 393766 593219 := bstep (se 1 (by rfl) ⟨444914, by rfl⟩ : syracuseStep 593219 = 889829) B889829
theorem B396611 : Blo 393766 396611 := bstep (se 1 (by rfl) ⟨297458, by rfl⟩ : syracuseStep 396611 = 594917) B594917
theorem B396627 : Blo 393766 396627 := bstep (se 1 (by rfl) ⟨297470, by rfl⟩ : syracuseStep 396627 = 594941) B594941
theorem B593249 : Blo 393766 593249 := bstep (se 2 (by rfl) ⟨222468, by rfl⟩ : syracuseStep 593249 = 444937) B444937
theorem B2035043 : Blo 393766 2035043 := bstep (se 1 (by rfl) ⟨1526282, by rfl⟩ : syracuseStep 2035043 = 3052565) B3052565
theorem B396643 : Blo 393766 396643 := bstep (se 1 (by rfl) ⟨297482, by rfl⟩ : syracuseStep 396643 = 594965) B594965
theorem B593267 : Blo 393766 593267 := bstep (se 1 (by rfl) ⟨444950, by rfl⟩ : syracuseStep 593267 = 889901) B889901
theorem B396659 : Blo 393766 396659 := bstep (se 1 (by rfl) ⟨297494, by rfl⟩ : syracuseStep 396659 = 594989) B594989
theorem B396675 : Blo 393766 396675 := bstep (se 1 (by rfl) ⟨297506, by rfl⟩ : syracuseStep 396675 = 595013) B595013
theorem B888209 : Blo 393766 888209 := bstep (se 2 (by rfl) ⟨333078, by rfl⟩ : syracuseStep 888209 = 666157) B666157
theorem B593297 : Blo 393766 593297 := bstep (se 2 (by rfl) ⟨222486, by rfl⟩ : syracuseStep 593297 = 444973) B444973
theorem B396691 : Blo 393766 396691 := bstep (se 1 (by rfl) ⟨297518, by rfl⟩ : syracuseStep 396691 = 595037) B595037
theorem B888227 : Blo 393766 888227 := bstep (se 1 (by rfl) ⟨666170, by rfl⟩ : syracuseStep 888227 = 1332341) B1332341
theorem B593315 : Blo 393766 593315 := bstep (se 1 (by rfl) ⟨444986, by rfl⟩ : syracuseStep 593315 = 889973) B889973
theorem B396707 : Blo 393766 396707 := bstep (se 1 (by rfl) ⟨297530, by rfl⟩ : syracuseStep 396707 = 595061) B595061
theorem B396723 : Blo 393766 396723 := bstep (se 1 (by rfl) ⟨297542, by rfl⟩ : syracuseStep 396723 = 595085) B595085
theorem B593345 : Blo 393766 593345 := bstep (se 2 (by rfl) ⟨222504, by rfl⟩ : syracuseStep 593345 = 445009) B445009
theorem B396739 : Blo 393766 396739 := bstep (se 1 (by rfl) ⟨297554, by rfl⟩ : syracuseStep 396739 = 595109) B595109
theorem B593363 : Blo 393766 593363 := bstep (se 1 (by rfl) ⟨445022, by rfl⟩ : syracuseStep 593363 = 890045) B890045
theorem B396755 : Blo 393766 396755 := bstep (se 1 (by rfl) ⟨297566, by rfl⟩ : syracuseStep 396755 = 595133) B595133
theorem B396771 : Blo 393766 396771 := bstep (se 1 (by rfl) ⟨297578, by rfl⟩ : syracuseStep 396771 = 595157) B595157
theorem B593393 : Blo 393766 593393 := bstep (se 2 (by rfl) ⟨222522, by rfl⟩ : syracuseStep 593393 = 445045) B445045
theorem B396787 : Blo 393766 396787 := bstep (se 1 (by rfl) ⟨297590, by rfl⟩ : syracuseStep 396787 = 595181) B595181
theorem B593411 : Blo 393766 593411 := bstep (se 1 (by rfl) ⟨445058, by rfl⟩ : syracuseStep 593411 = 890117) B890117
theorem B396803 : Blo 393766 396803 := bstep (se 1 (by rfl) ⟨297602, by rfl⟩ : syracuseStep 396803 = 595205) B595205
theorem B396819 : Blo 393766 396819 := bstep (se 1 (by rfl) ⟨297614, by rfl⟩ : syracuseStep 396819 = 595229) B595229
theorem B593441 : Blo 393766 593441 := bstep (se 2 (by rfl) ⟨222540, by rfl⟩ : syracuseStep 593441 = 445081) B445081
theorem B396835 : Blo 393766 396835 := bstep (se 1 (by rfl) ⟨297626, by rfl⟩ : syracuseStep 396835 = 595253) B595253
theorem B2002481 : Blo 393766 2002481 := bstep (se 2 (by rfl) ⟨750930, by rfl⟩ : syracuseStep 2002481 = 1501861) B1501861
theorem B593459 : Blo 393766 593459 := bstep (se 1 (by rfl) ⟨445094, by rfl⟩ : syracuseStep 593459 = 890189) B890189
theorem B396851 : Blo 393766 396851 := bstep (se 1 (by rfl) ⟨297638, by rfl⟩ : syracuseStep 396851 = 595277) B595277
theorem B396867 : Blo 393766 396867 := bstep (se 1 (by rfl) ⟨297650, by rfl⟩ : syracuseStep 396867 = 595301) B595301
theorem B593489 : Blo 393766 593489 := bstep (se 2 (by rfl) ⟨222558, by rfl⟩ : syracuseStep 593489 = 445117) B445117
theorem B396883 : Blo 393766 396883 := bstep (se 1 (by rfl) ⟨297662, by rfl⟩ : syracuseStep 396883 = 595325) B595325
theorem B593507 : Blo 393766 593507 := bstep (se 1 (by rfl) ⟨445130, by rfl⟩ : syracuseStep 593507 = 890261) B890261
theorem B396899 : Blo 393766 396899 := bstep (se 1 (by rfl) ⟨297674, by rfl⟩ : syracuseStep 396899 = 595349) B595349
theorem B396915 : Blo 393766 396915 := bstep (se 1 (by rfl) ⟨297686, by rfl⟩ : syracuseStep 396915 = 595373) B595373
theorem B429683 : Blo 393766 429683 := bstep (se 1 (by rfl) ⟨322262, by rfl⟩ : syracuseStep 429683 = 644525) B644525
theorem B593537 : Blo 393766 593537 := bstep (se 2 (by rfl) ⟨222576, by rfl⟩ : syracuseStep 593537 = 445153) B445153
theorem B396931 : Blo 393766 396931 := bstep (se 1 (by rfl) ⟨297698, by rfl⟩ : syracuseStep 396931 = 595397) B595397
theorem B593555 : Blo 393766 593555 := bstep (se 1 (by rfl) ⟨445166, by rfl⟩ : syracuseStep 593555 = 890333) B890333
theorem B396947 : Blo 393766 396947 := bstep (se 1 (by rfl) ⟨297710, by rfl⟩ : syracuseStep 396947 = 595421) B595421
theorem B396963 : Blo 393766 396963 := bstep (se 1 (by rfl) ⟨297722, by rfl⟩ : syracuseStep 396963 = 595445) B595445
theorem B888497 : Blo 393766 888497 := bstep (se 2 (by rfl) ⟨333186, by rfl⟩ : syracuseStep 888497 = 666373) B666373
theorem B593585 : Blo 393766 593585 := bstep (se 2 (by rfl) ⟨222594, by rfl⟩ : syracuseStep 593585 = 445189) B445189
theorem B396979 : Blo 393766 396979 := bstep (se 1 (by rfl) ⟨297734, by rfl⟩ : syracuseStep 396979 = 595469) B595469
theorem B888515 : Blo 393766 888515 := bstep (se 1 (by rfl) ⟨666386, by rfl⟩ : syracuseStep 888515 = 1332773) B1332773
theorem B593603 : Blo 393766 593603 := bstep (se 1 (by rfl) ⟨445202, by rfl⟩ : syracuseStep 593603 = 890405) B890405
theorem B396995 : Blo 393766 396995 := bstep (se 1 (by rfl) ⟨297746, by rfl⟩ : syracuseStep 396995 = 595493) B595493
theorem B397011 : Blo 393766 397011 := bstep (se 1 (by rfl) ⟨297758, by rfl⟩ : syracuseStep 397011 = 595517) B595517
theorem B593633 : Blo 393766 593633 := bstep (se 2 (by rfl) ⟨222612, by rfl⟩ : syracuseStep 593633 = 445225) B445225
theorem B397027 : Blo 393766 397027 := bstep (se 1 (by rfl) ⟨297770, by rfl⟩ : syracuseStep 397027 = 595541) B595541
theorem B593651 : Blo 393766 593651 := bstep (se 1 (by rfl) ⟨445238, by rfl⟩ : syracuseStep 593651 = 890477) B890477
theorem B397043 : Blo 393766 397043 := bstep (se 1 (by rfl) ⟨297782, by rfl⟩ : syracuseStep 397043 = 595565) B595565
theorem B397059 : Blo 393766 397059 := bstep (se 1 (by rfl) ⟨297794, by rfl⟩ : syracuseStep 397059 = 595589) B595589
theorem B593681 : Blo 393766 593681 := bstep (se 2 (by rfl) ⟨222630, by rfl⟩ : syracuseStep 593681 = 445261) B445261
theorem B397075 : Blo 393766 397075 := bstep (se 1 (by rfl) ⟨297806, by rfl⟩ : syracuseStep 397075 = 595613) B595613
theorem B593699 : Blo 393766 593699 := bstep (se 1 (by rfl) ⟨445274, by rfl⟩ : syracuseStep 593699 = 890549) B890549
theorem B397091 : Blo 393766 397091 := bstep (se 1 (by rfl) ⟨297818, by rfl⟩ : syracuseStep 397091 = 595637) B595637
theorem B2264867 : Blo 393766 2264867 := bstep (se 1 (by rfl) ⟨1698650, by rfl⟩ : syracuseStep 2264867 = 3397301) B3397301
theorem B397107 : Blo 393766 397107 := bstep (se 1 (by rfl) ⟨297830, by rfl⟩ : syracuseStep 397107 = 595661) B595661
theorem B593729 : Blo 393766 593729 := bstep (se 2 (by rfl) ⟨222648, by rfl⟩ : syracuseStep 593729 = 445297) B445297
theorem B397123 : Blo 393766 397123 := bstep (se 1 (by rfl) ⟨297842, by rfl⟩ : syracuseStep 397123 = 595685) B595685
theorem B593747 : Blo 393766 593747 := bstep (se 1 (by rfl) ⟨445310, by rfl⟩ : syracuseStep 593747 = 890621) B890621
theorem B397139 : Blo 393766 397139 := bstep (se 1 (by rfl) ⟨297854, by rfl⟩ : syracuseStep 397139 = 595709) B595709
theorem B397155 : Blo 393766 397155 := bstep (se 1 (by rfl) ⟨297866, by rfl⟩ : syracuseStep 397155 = 595733) B595733
theorem B593777 : Blo 393766 593777 := bstep (se 2 (by rfl) ⟨222666, by rfl⟩ : syracuseStep 593777 = 445333) B445333
theorem B561011 : Blo 393766 561011 := bstep (se 1 (by rfl) ⟨420758, by rfl⟩ : syracuseStep 561011 = 841517) B841517
theorem B397171 : Blo 393766 397171 := bstep (se 1 (by rfl) ⟨297878, by rfl⟩ : syracuseStep 397171 = 595757) B595757
theorem B593795 : Blo 393766 593795 := bstep (se 1 (by rfl) ⟨445346, by rfl⟩ : syracuseStep 593795 = 890693) B890693
theorem B397187 : Blo 393766 397187 := bstep (se 1 (by rfl) ⟨297890, by rfl⟩ : syracuseStep 397187 = 595781) B595781
theorem B397203 : Blo 393766 397203 := bstep (se 1 (by rfl) ⟨297902, by rfl⟩ : syracuseStep 397203 = 595805) B595805
theorem B593825 : Blo 393766 593825 := bstep (se 2 (by rfl) ⟨222684, by rfl⟩ : syracuseStep 593825 = 445369) B445369
theorem B397219 : Blo 393766 397219 := bstep (se 1 (by rfl) ⟨297914, by rfl⟩ : syracuseStep 397219 = 595829) B595829
theorem B593843 : Blo 393766 593843 := bstep (se 1 (by rfl) ⟨445382, by rfl⟩ : syracuseStep 593843 = 890765) B890765
theorem B397235 : Blo 393766 397235 := bstep (se 1 (by rfl) ⟨297926, by rfl⟩ : syracuseStep 397235 = 595853) B595853
theorem B397251 : Blo 393766 397251 := bstep (se 1 (by rfl) ⟨297938, by rfl⟩ : syracuseStep 397251 = 595877) B595877
theorem B888785 : Blo 393766 888785 := bstep (se 2 (by rfl) ⟨333294, by rfl⟩ : syracuseStep 888785 = 666589) B666589
theorem B593873 : Blo 393766 593873 := bstep (se 2 (by rfl) ⟨222702, by rfl⟩ : syracuseStep 593873 = 445405) B445405
theorem B397267 : Blo 393766 397267 := bstep (se 1 (by rfl) ⟨297950, by rfl⟩ : syracuseStep 397267 = 595901) B595901
theorem B888803 : Blo 393766 888803 := bstep (se 1 (by rfl) ⟨666602, by rfl⟩ : syracuseStep 888803 = 1333205) B1333205
theorem B593891 : Blo 393766 593891 := bstep (se 1 (by rfl) ⟨445418, by rfl⟩ : syracuseStep 593891 = 890837) B890837
theorem B397283 : Blo 393766 397283 := bstep (se 1 (by rfl) ⟨297962, by rfl⟩ : syracuseStep 397283 = 595925) B595925
theorem B397299 : Blo 393766 397299 := bstep (se 1 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 397299 = 595949) B595949
theorem B593921 : Blo 393766 593921 := bstep (se 2 (by rfl) ⟨222720, by rfl⟩ : syracuseStep 593921 = 445441) B445441
theorem B397315 : Blo 393766 397315 := bstep (se 1 (by rfl) ⟨297986, by rfl⟩ : syracuseStep 397315 = 595973) B595973
theorem B593939 : Blo 393766 593939 := bstep (se 1 (by rfl) ⟨445454, by rfl⟩ : syracuseStep 593939 = 890909) B890909
theorem B397331 : Blo 393766 397331 := bstep (se 1 (by rfl) ⟨297998, by rfl⟩ : syracuseStep 397331 = 595997) B595997
theorem B397347 : Blo 393766 397347 := bstep (se 1 (by rfl) ⟨298010, by rfl⟩ : syracuseStep 397347 = 596021) B596021
theorem B593969 : Blo 393766 593969 := bstep (se 2 (by rfl) ⟨222738, by rfl⟩ : syracuseStep 593969 = 445477) B445477
theorem B397363 : Blo 393766 397363 := bstep (se 1 (by rfl) ⟨298022, by rfl⟩ : syracuseStep 397363 = 596045) B596045
theorem B593987 : Blo 393766 593987 := bstep (se 1 (by rfl) ⟨445490, by rfl⟩ : syracuseStep 593987 = 890981) B890981
theorem B397379 : Blo 393766 397379 := bstep (se 1 (by rfl) ⟨298034, by rfl⟩ : syracuseStep 397379 = 596069) B596069
theorem B397395 : Blo 393766 397395 := bstep (se 1 (by rfl) ⟨298046, by rfl⟩ : syracuseStep 397395 = 596093) B596093
theorem B594017 : Blo 393766 594017 := bstep (se 2 (by rfl) ⟨222756, by rfl⟩ : syracuseStep 594017 = 445513) B445513
theorem B397411 : Blo 393766 397411 := bstep (se 1 (by rfl) ⟨298058, by rfl⟩ : syracuseStep 397411 = 596117) B596117
theorem B594035 : Blo 393766 594035 := bstep (se 1 (by rfl) ⟨445526, by rfl⟩ : syracuseStep 594035 = 891053) B891053
theorem B397427 : Blo 393766 397427 := bstep (se 1 (by rfl) ⟨298070, by rfl⟩ : syracuseStep 397427 = 596141) B596141
theorem B397443 : Blo 393766 397443 := bstep (se 1 (by rfl) ⟨298082, by rfl⟩ : syracuseStep 397443 = 596165) B596165
theorem B594065 : Blo 393766 594065 := bstep (se 2 (by rfl) ⟨222774, by rfl⟩ : syracuseStep 594065 = 445549) B445549
theorem B397459 : Blo 393766 397459 := bstep (se 1 (by rfl) ⟨298094, by rfl⟩ : syracuseStep 397459 = 596189) B596189
theorem B594083 : Blo 393766 594083 := bstep (se 1 (by rfl) ⟨445562, by rfl⟩ : syracuseStep 594083 = 891125) B891125
theorem B397475 : Blo 393766 397475 := bstep (se 1 (by rfl) ⟨298106, by rfl⟩ : syracuseStep 397475 = 596213) B596213
theorem B397491 : Blo 393766 397491 := bstep (se 1 (by rfl) ⟨298118, by rfl⟩ : syracuseStep 397491 = 596237) B596237
theorem B594113 : Blo 393766 594113 := bstep (se 2 (by rfl) ⟨222792, by rfl⟩ : syracuseStep 594113 = 445585) B445585
theorem B397507 : Blo 393766 397507 := bstep (se 1 (by rfl) ⟨298130, by rfl⟩ : syracuseStep 397507 = 596261) B596261
theorem B594131 : Blo 393766 594131 := bstep (se 1 (by rfl) ⟨445598, by rfl⟩ : syracuseStep 594131 = 891197) B891197
theorem B397523 : Blo 393766 397523 := bstep (se 1 (by rfl) ⟨298142, by rfl⟩ : syracuseStep 397523 = 596285) B596285
theorem B397539 : Blo 393766 397539 := bstep (se 1 (by rfl) ⟨298154, by rfl⟩ : syracuseStep 397539 = 596309) B596309
theorem B889073 : Blo 393766 889073 := bstep (se 2 (by rfl) ⟨333402, by rfl⟩ : syracuseStep 889073 = 666805) B666805
theorem B594161 : Blo 393766 594161 := bstep (se 2 (by rfl) ⟨222810, by rfl⟩ : syracuseStep 594161 = 445621) B445621
theorem B397555 : Blo 393766 397555 := bstep (se 1 (by rfl) ⟨298166, by rfl⟩ : syracuseStep 397555 = 596333) B596333
theorem B889091 : Blo 393766 889091 := bstep (se 1 (by rfl) ⟨666818, by rfl⟩ : syracuseStep 889091 = 1333637) B1333637
theorem B594179 : Blo 393766 594179 := bstep (se 1 (by rfl) ⟨445634, by rfl⟩ : syracuseStep 594179 = 891269) B891269
theorem B397571 : Blo 393766 397571 := bstep (se 1 (by rfl) ⟨298178, by rfl⟩ : syracuseStep 397571 = 596357) B596357
theorem B397587 : Blo 393766 397587 := bstep (se 1 (by rfl) ⟨298190, by rfl⟩ : syracuseStep 397587 = 596381) B596381
theorem B594209 : Blo 393766 594209 := bstep (se 2 (by rfl) ⟨222828, by rfl⟩ : syracuseStep 594209 = 445657) B445657
theorem B397603 : Blo 393766 397603 := bstep (se 1 (by rfl) ⟨298202, by rfl⟩ : syracuseStep 397603 = 596405) B596405
theorem B594227 : Blo 393766 594227 := bstep (se 1 (by rfl) ⟨445670, by rfl⟩ : syracuseStep 594227 = 891341) B891341
theorem B397619 : Blo 393766 397619 := bstep (se 1 (by rfl) ⟨298214, by rfl⟩ : syracuseStep 397619 = 596429) B596429
theorem B397635 : Blo 393766 397635 := bstep (se 1 (by rfl) ⟨298226, by rfl⟩ : syracuseStep 397635 = 596453) B596453
theorem B594257 : Blo 393766 594257 := bstep (se 2 (by rfl) ⟨222846, by rfl⟩ : syracuseStep 594257 = 445693) B445693
theorem B397651 : Blo 393766 397651 := bstep (se 1 (by rfl) ⟨298238, by rfl⟩ : syracuseStep 397651 = 596477) B596477
theorem B594275 : Blo 393766 594275 := bstep (se 1 (by rfl) ⟨445706, by rfl⟩ : syracuseStep 594275 = 891413) B891413
theorem B397667 : Blo 393766 397667 := bstep (se 1 (by rfl) ⟨298250, by rfl⟩ : syracuseStep 397667 = 596501) B596501
theorem B397683 : Blo 393766 397683 := bstep (se 1 (by rfl) ⟨298262, by rfl⟩ : syracuseStep 397683 = 596525) B596525
theorem B594305 : Blo 393766 594305 := bstep (se 2 (by rfl) ⟨222864, by rfl⟩ : syracuseStep 594305 = 445729) B445729
theorem B397699 : Blo 393766 397699 := bstep (se 1 (by rfl) ⟨298274, by rfl⟩ : syracuseStep 397699 = 596549) B596549
theorem B594323 : Blo 393766 594323 := bstep (se 1 (by rfl) ⟨445742, by rfl⟩ : syracuseStep 594323 = 891485) B891485
theorem B397715 : Blo 393766 397715 := bstep (se 1 (by rfl) ⟨298286, by rfl⟩ : syracuseStep 397715 = 596573) B596573
theorem B397731 : Blo 393766 397731 := bstep (se 1 (by rfl) ⟨298298, by rfl⟩ : syracuseStep 397731 = 596597) B596597
theorem B594353 : Blo 393766 594353 := bstep (se 2 (by rfl) ⟨222882, by rfl⟩ : syracuseStep 594353 = 445765) B445765
theorem B397747 : Blo 393766 397747 := bstep (se 1 (by rfl) ⟨298310, by rfl⟩ : syracuseStep 397747 = 596621) B596621
theorem B627139 : Blo 393766 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B594371 : Blo 393766 594371 := bstep (se 1 (by rfl) ⟨445778, by rfl⟩ : syracuseStep 594371 = 891557) B891557
theorem B397763 : Blo 393766 397763 := bstep (se 1 (by rfl) ⟨298322, by rfl⟩ : syracuseStep 397763 = 596645) B596645
theorem B594401 : Blo 393766 594401 := bstep (se 2 (by rfl) ⟨222900, by rfl⟩ : syracuseStep 594401 = 445801) B445801
theorem B561649 : Blo 393766 561649 := bstep (se 2 (by rfl) ⟨210618, by rfl⟩ : syracuseStep 561649 = 421237) B421237
theorem B594419 : Blo 393766 594419 := bstep (se 1 (by rfl) ⟨445814, by rfl⟩ : syracuseStep 594419 = 891629) B891629
theorem B889361 : Blo 393766 889361 := bstep (se 2 (by rfl) ⟨333510, by rfl⟩ : syracuseStep 889361 = 667021) B667021
theorem B594449 : Blo 393766 594449 := bstep (se 2 (by rfl) ⟨222918, by rfl⟩ : syracuseStep 594449 = 445837) B445837
theorem B889379 : Blo 393766 889379 := bstep (se 1 (by rfl) ⟨667034, by rfl⟩ : syracuseStep 889379 = 1334069) B1334069
theorem B594467 : Blo 393766 594467 := bstep (se 1 (by rfl) ⟨445850, by rfl⟩ : syracuseStep 594467 = 891701) B891701
theorem B594497 : Blo 393766 594497 := bstep (se 2 (by rfl) ⟨222936, by rfl⟩ : syracuseStep 594497 = 445873) B445873
theorem B594515 : Blo 393766 594515 := bstep (se 1 (by rfl) ⟨445886, by rfl⟩ : syracuseStep 594515 = 891773) B891773
theorem B561763 : Blo 393766 561763 := bstep (se 1 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 561763 = 842645) B842645
theorem B594545 : Blo 393766 594545 := bstep (se 2 (by rfl) ⟨222954, by rfl⟩ : syracuseStep 594545 = 445909) B445909
theorem B594563 : Blo 393766 594563 := bstep (se 1 (by rfl) ⟨445922, by rfl⟩ : syracuseStep 594563 = 891845) B891845
theorem B594593 : Blo 393766 594593 := bstep (se 2 (by rfl) ⟨222972, by rfl⟩ : syracuseStep 594593 = 445945) B445945
theorem B594611 : Blo 393766 594611 := bstep (se 1 (by rfl) ⟨445958, by rfl⟩ : syracuseStep 594611 = 891917) B891917
theorem B594641 : Blo 393766 594641 := bstep (se 2 (by rfl) ⟨222990, by rfl⟩ : syracuseStep 594641 = 445981) B445981
theorem B594659 : Blo 393766 594659 := bstep (se 1 (by rfl) ⟨445994, by rfl⟩ : syracuseStep 594659 = 891989) B891989
theorem B594689 : Blo 393766 594689 := bstep (se 2 (by rfl) ⟨223008, by rfl⟩ : syracuseStep 594689 = 446017) B446017
theorem B594707 : Blo 393766 594707 := bstep (se 1 (by rfl) ⟨446030, by rfl⟩ : syracuseStep 594707 = 892061) B892061
theorem B889649 : Blo 393766 889649 := bstep (se 2 (by rfl) ⟨333618, by rfl⟩ : syracuseStep 889649 = 667237) B667237
theorem B594737 : Blo 393766 594737 := bstep (se 2 (by rfl) ⟨223026, by rfl⟩ : syracuseStep 594737 = 446053) B446053
theorem B627521 : Blo 393766 627521 := bstep (se 2 (by rfl) ⟨235320, by rfl⟩ : syracuseStep 627521 = 470641) B470641
theorem B889667 : Blo 393766 889667 := bstep (se 1 (by rfl) ⟨667250, by rfl⟩ : syracuseStep 889667 = 1334501) B1334501
theorem B594755 : Blo 393766 594755 := bstep (se 1 (by rfl) ⟨446066, by rfl⟩ : syracuseStep 594755 = 892133) B892133
theorem B594785 : Blo 393766 594785 := bstep (se 2 (by rfl) ⟨223044, by rfl⟩ : syracuseStep 594785 = 446089) B446089
theorem B594803 : Blo 393766 594803 := bstep (se 1 (by rfl) ⟨446102, by rfl⟩ : syracuseStep 594803 = 892205) B892205
theorem B594833 : Blo 393766 594833 := bstep (se 2 (by rfl) ⟨223062, by rfl⟩ : syracuseStep 594833 = 446125) B446125
theorem B594851 : Blo 393766 594851 := bstep (se 1 (by rfl) ⟨446138, by rfl⟩ : syracuseStep 594851 = 892277) B892277
theorem B594881 : Blo 393766 594881 := bstep (se 2 (by rfl) ⟨223080, by rfl⟩ : syracuseStep 594881 = 446161) B446161
theorem B594899 : Blo 393766 594899 := bstep (se 1 (by rfl) ⟨446174, by rfl⟩ : syracuseStep 594899 = 892349) B892349
theorem B2003939 : Blo 393766 2003939 := bstep (se 1 (by rfl) ⟨1502954, by rfl⟩ : syracuseStep 2003939 = 3005909) B3005909
theorem B594929 : Blo 393766 594929 := bstep (se 2 (by rfl) ⟨223098, by rfl⟩ : syracuseStep 594929 = 446197) B446197
theorem B4527089 : Blo 393766 4527089 := bstep (se 2 (by rfl) ⟨1697658, by rfl⟩ : syracuseStep 4527089 = 3395317) B3395317
theorem B594947 : Blo 393766 594947 := bstep (se 1 (by rfl) ⟨446210, by rfl⟩ : syracuseStep 594947 = 892421) B892421
theorem B594977 : Blo 393766 594977 := bstep (se 2 (by rfl) ⟨223116, by rfl⟩ : syracuseStep 594977 = 446233) B446233
theorem B1217585 : Blo 393766 1217585 := bstep (se 2 (by rfl) ⟨456594, by rfl⟩ : syracuseStep 1217585 = 913189) B913189
theorem B594995 : Blo 393766 594995 := bstep (se 1 (by rfl) ⟨446246, by rfl⟩ : syracuseStep 594995 = 892493) B892493
theorem B889937 : Blo 393766 889937 := bstep (se 2 (by rfl) ⟨333726, by rfl⟩ : syracuseStep 889937 = 667453) B667453
theorem B595025 : Blo 393766 595025 := bstep (se 2 (by rfl) ⟨223134, by rfl⟩ : syracuseStep 595025 = 446269) B446269
theorem B889955 : Blo 393766 889955 := bstep (se 1 (by rfl) ⟨667466, by rfl⟩ : syracuseStep 889955 = 1334933) B1334933
theorem B2856035 : Blo 393766 2856035 := bstep (se 1 (by rfl) ⟨2142026, by rfl⟩ : syracuseStep 2856035 = 4284053) B4284053
theorem B595043 : Blo 393766 595043 := bstep (se 1 (by rfl) ⟨446282, by rfl⟩ : syracuseStep 595043 = 892565) B892565
theorem B595073 : Blo 393766 595073 := bstep (se 2 (by rfl) ⟨223152, by rfl⟩ : syracuseStep 595073 = 446305) B446305
theorem B595091 : Blo 393766 595091 := bstep (se 1 (by rfl) ⟨446318, by rfl⟩ : syracuseStep 595091 = 892637) B892637
theorem B595121 : Blo 393766 595121 := bstep (se 2 (by rfl) ⟨223170, by rfl⟩ : syracuseStep 595121 = 446341) B446341
theorem B2266289 : Blo 393766 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B595139 : Blo 393766 595139 := bstep (se 1 (by rfl) ⟨446354, by rfl⟩ : syracuseStep 595139 = 892709) B892709
theorem B1905869 : Blo 393766 1905869 := bstep (se 3 (by rfl) ⟨357350, by rfl⟩ : syracuseStep 1905869 = 714701) B714701
theorem B595169 : Blo 393766 595169 := bstep (se 2 (by rfl) ⟨223188, by rfl⟩ : syracuseStep 595169 = 446377) B446377
theorem B3020003 : Blo 393766 3020003 := bstep (se 1 (by rfl) ⟨2265002, by rfl⟩ : syracuseStep 3020003 = 4530005) B4530005
theorem B595187 : Blo 393766 595187 := bstep (se 1 (by rfl) ⟨446390, by rfl⟩ : syracuseStep 595187 = 892781) B892781
theorem B595217 : Blo 393766 595217 := bstep (se 2 (by rfl) ⟨223206, by rfl⟩ : syracuseStep 595217 = 446413) B446413
theorem B595235 : Blo 393766 595235 := bstep (se 1 (by rfl) ⟨446426, by rfl⟩ : syracuseStep 595235 = 892853) B892853
theorem B595265 : Blo 393766 595265 := bstep (se 2 (by rfl) ⟨223224, by rfl⟩ : syracuseStep 595265 = 446449) B446449
theorem B595283 : Blo 393766 595283 := bstep (se 1 (by rfl) ⟨446462, by rfl⟩ : syracuseStep 595283 = 892925) B892925
theorem B890225 : Blo 393766 890225 := bstep (se 2 (by rfl) ⟨333834, by rfl⟩ : syracuseStep 890225 = 667669) B667669
theorem B595313 : Blo 393766 595313 := bstep (se 2 (by rfl) ⟨223242, by rfl⟩ : syracuseStep 595313 = 446485) B446485
theorem B890243 : Blo 393766 890243 := bstep (se 1 (by rfl) ⟨667682, by rfl⟩ : syracuseStep 890243 = 1335365) B1335365
theorem B595331 : Blo 393766 595331 := bstep (se 1 (by rfl) ⟨446498, by rfl⟩ : syracuseStep 595331 = 892997) B892997
theorem B595361 : Blo 393766 595361 := bstep (se 2 (by rfl) ⟨223260, by rfl⟩ : syracuseStep 595361 = 446521) B446521
theorem B595379 : Blo 393766 595379 := bstep (se 1 (by rfl) ⟨446534, by rfl⟩ : syracuseStep 595379 = 893069) B893069
theorem B595409 : Blo 393766 595409 := bstep (se 2 (by rfl) ⟨223278, by rfl⟩ : syracuseStep 595409 = 446557) B446557
theorem B595427 : Blo 393766 595427 := bstep (se 1 (by rfl) ⟨446570, by rfl⟩ : syracuseStep 595427 = 893141) B893141
theorem B595457 : Blo 393766 595457 := bstep (se 2 (by rfl) ⟨223296, by rfl⟩ : syracuseStep 595457 = 446593) B446593
theorem B595475 : Blo 393766 595475 := bstep (se 1 (by rfl) ⟨446606, by rfl⟩ : syracuseStep 595475 = 893213) B893213
theorem B595505 : Blo 393766 595505 := bstep (se 2 (by rfl) ⟨223314, by rfl⟩ : syracuseStep 595505 = 446629) B446629
theorem B595523 : Blo 393766 595523 := bstep (se 1 (by rfl) ⟨446642, by rfl⟩ : syracuseStep 595523 = 893285) B893285
theorem B595553 : Blo 393766 595553 := bstep (se 2 (by rfl) ⟨223332, by rfl⟩ : syracuseStep 595553 = 446665) B446665
theorem B595571 : Blo 393766 595571 := bstep (se 1 (by rfl) ⟨446678, by rfl⟩ : syracuseStep 595571 = 893357) B893357
theorem B890513 : Blo 393766 890513 := bstep (se 2 (by rfl) ⟨333942, by rfl⟩ : syracuseStep 890513 = 667885) B667885
theorem B595601 : Blo 393766 595601 := bstep (se 2 (by rfl) ⟨223350, by rfl⟩ : syracuseStep 595601 = 446701) B446701
theorem B890531 : Blo 393766 890531 := bstep (se 1 (by rfl) ⟨667898, by rfl⟩ : syracuseStep 890531 = 1335797) B1335797
theorem B595619 : Blo 393766 595619 := bstep (se 1 (by rfl) ⟨446714, by rfl⟩ : syracuseStep 595619 = 893429) B893429
theorem B595649 : Blo 393766 595649 := bstep (se 2 (by rfl) ⟨223368, by rfl⟩ : syracuseStep 595649 = 446737) B446737
theorem B595667 : Blo 393766 595667 := bstep (se 1 (by rfl) ⟨446750, by rfl⟩ : syracuseStep 595667 = 893501) B893501
theorem B595697 : Blo 393766 595697 := bstep (se 2 (by rfl) ⟨223386, by rfl⟩ : syracuseStep 595697 = 446773) B446773
theorem B595715 : Blo 393766 595715 := bstep (se 1 (by rfl) ⟨446786, by rfl⟩ : syracuseStep 595715 = 893573) B893573
theorem B2004749 : Blo 393766 2004749 := bstep (se 3 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 2004749 = 751781) B751781
theorem B595745 : Blo 393766 595745 := bstep (se 2 (by rfl) ⟨223404, by rfl⟩ : syracuseStep 595745 = 446809) B446809
theorem B595763 : Blo 393766 595763 := bstep (se 1 (by rfl) ⟨446822, by rfl⟩ : syracuseStep 595763 = 893645) B893645
theorem B595793 : Blo 393766 595793 := bstep (se 2 (by rfl) ⟨223422, by rfl⟩ : syracuseStep 595793 = 446845) B446845
theorem B595811 : Blo 393766 595811 := bstep (se 1 (by rfl) ⟨446858, by rfl⟩ : syracuseStep 595811 = 893717) B893717
theorem B595841 : Blo 393766 595841 := bstep (se 2 (by rfl) ⟨223440, by rfl⟩ : syracuseStep 595841 = 446881) B446881
theorem B595859 : Blo 393766 595859 := bstep (se 1 (by rfl) ⟨446894, by rfl⟩ : syracuseStep 595859 = 893789) B893789
theorem B563107 : Blo 393766 563107 := bstep (se 1 (by rfl) ⟨422330, by rfl⟩ : syracuseStep 563107 = 844661) B844661
theorem B890801 : Blo 393766 890801 := bstep (se 2 (by rfl) ⟨334050, by rfl⟩ : syracuseStep 890801 = 668101) B668101
theorem B595889 : Blo 393766 595889 := bstep (se 2 (by rfl) ⟨223458, by rfl⟩ : syracuseStep 595889 = 446917) B446917
theorem B890819 : Blo 393766 890819 := bstep (se 1 (by rfl) ⟨668114, by rfl⟩ : syracuseStep 890819 = 1336229) B1336229
theorem B595907 : Blo 393766 595907 := bstep (se 1 (by rfl) ⟨446930, by rfl⟩ : syracuseStep 595907 = 893861) B893861
theorem B595937 : Blo 393766 595937 := bstep (se 2 (by rfl) ⟨223476, by rfl⟩ : syracuseStep 595937 = 446953) B446953
theorem B595955 : Blo 393766 595955 := bstep (se 1 (by rfl) ⟨446966, by rfl⟩ : syracuseStep 595955 = 893933) B893933
theorem B595985 : Blo 393766 595985 := bstep (se 2 (by rfl) ⟨223494, by rfl⟩ : syracuseStep 595985 = 446989) B446989
theorem B596003 : Blo 393766 596003 := bstep (se 1 (by rfl) ⟨447002, by rfl⟩ : syracuseStep 596003 = 894005) B894005
theorem B596033 : Blo 393766 596033 := bstep (se 2 (by rfl) ⟨223512, by rfl⟩ : syracuseStep 596033 = 447025) B447025
theorem B5150789 : Blo 393766 5150789 := bstep (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) B965773
theorem B596051 : Blo 393766 596051 := bstep (se 1 (by rfl) ⟨447038, by rfl⟩ : syracuseStep 596051 = 894077) B894077
theorem B1710193 : Blo 393766 1710193 := bstep (se 2 (by rfl) ⟨641322, by rfl⟩ : syracuseStep 1710193 = 1282645) B1282645
theorem B596081 : Blo 393766 596081 := bstep (se 2 (by rfl) ⟨223530, by rfl⟩ : syracuseStep 596081 = 447061) B447061
theorem B596099 : Blo 393766 596099 := bstep (se 1 (by rfl) ⟨447074, by rfl⟩ : syracuseStep 596099 = 894149) B894149
theorem B2398349 : Blo 393766 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B596129 : Blo 393766 596129 := bstep (se 2 (by rfl) ⟨223548, by rfl⟩ : syracuseStep 596129 = 447097) B447097
theorem B596147 : Blo 393766 596147 := bstep (se 1 (by rfl) ⟨447110, by rfl⟩ : syracuseStep 596147 = 894221) B894221
theorem B891089 : Blo 393766 891089 := bstep (se 2 (by rfl) ⟨334158, by rfl⟩ : syracuseStep 891089 = 668317) B668317
theorem B596177 : Blo 393766 596177 := bstep (se 2 (by rfl) ⟨223566, by rfl⟩ : syracuseStep 596177 = 447133) B447133
theorem B399587 : Blo 393766 399587 := bstep (se 1 (by rfl) ⟨299690, by rfl⟩ : syracuseStep 399587 = 599381) B599381
theorem B891107 : Blo 393766 891107 := bstep (se 1 (by rfl) ⟨668330, by rfl⟩ : syracuseStep 891107 = 1336661) B1336661
theorem B596195 : Blo 393766 596195 := bstep (se 1 (by rfl) ⟨447146, by rfl⟩ : syracuseStep 596195 = 894293) B894293
theorem B596225 : Blo 393766 596225 := bstep (se 2 (by rfl) ⟨223584, by rfl⟩ : syracuseStep 596225 = 447169) B447169
theorem B399619 : Blo 393766 399619 := bstep (se 1 (by rfl) ⟨299714, by rfl⟩ : syracuseStep 399619 = 599429) B599429
theorem B596243 : Blo 393766 596243 := bstep (se 1 (by rfl) ⟨447182, by rfl⟩ : syracuseStep 596243 = 894365) B894365
theorem B596273 : Blo 393766 596273 := bstep (se 2 (by rfl) ⟨223602, by rfl⟩ : syracuseStep 596273 = 447205) B447205
theorem B596291 : Blo 393766 596291 := bstep (se 1 (by rfl) ⟨447218, by rfl⟩ : syracuseStep 596291 = 894437) B894437
theorem B596321 : Blo 393766 596321 := bstep (se 2 (by rfl) ⟨223620, by rfl⟩ : syracuseStep 596321 = 447241) B447241
theorem B596339 : Blo 393766 596339 := bstep (se 1 (by rfl) ⟨447254, by rfl⟩ : syracuseStep 596339 = 894509) B894509
theorem B1350029 : Blo 393766 1350029 := bstep (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) B506261
theorem B596369 : Blo 393766 596369 := bstep (se 2 (by rfl) ⟨223638, by rfl⟩ : syracuseStep 596369 = 447277) B447277
theorem B596387 : Blo 393766 596387 := bstep (se 1 (by rfl) ⟨447290, by rfl⟩ : syracuseStep 596387 = 894581) B894581
theorem B596417 : Blo 393766 596417 := bstep (se 2 (by rfl) ⟨223656, by rfl⟩ : syracuseStep 596417 = 447313) B447313
theorem B596435 : Blo 393766 596435 := bstep (se 1 (by rfl) ⟨447326, by rfl⟩ : syracuseStep 596435 = 894653) B894653
theorem B4790755 : Blo 393766 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B891377 : Blo 393766 891377 := bstep (se 2 (by rfl) ⟨334266, by rfl⟩ : syracuseStep 891377 = 668533) B668533
theorem B596465 : Blo 393766 596465 := bstep (se 2 (by rfl) ⟨223674, by rfl⟩ : syracuseStep 596465 = 447349) B447349
theorem B891395 : Blo 393766 891395 := bstep (se 1 (by rfl) ⟨668546, by rfl⟩ : syracuseStep 891395 = 1337093) B1337093
theorem B596483 : Blo 393766 596483 := bstep (se 1 (by rfl) ⟨447362, by rfl⟩ : syracuseStep 596483 = 894725) B894725
theorem B4299277 : Blo 393766 4299277 := bstep (se 3 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 4299277 = 1612229) B1612229
theorem B596513 : Blo 393766 596513 := bstep (se 2 (by rfl) ⟨223692, by rfl⟩ : syracuseStep 596513 = 447385) B447385
theorem B596531 : Blo 393766 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B596561 : Blo 393766 596561 := bstep (se 2 (by rfl) ⟨223710, by rfl⟩ : syracuseStep 596561 = 447421) B447421
theorem B596579 : Blo 393766 596579 := bstep (se 1 (by rfl) ⟨447434, by rfl⟩ : syracuseStep 596579 = 894869) B894869
theorem B596609 : Blo 393766 596609 := bstep (se 2 (by rfl) ⟨223728, by rfl⟩ : syracuseStep 596609 = 447457) B447457
theorem B596627 : Blo 393766 596627 := bstep (se 1 (by rfl) ⟨447470, by rfl⟩ : syracuseStep 596627 = 894941) B894941
theorem B498403 : Blo 393766 498403 := bstep (se 1 (by rfl) ⟨373802, by rfl⟩ : syracuseStep 498403 = 747605) B747605
theorem B891665 : Blo 393766 891665 := bstep (se 2 (by rfl) ⟨334374, by rfl⟩ : syracuseStep 891665 = 668749) B668749
theorem B891683 : Blo 393766 891683 := bstep (se 1 (by rfl) ⟨668762, by rfl⟩ : syracuseStep 891683 = 1337525) B1337525
theorem B564241 : Blo 393766 564241 := bstep (se 2 (by rfl) ⟨211590, by rfl⟩ : syracuseStep 564241 = 423181) B423181
theorem B891953 : Blo 393766 891953 := bstep (se 2 (by rfl) ⟨334482, by rfl⟩ : syracuseStep 891953 = 668965) B668965
theorem B891971 : Blo 393766 891971 := bstep (se 1 (by rfl) ⟨668978, by rfl⟩ : syracuseStep 891971 = 1337957) B1337957
theorem B564337 : Blo 393766 564337 := bstep (se 2 (by rfl) ⟨211626, by rfl⟩ : syracuseStep 564337 = 423253) B423253
theorem B3382469 : Blo 393766 3382469 := bstep (se 4 (by rfl) ⟨317106, by rfl⟩ : syracuseStep 3382469 = 634213) B634213
theorem B498899 : Blo 393766 498899 := bstep (se 1 (by rfl) ⟨374174, by rfl⟩ : syracuseStep 498899 = 748349) B748349
theorem B1121521 : Blo 393766 1121521 := bstep (se 2 (by rfl) ⟨420570, by rfl⟩ : syracuseStep 1121521 = 841141) B841141
theorem B1219853 : Blo 393766 1219853 := bstep (se 3 (by rfl) ⟨228722, by rfl⟩ : syracuseStep 1219853 = 457445) B457445
theorem B892241 : Blo 393766 892241 := bstep (se 2 (by rfl) ⟨334590, by rfl⟩ : syracuseStep 892241 = 669181) B669181
theorem B892259 : Blo 393766 892259 := bstep (se 1 (by rfl) ⟨669194, by rfl⟩ : syracuseStep 892259 = 1338389) B1338389
theorem B400771 : Blo 393766 400771 := bstep (se 1 (by rfl) ⟨300578, by rfl⟩ : syracuseStep 400771 = 601157) B601157
theorem B1121681 : Blo 393766 1121681 := bstep (se 2 (by rfl) ⟨420630, by rfl⟩ : syracuseStep 1121681 = 841261) B841261
theorem B400819 : Blo 393766 400819 := bstep (se 1 (by rfl) ⟨300614, by rfl⟩ : syracuseStep 400819 = 601229) B601229
theorem B6757829 : Blo 393766 6757829 := bstep (se 4 (by rfl) ⟨633546, by rfl⟩ : syracuseStep 6757829 = 1267093) B1267093
theorem B1121795 : Blo 393766 1121795 := bstep (se 1 (by rfl) ⟨841346, by rfl⟩ : syracuseStep 1121795 = 1682693) B1682693
theorem B5054021 : Blo 393766 5054021 := bstep (se 4 (by rfl) ⟨473814, by rfl⟩ : syracuseStep 5054021 = 947629) B947629
theorem B564833 : Blo 393766 564833 := bstep (se 2 (by rfl) ⟨211812, by rfl⟩ : syracuseStep 564833 = 423625) B423625
theorem B892529 : Blo 393766 892529 := bstep (se 2 (by rfl) ⟨334698, by rfl⟩ : syracuseStep 892529 = 669397) B669397
theorem B892547 : Blo 393766 892547 := bstep (se 1 (by rfl) ⟨669410, by rfl⟩ : syracuseStep 892547 = 1338821) B1338821
theorem B3383153 : Blo 393766 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B892817 : Blo 393766 892817 := bstep (se 2 (by rfl) ⟨334806, by rfl⟩ : syracuseStep 892817 = 669613) B669613
theorem B499603 : Blo 393766 499603 := bstep (se 1 (by rfl) ⟨374702, by rfl⟩ : syracuseStep 499603 = 749405) B749405
theorem B892835 : Blo 393766 892835 := bstep (se 1 (by rfl) ⟨669626, by rfl⟩ : syracuseStep 892835 = 1339253) B1339253
theorem B499699 : Blo 393766 499699 := bstep (se 1 (by rfl) ⟨374774, by rfl⟩ : syracuseStep 499699 = 749549) B749549
theorem B5480561 : Blo 393766 5480561 := bstep (se 2 (by rfl) ⟨2055210, by rfl⟩ : syracuseStep 5480561 = 4110421) B4110421
theorem B893105 : Blo 393766 893105 := bstep (se 2 (by rfl) ⟨334914, by rfl⟩ : syracuseStep 893105 = 669829) B669829
theorem B893123 : Blo 393766 893123 := bstep (se 1 (by rfl) ⟨669842, by rfl⟩ : syracuseStep 893123 = 1339685) B1339685
theorem B860483 : Blo 393766 860483 := bstep (se 1 (by rfl) ⟨645362, by rfl⟩ : syracuseStep 860483 = 1290725) B1290725
theorem B631235 : Blo 393766 631235 := bstep (se 1 (by rfl) ⟨473426, by rfl⟩ : syracuseStep 631235 = 946853) B946853
theorem B565699 : Blo 393766 565699 := bstep (se 1 (by rfl) ⟨424274, by rfl⟩ : syracuseStep 565699 = 848549) B848549
theorem B893393 : Blo 393766 893393 := bstep (se 2 (by rfl) ⟨335022, by rfl⟩ : syracuseStep 893393 = 670045) B670045
theorem B500195 : Blo 393766 500195 := bstep (se 1 (by rfl) ⟨375146, by rfl⟩ : syracuseStep 500195 = 750293) B750293
theorem B893411 : Blo 393766 893411 := bstep (se 1 (by rfl) ⟨670058, by rfl⟩ : syracuseStep 893411 = 1340117) B1340117
theorem B1122797 : Blo 393766 1122797 := bstep (se 3 (by rfl) ⟨210524, by rfl⟩ : syracuseStep 1122797 = 421049) B421049
theorem B565795 : Blo 393766 565795 := bstep (se 1 (by rfl) ⟨424346, by rfl⟩ : syracuseStep 565795 = 848693) B848693
theorem B3809891 : Blo 393766 3809891 := bstep (se 1 (by rfl) ⟨2857418, by rfl⟩ : syracuseStep 3809891 = 5714837) B5714837
theorem B2007665 : Blo 393766 2007665 := bstep (se 2 (by rfl) ⟨752874, by rfl⟩ : syracuseStep 2007665 = 1505749) B1505749
theorem B1122979 : Blo 393766 1122979 := bstep (se 1 (by rfl) ⟨842234, by rfl⟩ : syracuseStep 1122979 = 1684469) B1684469
theorem B893681 : Blo 393766 893681 := bstep (se 2 (by rfl) ⟨335130, by rfl⟩ : syracuseStep 893681 = 670261) B670261
theorem B893699 : Blo 393766 893699 := bstep (se 1 (by rfl) ⟨670274, by rfl⟩ : syracuseStep 893699 = 1340549) B1340549
theorem B1123139 : Blo 393766 1123139 := bstep (se 1 (by rfl) ⟨842354, by rfl⟩ : syracuseStep 1123139 = 1684709) B1684709
theorem B664483 : Blo 393766 664483 := bstep (se 1 (by rfl) ⟨498362, by rfl⟩ : syracuseStep 664483 = 996725) B996725
theorem B631747 : Blo 393766 631747 := bstep (se 1 (by rfl) ⟨473810, by rfl⟩ : syracuseStep 631747 = 947621) B947621
theorem B893969 : Blo 393766 893969 := bstep (se 2 (by rfl) ⟨335238, by rfl⟩ : syracuseStep 893969 = 670477) B670477
theorem B566291 : Blo 393766 566291 := bstep (se 1 (by rfl) ⟨424718, by rfl⟩ : syracuseStep 566291 = 849437) B849437
theorem B893987 : Blo 393766 893987 := bstep (se 1 (by rfl) ⟨670490, by rfl⟩ : syracuseStep 893987 = 1340981) B1340981
theorem B664625 : Blo 393766 664625 := bstep (se 2 (by rfl) ⟨249234, by rfl⟩ : syracuseStep 664625 = 498469) B498469
theorem B1811555 : Blo 393766 1811555 := bstep (se 1 (by rfl) ⟨1358666, by rfl⟩ : syracuseStep 1811555 = 2717333) B2717333
theorem B500899 : Blo 393766 500899 := bstep (se 1 (by rfl) ⟨375674, by rfl⟩ : syracuseStep 500899 = 751349) B751349
theorem B664753 : Blo 393766 664753 := bstep (se 2 (by rfl) ⟨249282, by rfl⟩ : syracuseStep 664753 = 498565) B498565
theorem B664787 : Blo 393766 664787 := bstep (se 1 (by rfl) ⟨498590, by rfl⟩ : syracuseStep 664787 = 997181) B997181
theorem B533729 : Blo 393766 533729 := bstep (se 2 (by rfl) ⟨200148, by rfl⟩ : syracuseStep 533729 = 400297) B400297
theorem B500995 : Blo 393766 500995 := bstep (se 1 (by rfl) ⟨375746, by rfl⟩ : syracuseStep 500995 = 751493) B751493
theorem B894257 : Blo 393766 894257 := bstep (se 2 (by rfl) ⟨335346, by rfl⟩ : syracuseStep 894257 = 670693) B670693
theorem B894275 : Blo 393766 894275 := bstep (se 1 (by rfl) ⟨670706, by rfl⟩ : syracuseStep 894275 = 1341413) B1341413
theorem B664915 : Blo 393766 664915 := bstep (se 1 (by rfl) ⟨498686, by rfl⟩ : syracuseStep 664915 = 997373) B997373
theorem B665057 : Blo 393766 665057 := bstep (se 2 (by rfl) ⟨249396, by rfl⟩ : syracuseStep 665057 = 498793) B498793
theorem B632291 : Blo 393766 632291 := bstep (se 1 (by rfl) ⟨474218, by rfl⟩ : syracuseStep 632291 = 948437) B948437
theorem B894545 : Blo 393766 894545 := bstep (se 2 (by rfl) ⟨335454, by rfl⟩ : syracuseStep 894545 = 670909) B670909
theorem B665185 : Blo 393766 665185 := bstep (se 2 (by rfl) ⟨249444, by rfl⟩ : syracuseStep 665185 = 498889) B498889
theorem B894563 : Blo 393766 894563 := bstep (se 1 (by rfl) ⟨670922, by rfl⟩ : syracuseStep 894563 = 1341845) B1341845
theorem B665219 : Blo 393766 665219 := bstep (se 1 (by rfl) ⟨498914, by rfl⟩ : syracuseStep 665219 = 997829) B997829
theorem B632465 : Blo 393766 632465 := bstep (se 2 (by rfl) ⟨237174, by rfl⟩ : syracuseStep 632465 = 474349) B474349
theorem B501491 : Blo 393766 501491 := bstep (se 1 (by rfl) ⟨376118, by rfl⟩ : syracuseStep 501491 = 752237) B752237
theorem B665347 : Blo 393766 665347 := bstep (se 1 (by rfl) ⟨499010, by rfl⟩ : syracuseStep 665347 = 998021) B998021
theorem B1288045 : Blo 393766 1288045 := bstep (se 3 (by rfl) ⟨241508, by rfl⟩ : syracuseStep 1288045 = 483017) B483017
theorem B1124209 : Blo 393766 1124209 := bstep (se 2 (by rfl) ⟨421578, by rfl⟩ : syracuseStep 1124209 = 843157) B843157
theorem B894833 : Blo 393766 894833 := bstep (se 2 (by rfl) ⟨335562, by rfl⟩ : syracuseStep 894833 = 671125) B671125
theorem B894851 : Blo 393766 894851 := bstep (se 1 (by rfl) ⟨671138, by rfl⟩ : syracuseStep 894851 = 1342277) B1342277
theorem B665489 : Blo 393766 665489 := bstep (se 2 (by rfl) ⟨249558, by rfl⟩ : syracuseStep 665489 = 499117) B499117
theorem B665617 : Blo 393766 665617 := bstep (se 2 (by rfl) ⟨249606, by rfl⟩ : syracuseStep 665617 = 499213) B499213
theorem B2009123 : Blo 393766 2009123 := bstep (se 1 (by rfl) ⟨1506842, by rfl⟩ : syracuseStep 2009123 = 3013685) B3013685
theorem B665651 : Blo 393766 665651 := bstep (se 1 (by rfl) ⟨499238, by rfl⟩ : syracuseStep 665651 = 998477) B998477
theorem B665779 : Blo 393766 665779 := bstep (se 1 (by rfl) ⟨499334, by rfl⟩ : syracuseStep 665779 = 998669) B998669
theorem B2140451 : Blo 393766 2140451 := bstep (se 1 (by rfl) ⟨1605338, by rfl⟩ : syracuseStep 2140451 = 3210677) B3210677
theorem B665921 : Blo 393766 665921 := bstep (se 2 (by rfl) ⟨249720, by rfl⟩ : syracuseStep 665921 = 499441) B499441
theorem B502195 : Blo 393766 502195 := bstep (se 1 (by rfl) ⟨376646, by rfl⟩ : syracuseStep 502195 = 753293) B753293
theorem B666049 : Blo 393766 666049 := bstep (se 2 (by rfl) ⟨249768, by rfl⟩ : syracuseStep 666049 = 499537) B499537
theorem B666083 : Blo 393766 666083 := bstep (se 1 (by rfl) ⟨499562, by rfl⟩ : syracuseStep 666083 = 999125) B999125
theorem B2140643 : Blo 393766 2140643 := bstep (se 1 (by rfl) ⟨1605482, by rfl⟩ : syracuseStep 2140643 = 3210965) B3210965
theorem B535027 : Blo 393766 535027 := bstep (se 1 (by rfl) ⟨401270, by rfl⟩ : syracuseStep 535027 = 802541) B802541
theorem B502291 : Blo 393766 502291 := bstep (se 1 (by rfl) ⟨376718, by rfl⟩ : syracuseStep 502291 = 753437) B753437
theorem B1452593 : Blo 393766 1452593 := bstep (se 2 (by rfl) ⟨544722, by rfl⟩ : syracuseStep 1452593 = 1089445) B1089445
theorem B666211 : Blo 393766 666211 := bstep (se 1 (by rfl) ⟨499658, by rfl⟩ : syracuseStep 666211 = 999317) B999317
theorem B666353 : Blo 393766 666353 := bstep (se 2 (by rfl) ⟨249882, by rfl⟩ : syracuseStep 666353 = 499765) B499765
theorem B2009933 : Blo 393766 2009933 := bstep (se 3 (by rfl) ⟨376862, by rfl⟩ : syracuseStep 2009933 = 753725) B753725
theorem B666481 : Blo 393766 666481 := bstep (se 2 (by rfl) ⟨249930, by rfl⟩ : syracuseStep 666481 = 499861) B499861
theorem B666515 : Blo 393766 666515 := bstep (se 1 (by rfl) ⟨499886, by rfl⟩ : syracuseStep 666515 = 999773) B999773
theorem B502787 : Blo 393766 502787 := bstep (se 1 (by rfl) ⟨377090, by rfl⟩ : syracuseStep 502787 = 754181) B754181
theorem B666643 : Blo 393766 666643 := bstep (se 1 (by rfl) ⟨499982, by rfl⟩ : syracuseStep 666643 = 999965) B999965
theorem B1125485 : Blo 393766 1125485 := bstep (se 3 (by rfl) ⟨211028, by rfl⟩ : syracuseStep 1125485 = 422057) B422057
theorem B666785 : Blo 393766 666785 := bstep (se 2 (by rfl) ⟨250044, by rfl⟩ : syracuseStep 666785 = 500089) B500089
theorem B535745 : Blo 393766 535745 := bstep (se 2 (by rfl) ⟨200904, by rfl⟩ : syracuseStep 535745 = 401809) B401809
theorem B2534597 : Blo 393766 2534597 := bstep (se 4 (by rfl) ⟨237618, by rfl⟩ : syracuseStep 2534597 = 475237) B475237
theorem B666913 : Blo 393766 666913 := bstep (se 2 (by rfl) ⟨250092, by rfl⟩ : syracuseStep 666913 = 500185) B500185
theorem B1125667 : Blo 393766 1125667 := bstep (se 1 (by rfl) ⟨844250, by rfl⟩ : syracuseStep 1125667 = 1688501) B1688501
theorem B666947 : Blo 393766 666947 := bstep (se 1 (by rfl) ⟨500210, by rfl⟩ : syracuseStep 666947 = 1000421) B1000421
theorem B1125713 : Blo 393766 1125713 := bstep (se 2 (by rfl) ⟨422142, by rfl⟩ : syracuseStep 1125713 = 844285) B844285
theorem B535939 : Blo 393766 535939 := bstep (se 1 (by rfl) ⟨401954, by rfl⟩ : syracuseStep 535939 = 803909) B803909
theorem B667075 : Blo 393766 667075 := bstep (se 1 (by rfl) ⟨500306, by rfl⟩ : syracuseStep 667075 = 1000613) B1000613
theorem B667217 : Blo 393766 667217 := bstep (se 2 (by rfl) ⟨250206, by rfl⟩ : syracuseStep 667217 = 500413) B500413
theorem B634483 : Blo 393766 634483 := bstep (se 1 (by rfl) ⟨475862, by rfl⟩ : syracuseStep 634483 = 951725) B951725
theorem B2174597 : Blo 393766 2174597 := bstep (se 4 (by rfl) ⟨203868, by rfl⟩ : syracuseStep 2174597 = 407737) B407737
theorem B1289891 : Blo 393766 1289891 := bstep (se 1 (by rfl) ⟨967418, by rfl⟩ : syracuseStep 1289891 = 1934837) B1934837
theorem B634547 : Blo 393766 634547 := bstep (se 1 (by rfl) ⟨475910, by rfl⟩ : syracuseStep 634547 = 951821) B951821
theorem B667345 : Blo 393766 667345 := bstep (se 2 (by rfl) ⟨250254, by rfl⟩ : syracuseStep 667345 = 500509) B500509
theorem B667379 : Blo 393766 667379 := bstep (se 1 (by rfl) ⟨500534, by rfl⟩ : syracuseStep 667379 = 1001069) B1001069
theorem B2699021 : Blo 393766 2699021 := bstep (se 3 (by rfl) ⟨506066, by rfl⟩ : syracuseStep 2699021 = 1012133) B1012133
theorem B667507 : Blo 393766 667507 := bstep (se 1 (by rfl) ⟨500630, by rfl⟩ : syracuseStep 667507 = 1001261) B1001261
theorem B536545 : Blo 393766 536545 := bstep (se 2 (by rfl) ⟨201204, by rfl⟩ : syracuseStep 536545 = 402409) B402409
theorem B667649 : Blo 393766 667649 := bstep (se 2 (by rfl) ⟨250368, by rfl⟩ : syracuseStep 667649 = 500737) B500737
theorem B2994245 : Blo 393766 2994245 := bstep (se 4 (by rfl) ⟨280710, by rfl⟩ : syracuseStep 2994245 = 561421) B561421
theorem B667777 : Blo 393766 667777 := bstep (se 2 (by rfl) ⟨250416, by rfl⟩ : syracuseStep 667777 = 500833) B500833
theorem B667811 : Blo 393766 667811 := bstep (se 1 (by rfl) ⟨500858, by rfl⟩ : syracuseStep 667811 = 1001717) B1001717
theorem B798979 : Blo 393766 798979 := bstep (se 1 (by rfl) ⟨599234, by rfl⟩ : syracuseStep 798979 = 1198469) B1198469
theorem B667939 : Blo 393766 667939 := bstep (se 1 (by rfl) ⟨500954, by rfl⟩ : syracuseStep 667939 = 1001909) B1001909
theorem B1716515 : Blo 393766 1716515 := bstep (se 1 (by rfl) ⟨1287386, by rfl⟩ : syracuseStep 1716515 = 2574773) B2574773
theorem B2404721 : Blo 393766 2404721 := bstep (se 2 (by rfl) ⟨901770, by rfl⟩ : syracuseStep 2404721 = 1803541) B1803541
theorem B668081 : Blo 393766 668081 := bstep (se 2 (by rfl) ⟨250530, by rfl⟩ : syracuseStep 668081 = 501061) B501061
theorem B537043 : Blo 393766 537043 := bstep (se 1 (by rfl) ⟨402782, by rfl⟩ : syracuseStep 537043 = 805565) B805565
theorem B668209 : Blo 393766 668209 := bstep (se 2 (by rfl) ⟨250578, by rfl⟩ : syracuseStep 668209 = 501157) B501157
theorem B668243 : Blo 393766 668243 := bstep (se 1 (by rfl) ⟨501182, by rfl⟩ : syracuseStep 668243 = 1002365) B1002365
theorem B635521 : Blo 393766 635521 := bstep (se 2 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 635521 = 476641) B476641
theorem B668371 : Blo 393766 668371 := bstep (se 1 (by rfl) ⟨501278, by rfl⟩ : syracuseStep 668371 = 1002557) B1002557
theorem B1127171 : Blo 393766 1127171 := bstep (se 1 (by rfl) ⟨845378, by rfl⟩ : syracuseStep 1127171 = 1690757) B1690757
theorem B668513 : Blo 393766 668513 := bstep (se 2 (by rfl) ⟨250692, by rfl⟩ : syracuseStep 668513 = 501385) B501385
theorem B635777 : Blo 393766 635777 := bstep (se 2 (by rfl) ⟨238416, by rfl⟩ : syracuseStep 635777 = 476833) B476833
theorem B668641 : Blo 393766 668641 := bstep (se 2 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 668641 = 501481) B501481
theorem B668675 : Blo 393766 668675 := bstep (se 1 (by rfl) ⟨501506, by rfl⟩ : syracuseStep 668675 = 1003013) B1003013
theorem B635969 : Blo 393766 635969 := bstep (se 2 (by rfl) ⟨238488, by rfl⟩ : syracuseStep 635969 = 476977) B476977
theorem B668803 : Blo 393766 668803 := bstep (se 1 (by rfl) ⟨501602, by rfl⟩ : syracuseStep 668803 = 1003205) B1003205
theorem B668945 : Blo 393766 668945 := bstep (se 2 (by rfl) ⟨250854, by rfl⟩ : syracuseStep 668945 = 501709) B501709
theorem B5682545 : Blo 393766 5682545 := bstep (se 2 (by rfl) ⟨2130954, by rfl⟩ : syracuseStep 5682545 = 4261909) B4261909
theorem B669073 : Blo 393766 669073 := bstep (se 2 (by rfl) ⟨250902, by rfl⟩ : syracuseStep 669073 = 501805) B501805
theorem B669107 : Blo 393766 669107 := bstep (se 1 (by rfl) ⟨501830, by rfl⟩ : syracuseStep 669107 = 1003661) B1003661
theorem B669235 : Blo 393766 669235 := bstep (se 1 (by rfl) ⟨501926, by rfl⟩ : syracuseStep 669235 = 1003853) B1003853
theorem B1685069 : Blo 393766 1685069 := bstep (se 3 (by rfl) ⟨315950, by rfl⟩ : syracuseStep 1685069 = 631901) B631901
theorem B2012849 : Blo 393766 2012849 := bstep (se 2 (by rfl) ⟨754818, by rfl⟩ : syracuseStep 2012849 = 1509637) B1509637
theorem B669377 : Blo 393766 669377 := bstep (se 2 (by rfl) ⟨251016, by rfl⟩ : syracuseStep 669377 = 502033) B502033
theorem B669505 : Blo 393766 669505 := bstep (se 2 (by rfl) ⟨251064, by rfl⟩ : syracuseStep 669505 = 502129) B502129
theorem B2537315 : Blo 393766 2537315 := bstep (se 1 (by rfl) ⟨1902986, by rfl⟩ : syracuseStep 2537315 = 3805973) B3805973
theorem B669539 : Blo 393766 669539 := bstep (se 1 (by rfl) ⟨502154, by rfl⟩ : syracuseStep 669539 = 1004309) B1004309
theorem B604099 : Blo 393766 604099 := bstep (se 1 (by rfl) ⟨453074, by rfl⟩ : syracuseStep 604099 = 906149) B906149
theorem B1128401 : Blo 393766 1128401 := bstep (se 2 (by rfl) ⟨423150, by rfl⟩ : syracuseStep 1128401 = 846301) B846301
theorem B669667 : Blo 393766 669667 := bstep (se 1 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 669667 = 1004501) B1004501
theorem B997393 : Blo 393766 997393 := bstep (se 2 (by rfl) ⟨374022, by rfl⟩ : syracuseStep 997393 = 748045) B748045
theorem B669809 : Blo 393766 669809 := bstep (se 2 (by rfl) ⟨251178, by rfl⟩ : syracuseStep 669809 = 502357) B502357
theorem B669937 : Blo 393766 669937 := bstep (se 2 (by rfl) ⟨251226, by rfl⟩ : syracuseStep 669937 = 502453) B502453
theorem B604417 : Blo 393766 604417 := bstep (se 2 (by rfl) ⟨226656, by rfl⟩ : syracuseStep 604417 = 453313) B453313
theorem B669971 : Blo 393766 669971 := bstep (se 1 (by rfl) ⟨502478, by rfl⟩ : syracuseStep 669971 = 1004957) B1004957
theorem B997667 : Blo 393766 997667 := bstep (se 1 (by rfl) ⟨748250, by rfl⟩ : syracuseStep 997667 = 1496501) B1496501
theorem B801137 : Blo 393766 801137 := bstep (se 2 (by rfl) ⟨300426, by rfl⟩ : syracuseStep 801137 = 600853) B600853
theorem B670099 : Blo 393766 670099 := bstep (se 1 (by rfl) ⟨502574, by rfl⟩ : syracuseStep 670099 = 1005149) B1005149
theorem B997859 : Blo 393766 997859 := bstep (se 1 (by rfl) ⟨748394, by rfl⟩ : syracuseStep 997859 = 1496789) B1496789
theorem B670241 : Blo 393766 670241 := bstep (se 2 (by rfl) ⟨251340, by rfl⟩ : syracuseStep 670241 = 502681) B502681
theorem B4274801 : Blo 393766 4274801 := bstep (se 2 (by rfl) ⟨1603050, by rfl⟩ : syracuseStep 4274801 = 3206101) B3206101
theorem B670369 : Blo 393766 670369 := bstep (se 2 (by rfl) ⟨251388, by rfl⟩ : syracuseStep 670369 = 502777) B502777
theorem B670403 : Blo 393766 670403 := bstep (se 1 (by rfl) ⟨502802, by rfl⟩ : syracuseStep 670403 = 1005605) B1005605
theorem B670531 : Blo 393766 670531 := bstep (se 1 (by rfl) ⟨502898, by rfl⟩ : syracuseStep 670531 = 1005797) B1005797
theorem B670673 : Blo 393766 670673 := bstep (se 2 (by rfl) ⟨251502, by rfl⟩ : syracuseStep 670673 = 503005) B503005
theorem B5094413 : Blo 393766 5094413 := bstep (se 3 (by rfl) ⟨955202, by rfl⟩ : syracuseStep 5094413 = 1910405) B1910405
theorem B670801 : Blo 393766 670801 := bstep (se 2 (by rfl) ⟨251550, by rfl⟩ : syracuseStep 670801 = 503101) B503101
theorem B670835 : Blo 393766 670835 := bstep (se 1 (by rfl) ⟨503126, by rfl⟩ : syracuseStep 670835 = 1006253) B1006253
theorem B670963 : Blo 393766 670963 := bstep (se 1 (by rfl) ⟨503222, by rfl⟩ : syracuseStep 670963 = 1006445) B1006445
theorem B671105 : Blo 393766 671105 := bstep (se 2 (by rfl) ⟨251664, by rfl⟩ : syracuseStep 671105 = 503329) B503329
theorem B1129859 : Blo 393766 1129859 := bstep (se 1 (by rfl) ⟨847394, by rfl⟩ : syracuseStep 1129859 = 1694789) B1694789
theorem B998801 : Blo 393766 998801 := bstep (se 2 (by rfl) ⟨374550, by rfl⟩ : syracuseStep 998801 = 749101) B749101
theorem B998851 : Blo 393766 998851 := bstep (se 1 (by rfl) ⟨749138, by rfl⟩ : syracuseStep 998851 = 1498277) B1498277
theorem B998993 : Blo 393766 998993 := bstep (se 2 (by rfl) ⟨374622, by rfl⟩ : syracuseStep 998993 = 749245) B749245
theorem B3391217 : Blo 393766 3391217 := bstep (se 2 (by rfl) ⟨1271706, by rfl⟩ : syracuseStep 3391217 = 2543413) B2543413
theorem B2080561 : Blo 393766 2080561 := bstep (se 2 (by rfl) ⟨780210, by rfl⟩ : syracuseStep 2080561 = 1560421) B1560421
theorem B2539313 : Blo 393766 2539313 := bstep (se 2 (by rfl) ⟨952242, by rfl⟩ : syracuseStep 2539313 = 1904485) B1904485
theorem B1261507 : Blo 393766 1261507 := bstep (se 1 (by rfl) ⟨946130, by rfl⟩ : syracuseStep 1261507 = 1892261) B1892261
theorem B2572273 : Blo 393766 2572273 := bstep (se 2 (by rfl) ⟨964602, by rfl⟩ : syracuseStep 2572273 = 1929205) B1929205
theorem B802865 : Blo 393766 802865 := bstep (se 2 (by rfl) ⟨301074, by rfl⟩ : syracuseStep 802865 = 602149) B602149
theorem B901187 : Blo 393766 901187 := bstep (se 1 (by rfl) ⟨675890, by rfl⟩ : syracuseStep 901187 = 1351781) B1351781
theorem B1261649 : Blo 393766 1261649 := bstep (se 2 (by rfl) ⟨473118, by rfl⟩ : syracuseStep 1261649 = 946237) B946237
theorem B5390477 : Blo 393766 5390477 := bstep (se 3 (by rfl) ⟨1010714, by rfl⟩ : syracuseStep 5390477 = 2021429) B2021429
theorem B1130669 : Blo 393766 1130669 := bstep (se 3 (by rfl) ⟨212000, by rfl⟩ : syracuseStep 1130669 = 424001) B424001
theorem B5161229 : Blo 393766 5161229 := bstep (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) B1935461
theorem B475411 : Blo 393766 475411 := bstep (se 1 (by rfl) ⟨356558, by rfl⟩ : syracuseStep 475411 = 713117) B713117
theorem B1130861 : Blo 393766 1130861 := bstep (se 3 (by rfl) ⟨212036, by rfl⟩ : syracuseStep 1130861 = 424073) B424073
theorem B999985 : Blo 393766 999985 := bstep (se 2 (by rfl) ⟨374994, by rfl⟩ : syracuseStep 999985 = 749989) B749989
theorem B443011 : Blo 393766 443011 := bstep (se 1 (by rfl) ⟨332258, by rfl⟩ : syracuseStep 443011 = 664517) B664517
theorem B443155 : Blo 393766 443155 := bstep (se 1 (by rfl) ⟨332366, by rfl⟩ : syracuseStep 443155 = 664733) B664733
theorem B1000259 : Blo 393766 1000259 := bstep (se 1 (by rfl) ⟨750194, by rfl⟩ : syracuseStep 1000259 = 1500389) B1500389
theorem B901955 : Blo 393766 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B443299 : Blo 393766 443299 := bstep (se 1 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 443299 = 664949) B664949
theorem B1065901 : Blo 393766 1065901 := bstep (se 3 (by rfl) ⟨199856, by rfl⟩ : syracuseStep 1065901 = 399713) B399713
theorem B1000451 : Blo 393766 1000451 := bstep (se 1 (by rfl) ⟨750338, by rfl⟩ : syracuseStep 1000451 = 1500677) B1500677
theorem B2704433 : Blo 393766 2704433 := bstep (se 2 (by rfl) ⟨1014162, by rfl⟩ : syracuseStep 2704433 = 2028325) B2028325
theorem B443443 : Blo 393766 443443 := bstep (se 1 (by rfl) ⟨332582, by rfl⟩ : syracuseStep 443443 = 665165) B665165
theorem B4506677 : Blo 393766 4506677 := bstep (se 5 (by rfl) ⟨211250, by rfl⟩ : syracuseStep 4506677 = 422501) B422501
theorem B2278541 : Blo 393766 2278541 := bstep (se 3 (by rfl) ⟨427226, by rfl⟩ : syracuseStep 2278541 = 854453) B854453
theorem B443587 : Blo 393766 443587 := bstep (se 1 (by rfl) ⟨332690, by rfl⟩ : syracuseStep 443587 = 665381) B665381
theorem B1131853 : Blo 393766 1131853 := bstep (se 3 (by rfl) ⟨212222, by rfl⟩ : syracuseStep 1131853 = 424445) B424445
theorem B443731 : Blo 393766 443731 := bstep (se 1 (by rfl) ⟨332798, by rfl⟩ : syracuseStep 443731 = 665597) B665597
theorem B607651 : Blo 393766 607651 := bstep (se 1 (by rfl) ⟨455738, by rfl⟩ : syracuseStep 607651 = 911477) B911477
theorem B443875 : Blo 393766 443875 := bstep (se 1 (by rfl) ⟨332906, by rfl⟩ : syracuseStep 443875 = 665813) B665813
theorem B444019 : Blo 393766 444019 := bstep (se 1 (by rfl) ⟨333014, by rfl⟩ : syracuseStep 444019 = 666029) B666029
theorem B444163 : Blo 393766 444163 := bstep (se 1 (by rfl) ⟨333122, by rfl⟩ : syracuseStep 444163 = 666245) B666245
theorem B2246413 : Blo 393766 2246413 := bstep (se 3 (by rfl) ⟨421202, by rfl⟩ : syracuseStep 2246413 = 842405) B842405
theorem B3000077 : Blo 393766 3000077 := bstep (se 3 (by rfl) ⟨562514, by rfl⟩ : syracuseStep 3000077 = 1125029) B1125029
theorem B1689443 : Blo 393766 1689443 := bstep (se 1 (by rfl) ⟨1267082, by rfl⟩ : syracuseStep 1689443 = 2534165) B2534165
theorem B444307 : Blo 393766 444307 := bstep (se 1 (by rfl) ⟨333230, by rfl⟩ : syracuseStep 444307 = 666461) B666461
theorem B2738083 : Blo 393766 2738083 := bstep (se 1 (by rfl) ⟨2053562, by rfl⟩ : syracuseStep 2738083 = 4107125) B4107125
theorem B1001393 : Blo 393766 1001393 := bstep (se 2 (by rfl) ⟨375522, by rfl⟩ : syracuseStep 1001393 = 751045) B751045
theorem B1329101 : Blo 393766 1329101 := bstep (se 3 (by rfl) ⟨249206, by rfl⟩ : syracuseStep 1329101 = 498413) B498413
theorem B1001443 : Blo 393766 1001443 := bstep (se 1 (by rfl) ⟨751082, by rfl⟩ : syracuseStep 1001443 = 1502165) B1502165
theorem B1329155 : Blo 393766 1329155 := bstep (se 1 (by rfl) ⟨996866, by rfl⟩ : syracuseStep 1329155 = 1993733) B1993733
theorem B444451 : Blo 393766 444451 := bstep (se 1 (by rfl) ⟨333338, by rfl⟩ : syracuseStep 444451 = 666677) B666677
theorem B1001585 : Blo 393766 1001585 := bstep (se 2 (by rfl) ⟨375594, by rfl⟩ : syracuseStep 1001585 = 751189) B751189
theorem B3393677 : Blo 393766 3393677 := bstep (se 3 (by rfl) ⟨636314, by rfl⟩ : syracuseStep 3393677 = 1272629) B1272629
theorem B477347 : Blo 393766 477347 := bstep (se 1 (by rfl) ⟨358010, by rfl⟩ : syracuseStep 477347 = 716021) B716021
theorem B2148515 : Blo 393766 2148515 := bstep (se 1 (by rfl) ⟨1611386, by rfl⟩ : syracuseStep 2148515 = 3222773) B3222773
theorem B444595 : Blo 393766 444595 := bstep (se 1 (by rfl) ⟨333446, by rfl⟩ : syracuseStep 444595 = 666893) B666893
theorem B2541773 : Blo 393766 2541773 := bstep (se 3 (by rfl) ⟨476582, by rfl⟩ : syracuseStep 2541773 = 953165) B953165
theorem B1329425 : Blo 393766 1329425 := bstep (se 2 (by rfl) ⟨498534, by rfl⟩ : syracuseStep 1329425 = 997069) B997069
theorem B444739 : Blo 393766 444739 := bstep (se 1 (by rfl) ⟨333554, by rfl⟩ : syracuseStep 444739 = 667109) B667109
theorem B1264045 : Blo 393766 1264045 := bstep (se 3 (by rfl) ⟨237008, by rfl⟩ : syracuseStep 1264045 = 474017) B474017
theorem B444883 : Blo 393766 444883 := bstep (se 1 (by rfl) ⟨333662, by rfl⟩ : syracuseStep 444883 = 667325) B667325
theorem B445027 : Blo 393766 445027 := bstep (se 1 (by rfl) ⟨333770, by rfl⟩ : syracuseStep 445027 = 667541) B667541
theorem B445171 : Blo 393766 445171 := bstep (se 1 (by rfl) ⟨333878, by rfl⟩ : syracuseStep 445171 = 667757) B667757
theorem B1329965 : Blo 393766 1329965 := bstep (se 3 (by rfl) ⟨249368, by rfl⟩ : syracuseStep 1329965 = 498737) B498737
theorem B1330019 : Blo 393766 1330019 := bstep (se 1 (by rfl) ⟨997514, by rfl⟩ : syracuseStep 1330019 = 1995029) B1995029
theorem B445315 : Blo 393766 445315 := bstep (se 1 (by rfl) ⟨333986, by rfl⟩ : syracuseStep 445315 = 667973) B667973
theorem B2411441 : Blo 393766 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B445459 : Blo 393766 445459 := bstep (se 1 (by rfl) ⟨334094, by rfl⟩ : syracuseStep 445459 = 668189) B668189
theorem B1002577 : Blo 393766 1002577 := bstep (se 2 (by rfl) ⟨375966, by rfl⟩ : syracuseStep 1002577 = 751933) B751933
theorem B1330289 : Blo 393766 1330289 := bstep (se 2 (by rfl) ⟨498858, by rfl⟩ : syracuseStep 1330289 = 997717) B997717
theorem B445603 : Blo 393766 445603 := bstep (se 1 (by rfl) ⟨334202, by rfl⟩ : syracuseStep 445603 = 668405) B668405
theorem B445747 : Blo 393766 445747 := bstep (se 1 (by rfl) ⟨334310, by rfl⟩ : syracuseStep 445747 = 668621) B668621
theorem B1002851 : Blo 393766 1002851 := bstep (se 1 (by rfl) ⟨752138, by rfl⟩ : syracuseStep 1002851 = 1504277) B1504277
theorem B445891 : Blo 393766 445891 := bstep (se 1 (by rfl) ⟨334418, by rfl⟩ : syracuseStep 445891 = 668837) B668837
theorem B1428941 : Blo 393766 1428941 := bstep (se 3 (by rfl) ⟨267926, by rfl⟩ : syracuseStep 1428941 = 535853) B535853
theorem B1003043 : Blo 393766 1003043 := bstep (se 1 (by rfl) ⟨752282, by rfl⟩ : syracuseStep 1003043 = 1504565) B1504565
theorem B446035 : Blo 393766 446035 := bstep (se 1 (by rfl) ⟨334526, by rfl⟩ : syracuseStep 446035 = 669053) B669053
theorem B1330829 : Blo 393766 1330829 := bstep (se 3 (by rfl) ⟨249530, by rfl⟩ : syracuseStep 1330829 = 499061) B499061
theorem B1330883 : Blo 393766 1330883 := bstep (se 1 (by rfl) ⟨998162, by rfl⟩ : syracuseStep 1330883 = 1996325) B1996325
theorem B3460805 : Blo 393766 3460805 := bstep (se 4 (by rfl) ⟨324450, by rfl⟩ : syracuseStep 3460805 = 648901) B648901
theorem B2248397 : Blo 393766 2248397 := bstep (se 3 (by rfl) ⟨421574, by rfl⟩ : syracuseStep 2248397 = 843149) B843149
theorem B446179 : Blo 393766 446179 := bstep (se 1 (by rfl) ⟨334634, by rfl⟩ : syracuseStep 446179 = 669269) B669269
theorem B1691441 : Blo 393766 1691441 := bstep (se 2 (by rfl) ⟨634290, by rfl⟩ : syracuseStep 1691441 = 1268581) B1268581
theorem B446323 : Blo 393766 446323 := bstep (se 1 (by rfl) ⟨334742, by rfl⟩ : syracuseStep 446323 = 669485) B669485
theorem B1331153 : Blo 393766 1331153 := bstep (se 2 (by rfl) ⟨499182, by rfl⟩ : syracuseStep 1331153 = 998365) B998365
theorem B446467 : Blo 393766 446467 := bstep (se 1 (by rfl) ⟨334850, by rfl⟩ : syracuseStep 446467 = 669701) B669701
theorem B8572949 : Blo 393766 8572949 := bstep (se 6 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 8572949 = 401857) B401857
theorem B446611 : Blo 393766 446611 := bstep (se 1 (by rfl) ⟨334958, by rfl⟩ : syracuseStep 446611 = 669917) B669917
theorem B1495331 : Blo 393766 1495331 := bstep (se 1 (by rfl) ⟨1121498, by rfl⟩ : syracuseStep 1495331 = 2242997) B2242997
theorem B446755 : Blo 393766 446755 := bstep (se 1 (by rfl) ⟨335066, by rfl⟩ : syracuseStep 446755 = 670133) B670133
theorem B1528141 : Blo 393766 1528141 := bstep (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) B573053
theorem B7590257 : Blo 393766 7590257 := bstep (se 2 (by rfl) ⟨2846346, by rfl⟩ : syracuseStep 7590257 = 5692693) B5692693
theorem B446899 : Blo 393766 446899 := bstep (se 1 (by rfl) ⟨335174, by rfl⟩ : syracuseStep 446899 = 670349) B670349
theorem B1003985 : Blo 393766 1003985 := bstep (se 2 (by rfl) ⟨376494, by rfl⟩ : syracuseStep 1003985 = 752989) B752989
theorem B1331693 : Blo 393766 1331693 := bstep (se 3 (by rfl) ⟨249692, by rfl⟩ : syracuseStep 1331693 = 499385) B499385
theorem B1004035 : Blo 393766 1004035 := bstep (se 1 (by rfl) ⟨753026, by rfl⟩ : syracuseStep 1004035 = 1506053) B1506053
theorem B1331747 : Blo 393766 1331747 := bstep (se 1 (by rfl) ⟨998810, by rfl⟩ : syracuseStep 1331747 = 1997621) B1997621
theorem B447043 : Blo 393766 447043 := bstep (se 1 (by rfl) ⟨335282, by rfl⟩ : syracuseStep 447043 = 670565) B670565
theorem B1430093 : Blo 393766 1430093 := bstep (se 3 (by rfl) ⟨268142, by rfl⟩ : syracuseStep 1430093 = 536285) B536285
theorem B2249329 : Blo 393766 2249329 := bstep (se 2 (by rfl) ⟨843498, by rfl⟩ : syracuseStep 2249329 = 1686997) B1686997
theorem B3002993 : Blo 393766 3002993 := bstep (se 2 (by rfl) ⟨1126122, by rfl⟩ : syracuseStep 3002993 = 2252245) B2252245
theorem B8245901 : Blo 393766 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B1004177 : Blo 393766 1004177 := bstep (se 2 (by rfl) ⟨376566, by rfl⟩ : syracuseStep 1004177 = 753133) B753133
theorem B447187 : Blo 393766 447187 := bstep (se 1 (by rfl) ⟨335390, by rfl⟩ : syracuseStep 447187 = 670781) B670781
theorem B1332017 : Blo 393766 1332017 := bstep (se 2 (by rfl) ⟨499506, by rfl⟩ : syracuseStep 1332017 = 999013) B999013
theorem B447331 : Blo 393766 447331 := bstep (se 1 (by rfl) ⟨335498, by rfl⟩ : syracuseStep 447331 = 670997) B670997
theorem B447475 : Blo 393766 447475 := bstep (se 1 (by rfl) ⟨335606, by rfl⟩ : syracuseStep 447475 = 671213) B671213
theorem B676945 : Blo 393766 676945 := bstep (se 2 (by rfl) ⟨253854, by rfl⟩ : syracuseStep 676945 = 507709) B507709
theorem B1496333 : Blo 393766 1496333 := bstep (se 3 (by rfl) ⟨280562, by rfl⟩ : syracuseStep 1496333 = 561125) B561125
theorem B1332557 : Blo 393766 1332557 := bstep (se 3 (by rfl) ⟨249854, by rfl⟩ : syracuseStep 1332557 = 499709) B499709
theorem B1332611 : Blo 393766 1332611 := bstep (se 1 (by rfl) ⟨999458, by rfl⟩ : syracuseStep 1332611 = 1998917) B1998917
theorem B1693133 : Blo 393766 1693133 := bstep (se 3 (by rfl) ⟨317462, by rfl⟩ : syracuseStep 1693133 = 634925) B634925
theorem B1005169 : Blo 393766 1005169 := bstep (se 2 (by rfl) ⟨376938, by rfl⟩ : syracuseStep 1005169 = 753877) B753877
theorem B1332881 : Blo 393766 1332881 := bstep (se 2 (by rfl) ⟨499830, by rfl⟩ : syracuseStep 1332881 = 999661) B999661
theorem B1267427 : Blo 393766 1267427 := bstep (se 1 (by rfl) ⟨950570, by rfl⟩ : syracuseStep 1267427 = 1901141) B1901141
theorem B841585 : Blo 393766 841585 := bstep (se 2 (by rfl) ⟨315594, by rfl⟩ : syracuseStep 841585 = 631189) B631189
theorem B841603 : Blo 393766 841603 := bstep (se 1 (by rfl) ⟨631202, by rfl⟩ : syracuseStep 841603 = 1262405) B1262405
theorem B1005443 : Blo 393766 1005443 := bstep (se 1 (by rfl) ⟨754082, by rfl⟩ : syracuseStep 1005443 = 1508165) B1508165
theorem B2250787 : Blo 393766 2250787 := bstep (se 1 (by rfl) ⟨1688090, by rfl⟩ : syracuseStep 2250787 = 3376181) B3376181
theorem B1005635 : Blo 393766 1005635 := bstep (se 1 (by rfl) ⟨754226, by rfl⟩ : syracuseStep 1005635 = 1508453) B1508453
theorem B481411 : Blo 393766 481411 := bstep (se 1 (by rfl) ⟨361058, by rfl⟩ : syracuseStep 481411 = 722117) B722117
theorem B1333421 : Blo 393766 1333421 := bstep (se 3 (by rfl) ⟨250016, by rfl⟩ : syracuseStep 1333421 = 500033) B500033
theorem B1333475 : Blo 393766 1333475 := bstep (se 1 (by rfl) ⟨1000106, by rfl⟩ : syracuseStep 1333475 = 2000213) B2000213
theorem B1136963 : Blo 393766 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B711011 : Blo 393766 711011 := bstep (se 1 (by rfl) ⟨533258, by rfl⟩ : syracuseStep 711011 = 1066517) B1066517
theorem B1333745 : Blo 393766 1333745 := bstep (se 2 (by rfl) ⟨500154, by rfl⟩ : syracuseStep 1333745 = 1000309) B1000309
theorem B2251313 : Blo 393766 2251313 := bstep (se 2 (by rfl) ⟨844242, by rfl⟩ : syracuseStep 2251313 = 1688485) B1688485
theorem B1268273 : Blo 393766 1268273 := bstep (se 2 (by rfl) ⟨475602, by rfl⟩ : syracuseStep 1268273 = 951205) B951205
theorem B1137233 : Blo 393766 1137233 := bstep (se 2 (by rfl) ⟨426462, by rfl⟩ : syracuseStep 1137233 = 852925) B852925
theorem B711299 : Blo 393766 711299 := bstep (se 1 (by rfl) ⟨533474, by rfl⟩ : syracuseStep 711299 = 1066949) B1066949
theorem B1137539 : Blo 393766 1137539 := bstep (se 1 (by rfl) ⟨853154, by rfl⟩ : syracuseStep 1137539 = 1706309) B1706309
theorem B1006577 : Blo 393766 1006577 := bstep (se 2 (by rfl) ⟨377466, by rfl⟩ : syracuseStep 1006577 = 754933) B754933
theorem B1334285 : Blo 393766 1334285 := bstep (se 3 (by rfl) ⟨250178, by rfl⟩ : syracuseStep 1334285 = 500357) B500357
theorem B1006627 : Blo 393766 1006627 := bstep (se 1 (by rfl) ⟨754970, by rfl⟩ : syracuseStep 1006627 = 1509941) B1509941
theorem B1334339 : Blo 393766 1334339 := bstep (se 1 (by rfl) ⟨1000754, by rfl⟩ : syracuseStep 1334339 = 2001509) B2001509
theorem B1006769 : Blo 393766 1006769 := bstep (se 2 (by rfl) ⟨377538, by rfl⟩ : syracuseStep 1006769 = 755077) B755077
theorem B1072397 : Blo 393766 1072397 := bstep (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) B402149
theorem B711985 : Blo 393766 711985 := bstep (se 2 (by rfl) ⟨266994, by rfl⟩ : syracuseStep 711985 = 533989) B533989
theorem B1498445 : Blo 393766 1498445 := bstep (se 3 (by rfl) ⟨280958, by rfl⟩ : syracuseStep 1498445 = 561917) B561917
theorem B1334609 : Blo 393766 1334609 := bstep (se 2 (by rfl) ⟨500478, by rfl⟩ : syracuseStep 1334609 = 1000957) B1000957
theorem B1433123 : Blo 393766 1433123 := bstep (se 1 (by rfl) ⟨1074842, by rfl⟩ : syracuseStep 1433123 = 2149685) B2149685
theorem B1564337 : Blo 393766 1564337 := bstep (se 2 (by rfl) ⟨586626, by rfl⟩ : syracuseStep 1564337 = 1173253) B1173253
theorem B1335149 : Blo 393766 1335149 := bstep (se 3 (by rfl) ⟨250340, by rfl⟩ : syracuseStep 1335149 = 500681) B500681
theorem B1073027 : Blo 393766 1073027 := bstep (se 1 (by rfl) ⟨804770, by rfl⟩ : syracuseStep 1073027 = 1609541) B1609541
theorem B1335203 : Blo 393766 1335203 := bstep (se 1 (by rfl) ⟨1001402, by rfl⟩ : syracuseStep 1335203 = 2002805) B2002805
theorem B10117061 : Blo 393766 10117061 := bstep (se 4 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 10117061 = 1896949) B1896949
theorem B2252771 : Blo 393766 2252771 := bstep (se 1 (by rfl) ⟨1689578, by rfl⟩ : syracuseStep 2252771 = 3379157) B3379157
theorem B5070833 : Blo 393766 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B843875 : Blo 393766 843875 := bstep (se 1 (by rfl) ⟨632906, by rfl⟩ : syracuseStep 843875 = 1265813) B1265813
theorem B1597553 : Blo 393766 1597553 := bstep (se 2 (by rfl) ⟨599082, by rfl⟩ : syracuseStep 1597553 = 1198165) B1198165
theorem B1499249 : Blo 393766 1499249 := bstep (se 2 (by rfl) ⟨562218, by rfl⟩ : syracuseStep 1499249 = 1124437) B1124437
theorem B680051 : Blo 393766 680051 := bstep (se 1 (by rfl) ⟨510038, by rfl⟩ : syracuseStep 680051 = 1020077) B1020077
theorem B1335473 : Blo 393766 1335473 := bstep (se 2 (by rfl) ⟨500802, by rfl⟩ : syracuseStep 1335473 = 1001605) B1001605
theorem B1270093 : Blo 393766 1270093 := bstep (se 3 (by rfl) ⟨238142, by rfl⟩ : syracuseStep 1270093 = 476285) B476285
theorem B975235 : Blo 393766 975235 := bstep (se 1 (by rfl) ⟨731426, by rfl⟩ : syracuseStep 975235 = 1462853) B1462853
theorem B844337 : Blo 393766 844337 := bstep (se 2 (by rfl) ⟨316626, by rfl⟩ : syracuseStep 844337 = 633253) B633253
theorem B1336013 : Blo 393766 1336013 := bstep (se 3 (by rfl) ⟨250502, by rfl⟩ : syracuseStep 1336013 = 501005) B501005
theorem B1336067 : Blo 393766 1336067 := bstep (se 1 (by rfl) ⟨1002050, by rfl⟩ : syracuseStep 1336067 = 2004101) B2004101
theorem B1499917 : Blo 393766 1499917 := bstep (se 3 (by rfl) ⟨281234, by rfl⟩ : syracuseStep 1499917 = 562469) B562469
theorem B1598413 : Blo 393766 1598413 := bstep (se 3 (by rfl) ⟨299702, by rfl⟩ : syracuseStep 1598413 = 599405) B599405
theorem B1336337 : Blo 393766 1336337 := bstep (se 2 (by rfl) ⟨501126, by rfl⟩ : syracuseStep 1336337 = 1002253) B1002253
theorem B1074637 : Blo 393766 1074637 := bstep (se 3 (by rfl) ⟨201494, by rfl⟩ : syracuseStep 1074637 = 402989) B402989
theorem B1500707 : Blo 393766 1500707 := bstep (se 1 (by rfl) ⟨1125530, by rfl⟩ : syracuseStep 1500707 = 2251061) B2251061
theorem B1336877 : Blo 393766 1336877 := bstep (se 3 (by rfl) ⟨250664, by rfl⟩ : syracuseStep 1336877 = 501329) B501329
theorem B1336931 : Blo 393766 1336931 := bstep (se 1 (by rfl) ⟨1002698, by rfl⟩ : syracuseStep 1336931 = 2005397) B2005397
theorem B1697507 : Blo 393766 1697507 := bstep (se 1 (by rfl) ⟨1273130, by rfl⟩ : syracuseStep 1697507 = 2546261) B2546261
theorem B845635 : Blo 393766 845635 := bstep (se 1 (by rfl) ⟨634226, by rfl⟩ : syracuseStep 845635 = 1268453) B1268453
theorem B2254661 : Blo 393766 2254661 := bstep (se 4 (by rfl) ⟨211374, by rfl⟩ : syracuseStep 2254661 = 422749) B422749
theorem B1337201 : Blo 393766 1337201 := bstep (se 2 (by rfl) ⟨501450, by rfl⟩ : syracuseStep 1337201 = 1002901) B1002901
theorem B714673 : Blo 393766 714673 := bstep (se 2 (by rfl) ⟨268002, by rfl⟩ : syracuseStep 714673 = 536005) B536005
theorem B845891 : Blo 393766 845891 := bstep (se 1 (by rfl) ⟨634418, by rfl⟩ : syracuseStep 845891 = 1268837) B1268837
theorem B649315 : Blo 393766 649315 := bstep (se 1 (by rfl) ⟨486986, by rfl⟩ : syracuseStep 649315 = 973973) B973973
theorem B3369073 : Blo 393766 3369073 := bstep (se 2 (by rfl) ⟨1263402, by rfl⟩ : syracuseStep 3369073 = 2526805) B2526805
theorem B1501361 : Blo 393766 1501361 := bstep (se 2 (by rfl) ⟨563010, by rfl⟩ : syracuseStep 1501361 = 1126021) B1126021
theorem B2418929 : Blo 393766 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B5073293 : Blo 393766 5073293 := bstep (se 3 (by rfl) ⟨951242, by rfl⟩ : syracuseStep 5073293 = 1902485) B1902485
theorem B1337741 : Blo 393766 1337741 := bstep (se 3 (by rfl) ⟨250826, by rfl⟩ : syracuseStep 1337741 = 501653) B501653
theorem B1337795 : Blo 393766 1337795 := bstep (se 1 (by rfl) ⟨1003346, by rfl⟩ : syracuseStep 1337795 = 2006693) B2006693
theorem B1305229 : Blo 393766 1305229 := bstep (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) B489461
theorem B1600163 : Blo 393766 1600163 := bstep (se 1 (by rfl) ⟨1200122, by rfl⟩ : syracuseStep 1600163 = 2400245) B2400245
theorem B1338065 : Blo 393766 1338065 := bstep (se 2 (by rfl) ⟨501774, by rfl⟩ : syracuseStep 1338065 = 1003549) B1003549
theorem B748273 : Blo 393766 748273 := bstep (se 2 (by rfl) ⟨280602, by rfl⟩ : syracuseStep 748273 = 561205) B561205
theorem B1993571 : Blo 393766 1993571 := bstep (se 1 (by rfl) ⟨1495178, by rfl⟩ : syracuseStep 1993571 = 2990357) B2990357
theorem B748433 : Blo 393766 748433 := bstep (se 2 (by rfl) ⟨280662, by rfl⟩ : syracuseStep 748433 = 561325) B561325
theorem B846865 : Blo 393766 846865 := bstep (se 2 (by rfl) ⟨317574, by rfl⟩ : syracuseStep 846865 = 635149) B635149
theorem B1010819 : Blo 393766 1010819 := bstep (se 1 (by rfl) ⟨758114, by rfl⟩ : syracuseStep 1010819 = 1516229) B1516229
theorem B421075 : Blo 393766 421075 := bstep (se 1 (by rfl) ⟨315806, by rfl⟩ : syracuseStep 421075 = 631613) B631613
theorem B1338605 : Blo 393766 1338605 := bstep (se 3 (by rfl) ⟨250988, by rfl⟩ : syracuseStep 1338605 = 501977) B501977
theorem B1338659 : Blo 393766 1338659 := bstep (se 1 (by rfl) ⟨1003994, by rfl⟩ : syracuseStep 1338659 = 2007989) B2007989
theorem B748835 : Blo 393766 748835 := bstep (se 1 (by rfl) ⟨561626, by rfl⟩ : syracuseStep 748835 = 1123253) B1123253
theorem B1338929 : Blo 393766 1338929 := bstep (se 2 (by rfl) ⟨502098, by rfl⟩ : syracuseStep 1338929 = 1004197) B1004197
theorem B1502819 : Blo 393766 1502819 := bstep (se 1 (by rfl) ⟨1127114, by rfl⟩ : syracuseStep 1502819 = 2254229) B2254229
theorem B1502833 : Blo 393766 1502833 := bstep (se 2 (by rfl) ⟨563562, by rfl⟩ : syracuseStep 1502833 = 1127125) B1127125
theorem B1994381 : Blo 393766 1994381 := bstep (se 3 (by rfl) ⟨373946, by rfl⟩ : syracuseStep 1994381 = 747893) B747893
theorem B3665549 : Blo 393766 3665549 := bstep (se 3 (by rfl) ⟨687290, by rfl⟩ : syracuseStep 3665549 = 1374581) B1374581
theorem B847523 : Blo 393766 847523 := bstep (se 1 (by rfl) ⟨635642, by rfl⟩ : syracuseStep 847523 = 1271285) B1271285
theorem B1601201 : Blo 393766 1601201 := bstep (se 2 (by rfl) ⟨600450, by rfl⟩ : syracuseStep 1601201 = 1200901) B1200901
theorem B650929 : Blo 393766 650929 := bstep (se 2 (by rfl) ⟨244098, by rfl⟩ : syracuseStep 650929 = 488197) B488197
theorem B1273553 : Blo 393766 1273553 := bstep (se 2 (by rfl) ⟨477582, by rfl⟩ : syracuseStep 1273553 = 955165) B955165
theorem B9596693 : Blo 393766 9596693 := bstep (se 6 (by rfl) ⟨224922, by rfl⟩ : syracuseStep 9596693 = 449845) B449845
theorem B1273745 : Blo 393766 1273745 := bstep (se 2 (by rfl) ⟨477654, by rfl⟩ : syracuseStep 1273745 = 955309) B955309
theorem B1339469 : Blo 393766 1339469 := bstep (se 3 (by rfl) ⟨251150, by rfl⟩ : syracuseStep 1339469 = 502301) B502301
theorem B1339523 : Blo 393766 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B749731 : Blo 393766 749731 := bstep (se 1 (by rfl) ⟨562298, by rfl⟩ : syracuseStep 749731 = 1124597) B1124597
theorem B749891 : Blo 393766 749891 := bstep (se 1 (by rfl) ⟨562418, by rfl⟩ : syracuseStep 749891 = 1124837) B1124837
theorem B2879813 : Blo 393766 2879813 := bstep (se 4 (by rfl) ⟨269982, by rfl⟩ : syracuseStep 2879813 = 539965) B539965
theorem B1732963 : Blo 393766 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B5140849 : Blo 393766 5140849 := bstep (se 2 (by rfl) ⟨1927818, by rfl⟩ : syracuseStep 5140849 = 3855637) B3855637
theorem B1339793 : Blo 393766 1339793 := bstep (se 2 (by rfl) ⟨502422, by rfl⟩ : syracuseStep 1339793 = 1004845) B1004845
theorem B422339 : Blo 393766 422339 := bstep (se 1 (by rfl) ⟨316754, by rfl⟩ : syracuseStep 422339 = 633509) B633509
theorem B4518341 : Blo 393766 4518341 := bstep (se 4 (by rfl) ⟨423594, by rfl⟩ : syracuseStep 4518341 = 847189) B847189
theorem B848369 : Blo 393766 848369 := bstep (se 2 (by rfl) ⟨318138, by rfl⟩ : syracuseStep 848369 = 636277) B636277
theorem B1340333 : Blo 393766 1340333 := bstep (se 3 (by rfl) ⟨251312, by rfl⟩ : syracuseStep 1340333 = 502625) B502625
theorem B1340387 : Blo 393766 1340387 := bstep (se 1 (by rfl) ⟨1005290, by rfl⟩ : syracuseStep 1340387 = 2010581) B2010581
theorem B1504291 : Blo 393766 1504291 := bstep (se 1 (by rfl) ⟨1128218, by rfl⟩ : syracuseStep 1504291 = 2256437) B2256437
theorem B423091 : Blo 393766 423091 := bstep (se 1 (by rfl) ⟨317318, by rfl⟩ : syracuseStep 423091 = 634637) B634637
theorem B1340657 : Blo 393766 1340657 := bstep (se 2 (by rfl) ⟨502746, by rfl⟩ : syracuseStep 1340657 = 1005493) B1005493
theorem B750961 : Blo 393766 750961 := bstep (se 2 (by rfl) ⟨281610, by rfl⟩ : syracuseStep 750961 = 563221) B563221
theorem B1341197 : Blo 393766 1341197 := bstep (se 3 (by rfl) ⟨251474, by rfl⟩ : syracuseStep 1341197 = 502949) B502949
theorem B1341251 : Blo 393766 1341251 := bstep (se 1 (by rfl) ⟨1005938, by rfl⟩ : syracuseStep 1341251 = 2011877) B2011877
theorem B686051 : Blo 393766 686051 := bstep (se 1 (by rfl) ⟨514538, by rfl⟩ : syracuseStep 686051 = 1029077) B1029077
theorem B1341521 : Blo 393766 1341521 := bstep (se 2 (by rfl) ⟨503070, by rfl⟩ : syracuseStep 1341521 = 1006141) B1006141
theorem B948419 : Blo 393766 948419 := bstep (se 1 (by rfl) ⟨711314, by rfl⟩ : syracuseStep 948419 = 1422629) B1422629
theorem B2291939 : Blo 393766 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B2849093 : Blo 393766 2849093 := bstep (se 4 (by rfl) ⟨267102, by rfl⟩ : syracuseStep 2849093 = 534205) B534205
theorem B752017 : Blo 393766 752017 := bstep (se 2 (by rfl) ⟨282006, by rfl⟩ : syracuseStep 752017 = 564013) B564013
theorem B1997297 : Blo 393766 1997297 := bstep (se 2 (by rfl) ⟨748986, by rfl⟩ : syracuseStep 1997297 = 1497973) B1497973
theorem B424483 : Blo 393766 424483 := bstep (se 1 (by rfl) ⟨318362, by rfl⟩ : syracuseStep 424483 = 636725) B636725
theorem B1342061 : Blo 393766 1342061 := bstep (se 3 (by rfl) ⟨251636, by rfl⟩ : syracuseStep 1342061 = 503273) B503273
theorem B1145507 : Blo 393766 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B1342115 : Blo 393766 1342115 := bstep (se 1 (by rfl) ⟨1006586, by rfl⟩ : syracuseStep 1342115 = 2013173) B2013173
theorem B916145 : Blo 393766 916145 := bstep (se 2 (by rfl) ⟨343554, by rfl⟩ : syracuseStep 916145 = 687109) B687109
theorem B752419 : Blo 393766 752419 := bstep (se 1 (by rfl) ⟨564314, by rfl⟩ : syracuseStep 752419 = 1128629) B1128629
theorem B752465 : Blo 393766 752465 := bstep (se 2 (by rfl) ⟨282174, by rfl⟩ : syracuseStep 752465 = 564349) B564349
theorem B1342385 : Blo 393766 1342385 := bstep (se 2 (by rfl) ⟨503394, by rfl⟩ : syracuseStep 1342385 = 1006789) B1006789
theorem B4258757 : Blo 393766 4258757 := bstep (se 4 (by rfl) ⟨399258, by rfl⟩ : syracuseStep 4258757 = 798517) B798517
theorem B949265 : Blo 393766 949265 := bstep (se 2 (by rfl) ⟨355974, by rfl⟩ : syracuseStep 949265 = 711949) B711949
theorem B752753 : Blo 393766 752753 := bstep (se 2 (by rfl) ⟨282282, by rfl⟩ : syracuseStep 752753 = 564565) B564565
theorem B1506509 : Blo 393766 1506509 := bstep (se 3 (by rfl) ⟨282470, by rfl⟩ : syracuseStep 1506509 = 564941) B564941
theorem B949475 : Blo 393766 949475 := bstep (se 1 (by rfl) ⟨712106, by rfl⟩ : syracuseStep 949475 = 1424213) B1424213
theorem B2718947 : Blo 393766 2718947 := bstep (se 1 (by rfl) ⟨2039210, by rfl⟩ : syracuseStep 2718947 = 4078421) B4078421
theorem B3374405 : Blo 393766 3374405 := bstep (se 4 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 3374405 = 632701) B632701
theorem B2751877 : Blo 393766 2751877 := bstep (se 4 (by rfl) ⟨257988, by rfl⟩ : syracuseStep 2751877 = 515977) B515977
theorem B2260493 : Blo 393766 2260493 := bstep (se 3 (by rfl) ⟨423842, by rfl⟩ : syracuseStep 2260493 = 847685) B847685
theorem B753475 : Blo 393766 753475 := bstep (se 1 (by rfl) ⟨565106, by rfl⟩ : syracuseStep 753475 = 1130213) B1130213
theorem B2719601 : Blo 393766 2719601 := bstep (se 2 (by rfl) ⟨1019850, by rfl⟩ : syracuseStep 2719601 = 2039701) B2039701
theorem B1998755 : Blo 393766 1998755 := bstep (se 1 (by rfl) ⟨1499066, by rfl⟩ : syracuseStep 1998755 = 2998133) B2998133
theorem B13565893 : Blo 393766 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B753779 : Blo 393766 753779 := bstep (se 1 (by rfl) ⟨565334, by rfl⟩ : syracuseStep 753779 = 1130669) B1130669
theorem B3440819 : Blo 393766 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B393771 : Blo 393766 393771 := bstep (se 1 (by rfl) ⟨295328, by rfl⟩ : syracuseStep 393771 = 590657) B590657
theorem B393783 : Blo 393766 393783 := bstep (se 1 (by rfl) ⟨295337, by rfl⟩ : syracuseStep 393783 = 590675) B590675
theorem B393803 : Blo 393766 393803 := bstep (se 1 (by rfl) ⟨295352, by rfl⟩ : syracuseStep 393803 = 590705) B590705
theorem B393815 : Blo 393766 393815 := bstep (se 1 (by rfl) ⟨295361, by rfl⟩ : syracuseStep 393815 = 590723) B590723
theorem B754265 : Blo 393766 754265 := bstep (se 2 (by rfl) ⟨282849, by rfl⟩ : syracuseStep 754265 = 565699) B565699
theorem B393835 : Blo 393766 393835 := bstep (se 1 (by rfl) ⟨295376, by rfl⟩ : syracuseStep 393835 = 590753) B590753
theorem B393847 : Blo 393766 393847 := bstep (se 1 (by rfl) ⟨295385, by rfl⟩ : syracuseStep 393847 = 590771) B590771
theorem B393867 : Blo 393766 393867 := bstep (se 1 (by rfl) ⟨295400, by rfl⟩ : syracuseStep 393867 = 590801) B590801
theorem B393879 : Blo 393766 393879 := bstep (se 1 (by rfl) ⟨295409, by rfl⟩ : syracuseStep 393879 = 590819) B590819
theorem B393899 : Blo 393766 393899 := bstep (se 1 (by rfl) ⟨295424, by rfl⟩ : syracuseStep 393899 = 590849) B590849
theorem B393911 : Blo 393766 393911 := bstep (se 1 (by rfl) ⟨295433, by rfl⟩ : syracuseStep 393911 = 590867) B590867
theorem B393931 : Blo 393766 393931 := bstep (se 1 (by rfl) ⟨295448, by rfl⟩ : syracuseStep 393931 = 590897) B590897
theorem B393943 : Blo 393766 393943 := bstep (se 1 (by rfl) ⟨295457, by rfl⟩ : syracuseStep 393943 = 590915) B590915
theorem B393963 : Blo 393766 393963 := bstep (se 1 (by rfl) ⟨295472, by rfl⟩ : syracuseStep 393963 = 590945) B590945
theorem B393975 : Blo 393766 393975 := bstep (se 1 (by rfl) ⟨295481, by rfl⟩ : syracuseStep 393975 = 590963) B590963
theorem B393995 : Blo 393766 393995 := bstep (se 1 (by rfl) ⟨295496, by rfl⟩ : syracuseStep 393995 = 590993) B590993
theorem B394007 : Blo 393766 394007 := bstep (se 1 (by rfl) ⟨295505, by rfl⟩ : syracuseStep 394007 = 591011) B591011
theorem B394027 : Blo 393766 394027 := bstep (se 1 (by rfl) ⟨295520, by rfl⟩ : syracuseStep 394027 = 591041) B591041
theorem B394039 : Blo 393766 394039 := bstep (se 1 (by rfl) ⟨295529, by rfl⟩ : syracuseStep 394039 = 591059) B591059
theorem B394059 : Blo 393766 394059 := bstep (se 1 (by rfl) ⟨295544, by rfl⟩ : syracuseStep 394059 = 591089) B591089
theorem B394071 : Blo 393766 394071 := bstep (se 1 (by rfl) ⟨295553, by rfl⟩ : syracuseStep 394071 = 591107) B591107
theorem B590681 : Blo 393766 590681 := bstep (se 2 (by rfl) ⟨221505, by rfl⟩ : syracuseStep 590681 = 443011) B443011
theorem B394091 : Blo 393766 394091 := bstep (se 1 (by rfl) ⟨295568, by rfl⟩ : syracuseStep 394091 = 591137) B591137
theorem B394103 : Blo 393766 394103 := bstep (se 1 (by rfl) ⟨295577, by rfl⟩ : syracuseStep 394103 = 591155) B591155
theorem B394123 : Blo 393766 394123 := bstep (se 1 (by rfl) ⟨295592, by rfl⟩ : syracuseStep 394123 = 591185) B591185
theorem B394135 : Blo 393766 394135 := bstep (se 1 (by rfl) ⟨295601, by rfl⟩ : syracuseStep 394135 = 591203) B591203
theorem B394155 : Blo 393766 394155 := bstep (se 1 (by rfl) ⟨295616, by rfl⟩ : syracuseStep 394155 = 591233) B591233
theorem B394167 : Blo 393766 394167 := bstep (se 1 (by rfl) ⟨295625, by rfl⟩ : syracuseStep 394167 = 591251) B591251
theorem B590795 : Blo 393766 590795 := bstep (se 1 (by rfl) ⟨443096, by rfl⟩ : syracuseStep 590795 = 886193) B886193
theorem B394187 : Blo 393766 394187 := bstep (se 1 (by rfl) ⟨295640, by rfl⟩ : syracuseStep 394187 = 591281) B591281
theorem B3015629 : Blo 393766 3015629 := bstep (se 3 (by rfl) ⟨565430, by rfl⟩ : syracuseStep 3015629 = 1130861) B1130861
theorem B590807 : Blo 393766 590807 := bstep (se 1 (by rfl) ⟨443105, by rfl⟩ : syracuseStep 590807 = 886211) B886211
theorem B394199 : Blo 393766 394199 := bstep (se 1 (by rfl) ⟨295649, by rfl⟩ : syracuseStep 394199 = 591299) B591299
theorem B394219 : Blo 393766 394219 := bstep (se 1 (by rfl) ⟨295664, by rfl⟩ : syracuseStep 394219 = 591329) B591329
theorem B394231 : Blo 393766 394231 := bstep (se 1 (by rfl) ⟨295673, by rfl⟩ : syracuseStep 394231 = 591347) B591347
theorem B394251 : Blo 393766 394251 := bstep (se 1 (by rfl) ⟨295688, by rfl⟩ : syracuseStep 394251 = 591377) B591377
theorem B1999889 : Blo 393766 1999889 := bstep (se 2 (by rfl) ⟨749958, by rfl⟩ : syracuseStep 1999889 = 1499917) B1499917
theorem B394263 : Blo 393766 394263 := bstep (se 1 (by rfl) ⟨295697, by rfl⟩ : syracuseStep 394263 = 591395) B591395
theorem B590873 : Blo 393766 590873 := bstep (se 2 (by rfl) ⟨221577, by rfl⟩ : syracuseStep 590873 = 443155) B443155
theorem B394283 : Blo 393766 394283 := bstep (se 1 (by rfl) ⟨295712, by rfl⟩ : syracuseStep 394283 = 591425) B591425
theorem B394295 : Blo 393766 394295 := bstep (se 1 (by rfl) ⟨295721, by rfl⟩ : syracuseStep 394295 = 591443) B591443
theorem B394315 : Blo 393766 394315 := bstep (se 1 (by rfl) ⟨295736, by rfl⟩ : syracuseStep 394315 = 591473) B591473
theorem B394327 : Blo 393766 394327 := bstep (se 1 (by rfl) ⟨295745, by rfl⟩ : syracuseStep 394327 = 591491) B591491
theorem B394347 : Blo 393766 394347 := bstep (se 1 (by rfl) ⟨295760, by rfl⟩ : syracuseStep 394347 = 591521) B591521
theorem B394359 : Blo 393766 394359 := bstep (se 1 (by rfl) ⟨295769, by rfl⟩ : syracuseStep 394359 = 591539) B591539
theorem B1508483 : Blo 393766 1508483 := bstep (se 1 (by rfl) ⟨1131362, by rfl⟩ : syracuseStep 1508483 = 2262725) B2262725
theorem B590987 : Blo 393766 590987 := bstep (se 1 (by rfl) ⟨443240, by rfl⟩ : syracuseStep 590987 = 886481) B886481
theorem B394379 : Blo 393766 394379 := bstep (se 1 (by rfl) ⟨295784, by rfl⟩ : syracuseStep 394379 = 591569) B591569
theorem B590999 : Blo 393766 590999 := bstep (se 1 (by rfl) ⟨443249, by rfl⟩ : syracuseStep 590999 = 886499) B886499
theorem B394391 : Blo 393766 394391 := bstep (se 1 (by rfl) ⟨295793, by rfl⟩ : syracuseStep 394391 = 591587) B591587
theorem B394411 : Blo 393766 394411 := bstep (se 1 (by rfl) ⟨295808, by rfl⟩ : syracuseStep 394411 = 591617) B591617
theorem B2000051 : Blo 393766 2000051 := bstep (se 1 (by rfl) ⟨1500038, by rfl⟩ : syracuseStep 2000051 = 3000077) B3000077
theorem B394423 : Blo 393766 394423 := bstep (se 1 (by rfl) ⟨295817, by rfl⟩ : syracuseStep 394423 = 591635) B591635
theorem B394443 : Blo 393766 394443 := bstep (se 1 (by rfl) ⟨295832, by rfl⟩ : syracuseStep 394443 = 591665) B591665
theorem B394455 : Blo 393766 394455 := bstep (se 1 (by rfl) ⟨295841, by rfl⟩ : syracuseStep 394455 = 591683) B591683
theorem B885977 : Blo 393766 885977 := bstep (se 2 (by rfl) ⟨332241, by rfl⟩ : syracuseStep 885977 = 664483) B664483
theorem B591065 : Blo 393766 591065 := bstep (se 2 (by rfl) ⟨221649, by rfl⟩ : syracuseStep 591065 = 443299) B443299
theorem B394475 : Blo 393766 394475 := bstep (se 1 (by rfl) ⟨295856, by rfl⟩ : syracuseStep 394475 = 591713) B591713
theorem B394487 : Blo 393766 394487 := bstep (se 1 (by rfl) ⟨295865, by rfl⟩ : syracuseStep 394487 = 591731) B591731
theorem B394507 : Blo 393766 394507 := bstep (se 1 (by rfl) ⟨295880, by rfl⟩ : syracuseStep 394507 = 591761) B591761
theorem B2131217 : Blo 393766 2131217 := bstep (se 2 (by rfl) ⟨799206, by rfl⟩ : syracuseStep 2131217 = 1598413) B1598413
theorem B394519 : Blo 393766 394519 := bstep (se 1 (by rfl) ⟨295889, by rfl⟩ : syracuseStep 394519 = 591779) B591779
theorem B394539 : Blo 393766 394539 := bstep (se 1 (by rfl) ⟨295904, by rfl⟩ : syracuseStep 394539 = 591809) B591809
theorem B886067 : Blo 393766 886067 := bstep (se 1 (by rfl) ⟨664550, by rfl⟩ : syracuseStep 886067 = 1329101) B1329101
theorem B394551 : Blo 393766 394551 := bstep (se 1 (by rfl) ⟨295913, by rfl⟩ : syracuseStep 394551 = 591827) B591827
theorem B591179 : Blo 393766 591179 := bstep (se 1 (by rfl) ⟨443384, by rfl⟩ : syracuseStep 591179 = 886769) B886769
theorem B394571 : Blo 393766 394571 := bstep (se 1 (by rfl) ⟨295928, by rfl⟩ : syracuseStep 394571 = 591857) B591857
theorem B886103 : Blo 393766 886103 := bstep (se 1 (by rfl) ⟨664577, by rfl⟩ : syracuseStep 886103 = 1329155) B1329155
theorem B591191 : Blo 393766 591191 := bstep (se 1 (by rfl) ⟨443393, by rfl⟩ : syracuseStep 591191 = 886787) B886787
theorem B394583 : Blo 393766 394583 := bstep (se 1 (by rfl) ⟨295937, by rfl⟩ : syracuseStep 394583 = 591875) B591875
theorem B394603 : Blo 393766 394603 := bstep (se 1 (by rfl) ⟨295952, by rfl⟩ : syracuseStep 394603 = 591905) B591905
theorem B394615 : Blo 393766 394615 := bstep (se 1 (by rfl) ⟨295961, by rfl⟩ : syracuseStep 394615 = 591923) B591923
theorem B394635 : Blo 393766 394635 := bstep (se 1 (by rfl) ⟨295976, by rfl⟩ : syracuseStep 394635 = 591953) B591953
theorem B394647 : Blo 393766 394647 := bstep (se 1 (by rfl) ⟨295985, by rfl⟩ : syracuseStep 394647 = 591971) B591971
theorem B591257 : Blo 393766 591257 := bstep (se 2 (by rfl) ⟨221721, by rfl⟩ : syracuseStep 591257 = 443443) B443443
theorem B394667 : Blo 393766 394667 := bstep (se 1 (by rfl) ⟨296000, by rfl⟩ : syracuseStep 394667 = 592001) B592001
theorem B3016115 : Blo 393766 3016115 := bstep (se 1 (by rfl) ⟨2262086, by rfl⟩ : syracuseStep 3016115 = 4524173) B4524173
theorem B2262451 : Blo 393766 2262451 := bstep (se 1 (by rfl) ⟨1696838, by rfl⟩ : syracuseStep 2262451 = 3393677) B3393677
theorem B394679 : Blo 393766 394679 := bstep (se 1 (by rfl) ⟨296009, by rfl⟩ : syracuseStep 394679 = 592019) B592019
theorem B394699 : Blo 393766 394699 := bstep (se 1 (by rfl) ⟨296024, by rfl⟩ : syracuseStep 394699 = 592049) B592049
theorem B394711 : Blo 393766 394711 := bstep (se 1 (by rfl) ⟨296033, by rfl⟩ : syracuseStep 394711 = 592067) B592067
theorem B394731 : Blo 393766 394731 := bstep (se 1 (by rfl) ⟨296048, by rfl⟩ : syracuseStep 394731 = 592097) B592097
theorem B394743 : Blo 393766 394743 := bstep (se 1 (by rfl) ⟨296057, by rfl⟩ : syracuseStep 394743 = 592115) B592115
theorem B886283 : Blo 393766 886283 := bstep (se 1 (by rfl) ⟨664712, by rfl⟩ : syracuseStep 886283 = 1329425) B1329425
theorem B591371 : Blo 393766 591371 := bstep (se 1 (by rfl) ⟨443528, by rfl⟩ : syracuseStep 591371 = 887057) B887057
theorem B394763 : Blo 393766 394763 := bstep (se 1 (by rfl) ⟨296072, by rfl⟩ : syracuseStep 394763 = 592145) B592145
theorem B591383 : Blo 393766 591383 := bstep (se 1 (by rfl) ⟨443537, by rfl⟩ : syracuseStep 591383 = 887075) B887075
theorem B394775 : Blo 393766 394775 := bstep (se 1 (by rfl) ⟨296081, by rfl⟩ : syracuseStep 394775 = 592163) B592163
theorem B394795 : Blo 393766 394795 := bstep (se 1 (by rfl) ⟨296096, by rfl⟩ : syracuseStep 394795 = 592193) B592193
theorem B394807 : Blo 393766 394807 := bstep (se 1 (by rfl) ⟨296105, by rfl⟩ : syracuseStep 394807 = 592211) B592211
theorem B886337 : Blo 393766 886337 := bstep (se 2 (by rfl) ⟨332376, by rfl⟩ : syracuseStep 886337 = 664753) B664753
theorem B394827 : Blo 393766 394827 := bstep (se 1 (by rfl) ⟨296120, by rfl⟩ : syracuseStep 394827 = 592241) B592241
theorem B1508939 : Blo 393766 1508939 := bstep (se 1 (by rfl) ⟨1131704, by rfl⟩ : syracuseStep 1508939 = 2263409) B2263409
theorem B394839 : Blo 393766 394839 := bstep (se 1 (by rfl) ⟨296129, by rfl⟩ : syracuseStep 394839 = 592259) B592259
theorem B591449 : Blo 393766 591449 := bstep (se 2 (by rfl) ⟨221793, by rfl⟩ : syracuseStep 591449 = 443587) B443587
theorem B394859 : Blo 393766 394859 := bstep (se 1 (by rfl) ⟨296144, by rfl⟩ : syracuseStep 394859 = 592289) B592289
theorem B394871 : Blo 393766 394871 := bstep (se 1 (by rfl) ⟨296153, by rfl⟩ : syracuseStep 394871 = 592307) B592307
theorem B394891 : Blo 393766 394891 := bstep (se 1 (by rfl) ⟨296168, by rfl⟩ : syracuseStep 394891 = 592337) B592337
theorem B394903 : Blo 393766 394903 := bstep (se 1 (by rfl) ⟨296177, by rfl⟩ : syracuseStep 394903 = 592355) B592355
theorem B394923 : Blo 393766 394923 := bstep (se 1 (by rfl) ⟨296192, by rfl⟩ : syracuseStep 394923 = 592385) B592385
theorem B394935 : Blo 393766 394935 := bstep (se 1 (by rfl) ⟨296201, by rfl⟩ : syracuseStep 394935 = 592403) B592403
theorem B591563 : Blo 393766 591563 := bstep (se 1 (by rfl) ⟨443672, by rfl⟩ : syracuseStep 591563 = 887345) B887345
theorem B394955 : Blo 393766 394955 := bstep (se 1 (by rfl) ⟨296216, by rfl⟩ : syracuseStep 394955 = 592433) B592433
theorem B591575 : Blo 393766 591575 := bstep (se 1 (by rfl) ⟨443681, by rfl⟩ : syracuseStep 591575 = 887363) B887363
theorem B394967 : Blo 393766 394967 := bstep (se 1 (by rfl) ⟨296225, by rfl⟩ : syracuseStep 394967 = 592451) B592451
theorem B394987 : Blo 393766 394987 := bstep (se 1 (by rfl) ⟨296240, by rfl⟩ : syracuseStep 394987 = 592481) B592481
theorem B394999 : Blo 393766 394999 := bstep (se 1 (by rfl) ⟨296249, by rfl⟩ : syracuseStep 394999 = 592499) B592499
theorem B395019 : Blo 393766 395019 := bstep (se 1 (by rfl) ⟨296264, by rfl⟩ : syracuseStep 395019 = 592529) B592529
theorem B1509137 : Blo 393766 1509137 := bstep (se 2 (by rfl) ⟨565926, by rfl⟩ : syracuseStep 1509137 = 1131853) B1131853
theorem B395031 : Blo 393766 395031 := bstep (se 1 (by rfl) ⟨296273, by rfl⟩ : syracuseStep 395031 = 592547) B592547
theorem B886553 : Blo 393766 886553 := bstep (se 2 (by rfl) ⟨332457, by rfl⟩ : syracuseStep 886553 = 664915) B664915
theorem B591641 : Blo 393766 591641 := bstep (se 2 (by rfl) ⟨221865, by rfl⟩ : syracuseStep 591641 = 443731) B443731
theorem B395051 : Blo 393766 395051 := bstep (se 1 (by rfl) ⟨296288, by rfl⟩ : syracuseStep 395051 = 592577) B592577
theorem B395063 : Blo 393766 395063 := bstep (se 1 (by rfl) ⟨296297, by rfl⟩ : syracuseStep 395063 = 592595) B592595
theorem B395083 : Blo 393766 395083 := bstep (se 1 (by rfl) ⟨296312, by rfl⟩ : syracuseStep 395083 = 592625) B592625
theorem B395095 : Blo 393766 395095 := bstep (se 1 (by rfl) ⟨296321, by rfl⟩ : syracuseStep 395095 = 592643) B592643
theorem B395115 : Blo 393766 395115 := bstep (se 1 (by rfl) ⟨296336, by rfl⟩ : syracuseStep 395115 = 592673) B592673
theorem B886643 : Blo 393766 886643 := bstep (se 1 (by rfl) ⟨664982, by rfl⟩ : syracuseStep 886643 = 1329965) B1329965
theorem B395127 : Blo 393766 395127 := bstep (se 1 (by rfl) ⟨296345, by rfl⟩ : syracuseStep 395127 = 592691) B592691
theorem B591755 : Blo 393766 591755 := bstep (se 1 (by rfl) ⟨443816, by rfl⟩ : syracuseStep 591755 = 887633) B887633
theorem B395147 : Blo 393766 395147 := bstep (se 1 (by rfl) ⟨296360, by rfl⟩ : syracuseStep 395147 = 592721) B592721
theorem B886679 : Blo 393766 886679 := bstep (se 1 (by rfl) ⟨665009, by rfl⟩ : syracuseStep 886679 = 1330019) B1330019
theorem B591767 : Blo 393766 591767 := bstep (se 1 (by rfl) ⟨443825, by rfl⟩ : syracuseStep 591767 = 887651) B887651
theorem B395159 : Blo 393766 395159 := bstep (se 1 (by rfl) ⟨296369, by rfl⟩ : syracuseStep 395159 = 592739) B592739
theorem B395179 : Blo 393766 395179 := bstep (se 1 (by rfl) ⟨296384, by rfl⟩ : syracuseStep 395179 = 592769) B592769
theorem B395191 : Blo 393766 395191 := bstep (se 1 (by rfl) ⟨296393, by rfl⟩ : syracuseStep 395191 = 592787) B592787
theorem B395211 : Blo 393766 395211 := bstep (se 1 (by rfl) ⟨296408, by rfl⟩ : syracuseStep 395211 = 592817) B592817
theorem B1607627 : Blo 393766 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B395223 : Blo 393766 395223 := bstep (se 1 (by rfl) ⟨296417, by rfl⟩ : syracuseStep 395223 = 592835) B592835
theorem B591833 : Blo 393766 591833 := bstep (se 2 (by rfl) ⟨221937, by rfl⟩ : syracuseStep 591833 = 443875) B443875
theorem B395243 : Blo 393766 395243 := bstep (se 1 (by rfl) ⟨296432, by rfl⟩ : syracuseStep 395243 = 592865) B592865
theorem B395255 : Blo 393766 395255 := bstep (se 1 (by rfl) ⟨296441, by rfl⟩ : syracuseStep 395255 = 592883) B592883
theorem B395275 : Blo 393766 395275 := bstep (se 1 (by rfl) ⟨296456, by rfl⟩ : syracuseStep 395275 = 592913) B592913
theorem B854039 : Blo 393766 854039 := bstep (se 1 (by rfl) ⟨640529, by rfl⟩ : syracuseStep 854039 = 1281059) B1281059
theorem B395287 : Blo 393766 395287 := bstep (se 1 (by rfl) ⟨296465, by rfl⟩ : syracuseStep 395287 = 592931) B592931
theorem B395307 : Blo 393766 395307 := bstep (se 1 (by rfl) ⟨296480, by rfl⟩ : syracuseStep 395307 = 592961) B592961
theorem B395319 : Blo 393766 395319 := bstep (se 1 (by rfl) ⟨296489, by rfl⟩ : syracuseStep 395319 = 592979) B592979
theorem B886859 : Blo 393766 886859 := bstep (se 1 (by rfl) ⟨665144, by rfl⟩ : syracuseStep 886859 = 1330289) B1330289
theorem B591947 : Blo 393766 591947 := bstep (se 1 (by rfl) ⟨443960, by rfl⟩ : syracuseStep 591947 = 887921) B887921
theorem B395339 : Blo 393766 395339 := bstep (se 1 (by rfl) ⟨296504, by rfl⟩ : syracuseStep 395339 = 593009) B593009
theorem B591959 : Blo 393766 591959 := bstep (se 1 (by rfl) ⟨443969, by rfl⟩ : syracuseStep 591959 = 887939) B887939
theorem B395351 : Blo 393766 395351 := bstep (se 1 (by rfl) ⟨296513, by rfl⟩ : syracuseStep 395351 = 593027) B593027
theorem B395371 : Blo 393766 395371 := bstep (se 1 (by rfl) ⟨296528, by rfl⟩ : syracuseStep 395371 = 593057) B593057
theorem B395383 : Blo 393766 395383 := bstep (se 1 (by rfl) ⟨296537, by rfl⟩ : syracuseStep 395383 = 593075) B593075
theorem B886913 : Blo 393766 886913 := bstep (se 2 (by rfl) ⟨332592, by rfl⟩ : syracuseStep 886913 = 665185) B665185
theorem B395403 : Blo 393766 395403 := bstep (se 1 (by rfl) ⟨296552, by rfl⟩ : syracuseStep 395403 = 593105) B593105
theorem B395415 : Blo 393766 395415 := bstep (se 1 (by rfl) ⟨296561, by rfl⟩ : syracuseStep 395415 = 593123) B593123
theorem B592025 : Blo 393766 592025 := bstep (se 2 (by rfl) ⟨222009, by rfl⟩ : syracuseStep 592025 = 444019) B444019
theorem B395435 : Blo 393766 395435 := bstep (se 1 (by rfl) ⟨296576, by rfl⟩ : syracuseStep 395435 = 593153) B593153
theorem B1673389 : Blo 393766 1673389 := bstep (se 3 (by rfl) ⟨313760, by rfl⟩ : syracuseStep 1673389 = 627521) B627521
theorem B395447 : Blo 393766 395447 := bstep (se 1 (by rfl) ⟨296585, by rfl⟩ : syracuseStep 395447 = 593171) B593171
theorem B395467 : Blo 393766 395467 := bstep (se 1 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 395467 = 593201) B593201
theorem B395479 : Blo 393766 395479 := bstep (se 1 (by rfl) ⟨296609, by rfl⟩ : syracuseStep 395479 = 593219) B593219
theorem B395499 : Blo 393766 395499 := bstep (se 1 (by rfl) ⟨296624, by rfl⟩ : syracuseStep 395499 = 593249) B593249
theorem B395511 : Blo 393766 395511 := bstep (se 1 (by rfl) ⟨296633, by rfl⟩ : syracuseStep 395511 = 593267) B593267
theorem B592139 : Blo 393766 592139 := bstep (se 1 (by rfl) ⟨444104, by rfl⟩ : syracuseStep 592139 = 888209) B888209
theorem B395531 : Blo 393766 395531 := bstep (se 1 (by rfl) ⟨296648, by rfl⟩ : syracuseStep 395531 = 593297) B593297
theorem B592151 : Blo 393766 592151 := bstep (se 1 (by rfl) ⟨444113, by rfl⟩ : syracuseStep 592151 = 888227) B888227
theorem B395543 : Blo 393766 395543 := bstep (se 1 (by rfl) ⟨296657, by rfl⟩ : syracuseStep 395543 = 593315) B593315
theorem B395563 : Blo 393766 395563 := bstep (se 1 (by rfl) ⟨296672, by rfl⟩ : syracuseStep 395563 = 593345) B593345
theorem B952627 : Blo 393766 952627 := bstep (se 1 (by rfl) ⟨714470, by rfl⟩ : syracuseStep 952627 = 1428941) B1428941
theorem B395575 : Blo 393766 395575 := bstep (se 1 (by rfl) ⟨296681, by rfl⟩ : syracuseStep 395575 = 593363) B593363
theorem B395595 : Blo 393766 395595 := bstep (se 1 (by rfl) ⟨296696, by rfl⟩ : syracuseStep 395595 = 593393) B593393
theorem B395607 : Blo 393766 395607 := bstep (se 1 (by rfl) ⟨296705, by rfl⟩ : syracuseStep 395607 = 593411) B593411
theorem B887129 : Blo 393766 887129 := bstep (se 2 (by rfl) ⟨332673, by rfl⟩ : syracuseStep 887129 = 665347) B665347
theorem B592217 : Blo 393766 592217 := bstep (se 2 (by rfl) ⟨222081, by rfl⟩ : syracuseStep 592217 = 444163) B444163
theorem B395627 : Blo 393766 395627 := bstep (se 1 (by rfl) ⟨296720, by rfl⟩ : syracuseStep 395627 = 593441) B593441
theorem B395639 : Blo 393766 395639 := bstep (se 1 (by rfl) ⟨296729, by rfl⟩ : syracuseStep 395639 = 593459) B593459
theorem B395659 : Blo 393766 395659 := bstep (se 1 (by rfl) ⟨296744, by rfl⟩ : syracuseStep 395659 = 593489) B593489
theorem B395671 : Blo 393766 395671 := bstep (se 1 (by rfl) ⟨296753, by rfl⟩ : syracuseStep 395671 = 593507) B593507
theorem B395691 : Blo 393766 395691 := bstep (se 1 (by rfl) ⟨296768, by rfl⟩ : syracuseStep 395691 = 593537) B593537
theorem B887219 : Blo 393766 887219 := bstep (se 1 (by rfl) ⟨665414, by rfl⟩ : syracuseStep 887219 = 1330829) B1330829
theorem B395703 : Blo 393766 395703 := bstep (se 1 (by rfl) ⟨296777, by rfl⟩ : syracuseStep 395703 = 593555) B593555
theorem B592331 : Blo 393766 592331 := bstep (se 1 (by rfl) ⟨444248, by rfl⟩ : syracuseStep 592331 = 888497) B888497
theorem B395723 : Blo 393766 395723 := bstep (se 1 (by rfl) ⟨296792, by rfl⟩ : syracuseStep 395723 = 593585) B593585
theorem B887255 : Blo 393766 887255 := bstep (se 1 (by rfl) ⟨665441, by rfl⟩ : syracuseStep 887255 = 1330883) B1330883
theorem B592343 : Blo 393766 592343 := bstep (se 1 (by rfl) ⟨444257, by rfl⟩ : syracuseStep 592343 = 888515) B888515
theorem B395735 : Blo 393766 395735 := bstep (se 1 (by rfl) ⟨296801, by rfl⟩ : syracuseStep 395735 = 593603) B593603
theorem B395755 : Blo 393766 395755 := bstep (se 1 (by rfl) ⟨296816, by rfl⟩ : syracuseStep 395755 = 593633) B593633
theorem B395767 : Blo 393766 395767 := bstep (se 1 (by rfl) ⟨296825, by rfl⟩ : syracuseStep 395767 = 593651) B593651
theorem B395787 : Blo 393766 395787 := bstep (se 1 (by rfl) ⟨296840, by rfl⟩ : syracuseStep 395787 = 593681) B593681
theorem B395799 : Blo 393766 395799 := bstep (se 1 (by rfl) ⟨296849, by rfl⟩ : syracuseStep 395799 = 593699) B593699
theorem B1509911 : Blo 393766 1509911 := bstep (se 1 (by rfl) ⟨1132433, by rfl⟩ : syracuseStep 1509911 = 2264867) B2264867
theorem B592409 : Blo 393766 592409 := bstep (se 2 (by rfl) ⟨222153, by rfl⟩ : syracuseStep 592409 = 444307) B444307
theorem B395819 : Blo 393766 395819 := bstep (se 1 (by rfl) ⟨296864, by rfl⟩ : syracuseStep 395819 = 593729) B593729
theorem B395831 : Blo 393766 395831 := bstep (se 1 (by rfl) ⟨296873, by rfl⟩ : syracuseStep 395831 = 593747) B593747
theorem B952897 : Blo 393766 952897 := bstep (se 2 (by rfl) ⟨357336, by rfl⟩ : syracuseStep 952897 = 714673) B714673
theorem B395851 : Blo 393766 395851 := bstep (se 1 (by rfl) ⟨296888, by rfl⟩ : syracuseStep 395851 = 593777) B593777
theorem B395863 : Blo 393766 395863 := bstep (se 1 (by rfl) ⟨296897, by rfl⟩ : syracuseStep 395863 = 593795) B593795
theorem B395883 : Blo 393766 395883 := bstep (se 1 (by rfl) ⟨296912, by rfl⟩ : syracuseStep 395883 = 593825) B593825
theorem B395895 : Blo 393766 395895 := bstep (se 1 (by rfl) ⟨296921, by rfl⟩ : syracuseStep 395895 = 593843) B593843
theorem B887435 : Blo 393766 887435 := bstep (se 1 (by rfl) ⟨665576, by rfl⟩ : syracuseStep 887435 = 1331153) B1331153
theorem B592523 : Blo 393766 592523 := bstep (se 1 (by rfl) ⟨444392, by rfl⟩ : syracuseStep 592523 = 888785) B888785
theorem B395915 : Blo 393766 395915 := bstep (se 1 (by rfl) ⟨296936, by rfl⟩ : syracuseStep 395915 = 593873) B593873
theorem B592535 : Blo 393766 592535 := bstep (se 1 (by rfl) ⟨444401, by rfl⟩ : syracuseStep 592535 = 888803) B888803
theorem B395927 : Blo 393766 395927 := bstep (se 1 (by rfl) ⟨296945, by rfl⟩ : syracuseStep 395927 = 593891) B593891
theorem B395947 : Blo 393766 395947 := bstep (se 1 (by rfl) ⟨296960, by rfl⟩ : syracuseStep 395947 = 593921) B593921
theorem B395959 : Blo 393766 395959 := bstep (se 1 (by rfl) ⟨296969, by rfl⟩ : syracuseStep 395959 = 593939) B593939
theorem B887489 : Blo 393766 887489 := bstep (se 2 (by rfl) ⟨332808, by rfl⟩ : syracuseStep 887489 = 665617) B665617
theorem B395979 : Blo 393766 395979 := bstep (se 1 (by rfl) ⟨296984, by rfl⟩ : syracuseStep 395979 = 593969) B593969
theorem B395991 : Blo 393766 395991 := bstep (se 1 (by rfl) ⟨296993, by rfl⟩ : syracuseStep 395991 = 593987) B593987
theorem B592601 : Blo 393766 592601 := bstep (se 2 (by rfl) ⟨222225, by rfl⟩ : syracuseStep 592601 = 444451) B444451
theorem B1510109 : Blo 393766 1510109 := bstep (se 3 (by rfl) ⟨283145, by rfl⟩ : syracuseStep 1510109 = 566291) B566291
theorem B396011 : Blo 393766 396011 := bstep (se 1 (by rfl) ⟨297008, by rfl⟩ : syracuseStep 396011 = 594017) B594017
theorem B396023 : Blo 393766 396023 := bstep (se 1 (by rfl) ⟨297017, by rfl⟩ : syracuseStep 396023 = 594035) B594035
theorem B396043 : Blo 393766 396043 := bstep (se 1 (by rfl) ⟨297032, by rfl⟩ : syracuseStep 396043 = 594065) B594065
theorem B396055 : Blo 393766 396055 := bstep (se 1 (by rfl) ⟨297041, by rfl⟩ : syracuseStep 396055 = 594083) B594083
theorem B396075 : Blo 393766 396075 := bstep (se 1 (by rfl) ⟨297056, by rfl⟩ : syracuseStep 396075 = 594113) B594113
theorem B7211821 : Blo 393766 7211821 := bstep (se 3 (by rfl) ⟨1352216, by rfl⟩ : syracuseStep 7211821 = 2704433) B2704433
theorem B396087 : Blo 393766 396087 := bstep (se 1 (by rfl) ⟨297065, by rfl⟩ : syracuseStep 396087 = 594131) B594131
theorem B4492097 : Blo 393766 4492097 := bstep (se 2 (by rfl) ⟨1684536, by rfl⟩ : syracuseStep 4492097 = 3369073) B3369073
theorem B592715 : Blo 393766 592715 := bstep (se 1 (by rfl) ⟨444536, by rfl⟩ : syracuseStep 592715 = 889073) B889073
theorem B396107 : Blo 393766 396107 := bstep (se 1 (by rfl) ⟨297080, by rfl⟩ : syracuseStep 396107 = 594161) B594161
theorem B592727 : Blo 393766 592727 := bstep (se 1 (by rfl) ⟨444545, by rfl⟩ : syracuseStep 592727 = 889091) B889091
theorem B396119 : Blo 393766 396119 := bstep (se 1 (by rfl) ⟨297089, by rfl⟩ : syracuseStep 396119 = 594179) B594179
theorem B3017573 : Blo 393766 3017573 := bstep (se 4 (by rfl) ⟨282897, by rfl⟩ : syracuseStep 3017573 = 565795) B565795
theorem B2263909 : Blo 393766 2263909 := bstep (se 4 (by rfl) ⟨212241, by rfl⟩ : syracuseStep 2263909 = 424483) B424483
theorem B396139 : Blo 393766 396139 := bstep (se 1 (by rfl) ⟨297104, by rfl⟩ : syracuseStep 396139 = 594209) B594209
theorem B396151 : Blo 393766 396151 := bstep (se 1 (by rfl) ⟨297113, by rfl⟩ : syracuseStep 396151 = 594227) B594227
theorem B396171 : Blo 393766 396171 := bstep (se 1 (by rfl) ⟨297128, by rfl⟩ : syracuseStep 396171 = 594257) B594257
theorem B396183 : Blo 393766 396183 := bstep (se 1 (by rfl) ⟨297137, by rfl⟩ : syracuseStep 396183 = 594275) B594275
theorem B887705 : Blo 393766 887705 := bstep (se 2 (by rfl) ⟨332889, by rfl⟩ : syracuseStep 887705 = 665779) B665779
theorem B592793 : Blo 393766 592793 := bstep (se 2 (by rfl) ⟨222297, by rfl⟩ : syracuseStep 592793 = 444595) B444595
theorem B396203 : Blo 393766 396203 := bstep (se 1 (by rfl) ⟨297152, by rfl⟩ : syracuseStep 396203 = 594305) B594305
theorem B396215 : Blo 393766 396215 := bstep (se 1 (by rfl) ⟨297161, by rfl⟩ : syracuseStep 396215 = 594323) B594323
theorem B396235 : Blo 393766 396235 := bstep (se 1 (by rfl) ⟨297176, by rfl⟩ : syracuseStep 396235 = 594353) B594353
theorem B396247 : Blo 393766 396247 := bstep (se 1 (by rfl) ⟨297185, by rfl⟩ : syracuseStep 396247 = 594371) B594371
theorem B396267 : Blo 393766 396267 := bstep (se 1 (by rfl) ⟨297200, by rfl⟩ : syracuseStep 396267 = 594401) B594401
theorem B887795 : Blo 393766 887795 := bstep (se 1 (by rfl) ⟨665846, by rfl⟩ : syracuseStep 887795 = 1331693) B1331693
theorem B396279 : Blo 393766 396279 := bstep (se 1 (by rfl) ⟨297209, by rfl⟩ : syracuseStep 396279 = 594419) B594419
theorem B592907 : Blo 393766 592907 := bstep (se 1 (by rfl) ⟨444680, by rfl⟩ : syracuseStep 592907 = 889361) B889361
theorem B396299 : Blo 393766 396299 := bstep (se 1 (by rfl) ⟨297224, by rfl⟩ : syracuseStep 396299 = 594449) B594449
theorem B887831 : Blo 393766 887831 := bstep (se 1 (by rfl) ⟨665873, by rfl⟩ : syracuseStep 887831 = 1331747) B1331747
theorem B592919 : Blo 393766 592919 := bstep (se 1 (by rfl) ⟨444689, by rfl⟩ : syracuseStep 592919 = 889379) B889379
theorem B396311 : Blo 393766 396311 := bstep (se 1 (by rfl) ⟨297233, by rfl⟩ : syracuseStep 396311 = 594467) B594467
theorem B396331 : Blo 393766 396331 := bstep (se 1 (by rfl) ⟨297248, by rfl⟩ : syracuseStep 396331 = 594497) B594497
theorem B396343 : Blo 393766 396343 := bstep (se 1 (by rfl) ⟨297257, by rfl⟩ : syracuseStep 396343 = 594515) B594515
theorem B2001995 : Blo 393766 2001995 := bstep (se 1 (by rfl) ⟨1501496, by rfl⟩ : syracuseStep 2001995 = 3002993) B3002993
theorem B396363 : Blo 393766 396363 := bstep (se 1 (by rfl) ⟨297272, by rfl⟩ : syracuseStep 396363 = 594545) B594545
theorem B396375 : Blo 393766 396375 := bstep (se 1 (by rfl) ⟨297281, by rfl⟩ : syracuseStep 396375 = 594563) B594563
theorem B592985 : Blo 393766 592985 := bstep (se 2 (by rfl) ⟨222369, by rfl⟩ : syracuseStep 592985 = 444739) B444739
theorem B396395 : Blo 393766 396395 := bstep (se 1 (by rfl) ⟨297296, by rfl⟩ : syracuseStep 396395 = 594593) B594593
theorem B396407 : Blo 393766 396407 := bstep (se 1 (by rfl) ⟨297305, by rfl⟩ : syracuseStep 396407 = 594611) B594611
theorem B396427 : Blo 393766 396427 := bstep (se 1 (by rfl) ⟨297320, by rfl⟩ : syracuseStep 396427 = 594641) B594641
theorem B396439 : Blo 393766 396439 := bstep (se 1 (by rfl) ⟨297329, by rfl⟩ : syracuseStep 396439 = 594659) B594659
theorem B396459 : Blo 393766 396459 := bstep (se 1 (by rfl) ⟨297344, by rfl⟩ : syracuseStep 396459 = 594689) B594689
theorem B396471 : Blo 393766 396471 := bstep (se 1 (by rfl) ⟨297353, by rfl⟩ : syracuseStep 396471 = 594707) B594707
theorem B888011 : Blo 393766 888011 := bstep (se 1 (by rfl) ⟨666008, by rfl⟩ : syracuseStep 888011 = 1332017) B1332017
theorem B593099 : Blo 393766 593099 := bstep (se 1 (by rfl) ⟨444824, by rfl⟩ : syracuseStep 593099 = 889649) B889649
theorem B396491 : Blo 393766 396491 := bstep (se 1 (by rfl) ⟨297368, by rfl⟩ : syracuseStep 396491 = 594737) B594737
theorem B593111 : Blo 393766 593111 := bstep (se 1 (by rfl) ⟨444833, by rfl⟩ : syracuseStep 593111 = 889667) B889667
theorem B396503 : Blo 393766 396503 := bstep (se 1 (by rfl) ⟨297377, by rfl⟩ : syracuseStep 396503 = 594755) B594755
theorem B396523 : Blo 393766 396523 := bstep (se 1 (by rfl) ⟨297392, by rfl⟩ : syracuseStep 396523 = 594785) B594785
theorem B396535 : Blo 393766 396535 := bstep (se 1 (by rfl) ⟨297401, by rfl⟩ : syracuseStep 396535 = 594803) B594803
theorem B888065 : Blo 393766 888065 := bstep (se 2 (by rfl) ⟨333024, by rfl⟩ : syracuseStep 888065 = 666049) B666049
theorem B396555 : Blo 393766 396555 := bstep (se 1 (by rfl) ⟨297416, by rfl⟩ : syracuseStep 396555 = 594833) B594833
theorem B396567 : Blo 393766 396567 := bstep (se 1 (by rfl) ⟨297425, by rfl⟩ : syracuseStep 396567 = 594851) B594851
theorem B593177 : Blo 393766 593177 := bstep (se 2 (by rfl) ⟨222441, by rfl⟩ : syracuseStep 593177 = 444883) B444883
theorem B396587 : Blo 393766 396587 := bstep (se 1 (by rfl) ⟨297440, by rfl⟩ : syracuseStep 396587 = 594881) B594881
theorem B396599 : Blo 393766 396599 := bstep (se 1 (by rfl) ⟨297449, by rfl⟩ : syracuseStep 396599 = 594899) B594899
theorem B396619 : Blo 393766 396619 := bstep (se 1 (by rfl) ⟨297464, by rfl⟩ : syracuseStep 396619 = 594929) B594929
theorem B3018059 : Blo 393766 3018059 := bstep (se 1 (by rfl) ⟨2263544, by rfl⟩ : syracuseStep 3018059 = 4527089) B4527089
theorem B396631 : Blo 393766 396631 := bstep (se 1 (by rfl) ⟨297473, by rfl⟩ : syracuseStep 396631 = 594947) B594947
theorem B396651 : Blo 393766 396651 := bstep (se 1 (by rfl) ⟨297488, by rfl⟩ : syracuseStep 396651 = 594977) B594977
theorem B396663 : Blo 393766 396663 := bstep (se 1 (by rfl) ⟨297497, by rfl⟩ : syracuseStep 396663 = 594995) B594995
theorem B593291 : Blo 393766 593291 := bstep (se 1 (by rfl) ⟨444968, by rfl⟩ : syracuseStep 593291 = 889937) B889937
theorem B396683 : Blo 393766 396683 := bstep (se 1 (by rfl) ⟨297512, by rfl⟩ : syracuseStep 396683 = 595025) B595025
theorem B593303 : Blo 393766 593303 := bstep (se 1 (by rfl) ⟨444977, by rfl⟩ : syracuseStep 593303 = 889955) B889955
theorem B1904023 : Blo 393766 1904023 := bstep (se 1 (by rfl) ⟨1428017, by rfl⟩ : syracuseStep 1904023 = 2856035) B2856035
theorem B396695 : Blo 393766 396695 := bstep (se 1 (by rfl) ⟨297521, by rfl⟩ : syracuseStep 396695 = 595043) B595043
theorem B396715 : Blo 393766 396715 := bstep (se 1 (by rfl) ⟨297536, by rfl⟩ : syracuseStep 396715 = 595073) B595073
theorem B396727 : Blo 393766 396727 := bstep (se 1 (by rfl) ⟨297545, by rfl⟩ : syracuseStep 396727 = 595091) B595091
theorem B396747 : Blo 393766 396747 := bstep (se 1 (by rfl) ⟨297560, by rfl⟩ : syracuseStep 396747 = 595121) B595121
theorem B1510859 : Blo 393766 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B396759 : Blo 393766 396759 := bstep (se 1 (by rfl) ⟨297569, by rfl⟩ : syracuseStep 396759 = 595139) B595139
theorem B888281 : Blo 393766 888281 := bstep (se 2 (by rfl) ⟨333105, by rfl⟩ : syracuseStep 888281 = 666211) B666211
theorem B593369 : Blo 393766 593369 := bstep (se 2 (by rfl) ⟨222513, by rfl⟩ : syracuseStep 593369 = 445027) B445027
theorem B396779 : Blo 393766 396779 := bstep (se 1 (by rfl) ⟨297584, by rfl⟩ : syracuseStep 396779 = 595169) B595169
theorem B396791 : Blo 393766 396791 := bstep (se 1 (by rfl) ⟨297593, by rfl⟩ : syracuseStep 396791 = 595187) B595187
theorem B396811 : Blo 393766 396811 := bstep (se 1 (by rfl) ⟨297608, by rfl⟩ : syracuseStep 396811 = 595217) B595217
theorem B1740305 : Blo 393766 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B396823 : Blo 393766 396823 := bstep (se 1 (by rfl) ⟨297617, by rfl⟩ : syracuseStep 396823 = 595235) B595235
theorem B396843 : Blo 393766 396843 := bstep (se 1 (by rfl) ⟨297632, by rfl⟩ : syracuseStep 396843 = 595265) B595265
theorem B888371 : Blo 393766 888371 := bstep (se 1 (by rfl) ⟨666278, by rfl⟩ : syracuseStep 888371 = 1332557) B1332557
theorem B396855 : Blo 393766 396855 := bstep (se 1 (by rfl) ⟨297641, by rfl⟩ : syracuseStep 396855 = 595283) B595283
theorem B593483 : Blo 393766 593483 := bstep (se 1 (by rfl) ⟨445112, by rfl⟩ : syracuseStep 593483 = 890225) B890225
theorem B396875 : Blo 393766 396875 := bstep (se 1 (by rfl) ⟨297656, by rfl⟩ : syracuseStep 396875 = 595313) B595313
theorem B888407 : Blo 393766 888407 := bstep (se 1 (by rfl) ⟨666305, by rfl⟩ : syracuseStep 888407 = 1332611) B1332611
theorem B593495 : Blo 393766 593495 := bstep (se 1 (by rfl) ⟨445121, by rfl⟩ : syracuseStep 593495 = 890243) B890243
theorem B396887 : Blo 393766 396887 := bstep (se 1 (by rfl) ⟨297665, by rfl⟩ : syracuseStep 396887 = 595331) B595331
theorem B396907 : Blo 393766 396907 := bstep (se 1 (by rfl) ⟨297680, by rfl⟩ : syracuseStep 396907 = 595361) B595361
theorem B396919 : Blo 393766 396919 := bstep (se 1 (by rfl) ⟨297689, by rfl⟩ : syracuseStep 396919 = 595379) B595379
theorem B396939 : Blo 393766 396939 := bstep (se 1 (by rfl) ⟨297704, by rfl⟩ : syracuseStep 396939 = 595409) B595409
theorem B396951 : Blo 393766 396951 := bstep (se 1 (by rfl) ⟨297713, by rfl⟩ : syracuseStep 396951 = 595427) B595427
theorem B593561 : Blo 393766 593561 := bstep (se 2 (by rfl) ⟨222585, by rfl⟩ : syracuseStep 593561 = 445171) B445171
theorem B396971 : Blo 393766 396971 := bstep (se 1 (by rfl) ⟨297728, by rfl⟩ : syracuseStep 396971 = 595457) B595457
theorem B396983 : Blo 393766 396983 := bstep (se 1 (by rfl) ⟨297737, by rfl⟩ : syracuseStep 396983 = 595475) B595475
theorem B397003 : Blo 393766 397003 := bstep (se 1 (by rfl) ⟨297752, by rfl⟩ : syracuseStep 397003 = 595505) B595505
theorem B397015 : Blo 393766 397015 := bstep (se 1 (by rfl) ⟨297761, by rfl⟩ : syracuseStep 397015 = 595523) B595523
theorem B397035 : Blo 393766 397035 := bstep (se 1 (by rfl) ⟨297776, by rfl⟩ : syracuseStep 397035 = 595553) B595553
theorem B397047 : Blo 393766 397047 := bstep (se 1 (by rfl) ⟨297785, by rfl⟩ : syracuseStep 397047 = 595571) B595571
theorem B888587 : Blo 393766 888587 := bstep (se 1 (by rfl) ⟨666440, by rfl⟩ : syracuseStep 888587 = 1332881) B1332881
theorem B593675 : Blo 393766 593675 := bstep (se 1 (by rfl) ⟨445256, by rfl⟩ : syracuseStep 593675 = 890513) B890513
theorem B397067 : Blo 393766 397067 := bstep (se 1 (by rfl) ⟨297800, by rfl⟩ : syracuseStep 397067 = 595601) B595601
theorem B593687 : Blo 393766 593687 := bstep (se 1 (by rfl) ⟨445265, by rfl⟩ : syracuseStep 593687 = 890531) B890531
theorem B397079 : Blo 393766 397079 := bstep (se 1 (by rfl) ⟨297809, by rfl⟩ : syracuseStep 397079 = 595619) B595619
theorem B397099 : Blo 393766 397099 := bstep (se 1 (by rfl) ⟨297824, by rfl⟩ : syracuseStep 397099 = 595649) B595649
theorem B397111 : Blo 393766 397111 := bstep (se 1 (by rfl) ⟨297833, by rfl⟩ : syracuseStep 397111 = 595667) B595667
theorem B888641 : Blo 393766 888641 := bstep (se 2 (by rfl) ⟨333240, by rfl⟩ : syracuseStep 888641 = 666481) B666481
theorem B397131 : Blo 393766 397131 := bstep (se 1 (by rfl) ⟨297848, by rfl⟩ : syracuseStep 397131 = 595697) B595697
theorem B397143 : Blo 393766 397143 := bstep (se 1 (by rfl) ⟨297857, by rfl⟩ : syracuseStep 397143 = 595715) B595715
theorem B593753 : Blo 393766 593753 := bstep (se 2 (by rfl) ⟨222657, by rfl⟩ : syracuseStep 593753 = 445315) B445315
theorem B397163 : Blo 393766 397163 := bstep (se 1 (by rfl) ⟨297872, by rfl⟩ : syracuseStep 397163 = 595745) B595745
theorem B397175 : Blo 393766 397175 := bstep (se 1 (by rfl) ⟨297881, by rfl⟩ : syracuseStep 397175 = 595763) B595763
theorem B397195 : Blo 393766 397195 := bstep (se 1 (by rfl) ⟨297896, by rfl⟩ : syracuseStep 397195 = 595793) B595793
theorem B397207 : Blo 393766 397207 := bstep (se 1 (by rfl) ⟨297905, by rfl⟩ : syracuseStep 397207 = 595811) B595811
theorem B397227 : Blo 393766 397227 := bstep (se 1 (by rfl) ⟨297920, by rfl⟩ : syracuseStep 397227 = 595841) B595841
theorem B397239 : Blo 393766 397239 := bstep (se 1 (by rfl) ⟨297929, by rfl⟩ : syracuseStep 397239 = 595859) B595859
theorem B593867 : Blo 393766 593867 := bstep (se 1 (by rfl) ⟨445400, by rfl⟩ : syracuseStep 593867 = 890801) B890801
theorem B397259 : Blo 393766 397259 := bstep (se 1 (by rfl) ⟨297944, by rfl⟩ : syracuseStep 397259 = 595889) B595889
theorem B593879 : Blo 393766 593879 := bstep (se 1 (by rfl) ⟨445409, by rfl⟩ : syracuseStep 593879 = 890819) B890819
theorem B397271 : Blo 393766 397271 := bstep (se 1 (by rfl) ⟨297953, by rfl⟩ : syracuseStep 397271 = 595907) B595907
theorem B397291 : Blo 393766 397291 := bstep (se 1 (by rfl) ⟨297968, by rfl⟩ : syracuseStep 397291 = 595937) B595937
theorem B397303 : Blo 393766 397303 := bstep (se 1 (by rfl) ⟨297977, by rfl⟩ : syracuseStep 397303 = 595955) B595955
theorem B397323 : Blo 393766 397323 := bstep (se 1 (by rfl) ⟨297992, by rfl⟩ : syracuseStep 397323 = 595985) B595985
theorem B888857 : Blo 393766 888857 := bstep (se 2 (by rfl) ⟨333321, by rfl⟩ : syracuseStep 888857 = 666643) B666643
theorem B593945 : Blo 393766 593945 := bstep (se 2 (by rfl) ⟨222729, by rfl⟩ : syracuseStep 593945 = 445459) B445459
theorem B397335 : Blo 393766 397335 := bstep (se 1 (by rfl) ⟨298001, by rfl⟩ : syracuseStep 397335 = 596003) B596003
theorem B397355 : Blo 393766 397355 := bstep (se 1 (by rfl) ⟨298016, by rfl⟩ : syracuseStep 397355 = 596033) B596033
theorem B397367 : Blo 393766 397367 := bstep (se 1 (by rfl) ⟨298025, by rfl⟩ : syracuseStep 397367 = 596051) B596051
theorem B397387 : Blo 393766 397387 := bstep (se 1 (by rfl) ⟨298040, by rfl⟩ : syracuseStep 397387 = 596081) B596081
theorem B397399 : Blo 393766 397399 := bstep (se 1 (by rfl) ⟨298049, by rfl⟩ : syracuseStep 397399 = 596099) B596099
theorem B397419 : Blo 393766 397419 := bstep (se 1 (by rfl) ⟨298064, by rfl⟩ : syracuseStep 397419 = 596129) B596129
theorem B888947 : Blo 393766 888947 := bstep (se 1 (by rfl) ⟨666710, by rfl⟩ : syracuseStep 888947 = 1333421) B1333421
theorem B397431 : Blo 393766 397431 := bstep (se 1 (by rfl) ⟨298073, by rfl⟩ : syracuseStep 397431 = 596147) B596147
theorem B594059 : Blo 393766 594059 := bstep (se 1 (by rfl) ⟨445544, by rfl⟩ : syracuseStep 594059 = 891089) B891089
theorem B397451 : Blo 393766 397451 := bstep (se 1 (by rfl) ⟨298088, by rfl⟩ : syracuseStep 397451 = 596177) B596177
theorem B888983 : Blo 393766 888983 := bstep (se 1 (by rfl) ⟨666737, by rfl⟩ : syracuseStep 888983 = 1333475) B1333475
theorem B594071 : Blo 393766 594071 := bstep (se 1 (by rfl) ⟨445553, by rfl⟩ : syracuseStep 594071 = 891107) B891107
theorem B397463 : Blo 393766 397463 := bstep (se 1 (by rfl) ⟨298097, by rfl⟩ : syracuseStep 397463 = 596195) B596195
theorem B397483 : Blo 393766 397483 := bstep (se 1 (by rfl) ⟨298112, by rfl⟩ : syracuseStep 397483 = 596225) B596225
theorem B397495 : Blo 393766 397495 := bstep (se 1 (by rfl) ⟨298121, by rfl⟩ : syracuseStep 397495 = 596243) B596243
theorem B397515 : Blo 393766 397515 := bstep (se 1 (by rfl) ⟨298136, by rfl⟩ : syracuseStep 397515 = 596273) B596273
theorem B397527 : Blo 393766 397527 := bstep (se 1 (by rfl) ⟨298145, by rfl⟩ : syracuseStep 397527 = 596291) B596291
theorem B594137 : Blo 393766 594137 := bstep (se 2 (by rfl) ⟨222801, by rfl⟩ : syracuseStep 594137 = 445603) B445603
theorem B397547 : Blo 393766 397547 := bstep (se 1 (by rfl) ⟨298160, by rfl⟩ : syracuseStep 397547 = 596321) B596321
theorem B397559 : Blo 393766 397559 := bstep (se 1 (by rfl) ⟨298169, by rfl⟩ : syracuseStep 397559 = 596339) B596339
theorem B397579 : Blo 393766 397579 := bstep (se 1 (by rfl) ⟨298184, by rfl⟩ : syracuseStep 397579 = 596369) B596369
theorem B397591 : Blo 393766 397591 := bstep (se 1 (by rfl) ⟨298193, by rfl⟩ : syracuseStep 397591 = 596387) B596387
theorem B561433 : Blo 393766 561433 := bstep (se 2 (by rfl) ⟨210537, by rfl⟩ : syracuseStep 561433 = 421075) B421075
theorem B397611 : Blo 393766 397611 := bstep (se 1 (by rfl) ⟨298208, by rfl⟩ : syracuseStep 397611 = 596417) B596417
theorem B397623 : Blo 393766 397623 := bstep (se 1 (by rfl) ⟨298217, by rfl⟩ : syracuseStep 397623 = 596435) B596435
theorem B889163 : Blo 393766 889163 := bstep (se 1 (by rfl) ⟨666872, by rfl⟩ : syracuseStep 889163 = 1333745) B1333745
theorem B594251 : Blo 393766 594251 := bstep (se 1 (by rfl) ⟨445688, by rfl⟩ : syracuseStep 594251 = 891377) B891377
theorem B397643 : Blo 393766 397643 := bstep (se 1 (by rfl) ⟨298232, by rfl⟩ : syracuseStep 397643 = 596465) B596465
theorem B594263 : Blo 393766 594263 := bstep (se 1 (by rfl) ⟨445697, by rfl⟩ : syracuseStep 594263 = 891395) B891395
theorem B397655 : Blo 393766 397655 := bstep (se 1 (by rfl) ⟨298241, by rfl⟩ : syracuseStep 397655 = 596483) B596483
theorem B397675 : Blo 393766 397675 := bstep (se 1 (by rfl) ⟨298256, by rfl⟩ : syracuseStep 397675 = 596513) B596513
theorem B397687 : Blo 393766 397687 := bstep (se 1 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 397687 = 596531) B596531
theorem B889217 : Blo 393766 889217 := bstep (se 2 (by rfl) ⟨333456, by rfl⟩ : syracuseStep 889217 = 666913) B666913
theorem B758155 : Blo 393766 758155 := bstep (se 1 (by rfl) ⟨568616, by rfl⟩ : syracuseStep 758155 = 1137233) B1137233
theorem B397707 : Blo 393766 397707 := bstep (se 1 (by rfl) ⟨298280, by rfl⟩ : syracuseStep 397707 = 596561) B596561
theorem B397719 : Blo 393766 397719 := bstep (se 1 (by rfl) ⟨298289, by rfl⟩ : syracuseStep 397719 = 596579) B596579
theorem B594329 : Blo 393766 594329 := bstep (se 2 (by rfl) ⟨222873, by rfl⟩ : syracuseStep 594329 = 445747) B445747
theorem B397739 : Blo 393766 397739 := bstep (se 1 (by rfl) ⟨298304, by rfl⟩ : syracuseStep 397739 = 596609) B596609
theorem B397751 : Blo 393766 397751 := bstep (se 1 (by rfl) ⟨298313, by rfl⟩ : syracuseStep 397751 = 596627) B596627
theorem B594443 : Blo 393766 594443 := bstep (se 1 (by rfl) ⟨445832, by rfl⟩ : syracuseStep 594443 = 891665) B891665
theorem B594455 : Blo 393766 594455 := bstep (se 1 (by rfl) ⟨445841, by rfl⟩ : syracuseStep 594455 = 891683) B891683
theorem B889433 : Blo 393766 889433 := bstep (se 2 (by rfl) ⟨333537, by rfl⟩ : syracuseStep 889433 = 667075) B667075
theorem B594521 : Blo 393766 594521 := bstep (se 2 (by rfl) ⟨222945, by rfl⟩ : syracuseStep 594521 = 445891) B445891
theorem B3379805 : Blo 393766 3379805 := bstep (se 3 (by rfl) ⟨633713, by rfl⟩ : syracuseStep 3379805 = 1267427) B1267427
theorem B889523 : Blo 393766 889523 := bstep (se 1 (by rfl) ⟨667142, by rfl⟩ : syracuseStep 889523 = 1334285) B1334285
theorem B594635 : Blo 393766 594635 := bstep (se 1 (by rfl) ⟨445976, by rfl⟩ : syracuseStep 594635 = 891953) B891953
theorem B889559 : Blo 393766 889559 := bstep (se 1 (by rfl) ⟨667169, by rfl⟩ : syracuseStep 889559 = 1334339) B1334339
theorem B594647 : Blo 393766 594647 := bstep (se 1 (by rfl) ⟨445985, by rfl⟩ : syracuseStep 594647 = 891971) B891971
theorem B594713 : Blo 393766 594713 := bstep (se 2 (by rfl) ⟨223017, by rfl⟩ : syracuseStep 594713 = 446035) B446035
theorem B2003777 : Blo 393766 2003777 := bstep (se 2 (by rfl) ⟨751416, by rfl⟩ : syracuseStep 2003777 = 1502833) B1502833
theorem B889739 : Blo 393766 889739 := bstep (se 1 (by rfl) ⟨667304, by rfl⟩ : syracuseStep 889739 = 1334609) B1334609
theorem B594827 : Blo 393766 594827 := bstep (se 1 (by rfl) ⟨446120, by rfl⟩ : syracuseStep 594827 = 892241) B892241
theorem B594839 : Blo 393766 594839 := bstep (se 1 (by rfl) ⟨446129, by rfl⟩ : syracuseStep 594839 = 892259) B892259
theorem B889793 : Blo 393766 889793 := bstep (se 2 (by rfl) ⟨333672, by rfl⟩ : syracuseStep 889793 = 667345) B667345
theorem B594905 : Blo 393766 594905 := bstep (se 2 (by rfl) ⟨223089, by rfl⟩ : syracuseStep 594905 = 446179) B446179
theorem B955415 : Blo 393766 955415 := bstep (se 1 (by rfl) ⟨716561, by rfl⟩ : syracuseStep 955415 = 1433123) B1433123
theorem B595019 : Blo 393766 595019 := bstep (se 1 (by rfl) ⟨446264, by rfl⟩ : syracuseStep 595019 = 892529) B892529
theorem B595031 : Blo 393766 595031 := bstep (se 1 (by rfl) ⟨446273, by rfl⟩ : syracuseStep 595031 = 892547) B892547
theorem B890009 : Blo 393766 890009 := bstep (se 2 (by rfl) ⟨333753, by rfl⟩ : syracuseStep 890009 = 667507) B667507
theorem B595097 : Blo 393766 595097 := bstep (se 2 (by rfl) ⟨223161, by rfl⟩ : syracuseStep 595097 = 446323) B446323
theorem B890099 : Blo 393766 890099 := bstep (se 1 (by rfl) ⟨667574, by rfl⟩ : syracuseStep 890099 = 1335149) B1335149
theorem B595211 : Blo 393766 595211 := bstep (se 1 (by rfl) ⟨446408, by rfl⟩ : syracuseStep 595211 = 892817) B892817
theorem B890135 : Blo 393766 890135 := bstep (se 1 (by rfl) ⟨667601, by rfl⟩ : syracuseStep 890135 = 1335203) B1335203
theorem B595223 : Blo 393766 595223 := bstep (se 1 (by rfl) ⟨446417, by rfl⟩ : syracuseStep 595223 = 892835) B892835
theorem B3380555 : Blo 393766 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B595289 : Blo 393766 595289 := bstep (se 2 (by rfl) ⟨223233, by rfl⟩ : syracuseStep 595289 = 446467) B446467
theorem B4560229 : Blo 393766 4560229 := bstep (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) B855043
theorem B562583 : Blo 393766 562583 := bstep (se 1 (by rfl) ⟨421937, by rfl⟩ : syracuseStep 562583 = 843875) B843875
theorem B890315 : Blo 393766 890315 := bstep (se 1 (by rfl) ⟨667736, by rfl⟩ : syracuseStep 890315 = 1335473) B1335473
theorem B595403 : Blo 393766 595403 := bstep (se 1 (by rfl) ⟨446552, by rfl⟩ : syracuseStep 595403 = 893105) B893105
theorem B48534997 : Blo 393766 48534997 := bstep (se 7 (by rfl) ⟨568769, by rfl⟩ : syracuseStep 48534997 = 1137539) B1137539
theorem B595415 : Blo 393766 595415 := bstep (se 1 (by rfl) ⟨446561, by rfl⟩ : syracuseStep 595415 = 893123) B893123
theorem B890369 : Blo 393766 890369 := bstep (se 2 (by rfl) ⟨333888, by rfl⟩ : syracuseStep 890369 = 667777) B667777
theorem B595481 : Blo 393766 595481 := bstep (se 2 (by rfl) ⟨223305, by rfl⟩ : syracuseStep 595481 = 446611) B446611
theorem B595595 : Blo 393766 595595 := bstep (se 1 (by rfl) ⟨446696, by rfl⟩ : syracuseStep 595595 = 893393) B893393
theorem B595607 : Blo 393766 595607 := bstep (se 1 (by rfl) ⟨446705, by rfl⟩ : syracuseStep 595607 = 893411) B893411
theorem B562891 : Blo 393766 562891 := bstep (se 1 (by rfl) ⟨422168, by rfl⟩ : syracuseStep 562891 = 844337) B844337
theorem B890585 : Blo 393766 890585 := bstep (se 2 (by rfl) ⟨333969, by rfl⟩ : syracuseStep 890585 = 667939) B667939
theorem B595673 : Blo 393766 595673 := bstep (se 2 (by rfl) ⟨223377, by rfl⟩ : syracuseStep 595673 = 446755) B446755
theorem B2037521 : Blo 393766 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B890675 : Blo 393766 890675 := bstep (se 1 (by rfl) ⟨668006, by rfl⟩ : syracuseStep 890675 = 1336013) B1336013
theorem B6854465 : Blo 393766 6854465 := bstep (se 2 (by rfl) ⟨2570424, by rfl⟩ : syracuseStep 6854465 = 5140849) B5140849
theorem B595787 : Blo 393766 595787 := bstep (se 1 (by rfl) ⟨446840, by rfl⟩ : syracuseStep 595787 = 893681) B893681
theorem B890711 : Blo 393766 890711 := bstep (se 1 (by rfl) ⟨668033, by rfl⟩ : syracuseStep 890711 = 1336067) B1336067
theorem B595799 : Blo 393766 595799 := bstep (se 1 (by rfl) ⟨446849, by rfl⟩ : syracuseStep 595799 = 893699) B893699
theorem B595865 : Blo 393766 595865 := bstep (se 2 (by rfl) ⟨223449, by rfl⟩ : syracuseStep 595865 = 446899) B446899
theorem B890891 : Blo 393766 890891 := bstep (se 1 (by rfl) ⟨668168, by rfl⟩ : syracuseStep 890891 = 1336337) B1336337
theorem B595979 : Blo 393766 595979 := bstep (se 1 (by rfl) ⟨446984, by rfl⟩ : syracuseStep 595979 = 893969) B893969
theorem B595991 : Blo 393766 595991 := bstep (se 1 (by rfl) ⟨446993, by rfl⟩ : syracuseStep 595991 = 893987) B893987
theorem B890945 : Blo 393766 890945 := bstep (se 2 (by rfl) ⟨334104, by rfl⟩ : syracuseStep 890945 = 668209) B668209
theorem B596057 : Blo 393766 596057 := bstep (se 2 (by rfl) ⟨223521, by rfl⟩ : syracuseStep 596057 = 447043) B447043
theorem B596171 : Blo 393766 596171 := bstep (se 1 (by rfl) ⟨447128, by rfl⟩ : syracuseStep 596171 = 894257) B894257
theorem B596183 : Blo 393766 596183 := bstep (se 1 (by rfl) ⟨447137, by rfl⟩ : syracuseStep 596183 = 894275) B894275
theorem B891161 : Blo 393766 891161 := bstep (se 2 (by rfl) ⟨334185, by rfl⟩ : syracuseStep 891161 = 668371) B668371
theorem B596249 : Blo 393766 596249 := bstep (se 2 (by rfl) ⟨223593, by rfl⟩ : syracuseStep 596249 = 447187) B447187
theorem B2136365 : Blo 393766 2136365 := bstep (se 3 (by rfl) ⟨400568, by rfl⟩ : syracuseStep 2136365 = 801137) B801137
theorem B891251 : Blo 393766 891251 := bstep (se 1 (by rfl) ⟨668438, by rfl⟩ : syracuseStep 891251 = 1336877) B1336877
theorem B596363 : Blo 393766 596363 := bstep (se 1 (by rfl) ⟨447272, by rfl⟩ : syracuseStep 596363 = 894545) B894545
theorem B891287 : Blo 393766 891287 := bstep (se 1 (by rfl) ⟨668465, by rfl⟩ : syracuseStep 891287 = 1336931) B1336931
theorem B596375 : Blo 393766 596375 := bstep (se 1 (by rfl) ⟨447281, by rfl⟩ : syracuseStep 596375 = 894563) B894563
theorem B596441 : Blo 393766 596441 := bstep (se 2 (by rfl) ⟨223665, by rfl⟩ : syracuseStep 596441 = 447331) B447331
theorem B891467 : Blo 393766 891467 := bstep (se 1 (by rfl) ⟨668600, by rfl⟩ : syracuseStep 891467 = 1337201) B1337201
theorem B596555 : Blo 393766 596555 := bstep (se 1 (by rfl) ⟨447416, by rfl⟩ : syracuseStep 596555 = 894833) B894833
theorem B596567 : Blo 393766 596567 := bstep (se 1 (by rfl) ⟨447425, by rfl⟩ : syracuseStep 596567 = 894851) B894851
theorem B891521 : Blo 393766 891521 := bstep (se 2 (by rfl) ⟨334320, by rfl⟩ : syracuseStep 891521 = 668641) B668641
theorem B596633 : Blo 393766 596633 := bstep (se 2 (by rfl) ⟨223737, by rfl⟩ : syracuseStep 596633 = 447475) B447475
theorem B563927 : Blo 393766 563927 := bstep (se 1 (by rfl) ⟨422945, by rfl⟩ : syracuseStep 563927 = 845891) B845891
theorem B2005721 : Blo 393766 2005721 := bstep (se 2 (by rfl) ⟨752145, by rfl⟩ : syracuseStep 2005721 = 1504291) B1504291
theorem B3873581 : Blo 393766 3873581 := bstep (se 3 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 3873581 = 1452593) B1452593
theorem B1612619 : Blo 393766 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B891737 : Blo 393766 891737 := bstep (se 2 (by rfl) ⟨334401, by rfl⟩ : syracuseStep 891737 = 668803) B668803
theorem B564121 : Blo 393766 564121 := bstep (se 2 (by rfl) ⟨211545, by rfl⟩ : syracuseStep 564121 = 423091) B423091
theorem B3382195 : Blo 393766 3382195 := bstep (se 1 (by rfl) ⟨2536646, by rfl⟩ : syracuseStep 3382195 = 5073293) B5073293
theorem B891827 : Blo 393766 891827 := bstep (se 1 (by rfl) ⟨668870, by rfl⟩ : syracuseStep 891827 = 1337741) B1337741
theorem B891863 : Blo 393766 891863 := bstep (se 1 (by rfl) ⟨668897, by rfl⟩ : syracuseStep 891863 = 1337795) B1337795
theorem B3054685 : Blo 393766 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B892043 : Blo 393766 892043 := bstep (se 1 (by rfl) ⟨669032, by rfl⟩ : syracuseStep 892043 = 1338065) B1338065
theorem B892097 : Blo 393766 892097 := bstep (se 2 (by rfl) ⟨334536, by rfl⟩ : syracuseStep 892097 = 669073) B669073
theorem B498955 : Blo 393766 498955 := bstep (se 1 (by rfl) ⟨374216, by rfl⟩ : syracuseStep 498955 = 748433) B748433
theorem B2858341 : Blo 393766 2858341 := bstep (se 4 (by rfl) ⟨267969, by rfl⟩ : syracuseStep 2858341 = 535939) B535939
theorem B892313 : Blo 393766 892313 := bstep (se 2 (by rfl) ⟨334617, by rfl⟩ : syracuseStep 892313 = 669235) B669235
theorem B892403 : Blo 393766 892403 := bstep (se 1 (by rfl) ⟨669302, by rfl⟩ : syracuseStep 892403 = 1338605) B1338605
theorem B499223 : Blo 393766 499223 := bstep (se 1 (by rfl) ⟨374417, by rfl⟩ : syracuseStep 499223 = 748835) B748835
theorem B892439 : Blo 393766 892439 := bstep (se 1 (by rfl) ⟨669329, by rfl⟩ : syracuseStep 892439 = 1338659) B1338659
theorem B892619 : Blo 393766 892619 := bstep (se 1 (by rfl) ⟨669464, by rfl⟩ : syracuseStep 892619 = 1338929) B1338929
theorem B892673 : Blo 393766 892673 := bstep (se 2 (by rfl) ⟨334752, by rfl⟩ : syracuseStep 892673 = 669505) B669505
theorem B1449731 : Blo 393766 1449731 := bstep (se 1 (by rfl) ⟨1087298, by rfl⟩ : syracuseStep 1449731 = 2174597) B2174597
theorem B859927 : Blo 393766 859927 := bstep (se 1 (by rfl) ⟨644945, by rfl⟩ : syracuseStep 859927 = 1289891) B1289891
theorem B1122113 : Blo 393766 1122113 := bstep (se 2 (by rfl) ⟨420792, by rfl⟩ : syracuseStep 1122113 = 841585) B841585
theorem B1122137 : Blo 393766 1122137 := bstep (se 2 (by rfl) ⟨420801, by rfl⟩ : syracuseStep 1122137 = 841603) B841603
theorem B6397795 : Blo 393766 6397795 := bstep (se 1 (by rfl) ⟨4798346, by rfl⟩ : syracuseStep 6397795 = 9596693) B9596693
theorem B892889 : Blo 393766 892889 := bstep (se 2 (by rfl) ⟨334833, by rfl⟩ : syracuseStep 892889 = 669667) B669667
theorem B892979 : Blo 393766 892979 := bstep (se 1 (by rfl) ⟨669734, by rfl⟩ : syracuseStep 892979 = 1339469) B1339469
theorem B893015 : Blo 393766 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B499927 : Blo 393766 499927 := bstep (se 1 (by rfl) ⟨374945, by rfl⟩ : syracuseStep 499927 = 749891) B749891
theorem B893195 : Blo 393766 893195 := bstep (se 1 (by rfl) ⟨669896, by rfl⟩ : syracuseStep 893195 = 1339793) B1339793
theorem B2007341 : Blo 393766 2007341 := bstep (se 3 (by rfl) ⟨376376, by rfl⟩ : syracuseStep 2007341 = 752753) B752753
theorem B893249 : Blo 393766 893249 := bstep (se 2 (by rfl) ⟨334968, by rfl⟩ : syracuseStep 893249 = 669937) B669937
theorem B565579 : Blo 393766 565579 := bstep (se 1 (by rfl) ⟨424184, by rfl⟩ : syracuseStep 565579 = 848369) B848369
theorem B532825 : Blo 393766 532825 := bstep (se 2 (by rfl) ⟨199809, by rfl⟩ : syracuseStep 532825 = 399619) B399619
theorem B2695517 : Blo 393766 2695517 := bstep (se 3 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 2695517 = 1010819) B1010819
theorem B893465 : Blo 393766 893465 := bstep (se 2 (by rfl) ⟨335049, by rfl⟩ : syracuseStep 893465 = 670099) B670099
theorem B893555 : Blo 393766 893555 := bstep (se 1 (by rfl) ⟨670166, by rfl⟩ : syracuseStep 893555 = 1340333) B1340333
theorem B893591 : Blo 393766 893591 := bstep (se 1 (by rfl) ⟨670193, by rfl⟩ : syracuseStep 893591 = 1340387) B1340387
theorem B2859725 : Blo 393766 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B893771 : Blo 393766 893771 := bstep (se 1 (by rfl) ⟨670328, by rfl⟩ : syracuseStep 893771 = 1340657) B1340657
theorem B893825 : Blo 393766 893825 := bstep (se 2 (by rfl) ⟨335184, by rfl⟩ : syracuseStep 893825 = 670369) B670369
theorem B664537 : Blo 393766 664537 := bstep (se 2 (by rfl) ⟨249201, by rfl⟩ : syracuseStep 664537 = 498403) B498403
theorem B1123379 : Blo 393766 1123379 := bstep (se 1 (by rfl) ⟨842534, by rfl⟩ : syracuseStep 1123379 = 1685069) B1685069
theorem B894041 : Blo 393766 894041 := bstep (se 2 (by rfl) ⟨335265, by rfl⟩ : syracuseStep 894041 = 670531) B670531
theorem B894131 : Blo 393766 894131 := bstep (se 1 (by rfl) ⟨670598, by rfl⟩ : syracuseStep 894131 = 1341197) B1341197
theorem B894167 : Blo 393766 894167 := bstep (se 1 (by rfl) ⟨670625, by rfl⟩ : syracuseStep 894167 = 1341251) B1341251
theorem B894347 : Blo 393766 894347 := bstep (se 1 (by rfl) ⟨670760, by rfl⟩ : syracuseStep 894347 = 1341521) B1341521
theorem B894401 : Blo 393766 894401 := bstep (se 2 (by rfl) ⟨335400, by rfl⟩ : syracuseStep 894401 = 670801) B670801
theorem B632279 : Blo 393766 632279 := bstep (se 1 (by rfl) ⟨474209, by rfl⟩ : syracuseStep 632279 = 948419) B948419
theorem B665111 : Blo 393766 665111 := bstep (se 1 (by rfl) ⟨498833, by rfl⟩ : syracuseStep 665111 = 997667) B997667
theorem B665239 : Blo 393766 665239 := bstep (se 1 (by rfl) ⟨498929, by rfl⟩ : syracuseStep 665239 = 997859) B997859
theorem B894617 : Blo 393766 894617 := bstep (se 2 (by rfl) ⟨335481, by rfl⟩ : syracuseStep 894617 = 670963) B670963
theorem B894707 : Blo 393766 894707 := bstep (se 1 (by rfl) ⟨671030, by rfl⟩ : syracuseStep 894707 = 1342061) B1342061
theorem B894743 : Blo 393766 894743 := bstep (se 1 (by rfl) ⟨671057, by rfl⟩ : syracuseStep 894743 = 1342115) B1342115
theorem B4171565 : Blo 393766 4171565 := bstep (se 3 (by rfl) ⟨782168, by rfl⟩ : syracuseStep 4171565 = 1564337) B1564337
theorem B534361 : Blo 393766 534361 := bstep (se 2 (by rfl) ⟨200385, by rfl⟩ : syracuseStep 534361 = 400771) B400771
theorem B501643 : Blo 393766 501643 := bstep (se 1 (by rfl) ⟨376232, by rfl⟩ : syracuseStep 501643 = 752465) B752465
theorem B894923 : Blo 393766 894923 := bstep (se 1 (by rfl) ⟨671192, by rfl⟩ : syracuseStep 894923 = 1342385) B1342385
theorem B632843 : Blo 393766 632843 := bstep (se 1 (by rfl) ⟨474632, by rfl⟩ : syracuseStep 632843 = 949265) B949265
theorem B632983 : Blo 393766 632983 := bstep (se 1 (by rfl) ⟨474737, by rfl⟩ : syracuseStep 632983 = 949475) B949475
theorem B1812631 : Blo 393766 1812631 := bstep (se 1 (by rfl) ⟨1359473, by rfl⟩ : syracuseStep 1812631 = 2718947) B2718947
theorem B665867 : Blo 393766 665867 := bstep (se 1 (by rfl) ⟨499400, by rfl⟩ : syracuseStep 665867 = 998801) B998801
theorem B3221861 : Blo 393766 3221861 := bstep (se 4 (by rfl) ⟨302049, by rfl⟩ : syracuseStep 3221861 = 604099) B604099
theorem B665995 : Blo 393766 665995 := bstep (se 1 (by rfl) ⟨499496, by rfl⟩ : syracuseStep 665995 = 998993) B998993
theorem B666137 : Blo 393766 666137 := bstep (se 2 (by rfl) ⟨249801, by rfl⟩ : syracuseStep 666137 = 499603) B499603
theorem B1813067 : Blo 393766 1813067 := bstep (se 1 (by rfl) ⟨1359800, by rfl⟩ : syracuseStep 1813067 = 2719601) B2719601
theorem B1682009 : Blo 393766 1682009 := bstep (se 2 (by rfl) ⟨630753, by rfl⟩ : syracuseStep 1682009 = 1261507) B1261507
theorem B666265 : Blo 393766 666265 := bstep (se 2 (by rfl) ⟨249849, by rfl⟩ : syracuseStep 666265 = 499699) B499699
theorem B535243 : Blo 393766 535243 := bstep (se 1 (by rfl) ⟨401432, by rfl⟩ : syracuseStep 535243 = 802865) B802865
theorem B600791 : Blo 393766 600791 := bstep (se 1 (by rfl) ⟨450593, by rfl⟩ : syracuseStep 600791 = 901187) B901187
theorem B961303 : Blo 393766 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B502615 : Blo 393766 502615 := bstep (se 1 (by rfl) ⟨376961, by rfl⟩ : syracuseStep 502615 = 753923) B753923
theorem B633803 : Blo 393766 633803 := bstep (se 1 (by rfl) ⟨475352, by rfl⟩ : syracuseStep 633803 = 950705) B950705
theorem B633881 : Blo 393766 633881 := bstep (se 2 (by rfl) ⟨237705, by rfl⟩ : syracuseStep 633881 = 475411) B475411
theorem B666839 : Blo 393766 666839 := bstep (se 1 (by rfl) ⟨500129, by rfl⟩ : syracuseStep 666839 = 1000259) B1000259
theorem B666967 : Blo 393766 666967 := bstep (se 1 (by rfl) ⟨500225, by rfl⟩ : syracuseStep 666967 = 1000451) B1000451
theorem B1224215 : Blo 393766 1224215 := bstep (se 1 (by rfl) ⟨918161, by rfl⟩ : syracuseStep 1224215 = 1836323) B1836323
theorem B1126237 : Blo 393766 1126237 := bstep (se 3 (by rfl) ⟨211169, by rfl⟩ : syracuseStep 1126237 = 422339) B422339
theorem B1421201 : Blo 393766 1421201 := bstep (se 2 (by rfl) ⟨532950, by rfl⟩ : syracuseStep 1421201 = 1065901) B1065901
theorem B1126295 : Blo 393766 1126295 := bstep (se 1 (by rfl) ⟨844721, by rfl⟩ : syracuseStep 1126295 = 1689443) B1689443
theorem B667595 : Blo 393766 667595 := bstep (se 1 (by rfl) ⟨500696, by rfl⟩ : syracuseStep 667595 = 1001393) B1001393
theorem B667723 : Blo 393766 667723 := bstep (se 1 (by rfl) ⟨500792, by rfl⟩ : syracuseStep 667723 = 1001585) B1001585
theorem B2011229 : Blo 393766 2011229 := bstep (se 3 (by rfl) ⟨377105, by rfl⟩ : syracuseStep 2011229 = 754211) B754211
theorem B3813581 : Blo 393766 3813581 := bstep (se 3 (by rfl) ⟨715046, by rfl⟩ : syracuseStep 3813581 = 1430093) B1430093
theorem B667865 : Blo 393766 667865 := bstep (se 2 (by rfl) ⟨250449, by rfl⟩ : syracuseStep 667865 = 500899) B500899
theorem B2535725 : Blo 393766 2535725 := bstep (se 3 (by rfl) ⟨475448, by rfl⟩ : syracuseStep 2535725 = 950897) B950897
theorem B962891 : Blo 393766 962891 := bstep (se 1 (by rfl) ⟨722168, by rfl⟩ : syracuseStep 962891 = 1444337) B1444337
theorem B667993 : Blo 393766 667993 := bstep (se 2 (by rfl) ⟨250497, by rfl⟩ : syracuseStep 667993 = 500995) B500995
theorem B2405213 : Blo 393766 2405213 := bstep (se 3 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 2405213 = 901955) B901955
theorem B668567 : Blo 393766 668567 := bstep (se 1 (by rfl) ⟨501425, by rfl⟩ : syracuseStep 668567 = 1002851) B1002851
theorem B1356695 : Blo 393766 1356695 := bstep (se 1 (by rfl) ⟨1017521, by rfl⟩ : syracuseStep 1356695 = 2035043) B2035043
theorem B2995217 : Blo 393766 2995217 := bstep (se 2 (by rfl) ⟨1123206, by rfl⟩ : syracuseStep 2995217 = 2246413) B2246413
theorem B668695 : Blo 393766 668695 := bstep (se 1 (by rfl) ⟨501521, by rfl⟩ : syracuseStep 668695 = 1003043) B1003043
theorem B1127513 : Blo 393766 1127513 := bstep (se 2 (by rfl) ⟨422817, by rfl⟩ : syracuseStep 1127513 = 845635) B845635
theorem B2307203 : Blo 393766 2307203 := bstep (se 1 (by rfl) ⟨1730402, by rfl⟩ : syracuseStep 2307203 = 3460805) B3460805
theorem B1717393 : Blo 393766 1717393 := bstep (se 2 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 1717393 = 1288045) B1288045
theorem B1127627 : Blo 393766 1127627 := bstep (se 1 (by rfl) ⟨845720, by rfl⟩ : syracuseStep 1127627 = 1691441) B1691441
theorem B3650777 : Blo 393766 3650777 := bstep (se 2 (by rfl) ⟨1369041, by rfl⟩ : syracuseStep 3650777 = 2738083) B2738083
theorem B5715299 : Blo 393766 5715299 := bstep (se 1 (by rfl) ⟨4286474, by rfl⟩ : syracuseStep 5715299 = 8572949) B8572949
theorem B865753 : Blo 393766 865753 := bstep (se 2 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 865753 = 649315) B649315
theorem B996887 : Blo 393766 996887 := bstep (se 1 (by rfl) ⟨747665, by rfl⟩ : syracuseStep 996887 = 1495331) B1495331
theorem B5060171 : Blo 393766 5060171 := bstep (se 1 (by rfl) ⟨3795128, by rfl⟩ : syracuseStep 5060171 = 7590257) B7590257
theorem B669323 : Blo 393766 669323 := bstep (se 1 (by rfl) ⟨501992, by rfl⟩ : syracuseStep 669323 = 1003985) B1003985
theorem B6076109 : Blo 393766 6076109 := bstep (se 3 (by rfl) ⟨1139270, by rfl⟩ : syracuseStep 6076109 = 2278541) B2278541
theorem B669451 : Blo 393766 669451 := bstep (se 1 (by rfl) ⟨502088, by rfl⟩ : syracuseStep 669451 = 1004177) B1004177
theorem B6731585 : Blo 393766 6731585 := bstep (se 2 (by rfl) ⟨2524344, by rfl⟩ : syracuseStep 6731585 = 5048689) B5048689
theorem B1685393 : Blo 393766 1685393 := bstep (se 2 (by rfl) ⟨632022, by rfl⟩ : syracuseStep 1685393 = 1264045) B1264045
theorem B669593 : Blo 393766 669593 := bstep (se 2 (by rfl) ⟨251097, by rfl⟩ : syracuseStep 669593 = 502195) B502195
theorem B1423277 : Blo 393766 1423277 := bstep (se 3 (by rfl) ⟨266864, by rfl⟩ : syracuseStep 1423277 = 533729) B533729
theorem B3061709 : Blo 393766 3061709 := bstep (se 3 (by rfl) ⟨574070, by rfl⟩ : syracuseStep 3061709 = 1148141) B1148141
theorem B669721 : Blo 393766 669721 := bstep (se 2 (by rfl) ⟨251145, by rfl⟩ : syracuseStep 669721 = 502291) B502291
theorem B2013335 : Blo 393766 2013335 := bstep (se 1 (by rfl) ⟨1510001, by rfl⟩ : syracuseStep 2013335 = 3020003) B3020003
theorem B997555 : Blo 393766 997555 := bstep (se 1 (by rfl) ⟨748166, by rfl⟩ : syracuseStep 997555 = 1496333) B1496333
theorem B1128755 : Blo 393766 1128755 := bstep (se 1 (by rfl) ⟨846566, by rfl⟩ : syracuseStep 1128755 = 1693133) B1693133
theorem B997697 : Blo 393766 997697 := bstep (se 2 (by rfl) ⟨374136, by rfl⟩ : syracuseStep 997697 = 748273) B748273
theorem B670295 : Blo 393766 670295 := bstep (se 1 (by rfl) ⟨502721, by rfl⟩ : syracuseStep 670295 = 1005443) B1005443
theorem B1686109 : Blo 393766 1686109 := bstep (se 3 (by rfl) ⟨316145, by rfl⟩ : syracuseStep 1686109 = 632291) B632291
theorem B1129153 : Blo 393766 1129153 := bstep (se 2 (by rfl) ⟨423432, by rfl⟩ : syracuseStep 1129153 = 846865) B846865
theorem B670423 : Blo 393766 670423 := bstep (se 1 (by rfl) ⟨502817, by rfl⟩ : syracuseStep 670423 = 1005635) B1005635
theorem B474007 : Blo 393766 474007 := bstep (se 1 (by rfl) ⟨355505, by rfl⟩ : syracuseStep 474007 = 711011) B711011
theorem B900019 : Blo 393766 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B671051 : Blo 393766 671051 := bstep (se 1 (by rfl) ⟨503288, by rfl⟩ : syracuseStep 671051 = 1006577) B1006577
theorem B671179 : Blo 393766 671179 := bstep (se 1 (by rfl) ⟨503384, by rfl⟩ : syracuseStep 671179 = 1006769) B1006769
theorem B998963 : Blo 393766 998963 := bstep (se 1 (by rfl) ⟨749222, by rfl⟩ : syracuseStep 998963 = 1498445) B1498445
theorem B867905 : Blo 393766 867905 := bstep (se 2 (by rfl) ⟨325464, by rfl⟩ : syracuseStep 867905 = 650929) B650929
theorem B4505219 : Blo 393766 4505219 := bstep (se 1 (by rfl) ⟨3378914, by rfl⟩ : syracuseStep 4505219 = 6757829) B6757829
theorem B1065035 : Blo 393766 1065035 := bstep (se 1 (by rfl) ⟨798776, by rfl⟩ : syracuseStep 1065035 = 1597553) B1597553
theorem B999499 : Blo 393766 999499 := bstep (se 1 (by rfl) ⟨749624, by rfl⟩ : syracuseStep 999499 = 1499249) B1499249
theorem B3653707 : Blo 393766 3653707 := bstep (se 1 (by rfl) ⟨2740280, by rfl⟩ : syracuseStep 3653707 = 5480561) B5480561
theorem B573655 : Blo 393766 573655 := bstep (se 1 (by rfl) ⟨430241, by rfl⟩ : syracuseStep 573655 = 860483) B860483
theorem B999641 : Blo 393766 999641 := bstep (se 2 (by rfl) ⟨374865, by rfl⟩ : syracuseStep 999641 = 749731) B749731
theorem B1065305 : Blo 393766 1065305 := bstep (se 2 (by rfl) ⟨399489, by rfl⟩ : syracuseStep 1065305 = 798979) B798979
theorem B2539927 : Blo 393766 2539927 := bstep (se 1 (by rfl) ⟨1904945, by rfl⟩ : syracuseStep 2539927 = 3809891) B3809891
theorem B2310617 : Blo 393766 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B836185 : Blo 393766 836185 := bstep (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) B627139
theorem B1065565 : Blo 393766 1065565 := bstep (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) B399587
theorem B443083 : Blo 393766 443083 := bstep (se 1 (by rfl) ⟨332312, by rfl⟩ : syracuseStep 443083 = 664625) B664625
theorem B443191 : Blo 393766 443191 := bstep (se 1 (by rfl) ⟨332393, by rfl⟩ : syracuseStep 443191 = 664787) B664787
theorem B2999105 : Blo 393766 2999105 := bstep (se 2 (by rfl) ⟨1124664, by rfl⟩ : syracuseStep 2999105 = 2249329) B2249329
theorem B3031901 : Blo 393766 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B443371 : Blo 393766 443371 := bstep (se 1 (by rfl) ⟨332528, by rfl⟩ : syracuseStep 443371 = 665057) B665057
theorem B1000471 : Blo 393766 1000471 := bstep (se 1 (by rfl) ⟨750353, by rfl⟩ : syracuseStep 1000471 = 1500707) B1500707
theorem B443479 : Blo 393766 443479 := bstep (se 1 (by rfl) ⟨332609, by rfl⟩ : syracuseStep 443479 = 665219) B665219
theorem B1131671 : Blo 393766 1131671 := bstep (se 1 (by rfl) ⟨848753, by rfl⟩ : syracuseStep 1131671 = 1697507) B1697507
theorem B443659 : Blo 393766 443659 := bstep (se 1 (by rfl) ⟨332744, by rfl⟩ : syracuseStep 443659 = 665489) B665489
theorem B443767 : Blo 393766 443767 := bstep (se 1 (by rfl) ⟨332825, by rfl⟩ : syracuseStep 443767 = 665651) B665651
theorem B902593 : Blo 393766 902593 := bstep (se 2 (by rfl) ⟨338472, by rfl⟩ : syracuseStep 902593 = 676945) B676945
theorem B1000907 : Blo 393766 1000907 := bstep (se 1 (by rfl) ⟨750680, by rfl⟩ : syracuseStep 1000907 = 1501361) B1501361
theorem B1426967 : Blo 393766 1426967 := bstep (se 1 (by rfl) ⟨1070225, by rfl⟩ : syracuseStep 1426967 = 2140451) B2140451
theorem B443947 : Blo 393766 443947 := bstep (se 1 (by rfl) ⟨332960, by rfl⟩ : syracuseStep 443947 = 665921) B665921
theorem B444055 : Blo 393766 444055 := bstep (se 1 (by rfl) ⟨333041, by rfl⟩ : syracuseStep 444055 = 666083) B666083
theorem B1427095 : Blo 393766 1427095 := bstep (se 1 (by rfl) ⟨1070321, by rfl⟩ : syracuseStep 1427095 = 2140643) B2140643
theorem B1066775 : Blo 393766 1066775 := bstep (se 1 (by rfl) ⟨800081, by rfl⟩ : syracuseStep 1066775 = 1600163) B1600163
theorem B1001281 : Blo 393766 1001281 := bstep (se 2 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 1001281 = 750961) B750961
theorem B444235 : Blo 393766 444235 := bstep (se 1 (by rfl) ⟨333176, by rfl⟩ : syracuseStep 444235 = 666353) B666353
theorem B1329047 : Blo 393766 1329047 := bstep (se 1 (by rfl) ⟨996785, by rfl⟩ : syracuseStep 1329047 = 1993571) B1993571
theorem B444343 : Blo 393766 444343 := bstep (se 1 (by rfl) ⟨333257, by rfl⟩ : syracuseStep 444343 = 666515) B666515
theorem B444523 : Blo 393766 444523 := bstep (se 1 (by rfl) ⟨333392, by rfl⟩ : syracuseStep 444523 = 666785) B666785
theorem B1689731 : Blo 393766 1689731 := bstep (se 1 (by rfl) ⟨1267298, by rfl⟩ : syracuseStep 1689731 = 2534597) B2534597
theorem B444631 : Blo 393766 444631 := bstep (se 1 (by rfl) ⟨333473, by rfl⟩ : syracuseStep 444631 = 666947) B666947
theorem B444811 : Blo 393766 444811 := bstep (se 1 (by rfl) ⟨333608, by rfl⟩ : syracuseStep 444811 = 667217) B667217
theorem B1001879 : Blo 393766 1001879 := bstep (se 1 (by rfl) ⟨751409, by rfl⟩ : syracuseStep 1001879 = 1502819) B1502819
theorem B1329587 : Blo 393766 1329587 := bstep (se 1 (by rfl) ⟨997190, by rfl⟩ : syracuseStep 1329587 = 1994381) B1994381
theorem B2443699 : Blo 393766 2443699 := bstep (se 1 (by rfl) ⟨1832774, by rfl⟩ : syracuseStep 2443699 = 3665549) B3665549
theorem B1067467 : Blo 393766 1067467 := bstep (se 1 (by rfl) ⟨800600, by rfl⟩ : syracuseStep 1067467 = 1601201) B1601201
theorem B444919 : Blo 393766 444919 := bstep (se 1 (by rfl) ⟨333689, by rfl⟩ : syracuseStep 444919 = 667379) B667379
theorem B445099 : Blo 393766 445099 := bstep (se 1 (by rfl) ⟨333824, by rfl⟩ : syracuseStep 445099 = 667649) B667649
theorem B1329857 : Blo 393766 1329857 := bstep (se 2 (by rfl) ⟨498696, by rfl⟩ : syracuseStep 1329857 = 997393) B997393
theorem B3001049 : Blo 393766 3001049 := bstep (se 2 (by rfl) ⟨1125393, by rfl⟩ : syracuseStep 3001049 = 2250787) B2250787
theorem B445207 : Blo 393766 445207 := bstep (se 1 (by rfl) ⟨333905, by rfl⟩ : syracuseStep 445207 = 667811) B667811
theorem B2280257 : Blo 393766 2280257 := bstep (se 2 (by rfl) ⟨855096, by rfl⟩ : syracuseStep 2280257 = 1710193) B1710193
theorem B641881 : Blo 393766 641881 := bstep (se 2 (by rfl) ⟨240705, by rfl⟩ : syracuseStep 641881 = 481411) B481411
theorem B1919875 : Blo 393766 1919875 := bstep (se 1 (by rfl) ⟨1439906, by rfl⟩ : syracuseStep 1919875 = 2879813) B2879813
theorem B445387 : Blo 393766 445387 := bstep (se 1 (by rfl) ⟨334040, by rfl⟩ : syracuseStep 445387 = 668081) B668081
theorem B805889 : Blo 393766 805889 := bstep (se 2 (by rfl) ⟨302208, by rfl⟩ : syracuseStep 805889 = 604417) B604417
theorem B445495 : Blo 393766 445495 := bstep (se 1 (by rfl) ⟨334121, by rfl⟩ : syracuseStep 445495 = 668243) B668243
theorem B1428653 : Blo 393766 1428653 := bstep (se 3 (by rfl) ⟨267872, by rfl⟩ : syracuseStep 1428653 = 535745) B535745
theorem B1002689 : Blo 393766 1002689 := bstep (se 2 (by rfl) ⟨376008, by rfl⟩ : syracuseStep 1002689 = 752017) B752017
theorem B1330397 : Blo 393766 1330397 := bstep (se 3 (by rfl) ⟨249449, by rfl⟩ : syracuseStep 1330397 = 498899) B498899
theorem B445675 : Blo 393766 445675 := bstep (se 1 (by rfl) ⟨334256, by rfl⟩ : syracuseStep 445675 = 668513) B668513
theorem B445783 : Blo 393766 445783 := bstep (se 1 (by rfl) ⟨334337, by rfl⟩ : syracuseStep 445783 = 668675) B668675
theorem B445963 : Blo 393766 445963 := bstep (se 1 (by rfl) ⟨334472, by rfl⟩ : syracuseStep 445963 = 668945) B668945
theorem B3788363 : Blo 393766 3788363 := bstep (se 1 (by rfl) ⟨2841272, by rfl⟩ : syracuseStep 3788363 = 5682545) B5682545
theorem B446071 : Blo 393766 446071 := bstep (se 1 (by rfl) ⟨334553, by rfl⟩ : syracuseStep 446071 = 669107) B669107
theorem B1003225 : Blo 393766 1003225 := bstep (se 2 (by rfl) ⟨376209, by rfl⟩ : syracuseStep 1003225 = 752419) B752419
theorem B446251 : Blo 393766 446251 := bstep (se 1 (by rfl) ⟨334688, by rfl⟩ : syracuseStep 446251 = 669377) B669377
theorem B1691543 : Blo 393766 1691543 := bstep (se 1 (by rfl) ⟨1268657, by rfl⟩ : syracuseStep 1691543 = 2537315) B2537315
theorem B446359 : Blo 393766 446359 := bstep (se 1 (by rfl) ⟨334769, by rfl⟩ : syracuseStep 446359 = 669539) B669539
theorem B446539 : Blo 393766 446539 := bstep (se 1 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 446539 = 669809) B669809
theorem B1527959 : Blo 393766 1527959 := bstep (se 1 (by rfl) ⟨1145969, by rfl⟩ : syracuseStep 1527959 = 2291939) B2291939
theorem B446647 : Blo 393766 446647 := bstep (se 1 (by rfl) ⟨334985, by rfl⟩ : syracuseStep 446647 = 669971) B669971
theorem B1495361 : Blo 393766 1495361 := bstep (se 2 (by rfl) ⟨560760, by rfl⟩ : syracuseStep 1495361 = 1121521) B1121521
theorem B1331531 : Blo 393766 1331531 := bstep (se 1 (by rfl) ⟨998648, by rfl⟩ : syracuseStep 1331531 = 1997297) B1997297
theorem B446827 : Blo 393766 446827 := bstep (se 1 (by rfl) ⟨335120, by rfl⟩ : syracuseStep 446827 = 670241) B670241
theorem B610763 : Blo 393766 610763 := bstep (se 1 (by rfl) ⟨458072, by rfl⟩ : syracuseStep 610763 = 916145) B916145
theorem B446935 : Blo 393766 446935 := bstep (se 1 (by rfl) ⟨335201, by rfl⟩ : syracuseStep 446935 = 670403) B670403
theorem B1331801 : Blo 393766 1331801 := bstep (se 2 (by rfl) ⟨499425, by rfl⟩ : syracuseStep 1331801 = 998851) B998851
theorem B2839171 : Blo 393766 2839171 := bstep (se 1 (by rfl) ⟨2129378, by rfl⟩ : syracuseStep 2839171 = 4258757) B4258757
theorem B447115 : Blo 393766 447115 := bstep (se 1 (by rfl) ⟨335336, by rfl⟩ : syracuseStep 447115 = 670673) B670673
theorem B3396275 : Blo 393766 3396275 := bstep (se 1 (by rfl) ⟨2547206, by rfl⟩ : syracuseStep 3396275 = 5094413) B5094413
theorem B447223 : Blo 393766 447223 := bstep (se 1 (by rfl) ⟨335417, by rfl⟩ : syracuseStep 447223 = 670835) B670835
theorem B1004339 : Blo 393766 1004339 := bstep (se 1 (by rfl) ⟨753254, by rfl⟩ : syracuseStep 1004339 = 1506509) B1506509
theorem B2249603 : Blo 393766 2249603 := bstep (se 1 (by rfl) ⟨1687202, by rfl⟩ : syracuseStep 2249603 = 3374405) B3374405
theorem B447403 : Blo 393766 447403 := bstep (se 1 (by rfl) ⟨335552, by rfl⟩ : syracuseStep 447403 = 671105) B671105
theorem B1496029 : Blo 393766 1496029 := bstep (se 3 (by rfl) ⟨280505, by rfl⟩ : syracuseStep 1496029 = 561011) B561011
theorem B3396653 : Blo 393766 3396653 := bstep (se 3 (by rfl) ⟨636872, by rfl⟩ : syracuseStep 3396653 = 1273745) B1273745
theorem B2774081 : Blo 393766 2774081 := bstep (se 2 (by rfl) ⟨1040280, by rfl⟩ : syracuseStep 2774081 = 2080561) B2080561
theorem B1004633 : Blo 393766 1004633 := bstep (se 2 (by rfl) ⟨376737, by rfl⟩ : syracuseStep 1004633 = 753475) B753475
theorem B1692875 : Blo 393766 1692875 := bstep (se 1 (by rfl) ⟨1269656, by rfl⟩ : syracuseStep 1692875 = 2539313) B2539313
theorem B1332503 : Blo 393766 1332503 := bstep (se 1 (by rfl) ⟨999377, by rfl⟩ : syracuseStep 1332503 = 1998755) B1998755
theorem B3429697 : Blo 393766 3429697 := bstep (se 2 (by rfl) ⟨1286136, by rfl⟩ : syracuseStep 3429697 = 2572273) B2572273
theorem B841099 : Blo 393766 841099 := bstep (se 1 (by rfl) ⟨630824, by rfl⟩ : syracuseStep 841099 = 1261649) B1261649
theorem B3593651 : Blo 393766 3593651 := bstep (se 1 (by rfl) ⟨2695238, by rfl⟩ : syracuseStep 3593651 = 5390477) B5390477
theorem B611993 : Blo 393766 611993 := bstep (se 2 (by rfl) ⟨229497, by rfl⟩ : syracuseStep 611993 = 458995) B458995
theorem B1693457 : Blo 393766 1693457 := bstep (se 2 (by rfl) ⟨635046, by rfl⟩ : syracuseStep 1693457 = 1270093) B1270093
theorem B1333043 : Blo 393766 1333043 := bstep (se 1 (by rfl) ⟨999782, by rfl⟩ : syracuseStep 1333043 = 1999565) B1999565
theorem B1300313 : Blo 393766 1300313 := bstep (se 2 (by rfl) ⟨487617, by rfl⟩ : syracuseStep 1300313 = 975235) B975235
theorem B8214371 : Blo 393766 8214371 := bstep (se 1 (by rfl) ⟨6160778, by rfl⟩ : syracuseStep 8214371 = 12321557) B12321557
theorem B9656243 : Blo 393766 9656243 := bstep (se 1 (by rfl) ⟨7242182, by rfl⟩ : syracuseStep 9656243 = 14484365) B14484365
theorem B3004451 : Blo 393766 3004451 := bstep (se 1 (by rfl) ⟨2253338, by rfl⟩ : syracuseStep 3004451 = 4506677) B4506677
theorem B1333313 : Blo 393766 1333313 := bstep (se 2 (by rfl) ⟨499992, by rfl⟩ : syracuseStep 1333313 = 999985) B999985
theorem B1497305 : Blo 393766 1497305 := bstep (se 2 (by rfl) ⟨561489, by rfl⟩ : syracuseStep 1497305 = 1122979) B1122979
theorem B1202483 : Blo 393766 1202483 := bstep (se 1 (by rfl) ⟨901862, by rfl⟩ : syracuseStep 1202483 = 1803725) B1803725
theorem B842329 : Blo 393766 842329 := bstep (se 2 (by rfl) ⟨315873, by rfl⟩ : syracuseStep 842329 = 631747) B631747
theorem B1333853 : Blo 393766 1333853 := bstep (se 3 (by rfl) ⟨250097, by rfl⟩ : syracuseStep 1333853 = 500195) B500195
theorem B1006283 : Blo 393766 1006283 := bstep (se 1 (by rfl) ⟨754712, by rfl⟩ : syracuseStep 1006283 = 1509425) B1509425
theorem B1432343 : Blo 393766 1432343 := bstep (se 1 (by rfl) ⟨1074257, by rfl⟩ : syracuseStep 1432343 = 2148515) B2148515
theorem B1694515 : Blo 393766 1694515 := bstep (se 1 (by rfl) ⟨1270886, by rfl⟩ : syracuseStep 1694515 = 2541773) B2541773
theorem B6970211 : Blo 393766 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B1072075 : Blo 393766 1072075 := bstep (se 1 (by rfl) ⟨804056, by rfl⟩ : syracuseStep 1072075 = 1608113) B1608113
theorem B2579473 : Blo 393766 2579473 := bstep (se 2 (by rfl) ⟨967302, by rfl⟩ : syracuseStep 2579473 = 1934605) B1934605
theorem B1268939 : Blo 393766 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B1334987 : Blo 393766 1334987 := bstep (se 1 (by rfl) ⟨1001240, by rfl⟩ : syracuseStep 1334987 = 2002481) B2002481
theorem B1498931 : Blo 393766 1498931 := bstep (se 1 (by rfl) ⟨1124198, by rfl⟩ : syracuseStep 1498931 = 2248397) B2248397
theorem B1498945 : Blo 393766 1498945 := bstep (se 2 (by rfl) ⟨562104, by rfl⟩ : syracuseStep 1498945 = 1124209) B1124209
theorem B1335257 : Blo 393766 1335257 := bstep (se 2 (by rfl) ⟨500721, by rfl⟩ : syracuseStep 1335257 = 1001443) B1001443
theorem B1695917 : Blo 393766 1695917 := bstep (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) B635969
theorem B5497267 : Blo 393766 5497267 := bstep (se 1 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 5497267 = 8245901) B8245901
theorem B1335959 : Blo 393766 1335959 := bstep (se 1 (by rfl) ⟨1001969, by rfl⟩ : syracuseStep 1335959 = 2003939) B2003939
theorem B713369 : Blo 393766 713369 := bstep (se 2 (by rfl) ⟨267513, by rfl⟩ : syracuseStep 713369 = 535027) B535027
theorem B811723 : Blo 393766 811723 := bstep (se 1 (by rfl) ⟨608792, by rfl⟩ : syracuseStep 811723 = 1217585) B1217585
theorem B1270579 : Blo 393766 1270579 := bstep (se 1 (by rfl) ⟨952934, by rfl⟩ : syracuseStep 1270579 = 1905869) B1905869
theorem B1336499 : Blo 393766 1336499 := bstep (se 1 (by rfl) ⟨1002374, by rfl⟩ : syracuseStep 1336499 = 2004749) B2004749
theorem B3433859 : Blo 393766 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B1598899 : Blo 393766 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B1336769 : Blo 393766 1336769 := bstep (se 2 (by rfl) ⟨501288, by rfl⟩ : syracuseStep 1336769 = 1002577) B1002577
theorem B1500875 : Blo 393766 1500875 := bstep (se 1 (by rfl) ⟨1125656, by rfl⟩ : syracuseStep 1500875 = 2251313) B2251313
theorem B845515 : Blo 393766 845515 := bstep (se 1 (by rfl) ⟨634136, by rfl⟩ : syracuseStep 845515 = 1268273) B1268273
theorem B1500889 : Blo 393766 1500889 := bstep (se 2 (by rfl) ⟨562833, by rfl⟩ : syracuseStep 1500889 = 1125667) B1125667
theorem B1337309 : Blo 393766 1337309 := bstep (se 3 (by rfl) ⟨250745, by rfl⟩ : syracuseStep 1337309 = 501491) B501491
theorem B2254979 : Blo 393766 2254979 := bstep (se 1 (by rfl) ⟨1691234, by rfl⟩ : syracuseStep 2254979 = 3382469) B3382469
theorem B845977 : Blo 393766 845977 := bstep (se 2 (by rfl) ⟨317241, by rfl⟩ : syracuseStep 845977 = 634483) B634483
theorem B813235 : Blo 393766 813235 := bstep (se 1 (by rfl) ⟨609926, by rfl⟩ : syracuseStep 813235 = 1219853) B1219853
theorem B747787 : Blo 393766 747787 := bstep (se 1 (by rfl) ⟨560840, by rfl⟩ : syracuseStep 747787 = 1121681) B1121681
theorem B747863 : Blo 393766 747863 := bstep (se 1 (by rfl) ⟨560897, by rfl⟩ : syracuseStep 747863 = 1121795) B1121795
theorem B3369347 : Blo 393766 3369347 := bstep (se 1 (by rfl) ⟨2527010, by rfl⟩ : syracuseStep 3369347 = 5054021) B5054021
theorem B2255435 : Blo 393766 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B715351 : Blo 393766 715351 := bstep (se 1 (by rfl) ⟨536513, by rfl⟩ : syracuseStep 715351 = 1073027) B1073027
theorem B715393 : Blo 393766 715393 := bstep (se 2 (by rfl) ⟨268272, by rfl⟩ : syracuseStep 715393 = 536545) B536545
theorem B6744707 : Blo 393766 6744707 := bstep (se 1 (by rfl) ⟨5058530, by rfl⟩ : syracuseStep 6744707 = 10117061) B10117061
theorem B1501847 : Blo 393766 1501847 := bstep (se 1 (by rfl) ⟨1126385, by rfl⟩ : syracuseStep 1501847 = 2252771) B2252771
theorem B453367 : Blo 393766 453367 := bstep (se 1 (by rfl) ⟨340025, by rfl⟩ : syracuseStep 453367 = 680051) B680051
theorem B420823 : Blo 393766 420823 := bstep (se 1 (by rfl) ⟨315617, by rfl⟩ : syracuseStep 420823 = 631235) B631235
theorem B748531 : Blo 393766 748531 := bstep (se 1 (by rfl) ⟨561398, by rfl⟩ : syracuseStep 748531 = 1122797) B1122797
theorem B1338443 : Blo 393766 1338443 := bstep (se 1 (by rfl) ⟨1003832, by rfl⟩ : syracuseStep 1338443 = 2007665) B2007665
theorem B1272925 : Blo 393766 1272925 := bstep (se 3 (by rfl) ⟨238673, by rfl⟩ : syracuseStep 1272925 = 477347) B477347
theorem B748759 : Blo 393766 748759 := bstep (se 1 (by rfl) ⟨561569, by rfl⟩ : syracuseStep 748759 = 1123139) B1123139
theorem B3009797 : Blo 393766 3009797 := bstep (se 4 (by rfl) ⟨282168, by rfl⟩ : syracuseStep 3009797 = 564337) B564337
theorem B716057 : Blo 393766 716057 := bstep (se 2 (by rfl) ⟨268521, by rfl⟩ : syracuseStep 716057 = 537043) B537043
theorem B748865 : Blo 393766 748865 := bstep (se 2 (by rfl) ⟨280824, by rfl⟩ : syracuseStep 748865 = 561649) B561649
theorem B1338713 : Blo 393766 1338713 := bstep (se 2 (by rfl) ⟨502017, by rfl⟩ : syracuseStep 1338713 = 1004035) B1004035
theorem B1207703 : Blo 393766 1207703 := bstep (se 1 (by rfl) ⟨905777, by rfl⟩ : syracuseStep 1207703 = 1811555) B1811555
theorem B749017 : Blo 393766 749017 := bstep (se 2 (by rfl) ⟨280881, by rfl⟩ : syracuseStep 749017 = 561763) B561763
theorem B847361 : Blo 393766 847361 := bstep (se 2 (by rfl) ⟨317760, by rfl⟩ : syracuseStep 847361 = 635521) B635521
theorem B421643 : Blo 393766 421643 := bstep (se 1 (by rfl) ⟨316232, by rfl⟩ : syracuseStep 421643 = 632465) B632465
theorem B1503107 : Blo 393766 1503107 := bstep (se 1 (by rfl) ⟨1127330, by rfl⟩ : syracuseStep 1503107 = 2254661) B2254661
theorem B1339415 : Blo 393766 1339415 := bstep (se 1 (by rfl) ⟨1004561, by rfl⟩ : syracuseStep 1339415 = 2009123) B2009123
theorem B1896797 : Blo 393766 1896797 := bstep (se 3 (by rfl) ⟨355649, by rfl⟩ : syracuseStep 1896797 = 711299) B711299
theorem B1339955 : Blo 393766 1339955 := bstep (se 1 (by rfl) ⟨1004966, by rfl⟩ : syracuseStep 1339955 = 2009933) B2009933
theorem B14676677 : Blo 393766 14676677 := bstep (se 4 (by rfl) ⟨1375938, by rfl⟩ : syracuseStep 14676677 = 2751877) B2751877
theorem B750323 : Blo 393766 750323 := bstep (se 1 (by rfl) ⟨562742, by rfl⟩ : syracuseStep 750323 = 1125485) B1125485
theorem B1340225 : Blo 393766 1340225 := bstep (se 2 (by rfl) ⟨502584, by rfl⟩ : syracuseStep 1340225 = 1005169) B1005169
theorem B3240805 : Blo 393766 3240805 := bstep (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) B607651
theorem B750475 : Blo 393766 750475 := bstep (se 1 (by rfl) ⟨562856, by rfl⟩ : syracuseStep 750475 = 1125713) B1125713
theorem B5731397 : Blo 393766 5731397 := bstep (se 4 (by rfl) ⟨537318, by rfl⟩ : syracuseStep 5731397 = 1074637) B1074637
theorem B423031 : Blo 393766 423031 := bstep (se 1 (by rfl) ⟨317273, by rfl⟩ : syracuseStep 423031 = 634547) B634547
theorem B849035 : Blo 393766 849035 := bstep (se 1 (by rfl) ⟨636776, by rfl⟩ : syracuseStep 849035 = 1273553) B1273553
theorem B1799347 : Blo 393766 1799347 := bstep (se 1 (by rfl) ⟨1349510, by rfl⟩ : syracuseStep 1799347 = 2699021) B2699021
theorem B750809 : Blo 393766 750809 := bstep (se 2 (by rfl) ⟨281553, by rfl⟩ : syracuseStep 750809 = 563107) B563107
theorem B5076269 : Blo 393766 5076269 := bstep (se 3 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 5076269 = 1903601) B1903601
theorem B1340765 : Blo 393766 1340765 := bstep (se 3 (by rfl) ⟨251393, by rfl⟩ : syracuseStep 1340765 = 502787) B502787
theorem B1996163 : Blo 393766 1996163 := bstep (se 1 (by rfl) ⟨1497122, by rfl⟩ : syracuseStep 1996163 = 2994245) B2994245
theorem B1144343 : Blo 393766 1144343 := bstep (se 1 (by rfl) ⟨858257, by rfl⟩ : syracuseStep 1144343 = 1716515) B1716515
theorem B1603147 : Blo 393766 1603147 := bstep (se 1 (by rfl) ⟨1202360, by rfl⟩ : syracuseStep 1603147 = 2404721) B2404721
theorem B3012227 : Blo 393766 3012227 := bstep (se 1 (by rfl) ⟨2259170, by rfl⟩ : syracuseStep 3012227 = 4518341) B4518341
theorem B751447 : Blo 393766 751447 := bstep (se 1 (by rfl) ⟨563585, by rfl⟩ : syracuseStep 751447 = 1127171) B1127171
theorem B423851 : Blo 393766 423851 := bstep (se 1 (by rfl) ⟨317888, by rfl⟩ : syracuseStep 423851 = 635777) B635777
theorem B6387673 : Blo 393766 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B5732369 : Blo 393766 5732369 := bstep (se 2 (by rfl) ⟨2149638, by rfl⟩ : syracuseStep 5732369 = 4299277) B4299277
theorem B8550805 : Blo 393766 8550805 := bstep (se 6 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 8550805 = 400819) B400819
theorem B1341899 : Blo 393766 1341899 := bstep (se 1 (by rfl) ⟨1006424, by rfl⟩ : syracuseStep 1341899 = 2012849) B2012849
theorem B752267 : Blo 393766 752267 := bstep (se 1 (by rfl) ⟨564200, by rfl⟩ : syracuseStep 752267 = 1128401) B1128401
theorem B457367 : Blo 393766 457367 := bstep (se 1 (by rfl) ⟨343025, by rfl⟩ : syracuseStep 457367 = 686051) B686051
theorem B752321 : Blo 393766 752321 := bstep (se 2 (by rfl) ⟨282120, by rfl⟩ : syracuseStep 752321 = 564241) B564241
theorem B1342169 : Blo 393766 1342169 := bstep (se 2 (by rfl) ⟨503313, by rfl⟩ : syracuseStep 1342169 = 1006627) B1006627
theorem B1899395 : Blo 393766 1899395 := bstep (se 1 (by rfl) ⟨1424546, by rfl⟩ : syracuseStep 1899395 = 2849093) B2849093
theorem B1506221 : Blo 393766 1506221 := bstep (se 3 (by rfl) ⟨282416, by rfl⟩ : syracuseStep 1506221 = 564833) B564833
theorem B1145821 : Blo 393766 1145821 := bstep (se 3 (by rfl) ⟨214841, by rfl⟩ : syracuseStep 1145821 = 429683) B429683
theorem B949313 : Blo 393766 949313 := bstep (se 2 (by rfl) ⟨355992, by rfl⟩ : syracuseStep 949313 = 711985) B711985
theorem B2849867 : Blo 393766 2849867 := bstep (se 1 (by rfl) ⟨2137400, by rfl⟩ : syracuseStep 2849867 = 4274801) B4274801
theorem B2260061 : Blo 393766 2260061 := bstep (se 3 (by rfl) ⟨423761, by rfl⟩ : syracuseStep 2260061 = 847523) B847523
theorem B753239 : Blo 393766 753239 := bstep (se 1 (by rfl) ⟨564929, by rfl⟩ : syracuseStep 753239 = 1129859) B1129859
theorem B1506995 : Blo 393766 1506995 := bstep (se 1 (by rfl) ⟨1130246, by rfl⟩ : syracuseStep 1506995 = 2260493) B2260493
theorem B2260811 : Blo 393766 2260811 := bstep (se 1 (by rfl) ⟨1695608, by rfl⟩ : syracuseStep 2260811 = 3391217) B3391217
theorem B18087857 : Blo 393766 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B2293879 : Blo 393766 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B754105 : Blo 393766 754105 := bstep (se 2 (by rfl) ⟨282789, by rfl⟩ : syracuseStep 754105 = 565579) B565579
theorem B1999403 : Blo 393766 1999403 := bstep (se 1 (by rfl) ⟨1499552, by rfl⟩ : syracuseStep 1999403 = 2999105) B2999105
theorem B393787 : Blo 393766 393787 := bstep (se 1 (by rfl) ⟨295340, by rfl⟩ : syracuseStep 393787 = 590681) B590681
theorem B393863 : Blo 393766 393863 := bstep (se 1 (by rfl) ⟨295397, by rfl⟩ : syracuseStep 393863 = 590795) B590795
theorem B393871 : Blo 393766 393871 := bstep (se 1 (by rfl) ⟨295403, by rfl⟩ : syracuseStep 393871 = 590807) B590807
theorem B393915 : Blo 393766 393915 := bstep (se 1 (by rfl) ⟨295436, by rfl⟩ : syracuseStep 393915 = 590873) B590873
theorem B393991 : Blo 393766 393991 := bstep (se 1 (by rfl) ⟨295493, by rfl⟩ : syracuseStep 393991 = 590987) B590987
theorem B393999 : Blo 393766 393999 := bstep (se 1 (by rfl) ⟨295499, by rfl⟩ : syracuseStep 393999 = 590999) B590999
theorem B754447 : Blo 393766 754447 := bstep (se 1 (by rfl) ⟨565835, by rfl⟩ : syracuseStep 754447 = 1131671) B1131671
theorem B1114913 : Blo 393766 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B590651 : Blo 393766 590651 := bstep (se 1 (by rfl) ⟨442988, by rfl⟩ : syracuseStep 590651 = 885977) B885977
theorem B394043 : Blo 393766 394043 := bstep (se 1 (by rfl) ⟨295532, by rfl⟩ : syracuseStep 394043 = 591065) B591065
theorem B590711 : Blo 393766 590711 := bstep (se 1 (by rfl) ⟨443033, by rfl⟩ : syracuseStep 590711 = 886067) B886067
theorem B394119 : Blo 393766 394119 := bstep (se 1 (by rfl) ⟨295589, by rfl⟩ : syracuseStep 394119 = 591179) B591179
theorem B590735 : Blo 393766 590735 := bstep (se 1 (by rfl) ⟨443051, by rfl⟩ : syracuseStep 590735 = 886103) B886103
theorem B394127 : Blo 393766 394127 := bstep (se 1 (by rfl) ⟨295595, by rfl⟩ : syracuseStep 394127 = 591191) B591191
theorem B590777 : Blo 393766 590777 := bstep (se 2 (by rfl) ⟨221541, by rfl⟩ : syracuseStep 590777 = 443083) B443083
theorem B1082297 : Blo 393766 1082297 := bstep (se 2 (by rfl) ⟨405861, by rfl⟩ : syracuseStep 1082297 = 811723) B811723
theorem B394171 : Blo 393766 394171 := bstep (se 1 (by rfl) ⟨295628, by rfl⟩ : syracuseStep 394171 = 591257) B591257
theorem B590855 : Blo 393766 590855 := bstep (se 1 (by rfl) ⟨443141, by rfl⟩ : syracuseStep 590855 = 886283) B886283
theorem B394247 : Blo 393766 394247 := bstep (se 1 (by rfl) ⟨295685, by rfl⟩ : syracuseStep 394247 = 591371) B591371
theorem B394255 : Blo 393766 394255 := bstep (se 1 (by rfl) ⟨295691, by rfl⟩ : syracuseStep 394255 = 591383) B591383
theorem B951311 : Blo 393766 951311 := bstep (se 1 (by rfl) ⟨713483, by rfl⟩ : syracuseStep 951311 = 1426967) B1426967
theorem B590891 : Blo 393766 590891 := bstep (se 1 (by rfl) ⟨443168, by rfl⟩ : syracuseStep 590891 = 886337) B886337
theorem B394299 : Blo 393766 394299 := bstep (se 1 (by rfl) ⟨295724, by rfl⟩ : syracuseStep 394299 = 591449) B591449
theorem B590921 : Blo 393766 590921 := bstep (se 2 (by rfl) ⟨221595, by rfl⟩ : syracuseStep 590921 = 443191) B443191
theorem B394375 : Blo 393766 394375 := bstep (se 1 (by rfl) ⟨295781, by rfl⟩ : syracuseStep 394375 = 591563) B591563
theorem B394383 : Blo 393766 394383 := bstep (se 1 (by rfl) ⟨295787, by rfl⟩ : syracuseStep 394383 = 591575) B591575
theorem B591035 : Blo 393766 591035 := bstep (se 1 (by rfl) ⟨443276, by rfl⟩ : syracuseStep 591035 = 886553) B886553
theorem B394427 : Blo 393766 394427 := bstep (se 1 (by rfl) ⟨295820, by rfl⟩ : syracuseStep 394427 = 591641) B591641
theorem B6161645 : Blo 393766 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B591095 : Blo 393766 591095 := bstep (se 1 (by rfl) ⟨443321, by rfl⟩ : syracuseStep 591095 = 886643) B886643
theorem B394503 : Blo 393766 394503 := bstep (se 1 (by rfl) ⟨295877, by rfl⟩ : syracuseStep 394503 = 591755) B591755
theorem B886031 : Blo 393766 886031 := bstep (se 1 (by rfl) ⟨664523, by rfl⟩ : syracuseStep 886031 = 1329047) B1329047
theorem B591119 : Blo 393766 591119 := bstep (se 1 (by rfl) ⟨443339, by rfl⟩ : syracuseStep 591119 = 886679) B886679
theorem B394511 : Blo 393766 394511 := bstep (se 1 (by rfl) ⟨295883, by rfl⟩ : syracuseStep 394511 = 591767) B591767
theorem B886049 : Blo 393766 886049 := bstep (se 2 (by rfl) ⟨332268, by rfl⟩ : syracuseStep 886049 = 664537) B664537
theorem B591161 : Blo 393766 591161 := bstep (se 2 (by rfl) ⟨221685, by rfl⟩ : syracuseStep 591161 = 443371) B443371
theorem B394555 : Blo 393766 394555 := bstep (se 1 (by rfl) ⟨295916, by rfl⟩ : syracuseStep 394555 = 591833) B591833
theorem B591239 : Blo 393766 591239 := bstep (se 1 (by rfl) ⟨443429, by rfl⟩ : syracuseStep 591239 = 886859) B886859
theorem B394631 : Blo 393766 394631 := bstep (se 1 (by rfl) ⟨295973, by rfl⟩ : syracuseStep 394631 = 591947) B591947
theorem B394639 : Blo 393766 394639 := bstep (se 1 (by rfl) ⟨295979, by rfl⟩ : syracuseStep 394639 = 591959) B591959
theorem B591275 : Blo 393766 591275 := bstep (se 1 (by rfl) ⟨443456, by rfl⟩ : syracuseStep 591275 = 886913) B886913
theorem B394683 : Blo 393766 394683 := bstep (se 1 (by rfl) ⟨296012, by rfl⟩ : syracuseStep 394683 = 592025) B592025
theorem B591305 : Blo 393766 591305 := bstep (se 2 (by rfl) ⟨221739, by rfl⟩ : syracuseStep 591305 = 443479) B443479
theorem B394759 : Blo 393766 394759 := bstep (se 1 (by rfl) ⟨296069, by rfl⟩ : syracuseStep 394759 = 592139) B592139
theorem B394767 : Blo 393766 394767 := bstep (se 1 (by rfl) ⟨296075, by rfl⟩ : syracuseStep 394767 = 592151) B592151
theorem B591419 : Blo 393766 591419 := bstep (se 1 (by rfl) ⟨443564, by rfl⟩ : syracuseStep 591419 = 887129) B887129
theorem B394811 : Blo 393766 394811 := bstep (se 1 (by rfl) ⟨296108, by rfl⟩ : syracuseStep 394811 = 592217) B592217
theorem B886391 : Blo 393766 886391 := bstep (se 1 (by rfl) ⟨664793, by rfl⟩ : syracuseStep 886391 = 1329587) B1329587
theorem B591479 : Blo 393766 591479 := bstep (se 1 (by rfl) ⟨443609, by rfl⟩ : syracuseStep 591479 = 887219) B887219
theorem B394887 : Blo 393766 394887 := bstep (se 1 (by rfl) ⟨296165, by rfl⟩ : syracuseStep 394887 = 592331) B592331
theorem B591503 : Blo 393766 591503 := bstep (se 1 (by rfl) ⟨443627, by rfl⟩ : syracuseStep 591503 = 887255) B887255
theorem B394895 : Blo 393766 394895 := bstep (se 1 (by rfl) ⟨296171, by rfl⟩ : syracuseStep 394895 = 592343) B592343
theorem B591545 : Blo 393766 591545 := bstep (se 2 (by rfl) ⟨221829, by rfl⟩ : syracuseStep 591545 = 443659) B443659
theorem B394939 : Blo 393766 394939 := bstep (se 1 (by rfl) ⟨296204, by rfl⟩ : syracuseStep 394939 = 592409) B592409
theorem B591623 : Blo 393766 591623 := bstep (se 1 (by rfl) ⟨443717, by rfl⟩ : syracuseStep 591623 = 887435) B887435
theorem B395015 : Blo 393766 395015 := bstep (se 1 (by rfl) ⟨296261, by rfl⟩ : syracuseStep 395015 = 592523) B592523
theorem B395023 : Blo 393766 395023 := bstep (se 1 (by rfl) ⟨296267, by rfl⟩ : syracuseStep 395023 = 592535) B592535
theorem B886571 : Blo 393766 886571 := bstep (se 1 (by rfl) ⟨664928, by rfl⟩ : syracuseStep 886571 = 1329857) B1329857
theorem B591659 : Blo 393766 591659 := bstep (se 1 (by rfl) ⟨443744, by rfl⟩ : syracuseStep 591659 = 887489) B887489
theorem B395067 : Blo 393766 395067 := bstep (se 1 (by rfl) ⟨296300, by rfl⟩ : syracuseStep 395067 = 592601) B592601
theorem B2000699 : Blo 393766 2000699 := bstep (se 1 (by rfl) ⟨1500524, by rfl⟩ : syracuseStep 2000699 = 3001049) B3001049
theorem B591689 : Blo 393766 591689 := bstep (se 2 (by rfl) ⟨221883, by rfl⟩ : syracuseStep 591689 = 443767) B443767
theorem B395143 : Blo 393766 395143 := bstep (se 1 (by rfl) ⟨296357, by rfl⟩ : syracuseStep 395143 = 592715) B592715
theorem B395151 : Blo 393766 395151 := bstep (se 1 (by rfl) ⟨296363, by rfl⟩ : syracuseStep 395151 = 592727) B592727
theorem B2131865 : Blo 393766 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B3016601 : Blo 393766 3016601 := bstep (se 2 (by rfl) ⟨1131225, by rfl⟩ : syracuseStep 3016601 = 2262451) B2262451
theorem B591803 : Blo 393766 591803 := bstep (se 1 (by rfl) ⟨443852, by rfl⟩ : syracuseStep 591803 = 887705) B887705
theorem B395195 : Blo 393766 395195 := bstep (se 1 (by rfl) ⟨296396, by rfl⟩ : syracuseStep 395195 = 592793) B592793
theorem B2000861 : Blo 393766 2000861 := bstep (se 3 (by rfl) ⟨375161, by rfl⟩ : syracuseStep 2000861 = 750323) B750323
theorem B591863 : Blo 393766 591863 := bstep (se 1 (by rfl) ⟨443897, by rfl⟩ : syracuseStep 591863 = 887795) B887795
theorem B395271 : Blo 393766 395271 := bstep (se 1 (by rfl) ⟨296453, by rfl⟩ : syracuseStep 395271 = 592907) B592907
theorem B591887 : Blo 393766 591887 := bstep (se 1 (by rfl) ⟨443915, by rfl⟩ : syracuseStep 591887 = 887831) B887831
theorem B395279 : Blo 393766 395279 := bstep (se 1 (by rfl) ⟨296459, by rfl⟩ : syracuseStep 395279 = 592919) B592919
theorem B591929 : Blo 393766 591929 := bstep (se 2 (by rfl) ⟨221973, by rfl⟩ : syracuseStep 591929 = 443947) B443947
theorem B395323 : Blo 393766 395323 := bstep (se 1 (by rfl) ⟨296492, by rfl⟩ : syracuseStep 395323 = 592985) B592985
theorem B952435 : Blo 393766 952435 := bstep (se 1 (by rfl) ⟨714326, by rfl⟩ : syracuseStep 952435 = 1428653) B1428653
theorem B592007 : Blo 393766 592007 := bstep (se 1 (by rfl) ⟨444005, by rfl⟩ : syracuseStep 592007 = 888011) B888011
theorem B395399 : Blo 393766 395399 := bstep (se 1 (by rfl) ⟨296549, by rfl⟩ : syracuseStep 395399 = 593099) B593099
theorem B395407 : Blo 393766 395407 := bstep (se 1 (by rfl) ⟨296555, by rfl⟩ : syracuseStep 395407 = 593111) B593111
theorem B886931 : Blo 393766 886931 := bstep (se 1 (by rfl) ⟨665198, by rfl⟩ : syracuseStep 886931 = 1330397) B1330397
theorem B592043 : Blo 393766 592043 := bstep (se 1 (by rfl) ⟨444032, by rfl⟩ : syracuseStep 592043 = 888065) B888065
theorem B395451 : Blo 393766 395451 := bstep (se 1 (by rfl) ⟨296588, by rfl⟩ : syracuseStep 395451 = 593177) B593177
theorem B886985 : Blo 393766 886985 := bstep (se 2 (by rfl) ⟨332619, by rfl⟩ : syracuseStep 886985 = 665239) B665239
theorem B592073 : Blo 393766 592073 := bstep (se 2 (by rfl) ⟨222027, by rfl⟩ : syracuseStep 592073 = 444055) B444055
theorem B1902793 : Blo 393766 1902793 := bstep (se 2 (by rfl) ⟨713547, by rfl⟩ : syracuseStep 1902793 = 1427095) B1427095
theorem B395527 : Blo 393766 395527 := bstep (se 1 (by rfl) ⟨296645, by rfl⟩ : syracuseStep 395527 = 593291) B593291
theorem B395535 : Blo 393766 395535 := bstep (se 1 (by rfl) ⟨296651, by rfl⟩ : syracuseStep 395535 = 593303) B593303
theorem B2001185 : Blo 393766 2001185 := bstep (se 2 (by rfl) ⟨750444, by rfl⟩ : syracuseStep 2001185 = 1500889) B1500889
theorem B592187 : Blo 393766 592187 := bstep (se 1 (by rfl) ⟨444140, by rfl⟩ : syracuseStep 592187 = 888281) B888281
theorem B395579 : Blo 393766 395579 := bstep (se 1 (by rfl) ⟨296684, by rfl⟩ : syracuseStep 395579 = 593369) B593369
theorem B592247 : Blo 393766 592247 := bstep (se 1 (by rfl) ⟨444185, by rfl⟩ : syracuseStep 592247 = 888371) B888371
theorem B2525575 : Blo 393766 2525575 := bstep (se 1 (by rfl) ⟨1894181, by rfl⟩ : syracuseStep 2525575 = 3788363) B3788363
theorem B395655 : Blo 393766 395655 := bstep (se 1 (by rfl) ⟨296741, by rfl⟩ : syracuseStep 395655 = 593483) B593483
theorem B592271 : Blo 393766 592271 := bstep (se 1 (by rfl) ⟨444203, by rfl⟩ : syracuseStep 592271 = 888407) B888407
theorem B395663 : Blo 393766 395663 := bstep (se 1 (by rfl) ⟨296747, by rfl⟩ : syracuseStep 395663 = 593495) B593495
theorem B592313 : Blo 393766 592313 := bstep (se 2 (by rfl) ⟨222117, by rfl⟩ : syracuseStep 592313 = 444235) B444235
theorem B395707 : Blo 393766 395707 := bstep (se 1 (by rfl) ⟨296780, by rfl⟩ : syracuseStep 395707 = 593561) B593561
theorem B592391 : Blo 393766 592391 := bstep (se 1 (by rfl) ⟨444293, by rfl⟩ : syracuseStep 592391 = 888587) B888587
theorem B395783 : Blo 393766 395783 := bstep (se 1 (by rfl) ⟨296837, by rfl⟩ : syracuseStep 395783 = 593675) B593675
theorem B395791 : Blo 393766 395791 := bstep (se 1 (by rfl) ⟨296843, by rfl⟩ : syracuseStep 395791 = 593687) B593687
theorem B592427 : Blo 393766 592427 := bstep (se 1 (by rfl) ⟨444320, by rfl⟩ : syracuseStep 592427 = 888641) B888641
theorem B395835 : Blo 393766 395835 := bstep (se 1 (by rfl) ⟨296876, by rfl⟩ : syracuseStep 395835 = 593753) B593753
theorem B592457 : Blo 393766 592457 := bstep (se 2 (by rfl) ⟨222171, by rfl⟩ : syracuseStep 592457 = 444343) B444343
theorem B395911 : Blo 393766 395911 := bstep (se 1 (by rfl) ⟨296933, by rfl⟩ : syracuseStep 395911 = 593867) B593867
theorem B395919 : Blo 393766 395919 := bstep (se 1 (by rfl) ⟨296939, by rfl⟩ : syracuseStep 395919 = 593879) B593879
theorem B592571 : Blo 393766 592571 := bstep (se 1 (by rfl) ⟨444428, by rfl⟩ : syracuseStep 592571 = 888857) B888857
theorem B395963 : Blo 393766 395963 := bstep (se 1 (by rfl) ⟨296972, by rfl⟩ : syracuseStep 395963 = 593945) B593945
theorem B592631 : Blo 393766 592631 := bstep (se 1 (by rfl) ⟨444473, by rfl⟩ : syracuseStep 592631 = 888947) B888947
theorem B396039 : Blo 393766 396039 := bstep (se 1 (by rfl) ⟨297029, by rfl⟩ : syracuseStep 396039 = 594059) B594059
theorem B592655 : Blo 393766 592655 := bstep (se 1 (by rfl) ⟨444491, by rfl⟩ : syracuseStep 592655 = 888983) B888983
theorem B396047 : Blo 393766 396047 := bstep (se 1 (by rfl) ⟨297035, by rfl⟩ : syracuseStep 396047 = 594071) B594071
theorem B1018639 : Blo 393766 1018639 := bstep (se 1 (by rfl) ⟨763979, by rfl⟩ : syracuseStep 1018639 = 1527959) B1527959
theorem B592697 : Blo 393766 592697 := bstep (se 2 (by rfl) ⟨222261, by rfl⟩ : syracuseStep 592697 = 444523) B444523
theorem B396091 : Blo 393766 396091 := bstep (se 1 (by rfl) ⟨297068, by rfl⟩ : syracuseStep 396091 = 594137) B594137
theorem B887687 : Blo 393766 887687 := bstep (se 1 (by rfl) ⟨665765, by rfl⟩ : syracuseStep 887687 = 1331531) B1331531
theorem B592775 : Blo 393766 592775 := bstep (se 1 (by rfl) ⟨444581, by rfl⟩ : syracuseStep 592775 = 889163) B889163
theorem B396167 : Blo 393766 396167 := bstep (se 1 (by rfl) ⟨297125, by rfl⟩ : syracuseStep 396167 = 594251) B594251
theorem B396175 : Blo 393766 396175 := bstep (se 1 (by rfl) ⟨297131, by rfl⟩ : syracuseStep 396175 = 594263) B594263
theorem B2231185 : Blo 393766 2231185 := bstep (se 2 (by rfl) ⟨836694, by rfl⟩ : syracuseStep 2231185 = 1673389) B1673389
theorem B1084313 : Blo 393766 1084313 := bstep (se 2 (by rfl) ⟨406617, by rfl⟩ : syracuseStep 1084313 = 813235) B813235
theorem B592811 : Blo 393766 592811 := bstep (se 1 (by rfl) ⟨444608, by rfl⟩ : syracuseStep 592811 = 889217) B889217
theorem B396219 : Blo 393766 396219 := bstep (se 1 (by rfl) ⟨297164, by rfl⟩ : syracuseStep 396219 = 594329) B594329
theorem B592841 : Blo 393766 592841 := bstep (se 2 (by rfl) ⟨222315, by rfl⟩ : syracuseStep 592841 = 444631) B444631
theorem B396295 : Blo 393766 396295 := bstep (se 1 (by rfl) ⟨297221, by rfl⟩ : syracuseStep 396295 = 594443) B594443
theorem B396303 : Blo 393766 396303 := bstep (se 1 (by rfl) ⟨297227, by rfl⟩ : syracuseStep 396303 = 594455) B594455
theorem B36637717 : Blo 393766 36637717 := bstep (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) B1717393
theorem B887867 : Blo 393766 887867 := bstep (se 1 (by rfl) ⟨665900, by rfl⟩ : syracuseStep 887867 = 1331801) B1331801
theorem B592955 : Blo 393766 592955 := bstep (se 1 (by rfl) ⟨444716, by rfl⟩ : syracuseStep 592955 = 889433) B889433
theorem B396347 : Blo 393766 396347 := bstep (se 1 (by rfl) ⟨297260, by rfl⟩ : syracuseStep 396347 = 594521) B594521
theorem B593015 : Blo 393766 593015 := bstep (se 1 (by rfl) ⟨444761, by rfl⟩ : syracuseStep 593015 = 889523) B889523
theorem B2264183 : Blo 393766 2264183 := bstep (se 1 (by rfl) ⟨1698137, by rfl⟩ : syracuseStep 2264183 = 3396275) B3396275
theorem B396423 : Blo 393766 396423 := bstep (se 1 (by rfl) ⟨297317, by rfl⟩ : syracuseStep 396423 = 594635) B594635
theorem B593039 : Blo 393766 593039 := bstep (se 1 (by rfl) ⟨444779, by rfl⟩ : syracuseStep 593039 = 889559) B889559
theorem B396431 : Blo 393766 396431 := bstep (se 1 (by rfl) ⟨297323, by rfl⟩ : syracuseStep 396431 = 594647) B594647
theorem B887993 : Blo 393766 887993 := bstep (se 2 (by rfl) ⟨332997, by rfl⟩ : syracuseStep 887993 = 665995) B665995
theorem B593081 : Blo 393766 593081 := bstep (se 2 (by rfl) ⟨222405, by rfl⟩ : syracuseStep 593081 = 444811) B444811
theorem B396475 : Blo 393766 396475 := bstep (se 1 (by rfl) ⟨297356, by rfl⟩ : syracuseStep 396475 = 594713) B594713
theorem B2002157 : Blo 393766 2002157 := bstep (se 3 (by rfl) ⟨375404, by rfl⟩ : syracuseStep 2002157 = 750809) B750809
theorem B593159 : Blo 393766 593159 := bstep (se 1 (by rfl) ⟨444869, by rfl⟩ : syracuseStep 593159 = 889739) B889739
theorem B396551 : Blo 393766 396551 := bstep (se 1 (by rfl) ⟨297413, by rfl⟩ : syracuseStep 396551 = 594827) B594827
theorem B396559 : Blo 393766 396559 := bstep (se 1 (by rfl) ⟨297419, by rfl⟩ : syracuseStep 396559 = 594839) B594839
theorem B593195 : Blo 393766 593195 := bstep (se 1 (by rfl) ⟨444896, by rfl⟩ : syracuseStep 593195 = 889793) B889793
theorem B396603 : Blo 393766 396603 := bstep (se 1 (by rfl) ⟨297452, by rfl⟩ : syracuseStep 396603 = 594905) B594905
theorem B593225 : Blo 393766 593225 := bstep (se 2 (by rfl) ⟨222459, by rfl⟩ : syracuseStep 593225 = 444919) B444919
theorem B2264435 : Blo 393766 2264435 := bstep (se 1 (by rfl) ⟨1698326, by rfl⟩ : syracuseStep 2264435 = 3396653) B3396653
theorem B396679 : Blo 393766 396679 := bstep (se 1 (by rfl) ⟨297509, by rfl⟩ : syracuseStep 396679 = 595019) B595019
theorem B396687 : Blo 393766 396687 := bstep (se 1 (by rfl) ⟨297515, by rfl⟩ : syracuseStep 396687 = 595031) B595031
theorem B593339 : Blo 393766 593339 := bstep (se 1 (by rfl) ⟨445004, by rfl⟩ : syracuseStep 593339 = 890009) B890009
theorem B396731 : Blo 393766 396731 := bstep (se 1 (by rfl) ⟨297548, by rfl⟩ : syracuseStep 396731 = 595097) B595097
theorem B953801 : Blo 393766 953801 := bstep (se 2 (by rfl) ⟨357675, by rfl⟩ : syracuseStep 953801 = 715351) B715351
theorem B593399 : Blo 393766 593399 := bstep (se 1 (by rfl) ⟨445049, by rfl⟩ : syracuseStep 593399 = 890099) B890099
theorem B953857 : Blo 393766 953857 := bstep (se 2 (by rfl) ⟨357696, by rfl⟩ : syracuseStep 953857 = 715393) B715393
theorem B396807 : Blo 393766 396807 := bstep (se 1 (by rfl) ⟨297605, by rfl⟩ : syracuseStep 396807 = 595211) B595211
theorem B888335 : Blo 393766 888335 := bstep (se 1 (by rfl) ⟨666251, by rfl⟩ : syracuseStep 888335 = 1332503) B1332503
theorem B593423 : Blo 393766 593423 := bstep (se 1 (by rfl) ⟨445067, by rfl⟩ : syracuseStep 593423 = 890135) B890135
theorem B396815 : Blo 393766 396815 := bstep (se 1 (by rfl) ⟨297611, by rfl⟩ : syracuseStep 396815 = 595223) B595223
theorem B888353 : Blo 393766 888353 := bstep (se 2 (by rfl) ⟨333132, by rfl⟩ : syracuseStep 888353 = 666265) B666265
theorem B593465 : Blo 393766 593465 := bstep (se 2 (by rfl) ⟨222549, by rfl⟩ : syracuseStep 593465 = 445099) B445099
theorem B396859 : Blo 393766 396859 := bstep (se 1 (by rfl) ⟨297644, by rfl⟩ : syracuseStep 396859 = 595289) B595289
theorem B593543 : Blo 393766 593543 := bstep (se 1 (by rfl) ⟨445157, by rfl⟩ : syracuseStep 593543 = 890315) B890315
theorem B396935 : Blo 393766 396935 := bstep (se 1 (by rfl) ⟨297701, by rfl⟩ : syracuseStep 396935 = 595403) B595403
theorem B396943 : Blo 393766 396943 := bstep (se 1 (by rfl) ⟨297707, by rfl⟩ : syracuseStep 396943 = 595415) B595415
theorem B593579 : Blo 393766 593579 := bstep (se 1 (by rfl) ⟨445184, by rfl⟩ : syracuseStep 593579 = 890369) B890369
theorem B396987 : Blo 393766 396987 := bstep (se 1 (by rfl) ⟨297740, by rfl⟩ : syracuseStep 396987 = 595481) B595481
theorem B1281737 : Blo 393766 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B593609 : Blo 393766 593609 := bstep (se 2 (by rfl) ⟨222603, by rfl⟩ : syracuseStep 593609 = 445207) B445207
theorem B397063 : Blo 393766 397063 := bstep (se 1 (by rfl) ⟨297797, by rfl⟩ : syracuseStep 397063 = 595595) B595595
theorem B397071 : Blo 393766 397071 := bstep (se 1 (by rfl) ⟨297803, by rfl⟩ : syracuseStep 397071 = 595607) B595607
theorem B855841 : Blo 393766 855841 := bstep (se 2 (by rfl) ⟨320940, by rfl⟩ : syracuseStep 855841 = 641881) B641881
theorem B3018545 : Blo 393766 3018545 := bstep (se 2 (by rfl) ⟨1131954, by rfl⟩ : syracuseStep 3018545 = 2263909) B2263909
theorem B593723 : Blo 393766 593723 := bstep (se 1 (by rfl) ⟨445292, by rfl⟩ : syracuseStep 593723 = 890585) B890585
theorem B397115 : Blo 393766 397115 := bstep (se 1 (by rfl) ⟨297836, by rfl⟩ : syracuseStep 397115 = 595673) B595673
theorem B2559833 : Blo 393766 2559833 := bstep (se 2 (by rfl) ⟨959937, by rfl⟩ : syracuseStep 2559833 = 1919875) B1919875
theorem B888695 : Blo 393766 888695 := bstep (se 1 (by rfl) ⟨666521, by rfl⟩ : syracuseStep 888695 = 1333043) B1333043
theorem B593783 : Blo 393766 593783 := bstep (se 1 (by rfl) ⟨445337, by rfl⟩ : syracuseStep 593783 = 890675) B890675
theorem B397191 : Blo 393766 397191 := bstep (se 1 (by rfl) ⟨297893, by rfl⟩ : syracuseStep 397191 = 595787) B595787
theorem B593807 : Blo 393766 593807 := bstep (se 1 (by rfl) ⟨445355, by rfl⟩ : syracuseStep 593807 = 890711) B890711
theorem B397199 : Blo 393766 397199 := bstep (se 1 (by rfl) ⟨297899, by rfl⟩ : syracuseStep 397199 = 595799) B595799
theorem B5476247 : Blo 393766 5476247 := bstep (se 1 (by rfl) ⟨4107185, by rfl⟩ : syracuseStep 5476247 = 8214371) B8214371
theorem B593849 : Blo 393766 593849 := bstep (se 2 (by rfl) ⟨222693, by rfl⟩ : syracuseStep 593849 = 445387) B445387
theorem B397243 : Blo 393766 397243 := bstep (se 1 (by rfl) ⟨297932, by rfl⟩ : syracuseStep 397243 = 595865) B595865
theorem B561097 : Blo 393766 561097 := bstep (se 2 (by rfl) ⟨210411, by rfl⟩ : syracuseStep 561097 = 420823) B420823
theorem B593927 : Blo 393766 593927 := bstep (se 1 (by rfl) ⟨445445, by rfl⟩ : syracuseStep 593927 = 890891) B890891
theorem B397319 : Blo 393766 397319 := bstep (se 1 (by rfl) ⟨297989, by rfl⟩ : syracuseStep 397319 = 595979) B595979
theorem B397327 : Blo 393766 397327 := bstep (se 1 (by rfl) ⟨297995, by rfl⟩ : syracuseStep 397327 = 595991) B595991
theorem B2002967 : Blo 393766 2002967 := bstep (se 1 (by rfl) ⟨1502225, by rfl⟩ : syracuseStep 2002967 = 3004451) B3004451
theorem B888875 : Blo 393766 888875 := bstep (se 1 (by rfl) ⟨666656, by rfl⟩ : syracuseStep 888875 = 1333313) B1333313
theorem B593963 : Blo 393766 593963 := bstep (se 1 (by rfl) ⟨445472, by rfl⟩ : syracuseStep 593963 = 890945) B890945
theorem B397371 : Blo 393766 397371 := bstep (se 1 (by rfl) ⟨298028, by rfl⟩ : syracuseStep 397371 = 596057) B596057
theorem B593993 : Blo 393766 593993 := bstep (se 2 (by rfl) ⟨222747, by rfl⟩ : syracuseStep 593993 = 445495) B445495
theorem B397447 : Blo 393766 397447 := bstep (se 1 (by rfl) ⟨298085, by rfl⟩ : syracuseStep 397447 = 596171) B596171
theorem B397455 : Blo 393766 397455 := bstep (se 1 (by rfl) ⟨298091, by rfl⟩ : syracuseStep 397455 = 596183) B596183
theorem B594107 : Blo 393766 594107 := bstep (se 1 (by rfl) ⟨445580, by rfl⟩ : syracuseStep 594107 = 891161) B891161
theorem B397499 : Blo 393766 397499 := bstep (se 1 (by rfl) ⟨298124, by rfl⟩ : syracuseStep 397499 = 596249) B596249
theorem B594167 : Blo 393766 594167 := bstep (se 1 (by rfl) ⟨445625, by rfl⟩ : syracuseStep 594167 = 891251) B891251
theorem B397575 : Blo 393766 397575 := bstep (se 1 (by rfl) ⟨298181, by rfl⟩ : syracuseStep 397575 = 596363) B596363
theorem B594191 : Blo 393766 594191 := bstep (se 1 (by rfl) ⟨445643, by rfl⟩ : syracuseStep 594191 = 891287) B891287
theorem B397583 : Blo 393766 397583 := bstep (se 1 (by rfl) ⟨298187, by rfl⟩ : syracuseStep 397583 = 596375) B596375
theorem B594233 : Blo 393766 594233 := bstep (se 2 (by rfl) ⟨222837, by rfl⟩ : syracuseStep 594233 = 445675) B445675
theorem B397627 : Blo 393766 397627 := bstep (se 1 (by rfl) ⟨298220, by rfl⟩ : syracuseStep 397627 = 596441) B596441
theorem B594311 : Blo 393766 594311 := bstep (se 1 (by rfl) ⟨445733, by rfl⟩ : syracuseStep 594311 = 891467) B891467
theorem B397703 : Blo 393766 397703 := bstep (se 1 (by rfl) ⟨298277, by rfl⟩ : syracuseStep 397703 = 596555) B596555
theorem B397711 : Blo 393766 397711 := bstep (se 1 (by rfl) ⟨298283, by rfl⟩ : syracuseStep 397711 = 596567) B596567
theorem B889235 : Blo 393766 889235 := bstep (se 1 (by rfl) ⟨666926, by rfl⟩ : syracuseStep 889235 = 1333853) B1333853
theorem B594347 : Blo 393766 594347 := bstep (se 1 (by rfl) ⟨445760, by rfl⟩ : syracuseStep 594347 = 891521) B891521
theorem B397755 : Blo 393766 397755 := bstep (se 1 (by rfl) ⟨298316, by rfl⟩ : syracuseStep 397755 = 596633) B596633
theorem B889289 : Blo 393766 889289 := bstep (se 2 (by rfl) ⟨333483, by rfl⟩ : syracuseStep 889289 = 666967) B666967
theorem B594377 : Blo 393766 594377 := bstep (se 2 (by rfl) ⟨222891, by rfl⟩ : syracuseStep 594377 = 445783) B445783
theorem B594491 : Blo 393766 594491 := bstep (se 1 (by rfl) ⟨445868, by rfl⟩ : syracuseStep 594491 = 891737) B891737
theorem B594551 : Blo 393766 594551 := bstep (se 1 (by rfl) ⟨445913, by rfl⟩ : syracuseStep 594551 = 891827) B891827
theorem B594575 : Blo 393766 594575 := bstep (se 1 (by rfl) ⟨445931, by rfl⟩ : syracuseStep 594575 = 891863) B891863
theorem B594617 : Blo 393766 594617 := bstep (se 2 (by rfl) ⟨222981, by rfl⟩ : syracuseStep 594617 = 445963) B445963
theorem B594695 : Blo 393766 594695 := bstep (se 1 (by rfl) ⟨446021, by rfl⟩ : syracuseStep 594695 = 892043) B892043
theorem B594731 : Blo 393766 594731 := bstep (se 1 (by rfl) ⟨446048, by rfl⟩ : syracuseStep 594731 = 892097) B892097
theorem B594761 : Blo 393766 594761 := bstep (se 2 (by rfl) ⟨223035, by rfl⟩ : syracuseStep 594761 = 446071) B446071
theorem B594875 : Blo 393766 594875 := bstep (se 1 (by rfl) ⟨446156, by rfl⟩ : syracuseStep 594875 = 892313) B892313
theorem B594935 : Blo 393766 594935 := bstep (se 1 (by rfl) ⟨446201, by rfl⟩ : syracuseStep 594935 = 892403) B892403
theorem B594959 : Blo 393766 594959 := bstep (se 1 (by rfl) ⟨446219, by rfl⟩ : syracuseStep 594959 = 892439) B892439
theorem B595001 : Blo 393766 595001 := bstep (se 2 (by rfl) ⟨223125, by rfl⟩ : syracuseStep 595001 = 446251) B446251
theorem B889991 : Blo 393766 889991 := bstep (se 1 (by rfl) ⟨667493, by rfl⟩ : syracuseStep 889991 = 1334987) B1334987
theorem B595079 : Blo 393766 595079 := bstep (se 1 (by rfl) ⟨446309, by rfl⟩ : syracuseStep 595079 = 892619) B892619
theorem B595115 : Blo 393766 595115 := bstep (se 1 (by rfl) ⟨446336, by rfl⟩ : syracuseStep 595115 = 892673) B892673
theorem B595145 : Blo 393766 595145 := bstep (se 2 (by rfl) ⟨223179, by rfl⟩ : syracuseStep 595145 = 446359) B446359
theorem B890171 : Blo 393766 890171 := bstep (se 1 (by rfl) ⟨667628, by rfl⟩ : syracuseStep 890171 = 1335257) B1335257
theorem B595259 : Blo 393766 595259 := bstep (se 1 (by rfl) ⟨446444, by rfl⟩ : syracuseStep 595259 = 892889) B892889
theorem B595319 : Blo 393766 595319 := bstep (se 1 (by rfl) ⟨446489, by rfl⟩ : syracuseStep 595319 = 892979) B892979
theorem B595343 : Blo 393766 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B890297 : Blo 393766 890297 := bstep (se 2 (by rfl) ⟨333861, by rfl⟩ : syracuseStep 890297 = 667723) B667723
theorem B595385 : Blo 393766 595385 := bstep (se 2 (by rfl) ⟨223269, by rfl⟩ : syracuseStep 595385 = 446539) B446539
theorem B595463 : Blo 393766 595463 := bstep (se 1 (by rfl) ⟨446597, by rfl⟩ : syracuseStep 595463 = 893195) B893195
theorem B595499 : Blo 393766 595499 := bstep (se 1 (by rfl) ⟨446624, by rfl⟩ : syracuseStep 595499 = 893249) B893249
theorem B595529 : Blo 393766 595529 := bstep (se 2 (by rfl) ⟨223323, by rfl⟩ : syracuseStep 595529 = 446647) B446647
theorem B595643 : Blo 393766 595643 := bstep (se 1 (by rfl) ⟨446732, by rfl⟩ : syracuseStep 595643 = 893465) B893465
theorem B595703 : Blo 393766 595703 := bstep (se 1 (by rfl) ⟨446777, by rfl⟩ : syracuseStep 595703 = 893555) B893555
theorem B890639 : Blo 393766 890639 := bstep (se 1 (by rfl) ⟨667979, by rfl⟩ : syracuseStep 890639 = 1335959) B1335959
theorem B595727 : Blo 393766 595727 := bstep (se 1 (by rfl) ⟨446795, by rfl⟩ : syracuseStep 595727 = 893591) B893591
theorem B890657 : Blo 393766 890657 := bstep (se 2 (by rfl) ⟨333996, by rfl⟩ : syracuseStep 890657 = 667993) B667993
theorem B595769 : Blo 393766 595769 := bstep (se 2 (by rfl) ⟨223413, by rfl⟩ : syracuseStep 595769 = 446827) B446827
theorem B595847 : Blo 393766 595847 := bstep (se 1 (by rfl) ⟨446885, by rfl⟩ : syracuseStep 595847 = 893771) B893771
theorem B595883 : Blo 393766 595883 := bstep (se 1 (by rfl) ⟨446912, by rfl⟩ : syracuseStep 595883 = 893825) B893825
theorem B595913 : Blo 393766 595913 := bstep (se 2 (by rfl) ⟨223467, by rfl⟩ : syracuseStep 595913 = 446935) B446935
theorem B596027 : Blo 393766 596027 := bstep (se 1 (by rfl) ⟨447020, by rfl⟩ : syracuseStep 596027 = 894041) B894041
theorem B890999 : Blo 393766 890999 := bstep (se 1 (by rfl) ⟨668249, by rfl⟩ : syracuseStep 890999 = 1336499) B1336499
theorem B596087 : Blo 393766 596087 := bstep (se 1 (by rfl) ⟨447065, by rfl⟩ : syracuseStep 596087 = 894131) B894131
theorem B596111 : Blo 393766 596111 := bstep (se 1 (by rfl) ⟨447083, by rfl⟩ : syracuseStep 596111 = 894167) B894167
theorem B596153 : Blo 393766 596153 := bstep (se 2 (by rfl) ⟨223557, by rfl⟩ : syracuseStep 596153 = 447115) B447115
theorem B596231 : Blo 393766 596231 := bstep (se 1 (by rfl) ⟨447173, by rfl⟩ : syracuseStep 596231 = 894347) B894347
theorem B891179 : Blo 393766 891179 := bstep (se 1 (by rfl) ⟨668384, by rfl⟩ : syracuseStep 891179 = 1336769) B1336769
theorem B596267 : Blo 393766 596267 := bstep (se 1 (by rfl) ⟨447200, by rfl⟩ : syracuseStep 596267 = 894401) B894401
theorem B596297 : Blo 393766 596297 := bstep (se 2 (by rfl) ⟨223611, by rfl⟩ : syracuseStep 596297 = 447223) B447223
theorem B596411 : Blo 393766 596411 := bstep (se 1 (by rfl) ⟨447308, by rfl⟩ : syracuseStep 596411 = 894617) B894617
theorem B596471 : Blo 393766 596471 := bstep (se 1 (by rfl) ⟨447353, by rfl⟩ : syracuseStep 596471 = 894707) B894707
theorem B596495 : Blo 393766 596495 := bstep (se 1 (by rfl) ⟨447371, by rfl⟩ : syracuseStep 596495 = 894743) B894743
theorem B596537 : Blo 393766 596537 := bstep (se 2 (by rfl) ⟨223701, by rfl⟩ : syracuseStep 596537 = 447403) B447403
theorem B596615 : Blo 393766 596615 := bstep (se 1 (by rfl) ⟨447461, by rfl⟩ : syracuseStep 596615 = 894923) B894923
theorem B891539 : Blo 393766 891539 := bstep (se 1 (by rfl) ⟨668654, by rfl⟩ : syracuseStep 891539 = 1337309) B1337309
theorem B891593 : Blo 393766 891593 := bstep (se 2 (by rfl) ⟨334347, by rfl⟩ : syracuseStep 891593 = 668695) B668695
theorem B564041 : Blo 393766 564041 := bstep (se 2 (by rfl) ⟨211515, by rfl⟩ : syracuseStep 564041 = 423031) B423031
theorem B498575 : Blo 393766 498575 := bstep (se 1 (by rfl) ⟨373931, by rfl⟩ : syracuseStep 498575 = 747863) B747863
theorem B2399129 : Blo 393766 2399129 := bstep (se 2 (by rfl) ⟨899673, by rfl⟩ : syracuseStep 2399129 = 1799347) B1799347
theorem B2006045 : Blo 393766 2006045 := bstep (se 3 (by rfl) ⟨376133, by rfl⟩ : syracuseStep 2006045 = 752267) B752267
theorem B1121339 : Blo 393766 1121339 := bstep (se 1 (by rfl) ⟨841004, by rfl⟩ : syracuseStep 1121339 = 1682009) B1682009
theorem B1219645 : Blo 393766 1219645 := bstep (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) B457367
theorem B4496471 : Blo 393766 4496471 := bstep (se 1 (by rfl) ⟨3372353, by rfl⟩ : syracuseStep 4496471 = 6744707) B6744707
theorem B1121465 : Blo 393766 1121465 := bstep (se 2 (by rfl) ⟨420549, by rfl⟩ : syracuseStep 1121465 = 841099) B841099
theorem B892295 : Blo 393766 892295 := bstep (se 1 (by rfl) ⟨669221, by rfl⟩ : syracuseStep 892295 = 1338443) B1338443
theorem B2137529 : Blo 393766 2137529 := bstep (se 2 (by rfl) ⟨801573, by rfl⟩ : syracuseStep 2137529 = 1603147) B1603147
theorem B2006531 : Blo 393766 2006531 := bstep (se 1 (by rfl) ⟨1504898, by rfl⟩ : syracuseStep 2006531 = 3009797) B3009797
theorem B892475 : Blo 393766 892475 := bstep (se 1 (by rfl) ⟨669356, by rfl⟩ : syracuseStep 892475 = 1338713) B1338713
theorem B564907 : Blo 393766 564907 := bstep (se 1 (by rfl) ⟨423680, by rfl⟩ : syracuseStep 564907 = 847361) B847361
theorem B892601 : Blo 393766 892601 := bstep (se 2 (by rfl) ⟨334725, by rfl⟩ : syracuseStep 892601 = 669451) B669451
theorem B892943 : Blo 393766 892943 := bstep (se 1 (by rfl) ⟨669707, by rfl⟩ : syracuseStep 892943 = 1339415) B1339415
theorem B892961 : Blo 393766 892961 := bstep (se 2 (by rfl) ⟨334860, by rfl⟩ : syracuseStep 892961 = 669721) B669721
theorem B893303 : Blo 393766 893303 := bstep (se 1 (by rfl) ⟨669977, by rfl⟩ : syracuseStep 893303 = 1339955) B1339955
theorem B893483 : Blo 393766 893483 := bstep (se 1 (by rfl) ⟨670112, by rfl⟩ : syracuseStep 893483 = 1340225) B1340225
theorem B566023 : Blo 393766 566023 := bstep (se 1 (by rfl) ⟨424517, by rfl⟩ : syracuseStep 566023 = 849035) B849035
theorem B1123105 : Blo 393766 1123105 := bstep (se 2 (by rfl) ⟨421164, by rfl⟩ : syracuseStep 1123105 = 842329) B842329
theorem B2433851 : Blo 393766 2433851 := bstep (se 1 (by rfl) ⟨1825388, by rfl⟩ : syracuseStep 2433851 = 3650777) B3650777
theorem B3384179 : Blo 393766 3384179 := bstep (se 1 (by rfl) ⟨2538134, by rfl⟩ : syracuseStep 3384179 = 5076269) B5076269
theorem B893843 : Blo 393766 893843 := bstep (se 1 (by rfl) ⟨670382, by rfl⟩ : syracuseStep 893843 = 1340765) B1340765
theorem B3810199 : Blo 393766 3810199 := bstep (se 1 (by rfl) ⟨2857649, by rfl⟩ : syracuseStep 3810199 = 5715299) B5715299
theorem B893897 : Blo 393766 893897 := bstep (se 2 (by rfl) ⟨335211, by rfl⟩ : syracuseStep 893897 = 670423) B670423
theorem B664591 : Blo 393766 664591 := bstep (se 1 (by rfl) ⟨498443, by rfl⟩ : syracuseStep 664591 = 996887) B996887
theorem B762895 : Blo 393766 762895 := bstep (se 1 (by rfl) ⟨572171, by rfl⟩ : syracuseStep 762895 = 1144343) B1144343
theorem B2008151 : Blo 393766 2008151 := bstep (se 1 (by rfl) ⟨1506113, by rfl⟩ : syracuseStep 2008151 = 3012227) B3012227
theorem B632009 : Blo 393766 632009 := bstep (se 2 (by rfl) ⟨237003, by rfl⟩ : syracuseStep 632009 = 474007) B474007
theorem B1123595 : Blo 393766 1123595 := bstep (se 1 (by rfl) ⟨842696, by rfl⟩ : syracuseStep 1123595 = 1685393) B1685393
theorem B2041139 : Blo 393766 2041139 := bstep (se 1 (by rfl) ⟨1530854, by rfl⟩ : syracuseStep 2041139 = 3061709) B3061709
theorem B4072913 : Blo 393766 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B665131 : Blo 393766 665131 := bstep (se 1 (by rfl) ⟨498848, by rfl⟩ : syracuseStep 665131 = 997697) B997697
theorem B2008637 : Blo 393766 2008637 := bstep (se 3 (by rfl) ⟨376619, by rfl⟩ : syracuseStep 2008637 = 753239) B753239
theorem B894599 : Blo 393766 894599 := bstep (se 1 (by rfl) ⟨670949, by rfl⟩ : syracuseStep 894599 = 1341899) B1341899
theorem B665273 : Blo 393766 665273 := bstep (se 2 (by rfl) ⟨249477, by rfl⟩ : syracuseStep 665273 = 498955) B498955
theorem B501547 : Blo 393766 501547 := bstep (se 1 (by rfl) ⟨376160, by rfl⟩ : syracuseStep 501547 = 752321) B752321
theorem B3811121 : Blo 393766 3811121 := bstep (se 2 (by rfl) ⟨1429170, by rfl⟩ : syracuseStep 3811121 = 2858341) B2858341
theorem B894779 : Blo 393766 894779 := bstep (se 1 (by rfl) ⟨671084, by rfl⟩ : syracuseStep 894779 = 1342169) B1342169
theorem B894905 : Blo 393766 894905 := bstep (se 2 (by rfl) ⟨335589, by rfl⟩ : syracuseStep 894905 = 671179) B671179
theorem B1124381 : Blo 393766 1124381 := bstep (se 3 (by rfl) ⟨210821, by rfl⟩ : syracuseStep 1124381 = 421643) B421643
theorem B632875 : Blo 393766 632875 := bstep (se 1 (by rfl) ⟨474656, by rfl⟩ : syracuseStep 632875 = 949313) B949313
theorem B2992301 : Blo 393766 2992301 := bstep (se 3 (by rfl) ⟨561056, by rfl⟩ : syracuseStep 2992301 = 1122113) B1122113
theorem B665975 : Blo 393766 665975 := bstep (se 1 (by rfl) ⟨499481, by rfl⟩ : syracuseStep 665975 = 998963) B998963
theorem B8530393 : Blo 393766 8530393 := bstep (se 2 (by rfl) ⟨3198897, by rfl⟩ : syracuseStep 8530393 = 6397795) B6397795
theorem B502519 : Blo 393766 502519 := bstep (se 1 (by rfl) ⟨376889, by rfl⟩ : syracuseStep 502519 = 753779) B753779
theorem B666427 : Blo 393766 666427 := bstep (se 1 (by rfl) ⟨499820, by rfl⟩ : syracuseStep 666427 = 999641) B999641
theorem B666569 : Blo 393766 666569 := bstep (se 2 (by rfl) ⟨249963, by rfl⟩ : syracuseStep 666569 = 499927) B499927
theorem B764873 : Blo 393766 764873 := bstep (se 2 (by rfl) ⟨286827, by rfl⟩ : syracuseStep 764873 = 573655) B573655
theorem B502843 : Blo 393766 502843 := bstep (se 1 (by rfl) ⟨377132, by rfl⟩ : syracuseStep 502843 = 754265) B754265
theorem B3386569 : Blo 393766 3386569 := bstep (se 2 (by rfl) ⟨1269963, by rfl⟩ : syracuseStep 3386569 = 2539927) B2539927
theorem B10169549 : Blo 393766 10169549 := bstep (se 3 (by rfl) ⟨1906790, by rfl⟩ : syracuseStep 10169549 = 3813581) B3813581
theorem B2010419 : Blo 393766 2010419 := bstep (se 1 (by rfl) ⟨1507814, by rfl⟩ : syracuseStep 2010419 = 3015629) B3015629
theorem B1420753 : Blo 393766 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B1420811 : Blo 393766 1420811 := bstep (se 1 (by rfl) ⟨1065608, by rfl⟩ : syracuseStep 1420811 = 2131217) B2131217
theorem B2010743 : Blo 393766 2010743 := bstep (se 1 (by rfl) ⟨1508057, by rfl⟩ : syracuseStep 2010743 = 3016115) B3016115
theorem B667271 : Blo 393766 667271 := bstep (se 1 (by rfl) ⟨500453, by rfl⟩ : syracuseStep 667271 = 1000907) B1000907
theorem B569359 : Blo 393766 569359 := bstep (se 1 (by rfl) ⟨427019, by rfl⟩ : syracuseStep 569359 = 854039) B854039
theorem B1126487 : Blo 393766 1126487 := bstep (se 1 (by rfl) ⟨844865, by rfl⟩ : syracuseStep 1126487 = 1689731) B1689731
theorem B667919 : Blo 393766 667919 := bstep (se 1 (by rfl) ⟨500939, by rfl⟩ : syracuseStep 667919 = 1001879) B1001879
theorem B2994731 : Blo 393766 2994731 := bstep (se 1 (by rfl) ⟨2246048, by rfl⟩ : syracuseStep 2994731 = 4492097) B4492097
theorem B1520171 : Blo 393766 1520171 := bstep (se 1 (by rfl) ⟨1140128, by rfl⟩ : syracuseStep 1520171 = 2280257) B2280257
theorem B2011715 : Blo 393766 2011715 := bstep (se 1 (by rfl) ⟨1508786, by rfl⟩ : syracuseStep 2011715 = 3017573) B3017573
theorem B668459 : Blo 393766 668459 := bstep (se 1 (by rfl) ⟨501344, by rfl⟩ : syracuseStep 668459 = 1002689) B1002689
theorem B2012039 : Blo 393766 2012039 := bstep (se 1 (by rfl) ⟨1509029, by rfl⟩ : syracuseStep 2012039 = 3018059) B3018059
theorem B1127353 : Blo 393766 1127353 := bstep (se 2 (by rfl) ⟨422757, by rfl⟩ : syracuseStep 1127353 = 845515) B845515
theorem B668857 : Blo 393766 668857 := bstep (se 2 (by rfl) ⟨250821, by rfl⟩ : syracuseStep 668857 = 501643) B501643
theorem B1127695 : Blo 393766 1127695 := bstep (se 1 (by rfl) ⟨845771, by rfl⟩ : syracuseStep 1127695 = 1691543) B1691543
theorem B1127969 : Blo 393766 1127969 := bstep (se 2 (by rfl) ⟨422988, by rfl⟩ : syracuseStep 1127969 = 845977) B845977
theorem B996907 : Blo 393766 996907 := bstep (se 1 (by rfl) ⟨747680, by rfl⟩ : syracuseStep 996907 = 1495361) B1495361
theorem B997049 : Blo 393766 997049 := bstep (se 2 (by rfl) ⟨373893, by rfl⟩ : syracuseStep 997049 = 747787) B747787
theorem B669559 : Blo 393766 669559 := bstep (se 1 (by rfl) ⟨502169, by rfl⟩ : syracuseStep 669559 = 1004339) B1004339
theorem B3258265 : Blo 393766 3258265 := bstep (se 2 (by rfl) ⟨1221849, by rfl⟩ : syracuseStep 3258265 = 2443699) B2443699
theorem B1423289 : Blo 393766 1423289 := bstep (se 2 (by rfl) ⟨533733, by rfl⟩ : syracuseStep 1423289 = 1067467) B1067467
theorem B1849387 : Blo 393766 1849387 := bstep (se 1 (by rfl) ⟨1387040, by rfl⟩ : syracuseStep 1849387 = 2774081) B2774081
theorem B669755 : Blo 393766 669755 := bstep (se 1 (by rfl) ⟨502316, by rfl⟩ : syracuseStep 669755 = 1004633) B1004633
theorem B1128583 : Blo 393766 1128583 := bstep (se 1 (by rfl) ⟨846437, by rfl⟩ : syracuseStep 1128583 = 1692875) B1692875
theorem B9615761 : Blo 393766 9615761 := bstep (se 2 (by rfl) ⟨3605910, by rfl⟩ : syracuseStep 9615761 = 7211821) B7211821
theorem B670153 : Blo 393766 670153 := bstep (se 2 (by rfl) ⟨251307, by rfl⟩ : syracuseStep 670153 = 502615) B502615
theorem B9583069 : Blo 393766 9583069 := bstep (se 3 (by rfl) ⟨1796825, by rfl⟩ : syracuseStep 9583069 = 3593651) B3593651
theorem B1128971 : Blo 393766 1128971 := bstep (se 1 (by rfl) ⟨846728, by rfl⟩ : syracuseStep 1128971 = 1693457) B1693457
theorem B4569643 : Blo 393766 4569643 := bstep (se 1 (by rfl) ⟨3427232, by rfl⟩ : syracuseStep 4569643 = 6854465) B6854465
theorem B6437495 : Blo 393766 6437495 := bstep (se 1 (by rfl) ⟨4828121, by rfl⟩ : syracuseStep 6437495 = 9656243) B9656243
theorem B998041 : Blo 393766 998041 := bstep (se 2 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 998041 = 748531) B748531
theorem B998203 : Blo 393766 998203 := bstep (se 1 (by rfl) ⟨748652, by rfl⟩ : syracuseStep 998203 = 1497305) B1497305
theorem B1424243 : Blo 393766 1424243 := bstep (se 1 (by rfl) ⟨1068182, by rfl⟩ : syracuseStep 1424243 = 2136365) B2136365
theorem B998345 : Blo 393766 998345 := bstep (se 2 (by rfl) ⟨374379, by rfl⟩ : syracuseStep 998345 = 748759) B748759
theorem B670855 : Blo 393766 670855 := bstep (se 1 (by rfl) ⟨503141, by rfl⟩ : syracuseStep 670855 = 1006283) B1006283
theorem B2538697 : Blo 393766 2538697 := bstep (se 2 (by rfl) ⟨952011, by rfl⟩ : syracuseStep 2538697 = 1904023) B1904023
theorem B998689 : Blo 393766 998689 := bstep (se 2 (by rfl) ⟨374508, by rfl⟩ : syracuseStep 998689 = 749017) B749017
theorem B11124173 : Blo 393766 11124173 := bstep (se 3 (by rfl) ⟨2085782, by rfl⟩ : syracuseStep 11124173 = 4171565) B4171565
theorem B1130269 : Blo 393766 1130269 := bstep (se 3 (by rfl) ⟨211925, by rfl⟩ : syracuseStep 1130269 = 423851) B423851
theorem B966487 : Blo 393766 966487 := bstep (se 1 (by rfl) ⟨724865, by rfl⟩ : syracuseStep 966487 = 1449731) B1449731
theorem B999287 : Blo 393766 999287 := bstep (se 1 (by rfl) ⟨749465, by rfl⟩ : syracuseStep 999287 = 1498931) B1498931
theorem B1130611 : Blo 393766 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B475579 : Blo 393766 475579 := bstep (se 1 (by rfl) ⟨356684, by rfl⟩ : syracuseStep 475579 = 713369) B713369
theorem B3785561 : Blo 393766 3785561 := bstep (se 2 (by rfl) ⟨1419585, by rfl⟩ : syracuseStep 3785561 = 2839171) B2839171
theorem B443407 : Blo 393766 443407 := bstep (se 1 (by rfl) ⟨332555, by rfl⟩ : syracuseStep 443407 = 665111) B665111
theorem B1000583 : Blo 393766 1000583 := bstep (se 1 (by rfl) ⟨750437, by rfl⟩ : syracuseStep 1000583 = 1500875) B1500875
theorem B1000633 : Blo 393766 1000633 := bstep (se 2 (by rfl) ⟨375237, by rfl⟩ : syracuseStep 1000633 = 750475) B750475
theorem B443911 : Blo 393766 443911 := bstep (se 1 (by rfl) ⟨332933, by rfl⟩ : syracuseStep 443911 = 665867) B665867
theorem B2246231 : Blo 393766 2246231 := bstep (se 1 (by rfl) ⟨1684673, by rfl⟩ : syracuseStep 2246231 = 3369347) B3369347
theorem B444091 : Blo 393766 444091 := bstep (se 1 (by rfl) ⟨333068, by rfl⟩ : syracuseStep 444091 = 666137) B666137
theorem B4572929 : Blo 393766 4572929 := bstep (se 2 (by rfl) ⟨1714848, by rfl⟩ : syracuseStep 4572929 = 3429697) B3429697
theorem B1001231 : Blo 393766 1001231 := bstep (se 1 (by rfl) ⟨750923, by rfl⟩ : syracuseStep 1001231 = 1501847) B1501847
theorem B6080305 : Blo 393766 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B3819581 : Blo 393766 3819581 := bstep (se 3 (by rfl) ⟨716171, by rfl⟩ : syracuseStep 3819581 = 1432343) B1432343
theorem B444559 : Blo 393766 444559 := bstep (se 1 (by rfl) ⟨333419, by rfl⟩ : syracuseStep 444559 = 666839) B666839
theorem B477371 : Blo 393766 477371 := bstep (se 1 (by rfl) ⟨358028, by rfl⟩ : syracuseStep 477371 = 716057) B716057
theorem B805135 : Blo 393766 805135 := bstep (se 1 (by rfl) ⟨603851, by rfl⟩ : syracuseStep 805135 = 1207703) B1207703
theorem B1001929 : Blo 393766 1001929 := bstep (se 2 (by rfl) ⟨375723, by rfl⟩ : syracuseStep 1001929 = 751447) B751447
theorem B1690141 : Blo 393766 1690141 := bstep (se 3 (by rfl) ⟨316901, by rfl⟩ : syracuseStep 1690141 = 633803) B633803
theorem B1002071 : Blo 393766 1002071 := bstep (se 1 (by rfl) ⟨751553, by rfl⟩ : syracuseStep 1002071 = 1503107) B1503107
theorem B445063 : Blo 393766 445063 := bstep (se 1 (by rfl) ⟨333797, by rfl⟩ : syracuseStep 445063 = 667595) B667595
theorem B2149037 : Blo 393766 2149037 := bstep (se 3 (by rfl) ⟨402944, by rfl⟩ : syracuseStep 2149037 = 805889) B805889
theorem B445243 : Blo 393766 445243 := bstep (se 1 (by rfl) ⟨333932, by rfl⟩ : syracuseStep 445243 = 667865) B667865
theorem B1690483 : Blo 393766 1690483 := bstep (se 1 (by rfl) ⟨1267862, by rfl⟩ : syracuseStep 1690483 = 2535725) B2535725
theorem B641927 : Blo 393766 641927 := bstep (se 1 (by rfl) ⟨481445, by rfl⟩ : syracuseStep 641927 = 962891) B962891
theorem B1264531 : Blo 393766 1264531 := bstep (se 1 (by rfl) ⟨948398, by rfl⟩ : syracuseStep 1264531 = 1896797) B1896797
theorem B1330073 : Blo 393766 1330073 := bstep (se 2 (by rfl) ⟨498777, by rfl⟩ : syracuseStep 1330073 = 997555) B997555
theorem B9784451 : Blo 393766 9784451 := bstep (se 1 (by rfl) ⟨7338338, by rfl⟩ : syracuseStep 9784451 = 14676677) B14676677
theorem B445711 : Blo 393766 445711 := bstep (se 1 (by rfl) ⟨334283, by rfl⟩ : syracuseStep 445711 = 668567) B668567
theorem B904463 : Blo 393766 904463 := bstep (se 1 (by rfl) ⟨678347, by rfl⟩ : syracuseStep 904463 = 1356695) B1356695
theorem B3820931 : Blo 393766 3820931 := bstep (se 1 (by rfl) ⟨2865698, by rfl⟩ : syracuseStep 3820931 = 5731397) B5731397
theorem B2248145 : Blo 393766 2248145 := bstep (se 2 (by rfl) ⟨843054, by rfl⟩ : syracuseStep 2248145 = 1686109) B1686109
theorem B1330775 : Blo 393766 1330775 := bstep (se 1 (by rfl) ⟨998081, by rfl⟩ : syracuseStep 1330775 = 1996163) B1996163
theorem B446215 : Blo 393766 446215 := bstep (se 1 (by rfl) ⟨334661, by rfl⟩ : syracuseStep 446215 = 669323) B669323
theorem B4050739 : Blo 393766 4050739 := bstep (se 1 (by rfl) ⟨3038054, by rfl⟩ : syracuseStep 4050739 = 6076109) B6076109
theorem B1200025 : Blo 393766 1200025 := bstep (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) B900019
theorem B4509593 : Blo 393766 4509593 := bstep (se 2 (by rfl) ⟨1691097, by rfl⟩ : syracuseStep 4509593 = 3382195) B3382195
theorem B1429433 : Blo 393766 1429433 := bstep (se 2 (by rfl) ⟨536037, by rfl⟩ : syracuseStep 1429433 = 1072075) B1072075
theorem B446395 : Blo 393766 446395 := bstep (se 1 (by rfl) ⟨334796, by rfl⟩ : syracuseStep 446395 = 669593) B669593
theorem B1527761 : Blo 393766 1527761 := bstep (se 2 (by rfl) ⟨572910, by rfl⟩ : syracuseStep 1527761 = 1145821) B1145821
theorem B3821579 : Blo 393766 3821579 := bstep (se 1 (by rfl) ⟨2866184, by rfl⟩ : syracuseStep 3821579 = 5732369) B5732369
theorem B4640813 : Blo 393766 4640813 := bstep (se 3 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 4640813 = 1740305) B1740305
theorem B1331261 : Blo 393766 1331261 := bstep (se 3 (by rfl) ⟨249611, by rfl⟩ : syracuseStep 1331261 = 499223) B499223
theorem B446863 : Blo 393766 446863 := bstep (se 1 (by rfl) ⟨335147, by rfl⟩ : syracuseStep 446863 = 670295) B670295
theorem B18469397 : Blo 393766 18469397 := bstep (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) B865753
theorem B1266263 : Blo 393766 1266263 := bstep (se 1 (by rfl) ⟨949697, by rfl⟩ : syracuseStep 1266263 = 1899395) B1899395
theorem B1004147 : Blo 393766 1004147 := bstep (se 1 (by rfl) ⟨753110, by rfl⟩ : syracuseStep 1004147 = 1506221) B1506221
theorem B447367 : Blo 393766 447367 := bstep (se 1 (by rfl) ⟨335525, by rfl⟩ : syracuseStep 447367 = 671051) B671051
theorem B578603 : Blo 393766 578603 := bstep (se 1 (by rfl) ⟨433952, by rfl⟩ : syracuseStep 578603 = 867905) B867905
theorem B3003479 : Blo 393766 3003479 := bstep (se 1 (by rfl) ⟨2252609, by rfl⟩ : syracuseStep 3003479 = 4505219) B4505219
theorem B1004663 : Blo 393766 1004663 := bstep (se 1 (by rfl) ⟨753497, by rfl⟩ : syracuseStep 1004663 = 1506995) B1506995
theorem B1332665 : Blo 393766 1332665 := bstep (se 2 (by rfl) ⟨499749, by rfl⟩ : syracuseStep 1332665 = 999499) B999499
theorem B4871609 : Blo 393766 4871609 := bstep (se 2 (by rfl) ⟨1826853, by rfl⟩ : syracuseStep 4871609 = 3653707) B3653707
theorem B2840093 : Blo 393766 2840093 := bstep (se 3 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 2840093 = 1065035) B1065035
theorem B710203 : Blo 393766 710203 := bstep (se 1 (by rfl) ⟨532652, by rfl⟩ : syracuseStep 710203 = 1065305) B1065305
theorem B2021267 : Blo 393766 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B7329689 : Blo 393766 7329689 := bstep (se 2 (by rfl) ⟨2748633, by rfl⟩ : syracuseStep 7329689 = 5497267) B5497267
theorem B1333259 : Blo 393766 1333259 := bstep (se 1 (by rfl) ⟨999944, by rfl⟩ : syracuseStep 1333259 = 1999889) B1999889
theorem B1005655 : Blo 393766 1005655 := bstep (se 1 (by rfl) ⟨754241, by rfl⟩ : syracuseStep 1005655 = 1508483) B1508483
theorem B1333367 : Blo 393766 1333367 := bstep (se 1 (by rfl) ⟨1000025, by rfl⟩ : syracuseStep 1333367 = 2000051) B2000051
theorem B1005959 : Blo 393766 1005959 := bstep (se 1 (by rfl) ⟨754469, by rfl⟩ : syracuseStep 1005959 = 1508939) B1508939
theorem B1694105 : Blo 393766 1694105 := bstep (se 2 (by rfl) ⟨635289, by rfl⟩ : syracuseStep 1694105 = 1270579) B1270579
theorem B1006091 : Blo 393766 1006091 := bstep (se 1 (by rfl) ⟨754568, by rfl⟩ : syracuseStep 1006091 = 1509137) B1509137
theorem B1071751 : Blo 393766 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B1333961 : Blo 393766 1333961 := bstep (se 2 (by rfl) ⟨500235, by rfl⟩ : syracuseStep 1333961 = 1000471) B1000471
theorem B1006607 : Blo 393766 1006607 := bstep (se 1 (by rfl) ⟨754955, by rfl⟩ : syracuseStep 1006607 = 1509911) B1509911
theorem B2841733 : Blo 393766 2841733 := bstep (se 4 (by rfl) ⟨266412, by rfl⟩ : syracuseStep 2841733 = 532825) B532825
theorem B1006739 : Blo 393766 1006739 := bstep (se 1 (by rfl) ⟨755054, by rfl⟩ : syracuseStep 1006739 = 1510109) B1510109
theorem B7625933 : Blo 393766 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B1334663 : Blo 393766 1334663 := bstep (se 1 (by rfl) ⟨1000997, by rfl⟩ : syracuseStep 1334663 = 2001995) B2001995
theorem B1007239 : Blo 393766 1007239 := bstep (se 1 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 1007239 = 1510859) B1510859
theorem B1335041 : Blo 393766 1335041 := bstep (se 2 (by rfl) ⟨500640, by rfl⟩ : syracuseStep 1335041 = 1001281) B1001281
theorem B712481 : Blo 393766 712481 := bstep (se 2 (by rfl) ⟨267180, by rfl⟩ : syracuseStep 712481 = 534361) B534361
theorem B2547773 : Blo 393766 2547773 := bstep (se 3 (by rfl) ⟨477707, by rfl⟩ : syracuseStep 2547773 = 955415) B955415
theorem B843977 : Blo 393766 843977 := bstep (se 2 (by rfl) ⟨316491, by rfl⟩ : syracuseStep 843977 = 632983) B632983
theorem B2416841 : Blo 393766 2416841 := bstep (se 2 (by rfl) ⟨906315, by rfl⟩ : syracuseStep 2416841 = 1812631) B1812631
theorem B2253203 : Blo 393766 2253203 := bstep (se 1 (by rfl) ⟨1689902, by rfl⟩ : syracuseStep 2253203 = 3379805) B3379805
theorem B1270169 : Blo 393766 1270169 := bstep (se 2 (by rfl) ⟨476313, by rfl⟩ : syracuseStep 1270169 = 952627) B952627
theorem B1335851 : Blo 393766 1335851 := bstep (se 1 (by rfl) ⟨1001888, by rfl⟩ : syracuseStep 1335851 = 2003777) B2003777
theorem B1499735 : Blo 393766 1499735 := bstep (se 1 (by rfl) ⟨1124801, by rfl⟩ : syracuseStep 1499735 = 2249603) B2249603
theorem B1270529 : Blo 393766 1270529 := bstep (se 2 (by rfl) ⟨476448, by rfl⟩ : syracuseStep 1270529 = 952897) B952897
theorem B2253703 : Blo 393766 2253703 := bstep (se 1 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 2253703 = 3380555) B3380555
theorem B713657 : Blo 393766 713657 := bstep (se 2 (by rfl) ⟨267621, by rfl⟩ : syracuseStep 713657 = 535243) B535243
theorem B34366517 : Blo 393766 34366517 := bstep (se 5 (by rfl) ⟨1610930, by rfl⟩ : syracuseStep 34366517 = 3221861) B3221861
theorem B1500221 : Blo 393766 1500221 := bstep (se 3 (by rfl) ⟨281291, by rfl⟩ : syracuseStep 1500221 = 562583) B562583
theorem B2417957 : Blo 393766 2417957 := bstep (se 4 (by rfl) ⟨226683, by rfl⟩ : syracuseStep 2417957 = 453367) B453367
theorem B1697233 : Blo 393766 1697233 := bstep (se 2 (by rfl) ⟨636462, by rfl⟩ : syracuseStep 1697233 = 1272925) B1272925
theorem B1631981 : Blo 393766 1631981 := bstep (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) B611993
theorem B1337147 : Blo 393766 1337147 := bstep (se 1 (by rfl) ⟨1002860, by rfl⟩ : syracuseStep 1337147 = 2005721) B2005721
theorem B2582387 : Blo 393766 2582387 := bstep (se 1 (by rfl) ⟨1936790, by rfl⟩ : syracuseStep 2582387 = 3873581) B3873581
theorem B1075079 : Blo 393766 1075079 := bstep (se 1 (by rfl) ⟨806309, by rfl⟩ : syracuseStep 1075079 = 1612619) B1612619
theorem B4646807 : Blo 393766 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B5433389 : Blo 393766 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B2844733 : Blo 393766 2844733 := bstep (se 3 (by rfl) ⟨533387, by rfl⟩ : syracuseStep 2844733 = 1066775) B1066775
theorem B6514805 : Blo 393766 6514805 := bstep (se 5 (by rfl) ⟨305381, by rfl⟩ : syracuseStep 6514805 = 610763) B610763
theorem B845959 : Blo 393766 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B3467501 : Blo 393766 3467501 := bstep (se 3 (by rfl) ⟨650156, by rfl⟩ : syracuseStep 3467501 = 1300313) B1300313
theorem B1337633 : Blo 393766 1337633 := bstep (se 2 (by rfl) ⟨501612, by rfl⟩ : syracuseStep 1337633 = 1003225) B1003225
theorem B1501649 : Blo 393766 1501649 := bstep (se 2 (by rfl) ⟨563118, by rfl⟩ : syracuseStep 1501649 = 1126237) B1126237
theorem B748091 : Blo 393766 748091 := bstep (se 1 (by rfl) ⟨561068, by rfl⟩ : syracuseStep 748091 = 1122137) B1122137
theorem B1338227 : Blo 393766 1338227 := bstep (se 1 (by rfl) ⟨1003670, by rfl⟩ : syracuseStep 1338227 = 2007341) B2007341
theorem B1797011 : Blo 393766 1797011 := bstep (se 1 (by rfl) ⟨1347758, by rfl⟩ : syracuseStep 1797011 = 2695517) B2695517
theorem B748577 : Blo 393766 748577 := bstep (se 2 (by rfl) ⟨280716, by rfl⟩ : syracuseStep 748577 = 561433) B561433
theorem B1010873 : Blo 393766 1010873 := bstep (se 2 (by rfl) ⟨379077, by rfl⟩ : syracuseStep 1010873 = 758155) B758155
theorem B748919 : Blo 393766 748919 := bstep (se 1 (by rfl) ⟨561689, by rfl⟩ : syracuseStep 748919 = 1123379) B1123379
theorem B3206621 : Blo 393766 3206621 := bstep (se 3 (by rfl) ⟨601241, by rfl⟩ : syracuseStep 3206621 = 1202483) B1202483
theorem B2289239 : Blo 393766 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B421519 : Blo 393766 421519 := bstep (se 1 (by rfl) ⟨316139, by rfl⟩ : syracuseStep 421519 = 632279) B632279
theorem B4321073 : Blo 393766 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B1994705 : Blo 393766 1994705 := bstep (se 2 (by rfl) ⟨748014, by rfl⟩ : syracuseStep 1994705 = 1496029) B1496029
theorem B421895 : Blo 393766 421895 := bstep (se 1 (by rfl) ⟨316421, by rfl⟩ : syracuseStep 421895 = 632843) B632843
theorem B1503319 : Blo 393766 1503319 := bstep (se 1 (by rfl) ⟨1127489, by rfl⟩ : syracuseStep 1503319 = 2254979) B2254979
theorem B1503623 : Blo 393766 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B1208711 : Blo 393766 1208711 := bstep (se 1 (by rfl) ⟨906533, by rfl⟩ : syracuseStep 1208711 = 1813067) B1813067
theorem B1602109 : Blo 393766 1602109 := bstep (se 3 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 1602109 = 600791) B600791
theorem B1503805 : Blo 393766 1503805 := bstep (se 3 (by rfl) ⟨281963, by rfl⟩ : syracuseStep 1503805 = 563927) B563927
theorem B64713329 : Blo 393766 64713329 := bstep (se 2 (by rfl) ⟨24267498, by rfl⟩ : syracuseStep 64713329 = 48534997) B48534997
theorem B422587 : Blo 393766 422587 := bstep (se 1 (by rfl) ⟨316940, by rfl⟩ : syracuseStep 422587 = 633881) B633881
theorem B750521 : Blo 393766 750521 := bstep (se 2 (by rfl) ⟨281445, by rfl⟩ : syracuseStep 750521 = 562891) B562891
theorem B4813829 : Blo 393766 4813829 := bstep (se 4 (by rfl) ⟨451296, by rfl⟩ : syracuseStep 4813829 = 902593) B902593
theorem B816143 : Blo 393766 816143 := bstep (se 1 (by rfl) ⟨612107, by rfl⟩ : syracuseStep 816143 = 1224215) B1224215
theorem B947467 : Blo 393766 947467 := bstep (se 1 (by rfl) ⟨710600, by rfl⟩ : syracuseStep 947467 = 1421201) B1421201
theorem B750863 : Blo 393766 750863 := bstep (se 1 (by rfl) ⟨563147, by rfl⟩ : syracuseStep 750863 = 1126295) B1126295
theorem B8516897 : Blo 393766 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B1340819 : Blo 393766 1340819 := bstep (se 1 (by rfl) ⟨1005614, by rfl⟩ : syracuseStep 1340819 = 2011229) B2011229
theorem B11401073 : Blo 393766 11401073 := bstep (se 2 (by rfl) ⟨4275402, by rfl⟩ : syracuseStep 11401073 = 8550805) B8550805
theorem B1603475 : Blo 393766 1603475 := bstep (se 1 (by rfl) ⟨1202606, by rfl⟩ : syracuseStep 1603475 = 2405213) B2405213
theorem B1996811 : Blo 393766 1996811 := bstep (se 1 (by rfl) ⟨1497608, by rfl⟩ : syracuseStep 1996811 = 2995217) B2995217
theorem B751675 : Blo 393766 751675 := bstep (se 1 (by rfl) ⟨563756, by rfl⟩ : syracuseStep 751675 = 1127513) B1127513
theorem B1538135 : Blo 393766 1538135 := bstep (se 1 (by rfl) ⟨1153601, by rfl⟩ : syracuseStep 1538135 = 2307203) B2307203
theorem B751751 : Blo 393766 751751 := bstep (se 1 (by rfl) ⟨563813, by rfl⟩ : syracuseStep 751751 = 1127627) B1127627
theorem B1996973 : Blo 393766 1996973 := bstep (se 3 (by rfl) ⟨374432, by rfl⟩ : syracuseStep 1996973 = 748865) B748865
theorem B1505537 : Blo 393766 1505537 := bstep (se 2 (by rfl) ⟨564576, by rfl⟩ : syracuseStep 1505537 = 1129153) B1129153
theorem B3373447 : Blo 393766 3373447 := bstep (se 1 (by rfl) ⟨2530085, by rfl⟩ : syracuseStep 3373447 = 5060171) B5060171
theorem B2259353 : Blo 393766 2259353 := bstep (se 2 (by rfl) ⟨847257, by rfl⟩ : syracuseStep 2259353 = 1694515) B1694515
theorem B752161 : Blo 393766 752161 := bstep (se 2 (by rfl) ⟨282060, by rfl⟩ : syracuseStep 752161 = 564121) B564121
theorem B4487723 : Blo 393766 4487723 := bstep (se 1 (by rfl) ⟨3365792, by rfl⟩ : syracuseStep 4487723 = 6731585) B6731585
theorem B948851 : Blo 393766 948851 := bstep (se 1 (by rfl) ⟨711638, by rfl⟩ : syracuseStep 948851 = 1423277) B1423277
theorem B3439297 : Blo 393766 3439297 := bstep (se 2 (by rfl) ⟨1289736, by rfl⟩ : syracuseStep 3439297 = 2579473) B2579473
theorem B1342223 : Blo 393766 1342223 := bstep (se 1 (by rfl) ⟨1006667, by rfl⟩ : syracuseStep 1342223 = 2013335) B2013335
theorem B752503 : Blo 393766 752503 := bstep (se 1 (by rfl) ⟨564377, by rfl⟩ : syracuseStep 752503 = 1128755) B1128755
theorem B1899911 : Blo 393766 1899911 := bstep (se 1 (by rfl) ⟨1424933, by rfl⟩ : syracuseStep 1899911 = 2849867) B2849867
theorem B1506707 : Blo 393766 1506707 := bstep (se 1 (by rfl) ⟨1130030, by rfl⟩ : syracuseStep 1506707 = 2260061) B2260061
theorem B1146569 : Blo 393766 1146569 := bstep (se 2 (by rfl) ⟨429963, by rfl⟩ : syracuseStep 1146569 = 859927) B859927
theorem B1998593 : Blo 393766 1998593 := bstep (se 2 (by rfl) ⟨749472, by rfl⟩ : syracuseStep 1998593 = 1498945) B1498945
theorem B1507207 : Blo 393766 1507207 := bstep (se 1 (by rfl) ⟨1130405, by rfl⟩ : syracuseStep 1507207 = 2260811) B2260811
theorem B12058571 : Blo 393766 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B1507481 : Blo 393766 1507481 := bstep (se 2 (by rfl) ⟨565305, by rfl⟩ : syracuseStep 1507481 = 1130611) B1130611
theorem B393767 : Blo 393766 393767 := bstep (se 1 (by rfl) ⟨295325, by rfl⟩ : syracuseStep 393767 = 590651) B590651
theorem B2523707 : Blo 393766 2523707 := bstep (se 1 (by rfl) ⟨1892780, by rfl⟩ : syracuseStep 2523707 = 3785561) B3785561
theorem B393807 : Blo 393766 393807 := bstep (se 1 (by rfl) ⟨295355, by rfl⟩ : syracuseStep 393807 = 590711) B590711
theorem B393823 : Blo 393766 393823 := bstep (se 1 (by rfl) ⟨295367, by rfl⟩ : syracuseStep 393823 = 590735) B590735
theorem B393851 : Blo 393766 393851 := bstep (se 1 (by rfl) ⟨295388, by rfl⟩ : syracuseStep 393851 = 590777) B590777
theorem B721531 : Blo 393766 721531 := bstep (se 1 (by rfl) ⟨541148, by rfl⟩ : syracuseStep 721531 = 1082297) B1082297
theorem B393903 : Blo 393766 393903 := bstep (se 1 (by rfl) ⟨295427, by rfl⟩ : syracuseStep 393903 = 590855) B590855
theorem B393927 : Blo 393766 393927 := bstep (se 1 (by rfl) ⟨295445, by rfl⟩ : syracuseStep 393927 = 590891) B590891
theorem B393947 : Blo 393766 393947 := bstep (se 1 (by rfl) ⟨295460, by rfl⟩ : syracuseStep 393947 = 590921) B590921
theorem B394023 : Blo 393766 394023 := bstep (se 1 (by rfl) ⟨295517, by rfl⟩ : syracuseStep 394023 = 591035) B591035
theorem B394063 : Blo 393766 394063 := bstep (se 1 (by rfl) ⟨295547, by rfl⟩ : syracuseStep 394063 = 591095) B591095
theorem B590687 : Blo 393766 590687 := bstep (se 1 (by rfl) ⟨443015, by rfl⟩ : syracuseStep 590687 = 886031) B886031
theorem B394079 : Blo 393766 394079 := bstep (se 1 (by rfl) ⟨295559, by rfl⟩ : syracuseStep 394079 = 591119) B591119
theorem B590699 : Blo 393766 590699 := bstep (se 1 (by rfl) ⟨443024, by rfl⟩ : syracuseStep 590699 = 886049) B886049
theorem B394107 : Blo 393766 394107 := bstep (se 1 (by rfl) ⟨295580, by rfl⟩ : syracuseStep 394107 = 591161) B591161
theorem B394159 : Blo 393766 394159 := bstep (se 1 (by rfl) ⟨295619, by rfl⟩ : syracuseStep 394159 = 591239) B591239
theorem B394183 : Blo 393766 394183 := bstep (se 1 (by rfl) ⟨295637, by rfl⟩ : syracuseStep 394183 = 591275) B591275
theorem B394203 : Blo 393766 394203 := bstep (se 1 (by rfl) ⟨295652, by rfl⟩ : syracuseStep 394203 = 591305) B591305
theorem B754697 : Blo 393766 754697 := bstep (se 2 (by rfl) ⟨283011, by rfl⟩ : syracuseStep 754697 = 566023) B566023
theorem B394279 : Blo 393766 394279 := bstep (se 1 (by rfl) ⟨295709, by rfl⟩ : syracuseStep 394279 = 591419) B591419
theorem B590927 : Blo 393766 590927 := bstep (se 1 (by rfl) ⟨443195, by rfl⟩ : syracuseStep 590927 = 886391) B886391
theorem B394319 : Blo 393766 394319 := bstep (se 1 (by rfl) ⟨295739, by rfl⟩ : syracuseStep 394319 = 591479) B591479
theorem B394335 : Blo 393766 394335 := bstep (se 1 (by rfl) ⟨295751, by rfl⟩ : syracuseStep 394335 = 591503) B591503
theorem B394363 : Blo 393766 394363 := bstep (se 1 (by rfl) ⟨295772, by rfl⟩ : syracuseStep 394363 = 591545) B591545
theorem B3048619 : Blo 393766 3048619 := bstep (se 1 (by rfl) ⟨2286464, by rfl⟩ : syracuseStep 3048619 = 4572929) B4572929
theorem B394415 : Blo 393766 394415 := bstep (se 1 (by rfl) ⟨295811, by rfl⟩ : syracuseStep 394415 = 591623) B591623
theorem B591047 : Blo 393766 591047 := bstep (se 1 (by rfl) ⟨443285, by rfl⟩ : syracuseStep 591047 = 886571) B886571
theorem B394439 : Blo 393766 394439 := bstep (se 1 (by rfl) ⟨295829, by rfl⟩ : syracuseStep 394439 = 591659) B591659
theorem B5080265 : Blo 393766 5080265 := bstep (se 2 (by rfl) ⟨1905099, by rfl⟩ : syracuseStep 5080265 = 3810199) B3810199
theorem B394459 : Blo 393766 394459 := bstep (se 1 (by rfl) ⟨295844, by rfl⟩ : syracuseStep 394459 = 591689) B591689
theorem B394535 : Blo 393766 394535 := bstep (se 1 (by rfl) ⟨295901, by rfl⟩ : syracuseStep 394535 = 591803) B591803
theorem B394575 : Blo 393766 394575 := bstep (se 1 (by rfl) ⟨295931, by rfl⟩ : syracuseStep 394575 = 591863) B591863
theorem B394591 : Blo 393766 394591 := bstep (se 1 (by rfl) ⟨295943, by rfl⟩ : syracuseStep 394591 = 591887) B591887
theorem B886121 : Blo 393766 886121 := bstep (se 2 (by rfl) ⟨332295, by rfl⟩ : syracuseStep 886121 = 664591) B664591
theorem B591209 : Blo 393766 591209 := bstep (se 2 (by rfl) ⟨221703, by rfl⟩ : syracuseStep 591209 = 443407) B443407
theorem B1017193 : Blo 393766 1017193 := bstep (se 2 (by rfl) ⟨381447, by rfl⟩ : syracuseStep 1017193 = 762895) B762895
theorem B394619 : Blo 393766 394619 := bstep (se 1 (by rfl) ⟨295964, by rfl⟩ : syracuseStep 394619 = 591929) B591929
theorem B394671 : Blo 393766 394671 := bstep (se 1 (by rfl) ⟨296003, by rfl⟩ : syracuseStep 394671 = 592007) B592007
theorem B591287 : Blo 393766 591287 := bstep (se 1 (by rfl) ⟨443465, by rfl⟩ : syracuseStep 591287 = 886931) B886931
theorem B394695 : Blo 393766 394695 := bstep (se 1 (by rfl) ⟨296021, by rfl⟩ : syracuseStep 394695 = 592043) B592043
theorem B591323 : Blo 393766 591323 := bstep (se 1 (by rfl) ⟨443492, by rfl⟩ : syracuseStep 591323 = 886985) B886985
theorem B394715 : Blo 393766 394715 := bstep (se 1 (by rfl) ⟨296036, by rfl⟩ : syracuseStep 394715 = 592073) B592073
theorem B394791 : Blo 393766 394791 := bstep (se 1 (by rfl) ⟨296093, by rfl⟩ : syracuseStep 394791 = 592187) B592187
theorem B394831 : Blo 393766 394831 := bstep (se 1 (by rfl) ⟨296123, by rfl⟩ : syracuseStep 394831 = 592247) B592247
theorem B394847 : Blo 393766 394847 := bstep (se 1 (by rfl) ⟨296135, by rfl⟩ : syracuseStep 394847 = 592271) B592271
theorem B394875 : Blo 393766 394875 := bstep (se 1 (by rfl) ⟨296156, by rfl⟩ : syracuseStep 394875 = 592313) B592313
theorem B394927 : Blo 393766 394927 := bstep (se 1 (by rfl) ⟨296195, by rfl⟩ : syracuseStep 394927 = 592391) B592391
theorem B394951 : Blo 393766 394951 := bstep (se 1 (by rfl) ⟨296213, by rfl⟩ : syracuseStep 394951 = 592427) B592427
theorem B394971 : Blo 393766 394971 := bstep (se 1 (by rfl) ⟨296228, by rfl⟩ : syracuseStep 394971 = 592457) B592457
theorem B395047 : Blo 393766 395047 := bstep (se 1 (by rfl) ⟨296285, by rfl⟩ : syracuseStep 395047 = 592571) B592571
theorem B395087 : Blo 393766 395087 := bstep (se 1 (by rfl) ⟨296315, by rfl⟩ : syracuseStep 395087 = 592631) B592631
theorem B395103 : Blo 393766 395103 := bstep (se 1 (by rfl) ⟨296327, by rfl⟩ : syracuseStep 395103 = 592655) B592655
theorem B395131 : Blo 393766 395131 := bstep (se 1 (by rfl) ⟨296348, by rfl⟩ : syracuseStep 395131 = 592697) B592697
theorem B591791 : Blo 393766 591791 := bstep (se 1 (by rfl) ⟨443843, by rfl⟩ : syracuseStep 591791 = 887687) B887687
theorem B395183 : Blo 393766 395183 := bstep (se 1 (by rfl) ⟨296387, by rfl⟩ : syracuseStep 395183 = 592775) B592775
theorem B427951 : Blo 393766 427951 := bstep (se 1 (by rfl) ⟨320963, by rfl⟩ : syracuseStep 427951 = 641927) B641927
theorem B886715 : Blo 393766 886715 := bstep (se 1 (by rfl) ⟨665036, by rfl⟩ : syracuseStep 886715 = 1330073) B1330073
theorem B722875 : Blo 393766 722875 := bstep (se 1 (by rfl) ⟨542156, by rfl⟩ : syracuseStep 722875 = 1084313) B1084313
theorem B2262977 : Blo 393766 2262977 := bstep (se 2 (by rfl) ⟨848616, by rfl⟩ : syracuseStep 2262977 = 1697233) B1697233
theorem B395207 : Blo 393766 395207 := bstep (se 1 (by rfl) ⟨296405, by rfl⟩ : syracuseStep 395207 = 592811) B592811
theorem B395227 : Blo 393766 395227 := bstep (se 1 (by rfl) ⟨296420, by rfl⟩ : syracuseStep 395227 = 592841) B592841
theorem B591881 : Blo 393766 591881 := bstep (se 2 (by rfl) ⟨221955, by rfl⟩ : syracuseStep 591881 = 443911) B443911
theorem B591911 : Blo 393766 591911 := bstep (se 1 (by rfl) ⟨443933, by rfl⟩ : syracuseStep 591911 = 887867) B887867
theorem B395303 : Blo 393766 395303 := bstep (se 1 (by rfl) ⟨296477, by rfl⟩ : syracuseStep 395303 = 592955) B592955
theorem B886841 : Blo 393766 886841 := bstep (se 2 (by rfl) ⟨332565, by rfl⟩ : syracuseStep 886841 = 665131) B665131
theorem B395343 : Blo 393766 395343 := bstep (se 1 (by rfl) ⟨296507, by rfl⟩ : syracuseStep 395343 = 593015) B593015
theorem B1509455 : Blo 393766 1509455 := bstep (se 1 (by rfl) ⟨1132091, by rfl⟩ : syracuseStep 1509455 = 2264183) B2264183
theorem B6522967 : Blo 393766 6522967 := bstep (se 1 (by rfl) ⟨4892225, by rfl⟩ : syracuseStep 6522967 = 9784451) B9784451
theorem B395359 : Blo 393766 395359 := bstep (se 1 (by rfl) ⟨296519, by rfl⟩ : syracuseStep 395359 = 593039) B593039
theorem B591995 : Blo 393766 591995 := bstep (se 1 (by rfl) ⟨443996, by rfl⟩ : syracuseStep 591995 = 887993) B887993
theorem B395387 : Blo 393766 395387 := bstep (se 1 (by rfl) ⟨296540, by rfl⟩ : syracuseStep 395387 = 593081) B593081
theorem B395439 : Blo 393766 395439 := bstep (se 1 (by rfl) ⟨296579, by rfl⟩ : syracuseStep 395439 = 593159) B593159
theorem B395463 : Blo 393766 395463 := bstep (se 1 (by rfl) ⟨296597, by rfl⟩ : syracuseStep 395463 = 593195) B593195
theorem B395483 : Blo 393766 395483 := bstep (se 1 (by rfl) ⟨296612, by rfl⟩ : syracuseStep 395483 = 593225) B593225
theorem B1509623 : Blo 393766 1509623 := bstep (se 1 (by rfl) ⟨1132217, by rfl⟩ : syracuseStep 1509623 = 2264435) B2264435
theorem B592121 : Blo 393766 592121 := bstep (se 2 (by rfl) ⟨222045, by rfl⟩ : syracuseStep 592121 = 444091) B444091
theorem B395559 : Blo 393766 395559 := bstep (se 1 (by rfl) ⟨296669, by rfl⟩ : syracuseStep 395559 = 593339) B593339
theorem B395599 : Blo 393766 395599 := bstep (se 1 (by rfl) ⟨296699, by rfl⟩ : syracuseStep 395599 = 593399) B593399
theorem B592223 : Blo 393766 592223 := bstep (se 1 (by rfl) ⟨444167, by rfl⟩ : syracuseStep 592223 = 888335) B888335
theorem B395615 : Blo 393766 395615 := bstep (se 1 (by rfl) ⟨296711, by rfl⟩ : syracuseStep 395615 = 593423) B593423
theorem B592235 : Blo 393766 592235 := bstep (se 1 (by rfl) ⟨444176, by rfl⟩ : syracuseStep 592235 = 888353) B888353
theorem B395643 : Blo 393766 395643 := bstep (se 1 (by rfl) ⟨296732, by rfl⟩ : syracuseStep 395643 = 593465) B593465
theorem B887183 : Blo 393766 887183 := bstep (se 1 (by rfl) ⟨665387, by rfl⟩ : syracuseStep 887183 = 1330775) B1330775
theorem B395695 : Blo 393766 395695 := bstep (se 1 (by rfl) ⟨296771, by rfl⟩ : syracuseStep 395695 = 593543) B593543
theorem B395719 : Blo 393766 395719 := bstep (se 1 (by rfl) ⟨296789, by rfl⟩ : syracuseStep 395719 = 593579) B593579
theorem B854491 : Blo 393766 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B395739 : Blo 393766 395739 := bstep (se 1 (by rfl) ⟨296804, by rfl⟩ : syracuseStep 395739 = 593609) B593609
theorem B1903085 : Blo 393766 1903085 := bstep (se 3 (by rfl) ⟨356828, by rfl⟩ : syracuseStep 1903085 = 713657) B713657
theorem B395815 : Blo 393766 395815 := bstep (se 1 (by rfl) ⟨296861, by rfl⟩ : syracuseStep 395815 = 593723) B593723
theorem B1706555 : Blo 393766 1706555 := bstep (se 1 (by rfl) ⟨1279916, by rfl⟩ : syracuseStep 1706555 = 2559833) B2559833
theorem B592463 : Blo 393766 592463 := bstep (se 1 (by rfl) ⟨444347, by rfl⟩ : syracuseStep 592463 = 888695) B888695
theorem B395855 : Blo 393766 395855 := bstep (se 1 (by rfl) ⟨296891, by rfl⟩ : syracuseStep 395855 = 593783) B593783
theorem B395871 : Blo 393766 395871 := bstep (se 1 (by rfl) ⟨296903, by rfl⟩ : syracuseStep 395871 = 593807) B593807
theorem B395899 : Blo 393766 395899 := bstep (se 1 (by rfl) ⟨296924, by rfl⟩ : syracuseStep 395899 = 593849) B593849
theorem B952955 : Blo 393766 952955 := bstep (se 1 (by rfl) ⟨714716, by rfl⟩ : syracuseStep 952955 = 1429433) B1429433
theorem B1018507 : Blo 393766 1018507 := bstep (se 1 (by rfl) ⟨763880, by rfl⟩ : syracuseStep 1018507 = 1527761) B1527761
theorem B395951 : Blo 393766 395951 := bstep (se 1 (by rfl) ⟨296963, by rfl⟩ : syracuseStep 395951 = 593927) B593927
theorem B592583 : Blo 393766 592583 := bstep (se 1 (by rfl) ⟨444437, by rfl⟩ : syracuseStep 592583 = 888875) B888875
theorem B395975 : Blo 393766 395975 := bstep (se 1 (by rfl) ⟨296981, by rfl⟩ : syracuseStep 395975 = 593963) B593963
theorem B887507 : Blo 393766 887507 := bstep (se 1 (by rfl) ⟨665630, by rfl⟩ : syracuseStep 887507 = 1331261) B1331261
theorem B395995 : Blo 393766 395995 := bstep (se 1 (by rfl) ⟨296996, by rfl⟩ : syracuseStep 395995 = 593993) B593993
theorem B1542941 : Blo 393766 1542941 := bstep (se 3 (by rfl) ⟨289301, by rfl⟩ : syracuseStep 1542941 = 578603) B578603
theorem B396071 : Blo 393766 396071 := bstep (se 1 (by rfl) ⟨297053, by rfl⟩ : syracuseStep 396071 = 594107) B594107
theorem B396111 : Blo 393766 396111 := bstep (se 1 (by rfl) ⟨297083, by rfl⟩ : syracuseStep 396111 = 594167) B594167
theorem B396127 : Blo 393766 396127 := bstep (se 1 (by rfl) ⟨297095, by rfl⟩ : syracuseStep 396127 = 594191) B594191
theorem B592745 : Blo 393766 592745 := bstep (se 2 (by rfl) ⟨222279, by rfl⟩ : syracuseStep 592745 = 444559) B444559
theorem B396155 : Blo 393766 396155 := bstep (se 1 (by rfl) ⟨297116, by rfl⟩ : syracuseStep 396155 = 594233) B594233
theorem B396207 : Blo 393766 396207 := bstep (se 1 (by rfl) ⟨297155, by rfl⟩ : syracuseStep 396207 = 594311) B594311
theorem B592823 : Blo 393766 592823 := bstep (se 1 (by rfl) ⟨444617, by rfl⟩ : syracuseStep 592823 = 889235) B889235
theorem B396231 : Blo 393766 396231 := bstep (se 1 (by rfl) ⟨297173, by rfl⟩ : syracuseStep 396231 = 594347) B594347
theorem B592859 : Blo 393766 592859 := bstep (se 1 (by rfl) ⟨444644, by rfl⟩ : syracuseStep 592859 = 889289) B889289
theorem B396251 : Blo 393766 396251 := bstep (se 1 (by rfl) ⟨297188, by rfl⟩ : syracuseStep 396251 = 594377) B594377
theorem B396327 : Blo 393766 396327 := bstep (se 1 (by rfl) ⟨297245, by rfl⟩ : syracuseStep 396327 = 594491) B594491
theorem B396367 : Blo 393766 396367 := bstep (se 1 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 396367 = 594551) B594551
theorem B396383 : Blo 393766 396383 := bstep (se 1 (by rfl) ⟨297287, by rfl⟩ : syracuseStep 396383 = 594575) B594575
theorem B396411 : Blo 393766 396411 := bstep (se 1 (by rfl) ⟨297308, by rfl⟩ : syracuseStep 396411 = 594617) B594617
theorem B396463 : Blo 393766 396463 := bstep (se 1 (by rfl) ⟨297347, by rfl⟩ : syracuseStep 396463 = 594695) B594695
theorem B396487 : Blo 393766 396487 := bstep (se 1 (by rfl) ⟨297365, by rfl⟩ : syracuseStep 396487 = 594731) B594731
theorem B396507 : Blo 393766 396507 := bstep (se 1 (by rfl) ⟨297380, by rfl⟩ : syracuseStep 396507 = 594761) B594761
theorem B11373857 : Blo 393766 11373857 := bstep (se 2 (by rfl) ⟨4265196, by rfl⟩ : syracuseStep 11373857 = 8530393) B8530393
theorem B396583 : Blo 393766 396583 := bstep (se 1 (by rfl) ⟨297437, by rfl⟩ : syracuseStep 396583 = 594875) B594875
theorem B396623 : Blo 393766 396623 := bstep (se 1 (by rfl) ⟨297467, by rfl⟩ : syracuseStep 396623 = 594935) B594935
theorem B396639 : Blo 393766 396639 := bstep (se 1 (by rfl) ⟨297479, by rfl⟩ : syracuseStep 396639 = 594959) B594959
theorem B396667 : Blo 393766 396667 := bstep (se 1 (by rfl) ⟨297500, by rfl⟩ : syracuseStep 396667 = 595001) B595001
theorem B2002319 : Blo 393766 2002319 := bstep (se 1 (by rfl) ⟨1501739, by rfl⟩ : syracuseStep 2002319 = 3003479) B3003479
theorem B593327 : Blo 393766 593327 := bstep (se 1 (by rfl) ⟨444995, by rfl⟩ : syracuseStep 593327 = 889991) B889991
theorem B396719 : Blo 393766 396719 := bstep (se 1 (by rfl) ⟨297539, by rfl⟩ : syracuseStep 396719 = 595079) B595079
theorem B396743 : Blo 393766 396743 := bstep (se 1 (by rfl) ⟨297557, by rfl⟩ : syracuseStep 396743 = 595115) B595115
theorem B396763 : Blo 393766 396763 := bstep (se 1 (by rfl) ⟨297572, by rfl⟩ : syracuseStep 396763 = 595145) B595145
theorem B593417 : Blo 393766 593417 := bstep (se 2 (by rfl) ⟨222531, by rfl⟩ : syracuseStep 593417 = 445063) B445063
theorem B593447 : Blo 393766 593447 := bstep (se 1 (by rfl) ⟨445085, by rfl⟩ : syracuseStep 593447 = 890171) B890171
theorem B396839 : Blo 393766 396839 := bstep (se 1 (by rfl) ⟨297629, by rfl⟩ : syracuseStep 396839 = 595259) B595259
theorem B396879 : Blo 393766 396879 := bstep (se 1 (by rfl) ⟨297659, by rfl⟩ : syracuseStep 396879 = 595319) B595319
theorem B396895 : Blo 393766 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B888443 : Blo 393766 888443 := bstep (se 1 (by rfl) ⟨666332, by rfl⟩ : syracuseStep 888443 = 1332665) B1332665
theorem B3247739 : Blo 393766 3247739 := bstep (se 1 (by rfl) ⟨2435804, by rfl⟩ : syracuseStep 3247739 = 4871609) B4871609
theorem B593531 : Blo 393766 593531 := bstep (se 1 (by rfl) ⟨445148, by rfl⟩ : syracuseStep 593531 = 890297) B890297
theorem B396923 : Blo 393766 396923 := bstep (se 1 (by rfl) ⟨297692, by rfl⟩ : syracuseStep 396923 = 595385) B595385
theorem B396975 : Blo 393766 396975 := bstep (se 1 (by rfl) ⟨297731, by rfl⟩ : syracuseStep 396975 = 595463) B595463
theorem B396999 : Blo 393766 396999 := bstep (se 1 (by rfl) ⟨297749, by rfl⟩ : syracuseStep 396999 = 595499) B595499
theorem B397019 : Blo 393766 397019 := bstep (se 1 (by rfl) ⟨297764, by rfl⟩ : syracuseStep 397019 = 595529) B595529
theorem B888569 : Blo 393766 888569 := bstep (se 2 (by rfl) ⟨333213, by rfl⟩ : syracuseStep 888569 = 666427) B666427
theorem B593657 : Blo 393766 593657 := bstep (se 2 (by rfl) ⟨222621, by rfl⟩ : syracuseStep 593657 = 445243) B445243
theorem B397095 : Blo 393766 397095 := bstep (se 1 (by rfl) ⟨297821, by rfl⟩ : syracuseStep 397095 = 595643) B595643
theorem B397135 : Blo 393766 397135 := bstep (se 1 (by rfl) ⟨297851, by rfl⟩ : syracuseStep 397135 = 595703) B595703
theorem B593759 : Blo 393766 593759 := bstep (se 1 (by rfl) ⟨445319, by rfl⟩ : syracuseStep 593759 = 890639) B890639
theorem B397151 : Blo 393766 397151 := bstep (se 1 (by rfl) ⟨297863, by rfl⟩ : syracuseStep 397151 = 595727) B595727
theorem B593771 : Blo 393766 593771 := bstep (se 1 (by rfl) ⟨445328, by rfl⟩ : syracuseStep 593771 = 890657) B890657
theorem B397179 : Blo 393766 397179 := bstep (se 1 (by rfl) ⟨297884, by rfl⟩ : syracuseStep 397179 = 595769) B595769
theorem B397231 : Blo 393766 397231 := bstep (se 1 (by rfl) ⟨297923, by rfl⟩ : syracuseStep 397231 = 595847) B595847
theorem B1347511 : Blo 393766 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B4886459 : Blo 393766 4886459 := bstep (se 1 (by rfl) ⟨3664844, by rfl⟩ : syracuseStep 4886459 = 7329689) B7329689
theorem B397255 : Blo 393766 397255 := bstep (se 1 (by rfl) ⟨297941, by rfl⟩ : syracuseStep 397255 = 595883) B595883
theorem B397275 : Blo 393766 397275 := bstep (se 1 (by rfl) ⟨297956, by rfl⟩ : syracuseStep 397275 = 595913) B595913
theorem B888839 : Blo 393766 888839 := bstep (se 1 (by rfl) ⟨666629, by rfl⟩ : syracuseStep 888839 = 1333259) B1333259
theorem B397351 : Blo 393766 397351 := bstep (se 1 (by rfl) ⟨298013, by rfl⟩ : syracuseStep 397351 = 596027) B596027
theorem B888911 : Blo 393766 888911 := bstep (se 1 (by rfl) ⟨666683, by rfl⟩ : syracuseStep 888911 = 1333367) B1333367
theorem B593999 : Blo 393766 593999 := bstep (se 1 (by rfl) ⟨445499, by rfl⟩ : syracuseStep 593999 = 890999) B890999
theorem B397391 : Blo 393766 397391 := bstep (se 1 (by rfl) ⟨298043, by rfl⟩ : syracuseStep 397391 = 596087) B596087
theorem B397407 : Blo 393766 397407 := bstep (se 1 (by rfl) ⟨298055, by rfl⟩ : syracuseStep 397407 = 596111) B596111
theorem B397435 : Blo 393766 397435 := bstep (se 1 (by rfl) ⟨298076, by rfl⟩ : syracuseStep 397435 = 596153) B596153
theorem B397487 : Blo 393766 397487 := bstep (se 1 (by rfl) ⟨298115, by rfl⟩ : syracuseStep 397487 = 596231) B596231
theorem B594119 : Blo 393766 594119 := bstep (se 1 (by rfl) ⟨445589, by rfl⟩ : syracuseStep 594119 = 891179) B891179
theorem B397511 : Blo 393766 397511 := bstep (se 1 (by rfl) ⟨298133, by rfl⟩ : syracuseStep 397511 = 596267) B596267
theorem B397531 : Blo 393766 397531 := bstep (se 1 (by rfl) ⟨298148, by rfl⟩ : syracuseStep 397531 = 596297) B596297
theorem B397607 : Blo 393766 397607 := bstep (se 1 (by rfl) ⟨298205, by rfl⟩ : syracuseStep 397607 = 596411) B596411
theorem B397647 : Blo 393766 397647 := bstep (se 1 (by rfl) ⟨298235, by rfl⟩ : syracuseStep 397647 = 596471) B596471
theorem B397663 : Blo 393766 397663 := bstep (se 1 (by rfl) ⟨298247, by rfl⟩ : syracuseStep 397663 = 596495) B596495
theorem B594281 : Blo 393766 594281 := bstep (se 2 (by rfl) ⟨222855, by rfl⟩ : syracuseStep 594281 = 445711) B445711
theorem B397691 : Blo 393766 397691 := bstep (se 1 (by rfl) ⟨298268, by rfl⟩ : syracuseStep 397691 = 596537) B596537
theorem B397743 : Blo 393766 397743 := bstep (se 1 (by rfl) ⟨298307, by rfl⟩ : syracuseStep 397743 = 596615) B596615
theorem B594359 : Blo 393766 594359 := bstep (se 1 (by rfl) ⟨445769, by rfl⟩ : syracuseStep 594359 = 891539) B891539
theorem B889307 : Blo 393766 889307 := bstep (se 1 (by rfl) ⟨666980, by rfl⟩ : syracuseStep 889307 = 1333961) B1333961
theorem B594395 : Blo 393766 594395 := bstep (se 1 (by rfl) ⟨445796, by rfl⟩ : syracuseStep 594395 = 891593) B891593
theorem B5083955 : Blo 393766 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B562025 : Blo 393766 562025 := bstep (se 2 (by rfl) ⟨210759, by rfl⟩ : syracuseStep 562025 = 421519) B421519
theorem B889775 : Blo 393766 889775 := bstep (se 1 (by rfl) ⟨667331, by rfl⟩ : syracuseStep 889775 = 1334663) B1334663
theorem B594863 : Blo 393766 594863 := bstep (se 1 (by rfl) ⟨446147, by rfl⟩ : syracuseStep 594863 = 892295) B892295
theorem B594953 : Blo 393766 594953 := bstep (se 2 (by rfl) ⟨223107, by rfl⟩ : syracuseStep 594953 = 446215) B446215
theorem B594983 : Blo 393766 594983 := bstep (se 1 (by rfl) ⟨446237, by rfl⟩ : syracuseStep 594983 = 892475) B892475
theorem B595067 : Blo 393766 595067 := bstep (se 1 (by rfl) ⟨446300, by rfl⟩ : syracuseStep 595067 = 892601) B892601
theorem B890027 : Blo 393766 890027 := bstep (se 1 (by rfl) ⟨667520, by rfl⟩ : syracuseStep 890027 = 1335041) B1335041
theorem B595193 : Blo 393766 595193 := bstep (se 2 (by rfl) ⟨223197, by rfl⟩ : syracuseStep 595193 = 446395) B446395
theorem B595295 : Blo 393766 595295 := bstep (se 1 (by rfl) ⟨446471, by rfl⟩ : syracuseStep 595295 = 892943) B892943
theorem B759145 : Blo 393766 759145 := bstep (se 2 (by rfl) ⟨284679, by rfl⟩ : syracuseStep 759145 = 569359) B569359
theorem B595307 : Blo 393766 595307 := bstep (se 1 (by rfl) ⟨446480, by rfl⟩ : syracuseStep 595307 = 892961) B892961
theorem B2004425 : Blo 393766 2004425 := bstep (se 2 (by rfl) ⟨751659, by rfl⟩ : syracuseStep 2004425 = 1503319) B1503319
theorem B1611227 : Blo 393766 1611227 := bstep (se 1 (by rfl) ⟨1208420, by rfl⟩ : syracuseStep 1611227 = 2416841) B2416841
theorem B595535 : Blo 393766 595535 := bstep (se 1 (by rfl) ⟨446651, by rfl⟩ : syracuseStep 595535 = 893303) B893303
theorem B890567 : Blo 393766 890567 := bstep (se 1 (by rfl) ⟨667925, by rfl⟩ : syracuseStep 890567 = 1335851) B1335851
theorem B595655 : Blo 393766 595655 := bstep (se 1 (by rfl) ⟨446741, by rfl⟩ : syracuseStep 595655 = 893483) B893483
theorem B595817 : Blo 393766 595817 := bstep (se 2 (by rfl) ⟨223431, by rfl⟩ : syracuseStep 595817 = 446863) B446863
theorem B595895 : Blo 393766 595895 := bstep (se 1 (by rfl) ⟨446921, by rfl⟩ : syracuseStep 595895 = 893843) B893843
theorem B595931 : Blo 393766 595931 := bstep (se 1 (by rfl) ⟨446948, by rfl⟩ : syracuseStep 595931 = 893897) B893897
theorem B22911011 : Blo 393766 22911011 := bstep (se 1 (by rfl) ⟨17183258, by rfl⟩ : syracuseStep 22911011 = 34366517) B34366517
theorem B2136145 : Blo 393766 2136145 := bstep (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) B1602109
theorem B2005073 : Blo 393766 2005073 := bstep (se 2 (by rfl) ⟨751902, by rfl⟩ : syracuseStep 2005073 = 1503805) B1503805
theorem B1611971 : Blo 393766 1611971 := bstep (se 1 (by rfl) ⟨1208978, by rfl⟩ : syracuseStep 1611971 = 2417957) B2417957
theorem B563449 : Blo 393766 563449 := bstep (se 2 (by rfl) ⟨211293, by rfl⟩ : syracuseStep 563449 = 422587) B422587
theorem B596399 : Blo 393766 596399 := bstep (se 1 (by rfl) ⟨447299, by rfl⟩ : syracuseStep 596399 = 894599) B894599
theorem B1087987 : Blo 393766 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B596489 : Blo 393766 596489 := bstep (se 2 (by rfl) ⟨223683, by rfl⟩ : syracuseStep 596489 = 447367) B447367
theorem B891431 : Blo 393766 891431 := bstep (se 1 (by rfl) ⟨668573, by rfl⟩ : syracuseStep 891431 = 1337147) B1337147
theorem B596519 : Blo 393766 596519 := bstep (se 1 (by rfl) ⟨447389, by rfl⟩ : syracuseStep 596519 = 894779) B894779
theorem B596603 : Blo 393766 596603 := bstep (se 1 (by rfl) ⟨447452, by rfl⟩ : syracuseStep 596603 = 894905) B894905
theorem B891755 : Blo 393766 891755 := bstep (se 1 (by rfl) ⟨668816, by rfl⟩ : syracuseStep 891755 = 1337633) B1337633
theorem B891809 : Blo 393766 891809 := bstep (se 2 (by rfl) ⟨334428, by rfl⟩ : syracuseStep 891809 = 668857) B668857
theorem B498727 : Blo 393766 498727 := bstep (se 1 (by rfl) ⟨374045, by rfl⟩ : syracuseStep 498727 = 748091) B748091
theorem B892151 : Blo 393766 892151 := bstep (se 1 (by rfl) ⟨669113, by rfl⟩ : syracuseStep 892151 = 1338227) B1338227
theorem B499051 : Blo 393766 499051 := bstep (se 1 (by rfl) ⟨374288, by rfl⟩ : syracuseStep 499051 = 748577) B748577
theorem B499279 : Blo 393766 499279 := bstep (se 1 (by rfl) ⟨374459, by rfl⟩ : syracuseStep 499279 = 748919) B748919
theorem B2137747 : Blo 393766 2137747 := bstep (se 1 (by rfl) ⟨1603310, by rfl⟩ : syracuseStep 2137747 = 3206621) B3206621
theorem B892745 : Blo 393766 892745 := bstep (se 2 (by rfl) ⟨334779, by rfl⟩ : syracuseStep 892745 = 669559) B669559
theorem B2465849 : Blo 393766 2465849 := bstep (se 2 (by rfl) ⟨924693, by rfl⟩ : syracuseStep 2465849 = 1849387) B1849387
theorem B4497929 : Blo 393766 4497929 := bstep (se 2 (by rfl) ⟨1686723, by rfl⟩ : syracuseStep 4497929 = 3373447) B3373447
theorem B893537 : Blo 393766 893537 := bstep (se 2 (by rfl) ⟨335076, by rfl⟩ : syracuseStep 893537 = 670153) B670153
theorem B500347 : Blo 393766 500347 := bstep (se 1 (by rfl) ⟨375260, by rfl⟩ : syracuseStep 500347 = 750521) B750521
theorem B500575 : Blo 393766 500575 := bstep (se 1 (by rfl) ⟨375431, by rfl⟩ : syracuseStep 500575 = 750863) B750863
theorem B5677931 : Blo 393766 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B893879 : Blo 393766 893879 := bstep (se 1 (by rfl) ⟨670409, by rfl⟩ : syracuseStep 893879 = 1340819) B1340819
theorem B664699 : Blo 393766 664699 := bstep (se 1 (by rfl) ⟨498524, by rfl⟩ : syracuseStep 664699 = 997049) B997049
theorem B29664461 : Blo 393766 29664461 := bstep (se 3 (by rfl) ⟨5562086, by rfl⟩ : syracuseStep 29664461 = 11124173) B11124173
theorem B1025423 : Blo 393766 1025423 := bstep (se 1 (by rfl) ⟨769067, by rfl⟩ : syracuseStep 1025423 = 1538135) B1538135
theorem B501167 : Blo 393766 501167 := bstep (se 1 (by rfl) ⟨375875, by rfl⟩ : syracuseStep 501167 = 751751) B751751
theorem B894473 : Blo 393766 894473 := bstep (se 2 (by rfl) ⟨335427, by rfl⟩ : syracuseStep 894473 = 670855) B670855
theorem B3384929 : Blo 393766 3384929 := bstep (se 2 (by rfl) ⟨1269348, by rfl⟩ : syracuseStep 3384929 = 2538697) B2538697
theorem B2991815 : Blo 393766 2991815 := bstep (se 1 (by rfl) ⟨2243861, by rfl⟩ : syracuseStep 2991815 = 4487723) B4487723
theorem B632567 : Blo 393766 632567 := bstep (se 1 (by rfl) ⟨474425, by rfl⟩ : syracuseStep 632567 = 948851) B948851
theorem B894815 : Blo 393766 894815 := bstep (se 1 (by rfl) ⟨671111, by rfl⟩ : syracuseStep 894815 = 1342223) B1342223
theorem B3057517 : Blo 393766 3057517 := bstep (se 3 (by rfl) ⟨573284, by rfl⟩ : syracuseStep 3057517 = 1146569) B1146569
theorem B665563 : Blo 393766 665563 := bstep (se 1 (by rfl) ⟨499172, by rfl⟩ : syracuseStep 665563 = 998345) B998345
theorem B6400133 : Blo 393766 6400133 := bstep (se 4 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 6400133 = 1200025) B1200025
theorem B1288649 : Blo 393766 1288649 := bstep (se 2 (by rfl) ⟨483243, by rfl⟩ : syracuseStep 1288649 = 966487) B966487
theorem B2009609 : Blo 393766 2009609 := bstep (se 2 (by rfl) ⟨753603, by rfl⟩ : syracuseStep 2009609 = 1507207) B1507207
theorem B32156189 : Blo 393766 32156189 := bstep (se 3 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 32156189 = 12058571) B12058571
theorem B666191 : Blo 393766 666191 := bstep (se 1 (by rfl) ⟨499643, by rfl⟩ : syracuseStep 666191 = 999287) B999287
theorem B1125053 : Blo 393766 1125053 := bstep (se 3 (by rfl) ⟨210947, by rfl⟩ : syracuseStep 1125053 = 421895) B421895
theorem B3058505 : Blo 393766 3058505 := bstep (se 2 (by rfl) ⟨1146939, by rfl⟩ : syracuseStep 3058505 = 2293879) B2293879
theorem B634105 : Blo 393766 634105 := bstep (se 2 (by rfl) ⟨237789, by rfl⟩ : syracuseStep 634105 = 475579) B475579
theorem B667055 : Blo 393766 667055 := bstep (se 1 (by rfl) ⟨500291, by rfl⟩ : syracuseStep 667055 = 1000583) B1000583
theorem B4107763 : Blo 393766 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B667487 : Blo 393766 667487 := bstep (se 1 (by rfl) ⟨500615, by rfl⟩ : syracuseStep 667487 = 1001231) B1001231
theorem B1421243 : Blo 393766 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B2011067 : Blo 393766 2011067 := bstep (se 1 (by rfl) ⟨1508300, by rfl⟩ : syracuseStep 2011067 = 3016601) B3016601
theorem B668047 : Blo 393766 668047 := bstep (se 1 (by rfl) ⟨501035, by rfl⟩ : syracuseStep 668047 = 1002071) B1002071
theorem B602975 : Blo 393766 602975 := bstep (se 1 (by rfl) ⟨452231, by rfl⟩ : syracuseStep 602975 = 904463) B904463
theorem B635867 : Blo 393766 635867 := bstep (se 1 (by rfl) ⟨476900, by rfl⟩ : syracuseStep 635867 = 953801) B953801
theorem B668729 : Blo 393766 668729 := bstep (se 2 (by rfl) ⟨250773, by rfl⟩ : syracuseStep 668729 = 501547) B501547
theorem B8107073 : Blo 393766 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B2012363 : Blo 393766 2012363 := bstep (se 1 (by rfl) ⟨1509272, by rfl⟩ : syracuseStep 2012363 = 3018545) B3018545
theorem B3650831 : Blo 393766 3650831 := bstep (se 1 (by rfl) ⟨2738123, by rfl⟩ : syracuseStep 3650831 = 5476247) B5476247
theorem B3093875 : Blo 393766 3093875 := bstep (se 1 (by rfl) ⟨2320406, by rfl⟩ : syracuseStep 3093875 = 4640813) B4640813
theorem B2536829 : Blo 393766 2536829 := bstep (se 3 (by rfl) ⟨475655, by rfl⟩ : syracuseStep 2536829 = 951311) B951311
theorem B2176381 : Blo 393766 2176381 := bstep (se 3 (by rfl) ⟨408071, by rfl⟩ : syracuseStep 2176381 = 816143) B816143
theorem B1127945 : Blo 393766 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B2537057 : Blo 393766 2537057 := bstep (se 2 (by rfl) ⟨951396, by rfl⟩ : syracuseStep 2537057 = 1902793) B1902793
theorem B669431 : Blo 393766 669431 := bstep (se 1 (by rfl) ⟨502073, by rfl⟩ : syracuseStep 669431 = 1004147) B1004147
theorem B1685357 : Blo 393766 1685357 := bstep (se 3 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 1685357 = 632009) B632009
theorem B669775 : Blo 393766 669775 := bstep (se 1 (by rfl) ⟨502331, by rfl⟩ : syracuseStep 669775 = 1004663) B1004663
theorem B670025 : Blo 393766 670025 := bstep (se 2 (by rfl) ⟨251259, by rfl⟩ : syracuseStep 670025 = 502519) B502519
theorem B1686041 : Blo 393766 1686041 := bstep (se 2 (by rfl) ⟨632265, by rfl⟩ : syracuseStep 1686041 = 1264531) B1264531
theorem B670457 : Blo 393766 670457 := bstep (se 2 (by rfl) ⟨251421, by rfl⟩ : syracuseStep 670457 = 502843) B502843
theorem B670639 : Blo 393766 670639 := bstep (se 1 (by rfl) ⟨502979, by rfl⟩ : syracuseStep 670639 = 1005959) B1005959
theorem B1129403 : Blo 393766 1129403 := bstep (se 1 (by rfl) ⟨847052, by rfl⟩ : syracuseStep 1129403 = 1694105) B1694105
theorem B670727 : Blo 393766 670727 := bstep (se 1 (by rfl) ⟨503045, by rfl⟩ : syracuseStep 670727 = 1006091) B1006091
theorem B671071 : Blo 393766 671071 := bstep (se 1 (by rfl) ⟨503303, by rfl⟩ : syracuseStep 671071 = 1006607) B1006607
theorem B2997647 : Blo 393766 2997647 := bstep (se 1 (by rfl) ⟨2248235, by rfl⟩ : syracuseStep 2997647 = 4496471) B4496471
theorem B671159 : Blo 393766 671159 := bstep (se 1 (by rfl) ⟨503369, by rfl⟩ : syracuseStep 671159 = 1006739) B1006739
theorem B1425019 : Blo 393766 1425019 := bstep (se 1 (by rfl) ⟨1068764, by rfl⟩ : syracuseStep 1425019 = 2137529) B2137529
theorem B2866877 : Blo 393766 2866877 := bstep (se 3 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 2866877 = 1075079) B1075079
theorem B999823 : Blo 393766 999823 := bstep (se 1 (by rfl) ⟨749867, by rfl⟩ : syracuseStep 999823 = 1499735) B1499735
theorem B1622567 : Blo 393766 1622567 := bstep (se 1 (by rfl) ⟨1216925, by rfl⟩ : syracuseStep 1622567 = 2433851) B2433851
theorem B15155909 : Blo 393766 15155909 := bstep (se 4 (by rfl) ⟨1420866, by rfl⟩ : syracuseStep 15155909 = 2841733) B2841733
theorem B1000147 : Blo 393766 1000147 := bstep (se 1 (by rfl) ⟨750110, by rfl⟩ : syracuseStep 1000147 = 1500221) B1500221
theorem B1360759 : Blo 393766 1360759 := bstep (se 1 (by rfl) ⟨1020569, by rfl⟩ : syracuseStep 1360759 = 2041139) B2041139
theorem B443515 : Blo 393766 443515 := bstep (se 1 (by rfl) ⟨332636, by rfl⟩ : syracuseStep 443515 = 665273) B665273
theorem B2540747 : Blo 393766 2540747 := bstep (se 1 (by rfl) ⟨1905560, by rfl⟩ : syracuseStep 2540747 = 3811121) B3811121
theorem B1721591 : Blo 393766 1721591 := bstep (se 1 (by rfl) ⟨1291193, by rfl⟩ : syracuseStep 1721591 = 2582387) B2582387
theorem B3097871 : Blo 393766 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B3622259 : Blo 393766 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B4343203 : Blo 393766 4343203 := bstep (se 1 (by rfl) ⟨3257402, by rfl⟩ : syracuseStep 4343203 = 6514805) B6514805
theorem B2311667 : Blo 393766 2311667 := bstep (se 1 (by rfl) ⟨1733750, by rfl⟩ : syracuseStep 2311667 = 3467501) B3467501
theorem B443983 : Blo 393766 443983 := bstep (se 1 (by rfl) ⟨332987, by rfl⟩ : syracuseStep 443983 = 665975) B665975
theorem B1001099 : Blo 393766 1001099 := bstep (se 1 (by rfl) ⟨750824, by rfl⟩ : syracuseStep 1001099 = 1501649) B1501649
theorem B1263289 : Blo 393766 1263289 := bstep (se 2 (by rfl) ⟨473733, by rfl⟩ : syracuseStep 1263289 = 947467) B947467
theorem B1198007 : Blo 393766 1198007 := bstep (se 1 (by rfl) ⟨898505, by rfl⟩ : syracuseStep 1198007 = 1797011) B1797011
theorem B444379 : Blo 393766 444379 := bstep (se 1 (by rfl) ⟨333284, by rfl⟩ : syracuseStep 444379 = 666569) B666569
theorem B509915 : Blo 393766 509915 := bstep (se 1 (by rfl) ⟨382436, by rfl⟩ : syracuseStep 509915 = 764873) B764873
theorem B1329209 : Blo 393766 1329209 := bstep (se 2 (by rfl) ⟨498453, by rfl⟩ : syracuseStep 1329209 = 996907) B996907
theorem B673915 : Blo 393766 673915 := bstep (se 1 (by rfl) ⟨505436, by rfl⟩ : syracuseStep 673915 = 1010873) B1010873
theorem B1329533 : Blo 393766 1329533 := bstep (se 3 (by rfl) ⟨249287, by rfl⟩ : syracuseStep 1329533 = 498575) B498575
theorem B1526159 : Blo 393766 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B444847 : Blo 393766 444847 := bstep (se 1 (by rfl) ⟨333635, by rfl⟩ : syracuseStep 444847 = 667271) B667271
theorem B4344353 : Blo 393766 4344353 := bstep (se 2 (by rfl) ⟨1629132, by rfl⟩ : syracuseStep 4344353 = 3258265) B3258265
theorem B1329803 : Blo 393766 1329803 := bstep (se 1 (by rfl) ⟨997352, by rfl⟩ : syracuseStep 1329803 = 1994705) B1994705
theorem B1002233 : Blo 393766 1002233 := bstep (se 2 (by rfl) ⟨375837, by rfl⟩ : syracuseStep 1002233 = 751675) B751675
theorem B445279 : Blo 393766 445279 := bstep (se 1 (by rfl) ⟨333959, by rfl⟩ : syracuseStep 445279 = 667919) B667919
theorem B1002415 : Blo 393766 1002415 := bstep (se 1 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 1002415 = 1503623) B1503623
theorem B805807 : Blo 393766 805807 := bstep (se 1 (by rfl) ⟨604355, by rfl⟩ : syracuseStep 805807 = 1208711) B1208711
theorem B43142219 : Blo 393766 43142219 := bstep (se 1 (by rfl) ⟨32356664, by rfl⟩ : syracuseStep 43142219 = 64713329) B64713329
theorem B445639 : Blo 393766 445639 := bstep (se 1 (by rfl) ⟨334229, by rfl⟩ : syracuseStep 445639 = 668459) B668459
theorem B1002881 : Blo 393766 1002881 := bstep (se 2 (by rfl) ⟨376080, by rfl⟩ : syracuseStep 1002881 = 752161) B752161
theorem B1429001 : Blo 393766 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B1330721 : Blo 393766 1330721 := bstep (se 2 (by rfl) ⟨499020, by rfl⟩ : syracuseStep 1330721 = 998041) B998041
theorem B1330937 : Blo 393766 1330937 := bstep (se 2 (by rfl) ⟨499101, by rfl⟩ : syracuseStep 1330937 = 998203) B998203
theorem B1003337 : Blo 393766 1003337 := bstep (se 2 (by rfl) ⟨376251, by rfl⟩ : syracuseStep 1003337 = 752503) B752503
theorem B1068983 : Blo 393766 1068983 := bstep (se 1 (by rfl) ⟨801737, by rfl⟩ : syracuseStep 1068983 = 1603475) B1603475
theorem B1331207 : Blo 393766 1331207 := bstep (se 1 (by rfl) ⟨998405, by rfl⟩ : syracuseStep 1331207 = 1996811) B1996811
theorem B446503 : Blo 393766 446503 := bstep (se 1 (by rfl) ⟨334877, by rfl⟩ : syracuseStep 446503 = 669755) B669755
theorem B1626193 : Blo 393766 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B1331315 : Blo 393766 1331315 := bstep (se 1 (by rfl) ⟨998486, by rfl⟩ : syracuseStep 1331315 = 1996973) B1996973
theorem B1003691 : Blo 393766 1003691 := bstep (se 1 (by rfl) ⟨752768, by rfl⟩ : syracuseStep 1003691 = 1505537) B1505537
theorem B6410507 : Blo 393766 6410507 := bstep (se 1 (by rfl) ⟨4807880, by rfl⟩ : syracuseStep 6410507 = 9615761) B9615761
theorem B1331585 : Blo 393766 1331585 := bstep (se 2 (by rfl) ⟨499344, by rfl⟩ : syracuseStep 1331585 = 998689) B998689
theorem B1266607 : Blo 393766 1266607 := bstep (se 1 (by rfl) ⟨949955, by rfl⟩ : syracuseStep 1266607 = 1899911) B1899911
theorem B1004471 : Blo 393766 1004471 := bstep (se 1 (by rfl) ⟨753353, by rfl⟩ : syracuseStep 1004471 = 1506707) B1506707
theorem B1332395 : Blo 393766 1332395 := bstep (se 1 (by rfl) ⟨999296, by rfl⟩ : syracuseStep 1332395 = 1998593) B1998593
theorem B3003965 : Blo 393766 3003965 := bstep (se 3 (by rfl) ⟨563243, by rfl⟩ : syracuseStep 3003965 = 1126487) B1126487
theorem B1332935 : Blo 393766 1332935 := bstep (se 1 (by rfl) ⟨999701, by rfl⟩ : syracuseStep 1332935 = 1999403) B1999403
theorem B743275 : Blo 393766 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B2250605 : Blo 393766 2250605 := bstep (se 3 (by rfl) ⟨421988, by rfl⟩ : syracuseStep 2250605 = 843977) B843977
theorem B1005473 : Blo 393766 1005473 := bstep (se 2 (by rfl) ⟨377052, by rfl⟩ : syracuseStep 1005473 = 754105) B754105
theorem B1005929 : Blo 393766 1005929 := bstep (se 2 (by rfl) ⟨377223, by rfl⟩ : syracuseStep 1005929 = 754447) B754447
theorem B1497473 : Blo 393766 1497473 := bstep (se 2 (by rfl) ⟨561552, by rfl⟩ : syracuseStep 1497473 = 1123105) B1123105
theorem B1497487 : Blo 393766 1497487 := bstep (se 1 (by rfl) ⟨1123115, by rfl⟩ : syracuseStep 1497487 = 2246231) B2246231
theorem B3004937 : Blo 393766 3004937 := bstep (se 2 (by rfl) ⟨1126851, by rfl⟩ : syracuseStep 3004937 = 2253703) B2253703
theorem B1333799 : Blo 393766 1333799 := bstep (se 1 (by rfl) ⟨1000349, by rfl⟩ : syracuseStep 1333799 = 2000699) B2000699
theorem B1333907 : Blo 393766 1333907 := bstep (se 1 (by rfl) ⟨1000430, by rfl⟩ : syracuseStep 1333907 = 2000861) B2000861
theorem B2546387 : Blo 393766 2546387 := bstep (se 1 (by rfl) ⟨1909790, by rfl⟩ : syracuseStep 2546387 = 3819581) B3819581
theorem B1334123 : Blo 393766 1334123 := bstep (se 1 (by rfl) ⟨1000592, by rfl⟩ : syracuseStep 1334123 = 2001185) B2001185
theorem B1334177 : Blo 393766 1334177 := bstep (se 2 (by rfl) ⟨500316, by rfl⟩ : syracuseStep 1334177 = 1000633) B1000633
theorem B1432691 : Blo 393766 1432691 := bstep (se 1 (by rfl) ⟨1074518, by rfl⟩ : syracuseStep 1432691 = 2149037) B2149037
theorem B1334771 : Blo 393766 1334771 := bstep (se 1 (by rfl) ⟨1001078, by rfl⟩ : syracuseStep 1334771 = 2002157) B2002157
theorem B2547287 : Blo 393766 2547287 := bstep (se 1 (by rfl) ⟨1910465, by rfl⟩ : syracuseStep 2547287 = 3820931) B3820931
theorem B1498763 : Blo 393766 1498763 := bstep (se 1 (by rfl) ⟨1124072, by rfl⟩ : syracuseStep 1498763 = 2248145) B2248145
theorem B3006395 : Blo 393766 3006395 := bstep (se 1 (by rfl) ⟨2254796, by rfl⟩ : syracuseStep 3006395 = 4509593) B4509593
theorem B2547719 : Blo 393766 2547719 := bstep (se 1 (by rfl) ⟨1910789, by rfl⟩ : syracuseStep 2547719 = 3821579) B3821579
theorem B1335311 : Blo 393766 1335311 := bstep (se 1 (by rfl) ⟨1001483, by rfl⟩ : syracuseStep 1335311 = 2002967) B2002967
theorem B843833 : Blo 393766 843833 := bstep (se 2 (by rfl) ⟨316437, by rfl⟩ : syracuseStep 843833 = 632875) B632875
theorem B3792977 : Blo 393766 3792977 := bstep (se 2 (by rfl) ⟨1422366, by rfl⟩ : syracuseStep 3792977 = 2844733) B2844733
theorem B1269913 : Blo 393766 1269913 := bstep (se 2 (by rfl) ⟨476217, by rfl⟩ : syracuseStep 1269913 = 952435) B952435
theorem B12312931 : Blo 393766 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B1073513 : Blo 393766 1073513 := bstep (se 2 (by rfl) ⟨402567, by rfl⟩ : syracuseStep 1073513 = 805135) B805135
theorem B844175 : Blo 393766 844175 := bstep (se 1 (by rfl) ⟨633131, by rfl⟩ : syracuseStep 844175 = 1266263) B1266263
theorem B3367433 : Blo 393766 3367433 := bstep (se 2 (by rfl) ⟨1262787, by rfl⟩ : syracuseStep 3367433 = 2525575) B2525575
theorem B1335905 : Blo 393766 1335905 := bstep (se 2 (by rfl) ⟨500964, by rfl⟩ : syracuseStep 1335905 = 1001929) B1001929
theorem B2253521 : Blo 393766 2253521 := bstep (se 2 (by rfl) ⟨845070, by rfl⟩ : syracuseStep 2253521 = 1690141) B1690141
theorem B1893395 : Blo 393766 1893395 := bstep (se 1 (by rfl) ⟨1420046, by rfl⟩ : syracuseStep 1893395 = 2840093) B2840093
theorem B2253977 : Blo 393766 2253977 := bstep (se 2 (by rfl) ⟨845241, by rfl⟩ : syracuseStep 2253977 = 1690483) B1690483
theorem B2974913 : Blo 393766 2974913 := bstep (se 2 (by rfl) ⟨1115592, by rfl⟩ : syracuseStep 2974913 = 2231185) B2231185
theorem B48850289 : Blo 393766 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B5432741 : Blo 393766 5432741 := bstep (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) B1018639
theorem B4515425 : Blo 393766 4515425 := bstep (se 2 (by rfl) ⟨1693284, by rfl⟩ : syracuseStep 4515425 = 3386569) B3386569
theorem B1599419 : Blo 393766 1599419 := bstep (se 1 (by rfl) ⟨1199564, by rfl⟩ : syracuseStep 1599419 = 2399129) B2399129
theorem B1894337 : Blo 393766 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B1271809 : Blo 393766 1271809 := bstep (se 2 (by rfl) ⟨476928, by rfl⟩ : syracuseStep 1271809 = 953857) B953857
theorem B1337363 : Blo 393766 1337363 := bstep (se 1 (by rfl) ⟨1003022, by rfl⟩ : syracuseStep 1337363 = 2006045) B2006045
theorem B747559 : Blo 393766 747559 := bstep (se 1 (by rfl) ⟨560669, by rfl⟩ : syracuseStep 747559 = 1121339) B1121339
theorem B747643 : Blo 393766 747643 := bstep (se 1 (by rfl) ⟨560732, by rfl⟩ : syracuseStep 747643 = 1121465) B1121465
theorem B1337687 : Blo 393766 1337687 := bstep (se 1 (by rfl) ⟨1003265, by rfl⟩ : syracuseStep 1337687 = 2006531) B2006531
theorem B1141121 : Blo 393766 1141121 := bstep (se 2 (by rfl) ⟨427920, by rfl⟩ : syracuseStep 1141121 = 855841) B855841
theorem B5400985 : Blo 393766 5400985 := bstep (se 2 (by rfl) ⟨2025369, by rfl⟩ : syracuseStep 5400985 = 4050739) B4050739
theorem B3795437 : Blo 393766 3795437 := bstep (se 3 (by rfl) ⟨711644, by rfl⟩ : syracuseStep 3795437 = 1423289) B1423289
theorem B748129 : Blo 393766 748129 := bstep (se 2 (by rfl) ⟨280548, by rfl⟩ : syracuseStep 748129 = 561097) B561097
theorem B1698515 : Blo 393766 1698515 := bstep (se 1 (by rfl) ⟨1273886, by rfl⟩ : syracuseStep 1698515 = 2547773) B2547773
theorem B1502135 : Blo 393766 1502135 := bstep (se 1 (by rfl) ⟨1126601, by rfl⟩ : syracuseStep 1502135 = 2253203) B2253203
theorem B846779 : Blo 393766 846779 := bstep (se 1 (by rfl) ⟨635084, by rfl⟩ : syracuseStep 846779 = 1270169) B1270169
theorem B1272989 : Blo 393766 1272989 := bstep (se 3 (by rfl) ⟨238685, by rfl⟩ : syracuseStep 1272989 = 477371) B477371
theorem B847019 : Blo 393766 847019 := bstep (se 1 (by rfl) ⟨635264, by rfl⟩ : syracuseStep 847019 = 1270529) B1270529
theorem B2256119 : Blo 393766 2256119 := bstep (se 1 (by rfl) ⟨1692089, by rfl⟩ : syracuseStep 2256119 = 3384179) B3384179
theorem B1338767 : Blo 393766 1338767 := bstep (se 1 (by rfl) ⟨1004075, by rfl⟩ : syracuseStep 1338767 = 2008151) B2008151
theorem B749063 : Blo 393766 749063 := bstep (se 1 (by rfl) ⟨561797, by rfl⟩ : syracuseStep 749063 = 1123595) B1123595
theorem B2715275 : Blo 393766 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B1339091 : Blo 393766 1339091 := bstep (se 1 (by rfl) ⟨1004318, by rfl⟩ : syracuseStep 1339091 = 2008637) B2008637
theorem B1503137 : Blo 393766 1503137 := bstep (se 2 (by rfl) ⟨563676, by rfl⟩ : syracuseStep 1503137 = 1127353) B1127353
theorem B749587 : Blo 393766 749587 := bstep (se 1 (by rfl) ⟨562190, by rfl⟩ : syracuseStep 749587 = 1124381) B1124381
theorem B1994867 : Blo 393766 1994867 := bstep (se 1 (by rfl) ⟨1496150, by rfl⟩ : syracuseStep 1994867 = 2992301) B2992301
theorem B17166653 : Blo 393766 17166653 := bstep (se 3 (by rfl) ⟨3218747, by rfl⟩ : syracuseStep 17166653 = 6437495) B6437495
theorem B1503593 : Blo 393766 1503593 := bstep (se 2 (by rfl) ⟨563847, by rfl⟩ : syracuseStep 1503593 = 1127695) B1127695
theorem B946937 : Blo 393766 946937 := bstep (se 2 (by rfl) ⟨355101, by rfl⟩ : syracuseStep 946937 = 710203) B710203
theorem B6779699 : Blo 393766 6779699 := bstep (se 1 (by rfl) ⟨5084774, by rfl⟩ : syracuseStep 6779699 = 10169549) B10169549
theorem B1504109 : Blo 393766 1504109 := bstep (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) B564041
theorem B1340279 : Blo 393766 1340279 := bstep (se 1 (by rfl) ⟨1005209, by rfl⟩ : syracuseStep 1340279 = 2010419) B2010419
theorem B947207 : Blo 393766 947207 := bstep (se 1 (by rfl) ⟨710405, by rfl⟩ : syracuseStep 947207 = 1420811) B1420811
theorem B1340495 : Blo 393766 1340495 := bstep (se 1 (by rfl) ⟨1005371, by rfl⟩ : syracuseStep 1340495 = 2010743) B2010743
theorem B2880715 : Blo 393766 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B1340873 : Blo 393766 1340873 := bstep (se 2 (by rfl) ⟨502827, by rfl⟩ : syracuseStep 1340873 = 1005655) B1005655
theorem B1504777 : Blo 393766 1504777 := bstep (se 2 (by rfl) ⟨564291, by rfl⟩ : syracuseStep 1504777 = 1128583) B1128583
theorem B1996487 : Blo 393766 1996487 := bstep (se 1 (by rfl) ⟨1497365, by rfl⟩ : syracuseStep 1996487 = 2994731) B2994731
theorem B1013447 : Blo 393766 1013447 := bstep (se 1 (by rfl) ⟨760085, by rfl⟩ : syracuseStep 1013447 = 1520171) B1520171
theorem B1341143 : Blo 393766 1341143 := bstep (se 1 (by rfl) ⟨1005857, by rfl⟩ : syracuseStep 1341143 = 2011715) B2011715
theorem B1341359 : Blo 393766 1341359 := bstep (se 1 (by rfl) ⟨1006019, by rfl⟩ : syracuseStep 1341359 = 2012039) B2012039
theorem B12777425 : Blo 393766 12777425 := bstep (se 2 (by rfl) ⟨4791534, by rfl⟩ : syracuseStep 12777425 = 9583069) B9583069
theorem B3209219 : Blo 393766 3209219 := bstep (se 1 (by rfl) ⟨2406914, by rfl⟩ : syracuseStep 3209219 = 4813829) B4813829
theorem B6092857 : Blo 393766 6092857 := bstep (se 2 (by rfl) ⟨2284821, by rfl⟩ : syracuseStep 6092857 = 4569643) B4569643
theorem B4585729 : Blo 393766 4585729 := bstep (se 2 (by rfl) ⟨1719648, by rfl⟩ : syracuseStep 4585729 = 3439297) B3439297
theorem B751979 : Blo 393766 751979 := bstep (se 1 (by rfl) ⟨563984, by rfl⟩ : syracuseStep 751979 = 1127969) B1127969
theorem B7600715 : Blo 393766 7600715 := bstep (se 1 (by rfl) ⟨5700536, by rfl⟩ : syracuseStep 7600715 = 11401073) B11401073
theorem B1506235 : Blo 393766 1506235 := bstep (se 1 (by rfl) ⟨1129676, by rfl⟩ : syracuseStep 1506235 = 2259353) B2259353
theorem B752647 : Blo 393766 752647 := bstep (se 1 (by rfl) ⟨564485, by rfl⟩ : syracuseStep 752647 = 1128971) B1128971
theorem B949495 : Blo 393766 949495 := bstep (se 1 (by rfl) ⟨712121, by rfl⟩ : syracuseStep 949495 = 1424243) B1424243
theorem B1899949 : Blo 393766 1899949 := bstep (se 3 (by rfl) ⟨356240, by rfl⟩ : syracuseStep 1899949 = 712481) B712481
theorem B1342985 : Blo 393766 1342985 := bstep (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) B1007239
theorem B753209 : Blo 393766 753209 := bstep (se 2 (by rfl) ⟨282453, by rfl⟩ : syracuseStep 753209 = 564907) B564907
theorem B1507025 : Blo 393766 1507025 := bstep (se 2 (by rfl) ⟨565134, by rfl⟩ : syracuseStep 1507025 = 1130269) B1130269
theorem B1081711 : Blo 393766 1081711 := bstep (se 1 (by rfl) ⟨811283, by rfl⟩ : syracuseStep 1081711 = 1622567) B1622567
theorem B16417241 : Blo 393766 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B393791 : Blo 393766 393791 := bstep (se 1 (by rfl) ⟨295343, by rfl⟩ : syracuseStep 393791 = 590687) B590687
theorem B393799 : Blo 393766 393799 := bstep (se 1 (by rfl) ⟨295349, by rfl⟩ : syracuseStep 393799 = 590699) B590699
theorem B393951 : Blo 393766 393951 := bstep (se 1 (by rfl) ⟨295463, by rfl⟩ : syracuseStep 393951 = 590927) B590927
theorem B394031 : Blo 393766 394031 := bstep (se 1 (by rfl) ⟨295523, by rfl⟩ : syracuseStep 394031 = 591047) B591047
theorem B1147727 : Blo 393766 1147727 := bstep (se 1 (by rfl) ⟨860795, by rfl⟩ : syracuseStep 1147727 = 1721591) B1721591
theorem B2065247 : Blo 393766 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B590747 : Blo 393766 590747 := bstep (se 1 (by rfl) ⟨443060, by rfl⟩ : syracuseStep 590747 = 886121) B886121
theorem B394139 : Blo 393766 394139 := bstep (se 1 (by rfl) ⟨295604, by rfl⟩ : syracuseStep 394139 = 591209) B591209
theorem B394191 : Blo 393766 394191 := bstep (se 1 (by rfl) ⟨295643, by rfl⟩ : syracuseStep 394191 = 591287) B591287
theorem B394215 : Blo 393766 394215 := bstep (se 1 (by rfl) ⟨295661, by rfl⟩ : syracuseStep 394215 = 591323) B591323
theorem B1541111 : Blo 393766 1541111 := bstep (se 1 (by rfl) ⟨1155833, by rfl⟩ : syracuseStep 1541111 = 2311667) B2311667
theorem B394527 : Blo 393766 394527 := bstep (se 1 (by rfl) ⟨295895, by rfl⟩ : syracuseStep 394527 = 591791) B591791
theorem B591143 : Blo 393766 591143 := bstep (se 1 (by rfl) ⟨443357, by rfl⟩ : syracuseStep 591143 = 886715) B886715
theorem B1508651 : Blo 393766 1508651 := bstep (se 1 (by rfl) ⟨1131488, by rfl⟩ : syracuseStep 1508651 = 2262977) B2262977
theorem B394587 : Blo 393766 394587 := bstep (se 1 (by rfl) ⟨295940, by rfl⟩ : syracuseStep 394587 = 591881) B591881
theorem B394607 : Blo 393766 394607 := bstep (se 1 (by rfl) ⟨295955, by rfl⟩ : syracuseStep 394607 = 591911) B591911
theorem B886139 : Blo 393766 886139 := bstep (se 1 (by rfl) ⟨664604, by rfl⟩ : syracuseStep 886139 = 1329209) B1329209
theorem B591227 : Blo 393766 591227 := bstep (se 1 (by rfl) ⟨443420, by rfl⟩ : syracuseStep 591227 = 886841) B886841
theorem B394663 : Blo 393766 394663 := bstep (se 1 (by rfl) ⟨295997, by rfl⟩ : syracuseStep 394663 = 591995) B591995
theorem B886265 : Blo 393766 886265 := bstep (se 2 (by rfl) ⟨332349, by rfl⟩ : syracuseStep 886265 = 664699) B664699
theorem B591353 : Blo 393766 591353 := bstep (se 2 (by rfl) ⟨221757, by rfl⟩ : syracuseStep 591353 = 443515) B443515
theorem B394747 : Blo 393766 394747 := bstep (se 1 (by rfl) ⟨296060, by rfl⟩ : syracuseStep 394747 = 592121) B592121
theorem B4064825 : Blo 393766 4064825 := bstep (se 2 (by rfl) ⟨1524309, by rfl⟩ : syracuseStep 4064825 = 3048619) B3048619
theorem B394815 : Blo 393766 394815 := bstep (se 1 (by rfl) ⟨296111, by rfl⟩ : syracuseStep 394815 = 592223) B592223
theorem B394823 : Blo 393766 394823 := bstep (se 1 (by rfl) ⟨296117, by rfl⟩ : syracuseStep 394823 = 592235) B592235
theorem B886355 : Blo 393766 886355 := bstep (se 1 (by rfl) ⟨664766, by rfl⟩ : syracuseStep 886355 = 1329533) B1329533
theorem B591455 : Blo 393766 591455 := bstep (se 1 (by rfl) ⟨443591, by rfl⟩ : syracuseStep 591455 = 887183) B887183
theorem B394975 : Blo 393766 394975 := bstep (se 1 (by rfl) ⟨296231, by rfl⟩ : syracuseStep 394975 = 592463) B592463
theorem B886535 : Blo 393766 886535 := bstep (se 1 (by rfl) ⟨664901, by rfl⟩ : syracuseStep 886535 = 1329803) B1329803
theorem B395055 : Blo 393766 395055 := bstep (se 1 (by rfl) ⟨296291, by rfl⟩ : syracuseStep 395055 = 592583) B592583
theorem B591671 : Blo 393766 591671 := bstep (se 1 (by rfl) ⟨443753, by rfl⟩ : syracuseStep 591671 = 887507) B887507
theorem B395163 : Blo 393766 395163 := bstep (se 1 (by rfl) ⟨296372, by rfl⟩ : syracuseStep 395163 = 592745) B592745
theorem B395215 : Blo 393766 395215 := bstep (se 1 (by rfl) ⟨296411, by rfl⟩ : syracuseStep 395215 = 592823) B592823
theorem B395239 : Blo 393766 395239 := bstep (se 1 (by rfl) ⟨296429, by rfl⟩ : syracuseStep 395239 = 592859) B592859
theorem B2525165 : Blo 393766 2525165 := bstep (se 3 (by rfl) ⟨473468, by rfl⟩ : syracuseStep 2525165 = 946937) B946937
theorem B591977 : Blo 393766 591977 := bstep (se 2 (by rfl) ⟨221991, by rfl⟩ : syracuseStep 591977 = 443983) B443983
theorem B1607933 : Blo 393766 1607933 := bstep (se 3 (by rfl) ⟨301487, by rfl⟩ : syracuseStep 1607933 = 602975) B602975
theorem B395551 : Blo 393766 395551 := bstep (se 1 (by rfl) ⟨296663, by rfl⟩ : syracuseStep 395551 = 593327) B593327
theorem B395611 : Blo 393766 395611 := bstep (se 1 (by rfl) ⟨296708, by rfl⟩ : syracuseStep 395611 = 593417) B593417
theorem B952667 : Blo 393766 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B887147 : Blo 393766 887147 := bstep (se 1 (by rfl) ⟨665360, by rfl⟩ : syracuseStep 887147 = 1330721) B1330721
theorem B395631 : Blo 393766 395631 := bstep (se 1 (by rfl) ⟨296723, by rfl⟩ : syracuseStep 395631 = 593447) B593447
theorem B592295 : Blo 393766 592295 := bstep (se 1 (by rfl) ⟨444221, by rfl⟩ : syracuseStep 592295 = 888443) B888443
theorem B2165159 : Blo 393766 2165159 := bstep (se 1 (by rfl) ⟨1623869, by rfl⟩ : syracuseStep 2165159 = 3247739) B3247739
theorem B395687 : Blo 393766 395687 := bstep (se 1 (by rfl) ⟨296765, by rfl⟩ : syracuseStep 395687 = 593531) B593531
theorem B887291 : Blo 393766 887291 := bstep (se 1 (by rfl) ⟨665468, by rfl⟩ : syracuseStep 887291 = 1330937) B1330937
theorem B592379 : Blo 393766 592379 := bstep (se 1 (by rfl) ⟨444284, by rfl⟩ : syracuseStep 592379 = 888569) B888569
theorem B395771 : Blo 393766 395771 := bstep (se 1 (by rfl) ⟨296828, by rfl⟩ : syracuseStep 395771 = 593657) B593657
theorem B395839 : Blo 393766 395839 := bstep (se 1 (by rfl) ⟨296879, by rfl⟩ : syracuseStep 395839 = 593759) B593759
theorem B395847 : Blo 393766 395847 := bstep (se 1 (by rfl) ⟨296885, by rfl⟩ : syracuseStep 395847 = 593771) B593771
theorem B887417 : Blo 393766 887417 := bstep (se 2 (by rfl) ⟨332781, by rfl⟩ : syracuseStep 887417 = 665563) B665563
theorem B592505 : Blo 393766 592505 := bstep (se 2 (by rfl) ⟨222189, by rfl⟩ : syracuseStep 592505 = 444379) B444379
theorem B887471 : Blo 393766 887471 := bstep (se 1 (by rfl) ⟨665603, by rfl⟩ : syracuseStep 887471 = 1331207) B1331207
theorem B592559 : Blo 393766 592559 := bstep (se 1 (by rfl) ⟨444419, by rfl⟩ : syracuseStep 592559 = 888839) B888839
theorem B5049053 : Blo 393766 5049053 := bstep (se 3 (by rfl) ⟨946697, by rfl⟩ : syracuseStep 5049053 = 1893395) B1893395
theorem B592607 : Blo 393766 592607 := bstep (se 1 (by rfl) ⟨444455, by rfl⟩ : syracuseStep 592607 = 888911) B888911
theorem B395999 : Blo 393766 395999 := bstep (se 1 (by rfl) ⟨296999, by rfl⟩ : syracuseStep 395999 = 593999) B593999
theorem B887543 : Blo 393766 887543 := bstep (se 1 (by rfl) ⟨665657, by rfl⟩ : syracuseStep 887543 = 1331315) B1331315
theorem B396079 : Blo 393766 396079 := bstep (se 1 (by rfl) ⟨297059, by rfl⟩ : syracuseStep 396079 = 594119) B594119
theorem B396187 : Blo 393766 396187 := bstep (se 1 (by rfl) ⟨297140, by rfl⟩ : syracuseStep 396187 = 594281) B594281
theorem B887723 : Blo 393766 887723 := bstep (se 1 (by rfl) ⟨665792, by rfl⟩ : syracuseStep 887723 = 1331585) B1331585
theorem B396239 : Blo 393766 396239 := bstep (se 1 (by rfl) ⟨297179, by rfl⟩ : syracuseStep 396239 = 594359) B594359
theorem B592871 : Blo 393766 592871 := bstep (se 1 (by rfl) ⟨444653, by rfl⟩ : syracuseStep 592871 = 889307) B889307
theorem B396263 : Blo 393766 396263 := bstep (se 1 (by rfl) ⟨297197, by rfl⟩ : syracuseStep 396263 = 594395) B594395
theorem B593129 : Blo 393766 593129 := bstep (se 2 (by rfl) ⟨222423, by rfl⟩ : syracuseStep 593129 = 444847) B444847
theorem B593183 : Blo 393766 593183 := bstep (se 1 (by rfl) ⟨444887, by rfl⟩ : syracuseStep 593183 = 889775) B889775
theorem B396575 : Blo 393766 396575 := bstep (se 1 (by rfl) ⟨297431, by rfl⟩ : syracuseStep 396575 = 594863) B594863
theorem B396635 : Blo 393766 396635 := bstep (se 1 (by rfl) ⟨297476, by rfl⟩ : syracuseStep 396635 = 594953) B594953
theorem B396655 : Blo 393766 396655 := bstep (se 1 (by rfl) ⟨297491, by rfl⟩ : syracuseStep 396655 = 594983) B594983
theorem B396711 : Blo 393766 396711 := bstep (se 1 (by rfl) ⟨297533, by rfl⟩ : syracuseStep 396711 = 595067) B595067
theorem B888263 : Blo 393766 888263 := bstep (se 1 (by rfl) ⟨666197, by rfl⟩ : syracuseStep 888263 = 1332395) B1332395
theorem B593351 : Blo 393766 593351 := bstep (se 1 (by rfl) ⟨445013, by rfl⟩ : syracuseStep 593351 = 890027) B890027
theorem B396795 : Blo 393766 396795 := bstep (se 1 (by rfl) ⟨297596, by rfl⟩ : syracuseStep 396795 = 595193) B595193
theorem B396863 : Blo 393766 396863 := bstep (se 1 (by rfl) ⟨297647, by rfl⟩ : syracuseStep 396863 = 595295) B595295
theorem B396871 : Blo 393766 396871 := bstep (se 1 (by rfl) ⟨297653, by rfl⟩ : syracuseStep 396871 = 595307) B595307
theorem B2002643 : Blo 393766 2002643 := bstep (se 1 (by rfl) ⟨1501982, by rfl⟩ : syracuseStep 2002643 = 3003965) B3003965
theorem B397023 : Blo 393766 397023 := bstep (se 1 (by rfl) ⟨297767, by rfl⟩ : syracuseStep 397023 = 595535) B595535
theorem B593705 : Blo 393766 593705 := bstep (se 2 (by rfl) ⟨222639, by rfl⟩ : syracuseStep 593705 = 445279) B445279
theorem B888623 : Blo 393766 888623 := bstep (se 1 (by rfl) ⟨666467, by rfl⟩ : syracuseStep 888623 = 1332935) B1332935
theorem B593711 : Blo 393766 593711 := bstep (se 1 (by rfl) ⟨445283, by rfl⟩ : syracuseStep 593711 = 890567) B890567
theorem B397103 : Blo 393766 397103 := bstep (se 1 (by rfl) ⟨297827, by rfl⟩ : syracuseStep 397103 = 595655) B595655
theorem B397211 : Blo 393766 397211 := bstep (se 1 (by rfl) ⟨297908, by rfl⟩ : syracuseStep 397211 = 595817) B595817
theorem B397263 : Blo 393766 397263 := bstep (se 1 (by rfl) ⟨297947, by rfl⟩ : syracuseStep 397263 = 595895) B595895
theorem B397287 : Blo 393766 397287 := bstep (se 1 (by rfl) ⟨297965, by rfl⟩ : syracuseStep 397287 = 595931) B595931
theorem B15274007 : Blo 393766 15274007 := bstep (se 1 (by rfl) ⟨11455505, by rfl⟩ : syracuseStep 15274007 = 22911011) B22911011
theorem B594185 : Blo 393766 594185 := bstep (se 2 (by rfl) ⟨222819, by rfl⟩ : syracuseStep 594185 = 445639) B445639
theorem B397599 : Blo 393766 397599 := bstep (se 1 (by rfl) ⟨298199, by rfl⟩ : syracuseStep 397599 = 596399) B596399
theorem B2003291 : Blo 393766 2003291 := bstep (se 1 (by rfl) ⟨1502468, by rfl⟩ : syracuseStep 2003291 = 3004937) B3004937
theorem B397659 : Blo 393766 397659 := bstep (se 1 (by rfl) ⟨298244, by rfl⟩ : syracuseStep 397659 = 596489) B596489
theorem B889199 : Blo 393766 889199 := bstep (se 1 (by rfl) ⟨666899, by rfl⟩ : syracuseStep 889199 = 1333799) B1333799
theorem B594287 : Blo 393766 594287 := bstep (se 1 (by rfl) ⟨445715, by rfl⟩ : syracuseStep 594287 = 891431) B891431
theorem B397679 : Blo 393766 397679 := bstep (se 1 (by rfl) ⟨298259, by rfl⟩ : syracuseStep 397679 = 596519) B596519
theorem B397735 : Blo 393766 397735 := bstep (se 1 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 397735 = 596603) B596603
theorem B889271 : Blo 393766 889271 := bstep (se 1 (by rfl) ⟨666953, by rfl⟩ : syracuseStep 889271 = 1333907) B1333907
theorem B889415 : Blo 393766 889415 := bstep (se 1 (by rfl) ⟨667061, by rfl⟩ : syracuseStep 889415 = 1334123) B1334123
theorem B594503 : Blo 393766 594503 := bstep (se 1 (by rfl) ⟨445877, by rfl⟩ : syracuseStep 594503 = 891755) B891755
theorem B889451 : Blo 393766 889451 := bstep (se 1 (by rfl) ⟨667088, by rfl⟩ : syracuseStep 889451 = 1334177) B1334177
theorem B594539 : Blo 393766 594539 := bstep (se 1 (by rfl) ⟨445904, by rfl⟩ : syracuseStep 594539 = 891809) B891809
theorem B955127 : Blo 393766 955127 := bstep (se 1 (by rfl) ⟨716345, by rfl⟩ : syracuseStep 955127 = 1432691) B1432691
theorem B594767 : Blo 393766 594767 := bstep (se 1 (by rfl) ⟨446075, by rfl⟩ : syracuseStep 594767 = 892151) B892151
theorem B4297637 : Blo 393766 4297637 := bstep (se 4 (by rfl) ⟨402903, by rfl⟩ : syracuseStep 4297637 = 805807) B805807
theorem B889847 : Blo 393766 889847 := bstep (se 1 (by rfl) ⟨667385, by rfl⟩ : syracuseStep 889847 = 1334771) B1334771
theorem B595163 : Blo 393766 595163 := bstep (se 1 (by rfl) ⟨446372, by rfl⟩ : syracuseStep 595163 = 892745) B892745
theorem B2004263 : Blo 393766 2004263 := bstep (se 1 (by rfl) ⟨1503197, by rfl⟩ : syracuseStep 2004263 = 3006395) B3006395
theorem B890207 : Blo 393766 890207 := bstep (se 1 (by rfl) ⟨667655, by rfl⟩ : syracuseStep 890207 = 1335311) B1335311
theorem B1643899 : Blo 393766 1643899 := bstep (se 1 (by rfl) ⟨1232924, by rfl⟩ : syracuseStep 1643899 = 2465849) B2465849
theorem B562555 : Blo 393766 562555 := bstep (se 1 (by rfl) ⟨421916, by rfl⟩ : syracuseStep 562555 = 843833) B843833
theorem B595337 : Blo 393766 595337 := bstep (se 2 (by rfl) ⟨223251, by rfl⟩ : syracuseStep 595337 = 446503) B446503
theorem B2528651 : Blo 393766 2528651 := bstep (se 1 (by rfl) ⟨1896488, by rfl⟩ : syracuseStep 2528651 = 3792977) B3792977
theorem B2168257 : Blo 393766 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B562783 : Blo 393766 562783 := bstep (se 1 (by rfl) ⟨422087, by rfl⟩ : syracuseStep 562783 = 844175) B844175
theorem B890603 : Blo 393766 890603 := bstep (se 1 (by rfl) ⟨667952, by rfl⟩ : syracuseStep 890603 = 1335905) B1335905
theorem B595691 : Blo 393766 595691 := bstep (se 1 (by rfl) ⟨446768, by rfl⟩ : syracuseStep 595691 = 893537) B893537
theorem B890729 : Blo 393766 890729 := bstep (se 2 (by rfl) ⟨334023, by rfl⟩ : syracuseStep 890729 = 668047) B668047
theorem B595919 : Blo 393766 595919 := bstep (se 1 (by rfl) ⟨446939, by rfl⟩ : syracuseStep 595919 = 893879) B893879
theorem B596315 : Blo 393766 596315 := bstep (se 1 (by rfl) ⟨447236, by rfl⟩ : syracuseStep 596315 = 894473) B894473
theorem B4069757 : Blo 393766 4069757 := bstep (se 3 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 4069757 = 1526159) B1526159
theorem B596543 : Blo 393766 596543 := bstep (se 1 (by rfl) ⟨447407, by rfl⟩ : syracuseStep 596543 = 894815) B894815
theorem B891575 : Blo 393766 891575 := bstep (se 1 (by rfl) ⟨668681, by rfl⟩ : syracuseStep 891575 = 1337363) B1337363
theorem B4266755 : Blo 393766 4266755 := bstep (se 1 (by rfl) ⟨3200066, by rfl⟩ : syracuseStep 4266755 = 6400133) B6400133
theorem B891791 : Blo 393766 891791 := bstep (se 1 (by rfl) ⟨668843, by rfl⟩ : syracuseStep 891791 = 1337687) B1337687
theorem B760747 : Blo 393766 760747 := bstep (se 1 (by rfl) ⟨570560, by rfl⟩ : syracuseStep 760747 = 1141121) B1141121
theorem B3840953 : Blo 393766 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B859099 : Blo 393766 859099 := bstep (se 1 (by rfl) ⟨644324, by rfl⟩ : syracuseStep 859099 = 1288649) B1288649
theorem B2530291 : Blo 393766 2530291 := bstep (se 1 (by rfl) ⟨1897718, by rfl⟩ : syracuseStep 2530291 = 3795437) B3795437
theorem B21437459 : Blo 393766 21437459 := bstep (se 1 (by rfl) ⟨16078094, by rfl⟩ : syracuseStep 21437459 = 32156189) B32156189
theorem B2039003 : Blo 393766 2039003 := bstep (se 1 (by rfl) ⟨1529252, by rfl⟩ : syracuseStep 2039003 = 3058505) B3058505
theorem B2006369 : Blo 393766 2006369 := bstep (se 2 (by rfl) ⟨752388, by rfl⟩ : syracuseStep 2006369 = 1504777) B1504777
theorem B564679 : Blo 393766 564679 := bstep (se 1 (by rfl) ⟨423509, by rfl⟩ : syracuseStep 564679 = 847019) B847019
theorem B892511 : Blo 393766 892511 := bstep (se 1 (by rfl) ⟨669383, by rfl⟩ : syracuseStep 892511 = 1338767) B1338767
theorem B499375 : Blo 393766 499375 := bstep (se 1 (by rfl) ⟨374531, by rfl⟩ : syracuseStep 499375 = 749063) B749063
theorem B1810183 : Blo 393766 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B892727 : Blo 393766 892727 := bstep (se 1 (by rfl) ⟨669545, by rfl⟩ : syracuseStep 892727 = 1339091) B1339091
theorem B991033 : Blo 393766 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B893033 : Blo 393766 893033 := bstep (se 2 (by rfl) ⟨334887, by rfl⟩ : syracuseStep 893033 = 669775) B669775
theorem B11444435 : Blo 393766 11444435 := bstep (se 1 (by rfl) ⟨8583326, by rfl⟩ : syracuseStep 11444435 = 17166653) B17166653
theorem B893519 : Blo 393766 893519 := bstep (se 1 (by rfl) ⟨670139, by rfl⟩ : syracuseStep 893519 = 1340279) B1340279
theorem B1450649 : Blo 393766 1450649 := bstep (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) B1087987
theorem B631471 : Blo 393766 631471 := bstep (se 1 (by rfl) ⟨473603, by rfl⟩ : syracuseStep 631471 = 947207) B947207
theorem B893663 : Blo 393766 893663 := bstep (se 1 (by rfl) ⟨670247, by rfl⟩ : syracuseStep 893663 = 1340495) B1340495
theorem B2433887 : Blo 393766 2433887 := bstep (se 1 (by rfl) ⟨1825415, by rfl⟩ : syracuseStep 2433887 = 3650831) B3650831
theorem B893915 : Blo 393766 893915 := bstep (se 1 (by rfl) ⟨670436, by rfl⟩ : syracuseStep 893915 = 1340873) B1340873
theorem B894095 : Blo 393766 894095 := bstep (se 1 (by rfl) ⟨670571, by rfl⟩ : syracuseStep 894095 = 1341143) B1341143
theorem B894185 : Blo 393766 894185 := bstep (se 2 (by rfl) ⟨335319, by rfl⟩ : syracuseStep 894185 = 670639) B670639
theorem B1123571 : Blo 393766 1123571 := bstep (se 1 (by rfl) ⟨842678, by rfl⟩ : syracuseStep 1123571 = 1685357) B1685357
theorem B2008313 : Blo 393766 2008313 := bstep (se 2 (by rfl) ⟨753117, by rfl⟩ : syracuseStep 2008313 = 1506235) B1506235
theorem B894239 : Blo 393766 894239 := bstep (se 1 (by rfl) ⟨670679, by rfl⟩ : syracuseStep 894239 = 1341359) B1341359
theorem B2139479 : Blo 393766 2139479 := bstep (se 1 (by rfl) ⟨1604609, by rfl⟩ : syracuseStep 2139479 = 3209219) B3209219
theorem B3581293 : Blo 393766 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B664969 : Blo 393766 664969 := bstep (se 2 (by rfl) ⟨249363, by rfl⟩ : syracuseStep 664969 = 498727) B498727
theorem B501319 : Blo 393766 501319 := bstep (se 1 (by rfl) ⟨375989, by rfl⟩ : syracuseStep 501319 = 751979) B751979
theorem B1124027 : Blo 393766 1124027 := bstep (se 1 (by rfl) ⟨843020, by rfl⟩ : syracuseStep 1124027 = 1686041) B1686041
theorem B894761 : Blo 393766 894761 := bstep (se 2 (by rfl) ⟨335535, by rfl⟩ : syracuseStep 894761 = 671071) B671071
theorem B665401 : Blo 393766 665401 := bstep (se 2 (by rfl) ⟨249525, by rfl⟩ : syracuseStep 665401 = 499051) B499051
theorem B2533265 : Blo 393766 2533265 := bstep (se 2 (by rfl) ⟨949974, by rfl⟩ : syracuseStep 2533265 = 1899949) B1899949
theorem B665705 : Blo 393766 665705 := bstep (se 2 (by rfl) ⟨249639, by rfl⟩ : syracuseStep 665705 = 499279) B499279
theorem B502139 : Blo 393766 502139 := bstep (se 1 (by rfl) ⟨376604, by rfl⟩ : syracuseStep 502139 = 753209) B753209
theorem B1911251 : Blo 393766 1911251 := bstep (se 1 (by rfl) ⟨1433438, by rfl⟩ : syracuseStep 1911251 = 2866877) B2866877
theorem B1682471 : Blo 393766 1682471 := bstep (se 1 (by rfl) ⟨1261853, by rfl⟩ : syracuseStep 1682471 = 2523707) B2523707
theorem B10103939 : Blo 393766 10103939 := bstep (se 1 (by rfl) ⟨7577954, by rfl⟩ : syracuseStep 10103939 = 15155909) B15155909
theorem B3386843 : Blo 393766 3386843 := bstep (se 1 (by rfl) ⟨2540132, by rfl⟩ : syracuseStep 3386843 = 5080265) B5080265
theorem B962041 : Blo 393766 962041 := bstep (se 2 (by rfl) ⟨360765, by rfl⟩ : syracuseStep 962041 = 721531) B721531
theorem B667129 : Blo 393766 667129 := bstep (se 2 (by rfl) ⟨250173, by rfl⟩ : syracuseStep 667129 = 500347) B500347
theorem B2862701 : Blo 393766 2862701 := bstep (se 3 (by rfl) ⟨536756, by rfl⟩ : syracuseStep 2862701 = 1073513) B1073513
theorem B667399 : Blo 393766 667399 := bstep (se 1 (by rfl) ⟨500549, by rfl⟩ : syracuseStep 667399 = 1001099) B1001099
theorem B667433 : Blo 393766 667433 := bstep (se 2 (by rfl) ⟨250287, by rfl⟩ : syracuseStep 667433 = 500575) B500575
theorem B1814345 : Blo 393766 1814345 := bstep (se 2 (by rfl) ⟨680379, by rfl⟩ : syracuseStep 1814345 = 1360759) B1360759
theorem B798671 : Blo 393766 798671 := bstep (se 1 (by rfl) ⟨599003, by rfl⟩ : syracuseStep 798671 = 1198007) B1198007
theorem B2896235 : Blo 393766 2896235 := bstep (se 1 (by rfl) ⟨2172176, by rfl⟩ : syracuseStep 2896235 = 4344353) B4344353
theorem B635303 : Blo 393766 635303 := bstep (se 1 (by rfl) ⟨476477, by rfl⟩ : syracuseStep 635303 = 952955) B952955
theorem B1356257 : Blo 393766 1356257 := bstep (se 2 (by rfl) ⟨508596, by rfl⟩ : syracuseStep 1356257 = 1017193) B1017193
theorem B668155 : Blo 393766 668155 := bstep (se 1 (by rfl) ⟨501116, by rfl⟩ : syracuseStep 668155 = 1002233) B1002233
theorem B1028627 : Blo 393766 1028627 := bstep (se 1 (by rfl) ⟨771470, by rfl⟩ : syracuseStep 1028627 = 1542941) B1542941
theorem B7582571 : Blo 393766 7582571 := bstep (se 1 (by rfl) ⟨5686928, by rfl⟩ : syracuseStep 7582571 = 11373857) B11373857
theorem B1684385 : Blo 393766 1684385 := bstep (se 2 (by rfl) ⟨631644, by rfl⟩ : syracuseStep 1684385 = 1263289) B1263289
theorem B668587 : Blo 393766 668587 := bstep (se 1 (by rfl) ⟨501440, by rfl⟩ : syracuseStep 668587 = 1002881) B1002881
theorem B4076689 : Blo 393766 4076689 := bstep (se 2 (by rfl) ⟨1528758, by rfl⟩ : syracuseStep 4076689 = 3057517) B3057517
theorem B668891 : Blo 393766 668891 := bstep (se 1 (by rfl) ⟨501668, by rfl⟩ : syracuseStep 668891 = 1003337) B1003337
theorem B570601 : Blo 393766 570601 := bstep (se 2 (by rfl) ⟨213975, by rfl⟩ : syracuseStep 570601 = 427951) B427951
theorem B963833 : Blo 393766 963833 := bstep (se 2 (by rfl) ⟨361437, by rfl⟩ : syracuseStep 963833 = 722875) B722875
theorem B3257639 : Blo 393766 3257639 := bstep (se 1 (by rfl) ⟨2443229, by rfl⟩ : syracuseStep 3257639 = 4886459) B4886459
theorem B2012525 : Blo 393766 2012525 := bstep (se 3 (by rfl) ⟨377348, by rfl⟩ : syracuseStep 2012525 = 754697) B754697
theorem B996745 : Blo 393766 996745 := bstep (se 2 (by rfl) ⟨373779, by rfl⟩ : syracuseStep 996745 = 747559) B747559
theorem B669127 : Blo 393766 669127 := bstep (se 1 (by rfl) ⟨501845, by rfl⟩ : syracuseStep 669127 = 1003691) B1003691
theorem B8697289 : Blo 393766 8697289 := bstep (se 2 (by rfl) ⟨3261483, by rfl⟩ : syracuseStep 8697289 = 6522967) B6522967
theorem B996857 : Blo 393766 996857 := bstep (se 2 (by rfl) ⟨373821, by rfl⟩ : syracuseStep 996857 = 747643) B747643
theorem B898553 : Blo 393766 898553 := bstep (se 2 (by rfl) ⟨336957, by rfl⟩ : syracuseStep 898553 = 673915) B673915
theorem B3389303 : Blo 393766 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B669647 : Blo 393766 669647 := bstep (se 1 (by rfl) ⟨502235, by rfl⟩ : syracuseStep 669647 = 1004471) B1004471
theorem B997505 : Blo 393766 997505 := bstep (se 2 (by rfl) ⟨374064, by rfl⟩ : syracuseStep 997505 = 748129) B748129
theorem B1358009 : Blo 393766 1358009 := bstep (se 2 (by rfl) ⟨509253, by rfl⟩ : syracuseStep 1358009 = 1018507) B1018507
theorem B670315 : Blo 393766 670315 := bstep (se 1 (by rfl) ⟨502736, by rfl⟩ : syracuseStep 670315 = 1005473) B1005473
theorem B670619 : Blo 393766 670619 := bstep (se 1 (by rfl) ⟨502964, by rfl⟩ : syracuseStep 670619 = 1005929) B1005929
theorem B998315 : Blo 393766 998315 := bstep (se 1 (by rfl) ⟨748736, by rfl⟩ : syracuseStep 998315 = 1497473) B1497473
theorem B1686845 : Blo 393766 1686845 := bstep (se 3 (by rfl) ⟨316283, by rfl⟩ : syracuseStep 1686845 = 632567) B632567
theorem B999175 : Blo 393766 999175 := bstep (se 1 (by rfl) ⟨749381, by rfl⟩ : syracuseStep 999175 = 1498763) B1498763
theorem B1359773 : Blo 393766 1359773 := bstep (se 3 (by rfl) ⟨254957, by rfl⟩ : syracuseStep 1359773 = 509915) B509915
theorem B999449 : Blo 393766 999449 := bstep (se 2 (by rfl) ⟨374793, by rfl⟩ : syracuseStep 999449 = 749587) B749587
theorem B2244955 : Blo 393766 2244955 := bstep (se 1 (by rfl) ⟨1683716, by rfl⟩ : syracuseStep 2244955 = 3367433) B3367433
theorem B2998619 : Blo 393766 2998619 := bstep (se 1 (by rfl) ⟨2248964, by rfl⟩ : syracuseStep 2998619 = 4497929) B4497929
theorem B3785287 : Blo 393766 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B1983275 : Blo 393766 1983275 := bstep (se 1 (by rfl) ⟨1487456, by rfl⟩ : syracuseStep 1983275 = 2974913) B2974913
theorem B19776307 : Blo 393766 19776307 := bstep (se 1 (by rfl) ⟨14832230, by rfl⟩ : syracuseStep 19776307 = 29664461) B29664461
theorem B3621827 : Blo 393766 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B1688809 : Blo 393766 1688809 := bstep (se 2 (by rfl) ⟨633303, by rfl⟩ : syracuseStep 1688809 = 1266607) B1266607
theorem B1066279 : Blo 393766 1066279 := bstep (se 1 (by rfl) ⟨799709, by rfl⟩ : syracuseStep 1066279 = 1599419) B1599419
theorem B1262891 : Blo 393766 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B444127 : Blo 393766 444127 := bstep (se 1 (by rfl) ⟨333095, by rfl⟩ : syracuseStep 444127 = 666191) B666191
theorem B1132343 : Blo 393766 1132343 := bstep (se 1 (by rfl) ⟨849257, by rfl⟩ : syracuseStep 1132343 = 1698515) B1698515
theorem B2901841 : Blo 393766 2901841 := bstep (se 2 (by rfl) ⟨1088190, by rfl⟩ : syracuseStep 2901841 = 2176381) B2176381
theorem B1001423 : Blo 393766 1001423 := bstep (se 1 (by rfl) ⟨751067, by rfl⟩ : syracuseStep 1001423 = 1502135) B1502135
theorem B444703 : Blo 393766 444703 := bstep (se 1 (by rfl) ⟨333527, by rfl⟩ : syracuseStep 444703 = 667055) B667055
theorem B444991 : Blo 393766 444991 := bstep (se 1 (by rfl) ⟨333743, by rfl⟩ : syracuseStep 444991 = 667487) B667487
theorem B21908069 : Blo 393766 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B1002091 : Blo 393766 1002091 := bstep (se 1 (by rfl) ⟨751568, by rfl⟩ : syracuseStep 1002091 = 1503137) B1503137
theorem B1329911 : Blo 393766 1329911 := bstep (se 1 (by rfl) ⟨997433, by rfl⟩ : syracuseStep 1329911 = 1994867) B1994867
theorem B1002395 : Blo 393766 1002395 := bstep (se 1 (by rfl) ⟨751796, by rfl⟩ : syracuseStep 1002395 = 1503593) B1503593
theorem B6114305 : Blo 393766 6114305 := bstep (se 2 (by rfl) ⟨2292864, by rfl⟩ : syracuseStep 6114305 = 4585729) B4585729
theorem B1002739 : Blo 393766 1002739 := bstep (se 1 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 1002739 = 1504109) B1504109
theorem B445819 : Blo 393766 445819 := bstep (se 1 (by rfl) ⟨334364, by rfl⟩ : syracuseStep 445819 = 668729) B668729
theorem B1691219 : Blo 393766 1691219 := bstep (se 1 (by rfl) ⟨1268414, by rfl⟩ : syracuseStep 1691219 = 2536829) B2536829
theorem B1691371 : Blo 393766 1691371 := bstep (se 1 (by rfl) ⟨1268528, by rfl⟩ : syracuseStep 1691371 = 2537057) B2537057
theorem B1330991 : Blo 393766 1330991 := bstep (se 1 (by rfl) ⟨998243, by rfl⟩ : syracuseStep 1330991 = 1996487) B1996487
theorem B675631 : Blo 393766 675631 := bstep (se 1 (by rfl) ⟨506723, by rfl⟩ : syracuseStep 675631 = 1013447) B1013447
theorem B446287 : Blo 393766 446287 := bstep (se 1 (by rfl) ⟨334715, by rfl⟩ : syracuseStep 446287 = 669431) B669431
theorem B1003529 : Blo 393766 1003529 := bstep (se 2 (by rfl) ⟨376323, by rfl⟩ : syracuseStep 1003529 = 752647) B752647
theorem B446683 : Blo 393766 446683 := bstep (se 1 (by rfl) ⟨335012, by rfl⟩ : syracuseStep 446683 = 670025) B670025
theorem B1265993 : Blo 393766 1265993 := bstep (se 2 (by rfl) ⟨474747, by rfl⟩ : syracuseStep 1265993 = 949495) B949495
theorem B5067143 : Blo 393766 5067143 := bstep (se 1 (by rfl) ⟨3800357, by rfl⟩ : syracuseStep 5067143 = 7600715) B7600715
theorem B446971 : Blo 393766 446971 := bstep (se 1 (by rfl) ⟨335228, by rfl⟩ : syracuseStep 446971 = 670457) B670457
theorem B447151 : Blo 393766 447151 := bstep (se 1 (by rfl) ⟨335363, by rfl⟩ : syracuseStep 447151 = 670727) B670727
theorem B447439 : Blo 393766 447439 := bstep (se 1 (by rfl) ⟨335579, by rfl⟩ : syracuseStep 447439 = 671159) B671159
theorem B1004683 : Blo 393766 1004683 := bstep (se 1 (by rfl) ⟨753512, by rfl⟩ : syracuseStep 1004683 = 1507025) B1507025
theorem B1004987 : Blo 393766 1004987 := bstep (se 1 (by rfl) ⟨753740, by rfl⟩ : syracuseStep 1004987 = 1507481) B1507481
theorem B1693217 : Blo 393766 1693217 := bstep (se 2 (by rfl) ⟨634956, by rfl⟩ : syracuseStep 1693217 = 1269913) B1269913
theorem B1333097 : Blo 393766 1333097 := bstep (se 2 (by rfl) ⟨499911, by rfl⟩ : syracuseStep 1333097 = 999823) B999823
theorem B17094685 : Blo 393766 17094685 := bstep (se 3 (by rfl) ⟨3205253, by rfl⟩ : syracuseStep 17094685 = 6410507) B6410507
theorem B1333529 : Blo 393766 1333529 := bstep (se 2 (by rfl) ⟨500073, by rfl⟩ : syracuseStep 1333529 = 1000147) B1000147
theorem B1006303 : Blo 393766 1006303 := bstep (se 1 (by rfl) ⟨754727, by rfl⟩ : syracuseStep 1006303 = 1509455) B1509455
theorem B1006415 : Blo 393766 1006415 := bstep (se 1 (by rfl) ⟨754811, by rfl⟩ : syracuseStep 1006415 = 1509623) B1509623
theorem B1268723 : Blo 393766 1268723 := bstep (se 1 (by rfl) ⟨951542, by rfl⟩ : syracuseStep 1268723 = 1903085) B1903085
theorem B5790937 : Blo 393766 5790937 := bstep (se 2 (by rfl) ⟨2171601, by rfl⟩ : syracuseStep 5790937 = 4343203) B4343203
theorem B28761479 : Blo 393766 28761479 := bstep (se 1 (by rfl) ⟨21571109, by rfl⟩ : syracuseStep 28761479 = 43142219) B43142219
theorem B1334879 : Blo 393766 1334879 := bstep (se 1 (by rfl) ⟨1001159, by rfl⟩ : syracuseStep 1334879 = 2002319) B2002319
theorem B1498733 : Blo 393766 1498733 := bstep (se 3 (by rfl) ⟨281012, by rfl⟩ : syracuseStep 1498733 = 562025) B562025
theorem B712655 : Blo 393766 712655 := bstep (se 1 (by rfl) ⟨534491, by rfl⟩ : syracuseStep 712655 = 1068983) B1068983
theorem B1695745 : Blo 393766 1695745 := bstep (se 2 (by rfl) ⟨635904, by rfl⟩ : syracuseStep 1695745 = 1271809) B1271809
theorem B6775325 : Blo 393766 6775325 := bstep (se 3 (by rfl) ⟨1270373, by rfl⟩ : syracuseStep 6775325 = 2540747) B2540747
theorem B7201313 : Blo 393766 7201313 := bstep (se 2 (by rfl) ⟨2700492, by rfl⟩ : syracuseStep 7201313 = 5400985) B5400985
theorem B1139321 : Blo 393766 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B1336283 : Blo 393766 1336283 := bstep (se 1 (by rfl) ⟨1002212, by rfl⟩ : syracuseStep 1336283 = 2004425) B2004425
theorem B9659357 : Blo 393766 9659357 := bstep (se 3 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 9659357 = 3622259) B3622259
theorem B1074151 : Blo 393766 1074151 := bstep (se 1 (by rfl) ⟨805613, by rfl⟩ : syracuseStep 1074151 = 1611227) B1611227
theorem B1336445 : Blo 393766 1336445 := bstep (se 3 (by rfl) ⟨250583, by rfl⟩ : syracuseStep 1336445 = 501167) B501167
theorem B1336553 : Blo 393766 1336553 := bstep (se 2 (by rfl) ⟨501207, by rfl⟩ : syracuseStep 1336553 = 1002415) B1002415
theorem B1500403 : Blo 393766 1500403 := bstep (se 1 (by rfl) ⟨1125302, by rfl⟩ : syracuseStep 1500403 = 2250605) B2250605
theorem B3007853 : Blo 393766 3007853 := bstep (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) B1127945
theorem B1336715 : Blo 393766 1336715 := bstep (se 1 (by rfl) ⟨1002536, by rfl⟩ : syracuseStep 1336715 = 2005073) B2005073
theorem B1074647 : Blo 393766 1074647 := bstep (se 1 (by rfl) ⟨805985, by rfl⟩ : syracuseStep 1074647 = 1611971) B1611971
theorem B845473 : Blo 393766 845473 := bstep (se 2 (by rfl) ⟨317052, by rfl⟩ : syracuseStep 845473 = 634105) B634105
theorem B1697591 : Blo 393766 1697591 := bstep (se 1 (by rfl) ⟨1273193, by rfl⟩ : syracuseStep 1697591 = 2546387) B2546387
theorem B1698191 : Blo 393766 1698191 := bstep (se 1 (by rfl) ⟨1273643, by rfl⟩ : syracuseStep 1698191 = 2547287) B2547287
theorem B1796681 : Blo 393766 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B1698479 : Blo 393766 1698479 := bstep (se 1 (by rfl) ⟨1273859, by rfl⟩ : syracuseStep 1698479 = 2547719) B2547719
theorem B1502347 : Blo 393766 1502347 := bstep (se 1 (by rfl) ⟨1126760, by rfl⟩ : syracuseStep 1502347 = 2253521) B2253521
theorem B1502651 : Blo 393766 1502651 := bstep (se 1 (by rfl) ⟨1126988, by rfl⟩ : syracuseStep 1502651 = 2253977) B2253977
theorem B32566859 : Blo 393766 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B683615 : Blo 393766 683615 := bstep (se 1 (by rfl) ⟨512711, by rfl⟩ : syracuseStep 683615 = 1025423) B1025423
theorem B2256619 : Blo 393766 2256619 := bstep (se 1 (by rfl) ⟨1692464, by rfl⟩ : syracuseStep 2256619 = 3384929) B3384929
theorem B3010283 : Blo 393766 3010283 := bstep (se 1 (by rfl) ⟨2257712, by rfl⟩ : syracuseStep 3010283 = 4515425) B4515425
theorem B1994543 : Blo 393766 1994543 := bstep (se 1 (by rfl) ⟨1495907, by rfl⟩ : syracuseStep 1994543 = 2991815) B2991815
theorem B4550813 : Blo 393766 4550813 := bstep (se 3 (by rfl) ⟨853277, by rfl⟩ : syracuseStep 4550813 = 1706555) B1706555
theorem B1339739 : Blo 393766 1339739 := bstep (se 1 (by rfl) ⟨1004804, by rfl⟩ : syracuseStep 1339739 = 2009609) B2009609
theorem B750035 : Blo 393766 750035 := bstep (se 1 (by rfl) ⟨562526, by rfl⟩ : syracuseStep 750035 = 1125053) B1125053
theorem B1012193 : Blo 393766 1012193 := bstep (se 2 (by rfl) ⟨379572, by rfl⟩ : syracuseStep 1012193 = 759145) B759145
theorem B848659 : Blo 393766 848659 := bstep (se 1 (by rfl) ⟨636494, by rfl⟩ : syracuseStep 848659 = 1272989) B1272989
theorem B1504079 : Blo 393766 1504079 := bstep (se 1 (by rfl) ⟨1128059, by rfl⟩ : syracuseStep 1504079 = 2256119) B2256119
theorem B2258077 : Blo 393766 2258077 := bstep (se 3 (by rfl) ⟨423389, by rfl⟩ : syracuseStep 2258077 = 846779) B846779
theorem B3011741 : Blo 393766 3011741 := bstep (se 3 (by rfl) ⟨564701, by rfl⟩ : syracuseStep 3011741 = 1129403) B1129403
theorem B947495 : Blo 393766 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B1340711 : Blo 393766 1340711 := bstep (se 1 (by rfl) ⟨1005533, by rfl⟩ : syracuseStep 1340711 = 2011067) B2011067
theorem B8123809 : Blo 393766 8123809 := bstep (se 2 (by rfl) ⟨3046428, by rfl⟩ : syracuseStep 8123809 = 6092857) B6092857
theorem B2848193 : Blo 393766 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B751265 : Blo 393766 751265 := bstep (se 2 (by rfl) ⟨281724, by rfl⟩ : syracuseStep 751265 = 563449) B563449
theorem B1996649 : Blo 393766 1996649 := bstep (se 2 (by rfl) ⟨748743, by rfl⟩ : syracuseStep 1996649 = 1497487) B1497487
theorem B4519799 : Blo 393766 4519799 := bstep (se 1 (by rfl) ⟨3389849, by rfl⟩ : syracuseStep 4519799 = 6779699) B6779699
theorem B423911 : Blo 393766 423911 := bstep (se 1 (by rfl) ⟨317933, by rfl⟩ : syracuseStep 423911 = 635867) B635867
theorem B5404715 : Blo 393766 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B1341575 : Blo 393766 1341575 := bstep (se 1 (by rfl) ⟨1006181, by rfl⟩ : syracuseStep 1341575 = 2012363) B2012363
theorem B2062583 : Blo 393766 2062583 := bstep (se 1 (by rfl) ⟨1546937, by rfl⟩ : syracuseStep 2062583 = 3093875) B3093875
theorem B8518283 : Blo 393766 8518283 := bstep (se 1 (by rfl) ⟨6388712, by rfl⟩ : syracuseStep 8518283 = 12777425) B12777425
theorem B1900025 : Blo 393766 1900025 := bstep (se 2 (by rfl) ⟨712509, by rfl⟩ : syracuseStep 1900025 = 1425019) B1425019
theorem B2850329 : Blo 393766 2850329 := bstep (se 2 (by rfl) ⟨1068873, by rfl⟩ : syracuseStep 2850329 = 2137747) B2137747
theorem B1998431 : Blo 393766 1998431 := bstep (se 1 (by rfl) ⟨1498823, by rfl⟩ : syracuseStep 1998431 = 2997647) B2997647
theorem B2260993 : Blo 393766 2260993 := bstep (se 2 (by rfl) ⟨847872, by rfl⟩ : syracuseStep 2260993 = 1695745) B1695745
theorem B1999079 : Blo 393766 1999079 := bstep (se 1 (by rfl) ⟨1499309, by rfl⟩ : syracuseStep 1999079 = 2998619) B2998619
theorem B10944827 : Blo 393766 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B1442281 : Blo 393766 1442281 := bstep (se 2 (by rfl) ⟨540855, by rfl⟩ : syracuseStep 1442281 = 1081711) B1081711
theorem B1376831 : Blo 393766 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B393831 : Blo 393766 393831 := bstep (se 1 (by rfl) ⟨295373, by rfl⟩ : syracuseStep 393831 = 590747) B590747
theorem B5047049 : Blo 393766 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B394095 : Blo 393766 394095 := bstep (se 1 (by rfl) ⟨295571, by rfl⟩ : syracuseStep 394095 = 591143) B591143
theorem B590759 : Blo 393766 590759 := bstep (se 1 (by rfl) ⟨443069, by rfl⟩ : syracuseStep 590759 = 886139) B886139
theorem B394151 : Blo 393766 394151 := bstep (se 1 (by rfl) ⟨295613, by rfl⟩ : syracuseStep 394151 = 591227) B591227
theorem B590843 : Blo 393766 590843 := bstep (se 1 (by rfl) ⟨443132, by rfl⟩ : syracuseStep 590843 = 886265) B886265
theorem B394235 : Blo 393766 394235 := bstep (se 1 (by rfl) ⟨295676, by rfl⟩ : syracuseStep 394235 = 591353) B591353
theorem B590903 : Blo 393766 590903 := bstep (se 1 (by rfl) ⟨443177, by rfl⟩ : syracuseStep 590903 = 886355) B886355
theorem B394303 : Blo 393766 394303 := bstep (se 1 (by rfl) ⟨295727, by rfl⟩ : syracuseStep 394303 = 591455) B591455
theorem B591023 : Blo 393766 591023 := bstep (se 1 (by rfl) ⟨443267, by rfl⟩ : syracuseStep 591023 = 886535) B886535
theorem B394447 : Blo 393766 394447 := bstep (se 1 (by rfl) ⟨295835, by rfl⟩ : syracuseStep 394447 = 591671) B591671
theorem B754895 : Blo 393766 754895 := bstep (se 1 (by rfl) ⟨566171, by rfl⟩ : syracuseStep 754895 = 1132343) B1132343
theorem B394651 : Blo 393766 394651 := bstep (se 1 (by rfl) ⟨295988, by rfl⟩ : syracuseStep 394651 = 591977) B591977
theorem B591431 : Blo 393766 591431 := bstep (se 1 (by rfl) ⟨443573, by rfl⟩ : syracuseStep 591431 = 887147) B887147
theorem B394863 : Blo 393766 394863 := bstep (se 1 (by rfl) ⟨296147, by rfl⟩ : syracuseStep 394863 = 592295) B592295
theorem B1443439 : Blo 393766 1443439 := bstep (se 1 (by rfl) ⟨1082579, by rfl⟩ : syracuseStep 1443439 = 2165159) B2165159
theorem B2000537 : Blo 393766 2000537 := bstep (se 2 (by rfl) ⟨750201, by rfl⟩ : syracuseStep 2000537 = 1500403) B1500403
theorem B591527 : Blo 393766 591527 := bstep (se 1 (by rfl) ⟨443645, by rfl⟩ : syracuseStep 591527 = 887291) B887291
theorem B394919 : Blo 393766 394919 := bstep (se 1 (by rfl) ⟨296189, by rfl⟩ : syracuseStep 394919 = 592379) B592379
theorem B591611 : Blo 393766 591611 := bstep (se 1 (by rfl) ⟨443708, by rfl⟩ : syracuseStep 591611 = 887417) B887417
theorem B395003 : Blo 393766 395003 := bstep (se 1 (by rfl) ⟨296252, by rfl⟩ : syracuseStep 395003 = 592505) B592505
theorem B591647 : Blo 393766 591647 := bstep (se 1 (by rfl) ⟨443735, by rfl⟩ : syracuseStep 591647 = 887471) B887471
theorem B395039 : Blo 393766 395039 := bstep (se 1 (by rfl) ⟨296279, by rfl⟩ : syracuseStep 395039 = 592559) B592559
theorem B395071 : Blo 393766 395071 := bstep (se 1 (by rfl) ⟨296303, by rfl⟩ : syracuseStep 395071 = 592607) B592607
theorem B886607 : Blo 393766 886607 := bstep (se 1 (by rfl) ⟨664955, by rfl⟩ : syracuseStep 886607 = 1329911) B1329911
theorem B591695 : Blo 393766 591695 := bstep (se 1 (by rfl) ⟨443771, by rfl⟩ : syracuseStep 591695 = 887543) B887543
theorem B886625 : Blo 393766 886625 := bstep (se 2 (by rfl) ⟨332484, by rfl⟩ : syracuseStep 886625 = 664969) B664969
theorem B591815 : Blo 393766 591815 := bstep (se 1 (by rfl) ⟨443861, by rfl⟩ : syracuseStep 591815 = 887723) B887723
theorem B395247 : Blo 393766 395247 := bstep (se 1 (by rfl) ⟨296435, by rfl⟩ : syracuseStep 395247 = 592871) B592871
theorem B395419 : Blo 393766 395419 := bstep (se 1 (by rfl) ⟨296564, by rfl⟩ : syracuseStep 395419 = 593129) B593129
theorem B395455 : Blo 393766 395455 := bstep (se 1 (by rfl) ⟨296591, by rfl⟩ : syracuseStep 395455 = 593183) B593183
theorem B592169 : Blo 393766 592169 := bstep (se 2 (by rfl) ⟨222063, by rfl⟩ : syracuseStep 592169 = 444127) B444127
theorem B592175 : Blo 393766 592175 := bstep (se 1 (by rfl) ⟨444131, by rfl⟩ : syracuseStep 592175 = 888263) B888263
theorem B395567 : Blo 393766 395567 := bstep (se 1 (by rfl) ⟨296675, by rfl⟩ : syracuseStep 395567 = 593351) B593351
theorem B887201 : Blo 393766 887201 := bstep (se 2 (by rfl) ⟨332700, by rfl⟩ : syracuseStep 887201 = 665401) B665401
theorem B395803 : Blo 393766 395803 := bstep (se 1 (by rfl) ⟨296852, by rfl⟩ : syracuseStep 395803 = 593705) B593705
theorem B887327 : Blo 393766 887327 := bstep (se 1 (by rfl) ⟨665495, by rfl⟩ : syracuseStep 887327 = 1330991) B1330991
theorem B592415 : Blo 393766 592415 := bstep (se 1 (by rfl) ⟨444311, by rfl⟩ : syracuseStep 592415 = 888623) B888623
theorem B395807 : Blo 393766 395807 := bstep (se 1 (by rfl) ⟨296855, by rfl⟩ : syracuseStep 395807 = 593711) B593711
theorem B396123 : Blo 393766 396123 := bstep (se 1 (by rfl) ⟨297092, by rfl⟩ : syracuseStep 396123 = 594185) B594185
theorem B592799 : Blo 393766 592799 := bstep (se 1 (by rfl) ⟨444599, by rfl⟩ : syracuseStep 592799 = 889199) B889199
theorem B396191 : Blo 393766 396191 := bstep (se 1 (by rfl) ⟨297143, by rfl⟩ : syracuseStep 396191 = 594287) B594287
theorem B3378095 : Blo 393766 3378095 := bstep (se 1 (by rfl) ⟨2533571, by rfl⟩ : syracuseStep 3378095 = 5067143) B5067143
theorem B592847 : Blo 393766 592847 := bstep (se 1 (by rfl) ⟨444635, by rfl⟩ : syracuseStep 592847 = 889271) B889271
theorem B592937 : Blo 393766 592937 := bstep (se 2 (by rfl) ⟨222351, by rfl⟩ : syracuseStep 592937 = 444703) B444703
theorem B592943 : Blo 393766 592943 := bstep (se 1 (by rfl) ⟨444707, by rfl⟩ : syracuseStep 592943 = 889415) B889415
theorem B396335 : Blo 393766 396335 := bstep (se 1 (by rfl) ⟨297251, by rfl⟩ : syracuseStep 396335 = 594503) B594503
theorem B592967 : Blo 393766 592967 := bstep (se 1 (by rfl) ⟨444725, by rfl⟩ : syracuseStep 592967 = 889451) B889451
theorem B396359 : Blo 393766 396359 := bstep (se 1 (by rfl) ⟨297269, by rfl⟩ : syracuseStep 396359 = 594539) B594539
theorem B396511 : Blo 393766 396511 := bstep (se 1 (by rfl) ⟨297383, by rfl⟩ : syracuseStep 396511 = 594767) B594767
theorem B593231 : Blo 393766 593231 := bstep (se 1 (by rfl) ⟨444923, by rfl⟩ : syracuseStep 593231 = 889847) B889847
theorem B593321 : Blo 393766 593321 := bstep (se 2 (by rfl) ⟨222495, by rfl⟩ : syracuseStep 593321 = 444991) B444991
theorem B2526653 : Blo 393766 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B396775 : Blo 393766 396775 := bstep (se 1 (by rfl) ⟨297581, by rfl⟩ : syracuseStep 396775 = 595163) B595163
theorem B593471 : Blo 393766 593471 := bstep (se 1 (by rfl) ⟨445103, by rfl⟩ : syracuseStep 593471 = 890207) B890207
theorem B396891 : Blo 393766 396891 := bstep (se 1 (by rfl) ⟨297668, by rfl⟩ : syracuseStep 396891 = 595337) B595337
theorem B593735 : Blo 393766 593735 := bstep (se 1 (by rfl) ⟨445301, by rfl⟩ : syracuseStep 593735 = 890603) B890603
theorem B397127 : Blo 393766 397127 := bstep (se 1 (by rfl) ⟨297845, by rfl⟩ : syracuseStep 397127 = 595691) B595691
theorem B888731 : Blo 393766 888731 := bstep (se 1 (by rfl) ⟨666548, by rfl⟩ : syracuseStep 888731 = 1333097) B1333097
theorem B593819 : Blo 393766 593819 := bstep (se 1 (by rfl) ⟨445364, by rfl⟩ : syracuseStep 593819 = 890729) B890729
theorem B397279 : Blo 393766 397279 := bstep (se 1 (by rfl) ⟨297959, by rfl⟩ : syracuseStep 397279 = 595919) B595919
theorem B2396141 : Blo 393766 2396141 := bstep (se 3 (by rfl) ⟨449276, by rfl⟩ : syracuseStep 2396141 = 898553) B898553
theorem B2003129 : Blo 393766 2003129 := bstep (se 2 (by rfl) ⟨751173, by rfl⟩ : syracuseStep 2003129 = 1502347) B1502347
theorem B889019 : Blo 393766 889019 := bstep (se 1 (by rfl) ⟨666764, by rfl⟩ : syracuseStep 889019 = 1333529) B1333529
theorem B397543 : Blo 393766 397543 := bstep (se 1 (by rfl) ⟨298157, by rfl⟩ : syracuseStep 397543 = 596315) B596315
theorem B397695 : Blo 393766 397695 := bstep (se 1 (by rfl) ⟨298271, by rfl⟩ : syracuseStep 397695 = 596543) B596543
theorem B594383 : Blo 393766 594383 := bstep (se 1 (by rfl) ⟨445787, by rfl⟩ : syracuseStep 594383 = 891575) B891575
theorem B594425 : Blo 393766 594425 := bstep (se 2 (by rfl) ⟨222909, by rfl⟩ : syracuseStep 594425 = 445819) B445819
theorem B594527 : Blo 393766 594527 := bstep (se 1 (by rfl) ⟨445895, by rfl⟩ : syracuseStep 594527 = 891791) B891791
theorem B1282721 : Blo 393766 1282721 := bstep (se 2 (by rfl) ⟨481020, by rfl⟩ : syracuseStep 1282721 = 962041) B962041
theorem B889505 : Blo 393766 889505 := bstep (se 2 (by rfl) ⟨333564, by rfl⟩ : syracuseStep 889505 = 667129) B667129
theorem B14291639 : Blo 393766 14291639 := bstep (se 1 (by rfl) ⟨10718729, by rfl⟩ : syracuseStep 14291639 = 21437459) B21437459
theorem B19174319 : Blo 393766 19174319 := bstep (se 1 (by rfl) ⟨14380739, by rfl⟩ : syracuseStep 19174319 = 28761479) B28761479
theorem B889865 : Blo 393766 889865 := bstep (se 2 (by rfl) ⟨333699, by rfl⟩ : syracuseStep 889865 = 667399) B667399
theorem B889919 : Blo 393766 889919 := bstep (se 1 (by rfl) ⟨667439, by rfl⟩ : syracuseStep 889919 = 1334879) B1334879
theorem B595007 : Blo 393766 595007 := bstep (se 1 (by rfl) ⟨446255, by rfl⟩ : syracuseStep 595007 = 892511) B892511
theorem B595049 : Blo 393766 595049 := bstep (se 2 (by rfl) ⟨223143, by rfl⟩ : syracuseStep 595049 = 446287) B446287
theorem B595151 : Blo 393766 595151 := bstep (se 1 (by rfl) ⟨446363, by rfl⟩ : syracuseStep 595151 = 892727) B892727
theorem B595355 : Blo 393766 595355 := bstep (se 1 (by rfl) ⟨446516, by rfl⟩ : syracuseStep 595355 = 893033) B893033
theorem B595577 : Blo 393766 595577 := bstep (se 2 (by rfl) ⟨223341, by rfl⟩ : syracuseStep 595577 = 446683) B446683
theorem B595679 : Blo 393766 595679 := bstep (se 1 (by rfl) ⟨446759, by rfl⟩ : syracuseStep 595679 = 893519) B893519
theorem B759547 : Blo 393766 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B595775 : Blo 393766 595775 := bstep (se 1 (by rfl) ⟨446831, by rfl⟩ : syracuseStep 595775 = 893663) B893663
theorem B890855 : Blo 393766 890855 := bstep (se 1 (by rfl) ⟨668141, by rfl⟩ : syracuseStep 890855 = 1336283) B1336283
theorem B595943 : Blo 393766 595943 := bstep (se 1 (by rfl) ⟨446957, by rfl⟩ : syracuseStep 595943 = 893915) B893915
theorem B890873 : Blo 393766 890873 := bstep (se 2 (by rfl) ⟨334077, by rfl⟩ : syracuseStep 890873 = 668155) B668155
theorem B595961 : Blo 393766 595961 := bstep (se 2 (by rfl) ⟨223485, by rfl⟩ : syracuseStep 595961 = 446971) B446971
theorem B890963 : Blo 393766 890963 := bstep (se 1 (by rfl) ⟨668222, by rfl⟩ : syracuseStep 890963 = 1336445) B1336445
theorem B596063 : Blo 393766 596063 := bstep (se 1 (by rfl) ⟨447047, by rfl⟩ : syracuseStep 596063 = 894095) B894095
theorem B891035 : Blo 393766 891035 := bstep (se 1 (by rfl) ⟨668276, by rfl⟩ : syracuseStep 891035 = 1336553) B1336553
theorem B596123 : Blo 393766 596123 := bstep (se 1 (by rfl) ⟨447092, by rfl⟩ : syracuseStep 596123 = 894185) B894185
theorem B596159 : Blo 393766 596159 := bstep (se 1 (by rfl) ⟨447119, by rfl⟩ : syracuseStep 596159 = 894239) B894239
theorem B596201 : Blo 393766 596201 := bstep (se 2 (by rfl) ⟨223575, by rfl⟩ : syracuseStep 596201 = 447151) B447151
theorem B2005235 : Blo 393766 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B891143 : Blo 393766 891143 := bstep (se 1 (by rfl) ⟨668357, by rfl⟩ : syracuseStep 891143 = 1336715) B1336715
theorem B21142037 : Blo 393766 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B596507 : Blo 393766 596507 := bstep (se 1 (by rfl) ⟨447380, by rfl⟩ : syracuseStep 596507 = 894761) B894761
theorem B891449 : Blo 393766 891449 := bstep (se 2 (by rfl) ⟨334293, by rfl⟩ : syracuseStep 891449 = 668587) B668587
theorem B596585 : Blo 393766 596585 := bstep (se 2 (by rfl) ⟨223719, by rfl⟩ : syracuseStep 596585 = 447439) B447439
theorem B4791149 : Blo 393766 4791149 := bstep (se 3 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 4791149 = 1796681) B1796681
theorem B760801 : Blo 393766 760801 := bstep (se 2 (by rfl) ⟨285300, by rfl⟩ : syracuseStep 760801 = 570601) B570601
theorem B61905941 : Blo 393766 61905941 := bstep (se 6 (by rfl) ⟨1450920, by rfl⟩ : syracuseStep 61905941 = 2901841) B2901841
theorem B2891009 : Blo 393766 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B892169 : Blo 393766 892169 := bstep (se 2 (by rfl) ⟨334563, by rfl⟩ : syracuseStep 892169 = 669127) B669127
theorem B1121647 : Blo 393766 1121647 := bstep (se 1 (by rfl) ⟨841235, by rfl⟩ : syracuseStep 1121647 = 1682471) B1682471
theorem B1908467 : Blo 393766 1908467 := bstep (se 1 (by rfl) ⟨1431350, by rfl⟩ : syracuseStep 1908467 = 2862701) B2862701
theorem B2006855 : Blo 393766 2006855 := bstep (se 1 (by rfl) ⟨1505141, by rfl⟩ : syracuseStep 2006855 = 3010283) B3010283
theorem B893159 : Blo 393766 893159 := bstep (se 1 (by rfl) ⟨669869, by rfl⟩ : syracuseStep 893159 = 1339739) B1339739
theorem B500023 : Blo 393766 500023 := bstep (se 1 (by rfl) ⟨375017, by rfl⟩ : syracuseStep 500023 = 750035) B750035
theorem B5055047 : Blo 393766 5055047 := bstep (se 1 (by rfl) ⟨3791285, by rfl⟩ : syracuseStep 5055047 = 7582571) B7582571
theorem B1122923 : Blo 393766 1122923 := bstep (se 1 (by rfl) ⟨842192, by rfl⟩ : syracuseStep 1122923 = 1684385) B1684385
theorem B2007827 : Blo 393766 2007827 := bstep (se 1 (by rfl) ⟨1505870, by rfl⟩ : syracuseStep 2007827 = 3011741) B3011741
theorem B893753 : Blo 393766 893753 := bstep (se 2 (by rfl) ⟨335157, by rfl⟩ : syracuseStep 893753 = 670315) B670315
theorem B893807 : Blo 393766 893807 := bstep (se 1 (by rfl) ⟨670355, by rfl⟩ : syracuseStep 893807 = 1340711) B1340711
theorem B664571 : Blo 393766 664571 := bstep (se 1 (by rfl) ⟨498428, by rfl⟩ : syracuseStep 664571 = 996857) B996857
theorem B500843 : Blo 393766 500843 := bstep (se 1 (by rfl) ⟨375632, by rfl⟩ : syracuseStep 500843 = 751265) B751265
theorem B665003 : Blo 393766 665003 := bstep (se 1 (by rfl) ⟨498752, by rfl⟩ : syracuseStep 665003 = 997505) B997505
theorem B894383 : Blo 393766 894383 := bstep (se 1 (by rfl) ⟨670787, by rfl⟩ : syracuseStep 894383 = 1341575) B1341575
theorem B5678855 : Blo 393766 5678855 := bstep (se 1 (by rfl) ⟨4259141, by rfl⟩ : syracuseStep 5678855 = 8518283) B8518283
theorem B665543 : Blo 393766 665543 := bstep (se 1 (by rfl) ⟨499157, by rfl⟩ : syracuseStep 665543 = 998315) B998315
theorem B1124563 : Blo 393766 1124563 := bstep (se 1 (by rfl) ⟨843422, by rfl⟩ : syracuseStep 1124563 = 1686845) B1686845
theorem B665833 : Blo 393766 665833 := bstep (se 2 (by rfl) ⟨249687, by rfl⟩ : syracuseStep 665833 = 499375) B499375
theorem B666299 : Blo 393766 666299 := bstep (se 1 (by rfl) ⟨499724, by rfl⟩ : syracuseStep 666299 = 999449) B999449
theorem B2993273 : Blo 393766 2993273 := bstep (se 2 (by rfl) ⟨1122477, by rfl⟩ : syracuseStep 2993273 = 2244955) B2244955
theorem B1322183 : Blo 393766 1322183 := bstep (se 1 (by rfl) ⟨991637, by rfl⟩ : syracuseStep 1322183 = 1983275) B1983275
theorem B667615 : Blo 393766 667615 := bstep (se 1 (by rfl) ⟨500711, by rfl⟩ : syracuseStep 667615 = 1001423) B1001423
theorem B1683443 : Blo 393766 1683443 := bstep (se 1 (by rfl) ⟨1262582, by rfl⟩ : syracuseStep 1683443 = 2525165) B2525165
theorem B635111 : Blo 393766 635111 := bstep (se 1 (by rfl) ⟨476333, by rfl⟩ : syracuseStep 635111 = 952667) B952667
theorem B1421705 : Blo 393766 1421705 := bstep (se 2 (by rfl) ⟨533139, by rfl⟩ : syracuseStep 1421705 = 1066279) B1066279
theorem B668263 : Blo 393766 668263 := bstep (se 1 (by rfl) ⟨501197, by rfl⟩ : syracuseStep 668263 = 1002395) B1002395
theorem B4076203 : Blo 393766 4076203 := bstep (se 1 (by rfl) ⟨3057152, by rfl⟩ : syracuseStep 4076203 = 6114305) B6114305
theorem B668425 : Blo 393766 668425 := bstep (se 2 (by rfl) ⟨250659, by rfl⟩ : syracuseStep 668425 = 501319) B501319
theorem B3060605 : Blo 393766 3060605 := bstep (se 3 (by rfl) ⟨573863, by rfl⟩ : syracuseStep 3060605 = 1147727) B1147727
theorem B1127297 : Blo 393766 1127297 := bstep (se 2 (by rfl) ⟨422736, by rfl⟩ : syracuseStep 1127297 = 845473) B845473
theorem B1127479 : Blo 393766 1127479 := bstep (se 1 (by rfl) ⟨845609, by rfl⟩ : syracuseStep 1127479 = 1691219) B1691219
theorem B4109629 : Blo 393766 4109629 := bstep (se 3 (by rfl) ⟨770555, by rfl⟩ : syracuseStep 4109629 = 1541111) B1541111
theorem B669019 : Blo 393766 669019 := bstep (se 1 (by rfl) ⟨501764, by rfl⟩ : syracuseStep 669019 = 1003529) B1003529
theorem B34748149 : Blo 393766 34748149 := bstep (se 5 (by rfl) ⟨1628819, by rfl⟩ : syracuseStep 34748149 = 3257639) B3257639
theorem B636751 : Blo 393766 636751 := bstep (se 1 (by rfl) ⟨477563, by rfl⟩ : syracuseStep 636751 = 955127) B955127
theorem B2865091 : Blo 393766 2865091 := bstep (se 1 (by rfl) ⟨2148818, by rfl⟩ : syracuseStep 2865091 = 4297637) B4297637
theorem B2996189 : Blo 393766 2996189 := bstep (se 3 (by rfl) ⟨561785, by rfl⟩ : syracuseStep 2996189 = 1123571) B1123571
theorem B2570221 : Blo 393766 2570221 := bstep (se 3 (by rfl) ⟨481916, by rfl⟩ : syracuseStep 2570221 = 963833) B963833
theorem B1685767 : Blo 393766 1685767 := bstep (se 1 (by rfl) ⟨1264325, by rfl⟩ : syracuseStep 1685767 = 2528651) B2528651
theorem B669991 : Blo 393766 669991 := bstep (se 1 (by rfl) ⟨502493, by rfl⟩ : syracuseStep 669991 = 1004987) B1004987
theorem B1128811 : Blo 393766 1128811 := bstep (se 1 (by rfl) ⟨846608, by rfl⟩ : syracuseStep 1128811 = 1693217) B1693217
theorem B670943 : Blo 393766 670943 := bstep (se 1 (by rfl) ⟨503207, by rfl⟩ : syracuseStep 670943 = 1006415) B1006415
theorem B1359335 : Blo 393766 1359335 := bstep (se 1 (by rfl) ⟨1019501, by rfl⟩ : syracuseStep 1359335 = 2039003) B2039003
theorem B999155 : Blo 393766 999155 := bstep (se 1 (by rfl) ⟨749366, by rfl⟩ : syracuseStep 999155 = 1498733) B1498733
theorem B1130429 : Blo 393766 1130429 := bstep (se 3 (by rfl) ⟨211955, by rfl⟩ : syracuseStep 1130429 = 423911) B423911
theorem B475103 : Blo 393766 475103 := bstep (se 1 (by rfl) ⟨356327, by rfl⟩ : syracuseStep 475103 = 712655) B712655
theorem B4800875 : Blo 393766 4800875 := bstep (se 1 (by rfl) ⟨3600656, by rfl⟩ : syracuseStep 4800875 = 7201313) B7201313
theorem B967099 : Blo 393766 967099 := bstep (se 1 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 967099 = 1450649) B1450649
theorem B1622591 : Blo 393766 1622591 := bstep (se 1 (by rfl) ⟨1216943, by rfl⟩ : syracuseStep 1622591 = 2433887) B2433887
theorem B6439571 : Blo 393766 6439571 := bstep (se 1 (by rfl) ⟨4829678, by rfl⟩ : syracuseStep 6439571 = 9659357) B9659357
theorem B1426319 : Blo 393766 1426319 := bstep (se 1 (by rfl) ⟨1069739, by rfl⟩ : syracuseStep 1426319 = 2139479) B2139479
theorem B1131545 : Blo 393766 1131545 := bstep (se 2 (by rfl) ⟨424329, by rfl⟩ : syracuseStep 1131545 = 848659) B848659
theorem B1131727 : Blo 393766 1131727 := bstep (se 1 (by rfl) ⟨848795, by rfl⟩ : syracuseStep 1131727 = 1697591) B1697591
theorem B1688843 : Blo 393766 1688843 := bstep (se 1 (by rfl) ⟨1266632, by rfl⟩ : syracuseStep 1688843 = 2533265) B2533265
theorem B443803 : Blo 393766 443803 := bstep (se 1 (by rfl) ⟨332852, by rfl⟩ : syracuseStep 443803 = 665705) B665705
theorem B1132127 : Blo 393766 1132127 := bstep (se 1 (by rfl) ⟨849095, by rfl⟩ : syracuseStep 1132127 = 1698191) B1698191
theorem B1132319 : Blo 393766 1132319 := bstep (se 1 (by rfl) ⟨849239, by rfl⟩ : syracuseStep 1132319 = 1698479) B1698479
theorem B1328993 : Blo 393766 1328993 := bstep (se 2 (by rfl) ⟨498372, by rfl⟩ : syracuseStep 1328993 = 996745) B996745
theorem B10831745 : Blo 393766 10831745 := bstep (se 2 (by rfl) ⟨4061904, by rfl⟩ : syracuseStep 10831745 = 8123809) B8123809
theorem B6735959 : Blo 393766 6735959 := bstep (se 1 (by rfl) ⟨5051969, by rfl⟩ : syracuseStep 6735959 = 10103939) B10103939
theorem B1001767 : Blo 393766 1001767 := bstep (se 1 (by rfl) ⟨751325, by rfl⟩ : syracuseStep 1001767 = 1502651) B1502651
theorem B21711239 : Blo 393766 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B10242541 : Blo 393766 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B444955 : Blo 393766 444955 := bstep (se 1 (by rfl) ⟨333716, by rfl⟩ : syracuseStep 444955 = 667433) B667433
theorem B1329695 : Blo 393766 1329695 := bstep (se 1 (by rfl) ⟨997271, by rfl⟩ : syracuseStep 1329695 = 1994543) B1994543
theorem B22792913 : Blo 393766 22792913 := bstep (se 2 (by rfl) ⟨8547342, by rfl⟩ : syracuseStep 22792913 = 17094685) B17094685
theorem B3033875 : Blo 393766 3033875 := bstep (se 1 (by rfl) ⟨2275406, by rfl⟩ : syracuseStep 3033875 = 4550813) B4550813
theorem B674795 : Blo 393766 674795 := bstep (se 1 (by rfl) ⟨506096, by rfl⟩ : syracuseStep 674795 = 1012193) B1012193
theorem B904171 : Blo 393766 904171 := bstep (se 1 (by rfl) ⟨678128, by rfl⟩ : syracuseStep 904171 = 1356257) B1356257
theorem B1002719 : Blo 393766 1002719 := bstep (se 1 (by rfl) ⟨752039, by rfl⟩ : syracuseStep 1002719 = 1504079) B1504079
theorem B445927 : Blo 393766 445927 := bstep (se 1 (by rfl) ⟨334445, by rfl⟩ : syracuseStep 445927 = 668891) B668891
theorem B1331099 : Blo 393766 1331099 := bstep (se 1 (by rfl) ⟨998324, by rfl⟩ : syracuseStep 1331099 = 1996649) B1996649
theorem B446431 : Blo 393766 446431 := bstep (se 1 (by rfl) ⟨334823, by rfl⟩ : syracuseStep 446431 = 669647) B669647
theorem B905339 : Blo 393766 905339 := bstep (se 1 (by rfl) ⟨679004, by rfl⟩ : syracuseStep 905339 = 1358009) B1358009
theorem B7721249 : Blo 393766 7721249 := bstep (se 2 (by rfl) ⟨2895468, by rfl⟩ : syracuseStep 7721249 = 5790937) B5790937
theorem B447079 : Blo 393766 447079 := bstep (se 1 (by rfl) ⟨335309, by rfl⟩ : syracuseStep 447079 = 670619) B670619
theorem B1266683 : Blo 393766 1266683 := bstep (se 1 (by rfl) ⟨950012, by rfl⟩ : syracuseStep 1266683 = 1900025) B1900025
theorem B1332233 : Blo 393766 1332233 := bstep (se 2 (by rfl) ⟨499587, by rfl⟩ : syracuseStep 1332233 = 999175) B999175
theorem B2413577 : Blo 393766 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B1332287 : Blo 393766 1332287 := bstep (se 1 (by rfl) ⟨999215, by rfl⟩ : syracuseStep 1332287 = 1998431) B1998431
theorem B906515 : Blo 393766 906515 := bstep (se 1 (by rfl) ⟨679886, by rfl⟩ : syracuseStep 906515 = 1359773) B1359773
theorem B2414551 : Blo 393766 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B841927 : Blo 393766 841927 := bstep (se 1 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 841927 = 1262891) B1262891
theorem B1005767 : Blo 393766 1005767 := bstep (se 1 (by rfl) ⟨754325, by rfl⟩ : syracuseStep 1005767 = 1508651) B1508651
theorem B841961 : Blo 393766 841961 := bstep (se 2 (by rfl) ⟨315735, by rfl⟩ : syracuseStep 841961 = 631471) B631471
theorem B2709883 : Blo 393766 2709883 := bstep (se 1 (by rfl) ⟨2032412, by rfl⟩ : syracuseStep 2709883 = 4064825) B4064825
theorem B26368409 : Blo 393766 26368409 := bstep (se 2 (by rfl) ⟨9888153, by rfl⟩ : syracuseStep 26368409 = 19776307) B19776307
theorem B1694141 : Blo 393766 1694141 := bstep (se 3 (by rfl) ⟨317651, by rfl⟩ : syracuseStep 1694141 = 635303) B635303
theorem B1432201 : Blo 393766 1432201 := bstep (se 2 (by rfl) ⟨537075, by rfl⟩ : syracuseStep 1432201 = 1074151) B1074151
theorem B1071955 : Blo 393766 1071955 := bstep (se 1 (by rfl) ⟨803966, by rfl⟩ : syracuseStep 1071955 = 1607933) B1607933
theorem B2251745 : Blo 393766 2251745 := bstep (se 2 (by rfl) ⟨844404, by rfl⟩ : syracuseStep 2251745 = 1688809) B1688809
theorem B14605379 : Blo 393766 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B4775057 : Blo 393766 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B3366035 : Blo 393766 3366035 := bstep (se 1 (by rfl) ⟨2524526, by rfl⟩ : syracuseStep 3366035 = 5049053) B5049053
theorem B1335095 : Blo 393766 1335095 := bstep (se 1 (by rfl) ⟨1001321, by rfl⟩ : syracuseStep 1335095 = 2002643) B2002643
theorem B10182671 : Blo 393766 10182671 := bstep (se 1 (by rfl) ⟨7637003, by rfl⟩ : syracuseStep 10182671 = 15274007) B15274007
theorem B843995 : Blo 393766 843995 := bstep (se 1 (by rfl) ⟨632996, by rfl⟩ : syracuseStep 843995 = 1265993) B1265993
theorem B1335527 : Blo 393766 1335527 := bstep (se 1 (by rfl) ⟨1001645, by rfl⟩ : syracuseStep 1335527 = 2003291) B2003291
theorem B1336121 : Blo 393766 1336121 := bstep (se 2 (by rfl) ⟨501045, by rfl⟩ : syracuseStep 1336121 = 1002091) B1002091
theorem B1336175 : Blo 393766 1336175 := bstep (se 1 (by rfl) ⟨1002131, by rfl⟩ : syracuseStep 1336175 = 2004263) B2004263
theorem B2713171 : Blo 393766 2713171 := bstep (se 1 (by rfl) ⟨2034878, by rfl⟩ : syracuseStep 2713171 = 4069757) B4069757
theorem B1336985 : Blo 393766 1336985 := bstep (se 2 (by rfl) ⟨501369, by rfl⟩ : syracuseStep 1336985 = 1002739) B1002739
theorem B2844503 : Blo 393766 2844503 := bstep (se 1 (by rfl) ⟨2133377, by rfl⟩ : syracuseStep 2844503 = 4266755) B4266755
theorem B845815 : Blo 393766 845815 := bstep (se 1 (by rfl) ⟨634361, by rfl⟩ : syracuseStep 845815 = 1268723) B1268723
theorem B1337579 : Blo 393766 1337579 := bstep (se 1 (by rfl) ⟨1003184, by rfl⟩ : syracuseStep 1337579 = 2006369) B2006369
theorem B2255161 : Blo 393766 2255161 := bstep (se 2 (by rfl) ⟨845685, by rfl⟩ : syracuseStep 2255161 = 1691371) B1691371
theorem B3008825 : Blo 393766 3008825 := bstep (se 2 (by rfl) ⟨1128309, by rfl⟩ : syracuseStep 3008825 = 2256619) B2256619
theorem B7629623 : Blo 393766 7629623 := bstep (se 1 (by rfl) ⟨5722217, by rfl⟩ : syracuseStep 7629623 = 11444435) B11444435
theorem B4516883 : Blo 393766 4516883 := bstep (se 1 (by rfl) ⟨3387662, by rfl⟩ : syracuseStep 4516883 = 6775325) B6775325
theorem B1338875 : Blo 393766 1338875 := bstep (se 1 (by rfl) ⟨1004156, by rfl⟩ : syracuseStep 1338875 = 2008313) B2008313
theorem B716431 : Blo 393766 716431 := bstep (se 1 (by rfl) ⟨537323, by rfl⟩ : syracuseStep 716431 = 1074647) B1074647
theorem B1339037 : Blo 393766 1339037 := bstep (se 3 (by rfl) ⟨251069, by rfl⟩ : syracuseStep 1339037 = 502139) B502139
theorem B749351 : Blo 393766 749351 := bstep (se 1 (by rfl) ⟨562013, by rfl⟩ : syracuseStep 749351 = 1124027) B1124027
theorem B1339577 : Blo 393766 1339577 := bstep (se 2 (by rfl) ⟨502341, by rfl⟩ : syracuseStep 1339577 = 1004683) B1004683
theorem B5435585 : Blo 393766 5435585 := bstep (se 2 (by rfl) ⟨2038344, by rfl⟩ : syracuseStep 5435585 = 4076689) B4076689
theorem B3010769 : Blo 393766 3010769 := bstep (se 2 (by rfl) ⟨1129038, by rfl⟩ : syracuseStep 3010769 = 2258077) B2258077
theorem B1274167 : Blo 393766 1274167 := bstep (se 1 (by rfl) ⟨955625, by rfl⟩ : syracuseStep 1274167 = 1911251) B1911251
theorem B2191865 : Blo 393766 2191865 := bstep (se 2 (by rfl) ⟨821949, by rfl⟩ : syracuseStep 2191865 = 1643899) B1643899
theorem B750073 : Blo 393766 750073 := bstep (se 2 (by rfl) ⟨281277, by rfl⟩ : syracuseStep 750073 = 562555) B562555
theorem B11596385 : Blo 393766 11596385 := bstep (se 2 (by rfl) ⟨4348644, by rfl⟩ : syracuseStep 11596385 = 8697289) B8697289
theorem B750377 : Blo 393766 750377 := bstep (se 2 (by rfl) ⟨281391, by rfl⟩ : syracuseStep 750377 = 562783) B562783
theorem B2257895 : Blo 393766 2257895 := bstep (se 1 (by rfl) ⟨1693421, by rfl⟩ : syracuseStep 2257895 = 3386843) B3386843
theorem B455743 : Blo 393766 455743 := bstep (se 1 (by rfl) ⟨341807, by rfl⟩ : syracuseStep 455743 = 683615) B683615
theorem B1209563 : Blo 393766 1209563 := bstep (se 1 (by rfl) ⟨907172, by rfl⟩ : syracuseStep 1209563 = 1814345) B1814345
theorem B1930823 : Blo 393766 1930823 := bstep (se 1 (by rfl) ⟨1448117, by rfl⟩ : syracuseStep 1930823 = 2896235) B2896235
theorem B685751 : Blo 393766 685751 := bstep (se 1 (by rfl) ⟨514313, by rfl⟩ : syracuseStep 685751 = 1028627) B1028627
theorem B1341683 : Blo 393766 1341683 := bstep (se 1 (by rfl) ⟨1006262, by rfl⟩ : syracuseStep 1341683 = 2012525) B2012525
theorem B1341737 : Blo 393766 1341737 := bstep (se 2 (by rfl) ⟨503151, by rfl⟩ : syracuseStep 1341737 = 1006303) B1006303
theorem B1898795 : Blo 393766 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B1014329 : Blo 393766 1014329 := bstep (se 2 (by rfl) ⟨380373, by rfl⟩ : syracuseStep 1014329 = 760747) B760747
theorem B2259535 : Blo 393766 2259535 := bstep (se 1 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 2259535 = 3389303) B3389303
theorem B3013199 : Blo 393766 3013199 := bstep (se 1 (by rfl) ⟨2259899, by rfl⟩ : syracuseStep 3013199 = 4519799) B4519799
theorem B1145465 : Blo 393766 1145465 := bstep (se 2 (by rfl) ⟨429549, by rfl⟩ : syracuseStep 1145465 = 859099) B859099
theorem B3373721 : Blo 393766 3373721 := bstep (se 2 (by rfl) ⟨1265145, by rfl⟩ : syracuseStep 3373721 = 2530291) B2530291
theorem B3603143 : Blo 393766 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B1375055 : Blo 393766 1375055 := bstep (se 1 (by rfl) ⟨1031291, by rfl⟩ : syracuseStep 1375055 = 2062583) B2062583
theorem B3603365 : Blo 393766 3603365 := bstep (se 4 (by rfl) ⟨337815, by rfl⟩ : syracuseStep 3603365 = 675631) B675631
theorem B752905 : Blo 393766 752905 := bstep (se 2 (by rfl) ⟨282339, by rfl⟩ : syracuseStep 752905 = 564679) B564679
theorem B1900219 : Blo 393766 1900219 := bstep (se 1 (by rfl) ⟨1425164, by rfl⟩ : syracuseStep 1900219 = 2850329) B2850329
theorem B2129789 : Blo 393766 2129789 := bstep (se 3 (by rfl) ⟨399335, by rfl⟩ : syracuseStep 2129789 = 798671) B798671
theorem B3014657 : Blo 393766 3014657 := bstep (se 2 (by rfl) ⟨1130496, by rfl⟩ : syracuseStep 3014657 = 2260993) B2260993
theorem B1081727 : Blo 393766 1081727 := bstep (se 1 (by rfl) ⟨811295, by rfl⟩ : syracuseStep 1081727 = 1622591) B1622591
theorem B917887 : Blo 393766 917887 := bstep (se 1 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 917887 = 1376831) B1376831
theorem B4293047 : Blo 393766 4293047 := bstep (se 1 (by rfl) ⟨3219785, by rfl⟩ : syracuseStep 4293047 = 6439571) B6439571
theorem B950879 : Blo 393766 950879 := bstep (se 1 (by rfl) ⟨713159, by rfl⟩ : syracuseStep 950879 = 1426319) B1426319
theorem B393839 : Blo 393766 393839 := bstep (se 1 (by rfl) ⟨295379, by rfl⟩ : syracuseStep 393839 = 590759) B590759
theorem B393895 : Blo 393766 393895 := bstep (se 1 (by rfl) ⟨295421, by rfl⟩ : syracuseStep 393895 = 590843) B590843
theorem B754363 : Blo 393766 754363 := bstep (se 1 (by rfl) ⟨565772, by rfl⟩ : syracuseStep 754363 = 1131545) B1131545
theorem B393935 : Blo 393766 393935 := bstep (se 1 (by rfl) ⟨295451, by rfl⟩ : syracuseStep 393935 = 590903) B590903
theorem B394015 : Blo 393766 394015 := bstep (se 1 (by rfl) ⟨295511, by rfl⟩ : syracuseStep 394015 = 591023) B591023
theorem B394287 : Blo 393766 394287 := bstep (se 1 (by rfl) ⟨295715, by rfl⟩ : syracuseStep 394287 = 591431) B591431
theorem B754751 : Blo 393766 754751 := bstep (se 1 (by rfl) ⟨566063, by rfl⟩ : syracuseStep 754751 = 1132127) B1132127
theorem B394351 : Blo 393766 394351 := bstep (se 1 (by rfl) ⟨295763, by rfl⟩ : syracuseStep 394351 = 591527) B591527
theorem B394407 : Blo 393766 394407 := bstep (se 1 (by rfl) ⟨295805, by rfl⟩ : syracuseStep 394407 = 591611) B591611
theorem B394431 : Blo 393766 394431 := bstep (se 1 (by rfl) ⟨295823, by rfl⟩ : syracuseStep 394431 = 591647) B591647
theorem B591071 : Blo 393766 591071 := bstep (se 1 (by rfl) ⟨443303, by rfl⟩ : syracuseStep 591071 = 886607) B886607
theorem B394463 : Blo 393766 394463 := bstep (se 1 (by rfl) ⟨295847, by rfl⟩ : syracuseStep 394463 = 591695) B591695
theorem B885995 : Blo 393766 885995 := bstep (se 1 (by rfl) ⟨664496, by rfl⟩ : syracuseStep 885995 = 1328993) B1328993
theorem B591083 : Blo 393766 591083 := bstep (se 1 (by rfl) ⟨443312, by rfl⟩ : syracuseStep 591083 = 886625) B886625
theorem B394543 : Blo 393766 394543 := bstep (se 1 (by rfl) ⟨295907, by rfl⟩ : syracuseStep 394543 = 591815) B591815
theorem B4490639 : Blo 393766 4490639 := bstep (se 1 (by rfl) ⟨3367979, by rfl⟩ : syracuseStep 4490639 = 6735959) B6735959
theorem B394779 : Blo 393766 394779 := bstep (se 1 (by rfl) ⟨296084, by rfl⟩ : syracuseStep 394779 = 592169) B592169
theorem B394783 : Blo 393766 394783 := bstep (se 1 (by rfl) ⟨296087, by rfl⟩ : syracuseStep 394783 = 592175) B592175
theorem B1508969 : Blo 393766 1508969 := bstep (se 2 (by rfl) ⟨565863, by rfl⟩ : syracuseStep 1508969 = 1131727) B1131727
theorem B591467 : Blo 393766 591467 := bstep (se 1 (by rfl) ⟨443600, by rfl⟩ : syracuseStep 591467 = 887201) B887201
theorem B886463 : Blo 393766 886463 := bstep (se 1 (by rfl) ⟨664847, by rfl⟩ : syracuseStep 886463 = 1329695) B1329695
theorem B591551 : Blo 393766 591551 := bstep (se 1 (by rfl) ⟨443663, by rfl⟩ : syracuseStep 591551 = 887327) B887327
theorem B394943 : Blo 393766 394943 := bstep (se 1 (by rfl) ⟨296207, by rfl⟩ : syracuseStep 394943 = 592415) B592415
theorem B591737 : Blo 393766 591737 := bstep (se 2 (by rfl) ⟨221901, by rfl⟩ : syracuseStep 591737 = 443803) B443803
theorem B395199 : Blo 393766 395199 := bstep (se 1 (by rfl) ⟨296399, by rfl⟩ : syracuseStep 395199 = 592799) B592799
theorem B395231 : Blo 393766 395231 := bstep (se 1 (by rfl) ⟨296423, by rfl⟩ : syracuseStep 395231 = 592847) B592847
theorem B395291 : Blo 393766 395291 := bstep (se 1 (by rfl) ⟨296468, by rfl⟩ : syracuseStep 395291 = 592937) B592937
theorem B395295 : Blo 393766 395295 := bstep (se 1 (by rfl) ⟨296471, by rfl⟩ : syracuseStep 395295 = 592943) B592943
theorem B395311 : Blo 393766 395311 := bstep (se 1 (by rfl) ⟨296483, by rfl⟩ : syracuseStep 395311 = 592967) B592967
theorem B395487 : Blo 393766 395487 := bstep (se 1 (by rfl) ⟨296615, by rfl⟩ : syracuseStep 395487 = 593231) B593231
theorem B395547 : Blo 393766 395547 := bstep (se 1 (by rfl) ⟨296660, by rfl⟩ : syracuseStep 395547 = 593321) B593321
theorem B395647 : Blo 393766 395647 := bstep (se 1 (by rfl) ⟨296735, by rfl⟩ : syracuseStep 395647 = 593471) B593471
theorem B395823 : Blo 393766 395823 := bstep (se 1 (by rfl) ⟨296867, by rfl⟩ : syracuseStep 395823 = 593735) B593735
theorem B887399 : Blo 393766 887399 := bstep (se 1 (by rfl) ⟨665549, by rfl⟩ : syracuseStep 887399 = 1331099) B1331099
theorem B592487 : Blo 393766 592487 := bstep (se 1 (by rfl) ⟨444365, by rfl⟩ : syracuseStep 592487 = 888731) B888731
theorem B395879 : Blo 393766 395879 := bstep (se 1 (by rfl) ⟨296909, by rfl⟩ : syracuseStep 395879 = 593819) B593819
theorem B3377821 : Blo 393766 3377821 := bstep (se 3 (by rfl) ⟨633341, by rfl⟩ : syracuseStep 3377821 = 1266683) B1266683
theorem B592679 : Blo 393766 592679 := bstep (se 1 (by rfl) ⟨444509, by rfl⟩ : syracuseStep 592679 = 889019) B889019
theorem B396255 : Blo 393766 396255 := bstep (se 1 (by rfl) ⟨297191, by rfl⟩ : syracuseStep 396255 = 594383) B594383
theorem B887777 : Blo 393766 887777 := bstep (se 2 (by rfl) ⟨332916, by rfl⟩ : syracuseStep 887777 = 665833) B665833
theorem B396283 : Blo 393766 396283 := bstep (se 1 (by rfl) ⟨297212, by rfl⟩ : syracuseStep 396283 = 594425) B594425
theorem B396351 : Blo 393766 396351 := bstep (se 1 (by rfl) ⟨297263, by rfl⟩ : syracuseStep 396351 = 594527) B594527
theorem B593003 : Blo 393766 593003 := bstep (se 1 (by rfl) ⟨444752, by rfl⟩ : syracuseStep 593003 = 889505) B889505
theorem B12782879 : Blo 393766 12782879 := bstep (se 1 (by rfl) ⟨9587159, by rfl⟩ : syracuseStep 12782879 = 19174319) B19174319
theorem B888155 : Blo 393766 888155 := bstep (se 1 (by rfl) ⟨666116, by rfl⟩ : syracuseStep 888155 = 1332233) B1332233
theorem B593243 : Blo 393766 593243 := bstep (se 1 (by rfl) ⟨444932, by rfl⟩ : syracuseStep 593243 = 889865) B889865
theorem B593273 : Blo 393766 593273 := bstep (se 2 (by rfl) ⟨222477, by rfl⟩ : syracuseStep 593273 = 444955) B444955
theorem B888191 : Blo 393766 888191 := bstep (se 1 (by rfl) ⟨666143, by rfl⟩ : syracuseStep 888191 = 1332287) B1332287
theorem B593279 : Blo 393766 593279 := bstep (se 1 (by rfl) ⟨444959, by rfl⟩ : syracuseStep 593279 = 889919) B889919
theorem B396671 : Blo 393766 396671 := bstep (se 1 (by rfl) ⟨297503, by rfl⟩ : syracuseStep 396671 = 595007) B595007
theorem B396699 : Blo 393766 396699 := bstep (se 1 (by rfl) ⟨297524, by rfl⟩ : syracuseStep 396699 = 595049) B595049
theorem B396767 : Blo 393766 396767 := bstep (se 1 (by rfl) ⟨297575, by rfl⟩ : syracuseStep 396767 = 595151) B595151
theorem B396903 : Blo 393766 396903 := bstep (se 1 (by rfl) ⟨297677, by rfl⟩ : syracuseStep 396903 = 595355) B595355
theorem B397051 : Blo 393766 397051 := bstep (se 1 (by rfl) ⟨297788, by rfl⟩ : syracuseStep 397051 = 595577) B595577
theorem B397119 : Blo 393766 397119 := bstep (se 1 (by rfl) ⟨297839, by rfl⟩ : syracuseStep 397119 = 595679) B595679
theorem B397183 : Blo 393766 397183 := bstep (se 1 (by rfl) ⟨297887, by rfl⟩ : syracuseStep 397183 = 595775) B595775
theorem B593903 : Blo 393766 593903 := bstep (se 1 (by rfl) ⟨445427, by rfl⟩ : syracuseStep 593903 = 890855) B890855
theorem B397295 : Blo 393766 397295 := bstep (se 1 (by rfl) ⟨297971, by rfl⟩ : syracuseStep 397295 = 595943) B595943
theorem B593915 : Blo 393766 593915 := bstep (se 1 (by rfl) ⟨445436, by rfl⟩ : syracuseStep 593915 = 890873) B890873
theorem B397307 : Blo 393766 397307 := bstep (se 1 (by rfl) ⟨297980, by rfl⟩ : syracuseStep 397307 = 595961) B595961
theorem B593975 : Blo 393766 593975 := bstep (se 1 (by rfl) ⟨445481, by rfl⟩ : syracuseStep 593975 = 890963) B890963
theorem B397375 : Blo 393766 397375 := bstep (se 1 (by rfl) ⟨298031, by rfl⟩ : syracuseStep 397375 = 596063) B596063
theorem B594023 : Blo 393766 594023 := bstep (se 1 (by rfl) ⟨445517, by rfl⟩ : syracuseStep 594023 = 891035) B891035
theorem B397415 : Blo 393766 397415 := bstep (se 1 (by rfl) ⟨298061, by rfl⟩ : syracuseStep 397415 = 596123) B596123
theorem B397439 : Blo 393766 397439 := bstep (se 1 (by rfl) ⟨298079, by rfl⟩ : syracuseStep 397439 = 596159) B596159
theorem B397467 : Blo 393766 397467 := bstep (se 1 (by rfl) ⟨298100, by rfl⟩ : syracuseStep 397467 = 596201) B596201
theorem B594095 : Blo 393766 594095 := bstep (se 1 (by rfl) ⟨445571, by rfl⟩ : syracuseStep 594095 = 891143) B891143
theorem B14094691 : Blo 393766 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B397671 : Blo 393766 397671 := bstep (se 1 (by rfl) ⟨298253, by rfl⟩ : syracuseStep 397671 = 596507) B596507
theorem B594299 : Blo 393766 594299 := bstep (se 1 (by rfl) ⟨445724, by rfl⟩ : syracuseStep 594299 = 891449) B891449
theorem B397723 : Blo 393766 397723 := bstep (se 1 (by rfl) ⟨298292, by rfl⟩ : syracuseStep 397723 = 596585) B596585
theorem B594569 : Blo 393766 594569 := bstep (se 2 (by rfl) ⟨222963, by rfl⟩ : syracuseStep 594569 = 445927) B445927
theorem B9736919 : Blo 393766 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B3019517 : Blo 393766 3019517 := bstep (se 3 (by rfl) ⟨566159, by rfl⟩ : syracuseStep 3019517 = 1132319) B1132319
theorem B3183371 : Blo 393766 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B594779 : Blo 393766 594779 := bstep (se 1 (by rfl) ⟨446084, by rfl⟩ : syracuseStep 594779 = 892169) B892169
theorem B955241 : Blo 393766 955241 := bstep (se 2 (by rfl) ⟨358215, by rfl⟩ : syracuseStep 955241 = 716431) B716431
theorem B890063 : Blo 393766 890063 := bstep (se 1 (by rfl) ⟨667547, by rfl⟩ : syracuseStep 890063 = 1335095) B1335095
theorem B890153 : Blo 393766 890153 := bstep (se 2 (by rfl) ⟨333807, by rfl⟩ : syracuseStep 890153 = 667615) B667615
theorem B595241 : Blo 393766 595241 := bstep (se 2 (by rfl) ⟨223215, by rfl⟩ : syracuseStep 595241 = 446431) B446431
theorem B6788447 : Blo 393766 6788447 := bstep (se 1 (by rfl) ⟨5091335, by rfl⟩ : syracuseStep 6788447 = 10182671) B10182671
theorem B562663 : Blo 393766 562663 := bstep (se 1 (by rfl) ⟨421997, by rfl⟩ : syracuseStep 562663 = 843995) B843995
theorem B890351 : Blo 393766 890351 := bstep (se 1 (by rfl) ⟨667763, by rfl⟩ : syracuseStep 890351 = 1335527) B1335527
theorem B595439 : Blo 393766 595439 := bstep (se 1 (by rfl) ⟨446579, by rfl⟩ : syracuseStep 595439 = 893159) B893159
theorem B890747 : Blo 393766 890747 := bstep (se 1 (by rfl) ⟨668060, by rfl⟩ : syracuseStep 890747 = 1336121) B1336121
theorem B595835 : Blo 393766 595835 := bstep (se 1 (by rfl) ⟨446876, by rfl⟩ : syracuseStep 595835 = 893753) B893753
theorem B890783 : Blo 393766 890783 := bstep (se 1 (by rfl) ⟨668087, by rfl⟩ : syracuseStep 890783 = 1336175) B1336175
theorem B595871 : Blo 393766 595871 := bstep (se 1 (by rfl) ⟨446903, by rfl⟩ : syracuseStep 595871 = 893807) B893807
theorem B891017 : Blo 393766 891017 := bstep (se 2 (by rfl) ⟨334131, by rfl⟩ : syracuseStep 891017 = 668263) B668263
theorem B596105 : Blo 393766 596105 := bstep (se 2 (by rfl) ⟨223539, by rfl⟩ : syracuseStep 596105 = 447079) B447079
theorem B596255 : Blo 393766 596255 := bstep (se 1 (by rfl) ⟨447191, by rfl⟩ : syracuseStep 596255 = 894383) B894383
theorem B891233 : Blo 393766 891233 := bstep (se 2 (by rfl) ⟨334212, by rfl⟩ : syracuseStep 891233 = 668425) B668425
theorem B891323 : Blo 393766 891323 := bstep (se 1 (by rfl) ⟨668492, by rfl⟩ : syracuseStep 891323 = 1336985) B1336985
theorem B891719 : Blo 393766 891719 := bstep (se 1 (by rfl) ⟨668789, by rfl⟩ : syracuseStep 891719 = 1337579) B1337579
theorem B2005883 : Blo 393766 2005883 := bstep (se 1 (by rfl) ⟨1504412, by rfl⟩ : syracuseStep 2005883 = 3008825) B3008825
theorem B5479505 : Blo 393766 5479505 := bstep (se 2 (by rfl) ⟨2054814, by rfl⟩ : syracuseStep 5479505 = 4109629) B4109629
theorem B892025 : Blo 393766 892025 := bstep (se 2 (by rfl) ⟨334509, by rfl⟩ : syracuseStep 892025 = 669019) B669019
theorem B9608381 : Blo 393766 9608381 := bstep (se 3 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 9608381 = 3603143) B3603143
theorem B5086415 : Blo 393766 5086415 := bstep (se 1 (by rfl) ⟨3814811, by rfl⟩ : syracuseStep 5086415 = 7629623) B7629623
theorem B892583 : Blo 393766 892583 := bstep (se 1 (by rfl) ⟨669437, by rfl⟩ : syracuseStep 892583 = 1338875) B1338875
theorem B892691 : Blo 393766 892691 := bstep (se 1 (by rfl) ⟨669518, by rfl⟩ : syracuseStep 892691 = 1339037) B1339037
theorem B3219401 : Blo 393766 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B893051 : Blo 393766 893051 := bstep (se 1 (by rfl) ⟨669788, by rfl⟩ : syracuseStep 893051 = 1339577) B1339577
theorem B2007179 : Blo 393766 2007179 := bstep (se 1 (by rfl) ⟨1505384, by rfl⟩ : syracuseStep 2007179 = 3010769) B3010769
theorem B1122569 : Blo 393766 1122569 := bstep (se 2 (by rfl) ⟨420963, by rfl⟩ : syracuseStep 1122569 = 841927) B841927
theorem B893321 : Blo 393766 893321 := bstep (se 2 (by rfl) ⟨334995, by rfl⟩ : syracuseStep 893321 = 669991) B669991
theorem B3613177 : Blo 393766 3613177 := bstep (se 2 (by rfl) ⟨1354941, by rfl⟩ : syracuseStep 3613177 = 2709883) B2709883
theorem B500251 : Blo 393766 500251 := bstep (se 1 (by rfl) ⟨375188, by rfl⟩ : syracuseStep 500251 = 750377) B750377
theorem B2040403 : Blo 393766 2040403 := bstep (se 1 (by rfl) ⟨1530302, by rfl⟩ : syracuseStep 2040403 = 3060605) B3060605
theorem B7709357 : Blo 393766 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B1909601 : Blo 393766 1909601 := bstep (se 2 (by rfl) ⟨716100, by rfl⟩ : syracuseStep 1909601 = 1432201) B1432201
theorem B1287215 : Blo 393766 1287215 := bstep (se 1 (by rfl) ⟨965411, by rfl⟩ : syracuseStep 1287215 = 1930823) B1930823
theorem B894455 : Blo 393766 894455 := bstep (se 1 (by rfl) ⟨670841, by rfl⟩ : syracuseStep 894455 = 1341683) B1341683
theorem B894491 : Blo 393766 894491 := bstep (se 1 (by rfl) ⟨670868, by rfl⟩ : syracuseStep 894491 = 1341737) B1341737
theorem B2008799 : Blo 393766 2008799 := bstep (se 1 (by rfl) ⟨1506599, by rfl⟩ : syracuseStep 2008799 = 3013199) B3013199
theorem B763643 : Blo 393766 763643 := bstep (se 1 (by rfl) ⟨572732, by rfl⟩ : syracuseStep 763643 = 1145465) B1145465
theorem B2402243 : Blo 393766 2402243 := bstep (se 1 (by rfl) ⟨1801682, by rfl⟩ : syracuseStep 2402243 = 3603365) B3603365
theorem B2533625 : Blo 393766 2533625 := bstep (se 2 (by rfl) ⟨950109, by rfl⟩ : syracuseStep 2533625 = 1900219) B1900219
theorem B666103 : Blo 393766 666103 := bstep (se 1 (by rfl) ⟨499577, by rfl⟩ : syracuseStep 666103 = 999155) B999155
theorem B1419859 : Blo 393766 1419859 := bstep (se 1 (by rfl) ⟨1064894, by rfl⟩ : syracuseStep 1419859 = 2129789) B2129789
theorem B666697 : Blo 393766 666697 := bstep (se 2 (by rfl) ⟨250011, by rfl⟩ : syracuseStep 666697 = 500023) B500023
theorem B1289465 : Blo 393766 1289465 := bstep (se 2 (by rfl) ⟨483549, by rfl⟩ : syracuseStep 1289465 = 967099) B967099
theorem B20589997 : Blo 393766 20589997 := bstep (se 3 (by rfl) ⟨3860624, by rfl⟩ : syracuseStep 20589997 = 7721249) B7721249
theorem B503263 : Blo 393766 503263 := bstep (se 1 (by rfl) ⟨377447, by rfl⟩ : syracuseStep 503263 = 754895) B754895
theorem B1125895 : Blo 393766 1125895 := bstep (se 1 (by rfl) ⟨844421, by rfl⟩ : syracuseStep 1125895 = 1688843) B1688843
theorem B7221163 : Blo 393766 7221163 := bstep (se 1 (by rfl) ⟨5415872, by rfl⟩ : syracuseStep 7221163 = 10831745) B10831745
theorem B5844973 : Blo 393766 5844973 := bstep (se 3 (by rfl) ⟨1095932, by rfl⟩ : syracuseStep 5844973 = 2191865) B2191865
theorem B3420589 : Blo 393766 3420589 := bstep (se 3 (by rfl) ⟨641360, by rfl⟩ : syracuseStep 3420589 = 1282721) B1282721
theorem B3617561 : Blo 393766 3617561 := bstep (se 2 (by rfl) ⟨1356585, by rfl⟩ : syracuseStep 3617561 = 2713171) B2713171
theorem B668479 : Blo 393766 668479 := bstep (se 1 (by rfl) ⟨501359, by rfl⟩ : syracuseStep 668479 = 1002719) B1002719
theorem B1684435 : Blo 393766 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B1127753 : Blo 393766 1127753 := bstep (se 2 (by rfl) ⟨422907, by rfl⟩ : syracuseStep 1127753 = 845815) B845815
theorem B6436205 : Blo 393766 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B603559 : Blo 393766 603559 := bstep (se 1 (by rfl) ⟨452669, by rfl⟩ : syracuseStep 603559 = 905339) B905339
theorem B604343 : Blo 393766 604343 := bstep (se 1 (by rfl) ⟨453257, by rfl⟩ : syracuseStep 604343 = 906515) B906515
theorem B670511 : Blo 393766 670511 := bstep (se 1 (by rfl) ⟨502883, by rfl⟩ : syracuseStep 670511 = 1005767) B1005767
theorem B17578939 : Blo 393766 17578939 := bstep (se 1 (by rfl) ⟨13184204, by rfl⟩ : syracuseStep 17578939 = 26368409) B26368409
theorem B1129427 : Blo 393766 1129427 := bstep (se 1 (by rfl) ⟨847070, by rfl⟩ : syracuseStep 1129427 = 1694141) B1694141
theorem B3194099 : Blo 393766 3194099 := bstep (se 1 (by rfl) ⟨2395574, by rfl⟩ : syracuseStep 3194099 = 4791149) B4791149
theorem B41270627 : Blo 393766 41270627 := bstep (se 1 (by rfl) ⟨30952970, by rfl⟩ : syracuseStep 41270627 = 61905941) B61905941
theorem B2244023 : Blo 393766 2244023 := bstep (se 1 (by rfl) ⟨1683017, by rfl⟩ : syracuseStep 2244023 = 3366035) B3366035
theorem B2245229 : Blo 393766 2245229 := bstep (se 3 (by rfl) ⟨420980, by rfl⟩ : syracuseStep 2245229 = 841961) B841961
theorem B1000097 : Blo 393766 1000097 := bstep (se 2 (by rfl) ⟨375036, by rfl⟩ : syracuseStep 1000097 = 750073) B750073
theorem B443047 : Blo 393766 443047 := bstep (se 1 (by rfl) ⟨332285, by rfl⟩ : syracuseStep 443047 = 664571) B664571
theorem B443335 : Blo 393766 443335 := bstep (se 1 (by rfl) ⟨332501, by rfl⟩ : syracuseStep 443335 = 665003) B665003
theorem B3785903 : Blo 393766 3785903 := bstep (se 1 (by rfl) ⟨2839427, by rfl⟩ : syracuseStep 3785903 = 5678855) B5678855
theorem B443695 : Blo 393766 443695 := bstep (se 1 (by rfl) ⟨332771, by rfl⟩ : syracuseStep 443695 = 665543) B665543
theorem B607657 : Blo 393766 607657 := bstep (se 2 (by rfl) ⟨227871, by rfl⟩ : syracuseStep 607657 = 455743) B455743
theorem B444199 : Blo 393766 444199 := bstep (se 1 (by rfl) ⟨333149, by rfl⟩ : syracuseStep 444199 = 666299) B666299
theorem B3820121 : Blo 393766 3820121 := bstep (se 2 (by rfl) ⟨1432545, by rfl⟩ : syracuseStep 3820121 = 2865091) B2865091
theorem B3426961 : Blo 393766 3426961 := bstep (se 2 (by rfl) ⟨1285110, by rfl⟩ : syracuseStep 3426961 = 2570221) B2570221
theorem B3623723 : Blo 393766 3623723 := bstep (se 1 (by rfl) ⟨2717792, by rfl⟩ : syracuseStep 3623723 = 5435585) B5435585
theorem B2247689 : Blo 393766 2247689 := bstep (se 2 (by rfl) ⟨842883, by rfl⟩ : syracuseStep 2247689 = 1685767) B1685767
theorem B806375 : Blo 393766 806375 := bstep (se 1 (by rfl) ⟨604781, by rfl⟩ : syracuseStep 806375 = 1209563) B1209563
theorem B1429273 : Blo 393766 1429273 := bstep (se 2 (by rfl) ⟨535977, by rfl⟩ : syracuseStep 1429273 = 1071955) B1071955
theorem B4050917 : Blo 393766 4050917 := bstep (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) B759547
theorem B1265863 : Blo 393766 1265863 := bstep (se 1 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 1265863 = 1898795) B1898795
theorem B1003873 : Blo 393766 1003873 := bstep (se 2 (by rfl) ⟨376452, by rfl⟩ : syracuseStep 1003873 = 752905) B752905
theorem B676219 : Blo 393766 676219 := bstep (se 1 (by rfl) ⟨507164, by rfl⟩ : syracuseStep 676219 = 1014329) B1014329
theorem B2249147 : Blo 393766 2249147 := bstep (se 1 (by rfl) ⟨1686860, by rfl⟩ : syracuseStep 2249147 = 3373721) B3373721
theorem B1495529 : Blo 393766 1495529 := bstep (se 2 (by rfl) ⟨560823, by rfl⟩ : syracuseStep 1495529 = 1121647) B1121647
theorem B447295 : Blo 393766 447295 := bstep (se 1 (by rfl) ⟨335471, by rfl⟩ : syracuseStep 447295 = 670943) B670943
theorem B906223 : Blo 393766 906223 := bstep (se 1 (by rfl) ⟨679667, by rfl⟩ : syracuseStep 906223 = 1359335) B1359335
theorem B1266941 : Blo 393766 1266941 := bstep (se 3 (by rfl) ⟨237551, by rfl⟩ : syracuseStep 1266941 = 475103) B475103
theorem B1332719 : Blo 393766 1332719 := bstep (se 1 (by rfl) ⟨999539, by rfl⟩ : syracuseStep 1332719 = 1999079) B1999079
theorem B7296551 : Blo 393766 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B3364699 : Blo 393766 3364699 := bstep (se 1 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 3364699 = 5047049) B5047049
theorem B1923041 : Blo 393766 1923041 := bstep (se 2 (by rfl) ⟨721140, by rfl⟩ : syracuseStep 1923041 = 1442281) B1442281
theorem B12802333 : Blo 393766 12802333 := bstep (se 3 (by rfl) ⟨2400437, by rfl⟩ : syracuseStep 12802333 = 4800875) B4800875
theorem B1333691 : Blo 393766 1333691 := bstep (se 1 (by rfl) ⟨1000268, by rfl⟩ : syracuseStep 1333691 = 2000537) B2000537
theorem B14474159 : Blo 393766 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B15195275 : Blo 393766 15195275 := bstep (se 1 (by rfl) ⟨11396456, by rfl⟩ : syracuseStep 15195275 = 22792913) B22792913
theorem B2022583 : Blo 393766 2022583 := bstep (se 1 (by rfl) ⟨1516937, by rfl⟩ : syracuseStep 2022583 = 3033875) B3033875
theorem B2252063 : Blo 393766 2252063 := bstep (se 1 (by rfl) ⟨1689047, by rfl⟩ : syracuseStep 2252063 = 3378095) B3378095
theorem B1597427 : Blo 393766 1597427 := bstep (se 1 (by rfl) ⟨1198070, by rfl⟩ : syracuseStep 1597427 = 2396141) B2396141
theorem B1335419 : Blo 393766 1335419 := bstep (se 1 (by rfl) ⟨1001564, by rfl⟩ : syracuseStep 1335419 = 2003129) B2003129
theorem B1499417 : Blo 393766 1499417 := bstep (se 2 (by rfl) ⟨562281, by rfl⟩ : syracuseStep 1499417 = 1124563) B1124563
theorem B1335581 : Blo 393766 1335581 := bstep (se 3 (by rfl) ⟨250421, by rfl⟩ : syracuseStep 1335581 = 500843) B500843
theorem B1335689 : Blo 393766 1335689 := bstep (se 2 (by rfl) ⟨500883, by rfl⟩ : syracuseStep 1335689 = 1001767) B1001767
theorem B3006881 : Blo 393766 3006881 := bstep (se 2 (by rfl) ⟨1127580, by rfl⟩ : syracuseStep 3006881 = 2255161) B2255161
theorem B9527759 : Blo 393766 9527759 := bstep (se 1 (by rfl) ⟨7145819, by rfl⟩ : syracuseStep 9527759 = 14291639) B14291639
theorem B13656721 : Blo 393766 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B1205561 : Blo 393766 1205561 := bstep (se 2 (by rfl) ⟨452085, by rfl⟩ : syracuseStep 1205561 = 904171) B904171
theorem B1336823 : Blo 393766 1336823 := bstep (se 1 (by rfl) ⟨1002617, by rfl⟩ : syracuseStep 1336823 = 2005235) B2005235
theorem B1828669 : Blo 393766 1828669 := bstep (se 3 (by rfl) ⟨342875, by rfl⟩ : syracuseStep 1828669 = 685751) B685751
theorem B1501163 : Blo 393766 1501163 := bstep (se 1 (by rfl) ⟨1125872, by rfl⟩ : syracuseStep 1501163 = 2251745) B2251745
theorem B1272311 : Blo 393766 1272311 := bstep (se 1 (by rfl) ⟨954233, by rfl⟩ : syracuseStep 1272311 = 1908467) B1908467
theorem B1337903 : Blo 393766 1337903 := bstep (se 1 (by rfl) ⟨1003427, by rfl⟩ : syracuseStep 1337903 = 2006855) B2006855
theorem B3370031 : Blo 393766 3370031 := bstep (se 1 (by rfl) ⟨2527523, by rfl⟩ : syracuseStep 3370031 = 5055047) B5055047
theorem B748615 : Blo 393766 748615 := bstep (se 1 (by rfl) ⟨561461, by rfl⟩ : syracuseStep 748615 = 1122923) B1122923
theorem B1698889 : Blo 393766 1698889 := bstep (se 2 (by rfl) ⟨637083, by rfl⟩ : syracuseStep 1698889 = 1274167) B1274167
theorem B1338551 : Blo 393766 1338551 := bstep (se 1 (by rfl) ⟨1003913, by rfl⟩ : syracuseStep 1338551 = 2007827) B2007827
theorem B5434937 : Blo 393766 5434937 := bstep (se 2 (by rfl) ⟨2038101, by rfl⟩ : syracuseStep 5434937 = 4076203) B4076203
theorem B1896335 : Blo 393766 1896335 := bstep (se 1 (by rfl) ⟨1422251, by rfl⟩ : syracuseStep 1896335 = 2844503) B2844503
theorem B1503305 : Blo 393766 1503305 := bstep (se 2 (by rfl) ⟨563739, by rfl⟩ : syracuseStep 1503305 = 1127479) B1127479
theorem B3011255 : Blo 393766 3011255 := bstep (se 1 (by rfl) ⟨2258441, by rfl⟩ : syracuseStep 3011255 = 4516883) B4516883
theorem B1995515 : Blo 393766 1995515 := bstep (se 1 (by rfl) ⟨1496636, by rfl⟩ : syracuseStep 1995515 = 2993273) B2993273
theorem B881455 : Blo 393766 881455 := bstep (se 1 (by rfl) ⟨661091, by rfl⟩ : syracuseStep 881455 = 1322183) B1322183
theorem B46330865 : Blo 393766 46330865 := bstep (se 2 (by rfl) ⟨17374074, by rfl⟩ : syracuseStep 46330865 = 34748149) B34748149
theorem B849001 : Blo 393766 849001 := bstep (se 2 (by rfl) ⟨318375, by rfl⟩ : syracuseStep 849001 = 636751) B636751
theorem B1799453 : Blo 393766 1799453 := bstep (se 3 (by rfl) ⟨337397, by rfl⟩ : syracuseStep 1799453 = 674795) B674795
theorem B423407 : Blo 393766 423407 := bstep (se 1 (by rfl) ⟨317555, by rfl⟩ : syracuseStep 423407 = 635111) B635111
theorem B947803 : Blo 393766 947803 := bstep (se 1 (by rfl) ⟨710852, by rfl⟩ : syracuseStep 947803 = 1421705) B1421705
theorem B7730923 : Blo 393766 7730923 := bstep (se 1 (by rfl) ⟨5798192, by rfl⟩ : syracuseStep 7730923 = 11596385) B11596385
theorem B1505081 : Blo 393766 1505081 := bstep (se 2 (by rfl) ⟨564405, by rfl⟩ : syracuseStep 1505081 = 1128811) B1128811
theorem B7698341 : Blo 393766 7698341 := bstep (se 4 (by rfl) ⟨721719, by rfl⟩ : syracuseStep 7698341 = 1443439) B1443439
theorem B751531 : Blo 393766 751531 := bstep (se 1 (by rfl) ⟨563648, by rfl⟩ : syracuseStep 751531 = 1127297) B1127297
theorem B1505263 : Blo 393766 1505263 := bstep (se 1 (by rfl) ⟨1128947, by rfl⟩ : syracuseStep 1505263 = 2257895) B2257895
theorem B3012713 : Blo 393766 3012713 := bstep (se 2 (by rfl) ⟨1129767, by rfl⟩ : syracuseStep 3012713 = 2259535) B2259535
theorem B1014401 : Blo 393766 1014401 := bstep (se 2 (by rfl) ⟨380400, by rfl⟩ : syracuseStep 1014401 = 760801) B760801
theorem B1997459 : Blo 393766 1997459 := bstep (se 1 (by rfl) ⟨1498094, by rfl⟩ : syracuseStep 1997459 = 2996189) B2996189
theorem B916703 : Blo 393766 916703 := bstep (se 1 (by rfl) ⟨687527, by rfl⟩ : syracuseStep 916703 = 1375055) B1375055
theorem B1998269 : Blo 393766 1998269 := bstep (se 3 (by rfl) ⟨374675, by rfl⟩ : syracuseStep 1998269 = 749351) B749351
theorem B753619 : Blo 393766 753619 := bstep (se 1 (by rfl) ⟨565214, by rfl⟩ : syracuseStep 753619 = 1130429) B1130429
theorem B4489181 : Blo 393766 4489181 := bstep (se 3 (by rfl) ⟨841721, by rfl⟩ : syracuseStep 4489181 = 1683443) B1683443
theorem B721151 : Blo 393766 721151 := bstep (se 1 (by rfl) ⟨540863, by rfl⟩ : syracuseStep 721151 = 1081727) B1081727
theorem B4817569 : Blo 393766 4817569 := bstep (se 2 (by rfl) ⟨1806588, by rfl⟩ : syracuseStep 4817569 = 3613177) B3613177
theorem B2720537 : Blo 393766 2720537 := bstep (se 2 (by rfl) ⟨1020201, by rfl⟩ : syracuseStep 2720537 = 2040403) B2040403
theorem B2523935 : Blo 393766 2523935 := bstep (se 1 (by rfl) ⟨1892951, by rfl⟩ : syracuseStep 2523935 = 3785903) B3785903
theorem B394047 : Blo 393766 394047 := bstep (se 1 (by rfl) ⟨295535, by rfl⟩ : syracuseStep 394047 = 591071) B591071
theorem B590663 : Blo 393766 590663 := bstep (se 1 (by rfl) ⟨442997, by rfl⟩ : syracuseStep 590663 = 885995) B885995
theorem B394055 : Blo 393766 394055 := bstep (se 1 (by rfl) ⟨295541, by rfl⟩ : syracuseStep 394055 = 591083) B591083
theorem B590729 : Blo 393766 590729 := bstep (se 2 (by rfl) ⟨221523, by rfl⟩ : syracuseStep 590729 = 443047) B443047
theorem B394311 : Blo 393766 394311 := bstep (se 1 (by rfl) ⟨295733, by rfl⟩ : syracuseStep 394311 = 591467) B591467
theorem B590975 : Blo 393766 590975 := bstep (se 1 (by rfl) ⟨443231, by rfl⟩ : syracuseStep 590975 = 886463) B886463
theorem B394367 : Blo 393766 394367 := bstep (se 1 (by rfl) ⟨295775, by rfl⟩ : syracuseStep 394367 = 591551) B591551
theorem B394491 : Blo 393766 394491 := bstep (se 1 (by rfl) ⟨295868, by rfl⟩ : syracuseStep 394491 = 591737) B591737
theorem B591113 : Blo 393766 591113 := bstep (se 2 (by rfl) ⟨221667, by rfl⟩ : syracuseStep 591113 = 443335) B443335
theorem B591593 : Blo 393766 591593 := bstep (se 2 (by rfl) ⟨221847, by rfl⟩ : syracuseStep 591593 = 443695) B443695
theorem B591599 : Blo 393766 591599 := bstep (se 1 (by rfl) ⟨443699, by rfl⟩ : syracuseStep 591599 = 887399) B887399
theorem B394991 : Blo 393766 394991 := bstep (se 1 (by rfl) ⟨296243, by rfl⟩ : syracuseStep 394991 = 592487) B592487
theorem B75171685 : Blo 393766 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B395119 : Blo 393766 395119 := bstep (se 1 (by rfl) ⟨296339, by rfl⟩ : syracuseStep 395119 = 592679) B592679
theorem B591851 : Blo 393766 591851 := bstep (se 1 (by rfl) ⟨443888, by rfl⟩ : syracuseStep 591851 = 887777) B887777
theorem B395335 : Blo 393766 395335 := bstep (se 1 (by rfl) ⟨296501, by rfl⟩ : syracuseStep 395335 = 593003) B593003
theorem B8521919 : Blo 393766 8521919 := bstep (se 1 (by rfl) ⟨6391439, by rfl⟩ : syracuseStep 8521919 = 12782879) B12782879
theorem B592103 : Blo 393766 592103 := bstep (se 1 (by rfl) ⟨444077, by rfl⟩ : syracuseStep 592103 = 888155) B888155
theorem B395495 : Blo 393766 395495 := bstep (se 1 (by rfl) ⟨296621, by rfl⟩ : syracuseStep 395495 = 593243) B593243
theorem B395515 : Blo 393766 395515 := bstep (se 1 (by rfl) ⟨296636, by rfl⟩ : syracuseStep 395515 = 593273) B593273
theorem B592127 : Blo 393766 592127 := bstep (se 1 (by rfl) ⟨444095, by rfl⟩ : syracuseStep 592127 = 888191) B888191
theorem B395519 : Blo 393766 395519 := bstep (se 1 (by rfl) ⟨296639, by rfl⟩ : syracuseStep 395519 = 593279) B593279
theorem B592265 : Blo 393766 592265 := bstep (se 2 (by rfl) ⟨222099, by rfl⟩ : syracuseStep 592265 = 444199) B444199
theorem B395935 : Blo 393766 395935 := bstep (se 1 (by rfl) ⟨296951, by rfl⟩ : syracuseStep 395935 = 593903) B593903
theorem B395943 : Blo 393766 395943 := bstep (se 1 (by rfl) ⟨296957, by rfl⟩ : syracuseStep 395943 = 593915) B593915
theorem B395983 : Blo 393766 395983 := bstep (se 1 (by rfl) ⟨296987, by rfl⟩ : syracuseStep 395983 = 593975) B593975
theorem B396015 : Blo 393766 396015 := bstep (se 1 (by rfl) ⟨297011, by rfl⟩ : syracuseStep 396015 = 594023) B594023
theorem B396063 : Blo 393766 396063 := bstep (se 1 (by rfl) ⟨297047, by rfl⟩ : syracuseStep 396063 = 594095) B594095
theorem B396199 : Blo 393766 396199 := bstep (se 1 (by rfl) ⟨297149, by rfl⟩ : syracuseStep 396199 = 594299) B594299
theorem B396379 : Blo 393766 396379 := bstep (se 1 (by rfl) ⟨297284, by rfl⟩ : syracuseStep 396379 = 594569) B594569
theorem B6491279 : Blo 393766 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B396519 : Blo 393766 396519 := bstep (se 1 (by rfl) ⟨297389, by rfl⟩ : syracuseStep 396519 = 594779) B594779
theorem B888137 : Blo 393766 888137 := bstep (se 2 (by rfl) ⟨333051, by rfl⟩ : syracuseStep 888137 = 666103) B666103
theorem B593375 : Blo 393766 593375 := bstep (se 1 (by rfl) ⟨445031, by rfl⟩ : syracuseStep 593375 = 890063) B890063
theorem B3214829 : Blo 393766 3214829 := bstep (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) B1205561
theorem B593435 : Blo 393766 593435 := bstep (se 1 (by rfl) ⟨445076, by rfl⟩ : syracuseStep 593435 = 890153) B890153
theorem B396827 : Blo 393766 396827 := bstep (se 1 (by rfl) ⟨297620, by rfl⟩ : syracuseStep 396827 = 595241) B595241
theorem B4525631 : Blo 393766 4525631 := bstep (se 1 (by rfl) ⟨3394223, by rfl⟩ : syracuseStep 4525631 = 6788447) B6788447
theorem B888479 : Blo 393766 888479 := bstep (se 1 (by rfl) ⟨666359, by rfl⟩ : syracuseStep 888479 = 1332719) B1332719
theorem B593567 : Blo 393766 593567 := bstep (se 1 (by rfl) ⟨445175, by rfl⟩ : syracuseStep 593567 = 890351) B890351
theorem B396959 : Blo 393766 396959 := bstep (se 1 (by rfl) ⟨297719, by rfl⟩ : syracuseStep 396959 = 595439) B595439
theorem B593831 : Blo 393766 593831 := bstep (se 1 (by rfl) ⟨445373, by rfl⟩ : syracuseStep 593831 = 890747) B890747
theorem B397223 : Blo 393766 397223 := bstep (se 1 (by rfl) ⟨297917, by rfl⟩ : syracuseStep 397223 = 595835) B595835
theorem B593855 : Blo 393766 593855 := bstep (se 1 (by rfl) ⟨445391, by rfl⟩ : syracuseStep 593855 = 890783) B890783
theorem B397247 : Blo 393766 397247 := bstep (se 1 (by rfl) ⟨297935, by rfl⟩ : syracuseStep 397247 = 595871) B595871
theorem B1282027 : Blo 393766 1282027 := bstep (se 1 (by rfl) ⟨961520, by rfl⟩ : syracuseStep 1282027 = 1923041) B1923041
theorem B594011 : Blo 393766 594011 := bstep (se 1 (by rfl) ⟨445508, by rfl⟩ : syracuseStep 594011 = 891017) B891017
theorem B397403 : Blo 393766 397403 := bstep (se 1 (by rfl) ⟨298052, by rfl⟩ : syracuseStep 397403 = 596105) B596105
theorem B888929 : Blo 393766 888929 := bstep (se 2 (by rfl) ⟨333348, by rfl⟩ : syracuseStep 888929 = 666697) B666697
theorem B2265185 : Blo 393766 2265185 := bstep (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) B1698889
theorem B397503 : Blo 393766 397503 := bstep (se 1 (by rfl) ⟨298127, by rfl⟩ : syracuseStep 397503 = 596255) B596255
theorem B594155 : Blo 393766 594155 := bstep (se 1 (by rfl) ⟨445616, by rfl⟩ : syracuseStep 594155 = 891233) B891233
theorem B889127 : Blo 393766 889127 := bstep (se 1 (by rfl) ⟨666845, by rfl⟩ : syracuseStep 889127 = 1333691) B1333691
theorem B594215 : Blo 393766 594215 := bstep (se 1 (by rfl) ⟨445661, by rfl⟩ : syracuseStep 594215 = 891323) B891323
theorem B594479 : Blo 393766 594479 := bstep (se 1 (by rfl) ⟨445859, by rfl⟩ : syracuseStep 594479 = 891719) B891719
theorem B594683 : Blo 393766 594683 := bstep (se 1 (by rfl) ⟨446012, by rfl⟩ : syracuseStep 594683 = 892025) B892025
theorem B10130183 : Blo 393766 10130183 := bstep (se 1 (by rfl) ⟨7597637, by rfl⟩ : syracuseStep 10130183 = 15195275) B15195275
theorem B1905697 : Blo 393766 1905697 := bstep (se 2 (by rfl) ⟨714636, by rfl⟩ : syracuseStep 1905697 = 1429273) B1429273
theorem B595055 : Blo 393766 595055 := bstep (se 1 (by rfl) ⟨446291, by rfl⟩ : syracuseStep 595055 = 892583) B892583
theorem B595127 : Blo 393766 595127 := bstep (se 1 (by rfl) ⟨446345, by rfl⟩ : syracuseStep 595127 = 892691) B892691
theorem B890279 : Blo 393766 890279 := bstep (se 1 (by rfl) ⟨667709, by rfl⟩ : syracuseStep 890279 = 1335419) B1335419
theorem B595367 : Blo 393766 595367 := bstep (se 1 (by rfl) ⟨446525, by rfl⟩ : syracuseStep 595367 = 893051) B893051
theorem B890387 : Blo 393766 890387 := bstep (se 1 (by rfl) ⟨667790, by rfl⟩ : syracuseStep 890387 = 1335581) B1335581
theorem B890459 : Blo 393766 890459 := bstep (se 1 (by rfl) ⟨667844, by rfl⟩ : syracuseStep 890459 = 1335689) B1335689
theorem B595547 : Blo 393766 595547 := bstep (se 1 (by rfl) ⟨446660, by rfl⟩ : syracuseStep 595547 = 893321) B893321
theorem B2004587 : Blo 393766 2004587 := bstep (se 1 (by rfl) ⟨1503440, by rfl⟩ : syracuseStep 2004587 = 3006881) B3006881
theorem B4560785 : Blo 393766 4560785 := bstep (se 2 (by rfl) ⟨1710294, by rfl⟩ : syracuseStep 4560785 = 3420589) B3420589
theorem B858143 : Blo 393766 858143 := bstep (se 1 (by rfl) ⟨643607, by rfl⟩ : syracuseStep 858143 = 1287215) B1287215
theorem B891215 : Blo 393766 891215 := bstep (se 1 (by rfl) ⟨668411, by rfl⟩ : syracuseStep 891215 = 1336823) B1336823
theorem B596303 : Blo 393766 596303 := bstep (se 1 (by rfl) ⟨447227, by rfl⟩ : syracuseStep 596303 = 894455) B894455
theorem B596327 : Blo 393766 596327 := bstep (se 1 (by rfl) ⟨447245, by rfl⟩ : syracuseStep 596327 = 894491) B894491
theorem B891305 : Blo 393766 891305 := bstep (se 2 (by rfl) ⟨334239, by rfl⟩ : syracuseStep 891305 = 668479) B668479
theorem B596393 : Blo 393766 596393 := bstep (se 2 (by rfl) ⟨223647, by rfl⟩ : syracuseStep 596393 = 447295) B447295
theorem B891935 : Blo 393766 891935 := bstep (se 1 (by rfl) ⟨668951, by rfl⟩ : syracuseStep 891935 = 1337903) B1337903
theorem B892367 : Blo 393766 892367 := bstep (se 1 (by rfl) ⟨669275, by rfl⟩ : syracuseStep 892367 = 1338551) B1338551
theorem B859643 : Blo 393766 859643 := bstep (se 1 (by rfl) ⟨644732, by rfl⟩ : syracuseStep 859643 = 1289465) B1289465
theorem B2007017 : Blo 393766 2007017 := bstep (se 2 (by rfl) ⟨752631, by rfl⟩ : syracuseStep 2007017 = 1505263) B1505263
theorem B2007503 : Blo 393766 2007503 := bstep (se 1 (by rfl) ⟨1505627, by rfl⟩ : syracuseStep 2007503 = 3011255) B3011255
theorem B23438585 : Blo 393766 23438585 := bstep (se 2 (by rfl) ⟨8789469, by rfl⟩ : syracuseStep 23438585 = 17578939) B17578939
theorem B2008475 : Blo 393766 2008475 := bstep (se 1 (by rfl) ⟨1506356, by rfl⟩ : syracuseStep 2008475 = 3012713) B3012713
theorem B402895 : Blo 393766 402895 := bstep (se 1 (by rfl) ⟨302171, by rfl⟩ : syracuseStep 402895 = 604343) B604343
theorem B2696777 : Blo 393766 2696777 := bstep (se 2 (by rfl) ⟨1011291, by rfl⟩ : syracuseStep 2696777 = 2022583) B2022583
theorem B2992787 : Blo 393766 2992787 := bstep (se 1 (by rfl) ⟨2244590, by rfl⟩ : syracuseStep 2992787 = 4489181) B4489181
theorem B2009771 : Blo 393766 2009771 := bstep (se 1 (by rfl) ⟨1507328, by rfl⟩ : syracuseStep 2009771 = 3014657) B3014657
theorem B633919 : Blo 393766 633919 := bstep (se 1 (by rfl) ⟨475439, by rfl⟩ : syracuseStep 633919 = 950879) B950879
theorem B666731 : Blo 393766 666731 := bstep (se 1 (by rfl) ⟨500048, by rfl⟩ : syracuseStep 666731 = 1000097) B1000097
theorem B1223849 : Blo 393766 1223849 := bstep (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) B917887
theorem B667001 : Blo 393766 667001 := bstep (se 2 (by rfl) ⟨250125, by rfl⟩ : syracuseStep 667001 = 500251) B500251
theorem B503167 : Blo 393766 503167 := bstep (se 1 (by rfl) ⟨377375, by rfl⟩ : syracuseStep 503167 = 754751) B754751
theorem B2993759 : Blo 393766 2993759 := bstep (se 1 (by rfl) ⟨2245319, by rfl⟩ : syracuseStep 2993759 = 4490639) B4490639
theorem B11448125 : Blo 393766 11448125 := bstep (se 3 (by rfl) ⟨2146523, by rfl⟩ : syracuseStep 11448125 = 4293047) B4293047
theorem B537583 : Blo 393766 537583 := bstep (se 1 (by rfl) ⟨403187, by rfl⟩ : syracuseStep 537583 = 806375) B806375
theorem B2438225 : Blo 393766 2438225 := bstep (se 2 (by rfl) ⟨914334, by rfl⟩ : syracuseStep 2438225 = 1828669) B1828669
theorem B2700611 : Blo 393766 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B997019 : Blo 393766 997019 := bstep (se 1 (by rfl) ⟨747764, by rfl⟩ : syracuseStep 997019 = 1495529) B1495529
theorem B2013011 : Blo 393766 2013011 := bstep (se 1 (by rfl) ⟨1509758, by rfl⟩ : syracuseStep 2013011 = 3019517) B3019517
theorem B636827 : Blo 393766 636827 := bstep (se 1 (by rfl) ⟨477620, by rfl⟩ : syracuseStep 636827 = 955241) B955241
theorem B4798541 : Blo 393766 4798541 := bstep (se 3 (by rfl) ⟨899726, by rfl⟩ : syracuseStep 4798541 = 1799453) B1799453
theorem B4569281 : Blo 393766 4569281 := bstep (se 2 (by rfl) ⟨1713480, by rfl⟩ : syracuseStep 4569281 = 3426961) B3426961
theorem B4503761 : Blo 393766 4503761 := bstep (se 2 (by rfl) ⟨1688910, by rfl⟩ : syracuseStep 4503761 = 3377821) B3377821
theorem B4864367 : Blo 393766 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B1129085 : Blo 393766 1129085 := bstep (se 3 (by rfl) ⟨211703, by rfl⟩ : syracuseStep 1129085 = 423407) B423407
theorem B998153 : Blo 393766 998153 := bstep (se 2 (by rfl) ⟨374307, by rfl⟩ : syracuseStep 998153 = 748615) B748615
theorem B9649439 : Blo 393766 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B671017 : Blo 393766 671017 := bstep (se 2 (by rfl) ⟨251631, by rfl⟩ : syracuseStep 671017 = 503263) B503263
theorem B3653003 : Blo 393766 3653003 := bstep (se 1 (by rfl) ⟨2739752, by rfl⟩ : syracuseStep 3653003 = 5479505) B5479505
theorem B6405587 : Blo 393766 6405587 := bstep (se 1 (by rfl) ⟨4804190, by rfl⟩ : syracuseStep 6405587 = 9608381) B9608381
theorem B3390943 : Blo 393766 3390943 := bstep (se 1 (by rfl) ⟨2543207, by rfl⟩ : syracuseStep 3390943 = 5086415) B5086415
theorem B20528909 : Blo 393766 20528909 := bstep (se 3 (by rfl) ⟨3849170, by rfl⟩ : syracuseStep 20528909 = 7698341) B7698341
theorem B2146267 : Blo 393766 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B1064951 : Blo 393766 1064951 := bstep (se 1 (by rfl) ⟨798713, by rfl⟩ : syracuseStep 1064951 = 1597427) B1597427
theorem B999611 : Blo 393766 999611 := bstep (se 1 (by rfl) ⟨749708, by rfl⟩ : syracuseStep 999611 = 1499417) B1499417
theorem B1687817 : Blo 393766 1687817 := bstep (se 2 (by rfl) ⟨632931, by rfl⟩ : syracuseStep 1687817 = 1265863) B1265863
theorem B901625 : Blo 393766 901625 := bstep (se 2 (by rfl) ⟨338109, by rfl⟩ : syracuseStep 901625 = 676219) B676219
theorem B509095 : Blo 393766 509095 := bstep (se 1 (by rfl) ⟨381821, by rfl⟩ : syracuseStep 509095 = 763643) B763643
theorem B2245913 : Blo 393766 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B1000775 : Blo 393766 1000775 := bstep (se 1 (by rfl) ⟨750581, by rfl⟩ : syracuseStep 1000775 = 1501163) B1501163
theorem B1132001 : Blo 393766 1132001 := bstep (se 2 (by rfl) ⟨424500, by rfl⟩ : syracuseStep 1132001 = 849001) B849001
theorem B1689083 : Blo 393766 1689083 := bstep (se 1 (by rfl) ⟨1266812, by rfl⟩ : syracuseStep 1689083 = 2533625) B2533625
theorem B2705069 : Blo 393766 2705069 := bstep (se 3 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 2705069 = 1014401) B1014401
theorem B804745 : Blo 393766 804745 := bstep (se 2 (by rfl) ⟨301779, by rfl⟩ : syracuseStep 804745 = 603559) B603559
theorem B2246687 : Blo 393766 2246687 := bstep (se 1 (by rfl) ⟨1685015, by rfl⟩ : syracuseStep 2246687 = 3370031) B3370031
theorem B1263737 : Blo 393766 1263737 := bstep (se 2 (by rfl) ⟨473901, by rfl⟩ : syracuseStep 1263737 = 947803) B947803
theorem B10307897 : Blo 393766 10307897 := bstep (se 2 (by rfl) ⟨3865461, by rfl⟩ : syracuseStep 10307897 = 7730923) B7730923
theorem B3623291 : Blo 393766 3623291 := bstep (se 1 (by rfl) ⟨2717468, by rfl⟩ : syracuseStep 3623291 = 5434937) B5434937
theorem B1002041 : Blo 393766 1002041 := bstep (se 2 (by rfl) ⟨375765, by rfl⟩ : syracuseStep 1002041 = 751531) B751531
theorem B1264223 : Blo 393766 1264223 := bstep (se 1 (by rfl) ⟨948167, by rfl⟩ : syracuseStep 1264223 = 1896335) B1896335
theorem B1002203 : Blo 393766 1002203 := bstep (se 1 (by rfl) ⟨751652, by rfl⟩ : syracuseStep 1002203 = 1503305) B1503305
theorem B1330343 : Blo 393766 1330343 := bstep (se 1 (by rfl) ⟨997757, by rfl⟩ : syracuseStep 1330343 = 1995515) B1995515
theorem B2411707 : Blo 393766 2411707 := bstep (se 1 (by rfl) ⟨1808780, by rfl⟩ : syracuseStep 2411707 = 3617561) B3617561
theorem B30887243 : Blo 393766 30887243 := bstep (se 1 (by rfl) ⟨23165432, by rfl⟩ : syracuseStep 30887243 = 46330865) B46330865
theorem B1003387 : Blo 393766 1003387 := bstep (se 1 (by rfl) ⟨752540, by rfl⟩ : syracuseStep 1003387 = 1505081) B1505081
theorem B1331639 : Blo 393766 1331639 := bstep (se 1 (by rfl) ⟨998729, by rfl⟩ : syracuseStep 1331639 = 1997459) B1997459
theorem B447007 : Blo 393766 447007 := bstep (se 1 (by rfl) ⟨335255, by rfl⟩ : syracuseStep 447007 = 670511) B670511
theorem B611135 : Blo 393766 611135 := bstep (se 1 (by rfl) ⟨458351, by rfl⟩ : syracuseStep 611135 = 916703) B916703
theorem B27513751 : Blo 393766 27513751 := bstep (se 1 (by rfl) ⟨20635313, by rfl⟩ : syracuseStep 27513751 = 41270627) B41270627
theorem B1496015 : Blo 393766 1496015 := bstep (se 1 (by rfl) ⟨1122011, by rfl⟩ : syracuseStep 1496015 = 2244023) B2244023
theorem B1332179 : Blo 393766 1332179 := bstep (se 1 (by rfl) ⟨999134, by rfl⟩ : syracuseStep 1332179 = 1998269) B1998269
theorem B1004825 : Blo 393766 1004825 := bstep (se 2 (by rfl) ⟨376809, by rfl⟩ : syracuseStep 1004825 = 753619) B753619
theorem B1496819 : Blo 393766 1496819 := bstep (se 1 (by rfl) ⟨1122614, by rfl⟩ : syracuseStep 1496819 = 2245229) B2245229
theorem B18208961 : Blo 393766 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B1005817 : Blo 393766 1005817 := bstep (se 2 (by rfl) ⟨377181, by rfl⟩ : syracuseStep 1005817 = 754363) B754363
theorem B1005979 : Blo 393766 1005979 := bstep (se 1 (by rfl) ⟨754484, by rfl⟩ : syracuseStep 1005979 = 1508969) B1508969
theorem B2546747 : Blo 393766 2546747 := bstep (se 1 (by rfl) ⟨1910060, by rfl⟩ : syracuseStep 2546747 = 3820121) B3820121
theorem B2415815 : Blo 393766 2415815 := bstep (se 1 (by rfl) ⟨1811861, by rfl⟩ : syracuseStep 2415815 = 3623723) B3623723
theorem B810209 : Blo 393766 810209 := bstep (se 2 (by rfl) ⟨303828, by rfl⟩ : syracuseStep 810209 = 607657) B607657
theorem B1498459 : Blo 393766 1498459 := bstep (se 1 (by rfl) ⟨1123844, by rfl⟩ : syracuseStep 1498459 = 2247689) B2247689
theorem B1499431 : Blo 393766 1499431 := bstep (se 1 (by rfl) ⟨1124573, by rfl⟩ : syracuseStep 1499431 = 2249147) B2249147
theorem B2122247 : Blo 393766 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B1893145 : Blo 393766 1893145 := bstep (se 2 (by rfl) ⟨709929, by rfl⟩ : syracuseStep 1893145 = 1419859) B1419859
theorem B844627 : Blo 393766 844627 := bstep (se 1 (by rfl) ⟨633470, by rfl⟩ : syracuseStep 844627 = 1266941) B1266941
theorem B27453329 : Blo 393766 27453329 := bstep (se 2 (by rfl) ⟨10294998, by rfl⟩ : syracuseStep 27453329 = 20589997) B20589997
theorem B1337255 : Blo 393766 1337255 := bstep (se 1 (by rfl) ⟨1002941, by rfl⟩ : syracuseStep 1337255 = 2005883) B2005883
theorem B1501193 : Blo 393766 1501193 := bstep (se 2 (by rfl) ⟨562947, by rfl⟩ : syracuseStep 1501193 = 1125895) B1125895
theorem B1501375 : Blo 393766 1501375 := bstep (se 1 (by rfl) ⟨1126031, by rfl⟩ : syracuseStep 1501375 = 2252063) B2252063
theorem B9628217 : Blo 393766 9628217 := bstep (se 2 (by rfl) ⟨3610581, by rfl⟩ : syracuseStep 9628217 = 7221163) B7221163
theorem B7793297 : Blo 393766 7793297 := bstep (se 2 (by rfl) ⟨2922486, by rfl⟩ : syracuseStep 7793297 = 5844973) B5844973
theorem B1338119 : Blo 393766 1338119 := bstep (se 1 (by rfl) ⟨1003589, by rfl⟩ : syracuseStep 1338119 = 2007179) B2007179
theorem B748379 : Blo 393766 748379 := bstep (se 1 (by rfl) ⟨561284, by rfl⟩ : syracuseStep 748379 = 1122569) B1122569
theorem B6351839 : Blo 393766 6351839 := bstep (se 1 (by rfl) ⟨4763879, by rfl⟩ : syracuseStep 6351839 = 9527759) B9527759
theorem B5139571 : Blo 393766 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B1338497 : Blo 393766 1338497 := bstep (se 2 (by rfl) ⟨501936, by rfl⟩ : syracuseStep 1338497 = 1003873) B1003873
theorem B1273067 : Blo 393766 1273067 := bstep (se 1 (by rfl) ⟨954800, by rfl⟩ : syracuseStep 1273067 = 1909601) B1909601
theorem B1175273 : Blo 393766 1175273 := bstep (se 2 (by rfl) ⟨440727, by rfl⟩ : syracuseStep 1175273 = 881455) B881455
theorem B1339199 : Blo 393766 1339199 := bstep (se 1 (by rfl) ⟨1004399, by rfl⟩ : syracuseStep 1339199 = 2008799) B2008799
theorem B1601495 : Blo 393766 1601495 := bstep (se 1 (by rfl) ⟨1201121, by rfl⟩ : syracuseStep 1601495 = 2402243) B2402243
theorem B1208297 : Blo 393766 1208297 := bstep (se 2 (by rfl) ⟨453111, by rfl⟩ : syracuseStep 1208297 = 906223) B906223
theorem B848207 : Blo 393766 848207 := bstep (se 1 (by rfl) ⟨636155, by rfl⟩ : syracuseStep 848207 = 1272311) B1272311
theorem B750217 : Blo 393766 750217 := bstep (se 2 (by rfl) ⟨281331, by rfl⟩ : syracuseStep 750217 = 562663) B562663
theorem B4486265 : Blo 393766 4486265 := bstep (se 2 (by rfl) ⟨1682349, by rfl⟩ : syracuseStep 4486265 = 3364699) B3364699
theorem B17069777 : Blo 393766 17069777 := bstep (se 2 (by rfl) ⟨6401166, by rfl⟩ : syracuseStep 17069777 = 12802333) B12802333
theorem B751835 : Blo 393766 751835 := bstep (se 1 (by rfl) ⟨563876, by rfl⟩ : syracuseStep 751835 = 1127753) B1127753
theorem B4290803 : Blo 393766 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B752951 : Blo 393766 752951 := bstep (se 1 (by rfl) ⟨564713, by rfl⟩ : syracuseStep 752951 = 1129427) B1129427
theorem B2129399 : Blo 393766 2129399 := bstep (se 1 (by rfl) ⟨1597049, by rfl⟩ : syracuseStep 2129399 = 3194099) B3194099
theorem B1999241 : Blo 393766 1999241 := bstep (se 2 (by rfl) ⟨749715, by rfl⟩ : syracuseStep 1999241 = 1499431) B1499431
theorem B393775 : Blo 393766 393775 := bstep (se 1 (by rfl) ⟨295331, by rfl⟩ : syracuseStep 393775 = 590663) B590663
theorem B393819 : Blo 393766 393819 := bstep (se 1 (by rfl) ⟨295364, by rfl⟩ : syracuseStep 393819 = 590729) B590729
theorem B393983 : Blo 393766 393983 := bstep (se 1 (by rfl) ⟨295487, by rfl⟩ : syracuseStep 393983 = 590975) B590975
theorem B394075 : Blo 393766 394075 := bstep (se 1 (by rfl) ⟨295556, by rfl⟩ : syracuseStep 394075 = 591113) B591113
theorem B6423425 : Blo 393766 6423425 := bstep (se 2 (by rfl) ⟨2408784, by rfl⟩ : syracuseStep 6423425 = 4817569) B4817569
theorem B754667 : Blo 393766 754667 := bstep (se 1 (by rfl) ⟨566000, by rfl⟩ : syracuseStep 754667 = 1132001) B1132001
theorem B2524193 : Blo 393766 2524193 := bstep (se 2 (by rfl) ⟨946572, by rfl⟩ : syracuseStep 2524193 = 1893145) B1893145
theorem B1803379 : Blo 393766 1803379 := bstep (se 1 (by rfl) ⟨1352534, by rfl⟩ : syracuseStep 1803379 = 2705069) B2705069
theorem B394395 : Blo 393766 394395 := bstep (se 1 (by rfl) ⟨295796, by rfl⟩ : syracuseStep 394395 = 591593) B591593
theorem B394399 : Blo 393766 394399 := bstep (se 1 (by rfl) ⟨295799, by rfl⟩ : syracuseStep 394399 = 591599) B591599
theorem B394567 : Blo 393766 394567 := bstep (se 1 (by rfl) ⟨295925, by rfl⟩ : syracuseStep 394567 = 591851) B591851
theorem B394735 : Blo 393766 394735 := bstep (se 1 (by rfl) ⟨296051, by rfl⟩ : syracuseStep 394735 = 592103) B592103
theorem B394751 : Blo 393766 394751 := bstep (se 1 (by rfl) ⟨296063, by rfl⟩ : syracuseStep 394751 = 592127) B592127
theorem B394843 : Blo 393766 394843 := bstep (se 1 (by rfl) ⟨296132, by rfl⟩ : syracuseStep 394843 = 592265) B592265
theorem B4327519 : Blo 393766 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B886895 : Blo 393766 886895 := bstep (se 1 (by rfl) ⟨665171, by rfl⟩ : syracuseStep 886895 = 1330343) B1330343
theorem B592091 : Blo 393766 592091 := bstep (se 1 (by rfl) ⟨444068, by rfl⟩ : syracuseStep 592091 = 888137) B888137
theorem B395583 : Blo 393766 395583 := bstep (se 1 (by rfl) ⟨296687, by rfl⟩ : syracuseStep 395583 = 593375) B593375
theorem B395623 : Blo 393766 395623 := bstep (se 1 (by rfl) ⟨296717, by rfl⟩ : syracuseStep 395623 = 593435) B593435
theorem B3017087 : Blo 393766 3017087 := bstep (se 1 (by rfl) ⟨2262815, by rfl⟩ : syracuseStep 3017087 = 4525631) B4525631
theorem B592319 : Blo 393766 592319 := bstep (se 1 (by rfl) ⟨444239, by rfl⟩ : syracuseStep 592319 = 888479) B888479
theorem B395711 : Blo 393766 395711 := bstep (se 1 (by rfl) ⟨296783, by rfl⟩ : syracuseStep 395711 = 593567) B593567
theorem B395887 : Blo 393766 395887 := bstep (se 1 (by rfl) ⟨296915, by rfl⟩ : syracuseStep 395887 = 593831) B593831
theorem B395903 : Blo 393766 395903 := bstep (se 1 (by rfl) ⟨296927, by rfl⟩ : syracuseStep 395903 = 593855) B593855
theorem B396007 : Blo 393766 396007 := bstep (se 1 (by rfl) ⟨297005, by rfl⟩ : syracuseStep 396007 = 594011) B594011
theorem B592619 : Blo 393766 592619 := bstep (se 1 (by rfl) ⟨444464, by rfl⟩ : syracuseStep 592619 = 888929) B888929
theorem B1510123 : Blo 393766 1510123 := bstep (se 1 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 1510123 = 2265185) B2265185
theorem B396103 : Blo 393766 396103 := bstep (se 1 (by rfl) ⟨297077, by rfl⟩ : syracuseStep 396103 = 594155) B594155
theorem B592751 : Blo 393766 592751 := bstep (se 1 (by rfl) ⟨444563, by rfl⟩ : syracuseStep 592751 = 889127) B889127
theorem B396143 : Blo 393766 396143 := bstep (se 1 (by rfl) ⟨297107, by rfl⟩ : syracuseStep 396143 = 594215) B594215
theorem B2001833 : Blo 393766 2001833 := bstep (se 2 (by rfl) ⟨750687, by rfl⟩ : syracuseStep 2001833 = 1501375) B1501375
theorem B887759 : Blo 393766 887759 := bstep (se 1 (by rfl) ⟨665819, by rfl⟩ : syracuseStep 887759 = 1331639) B1331639
theorem B396319 : Blo 393766 396319 := bstep (se 1 (by rfl) ⟨297239, by rfl⟩ : syracuseStep 396319 = 594479) B594479
theorem B396455 : Blo 393766 396455 := bstep (se 1 (by rfl) ⟨297341, by rfl⟩ : syracuseStep 396455 = 594683) B594683
theorem B6753455 : Blo 393766 6753455 := bstep (se 1 (by rfl) ⟨5065091, by rfl⟩ : syracuseStep 6753455 = 10130183) B10130183
theorem B888119 : Blo 393766 888119 := bstep (se 1 (by rfl) ⟨666089, by rfl⟩ : syracuseStep 888119 = 1332179) B1332179
theorem B396703 : Blo 393766 396703 := bstep (se 1 (by rfl) ⟨297527, by rfl⟩ : syracuseStep 396703 = 595055) B595055
theorem B396751 : Blo 393766 396751 := bstep (se 1 (by rfl) ⟨297563, by rfl⟩ : syracuseStep 396751 = 595127) B595127
theorem B593519 : Blo 393766 593519 := bstep (se 1 (by rfl) ⟨445139, by rfl⟩ : syracuseStep 593519 = 890279) B890279
theorem B396911 : Blo 393766 396911 := bstep (se 1 (by rfl) ⟨297683, by rfl⟩ : syracuseStep 396911 = 595367) B595367
theorem B593591 : Blo 393766 593591 := bstep (se 1 (by rfl) ⟨445193, by rfl⟩ : syracuseStep 593591 = 890387) B890387
theorem B593639 : Blo 393766 593639 := bstep (se 1 (by rfl) ⟨445229, by rfl⟩ : syracuseStep 593639 = 890459) B890459
theorem B397031 : Blo 393766 397031 := bstep (se 1 (by rfl) ⟨297773, by rfl⟩ : syracuseStep 397031 = 595547) B595547
theorem B6852761 : Blo 393766 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B594143 : Blo 393766 594143 := bstep (se 1 (by rfl) ⟨445607, by rfl⟩ : syracuseStep 594143 = 891215) B891215
theorem B397535 : Blo 393766 397535 := bstep (se 1 (by rfl) ⟨298151, by rfl⟩ : syracuseStep 397535 = 596303) B596303
theorem B397551 : Blo 393766 397551 := bstep (se 1 (by rfl) ⟨298163, by rfl⟩ : syracuseStep 397551 = 596327) B596327
theorem B3215609 : Blo 393766 3215609 := bstep (se 2 (by rfl) ⟨1205853, by rfl⟩ : syracuseStep 3215609 = 2411707) B2411707
theorem B594203 : Blo 393766 594203 := bstep (se 1 (by rfl) ⟨445652, by rfl⟩ : syracuseStep 594203 = 891305) B891305
theorem B397595 : Blo 393766 397595 := bstep (se 1 (by rfl) ⟨298196, by rfl⟩ : syracuseStep 397595 = 596393) B596393
theorem B594623 : Blo 393766 594623 := bstep (se 1 (by rfl) ⟨445967, by rfl⟩ : syracuseStep 594623 = 891935) B891935
theorem B1610543 : Blo 393766 1610543 := bstep (se 1 (by rfl) ⟨1207907, by rfl⟩ : syracuseStep 1610543 = 2415815) B2415815
theorem B594911 : Blo 393766 594911 := bstep (se 1 (by rfl) ⟨446183, by rfl⟩ : syracuseStep 594911 = 892367) B892367
theorem B1709369 : Blo 393766 1709369 := bstep (se 2 (by rfl) ⟨641013, by rfl⟩ : syracuseStep 1709369 = 1282027) B1282027
theorem B1414831 : Blo 393766 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B596009 : Blo 393766 596009 := bstep (se 2 (by rfl) ⟨223503, by rfl⟩ : syracuseStep 596009 = 447007) B447007
theorem B891503 : Blo 393766 891503 := bstep (se 1 (by rfl) ⟨668627, by rfl⟩ : syracuseStep 891503 = 1337255) B1337255
theorem B892079 : Blo 393766 892079 := bstep (se 1 (by rfl) ⟨669059, by rfl⟩ : syracuseStep 892079 = 1338119) B1338119
theorem B4234559 : Blo 393766 4234559 := bstep (se 1 (by rfl) ⟨3175919, by rfl⟩ : syracuseStep 4234559 = 6351839) B6351839
theorem B892331 : Blo 393766 892331 := bstep (se 1 (by rfl) ⟨669248, by rfl⟩ : syracuseStep 892331 = 1338497) B1338497
theorem B892799 : Blo 393766 892799 := bstep (se 1 (by rfl) ⟨669599, by rfl⟩ : syracuseStep 892799 = 1339199) B1339199
theorem B565471 : Blo 393766 565471 := bstep (se 1 (by rfl) ⟨424103, by rfl⟩ : syracuseStep 565471 = 848207) B848207
theorem B2990843 : Blo 393766 2990843 := bstep (se 1 (by rfl) ⟨2243132, by rfl⟩ : syracuseStep 2990843 = 4486265) B4486265
theorem B9741341 : Blo 393766 9741341 := bstep (se 3 (by rfl) ⟨1826501, by rfl⟩ : syracuseStep 9741341 = 3653003) B3653003
theorem B664679 : Blo 393766 664679 := bstep (se 1 (by rfl) ⟨498509, by rfl⟩ : syracuseStep 664679 = 997019) B997019
theorem B11379851 : Blo 393766 11379851 := bstep (se 1 (by rfl) ⟨8534888, by rfl⟩ : syracuseStep 11379851 = 17069777) B17069777
theorem B501223 : Blo 393766 501223 := bstep (se 1 (by rfl) ⟨375917, by rfl⟩ : syracuseStep 501223 = 751835) B751835
theorem B2860535 : Blo 393766 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B6792821 : Blo 393766 6792821 := bstep (se 5 (by rfl) ⟨318413, by rfl⟩ : syracuseStep 6792821 = 636827) B636827
theorem B894689 : Blo 393766 894689 := bstep (se 2 (by rfl) ⟨335508, by rfl⟩ : syracuseStep 894689 = 671017) B671017
theorem B665435 : Blo 393766 665435 := bstep (se 1 (by rfl) ⟨499076, by rfl⟩ : syracuseStep 665435 = 998153) B998153
theorem B6432959 : Blo 393766 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B501967 : Blo 393766 501967 := bstep (se 1 (by rfl) ⟨376475, by rfl⟩ : syracuseStep 501967 = 752951) B752951
theorem B4270391 : Blo 393766 4270391 := bstep (se 1 (by rfl) ⟨3202793, by rfl⟩ : syracuseStep 4270391 = 6405587) B6405587
theorem B1419599 : Blo 393766 1419599 := bstep (se 1 (by rfl) ⟨1064699, by rfl⟩ : syracuseStep 1419599 = 2129399) B2129399
theorem B3222125 : Blo 393766 3222125 := bstep (se 3 (by rfl) ⟨604148, by rfl⟩ : syracuseStep 3222125 = 1208297) B1208297
theorem B2861689 : Blo 393766 2861689 := bstep (se 2 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 2861689 = 2146267) B2146267
theorem B666407 : Blo 393766 666407 := bstep (se 1 (by rfl) ⟨499805, by rfl⟩ : syracuseStep 666407 = 999611) B999611
theorem B1813691 : Blo 393766 1813691 := bstep (se 1 (by rfl) ⟨1360268, by rfl⟩ : syracuseStep 1813691 = 2720537) B2720537
theorem B1682623 : Blo 393766 1682623 := bstep (se 1 (by rfl) ⟨1261967, by rfl⟩ : syracuseStep 1682623 = 2523935) B2523935
theorem B4500845 : Blo 393766 4500845 := bstep (se 3 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 4500845 = 1687817) B1687817
theorem B667183 : Blo 393766 667183 := bstep (se 1 (by rfl) ⟨500387, by rfl⟩ : syracuseStep 667183 = 1000775) B1000775
theorem B1126055 : Blo 393766 1126055 := bstep (se 1 (by rfl) ⟨844541, by rfl⟩ : syracuseStep 1126055 = 1689083) B1689083
theorem B1126169 : Blo 393766 1126169 := bstep (se 2 (by rfl) ⟨422313, by rfl⟩ : syracuseStep 1126169 = 844627) B844627
theorem B2404333 : Blo 393766 2404333 := bstep (se 3 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 2404333 = 901625) B901625
theorem B5681279 : Blo 393766 5681279 := bstep (se 1 (by rfl) ⟨4260959, by rfl⟩ : syracuseStep 5681279 = 8521919) B8521919
theorem B668027 : Blo 393766 668027 := bstep (se 1 (by rfl) ⟨501020, by rfl⟩ : syracuseStep 668027 = 1002041) B1002041
theorem B668135 : Blo 393766 668135 := bstep (se 1 (by rfl) ⟨501101, by rfl⟩ : syracuseStep 668135 = 1002203) B1002203
theorem B20591495 : Blo 393766 20591495 := bstep (se 1 (by rfl) ⟨15443621, by rfl⟩ : syracuseStep 20591495 = 30887243) B30887243
theorem B2143219 : Blo 393766 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B407423 : Blo 393766 407423 := bstep (se 1 (by rfl) ⟨305567, by rfl⟩ : syracuseStep 407423 = 611135) B611135
theorem B997343 : Blo 393766 997343 := bstep (se 1 (by rfl) ⟨748007, by rfl⟩ : syracuseStep 997343 = 1496015) B1496015
theorem B669883 : Blo 393766 669883 := bstep (se 1 (by rfl) ⟨502412, by rfl⟩ : syracuseStep 669883 = 1004825) B1004825
theorem B997879 : Blo 393766 997879 := bstep (se 1 (by rfl) ⟨748409, by rfl⟩ : syracuseStep 997879 = 1496819) B1496819
theorem B572095 : Blo 393766 572095 := bstep (se 1 (by rfl) ⟨429071, by rfl⟩ : syracuseStep 572095 = 858143) B858143
theorem B12139307 : Blo 393766 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B670889 : Blo 393766 670889 := bstep (se 2 (by rfl) ⟨251583, by rfl⟩ : syracuseStep 670889 = 503167) B503167
theorem B573095 : Blo 393766 573095 := bstep (se 1 (by rfl) ⟨429821, by rfl⟩ : syracuseStep 573095 = 859643) B859643
theorem B1000289 : Blo 393766 1000289 := bstep (se 2 (by rfl) ⟨375108, by rfl⟩ : syracuseStep 1000289 = 750217) B750217
theorem B36685001 : Blo 393766 36685001 := bstep (se 2 (by rfl) ⟨13756875, by rfl⟩ : syracuseStep 36685001 = 27513751) B27513751
theorem B18302219 : Blo 393766 18302219 := bstep (se 1 (by rfl) ⟨13726664, by rfl⟩ : syracuseStep 18302219 = 27453329) B27453329
theorem B1000795 : Blo 393766 1000795 := bstep (se 1 (by rfl) ⟨750596, by rfl⟩ : syracuseStep 1000795 = 1501193) B1501193
theorem B2540929 : Blo 393766 2540929 := bstep (se 2 (by rfl) ⟨952848, by rfl⟩ : syracuseStep 2540929 = 1905697) B1905697
theorem B5195531 : Blo 393766 5195531 := bstep (se 1 (by rfl) ⟨3896648, by rfl⟩ : syracuseStep 5195531 = 7793297) B7793297
theorem B444487 : Blo 393766 444487 := bstep (se 1 (by rfl) ⟨333365, by rfl⟩ : syracuseStep 444487 = 666731) B666731
theorem B444667 : Blo 393766 444667 := bstep (se 1 (by rfl) ⟨333500, by rfl⟩ : syracuseStep 444667 = 667001) B667001
theorem B2148773 : Blo 393766 2148773 := bstep (se 4 (by rfl) ⟨201447, by rfl⟩ : syracuseStep 2148773 = 402895) B402895
theorem B1067663 : Blo 393766 1067663 := bstep (se 1 (by rfl) ⟨800747, by rfl⟩ : syracuseStep 1067663 = 1601495) B1601495
theorem B3263597 : Blo 393766 3263597 := bstep (se 3 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 3263597 = 1223849) B1223849
theorem B1625483 : Blo 393766 1625483 := bstep (se 1 (by rfl) ⟨1219112, by rfl⟩ : syracuseStep 1625483 = 2438225) B2438225
theorem B3199027 : Blo 393766 3199027 := bstep (se 1 (by rfl) ⟨2399270, by rfl⟩ : syracuseStep 3199027 = 4798541) B4798541
theorem B3002507 : Blo 393766 3002507 := bstep (se 1 (by rfl) ⟨2251880, by rfl⟩ : syracuseStep 3002507 = 4503761) B4503761
theorem B13685939 : Blo 393766 13685939 := bstep (se 1 (by rfl) ⟨10264454, by rfl⟩ : syracuseStep 13685939 = 20528909) B20528909
theorem B709967 : Blo 393766 709967 := bstep (se 1 (by rfl) ⟨532475, by rfl⟩ : syracuseStep 709967 = 1064951) B1064951
theorem B480767 : Blo 393766 480767 := bstep (se 1 (by rfl) ⟨360575, by rfl⟩ : syracuseStep 480767 = 721151) B721151
theorem B1497275 : Blo 393766 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B1497791 : Blo 393766 1497791 := bstep (se 1 (by rfl) ⟨1123343, by rfl⟩ : syracuseStep 1497791 = 2246687) B2246687
theorem B842491 : Blo 393766 842491 := bstep (se 1 (by rfl) ⟨631868, by rfl⟩ : syracuseStep 842491 = 1263737) B1263737
theorem B6871931 : Blo 393766 6871931 := bstep (se 1 (by rfl) ⟨5153948, by rfl⟩ : syracuseStep 6871931 = 10307897) B10307897
theorem B678793 : Blo 393766 678793 := bstep (se 2 (by rfl) ⟨254547, by rfl⟩ : syracuseStep 678793 = 509095) B509095
theorem B2415527 : Blo 393766 2415527 := bstep (se 1 (by rfl) ⟨1811645, by rfl⟩ : syracuseStep 2415527 = 3623291) B3623291
theorem B842815 : Blo 393766 842815 := bstep (se 1 (by rfl) ⟨632111, by rfl⟩ : syracuseStep 842815 = 1264223) B1264223
theorem B100228913 : Blo 393766 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B1336391 : Blo 393766 1336391 := bstep (se 1 (by rfl) ⟨1002293, by rfl⟩ : syracuseStep 1336391 = 2004587) B2004587
theorem B3040523 : Blo 393766 3040523 := bstep (se 1 (by rfl) ⟨2280392, by rfl⟩ : syracuseStep 3040523 = 4560785) B4560785
theorem B845225 : Blo 393766 845225 := bstep (se 2 (by rfl) ⟨316959, by rfl⟩ : syracuseStep 845225 = 633919) B633919
theorem B1697831 : Blo 393766 1697831 := bstep (se 1 (by rfl) ⟨1273373, by rfl⟩ : syracuseStep 1697831 = 2546747) B2546747
theorem B1337849 : Blo 393766 1337849 := bstep (se 2 (by rfl) ⟨501693, by rfl⟩ : syracuseStep 1337849 = 1003387) B1003387
theorem B1338011 : Blo 393766 1338011 := bstep (se 1 (by rfl) ⟨1003508, by rfl⟩ : syracuseStep 1338011 = 2007017) B2007017
theorem B1338335 : Blo 393766 1338335 := bstep (se 1 (by rfl) ⟨1003751, by rfl⟩ : syracuseStep 1338335 = 2007503) B2007503
theorem B15625723 : Blo 393766 15625723 := bstep (se 1 (by rfl) ⟨11719292, by rfl⟩ : syracuseStep 15625723 = 23438585) B23438585
theorem B1338983 : Blo 393766 1338983 := bstep (se 1 (by rfl) ⟨1004237, by rfl⟩ : syracuseStep 1338983 = 2008475) B2008475
theorem B1797851 : Blo 393766 1797851 := bstep (se 1 (by rfl) ⟨1348388, by rfl⟩ : syracuseStep 1797851 = 2696777) B2696777
theorem B716777 : Blo 393766 716777 := bstep (se 2 (by rfl) ⟨268791, by rfl⟩ : syracuseStep 716777 = 537583) B537583
theorem B6418811 : Blo 393766 6418811 := bstep (se 1 (by rfl) ⟨4814108, by rfl⟩ : syracuseStep 6418811 = 9628217) B9628217
theorem B1995191 : Blo 393766 1995191 := bstep (se 1 (by rfl) ⟨1496393, by rfl⟩ : syracuseStep 1995191 = 2992787) B2992787
theorem B1339847 : Blo 393766 1339847 := bstep (se 1 (by rfl) ⟨1004885, by rfl⟩ : syracuseStep 1339847 = 2009771) B2009771
theorem B848711 : Blo 393766 848711 := bstep (se 1 (by rfl) ⟨636533, by rfl⟩ : syracuseStep 848711 = 1273067) B1273067
theorem B1995677 : Blo 393766 1995677 := bstep (se 3 (by rfl) ⟨374189, by rfl⟩ : syracuseStep 1995677 = 748379) B748379
theorem B1995839 : Blo 393766 1995839 := bstep (se 1 (by rfl) ⟨1496879, by rfl⟩ : syracuseStep 1995839 = 2993759) B2993759
theorem B783515 : Blo 393766 783515 := bstep (se 1 (by rfl) ⟨587636, by rfl⟩ : syracuseStep 783515 = 1175273) B1175273
theorem B7632083 : Blo 393766 7632083 := bstep (se 1 (by rfl) ⟨5724062, by rfl⟩ : syracuseStep 7632083 = 11448125) B11448125
theorem B1341089 : Blo 393766 1341089 := bstep (se 2 (by rfl) ⟨502908, by rfl⟩ : syracuseStep 1341089 = 1005817) B1005817
theorem B1341305 : Blo 393766 1341305 := bstep (se 2 (by rfl) ⟨502989, by rfl⟩ : syracuseStep 1341305 = 1005979) B1005979
theorem B2160557 : Blo 393766 2160557 := bstep (se 3 (by rfl) ⟨405104, by rfl⟩ : syracuseStep 2160557 = 810209) B810209
theorem B1800407 : Blo 393766 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B1342007 : Blo 393766 1342007 := bstep (se 1 (by rfl) ⟨1006505, by rfl⟩ : syracuseStep 1342007 = 2013011) B2013011
theorem B3046187 : Blo 393766 3046187 := bstep (se 1 (by rfl) ⟨2284640, by rfl⟩ : syracuseStep 3046187 = 4569281) B4569281
theorem B3242911 : Blo 393766 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B752723 : Blo 393766 752723 := bstep (se 1 (by rfl) ⟨564542, by rfl⟩ : syracuseStep 752723 = 1129085) B1129085
theorem B1997945 : Blo 393766 1997945 := bstep (se 2 (by rfl) ⟨749229, by rfl⟩ : syracuseStep 1997945 = 1498459) B1498459
theorem B4521257 : Blo 393766 4521257 := bstep (se 2 (by rfl) ⟨1695471, by rfl⟩ : syracuseStep 4521257 = 3390943) B3390943
theorem B4291973 : Blo 393766 4291973 := bstep (se 4 (by rfl) ⟨402372, by rfl⟩ : syracuseStep 4291973 = 804745) B804745
theorem B753961 : Blo 393766 753961 := bstep (se 2 (by rfl) ⟨282735, by rfl⟩ : syracuseStep 753961 = 565471) B565471
theorem B591263 : Blo 393766 591263 := bstep (se 1 (by rfl) ⟨443447, by rfl⟩ : syracuseStep 591263 = 886895) B886895
theorem B394727 : Blo 393766 394727 := bstep (se 1 (by rfl) ⟨296045, by rfl⟩ : syracuseStep 394727 = 592091) B592091
theorem B394879 : Blo 393766 394879 := bstep (se 1 (by rfl) ⟨296159, by rfl⟩ : syracuseStep 394879 = 592319) B592319
theorem B395079 : Blo 393766 395079 := bstep (se 1 (by rfl) ⟨296309, by rfl⟩ : syracuseStep 395079 = 592619) B592619
theorem B395167 : Blo 393766 395167 := bstep (se 1 (by rfl) ⟨296375, by rfl⟩ : syracuseStep 395167 = 592751) B592751
theorem B591839 : Blo 393766 591839 := bstep (se 1 (by rfl) ⟨443879, by rfl⟩ : syracuseStep 591839 = 887759) B887759
theorem B4294781 : Blo 393766 4294781 := bstep (se 3 (by rfl) ⟨805271, by rfl⟩ : syracuseStep 4294781 = 1610543) B1610543
theorem B592079 : Blo 393766 592079 := bstep (se 1 (by rfl) ⟨444059, by rfl⟩ : syracuseStep 592079 = 888119) B888119
theorem B1083655 : Blo 393766 1083655 := bstep (se 1 (by rfl) ⟨812741, by rfl⟩ : syracuseStep 1083655 = 1625483) B1625483
theorem B395679 : Blo 393766 395679 := bstep (se 1 (by rfl) ⟨296759, by rfl⟩ : syracuseStep 395679 = 593519) B593519
theorem B395727 : Blo 393766 395727 := bstep (se 1 (by rfl) ⟨296795, by rfl⟩ : syracuseStep 395727 = 593591) B593591
theorem B395759 : Blo 393766 395759 := bstep (se 1 (by rfl) ⟨296819, by rfl⟩ : syracuseStep 395759 = 593639) B593639
theorem B2001671 : Blo 393766 2001671 := bstep (se 1 (by rfl) ⟨1501253, by rfl⟩ : syracuseStep 2001671 = 3002507) B3002507
theorem B592649 : Blo 393766 592649 := bstep (se 2 (by rfl) ⟨222243, by rfl⟩ : syracuseStep 592649 = 444487) B444487
theorem B5770025 : Blo 393766 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B396095 : Blo 393766 396095 := bstep (se 1 (by rfl) ⟨297071, by rfl⟩ : syracuseStep 396095 = 594143) B594143
theorem B396135 : Blo 393766 396135 := bstep (se 1 (by rfl) ⟨297101, by rfl⟩ : syracuseStep 396135 = 594203) B594203
theorem B592889 : Blo 393766 592889 := bstep (se 2 (by rfl) ⟨222333, by rfl⟩ : syracuseStep 592889 = 444667) B444667
theorem B396415 : Blo 393766 396415 := bstep (se 1 (by rfl) ⟨297311, by rfl⟩ : syracuseStep 396415 = 594623) B594623
theorem B396607 : Blo 393766 396607 := bstep (se 1 (by rfl) ⟨297455, by rfl⟩ : syracuseStep 396607 = 594911) B594911
theorem B3051173 : Blo 393766 3051173 := bstep (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) B572095
theorem B397339 : Blo 393766 397339 := bstep (se 1 (by rfl) ⟨298004, by rfl⟩ : syracuseStep 397339 = 596009) B596009
theorem B594335 : Blo 393766 594335 := bstep (se 1 (by rfl) ⟨445751, by rfl⟩ : syracuseStep 594335 = 891503) B891503
theorem B1610351 : Blo 393766 1610351 := bstep (se 1 (by rfl) ⟨1207763, by rfl⟩ : syracuseStep 1610351 = 2415527) B2415527
theorem B889577 : Blo 393766 889577 := bstep (se 2 (by rfl) ⟨333591, by rfl⟩ : syracuseStep 889577 = 667183) B667183
theorem B594719 : Blo 393766 594719 := bstep (se 1 (by rfl) ⟨446039, by rfl⟩ : syracuseStep 594719 = 892079) B892079
theorem B594887 : Blo 393766 594887 := bstep (se 1 (by rfl) ⟨446165, by rfl⟩ : syracuseStep 594887 = 892331) B892331
theorem B1086461 : Blo 393766 1086461 := bstep (se 3 (by rfl) ⟨203711, by rfl⟩ : syracuseStep 1086461 = 407423) B407423
theorem B66819275 : Blo 393766 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B595199 : Blo 393766 595199 := bstep (se 1 (by rfl) ⟨446399, by rfl⟩ : syracuseStep 595199 = 892799) B892799
theorem B4265369 : Blo 393766 4265369 := bstep (se 2 (by rfl) ⟨1599513, by rfl⟩ : syracuseStep 4265369 = 3199027) B3199027
theorem B4495013 : Blo 393766 4495013 := bstep (se 4 (by rfl) ⟨421407, by rfl⟩ : syracuseStep 4495013 = 842815) B842815
theorem B890927 : Blo 393766 890927 := bstep (se 1 (by rfl) ⟨668195, by rfl⟩ : syracuseStep 890927 = 1336391) B1336391
theorem B563483 : Blo 393766 563483 := bstep (se 1 (by rfl) ⟨422612, by rfl⟩ : syracuseStep 563483 = 845225) B845225
theorem B1907023 : Blo 393766 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B4528547 : Blo 393766 4528547 := bstep (se 1 (by rfl) ⟨3396410, by rfl⟩ : syracuseStep 4528547 = 6792821) B6792821
theorem B596459 : Blo 393766 596459 := bstep (se 1 (by rfl) ⟨447344, by rfl⟩ : syracuseStep 596459 = 894689) B894689
theorem B2857625 : Blo 393766 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B891899 : Blo 393766 891899 := bstep (se 1 (by rfl) ⟨668924, by rfl⟩ : syracuseStep 891899 = 1337849) B1337849
theorem B892007 : Blo 393766 892007 := bstep (se 1 (by rfl) ⟨669005, by rfl⟩ : syracuseStep 892007 = 1338011) B1338011
theorem B892223 : Blo 393766 892223 := bstep (se 1 (by rfl) ⟨669167, by rfl⟩ : syracuseStep 892223 = 1338335) B1338335
theorem B892655 : Blo 393766 892655 := bstep (se 1 (by rfl) ⟨669491, by rfl⟩ : syracuseStep 892655 = 1338983) B1338983
theorem B893177 : Blo 393766 893177 := bstep (se 2 (by rfl) ⟨334941, by rfl⟩ : syracuseStep 893177 = 669883) B669883
theorem B893231 : Blo 393766 893231 := bstep (se 1 (by rfl) ⟨669923, by rfl⟩ : syracuseStep 893231 = 1339847) B1339847
theorem B565807 : Blo 393766 565807 := bstep (se 1 (by rfl) ⟨424355, by rfl⟩ : syracuseStep 565807 = 848711) B848711
theorem B5088055 : Blo 393766 5088055 := bstep (se 1 (by rfl) ⟨3816041, by rfl⟩ : syracuseStep 5088055 = 7632083) B7632083
theorem B1123321 : Blo 393766 1123321 := bstep (se 2 (by rfl) ⟨421245, by rfl⟩ : syracuseStep 1123321 = 842491) B842491
theorem B894059 : Blo 393766 894059 := bstep (se 1 (by rfl) ⟨670544, by rfl⟩ : syracuseStep 894059 = 1341089) B1341089
theorem B894203 : Blo 393766 894203 := bstep (se 1 (by rfl) ⟨670652, by rfl⟩ : syracuseStep 894203 = 1341305) B1341305
theorem B664895 : Blo 393766 664895 := bstep (se 1 (by rfl) ⟨498671, by rfl⟩ : syracuseStep 664895 = 997343) B997343
theorem B894671 : Blo 393766 894671 := bstep (se 1 (by rfl) ⟨671003, by rfl⟩ : syracuseStep 894671 = 1342007) B1342007
theorem B501815 : Blo 393766 501815 := bstep (se 1 (by rfl) ⟨376361, by rfl⟩ : syracuseStep 501815 = 752723) B752723
theorem B2861315 : Blo 393766 2861315 := bstep (se 1 (by rfl) ⟨2145986, by rfl⟩ : syracuseStep 2861315 = 4291973) B4291973
theorem B666859 : Blo 393766 666859 := bstep (se 1 (by rfl) ⟨500144, by rfl⟩ : syracuseStep 666859 = 1000289) B1000289
theorem B503111 : Blo 393766 503111 := bstep (se 1 (by rfl) ⟨377333, by rfl⟩ : syracuseStep 503111 = 754667) B754667
theorem B1682795 : Blo 393766 1682795 := bstep (se 1 (by rfl) ⟨1262096, by rfl⟩ : syracuseStep 1682795 = 2524193) B2524193
theorem B24456667 : Blo 393766 24456667 := bstep (se 1 (by rfl) ⟨18342500, by rfl⟩ : syracuseStep 24456667 = 36685001) B36685001
theorem B12201479 : Blo 393766 12201479 := bstep (se 1 (by rfl) ⟨9151109, by rfl⟩ : syracuseStep 12201479 = 18302219) B18302219
theorem B17116829 : Blo 393766 17116829 := bstep (se 3 (by rfl) ⟨3209405, by rfl⟩ : syracuseStep 17116829 = 6418811) B6418811
theorem B2404505 : Blo 393766 2404505 := bstep (se 2 (by rfl) ⟨901689, by rfl⟩ : syracuseStep 2404505 = 1803379) B1803379
theorem B2011391 : Blo 393766 2011391 := bstep (se 1 (by rfl) ⟨1508543, by rfl⟩ : syracuseStep 2011391 = 3017087) B3017087
theorem B3387905 : Blo 393766 3387905 := bstep (se 2 (by rfl) ⟨1270464, by rfl⟩ : syracuseStep 3387905 = 2540929) B2540929
theorem B668297 : Blo 393766 668297 := bstep (se 2 (by rfl) ⟨250611, by rfl⟩ : syracuseStep 668297 = 501223) B501223
theorem B2175731 : Blo 393766 2175731 := bstep (se 1 (by rfl) ⟨1631798, by rfl⟩ : syracuseStep 2175731 = 3263597) B3263597
theorem B4502303 : Blo 393766 4502303 := bstep (se 1 (by rfl) ⟨3376727, by rfl⟩ : syracuseStep 4502303 = 6753455) B6753455
theorem B4568507 : Blo 393766 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B2143739 : Blo 393766 2143739 := bstep (se 1 (by rfl) ⟨1607804, by rfl⟩ : syracuseStep 2143739 = 3215609) B3215609
theorem B669289 : Blo 393766 669289 := bstep (se 2 (by rfl) ⟨250983, by rfl⟩ : syracuseStep 669289 = 501967) B501967
theorem B9123959 : Blo 393766 9123959 := bstep (se 1 (by rfl) ⟨6842969, by rfl⟩ : syracuseStep 9123959 = 13685939) B13685939
theorem B3815585 : Blo 393766 3815585 := bstep (se 2 (by rfl) ⟨1430844, by rfl⟩ : syracuseStep 3815585 = 2861689) B2861689
theorem B473311 : Blo 393766 473311 := bstep (se 1 (by rfl) ⟨354983, by rfl⟩ : syracuseStep 473311 = 709967) B709967
theorem B2013497 : Blo 393766 2013497 := bstep (se 2 (by rfl) ⟨755061, by rfl⟩ : syracuseStep 2013497 = 1510123) B1510123
theorem B998183 : Blo 393766 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B2243497 : Blo 393766 2243497 := bstep (se 2 (by rfl) ⟨841311, by rfl⟩ : syracuseStep 2243497 = 1682623) B1682623
theorem B998527 : Blo 393766 998527 := bstep (se 1 (by rfl) ⟨748895, by rfl⟩ : syracuseStep 998527 = 1497791) B1497791
theorem B5128181 : Blo 393766 5128181 := bstep (se 5 (by rfl) ⟨240383, by rfl⟩ : syracuseStep 5128181 = 480767) B480767
theorem B443119 : Blo 393766 443119 := bstep (se 1 (by rfl) ⟨332339, by rfl⟩ : syracuseStep 443119 = 664679) B664679
theorem B7586567 : Blo 393766 7586567 := bstep (se 1 (by rfl) ⟨5689925, by rfl⟩ : syracuseStep 7586567 = 11379851) B11379851
theorem B443623 : Blo 393766 443623 := bstep (se 1 (by rfl) ⟨332717, by rfl⟩ : syracuseStep 443623 = 665435) B665435
theorem B1131887 : Blo 393766 1131887 := bstep (se 1 (by rfl) ⟨848915, by rfl⟩ : syracuseStep 1131887 = 1697831) B1697831
theorem B2148083 : Blo 393766 2148083 := bstep (se 1 (by rfl) ⟨1611062, by rfl⟩ : syracuseStep 2148083 = 3222125) B3222125
theorem B444271 : Blo 393766 444271 := bstep (se 1 (by rfl) ⟨333203, by rfl⟩ : syracuseStep 444271 = 666407) B666407
theorem B1886441 : Blo 393766 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B3000563 : Blo 393766 3000563 := bstep (se 1 (by rfl) ⟨2250422, by rfl⟩ : syracuseStep 3000563 = 4500845) B4500845
theorem B1198567 : Blo 393766 1198567 := bstep (se 1 (by rfl) ⟨898925, by rfl⟩ : syracuseStep 1198567 = 1797851) B1797851
theorem B477851 : Blo 393766 477851 := bstep (se 1 (by rfl) ⟨358388, by rfl⟩ : syracuseStep 477851 = 716777) B716777
theorem B3787519 : Blo 393766 3787519 := bstep (se 1 (by rfl) ⟨2840639, by rfl⟩ : syracuseStep 3787519 = 5681279) B5681279
theorem B445351 : Blo 393766 445351 := bstep (se 1 (by rfl) ⟨334013, by rfl⟩ : syracuseStep 445351 = 668027) B668027
theorem B1330127 : Blo 393766 1330127 := bstep (se 1 (by rfl) ⟨997595, by rfl⟩ : syracuseStep 1330127 = 1995191) B1995191
theorem B445423 : Blo 393766 445423 := bstep (se 1 (by rfl) ⟨334067, by rfl⟩ : syracuseStep 445423 = 668135) B668135
theorem B1330451 : Blo 393766 1330451 := bstep (se 1 (by rfl) ⟨997838, by rfl⟩ : syracuseStep 1330451 = 1995677) B1995677
theorem B1330505 : Blo 393766 1330505 := bstep (se 2 (by rfl) ⟨498939, by rfl⟩ : syracuseStep 1330505 = 997879) B997879
theorem B1330559 : Blo 393766 1330559 := bstep (se 1 (by rfl) ⟨997919, by rfl⟩ : syracuseStep 1330559 = 1995839) B1995839
theorem B11292157 : Blo 393766 11292157 := bstep (se 3 (by rfl) ⟨2117279, by rfl⟩ : syracuseStep 11292157 = 4234559) B4234559
theorem B905057 : Blo 393766 905057 := bstep (se 2 (by rfl) ⟨339396, by rfl⟩ : syracuseStep 905057 = 678793) B678793
theorem B1200271 : Blo 393766 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B1528253 : Blo 393766 1528253 := bstep (se 3 (by rfl) ⟨286547, by rfl⟩ : syracuseStep 1528253 = 573095) B573095
theorem B1331963 : Blo 393766 1331963 := bstep (se 1 (by rfl) ⟨998972, by rfl⟩ : syracuseStep 1331963 = 1997945) B1997945
theorem B447259 : Blo 393766 447259 := bstep (se 1 (by rfl) ⟨335444, by rfl⟩ : syracuseStep 447259 = 670889) B670889
theorem B1332827 : Blo 393766 1332827 := bstep (se 1 (by rfl) ⟨999620, by rfl⟩ : syracuseStep 1332827 = 1999241) B1999241
theorem B4282283 : Blo 393766 4282283 := bstep (se 1 (by rfl) ⟨3211712, by rfl⟩ : syracuseStep 4282283 = 6423425) B6423425
theorem B3463687 : Blo 393766 3463687 := bstep (se 1 (by rfl) ⟨2597765, by rfl⟩ : syracuseStep 3463687 = 5195531) B5195531
theorem B711775 : Blo 393766 711775 := bstep (se 1 (by rfl) ⟨533831, by rfl⟩ : syracuseStep 711775 = 1067663) B1067663
theorem B1334393 : Blo 393766 1334393 := bstep (se 2 (by rfl) ⟨500397, by rfl⟩ : syracuseStep 1334393 = 1000795) B1000795
theorem B1334555 : Blo 393766 1334555 := bstep (se 1 (by rfl) ⟨1000916, by rfl⟩ : syracuseStep 1334555 = 2001833) B2001833
theorem B25976909 : Blo 393766 25976909 := bstep (se 3 (by rfl) ⟨4870670, by rfl⟩ : syracuseStep 25976909 = 9741341) B9741341
theorem B1139579 : Blo 393766 1139579 := bstep (se 1 (by rfl) ⟨854684, by rfl⟩ : syracuseStep 1139579 = 1709369) B1709369
theorem B4581287 : Blo 393766 4581287 := bstep (se 1 (by rfl) ⟨3435965, by rfl⟩ : syracuseStep 4581287 = 6871931) B6871931
theorem B20834297 : Blo 393766 20834297 := bstep (se 2 (by rfl) ⟨7812861, by rfl⟩ : syracuseStep 20834297 = 15625723) B15625723
theorem B3205777 : Blo 393766 3205777 := bstep (se 2 (by rfl) ⟨1202166, by rfl⟩ : syracuseStep 3205777 = 2404333) B2404333
theorem B1993895 : Blo 393766 1993895 := bstep (se 1 (by rfl) ⟨1495421, by rfl⟩ : syracuseStep 1993895 = 2990843) B2990843
theorem B2027015 : Blo 393766 2027015 := bstep (se 1 (by rfl) ⟨1520261, by rfl⟩ : syracuseStep 2027015 = 3040523) B3040523
theorem B5730061 : Blo 393766 5730061 := bstep (se 3 (by rfl) ⟨1074386, by rfl⟩ : syracuseStep 5730061 = 2148773) B2148773
theorem B4288639 : Blo 393766 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B2846927 : Blo 393766 2846927 := bstep (se 1 (by rfl) ⟨2135195, by rfl⟩ : syracuseStep 2846927 = 4270391) B4270391
theorem B946399 : Blo 393766 946399 := bstep (se 1 (by rfl) ⟨709799, by rfl⟩ : syracuseStep 946399 = 1419599) B1419599
theorem B1209127 : Blo 393766 1209127 := bstep (se 1 (by rfl) ⟨906845, by rfl⟩ : syracuseStep 1209127 = 1813691) B1813691
theorem B750703 : Blo 393766 750703 := bstep (se 1 (by rfl) ⟨563027, by rfl⟩ : syracuseStep 750703 = 1126055) B1126055
theorem B750779 : Blo 393766 750779 := bstep (se 1 (by rfl) ⟨563084, by rfl⟩ : syracuseStep 750779 = 1126169) B1126169
theorem B13727663 : Blo 393766 13727663 := bstep (se 1 (by rfl) ⟨10295747, by rfl⟩ : syracuseStep 13727663 = 20591495) B20591495
theorem B522343 : Blo 393766 522343 := bstep (se 1 (by rfl) ⟨391757, by rfl⟩ : syracuseStep 522343 = 783515) B783515
theorem B4323881 : Blo 393766 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B1440371 : Blo 393766 1440371 := bstep (se 1 (by rfl) ⟨1080278, by rfl⟩ : syracuseStep 1440371 = 2160557) B2160557
theorem B8092871 : Blo 393766 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B2030791 : Blo 393766 2030791 := bstep (se 1 (by rfl) ⟨1523093, by rfl⟩ : syracuseStep 2030791 = 3046187) B3046187
theorem B3014171 : Blo 393766 3014171 := bstep (se 1 (by rfl) ⟨2260628, by rfl⟩ : syracuseStep 3014171 = 4521257) B4521257
theorem B69271757 : Blo 393766 69271757 := bstep (se 3 (by rfl) ⟨12988454, by rfl⟩ : syracuseStep 69271757 = 25976909) B25976909
theorem B754409 : Blo 393766 754409 := bstep (se 2 (by rfl) ⟨282903, by rfl⟩ : syracuseStep 754409 = 565807) B565807
theorem B754591 : Blo 393766 754591 := bstep (se 1 (by rfl) ⟨565943, by rfl⟩ : syracuseStep 754591 = 1131887) B1131887
theorem B394175 : Blo 393766 394175 := bstep (se 1 (by rfl) ⟨295631, by rfl⟩ : syracuseStep 394175 = 591263) B591263
theorem B590825 : Blo 393766 590825 := bstep (se 2 (by rfl) ⟨221559, by rfl⟩ : syracuseStep 590825 = 443119) B443119
theorem B6784073 : Blo 393766 6784073 := bstep (se 2 (by rfl) ⟨2544027, by rfl⟩ : syracuseStep 6784073 = 5088055) B5088055
theorem B394559 : Blo 393766 394559 := bstep (se 1 (by rfl) ⟨295919, by rfl⟩ : syracuseStep 394559 = 591839) B591839
theorem B394719 : Blo 393766 394719 := bstep (se 1 (by rfl) ⟨296039, by rfl⟩ : syracuseStep 394719 = 592079) B592079
theorem B2000375 : Blo 393766 2000375 := bstep (se 1 (by rfl) ⟨1500281, by rfl⟩ : syracuseStep 2000375 = 3000563) B3000563
theorem B591497 : Blo 393766 591497 := bstep (se 2 (by rfl) ⟨221811, by rfl⟩ : syracuseStep 591497 = 443623) B443623
theorem B395099 : Blo 393766 395099 := bstep (se 1 (by rfl) ⟨296324, by rfl⟩ : syracuseStep 395099 = 592649) B592649
theorem B886751 : Blo 393766 886751 := bstep (se 1 (by rfl) ⟨665063, by rfl⟩ : syracuseStep 886751 = 1330127) B1330127
theorem B395259 : Blo 393766 395259 := bstep (se 1 (by rfl) ⟨296444, by rfl⟩ : syracuseStep 395259 = 592889) B592889
theorem B886967 : Blo 393766 886967 := bstep (se 1 (by rfl) ⟨665225, by rfl⟩ : syracuseStep 886967 = 1330451) B1330451
theorem B887003 : Blo 393766 887003 := bstep (se 1 (by rfl) ⟨665252, by rfl⟩ : syracuseStep 887003 = 1330505) B1330505
theorem B887039 : Blo 393766 887039 := bstep (se 1 (by rfl) ⟨665279, by rfl⟩ : syracuseStep 887039 = 1330559) B1330559
theorem B20122037 : Blo 393766 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B2034115 : Blo 393766 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B592361 : Blo 393766 592361 := bstep (se 2 (by rfl) ⟨222135, by rfl⟩ : syracuseStep 592361 = 444271) B444271
theorem B396223 : Blo 393766 396223 := bstep (se 1 (by rfl) ⟨297167, by rfl⟩ : syracuseStep 396223 = 594335) B594335
theorem B1018835 : Blo 393766 1018835 := bstep (se 1 (by rfl) ⟨764126, by rfl⟩ : syracuseStep 1018835 = 1528253) B1528253
theorem B1444873 : Blo 393766 1444873 := bstep (se 2 (by rfl) ⟨541827, by rfl⟩ : syracuseStep 1444873 = 1083655) B1083655
theorem B593051 : Blo 393766 593051 := bstep (se 1 (by rfl) ⟨444788, by rfl⟩ : syracuseStep 593051 = 889577) B889577
theorem B887975 : Blo 393766 887975 := bstep (se 1 (by rfl) ⟨665981, by rfl⟩ : syracuseStep 887975 = 1331963) B1331963
theorem B396479 : Blo 393766 396479 := bstep (se 1 (by rfl) ⟨297359, by rfl⟩ : syracuseStep 396479 = 594719) B594719
theorem B396591 : Blo 393766 396591 := bstep (se 1 (by rfl) ⟨297443, by rfl⟩ : syracuseStep 396591 = 594887) B594887
theorem B724307 : Blo 393766 724307 := bstep (se 1 (by rfl) ⟨543230, by rfl⟩ : syracuseStep 724307 = 1086461) B1086461
theorem B396799 : Blo 393766 396799 := bstep (se 1 (by rfl) ⟨297599, by rfl⟩ : syracuseStep 396799 = 595199) B595199
theorem B5050025 : Blo 393766 5050025 := bstep (se 2 (by rfl) ⟨1893759, by rfl⟩ : syracuseStep 5050025 = 3787519) B3787519
theorem B888551 : Blo 393766 888551 := bstep (se 1 (by rfl) ⟨666413, by rfl⟩ : syracuseStep 888551 = 1332827) B1332827
theorem B593801 : Blo 393766 593801 := bstep (se 2 (by rfl) ⟨222675, by rfl⟩ : syracuseStep 593801 = 445351) B445351
theorem B2854855 : Blo 393766 2854855 := bstep (se 1 (by rfl) ⟨2141141, by rfl⟩ : syracuseStep 2854855 = 4282283) B4282283
theorem B593897 : Blo 393766 593897 := bstep (se 2 (by rfl) ⟨222711, by rfl⟩ : syracuseStep 593897 = 445423) B445423
theorem B593951 : Blo 393766 593951 := bstep (se 1 (by rfl) ⟨445463, by rfl⟩ : syracuseStep 593951 = 890927) B890927
theorem B3019031 : Blo 393766 3019031 := bstep (se 1 (by rfl) ⟨2264273, by rfl⟩ : syracuseStep 3019031 = 4528547) B4528547
theorem B889145 : Blo 393766 889145 := bstep (se 2 (by rfl) ⟨333429, by rfl⟩ : syracuseStep 889145 = 666859) B666859
theorem B397639 : Blo 393766 397639 := bstep (se 1 (by rfl) ⟨298229, by rfl⟩ : syracuseStep 397639 = 596459) B596459
theorem B1905083 : Blo 393766 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B32608889 : Blo 393766 32608889 := bstep (se 2 (by rfl) ⟨12228333, by rfl⟩ : syracuseStep 32608889 = 24456667) B24456667
theorem B594599 : Blo 393766 594599 := bstep (se 1 (by rfl) ⟨445949, by rfl⟩ : syracuseStep 594599 = 891899) B891899
theorem B594671 : Blo 393766 594671 := bstep (se 1 (by rfl) ⟨446003, by rfl⟩ : syracuseStep 594671 = 892007) B892007
theorem B889595 : Blo 393766 889595 := bstep (se 1 (by rfl) ⟨667196, by rfl⟩ : syracuseStep 889595 = 1334393) B1334393
theorem B889703 : Blo 393766 889703 := bstep (se 1 (by rfl) ⟨667277, by rfl⟩ : syracuseStep 889703 = 1334555) B1334555
theorem B594815 : Blo 393766 594815 := bstep (se 1 (by rfl) ⟨446111, by rfl⟩ : syracuseStep 594815 = 892223) B892223
theorem B7640081 : Blo 393766 7640081 := bstep (se 2 (by rfl) ⟨2865030, by rfl⟩ : syracuseStep 7640081 = 5730061) B5730061
theorem B595103 : Blo 393766 595103 := bstep (se 1 (by rfl) ⟨446327, by rfl⟩ : syracuseStep 595103 = 892655) B892655
theorem B595451 : Blo 393766 595451 := bstep (se 1 (by rfl) ⟨446588, by rfl⟩ : syracuseStep 595451 = 893177) B893177
theorem B595487 : Blo 393766 595487 := bstep (se 1 (by rfl) ⟨446615, by rfl⟩ : syracuseStep 595487 = 893231) B893231
theorem B759719 : Blo 393766 759719 := bstep (se 1 (by rfl) ⟨569789, by rfl⟩ : syracuseStep 759719 = 1139579) B1139579
theorem B596039 : Blo 393766 596039 := bstep (se 1 (by rfl) ⟨447029, by rfl⟩ : syracuseStep 596039 = 894059) B894059
theorem B596135 : Blo 393766 596135 := bstep (se 1 (by rfl) ⟨447101, by rfl⟩ : syracuseStep 596135 = 894203) B894203
theorem B596345 : Blo 393766 596345 := bstep (se 2 (by rfl) ⟨223629, by rfl⟩ : syracuseStep 596345 = 447259) B447259
theorem B1612169 : Blo 393766 1612169 := bstep (se 2 (by rfl) ⟨604563, by rfl⟩ : syracuseStep 1612169 = 1209127) B1209127
theorem B596447 : Blo 393766 596447 := bstep (se 1 (by rfl) ⟨447335, by rfl⟩ : syracuseStep 596447 = 894671) B894671
theorem B3054191 : Blo 393766 3054191 := bstep (se 1 (by rfl) ⟨2290643, by rfl⟩ : syracuseStep 3054191 = 4581287) B4581287
theorem B1907543 : Blo 393766 1907543 := bstep (se 1 (by rfl) ⟨1430657, by rfl⟩ : syracuseStep 1907543 = 2861315) B2861315
theorem B892385 : Blo 393766 892385 := bstep (se 2 (by rfl) ⟨334644, by rfl⟩ : syracuseStep 892385 = 669289) B669289
theorem B1121863 : Blo 393766 1121863 := bstep (se 1 (by rfl) ⟨841397, by rfl⟩ : syracuseStep 1121863 = 1682795) B1682795
theorem B1351343 : Blo 393766 1351343 := bstep (se 1 (by rfl) ⟨1013507, by rfl⟩ : syracuseStep 1351343 = 2027015) B2027015
theorem B8134319 : Blo 393766 8134319 := bstep (se 1 (by rfl) ⟨6100739, by rfl⟩ : syracuseStep 8134319 = 12201479) B12201479
theorem B11411219 : Blo 393766 11411219 := bstep (se 1 (by rfl) ⟨8558414, by rfl⟩ : syracuseStep 11411219 = 17116829) B17116829
theorem B696457 : Blo 393766 696457 := bstep (se 2 (by rfl) ⟨261171, by rfl⟩ : syracuseStep 696457 = 522343) B522343
theorem B631081 : Blo 393766 631081 := bstep (se 2 (by rfl) ⟨236655, by rfl⟩ : syracuseStep 631081 = 473311) B473311
theorem B1450487 : Blo 393766 1450487 := bstep (se 1 (by rfl) ⟨1087865, by rfl⟩ : syracuseStep 1450487 = 2175731) B2175731
theorem B500519 : Blo 393766 500519 := bstep (se 1 (by rfl) ⟨375389, by rfl⟩ : syracuseStep 500519 = 750779) B750779
theorem B2991329 : Blo 393766 2991329 := bstep (se 2 (by rfl) ⟨1121748, by rfl⟩ : syracuseStep 2991329 = 2243497) B2243497
theorem B9151775 : Blo 393766 9151775 := bstep (se 1 (by rfl) ⟨6863831, by rfl⟩ : syracuseStep 9151775 = 13727663) B13727663
theorem B960247 : Blo 393766 960247 := bstep (se 1 (by rfl) ⟨720185, by rfl⟩ : syracuseStep 960247 = 1440371) B1440371
theorem B665455 : Blo 393766 665455 := bstep (se 1 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 665455 = 998183) B998183
theorem B2009447 : Blo 393766 2009447 := bstep (se 1 (by rfl) ⟨1507085, by rfl⟩ : syracuseStep 2009447 = 3014171) B3014171
theorem B3418787 : Blo 393766 3418787 := bstep (se 1 (by rfl) ⟨2564090, by rfl⟩ : syracuseStep 3418787 = 5128181) B5128181
theorem B5057711 : Blo 393766 5057711 := bstep (se 1 (by rfl) ⟨3793283, by rfl⟩ : syracuseStep 5057711 = 7586567) B7586567
theorem B2863187 : Blo 393766 2863187 := bstep (se 1 (by rfl) ⟨2147390, by rfl⟩ : syracuseStep 2863187 = 4294781) B4294781
theorem B3846683 : Blo 393766 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B603371 : Blo 393766 603371 := bstep (se 1 (by rfl) ⟨452528, by rfl⟩ : syracuseStep 603371 = 905057) B905057
theorem B44546183 : Blo 393766 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B4274369 : Blo 393766 4274369 := bstep (se 2 (by rfl) ⟨1602888, by rfl⟩ : syracuseStep 4274369 = 3205777) B3205777
theorem B2996675 : Blo 393766 2996675 := bstep (se 1 (by rfl) ⟨2247506, by rfl⟩ : syracuseStep 2996675 = 4495013) B4495013
theorem B15056209 : Blo 393766 15056209 := bstep (se 2 (by rfl) ⟨5646078, by rfl⟩ : syracuseStep 15056209 = 11292157) B11292157
theorem B5718185 : Blo 393766 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B1261865 : Blo 393766 1261865 := bstep (se 2 (by rfl) ⟨473199, by rfl⟩ : syracuseStep 1261865 = 946399) B946399
theorem B24330557 : Blo 393766 24330557 := bstep (se 3 (by rfl) ⟨4561979, by rfl⟩ : syracuseStep 24330557 = 9123959) B9123959
theorem B443263 : Blo 393766 443263 := bstep (se 1 (by rfl) ⟨332447, by rfl⟩ : syracuseStep 443263 = 664895) B664895
theorem B1000937 : Blo 393766 1000937 := bstep (se 2 (by rfl) ⟨375351, by rfl⟩ : syracuseStep 1000937 = 750703) B750703
theorem B5097077 : Blo 393766 5097077 := bstep (se 5 (by rfl) ⟨238925, by rfl⟩ : syracuseStep 5097077 = 477851) B477851
theorem B1329263 : Blo 393766 1329263 := bstep (se 1 (by rfl) ⟨996947, by rfl⟩ : syracuseStep 1329263 = 1993895) B1993895
theorem B445531 : Blo 393766 445531 := bstep (se 1 (by rfl) ⟨334148, by rfl⟩ : syracuseStep 445531 = 668297) B668297
theorem B2542697 : Blo 393766 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B3001535 : Blo 393766 3001535 := bstep (se 1 (by rfl) ⟨2251151, by rfl⟩ : syracuseStep 3001535 = 4502303) B4502303
theorem B1429159 : Blo 393766 1429159 := bstep (se 1 (by rfl) ⟨1071869, by rfl⟩ : syracuseStep 1429159 = 2143739) B2143739
theorem B2543723 : Blo 393766 2543723 := bstep (se 1 (by rfl) ⟨1907792, by rfl⟩ : syracuseStep 2543723 = 3815585) B3815585
theorem B1331369 : Blo 393766 1331369 := bstep (se 2 (by rfl) ⟨499263, by rfl⟩ : syracuseStep 1331369 = 998527) B998527
theorem B2707721 : Blo 393766 2707721 := bstep (se 2 (by rfl) ⟨1015395, by rfl⟩ : syracuseStep 2707721 = 2030791) B2030791
theorem B5395247 : Blo 393766 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B1005281 : Blo 393766 1005281 := bstep (se 2 (by rfl) ⟨376980, by rfl⟩ : syracuseStep 1005281 = 753961) B753961
theorem B1432055 : Blo 393766 1432055 := bstep (se 1 (by rfl) ⟨1074041, by rfl⟩ : syracuseStep 1432055 = 2148083) B2148083
theorem B1497761 : Blo 393766 1497761 := bstep (se 2 (by rfl) ⟨561660, by rfl⟩ : syracuseStep 1497761 = 1123321) B1123321
theorem B1334447 : Blo 393766 1334447 := bstep (se 1 (by rfl) ⟨1000835, by rfl⟩ : syracuseStep 1334447 = 2001671) B2001671
theorem B18472997 : Blo 393766 18472997 := bstep (se 4 (by rfl) ⟨1731843, by rfl⟩ : syracuseStep 18472997 = 3463687) B3463687
theorem B1073567 : Blo 393766 1073567 := bstep (se 1 (by rfl) ⟨805175, by rfl⟩ : syracuseStep 1073567 = 1610351) B1610351
theorem B1598089 : Blo 393766 1598089 := bstep (se 2 (by rfl) ⟨599283, by rfl⟩ : syracuseStep 1598089 = 1198567) B1198567
theorem B2843579 : Blo 393766 2843579 := bstep (se 1 (by rfl) ⟨2132684, by rfl⟩ : syracuseStep 2843579 = 4265369) B4265369
theorem B1338173 : Blo 393766 1338173 := bstep (se 3 (by rfl) ⟨250907, by rfl⟩ : syracuseStep 1338173 = 501815) B501815
theorem B1600361 : Blo 393766 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B1502621 : Blo 393766 1502621 := bstep (se 3 (by rfl) ⟨281741, by rfl⟩ : syracuseStep 1502621 = 563483) B563483
theorem B13889531 : Blo 393766 13889531 := bstep (se 1 (by rfl) ⟨10417148, by rfl⟩ : syracuseStep 13889531 = 20834297) B20834297
theorem B1603003 : Blo 393766 1603003 := bstep (se 1 (by rfl) ⟨1202252, by rfl⟩ : syracuseStep 1603003 = 2404505) B2404505
theorem B1897951 : Blo 393766 1897951 := bstep (se 1 (by rfl) ⟨1423463, by rfl⟩ : syracuseStep 1897951 = 2846927) B2846927
theorem B1340927 : Blo 393766 1340927 := bstep (se 1 (by rfl) ⟨1005695, by rfl⟩ : syracuseStep 1340927 = 2011391) B2011391
theorem B2258603 : Blo 393766 2258603 := bstep (se 1 (by rfl) ⟨1693952, by rfl⟩ : syracuseStep 2258603 = 3387905) B3387905
theorem B1341629 : Blo 393766 1341629 := bstep (se 3 (by rfl) ⟨251555, by rfl⟩ : syracuseStep 1341629 = 503111) B503111
theorem B3045671 : Blo 393766 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B949033 : Blo 393766 949033 := bstep (se 2 (by rfl) ⟨355887, by rfl⟩ : syracuseStep 949033 = 711775) B711775
theorem B1342331 : Blo 393766 1342331 := bstep (se 1 (by rfl) ⟨1006748, by rfl⟩ : syracuseStep 1342331 = 2013497) B2013497
theorem B2882587 : Blo 393766 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B16220371 : Blo 393766 16220371 := bstep (se 1 (by rfl) ⟨12165278, by rfl⟩ : syracuseStep 16220371 = 24330557) B24330557
theorem B393883 : Blo 393766 393883 := bstep (se 1 (by rfl) ⟨295412, by rfl⟩ : syracuseStep 393883 = 590825) B590825
theorem B4522715 : Blo 393766 4522715 := bstep (se 1 (by rfl) ⟨3392036, by rfl⟩ : syracuseStep 4522715 = 6784073) B6784073
theorem B2130785 : Blo 393766 2130785 := bstep (se 2 (by rfl) ⟨799044, by rfl⟩ : syracuseStep 2130785 = 1598089) B1598089
theorem B394331 : Blo 393766 394331 := bstep (se 1 (by rfl) ⟨295748, by rfl⟩ : syracuseStep 394331 = 591497) B591497
theorem B591017 : Blo 393766 591017 := bstep (se 2 (by rfl) ⟨221631, by rfl⟩ : syracuseStep 591017 = 443263) B443263
theorem B591167 : Blo 393766 591167 := bstep (se 1 (by rfl) ⟨443375, by rfl⟩ : syracuseStep 591167 = 886751) B886751
theorem B886175 : Blo 393766 886175 := bstep (se 1 (by rfl) ⟨664631, by rfl⟩ : syracuseStep 886175 = 1329263) B1329263
theorem B591311 : Blo 393766 591311 := bstep (se 1 (by rfl) ⟨443483, by rfl⟩ : syracuseStep 591311 = 886967) B886967
theorem B591335 : Blo 393766 591335 := bstep (se 1 (by rfl) ⟨443501, by rfl⟩ : syracuseStep 591335 = 887003) B887003
theorem B591359 : Blo 393766 591359 := bstep (se 1 (by rfl) ⟨443519, by rfl⟩ : syracuseStep 591359 = 887039) B887039
theorem B394907 : Blo 393766 394907 := bstep (se 1 (by rfl) ⟨296180, by rfl⟩ : syracuseStep 394907 = 592361) B592361
theorem B395367 : Blo 393766 395367 := bstep (se 1 (by rfl) ⟨296525, by rfl⟩ : syracuseStep 395367 = 593051) B593051
theorem B591983 : Blo 393766 591983 := bstep (se 1 (by rfl) ⟨443987, by rfl⟩ : syracuseStep 591983 = 887975) B887975
theorem B2001023 : Blo 393766 2001023 := bstep (se 1 (by rfl) ⟨1500767, by rfl⟩ : syracuseStep 2001023 = 3001535) B3001535
theorem B1280329 : Blo 393766 1280329 := bstep (se 2 (by rfl) ⟨480123, by rfl⟩ : syracuseStep 1280329 = 960247) B960247
theorem B887273 : Blo 393766 887273 := bstep (se 2 (by rfl) ⟨332727, by rfl⟩ : syracuseStep 887273 = 665455) B665455
theorem B592367 : Blo 393766 592367 := bstep (se 1 (by rfl) ⟨444275, by rfl⟩ : syracuseStep 592367 = 888551) B888551
theorem B395867 : Blo 393766 395867 := bstep (se 1 (by rfl) ⟨296900, by rfl⟩ : syracuseStep 395867 = 593801) B593801
theorem B395931 : Blo 393766 395931 := bstep (se 1 (by rfl) ⟨296948, by rfl⟩ : syracuseStep 395931 = 593897) B593897
theorem B395967 : Blo 393766 395967 := bstep (se 1 (by rfl) ⟨296975, by rfl⟩ : syracuseStep 395967 = 593951) B593951
theorem B887579 : Blo 393766 887579 := bstep (se 1 (by rfl) ⟨665684, by rfl⟩ : syracuseStep 887579 = 1331369) B1331369
theorem B1805147 : Blo 393766 1805147 := bstep (se 1 (by rfl) ⟨1353860, by rfl⟩ : syracuseStep 1805147 = 2707721) B2707721
theorem B592763 : Blo 393766 592763 := bstep (se 1 (by rfl) ⟨444572, by rfl⟩ : syracuseStep 592763 = 889145) B889145
theorem B396399 : Blo 393766 396399 := bstep (se 1 (by rfl) ⟨297299, by rfl⟩ : syracuseStep 396399 = 594599) B594599
theorem B396447 : Blo 393766 396447 := bstep (se 1 (by rfl) ⟨297335, by rfl⟩ : syracuseStep 396447 = 594671) B594671
theorem B593063 : Blo 393766 593063 := bstep (se 1 (by rfl) ⟨444797, by rfl⟩ : syracuseStep 593063 = 889595) B889595
theorem B593135 : Blo 393766 593135 := bstep (se 1 (by rfl) ⟨444851, by rfl⟩ : syracuseStep 593135 = 889703) B889703
theorem B396543 : Blo 393766 396543 := bstep (se 1 (by rfl) ⟨297407, by rfl⟩ : syracuseStep 396543 = 594815) B594815
theorem B396735 : Blo 393766 396735 := bstep (se 1 (by rfl) ⟨297551, by rfl⟩ : syracuseStep 396735 = 595103) B595103
theorem B396967 : Blo 393766 396967 := bstep (se 1 (by rfl) ⟨297725, by rfl⟩ : syracuseStep 396967 = 595451) B595451
theorem B396991 : Blo 393766 396991 := bstep (se 1 (by rfl) ⟨297743, by rfl⟩ : syracuseStep 396991 = 595487) B595487
theorem B397359 : Blo 393766 397359 := bstep (se 1 (by rfl) ⟨298019, by rfl⟩ : syracuseStep 397359 = 596039) B596039
theorem B397423 : Blo 393766 397423 := bstep (se 1 (by rfl) ⟨298067, by rfl⟩ : syracuseStep 397423 = 596135) B596135
theorem B594041 : Blo 393766 594041 := bstep (se 2 (by rfl) ⟨222765, by rfl⟩ : syracuseStep 594041 = 445531) B445531
theorem B397563 : Blo 393766 397563 := bstep (se 1 (by rfl) ⟨298172, by rfl⟩ : syracuseStep 397563 = 596345) B596345
theorem B397631 : Blo 393766 397631 := bstep (se 1 (by rfl) ⟨298223, by rfl⟩ : syracuseStep 397631 = 596447) B596447
theorem B954703 : Blo 393766 954703 := bstep (se 1 (by rfl) ⟨716027, by rfl⟩ : syracuseStep 954703 = 1432055) B1432055
theorem B889631 : Blo 393766 889631 := bstep (se 1 (by rfl) ⟨667223, by rfl⟩ : syracuseStep 889631 = 1334447) B1334447
theorem B1905545 : Blo 393766 1905545 := bstep (se 2 (by rfl) ⟨714579, by rfl⟩ : syracuseStep 1905545 = 1429159) B1429159
theorem B594923 : Blo 393766 594923 := bstep (se 1 (by rfl) ⟨446192, by rfl⟩ : syracuseStep 594923 = 892385) B892385
theorem B7607479 : Blo 393766 7607479 := bstep (se 1 (by rfl) ⟨5705609, by rfl⟩ : syracuseStep 7607479 = 11411219) B11411219
theorem B3806473 : Blo 393766 3806473 := bstep (se 2 (by rfl) ⟨1427427, by rfl⟩ : syracuseStep 3806473 = 2854855) B2854855
theorem B6101183 : Blo 393766 6101183 := bstep (se 1 (by rfl) ⟨4575887, by rfl⟩ : syracuseStep 6101183 = 9151775) B9151775
theorem B892115 : Blo 393766 892115 := bstep (se 1 (by rfl) ⟨669086, by rfl⟩ : syracuseStep 892115 = 1338173) B1338173
theorem B2137337 : Blo 393766 2137337 := bstep (se 2 (by rfl) ⟨801501, by rfl⟩ : syracuseStep 2137337 = 1603003) B1603003
theorem B2530601 : Blo 393766 2530601 := bstep (se 2 (by rfl) ⟨948975, by rfl⟩ : syracuseStep 2530601 = 1897951) B1897951
theorem B1908791 : Blo 393766 1908791 := bstep (se 1 (by rfl) ⟨1431593, by rfl⟩ : syracuseStep 1908791 = 2863187) B2863187
theorem B2564455 : Blo 393766 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B402247 : Blo 393766 402247 := bstep (se 1 (by rfl) ⟨301685, by rfl⟩ : syracuseStep 402247 = 603371) B603371
theorem B893951 : Blo 393766 893951 := bstep (se 1 (by rfl) ⟨670463, by rfl⟩ : syracuseStep 893951 = 1340927) B1340927
theorem B3843449 : Blo 393766 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B43394453 : Blo 393766 43394453 := bstep (se 6 (by rfl) ⟨1017057, by rfl⟩ : syracuseStep 43394453 = 2034115) B2034115
theorem B29697455 : Blo 393766 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B894419 : Blo 393766 894419 := bstep (se 1 (by rfl) ⟨670814, by rfl⟩ : syracuseStep 894419 = 1341629) B1341629
theorem B894887 : Blo 393766 894887 := bstep (se 1 (by rfl) ⟨671165, by rfl⟩ : syracuseStep 894887 = 1342331) B1342331
theorem B3812123 : Blo 393766 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B46181171 : Blo 393766 46181171 := bstep (se 1 (by rfl) ⟨34635878, by rfl⟩ : syracuseStep 46181171 = 69271757) B69271757
theorem B928609 : Blo 393766 928609 := bstep (se 2 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 928609 = 696457) B696457
theorem B502939 : Blo 393766 502939 := bstep (se 1 (by rfl) ⟨377204, by rfl⟩ : syracuseStep 502939 = 754409) B754409
theorem B667291 : Blo 393766 667291 := bstep (se 1 (by rfl) ⟨500468, by rfl⟩ : syracuseStep 667291 = 1000937) B1000937
theorem B13414691 : Blo 393766 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B2012687 : Blo 393766 2012687 := bstep (se 1 (by rfl) ⟨1509515, by rfl⟩ : syracuseStep 2012687 = 3019031) B3019031
theorem B21739259 : Blo 393766 21739259 := bstep (se 1 (by rfl) ⟨16304444, by rfl⟩ : syracuseStep 21739259 = 32608889) B32608889
theorem B5093387 : Blo 393766 5093387 := bstep (se 1 (by rfl) ⟨3820040, by rfl⟩ : syracuseStep 5093387 = 7640081) B7640081
theorem B670187 : Blo 393766 670187 := bstep (se 1 (by rfl) ⟨502640, by rfl⟩ : syracuseStep 670187 = 1005281) B1005281
theorem B506479 : Blo 393766 506479 := bstep (se 1 (by rfl) ⟨379859, by rfl⟩ : syracuseStep 506479 = 759719) B759719
theorem B998507 : Blo 393766 998507 := bstep (se 1 (by rfl) ⟨748880, by rfl⟩ : syracuseStep 998507 = 1497761) B1497761
theorem B900895 : Blo 393766 900895 := bstep (se 1 (by rfl) ⟨675671, by rfl⟩ : syracuseStep 900895 = 1351343) B1351343
theorem B5422879 : Blo 393766 5422879 := bstep (se 1 (by rfl) ⟨4067159, by rfl⟩ : syracuseStep 5422879 = 8134319) B8134319
theorem B966991 : Blo 393766 966991 := bstep (se 1 (by rfl) ⟨725243, by rfl⟩ : syracuseStep 966991 = 1450487) B1450487
theorem B8144509 : Blo 393766 8144509 := bstep (se 3 (by rfl) ⟨1527095, by rfl⟩ : syracuseStep 8144509 = 3054191) B3054191
theorem B80299781 : Blo 393766 80299781 := bstep (se 4 (by rfl) ⟨7528104, by rfl⟩ : syracuseStep 80299781 = 15056209) B15056209
theorem B2279191 : Blo 393766 2279191 := bstep (se 1 (by rfl) ⟨1709393, by rfl⟩ : syracuseStep 2279191 = 3418787) B3418787
theorem B1066907 : Blo 393766 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B1001747 : Blo 393766 1001747 := bstep (se 1 (by rfl) ⟨751310, by rfl⟩ : syracuseStep 1001747 = 1502621) B1502621
theorem B9259687 : Blo 393766 9259687 := bstep (se 1 (by rfl) ⟨6944765, by rfl⟩ : syracuseStep 9259687 = 13889531) B13889531
theorem B1265377 : Blo 393766 1265377 := bstep (se 2 (by rfl) ⟨474516, by rfl⟩ : syracuseStep 1265377 = 949033) B949033
theorem B1495817 : Blo 393766 1495817 := bstep (se 2 (by rfl) ⟨560931, by rfl⟩ : syracuseStep 1495817 = 1121863) B1121863
theorem B841441 : Blo 393766 841441 := bstep (se 2 (by rfl) ⟨315540, by rfl⟩ : syracuseStep 841441 = 631081) B631081
theorem B3364973 : Blo 393766 3364973 := bstep (se 3 (by rfl) ⟨630932, by rfl⟩ : syracuseStep 3364973 = 1261865) B1261865
theorem B1333583 : Blo 393766 1333583 := bstep (se 1 (by rfl) ⟨1000187, by rfl⟩ : syracuseStep 1333583 = 2000375) B2000375
theorem B3398051 : Blo 393766 3398051 := bstep (se 1 (by rfl) ⟨2548538, by rfl⟩ : syracuseStep 3398051 = 5097077) B5097077
theorem B1006121 : Blo 393766 1006121 := bstep (se 2 (by rfl) ⟨377295, by rfl⟩ : syracuseStep 1006121 = 754591) B754591
theorem B679223 : Blo 393766 679223 := bstep (se 1 (by rfl) ⟨509417, by rfl⟩ : syracuseStep 679223 = 1018835) B1018835
theorem B1695131 : Blo 393766 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B1334717 : Blo 393766 1334717 := bstep (se 3 (by rfl) ⟨250259, by rfl⟩ : syracuseStep 1334717 = 500519) B500519
theorem B3366683 : Blo 393766 3366683 := bstep (se 1 (by rfl) ⟨2525012, by rfl⟩ : syracuseStep 3366683 = 5050025) B5050025
theorem B1695815 : Blo 393766 1695815 := bstep (se 1 (by rfl) ⟨1271861, by rfl⟩ : syracuseStep 1695815 = 2543723) B2543723
theorem B1270055 : Blo 393766 1270055 := bstep (se 1 (by rfl) ⟨952541, by rfl⟩ : syracuseStep 1270055 = 1905083) B1905083
theorem B3596831 : Blo 393766 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B7725941 : Blo 393766 7725941 := bstep (se 5 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 7725941 = 724307) B724307
theorem B1926497 : Blo 393766 1926497 := bstep (se 2 (by rfl) ⟨722436, by rfl⟩ : syracuseStep 1926497 = 1444873) B1444873
theorem B1074779 : Blo 393766 1074779 := bstep (se 1 (by rfl) ⟨806084, by rfl⟩ : syracuseStep 1074779 = 1612169) B1612169
theorem B1271695 : Blo 393766 1271695 := bstep (se 1 (by rfl) ⟨953771, by rfl⟩ : syracuseStep 1271695 = 1907543) B1907543
theorem B12315331 : Blo 393766 12315331 := bstep (se 1 (by rfl) ⟨9236498, by rfl⟩ : syracuseStep 12315331 = 18472997) B18472997
theorem B715711 : Blo 393766 715711 := bstep (se 1 (by rfl) ⟨536783, by rfl⟩ : syracuseStep 715711 = 1073567) B1073567
theorem B1895719 : Blo 393766 1895719 := bstep (se 1 (by rfl) ⟨1421789, by rfl⟩ : syracuseStep 1895719 = 2843579) B2843579
theorem B1994219 : Blo 393766 1994219 := bstep (se 1 (by rfl) ⟨1495664, by rfl⟩ : syracuseStep 1994219 = 2991329) B2991329
theorem B1339631 : Blo 393766 1339631 := bstep (se 1 (by rfl) ⟨1004723, by rfl⟩ : syracuseStep 1339631 = 2009447) B2009447
theorem B3371807 : Blo 393766 3371807 := bstep (se 1 (by rfl) ⟨2528855, by rfl⟩ : syracuseStep 3371807 = 5057711) B5057711
theorem B1505735 : Blo 393766 1505735 := bstep (se 1 (by rfl) ⟨1129301, by rfl⟩ : syracuseStep 1505735 = 2258603) B2258603
theorem B2849579 : Blo 393766 2849579 := bstep (se 1 (by rfl) ⟨2137184, by rfl⟩ : syracuseStep 2849579 = 4274369) B4274369
theorem B2030447 : Blo 393766 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B1997783 : Blo 393766 1997783 := bstep (se 1 (by rfl) ⟨1498337, by rfl⟩ : syracuseStep 1997783 = 2996675) B2996675
theorem B21627161 : Blo 393766 21627161 := bstep (se 2 (by rfl) ⟨8110185, by rfl⟩ : syracuseStep 21627161 = 16220371) B16220371
theorem B3015143 : Blo 393766 3015143 := bstep (se 1 (by rfl) ⟨2261357, by rfl⟩ : syracuseStep 3015143 = 4522715) B4522715
theorem B394011 : Blo 393766 394011 := bstep (se 1 (by rfl) ⟨295508, by rfl⟩ : syracuseStep 394011 = 591017) B591017
theorem B394111 : Blo 393766 394111 := bstep (se 1 (by rfl) ⟨295583, by rfl⟩ : syracuseStep 394111 = 591167) B591167
theorem B590783 : Blo 393766 590783 := bstep (se 1 (by rfl) ⟨443087, by rfl⟩ : syracuseStep 590783 = 886175) B886175
theorem B394207 : Blo 393766 394207 := bstep (se 1 (by rfl) ⟨295655, by rfl⟩ : syracuseStep 394207 = 591311) B591311
theorem B394223 : Blo 393766 394223 := bstep (se 1 (by rfl) ⟨295667, by rfl⟩ : syracuseStep 394223 = 591335) B591335
theorem B394239 : Blo 393766 394239 := bstep (se 1 (by rfl) ⟨295679, by rfl⟩ : syracuseStep 394239 = 591359) B591359
theorem B394655 : Blo 393766 394655 := bstep (se 1 (by rfl) ⟨295991, by rfl⟩ : syracuseStep 394655 = 591983) B591983
theorem B591515 : Blo 393766 591515 := bstep (se 1 (by rfl) ⟨443636, by rfl⟩ : syracuseStep 591515 = 887273) B887273
theorem B394911 : Blo 393766 394911 := bstep (se 1 (by rfl) ⟨296183, by rfl⟩ : syracuseStep 394911 = 592367) B592367
theorem B591719 : Blo 393766 591719 := bstep (se 1 (by rfl) ⟨443789, by rfl⟩ : syracuseStep 591719 = 887579) B887579
theorem B395175 : Blo 393766 395175 := bstep (se 1 (by rfl) ⟨296381, by rfl⟩ : syracuseStep 395175 = 592763) B592763
theorem B395375 : Blo 393766 395375 := bstep (se 1 (by rfl) ⟨296531, by rfl⟩ : syracuseStep 395375 = 593063) B593063
theorem B395423 : Blo 393766 395423 := bstep (se 1 (by rfl) ⟨296567, by rfl⟩ : syracuseStep 395423 = 593135) B593135
theorem B396027 : Blo 393766 396027 := bstep (se 1 (by rfl) ⟨297020, by rfl⟩ : syracuseStep 396027 = 594041) B594041
theorem B593087 : Blo 393766 593087 := bstep (se 1 (by rfl) ⟨444815, by rfl⟩ : syracuseStep 593087 = 889631) B889631
theorem B396615 : Blo 393766 396615 := bstep (se 1 (by rfl) ⟨297461, by rfl⟩ : syracuseStep 396615 = 594923) B594923
theorem B49384997 : Blo 393766 49384997 := bstep (se 4 (by rfl) ⟨4629843, by rfl⟩ : syracuseStep 49384997 = 9259687) B9259687
theorem B16420441 : Blo 393766 16420441 := bstep (se 2 (by rfl) ⟨6157665, by rfl⟩ : syracuseStep 16420441 = 12315331) B12315331
theorem B954281 : Blo 393766 954281 := bstep (se 2 (by rfl) ⟨357855, by rfl⟩ : syracuseStep 954281 = 715711) B715711
theorem B4067455 : Blo 393766 4067455 := bstep (se 1 (by rfl) ⟨3050591, by rfl⟩ : syracuseStep 4067455 = 6101183) B6101183
theorem B889055 : Blo 393766 889055 := bstep (se 1 (by rfl) ⟨666791, by rfl⟩ : syracuseStep 889055 = 1333583) B1333583
theorem B2265367 : Blo 393766 2265367 := bstep (se 1 (by rfl) ⟨1699025, by rfl⟩ : syracuseStep 2265367 = 3398051) B3398051
theorem B2527625 : Blo 393766 2527625 := bstep (se 2 (by rfl) ⟨947859, by rfl⟩ : syracuseStep 2527625 = 1895719) B1895719
theorem B594743 : Blo 393766 594743 := bstep (se 1 (by rfl) ⟨446057, by rfl⟩ : syracuseStep 594743 = 892115) B892115
theorem B889721 : Blo 393766 889721 := bstep (se 2 (by rfl) ⟨333645, by rfl⟩ : syracuseStep 889721 = 667291) B667291
theorem B889811 : Blo 393766 889811 := bstep (se 1 (by rfl) ⟨667358, by rfl⟩ : syracuseStep 889811 = 1334717) B1334717
theorem B2397887 : Blo 393766 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B5150627 : Blo 393766 5150627 := bstep (se 1 (by rfl) ⟨3862970, by rfl⟩ : syracuseStep 5150627 = 7725941) B7725941
theorem B595967 : Blo 393766 595967 := bstep (se 1 (by rfl) ⟨446975, by rfl⟩ : syracuseStep 595967 = 893951) B893951
theorem B1284331 : Blo 393766 1284331 := bstep (se 1 (by rfl) ⟨963248, by rfl⟩ : syracuseStep 1284331 = 1926497) B1926497
theorem B2562299 : Blo 393766 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B596279 : Blo 393766 596279 := bstep (se 1 (by rfl) ⟨447209, by rfl⟩ : syracuseStep 596279 = 894419) B894419
theorem B596591 : Blo 393766 596591 := bstep (se 1 (by rfl) ⟨447443, by rfl⟩ : syracuseStep 596591 = 894887) B894887
theorem B1121921 : Blo 393766 1121921 := bstep (se 2 (by rfl) ⟨420720, by rfl⟩ : syracuseStep 1121921 = 841441) B841441
theorem B893087 : Blo 393766 893087 := bstep (se 1 (by rfl) ⟨669815, by rfl⟩ : syracuseStep 893087 = 1339631) B1339631
theorem B1811261 : Blo 393766 1811261 := bstep (se 3 (by rfl) ⟨339611, by rfl⟩ : syracuseStep 1811261 = 679223) B679223
theorem B14492839 : Blo 393766 14492839 := bstep (se 1 (by rfl) ⟨10869629, by rfl⟩ : syracuseStep 14492839 = 21739259) B21739259
theorem B1353631 : Blo 393766 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B665671 : Blo 393766 665671 := bstep (se 1 (by rfl) ⟨499253, by rfl⟩ : syracuseStep 665671 = 998507) B998507
theorem B1289321 : Blo 393766 1289321 := bstep (se 2 (by rfl) ⟨483495, by rfl⟩ : syracuseStep 1289321 = 966991) B966991
theorem B3419273 : Blo 393766 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B1420523 : Blo 393766 1420523 := bstep (se 1 (by rfl) ⟨1065392, by rfl⟩ : syracuseStep 1420523 = 2130785) B2130785
theorem B536329 : Blo 393766 536329 := bstep (se 2 (by rfl) ⟨201123, by rfl⟩ : syracuseStep 536329 = 402247) B402247
theorem B667831 : Blo 393766 667831 := bstep (se 1 (by rfl) ⟨500873, by rfl⟩ : syracuseStep 667831 = 1001747) B1001747
theorem B10859345 : Blo 393766 10859345 := bstep (se 2 (by rfl) ⟨4072254, by rfl⟩ : syracuseStep 10859345 = 8144509) B8144509
theorem B997211 : Blo 393766 997211 := bstep (se 1 (by rfl) ⟨747908, by rfl⟩ : syracuseStep 997211 = 1495817) B1495817
theorem B2243315 : Blo 393766 2243315 := bstep (se 1 (by rfl) ⟨1682486, by rfl⟩ : syracuseStep 2243315 = 3364973) B3364973
theorem B670585 : Blo 393766 670585 := bstep (se 2 (by rfl) ⟨251469, by rfl⟩ : syracuseStep 670585 = 502939) B502939
theorem B670747 : Blo 393766 670747 := bstep (se 1 (by rfl) ⟨503060, by rfl⟩ : syracuseStep 670747 = 1006121) B1006121
theorem B1424891 : Blo 393766 1424891 := bstep (se 1 (by rfl) ⟨1068668, by rfl⟩ : syracuseStep 1424891 = 2137337) B2137337
theorem B1687067 : Blo 393766 1687067 := bstep (se 1 (by rfl) ⟨1265300, by rfl⟩ : syracuseStep 1687067 = 2530601) B2530601
theorem B1130087 : Blo 393766 1130087 := bstep (se 1 (by rfl) ⟨847565, by rfl⟩ : syracuseStep 1130087 = 1695131) B1695131
theorem B1687169 : Blo 393766 1687169 := bstep (se 2 (by rfl) ⟨632688, by rfl⟩ : syracuseStep 1687169 = 1265377) B1265377
theorem B2244455 : Blo 393766 2244455 := bstep (se 1 (by rfl) ⟨1683341, by rfl⟩ : syracuseStep 2244455 = 3366683) B3366683
theorem B1130543 : Blo 393766 1130543 := bstep (se 1 (by rfl) ⟨847907, by rfl⟩ : syracuseStep 1130543 = 1695815) B1695815
theorem B27313685 : Blo 393766 27313685 := bstep (se 6 (by rfl) ⟨640164, by rfl⟩ : syracuseStep 27313685 = 1280329) B1280329
theorem B10143305 : Blo 393766 10143305 := bstep (se 2 (by rfl) ⟨3803739, by rfl⟩ : syracuseStep 10143305 = 7607479) B7607479
theorem B2541415 : Blo 393766 2541415 := bstep (se 1 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 2541415 = 3812123) B3812123
theorem B30787447 : Blo 393766 30787447 := bstep (se 1 (by rfl) ⟨23090585, by rfl⟩ : syracuseStep 30787447 = 46181171) B46181171
theorem B19810325 : Blo 393766 19810325 := bstep (se 6 (by rfl) ⟨464304, by rfl⟩ : syracuseStep 19810325 = 928609) B928609
theorem B1329479 : Blo 393766 1329479 := bstep (se 1 (by rfl) ⟨997109, by rfl⟩ : syracuseStep 1329479 = 1994219) B1994219
theorem B2247871 : Blo 393766 2247871 := bstep (se 1 (by rfl) ⟨1685903, by rfl⟩ : syracuseStep 2247871 = 3371807) B3371807
theorem B675305 : Blo 393766 675305 := bstep (se 2 (by rfl) ⟨253239, by rfl⟩ : syracuseStep 675305 = 506479) B506479
theorem B3395591 : Blo 393766 3395591 := bstep (se 1 (by rfl) ⟨2546693, by rfl⟩ : syracuseStep 3395591 = 5093387) B5093387
theorem B1003823 : Blo 393766 1003823 := bstep (se 1 (by rfl) ⟨752867, by rfl⟩ : syracuseStep 1003823 = 1505735) B1505735
theorem B446791 : Blo 393766 446791 := bstep (se 1 (by rfl) ⟨335093, by rfl⟩ : syracuseStep 446791 = 670187) B670187
theorem B1331855 : Blo 393766 1331855 := bstep (se 1 (by rfl) ⟨998891, by rfl⟩ : syracuseStep 1331855 = 1997783) B1997783
theorem B1201193 : Blo 393766 1201193 := bstep (se 2 (by rfl) ⟨450447, by rfl⟩ : syracuseStep 1201193 = 900895) B900895
theorem B7230505 : Blo 393766 7230505 := bstep (se 2 (by rfl) ⟨2711439, by rfl⟩ : syracuseStep 7230505 = 5422879) B5422879
theorem B35772509 : Blo 393766 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B53533187 : Blo 393766 53533187 := bstep (se 1 (by rfl) ⟨40149890, by rfl⟩ : syracuseStep 53533187 = 80299781) B80299781
theorem B711271 : Blo 393766 711271 := bstep (se 1 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 711271 = 1066907) B1066907
theorem B1334015 : Blo 393766 1334015 := bstep (se 1 (by rfl) ⟨1000511, by rfl⟩ : syracuseStep 1334015 = 2001023) B2001023
theorem B1203431 : Blo 393766 1203431 := bstep (se 1 (by rfl) ⟨902573, by rfl⟩ : syracuseStep 1203431 = 1805147) B1805147
theorem B3038921 : Blo 393766 3038921 := bstep (se 2 (by rfl) ⟨1139595, by rfl⟩ : syracuseStep 3038921 = 2279191) B2279191
theorem B1695593 : Blo 393766 1695593 := bstep (se 2 (by rfl) ⟨635847, by rfl⟩ : syracuseStep 1695593 = 1271695) B1271695
theorem B1270363 : Blo 393766 1270363 := bstep (se 1 (by rfl) ⟨952772, by rfl⟩ : syracuseStep 1270363 = 1905545) B1905545
theorem B79193213 : Blo 393766 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B1272527 : Blo 393766 1272527 := bstep (se 1 (by rfl) ⟨954395, by rfl⟩ : syracuseStep 1272527 = 1908791) B1908791
theorem B846703 : Blo 393766 846703 := bstep (se 1 (by rfl) ⟨635027, by rfl⟩ : syracuseStep 846703 = 1270055) B1270055
theorem B1272937 : Blo 393766 1272937 := bstep (se 2 (by rfl) ⟨477351, by rfl⟩ : syracuseStep 1272937 = 954703) B954703
theorem B28929635 : Blo 393766 28929635 := bstep (se 1 (by rfl) ⟨21697226, by rfl⟩ : syracuseStep 28929635 = 43394453) B43394453
theorem B716519 : Blo 393766 716519 := bstep (se 1 (by rfl) ⟨537389, by rfl⟩ : syracuseStep 716519 = 1074779) B1074779
theorem B5075297 : Blo 393766 5075297 := bstep (se 2 (by rfl) ⟨1903236, by rfl⟩ : syracuseStep 5075297 = 3806473) B3806473
theorem B1341791 : Blo 393766 1341791 := bstep (se 1 (by rfl) ⟨1006343, by rfl⟩ : syracuseStep 1341791 = 2012687) B2012687
theorem B1899719 : Blo 393766 1899719 := bstep (se 1 (by rfl) ⟨1424789, by rfl⟩ : syracuseStep 1899719 = 2849579) B2849579
theorem B753695 : Blo 393766 753695 := bstep (se 1 (by rfl) ⟨565271, by rfl⟩ : syracuseStep 753695 = 1130543) B1130543
theorem B14418107 : Blo 393766 14418107 := bstep (se 1 (by rfl) ⟨10813580, by rfl⟩ : syracuseStep 14418107 = 21627161) B21627161
theorem B393855 : Blo 393766 393855 := bstep (se 1 (by rfl) ⟨295391, by rfl⟩ : syracuseStep 393855 = 590783) B590783
theorem B394343 : Blo 393766 394343 := bstep (se 1 (by rfl) ⟨295757, by rfl⟩ : syracuseStep 394343 = 591515) B591515
theorem B394479 : Blo 393766 394479 := bstep (se 1 (by rfl) ⟨295859, by rfl⟩ : syracuseStep 394479 = 591719) B591719
theorem B13206883 : Blo 393766 13206883 := bstep (se 1 (by rfl) ⟨9905162, by rfl⟩ : syracuseStep 13206883 = 19810325) B19810325
theorem B886319 : Blo 393766 886319 := bstep (se 1 (by rfl) ⟨664739, by rfl⟩ : syracuseStep 886319 = 1329479) B1329479
theorem B395391 : Blo 393766 395391 := bstep (se 1 (by rfl) ⟨296543, by rfl⟩ : syracuseStep 395391 = 593087) B593087
theorem B1804841 : Blo 393766 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B2263727 : Blo 393766 2263727 := bstep (se 1 (by rfl) ⟨1697795, by rfl⟩ : syracuseStep 2263727 = 3395591) B3395591
theorem B887561 : Blo 393766 887561 := bstep (se 2 (by rfl) ⟨332835, by rfl⟩ : syracuseStep 887561 = 665671) B665671
theorem B592703 : Blo 393766 592703 := bstep (se 1 (by rfl) ⟨444527, by rfl⟩ : syracuseStep 592703 = 889055) B889055
theorem B887903 : Blo 393766 887903 := bstep (se 1 (by rfl) ⟨665927, by rfl⟩ : syracuseStep 887903 = 1331855) B1331855
theorem B396495 : Blo 393766 396495 := bstep (se 1 (by rfl) ⟨297371, by rfl⟩ : syracuseStep 396495 = 594743) B594743
theorem B593147 : Blo 393766 593147 := bstep (se 1 (by rfl) ⟨444860, by rfl⟩ : syracuseStep 593147 = 889721) B889721
theorem B593207 : Blo 393766 593207 := bstep (se 1 (by rfl) ⟨444905, by rfl⟩ : syracuseStep 593207 = 889811) B889811
theorem B397311 : Blo 393766 397311 := bstep (se 1 (by rfl) ⟨297983, by rfl⟩ : syracuseStep 397311 = 595967) B595967
theorem B1708199 : Blo 393766 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B397519 : Blo 393766 397519 := bstep (se 1 (by rfl) ⟨298139, by rfl⟩ : syracuseStep 397519 = 596279) B596279
theorem B35688791 : Blo 393766 35688791 := bstep (se 1 (by rfl) ⟨26766593, by rfl⟩ : syracuseStep 35688791 = 53533187) B53533187
theorem B397727 : Blo 393766 397727 := bstep (se 1 (by rfl) ⟨298295, by rfl⟩ : syracuseStep 397727 = 596591) B596591
theorem B889343 : Blo 393766 889343 := bstep (se 1 (by rfl) ⟨667007, by rfl⟩ : syracuseStep 889343 = 1334015) B1334015
theorem B21893921 : Blo 393766 21893921 := bstep (se 2 (by rfl) ⟨8210220, by rfl⟩ : syracuseStep 21893921 = 16420441) B16420441
theorem B595391 : Blo 393766 595391 := bstep (se 1 (by rfl) ⟨446543, by rfl⟩ : syracuseStep 595391 = 893087) B893087
theorem B890441 : Blo 393766 890441 := bstep (se 2 (by rfl) ⟨333915, by rfl⟩ : syracuseStep 890441 = 667831) B667831
theorem B3020489 : Blo 393766 3020489 := bstep (se 2 (by rfl) ⟨1132683, by rfl⟩ : syracuseStep 3020489 = 2265367) B2265367
theorem B595721 : Blo 393766 595721 := bstep (se 2 (by rfl) ⟨223395, by rfl⟩ : syracuseStep 595721 = 446791) B446791
theorem B52795475 : Blo 393766 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B9640673 : Blo 393766 9640673 := bstep (se 2 (by rfl) ⟨3615252, by rfl⟩ : syracuseStep 9640673 = 7230505) B7230505
theorem B859547 : Blo 393766 859547 := bstep (se 1 (by rfl) ⟨644660, by rfl⟩ : syracuseStep 859547 = 1289321) B1289321
theorem B3383531 : Blo 393766 3383531 := bstep (se 1 (by rfl) ⟨2537648, by rfl⟩ : syracuseStep 3383531 = 5075297) B5075297
theorem B1712441 : Blo 393766 1712441 := bstep (se 2 (by rfl) ⟨642165, by rfl⟩ : syracuseStep 1712441 = 1284331) B1284331
theorem B894113 : Blo 393766 894113 := bstep (se 2 (by rfl) ⟨335292, by rfl⟩ : syracuseStep 894113 = 670585) B670585
theorem B664807 : Blo 393766 664807 := bstep (se 1 (by rfl) ⟨498605, by rfl⟩ : syracuseStep 664807 = 997211) B997211
theorem B894329 : Blo 393766 894329 := bstep (se 2 (by rfl) ⟨335373, by rfl⟩ : syracuseStep 894329 = 670747) B670747
theorem B894527 : Blo 393766 894527 := bstep (se 1 (by rfl) ⟨670895, by rfl⟩ : syracuseStep 894527 = 1341791) B1341791
theorem B1124711 : Blo 393766 1124711 := bstep (se 1 (by rfl) ⟨843533, by rfl⟩ : syracuseStep 1124711 = 1687067) B1687067
theorem B1124779 : Blo 393766 1124779 := bstep (se 1 (by rfl) ⟨843584, by rfl⟩ : syracuseStep 1124779 = 1687169) B1687169
theorem B2010095 : Blo 393766 2010095 := bstep (se 1 (by rfl) ⟨1507571, by rfl⟩ : syracuseStep 2010095 = 3015143) B3015143
theorem B6762203 : Blo 393766 6762203 := bstep (se 1 (by rfl) ⟨5071652, by rfl⟩ : syracuseStep 6762203 = 10143305) B10143305
theorem B3388553 : Blo 393766 3388553 := bstep (se 2 (by rfl) ⟨1270707, by rfl⟩ : syracuseStep 3388553 = 2541415) B2541415
theorem B636187 : Blo 393766 636187 := bstep (se 1 (by rfl) ⟨477140, by rfl⟩ : syracuseStep 636187 = 954281) B954281
theorem B669215 : Blo 393766 669215 := bstep (se 1 (by rfl) ⟨501911, by rfl⟩ : syracuseStep 669215 = 1003823) B1003823
theorem B800795 : Blo 393766 800795 := bstep (se 1 (by rfl) ⟨600596, by rfl⟩ : syracuseStep 800795 = 1201193) B1201193
theorem B1128937 : Blo 393766 1128937 := bstep (se 2 (by rfl) ⟨423351, by rfl⟩ : syracuseStep 1128937 = 846703) B846703
theorem B2997161 : Blo 393766 2997161 := bstep (se 2 (by rfl) ⟨1123935, by rfl⟩ : syracuseStep 2997161 = 2247871) B2247871
theorem B1130395 : Blo 393766 1130395 := bstep (se 1 (by rfl) ⟨847796, by rfl⟩ : syracuseStep 1130395 = 1695593) B1695593
theorem B5423273 : Blo 393766 5423273 := bstep (se 2 (by rfl) ⟨2033727, by rfl⟩ : syracuseStep 5423273 = 4067455) B4067455
theorem B2279515 : Blo 393766 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B19286423 : Blo 393766 19286423 := bstep (se 1 (by rfl) ⟨14464817, by rfl⟩ : syracuseStep 19286423 = 28929635) B28929635
theorem B477679 : Blo 393766 477679 := bstep (se 1 (by rfl) ⟨358259, by rfl⟩ : syracuseStep 477679 = 716519) B716519
theorem B1495543 : Blo 393766 1495543 := bstep (se 1 (by rfl) ⟨1121657, by rfl⟩ : syracuseStep 1495543 = 2243315) B2243315
theorem B1266479 : Blo 393766 1266479 := bstep (se 1 (by rfl) ⟨949859, by rfl⟩ : syracuseStep 1266479 = 1899719) B1899719
theorem B1496303 : Blo 393766 1496303 := bstep (se 1 (by rfl) ⟨1122227, by rfl⟩ : syracuseStep 1496303 = 2244455) B2244455
theorem B1693817 : Blo 393766 1693817 := bstep (se 2 (by rfl) ⟨635181, by rfl⟩ : syracuseStep 1693817 = 1270363) B1270363
theorem B18209123 : Blo 393766 18209123 := bstep (se 1 (by rfl) ⟨13656842, by rfl⟩ : syracuseStep 18209123 = 27313685) B27313685
theorem B6740333 : Blo 393766 6740333 := bstep (se 3 (by rfl) ⟨1263812, by rfl⟩ : syracuseStep 6740333 = 2527625) B2527625
theorem B19323785 : Blo 393766 19323785 := bstep (se 2 (by rfl) ⟨7246419, by rfl⟩ : syracuseStep 19323785 = 14492839) B14492839
theorem B450203 : Blo 393766 450203 := bstep (se 1 (by rfl) ⟨337652, by rfl⟩ : syracuseStep 450203 = 675305) B675305
theorem B32923331 : Blo 393766 32923331 := bstep (se 1 (by rfl) ⟨24692498, by rfl⟩ : syracuseStep 32923331 = 49384997) B49384997
theorem B41049929 : Blo 393766 41049929 := bstep (se 2 (by rfl) ⟨15393723, by rfl⟩ : syracuseStep 41049929 = 30787447) B30787447
theorem B1598591 : Blo 393766 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B3433751 : Blo 393766 3433751 := bstep (se 1 (by rfl) ⟨2575313, by rfl⟩ : syracuseStep 3433751 = 5150627) B5150627
theorem B23848339 : Blo 393766 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B1697249 : Blo 393766 1697249 := bstep (se 2 (by rfl) ⟨636468, by rfl⟩ : syracuseStep 1697249 = 1272937) B1272937
theorem B715105 : Blo 393766 715105 := bstep (se 2 (by rfl) ⟨268164, by rfl⟩ : syracuseStep 715105 = 536329) B536329
theorem B747947 : Blo 393766 747947 := bstep (se 1 (by rfl) ⟨560960, by rfl⟩ : syracuseStep 747947 = 1121921) B1121921
theorem B2025947 : Blo 393766 2025947 := bstep (se 1 (by rfl) ⟨1519460, by rfl⟩ : syracuseStep 2025947 = 3038921) B3038921
theorem B1207507 : Blo 393766 1207507 := bstep (se 1 (by rfl) ⟨905630, by rfl⟩ : syracuseStep 1207507 = 1811261) B1811261
theorem B848351 : Blo 393766 848351 := bstep (se 1 (by rfl) ⟨636263, by rfl⟩ : syracuseStep 848351 = 1272527) B1272527
theorem B947015 : Blo 393766 947015 := bstep (se 1 (by rfl) ⟨710261, by rfl⟩ : syracuseStep 947015 = 1420523) B1420523
theorem B7239563 : Blo 393766 7239563 := bstep (se 1 (by rfl) ⟨5429672, by rfl⟩ : syracuseStep 7239563 = 10859345) B10859345
theorem B3209149 : Blo 393766 3209149 := bstep (se 3 (by rfl) ⟨601715, by rfl⟩ : syracuseStep 3209149 = 1203431) B1203431
theorem B948361 : Blo 393766 948361 := bstep (se 2 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 948361 = 711271) B711271
theorem B3799709 : Blo 393766 3799709 := bstep (se 3 (by rfl) ⟨712445, by rfl⟩ : syracuseStep 3799709 = 1424891) B1424891
theorem B753391 : Blo 393766 753391 := bstep (se 1 (by rfl) ⟨565043, by rfl⟩ : syracuseStep 753391 = 1130087) B1130087
theorem B590879 : Blo 393766 590879 := bstep (se 1 (by rfl) ⟨443159, by rfl⟩ : syracuseStep 590879 = 886319) B886319
theorem B2262269 : Blo 393766 2262269 := bstep (se 3 (by rfl) ⟨424175, by rfl⟩ : syracuseStep 2262269 = 848351) B848351
theorem B886409 : Blo 393766 886409 := bstep (se 2 (by rfl) ⟨332403, by rfl⟩ : syracuseStep 886409 = 664807) B664807
theorem B1509151 : Blo 393766 1509151 := bstep (se 1 (by rfl) ⟨1131863, by rfl⟩ : syracuseStep 1509151 = 2263727) B2263727
theorem B591707 : Blo 393766 591707 := bstep (se 1 (by rfl) ⟨443780, by rfl⟩ : syracuseStep 591707 = 887561) B887561
theorem B395135 : Blo 393766 395135 := bstep (se 1 (by rfl) ⟨296351, by rfl⟩ : syracuseStep 395135 = 592703) B592703
theorem B591935 : Blo 393766 591935 := bstep (se 1 (by rfl) ⟨443951, by rfl⟩ : syracuseStep 591935 = 887903) B887903
theorem B395431 : Blo 393766 395431 := bstep (se 1 (by rfl) ⟨296573, by rfl⟩ : syracuseStep 395431 = 593147) B593147
theorem B395471 : Blo 393766 395471 := bstep (se 1 (by rfl) ⟨296603, by rfl⟩ : syracuseStep 395471 = 593207) B593207
theorem B23792527 : Blo 393766 23792527 := bstep (se 1 (by rfl) ⟨17844395, by rfl⟩ : syracuseStep 23792527 = 35688791) B35688791
theorem B592895 : Blo 393766 592895 := bstep (se 1 (by rfl) ⟨444671, by rfl⟩ : syracuseStep 592895 = 889343) B889343
theorem B953473 : Blo 393766 953473 := bstep (se 2 (by rfl) ⟨357552, by rfl⟩ : syracuseStep 953473 = 715105) B715105
theorem B396927 : Blo 393766 396927 := bstep (se 1 (by rfl) ⟨297695, by rfl⟩ : syracuseStep 396927 = 595391) B595391
theorem B593627 : Blo 393766 593627 := bstep (se 1 (by rfl) ⟨445220, by rfl⟩ : syracuseStep 593627 = 890441) B890441
theorem B397147 : Blo 393766 397147 := bstep (se 1 (by rfl) ⟨297860, by rfl⟩ : syracuseStep 397147 = 595721) B595721
theorem B35196983 : Blo 393766 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B4493555 : Blo 393766 4493555 := bstep (se 1 (by rfl) ⟨3370166, by rfl⟩ : syracuseStep 4493555 = 6740333) B6740333
theorem B1610009 : Blo 393766 1610009 := bstep (se 2 (by rfl) ⟨603753, by rfl⟩ : syracuseStep 1610009 = 1207507) B1207507
theorem B6427115 : Blo 393766 6427115 := bstep (se 1 (by rfl) ⟨4820336, by rfl⟩ : syracuseStep 6427115 = 9640673) B9640673
theorem B12882523 : Blo 393766 12882523 := bstep (se 1 (by rfl) ⟨9661892, by rfl⟩ : syracuseStep 12882523 = 19323785) B19323785
theorem B27366619 : Blo 393766 27366619 := bstep (se 1 (by rfl) ⟨20524964, by rfl⟩ : syracuseStep 27366619 = 41049929) B41049929
theorem B596075 : Blo 393766 596075 := bstep (se 1 (by rfl) ⟨447056, by rfl⟩ : syracuseStep 596075 = 894113) B894113
theorem B596219 : Blo 393766 596219 := bstep (se 1 (by rfl) ⟨447164, by rfl⟩ : syracuseStep 596219 = 894329) B894329
theorem B596351 : Blo 393766 596351 := bstep (se 1 (by rfl) ⟨447263, by rfl⟩ : syracuseStep 596351 = 894527) B894527
theorem B498631 : Blo 393766 498631 := bstep (se 1 (by rfl) ⟨373973, by rfl⟩ : syracuseStep 498631 = 747947) B747947
theorem B1350631 : Blo 393766 1350631 := bstep (se 1 (by rfl) ⟨1012973, by rfl⟩ : syracuseStep 1350631 = 2025947) B2025947
theorem B631343 : Blo 393766 631343 := bstep (se 1 (by rfl) ⟨473507, by rfl⟩ : syracuseStep 631343 = 947015) B947015
theorem B4826375 : Blo 393766 4826375 := bstep (se 1 (by rfl) ⟨3619781, by rfl⟩ : syracuseStep 4826375 = 7239563) B7239563
theorem B533863 : Blo 393766 533863 := bstep (se 1 (by rfl) ⟨400397, by rfl⟩ : syracuseStep 533863 = 800795) B800795
theorem B2533139 : Blo 393766 2533139 := bstep (se 1 (by rfl) ⟨1899854, by rfl⟩ : syracuseStep 2533139 = 3799709) B3799709
theorem B502463 : Blo 393766 502463 := bstep (se 1 (by rfl) ⟨376847, by rfl⟩ : syracuseStep 502463 = 753695) B753695
theorem B3615515 : Blo 393766 3615515 := bstep (se 1 (by rfl) ⟨2711636, by rfl⟩ : syracuseStep 3615515 = 5423273) B5423273
theorem B9612071 : Blo 393766 9612071 := bstep (se 1 (by rfl) ⟨7209053, by rfl⟩ : syracuseStep 9612071 = 14418107) B14418107
theorem B12857615 : Blo 393766 12857615 := bstep (se 1 (by rfl) ⟨9643211, by rfl⟩ : syracuseStep 12857615 = 19286423) B19286423
theorem B17609177 : Blo 393766 17609177 := bstep (se 2 (by rfl) ⟨6603441, by rfl⟩ : syracuseStep 17609177 = 13206883) B13206883
theorem B31797785 : Blo 393766 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B14595947 : Blo 393766 14595947 := bstep (se 1 (by rfl) ⟨10946960, by rfl⟩ : syracuseStep 14595947 = 21893921) B21893921
theorem B636905 : Blo 393766 636905 := bstep (se 2 (by rfl) ⟨238839, by rfl⟩ : syracuseStep 636905 = 477679) B477679
theorem B997535 : Blo 393766 997535 := bstep (se 1 (by rfl) ⟨748151, by rfl⟩ : syracuseStep 997535 = 1496303) B1496303
theorem B2013659 : Blo 393766 2013659 := bstep (se 1 (by rfl) ⟨1510244, by rfl⟩ : syracuseStep 2013659 = 3020489) B3020489
theorem B1129211 : Blo 393766 1129211 := bstep (se 1 (by rfl) ⟨846908, by rfl⟩ : syracuseStep 1129211 = 1693817) B1693817
theorem B12139415 : Blo 393766 12139415 := bstep (se 1 (by rfl) ⟨9104561, by rfl⟩ : syracuseStep 12139415 = 18209123) B18209123
theorem B573031 : Blo 393766 573031 := bstep (se 1 (by rfl) ⟨429773, by rfl⟩ : syracuseStep 573031 = 859547) B859547
theorem B1065727 : Blo 393766 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B1131499 : Blo 393766 1131499 := bstep (se 1 (by rfl) ⟨848624, by rfl⟩ : syracuseStep 1131499 = 1697249) B1697249
theorem B4508135 : Blo 393766 4508135 := bstep (se 1 (by rfl) ⟨3381101, by rfl⟩ : syracuseStep 4508135 = 6762203) B6762203
theorem B4278865 : Blo 393766 4278865 := bstep (se 2 (by rfl) ⟨1604574, by rfl⟩ : syracuseStep 4278865 = 3209149) B3209149
theorem B1264481 : Blo 393766 1264481 := bstep (se 2 (by rfl) ⟨474180, by rfl⟩ : syracuseStep 1264481 = 948361) B948361
theorem B446143 : Blo 393766 446143 := bstep (se 1 (by rfl) ⟨334607, by rfl⟩ : syracuseStep 446143 = 669215) B669215
theorem B1200541 : Blo 393766 1200541 := bstep (se 3 (by rfl) ⟨225101, by rfl⟩ : syracuseStep 1200541 = 450203) B450203
theorem B1004521 : Blo 393766 1004521 := bstep (se 2 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 1004521 = 753391) B753391
theorem B1203227 : Blo 393766 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B1138799 : Blo 393766 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B3039353 : Blo 393766 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B844319 : Blo 393766 844319 := bstep (se 1 (by rfl) ⟨633239, by rfl⟩ : syracuseStep 844319 = 1266479) B1266479
theorem B1499705 : Blo 393766 1499705 := bstep (se 2 (by rfl) ⟨562389, by rfl⟩ : syracuseStep 1499705 = 1124779) B1124779
theorem B21948887 : Blo 393766 21948887 := bstep (se 1 (by rfl) ⟨16461665, by rfl⟩ : syracuseStep 21948887 = 32923331) B32923331
theorem B2255687 : Blo 393766 2255687 := bstep (se 1 (by rfl) ⟨1691765, by rfl⟩ : syracuseStep 2255687 = 3383531) B3383531
theorem B1141627 : Blo 393766 1141627 := bstep (se 1 (by rfl) ⟨856220, by rfl⟩ : syracuseStep 1141627 = 1712441) B1712441
theorem B1994057 : Blo 393766 1994057 := bstep (se 2 (by rfl) ⟨747771, by rfl⟩ : syracuseStep 1994057 = 1495543) B1495543
theorem B2289167 : Blo 393766 2289167 := bstep (se 1 (by rfl) ⟨1716875, by rfl⟩ : syracuseStep 2289167 = 3433751) B3433751
theorem B749807 : Blo 393766 749807 := bstep (se 1 (by rfl) ⟨562355, by rfl⟩ : syracuseStep 749807 = 1124711) B1124711
theorem B848249 : Blo 393766 848249 := bstep (se 2 (by rfl) ⟨318093, by rfl⟩ : syracuseStep 848249 = 636187) B636187
theorem B1340063 : Blo 393766 1340063 := bstep (se 1 (by rfl) ⟨1005047, by rfl⟩ : syracuseStep 1340063 = 2010095) B2010095
theorem B1505249 : Blo 393766 1505249 := bstep (se 2 (by rfl) ⟨564468, by rfl⟩ : syracuseStep 1505249 = 1128937) B1128937
theorem B2259035 : Blo 393766 2259035 := bstep (se 1 (by rfl) ⟨1694276, by rfl⟩ : syracuseStep 2259035 = 3388553) B3388553
theorem B1998107 : Blo 393766 1998107 := bstep (se 1 (by rfl) ⟨1498580, by rfl⟩ : syracuseStep 1998107 = 2997161) B2997161
theorem B1507193 : Blo 393766 1507193 := bstep (se 2 (by rfl) ⟨565197, by rfl⟩ : syracuseStep 1507193 = 1130395) B1130395
theorem B393919 : Blo 393766 393919 := bstep (se 1 (by rfl) ⟨295439, by rfl⟩ : syracuseStep 393919 = 590879) B590879
theorem B1508179 : Blo 393766 1508179 := bstep (se 1 (by rfl) ⟨1131134, by rfl⟩ : syracuseStep 1508179 = 2262269) B2262269
theorem B590939 : Blo 393766 590939 := bstep (se 1 (by rfl) ⟨443204, by rfl⟩ : syracuseStep 590939 = 886409) B886409
theorem B394471 : Blo 393766 394471 := bstep (se 1 (by rfl) ⟨295853, by rfl⟩ : syracuseStep 394471 = 591707) B591707
theorem B1508665 : Blo 393766 1508665 := bstep (se 2 (by rfl) ⟨565749, by rfl⟩ : syracuseStep 1508665 = 1131499) B1131499
theorem B394623 : Blo 393766 394623 := bstep (se 1 (by rfl) ⟨295967, by rfl⟩ : syracuseStep 394623 = 591935) B591935
theorem B395263 : Blo 393766 395263 := bstep (se 1 (by rfl) ⟨296447, by rfl⟩ : syracuseStep 395263 = 592895) B592895
theorem B395751 : Blo 393766 395751 := bstep (se 1 (by rfl) ⟨296813, by rfl⟩ : syracuseStep 395751 = 593627) B593627
theorem B23464655 : Blo 393766 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B5705153 : Blo 393766 5705153 := bstep (se 2 (by rfl) ⟨2139432, by rfl⟩ : syracuseStep 5705153 = 4278865) B4278865
theorem B31723369 : Blo 393766 31723369 := bstep (se 2 (by rfl) ⟨11896263, by rfl⟩ : syracuseStep 31723369 = 23792527) B23792527
theorem B397383 : Blo 393766 397383 := bstep (se 1 (by rfl) ⟨298037, by rfl⟩ : syracuseStep 397383 = 596075) B596075
theorem B397479 : Blo 393766 397479 := bstep (se 1 (by rfl) ⟨298109, by rfl⟩ : syracuseStep 397479 = 596219) B596219
theorem B397567 : Blo 393766 397567 := bstep (se 1 (by rfl) ⟨298175, by rfl⟩ : syracuseStep 397567 = 596351) B596351
theorem B594857 : Blo 393766 594857 := bstep (se 2 (by rfl) ⟨223071, by rfl⟩ : syracuseStep 594857 = 446143) B446143
theorem B562879 : Blo 393766 562879 := bstep (se 1 (by rfl) ⟨422159, by rfl⟩ : syracuseStep 562879 = 844319) B844319
theorem B17176697 : Blo 393766 17176697 := bstep (se 2 (by rfl) ⟨6441261, by rfl⟩ : syracuseStep 17176697 = 12882523) B12882523
theorem B3217583 : Blo 393766 3217583 := bstep (se 1 (by rfl) ⟨2413187, by rfl⟩ : syracuseStep 3217583 = 4826375) B4826375
theorem B499871 : Blo 393766 499871 := bstep (se 1 (by rfl) ⟨374903, by rfl⟩ : syracuseStep 499871 = 749807) B749807
theorem B565499 : Blo 393766 565499 := bstep (se 1 (by rfl) ⟨424124, by rfl⟩ : syracuseStep 565499 = 848249) B848249
theorem B11739451 : Blo 393766 11739451 := bstep (se 1 (by rfl) ⟨8804588, by rfl⟩ : syracuseStep 11739451 = 17609177) B17609177
theorem B893375 : Blo 393766 893375 := bstep (se 1 (by rfl) ⟨670031, by rfl⟩ : syracuseStep 893375 = 1340063) B1340063
theorem B664841 : Blo 393766 664841 := bstep (se 2 (by rfl) ⟨249315, by rfl⟩ : syracuseStep 664841 = 498631) B498631
theorem B665023 : Blo 393766 665023 := bstep (se 1 (by rfl) ⟨498767, by rfl⟩ : syracuseStep 665023 = 997535) B997535
theorem B764041 : Blo 393766 764041 := bstep (se 2 (by rfl) ⟨286515, by rfl⟩ : syracuseStep 764041 = 573031) B573031
theorem B2012201 : Blo 393766 2012201 := bstep (se 2 (by rfl) ⟨754575, by rfl⟩ : syracuseStep 2012201 = 1509151) B1509151
theorem B2995703 : Blo 393766 2995703 := bstep (se 1 (by rfl) ⟨2246777, by rfl⟩ : syracuseStep 2995703 = 4493555) B4493555
theorem B1522169 : Blo 393766 1522169 := bstep (se 2 (by rfl) ⟨570813, by rfl⟩ : syracuseStep 1522169 = 1141627) B1141627
theorem B5683877 : Blo 393766 5683877 := bstep (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) B1065727
theorem B802151 : Blo 393766 802151 := bstep (se 1 (by rfl) ⟨601613, by rfl⟩ : syracuseStep 802151 = 1203227) B1203227
theorem B999803 : Blo 393766 999803 := bstep (se 1 (by rfl) ⟨749852, by rfl⟩ : syracuseStep 999803 = 1499705) B1499705
theorem B1688759 : Blo 393766 1688759 := bstep (se 1 (by rfl) ⟨1266569, by rfl⟩ : syracuseStep 1688759 = 2533139) B2533139
theorem B36488825 : Blo 393766 36488825 := bstep (se 2 (by rfl) ⟨13683309, by rfl⟩ : syracuseStep 36488825 = 27366619) B27366619
theorem B14632591 : Blo 393766 14632591 := bstep (se 1 (by rfl) ⟨10974443, by rfl⟩ : syracuseStep 14632591 = 21948887) B21948887
theorem B2410343 : Blo 393766 2410343 := bstep (se 1 (by rfl) ⟨1807757, by rfl⟩ : syracuseStep 2410343 = 3615515) B3615515
theorem B6408047 : Blo 393766 6408047 := bstep (se 1 (by rfl) ⟨4806035, by rfl⟩ : syracuseStep 6408047 = 9612071) B9612071
theorem B1329371 : Blo 393766 1329371 := bstep (se 1 (by rfl) ⟨997028, by rfl⟩ : syracuseStep 1329371 = 1994057) B1994057
theorem B1526111 : Blo 393766 1526111 := bstep (se 1 (by rfl) ⟨1144583, by rfl⟩ : syracuseStep 1526111 = 2289167) B2289167
theorem B8571743 : Blo 393766 8571743 := bstep (se 1 (by rfl) ⟨6428807, by rfl⟩ : syracuseStep 8571743 = 12857615) B12857615
theorem B1003499 : Blo 393766 1003499 := bstep (se 1 (by rfl) ⟨752624, by rfl⟩ : syracuseStep 1003499 = 1505249) B1505249
theorem B1332071 : Blo 393766 1332071 := bstep (se 1 (by rfl) ⟨999053, by rfl⟩ : syracuseStep 1332071 = 1998107) B1998107
theorem B1004795 : Blo 393766 1004795 := bstep (se 1 (by rfl) ⟨753596, by rfl⟩ : syracuseStep 1004795 = 1507193) B1507193
theorem B3036797 : Blo 393766 3036797 := bstep (se 3 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 3036797 = 1138799) B1138799
theorem B3005423 : Blo 393766 3005423 := bstep (se 1 (by rfl) ⟨2254067, by rfl⟩ : syracuseStep 3005423 = 4508135) B4508135
theorem B842987 : Blo 393766 842987 := bstep (se 1 (by rfl) ⟨632240, by rfl⟩ : syracuseStep 842987 = 1264481) B1264481
theorem B1073339 : Blo 393766 1073339 := bstep (se 1 (by rfl) ⟨805004, by rfl⟩ : syracuseStep 1073339 = 1610009) B1610009
theorem B4284743 : Blo 393766 4284743 := bstep (se 1 (by rfl) ⟨3213557, by rfl⟩ : syracuseStep 4284743 = 6427115) B6427115
theorem B1271297 : Blo 393766 1271297 := bstep (se 2 (by rfl) ⟨476736, by rfl⟩ : syracuseStep 1271297 = 953473) B953473
theorem B2026235 : Blo 393766 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B420895 : Blo 393766 420895 := bstep (se 1 (by rfl) ⟨315671, by rfl⟩ : syracuseStep 420895 = 631343) B631343
theorem B1600721 : Blo 393766 1600721 := bstep (se 2 (by rfl) ⟨600270, by rfl⟩ : syracuseStep 1600721 = 1200541) B1200541
theorem B1339361 : Blo 393766 1339361 := bstep (se 2 (by rfl) ⟨502260, by rfl⟩ : syracuseStep 1339361 = 1004521) B1004521
theorem B1339901 : Blo 393766 1339901 := bstep (se 3 (by rfl) ⟨251231, by rfl⟩ : syracuseStep 1339901 = 502463) B502463
theorem B2847269 : Blo 393766 2847269 := bstep (se 4 (by rfl) ⟨266931, by rfl⟩ : syracuseStep 2847269 = 533863) B533863
theorem B1503791 : Blo 393766 1503791 := bstep (se 1 (by rfl) ⟨1127843, by rfl⟩ : syracuseStep 1503791 = 2255687) B2255687
theorem B21198523 : Blo 393766 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B9730631 : Blo 393766 9730631 := bstep (se 1 (by rfl) ⟨7297973, by rfl⟩ : syracuseStep 9730631 = 14595947) B14595947
theorem B1800841 : Blo 393766 1800841 := bstep (se 2 (by rfl) ⟨675315, by rfl⟩ : syracuseStep 1800841 = 1350631) B1350631
theorem B424603 : Blo 393766 424603 := bstep (se 1 (by rfl) ⟨318452, by rfl⟩ : syracuseStep 424603 = 636905) B636905
theorem B1506023 : Blo 393766 1506023 := bstep (se 1 (by rfl) ⟨1129517, by rfl⟩ : syracuseStep 1506023 = 2259035) B2259035
theorem B1342439 : Blo 393766 1342439 := bstep (se 1 (by rfl) ⟨1006829, by rfl⟩ : syracuseStep 1342439 = 2013659) B2013659
theorem B752807 : Blo 393766 752807 := bstep (se 1 (by rfl) ⟨564605, by rfl⟩ : syracuseStep 752807 = 1129211) B1129211
theorem B8092943 : Blo 393766 8092943 := bstep (se 1 (by rfl) ⟨6069707, by rfl⟩ : syracuseStep 8092943 = 12139415) B12139415
theorem B1507997 : Blo 393766 1507997 := bstep (se 3 (by rfl) ⟨282749, by rfl⟩ : syracuseStep 1507997 = 565499) B565499
theorem B393959 : Blo 393766 393959 := bstep (se 1 (by rfl) ⟨295469, by rfl⟩ : syracuseStep 393959 = 590939) B590939
theorem B1606895 : Blo 393766 1606895 := bstep (se 1 (by rfl) ⟨1205171, by rfl⟩ : syracuseStep 1606895 = 2410343) B2410343
theorem B886247 : Blo 393766 886247 := bstep (se 1 (by rfl) ⟨664685, by rfl⟩ : syracuseStep 886247 = 1329371) B1329371
theorem B1017407 : Blo 393766 1017407 := bstep (se 1 (by rfl) ⟨763055, by rfl⟩ : syracuseStep 1017407 = 1526111) B1526111
theorem B886697 : Blo 393766 886697 := bstep (se 2 (by rfl) ⟨332511, by rfl⟩ : syracuseStep 886697 = 665023) B665023
theorem B3803435 : Blo 393766 3803435 := bstep (se 1 (by rfl) ⟨2852576, by rfl⟩ : syracuseStep 3803435 = 5705153) B5705153
theorem B1018721 : Blo 393766 1018721 := bstep (se 2 (by rfl) ⟨382020, by rfl⟩ : syracuseStep 1018721 = 764041) B764041
theorem B888047 : Blo 393766 888047 := bstep (se 1 (by rfl) ⟨666035, by rfl⟩ : syracuseStep 888047 = 1332071) B1332071
theorem B396571 : Blo 393766 396571 := bstep (se 1 (by rfl) ⟨297428, by rfl⟩ : syracuseStep 396571 = 594857) B594857
theorem B2003615 : Blo 393766 2003615 := bstep (se 1 (by rfl) ⟨1502711, by rfl⟩ : syracuseStep 2003615 = 3005423) B3005423
theorem B561991 : Blo 393766 561991 := bstep (se 1 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 561991 = 842987) B842987
theorem B595583 : Blo 393766 595583 := bstep (se 1 (by rfl) ⟨446687, by rfl⟩ : syracuseStep 595583 = 893375) B893375
theorem B676765205 : Blo 393766 676765205 := bstep (se 6 (by rfl) ⟨15861684, by rfl⟩ : syracuseStep 676765205 = 31723369) B31723369
theorem B892907 : Blo 393766 892907 := bstep (se 1 (by rfl) ⟨669680, by rfl⟩ : syracuseStep 892907 = 1339361) B1339361
theorem B893267 : Blo 393766 893267 := bstep (se 1 (by rfl) ⟨669950, by rfl⟩ : syracuseStep 893267 = 1339901) B1339901
theorem B2401121 : Blo 393766 2401121 := bstep (se 2 (by rfl) ⟨900420, by rfl⟩ : syracuseStep 2401121 = 1800841) B1800841
theorem B566137 : Blo 393766 566137 := bstep (se 2 (by rfl) ⟨212301, by rfl⟩ : syracuseStep 566137 = 424603) B424603
theorem B894959 : Blo 393766 894959 := bstep (se 1 (by rfl) ⟨671219, by rfl⟩ : syracuseStep 894959 = 1342439) B1342439
theorem B501871 : Blo 393766 501871 := bstep (se 1 (by rfl) ⟨376403, by rfl⟩ : syracuseStep 501871 = 752807) B752807
theorem B534767 : Blo 393766 534767 := bstep (se 1 (by rfl) ⟨401075, by rfl⟩ : syracuseStep 534767 = 802151) B802151
theorem B666535 : Blo 393766 666535 := bstep (se 1 (by rfl) ⟨499901, by rfl⟩ : syracuseStep 666535 = 999803) B999803
theorem B1125839 : Blo 393766 1125839 := bstep (se 1 (by rfl) ⟨844379, by rfl⟩ : syracuseStep 1125839 = 1688759) B1688759
theorem B24325883 : Blo 393766 24325883 := bstep (se 1 (by rfl) ⟨18244412, by rfl⟩ : syracuseStep 24325883 = 36488825) B36488825
theorem B2010905 : Blo 393766 2010905 := bstep (se 2 (by rfl) ⟨754089, by rfl⟩ : syracuseStep 2010905 = 1508179) B1508179
theorem B4272031 : Blo 393766 4272031 := bstep (se 1 (by rfl) ⟨3204023, by rfl⟩ : syracuseStep 4272031 = 6408047) B6408047
theorem B2011553 : Blo 393766 2011553 := bstep (se 2 (by rfl) ⟨754332, by rfl⟩ : syracuseStep 2011553 = 1508665) B1508665
theorem B15643103 : Blo 393766 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B5714495 : Blo 393766 5714495 := bstep (se 1 (by rfl) ⟨4285871, by rfl⟩ : syracuseStep 5714495 = 8571743) B8571743
theorem B19510121 : Blo 393766 19510121 := bstep (se 2 (by rfl) ⟨7316295, by rfl⟩ : syracuseStep 19510121 = 14632591) B14632591
theorem B668999 : Blo 393766 668999 := bstep (se 1 (by rfl) ⟨501749, by rfl⟩ : syracuseStep 668999 = 1003499) B1003499
theorem B669863 : Blo 393766 669863 := bstep (se 1 (by rfl) ⟨502397, by rfl⟩ : syracuseStep 669863 = 1004795) B1004795
theorem B11451131 : Blo 393766 11451131 := bstep (se 1 (by rfl) ⟨8588348, by rfl⟩ : syracuseStep 11451131 = 17176697) B17176697
theorem B2145055 : Blo 393766 2145055 := bstep (se 1 (by rfl) ⟨1608791, by rfl⟩ : syracuseStep 2145055 = 3217583) B3217583
theorem B2244773 : Blo 393766 2244773 := bstep (se 4 (by rfl) ⟨210447, by rfl⟩ : syracuseStep 2244773 = 420895) B420895
theorem B443227 : Blo 393766 443227 := bstep (se 1 (by rfl) ⟨332420, by rfl⟩ : syracuseStep 443227 = 664841) B664841
theorem B1067147 : Blo 393766 1067147 := bstep (se 1 (by rfl) ⟨800360, by rfl⟩ : syracuseStep 1067147 = 1600721) B1600721
theorem B28264697 : Blo 393766 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B1002527 : Blo 393766 1002527 := bstep (se 1 (by rfl) ⟨751895, by rfl⟩ : syracuseStep 1002527 = 1503791) B1503791
theorem B3002021 : Blo 393766 3002021 := bstep (se 4 (by rfl) ⟨281439, by rfl⟩ : syracuseStep 3002021 = 562879) B562879
theorem B3789251 : Blo 393766 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B1004015 : Blo 393766 1004015 := bstep (se 1 (by rfl) ⟨753011, by rfl⟩ : syracuseStep 1004015 = 1506023) B1506023
theorem B5395295 : Blo 393766 5395295 := bstep (se 1 (by rfl) ⟨4046471, by rfl⟩ : syracuseStep 5395295 = 8092943) B8092943
theorem B15652601 : Blo 393766 15652601 := bstep (se 2 (by rfl) ⟨5869725, by rfl⟩ : syracuseStep 15652601 = 11739451) B11739451
theorem B1332989 : Blo 393766 1332989 := bstep (se 3 (by rfl) ⟨249935, by rfl⟩ : syracuseStep 1332989 = 499871) B499871
theorem B11425981 : Blo 393766 11425981 := bstep (se 3 (by rfl) ⟨2142371, by rfl⟩ : syracuseStep 11425981 = 4284743) B4284743
theorem B7592717 : Blo 393766 7592717 := bstep (se 3 (by rfl) ⟨1423634, by rfl⟩ : syracuseStep 7592717 = 2847269) B2847269
theorem B2024531 : Blo 393766 2024531 := bstep (se 1 (by rfl) ⟨1518398, by rfl⟩ : syracuseStep 2024531 = 3036797) B3036797
theorem B715559 : Blo 393766 715559 := bstep (se 1 (by rfl) ⟨536669, by rfl⟩ : syracuseStep 715559 = 1073339) B1073339
theorem B847531 : Blo 393766 847531 := bstep (se 1 (by rfl) ⟨635648, by rfl⟩ : syracuseStep 847531 = 1271297) B1271297
theorem B5403293 : Blo 393766 5403293 := bstep (se 3 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 5403293 = 2026235) B2026235
theorem B1341467 : Blo 393766 1341467 := bstep (se 1 (by rfl) ⟨1006100, by rfl⟩ : syracuseStep 1341467 = 2012201) B2012201
theorem B1997135 : Blo 393766 1997135 := bstep (se 1 (by rfl) ⟨1497851, by rfl⟩ : syracuseStep 1997135 = 2995703) B2995703
theorem B1014779 : Blo 393766 1014779 := bstep (se 1 (by rfl) ⟨761084, by rfl⟩ : syracuseStep 1014779 = 1522169) B1522169
theorem B6487087 : Blo 393766 6487087 := bstep (se 1 (by rfl) ⟨4865315, by rfl⟩ : syracuseStep 6487087 = 9730631) B9730631
theorem B590831 : Blo 393766 590831 := bstep (se 1 (by rfl) ⟨443123, by rfl⟩ : syracuseStep 590831 = 886247) B886247
theorem B590969 : Blo 393766 590969 := bstep (se 2 (by rfl) ⟨221613, by rfl⟩ : syracuseStep 590969 = 443227) B443227
theorem B754849 : Blo 393766 754849 := bstep (se 2 (by rfl) ⟨283068, by rfl⟩ : syracuseStep 754849 = 566137) B566137
theorem B41714941 : Blo 393766 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B591131 : Blo 393766 591131 := bstep (se 1 (by rfl) ⟨443348, by rfl⟩ : syracuseStep 591131 = 886697) B886697
theorem B18843131 : Blo 393766 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B592031 : Blo 393766 592031 := bstep (se 1 (by rfl) ⟨444023, by rfl⟩ : syracuseStep 592031 = 888047) B888047
theorem B14387453 : Blo 393766 14387453 := bstep (se 3 (by rfl) ⟨2697647, by rfl⟩ : syracuseStep 14387453 = 5395295) B5395295
theorem B2001347 : Blo 393766 2001347 := bstep (se 1 (by rfl) ⟨1501010, by rfl⟩ : syracuseStep 2001347 = 3002021) B3002021
theorem B2526167 : Blo 393766 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B397055 : Blo 393766 397055 := bstep (se 1 (by rfl) ⟨297791, by rfl⟩ : syracuseStep 397055 = 595583) B595583
theorem B888659 : Blo 393766 888659 := bstep (se 1 (by rfl) ⟨666494, by rfl⟩ : syracuseStep 888659 = 1332989) B1332989
theorem B888713 : Blo 393766 888713 := bstep (se 2 (by rfl) ⟨333267, by rfl⟩ : syracuseStep 888713 = 666535) B666535
theorem B595271 : Blo 393766 595271 := bstep (se 1 (by rfl) ⟨446453, by rfl⟩ : syracuseStep 595271 = 892907) B892907
theorem B595511 : Blo 393766 595511 := bstep (se 1 (by rfl) ⟨446633, by rfl⟩ : syracuseStep 595511 = 893267) B893267
theorem B1349687 : Blo 393766 1349687 := bstep (se 1 (by rfl) ⟨1012265, by rfl⟩ : syracuseStep 1349687 = 2024531) B2024531
theorem B596639 : Blo 393766 596639 := bstep (se 1 (by rfl) ⟨447479, by rfl⟩ : syracuseStep 596639 = 894959) B894959
theorem B3809663 : Blo 393766 3809663 := bstep (se 1 (by rfl) ⟨2857247, by rfl⟩ : syracuseStep 3809663 = 5714495) B5714495
theorem B2860073 : Blo 393766 2860073 := bstep (se 2 (by rfl) ⟨1072527, by rfl⟩ : syracuseStep 2860073 = 2145055) B2145055
theorem B894311 : Blo 393766 894311 := bstep (se 1 (by rfl) ⟨670733, by rfl⟩ : syracuseStep 894311 = 1341467) B1341467
theorem B2535623 : Blo 393766 2535623 := bstep (se 1 (by rfl) ⟨1901717, by rfl⟩ : syracuseStep 2535623 = 3803435) B3803435
theorem B668351 : Blo 393766 668351 := bstep (se 1 (by rfl) ⟨501263, by rfl⟩ : syracuseStep 668351 = 1002527) B1002527
theorem B6402989 : Blo 393766 6402989 := bstep (se 3 (by rfl) ⟨1200560, by rfl⟩ : syracuseStep 6402989 = 2401121) B2401121
theorem B669161 : Blo 393766 669161 := bstep (se 2 (by rfl) ⟨250935, by rfl⟩ : syracuseStep 669161 = 501871) B501871
theorem B669343 : Blo 393766 669343 := bstep (se 1 (by rfl) ⟨502007, by rfl⟩ : syracuseStep 669343 = 1004015) B1004015
theorem B10435067 : Blo 393766 10435067 := bstep (se 1 (by rfl) ⟨7826300, by rfl⟩ : syracuseStep 10435067 = 15652601) B15652601
theorem B5061811 : Blo 393766 5061811 := bstep (se 1 (by rfl) ⟨3796358, by rfl⟩ : syracuseStep 5061811 = 7592717) B7592717
theorem B1130041 : Blo 393766 1130041 := bstep (se 2 (by rfl) ⟨423765, by rfl⟩ : syracuseStep 1130041 = 847531) B847531
theorem B1426045 : Blo 393766 1426045 := bstep (se 3 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 1426045 = 534767) B534767
theorem B2706077 : Blo 393766 2706077 := bstep (se 3 (by rfl) ⟨507389, by rfl⟩ : syracuseStep 2706077 = 1014779) B1014779
theorem B445999 : Blo 393766 445999 := bstep (se 1 (by rfl) ⟨334499, by rfl⟩ : syracuseStep 445999 = 668999) B668999
theorem B446575 : Blo 393766 446575 := bstep (se 1 (by rfl) ⟨334931, by rfl⟩ : syracuseStep 446575 = 669863) B669863
theorem B1331423 : Blo 393766 1331423 := bstep (se 1 (by rfl) ⟨998567, by rfl⟩ : syracuseStep 1331423 = 1997135) B1997135
theorem B1496515 : Blo 393766 1496515 := bstep (se 1 (by rfl) ⟨1122386, by rfl⟩ : syracuseStep 1496515 = 2244773) B2244773
theorem B1005331 : Blo 393766 1005331 := bstep (se 1 (by rfl) ⟨753998, by rfl⟩ : syracuseStep 1005331 = 1507997) B1507997
theorem B1071263 : Blo 393766 1071263 := bstep (se 1 (by rfl) ⟨803447, by rfl⟩ : syracuseStep 1071263 = 1606895) B1606895
theorem B711431 : Blo 393766 711431 := bstep (se 1 (by rfl) ⟨533573, by rfl⟩ : syracuseStep 711431 = 1067147) B1067147
theorem B679147 : Blo 393766 679147 := bstep (se 1 (by rfl) ⟨509360, by rfl⟩ : syracuseStep 679147 = 1018721) B1018721
theorem B1335743 : Blo 393766 1335743 := bstep (se 1 (by rfl) ⟨1001807, by rfl⟩ : syracuseStep 1335743 = 2003615) B2003615
theorem B2713085 : Blo 393766 2713085 := bstep (se 3 (by rfl) ⟨508703, by rfl⟩ : syracuseStep 2713085 = 1017407) B1017407
theorem B451176803 : Blo 393766 451176803 := bstep (se 1 (by rfl) ⟨338382602, by rfl⟩ : syracuseStep 451176803 = 676765205) B676765205
theorem B5696041 : Blo 393766 5696041 := bstep (se 2 (by rfl) ⟨2136015, by rfl⟩ : syracuseStep 5696041 = 4272031) B4272031
theorem B749321 : Blo 393766 749321 := bstep (se 2 (by rfl) ⟨280995, by rfl⟩ : syracuseStep 749321 = 561991) B561991
theorem B750559 : Blo 393766 750559 := bstep (se 1 (by rfl) ⟨562919, by rfl⟩ : syracuseStep 750559 = 1125839) B1125839
theorem B16217255 : Blo 393766 16217255 := bstep (se 1 (by rfl) ⟨12162941, by rfl⟩ : syracuseStep 16217255 = 24325883) B24325883
theorem B1340603 : Blo 393766 1340603 := bstep (se 1 (by rfl) ⟨1005452, by rfl⟩ : syracuseStep 1340603 = 2010905) B2010905
theorem B15234641 : Blo 393766 15234641 := bstep (se 2 (by rfl) ⟨5712990, by rfl⟩ : syracuseStep 15234641 = 11425981) B11425981
theorem B1341035 : Blo 393766 1341035 := bstep (se 1 (by rfl) ⟨1005776, by rfl⟩ : syracuseStep 1341035 = 2011553) B2011553
theorem B7632629 : Blo 393766 7632629 := bstep (se 5 (by rfl) ⟨357779, by rfl⟩ : syracuseStep 7632629 = 715559) B715559
theorem B3602195 : Blo 393766 3602195 := bstep (se 1 (by rfl) ⟨2701646, by rfl⟩ : syracuseStep 3602195 = 5403293) B5403293
theorem B13006747 : Blo 393766 13006747 := bstep (se 1 (by rfl) ⟨9755060, by rfl⟩ : syracuseStep 13006747 = 19510121) B19510121
theorem B8649449 : Blo 393766 8649449 := bstep (se 2 (by rfl) ⟨3243543, by rfl⟩ : syracuseStep 8649449 = 6487087) B6487087
theorem B7634087 : Blo 393766 7634087 := bstep (se 1 (by rfl) ⟨5725565, by rfl⟩ : syracuseStep 7634087 = 11451131) B11451131
theorem B393887 : Blo 393766 393887 := bstep (se 1 (by rfl) ⟨295415, by rfl⟩ : syracuseStep 393887 = 590831) B590831
theorem B393979 : Blo 393766 393979 := bstep (se 1 (by rfl) ⟨295484, by rfl⟩ : syracuseStep 393979 = 590969) B590969
theorem B1901393 : Blo 393766 1901393 := bstep (se 2 (by rfl) ⟨713022, by rfl⟩ : syracuseStep 1901393 = 1426045) B1426045
theorem B394087 : Blo 393766 394087 := bstep (se 1 (by rfl) ⟨295565, by rfl⟩ : syracuseStep 394087 = 591131) B591131
theorem B394687 : Blo 393766 394687 := bstep (se 1 (by rfl) ⟨296015, by rfl⟩ : syracuseStep 394687 = 592031) B592031
theorem B1804051 : Blo 393766 1804051 := bstep (se 1 (by rfl) ⟨1353038, by rfl⟩ : syracuseStep 1804051 = 2706077) B2706077
theorem B592439 : Blo 393766 592439 := bstep (se 1 (by rfl) ⟨444329, by rfl⟩ : syracuseStep 592439 = 888659) B888659
theorem B592475 : Blo 393766 592475 := bstep (se 1 (by rfl) ⟨444356, by rfl⟩ : syracuseStep 592475 = 888713) B888713
theorem B887615 : Blo 393766 887615 := bstep (se 1 (by rfl) ⟨665711, by rfl⟩ : syracuseStep 887615 = 1331423) B1331423
theorem B396847 : Blo 393766 396847 := bstep (se 1 (by rfl) ⟨297635, by rfl⟩ : syracuseStep 396847 = 595271) B595271
theorem B397007 : Blo 393766 397007 := bstep (se 1 (by rfl) ⟨297755, by rfl⟩ : syracuseStep 397007 = 595511) B595511
theorem B397759 : Blo 393766 397759 := bstep (se 1 (by rfl) ⟨298319, by rfl⟩ : syracuseStep 397759 = 596639) B596639
theorem B594665 : Blo 393766 594665 := bstep (se 2 (by rfl) ⟨222999, by rfl⟩ : syracuseStep 594665 = 445999) B445999
theorem B595433 : Blo 393766 595433 := bstep (se 2 (by rfl) ⟨223287, by rfl⟩ : syracuseStep 595433 = 446575) B446575
theorem B890495 : Blo 393766 890495 := bstep (se 1 (by rfl) ⟨667871, by rfl⟩ : syracuseStep 890495 = 1335743) B1335743
theorem B2856701 : Blo 393766 2856701 := bstep (se 3 (by rfl) ⟨535631, by rfl⟩ : syracuseStep 2856701 = 1071263) B1071263
theorem B1906715 : Blo 393766 1906715 := bstep (se 1 (by rfl) ⟨1430036, by rfl⟩ : syracuseStep 1906715 = 2860073) B2860073
theorem B596207 : Blo 393766 596207 := bstep (se 1 (by rfl) ⟨447155, by rfl⟩ : syracuseStep 596207 = 894311) B894311
theorem B1808723 : Blo 393766 1808723 := bstep (se 1 (by rfl) ⟨1356542, by rfl⟩ : syracuseStep 1808723 = 2713085) B2713085
theorem B300784535 : Blo 393766 300784535 := bstep (se 1 (by rfl) ⟨225588401, by rfl⟩ : syracuseStep 300784535 = 451176803) B451176803
theorem B892457 : Blo 393766 892457 := bstep (se 2 (by rfl) ⟨334671, by rfl⟩ : syracuseStep 892457 = 669343) B669343
theorem B499547 : Blo 393766 499547 := bstep (se 1 (by rfl) ⟨374660, by rfl⟩ : syracuseStep 499547 = 749321) B749321
theorem B4268659 : Blo 393766 4268659 := bstep (se 1 (by rfl) ⟨3201494, by rfl⟩ : syracuseStep 4268659 = 6402989) B6402989
theorem B893735 : Blo 393766 893735 := bstep (se 1 (by rfl) ⟨670301, by rfl⟩ : syracuseStep 893735 = 1340603) B1340603
theorem B894023 : Blo 393766 894023 := bstep (se 1 (by rfl) ⟨670517, by rfl⟩ : syracuseStep 894023 = 1341035) B1341035
theorem B5088419 : Blo 393766 5088419 := bstep (se 1 (by rfl) ⟨3816314, by rfl⟩ : syracuseStep 5088419 = 7632629) B7632629
theorem B2401463 : Blo 393766 2401463 := bstep (se 1 (by rfl) ⟨1801097, by rfl⟩ : syracuseStep 2401463 = 3602195) B3602195
theorem B6956711 : Blo 393766 6956711 := bstep (se 1 (by rfl) ⟨5217533, by rfl⟩ : syracuseStep 6956711 = 10435067) B10435067
theorem B5089391 : Blo 393766 5089391 := bstep (se 1 (by rfl) ⟨3817043, by rfl⟩ : syracuseStep 5089391 = 7634087) B7634087
theorem B12562087 : Blo 393766 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B55619921 : Blo 393766 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B1684111 : Blo 393766 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B899791 : Blo 393766 899791 := bstep (se 1 (by rfl) ⟨674843, by rfl⟩ : syracuseStep 899791 = 1349687) B1349687
theorem B474287 : Blo 393766 474287 := bstep (se 1 (by rfl) ⟨355715, by rfl⟩ : syracuseStep 474287 = 711431) B711431
theorem B2539775 : Blo 393766 2539775 := bstep (se 1 (by rfl) ⟨1904831, by rfl⟩ : syracuseStep 2539775 = 3809663) B3809663
theorem B3622117 : Blo 393766 3622117 := bstep (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) B679147
theorem B1000745 : Blo 393766 1000745 := bstep (se 2 (by rfl) ⟨375279, by rfl⟩ : syracuseStep 1000745 = 750559) B750559
theorem B1690415 : Blo 393766 1690415 := bstep (se 1 (by rfl) ⟨1267811, by rfl⟩ : syracuseStep 1690415 = 2535623) B2535623
theorem B445567 : Blo 393766 445567 := bstep (se 1 (by rfl) ⟨334175, by rfl⟩ : syracuseStep 445567 = 668351) B668351
theorem B446107 : Blo 393766 446107 := bstep (se 1 (by rfl) ⟨334580, by rfl⟩ : syracuseStep 446107 = 669161) B669161
theorem B9591635 : Blo 393766 9591635 := bstep (se 1 (by rfl) ⟨7193726, by rfl⟩ : syracuseStep 9591635 = 14387453) B14387453
theorem B1006465 : Blo 393766 1006465 := bstep (se 2 (by rfl) ⟨377424, by rfl⟩ : syracuseStep 1006465 = 754849) B754849
theorem B1334231 : Blo 393766 1334231 := bstep (se 1 (by rfl) ⟨1000673, by rfl⟩ : syracuseStep 1334231 = 2001347) B2001347
theorem B7594721 : Blo 393766 7594721 := bstep (se 2 (by rfl) ⟨2848020, by rfl⟩ : syracuseStep 7594721 = 5696041) B5696041
theorem B1995353 : Blo 393766 1995353 := bstep (se 2 (by rfl) ⟨748257, by rfl⟩ : syracuseStep 1995353 = 1496515) B1496515
theorem B1340441 : Blo 393766 1340441 := bstep (se 2 (by rfl) ⟨502665, by rfl⟩ : syracuseStep 1340441 = 1005331) B1005331
theorem B10811503 : Blo 393766 10811503 := bstep (se 1 (by rfl) ⟨8108627, by rfl⟩ : syracuseStep 10811503 = 16217255) B16217255
theorem B10156427 : Blo 393766 10156427 := bstep (se 1 (by rfl) ⟨7617320, by rfl⟩ : syracuseStep 10156427 = 15234641) B15234641
theorem B6749081 : Blo 393766 6749081 := bstep (se 2 (by rfl) ⟨2530905, by rfl⟩ : syracuseStep 6749081 = 5061811) B5061811
theorem B5766299 : Blo 393766 5766299 := bstep (se 1 (by rfl) ⟨4324724, by rfl⟩ : syracuseStep 5766299 = 8649449) B8649449
theorem B1506721 : Blo 393766 1506721 := bstep (se 2 (by rfl) ⟨565020, by rfl⟩ : syracuseStep 1506721 = 1130041) B1130041
theorem B69369317 : Blo 393766 69369317 := bstep (se 4 (by rfl) ⟨6503373, by rfl⟩ : syracuseStep 69369317 = 13006747) B13006747
theorem B394959 : Blo 393766 394959 := bstep (se 1 (by rfl) ⟨296219, by rfl⟩ : syracuseStep 394959 = 592439) B592439
theorem B394983 : Blo 393766 394983 := bstep (se 1 (by rfl) ⟨296237, by rfl⟩ : syracuseStep 394983 = 592475) B592475
theorem B591743 : Blo 393766 591743 := bstep (se 1 (by rfl) ⟨443807, by rfl⟩ : syracuseStep 591743 = 887615) B887615
theorem B396443 : Blo 393766 396443 := bstep (se 1 (by rfl) ⟨297332, by rfl⟩ : syracuseStep 396443 = 594665) B594665
theorem B396955 : Blo 393766 396955 := bstep (se 1 (by rfl) ⟨297716, by rfl⟩ : syracuseStep 396955 = 595433) B595433
theorem B593663 : Blo 393766 593663 := bstep (se 1 (by rfl) ⟨445247, by rfl⟩ : syracuseStep 593663 = 890495) B890495
theorem B1904467 : Blo 393766 1904467 := bstep (se 1 (by rfl) ⟨1428350, by rfl⟩ : syracuseStep 1904467 = 2856701) B2856701
theorem B397471 : Blo 393766 397471 := bstep (se 1 (by rfl) ⟨298103, by rfl⟩ : syracuseStep 397471 = 596207) B596207
theorem B594089 : Blo 393766 594089 := bstep (se 2 (by rfl) ⟨222783, by rfl⟩ : syracuseStep 594089 = 445567) B445567
theorem B6394423 : Blo 393766 6394423 := bstep (se 1 (by rfl) ⟨4795817, by rfl⟩ : syracuseStep 6394423 = 9591635) B9591635
theorem B889487 : Blo 393766 889487 := bstep (se 1 (by rfl) ⟨667115, by rfl⟩ : syracuseStep 889487 = 1334231) B1334231
theorem B594809 : Blo 393766 594809 := bstep (se 2 (by rfl) ⟨223053, by rfl⟩ : syracuseStep 594809 = 446107) B446107
theorem B16749449 : Blo 393766 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B594971 : Blo 393766 594971 := bstep (se 1 (by rfl) ⟨446228, by rfl⟩ : syracuseStep 594971 = 892457) B892457
theorem B595823 : Blo 393766 595823 := bstep (se 1 (by rfl) ⟨446867, by rfl⟩ : syracuseStep 595823 = 893735) B893735
theorem B596015 : Blo 393766 596015 := bstep (se 1 (by rfl) ⟨447011, by rfl⟩ : syracuseStep 596015 = 894023) B894023
theorem B893627 : Blo 393766 893627 := bstep (se 1 (by rfl) ⟨670220, by rfl⟩ : syracuseStep 893627 = 1340441) B1340441
theorem B2008961 : Blo 393766 2008961 := bstep (se 2 (by rfl) ⟨753360, by rfl⟩ : syracuseStep 2008961 = 1506721) B1506721
theorem B4499387 : Blo 393766 4499387 := bstep (se 1 (by rfl) ⟨3374540, by rfl⟩ : syracuseStep 4499387 = 6749081) B6749081
theorem B3844199 : Blo 393766 3844199 := bstep (se 1 (by rfl) ⟨2883149, by rfl⟩ : syracuseStep 3844199 = 5766299) B5766299
theorem B46246211 : Blo 393766 46246211 := bstep (se 1 (by rfl) ⟨34684658, by rfl⟩ : syracuseStep 46246211 = 69369317) B69369317
theorem B667163 : Blo 393766 667163 := bstep (se 1 (by rfl) ⟨500372, by rfl⟩ : syracuseStep 667163 = 1000745) B1000745
theorem B4829489 : Blo 393766 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B1126943 : Blo 393766 1126943 := bstep (se 1 (by rfl) ⟨845207, by rfl⟩ : syracuseStep 1126943 = 1690415) B1690415
theorem B200523023 : Blo 393766 200523023 := bstep (se 1 (by rfl) ⟨150392267, by rfl⟩ : syracuseStep 200523023 = 300784535) B300784535
theorem B5063147 : Blo 393766 5063147 := bstep (se 1 (by rfl) ⟨3797360, by rfl⟩ : syracuseStep 5063147 = 7594721) B7594721
theorem B3392279 : Blo 393766 3392279 := bstep (se 1 (by rfl) ⟨2544209, by rfl⟩ : syracuseStep 3392279 = 5088419) B5088419
theorem B2245481 : Blo 393766 2245481 := bstep (se 2 (by rfl) ⟨842055, by rfl⟩ : syracuseStep 2245481 = 1684111) B1684111
theorem B4637807 : Blo 393766 4637807 := bstep (se 1 (by rfl) ⟨3478355, by rfl⟩ : syracuseStep 4637807 = 6956711) B6956711
theorem B3392927 : Blo 393766 3392927 := bstep (se 1 (by rfl) ⟨2544695, by rfl⟩ : syracuseStep 3392927 = 5089391) B5089391
theorem B37079947 : Blo 393766 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B1330235 : Blo 393766 1330235 := bstep (se 1 (by rfl) ⟨997676, by rfl⟩ : syracuseStep 1330235 = 1995353) B1995353
theorem B1264765 : Blo 393766 1264765 := bstep (se 3 (by rfl) ⟨237143, by rfl⟩ : syracuseStep 1264765 = 474287) B474287
theorem B9621605 : Blo 393766 9621605 := bstep (se 4 (by rfl) ⟨902025, by rfl⟩ : syracuseStep 9621605 = 1804051) B1804051
theorem B6770951 : Blo 393766 6770951 := bstep (se 1 (by rfl) ⟨5078213, by rfl⟩ : syracuseStep 6770951 = 10156427) B10156427
theorem B1332125 : Blo 393766 1332125 := bstep (se 3 (by rfl) ⟨249773, by rfl⟩ : syracuseStep 1332125 = 499547) B499547
theorem B1693183 : Blo 393766 1693183 := bstep (se 1 (by rfl) ⟨1269887, by rfl⟩ : syracuseStep 1693183 = 2539775) B2539775
theorem B1267595 : Blo 393766 1267595 := bstep (se 1 (by rfl) ⟨950696, by rfl⟩ : syracuseStep 1267595 = 1901393) B1901393
theorem B5691545 : Blo 393766 5691545 := bstep (se 2 (by rfl) ⟨2134329, by rfl⟩ : syracuseStep 5691545 = 4268659) B4268659
theorem B1271143 : Blo 393766 1271143 := bstep (se 1 (by rfl) ⟨953357, by rfl⟩ : syracuseStep 1271143 = 1906715) B1906715
theorem B1205815 : Blo 393766 1205815 := bstep (se 1 (by rfl) ⟨904361, by rfl⟩ : syracuseStep 1205815 = 1808723) B1808723
theorem B19195541 : Blo 393766 19195541 := bstep (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) B899791
theorem B1600975 : Blo 393766 1600975 := bstep (se 1 (by rfl) ⟨1200731, by rfl⟩ : syracuseStep 1600975 = 2401463) B2401463
theorem B14415337 : Blo 393766 14415337 := bstep (se 2 (by rfl) ⟨5405751, by rfl⟩ : syracuseStep 14415337 = 10811503) B10811503
theorem B1341953 : Blo 393766 1341953 := bstep (se 2 (by rfl) ⟨503232, by rfl⟩ : syracuseStep 1341953 = 1006465) B1006465
theorem B3375431 : Blo 393766 3375431 := bstep (se 1 (by rfl) ⟨2531573, by rfl⟩ : syracuseStep 3375431 = 5063147) B5063147
theorem B2261519 : Blo 393766 2261519 := bstep (se 1 (by rfl) ⟨1696139, by rfl⟩ : syracuseStep 2261519 = 3392279) B3392279
theorem B2261951 : Blo 393766 2261951 := bstep (se 1 (by rfl) ⟨1696463, by rfl⟩ : syracuseStep 2261951 = 3392927) B3392927
theorem B394495 : Blo 393766 394495 := bstep (se 1 (by rfl) ⟨295871, by rfl⟩ : syracuseStep 394495 = 591743) B591743
theorem B886823 : Blo 393766 886823 := bstep (se 1 (by rfl) ⟨665117, by rfl⟩ : syracuseStep 886823 = 1330235) B1330235
theorem B1607753 : Blo 393766 1607753 := bstep (se 2 (by rfl) ⟨602907, by rfl⟩ : syracuseStep 1607753 = 1205815) B1205815
theorem B395775 : Blo 393766 395775 := bstep (se 1 (by rfl) ⟨296831, by rfl⟩ : syracuseStep 395775 = 593663) B593663
theorem B396059 : Blo 393766 396059 := bstep (se 1 (by rfl) ⟨297044, by rfl⟩ : syracuseStep 396059 = 594089) B594089
theorem B592991 : Blo 393766 592991 := bstep (se 1 (by rfl) ⟨444743, by rfl⟩ : syracuseStep 592991 = 889487) B889487
theorem B396539 : Blo 393766 396539 := bstep (se 1 (by rfl) ⟨297404, by rfl⟩ : syracuseStep 396539 = 594809) B594809
theorem B888083 : Blo 393766 888083 := bstep (se 1 (by rfl) ⟨666062, by rfl⟩ : syracuseStep 888083 = 1332125) B1332125
theorem B396647 : Blo 393766 396647 := bstep (se 1 (by rfl) ⟨297485, by rfl⟩ : syracuseStep 396647 = 594971) B594971
theorem B397215 : Blo 393766 397215 := bstep (se 1 (by rfl) ⟨297911, by rfl⟩ : syracuseStep 397215 = 595823) B595823
theorem B397343 : Blo 393766 397343 := bstep (se 1 (by rfl) ⟨298007, by rfl⟩ : syracuseStep 397343 = 596015) B596015
theorem B2134633 : Blo 393766 2134633 := bstep (se 2 (by rfl) ⟨800487, by rfl⟩ : syracuseStep 2134633 = 1600975) B1600975
theorem B197759717 : Blo 393766 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B595751 : Blo 393766 595751 := bstep (se 1 (by rfl) ⟨446813, by rfl⟩ : syracuseStep 595751 = 893627) B893627
theorem B8525897 : Blo 393766 8525897 := bstep (se 2 (by rfl) ⟨3197211, by rfl⟩ : syracuseStep 8525897 = 6394423) B6394423
theorem B2562799 : Blo 393766 2562799 := bstep (se 1 (by rfl) ⟨1922099, by rfl⟩ : syracuseStep 2562799 = 3844199) B3844199
theorem B3219659 : Blo 393766 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B894635 : Blo 393766 894635 := bstep (se 1 (by rfl) ⟨670976, by rfl⟩ : syracuseStep 894635 = 1341953) B1341953
theorem B3091871 : Blo 393766 3091871 := bstep (se 1 (by rfl) ⟨2318903, by rfl⟩ : syracuseStep 3091871 = 4637807) B4637807
theorem B1686353 : Blo 393766 1686353 := bstep (se 2 (by rfl) ⟨632382, by rfl⟩ : syracuseStep 1686353 = 1264765) B1264765
theorem B2539289 : Blo 393766 2539289 := bstep (se 2 (by rfl) ⟨952233, by rfl⟩ : syracuseStep 2539289 = 1904467) B1904467
theorem B12797027 : Blo 393766 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B2999591 : Blo 393766 2999591 := bstep (se 1 (by rfl) ⟨2249693, by rfl⟩ : syracuseStep 2999591 = 4499387) B4499387
theorem B19220449 : Blo 393766 19220449 := bstep (se 2 (by rfl) ⟨7207668, by rfl⟩ : syracuseStep 19220449 = 14415337) B14415337
theorem B444775 : Blo 393766 444775 := bstep (se 1 (by rfl) ⟨333581, by rfl⟩ : syracuseStep 444775 = 667163) B667163
theorem B133682015 : Blo 393766 133682015 := bstep (se 1 (by rfl) ⟨100261511, by rfl⟩ : syracuseStep 133682015 = 200523023) B200523023
theorem B1496987 : Blo 393766 1496987 := bstep (se 1 (by rfl) ⟨1122740, by rfl⟩ : syracuseStep 1496987 = 2245481) B2245481
theorem B1694857 : Blo 393766 1694857 := bstep (se 2 (by rfl) ⟨635571, by rfl⟩ : syracuseStep 1694857 = 1271143) B1271143
theorem B6414403 : Blo 393766 6414403 := bstep (se 1 (by rfl) ⟨4810802, by rfl⟩ : syracuseStep 6414403 = 9621605) B9621605
theorem B4513967 : Blo 393766 4513967 := bstep (se 1 (by rfl) ⟨3385475, by rfl⟩ : syracuseStep 4513967 = 6770951) B6770951
theorem B11166299 : Blo 393766 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B845063 : Blo 393766 845063 := bstep (se 1 (by rfl) ⟨633797, by rfl⟩ : syracuseStep 845063 = 1267595) B1267595
theorem B3794363 : Blo 393766 3794363 := bstep (se 1 (by rfl) ⟨2845772, by rfl⟩ : syracuseStep 3794363 = 5691545) B5691545
theorem B1339307 : Blo 393766 1339307 := bstep (se 1 (by rfl) ⟨1004480, by rfl⟩ : syracuseStep 1339307 = 2008961) B2008961
theorem B30830807 : Blo 393766 30830807 := bstep (se 1 (by rfl) ⟨23123105, by rfl⟩ : syracuseStep 30830807 = 46246211) B46246211
theorem B2257577 : Blo 393766 2257577 := bstep (se 2 (by rfl) ⟨846591, by rfl⟩ : syracuseStep 2257577 = 1693183) B1693183
theorem B751295 : Blo 393766 751295 := bstep (se 1 (by rfl) ⟨563471, by rfl⟩ : syracuseStep 751295 = 1126943) B1126943
theorem B8552537 : Blo 393766 8552537 := bstep (se 2 (by rfl) ⟨3207201, by rfl⟩ : syracuseStep 8552537 = 6414403) B6414403
theorem B1507679 : Blo 393766 1507679 := bstep (se 1 (by rfl) ⟨1130759, by rfl⟩ : syracuseStep 1507679 = 2261519) B2261519
theorem B1507967 : Blo 393766 1507967 := bstep (se 1 (by rfl) ⟨1130975, by rfl⟩ : syracuseStep 1507967 = 2261951) B2261951
theorem B1999727 : Blo 393766 1999727 := bstep (se 1 (by rfl) ⟨1499795, by rfl⟩ : syracuseStep 1999727 = 2999591) B2999591
theorem B591215 : Blo 393766 591215 := bstep (se 1 (by rfl) ⟨443411, by rfl⟩ : syracuseStep 591215 = 886823) B886823
theorem B395327 : Blo 393766 395327 := bstep (se 1 (by rfl) ⟨296495, by rfl⟩ : syracuseStep 395327 = 592991) B592991
theorem B592055 : Blo 393766 592055 := bstep (se 1 (by rfl) ⟨444041, by rfl⟩ : syracuseStep 592055 = 888083) B888083
theorem B25627265 : Blo 393766 25627265 := bstep (se 2 (by rfl) ⟨9610224, by rfl⟩ : syracuseStep 25627265 = 19220449) B19220449
theorem B593033 : Blo 393766 593033 := bstep (se 2 (by rfl) ⟨222387, by rfl⟩ : syracuseStep 593033 = 444775) B444775
theorem B397167 : Blo 393766 397167 := bstep (se 1 (by rfl) ⟨297875, by rfl⟩ : syracuseStep 397167 = 595751) B595751
theorem B2003453 : Blo 393766 2003453 := bstep (se 3 (by rfl) ⟨375647, by rfl⟩ : syracuseStep 2003453 = 751295) B751295
theorem B7444199 : Blo 393766 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B563375 : Blo 393766 563375 := bstep (se 1 (by rfl) ⟨422531, by rfl⟩ : syracuseStep 563375 = 845063) B845063
theorem B2529575 : Blo 393766 2529575 := bstep (se 1 (by rfl) ⟨1897181, by rfl⟩ : syracuseStep 2529575 = 3794363) B3794363
theorem B596423 : Blo 393766 596423 := bstep (se 1 (by rfl) ⟨447317, by rfl⟩ : syracuseStep 596423 = 894635) B894635
theorem B4496941 : Blo 393766 4496941 := bstep (se 3 (by rfl) ⟨843176, by rfl⟩ : syracuseStep 4496941 = 1686353) B1686353
theorem B892871 : Blo 393766 892871 := bstep (se 1 (by rfl) ⟨669653, by rfl⟩ : syracuseStep 892871 = 1339307) B1339307
theorem B20553871 : Blo 393766 20553871 := bstep (se 1 (by rfl) ⟨15415403, by rfl⟩ : syracuseStep 20553871 = 30830807) B30830807
theorem B3417065 : Blo 393766 3417065 := bstep (se 2 (by rfl) ⟨1281399, by rfl⟩ : syracuseStep 3417065 = 2562799) B2562799
theorem B8531351 : Blo 393766 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B131839811 : Blo 393766 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B997991 : Blo 393766 997991 := bstep (se 1 (by rfl) ⟨748493, by rfl⟩ : syracuseStep 997991 = 1496987) B1496987
theorem B5683931 : Blo 393766 5683931 := bstep (se 1 (by rfl) ⟨4262948, by rfl⟩ : syracuseStep 5683931 = 8525897) B8525897
theorem B2146439 : Blo 393766 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B1692859 : Blo 393766 1692859 := bstep (se 1 (by rfl) ⟨1269644, by rfl⟩ : syracuseStep 1692859 = 2539289) B2539289
theorem B2250287 : Blo 393766 2250287 := bstep (se 1 (by rfl) ⟨1687715, by rfl⟩ : syracuseStep 2250287 = 3375431) B3375431
theorem B1071835 : Blo 393766 1071835 := bstep (se 1 (by rfl) ⟨803876, by rfl⟩ : syracuseStep 1071835 = 1607753) B1607753
theorem B89121343 : Blo 393766 89121343 := bstep (se 1 (by rfl) ⟨66841007, by rfl⟩ : syracuseStep 89121343 = 133682015) B133682015
theorem B3009311 : Blo 393766 3009311 := bstep (se 1 (by rfl) ⟨2256983, by rfl⟩ : syracuseStep 3009311 = 4513967) B4513967
theorem B2846177 : Blo 393766 2846177 := bstep (se 2 (by rfl) ⟨1067316, by rfl⟩ : syracuseStep 2846177 = 2134633) B2134633
theorem B2061247 : Blo 393766 2061247 := bstep (se 1 (by rfl) ⟨1545935, by rfl⟩ : syracuseStep 2061247 = 3091871) B3091871
theorem B1505051 : Blo 393766 1505051 := bstep (se 1 (by rfl) ⟨1128788, by rfl⟩ : syracuseStep 1505051 = 2257577) B2257577
theorem B2259809 : Blo 393766 2259809 := bstep (se 2 (by rfl) ⟨847428, by rfl⟩ : syracuseStep 2259809 = 1694857) B1694857
theorem B5701691 : Blo 393766 5701691 := bstep (se 1 (by rfl) ⟨4276268, by rfl⟩ : syracuseStep 5701691 = 8552537) B8552537
theorem B394143 : Blo 393766 394143 := bstep (se 1 (by rfl) ⟨295607, by rfl⟩ : syracuseStep 394143 = 591215) B591215
theorem B394703 : Blo 393766 394703 := bstep (se 1 (by rfl) ⟨296027, by rfl⟩ : syracuseStep 394703 = 592055) B592055
theorem B395355 : Blo 393766 395355 := bstep (se 1 (by rfl) ⟨296516, by rfl⟩ : syracuseStep 395355 = 593033) B593033
theorem B397615 : Blo 393766 397615 := bstep (se 1 (by rfl) ⟨298211, by rfl⟩ : syracuseStep 397615 = 596423) B596423
theorem B595247 : Blo 393766 595247 := bstep (se 1 (by rfl) ⟨446435, by rfl⟩ : syracuseStep 595247 = 892871) B892871
theorem B2006207 : Blo 393766 2006207 := bstep (se 1 (by rfl) ⟨1504655, by rfl⟩ : syracuseStep 2006207 = 3009311) B3009311
theorem B87893207 : Blo 393766 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B665327 : Blo 393766 665327 := bstep (se 1 (by rfl) ⟨498995, by rfl⟩ : syracuseStep 665327 = 997991) B997991
theorem B27405161 : Blo 393766 27405161 := bstep (se 2 (by rfl) ⟨10276935, by rfl⟩ : syracuseStep 27405161 = 20553871) B20553871
theorem B118828457 : Blo 393766 118828457 := bstep (se 2 (by rfl) ⟨44560671, by rfl⟩ : syracuseStep 118828457 = 89121343) B89121343
theorem B17084843 : Blo 393766 17084843 := bstep (se 1 (by rfl) ⟨12813632, by rfl⟩ : syracuseStep 17084843 = 25627265) B25627265
theorem B5716453 : Blo 393766 5716453 := bstep (se 4 (by rfl) ⟨535917, by rfl⟩ : syracuseStep 5716453 = 1071835) B1071835
theorem B4962799 : Blo 393766 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B1686383 : Blo 393766 1686383 := bstep (se 1 (by rfl) ⟨1264787, by rfl⟩ : syracuseStep 1686383 = 2529575) B2529575
theorem B2278043 : Blo 393766 2278043 := bstep (se 1 (by rfl) ⟨1708532, by rfl⟩ : syracuseStep 2278043 = 3417065) B3417065
theorem B5687567 : Blo 393766 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B1003367 : Blo 393766 1003367 := bstep (se 1 (by rfl) ⟨752525, by rfl⟩ : syracuseStep 1003367 = 1505051) B1505051
theorem B3789287 : Blo 393766 3789287 := bstep (se 1 (by rfl) ⟨2841965, by rfl⟩ : syracuseStep 3789287 = 5683931) B5683931
theorem B1430959 : Blo 393766 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B1005119 : Blo 393766 1005119 := bstep (se 1 (by rfl) ⟨753839, by rfl⟩ : syracuseStep 1005119 = 1507679) B1507679
theorem B1005311 : Blo 393766 1005311 := bstep (se 1 (by rfl) ⟨753983, by rfl⟩ : syracuseStep 1005311 = 1507967) B1507967
theorem B1333151 : Blo 393766 1333151 := bstep (se 1 (by rfl) ⟨999863, by rfl⟩ : syracuseStep 1333151 = 1999727) B1999727
theorem B1335635 : Blo 393766 1335635 := bstep (se 1 (by rfl) ⟨1001726, by rfl⟩ : syracuseStep 1335635 = 2003453) B2003453
theorem B1500191 : Blo 393766 1500191 := bstep (se 1 (by rfl) ⟨1125143, by rfl⟩ : syracuseStep 1500191 = 2250287) B2250287
theorem B1502333 : Blo 393766 1502333 := bstep (se 3 (by rfl) ⟨281687, by rfl⟩ : syracuseStep 1502333 = 563375) B563375
theorem B2748329 : Blo 393766 2748329 := bstep (se 2 (by rfl) ⟨1030623, by rfl⟩ : syracuseStep 2748329 = 2061247) B2061247
theorem B2257145 : Blo 393766 2257145 := bstep (se 2 (by rfl) ⟨846429, by rfl⟩ : syracuseStep 2257145 = 1692859) B1692859
theorem B1897451 : Blo 393766 1897451 := bstep (se 1 (by rfl) ⟨1423088, by rfl⟩ : syracuseStep 1897451 = 2846177) B2846177
theorem B23983685 : Blo 393766 23983685 := bstep (se 4 (by rfl) ⟨2248470, by rfl⟩ : syracuseStep 23983685 = 4496941) B4496941
theorem B1506539 : Blo 393766 1506539 := bstep (se 1 (by rfl) ⟨1129904, by rfl⟩ : syracuseStep 1506539 = 2259809) B2259809
theorem B3801127 : Blo 393766 3801127 := bstep (se 1 (by rfl) ⟨2850845, by rfl⟩ : syracuseStep 3801127 = 5701691) B5701691
theorem B2526191 : Blo 393766 2526191 := bstep (se 1 (by rfl) ⟨1894643, by rfl⟩ : syracuseStep 2526191 = 3789287) B3789287
theorem B396831 : Blo 393766 396831 := bstep (se 1 (by rfl) ⟨297623, by rfl⟩ : syracuseStep 396831 = 595247) B595247
theorem B888767 : Blo 393766 888767 := bstep (se 1 (by rfl) ⟨666575, by rfl⟩ : syracuseStep 888767 = 1333151) B1333151
theorem B890423 : Blo 393766 890423 := bstep (se 1 (by rfl) ⟨667817, by rfl⟩ : syracuseStep 890423 = 1335635) B1335635
theorem B58595471 : Blo 393766 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B1907945 : Blo 393766 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B1124255 : Blo 393766 1124255 := bstep (se 1 (by rfl) ⟨843191, by rfl⟩ : syracuseStep 1124255 = 1686383) B1686383
theorem B1518695 : Blo 393766 1518695 := bstep (se 1 (by rfl) ⟨1139021, by rfl⟩ : syracuseStep 1518695 = 2278043) B2278043
theorem B668911 : Blo 393766 668911 := bstep (se 1 (by rfl) ⟨501683, by rfl⟩ : syracuseStep 668911 = 1003367) B1003367
theorem B670079 : Blo 393766 670079 := bstep (se 1 (by rfl) ⟨502559, by rfl⟩ : syracuseStep 670079 = 1005119) B1005119
theorem B670207 : Blo 393766 670207 := bstep (se 1 (by rfl) ⟨502655, by rfl⟩ : syracuseStep 670207 = 1005311) B1005311
theorem B1000127 : Blo 393766 1000127 := bstep (se 1 (by rfl) ⟨750095, by rfl⟩ : syracuseStep 1000127 = 1500191) B1500191
theorem B443551 : Blo 393766 443551 := bstep (se 1 (by rfl) ⟨332663, by rfl⟩ : syracuseStep 443551 = 665327) B665327
theorem B18270107 : Blo 393766 18270107 := bstep (se 1 (by rfl) ⟨13702580, by rfl⟩ : syracuseStep 18270107 = 27405161) B27405161
theorem B1001555 : Blo 393766 1001555 := bstep (se 1 (by rfl) ⟨751166, by rfl⟩ : syracuseStep 1001555 = 1502333) B1502333
theorem B79218971 : Blo 393766 79218971 := bstep (se 1 (by rfl) ⟨59414228, by rfl⟩ : syracuseStep 79218971 = 118828457) B118828457
theorem B11389895 : Blo 393766 11389895 := bstep (se 1 (by rfl) ⟨8542421, by rfl⟩ : syracuseStep 11389895 = 17084843) B17084843
theorem B7621937 : Blo 393766 7621937 := bstep (se 2 (by rfl) ⟨2858226, by rfl⟩ : syracuseStep 7621937 = 5716453) B5716453
theorem B1264967 : Blo 393766 1264967 := bstep (se 1 (by rfl) ⟨948725, by rfl⟩ : syracuseStep 1264967 = 1897451) B1897451
theorem B1004359 : Blo 393766 1004359 := bstep (se 1 (by rfl) ⟨753269, by rfl⟩ : syracuseStep 1004359 = 1506539) B1506539
theorem B3791711 : Blo 393766 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B1337471 : Blo 393766 1337471 := bstep (se 1 (by rfl) ⟨1003103, by rfl⟩ : syracuseStep 1337471 = 2006207) B2006207
theorem B1832219 : Blo 393766 1832219 := bstep (se 1 (by rfl) ⟨1374164, by rfl⟩ : syracuseStep 1832219 = 2748329) B2748329
theorem B1504763 : Blo 393766 1504763 := bstep (se 1 (by rfl) ⟨1128572, by rfl⟩ : syracuseStep 1504763 = 2257145) B2257145
theorem B6617065 : Blo 393766 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B15989123 : Blo 393766 15989123 := bstep (se 1 (by rfl) ⟨11991842, by rfl⟩ : syracuseStep 15989123 = 23983685) B23983685
theorem B591401 : Blo 393766 591401 := bstep (se 2 (by rfl) ⟨221775, by rfl⟩ : syracuseStep 591401 = 443551) B443551
theorem B5081291 : Blo 393766 5081291 := bstep (se 1 (by rfl) ⟨3810968, by rfl⟩ : syracuseStep 5081291 = 7621937) B7621937
theorem B592511 : Blo 393766 592511 := bstep (se 1 (by rfl) ⟨444383, by rfl⟩ : syracuseStep 592511 = 888767) B888767
theorem B593615 : Blo 393766 593615 := bstep (se 1 (by rfl) ⟨445211, by rfl⟩ : syracuseStep 593615 = 890423) B890423
theorem B39063647 : Blo 393766 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B2527807 : Blo 393766 2527807 := bstep (se 1 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 2527807 = 3791711) B3791711
theorem B42637661 : Blo 393766 42637661 := bstep (se 3 (by rfl) ⟨7994561, by rfl⟩ : syracuseStep 42637661 = 15989123) B15989123
theorem B891647 : Blo 393766 891647 := bstep (se 1 (by rfl) ⟨668735, by rfl⟩ : syracuseStep 891647 = 1337471) B1337471
theorem B891881 : Blo 393766 891881 := bstep (se 2 (by rfl) ⟨334455, by rfl⟩ : syracuseStep 891881 = 668911) B668911
theorem B8822753 : Blo 393766 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B893609 : Blo 393766 893609 := bstep (se 2 (by rfl) ⟨335103, by rfl⟩ : syracuseStep 893609 = 670207) B670207
theorem B1221479 : Blo 393766 1221479 := bstep (se 1 (by rfl) ⟨916109, by rfl⟩ : syracuseStep 1221479 = 1832219) B1832219
theorem B666751 : Blo 393766 666751 := bstep (se 1 (by rfl) ⟨500063, by rfl⟩ : syracuseStep 666751 = 1000127) B1000127
theorem B667703 : Blo 393766 667703 := bstep (se 1 (by rfl) ⟨500777, by rfl⟩ : syracuseStep 667703 = 1001555) B1001555
theorem B1684127 : Blo 393766 1684127 := bstep (se 1 (by rfl) ⟨1263095, by rfl⟩ : syracuseStep 1684127 = 2526191) B2526191
theorem B1003175 : Blo 393766 1003175 := bstep (se 1 (by rfl) ⟨752381, by rfl⟩ : syracuseStep 1003175 = 1504763) B1504763
theorem B446719 : Blo 393766 446719 := bstep (se 1 (by rfl) ⟨335039, by rfl⟩ : syracuseStep 446719 = 670079) B670079
theorem B5068169 : Blo 393766 5068169 := bstep (se 2 (by rfl) ⟨1900563, by rfl⟩ : syracuseStep 5068169 = 3801127) B3801127
theorem B12180071 : Blo 393766 12180071 := bstep (se 1 (by rfl) ⟨9135053, by rfl⟩ : syracuseStep 12180071 = 18270107) B18270107
theorem B52812647 : Blo 393766 52812647 := bstep (se 1 (by rfl) ⟨39609485, by rfl⟩ : syracuseStep 52812647 = 79218971) B79218971
theorem B7593263 : Blo 393766 7593263 := bstep (se 1 (by rfl) ⟨5694947, by rfl⟩ : syracuseStep 7593263 = 11389895) B11389895
theorem B843311 : Blo 393766 843311 := bstep (se 1 (by rfl) ⟨632483, by rfl⟩ : syracuseStep 843311 = 1264967) B1264967
theorem B1271963 : Blo 393766 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B1339145 : Blo 393766 1339145 := bstep (se 2 (by rfl) ⟨502179, by rfl⟩ : syracuseStep 1339145 = 1004359) B1004359
theorem B749503 : Blo 393766 749503 := bstep (se 1 (by rfl) ⟨562127, by rfl⟩ : syracuseStep 749503 = 1124255) B1124255
theorem B1012463 : Blo 393766 1012463 := bstep (se 1 (by rfl) ⟨759347, by rfl⟩ : syracuseStep 1012463 = 1518695) B1518695
theorem B394267 : Blo 393766 394267 := bstep (se 1 (by rfl) ⟨295700, by rfl⟩ : syracuseStep 394267 = 591401) B591401
theorem B395007 : Blo 393766 395007 := bstep (se 1 (by rfl) ⟨296255, by rfl⟩ : syracuseStep 395007 = 592511) B592511
theorem B395743 : Blo 393766 395743 := bstep (se 1 (by rfl) ⟨296807, by rfl⟩ : syracuseStep 395743 = 593615) B593615
theorem B3378779 : Blo 393766 3378779 := bstep (se 1 (by rfl) ⟨2534084, by rfl⟩ : syracuseStep 3378779 = 5068169) B5068169
theorem B889001 : Blo 393766 889001 := bstep (se 2 (by rfl) ⟨333375, by rfl⟩ : syracuseStep 889001 = 666751) B666751
theorem B594431 : Blo 393766 594431 := bstep (se 1 (by rfl) ⟨445823, by rfl⟩ : syracuseStep 594431 = 891647) B891647
theorem B594587 : Blo 393766 594587 := bstep (se 1 (by rfl) ⟨445940, by rfl⟩ : syracuseStep 594587 = 891881) B891881
theorem B595625 : Blo 393766 595625 := bstep (se 2 (by rfl) ⟨223359, by rfl⟩ : syracuseStep 595625 = 446719) B446719
theorem B595739 : Blo 393766 595739 := bstep (se 1 (by rfl) ⟨446804, by rfl⟩ : syracuseStep 595739 = 893609) B893609
theorem B892763 : Blo 393766 892763 := bstep (se 1 (by rfl) ⟨669572, by rfl⟩ : syracuseStep 892763 = 1339145) B1339145
theorem B1122751 : Blo 393766 1122751 := bstep (se 1 (by rfl) ⟨842063, by rfl⟩ : syracuseStep 1122751 = 1684127) B1684127
theorem B3387527 : Blo 393766 3387527 := bstep (se 1 (by rfl) ⟨2540645, by rfl⟩ : syracuseStep 3387527 = 5081291) B5081291
theorem B668783 : Blo 393766 668783 := bstep (se 1 (by rfl) ⟨501587, by rfl⟩ : syracuseStep 668783 = 1003175) B1003175
theorem B28425107 : Blo 393766 28425107 := bstep (se 1 (by rfl) ⟨21318830, by rfl⟩ : syracuseStep 28425107 = 42637661) B42637661
theorem B35208431 : Blo 393766 35208431 := bstep (se 1 (by rfl) ⟨26406323, by rfl⟩ : syracuseStep 35208431 = 52812647) B52812647
theorem B5062175 : Blo 393766 5062175 := bstep (se 1 (by rfl) ⟨3796631, by rfl⟩ : syracuseStep 5062175 = 7593263) B7593263
theorem B999337 : Blo 393766 999337 := bstep (se 2 (by rfl) ⟨374751, by rfl⟩ : syracuseStep 999337 = 749503) B749503
theorem B5881835 : Blo 393766 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B3391901 : Blo 393766 3391901 := bstep (se 3 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 3391901 = 1271963) B1271963
theorem B445135 : Blo 393766 445135 := bstep (se 1 (by rfl) ⟨333851, by rfl⟩ : syracuseStep 445135 = 667703) B667703
theorem B674975 : Blo 393766 674975 := bstep (se 1 (by rfl) ⟨506231, by rfl⟩ : syracuseStep 674975 = 1012463) B1012463
theorem B2248829 : Blo 393766 2248829 := bstep (se 3 (by rfl) ⟨421655, by rfl⟩ : syracuseStep 2248829 = 843311) B843311
theorem B26042431 : Blo 393766 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B8120047 : Blo 393766 8120047 := bstep (se 1 (by rfl) ⟨6090035, by rfl⟩ : syracuseStep 8120047 = 12180071) B12180071
theorem B814319 : Blo 393766 814319 := bstep (se 1 (by rfl) ⟨610739, by rfl⟩ : syracuseStep 814319 = 1221479) B1221479
theorem B3370409 : Blo 393766 3370409 := bstep (se 2 (by rfl) ⟨1263903, by rfl⟩ : syracuseStep 3370409 = 2527807) B2527807
theorem B2261267 : Blo 393766 2261267 := bstep (se 1 (by rfl) ⟨1695950, by rfl⟩ : syracuseStep 2261267 = 3391901) B3391901
theorem B592667 : Blo 393766 592667 := bstep (se 1 (by rfl) ⟨444500, by rfl⟩ : syracuseStep 592667 = 889001) B889001
theorem B396287 : Blo 393766 396287 := bstep (se 1 (by rfl) ⟨297215, by rfl⟩ : syracuseStep 396287 = 594431) B594431
theorem B396391 : Blo 393766 396391 := bstep (se 1 (by rfl) ⟨297293, by rfl⟩ : syracuseStep 396391 = 594587) B594587
theorem B593513 : Blo 393766 593513 := bstep (se 2 (by rfl) ⟨222567, by rfl⟩ : syracuseStep 593513 = 445135) B445135
theorem B397083 : Blo 393766 397083 := bstep (se 1 (by rfl) ⟨297812, by rfl⟩ : syracuseStep 397083 = 595625) B595625
theorem B397159 : Blo 393766 397159 := bstep (se 1 (by rfl) ⟨297869, by rfl⟩ : syracuseStep 397159 = 595739) B595739
theorem B595175 : Blo 393766 595175 := bstep (se 1 (by rfl) ⟨446381, by rfl⟩ : syracuseStep 595175 = 892763) B892763
theorem B18950071 : Blo 393766 18950071 := bstep (se 1 (by rfl) ⟨14212553, by rfl⟩ : syracuseStep 18950071 = 28425107) B28425107
theorem B23472287 : Blo 393766 23472287 := bstep (se 1 (by rfl) ⟨17604215, by rfl⟩ : syracuseStep 23472287 = 35208431) B35208431
theorem B10826729 : Blo 393766 10826729 := bstep (se 2 (by rfl) ⟨4060023, by rfl⟩ : syracuseStep 10826729 = 8120047) B8120047
theorem B542879 : Blo 393766 542879 := bstep (se 1 (by rfl) ⟨407159, by rfl⟩ : syracuseStep 542879 = 814319) B814319
theorem B2246939 : Blo 393766 2246939 := bstep (se 1 (by rfl) ⟨1685204, by rfl⟩ : syracuseStep 2246939 = 3370409) B3370409
theorem B445855 : Blo 393766 445855 := bstep (se 1 (by rfl) ⟨334391, by rfl⟩ : syracuseStep 445855 = 668783) B668783
theorem B1332449 : Blo 393766 1332449 := bstep (se 2 (by rfl) ⟨499668, by rfl⟩ : syracuseStep 1332449 = 999337) B999337
theorem B3921223 : Blo 393766 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B34723241 : Blo 393766 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B1497001 : Blo 393766 1497001 := bstep (se 2 (by rfl) ⟨561375, by rfl⟩ : syracuseStep 1497001 = 1122751) B1122751
theorem B449983 : Blo 393766 449983 := bstep (se 1 (by rfl) ⟨337487, by rfl⟩ : syracuseStep 449983 = 674975) B674975
theorem B2252519 : Blo 393766 2252519 := bstep (se 1 (by rfl) ⟨1689389, by rfl⟩ : syracuseStep 2252519 = 3378779) B3378779
theorem B1499219 : Blo 393766 1499219 := bstep (se 1 (by rfl) ⟨1124414, by rfl⟩ : syracuseStep 1499219 = 2248829) B2248829
theorem B2258351 : Blo 393766 2258351 := bstep (se 1 (by rfl) ⟨1693763, by rfl⟩ : syracuseStep 2258351 = 3387527) B3387527
theorem B3374783 : Blo 393766 3374783 := bstep (se 1 (by rfl) ⟨2531087, by rfl⟩ : syracuseStep 3374783 = 5062175) B5062175
theorem B1507511 : Blo 393766 1507511 := bstep (se 1 (by rfl) ⟨1130633, by rfl⟩ : syracuseStep 1507511 = 2261267) B2261267
theorem B395111 : Blo 393766 395111 := bstep (se 1 (by rfl) ⟨296333, by rfl⟩ : syracuseStep 395111 = 592667) B592667
theorem B395675 : Blo 393766 395675 := bstep (se 1 (by rfl) ⟨296756, by rfl⟩ : syracuseStep 395675 = 593513) B593513
theorem B25266761 : Blo 393766 25266761 := bstep (se 2 (by rfl) ⟨9475035, by rfl⟩ : syracuseStep 25266761 = 18950071) B18950071
theorem B888299 : Blo 393766 888299 := bstep (se 1 (by rfl) ⟨666224, by rfl⟩ : syracuseStep 888299 = 1332449) B1332449
theorem B396783 : Blo 393766 396783 := bstep (se 1 (by rfl) ⟨297587, by rfl⟩ : syracuseStep 396783 = 595175) B595175
theorem B594473 : Blo 393766 594473 := bstep (se 2 (by rfl) ⟨222927, by rfl⟩ : syracuseStep 594473 = 445855) B445855
theorem B7217819 : Blo 393766 7217819 := bstep (se 1 (by rfl) ⟨5413364, by rfl⟩ : syracuseStep 7217819 = 10826729) B10826729
theorem B599977 : Blo 393766 599977 := bstep (se 2 (by rfl) ⟨224991, by rfl⟩ : syracuseStep 599977 = 449983) B449983
theorem B23148827 : Blo 393766 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B999479 : Blo 393766 999479 := bstep (se 1 (by rfl) ⟨749609, by rfl⟩ : syracuseStep 999479 = 1499219) B1499219
theorem B15648191 : Blo 393766 15648191 := bstep (se 1 (by rfl) ⟨11736143, by rfl⟩ : syracuseStep 15648191 = 23472287) B23472287
theorem B5228297 : Blo 393766 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B2249855 : Blo 393766 2249855 := bstep (se 1 (by rfl) ⟨1687391, by rfl⟩ : syracuseStep 2249855 = 3374783) B3374783
theorem B1497959 : Blo 393766 1497959 := bstep (se 1 (by rfl) ⟨1123469, by rfl⟩ : syracuseStep 1497959 = 2246939) B2246939
theorem B5790709 : Blo 393766 5790709 := bstep (se 5 (by rfl) ⟨271439, by rfl⟩ : syracuseStep 5790709 = 542879) B542879
theorem B1501679 : Blo 393766 1501679 := bstep (se 1 (by rfl) ⟨1126259, by rfl⟩ : syracuseStep 1501679 = 2252519) B2252519
theorem B1996001 : Blo 393766 1996001 := bstep (se 2 (by rfl) ⟨748500, by rfl⟩ : syracuseStep 1996001 = 1497001) B1497001
theorem B1505567 : Blo 393766 1505567 := bstep (se 1 (by rfl) ⟨1129175, by rfl⟩ : syracuseStep 1505567 = 2258351) B2258351
theorem B16844507 : Blo 393766 16844507 := bstep (se 1 (by rfl) ⟨12633380, by rfl⟩ : syracuseStep 16844507 = 25266761) B25266761
theorem B592199 : Blo 393766 592199 := bstep (se 1 (by rfl) ⟨444149, by rfl⟩ : syracuseStep 592199 = 888299) B888299
theorem B396315 : Blo 393766 396315 := bstep (se 1 (by rfl) ⟨297236, by rfl⟩ : syracuseStep 396315 = 594473) B594473
theorem B666319 : Blo 393766 666319 := bstep (se 1 (by rfl) ⟨499739, by rfl⟩ : syracuseStep 666319 = 999479) B999479
theorem B10432127 : Blo 393766 10432127 := bstep (se 1 (by rfl) ⟨7824095, by rfl⟩ : syracuseStep 10432127 = 15648191) B15648191
theorem B3485531 : Blo 393766 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B799969 : Blo 393766 799969 := bstep (se 2 (by rfl) ⟨299988, by rfl⟩ : syracuseStep 799969 = 599977) B599977
theorem B998639 : Blo 393766 998639 := bstep (se 1 (by rfl) ⟨748979, by rfl⟩ : syracuseStep 998639 = 1497959) B1497959
theorem B30883781 : Blo 393766 30883781 := bstep (se 4 (by rfl) ⟨2895354, by rfl⟩ : syracuseStep 30883781 = 5790709) B5790709
theorem B1001119 : Blo 393766 1001119 := bstep (se 1 (by rfl) ⟨750839, by rfl⟩ : syracuseStep 1001119 = 1501679) B1501679
theorem B1330667 : Blo 393766 1330667 := bstep (se 1 (by rfl) ⟨998000, by rfl⟩ : syracuseStep 1330667 = 1996001) B1996001
theorem B1003711 : Blo 393766 1003711 := bstep (se 1 (by rfl) ⟨752783, by rfl⟩ : syracuseStep 1003711 = 1505567) B1505567
theorem B1005007 : Blo 393766 1005007 := bstep (se 1 (by rfl) ⟨753755, by rfl⟩ : syracuseStep 1005007 = 1507511) B1507511
theorem B1499903 : Blo 393766 1499903 := bstep (se 1 (by rfl) ⟨1124927, by rfl⟩ : syracuseStep 1499903 = 2249855) B2249855
theorem B4811879 : Blo 393766 4811879 := bstep (se 1 (by rfl) ⟨3608909, by rfl⟩ : syracuseStep 4811879 = 7217819) B7217819
theorem B15432551 : Blo 393766 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B394799 : Blo 393766 394799 := bstep (se 1 (by rfl) ⟨296099, by rfl⟩ : syracuseStep 394799 = 592199) B592199
theorem B887111 : Blo 393766 887111 := bstep (se 1 (by rfl) ⟨665333, by rfl⟩ : syracuseStep 887111 = 1330667) B1330667
theorem B888425 : Blo 393766 888425 := bstep (se 2 (by rfl) ⟨333159, by rfl⟩ : syracuseStep 888425 = 666319) B666319
theorem B6954751 : Blo 393766 6954751 := bstep (se 1 (by rfl) ⟨5216063, by rfl⟩ : syracuseStep 6954751 = 10432127) B10432127
theorem B665759 : Blo 393766 665759 := bstep (se 1 (by rfl) ⟨499319, by rfl⟩ : syracuseStep 665759 = 998639) B998639
theorem B82356749 : Blo 393766 82356749 := bstep (se 3 (by rfl) ⟨15441890, by rfl⟩ : syracuseStep 82356749 = 30883781) B30883781
theorem B999935 : Blo 393766 999935 := bstep (se 1 (by rfl) ⟨749951, by rfl⟩ : syracuseStep 999935 = 1499903) B1499903
theorem B1066625 : Blo 393766 1066625 := bstep (se 2 (by rfl) ⟨399984, by rfl⟩ : syracuseStep 1066625 = 799969) B799969
theorem B9294749 : Blo 393766 9294749 := bstep (se 3 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 9294749 = 3485531) B3485531
theorem B11229671 : Blo 393766 11229671 := bstep (se 1 (by rfl) ⟨8422253, by rfl⟩ : syracuseStep 11229671 = 16844507) B16844507
theorem B1334825 : Blo 393766 1334825 := bstep (se 2 (by rfl) ⟨500559, by rfl⟩ : syracuseStep 1334825 = 1001119) B1001119
theorem B1338281 : Blo 393766 1338281 := bstep (se 2 (by rfl) ⟨501855, by rfl⟩ : syracuseStep 1338281 = 1003711) B1003711
theorem B1340009 : Blo 393766 1340009 := bstep (se 2 (by rfl) ⟨502503, by rfl⟩ : syracuseStep 1340009 = 1005007) B1005007
theorem B3207919 : Blo 393766 3207919 := bstep (se 1 (by rfl) ⟨2405939, by rfl⟩ : syracuseStep 3207919 = 4811879) B4811879
theorem B10288367 : Blo 393766 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B591407 : Blo 393766 591407 := bstep (se 1 (by rfl) ⟨443555, by rfl⟩ : syracuseStep 591407 = 887111) B887111
theorem B592283 : Blo 393766 592283 := bstep (se 1 (by rfl) ⟨444212, by rfl⟩ : syracuseStep 592283 = 888425) B888425
theorem B6196499 : Blo 393766 6196499 := bstep (se 1 (by rfl) ⟨4647374, by rfl⟩ : syracuseStep 6196499 = 9294749) B9294749
theorem B889883 : Blo 393766 889883 := bstep (se 1 (by rfl) ⟨667412, by rfl⟩ : syracuseStep 889883 = 1334825) B1334825
theorem B892187 : Blo 393766 892187 := bstep (se 1 (by rfl) ⟨669140, by rfl⟩ : syracuseStep 892187 = 1338281) B1338281
theorem B893339 : Blo 393766 893339 := bstep (se 1 (by rfl) ⟨670004, by rfl⟩ : syracuseStep 893339 = 1340009) B1340009
theorem B6858911 : Blo 393766 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B666623 : Blo 393766 666623 := bstep (se 1 (by rfl) ⟨499967, by rfl⟩ : syracuseStep 666623 = 999935) B999935
theorem B7486447 : Blo 393766 7486447 := bstep (se 1 (by rfl) ⟨5614835, by rfl⟩ : syracuseStep 7486447 = 11229671) B11229671
theorem B4277225 : Blo 393766 4277225 := bstep (se 2 (by rfl) ⟨1603959, by rfl⟩ : syracuseStep 4277225 = 3207919) B3207919
theorem B443839 : Blo 393766 443839 := bstep (se 1 (by rfl) ⟨332879, by rfl⟩ : syracuseStep 443839 = 665759) B665759
theorem B54904499 : Blo 393766 54904499 := bstep (se 1 (by rfl) ⟨41178374, by rfl⟩ : syracuseStep 54904499 = 82356749) B82356749
theorem B711083 : Blo 393766 711083 := bstep (se 1 (by rfl) ⟨533312, by rfl⟩ : syracuseStep 711083 = 1066625) B1066625
theorem B9273001 : Blo 393766 9273001 := bstep (se 2 (by rfl) ⟨3477375, by rfl⟩ : syracuseStep 9273001 = 6954751) B6954751
theorem B2851483 : Blo 393766 2851483 := bstep (se 1 (by rfl) ⟨2138612, by rfl⟩ : syracuseStep 2851483 = 4277225) B4277225
theorem B394271 : Blo 393766 394271 := bstep (se 1 (by rfl) ⟨295703, by rfl⟩ : syracuseStep 394271 = 591407) B591407
theorem B36602999 : Blo 393766 36602999 := bstep (se 1 (by rfl) ⟨27452249, by rfl⟩ : syracuseStep 36602999 = 54904499) B54904499
theorem B394855 : Blo 393766 394855 := bstep (se 1 (by rfl) ⟨296141, by rfl⟩ : syracuseStep 394855 = 592283) B592283
theorem B591785 : Blo 393766 591785 := bstep (se 2 (by rfl) ⟨221919, by rfl⟩ : syracuseStep 591785 = 443839) B443839
theorem B4130999 : Blo 393766 4130999 := bstep (se 1 (by rfl) ⟨3098249, by rfl⟩ : syracuseStep 4130999 = 6196499) B6196499
theorem B593255 : Blo 393766 593255 := bstep (se 1 (by rfl) ⟨444941, by rfl⟩ : syracuseStep 593255 = 889883) B889883
theorem B594791 : Blo 393766 594791 := bstep (se 1 (by rfl) ⟨446093, by rfl⟩ : syracuseStep 594791 = 892187) B892187
theorem B595559 : Blo 393766 595559 := bstep (se 1 (by rfl) ⟨446669, by rfl⟩ : syracuseStep 595559 = 893339) B893339
theorem B12364001 : Blo 393766 12364001 := bstep (se 2 (by rfl) ⟨4636500, by rfl⟩ : syracuseStep 12364001 = 9273001) B9273001
theorem B474055 : Blo 393766 474055 := bstep (se 1 (by rfl) ⟨355541, by rfl⟩ : syracuseStep 474055 = 711083) B711083
theorem B4572607 : Blo 393766 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B444415 : Blo 393766 444415 := bstep (se 1 (by rfl) ⟨333311, by rfl⟩ : syracuseStep 444415 = 666623) B666623
theorem B9981929 : Blo 393766 9981929 := bstep (se 2 (by rfl) ⟨3743223, by rfl⟩ : syracuseStep 9981929 = 7486447) B7486447
theorem B3801977 : Blo 393766 3801977 := bstep (se 2 (by rfl) ⟨1425741, by rfl⟩ : syracuseStep 3801977 = 2851483) B2851483
theorem B394523 : Blo 393766 394523 := bstep (se 1 (by rfl) ⟨295892, by rfl⟩ : syracuseStep 394523 = 591785) B591785
theorem B2753999 : Blo 393766 2753999 := bstep (se 1 (by rfl) ⟨2065499, by rfl⟩ : syracuseStep 2753999 = 4130999) B4130999
theorem B6096809 : Blo 393766 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B395503 : Blo 393766 395503 := bstep (se 1 (by rfl) ⟨296627, by rfl⟩ : syracuseStep 395503 = 593255) B593255
theorem B6654619 : Blo 393766 6654619 := bstep (se 1 (by rfl) ⟨4990964, by rfl⟩ : syracuseStep 6654619 = 9981929) B9981929
theorem B592553 : Blo 393766 592553 := bstep (se 2 (by rfl) ⟨222207, by rfl⟩ : syracuseStep 592553 = 444415) B444415
theorem B396527 : Blo 393766 396527 := bstep (se 1 (by rfl) ⟨297395, by rfl⟩ : syracuseStep 396527 = 594791) B594791
theorem B397039 : Blo 393766 397039 := bstep (se 1 (by rfl) ⟨297779, by rfl⟩ : syracuseStep 397039 = 595559) B595559
theorem B2528293 : Blo 393766 2528293 := bstep (se 4 (by rfl) ⟨237027, by rfl⟩ : syracuseStep 2528293 = 474055) B474055
theorem B8242667 : Blo 393766 8242667 := bstep (se 1 (by rfl) ⟨6182000, by rfl⟩ : syracuseStep 8242667 = 12364001) B12364001
theorem B24401999 : Blo 393766 24401999 := bstep (se 1 (by rfl) ⟨18301499, by rfl⟩ : syracuseStep 24401999 = 36602999) B36602999
theorem B1835999 : Blo 393766 1835999 := bstep (se 1 (by rfl) ⟨1376999, by rfl⟩ : syracuseStep 1835999 = 2753999) B2753999
theorem B4064539 : Blo 393766 4064539 := bstep (se 1 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 4064539 = 6096809) B6096809
theorem B395035 : Blo 393766 395035 := bstep (se 1 (by rfl) ⟨296276, by rfl⟩ : syracuseStep 395035 = 592553) B592553
theorem B35491301 : Blo 393766 35491301 := bstep (se 4 (by rfl) ⟨3327309, by rfl⟩ : syracuseStep 35491301 = 6654619) B6654619
theorem B2534651 : Blo 393766 2534651 := bstep (se 1 (by rfl) ⟨1900988, by rfl⟩ : syracuseStep 2534651 = 3801977) B3801977
theorem B16267999 : Blo 393766 16267999 := bstep (se 1 (by rfl) ⟨12200999, by rfl⟩ : syracuseStep 16267999 = 24401999) B24401999
theorem B5495111 : Blo 393766 5495111 := bstep (se 1 (by rfl) ⟨4121333, by rfl⟩ : syracuseStep 5495111 = 8242667) B8242667
theorem B3371057 : Blo 393766 3371057 := bstep (se 2 (by rfl) ⟨1264146, by rfl⟩ : syracuseStep 3371057 = 2528293) B2528293
theorem B23660867 : Blo 393766 23660867 := bstep (se 1 (by rfl) ⟨17745650, by rfl⟩ : syracuseStep 23660867 = 35491301) B35491301
theorem B1223999 : Blo 393766 1223999 := bstep (se 1 (by rfl) ⟨917999, by rfl⟩ : syracuseStep 1223999 = 1835999) B1835999
theorem B5419385 : Blo 393766 5419385 := bstep (se 2 (by rfl) ⟨2032269, by rfl⟩ : syracuseStep 5419385 = 4064539) B4064539
theorem B1689767 : Blo 393766 1689767 := bstep (se 1 (by rfl) ⟨1267325, by rfl⟩ : syracuseStep 1689767 = 2534651) B2534651
theorem B2247371 : Blo 393766 2247371 := bstep (se 1 (by rfl) ⟨1685528, by rfl⟩ : syracuseStep 2247371 = 3371057) B3371057
theorem B3663407 : Blo 393766 3663407 := bstep (se 1 (by rfl) ⟨2747555, by rfl⟩ : syracuseStep 3663407 = 5495111) B5495111
theorem B21690665 : Blo 393766 21690665 := bstep (se 2 (by rfl) ⟨8133999, by rfl⟩ : syracuseStep 21690665 = 16267999) B16267999
theorem B3612923 : Blo 393766 3612923 := bstep (se 1 (by rfl) ⟨2709692, by rfl⟩ : syracuseStep 3612923 = 5419385) B5419385
theorem B14460443 : Blo 393766 14460443 := bstep (se 1 (by rfl) ⟨10845332, by rfl⟩ : syracuseStep 14460443 = 21690665) B21690665
theorem B1126511 : Blo 393766 1126511 := bstep (se 1 (by rfl) ⟨844883, by rfl⟩ : syracuseStep 1126511 = 1689767) B1689767
theorem B63095645 : Blo 393766 63095645 := bstep (se 3 (by rfl) ⟨11830433, by rfl⟩ : syracuseStep 63095645 = 23660867) B23660867
theorem B2442271 : Blo 393766 2442271 := bstep (se 1 (by rfl) ⟨1831703, by rfl⟩ : syracuseStep 2442271 = 3663407) B3663407
theorem B1498247 : Blo 393766 1498247 := bstep (se 1 (by rfl) ⟨1123685, by rfl⟩ : syracuseStep 1498247 = 2247371) B2247371
theorem B815999 : Blo 393766 815999 := bstep (se 1 (by rfl) ⟨611999, by rfl⟩ : syracuseStep 815999 = 1223999) B1223999
theorem B9640295 : Blo 393766 9640295 := bstep (se 1 (by rfl) ⟨7230221, by rfl⟩ : syracuseStep 9640295 = 14460443) B14460443
theorem B3256361 : Blo 393766 3256361 := bstep (se 2 (by rfl) ⟨1221135, by rfl⟩ : syracuseStep 3256361 = 2442271) B2442271
theorem B2175997 : Blo 393766 2175997 := bstep (se 3 (by rfl) ⟨407999, by rfl⟩ : syracuseStep 2175997 = 815999) B815999
theorem B998831 : Blo 393766 998831 := bstep (se 1 (by rfl) ⟨749123, by rfl⟩ : syracuseStep 998831 = 1498247) B1498247
theorem B2408615 : Blo 393766 2408615 := bstep (se 1 (by rfl) ⟨1806461, by rfl⟩ : syracuseStep 2408615 = 3612923) B3612923
theorem B168255053 : Blo 393766 168255053 := bstep (se 3 (by rfl) ⟨31547822, by rfl⟩ : syracuseStep 168255053 = 63095645) B63095645
theorem B751007 : Blo 393766 751007 := bstep (se 1 (by rfl) ⟨563255, by rfl⟩ : syracuseStep 751007 = 1126511) B1126511
theorem B1605743 : Blo 393766 1605743 := bstep (se 1 (by rfl) ⟨1204307, by rfl⟩ : syracuseStep 1605743 = 2408615) B2408615
theorem B6426863 : Blo 393766 6426863 := bstep (se 1 (by rfl) ⟨4820147, by rfl⟩ : syracuseStep 6426863 = 9640295) B9640295
theorem B112170035 : Blo 393766 112170035 := bstep (se 1 (by rfl) ⟨84127526, by rfl⟩ : syracuseStep 112170035 = 168255053) B168255053
theorem B2170907 : Blo 393766 2170907 := bstep (se 1 (by rfl) ⟨1628180, by rfl⟩ : syracuseStep 2170907 = 3256361) B3256361
theorem B500671 : Blo 393766 500671 := bstep (se 1 (by rfl) ⟨375503, by rfl⟩ : syracuseStep 500671 = 751007) B751007
theorem B665887 : Blo 393766 665887 := bstep (se 1 (by rfl) ⟨499415, by rfl⟩ : syracuseStep 665887 = 998831) B998831
theorem B2901329 : Blo 393766 2901329 := bstep (se 2 (by rfl) ⟨1087998, by rfl⟩ : syracuseStep 2901329 = 2175997) B2175997
theorem B1934219 : Blo 393766 1934219 := bstep (se 1 (by rfl) ⟨1450664, by rfl⟩ : syracuseStep 1934219 = 2901329) B2901329
theorem B887849 : Blo 393766 887849 := bstep (se 2 (by rfl) ⟨332943, by rfl⟩ : syracuseStep 887849 = 665887) B665887
theorem B74780023 : Blo 393766 74780023 := bstep (se 1 (by rfl) ⟨56085017, by rfl⟩ : syracuseStep 74780023 = 112170035) B112170035
theorem B1447271 : Blo 393766 1447271 := bstep (se 1 (by rfl) ⟨1085453, by rfl⟩ : syracuseStep 1447271 = 2170907) B2170907
theorem B667561 : Blo 393766 667561 := bstep (se 2 (by rfl) ⟨250335, by rfl⟩ : syracuseStep 667561 = 500671) B500671
theorem B1070495 : Blo 393766 1070495 := bstep (se 1 (by rfl) ⟨802871, by rfl⟩ : syracuseStep 1070495 = 1605743) B1605743
theorem B4284575 : Blo 393766 4284575 := bstep (se 1 (by rfl) ⟨3213431, by rfl⟩ : syracuseStep 4284575 = 6426863) B6426863
theorem B591899 : Blo 393766 591899 := bstep (se 1 (by rfl) ⟨443924, by rfl⟩ : syracuseStep 591899 = 887849) B887849
theorem B890081 : Blo 393766 890081 := bstep (se 2 (by rfl) ⟨333780, by rfl⟩ : syracuseStep 890081 = 667561) B667561
theorem B2856383 : Blo 393766 2856383 := bstep (se 1 (by rfl) ⟨2142287, by rfl⟩ : syracuseStep 2856383 = 4284575) B4284575
theorem B1289479 : Blo 393766 1289479 := bstep (se 1 (by rfl) ⟨967109, by rfl⟩ : syracuseStep 1289479 = 1934219) B1934219
theorem B964847 : Blo 393766 964847 := bstep (se 1 (by rfl) ⟨723635, by rfl⟩ : syracuseStep 964847 = 1447271) B1447271
theorem B713663 : Blo 393766 713663 := bstep (se 1 (by rfl) ⟨535247, by rfl⟩ : syracuseStep 713663 = 1070495) B1070495
theorem B99706697 : Blo 393766 99706697 := bstep (se 2 (by rfl) ⟨37390011, by rfl⟩ : syracuseStep 99706697 = 74780023) B74780023
theorem B394599 : Blo 393766 394599 := bstep (se 1 (by rfl) ⟨295949, by rfl⟩ : syracuseStep 394599 = 591899) B591899
theorem B593387 : Blo 393766 593387 := bstep (se 1 (by rfl) ⟨445040, by rfl⟩ : syracuseStep 593387 = 890081) B890081
theorem B1904255 : Blo 393766 1904255 := bstep (se 1 (by rfl) ⟨1428191, by rfl⟩ : syracuseStep 1904255 = 2856383) B2856383
theorem B1719305 : Blo 393766 1719305 := bstep (se 2 (by rfl) ⟨644739, by rfl⟩ : syracuseStep 1719305 = 1289479) B1289479
theorem B475775 : Blo 393766 475775 := bstep (se 1 (by rfl) ⟨356831, by rfl⟩ : syracuseStep 475775 = 713663) B713663
theorem B66471131 : Blo 393766 66471131 := bstep (se 1 (by rfl) ⟨49853348, by rfl⟩ : syracuseStep 66471131 = 99706697) B99706697
theorem B643231 : Blo 393766 643231 := bstep (se 1 (by rfl) ⟨482423, by rfl⟩ : syracuseStep 643231 = 964847) B964847
theorem B395591 : Blo 393766 395591 := bstep (se 1 (by rfl) ⟨296693, by rfl⟩ : syracuseStep 395591 = 593387) B593387
theorem B857641 : Blo 393766 857641 := bstep (se 2 (by rfl) ⟨321615, by rfl⟩ : syracuseStep 857641 = 643231) B643231
theorem B44314087 : Blo 393766 44314087 := bstep (se 1 (by rfl) ⟨33235565, by rfl⟩ : syracuseStep 44314087 = 66471131) B66471131
theorem B1269503 : Blo 393766 1269503 := bstep (se 1 (by rfl) ⟨952127, by rfl⟩ : syracuseStep 1269503 = 1904255) B1904255
theorem B5074933 : Blo 393766 5074933 := bstep (se 5 (by rfl) ⟨237887, by rfl⟩ : syracuseStep 5074933 = 475775) B475775
theorem B1146203 : Blo 393766 1146203 := bstep (se 1 (by rfl) ⟨859652, by rfl⟩ : syracuseStep 1146203 = 1719305) B1719305
theorem B59085449 : Blo 393766 59085449 := bstep (se 2 (by rfl) ⟨22157043, by rfl⟩ : syracuseStep 59085449 = 44314087) B44314087
theorem B764135 : Blo 393766 764135 := bstep (se 1 (by rfl) ⟨573101, by rfl⟩ : syracuseStep 764135 = 1146203) B1146203
theorem B6766577 : Blo 393766 6766577 := bstep (se 2 (by rfl) ⟨2537466, by rfl⟩ : syracuseStep 6766577 = 5074933) B5074933
theorem B846335 : Blo 393766 846335 := bstep (se 1 (by rfl) ⟨634751, by rfl⟩ : syracuseStep 846335 = 1269503) B1269503
theorem B1143521 : Blo 393766 1143521 := bstep (se 2 (by rfl) ⟨428820, by rfl⟩ : syracuseStep 1143521 = 857641) B857641
theorem B39390299 : Blo 393766 39390299 := bstep (se 1 (by rfl) ⟨29542724, by rfl⟩ : syracuseStep 39390299 = 59085449) B59085449
theorem B762347 : Blo 393766 762347 := bstep (se 1 (by rfl) ⟨571760, by rfl⟩ : syracuseStep 762347 = 1143521) B1143521
theorem B509423 : Blo 393766 509423 := bstep (se 1 (by rfl) ⟨382067, by rfl⟩ : syracuseStep 509423 = 764135) B764135
theorem B4511051 : Blo 393766 4511051 := bstep (se 1 (by rfl) ⟨3383288, by rfl⟩ : syracuseStep 4511051 = 6766577) B6766577
theorem B2256893 : Blo 393766 2256893 := bstep (se 3 (by rfl) ⟨423167, by rfl⟩ : syracuseStep 2256893 = 846335) B846335
theorem B26260199 : Blo 393766 26260199 := bstep (se 1 (by rfl) ⟨19695149, by rfl⟩ : syracuseStep 26260199 = 39390299) B39390299
theorem B1358461 : Blo 393766 1358461 := bstep (se 3 (by rfl) ⟨254711, by rfl⟩ : syracuseStep 1358461 = 509423) B509423
theorem B508231 : Blo 393766 508231 := bstep (se 1 (by rfl) ⟨381173, by rfl⟩ : syracuseStep 508231 = 762347) B762347
theorem B3007367 : Blo 393766 3007367 := bstep (se 1 (by rfl) ⟨2255525, by rfl⟩ : syracuseStep 3007367 = 4511051) B4511051
theorem B1504595 : Blo 393766 1504595 := bstep (se 1 (by rfl) ⟨1128446, by rfl⟩ : syracuseStep 1504595 = 2256893) B2256893
theorem B2004911 : Blo 393766 2004911 := bstep (se 1 (by rfl) ⟨1503683, by rfl⟩ : syracuseStep 2004911 = 3007367) B3007367
theorem B17506799 : Blo 393766 17506799 := bstep (se 1 (by rfl) ⟨13130099, by rfl⟩ : syracuseStep 17506799 = 26260199) B26260199
theorem B1811281 : Blo 393766 1811281 := bstep (se 2 (by rfl) ⟨679230, by rfl⟩ : syracuseStep 1811281 = 1358461) B1358461
theorem B1003063 : Blo 393766 1003063 := bstep (se 1 (by rfl) ⟨752297, by rfl⟩ : syracuseStep 1003063 = 1504595) B1504595
theorem B2710565 : Blo 393766 2710565 := bstep (se 4 (by rfl) ⟨254115, by rfl⟩ : syracuseStep 2710565 = 508231) B508231
theorem B1807043 : Blo 393766 1807043 := bstep (se 1 (by rfl) ⟨1355282, by rfl⟩ : syracuseStep 1807043 = 2710565) B2710565
theorem B11671199 : Blo 393766 11671199 := bstep (se 1 (by rfl) ⟨8753399, by rfl⟩ : syracuseStep 11671199 = 17506799) B17506799
theorem B2415041 : Blo 393766 2415041 := bstep (se 2 (by rfl) ⟨905640, by rfl⟩ : syracuseStep 2415041 = 1811281) B1811281
theorem B1336607 : Blo 393766 1336607 := bstep (se 1 (by rfl) ⟨1002455, by rfl⟩ : syracuseStep 1336607 = 2004911) B2004911
theorem B1337417 : Blo 393766 1337417 := bstep (se 2 (by rfl) ⟨501531, by rfl⟩ : syracuseStep 1337417 = 1003063) B1003063
theorem B4818781 : Blo 393766 4818781 := bstep (se 3 (by rfl) ⟨903521, by rfl⟩ : syracuseStep 4818781 = 1807043) B1807043
theorem B1610027 : Blo 393766 1610027 := bstep (se 1 (by rfl) ⟨1207520, by rfl⟩ : syracuseStep 1610027 = 2415041) B2415041
theorem B891071 : Blo 393766 891071 := bstep (se 1 (by rfl) ⟨668303, by rfl⟩ : syracuseStep 891071 = 1336607) B1336607
theorem B891611 : Blo 393766 891611 := bstep (se 1 (by rfl) ⟨668708, by rfl⟩ : syracuseStep 891611 = 1337417) B1337417
theorem B7780799 : Blo 393766 7780799 := bstep (se 1 (by rfl) ⟨5835599, by rfl⟩ : syracuseStep 7780799 = 11671199) B11671199
theorem B6425041 : Blo 393766 6425041 := bstep (se 2 (by rfl) ⟨2409390, by rfl⟩ : syracuseStep 6425041 = 4818781) B4818781
theorem B594047 : Blo 393766 594047 := bstep (se 1 (by rfl) ⟨445535, by rfl⟩ : syracuseStep 594047 = 891071) B891071
theorem B594407 : Blo 393766 594407 := bstep (se 1 (by rfl) ⟨445805, by rfl⟩ : syracuseStep 594407 = 891611) B891611
theorem B5187199 : Blo 393766 5187199 := bstep (se 1 (by rfl) ⟨3890399, by rfl⟩ : syracuseStep 5187199 = 7780799) B7780799
theorem B1073351 : Blo 393766 1073351 := bstep (se 1 (by rfl) ⟨805013, by rfl⟩ : syracuseStep 1073351 = 1610027) B1610027
theorem B6916265 : Blo 393766 6916265 := bstep (se 2 (by rfl) ⟨2593599, by rfl⟩ : syracuseStep 6916265 = 5187199) B5187199
theorem B396031 : Blo 393766 396031 := bstep (se 1 (by rfl) ⟨297023, by rfl⟩ : syracuseStep 396031 = 594047) B594047
theorem B396271 : Blo 393766 396271 := bstep (se 1 (by rfl) ⟨297203, by rfl⟩ : syracuseStep 396271 = 594407) B594407
theorem B8566721 : Blo 393766 8566721 := bstep (se 2 (by rfl) ⟨3212520, by rfl⟩ : syracuseStep 8566721 = 6425041) B6425041
theorem B715567 : Blo 393766 715567 := bstep (se 1 (by rfl) ⟨536675, by rfl⟩ : syracuseStep 715567 = 1073351) B1073351
theorem B954089 : Blo 393766 954089 := bstep (se 2 (by rfl) ⟨357783, by rfl⟩ : syracuseStep 954089 = 715567) B715567
theorem B5711147 : Blo 393766 5711147 := bstep (se 1 (by rfl) ⟨4283360, by rfl⟩ : syracuseStep 5711147 = 8566721) B8566721
theorem B4610843 : Blo 393766 4610843 := bstep (se 1 (by rfl) ⟨3458132, by rfl⟩ : syracuseStep 4610843 = 6916265) B6916265
theorem B3807431 : Blo 393766 3807431 := bstep (se 1 (by rfl) ⟨2855573, by rfl⟩ : syracuseStep 3807431 = 5711147) B5711147
theorem B636059 : Blo 393766 636059 := bstep (se 1 (by rfl) ⟨477044, by rfl⟩ : syracuseStep 636059 = 954089) B954089
theorem B3073895 : Blo 393766 3073895 := bstep (se 1 (by rfl) ⟨2305421, by rfl⟩ : syracuseStep 3073895 = 4610843) B4610843
theorem B2538287 : Blo 393766 2538287 := bstep (se 1 (by rfl) ⟨1903715, by rfl⟩ : syracuseStep 2538287 = 3807431) B3807431
theorem B2049263 : Blo 393766 2049263 := bstep (se 1 (by rfl) ⟨1536947, by rfl⟩ : syracuseStep 2049263 = 3073895) B3073895
theorem B424039 : Blo 393766 424039 := bstep (se 1 (by rfl) ⟨318029, by rfl⟩ : syracuseStep 424039 = 636059) B636059
theorem B565385 : Blo 393766 565385 := bstep (se 2 (by rfl) ⟨212019, by rfl⟩ : syracuseStep 565385 = 424039) B424039
theorem B1692191 : Blo 393766 1692191 := bstep (se 1 (by rfl) ⟨1269143, by rfl⟩ : syracuseStep 1692191 = 2538287) B2538287
theorem B1366175 : Blo 393766 1366175 := bstep (se 1 (by rfl) ⟨1024631, by rfl⟩ : syracuseStep 1366175 = 2049263) B2049263
theorem B1507693 : Blo 393766 1507693 := bstep (se 3 (by rfl) ⟨282692, by rfl⟩ : syracuseStep 1507693 = 565385) B565385
theorem B4512509 : Blo 393766 4512509 := bstep (se 3 (by rfl) ⟨846095, by rfl⟩ : syracuseStep 4512509 = 1692191) B1692191
theorem B910783 : Blo 393766 910783 := bstep (se 1 (by rfl) ⟨683087, by rfl⟩ : syracuseStep 910783 = 1366175) B1366175
theorem B4857509 : Blo 393766 4857509 := bstep (se 4 (by rfl) ⟨455391, by rfl⟩ : syracuseStep 4857509 = 910783) B910783
theorem B2010257 : Blo 393766 2010257 := bstep (se 2 (by rfl) ⟨753846, by rfl⟩ : syracuseStep 2010257 = 1507693) B1507693
theorem B3008339 : Blo 393766 3008339 := bstep (se 1 (by rfl) ⟨2256254, by rfl⟩ : syracuseStep 3008339 = 4512509) B4512509
theorem B2005559 : Blo 393766 2005559 := bstep (se 1 (by rfl) ⟨1504169, by rfl⟩ : syracuseStep 2005559 = 3008339) B3008339
theorem B3238339 : Blo 393766 3238339 := bstep (se 1 (by rfl) ⟨2428754, by rfl⟩ : syracuseStep 3238339 = 4857509) B4857509
theorem B1340171 : Blo 393766 1340171 := bstep (se 1 (by rfl) ⟨1005128, by rfl⟩ : syracuseStep 1340171 = 2010257) B2010257
theorem B893447 : Blo 393766 893447 := bstep (se 1 (by rfl) ⟨670085, by rfl⟩ : syracuseStep 893447 = 1340171) B1340171
theorem B4317785 : Blo 393766 4317785 := bstep (se 2 (by rfl) ⟨1619169, by rfl⟩ : syracuseStep 4317785 = 3238339) B3238339
theorem B1337039 : Blo 393766 1337039 := bstep (se 1 (by rfl) ⟨1002779, by rfl⟩ : syracuseStep 1337039 = 2005559) B2005559
theorem B595631 : Blo 393766 595631 := bstep (se 1 (by rfl) ⟨446723, by rfl⟩ : syracuseStep 595631 = 893447) B893447
theorem B891359 : Blo 393766 891359 := bstep (se 1 (by rfl) ⟨668519, by rfl⟩ : syracuseStep 891359 = 1337039) B1337039
theorem B2878523 : Blo 393766 2878523 := bstep (se 1 (by rfl) ⟨2158892, by rfl⟩ : syracuseStep 2878523 = 4317785) B4317785
theorem B397087 : Blo 393766 397087 := bstep (se 1 (by rfl) ⟨297815, by rfl⟩ : syracuseStep 397087 = 595631) B595631
theorem B594239 : Blo 393766 594239 := bstep (se 1 (by rfl) ⟨445679, by rfl⟩ : syracuseStep 594239 = 891359) B891359
theorem B1919015 : Blo 393766 1919015 := bstep (se 1 (by rfl) ⟨1439261, by rfl⟩ : syracuseStep 1919015 = 2878523) B2878523
theorem B1279343 : Blo 393766 1279343 := bstep (se 1 (by rfl) ⟨959507, by rfl⟩ : syracuseStep 1279343 = 1919015) B1919015
theorem B396159 : Blo 393766 396159 := bstep (se 1 (by rfl) ⟨297119, by rfl⟩ : syracuseStep 396159 = 594239) B594239
theorem B852895 : Blo 393766 852895 := bstep (se 1 (by rfl) ⟨639671, by rfl⟩ : syracuseStep 852895 = 1279343) B1279343
theorem B4548773 : Blo 393766 4548773 := bstep (se 4 (by rfl) ⟨426447, by rfl⟩ : syracuseStep 4548773 = 852895) B852895
theorem B3032515 : Blo 393766 3032515 := bstep (se 1 (by rfl) ⟨2274386, by rfl⟩ : syracuseStep 3032515 = 4548773) B4548773
theorem B4043353 : Blo 393766 4043353 := bstep (se 2 (by rfl) ⟨1516257, by rfl⟩ : syracuseStep 4043353 = 3032515) B3032515
theorem B5391137 : Blo 393766 5391137 := bstep (se 2 (by rfl) ⟨2021676, by rfl⟩ : syracuseStep 5391137 = 4043353) B4043353
theorem B3594091 : Blo 393766 3594091 := bstep (se 1 (by rfl) ⟨2695568, by rfl⟩ : syracuseStep 3594091 = 5391137) B5391137
theorem B4792121 : Blo 393766 4792121 := bstep (se 2 (by rfl) ⟨1797045, by rfl⟩ : syracuseStep 4792121 = 3594091) B3594091
theorem B3194747 : Blo 393766 3194747 := bstep (se 1 (by rfl) ⟨2396060, by rfl⟩ : syracuseStep 3194747 = 4792121) B4792121
theorem B2129831 : Blo 393766 2129831 := bstep (se 1 (by rfl) ⟨1597373, by rfl⟩ : syracuseStep 2129831 = 3194747) B3194747
theorem B1419887 : Blo 393766 1419887 := bstep (se 1 (by rfl) ⟨1064915, by rfl⟩ : syracuseStep 1419887 = 2129831) B2129831
theorem B3786365 : Blo 393766 3786365 := bstep (se 3 (by rfl) ⟨709943, by rfl⟩ : syracuseStep 3786365 = 1419887) B1419887
theorem B2524243 : Blo 393766 2524243 := bstep (se 1 (by rfl) ⟨1893182, by rfl⟩ : syracuseStep 2524243 = 3786365) B3786365
theorem B3365657 : Blo 393766 3365657 := bstep (se 2 (by rfl) ⟨1262121, by rfl⟩ : syracuseStep 3365657 = 2524243) B2524243
theorem B2243771 : Blo 393766 2243771 := bstep (se 1 (by rfl) ⟨1682828, by rfl⟩ : syracuseStep 2243771 = 3365657) B3365657
theorem B1495847 : Blo 393766 1495847 := bstep (se 1 (by rfl) ⟨1121885, by rfl⟩ : syracuseStep 1495847 = 2243771) B2243771
theorem B997231 : Blo 393766 997231 := bstep (se 1 (by rfl) ⟨747923, by rfl⟩ : syracuseStep 997231 = 1495847) B1495847
theorem B1329641 : Blo 393766 1329641 := bstep (se 2 (by rfl) ⟨498615, by rfl⟩ : syracuseStep 1329641 = 997231) B997231
theorem B886427 : Blo 393766 886427 := bstep (se 1 (by rfl) ⟨664820, by rfl⟩ : syracuseStep 886427 = 1329641) B1329641
theorem B590951 : Blo 393766 590951 := bstep (se 1 (by rfl) ⟨443213, by rfl⟩ : syracuseStep 590951 = 886427) B886427
theorem B393967 : Blo 393766 393967 := bstep (se 1 (by rfl) ⟨295475, by rfl⟩ : syracuseStep 393967 = 590951) B590951

theorem C0 (j : ℕ) (h1 : 98441 ≤ j) (h2 : j ≤ 99140) : Blo 393766 (4 * j + 3) := by
  interval_cases j
  · exact B393767
  · exact B393771
  · exact B393775
  · exact B393779
  · exact B393783
  · exact B393787
  · exact B393791
  · exact B393795
  · exact B393799
  · exact B393803
  · exact B393807
  · exact B393811
  · exact B393815
  · exact B393819
  · exact B393823
  · exact B393827
  · exact B393831
  · exact B393835
  · exact B393839
  · exact B393843
  · exact B393847
  · exact B393851
  · exact B393855
  · exact B393859
  · exact B393863
  · exact B393867
  · exact B393871
  · exact B393875
  · exact B393879
  · exact B393883
  · exact B393887
  · exact B393891
  · exact B393895
  · exact B393899
  · exact B393903
  · exact B393907
  · exact B393911
  · exact B393915
  · exact B393919
  · exact B393923
  · exact B393927
  · exact B393931
  · exact B393935
  · exact B393939
  · exact B393943
  · exact B393947
  · exact B393951
  · exact B393955
  · exact B393959
  · exact B393963
  · exact B393967
  · exact B393971
  · exact B393975
  · exact B393979
  · exact B393983
  · exact B393987
  · exact B393991
  · exact B393995
  · exact B393999
  · exact B394003
  · exact B394007
  · exact B394011
  · exact B394015
  · exact B394019
  · exact B394023
  · exact B394027
  · exact B394031
  · exact B394035
  · exact B394039
  · exact B394043
  · exact B394047
  · exact B394051
  · exact B394055
  · exact B394059
  · exact B394063
  · exact B394067
  · exact B394071
  · exact B394075
  · exact B394079
  · exact B394083
  · exact B394087
  · exact B394091
  · exact B394095
  · exact B394099
  · exact B394103
  · exact B394107
  · exact B394111
  · exact B394115
  · exact B394119
  · exact B394123
  · exact B394127
  · exact B394131
  · exact B394135
  · exact B394139
  · exact B394143
  · exact B394147
  · exact B394151
  · exact B394155
  · exact B394159
  · exact B394163
  · exact B394167
  · exact B394171
  · exact B394175
  · exact B394179
  · exact B394183
  · exact B394187
  · exact B394191
  · exact B394195
  · exact B394199
  · exact B394203
  · exact B394207
  · exact B394211
  · exact B394215
  · exact B394219
  · exact B394223
  · exact B394227
  · exact B394231
  · exact B394235
  · exact B394239
  · exact B394243
  · exact B394247
  · exact B394251
  · exact B394255
  · exact B394259
  · exact B394263
  · exact B394267
  · exact B394271
  · exact B394275
  · exact B394279
  · exact B394283
  · exact B394287
  · exact B394291
  · exact B394295
  · exact B394299
  · exact B394303
  · exact B394307
  · exact B394311
  · exact B394315
  · exact B394319
  · exact B394323
  · exact B394327
  · exact B394331
  · exact B394335
  · exact B394339
  · exact B394343
  · exact B394347
  · exact B394351
  · exact B394355
  · exact B394359
  · exact B394363
  · exact B394367
  · exact B394371
  · exact B394375
  · exact B394379
  · exact B394383
  · exact B394387
  · exact B394391
  · exact B394395
  · exact B394399
  · exact B394403
  · exact B394407
  · exact B394411
  · exact B394415
  · exact B394419
  · exact B394423
  · exact B394427
  · exact B394431
  · exact B394435
  · exact B394439
  · exact B394443
  · exact B394447
  · exact B394451
  · exact B394455
  · exact B394459
  · exact B394463
  · exact B394467
  · exact B394471
  · exact B394475
  · exact B394479
  · exact B394483
  · exact B394487
  · exact B394491
  · exact B394495
  · exact B394499
  · exact B394503
  · exact B394507
  · exact B394511
  · exact B394515
  · exact B394519
  · exact B394523
  · exact B394527
  · exact B394531
  · exact B394535
  · exact B394539
  · exact B394543
  · exact B394547
  · exact B394551
  · exact B394555
  · exact B394559
  · exact B394563
  · exact B394567
  · exact B394571
  · exact B394575
  · exact B394579
  · exact B394583
  · exact B394587
  · exact B394591
  · exact B394595
  · exact B394599
  · exact B394603
  · exact B394607
  · exact B394611
  · exact B394615
  · exact B394619
  · exact B394623
  · exact B394627
  · exact B394631
  · exact B394635
  · exact B394639
  · exact B394643
  · exact B394647
  · exact B394651
  · exact B394655
  · exact B394659
  · exact B394663
  · exact B394667
  · exact B394671
  · exact B394675
  · exact B394679
  · exact B394683
  · exact B394687
  · exact B394691
  · exact B394695
  · exact B394699
  · exact B394703
  · exact B394707
  · exact B394711
  · exact B394715
  · exact B394719
  · exact B394723
  · exact B394727
  · exact B394731
  · exact B394735
  · exact B394739
  · exact B394743
  · exact B394747
  · exact B394751
  · exact B394755
  · exact B394759
  · exact B394763
  · exact B394767
  · exact B394771
  · exact B394775
  · exact B394779
  · exact B394783
  · exact B394787
  · exact B394791
  · exact B394795
  · exact B394799
  · exact B394803
  · exact B394807
  · exact B394811
  · exact B394815
  · exact B394819
  · exact B394823
  · exact B394827
  · exact B394831
  · exact B394835
  · exact B394839
  · exact B394843
  · exact B394847
  · exact B394851
  · exact B394855
  · exact B394859
  · exact B394863
  · exact B394867
  · exact B394871
  · exact B394875
  · exact B394879
  · exact B394883
  · exact B394887
  · exact B394891
  · exact B394895
  · exact B394899
  · exact B394903
  · exact B394907
  · exact B394911
  · exact B394915
  · exact B394919
  · exact B394923
  · exact B394927
  · exact B394931
  · exact B394935
  · exact B394939
  · exact B394943
  · exact B394947
  · exact B394951
  · exact B394955
  · exact B394959
  · exact B394963
  · exact B394967
  · exact B394971
  · exact B394975
  · exact B394979
  · exact B394983
  · exact B394987
  · exact B394991
  · exact B394995
  · exact B394999
  · exact B395003
  · exact B395007
  · exact B395011
  · exact B395015
  · exact B395019
  · exact B395023
  · exact B395027
  · exact B395031
  · exact B395035
  · exact B395039
  · exact B395043
  · exact B395047
  · exact B395051
  · exact B395055
  · exact B395059
  · exact B395063
  · exact B395067
  · exact B395071
  · exact B395075
  · exact B395079
  · exact B395083
  · exact B395087
  · exact B395091
  · exact B395095
  · exact B395099
  · exact B395103
  · exact B395107
  · exact B395111
  · exact B395115
  · exact B395119
  · exact B395123
  · exact B395127
  · exact B395131
  · exact B395135
  · exact B395139
  · exact B395143
  · exact B395147
  · exact B395151
  · exact B395155
  · exact B395159
  · exact B395163
  · exact B395167
  · exact B395171
  · exact B395175
  · exact B395179
  · exact B395183
  · exact B395187
  · exact B395191
  · exact B395195
  · exact B395199
  · exact B395203
  · exact B395207
  · exact B395211
  · exact B395215
  · exact B395219
  · exact B395223
  · exact B395227
  · exact B395231
  · exact B395235
  · exact B395239
  · exact B395243
  · exact B395247
  · exact B395251
  · exact B395255
  · exact B395259
  · exact B395263
  · exact B395267
  · exact B395271
  · exact B395275
  · exact B395279
  · exact B395283
  · exact B395287
  · exact B395291
  · exact B395295
  · exact B395299
  · exact B395303
  · exact B395307
  · exact B395311
  · exact B395315
  · exact B395319
  · exact B395323
  · exact B395327
  · exact B395331
  · exact B395335
  · exact B395339
  · exact B395343
  · exact B395347
  · exact B395351
  · exact B395355
  · exact B395359
  · exact B395363
  · exact B395367
  · exact B395371
  · exact B395375
  · exact B395379
  · exact B395383
  · exact B395387
  · exact B395391
  · exact B395395
  · exact B395399
  · exact B395403
  · exact B395407
  · exact B395411
  · exact B395415
  · exact B395419
  · exact B395423
  · exact B395427
  · exact B395431
  · exact B395435
  · exact B395439
  · exact B395443
  · exact B395447
  · exact B395451
  · exact B395455
  · exact B395459
  · exact B395463
  · exact B395467
  · exact B395471
  · exact B395475
  · exact B395479
  · exact B395483
  · exact B395487
  · exact B395491
  · exact B395495
  · exact B395499
  · exact B395503
  · exact B395507
  · exact B395511
  · exact B395515
  · exact B395519
  · exact B395523
  · exact B395527
  · exact B395531
  · exact B395535
  · exact B395539
  · exact B395543
  · exact B395547
  · exact B395551
  · exact B395555
  · exact B395559
  · exact B395563
  · exact B395567
  · exact B395571
  · exact B395575
  · exact B395579
  · exact B395583
  · exact B395587
  · exact B395591
  · exact B395595
  · exact B395599
  · exact B395603
  · exact B395607
  · exact B395611
  · exact B395615
  · exact B395619
  · exact B395623
  · exact B395627
  · exact B395631
  · exact B395635
  · exact B395639
  · exact B395643
  · exact B395647
  · exact B395651
  · exact B395655
  · exact B395659
  · exact B395663
  · exact B395667
  · exact B395671
  · exact B395675
  · exact B395679
  · exact B395683
  · exact B395687
  · exact B395691
  · exact B395695
  · exact B395699
  · exact B395703
  · exact B395707
  · exact B395711
  · exact B395715
  · exact B395719
  · exact B395723
  · exact B395727
  · exact B395731
  · exact B395735
  · exact B395739
  · exact B395743
  · exact B395747
  · exact B395751
  · exact B395755
  · exact B395759
  · exact B395763
  · exact B395767
  · exact B395771
  · exact B395775
  · exact B395779
  · exact B395783
  · exact B395787
  · exact B395791
  · exact B395795
  · exact B395799
  · exact B395803
  · exact B395807
  · exact B395811
  · exact B395815
  · exact B395819
  · exact B395823
  · exact B395827
  · exact B395831
  · exact B395835
  · exact B395839
  · exact B395843
  · exact B395847
  · exact B395851
  · exact B395855
  · exact B395859
  · exact B395863
  · exact B395867
  · exact B395871
  · exact B395875
  · exact B395879
  · exact B395883
  · exact B395887
  · exact B395891
  · exact B395895
  · exact B395899
  · exact B395903
  · exact B395907
  · exact B395911
  · exact B395915
  · exact B395919
  · exact B395923
  · exact B395927
  · exact B395931
  · exact B395935
  · exact B395939
  · exact B395943
  · exact B395947
  · exact B395951
  · exact B395955
  · exact B395959
  · exact B395963
  · exact B395967
  · exact B395971
  · exact B395975
  · exact B395979
  · exact B395983
  · exact B395987
  · exact B395991
  · exact B395995
  · exact B395999
  · exact B396003
  · exact B396007
  · exact B396011
  · exact B396015
  · exact B396019
  · exact B396023
  · exact B396027
  · exact B396031
  · exact B396035
  · exact B396039
  · exact B396043
  · exact B396047
  · exact B396051
  · exact B396055
  · exact B396059
  · exact B396063
  · exact B396067
  · exact B396071
  · exact B396075
  · exact B396079
  · exact B396083
  · exact B396087
  · exact B396091
  · exact B396095
  · exact B396099
  · exact B396103
  · exact B396107
  · exact B396111
  · exact B396115
  · exact B396119
  · exact B396123
  · exact B396127
  · exact B396131
  · exact B396135
  · exact B396139
  · exact B396143
  · exact B396147
  · exact B396151
  · exact B396155
  · exact B396159
  · exact B396163
  · exact B396167
  · exact B396171
  · exact B396175
  · exact B396179
  · exact B396183
  · exact B396187
  · exact B396191
  · exact B396195
  · exact B396199
  · exact B396203
  · exact B396207
  · exact B396211
  · exact B396215
  · exact B396219
  · exact B396223
  · exact B396227
  · exact B396231
  · exact B396235
  · exact B396239
  · exact B396243
  · exact B396247
  · exact B396251
  · exact B396255
  · exact B396259
  · exact B396263
  · exact B396267
  · exact B396271
  · exact B396275
  · exact B396279
  · exact B396283
  · exact B396287
  · exact B396291
  · exact B396295
  · exact B396299
  · exact B396303
  · exact B396307
  · exact B396311
  · exact B396315
  · exact B396319
  · exact B396323
  · exact B396327
  · exact B396331
  · exact B396335
  · exact B396339
  · exact B396343
  · exact B396347
  · exact B396351
  · exact B396355
  · exact B396359
  · exact B396363
  · exact B396367
  · exact B396371
  · exact B396375
  · exact B396379
  · exact B396383
  · exact B396387
  · exact B396391
  · exact B396395
  · exact B396399
  · exact B396403
  · exact B396407
  · exact B396411
  · exact B396415
  · exact B396419
  · exact B396423
  · exact B396427
  · exact B396431
  · exact B396435
  · exact B396439
  · exact B396443
  · exact B396447
  · exact B396451
  · exact B396455
  · exact B396459
  · exact B396463
  · exact B396467
  · exact B396471
  · exact B396475
  · exact B396479
  · exact B396483
  · exact B396487
  · exact B396491
  · exact B396495
  · exact B396499
  · exact B396503
  · exact B396507
  · exact B396511
  · exact B396515
  · exact B396519
  · exact B396523
  · exact B396527
  · exact B396531
  · exact B396535
  · exact B396539
  · exact B396543
  · exact B396547
  · exact B396551
  · exact B396555
  · exact B396559
  · exact B396563

theorem C1 (j : ℕ) (h1 : 99141 ≤ j) (h2 : j ≤ 99440) : Blo 393766 (4 * j + 3) := by
  interval_cases j
  · exact B396567
  · exact B396571
  · exact B396575
  · exact B396579
  · exact B396583
  · exact B396587
  · exact B396591
  · exact B396595
  · exact B396599
  · exact B396603
  · exact B396607
  · exact B396611
  · exact B396615
  · exact B396619
  · exact B396623
  · exact B396627
  · exact B396631
  · exact B396635
  · exact B396639
  · exact B396643
  · exact B396647
  · exact B396651
  · exact B396655
  · exact B396659
  · exact B396663
  · exact B396667
  · exact B396671
  · exact B396675
  · exact B396679
  · exact B396683
  · exact B396687
  · exact B396691
  · exact B396695
  · exact B396699
  · exact B396703
  · exact B396707
  · exact B396711
  · exact B396715
  · exact B396719
  · exact B396723
  · exact B396727
  · exact B396731
  · exact B396735
  · exact B396739
  · exact B396743
  · exact B396747
  · exact B396751
  · exact B396755
  · exact B396759
  · exact B396763
  · exact B396767
  · exact B396771
  · exact B396775
  · exact B396779
  · exact B396783
  · exact B396787
  · exact B396791
  · exact B396795
  · exact B396799
  · exact B396803
  · exact B396807
  · exact B396811
  · exact B396815
  · exact B396819
  · exact B396823
  · exact B396827
  · exact B396831
  · exact B396835
  · exact B396839
  · exact B396843
  · exact B396847
  · exact B396851
  · exact B396855
  · exact B396859
  · exact B396863
  · exact B396867
  · exact B396871
  · exact B396875
  · exact B396879
  · exact B396883
  · exact B396887
  · exact B396891
  · exact B396895
  · exact B396899
  · exact B396903
  · exact B396907
  · exact B396911
  · exact B396915
  · exact B396919
  · exact B396923
  · exact B396927
  · exact B396931
  · exact B396935
  · exact B396939
  · exact B396943
  · exact B396947
  · exact B396951
  · exact B396955
  · exact B396959
  · exact B396963
  · exact B396967
  · exact B396971
  · exact B396975
  · exact B396979
  · exact B396983
  · exact B396987
  · exact B396991
  · exact B396995
  · exact B396999
  · exact B397003
  · exact B397007
  · exact B397011
  · exact B397015
  · exact B397019
  · exact B397023
  · exact B397027
  · exact B397031
  · exact B397035
  · exact B397039
  · exact B397043
  · exact B397047
  · exact B397051
  · exact B397055
  · exact B397059
  · exact B397063
  · exact B397067
  · exact B397071
  · exact B397075
  · exact B397079
  · exact B397083
  · exact B397087
  · exact B397091
  · exact B397095
  · exact B397099
  · exact B397103
  · exact B397107
  · exact B397111
  · exact B397115
  · exact B397119
  · exact B397123
  · exact B397127
  · exact B397131
  · exact B397135
  · exact B397139
  · exact B397143
  · exact B397147
  · exact B397151
  · exact B397155
  · exact B397159
  · exact B397163
  · exact B397167
  · exact B397171
  · exact B397175
  · exact B397179
  · exact B397183
  · exact B397187
  · exact B397191
  · exact B397195
  · exact B397199
  · exact B397203
  · exact B397207
  · exact B397211
  · exact B397215
  · exact B397219
  · exact B397223
  · exact B397227
  · exact B397231
  · exact B397235
  · exact B397239
  · exact B397243
  · exact B397247
  · exact B397251
  · exact B397255
  · exact B397259
  · exact B397263
  · exact B397267
  · exact B397271
  · exact B397275
  · exact B397279
  · exact B397283
  · exact B397287
  · exact B397291
  · exact B397295
  · exact B397299
  · exact B397303
  · exact B397307
  · exact B397311
  · exact B397315
  · exact B397319
  · exact B397323
  · exact B397327
  · exact B397331
  · exact B397335
  · exact B397339
  · exact B397343
  · exact B397347
  · exact B397351
  · exact B397355
  · exact B397359
  · exact B397363
  · exact B397367
  · exact B397371
  · exact B397375
  · exact B397379
  · exact B397383
  · exact B397387
  · exact B397391
  · exact B397395
  · exact B397399
  · exact B397403
  · exact B397407
  · exact B397411
  · exact B397415
  · exact B397419
  · exact B397423
  · exact B397427
  · exact B397431
  · exact B397435
  · exact B397439
  · exact B397443
  · exact B397447
  · exact B397451
  · exact B397455
  · exact B397459
  · exact B397463
  · exact B397467
  · exact B397471
  · exact B397475
  · exact B397479
  · exact B397483
  · exact B397487
  · exact B397491
  · exact B397495
  · exact B397499
  · exact B397503
  · exact B397507
  · exact B397511
  · exact B397515
  · exact B397519
  · exact B397523
  · exact B397527
  · exact B397531
  · exact B397535
  · exact B397539
  · exact B397543
  · exact B397547
  · exact B397551
  · exact B397555
  · exact B397559
  · exact B397563
  · exact B397567
  · exact B397571
  · exact B397575
  · exact B397579
  · exact B397583
  · exact B397587
  · exact B397591
  · exact B397595
  · exact B397599
  · exact B397603
  · exact B397607
  · exact B397611
  · exact B397615
  · exact B397619
  · exact B397623
  · exact B397627
  · exact B397631
  · exact B397635
  · exact B397639
  · exact B397643
  · exact B397647
  · exact B397651
  · exact B397655
  · exact B397659
  · exact B397663
  · exact B397667
  · exact B397671
  · exact B397675
  · exact B397679
  · exact B397683
  · exact B397687
  · exact B397691
  · exact B397695
  · exact B397699
  · exact B397703
  · exact B397707
  · exact B397711
  · exact B397715
  · exact B397719
  · exact B397723
  · exact B397727
  · exact B397731
  · exact B397735
  · exact B397739
  · exact B397743
  · exact B397747
  · exact B397751
  · exact B397755
  · exact B397759
  · exact B397763

theorem solution (m : ℕ) (hlo : 393766 ≤ m) (hhi : m ≤ 397766) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 98441 ≤ j := by omega
    have hj2 : j ≤ 99440 := by omega
    have hb : Blo 393766 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 99141 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
