-- Prove2me | solution 1 for syracuse_descends_range_1389514_1391514
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:33.469323+00:00
-- url     : https://prove2.me/submissions/cd0cf244-e3f0-4e50-b7ae-8276e1714009

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


theorem B1564681 : Blo 1389514 1564681 := bbase (se 2 (by rfl) ⟨586755, by rfl⟩ : syracuseStep 1564681 = 1173511) (by norm_num)
theorem B3129389 : Blo 1389514 3129389 := bbase (se 3 (by rfl) ⟨586760, by rfl⟩ : syracuseStep 3129389 = 1173521) (by norm_num)
theorem B1564717 : Blo 1389514 1564717 := bbase (se 3 (by rfl) ⟨293384, by rfl⟩ : syracuseStep 1564717 = 586769) (by norm_num)
theorem B1564753 : Blo 1389514 1564753 := bbase (se 2 (by rfl) ⟨586782, by rfl⟩ : syracuseStep 1564753 = 1173565) (by norm_num)
theorem B2637917 : Blo 1389514 2637917 := bbase (se 3 (by rfl) ⟨494609, by rfl⟩ : syracuseStep 2637917 = 989219) (by norm_num)
theorem B3129461 : Blo 1389514 3129461 := bbase (se 5 (by rfl) ⟨146693, by rfl⟩ : syracuseStep 3129461 = 293387) (by norm_num)
theorem B1564789 : Blo 1389514 1564789 := bbase (se 5 (by rfl) ⟨73349, by rfl⟩ : syracuseStep 1564789 = 146699) (by norm_num)
theorem B2228357 : Blo 1389514 2228357 := bbase (se 4 (by rfl) ⟨208908, by rfl⟩ : syracuseStep 2228357 = 417817) (by norm_num)
theorem B2818189 : Blo 1389514 2818189 := bbase (se 3 (by rfl) ⟨528410, by rfl⟩ : syracuseStep 2818189 = 1056821) (by norm_num)
theorem B4694165 : Blo 1389514 4694165 := bbase (se 6 (by rfl) ⟨110019, by rfl⟩ : syracuseStep 4694165 = 220039) (by norm_num)
theorem B1564825 : Blo 1389514 1564825 := bbase (se 2 (by rfl) ⟨586809, by rfl⟩ : syracuseStep 1564825 = 1173619) (by norm_num)
theorem B3129533 : Blo 1389514 3129533 := bbase (se 3 (by rfl) ⟨586787, by rfl⟩ : syracuseStep 3129533 = 1173575) (by norm_num)
theorem B1564861 : Blo 1389514 1564861 := bbase (se 3 (by rfl) ⟨293411, by rfl⟩ : syracuseStep 1564861 = 586823) (by norm_num)
theorem B8904917 : Blo 1389514 8904917 := bbase (se 7 (by rfl) ⟨104354, by rfl⟩ : syracuseStep 8904917 = 208709) (by norm_num)
theorem B1564897 : Blo 1389514 1564897 := bbase (se 2 (by rfl) ⟨586836, by rfl⟩ : syracuseStep 1564897 = 1173673) (by norm_num)
theorem B2859229 : Blo 1389514 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B1409281 : Blo 1389514 1409281 := bbase (se 2 (by rfl) ⟨528480, by rfl⟩ : syracuseStep 1409281 = 1056961) (by norm_num)
theorem B3129605 : Blo 1389514 3129605 := bbase (se 4 (by rfl) ⟨293400, by rfl⟩ : syracuseStep 3129605 = 586801) (by norm_num)
theorem B1564933 : Blo 1389514 1564933 := bbase (se 4 (by rfl) ⟨146712, by rfl⟩ : syracuseStep 1564933 = 293425) (by norm_num)
theorem B5275925 : Blo 1389514 5275925 := bbase (se 6 (by rfl) ⟨123654, by rfl⟩ : syracuseStep 5275925 = 247309) (by norm_num)
theorem B1409305 : Blo 1389514 1409305 := bbase (se 2 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 1409305 = 1056979) (by norm_num)
theorem B1564969 : Blo 1389514 1564969 := bbase (se 2 (by rfl) ⟨586863, by rfl⟩ : syracuseStep 1564969 = 1173727) (by norm_num)
theorem B3129677 : Blo 1389514 3129677 := bbase (se 3 (by rfl) ⟨586814, by rfl⟩ : syracuseStep 3129677 = 1173629) (by norm_num)
theorem B1565005 : Blo 1389514 1565005 := bbase (se 3 (by rfl) ⟨293438, by rfl⟩ : syracuseStep 1565005 = 586877) (by norm_num)
theorem B1565041 : Blo 1389514 1565041 := bbase (se 2 (by rfl) ⟨586890, by rfl⟩ : syracuseStep 1565041 = 1173781) (by norm_num)
theorem B3129749 : Blo 1389514 3129749 := bbase (se 6 (by rfl) ⟨73353, by rfl⟩ : syracuseStep 3129749 = 146707) (by norm_num)
theorem B1565077 : Blo 1389514 1565077 := bbase (se 6 (by rfl) ⟨36681, by rfl⟩ : syracuseStep 1565077 = 73363) (by norm_num)
theorem B13541813 : Blo 1389514 13541813 := bbase (se 5 (by rfl) ⟨634772, by rfl⟩ : syracuseStep 13541813 = 1269545) (by norm_num)
theorem B1565113 : Blo 1389514 1565113 := bbase (se 2 (by rfl) ⟨586917, by rfl⟩ : syracuseStep 1565113 = 1173835) (by norm_num)
theorem B3129821 : Blo 1389514 3129821 := bbase (se 3 (by rfl) ⟨586841, by rfl⟩ : syracuseStep 3129821 = 1173683) (by norm_num)
theorem B1565149 : Blo 1389514 1565149 := bbase (se 3 (by rfl) ⟨293465, by rfl⟩ : syracuseStep 1565149 = 586931) (by norm_num)
theorem B1565185 : Blo 1389514 1565185 := bbase (se 2 (by rfl) ⟨586944, by rfl⟩ : syracuseStep 1565185 = 1173889) (by norm_num)
theorem B3129893 : Blo 1389514 3129893 := bbase (se 4 (by rfl) ⟨293427, by rfl⟩ : syracuseStep 3129893 = 586855) (by norm_num)
theorem B1565221 : Blo 1389514 1565221 := bbase (se 4 (by rfl) ⟨146739, by rfl⟩ : syracuseStep 1565221 = 293479) (by norm_num)
theorem B4694597 : Blo 1389514 4694597 := bbase (se 4 (by rfl) ⟨440118, by rfl⟩ : syracuseStep 4694597 = 880237) (by norm_num)
theorem B1565257 : Blo 1389514 1565257 := bbase (se 2 (by rfl) ⟨586971, by rfl⟩ : syracuseStep 1565257 = 1173943) (by norm_num)
theorem B3129965 : Blo 1389514 3129965 := bbase (se 3 (by rfl) ⟨586868, by rfl⟩ : syracuseStep 3129965 = 1173737) (by norm_num)
theorem B1565293 : Blo 1389514 1565293 := bbase (se 3 (by rfl) ⟨293492, by rfl⟩ : syracuseStep 1565293 = 586985) (by norm_num)
theorem B1565329 : Blo 1389514 1565329 := bbase (se 2 (by rfl) ⟨586998, by rfl⟩ : syracuseStep 1565329 = 1173997) (by norm_num)
theorem B3130037 : Blo 1389514 3130037 := bbase (se 5 (by rfl) ⟨146720, by rfl⟩ : syracuseStep 3130037 = 293441) (by norm_num)
theorem B1565365 : Blo 1389514 1565365 := bbase (se 5 (by rfl) ⟨73376, by rfl⟩ : syracuseStep 1565365 = 146753) (by norm_num)
theorem B1565401 : Blo 1389514 1565401 := bbase (se 2 (by rfl) ⟨587025, by rfl⟩ : syracuseStep 1565401 = 1174051) (by norm_num)
theorem B3130109 : Blo 1389514 3130109 := bbase (se 3 (by rfl) ⟨586895, by rfl⟩ : syracuseStep 3130109 = 1173791) (by norm_num)
theorem B1565437 : Blo 1389514 1565437 := bbase (se 3 (by rfl) ⟨293519, by rfl⟩ : syracuseStep 1565437 = 587039) (by norm_num)
theorem B7037765 : Blo 1389514 7037765 := bbase (se 4 (by rfl) ⟨659790, by rfl⟩ : syracuseStep 7037765 = 1319581) (by norm_num)
theorem B3130181 : Blo 1389514 3130181 := bbase (se 4 (by rfl) ⟨293454, by rfl⟩ : syracuseStep 3130181 = 586909) (by norm_num)
theorem B2638669 : Blo 1389514 2638669 := bbase (se 3 (by rfl) ⟨494750, by rfl⟩ : syracuseStep 2638669 = 989501) (by norm_num)
theorem B6021973 : Blo 1389514 6021973 := bbase (se 9 (by rfl) ⟨17642, by rfl⟩ : syracuseStep 6021973 = 35285) (by norm_num)
theorem B3343189 : Blo 1389514 3343189 := bbase (se 9 (by rfl) ⟨9794, by rfl⟩ : syracuseStep 3343189 = 19589) (by norm_num)
theorem B3957605 : Blo 1389514 3957605 := bbase (se 4 (by rfl) ⟨371025, by rfl⟩ : syracuseStep 3957605 = 742051) (by norm_num)
theorem B1606541 : Blo 1389514 1606541 := bbase (se 3 (by rfl) ⟨301226, by rfl⟩ : syracuseStep 1606541 = 602453) (by norm_num)
theorem B3130253 : Blo 1389514 3130253 := bbase (se 3 (by rfl) ⟨586922, by rfl⟩ : syracuseStep 3130253 = 1173845) (by norm_num)
theorem B3343285 : Blo 1389514 3343285 := bbase (se 5 (by rfl) ⟨156716, by rfl⟩ : syracuseStep 3343285 = 313433) (by norm_num)
theorem B3130325 : Blo 1389514 3130325 := bbase (se 7 (by rfl) ⟨36683, by rfl⟩ : syracuseStep 3130325 = 73367) (by norm_num)
theorem B2638813 : Blo 1389514 2638813 := bbase (se 3 (by rfl) ⟨494777, by rfl⟩ : syracuseStep 2638813 = 989555) (by norm_num)
theorem B4695029 : Blo 1389514 4695029 := bbase (se 5 (by rfl) ⟨220079, by rfl⟩ : syracuseStep 4695029 = 440159) (by norm_num)
theorem B3130397 : Blo 1389514 3130397 := bbase (se 3 (by rfl) ⟨586949, by rfl⟩ : syracuseStep 3130397 = 1173899) (by norm_num)
theorem B3130469 : Blo 1389514 3130469 := bbase (se 4 (by rfl) ⟨293481, by rfl⟩ : syracuseStep 3130469 = 586963) (by norm_num)
theorem B2638973 : Blo 1389514 2638973 := bbase (se 3 (by rfl) ⟨494807, by rfl⟩ : syracuseStep 2638973 = 989615) (by norm_num)
theorem B3130541 : Blo 1389514 3130541 := bbase (se 3 (by rfl) ⟨586976, by rfl⟩ : syracuseStep 3130541 = 1173953) (by norm_num)
theorem B1483957 : Blo 1389514 1483957 := bbase (se 5 (by rfl) ⟨69560, by rfl⟩ : syracuseStep 1483957 = 139121) (by norm_num)
theorem B7619765 : Blo 1389514 7619765 := bbase (se 5 (by rfl) ⟨357176, by rfl⟩ : syracuseStep 7619765 = 714353) (by norm_num)
theorem B7922933 : Blo 1389514 7922933 := bbase (se 5 (by rfl) ⟨371387, by rfl⟩ : syracuseStep 7922933 = 742775) (by norm_num)
theorem B3130613 : Blo 1389514 3130613 := bbase (se 5 (by rfl) ⟨146747, by rfl⟩ : syracuseStep 3130613 = 293495) (by norm_num)
theorem B2376973 : Blo 1389514 2376973 := bbase (se 3 (by rfl) ⟨445682, by rfl⟩ : syracuseStep 2376973 = 891365) (by norm_num)
theorem B2639117 : Blo 1389514 2639117 := bbase (se 3 (by rfl) ⟨494834, by rfl⟩ : syracuseStep 2639117 = 989669) (by norm_num)
theorem B2819357 : Blo 1389514 2819357 := bbase (se 3 (by rfl) ⟨528629, by rfl⟩ : syracuseStep 2819357 = 1057259) (by norm_num)
theorem B2819389 : Blo 1389514 2819389 := bbase (se 3 (by rfl) ⟨528635, by rfl⟩ : syracuseStep 2819389 = 1057271) (by norm_num)
theorem B3130685 : Blo 1389514 3130685 := bbase (se 3 (by rfl) ⟨587003, by rfl⟩ : syracuseStep 3130685 = 1174007) (by norm_num)
theorem B6686069 : Blo 1389514 6686069 := bbase (se 5 (by rfl) ⟨313409, by rfl⟩ : syracuseStep 6686069 = 626819) (by norm_num)
theorem B3130757 : Blo 1389514 3130757 := bbase (se 4 (by rfl) ⟨293508, by rfl⟩ : syracuseStep 3130757 = 587017) (by norm_num)
theorem B4695461 : Blo 1389514 4695461 := bbase (se 4 (by rfl) ⟨440199, by rfl⟩ : syracuseStep 4695461 = 880399) (by norm_num)
theorem B5277109 : Blo 1389514 5277109 := bbase (se 5 (by rfl) ⟨247364, by rfl⟩ : syracuseStep 5277109 = 494729) (by norm_num)
theorem B3130829 : Blo 1389514 3130829 := bbase (se 3 (by rfl) ⟨587030, by rfl⟩ : syracuseStep 3130829 = 1174061) (by norm_num)
theorem B2115077 : Blo 1389514 2115077 := bbase (se 4 (by rfl) ⟨198288, by rfl⟩ : syracuseStep 2115077 = 396577) (by norm_num)
theorem B3130901 : Blo 1389514 3130901 := bbase (se 6 (by rfl) ⟨73380, by rfl⟩ : syracuseStep 3130901 = 146761) (by norm_num)
theorem B2639405 : Blo 1389514 2639405 := bbase (se 3 (by rfl) ⟨494888, by rfl⟩ : syracuseStep 2639405 = 989777) (by norm_num)
theorem B10298933 : Blo 1389514 10298933 := bbase (se 5 (by rfl) ⟨482762, by rfl⟩ : syracuseStep 10298933 = 965525) (by norm_num)
theorem B51455573 : Blo 1389514 51455573 := bbase (se 8 (by rfl) ⟨301497, by rfl⟩ : syracuseStep 51455573 = 602995) (by norm_num)
theorem B1484401 : Blo 1389514 1484401 := bbase (se 2 (by rfl) ⟨556650, by rfl⟩ : syracuseStep 1484401 = 1113301) (by norm_num)
theorem B14460565 : Blo 1389514 14460565 := bbase (se 6 (by rfl) ⟨338919, by rfl⟩ : syracuseStep 14460565 = 677839) (by norm_num)
theorem B2639557 : Blo 1389514 2639557 := bbase (se 4 (by rfl) ⟨247458, by rfl⟩ : syracuseStep 2639557 = 494917) (by norm_num)
theorem B24094421 : Blo 1389514 24094421 := bbase (se 7 (by rfl) ⟨282356, by rfl⟩ : syracuseStep 24094421 = 564713) (by norm_num)
theorem B5277413 : Blo 1389514 5277413 := bbase (se 4 (by rfl) ⟨494757, by rfl⟩ : syracuseStep 5277413 = 989515) (by norm_num)
theorem B1484525 : Blo 1389514 1484525 := bbase (se 3 (by rfl) ⟨278348, by rfl⟩ : syracuseStep 1484525 = 556697) (by norm_num)
theorem B2819909 : Blo 1389514 2819909 := bbase (se 4 (by rfl) ⟨264366, by rfl⟩ : syracuseStep 2819909 = 528733) (by norm_num)
theorem B4695893 : Blo 1389514 4695893 := bbase (se 9 (by rfl) ⟨13757, by rfl⟩ : syracuseStep 4695893 = 27515) (by norm_num)
theorem B2344909 : Blo 1389514 2344909 := bbase (se 3 (by rfl) ⟨439670, by rfl⟩ : syracuseStep 2344909 = 879341) (by norm_num)
theorem B3008477 : Blo 1389514 3008477 := bbase (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) (by norm_num)
theorem B1484777 : Blo 1389514 1484777 := bbase (se 2 (by rfl) ⟨556791, by rfl⟩ : syracuseStep 1484777 = 1113583) (by norm_num)
theorem B2639861 : Blo 1389514 2639861 := bbase (se 5 (by rfl) ⟨123743, by rfl⟩ : syracuseStep 2639861 = 247487) (by norm_num)
theorem B3958789 : Blo 1389514 3958789 := bbase (se 4 (by rfl) ⟨371136, by rfl⟩ : syracuseStep 3958789 = 742273) (by norm_num)
theorem B15042581 : Blo 1389514 15042581 := bbase (se 6 (by rfl) ⟨352560, by rfl⟩ : syracuseStep 15042581 = 705121) (by norm_num)
theorem B2344997 : Blo 1389514 2344997 := bbase (se 4 (by rfl) ⟨219843, by rfl⟩ : syracuseStep 2344997 = 439687) (by norm_num)
theorem B2377765 : Blo 1389514 2377765 := bbase (se 4 (by rfl) ⟨222915, by rfl⟩ : syracuseStep 2377765 = 445831) (by norm_num)
theorem B7039061 : Blo 1389514 7039061 := bbase (se 8 (by rfl) ⟨41244, by rfl⟩ : syracuseStep 7039061 = 82489) (by norm_num)
theorem B2115709 : Blo 1389514 2115709 := bbase (se 3 (by rfl) ⟨396695, by rfl⟩ : syracuseStep 2115709 = 793391) (by norm_num)
theorem B2345125 : Blo 1389514 2345125 := bbase (se 4 (by rfl) ⟨219855, by rfl⟩ : syracuseStep 2345125 = 439711) (by norm_num)
theorem B3958949 : Blo 1389514 3958949 := bbase (se 4 (by rfl) ⟨371151, by rfl⟩ : syracuseStep 3958949 = 742303) (by norm_num)
theorem B2967725 : Blo 1389514 2967725 := bbase (se 3 (by rfl) ⟨556448, by rfl⟩ : syracuseStep 2967725 = 1112897) (by norm_num)
theorem B13355189 : Blo 1389514 13355189 := bbase (se 5 (by rfl) ⟨626024, by rfl⟩ : syracuseStep 13355189 = 1252049) (by norm_num)
theorem B2345213 : Blo 1389514 2345213 := bbase (se 3 (by rfl) ⟨439727, by rfl⟩ : syracuseStep 2345213 = 879455) (by norm_num)
theorem B4696325 : Blo 1389514 4696325 := bbase (se 4 (by rfl) ⟨440280, by rfl⟩ : syracuseStep 4696325 = 880561) (by norm_num)
theorem B2345341 : Blo 1389514 2345341 := bbase (se 3 (by rfl) ⟨439751, by rfl⟩ : syracuseStep 2345341 = 879503) (by norm_num)
theorem B3959189 : Blo 1389514 3959189 := bbase (se 6 (by rfl) ⟨92793, by rfl⟩ : syracuseStep 3959189 = 185587) (by norm_num)
theorem B2820509 : Blo 1389514 2820509 := bbase (se 3 (by rfl) ⟨528845, by rfl⟩ : syracuseStep 2820509 = 1057691) (by norm_num)
theorem B1485221 : Blo 1389514 1485221 := bbase (se 4 (by rfl) ⟨139239, by rfl⟩ : syracuseStep 1485221 = 278479) (by norm_num)
theorem B5941669 : Blo 1389514 5941669 := bbase (se 4 (by rfl) ⟨557031, by rfl⟩ : syracuseStep 5941669 = 1114063) (by norm_num)
theorem B2820557 : Blo 1389514 2820557 := bbase (se 3 (by rfl) ⟨528854, by rfl⟩ : syracuseStep 2820557 = 1057709) (by norm_num)
theorem B2345429 : Blo 1389514 2345429 := bbase (se 7 (by rfl) ⟨27485, by rfl⟩ : syracuseStep 2345429 = 54971) (by norm_num)
theorem B2968093 : Blo 1389514 2968093 := bbase (se 3 (by rfl) ⟨556517, by rfl⟩ : syracuseStep 2968093 = 1113035) (by norm_num)
theorem B2345557 : Blo 1389514 2345557 := bbase (se 8 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 2345557 = 27487) (by norm_num)
theorem B3959381 : Blo 1389514 3959381 := bbase (se 8 (by rfl) ⟨23199, by rfl⟩ : syracuseStep 3959381 = 46399) (by norm_num)
theorem B6679189 : Blo 1389514 6679189 := bbase (se 6 (by rfl) ⟨156543, by rfl⟩ : syracuseStep 6679189 = 313087) (by norm_num)
theorem B1485469 : Blo 1389514 1485469 := bbase (se 3 (by rfl) ⟨278525, by rfl⟩ : syracuseStep 1485469 = 557051) (by norm_num)
theorem B2345645 : Blo 1389514 2345645 := bbase (se 3 (by rfl) ⟨439808, by rfl⟩ : syracuseStep 2345645 = 879617) (by norm_num)
theorem B2640613 : Blo 1389514 2640613 := bbase (se 4 (by rfl) ⟨247557, by rfl⟩ : syracuseStep 2640613 = 495115) (by norm_num)
theorem B2345773 : Blo 1389514 2345773 := bbase (se 3 (by rfl) ⟨439832, by rfl⟩ : syracuseStep 2345773 = 879665) (by norm_num)
theorem B3173165 : Blo 1389514 3173165 := bbase (se 3 (by rfl) ⟨594968, by rfl⟩ : syracuseStep 3173165 = 1189937) (by norm_num)
theorem B3517253 : Blo 1389514 3517253 := bbase (se 4 (by rfl) ⟨329742, by rfl⟩ : syracuseStep 3517253 = 659485) (by norm_num)
theorem B2640757 : Blo 1389514 2640757 := bbase (se 5 (by rfl) ⟨123785, by rfl⟩ : syracuseStep 2640757 = 247571) (by norm_num)
theorem B2345861 : Blo 1389514 2345861 := bbase (se 4 (by rfl) ⟨219924, by rfl⟩ : syracuseStep 2345861 = 439849) (by norm_num)
theorem B3615725 : Blo 1389514 3615725 := bbase (se 3 (by rfl) ⟨677948, by rfl⟩ : syracuseStep 3615725 = 1355897) (by norm_num)
theorem B3517445 : Blo 1389514 3517445 := bbase (se 4 (by rfl) ⟨329760, by rfl⟩ : syracuseStep 3517445 = 659521) (by norm_num)
theorem B2345989 : Blo 1389514 2345989 := bbase (se 4 (by rfl) ⟨219936, by rfl⟩ : syracuseStep 2345989 = 439873) (by norm_num)
theorem B2640917 : Blo 1389514 2640917 := bbase (se 6 (by rfl) ⟨61896, by rfl⟩ : syracuseStep 2640917 = 123793) (by norm_num)
theorem B1485913 : Blo 1389514 1485913 := bbase (se 2 (by rfl) ⟨557217, by rfl⟩ : syracuseStep 1485913 = 1114435) (by norm_num)
theorem B2346077 : Blo 1389514 2346077 := bbase (se 3 (by rfl) ⟨439889, by rfl⟩ : syracuseStep 2346077 = 879779) (by norm_num)
theorem B8907893 : Blo 1389514 8907893 := bbase (se 5 (by rfl) ⟨417557, by rfl⟩ : syracuseStep 8907893 = 835115) (by norm_num)
theorem B2641061 : Blo 1389514 2641061 := bbase (se 4 (by rfl) ⟨247599, by rfl⟩ : syracuseStep 2641061 = 495199) (by norm_num)
theorem B2346205 : Blo 1389514 2346205 := bbase (se 3 (by rfl) ⟨439913, by rfl⟩ : syracuseStep 2346205 = 879827) (by norm_num)
theorem B2346293 : Blo 1389514 2346293 := bbase (se 5 (by rfl) ⟨109982, by rfl⟩ : syracuseStep 2346293 = 219965) (by norm_num)
theorem B3517789 : Blo 1389514 3517789 := bbase (se 3 (by rfl) ⟨659585, by rfl⟩ : syracuseStep 3517789 = 1319171) (by norm_num)
theorem B7040357 : Blo 1389514 7040357 := bbase (se 4 (by rfl) ⟨660033, by rfl⟩ : syracuseStep 7040357 = 1320067) (by norm_num)
theorem B2346421 : Blo 1389514 2346421 := bbase (se 5 (by rfl) ⟨109988, by rfl⟩ : syracuseStep 2346421 = 219977) (by norm_num)
theorem B2084285 : Blo 1389514 2084285 := bbase (se 3 (by rfl) ⟨390803, by rfl⟩ : syracuseStep 2084285 = 781607) (by norm_num)
theorem B2641349 : Blo 1389514 2641349 := bbase (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) (by norm_num)
theorem B3517901 : Blo 1389514 3517901 := bbase (se 3 (by rfl) ⟨659606, by rfl⟩ : syracuseStep 3517901 = 1319213) (by norm_num)
theorem B2084309 : Blo 1389514 2084309 := bbase (se 7 (by rfl) ⟨24425, by rfl⟩ : syracuseStep 2084309 = 48851) (by norm_num)
theorem B2084333 : Blo 1389514 2084333 := bbase (se 3 (by rfl) ⟨390812, by rfl⟩ : syracuseStep 2084333 = 781625) (by norm_num)
theorem B2084357 : Blo 1389514 2084357 := bbase (se 4 (by rfl) ⟨195408, by rfl⟩ : syracuseStep 2084357 = 390817) (by norm_num)
theorem B2346509 : Blo 1389514 2346509 := bbase (se 3 (by rfl) ⟨439970, by rfl⟩ : syracuseStep 2346509 = 879941) (by norm_num)
theorem B2084381 : Blo 1389514 2084381 := bbase (se 3 (by rfl) ⟨390821, by rfl⟩ : syracuseStep 2084381 = 781643) (by norm_num)
theorem B2084405 : Blo 1389514 2084405 := bbase (se 5 (by rfl) ⟨97706, by rfl⟩ : syracuseStep 2084405 = 195413) (by norm_num)
theorem B3960373 : Blo 1389514 3960373 := bbase (se 5 (by rfl) ⟨185642, by rfl⟩ : syracuseStep 3960373 = 371285) (by norm_num)
theorem B4951621 : Blo 1389514 4951621 := bbase (se 4 (by rfl) ⟨464214, by rfl⟩ : syracuseStep 4951621 = 928429) (by norm_num)
theorem B2084429 : Blo 1389514 2084429 := bbase (se 3 (by rfl) ⟨390830, by rfl⟩ : syracuseStep 2084429 = 781661) (by norm_num)
theorem B1584721 : Blo 1389514 1584721 := bbase (se 2 (by rfl) ⟨594270, by rfl⟩ : syracuseStep 1584721 = 1188541) (by norm_num)
theorem B2641501 : Blo 1389514 2641501 := bbase (se 3 (by rfl) ⟨495281, by rfl⟩ : syracuseStep 2641501 = 990563) (by norm_num)
theorem B2084453 : Blo 1389514 2084453 := bbase (se 4 (by rfl) ⟨195417, by rfl⟩ : syracuseStep 2084453 = 390835) (by norm_num)
theorem B2084477 : Blo 1389514 2084477 := bbase (se 3 (by rfl) ⟨390839, by rfl⟩ : syracuseStep 2084477 = 781679) (by norm_num)
theorem B2674309 : Blo 1389514 2674309 := bbase (se 4 (by rfl) ⟨250716, by rfl⟩ : syracuseStep 2674309 = 501433) (by norm_num)
theorem B3518093 : Blo 1389514 3518093 := bbase (se 3 (by rfl) ⟨659642, by rfl⟩ : syracuseStep 3518093 = 1319285) (by norm_num)
theorem B2346637 : Blo 1389514 2346637 := bbase (se 3 (by rfl) ⟨439994, by rfl⟩ : syracuseStep 2346637 = 879989) (by norm_num)
theorem B2084501 : Blo 1389514 2084501 := bbase (se 6 (by rfl) ⟨48855, by rfl⟩ : syracuseStep 2084501 = 97711) (by norm_num)
theorem B2084525 : Blo 1389514 2084525 := bbase (se 3 (by rfl) ⟨390848, by rfl⟩ : syracuseStep 2084525 = 781697) (by norm_num)
theorem B2084549 : Blo 1389514 2084549 := bbase (se 4 (by rfl) ⟨195426, by rfl⟩ : syracuseStep 2084549 = 390853) (by norm_num)
theorem B2084573 : Blo 1389514 2084573 := bbase (se 3 (by rfl) ⟨390857, by rfl⟩ : syracuseStep 2084573 = 781715) (by norm_num)
theorem B2346725 : Blo 1389514 2346725 := bbase (se 4 (by rfl) ⟨220005, by rfl⟩ : syracuseStep 2346725 = 440011) (by norm_num)
theorem B2084597 : Blo 1389514 2084597 := bbase (se 5 (by rfl) ⟨97715, by rfl⟩ : syracuseStep 2084597 = 195431) (by norm_num)
theorem B2084621 : Blo 1389514 2084621 := bbase (se 3 (by rfl) ⟨390866, by rfl⟩ : syracuseStep 2084621 = 781733) (by norm_num)
theorem B2084645 : Blo 1389514 2084645 := bbase (se 4 (by rfl) ⟨195435, by rfl⟩ : syracuseStep 2084645 = 390871) (by norm_num)
theorem B5279525 : Blo 1389514 5279525 := bbase (se 4 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 5279525 = 989911) (by norm_num)
theorem B2084669 : Blo 1389514 2084669 := bbase (se 3 (by rfl) ⟨390875, by rfl⟩ : syracuseStep 2084669 = 781751) (by norm_num)
theorem B2084693 : Blo 1389514 2084693 := bbase (se 9 (by rfl) ⟨6107, by rfl⟩ : syracuseStep 2084693 = 12215) (by norm_num)
theorem B2346853 : Blo 1389514 2346853 := bbase (se 4 (by rfl) ⟨220017, by rfl⟩ : syracuseStep 2346853 = 440035) (by norm_num)
theorem B2084717 : Blo 1389514 2084717 := bbase (se 3 (by rfl) ⟨390884, by rfl⟩ : syracuseStep 2084717 = 781769) (by norm_num)
theorem B2084741 : Blo 1389514 2084741 := bbase (se 4 (by rfl) ⟨195444, by rfl⟩ : syracuseStep 2084741 = 390889) (by norm_num)
theorem B2084765 : Blo 1389514 2084765 := bbase (se 3 (by rfl) ⟨390893, by rfl⟩ : syracuseStep 2084765 = 781787) (by norm_num)
theorem B4689845 : Blo 1389514 4689845 := bbase (se 5 (by rfl) ⟨219836, by rfl⟩ : syracuseStep 4689845 = 439673) (by norm_num)
theorem B2084789 : Blo 1389514 2084789 := bbase (se 5 (by rfl) ⟨97724, by rfl⟩ : syracuseStep 2084789 = 195449) (by norm_num)
theorem B2346941 : Blo 1389514 2346941 := bbase (se 3 (by rfl) ⟨440051, by rfl⟩ : syracuseStep 2346941 = 880103) (by norm_num)
theorem B2379709 : Blo 1389514 2379709 := bbase (se 3 (by rfl) ⟨446195, by rfl⟩ : syracuseStep 2379709 = 892391) (by norm_num)
theorem B2084813 : Blo 1389514 2084813 := bbase (se 3 (by rfl) ⟨390902, by rfl⟩ : syracuseStep 2084813 = 781805) (by norm_num)
theorem B2084837 : Blo 1389514 2084837 := bbase (se 4 (by rfl) ⟨195453, by rfl⟩ : syracuseStep 2084837 = 390907) (by norm_num)
theorem B3518437 : Blo 1389514 3518437 := bbase (se 4 (by rfl) ⟨329853, by rfl⟩ : syracuseStep 3518437 = 659707) (by norm_num)
theorem B2084861 : Blo 1389514 2084861 := bbase (se 3 (by rfl) ⟨390911, by rfl⟩ : syracuseStep 2084861 = 781823) (by norm_num)
theorem B2969597 : Blo 1389514 2969597 := bbase (se 3 (by rfl) ⟨556799, by rfl⟩ : syracuseStep 2969597 = 1113599) (by norm_num)
theorem B2084885 : Blo 1389514 2084885 := bbase (se 6 (by rfl) ⟨48864, by rfl⟩ : syracuseStep 2084885 = 97729) (by norm_num)
theorem B2084909 : Blo 1389514 2084909 := bbase (se 3 (by rfl) ⟨390920, by rfl⟩ : syracuseStep 2084909 = 781841) (by norm_num)
theorem B2347069 : Blo 1389514 2347069 := bbase (se 3 (by rfl) ⟨440075, by rfl⟩ : syracuseStep 2347069 = 880151) (by norm_num)
theorem B2084933 : Blo 1389514 2084933 := bbase (se 4 (by rfl) ⟨195462, by rfl⟩ : syracuseStep 2084933 = 390925) (by norm_num)
theorem B5279813 : Blo 1389514 5279813 := bbase (se 4 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 5279813 = 989965) (by norm_num)
theorem B3518549 : Blo 1389514 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B2084957 : Blo 1389514 2084957 := bbase (se 3 (by rfl) ⟨390929, by rfl⟩ : syracuseStep 2084957 = 781859) (by norm_num)
theorem B2084981 : Blo 1389514 2084981 := bbase (se 5 (by rfl) ⟨97733, by rfl⟩ : syracuseStep 2084981 = 195467) (by norm_num)
theorem B1978501 : Blo 1389514 1978501 := bbase (se 4 (by rfl) ⟨185484, by rfl⟩ : syracuseStep 1978501 = 370969) (by norm_num)
theorem B2085005 : Blo 1389514 2085005 := bbase (se 3 (by rfl) ⟨390938, by rfl⟩ : syracuseStep 2085005 = 781877) (by norm_num)
theorem B2969741 : Blo 1389514 2969741 := bbase (se 3 (by rfl) ⟨556826, by rfl⟩ : syracuseStep 2969741 = 1113653) (by norm_num)
theorem B2347157 : Blo 1389514 2347157 := bbase (se 6 (by rfl) ⟨55011, by rfl⟩ : syracuseStep 2347157 = 110023) (by norm_num)
theorem B2085029 : Blo 1389514 2085029 := bbase (se 4 (by rfl) ⟨195471, by rfl⟩ : syracuseStep 2085029 = 390943) (by norm_num)
theorem B2085053 : Blo 1389514 2085053 := bbase (se 3 (by rfl) ⟨390947, by rfl⟩ : syracuseStep 2085053 = 781895) (by norm_num)
theorem B2085077 : Blo 1389514 2085077 := bbase (se 7 (by rfl) ⟨24434, by rfl⟩ : syracuseStep 2085077 = 48869) (by norm_num)
theorem B1978597 : Blo 1389514 1978597 := bbase (se 4 (by rfl) ⟨185493, by rfl⟩ : syracuseStep 1978597 = 370987) (by norm_num)
theorem B2085101 : Blo 1389514 2085101 := bbase (se 3 (by rfl) ⟨390956, by rfl⟩ : syracuseStep 2085101 = 781913) (by norm_num)
theorem B2085125 : Blo 1389514 2085125 := bbase (se 4 (by rfl) ⟨195480, by rfl⟩ : syracuseStep 2085125 = 390961) (by norm_num)
theorem B3518741 : Blo 1389514 3518741 := bbase (se 6 (by rfl) ⟨82470, by rfl⟩ : syracuseStep 3518741 = 164941) (by norm_num)
theorem B2347285 : Blo 1389514 2347285 := bbase (se 6 (by rfl) ⟨55014, by rfl⟩ : syracuseStep 2347285 = 110029) (by norm_num)
theorem B2085149 : Blo 1389514 2085149 := bbase (se 3 (by rfl) ⟨390965, by rfl⟩ : syracuseStep 2085149 = 781931) (by norm_num)
theorem B2085173 : Blo 1389514 2085173 := bbase (se 5 (by rfl) ⟨97742, by rfl⟩ : syracuseStep 2085173 = 195485) (by norm_num)
theorem B2085197 : Blo 1389514 2085197 := bbase (se 3 (by rfl) ⟨390974, by rfl⟩ : syracuseStep 2085197 = 781949) (by norm_num)
theorem B4690277 : Blo 1389514 4690277 := bbase (se 4 (by rfl) ⟨439713, by rfl⟩ : syracuseStep 4690277 = 879427) (by norm_num)
theorem B2085221 : Blo 1389514 2085221 := bbase (se 4 (by rfl) ⟨195489, by rfl⟩ : syracuseStep 2085221 = 390979) (by norm_num)
theorem B2347373 : Blo 1389514 2347373 := bbase (se 3 (by rfl) ⟨440132, by rfl⟩ : syracuseStep 2347373 = 880265) (by norm_num)
theorem B3051893 : Blo 1389514 3051893 := bbase (se 5 (by rfl) ⟨143057, by rfl⟩ : syracuseStep 3051893 = 286115) (by norm_num)
theorem B2085245 : Blo 1389514 2085245 := bbase (se 3 (by rfl) ⟨390983, by rfl⟩ : syracuseStep 2085245 = 781967) (by norm_num)
theorem B1880453 : Blo 1389514 1880453 := bbase (se 4 (by rfl) ⟨176292, by rfl⟩ : syracuseStep 1880453 = 352585) (by norm_num)
theorem B2085269 : Blo 1389514 2085269 := bbase (se 6 (by rfl) ⟨48873, by rfl⟩ : syracuseStep 2085269 = 97747) (by norm_num)
theorem B3338653 : Blo 1389514 3338653 := bbase (se 3 (by rfl) ⟨625997, by rfl⟩ : syracuseStep 3338653 = 1251995) (by norm_num)
theorem B1905061 : Blo 1389514 1905061 := bbase (se 4 (by rfl) ⟨178599, by rfl⟩ : syracuseStep 1905061 = 357199) (by norm_num)
theorem B2085293 : Blo 1389514 2085293 := bbase (se 3 (by rfl) ⟨390992, by rfl⟩ : syracuseStep 2085293 = 781985) (by norm_num)
theorem B3568045 : Blo 1389514 3568045 := bbase (se 3 (by rfl) ⟨669008, by rfl⟩ : syracuseStep 3568045 = 1338017) (by norm_num)
theorem B1880501 : Blo 1389514 1880501 := bbase (se 5 (by rfl) ⟨88148, by rfl⟩ : syracuseStep 1880501 = 176297) (by norm_num)
theorem B1585597 : Blo 1389514 1585597 := bbase (se 3 (by rfl) ⟨297299, by rfl⟩ : syracuseStep 1585597 = 594599) (by norm_num)
theorem B2085317 : Blo 1389514 2085317 := bbase (se 4 (by rfl) ⟨195498, by rfl⟩ : syracuseStep 2085317 = 390997) (by norm_num)
theorem B2085341 : Blo 1389514 2085341 := bbase (se 3 (by rfl) ⟨391001, by rfl⟩ : syracuseStep 2085341 = 782003) (by norm_num)
theorem B2347501 : Blo 1389514 2347501 := bbase (se 3 (by rfl) ⟨440156, by rfl⟩ : syracuseStep 2347501 = 880313) (by norm_num)
theorem B2085365 : Blo 1389514 2085365 := bbase (se 5 (by rfl) ⟨97751, by rfl⟩ : syracuseStep 2085365 = 195503) (by norm_num)
theorem B2970101 : Blo 1389514 2970101 := bbase (se 5 (by rfl) ⟨139223, by rfl⟩ : syracuseStep 2970101 = 278447) (by norm_num)
theorem B4452869 : Blo 1389514 4452869 := bbase (se 4 (by rfl) ⟨417456, by rfl⟩ : syracuseStep 4452869 = 834913) (by norm_num)
theorem B2085389 : Blo 1389514 2085389 := bbase (se 3 (by rfl) ⟨391010, by rfl⟩ : syracuseStep 2085389 = 782021) (by norm_num)
theorem B1692181 : Blo 1389514 1692181 := bbase (se 6 (by rfl) ⟨39660, by rfl⟩ : syracuseStep 1692181 = 79321) (by norm_num)
theorem B2085413 : Blo 1389514 2085413 := bbase (se 4 (by rfl) ⟨195507, by rfl⟩ : syracuseStep 2085413 = 391015) (by norm_num)
theorem B2085437 : Blo 1389514 2085437 := bbase (se 3 (by rfl) ⟨391019, by rfl⟩ : syracuseStep 2085437 = 782039) (by norm_num)
theorem B2347589 : Blo 1389514 2347589 := bbase (se 4 (by rfl) ⟨220086, by rfl⟩ : syracuseStep 2347589 = 440173) (by norm_num)
theorem B2085461 : Blo 1389514 2085461 := bbase (se 8 (by rfl) ⟨12219, by rfl⟩ : syracuseStep 2085461 = 24439) (by norm_num)
theorem B10564181 : Blo 1389514 10564181 := bbase (se 8 (by rfl) ⟨61899, by rfl⟩ : syracuseStep 10564181 = 123799) (by norm_num)
theorem B3519085 : Blo 1389514 3519085 := bbase (se 3 (by rfl) ⟨659828, by rfl⟩ : syracuseStep 3519085 = 1319657) (by norm_num)
theorem B2085485 : Blo 1389514 2085485 := bbase (se 3 (by rfl) ⟨391028, by rfl⟩ : syracuseStep 2085485 = 782057) (by norm_num)
theorem B7041653 : Blo 1389514 7041653 := bbase (se 5 (by rfl) ⟨330077, by rfl⟩ : syracuseStep 7041653 = 660155) (by norm_num)
theorem B2085509 : Blo 1389514 2085509 := bbase (se 4 (by rfl) ⟨195516, by rfl⟩ : syracuseStep 2085509 = 391033) (by norm_num)
theorem B3961477 : Blo 1389514 3961477 := bbase (se 4 (by rfl) ⟨371388, by rfl⟩ : syracuseStep 3961477 = 742777) (by norm_num)
theorem B19075733 : Blo 1389514 19075733 := bbase (se 6 (by rfl) ⟨447087, by rfl⟩ : syracuseStep 19075733 = 894175) (by norm_num)
theorem B5640853 : Blo 1389514 5640853 := bbase (se 6 (by rfl) ⟨132207, by rfl⟩ : syracuseStep 5640853 = 264415) (by norm_num)
theorem B2085533 : Blo 1389514 2085533 := bbase (se 3 (by rfl) ⟨391037, by rfl⟩ : syracuseStep 2085533 = 782075) (by norm_num)
theorem B2085557 : Blo 1389514 2085557 := bbase (se 5 (by rfl) ⟨97760, by rfl⟩ : syracuseStep 2085557 = 195521) (by norm_num)
theorem B2347717 : Blo 1389514 2347717 := bbase (se 4 (by rfl) ⟨220098, by rfl⟩ : syracuseStep 2347717 = 440197) (by norm_num)
theorem B2085581 : Blo 1389514 2085581 := bbase (se 3 (by rfl) ⟨391046, by rfl⟩ : syracuseStep 2085581 = 782093) (by norm_num)
theorem B1979093 : Blo 1389514 1979093 := bbase (se 7 (by rfl) ⟨23192, by rfl⟩ : syracuseStep 1979093 = 46385) (by norm_num)
theorem B3519197 : Blo 1389514 3519197 := bbase (se 3 (by rfl) ⟨659849, by rfl⟩ : syracuseStep 3519197 = 1319699) (by norm_num)
theorem B2085605 : Blo 1389514 2085605 := bbase (se 4 (by rfl) ⟨195525, by rfl⟩ : syracuseStep 2085605 = 391051) (by norm_num)
theorem B2085629 : Blo 1389514 2085629 := bbase (se 3 (by rfl) ⟨391055, by rfl⟩ : syracuseStep 2085629 = 782111) (by norm_num)
theorem B4690709 : Blo 1389514 4690709 := bbase (se 6 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 4690709 = 219877) (by norm_num)
theorem B2085653 : Blo 1389514 2085653 := bbase (se 6 (by rfl) ⟨48882, by rfl⟩ : syracuseStep 2085653 = 97765) (by norm_num)
theorem B2347805 : Blo 1389514 2347805 := bbase (se 3 (by rfl) ⟨440213, by rfl⟩ : syracuseStep 2347805 = 880427) (by norm_num)
theorem B2085677 : Blo 1389514 2085677 := bbase (se 3 (by rfl) ⟨391064, by rfl⟩ : syracuseStep 2085677 = 782129) (by norm_num)
theorem B2085701 : Blo 1389514 2085701 := bbase (se 4 (by rfl) ⟨195534, by rfl⟩ : syracuseStep 2085701 = 391069) (by norm_num)
theorem B2085725 : Blo 1389514 2085725 := bbase (se 3 (by rfl) ⟨391073, by rfl⟩ : syracuseStep 2085725 = 782147) (by norm_num)
theorem B1586017 : Blo 1389514 1586017 := bbase (se 2 (by rfl) ⟨594756, by rfl⟩ : syracuseStep 1586017 = 1189513) (by norm_num)
theorem B2085749 : Blo 1389514 2085749 := bbase (se 5 (by rfl) ⟨97769, by rfl⟩ : syracuseStep 2085749 = 195539) (by norm_num)
theorem B2085773 : Blo 1389514 2085773 := bbase (se 3 (by rfl) ⟨391082, by rfl⟩ : syracuseStep 2085773 = 782165) (by norm_num)
theorem B3519389 : Blo 1389514 3519389 := bbase (se 3 (by rfl) ⟨659885, by rfl⟩ : syracuseStep 3519389 = 1319771) (by norm_num)
theorem B2347933 : Blo 1389514 2347933 := bbase (se 3 (by rfl) ⟨440237, by rfl⟩ : syracuseStep 2347933 = 880475) (by norm_num)
theorem B2085797 : Blo 1389514 2085797 := bbase (se 4 (by rfl) ⟨195543, by rfl⟩ : syracuseStep 2085797 = 391087) (by norm_num)
theorem B2085821 : Blo 1389514 2085821 := bbase (se 3 (by rfl) ⟨391091, by rfl⟩ : syracuseStep 2085821 = 782183) (by norm_num)
theorem B2085845 : Blo 1389514 2085845 := bbase (se 7 (by rfl) ⟨24443, by rfl⟩ : syracuseStep 2085845 = 48887) (by norm_num)
theorem B14275541 : Blo 1389514 14275541 := bbase (se 7 (by rfl) ⟨167291, by rfl⟩ : syracuseStep 14275541 = 334583) (by norm_num)
theorem B2085869 : Blo 1389514 2085869 := bbase (se 3 (by rfl) ⟨391100, by rfl⟩ : syracuseStep 2085869 = 782201) (by norm_num)
theorem B10556405 : Blo 1389514 10556405 := bbase (se 5 (by rfl) ⟨494831, by rfl⟩ : syracuseStep 10556405 = 989663) (by norm_num)
theorem B2348021 : Blo 1389514 2348021 := bbase (se 5 (by rfl) ⟨110063, by rfl⟩ : syracuseStep 2348021 = 220127) (by norm_num)
theorem B3339269 : Blo 1389514 3339269 := bbase (se 4 (by rfl) ⟨313056, by rfl⟩ : syracuseStep 3339269 = 626113) (by norm_num)
theorem B2085893 : Blo 1389514 2085893 := bbase (se 4 (by rfl) ⟨195552, by rfl⟩ : syracuseStep 2085893 = 391105) (by norm_num)
theorem B9638933 : Blo 1389514 9638933 := bbase (se 6 (by rfl) ⟨225912, by rfl⟩ : syracuseStep 9638933 = 451825) (by norm_num)
theorem B4756501 : Blo 1389514 4756501 := bbase (se 6 (by rfl) ⟨111480, by rfl⟩ : syracuseStep 4756501 = 222961) (by norm_num)
theorem B2085917 : Blo 1389514 2085917 := bbase (se 3 (by rfl) ⟨391109, by rfl⟩ : syracuseStep 2085917 = 782219) (by norm_num)
theorem B2085941 : Blo 1389514 2085941 := bbase (se 5 (by rfl) ⟨97778, by rfl⟩ : syracuseStep 2085941 = 195557) (by norm_num)
theorem B2085965 : Blo 1389514 2085965 := bbase (se 3 (by rfl) ⟨391118, by rfl⟩ : syracuseStep 2085965 = 782237) (by norm_num)
theorem B2085989 : Blo 1389514 2085989 := bbase (se 4 (by rfl) ⟨195561, by rfl⟩ : syracuseStep 2085989 = 391123) (by norm_num)
theorem B2348149 : Blo 1389514 2348149 := bbase (se 5 (by rfl) ⟨110069, by rfl⟩ : syracuseStep 2348149 = 220139) (by norm_num)
theorem B2086013 : Blo 1389514 2086013 := bbase (se 3 (by rfl) ⟨391127, by rfl⟩ : syracuseStep 2086013 = 782255) (by norm_num)
theorem B2086037 : Blo 1389514 2086037 := bbase (se 6 (by rfl) ⟨48891, by rfl⟩ : syracuseStep 2086037 = 97783) (by norm_num)
theorem B3126437 : Blo 1389514 3126437 := bbase (se 4 (by rfl) ⟨293103, by rfl⟩ : syracuseStep 3126437 = 586207) (by norm_num)
theorem B2086061 : Blo 1389514 2086061 := bbase (se 3 (by rfl) ⟨391136, by rfl⟩ : syracuseStep 2086061 = 782273) (by norm_num)
theorem B3339461 : Blo 1389514 3339461 := bbase (se 4 (by rfl) ⟨313074, by rfl⟩ : syracuseStep 3339461 = 626149) (by norm_num)
theorem B4691141 : Blo 1389514 4691141 := bbase (se 4 (by rfl) ⟨439794, by rfl⟩ : syracuseStep 4691141 = 879589) (by norm_num)
theorem B2086085 : Blo 1389514 2086085 := bbase (se 4 (by rfl) ⟨195570, by rfl⟩ : syracuseStep 2086085 = 391141) (by norm_num)
theorem B2086109 : Blo 1389514 2086109 := bbase (se 3 (by rfl) ⟨391145, by rfl⟩ : syracuseStep 2086109 = 782291) (by norm_num)
theorem B1504481 : Blo 1389514 1504481 := bbase (se 2 (by rfl) ⟨564180, by rfl⟩ : syracuseStep 1504481 = 1128361) (by norm_num)
theorem B5280997 : Blo 1389514 5280997 := bbase (se 4 (by rfl) ⟨495093, by rfl⟩ : syracuseStep 5280997 = 990187) (by norm_num)
theorem B3126509 : Blo 1389514 3126509 := bbase (se 3 (by rfl) ⟨586220, by rfl⟩ : syracuseStep 3126509 = 1172441) (by norm_num)
theorem B3519733 : Blo 1389514 3519733 := bbase (se 5 (by rfl) ⟨164987, by rfl⟩ : syracuseStep 3519733 = 329975) (by norm_num)
theorem B2086133 : Blo 1389514 2086133 := bbase (se 5 (by rfl) ⟨97787, by rfl⟩ : syracuseStep 2086133 = 195575) (by norm_num)
theorem B1979645 : Blo 1389514 1979645 := bbase (se 3 (by rfl) ⟨371183, by rfl⟩ : syracuseStep 1979645 = 742367) (by norm_num)
theorem B2086157 : Blo 1389514 2086157 := bbase (se 3 (by rfl) ⟨391154, by rfl⟩ : syracuseStep 2086157 = 782309) (by norm_num)
theorem B2086181 : Blo 1389514 2086181 := bbase (se 4 (by rfl) ⟨195579, by rfl⟩ : syracuseStep 2086181 = 391159) (by norm_num)
theorem B3126581 : Blo 1389514 3126581 := bbase (se 5 (by rfl) ⟨146558, by rfl⟩ : syracuseStep 3126581 = 293117) (by norm_num)
theorem B2086205 : Blo 1389514 2086205 := bbase (se 3 (by rfl) ⟨391163, by rfl⟩ : syracuseStep 2086205 = 782327) (by norm_num)
theorem B2086229 : Blo 1389514 2086229 := bbase (se 15 (by rfl) ⟨95, by rfl⟩ : syracuseStep 2086229 = 191) (by norm_num)
theorem B3519845 : Blo 1389514 3519845 := bbase (se 4 (by rfl) ⟨329985, by rfl⟩ : syracuseStep 3519845 = 659971) (by norm_num)
theorem B2086253 : Blo 1389514 2086253 := bbase (se 3 (by rfl) ⟨391172, by rfl⟩ : syracuseStep 2086253 = 782345) (by norm_num)
theorem B2970989 : Blo 1389514 2970989 := bbase (se 3 (by rfl) ⟨557060, by rfl⟩ : syracuseStep 2970989 = 1114121) (by norm_num)
theorem B3126653 : Blo 1389514 3126653 := bbase (se 3 (by rfl) ⟨586247, by rfl⟩ : syracuseStep 3126653 = 1172495) (by norm_num)
theorem B2086277 : Blo 1389514 2086277 := bbase (se 4 (by rfl) ⟨195588, by rfl⟩ : syracuseStep 2086277 = 391177) (by norm_num)
theorem B2086301 : Blo 1389514 2086301 := bbase (se 3 (by rfl) ⟨391181, by rfl⟩ : syracuseStep 2086301 = 782363) (by norm_num)
theorem B1783201 : Blo 1389514 1783201 := bbase (se 2 (by rfl) ⟨668700, by rfl⟩ : syracuseStep 1783201 = 1337401) (by norm_num)
theorem B2676149 : Blo 1389514 2676149 := bbase (se 5 (by rfl) ⟨125444, by rfl⟩ : syracuseStep 2676149 = 250889) (by norm_num)
theorem B2086325 : Blo 1389514 2086325 := bbase (se 5 (by rfl) ⟨97796, by rfl⟩ : syracuseStep 2086325 = 195593) (by norm_num)
theorem B3126725 : Blo 1389514 3126725 := bbase (se 4 (by rfl) ⟨293130, by rfl⟩ : syracuseStep 3126725 = 586261) (by norm_num)
theorem B2086349 : Blo 1389514 2086349 := bbase (se 3 (by rfl) ⟨391190, by rfl⟩ : syracuseStep 2086349 = 782381) (by norm_num)
theorem B5936597 : Blo 1389514 5936597 := bbase (se 7 (by rfl) ⟨69569, by rfl⟩ : syracuseStep 5936597 = 139139) (by norm_num)
theorem B2086373 : Blo 1389514 2086373 := bbase (se 4 (by rfl) ⟨195597, by rfl⟩ : syracuseStep 2086373 = 391195) (by norm_num)
theorem B2086397 : Blo 1389514 2086397 := bbase (se 3 (by rfl) ⟨391199, by rfl⟩ : syracuseStep 2086397 = 782399) (by norm_num)
theorem B3126797 : Blo 1389514 3126797 := bbase (se 3 (by rfl) ⟨586274, by rfl⟩ : syracuseStep 3126797 = 1172549) (by norm_num)
theorem B2086421 : Blo 1389514 2086421 := bbase (se 6 (by rfl) ⟨48900, by rfl⟩ : syracuseStep 2086421 = 97801) (by norm_num)
theorem B5281301 : Blo 1389514 5281301 := bbase (se 6 (by rfl) ⟨123780, by rfl⟩ : syracuseStep 5281301 = 247561) (by norm_num)
theorem B3520037 : Blo 1389514 3520037 := bbase (se 4 (by rfl) ⟨330003, by rfl⟩ : syracuseStep 3520037 = 660007) (by norm_num)
theorem B2086445 : Blo 1389514 2086445 := bbase (se 3 (by rfl) ⟨391208, by rfl⟩ : syracuseStep 2086445 = 782417) (by norm_num)
theorem B1758773 : Blo 1389514 1758773 := bbase (se 5 (by rfl) ⟨82442, by rfl⟩ : syracuseStep 1758773 = 164885) (by norm_num)
theorem B2086469 : Blo 1389514 2086469 := bbase (se 4 (by rfl) ⟨195606, by rfl⟩ : syracuseStep 2086469 = 391213) (by norm_num)
theorem B3126869 : Blo 1389514 3126869 := bbase (se 8 (by rfl) ⟨18321, by rfl⟩ : syracuseStep 3126869 = 36643) (by norm_num)
theorem B2086493 : Blo 1389514 2086493 := bbase (se 3 (by rfl) ⟨391217, by rfl⟩ : syracuseStep 2086493 = 782435) (by norm_num)
theorem B2971237 : Blo 1389514 2971237 := bbase (se 4 (by rfl) ⟨278553, by rfl⟩ : syracuseStep 2971237 = 557107) (by norm_num)
theorem B1758829 : Blo 1389514 1758829 := bbase (se 3 (by rfl) ⟨329780, by rfl⟩ : syracuseStep 1758829 = 659561) (by norm_num)
theorem B4691573 : Blo 1389514 4691573 := bbase (se 5 (by rfl) ⟨219917, by rfl⟩ : syracuseStep 4691573 = 439835) (by norm_num)
theorem B2086517 : Blo 1389514 2086517 := bbase (se 5 (by rfl) ⟨97805, by rfl⟩ : syracuseStep 2086517 = 195611) (by norm_num)
theorem B2086541 : Blo 1389514 2086541 := bbase (se 3 (by rfl) ⟨391226, by rfl⟩ : syracuseStep 2086541 = 782453) (by norm_num)
theorem B3126941 : Blo 1389514 3126941 := bbase (se 3 (by rfl) ⟨586301, by rfl⟩ : syracuseStep 3126941 = 1172603) (by norm_num)
theorem B2086565 : Blo 1389514 2086565 := bbase (se 4 (by rfl) ⟨195615, by rfl⟩ : syracuseStep 2086565 = 391231) (by norm_num)
theorem B2086589 : Blo 1389514 2086589 := bbase (se 3 (by rfl) ⟨391235, by rfl⟩ : syracuseStep 2086589 = 782471) (by norm_num)
theorem B1758925 : Blo 1389514 1758925 := bbase (se 3 (by rfl) ⟨329798, by rfl⟩ : syracuseStep 1758925 = 659597) (by norm_num)
theorem B2086613 : Blo 1389514 2086613 := bbase (se 7 (by rfl) ⟨24452, by rfl⟩ : syracuseStep 2086613 = 48905) (by norm_num)
theorem B3127013 : Blo 1389514 3127013 := bbase (se 4 (by rfl) ⟨293157, by rfl⟩ : syracuseStep 3127013 = 586315) (by norm_num)
theorem B2086637 : Blo 1389514 2086637 := bbase (se 3 (by rfl) ⟨391244, by rfl⟩ : syracuseStep 2086637 = 782489) (by norm_num)
theorem B5936885 : Blo 1389514 5936885 := bbase (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) (by norm_num)
theorem B3340037 : Blo 1389514 3340037 := bbase (se 4 (by rfl) ⟨313128, by rfl⟩ : syracuseStep 3340037 = 626257) (by norm_num)
theorem B2086661 : Blo 1389514 2086661 := bbase (se 4 (by rfl) ⟨195624, by rfl⟩ : syracuseStep 2086661 = 391249) (by norm_num)
theorem B2086685 : Blo 1389514 2086685 := bbase (se 3 (by rfl) ⟨391253, by rfl⟩ : syracuseStep 2086685 = 782507) (by norm_num)
theorem B5011237 : Blo 1389514 5011237 := bbase (se 4 (by rfl) ⟨469803, by rfl⟩ : syracuseStep 5011237 = 939607) (by norm_num)
theorem B3127085 : Blo 1389514 3127085 := bbase (se 3 (by rfl) ⟨586328, by rfl⟩ : syracuseStep 3127085 = 1172657) (by norm_num)
theorem B2086709 : Blo 1389514 2086709 := bbase (se 5 (by rfl) ⟨97814, by rfl⟩ : syracuseStep 2086709 = 195629) (by norm_num)
theorem B2086733 : Blo 1389514 2086733 := bbase (se 3 (by rfl) ⟨391262, by rfl⟩ : syracuseStep 2086733 = 782525) (by norm_num)
theorem B2086757 : Blo 1389514 2086757 := bbase (se 4 (by rfl) ⟨195633, by rfl⟩ : syracuseStep 2086757 = 391267) (by norm_num)
theorem B3127157 : Blo 1389514 3127157 := bbase (se 5 (by rfl) ⟨146585, by rfl⟩ : syracuseStep 3127157 = 293171) (by norm_num)
theorem B1759097 : Blo 1389514 1759097 := bbase (se 2 (by rfl) ⟨659661, by rfl⟩ : syracuseStep 1759097 = 1319323) (by norm_num)
theorem B3520381 : Blo 1389514 3520381 := bbase (se 3 (by rfl) ⟨660071, by rfl⟩ : syracuseStep 3520381 = 1320143) (by norm_num)
theorem B2086781 : Blo 1389514 2086781 := bbase (se 3 (by rfl) ⟨391271, by rfl⟩ : syracuseStep 2086781 = 782543) (by norm_num)
theorem B7042949 : Blo 1389514 7042949 := bbase (se 4 (by rfl) ⟨660276, by rfl⟩ : syracuseStep 7042949 = 1320553) (by norm_num)
theorem B2086805 : Blo 1389514 2086805 := bbase (se 6 (by rfl) ⟨48909, by rfl⟩ : syracuseStep 2086805 = 97819) (by norm_num)
theorem B2086829 : Blo 1389514 2086829 := bbase (se 3 (by rfl) ⟨391280, by rfl⟩ : syracuseStep 2086829 = 782561) (by norm_num)
theorem B1759153 : Blo 1389514 1759153 := bbase (se 2 (by rfl) ⟨659682, by rfl⟩ : syracuseStep 1759153 = 1319365) (by norm_num)
theorem B3127229 : Blo 1389514 3127229 := bbase (se 3 (by rfl) ⟨586355, by rfl⟩ : syracuseStep 3127229 = 1172711) (by norm_num)
theorem B2086853 : Blo 1389514 2086853 := bbase (se 4 (by rfl) ⟨195642, by rfl⟩ : syracuseStep 2086853 = 391285) (by norm_num)
theorem B2086877 : Blo 1389514 2086877 := bbase (se 3 (by rfl) ⟨391289, by rfl⟩ : syracuseStep 2086877 = 782579) (by norm_num)
theorem B3520493 : Blo 1389514 3520493 := bbase (se 3 (by rfl) ⟨660092, by rfl⟩ : syracuseStep 3520493 = 1320185) (by norm_num)
theorem B1980397 : Blo 1389514 1980397 := bbase (se 3 (by rfl) ⟨371324, by rfl⟩ : syracuseStep 1980397 = 742649) (by norm_num)
theorem B2086901 : Blo 1389514 2086901 := bbase (se 5 (by rfl) ⟨97823, by rfl⟩ : syracuseStep 2086901 = 195647) (by norm_num)
theorem B3127301 : Blo 1389514 3127301 := bbase (se 4 (by rfl) ⟨293184, by rfl⟩ : syracuseStep 3127301 = 586369) (by norm_num)
theorem B2086925 : Blo 1389514 2086925 := bbase (se 3 (by rfl) ⟨391298, by rfl⟩ : syracuseStep 2086925 = 782597) (by norm_num)
theorem B1759249 : Blo 1389514 1759249 := bbase (se 2 (by rfl) ⟨659718, by rfl⟩ : syracuseStep 1759249 = 1319437) (by norm_num)
theorem B4692005 : Blo 1389514 4692005 := bbase (se 4 (by rfl) ⟨439875, by rfl⟩ : syracuseStep 4692005 = 879751) (by norm_num)
theorem B2086949 : Blo 1389514 2086949 := bbase (se 4 (by rfl) ⟨195651, by rfl⟩ : syracuseStep 2086949 = 391303) (by norm_num)
theorem B2086973 : Blo 1389514 2086973 := bbase (se 3 (by rfl) ⟨391307, by rfl⟩ : syracuseStep 2086973 = 782615) (by norm_num)
theorem B3127373 : Blo 1389514 3127373 := bbase (se 3 (by rfl) ⟨586382, by rfl⟩ : syracuseStep 3127373 = 1172765) (by norm_num)
theorem B2086997 : Blo 1389514 2086997 := bbase (se 8 (by rfl) ⟨12228, by rfl⟩ : syracuseStep 2086997 = 24457) (by norm_num)
theorem B2971741 : Blo 1389514 2971741 := bbase (se 3 (by rfl) ⟨557201, by rfl⟩ : syracuseStep 2971741 = 1114403) (by norm_num)
theorem B2087021 : Blo 1389514 2087021 := bbase (se 3 (by rfl) ⟨391316, by rfl⟩ : syracuseStep 2087021 = 782633) (by norm_num)
theorem B3340421 : Blo 1389514 3340421 := bbase (se 4 (by rfl) ⟨313164, by rfl⟩ : syracuseStep 3340421 = 626329) (by norm_num)
theorem B2087045 : Blo 1389514 2087045 := bbase (se 4 (by rfl) ⟨195660, by rfl⟩ : syracuseStep 2087045 = 391321) (by norm_num)
theorem B3127445 : Blo 1389514 3127445 := bbase (se 6 (by rfl) ⟨73299, by rfl⟩ : syracuseStep 3127445 = 146599) (by norm_num)
theorem B7919765 : Blo 1389514 7919765 := bbase (se 6 (by rfl) ⟨185619, by rfl⟩ : syracuseStep 7919765 = 371239) (by norm_num)
theorem B2087069 : Blo 1389514 2087069 := bbase (se 3 (by rfl) ⟨391325, by rfl⟩ : syracuseStep 2087069 = 782651) (by norm_num)
theorem B3520685 : Blo 1389514 3520685 := bbase (se 3 (by rfl) ⟨660128, by rfl⟩ : syracuseStep 3520685 = 1320257) (by norm_num)
theorem B2087093 : Blo 1389514 2087093 := bbase (se 5 (by rfl) ⟨97832, by rfl⟩ : syracuseStep 2087093 = 195665) (by norm_num)
theorem B1759421 : Blo 1389514 1759421 := bbase (se 3 (by rfl) ⟨329891, by rfl⟩ : syracuseStep 1759421 = 659783) (by norm_num)
theorem B2087117 : Blo 1389514 2087117 := bbase (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) (by norm_num)
theorem B3127517 : Blo 1389514 3127517 := bbase (se 3 (by rfl) ⟨586409, by rfl⟩ : syracuseStep 3127517 = 1172819) (by norm_num)
theorem B2087141 : Blo 1389514 2087141 := bbase (se 4 (by rfl) ⟨195669, by rfl⟩ : syracuseStep 2087141 = 391339) (by norm_num)
theorem B1759477 : Blo 1389514 1759477 := bbase (se 5 (by rfl) ⟨82475, by rfl⟩ : syracuseStep 1759477 = 164951) (by norm_num)
theorem B2087165 : Blo 1389514 2087165 := bbase (se 3 (by rfl) ⟨391343, by rfl⟩ : syracuseStep 2087165 = 782687) (by norm_num)
theorem B2087189 : Blo 1389514 2087189 := bbase (se 6 (by rfl) ⟨48918, by rfl⟩ : syracuseStep 2087189 = 97837) (by norm_num)
theorem B7035173 : Blo 1389514 7035173 := bbase (se 4 (by rfl) ⟨659547, by rfl⟩ : syracuseStep 7035173 = 1319095) (by norm_num)
theorem B3127589 : Blo 1389514 3127589 := bbase (se 4 (by rfl) ⟨293211, by rfl⟩ : syracuseStep 3127589 = 586423) (by norm_num)
theorem B2087213 : Blo 1389514 2087213 := bbase (se 3 (by rfl) ⟨391352, by rfl⟩ : syracuseStep 2087213 = 782705) (by norm_num)
theorem B2087237 : Blo 1389514 2087237 := bbase (se 4 (by rfl) ⟨195678, by rfl⟩ : syracuseStep 2087237 = 391357) (by norm_num)
theorem B1759573 : Blo 1389514 1759573 := bbase (se 10 (by rfl) ⟨2577, by rfl⟩ : syracuseStep 1759573 = 5155) (by norm_num)
theorem B2087261 : Blo 1389514 2087261 := bbase (se 3 (by rfl) ⟨391361, by rfl⟩ : syracuseStep 2087261 = 782723) (by norm_num)
theorem B3127661 : Blo 1389514 3127661 := bbase (se 3 (by rfl) ⟨586436, by rfl⟩ : syracuseStep 3127661 = 1172873) (by norm_num)
theorem B3127733 : Blo 1389514 3127733 := bbase (se 5 (by rfl) ⟨146612, by rfl⟩ : syracuseStep 3127733 = 293225) (by norm_num)
theorem B4692437 : Blo 1389514 4692437 := bbase (se 7 (by rfl) ⟨54989, by rfl⟩ : syracuseStep 4692437 = 109979) (by norm_num)
theorem B5937637 : Blo 1389514 5937637 := bbase (se 4 (by rfl) ⟨556653, by rfl⟩ : syracuseStep 5937637 = 1113307) (by norm_num)
theorem B1784305 : Blo 1389514 1784305 := bbase (se 2 (by rfl) ⟨669114, by rfl⟩ : syracuseStep 1784305 = 1338229) (by norm_num)
theorem B2226685 : Blo 1389514 2226685 := bbase (se 3 (by rfl) ⟨417503, by rfl⟩ : syracuseStep 2226685 = 835007) (by norm_num)
theorem B3127805 : Blo 1389514 3127805 := bbase (se 3 (by rfl) ⟨586463, by rfl⟩ : syracuseStep 3127805 = 1172927) (by norm_num)
theorem B1759745 : Blo 1389514 1759745 := bbase (se 2 (by rfl) ⟨659904, by rfl⟩ : syracuseStep 1759745 = 1319809) (by norm_num)
theorem B3521029 : Blo 1389514 3521029 := bbase (se 4 (by rfl) ⟨330096, by rfl⟩ : syracuseStep 3521029 = 660193) (by norm_num)
theorem B1759801 : Blo 1389514 1759801 := bbase (se 2 (by rfl) ⟨659925, by rfl⟩ : syracuseStep 1759801 = 1319851) (by norm_num)
theorem B1563205 : Blo 1389514 1563205 := bbase (se 4 (by rfl) ⟨146550, by rfl⟩ : syracuseStep 1563205 = 293101) (by norm_num)
theorem B3127877 : Blo 1389514 3127877 := bbase (se 4 (by rfl) ⟨293238, by rfl⟩ : syracuseStep 3127877 = 586477) (by norm_num)
theorem B1563241 : Blo 1389514 1563241 := bbase (se 2 (by rfl) ⟨586215, by rfl⟩ : syracuseStep 1563241 = 1172431) (by norm_num)
theorem B3521141 : Blo 1389514 3521141 := bbase (se 5 (by rfl) ⟨165053, by rfl⟩ : syracuseStep 3521141 = 330107) (by norm_num)
theorem B1563277 : Blo 1389514 1563277 := bbase (se 3 (by rfl) ⟨293114, by rfl⟩ : syracuseStep 1563277 = 586229) (by norm_num)
theorem B3127949 : Blo 1389514 3127949 := bbase (se 3 (by rfl) ⟨586490, by rfl⟩ : syracuseStep 3127949 = 1172981) (by norm_num)
theorem B1759897 : Blo 1389514 1759897 := bbase (se 2 (by rfl) ⟨659961, by rfl⟩ : syracuseStep 1759897 = 1319923) (by norm_num)
theorem B1563313 : Blo 1389514 1563313 := bbase (se 2 (by rfl) ⟨586242, by rfl⟩ : syracuseStep 1563313 = 1172485) (by norm_num)
theorem B1563349 : Blo 1389514 1563349 := bbase (se 7 (by rfl) ⟨18320, by rfl⟩ : syracuseStep 1563349 = 36641) (by norm_num)
theorem B9026261 : Blo 1389514 9026261 := bbase (se 7 (by rfl) ⟨105776, by rfl⟩ : syracuseStep 9026261 = 211553) (by norm_num)
theorem B3128021 : Blo 1389514 3128021 := bbase (se 7 (by rfl) ⟨36656, by rfl⟩ : syracuseStep 3128021 = 73313) (by norm_num)
theorem B4455125 : Blo 1389514 4455125 := bbase (se 7 (by rfl) ⟨52208, by rfl⟩ : syracuseStep 4455125 = 104417) (by norm_num)
theorem B6683381 : Blo 1389514 6683381 := bbase (se 5 (by rfl) ⟨313283, by rfl⟩ : syracuseStep 6683381 = 626567) (by norm_num)
theorem B1563385 : Blo 1389514 1563385 := bbase (se 2 (by rfl) ⟨586269, by rfl⟩ : syracuseStep 1563385 = 1172539) (by norm_num)
theorem B1981189 : Blo 1389514 1981189 := bbase (se 4 (by rfl) ⟨185736, by rfl⟩ : syracuseStep 1981189 = 371473) (by norm_num)
theorem B1563421 : Blo 1389514 1563421 := bbase (se 3 (by rfl) ⟨293141, by rfl⟩ : syracuseStep 1563421 = 586283) (by norm_num)
theorem B3128093 : Blo 1389514 3128093 := bbase (se 3 (by rfl) ⟨586517, by rfl⟩ : syracuseStep 3128093 = 1173035) (by norm_num)
theorem B3521333 : Blo 1389514 3521333 := bbase (se 5 (by rfl) ⟨165062, by rfl⟩ : syracuseStep 3521333 = 330125) (by norm_num)
theorem B1563457 : Blo 1389514 1563457 := bbase (se 2 (by rfl) ⟨586296, by rfl⟩ : syracuseStep 1563457 = 1172593) (by norm_num)
theorem B4225861 : Blo 1389514 4225861 := bbase (se 4 (by rfl) ⟨396174, by rfl⟩ : syracuseStep 4225861 = 792349) (by norm_num)
theorem B1760069 : Blo 1389514 1760069 := bbase (se 4 (by rfl) ⟨165006, by rfl⟩ : syracuseStep 1760069 = 330013) (by norm_num)
theorem B4455253 : Blo 1389514 4455253 := bbase (se 9 (by rfl) ⟨13052, by rfl⟩ : syracuseStep 4455253 = 26105) (by norm_num)
theorem B7519061 : Blo 1389514 7519061 := bbase (se 9 (by rfl) ⟨22028, by rfl⟩ : syracuseStep 7519061 = 44057) (by norm_num)
theorem B1563493 : Blo 1389514 1563493 := bbase (se 4 (by rfl) ⟨146577, by rfl⟩ : syracuseStep 1563493 = 293155) (by norm_num)
theorem B3128165 : Blo 1389514 3128165 := bbase (se 4 (by rfl) ⟨293265, by rfl⟩ : syracuseStep 3128165 = 586531) (by norm_num)
theorem B1760125 : Blo 1389514 1760125 := bbase (se 3 (by rfl) ⟨330023, by rfl⟩ : syracuseStep 1760125 = 660047) (by norm_num)
theorem B4692869 : Blo 1389514 4692869 := bbase (se 4 (by rfl) ⟨439956, by rfl⟩ : syracuseStep 4692869 = 879913) (by norm_num)
theorem B1563529 : Blo 1389514 1563529 := bbase (se 2 (by rfl) ⟨586323, by rfl⟩ : syracuseStep 1563529 = 1172647) (by norm_num)
theorem B1809289 : Blo 1389514 1809289 := bbase (se 2 (by rfl) ⟨678483, by rfl⟩ : syracuseStep 1809289 = 1356967) (by norm_num)
theorem B1563565 : Blo 1389514 1563565 := bbase (se 3 (by rfl) ⟨293168, by rfl⟩ : syracuseStep 1563565 = 586337) (by norm_num)
theorem B3128237 : Blo 1389514 3128237 := bbase (se 3 (by rfl) ⟨586544, by rfl⟩ : syracuseStep 3128237 = 1173089) (by norm_num)
theorem B1563601 : Blo 1389514 1563601 := bbase (se 2 (by rfl) ⟨586350, by rfl⟩ : syracuseStep 1563601 = 1172701) (by norm_num)
theorem B11885525 : Blo 1389514 11885525 := bbase (se 7 (by rfl) ⟨139283, by rfl⟩ : syracuseStep 11885525 = 278567) (by norm_num)
theorem B1670105 : Blo 1389514 1670105 := bbase (se 2 (by rfl) ⟨626289, by rfl⟩ : syracuseStep 1670105 = 1252579) (by norm_num)
theorem B1760221 : Blo 1389514 1760221 := bbase (se 3 (by rfl) ⟨330041, by rfl⟩ : syracuseStep 1760221 = 660083) (by norm_num)
theorem B1563637 : Blo 1389514 1563637 := bbase (se 5 (by rfl) ⟨73295, by rfl⟩ : syracuseStep 1563637 = 146591) (by norm_num)
theorem B3128309 : Blo 1389514 3128309 := bbase (se 5 (by rfl) ⟨146639, by rfl⟩ : syracuseStep 3128309 = 293279) (by norm_num)
theorem B1563673 : Blo 1389514 1563673 := bbase (se 2 (by rfl) ⟨586377, by rfl⟩ : syracuseStep 1563673 = 1172755) (by norm_num)
theorem B2817053 : Blo 1389514 2817053 := bbase (se 3 (by rfl) ⟨528197, by rfl⟩ : syracuseStep 2817053 = 1056395) (by norm_num)
theorem B1563709 : Blo 1389514 1563709 := bbase (se 3 (by rfl) ⟨293195, by rfl⟩ : syracuseStep 1563709 = 586391) (by norm_num)
theorem B3128381 : Blo 1389514 3128381 := bbase (se 3 (by rfl) ⟨586571, by rfl⟩ : syracuseStep 3128381 = 1173143) (by norm_num)
theorem B11877461 : Blo 1389514 11877461 := bbase (se 8 (by rfl) ⟨69594, by rfl⟩ : syracuseStep 11877461 = 139189) (by norm_num)
theorem B1563745 : Blo 1389514 1563745 := bbase (se 2 (by rfl) ⟨586404, by rfl⟩ : syracuseStep 1563745 = 1172809) (by norm_num)
theorem B4226165 : Blo 1389514 4226165 := bbase (se 5 (by rfl) ⟨198101, by rfl⟩ : syracuseStep 4226165 = 396203) (by norm_num)
theorem B1563781 : Blo 1389514 1563781 := bbase (se 4 (by rfl) ⟨146604, by rfl⟩ : syracuseStep 1563781 = 293209) (by norm_num)
theorem B3128453 : Blo 1389514 3128453 := bbase (se 4 (by rfl) ⟨293292, by rfl⟩ : syracuseStep 3128453 = 586585) (by norm_num)
theorem B1760393 : Blo 1389514 1760393 := bbase (se 2 (by rfl) ⟨660147, by rfl⟩ : syracuseStep 1760393 = 1320295) (by norm_num)
theorem B3521677 : Blo 1389514 3521677 := bbase (se 3 (by rfl) ⟨660314, by rfl⟩ : syracuseStep 3521677 = 1320629) (by norm_num)
theorem B7044245 : Blo 1389514 7044245 := bbase (se 6 (by rfl) ⟨165099, by rfl⟩ : syracuseStep 7044245 = 330199) (by norm_num)
theorem B2227357 : Blo 1389514 2227357 := bbase (se 3 (by rfl) ⟨417629, by rfl⟩ : syracuseStep 2227357 = 835259) (by norm_num)
theorem B1563817 : Blo 1389514 1563817 := bbase (se 2 (by rfl) ⟨586431, by rfl⟩ : syracuseStep 1563817 = 1172863) (by norm_num)
theorem B1760449 : Blo 1389514 1760449 := bbase (se 2 (by rfl) ⟨660168, by rfl⟩ : syracuseStep 1760449 = 1320337) (by norm_num)
theorem B3169477 : Blo 1389514 3169477 := bbase (se 4 (by rfl) ⟨297138, by rfl⟩ : syracuseStep 3169477 = 594277) (by norm_num)
theorem B5938373 : Blo 1389514 5938373 := bbase (se 4 (by rfl) ⟨556722, by rfl⟩ : syracuseStep 5938373 = 1113445) (by norm_num)
theorem B1563853 : Blo 1389514 1563853 := bbase (se 3 (by rfl) ⟨293222, by rfl⟩ : syracuseStep 1563853 = 586445) (by norm_num)
theorem B3128525 : Blo 1389514 3128525 := bbase (se 3 (by rfl) ⟨586598, by rfl⟩ : syracuseStep 3128525 = 1173197) (by norm_num)
theorem B1563889 : Blo 1389514 1563889 := bbase (se 2 (by rfl) ⟨586458, by rfl⟩ : syracuseStep 1563889 = 1172917) (by norm_num)
theorem B3521789 : Blo 1389514 3521789 := bbase (se 3 (by rfl) ⟨660335, by rfl⟩ : syracuseStep 3521789 = 1320671) (by norm_num)
theorem B1563925 : Blo 1389514 1563925 := bbase (se 6 (by rfl) ⟨36654, by rfl⟩ : syracuseStep 1563925 = 73309) (by norm_num)
theorem B3128597 : Blo 1389514 3128597 := bbase (se 6 (by rfl) ⟨73326, by rfl⟩ : syracuseStep 3128597 = 146653) (by norm_num)
theorem B1760545 : Blo 1389514 1760545 := bbase (se 2 (by rfl) ⟨660204, by rfl⟩ : syracuseStep 1760545 = 1320409) (by norm_num)
theorem B1670441 : Blo 1389514 1670441 := bbase (se 2 (by rfl) ⟨626415, by rfl⟩ : syracuseStep 1670441 = 1252831) (by norm_num)
theorem B4693301 : Blo 1389514 4693301 := bbase (se 5 (by rfl) ⟨219998, by rfl⟩ : syracuseStep 4693301 = 439997) (by norm_num)
theorem B7920949 : Blo 1389514 7920949 := bbase (se 5 (by rfl) ⟨371294, by rfl⟩ : syracuseStep 7920949 = 742589) (by norm_num)
theorem B1563961 : Blo 1389514 1563961 := bbase (se 2 (by rfl) ⟨586485, by rfl⟩ : syracuseStep 1563961 = 1172971) (by norm_num)
theorem B57105749 : Blo 1389514 57105749 := bbase (se 11 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 57105749 = 83651) (by norm_num)
theorem B1563997 : Blo 1389514 1563997 := bbase (se 3 (by rfl) ⟨293249, by rfl⟩ : syracuseStep 1563997 = 586499) (by norm_num)
theorem B3128669 : Blo 1389514 3128669 := bbase (se 3 (by rfl) ⟨586625, by rfl⟩ : syracuseStep 3128669 = 1173251) (by norm_num)
theorem B1564033 : Blo 1389514 1564033 := bbase (se 2 (by rfl) ⟨586512, by rfl⟩ : syracuseStep 1564033 = 1173025) (by norm_num)
theorem B1670557 : Blo 1389514 1670557 := bbase (se 3 (by rfl) ⟨313229, by rfl⟩ : syracuseStep 1670557 = 626459) (by norm_num)
theorem B1564069 : Blo 1389514 1564069 := bbase (se 4 (by rfl) ⟨146631, by rfl⟩ : syracuseStep 1564069 = 293263) (by norm_num)
theorem B3128741 : Blo 1389514 3128741 := bbase (se 4 (by rfl) ⟨293319, by rfl⟩ : syracuseStep 3128741 = 586639) (by norm_num)
theorem B9649589 : Blo 1389514 9649589 := bbase (se 5 (by rfl) ⟨452324, by rfl⟩ : syracuseStep 9649589 = 904649) (by norm_num)
theorem B3521981 : Blo 1389514 3521981 := bbase (se 3 (by rfl) ⟨660371, by rfl⟩ : syracuseStep 3521981 = 1320743) (by norm_num)
theorem B1564105 : Blo 1389514 1564105 := bbase (se 2 (by rfl) ⟨586539, by rfl⟩ : syracuseStep 1564105 = 1173079) (by norm_num)
theorem B1760717 : Blo 1389514 1760717 := bbase (se 3 (by rfl) ⟨330134, by rfl⟩ : syracuseStep 1760717 = 660269) (by norm_num)
theorem B1670629 : Blo 1389514 1670629 := bbase (se 4 (by rfl) ⟨156621, by rfl⟩ : syracuseStep 1670629 = 313243) (by norm_num)
theorem B1564141 : Blo 1389514 1564141 := bbase (se 3 (by rfl) ⟨293276, by rfl⟩ : syracuseStep 1564141 = 586553) (by norm_num)
theorem B3128813 : Blo 1389514 3128813 := bbase (se 3 (by rfl) ⟨586652, by rfl⟩ : syracuseStep 3128813 = 1173305) (by norm_num)
theorem B1670653 : Blo 1389514 1670653 := bbase (se 3 (by rfl) ⟨313247, by rfl⟩ : syracuseStep 1670653 = 626495) (by norm_num)
theorem B1760773 : Blo 1389514 1760773 := bbase (se 4 (by rfl) ⟨165072, by rfl⟩ : syracuseStep 1760773 = 330145) (by norm_num)
theorem B1564177 : Blo 1389514 1564177 := bbase (se 2 (by rfl) ⟨586566, by rfl⟩ : syracuseStep 1564177 = 1173133) (by norm_num)
theorem B7036469 : Blo 1389514 7036469 := bbase (se 5 (by rfl) ⟨329834, by rfl⟩ : syracuseStep 7036469 = 659669) (by norm_num)
theorem B1564213 : Blo 1389514 1564213 := bbase (se 5 (by rfl) ⟨73322, by rfl⟩ : syracuseStep 1564213 = 146645) (by norm_num)
theorem B3128885 : Blo 1389514 3128885 := bbase (se 5 (by rfl) ⟨146666, by rfl⟩ : syracuseStep 3128885 = 293333) (by norm_num)
theorem B1564249 : Blo 1389514 1564249 := bbase (se 2 (by rfl) ⟨586593, by rfl⟩ : syracuseStep 1564249 = 1173187) (by norm_num)
theorem B1760869 : Blo 1389514 1760869 := bbase (se 4 (by rfl) ⟨165081, by rfl⟩ : syracuseStep 1760869 = 330163) (by norm_num)
theorem B1564285 : Blo 1389514 1564285 := bbase (se 3 (by rfl) ⟨293303, by rfl⟩ : syracuseStep 1564285 = 586607) (by norm_num)
theorem B3128957 : Blo 1389514 3128957 := bbase (se 3 (by rfl) ⟨586679, by rfl⟩ : syracuseStep 3128957 = 1173359) (by norm_num)
theorem B1670797 : Blo 1389514 1670797 := bbase (se 3 (by rfl) ⟨313274, by rfl⟩ : syracuseStep 1670797 = 626549) (by norm_num)
theorem B1564321 : Blo 1389514 1564321 := bbase (se 2 (by rfl) ⟨586620, by rfl⟩ : syracuseStep 1564321 = 1173241) (by norm_num)
theorem B2506405 : Blo 1389514 2506405 := bbase (se 4 (by rfl) ⟨234975, by rfl⟩ : syracuseStep 2506405 = 469951) (by norm_num)
theorem B12689077 : Blo 1389514 12689077 := bbase (se 5 (by rfl) ⟨594800, by rfl⟩ : syracuseStep 12689077 = 1189601) (by norm_num)
theorem B1564357 : Blo 1389514 1564357 := bbase (se 4 (by rfl) ⟨146658, by rfl⟩ : syracuseStep 1564357 = 293317) (by norm_num)
theorem B3129029 : Blo 1389514 3129029 := bbase (se 4 (by rfl) ⟨293346, by rfl⟩ : syracuseStep 3129029 = 586693) (by norm_num)
theorem B4693733 : Blo 1389514 4693733 := bbase (se 4 (by rfl) ⟨440037, by rfl⟩ : syracuseStep 4693733 = 880075) (by norm_num)
theorem B2506469 : Blo 1389514 2506469 := bbase (se 4 (by rfl) ⟨234981, by rfl⟩ : syracuseStep 2506469 = 469963) (by norm_num)
theorem B1564393 : Blo 1389514 1564393 := bbase (se 2 (by rfl) ⟨586647, by rfl⟩ : syracuseStep 1564393 = 1173295) (by norm_num)
theorem B1564429 : Blo 1389514 1564429 := bbase (se 3 (by rfl) ⟨293330, by rfl⟩ : syracuseStep 1564429 = 586661) (by norm_num)
theorem B3129101 : Blo 1389514 3129101 := bbase (se 3 (by rfl) ⟨586706, by rfl⟩ : syracuseStep 3129101 = 1173413) (by norm_num)
theorem B1761041 : Blo 1389514 1761041 := bbase (se 2 (by rfl) ⟨660390, by rfl⟩ : syracuseStep 1761041 = 1320781) (by norm_num)
theorem B1564465 : Blo 1389514 1564465 := bbase (se 2 (by rfl) ⟨586674, by rfl⟩ : syracuseStep 1564465 = 1173349) (by norm_num)
theorem B1761097 : Blo 1389514 1761097 := bbase (se 2 (by rfl) ⟨660411, by rfl⟩ : syracuseStep 1761097 = 1320823) (by norm_num)
theorem B26722133 : Blo 1389514 26722133 := bbase (se 9 (by rfl) ⟨78287, by rfl⟩ : syracuseStep 26722133 = 156575) (by norm_num)
theorem B1564501 : Blo 1389514 1564501 := bbase (se 9 (by rfl) ⟨4583, by rfl⟩ : syracuseStep 1564501 = 9167) (by norm_num)
theorem B3129173 : Blo 1389514 3129173 := bbase (se 9 (by rfl) ⟨9167, by rfl⟩ : syracuseStep 3129173 = 18335) (by norm_num)
theorem B3342181 : Blo 1389514 3342181 := bbase (se 4 (by rfl) ⟨313329, by rfl⟩ : syracuseStep 3342181 = 626659) (by norm_num)
theorem B1564537 : Blo 1389514 1564537 := bbase (se 2 (by rfl) ⟨586701, by rfl⟩ : syracuseStep 1564537 = 1173403) (by norm_num)
theorem B1564573 : Blo 1389514 1564573 := bbase (se 3 (by rfl) ⟨293357, by rfl⟩ : syracuseStep 1564573 = 586715) (by norm_num)
theorem B3129245 : Blo 1389514 3129245 := bbase (se 3 (by rfl) ⟨586733, by rfl⟩ : syracuseStep 3129245 = 1173467) (by norm_num)
theorem B1564609 : Blo 1389514 1564609 := bbase (se 2 (by rfl) ⟨586728, by rfl⟩ : syracuseStep 1564609 = 1173457) (by norm_num)
theorem B3170245 : Blo 1389514 3170245 := bbase (se 4 (by rfl) ⟨297210, by rfl⟩ : syracuseStep 3170245 = 594421) (by norm_num)
theorem B1564645 : Blo 1389514 1564645 := bbase (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) (by norm_num)
theorem B3129317 : Blo 1389514 3129317 := bbase (se 4 (by rfl) ⟨293373, by rfl⟩ : syracuseStep 3129317 = 586747) (by norm_num)
theorem B3170353 : Blo 1389514 3170353 := bstep (se 2 (by rfl) ⟨1188882, by rfl⟩ : syracuseStep 3170353 = 2377765) B2377765
theorem B3129425 : Blo 1389514 3129425 := bstep (se 2 (by rfl) ⟨1173534, by rfl⟩ : syracuseStep 3129425 = 2347069) B2347069
theorem B3129443 : Blo 1389514 3129443 := bstep (se 1 (by rfl) ⟨2347082, by rfl⟩ : syracuseStep 3129443 = 4694165) B4694165
theorem B1564771 : Blo 1389514 1564771 := bstep (se 1 (by rfl) ⟨1173578, by rfl⟩ : syracuseStep 1564771 = 2347157) B2347157
theorem B2638001 : Blo 1389514 2638001 := bstep (se 2 (by rfl) ⟨989250, by rfl⟩ : syracuseStep 2638001 = 1978501) B1978501
theorem B1564915 : Blo 1389514 1564915 := bstep (se 1 (by rfl) ⟨1173686, by rfl⟩ : syracuseStep 1564915 = 2347373) B2347373
theorem B9027875 : Blo 1389514 9027875 := bstep (se 1 (by rfl) ⟨6770906, by rfl⟩ : syracuseStep 9027875 = 13541813) B13541813
theorem B4694381 : Blo 1389514 4694381 := bstep (se 3 (by rfl) ⟨880196, by rfl⟩ : syracuseStep 4694381 = 1760393) B1760393
theorem B3129713 : Blo 1389514 3129713 := bstep (se 2 (by rfl) ⟨1173642, by rfl⟩ : syracuseStep 3129713 = 2347285) B2347285
theorem B3129731 : Blo 1389514 3129731 := bstep (se 1 (by rfl) ⟨2347298, by rfl⟩ : syracuseStep 3129731 = 4694597) B4694597
theorem B1565059 : Blo 1389514 1565059 := bstep (se 1 (by rfl) ⟨1173794, by rfl⟩ : syracuseStep 1565059 = 2347589) B2347589
theorem B4694435 : Blo 1389514 4694435 := bstep (se 1 (by rfl) ⟨3520826, by rfl⟩ : syracuseStep 4694435 = 7041653) B7041653
theorem B7913933 : Blo 1389514 7913933 := bstep (se 3 (by rfl) ⟨1483862, by rfl⟩ : syracuseStep 7913933 = 2967725) B2967725
theorem B1565203 : Blo 1389514 1565203 := bstep (se 1 (by rfl) ⟨1173902, by rfl⟩ : syracuseStep 1565203 = 2347805) B2347805
theorem B2540081 : Blo 1389514 2540081 := bstep (se 2 (by rfl) ⟨952530, by rfl⟩ : syracuseStep 2540081 = 1905061) B1905061
theorem B7922225 : Blo 1389514 7922225 := bstep (se 2 (by rfl) ⟨2970834, by rfl⟩ : syracuseStep 7922225 = 5941669) B5941669
theorem B2638403 : Blo 1389514 2638403 := bstep (se 1 (by rfl) ⟨1978802, by rfl⟩ : syracuseStep 2638403 = 3957605) B3957605
theorem B2114129 : Blo 1389514 2114129 := bstep (se 2 (by rfl) ⟨792798, by rfl⟩ : syracuseStep 2114129 = 1585597) B1585597
theorem B3130001 : Blo 1389514 3130001 := bstep (se 2 (by rfl) ⟨1173750, by rfl⟩ : syracuseStep 3130001 = 2347501) B2347501
theorem B7037603 : Blo 1389514 7037603 := bstep (se 1 (by rfl) ⟨5278202, by rfl⟩ : syracuseStep 7037603 = 10556405) B10556405
theorem B3130019 : Blo 1389514 3130019 := bstep (se 1 (by rfl) ⟨2347514, by rfl⟩ : syracuseStep 3130019 = 4695029) B4695029
theorem B1565347 : Blo 1389514 1565347 := bstep (se 1 (by rfl) ⟨1174010, by rfl⟩ : syracuseStep 1565347 = 2348021) B2348021
theorem B4694705 : Blo 1389514 4694705 := bstep (se 2 (by rfl) ⟨1760514, by rfl⟩ : syracuseStep 4694705 = 3521029) B3521029
theorem B3957457 : Blo 1389514 3957457 := bstep (se 2 (by rfl) ⟨1484046, by rfl⟩ : syracuseStep 3957457 = 2968093) B2968093
theorem B11879237 : Blo 1389514 11879237 := bstep (se 4 (by rfl) ⟨1113678, by rfl⟩ : syracuseStep 11879237 = 2227357) B2227357
theorem B8905585 : Blo 1389514 8905585 := bstep (se 2 (by rfl) ⟨3339594, by rfl⟩ : syracuseStep 8905585 = 6679189) B6679189
theorem B7521137 : Blo 1389514 7521137 := bstep (se 2 (by rfl) ⟨2820426, by rfl⟩ : syracuseStep 7521137 = 5640853) B5640853
theorem B3130289 : Blo 1389514 3130289 := bstep (se 2 (by rfl) ⟨1173858, by rfl⟩ : syracuseStep 3130289 = 2347717) B2347717
theorem B3130307 : Blo 1389514 3130307 := bstep (se 1 (by rfl) ⟨2347730, by rfl⟩ : syracuseStep 3130307 = 4695461) B4695461
theorem B3957731 : Blo 1389514 3957731 := bstep (se 1 (by rfl) ⟨2968298, by rfl⟩ : syracuseStep 3957731 = 5936597) B5936597
theorem B5014541 : Blo 1389514 5014541 := bstep (se 3 (by rfl) ⟨940226, by rfl⟩ : syracuseStep 5014541 = 1880453) B1880453
theorem B6865955 : Blo 1389514 6865955 := bstep (se 1 (by rfl) ⟨5149466, by rfl⟩ : syracuseStep 6865955 = 10298933) B10298933
theorem B5940337 : Blo 1389514 5940337 := bstep (se 2 (by rfl) ⟨2227626, by rfl⟩ : syracuseStep 5940337 = 4455253) B4455253
theorem B8029297 : Blo 1389514 8029297 := bstep (se 2 (by rfl) ⟨3010986, by rfl⟩ : syracuseStep 8029297 = 6021973) B6021973
theorem B4457585 : Blo 1389514 4457585 := bstep (se 2 (by rfl) ⟨1671594, by rfl⟩ : syracuseStep 4457585 = 3343189) B3343189
theorem B2114689 : Blo 1389514 2114689 := bstep (se 2 (by rfl) ⟨793008, by rfl⟩ : syracuseStep 2114689 = 1586017) B1586017
theorem B25732237 : Blo 1389514 25732237 := bstep (se 3 (by rfl) ⟨4824794, by rfl⟩ : syracuseStep 25732237 = 9649589) B9649589
theorem B5014669 : Blo 1389514 5014669 := bstep (se 3 (by rfl) ⟨940250, by rfl⟩ : syracuseStep 5014669 = 1880501) B1880501
theorem B3957923 : Blo 1389514 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B10552517 : Blo 1389514 10552517 := bstep (se 4 (by rfl) ⟨989298, by rfl⟩ : syracuseStep 10552517 = 1978597) B1978597
theorem B4695245 : Blo 1389514 4695245 := bstep (se 3 (by rfl) ⟨880358, by rfl⟩ : syracuseStep 4695245 = 1760717) B1760717
theorem B3130577 : Blo 1389514 3130577 := bstep (se 2 (by rfl) ⟨1173966, by rfl⟩ : syracuseStep 3130577 = 2347933) B2347933
theorem B3130595 : Blo 1389514 3130595 := bstep (se 1 (by rfl) ⟨2347946, by rfl⟩ : syracuseStep 3130595 = 4695893) B4695893
theorem B4695299 : Blo 1389514 4695299 := bstep (se 1 (by rfl) ⟨3521474, by rfl⟩ : syracuseStep 4695299 = 7042949) B7042949
theorem B10028387 : Blo 1389514 10028387 := bstep (se 1 (by rfl) ⟨7521290, by rfl⟩ : syracuseStep 10028387 = 15042581) B15042581
theorem B2639299 : Blo 1389514 2639299 := bstep (se 1 (by rfl) ⟨1979474, by rfl⟩ : syracuseStep 2639299 = 3958949) B3958949
theorem B7038413 : Blo 1389514 7038413 := bstep (se 3 (by rfl) ⟨1319702, by rfl⟩ : syracuseStep 7038413 = 2639405) B2639405
theorem B3130865 : Blo 1389514 3130865 := bstep (se 2 (by rfl) ⟨1174074, by rfl⟩ : syracuseStep 3130865 = 2348149) B2348149
theorem B3130883 : Blo 1389514 3130883 := bstep (se 1 (by rfl) ⟨2348162, by rfl⟩ : syracuseStep 3130883 = 4696325) B4696325
theorem B4695569 : Blo 1389514 4695569 := bstep (se 2 (by rfl) ⟨1760838, by rfl⟩ : syracuseStep 4695569 = 3521677) B3521677
theorem B2639459 : Blo 1389514 2639459 := bstep (se 1 (by rfl) ⟨1979594, by rfl⟩ : syracuseStep 2639459 = 3959189) B3959189
theorem B22537925 : Blo 1389514 22537925 := bstep (se 4 (by rfl) ⟨2112930, by rfl⟩ : syracuseStep 22537925 = 4225861) B4225861
theorem B10561265 : Blo 1389514 10561265 := bstep (se 2 (by rfl) ⟨3960474, by rfl⟩ : syracuseStep 10561265 = 7920949) B7920949
theorem B2115443 : Blo 1389514 2115443 := bstep (se 1 (by rfl) ⟨1586582, by rfl⟩ : syracuseStep 2115443 = 3173165) B3173165
theorem B2377601 : Blo 1389514 2377601 := bstep (se 2 (by rfl) ⟨891600, by rfl⟩ : syracuseStep 2377601 = 1783201) B1783201
theorem B2344835 : Blo 1389514 2344835 := bstep (se 1 (by rfl) ⟨1758626, by rfl⟩ : syracuseStep 2344835 = 3517253) B3517253
theorem B5277581 : Blo 1389514 5277581 := bstep (se 3 (by rfl) ⟨989546, by rfl⟩ : syracuseStep 5277581 = 1979093) B1979093
theorem B3958733 : Blo 1389514 3958733 := bstep (se 3 (by rfl) ⟨742262, by rfl⟩ : syracuseStep 3958733 = 1484525) B1484525
theorem B7923683 : Blo 1389514 7923683 := bstep (se 1 (by rfl) ⟨5942762, by rfl⟩ : syracuseStep 7923683 = 11885525) B11885525
theorem B2410483 : Blo 1389514 2410483 := bstep (se 1 (by rfl) ⟨1807862, by rfl⟩ : syracuseStep 2410483 = 3615725) B3615725
theorem B2344963 : Blo 1389514 2344963 := bstep (se 1 (by rfl) ⟨1758722, by rfl⟩ : syracuseStep 2344963 = 3517445) B3517445
theorem B1878035 : Blo 1389514 1878035 := bstep (se 1 (by rfl) ⟨1408526, by rfl⟩ : syracuseStep 1878035 = 2817053) B2817053
theorem B4696109 : Blo 1389514 4696109 := bstep (se 3 (by rfl) ⟨880520, by rfl⟩ : syracuseStep 4696109 = 1761041) B1761041
theorem B4696163 : Blo 1389514 4696163 := bstep (se 1 (by rfl) ⟨3522122, by rfl⟩ : syracuseStep 4696163 = 7044245) B7044245
theorem B3958915 : Blo 1389514 3958915 := bstep (se 1 (by rfl) ⟨2969186, by rfl⟩ : syracuseStep 3958915 = 5938373) B5938373
theorem B2345105 : Blo 1389514 2345105 := bstep (se 2 (by rfl) ⟨879414, by rfl⟩ : syracuseStep 2345105 = 1758829) B1758829
theorem B3565745 : Blo 1389514 3565745 := bstep (se 2 (by rfl) ⟨1337154, by rfl⟩ : syracuseStep 3565745 = 2674309) B2674309
theorem B38070499 : Blo 1389514 38070499 := bstep (se 1 (by rfl) ⟨28552874, by rfl⟩ : syracuseStep 38070499 = 57105749) B57105749
theorem B16918769 : Blo 1389514 16918769 := bstep (se 2 (by rfl) ⟨6344538, by rfl⟩ : syracuseStep 16918769 = 12689077) B12689077
theorem B2345233 : Blo 1389514 2345233 := bstep (se 2 (by rfl) ⟨879462, by rfl⟩ : syracuseStep 2345233 = 1758925) B1758925
theorem B2345267 : Blo 1389514 2345267 := bstep (se 1 (by rfl) ⟨1758950, by rfl⟩ : syracuseStep 2345267 = 3517901) B3517901
theorem B2345395 : Blo 1389514 2345395 := bstep (se 1 (by rfl) ⟨1759046, by rfl⟩ : syracuseStep 2345395 = 3518093) B3518093
theorem B2345537 : Blo 1389514 2345537 := bstep (se 2 (by rfl) ⟨879576, by rfl⟩ : syracuseStep 2345537 = 1759153) B1759153
theorem B3172945 : Blo 1389514 3172945 := bstep (se 2 (by rfl) ⟨1189854, by rfl⟩ : syracuseStep 3172945 = 2379709) B2379709
theorem B3959405 : Blo 1389514 3959405 := bstep (se 3 (by rfl) ⟨742388, by rfl⟩ : syracuseStep 3959405 = 1484777) B1484777
theorem B2640529 : Blo 1389514 2640529 := bstep (se 2 (by rfl) ⟨990198, by rfl⟩ : syracuseStep 2640529 = 1980397) B1980397
theorem B5278385 : Blo 1389514 5278385 := bstep (se 2 (by rfl) ⟨1979394, by rfl⟩ : syracuseStep 5278385 = 3958789) B3958789
theorem B2345665 : Blo 1389514 2345665 := bstep (se 2 (by rfl) ⟨879624, by rfl⟩ : syracuseStep 2345665 = 1759249) B1759249
theorem B2345699 : Blo 1389514 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B3517283 : Blo 1389514 3517283 := bstep (se 1 (by rfl) ⟨2637962, by rfl⟩ : syracuseStep 3517283 = 5275925) B5275925
theorem B2345827 : Blo 1389514 2345827 := bstep (se 1 (by rfl) ⟨1759370, by rfl⟩ : syracuseStep 2345827 = 3518741) B3518741
theorem B2034595 : Blo 1389514 2034595 := bstep (se 1 (by rfl) ⟨1525946, by rfl⟩ : syracuseStep 2034595 = 3051893) B3051893
theorem B2345969 : Blo 1389514 2345969 := bstep (se 2 (by rfl) ⟨879738, by rfl⟩ : syracuseStep 2345969 = 1759477) B1759477
theorem B2968579 : Blo 1389514 2968579 := bstep (se 1 (by rfl) ⟨2226434, by rfl⟩ : syracuseStep 2968579 = 4452869) B4452869
theorem B5942285 : Blo 1389514 5942285 := bstep (se 3 (by rfl) ⟨1114178, by rfl⟩ : syracuseStep 5942285 = 2228357) B2228357
theorem B1879073 : Blo 1389514 1879073 := bstep (se 2 (by rfl) ⟨704652, by rfl⟩ : syracuseStep 1879073 = 1409305) B1409305
theorem B12717155 : Blo 1389514 12717155 := bstep (se 1 (by rfl) ⟨9537866, by rfl⟩ : syracuseStep 12717155 = 19075733) B19075733
theorem B2346097 : Blo 1389514 2346097 := bstep (se 2 (by rfl) ⟨879786, by rfl⟩ : syracuseStep 2346097 = 1759573) B1759573
theorem B20319373 : Blo 1389514 20319373 := bstep (se 3 (by rfl) ⟨3809882, by rfl⟩ : syracuseStep 20319373 = 7619765) B7619765
theorem B2346131 : Blo 1389514 2346131 := bstep (se 1 (by rfl) ⟨1759598, by rfl⟩ : syracuseStep 2346131 = 3519197) B3519197
theorem B4451537 : Blo 1389514 4451537 := bstep (se 2 (by rfl) ⟨1669326, by rfl⟩ : syracuseStep 4451537 = 3338653) B3338653
theorem B2346259 : Blo 1389514 2346259 := bstep (se 1 (by rfl) ⟨1759694, by rfl⟩ : syracuseStep 2346259 = 3519389) B3519389
theorem B7916849 : Blo 1389514 7916849 := bstep (se 2 (by rfl) ⟨2968818, by rfl⟩ : syracuseStep 7916849 = 5937637) B5937637
theorem B2379073 : Blo 1389514 2379073 := bstep (se 2 (by rfl) ⟨892152, by rfl⟩ : syracuseStep 2379073 = 1784305) B1784305
theorem B11283781 : Blo 1389514 11283781 := bstep (se 4 (by rfl) ⟨1057854, by rfl⟩ : syracuseStep 11283781 = 2115709) B2115709
theorem B5279053 : Blo 1389514 5279053 := bstep (se 3 (by rfl) ⟨989822, by rfl⟩ : syracuseStep 5279053 = 1979645) B1979645
theorem B2968913 : Blo 1389514 2968913 := bstep (se 2 (by rfl) ⟨1113342, by rfl⟩ : syracuseStep 2968913 = 2226685) B2226685
theorem B2346401 : Blo 1389514 2346401 := bstep (se 2 (by rfl) ⟨879900, by rfl⟩ : syracuseStep 2346401 = 1759801) B1759801
theorem B2084273 : Blo 1389514 2084273 := bstep (se 2 (by rfl) ⟨781602, by rfl⟩ : syracuseStep 2084273 = 1563205) B1563205
theorem B2084291 : Blo 1389514 2084291 := bstep (se 1 (by rfl) ⟨1563218, by rfl⟩ : syracuseStep 2084291 = 3126437) B3126437
theorem B2084321 : Blo 1389514 2084321 := bstep (se 2 (by rfl) ⟨781620, by rfl⟩ : syracuseStep 2084321 = 1563241) B1563241
theorem B2084339 : Blo 1389514 2084339 := bstep (se 1 (by rfl) ⟨1563254, by rfl⟩ : syracuseStep 2084339 = 3126509) B3126509
theorem B2084369 : Blo 1389514 2084369 := bstep (se 2 (by rfl) ⟨781638, by rfl⟩ : syracuseStep 2084369 = 1563277) B1563277
theorem B1879571 : Blo 1389514 1879571 := bstep (se 1 (by rfl) ⟨1409678, by rfl⟩ : syracuseStep 1879571 = 2819357) B2819357
theorem B2346529 : Blo 1389514 2346529 := bstep (se 2 (by rfl) ⟨879948, by rfl⟩ : syracuseStep 2346529 = 1759897) B1759897
theorem B2084387 : Blo 1389514 2084387 := bstep (se 1 (by rfl) ⟨1563290, by rfl⟩ : syracuseStep 2084387 = 3126581) B3126581
theorem B2084417 : Blo 1389514 2084417 := bstep (se 2 (by rfl) ⟨781656, by rfl⟩ : syracuseStep 2084417 = 1563313) B1563313
theorem B2346563 : Blo 1389514 2346563 := bstep (se 1 (by rfl) ⟨1759922, by rfl⟩ : syracuseStep 2346563 = 3519845) B3519845
theorem B2084435 : Blo 1389514 2084435 := bstep (se 1 (by rfl) ⟨1563326, by rfl⟩ : syracuseStep 2084435 = 3126653) B3126653
theorem B2084465 : Blo 1389514 2084465 := bstep (se 2 (by rfl) ⟨781674, by rfl⟩ : syracuseStep 2084465 = 1563349) B1563349
theorem B2084483 : Blo 1389514 2084483 := bstep (se 1 (by rfl) ⟨1563362, by rfl⟩ : syracuseStep 2084483 = 3126725) B3126725
theorem B17829517 : Blo 1389514 17829517 := bstep (se 3 (by rfl) ⟨3343034, by rfl⟩ : syracuseStep 17829517 = 6686069) B6686069
theorem B2084513 : Blo 1389514 2084513 := bstep (se 2 (by rfl) ⟨781692, by rfl⟩ : syracuseStep 2084513 = 1563385) B1563385
theorem B2641585 : Blo 1389514 2641585 := bstep (se 2 (by rfl) ⟨990594, by rfl⟩ : syracuseStep 2641585 = 1981189) B1981189
theorem B2084531 : Blo 1389514 2084531 := bstep (se 1 (by rfl) ⟨1563398, by rfl⟩ : syracuseStep 2084531 = 3126797) B3126797
theorem B2346691 : Blo 1389514 2346691 := bstep (se 1 (by rfl) ⟨1760018, by rfl⟩ : syracuseStep 2346691 = 3520037) B3520037
theorem B2084561 : Blo 1389514 2084561 := bstep (se 2 (by rfl) ⟨781710, by rfl⟩ : syracuseStep 2084561 = 1563421) B1563421
theorem B2084579 : Blo 1389514 2084579 := bstep (se 1 (by rfl) ⟨1563434, by rfl⟩ : syracuseStep 2084579 = 3126869) B3126869
theorem B34303715 : Blo 1389514 34303715 := bstep (se 1 (by rfl) ⟨25727786, by rfl⟩ : syracuseStep 34303715 = 51455573) B51455573
theorem B2084609 : Blo 1389514 2084609 := bstep (se 2 (by rfl) ⟨781728, by rfl⟩ : syracuseStep 2084609 = 1563457) B1563457
theorem B3960589 : Blo 1389514 3960589 := bstep (se 3 (by rfl) ⟨742610, by rfl⟩ : syracuseStep 3960589 = 1485221) B1485221
theorem B3518225 : Blo 1389514 3518225 := bstep (se 2 (by rfl) ⟨1319334, by rfl⟩ : syracuseStep 3518225 = 2638669) B2638669
theorem B2084627 : Blo 1389514 2084627 := bstep (se 1 (by rfl) ⟨1563470, by rfl⟩ : syracuseStep 2084627 = 3126941) B3126941
theorem B2084657 : Blo 1389514 2084657 := bstep (se 2 (by rfl) ⟨781746, by rfl⟩ : syracuseStep 2084657 = 1563493) B1563493
theorem B2084675 : Blo 1389514 2084675 := bstep (se 1 (by rfl) ⟨1563506, by rfl⟩ : syracuseStep 2084675 = 3127013) B3127013
theorem B3518275 : Blo 1389514 3518275 := bstep (se 1 (by rfl) ⟨2638706, by rfl⟩ : syracuseStep 3518275 = 5277413) B5277413
theorem B15249221 : Blo 1389514 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B2346833 : Blo 1389514 2346833 := bstep (se 2 (by rfl) ⟨880062, by rfl⟩ : syracuseStep 2346833 = 1760125) B1760125
theorem B2084705 : Blo 1389514 2084705 := bstep (se 2 (by rfl) ⟨781764, by rfl⟩ : syracuseStep 2084705 = 1563529) B1563529
theorem B2412385 : Blo 1389514 2412385 := bstep (se 2 (by rfl) ⟨904644, by rfl⟩ : syracuseStep 2412385 = 1809289) B1809289
theorem B2084723 : Blo 1389514 2084723 := bstep (se 1 (by rfl) ⟨1563542, by rfl⟩ : syracuseStep 2084723 = 3127085) B3127085
theorem B1879939 : Blo 1389514 1879939 := bstep (se 1 (by rfl) ⟨1409954, by rfl⟩ : syracuseStep 1879939 = 2819909) B2819909
theorem B2084753 : Blo 1389514 2084753 := bstep (se 2 (by rfl) ⟨781782, by rfl⟩ : syracuseStep 2084753 = 1563565) B1563565
theorem B2084771 : Blo 1389514 2084771 := bstep (se 1 (by rfl) ⟨1563578, by rfl⟩ : syracuseStep 2084771 = 3127157) B3127157
theorem B2084801 : Blo 1389514 2084801 := bstep (se 2 (by rfl) ⟨781800, by rfl⟩ : syracuseStep 2084801 = 1563601) B1563601
theorem B3518417 : Blo 1389514 3518417 := bstep (se 2 (by rfl) ⟨1319406, by rfl⟩ : syracuseStep 3518417 = 2638813) B2638813
theorem B2346961 : Blo 1389514 2346961 := bstep (se 2 (by rfl) ⟨880110, by rfl⟩ : syracuseStep 2346961 = 1760221) B1760221
theorem B2084819 : Blo 1389514 2084819 := bstep (se 1 (by rfl) ⟨1563614, by rfl⟩ : syracuseStep 2084819 = 3127229) B3127229
theorem B2084849 : Blo 1389514 2084849 := bstep (se 2 (by rfl) ⟨781818, by rfl⟩ : syracuseStep 2084849 = 1563637) B1563637
theorem B2346995 : Blo 1389514 2346995 := bstep (se 1 (by rfl) ⟨1760246, by rfl⟩ : syracuseStep 2346995 = 3520493) B3520493
theorem B2084867 : Blo 1389514 2084867 := bstep (se 1 (by rfl) ⟨1563650, by rfl⟩ : syracuseStep 2084867 = 3127301) B3127301
theorem B7516165 : Blo 1389514 7516165 := bstep (se 4 (by rfl) ⟨704640, by rfl⟩ : syracuseStep 7516165 = 1409281) B1409281
theorem B5640205 : Blo 1389514 5640205 := bstep (se 3 (by rfl) ⟨1057538, by rfl⟩ : syracuseStep 5640205 = 2115077) B2115077
theorem B2084897 : Blo 1389514 2084897 := bstep (se 2 (by rfl) ⟨781836, by rfl⟩ : syracuseStep 2084897 = 1563673) B1563673
theorem B2084915 : Blo 1389514 2084915 := bstep (se 1 (by rfl) ⟨1563686, by rfl⟩ : syracuseStep 2084915 = 3127373) B3127373
theorem B2084945 : Blo 1389514 2084945 := bstep (se 2 (by rfl) ⟨781854, by rfl⟩ : syracuseStep 2084945 = 1563709) B1563709
theorem B2084963 : Blo 1389514 2084963 := bstep (se 1 (by rfl) ⟨1563722, by rfl⟩ : syracuseStep 2084963 = 3127445) B3127445
theorem B5279843 : Blo 1389514 5279843 := bstep (se 1 (by rfl) ⟨3959882, by rfl⟩ : syracuseStep 5279843 = 7919765) B7919765
theorem B2347123 : Blo 1389514 2347123 := bstep (se 1 (by rfl) ⟨1760342, by rfl⟩ : syracuseStep 2347123 = 3520685) B3520685
theorem B2084993 : Blo 1389514 2084993 := bstep (se 2 (by rfl) ⟨781872, by rfl⟩ : syracuseStep 2084993 = 1563745) B1563745
theorem B4690061 : Blo 1389514 4690061 := bstep (se 3 (by rfl) ⟨879386, by rfl⟩ : syracuseStep 4690061 = 1758773) B1758773
theorem B2085011 : Blo 1389514 2085011 := bstep (se 1 (by rfl) ⟨1563758, by rfl⟩ : syracuseStep 2085011 = 3127517) B3127517
theorem B2085041 : Blo 1389514 2085041 := bstep (se 2 (by rfl) ⟨781890, by rfl⟩ : syracuseStep 2085041 = 1563781) B1563781
theorem B4690115 : Blo 1389514 4690115 := bstep (se 1 (by rfl) ⟨3517586, by rfl⟩ : syracuseStep 4690115 = 7035173) B7035173
theorem B2085059 : Blo 1389514 2085059 := bstep (se 1 (by rfl) ⟨1563794, by rfl⟩ : syracuseStep 2085059 = 3127589) B3127589
theorem B26726597 : Blo 1389514 26726597 := bstep (se 4 (by rfl) ⟨2505618, by rfl⟩ : syracuseStep 26726597 = 5011237) B5011237
theorem B2085089 : Blo 1389514 2085089 := bstep (se 2 (by rfl) ⟨781908, by rfl⟩ : syracuseStep 2085089 = 1563817) B1563817
theorem B1978609 : Blo 1389514 1978609 := bstep (se 2 (by rfl) ⟨741978, by rfl⟩ : syracuseStep 1978609 = 1483957) B1483957
theorem B2085107 : Blo 1389514 2085107 := bstep (se 1 (by rfl) ⟨1563830, by rfl⟩ : syracuseStep 2085107 = 3127661) B3127661
theorem B2347265 : Blo 1389514 2347265 := bstep (se 2 (by rfl) ⟨880224, by rfl⟩ : syracuseStep 2347265 = 1760449) B1760449
theorem B2085137 : Blo 1389514 2085137 := bstep (se 2 (by rfl) ⟨781926, by rfl⟩ : syracuseStep 2085137 = 1563853) B1563853
theorem B1880339 : Blo 1389514 1880339 := bstep (se 1 (by rfl) ⟨1410254, by rfl⟩ : syracuseStep 1880339 = 2820509) B2820509
theorem B2085155 : Blo 1389514 2085155 := bstep (se 1 (by rfl) ⟨1563866, by rfl⟩ : syracuseStep 2085155 = 3127733) B3127733
theorem B7041329 : Blo 1389514 7041329 := bstep (se 2 (by rfl) ⟨2640498, by rfl⟩ : syracuseStep 7041329 = 5280997) B5280997
theorem B1880371 : Blo 1389514 1880371 := bstep (se 1 (by rfl) ⟨1410278, by rfl⟩ : syracuseStep 1880371 = 2820557) B2820557
theorem B2085185 : Blo 1389514 2085185 := bstep (se 2 (by rfl) ⟨781944, by rfl⟩ : syracuseStep 2085185 = 1563889) B1563889
theorem B2085203 : Blo 1389514 2085203 := bstep (se 1 (by rfl) ⟨1563902, by rfl⟩ : syracuseStep 2085203 = 3127805) B3127805
theorem B2085233 : Blo 1389514 2085233 := bstep (se 2 (by rfl) ⟨781962, by rfl⟩ : syracuseStep 2085233 = 1563925) B1563925
theorem B2347393 : Blo 1389514 2347393 := bstep (se 2 (by rfl) ⟨880272, by rfl⟩ : syracuseStep 2347393 = 1760545) B1760545
theorem B2085251 : Blo 1389514 2085251 := bstep (se 1 (by rfl) ⟨1563938, by rfl⟩ : syracuseStep 2085251 = 3127877) B3127877
theorem B2085281 : Blo 1389514 2085281 := bstep (se 2 (by rfl) ⟨781980, by rfl⟩ : syracuseStep 2085281 = 1563961) B1563961
theorem B2347427 : Blo 1389514 2347427 := bstep (se 1 (by rfl) ⟨1760570, by rfl⟩ : syracuseStep 2347427 = 3521141) B3521141
theorem B2085299 : Blo 1389514 2085299 := bstep (se 1 (by rfl) ⟨1563974, by rfl⟩ : syracuseStep 2085299 = 3127949) B3127949
theorem B4690385 : Blo 1389514 4690385 := bstep (se 2 (by rfl) ⟨1758894, by rfl⟩ : syracuseStep 4690385 = 3517789) B3517789
theorem B2085329 : Blo 1389514 2085329 := bstep (se 2 (by rfl) ⟨781998, by rfl⟩ : syracuseStep 2085329 = 1563997) B1563997
theorem B6017507 : Blo 1389514 6017507 := bstep (se 1 (by rfl) ⟨4513130, by rfl⟩ : syracuseStep 6017507 = 9026261) B9026261
theorem B2085347 : Blo 1389514 2085347 := bstep (se 1 (by rfl) ⟨1564010, by rfl⟩ : syracuseStep 2085347 = 3128021) B3128021
theorem B2970083 : Blo 1389514 2970083 := bstep (se 1 (by rfl) ⟨2227562, by rfl⟩ : syracuseStep 2970083 = 4455125) B4455125
theorem B2085377 : Blo 1389514 2085377 := bstep (se 2 (by rfl) ⟨782016, by rfl⟩ : syracuseStep 2085377 = 1564033) B1564033
theorem B2085395 : Blo 1389514 2085395 := bstep (se 1 (by rfl) ⟨1564046, by rfl⟩ : syracuseStep 2085395 = 3128093) B3128093
theorem B2347555 : Blo 1389514 2347555 := bstep (se 1 (by rfl) ⟨1760666, by rfl⟩ : syracuseStep 2347555 = 3521333) B3521333
theorem B2085425 : Blo 1389514 2085425 := bstep (se 2 (by rfl) ⟨782034, by rfl⟩ : syracuseStep 2085425 = 1564069) B1564069
theorem B2085443 : Blo 1389514 2085443 := bstep (se 1 (by rfl) ⟨1564082, by rfl⟩ : syracuseStep 2085443 = 3128165) B3128165
theorem B2085473 : Blo 1389514 2085473 := bstep (se 2 (by rfl) ⟨782052, by rfl⟩ : syracuseStep 2085473 = 1564105) B1564105
theorem B2085491 : Blo 1389514 2085491 := bstep (se 1 (by rfl) ⟨1564118, by rfl⟩ : syracuseStep 2085491 = 3128237) B3128237
theorem B2085521 : Blo 1389514 2085521 := bstep (se 2 (by rfl) ⟨782070, by rfl⟩ : syracuseStep 2085521 = 1564141) B1564141
theorem B2085539 : Blo 1389514 2085539 := bstep (se 1 (by rfl) ⟨1564154, by rfl⟩ : syracuseStep 2085539 = 3128309) B3128309
theorem B2347697 : Blo 1389514 2347697 := bstep (se 2 (by rfl) ⟨880386, by rfl⟩ : syracuseStep 2347697 = 1760773) B1760773
theorem B2085569 : Blo 1389514 2085569 := bstep (se 2 (by rfl) ⟨782088, by rfl⟩ : syracuseStep 2085569 = 1564177) B1564177
theorem B2085587 : Blo 1389514 2085587 := bstep (se 1 (by rfl) ⟨1564190, by rfl⟩ : syracuseStep 2085587 = 3128381) B3128381
theorem B7918307 : Blo 1389514 7918307 := bstep (se 1 (by rfl) ⟨5938730, by rfl⟩ : syracuseStep 7918307 = 11877461) B11877461
theorem B2085617 : Blo 1389514 2085617 := bstep (se 2 (by rfl) ⟨782106, by rfl⟩ : syracuseStep 2085617 = 1564213) B1564213
theorem B5280497 : Blo 1389514 5280497 := bstep (se 2 (by rfl) ⟨1980186, by rfl⟩ : syracuseStep 5280497 = 3960373) B3960373
theorem B2085635 : Blo 1389514 2085635 := bstep (se 1 (by rfl) ⟨1564226, by rfl⟩ : syracuseStep 2085635 = 3128453) B3128453
theorem B2085665 : Blo 1389514 2085665 := bstep (se 2 (by rfl) ⟨782124, by rfl⟩ : syracuseStep 2085665 = 1564249) B1564249
theorem B3961649 : Blo 1389514 3961649 := bstep (se 2 (by rfl) ⟨1485618, by rfl⟩ : syracuseStep 3961649 = 2971237) B2971237
theorem B2347825 : Blo 1389514 2347825 := bstep (se 2 (by rfl) ⟨880434, by rfl⟩ : syracuseStep 2347825 = 1760869) B1760869
theorem B2085683 : Blo 1389514 2085683 := bstep (se 1 (by rfl) ⟨1564262, by rfl⟩ : syracuseStep 2085683 = 3128525) B3128525
theorem B1979201 : Blo 1389514 1979201 := bstep (se 2 (by rfl) ⟨742200, by rfl⟩ : syracuseStep 1979201 = 1484401) B1484401
theorem B2085713 : Blo 1389514 2085713 := bstep (se 2 (by rfl) ⟨782142, by rfl⟩ : syracuseStep 2085713 = 1564285) B1564285
theorem B2347859 : Blo 1389514 2347859 := bstep (se 1 (by rfl) ⟨1760894, by rfl⟩ : syracuseStep 2347859 = 3521789) B3521789
theorem B2085731 : Blo 1389514 2085731 := bstep (se 1 (by rfl) ⟨1564298, by rfl⟩ : syracuseStep 2085731 = 3128597) B3128597
theorem B19280753 : Blo 1389514 19280753 := bstep (se 2 (by rfl) ⟨7230282, by rfl⟩ : syracuseStep 19280753 = 14460565) B14460565
theorem B2085761 : Blo 1389514 2085761 := bstep (se 2 (by rfl) ⟨782160, by rfl⟩ : syracuseStep 2085761 = 1564321) B1564321
theorem B2085779 : Blo 1389514 2085779 := bstep (se 1 (by rfl) ⟨1564334, by rfl⟩ : syracuseStep 2085779 = 3128669) B3128669
theorem B3519409 : Blo 1389514 3519409 := bstep (se 2 (by rfl) ⟨1319778, by rfl⟩ : syracuseStep 3519409 = 2639557) B2639557
theorem B2085809 : Blo 1389514 2085809 := bstep (se 2 (by rfl) ⟨782178, by rfl⟩ : syracuseStep 2085809 = 1564357) B1564357
theorem B2085827 : Blo 1389514 2085827 := bstep (se 1 (by rfl) ⟨1564370, by rfl⟩ : syracuseStep 2085827 = 3128741) B3128741
theorem B17830853 : Blo 1389514 17830853 := bstep (se 4 (by rfl) ⟨1671642, by rfl⟩ : syracuseStep 17830853 = 3343285) B3343285
theorem B1389523 : Blo 1389514 1389523 := bstep (se 1 (by rfl) ⟨1042142, by rfl⟩ : syracuseStep 1389523 = 2084285) B2084285
theorem B2347987 : Blo 1389514 2347987 := bstep (se 1 (by rfl) ⟨1760990, by rfl⟩ : syracuseStep 2347987 = 3521981) B3521981
theorem B2085857 : Blo 1389514 2085857 := bstep (se 2 (by rfl) ⟨782196, by rfl⟩ : syracuseStep 2085857 = 1564393) B1564393
theorem B1389539 : Blo 1389514 1389539 := bstep (se 1 (by rfl) ⟨1042154, by rfl⟩ : syracuseStep 1389539 = 2084309) B2084309
theorem B4690925 : Blo 1389514 4690925 := bstep (se 3 (by rfl) ⟨879548, by rfl⟩ : syracuseStep 4690925 = 1759097) B1759097
theorem B1389555 : Blo 1389514 1389555 := bstep (se 1 (by rfl) ⟨1042166, by rfl⟩ : syracuseStep 1389555 = 2084333) B2084333
theorem B2085875 : Blo 1389514 2085875 := bstep (se 1 (by rfl) ⟨1564406, by rfl⟩ : syracuseStep 2085875 = 3128813) B3128813
theorem B1389571 : Blo 1389514 1389571 := bstep (se 1 (by rfl) ⟨1042178, by rfl⟩ : syracuseStep 1389571 = 2084357) B2084357
theorem B2085905 : Blo 1389514 2085905 := bstep (se 2 (by rfl) ⟨782214, by rfl⟩ : syracuseStep 2085905 = 1564429) B1564429
theorem B1389587 : Blo 1389514 1389587 := bstep (se 1 (by rfl) ⟨1042190, by rfl⟩ : syracuseStep 1389587 = 2084381) B2084381
theorem B1389603 : Blo 1389514 1389603 := bstep (se 1 (by rfl) ⟨1042202, by rfl⟩ : syracuseStep 1389603 = 2084405) B2084405
theorem B4690979 : Blo 1389514 4690979 := bstep (se 1 (by rfl) ⟨3518234, by rfl⟩ : syracuseStep 4690979 = 7036469) B7036469
theorem B2085923 : Blo 1389514 2085923 := bstep (se 1 (by rfl) ⟨1564442, by rfl⟩ : syracuseStep 2085923 = 3128885) B3128885
theorem B1389619 : Blo 1389514 1389619 := bstep (se 1 (by rfl) ⟨1042214, by rfl⟩ : syracuseStep 1389619 = 2084429) B2084429
theorem B2085953 : Blo 1389514 2085953 := bstep (se 2 (by rfl) ⟨782232, by rfl⟩ : syracuseStep 2085953 = 1564465) B1564465
theorem B1389635 : Blo 1389514 1389635 := bstep (se 1 (by rfl) ⟨1042226, by rfl⟩ : syracuseStep 1389635 = 2084453) B2084453
theorem B1389651 : Blo 1389514 1389651 := bstep (se 1 (by rfl) ⟨1042238, by rfl⟩ : syracuseStep 1389651 = 2084477) B2084477
theorem B2085971 : Blo 1389514 2085971 := bstep (se 1 (by rfl) ⟨1564478, by rfl⟩ : syracuseStep 2085971 = 3128957) B3128957
theorem B2348129 : Blo 1389514 2348129 := bstep (se 2 (by rfl) ⟨880548, by rfl⟩ : syracuseStep 2348129 = 1761097) B1761097
theorem B1389667 : Blo 1389514 1389667 := bstep (se 1 (by rfl) ⟨1042250, by rfl⟩ : syracuseStep 1389667 = 2084501) B2084501
theorem B2086001 : Blo 1389514 2086001 := bstep (se 2 (by rfl) ⟨782250, by rfl⟩ : syracuseStep 2086001 = 1564501) B1564501
theorem B1389683 : Blo 1389514 1389683 := bstep (se 1 (by rfl) ⟨1042262, by rfl⟩ : syracuseStep 1389683 = 2084525) B2084525
theorem B1389699 : Blo 1389514 1389699 := bstep (se 1 (by rfl) ⟨1042274, by rfl⟩ : syracuseStep 1389699 = 2084549) B2084549
theorem B2086019 : Blo 1389514 2086019 := bstep (se 1 (by rfl) ⟨1564514, by rfl⟩ : syracuseStep 2086019 = 3129029) B3129029
theorem B1389715 : Blo 1389514 1389715 := bstep (se 1 (by rfl) ⟨1042286, by rfl⟩ : syracuseStep 1389715 = 2084573) B2084573
theorem B2086049 : Blo 1389514 2086049 := bstep (se 2 (by rfl) ⟨782268, by rfl⟩ : syracuseStep 2086049 = 1564537) B1564537
theorem B1389731 : Blo 1389514 1389731 := bstep (se 1 (by rfl) ⟨1042298, by rfl⟩ : syracuseStep 1389731 = 2084597) B2084597
theorem B1389747 : Blo 1389514 1389747 := bstep (se 1 (by rfl) ⟨1042310, by rfl⟩ : syracuseStep 1389747 = 2084621) B2084621
theorem B2086067 : Blo 1389514 2086067 := bstep (se 1 (by rfl) ⟨1564550, by rfl⟩ : syracuseStep 2086067 = 3129101) B3129101
theorem B1389763 : Blo 1389514 1389763 := bstep (se 1 (by rfl) ⟨1042322, by rfl⟩ : syracuseStep 1389763 = 2084645) B2084645
theorem B3519683 : Blo 1389514 3519683 := bstep (se 1 (by rfl) ⟨2639762, by rfl⟩ : syracuseStep 3519683 = 5279525) B5279525
theorem B2086097 : Blo 1389514 2086097 := bstep (se 2 (by rfl) ⟨782286, by rfl⟩ : syracuseStep 2086097 = 1564573) B1564573
theorem B1389779 : Blo 1389514 1389779 := bstep (se 1 (by rfl) ⟨1042334, by rfl⟩ : syracuseStep 1389779 = 2084669) B2084669
theorem B1389795 : Blo 1389514 1389795 := bstep (se 1 (by rfl) ⟨1042346, by rfl⟩ : syracuseStep 1389795 = 2084693) B2084693
theorem B17814755 : Blo 1389514 17814755 := bstep (se 1 (by rfl) ⟨13361066, by rfl⟩ : syracuseStep 17814755 = 26722133) B26722133
theorem B2086115 : Blo 1389514 2086115 := bstep (se 1 (by rfl) ⟨1564586, by rfl⟩ : syracuseStep 2086115 = 3129173) B3129173
theorem B4453613 : Blo 1389514 4453613 := bstep (se 3 (by rfl) ⟨835052, by rfl⟩ : syracuseStep 4453613 = 1670105) B1670105
theorem B1389811 : Blo 1389514 1389811 := bstep (se 1 (by rfl) ⟨1042358, by rfl⟩ : syracuseStep 1389811 = 2084717) B2084717
theorem B2086145 : Blo 1389514 2086145 := bstep (se 2 (by rfl) ⟨782304, by rfl⟩ : syracuseStep 2086145 = 1564609) B1564609
theorem B1389827 : Blo 1389514 1389827 := bstep (se 1 (by rfl) ⟨1042370, by rfl⟩ : syracuseStep 1389827 = 2084741) B2084741
theorem B3126545 : Blo 1389514 3126545 := bstep (se 2 (by rfl) ⟨1172454, by rfl⟩ : syracuseStep 3126545 = 2344909) B2344909
theorem B1389843 : Blo 1389514 1389843 := bstep (se 1 (by rfl) ⟨1042382, by rfl⟩ : syracuseStep 1389843 = 2084765) B2084765
theorem B2086163 : Blo 1389514 2086163 := bstep (se 1 (by rfl) ⟨1564622, by rfl⟩ : syracuseStep 2086163 = 3129245) B3129245
theorem B3126563 : Blo 1389514 3126563 := bstep (se 1 (by rfl) ⟨2344922, by rfl⟩ : syracuseStep 3126563 = 4689845) B4689845
theorem B1389859 : Blo 1389514 1389859 := bstep (se 1 (by rfl) ⟨1042394, by rfl⟩ : syracuseStep 1389859 = 2084789) B2084789
theorem B4691249 : Blo 1389514 4691249 := bstep (se 2 (by rfl) ⟨1759218, by rfl⟩ : syracuseStep 4691249 = 3518437) B3518437
theorem B2086193 : Blo 1389514 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B1389875 : Blo 1389514 1389875 := bstep (se 1 (by rfl) ⟨1042406, by rfl⟩ : syracuseStep 1389875 = 2084813) B2084813
theorem B1389891 : Blo 1389514 1389891 := bstep (se 1 (by rfl) ⟨1042418, by rfl⟩ : syracuseStep 1389891 = 2084837) B2084837
theorem B2086211 : Blo 1389514 2086211 := bstep (se 1 (by rfl) ⟨1564658, by rfl⟩ : syracuseStep 2086211 = 3129317) B3129317
theorem B1389907 : Blo 1389514 1389907 := bstep (se 1 (by rfl) ⟨1042430, by rfl⟩ : syracuseStep 1389907 = 2084861) B2084861
theorem B1979731 : Blo 1389514 1979731 := bstep (se 1 (by rfl) ⟨1484798, by rfl⟩ : syracuseStep 1979731 = 2969597) B2969597
theorem B2086241 : Blo 1389514 2086241 := bstep (se 2 (by rfl) ⟨782340, by rfl⟩ : syracuseStep 2086241 = 1564681) B1564681
theorem B1389923 : Blo 1389514 1389923 := bstep (se 1 (by rfl) ⟨1042442, by rfl⟩ : syracuseStep 1389923 = 2084885) B2084885
theorem B1389939 : Blo 1389514 1389939 := bstep (se 1 (by rfl) ⟨1042454, by rfl⟩ : syracuseStep 1389939 = 2084909) B2084909
theorem B2086259 : Blo 1389514 2086259 := bstep (se 1 (by rfl) ⟨1564694, by rfl⟩ : syracuseStep 2086259 = 3129389) B3129389
theorem B1389955 : Blo 1389514 1389955 := bstep (se 1 (by rfl) ⟨1042466, by rfl⟩ : syracuseStep 1389955 = 2084933) B2084933
theorem B3519875 : Blo 1389514 3519875 := bstep (se 1 (by rfl) ⟨2639906, by rfl⟩ : syracuseStep 3519875 = 5279813) B5279813
theorem B25703821 : Blo 1389514 25703821 := bstep (se 3 (by rfl) ⟨4819466, by rfl⟩ : syracuseStep 25703821 = 9638933) B9638933
theorem B2086289 : Blo 1389514 2086289 := bstep (se 2 (by rfl) ⟨782358, by rfl⟩ : syracuseStep 2086289 = 1564717) B1564717
theorem B1758611 : Blo 1389514 1758611 := bstep (se 1 (by rfl) ⟨1318958, by rfl⟩ : syracuseStep 1758611 = 2637917) B2637917
theorem B1389971 : Blo 1389514 1389971 := bstep (se 1 (by rfl) ⟨1042478, by rfl⟩ : syracuseStep 1389971 = 2084957) B2084957
theorem B1389987 : Blo 1389514 1389987 := bstep (se 1 (by rfl) ⟨1042490, by rfl⟩ : syracuseStep 1389987 = 2084981) B2084981
theorem B2086307 : Blo 1389514 2086307 := bstep (se 1 (by rfl) ⟨1564730, by rfl⟩ : syracuseStep 2086307 = 3129461) B3129461
theorem B1390003 : Blo 1389514 1390003 := bstep (se 1 (by rfl) ⟨1042502, by rfl⟩ : syracuseStep 1390003 = 2085005) B2085005
theorem B2086337 : Blo 1389514 2086337 := bstep (se 2 (by rfl) ⟨782376, by rfl⟩ : syracuseStep 2086337 = 1564753) B1564753
theorem B1390019 : Blo 1389514 1390019 := bstep (se 1 (by rfl) ⟨1042514, by rfl⟩ : syracuseStep 1390019 = 2085029) B2085029
theorem B9024965 : Blo 1389514 9024965 := bstep (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) B1692181
theorem B25368005 : Blo 1389514 25368005 := bstep (se 4 (by rfl) ⟨2378250, by rfl⟩ : syracuseStep 25368005 = 4756501) B4756501
theorem B3962321 : Blo 1389514 3962321 := bstep (se 2 (by rfl) ⟨1485870, by rfl⟩ : syracuseStep 3962321 = 2971741) B2971741
theorem B1390035 : Blo 1389514 1390035 := bstep (se 1 (by rfl) ⟨1042526, by rfl⟩ : syracuseStep 1390035 = 2085053) B2085053
theorem B2086355 : Blo 1389514 2086355 := bstep (se 1 (by rfl) ⟨1564766, by rfl⟩ : syracuseStep 2086355 = 3129533) B3129533
theorem B1390051 : Blo 1389514 1390051 := bstep (se 1 (by rfl) ⟨1042538, by rfl⟩ : syracuseStep 1390051 = 2085077) B2085077
theorem B2086385 : Blo 1389514 2086385 := bstep (se 2 (by rfl) ⟨782394, by rfl⟩ : syracuseStep 2086385 = 1564789) B1564789
theorem B1390067 : Blo 1389514 1390067 := bstep (se 1 (by rfl) ⟨1042550, by rfl⟩ : syracuseStep 1390067 = 2085101) B2085101
theorem B1390083 : Blo 1389514 1390083 := bstep (se 1 (by rfl) ⟨1042562, by rfl⟩ : syracuseStep 1390083 = 2085125) B2085125
theorem B2086403 : Blo 1389514 2086403 := bstep (se 1 (by rfl) ⟨1564802, by rfl⟩ : syracuseStep 2086403 = 3129605) B3129605
theorem B3757585 : Blo 1389514 3757585 := bstep (se 2 (by rfl) ⟨1409094, by rfl⟩ : syracuseStep 3757585 = 2818189) B2818189
theorem B1390099 : Blo 1389514 1390099 := bstep (se 1 (by rfl) ⟨1042574, by rfl⟩ : syracuseStep 1390099 = 2085149) B2085149
theorem B2086433 : Blo 1389514 2086433 := bstep (se 2 (by rfl) ⟨782412, by rfl⟩ : syracuseStep 2086433 = 1564825) B1564825
theorem B1390115 : Blo 1389514 1390115 := bstep (se 1 (by rfl) ⟨1042586, by rfl⟩ : syracuseStep 1390115 = 2085173) B2085173
theorem B3126833 : Blo 1389514 3126833 := bstep (se 2 (by rfl) ⟨1172562, by rfl⟩ : syracuseStep 3126833 = 2345125) B2345125
theorem B1390131 : Blo 1389514 1390131 := bstep (se 1 (by rfl) ⟨1042598, by rfl⟩ : syracuseStep 1390131 = 2085197) B2085197
theorem B2086451 : Blo 1389514 2086451 := bstep (se 1 (by rfl) ⟨1564838, by rfl⟩ : syracuseStep 2086451 = 3129677) B3129677
theorem B3126851 : Blo 1389514 3126851 := bstep (se 1 (by rfl) ⟨2345138, by rfl⟩ : syracuseStep 3126851 = 4690277) B4690277
theorem B1390147 : Blo 1389514 1390147 := bstep (se 1 (by rfl) ⟨1042610, by rfl⟩ : syracuseStep 1390147 = 2085221) B2085221
theorem B2086481 : Blo 1389514 2086481 := bstep (se 2 (by rfl) ⟨782430, by rfl⟩ : syracuseStep 2086481 = 1564861) B1564861
theorem B1390163 : Blo 1389514 1390163 := bstep (se 1 (by rfl) ⟨1042622, by rfl⟩ : syracuseStep 1390163 = 2085245) B2085245
theorem B1390179 : Blo 1389514 1390179 := bstep (se 1 (by rfl) ⟨1042634, by rfl⟩ : syracuseStep 1390179 = 2085269) B2085269
theorem B2086499 : Blo 1389514 2086499 := bstep (se 1 (by rfl) ⟨1564874, by rfl⟩ : syracuseStep 2086499 = 3129749) B3129749
theorem B1390195 : Blo 1389514 1390195 := bstep (se 1 (by rfl) ⟨1042646, by rfl⟩ : syracuseStep 1390195 = 2085293) B2085293
theorem B2086529 : Blo 1389514 2086529 := bstep (se 2 (by rfl) ⟨782448, by rfl⟩ : syracuseStep 2086529 = 1564897) B1564897
theorem B1390211 : Blo 1389514 1390211 := bstep (se 1 (by rfl) ⟨1042658, by rfl⟩ : syracuseStep 1390211 = 2085317) B2085317
theorem B1390227 : Blo 1389514 1390227 := bstep (se 1 (by rfl) ⟨1042670, by rfl⟩ : syracuseStep 1390227 = 2085341) B2085341
theorem B2086547 : Blo 1389514 2086547 := bstep (se 1 (by rfl) ⟨1564910, by rfl⟩ : syracuseStep 2086547 = 3129821) B3129821
theorem B1390243 : Blo 1389514 1390243 := bstep (se 1 (by rfl) ⟨1042682, by rfl⟩ : syracuseStep 1390243 = 2085365) B2085365
theorem B1980067 : Blo 1389514 1980067 := bstep (se 1 (by rfl) ⟨1485050, by rfl⟩ : syracuseStep 1980067 = 2970101) B2970101
theorem B2086577 : Blo 1389514 2086577 := bstep (se 2 (by rfl) ⟨782466, by rfl⟩ : syracuseStep 2086577 = 1564933) B1564933
theorem B1390259 : Blo 1389514 1390259 := bstep (se 1 (by rfl) ⟨1042694, by rfl⟩ : syracuseStep 1390259 = 2085389) B2085389
theorem B1390275 : Blo 1389514 1390275 := bstep (se 1 (by rfl) ⟨1042706, by rfl⟩ : syracuseStep 1390275 = 2085413) B2085413
theorem B2086595 : Blo 1389514 2086595 := bstep (se 1 (by rfl) ⟨1564946, by rfl⟩ : syracuseStep 2086595 = 3129893) B3129893
theorem B7919309 : Blo 1389514 7919309 := bstep (se 3 (by rfl) ⟨1484870, by rfl⟩ : syracuseStep 7919309 = 2969741) B2969741
theorem B1390291 : Blo 1389514 1390291 := bstep (se 1 (by rfl) ⟨1042718, by rfl⟩ : syracuseStep 1390291 = 2085437) B2085437
theorem B2086625 : Blo 1389514 2086625 := bstep (se 2 (by rfl) ⟨782484, by rfl⟩ : syracuseStep 2086625 = 1564969) B1564969
theorem B1390307 : Blo 1389514 1390307 := bstep (se 1 (by rfl) ⟨1042730, by rfl⟩ : syracuseStep 1390307 = 2085461) B2085461
theorem B7042787 : Blo 1389514 7042787 := bstep (se 1 (by rfl) ⟨5282090, by rfl⟩ : syracuseStep 7042787 = 10564181) B10564181
theorem B1390323 : Blo 1389514 1390323 := bstep (se 1 (by rfl) ⟨1042742, by rfl⟩ : syracuseStep 1390323 = 2085485) B2085485
theorem B2086643 : Blo 1389514 2086643 := bstep (se 1 (by rfl) ⟨1564982, by rfl⟩ : syracuseStep 2086643 = 3129965) B3129965
theorem B1390339 : Blo 1389514 1390339 := bstep (se 1 (by rfl) ⟨1042754, by rfl⟩ : syracuseStep 1390339 = 2085509) B2085509
theorem B2086673 : Blo 1389514 2086673 := bstep (se 2 (by rfl) ⟨782502, by rfl⟩ : syracuseStep 2086673 = 1565005) B1565005
theorem B1390355 : Blo 1389514 1390355 := bstep (se 1 (by rfl) ⟨1042766, by rfl⟩ : syracuseStep 1390355 = 2085533) B2085533
theorem B1390371 : Blo 1389514 1390371 := bstep (se 1 (by rfl) ⟨1042778, by rfl⟩ : syracuseStep 1390371 = 2085557) B2085557
theorem B2086691 : Blo 1389514 2086691 := bstep (se 1 (by rfl) ⟨1565018, by rfl⟩ : syracuseStep 2086691 = 3130037) B3130037
theorem B1390387 : Blo 1389514 1390387 := bstep (se 1 (by rfl) ⟨1042790, by rfl⟩ : syracuseStep 1390387 = 2085581) B2085581
theorem B2086721 : Blo 1389514 2086721 := bstep (se 2 (by rfl) ⟨782520, by rfl⟩ : syracuseStep 2086721 = 1565041) B1565041
theorem B1390403 : Blo 1389514 1390403 := bstep (se 1 (by rfl) ⟨1042802, by rfl⟩ : syracuseStep 1390403 = 2085605) B2085605
theorem B4691789 : Blo 1389514 4691789 := bstep (se 3 (by rfl) ⟨879710, by rfl⟩ : syracuseStep 4691789 = 1759421) B1759421
theorem B3127121 : Blo 1389514 3127121 := bstep (se 2 (by rfl) ⟨1172670, by rfl⟩ : syracuseStep 3127121 = 2345341) B2345341
theorem B1390419 : Blo 1389514 1390419 := bstep (se 1 (by rfl) ⟨1042814, by rfl⟩ : syracuseStep 1390419 = 2085629) B2085629
theorem B2086739 : Blo 1389514 2086739 := bstep (se 1 (by rfl) ⟨1565054, by rfl⟩ : syracuseStep 2086739 = 3130109) B3130109
theorem B3127139 : Blo 1389514 3127139 := bstep (se 1 (by rfl) ⟨2345354, by rfl⟩ : syracuseStep 3127139 = 4690709) B4690709
theorem B1390435 : Blo 1389514 1390435 := bstep (se 1 (by rfl) ⟨1042826, by rfl⟩ : syracuseStep 1390435 = 2085653) B2085653
theorem B2086769 : Blo 1389514 2086769 := bstep (se 2 (by rfl) ⟨782538, by rfl⟩ : syracuseStep 2086769 = 1565077) B1565077
theorem B1390451 : Blo 1389514 1390451 := bstep (se 1 (by rfl) ⟨1042838, by rfl⟩ : syracuseStep 1390451 = 2085677) B2085677
theorem B4691843 : Blo 1389514 4691843 := bstep (se 1 (by rfl) ⟨3518882, by rfl⟩ : syracuseStep 4691843 = 7037765) B7037765
theorem B1390467 : Blo 1389514 1390467 := bstep (se 1 (by rfl) ⟨1042850, by rfl⟩ : syracuseStep 1390467 = 2085701) B2085701
theorem B2086787 : Blo 1389514 2086787 := bstep (se 1 (by rfl) ⟨1565090, by rfl⟩ : syracuseStep 2086787 = 3130181) B3130181
theorem B23746445 : Blo 1389514 23746445 := bstep (se 3 (by rfl) ⟨4452458, by rfl⟩ : syracuseStep 23746445 = 8904917) B8904917
theorem B4757393 : Blo 1389514 4757393 := bstep (se 2 (by rfl) ⟨1784022, by rfl⟩ : syracuseStep 4757393 = 3568045) B3568045
theorem B1390483 : Blo 1389514 1390483 := bstep (se 1 (by rfl) ⟨1042862, by rfl⟩ : syracuseStep 1390483 = 2085725) B2085725
theorem B2086817 : Blo 1389514 2086817 := bstep (se 2 (by rfl) ⟨782556, by rfl⟩ : syracuseStep 2086817 = 1565113) B1565113
theorem B1390499 : Blo 1389514 1390499 := bstep (se 1 (by rfl) ⟨1042874, by rfl⟩ : syracuseStep 1390499 = 2085749) B2085749
theorem B4011949 : Blo 1389514 4011949 := bstep (se 3 (by rfl) ⟨752240, by rfl⟩ : syracuseStep 4011949 = 1504481) B1504481
theorem B1390515 : Blo 1389514 1390515 := bstep (se 1 (by rfl) ⟨1042886, by rfl⟩ : syracuseStep 1390515 = 2085773) B2085773
theorem B2086835 : Blo 1389514 2086835 := bstep (se 1 (by rfl) ⟨1565126, by rfl⟩ : syracuseStep 2086835 = 3130253) B3130253
theorem B1390531 : Blo 1389514 1390531 := bstep (se 1 (by rfl) ⟨1042898, by rfl⟩ : syracuseStep 1390531 = 2085797) B2085797
theorem B2086865 : Blo 1389514 2086865 := bstep (se 2 (by rfl) ⟨782574, by rfl⟩ : syracuseStep 2086865 = 1565149) B1565149
theorem B1390547 : Blo 1389514 1390547 := bstep (se 1 (by rfl) ⟨1042910, by rfl⟩ : syracuseStep 1390547 = 2085821) B2085821
theorem B1390563 : Blo 1389514 1390563 := bstep (se 1 (by rfl) ⟨1042922, by rfl⟩ : syracuseStep 1390563 = 2085845) B2085845
theorem B9517027 : Blo 1389514 9517027 := bstep (se 1 (by rfl) ⟨7137770, by rfl⟩ : syracuseStep 9517027 = 14275541) B14275541
theorem B2086883 : Blo 1389514 2086883 := bstep (se 1 (by rfl) ⟨1565162, by rfl⟩ : syracuseStep 2086883 = 3130325) B3130325
theorem B1390579 : Blo 1389514 1390579 := bstep (se 1 (by rfl) ⟨1042934, by rfl⟩ : syracuseStep 1390579 = 2085869) B2085869
theorem B2086913 : Blo 1389514 2086913 := bstep (se 2 (by rfl) ⟨782592, by rfl⟩ : syracuseStep 2086913 = 1565185) B1565185
theorem B2226179 : Blo 1389514 2226179 := bstep (se 1 (by rfl) ⟨1669634, by rfl⟩ : syracuseStep 2226179 = 3339269) B3339269
theorem B1390595 : Blo 1389514 1390595 := bstep (se 1 (by rfl) ⟨1042946, by rfl⟩ : syracuseStep 1390595 = 2085893) B2085893
theorem B1390611 : Blo 1389514 1390611 := bstep (se 1 (by rfl) ⟨1042958, by rfl⟩ : syracuseStep 1390611 = 2085917) B2085917
theorem B2086931 : Blo 1389514 2086931 := bstep (se 1 (by rfl) ⟨1565198, by rfl⟩ : syracuseStep 2086931 = 3130397) B3130397
theorem B1390627 : Blo 1389514 1390627 := bstep (se 1 (by rfl) ⟨1042970, by rfl⟩ : syracuseStep 1390627 = 2085941) B2085941
theorem B2086961 : Blo 1389514 2086961 := bstep (se 2 (by rfl) ⟨782610, by rfl⟩ : syracuseStep 2086961 = 1565221) B1565221
theorem B1390643 : Blo 1389514 1390643 := bstep (se 1 (by rfl) ⟨1042982, by rfl⟩ : syracuseStep 1390643 = 2085965) B2085965
theorem B1390659 : Blo 1389514 1390659 := bstep (se 1 (by rfl) ⟨1042994, by rfl⟩ : syracuseStep 1390659 = 2085989) B2085989
theorem B2086979 : Blo 1389514 2086979 := bstep (se 1 (by rfl) ⟨1565234, by rfl⟩ : syracuseStep 2086979 = 3130469) B3130469
theorem B8910917 : Blo 1389514 8910917 := bstep (se 4 (by rfl) ⟨835398, by rfl⟩ : syracuseStep 8910917 = 1670797) B1670797
theorem B1759315 : Blo 1389514 1759315 := bstep (se 1 (by rfl) ⟨1319486, by rfl⟩ : syracuseStep 1759315 = 2638973) B2638973
theorem B1390675 : Blo 1389514 1390675 := bstep (se 1 (by rfl) ⟨1043006, by rfl⟩ : syracuseStep 1390675 = 2086013) B2086013
theorem B2087009 : Blo 1389514 2087009 := bstep (se 2 (by rfl) ⟨782628, by rfl⟩ : syracuseStep 2087009 = 1565257) B1565257
theorem B1390691 : Blo 1389514 1390691 := bstep (se 1 (by rfl) ⟨1043018, by rfl⟩ : syracuseStep 1390691 = 2086037) B2086037
theorem B4454509 : Blo 1389514 4454509 := bstep (se 3 (by rfl) ⟨835220, by rfl⟩ : syracuseStep 4454509 = 1670441) B1670441
theorem B3127409 : Blo 1389514 3127409 := bstep (se 2 (by rfl) ⟨1172778, by rfl⟩ : syracuseStep 3127409 = 2345557) B2345557
theorem B1390707 : Blo 1389514 1390707 := bstep (se 1 (by rfl) ⟨1043030, by rfl⟩ : syracuseStep 1390707 = 2086061) B2086061
theorem B2087027 : Blo 1389514 2087027 := bstep (se 1 (by rfl) ⟨1565270, by rfl⟩ : syracuseStep 2087027 = 3130541) B3130541
theorem B2226307 : Blo 1389514 2226307 := bstep (se 1 (by rfl) ⟨1669730, by rfl⟩ : syracuseStep 2226307 = 3339461) B3339461
theorem B3127427 : Blo 1389514 3127427 := bstep (se 1 (by rfl) ⟨2345570, by rfl⟩ : syracuseStep 3127427 = 4691141) B4691141
theorem B1390723 : Blo 1389514 1390723 := bstep (se 1 (by rfl) ⟨1043042, by rfl⟩ : syracuseStep 1390723 = 2086085) B2086085
theorem B4692113 : Blo 1389514 4692113 := bstep (se 2 (by rfl) ⟨1759542, by rfl⟩ : syracuseStep 4692113 = 3519085) B3519085
theorem B1390739 : Blo 1389514 1390739 := bstep (se 1 (by rfl) ⟨1043054, by rfl⟩ : syracuseStep 1390739 = 2086109) B2086109
theorem B2087057 : Blo 1389514 2087057 := bstep (se 2 (by rfl) ⟨782646, by rfl⟩ : syracuseStep 2087057 = 1565293) B1565293
theorem B1390755 : Blo 1389514 1390755 := bstep (se 1 (by rfl) ⟨1043066, by rfl⟩ : syracuseStep 1390755 = 2086133) B2086133
theorem B5281955 : Blo 1389514 5281955 := bstep (se 1 (by rfl) ⟨3961466, by rfl⟩ : syracuseStep 5281955 = 7922933) B7922933
theorem B2087075 : Blo 1389514 2087075 := bstep (se 1 (by rfl) ⟨1565306, by rfl⟩ : syracuseStep 2087075 = 3130613) B3130613
theorem B5281969 : Blo 1389514 5281969 := bstep (se 2 (by rfl) ⟨1980738, by rfl⟩ : syracuseStep 5281969 = 3961477) B3961477
theorem B1759411 : Blo 1389514 1759411 := bstep (se 1 (by rfl) ⟨1319558, by rfl⟩ : syracuseStep 1759411 = 2639117) B2639117
theorem B1390771 : Blo 1389514 1390771 := bstep (se 1 (by rfl) ⟨1043078, by rfl⟩ : syracuseStep 1390771 = 2086157) B2086157
theorem B2087105 : Blo 1389514 2087105 := bstep (se 2 (by rfl) ⟨782664, by rfl⟩ : syracuseStep 2087105 = 1565329) B1565329
theorem B1390787 : Blo 1389514 1390787 := bstep (se 1 (by rfl) ⟨1043090, by rfl⟩ : syracuseStep 1390787 = 2086181) B2086181
theorem B1980625 : Blo 1389514 1980625 := bstep (se 2 (by rfl) ⟨742734, by rfl⟩ : syracuseStep 1980625 = 1485469) B1485469
theorem B1390803 : Blo 1389514 1390803 := bstep (se 1 (by rfl) ⟨1043102, by rfl⟩ : syracuseStep 1390803 = 2086205) B2086205
theorem B2087123 : Blo 1389514 2087123 := bstep (se 1 (by rfl) ⟨1565342, by rfl⟩ : syracuseStep 2087123 = 3130685) B3130685
theorem B1390819 : Blo 1389514 1390819 := bstep (se 1 (by rfl) ⟨1043114, by rfl⟩ : syracuseStep 1390819 = 2086229) B2086229
theorem B2087153 : Blo 1389514 2087153 := bstep (se 2 (by rfl) ⟨782682, by rfl⟩ : syracuseStep 2087153 = 1565365) B1565365
theorem B1390835 : Blo 1389514 1390835 := bstep (se 1 (by rfl) ⟨1043126, by rfl⟩ : syracuseStep 1390835 = 2086253) B2086253
theorem B1980659 : Blo 1389514 1980659 := bstep (se 1 (by rfl) ⟨1485494, by rfl⟩ : syracuseStep 1980659 = 2970989) B2970989
theorem B1390851 : Blo 1389514 1390851 := bstep (se 1 (by rfl) ⟨1043138, by rfl⟩ : syracuseStep 1390851 = 2086277) B2086277
theorem B2087171 : Blo 1389514 2087171 := bstep (se 1 (by rfl) ⟨1565378, by rfl⟩ : syracuseStep 2087171 = 3130757) B3130757
theorem B1390867 : Blo 1389514 1390867 := bstep (se 1 (by rfl) ⟨1043150, by rfl⟩ : syracuseStep 1390867 = 2086301) B2086301
theorem B2087201 : Blo 1389514 2087201 := bstep (se 2 (by rfl) ⟨782700, by rfl⟩ : syracuseStep 2087201 = 1565401) B1565401
theorem B1784099 : Blo 1389514 1784099 := bstep (se 1 (by rfl) ⟨1338074, by rfl⟩ : syracuseStep 1784099 = 2676149) B2676149
theorem B1390883 : Blo 1389514 1390883 := bstep (se 1 (by rfl) ⟨1043162, by rfl⟩ : syracuseStep 1390883 = 2086325) B2086325
theorem B3520817 : Blo 1389514 3520817 := bstep (se 2 (by rfl) ⟨1320306, by rfl⟩ : syracuseStep 3520817 = 2640613) B2640613
theorem B1390899 : Blo 1389514 1390899 := bstep (se 1 (by rfl) ⟨1043174, by rfl⟩ : syracuseStep 1390899 = 2086349) B2086349
theorem B2087219 : Blo 1389514 2087219 := bstep (se 1 (by rfl) ⟨1565414, by rfl⟩ : syracuseStep 2087219 = 3130829) B3130829
theorem B1390915 : Blo 1389514 1390915 := bstep (se 1 (by rfl) ⟨1043186, by rfl⟩ : syracuseStep 1390915 = 2086373) B2086373
theorem B2087249 : Blo 1389514 2087249 := bstep (se 2 (by rfl) ⟨782718, by rfl⟩ : syracuseStep 2087249 = 1565437) B1565437
theorem B1390931 : Blo 1389514 1390931 := bstep (se 1 (by rfl) ⟨1043198, by rfl⟩ : syracuseStep 1390931 = 2086397) B2086397
theorem B1390947 : Blo 1389514 1390947 := bstep (se 1 (by rfl) ⟨1043210, by rfl⟩ : syracuseStep 1390947 = 2086421) B2086421
theorem B3520867 : Blo 1389514 3520867 := bstep (se 1 (by rfl) ⟨2640650, by rfl⟩ : syracuseStep 3520867 = 5281301) B5281301
theorem B2087267 : Blo 1389514 2087267 := bstep (se 1 (by rfl) ⟨1565450, by rfl⟩ : syracuseStep 2087267 = 3130901) B3130901
theorem B1390963 : Blo 1389514 1390963 := bstep (se 1 (by rfl) ⟨1043222, by rfl⟩ : syracuseStep 1390963 = 2086445) B2086445
theorem B1390979 : Blo 1389514 1390979 := bstep (se 1 (by rfl) ⟨1043234, by rfl⟩ : syracuseStep 1390979 = 2086469) B2086469
theorem B3127697 : Blo 1389514 3127697 := bstep (se 2 (by rfl) ⟨1172886, by rfl⟩ : syracuseStep 3127697 = 2345773) B2345773
theorem B1390995 : Blo 1389514 1390995 := bstep (se 1 (by rfl) ⟨1043246, by rfl⟩ : syracuseStep 1390995 = 2086493) B2086493
theorem B3127715 : Blo 1389514 3127715 := bstep (se 1 (by rfl) ⟨2345786, by rfl⟩ : syracuseStep 3127715 = 4691573) B4691573
theorem B1391011 : Blo 1389514 1391011 := bstep (se 1 (by rfl) ⟨1043258, by rfl⟩ : syracuseStep 1391011 = 2086517) B2086517
theorem B1391027 : Blo 1389514 1391027 := bstep (se 1 (by rfl) ⟨1043270, by rfl⟩ : syracuseStep 1391027 = 2086541) B2086541
theorem B1391043 : Blo 1389514 1391043 := bstep (se 1 (by rfl) ⟨1043282, by rfl⟩ : syracuseStep 1391043 = 2086565) B2086565
theorem B1391059 : Blo 1389514 1391059 := bstep (se 1 (by rfl) ⟨1043294, by rfl⟩ : syracuseStep 1391059 = 2086589) B2086589
theorem B1391075 : Blo 1389514 1391075 := bstep (se 1 (by rfl) ⟨1043306, by rfl⟩ : syracuseStep 1391075 = 2086613) B2086613
theorem B16062947 : Blo 1389514 16062947 := bstep (se 1 (by rfl) ⟨12047210, by rfl⟩ : syracuseStep 16062947 = 24094421) B24094421
theorem B3521009 : Blo 1389514 3521009 := bstep (se 2 (by rfl) ⟨1320378, by rfl⟩ : syracuseStep 3521009 = 2640757) B2640757
theorem B1391091 : Blo 1389514 1391091 := bstep (se 1 (by rfl) ⟨1043318, by rfl⟩ : syracuseStep 1391091 = 2086637) B2086637
theorem B2226691 : Blo 1389514 2226691 := bstep (se 1 (by rfl) ⟨1670018, by rfl⟩ : syracuseStep 2226691 = 3340037) B3340037
theorem B1391107 : Blo 1389514 1391107 := bstep (se 1 (by rfl) ⟨1043330, by rfl⟩ : syracuseStep 1391107 = 2086661) B2086661
theorem B7043597 : Blo 1389514 7043597 := bstep (se 3 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 7043597 = 2641349) B2641349
theorem B1391123 : Blo 1389514 1391123 := bstep (se 1 (by rfl) ⟨1043342, by rfl⟩ : syracuseStep 1391123 = 2086685) B2086685
theorem B1391139 : Blo 1389514 1391139 := bstep (se 1 (by rfl) ⟨1043354, by rfl⟩ : syracuseStep 1391139 = 2086709) B2086709
theorem B1391155 : Blo 1389514 1391155 := bstep (se 1 (by rfl) ⟨1043366, by rfl⟩ : syracuseStep 1391155 = 2086733) B2086733
theorem B1391171 : Blo 1389514 1391171 := bstep (se 1 (by rfl) ⟨1043378, by rfl⟩ : syracuseStep 1391171 = 2086757) B2086757
theorem B1391187 : Blo 1389514 1391187 := bstep (se 1 (by rfl) ⟨1043390, by rfl⟩ : syracuseStep 1391187 = 2086781) B2086781
theorem B1391203 : Blo 1389514 1391203 := bstep (se 1 (by rfl) ⟨1043402, by rfl⟩ : syracuseStep 1391203 = 2086805) B2086805
theorem B1391219 : Blo 1389514 1391219 := bstep (se 1 (by rfl) ⟨1043414, by rfl⟩ : syracuseStep 1391219 = 2086829) B2086829
theorem B1391235 : Blo 1389514 1391235 := bstep (se 1 (by rfl) ⟨1043426, by rfl⟩ : syracuseStep 1391235 = 2086853) B2086853
theorem B2005651 : Blo 1389514 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B1391251 : Blo 1389514 1391251 := bstep (se 1 (by rfl) ⟨1043438, by rfl⟩ : syracuseStep 1391251 = 2086877) B2086877
theorem B1759907 : Blo 1389514 1759907 := bstep (se 1 (by rfl) ⟨1319930, by rfl⟩ : syracuseStep 1759907 = 2639861) B2639861
theorem B1391267 : Blo 1389514 1391267 := bstep (se 1 (by rfl) ⟨1043450, by rfl⟩ : syracuseStep 1391267 = 2086901) B2086901
theorem B4692653 : Blo 1389514 4692653 := bstep (se 3 (by rfl) ⟨879872, by rfl⟩ : syracuseStep 4692653 = 1759745) B1759745
theorem B3127985 : Blo 1389514 3127985 := bstep (se 2 (by rfl) ⟨1172994, by rfl⟩ : syracuseStep 3127985 = 2345989) B2345989
theorem B1391283 : Blo 1389514 1391283 := bstep (se 1 (by rfl) ⟨1043462, by rfl⟩ : syracuseStep 1391283 = 2086925) B2086925
theorem B1563331 : Blo 1389514 1563331 := bstep (se 1 (by rfl) ⟨1172498, by rfl⟩ : syracuseStep 1563331 = 2344997) B2344997
theorem B3128003 : Blo 1389514 3128003 := bstep (se 1 (by rfl) ⟨2346002, by rfl⟩ : syracuseStep 3128003 = 4692005) B4692005
theorem B1391299 : Blo 1389514 1391299 := bstep (se 1 (by rfl) ⟨1043474, by rfl⟩ : syracuseStep 1391299 = 2086949) B2086949
theorem B1391315 : Blo 1389514 1391315 := bstep (se 1 (by rfl) ⟨1043486, by rfl⟩ : syracuseStep 1391315 = 2086973) B2086973
theorem B4692707 : Blo 1389514 4692707 := bstep (se 1 (by rfl) ⟨3519530, by rfl⟩ : syracuseStep 4692707 = 7039061) B7039061
theorem B1391331 : Blo 1389514 1391331 := bstep (se 1 (by rfl) ⟨1043498, by rfl⟩ : syracuseStep 1391331 = 2086997) B2086997
theorem B1391347 : Blo 1389514 1391347 := bstep (se 1 (by rfl) ⟨1043510, by rfl⟩ : syracuseStep 1391347 = 2087021) B2087021
theorem B2226947 : Blo 1389514 2226947 := bstep (se 1 (by rfl) ⟨1670210, by rfl⟩ : syracuseStep 2226947 = 3340421) B3340421
theorem B1391363 : Blo 1389514 1391363 := bstep (se 1 (by rfl) ⟨1043522, by rfl⟩ : syracuseStep 1391363 = 2087045) B2087045
theorem B1391379 : Blo 1389514 1391379 := bstep (se 1 (by rfl) ⟨1043534, by rfl⟩ : syracuseStep 1391379 = 2087069) B2087069
theorem B1981217 : Blo 1389514 1981217 := bstep (se 2 (by rfl) ⟨742956, by rfl⟩ : syracuseStep 1981217 = 1485913) B1485913
theorem B8903459 : Blo 1389514 8903459 := bstep (se 1 (by rfl) ⟨6677594, by rfl⟩ : syracuseStep 8903459 = 13355189) B13355189
theorem B1391395 : Blo 1389514 1391395 := bstep (se 1 (by rfl) ⟨1043546, by rfl⟩ : syracuseStep 1391395 = 2087093) B2087093
theorem B1391411 : Blo 1389514 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B1391427 : Blo 1389514 1391427 := bstep (se 1 (by rfl) ⟨1043570, by rfl⟩ : syracuseStep 1391427 = 2087141) B2087141
theorem B1563475 : Blo 1389514 1563475 := bstep (se 1 (by rfl) ⟨1172606, by rfl⟩ : syracuseStep 1563475 = 2345213) B2345213
theorem B1391443 : Blo 1389514 1391443 := bstep (se 1 (by rfl) ⟨1043582, by rfl⟩ : syracuseStep 1391443 = 2087165) B2087165
theorem B1391459 : Blo 1389514 1391459 := bstep (se 1 (by rfl) ⟨1043594, by rfl⟩ : syracuseStep 1391459 = 2087189) B2087189
theorem B1391475 : Blo 1389514 1391475 := bstep (se 1 (by rfl) ⟨1043606, by rfl⟩ : syracuseStep 1391475 = 2087213) B2087213
theorem B1391491 : Blo 1389514 1391491 := bstep (se 1 (by rfl) ⟨1043618, by rfl⟩ : syracuseStep 1391491 = 2087237) B2087237
theorem B10558349 : Blo 1389514 10558349 := bstep (se 3 (by rfl) ⟨1979690, by rfl⟩ : syracuseStep 10558349 = 3959381) B3959381
theorem B1391507 : Blo 1389514 1391507 := bstep (se 1 (by rfl) ⟨1043630, by rfl⟩ : syracuseStep 1391507 = 2087261) B2087261
theorem B4225969 : Blo 1389514 4225969 := bstep (se 2 (by rfl) ⟨1584738, by rfl⟩ : syracuseStep 4225969 = 3169477) B3169477
theorem B3128273 : Blo 1389514 3128273 := bstep (se 2 (by rfl) ⟨1173102, by rfl⟩ : syracuseStep 3128273 = 2346205) B2346205
theorem B1563619 : Blo 1389514 1563619 := bstep (se 1 (by rfl) ⟨1172714, by rfl⟩ : syracuseStep 1563619 = 2345429) B2345429
theorem B3128291 : Blo 1389514 3128291 := bstep (se 1 (by rfl) ⟨2346218, by rfl⟩ : syracuseStep 3128291 = 4692437) B4692437
theorem B4692977 : Blo 1389514 4692977 := bstep (se 2 (by rfl) ⟨1759866, by rfl⟩ : syracuseStep 4692977 = 3519733) B3519733
theorem B3169297 : Blo 1389514 3169297 := bstep (se 2 (by rfl) ⟨1188486, by rfl⟩ : syracuseStep 3169297 = 2376973) B2376973
theorem B3759185 : Blo 1389514 3759185 := bstep (se 2 (by rfl) ⟨1409694, by rfl⟩ : syracuseStep 3759185 = 2819389) B2819389
theorem B1563763 : Blo 1389514 1563763 := bstep (se 1 (by rfl) ⟨1172822, by rfl⟩ : syracuseStep 1563763 = 2345645) B2345645
theorem B4455587 : Blo 1389514 4455587 := bstep (se 1 (by rfl) ⟨3341690, by rfl⟩ : syracuseStep 4455587 = 6683381) B6683381
theorem B2227409 : Blo 1389514 2227409 := bstep (se 2 (by rfl) ⟨835278, by rfl⟩ : syracuseStep 2227409 = 1670557) B1670557
theorem B5012707 : Blo 1389514 5012707 := bstep (se 1 (by rfl) ⟨3759530, by rfl⟩ : syracuseStep 5012707 = 7519061) B7519061
theorem B7036145 : Blo 1389514 7036145 := bstep (se 2 (by rfl) ⟨2638554, by rfl⟩ : syracuseStep 7036145 = 5277109) B5277109
theorem B3128561 : Blo 1389514 3128561 := bstep (se 2 (by rfl) ⟨1173210, by rfl⟩ : syracuseStep 3128561 = 2346421) B2346421
theorem B1563907 : Blo 1389514 1563907 := bstep (se 1 (by rfl) ⟨1172930, by rfl⟩ : syracuseStep 1563907 = 2345861) B2345861
theorem B3128579 : Blo 1389514 3128579 := bstep (se 1 (by rfl) ⟨2346434, by rfl⟩ : syracuseStep 3128579 = 4692869) B4692869
theorem B6683917 : Blo 1389514 6683917 := bstep (se 3 (by rfl) ⟨1253234, by rfl⟩ : syracuseStep 6683917 = 2506469) B2506469
theorem B2227505 : Blo 1389514 2227505 := bstep (se 2 (by rfl) ⟨835314, by rfl⟩ : syracuseStep 2227505 = 1670629) B1670629
theorem B2227537 : Blo 1389514 2227537 := bstep (se 2 (by rfl) ⟨835326, by rfl⟩ : syracuseStep 2227537 = 1670653) B1670653
theorem B1760611 : Blo 1389514 1760611 := bstep (se 1 (by rfl) ⟨1320458, by rfl⟩ : syracuseStep 1760611 = 2640917) B2640917
theorem B1564051 : Blo 1389514 1564051 := bstep (se 1 (by rfl) ⟨1173038, by rfl⟩ : syracuseStep 1564051 = 2346077) B2346077
theorem B2817443 : Blo 1389514 2817443 := bstep (se 1 (by rfl) ⟨2113082, by rfl⟩ : syracuseStep 2817443 = 4226165) B4226165
theorem B5938595 : Blo 1389514 5938595 := bstep (se 1 (by rfl) ⟨4453946, by rfl⟩ : syracuseStep 5938595 = 8907893) B8907893
theorem B6602161 : Blo 1389514 6602161 := bstep (se 2 (by rfl) ⟨2475810, by rfl⟩ : syracuseStep 6602161 = 4951621) B4951621
theorem B2112961 : Blo 1389514 2112961 := bstep (se 2 (by rfl) ⟨792360, by rfl⟩ : syracuseStep 2112961 = 1584721) B1584721
theorem B1760707 : Blo 1389514 1760707 := bstep (se 1 (by rfl) ⟨1320530, by rfl⟩ : syracuseStep 1760707 = 2641061) B2641061
theorem B3522001 : Blo 1389514 3522001 := bstep (se 2 (by rfl) ⟨1320750, by rfl⟩ : syracuseStep 3522001 = 2641501) B2641501
theorem B4693517 : Blo 1389514 4693517 := bstep (se 3 (by rfl) ⟨880034, by rfl⟩ : syracuseStep 4693517 = 1760069) B1760069
theorem B3128849 : Blo 1389514 3128849 := bstep (se 2 (by rfl) ⟨1173318, by rfl⟩ : syracuseStep 3128849 = 2346637) B2346637
theorem B1564195 : Blo 1389514 1564195 := bstep (se 1 (by rfl) ⟨1173146, by rfl⟩ : syracuseStep 1564195 = 2346293) B2346293
theorem B3128867 : Blo 1389514 3128867 := bstep (se 1 (by rfl) ⟨2346650, by rfl⟩ : syracuseStep 3128867 = 4693301) B4693301
theorem B3341873 : Blo 1389514 3341873 := bstep (se 2 (by rfl) ⟨1253202, by rfl⟩ : syracuseStep 3341873 = 2506405) B2506405
theorem B4693571 : Blo 1389514 4693571 := bstep (se 1 (by rfl) ⟨3520178, by rfl⟩ : syracuseStep 4693571 = 7040357) B7040357
theorem B1564339 : Blo 1389514 1564339 := bstep (se 1 (by rfl) ⟨1173254, by rfl⟩ : syracuseStep 1564339 = 2346509) B2346509
theorem B4284109 : Blo 1389514 4284109 := bstep (se 3 (by rfl) ⟨803270, by rfl⟩ : syracuseStep 4284109 = 1606541) B1606541
theorem B3129137 : Blo 1389514 3129137 := bstep (se 2 (by rfl) ⟨1173426, by rfl⟩ : syracuseStep 3129137 = 2346853) B2346853
theorem B4456241 : Blo 1389514 4456241 := bstep (se 2 (by rfl) ⟨1671090, by rfl⟩ : syracuseStep 4456241 = 3342181) B3342181
theorem B1564483 : Blo 1389514 1564483 := bstep (se 1 (by rfl) ⟨1173362, by rfl⟩ : syracuseStep 1564483 = 2346725) B2346725
theorem B3129155 : Blo 1389514 3129155 := bstep (se 1 (by rfl) ⟨2346866, by rfl⟩ : syracuseStep 3129155 = 4693733) B4693733
theorem B4693841 : Blo 1389514 4693841 := bstep (se 2 (by rfl) ⟨1760190, by rfl⟩ : syracuseStep 4693841 = 3520381) B3520381
theorem B4226993 : Blo 1389514 4226993 := bstep (se 2 (by rfl) ⟨1585122, by rfl⟩ : syracuseStep 4226993 = 3170245) B3170245
theorem B1564627 : Blo 1389514 1564627 := bstep (se 1 (by rfl) ⟨1173470, by rfl⟩ : syracuseStep 1564627 = 2346941) B2346941
theorem B7520273 : Blo 1389514 7520273 := bstep (se 2 (by rfl) ⟨2820102, by rfl⟩ : syracuseStep 7520273 = 5640205) B5640205
theorem B4227137 : Blo 1389514 4227137 := bstep (se 2 (by rfl) ⟨1585176, by rfl⟩ : syracuseStep 4227137 = 3170353) B3170353
theorem B17817731 : Blo 1389514 17817731 := bstep (se 1 (by rfl) ⟨13363298, by rfl⟩ : syracuseStep 17817731 = 26726597) B26726597
theorem B5939345 : Blo 1389514 5939345 := bstep (se 2 (by rfl) ⟨2227254, by rfl⟩ : syracuseStep 5939345 = 4454509) B4454509
theorem B3129497 : Blo 1389514 3129497 := bstep (se 2 (by rfl) ⟨1173561, by rfl⟩ : syracuseStep 3129497 = 2347123) B2347123
theorem B1564843 : Blo 1389514 1564843 := bstep (se 1 (by rfl) ⟨1173632, by rfl⟩ : syracuseStep 1564843 = 2347265) B2347265
theorem B4694219 : Blo 1389514 4694219 := bstep (se 1 (by rfl) ⟨3520664, by rfl⟩ : syracuseStep 4694219 = 7041329) B7041329
theorem B3129587 : Blo 1389514 3129587 := bstep (se 1 (by rfl) ⟨2347190, by rfl⟩ : syracuseStep 3129587 = 4694381) B4694381
theorem B3129623 : Blo 1389514 3129623 := bstep (se 1 (by rfl) ⟨2347217, by rfl⟩ : syracuseStep 3129623 = 4694435) B4694435
theorem B1564951 : Blo 1389514 1564951 := bstep (se 1 (by rfl) ⟨1173713, by rfl⟩ : syracuseStep 1564951 = 2347427) B2347427
theorem B5275955 : Blo 1389514 5275955 := bstep (se 1 (by rfl) ⟨3956966, by rfl⟩ : syracuseStep 5275955 = 7913933) B7913933
theorem B2638145 : Blo 1389514 2638145 := bstep (se 2 (by rfl) ⟨989304, by rfl⟩ : syracuseStep 2638145 = 1978609) B1978609
theorem B1409419 : Blo 1389514 1409419 := bstep (se 1 (by rfl) ⟨1057064, by rfl⟩ : syracuseStep 1409419 = 2114129) B2114129
theorem B2507161 : Blo 1389514 2507161 := bstep (se 2 (by rfl) ⟨940185, by rfl⟩ : syracuseStep 2507161 = 1880371) B1880371
theorem B3129803 : Blo 1389514 3129803 := bstep (se 1 (by rfl) ⟨2347352, by rfl⟩ : syracuseStep 3129803 = 4694705) B4694705
theorem B1565131 : Blo 1389514 1565131 := bstep (se 1 (by rfl) ⟨1173848, by rfl⟩ : syracuseStep 1565131 = 2347697) B2347697
theorem B4694489 : Blo 1389514 4694489 := bstep (se 2 (by rfl) ⟨1760433, by rfl⟩ : syracuseStep 4694489 = 3520867) B3520867
theorem B3129857 : Blo 1389514 3129857 := bstep (se 2 (by rfl) ⟨1173696, by rfl⟩ : syracuseStep 3129857 = 2347393) B2347393
theorem B1565239 : Blo 1389514 1565239 := bstep (se 1 (by rfl) ⟨1173929, by rfl⟩ : syracuseStep 1565239 = 2347859) B2347859
theorem B12853835 : Blo 1389514 12853835 := bstep (se 1 (by rfl) ⟨9640376, by rfl⟩ : syracuseStep 12853835 = 19280753) B19280753
theorem B5014091 : Blo 1389514 5014091 := bstep (se 1 (by rfl) ⟨3760568, by rfl⟩ : syracuseStep 5014091 = 7521137) B7521137
theorem B11887235 : Blo 1389514 11887235 := bstep (se 1 (by rfl) ⟨8915426, by rfl⟩ : syracuseStep 11887235 = 17830853) B17830853
theorem B2638487 : Blo 1389514 2638487 := bstep (se 1 (by rfl) ⟨1978865, by rfl⟩ : syracuseStep 2638487 = 3957731) B3957731
theorem B3343027 : Blo 1389514 3343027 := bstep (se 1 (by rfl) ⟨2507270, by rfl⟩ : syracuseStep 3343027 = 5014541) B5014541
theorem B3130073 : Blo 1389514 3130073 := bstep (se 2 (by rfl) ⟨1173777, by rfl⟩ : syracuseStep 3130073 = 2347555) B2347555
theorem B5014237 : Blo 1389514 5014237 := bstep (se 3 (by rfl) ⟨940169, by rfl⟩ : syracuseStep 5014237 = 1880339) B1880339
theorem B1565419 : Blo 1389514 1565419 := bstep (se 1 (by rfl) ⟨1174064, by rfl⟩ : syracuseStep 1565419 = 2348129) B2348129
theorem B5940013 : Blo 1389514 5940013 := bstep (se 3 (by rfl) ⟨1113752, by rfl⟩ : syracuseStep 5940013 = 2227505) B2227505
theorem B3130163 : Blo 1389514 3130163 := bstep (se 1 (by rfl) ⟨2347622, by rfl⟩ : syracuseStep 3130163 = 4695245) B4695245
theorem B3130199 : Blo 1389514 3130199 := bstep (se 1 (by rfl) ⟨2347649, by rfl⟩ : syracuseStep 3130199 = 4695299) B4695299
theorem B6685591 : Blo 1389514 6685591 := bstep (se 1 (by rfl) ⟨5014193, by rfl⟩ : syracuseStep 6685591 = 10028387) B10028387
theorem B5276609 : Blo 1389514 5276609 := bstep (se 2 (by rfl) ⟨1978728, by rfl⟩ : syracuseStep 5276609 = 3957457) B3957457
theorem B3130379 : Blo 1389514 3130379 := bstep (se 1 (by rfl) ⟨2347784, by rfl⟩ : syracuseStep 3130379 = 4695569) B4695569
theorem B3130433 : Blo 1389514 3130433 := bstep (se 2 (by rfl) ⟨1173912, by rfl⟩ : syracuseStep 3130433 = 2347825) B2347825
theorem B22848581 : Blo 1389514 22848581 := bstep (se 4 (by rfl) ⟨2142054, by rfl⟩ : syracuseStep 22848581 = 4284109) B4284109
theorem B7513181 : Blo 1389514 7513181 := bstep (se 3 (by rfl) ⟨1408721, by rfl⟩ : syracuseStep 7513181 = 2817443) B2817443
theorem B15025283 : Blo 1389514 15025283 := bstep (se 1 (by rfl) ⟨11268962, by rfl⟩ : syracuseStep 15025283 = 22537925) B22537925
theorem B4695191 : Blo 1389514 4695191 := bstep (se 1 (by rfl) ⟨3521393, by rfl⟩ : syracuseStep 4695191 = 7042787) B7042787
theorem B2712793 : Blo 1389514 2712793 := bstep (se 2 (by rfl) ⟨1017297, by rfl⟩ : syracuseStep 2712793 = 2034595) B2034595
theorem B1410295 : Blo 1389514 1410295 := bstep (se 1 (by rfl) ⟨1057721, by rfl⟩ : syracuseStep 1410295 = 2115443) B2115443
theorem B3171595 : Blo 1389514 3171595 := bstep (se 1 (by rfl) ⟨2378696, by rfl⟩ : syracuseStep 3171595 = 4757393) B4757393
theorem B3130649 : Blo 1389514 3130649 := bstep (se 2 (by rfl) ⟨1173993, by rfl⟩ : syracuseStep 3130649 = 2347987) B2347987
theorem B2639155 : Blo 1389514 2639155 := bstep (se 1 (by rfl) ⟨1979366, by rfl⟩ : syracuseStep 2639155 = 3958733) B3958733
theorem B1484119 : Blo 1389514 1484119 := bstep (se 1 (by rfl) ⟨1113089, by rfl⟩ : syracuseStep 1484119 = 2226179) B2226179
theorem B3130739 : Blo 1389514 3130739 := bstep (se 1 (by rfl) ⟨2348054, by rfl⟩ : syracuseStep 3130739 = 4696109) B4696109
theorem B5940611 : Blo 1389514 5940611 := bstep (se 1 (by rfl) ⟨4455458, by rfl⟩ : syracuseStep 5940611 = 8910917) B8910917
theorem B3130775 : Blo 1389514 3130775 := bstep (se 1 (by rfl) ⟨2348081, by rfl⟩ : syracuseStep 3130775 = 4696163) B4696163
theorem B2377163 : Blo 1389514 2377163 := bstep (se 1 (by rfl) ⟨1782872, by rfl⟩ : syracuseStep 2377163 = 3565745) B3565745
theorem B2819585 : Blo 1389514 2819585 := bstep (se 2 (by rfl) ⟨1057344, by rfl⟩ : syracuseStep 2819585 = 2114689) B2114689
theorem B27092497 : Blo 1389514 27092497 := bstep (se 2 (by rfl) ⟨10159686, by rfl⟩ : syracuseStep 27092497 = 20319373) B20319373
theorem B34309649 : Blo 1389514 34309649 := bstep (se 2 (by rfl) ⟨12866118, by rfl⟩ : syracuseStep 34309649 = 25732237) B25732237
theorem B6686225 : Blo 1389514 6686225 := bstep (se 2 (by rfl) ⟨2507334, by rfl⟩ : syracuseStep 6686225 = 5014669) B5014669
theorem B10708631 : Blo 1389514 10708631 := bstep (se 1 (by rfl) ⟨8031473, by rfl⟩ : syracuseStep 10708631 = 16062947) B16062947
theorem B4695731 : Blo 1389514 4695731 := bstep (se 1 (by rfl) ⟨3521798, by rfl⟩ : syracuseStep 4695731 = 7043597) B7043597
theorem B2639603 : Blo 1389514 2639603 := bstep (se 1 (by rfl) ⟨1979702, by rfl⟩ : syracuseStep 2639603 = 3959405) B3959405
theorem B3172097 : Blo 1389514 3172097 := bstep (se 2 (by rfl) ⟨1189536, by rfl⟩ : syracuseStep 3172097 = 2379073) B2379073
theorem B7038737 : Blo 1389514 7038737 := bstep (se 2 (by rfl) ⟨2639526, by rfl⟩ : syracuseStep 7038737 = 5279053) B5279053
theorem B2639641 : Blo 1389514 2639641 := bstep (se 2 (by rfl) ⟨989865, by rfl⟩ : syracuseStep 2639641 = 1979731) B1979731
theorem B2344855 : Blo 1389514 2344855 := bstep (se 1 (by rfl) ⟨1758641, by rfl⟩ : syracuseStep 2344855 = 3517283) B3517283
theorem B7038899 : Blo 1389514 7038899 := bstep (se 1 (by rfl) ⟨5279174, by rfl⟩ : syracuseStep 7038899 = 10558349) B10558349
theorem B4696001 : Blo 1389514 4696001 := bstep (se 2 (by rfl) ⟨1761000, by rfl⟩ : syracuseStep 4696001 = 3522001) B3522001
theorem B2967691 : Blo 1389514 2967691 := bstep (se 1 (by rfl) ⟨2225768, by rfl⟩ : syracuseStep 2967691 = 4451537) B4451537
theorem B1484939 : Blo 1389514 1484939 := bstep (se 1 (by rfl) ⟨1113704, by rfl⟩ : syracuseStep 1484939 = 2227409) B2227409
theorem B5277869 : Blo 1389514 5277869 := bstep (se 3 (by rfl) ⟨989600, by rfl⟩ : syracuseStep 5277869 = 1979201) B1979201
theorem B5277899 : Blo 1389514 5277899 := bstep (se 1 (by rfl) ⟨3958424, by rfl⟩ : syracuseStep 5277899 = 7916849) B7916849
theorem B2640089 : Blo 1389514 2640089 := bstep (se 2 (by rfl) ⟨990033, by rfl⟩ : syracuseStep 2640089 = 1980067) B1980067
theorem B3959063 : Blo 1389514 3959063 := bstep (se 1 (by rfl) ⟨2969297, by rfl⟩ : syracuseStep 3959063 = 5938595) B5938595
theorem B2345483 : Blo 1389514 2345483 := bstep (se 1 (by rfl) ⟨1759112, by rfl⟩ : syracuseStep 2345483 = 3518225) B3518225
theorem B2345611 : Blo 1389514 2345611 := bstep (se 1 (by rfl) ⟨1759208, by rfl⟩ : syracuseStep 2345611 = 3518417) B3518417
theorem B3213977 : Blo 1389514 3213977 := bstep (se 2 (by rfl) ⟨1205241, by rfl⟩ : syracuseStep 3213977 = 2410483) B2410483
theorem B10021553 : Blo 1389514 10021553 := bstep (se 2 (by rfl) ⟨3758082, by rfl⟩ : syracuseStep 10021553 = 7516165) B7516165
theorem B2345753 : Blo 1389514 2345753 := bstep (se 2 (by rfl) ⟨879657, by rfl⟩ : syracuseStep 2345753 = 1759315) B1759315
theorem B2968409 : Blo 1389514 2968409 := bstep (se 2 (by rfl) ⟨1113153, by rfl⟩ : syracuseStep 2968409 = 2226307) B2226307
theorem B5278553 : Blo 1389514 5278553 := bstep (se 2 (by rfl) ⟨1979457, by rfl⟩ : syracuseStep 5278553 = 3958915) B3958915
theorem B20032373 : Blo 1389514 20032373 := bstep (se 5 (by rfl) ⟨939017, by rfl⟩ : syracuseStep 20032373 = 1878035) B1878035
theorem B2345881 : Blo 1389514 2345881 := bstep (se 2 (by rfl) ⟨879705, by rfl⟩ : syracuseStep 2345881 = 1759411) B1759411
theorem B2640833 : Blo 1389514 2640833 := bstep (se 2 (by rfl) ⟨990312, by rfl⟩ : syracuseStep 2640833 = 1980625) B1980625
theorem B50760665 : Blo 1389514 50760665 := bstep (se 2 (by rfl) ⟨19035249, by rfl⟩ : syracuseStep 50760665 = 38070499) B38070499
theorem B10554461 : Blo 1389514 10554461 := bstep (se 3 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 10554461 = 3957923) B3957923
theorem B5278871 : Blo 1389514 5278871 := bstep (se 1 (by rfl) ⟨3959153, by rfl⟩ : syracuseStep 5278871 = 7918307) B7918307
theorem B2641099 : Blo 1389514 2641099 := bstep (se 1 (by rfl) ⟨1980824, by rfl⟩ : syracuseStep 2641099 = 3961649) B3961649
theorem B42822917 : Blo 1389514 42822917 := bstep (se 4 (by rfl) ⟨4014648, by rfl⟩ : syracuseStep 42822917 = 8029297) B8029297
theorem B2968921 : Blo 1389514 2968921 := bstep (se 2 (by rfl) ⟨1113345, by rfl⟩ : syracuseStep 2968921 = 2226691) B2226691
theorem B4230593 : Blo 1389514 4230593 := bstep (se 2 (by rfl) ⟨1586472, by rfl⟩ : syracuseStep 4230593 = 3172945) B3172945
theorem B2346455 : Blo 1389514 2346455 := bstep (se 1 (by rfl) ⟨1759841, by rfl⟩ : syracuseStep 2346455 = 3519683) B3519683
theorem B2969075 : Blo 1389514 2969075 := bstep (se 1 (by rfl) ⟨2226806, by rfl⟩ : syracuseStep 2969075 = 4453613) B4453613
theorem B2084363 : Blo 1389514 2084363 := bstep (se 1 (by rfl) ⟨1563272, by rfl⟩ : syracuseStep 2084363 = 3126545) B3126545
theorem B2084375 : Blo 1389514 2084375 := bstep (se 1 (by rfl) ⟨1563281, by rfl⟩ : syracuseStep 2084375 = 3126563) B3126563
theorem B2674201 : Blo 1389514 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B7917101 : Blo 1389514 7917101 := bstep (se 3 (by rfl) ⟨1484456, by rfl⟩ : syracuseStep 7917101 = 2968913) B2968913
theorem B2346583 : Blo 1389514 2346583 := bstep (se 1 (by rfl) ⟨1759937, by rfl⟩ : syracuseStep 2346583 = 3519875) B3519875
theorem B2084441 : Blo 1389514 2084441 := bstep (se 2 (by rfl) ⟨781665, by rfl⟩ : syracuseStep 2084441 = 1563331) B1563331
theorem B6016643 : Blo 1389514 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B16912003 : Blo 1389514 16912003 := bstep (se 1 (by rfl) ⟨12684002, by rfl⟩ : syracuseStep 16912003 = 25368005) B25368005
theorem B2641547 : Blo 1389514 2641547 := bstep (se 1 (by rfl) ⟨1981160, by rfl⟩ : syracuseStep 2641547 = 3962321) B3962321
theorem B2084555 : Blo 1389514 2084555 := bstep (se 1 (by rfl) ⟨1563416, by rfl⟩ : syracuseStep 2084555 = 3126833) B3126833
theorem B2084567 : Blo 1389514 2084567 := bstep (se 1 (by rfl) ⟨1563425, by rfl⟩ : syracuseStep 2084567 = 3126851) B3126851
theorem B4689629 : Blo 1389514 4689629 := bstep (se 3 (by rfl) ⟨879305, by rfl⟩ : syracuseStep 4689629 = 1758611) B1758611
theorem B2084633 : Blo 1389514 2084633 := bstep (se 2 (by rfl) ⟨781737, by rfl⟩ : syracuseStep 2084633 = 1563475) B1563475
theorem B5279539 : Blo 1389514 5279539 := bstep (se 1 (by rfl) ⟨3959654, by rfl⟩ : syracuseStep 5279539 = 7919309) B7919309
theorem B11874113 : Blo 1389514 11874113 := bstep (se 2 (by rfl) ⟨4452792, by rfl⟩ : syracuseStep 11874113 = 8905585) B8905585
theorem B7040843 : Blo 1389514 7040843 := bstep (se 1 (by rfl) ⟨5280632, by rfl⟩ : syracuseStep 7040843 = 10561265) B10561265
theorem B2084747 : Blo 1389514 2084747 := bstep (se 1 (by rfl) ⟨1563560, by rfl⟩ : syracuseStep 2084747 = 3127121) B3127121
theorem B2084759 : Blo 1389514 2084759 := bstep (se 1 (by rfl) ⟨1563569, by rfl⟩ : syracuseStep 2084759 = 3127139) B3127139
theorem B1585067 : Blo 1389514 1585067 := bstep (se 1 (by rfl) ⟨1188800, by rfl⟩ : syracuseStep 1585067 = 2377601) B2377601
theorem B15830963 : Blo 1389514 15830963 := bstep (se 1 (by rfl) ⟨11873222, by rfl⟩ : syracuseStep 15830963 = 23746445) B23746445
theorem B3518387 : Blo 1389514 3518387 := bstep (se 1 (by rfl) ⟨2638790, by rfl⟩ : syracuseStep 3518387 = 5277581) B5277581
theorem B2084825 : Blo 1389514 2084825 := bstep (se 2 (by rfl) ⟨781809, by rfl⟩ : syracuseStep 2084825 = 1563619) B1563619
theorem B2084939 : Blo 1389514 2084939 := bstep (se 1 (by rfl) ⟨1563704, by rfl⟩ : syracuseStep 2084939 = 3127409) B3127409
theorem B2084951 : Blo 1389514 2084951 := bstep (se 1 (by rfl) ⟨1563713, by rfl⟩ : syracuseStep 2084951 = 3127427) B3127427
theorem B2085017 : Blo 1389514 2085017 := bstep (se 2 (by rfl) ⟨781881, by rfl⟩ : syracuseStep 2085017 = 1563763) B1563763
theorem B2347211 : Blo 1389514 2347211 := bstep (se 1 (by rfl) ⟨1760408, by rfl⟩ : syracuseStep 2347211 = 3520817) B3520817
theorem B2085131 : Blo 1389514 2085131 := bstep (se 1 (by rfl) ⟨1563848, by rfl⟩ : syracuseStep 2085131 = 3127697) B3127697
theorem B2085143 : Blo 1389514 2085143 := bstep (se 1 (by rfl) ⟨1563857, by rfl⟩ : syracuseStep 2085143 = 3127715) B3127715
theorem B2347339 : Blo 1389514 2347339 := bstep (se 1 (by rfl) ⟨1760504, by rfl⟩ : syracuseStep 2347339 = 3521009) B3521009
theorem B2085209 : Blo 1389514 2085209 := bstep (se 2 (by rfl) ⟨781953, by rfl⟩ : syracuseStep 2085209 = 1563907) B1563907
theorem B15045041 : Blo 1389514 15045041 := bstep (se 2 (by rfl) ⟨5641890, by rfl⟩ : syracuseStep 15045041 = 11283781) B11283781
theorem B2970049 : Blo 1389514 2970049 := bstep (se 2 (by rfl) ⟨1113768, by rfl⟩ : syracuseStep 2970049 = 2227537) B2227537
theorem B3518923 : Blo 1389514 3518923 := bstep (se 1 (by rfl) ⟨2639192, by rfl⟩ : syracuseStep 3518923 = 5278385) B5278385
theorem B2085323 : Blo 1389514 2085323 := bstep (se 1 (by rfl) ⟨1563992, by rfl⟩ : syracuseStep 2085323 = 3127985) B3127985
theorem B2085335 : Blo 1389514 2085335 := bstep (se 1 (by rfl) ⟨1564001, by rfl⟩ : syracuseStep 2085335 = 3128003) B3128003
theorem B2347481 : Blo 1389514 2347481 := bstep (se 2 (by rfl) ⟨880305, by rfl⟩ : syracuseStep 2347481 = 1760611) B1760611
theorem B12866053 : Blo 1389514 12866053 := bstep (se 4 (by rfl) ⟨1206192, by rfl⟩ : syracuseStep 12866053 = 2412385) B2412385
theorem B34271761 : Blo 1389514 34271761 := bstep (se 2 (by rfl) ⟨12851910, by rfl⟩ : syracuseStep 34271761 = 25703821) B25703821
theorem B5935639 : Blo 1389514 5935639 := bstep (se 1 (by rfl) ⟨4451729, by rfl⟩ : syracuseStep 5935639 = 8903459) B8903459
theorem B2085401 : Blo 1389514 2085401 := bstep (se 2 (by rfl) ⟨782025, by rfl⟩ : syracuseStep 2085401 = 1564051) B1564051
theorem B8802881 : Blo 1389514 8802881 := bstep (se 2 (by rfl) ⟨3301080, by rfl⟩ : syracuseStep 8802881 = 6602161) B6602161
theorem B3519065 : Blo 1389514 3519065 := bstep (se 2 (by rfl) ⟨1319649, by rfl⟩ : syracuseStep 3519065 = 2639299) B2639299
theorem B2347609 : Blo 1389514 2347609 := bstep (se 2 (by rfl) ⟨880353, by rfl⟩ : syracuseStep 2347609 = 1760707) B1760707
theorem B2085515 : Blo 1389514 2085515 := bstep (se 1 (by rfl) ⟨1564136, by rfl⟩ : syracuseStep 2085515 = 3128273) B3128273
theorem B2085527 : Blo 1389514 2085527 := bstep (se 1 (by rfl) ⟨1564145, by rfl⟩ : syracuseStep 2085527 = 3128291) B3128291
theorem B3961523 : Blo 1389514 3961523 := bstep (se 1 (by rfl) ⟨2971142, by rfl⟩ : syracuseStep 3961523 = 5942285) B5942285
theorem B5010113 : Blo 1389514 5010113 := bstep (se 2 (by rfl) ⟨1878792, by rfl⟩ : syracuseStep 5010113 = 3757585) B3757585
theorem B2085593 : Blo 1389514 2085593 := bstep (se 2 (by rfl) ⟨782097, by rfl⟩ : syracuseStep 2085593 = 1564195) B1564195
theorem B2970391 : Blo 1389514 2970391 := bstep (se 1 (by rfl) ⟨2227793, by rfl⟩ : syracuseStep 2970391 = 4455587) B4455587
theorem B4690763 : Blo 1389514 4690763 := bstep (se 1 (by rfl) ⟨3518072, by rfl⟩ : syracuseStep 4690763 = 7036145) B7036145
theorem B2085707 : Blo 1389514 2085707 := bstep (se 1 (by rfl) ⟨1564280, by rfl⟩ : syracuseStep 2085707 = 3128561) B3128561
theorem B2085719 : Blo 1389514 2085719 := bstep (se 1 (by rfl) ⟨1564289, by rfl⟩ : syracuseStep 2085719 = 3128579) B3128579
theorem B2085785 : Blo 1389514 2085785 := bstep (se 2 (by rfl) ⟨782169, by rfl⟩ : syracuseStep 2085785 = 1564339) B1564339
theorem B1389515 : Blo 1389514 1389515 := bstep (se 1 (by rfl) ⟨1042136, by rfl⟩ : syracuseStep 1389515 = 2084273) B2084273
theorem B1389527 : Blo 1389514 1389527 := bstep (se 1 (by rfl) ⟨1042145, by rfl⟩ : syracuseStep 1389527 = 2084291) B2084291
theorem B1389547 : Blo 1389514 1389547 := bstep (se 1 (by rfl) ⟨1042160, by rfl⟩ : syracuseStep 1389547 = 2084321) B2084321
theorem B1389559 : Blo 1389514 1389559 := bstep (se 1 (by rfl) ⟨1042169, by rfl⟩ : syracuseStep 1389559 = 2084339) B2084339
theorem B1389579 : Blo 1389514 1389579 := bstep (se 1 (by rfl) ⟨1042184, by rfl⟩ : syracuseStep 1389579 = 2084369) B2084369
theorem B2085899 : Blo 1389514 2085899 := bstep (se 1 (by rfl) ⟨1564424, by rfl⟩ : syracuseStep 2085899 = 3128849) B3128849
theorem B5280785 : Blo 1389514 5280785 := bstep (se 2 (by rfl) ⟨1980294, by rfl⟩ : syracuseStep 5280785 = 3960589) B3960589
theorem B1389591 : Blo 1389514 1389591 := bstep (se 1 (by rfl) ⟨1042193, by rfl⟩ : syracuseStep 1389591 = 2084387) B2084387
theorem B2085911 : Blo 1389514 2085911 := bstep (se 1 (by rfl) ⟨1564433, by rfl⟩ : syracuseStep 2085911 = 3128867) B3128867
theorem B1389611 : Blo 1389514 1389611 := bstep (se 1 (by rfl) ⟨1042208, by rfl⟩ : syracuseStep 1389611 = 2084417) B2084417
theorem B1389623 : Blo 1389514 1389623 := bstep (se 1 (by rfl) ⟨1042217, by rfl⟩ : syracuseStep 1389623 = 2084435) B2084435
theorem B1389643 : Blo 1389514 1389643 := bstep (se 1 (by rfl) ⟨1042232, by rfl⟩ : syracuseStep 1389643 = 2084465) B2084465
theorem B1389655 : Blo 1389514 1389655 := bstep (se 1 (by rfl) ⟨1042241, by rfl⟩ : syracuseStep 1389655 = 2084483) B2084483
theorem B4691033 : Blo 1389514 4691033 := bstep (se 2 (by rfl) ⟨1759137, by rfl⟩ : syracuseStep 4691033 = 3518275) B3518275
theorem B2085977 : Blo 1389514 2085977 := bstep (se 2 (by rfl) ⟨782241, by rfl⟩ : syracuseStep 2085977 = 1564483) B1564483
theorem B1389675 : Blo 1389514 1389675 := bstep (se 1 (by rfl) ⟨1042256, by rfl⟩ : syracuseStep 1389675 = 2084513) B2084513
theorem B1389687 : Blo 1389514 1389687 := bstep (se 1 (by rfl) ⟨1042265, by rfl⟩ : syracuseStep 1389687 = 2084531) B2084531
theorem B1389707 : Blo 1389514 1389707 := bstep (se 1 (by rfl) ⟨1042280, by rfl⟩ : syracuseStep 1389707 = 2084561) B2084561
theorem B1389719 : Blo 1389514 1389719 := bstep (se 1 (by rfl) ⟨1042289, by rfl⟩ : syracuseStep 1389719 = 2084579) B2084579
theorem B22869143 : Blo 1389514 22869143 := bstep (se 1 (by rfl) ⟨17151857, by rfl⟩ : syracuseStep 22869143 = 34303715) B34303715
theorem B1389739 : Blo 1389514 1389739 := bstep (se 1 (by rfl) ⟨1042304, by rfl⟩ : syracuseStep 1389739 = 2084609) B2084609
theorem B1389751 : Blo 1389514 1389751 := bstep (se 1 (by rfl) ⟨1042313, by rfl⟩ : syracuseStep 1389751 = 2084627) B2084627
theorem B1389771 : Blo 1389514 1389771 := bstep (se 1 (by rfl) ⟨1042328, by rfl⟩ : syracuseStep 1389771 = 2084657) B2084657
theorem B2086091 : Blo 1389514 2086091 := bstep (se 1 (by rfl) ⟨1564568, by rfl⟩ : syracuseStep 2086091 = 3129137) B3129137
theorem B2970827 : Blo 1389514 2970827 := bstep (se 1 (by rfl) ⟨2228120, by rfl⟩ : syracuseStep 2970827 = 4456241) B4456241
theorem B1389783 : Blo 1389514 1389783 := bstep (se 1 (by rfl) ⟨1042337, by rfl⟩ : syracuseStep 1389783 = 2084675) B2084675
theorem B2086103 : Blo 1389514 2086103 := bstep (se 1 (by rfl) ⟨1564577, by rfl⟩ : syracuseStep 2086103 = 3129155) B3129155
theorem B1389803 : Blo 1389514 1389803 := bstep (se 1 (by rfl) ⟨1042352, by rfl⟩ : syracuseStep 1389803 = 2084705) B2084705
theorem B1389815 : Blo 1389514 1389815 := bstep (se 1 (by rfl) ⟨1042361, by rfl⟩ : syracuseStep 1389815 = 2084723) B2084723
theorem B1389835 : Blo 1389514 1389835 := bstep (se 1 (by rfl) ⟨1042376, by rfl⟩ : syracuseStep 1389835 = 2084753) B2084753
theorem B1389847 : Blo 1389514 1389847 := bstep (se 1 (by rfl) ⟨1042385, by rfl⟩ : syracuseStep 1389847 = 2084771) B2084771
theorem B2086169 : Blo 1389514 2086169 := bstep (se 2 (by rfl) ⟨782313, by rfl⟩ : syracuseStep 2086169 = 1564627) B1564627
theorem B1389867 : Blo 1389514 1389867 := bstep (se 1 (by rfl) ⟨1042400, by rfl⟩ : syracuseStep 1389867 = 2084801) B2084801
theorem B1389879 : Blo 1389514 1389879 := bstep (se 1 (by rfl) ⟨1042409, by rfl⟩ : syracuseStep 1389879 = 2084819) B2084819
theorem B1389899 : Blo 1389514 1389899 := bstep (se 1 (by rfl) ⟨1042424, by rfl⟩ : syracuseStep 1389899 = 2084849) B2084849
theorem B1389911 : Blo 1389514 1389911 := bstep (se 1 (by rfl) ⟨1042433, by rfl⟩ : syracuseStep 1389911 = 2084867) B2084867
theorem B3126617 : Blo 1389514 3126617 := bstep (se 2 (by rfl) ⟨1172481, by rfl⟩ : syracuseStep 3126617 = 2344963) B2344963
theorem B15832421 : Blo 1389514 15832421 := bstep (se 4 (by rfl) ⟨1484289, by rfl⟩ : syracuseStep 15832421 = 2968579) B2968579
theorem B1389931 : Blo 1389514 1389931 := bstep (se 1 (by rfl) ⟨1042448, by rfl⟩ : syracuseStep 1389931 = 2084897) B2084897
theorem B1389943 : Blo 1389514 1389943 := bstep (se 1 (by rfl) ⟨1042457, by rfl⟩ : syracuseStep 1389943 = 2084915) B2084915
theorem B1389963 : Blo 1389514 1389963 := bstep (se 1 (by rfl) ⟨1042472, by rfl⟩ : syracuseStep 1389963 = 2084945) B2084945
theorem B2086283 : Blo 1389514 2086283 := bstep (se 1 (by rfl) ⟨1564712, by rfl⟩ : syracuseStep 2086283 = 3129425) B3129425
theorem B1389975 : Blo 1389514 1389975 := bstep (se 1 (by rfl) ⟨1042481, by rfl⟩ : syracuseStep 1389975 = 2084963) B2084963
theorem B3519895 : Blo 1389514 3519895 := bstep (se 1 (by rfl) ⟨2639921, by rfl⟩ : syracuseStep 3519895 = 5279843) B5279843
theorem B2086295 : Blo 1389514 2086295 := bstep (se 1 (by rfl) ⟨1564721, by rfl⟩ : syracuseStep 2086295 = 3129443) B3129443
theorem B1389995 : Blo 1389514 1389995 := bstep (se 1 (by rfl) ⟨1042496, by rfl⟩ : syracuseStep 1389995 = 2084993) B2084993
theorem B3126707 : Blo 1389514 3126707 := bstep (se 1 (by rfl) ⟨2345030, by rfl⟩ : syracuseStep 3126707 = 4690061) B4690061
theorem B1390007 : Blo 1389514 1390007 := bstep (se 1 (by rfl) ⟨1042505, by rfl⟩ : syracuseStep 1390007 = 2085011) B2085011
theorem B1758667 : Blo 1389514 1758667 := bstep (se 1 (by rfl) ⟨1319000, by rfl⟩ : syracuseStep 1758667 = 2638001) B2638001
theorem B1390027 : Blo 1389514 1390027 := bstep (se 1 (by rfl) ⟨1042520, by rfl⟩ : syracuseStep 1390027 = 2085041) B2085041
theorem B3126743 : Blo 1389514 3126743 := bstep (se 1 (by rfl) ⟨2345057, by rfl⟩ : syracuseStep 3126743 = 4690115) B4690115
theorem B1390039 : Blo 1389514 1390039 := bstep (se 1 (by rfl) ⟨1042529, by rfl⟩ : syracuseStep 1390039 = 2085059) B2085059
theorem B2086361 : Blo 1389514 2086361 := bstep (se 2 (by rfl) ⟨782385, by rfl⟩ : syracuseStep 2086361 = 1564771) B1564771
theorem B1390059 : Blo 1389514 1390059 := bstep (se 1 (by rfl) ⟨1042544, by rfl⟩ : syracuseStep 1390059 = 2085089) B2085089
theorem B1390071 : Blo 1389514 1390071 := bstep (se 1 (by rfl) ⟨1042553, by rfl⟩ : syracuseStep 1390071 = 2085107) B2085107
theorem B1390091 : Blo 1389514 1390091 := bstep (se 1 (by rfl) ⟨1042568, by rfl⟩ : syracuseStep 1390091 = 2085137) B2085137
theorem B6018583 : Blo 1389514 6018583 := bstep (se 1 (by rfl) ⟨4513937, by rfl⟩ : syracuseStep 6018583 = 9027875) B9027875
theorem B1390103 : Blo 1389514 1390103 := bstep (se 1 (by rfl) ⟨1042577, by rfl⟩ : syracuseStep 1390103 = 2085155) B2085155
theorem B1390123 : Blo 1389514 1390123 := bstep (se 1 (by rfl) ⟨1042592, by rfl⟩ : syracuseStep 1390123 = 2085185) B2085185
theorem B1390135 : Blo 1389514 1390135 := bstep (se 1 (by rfl) ⟨1042601, by rfl⟩ : syracuseStep 1390135 = 2085203) B2085203
theorem B7042625 : Blo 1389514 7042625 := bstep (se 2 (by rfl) ⟨2640984, by rfl⟩ : syracuseStep 7042625 = 5281969) B5281969
theorem B1390155 : Blo 1389514 1390155 := bstep (se 1 (by rfl) ⟨1042616, by rfl⟩ : syracuseStep 1390155 = 2085233) B2085233
theorem B2086475 : Blo 1389514 2086475 := bstep (se 1 (by rfl) ⟨1564856, by rfl⟩ : syracuseStep 2086475 = 3129713) B3129713
theorem B1390167 : Blo 1389514 1390167 := bstep (se 1 (by rfl) ⟨1042625, by rfl⟩ : syracuseStep 1390167 = 2085251) B2085251
theorem B2086487 : Blo 1389514 2086487 := bstep (se 1 (by rfl) ⟨1564865, by rfl⟩ : syracuseStep 2086487 = 3129731) B3129731
theorem B1390187 : Blo 1389514 1390187 := bstep (se 1 (by rfl) ⟨1042640, by rfl⟩ : syracuseStep 1390187 = 2085281) B2085281
theorem B1390199 : Blo 1389514 1390199 := bstep (se 1 (by rfl) ⟨1042649, by rfl⟩ : syracuseStep 1390199 = 2085299) B2085299
theorem B3126923 : Blo 1389514 3126923 := bstep (se 1 (by rfl) ⟨2345192, by rfl⟩ : syracuseStep 3126923 = 4690385) B4690385
theorem B1390219 : Blo 1389514 1390219 := bstep (se 1 (by rfl) ⟨1042664, by rfl⟩ : syracuseStep 1390219 = 2085329) B2085329
theorem B4011671 : Blo 1389514 4011671 := bstep (se 1 (by rfl) ⟨3008753, by rfl⟩ : syracuseStep 4011671 = 6017507) B6017507
theorem B1390231 : Blo 1389514 1390231 := bstep (se 1 (by rfl) ⟨1042673, by rfl⟩ : syracuseStep 1390231 = 2085347) B2085347
theorem B1980055 : Blo 1389514 1980055 := bstep (se 1 (by rfl) ⟨1485041, by rfl⟩ : syracuseStep 1980055 = 2970083) B2970083
theorem B2086553 : Blo 1389514 2086553 := bstep (se 2 (by rfl) ⟨782457, by rfl⟩ : syracuseStep 2086553 = 1564915) B1564915
theorem B1390251 : Blo 1389514 1390251 := bstep (se 1 (by rfl) ⟨1042688, by rfl⟩ : syracuseStep 1390251 = 2085377) B2085377
theorem B20043445 : Blo 1389514 20043445 := bstep (se 5 (by rfl) ⟨939536, by rfl⟩ : syracuseStep 20043445 = 1879073) B1879073
theorem B1390263 : Blo 1389514 1390263 := bstep (se 1 (by rfl) ⟨1042697, by rfl⟩ : syracuseStep 1390263 = 2085395) B2085395
theorem B3126977 : Blo 1389514 3126977 := bstep (se 2 (by rfl) ⟨1172616, by rfl⟩ : syracuseStep 3126977 = 2345233) B2345233
theorem B1390283 : Blo 1389514 1390283 := bstep (se 1 (by rfl) ⟨1042712, by rfl⟩ : syracuseStep 1390283 = 2085425) B2085425
theorem B5281483 : Blo 1389514 5281483 := bstep (se 1 (by rfl) ⟨3961112, by rfl⟩ : syracuseStep 5281483 = 7922225) B7922225
theorem B1758935 : Blo 1389514 1758935 := bstep (se 1 (by rfl) ⟨1319201, by rfl⟩ : syracuseStep 1758935 = 2638403) B2638403
theorem B1390295 : Blo 1389514 1390295 := bstep (se 1 (by rfl) ⟨1042721, by rfl⟩ : syracuseStep 1390295 = 2085443) B2085443
theorem B1390315 : Blo 1389514 1390315 := bstep (se 1 (by rfl) ⟨1042736, by rfl⟩ : syracuseStep 1390315 = 2085473) B2085473
theorem B1390327 : Blo 1389514 1390327 := bstep (se 1 (by rfl) ⟨1042745, by rfl⟩ : syracuseStep 1390327 = 2085491) B2085491
theorem B1390347 : Blo 1389514 1390347 := bstep (se 1 (by rfl) ⟨1042760, by rfl⟩ : syracuseStep 1390347 = 2085521) B2085521
theorem B2086667 : Blo 1389514 2086667 := bstep (se 1 (by rfl) ⟨1565000, by rfl⟩ : syracuseStep 2086667 = 3130001) B3130001
theorem B4691735 : Blo 1389514 4691735 := bstep (se 1 (by rfl) ⟨3518801, by rfl⟩ : syracuseStep 4691735 = 7037603) B7037603
theorem B1390359 : Blo 1389514 1390359 := bstep (se 1 (by rfl) ⟨1042769, by rfl⟩ : syracuseStep 1390359 = 2085539) B2085539
theorem B2086679 : Blo 1389514 2086679 := bstep (se 1 (by rfl) ⟨1565009, by rfl⟩ : syracuseStep 2086679 = 3130019) B3130019
theorem B1390379 : Blo 1389514 1390379 := bstep (se 1 (by rfl) ⟨1042784, by rfl⟩ : syracuseStep 1390379 = 2085569) B2085569
theorem B1390391 : Blo 1389514 1390391 := bstep (se 1 (by rfl) ⟨1042793, by rfl⟩ : syracuseStep 1390391 = 2085587) B2085587
theorem B1390411 : Blo 1389514 1390411 := bstep (se 1 (by rfl) ⟨1042808, by rfl⟩ : syracuseStep 1390411 = 2085617) B2085617
theorem B3520331 : Blo 1389514 3520331 := bstep (se 1 (by rfl) ⟨2640248, by rfl⟩ : syracuseStep 3520331 = 5280497) B5280497
theorem B1390423 : Blo 1389514 1390423 := bstep (se 1 (by rfl) ⟨1042817, by rfl⟩ : syracuseStep 1390423 = 2085635) B2085635
theorem B2086745 : Blo 1389514 2086745 := bstep (se 2 (by rfl) ⟨782529, by rfl⟩ : syracuseStep 2086745 = 1565059) B1565059
theorem B1390443 : Blo 1389514 1390443 := bstep (se 1 (by rfl) ⟨1042832, by rfl⟩ : syracuseStep 1390443 = 2085665) B2085665
theorem B1390455 : Blo 1389514 1390455 := bstep (se 1 (by rfl) ⟨1042841, by rfl⟩ : syracuseStep 1390455 = 2085683) B2085683
theorem B7919491 : Blo 1389514 7919491 := bstep (se 1 (by rfl) ⟨5939618, by rfl⟩ : syracuseStep 7919491 = 11879237) B11879237
theorem B1390475 : Blo 1389514 1390475 := bstep (se 1 (by rfl) ⟨1042856, by rfl⟩ : syracuseStep 1390475 = 2085713) B2085713
theorem B1390487 : Blo 1389514 1390487 := bstep (se 1 (by rfl) ⟨1042865, by rfl⟩ : syracuseStep 1390487 = 2085731) B2085731
theorem B3127193 : Blo 1389514 3127193 := bstep (se 2 (by rfl) ⟨1172697, by rfl⟩ : syracuseStep 3127193 = 2345395) B2345395
theorem B1390507 : Blo 1389514 1390507 := bstep (se 1 (by rfl) ⟨1042880, by rfl⟩ : syracuseStep 1390507 = 2085761) B2085761
theorem B1390519 : Blo 1389514 1390519 := bstep (se 1 (by rfl) ⟨1042889, by rfl⟩ : syracuseStep 1390519 = 2085779) B2085779
theorem B1390539 : Blo 1389514 1390539 := bstep (se 1 (by rfl) ⟨1042904, by rfl⟩ : syracuseStep 1390539 = 2085809) B2085809
theorem B2086859 : Blo 1389514 2086859 := bstep (se 1 (by rfl) ⟨1565144, by rfl⟩ : syracuseStep 2086859 = 3130289) B3130289
theorem B1390551 : Blo 1389514 1390551 := bstep (se 1 (by rfl) ⟨1042913, by rfl⟩ : syracuseStep 1390551 = 2085827) B2085827
theorem B2086871 : Blo 1389514 2086871 := bstep (se 1 (by rfl) ⟨1565153, by rfl⟩ : syracuseStep 2086871 = 3130307) B3130307
theorem B5281757 : Blo 1389514 5281757 := bstep (se 3 (by rfl) ⟨990329, by rfl⟩ : syracuseStep 5281757 = 1980659) B1980659
theorem B1390571 : Blo 1389514 1390571 := bstep (se 1 (by rfl) ⟨1042928, by rfl⟩ : syracuseStep 1390571 = 2085857) B2085857
theorem B3127283 : Blo 1389514 3127283 := bstep (se 1 (by rfl) ⟨2345462, by rfl⟩ : syracuseStep 3127283 = 4690925) B4690925
theorem B1390583 : Blo 1389514 1390583 := bstep (se 1 (by rfl) ⟨1042937, by rfl⟩ : syracuseStep 1390583 = 2085875) B2085875
theorem B1390603 : Blo 1389514 1390603 := bstep (se 1 (by rfl) ⟨1042952, by rfl⟩ : syracuseStep 1390603 = 2085905) B2085905
theorem B3127319 : Blo 1389514 3127319 := bstep (se 1 (by rfl) ⟨2345489, by rfl⟩ : syracuseStep 3127319 = 4690979) B4690979
theorem B4577303 : Blo 1389514 4577303 := bstep (se 1 (by rfl) ⟨3432977, by rfl⟩ : syracuseStep 4577303 = 6865955) B6865955
theorem B1390615 : Blo 1389514 1390615 := bstep (se 1 (by rfl) ⟨1042961, by rfl⟩ : syracuseStep 1390615 = 2085923) B2085923
theorem B2086937 : Blo 1389514 2086937 := bstep (se 2 (by rfl) ⟨782601, by rfl⟩ : syracuseStep 2086937 = 1565203) B1565203
theorem B1390635 : Blo 1389514 1390635 := bstep (se 1 (by rfl) ⟨1042976, by rfl⟩ : syracuseStep 1390635 = 2085953) B2085953
theorem B1390647 : Blo 1389514 1390647 := bstep (se 1 (by rfl) ⟨1042985, by rfl⟩ : syracuseStep 1390647 = 2085971) B2085971
theorem B1390667 : Blo 1389514 1390667 := bstep (se 1 (by rfl) ⟨1043000, by rfl⟩ : syracuseStep 1390667 = 2086001) B2086001
theorem B2971723 : Blo 1389514 2971723 := bstep (se 1 (by rfl) ⟨2228792, by rfl⟩ : syracuseStep 2971723 = 4457585) B4457585
theorem B1390679 : Blo 1389514 1390679 := bstep (se 1 (by rfl) ⟨1043009, by rfl⟩ : syracuseStep 1390679 = 2086019) B2086019
theorem B4757597 : Blo 1389514 4757597 := bstep (se 3 (by rfl) ⟨892049, by rfl⟩ : syracuseStep 4757597 = 1784099) B1784099
theorem B1390699 : Blo 1389514 1390699 := bstep (se 1 (by rfl) ⟨1043024, by rfl⟩ : syracuseStep 1390699 = 2086049) B2086049
theorem B1390711 : Blo 1389514 1390711 := bstep (se 1 (by rfl) ⟨1043033, by rfl⟩ : syracuseStep 1390711 = 2086067) B2086067
theorem B7035011 : Blo 1389514 7035011 := bstep (se 1 (by rfl) ⟨5276258, by rfl⟩ : syracuseStep 7035011 = 10552517) B10552517
theorem B1390731 : Blo 1389514 1390731 := bstep (se 1 (by rfl) ⟨1043048, by rfl⟩ : syracuseStep 1390731 = 2086097) B2086097
theorem B2087051 : Blo 1389514 2087051 := bstep (se 1 (by rfl) ⟨1565288, by rfl⟩ : syracuseStep 2087051 = 3130577) B3130577
theorem B11876503 : Blo 1389514 11876503 := bstep (se 1 (by rfl) ⟨8907377, by rfl⟩ : syracuseStep 11876503 = 17814755) B17814755
theorem B1390743 : Blo 1389514 1390743 := bstep (se 1 (by rfl) ⟨1043057, by rfl⟩ : syracuseStep 1390743 = 2086115) B2086115
theorem B2087063 : Blo 1389514 2087063 := bstep (se 1 (by rfl) ⟨1565297, by rfl⟩ : syracuseStep 2087063 = 3130595) B3130595
theorem B1390763 : Blo 1389514 1390763 := bstep (se 1 (by rfl) ⟨1043072, by rfl⟩ : syracuseStep 1390763 = 2086145) B2086145
theorem B1390775 : Blo 1389514 1390775 := bstep (se 1 (by rfl) ⟨1043081, by rfl⟩ : syracuseStep 1390775 = 2086163) B2086163
theorem B3520705 : Blo 1389514 3520705 := bstep (se 2 (by rfl) ⟨1320264, by rfl⟩ : syracuseStep 3520705 = 2640529) B2640529
theorem B3127499 : Blo 1389514 3127499 := bstep (se 1 (by rfl) ⟨2345624, by rfl⟩ : syracuseStep 3127499 = 4691249) B4691249
theorem B1390795 : Blo 1389514 1390795 := bstep (se 1 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 1390795 = 2086193) B2086193
theorem B1390807 : Blo 1389514 1390807 := bstep (se 1 (by rfl) ⟨1043105, by rfl⟩ : syracuseStep 1390807 = 2086211) B2086211
theorem B2087129 : Blo 1389514 2087129 := bstep (se 2 (by rfl) ⟨782673, by rfl⟩ : syracuseStep 2087129 = 1565347) B1565347
theorem B1390827 : Blo 1389514 1390827 := bstep (se 1 (by rfl) ⟨1043120, by rfl⟩ : syracuseStep 1390827 = 2086241) B2086241
theorem B1390839 : Blo 1389514 1390839 := bstep (se 1 (by rfl) ⟨1043129, by rfl⟩ : syracuseStep 1390839 = 2086259) B2086259
theorem B3127553 : Blo 1389514 3127553 := bstep (se 2 (by rfl) ⟨1172832, by rfl⟩ : syracuseStep 3127553 = 2345665) B2345665
theorem B1390859 : Blo 1389514 1390859 := bstep (se 1 (by rfl) ⟨1043144, by rfl⟩ : syracuseStep 1390859 = 2086289) B2086289
theorem B1390871 : Blo 1389514 1390871 := bstep (se 1 (by rfl) ⟨1043153, by rfl⟩ : syracuseStep 1390871 = 2086307) B2086307
theorem B1390891 : Blo 1389514 1390891 := bstep (se 1 (by rfl) ⟨1043168, by rfl⟩ : syracuseStep 1390891 = 2086337) B2086337
theorem B4692275 : Blo 1389514 4692275 := bstep (se 1 (by rfl) ⟨3519206, by rfl⟩ : syracuseStep 4692275 = 7038413) B7038413
theorem B1390903 : Blo 1389514 1390903 := bstep (se 1 (by rfl) ⟨1043177, by rfl⟩ : syracuseStep 1390903 = 2086355) B2086355
theorem B1390923 : Blo 1389514 1390923 := bstep (se 1 (by rfl) ⟨1043192, by rfl⟩ : syracuseStep 1390923 = 2086385) B2086385
theorem B2087243 : Blo 1389514 2087243 := bstep (se 1 (by rfl) ⟨1565432, by rfl⟩ : syracuseStep 2087243 = 3130865) B3130865
theorem B1390935 : Blo 1389514 1390935 := bstep (se 1 (by rfl) ⟨1043201, by rfl⟩ : syracuseStep 1390935 = 2086403) B2086403
theorem B2087255 : Blo 1389514 2087255 := bstep (se 1 (by rfl) ⟨1565441, by rfl⟩ : syracuseStep 2087255 = 3130883) B3130883
theorem B1390955 : Blo 1389514 1390955 := bstep (se 1 (by rfl) ⟨1043216, by rfl⟩ : syracuseStep 1390955 = 2086433) B2086433
theorem B1390967 : Blo 1389514 1390967 := bstep (se 1 (by rfl) ⟨1043225, by rfl⟩ : syracuseStep 1390967 = 2086451) B2086451
theorem B1390987 : Blo 1389514 1390987 := bstep (se 1 (by rfl) ⟨1043240, by rfl⟩ : syracuseStep 1390987 = 2086481) B2086481
theorem B1759639 : Blo 1389514 1759639 := bstep (se 1 (by rfl) ⟨1319729, by rfl⟩ : syracuseStep 1759639 = 2639459) B2639459
theorem B1390999 : Blo 1389514 1390999 := bstep (se 1 (by rfl) ⟨1043249, by rfl⟩ : syracuseStep 1390999 = 2086499) B2086499
theorem B1391019 : Blo 1389514 1391019 := bstep (se 1 (by rfl) ⟨1043264, by rfl⟩ : syracuseStep 1391019 = 2086529) B2086529
theorem B1391031 : Blo 1389514 1391031 := bstep (se 1 (by rfl) ⟨1043273, by rfl⟩ : syracuseStep 1391031 = 2086547) B2086547
theorem B1391051 : Blo 1389514 1391051 := bstep (se 1 (by rfl) ⟨1043288, by rfl⟩ : syracuseStep 1391051 = 2086577) B2086577
theorem B1391063 : Blo 1389514 1391063 := bstep (se 1 (by rfl) ⟨1043297, by rfl⟩ : syracuseStep 1391063 = 2086595) B2086595
theorem B3127769 : Blo 1389514 3127769 := bstep (se 2 (by rfl) ⟨1172913, by rfl⟩ : syracuseStep 3127769 = 2345827) B2345827
theorem B1391083 : Blo 1389514 1391083 := bstep (se 1 (by rfl) ⟨1043312, by rfl⟩ : syracuseStep 1391083 = 2086625) B2086625
theorem B1391095 : Blo 1389514 1391095 := bstep (se 1 (by rfl) ⟨1043321, by rfl⟩ : syracuseStep 1391095 = 2086643) B2086643
theorem B1391115 : Blo 1389514 1391115 := bstep (se 1 (by rfl) ⟨1043336, by rfl⟩ : syracuseStep 1391115 = 2086673) B2086673
theorem B1391127 : Blo 1389514 1391127 := bstep (se 1 (by rfl) ⟨1043345, by rfl⟩ : syracuseStep 1391127 = 2086691) B2086691
theorem B1391147 : Blo 1389514 1391147 := bstep (se 1 (by rfl) ⟨1043360, by rfl⟩ : syracuseStep 1391147 = 2086721) B2086721
theorem B3127859 : Blo 1389514 3127859 := bstep (se 1 (by rfl) ⟨2345894, by rfl⟩ : syracuseStep 3127859 = 4691789) B4691789
theorem B1391159 : Blo 1389514 1391159 := bstep (se 1 (by rfl) ⟨1043369, by rfl⟩ : syracuseStep 1391159 = 2086739) B2086739
theorem B5634625 : Blo 1389514 5634625 := bstep (se 2 (by rfl) ⟨2112984, by rfl⟩ : syracuseStep 5634625 = 4225969) B4225969
theorem B4692545 : Blo 1389514 4692545 := bstep (se 2 (by rfl) ⟨1759704, by rfl⟩ : syracuseStep 4692545 = 3519409) B3519409
theorem B1391179 : Blo 1389514 1391179 := bstep (se 1 (by rfl) ⟨1043384, by rfl⟩ : syracuseStep 1391179 = 2086769) B2086769
theorem B1563223 : Blo 1389514 1563223 := bstep (se 1 (by rfl) ⟨1172417, by rfl⟩ : syracuseStep 1563223 = 2344835) B2344835
theorem B3127895 : Blo 1389514 3127895 := bstep (se 1 (by rfl) ⟨2345921, by rfl⟩ : syracuseStep 3127895 = 4691843) B4691843
theorem B1391191 : Blo 1389514 1391191 := bstep (se 1 (by rfl) ⟨1043393, by rfl⟩ : syracuseStep 1391191 = 2086787) B2086787
theorem B1391211 : Blo 1389514 1391211 := bstep (se 1 (by rfl) ⟨1043408, by rfl⟩ : syracuseStep 1391211 = 2086817) B2086817
theorem B1391223 : Blo 1389514 1391223 := bstep (se 1 (by rfl) ⟨1043417, by rfl⟩ : syracuseStep 1391223 = 2086835) B2086835
theorem B1391243 : Blo 1389514 1391243 := bstep (se 1 (by rfl) ⟨1043432, by rfl⟩ : syracuseStep 1391243 = 2086865) B2086865
theorem B1391255 : Blo 1389514 1391255 := bstep (se 1 (by rfl) ⟨1043441, by rfl⟩ : syracuseStep 1391255 = 2086883) B2086883
theorem B5282455 : Blo 1389514 5282455 := bstep (se 1 (by rfl) ⟨3961841, by rfl⟩ : syracuseStep 5282455 = 7923683) B7923683
theorem B1391275 : Blo 1389514 1391275 := bstep (se 1 (by rfl) ⟨1043456, by rfl⟩ : syracuseStep 1391275 = 2086913) B2086913
theorem B1391287 : Blo 1389514 1391287 := bstep (se 1 (by rfl) ⟨1043465, by rfl⟩ : syracuseStep 1391287 = 2086931) B2086931
theorem B4225729 : Blo 1389514 4225729 := bstep (se 2 (by rfl) ⟨1584648, by rfl⟩ : syracuseStep 4225729 = 3169297) B3169297
theorem B1391307 : Blo 1389514 1391307 := bstep (se 1 (by rfl) ⟨1043480, by rfl⟩ : syracuseStep 1391307 = 2086961) B2086961
theorem B1391319 : Blo 1389514 1391319 := bstep (se 1 (by rfl) ⟨1043489, by rfl⟩ : syracuseStep 1391319 = 2086979) B2086979
theorem B5012189 : Blo 1389514 5012189 := bstep (se 3 (by rfl) ⟨939785, by rfl⟩ : syracuseStep 5012189 = 1879571) B1879571
theorem B1391339 : Blo 1389514 1391339 := bstep (se 1 (by rfl) ⟨1043504, by rfl⟩ : syracuseStep 1391339 = 2087009) B2087009
theorem B1391351 : Blo 1389514 1391351 := bstep (se 1 (by rfl) ⟨1043513, by rfl⟩ : syracuseStep 1391351 = 2087027) B2087027
theorem B1563403 : Blo 1389514 1563403 := bstep (se 1 (by rfl) ⟨1172552, by rfl⟩ : syracuseStep 1563403 = 2345105) B2345105
theorem B3128075 : Blo 1389514 3128075 := bstep (se 1 (by rfl) ⟨2346056, by rfl⟩ : syracuseStep 3128075 = 4692113) B4692113
theorem B1391371 : Blo 1389514 1391371 := bstep (se 1 (by rfl) ⟨1043528, by rfl⟩ : syracuseStep 1391371 = 2087057) B2087057
theorem B3521303 : Blo 1389514 3521303 := bstep (se 1 (by rfl) ⟨2640977, by rfl⟩ : syracuseStep 3521303 = 5281955) B5281955
theorem B1391383 : Blo 1389514 1391383 := bstep (se 1 (by rfl) ⟨1043537, by rfl⟩ : syracuseStep 1391383 = 2087075) B2087075
theorem B1391403 : Blo 1389514 1391403 := bstep (se 1 (by rfl) ⟨1043552, by rfl⟩ : syracuseStep 1391403 = 2087105) B2087105
theorem B6773549 : Blo 1389514 6773549 := bstep (se 3 (by rfl) ⟨1270040, by rfl⟩ : syracuseStep 6773549 = 2540081) B2540081
theorem B1391415 : Blo 1389514 1391415 := bstep (se 1 (by rfl) ⟨1043561, by rfl⟩ : syracuseStep 1391415 = 2087123) B2087123
theorem B3128129 : Blo 1389514 3128129 := bstep (se 2 (by rfl) ⟨1173048, by rfl⟩ : syracuseStep 3128129 = 2346097) B2346097
theorem B7920449 : Blo 1389514 7920449 := bstep (se 2 (by rfl) ⟨2970168, by rfl⟩ : syracuseStep 7920449 = 5940337) B5940337
theorem B11279179 : Blo 1389514 11279179 := bstep (se 1 (by rfl) ⟨8459384, by rfl⟩ : syracuseStep 11279179 = 16918769) B16918769
theorem B1391435 : Blo 1389514 1391435 := bstep (se 1 (by rfl) ⟨1043576, by rfl⟩ : syracuseStep 1391435 = 2087153) B2087153
theorem B1391447 : Blo 1389514 1391447 := bstep (se 1 (by rfl) ⟨1043585, by rfl⟩ : syracuseStep 1391447 = 2087171) B2087171
theorem B1391467 : Blo 1389514 1391467 := bstep (se 1 (by rfl) ⟨1043600, by rfl⟩ : syracuseStep 1391467 = 2087201) B2087201
theorem B1563511 : Blo 1389514 1563511 := bstep (se 1 (by rfl) ⟨1172633, by rfl⟩ : syracuseStep 1563511 = 2345267) B2345267
theorem B1391479 : Blo 1389514 1391479 := bstep (se 1 (by rfl) ⟨1043609, by rfl⟩ : syracuseStep 1391479 = 2087219) B2087219
theorem B1391499 : Blo 1389514 1391499 := bstep (se 1 (by rfl) ⟨1043624, by rfl⟩ : syracuseStep 1391499 = 2087249) B2087249
theorem B1391511 : Blo 1389514 1391511 := bstep (se 1 (by rfl) ⟨1043633, by rfl⟩ : syracuseStep 1391511 = 2087267) B2087267
theorem B6683609 : Blo 1389514 6683609 := bstep (se 2 (by rfl) ⟨2506353, by rfl⟩ : syracuseStep 6683609 = 5012707) B5012707
theorem B8911889 : Blo 1389514 8911889 := bstep (se 2 (by rfl) ⟨3341958, by rfl⟩ : syracuseStep 8911889 = 6683917) B6683917
theorem B3128345 : Blo 1389514 3128345 := bstep (se 2 (by rfl) ⟨1173129, by rfl⟩ : syracuseStep 3128345 = 2346259) B2346259
theorem B1563691 : Blo 1389514 1563691 := bstep (se 1 (by rfl) ⟨1172768, by rfl⟩ : syracuseStep 1563691 = 2345537) B2345537
theorem B4693085 : Blo 1389514 4693085 := bstep (se 3 (by rfl) ⟨879953, by rfl⟩ : syracuseStep 4693085 = 1759907) B1759907
theorem B3128435 : Blo 1389514 3128435 := bstep (se 1 (by rfl) ⟨2346326, by rfl⟩ : syracuseStep 3128435 = 4692653) B4692653
theorem B1563799 : Blo 1389514 1563799 := bstep (se 1 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 1563799 = 2345699) B2345699
theorem B3128471 : Blo 1389514 3128471 := bstep (se 1 (by rfl) ⟨2346353, by rfl⟩ : syracuseStep 3128471 = 4692707) B4692707
theorem B2817281 : Blo 1389514 2817281 := bstep (se 2 (by rfl) ⟨1056480, by rfl⟩ : syracuseStep 2817281 = 2112961) B2112961
theorem B1563979 : Blo 1389514 1563979 := bstep (se 1 (by rfl) ⟨1172984, by rfl⟩ : syracuseStep 1563979 = 2345969) B2345969
theorem B3128651 : Blo 1389514 3128651 := bstep (se 1 (by rfl) ⟨2346488, by rfl⟩ : syracuseStep 3128651 = 4692977) B4692977
theorem B5938525 : Blo 1389514 5938525 := bstep (se 3 (by rfl) ⟨1113473, by rfl⟩ : syracuseStep 5938525 = 2226947) B2226947
theorem B3128705 : Blo 1389514 3128705 := bstep (se 2 (by rfl) ⟨1173264, by rfl⟩ : syracuseStep 3128705 = 2346529) B2346529
theorem B2506123 : Blo 1389514 2506123 := bstep (se 1 (by rfl) ⟨1879592, by rfl⟩ : syracuseStep 2506123 = 3759185) B3759185
theorem B8478103 : Blo 1389514 8478103 := bstep (se 1 (by rfl) ⟨6358577, by rfl⟩ : syracuseStep 8478103 = 12717155) B12717155
theorem B5283245 : Blo 1389514 5283245 := bstep (se 3 (by rfl) ⟨990608, by rfl⟩ : syracuseStep 5283245 = 1981217) B1981217
theorem B1564087 : Blo 1389514 1564087 := bstep (se 1 (by rfl) ⟨1173065, by rfl⟩ : syracuseStep 1564087 = 2346131) B2346131
theorem B23772689 : Blo 1389514 23772689 := bstep (se 2 (by rfl) ⟨8914758, by rfl⟩ : syracuseStep 23772689 = 17829517) B17829517
theorem B3522113 : Blo 1389514 3522113 := bstep (se 2 (by rfl) ⟨1320792, by rfl⟩ : syracuseStep 3522113 = 2641585) B2641585
theorem B21397061 : Blo 1389514 21397061 := bstep (se 4 (by rfl) ⟨2005974, by rfl⟩ : syracuseStep 21397061 = 4011949) B4011949
theorem B3128921 : Blo 1389514 3128921 := bstep (se 2 (by rfl) ⟨1173345, by rfl⟩ : syracuseStep 3128921 = 2346691) B2346691
theorem B1564267 : Blo 1389514 1564267 := bstep (se 1 (by rfl) ⟨1173200, by rfl⟩ : syracuseStep 1564267 = 2346401) B2346401
theorem B3129011 : Blo 1389514 3129011 := bstep (se 1 (by rfl) ⟨2346758, by rfl⟩ : syracuseStep 3129011 = 4693517) B4693517
theorem B2227915 : Blo 1389514 2227915 := bstep (se 1 (by rfl) ⟨1670936, by rfl⟩ : syracuseStep 2227915 = 3341873) B3341873
theorem B1564375 : Blo 1389514 1564375 := bstep (se 1 (by rfl) ⟨1173281, by rfl⟩ : syracuseStep 1564375 = 2346563) B2346563
theorem B3129047 : Blo 1389514 3129047 := bstep (se 1 (by rfl) ⟨2346785, by rfl⟩ : syracuseStep 3129047 = 4693571) B4693571
theorem B2506585 : Blo 1389514 2506585 := bstep (se 2 (by rfl) ⟨939969, by rfl⟩ : syracuseStep 2506585 = 1879939) B1879939
theorem B10166147 : Blo 1389514 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B1564555 : Blo 1389514 1564555 := bstep (se 1 (by rfl) ⟨1173416, by rfl⟩ : syracuseStep 1564555 = 2346833) B2346833
theorem B3129227 : Blo 1389514 3129227 := bstep (se 1 (by rfl) ⟨2346920, by rfl⟩ : syracuseStep 3129227 = 4693841) B4693841
theorem B3129281 : Blo 1389514 3129281 := bstep (se 2 (by rfl) ⟨1173480, by rfl⟩ : syracuseStep 3129281 = 2346961) B2346961
theorem B2817995 : Blo 1389514 2817995 := bstep (se 1 (by rfl) ⟨2113496, by rfl⟩ : syracuseStep 2817995 = 4226993) B4226993
theorem B12689369 : Blo 1389514 12689369 := bstep (se 2 (by rfl) ⟨4758513, by rfl⟩ : syracuseStep 12689369 = 9517027) B9517027
theorem B1564663 : Blo 1389514 1564663 := bstep (se 1 (by rfl) ⟨1173497, by rfl⟩ : syracuseStep 1564663 = 2346995) B2346995
theorem B5013515 : Blo 1389514 5013515 := bstep (se 1 (by rfl) ⟨3760136, by rfl⟩ : syracuseStep 5013515 = 7520273) B7520273
theorem B2818091 : Blo 1389514 2818091 := bstep (se 1 (by rfl) ⟨2113568, by rfl⟩ : syracuseStep 2818091 = 4227137) B4227137
theorem B11878487 : Blo 1389514 11878487 := bstep (se 1 (by rfl) ⟨8908865, by rfl⟩ : syracuseStep 11878487 = 17817731) B17817731
theorem B3129479 : Blo 1389514 3129479 := bstep (se 1 (by rfl) ⟨2347109, by rfl⟩ : syracuseStep 3129479 = 4694219) B4694219
theorem B1564807 : Blo 1389514 1564807 := bstep (se 1 (by rfl) ⟨1173605, by rfl⟩ : syracuseStep 1564807 = 2347211) B2347211
theorem B3956921 : Blo 1389514 3956921 := bstep (se 2 (by rfl) ⟨1483845, by rfl⟩ : syracuseStep 3956921 = 2967691) B2967691
theorem B15835337 : Blo 1389514 15835337 := bstep (se 2 (by rfl) ⟨5938251, by rfl⟩ : syracuseStep 15835337 = 11876503) B11876503
theorem B4694273 : Blo 1389514 4694273 := bstep (se 2 (by rfl) ⟨1760352, by rfl⟩ : syracuseStep 4694273 = 3520705) B3520705
theorem B3129659 : Blo 1389514 3129659 := bstep (se 1 (by rfl) ⟨2347244, by rfl⟩ : syracuseStep 3129659 = 4694489) B4694489
theorem B1564987 : Blo 1389514 1564987 := bstep (se 1 (by rfl) ⟨1173740, by rfl⟩ : syracuseStep 1564987 = 2347481) B2347481
theorem B8569223 : Blo 1389514 8569223 := bstep (se 1 (by rfl) ⟨6426917, by rfl⟩ : syracuseStep 8569223 = 12853835) B12853835
theorem B3342727 : Blo 1389514 3342727 := bstep (se 1 (by rfl) ⟨2507045, by rfl⟩ : syracuseStep 3342727 = 5014091) B5014091
theorem B3129785 : Blo 1389514 3129785 := bstep (se 2 (by rfl) ⟨1173669, by rfl⟩ : syracuseStep 3129785 = 2347339) B2347339
theorem B3342881 : Blo 1389514 3342881 := bstep (se 2 (by rfl) ⟨1253580, by rfl⟩ : syracuseStep 3342881 = 2507161) B2507161
theorem B7512749 : Blo 1389514 7512749 := bstep (se 3 (by rfl) ⟨1408640, by rfl⟩ : syracuseStep 7512749 = 2817281) B2817281
theorem B17154737 : Blo 1389514 17154737 := bstep (se 2 (by rfl) ⟨6433026, by rfl⟩ : syracuseStep 17154737 = 12866053) B12866053
theorem B45695681 : Blo 1389514 45695681 := bstep (se 2 (by rfl) ⟨17135880, by rfl⟩ : syracuseStep 45695681 = 34271761) B34271761
theorem B7914185 : Blo 1389514 7914185 := bstep (se 2 (by rfl) ⟨2967819, by rfl⟩ : syracuseStep 7914185 = 5935639) B5935639
theorem B7512833 : Blo 1389514 7512833 := bstep (se 2 (by rfl) ⟨2817312, by rfl⟩ : syracuseStep 7512833 = 5634625) B5634625
theorem B15246095 : Blo 1389514 15246095 := bstep (se 1 (by rfl) ⟨11434571, by rfl⟩ : syracuseStep 15246095 = 22869143) B22869143
theorem B3130127 : Blo 1389514 3130127 := bstep (se 1 (by rfl) ⟨2347595, by rfl⟩ : syracuseStep 3130127 = 4695191) B4695191
theorem B3130145 : Blo 1389514 3130145 := bstep (se 2 (by rfl) ⟨1173804, by rfl⟩ : syracuseStep 3130145 = 2347609) B2347609
theorem B10560293 : Blo 1389514 10560293 := bstep (se 4 (by rfl) ⟨990027, by rfl⟩ : syracuseStep 10560293 = 1980055) B1980055
theorem B4457369 : Blo 1389514 4457369 := bstep (se 2 (by rfl) ⟨1671513, by rfl⟩ : syracuseStep 4457369 = 3343027) B3343027
theorem B6685649 : Blo 1389514 6685649 := bstep (se 2 (by rfl) ⟨2507118, by rfl⟩ : syracuseStep 6685649 = 5014237) B5014237
theorem B22873099 : Blo 1389514 22873099 := bstep (se 1 (by rfl) ⟨17154824, by rfl⟩ : syracuseStep 22873099 = 34309649) B34309649
theorem B4457483 : Blo 1389514 4457483 := bstep (se 1 (by rfl) ⟨3343112, by rfl⟩ : syracuseStep 4457483 = 6686225) B6686225
theorem B4695083 : Blo 1389514 4695083 := bstep (se 1 (by rfl) ⟨3521312, by rfl⟩ : syracuseStep 4695083 = 7042625) B7042625
theorem B3130487 : Blo 1389514 3130487 := bstep (se 1 (by rfl) ⟨2347865, by rfl⟩ : syracuseStep 3130487 = 4695731) B4695731
theorem B2114731 : Blo 1389514 2114731 := bstep (se 1 (by rfl) ⟨1586048, by rfl⟩ : syracuseStep 2114731 = 3172097) B3172097
theorem B8914121 : Blo 1389514 8914121 := bstep (se 2 (by rfl) ⟨3342795, by rfl⟩ : syracuseStep 8914121 = 6685591) B6685591
theorem B3130667 : Blo 1389514 3130667 := bstep (se 1 (by rfl) ⟨2348000, by rfl⟩ : syracuseStep 3130667 = 4696001) B4696001
theorem B3171731 : Blo 1389514 3171731 := bstep (se 1 (by rfl) ⟨2378798, by rfl⟩ : syracuseStep 3171731 = 4757597) B4757597
theorem B2639375 : Blo 1389514 2639375 := bstep (se 1 (by rfl) ⟨1979531, by rfl⟩ : syracuseStep 2639375 = 3959063) B3959063
theorem B4228793 : Blo 1389514 4228793 := bstep (se 2 (by rfl) ⟨1585797, by rfl⟩ : syracuseStep 4228793 = 3171595) B3171595
theorem B8570605 : Blo 1389514 8570605 := bstep (se 3 (by rfl) ⟨1606988, by rfl⟩ : syracuseStep 8570605 = 3213977) B3213977
theorem B3958561 : Blo 1389514 3958561 := bstep (se 2 (by rfl) ⟨1484460, by rfl⟩ : syracuseStep 3958561 = 2968921) B2968921
theorem B2344889 : Blo 1389514 2344889 := bstep (se 2 (by rfl) ⟨879333, by rfl⟩ : syracuseStep 2344889 = 1758667) B1758667
theorem B5941259 : Blo 1389514 5941259 := bstep (se 1 (by rfl) ⟨4455944, by rfl⟩ : syracuseStep 5941259 = 8911889) B8911889
theorem B3565601 : Blo 1389514 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B26724593 : Blo 1389514 26724593 := bstep (se 2 (by rfl) ⟨10021722, by rfl⟩ : syracuseStep 26724593 = 20043445) B20043445
theorem B2820395 : Blo 1389514 2820395 := bstep (se 1 (by rfl) ⟨2115296, by rfl⟩ : syracuseStep 2820395 = 4230593) B4230593
theorem B5278067 : Blo 1389514 5278067 := bstep (se 1 (by rfl) ⟨3958550, by rfl⟩ : syracuseStep 5278067 = 7917101) B7917101
theorem B14264707 : Blo 1389514 14264707 := bstep (se 1 (by rfl) ⟨10698530, by rfl⟩ : syracuseStep 14264707 = 21397061) B21397061
theorem B7039385 : Blo 1389514 7039385 := bstep (se 2 (by rfl) ⟨2639769, by rfl⟩ : syracuseStep 7039385 = 5279539) B5279539
theorem B7514653 : Blo 1389514 7514653 := bstep (se 3 (by rfl) ⟨1408997, by rfl⟩ : syracuseStep 7514653 = 2817995) B2817995
theorem B7916075 : Blo 1389514 7916075 := bstep (se 1 (by rfl) ⟨5937056, by rfl⟩ : syracuseStep 7916075 = 11874113) B11874113
theorem B6777431 : Blo 1389514 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B10553975 : Blo 1389514 10553975 := bstep (se 1 (by rfl) ⟨7915481, by rfl⟩ : syracuseStep 10553975 = 15830963) B15830963
theorem B2345591 : Blo 1389514 2345591 := bstep (se 1 (by rfl) ⟨1759193, by rfl⟩ : syracuseStep 2345591 = 3518387) B3518387
theorem B3517303 : Blo 1389514 3517303 := bstep (se 1 (by rfl) ⟨2637977, by rfl⟩ : syracuseStep 3517303 = 5275955) B5275955
theorem B10030027 : Blo 1389514 10030027 := bstep (se 1 (by rfl) ⟨7522520, by rfl⟩ : syracuseStep 10030027 = 15045041) B15045041
theorem B3959837 : Blo 1389514 3959837 := bstep (se 3 (by rfl) ⟨742469, by rfl⟩ : syracuseStep 3959837 = 1484939) B1484939
theorem B5868587 : Blo 1389514 5868587 := bstep (se 1 (by rfl) ⟨4401440, by rfl⟩ : syracuseStep 5868587 = 8802881) B8802881
theorem B15838253 : Blo 1389514 15838253 := bstep (se 3 (by rfl) ⟨2969672, by rfl⟩ : syracuseStep 15838253 = 5939345) B5939345
theorem B2346043 : Blo 1389514 2346043 := bstep (se 1 (by rfl) ⟨1759532, by rfl⟩ : syracuseStep 2346043 = 3519065) B3519065
theorem B7924823 : Blo 1389514 7924823 := bstep (se 1 (by rfl) ⟨5943617, by rfl⟩ : syracuseStep 7924823 = 11887235) B11887235
theorem B2641015 : Blo 1389514 2641015 := bstep (se 1 (by rfl) ⟨1980761, by rfl⟩ : syracuseStep 2641015 = 3961523) B3961523
theorem B2346185 : Blo 1389514 2346185 := bstep (se 2 (by rfl) ⟨879819, by rfl⟩ : syracuseStep 2346185 = 1759639) B1759639
theorem B3960065 : Blo 1389514 3960065 := bstep (se 2 (by rfl) ⟨1485024, by rfl⟩ : syracuseStep 3960065 = 2970049) B2970049
theorem B3517739 : Blo 1389514 3517739 := bstep (se 1 (by rfl) ⟨2638304, by rfl⟩ : syracuseStep 3517739 = 5276609) B5276609
theorem B15232387 : Blo 1389514 15232387 := bstep (se 1 (by rfl) ⟨11424290, by rfl⟩ : syracuseStep 15232387 = 22848581) B22848581
theorem B5008787 : Blo 1389514 5008787 := bstep (se 1 (by rfl) ⟨3756590, by rfl⟩ : syracuseStep 5008787 = 7513181) B7513181
theorem B2084297 : Blo 1389514 2084297 := bstep (se 2 (by rfl) ⟨781611, by rfl⟩ : syracuseStep 2084297 = 1563223) B1563223
theorem B2084411 : Blo 1389514 2084411 := bstep (se 1 (by rfl) ⟨1563308, by rfl⟩ : syracuseStep 2084411 = 3126617) B3126617
theorem B10554947 : Blo 1389514 10554947 := bstep (se 1 (by rfl) ⟨7916210, by rfl⟩ : syracuseStep 10554947 = 15832421) B15832421
theorem B3960407 : Blo 1389514 3960407 := bstep (se 1 (by rfl) ⟨2970305, by rfl⟩ : syracuseStep 3960407 = 5940611) B5940611
theorem B2084471 : Blo 1389514 2084471 := bstep (se 1 (by rfl) ⟨1563353, by rfl⟩ : syracuseStep 2084471 = 3126707) B3126707
theorem B1584775 : Blo 1389514 1584775 := bstep (se 1 (by rfl) ⟨1188581, by rfl⟩ : syracuseStep 1584775 = 2377163) B2377163
theorem B2084495 : Blo 1389514 2084495 := bstep (se 1 (by rfl) ⟨1563371, by rfl⟩ : syracuseStep 2084495 = 3126743) B3126743
theorem B1879723 : Blo 1389514 1879723 := bstep (se 1 (by rfl) ⟨1409792, by rfl⟩ : syracuseStep 1879723 = 2819585) B2819585
theorem B2084537 : Blo 1389514 2084537 := bstep (se 2 (by rfl) ⟨781701, by rfl⟩ : syracuseStep 2084537 = 1563403) B1563403
theorem B3960521 : Blo 1389514 3960521 := bstep (se 2 (by rfl) ⟨1485195, by rfl⟩ : syracuseStep 3960521 = 2970391) B2970391
theorem B11882213 : Blo 1389514 11882213 := bstep (se 4 (by rfl) ⟨1113957, by rfl⟩ : syracuseStep 11882213 = 2227915) B2227915
theorem B2084615 : Blo 1389514 2084615 := bstep (se 1 (by rfl) ⟨1563461, by rfl⟩ : syracuseStep 2084615 = 3126923) B3126923
theorem B2674447 : Blo 1389514 2674447 := bstep (se 1 (by rfl) ⟨2005835, by rfl⟩ : syracuseStep 2674447 = 4011671) B4011671
theorem B7139087 : Blo 1389514 7139087 := bstep (se 1 (by rfl) ⟨5354315, by rfl⟩ : syracuseStep 7139087 = 10708631) B10708631
theorem B2084651 : Blo 1389514 2084651 := bstep (se 1 (by rfl) ⟨1563488, by rfl⟩ : syracuseStep 2084651 = 3126977) B3126977
theorem B2084681 : Blo 1389514 2084681 := bstep (se 2 (by rfl) ⟨781755, by rfl⟩ : syracuseStep 2084681 = 1563511) B1563511
theorem B2346887 : Blo 1389514 2346887 := bstep (se 1 (by rfl) ⟨1760165, by rfl⟩ : syracuseStep 2346887 = 3520331) B3520331
theorem B2084795 : Blo 1389514 2084795 := bstep (se 1 (by rfl) ⟨1563596, by rfl⟩ : syracuseStep 2084795 = 3127193) B3127193
theorem B7917533 : Blo 1389514 7917533 := bstep (se 3 (by rfl) ⟨1484537, by rfl⟩ : syracuseStep 7917533 = 2969075) B2969075
theorem B2084855 : Blo 1389514 2084855 := bstep (se 1 (by rfl) ⟨1563641, by rfl⟩ : syracuseStep 2084855 = 3127283) B3127283
theorem B2084879 : Blo 1389514 2084879 := bstep (se 1 (by rfl) ⟨1563659, by rfl⟩ : syracuseStep 2084879 = 3127319) B3127319
theorem B3051535 : Blo 1389514 3051535 := bstep (se 1 (by rfl) ⟨2288651, by rfl⟩ : syracuseStep 3051535 = 4577303) B4577303
theorem B2084921 : Blo 1389514 2084921 := bstep (se 2 (by rfl) ⟨781845, by rfl⟩ : syracuseStep 2084921 = 1563691) B1563691
theorem B4690007 : Blo 1389514 4690007 := bstep (se 1 (by rfl) ⟨3517505, by rfl⟩ : syracuseStep 4690007 = 7035011) B7035011
theorem B3518579 : Blo 1389514 3518579 := bstep (se 1 (by rfl) ⟨2638934, by rfl⟩ : syracuseStep 3518579 = 5277869) B5277869
theorem B2084999 : Blo 1389514 2084999 := bstep (se 1 (by rfl) ⟨1563749, by rfl⟩ : syracuseStep 2084999 = 3127499) B3127499
theorem B3518599 : Blo 1389514 3518599 := bstep (se 1 (by rfl) ⟨2638949, by rfl⟩ : syracuseStep 3518599 = 5277899) B5277899
theorem B2085035 : Blo 1389514 2085035 := bstep (se 1 (by rfl) ⟨1563776, by rfl⟩ : syracuseStep 2085035 = 3127553) B3127553
theorem B2085065 : Blo 1389514 2085065 := bstep (se 2 (by rfl) ⟨781899, by rfl⟩ : syracuseStep 2085065 = 1563799) B1563799
theorem B3617057 : Blo 1389514 3617057 := bstep (se 2 (by rfl) ⟨1356396, by rfl⟩ : syracuseStep 3617057 = 2712793) B2712793
theorem B2085179 : Blo 1389514 2085179 := bstep (se 1 (by rfl) ⟨1563884, by rfl⟩ : syracuseStep 2085179 = 3127769) B3127769
theorem B1880393 : Blo 1389514 1880393 := bstep (se 2 (by rfl) ⟨705147, by rfl⟩ : syracuseStep 1880393 = 1410295) B1410295
theorem B2085239 : Blo 1389514 2085239 := bstep (se 1 (by rfl) ⟨1563929, by rfl⟩ : syracuseStep 2085239 = 3127859) B3127859
theorem B2085263 : Blo 1389514 2085263 := bstep (se 1 (by rfl) ⟨1563947, by rfl⟩ : syracuseStep 2085263 = 3127895) B3127895
theorem B3518873 : Blo 1389514 3518873 := bstep (se 2 (by rfl) ⟨1319577, by rfl⟩ : syracuseStep 3518873 = 2639155) B2639155
theorem B2085305 : Blo 1389514 2085305 := bstep (se 2 (by rfl) ⟨781989, by rfl⟩ : syracuseStep 2085305 = 1563979) B1563979
theorem B1978825 : Blo 1389514 1978825 := bstep (se 2 (by rfl) ⟨742059, by rfl⟩ : syracuseStep 1978825 = 1484119) B1484119
theorem B6681035 : Blo 1389514 6681035 := bstep (se 1 (by rfl) ⟨5010776, by rfl⟩ : syracuseStep 6681035 = 10021553) B10021553
theorem B7918033 : Blo 1389514 7918033 := bstep (se 2 (by rfl) ⟨2969262, by rfl⟩ : syracuseStep 7918033 = 5938525) B5938525
theorem B2085383 : Blo 1389514 2085383 := bstep (se 1 (by rfl) ⟨1564037, by rfl⟩ : syracuseStep 2085383 = 3128075) B3128075
theorem B2347535 : Blo 1389514 2347535 := bstep (se 1 (by rfl) ⟨1760651, by rfl⟩ : syracuseStep 2347535 = 3521303) B3521303
theorem B2085419 : Blo 1389514 2085419 := bstep (se 1 (by rfl) ⟨1564064, by rfl⟩ : syracuseStep 2085419 = 3128129) B3128129
theorem B5280299 : Blo 1389514 5280299 := bstep (se 1 (by rfl) ⟨3960224, by rfl⟩ : syracuseStep 5280299 = 7920449) B7920449
theorem B1978939 : Blo 1389514 1978939 := bstep (se 1 (by rfl) ⟨1484204, by rfl⟩ : syracuseStep 1978939 = 2968409) B2968409
theorem B3519035 : Blo 1389514 3519035 := bstep (se 1 (by rfl) ⟨2639276, by rfl⟩ : syracuseStep 3519035 = 5278553) B5278553
theorem B4690493 : Blo 1389514 4690493 := bstep (se 3 (by rfl) ⟨879467, by rfl⟩ : syracuseStep 4690493 = 1758935) B1758935
theorem B2085449 : Blo 1389514 2085449 := bstep (se 2 (by rfl) ⟨782043, by rfl⟩ : syracuseStep 2085449 = 1564087) B1564087
theorem B2085563 : Blo 1389514 2085563 := bstep (se 1 (by rfl) ⟨1564172, by rfl⟩ : syracuseStep 2085563 = 3128345) B3128345
theorem B36123329 : Blo 1389514 36123329 := bstep (se 2 (by rfl) ⟨13546248, by rfl⟩ : syracuseStep 36123329 = 27092497) B27092497
theorem B8024777 : Blo 1389514 8024777 := bstep (se 2 (by rfl) ⟨3009291, by rfl⟩ : syracuseStep 8024777 = 6018583) B6018583
theorem B7516901 : Blo 1389514 7516901 := bstep (se 4 (by rfl) ⟨704709, by rfl⟩ : syracuseStep 7516901 = 1409419) B1409419
theorem B2085623 : Blo 1389514 2085623 := bstep (se 1 (by rfl) ⟨1564217, by rfl⟩ : syracuseStep 2085623 = 3128435) B3128435
theorem B3519247 : Blo 1389514 3519247 := bstep (se 1 (by rfl) ⟨2639435, by rfl⟩ : syracuseStep 3519247 = 5278871) B5278871
theorem B2085647 : Blo 1389514 2085647 := bstep (se 1 (by rfl) ⟨1564235, by rfl⟩ : syracuseStep 2085647 = 3128471) B3128471
theorem B2085689 : Blo 1389514 2085689 := bstep (se 2 (by rfl) ⟨782133, by rfl⟩ : syracuseStep 2085689 = 1564267) B1564267
theorem B22549337 : Blo 1389514 22549337 := bstep (se 2 (by rfl) ⟨8456001, by rfl⟩ : syracuseStep 22549337 = 16912003) B16912003
theorem B2085767 : Blo 1389514 2085767 := bstep (se 1 (by rfl) ⟨1564325, by rfl⟩ : syracuseStep 2085767 = 3128651) B3128651
theorem B2085803 : Blo 1389514 2085803 := bstep (se 1 (by rfl) ⟨1564352, by rfl⟩ : syracuseStep 2085803 = 3128705) B3128705
theorem B7041977 : Blo 1389514 7041977 := bstep (se 2 (by rfl) ⟨2640741, by rfl⟩ : syracuseStep 7041977 = 5281483) B5281483
theorem B2085833 : Blo 1389514 2085833 := bstep (se 2 (by rfl) ⟨782187, by rfl⟩ : syracuseStep 2085833 = 1564375) B1564375
theorem B1389575 : Blo 1389514 1389575 := bstep (se 1 (by rfl) ⟨1042181, by rfl⟩ : syracuseStep 1389575 = 2084363) B2084363
theorem B15848459 : Blo 1389514 15848459 := bstep (se 1 (by rfl) ⟨11886344, by rfl⟩ : syracuseStep 15848459 = 23772689) B23772689
theorem B1389583 : Blo 1389514 1389583 := bstep (se 1 (by rfl) ⟨1042187, by rfl⟩ : syracuseStep 1389583 = 2084375) B2084375
theorem B3519521 : Blo 1389514 3519521 := bstep (se 2 (by rfl) ⟨1319820, by rfl⟩ : syracuseStep 3519521 = 2639641) B2639641
theorem B2348075 : Blo 1389514 2348075 := bstep (se 1 (by rfl) ⟨1761056, by rfl⟩ : syracuseStep 2348075 = 3522113) B3522113
theorem B1389627 : Blo 1389514 1389627 := bstep (se 1 (by rfl) ⟨1042220, by rfl⟩ : syracuseStep 1389627 = 2084441) B2084441
theorem B2085947 : Blo 1389514 2085947 := bstep (se 1 (by rfl) ⟨1564460, by rfl⟩ : syracuseStep 2085947 = 3128921) B3128921
theorem B4011095 : Blo 1389514 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B2086007 : Blo 1389514 2086007 := bstep (se 1 (by rfl) ⟨1564505, by rfl⟩ : syracuseStep 2086007 = 3129011) B3129011
theorem B1389703 : Blo 1389514 1389703 := bstep (se 1 (by rfl) ⟨1042277, by rfl⟩ : syracuseStep 1389703 = 2084555) B2084555
theorem B1389711 : Blo 1389514 1389711 := bstep (se 1 (by rfl) ⟨1042283, by rfl⟩ : syracuseStep 1389711 = 2084567) B2084567
theorem B2086031 : Blo 1389514 2086031 := bstep (se 1 (by rfl) ⟨1564523, by rfl⟩ : syracuseStep 2086031 = 3129047) B3129047
theorem B3126419 : Blo 1389514 3126419 := bstep (se 1 (by rfl) ⟨2344814, by rfl⟩ : syracuseStep 3126419 = 4689629) B4689629
theorem B2086073 : Blo 1389514 2086073 := bstep (se 2 (by rfl) ⟨782277, by rfl⟩ : syracuseStep 2086073 = 1564555) B1564555
theorem B1389755 : Blo 1389514 1389755 := bstep (se 1 (by rfl) ⟨1042316, by rfl⟩ : syracuseStep 1389755 = 2084633) B2084633
theorem B3126473 : Blo 1389514 3126473 := bstep (se 2 (by rfl) ⟨1172427, by rfl⟩ : syracuseStep 3126473 = 2344855) B2344855
theorem B1389831 : Blo 1389514 1389831 := bstep (se 1 (by rfl) ⟨1042373, by rfl⟩ : syracuseStep 1389831 = 2084747) B2084747
theorem B2086151 : Blo 1389514 2086151 := bstep (se 1 (by rfl) ⟨1564613, by rfl⟩ : syracuseStep 2086151 = 3129227) B3129227
theorem B1389839 : Blo 1389514 1389839 := bstep (se 1 (by rfl) ⟨1042379, by rfl⟩ : syracuseStep 1389839 = 2084759) B2084759
theorem B2086187 : Blo 1389514 2086187 := bstep (se 1 (by rfl) ⟨1564640, by rfl⟩ : syracuseStep 2086187 = 3129281) B3129281
theorem B1389883 : Blo 1389514 1389883 := bstep (se 1 (by rfl) ⟨1042412, by rfl⟩ : syracuseStep 1389883 = 2084825) B2084825
theorem B8459579 : Blo 1389514 8459579 := bstep (se 1 (by rfl) ⟨6344684, by rfl⟩ : syracuseStep 8459579 = 12689369) B12689369
theorem B2086217 : Blo 1389514 2086217 := bstep (se 2 (by rfl) ⟨782331, by rfl⟩ : syracuseStep 2086217 = 1564663) B1564663
theorem B1389959 : Blo 1389514 1389959 := bstep (se 1 (by rfl) ⟨1042469, by rfl⟩ : syracuseStep 1389959 = 2084939) B2084939
theorem B1389967 : Blo 1389514 1389967 := bstep (se 1 (by rfl) ⟨1042475, by rfl⟩ : syracuseStep 1389967 = 2084951) B2084951
theorem B3962297 : Blo 1389514 3962297 := bstep (se 2 (by rfl) ⟨1485861, by rfl⟩ : syracuseStep 3962297 = 2971723) B2971723
theorem B1390011 : Blo 1389514 1390011 := bstep (se 1 (by rfl) ⟨1042508, by rfl⟩ : syracuseStep 1390011 = 2085017) B2085017
theorem B2086331 : Blo 1389514 2086331 := bstep (se 1 (by rfl) ⟨1564748, by rfl⟩ : syracuseStep 2086331 = 3129497) B3129497
theorem B2086391 : Blo 1389514 2086391 := bstep (se 1 (by rfl) ⟨1564793, by rfl⟩ : syracuseStep 2086391 = 3129587) B3129587
theorem B1390087 : Blo 1389514 1390087 := bstep (se 1 (by rfl) ⟨1042565, by rfl⟩ : syracuseStep 1390087 = 2085131) B2085131
theorem B1390095 : Blo 1389514 1390095 := bstep (se 1 (by rfl) ⟨1042571, by rfl⟩ : syracuseStep 1390095 = 2085143) B2085143
theorem B2086415 : Blo 1389514 2086415 := bstep (se 1 (by rfl) ⟨1564811, by rfl⟩ : syracuseStep 2086415 = 3129623) B3129623
theorem B1758763 : Blo 1389514 1758763 := bstep (se 1 (by rfl) ⟨1319072, by rfl⟩ : syracuseStep 1758763 = 2638145) B2638145
theorem B2086457 : Blo 1389514 2086457 := bstep (se 2 (by rfl) ⟨782421, by rfl⟩ : syracuseStep 2086457 = 1564843) B1564843
theorem B1390139 : Blo 1389514 1390139 := bstep (se 1 (by rfl) ⟨1042604, by rfl⟩ : syracuseStep 1390139 = 2085209) B2085209
theorem B1390215 : Blo 1389514 1390215 := bstep (se 1 (by rfl) ⟨1042661, by rfl⟩ : syracuseStep 1390215 = 2085323) B2085323
theorem B2086535 : Blo 1389514 2086535 := bstep (se 1 (by rfl) ⟨1564901, by rfl⟩ : syracuseStep 2086535 = 3129803) B3129803
theorem B1390223 : Blo 1389514 1390223 := bstep (se 1 (by rfl) ⟨1042667, by rfl⟩ : syracuseStep 1390223 = 2085335) B2085335
theorem B2086571 : Blo 1389514 2086571 := bstep (se 1 (by rfl) ⟨1564928, by rfl⟩ : syracuseStep 2086571 = 3129857) B3129857
theorem B1390267 : Blo 1389514 1390267 := bstep (se 1 (by rfl) ⟨1042700, by rfl⟩ : syracuseStep 1390267 = 2085401) B2085401
theorem B2086601 : Blo 1389514 2086601 := bstep (se 2 (by rfl) ⟨782475, by rfl⟩ : syracuseStep 2086601 = 1564951) B1564951
theorem B1390343 : Blo 1389514 1390343 := bstep (se 1 (by rfl) ⟨1042757, by rfl⟩ : syracuseStep 1390343 = 2085515) B2085515
theorem B1758991 : Blo 1389514 1758991 := bstep (se 1 (by rfl) ⟨1319243, by rfl⟩ : syracuseStep 1758991 = 2638487) B2638487
theorem B1390351 : Blo 1389514 1390351 := bstep (se 1 (by rfl) ⟨1042763, by rfl⟩ : syracuseStep 1390351 = 2085527) B2085527
theorem B1390395 : Blo 1389514 1390395 := bstep (se 1 (by rfl) ⟨1042796, by rfl⟩ : syracuseStep 1390395 = 2085593) B2085593
theorem B2086715 : Blo 1389514 2086715 := bstep (se 1 (by rfl) ⟨1565036, by rfl⟩ : syracuseStep 2086715 = 3130073) B3130073
theorem B2086775 : Blo 1389514 2086775 := bstep (se 1 (by rfl) ⟨1565081, by rfl⟩ : syracuseStep 2086775 = 3130163) B3130163
theorem B3127175 : Blo 1389514 3127175 := bstep (se 1 (by rfl) ⟨2345381, by rfl⟩ : syracuseStep 3127175 = 4690763) B4690763
theorem B1390471 : Blo 1389514 1390471 := bstep (se 1 (by rfl) ⟨1042853, by rfl⟩ : syracuseStep 1390471 = 2085707) B2085707
theorem B1390479 : Blo 1389514 1390479 := bstep (se 1 (by rfl) ⟨1042859, by rfl⟩ : syracuseStep 1390479 = 2085719) B2085719
theorem B2086799 : Blo 1389514 2086799 := bstep (se 1 (by rfl) ⟨1565099, by rfl⟩ : syracuseStep 2086799 = 3130199) B3130199
theorem B4691897 : Blo 1389514 4691897 := bstep (se 2 (by rfl) ⟨1759461, by rfl⟩ : syracuseStep 4691897 = 3518923) B3518923
theorem B2086841 : Blo 1389514 2086841 := bstep (se 2 (by rfl) ⟨782565, by rfl⟩ : syracuseStep 2086841 = 1565131) B1565131
theorem B1390523 : Blo 1389514 1390523 := bstep (se 1 (by rfl) ⟨1042892, by rfl⟩ : syracuseStep 1390523 = 2085785) B2085785
theorem B1390599 : Blo 1389514 1390599 := bstep (se 1 (by rfl) ⟨1042949, by rfl⟩ : syracuseStep 1390599 = 2085899) B2085899
theorem B2086919 : Blo 1389514 2086919 := bstep (se 1 (by rfl) ⟨1565189, by rfl⟩ : syracuseStep 2086919 = 3130379) B3130379
theorem B3520523 : Blo 1389514 3520523 := bstep (se 1 (by rfl) ⟨2640392, by rfl⟩ : syracuseStep 3520523 = 5280785) B5280785
theorem B1390607 : Blo 1389514 1390607 := bstep (se 1 (by rfl) ⟨1042955, by rfl⟩ : syracuseStep 1390607 = 2085911) B2085911
theorem B2086955 : Blo 1389514 2086955 := bstep (se 1 (by rfl) ⟨1565216, by rfl⟩ : syracuseStep 2086955 = 3130433) B3130433
theorem B3127355 : Blo 1389514 3127355 := bstep (se 1 (by rfl) ⟨2345516, by rfl⟩ : syracuseStep 3127355 = 4691033) B4691033
theorem B1390651 : Blo 1389514 1390651 := bstep (se 1 (by rfl) ⟨1042988, by rfl⟩ : syracuseStep 1390651 = 2085977) B2085977
theorem B2086985 : Blo 1389514 2086985 := bstep (se 2 (by rfl) ⟨782619, by rfl⟩ : syracuseStep 2086985 = 1565239) B1565239
theorem B10016855 : Blo 1389514 10016855 := bstep (se 1 (by rfl) ⟨7512641, by rfl⟩ : syracuseStep 10016855 = 15025283) B15025283
theorem B1390727 : Blo 1389514 1390727 := bstep (se 1 (by rfl) ⟨1043045, by rfl⟩ : syracuseStep 1390727 = 2086091) B2086091
theorem B1980551 : Blo 1389514 1980551 := bstep (se 1 (by rfl) ⟨1485413, by rfl⟩ : syracuseStep 1980551 = 2970827) B2970827
theorem B1390735 : Blo 1389514 1390735 := bstep (se 1 (by rfl) ⟨1043051, by rfl⟩ : syracuseStep 1390735 = 2086103) B2086103
theorem B3127481 : Blo 1389514 3127481 := bstep (se 2 (by rfl) ⟨1172805, by rfl⟩ : syracuseStep 3127481 = 2345611) B2345611
theorem B1390779 : Blo 1389514 1390779 := bstep (se 1 (by rfl) ⟨1043084, by rfl⟩ : syracuseStep 1390779 = 2086169) B2086169
theorem B2087099 : Blo 1389514 2087099 := bstep (se 1 (by rfl) ⟨1565324, by rfl⟩ : syracuseStep 2087099 = 3130649) B3130649
theorem B7043273 : Blo 1389514 7043273 := bstep (se 2 (by rfl) ⟨2641227, by rfl⟩ : syracuseStep 7043273 = 5282455) B5282455
theorem B2087159 : Blo 1389514 2087159 := bstep (se 1 (by rfl) ⟨1565369, by rfl⟩ : syracuseStep 2087159 = 3130739) B3130739
theorem B5634305 : Blo 1389514 5634305 := bstep (se 2 (by rfl) ⟨2112864, by rfl⟩ : syracuseStep 5634305 = 4225729) B4225729
theorem B1390855 : Blo 1389514 1390855 := bstep (se 1 (by rfl) ⟨1043141, by rfl⟩ : syracuseStep 1390855 = 2086283) B2086283
theorem B1390863 : Blo 1389514 1390863 := bstep (se 1 (by rfl) ⟨1043147, by rfl⟩ : syracuseStep 1390863 = 2086295) B2086295
theorem B2087183 : Blo 1389514 2087183 := bstep (se 1 (by rfl) ⟨1565387, by rfl⟩ : syracuseStep 2087183 = 3130775) B3130775
theorem B2087225 : Blo 1389514 2087225 := bstep (se 2 (by rfl) ⟨782709, by rfl⟩ : syracuseStep 2087225 = 1565419) B1565419
theorem B1390907 : Blo 1389514 1390907 := bstep (se 1 (by rfl) ⟨1043180, by rfl⟩ : syracuseStep 1390907 = 2086361) B2086361
theorem B1390983 : Blo 1389514 1390983 := bstep (se 1 (by rfl) ⟨1043237, by rfl⟩ : syracuseStep 1390983 = 2086475) B2086475
theorem B1390991 : Blo 1389514 1390991 := bstep (se 1 (by rfl) ⟨1043243, by rfl⟩ : syracuseStep 1390991 = 2086487) B2086487
theorem B7920017 : Blo 1389514 7920017 := bstep (se 2 (by rfl) ⟨2970006, by rfl⟩ : syracuseStep 7920017 = 5940013) B5940013
theorem B15038905 : Blo 1389514 15038905 := bstep (se 2 (by rfl) ⟨5639589, by rfl⟩ : syracuseStep 15038905 = 11279179) B11279179
theorem B1391035 : Blo 1389514 1391035 := bstep (se 1 (by rfl) ⟨1043276, by rfl⟩ : syracuseStep 1391035 = 2086553) B2086553
theorem B1759735 : Blo 1389514 1759735 := bstep (se 1 (by rfl) ⟨1319801, by rfl⟩ : syracuseStep 1759735 = 2639603) B2639603
theorem B1391111 : Blo 1389514 1391111 := bstep (se 1 (by rfl) ⟨1043333, by rfl⟩ : syracuseStep 1391111 = 2086667) B2086667
theorem B4692491 : Blo 1389514 4692491 := bstep (se 1 (by rfl) ⟨3519368, by rfl⟩ : syracuseStep 4692491 = 7038737) B7038737
theorem B3127823 : Blo 1389514 3127823 := bstep (se 1 (by rfl) ⟨2345867, by rfl⟩ : syracuseStep 3127823 = 4691735) B4691735
theorem B1391119 : Blo 1389514 1391119 := bstep (se 1 (by rfl) ⟨1043339, by rfl⟩ : syracuseStep 1391119 = 2086679) B2086679
theorem B3127841 : Blo 1389514 3127841 := bstep (se 2 (by rfl) ⟨1172940, by rfl⟩ : syracuseStep 3127841 = 2345881) B2345881
theorem B1391163 : Blo 1389514 1391163 := bstep (se 1 (by rfl) ⟨1043372, by rfl⟩ : syracuseStep 1391163 = 2086745) B2086745
theorem B4692599 : Blo 1389514 4692599 := bstep (se 1 (by rfl) ⟨3519449, by rfl⟩ : syracuseStep 4692599 = 7038899) B7038899
theorem B1391239 : Blo 1389514 1391239 := bstep (se 1 (by rfl) ⟨1043429, by rfl⟩ : syracuseStep 1391239 = 2086859) B2086859
theorem B1391247 : Blo 1389514 1391247 := bstep (se 1 (by rfl) ⟨1043435, by rfl⟩ : syracuseStep 1391247 = 2086871) B2086871
theorem B3521171 : Blo 1389514 3521171 := bstep (se 1 (by rfl) ⟨2640878, by rfl⟩ : syracuseStep 3521171 = 5281757) B5281757
theorem B1391291 : Blo 1389514 1391291 := bstep (se 1 (by rfl) ⟨1043468, by rfl⟩ : syracuseStep 1391291 = 2086937) B2086937
theorem B1391367 : Blo 1389514 1391367 := bstep (se 1 (by rfl) ⟨1043525, by rfl⟩ : syracuseStep 1391367 = 2087051) B2087051
theorem B1391375 : Blo 1389514 1391375 := bstep (se 1 (by rfl) ⟨1043531, by rfl⟩ : syracuseStep 1391375 = 2087063) B2087063
theorem B1760059 : Blo 1389514 1760059 := bstep (se 1 (by rfl) ⟨1320044, by rfl⟩ : syracuseStep 1760059 = 2640089) B2640089
theorem B1391419 : Blo 1389514 1391419 := bstep (se 1 (by rfl) ⟨1043564, by rfl⟩ : syracuseStep 1391419 = 2087129) B2087129
theorem B3128183 : Blo 1389514 3128183 := bstep (se 1 (by rfl) ⟨2346137, by rfl⟩ : syracuseStep 3128183 = 4692275) B4692275
theorem B1391495 : Blo 1389514 1391495 := bstep (se 1 (by rfl) ⟨1043621, by rfl⟩ : syracuseStep 1391495 = 2087243) B2087243
theorem B1391503 : Blo 1389514 1391503 := bstep (se 1 (by rfl) ⟨1043627, by rfl⟩ : syracuseStep 1391503 = 2087255) B2087255
theorem B3521465 : Blo 1389514 3521465 := bstep (se 2 (by rfl) ⟨1320549, by rfl⟩ : syracuseStep 3521465 = 2641099) B2641099
theorem B1563655 : Blo 1389514 1563655 := bstep (se 1 (by rfl) ⟨1172741, by rfl⟩ : syracuseStep 1563655 = 2345483) B2345483
theorem B3128363 : Blo 1389514 3128363 := bstep (se 1 (by rfl) ⟨2346272, by rfl⟩ : syracuseStep 3128363 = 4692545) B4692545
theorem B3341459 : Blo 1389514 3341459 := bstep (se 1 (by rfl) ⟨2506094, by rfl⟩ : syracuseStep 3341459 = 5012189) B5012189
theorem B13360301 : Blo 1389514 13360301 := bstep (se 3 (by rfl) ⟨2505056, by rfl⟩ : syracuseStep 13360301 = 5010113) B5010113
theorem B3341497 : Blo 1389514 3341497 := bstep (se 2 (by rfl) ⟨1253061, by rfl⟩ : syracuseStep 3341497 = 2506123) B2506123
theorem B1563835 : Blo 1389514 1563835 := bstep (se 1 (by rfl) ⟨1172876, by rfl⟩ : syracuseStep 1563835 = 2345753) B2345753
theorem B4693193 : Blo 1389514 4693193 := bstep (se 2 (by rfl) ⟨1759947, by rfl⟩ : syracuseStep 4693193 = 3519895) B3519895
theorem B11304137 : Blo 1389514 11304137 := bstep (se 2 (by rfl) ⟨4239051, by rfl⟩ : syracuseStep 11304137 = 8478103) B8478103
theorem B1760555 : Blo 1389514 1760555 := bstep (se 1 (by rfl) ⟨1320416, by rfl⟩ : syracuseStep 1760555 = 2640833) B2640833
theorem B4455739 : Blo 1389514 4455739 := bstep (se 1 (by rfl) ⟨3341804, by rfl⟩ : syracuseStep 4455739 = 6683609) B6683609
theorem B33840443 : Blo 1389514 33840443 := bstep (se 1 (by rfl) ⟨25380332, by rfl⟩ : syracuseStep 33840443 = 50760665) B50760665
theorem B7036307 : Blo 1389514 7036307 := bstep (se 1 (by rfl) ⟨5277230, by rfl⟩ : syracuseStep 7036307 = 10554461) B10554461
theorem B3128723 : Blo 1389514 3128723 := bstep (se 1 (by rfl) ⟨2346542, by rfl⟩ : syracuseStep 3128723 = 4693085) B4693085
theorem B3128777 : Blo 1389514 3128777 := bstep (se 2 (by rfl) ⟨1173291, by rfl⟩ : syracuseStep 3128777 = 2346583) B2346583
theorem B18062797 : Blo 1389514 18062797 := bstep (se 3 (by rfl) ⟨3386774, by rfl⟩ : syracuseStep 18062797 = 6773549) B6773549
theorem B28548611 : Blo 1389514 28548611 := bstep (se 1 (by rfl) ⟨21411458, by rfl⟩ : syracuseStep 28548611 = 42822917) B42822917
theorem B3522163 : Blo 1389514 3522163 := bstep (se 1 (by rfl) ⟨2641622, by rfl⟩ : syracuseStep 3522163 = 5283245) B5283245
theorem B53419661 : Blo 1389514 53419661 := bstep (se 3 (by rfl) ⟨10016186, by rfl⟩ : syracuseStep 53419661 = 20032373) B20032373
theorem B1564303 : Blo 1389514 1564303 := bstep (se 1 (by rfl) ⟨1173227, by rfl⟩ : syracuseStep 1564303 = 2346455) B2346455
theorem B1761031 : Blo 1389514 1761031 := bstep (se 1 (by rfl) ⟨1320773, by rfl⟩ : syracuseStep 1761031 = 2641547) B2641547
theorem B4226845 : Blo 1389514 4226845 := bstep (se 3 (by rfl) ⟨792533, by rfl⟩ : syracuseStep 4226845 = 1585067) B1585067
theorem B3342113 : Blo 1389514 3342113 := bstep (se 2 (by rfl) ⟨1253292, by rfl⟩ : syracuseStep 3342113 = 2506585) B2506585
theorem B10559321 : Blo 1389514 10559321 := bstep (se 2 (by rfl) ⟨3959745, by rfl⟩ : syracuseStep 10559321 = 7919491) B7919491
theorem B4693895 : Blo 1389514 4693895 := bstep (se 1 (by rfl) ⟨3520421, by rfl⟩ : syracuseStep 4693895 = 7040843) B7040843
theorem B13369373 : Blo 1389514 13369373 := bstep (se 3 (by rfl) ⟨2506757, by rfl⟩ : syracuseStep 13369373 = 5013515) B5013515
theorem B2637947 : Blo 1389514 2637947 := bstep (se 1 (by rfl) ⟨1978460, by rfl⟩ : syracuseStep 2637947 = 3956921) B3956921
theorem B3129515 : Blo 1389514 3129515 := bstep (se 1 (by rfl) ⟨2347136, by rfl⟩ : syracuseStep 3129515 = 4694273) B4694273
theorem B1565023 : Blo 1389514 1565023 := bstep (se 1 (by rfl) ⟨1173767, by rfl⟩ : syracuseStep 1565023 = 2347535) B2347535
theorem B11436491 : Blo 1389514 11436491 := bstep (se 1 (by rfl) ⟨8577368, by rfl⟩ : syracuseStep 11436491 = 17154737) B17154737
theorem B5276123 : Blo 1389514 5276123 := bstep (se 1 (by rfl) ⟨3957092, by rfl⟩ : syracuseStep 5276123 = 7914185) B7914185
theorem B5349851 : Blo 1389514 5349851 := bstep (se 1 (by rfl) ⟨4012388, by rfl⟩ : syracuseStep 5349851 = 8024777) B8024777
theorem B15032891 : Blo 1389514 15032891 := bstep (se 1 (by rfl) ⟨11274668, by rfl⟩ : syracuseStep 15032891 = 22549337) B22549337
theorem B2638433 : Blo 1389514 2638433 := bstep (se 2 (by rfl) ⟨989412, by rfl⟩ : syracuseStep 2638433 = 1978825) B1978825
theorem B4694651 : Blo 1389514 4694651 := bstep (se 1 (by rfl) ⟨3520988, by rfl⟩ : syracuseStep 4694651 = 7041977) B7041977
theorem B4457099 : Blo 1389514 4457099 := bstep (se 1 (by rfl) ⟨3342824, by rfl⟩ : syracuseStep 4457099 = 6685649) B6685649
theorem B3130055 : Blo 1389514 3130055 := bstep (se 1 (by rfl) ⟨2347541, by rfl⟩ : syracuseStep 3130055 = 4695083) B4695083
theorem B1565383 : Blo 1389514 1565383 := bstep (se 1 (by rfl) ⟨1174037, by rfl⟩ : syracuseStep 1565383 = 2348075) B2348075
theorem B10019537 : Blo 1389514 10019537 := bstep (se 2 (by rfl) ⟨3757326, by rfl⟩ : syracuseStep 10019537 = 7514653) B7514653
theorem B2638585 : Blo 1389514 2638585 := bstep (se 2 (by rfl) ⟨989469, by rfl⟩ : syracuseStep 2638585 = 1978939) B1978939
theorem B4694813 : Blo 1389514 4694813 := bstep (se 3 (by rfl) ⟨880277, by rfl⟩ : syracuseStep 4694813 = 1760555) B1760555
theorem B5014381 : Blo 1389514 5014381 := bstep (se 3 (by rfl) ⟨940196, by rfl⟩ : syracuseStep 5014381 = 1880393) B1880393
theorem B2819195 : Blo 1389514 2819195 := bstep (se 1 (by rfl) ⟨2114396, by rfl⟩ : syracuseStep 2819195 = 4228793) B4228793
theorem B2377067 : Blo 1389514 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B6677903 : Blo 1389514 6677903 := bstep (se 1 (by rfl) ⟨5008427, by rfl⟩ : syracuseStep 6677903 = 10016855) B10016855
theorem B14263717 : Blo 1389514 14263717 := bstep (se 4 (by rfl) ⟨1337223, by rfl⟩ : syracuseStep 14263717 = 2674447) B2674447
theorem B8914349 : Blo 1389514 8914349 := bstep (se 3 (by rfl) ⟨1671440, by rfl⟩ : syracuseStep 8914349 = 3342881) B3342881
theorem B4695515 : Blo 1389514 4695515 := bstep (se 1 (by rfl) ⟨3521636, by rfl⟩ : syracuseStep 4695515 = 7043273) B7043273
theorem B5277383 : Blo 1389514 5277383 := bstep (se 1 (by rfl) ⟨3958037, by rfl⟩ : syracuseStep 5277383 = 7916075) B7916075
theorem B20309849 : Blo 1389514 20309849 := bstep (se 2 (by rfl) ⟨7616193, by rfl⟩ : syracuseStep 20309849 = 15232387) B15232387
theorem B2639891 : Blo 1389514 2639891 := bstep (se 1 (by rfl) ⟨1979918, by rfl⟩ : syracuseStep 2639891 = 3959837) B3959837
theorem B17827877 : Blo 1389514 17827877 := bstep (se 4 (by rfl) ⟨1671363, by rfl⟩ : syracuseStep 17827877 = 3342727) B3342727
theorem B2345017 : Blo 1389514 2345017 := bstep (se 2 (by rfl) ⟨879381, by rfl⟩ : syracuseStep 2345017 = 1758763) B1758763
theorem B8906867 : Blo 1389514 8906867 := bstep (se 1 (by rfl) ⟨6680150, by rfl⟩ : syracuseStep 8906867 = 13360301) B13360301
theorem B4696217 : Blo 1389514 4696217 := bstep (se 2 (by rfl) ⟨1761081, by rfl⟩ : syracuseStep 4696217 = 3522163) B3522163
theorem B2640043 : Blo 1389514 2640043 := bstep (se 1 (by rfl) ⟨1980032, by rfl⟩ : syracuseStep 2640043 = 3960065) B3960065
theorem B2345159 : Blo 1389514 2345159 := bstep (se 1 (by rfl) ⟨1758869, by rfl⟩ : syracuseStep 2345159 = 3517739) B3517739
theorem B19032407 : Blo 1389514 19032407 := bstep (se 1 (by rfl) ⟨14274305, by rfl⟩ : syracuseStep 19032407 = 28548611) B28548611
theorem B2345321 : Blo 1389514 2345321 := bstep (se 2 (by rfl) ⟨879495, by rfl⟩ : syracuseStep 2345321 = 1758991) B1758991
theorem B5278081 : Blo 1389514 5278081 := bstep (se 2 (by rfl) ⟨1979280, by rfl⟩ : syracuseStep 5278081 = 3958561) B3958561
theorem B2640271 : Blo 1389514 2640271 := bstep (se 1 (by rfl) ⟨1980203, by rfl⟩ : syracuseStep 2640271 = 3960407) B3960407
theorem B35613107 : Blo 1389514 35613107 := bstep (se 1 (by rfl) ⟨26709830, by rfl⟩ : syracuseStep 35613107 = 53419661) B53419661
theorem B2640347 : Blo 1389514 2640347 := bstep (se 1 (by rfl) ⟨1980260, by rfl⟩ : syracuseStep 2640347 = 3960521) B3960521
theorem B7039547 : Blo 1389514 7039547 := bstep (se 1 (by rfl) ⟨5279660, by rfl⟩ : syracuseStep 7039547 = 10559321) B10559321
theorem B5278355 : Blo 1389514 5278355 := bstep (se 1 (by rfl) ⟨3958766, by rfl⟩ : syracuseStep 5278355 = 7917533) B7917533
theorem B2345719 : Blo 1389514 2345719 := bstep (se 1 (by rfl) ⟨1759289, by rfl⟩ : syracuseStep 2345719 = 3518579) B3518579
theorem B7514909 : Blo 1389514 7514909 := bstep (se 3 (by rfl) ⟨1409045, by rfl⟩ : syracuseStep 7514909 = 2818091) B2818091
theorem B2411371 : Blo 1389514 2411371 := bstep (se 1 (by rfl) ⟨1808528, by rfl⟩ : syracuseStep 2411371 = 3617057) B3617057
theorem B5712815 : Blo 1389514 5712815 := bstep (se 1 (by rfl) ⟨4284611, by rfl⟩ : syracuseStep 5712815 = 8569223) B8569223
theorem B2345915 : Blo 1389514 2345915 := bstep (se 1 (by rfl) ⟨1759436, by rfl⟩ : syracuseStep 2345915 = 3518873) B3518873
theorem B2346023 : Blo 1389514 2346023 := bstep (se 1 (by rfl) ⟨1759517, by rfl⟩ : syracuseStep 2346023 = 3519035) B3519035
theorem B5008499 : Blo 1389514 5008499 := bstep (se 1 (by rfl) ⟨3756374, by rfl⟩ : syracuseStep 5008499 = 7512749) B7512749
theorem B5008555 : Blo 1389514 5008555 := bstep (se 1 (by rfl) ⟨3756416, by rfl⟩ : syracuseStep 5008555 = 7512833) B7512833
theorem B7040195 : Blo 1389514 7040195 := bstep (se 1 (by rfl) ⟨5280146, by rfl⟩ : syracuseStep 7040195 = 10560293) B10560293
theorem B2346313 : Blo 1389514 2346313 := bstep (se 2 (by rfl) ⟨879867, by rfl⟩ : syracuseStep 2346313 = 1759735) B1759735
theorem B2346347 : Blo 1389514 2346347 := bstep (se 1 (by rfl) ⟨1759760, by rfl⟩ : syracuseStep 2346347 = 3519521) B3519521
theorem B2674063 : Blo 1389514 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B2084279 : Blo 1389514 2084279 := bstep (se 1 (by rfl) ⟨1563209, by rfl⟩ : syracuseStep 2084279 = 3126419) B3126419
theorem B2084315 : Blo 1389514 2084315 := bstep (se 1 (by rfl) ⟨1563236, by rfl⟩ : syracuseStep 2084315 = 3126473) B3126473
theorem B5942747 : Blo 1389514 5942747 := bstep (se 1 (by rfl) ⟨4457060, by rfl⟩ : syracuseStep 5942747 = 8914121) B8914121
theorem B5639719 : Blo 1389514 5639719 := bstep (se 1 (by rfl) ⟨4229789, by rfl⟩ : syracuseStep 5639719 = 8459579) B8459579
theorem B8457949 : Blo 1389514 8457949 := bstep (se 3 (by rfl) ⟨1585865, by rfl⟩ : syracuseStep 8457949 = 3171731) B3171731
theorem B2346745 : Blo 1389514 2346745 := bstep (se 2 (by rfl) ⟨880029, by rfl⟩ : syracuseStep 2346745 = 1760059) B1760059
theorem B4689737 : Blo 1389514 4689737 := bstep (se 2 (by rfl) ⟨1758651, by rfl⟩ : syracuseStep 4689737 = 3517303) B3517303
theorem B2084783 : Blo 1389514 2084783 := bstep (se 1 (by rfl) ⟨1563587, by rfl⟩ : syracuseStep 2084783 = 3127175) B3127175
theorem B13373369 : Blo 1389514 13373369 := bstep (se 2 (by rfl) ⟨5015013, by rfl⟩ : syracuseStep 13373369 = 10030027) B10030027
theorem B2347015 : Blo 1389514 2347015 := bstep (se 1 (by rfl) ⟨1760261, by rfl⟩ : syracuseStep 2347015 = 3520523) B3520523
theorem B3960839 : Blo 1389514 3960839 := bstep (se 1 (by rfl) ⟨2970629, by rfl⟩ : syracuseStep 3960839 = 5941259) B5941259
theorem B2084873 : Blo 1389514 2084873 := bstep (se 2 (by rfl) ⟨781827, by rfl⟩ : syracuseStep 2084873 = 1563655) B1563655
theorem B2084903 : Blo 1389514 2084903 := bstep (se 1 (by rfl) ⟨1563677, by rfl⟩ : syracuseStep 2084903 = 3127355) B3127355
theorem B2084987 : Blo 1389514 2084987 := bstep (se 1 (by rfl) ⟨1563740, by rfl⟩ : syracuseStep 2084987 = 3127481) B3127481
theorem B3756203 : Blo 1389514 3756203 := bstep (se 1 (by rfl) ⟨2817152, by rfl⟩ : syracuseStep 3756203 = 5634305) B5634305
theorem B1880263 : Blo 1389514 1880263 := bstep (se 1 (by rfl) ⟨1410197, by rfl⟩ : syracuseStep 1880263 = 2820395) B2820395
theorem B3518711 : Blo 1389514 3518711 := bstep (se 1 (by rfl) ⟨2639033, by rfl⟩ : syracuseStep 3518711 = 5278067) B5278067
theorem B2085113 : Blo 1389514 2085113 := bstep (se 2 (by rfl) ⟨781917, by rfl⟩ : syracuseStep 2085113 = 1563835) B1563835
theorem B5280011 : Blo 1389514 5280011 := bstep (se 1 (by rfl) ⟨3960008, by rfl⟩ : syracuseStep 5280011 = 7920017) B7920017
theorem B2085215 : Blo 1389514 2085215 := bstep (se 1 (by rfl) ⟨1563911, by rfl⟩ : syracuseStep 2085215 = 3127823) B3127823
theorem B2085227 : Blo 1389514 2085227 := bstep (se 1 (by rfl) ⟨1563920, by rfl⟩ : syracuseStep 2085227 = 3127841) B3127841
theorem B4518287 : Blo 1389514 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B2347447 : Blo 1389514 2347447 := bstep (se 1 (by rfl) ⟨1760585, by rfl⟩ : syracuseStep 2347447 = 3521171) B3521171
theorem B2085455 : Blo 1389514 2085455 := bstep (se 1 (by rfl) ⟨1564091, by rfl⟩ : syracuseStep 2085455 = 3128183) B3128183
theorem B2347643 : Blo 1389514 2347643 := bstep (se 1 (by rfl) ⟨1760732, by rfl⟩ : syracuseStep 2347643 = 3521465) B3521465
theorem B3912391 : Blo 1389514 3912391 := bstep (se 1 (by rfl) ⟨2934293, by rfl⟩ : syracuseStep 3912391 = 5868587) B5868587
theorem B2085575 : Blo 1389514 2085575 := bstep (se 1 (by rfl) ⟨1564181, by rfl⟩ : syracuseStep 2085575 = 3128363) B3128363
theorem B2085737 : Blo 1389514 2085737 := bstep (se 2 (by rfl) ⟨782151, by rfl⟩ : syracuseStep 2085737 = 1564303) B1564303
theorem B3339191 : Blo 1389514 3339191 := bstep (se 1 (by rfl) ⟨2504393, by rfl⟩ : syracuseStep 3339191 = 5008787) B5008787
theorem B4690871 : Blo 1389514 4690871 := bstep (se 1 (by rfl) ⟨3518153, by rfl⟩ : syracuseStep 4690871 = 7036307) B7036307
theorem B2085815 : Blo 1389514 2085815 := bstep (se 1 (by rfl) ⟨1564361, by rfl⟩ : syracuseStep 2085815 = 3128723) B3128723
theorem B1389531 : Blo 1389514 1389531 := bstep (se 1 (by rfl) ⟨1042148, by rfl⟩ : syracuseStep 1389531 = 2084297) B2084297
theorem B2085851 : Blo 1389514 2085851 := bstep (se 1 (by rfl) ⟨1564388, by rfl⟩ : syracuseStep 2085851 = 3128777) B3128777
theorem B2348041 : Blo 1389514 2348041 := bstep (se 2 (by rfl) ⟨880515, by rfl⟩ : syracuseStep 2348041 = 1761031) B1761031
theorem B1389607 : Blo 1389514 1389607 := bstep (se 1 (by rfl) ⟨1042205, by rfl⟩ : syracuseStep 1389607 = 2084411) B2084411
theorem B1389647 : Blo 1389514 1389647 := bstep (se 1 (by rfl) ⟨1042235, by rfl⟩ : syracuseStep 1389647 = 2084471) B2084471
theorem B1389663 : Blo 1389514 1389663 := bstep (se 1 (by rfl) ⟨1042247, by rfl⟩ : syracuseStep 1389663 = 2084495) B2084495
theorem B1389691 : Blo 1389514 1389691 := bstep (se 1 (by rfl) ⟨1042268, by rfl⟩ : syracuseStep 1389691 = 2084537) B2084537
theorem B1389743 : Blo 1389514 1389743 := bstep (se 1 (by rfl) ⟨1042307, by rfl⟩ : syracuseStep 1389743 = 2084615) B2084615
theorem B1389767 : Blo 1389514 1389767 := bstep (se 1 (by rfl) ⟨1042325, by rfl⟩ : syracuseStep 1389767 = 2084651) B2084651
theorem B1389787 : Blo 1389514 1389787 := bstep (se 1 (by rfl) ⟨1042340, by rfl⟩ : syracuseStep 1389787 = 2084681) B2084681
theorem B1389863 : Blo 1389514 1389863 := bstep (se 1 (by rfl) ⟨1042397, by rfl⟩ : syracuseStep 1389863 = 2084795) B2084795
theorem B1389903 : Blo 1389514 1389903 := bstep (se 1 (by rfl) ⟨1042427, by rfl⟩ : syracuseStep 1389903 = 2084855) B2084855
theorem B1389919 : Blo 1389514 1389919 := bstep (se 1 (by rfl) ⟨1042439, by rfl⟩ : syracuseStep 1389919 = 2084879) B2084879
theorem B4068713 : Blo 1389514 4068713 := bstep (se 2 (by rfl) ⟨1525767, by rfl⟩ : syracuseStep 4068713 = 3051535) B3051535
theorem B1389947 : Blo 1389514 1389947 := bstep (se 1 (by rfl) ⟨1042460, by rfl⟩ : syracuseStep 1389947 = 2084921) B2084921
theorem B3126671 : Blo 1389514 3126671 := bstep (se 1 (by rfl) ⟨2345003, by rfl⟩ : syracuseStep 3126671 = 4690007) B4690007
theorem B7918991 : Blo 1389514 7918991 := bstep (se 1 (by rfl) ⟨5939243, by rfl⟩ : syracuseStep 7918991 = 11878487) B11878487
theorem B1389999 : Blo 1389514 1389999 := bstep (se 1 (by rfl) ⟨1042499, by rfl⟩ : syracuseStep 1389999 = 2084999) B2084999
theorem B2086319 : Blo 1389514 2086319 := bstep (se 1 (by rfl) ⟨1564739, by rfl⟩ : syracuseStep 2086319 = 3129479) B3129479
theorem B1390023 : Blo 1389514 1390023 := bstep (se 1 (by rfl) ⟨1042517, by rfl⟩ : syracuseStep 1390023 = 2085035) B2085035
theorem B1390043 : Blo 1389514 1390043 := bstep (se 1 (by rfl) ⟨1042532, by rfl⟩ : syracuseStep 1390043 = 2085065) B2085065
theorem B10556891 : Blo 1389514 10556891 := bstep (se 1 (by rfl) ⟨7917668, by rfl⟩ : syracuseStep 10556891 = 15835337) B15835337
theorem B162625013 : Blo 1389514 162625013 := bstep (se 5 (by rfl) ⟨7623047, by rfl⟩ : syracuseStep 162625013 = 15246095) B15246095
theorem B4691465 : Blo 1389514 4691465 := bstep (se 2 (by rfl) ⟨1759299, by rfl⟩ : syracuseStep 4691465 = 3518599) B3518599
theorem B2086409 : Blo 1389514 2086409 := bstep (se 2 (by rfl) ⟨782403, by rfl⟩ : syracuseStep 2086409 = 1564807) B1564807
theorem B1390119 : Blo 1389514 1390119 := bstep (se 1 (by rfl) ⟨1042589, by rfl⟩ : syracuseStep 1390119 = 2085179) B2085179
theorem B2086439 : Blo 1389514 2086439 := bstep (se 1 (by rfl) ⟨1564829, by rfl⟩ : syracuseStep 2086439 = 3129659) B3129659
theorem B1390159 : Blo 1389514 1390159 := bstep (se 1 (by rfl) ⟨1042619, by rfl⟩ : syracuseStep 1390159 = 2085239) B2085239
theorem B1390175 : Blo 1389514 1390175 := bstep (se 1 (by rfl) ⟨1042631, by rfl⟩ : syracuseStep 1390175 = 2085263) B2085263
theorem B1390203 : Blo 1389514 1390203 := bstep (se 1 (by rfl) ⟨1042652, by rfl⟩ : syracuseStep 1390203 = 2085305) B2085305
theorem B2086523 : Blo 1389514 2086523 := bstep (se 1 (by rfl) ⟨1564892, by rfl⟩ : syracuseStep 2086523 = 3129785) B3129785
theorem B4454023 : Blo 1389514 4454023 := bstep (se 1 (by rfl) ⟨3340517, by rfl⟩ : syracuseStep 4454023 = 6681035) B6681035
theorem B1390255 : Blo 1389514 1390255 := bstep (se 1 (by rfl) ⟨1042691, by rfl⟩ : syracuseStep 1390255 = 2085383) B2085383
theorem B5281469 : Blo 1389514 5281469 := bstep (se 3 (by rfl) ⟨990275, by rfl⟩ : syracuseStep 5281469 = 1980551) B1980551
theorem B1390279 : Blo 1389514 1390279 := bstep (se 1 (by rfl) ⟨1042709, by rfl⟩ : syracuseStep 1390279 = 2085419) B2085419
theorem B3520199 : Blo 1389514 3520199 := bstep (se 1 (by rfl) ⟨2640149, by rfl⟩ : syracuseStep 3520199 = 5280299) B5280299
theorem B3126995 : Blo 1389514 3126995 := bstep (se 1 (by rfl) ⟨2345246, by rfl⟩ : syracuseStep 3126995 = 4690493) B4690493
theorem B1390299 : Blo 1389514 1390299 := bstep (se 1 (by rfl) ⟨1042724, by rfl⟩ : syracuseStep 1390299 = 2085449) B2085449
theorem B8910557 : Blo 1389514 8910557 := bstep (se 3 (by rfl) ⟨1670729, by rfl⟩ : syracuseStep 8910557 = 3341459) B3341459
theorem B2086649 : Blo 1389514 2086649 := bstep (se 2 (by rfl) ⟨782493, by rfl⟩ : syracuseStep 2086649 = 1564987) B1564987
theorem B1390375 : Blo 1389514 1390375 := bstep (se 1 (by rfl) ⟨1042781, by rfl⟩ : syracuseStep 1390375 = 2085563) B2085563
theorem B30463787 : Blo 1389514 30463787 := bstep (se 1 (by rfl) ⟨22847840, by rfl⟩ : syracuseStep 30463787 = 45695681) B45695681
theorem B24082219 : Blo 1389514 24082219 := bstep (se 1 (by rfl) ⟨18061664, by rfl⟩ : syracuseStep 24082219 = 36123329) B36123329
theorem B5011267 : Blo 1389514 5011267 := bstep (se 1 (by rfl) ⟨3758450, by rfl⟩ : syracuseStep 5011267 = 7516901) B7516901
theorem B1390415 : Blo 1389514 1390415 := bstep (se 1 (by rfl) ⟨1042811, by rfl⟩ : syracuseStep 1390415 = 2085623) B2085623
theorem B19019609 : Blo 1389514 19019609 := bstep (se 2 (by rfl) ⟨7132353, by rfl⟩ : syracuseStep 19019609 = 14264707) B14264707
theorem B1390431 : Blo 1389514 1390431 := bstep (se 1 (by rfl) ⟨1042823, by rfl⟩ : syracuseStep 1390431 = 2085647) B2085647
theorem B2086751 : Blo 1389514 2086751 := bstep (se 1 (by rfl) ⟨1565063, by rfl⟩ : syracuseStep 2086751 = 3130127) B3130127
theorem B2086763 : Blo 1389514 2086763 := bstep (se 1 (by rfl) ⟨1565072, by rfl⟩ : syracuseStep 2086763 = 3130145) B3130145
theorem B1390459 : Blo 1389514 1390459 := bstep (se 1 (by rfl) ⟨1042844, by rfl⟩ : syracuseStep 1390459 = 2085689) B2085689
theorem B20051873 : Blo 1389514 20051873 := bstep (se 2 (by rfl) ⟨7519452, by rfl⟩ : syracuseStep 20051873 = 15038905) B15038905
theorem B1390511 : Blo 1389514 1390511 := bstep (se 1 (by rfl) ⟨1042883, by rfl⟩ : syracuseStep 1390511 = 2085767) B2085767
theorem B2971579 : Blo 1389514 2971579 := bstep (se 1 (by rfl) ⟨2228684, by rfl⟩ : syracuseStep 2971579 = 4457369) B4457369
theorem B10557377 : Blo 1389514 10557377 := bstep (se 2 (by rfl) ⟨3959016, by rfl⟩ : syracuseStep 10557377 = 7918033) B7918033
theorem B1390535 : Blo 1389514 1390535 := bstep (se 1 (by rfl) ⟨1042901, by rfl⟩ : syracuseStep 1390535 = 2085803) B2085803
theorem B1390555 : Blo 1389514 1390555 := bstep (se 1 (by rfl) ⟨1042916, by rfl⟩ : syracuseStep 1390555 = 2085833) B2085833
theorem B10565639 : Blo 1389514 10565639 := bstep (se 1 (by rfl) ⟨7924229, by rfl⟩ : syracuseStep 10565639 = 15848459) B15848459
theorem B2971655 : Blo 1389514 2971655 := bstep (se 1 (by rfl) ⟨2228741, by rfl⟩ : syracuseStep 2971655 = 4457483) B4457483
theorem B8452133 : Blo 1389514 8452133 := bstep (se 4 (by rfl) ⟨792387, by rfl⟩ : syracuseStep 8452133 = 1584775) B1584775
theorem B1390631 : Blo 1389514 1390631 := bstep (se 1 (by rfl) ⟨1042973, by rfl⟩ : syracuseStep 1390631 = 2085947) B2085947
theorem B1390671 : Blo 1389514 1390671 := bstep (se 1 (by rfl) ⟨1043003, by rfl⟩ : syracuseStep 1390671 = 2086007) B2086007
theorem B2086991 : Blo 1389514 2086991 := bstep (se 1 (by rfl) ⟨1565243, by rfl⟩ : syracuseStep 2086991 = 3130487) B3130487
theorem B1390687 : Blo 1389514 1390687 := bstep (se 1 (by rfl) ⟨1043015, by rfl⟩ : syracuseStep 1390687 = 2086031) B2086031
theorem B1390715 : Blo 1389514 1390715 := bstep (se 1 (by rfl) ⟨1043036, by rfl⟩ : syracuseStep 1390715 = 2086073) B2086073
theorem B1390767 : Blo 1389514 1390767 := bstep (se 1 (by rfl) ⟨1043075, by rfl⟩ : syracuseStep 1390767 = 2086151) B2086151
theorem B1390791 : Blo 1389514 1390791 := bstep (se 1 (by rfl) ⟨1043093, by rfl⟩ : syracuseStep 1390791 = 2086187) B2086187
theorem B2087111 : Blo 1389514 2087111 := bstep (se 1 (by rfl) ⟨1565333, by rfl⟩ : syracuseStep 2087111 = 3130667) B3130667
theorem B1390811 : Blo 1389514 1390811 := bstep (se 1 (by rfl) ⟨1043108, by rfl⟩ : syracuseStep 1390811 = 2086217) B2086217
theorem B11278565 : Blo 1389514 11278565 := bstep (se 4 (by rfl) ⟨1057365, by rfl⟩ : syracuseStep 11278565 = 2114731) B2114731
theorem B1390887 : Blo 1389514 1390887 := bstep (se 1 (by rfl) ⟨1043165, by rfl⟩ : syracuseStep 1390887 = 2086331) B2086331
theorem B1390927 : Blo 1389514 1390927 := bstep (se 1 (by rfl) ⟨1043195, by rfl⟩ : syracuseStep 1390927 = 2086391) B2086391
theorem B1759583 : Blo 1389514 1759583 := bstep (se 1 (by rfl) ⟨1319687, by rfl⟩ : syracuseStep 1759583 = 2639375) B2639375
theorem B1390943 : Blo 1389514 1390943 := bstep (se 1 (by rfl) ⟨1043207, by rfl⟩ : syracuseStep 1390943 = 2086415) B2086415
theorem B4692329 : Blo 1389514 4692329 := bstep (se 2 (by rfl) ⟨1759623, by rfl⟩ : syracuseStep 4692329 = 3519247) B3519247
theorem B1390971 : Blo 1389514 1390971 := bstep (se 1 (by rfl) ⟨1043228, by rfl⟩ : syracuseStep 1390971 = 2086457) B2086457
theorem B1391023 : Blo 1389514 1391023 := bstep (se 1 (by rfl) ⟨1043267, by rfl⟩ : syracuseStep 1391023 = 2086535) B2086535
theorem B1391047 : Blo 1389514 1391047 := bstep (se 1 (by rfl) ⟨1043285, by rfl⟩ : syracuseStep 1391047 = 2086571) B2086571
theorem B1391067 : Blo 1389514 1391067 := bstep (se 1 (by rfl) ⟨1043300, by rfl⟩ : syracuseStep 1391067 = 2086601) B2086601
theorem B10566125 : Blo 1389514 10566125 := bstep (se 3 (by rfl) ⟨1981148, by rfl⟩ : syracuseStep 10566125 = 3962297) B3962297
theorem B1391143 : Blo 1389514 1391143 := bstep (se 1 (by rfl) ⟨1043357, by rfl⟩ : syracuseStep 1391143 = 2086715) B2086715
theorem B1391183 : Blo 1389514 1391183 := bstep (se 1 (by rfl) ⟨1043387, by rfl⟩ : syracuseStep 1391183 = 2086775) B2086775
theorem B1391199 : Blo 1389514 1391199 := bstep (se 1 (by rfl) ⟨1043399, by rfl⟩ : syracuseStep 1391199 = 2086799) B2086799
theorem B1563259 : Blo 1389514 1563259 := bstep (se 1 (by rfl) ⟨1172444, by rfl⟩ : syracuseStep 1563259 = 2344889) B2344889
theorem B3127931 : Blo 1389514 3127931 := bstep (se 1 (by rfl) ⟨2345948, by rfl⟩ : syracuseStep 3127931 = 4691897) B4691897
theorem B1391227 : Blo 1389514 1391227 := bstep (se 1 (by rfl) ⟨1043420, by rfl⟩ : syracuseStep 1391227 = 2086841) B2086841
theorem B1391279 : Blo 1389514 1391279 := bstep (se 1 (by rfl) ⟨1043459, by rfl⟩ : syracuseStep 1391279 = 2086919) B2086919
theorem B30497465 : Blo 1389514 30497465 := bstep (se 2 (by rfl) ⟨11436549, by rfl⟩ : syracuseStep 30497465 = 22873099) B22873099
theorem B1391303 : Blo 1389514 1391303 := bstep (se 1 (by rfl) ⟨1043477, by rfl⟩ : syracuseStep 1391303 = 2086955) B2086955
theorem B1391323 : Blo 1389514 1391323 := bstep (se 1 (by rfl) ⟨1043492, by rfl⟩ : syracuseStep 1391323 = 2086985) B2086985
theorem B3128057 : Blo 1389514 3128057 := bstep (se 2 (by rfl) ⟨1173021, by rfl⟩ : syracuseStep 3128057 = 2346043) B2346043
theorem B1391399 : Blo 1389514 1391399 := bstep (se 1 (by rfl) ⟨1043549, by rfl⟩ : syracuseStep 1391399 = 2087099) B2087099
theorem B3521353 : Blo 1389514 3521353 := bstep (se 2 (by rfl) ⟨1320507, by rfl⟩ : syracuseStep 3521353 = 2641015) B2641015
theorem B17816395 : Blo 1389514 17816395 := bstep (se 1 (by rfl) ⟨13362296, by rfl⟩ : syracuseStep 17816395 = 26724593) B26724593
theorem B1391439 : Blo 1389514 1391439 := bstep (se 1 (by rfl) ⟨1043579, by rfl⟩ : syracuseStep 1391439 = 2087159) B2087159
theorem B1391455 : Blo 1389514 1391455 := bstep (se 1 (by rfl) ⟨1043591, by rfl⟩ : syracuseStep 1391455 = 2087183) B2087183
theorem B1391483 : Blo 1389514 1391483 := bstep (se 1 (by rfl) ⟨1043612, by rfl⟩ : syracuseStep 1391483 = 2087225) B2087225
theorem B4455329 : Blo 1389514 4455329 := bstep (se 2 (by rfl) ⟨1670748, by rfl⟩ : syracuseStep 4455329 = 3341497) B3341497
theorem B4692923 : Blo 1389514 4692923 := bstep (se 1 (by rfl) ⟨3519692, by rfl⟩ : syracuseStep 4692923 = 7039385) B7039385
theorem B23763941 : Blo 1389514 23763941 := bstep (se 4 (by rfl) ⟨2227869, by rfl⟩ : syracuseStep 23763941 = 4455739) B4455739
theorem B3128327 : Blo 1389514 3128327 := bstep (se 1 (by rfl) ⟨2346245, by rfl⟩ : syracuseStep 3128327 = 4692491) B4692491
theorem B7035983 : Blo 1389514 7035983 := bstep (se 1 (by rfl) ⟨5276987, by rfl⟩ : syracuseStep 7035983 = 10553975) B10553975
theorem B1563727 : Blo 1389514 1563727 := bstep (se 1 (by rfl) ⟨1172795, by rfl⟩ : syracuseStep 1563727 = 2345591) B2345591
theorem B3128399 : Blo 1389514 3128399 := bstep (se 1 (by rfl) ⟨2346299, by rfl⟩ : syracuseStep 3128399 = 4692599) B4692599
theorem B24083729 : Blo 1389514 24083729 := bstep (se 2 (by rfl) ⟨9031398, by rfl⟩ : syracuseStep 24083729 = 18062797) B18062797
theorem B10558835 : Blo 1389514 10558835 := bstep (se 1 (by rfl) ⟨7919126, by rfl⟩ : syracuseStep 10558835 = 15838253) B15838253
theorem B5283215 : Blo 1389514 5283215 := bstep (se 1 (by rfl) ⟨3962411, by rfl⟩ : syracuseStep 5283215 = 7924823) B7924823
theorem B1564123 : Blo 1389514 1564123 := bstep (se 1 (by rfl) ⟨1173092, by rfl⟩ : syracuseStep 1564123 = 2346185) B2346185
theorem B3128795 : Blo 1389514 3128795 := bstep (se 1 (by rfl) ⟨2346596, by rfl⟩ : syracuseStep 3128795 = 4693193) B4693193
theorem B7536091 : Blo 1389514 7536091 := bstep (se 1 (by rfl) ⟨5652068, by rfl⟩ : syracuseStep 7536091 = 11304137) B11304137
theorem B22560295 : Blo 1389514 22560295 := bstep (se 1 (by rfl) ⟨16920221, by rfl⟩ : syracuseStep 22560295 = 33840443) B33840443
theorem B2506297 : Blo 1389514 2506297 := bstep (se 2 (by rfl) ⟨939861, by rfl⟩ : syracuseStep 2506297 = 1879723) B1879723
theorem B11427473 : Blo 1389514 11427473 := bstep (se 2 (by rfl) ⟨4285302, by rfl⟩ : syracuseStep 11427473 = 8570605) B8570605
theorem B5635793 : Blo 1389514 5635793 := bstep (se 2 (by rfl) ⟨2113422, by rfl⟩ : syracuseStep 5635793 = 4226845) B4226845
theorem B7036631 : Blo 1389514 7036631 := bstep (se 1 (by rfl) ⟨5277473, by rfl⟩ : syracuseStep 7036631 = 10554947) B10554947
theorem B7921475 : Blo 1389514 7921475 := bstep (se 1 (by rfl) ⟨5941106, by rfl⟩ : syracuseStep 7921475 = 11882213) B11882213
theorem B4759391 : Blo 1389514 4759391 := bstep (se 1 (by rfl) ⟨3569543, by rfl⟩ : syracuseStep 4759391 = 7139087) B7139087
theorem B2228075 : Blo 1389514 2228075 := bstep (se 1 (by rfl) ⟨1671056, by rfl⟩ : syracuseStep 2228075 = 3342113) B3342113
theorem B1564591 : Blo 1389514 1564591 := bstep (se 1 (by rfl) ⟨1173443, by rfl⟩ : syracuseStep 1564591 = 2346887) B2346887
theorem B3129263 : Blo 1389514 3129263 := bstep (se 1 (by rfl) ⟨2346947, by rfl⟩ : syracuseStep 3129263 = 4693895) B4693895
theorem B3129353 : Blo 1389514 3129353 := bstep (se 2 (by rfl) ⟨1173507, by rfl⟩ : syracuseStep 3129353 = 2347015) B2347015
theorem B8912915 : Blo 1389514 8912915 := bstep (se 1 (by rfl) ⟨6684686, by rfl⟩ : syracuseStep 8912915 = 13369373) B13369373
theorem B3129767 : Blo 1389514 3129767 := bstep (se 1 (by rfl) ⟨2347325, by rfl⟩ : syracuseStep 3129767 = 4694651) B4694651
theorem B1565095 : Blo 1389514 1565095 := bstep (se 1 (by rfl) ⟨1173821, by rfl⟩ : syracuseStep 1565095 = 2347643) B2347643
theorem B7037441 : Blo 1389514 7037441 := bstep (se 2 (by rfl) ⟨2639040, by rfl⟩ : syracuseStep 7037441 = 5278081) B5278081
theorem B3129875 : Blo 1389514 3129875 := bstep (se 1 (by rfl) ⟨2347406, by rfl⟩ : syracuseStep 3129875 = 4694813) B4694813
theorem B3129929 : Blo 1389514 3129929 := bstep (se 2 (by rfl) ⟨1173723, by rfl⟩ : syracuseStep 3129929 = 2347447) B2347447
theorem B2712475 : Blo 1389514 2712475 := bstep (se 1 (by rfl) ⟨2034356, by rfl⟩ : syracuseStep 2712475 = 4068713) B4068713
theorem B7037927 : Blo 1389514 7037927 := bstep (se 1 (by rfl) ⟨5278445, by rfl⟩ : syracuseStep 7037927 = 10556891) B10556891
theorem B3130343 : Blo 1389514 3130343 := bstep (se 1 (by rfl) ⟨2347757, by rfl⟩ : syracuseStep 3130343 = 4695515) B4695515
theorem B20866085 : Blo 1389514 20866085 := bstep (se 4 (by rfl) ⟨1956195, by rfl⟩ : syracuseStep 20866085 = 3912391) B3912391
theorem B10028069 : Blo 1389514 10028069 := bstep (se 4 (by rfl) ⟨940131, by rfl⟩ : syracuseStep 10028069 = 1880263) B1880263
theorem B4695137 : Blo 1389514 4695137 := bstep (se 2 (by rfl) ⟨1760676, by rfl⟩ : syracuseStep 4695137 = 3521353) B3521353
theorem B6685841 : Blo 1389514 6685841 := bstep (se 2 (by rfl) ⟨2507190, by rfl⟩ : syracuseStep 6685841 = 5014381) B5014381
theorem B5940371 : Blo 1389514 5940371 := bstep (se 1 (by rfl) ⟨4455278, by rfl⟩ : syracuseStep 5940371 = 8910557) B8910557
theorem B7038251 : Blo 1389514 7038251 := bstep (se 1 (by rfl) ⟨5278688, by rfl⟩ : syracuseStep 7038251 = 10557377) B10557377
theorem B3130721 : Blo 1389514 3130721 := bstep (se 2 (by rfl) ⟨1174020, by rfl⟩ : syracuseStep 3130721 = 2348041) B2348041
theorem B3130811 : Blo 1389514 3130811 := bstep (se 1 (by rfl) ⟨2348108, by rfl⟩ : syracuseStep 3130811 = 4696217) B4696217
theorem B6678073 : Blo 1389514 6678073 := bstep (se 2 (by rfl) ⟨2504277, by rfl⟩ : syracuseStep 6678073 = 5008555) B5008555
theorem B23742071 : Blo 1389514 23742071 := bstep (se 1 (by rfl) ⟨17806553, by rfl⟩ : syracuseStep 23742071 = 35613107) B35613107
theorem B3565417 : Blo 1389514 3565417 := bstep (se 2 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 3565417 = 2674063) B2674063
theorem B7039223 : Blo 1389514 7039223 := bstep (se 1 (by rfl) ⟨5279417, by rfl⟩ : syracuseStep 7039223 = 10558835) B10558835
theorem B11880877 : Blo 1389514 11880877 := bstep (se 3 (by rfl) ⟨2227664, by rfl⟩ : syracuseStep 11880877 = 4455329) B4455329
theorem B3172927 : Blo 1389514 3172927 := bstep (se 1 (by rfl) ⟨2379695, by rfl⟩ : syracuseStep 3172927 = 4759391) B4759391
theorem B1485383 : Blo 1389514 1485383 := bstep (se 1 (by rfl) ⟨1114037, by rfl⟩ : syracuseStep 1485383 = 2228075) B2228075
theorem B8915579 : Blo 1389514 8915579 := bstep (se 1 (by rfl) ⟨6686684, by rfl⟩ : syracuseStep 8915579 = 13373369) B13373369
theorem B10562237 : Blo 1389514 10562237 := bstep (se 3 (by rfl) ⟨1980419, by rfl⟩ : syracuseStep 10562237 = 3960839) B3960839
theorem B7039709 : Blo 1389514 7039709 := bstep (se 3 (by rfl) ⟨1319945, by rfl⟩ : syracuseStep 7039709 = 2639891) B2639891
theorem B2345807 : Blo 1389514 2345807 := bstep (se 1 (by rfl) ⟨1759355, by rfl⟩ : syracuseStep 2345807 = 3518711) B3518711
theorem B3517415 : Blo 1389514 3517415 := bstep (se 1 (by rfl) ⟨2638061, by rfl⟩ : syracuseStep 3517415 = 5276123) B5276123
theorem B3566567 : Blo 1389514 3566567 := bstep (se 1 (by rfl) ⟨2674925, by rfl⟩ : syracuseStep 3566567 = 5349851) B5349851
theorem B6679691 : Blo 1389514 6679691 := bstep (se 1 (by rfl) ⟨5009768, by rfl⟩ : syracuseStep 6679691 = 10019537) B10019537
theorem B1879463 : Blo 1389514 1879463 := bstep (se 1 (by rfl) ⟨1409597, by rfl⟩ : syracuseStep 1879463 = 2819195) B2819195
theorem B2084345 : Blo 1389514 2084345 := bstep (se 2 (by rfl) ⟨781629, by rfl⟩ : syracuseStep 2084345 = 1563259) B1563259
theorem B2084447 : Blo 1389514 2084447 := bstep (se 1 (by rfl) ⟨1563335, by rfl⟩ : syracuseStep 2084447 = 3126671) B3126671
theorem B4451935 : Blo 1389514 4451935 := bstep (se 1 (by rfl) ⟨3338951, by rfl⟩ : syracuseStep 4451935 = 6677903) B6677903
theorem B5279327 : Blo 1389514 5279327 := bstep (se 1 (by rfl) ⟨3959495, by rfl⟩ : syracuseStep 5279327 = 7918991) B7918991
theorem B5942899 : Blo 1389514 5942899 := bstep (se 1 (by rfl) ⟨4457174, by rfl⟩ : syracuseStep 5942899 = 8914349) B8914349
theorem B3518113 : Blo 1389514 3518113 := bstep (se 2 (by rfl) ⟨1319292, by rfl⟩ : syracuseStep 3518113 = 2638585) B2638585
theorem B108416675 : Blo 1389514 108416675 := bstep (se 1 (by rfl) ⟨81312506, by rfl⟩ : syracuseStep 108416675 = 162625013) B162625013
theorem B3518255 : Blo 1389514 3518255 := bstep (se 1 (by rfl) ⟨2638691, by rfl⟩ : syracuseStep 3518255 = 5277383) B5277383
theorem B2346799 : Blo 1389514 2346799 := bstep (se 1 (by rfl) ⟨1760099, by rfl⟩ : syracuseStep 2346799 = 3520199) B3520199
theorem B2084663 : Blo 1389514 2084663 := bstep (se 1 (by rfl) ⟨1563497, by rfl⟩ : syracuseStep 2084663 = 3126995) B3126995
theorem B3215161 : Blo 1389514 3215161 := bstep (se 2 (by rfl) ⟨1205685, by rfl⟩ : syracuseStep 3215161 = 2411371) B2411371
theorem B45109061 : Blo 1389514 45109061 := bstep (se 4 (by rfl) ⟨4228974, by rfl⟩ : syracuseStep 45109061 = 8457949) B8457949
theorem B2084969 : Blo 1389514 2084969 := bstep (se 2 (by rfl) ⟨781863, by rfl⟩ : syracuseStep 2084969 = 1563727) B1563727
theorem B40087709 : Blo 1389514 40087709 := bstep (se 3 (by rfl) ⟨7516445, by rfl⟩ : syracuseStep 40087709 = 15032891) B15032891
theorem B2085287 : Blo 1389514 2085287 := bstep (se 1 (by rfl) ⟨1563965, by rfl⟩ : syracuseStep 2085287 = 3127931) B3127931
theorem B3518903 : Blo 1389514 3518903 := bstep (se 1 (by rfl) ⟨2639177, by rfl⟩ : syracuseStep 3518903 = 5278355) B5278355
theorem B2085371 : Blo 1389514 2085371 := bstep (se 1 (by rfl) ⟨1564028, by rfl⟩ : syracuseStep 2085371 = 3128057) B3128057
theorem B5009939 : Blo 1389514 5009939 := bstep (se 1 (by rfl) ⟨3757454, by rfl⟩ : syracuseStep 5009939 = 7514909) B7514909
theorem B19018289 : Blo 1389514 19018289 := bstep (se 2 (by rfl) ⟨7131858, by rfl⟩ : syracuseStep 19018289 = 14263717) B14263717
theorem B2085497 : Blo 1389514 2085497 := bstep (se 2 (by rfl) ⟨782061, by rfl⟩ : syracuseStep 2085497 = 1564123) B1564123
theorem B10048121 : Blo 1389514 10048121 := bstep (se 2 (by rfl) ⟨3768045, by rfl⟩ : syracuseStep 10048121 = 7536091) B7536091
theorem B2085551 : Blo 1389514 2085551 := bstep (se 1 (by rfl) ⟨1564163, by rfl⟩ : syracuseStep 2085551 = 3128327) B3128327
theorem B4690655 : Blo 1389514 4690655 := bstep (se 1 (by rfl) ⟨3517991, by rfl⟩ : syracuseStep 4690655 = 7035983) B7035983
theorem B2085599 : Blo 1389514 2085599 := bstep (se 1 (by rfl) ⟨1564199, by rfl⟩ : syracuseStep 2085599 = 3128399) B3128399
theorem B3338999 : Blo 1389514 3338999 := bstep (se 1 (by rfl) ⟨2504249, by rfl⟩ : syracuseStep 3338999 = 5008499) B5008499
theorem B81236765 : Blo 1389514 81236765 := bstep (se 3 (by rfl) ⟨15231893, by rfl⟩ : syracuseStep 81236765 = 30463787) B30463787
theorem B1389519 : Blo 1389514 1389519 := bstep (se 1 (by rfl) ⟨1042139, by rfl⟩ : syracuseStep 1389519 = 2084279) B2084279
theorem B1389543 : Blo 1389514 1389543 := bstep (se 1 (by rfl) ⟨1042157, by rfl⟩ : syracuseStep 1389543 = 2084315) B2084315
theorem B2085863 : Blo 1389514 2085863 := bstep (se 1 (by rfl) ⟨1564397, by rfl⟩ : syracuseStep 2085863 = 3128795) B3128795
theorem B3961831 : Blo 1389514 3961831 := bstep (se 1 (by rfl) ⟨2971373, by rfl⟩ : syracuseStep 3961831 = 5942747) B5942747
theorem B32109625 : Blo 1389514 32109625 := bstep (se 2 (by rfl) ⟨12041109, by rfl⟩ : syracuseStep 32109625 = 24082219) B24082219
theorem B6681689 : Blo 1389514 6681689 := bstep (se 2 (by rfl) ⟨2505633, by rfl⟩ : syracuseStep 6681689 = 5011267) B5011267
theorem B15234173 : Blo 1389514 15234173 := bstep (se 3 (by rfl) ⟨2856407, by rfl⟩ : syracuseStep 15234173 = 5712815) B5712815
theorem B3757195 : Blo 1389514 3757195 := bstep (se 1 (by rfl) ⟨2817896, by rfl⟩ : syracuseStep 3757195 = 5635793) B5635793
theorem B4691087 : Blo 1389514 4691087 := bstep (se 1 (by rfl) ⟨3518315, by rfl⟩ : syracuseStep 4691087 = 7036631) B7036631
theorem B5280983 : Blo 1389514 5280983 := bstep (se 1 (by rfl) ⟨3960737, by rfl⟩ : syracuseStep 5280983 = 7921475) B7921475
theorem B3126491 : Blo 1389514 3126491 := bstep (se 1 (by rfl) ⟨2344868, by rfl⟩ : syracuseStep 3126491 = 4689737) B4689737
theorem B2086121 : Blo 1389514 2086121 := bstep (se 2 (by rfl) ⟨782295, by rfl⟩ : syracuseStep 2086121 = 1564591) B1564591
theorem B3962105 : Blo 1389514 3962105 := bstep (se 2 (by rfl) ⟨1485789, by rfl⟩ : syracuseStep 3962105 = 2971579) B2971579
theorem B1389855 : Blo 1389514 1389855 := bstep (se 1 (by rfl) ⟨1042391, by rfl⟩ : syracuseStep 1389855 = 2084783) B2084783
theorem B2086175 : Blo 1389514 2086175 := bstep (se 1 (by rfl) ⟨1564631, by rfl⟩ : syracuseStep 2086175 = 3129263) B3129263
theorem B1389915 : Blo 1389514 1389915 := bstep (se 1 (by rfl) ⟨1042436, by rfl⟩ : syracuseStep 1389915 = 2084873) B2084873
theorem B1389935 : Blo 1389514 1389935 := bstep (se 1 (by rfl) ⟨1042451, by rfl⟩ : syracuseStep 1389935 = 2084903) B2084903
theorem B3126689 : Blo 1389514 3126689 := bstep (se 2 (by rfl) ⟨1172508, by rfl⟩ : syracuseStep 3126689 = 2345017) B2345017
theorem B1389991 : Blo 1389514 1389991 := bstep (se 1 (by rfl) ⟨1042493, by rfl⟩ : syracuseStep 1389991 = 2084987) B2084987
theorem B2504135 : Blo 1389514 2504135 := bstep (se 1 (by rfl) ⟨1878101, by rfl⟩ : syracuseStep 2504135 = 3756203) B3756203
theorem B2086343 : Blo 1389514 2086343 := bstep (se 1 (by rfl) ⟨1564757, by rfl⟩ : syracuseStep 2086343 = 3129515) B3129515
theorem B1390075 : Blo 1389514 1390075 := bstep (se 1 (by rfl) ⟨1042556, by rfl⟩ : syracuseStep 1390075 = 2085113) B2085113
theorem B3520007 : Blo 1389514 3520007 := bstep (se 1 (by rfl) ⟨2640005, by rfl⟩ : syracuseStep 3520007 = 5280011) B5280011
theorem B3520057 : Blo 1389514 3520057 := bstep (se 2 (by rfl) ⟨1320021, by rfl⟩ : syracuseStep 3520057 = 2640043) B2640043
theorem B1390143 : Blo 1389514 1390143 := bstep (se 1 (by rfl) ⟨1042607, by rfl⟩ : syracuseStep 1390143 = 2085215) B2085215
theorem B1390151 : Blo 1389514 1390151 := bstep (se 1 (by rfl) ⟨1042613, by rfl⟩ : syracuseStep 1390151 = 2085227) B2085227
theorem B3012191 : Blo 1389514 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B7624327 : Blo 1389514 7624327 := bstep (se 1 (by rfl) ⟨5718245, by rfl⟩ : syracuseStep 7624327 = 11436491) B11436491
theorem B7034525 : Blo 1389514 7034525 := bstep (se 3 (by rfl) ⟨1318973, by rfl⟩ : syracuseStep 7034525 = 2637947) B2637947
theorem B1390303 : Blo 1389514 1390303 := bstep (se 1 (by rfl) ⟨1042727, by rfl⟩ : syracuseStep 1390303 = 2085455) B2085455
theorem B2971399 : Blo 1389514 2971399 := bstep (se 1 (by rfl) ⟨2228549, by rfl⟩ : syracuseStep 2971399 = 4457099) B4457099
theorem B2086697 : Blo 1389514 2086697 := bstep (se 2 (by rfl) ⟨782511, by rfl⟩ : syracuseStep 2086697 = 1565023) B1565023
theorem B1390383 : Blo 1389514 1390383 := bstep (se 1 (by rfl) ⟨1042787, by rfl⟩ : syracuseStep 1390383 = 2085575) B2085575
theorem B2086703 : Blo 1389514 2086703 := bstep (se 1 (by rfl) ⟨1565027, by rfl⟩ : syracuseStep 2086703 = 3130055) B3130055
theorem B3520361 : Blo 1389514 3520361 := bstep (se 2 (by rfl) ⟨1320135, by rfl⟩ : syracuseStep 3520361 = 2640271) B2640271
theorem B1390491 : Blo 1389514 1390491 := bstep (se 1 (by rfl) ⟨1042868, by rfl⟩ : syracuseStep 1390491 = 2085737) B2085737
theorem B2226127 : Blo 1389514 2226127 := bstep (se 1 (by rfl) ⟨1669595, by rfl⟩ : syracuseStep 2226127 = 3339191) B3339191
theorem B3127247 : Blo 1389514 3127247 := bstep (se 1 (by rfl) ⟨2345435, by rfl⟩ : syracuseStep 3127247 = 4690871) B4690871
theorem B1390543 : Blo 1389514 1390543 := bstep (se 1 (by rfl) ⟨1042907, by rfl⟩ : syracuseStep 1390543 = 2085815) B2085815
theorem B1390567 : Blo 1389514 1390567 := bstep (se 1 (by rfl) ⟨1042925, by rfl⟩ : syracuseStep 1390567 = 2085851) B2085851
theorem B4692221 : Blo 1389514 4692221 := bstep (se 3 (by rfl) ⟨879791, by rfl⟩ : syracuseStep 4692221 = 1759583) B1759583
theorem B2087177 : Blo 1389514 2087177 := bstep (se 2 (by rfl) ⟨782691, by rfl⟩ : syracuseStep 2087177 = 1565383) B1565383
theorem B6338845 : Blo 1389514 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B1390879 : Blo 1389514 1390879 := bstep (se 1 (by rfl) ⟨1043159, by rfl⟩ : syracuseStep 1390879 = 2086319) B2086319
theorem B3127625 : Blo 1389514 3127625 := bstep (se 2 (by rfl) ⟨1172859, by rfl⟩ : syracuseStep 3127625 = 2345719) B2345719
theorem B3127643 : Blo 1389514 3127643 := bstep (se 1 (by rfl) ⟨2345732, by rfl⟩ : syracuseStep 3127643 = 4691465) B4691465
theorem B1390939 : Blo 1389514 1390939 := bstep (se 1 (by rfl) ⟨1043204, by rfl⟩ : syracuseStep 1390939 = 2086409) B2086409
theorem B1390959 : Blo 1389514 1390959 := bstep (se 1 (by rfl) ⟨1043219, by rfl⟩ : syracuseStep 1390959 = 2086439) B2086439
theorem B1391015 : Blo 1389514 1391015 := bstep (se 1 (by rfl) ⟨1043261, by rfl⟩ : syracuseStep 1391015 = 2086523) B2086523
theorem B23755193 : Blo 1389514 23755193 := bstep (se 2 (by rfl) ⟨8908197, by rfl⟩ : syracuseStep 23755193 = 17816395) B17816395
theorem B3520979 : Blo 1389514 3520979 := bstep (se 1 (by rfl) ⟨2640734, by rfl⟩ : syracuseStep 3520979 = 5281469) B5281469
theorem B1391099 : Blo 1389514 1391099 := bstep (se 1 (by rfl) ⟨1043324, by rfl⟩ : syracuseStep 1391099 = 2086649) B2086649
theorem B13539899 : Blo 1389514 13539899 := bstep (se 1 (by rfl) ⟨10154924, by rfl⟩ : syracuseStep 13539899 = 20309849) B20309849
theorem B12679739 : Blo 1389514 12679739 := bstep (se 1 (by rfl) ⟨9509804, by rfl⟩ : syracuseStep 12679739 = 19019609) B19019609
theorem B1391167 : Blo 1389514 1391167 := bstep (se 1 (by rfl) ⟨1043375, by rfl⟩ : syracuseStep 1391167 = 2086751) B2086751
theorem B1391175 : Blo 1389514 1391175 := bstep (se 1 (by rfl) ⟨1043381, by rfl⟩ : syracuseStep 1391175 = 2086763) B2086763
theorem B13367915 : Blo 1389514 13367915 := bstep (se 1 (by rfl) ⟨10025936, by rfl⟩ : syracuseStep 13367915 = 20051873) B20051873
theorem B7043759 : Blo 1389514 7043759 := bstep (se 1 (by rfl) ⟨5282819, by rfl⟩ : syracuseStep 7043759 = 10565639) B10565639
theorem B1981103 : Blo 1389514 1981103 := bstep (se 1 (by rfl) ⟨1485827, by rfl⟩ : syracuseStep 1981103 = 2971655) B2971655
theorem B5634755 : Blo 1389514 5634755 := bstep (se 1 (by rfl) ⟨4226066, by rfl⟩ : syracuseStep 5634755 = 8452133) B8452133
theorem B11885251 : Blo 1389514 11885251 := bstep (se 1 (by rfl) ⟨8913938, by rfl⟩ : syracuseStep 11885251 = 17827877) B17827877
theorem B1391327 : Blo 1389514 1391327 := bstep (se 1 (by rfl) ⟨1043495, by rfl⟩ : syracuseStep 1391327 = 2086991) B2086991
theorem B5937911 : Blo 1389514 5937911 := bstep (se 1 (by rfl) ⟨4453433, by rfl⟩ : syracuseStep 5937911 = 8906867) B8906867
theorem B1563439 : Blo 1389514 1563439 := bstep (se 1 (by rfl) ⟨1172579, by rfl⟩ : syracuseStep 1563439 = 2345159) B2345159
theorem B1391407 : Blo 1389514 1391407 := bstep (se 1 (by rfl) ⟨1043555, by rfl⟩ : syracuseStep 1391407 = 2087111) B2087111
theorem B7519043 : Blo 1389514 7519043 := bstep (se 1 (by rfl) ⟨5639282, by rfl⟩ : syracuseStep 7519043 = 11278565) B11278565
theorem B12688271 : Blo 1389514 12688271 := bstep (se 1 (by rfl) ⟨9516203, by rfl⟩ : syracuseStep 12688271 = 19032407) B19032407
theorem B1563547 : Blo 1389514 1563547 := bstep (se 1 (by rfl) ⟨1172660, by rfl⟩ : syracuseStep 1563547 = 2345321) B2345321
theorem B3128219 : Blo 1389514 3128219 := bstep (se 1 (by rfl) ⟨2346164, by rfl⟩ : syracuseStep 3128219 = 4692329) B4692329
theorem B7035821 : Blo 1389514 7035821 := bstep (se 3 (by rfl) ⟨1319216, by rfl⟩ : syracuseStep 7035821 = 2638433) B2638433
theorem B1760231 : Blo 1389514 1760231 := bstep (se 1 (by rfl) ⟨1320173, by rfl⟩ : syracuseStep 1760231 = 2640347) B2640347
theorem B7044083 : Blo 1389514 7044083 := bstep (se 1 (by rfl) ⟨5283062, by rfl⟩ : syracuseStep 7044083 = 10566125) B10566125
theorem B4693031 : Blo 1389514 4693031 := bstep (se 1 (by rfl) ⟨3519773, by rfl⟩ : syracuseStep 4693031 = 7039547) B7039547
theorem B3128417 : Blo 1389514 3128417 := bstep (se 2 (by rfl) ⟨1173156, by rfl⟩ : syracuseStep 3128417 = 2346313) B2346313
theorem B20331643 : Blo 1389514 20331643 := bstep (se 1 (by rfl) ⟨15248732, by rfl⟩ : syracuseStep 20331643 = 30497465) B30497465
theorem B1563943 : Blo 1389514 1563943 := bstep (se 1 (by rfl) ⟨1172957, by rfl⟩ : syracuseStep 1563943 = 2345915) B2345915
theorem B3128615 : Blo 1389514 3128615 := bstep (se 1 (by rfl) ⟨2346461, by rfl⟩ : syracuseStep 3128615 = 4692923) B4692923
theorem B15842627 : Blo 1389514 15842627 := bstep (se 1 (by rfl) ⟨11881970, by rfl⟩ : syracuseStep 15842627 = 23763941) B23763941
theorem B1564015 : Blo 1389514 1564015 := bstep (se 1 (by rfl) ⟨1173011, by rfl⟩ : syracuseStep 1564015 = 2346023) B2346023
theorem B7519625 : Blo 1389514 7519625 := bstep (se 2 (by rfl) ⟨2819859, by rfl⟩ : syracuseStep 7519625 = 5639719) B5639719
theorem B30080393 : Blo 1389514 30080393 := bstep (se 2 (by rfl) ⟨11280147, by rfl⟩ : syracuseStep 30080393 = 22560295) B22560295
theorem B3341729 : Blo 1389514 3341729 := bstep (se 2 (by rfl) ⟨1253148, by rfl⟩ : syracuseStep 3341729 = 2506297) B2506297
theorem B4693463 : Blo 1389514 4693463 := bstep (se 1 (by rfl) ⟨3520097, by rfl⟩ : syracuseStep 4693463 = 7040195) B7040195
theorem B5938697 : Blo 1389514 5938697 := bstep (se 2 (by rfl) ⟨2227011, by rfl⟩ : syracuseStep 5938697 = 4454023) B4454023
theorem B16055819 : Blo 1389514 16055819 := bstep (se 1 (by rfl) ⟨12041864, by rfl⟩ : syracuseStep 16055819 = 24083729) B24083729
theorem B1564231 : Blo 1389514 1564231 := bstep (se 1 (by rfl) ⟨1173173, by rfl⟩ : syracuseStep 1564231 = 2346347) B2346347
theorem B3522143 : Blo 1389514 3522143 := bstep (se 1 (by rfl) ⟨2641607, by rfl⟩ : syracuseStep 3522143 = 5283215) B5283215
theorem B3128993 : Blo 1389514 3128993 := bstep (se 2 (by rfl) ⟨1173372, by rfl⟩ : syracuseStep 3128993 = 2346745) B2346745
theorem B7618315 : Blo 1389514 7618315 := bstep (se 1 (by rfl) ⟨5713736, by rfl⟩ : syracuseStep 7618315 = 11427473) B11427473
theorem B54157843 : Blo 1389514 54157843 := bstep (se 1 (by rfl) ⟨40618382, by rfl⟩ : syracuseStep 54157843 = 81236765) B81236765
theorem B13910723 : Blo 1389514 13910723 := bstep (se 1 (by rfl) ⟨10433042, by rfl⟩ : syracuseStep 13910723 = 20866085) B20866085
theorem B6685379 : Blo 1389514 6685379 := bstep (se 1 (by rfl) ⟨5014034, by rfl⟩ : syracuseStep 6685379 = 10028069) B10028069
theorem B20038373 : Blo 1389514 20038373 := bstep (se 4 (by rfl) ⟨1878597, by rfl⟩ : syracuseStep 20038373 = 3757195) B3757195
theorem B3130091 : Blo 1389514 3130091 := bstep (se 1 (by rfl) ⟨2347568, by rfl⟩ : syracuseStep 3130091 = 4695137) B4695137
theorem B15844085 : Blo 1389514 15844085 := bstep (se 5 (by rfl) ⟨742691, by rfl⟩ : syracuseStep 15844085 = 1485383) B1485383
theorem B4457227 : Blo 1389514 4457227 := bstep (se 1 (by rfl) ⟨3342920, by rfl⟩ : syracuseStep 4457227 = 6685841) B6685841
theorem B2008127 : Blo 1389514 2008127 := bstep (se 1 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 2008127 = 3012191) B3012191
theorem B15828047 : Blo 1389514 15828047 := bstep (se 1 (by rfl) ⟨11871035, by rfl⟩ : syracuseStep 15828047 = 23742071) B23742071
theorem B42812833 : Blo 1389514 42812833 := bstep (se 2 (by rfl) ⟨16054812, by rfl⟩ : syracuseStep 42812833 = 32109625) B32109625
theorem B27108857 : Blo 1389514 27108857 := bstep (se 2 (by rfl) ⟨10165821, by rfl⟩ : syracuseStep 27108857 = 20331643) B20331643
theorem B15836795 : Blo 1389514 15836795 := bstep (se 1 (by rfl) ⟨11877596, by rfl⟩ : syracuseStep 15836795 = 23755193) B23755193
theorem B4695839 : Blo 1389514 4695839 := bstep (se 1 (by rfl) ⟨3521879, by rfl⟩ : syracuseStep 4695839 = 7043759) B7043759
theorem B3958607 : Blo 1389514 3958607 := bstep (se 1 (by rfl) ⟨2968955, by rfl⟩ : syracuseStep 3958607 = 5937911) B5937911
theorem B2344943 : Blo 1389514 2344943 := bstep (se 1 (by rfl) ⟨1758707, by rfl⟩ : syracuseStep 2344943 = 3517415) B3517415
theorem B2377711 : Blo 1389514 2377711 := bstep (se 1 (by rfl) ⟨1783283, by rfl⟩ : syracuseStep 2377711 = 3566567) B3566567
theorem B4696055 : Blo 1389514 4696055 := bstep (se 1 (by rfl) ⟨3522041, by rfl⟩ : syracuseStep 4696055 = 7044083) B7044083
theorem B7923865 : Blo 1389514 7923865 := bstep (se 2 (by rfl) ⟨2971449, by rfl⟩ : syracuseStep 7923865 = 5942899) B5942899
theorem B10561751 : Blo 1389514 10561751 := bstep (se 1 (by rfl) ⟨7921313, by rfl⟩ : syracuseStep 10561751 = 15842627) B15842627
theorem B3959131 : Blo 1389514 3959131 := bstep (se 1 (by rfl) ⟨2969348, by rfl⟩ : syracuseStep 3959131 = 5938697) B5938697
theorem B4286881 : Blo 1389514 4286881 := bstep (se 2 (by rfl) ⟨1607580, by rfl⟩ : syracuseStep 4286881 = 3215161) B3215161
theorem B4753889 : Blo 1389514 4753889 := bstep (se 2 (by rfl) ⟨1782708, by rfl⟩ : syracuseStep 4753889 = 3565417) B3565417
theorem B2345503 : Blo 1389514 2345503 := bstep (se 1 (by rfl) ⟨1759127, by rfl⟩ : syracuseStep 2345503 = 3518255) B3518255
theorem B2968169 : Blo 1389514 2968169 := bstep (se 2 (by rfl) ⟨1113063, by rfl⟩ : syracuseStep 2968169 = 2226127) B2226127
theorem B5941943 : Blo 1389514 5941943 := bstep (se 1 (by rfl) ⟨4456457, by rfl⟩ : syracuseStep 5941943 = 8912915) B8912915
theorem B26725139 : Blo 1389514 26725139 := bstep (se 1 (by rfl) ⟨20043854, by rfl⟩ : syracuseStep 26725139 = 40087709) B40087709
theorem B2345935 : Blo 1389514 2345935 := bstep (se 1 (by rfl) ⟨1759451, by rfl⟩ : syracuseStep 2345935 = 3518903) B3518903
theorem B4230569 : Blo 1389514 4230569 := bstep (se 2 (by rfl) ⟨1586463, by rfl⟩ : syracuseStep 4230569 = 3172927) B3172927
theorem B3960247 : Blo 1389514 3960247 := bstep (se 1 (by rfl) ⟨2970185, by rfl⟩ : syracuseStep 3960247 = 5940371) B5940371
theorem B2084327 : Blo 1389514 2084327 := bstep (se 1 (by rfl) ⟨1563245, by rfl⟩ : syracuseStep 2084327 = 3126491) B3126491
theorem B2641403 : Blo 1389514 2641403 := bstep (se 1 (by rfl) ⟨1981052, by rfl⟩ : syracuseStep 2641403 = 3962105) B3962105
theorem B15847001 : Blo 1389514 15847001 := bstep (se 2 (by rfl) ⟨5942625, by rfl⟩ : syracuseStep 15847001 = 11885251) B11885251
theorem B2084459 : Blo 1389514 2084459 := bstep (se 1 (by rfl) ⟨1563344, by rfl⟩ : syracuseStep 2084459 = 3126689) B3126689
theorem B2346671 : Blo 1389514 2346671 := bstep (se 1 (by rfl) ⟨1760003, by rfl⟩ : syracuseStep 2346671 = 3520007) B3520007
theorem B2084585 : Blo 1389514 2084585 := bstep (se 2 (by rfl) ⟨781719, by rfl⟩ : syracuseStep 2084585 = 1563439) B1563439
theorem B4689683 : Blo 1389514 4689683 := bstep (se 1 (by rfl) ⟨3517262, by rfl⟩ : syracuseStep 4689683 = 7034525) B7034525
theorem B2084729 : Blo 1389514 2084729 := bstep (se 2 (by rfl) ⟨781773, by rfl⟩ : syracuseStep 2084729 = 1563547) B1563547
theorem B3616633 : Blo 1389514 3616633 := bstep (se 2 (by rfl) ⟨1356237, by rfl⟩ : syracuseStep 3616633 = 2712475) B2712475
theorem B2346907 : Blo 1389514 2346907 := bstep (se 1 (by rfl) ⟨1760180, by rfl⟩ : syracuseStep 2346907 = 3520361) B3520361
theorem B2084831 : Blo 1389514 2084831 := bstep (se 1 (by rfl) ⟨1563623, by rfl⟩ : syracuseStep 2084831 = 3127247) B3127247
theorem B2085083 : Blo 1389514 2085083 := bstep (se 1 (by rfl) ⟨1563812, by rfl⟩ : syracuseStep 2085083 = 3127625) B3127625
theorem B2085095 : Blo 1389514 2085095 := bstep (se 1 (by rfl) ⟨1563821, by rfl⟩ : syracuseStep 2085095 = 3127643) B3127643
theorem B2347319 : Blo 1389514 2347319 := bstep (se 1 (by rfl) ⟨1760489, by rfl⟩ : syracuseStep 2347319 = 3520979) B3520979
theorem B2085257 : Blo 1389514 2085257 := bstep (se 2 (by rfl) ⟨781971, by rfl⟩ : syracuseStep 2085257 = 1563943) B1563943
theorem B5943719 : Blo 1389514 5943719 := bstep (se 1 (by rfl) ⟨4457789, by rfl⟩ : syracuseStep 5943719 = 8915579) B8915579
theorem B7041491 : Blo 1389514 7041491 := bstep (se 1 (by rfl) ⟨5281118, by rfl⟩ : syracuseStep 7041491 = 10562237) B10562237
theorem B3756503 : Blo 1389514 3756503 := bstep (se 1 (by rfl) ⟨2817377, by rfl⟩ : syracuseStep 3756503 = 5634755) B5634755
theorem B2085353 : Blo 1389514 2085353 := bstep (se 2 (by rfl) ⟨782007, by rfl⟩ : syracuseStep 2085353 = 1564015) B1564015
theorem B8458847 : Blo 1389514 8458847 := bstep (se 1 (by rfl) ⟨6344135, by rfl⟩ : syracuseStep 8458847 = 12688271) B12688271
theorem B2085479 : Blo 1389514 2085479 := bstep (se 1 (by rfl) ⟨1564109, by rfl⟩ : syracuseStep 2085479 = 3128219) B3128219
theorem B4690547 : Blo 1389514 4690547 := bstep (se 1 (by rfl) ⟨3517910, by rfl⟩ : syracuseStep 4690547 = 7035821) B7035821
theorem B2085611 : Blo 1389514 2085611 := bstep (se 1 (by rfl) ⟨1564208, by rfl⟩ : syracuseStep 2085611 = 3128417) B3128417
theorem B4453127 : Blo 1389514 4453127 := bstep (se 1 (by rfl) ⟨3339845, by rfl⟩ : syracuseStep 4453127 = 6679691) B6679691
theorem B2085641 : Blo 1389514 2085641 := bstep (se 2 (by rfl) ⟨782115, by rfl⟩ : syracuseStep 2085641 = 1564231) B1564231
theorem B5935913 : Blo 1389514 5935913 := bstep (se 2 (by rfl) ⟨2225967, by rfl⟩ : syracuseStep 5935913 = 4451935) B4451935
theorem B2085743 : Blo 1389514 2085743 := bstep (se 1 (by rfl) ⟨1564307, by rfl⟩ : syracuseStep 2085743 = 3128615) B3128615
theorem B4690817 : Blo 1389514 4690817 := bstep (se 2 (by rfl) ⟨1759056, by rfl⟩ : syracuseStep 4690817 = 3518113) B3518113
theorem B1389563 : Blo 1389514 1389563 := bstep (se 1 (by rfl) ⟨1042172, by rfl⟩ : syracuseStep 1389563 = 2084345) B2084345
theorem B10703879 : Blo 1389514 10703879 := bstep (se 1 (by rfl) ⟨8027909, by rfl⟩ : syracuseStep 10703879 = 16055819) B16055819
theorem B3961865 : Blo 1389514 3961865 := bstep (se 2 (by rfl) ⟨1485699, by rfl⟩ : syracuseStep 3961865 = 2971399) B2971399
theorem B1389631 : Blo 1389514 1389631 := bstep (se 1 (by rfl) ⟨1042223, by rfl⟩ : syracuseStep 1389631 = 2084447) B2084447
theorem B3519551 : Blo 1389514 3519551 := bstep (se 1 (by rfl) ⟨2639663, by rfl⟩ : syracuseStep 3519551 = 5279327) B5279327
theorem B2348095 : Blo 1389514 2348095 := bstep (se 1 (by rfl) ⟨1761071, by rfl⟩ : syracuseStep 2348095 = 3522143) B3522143
theorem B2085995 : Blo 1389514 2085995 := bstep (se 1 (by rfl) ⟨1564496, by rfl⟩ : syracuseStep 2085995 = 3128993) B3128993
theorem B1389775 : Blo 1389514 1389775 := bstep (se 1 (by rfl) ⟨1042331, by rfl⟩ : syracuseStep 1389775 = 2084663) B2084663
theorem B2086235 : Blo 1389514 2086235 := bstep (se 1 (by rfl) ⟨1564676, by rfl⟩ : syracuseStep 2086235 = 3129353) B3129353
theorem B1389979 : Blo 1389514 1389979 := bstep (se 1 (by rfl) ⟨1042484, by rfl⟩ : syracuseStep 1389979 = 2084969) B2084969
theorem B1390191 : Blo 1389514 1390191 := bstep (se 1 (by rfl) ⟨1042643, by rfl⟩ : syracuseStep 1390191 = 2085287) B2085287
theorem B2086511 : Blo 1389514 2086511 := bstep (se 1 (by rfl) ⟨1564883, by rfl⟩ : syracuseStep 2086511 = 3129767) B3129767
theorem B1390247 : Blo 1389514 1390247 := bstep (se 1 (by rfl) ⟨1042685, by rfl⟩ : syracuseStep 1390247 = 2085371) B2085371
theorem B4691627 : Blo 1389514 4691627 := bstep (se 1 (by rfl) ⟨3518720, by rfl⟩ : syracuseStep 4691627 = 7037441) B7037441
theorem B3339959 : Blo 1389514 3339959 := bstep (se 1 (by rfl) ⟨2504969, by rfl⟩ : syracuseStep 3339959 = 5009939) B5009939
theorem B2086583 : Blo 1389514 2086583 := bstep (se 1 (by rfl) ⟨1564937, by rfl⟩ : syracuseStep 2086583 = 3129875) B3129875
theorem B12678859 : Blo 1389514 12678859 := bstep (se 1 (by rfl) ⟨9509144, by rfl⟩ : syracuseStep 12678859 = 19018289) B19018289
theorem B8451793 : Blo 1389514 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B2086619 : Blo 1389514 2086619 := bstep (se 1 (by rfl) ⟨1564964, by rfl⟩ : syracuseStep 2086619 = 3129929) B3129929
theorem B1390331 : Blo 1389514 1390331 := bstep (se 1 (by rfl) ⟨1042748, by rfl⟩ : syracuseStep 1390331 = 2085497) B2085497
theorem B6698747 : Blo 1389514 6698747 := bstep (se 1 (by rfl) ⟨5024060, by rfl⟩ : syracuseStep 6698747 = 10048121) B10048121
theorem B1390367 : Blo 1389514 1390367 := bstep (se 1 (by rfl) ⟨1042775, by rfl⟩ : syracuseStep 1390367 = 2085551) B2085551
theorem B3127103 : Blo 1389514 3127103 := bstep (se 1 (by rfl) ⟨2345327, by rfl⟩ : syracuseStep 3127103 = 4690655) B4690655
theorem B1390399 : Blo 1389514 1390399 := bstep (se 1 (by rfl) ⟨1042799, by rfl⟩ : syracuseStep 1390399 = 2085599) B2085599
theorem B2225999 : Blo 1389514 2225999 := bstep (se 1 (by rfl) ⟨1669499, by rfl⟩ : syracuseStep 2225999 = 3338999) B3338999
theorem B2086793 : Blo 1389514 2086793 := bstep (se 2 (by rfl) ⟨782547, by rfl⟩ : syracuseStep 2086793 = 1565095) B1565095
theorem B15841169 : Blo 1389514 15841169 := bstep (se 2 (by rfl) ⟨5940438, by rfl⟩ : syracuseStep 15841169 = 11880877) B11880877
theorem B4691951 : Blo 1389514 4691951 := bstep (se 1 (by rfl) ⟨3518963, by rfl⟩ : syracuseStep 4691951 = 7037927) B7037927
theorem B1390575 : Blo 1389514 1390575 := bstep (se 1 (by rfl) ⟨1042931, by rfl⟩ : syracuseStep 1390575 = 2085863) B2085863
theorem B2086895 : Blo 1389514 2086895 := bstep (se 1 (by rfl) ⟨1565171, by rfl⟩ : syracuseStep 2086895 = 3130343) B3130343
theorem B4454459 : Blo 1389514 4454459 := bstep (se 1 (by rfl) ⟨3340844, by rfl⟩ : syracuseStep 4454459 = 6681689) B6681689
theorem B10156115 : Blo 1389514 10156115 := bstep (se 1 (by rfl) ⟨7617086, by rfl⟩ : syracuseStep 10156115 = 15234173) B15234173
theorem B3127391 : Blo 1389514 3127391 := bstep (se 1 (by rfl) ⟨2345543, by rfl⟩ : syracuseStep 3127391 = 4691087) B4691087
theorem B3520655 : Blo 1389514 3520655 := bstep (se 1 (by rfl) ⟨2640491, by rfl⟩ : syracuseStep 3520655 = 5280983) B5280983
theorem B1390747 : Blo 1389514 1390747 := bstep (se 1 (by rfl) ⟨1043060, by rfl⟩ : syracuseStep 1390747 = 2086121) B2086121
theorem B1390783 : Blo 1389514 1390783 := bstep (se 1 (by rfl) ⟨1043087, by rfl⟩ : syracuseStep 1390783 = 2086175) B2086175
theorem B4692167 : Blo 1389514 4692167 := bstep (se 1 (by rfl) ⟨3519125, by rfl⟩ : syracuseStep 4692167 = 7038251) B7038251
theorem B2087147 : Blo 1389514 2087147 := bstep (se 1 (by rfl) ⟨1565360, by rfl⟩ : syracuseStep 2087147 = 3130721) B3130721
theorem B2087207 : Blo 1389514 2087207 := bstep (se 1 (by rfl) ⟨1565405, by rfl⟩ : syracuseStep 2087207 = 3130811) B3130811
theorem B1669423 : Blo 1389514 1669423 := bstep (se 1 (by rfl) ⟨1252067, by rfl⟩ : syracuseStep 1669423 = 2504135) B2504135
theorem B1390895 : Blo 1389514 1390895 := bstep (se 1 (by rfl) ⟨1043171, by rfl⟩ : syracuseStep 1390895 = 2086343) B2086343
theorem B5011901 : Blo 1389514 5011901 := bstep (se 3 (by rfl) ⟨939731, by rfl⟩ : syracuseStep 5011901 = 1879463) B1879463
theorem B1391131 : Blo 1389514 1391131 := bstep (se 1 (by rfl) ⟨1043348, by rfl⟩ : syracuseStep 1391131 = 2086697) B2086697
theorem B1391135 : Blo 1389514 1391135 := bstep (se 1 (by rfl) ⟨1043351, by rfl⟩ : syracuseStep 1391135 = 2086703) B2086703
theorem B5282441 : Blo 1389514 5282441 := bstep (se 2 (by rfl) ⟨1980915, by rfl⟩ : syracuseStep 5282441 = 3961831) B3961831
theorem B4692815 : Blo 1389514 4692815 := bstep (se 1 (by rfl) ⟨3519611, by rfl⟩ : syracuseStep 4692815 = 7039223) B7039223
theorem B3128147 : Blo 1389514 3128147 := bstep (se 1 (by rfl) ⟨2346110, by rfl⟩ : syracuseStep 3128147 = 4692221) B4692221
theorem B1391451 : Blo 1389514 1391451 := bstep (se 1 (by rfl) ⟨1043588, by rfl⟩ : syracuseStep 1391451 = 2087177) B2087177
theorem B9026599 : Blo 1389514 9026599 := bstep (se 1 (by rfl) ⟨6769949, by rfl⟩ : syracuseStep 9026599 = 13539899) B13539899
theorem B8453159 : Blo 1389514 8453159 := bstep (se 1 (by rfl) ⟨6339869, by rfl⟩ : syracuseStep 8453159 = 12679739) B12679739
theorem B8911943 : Blo 1389514 8911943 := bstep (se 1 (by rfl) ⟨6683957, by rfl⟩ : syracuseStep 8911943 = 13367915) B13367915
theorem B289111133 : Blo 1389514 289111133 := bstep (se 3 (by rfl) ⟨54208337, by rfl⟩ : syracuseStep 289111133 = 108416675) B108416675
theorem B5282941 : Blo 1389514 5282941 := bstep (se 3 (by rfl) ⟨990551, by rfl⟩ : syracuseStep 5282941 = 1981103) B1981103
theorem B4693139 : Blo 1389514 4693139 := bstep (se 1 (by rfl) ⟨3519854, by rfl⟩ : syracuseStep 4693139 = 7039709) B7039709
theorem B5012695 : Blo 1389514 5012695 := bstep (se 1 (by rfl) ⟨3759521, by rfl⟩ : syracuseStep 5012695 = 7519043) B7519043
theorem B1563871 : Blo 1389514 1563871 := bstep (se 1 (by rfl) ⟨1172903, by rfl⟩ : syracuseStep 1563871 = 2345807) B2345807
theorem B3128687 : Blo 1389514 3128687 := bstep (se 1 (by rfl) ⟨2346515, by rfl⟩ : syracuseStep 3128687 = 4693031) B4693031
theorem B8904097 : Blo 1389514 8904097 := bstep (se 2 (by rfl) ⟨3339036, by rfl⟩ : syracuseStep 8904097 = 6678073) B6678073
theorem B4693409 : Blo 1389514 4693409 := bstep (se 2 (by rfl) ⟨1760028, by rfl⟩ : syracuseStep 4693409 = 3520057) B3520057
theorem B10165769 : Blo 1389514 10165769 := bstep (se 2 (by rfl) ⟨3812163, by rfl⟩ : syracuseStep 10165769 = 7624327) B7624327
theorem B5013083 : Blo 1389514 5013083 := bstep (se 1 (by rfl) ⟨3759812, by rfl⟩ : syracuseStep 5013083 = 7519625) B7519625
theorem B20053595 : Blo 1389514 20053595 := bstep (se 1 (by rfl) ⟨15040196, by rfl⟩ : syracuseStep 20053595 = 30080393) B30080393
theorem B2227819 : Blo 1389514 2227819 := bstep (se 1 (by rfl) ⟨1670864, by rfl⟩ : syracuseStep 2227819 = 3341729) B3341729
theorem B3128975 : Blo 1389514 3128975 := bstep (se 1 (by rfl) ⟨2346731, by rfl⟩ : syracuseStep 3128975 = 4693463) B4693463
theorem B10157753 : Blo 1389514 10157753 := bstep (se 2 (by rfl) ⟨3809157, by rfl⟩ : syracuseStep 10157753 = 7618315) B7618315
theorem B3129065 : Blo 1389514 3129065 := bstep (se 2 (by rfl) ⟨1173399, by rfl⟩ : syracuseStep 3129065 = 2346799) B2346799
theorem B30072707 : Blo 1389514 30072707 := bstep (se 1 (by rfl) ⟨22554530, by rfl⟩ : syracuseStep 30072707 = 45109061) B45109061
theorem B4693949 : Blo 1389514 4693949 := bstep (se 3 (by rfl) ⟨880115, by rfl⟩ : syracuseStep 4693949 = 1760231) B1760231
theorem B1564879 : Blo 1389514 1564879 := bstep (se 1 (by rfl) ⟨1173659, by rfl⟩ : syracuseStep 1564879 = 2347319) B2347319
theorem B27082973 : Blo 1389514 27082973 := bstep (se 3 (by rfl) ⟨5078057, by rfl⟩ : syracuseStep 27082973 = 10156115) B10156115
theorem B4694327 : Blo 1389514 4694327 := bstep (se 1 (by rfl) ⟨3520745, by rfl⟩ : syracuseStep 4694327 = 7041491) B7041491
theorem B9273815 : Blo 1389514 9273815 := bstep (se 1 (by rfl) ⟨6955361, by rfl⟩ : syracuseStep 9273815 = 13910723) B13910723
theorem B4456919 : Blo 1389514 4456919 := bstep (se 1 (by rfl) ⟨3342689, by rfl⟩ : syracuseStep 4456919 = 6685379) B6685379
theorem B3957275 : Blo 1389514 3957275 := bstep (se 1 (by rfl) ⟨2967956, by rfl⟩ : syracuseStep 3957275 = 5935913) B5935913
theorem B7135919 : Blo 1389514 7135919 := bstep (se 1 (by rfl) ⟨5351939, by rfl⟩ : syracuseStep 7135919 = 10703879) B10703879
theorem B10552031 : Blo 1389514 10552031 := bstep (se 1 (by rfl) ⟨7914023, by rfl⟩ : syracuseStep 10552031 = 15828047) B15828047
theorem B18072571 : Blo 1389514 18072571 := bstep (se 1 (by rfl) ⟨13554428, by rfl⟩ : syracuseStep 18072571 = 27108857) B27108857
theorem B11281517 : Blo 1389514 11281517 := bstep (se 3 (by rfl) ⟨2115284, by rfl⟩ : syracuseStep 11281517 = 4230569) B4230569
theorem B3130559 : Blo 1389514 3130559 := bstep (se 1 (by rfl) ⟨2347919, by rfl⟩ : syracuseStep 3130559 = 4695839) B4695839
theorem B2639071 : Blo 1389514 2639071 := bstep (se 1 (by rfl) ⟨1979303, by rfl⟩ : syracuseStep 2639071 = 3958607) B3958607
theorem B10560779 : Blo 1389514 10560779 := bstep (se 1 (by rfl) ⟨7920584, by rfl⟩ : syracuseStep 10560779 = 15841169) B15841169
theorem B3130703 : Blo 1389514 3130703 := bstep (se 1 (by rfl) ⟨2348027, by rfl⟩ : syracuseStep 3130703 = 4696055) B4696055
theorem B12035465 : Blo 1389514 12035465 := bstep (se 2 (by rfl) ⟨4513299, by rfl⟩ : syracuseStep 12035465 = 9026599) B9026599
theorem B3130793 : Blo 1389514 3130793 := bstep (se 2 (by rfl) ⟨1174047, by rfl⟩ : syracuseStep 3130793 = 2348095) B2348095
theorem B7915117 : Blo 1389514 7915117 := bstep (se 3 (by rfl) ⟨1484084, by rfl⟩ : syracuseStep 7915117 = 2968169) B2968169
theorem B11872129 : Blo 1389514 11872129 := bstep (se 2 (by rfl) ⟨4452048, by rfl⟩ : syracuseStep 11872129 = 8904097) B8904097
theorem B57083777 : Blo 1389514 57083777 := bstep (se 2 (by rfl) ⟨21406416, by rfl⟩ : syracuseStep 57083777 = 42812833) B42812833
theorem B5941295 : Blo 1389514 5941295 := bstep (se 1 (by rfl) ⟨4455971, by rfl⟩ : syracuseStep 5941295 = 8911943) B8911943
theorem B6777179 : Blo 1389514 6777179 := bstep (se 1 (by rfl) ⟨5082884, by rfl⟩ : syracuseStep 6777179 = 10165769) B10165769
theorem B20048471 : Blo 1389514 20048471 := bstep (se 1 (by rfl) ⟨15036353, by rfl⟩ : syracuseStep 20048471 = 30072707) B30072707
theorem B5639231 : Blo 1389514 5639231 := bstep (se 1 (by rfl) ⟨4229423, by rfl⟩ : syracuseStep 5639231 = 8458847) B8458847
theorem B5278841 : Blo 1389514 5278841 := bstep (se 2 (by rfl) ⟨1979565, by rfl⟩ : syracuseStep 5278841 = 3959131) B3959131
theorem B10562723 : Blo 1389514 10562723 := bstep (se 1 (by rfl) ⟨7922042, by rfl⟩ : syracuseStep 10562723 = 15844085) B15844085
theorem B2968751 : Blo 1389514 2968751 := bstep (se 1 (by rfl) ⟨2226563, by rfl⟩ : syracuseStep 2968751 = 4453127) B4453127
theorem B2641243 : Blo 1389514 2641243 := bstep (se 1 (by rfl) ⟨1980932, by rfl⟩ : syracuseStep 2641243 = 3961865) B3961865
theorem B2346367 : Blo 1389514 2346367 := bstep (se 1 (by rfl) ⟨1759775, by rfl⟩ : syracuseStep 2346367 = 3519551) B3519551
theorem B5942969 : Blo 1389514 5942969 := bstep (se 2 (by rfl) ⟨2228613, by rfl⟩ : syracuseStep 5942969 = 4457227) B4457227
theorem B2084735 : Blo 1389514 2084735 := bstep (se 1 (by rfl) ⟨1563551, by rfl⟩ : syracuseStep 2084735 = 3127103) B3127103
theorem B2969639 : Blo 1389514 2969639 := bstep (se 1 (by rfl) ⟨2227229, by rfl⟩ : syracuseStep 2969639 = 4454459) B4454459
theorem B2084927 : Blo 1389514 2084927 := bstep (se 1 (by rfl) ⟨1563695, by rfl⟩ : syracuseStep 2084927 = 3127391) B3127391
theorem B2347103 : Blo 1389514 2347103 := bstep (se 1 (by rfl) ⟨1760327, by rfl⟩ : syracuseStep 2347103 = 3520655) B3520655
theorem B7041167 : Blo 1389514 7041167 := bstep (se 1 (by rfl) ⟨5280875, by rfl⟩ : syracuseStep 7041167 = 10561751) B10561751
theorem B2085161 : Blo 1389514 2085161 := bstep (se 2 (by rfl) ⟨781935, by rfl⟩ : syracuseStep 2085161 = 1563871) B1563871
theorem B3961295 : Blo 1389514 3961295 := bstep (se 1 (by rfl) ⟨2970971, by rfl⟩ : syracuseStep 3961295 = 5941943) B5941943
theorem B2085431 : Blo 1389514 2085431 := bstep (se 1 (by rfl) ⟨1564073, by rfl⟩ : syracuseStep 2085431 = 3128147) B3128147
theorem B5280329 : Blo 1389514 5280329 := bstep (se 2 (by rfl) ⟨1980123, by rfl⟩ : syracuseStep 5280329 = 3960247) B3960247
theorem B19288709 : Blo 1389514 19288709 := bstep (se 4 (by rfl) ⟨1808316, by rfl⟩ : syracuseStep 19288709 = 3616633) B3616633
theorem B17863325 : Blo 1389514 17863325 := bstep (se 3 (by rfl) ⟨3349373, by rfl⟩ : syracuseStep 17863325 = 6698747) B6698747
theorem B2970425 : Blo 1389514 2970425 := bstep (se 2 (by rfl) ⟨1113909, by rfl⟩ : syracuseStep 2970425 = 2227819) B2227819
theorem B5935997 : Blo 1389514 5935997 := bstep (se 3 (by rfl) ⟨1112999, by rfl⟩ : syracuseStep 5935997 = 2225999) B2225999
theorem B2085791 : Blo 1389514 2085791 := bstep (se 1 (by rfl) ⟨1564343, by rfl⟩ : syracuseStep 2085791 = 3128687) B3128687
theorem B16905145 : Blo 1389514 16905145 := bstep (se 2 (by rfl) ⟨6339429, by rfl⟩ : syracuseStep 16905145 = 12678859) B12678859
theorem B11269057 : Blo 1389514 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B1389551 : Blo 1389514 1389551 := bstep (se 1 (by rfl) ⟨1042163, by rfl⟩ : syracuseStep 1389551 = 2084327) B2084327
theorem B10564667 : Blo 1389514 10564667 := bstep (se 1 (by rfl) ⟨7923500, by rfl⟩ : syracuseStep 10564667 = 15847001) B15847001
theorem B1389639 : Blo 1389514 1389639 := bstep (se 1 (by rfl) ⟨1042229, by rfl⟩ : syracuseStep 1389639 = 2084459) B2084459
theorem B2085983 : Blo 1389514 2085983 := bstep (se 1 (by rfl) ⟨1564487, by rfl⟩ : syracuseStep 2085983 = 3128975) B3128975
theorem B6771835 : Blo 1389514 6771835 := bstep (se 1 (by rfl) ⟨5078876, by rfl⟩ : syracuseStep 6771835 = 10157753) B10157753
theorem B1389723 : Blo 1389514 1389723 := bstep (se 1 (by rfl) ⟨1042292, by rfl⟩ : syracuseStep 1389723 = 2084585) B2084585
theorem B2086043 : Blo 1389514 2086043 := bstep (se 1 (by rfl) ⟨1564532, by rfl⟩ : syracuseStep 2086043 = 3129065) B3129065
theorem B3126455 : Blo 1389514 3126455 := bstep (se 1 (by rfl) ⟨2344841, by rfl⟩ : syracuseStep 3126455 = 4689683) B4689683
theorem B1389819 : Blo 1389514 1389819 := bstep (se 1 (by rfl) ⟨1042364, by rfl⟩ : syracuseStep 1389819 = 2084729) B2084729
theorem B1389887 : Blo 1389514 1389887 := bstep (se 1 (by rfl) ⟨1042415, by rfl⟩ : syracuseStep 1389887 = 2084831) B2084831
theorem B1390055 : Blo 1389514 1390055 := bstep (se 1 (by rfl) ⟨1042541, by rfl⟩ : syracuseStep 1390055 = 2085083) B2085083
theorem B1390063 : Blo 1389514 1390063 := bstep (se 1 (by rfl) ⟨1042547, by rfl⟩ : syracuseStep 1390063 = 2085095) B2085095
theorem B5355005 : Blo 1389514 5355005 := bstep (se 3 (by rfl) ⟨1004063, by rfl⟩ : syracuseStep 5355005 = 2008127) B2008127
theorem B10565153 : Blo 1389514 10565153 := bstep (se 2 (by rfl) ⟨3961932, by rfl⟩ : syracuseStep 10565153 = 7923865) B7923865
theorem B1390171 : Blo 1389514 1390171 := bstep (se 1 (by rfl) ⟨1042628, by rfl⟩ : syracuseStep 1390171 = 2085257) B2085257
theorem B1390235 : Blo 1389514 1390235 := bstep (se 1 (by rfl) ⟨1042676, by rfl⟩ : syracuseStep 1390235 = 2085353) B2085353
theorem B2225897 : Blo 1389514 2225897 := bstep (se 2 (by rfl) ⟨834711, by rfl⟩ : syracuseStep 2225897 = 1669423) B1669423
theorem B1390319 : Blo 1389514 1390319 := bstep (se 1 (by rfl) ⟨1042739, by rfl⟩ : syracuseStep 1390319 = 2085479) B2085479
theorem B3127031 : Blo 1389514 3127031 := bstep (se 1 (by rfl) ⟨2345273, by rfl⟩ : syracuseStep 3127031 = 4690547) B4690547
theorem B13358915 : Blo 1389514 13358915 := bstep (se 1 (by rfl) ⟨10019186, by rfl⟩ : syracuseStep 13358915 = 20038373) B20038373
theorem B1390407 : Blo 1389514 1390407 := bstep (se 1 (by rfl) ⟨1042805, by rfl⟩ : syracuseStep 1390407 = 2085611) B2085611
theorem B2086727 : Blo 1389514 2086727 := bstep (se 1 (by rfl) ⟨1565045, by rfl⟩ : syracuseStep 2086727 = 3130091) B3130091
theorem B1390427 : Blo 1389514 1390427 := bstep (se 1 (by rfl) ⟨1042820, by rfl⟩ : syracuseStep 1390427 = 2085641) B2085641
theorem B5715841 : Blo 1389514 5715841 := bstep (se 2 (by rfl) ⟨2143440, by rfl⟩ : syracuseStep 5715841 = 4286881) B4286881
theorem B1390495 : Blo 1389514 1390495 := bstep (se 1 (by rfl) ⟨1042871, by rfl⟩ : syracuseStep 1390495 = 2085743) B2085743
theorem B3127211 : Blo 1389514 3127211 := bstep (se 1 (by rfl) ⟨2345408, by rfl⟩ : syracuseStep 3127211 = 4690817) B4690817
theorem B72210457 : Blo 1389514 72210457 := bstep (se 2 (by rfl) ⟨27078921, by rfl⟩ : syracuseStep 72210457 = 54157843) B54157843
theorem B3127337 : Blo 1389514 3127337 := bstep (se 2 (by rfl) ⟨1172751, by rfl⟩ : syracuseStep 3127337 = 2345503) B2345503
theorem B1390663 : Blo 1389514 1390663 := bstep (se 1 (by rfl) ⟨1042997, by rfl⟩ : syracuseStep 1390663 = 2085995) B2085995
theorem B1390823 : Blo 1389514 1390823 := bstep (se 1 (by rfl) ⟨1043117, by rfl⟩ : syracuseStep 1390823 = 2086235) B2086235
theorem B1391007 : Blo 1389514 1391007 := bstep (se 1 (by rfl) ⟨1043255, by rfl⟩ : syracuseStep 1391007 = 2086511) B2086511
theorem B10557863 : Blo 1389514 10557863 := bstep (se 1 (by rfl) ⟨7918397, by rfl⟩ : syracuseStep 10557863 = 15836795) B15836795
theorem B15849917 : Blo 1389514 15849917 := bstep (se 3 (by rfl) ⟨2971859, by rfl⟩ : syracuseStep 15849917 = 5943719) B5943719
theorem B3127751 : Blo 1389514 3127751 := bstep (se 1 (by rfl) ⟨2345813, by rfl⟩ : syracuseStep 3127751 = 4691627) B4691627
theorem B1391055 : Blo 1389514 1391055 := bstep (se 1 (by rfl) ⟨1043291, by rfl⟩ : syracuseStep 1391055 = 2086583) B2086583
theorem B1391079 : Blo 1389514 1391079 := bstep (se 1 (by rfl) ⟨1043309, by rfl⟩ : syracuseStep 1391079 = 2086619) B2086619
theorem B10017341 : Blo 1389514 10017341 := bstep (se 3 (by rfl) ⟨1878251, by rfl⟩ : syracuseStep 10017341 = 3756503) B3756503
theorem B1391195 : Blo 1389514 1391195 := bstep (se 1 (by rfl) ⟨1043396, by rfl⟩ : syracuseStep 1391195 = 2086793) B2086793
theorem B3127913 : Blo 1389514 3127913 := bstep (se 2 (by rfl) ⟨1172967, by rfl⟩ : syracuseStep 3127913 = 2345935) B2345935
theorem B1563295 : Blo 1389514 1563295 := bstep (se 1 (by rfl) ⟨1172471, by rfl⟩ : syracuseStep 1563295 = 2344943) B2344943
theorem B3127967 : Blo 1389514 3127967 := bstep (se 1 (by rfl) ⟨2345975, by rfl⟩ : syracuseStep 3127967 = 4691951) B4691951
theorem B1391263 : Blo 1389514 1391263 := bstep (se 1 (by rfl) ⟨1043447, by rfl⟩ : syracuseStep 1391263 = 2086895) B2086895
theorem B3128111 : Blo 1389514 3128111 := bstep (se 1 (by rfl) ⟨2346083, by rfl⟩ : syracuseStep 3128111 = 4692167) B4692167
theorem B1391431 : Blo 1389514 1391431 := bstep (se 1 (by rfl) ⟨1043573, by rfl⟩ : syracuseStep 1391431 = 2087147) B2087147
theorem B7043921 : Blo 1389514 7043921 := bstep (se 2 (by rfl) ⟨2641470, by rfl⟩ : syracuseStep 7043921 = 5282941) B5282941
theorem B1391471 : Blo 1389514 1391471 := bstep (se 1 (by rfl) ⟨1043603, by rfl⟩ : syracuseStep 1391471 = 2087207) B2087207
theorem B6683593 : Blo 1389514 6683593 := bstep (se 2 (by rfl) ⟨2506347, by rfl⟩ : syracuseStep 6683593 = 5012695) B5012695
theorem B3341267 : Blo 1389514 3341267 := bstep (se 1 (by rfl) ⟨2505950, by rfl⟩ : syracuseStep 3341267 = 5011901) B5011901
theorem B3169259 : Blo 1389514 3169259 := bstep (se 1 (by rfl) ⟨2376944, by rfl⟩ : syracuseStep 3169259 = 4753889) B4753889
theorem B3521627 : Blo 1389514 3521627 := bstep (se 1 (by rfl) ⟨2641220, by rfl⟩ : syracuseStep 3521627 = 5282441) B5282441
theorem B17816759 : Blo 1389514 17816759 := bstep (se 1 (by rfl) ⟨13362569, by rfl⟩ : syracuseStep 17816759 = 26725139) B26725139
theorem B3128543 : Blo 1389514 3128543 := bstep (se 1 (by rfl) ⟨2346407, by rfl⟩ : syracuseStep 3128543 = 4692815) B4692815
theorem B35626229 : Blo 1389514 35626229 := bstep (se 5 (by rfl) ⟨1669979, by rfl⟩ : syracuseStep 35626229 = 3339959) B3339959
theorem B5635439 : Blo 1389514 5635439 := bstep (se 1 (by rfl) ⟨4226579, by rfl⟩ : syracuseStep 5635439 = 8453159) B8453159
theorem B192740755 : Blo 1389514 192740755 := bstep (se 1 (by rfl) ⟨144555566, by rfl⟩ : syracuseStep 192740755 = 289111133) B289111133
theorem B3128759 : Blo 1389514 3128759 := bstep (se 1 (by rfl) ⟨2346569, by rfl⟩ : syracuseStep 3128759 = 4693139) B4693139
theorem B3128939 : Blo 1389514 3128939 := bstep (se 1 (by rfl) ⟨2346704, by rfl⟩ : syracuseStep 3128939 = 4693409) B4693409
theorem B1760935 : Blo 1389514 1760935 := bstep (se 1 (by rfl) ⟨1320701, by rfl⟩ : syracuseStep 1760935 = 2641403) B2641403
theorem B3342055 : Blo 1389514 3342055 := bstep (se 1 (by rfl) ⟨2506541, by rfl⟩ : syracuseStep 3342055 = 5013083) B5013083
theorem B13369063 : Blo 1389514 13369063 := bstep (se 1 (by rfl) ⟨10026797, by rfl⟩ : syracuseStep 13369063 = 20053595) B20053595
theorem B1564447 : Blo 1389514 1564447 := bstep (se 1 (by rfl) ⟨1173335, by rfl⟩ : syracuseStep 1564447 = 2346671) B2346671
theorem B3129209 : Blo 1389514 3129209 := bstep (se 2 (by rfl) ⟨1173453, by rfl⟩ : syracuseStep 3129209 = 2346907) B2346907
theorem B3129299 : Blo 1389514 3129299 := bstep (se 1 (by rfl) ⟨2346974, by rfl⟩ : syracuseStep 3129299 = 4693949) B4693949
theorem B3170281 : Blo 1389514 3170281 := bstep (se 2 (by rfl) ⟨1188855, by rfl⟩ : syracuseStep 3170281 = 2377711) B2377711
theorem B96280609 : Blo 1389514 96280609 := bstep (se 2 (by rfl) ⟨36105228, by rfl⟩ : syracuseStep 96280609 = 72210457) B72210457
theorem B1564735 : Blo 1389514 1564735 := bstep (se 1 (by rfl) ⟨1173551, by rfl⟩ : syracuseStep 1564735 = 2347103) B2347103
theorem B4694111 : Blo 1389514 4694111 := bstep (se 1 (by rfl) ⟨3520583, by rfl⟩ : syracuseStep 4694111 = 7041167) B7041167
theorem B18055315 : Blo 1389514 18055315 := bstep (se 1 (by rfl) ⟨13541486, by rfl⟩ : syracuseStep 18055315 = 27082973) B27082973
theorem B3129551 : Blo 1389514 3129551 := bstep (se 1 (by rfl) ⟨2347163, by rfl⟩ : syracuseStep 3129551 = 4694327) B4694327
theorem B2638183 : Blo 1389514 2638183 := bstep (se 1 (by rfl) ⟨1978637, by rfl⟩ : syracuseStep 2638183 = 3957275) B3957275
theorem B3957331 : Blo 1389514 3957331 := bstep (se 1 (by rfl) ⟨2967998, by rfl⟩ : syracuseStep 3957331 = 5935997) B5935997
theorem B7521011 : Blo 1389514 7521011 := bstep (se 1 (by rfl) ⟨5640758, by rfl⟩ : syracuseStep 7521011 = 11281517) B11281517
theorem B1483931 : Blo 1389514 1483931 := bstep (se 1 (by rfl) ⟨1112948, by rfl⟩ : syracuseStep 1483931 = 2225897) B2225897
theorem B8905943 : Blo 1389514 8905943 := bstep (se 1 (by rfl) ⟨6679457, by rfl⟩ : syracuseStep 8905943 = 13358915) B13358915
theorem B15025409 : Blo 1389514 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B14280013 : Blo 1389514 14280013 := bstep (se 3 (by rfl) ⟨2677502, by rfl⟩ : syracuseStep 14280013 = 5355005) B5355005
theorem B9029113 : Blo 1389514 9029113 := bstep (se 2 (by rfl) ⟨3385917, by rfl⟩ : syracuseStep 9029113 = 6771835) B6771835
theorem B7038575 : Blo 1389514 7038575 := bstep (se 1 (by rfl) ⟨5278931, by rfl⟩ : syracuseStep 7038575 = 10557863) B10557863
theorem B6678227 : Blo 1389514 6678227 := bstep (se 1 (by rfl) ⟨5008670, by rfl⟩ : syracuseStep 6678227 = 10017341) B10017341
theorem B4695947 : Blo 1389514 4695947 := bstep (se 1 (by rfl) ⟨3521960, by rfl⟩ : syracuseStep 4695947 = 7043921) B7043921
theorem B10553489 : Blo 1389514 10553489 := bstep (se 2 (by rfl) ⟨3957558, by rfl⟩ : syracuseStep 10553489 = 7915117) B7915117
theorem B23750819 : Blo 1389514 23750819 := bstep (se 1 (by rfl) ⟨17813114, by rfl⟩ : syracuseStep 23750819 = 35626229) B35626229
theorem B15829505 : Blo 1389514 15829505 := bstep (se 2 (by rfl) ⟨5936064, by rfl⟩ : syracuseStep 15829505 = 11872129) B11872129
theorem B7621121 : Blo 1389514 7621121 := bstep (se 2 (by rfl) ⟨2857920, by rfl⟩ : syracuseStep 7621121 = 5715841) B5715841
theorem B2640863 : Blo 1389514 2640863 := bstep (se 1 (by rfl) ⟨1980647, by rfl⟩ : syracuseStep 2640863 = 3961295) B3961295
theorem B2084303 : Blo 1389514 2084303 := bstep (se 1 (by rfl) ⟨1563227, by rfl⟩ : syracuseStep 2084303 = 3126455) B3126455
theorem B7040519 : Blo 1389514 7040519 := bstep (se 1 (by rfl) ⟨5280389, by rfl⟩ : syracuseStep 7040519 = 10560779) B10560779
theorem B2084393 : Blo 1389514 2084393 := bstep (se 2 (by rfl) ⟨781647, by rfl⟩ : syracuseStep 2084393 = 1563295) B1563295
theorem B8023643 : Blo 1389514 8023643 := bstep (se 1 (by rfl) ⟨6017732, by rfl⟩ : syracuseStep 8023643 = 12035465) B12035465
theorem B2084687 : Blo 1389514 2084687 := bstep (se 1 (by rfl) ⟨1563515, by rfl⟩ : syracuseStep 2084687 = 3127031) B3127031
theorem B22540193 : Blo 1389514 22540193 := bstep (se 2 (by rfl) ⟨8452572, by rfl⟩ : syracuseStep 22540193 = 16905145) B16905145
theorem B38055851 : Blo 1389514 38055851 := bstep (se 1 (by rfl) ⟨28541888, by rfl⟩ : syracuseStep 38055851 = 57083777) B57083777
theorem B2084807 : Blo 1389514 2084807 := bstep (se 1 (by rfl) ⟨1563605, by rfl⟩ : syracuseStep 2084807 = 3127211) B3127211
theorem B24096761 : Blo 1389514 24096761 := bstep (se 2 (by rfl) ⟨9036285, by rfl⟩ : syracuseStep 24096761 = 18072571) B18072571
theorem B2084891 : Blo 1389514 2084891 := bstep (se 1 (by rfl) ⟨1563668, by rfl⟩ : syracuseStep 2084891 = 3127337) B3127337
theorem B3960863 : Blo 1389514 3960863 := bstep (se 1 (by rfl) ⟨2970647, by rfl⟩ : syracuseStep 3960863 = 5941295) B5941295
theorem B4518119 : Blo 1389514 4518119 := bstep (se 1 (by rfl) ⟨3388589, by rfl⟩ : syracuseStep 4518119 = 6777179) B6777179
theorem B3518761 : Blo 1389514 3518761 := bstep (se 2 (by rfl) ⟨1319535, by rfl⟩ : syracuseStep 3518761 = 2639071) B2639071
theorem B2085167 : Blo 1389514 2085167 := bstep (se 1 (by rfl) ⟨1563875, by rfl⟩ : syracuseStep 2085167 = 3127751) B3127751
theorem B13365647 : Blo 1389514 13365647 := bstep (se 1 (by rfl) ⟨10024235, by rfl⟩ : syracuseStep 13365647 = 20048471) B20048471
theorem B2085275 : Blo 1389514 2085275 := bstep (se 1 (by rfl) ⟨1563956, by rfl⟩ : syracuseStep 2085275 = 3127913) B3127913
theorem B2085311 : Blo 1389514 2085311 := bstep (se 1 (by rfl) ⟨1563983, by rfl⟩ : syracuseStep 2085311 = 3127967) B3127967
theorem B76116469 : Blo 1389514 76116469 := bstep (se 5 (by rfl) ⟨3567959, by rfl⟩ : syracuseStep 76116469 = 7135919) B7135919
theorem B256987673 : Blo 1389514 256987673 := bstep (se 2 (by rfl) ⟨96370377, by rfl⟩ : syracuseStep 256987673 = 192740755) B192740755
theorem B2085407 : Blo 1389514 2085407 := bstep (se 1 (by rfl) ⟨1564055, by rfl⟩ : syracuseStep 2085407 = 3128111) B3128111
theorem B2347751 : Blo 1389514 2347751 := bstep (se 1 (by rfl) ⟨1760813, by rfl⟩ : syracuseStep 2347751 = 3521627) B3521627
theorem B3519227 : Blo 1389514 3519227 := bstep (se 1 (by rfl) ⟨2639420, by rfl⟩ : syracuseStep 3519227 = 5278841) B5278841
theorem B7041815 : Blo 1389514 7041815 := bstep (se 1 (by rfl) ⟨5281361, by rfl⟩ : syracuseStep 7041815 = 10562723) B10562723
theorem B1979167 : Blo 1389514 1979167 := bstep (se 1 (by rfl) ⟨1484375, by rfl⟩ : syracuseStep 1979167 = 2968751) B2968751
theorem B2085695 : Blo 1389514 2085695 := bstep (se 1 (by rfl) ⟨1564271, by rfl⟩ : syracuseStep 2085695 = 3128543) B3128543
theorem B2347913 : Blo 1389514 2347913 := bstep (se 2 (by rfl) ⟨880467, by rfl⟩ : syracuseStep 2347913 = 1760935) B1760935
theorem B3756959 : Blo 1389514 3756959 := bstep (se 1 (by rfl) ⟨2817719, by rfl⟩ : syracuseStep 3756959 = 5635439) B5635439
theorem B2085839 : Blo 1389514 2085839 := bstep (se 1 (by rfl) ⟨1564379, by rfl⟩ : syracuseStep 2085839 = 3128759) B3128759
theorem B2085929 : Blo 1389514 2085929 := bstep (se 2 (by rfl) ⟨782223, by rfl⟩ : syracuseStep 2085929 = 1564447) B1564447
theorem B2085959 : Blo 1389514 2085959 := bstep (se 1 (by rfl) ⟨1564469, by rfl⟩ : syracuseStep 2085959 = 3128939) B3128939
theorem B3961979 : Blo 1389514 3961979 := bstep (se 1 (by rfl) ⟨2971484, by rfl⟩ : syracuseStep 3961979 = 5942969) B5942969
theorem B2086139 : Blo 1389514 2086139 := bstep (se 1 (by rfl) ⟨1564604, by rfl⟩ : syracuseStep 2086139 = 3129209) B3129209
theorem B1389823 : Blo 1389514 1389823 := bstep (se 1 (by rfl) ⟨1042367, by rfl⟩ : syracuseStep 1389823 = 2084735) B2084735
theorem B2086199 : Blo 1389514 2086199 := bstep (se 1 (by rfl) ⟨1564649, by rfl⟩ : syracuseStep 2086199 = 3129299) B3129299
theorem B1979759 : Blo 1389514 1979759 := bstep (se 1 (by rfl) ⟨1484819, by rfl⟩ : syracuseStep 1979759 = 2969639) B2969639
theorem B1389951 : Blo 1389514 1389951 := bstep (se 1 (by rfl) ⟨1042463, by rfl⟩ : syracuseStep 1389951 = 2084927) B2084927
theorem B15037949 : Blo 1389514 15037949 := bstep (se 3 (by rfl) ⟨2819615, by rfl⟩ : syracuseStep 15037949 = 5639231) B5639231
theorem B1390107 : Blo 1389514 1390107 := bstep (se 1 (by rfl) ⟨1042580, by rfl⟩ : syracuseStep 1390107 = 2085161) B2085161
theorem B2086505 : Blo 1389514 2086505 := bstep (se 2 (by rfl) ⟨782439, by rfl⟩ : syracuseStep 2086505 = 1564879) B1564879
theorem B6182543 : Blo 1389514 6182543 := bstep (se 1 (by rfl) ⟨4636907, by rfl⟩ : syracuseStep 6182543 = 9273815) B9273815
theorem B2971279 : Blo 1389514 2971279 := bstep (se 1 (by rfl) ⟨2228459, by rfl⟩ : syracuseStep 2971279 = 4456919) B4456919
theorem B1390287 : Blo 1389514 1390287 := bstep (se 1 (by rfl) ⟨1042715, by rfl⟩ : syracuseStep 1390287 = 2085431) B2085431
theorem B3520219 : Blo 1389514 3520219 := bstep (se 1 (by rfl) ⟨2640164, by rfl⟩ : syracuseStep 3520219 = 5280329) B5280329
theorem B12859139 : Blo 1389514 12859139 := bstep (se 1 (by rfl) ⟨9644354, by rfl⟩ : syracuseStep 12859139 = 19288709) B19288709
theorem B11908883 : Blo 1389514 11908883 := bstep (se 1 (by rfl) ⟨8931662, by rfl⟩ : syracuseStep 11908883 = 17863325) B17863325
theorem B7034687 : Blo 1389514 7034687 := bstep (se 1 (by rfl) ⟨5276015, by rfl⟩ : syracuseStep 7034687 = 10552031) B10552031
theorem B1980283 : Blo 1389514 1980283 := bstep (se 1 (by rfl) ⟨1485212, by rfl⟩ : syracuseStep 1980283 = 2970425) B2970425
theorem B1390527 : Blo 1389514 1390527 := bstep (se 1 (by rfl) ⟨1042895, by rfl⟩ : syracuseStep 1390527 = 2085791) B2085791
theorem B7043111 : Blo 1389514 7043111 := bstep (se 1 (by rfl) ⟨5282333, by rfl⟩ : syracuseStep 7043111 = 10564667) B10564667
theorem B1390655 : Blo 1389514 1390655 := bstep (se 1 (by rfl) ⟨1042991, by rfl⟩ : syracuseStep 1390655 = 2085983) B2085983
theorem B1390695 : Blo 1389514 1390695 := bstep (se 1 (by rfl) ⟨1043021, by rfl⟩ : syracuseStep 1390695 = 2086043) B2086043
theorem B2087039 : Blo 1389514 2087039 := bstep (se 1 (by rfl) ⟨1565279, by rfl⟩ : syracuseStep 2087039 = 3130559) B3130559
theorem B2087135 : Blo 1389514 2087135 := bstep (se 1 (by rfl) ⟨1565351, by rfl⟩ : syracuseStep 2087135 = 3130703) B3130703
theorem B2087195 : Blo 1389514 2087195 := bstep (se 1 (by rfl) ⟨1565396, by rfl⟩ : syracuseStep 2087195 = 3130793) B3130793
theorem B7043435 : Blo 1389514 7043435 := bstep (se 1 (by rfl) ⟨5282576, by rfl⟩ : syracuseStep 7043435 = 10565153) B10565153
theorem B1391151 : Blo 1389514 1391151 := bstep (se 1 (by rfl) ⟨1043363, by rfl⟩ : syracuseStep 1391151 = 2086727) B2086727
theorem B8911457 : Blo 1389514 8911457 := bstep (se 2 (by rfl) ⟨3341796, by rfl⟩ : syracuseStep 8911457 = 6683593) B6683593
theorem B10566611 : Blo 1389514 10566611 := bstep (se 1 (by rfl) ⟨7924958, by rfl⟩ : syracuseStep 10566611 = 15849917) B15849917
theorem B3521657 : Blo 1389514 3521657 := bstep (se 2 (by rfl) ⟨1320621, by rfl⟩ : syracuseStep 3521657 = 2641243) B2641243
theorem B3128489 : Blo 1389514 3128489 := bstep (se 2 (by rfl) ⟨1173183, by rfl⟩ : syracuseStep 3128489 = 2346367) B2346367
theorem B2227511 : Blo 1389514 2227511 := bstep (se 1 (by rfl) ⟨1670633, by rfl⟩ : syracuseStep 2227511 = 3341267) B3341267
theorem B2112839 : Blo 1389514 2112839 := bstep (se 1 (by rfl) ⟨1584629, by rfl⟩ : syracuseStep 2112839 = 3169259) B3169259
theorem B11877839 : Blo 1389514 11877839 := bstep (se 1 (by rfl) ⟨8908379, by rfl⟩ : syracuseStep 11877839 = 17816759) B17816759
theorem B4456073 : Blo 1389514 4456073 := bstep (se 2 (by rfl) ⟨1671027, by rfl⟩ : syracuseStep 4456073 = 3342055) B3342055
theorem B17825417 : Blo 1389514 17825417 := bstep (se 2 (by rfl) ⟨6684531, by rfl⟩ : syracuseStep 17825417 = 13369063) B13369063
theorem B4227041 : Blo 1389514 4227041 := bstep (se 2 (by rfl) ⟨1585140, by rfl⟩ : syracuseStep 4227041 = 3170281) B3170281
theorem B3129407 : Blo 1389514 3129407 := bstep (se 1 (by rfl) ⟨2347055, by rfl⟩ : syracuseStep 3129407 = 4694111) B4694111
theorem B3957149 : Blo 1389514 3957149 := bstep (se 3 (by rfl) ⟨741965, by rfl⟩ : syracuseStep 3957149 = 1483931) B1483931
theorem B1565167 : Blo 1389514 1565167 := bstep (se 1 (by rfl) ⟨1173875, by rfl⟩ : syracuseStep 1565167 = 2347751) B2347751
theorem B5014007 : Blo 1389514 5014007 := bstep (se 1 (by rfl) ⟨3760505, by rfl⟩ : syracuseStep 5014007 = 7521011) B7521011
theorem B4694543 : Blo 1389514 4694543 := bstep (se 1 (by rfl) ⟨3520907, by rfl⟩ : syracuseStep 4694543 = 7041815) B7041815
theorem B1565275 : Blo 1389514 1565275 := bstep (se 1 (by rfl) ⟨1173956, by rfl⟩ : syracuseStep 1565275 = 2347913) B2347913
theorem B5276441 : Blo 1389514 5276441 := bstep (se 2 (by rfl) ⟨1978665, by rfl⟩ : syracuseStep 5276441 = 3957331) B3957331
theorem B5940029 : Blo 1389514 5940029 := bstep (se 3 (by rfl) ⟨1113755, by rfl⟩ : syracuseStep 5940029 = 2227511) B2227511
theorem B2638889 : Blo 1389514 2638889 := bstep (se 2 (by rfl) ⟨989583, by rfl⟩ : syracuseStep 2638889 = 1979167) B1979167
theorem B4121695 : Blo 1389514 4121695 := bstep (se 1 (by rfl) ⟨3091271, by rfl⟩ : syracuseStep 4121695 = 6182543) B6182543
theorem B7939255 : Blo 1389514 7939255 := bstep (se 1 (by rfl) ⟨5954441, by rfl⟩ : syracuseStep 7939255 = 11908883) B11908883
theorem B3130631 : Blo 1389514 3130631 := bstep (se 1 (by rfl) ⟨2347973, by rfl⟩ : syracuseStep 3130631 = 4695947) B4695947
theorem B4695407 : Blo 1389514 4695407 := bstep (se 1 (by rfl) ⟨3521555, by rfl⟩ : syracuseStep 4695407 = 7043111) B7043111
theorem B4695623 : Blo 1389514 4695623 := bstep (se 1 (by rfl) ⟨3521717, by rfl⟩ : syracuseStep 4695623 = 7043435) B7043435
theorem B10553003 : Blo 1389514 10553003 := bstep (se 1 (by rfl) ⟨7914752, by rfl⟩ : syracuseStep 10553003 = 15829505) B15829505
theorem B5080747 : Blo 1389514 5080747 := bstep (se 1 (by rfl) ⟨3810560, by rfl⟩ : syracuseStep 5080747 = 7621121) B7621121
theorem B5940971 : Blo 1389514 5940971 := bstep (se 1 (by rfl) ⟨4455728, by rfl⟩ : syracuseStep 5940971 = 8911457) B8911457
theorem B19040017 : Blo 1389514 19040017 := bstep (se 2 (by rfl) ⟨7140006, by rfl⟩ : syracuseStep 19040017 = 14280013) B14280013
theorem B2640377 : Blo 1389514 2640377 := bstep (se 2 (by rfl) ⟨990141, by rfl⟩ : syracuseStep 2640377 = 1980283) B1980283
theorem B15026795 : Blo 1389514 15026795 := bstep (se 1 (by rfl) ⟨11270096, by rfl⟩ : syracuseStep 15026795 = 22540193) B22540193
theorem B48155269 : Blo 1389514 48155269 := bstep (se 4 (by rfl) ⟨4514556, by rfl⟩ : syracuseStep 48155269 = 9029113) B9029113
theorem B2640575 : Blo 1389514 2640575 := bstep (se 1 (by rfl) ⟨1980431, by rfl⟩ : syracuseStep 2640575 = 3960863) B3960863
theorem B3517577 : Blo 1389514 3517577 := bstep (se 2 (by rfl) ⟨1319091, by rfl⟩ : syracuseStep 3517577 = 2638183) B2638183
theorem B2346151 : Blo 1389514 2346151 := bstep (se 1 (by rfl) ⟨1759613, by rfl⟩ : syracuseStep 2346151 = 3519227) B3519227
theorem B2641319 : Blo 1389514 2641319 := bstep (se 1 (by rfl) ⟨1980989, by rfl⟩ : syracuseStep 2641319 = 3961979) B3961979
theorem B5279357 : Blo 1389514 5279357 := bstep (se 3 (by rfl) ⟨989879, by rfl⟩ : syracuseStep 5279357 = 1979759) B1979759
theorem B8572759 : Blo 1389514 8572759 := bstep (se 1 (by rfl) ⟨6429569, by rfl⟩ : syracuseStep 8572759 = 12859139) B12859139
theorem B4689791 : Blo 1389514 4689791 := bstep (se 1 (by rfl) ⟨3517343, by rfl⟩ : syracuseStep 4689791 = 7034687) B7034687
theorem B11882861 : Blo 1389514 11882861 := bstep (se 3 (by rfl) ⟨2228036, by rfl⟩ : syracuseStep 11882861 = 4456073) B4456073
theorem B2347771 : Blo 1389514 2347771 := bstep (se 1 (by rfl) ⟨1760828, by rfl⟩ : syracuseStep 2347771 = 3521657) B3521657
theorem B2085659 : Blo 1389514 2085659 := bstep (se 1 (by rfl) ⟨1564244, by rfl⟩ : syracuseStep 2085659 = 3128489) B3128489
theorem B3961705 : Blo 1389514 3961705 := bstep (se 2 (by rfl) ⟨1485639, by rfl⟩ : syracuseStep 3961705 = 2971279) B2971279
theorem B1389535 : Blo 1389514 1389535 := bstep (se 1 (by rfl) ⟨1042151, by rfl⟩ : syracuseStep 1389535 = 2084303) B2084303
theorem B7918559 : Blo 1389514 7918559 := bstep (se 1 (by rfl) ⟨5938919, by rfl⟩ : syracuseStep 7918559 = 11877839) B11877839
theorem B1389595 : Blo 1389514 1389595 := bstep (se 1 (by rfl) ⟨1042196, by rfl⟩ : syracuseStep 1389595 = 2084393) B2084393
theorem B11883611 : Blo 1389514 11883611 := bstep (se 1 (by rfl) ⟨8912708, by rfl⟩ : syracuseStep 11883611 = 17825417) B17825417
theorem B1389791 : Blo 1389514 1389791 := bstep (se 1 (by rfl) ⟨1042343, by rfl⟩ : syracuseStep 1389791 = 2084687) B2084687
theorem B7042301 : Blo 1389514 7042301 := bstep (se 3 (by rfl) ⟨1320431, by rfl⟩ : syracuseStep 7042301 = 2640863) B2640863
theorem B1389871 : Blo 1389514 1389871 := bstep (se 1 (by rfl) ⟨1042403, by rfl⟩ : syracuseStep 1389871 = 2084807) B2084807
theorem B1389927 : Blo 1389514 1389927 := bstep (se 1 (by rfl) ⟨1042445, by rfl⟩ : syracuseStep 1389927 = 2084891) B2084891
theorem B128374145 : Blo 1389514 128374145 := bstep (se 2 (by rfl) ⟨48140304, by rfl⟩ : syracuseStep 128374145 = 96280609) B96280609
theorem B2086313 : Blo 1389514 2086313 := bstep (se 2 (by rfl) ⟨782367, by rfl⟩ : syracuseStep 2086313 = 1564735) B1564735
theorem B2086367 : Blo 1389514 2086367 := bstep (se 1 (by rfl) ⟨1564775, by rfl⟩ : syracuseStep 2086367 = 3129551) B3129551
theorem B3012079 : Blo 1389514 3012079 := bstep (se 1 (by rfl) ⟨2259059, by rfl⟩ : syracuseStep 3012079 = 4518119) B4518119
theorem B1390111 : Blo 1389514 1390111 := bstep (se 1 (by rfl) ⟨1042583, by rfl⟩ : syracuseStep 1390111 = 2085167) B2085167
theorem B8910431 : Blo 1389514 8910431 := bstep (se 1 (by rfl) ⟨6682823, by rfl⟩ : syracuseStep 8910431 = 13365647) B13365647
theorem B1390183 : Blo 1389514 1390183 := bstep (se 1 (by rfl) ⟨1042637, by rfl⟩ : syracuseStep 1390183 = 2085275) B2085275
theorem B1390207 : Blo 1389514 1390207 := bstep (se 1 (by rfl) ⟨1042655, by rfl⟩ : syracuseStep 1390207 = 2085311) B2085311
theorem B171325115 : Blo 1389514 171325115 := bstep (se 1 (by rfl) ⟨128493836, by rfl⟩ : syracuseStep 171325115 = 256987673) B256987673
theorem B1390271 : Blo 1389514 1390271 := bstep (se 1 (by rfl) ⟨1042703, by rfl⟩ : syracuseStep 1390271 = 2085407) B2085407
theorem B4691681 : Blo 1389514 4691681 := bstep (se 2 (by rfl) ⟨1759380, by rfl⟩ : syracuseStep 4691681 = 3518761) B3518761
theorem B1390463 : Blo 1389514 1390463 := bstep (se 1 (by rfl) ⟨1042847, by rfl⟩ : syracuseStep 1390463 = 2085695) B2085695
theorem B2504639 : Blo 1389514 2504639 := bstep (se 1 (by rfl) ⟨1878479, by rfl⟩ : syracuseStep 2504639 = 3756959) B3756959
theorem B1390559 : Blo 1389514 1390559 := bstep (se 1 (by rfl) ⟨1042919, by rfl⟩ : syracuseStep 1390559 = 2085839) B2085839
theorem B101488625 : Blo 1389514 101488625 := bstep (se 2 (by rfl) ⟨38058234, by rfl⟩ : syracuseStep 101488625 = 76116469) B76116469
theorem B1390619 : Blo 1389514 1390619 := bstep (se 1 (by rfl) ⟨1042964, by rfl⟩ : syracuseStep 1390619 = 2085929) B2085929
theorem B1390639 : Blo 1389514 1390639 := bstep (se 1 (by rfl) ⟨1042979, by rfl⟩ : syracuseStep 1390639 = 2085959) B2085959
theorem B96295013 : Blo 1389514 96295013 := bstep (se 4 (by rfl) ⟨9027657, by rfl⟩ : syracuseStep 96295013 = 18055315) B18055315
theorem B5937295 : Blo 1389514 5937295 := bstep (se 1 (by rfl) ⟨4452971, by rfl⟩ : syracuseStep 5937295 = 8905943) B8905943
theorem B1390759 : Blo 1389514 1390759 := bstep (se 1 (by rfl) ⟨1043069, by rfl⟩ : syracuseStep 1390759 = 2086139) B2086139
theorem B10016939 : Blo 1389514 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B1390799 : Blo 1389514 1390799 := bstep (se 1 (by rfl) ⟨1043099, by rfl⟩ : syracuseStep 1390799 = 2086199) B2086199
theorem B10025299 : Blo 1389514 10025299 := bstep (se 1 (by rfl) ⟨7518974, by rfl⟩ : syracuseStep 10025299 = 15037949) B15037949
theorem B1391003 : Blo 1389514 1391003 := bstep (se 1 (by rfl) ⟨1043252, by rfl⟩ : syracuseStep 1391003 = 2086505) B2086505
theorem B4692383 : Blo 1389514 4692383 := bstep (se 1 (by rfl) ⟨3519287, by rfl⟩ : syracuseStep 4692383 = 7038575) B7038575
theorem B1391359 : Blo 1389514 1391359 := bstep (se 1 (by rfl) ⟨1043519, by rfl⟩ : syracuseStep 1391359 = 2087039) B2087039
theorem B7035659 : Blo 1389514 7035659 := bstep (se 1 (by rfl) ⟨5276744, by rfl⟩ : syracuseStep 7035659 = 10553489) B10553489
theorem B15833879 : Blo 1389514 15833879 := bstep (se 1 (by rfl) ⟨11875409, by rfl⟩ : syracuseStep 15833879 = 23750819) B23750819
theorem B1391423 : Blo 1389514 1391423 := bstep (se 1 (by rfl) ⟨1043567, by rfl⟩ : syracuseStep 1391423 = 2087135) B2087135
theorem B1391463 : Blo 1389514 1391463 := bstep (se 1 (by rfl) ⟨1043597, by rfl⟩ : syracuseStep 1391463 = 2087195) B2087195
theorem B17808605 : Blo 1389514 17808605 := bstep (se 3 (by rfl) ⟨3339113, by rfl⟩ : syracuseStep 17808605 = 6678227) B6678227
theorem B7044407 : Blo 1389514 7044407 := bstep (se 1 (by rfl) ⟨5283305, by rfl⟩ : syracuseStep 7044407 = 10566611) B10566611
theorem B1408559 : Blo 1389514 1408559 := bstep (se 1 (by rfl) ⟨1056419, by rfl⟩ : syracuseStep 1408559 = 2112839) B2112839
theorem B4693625 : Blo 1389514 4693625 := bstep (se 2 (by rfl) ⟨1760109, by rfl⟩ : syracuseStep 4693625 = 3520219) B3520219
theorem B4693679 : Blo 1389514 4693679 := bstep (se 1 (by rfl) ⟨3520259, by rfl⟩ : syracuseStep 4693679 = 7040519) B7040519
theorem B5349095 : Blo 1389514 5349095 := bstep (se 1 (by rfl) ⟨4011821, by rfl⟩ : syracuseStep 5349095 = 8023643) B8023643
theorem B25370567 : Blo 1389514 25370567 := bstep (se 1 (by rfl) ⟨19027925, by rfl⟩ : syracuseStep 25370567 = 38055851) B38055851
theorem B2818027 : Blo 1389514 2818027 := bstep (se 1 (by rfl) ⟨2113520, by rfl⟩ : syracuseStep 2818027 = 4227041) B4227041
theorem B16064507 : Blo 1389514 16064507 := bstep (se 1 (by rfl) ⟨12048380, by rfl⟩ : syracuseStep 16064507 = 24096761) B24096761
theorem B7921907 : Blo 1389514 7921907 := bstep (se 1 (by rfl) ⟨5941430, by rfl⟩ : syracuseStep 7921907 = 11882861) B11882861
theorem B2638099 : Blo 1389514 2638099 := bstep (se 1 (by rfl) ⟨1978574, by rfl⟩ : syracuseStep 2638099 = 3957149) B3957149
theorem B3342671 : Blo 1389514 3342671 := bstep (se 1 (by rfl) ⟨2507003, by rfl⟩ : syracuseStep 3342671 = 5014007) B5014007
theorem B3129695 : Blo 1389514 3129695 := bstep (se 1 (by rfl) ⟨2347271, by rfl⟩ : syracuseStep 3129695 = 4694543) B4694543
theorem B15024629 : Blo 1389514 15024629 := bstep (se 5 (by rfl) ⟨704279, by rfl⟩ : syracuseStep 15024629 = 1408559) B1408559
theorem B7922407 : Blo 1389514 7922407 := bstep (se 1 (by rfl) ⟨5941805, by rfl⟩ : syracuseStep 7922407 = 11883611) B11883611
theorem B4694867 : Blo 1389514 4694867 := bstep (se 1 (by rfl) ⟨3521150, by rfl⟩ : syracuseStep 4694867 = 7042301) B7042301
theorem B3130271 : Blo 1389514 3130271 := bstep (se 1 (by rfl) ⟨2347703, by rfl⟩ : syracuseStep 3130271 = 4695407) B4695407
theorem B85582763 : Blo 1389514 85582763 := bstep (se 1 (by rfl) ⟨64187072, by rfl⟩ : syracuseStep 85582763 = 128374145) B128374145
theorem B3130361 : Blo 1389514 3130361 := bstep (se 2 (by rfl) ⟨1173885, by rfl⟩ : syracuseStep 3130361 = 2347771) B2347771
theorem B3130415 : Blo 1389514 3130415 := bstep (se 1 (by rfl) ⟨2347811, by rfl⟩ : syracuseStep 3130415 = 4695623) B4695623
theorem B5940287 : Blo 1389514 5940287 := bstep (se 1 (by rfl) ⟨4455215, by rfl⟩ : syracuseStep 5940287 = 8910431) B8910431
theorem B67659083 : Blo 1389514 67659083 := bstep (se 1 (by rfl) ⟨50744312, by rfl⟩ : syracuseStep 67659083 = 101488625) B101488625
theorem B6677959 : Blo 1389514 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B10585673 : Blo 1389514 10585673 := bstep (se 2 (by rfl) ⟨3969627, by rfl⟩ : syracuseStep 10585673 = 7939255) B7939255
theorem B45721381 : Blo 1389514 45721381 := bstep (se 4 (by rfl) ⟨4286379, by rfl⟩ : syracuseStep 45721381 = 8572759) B8572759
theorem B4016105 : Blo 1389514 4016105 := bstep (se 2 (by rfl) ⟨1506039, by rfl⟩ : syracuseStep 4016105 = 3012079) B3012079
theorem B2345051 : Blo 1389514 2345051 := bstep (se 1 (by rfl) ⟨1758788, by rfl⟩ : syracuseStep 2345051 = 3517577) B3517577
theorem B11872403 : Blo 1389514 11872403 := bstep (se 1 (by rfl) ⟨8904302, by rfl⟩ : syracuseStep 11872403 = 17808605) B17808605
theorem B4696271 : Blo 1389514 4696271 := bstep (se 1 (by rfl) ⟨3522203, by rfl⟩ : syracuseStep 4696271 = 7044407) B7044407
theorem B3566063 : Blo 1389514 3566063 := bstep (se 1 (by rfl) ⟨2674547, by rfl⟩ : syracuseStep 3566063 = 5349095) B5349095
theorem B6679037 : Blo 1389514 6679037 := bstep (se 3 (by rfl) ⟨1252319, by rfl⟩ : syracuseStep 6679037 = 2504639) B2504639
theorem B10709671 : Blo 1389514 10709671 := bstep (se 1 (by rfl) ⟨8032253, by rfl⟩ : syracuseStep 10709671 = 16064507) B16064507
theorem B7916393 : Blo 1389514 7916393 := bstep (se 2 (by rfl) ⟨2968647, by rfl⟩ : syracuseStep 7916393 = 5937295) B5937295
theorem B21982373 : Blo 1389514 21982373 := bstep (se 4 (by rfl) ⟨2060847, by rfl⟩ : syracuseStep 21982373 = 4121695) B4121695
theorem B3517627 : Blo 1389514 3517627 := bstep (se 1 (by rfl) ⟨2638220, by rfl⟩ : syracuseStep 3517627 = 5276441) B5276441
theorem B3960019 : Blo 1389514 3960019 := bstep (se 1 (by rfl) ⟨2970014, by rfl⟩ : syracuseStep 3960019 = 5940029) B5940029
theorem B5279039 : Blo 1389514 5279039 := bstep (se 1 (by rfl) ⟨3959279, by rfl⟩ : syracuseStep 5279039 = 7918559) B7918559
theorem B114216743 : Blo 1389514 114216743 := bstep (se 1 (by rfl) ⟨85662557, by rfl⟩ : syracuseStep 114216743 = 171325115) B171325115
theorem B3960647 : Blo 1389514 3960647 := bstep (se 1 (by rfl) ⟨2970485, by rfl⟩ : syracuseStep 3960647 = 5940971) B5940971
theorem B7041005 : Blo 1389514 7041005 := bstep (se 3 (by rfl) ⟨1320188, by rfl⟩ : syracuseStep 7041005 = 2640377) B2640377
theorem B64196675 : Blo 1389514 64196675 := bstep (se 1 (by rfl) ⟨48147506, by rfl⟩ : syracuseStep 64196675 = 96295013) B96295013
theorem B4690439 : Blo 1389514 4690439 := bstep (se 1 (by rfl) ⟨3517829, by rfl⟩ : syracuseStep 4690439 = 7035659) B7035659
theorem B10555919 : Blo 1389514 10555919 := bstep (se 1 (by rfl) ⟨7916939, by rfl⟩ : syracuseStep 10555919 = 15833879) B15833879
theorem B3519571 : Blo 1389514 3519571 := bstep (se 1 (by rfl) ⟨2639678, by rfl⟩ : syracuseStep 3519571 = 5279357) B5279357
theorem B3126527 : Blo 1389514 3126527 := bstep (se 1 (by rfl) ⟨2344895, by rfl⟩ : syracuseStep 3126527 = 4689791) B4689791
theorem B16913711 : Blo 1389514 16913711 := bstep (se 1 (by rfl) ⟨12685283, by rfl⟩ : syracuseStep 16913711 = 25370567) B25370567
theorem B3757369 : Blo 1389514 3757369 := bstep (se 2 (by rfl) ⟨1409013, by rfl⟩ : syracuseStep 3757369 = 2818027) B2818027
theorem B2086271 : Blo 1389514 2086271 := bstep (se 1 (by rfl) ⟨1564703, by rfl⟩ : syracuseStep 2086271 = 3129407) B3129407
theorem B13367065 : Blo 1389514 13367065 := bstep (se 2 (by rfl) ⟨5012649, by rfl⟩ : syracuseStep 13367065 = 10025299) B10025299
theorem B1390439 : Blo 1389514 1390439 := bstep (se 1 (by rfl) ⟨1042829, by rfl⟩ : syracuseStep 1390439 = 2085659) B2085659
theorem B2086889 : Blo 1389514 2086889 := bstep (se 2 (by rfl) ⟨782583, by rfl⟩ : syracuseStep 2086889 = 1565167) B1565167
theorem B1759259 : Blo 1389514 1759259 := bstep (se 1 (by rfl) ⟨1319444, by rfl⟩ : syracuseStep 1759259 = 2638889) B2638889
theorem B2087033 : Blo 1389514 2087033 := bstep (se 2 (by rfl) ⟨782637, by rfl⟩ : syracuseStep 2087033 = 1565275) B1565275
theorem B2087087 : Blo 1389514 2087087 := bstep (se 1 (by rfl) ⟨1565315, by rfl⟩ : syracuseStep 2087087 = 3130631) B3130631
theorem B64207025 : Blo 1389514 64207025 := bstep (se 2 (by rfl) ⟨24077634, by rfl⟩ : syracuseStep 64207025 = 48155269) B48155269
theorem B1390875 : Blo 1389514 1390875 := bstep (se 1 (by rfl) ⟨1043156, by rfl⟩ : syracuseStep 1390875 = 2086313) B2086313
theorem B1390911 : Blo 1389514 1390911 := bstep (se 1 (by rfl) ⟨1043183, by rfl⟩ : syracuseStep 1390911 = 2086367) B2086367
theorem B7035335 : Blo 1389514 7035335 := bstep (se 1 (by rfl) ⟨5276501, by rfl⟩ : syracuseStep 7035335 = 10553003) B10553003
theorem B5282273 : Blo 1389514 5282273 := bstep (se 2 (by rfl) ⟨1980852, by rfl⟩ : syracuseStep 5282273 = 3961705) B3961705
theorem B3127787 : Blo 1389514 3127787 := bstep (se 1 (by rfl) ⟨2345840, by rfl⟩ : syracuseStep 3127787 = 4691681) B4691681
theorem B3128201 : Blo 1389514 3128201 := bstep (se 2 (by rfl) ⟨1173075, by rfl⟩ : syracuseStep 3128201 = 2346151) B2346151
theorem B3128255 : Blo 1389514 3128255 := bstep (se 1 (by rfl) ⟨2346191, by rfl⟩ : syracuseStep 3128255 = 4692383) B4692383
theorem B10017863 : Blo 1389514 10017863 := bstep (se 1 (by rfl) ⟨7513397, by rfl⟩ : syracuseStep 10017863 = 15026795) B15026795
theorem B1760383 : Blo 1389514 1760383 := bstep (se 1 (by rfl) ⟨1320287, by rfl⟩ : syracuseStep 1760383 = 2640575) B2640575
theorem B6774329 : Blo 1389514 6774329 := bstep (se 2 (by rfl) ⟨2540373, by rfl⟩ : syracuseStep 6774329 = 5080747) B5080747
theorem B1760879 : Blo 1389514 1760879 := bstep (se 1 (by rfl) ⟨1320659, by rfl⟩ : syracuseStep 1760879 = 2641319) B2641319
theorem B25386689 : Blo 1389514 25386689 := bstep (se 2 (by rfl) ⟨9520008, by rfl⟩ : syracuseStep 25386689 = 19040017) B19040017
theorem B3129083 : Blo 1389514 3129083 := bstep (se 1 (by rfl) ⟨2346812, by rfl⟩ : syracuseStep 3129083 = 4693625) B4693625
theorem B3129119 : Blo 1389514 3129119 := bstep (se 1 (by rfl) ⟨2346839, by rfl⟩ : syracuseStep 3129119 = 4693679) B4693679
theorem B2228447 : Blo 1389514 2228447 := bstep (se 1 (by rfl) ⟨1671335, by rfl⟩ : syracuseStep 2228447 = 3342671) B3342671
theorem B7037279 : Blo 1389514 7037279 := bstep (se 1 (by rfl) ⟨5277959, by rfl⟩ : syracuseStep 7037279 = 10555919) B10555919
theorem B3129911 : Blo 1389514 3129911 := bstep (se 1 (by rfl) ⟨2347433, by rfl⟩ : syracuseStep 3129911 = 4694867) B4694867
theorem B45106055 : Blo 1389514 45106055 := bstep (se 1 (by rfl) ⟨33829541, by rfl⟩ : syracuseStep 45106055 = 67659083) B67659083
theorem B14279561 : Blo 1389514 14279561 := bstep (se 2 (by rfl) ⟨5354835, by rfl⟩ : syracuseStep 14279561 = 10709671) B10709671
theorem B7914935 : Blo 1389514 7914935 := bstep (se 1 (by rfl) ⟨5936201, by rfl⟩ : syracuseStep 7914935 = 11872403) B11872403
theorem B42804683 : Blo 1389514 42804683 := bstep (se 1 (by rfl) ⟨32103512, by rfl⟩ : syracuseStep 42804683 = 64207025) B64207025
theorem B3130847 : Blo 1389514 3130847 := bstep (se 1 (by rfl) ⟨2348135, by rfl⟩ : syracuseStep 3130847 = 4696271) B4696271
theorem B4695677 : Blo 1389514 4695677 := bstep (se 3 (by rfl) ⟨880439, by rfl⟩ : syracuseStep 4695677 = 1760879) B1760879
theorem B5277595 : Blo 1389514 5277595 := bstep (se 1 (by rfl) ⟨3958196, by rfl⟩ : syracuseStep 5277595 = 7916393) B7916393
theorem B6678575 : Blo 1389514 6678575 := bstep (se 1 (by rfl) ⟨5008931, by rfl⟩ : syracuseStep 6678575 = 10017863) B10017863
theorem B4516219 : Blo 1389514 4516219 := bstep (se 1 (by rfl) ⟨3387164, by rfl⟩ : syracuseStep 4516219 = 6774329) B6774329
theorem B2640431 : Blo 1389514 2640431 := bstep (se 1 (by rfl) ⟨1980323, by rfl⟩ : syracuseStep 2640431 = 3960647) B3960647
theorem B42797783 : Blo 1389514 42797783 := bstep (se 1 (by rfl) ⟨32098337, by rfl⟩ : syracuseStep 42797783 = 64196675) B64196675
theorem B3517465 : Blo 1389514 3517465 := bstep (se 2 (by rfl) ⟨1319049, by rfl⟩ : syracuseStep 3517465 = 2638099) B2638099
theorem B3960191 : Blo 1389514 3960191 := bstep (se 1 (by rfl) ⟨2970143, by rfl⟩ : syracuseStep 3960191 = 5940287) B5940287
theorem B2084351 : Blo 1389514 2084351 := bstep (se 1 (by rfl) ⟨1563263, by rfl⟩ : syracuseStep 2084351 = 3126527) B3126527
theorem B11275807 : Blo 1389514 11275807 := bstep (se 1 (by rfl) ⟨8456855, by rfl⟩ : syracuseStep 11275807 = 16913711) B16913711
theorem B10563209 : Blo 1389514 10563209 := bstep (se 2 (by rfl) ⟨3961203, by rfl⟩ : syracuseStep 10563209 = 7922407) B7922407
theorem B7057115 : Blo 1389514 7057115 := bstep (se 1 (by rfl) ⟨5292836, by rfl⟩ : syracuseStep 7057115 = 10585673) B10585673
theorem B2347177 : Blo 1389514 2347177 := bstep (se 2 (by rfl) ⟨880191, by rfl⟩ : syracuseStep 2347177 = 1760383) B1760383
theorem B4690169 : Blo 1389514 4690169 := bstep (se 2 (by rfl) ⟨1758813, by rfl⟩ : syracuseStep 4690169 = 3517627) B3517627
theorem B5280025 : Blo 1389514 5280025 := bstep (se 2 (by rfl) ⟨1980009, by rfl⟩ : syracuseStep 5280025 = 3960019) B3960019
theorem B4690223 : Blo 1389514 4690223 := bstep (se 1 (by rfl) ⟨3517667, by rfl⟩ : syracuseStep 4690223 = 7035335) B7035335
theorem B2085191 : Blo 1389514 2085191 := bstep (se 1 (by rfl) ⟨1563893, by rfl⟩ : syracuseStep 2085191 = 3127787) B3127787
theorem B4452691 : Blo 1389514 4452691 := bstep (se 1 (by rfl) ⟨3339518, by rfl⟩ : syracuseStep 4452691 = 6679037) B6679037
theorem B5009825 : Blo 1389514 5009825 := bstep (se 2 (by rfl) ⟨1878684, by rfl⟩ : syracuseStep 5009825 = 3757369) B3757369
theorem B2085467 : Blo 1389514 2085467 := bstep (se 1 (by rfl) ⟨1564100, by rfl⟩ : syracuseStep 2085467 = 3128201) B3128201
theorem B2085503 : Blo 1389514 2085503 := bstep (se 1 (by rfl) ⟨1564127, by rfl⟩ : syracuseStep 2085503 = 3128255) B3128255
theorem B3519359 : Blo 1389514 3519359 := bstep (se 1 (by rfl) ⟨2639519, by rfl⟩ : syracuseStep 3519359 = 5279039) B5279039
theorem B17822753 : Blo 1389514 17822753 := bstep (se 2 (by rfl) ⟨6683532, by rfl⟩ : syracuseStep 17822753 = 13367065) B13367065
theorem B60961841 : Blo 1389514 60961841 := bstep (se 2 (by rfl) ⟨22860690, by rfl⟩ : syracuseStep 60961841 = 45721381) B45721381
theorem B2086055 : Blo 1389514 2086055 := bstep (se 1 (by rfl) ⟨1564541, by rfl⟩ : syracuseStep 2086055 = 3129083) B3129083
theorem B2086079 : Blo 1389514 2086079 := bstep (se 1 (by rfl) ⟨1564559, by rfl⟩ : syracuseStep 2086079 = 3129119) B3129119
theorem B4691357 : Blo 1389514 4691357 := bstep (se 3 (by rfl) ⟨879629, by rfl⟩ : syracuseStep 4691357 = 1759259) B1759259
theorem B5281271 : Blo 1389514 5281271 := bstep (se 1 (by rfl) ⟨3960953, by rfl⟩ : syracuseStep 5281271 = 7921907) B7921907
theorem B2086463 : Blo 1389514 2086463 := bstep (se 1 (by rfl) ⟨1564847, by rfl⟩ : syracuseStep 2086463 = 3129695) B3129695
theorem B10016419 : Blo 1389514 10016419 := bstep (se 1 (by rfl) ⟨7512314, by rfl⟩ : syracuseStep 10016419 = 15024629) B15024629
theorem B3126959 : Blo 1389514 3126959 := bstep (se 1 (by rfl) ⟨2345219, by rfl⟩ : syracuseStep 3126959 = 4690439) B4690439
theorem B2086847 : Blo 1389514 2086847 := bstep (se 1 (by rfl) ⟨1565135, by rfl⟩ : syracuseStep 2086847 = 3130271) B3130271
theorem B57055175 : Blo 1389514 57055175 := bstep (se 1 (by rfl) ⟨42791381, by rfl⟩ : syracuseStep 57055175 = 85582763) B85582763
theorem B2086907 : Blo 1389514 2086907 := bstep (se 1 (by rfl) ⟨1565180, by rfl⟩ : syracuseStep 2086907 = 3130361) B3130361
theorem B2086943 : Blo 1389514 2086943 := bstep (se 1 (by rfl) ⟨1565207, by rfl⟩ : syracuseStep 2086943 = 3130415) B3130415
theorem B1390847 : Blo 1389514 1390847 := bstep (se 1 (by rfl) ⟨1043135, by rfl⟩ : syracuseStep 1390847 = 2086271) B2086271
theorem B9509501 : Blo 1389514 9509501 := bstep (se 3 (by rfl) ⟨1783031, by rfl⟩ : syracuseStep 9509501 = 3566063) B3566063
theorem B1391259 : Blo 1389514 1391259 := bstep (se 1 (by rfl) ⟨1043444, by rfl⟩ : syracuseStep 1391259 = 2086889) B2086889
theorem B2677403 : Blo 1389514 2677403 := bstep (se 1 (by rfl) ⟨2008052, by rfl⟩ : syracuseStep 2677403 = 4016105) B4016105
theorem B1563367 : Blo 1389514 1563367 := bstep (se 1 (by rfl) ⟨1172525, by rfl⟩ : syracuseStep 1563367 = 2345051) B2345051
theorem B1391355 : Blo 1389514 1391355 := bstep (se 1 (by rfl) ⟨1043516, by rfl⟩ : syracuseStep 1391355 = 2087033) B2087033
theorem B4692761 : Blo 1389514 4692761 := bstep (se 2 (by rfl) ⟨1759785, by rfl⟩ : syracuseStep 4692761 = 3519571) B3519571
theorem B1391391 : Blo 1389514 1391391 := bstep (se 1 (by rfl) ⟨1043543, by rfl⟩ : syracuseStep 1391391 = 2087087) B2087087
theorem B3521515 : Blo 1389514 3521515 := bstep (se 1 (by rfl) ⟨2641136, by rfl⟩ : syracuseStep 3521515 = 5282273) B5282273
theorem B8903945 : Blo 1389514 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B14654915 : Blo 1389514 14654915 := bstep (se 1 (by rfl) ⟨10991186, by rfl⟩ : syracuseStep 14654915 = 21982373) B21982373
theorem B16924459 : Blo 1389514 16924459 := bstep (se 1 (by rfl) ⟨12693344, by rfl⟩ : syracuseStep 16924459 = 25386689) B25386689
theorem B76144495 : Blo 1389514 76144495 := bstep (se 1 (by rfl) ⟨57108371, by rfl⟩ : syracuseStep 76144495 = 114216743) B114216743
theorem B4694003 : Blo 1389514 4694003 := bstep (se 1 (by rfl) ⟨3520502, by rfl⟩ : syracuseStep 4694003 = 7041005) B7041005
theorem B3129569 : Blo 1389514 3129569 := bstep (se 2 (by rfl) ⟨1173588, by rfl⟩ : syracuseStep 3129569 = 2347177) B2347177
theorem B9519707 : Blo 1389514 9519707 := bstep (se 1 (by rfl) ⟨7139780, by rfl⟩ : syracuseStep 9519707 = 14279561) B14279561
theorem B40641227 : Blo 1389514 40641227 := bstep (se 1 (by rfl) ⟨30480920, by rfl⟩ : syracuseStep 40641227 = 60961841) B60961841
theorem B5276623 : Blo 1389514 5276623 := bstep (se 1 (by rfl) ⟨3957467, by rfl⟩ : syracuseStep 5276623 = 7914935) B7914935
theorem B3130451 : Blo 1389514 3130451 := bstep (se 1 (by rfl) ⟨2347838, by rfl⟩ : syracuseStep 3130451 = 4695677) B4695677
theorem B38036783 : Blo 1389514 38036783 := bstep (se 1 (by rfl) ⟨28527587, by rfl⟩ : syracuseStep 38036783 = 57055175) B57055175
theorem B4695353 : Blo 1389514 4695353 := bstep (se 2 (by rfl) ⟨1760757, by rfl⟩ : syracuseStep 4695353 = 3521515) B3521515
theorem B24086501 : Blo 1389514 24086501 := bstep (se 4 (by rfl) ⟨2258109, by rfl⟩ : syracuseStep 24086501 = 4516219) B4516219
theorem B15034409 : Blo 1389514 15034409 := bstep (se 2 (by rfl) ⟨5637903, by rfl⟩ : syracuseStep 15034409 = 11275807) B11275807
theorem B13355225 : Blo 1389514 13355225 := bstep (se 2 (by rfl) ⟨5008209, by rfl⟩ : syracuseStep 13355225 = 10016419) B10016419
theorem B2640127 : Blo 1389514 2640127 := bstep (se 1 (by rfl) ⟨1980095, by rfl⟩ : syracuseStep 2640127 = 3960191) B3960191
theorem B4704743 : Blo 1389514 4704743 := bstep (se 1 (by rfl) ⟨3528557, by rfl⟩ : syracuseStep 4704743 = 7057115) B7057115
theorem B101525993 : Blo 1389514 101525993 := bstep (se 2 (by rfl) ⟨38072247, by rfl⟩ : syracuseStep 101525993 = 76144495) B76144495
theorem B1485631 : Blo 1389514 1485631 := bstep (se 1 (by rfl) ⟨1114223, by rfl⟩ : syracuseStep 1485631 = 2228447) B2228447
theorem B7040033 : Blo 1389514 7040033 := bstep (se 2 (by rfl) ⟨2640012, by rfl⟩ : syracuseStep 7040033 = 5280025) B5280025
theorem B2346239 : Blo 1389514 2346239 := bstep (se 1 (by rfl) ⟨1759679, by rfl⟩ : syracuseStep 2346239 = 3519359) B3519359
theorem B11881835 : Blo 1389514 11881835 := bstep (se 1 (by rfl) ⟨8911376, by rfl⟩ : syracuseStep 11881835 = 17822753) B17822753
theorem B28536455 : Blo 1389514 28536455 := bstep (se 1 (by rfl) ⟨21402341, by rfl⟩ : syracuseStep 28536455 = 42804683) B42804683
theorem B2084489 : Blo 1389514 2084489 := bstep (se 2 (by rfl) ⟨781683, by rfl⟩ : syracuseStep 2084489 = 1563367) B1563367
theorem B2084639 : Blo 1389514 2084639 := bstep (se 1 (by rfl) ⟨1563479, by rfl⟩ : syracuseStep 2084639 = 3126959) B3126959
theorem B4452383 : Blo 1389514 4452383 := bstep (se 1 (by rfl) ⟨3339287, by rfl⟩ : syracuseStep 4452383 = 6678575) B6678575
theorem B4689953 : Blo 1389514 4689953 := bstep (se 2 (by rfl) ⟨1758732, by rfl⟩ : syracuseStep 4689953 = 3517465) B3517465
theorem B5935963 : Blo 1389514 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B9769943 : Blo 1389514 9769943 := bstep (se 1 (by rfl) ⟨7327457, by rfl⟩ : syracuseStep 9769943 = 14654915) B14654915
theorem B1389567 : Blo 1389514 1389567 := bstep (se 1 (by rfl) ⟨1042175, by rfl⟩ : syracuseStep 1389567 = 2084351) B2084351
theorem B22565945 : Blo 1389514 22565945 := bstep (se 2 (by rfl) ⟨8462229, by rfl⟩ : syracuseStep 22565945 = 16924459) B16924459
theorem B7042139 : Blo 1389514 7042139 := bstep (se 1 (by rfl) ⟨5281604, by rfl⟩ : syracuseStep 7042139 = 10563209) B10563209
theorem B3126779 : Blo 1389514 3126779 := bstep (se 1 (by rfl) ⟨2345084, by rfl⟩ : syracuseStep 3126779 = 4690169) B4690169
theorem B3126815 : Blo 1389514 3126815 := bstep (se 1 (by rfl) ⟨2345111, by rfl⟩ : syracuseStep 3126815 = 4690223) B4690223
theorem B1390127 : Blo 1389514 1390127 := bstep (se 1 (by rfl) ⟨1042595, by rfl⟩ : syracuseStep 1390127 = 2085191) B2085191
theorem B4691519 : Blo 1389514 4691519 := bstep (se 1 (by rfl) ⟨3518639, by rfl⟩ : syracuseStep 4691519 = 7037279) B7037279
theorem B3339883 : Blo 1389514 3339883 := bstep (se 1 (by rfl) ⟨2504912, by rfl⟩ : syracuseStep 3339883 = 5009825) B5009825
theorem B2086607 : Blo 1389514 2086607 := bstep (se 1 (by rfl) ⟨1564955, by rfl⟩ : syracuseStep 2086607 = 3129911) B3129911
theorem B1390311 : Blo 1389514 1390311 := bstep (se 1 (by rfl) ⟨1042733, by rfl⟩ : syracuseStep 1390311 = 2085467) B2085467
theorem B1390335 : Blo 1389514 1390335 := bstep (se 1 (by rfl) ⟨1042751, by rfl⟩ : syracuseStep 1390335 = 2085503) B2085503
theorem B5936921 : Blo 1389514 5936921 := bstep (se 2 (by rfl) ⟨2226345, by rfl⟩ : syracuseStep 5936921 = 4452691) B4452691
theorem B30070703 : Blo 1389514 30070703 := bstep (se 1 (by rfl) ⟨22553027, by rfl⟩ : syracuseStep 30070703 = 45106055) B45106055
theorem B1390703 : Blo 1389514 1390703 := bstep (se 1 (by rfl) ⟨1043027, by rfl⟩ : syracuseStep 1390703 = 2086055) B2086055
theorem B1390719 : Blo 1389514 1390719 := bstep (se 1 (by rfl) ⟨1043039, by rfl⟩ : syracuseStep 1390719 = 2086079) B2086079
theorem B3127571 : Blo 1389514 3127571 := bstep (se 1 (by rfl) ⟨2345678, by rfl⟩ : syracuseStep 3127571 = 4691357) B4691357
theorem B2087231 : Blo 1389514 2087231 := bstep (se 1 (by rfl) ⟨1565423, by rfl⟩ : syracuseStep 2087231 = 3130847) B3130847
theorem B3520847 : Blo 1389514 3520847 := bstep (se 1 (by rfl) ⟨2640635, by rfl⟩ : syracuseStep 3520847 = 5281271) B5281271
theorem B1390975 : Blo 1389514 1390975 := bstep (se 1 (by rfl) ⟨1043231, by rfl⟩ : syracuseStep 1390975 = 2086463) B2086463
theorem B1391231 : Blo 1389514 1391231 := bstep (se 1 (by rfl) ⟨1043423, by rfl⟩ : syracuseStep 1391231 = 2086847) B2086847
theorem B1391271 : Blo 1389514 1391271 := bstep (se 1 (by rfl) ⟨1043453, by rfl⟩ : syracuseStep 1391271 = 2086907) B2086907
theorem B1391295 : Blo 1389514 1391295 := bstep (se 1 (by rfl) ⟨1043471, by rfl⟩ : syracuseStep 1391295 = 2086943) B2086943
theorem B1760287 : Blo 1389514 1760287 := bstep (se 1 (by rfl) ⟨1320215, by rfl⟩ : syracuseStep 1760287 = 2640431) B2640431
theorem B6339667 : Blo 1389514 6339667 := bstep (se 1 (by rfl) ⟨4754750, by rfl⟩ : syracuseStep 6339667 = 9509501) B9509501
theorem B1784935 : Blo 1389514 1784935 := bstep (se 1 (by rfl) ⟨1338701, by rfl⟩ : syracuseStep 1784935 = 2677403) B2677403
theorem B28531855 : Blo 1389514 28531855 := bstep (se 1 (by rfl) ⟨21398891, by rfl⟩ : syracuseStep 28531855 = 42797783) B42797783
theorem B3128507 : Blo 1389514 3128507 := bstep (se 1 (by rfl) ⟨2346380, by rfl⟩ : syracuseStep 3128507 = 4692761) B4692761
theorem B3129335 : Blo 1389514 3129335 := bstep (se 1 (by rfl) ⟨2347001, by rfl⟩ : syracuseStep 3129335 = 4694003) B4694003
theorem B7036793 : Blo 1389514 7036793 := bstep (se 2 (by rfl) ⟨2638797, by rfl⟩ : syracuseStep 7036793 = 5277595) B5277595
theorem B9519653 : Blo 1389514 9519653 := bstep (se 4 (by rfl) ⟨892467, by rfl⟩ : syracuseStep 9519653 = 1784935) B1784935
theorem B6513295 : Blo 1389514 6513295 := bstep (se 1 (by rfl) ⟨4884971, by rfl⟩ : syracuseStep 6513295 = 9769943) B9769943
theorem B4694759 : Blo 1389514 4694759 := bstep (se 1 (by rfl) ⟨3521069, by rfl⟩ : syracuseStep 4694759 = 7042139) B7042139
theorem B3130235 : Blo 1389514 3130235 := bstep (se 1 (by rfl) ⟨2347676, by rfl⟩ : syracuseStep 3130235 = 4695353) B4695353
theorem B7914617 : Blo 1389514 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B3957947 : Blo 1389514 3957947 := bstep (se 1 (by rfl) ⟨2968460, by rfl⟩ : syracuseStep 3957947 = 5936921) B5936921
theorem B16057667 : Blo 1389514 16057667 := bstep (se 1 (by rfl) ⟨12043250, by rfl⟩ : syracuseStep 16057667 = 24086501) B24086501
theorem B67683995 : Blo 1389514 67683995 := bstep (se 1 (by rfl) ⟨50762996, by rfl⟩ : syracuseStep 67683995 = 101525993) B101525993
theorem B7923365 : Blo 1389514 7923365 := bstep (se 4 (by rfl) ⟨742815, by rfl⟩ : syracuseStep 7923365 = 1485631) B1485631
theorem B19024303 : Blo 1389514 19024303 := bstep (se 1 (by rfl) ⟨14268227, by rfl⟩ : syracuseStep 19024303 = 28536455) B28536455
theorem B2968255 : Blo 1389514 2968255 := bstep (se 1 (by rfl) ⟨2226191, by rfl⟩ : syracuseStep 2968255 = 4452383) B4452383
theorem B27094151 : Blo 1389514 27094151 := bstep (se 1 (by rfl) ⟨20320613, by rfl⟩ : syracuseStep 27094151 = 40641227) B40641227
theorem B15043963 : Blo 1389514 15043963 := bstep (se 1 (by rfl) ⟨11282972, by rfl⟩ : syracuseStep 15043963 = 22565945) B22565945
theorem B25357855 : Blo 1389514 25357855 := bstep (se 1 (by rfl) ⟨19018391, by rfl⟩ : syracuseStep 25357855 = 38036783) B38036783
theorem B2084519 : Blo 1389514 2084519 := bstep (se 1 (by rfl) ⟨1563389, by rfl⟩ : syracuseStep 2084519 = 3126779) B3126779
theorem B2084543 : Blo 1389514 2084543 := bstep (se 1 (by rfl) ⟨1563407, by rfl⟩ : syracuseStep 2084543 = 3126815) B3126815
theorem B10022939 : Blo 1389514 10022939 := bstep (se 1 (by rfl) ⟨7517204, by rfl⟩ : syracuseStep 10022939 = 15034409) B15034409
theorem B2347049 : Blo 1389514 2347049 := bstep (se 2 (by rfl) ⟨880143, by rfl⟩ : syracuseStep 2347049 = 1760287) B1760287
theorem B2085047 : Blo 1389514 2085047 := bstep (se 1 (by rfl) ⟨1563785, by rfl⟩ : syracuseStep 2085047 = 3127571) B3127571
theorem B2347231 : Blo 1389514 2347231 := bstep (se 1 (by rfl) ⟨1760423, by rfl⟩ : syracuseStep 2347231 = 3520847) B3520847
theorem B2085671 : Blo 1389514 2085671 := bstep (se 1 (by rfl) ⟨1564253, by rfl⟩ : syracuseStep 2085671 = 3128507) B3128507
theorem B4453177 : Blo 1389514 4453177 := bstep (se 2 (by rfl) ⟨1669941, by rfl⟩ : syracuseStep 4453177 = 3339883) B3339883
theorem B1389659 : Blo 1389514 1389659 := bstep (se 1 (by rfl) ⟨1042244, by rfl⟩ : syracuseStep 1389659 = 2084489) B2084489
theorem B80188541 : Blo 1389514 80188541 := bstep (se 3 (by rfl) ⟨15035351, by rfl⟩ : syracuseStep 80188541 = 30070703) B30070703
theorem B1389759 : Blo 1389514 1389759 := bstep (se 1 (by rfl) ⟨1042319, by rfl⟩ : syracuseStep 1389759 = 2084639) B2084639
theorem B4691195 : Blo 1389514 4691195 := bstep (se 1 (by rfl) ⟨3518396, by rfl⟩ : syracuseStep 4691195 = 7036793) B7036793
theorem B2086223 : Blo 1389514 2086223 := bstep (se 1 (by rfl) ⟨1564667, by rfl⟩ : syracuseStep 2086223 = 3129335) B3129335
theorem B3126635 : Blo 1389514 3126635 := bstep (se 1 (by rfl) ⟨2344976, by rfl⟩ : syracuseStep 3126635 = 4689953) B4689953
theorem B2086379 : Blo 1389514 2086379 := bstep (se 1 (by rfl) ⟨1564784, by rfl⟩ : syracuseStep 2086379 = 3129569) B3129569
theorem B3520169 : Blo 1389514 3520169 := bstep (se 2 (by rfl) ⟨1320063, by rfl⟩ : syracuseStep 3520169 = 2640127) B2640127
theorem B2086967 : Blo 1389514 2086967 := bstep (se 1 (by rfl) ⟨1565225, by rfl⟩ : syracuseStep 2086967 = 3130451) B3130451
theorem B3127679 : Blo 1389514 3127679 := bstep (se 1 (by rfl) ⟨2345759, by rfl⟩ : syracuseStep 3127679 = 4691519) B4691519
theorem B1391071 : Blo 1389514 1391071 := bstep (se 1 (by rfl) ⟨1043303, by rfl⟩ : syracuseStep 1391071 = 2086607) B2086607
theorem B7035497 : Blo 1389514 7035497 := bstep (se 2 (by rfl) ⟨2638311, by rfl⟩ : syracuseStep 7035497 = 5276623) B5276623
theorem B8452889 : Blo 1389514 8452889 := bstep (se 2 (by rfl) ⟨3169833, by rfl⟩ : syracuseStep 8452889 = 6339667) B6339667
theorem B8903483 : Blo 1389514 8903483 := bstep (se 1 (by rfl) ⟨6677612, by rfl⟩ : syracuseStep 8903483 = 13355225) B13355225
theorem B38042473 : Blo 1389514 38042473 := bstep (se 2 (by rfl) ⟨14265927, by rfl⟩ : syracuseStep 38042473 = 28531855) B28531855
theorem B1391487 : Blo 1389514 1391487 := bstep (se 1 (by rfl) ⟨1043615, by rfl⟩ : syracuseStep 1391487 = 2087231) B2087231
theorem B25385885 : Blo 1389514 25385885 := bstep (se 3 (by rfl) ⟨4759853, by rfl⟩ : syracuseStep 25385885 = 9519707) B9519707
theorem B3136495 : Blo 1389514 3136495 := bstep (se 1 (by rfl) ⟨2352371, by rfl⟩ : syracuseStep 3136495 = 4704743) B4704743
theorem B4693355 : Blo 1389514 4693355 := bstep (se 1 (by rfl) ⟨3520016, by rfl⟩ : syracuseStep 4693355 = 7040033) B7040033
theorem B1564159 : Blo 1389514 1564159 := bstep (se 1 (by rfl) ⟨1173119, by rfl⟩ : syracuseStep 1564159 = 2346239) B2346239
theorem B7921223 : Blo 1389514 7921223 := bstep (se 1 (by rfl) ⟨5940917, by rfl⟩ : syracuseStep 7921223 = 11881835) B11881835
theorem B1564699 : Blo 1389514 1564699 := bstep (se 1 (by rfl) ⟨1173524, by rfl⟩ : syracuseStep 1564699 = 2347049) B2347049
theorem B3129641 : Blo 1389514 3129641 := bstep (se 2 (by rfl) ⟨1173615, by rfl⟩ : syracuseStep 3129641 = 2347231) B2347231
theorem B3129839 : Blo 1389514 3129839 := bstep (se 1 (by rfl) ⟨2347379, by rfl⟩ : syracuseStep 3129839 = 4694759) B4694759
theorem B5276411 : Blo 1389514 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B2638631 : Blo 1389514 2638631 := bstep (se 1 (by rfl) ⟨1978973, by rfl⟩ : syracuseStep 2638631 = 3957947) B3957947
theorem B3957673 : Blo 1389514 3957673 := bstep (se 2 (by rfl) ⟨1484127, by rfl⟩ : syracuseStep 3957673 = 2968255) B2968255
theorem B45122663 : Blo 1389514 45122663 := bstep (se 1 (by rfl) ⟨33841997, by rfl⟩ : syracuseStep 45122663 = 67683995) B67683995
theorem B33810473 : Blo 1389514 33810473 := bstep (se 2 (by rfl) ⟨12678927, by rfl⟩ : syracuseStep 33810473 = 25357855) B25357855
theorem B25365737 : Blo 1389514 25365737 := bstep (se 2 (by rfl) ⟨9512151, by rfl⟩ : syracuseStep 25365737 = 19024303) B19024303
theorem B2084423 : Blo 1389514 2084423 := bstep (se 1 (by rfl) ⟨1563317, by rfl⟩ : syracuseStep 2084423 = 3126635) B3126635
theorem B2346779 : Blo 1389514 2346779 := bstep (se 1 (by rfl) ⟨1760084, by rfl⟩ : syracuseStep 2346779 = 3520169) B3520169
theorem B4181993 : Blo 1389514 4181993 := bstep (se 2 (by rfl) ⟨1568247, by rfl⟩ : syracuseStep 4181993 = 3136495) B3136495
theorem B2085119 : Blo 1389514 2085119 := bstep (se 1 (by rfl) ⟨1563839, by rfl⟩ : syracuseStep 2085119 = 3127679) B3127679
theorem B4690331 : Blo 1389514 4690331 := bstep (se 1 (by rfl) ⟨3517748, by rfl⟩ : syracuseStep 4690331 = 7035497) B7035497
theorem B20058617 : Blo 1389514 20058617 := bstep (se 2 (by rfl) ⟨7521981, by rfl⟩ : syracuseStep 20058617 = 15043963) B15043963
theorem B5935655 : Blo 1389514 5935655 := bstep (se 1 (by rfl) ⟨4451741, by rfl⟩ : syracuseStep 5935655 = 8903483) B8903483
theorem B2085545 : Blo 1389514 2085545 := bstep (se 2 (by rfl) ⟨782079, by rfl⟩ : syracuseStep 2085545 = 1564159) B1564159
theorem B5280815 : Blo 1389514 5280815 := bstep (se 1 (by rfl) ⟨3960611, by rfl⟩ : syracuseStep 5280815 = 7921223) B7921223
theorem B1389679 : Blo 1389514 1389679 := bstep (se 1 (by rfl) ⟨1042259, by rfl⟩ : syracuseStep 1389679 = 2084519) B2084519
theorem B1389695 : Blo 1389514 1389695 := bstep (se 1 (by rfl) ⟨1042271, by rfl⟩ : syracuseStep 1389695 = 2084543) B2084543
theorem B6681959 : Blo 1389514 6681959 := bstep (se 1 (by rfl) ⟨5011469, by rfl⟩ : syracuseStep 6681959 = 10022939) B10022939
theorem B1390031 : Blo 1389514 1390031 := bstep (se 1 (by rfl) ⟨1042523, by rfl⟩ : syracuseStep 1390031 = 2085047) B2085047
theorem B6346435 : Blo 1389514 6346435 := bstep (se 1 (by rfl) ⟨4759826, by rfl⟩ : syracuseStep 6346435 = 9519653) B9519653
theorem B1390447 : Blo 1389514 1390447 := bstep (se 1 (by rfl) ⟨1042835, by rfl⟩ : syracuseStep 1390447 = 2085671) B2085671
theorem B2086823 : Blo 1389514 2086823 := bstep (se 1 (by rfl) ⟨1565117, by rfl⟩ : syracuseStep 2086823 = 3130235) B3130235
theorem B53459027 : Blo 1389514 53459027 := bstep (se 1 (by rfl) ⟨40094270, by rfl⟩ : syracuseStep 53459027 = 80188541) B80188541
theorem B3127463 : Blo 1389514 3127463 := bstep (se 1 (by rfl) ⟨2345597, by rfl⟩ : syracuseStep 3127463 = 4691195) B4691195
theorem B10705111 : Blo 1389514 10705111 := bstep (se 1 (by rfl) ⟨8028833, by rfl⟩ : syracuseStep 10705111 = 16057667) B16057667
theorem B1390815 : Blo 1389514 1390815 := bstep (se 1 (by rfl) ⟨1043111, by rfl⟩ : syracuseStep 1390815 = 2086223) B2086223
theorem B1390919 : Blo 1389514 1390919 := bstep (se 1 (by rfl) ⟨1043189, by rfl⟩ : syracuseStep 1390919 = 2086379) B2086379
theorem B5937569 : Blo 1389514 5937569 := bstep (se 2 (by rfl) ⟨2226588, by rfl⟩ : syracuseStep 5937569 = 4453177) B4453177
theorem B5282243 : Blo 1389514 5282243 := bstep (se 1 (by rfl) ⟨3961682, by rfl⟩ : syracuseStep 5282243 = 7923365) B7923365
theorem B50723297 : Blo 1389514 50723297 := bstep (se 2 (by rfl) ⟨19021236, by rfl⟩ : syracuseStep 50723297 = 38042473) B38042473
theorem B555801173 : Blo 1389514 555801173 := bstep (se 8 (by rfl) ⟨3256647, by rfl⟩ : syracuseStep 555801173 = 6513295) B6513295
theorem B1391311 : Blo 1389514 1391311 := bstep (se 1 (by rfl) ⟨1043483, by rfl⟩ : syracuseStep 1391311 = 2086967) B2086967
theorem B5635259 : Blo 1389514 5635259 := bstep (se 1 (by rfl) ⟨4226444, by rfl⟩ : syracuseStep 5635259 = 8452889) B8452889
theorem B16923923 : Blo 1389514 16923923 := bstep (se 1 (by rfl) ⟨12692942, by rfl⟩ : syracuseStep 16923923 = 25385885) B25385885
theorem B18062767 : Blo 1389514 18062767 := bstep (se 1 (by rfl) ⟨13547075, by rfl⟩ : syracuseStep 18062767 = 27094151) B27094151
theorem B3128903 : Blo 1389514 3128903 := bstep (se 1 (by rfl) ⟨2346677, by rfl⟩ : syracuseStep 3128903 = 4693355) B4693355
theorem B90161261 : Blo 1389514 90161261 := bstep (se 3 (by rfl) ⟨16905236, by rfl⟩ : syracuseStep 90161261 = 33810473) B33810473
theorem B3957103 : Blo 1389514 3957103 := bstep (se 1 (by rfl) ⟨2967827, by rfl⟩ : syracuseStep 3957103 = 5935655) B5935655
theorem B67641965 : Blo 1389514 67641965 := bstep (se 3 (by rfl) ⟨12682868, by rfl⟩ : syracuseStep 67641965 = 25365737) B25365737
theorem B30081775 : Blo 1389514 30081775 := bstep (se 1 (by rfl) ⟨22561331, by rfl⟩ : syracuseStep 30081775 = 45122663) B45122663
theorem B5276897 : Blo 1389514 5276897 := bstep (se 2 (by rfl) ⟨1978836, by rfl⟩ : syracuseStep 5276897 = 3957673) B3957673
theorem B3958379 : Blo 1389514 3958379 := bstep (se 1 (by rfl) ⟨2968784, by rfl⟩ : syracuseStep 3958379 = 5937569) B5937569
theorem B370534115 : Blo 1389514 370534115 := bstep (se 1 (by rfl) ⟨277900586, by rfl⟩ : syracuseStep 370534115 = 555801173) B555801173
theorem B11282615 : Blo 1389514 11282615 := bstep (se 1 (by rfl) ⟨8461961, by rfl⟩ : syracuseStep 11282615 = 16923923) B16923923
theorem B2787995 : Blo 1389514 2787995 := bstep (se 1 (by rfl) ⟨2090996, by rfl⟩ : syracuseStep 2787995 = 4181993) B4181993
theorem B13372411 : Blo 1389514 13372411 := bstep (se 1 (by rfl) ⟨10029308, by rfl⟩ : syracuseStep 13372411 = 20058617) B20058617
theorem B3517607 : Blo 1389514 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B57093925 : Blo 1389514 57093925 := bstep (se 4 (by rfl) ⟨5352555, by rfl⟩ : syracuseStep 57093925 = 10705111) B10705111
theorem B35639351 : Blo 1389514 35639351 := bstep (se 1 (by rfl) ⟨26729513, by rfl⟩ : syracuseStep 35639351 = 53459027) B53459027
theorem B2084975 : Blo 1389514 2084975 := bstep (se 1 (by rfl) ⟨1563731, by rfl⟩ : syracuseStep 2084975 = 3127463) B3127463
theorem B3756839 : Blo 1389514 3756839 := bstep (se 1 (by rfl) ⟨2817629, by rfl⟩ : syracuseStep 3756839 = 5635259) B5635259
theorem B1389615 : Blo 1389514 1389615 := bstep (se 1 (by rfl) ⟨1042211, by rfl⟩ : syracuseStep 1389615 = 2084423) B2084423
theorem B2085935 : Blo 1389514 2085935 := bstep (se 1 (by rfl) ⟨1564451, by rfl⟩ : syracuseStep 2085935 = 3128903) B3128903
theorem B2086265 : Blo 1389514 2086265 := bstep (se 2 (by rfl) ⟨782349, by rfl⟩ : syracuseStep 2086265 = 1564699) B1564699
theorem B1390079 : Blo 1389514 1390079 := bstep (se 1 (by rfl) ⟨1042559, by rfl⟩ : syracuseStep 1390079 = 2085119) B2085119
theorem B2086427 : Blo 1389514 2086427 := bstep (se 1 (by rfl) ⟨1564820, by rfl⟩ : syracuseStep 2086427 = 3129641) B3129641
theorem B3126887 : Blo 1389514 3126887 := bstep (se 1 (by rfl) ⟨2345165, by rfl⟩ : syracuseStep 3126887 = 4690331) B4690331
theorem B2086559 : Blo 1389514 2086559 := bstep (se 1 (by rfl) ⟨1564919, by rfl⟩ : syracuseStep 2086559 = 3129839) B3129839
theorem B1390363 : Blo 1389514 1390363 := bstep (se 1 (by rfl) ⟨1042772, by rfl⟩ : syracuseStep 1390363 = 2085545) B2085545
theorem B1759087 : Blo 1389514 1759087 := bstep (se 1 (by rfl) ⟨1319315, by rfl⟩ : syracuseStep 1759087 = 2638631) B2638631
theorem B3520543 : Blo 1389514 3520543 := bstep (se 1 (by rfl) ⟨2640407, by rfl⟩ : syracuseStep 3520543 = 5280815) B5280815
theorem B4454639 : Blo 1389514 4454639 := bstep (se 1 (by rfl) ⟨3340979, by rfl⟩ : syracuseStep 4454639 = 6681959) B6681959
theorem B1391215 : Blo 1389514 1391215 := bstep (se 1 (by rfl) ⟨1043411, by rfl⟩ : syracuseStep 1391215 = 2086823) B2086823
theorem B3521495 : Blo 1389514 3521495 := bstep (se 1 (by rfl) ⟨2641121, by rfl⟩ : syracuseStep 3521495 = 5282243) B5282243
theorem B33815531 : Blo 1389514 33815531 := bstep (se 1 (by rfl) ⟨25361648, by rfl⟩ : syracuseStep 33815531 = 50723297) B50723297
theorem B24083689 : Blo 1389514 24083689 := bstep (se 2 (by rfl) ⟨9031383, by rfl⟩ : syracuseStep 24083689 = 18062767) B18062767
theorem B8461913 : Blo 1389514 8461913 := bstep (se 2 (by rfl) ⟨3173217, by rfl⟩ : syracuseStep 8461913 = 6346435) B6346435
theorem B1564519 : Blo 1389514 1564519 := bstep (se 1 (by rfl) ⟨1173389, by rfl⟩ : syracuseStep 1564519 = 2346779) B2346779
theorem B4694057 : Blo 1389514 4694057 := bstep (se 2 (by rfl) ⟨1760271, by rfl⟩ : syracuseStep 4694057 = 3520543) B3520543
theorem B5276137 : Blo 1389514 5276137 := bstep (se 2 (by rfl) ⟨1978551, by rfl⟩ : syracuseStep 5276137 = 3957103) B3957103
theorem B40109033 : Blo 1389514 40109033 := bstep (se 2 (by rfl) ⟨15040887, by rfl⟩ : syracuseStep 40109033 = 30081775) B30081775
theorem B2638919 : Blo 1389514 2638919 := bstep (se 1 (by rfl) ⟨1979189, by rfl⟩ : syracuseStep 2638919 = 3958379) B3958379
theorem B247022743 : Blo 1389514 247022743 := bstep (se 1 (by rfl) ⟨185267057, by rfl⟩ : syracuseStep 247022743 = 370534115) B370534115
theorem B7521743 : Blo 1389514 7521743 := bstep (se 1 (by rfl) ⟨5641307, by rfl⟩ : syracuseStep 7521743 = 11282615) B11282615
theorem B2345071 : Blo 1389514 2345071 := bstep (se 1 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 2345071 = 3517607) B3517607
theorem B2345449 : Blo 1389514 2345449 := bstep (se 2 (by rfl) ⟨879543, by rfl⟩ : syracuseStep 2345449 = 1759087) B1759087
theorem B23759567 : Blo 1389514 23759567 := bstep (se 1 (by rfl) ⟨17819675, by rfl⟩ : syracuseStep 23759567 = 35639351) B35639351
theorem B60107507 : Blo 1389514 60107507 := bstep (se 1 (by rfl) ⟨45080630, by rfl⟩ : syracuseStep 60107507 = 90161261) B90161261
theorem B3517931 : Blo 1389514 3517931 := bstep (se 1 (by rfl) ⟨2638448, by rfl⟩ : syracuseStep 3517931 = 5276897) B5276897
theorem B2084591 : Blo 1389514 2084591 := bstep (se 1 (by rfl) ⟨1563443, by rfl⟩ : syracuseStep 2084591 = 3126887) B3126887
theorem B17829881 : Blo 1389514 17829881 := bstep (se 2 (by rfl) ⟨6686205, by rfl⟩ : syracuseStep 17829881 = 13372411) B13372411
theorem B2969759 : Blo 1389514 2969759 := bstep (se 1 (by rfl) ⟨2227319, by rfl⟩ : syracuseStep 2969759 = 4454639) B4454639
theorem B22565101 : Blo 1389514 22565101 := bstep (se 3 (by rfl) ⟨4230956, by rfl⟩ : syracuseStep 22565101 = 8461913) B8461913
theorem B2347663 : Blo 1389514 2347663 := bstep (se 1 (by rfl) ⟨1760747, by rfl⟩ : syracuseStep 2347663 = 3521495) B3521495
theorem B76125233 : Blo 1389514 76125233 := bstep (se 2 (by rfl) ⟨28546962, by rfl⟩ : syracuseStep 76125233 = 57093925) B57093925
theorem B2086025 : Blo 1389514 2086025 := bstep (se 2 (by rfl) ⟨782259, by rfl⟩ : syracuseStep 2086025 = 1564519) B1564519
theorem B1389983 : Blo 1389514 1389983 := bstep (se 1 (by rfl) ⟨1042487, by rfl⟩ : syracuseStep 1389983 = 2084975) B2084975
theorem B45094643 : Blo 1389514 45094643 := bstep (se 1 (by rfl) ⟨33820982, by rfl⟩ : syracuseStep 45094643 = 67641965) B67641965
theorem B1390623 : Blo 1389514 1390623 := bstep (se 1 (by rfl) ⟨1042967, by rfl⟩ : syracuseStep 1390623 = 2085935) B2085935
theorem B1390843 : Blo 1389514 1390843 := bstep (se 1 (by rfl) ⟨1043132, by rfl⟩ : syracuseStep 1390843 = 2086265) B2086265
theorem B1390951 : Blo 1389514 1390951 := bstep (se 1 (by rfl) ⟨1043213, by rfl⟩ : syracuseStep 1390951 = 2086427) B2086427
theorem B1391039 : Blo 1389514 1391039 := bstep (se 1 (by rfl) ⟨1043279, by rfl⟩ : syracuseStep 1391039 = 2086559) B2086559
theorem B32111585 : Blo 1389514 32111585 := bstep (se 2 (by rfl) ⟨12041844, by rfl⟩ : syracuseStep 32111585 = 24083689) B24083689
theorem B1858663 : Blo 1389514 1858663 := bstep (se 1 (by rfl) ⟨1393997, by rfl⟩ : syracuseStep 1858663 = 2787995) B2787995
theorem B22543687 : Blo 1389514 22543687 := bstep (se 1 (by rfl) ⟨16907765, by rfl⟩ : syracuseStep 22543687 = 33815531) B33815531
theorem B10018237 : Blo 1389514 10018237 := bstep (se 3 (by rfl) ⟨1878419, by rfl⟩ : syracuseStep 10018237 = 3756839) B3756839
theorem B3129371 : Blo 1389514 3129371 := bstep (se 1 (by rfl) ⟨2347028, by rfl⟩ : syracuseStep 3129371 = 4694057) B4694057
theorem B7037117 : Blo 1389514 7037117 := bstep (se 3 (by rfl) ⟨1319459, by rfl⟩ : syracuseStep 7037117 = 2638919) B2638919
theorem B26739355 : Blo 1389514 26739355 := bstep (se 1 (by rfl) ⟨20054516, by rfl⟩ : syracuseStep 26739355 = 40109033) B40109033
theorem B50750155 : Blo 1389514 50750155 := bstep (se 1 (by rfl) ⟨38062616, by rfl⟩ : syracuseStep 50750155 = 76125233) B76125233
theorem B3130217 : Blo 1389514 3130217 := bstep (se 2 (by rfl) ⟨1173831, by rfl⟩ : syracuseStep 3130217 = 2347663) B2347663
theorem B5014495 : Blo 1389514 5014495 := bstep (se 1 (by rfl) ⟨3760871, by rfl⟩ : syracuseStep 5014495 = 7521743) B7521743
theorem B30058249 : Blo 1389514 30058249 := bstep (se 2 (by rfl) ⟨11271843, by rfl⟩ : syracuseStep 30058249 = 22543687) B22543687
theorem B21407723 : Blo 1389514 21407723 := bstep (se 1 (by rfl) ⟨16055792, by rfl⟩ : syracuseStep 21407723 = 32111585) B32111585
theorem B2345287 : Blo 1389514 2345287 := bstep (se 1 (by rfl) ⟨1758965, by rfl⟩ : syracuseStep 2345287 = 3517931) B3517931
theorem B11886587 : Blo 1389514 11886587 := bstep (se 1 (by rfl) ⟨8914940, by rfl⟩ : syracuseStep 11886587 = 17829881) B17829881
theorem B2478217 : Blo 1389514 2478217 := bstep (se 2 (by rfl) ⟨929331, by rfl⟩ : syracuseStep 2478217 = 1858663) B1858663
theorem B329363657 : Blo 1389514 329363657 := bstep (se 2 (by rfl) ⟨123511371, by rfl⟩ : syracuseStep 329363657 = 247022743) B247022743
theorem B15839711 : Blo 1389514 15839711 := bstep (se 1 (by rfl) ⟨11879783, by rfl⟩ : syracuseStep 15839711 = 23759567) B23759567
theorem B40071671 : Blo 1389514 40071671 := bstep (se 1 (by rfl) ⟨30053753, by rfl⟩ : syracuseStep 40071671 = 60107507) B60107507
theorem B13357649 : Blo 1389514 13357649 := bstep (se 2 (by rfl) ⟨5009118, by rfl⟩ : syracuseStep 13357649 = 10018237) B10018237
theorem B1389727 : Blo 1389514 1389727 := bstep (se 1 (by rfl) ⟨1042295, by rfl⟩ : syracuseStep 1389727 = 2084591) B2084591
theorem B1979839 : Blo 1389514 1979839 := bstep (se 1 (by rfl) ⟨1484879, by rfl⟩ : syracuseStep 1979839 = 2969759) B2969759
theorem B3126761 : Blo 1389514 3126761 := bstep (se 2 (by rfl) ⟨1172535, by rfl⟩ : syracuseStep 3126761 = 2345071) B2345071
theorem B30086801 : Blo 1389514 30086801 := bstep (se 2 (by rfl) ⟨11282550, by rfl⟩ : syracuseStep 30086801 = 22565101) B22565101
theorem B7034849 : Blo 1389514 7034849 := bstep (se 2 (by rfl) ⟨2638068, by rfl⟩ : syracuseStep 7034849 = 5276137) B5276137
theorem B3127265 : Blo 1389514 3127265 := bstep (se 2 (by rfl) ⟨1172724, by rfl⟩ : syracuseStep 3127265 = 2345449) B2345449
theorem B1390683 : Blo 1389514 1390683 := bstep (se 1 (by rfl) ⟨1043012, by rfl⟩ : syracuseStep 1390683 = 2086025) B2086025
theorem B30063095 : Blo 1389514 30063095 := bstep (se 1 (by rfl) ⟨22547321, by rfl⟩ : syracuseStep 30063095 = 45094643) B45094643
theorem B10559807 : Blo 1389514 10559807 := bstep (se 1 (by rfl) ⟨7919855, by rfl⟩ : syracuseStep 10559807 = 15839711) B15839711
theorem B26714447 : Blo 1389514 26714447 := bstep (se 1 (by rfl) ⟨20035835, by rfl⟩ : syracuseStep 26714447 = 40071671) B40071671
theorem B8905099 : Blo 1389514 8905099 := bstep (se 1 (by rfl) ⟨6678824, by rfl⟩ : syracuseStep 8905099 = 13357649) B13357649
theorem B35652473 : Blo 1389514 35652473 := bstep (se 2 (by rfl) ⟨13369677, by rfl⟩ : syracuseStep 35652473 = 26739355) B26739355
theorem B67666873 : Blo 1389514 67666873 := bstep (se 2 (by rfl) ⟨25375077, by rfl⟩ : syracuseStep 67666873 = 50750155) B50750155
theorem B6685993 : Blo 1389514 6685993 := bstep (se 2 (by rfl) ⟨2507247, by rfl⟩ : syracuseStep 6685993 = 5014495) B5014495
theorem B14271815 : Blo 1389514 14271815 := bstep (se 1 (by rfl) ⟨10703861, by rfl⟩ : syracuseStep 14271815 = 21407723) B21407723
theorem B2639785 : Blo 1389514 2639785 := bstep (se 2 (by rfl) ⟨989919, by rfl⟩ : syracuseStep 2639785 = 1979839) B1979839
theorem B40077665 : Blo 1389514 40077665 := bstep (se 2 (by rfl) ⟨15029124, by rfl⟩ : syracuseStep 40077665 = 30058249) B30058249
theorem B7924391 : Blo 1389514 7924391 := bstep (se 1 (by rfl) ⟨5943293, by rfl⟩ : syracuseStep 7924391 = 11886587) B11886587
theorem B2084507 : Blo 1389514 2084507 := bstep (se 1 (by rfl) ⟨1563380, by rfl⟩ : syracuseStep 2084507 = 3126761) B3126761
theorem B20057867 : Blo 1389514 20057867 := bstep (se 1 (by rfl) ⟨15043400, by rfl⟩ : syracuseStep 20057867 = 30086801) B30086801
theorem B4689899 : Blo 1389514 4689899 := bstep (se 1 (by rfl) ⟨3517424, by rfl⟩ : syracuseStep 4689899 = 7034849) B7034849
theorem B2084843 : Blo 1389514 2084843 := bstep (se 1 (by rfl) ⟨1563632, by rfl⟩ : syracuseStep 2084843 = 3127265) B3127265
theorem B20042063 : Blo 1389514 20042063 := bstep (se 1 (by rfl) ⟨15031547, by rfl⟩ : syracuseStep 20042063 = 30063095) B30063095
theorem B2086247 : Blo 1389514 2086247 := bstep (se 1 (by rfl) ⟨1564685, by rfl⟩ : syracuseStep 2086247 = 3129371) B3129371
theorem B4691411 : Blo 1389514 4691411 := bstep (se 1 (by rfl) ⟨3518558, by rfl⟩ : syracuseStep 4691411 = 7037117) B7037117
theorem B219575771 : Blo 1389514 219575771 := bstep (se 1 (by rfl) ⟨164681828, by rfl⟩ : syracuseStep 219575771 = 329363657) B329363657
theorem B52868629 : Blo 1389514 52868629 := bstep (se 6 (by rfl) ⟨1239108, by rfl⟩ : syracuseStep 52868629 = 2478217) B2478217
theorem B3127049 : Blo 1389514 3127049 := bstep (se 2 (by rfl) ⟨1172643, by rfl⟩ : syracuseStep 3127049 = 2345287) B2345287
theorem B2086811 : Blo 1389514 2086811 := bstep (se 1 (by rfl) ⟨1565108, by rfl⟩ : syracuseStep 2086811 = 3130217) B3130217
theorem B17809631 : Blo 1389514 17809631 := bstep (se 1 (by rfl) ⟨13357223, by rfl⟩ : syracuseStep 17809631 = 26714447) B26714447
theorem B13361375 : Blo 1389514 13361375 := bstep (se 1 (by rfl) ⟨10021031, by rfl⟩ : syracuseStep 13361375 = 20042063) B20042063
theorem B146383847 : Blo 1389514 146383847 := bstep (se 1 (by rfl) ⟨109787885, by rfl⟩ : syracuseStep 146383847 = 219575771) B219575771
theorem B8914657 : Blo 1389514 8914657 := bstep (se 2 (by rfl) ⟨3342996, by rfl⟩ : syracuseStep 8914657 = 6685993) B6685993
theorem B13371911 : Blo 1389514 13371911 := bstep (se 1 (by rfl) ⟨10028933, by rfl⟩ : syracuseStep 13371911 = 20057867) B20057867
theorem B7039871 : Blo 1389514 7039871 := bstep (se 1 (by rfl) ⟨5279903, by rfl⟩ : syracuseStep 7039871 = 10559807) B10559807
theorem B11873465 : Blo 1389514 11873465 := bstep (se 2 (by rfl) ⟨4452549, by rfl⟩ : syracuseStep 11873465 = 8905099) B8905099
theorem B23768315 : Blo 1389514 23768315 := bstep (se 1 (by rfl) ⟨17826236, by rfl⟩ : syracuseStep 23768315 = 35652473) B35652473
theorem B9514543 : Blo 1389514 9514543 := bstep (se 1 (by rfl) ⟨7135907, by rfl⟩ : syracuseStep 9514543 = 14271815) B14271815
theorem B2084699 : Blo 1389514 2084699 := bstep (se 1 (by rfl) ⟨1563524, by rfl⟩ : syracuseStep 2084699 = 3127049) B3127049
theorem B90222497 : Blo 1389514 90222497 := bstep (se 2 (by rfl) ⟨33833436, by rfl⟩ : syracuseStep 90222497 = 67666873) B67666873
theorem B26718443 : Blo 1389514 26718443 := bstep (se 1 (by rfl) ⟨20038832, by rfl⟩ : syracuseStep 26718443 = 40077665) B40077665
theorem B1389671 : Blo 1389514 1389671 := bstep (se 1 (by rfl) ⟨1042253, by rfl⟩ : syracuseStep 1389671 = 2084507) B2084507
theorem B3519713 : Blo 1389514 3519713 := bstep (se 2 (by rfl) ⟨1319892, by rfl⟩ : syracuseStep 3519713 = 2639785) B2639785
theorem B3126599 : Blo 1389514 3126599 := bstep (se 1 (by rfl) ⟨2344949, by rfl⟩ : syracuseStep 3126599 = 4689899) B4689899
theorem B1389895 : Blo 1389514 1389895 := bstep (se 1 (by rfl) ⟨1042421, by rfl⟩ : syracuseStep 1389895 = 2084843) B2084843
theorem B1390831 : Blo 1389514 1390831 := bstep (se 1 (by rfl) ⟨1043123, by rfl⟩ : syracuseStep 1390831 = 2086247) B2086247
theorem B3127607 : Blo 1389514 3127607 := bstep (se 1 (by rfl) ⟨2345705, by rfl⟩ : syracuseStep 3127607 = 4691411) B4691411
theorem B1391207 : Blo 1389514 1391207 := bstep (se 1 (by rfl) ⟨1043405, by rfl⟩ : syracuseStep 1391207 = 2086811) B2086811
theorem B5282927 : Blo 1389514 5282927 := bstep (se 1 (by rfl) ⟨3962195, by rfl⟩ : syracuseStep 5282927 = 7924391) B7924391
theorem B70491505 : Blo 1389514 70491505 := bstep (se 2 (by rfl) ⟨26434314, by rfl⟩ : syracuseStep 70491505 = 52868629) B52868629
theorem B8914607 : Blo 1389514 8914607 := bstep (se 1 (by rfl) ⟨6685955, by rfl⟩ : syracuseStep 8914607 = 13371911) B13371911
theorem B93988673 : Blo 1389514 93988673 := bstep (se 2 (by rfl) ⟨35245752, by rfl⟩ : syracuseStep 93988673 = 70491505) B70491505
theorem B7915643 : Blo 1389514 7915643 := bstep (se 1 (by rfl) ⟨5936732, by rfl⟩ : syracuseStep 7915643 = 11873465) B11873465
theorem B15845543 : Blo 1389514 15845543 := bstep (se 1 (by rfl) ⟨11884157, by rfl⟩ : syracuseStep 15845543 = 23768315) B23768315
theorem B60148331 : Blo 1389514 60148331 := bstep (se 1 (by rfl) ⟨45111248, by rfl⟩ : syracuseStep 60148331 = 90222497) B90222497
theorem B11873087 : Blo 1389514 11873087 := bstep (se 1 (by rfl) ⟨8904815, by rfl⟩ : syracuseStep 11873087 = 17809631) B17809631
theorem B8907583 : Blo 1389514 8907583 := bstep (se 1 (by rfl) ⟨6680687, by rfl⟩ : syracuseStep 8907583 = 13361375) B13361375
theorem B17812295 : Blo 1389514 17812295 := bstep (se 1 (by rfl) ⟨13359221, by rfl⟩ : syracuseStep 17812295 = 26718443) B26718443
theorem B2346475 : Blo 1389514 2346475 := bstep (se 1 (by rfl) ⟨1759856, by rfl⟩ : syracuseStep 2346475 = 3519713) B3519713
theorem B2084399 : Blo 1389514 2084399 := bstep (se 1 (by rfl) ⟨1563299, by rfl⟩ : syracuseStep 2084399 = 3126599) B3126599
theorem B2085071 : Blo 1389514 2085071 := bstep (se 1 (by rfl) ⟨1563803, by rfl⟩ : syracuseStep 2085071 = 3127607) B3127607
theorem B12686057 : Blo 1389514 12686057 := bstep (se 2 (by rfl) ⟨4757271, by rfl⟩ : syracuseStep 12686057 = 9514543) B9514543
theorem B1389799 : Blo 1389514 1389799 := bstep (se 1 (by rfl) ⟨1042349, by rfl⟩ : syracuseStep 1389799 = 2084699) B2084699
theorem B97589231 : Blo 1389514 97589231 := bstep (se 1 (by rfl) ⟨73191923, by rfl⟩ : syracuseStep 97589231 = 146383847) B146383847
theorem B4693247 : Blo 1389514 4693247 := bstep (se 1 (by rfl) ⟨3519935, by rfl⟩ : syracuseStep 4693247 = 7039871) B7039871
theorem B3521951 : Blo 1389514 3521951 := bstep (se 1 (by rfl) ⟨2641463, by rfl⟩ : syracuseStep 3521951 = 5282927) B5282927
theorem B11886209 : Blo 1389514 11886209 := bstep (se 2 (by rfl) ⟨4457328, by rfl⟩ : syracuseStep 11886209 = 8914657) B8914657
theorem B5277095 : Blo 1389514 5277095 := bstep (se 1 (by rfl) ⟨3957821, by rfl⟩ : syracuseStep 5277095 = 7915643) B7915643
theorem B7915391 : Blo 1389514 7915391 := bstep (se 1 (by rfl) ⟨5936543, by rfl⟩ : syracuseStep 7915391 = 11873087) B11873087
theorem B7924139 : Blo 1389514 7924139 := bstep (se 1 (by rfl) ⟨5943104, by rfl⟩ : syracuseStep 7924139 = 11886209) B11886209
theorem B8457371 : Blo 1389514 8457371 := bstep (se 1 (by rfl) ⟨6343028, by rfl⟩ : syracuseStep 8457371 = 12686057) B12686057
theorem B5943071 : Blo 1389514 5943071 := bstep (se 1 (by rfl) ⟨4457303, by rfl⟩ : syracuseStep 5943071 = 8914607) B8914607
theorem B10563695 : Blo 1389514 10563695 := bstep (se 1 (by rfl) ⟨7922771, by rfl⟩ : syracuseStep 10563695 = 15845543) B15845543
theorem B11874863 : Blo 1389514 11874863 := bstep (se 1 (by rfl) ⟨8906147, by rfl⟩ : syracuseStep 11874863 = 17812295) B17812295
theorem B2347967 : Blo 1389514 2347967 := bstep (se 1 (by rfl) ⟨1760975, by rfl⟩ : syracuseStep 2347967 = 3521951) B3521951
theorem B1389599 : Blo 1389514 1389599 := bstep (se 1 (by rfl) ⟨1042199, by rfl⟩ : syracuseStep 1389599 = 2084399) B2084399
theorem B1390047 : Blo 1389514 1390047 := bstep (se 1 (by rfl) ⟨1042535, by rfl⟩ : syracuseStep 1390047 = 2085071) B2085071
theorem B11876777 : Blo 1389514 11876777 := bstep (se 2 (by rfl) ⟨4453791, by rfl⟩ : syracuseStep 11876777 = 8907583) B8907583
theorem B62659115 : Blo 1389514 62659115 := bstep (se 1 (by rfl) ⟨46994336, by rfl⟩ : syracuseStep 62659115 = 93988673) B93988673
theorem B65059487 : Blo 1389514 65059487 := bstep (se 1 (by rfl) ⟨48794615, by rfl⟩ : syracuseStep 65059487 = 97589231) B97589231
theorem B40098887 : Blo 1389514 40098887 := bstep (se 1 (by rfl) ⟨30074165, by rfl⟩ : syracuseStep 40098887 = 60148331) B60148331
theorem B3128633 : Blo 1389514 3128633 := bstep (se 2 (by rfl) ⟨1173237, by rfl⟩ : syracuseStep 3128633 = 2346475) B2346475
theorem B3128831 : Blo 1389514 3128831 := bstep (se 1 (by rfl) ⟨2346623, by rfl⟩ : syracuseStep 3128831 = 4693247) B4693247
theorem B1565311 : Blo 1389514 1565311 := bstep (se 1 (by rfl) ⟨1173983, by rfl⟩ : syracuseStep 1565311 = 2347967) B2347967
theorem B5276927 : Blo 1389514 5276927 := bstep (se 1 (by rfl) ⟨3957695, by rfl⟩ : syracuseStep 5276927 = 7915391) B7915391
theorem B41772743 : Blo 1389514 41772743 := bstep (se 1 (by rfl) ⟨31329557, by rfl⟩ : syracuseStep 41772743 = 62659115) B62659115
theorem B26732591 : Blo 1389514 26732591 := bstep (se 1 (by rfl) ⟨20049443, by rfl⟩ : syracuseStep 26732591 = 40098887) B40098887
theorem B5638247 : Blo 1389514 5638247 := bstep (se 1 (by rfl) ⟨4228685, by rfl⟩ : syracuseStep 5638247 = 8457371) B8457371
theorem B7916575 : Blo 1389514 7916575 := bstep (se 1 (by rfl) ⟨5937431, by rfl⟩ : syracuseStep 7916575 = 11874863) B11874863
theorem B3518063 : Blo 1389514 3518063 := bstep (se 1 (by rfl) ⟨2638547, by rfl⟩ : syracuseStep 3518063 = 5277095) B5277095
theorem B7917851 : Blo 1389514 7917851 := bstep (se 1 (by rfl) ⟨5938388, by rfl⟩ : syracuseStep 7917851 = 11876777) B11876777
theorem B43372991 : Blo 1389514 43372991 := bstep (se 1 (by rfl) ⟨32529743, by rfl⟩ : syracuseStep 43372991 = 65059487) B65059487
theorem B2085755 : Blo 1389514 2085755 := bstep (se 1 (by rfl) ⟨1564316, by rfl⟩ : syracuseStep 2085755 = 3128633) B3128633
theorem B2085887 : Blo 1389514 2085887 := bstep (se 1 (by rfl) ⟨1564415, by rfl⟩ : syracuseStep 2085887 = 3128831) B3128831
theorem B3962047 : Blo 1389514 3962047 := bstep (se 1 (by rfl) ⟨2971535, by rfl⟩ : syracuseStep 3962047 = 5943071) B5943071
theorem B7042463 : Blo 1389514 7042463 := bstep (se 1 (by rfl) ⟨5281847, by rfl⟩ : syracuseStep 7042463 = 10563695) B10563695
theorem B5282759 : Blo 1389514 5282759 := bstep (se 1 (by rfl) ⟨3962069, by rfl⟩ : syracuseStep 5282759 = 7924139) B7924139
theorem B4694975 : Blo 1389514 4694975 := bstep (se 1 (by rfl) ⟨3521231, by rfl⟩ : syracuseStep 4694975 = 7042463) B7042463
theorem B2345375 : Blo 1389514 2345375 := bstep (se 1 (by rfl) ⟨1759031, by rfl⟩ : syracuseStep 2345375 = 3518063) B3518063
theorem B5278567 : Blo 1389514 5278567 := bstep (se 1 (by rfl) ⟨3958925, by rfl⟩ : syracuseStep 5278567 = 7917851) B7917851
theorem B3517951 : Blo 1389514 3517951 := bstep (se 1 (by rfl) ⟨2638463, by rfl⟩ : syracuseStep 3517951 = 5276927) B5276927
theorem B27848495 : Blo 1389514 27848495 := bstep (se 1 (by rfl) ⟨20886371, by rfl⟩ : syracuseStep 27848495 = 41772743) B41772743
theorem B17821727 : Blo 1389514 17821727 := bstep (se 1 (by rfl) ⟨13366295, by rfl⟩ : syracuseStep 17821727 = 26732591) B26732591
theorem B10555433 : Blo 1389514 10555433 := bstep (se 2 (by rfl) ⟨3958287, by rfl⟩ : syracuseStep 10555433 = 7916575) B7916575
theorem B28915327 : Blo 1389514 28915327 := bstep (se 1 (by rfl) ⟨21686495, by rfl⟩ : syracuseStep 28915327 = 43372991) B43372991
theorem B1390503 : Blo 1389514 1390503 := bstep (se 1 (by rfl) ⟨1042877, by rfl⟩ : syracuseStep 1390503 = 2085755) B2085755
theorem B1390591 : Blo 1389514 1390591 := bstep (se 1 (by rfl) ⟨1042943, by rfl⟩ : syracuseStep 1390591 = 2085887) B2085887
theorem B2087081 : Blo 1389514 2087081 := bstep (se 2 (by rfl) ⟨782655, by rfl⟩ : syracuseStep 2087081 = 1565311) B1565311
theorem B3758831 : Blo 1389514 3758831 := bstep (se 1 (by rfl) ⟨2819123, by rfl⟩ : syracuseStep 3758831 = 5638247) B5638247
theorem B5282729 : Blo 1389514 5282729 := bstep (se 2 (by rfl) ⟨1981023, by rfl⟩ : syracuseStep 5282729 = 3962047) B3962047
theorem B3521839 : Blo 1389514 3521839 := bstep (se 1 (by rfl) ⟨2641379, by rfl⟩ : syracuseStep 3521839 = 5282759) B5282759
theorem B7036955 : Blo 1389514 7036955 := bstep (se 1 (by rfl) ⟨5277716, by rfl⟩ : syracuseStep 7036955 = 10555433) B10555433
theorem B3129983 : Blo 1389514 3129983 := bstep (se 1 (by rfl) ⟨2347487, by rfl⟩ : syracuseStep 3129983 = 4694975) B4694975
theorem B7038089 : Blo 1389514 7038089 := bstep (se 2 (by rfl) ⟨2639283, by rfl⟩ : syracuseStep 7038089 = 5278567) B5278567
theorem B4695785 : Blo 1389514 4695785 := bstep (se 2 (by rfl) ⟨1760919, by rfl⟩ : syracuseStep 4695785 = 3521839) B3521839
theorem B74262653 : Blo 1389514 74262653 := bstep (se 3 (by rfl) ⟨13924247, by rfl⟩ : syracuseStep 74262653 = 27848495) B27848495
theorem B38553769 : Blo 1389514 38553769 := bstep (se 2 (by rfl) ⟨14457663, by rfl⟩ : syracuseStep 38553769 = 28915327) B28915327
theorem B11881151 : Blo 1389514 11881151 := bstep (se 1 (by rfl) ⟨8910863, by rfl⟩ : syracuseStep 11881151 = 17821727) B17821727
theorem B4690601 : Blo 1389514 4690601 := bstep (se 2 (by rfl) ⟨1758975, by rfl⟩ : syracuseStep 4690601 = 3517951) B3517951
theorem B1391387 : Blo 1389514 1391387 := bstep (se 1 (by rfl) ⟨1043540, by rfl⟩ : syracuseStep 1391387 = 2087081) B2087081
theorem B1563583 : Blo 1389514 1563583 := bstep (se 1 (by rfl) ⟨1172687, by rfl⟩ : syracuseStep 1563583 = 2345375) B2345375
theorem B2505887 : Blo 1389514 2505887 := bstep (se 1 (by rfl) ⟨1879415, by rfl⟩ : syracuseStep 2505887 = 3758831) B3758831
theorem B3521819 : Blo 1389514 3521819 := bstep (se 1 (by rfl) ⟨2641364, by rfl⟩ : syracuseStep 3521819 = 5282729) B5282729
theorem B51405025 : Blo 1389514 51405025 := bstep (se 2 (by rfl) ⟨19276884, by rfl⟩ : syracuseStep 51405025 = 38553769) B38553769
theorem B3130523 : Blo 1389514 3130523 := bstep (se 1 (by rfl) ⟨2347892, by rfl⟩ : syracuseStep 3130523 = 4695785) B4695785
theorem B2084777 : Blo 1389514 2084777 := bstep (se 2 (by rfl) ⟨781791, by rfl⟩ : syracuseStep 2084777 = 1563583) B1563583
theorem B49508435 : Blo 1389514 49508435 := bstep (se 1 (by rfl) ⟨37131326, by rfl⟩ : syracuseStep 49508435 = 74262653) B74262653
theorem B2347879 : Blo 1389514 2347879 := bstep (se 1 (by rfl) ⟨1760909, by rfl⟩ : syracuseStep 2347879 = 3521819) B3521819
theorem B4691303 : Blo 1389514 4691303 := bstep (se 1 (by rfl) ⟨3518477, by rfl⟩ : syracuseStep 4691303 = 7036955) B7036955
theorem B2086655 : Blo 1389514 2086655 := bstep (se 1 (by rfl) ⟨1564991, by rfl⟩ : syracuseStep 2086655 = 3129983) B3129983
theorem B3127067 : Blo 1389514 3127067 := bstep (se 1 (by rfl) ⟨2345300, by rfl⟩ : syracuseStep 3127067 = 4690601) B4690601
theorem B4692059 : Blo 1389514 4692059 := bstep (se 1 (by rfl) ⟨3519044, by rfl⟩ : syracuseStep 4692059 = 7038089) B7038089
theorem B7920767 : Blo 1389514 7920767 := bstep (se 1 (by rfl) ⟨5940575, by rfl⟩ : syracuseStep 7920767 = 11881151) B11881151
theorem B1670591 : Blo 1389514 1670591 := bstep (se 1 (by rfl) ⟨1252943, by rfl⟩ : syracuseStep 1670591 = 2505887) B2505887
theorem B132022493 : Blo 1389514 132022493 := bstep (se 3 (by rfl) ⟨24754217, by rfl⟩ : syracuseStep 132022493 = 49508435) B49508435
theorem B3130505 : Blo 1389514 3130505 := bstep (se 2 (by rfl) ⟨1173939, by rfl⟩ : syracuseStep 3130505 = 2347879) B2347879
theorem B2084711 : Blo 1389514 2084711 := bstep (se 1 (by rfl) ⟨1563533, by rfl⟩ : syracuseStep 2084711 = 3127067) B3127067
theorem B5280511 : Blo 1389514 5280511 := bstep (se 1 (by rfl) ⟨3960383, by rfl⟩ : syracuseStep 5280511 = 7920767) B7920767
theorem B1389851 : Blo 1389514 1389851 := bstep (se 1 (by rfl) ⟨1042388, by rfl⟩ : syracuseStep 1389851 = 2084777) B2084777
theorem B68540033 : Blo 1389514 68540033 := bstep (se 2 (by rfl) ⟨25702512, by rfl⟩ : syracuseStep 68540033 = 51405025) B51405025
theorem B2087015 : Blo 1389514 2087015 := bstep (se 1 (by rfl) ⟨1565261, by rfl⟩ : syracuseStep 2087015 = 3130523) B3130523
theorem B3127535 : Blo 1389514 3127535 := bstep (se 1 (by rfl) ⟨2345651, by rfl⟩ : syracuseStep 3127535 = 4691303) B4691303
theorem B4454909 : Blo 1389514 4454909 := bstep (se 3 (by rfl) ⟨835295, by rfl⟩ : syracuseStep 4454909 = 1670591) B1670591
theorem B1391103 : Blo 1389514 1391103 := bstep (se 1 (by rfl) ⟨1043327, by rfl⟩ : syracuseStep 1391103 = 2086655) B2086655
theorem B3128039 : Blo 1389514 3128039 := bstep (se 1 (by rfl) ⟨2346029, by rfl⟩ : syracuseStep 3128039 = 4692059) B4692059
theorem B88014995 : Blo 1389514 88014995 := bstep (se 1 (by rfl) ⟨66011246, by rfl⟩ : syracuseStep 88014995 = 132022493) B132022493
theorem B182773421 : Blo 1389514 182773421 := bstep (se 3 (by rfl) ⟨34270016, by rfl⟩ : syracuseStep 182773421 = 68540033) B68540033
theorem B7040681 : Blo 1389514 7040681 := bstep (se 2 (by rfl) ⟨2640255, by rfl⟩ : syracuseStep 7040681 = 5280511) B5280511
theorem B2085023 : Blo 1389514 2085023 := bstep (se 1 (by rfl) ⟨1563767, by rfl⟩ : syracuseStep 2085023 = 3127535) B3127535
theorem B2969939 : Blo 1389514 2969939 := bstep (se 1 (by rfl) ⟨2227454, by rfl⟩ : syracuseStep 2969939 = 4454909) B4454909
theorem B2085359 : Blo 1389514 2085359 := bstep (se 1 (by rfl) ⟨1564019, by rfl⟩ : syracuseStep 2085359 = 3128039) B3128039
theorem B1389807 : Blo 1389514 1389807 := bstep (se 1 (by rfl) ⟨1042355, by rfl⟩ : syracuseStep 1389807 = 2084711) B2084711
theorem B2087003 : Blo 1389514 2087003 := bstep (se 1 (by rfl) ⟨1565252, by rfl⟩ : syracuseStep 2087003 = 3130505) B3130505
theorem B1391343 : Blo 1389514 1391343 := bstep (se 1 (by rfl) ⟨1043507, by rfl⟩ : syracuseStep 1391343 = 2087015) B2087015
theorem B121848947 : Blo 1389514 121848947 := bstep (se 1 (by rfl) ⟨91386710, by rfl⟩ : syracuseStep 121848947 = 182773421) B182773421
theorem B58676663 : Blo 1389514 58676663 := bstep (se 1 (by rfl) ⟨44007497, by rfl⟩ : syracuseStep 58676663 = 88014995) B88014995
theorem B1390015 : Blo 1389514 1390015 := bstep (se 1 (by rfl) ⟨1042511, by rfl⟩ : syracuseStep 1390015 = 2085023) B2085023
theorem B1979959 : Blo 1389514 1979959 := bstep (se 1 (by rfl) ⟨1484969, by rfl⟩ : syracuseStep 1979959 = 2969939) B2969939
theorem B1390239 : Blo 1389514 1390239 := bstep (se 1 (by rfl) ⟨1042679, by rfl⟩ : syracuseStep 1390239 = 2085359) B2085359
theorem B1391335 : Blo 1389514 1391335 := bstep (se 1 (by rfl) ⟨1043501, by rfl⟩ : syracuseStep 1391335 = 2087003) B2087003
theorem B4693787 : Blo 1389514 4693787 := bstep (se 1 (by rfl) ⟨3520340, by rfl⟩ : syracuseStep 4693787 = 7040681) B7040681
theorem B81232631 : Blo 1389514 81232631 := bstep (se 1 (by rfl) ⟨60924473, by rfl⟩ : syracuseStep 81232631 = 121848947) B121848947
theorem B39117775 : Blo 1389514 39117775 := bstep (se 1 (by rfl) ⟨29338331, by rfl⟩ : syracuseStep 39117775 = 58676663) B58676663
theorem B2639945 : Blo 1389514 2639945 := bstep (se 2 (by rfl) ⟨989979, by rfl⟩ : syracuseStep 2639945 = 1979959) B1979959
theorem B3129191 : Blo 1389514 3129191 := bstep (se 1 (by rfl) ⟨2346893, by rfl⟩ : syracuseStep 3129191 = 4693787) B4693787
theorem B2086127 : Blo 1389514 2086127 := bstep (se 1 (by rfl) ⟨1564595, by rfl⟩ : syracuseStep 2086127 = 3129191) B3129191
theorem B54155087 : Blo 1389514 54155087 := bstep (se 1 (by rfl) ⟨40616315, by rfl⟩ : syracuseStep 54155087 = 81232631) B81232631
theorem B52157033 : Blo 1389514 52157033 := bstep (se 2 (by rfl) ⟨19558887, by rfl⟩ : syracuseStep 52157033 = 39117775) B39117775
theorem B1759963 : Blo 1389514 1759963 := bstep (se 1 (by rfl) ⟨1319972, by rfl⟩ : syracuseStep 1759963 = 2639945) B2639945
theorem B36103391 : Blo 1389514 36103391 := bstep (se 1 (by rfl) ⟨27077543, by rfl⟩ : syracuseStep 36103391 = 54155087) B54155087
theorem B2346617 : Blo 1389514 2346617 := bstep (se 2 (by rfl) ⟨879981, by rfl⟩ : syracuseStep 2346617 = 1759963) B1759963
theorem B34771355 : Blo 1389514 34771355 := bstep (se 1 (by rfl) ⟨26078516, by rfl⟩ : syracuseStep 34771355 = 52157033) B52157033
theorem B1390751 : Blo 1389514 1390751 := bstep (se 1 (by rfl) ⟨1043063, by rfl⟩ : syracuseStep 1390751 = 2086127) B2086127
theorem B24068927 : Blo 1389514 24068927 := bstep (se 1 (by rfl) ⟨18051695, by rfl⟩ : syracuseStep 24068927 = 36103391) B36103391
theorem B23180903 : Blo 1389514 23180903 := bstep (se 1 (by rfl) ⟨17385677, by rfl⟩ : syracuseStep 23180903 = 34771355) B34771355
theorem B1564411 : Blo 1389514 1564411 := bstep (se 1 (by rfl) ⟨1173308, by rfl⟩ : syracuseStep 1564411 = 2346617) B2346617
theorem B15453935 : Blo 1389514 15453935 := bstep (se 1 (by rfl) ⟨11590451, by rfl⟩ : syracuseStep 15453935 = 23180903) B23180903
theorem B2085881 : Blo 1389514 2085881 := bstep (se 2 (by rfl) ⟨782205, by rfl⟩ : syracuseStep 2085881 = 1564411) B1564411
theorem B16045951 : Blo 1389514 16045951 := bstep (se 1 (by rfl) ⟨12034463, by rfl⟩ : syracuseStep 16045951 = 24068927) B24068927
theorem B10302623 : Blo 1389514 10302623 := bstep (se 1 (by rfl) ⟨7726967, by rfl⟩ : syracuseStep 10302623 = 15453935) B15453935
theorem B21394601 : Blo 1389514 21394601 := bstep (se 2 (by rfl) ⟨8022975, by rfl⟩ : syracuseStep 21394601 = 16045951) B16045951
theorem B1390587 : Blo 1389514 1390587 := bstep (se 1 (by rfl) ⟨1042940, by rfl⟩ : syracuseStep 1390587 = 2085881) B2085881
theorem B14263067 : Blo 1389514 14263067 := bstep (se 1 (by rfl) ⟨10697300, by rfl⟩ : syracuseStep 14263067 = 21394601) B21394601
theorem B6868415 : Blo 1389514 6868415 := bstep (se 1 (by rfl) ⟨5151311, by rfl⟩ : syracuseStep 6868415 = 10302623) B10302623
theorem B9508711 : Blo 1389514 9508711 := bstep (se 1 (by rfl) ⟨7131533, by rfl⟩ : syracuseStep 9508711 = 14263067) B14263067
theorem B18315773 : Blo 1389514 18315773 := bstep (se 3 (by rfl) ⟨3434207, by rfl⟩ : syracuseStep 18315773 = 6868415) B6868415
theorem B12210515 : Blo 1389514 12210515 := bstep (se 1 (by rfl) ⟨9157886, by rfl⟩ : syracuseStep 12210515 = 18315773) B18315773
theorem B12678281 : Blo 1389514 12678281 := bstep (se 2 (by rfl) ⟨4754355, by rfl⟩ : syracuseStep 12678281 = 9508711) B9508711
theorem B8140343 : Blo 1389514 8140343 := bstep (se 1 (by rfl) ⟨6105257, by rfl⟩ : syracuseStep 8140343 = 12210515) B12210515
theorem B8452187 : Blo 1389514 8452187 := bstep (se 1 (by rfl) ⟨6339140, by rfl⟩ : syracuseStep 8452187 = 12678281) B12678281
theorem B86830325 : Blo 1389514 86830325 := bstep (se 5 (by rfl) ⟨4070171, by rfl⟩ : syracuseStep 86830325 = 8140343) B8140343
theorem B5634791 : Blo 1389514 5634791 := bstep (se 1 (by rfl) ⟨4226093, by rfl⟩ : syracuseStep 5634791 = 8452187) B8452187
theorem B57886883 : Blo 1389514 57886883 := bstep (se 1 (by rfl) ⟨43415162, by rfl⟩ : syracuseStep 57886883 = 86830325) B86830325
theorem B3756527 : Blo 1389514 3756527 := bstep (se 1 (by rfl) ⟨2817395, by rfl⟩ : syracuseStep 3756527 = 5634791) B5634791
theorem B2504351 : Blo 1389514 2504351 := bstep (se 1 (by rfl) ⟨1878263, by rfl⟩ : syracuseStep 2504351 = 3756527) B3756527
theorem B38591255 : Blo 1389514 38591255 := bstep (se 1 (by rfl) ⟨28943441, by rfl⟩ : syracuseStep 38591255 = 57886883) B57886883
theorem B25727503 : Blo 1389514 25727503 := bstep (se 1 (by rfl) ⟨19295627, by rfl⟩ : syracuseStep 25727503 = 38591255) B38591255
theorem B1669567 : Blo 1389514 1669567 := bstep (se 1 (by rfl) ⟨1252175, by rfl⟩ : syracuseStep 1669567 = 2504351) B2504351
theorem B34303337 : Blo 1389514 34303337 := bstep (se 2 (by rfl) ⟨12863751, by rfl⟩ : syracuseStep 34303337 = 25727503) B25727503
theorem B2226089 : Blo 1389514 2226089 := bstep (se 2 (by rfl) ⟨834783, by rfl⟩ : syracuseStep 2226089 = 1669567) B1669567
theorem B22868891 : Blo 1389514 22868891 := bstep (se 1 (by rfl) ⟨17151668, by rfl⟩ : syracuseStep 22868891 = 34303337) B34303337
theorem B5936237 : Blo 1389514 5936237 := bstep (se 3 (by rfl) ⟨1113044, by rfl⟩ : syracuseStep 5936237 = 2226089) B2226089
theorem B15245927 : Blo 1389514 15245927 := bstep (se 1 (by rfl) ⟨11434445, by rfl⟩ : syracuseStep 15245927 = 22868891) B22868891
theorem B3957491 : Blo 1389514 3957491 := bstep (se 1 (by rfl) ⟨2968118, by rfl⟩ : syracuseStep 3957491 = 5936237) B5936237
theorem B2638327 : Blo 1389514 2638327 := bstep (se 1 (by rfl) ⟨1978745, by rfl⟩ : syracuseStep 2638327 = 3957491) B3957491
theorem B10163951 : Blo 1389514 10163951 := bstep (se 1 (by rfl) ⟨7622963, by rfl⟩ : syracuseStep 10163951 = 15245927) B15245927
theorem B6775967 : Blo 1389514 6775967 := bstep (se 1 (by rfl) ⟨5081975, by rfl⟩ : syracuseStep 6775967 = 10163951) B10163951
theorem B3517769 : Blo 1389514 3517769 := bstep (se 2 (by rfl) ⟨1319163, by rfl⟩ : syracuseStep 3517769 = 2638327) B2638327
theorem B2345179 : Blo 1389514 2345179 := bstep (se 1 (by rfl) ⟨1758884, by rfl⟩ : syracuseStep 2345179 = 3517769) B3517769
theorem B18069245 : Blo 1389514 18069245 := bstep (se 3 (by rfl) ⟨3387983, by rfl⟩ : syracuseStep 18069245 = 6775967) B6775967
theorem B12046163 : Blo 1389514 12046163 := bstep (se 1 (by rfl) ⟨9034622, by rfl⟩ : syracuseStep 12046163 = 18069245) B18069245
theorem B3126905 : Blo 1389514 3126905 := bstep (se 2 (by rfl) ⟨1172589, by rfl⟩ : syracuseStep 3126905 = 2345179) B2345179
theorem B32123101 : Blo 1389514 32123101 := bstep (se 3 (by rfl) ⟨6023081, by rfl⟩ : syracuseStep 32123101 = 12046163) B12046163
theorem B2084603 : Blo 1389514 2084603 := bstep (se 1 (by rfl) ⟨1563452, by rfl⟩ : syracuseStep 2084603 = 3126905) B3126905
theorem B42830801 : Blo 1389514 42830801 := bstep (se 2 (by rfl) ⟨16061550, by rfl⟩ : syracuseStep 42830801 = 32123101) B32123101
theorem B1389735 : Blo 1389514 1389735 := bstep (se 1 (by rfl) ⟨1042301, by rfl⟩ : syracuseStep 1389735 = 2084603) B2084603
theorem B28553867 : Blo 1389514 28553867 := bstep (se 1 (by rfl) ⟨21415400, by rfl⟩ : syracuseStep 28553867 = 42830801) B42830801
theorem B19035911 : Blo 1389514 19035911 := bstep (se 1 (by rfl) ⟨14276933, by rfl⟩ : syracuseStep 19035911 = 28553867) B28553867
theorem B12690607 : Blo 1389514 12690607 := bstep (se 1 (by rfl) ⟨9517955, by rfl⟩ : syracuseStep 12690607 = 19035911) B19035911
theorem B16920809 : Blo 1389514 16920809 := bstep (se 2 (by rfl) ⟨6345303, by rfl⟩ : syracuseStep 16920809 = 12690607) B12690607
theorem B11280539 : Blo 1389514 11280539 := bstep (se 1 (by rfl) ⟨8460404, by rfl⟩ : syracuseStep 11280539 = 16920809) B16920809
theorem B7520359 : Blo 1389514 7520359 := bstep (se 1 (by rfl) ⟨5640269, by rfl⟩ : syracuseStep 7520359 = 11280539) B11280539
theorem B10027145 : Blo 1389514 10027145 := bstep (se 2 (by rfl) ⟨3760179, by rfl⟩ : syracuseStep 10027145 = 7520359) B7520359
theorem B6684763 : Blo 1389514 6684763 := bstep (se 1 (by rfl) ⟨5013572, by rfl⟩ : syracuseStep 6684763 = 10027145) B10027145
theorem B8913017 : Blo 1389514 8913017 := bstep (se 2 (by rfl) ⟨3342381, by rfl⟩ : syracuseStep 8913017 = 6684763) B6684763
theorem B5942011 : Blo 1389514 5942011 := bstep (se 1 (by rfl) ⟨4456508, by rfl⟩ : syracuseStep 5942011 = 8913017) B8913017
theorem B7922681 : Blo 1389514 7922681 := bstep (se 2 (by rfl) ⟨2971005, by rfl⟩ : syracuseStep 7922681 = 5942011) B5942011
theorem B5281787 : Blo 1389514 5281787 := bstep (se 1 (by rfl) ⟨3961340, by rfl⟩ : syracuseStep 5281787 = 7922681) B7922681
theorem B3521191 : Blo 1389514 3521191 := bstep (se 1 (by rfl) ⟨2640893, by rfl⟩ : syracuseStep 3521191 = 5281787) B5281787
theorem B4694921 : Blo 1389514 4694921 := bstep (se 2 (by rfl) ⟨1760595, by rfl⟩ : syracuseStep 4694921 = 3521191) B3521191
theorem B3129947 : Blo 1389514 3129947 := bstep (se 1 (by rfl) ⟨2347460, by rfl⟩ : syracuseStep 3129947 = 4694921) B4694921
theorem B2086631 : Blo 1389514 2086631 := bstep (se 1 (by rfl) ⟨1564973, by rfl⟩ : syracuseStep 2086631 = 3129947) B3129947
theorem B1391087 : Blo 1389514 1391087 := bstep (se 1 (by rfl) ⟨1043315, by rfl⟩ : syracuseStep 1391087 = 2086631) B2086631

theorem C0 (j : ℕ) (h1 : 347378 ≤ j) (h2 : j ≤ 347877) : Blo 1389514 (4 * j + 3) := by
  interval_cases j
  · exact B1389515
  · exact B1389519
  · exact B1389523
  · exact B1389527
  · exact B1389531
  · exact B1389535
  · exact B1389539
  · exact B1389543
  · exact B1389547
  · exact B1389551
  · exact B1389555
  · exact B1389559
  · exact B1389563
  · exact B1389567
  · exact B1389571
  · exact B1389575
  · exact B1389579
  · exact B1389583
  · exact B1389587
  · exact B1389591
  · exact B1389595
  · exact B1389599
  · exact B1389603
  · exact B1389607
  · exact B1389611
  · exact B1389615
  · exact B1389619
  · exact B1389623
  · exact B1389627
  · exact B1389631
  · exact B1389635
  · exact B1389639
  · exact B1389643
  · exact B1389647
  · exact B1389651
  · exact B1389655
  · exact B1389659
  · exact B1389663
  · exact B1389667
  · exact B1389671
  · exact B1389675
  · exact B1389679
  · exact B1389683
  · exact B1389687
  · exact B1389691
  · exact B1389695
  · exact B1389699
  · exact B1389703
  · exact B1389707
  · exact B1389711
  · exact B1389715
  · exact B1389719
  · exact B1389723
  · exact B1389727
  · exact B1389731
  · exact B1389735
  · exact B1389739
  · exact B1389743
  · exact B1389747
  · exact B1389751
  · exact B1389755
  · exact B1389759
  · exact B1389763
  · exact B1389767
  · exact B1389771
  · exact B1389775
  · exact B1389779
  · exact B1389783
  · exact B1389787
  · exact B1389791
  · exact B1389795
  · exact B1389799
  · exact B1389803
  · exact B1389807
  · exact B1389811
  · exact B1389815
  · exact B1389819
  · exact B1389823
  · exact B1389827
  · exact B1389831
  · exact B1389835
  · exact B1389839
  · exact B1389843
  · exact B1389847
  · exact B1389851
  · exact B1389855
  · exact B1389859
  · exact B1389863
  · exact B1389867
  · exact B1389871
  · exact B1389875
  · exact B1389879
  · exact B1389883
  · exact B1389887
  · exact B1389891
  · exact B1389895
  · exact B1389899
  · exact B1389903
  · exact B1389907
  · exact B1389911
  · exact B1389915
  · exact B1389919
  · exact B1389923
  · exact B1389927
  · exact B1389931
  · exact B1389935
  · exact B1389939
  · exact B1389943
  · exact B1389947
  · exact B1389951
  · exact B1389955
  · exact B1389959
  · exact B1389963
  · exact B1389967
  · exact B1389971
  · exact B1389975
  · exact B1389979
  · exact B1389983
  · exact B1389987
  · exact B1389991
  · exact B1389995
  · exact B1389999
  · exact B1390003
  · exact B1390007
  · exact B1390011
  · exact B1390015
  · exact B1390019
  · exact B1390023
  · exact B1390027
  · exact B1390031
  · exact B1390035
  · exact B1390039
  · exact B1390043
  · exact B1390047
  · exact B1390051
  · exact B1390055
  · exact B1390059
  · exact B1390063
  · exact B1390067
  · exact B1390071
  · exact B1390075
  · exact B1390079
  · exact B1390083
  · exact B1390087
  · exact B1390091
  · exact B1390095
  · exact B1390099
  · exact B1390103
  · exact B1390107
  · exact B1390111
  · exact B1390115
  · exact B1390119
  · exact B1390123
  · exact B1390127
  · exact B1390131
  · exact B1390135
  · exact B1390139
  · exact B1390143
  · exact B1390147
  · exact B1390151
  · exact B1390155
  · exact B1390159
  · exact B1390163
  · exact B1390167
  · exact B1390171
  · exact B1390175
  · exact B1390179
  · exact B1390183
  · exact B1390187
  · exact B1390191
  · exact B1390195
  · exact B1390199
  · exact B1390203
  · exact B1390207
  · exact B1390211
  · exact B1390215
  · exact B1390219
  · exact B1390223
  · exact B1390227
  · exact B1390231
  · exact B1390235
  · exact B1390239
  · exact B1390243
  · exact B1390247
  · exact B1390251
  · exact B1390255
  · exact B1390259
  · exact B1390263
  · exact B1390267
  · exact B1390271
  · exact B1390275
  · exact B1390279
  · exact B1390283
  · exact B1390287
  · exact B1390291
  · exact B1390295
  · exact B1390299
  · exact B1390303
  · exact B1390307
  · exact B1390311
  · exact B1390315
  · exact B1390319
  · exact B1390323
  · exact B1390327
  · exact B1390331
  · exact B1390335
  · exact B1390339
  · exact B1390343
  · exact B1390347
  · exact B1390351
  · exact B1390355
  · exact B1390359
  · exact B1390363
  · exact B1390367
  · exact B1390371
  · exact B1390375
  · exact B1390379
  · exact B1390383
  · exact B1390387
  · exact B1390391
  · exact B1390395
  · exact B1390399
  · exact B1390403
  · exact B1390407
  · exact B1390411
  · exact B1390415
  · exact B1390419
  · exact B1390423
  · exact B1390427
  · exact B1390431
  · exact B1390435
  · exact B1390439
  · exact B1390443
  · exact B1390447
  · exact B1390451
  · exact B1390455
  · exact B1390459
  · exact B1390463
  · exact B1390467
  · exact B1390471
  · exact B1390475
  · exact B1390479
  · exact B1390483
  · exact B1390487
  · exact B1390491
  · exact B1390495
  · exact B1390499
  · exact B1390503
  · exact B1390507
  · exact B1390511
  · exact B1390515
  · exact B1390519
  · exact B1390523
  · exact B1390527
  · exact B1390531
  · exact B1390535
  · exact B1390539
  · exact B1390543
  · exact B1390547
  · exact B1390551
  · exact B1390555
  · exact B1390559
  · exact B1390563
  · exact B1390567
  · exact B1390571
  · exact B1390575
  · exact B1390579
  · exact B1390583
  · exact B1390587
  · exact B1390591
  · exact B1390595
  · exact B1390599
  · exact B1390603
  · exact B1390607
  · exact B1390611
  · exact B1390615
  · exact B1390619
  · exact B1390623
  · exact B1390627
  · exact B1390631
  · exact B1390635
  · exact B1390639
  · exact B1390643
  · exact B1390647
  · exact B1390651
  · exact B1390655
  · exact B1390659
  · exact B1390663
  · exact B1390667
  · exact B1390671
  · exact B1390675
  · exact B1390679
  · exact B1390683
  · exact B1390687
  · exact B1390691
  · exact B1390695
  · exact B1390699
  · exact B1390703
  · exact B1390707
  · exact B1390711
  · exact B1390715
  · exact B1390719
  · exact B1390723
  · exact B1390727
  · exact B1390731
  · exact B1390735
  · exact B1390739
  · exact B1390743
  · exact B1390747
  · exact B1390751
  · exact B1390755
  · exact B1390759
  · exact B1390763
  · exact B1390767
  · exact B1390771
  · exact B1390775
  · exact B1390779
  · exact B1390783
  · exact B1390787
  · exact B1390791
  · exact B1390795
  · exact B1390799
  · exact B1390803
  · exact B1390807
  · exact B1390811
  · exact B1390815
  · exact B1390819
  · exact B1390823
  · exact B1390827
  · exact B1390831
  · exact B1390835
  · exact B1390839
  · exact B1390843
  · exact B1390847
  · exact B1390851
  · exact B1390855
  · exact B1390859
  · exact B1390863
  · exact B1390867
  · exact B1390871
  · exact B1390875
  · exact B1390879
  · exact B1390883
  · exact B1390887
  · exact B1390891
  · exact B1390895
  · exact B1390899
  · exact B1390903
  · exact B1390907
  · exact B1390911
  · exact B1390915
  · exact B1390919
  · exact B1390923
  · exact B1390927
  · exact B1390931
  · exact B1390935
  · exact B1390939
  · exact B1390943
  · exact B1390947
  · exact B1390951
  · exact B1390955
  · exact B1390959
  · exact B1390963
  · exact B1390967
  · exact B1390971
  · exact B1390975
  · exact B1390979
  · exact B1390983
  · exact B1390987
  · exact B1390991
  · exact B1390995
  · exact B1390999
  · exact B1391003
  · exact B1391007
  · exact B1391011
  · exact B1391015
  · exact B1391019
  · exact B1391023
  · exact B1391027
  · exact B1391031
  · exact B1391035
  · exact B1391039
  · exact B1391043
  · exact B1391047
  · exact B1391051
  · exact B1391055
  · exact B1391059
  · exact B1391063
  · exact B1391067
  · exact B1391071
  · exact B1391075
  · exact B1391079
  · exact B1391083
  · exact B1391087
  · exact B1391091
  · exact B1391095
  · exact B1391099
  · exact B1391103
  · exact B1391107
  · exact B1391111
  · exact B1391115
  · exact B1391119
  · exact B1391123
  · exact B1391127
  · exact B1391131
  · exact B1391135
  · exact B1391139
  · exact B1391143
  · exact B1391147
  · exact B1391151
  · exact B1391155
  · exact B1391159
  · exact B1391163
  · exact B1391167
  · exact B1391171
  · exact B1391175
  · exact B1391179
  · exact B1391183
  · exact B1391187
  · exact B1391191
  · exact B1391195
  · exact B1391199
  · exact B1391203
  · exact B1391207
  · exact B1391211
  · exact B1391215
  · exact B1391219
  · exact B1391223
  · exact B1391227
  · exact B1391231
  · exact B1391235
  · exact B1391239
  · exact B1391243
  · exact B1391247
  · exact B1391251
  · exact B1391255
  · exact B1391259
  · exact B1391263
  · exact B1391267
  · exact B1391271
  · exact B1391275
  · exact B1391279
  · exact B1391283
  · exact B1391287
  · exact B1391291
  · exact B1391295
  · exact B1391299
  · exact B1391303
  · exact B1391307
  · exact B1391311
  · exact B1391315
  · exact B1391319
  · exact B1391323
  · exact B1391327
  · exact B1391331
  · exact B1391335
  · exact B1391339
  · exact B1391343
  · exact B1391347
  · exact B1391351
  · exact B1391355
  · exact B1391359
  · exact B1391363
  · exact B1391367
  · exact B1391371
  · exact B1391375
  · exact B1391379
  · exact B1391383
  · exact B1391387
  · exact B1391391
  · exact B1391395
  · exact B1391399
  · exact B1391403
  · exact B1391407
  · exact B1391411
  · exact B1391415
  · exact B1391419
  · exact B1391423
  · exact B1391427
  · exact B1391431
  · exact B1391435
  · exact B1391439
  · exact B1391443
  · exact B1391447
  · exact B1391451
  · exact B1391455
  · exact B1391459
  · exact B1391463
  · exact B1391467
  · exact B1391471
  · exact B1391475
  · exact B1391479
  · exact B1391483
  · exact B1391487
  · exact B1391491
  · exact B1391495
  · exact B1391499
  · exact B1391503
  · exact B1391507
  · exact B1391511

theorem solution (m : ℕ) (hlo : 1389514 ≤ m) (hhi : m ≤ 1391514) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 347378 ≤ j := by omega
    have hj2 : j ≤ 347877 := by omega
    have hb : Blo 1389514 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
