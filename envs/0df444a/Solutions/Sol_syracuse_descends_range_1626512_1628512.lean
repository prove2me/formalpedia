-- Prove2me | solution 1 for syracuse_descends_range_1626512_1628512
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:14:01.657307+00:00
-- url     : https://prove2.me/submissions/b18a3536-61af-4fe3-bdcc-0173c06b49ab

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


theorem B3661829 : Blo 1626512 3661829 := bbase (se 4 (by rfl) ⟨343296, by rfl⟩ : syracuseStep 3661829 = 686593) (by norm_num)
theorem B2441237 : Blo 1626512 2441237 := bbase (se 6 (by rfl) ⟨57216, by rfl⟩ : syracuseStep 2441237 = 114433) (by norm_num)
theorem B2441261 : Blo 1626512 2441261 := bbase (se 3 (by rfl) ⟨457736, by rfl⟩ : syracuseStep 2441261 = 915473) (by norm_num)
theorem B2441285 : Blo 1626512 2441285 := bbase (se 4 (by rfl) ⟨228870, by rfl⟩ : syracuseStep 2441285 = 457741) (by norm_num)
theorem B3661901 : Blo 1626512 3661901 := bbase (se 3 (by rfl) ⟨686606, by rfl⟩ : syracuseStep 3661901 = 1373213) (by norm_num)
theorem B3088469 : Blo 1626512 3088469 := bbase (se 8 (by rfl) ⟨18096, by rfl⟩ : syracuseStep 3088469 = 36193) (by norm_num)
theorem B2441309 : Blo 1626512 2441309 := bbase (se 3 (by rfl) ⟨457745, by rfl⟩ : syracuseStep 2441309 = 915491) (by norm_num)
theorem B2441333 : Blo 1626512 2441333 := bbase (se 5 (by rfl) ⟨114437, by rfl⟩ : syracuseStep 2441333 = 228875) (by norm_num)
theorem B2441357 : Blo 1626512 2441357 := bbase (se 3 (by rfl) ⟨457754, by rfl⟩ : syracuseStep 2441357 = 915509) (by norm_num)
theorem B3661973 : Blo 1626512 3661973 := bbase (se 6 (by rfl) ⟨85827, by rfl⟩ : syracuseStep 3661973 = 171655) (by norm_num)
theorem B4120733 : Blo 1626512 4120733 := bbase (se 3 (by rfl) ⟨772637, by rfl⟩ : syracuseStep 4120733 = 1545275) (by norm_num)
theorem B2441381 : Blo 1626512 2441381 := bbase (se 4 (by rfl) ⟨228879, by rfl⟩ : syracuseStep 2441381 = 457759) (by norm_num)
theorem B2441405 : Blo 1626512 2441405 := bbase (se 3 (by rfl) ⟨457763, by rfl⟩ : syracuseStep 2441405 = 915527) (by norm_num)
theorem B2441429 : Blo 1626512 2441429 := bbase (se 7 (by rfl) ⟨28610, by rfl⟩ : syracuseStep 2441429 = 57221) (by norm_num)
theorem B7823573 : Blo 1626512 7823573 := bbase (se 7 (by rfl) ⟨91682, by rfl⟩ : syracuseStep 7823573 = 183365) (by norm_num)
theorem B4636885 : Blo 1626512 4636885 := bbase (se 7 (by rfl) ⟨54338, by rfl⟩ : syracuseStep 4636885 = 108677) (by norm_num)
theorem B3662045 : Blo 1626512 3662045 := bbase (se 3 (by rfl) ⟨686633, by rfl⟩ : syracuseStep 3662045 = 1373267) (by norm_num)
theorem B3088621 : Blo 1626512 3088621 := bbase (se 3 (by rfl) ⟨579116, by rfl⟩ : syracuseStep 3088621 = 1158233) (by norm_num)
theorem B2441453 : Blo 1626512 2441453 := bbase (se 3 (by rfl) ⟨457772, by rfl⟩ : syracuseStep 2441453 = 915545) (by norm_num)
theorem B2441477 : Blo 1626512 2441477 := bbase (se 4 (by rfl) ⟨228888, by rfl⟩ : syracuseStep 2441477 = 457777) (by norm_num)
theorem B2441501 : Blo 1626512 2441501 := bbase (se 3 (by rfl) ⟨457781, by rfl⟩ : syracuseStep 2441501 = 915563) (by norm_num)
theorem B3662117 : Blo 1626512 3662117 := bbase (se 4 (by rfl) ⟨343323, by rfl⟩ : syracuseStep 3662117 = 686647) (by norm_num)
theorem B2441525 : Blo 1626512 2441525 := bbase (se 5 (by rfl) ⟨114446, by rfl⟩ : syracuseStep 2441525 = 228893) (by norm_num)
theorem B2318653 : Blo 1626512 2318653 := bbase (se 3 (by rfl) ⟨434747, by rfl⟩ : syracuseStep 2318653 = 869495) (by norm_num)
theorem B2441549 : Blo 1626512 2441549 := bbase (se 3 (by rfl) ⟨457790, by rfl⟩ : syracuseStep 2441549 = 915581) (by norm_num)
theorem B2441573 : Blo 1626512 2441573 := bbase (se 4 (by rfl) ⟨228897, by rfl⟩ : syracuseStep 2441573 = 457795) (by norm_num)
theorem B3662189 : Blo 1626512 3662189 := bbase (se 3 (by rfl) ⟨686660, by rfl⟩ : syracuseStep 3662189 = 1373321) (by norm_num)
theorem B2441597 : Blo 1626512 2441597 := bbase (se 3 (by rfl) ⟨457799, by rfl⟩ : syracuseStep 2441597 = 915599) (by norm_num)
theorem B2441621 : Blo 1626512 2441621 := bbase (se 6 (by rfl) ⟨57225, by rfl⟩ : syracuseStep 2441621 = 114451) (by norm_num)
theorem B3473837 : Blo 1626512 3473837 := bbase (se 3 (by rfl) ⟨651344, by rfl⟩ : syracuseStep 3473837 = 1302689) (by norm_num)
theorem B2441645 : Blo 1626512 2441645 := bbase (se 3 (by rfl) ⟨457808, by rfl⟩ : syracuseStep 2441645 = 915617) (by norm_num)
theorem B3662261 : Blo 1626512 3662261 := bbase (se 5 (by rfl) ⟨171668, by rfl⟩ : syracuseStep 3662261 = 343337) (by norm_num)
theorem B2441669 : Blo 1626512 2441669 := bbase (se 4 (by rfl) ⟨228906, by rfl⟩ : syracuseStep 2441669 = 457813) (by norm_num)
theorem B2441693 : Blo 1626512 2441693 := bbase (se 3 (by rfl) ⟨457817, by rfl⟩ : syracuseStep 2441693 = 915635) (by norm_num)
theorem B2744813 : Blo 1626512 2744813 := bbase (se 3 (by rfl) ⟨514652, by rfl⟩ : syracuseStep 2744813 = 1029305) (by norm_num)
theorem B3523061 : Blo 1626512 3523061 := bbase (se 5 (by rfl) ⟨165143, by rfl⟩ : syracuseStep 3523061 = 330287) (by norm_num)
theorem B2441717 : Blo 1626512 2441717 := bbase (se 5 (by rfl) ⟨114455, by rfl⟩ : syracuseStep 2441717 = 228911) (by norm_num)
theorem B4121077 : Blo 1626512 4121077 := bbase (se 5 (by rfl) ⟨193175, by rfl⟩ : syracuseStep 4121077 = 386351) (by norm_num)
theorem B3662333 : Blo 1626512 3662333 := bbase (se 3 (by rfl) ⟨686687, by rfl⟩ : syracuseStep 3662333 = 1373375) (by norm_num)
theorem B2441741 : Blo 1626512 2441741 := bbase (se 3 (by rfl) ⟨457826, by rfl⟩ : syracuseStep 2441741 = 915653) (by norm_num)
theorem B2605589 : Blo 1626512 2605589 := bbase (se 6 (by rfl) ⟨61068, by rfl⟩ : syracuseStep 2605589 = 122137) (by norm_num)
theorem B3088925 : Blo 1626512 3088925 := bbase (se 3 (by rfl) ⟨579173, by rfl⟩ : syracuseStep 3088925 = 1158347) (by norm_num)
theorem B2441765 : Blo 1626512 2441765 := bbase (se 4 (by rfl) ⟨228915, by rfl⟩ : syracuseStep 2441765 = 457831) (by norm_num)
theorem B2441789 : Blo 1626512 2441789 := bbase (se 3 (by rfl) ⟨457835, by rfl⟩ : syracuseStep 2441789 = 915671) (by norm_num)
theorem B3662405 : Blo 1626512 3662405 := bbase (se 4 (by rfl) ⟨343350, by rfl⟩ : syracuseStep 3662405 = 686701) (by norm_num)
theorem B2441813 : Blo 1626512 2441813 := bbase (se 8 (by rfl) ⟨14307, by rfl⟩ : syracuseStep 2441813 = 28615) (by norm_num)
theorem B8241749 : Blo 1626512 8241749 := bbase (se 8 (by rfl) ⟨48291, by rfl⟩ : syracuseStep 8241749 = 96583) (by norm_num)
theorem B4121189 : Blo 1626512 4121189 := bbase (se 4 (by rfl) ⟨386361, by rfl⟩ : syracuseStep 4121189 = 772723) (by norm_num)
theorem B2744941 : Blo 1626512 2744941 := bbase (se 3 (by rfl) ⟨514676, by rfl⟩ : syracuseStep 2744941 = 1029353) (by norm_num)
theorem B2441837 : Blo 1626512 2441837 := bbase (se 3 (by rfl) ⟨457844, by rfl⟩ : syracuseStep 2441837 = 915689) (by norm_num)
theorem B9273973 : Blo 1626512 9273973 := bbase (se 5 (by rfl) ⟨434717, by rfl⟩ : syracuseStep 9273973 = 869435) (by norm_num)
theorem B2441861 : Blo 1626512 2441861 := bbase (se 4 (by rfl) ⟨228924, by rfl⟩ : syracuseStep 2441861 = 457849) (by norm_num)
theorem B3662477 : Blo 1626512 3662477 := bbase (se 3 (by rfl) ⟨686714, by rfl⟩ : syracuseStep 3662477 = 1373429) (by norm_num)
theorem B2605717 : Blo 1626512 2605717 := bbase (se 6 (by rfl) ⟨61071, by rfl⟩ : syracuseStep 2605717 = 122143) (by norm_num)
theorem B2441885 : Blo 1626512 2441885 := bbase (se 3 (by rfl) ⟨457853, by rfl⟩ : syracuseStep 2441885 = 915707) (by norm_num)
theorem B1737397 : Blo 1626512 1737397 := bbase (se 5 (by rfl) ⟨81440, by rfl⟩ : syracuseStep 1737397 = 162881) (by norm_num)
theorem B2441909 : Blo 1626512 2441909 := bbase (se 5 (by rfl) ⟨114464, by rfl⟩ : syracuseStep 2441909 = 228929) (by norm_num)
theorem B2745029 : Blo 1626512 2745029 := bbase (se 4 (by rfl) ⟨257346, by rfl⟩ : syracuseStep 2745029 = 514693) (by norm_num)
theorem B2441933 : Blo 1626512 2441933 := bbase (se 3 (by rfl) ⟨457862, by rfl⟩ : syracuseStep 2441933 = 915725) (by norm_num)
theorem B3662549 : Blo 1626512 3662549 := bbase (se 7 (by rfl) ⟨42920, by rfl⟩ : syracuseStep 3662549 = 85841) (by norm_num)
theorem B2441957 : Blo 1626512 2441957 := bbase (se 4 (by rfl) ⟨228933, by rfl⟩ : syracuseStep 2441957 = 457867) (by norm_num)
theorem B1737469 : Blo 1626512 1737469 := bbase (se 3 (by rfl) ⟨325775, by rfl⟩ : syracuseStep 1737469 = 651551) (by norm_num)
theorem B2441981 : Blo 1626512 2441981 := bbase (se 3 (by rfl) ⟨457871, by rfl⟩ : syracuseStep 2441981 = 915743) (by norm_num)
theorem B2442005 : Blo 1626512 2442005 := bbase (se 6 (by rfl) ⟨57234, by rfl⟩ : syracuseStep 2442005 = 114469) (by norm_num)
theorem B3662621 : Blo 1626512 3662621 := bbase (se 3 (by rfl) ⟨686741, by rfl⟩ : syracuseStep 3662621 = 1373483) (by norm_num)
theorem B4121381 : Blo 1626512 4121381 := bbase (se 4 (by rfl) ⟨386379, by rfl⟩ : syracuseStep 4121381 = 772759) (by norm_num)
theorem B2442029 : Blo 1626512 2442029 := bbase (se 3 (by rfl) ⟨457880, by rfl⟩ : syracuseStep 2442029 = 915761) (by norm_num)
theorem B8356661 : Blo 1626512 8356661 := bbase (se 5 (by rfl) ⟨391718, by rfl⟩ : syracuseStep 8356661 = 783437) (by norm_num)
theorem B2745157 : Blo 1626512 2745157 := bbase (se 4 (by rfl) ⟨257358, by rfl⟩ : syracuseStep 2745157 = 514717) (by norm_num)
theorem B2442053 : Blo 1626512 2442053 := bbase (se 4 (by rfl) ⟨228942, by rfl⟩ : syracuseStep 2442053 = 457885) (by norm_num)
theorem B2442077 : Blo 1626512 2442077 := bbase (se 3 (by rfl) ⟨457889, by rfl⟩ : syracuseStep 2442077 = 915779) (by norm_num)
theorem B3662693 : Blo 1626512 3662693 := bbase (se 4 (by rfl) ⟨343377, by rfl⟩ : syracuseStep 3662693 = 686755) (by norm_num)
theorem B6177653 : Blo 1626512 6177653 := bbase (se 5 (by rfl) ⟨289577, by rfl⟩ : syracuseStep 6177653 = 579155) (by norm_num)
theorem B2442101 : Blo 1626512 2442101 := bbase (se 5 (by rfl) ⟨114473, by rfl⟩ : syracuseStep 2442101 = 228947) (by norm_num)
theorem B2442125 : Blo 1626512 2442125 := bbase (se 3 (by rfl) ⟨457898, by rfl⟩ : syracuseStep 2442125 = 915797) (by norm_num)
theorem B2745245 : Blo 1626512 2745245 := bbase (se 3 (by rfl) ⟨514733, by rfl⟩ : syracuseStep 2745245 = 1029467) (by norm_num)
theorem B2442149 : Blo 1626512 2442149 := bbase (se 4 (by rfl) ⟨228951, by rfl⟩ : syracuseStep 2442149 = 457903) (by norm_num)
theorem B3662765 : Blo 1626512 3662765 := bbase (se 3 (by rfl) ⟨686768, by rfl⟩ : syracuseStep 3662765 = 1373537) (by norm_num)
theorem B1737649 : Blo 1626512 1737649 := bbase (se 2 (by rfl) ⟨651618, by rfl⟩ : syracuseStep 1737649 = 1303237) (by norm_num)
theorem B6783925 : Blo 1626512 6783925 := bbase (se 5 (by rfl) ⟨317996, by rfl⟩ : syracuseStep 6783925 = 635993) (by norm_num)
theorem B2442173 : Blo 1626512 2442173 := bbase (se 3 (by rfl) ⟨457907, by rfl⟩ : syracuseStep 2442173 = 915815) (by norm_num)
theorem B35652565 : Blo 1626512 35652565 := bbase (se 7 (by rfl) ⟨417803, by rfl⟩ : syracuseStep 35652565 = 835607) (by norm_num)
theorem B2442197 : Blo 1626512 2442197 := bbase (se 7 (by rfl) ⟨28619, by rfl⟩ : syracuseStep 2442197 = 57239) (by norm_num)
theorem B2442221 : Blo 1626512 2442221 := bbase (se 3 (by rfl) ⟨457916, by rfl⟩ : syracuseStep 2442221 = 915833) (by norm_num)
theorem B3662837 : Blo 1626512 3662837 := bbase (se 5 (by rfl) ⟨171695, by rfl⟩ : syracuseStep 3662837 = 343391) (by norm_num)
theorem B2442245 : Blo 1626512 2442245 := bbase (se 4 (by rfl) ⟨228960, by rfl⟩ : syracuseStep 2442245 = 457921) (by norm_num)
theorem B2745373 : Blo 1626512 2745373 := bbase (se 3 (by rfl) ⟨514757, by rfl⟩ : syracuseStep 2745373 = 1029515) (by norm_num)
theorem B2442269 : Blo 1626512 2442269 := bbase (se 3 (by rfl) ⟨457925, by rfl⟩ : syracuseStep 2442269 = 915851) (by norm_num)
theorem B2442293 : Blo 1626512 2442293 := bbase (se 5 (by rfl) ⟨114482, by rfl⟩ : syracuseStep 2442293 = 228965) (by norm_num)
theorem B3662909 : Blo 1626512 3662909 := bbase (se 3 (by rfl) ⟨686795, by rfl⟩ : syracuseStep 3662909 = 1373591) (by norm_num)
theorem B2442317 : Blo 1626512 2442317 := bbase (se 3 (by rfl) ⟨457934, by rfl⟩ : syracuseStep 2442317 = 915869) (by norm_num)
theorem B2442341 : Blo 1626512 2442341 := bbase (se 4 (by rfl) ⟨228969, by rfl⟩ : syracuseStep 2442341 = 457939) (by norm_num)
theorem B2745461 : Blo 1626512 2745461 := bbase (se 5 (by rfl) ⟨128693, by rfl⟩ : syracuseStep 2745461 = 257387) (by norm_num)
theorem B2442365 : Blo 1626512 2442365 := bbase (se 3 (by rfl) ⟨457943, by rfl⟩ : syracuseStep 2442365 = 915887) (by norm_num)
theorem B4121725 : Blo 1626512 4121725 := bbase (se 3 (by rfl) ⟨772823, by rfl⟩ : syracuseStep 4121725 = 1545647) (by norm_num)
theorem B3662981 : Blo 1626512 3662981 := bbase (se 4 (by rfl) ⟨343404, by rfl⟩ : syracuseStep 3662981 = 686809) (by norm_num)
theorem B6177941 : Blo 1626512 6177941 := bbase (se 6 (by rfl) ⟨144795, by rfl⟩ : syracuseStep 6177941 = 289591) (by norm_num)
theorem B2442389 : Blo 1626512 2442389 := bbase (se 6 (by rfl) ⟨57243, by rfl⟩ : syracuseStep 2442389 = 114487) (by norm_num)
theorem B3474589 : Blo 1626512 3474589 := bbase (se 3 (by rfl) ⟨651485, by rfl⟩ : syracuseStep 3474589 = 1302971) (by norm_num)
theorem B2442413 : Blo 1626512 2442413 := bbase (se 3 (by rfl) ⟨457952, by rfl⟩ : syracuseStep 2442413 = 915905) (by norm_num)
theorem B2933941 : Blo 1626512 2933941 := bbase (se 5 (by rfl) ⟨137528, by rfl⟩ : syracuseStep 2933941 = 275057) (by norm_num)
theorem B9659573 : Blo 1626512 9659573 := bbase (se 5 (by rfl) ⟨452792, by rfl⟩ : syracuseStep 9659573 = 905585) (by norm_num)
theorem B2442437 : Blo 1626512 2442437 := bbase (se 4 (by rfl) ⟨228978, by rfl⟩ : syracuseStep 2442437 = 457957) (by norm_num)
theorem B3663053 : Blo 1626512 3663053 := bbase (se 3 (by rfl) ⟨686822, by rfl⟩ : syracuseStep 3663053 = 1373645) (by norm_num)
theorem B2442461 : Blo 1626512 2442461 := bbase (se 3 (by rfl) ⟨457961, by rfl⟩ : syracuseStep 2442461 = 915923) (by norm_num)
theorem B4121837 : Blo 1626512 4121837 := bbase (se 3 (by rfl) ⟨772844, by rfl⟩ : syracuseStep 4121837 = 1545689) (by norm_num)
theorem B5489909 : Blo 1626512 5489909 := bbase (se 5 (by rfl) ⟨257339, by rfl⟩ : syracuseStep 5489909 = 514679) (by norm_num)
theorem B2745589 : Blo 1626512 2745589 := bbase (se 5 (by rfl) ⟨128699, by rfl⟩ : syracuseStep 2745589 = 257399) (by norm_num)
theorem B2442485 : Blo 1626512 2442485 := bbase (se 5 (by rfl) ⟨114491, by rfl⟩ : syracuseStep 2442485 = 228983) (by norm_num)
theorem B3089677 : Blo 1626512 3089677 := bbase (se 3 (by rfl) ⟨579314, by rfl⟩ : syracuseStep 3089677 = 1158629) (by norm_num)
theorem B2442509 : Blo 1626512 2442509 := bbase (se 3 (by rfl) ⟨457970, by rfl⟩ : syracuseStep 2442509 = 915941) (by norm_num)
theorem B3663125 : Blo 1626512 3663125 := bbase (se 6 (by rfl) ⟨85854, by rfl⟩ : syracuseStep 3663125 = 171709) (by norm_num)
theorem B2442533 : Blo 1626512 2442533 := bbase (se 4 (by rfl) ⟨228987, by rfl⟩ : syracuseStep 2442533 = 457975) (by norm_num)
theorem B3474733 : Blo 1626512 3474733 := bbase (se 3 (by rfl) ⟨651512, by rfl⟩ : syracuseStep 3474733 = 1303025) (by norm_num)
theorem B2442557 : Blo 1626512 2442557 := bbase (se 3 (by rfl) ⟨457979, by rfl⟩ : syracuseStep 2442557 = 915959) (by norm_num)
theorem B2934085 : Blo 1626512 2934085 := bbase (se 4 (by rfl) ⟨275070, by rfl⟩ : syracuseStep 2934085 = 550141) (by norm_num)
theorem B2745677 : Blo 1626512 2745677 := bbase (se 3 (by rfl) ⟨514814, by rfl⟩ : syracuseStep 2745677 = 1029629) (by norm_num)
theorem B2442581 : Blo 1626512 2442581 := bbase (se 12 (by rfl) ⟨894, by rfl⟩ : syracuseStep 2442581 = 1789) (by norm_num)
theorem B3663197 : Blo 1626512 3663197 := bbase (se 3 (by rfl) ⟨686849, by rfl⟩ : syracuseStep 3663197 = 1373699) (by norm_num)
theorem B1738093 : Blo 1626512 1738093 := bbase (se 3 (by rfl) ⟨325892, by rfl⟩ : syracuseStep 1738093 = 651785) (by norm_num)
theorem B2442605 : Blo 1626512 2442605 := bbase (se 3 (by rfl) ⟨457988, by rfl⟩ : syracuseStep 2442605 = 915977) (by norm_num)
theorem B3908989 : Blo 1626512 3908989 := bbase (se 3 (by rfl) ⟨732935, by rfl⟩ : syracuseStep 3908989 = 1465871) (by norm_num)
theorem B2442629 : Blo 1626512 2442629 := bbase (se 4 (by rfl) ⟨228996, by rfl⟩ : syracuseStep 2442629 = 457993) (by norm_num)
theorem B5866901 : Blo 1626512 5866901 := bbase (se 6 (by rfl) ⟨137505, by rfl⟩ : syracuseStep 5866901 = 275011) (by norm_num)
theorem B3089821 : Blo 1626512 3089821 := bbase (se 3 (by rfl) ⟨579341, by rfl⟩ : syracuseStep 3089821 = 1158683) (by norm_num)
theorem B2442653 : Blo 1626512 2442653 := bbase (se 3 (by rfl) ⟨457997, by rfl⟩ : syracuseStep 2442653 = 915995) (by norm_num)
theorem B3663269 : Blo 1626512 3663269 := bbase (se 4 (by rfl) ⟨343431, by rfl⟩ : syracuseStep 3663269 = 686863) (by norm_num)
theorem B4122029 : Blo 1626512 4122029 := bbase (se 3 (by rfl) ⟨772880, by rfl⟩ : syracuseStep 4122029 = 1545761) (by norm_num)
theorem B2442677 : Blo 1626512 2442677 := bbase (se 5 (by rfl) ⟨114500, by rfl⟩ : syracuseStep 2442677 = 229001) (by norm_num)
theorem B2745805 : Blo 1626512 2745805 := bbase (se 3 (by rfl) ⟨514838, by rfl⟩ : syracuseStep 2745805 = 1029677) (by norm_num)
theorem B2442701 : Blo 1626512 2442701 := bbase (se 3 (by rfl) ⟨458006, by rfl⟩ : syracuseStep 2442701 = 916013) (by norm_num)
theorem B2442725 : Blo 1626512 2442725 := bbase (se 4 (by rfl) ⟨229005, by rfl⟩ : syracuseStep 2442725 = 458011) (by norm_num)
theorem B1738217 : Blo 1626512 1738217 := bbase (se 2 (by rfl) ⟨651831, by rfl⟩ : syracuseStep 1738217 = 1303663) (by norm_num)
theorem B3663341 : Blo 1626512 3663341 := bbase (se 3 (by rfl) ⟨686876, by rfl⟩ : syracuseStep 3663341 = 1373753) (by norm_num)
theorem B2442749 : Blo 1626512 2442749 := bbase (se 3 (by rfl) ⟨458015, by rfl⟩ : syracuseStep 2442749 = 916031) (by norm_num)
theorem B2934301 : Blo 1626512 2934301 := bbase (se 3 (by rfl) ⟨550181, by rfl⟩ : syracuseStep 2934301 = 1100363) (by norm_num)
theorem B2745893 : Blo 1626512 2745893 := bbase (se 4 (by rfl) ⟨257427, by rfl⟩ : syracuseStep 2745893 = 514855) (by norm_num)
theorem B3663413 : Blo 1626512 3663413 := bbase (se 5 (by rfl) ⟨171722, by rfl⟩ : syracuseStep 3663413 = 343445) (by norm_num)
theorem B3089981 : Blo 1626512 3089981 := bbase (se 3 (by rfl) ⟨579371, by rfl⟩ : syracuseStep 3089981 = 1158743) (by norm_num)
theorem B2475605 : Blo 1626512 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B2606717 : Blo 1626512 2606717 := bbase (se 3 (by rfl) ⟨488759, by rfl⟩ : syracuseStep 2606717 = 977519) (by norm_num)
theorem B3663485 : Blo 1626512 3663485 := bbase (se 3 (by rfl) ⟨686903, by rfl⟩ : syracuseStep 3663485 = 1373807) (by norm_num)
theorem B5490341 : Blo 1626512 5490341 := bbase (se 4 (by rfl) ⟨514719, by rfl⟩ : syracuseStep 5490341 = 1029439) (by norm_num)
theorem B3475109 : Blo 1626512 3475109 := bbase (se 4 (by rfl) ⟨325791, by rfl⟩ : syracuseStep 3475109 = 651583) (by norm_num)
theorem B2746021 : Blo 1626512 2746021 := bbase (se 4 (by rfl) ⟨257439, by rfl⟩ : syracuseStep 2746021 = 514879) (by norm_num)
theorem B3663557 : Blo 1626512 3663557 := bbase (se 4 (by rfl) ⟨343458, by rfl⟩ : syracuseStep 3663557 = 686917) (by norm_num)
theorem B3090125 : Blo 1626512 3090125 := bbase (se 3 (by rfl) ⟨579398, by rfl⟩ : syracuseStep 3090125 = 1158797) (by norm_num)
theorem B17589973 : Blo 1626512 17589973 := bbase (se 7 (by rfl) ⟨206132, by rfl⟩ : syracuseStep 17589973 = 412265) (by norm_num)
theorem B1738469 : Blo 1626512 1738469 := bbase (se 4 (by rfl) ⟨162981, by rfl⟩ : syracuseStep 1738469 = 325963) (by norm_num)
theorem B2746109 : Blo 1626512 2746109 := bbase (se 3 (by rfl) ⟨514895, by rfl⟩ : syracuseStep 2746109 = 1029791) (by norm_num)
theorem B2606845 : Blo 1626512 2606845 := bbase (se 3 (by rfl) ⟨488783, by rfl⟩ : syracuseStep 2606845 = 977567) (by norm_num)
theorem B3663629 : Blo 1626512 3663629 := bbase (se 3 (by rfl) ⟨686930, by rfl⟩ : syracuseStep 3663629 = 1373861) (by norm_num)
theorem B6596437 : Blo 1626512 6596437 := bbase (se 9 (by rfl) ⟨19325, by rfl⟩ : syracuseStep 6596437 = 38651) (by norm_num)
theorem B3663701 : Blo 1626512 3663701 := bbase (se 9 (by rfl) ⟨10733, by rfl⟩ : syracuseStep 3663701 = 21467) (by norm_num)
theorem B8243045 : Blo 1626512 8243045 := bbase (se 4 (by rfl) ⟨772785, by rfl⟩ : syracuseStep 8243045 = 1545571) (by norm_num)
theorem B2746237 : Blo 1626512 2746237 := bbase (se 3 (by rfl) ⟨514919, by rfl⟩ : syracuseStep 2746237 = 1029839) (by norm_num)
theorem B3663773 : Blo 1626512 3663773 := bbase (se 3 (by rfl) ⟨686957, by rfl⟩ : syracuseStep 3663773 = 1373915) (by norm_num)
theorem B2746325 : Blo 1626512 2746325 := bbase (se 7 (by rfl) ⟨32183, by rfl⟩ : syracuseStep 2746325 = 64367) (by norm_num)
theorem B3663845 : Blo 1626512 3663845 := bbase (se 4 (by rfl) ⟨343485, by rfl⟩ : syracuseStep 3663845 = 686971) (by norm_num)
theorem B3090413 : Blo 1626512 3090413 := bbase (se 3 (by rfl) ⟨579452, by rfl⟩ : syracuseStep 3090413 = 1158905) (by norm_num)
theorem B3909653 : Blo 1626512 3909653 := bbase (se 6 (by rfl) ⟨91632, by rfl⟩ : syracuseStep 3909653 = 183265) (by norm_num)
theorem B3475477 : Blo 1626512 3475477 := bbase (se 6 (by rfl) ⟨81456, by rfl⟩ : syracuseStep 3475477 = 162913) (by norm_num)
theorem B3663917 : Blo 1626512 3663917 := bbase (se 3 (by rfl) ⟨686984, by rfl⟩ : syracuseStep 3663917 = 1373969) (by norm_num)
theorem B5490773 : Blo 1626512 5490773 := bbase (se 8 (by rfl) ⟨32172, by rfl⟩ : syracuseStep 5490773 = 64345) (by norm_num)
theorem B2746453 : Blo 1626512 2746453 := bbase (se 8 (by rfl) ⟨16092, by rfl⟩ : syracuseStep 2746453 = 32185) (by norm_num)
theorem B11724917 : Blo 1626512 11724917 := bbase (se 5 (by rfl) ⟨549605, by rfl⟩ : syracuseStep 11724917 = 1099211) (by norm_num)
theorem B3663989 : Blo 1626512 3663989 := bbase (se 5 (by rfl) ⟨171749, by rfl⟩ : syracuseStep 3663989 = 343499) (by norm_num)
theorem B2607229 : Blo 1626512 2607229 := bbase (se 3 (by rfl) ⟨488855, by rfl⟩ : syracuseStep 2607229 = 977711) (by norm_num)
theorem B3090565 : Blo 1626512 3090565 := bbase (se 4 (by rfl) ⟨289740, by rfl⟩ : syracuseStep 3090565 = 579481) (by norm_num)
theorem B2508941 : Blo 1626512 2508941 := bbase (se 3 (by rfl) ⟨470426, by rfl⟩ : syracuseStep 2508941 = 940853) (by norm_num)
theorem B4696213 : Blo 1626512 4696213 := bbase (se 6 (by rfl) ⟨110067, by rfl⟩ : syracuseStep 4696213 = 220135) (by norm_num)
theorem B1648793 : Blo 1626512 1648793 := bbase (se 2 (by rfl) ⟨618297, by rfl⟩ : syracuseStep 1648793 = 1236595) (by norm_num)
theorem B1738913 : Blo 1626512 1738913 := bbase (se 2 (by rfl) ⟨652092, by rfl⟩ : syracuseStep 1738913 = 1304185) (by norm_num)
theorem B7817381 : Blo 1626512 7817381 := bbase (se 4 (by rfl) ⟨732879, by rfl⟩ : syracuseStep 7817381 = 1465759) (by norm_num)
theorem B2746541 : Blo 1626512 2746541 := bbase (se 3 (by rfl) ⟨514976, by rfl⟩ : syracuseStep 2746541 = 1029953) (by norm_num)
theorem B3664061 : Blo 1626512 3664061 := bbase (se 3 (by rfl) ⟨687011, by rfl⟩ : syracuseStep 3664061 = 1374023) (by norm_num)
theorem B5867765 : Blo 1626512 5867765 := bbase (se 5 (by rfl) ⟨275051, by rfl⟩ : syracuseStep 5867765 = 550103) (by norm_num)
theorem B8235269 : Blo 1626512 8235269 := bbase (se 4 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 8235269 = 1544113) (by norm_num)
theorem B3664133 : Blo 1626512 3664133 := bbase (se 4 (by rfl) ⟨343512, by rfl⟩ : syracuseStep 3664133 = 687025) (by norm_num)
theorem B2746669 : Blo 1626512 2746669 := bbase (se 3 (by rfl) ⟨515000, by rfl⟩ : syracuseStep 2746669 = 1030001) (by norm_num)
theorem B3909941 : Blo 1626512 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B6179125 : Blo 1626512 6179125 := bbase (se 5 (by rfl) ⟨289646, by rfl⟩ : syracuseStep 6179125 = 579293) (by norm_num)
theorem B2607485 : Blo 1626512 2607485 := bbase (se 3 (by rfl) ⟨488903, by rfl⟩ : syracuseStep 2607485 = 977807) (by norm_num)
theorem B2058625 : Blo 1626512 2058625 := bbase (se 2 (by rfl) ⟨771984, by rfl⟩ : syracuseStep 2058625 = 1543969) (by norm_num)
theorem B2746757 : Blo 1626512 2746757 := bbase (se 4 (by rfl) ⟨257508, by rfl⟩ : syracuseStep 2746757 = 515017) (by norm_num)
theorem B3090869 : Blo 1626512 3090869 := bbase (se 5 (by rfl) ⟨144884, by rfl⟩ : syracuseStep 3090869 = 289769) (by norm_num)
theorem B5212613 : Blo 1626512 5212613 := bbase (se 4 (by rfl) ⟨488682, by rfl⟩ : syracuseStep 5212613 = 977365) (by norm_num)
theorem B5491205 : Blo 1626512 5491205 := bbase (se 4 (by rfl) ⟨514800, by rfl⟩ : syracuseStep 5491205 = 1029601) (by norm_num)
theorem B2746885 : Blo 1626512 2746885 := bbase (se 4 (by rfl) ⟨257520, by rfl⟩ : syracuseStep 2746885 = 515041) (by norm_num)
theorem B5286421 : Blo 1626512 5286421 := bbase (se 6 (by rfl) ⟨123900, by rfl⟩ : syracuseStep 5286421 = 247801) (by norm_num)
theorem B2058797 : Blo 1626512 2058797 := bbase (se 3 (by rfl) ⟨386024, by rfl⟩ : syracuseStep 2058797 = 772049) (by norm_num)
theorem B2746973 : Blo 1626512 2746973 := bbase (se 3 (by rfl) ⟨515057, by rfl⟩ : syracuseStep 2746973 = 1030115) (by norm_num)
theorem B2058853 : Blo 1626512 2058853 := bbase (se 4 (by rfl) ⟨193017, by rfl⟩ : syracuseStep 2058853 = 386035) (by norm_num)
theorem B6179429 : Blo 1626512 6179429 := bbase (se 4 (by rfl) ⟨579321, by rfl⟩ : syracuseStep 6179429 = 1158643) (by norm_num)
theorem B2058949 : Blo 1626512 2058949 := bbase (se 4 (by rfl) ⟨193026, by rfl⟩ : syracuseStep 2058949 = 386053) (by norm_num)
theorem B2747101 : Blo 1626512 2747101 := bbase (se 3 (by rfl) ⟨515081, by rfl⟩ : syracuseStep 2747101 = 1030163) (by norm_num)
theorem B2747189 : Blo 1626512 2747189 := bbase (se 5 (by rfl) ⟨128774, by rfl⟩ : syracuseStep 2747189 = 257549) (by norm_num)
theorem B2009933 : Blo 1626512 2009933 := bbase (se 3 (by rfl) ⟨376862, by rfl⟩ : syracuseStep 2009933 = 753725) (by norm_num)
theorem B2059121 : Blo 1626512 2059121 := bbase (se 2 (by rfl) ⟨772170, by rfl⟩ : syracuseStep 2059121 = 1544341) (by norm_num)
theorem B2059177 : Blo 1626512 2059177 := bbase (se 2 (by rfl) ⟨772191, by rfl⟩ : syracuseStep 2059177 = 1544383) (by norm_num)
theorem B5491637 : Blo 1626512 5491637 := bbase (se 5 (by rfl) ⟨257420, by rfl⟩ : syracuseStep 5491637 = 514841) (by norm_num)
theorem B5721013 : Blo 1626512 5721013 := bbase (se 5 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 5721013 = 536345) (by norm_num)
theorem B2747317 : Blo 1626512 2747317 := bbase (se 5 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 2747317 = 257561) (by norm_num)
theorem B20843477 : Blo 1626512 20843477 := bbase (se 7 (by rfl) ⟨244259, by rfl⟩ : syracuseStep 20843477 = 488519) (by norm_num)
theorem B1829857 : Blo 1626512 1829857 := bbase (se 2 (by rfl) ⟨686196, by rfl⟩ : syracuseStep 1829857 = 1372393) (by norm_num)
theorem B2116589 : Blo 1626512 2116589 := bbase (se 3 (by rfl) ⟨396860, by rfl⟩ : syracuseStep 2116589 = 793721) (by norm_num)
theorem B1829893 : Blo 1626512 1829893 := bbase (se 4 (by rfl) ⟨171552, by rfl⟩ : syracuseStep 1829893 = 343105) (by norm_num)
theorem B2059273 : Blo 1626512 2059273 := bbase (se 2 (by rfl) ⟨772227, by rfl⟩ : syracuseStep 2059273 = 1544455) (by norm_num)
theorem B2747405 : Blo 1626512 2747405 := bbase (se 3 (by rfl) ⟨515138, by rfl⟩ : syracuseStep 2747405 = 1030277) (by norm_num)
theorem B1649701 : Blo 1626512 1649701 := bbase (se 4 (by rfl) ⟨154659, by rfl⟩ : syracuseStep 1649701 = 309319) (by norm_num)
theorem B1829929 : Blo 1626512 1829929 := bbase (se 2 (by rfl) ⟨686223, by rfl⟩ : syracuseStep 1829929 = 1372447) (by norm_num)
theorem B1829965 : Blo 1626512 1829965 := bbase (se 3 (by rfl) ⟨343118, by rfl⟩ : syracuseStep 1829965 = 686237) (by norm_num)
theorem B1830001 : Blo 1626512 1830001 := bbase (se 2 (by rfl) ⟨686250, by rfl⟩ : syracuseStep 1830001 = 1372501) (by norm_num)
theorem B8244341 : Blo 1626512 8244341 := bbase (se 5 (by rfl) ⟨386453, by rfl⟩ : syracuseStep 8244341 = 772907) (by norm_num)
theorem B2747533 : Blo 1626512 2747533 := bbase (se 3 (by rfl) ⟨515162, by rfl⟩ : syracuseStep 2747533 = 1030325) (by norm_num)
theorem B1830037 : Blo 1626512 1830037 := bbase (se 6 (by rfl) ⟨42891, by rfl⟩ : syracuseStep 1830037 = 85783) (by norm_num)
theorem B2641061 : Blo 1626512 2641061 := bbase (se 4 (by rfl) ⟨247599, by rfl⟩ : syracuseStep 2641061 = 495199) (by norm_num)
theorem B3091621 : Blo 1626512 3091621 := bbase (se 4 (by rfl) ⟨289839, by rfl⟩ : syracuseStep 3091621 = 579679) (by norm_num)
theorem B2059445 : Blo 1626512 2059445 := bbase (se 5 (by rfl) ⟨96536, by rfl⟩ : syracuseStep 2059445 = 193073) (by norm_num)
theorem B1830073 : Blo 1626512 1830073 := bbase (se 2 (by rfl) ⟨686277, by rfl⟩ : syracuseStep 1830073 = 1372555) (by norm_num)
theorem B1830109 : Blo 1626512 1830109 := bbase (se 3 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 1830109 = 686291) (by norm_num)
theorem B2747621 : Blo 1626512 2747621 := bbase (se 4 (by rfl) ⟨257589, by rfl⟩ : syracuseStep 2747621 = 515179) (by norm_num)
theorem B2608357 : Blo 1626512 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B2059501 : Blo 1626512 2059501 := bbase (se 3 (by rfl) ⟨386156, by rfl⟩ : syracuseStep 2059501 = 772313) (by norm_num)
theorem B1830145 : Blo 1626512 1830145 := bbase (se 2 (by rfl) ⟨686304, by rfl⟩ : syracuseStep 1830145 = 1372609) (by norm_num)
theorem B1830181 : Blo 1626512 1830181 := bbase (se 4 (by rfl) ⟨171579, by rfl⟩ : syracuseStep 1830181 = 343159) (by norm_num)
theorem B2608453 : Blo 1626512 2608453 := bbase (se 4 (by rfl) ⟨244542, by rfl⟩ : syracuseStep 2608453 = 489085) (by norm_num)
theorem B1830217 : Blo 1626512 1830217 := bbase (se 2 (by rfl) ⟨686331, by rfl⟩ : syracuseStep 1830217 = 1372663) (by norm_num)
theorem B2059597 : Blo 1626512 2059597 := bbase (se 3 (by rfl) ⟨386174, by rfl⟩ : syracuseStep 2059597 = 772349) (by norm_num)
theorem B10423637 : Blo 1626512 10423637 := bbase (se 11 (by rfl) ⟨7634, by rfl⟩ : syracuseStep 10423637 = 15269) (by norm_num)
theorem B5492069 : Blo 1626512 5492069 := bbase (se 4 (by rfl) ⟨514881, by rfl⟩ : syracuseStep 5492069 = 1029763) (by norm_num)
theorem B2747749 : Blo 1626512 2747749 := bbase (se 4 (by rfl) ⟨257601, by rfl⟩ : syracuseStep 2747749 = 515203) (by norm_num)
theorem B1830253 : Blo 1626512 1830253 := bbase (se 3 (by rfl) ⟨343172, by rfl⟩ : syracuseStep 1830253 = 686345) (by norm_num)
theorem B2198909 : Blo 1626512 2198909 := bbase (se 3 (by rfl) ⟨412295, by rfl⟩ : syracuseStep 2198909 = 824591) (by norm_num)
theorem B1830289 : Blo 1626512 1830289 := bbase (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) (by norm_num)
theorem B1830325 : Blo 1626512 1830325 := bbase (se 5 (by rfl) ⟨85796, by rfl⟩ : syracuseStep 1830325 = 171593) (by norm_num)
theorem B2747837 : Blo 1626512 2747837 := bbase (se 3 (by rfl) ⟨515219, by rfl⟩ : syracuseStep 2747837 = 1030439) (by norm_num)
theorem B1830361 : Blo 1626512 1830361 := bbase (se 2 (by rfl) ⟨686385, by rfl⟩ : syracuseStep 1830361 = 1372771) (by norm_num)
theorem B16698869 : Blo 1626512 16698869 := bbase (se 5 (by rfl) ⟨782759, by rfl⟩ : syracuseStep 16698869 = 1565519) (by norm_num)
theorem B3476981 : Blo 1626512 3476981 := bbase (se 5 (by rfl) ⟨162983, by rfl⟩ : syracuseStep 3476981 = 325967) (by norm_num)
theorem B2059769 : Blo 1626512 2059769 := bbase (se 2 (by rfl) ⟨772413, by rfl⟩ : syracuseStep 2059769 = 1544827) (by norm_num)
theorem B15650293 : Blo 1626512 15650293 := bbase (se 5 (by rfl) ⟨733607, by rfl⟩ : syracuseStep 15650293 = 1467215) (by norm_num)
theorem B14855669 : Blo 1626512 14855669 := bbase (se 5 (by rfl) ⟨696359, by rfl⟩ : syracuseStep 14855669 = 1392719) (by norm_num)
theorem B1830397 : Blo 1626512 1830397 := bbase (se 3 (by rfl) ⟨343199, by rfl⟩ : syracuseStep 1830397 = 686399) (by norm_num)
theorem B2821645 : Blo 1626512 2821645 := bbase (se 3 (by rfl) ⟨529058, by rfl⟩ : syracuseStep 2821645 = 1058117) (by norm_num)
theorem B8236565 : Blo 1626512 8236565 := bbase (se 6 (by rfl) ⟨193044, by rfl⟩ : syracuseStep 8236565 = 386089) (by norm_num)
theorem B1830433 : Blo 1626512 1830433 := bbase (se 2 (by rfl) ⟨686412, by rfl⟩ : syracuseStep 1830433 = 1372825) (by norm_num)
theorem B2059825 : Blo 1626512 2059825 := bbase (se 2 (by rfl) ⟨772434, by rfl⟩ : syracuseStep 2059825 = 1544869) (by norm_num)
theorem B2747965 : Blo 1626512 2747965 := bbase (se 3 (by rfl) ⟨515243, by rfl⟩ : syracuseStep 2747965 = 1030487) (by norm_num)
theorem B1830469 : Blo 1626512 1830469 := bbase (se 4 (by rfl) ⟨171606, by rfl⟩ : syracuseStep 1830469 = 343213) (by norm_num)
theorem B1830505 : Blo 1626512 1830505 := bbase (se 2 (by rfl) ⟨686439, by rfl⟩ : syracuseStep 1830505 = 1372879) (by norm_num)
theorem B3477125 : Blo 1626512 3477125 := bbase (se 4 (by rfl) ⟨325980, by rfl⟩ : syracuseStep 3477125 = 651961) (by norm_num)
theorem B1830541 : Blo 1626512 1830541 := bbase (se 3 (by rfl) ⟨343226, by rfl⟩ : syracuseStep 1830541 = 686453) (by norm_num)
theorem B2059921 : Blo 1626512 2059921 := bbase (se 2 (by rfl) ⟨772470, by rfl⟩ : syracuseStep 2059921 = 1544941) (by norm_num)
theorem B2748053 : Blo 1626512 2748053 := bbase (se 6 (by rfl) ⟨64407, by rfl⟩ : syracuseStep 2748053 = 128815) (by norm_num)
theorem B1830577 : Blo 1626512 1830577 := bbase (se 2 (by rfl) ⟨686466, by rfl⟩ : syracuseStep 1830577 = 1372933) (by norm_num)
theorem B1855157 : Blo 1626512 1855157 := bbase (se 5 (by rfl) ⟨86960, by rfl⟩ : syracuseStep 1855157 = 173921) (by norm_num)
theorem B1830613 : Blo 1626512 1830613 := bbase (se 7 (by rfl) ⟨21452, by rfl⟩ : syracuseStep 1830613 = 42905) (by norm_num)
theorem B8793845 : Blo 1626512 8793845 := bbase (se 5 (by rfl) ⟨412211, by rfl⟩ : syracuseStep 8793845 = 824423) (by norm_num)
theorem B9899765 : Blo 1626512 9899765 := bbase (se 5 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 9899765 = 928103) (by norm_num)
theorem B1830649 : Blo 1626512 1830649 := bbase (se 2 (by rfl) ⟨686493, by rfl⟩ : syracuseStep 1830649 = 1372987) (by norm_num)
theorem B5943061 : Blo 1626512 5943061 := bbase (se 6 (by rfl) ⟨139290, by rfl⟩ : syracuseStep 5943061 = 278581) (by norm_num)
theorem B5492501 : Blo 1626512 5492501 := bbase (se 6 (by rfl) ⟨128730, by rfl⟩ : syracuseStep 5492501 = 257461) (by norm_num)
theorem B1830685 : Blo 1626512 1830685 := bbase (se 3 (by rfl) ⟨343253, by rfl⟩ : syracuseStep 1830685 = 686507) (by norm_num)
theorem B2060093 : Blo 1626512 2060093 := bbase (se 3 (by rfl) ⟨386267, by rfl⟩ : syracuseStep 2060093 = 772535) (by norm_num)
theorem B1830721 : Blo 1626512 1830721 := bbase (se 2 (by rfl) ⟨686520, by rfl⟩ : syracuseStep 1830721 = 1373041) (by norm_num)
theorem B1830757 : Blo 1626512 1830757 := bbase (se 4 (by rfl) ⟨171633, by rfl⟩ : syracuseStep 1830757 = 343267) (by norm_num)
theorem B2060149 : Blo 1626512 2060149 := bbase (se 5 (by rfl) ⟨96569, by rfl⟩ : syracuseStep 2060149 = 193139) (by norm_num)
theorem B1830793 : Blo 1626512 1830793 := bbase (se 2 (by rfl) ⟨686547, by rfl⟩ : syracuseStep 1830793 = 1373095) (by norm_num)
theorem B3133333 : Blo 1626512 3133333 := bbase (se 6 (by rfl) ⟨73437, by rfl⟩ : syracuseStep 3133333 = 146875) (by norm_num)
theorem B1830829 : Blo 1626512 1830829 := bbase (se 3 (by rfl) ⟨343280, by rfl⟩ : syracuseStep 1830829 = 686561) (by norm_num)
theorem B1830865 : Blo 1626512 1830865 := bbase (se 2 (by rfl) ⟨686574, by rfl⟩ : syracuseStep 1830865 = 1373149) (by norm_num)
theorem B2060245 : Blo 1626512 2060245 := bbase (se 7 (by rfl) ⟨24143, by rfl⟩ : syracuseStep 2060245 = 48287) (by norm_num)
theorem B3477485 : Blo 1626512 3477485 := bbase (se 3 (by rfl) ⟨652028, by rfl⟩ : syracuseStep 3477485 = 1304057) (by norm_num)
theorem B1830901 : Blo 1626512 1830901 := bbase (se 5 (by rfl) ⟨85823, by rfl⟩ : syracuseStep 1830901 = 171647) (by norm_num)
theorem B15634453 : Blo 1626512 15634453 := bbase (se 6 (by rfl) ⟨366432, by rfl⟩ : syracuseStep 15634453 = 732865) (by norm_num)
theorem B1830937 : Blo 1626512 1830937 := bbase (se 2 (by rfl) ⟨686601, by rfl⟩ : syracuseStep 1830937 = 1373203) (by norm_num)
theorem B1830973 : Blo 1626512 1830973 := bbase (se 3 (by rfl) ⟨343307, by rfl⟩ : syracuseStep 1830973 = 686615) (by norm_num)
theorem B1831009 : Blo 1626512 1831009 := bbase (se 2 (by rfl) ⟨686628, by rfl⟩ : syracuseStep 1831009 = 1373257) (by norm_num)
theorem B2060417 : Blo 1626512 2060417 := bbase (se 2 (by rfl) ⟨772656, by rfl⟩ : syracuseStep 2060417 = 1545313) (by norm_num)
theorem B1831045 : Blo 1626512 1831045 := bbase (se 4 (by rfl) ⟨171660, by rfl⟩ : syracuseStep 1831045 = 343321) (by norm_num)
theorem B1831081 : Blo 1626512 1831081 := bbase (se 2 (by rfl) ⟨686655, by rfl⟩ : syracuseStep 1831081 = 1373311) (by norm_num)
theorem B2060473 : Blo 1626512 2060473 := bbase (se 2 (by rfl) ⟨772677, by rfl⟩ : syracuseStep 2060473 = 1545355) (by norm_num)
theorem B5492933 : Blo 1626512 5492933 := bbase (se 4 (by rfl) ⟨514962, by rfl⟩ : syracuseStep 5492933 = 1029925) (by norm_num)
theorem B1831117 : Blo 1626512 1831117 := bbase (se 3 (by rfl) ⟨343334, by rfl⟩ : syracuseStep 1831117 = 686669) (by norm_num)
theorem B1831153 : Blo 1626512 1831153 := bbase (se 2 (by rfl) ⟨686682, by rfl⟩ : syracuseStep 1831153 = 1373365) (by norm_num)
theorem B6598901 : Blo 1626512 6598901 := bbase (se 5 (by rfl) ⟨309323, by rfl⟩ : syracuseStep 6598901 = 618647) (by norm_num)
theorem B1831189 : Blo 1626512 1831189 := bbase (se 6 (by rfl) ⟨42918, by rfl⟩ : syracuseStep 1831189 = 85837) (by norm_num)
theorem B2060569 : Blo 1626512 2060569 := bbase (se 2 (by rfl) ⟨772713, by rfl⟩ : syracuseStep 2060569 = 1545427) (by norm_num)
theorem B2199845 : Blo 1626512 2199845 := bbase (se 4 (by rfl) ⟨206235, by rfl⟩ : syracuseStep 2199845 = 412471) (by norm_num)
theorem B7819573 : Blo 1626512 7819573 := bbase (se 5 (by rfl) ⟨366542, by rfl⟩ : syracuseStep 7819573 = 733085) (by norm_num)
theorem B3911989 : Blo 1626512 3911989 := bbase (se 5 (by rfl) ⟨183374, by rfl⟩ : syracuseStep 3911989 = 366749) (by norm_num)
theorem B1831225 : Blo 1626512 1831225 := bbase (se 2 (by rfl) ⟨686709, by rfl⟩ : syracuseStep 1831225 = 1373419) (by norm_num)
theorem B1831261 : Blo 1626512 1831261 := bbase (se 3 (by rfl) ⟨343361, by rfl⟩ : syracuseStep 1831261 = 686723) (by norm_num)
theorem B1831297 : Blo 1626512 1831297 := bbase (se 2 (by rfl) ⟨686736, by rfl⟩ : syracuseStep 1831297 = 1373473) (by norm_num)
theorem B1831333 : Blo 1626512 1831333 := bbase (se 4 (by rfl) ⟨171687, by rfl⟩ : syracuseStep 1831333 = 343375) (by norm_num)
theorem B6951365 : Blo 1626512 6951365 := bbase (se 4 (by rfl) ⟨651690, by rfl⟩ : syracuseStep 6951365 = 1303381) (by norm_num)
theorem B2060741 : Blo 1626512 2060741 := bbase (se 4 (by rfl) ⟨193194, by rfl⟩ : syracuseStep 2060741 = 386389) (by norm_num)
theorem B1831369 : Blo 1626512 1831369 := bbase (se 2 (by rfl) ⟨686763, by rfl⟩ : syracuseStep 1831369 = 1373527) (by norm_num)
theorem B1831405 : Blo 1626512 1831405 := bbase (se 3 (by rfl) ⟨343388, by rfl⟩ : syracuseStep 1831405 = 686777) (by norm_num)
theorem B2060797 : Blo 1626512 2060797 := bbase (se 3 (by rfl) ⟨386399, by rfl⟩ : syracuseStep 2060797 = 772799) (by norm_num)
theorem B1831441 : Blo 1626512 1831441 := bbase (se 2 (by rfl) ⟨686790, by rfl⟩ : syracuseStep 1831441 = 1373581) (by norm_num)
theorem B1831477 : Blo 1626512 1831477 := bbase (se 5 (by rfl) ⟨85850, by rfl⟩ : syracuseStep 1831477 = 171701) (by norm_num)
theorem B1831513 : Blo 1626512 1831513 := bbase (se 2 (by rfl) ⟨686817, by rfl⟩ : syracuseStep 1831513 = 1373635) (by norm_num)
theorem B2060893 : Blo 1626512 2060893 := bbase (se 3 (by rfl) ⟨386417, by rfl⟩ : syracuseStep 2060893 = 772835) (by norm_num)
theorem B5493365 : Blo 1626512 5493365 := bbase (se 5 (by rfl) ⟨257501, by rfl⟩ : syracuseStep 5493365 = 515003) (by norm_num)
theorem B1831549 : Blo 1626512 1831549 := bbase (se 3 (by rfl) ⟨343415, by rfl⟩ : syracuseStep 1831549 = 686831) (by norm_num)
theorem B1831585 : Blo 1626512 1831585 := bbase (se 2 (by rfl) ⟨686844, by rfl⟩ : syracuseStep 1831585 = 1373689) (by norm_num)
theorem B6181541 : Blo 1626512 6181541 := bbase (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) (by norm_num)
theorem B4117189 : Blo 1626512 4117189 := bbase (se 4 (by rfl) ⟨385986, by rfl⟩ : syracuseStep 4117189 = 771973) (by norm_num)
theorem B1831621 : Blo 1626512 1831621 := bbase (se 4 (by rfl) ⟨171714, by rfl⟩ : syracuseStep 1831621 = 343429) (by norm_num)
theorem B6951653 : Blo 1626512 6951653 := bbase (se 4 (by rfl) ⟨651717, by rfl⟩ : syracuseStep 6951653 = 1303435) (by norm_num)
theorem B1856233 : Blo 1626512 1856233 := bbase (se 2 (by rfl) ⟨696087, by rfl⟩ : syracuseStep 1856233 = 1392175) (by norm_num)
theorem B1831657 : Blo 1626512 1831657 := bbase (se 2 (by rfl) ⟨686871, by rfl⟩ : syracuseStep 1831657 = 1373743) (by norm_num)
theorem B2061065 : Blo 1626512 2061065 := bbase (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) (by norm_num)
theorem B1856269 : Blo 1626512 1856269 := bbase (se 3 (by rfl) ⟨348050, by rfl⟩ : syracuseStep 1856269 = 696101) (by norm_num)
theorem B1831693 : Blo 1626512 1831693 := bbase (se 3 (by rfl) ⟨343442, by rfl⟩ : syracuseStep 1831693 = 686885) (by norm_num)
theorem B8237861 : Blo 1626512 8237861 := bbase (se 4 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 8237861 = 1544599) (by norm_num)
theorem B1831729 : Blo 1626512 1831729 := bbase (se 2 (by rfl) ⟨686898, by rfl⟩ : syracuseStep 1831729 = 1373797) (by norm_num)
theorem B4117301 : Blo 1626512 4117301 := bbase (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) (by norm_num)
theorem B1831765 : Blo 1626512 1831765 := bbase (se 9 (by rfl) ⟨5366, by rfl⟩ : syracuseStep 1831765 = 10733) (by norm_num)
theorem B1831801 : Blo 1626512 1831801 := bbase (se 2 (by rfl) ⟨686925, by rfl⟩ : syracuseStep 1831801 = 1373851) (by norm_num)
theorem B2347909 : Blo 1626512 2347909 := bbase (se 4 (by rfl) ⟨220116, by rfl⟩ : syracuseStep 2347909 = 440233) (by norm_num)
theorem B1831837 : Blo 1626512 1831837 := bbase (se 3 (by rfl) ⟨343469, by rfl⟩ : syracuseStep 1831837 = 686939) (by norm_num)
theorem B1831873 : Blo 1626512 1831873 := bbase (se 2 (by rfl) ⟨686952, by rfl⟩ : syracuseStep 1831873 = 1373905) (by norm_num)
theorem B6181829 : Blo 1626512 6181829 := bbase (se 4 (by rfl) ⟨579546, by rfl⟩ : syracuseStep 6181829 = 1159093) (by norm_num)
theorem B1831909 : Blo 1626512 1831909 := bbase (se 4 (by rfl) ⟨171741, by rfl⟩ : syracuseStep 1831909 = 343483) (by norm_num)
theorem B4117493 : Blo 1626512 4117493 := bbase (se 5 (by rfl) ⟨193007, by rfl⟩ : syracuseStep 4117493 = 386015) (by norm_num)
theorem B1831945 : Blo 1626512 1831945 := bbase (se 2 (by rfl) ⟨686979, by rfl⟩ : syracuseStep 1831945 = 1373959) (by norm_num)
theorem B1856525 : Blo 1626512 1856525 := bbase (se 3 (by rfl) ⟨348098, by rfl⟩ : syracuseStep 1856525 = 696197) (by norm_num)
theorem B5493797 : Blo 1626512 5493797 := bbase (se 4 (by rfl) ⟨515043, by rfl⟩ : syracuseStep 5493797 = 1030087) (by norm_num)
theorem B1831981 : Blo 1626512 1831981 := bbase (se 3 (by rfl) ⟨343496, by rfl⟩ : syracuseStep 1831981 = 686993) (by norm_num)
theorem B13906997 : Blo 1626512 13906997 := bbase (se 5 (by rfl) ⟨651890, by rfl⟩ : syracuseStep 13906997 = 1303781) (by norm_num)
theorem B1832017 : Blo 1626512 1832017 := bbase (se 2 (by rfl) ⟨687006, by rfl⟩ : syracuseStep 1832017 = 1374013) (by norm_num)
theorem B5944421 : Blo 1626512 5944421 := bbase (se 4 (by rfl) ⟨557289, by rfl⟩ : syracuseStep 5944421 = 1114579) (by norm_num)
theorem B2782325 : Blo 1626512 2782325 := bbase (se 5 (by rfl) ⟨130421, by rfl⟩ : syracuseStep 2782325 = 260843) (by norm_num)
theorem B1832053 : Blo 1626512 1832053 := bbase (se 5 (by rfl) ⟨85877, by rfl⟩ : syracuseStep 1832053 = 171755) (by norm_num)
theorem B4117837 : Blo 1626512 4117837 := bbase (se 3 (by rfl) ⟨772094, by rfl⟩ : syracuseStep 4117837 = 1544189) (by norm_num)
theorem B4117949 : Blo 1626512 4117949 := bbase (se 3 (by rfl) ⟨772115, by rfl⟩ : syracuseStep 4117949 = 1544231) (by norm_num)
theorem B6952405 : Blo 1626512 6952405 := bbase (se 7 (by rfl) ⟨81473, by rfl⟩ : syracuseStep 6952405 = 162947) (by norm_num)
theorem B5494229 : Blo 1626512 5494229 := bbase (se 7 (by rfl) ⟨64385, by rfl⟩ : syracuseStep 5494229 = 128771) (by norm_num)
theorem B4019701 : Blo 1626512 4019701 := bbase (se 5 (by rfl) ⟨188423, by rfl⟩ : syracuseStep 4019701 = 376847) (by norm_num)
theorem B4634117 : Blo 1626512 4634117 := bbase (se 4 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 4634117 = 868897) (by norm_num)
theorem B1955345 : Blo 1626512 1955345 := bbase (se 2 (by rfl) ⟨733254, by rfl⟩ : syracuseStep 1955345 = 1466509) (by norm_num)
theorem B8795765 : Blo 1626512 8795765 := bbase (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) (by norm_num)
theorem B4118141 : Blo 1626512 4118141 := bbase (se 3 (by rfl) ⟨772151, by rfl⟩ : syracuseStep 4118141 = 1544303) (by norm_num)
theorem B2315965 : Blo 1626512 2315965 := bbase (se 3 (by rfl) ⟨434243, by rfl⟩ : syracuseStep 2315965 = 868487) (by norm_num)
theorem B4175725 : Blo 1626512 4175725 := bbase (se 3 (by rfl) ⟨782948, by rfl⟩ : syracuseStep 4175725 = 1565897) (by norm_num)
theorem B5494661 : Blo 1626512 5494661 := bbase (se 4 (by rfl) ⟨515124, by rfl⟩ : syracuseStep 5494661 = 1030249) (by norm_num)
theorem B3659669 : Blo 1626512 3659669 := bbase (se 6 (by rfl) ⟨85773, by rfl⟩ : syracuseStep 3659669 = 171547) (by norm_num)
theorem B4118485 : Blo 1626512 4118485 := bbase (se 7 (by rfl) ⟨48263, by rfl⟩ : syracuseStep 4118485 = 96527) (by norm_num)
theorem B3659741 : Blo 1626512 3659741 := bbase (se 3 (by rfl) ⟨686201, by rfl⟩ : syracuseStep 3659741 = 1372403) (by norm_num)
theorem B3659813 : Blo 1626512 3659813 := bbase (se 4 (by rfl) ⟨343107, by rfl⟩ : syracuseStep 3659813 = 686215) (by norm_num)
theorem B8239157 : Blo 1626512 8239157 := bbase (se 5 (by rfl) ⟨386210, by rfl⟩ : syracuseStep 8239157 = 772421) (by norm_num)
theorem B4118597 : Blo 1626512 4118597 := bbase (se 4 (by rfl) ⟨386118, by rfl⟩ : syracuseStep 4118597 = 772237) (by norm_num)
theorem B6183013 : Blo 1626512 6183013 := bbase (se 4 (by rfl) ⟨579657, by rfl⟩ : syracuseStep 6183013 = 1159315) (by norm_num)
theorem B3659885 : Blo 1626512 3659885 := bbase (se 3 (by rfl) ⟨686228, by rfl⟩ : syracuseStep 3659885 = 1372457) (by norm_num)
theorem B5216405 : Blo 1626512 5216405 := bbase (se 6 (by rfl) ⟨122259, by rfl⟩ : syracuseStep 5216405 = 244519) (by norm_num)
theorem B3659957 : Blo 1626512 3659957 := bbase (se 5 (by rfl) ⟨171560, by rfl⟩ : syracuseStep 3659957 = 343121) (by norm_num)
theorem B2783413 : Blo 1626512 2783413 := bbase (se 5 (by rfl) ⟨130472, by rfl⟩ : syracuseStep 2783413 = 260945) (by norm_num)
theorem B6953141 : Blo 1626512 6953141 := bbase (se 5 (by rfl) ⟨325928, by rfl⟩ : syracuseStep 6953141 = 651857) (by norm_num)
theorem B1956037 : Blo 1626512 1956037 := bbase (se 4 (by rfl) ⟨183378, by rfl⟩ : syracuseStep 1956037 = 366757) (by norm_num)
theorem B3660029 : Blo 1626512 3660029 := bbase (se 3 (by rfl) ⟨686255, by rfl⟩ : syracuseStep 3660029 = 1372511) (by norm_num)
theorem B4118789 : Blo 1626512 4118789 := bbase (se 4 (by rfl) ⟨386136, by rfl⟩ : syracuseStep 4118789 = 772273) (by norm_num)
theorem B2316557 : Blo 1626512 2316557 := bbase (se 3 (by rfl) ⟨434354, by rfl⟩ : syracuseStep 2316557 = 868709) (by norm_num)
theorem B1956133 : Blo 1626512 1956133 := bbase (se 4 (by rfl) ⟨183387, by rfl⟩ : syracuseStep 1956133 = 366775) (by norm_num)
theorem B5495093 : Blo 1626512 5495093 := bbase (se 5 (by rfl) ⟨257582, by rfl⟩ : syracuseStep 5495093 = 515165) (by norm_num)
theorem B3660101 : Blo 1626512 3660101 := bbase (se 4 (by rfl) ⟨343134, by rfl⟩ : syracuseStep 3660101 = 686269) (by norm_num)
theorem B2316637 : Blo 1626512 2316637 := bbase (se 3 (by rfl) ⟨434369, by rfl⟩ : syracuseStep 2316637 = 868739) (by norm_num)
theorem B3660173 : Blo 1626512 3660173 := bbase (se 3 (by rfl) ⟨686282, by rfl⟩ : syracuseStep 3660173 = 1372565) (by norm_num)
theorem B11737493 : Blo 1626512 11737493 := bbase (se 6 (by rfl) ⟨275097, by rfl⟩ : syracuseStep 11737493 = 550195) (by norm_num)
theorem B2783693 : Blo 1626512 2783693 := bbase (se 3 (by rfl) ⟨521942, by rfl⟩ : syracuseStep 2783693 = 1043885) (by norm_num)
theorem B3660245 : Blo 1626512 3660245 := bbase (se 7 (by rfl) ⟨42893, by rfl⟩ : syracuseStep 3660245 = 85787) (by norm_num)
theorem B2316757 : Blo 1626512 2316757 := bbase (se 7 (by rfl) ⟨27149, by rfl⟩ : syracuseStep 2316757 = 54299) (by norm_num)
theorem B7043573 : Blo 1626512 7043573 := bbase (se 5 (by rfl) ⟨330167, by rfl⟩ : syracuseStep 7043573 = 660335) (by norm_num)
theorem B3660317 : Blo 1626512 3660317 := bbase (se 3 (by rfl) ⟨686309, by rfl⟩ : syracuseStep 3660317 = 1372619) (by norm_num)
theorem B2316853 : Blo 1626512 2316853 := bbase (se 5 (by rfl) ⟨108602, by rfl⟩ : syracuseStep 2316853 = 217205) (by norm_num)
theorem B2439773 : Blo 1626512 2439773 := bbase (se 3 (by rfl) ⟨457457, by rfl⟩ : syracuseStep 2439773 = 914915) (by norm_num)
theorem B4119133 : Blo 1626512 4119133 := bbase (se 3 (by rfl) ⟨772337, by rfl⟩ : syracuseStep 4119133 = 1544675) (by norm_num)
theorem B3660389 : Blo 1626512 3660389 := bbase (se 4 (by rfl) ⟨343161, by rfl⟩ : syracuseStep 3660389 = 686323) (by norm_num)
theorem B2439797 : Blo 1626512 2439797 := bbase (se 5 (by rfl) ⟨114365, by rfl⟩ : syracuseStep 2439797 = 228731) (by norm_num)
theorem B2931317 : Blo 1626512 2931317 := bbase (se 5 (by rfl) ⟨137405, by rfl⟩ : syracuseStep 2931317 = 274811) (by norm_num)
theorem B2439821 : Blo 1626512 2439821 := bbase (se 3 (by rfl) ⟨457466, by rfl⟩ : syracuseStep 2439821 = 914933) (by norm_num)
theorem B2439845 : Blo 1626512 2439845 := bbase (se 4 (by rfl) ⟨228735, by rfl⟩ : syracuseStep 2439845 = 457471) (by norm_num)
theorem B4635301 : Blo 1626512 4635301 := bbase (se 4 (by rfl) ⟨434559, by rfl⟩ : syracuseStep 4635301 = 869119) (by norm_num)
theorem B3660461 : Blo 1626512 3660461 := bbase (se 3 (by rfl) ⟨686336, by rfl⟩ : syracuseStep 3660461 = 1372673) (by norm_num)
theorem B2087605 : Blo 1626512 2087605 := bbase (se 5 (by rfl) ⟨97856, by rfl⟩ : syracuseStep 2087605 = 195713) (by norm_num)
theorem B2439869 : Blo 1626512 2439869 := bbase (se 3 (by rfl) ⟨457475, by rfl⟩ : syracuseStep 2439869 = 914951) (by norm_num)
theorem B4119245 : Blo 1626512 4119245 := bbase (se 3 (by rfl) ⟨772358, by rfl⟩ : syracuseStep 4119245 = 1544717) (by norm_num)
theorem B2439893 : Blo 1626512 2439893 := bbase (se 7 (by rfl) ⟨28592, by rfl⟩ : syracuseStep 2439893 = 57185) (by norm_num)
theorem B5495525 : Blo 1626512 5495525 := bbase (se 4 (by rfl) ⟨515205, by rfl⟩ : syracuseStep 5495525 = 1030411) (by norm_num)
theorem B2439917 : Blo 1626512 2439917 := bbase (se 3 (by rfl) ⟨457484, by rfl⟩ : syracuseStep 2439917 = 914969) (by norm_num)
theorem B3660533 : Blo 1626512 3660533 := bbase (se 5 (by rfl) ⟨171587, by rfl⟩ : syracuseStep 3660533 = 343175) (by norm_num)
theorem B12360437 : Blo 1626512 12360437 := bbase (se 5 (by rfl) ⟨579395, by rfl⟩ : syracuseStep 12360437 = 1158791) (by norm_num)
theorem B2439941 : Blo 1626512 2439941 := bbase (se 4 (by rfl) ⟨228744, by rfl⟩ : syracuseStep 2439941 = 457489) (by norm_num)
theorem B2087689 : Blo 1626512 2087689 := bbase (se 2 (by rfl) ⟨782883, by rfl⟩ : syracuseStep 2087689 = 1565767) (by norm_num)
theorem B2439965 : Blo 1626512 2439965 := bbase (se 3 (by rfl) ⟨457493, by rfl⟩ : syracuseStep 2439965 = 914987) (by norm_num)
theorem B2439989 : Blo 1626512 2439989 := bbase (se 5 (by rfl) ⟨114374, by rfl⟩ : syracuseStep 2439989 = 228749) (by norm_num)
theorem B3660605 : Blo 1626512 3660605 := bbase (se 3 (by rfl) ⟨686363, by rfl⟩ : syracuseStep 3660605 = 1372727) (by norm_num)
theorem B4635461 : Blo 1626512 4635461 := bbase (se 4 (by rfl) ⟨434574, by rfl⟩ : syracuseStep 4635461 = 869149) (by norm_num)
theorem B2440013 : Blo 1626512 2440013 := bbase (se 3 (by rfl) ⟨457502, by rfl⟩ : syracuseStep 2440013 = 915005) (by norm_num)
theorem B2440037 : Blo 1626512 2440037 := bbase (se 4 (by rfl) ⟨228753, by rfl⟩ : syracuseStep 2440037 = 457507) (by norm_num)
theorem B2440061 : Blo 1626512 2440061 := bbase (se 3 (by rfl) ⟨457511, by rfl⟩ : syracuseStep 2440061 = 915023) (by norm_num)
theorem B4234109 : Blo 1626512 4234109 := bbase (se 3 (by rfl) ⟨793895, by rfl⟩ : syracuseStep 4234109 = 1587791) (by norm_num)
theorem B3660677 : Blo 1626512 3660677 := bbase (se 4 (by rfl) ⟨343188, by rfl⟩ : syracuseStep 3660677 = 686377) (by norm_num)
theorem B4119437 : Blo 1626512 4119437 := bbase (se 3 (by rfl) ⟨772394, by rfl⟩ : syracuseStep 4119437 = 1544789) (by norm_num)
theorem B2440085 : Blo 1626512 2440085 := bbase (se 6 (by rfl) ⟨57189, by rfl⟩ : syracuseStep 2440085 = 114379) (by norm_num)
theorem B4234133 : Blo 1626512 4234133 := bbase (se 6 (by rfl) ⟨99237, by rfl⟩ : syracuseStep 4234133 = 198475) (by norm_num)
theorem B2440109 : Blo 1626512 2440109 := bbase (se 3 (by rfl) ⟨457520, by rfl⟩ : syracuseStep 2440109 = 915041) (by norm_num)
theorem B11140021 : Blo 1626512 11140021 := bbase (se 5 (by rfl) ⟨522188, by rfl⟩ : syracuseStep 11140021 = 1044377) (by norm_num)
theorem B2440133 : Blo 1626512 2440133 := bbase (se 4 (by rfl) ⟨228762, by rfl⟩ : syracuseStep 2440133 = 457525) (by norm_num)
theorem B3660749 : Blo 1626512 3660749 := bbase (se 3 (by rfl) ⟨686390, by rfl⟩ : syracuseStep 3660749 = 1372781) (by norm_num)
theorem B2440157 : Blo 1626512 2440157 := bbase (se 3 (by rfl) ⟨457529, by rfl⟩ : syracuseStep 2440157 = 915059) (by norm_num)
theorem B2440181 : Blo 1626512 2440181 := bbase (se 5 (by rfl) ⟨114383, by rfl⟩ : syracuseStep 2440181 = 228767) (by norm_num)
theorem B2440205 : Blo 1626512 2440205 := bbase (se 3 (by rfl) ⟨457538, by rfl⟩ : syracuseStep 2440205 = 915077) (by norm_num)
theorem B3660821 : Blo 1626512 3660821 := bbase (se 6 (by rfl) ⟨85800, by rfl⟩ : syracuseStep 3660821 = 171601) (by norm_num)
theorem B2440229 : Blo 1626512 2440229 := bbase (se 4 (by rfl) ⟨228771, by rfl⟩ : syracuseStep 2440229 = 457543) (by norm_num)
theorem B2317349 : Blo 1626512 2317349 := bbase (se 4 (by rfl) ⟨217251, by rfl⟩ : syracuseStep 2317349 = 434503) (by norm_num)
theorem B4635701 : Blo 1626512 4635701 := bbase (se 5 (by rfl) ⟨217298, by rfl⟩ : syracuseStep 4635701 = 434597) (by norm_num)
theorem B2440253 : Blo 1626512 2440253 := bbase (se 3 (by rfl) ⟨457547, by rfl⟩ : syracuseStep 2440253 = 915095) (by norm_num)
theorem B2440277 : Blo 1626512 2440277 := bbase (se 8 (by rfl) ⟨14298, by rfl⟩ : syracuseStep 2440277 = 28597) (by norm_num)
theorem B3660893 : Blo 1626512 3660893 := bbase (se 3 (by rfl) ⟨686417, by rfl⟩ : syracuseStep 3660893 = 1372835) (by norm_num)
theorem B2088037 : Blo 1626512 2088037 := bbase (se 4 (by rfl) ⟨195753, by rfl⟩ : syracuseStep 2088037 = 391507) (by norm_num)
theorem B2440301 : Blo 1626512 2440301 := bbase (se 3 (by rfl) ⟨457556, by rfl⟩ : syracuseStep 2440301 = 915113) (by norm_num)
theorem B2440325 : Blo 1626512 2440325 := bbase (se 4 (by rfl) ⟨228780, by rfl⟩ : syracuseStep 2440325 = 457561) (by norm_num)
theorem B12352661 : Blo 1626512 12352661 := bbase (se 6 (by rfl) ⟨289515, by rfl⟩ : syracuseStep 12352661 = 579031) (by norm_num)
theorem B5495957 : Blo 1626512 5495957 := bbase (se 6 (by rfl) ⟨128811, by rfl⟩ : syracuseStep 5495957 = 257623) (by norm_num)
theorem B2440349 : Blo 1626512 2440349 := bbase (se 3 (by rfl) ⟨457565, by rfl⟩ : syracuseStep 2440349 = 915131) (by norm_num)
theorem B3660965 : Blo 1626512 3660965 := bbase (se 4 (by rfl) ⟨343215, by rfl⟩ : syracuseStep 3660965 = 686431) (by norm_num)
theorem B2440373 : Blo 1626512 2440373 := bbase (se 5 (by rfl) ⟨114392, by rfl⟩ : syracuseStep 2440373 = 228785) (by norm_num)
theorem B2440397 : Blo 1626512 2440397 := bbase (se 3 (by rfl) ⟨457574, by rfl⟩ : syracuseStep 2440397 = 915149) (by norm_num)
theorem B2440421 : Blo 1626512 2440421 := bbase (se 4 (by rfl) ⟨228789, by rfl⟩ : syracuseStep 2440421 = 457579) (by norm_num)
theorem B4119781 : Blo 1626512 4119781 := bbase (se 4 (by rfl) ⟨386229, by rfl⟩ : syracuseStep 4119781 = 772459) (by norm_num)
theorem B3661037 : Blo 1626512 3661037 := bbase (se 3 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 3661037 = 1372889) (by norm_num)
theorem B4635893 : Blo 1626512 4635893 := bbase (se 5 (by rfl) ⟨217307, by rfl⟩ : syracuseStep 4635893 = 434615) (by norm_num)
theorem B2440445 : Blo 1626512 2440445 := bbase (se 3 (by rfl) ⟨457583, by rfl⟩ : syracuseStep 2440445 = 915167) (by norm_num)
theorem B1809665 : Blo 1626512 1809665 := bbase (se 2 (by rfl) ⟨678624, by rfl⟩ : syracuseStep 1809665 = 1357249) (by norm_num)
theorem B2440469 : Blo 1626512 2440469 := bbase (se 6 (by rfl) ⟨57198, by rfl⟩ : syracuseStep 2440469 = 114397) (by norm_num)
theorem B2440493 : Blo 1626512 2440493 := bbase (se 3 (by rfl) ⟨457592, by rfl⟩ : syracuseStep 2440493 = 915185) (by norm_num)
theorem B3661109 : Blo 1626512 3661109 := bbase (se 5 (by rfl) ⟨171614, by rfl⟩ : syracuseStep 3661109 = 343229) (by norm_num)
theorem B2440517 : Blo 1626512 2440517 := bbase (se 4 (by rfl) ⟨228798, by rfl⟩ : syracuseStep 2440517 = 457597) (by norm_num)
theorem B8240453 : Blo 1626512 8240453 := bbase (se 4 (by rfl) ⟨772542, by rfl⟩ : syracuseStep 8240453 = 1545085) (by norm_num)
theorem B4119893 : Blo 1626512 4119893 := bbase (se 11 (by rfl) ⟨3017, by rfl⟩ : syracuseStep 4119893 = 6035) (by norm_num)
theorem B2440541 : Blo 1626512 2440541 := bbase (se 3 (by rfl) ⟨457601, by rfl⟩ : syracuseStep 2440541 = 915203) (by norm_num)
theorem B2440565 : Blo 1626512 2440565 := bbase (se 5 (by rfl) ⟨114401, by rfl⟩ : syracuseStep 2440565 = 228803) (by norm_num)
theorem B3661181 : Blo 1626512 3661181 := bbase (se 3 (by rfl) ⟨686471, by rfl⟩ : syracuseStep 3661181 = 1372943) (by norm_num)
theorem B2440589 : Blo 1626512 2440589 := bbase (se 3 (by rfl) ⟨457610, by rfl⟩ : syracuseStep 2440589 = 915221) (by norm_num)
theorem B2440613 : Blo 1626512 2440613 := bbase (se 4 (by rfl) ⟨228807, by rfl⟩ : syracuseStep 2440613 = 457615) (by norm_num)
theorem B2440637 : Blo 1626512 2440637 := bbase (se 3 (by rfl) ⟨457619, by rfl⟩ : syracuseStep 2440637 = 915239) (by norm_num)
theorem B3661253 : Blo 1626512 3661253 := bbase (se 4 (by rfl) ⟨343242, by rfl⟩ : syracuseStep 3661253 = 686485) (by norm_num)
theorem B4398533 : Blo 1626512 4398533 := bbase (se 4 (by rfl) ⟨412362, by rfl⟩ : syracuseStep 4398533 = 824725) (by norm_num)
theorem B2440661 : Blo 1626512 2440661 := bbase (se 7 (by rfl) ⟨28601, by rfl⟩ : syracuseStep 2440661 = 57203) (by norm_num)
theorem B9272789 : Blo 1626512 9272789 := bbase (se 7 (by rfl) ⟨108665, by rfl⟩ : syracuseStep 9272789 = 217331) (by norm_num)
theorem B2440685 : Blo 1626512 2440685 := bbase (se 3 (by rfl) ⟨457628, by rfl⟩ : syracuseStep 2440685 = 915257) (by norm_num)
theorem B1981945 : Blo 1626512 1981945 := bbase (se 2 (by rfl) ⟨743229, by rfl⟩ : syracuseStep 1981945 = 1486459) (by norm_num)
theorem B2973181 : Blo 1626512 2973181 := bbase (se 3 (by rfl) ⟨557471, by rfl⟩ : syracuseStep 2973181 = 1114943) (by norm_num)
theorem B3087877 : Blo 1626512 3087877 := bbase (se 4 (by rfl) ⟨289488, by rfl⟩ : syracuseStep 3087877 = 578977) (by norm_num)
theorem B2440709 : Blo 1626512 2440709 := bbase (se 4 (by rfl) ⟨228816, by rfl⟩ : syracuseStep 2440709 = 457633) (by norm_num)
theorem B3661325 : Blo 1626512 3661325 := bbase (se 3 (by rfl) ⟨686498, by rfl⟩ : syracuseStep 3661325 = 1372997) (by norm_num)
theorem B4120085 : Blo 1626512 4120085 := bbase (se 6 (by rfl) ⟨96564, by rfl⟩ : syracuseStep 4120085 = 193129) (by norm_num)
theorem B2440733 : Blo 1626512 2440733 := bbase (se 3 (by rfl) ⟨457637, by rfl⟩ : syracuseStep 2440733 = 915275) (by norm_num)
theorem B2440757 : Blo 1626512 2440757 := bbase (se 5 (by rfl) ⟨114410, by rfl⟩ : syracuseStep 2440757 = 228821) (by norm_num)
theorem B1760825 : Blo 1626512 1760825 := bbase (se 2 (by rfl) ⟨660309, by rfl⟩ : syracuseStep 1760825 = 1320619) (by norm_num)
theorem B4398661 : Blo 1626512 4398661 := bbase (se 4 (by rfl) ⟨412374, by rfl⟩ : syracuseStep 4398661 = 824749) (by norm_num)
theorem B2440781 : Blo 1626512 2440781 := bbase (se 3 (by rfl) ⟨457646, by rfl⟩ : syracuseStep 2440781 = 915293) (by norm_num)
theorem B2317901 : Blo 1626512 2317901 := bbase (se 3 (by rfl) ⟨434606, by rfl⟩ : syracuseStep 2317901 = 869213) (by norm_num)
theorem B9264725 : Blo 1626512 9264725 := bbase (se 8 (by rfl) ⟨54285, by rfl⟩ : syracuseStep 9264725 = 108571) (by norm_num)
theorem B3661397 : Blo 1626512 3661397 := bbase (se 8 (by rfl) ⟨21453, by rfl⟩ : syracuseStep 3661397 = 42907) (by norm_num)
theorem B2440805 : Blo 1626512 2440805 := bbase (se 4 (by rfl) ⟨228825, by rfl⟩ : syracuseStep 2440805 = 457651) (by norm_num)
theorem B2440829 : Blo 1626512 2440829 := bbase (se 3 (by rfl) ⟨457655, by rfl⟩ : syracuseStep 2440829 = 915311) (by norm_num)
theorem B2440853 : Blo 1626512 2440853 := bbase (se 6 (by rfl) ⟨57207, by rfl⟩ : syracuseStep 2440853 = 114415) (by norm_num)
theorem B3661469 : Blo 1626512 3661469 := bbase (se 3 (by rfl) ⟨686525, by rfl⟩ : syracuseStep 3661469 = 1373051) (by norm_num)
theorem B3088037 : Blo 1626512 3088037 := bbase (se 4 (by rfl) ⟨289503, by rfl⟩ : syracuseStep 3088037 = 579007) (by norm_num)
theorem B2440877 : Blo 1626512 2440877 := bbase (se 3 (by rfl) ⟨457664, by rfl⟩ : syracuseStep 2440877 = 915329) (by norm_num)
theorem B2440901 : Blo 1626512 2440901 := bbase (se 4 (by rfl) ⟨228834, by rfl⟩ : syracuseStep 2440901 = 457669) (by norm_num)
theorem B2440925 : Blo 1626512 2440925 := bbase (se 3 (by rfl) ⟨457673, by rfl⟩ : syracuseStep 2440925 = 915347) (by norm_num)
theorem B3661541 : Blo 1626512 3661541 := bbase (se 4 (by rfl) ⟨343269, by rfl⟩ : syracuseStep 3661541 = 686539) (by norm_num)
theorem B2440949 : Blo 1626512 2440949 := bbase (se 5 (by rfl) ⟨114419, by rfl⟩ : syracuseStep 2440949 = 228839) (by norm_num)
theorem B2440973 : Blo 1626512 2440973 := bbase (se 3 (by rfl) ⟨457682, by rfl⟩ : syracuseStep 2440973 = 915365) (by norm_num)
theorem B2440997 : Blo 1626512 2440997 := bbase (se 4 (by rfl) ⟨228843, by rfl⟩ : syracuseStep 2440997 = 457687) (by norm_num)
theorem B3661613 : Blo 1626512 3661613 := bbase (se 3 (by rfl) ⟨686552, by rfl⟩ : syracuseStep 3661613 = 1373105) (by norm_num)
theorem B3088181 : Blo 1626512 3088181 := bbase (se 5 (by rfl) ⟨144758, by rfl⟩ : syracuseStep 3088181 = 289517) (by norm_num)
theorem B2441021 : Blo 1626512 2441021 := bbase (se 3 (by rfl) ⟨457691, by rfl⟩ : syracuseStep 2441021 = 915383) (by norm_num)
theorem B2973517 : Blo 1626512 2973517 := bbase (se 3 (by rfl) ⟨557534, by rfl⟩ : syracuseStep 2973517 = 1115069) (by norm_num)
theorem B23453525 : Blo 1626512 23453525 := bbase (se 9 (by rfl) ⟨68711, by rfl⟩ : syracuseStep 23453525 = 137423) (by norm_num)
theorem B2441045 : Blo 1626512 2441045 := bbase (se 9 (by rfl) ⟨7151, by rfl⟩ : syracuseStep 2441045 = 14303) (by norm_num)
theorem B2785117 : Blo 1626512 2785117 := bbase (se 3 (by rfl) ⟨522209, by rfl⟩ : syracuseStep 2785117 = 1044419) (by norm_num)
theorem B2441069 : Blo 1626512 2441069 := bbase (se 3 (by rfl) ⟨457700, by rfl⟩ : syracuseStep 2441069 = 915401) (by norm_num)
theorem B4120429 : Blo 1626512 4120429 := bbase (se 3 (by rfl) ⟨772580, by rfl⟩ : syracuseStep 4120429 = 1545161) (by norm_num)
theorem B3661685 : Blo 1626512 3661685 := bbase (se 5 (by rfl) ⟨171641, by rfl⟩ : syracuseStep 3661685 = 343283) (by norm_num)
theorem B2441093 : Blo 1626512 2441093 := bbase (se 4 (by rfl) ⟨228852, by rfl⟩ : syracuseStep 2441093 = 457705) (by norm_num)
theorem B4398997 : Blo 1626512 4398997 := bbase (se 6 (by rfl) ⟨103101, by rfl⟩ : syracuseStep 4398997 = 206203) (by norm_num)
theorem B2441117 : Blo 1626512 2441117 := bbase (se 3 (by rfl) ⟨457709, by rfl⟩ : syracuseStep 2441117 = 915419) (by norm_num)
theorem B15638453 : Blo 1626512 15638453 := bbase (se 5 (by rfl) ⟨733052, by rfl⟩ : syracuseStep 15638453 = 1466105) (by norm_num)
theorem B2441141 : Blo 1626512 2441141 := bbase (se 5 (by rfl) ⟨114428, by rfl⟩ : syracuseStep 2441141 = 228857) (by norm_num)
theorem B3661757 : Blo 1626512 3661757 := bbase (se 3 (by rfl) ⟨686579, by rfl⟩ : syracuseStep 3661757 = 1373159) (by norm_num)
theorem B2441165 : Blo 1626512 2441165 := bbase (se 3 (by rfl) ⟨457718, by rfl⟩ : syracuseStep 2441165 = 915437) (by norm_num)
theorem B4120541 : Blo 1626512 4120541 := bbase (se 3 (by rfl) ⟨772601, by rfl⟩ : syracuseStep 4120541 = 1545203) (by norm_num)
theorem B2441189 : Blo 1626512 2441189 := bbase (se 4 (by rfl) ⟨228861, by rfl⟩ : syracuseStep 2441189 = 457723) (by norm_num)
theorem B2441213 : Blo 1626512 2441213 := bbase (se 3 (by rfl) ⟨457727, by rfl⟩ : syracuseStep 2441213 = 915455) (by norm_num)
theorem B2441219 : Blo 1626512 2441219 := bstep (se 1 (by rfl) ⟨1830914, by rfl⟩ : syracuseStep 2441219 = 3661829) B3661829
theorem B2441249 : Blo 1626512 2441249 := bstep (se 2 (by rfl) ⟨915468, by rfl⟩ : syracuseStep 2441249 = 1830937) B1830937
theorem B2441267 : Blo 1626512 2441267 := bstep (se 1 (by rfl) ⟨1830950, by rfl⟩ : syracuseStep 2441267 = 3661901) B3661901
theorem B2441297 : Blo 1626512 2441297 := bstep (se 2 (by rfl) ⟨915486, by rfl⟩ : syracuseStep 2441297 = 1830973) B1830973
theorem B2441315 : Blo 1626512 2441315 := bstep (se 1 (by rfl) ⟨1830986, by rfl⟩ : syracuseStep 2441315 = 3661973) B3661973
theorem B3661937 : Blo 1626512 3661937 := bstep (se 2 (by rfl) ⟨1373226, by rfl⟩ : syracuseStep 3661937 = 2746453) B2746453
theorem B2441345 : Blo 1626512 2441345 := bstep (se 2 (by rfl) ⟨915504, by rfl⟩ : syracuseStep 2441345 = 1831009) B1831009
theorem B3661955 : Blo 1626512 3661955 := bstep (se 1 (by rfl) ⟨2746466, by rfl⟩ : syracuseStep 3661955 = 5492933) B5492933
theorem B2441363 : Blo 1626512 2441363 := bstep (se 1 (by rfl) ⟨1831022, by rfl⟩ : syracuseStep 2441363 = 3662045) B3662045
theorem B4399267 : Blo 1626512 4399267 := bstep (se 1 (by rfl) ⟨3299450, by rfl⟩ : syracuseStep 4399267 = 6598901) B6598901
theorem B2441393 : Blo 1626512 2441393 := bstep (se 2 (by rfl) ⟨915522, by rfl⟩ : syracuseStep 2441393 = 1831045) B1831045
theorem B4120753 : Blo 1626512 4120753 := bstep (se 2 (by rfl) ⟨1545282, by rfl⟩ : syracuseStep 4120753 = 3090565) B3090565
theorem B2441411 : Blo 1626512 2441411 := bstep (se 1 (by rfl) ⟨1831058, by rfl⟩ : syracuseStep 2441411 = 3662117) B3662117
theorem B2441441 : Blo 1626512 2441441 := bstep (se 2 (by rfl) ⟨915540, by rfl⟩ : syracuseStep 2441441 = 1831081) B1831081
theorem B2441459 : Blo 1626512 2441459 := bstep (se 1 (by rfl) ⟨1831094, by rfl⟩ : syracuseStep 2441459 = 3662189) B3662189
theorem B2441489 : Blo 1626512 2441489 := bstep (se 2 (by rfl) ⟨915558, by rfl⟩ : syracuseStep 2441489 = 1831117) B1831117
theorem B2441507 : Blo 1626512 2441507 := bstep (se 1 (by rfl) ⟨1831130, by rfl⟩ : syracuseStep 2441507 = 3662261) B3662261
theorem B2441537 : Blo 1626512 2441537 := bstep (se 2 (by rfl) ⟨915576, by rfl⟩ : syracuseStep 2441537 = 1831153) B1831153
theorem B2441555 : Blo 1626512 2441555 := bstep (se 1 (by rfl) ⟨1831166, by rfl⟩ : syracuseStep 2441555 = 3662333) B3662333
theorem B1737059 : Blo 1626512 1737059 := bstep (se 1 (by rfl) ⟨1302794, by rfl⟩ : syracuseStep 1737059 = 2605589) B2605589
theorem B2441585 : Blo 1626512 2441585 := bstep (se 2 (by rfl) ⟨915594, by rfl⟩ : syracuseStep 2441585 = 1831189) B1831189
theorem B2441603 : Blo 1626512 2441603 := bstep (se 1 (by rfl) ⟨1831202, by rfl⟩ : syracuseStep 2441603 = 3662405) B3662405
theorem B13910413 : Blo 1626512 13910413 := bstep (se 3 (by rfl) ⟨2608202, by rfl⟩ : syracuseStep 13910413 = 5216405) B5216405
theorem B3662225 : Blo 1626512 3662225 := bstep (se 2 (by rfl) ⟨1373334, by rfl⟩ : syracuseStep 3662225 = 2746669) B2746669
theorem B2441633 : Blo 1626512 2441633 := bstep (se 2 (by rfl) ⟨915612, by rfl⟩ : syracuseStep 2441633 = 1831225) B1831225
theorem B3662243 : Blo 1626512 3662243 := bstep (se 1 (by rfl) ⟨2746682, by rfl⟩ : syracuseStep 3662243 = 5493365) B5493365
theorem B4637101 : Blo 1626512 4637101 := bstep (se 3 (by rfl) ⟨869456, by rfl⟩ : syracuseStep 4637101 = 1738913) B1738913
theorem B2441651 : Blo 1626512 2441651 := bstep (se 1 (by rfl) ⟨1831238, by rfl⟩ : syracuseStep 2441651 = 3662477) B3662477
theorem B4121027 : Blo 1626512 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B3088849 : Blo 1626512 3088849 := bstep (se 2 (by rfl) ⟨1158318, by rfl⟩ : syracuseStep 3088849 = 2316637) B2316637
theorem B2441681 : Blo 1626512 2441681 := bstep (se 2 (by rfl) ⟨915630, by rfl⟩ : syracuseStep 2441681 = 1831261) B1831261
theorem B2441699 : Blo 1626512 2441699 := bstep (se 1 (by rfl) ⟨1831274, by rfl⟩ : syracuseStep 2441699 = 3662549) B3662549
theorem B2744833 : Blo 1626512 2744833 := bstep (se 2 (by rfl) ⟨1029312, by rfl⟩ : syracuseStep 2744833 = 2058625) B2058625
theorem B2441729 : Blo 1626512 2441729 := bstep (se 2 (by rfl) ⟨915648, by rfl⟩ : syracuseStep 2441729 = 1831297) B1831297
theorem B2441747 : Blo 1626512 2441747 := bstep (se 1 (by rfl) ⟨1831310, by rfl⟩ : syracuseStep 2441747 = 3662621) B3662621
theorem B2744867 : Blo 1626512 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B5571107 : Blo 1626512 5571107 := bstep (se 1 (by rfl) ⟨4178330, by rfl⟩ : syracuseStep 5571107 = 8356661) B8356661
theorem B2441777 : Blo 1626512 2441777 := bstep (se 2 (by rfl) ⟨915666, by rfl⟩ : syracuseStep 2441777 = 1831333) B1831333
theorem B2441795 : Blo 1626512 2441795 := bstep (se 1 (by rfl) ⟨1831346, by rfl⟩ : syracuseStep 2441795 = 3662693) B3662693
theorem B2441825 : Blo 1626512 2441825 := bstep (se 2 (by rfl) ⟨915684, by rfl⟩ : syracuseStep 2441825 = 1831369) B1831369
theorem B3089009 : Blo 1626512 3089009 := bstep (se 2 (by rfl) ⟨1158378, by rfl⟩ : syracuseStep 3089009 = 2316757) B2316757
theorem B2441843 : Blo 1626512 2441843 := bstep (se 1 (by rfl) ⟨1831382, by rfl⟩ : syracuseStep 2441843 = 3662765) B3662765
theorem B4121219 : Blo 1626512 4121219 := bstep (se 1 (by rfl) ⟨3090914, by rfl⟩ : syracuseStep 4121219 = 6181829) B6181829
theorem B12362381 : Blo 1626512 12362381 := bstep (se 3 (by rfl) ⟨2317946, by rfl⟩ : syracuseStep 12362381 = 4635893) B4635893
theorem B2441873 : Blo 1626512 2441873 := bstep (se 2 (by rfl) ⟨915702, by rfl⟩ : syracuseStep 2441873 = 1831405) B1831405
theorem B2744995 : Blo 1626512 2744995 := bstep (se 1 (by rfl) ⟨2058746, by rfl⟩ : syracuseStep 2744995 = 4117493) B4117493
theorem B2441891 : Blo 1626512 2441891 := bstep (se 1 (by rfl) ⟨1831418, by rfl⟩ : syracuseStep 2441891 = 3662837) B3662837
theorem B3662513 : Blo 1626512 3662513 := bstep (se 2 (by rfl) ⟨1373442, by rfl⟩ : syracuseStep 3662513 = 2746885) B2746885
theorem B2441921 : Blo 1626512 2441921 := bstep (se 2 (by rfl) ⟨915720, by rfl⟩ : syracuseStep 2441921 = 1831441) B1831441
theorem B3662531 : Blo 1626512 3662531 := bstep (se 1 (by rfl) ⟨2746898, by rfl⟩ : syracuseStep 3662531 = 5493797) B5493797
theorem B6177485 : Blo 1626512 6177485 := bstep (se 3 (by rfl) ⟨1158278, by rfl⟩ : syracuseStep 6177485 = 2316557) B2316557
theorem B2441939 : Blo 1626512 2441939 := bstep (se 1 (by rfl) ⟨1831454, by rfl⟩ : syracuseStep 2441939 = 3662909) B3662909
theorem B2441969 : Blo 1626512 2441969 := bstep (se 2 (by rfl) ⟨915738, by rfl⟩ : syracuseStep 2441969 = 1831477) B1831477
theorem B2441987 : Blo 1626512 2441987 := bstep (se 1 (by rfl) ⟨1831490, by rfl⟩ : syracuseStep 2441987 = 3662981) B3662981
theorem B5866253 : Blo 1626512 5866253 := bstep (se 3 (by rfl) ⟨1099922, by rfl⟩ : syracuseStep 5866253 = 2199845) B2199845
theorem B2442017 : Blo 1626512 2442017 := bstep (se 2 (by rfl) ⟨915756, by rfl⟩ : syracuseStep 2442017 = 1831513) B1831513
theorem B6439715 : Blo 1626512 6439715 := bstep (se 1 (by rfl) ⟨4829786, by rfl⟩ : syracuseStep 6439715 = 9659573) B9659573
theorem B2745137 : Blo 1626512 2745137 := bstep (se 2 (by rfl) ⟨1029426, by rfl⟩ : syracuseStep 2745137 = 2058853) B2058853
theorem B2442035 : Blo 1626512 2442035 := bstep (se 1 (by rfl) ⟨1831526, by rfl⟩ : syracuseStep 2442035 = 3663053) B3663053
theorem B21439285 : Blo 1626512 21439285 := bstep (se 5 (by rfl) ⟨1004966, by rfl⟩ : syracuseStep 21439285 = 2009933) B2009933
theorem B2442065 : Blo 1626512 2442065 := bstep (se 2 (by rfl) ⟨915774, by rfl⟩ : syracuseStep 2442065 = 1831549) B1831549
theorem B2442083 : Blo 1626512 2442083 := bstep (se 1 (by rfl) ⟨1831562, by rfl⟩ : syracuseStep 2442083 = 3663125) B3663125
theorem B3474289 : Blo 1626512 3474289 := bstep (se 2 (by rfl) ⟨1302858, by rfl⟩ : syracuseStep 3474289 = 2605717) B2605717
theorem B2442113 : Blo 1626512 2442113 := bstep (se 2 (by rfl) ⟨915792, by rfl⟩ : syracuseStep 2442113 = 1831585) B1831585
theorem B2442131 : Blo 1626512 2442131 := bstep (se 1 (by rfl) ⟨1831598, by rfl⟩ : syracuseStep 2442131 = 3663197) B3663197
theorem B5489585 : Blo 1626512 5489585 := bstep (se 2 (by rfl) ⟨2058594, by rfl⟩ : syracuseStep 5489585 = 4117189) B4117189
theorem B2745265 : Blo 1626512 2745265 := bstep (se 2 (by rfl) ⟨1029474, by rfl⟩ : syracuseStep 2745265 = 2058949) B2058949
theorem B2442161 : Blo 1626512 2442161 := bstep (se 2 (by rfl) ⟨915810, by rfl⟩ : syracuseStep 2442161 = 1831621) B1831621
theorem B2442179 : Blo 1626512 2442179 := bstep (se 1 (by rfl) ⟨1831634, by rfl⟩ : syracuseStep 2442179 = 3663269) B3663269
theorem B14844869 : Blo 1626512 14844869 := bstep (se 4 (by rfl) ⟨1391706, by rfl⟩ : syracuseStep 14844869 = 2783413) B2783413
theorem B3662801 : Blo 1626512 3662801 := bstep (se 2 (by rfl) ⟨1373550, by rfl⟩ : syracuseStep 3662801 = 2747101) B2747101
theorem B2745299 : Blo 1626512 2745299 := bstep (se 1 (by rfl) ⟨2058974, by rfl⟩ : syracuseStep 2745299 = 4117949) B4117949
theorem B2474977 : Blo 1626512 2474977 := bstep (se 2 (by rfl) ⟨928116, by rfl⟩ : syracuseStep 2474977 = 1856233) B1856233
theorem B2442209 : Blo 1626512 2442209 := bstep (se 2 (by rfl) ⟨915828, by rfl⟩ : syracuseStep 2442209 = 1831657) B1831657
theorem B3662819 : Blo 1626512 3662819 := bstep (se 1 (by rfl) ⟨2747114, by rfl⟩ : syracuseStep 3662819 = 5494229) B5494229
theorem B2442227 : Blo 1626512 2442227 := bstep (se 1 (by rfl) ⟨1831670, by rfl⟩ : syracuseStep 2442227 = 3663341) B3663341
theorem B3089411 : Blo 1626512 3089411 := bstep (se 1 (by rfl) ⟨2317058, by rfl⟩ : syracuseStep 3089411 = 4634117) B4634117
theorem B2442257 : Blo 1626512 2442257 := bstep (se 2 (by rfl) ⟨915846, by rfl⟩ : syracuseStep 2442257 = 1831693) B1831693
theorem B2442275 : Blo 1626512 2442275 := bstep (se 1 (by rfl) ⟨1831706, by rfl⟩ : syracuseStep 2442275 = 3663413) B3663413
theorem B2442305 : Blo 1626512 2442305 := bstep (se 2 (by rfl) ⟨915864, by rfl⟩ : syracuseStep 2442305 = 1831729) B1831729
theorem B1737811 : Blo 1626512 1737811 := bstep (se 1 (by rfl) ⟨1303358, by rfl⟩ : syracuseStep 1737811 = 2606717) B2606717
theorem B2745427 : Blo 1626512 2745427 := bstep (se 1 (by rfl) ⟨2059070, by rfl⟩ : syracuseStep 2745427 = 4118141) B4118141
theorem B2442323 : Blo 1626512 2442323 := bstep (se 1 (by rfl) ⟨1831742, by rfl⟩ : syracuseStep 2442323 = 3663485) B3663485
theorem B2442353 : Blo 1626512 2442353 := bstep (se 2 (by rfl) ⟨915882, by rfl⟩ : syracuseStep 2442353 = 1831765) B1831765
theorem B2442371 : Blo 1626512 2442371 := bstep (se 1 (by rfl) ⟨1831778, by rfl⟩ : syracuseStep 2442371 = 3663557) B3663557
theorem B2442401 : Blo 1626512 2442401 := bstep (se 2 (by rfl) ⟨915900, by rfl⟩ : syracuseStep 2442401 = 1831801) B1831801
theorem B2442419 : Blo 1626512 2442419 := bstep (se 1 (by rfl) ⟨1831814, by rfl⟩ : syracuseStep 2442419 = 3663629) B3663629
theorem B2442449 : Blo 1626512 2442449 := bstep (se 2 (by rfl) ⟨915918, by rfl⟩ : syracuseStep 2442449 = 1831837) B1831837
theorem B2745569 : Blo 1626512 2745569 := bstep (se 2 (by rfl) ⟨1029588, by rfl⟩ : syracuseStep 2745569 = 2059177) B2059177
theorem B2442467 : Blo 1626512 2442467 := bstep (se 1 (by rfl) ⟨1831850, by rfl⟩ : syracuseStep 2442467 = 3663701) B3663701
theorem B7628017 : Blo 1626512 7628017 := bstep (se 2 (by rfl) ⟨2860506, by rfl⟩ : syracuseStep 7628017 = 5721013) B5721013
theorem B3663089 : Blo 1626512 3663089 := bstep (se 2 (by rfl) ⟨1373658, by rfl⟩ : syracuseStep 3663089 = 2747317) B2747317
theorem B9045233 : Blo 1626512 9045233 := bstep (se 2 (by rfl) ⟨3391962, by rfl⟩ : syracuseStep 9045233 = 6783925) B6783925
theorem B2442497 : Blo 1626512 2442497 := bstep (se 2 (by rfl) ⟨915936, by rfl⟩ : syracuseStep 2442497 = 1831873) B1831873
theorem B3663107 : Blo 1626512 3663107 := bstep (se 1 (by rfl) ⟨2747330, by rfl⟩ : syracuseStep 3663107 = 5494661) B5494661
theorem B2442515 : Blo 1626512 2442515 := bstep (se 1 (by rfl) ⟨1831886, by rfl⟩ : syracuseStep 2442515 = 3663773) B3663773
theorem B2442545 : Blo 1626512 2442545 := bstep (se 2 (by rfl) ⟨915954, by rfl⟩ : syracuseStep 2442545 = 1831909) B1831909
theorem B2442563 : Blo 1626512 2442563 := bstep (se 1 (by rfl) ⟨1831922, by rfl⟩ : syracuseStep 2442563 = 3663845) B3663845
theorem B9266501 : Blo 1626512 9266501 := bstep (se 4 (by rfl) ⟨868734, by rfl⟩ : syracuseStep 9266501 = 1737469) B1737469
theorem B2745697 : Blo 1626512 2745697 := bstep (se 2 (by rfl) ⟨1029636, by rfl⟩ : syracuseStep 2745697 = 2059273) B2059273
theorem B2606435 : Blo 1626512 2606435 := bstep (se 1 (by rfl) ⟨1954826, by rfl⟩ : syracuseStep 2606435 = 3909653) B3909653
theorem B2442593 : Blo 1626512 2442593 := bstep (se 2 (by rfl) ⟨915972, by rfl⟩ : syracuseStep 2442593 = 1831945) B1831945
theorem B2442611 : Blo 1626512 2442611 := bstep (se 1 (by rfl) ⟨1831958, by rfl⟩ : syracuseStep 2442611 = 3663917) B3663917
theorem B2745731 : Blo 1626512 2745731 := bstep (se 1 (by rfl) ⟨2059298, by rfl⟩ : syracuseStep 2745731 = 4118597) B4118597
theorem B2442641 : Blo 1626512 2442641 := bstep (se 2 (by rfl) ⟨915990, by rfl⟩ : syracuseStep 2442641 = 1831981) B1831981
theorem B2442659 : Blo 1626512 2442659 := bstep (se 1 (by rfl) ⟨1831994, by rfl⟩ : syracuseStep 2442659 = 3663989) B3663989
theorem B1672627 : Blo 1626512 1672627 := bstep (se 1 (by rfl) ⟨1254470, by rfl⟩ : syracuseStep 1672627 = 2508941) B2508941
theorem B2442689 : Blo 1626512 2442689 := bstep (se 2 (by rfl) ⟨916008, by rfl⟩ : syracuseStep 2442689 = 1832017) B1832017
theorem B5211587 : Blo 1626512 5211587 := bstep (se 1 (by rfl) ⟨3908690, by rfl⟩ : syracuseStep 5211587 = 7817381) B7817381
theorem B5490125 : Blo 1626512 5490125 := bstep (se 3 (by rfl) ⟨1029398, by rfl⟩ : syracuseStep 5490125 = 2058797) B2058797
theorem B2442707 : Blo 1626512 2442707 := bstep (se 1 (by rfl) ⟨1832030, by rfl⟩ : syracuseStep 2442707 = 3664061) B3664061
theorem B4695533 : Blo 1626512 4695533 := bstep (se 3 (by rfl) ⟨880412, by rfl⟩ : syracuseStep 4695533 = 1760825) B1760825
theorem B2442737 : Blo 1626512 2442737 := bstep (se 2 (by rfl) ⟨916026, by rfl⟩ : syracuseStep 2442737 = 1832053) B1832053
theorem B5490179 : Blo 1626512 5490179 := bstep (se 1 (by rfl) ⟨4117634, by rfl⟩ : syracuseStep 5490179 = 8235269) B8235269
theorem B2745859 : Blo 1626512 2745859 := bstep (se 1 (by rfl) ⟨2059394, by rfl⟩ : syracuseStep 2745859 = 4118789) B4118789
theorem B2442755 : Blo 1626512 2442755 := bstep (se 1 (by rfl) ⟨1832066, by rfl⟩ : syracuseStep 2442755 = 3664133) B3664133
theorem B3663377 : Blo 1626512 3663377 := bstep (se 2 (by rfl) ⟨1373766, by rfl⟩ : syracuseStep 3663377 = 2747533) B2747533
theorem B2606627 : Blo 1626512 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B3663395 : Blo 1626512 3663395 := bstep (se 1 (by rfl) ⟨2747546, by rfl⟩ : syracuseStep 3663395 = 5495093) B5495093
theorem B4122161 : Blo 1626512 4122161 := bstep (se 2 (by rfl) ⟨1545810, by rfl⟩ : syracuseStep 4122161 = 3091621) B3091621
theorem B7824995 : Blo 1626512 7824995 := bstep (se 1 (by rfl) ⟨5868746, by rfl⟩ : syracuseStep 7824995 = 11737493) B11737493
theorem B3475075 : Blo 1626512 3475075 := bstep (se 1 (by rfl) ⟨2606306, by rfl⟩ : syracuseStep 3475075 = 5212613) B5212613
theorem B2746001 : Blo 1626512 2746001 := bstep (se 2 (by rfl) ⟨1029750, by rfl⟩ : syracuseStep 2746001 = 2059501) B2059501
theorem B4695715 : Blo 1626512 4695715 := bstep (se 1 (by rfl) ⟨3521786, by rfl⟩ : syracuseStep 4695715 = 7043573) B7043573
theorem B13911749 : Blo 1626512 13911749 := bstep (se 4 (by rfl) ⟨1304226, by rfl⟩ : syracuseStep 13911749 = 2608453) B2608453
theorem B9266957 : Blo 1626512 9266957 := bstep (se 3 (by rfl) ⟨1737554, by rfl⟩ : syracuseStep 9266957 = 3475109) B3475109
theorem B5490449 : Blo 1626512 5490449 := bstep (se 2 (by rfl) ⟨2058918, by rfl⟩ : syracuseStep 5490449 = 4117837) B4117837
theorem B2746129 : Blo 1626512 2746129 := bstep (se 2 (by rfl) ⟨1029798, by rfl⟩ : syracuseStep 2746129 = 2059597) B2059597
theorem B3663665 : Blo 1626512 3663665 := bstep (se 2 (by rfl) ⟨1373874, by rfl⟩ : syracuseStep 3663665 = 2747749) B2747749
theorem B2746163 : Blo 1626512 2746163 := bstep (se 1 (by rfl) ⟨2059622, by rfl⟩ : syracuseStep 2746163 = 4119245) B4119245
theorem B3663683 : Blo 1626512 3663683 := bstep (se 1 (by rfl) ⟨2747762, by rfl⟩ : syracuseStep 3663683 = 5495525) B5495525
theorem B3090307 : Blo 1626512 3090307 := bstep (se 1 (by rfl) ⟨2317730, by rfl⟩ : syracuseStep 3090307 = 4635461) B4635461
theorem B2746291 : Blo 1626512 2746291 := bstep (se 1 (by rfl) ⟨2059718, by rfl⟩ : syracuseStep 2746291 = 4119437) B4119437
theorem B13895651 : Blo 1626512 13895651 := bstep (se 1 (by rfl) ⟨10421738, by rfl⟩ : syracuseStep 13895651 = 20843477) B20843477
theorem B5359601 : Blo 1626512 5359601 := bstep (se 2 (by rfl) ⟨2009850, by rfl⟩ : syracuseStep 5359601 = 4019701) B4019701
theorem B20867057 : Blo 1626512 20867057 := bstep (se 2 (by rfl) ⟨7825146, by rfl⟩ : syracuseStep 20867057 = 15650293) B15650293
theorem B3762193 : Blo 1626512 3762193 := bstep (se 2 (by rfl) ⟨1410822, by rfl⟩ : syracuseStep 3762193 = 2821645) B2821645
theorem B3090467 : Blo 1626512 3090467 := bstep (se 1 (by rfl) ⟨2317850, by rfl⟩ : syracuseStep 3090467 = 4635701) B4635701
theorem B2746433 : Blo 1626512 2746433 := bstep (se 2 (by rfl) ⟨1029912, by rfl⟩ : syracuseStep 2746433 = 2059825) B2059825
theorem B3663953 : Blo 1626512 3663953 := bstep (se 2 (by rfl) ⟨1373982, by rfl⟩ : syracuseStep 3663953 = 2747965) B2747965
theorem B8235107 : Blo 1626512 8235107 := bstep (se 1 (by rfl) ⟨6176330, by rfl⟩ : syracuseStep 8235107 = 12352661) B12352661
theorem B3663971 : Blo 1626512 3663971 := bstep (se 1 (by rfl) ⟨2747978, by rfl⟩ : syracuseStep 3663971 = 5495957) B5495957
theorem B2746561 : Blo 1626512 2746561 := bstep (se 2 (by rfl) ⟨1029960, by rfl⟩ : syracuseStep 2746561 = 2059921) B2059921
theorem B6949091 : Blo 1626512 6949091 := bstep (se 1 (by rfl) ⟨5211818, by rfl⟩ : syracuseStep 6949091 = 10423637) B10423637
theorem B2746595 : Blo 1626512 2746595 := bstep (se 1 (by rfl) ⟨2059946, by rfl⟩ : syracuseStep 2746595 = 4119893) B4119893
theorem B5490989 : Blo 1626512 5490989 := bstep (se 3 (by rfl) ⟨1029560, by rfl⟩ : syracuseStep 5490989 = 2059121) B2059121
theorem B11290957 : Blo 1626512 11290957 := bstep (se 3 (by rfl) ⟨2117054, by rfl⟩ : syracuseStep 11290957 = 4234109) B4234109
theorem B3475793 : Blo 1626512 3475793 := bstep (se 2 (by rfl) ⟨1303422, by rfl⟩ : syracuseStep 3475793 = 2606845) B2606845
theorem B5491043 : Blo 1626512 5491043 := bstep (se 1 (by rfl) ⟨4118282, by rfl⟩ : syracuseStep 5491043 = 8236565) B8236565
theorem B2746723 : Blo 1626512 2746723 := bstep (se 1 (by rfl) ⟨2060042, by rfl⟩ : syracuseStep 2746723 = 4120085) B4120085
theorem B7924081 : Blo 1626512 7924081 := bstep (se 2 (by rfl) ⟨2971530, by rfl⟩ : syracuseStep 7924081 = 5943061) B5943061
theorem B2058691 : Blo 1626512 2058691 := bstep (se 1 (by rfl) ⟨1544018, by rfl⟩ : syracuseStep 2058691 = 3088037) B3088037
theorem B3713489 : Blo 1626512 3713489 := bstep (se 2 (by rfl) ⟨1392558, by rfl⟩ : syracuseStep 3713489 = 2785117) B2785117
theorem B2746865 : Blo 1626512 2746865 := bstep (se 2 (by rfl) ⟨1030074, by rfl⟩ : syracuseStep 2746865 = 2060149) B2060149
theorem B2058787 : Blo 1626512 2058787 := bstep (se 1 (by rfl) ⟨1544090, by rfl⟩ : syracuseStep 2058787 = 3088181) B3088181
theorem B5491313 : Blo 1626512 5491313 := bstep (se 2 (by rfl) ⟨2059242, by rfl⟩ : syracuseStep 5491313 = 4118485) B4118485
theorem B2746993 : Blo 1626512 2746993 := bstep (se 2 (by rfl) ⟨1030122, by rfl⟩ : syracuseStep 2746993 = 2060245) B2060245
theorem B2747027 : Blo 1626512 2747027 := bstep (se 1 (by rfl) ⟨2060270, by rfl⟩ : syracuseStep 2747027 = 4120541) B4120541
theorem B19303093 : Blo 1626512 19303093 := bstep (se 5 (by rfl) ⟨904832, by rfl⟩ : syracuseStep 19303093 = 1809665) B1809665
theorem B4950733 : Blo 1626512 4950733 := bstep (se 3 (by rfl) ⟨928262, by rfl⟩ : syracuseStep 4950733 = 1856525) B1856525
theorem B6179597 : Blo 1626512 6179597 := bstep (se 3 (by rfl) ⟨1158674, by rfl⟩ : syracuseStep 6179597 = 2317349) B2317349
theorem B2747155 : Blo 1626512 2747155 := bstep (se 1 (by rfl) ⟨2060366, by rfl⟩ : syracuseStep 2747155 = 4120733) B4120733
theorem B50088725 : Blo 1626512 50088725 := bstep (se 6 (by rfl) ⟨1173954, by rfl⟩ : syracuseStep 50088725 = 2347909) B2347909
theorem B8244017 : Blo 1626512 8244017 := bstep (se 2 (by rfl) ⟨3091506, by rfl⟩ : syracuseStep 8244017 = 6183013) B6183013
theorem B3476305 : Blo 1626512 3476305 := bstep (se 2 (by rfl) ⟨1303614, by rfl⟩ : syracuseStep 3476305 = 2607229) B2607229
theorem B6261617 : Blo 1626512 6261617 := bstep (se 2 (by rfl) ⟨2348106, by rfl⟩ : syracuseStep 6261617 = 4696213) B4696213
theorem B8235917 : Blo 1626512 8235917 := bstep (se 3 (by rfl) ⟨1544234, by rfl⟩ : syracuseStep 8235917 = 3088469) B3088469
theorem B2747297 : Blo 1626512 2747297 := bstep (se 2 (by rfl) ⟨1030236, by rfl⟩ : syracuseStep 2747297 = 2060473) B2060473
theorem B2608049 : Blo 1626512 2608049 := bstep (se 2 (by rfl) ⟨978018, by rfl⟩ : syracuseStep 2608049 = 1956037) B1956037
theorem B12356549 : Blo 1626512 12356549 := bstep (se 4 (by rfl) ⟨1158426, by rfl⟩ : syracuseStep 12356549 = 2316853) B2316853
theorem B1829875 : Blo 1626512 1829875 := bstep (se 1 (by rfl) ⟨1372406, by rfl⟩ : syracuseStep 1829875 = 2744813) B2744813
theorem B2059283 : Blo 1626512 2059283 := bstep (se 1 (by rfl) ⟨1544462, by rfl⟩ : syracuseStep 2059283 = 3088925) B3088925
theorem B2747425 : Blo 1626512 2747425 := bstep (se 2 (by rfl) ⟨1030284, by rfl⟩ : syracuseStep 2747425 = 2060569) B2060569
theorem B2747459 : Blo 1626512 2747459 := bstep (se 1 (by rfl) ⟨2060594, by rfl⟩ : syracuseStep 2747459 = 4121189) B4121189
theorem B3091537 : Blo 1626512 3091537 := bstep (se 2 (by rfl) ⟨1159326, by rfl⟩ : syracuseStep 3091537 = 2318653) B2318653
theorem B1830019 : Blo 1626512 1830019 := bstep (se 1 (by rfl) ⟨1372514, by rfl⟩ : syracuseStep 1830019 = 2745029) B2745029
theorem B5491853 : Blo 1626512 5491853 := bstep (se 3 (by rfl) ⟨1029722, by rfl⟩ : syracuseStep 5491853 = 2059445) B2059445
theorem B5491907 : Blo 1626512 5491907 := bstep (se 1 (by rfl) ⟨4118930, by rfl⟩ : syracuseStep 5491907 = 8237861) B8237861
theorem B2747587 : Blo 1626512 2747587 := bstep (se 1 (by rfl) ⟨2060690, by rfl⟩ : syracuseStep 2747587 = 4121381) B4121381
theorem B11136197 : Blo 1626512 11136197 := bstep (se 4 (by rfl) ⟨1044018, by rfl⟩ : syracuseStep 11136197 = 2088037) B2088037
theorem B1830163 : Blo 1626512 1830163 := bstep (se 1 (by rfl) ⟨1372622, by rfl⟩ : syracuseStep 1830163 = 2745245) B2745245
theorem B2747729 : Blo 1626512 2747729 := bstep (se 2 (by rfl) ⟨1030398, by rfl⟩ : syracuseStep 2747729 = 2060797) B2060797
theorem B7048561 : Blo 1626512 7048561 := bstep (se 2 (by rfl) ⟨2643210, by rfl⟩ : syracuseStep 7048561 = 5286421) B5286421
theorem B1854883 : Blo 1626512 1854883 := bstep (se 1 (by rfl) ⟨1391162, by rfl⟩ : syracuseStep 1854883 = 2782325) B2782325
theorem B1830307 : Blo 1626512 1830307 := bstep (se 1 (by rfl) ⟨1372730, by rfl⟩ : syracuseStep 1830307 = 2745461) B2745461
theorem B5492177 : Blo 1626512 5492177 := bstep (se 2 (by rfl) ⟨2059566, by rfl⟩ : syracuseStep 5492177 = 4119133) B4119133
theorem B2747857 : Blo 1626512 2747857 := bstep (se 2 (by rfl) ⟨1030446, by rfl⟩ : syracuseStep 2747857 = 2060893) B2060893
theorem B12365297 : Blo 1626512 12365297 := bstep (se 2 (by rfl) ⟨4636986, by rfl⟩ : syracuseStep 12365297 = 9273973) B9273973
theorem B2747891 : Blo 1626512 2747891 := bstep (se 1 (by rfl) ⟨2060918, by rfl⟩ : syracuseStep 2747891 = 4121837) B4121837
theorem B6180401 : Blo 1626512 6180401 := bstep (se 2 (by rfl) ⟨2317650, by rfl⟩ : syracuseStep 6180401 = 4635301) B4635301
theorem B1830451 : Blo 1626512 1830451 := bstep (se 1 (by rfl) ⟨1372838, by rfl⟩ : syracuseStep 1830451 = 2745677) B2745677
theorem B3911267 : Blo 1626512 3911267 := bstep (se 1 (by rfl) ⟨2933450, by rfl⟩ : syracuseStep 3911267 = 5866901) B5866901
theorem B2748019 : Blo 1626512 2748019 := bstep (se 1 (by rfl) ⟨2061014, by rfl⟩ : syracuseStep 2748019 = 4122029) B4122029
theorem B1830595 : Blo 1626512 1830595 := bstep (se 1 (by rfl) ⟨1372946, by rfl⟩ : syracuseStep 1830595 = 2745893) B2745893
theorem B2059987 : Blo 1626512 2059987 := bstep (se 1 (by rfl) ⟨1544990, by rfl⟩ : syracuseStep 2059987 = 3089981) B3089981
theorem B1650403 : Blo 1626512 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B2060083 : Blo 1626512 2060083 := bstep (se 1 (by rfl) ⟨1545062, by rfl⟩ : syracuseStep 2060083 = 3090125) B3090125
theorem B1830739 : Blo 1626512 1830739 := bstep (se 1 (by rfl) ⟨1373054, by rfl⟩ : syracuseStep 1830739 = 2746109) B2746109
theorem B1830883 : Blo 1626512 1830883 := bstep (se 1 (by rfl) ⟨1373162, by rfl⟩ : syracuseStep 1830883 = 2746325) B2746325
theorem B5492717 : Blo 1626512 5492717 := bstep (se 3 (by rfl) ⟨1029884, by rfl⟩ : syracuseStep 5492717 = 2059769) B2059769
theorem B5492771 : Blo 1626512 5492771 := bstep (se 1 (by rfl) ⟨4119578, by rfl⟩ : syracuseStep 5492771 = 8239157) B8239157
theorem B5214253 : Blo 1626512 5214253 := bstep (se 3 (by rfl) ⟨977672, by rfl⟩ : syracuseStep 5214253 = 1955345) B1955345
theorem B2199601 : Blo 1626512 2199601 := bstep (se 2 (by rfl) ⟨824850, by rfl⟩ : syracuseStep 2199601 = 1649701) B1649701
theorem B9900101 : Blo 1626512 9900101 := bstep (se 4 (by rfl) ⟨928134, by rfl⟩ : syracuseStep 9900101 = 1856269) B1856269
theorem B1831027 : Blo 1626512 1831027 := bstep (se 1 (by rfl) ⟨1373270, by rfl⟩ : syracuseStep 1831027 = 2746541) B2746541
theorem B3911843 : Blo 1626512 3911843 := bstep (se 1 (by rfl) ⟨2933882, by rfl⟩ : syracuseStep 3911843 = 5867765) B5867765
theorem B10432709 : Blo 1626512 10432709 := bstep (se 4 (by rfl) ⟨978066, by rfl⟩ : syracuseStep 10432709 = 1956133) B1956133
theorem B6181069 : Blo 1626512 6181069 := bstep (se 3 (by rfl) ⟨1158950, by rfl⟩ : syracuseStep 6181069 = 2317901) B2317901
theorem B4632785 : Blo 1626512 4632785 := bstep (se 2 (by rfl) ⟨1737294, by rfl⟩ : syracuseStep 4632785 = 3474589) B3474589
theorem B3911921 : Blo 1626512 3911921 := bstep (se 2 (by rfl) ⟨1466970, by rfl⟩ : syracuseStep 3911921 = 2933941) B2933941
theorem B1831171 : Blo 1626512 1831171 := bstep (se 1 (by rfl) ⟨1373378, by rfl⟩ : syracuseStep 1831171 = 2746757) B2746757
theorem B2060579 : Blo 1626512 2060579 := bstep (se 1 (by rfl) ⟨1545434, by rfl⟩ : syracuseStep 2060579 = 3090869) B3090869
theorem B5493041 : Blo 1626512 5493041 := bstep (se 2 (by rfl) ⟨2059890, by rfl⟩ : syracuseStep 5493041 = 4119781) B4119781
theorem B3477809 : Blo 1626512 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B1855795 : Blo 1626512 1855795 := bstep (se 1 (by rfl) ⟨1391846, by rfl⟩ : syracuseStep 1855795 = 2783693) B2783693
theorem B4632977 : Blo 1626512 4632977 := bstep (se 2 (by rfl) ⟨1737366, by rfl⟩ : syracuseStep 4632977 = 3474733) B3474733
theorem B1626515 : Blo 1626512 1626515 := bstep (se 1 (by rfl) ⟨1219886, by rfl⟩ : syracuseStep 1626515 = 2439773) B2439773
theorem B1831315 : Blo 1626512 1831315 := bstep (se 1 (by rfl) ⟨1373486, by rfl⟩ : syracuseStep 1831315 = 2746973) B2746973
theorem B1626531 : Blo 1626512 1626531 := bstep (se 1 (by rfl) ⟨1219898, by rfl⟩ : syracuseStep 1626531 = 2439797) B2439797
theorem B1954211 : Blo 1626512 1954211 := bstep (se 1 (by rfl) ⟨1465658, by rfl⟩ : syracuseStep 1954211 = 2931317) B2931317
theorem B3912113 : Blo 1626512 3912113 := bstep (se 2 (by rfl) ⟨1467042, by rfl⟩ : syracuseStep 3912113 = 2934085) B2934085
theorem B1626547 : Blo 1626512 1626547 := bstep (se 1 (by rfl) ⟨1219910, by rfl⟩ : syracuseStep 1626547 = 2439821) B2439821
theorem B1626563 : Blo 1626512 1626563 := bstep (se 1 (by rfl) ⟨1219922, by rfl⟩ : syracuseStep 1626563 = 2439845) B2439845
theorem B1626579 : Blo 1626512 1626579 := bstep (se 1 (by rfl) ⟨1219934, by rfl⟩ : syracuseStep 1626579 = 2439869) B2439869
theorem B1626595 : Blo 1626512 1626595 := bstep (se 1 (by rfl) ⟨1219946, by rfl⟩ : syracuseStep 1626595 = 2439893) B2439893
theorem B1626611 : Blo 1626512 1626611 := bstep (se 1 (by rfl) ⟨1219958, by rfl⟩ : syracuseStep 1626611 = 2439917) B2439917
theorem B1626627 : Blo 1626512 1626627 := bstep (se 1 (by rfl) ⟨1219970, by rfl⟩ : syracuseStep 1626627 = 2439941) B2439941
theorem B1626643 : Blo 1626512 1626643 := bstep (se 1 (by rfl) ⟨1219982, by rfl⟩ : syracuseStep 1626643 = 2439965) B2439965
theorem B1626659 : Blo 1626512 1626659 := bstep (se 1 (by rfl) ⟨1219994, by rfl⟩ : syracuseStep 1626659 = 2439989) B2439989
theorem B1831459 : Blo 1626512 1831459 := bstep (se 1 (by rfl) ⟨1373594, by rfl⟩ : syracuseStep 1831459 = 2747189) B2747189
theorem B1626675 : Blo 1626512 1626675 := bstep (se 1 (by rfl) ⟨1220006, by rfl⟩ : syracuseStep 1626675 = 2440013) B2440013
theorem B1626691 : Blo 1626512 1626691 := bstep (se 1 (by rfl) ⟨1220018, by rfl⟩ : syracuseStep 1626691 = 2440037) B2440037
theorem B1626707 : Blo 1626512 1626707 := bstep (se 1 (by rfl) ⟨1220030, by rfl⟩ : syracuseStep 1626707 = 2440061) B2440061
theorem B1626723 : Blo 1626512 1626723 := bstep (se 1 (by rfl) ⟨1220042, by rfl⟩ : syracuseStep 1626723 = 2440085) B2440085
theorem B2822755 : Blo 1626512 2822755 := bstep (se 1 (by rfl) ⟨2117066, by rfl⟩ : syracuseStep 2822755 = 4234133) B4234133
theorem B9269873 : Blo 1626512 9269873 := bstep (se 2 (by rfl) ⟨3476202, by rfl⟩ : syracuseStep 9269873 = 6952405) B6952405
theorem B1626739 : Blo 1626512 1626739 := bstep (se 1 (by rfl) ⟨1220054, by rfl⟩ : syracuseStep 1626739 = 2440109) B2440109
theorem B1626755 : Blo 1626512 1626755 := bstep (se 1 (by rfl) ⟨1220066, by rfl⟩ : syracuseStep 1626755 = 2440133) B2440133
theorem B1626771 : Blo 1626512 1626771 := bstep (se 1 (by rfl) ⟨1220078, by rfl⟩ : syracuseStep 1626771 = 2440157) B2440157
theorem B2642593 : Blo 1626512 2642593 := bstep (se 2 (by rfl) ⟨990972, by rfl⟩ : syracuseStep 2642593 = 1981945) B1981945
theorem B1626787 : Blo 1626512 1626787 := bstep (se 1 (by rfl) ⟨1220090, by rfl⟩ : syracuseStep 1626787 = 2440181) B2440181
theorem B4117169 : Blo 1626512 4117169 := bstep (se 2 (by rfl) ⟨1543938, by rfl⟩ : syracuseStep 4117169 = 3087877) B3087877
theorem B1626803 : Blo 1626512 1626803 := bstep (se 1 (by rfl) ⟨1220102, by rfl⟩ : syracuseStep 1626803 = 2440205) B2440205
theorem B1831603 : Blo 1626512 1831603 := bstep (se 1 (by rfl) ⟨1373702, by rfl⟩ : syracuseStep 1831603 = 2747405) B2747405
theorem B1626819 : Blo 1626512 1626819 := bstep (se 1 (by rfl) ⟨1220114, by rfl⟩ : syracuseStep 1626819 = 2440229) B2440229
theorem B3912401 : Blo 1626512 3912401 := bstep (se 2 (by rfl) ⟨1467150, by rfl⟩ : syracuseStep 3912401 = 2934301) B2934301
theorem B1626835 : Blo 1626512 1626835 := bstep (se 1 (by rfl) ⟨1220126, by rfl⟩ : syracuseStep 1626835 = 2440253) B2440253
theorem B1626851 : Blo 1626512 1626851 := bstep (se 1 (by rfl) ⟨1220138, by rfl⟩ : syracuseStep 1626851 = 2440277) B2440277
theorem B1626867 : Blo 1626512 1626867 := bstep (se 1 (by rfl) ⟨1220150, by rfl⟩ : syracuseStep 1626867 = 2440301) B2440301
theorem B1626883 : Blo 1626512 1626883 := bstep (se 1 (by rfl) ⟨1220162, by rfl⟩ : syracuseStep 1626883 = 2440325) B2440325
theorem B1626899 : Blo 1626512 1626899 := bstep (se 1 (by rfl) ⟨1220174, by rfl⟩ : syracuseStep 1626899 = 2440349) B2440349
theorem B1626915 : Blo 1626512 1626915 := bstep (se 1 (by rfl) ⟨1220186, by rfl⟩ : syracuseStep 1626915 = 2440373) B2440373
theorem B1626931 : Blo 1626512 1626931 := bstep (se 1 (by rfl) ⟨1220198, by rfl⟩ : syracuseStep 1626931 = 2440397) B2440397
theorem B1626947 : Blo 1626512 1626947 := bstep (se 1 (by rfl) ⟨1220210, by rfl⟩ : syracuseStep 1626947 = 2440421) B2440421
theorem B1831747 : Blo 1626512 1831747 := bstep (se 1 (by rfl) ⟨1373810, by rfl⟩ : syracuseStep 1831747 = 2747621) B2747621
theorem B5493581 : Blo 1626512 5493581 := bstep (se 3 (by rfl) ⟨1030046, by rfl⟩ : syracuseStep 5493581 = 2060093) B2060093
theorem B1626963 : Blo 1626512 1626963 := bstep (se 1 (by rfl) ⟨1220222, by rfl⟩ : syracuseStep 1626963 = 2440445) B2440445
theorem B1626979 : Blo 1626512 1626979 := bstep (se 1 (by rfl) ⟨1220234, by rfl⟩ : syracuseStep 1626979 = 2440469) B2440469
theorem B1626995 : Blo 1626512 1626995 := bstep (se 1 (by rfl) ⟨1220246, by rfl⟩ : syracuseStep 1626995 = 2440493) B2440493
theorem B1627011 : Blo 1626512 1627011 := bstep (se 1 (by rfl) ⟨1220258, by rfl⟩ : syracuseStep 1627011 = 2440517) B2440517
theorem B5493635 : Blo 1626512 5493635 := bstep (se 1 (by rfl) ⟨4120226, by rfl⟩ : syracuseStep 5493635 = 8240453) B8240453
theorem B1627027 : Blo 1626512 1627027 := bstep (se 1 (by rfl) ⟨1220270, by rfl⟩ : syracuseStep 1627027 = 2440541) B2440541
theorem B1627043 : Blo 1626512 1627043 := bstep (se 1 (by rfl) ⟨1220282, by rfl⟩ : syracuseStep 1627043 = 2440565) B2440565
theorem B1627059 : Blo 1626512 1627059 := bstep (se 1 (by rfl) ⟨1220294, by rfl⟩ : syracuseStep 1627059 = 2440589) B2440589
theorem B1627075 : Blo 1626512 1627075 := bstep (se 1 (by rfl) ⟨1220306, by rfl⟩ : syracuseStep 1627075 = 2440613) B2440613
theorem B59413445 : Blo 1626512 59413445 := bstep (se 4 (by rfl) ⟨5570010, by rfl⟩ : syracuseStep 59413445 = 11140021) B11140021
theorem B1627091 : Blo 1626512 1627091 := bstep (se 1 (by rfl) ⟨1220318, by rfl⟩ : syracuseStep 1627091 = 2440637) B2440637
theorem B1831891 : Blo 1626512 1831891 := bstep (se 1 (by rfl) ⟨1373918, by rfl⟩ : syracuseStep 1831891 = 2747837) B2747837
theorem B1627107 : Blo 1626512 1627107 := bstep (se 1 (by rfl) ⟨1220330, by rfl⟩ : syracuseStep 1627107 = 2440661) B2440661
theorem B6181859 : Blo 1626512 6181859 := bstep (se 1 (by rfl) ⟨4636394, by rfl⟩ : syracuseStep 6181859 = 9272789) B9272789
theorem B1627123 : Blo 1626512 1627123 := bstep (se 1 (by rfl) ⟨1220342, by rfl⟩ : syracuseStep 1627123 = 2440685) B2440685
theorem B1627139 : Blo 1626512 1627139 := bstep (se 1 (by rfl) ⟨1220354, by rfl⟩ : syracuseStep 1627139 = 2440709) B2440709
theorem B1627155 : Blo 1626512 1627155 := bstep (se 1 (by rfl) ⟨1220366, by rfl⟩ : syracuseStep 1627155 = 2440733) B2440733
theorem B1627171 : Blo 1626512 1627171 := bstep (se 1 (by rfl) ⟨1220378, by rfl⟩ : syracuseStep 1627171 = 2440757) B2440757
theorem B1627187 : Blo 1626512 1627187 := bstep (se 1 (by rfl) ⟨1220390, by rfl⟩ : syracuseStep 1627187 = 2440781) B2440781
theorem B1627203 : Blo 1626512 1627203 := bstep (se 1 (by rfl) ⟨1220402, by rfl⟩ : syracuseStep 1627203 = 2440805) B2440805
theorem B1627219 : Blo 1626512 1627219 := bstep (se 1 (by rfl) ⟨1220414, by rfl⟩ : syracuseStep 1627219 = 2440829) B2440829
theorem B1627235 : Blo 1626512 1627235 := bstep (se 1 (by rfl) ⟨1220426, by rfl⟩ : syracuseStep 1627235 = 2440853) B2440853
theorem B1832035 : Blo 1626512 1832035 := bstep (se 1 (by rfl) ⟨1374026, by rfl⟩ : syracuseStep 1832035 = 2748053) B2748053
theorem B8795249 : Blo 1626512 8795249 := bstep (se 2 (by rfl) ⟨3298218, by rfl⟩ : syracuseStep 8795249 = 6596437) B6596437
theorem B1627251 : Blo 1626512 1627251 := bstep (se 1 (by rfl) ⟨1220438, by rfl⟩ : syracuseStep 1627251 = 2440877) B2440877
theorem B1627267 : Blo 1626512 1627267 := bstep (se 1 (by rfl) ⟨1220450, by rfl⟩ : syracuseStep 1627267 = 2440901) B2440901
theorem B5567633 : Blo 1626512 5567633 := bstep (se 2 (by rfl) ⟨2087862, by rfl⟩ : syracuseStep 5567633 = 4175725) B4175725
theorem B5493905 : Blo 1626512 5493905 := bstep (se 2 (by rfl) ⟨2060214, by rfl⟩ : syracuseStep 5493905 = 4120429) B4120429
theorem B1627283 : Blo 1626512 1627283 := bstep (se 1 (by rfl) ⟨1220462, by rfl⟩ : syracuseStep 1627283 = 2440925) B2440925
theorem B5862563 : Blo 1626512 5862563 := bstep (se 1 (by rfl) ⟨4396922, by rfl⟩ : syracuseStep 5862563 = 8793845) B8793845
theorem B1627299 : Blo 1626512 1627299 := bstep (se 1 (by rfl) ⟨1220474, by rfl⟩ : syracuseStep 1627299 = 2440949) B2440949
theorem B6599843 : Blo 1626512 6599843 := bstep (se 1 (by rfl) ⟨4949882, by rfl⟩ : syracuseStep 6599843 = 9899765) B9899765
theorem B1627315 : Blo 1626512 1627315 := bstep (se 1 (by rfl) ⟨1220486, by rfl⟩ : syracuseStep 1627315 = 2440973) B2440973
theorem B1627331 : Blo 1626512 1627331 := bstep (se 1 (by rfl) ⟨1220498, by rfl⟩ : syracuseStep 1627331 = 2440997) B2440997
theorem B1627347 : Blo 1626512 1627347 := bstep (se 1 (by rfl) ⟨1220510, by rfl⟩ : syracuseStep 1627347 = 2441021) B2441021
theorem B15635683 : Blo 1626512 15635683 := bstep (se 1 (by rfl) ⟨11726762, by rfl⟩ : syracuseStep 15635683 = 23453525) B23453525
theorem B1627363 : Blo 1626512 1627363 := bstep (se 1 (by rfl) ⟨1220522, by rfl⟩ : syracuseStep 1627363 = 2441045) B2441045
theorem B1627379 : Blo 1626512 1627379 := bstep (se 1 (by rfl) ⟨1220534, by rfl⟩ : syracuseStep 1627379 = 2441069) B2441069
theorem B1627395 : Blo 1626512 1627395 := bstep (se 1 (by rfl) ⟨1220546, by rfl⟩ : syracuseStep 1627395 = 2441093) B2441093
theorem B1627411 : Blo 1626512 1627411 := bstep (se 1 (by rfl) ⟨1220558, by rfl⟩ : syracuseStep 1627411 = 2441117) B2441117
theorem B10425635 : Blo 1626512 10425635 := bstep (se 1 (by rfl) ⟨7819226, by rfl⟩ : syracuseStep 10425635 = 15638453) B15638453
theorem B1627427 : Blo 1626512 1627427 := bstep (se 1 (by rfl) ⟨1220570, by rfl⟩ : syracuseStep 1627427 = 2441141) B2441141
theorem B1627443 : Blo 1626512 1627443 := bstep (se 1 (by rfl) ⟨1220582, by rfl⟩ : syracuseStep 1627443 = 2441165) B2441165
theorem B1627459 : Blo 1626512 1627459 := bstep (se 1 (by rfl) ⟨1220594, by rfl⟩ : syracuseStep 1627459 = 2441189) B2441189
theorem B1627475 : Blo 1626512 1627475 := bstep (se 1 (by rfl) ⟨1220606, by rfl⟩ : syracuseStep 1627475 = 2441213) B2441213
theorem B1627491 : Blo 1626512 1627491 := bstep (se 1 (by rfl) ⟨1220618, by rfl⟩ : syracuseStep 1627491 = 2441237) B2441237
theorem B20845937 : Blo 1626512 20845937 := bstep (se 2 (by rfl) ⟨7817226, by rfl⟩ : syracuseStep 20845937 = 15634453) B15634453
theorem B4633969 : Blo 1626512 4633969 := bstep (se 2 (by rfl) ⟨1737738, by rfl⟩ : syracuseStep 4633969 = 3475477) B3475477
theorem B1627507 : Blo 1626512 1627507 := bstep (se 1 (by rfl) ⟨1220630, by rfl⟩ : syracuseStep 1627507 = 2441261) B2441261
theorem B1627523 : Blo 1626512 1627523 := bstep (se 1 (by rfl) ⟨1220642, by rfl⟩ : syracuseStep 1627523 = 2441285) B2441285
theorem B1627539 : Blo 1626512 1627539 := bstep (se 1 (by rfl) ⟨1220654, by rfl⟩ : syracuseStep 1627539 = 2441309) B2441309
theorem B1627555 : Blo 1626512 1627555 := bstep (se 1 (by rfl) ⟨1220666, by rfl⟩ : syracuseStep 1627555 = 2441333) B2441333
theorem B1627571 : Blo 1626512 1627571 := bstep (se 1 (by rfl) ⟨1220678, by rfl⟩ : syracuseStep 1627571 = 2441357) B2441357
theorem B1627587 : Blo 1626512 1627587 := bstep (se 1 (by rfl) ⟨1220690, by rfl⟩ : syracuseStep 1627587 = 2441381) B2441381
theorem B1627603 : Blo 1626512 1627603 := bstep (se 1 (by rfl) ⟨1220702, by rfl⟩ : syracuseStep 1627603 = 2441405) B2441405
theorem B1627619 : Blo 1626512 1627619 := bstep (se 1 (by rfl) ⟨1220714, by rfl⟩ : syracuseStep 1627619 = 2441429) B2441429
theorem B5215715 : Blo 1626512 5215715 := bstep (se 1 (by rfl) ⟨3911786, by rfl⟩ : syracuseStep 5215715 = 7823573) B7823573
theorem B1627635 : Blo 1626512 1627635 := bstep (se 1 (by rfl) ⟨1220726, by rfl⟩ : syracuseStep 1627635 = 2441453) B2441453
theorem B1627651 : Blo 1626512 1627651 := bstep (se 1 (by rfl) ⟨1220738, by rfl⟩ : syracuseStep 1627651 = 2441477) B2441477
theorem B1627667 : Blo 1626512 1627667 := bstep (se 1 (by rfl) ⟨1220750, by rfl⟩ : syracuseStep 1627667 = 2441501) B2441501
theorem B1627683 : Blo 1626512 1627683 := bstep (se 1 (by rfl) ⟨1220762, by rfl⟩ : syracuseStep 1627683 = 2441525) B2441525
theorem B1627699 : Blo 1626512 1627699 := bstep (se 1 (by rfl) ⟨1220774, by rfl⟩ : syracuseStep 1627699 = 2441549) B2441549
theorem B1627715 : Blo 1626512 1627715 := bstep (se 1 (by rfl) ⟨1220786, by rfl⟩ : syracuseStep 1627715 = 2441573) B2441573
theorem B1627731 : Blo 1626512 1627731 := bstep (se 1 (by rfl) ⟨1220798, by rfl⟩ : syracuseStep 1627731 = 2441597) B2441597
theorem B1627747 : Blo 1626512 1627747 := bstep (se 1 (by rfl) ⟨1220810, by rfl⟩ : syracuseStep 1627747 = 2441621) B2441621
theorem B6182513 : Blo 1626512 6182513 := bstep (se 2 (by rfl) ⟨2318442, by rfl⟩ : syracuseStep 6182513 = 4636885) B4636885
theorem B2315891 : Blo 1626512 2315891 := bstep (se 1 (by rfl) ⟨1736918, by rfl⟩ : syracuseStep 2315891 = 3473837) B3473837
theorem B1627763 : Blo 1626512 1627763 := bstep (se 1 (by rfl) ⟨1220822, by rfl⟩ : syracuseStep 1627763 = 2441645) B2441645
theorem B4634243 : Blo 1626512 4634243 := bstep (se 1 (by rfl) ⟨3475682, by rfl⟩ : syracuseStep 4634243 = 6951365) B6951365
theorem B1627779 : Blo 1626512 1627779 := bstep (se 1 (by rfl) ⟨1220834, by rfl⟩ : syracuseStep 1627779 = 2441669) B2441669
theorem B31266445 : Blo 1626512 31266445 := bstep (se 3 (by rfl) ⟨5862458, by rfl⟩ : syracuseStep 31266445 = 11724917) B11724917
theorem B4118161 : Blo 1626512 4118161 := bstep (se 2 (by rfl) ⟨1544310, by rfl⟩ : syracuseStep 4118161 = 3088621) B3088621
theorem B1627795 : Blo 1626512 1627795 := bstep (se 1 (by rfl) ⟨1220846, by rfl⟩ : syracuseStep 1627795 = 2441693) B2441693
theorem B1627811 : Blo 1626512 1627811 := bstep (se 1 (by rfl) ⟨1220858, by rfl⟩ : syracuseStep 1627811 = 2441717) B2441717
theorem B5494445 : Blo 1626512 5494445 := bstep (se 3 (by rfl) ⟨1030208, by rfl⟩ : syracuseStep 5494445 = 2060417) B2060417
theorem B1627827 : Blo 1626512 1627827 := bstep (se 1 (by rfl) ⟨1220870, by rfl⟩ : syracuseStep 1627827 = 2441741) B2441741
theorem B1627843 : Blo 1626512 1627843 := bstep (se 1 (by rfl) ⟨1220882, by rfl⟩ : syracuseStep 1627843 = 2441765) B2441765
theorem B1627859 : Blo 1626512 1627859 := bstep (se 1 (by rfl) ⟨1220894, by rfl⟩ : syracuseStep 1627859 = 2441789) B2441789
theorem B1627875 : Blo 1626512 1627875 := bstep (se 1 (by rfl) ⟨1220906, by rfl⟩ : syracuseStep 1627875 = 2441813) B2441813
theorem B5494499 : Blo 1626512 5494499 := bstep (se 1 (by rfl) ⟨4120874, by rfl⟩ : syracuseStep 5494499 = 8241749) B8241749
theorem B4396781 : Blo 1626512 4396781 := bstep (se 3 (by rfl) ⟨824396, by rfl⟩ : syracuseStep 4396781 = 1648793) B1648793
theorem B10426097 : Blo 1626512 10426097 := bstep (se 2 (by rfl) ⟨3909786, by rfl⟩ : syracuseStep 10426097 = 7819573) B7819573
theorem B8238833 : Blo 1626512 8238833 := bstep (se 2 (by rfl) ⟨3089562, by rfl⟩ : syracuseStep 8238833 = 6179125) B6179125
theorem B1627891 : Blo 1626512 1627891 := bstep (se 1 (by rfl) ⟨1220918, by rfl⟩ : syracuseStep 1627891 = 2441837) B2441837
theorem B5215985 : Blo 1626512 5215985 := bstep (se 2 (by rfl) ⟨1955994, by rfl⟩ : syracuseStep 5215985 = 3911989) B3911989
theorem B1627907 : Blo 1626512 1627907 := bstep (se 1 (by rfl) ⟨1220930, by rfl⟩ : syracuseStep 1627907 = 2441861) B2441861
theorem B1627923 : Blo 1626512 1627923 := bstep (se 1 (by rfl) ⟨1220942, by rfl⟩ : syracuseStep 1627923 = 2441885) B2441885
theorem B1627939 : Blo 1626512 1627939 := bstep (se 1 (by rfl) ⟨1220954, by rfl⟩ : syracuseStep 1627939 = 2441909) B2441909
theorem B1627955 : Blo 1626512 1627955 := bstep (se 1 (by rfl) ⟨1220966, by rfl⟩ : syracuseStep 1627955 = 2441933) B2441933
theorem B4634435 : Blo 1626512 4634435 := bstep (se 1 (by rfl) ⟨3475826, by rfl⟩ : syracuseStep 4634435 = 6951653) B6951653
theorem B1627971 : Blo 1626512 1627971 := bstep (se 1 (by rfl) ⟨1220978, by rfl⟩ : syracuseStep 1627971 = 2441957) B2441957
theorem B1627987 : Blo 1626512 1627987 := bstep (se 1 (by rfl) ⟨1220990, by rfl⟩ : syracuseStep 1627987 = 2441981) B2441981
theorem B1628003 : Blo 1626512 1628003 := bstep (se 1 (by rfl) ⟨1221002, by rfl⟩ : syracuseStep 1628003 = 2442005) B2442005
theorem B1628019 : Blo 1626512 1628019 := bstep (se 1 (by rfl) ⟨1221014, by rfl⟩ : syracuseStep 1628019 = 2442029) B2442029
theorem B1628035 : Blo 1626512 1628035 := bstep (se 1 (by rfl) ⟨1221026, by rfl⟩ : syracuseStep 1628035 = 2442053) B2442053
theorem B1628051 : Blo 1626512 1628051 := bstep (se 1 (by rfl) ⟨1221038, by rfl⟩ : syracuseStep 1628051 = 2442077) B2442077
theorem B4118435 : Blo 1626512 4118435 := bstep (se 1 (by rfl) ⟨3088826, by rfl⟩ : syracuseStep 4118435 = 6177653) B6177653
theorem B1628067 : Blo 1626512 1628067 := bstep (se 1 (by rfl) ⟨1221050, by rfl⟩ : syracuseStep 1628067 = 2442101) B2442101
theorem B1628083 : Blo 1626512 1628083 := bstep (se 1 (by rfl) ⟨1221062, by rfl⟩ : syracuseStep 1628083 = 2442125) B2442125
theorem B1628099 : Blo 1626512 1628099 := bstep (se 1 (by rfl) ⟨1221074, by rfl⟩ : syracuseStep 1628099 = 2442149) B2442149
theorem B1628115 : Blo 1626512 1628115 := bstep (se 1 (by rfl) ⟨1221086, by rfl⟩ : syracuseStep 1628115 = 2442173) B2442173
theorem B1628131 : Blo 1626512 1628131 := bstep (se 1 (by rfl) ⟨1221098, by rfl⟩ : syracuseStep 1628131 = 2442197) B2442197
theorem B5494769 : Blo 1626512 5494769 := bstep (se 2 (by rfl) ⟨2060538, by rfl⟩ : syracuseStep 5494769 = 4121077) B4121077
theorem B1628147 : Blo 1626512 1628147 := bstep (se 1 (by rfl) ⟨1221110, by rfl⟩ : syracuseStep 1628147 = 2442221) B2442221
theorem B1628163 : Blo 1626512 1628163 := bstep (se 1 (by rfl) ⟨1221122, by rfl⟩ : syracuseStep 1628163 = 2442245) B2442245
theorem B1628179 : Blo 1626512 1628179 := bstep (se 1 (by rfl) ⟨1221134, by rfl⟩ : syracuseStep 1628179 = 2442269) B2442269
theorem B9271331 : Blo 1626512 9271331 := bstep (se 1 (by rfl) ⟨6953498, by rfl⟩ : syracuseStep 9271331 = 13906997) B13906997
theorem B1628195 : Blo 1626512 1628195 := bstep (se 1 (by rfl) ⟨1221146, by rfl⟩ : syracuseStep 1628195 = 2442293) B2442293
theorem B1628211 : Blo 1626512 1628211 := bstep (se 1 (by rfl) ⟨1221158, by rfl⟩ : syracuseStep 1628211 = 2442317) B2442317
theorem B3962947 : Blo 1626512 3962947 := bstep (se 1 (by rfl) ⟨2972210, by rfl⟩ : syracuseStep 3962947 = 5944421) B5944421
theorem B1628227 : Blo 1626512 1628227 := bstep (se 1 (by rfl) ⟨1221170, by rfl⟩ : syracuseStep 1628227 = 2442341) B2442341
theorem B1628243 : Blo 1626512 1628243 := bstep (se 1 (by rfl) ⟨1221182, by rfl⟩ : syracuseStep 1628243 = 2442365) B2442365
theorem B4118627 : Blo 1626512 4118627 := bstep (se 1 (by rfl) ⟨3088970, by rfl⟩ : syracuseStep 4118627 = 6177941) B6177941
theorem B1628259 : Blo 1626512 1628259 := bstep (se 1 (by rfl) ⟨1221194, by rfl⟩ : syracuseStep 1628259 = 2442389) B2442389
theorem B1628275 : Blo 1626512 1628275 := bstep (se 1 (by rfl) ⟨1221206, by rfl⟩ : syracuseStep 1628275 = 2442413) B2442413
theorem B1628291 : Blo 1626512 1628291 := bstep (se 1 (by rfl) ⟨1221218, by rfl⟩ : syracuseStep 1628291 = 2442437) B2442437
theorem B3659921 : Blo 1626512 3659921 := bstep (se 2 (by rfl) ⟨1372470, by rfl⟩ : syracuseStep 3659921 = 2744941) B2744941
theorem B1628307 : Blo 1626512 1628307 := bstep (se 1 (by rfl) ⟨1221230, by rfl⟩ : syracuseStep 1628307 = 2442461) B2442461
theorem B3659939 : Blo 1626512 3659939 := bstep (se 1 (by rfl) ⟨2744954, by rfl⟩ : syracuseStep 3659939 = 5489909) B5489909
theorem B1628323 : Blo 1626512 1628323 := bstep (se 1 (by rfl) ⟨1221242, by rfl⟩ : syracuseStep 1628323 = 2442485) B2442485
theorem B1628339 : Blo 1626512 1628339 := bstep (se 1 (by rfl) ⟨1221254, by rfl⟩ : syracuseStep 1628339 = 2442509) B2442509
theorem B1628355 : Blo 1626512 1628355 := bstep (se 1 (by rfl) ⟨1221266, by rfl⟩ : syracuseStep 1628355 = 2442533) B2442533
theorem B1628371 : Blo 1626512 1628371 := bstep (se 1 (by rfl) ⟨1221278, by rfl⟩ : syracuseStep 1628371 = 2442557) B2442557
theorem B1628387 : Blo 1626512 1628387 := bstep (se 1 (by rfl) ⟨1221290, by rfl⟩ : syracuseStep 1628387 = 2442581) B2442581
theorem B2316529 : Blo 1626512 2316529 := bstep (se 2 (by rfl) ⟨868698, by rfl⟩ : syracuseStep 2316529 = 1737397) B1737397
theorem B2783473 : Blo 1626512 2783473 := bstep (se 2 (by rfl) ⟨1043802, by rfl⟩ : syracuseStep 2783473 = 2087605) B2087605
theorem B1628403 : Blo 1626512 1628403 := bstep (se 1 (by rfl) ⟨1221302, by rfl⟩ : syracuseStep 1628403 = 2442605) B2442605
theorem B1628419 : Blo 1626512 1628419 := bstep (se 1 (by rfl) ⟨1221314, by rfl⟩ : syracuseStep 1628419 = 2442629) B2442629
theorem B1628435 : Blo 1626512 1628435 := bstep (se 1 (by rfl) ⟨1221326, by rfl⟩ : syracuseStep 1628435 = 2442653) B2442653
theorem B1628451 : Blo 1626512 1628451 := bstep (se 1 (by rfl) ⟨1221338, by rfl⟩ : syracuseStep 1628451 = 2442677) B2442677
theorem B1628467 : Blo 1626512 1628467 := bstep (se 1 (by rfl) ⟨1221350, by rfl⟩ : syracuseStep 1628467 = 2442701) B2442701
theorem B1628483 : Blo 1626512 1628483 := bstep (se 1 (by rfl) ⟨1221362, by rfl⟩ : syracuseStep 1628483 = 2442725) B2442725
theorem B5863757 : Blo 1626512 5863757 := bstep (se 3 (by rfl) ⟨1099454, by rfl⟩ : syracuseStep 5863757 = 2198909) B2198909
theorem B6953293 : Blo 1626512 6953293 := bstep (se 3 (by rfl) ⟨1303742, by rfl⟩ : syracuseStep 6953293 = 2607485) B2607485
theorem B1628499 : Blo 1626512 1628499 := bstep (se 1 (by rfl) ⟨1221374, by rfl⟩ : syracuseStep 1628499 = 2442749) B2442749
theorem B2783585 : Blo 1626512 2783585 := bstep (se 2 (by rfl) ⟨1043844, by rfl⟩ : syracuseStep 2783585 = 2087689) B2087689
theorem B5863843 : Blo 1626512 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B3660209 : Blo 1626512 3660209 := bstep (se 2 (by rfl) ⟨1372578, by rfl⟩ : syracuseStep 3660209 = 2745157) B2745157
theorem B3660227 : Blo 1626512 3660227 := bstep (se 1 (by rfl) ⟨2745170, by rfl⟩ : syracuseStep 3660227 = 5490341) B5490341
theorem B5495309 : Blo 1626512 5495309 := bstep (se 3 (by rfl) ⟨1030370, by rfl⟩ : syracuseStep 5495309 = 2060741) B2060741
theorem B2316865 : Blo 1626512 2316865 := bstep (se 2 (by rfl) ⟨868824, by rfl⟩ : syracuseStep 2316865 = 1737649) B1737649
theorem B5495363 : Blo 1626512 5495363 := bstep (se 1 (by rfl) ⟨4121522, by rfl⟩ : syracuseStep 5495363 = 8243045) B8243045
theorem B2439779 : Blo 1626512 2439779 := bstep (se 1 (by rfl) ⟨1829834, by rfl⟩ : syracuseStep 2439779 = 3659669) B3659669
theorem B4635245 : Blo 1626512 4635245 := bstep (se 3 (by rfl) ⟨869108, by rfl⟩ : syracuseStep 4635245 = 1738217) B1738217
theorem B47536753 : Blo 1626512 47536753 := bstep (se 2 (by rfl) ⟨17826282, by rfl⟩ : syracuseStep 47536753 = 35652565) B35652565
theorem B2439809 : Blo 1626512 2439809 := bstep (se 2 (by rfl) ⟨914928, by rfl⟩ : syracuseStep 2439809 = 1829857) B1829857
theorem B9394829 : Blo 1626512 9394829 := bstep (se 3 (by rfl) ⟨1761530, by rfl⟩ : syracuseStep 9394829 = 3523061) B3523061
theorem B2439827 : Blo 1626512 2439827 := bstep (se 1 (by rfl) ⟨1829870, by rfl⟩ : syracuseStep 2439827 = 3659741) B3659741
theorem B2439857 : Blo 1626512 2439857 := bstep (se 2 (by rfl) ⟨914946, by rfl⟩ : syracuseStep 2439857 = 1829893) B1829893
theorem B2439875 : Blo 1626512 2439875 := bstep (se 1 (by rfl) ⟨1829906, by rfl⟩ : syracuseStep 2439875 = 3659813) B3659813
theorem B3660497 : Blo 1626512 3660497 := bstep (se 2 (by rfl) ⟨1372686, by rfl⟩ : syracuseStep 3660497 = 2745373) B2745373
theorem B2439905 : Blo 1626512 2439905 := bstep (se 2 (by rfl) ⟨914964, by rfl⟩ : syracuseStep 2439905 = 1829929) B1829929
theorem B3660515 : Blo 1626512 3660515 := bstep (se 1 (by rfl) ⟨2745386, by rfl⟩ : syracuseStep 3660515 = 5490773) B5490773
theorem B2439923 : Blo 1626512 2439923 := bstep (se 1 (by rfl) ⟨1829942, by rfl⟩ : syracuseStep 2439923 = 3659885) B3659885
theorem B2439953 : Blo 1626512 2439953 := bstep (se 2 (by rfl) ⟨914982, by rfl⟩ : syracuseStep 2439953 = 1829965) B1829965
theorem B2439971 : Blo 1626512 2439971 := bstep (se 1 (by rfl) ⟨1829978, by rfl⟩ : syracuseStep 2439971 = 3659957) B3659957
theorem B4635427 : Blo 1626512 4635427 := bstep (se 1 (by rfl) ⟨3476570, by rfl⟩ : syracuseStep 4635427 = 6953141) B6953141
theorem B2440001 : Blo 1626512 2440001 := bstep (se 2 (by rfl) ⟨915000, by rfl⟩ : syracuseStep 2440001 = 1830001) B1830001
theorem B5495633 : Blo 1626512 5495633 := bstep (se 2 (by rfl) ⟨2060862, by rfl⟩ : syracuseStep 5495633 = 4121725) B4121725
theorem B2440019 : Blo 1626512 2440019 := bstep (se 1 (by rfl) ⟨1830014, by rfl⟩ : syracuseStep 2440019 = 3660029) B3660029
theorem B2440049 : Blo 1626512 2440049 := bstep (se 2 (by rfl) ⟨915018, by rfl⟩ : syracuseStep 2440049 = 1830037) B1830037
theorem B2440067 : Blo 1626512 2440067 := bstep (se 1 (by rfl) ⟨1830050, by rfl⟩ : syracuseStep 2440067 = 3660101) B3660101
theorem B2440097 : Blo 1626512 2440097 := bstep (se 2 (by rfl) ⟨915036, by rfl⟩ : syracuseStep 2440097 = 1830073) B1830073
theorem B2440115 : Blo 1626512 2440115 := bstep (se 1 (by rfl) ⟨1830086, by rfl⟩ : syracuseStep 2440115 = 3660173) B3660173
theorem B2440145 : Blo 1626512 2440145 := bstep (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) B1830109
theorem B2440163 : Blo 1626512 2440163 := bstep (se 1 (by rfl) ⟨1830122, by rfl⟩ : syracuseStep 2440163 = 3660245) B3660245
theorem B3660785 : Blo 1626512 3660785 := bstep (se 2 (by rfl) ⟨1372794, by rfl⟩ : syracuseStep 3660785 = 2745589) B2745589
theorem B2440193 : Blo 1626512 2440193 := bstep (se 2 (by rfl) ⟨915072, by rfl⟩ : syracuseStep 2440193 = 1830145) B1830145
theorem B3660803 : Blo 1626512 3660803 := bstep (se 1 (by rfl) ⟨2745602, by rfl⟩ : syracuseStep 3660803 = 5491205) B5491205
theorem B9272333 : Blo 1626512 9272333 := bstep (se 3 (by rfl) ⟨1738562, by rfl⟩ : syracuseStep 9272333 = 3477125) B3477125
theorem B4119569 : Blo 1626512 4119569 := bstep (se 2 (by rfl) ⟨1544838, by rfl⟩ : syracuseStep 4119569 = 3089677) B3089677
theorem B2440211 : Blo 1626512 2440211 := bstep (se 1 (by rfl) ⟨1830158, by rfl⟩ : syracuseStep 2440211 = 3660317) B3660317
theorem B2440241 : Blo 1626512 2440241 := bstep (se 2 (by rfl) ⟨915090, by rfl⟩ : syracuseStep 2440241 = 1830181) B1830181
theorem B2440259 : Blo 1626512 2440259 := bstep (se 1 (by rfl) ⟨1830194, by rfl⟩ : syracuseStep 2440259 = 3660389) B3660389
theorem B4119619 : Blo 1626512 4119619 := bstep (se 1 (by rfl) ⟨3089714, by rfl⟩ : syracuseStep 4119619 = 6179429) B6179429
theorem B15858757 : Blo 1626512 15858757 := bstep (se 4 (by rfl) ⟨1486758, by rfl⟩ : syracuseStep 15858757 = 2973517) B2973517
theorem B2440289 : Blo 1626512 2440289 := bstep (se 2 (by rfl) ⟨915108, by rfl⟩ : syracuseStep 2440289 = 1830217) B1830217
theorem B2440307 : Blo 1626512 2440307 := bstep (se 1 (by rfl) ⟨1830230, by rfl⟩ : syracuseStep 2440307 = 3660461) B3660461
theorem B4947085 : Blo 1626512 4947085 := bstep (se 3 (by rfl) ⟨927578, by rfl⟩ : syracuseStep 4947085 = 1855157) B1855157
theorem B2440337 : Blo 1626512 2440337 := bstep (se 2 (by rfl) ⟨915126, by rfl⟩ : syracuseStep 2440337 = 1830253) B1830253
theorem B2317457 : Blo 1626512 2317457 := bstep (se 2 (by rfl) ⟨869046, by rfl⟩ : syracuseStep 2317457 = 1738093) B1738093
theorem B2440355 : Blo 1626512 2440355 := bstep (se 1 (by rfl) ⟨1830266, by rfl⟩ : syracuseStep 2440355 = 3660533) B3660533
theorem B8240291 : Blo 1626512 8240291 := bstep (se 1 (by rfl) ⟨6180218, by rfl⟩ : syracuseStep 8240291 = 12360437) B12360437
theorem B2440385 : Blo 1626512 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B4119761 : Blo 1626512 4119761 := bstep (se 2 (by rfl) ⟨1544910, by rfl⟩ : syracuseStep 4119761 = 3089821) B3089821
theorem B2440403 : Blo 1626512 2440403 := bstep (se 1 (by rfl) ⟨1830302, by rfl⟩ : syracuseStep 2440403 = 3660605) B3660605
theorem B2440433 : Blo 1626512 2440433 := bstep (se 2 (by rfl) ⟨915162, by rfl⟩ : syracuseStep 2440433 = 1830325) B1830325
theorem B2440451 : Blo 1626512 2440451 := bstep (se 1 (by rfl) ⟨1830338, by rfl⟩ : syracuseStep 2440451 = 3660677) B3660677
theorem B4635917 : Blo 1626512 4635917 := bstep (se 3 (by rfl) ⟨869234, by rfl⟩ : syracuseStep 4635917 = 1738469) B1738469
theorem B3661073 : Blo 1626512 3661073 := bstep (se 2 (by rfl) ⟨1372902, by rfl⟩ : syracuseStep 3661073 = 2745805) B2745805
theorem B2440481 : Blo 1626512 2440481 := bstep (se 2 (by rfl) ⟨915180, by rfl⟩ : syracuseStep 2440481 = 1830361) B1830361
theorem B3661091 : Blo 1626512 3661091 := bstep (se 1 (by rfl) ⟨2745818, by rfl⟩ : syracuseStep 3661091 = 5491637) B5491637
theorem B2440499 : Blo 1626512 2440499 := bstep (se 1 (by rfl) ⟨1830374, by rfl⟩ : syracuseStep 2440499 = 3660749) B3660749
theorem B20847941 : Blo 1626512 20847941 := bstep (se 4 (by rfl) ⟨1954494, by rfl⟩ : syracuseStep 20847941 = 3908989) B3908989
theorem B2440529 : Blo 1626512 2440529 := bstep (se 2 (by rfl) ⟨915198, by rfl⟩ : syracuseStep 2440529 = 1830397) B1830397
theorem B3964241 : Blo 1626512 3964241 := bstep (se 2 (by rfl) ⟨1486590, by rfl⟩ : syracuseStep 3964241 = 2973181) B2973181
theorem B2440547 : Blo 1626512 2440547 := bstep (se 1 (by rfl) ⟨1830410, by rfl⟩ : syracuseStep 2440547 = 3660821) B3660821
theorem B5496173 : Blo 1626512 5496173 := bstep (se 3 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 5496173 = 2061065) B2061065
theorem B2440577 : Blo 1626512 2440577 := bstep (se 2 (by rfl) ⟨915216, by rfl⟩ : syracuseStep 2440577 = 1830433) B1830433
theorem B2440595 : Blo 1626512 2440595 := bstep (se 1 (by rfl) ⟨1830446, by rfl⟩ : syracuseStep 2440595 = 3660893) B3660893
theorem B5496227 : Blo 1626512 5496227 := bstep (se 1 (by rfl) ⟨4122170, by rfl⟩ : syracuseStep 5496227 = 8244341) B8244341
theorem B2440625 : Blo 1626512 2440625 := bstep (se 2 (by rfl) ⟨915234, by rfl⟩ : syracuseStep 2440625 = 1830469) B1830469
theorem B5864881 : Blo 1626512 5864881 := bstep (se 2 (by rfl) ⟨2199330, by rfl⟩ : syracuseStep 5864881 = 4398661) B4398661
theorem B1760707 : Blo 1626512 1760707 := bstep (se 1 (by rfl) ⟨1320530, by rfl⟩ : syracuseStep 1760707 = 2641061) B2641061
theorem B2440643 : Blo 1626512 2440643 := bstep (se 1 (by rfl) ⟨1830482, by rfl⟩ : syracuseStep 2440643 = 3660965) B3660965
theorem B16711109 : Blo 1626512 16711109 := bstep (se 4 (by rfl) ⟨1566666, by rfl⟩ : syracuseStep 16711109 = 3133333) B3133333
theorem B2440673 : Blo 1626512 2440673 := bstep (se 2 (by rfl) ⟨915252, by rfl⟩ : syracuseStep 2440673 = 1830505) B1830505
theorem B2440691 : Blo 1626512 2440691 := bstep (se 1 (by rfl) ⟨1830518, by rfl⟩ : syracuseStep 2440691 = 3661037) B3661037
theorem B2440721 : Blo 1626512 2440721 := bstep (se 2 (by rfl) ⟨915270, by rfl⟩ : syracuseStep 2440721 = 1830541) B1830541
theorem B2440739 : Blo 1626512 2440739 := bstep (se 1 (by rfl) ⟨1830554, by rfl⟩ : syracuseStep 2440739 = 3661109) B3661109
theorem B3661361 : Blo 1626512 3661361 := bstep (se 2 (by rfl) ⟨1373010, by rfl⟩ : syracuseStep 3661361 = 2746021) B2746021
theorem B2440769 : Blo 1626512 2440769 := bstep (se 2 (by rfl) ⟨915288, by rfl⟩ : syracuseStep 2440769 = 1830577) B1830577
theorem B3661379 : Blo 1626512 3661379 := bstep (se 1 (by rfl) ⟨2746034, by rfl⟩ : syracuseStep 3661379 = 5492069) B5492069
theorem B3087953 : Blo 1626512 3087953 := bstep (se 2 (by rfl) ⟨1157982, by rfl⟩ : syracuseStep 3087953 = 2315965) B2315965
theorem B2440787 : Blo 1626512 2440787 := bstep (se 1 (by rfl) ⟨1830590, by rfl⟩ : syracuseStep 2440787 = 3661181) B3661181
theorem B23453297 : Blo 1626512 23453297 := bstep (se 2 (by rfl) ⟨8794986, by rfl⟩ : syracuseStep 23453297 = 17589973) B17589973
theorem B2440817 : Blo 1626512 2440817 := bstep (se 2 (by rfl) ⟨915306, by rfl⟩ : syracuseStep 2440817 = 1830613) B1830613
theorem B2440835 : Blo 1626512 2440835 := bstep (se 1 (by rfl) ⟨1830626, by rfl⟩ : syracuseStep 2440835 = 3661253) B3661253
theorem B2932355 : Blo 1626512 2932355 := bstep (se 1 (by rfl) ⟨2199266, by rfl⟩ : syracuseStep 2932355 = 4398533) B4398533
theorem B2440865 : Blo 1626512 2440865 := bstep (se 2 (by rfl) ⟨915324, by rfl⟩ : syracuseStep 2440865 = 1830649) B1830649
theorem B11132579 : Blo 1626512 11132579 := bstep (se 1 (by rfl) ⟨8349434, by rfl⟩ : syracuseStep 11132579 = 16698869) B16698869
theorem B2317987 : Blo 1626512 2317987 := bstep (se 1 (by rfl) ⟨1738490, by rfl⟩ : syracuseStep 2317987 = 3476981) B3476981
theorem B9903779 : Blo 1626512 9903779 := bstep (se 1 (by rfl) ⟨7427834, by rfl⟩ : syracuseStep 9903779 = 14855669) B14855669
theorem B2440883 : Blo 1626512 2440883 := bstep (se 1 (by rfl) ⟨1830662, by rfl⟩ : syracuseStep 2440883 = 3661325) B3661325
theorem B2440913 : Blo 1626512 2440913 := bstep (se 2 (by rfl) ⟨915342, by rfl⟩ : syracuseStep 2440913 = 1830685) B1830685
theorem B6176483 : Blo 1626512 6176483 := bstep (se 1 (by rfl) ⟨4632362, by rfl⟩ : syracuseStep 6176483 = 9264725) B9264725
theorem B2440931 : Blo 1626512 2440931 := bstep (se 1 (by rfl) ⟨1830698, by rfl⟩ : syracuseStep 2440931 = 3661397) B3661397
theorem B2440961 : Blo 1626512 2440961 := bstep (se 2 (by rfl) ⟨915360, by rfl⟩ : syracuseStep 2440961 = 1830721) B1830721
theorem B2440979 : Blo 1626512 2440979 := bstep (se 1 (by rfl) ⟨1830734, by rfl⟩ : syracuseStep 2440979 = 3661469) B3661469
theorem B2441009 : Blo 1626512 2441009 := bstep (se 2 (by rfl) ⟨915378, by rfl⟩ : syracuseStep 2441009 = 1830757) B1830757
theorem B2441027 : Blo 1626512 2441027 := bstep (se 1 (by rfl) ⟨1830770, by rfl⟩ : syracuseStep 2441027 = 3661541) B3661541
theorem B3661649 : Blo 1626512 3661649 := bstep (se 2 (by rfl) ⟨1373118, by rfl⟩ : syracuseStep 3661649 = 2746237) B2746237
theorem B2441057 : Blo 1626512 2441057 := bstep (se 2 (by rfl) ⟨915396, by rfl⟩ : syracuseStep 2441057 = 1830793) B1830793
theorem B3661667 : Blo 1626512 3661667 := bstep (se 1 (by rfl) ⟨2746250, by rfl⟩ : syracuseStep 3661667 = 5492501) B5492501
theorem B5865329 : Blo 1626512 5865329 := bstep (se 2 (by rfl) ⟨2199498, by rfl⟩ : syracuseStep 5865329 = 4398997) B4398997
theorem B2441075 : Blo 1626512 2441075 := bstep (se 1 (by rfl) ⟨1830806, by rfl⟩ : syracuseStep 2441075 = 3661613) B3661613
theorem B2441105 : Blo 1626512 2441105 := bstep (se 2 (by rfl) ⟨915414, by rfl⟩ : syracuseStep 2441105 = 1830829) B1830829
theorem B2441123 : Blo 1626512 2441123 := bstep (se 1 (by rfl) ⟨1830842, by rfl⟩ : syracuseStep 2441123 = 3661685) B3661685
theorem B2441153 : Blo 1626512 2441153 := bstep (se 2 (by rfl) ⟨915432, by rfl⟩ : syracuseStep 2441153 = 1830865) B1830865
theorem B5644237 : Blo 1626512 5644237 := bstep (se 3 (by rfl) ⟨1058294, by rfl⟩ : syracuseStep 5644237 = 2116589) B2116589
theorem B8241101 : Blo 1626512 8241101 := bstep (se 3 (by rfl) ⟨1545206, by rfl⟩ : syracuseStep 8241101 = 3090413) B3090413
theorem B2441171 : Blo 1626512 2441171 := bstep (se 1 (by rfl) ⟨1830878, by rfl⟩ : syracuseStep 2441171 = 3661757) B3661757
theorem B2441201 : Blo 1626512 2441201 := bstep (se 2 (by rfl) ⟨915450, by rfl⟩ : syracuseStep 2441201 = 1830901) B1830901
theorem B2318323 : Blo 1626512 2318323 := bstep (se 1 (by rfl) ⟨1738742, by rfl⟩ : syracuseStep 2318323 = 3477485) B3477485
theorem B3661847 : Blo 1626512 3661847 := bstep (se 1 (by rfl) ⟨2746385, by rfl⟩ : syracuseStep 3661847 = 5492771) B5492771
theorem B2441291 : Blo 1626512 2441291 := bstep (se 1 (by rfl) ⟨1830968, by rfl⟩ : syracuseStep 2441291 = 3661937) B3661937
theorem B2441303 : Blo 1626512 2441303 := bstep (se 1 (by rfl) ⟨1830977, by rfl⟩ : syracuseStep 2441303 = 3661955) B3661955
theorem B5283929 : Blo 1626512 5283929 := bstep (se 2 (by rfl) ⟨1981473, by rfl⟩ : syracuseStep 5283929 = 3962947) B3962947
theorem B6955139 : Blo 1626512 6955139 := bstep (se 1 (by rfl) ⟨5216354, by rfl⟩ : syracuseStep 6955139 = 10432709) B10432709
theorem B3088523 : Blo 1626512 3088523 := bstep (se 1 (by rfl) ⟨2316392, by rfl⟩ : syracuseStep 3088523 = 4632785) B4632785
theorem B2441369 : Blo 1626512 2441369 := bstep (se 2 (by rfl) ⟨915513, by rfl⟩ : syracuseStep 2441369 = 1831027) B1831027
theorem B3662027 : Blo 1626512 3662027 := bstep (se 1 (by rfl) ⟨2746520, by rfl⟩ : syracuseStep 3662027 = 5493041) B5493041
theorem B2318539 : Blo 1626512 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B5865689 : Blo 1626512 5865689 := bstep (se 2 (by rfl) ⟨2199633, by rfl⟩ : syracuseStep 5865689 = 4399267) B4399267
theorem B3662081 : Blo 1626512 3662081 := bstep (se 2 (by rfl) ⟨1373280, by rfl⟩ : syracuseStep 3662081 = 2746561) B2746561
theorem B11731205 : Blo 1626512 11731205 := bstep (se 4 (by rfl) ⟨1099800, by rfl⟩ : syracuseStep 11731205 = 2199601) B2199601
theorem B2441483 : Blo 1626512 2441483 := bstep (se 1 (by rfl) ⟨1831112, by rfl⟩ : syracuseStep 2441483 = 3662225) B3662225
theorem B8241425 : Blo 1626512 8241425 := bstep (se 2 (by rfl) ⟨3090534, by rfl⟩ : syracuseStep 8241425 = 6181069) B6181069
theorem B2441495 : Blo 1626512 2441495 := bstep (se 1 (by rfl) ⟨1831121, by rfl⟩ : syracuseStep 2441495 = 3662243) B3662243
theorem B3088705 : Blo 1626512 3088705 := bstep (se 2 (by rfl) ⟨1158264, by rfl⟩ : syracuseStep 3088705 = 2316529) B2316529
theorem B2441561 : Blo 1626512 2441561 := bstep (se 2 (by rfl) ⟨915585, by rfl⟩ : syracuseStep 2441561 = 1831171) B1831171
theorem B2474393 : Blo 1626512 2474393 := bstep (se 2 (by rfl) ⟨927897, by rfl⟩ : syracuseStep 2474393 = 1855795) B1855795
theorem B8241587 : Blo 1626512 8241587 := bstep (se 1 (by rfl) ⟨6181190, by rfl⟩ : syracuseStep 8241587 = 12362381) B12362381
theorem B2744779 : Blo 1626512 2744779 := bstep (se 1 (by rfl) ⟨2058584, by rfl⟩ : syracuseStep 2744779 = 4117169) B4117169
theorem B2441675 : Blo 1626512 2441675 := bstep (se 1 (by rfl) ⟨1831256, by rfl⟩ : syracuseStep 2441675 = 3662513) B3662513
theorem B2441687 : Blo 1626512 2441687 := bstep (se 1 (by rfl) ⟨1831265, by rfl⟩ : syracuseStep 2441687 = 3662531) B3662531
theorem B3662297 : Blo 1626512 3662297 := bstep (se 2 (by rfl) ⟨1373361, by rfl⟩ : syracuseStep 3662297 = 2746723) B2746723
theorem B18547217 : Blo 1626512 18547217 := bstep (se 2 (by rfl) ⟨6955206, by rfl⟩ : syracuseStep 18547217 = 13910413) B13910413
theorem B4293143 : Blo 1626512 4293143 := bstep (se 1 (by rfl) ⟨3219857, by rfl⟩ : syracuseStep 4293143 = 6439715) B6439715
theorem B2441753 : Blo 1626512 2441753 := bstep (se 2 (by rfl) ⟨915657, by rfl⟩ : syracuseStep 2441753 = 1831315) B1831315
theorem B3662387 : Blo 1626512 3662387 := bstep (se 1 (by rfl) ⟨2746790, by rfl⟩ : syracuseStep 3662387 = 5493581) B5493581
theorem B3662423 : Blo 1626512 3662423 := bstep (se 1 (by rfl) ⟨2746817, by rfl⟩ : syracuseStep 3662423 = 5493635) B5493635
theorem B2744921 : Blo 1626512 2744921 := bstep (se 2 (by rfl) ⟨1029345, by rfl⟩ : syracuseStep 2744921 = 2058691) B2058691
theorem B9896579 : Blo 1626512 9896579 := bstep (se 1 (by rfl) ⟨7422434, by rfl⟩ : syracuseStep 9896579 = 14844869) B14844869
theorem B39608963 : Blo 1626512 39608963 := bstep (se 1 (by rfl) ⟨29706722, by rfl⟩ : syracuseStep 39608963 = 59413445) B59413445
theorem B2441867 : Blo 1626512 2441867 := bstep (se 1 (by rfl) ⟨1831400, by rfl⟩ : syracuseStep 2441867 = 3662801) B3662801
theorem B2441879 : Blo 1626512 2441879 := bstep (se 1 (by rfl) ⟨1831409, by rfl⟩ : syracuseStep 2441879 = 3662819) B3662819
theorem B4121239 : Blo 1626512 4121239 := bstep (se 1 (by rfl) ⟨3090929, by rfl⟩ : syracuseStep 4121239 = 6181859) B6181859
theorem B2745049 : Blo 1626512 2745049 := bstep (se 2 (by rfl) ⟨1029393, by rfl⟩ : syracuseStep 2745049 = 2058787) B2058787
theorem B2441945 : Blo 1626512 2441945 := bstep (se 2 (by rfl) ⟨915729, by rfl⟩ : syracuseStep 2441945 = 1831459) B1831459
theorem B3089153 : Blo 1626512 3089153 := bstep (se 2 (by rfl) ⟨1158432, by rfl⟩ : syracuseStep 3089153 = 2316865) B2316865
theorem B3711755 : Blo 1626512 3711755 := bstep (se 1 (by rfl) ⟨2783816, by rfl⟩ : syracuseStep 3711755 = 5567633) B5567633
theorem B3662603 : Blo 1626512 3662603 := bstep (se 1 (by rfl) ⟨2746952, by rfl⟩ : syracuseStep 3662603 = 5493905) B5493905
theorem B3908375 : Blo 1626512 3908375 := bstep (se 1 (by rfl) ⟨2931281, by rfl⟩ : syracuseStep 3908375 = 5862563) B5862563
theorem B4399895 : Blo 1626512 4399895 := bstep (se 1 (by rfl) ⟨3299921, by rfl⟩ : syracuseStep 4399895 = 6599843) B6599843
theorem B63382337 : Blo 1626512 63382337 := bstep (se 2 (by rfl) ⟨23768376, by rfl⟩ : syracuseStep 63382337 = 47536753) B47536753
theorem B3662657 : Blo 1626512 3662657 := bstep (se 2 (by rfl) ⟨1373496, by rfl⟩ : syracuseStep 3662657 = 2746993) B2746993
theorem B2442059 : Blo 1626512 2442059 := bstep (se 1 (by rfl) ⟨1831544, by rfl⟩ : syracuseStep 2442059 = 3663089) B3663089
theorem B6030155 : Blo 1626512 6030155 := bstep (se 1 (by rfl) ⟨4522616, by rfl⟩ : syracuseStep 6030155 = 9045233) B9045233
theorem B2442071 : Blo 1626512 2442071 := bstep (se 1 (by rfl) ⟨1831553, by rfl⟩ : syracuseStep 2442071 = 3663107) B3663107
theorem B25043813 : Blo 1626512 25043813 := bstep (se 4 (by rfl) ⟨2347857, by rfl⟩ : syracuseStep 25043813 = 4695715) B4695715
theorem B3523457 : Blo 1626512 3523457 := bstep (se 2 (by rfl) ⟨1321296, by rfl⟩ : syracuseStep 3523457 = 2642593) B2642593
theorem B6177667 : Blo 1626512 6177667 := bstep (se 1 (by rfl) ⟨4633250, by rfl⟩ : syracuseStep 6177667 = 9266501) B9266501
theorem B1737623 : Blo 1626512 1737623 := bstep (se 1 (by rfl) ⟨1303217, by rfl⟩ : syracuseStep 1737623 = 2606435) B2606435
theorem B2442137 : Blo 1626512 2442137 := bstep (se 2 (by rfl) ⟨915801, by rfl⟩ : syracuseStep 2442137 = 1831603) B1831603
theorem B102949829 : Blo 1626512 102949829 := bstep (se 4 (by rfl) ⟨9651546, by rfl⟩ : syracuseStep 102949829 = 19303093) B19303093
theorem B3130355 : Blo 1626512 3130355 := bstep (se 1 (by rfl) ⟨2347766, by rfl⟩ : syracuseStep 3130355 = 4695533) B4695533
theorem B2442251 : Blo 1626512 2442251 := bstep (se 1 (by rfl) ⟨1831688, by rfl⟩ : syracuseStep 2442251 = 3663377) B3663377
theorem B2442263 : Blo 1626512 2442263 := bstep (se 1 (by rfl) ⟨1831697, by rfl⟩ : syracuseStep 2442263 = 3663395) B3663395
theorem B3662873 : Blo 1626512 3662873 := bstep (se 2 (by rfl) ⟨1373577, by rfl⟩ : syracuseStep 3662873 = 2747155) B2747155
theorem B12354605 : Blo 1626512 12354605 := bstep (se 3 (by rfl) ⟨2316488, by rfl⟩ : syracuseStep 12354605 = 4632977) B4632977
theorem B4121675 : Blo 1626512 4121675 := bstep (se 1 (by rfl) ⟨3091256, by rfl⟩ : syracuseStep 4121675 = 6182513) B6182513
theorem B3089495 : Blo 1626512 3089495 := bstep (se 1 (by rfl) ⟨2317121, by rfl⟩ : syracuseStep 3089495 = 4634243) B4634243
theorem B2442329 : Blo 1626512 2442329 := bstep (se 2 (by rfl) ⟨915873, by rfl⟩ : syracuseStep 2442329 = 1831747) B1831747
theorem B5211229 : Blo 1626512 5211229 := bstep (se 3 (by rfl) ⟨977105, by rfl⟩ : syracuseStep 5211229 = 1954211) B1954211
theorem B3662963 : Blo 1626512 3662963 := bstep (se 1 (by rfl) ⟨2747222, by rfl⟩ : syracuseStep 3662963 = 5494445) B5494445
theorem B9274499 : Blo 1626512 9274499 := bstep (se 1 (by rfl) ⟨6955874, by rfl⟩ : syracuseStep 9274499 = 13911749) B13911749
theorem B3662999 : Blo 1626512 3662999 := bstep (se 1 (by rfl) ⟨2747249, by rfl⟩ : syracuseStep 3662999 = 5494499) B5494499
theorem B6177971 : Blo 1626512 6177971 := bstep (se 1 (by rfl) ⟨4633478, by rfl⟩ : syracuseStep 6177971 = 9266957) B9266957
theorem B2442443 : Blo 1626512 2442443 := bstep (se 1 (by rfl) ⟨1831832, by rfl⟩ : syracuseStep 2442443 = 3663665) B3663665
theorem B2442455 : Blo 1626512 2442455 := bstep (se 1 (by rfl) ⟨1831841, by rfl⟩ : syracuseStep 2442455 = 3663683) B3663683
theorem B14845189 : Blo 1626512 14845189 := bstep (se 4 (by rfl) ⟨1391736, by rfl⟩ : syracuseStep 14845189 = 2783473) B2783473
theorem B2745623 : Blo 1626512 2745623 := bstep (se 1 (by rfl) ⟨2059217, by rfl⟩ : syracuseStep 2745623 = 4118435) B4118435
theorem B2442521 : Blo 1626512 2442521 := bstep (se 2 (by rfl) ⟨915945, by rfl⟩ : syracuseStep 2442521 = 1831891) B1831891
theorem B3663179 : Blo 1626512 3663179 := bstep (se 1 (by rfl) ⟨2747384, by rfl⟩ : syracuseStep 3663179 = 5494769) B5494769
theorem B3573067 : Blo 1626512 3573067 := bstep (se 1 (by rfl) ⟨2679800, by rfl⟩ : syracuseStep 3573067 = 5359601) B5359601
theorem B13911371 : Blo 1626512 13911371 := bstep (se 1 (by rfl) ⟨10433528, by rfl⟩ : syracuseStep 13911371 = 20867057) B20867057
theorem B3663233 : Blo 1626512 3663233 := bstep (se 2 (by rfl) ⟨1373712, by rfl⟩ : syracuseStep 3663233 = 2747425) B2747425
theorem B2442635 : Blo 1626512 2442635 := bstep (se 1 (by rfl) ⟨1831976, by rfl⟩ : syracuseStep 2442635 = 3663953) B3663953
theorem B5490071 : Blo 1626512 5490071 := bstep (se 1 (by rfl) ⟨4117553, by rfl⟩ : syracuseStep 5490071 = 8235107) B8235107
theorem B2745751 : Blo 1626512 2745751 := bstep (se 1 (by rfl) ⟨2059313, by rfl⟩ : syracuseStep 2745751 = 4118627) B4118627
theorem B2442647 : Blo 1626512 2442647 := bstep (se 1 (by rfl) ⟨1831985, by rfl⟩ : syracuseStep 2442647 = 3663971) B3663971
theorem B4122049 : Blo 1626512 4122049 := bstep (se 2 (by rfl) ⟨1545768, by rfl⟩ : syracuseStep 4122049 = 3091537) B3091537
theorem B2442713 : Blo 1626512 2442713 := bstep (se 2 (by rfl) ⟨916017, by rfl⟩ : syracuseStep 2442713 = 1832035) B1832035
theorem B6596113 : Blo 1626512 6596113 := bstep (se 2 (by rfl) ⟨2473542, by rfl⟩ : syracuseStep 6596113 = 4947085) B4947085
theorem B3663449 : Blo 1626512 3663449 := bstep (se 2 (by rfl) ⟨1373793, by rfl⟩ : syracuseStep 3663449 = 2747587) B2747587
theorem B10430045 : Blo 1626512 10430045 := bstep (se 3 (by rfl) ⟨1955633, by rfl⟩ : syracuseStep 10430045 = 3911267) B3911267
theorem B2475659 : Blo 1626512 2475659 := bstep (se 1 (by rfl) ⟨1856744, by rfl⟩ : syracuseStep 2475659 = 3713489) B3713489
theorem B3663539 : Blo 1626512 3663539 := bstep (se 1 (by rfl) ⟨2747654, by rfl⟩ : syracuseStep 3663539 = 5495309) B5495309
theorem B3663575 : Blo 1626512 3663575 := bstep (se 1 (by rfl) ⟨2747681, by rfl⟩ : syracuseStep 3663575 = 5495363) B5495363
theorem B3090163 : Blo 1626512 3090163 := bstep (se 1 (by rfl) ⟨2317622, by rfl⟩ : syracuseStep 3090163 = 4635245) B4635245
theorem B6178625 : Blo 1626512 6178625 := bstep (se 2 (by rfl) ⟨2316984, by rfl⟩ : syracuseStep 6178625 = 4633969) B4633969
theorem B9398081 : Blo 1626512 9398081 := bstep (se 2 (by rfl) ⟨3524280, by rfl⟩ : syracuseStep 9398081 = 7048561) B7048561
theorem B33392483 : Blo 1626512 33392483 := bstep (se 1 (by rfl) ⟨25044362, by rfl⟩ : syracuseStep 33392483 = 50088725) B50088725
theorem B3663755 : Blo 1626512 3663755 := bstep (se 1 (by rfl) ⟨2747816, by rfl⟩ : syracuseStep 3663755 = 5495633) B5495633
theorem B5490611 : Blo 1626512 5490611 := bstep (se 1 (by rfl) ⟨4117958, by rfl⟩ : syracuseStep 5490611 = 8235917) B8235917
theorem B3663809 : Blo 1626512 3663809 := bstep (se 2 (by rfl) ⟨1373928, by rfl⟩ : syracuseStep 3663809 = 2747857) B2747857
theorem B11724749 : Blo 1626512 11724749 := bstep (se 3 (by rfl) ⟨2198390, by rfl⟩ : syracuseStep 11724749 = 4396781) B4396781
theorem B2746379 : Blo 1626512 2746379 := bstep (se 1 (by rfl) ⟨2059784, by rfl⟩ : syracuseStep 2746379 = 4119569) B4119569
theorem B7424131 : Blo 1626512 7424131 := bstep (se 1 (by rfl) ⟨5568098, by rfl⟩ : syracuseStep 7424131 = 11136197) B11136197
theorem B2746507 : Blo 1626512 2746507 := bstep (se 1 (by rfl) ⟨2059880, by rfl⟩ : syracuseStep 2746507 = 4119761) B4119761
theorem B3664025 : Blo 1626512 3664025 := bstep (se 2 (by rfl) ⟨1374009, by rfl⟩ : syracuseStep 3664025 = 2748019) B2748019
theorem B3090611 : Blo 1626512 3090611 := bstep (se 1 (by rfl) ⟨2317958, by rfl⟩ : syracuseStep 3090611 = 4635917) B4635917
theorem B5490881 : Blo 1626512 5490881 := bstep (se 2 (by rfl) ⟨2059080, by rfl⟩ : syracuseStep 5490881 = 4118161) B4118161
theorem B3090649 : Blo 1626512 3090649 := bstep (se 2 (by rfl) ⟨1158993, by rfl⟩ : syracuseStep 3090649 = 2317987) B2317987
theorem B3664115 : Blo 1626512 3664115 := bstep (se 1 (by rfl) ⟨2748086, by rfl⟩ : syracuseStep 3664115 = 5496173) B5496173
theorem B3664151 : Blo 1626512 3664151 := bstep (se 1 (by rfl) ⟨2748113, by rfl⟩ : syracuseStep 3664151 = 5496227) B5496227
theorem B2746649 : Blo 1626512 2746649 := bstep (se 2 (by rfl) ⟨1029993, by rfl⟩ : syracuseStep 2746649 = 2059987) B2059987
theorem B15640877 : Blo 1626512 15640877 := bstep (se 3 (by rfl) ⟨2932664, by rfl⟩ : syracuseStep 15640877 = 5865329) B5865329
theorem B8243531 : Blo 1626512 8243531 := bstep (se 1 (by rfl) ⟨6182648, by rfl⟩ : syracuseStep 8243531 = 12365297) B12365297
theorem B9390437 : Blo 1626512 9390437 := bstep (se 4 (by rfl) ⟨880353, by rfl⟩ : syracuseStep 9390437 = 1760707) B1760707
theorem B2058635 : Blo 1626512 2058635 := bstep (se 1 (by rfl) ⟨1543976, by rfl⟩ : syracuseStep 2058635 = 3087953) B3087953
theorem B2746777 : Blo 1626512 2746777 := bstep (se 2 (by rfl) ⟨1030041, by rfl⟩ : syracuseStep 2746777 = 2060083) B2060083
theorem B3091097 : Blo 1626512 3091097 := bstep (se 2 (by rfl) ⟨1159161, by rfl⟩ : syracuseStep 3091097 = 2318323) B2318323
theorem B5016257 : Blo 1626512 5016257 := bstep (se 2 (by rfl) ⟨1881096, by rfl⟩ : syracuseStep 5016257 = 3762193) B3762193
theorem B5491421 : Blo 1626512 5491421 := bstep (se 3 (by rfl) ⟨1029641, by rfl⟩ : syracuseStep 5491421 = 2059283) B2059283
theorem B2607895 : Blo 1626512 2607895 := bstep (se 1 (by rfl) ⟨1955921, by rfl⟩ : syracuseStep 2607895 = 3911843) B3911843
theorem B2607947 : Blo 1626512 2607947 := bstep (se 1 (by rfl) ⟨1955960, by rfl⟩ : syracuseStep 2607947 = 3911921) B3911921
theorem B2608075 : Blo 1626512 2608075 := bstep (se 1 (by rfl) ⟨1956056, by rfl⟩ : syracuseStep 2608075 = 3912113) B3912113
theorem B2747351 : Blo 1626512 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B1829911 : Blo 1626512 1829911 := bstep (se 1 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 1829911 = 2744867) B2744867
theorem B3714071 : Blo 1626512 3714071 := bstep (se 1 (by rfl) ⟨2785553, by rfl⟩ : syracuseStep 3714071 = 5571107) B5571107
theorem B6179885 : Blo 1626512 6179885 := bstep (se 3 (by rfl) ⟨1158728, by rfl⟩ : syracuseStep 6179885 = 2317457) B2317457
theorem B2059339 : Blo 1626512 2059339 := bstep (se 1 (by rfl) ⟨1544504, by rfl⟩ : syracuseStep 2059339 = 3089009) B3089009
theorem B6179915 : Blo 1626512 6179915 := bstep (se 1 (by rfl) ⟨4634936, by rfl⟩ : syracuseStep 6179915 = 9269873) B9269873
theorem B2747479 : Blo 1626512 2747479 := bstep (se 1 (by rfl) ⟨2060609, by rfl⟩ : syracuseStep 2747479 = 4121219) B4121219
theorem B3910835 : Blo 1626512 3910835 := bstep (se 1 (by rfl) ⟨2933126, by rfl⟩ : syracuseStep 3910835 = 5866253) B5866253
theorem B1830091 : Blo 1626512 1830091 := bstep (se 1 (by rfl) ⟨1372568, by rfl⟩ : syracuseStep 1830091 = 2745137) B2745137
theorem B7818457 : Blo 1626512 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B1830199 : Blo 1626512 1830199 := bstep (se 1 (by rfl) ⟨1372649, by rfl⟩ : syracuseStep 1830199 = 2745299) B2745299
theorem B2059607 : Blo 1626512 2059607 := bstep (se 1 (by rfl) ⟨1544705, by rfl⟩ : syracuseStep 2059607 = 3089411) B3089411
theorem B3763673 : Blo 1626512 3763673 := bstep (se 2 (by rfl) ⟨1411377, by rfl⟩ : syracuseStep 3763673 = 2822755) B2822755
theorem B1830379 : Blo 1626512 1830379 := bstep (se 1 (by rfl) ⟨1372784, by rfl⟩ : syracuseStep 1830379 = 2745569) B2745569
theorem B6950423 : Blo 1626512 6950423 := bstep (se 1 (by rfl) ⟨5212817, by rfl⟩ : syracuseStep 6950423 = 10425635) B10425635
theorem B10571309 : Blo 1626512 10571309 := bstep (se 3 (by rfl) ⟨1982120, by rfl⟩ : syracuseStep 10571309 = 3964241) B3964241
theorem B13897291 : Blo 1626512 13897291 := bstep (se 1 (by rfl) ⟨10422968, by rfl⟩ : syracuseStep 13897291 = 20845937) B20845937
theorem B1830487 : Blo 1626512 1830487 := bstep (se 1 (by rfl) ⟨1372865, by rfl⟩ : syracuseStep 1830487 = 2745731) B2745731
theorem B4632157 : Blo 1626512 4632157 := bstep (se 3 (by rfl) ⟨868529, by rfl⟩ : syracuseStep 4632157 = 1737059) B1737059
theorem B3477143 : Blo 1626512 3477143 := bstep (se 1 (by rfl) ⟨2607857, by rfl⟩ : syracuseStep 3477143 = 5215715) B5215715
theorem B2748107 : Blo 1626512 2748107 := bstep (se 1 (by rfl) ⟨2061080, by rfl⟩ : syracuseStep 2748107 = 4122161) B4122161
theorem B6180569 : Blo 1626512 6180569 := bstep (se 2 (by rfl) ⟨2317713, by rfl⟩ : syracuseStep 6180569 = 4635427) B4635427
theorem B1830667 : Blo 1626512 1830667 := bstep (se 1 (by rfl) ⟨1373000, by rfl⟩ : syracuseStep 1830667 = 2746001) B2746001
theorem B4632385 : Blo 1626512 4632385 := bstep (se 2 (by rfl) ⟨1737144, by rfl⟩ : syracuseStep 4632385 = 3474289) B3474289
theorem B6950731 : Blo 1626512 6950731 := bstep (se 1 (by rfl) ⟨5213048, by rfl⟩ : syracuseStep 6950731 = 10426097) B10426097
theorem B5492555 : Blo 1626512 5492555 := bstep (se 1 (by rfl) ⟨4119416, by rfl⟩ : syracuseStep 5492555 = 8238833) B8238833
theorem B3477323 : Blo 1626512 3477323 := bstep (se 1 (by rfl) ⟨2607992, by rfl⟩ : syracuseStep 3477323 = 5215985) B5215985
theorem B13897565 : Blo 1626512 13897565 := bstep (se 3 (by rfl) ⟨2605793, by rfl⟩ : syracuseStep 13897565 = 5211587) B5211587
theorem B1830775 : Blo 1626512 1830775 := bstep (se 1 (by rfl) ⟨1373081, by rfl⟩ : syracuseStep 1830775 = 2746163) B2746163
theorem B6180887 : Blo 1626512 6180887 := bstep (se 1 (by rfl) ⟨4635665, by rfl⟩ : syracuseStep 6180887 = 9271331) B9271331
theorem B2060311 : Blo 1626512 2060311 := bstep (se 1 (by rfl) ⟨1545233, by rfl⟩ : syracuseStep 2060311 = 3090467) B3090467
theorem B1830955 : Blo 1626512 1830955 := bstep (se 1 (by rfl) ⟨1373216, by rfl⟩ : syracuseStep 1830955 = 2746433) B2746433
theorem B5492825 : Blo 1626512 5492825 := bstep (se 2 (by rfl) ⟨2059809, by rfl⟩ : syracuseStep 5492825 = 4119619) B4119619
theorem B6951005 : Blo 1626512 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B4632727 : Blo 1626512 4632727 := bstep (se 1 (by rfl) ⟨3474545, by rfl⟩ : syracuseStep 4632727 = 6949091) B6949091
theorem B1831063 : Blo 1626512 1831063 := bstep (se 1 (by rfl) ⟨1373297, by rfl⟩ : syracuseStep 1831063 = 2746595) B2746595
theorem B1855723 : Blo 1626512 1855723 := bstep (se 1 (by rfl) ⟨1391792, by rfl⟩ : syracuseStep 1855723 = 2783585) B2783585
theorem B10170689 : Blo 1626512 10170689 := bstep (se 2 (by rfl) ⟨3814008, by rfl⟩ : syracuseStep 10170689 = 7628017) B7628017
theorem B1831243 : Blo 1626512 1831243 := bstep (se 1 (by rfl) ⟨1373432, by rfl⟩ : syracuseStep 1831243 = 2746865) B2746865
theorem B1626519 : Blo 1626512 1626519 := bstep (se 1 (by rfl) ⟨1219889, by rfl⟩ : syracuseStep 1626519 = 2439779) B2439779
theorem B1626539 : Blo 1626512 1626539 := bstep (se 1 (by rfl) ⟨1219904, by rfl⟩ : syracuseStep 1626539 = 2439809) B2439809
theorem B6263219 : Blo 1626512 6263219 := bstep (se 1 (by rfl) ⟨4697414, by rfl⟩ : syracuseStep 6263219 = 9394829) B9394829
theorem B1626551 : Blo 1626512 1626551 := bstep (se 1 (by rfl) ⟨1219913, by rfl⟩ : syracuseStep 1626551 = 2439827) B2439827
theorem B1831351 : Blo 1626512 1831351 := bstep (se 1 (by rfl) ⟨1373513, by rfl⟩ : syracuseStep 1831351 = 2747027) B2747027
theorem B1626571 : Blo 1626512 1626571 := bstep (se 1 (by rfl) ⟨1219928, by rfl⟩ : syracuseStep 1626571 = 2439857) B2439857
theorem B1626583 : Blo 1626512 1626583 := bstep (se 1 (by rfl) ⟨1219937, by rfl⟩ : syracuseStep 1626583 = 2439875) B2439875
theorem B1626603 : Blo 1626512 1626603 := bstep (se 1 (by rfl) ⟨1219952, by rfl⟩ : syracuseStep 1626603 = 2439905) B2439905
theorem B1626615 : Blo 1626512 1626615 := bstep (se 1 (by rfl) ⟨1219961, by rfl⟩ : syracuseStep 1626615 = 2439923) B2439923
theorem B1626635 : Blo 1626512 1626635 := bstep (se 1 (by rfl) ⟨1219976, by rfl⟩ : syracuseStep 1626635 = 2439953) B2439953
theorem B1626647 : Blo 1626512 1626647 := bstep (se 1 (by rfl) ⟨1219985, by rfl⟩ : syracuseStep 1626647 = 2439971) B2439971
theorem B1626667 : Blo 1626512 1626667 := bstep (se 1 (by rfl) ⟨1220000, by rfl⟩ : syracuseStep 1626667 = 2440001) B2440001
theorem B10433069 : Blo 1626512 10433069 := bstep (se 3 (by rfl) ⟨1956200, by rfl⟩ : syracuseStep 10433069 = 3912401) B3912401
theorem B1626679 : Blo 1626512 1626679 := bstep (se 1 (by rfl) ⟨1220009, by rfl⟩ : syracuseStep 1626679 = 2440019) B2440019
theorem B7819841 : Blo 1626512 7819841 := bstep (se 2 (by rfl) ⟨2932440, by rfl⟩ : syracuseStep 7819841 = 5864881) B5864881
theorem B1626699 : Blo 1626512 1626699 := bstep (se 1 (by rfl) ⟨1220024, by rfl⟩ : syracuseStep 1626699 = 2440049) B2440049
theorem B4174411 : Blo 1626512 4174411 := bstep (se 1 (by rfl) ⟨3130808, by rfl⟩ : syracuseStep 4174411 = 6261617) B6261617
theorem B1626711 : Blo 1626512 1626711 := bstep (se 1 (by rfl) ⟨1220033, by rfl⟩ : syracuseStep 1626711 = 2440067) B2440067
theorem B1626731 : Blo 1626512 1626731 := bstep (se 1 (by rfl) ⟨1220048, by rfl⟩ : syracuseStep 1626731 = 2440097) B2440097
theorem B1831531 : Blo 1626512 1831531 := bstep (se 1 (by rfl) ⟨1373648, by rfl⟩ : syracuseStep 1831531 = 2747297) B2747297
theorem B1626743 : Blo 1626512 1626743 := bstep (se 1 (by rfl) ⟨1220057, by rfl⟩ : syracuseStep 1626743 = 2440115) B2440115
theorem B8237699 : Blo 1626512 8237699 := bstep (se 1 (by rfl) ⟨6178274, by rfl⟩ : syracuseStep 8237699 = 12356549) B12356549
theorem B1626763 : Blo 1626512 1626763 := bstep (se 1 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 1626763 = 2440145) B2440145
theorem B1626775 : Blo 1626512 1626775 := bstep (se 1 (by rfl) ⟨1220081, by rfl⟩ : syracuseStep 1626775 = 2440163) B2440163
theorem B1626795 : Blo 1626512 1626795 := bstep (se 1 (by rfl) ⟨1220096, by rfl⟩ : syracuseStep 1626795 = 2440193) B2440193
theorem B6181555 : Blo 1626512 6181555 := bstep (se 1 (by rfl) ⟨4636166, by rfl⟩ : syracuseStep 6181555 = 9272333) B9272333
theorem B1626807 : Blo 1626512 1626807 := bstep (se 1 (by rfl) ⟨1220105, by rfl⟩ : syracuseStep 1626807 = 2440211) B2440211
theorem B1626827 : Blo 1626512 1626827 := bstep (se 1 (by rfl) ⟨1220120, by rfl⟩ : syracuseStep 1626827 = 2440241) B2440241
theorem B1626839 : Blo 1626512 1626839 := bstep (se 1 (by rfl) ⟨1220129, by rfl⟩ : syracuseStep 1626839 = 2440259) B2440259
theorem B1831639 : Blo 1626512 1831639 := bstep (se 1 (by rfl) ⟨1373729, by rfl⟩ : syracuseStep 1831639 = 2747459) B2747459
theorem B1626859 : Blo 1626512 1626859 := bstep (se 1 (by rfl) ⟨1220144, by rfl⟩ : syracuseStep 1626859 = 2440289) B2440289
theorem B1626871 : Blo 1626512 1626871 := bstep (se 1 (by rfl) ⟨1220153, by rfl⟩ : syracuseStep 1626871 = 2440307) B2440307
theorem B1626891 : Blo 1626512 1626891 := bstep (se 1 (by rfl) ⟨1220168, by rfl⟩ : syracuseStep 1626891 = 2440337) B2440337
theorem B1626903 : Blo 1626512 1626903 := bstep (se 1 (by rfl) ⟨1220177, by rfl⟩ : syracuseStep 1626903 = 2440355) B2440355
theorem B5493527 : Blo 1626512 5493527 := bstep (se 1 (by rfl) ⟨4120145, by rfl⟩ : syracuseStep 5493527 = 8240291) B8240291
theorem B1626923 : Blo 1626512 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B1626935 : Blo 1626512 1626935 := bstep (se 1 (by rfl) ⟨1220201, by rfl⟩ : syracuseStep 1626935 = 2440403) B2440403
theorem B1626955 : Blo 1626512 1626955 := bstep (se 1 (by rfl) ⟨1220216, by rfl⟩ : syracuseStep 1626955 = 2440433) B2440433
theorem B1626967 : Blo 1626512 1626967 := bstep (se 1 (by rfl) ⟨1220225, by rfl⟩ : syracuseStep 1626967 = 2440451) B2440451
theorem B4633433 : Blo 1626512 4633433 := bstep (se 2 (by rfl) ⟨1737537, by rfl⟩ : syracuseStep 4633433 = 3475075) B3475075
theorem B12358493 : Blo 1626512 12358493 := bstep (se 3 (by rfl) ⟨2317217, by rfl⟩ : syracuseStep 12358493 = 4634435) B4634435
theorem B1626987 : Blo 1626512 1626987 := bstep (se 1 (by rfl) ⟨1220240, by rfl⟩ : syracuseStep 1626987 = 2440481) B2440481
theorem B1626999 : Blo 1626512 1626999 := bstep (se 1 (by rfl) ⟨1220249, by rfl⟩ : syracuseStep 1626999 = 2440499) B2440499
theorem B13898627 : Blo 1626512 13898627 := bstep (se 1 (by rfl) ⟨10423970, by rfl⟩ : syracuseStep 13898627 = 20847941) B20847941
theorem B1627019 : Blo 1626512 1627019 := bstep (se 1 (by rfl) ⟨1220264, by rfl⟩ : syracuseStep 1627019 = 2440529) B2440529
theorem B1831819 : Blo 1626512 1831819 := bstep (se 1 (by rfl) ⟨1373864, by rfl⟩ : syracuseStep 1831819 = 2747729) B2747729
theorem B1627031 : Blo 1626512 1627031 := bstep (se 1 (by rfl) ⟨1220273, by rfl⟩ : syracuseStep 1627031 = 2440547) B2440547
theorem B1627051 : Blo 1626512 1627051 := bstep (se 1 (by rfl) ⟨1220288, by rfl⟩ : syracuseStep 1627051 = 2440577) B2440577
theorem B1627063 : Blo 1626512 1627063 := bstep (se 1 (by rfl) ⟨1220297, by rfl⟩ : syracuseStep 1627063 = 2440595) B2440595
theorem B1627083 : Blo 1626512 1627083 := bstep (se 1 (by rfl) ⟨1220312, by rfl⟩ : syracuseStep 1627083 = 2440625) B2440625
theorem B1627095 : Blo 1626512 1627095 := bstep (se 1 (by rfl) ⟨1220321, by rfl⟩ : syracuseStep 1627095 = 2440643) B2440643
theorem B2200537 : Blo 1626512 2200537 := bstep (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) B1650403
theorem B1627115 : Blo 1626512 1627115 := bstep (se 1 (by rfl) ⟨1220336, by rfl⟩ : syracuseStep 1627115 = 2440673) B2440673
theorem B1627127 : Blo 1626512 1627127 := bstep (se 1 (by rfl) ⟨1220345, by rfl⟩ : syracuseStep 1627127 = 2440691) B2440691
theorem B1831927 : Blo 1626512 1831927 := bstep (se 1 (by rfl) ⟨1373945, by rfl⟩ : syracuseStep 1831927 = 2747891) B2747891
theorem B1627147 : Blo 1626512 1627147 := bstep (se 1 (by rfl) ⟨1220360, by rfl⟩ : syracuseStep 1627147 = 2440721) B2440721
theorem B1627159 : Blo 1626512 1627159 := bstep (se 1 (by rfl) ⟨1220369, by rfl⟩ : syracuseStep 1627159 = 2440739) B2440739
theorem B1627179 : Blo 1626512 1627179 := bstep (se 1 (by rfl) ⟨1220384, by rfl⟩ : syracuseStep 1627179 = 2440769) B2440769
theorem B1627191 : Blo 1626512 1627191 := bstep (se 1 (by rfl) ⟨1220393, by rfl⟩ : syracuseStep 1627191 = 2440787) B2440787
theorem B15635531 : Blo 1626512 15635531 := bstep (se 1 (by rfl) ⟨11726648, by rfl⟩ : syracuseStep 15635531 = 23453297) B23453297
theorem B1627211 : Blo 1626512 1627211 := bstep (se 1 (by rfl) ⟨1220408, by rfl⟩ : syracuseStep 1627211 = 2440817) B2440817
theorem B1627223 : Blo 1626512 1627223 := bstep (se 1 (by rfl) ⟨1220417, by rfl⟩ : syracuseStep 1627223 = 2440835) B2440835
theorem B1954903 : Blo 1626512 1954903 := bstep (se 1 (by rfl) ⟨1466177, by rfl⟩ : syracuseStep 1954903 = 2932355) B2932355
theorem B1627243 : Blo 1626512 1627243 := bstep (se 1 (by rfl) ⟨1220432, by rfl⟩ : syracuseStep 1627243 = 2440865) B2440865
theorem B1627255 : Blo 1626512 1627255 := bstep (se 1 (by rfl) ⟨1220441, by rfl⟩ : syracuseStep 1627255 = 2440883) B2440883
theorem B1627275 : Blo 1626512 1627275 := bstep (se 1 (by rfl) ⟨1220456, by rfl⟩ : syracuseStep 1627275 = 2440913) B2440913
theorem B4117655 : Blo 1626512 4117655 := bstep (se 1 (by rfl) ⟨3088241, by rfl⟩ : syracuseStep 4117655 = 6176483) B6176483
theorem B1627287 : Blo 1626512 1627287 := bstep (se 1 (by rfl) ⟨1220465, by rfl⟩ : syracuseStep 1627287 = 2440931) B2440931
theorem B1627307 : Blo 1626512 1627307 := bstep (se 1 (by rfl) ⟨1220480, by rfl⟩ : syracuseStep 1627307 = 2440961) B2440961
theorem B1627319 : Blo 1626512 1627319 := bstep (se 1 (by rfl) ⟨1220489, by rfl⟩ : syracuseStep 1627319 = 2440979) B2440979
theorem B1627339 : Blo 1626512 1627339 := bstep (se 1 (by rfl) ⟨1220504, by rfl⟩ : syracuseStep 1627339 = 2441009) B2441009
theorem B1627351 : Blo 1626512 1627351 := bstep (se 1 (by rfl) ⟨1220513, by rfl⟩ : syracuseStep 1627351 = 2441027) B2441027
theorem B1627371 : Blo 1626512 1627371 := bstep (se 1 (by rfl) ⟨1220528, by rfl⟩ : syracuseStep 1627371 = 2441057) B2441057
theorem B1627383 : Blo 1626512 1627383 := bstep (se 1 (by rfl) ⟨1220537, by rfl⟩ : syracuseStep 1627383 = 2441075) B2441075
theorem B1627403 : Blo 1626512 1627403 := bstep (se 1 (by rfl) ⟨1220552, by rfl⟩ : syracuseStep 1627403 = 2441105) B2441105
theorem B7525649 : Blo 1626512 7525649 := bstep (se 2 (by rfl) ⟨2822118, by rfl⟩ : syracuseStep 7525649 = 5644237) B5644237
theorem B1627415 : Blo 1626512 1627415 := bstep (se 1 (by rfl) ⟨1220561, by rfl⟩ : syracuseStep 1627415 = 2441123) B2441123
theorem B1627435 : Blo 1626512 1627435 := bstep (se 1 (by rfl) ⟨1220576, by rfl⟩ : syracuseStep 1627435 = 2441153) B2441153
theorem B5494067 : Blo 1626512 5494067 := bstep (se 1 (by rfl) ⟨4120550, by rfl⟩ : syracuseStep 5494067 = 8241101) B8241101
theorem B1627447 : Blo 1626512 1627447 := bstep (se 1 (by rfl) ⟨1220585, by rfl⟩ : syracuseStep 1627447 = 2441171) B2441171
theorem B1627467 : Blo 1626512 1627467 := bstep (se 1 (by rfl) ⟨1220600, by rfl⟩ : syracuseStep 1627467 = 2441201) B2441201
theorem B1627479 : Blo 1626512 1627479 := bstep (se 1 (by rfl) ⟨1220609, by rfl⟩ : syracuseStep 1627479 = 2441219) B2441219
theorem B1627499 : Blo 1626512 1627499 := bstep (se 1 (by rfl) ⟨1220624, by rfl⟩ : syracuseStep 1627499 = 2441249) B2441249
theorem B1627511 : Blo 1626512 1627511 := bstep (se 1 (by rfl) ⟨1220633, by rfl⟩ : syracuseStep 1627511 = 2441267) B2441267
theorem B1627531 : Blo 1626512 1627531 := bstep (se 1 (by rfl) ⟨1220648, by rfl⟩ : syracuseStep 1627531 = 2441297) B2441297
theorem B6952337 : Blo 1626512 6952337 := bstep (se 2 (by rfl) ⟨2607126, by rfl⟩ : syracuseStep 6952337 = 5214253) B5214253
theorem B1627543 : Blo 1626512 1627543 := bstep (se 1 (by rfl) ⟨1220657, by rfl⟩ : syracuseStep 1627543 = 2441315) B2441315
theorem B1627563 : Blo 1626512 1627563 := bstep (se 1 (by rfl) ⟨1220672, by rfl⟩ : syracuseStep 1627563 = 2441345) B2441345
theorem B1627575 : Blo 1626512 1627575 := bstep (se 1 (by rfl) ⟨1220681, by rfl⟩ : syracuseStep 1627575 = 2441363) B2441363
theorem B1627595 : Blo 1626512 1627595 := bstep (se 1 (by rfl) ⟨1220696, by rfl⟩ : syracuseStep 1627595 = 2441393) B2441393
theorem B1627607 : Blo 1626512 1627607 := bstep (se 1 (by rfl) ⟨1220705, by rfl⟩ : syracuseStep 1627607 = 2441411) B2441411
theorem B1627627 : Blo 1626512 1627627 := bstep (se 1 (by rfl) ⟨1220720, by rfl⟩ : syracuseStep 1627627 = 2441441) B2441441
theorem B1627639 : Blo 1626512 1627639 := bstep (se 1 (by rfl) ⟨1220729, by rfl⟩ : syracuseStep 1627639 = 2441459) B2441459
theorem B1627659 : Blo 1626512 1627659 := bstep (se 1 (by rfl) ⟨1220744, by rfl⟩ : syracuseStep 1627659 = 2441489) B2441489
theorem B26400269 : Blo 1626512 26400269 := bstep (se 3 (by rfl) ⟨4950050, by rfl⟩ : syracuseStep 26400269 = 9900101) B9900101
theorem B1627671 : Blo 1626512 1627671 := bstep (se 1 (by rfl) ⟨1220753, by rfl⟩ : syracuseStep 1627671 = 2441507) B2441507
theorem B1627691 : Blo 1626512 1627691 := bstep (se 1 (by rfl) ⟨1220768, by rfl⟩ : syracuseStep 1627691 = 2441537) B2441537
theorem B1627703 : Blo 1626512 1627703 := bstep (se 1 (by rfl) ⟨1220777, by rfl⟩ : syracuseStep 1627703 = 2441555) B2441555
theorem B5494337 : Blo 1626512 5494337 := bstep (se 2 (by rfl) ⟨2060376, by rfl⟩ : syracuseStep 5494337 = 4120753) B4120753
theorem B1627723 : Blo 1626512 1627723 := bstep (se 1 (by rfl) ⟨1220792, by rfl⟩ : syracuseStep 1627723 = 2441585) B2441585
theorem B1627735 : Blo 1626512 1627735 := bstep (se 1 (by rfl) ⟨1220801, by rfl⟩ : syracuseStep 1627735 = 2441603) B2441603
theorem B1627755 : Blo 1626512 1627755 := bstep (se 1 (by rfl) ⟨1220816, by rfl⟩ : syracuseStep 1627755 = 2441633) B2441633
theorem B1627767 : Blo 1626512 1627767 := bstep (se 1 (by rfl) ⟨1220825, by rfl⟩ : syracuseStep 1627767 = 2441651) B2441651
theorem B1627787 : Blo 1626512 1627787 := bstep (se 1 (by rfl) ⟨1220840, by rfl⟩ : syracuseStep 1627787 = 2441681) B2441681
theorem B1627799 : Blo 1626512 1627799 := bstep (se 1 (by rfl) ⟨1220849, by rfl⟩ : syracuseStep 1627799 = 2441699) B2441699
theorem B1627819 : Blo 1626512 1627819 := bstep (se 1 (by rfl) ⟨1220864, by rfl⟩ : syracuseStep 1627819 = 2441729) B2441729
theorem B1627831 : Blo 1626512 1627831 := bstep (se 1 (by rfl) ⟨1220873, by rfl⟩ : syracuseStep 1627831 = 2441747) B2441747
theorem B84580037 : Blo 1626512 84580037 := bstep (se 4 (by rfl) ⟨7929378, by rfl⟩ : syracuseStep 84580037 = 15858757) B15858757
theorem B1627851 : Blo 1626512 1627851 := bstep (se 1 (by rfl) ⟨1220888, by rfl⟩ : syracuseStep 1627851 = 2441777) B2441777
theorem B1627863 : Blo 1626512 1627863 := bstep (se 1 (by rfl) ⟨1220897, by rfl⟩ : syracuseStep 1627863 = 2441795) B2441795
theorem B1627883 : Blo 1626512 1627883 := bstep (se 1 (by rfl) ⟨1220912, by rfl⟩ : syracuseStep 1627883 = 2441825) B2441825
theorem B1627895 : Blo 1626512 1627895 := bstep (se 1 (by rfl) ⟨1220921, by rfl⟩ : syracuseStep 1627895 = 2441843) B2441843
theorem B1627915 : Blo 1626512 1627915 := bstep (se 1 (by rfl) ⟨1220936, by rfl⟩ : syracuseStep 1627915 = 2441873) B2441873
theorem B9271057 : Blo 1626512 9271057 := bstep (se 2 (by rfl) ⟨3476646, by rfl⟩ : syracuseStep 9271057 = 6953293) B6953293
theorem B1627927 : Blo 1626512 1627927 := bstep (se 1 (by rfl) ⟨1220945, by rfl⟩ : syracuseStep 1627927 = 2441891) B2441891
theorem B1627947 : Blo 1626512 1627947 := bstep (se 1 (by rfl) ⟨1220960, by rfl⟩ : syracuseStep 1627947 = 2441921) B2441921
theorem B4118323 : Blo 1626512 4118323 := bstep (se 1 (by rfl) ⟨3088742, by rfl⟩ : syracuseStep 4118323 = 6177485) B6177485
theorem B1627959 : Blo 1626512 1627959 := bstep (se 1 (by rfl) ⟨1220969, by rfl⟩ : syracuseStep 1627959 = 2441939) B2441939
theorem B10565441 : Blo 1626512 10565441 := bstep (se 2 (by rfl) ⟨3962040, by rfl⟩ : syracuseStep 10565441 = 7924081) B7924081
theorem B1627979 : Blo 1626512 1627979 := bstep (se 1 (by rfl) ⟨1220984, by rfl⟩ : syracuseStep 1627979 = 2441969) B2441969
theorem B1627991 : Blo 1626512 1627991 := bstep (se 1 (by rfl) ⟨1220993, by rfl⟩ : syracuseStep 1627991 = 2441987) B2441987
theorem B1628011 : Blo 1626512 1628011 := bstep (se 1 (by rfl) ⟨1221008, by rfl⟩ : syracuseStep 1628011 = 2442017) B2442017
theorem B1628023 : Blo 1626512 1628023 := bstep (se 1 (by rfl) ⟨1221017, by rfl⟩ : syracuseStep 1628023 = 2442035) B2442035
theorem B1628043 : Blo 1626512 1628043 := bstep (se 1 (by rfl) ⟨1221032, by rfl⟩ : syracuseStep 1628043 = 2442065) B2442065
theorem B6182801 : Blo 1626512 6182801 := bstep (se 2 (by rfl) ⟨2318550, by rfl⟩ : syracuseStep 6182801 = 4637101) B4637101
theorem B1628055 : Blo 1626512 1628055 := bstep (se 1 (by rfl) ⟨1221041, by rfl⟩ : syracuseStep 1628055 = 2442083) B2442083
theorem B1628075 : Blo 1626512 1628075 := bstep (se 1 (by rfl) ⟨1221056, by rfl⟩ : syracuseStep 1628075 = 2442113) B2442113
theorem B1628087 : Blo 1626512 1628087 := bstep (se 1 (by rfl) ⟨1221065, by rfl⟩ : syracuseStep 1628087 = 2442131) B2442131
theorem B4118465 : Blo 1626512 4118465 := bstep (se 2 (by rfl) ⟨1544424, by rfl⟩ : syracuseStep 4118465 = 3088849) B3088849
theorem B3659723 : Blo 1626512 3659723 := bstep (se 1 (by rfl) ⟨2744792, by rfl⟩ : syracuseStep 3659723 = 5489585) B5489585
theorem B1628107 : Blo 1626512 1628107 := bstep (se 1 (by rfl) ⟨1221080, by rfl⟩ : syracuseStep 1628107 = 2442161) B2442161
theorem B1628119 : Blo 1626512 1628119 := bstep (se 1 (by rfl) ⟨1221089, by rfl⟩ : syracuseStep 1628119 = 2442179) B2442179
theorem B1628139 : Blo 1626512 1628139 := bstep (se 1 (by rfl) ⟨1221104, by rfl⟩ : syracuseStep 1628139 = 2442209) B2442209
theorem B1628151 : Blo 1626512 1628151 := bstep (se 1 (by rfl) ⟨1221113, by rfl⟩ : syracuseStep 1628151 = 2442227) B2442227
theorem B3659777 : Blo 1626512 3659777 := bstep (se 2 (by rfl) ⟨1372416, by rfl⟩ : syracuseStep 3659777 = 2744833) B2744833
theorem B1628171 : Blo 1626512 1628171 := bstep (se 1 (by rfl) ⟨1221128, by rfl⟩ : syracuseStep 1628171 = 2442257) B2442257
theorem B1628183 : Blo 1626512 1628183 := bstep (se 1 (by rfl) ⟨1221137, by rfl⟩ : syracuseStep 1628183 = 2442275) B2442275
theorem B1628203 : Blo 1626512 1628203 := bstep (se 1 (by rfl) ⟨1221152, by rfl⟩ : syracuseStep 1628203 = 2442305) B2442305
theorem B1628215 : Blo 1626512 1628215 := bstep (se 1 (by rfl) ⟨1221161, by rfl⟩ : syracuseStep 1628215 = 2442323) B2442323
theorem B5863499 : Blo 1626512 5863499 := bstep (se 1 (by rfl) ⟨4397624, by rfl⟩ : syracuseStep 5863499 = 8795249) B8795249
theorem B1628235 : Blo 1626512 1628235 := bstep (se 1 (by rfl) ⟨1221176, by rfl⟩ : syracuseStep 1628235 = 2442353) B2442353
theorem B1628247 : Blo 1626512 1628247 := bstep (se 1 (by rfl) ⟨1221185, by rfl⟩ : syracuseStep 1628247 = 2442371) B2442371
theorem B5494877 : Blo 1626512 5494877 := bstep (se 3 (by rfl) ⟨1030289, by rfl⟩ : syracuseStep 5494877 = 2060579) B2060579
theorem B1628267 : Blo 1626512 1628267 := bstep (se 1 (by rfl) ⟨1221200, by rfl⟩ : syracuseStep 1628267 = 2442401) B2442401
theorem B1628279 : Blo 1626512 1628279 := bstep (se 1 (by rfl) ⟨1221209, by rfl⟩ : syracuseStep 1628279 = 2442419) B2442419
theorem B1628299 : Blo 1626512 1628299 := bstep (se 1 (by rfl) ⟨1221224, by rfl⟩ : syracuseStep 1628299 = 2442449) B2442449
theorem B1628311 : Blo 1626512 1628311 := bstep (se 1 (by rfl) ⟨1221233, by rfl⟩ : syracuseStep 1628311 = 2442467) B2442467
theorem B1628331 : Blo 1626512 1628331 := bstep (se 1 (by rfl) ⟨1221248, by rfl⟩ : syracuseStep 1628331 = 2442497) B2442497
theorem B1628343 : Blo 1626512 1628343 := bstep (se 1 (by rfl) ⟨1221257, by rfl⟩ : syracuseStep 1628343 = 2442515) B2442515
theorem B15636685 : Blo 1626512 15636685 := bstep (se 3 (by rfl) ⟨2931878, by rfl⟩ : syracuseStep 15636685 = 5863757) B5863757
theorem B1628363 : Blo 1626512 1628363 := bstep (se 1 (by rfl) ⟨1221272, by rfl⟩ : syracuseStep 1628363 = 2442545) B2442545
theorem B1628375 : Blo 1626512 1628375 := bstep (se 1 (by rfl) ⟨1221281, by rfl⟩ : syracuseStep 1628375 = 2442563) B2442563
theorem B3659993 : Blo 1626512 3659993 := bstep (se 2 (by rfl) ⟨1372497, by rfl⟩ : syracuseStep 3659993 = 2744995) B2744995
theorem B1628395 : Blo 1626512 1628395 := bstep (se 1 (by rfl) ⟨1221296, by rfl⟩ : syracuseStep 1628395 = 2442593) B2442593
theorem B1628407 : Blo 1626512 1628407 := bstep (se 1 (by rfl) ⟨1221305, by rfl⟩ : syracuseStep 1628407 = 2442611) B2442611
theorem B1628427 : Blo 1626512 1628427 := bstep (se 1 (by rfl) ⟨1221320, by rfl⟩ : syracuseStep 1628427 = 2442641) B2442641
theorem B6600977 : Blo 1626512 6600977 := bstep (se 2 (by rfl) ⟨2475366, by rfl⟩ : syracuseStep 6600977 = 4950733) B4950733
theorem B1628439 : Blo 1626512 1628439 := bstep (se 1 (by rfl) ⟨1221329, by rfl⟩ : syracuseStep 1628439 = 2442659) B2442659
theorem B1628459 : Blo 1626512 1628459 := bstep (se 1 (by rfl) ⟨1221344, by rfl⟩ : syracuseStep 1628459 = 2442689) B2442689
theorem B3660083 : Blo 1626512 3660083 := bstep (se 1 (by rfl) ⟨2745062, by rfl⟩ : syracuseStep 3660083 = 5490125) B5490125
theorem B1628471 : Blo 1626512 1628471 := bstep (se 1 (by rfl) ⟨1221353, by rfl⟩ : syracuseStep 1628471 = 2442707) B2442707
theorem B1628491 : Blo 1626512 1628491 := bstep (se 1 (by rfl) ⟨1221368, by rfl⟩ : syracuseStep 1628491 = 2442737) B2442737
theorem B3660119 : Blo 1626512 3660119 := bstep (se 1 (by rfl) ⟨2745089, by rfl⟩ : syracuseStep 3660119 = 5490179) B5490179
theorem B1628503 : Blo 1626512 1628503 := bstep (se 1 (by rfl) ⟨1221377, by rfl⟩ : syracuseStep 1628503 = 2442755) B2442755
theorem B35682709 : Blo 1626512 35682709 := bstep (se 6 (by rfl) ⟨836313, by rfl⟩ : syracuseStep 35682709 = 1672627) B1672627
theorem B5216663 : Blo 1626512 5216663 := bstep (se 1 (by rfl) ⟨3912497, by rfl⟩ : syracuseStep 5216663 = 7824995) B7824995
theorem B4635073 : Blo 1626512 4635073 := bstep (se 2 (by rfl) ⟨1738152, by rfl⟩ : syracuseStep 4635073 = 3476305) B3476305
theorem B3660299 : Blo 1626512 3660299 := bstep (se 1 (by rfl) ⟨2745224, by rfl⟩ : syracuseStep 3660299 = 5490449) B5490449
theorem B3660353 : Blo 1626512 3660353 := bstep (se 2 (by rfl) ⟨1372632, by rfl⟩ : syracuseStep 3660353 = 2745265) B2745265
theorem B3299969 : Blo 1626512 3299969 := bstep (se 2 (by rfl) ⟨1237488, by rfl⟩ : syracuseStep 3299969 = 2474977) B2474977
theorem B9263767 : Blo 1626512 9263767 := bstep (se 1 (by rfl) ⟨6947825, by rfl⟩ : syracuseStep 9263767 = 13895651) B13895651
theorem B2439833 : Blo 1626512 2439833 := bstep (se 2 (by rfl) ⟨914937, by rfl⟩ : syracuseStep 2439833 = 1829875) B1829875
theorem B2439947 : Blo 1626512 2439947 := bstep (se 1 (by rfl) ⟨1829960, by rfl⟩ : syracuseStep 2439947 = 3659921) B3659921
theorem B2439959 : Blo 1626512 2439959 := bstep (se 1 (by rfl) ⟨1829969, by rfl⟩ : syracuseStep 2439959 = 3659939) B3659939
theorem B3660569 : Blo 1626512 3660569 := bstep (se 2 (by rfl) ⟨1372713, by rfl⟩ : syracuseStep 3660569 = 2745427) B2745427
theorem B2317081 : Blo 1626512 2317081 := bstep (se 2 (by rfl) ⟨868905, by rfl⟩ : syracuseStep 2317081 = 1737811) B1737811
theorem B2440025 : Blo 1626512 2440025 := bstep (se 2 (by rfl) ⟨915009, by rfl⟩ : syracuseStep 2440025 = 1830019) B1830019
theorem B3660659 : Blo 1626512 3660659 := bstep (se 1 (by rfl) ⟨2745494, by rfl⟩ : syracuseStep 3660659 = 5490989) B5490989
theorem B2317195 : Blo 1626512 2317195 := bstep (se 1 (by rfl) ⟨1737896, by rfl⟩ : syracuseStep 2317195 = 3475793) B3475793
theorem B3660695 : Blo 1626512 3660695 := bstep (se 1 (by rfl) ⟨2745521, by rfl⟩ : syracuseStep 3660695 = 5491043) B5491043
theorem B114342853 : Blo 1626512 114342853 := bstep (se 4 (by rfl) ⟨10719642, by rfl⟩ : syracuseStep 114342853 = 21439285) B21439285
theorem B2440139 : Blo 1626512 2440139 := bstep (se 1 (by rfl) ⟨1830104, by rfl⟩ : syracuseStep 2440139 = 3660209) B3660209
theorem B2440151 : Blo 1626512 2440151 := bstep (se 1 (by rfl) ⟨1830113, by rfl⟩ : syracuseStep 2440151 = 3660227) B3660227
theorem B20847577 : Blo 1626512 20847577 := bstep (se 2 (by rfl) ⟨7817841, by rfl⟩ : syracuseStep 20847577 = 15635683) B15635683
theorem B6175709 : Blo 1626512 6175709 := bstep (se 3 (by rfl) ⟨1157945, by rfl⟩ : syracuseStep 6175709 = 2315891) B2315891
theorem B2440217 : Blo 1626512 2440217 := bstep (se 2 (by rfl) ⟨915081, by rfl⟩ : syracuseStep 2440217 = 1830163) B1830163
theorem B60218437 : Blo 1626512 60218437 := bstep (se 4 (by rfl) ⟨5645478, by rfl⟩ : syracuseStep 60218437 = 11290957) B11290957
theorem B3660875 : Blo 1626512 3660875 := bstep (se 1 (by rfl) ⟨2745656, by rfl⟩ : syracuseStep 3660875 = 5491313) B5491313
theorem B3660929 : Blo 1626512 3660929 := bstep (se 2 (by rfl) ⟨1372848, by rfl⟩ : syracuseStep 3660929 = 2745697) B2745697
theorem B2440331 : Blo 1626512 2440331 := bstep (se 1 (by rfl) ⟨1830248, by rfl⟩ : syracuseStep 2440331 = 3660497) B3660497
theorem B2440343 : Blo 1626512 2440343 := bstep (se 1 (by rfl) ⟨1830257, by rfl⟩ : syracuseStep 2440343 = 3660515) B3660515
theorem B4119731 : Blo 1626512 4119731 := bstep (se 1 (by rfl) ⟨3089798, by rfl⟩ : syracuseStep 4119731 = 6179597) B6179597
theorem B5496011 : Blo 1626512 5496011 := bstep (se 1 (by rfl) ⟨4122008, by rfl⟩ : syracuseStep 5496011 = 8244017) B8244017
theorem B2473177 : Blo 1626512 2473177 := bstep (se 2 (by rfl) ⟨927441, by rfl⟩ : syracuseStep 2473177 = 1854883) B1854883
theorem B2440409 : Blo 1626512 2440409 := bstep (se 2 (by rfl) ⟨915153, by rfl⟩ : syracuseStep 2440409 = 1830307) B1830307
theorem B2440523 : Blo 1626512 2440523 := bstep (se 1 (by rfl) ⟨1830392, by rfl⟩ : syracuseStep 2440523 = 3660785) B3660785
theorem B2440535 : Blo 1626512 2440535 := bstep (se 1 (by rfl) ⟨1830401, by rfl⟩ : syracuseStep 2440535 = 3660803) B3660803
theorem B3661145 : Blo 1626512 3661145 := bstep (se 2 (by rfl) ⟨1372929, by rfl⟩ : syracuseStep 3661145 = 2745859) B2745859
theorem B2440601 : Blo 1626512 2440601 := bstep (se 2 (by rfl) ⟨915225, by rfl⟩ : syracuseStep 2440601 = 1830451) B1830451
theorem B3661235 : Blo 1626512 3661235 := bstep (se 1 (by rfl) ⟨2745926, by rfl⟩ : syracuseStep 3661235 = 5491853) B5491853
theorem B3661271 : Blo 1626512 3661271 := bstep (se 1 (by rfl) ⟨2745953, by rfl⟩ : syracuseStep 3661271 = 5491907) B5491907
theorem B2440715 : Blo 1626512 2440715 := bstep (se 1 (by rfl) ⟨1830536, by rfl⟩ : syracuseStep 2440715 = 3661073) B3661073
theorem B41688593 : Blo 1626512 41688593 := bstep (se 2 (by rfl) ⟨15633222, by rfl⟩ : syracuseStep 41688593 = 31266445) B31266445
theorem B2440727 : Blo 1626512 2440727 := bstep (se 1 (by rfl) ⟨1830545, by rfl⟩ : syracuseStep 2440727 = 3661091) B3661091
theorem B2440793 : Blo 1626512 2440793 := bstep (se 2 (by rfl) ⟨915297, by rfl⟩ : syracuseStep 2440793 = 1830595) B1830595
theorem B11140739 : Blo 1626512 11140739 := bstep (se 1 (by rfl) ⟨8355554, by rfl⟩ : syracuseStep 11140739 = 16711109) B16711109
theorem B3661451 : Blo 1626512 3661451 := bstep (se 1 (by rfl) ⟨2746088, by rfl⟩ : syracuseStep 3661451 = 5492177) B5492177
theorem B3661505 : Blo 1626512 3661505 := bstep (se 2 (by rfl) ⟨1373064, by rfl⟩ : syracuseStep 3661505 = 2746129) B2746129
theorem B2440907 : Blo 1626512 2440907 := bstep (se 1 (by rfl) ⟨1830680, by rfl⟩ : syracuseStep 2440907 = 3661361) B3661361
theorem B4120267 : Blo 1626512 4120267 := bstep (se 1 (by rfl) ⟨3090200, by rfl⟩ : syracuseStep 4120267 = 6180401) B6180401
theorem B2440919 : Blo 1626512 2440919 := bstep (se 1 (by rfl) ⟨1830689, by rfl⟩ : syracuseStep 2440919 = 3661379) B3661379
theorem B7421719 : Blo 1626512 7421719 := bstep (se 1 (by rfl) ⟨5566289, by rfl⟩ : syracuseStep 7421719 = 11132579) B11132579
theorem B2440985 : Blo 1626512 2440985 := bstep (se 2 (by rfl) ⟨915369, by rfl⟩ : syracuseStep 2440985 = 1830739) B1830739
theorem B6602519 : Blo 1626512 6602519 := bstep (se 1 (by rfl) ⟨4951889, by rfl⟩ : syracuseStep 6602519 = 9903779) B9903779
theorem B6954797 : Blo 1626512 6954797 := bstep (se 3 (by rfl) ⟨1304024, by rfl⟩ : syracuseStep 6954797 = 2608049) B2608049
theorem B4120409 : Blo 1626512 4120409 := bstep (se 2 (by rfl) ⟨1545153, by rfl⟩ : syracuseStep 4120409 = 3090307) B3090307
theorem B2441099 : Blo 1626512 2441099 := bstep (se 1 (by rfl) ⟨1830824, by rfl⟩ : syracuseStep 2441099 = 3661649) B3661649
theorem B2441111 : Blo 1626512 2441111 := bstep (se 1 (by rfl) ⟨1830833, by rfl⟩ : syracuseStep 2441111 = 3661667) B3661667
theorem B3661721 : Blo 1626512 3661721 := bstep (se 2 (by rfl) ⟨1373145, by rfl⟩ : syracuseStep 3661721 = 2746291) B2746291
theorem B2441177 : Blo 1626512 2441177 := bstep (se 2 (by rfl) ⟨915441, by rfl⟩ : syracuseStep 2441177 = 1830883) B1830883
theorem B3661811 : Blo 1626512 3661811 := bstep (se 1 (by rfl) ⟨2746358, by rfl⟩ : syracuseStep 3661811 = 5492717) B5492717
theorem B2441231 : Blo 1626512 2441231 := bstep (se 1 (by rfl) ⟨1830923, by rfl⟩ : syracuseStep 2441231 = 3661847) B3661847
theorem B4120591 : Blo 1626512 4120591 := bstep (se 1 (by rfl) ⟨3090443, by rfl⟩ : syracuseStep 4120591 = 6180887) B6180887
theorem B2441273 : Blo 1626512 2441273 := bstep (se 2 (by rfl) ⟨915477, by rfl⟩ : syracuseStep 2441273 = 1830955) B1830955
theorem B3522619 : Blo 1626512 3522619 := bstep (se 1 (by rfl) ⟨2641964, by rfl⟩ : syracuseStep 3522619 = 5283929) B5283929
theorem B3661883 : Blo 1626512 3661883 := bstep (se 1 (by rfl) ⟨2746412, by rfl⟩ : syracuseStep 3661883 = 5492825) B5492825
theorem B9904189 : Blo 1626512 9904189 := bstep (se 3 (by rfl) ⟨1857035, by rfl⟩ : syracuseStep 9904189 = 3714071) B3714071
theorem B4636759 : Blo 1626512 4636759 := bstep (se 1 (by rfl) ⟨3477569, by rfl⟩ : syracuseStep 4636759 = 6955139) B6955139
theorem B2441351 : Blo 1626512 2441351 := bstep (se 1 (by rfl) ⟨1831013, by rfl⟩ : syracuseStep 2441351 = 3662027) B3662027
theorem B2441387 : Blo 1626512 2441387 := bstep (se 1 (by rfl) ⟨1831040, by rfl⟩ : syracuseStep 2441387 = 3662081) B3662081
theorem B3662009 : Blo 1626512 3662009 := bstep (se 2 (by rfl) ⟨1373253, by rfl⟩ : syracuseStep 3662009 = 2746507) B2746507
theorem B6176969 : Blo 1626512 6176969 := bstep (se 2 (by rfl) ⟨2316363, by rfl⟩ : syracuseStep 6176969 = 4632727) B4632727
theorem B2441417 : Blo 1626512 2441417 := bstep (se 2 (by rfl) ⟨915531, by rfl⟩ : syracuseStep 2441417 = 1831063) B1831063
theorem B45793525 : Blo 1626512 45793525 := bstep (se 5 (by rfl) ⟨2146571, by rfl⟩ : syracuseStep 45793525 = 4293143) B4293143
theorem B20848913 : Blo 1626512 20848913 := bstep (se 2 (by rfl) ⟨7818342, by rfl⟩ : syracuseStep 20848913 = 15636685) B15636685
theorem B4120865 : Blo 1626512 4120865 := bstep (se 2 (by rfl) ⟨1545324, by rfl⟩ : syracuseStep 4120865 = 3090649) B3090649
theorem B2474297 : Blo 1626512 2474297 := bstep (se 2 (by rfl) ⟨927861, by rfl⟩ : syracuseStep 2474297 = 1855723) B1855723
theorem B2441531 : Blo 1626512 2441531 := bstep (se 1 (by rfl) ⟨1831148, by rfl⟩ : syracuseStep 2441531 = 3662297) B3662297
theorem B6955379 : Blo 1626512 6955379 := bstep (se 1 (by rfl) ⟨5216534, by rfl⟩ : syracuseStep 6955379 = 10433069) B10433069
theorem B2441591 : Blo 1626512 2441591 := bstep (se 1 (by rfl) ⟨1831193, by rfl⟩ : syracuseStep 2441591 = 3662387) B3662387
theorem B2441615 : Blo 1626512 2441615 := bstep (se 1 (by rfl) ⟨1831211, by rfl⟩ : syracuseStep 2441615 = 3662423) B3662423
theorem B2441657 : Blo 1626512 2441657 := bstep (se 2 (by rfl) ⟨915621, by rfl⟩ : syracuseStep 2441657 = 1831243) B1831243
theorem B2441735 : Blo 1626512 2441735 := bstep (se 1 (by rfl) ⟨1831301, by rfl⟩ : syracuseStep 2441735 = 3662603) B3662603
theorem B2605583 : Blo 1626512 2605583 := bstep (se 1 (by rfl) ⟨1954187, by rfl⟩ : syracuseStep 2605583 = 3908375) B3908375
theorem B3662351 : Blo 1626512 3662351 := bstep (se 1 (by rfl) ⟨2746763, by rfl⟩ : syracuseStep 3662351 = 5493527) B5493527
theorem B2933263 : Blo 1626512 2933263 := bstep (se 1 (by rfl) ⟨2199947, by rfl⟩ : syracuseStep 2933263 = 4399895) B4399895
theorem B3662369 : Blo 1626512 3662369 := bstep (se 2 (by rfl) ⟨1373388, by rfl⟩ : syracuseStep 3662369 = 2746777) B2746777
theorem B42254891 : Blo 1626512 42254891 := bstep (se 1 (by rfl) ⟨31691168, by rfl⟩ : syracuseStep 42254891 = 63382337) B63382337
theorem B2441771 : Blo 1626512 2441771 := bstep (se 1 (by rfl) ⟨1831328, by rfl⟩ : syracuseStep 2441771 = 3662657) B3662657
theorem B3088955 : Blo 1626512 3088955 := bstep (se 1 (by rfl) ⟨2316716, by rfl⟩ : syracuseStep 3088955 = 4633433) B4633433
theorem B16695875 : Blo 1626512 16695875 := bstep (se 1 (by rfl) ⟨12521906, by rfl⟩ : syracuseStep 16695875 = 25043813) B25043813
theorem B2441801 : Blo 1626512 2441801 := bstep (se 2 (by rfl) ⟨915675, by rfl⟩ : syracuseStep 2441801 = 1831351) B1831351
theorem B9265751 : Blo 1626512 9265751 := bstep (se 1 (by rfl) ⟨6949313, by rfl⟩ : syracuseStep 9265751 = 13898627) B13898627
theorem B68633219 : Blo 1626512 68633219 := bstep (se 1 (by rfl) ⟨51474914, by rfl⟩ : syracuseStep 68633219 = 102949829) B102949829
theorem B2441915 : Blo 1626512 2441915 := bstep (se 1 (by rfl) ⟨1831436, by rfl⟩ : syracuseStep 2441915 = 3662873) B3662873
theorem B2441975 : Blo 1626512 2441975 := bstep (se 1 (by rfl) ⟨1831481, by rfl⟩ : syracuseStep 2441975 = 3662963) B3662963
theorem B2745103 : Blo 1626512 2745103 := bstep (se 1 (by rfl) ⟨2058827, by rfl⟩ : syracuseStep 2745103 = 4117655) B4117655
theorem B2441999 : Blo 1626512 2441999 := bstep (se 1 (by rfl) ⟨1831499, by rfl⟩ : syracuseStep 2441999 = 3662999) B3662999
theorem B2442041 : Blo 1626512 2442041 := bstep (se 2 (by rfl) ⟨915765, by rfl⟩ : syracuseStep 2442041 = 1831531) B1831531
theorem B3662711 : Blo 1626512 3662711 := bstep (se 1 (by rfl) ⟨2747033, by rfl⟩ : syracuseStep 3662711 = 5494067) B5494067
theorem B2442119 : Blo 1626512 2442119 := bstep (se 1 (by rfl) ⟨1831589, by rfl⟩ : syracuseStep 2442119 = 3663179) B3663179
theorem B9274247 : Blo 1626512 9274247 := bstep (se 1 (by rfl) ⟨6955685, by rfl⟩ : syracuseStep 9274247 = 13911371) B13911371
theorem B8242073 : Blo 1626512 8242073 := bstep (se 2 (by rfl) ⟨3090777, by rfl⟩ : syracuseStep 8242073 = 6181555) B6181555
theorem B2442155 : Blo 1626512 2442155 := bstep (se 1 (by rfl) ⟨1831616, by rfl⟩ : syracuseStep 2442155 = 3663233) B3663233
theorem B2442185 : Blo 1626512 2442185 := bstep (se 2 (by rfl) ⟨915819, by rfl⟩ : syracuseStep 2442185 = 1831639) B1831639
theorem B5489693 : Blo 1626512 5489693 := bstep (se 3 (by rfl) ⟨1029317, by rfl⟩ : syracuseStep 5489693 = 2058635) B2058635
theorem B3089441 : Blo 1626512 3089441 := bstep (se 2 (by rfl) ⟨1158540, by rfl⟩ : syracuseStep 3089441 = 2317081) B2317081
theorem B3662891 : Blo 1626512 3662891 := bstep (se 1 (by rfl) ⟨2747168, by rfl⟩ : syracuseStep 3662891 = 5494337) B5494337
theorem B2442299 : Blo 1626512 2442299 := bstep (se 1 (by rfl) ⟨1831724, by rfl⟩ : syracuseStep 2442299 = 3663449) B3663449
theorem B2442359 : Blo 1626512 2442359 := bstep (se 1 (by rfl) ⟨1831769, by rfl⟩ : syracuseStep 2442359 = 3663539) B3663539
theorem B56386691 : Blo 1626512 56386691 := bstep (se 1 (by rfl) ⟨42290018, by rfl⟩ : syracuseStep 56386691 = 84580037) B84580037
theorem B2442383 : Blo 1626512 2442383 := bstep (se 1 (by rfl) ⟨1831787, by rfl⟩ : syracuseStep 2442383 = 3663575) B3663575
theorem B3089593 : Blo 1626512 3089593 := bstep (se 2 (by rfl) ⟨1158597, by rfl⟩ : syracuseStep 3089593 = 2317195) B2317195
theorem B2442425 : Blo 1626512 2442425 := bstep (se 2 (by rfl) ⟨915909, by rfl⟩ : syracuseStep 2442425 = 1831819) B1831819
theorem B2442503 : Blo 1626512 2442503 := bstep (se 1 (by rfl) ⟨1831877, by rfl⟩ : syracuseStep 2442503 = 3663755) B3663755
theorem B4121867 : Blo 1626512 4121867 := bstep (se 1 (by rfl) ⟨3091400, by rfl⟩ : syracuseStep 4121867 = 6182801) B6182801
theorem B27796769 : Blo 1626512 27796769 := bstep (se 2 (by rfl) ⟨10423788, by rfl⟩ : syracuseStep 27796769 = 20847577) B20847577
theorem B2934049 : Blo 1626512 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B2745643 : Blo 1626512 2745643 := bstep (se 1 (by rfl) ⟨2059232, by rfl⟩ : syracuseStep 2745643 = 4118465) B4118465
theorem B2442539 : Blo 1626512 2442539 := bstep (se 1 (by rfl) ⟨1831904, by rfl⟩ : syracuseStep 2442539 = 3663809) B3663809
theorem B7816499 : Blo 1626512 7816499 := bstep (se 1 (by rfl) ⟨5862374, by rfl⟩ : syracuseStep 7816499 = 11724749) B11724749
theorem B2442569 : Blo 1626512 2442569 := bstep (se 2 (by rfl) ⟨915963, by rfl⟩ : syracuseStep 2442569 = 1831927) B1831927
theorem B3908999 : Blo 1626512 3908999 := bstep (se 1 (by rfl) ⟨2931749, by rfl⟩ : syracuseStep 3908999 = 5863499) B5863499
theorem B3663251 : Blo 1626512 3663251 := bstep (se 1 (by rfl) ⟨2747438, by rfl⟩ : syracuseStep 3663251 = 5494877) B5494877
theorem B80291249 : Blo 1626512 80291249 := bstep (se 2 (by rfl) ⟨30109218, by rfl⟩ : syracuseStep 80291249 = 60218437) B60218437
theorem B2745785 : Blo 1626512 2745785 := bstep (se 2 (by rfl) ⟨1029669, by rfl⟩ : syracuseStep 2745785 = 2059339) B2059339
theorem B2442683 : Blo 1626512 2442683 := bstep (se 1 (by rfl) ⟨1832012, by rfl⟩ : syracuseStep 2442683 = 3664025) B3664025
theorem B2606537 : Blo 1626512 2606537 := bstep (se 2 (by rfl) ⟨977451, by rfl⟩ : syracuseStep 2606537 = 1954903) B1954903
theorem B3663305 : Blo 1626512 3663305 := bstep (se 2 (by rfl) ⟨1373739, by rfl⟩ : syracuseStep 3663305 = 2747479) B2747479
theorem B6948305 : Blo 1626512 6948305 := bstep (se 2 (by rfl) ⟨2605614, by rfl⟩ : syracuseStep 6948305 = 5211229) B5211229
theorem B2442743 : Blo 1626512 2442743 := bstep (se 1 (by rfl) ⟨1832057, by rfl⟩ : syracuseStep 2442743 = 3664115) B3664115
theorem B4400651 : Blo 1626512 4400651 := bstep (se 1 (by rfl) ⟨3300488, by rfl⟩ : syracuseStep 4400651 = 6600977) B6600977
theorem B2442767 : Blo 1626512 2442767 := bstep (se 1 (by rfl) ⟨1832075, by rfl⟩ : syracuseStep 2442767 = 3664151) B3664151
theorem B6260291 : Blo 1626512 6260291 := bstep (se 1 (by rfl) ⟨4695218, by rfl⟩ : syracuseStep 6260291 = 9390437) B9390437
theorem B19793585 : Blo 1626512 19793585 := bstep (se 2 (by rfl) ⟨7422594, by rfl⟩ : syracuseStep 19793585 = 14845189) B14845189
theorem B3344171 : Blo 1626512 3344171 := bstep (se 1 (by rfl) ⟨2508128, by rfl⟩ : syracuseStep 3344171 = 5016257) B5016257
theorem B1738631 : Blo 1626512 1738631 := bstep (se 1 (by rfl) ⟨1303973, by rfl⟩ : syracuseStep 1738631 = 2607947) B2607947
theorem B9898013 : Blo 1626512 9898013 := bstep (se 3 (by rfl) ⟨1855877, by rfl⟩ : syracuseStep 9898013 = 3711755) B3711755
theorem B17606717 : Blo 1626512 17606717 := bstep (se 3 (by rfl) ⟨3301259, by rfl⟩ : syracuseStep 17606717 = 6602519) B6602519
theorem B2746487 : Blo 1626512 2746487 := bstep (se 1 (by rfl) ⟨2059865, by rfl⟩ : syracuseStep 2746487 = 4119731) B4119731
theorem B2607223 : Blo 1626512 2607223 := bstep (se 1 (by rfl) ⟨1955417, by rfl⟩ : syracuseStep 2607223 = 3910835) B3910835
theorem B3664007 : Blo 1626512 3664007 := bstep (se 1 (by rfl) ⟨2748005, by rfl⟩ : syracuseStep 3664007 = 5496011) B5496011
theorem B2509115 : Blo 1626512 2509115 := bstep (se 1 (by rfl) ⟨1881836, by rfl⟩ : syracuseStep 2509115 = 3763673) B3763673
theorem B7047539 : Blo 1626512 7047539 := bstep (se 1 (by rfl) ⟨5285654, by rfl⟩ : syracuseStep 7047539 = 10571309) B10571309
theorem B5491097 : Blo 1626512 5491097 := bstep (se 2 (by rfl) ⟨2059161, by rfl⟩ : syracuseStep 5491097 = 4118323) B4118323
theorem B9267641 : Blo 1626512 9267641 := bstep (se 2 (by rfl) ⟨3475365, by rfl⟩ : syracuseStep 9267641 = 6950731) B6950731
theorem B2746939 : Blo 1626512 2746939 := bstep (se 1 (by rfl) ⟨2060204, by rfl⟩ : syracuseStep 2746939 = 4120409) B4120409
theorem B2747081 : Blo 1626512 2747081 := bstep (se 2 (by rfl) ⟨1030155, by rfl⟩ : syracuseStep 2747081 = 2060311) B2060311
theorem B2059015 : Blo 1626512 2059015 := bstep (se 1 (by rfl) ⟨1544261, by rfl⟩ : syracuseStep 2059015 = 3088523) B3088523
theorem B3910459 : Blo 1626512 3910459 := bstep (se 1 (by rfl) ⟨2932844, by rfl⟩ : syracuseStep 3910459 = 5865689) B5865689
theorem B9898841 : Blo 1626512 9898841 := bstep (se 2 (by rfl) ⟨3712065, by rfl⟩ : syracuseStep 9898841 = 7424131) B7424131
theorem B3091385 : Blo 1626512 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B12364811 : Blo 1626512 12364811 := bstep (se 1 (by rfl) ⟨9273608, by rfl⟩ : syracuseStep 12364811 = 18547217) B18547217
theorem B1829947 : Blo 1626512 1829947 := bstep (se 1 (by rfl) ⟨1372460, by rfl⟩ : syracuseStep 1829947 = 2744921) B2744921
theorem B5491799 : Blo 1626512 5491799 := bstep (se 1 (by rfl) ⟨4118849, by rfl⟩ : syracuseStep 5491799 = 8237699) B8237699
theorem B6597719 : Blo 1626512 6597719 := bstep (se 1 (by rfl) ⟨4948289, by rfl⟩ : syracuseStep 6597719 = 9896579) B9896579
theorem B26405975 : Blo 1626512 26405975 := bstep (se 1 (by rfl) ⟨19804481, by rfl⟩ : syracuseStep 26405975 = 39608963) B39608963
theorem B2059435 : Blo 1626512 2059435 := bstep (se 1 (by rfl) ⟨1544576, by rfl⟩ : syracuseStep 2059435 = 3089153) B3089153
theorem B6180097 : Blo 1626512 6180097 := bstep (se 2 (by rfl) ⟨2317536, by rfl⟩ : syracuseStep 6180097 = 4635073) B4635073
theorem B8236403 : Blo 1626512 8236403 := bstep (se 1 (by rfl) ⟨6177302, by rfl⟩ : syracuseStep 8236403 = 12354605) B12354605
theorem B10423687 : Blo 1626512 10423687 := bstep (se 1 (by rfl) ⟨7817765, by rfl⟩ : syracuseStep 10423687 = 15635531) B15635531
theorem B2747783 : Blo 1626512 2747783 := bstep (se 1 (by rfl) ⟨2060837, by rfl⟩ : syracuseStep 2747783 = 4121675) B4121675
theorem B2059663 : Blo 1626512 2059663 := bstep (se 1 (by rfl) ⟨1544747, by rfl⟩ : syracuseStep 2059663 = 3089495) B3089495
theorem B5565881 : Blo 1626512 5565881 := bstep (se 2 (by rfl) ⟨2087205, by rfl⟩ : syracuseStep 5565881 = 4174411) B4174411
theorem B5017099 : Blo 1626512 5017099 := bstep (se 1 (by rfl) ⟨3762824, by rfl⟩ : syracuseStep 5017099 = 7525649) B7525649
theorem B1830415 : Blo 1626512 1830415 := bstep (se 1 (by rfl) ⟨1372811, by rfl⟩ : syracuseStep 1830415 = 2745623) B2745623
theorem B5492285 : Blo 1626512 5492285 := bstep (se 3 (by rfl) ⟨1029803, by rfl⟩ : syracuseStep 5492285 = 2059607) B2059607
theorem B17600179 : Blo 1626512 17600179 := bstep (se 1 (by rfl) ⟨13200134, by rfl⟩ : syracuseStep 17600179 = 26400269) B26400269
theorem B6598381 : Blo 1626512 6598381 := bstep (se 3 (by rfl) ⟨1237196, by rfl⟩ : syracuseStep 6598381 = 2474393) B2474393
theorem B1650439 : Blo 1626512 1650439 := bstep (se 1 (by rfl) ⟨1237829, by rfl⟩ : syracuseStep 1650439 = 2475659) B2475659
theorem B8236889 : Blo 1626512 8236889 := bstep (se 2 (by rfl) ⟨3088833, by rfl⟩ : syracuseStep 8236889 = 6177667) B6177667
theorem B22261655 : Blo 1626512 22261655 := bstep (se 1 (by rfl) ⟨16696241, by rfl⟩ : syracuseStep 22261655 = 33392483) B33392483
theorem B152457137 : Blo 1626512 152457137 := bstep (se 2 (by rfl) ⟨57171426, by rfl⟩ : syracuseStep 152457137 = 114342853) B114342853
theorem B3477433 : Blo 1626512 3477433 := bstep (se 2 (by rfl) ⟨1304037, by rfl⟩ : syracuseStep 3477433 = 2608075) B2608075
theorem B1830919 : Blo 1626512 1830919 := bstep (se 1 (by rfl) ⟨1373189, by rfl⟩ : syracuseStep 1830919 = 2746379) B2746379
theorem B2060407 : Blo 1626512 2060407 := bstep (se 1 (by rfl) ⟨1545305, by rfl⟩ : syracuseStep 2060407 = 3090611) B3090611
theorem B20852909 : Blo 1626512 20852909 := bstep (se 3 (by rfl) ⟨3909920, by rfl⟩ : syracuseStep 20852909 = 7819841) B7819841
theorem B1831099 : Blo 1626512 1831099 := bstep (se 1 (by rfl) ⟨1373324, by rfl⟩ : syracuseStep 1831099 = 2746649) B2746649
theorem B3477775 : Blo 1626512 3477775 := bstep (se 1 (by rfl) ⟨2608331, by rfl⟩ : syracuseStep 3477775 = 5216663) B5216663
theorem B3297569 : Blo 1626512 3297569 := bstep (se 2 (by rfl) ⟨1236588, by rfl⟩ : syracuseStep 3297569 = 2473177) B2473177
theorem B10424609 : Blo 1626512 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B2199979 : Blo 1626512 2199979 := bstep (se 1 (by rfl) ⟨1649984, by rfl⟩ : syracuseStep 2199979 = 3299969) B3299969
theorem B4764089 : Blo 1626512 4764089 := bstep (se 2 (by rfl) ⟨1786533, by rfl⟩ : syracuseStep 4764089 = 3573067) B3573067
theorem B1626555 : Blo 1626512 1626555 := bstep (se 1 (by rfl) ⟨1219916, by rfl⟩ : syracuseStep 1626555 = 2439833) B2439833
theorem B2060731 : Blo 1626512 2060731 := bstep (se 1 (by rfl) ⟨1545548, by rfl⟩ : syracuseStep 2060731 = 3091097) B3091097
theorem B1626631 : Blo 1626512 1626631 := bstep (se 1 (by rfl) ⟨1219973, by rfl⟩ : syracuseStep 1626631 = 2439947) B2439947
theorem B1626639 : Blo 1626512 1626639 := bstep (se 1 (by rfl) ⟨1219979, by rfl⟩ : syracuseStep 1626639 = 2439959) B2439959
theorem B1626683 : Blo 1626512 1626683 := bstep (se 1 (by rfl) ⟨1220012, by rfl⟩ : syracuseStep 1626683 = 2440025) B2440025
theorem B1626759 : Blo 1626512 1626759 := bstep (se 1 (by rfl) ⟨1220069, by rfl⟩ : syracuseStep 1626759 = 2440139) B2440139
theorem B1626767 : Blo 1626512 1626767 := bstep (se 1 (by rfl) ⟨1220075, by rfl⟩ : syracuseStep 1626767 = 2440151) B2440151
theorem B1831567 : Blo 1626512 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B4117139 : Blo 1626512 4117139 := bstep (se 1 (by rfl) ⟨3087854, by rfl⟩ : syracuseStep 4117139 = 6175709) B6175709
theorem B1626811 : Blo 1626512 1626811 := bstep (se 1 (by rfl) ⟨1220108, by rfl⟩ : syracuseStep 1626811 = 2440217) B2440217
theorem B8794817 : Blo 1626512 8794817 := bstep (se 2 (by rfl) ⟨3298056, by rfl⟩ : syracuseStep 8794817 = 6596113) B6596113
theorem B1626887 : Blo 1626512 1626887 := bstep (se 1 (by rfl) ⟨1220165, by rfl⟩ : syracuseStep 1626887 = 2440331) B2440331
theorem B1626895 : Blo 1626512 1626895 := bstep (se 1 (by rfl) ⟨1220171, by rfl⟩ : syracuseStep 1626895 = 2440343) B2440343
theorem B1626939 : Blo 1626512 1626939 := bstep (se 1 (by rfl) ⟨1220204, by rfl⟩ : syracuseStep 1626939 = 2440409) B2440409
theorem B1627015 : Blo 1626512 1627015 := bstep (se 1 (by rfl) ⟨1220261, by rfl⟩ : syracuseStep 1627015 = 2440523) B2440523
theorem B1627023 : Blo 1626512 1627023 := bstep (se 1 (by rfl) ⟨1220267, by rfl⟩ : syracuseStep 1627023 = 2440535) B2440535
theorem B5493689 : Blo 1626512 5493689 := bstep (se 2 (by rfl) ⟨2060133, by rfl⟩ : syracuseStep 5493689 = 4120267) B4120267
theorem B1627067 : Blo 1626512 1627067 := bstep (se 1 (by rfl) ⟨1220300, by rfl⟩ : syracuseStep 1627067 = 2440601) B2440601
theorem B1627143 : Blo 1626512 1627143 := bstep (se 1 (by rfl) ⟨1220357, by rfl⟩ : syracuseStep 1627143 = 2440715) B2440715
theorem B27792395 : Blo 1626512 27792395 := bstep (se 1 (by rfl) ⟨20844296, by rfl⟩ : syracuseStep 27792395 = 41688593) B41688593
theorem B4633615 : Blo 1626512 4633615 := bstep (se 1 (by rfl) ⟨3475211, by rfl⟩ : syracuseStep 4633615 = 6950423) B6950423
theorem B1627151 : Blo 1626512 1627151 := bstep (se 1 (by rfl) ⟨1220363, by rfl⟩ : syracuseStep 1627151 = 2440727) B2440727
theorem B1627195 : Blo 1626512 1627195 := bstep (se 1 (by rfl) ⟨1220396, by rfl⟩ : syracuseStep 1627195 = 2440793) B2440793
theorem B4633661 : Blo 1626512 4633661 := bstep (se 3 (by rfl) ⟨868811, by rfl⟩ : syracuseStep 4633661 = 1737623) B1737623
theorem B7427159 : Blo 1626512 7427159 := bstep (se 1 (by rfl) ⟨5570369, by rfl⟩ : syracuseStep 7427159 = 11140739) B11140739
theorem B1627271 : Blo 1626512 1627271 := bstep (se 1 (by rfl) ⟨1220453, by rfl⟩ : syracuseStep 1627271 = 2440907) B2440907
theorem B1832071 : Blo 1626512 1832071 := bstep (se 1 (by rfl) ⟨1374053, by rfl⟩ : syracuseStep 1832071 = 2748107) B2748107
theorem B1627279 : Blo 1626512 1627279 := bstep (se 1 (by rfl) ⟨1220459, by rfl⟩ : syracuseStep 1627279 = 2440919) B2440919
theorem B1627323 : Blo 1626512 1627323 := bstep (se 1 (by rfl) ⟨1220492, by rfl⟩ : syracuseStep 1627323 = 2440985) B2440985
theorem B1627399 : Blo 1626512 1627399 := bstep (se 1 (by rfl) ⟨1220549, by rfl⟩ : syracuseStep 1627399 = 2441099) B2441099
theorem B1627407 : Blo 1626512 1627407 := bstep (se 1 (by rfl) ⟨1220555, by rfl⟩ : syracuseStep 1627407 = 2441111) B2441111
theorem B1627451 : Blo 1626512 1627451 := bstep (se 1 (by rfl) ⟨1220588, by rfl⟩ : syracuseStep 1627451 = 2441177) B2441177
theorem B1627527 : Blo 1626512 1627527 := bstep (se 1 (by rfl) ⟨1220645, by rfl⟩ : syracuseStep 1627527 = 2441291) B2441291
theorem B1627535 : Blo 1626512 1627535 := bstep (se 1 (by rfl) ⟨1220651, by rfl⟩ : syracuseStep 1627535 = 2441303) B2441303
theorem B4634003 : Blo 1626512 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B1627579 : Blo 1626512 1627579 := bstep (se 1 (by rfl) ⟨1220684, by rfl⟩ : syracuseStep 1627579 = 2441369) B2441369
theorem B7820803 : Blo 1626512 7820803 := bstep (se 1 (by rfl) ⟨5865602, by rfl⟩ : syracuseStep 7820803 = 11731205) B11731205
theorem B1627655 : Blo 1626512 1627655 := bstep (se 1 (by rfl) ⟨1220741, by rfl⟩ : syracuseStep 1627655 = 2441483) B2441483
theorem B5494283 : Blo 1626512 5494283 := bstep (se 1 (by rfl) ⟨4120712, by rfl⟩ : syracuseStep 5494283 = 8241425) B8241425
theorem B1627663 : Blo 1626512 1627663 := bstep (se 1 (by rfl) ⟨1220747, by rfl⟩ : syracuseStep 1627663 = 2441495) B2441495
theorem B1627707 : Blo 1626512 1627707 := bstep (se 1 (by rfl) ⟨1220780, by rfl⟩ : syracuseStep 1627707 = 2441561) B2441561
theorem B4175479 : Blo 1626512 4175479 := bstep (se 1 (by rfl) ⟨3131609, by rfl⟩ : syracuseStep 4175479 = 6263219) B6263219
theorem B5494391 : Blo 1626512 5494391 := bstep (se 1 (by rfl) ⟨4120793, by rfl⟩ : syracuseStep 5494391 = 8241587) B8241587
theorem B1627783 : Blo 1626512 1627783 := bstep (se 1 (by rfl) ⟨1220837, by rfl⟩ : syracuseStep 1627783 = 2441675) B2441675
theorem B1627791 : Blo 1626512 1627791 := bstep (se 1 (by rfl) ⟨1220843, by rfl⟩ : syracuseStep 1627791 = 2441687) B2441687
theorem B1627835 : Blo 1626512 1627835 := bstep (se 1 (by rfl) ⟨1220876, by rfl⟩ : syracuseStep 1627835 = 2441753) B2441753
theorem B4118273 : Blo 1626512 4118273 := bstep (se 2 (by rfl) ⟨1544352, by rfl⟩ : syracuseStep 4118273 = 3088705) B3088705
theorem B1627911 : Blo 1626512 1627911 := bstep (se 1 (by rfl) ⟨1220933, by rfl⟩ : syracuseStep 1627911 = 2441867) B2441867
theorem B1627919 : Blo 1626512 1627919 := bstep (se 1 (by rfl) ⟨1220939, by rfl⟩ : syracuseStep 1627919 = 2441879) B2441879
theorem B1627963 : Blo 1626512 1627963 := bstep (se 1 (by rfl) ⟨1220972, by rfl⟩ : syracuseStep 1627963 = 2441945) B2441945
theorem B47576945 : Blo 1626512 47576945 := bstep (se 2 (by rfl) ⟨17841354, by rfl⟩ : syracuseStep 47576945 = 35682709) B35682709
theorem B1628039 : Blo 1626512 1628039 := bstep (se 1 (by rfl) ⟨1221029, by rfl⟩ : syracuseStep 1628039 = 2442059) B2442059
theorem B1628047 : Blo 1626512 1628047 := bstep (se 1 (by rfl) ⟨1221035, by rfl⟩ : syracuseStep 1628047 = 2442071) B2442071
theorem B8238995 : Blo 1626512 8238995 := bstep (se 1 (by rfl) ⟨6179246, by rfl⟩ : syracuseStep 8238995 = 12358493) B12358493
theorem B2348971 : Blo 1626512 2348971 := bstep (se 1 (by rfl) ⟨1761728, by rfl⟩ : syracuseStep 2348971 = 3523457) B3523457
theorem B3659705 : Blo 1626512 3659705 := bstep (se 2 (by rfl) ⟨1372389, by rfl⟩ : syracuseStep 3659705 = 2744779) B2744779
theorem B1628091 : Blo 1626512 1628091 := bstep (se 1 (by rfl) ⟨1221068, by rfl⟩ : syracuseStep 1628091 = 2442137) B2442137
theorem B2086903 : Blo 1626512 2086903 := bstep (se 1 (by rfl) ⟨1565177, by rfl⟩ : syracuseStep 2086903 = 3130355) B3130355
theorem B1628167 : Blo 1626512 1628167 := bstep (se 1 (by rfl) ⟨1221125, by rfl⟩ : syracuseStep 1628167 = 2442251) B2442251
theorem B1628175 : Blo 1626512 1628175 := bstep (se 1 (by rfl) ⟨1221131, by rfl⟩ : syracuseStep 1628175 = 2442263) B2442263
theorem B1628219 : Blo 1626512 1628219 := bstep (se 1 (by rfl) ⟨1221164, by rfl⟩ : syracuseStep 1628219 = 2442329) B2442329
theorem B6182999 : Blo 1626512 6182999 := bstep (se 1 (by rfl) ⟨4637249, by rfl⟩ : syracuseStep 6182999 = 9274499) B9274499
theorem B4118647 : Blo 1626512 4118647 := bstep (se 1 (by rfl) ⟨3088985, by rfl⟩ : syracuseStep 4118647 = 6177971) B6177971
theorem B1628295 : Blo 1626512 1628295 := bstep (se 1 (by rfl) ⟨1221221, by rfl⟩ : syracuseStep 1628295 = 2442443) B2442443
theorem B1628303 : Blo 1626512 1628303 := bstep (se 1 (by rfl) ⟨1221227, by rfl⟩ : syracuseStep 1628303 = 2442455) B2442455
theorem B27121837 : Blo 1626512 27121837 := bstep (se 3 (by rfl) ⟨5085344, by rfl⟩ : syracuseStep 27121837 = 10170689) B10170689
theorem B1628347 : Blo 1626512 1628347 := bstep (se 1 (by rfl) ⟨1221260, by rfl⟩ : syracuseStep 1628347 = 2442521) B2442521
theorem B12351689 : Blo 1626512 12351689 := bstep (se 2 (by rfl) ⟨4631883, by rfl⟩ : syracuseStep 12351689 = 9263767) B9263767
theorem B5494985 : Blo 1626512 5494985 := bstep (se 2 (by rfl) ⟨2060619, by rfl⟩ : syracuseStep 5494985 = 4121239) B4121239
theorem B1628423 : Blo 1626512 1628423 := bstep (se 1 (by rfl) ⟨1221317, by rfl⟩ : syracuseStep 1628423 = 2442635) B2442635
theorem B4634891 : Blo 1626512 4634891 := bstep (se 1 (by rfl) ⟨3476168, by rfl⟩ : syracuseStep 4634891 = 6952337) B6952337
theorem B3660047 : Blo 1626512 3660047 := bstep (se 1 (by rfl) ⟨2745035, by rfl⟩ : syracuseStep 3660047 = 5490071) B5490071
theorem B1628431 : Blo 1626512 1628431 := bstep (se 1 (by rfl) ⟨1221323, by rfl⟩ : syracuseStep 1628431 = 2442647) B2442647
theorem B3660065 : Blo 1626512 3660065 := bstep (se 2 (by rfl) ⟨1372524, by rfl⟩ : syracuseStep 3660065 = 2745049) B2745049
theorem B1628475 : Blo 1626512 1628475 := bstep (se 1 (by rfl) ⟨1221356, by rfl⟩ : syracuseStep 1628475 = 2442713) B2442713
theorem B6953363 : Blo 1626512 6953363 := bstep (se 1 (by rfl) ⟨5215022, by rfl⟩ : syracuseStep 6953363 = 10430045) B10430045
theorem B7043627 : Blo 1626512 7043627 := bstep (se 1 (by rfl) ⟨5282720, by rfl⟩ : syracuseStep 7043627 = 10565441) B10565441
theorem B4119083 : Blo 1626512 4119083 := bstep (se 1 (by rfl) ⟨3089312, by rfl⟩ : syracuseStep 4119083 = 6178625) B6178625
theorem B6265387 : Blo 1626512 6265387 := bstep (se 1 (by rfl) ⟨4699040, by rfl⟩ : syracuseStep 6265387 = 9398081) B9398081
theorem B3660407 : Blo 1626512 3660407 := bstep (se 1 (by rfl) ⟨2745305, by rfl⟩ : syracuseStep 3660407 = 5490611) B5490611
theorem B2439815 : Blo 1626512 2439815 := bstep (se 1 (by rfl) ⟨1829861, by rfl⟩ : syracuseStep 2439815 = 3659723) B3659723
theorem B2439851 : Blo 1626512 2439851 := bstep (se 1 (by rfl) ⟨1829888, by rfl⟩ : syracuseStep 2439851 = 3659777) B3659777
theorem B2439881 : Blo 1626512 2439881 := bstep (se 2 (by rfl) ⟨914955, by rfl⟩ : syracuseStep 2439881 = 1829911) B1829911
theorem B13908773 : Blo 1626512 13908773 := bstep (se 4 (by rfl) ⟨1303947, by rfl⟩ : syracuseStep 13908773 = 2607895) B2607895
theorem B3660587 : Blo 1626512 3660587 := bstep (se 1 (by rfl) ⟨2745440, by rfl⟩ : syracuseStep 3660587 = 5490881) B5490881
theorem B2439995 : Blo 1626512 2439995 := bstep (se 1 (by rfl) ⟨1829996, by rfl⟩ : syracuseStep 2439995 = 3659993) B3659993
theorem B10427251 : Blo 1626512 10427251 := bstep (se 1 (by rfl) ⟨7820438, by rfl⟩ : syracuseStep 10427251 = 15640877) B15640877
theorem B2440055 : Blo 1626512 2440055 := bstep (se 1 (by rfl) ⟨1830041, by rfl⟩ : syracuseStep 2440055 = 3660083) B3660083
theorem B5495687 : Blo 1626512 5495687 := bstep (se 1 (by rfl) ⟨4121765, by rfl⟩ : syracuseStep 5495687 = 8243531) B8243531
theorem B2440079 : Blo 1626512 2440079 := bstep (se 1 (by rfl) ⟨1830059, by rfl⟩ : syracuseStep 2440079 = 3660119) B3660119
theorem B2440121 : Blo 1626512 2440121 := bstep (se 2 (by rfl) ⟨915045, by rfl⟩ : syracuseStep 2440121 = 1830091) B1830091
theorem B2440199 : Blo 1626512 2440199 := bstep (se 1 (by rfl) ⟨1830149, by rfl⟩ : syracuseStep 2440199 = 3660299) B3660299
theorem B2440235 : Blo 1626512 2440235 := bstep (se 1 (by rfl) ⟨1830176, by rfl⟩ : syracuseStep 2440235 = 3660353) B3660353
theorem B2440265 : Blo 1626512 2440265 := bstep (se 2 (by rfl) ⟨915099, by rfl⟩ : syracuseStep 2440265 = 1830199) B1830199
theorem B3660947 : Blo 1626512 3660947 := bstep (se 1 (by rfl) ⟨2745710, by rfl⟩ : syracuseStep 3660947 = 5491421) B5491421
theorem B2440379 : Blo 1626512 2440379 := bstep (se 1 (by rfl) ⟨1830284, by rfl⟩ : syracuseStep 2440379 = 3660569) B3660569
theorem B3661001 : Blo 1626512 3661001 := bstep (se 2 (by rfl) ⟨1372875, by rfl⟩ : syracuseStep 3661001 = 2745751) B2745751
theorem B2440439 : Blo 1626512 2440439 := bstep (se 1 (by rfl) ⟨1830329, by rfl⟩ : syracuseStep 2440439 = 3660659) B3660659
theorem B5496065 : Blo 1626512 5496065 := bstep (se 2 (by rfl) ⟨2061024, by rfl⟩ : syracuseStep 5496065 = 4122049) B4122049
theorem B2440463 : Blo 1626512 2440463 := bstep (se 1 (by rfl) ⟨1830347, by rfl⟩ : syracuseStep 2440463 = 3660695) B3660695
theorem B2440505 : Blo 1626512 2440505 := bstep (se 2 (by rfl) ⟨915189, by rfl⟩ : syracuseStep 2440505 = 1830379) B1830379
theorem B4119923 : Blo 1626512 4119923 := bstep (se 1 (by rfl) ⟨3089942, by rfl⟩ : syracuseStep 4119923 = 6179885) B6179885
theorem B2440583 : Blo 1626512 2440583 := bstep (se 1 (by rfl) ⟨1830437, by rfl⟩ : syracuseStep 2440583 = 3660875) B3660875
theorem B4119943 : Blo 1626512 4119943 := bstep (se 1 (by rfl) ⟨3089957, by rfl⟩ : syracuseStep 4119943 = 6179915) B6179915
theorem B2440619 : Blo 1626512 2440619 := bstep (se 1 (by rfl) ⟨1830464, by rfl⟩ : syracuseStep 2440619 = 3660929) B3660929
theorem B18529721 : Blo 1626512 18529721 := bstep (se 2 (by rfl) ⟨6948645, by rfl⟩ : syracuseStep 18529721 = 13897291) B13897291
theorem B2440649 : Blo 1626512 2440649 := bstep (se 2 (by rfl) ⟨915243, by rfl⟩ : syracuseStep 2440649 = 1830487) B1830487
theorem B6176209 : Blo 1626512 6176209 := bstep (se 2 (by rfl) ⟨2316078, by rfl⟩ : syracuseStep 6176209 = 4632157) B4632157
theorem B16080413 : Blo 1626512 16080413 := bstep (se 3 (by rfl) ⟨3015077, by rfl⟩ : syracuseStep 16080413 = 6030155) B6030155
theorem B2440763 : Blo 1626512 2440763 := bstep (se 1 (by rfl) ⟨1830572, by rfl⟩ : syracuseStep 2440763 = 3661145) B3661145
theorem B2440823 : Blo 1626512 2440823 := bstep (se 1 (by rfl) ⟨1830617, by rfl⟩ : syracuseStep 2440823 = 3661235) B3661235
theorem B2440847 : Blo 1626512 2440847 := bstep (se 1 (by rfl) ⟨1830635, by rfl⟩ : syracuseStep 2440847 = 3661271) B3661271
theorem B4120217 : Blo 1626512 4120217 := bstep (se 2 (by rfl) ⟨1545081, by rfl⟩ : syracuseStep 4120217 = 3090163) B3090163
theorem B2440889 : Blo 1626512 2440889 := bstep (se 2 (by rfl) ⟨915333, by rfl⟩ : syracuseStep 2440889 = 1830667) B1830667
theorem B12361409 : Blo 1626512 12361409 := bstep (se 2 (by rfl) ⟨4635528, by rfl⟩ : syracuseStep 12361409 = 9271057) B9271057
theorem B9895625 : Blo 1626512 9895625 := bstep (se 2 (by rfl) ⟨3710859, by rfl⟩ : syracuseStep 9895625 = 7421719) B7421719
theorem B6176513 : Blo 1626512 6176513 := bstep (se 2 (by rfl) ⟨2316192, by rfl⟩ : syracuseStep 6176513 = 4632385) B4632385
theorem B2440967 : Blo 1626512 2440967 := bstep (se 1 (by rfl) ⟨1830725, by rfl⟩ : syracuseStep 2440967 = 3661451) B3661451
theorem B2318095 : Blo 1626512 2318095 := bstep (se 1 (by rfl) ⟨1738571, by rfl⟩ : syracuseStep 2318095 = 3477143) B3477143
theorem B2441003 : Blo 1626512 2441003 := bstep (se 1 (by rfl) ⟨1830752, by rfl⟩ : syracuseStep 2441003 = 3661505) B3661505
theorem B4120379 : Blo 1626512 4120379 := bstep (se 1 (by rfl) ⟨3090284, by rfl⟩ : syracuseStep 4120379 = 6180569) B6180569
theorem B2441033 : Blo 1626512 2441033 := bstep (se 2 (by rfl) ⟨915387, by rfl⟩ : syracuseStep 2441033 = 1830775) B1830775
theorem B4636531 : Blo 1626512 4636531 := bstep (se 1 (by rfl) ⟨3477398, by rfl⟩ : syracuseStep 4636531 = 6954797) B6954797
theorem B3661703 : Blo 1626512 3661703 := bstep (se 1 (by rfl) ⟨2746277, by rfl⟩ : syracuseStep 3661703 = 5492555) B5492555
theorem B2318215 : Blo 1626512 2318215 := bstep (se 1 (by rfl) ⟨1738661, by rfl⟩ : syracuseStep 2318215 = 3477323) B3477323
theorem B9265043 : Blo 1626512 9265043 := bstep (se 1 (by rfl) ⟨6948782, by rfl⟩ : syracuseStep 9265043 = 13897565) B13897565
theorem B2441147 : Blo 1626512 2441147 := bstep (se 1 (by rfl) ⟨1830860, by rfl⟩ : syracuseStep 2441147 = 3661721) B3661721
theorem B2441207 : Blo 1626512 2441207 := bstep (se 1 (by rfl) ⟨1830905, by rfl⟩ : syracuseStep 2441207 = 3661811) B3661811
theorem B2441225 : Blo 1626512 2441225 := bstep (se 2 (by rfl) ⟨915459, by rfl⟩ : syracuseStep 2441225 = 1830919) B1830919
theorem B2441255 : Blo 1626512 2441255 := bstep (se 1 (by rfl) ⟨1830941, by rfl⟩ : syracuseStep 2441255 = 3661883) B3661883
theorem B13205585 : Blo 1626512 13205585 := bstep (se 2 (by rfl) ⟨4952094, by rfl⟩ : syracuseStep 13205585 = 9904189) B9904189
theorem B13901939 : Blo 1626512 13901939 := bstep (se 1 (by rfl) ⟨10426454, by rfl⟩ : syracuseStep 13901939 = 20852909) B20852909
theorem B2441339 : Blo 1626512 2441339 := bstep (se 1 (by rfl) ⟨1831004, by rfl⟩ : syracuseStep 2441339 = 3662009) B3662009
theorem B4636919 : Blo 1626512 4636919 := bstep (se 1 (by rfl) ⟨3477689, by rfl⟩ : syracuseStep 4636919 = 6955379) B6955379
theorem B2441465 : Blo 1626512 2441465 := bstep (se 2 (by rfl) ⟨915549, by rfl⟩ : syracuseStep 2441465 = 1831099) B1831099
theorem B171524405 : Blo 1626512 171524405 := bstep (se 5 (by rfl) ⟨8040206, by rfl⟩ : syracuseStep 171524405 = 16080413) B16080413
theorem B1737055 : Blo 1626512 1737055 := bstep (se 1 (by rfl) ⟨1302791, by rfl⟩ : syracuseStep 1737055 = 2605583) B2605583
theorem B2441567 : Blo 1626512 2441567 := bstep (se 1 (by rfl) ⟨1831175, by rfl⟩ : syracuseStep 2441567 = 3662351) B3662351
theorem B4637033 : Blo 1626512 4637033 := bstep (se 2 (by rfl) ⟨1738887, by rfl⟩ : syracuseStep 4637033 = 3477775) B3477775
theorem B2441579 : Blo 1626512 2441579 := bstep (se 1 (by rfl) ⟨1831184, by rfl⟩ : syracuseStep 2441579 = 3662369) B3662369
theorem B6177167 : Blo 1626512 6177167 := bstep (se 1 (by rfl) ⟨4632875, by rfl⟩ : syracuseStep 6177167 = 9265751) B9265751
theorem B2744759 : Blo 1626512 2744759 := bstep (se 1 (by rfl) ⟨2058569, by rfl⟩ : syracuseStep 2744759 = 4117139) B4117139
theorem B2441807 : Blo 1626512 2441807 := bstep (se 1 (by rfl) ⟨1831355, by rfl⟩ : syracuseStep 2441807 = 3662711) B3662711
theorem B3662459 : Blo 1626512 3662459 := bstep (se 1 (by rfl) ⟨2746844, by rfl⟩ : syracuseStep 3662459 = 5493689) B5493689
theorem B2441927 : Blo 1626512 2441927 := bstep (se 1 (by rfl) ⟨1831445, by rfl⟩ : syracuseStep 2441927 = 3662891) B3662891
theorem B3089107 : Blo 1626512 3089107 := bstep (se 1 (by rfl) ⟨2316830, by rfl⟩ : syracuseStep 3089107 = 4633661) B4633661
theorem B3662585 : Blo 1626512 3662585 := bstep (se 2 (by rfl) ⟨1373469, by rfl⟩ : syracuseStep 3662585 = 2746939) B2746939
theorem B2442089 : Blo 1626512 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B18531179 : Blo 1626512 18531179 := bstep (se 1 (by rfl) ⟨13898384, by rfl⟩ : syracuseStep 18531179 = 27796769) B27796769
theorem B5210999 : Blo 1626512 5210999 := bstep (se 1 (by rfl) ⟨3908249, by rfl⟩ : syracuseStep 5210999 = 7816499) B7816499
theorem B50111381 : Blo 1626512 50111381 := bstep (se 6 (by rfl) ⟨1174485, by rfl⟩ : syracuseStep 50111381 = 2348971) B2348971
theorem B2605999 : Blo 1626512 2605999 := bstep (se 1 (by rfl) ⟨1954499, by rfl⟩ : syracuseStep 2605999 = 3908999) B3908999
theorem B3089335 : Blo 1626512 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B2442167 : Blo 1626512 2442167 := bstep (se 1 (by rfl) ⟨1831625, by rfl⟩ : syracuseStep 2442167 = 3663251) B3663251
theorem B53527499 : Blo 1626512 53527499 := bstep (se 1 (by rfl) ⟨40145624, by rfl⟩ : syracuseStep 53527499 = 80291249) B80291249
theorem B2442203 : Blo 1626512 2442203 := bstep (se 1 (by rfl) ⟨1831652, by rfl⟩ : syracuseStep 2442203 = 3663305) B3663305
theorem B3662855 : Blo 1626512 3662855 := bstep (se 1 (by rfl) ⟨2747141, by rfl⟩ : syracuseStep 3662855 = 5494283) B5494283
theorem B2745353 : Blo 1626512 2745353 := bstep (se 2 (by rfl) ⟨1029507, by rfl⟩ : syracuseStep 2745353 = 2059015) B2059015
theorem B2933767 : Blo 1626512 2933767 := bstep (se 1 (by rfl) ⟨2200325, by rfl⟩ : syracuseStep 2933767 = 4400651) B4400651
theorem B3662927 : Blo 1626512 3662927 := bstep (se 1 (by rfl) ⟨2747195, by rfl⟩ : syracuseStep 3662927 = 5494391) B5494391
theorem B13903001 : Blo 1626512 13903001 := bstep (se 2 (by rfl) ⟨5213625, by rfl⟩ : syracuseStep 13903001 = 10427251) B10427251
theorem B2745515 : Blo 1626512 2745515 := bstep (se 1 (by rfl) ⟨2059136, by rfl⟩ : syracuseStep 2745515 = 4118273) B4118273
theorem B6178153 : Blo 1626512 6178153 := bstep (se 2 (by rfl) ⟨2316807, by rfl⟩ : syracuseStep 6178153 = 4633615) B4633615
theorem B4121999 : Blo 1626512 4121999 := bstep (se 1 (by rfl) ⟨3091499, by rfl⟩ : syracuseStep 4121999 = 6182999) B6182999
theorem B2442671 : Blo 1626512 2442671 := bstep (se 1 (by rfl) ⟨1832003, by rfl⟩ : syracuseStep 2442671 = 3664007) B3664007
theorem B8234459 : Blo 1626512 8234459 := bstep (se 1 (by rfl) ⟨6175844, by rfl⟩ : syracuseStep 8234459 = 12351689) B12351689
theorem B3663323 : Blo 1626512 3663323 := bstep (se 1 (by rfl) ⟨2747492, by rfl⟩ : syracuseStep 3663323 = 5494985) B5494985
theorem B3089927 : Blo 1626512 3089927 := bstep (se 1 (by rfl) ⟨2317445, by rfl⟩ : syracuseStep 3089927 = 4634891) B4634891
theorem B2442761 : Blo 1626512 2442761 := bstep (se 2 (by rfl) ⟨916035, by rfl⟩ : syracuseStep 2442761 = 1832071) B1832071
theorem B2745913 : Blo 1626512 2745913 := bstep (se 2 (by rfl) ⟨1029717, by rfl⟩ : syracuseStep 2745913 = 2059435) B2059435
theorem B6178427 : Blo 1626512 6178427 := bstep (se 1 (by rfl) ⟨4633820, by rfl⟩ : syracuseStep 6178427 = 9267641) B9267641
theorem B4695751 : Blo 1626512 4695751 := bstep (se 1 (by rfl) ⟨3521813, by rfl⟩ : syracuseStep 4695751 = 7043627) B7043627
theorem B2746055 : Blo 1626512 2746055 := bstep (se 1 (by rfl) ⟨2059541, by rfl⟩ : syracuseStep 2746055 = 4119083) B4119083
theorem B2746217 : Blo 1626512 2746217 := bstep (se 2 (by rfl) ⟨1029831, by rfl⟩ : syracuseStep 2746217 = 2059663) B2059663
theorem B3663791 : Blo 1626512 3663791 := bstep (se 1 (by rfl) ⟨2747843, by rfl⟩ : syracuseStep 3663791 = 5495687) B5495687
theorem B8234945 : Blo 1626512 8234945 := bstep (se 2 (by rfl) ⟨3088104, by rfl⟩ : syracuseStep 8234945 = 6176209) B6176209
theorem B8243207 : Blo 1626512 8243207 := bstep (se 1 (by rfl) ⟨6182405, by rfl⟩ : syracuseStep 8243207 = 12364811) B12364811
theorem B3664043 : Blo 1626512 3664043 := bstep (se 1 (by rfl) ⟨2748032, by rfl⟩ : syracuseStep 3664043 = 5496065) B5496065
theorem B11733221 : Blo 1626512 11733221 := bstep (se 4 (by rfl) ⟨1099989, by rfl⟩ : syracuseStep 11733221 = 2199979) B2199979
theorem B5490935 : Blo 1626512 5490935 := bstep (se 1 (by rfl) ⟨4118201, by rfl⟩ : syracuseStep 5490935 = 8236403) B8236403
theorem B2746615 : Blo 1626512 2746615 := bstep (se 1 (by rfl) ⟨2059961, by rfl⟩ : syracuseStep 2746615 = 4119923) B4119923
theorem B3090793 : Blo 1626512 3090793 := bstep (se 2 (by rfl) ⟨1159047, by rfl⟩ : syracuseStep 3090793 = 2318095) B2318095
theorem B2746811 : Blo 1626512 2746811 := bstep (se 1 (by rfl) ⟨2060108, by rfl⟩ : syracuseStep 2746811 = 4120217) B4120217
theorem B6597083 : Blo 1626512 6597083 := bstep (se 1 (by rfl) ⟨4947812, by rfl⟩ : syracuseStep 6597083 = 9895625) B9895625
theorem B8243693 : Blo 1626512 8243693 := bstep (se 3 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 8243693 = 3091385) B3091385
theorem B3090953 : Blo 1626512 3090953 := bstep (se 2 (by rfl) ⟨1159107, by rfl⟩ : syracuseStep 3090953 = 2318215) B2318215
theorem B2746919 : Blo 1626512 2746919 := bstep (se 1 (by rfl) ⟨2060189, by rfl⟩ : syracuseStep 2746919 = 4120379) B4120379
theorem B5491259 : Blo 1626512 5491259 := bstep (se 1 (by rfl) ⟨4118444, by rfl⟩ : syracuseStep 5491259 = 8236889) B8236889
theorem B5491529 : Blo 1626512 5491529 := bstep (se 2 (by rfl) ⟨2059323, by rfl⟩ : syracuseStep 5491529 = 4118647) B4118647
theorem B3476297 : Blo 1626512 3476297 := bstep (se 2 (by rfl) ⟨1303611, by rfl⟩ : syracuseStep 3476297 = 2607223) B2607223
theorem B2747209 : Blo 1626512 2747209 := bstep (se 2 (by rfl) ⟨1030203, by rfl⟩ : syracuseStep 2747209 = 2060407) B2060407
theorem B6949739 : Blo 1626512 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B2747243 : Blo 1626512 2747243 := bstep (se 1 (by rfl) ⟨2060432, by rfl⟩ : syracuseStep 2747243 = 4120865) B4120865
theorem B1649531 : Blo 1626512 1649531 := bstep (se 1 (by rfl) ⟨1237148, by rfl⟩ : syracuseStep 1649531 = 2474297) B2474297
theorem B36162449 : Blo 1626512 36162449 := bstep (se 2 (by rfl) ⟨13560918, by rfl⟩ : syracuseStep 36162449 = 27121837) B27121837
theorem B18787301 : Blo 1626512 18787301 := bstep (se 4 (by rfl) ⟨1761309, by rfl⟩ : syracuseStep 18787301 = 3522619) B3522619
theorem B61058033 : Blo 1626512 61058033 := bstep (se 2 (by rfl) ⟨22896762, by rfl⟩ : syracuseStep 61058033 = 45793525) B45793525
theorem B45755479 : Blo 1626512 45755479 := bstep (se 1 (by rfl) ⟨34316609, by rfl⟩ : syracuseStep 45755479 = 68633219) B68633219
theorem B2747641 : Blo 1626512 2747641 := bstep (se 2 (by rfl) ⟨1030365, by rfl⟩ : syracuseStep 2747641 = 2060731) B2060731
theorem B3911017 : Blo 1626512 3911017 := bstep (se 2 (by rfl) ⟨1466631, by rfl⟩ : syracuseStep 3911017 = 2933263) B2933263
theorem B4951439 : Blo 1626512 4951439 := bstep (se 1 (by rfl) ⟨3713579, by rfl⟩ : syracuseStep 4951439 = 7427159) B7427159
theorem B8793517 : Blo 1626512 8793517 := bstep (se 3 (by rfl) ⟨1648784, by rfl⟩ : syracuseStep 8793517 = 3297569) B3297569
theorem B2747911 : Blo 1626512 2747911 := bstep (se 1 (by rfl) ⟨2060933, by rfl⟩ : syracuseStep 2747911 = 4121867) B4121867
theorem B1830523 : Blo 1626512 1830523 := bstep (se 1 (by rfl) ⟨1372892, by rfl⟩ : syracuseStep 1830523 = 2745785) B2745785
theorem B4632203 : Blo 1626512 4632203 := bstep (se 1 (by rfl) ⟨3474152, by rfl⟩ : syracuseStep 4632203 = 6948305) B6948305
theorem B4173527 : Blo 1626512 4173527 := bstep (se 1 (by rfl) ⟨3130145, by rfl⟩ : syracuseStep 4173527 = 6260291) B6260291
theorem B5213945 : Blo 1626512 5213945 := bstep (se 2 (by rfl) ⟨1955229, by rfl⟩ : syracuseStep 5213945 = 3910459) B3910459
theorem B6950765 : Blo 1626512 6950765 := bstep (se 3 (by rfl) ⟨1303268, by rfl⟩ : syracuseStep 6950765 = 2606537) B2606537
theorem B5492663 : Blo 1626512 5492663 := bstep (se 1 (by rfl) ⟨4119497, by rfl⟩ : syracuseStep 5492663 = 8238995) B8238995
theorem B6598675 : Blo 1626512 6598675 := bstep (se 1 (by rfl) ⟨4949006, by rfl⟩ : syracuseStep 6598675 = 9898013) B9898013
theorem B8802341 : Blo 1626512 8802341 := bstep (se 4 (by rfl) ⟨825219, by rfl⟩ : syracuseStep 8802341 = 1650439) B1650439
theorem B1830991 : Blo 1626512 1830991 := bstep (se 1 (by rfl) ⟨1373243, by rfl⟩ : syracuseStep 1830991 = 2746487) B2746487
theorem B8237213 : Blo 1626512 8237213 := bstep (se 3 (by rfl) ⟨1544477, by rfl⟩ : syracuseStep 8237213 = 3088955) B3088955
theorem B4698359 : Blo 1626512 4698359 := bstep (se 1 (by rfl) ⟨3523769, by rfl⟩ : syracuseStep 4698359 = 7047539) B7047539
theorem B3912065 : Blo 1626512 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B1626543 : Blo 1626512 1626543 := bstep (se 1 (by rfl) ⟨1219907, by rfl⟩ : syracuseStep 1626543 = 2439815) B2439815
theorem B1626567 : Blo 1626512 1626567 := bstep (se 1 (by rfl) ⟨1219925, by rfl⟩ : syracuseStep 1626567 = 2439851) B2439851
theorem B1626587 : Blo 1626512 1626587 := bstep (se 1 (by rfl) ⟨1219940, by rfl⟩ : syracuseStep 1626587 = 2439881) B2439881
theorem B1831387 : Blo 1626512 1831387 := bstep (se 1 (by rfl) ⟨1373540, by rfl⟩ : syracuseStep 1831387 = 2747081) B2747081
theorem B13898249 : Blo 1626512 13898249 := bstep (se 2 (by rfl) ⟨5211843, by rfl⟩ : syracuseStep 13898249 = 10423687) B10423687
theorem B5493257 : Blo 1626512 5493257 := bstep (se 2 (by rfl) ⟨2059971, by rfl⟩ : syracuseStep 5493257 = 4119943) B4119943
theorem B1626663 : Blo 1626512 1626663 := bstep (se 1 (by rfl) ⟨1219997, by rfl⟩ : syracuseStep 1626663 = 2439995) B2439995
theorem B6599227 : Blo 1626512 6599227 := bstep (se 1 (by rfl) ⟨4949420, by rfl⟩ : syracuseStep 6599227 = 9898841) B9898841
theorem B1626703 : Blo 1626512 1626703 := bstep (se 1 (by rfl) ⟨1220027, by rfl⟩ : syracuseStep 1626703 = 2440055) B2440055
theorem B1626719 : Blo 1626512 1626719 := bstep (se 1 (by rfl) ⟨1220039, by rfl⟩ : syracuseStep 1626719 = 2440079) B2440079
theorem B1626747 : Blo 1626512 1626747 := bstep (se 1 (by rfl) ⟨1220060, by rfl⟩ : syracuseStep 1626747 = 2440121) B2440121
theorem B1626799 : Blo 1626512 1626799 := bstep (se 1 (by rfl) ⟨1220099, by rfl⟩ : syracuseStep 1626799 = 2440199) B2440199
theorem B6689465 : Blo 1626512 6689465 := bstep (se 2 (by rfl) ⟨2508549, by rfl⟩ : syracuseStep 6689465 = 5017099) B5017099
theorem B1626823 : Blo 1626512 1626823 := bstep (se 1 (by rfl) ⟨1220117, by rfl⟩ : syracuseStep 1626823 = 2440235) B2440235
theorem B1626843 : Blo 1626512 1626843 := bstep (se 1 (by rfl) ⟨1220132, by rfl⟩ : syracuseStep 1626843 = 2440265) B2440265
theorem B8917789 : Blo 1626512 8917789 := bstep (se 3 (by rfl) ⟨1672085, by rfl⟩ : syracuseStep 8917789 = 3344171) B3344171
theorem B1626919 : Blo 1626512 1626919 := bstep (se 1 (by rfl) ⟨1220189, by rfl⟩ : syracuseStep 1626919 = 2440379) B2440379
theorem B5567305 : Blo 1626512 5567305 := bstep (se 2 (by rfl) ⟨2087739, by rfl⟩ : syracuseStep 5567305 = 4175479) B4175479
theorem B1626959 : Blo 1626512 1626959 := bstep (se 1 (by rfl) ⟨1220219, by rfl⟩ : syracuseStep 1626959 = 2440439) B2440439
theorem B1626975 : Blo 1626512 1626975 := bstep (se 1 (by rfl) ⟨1220231, by rfl⟩ : syracuseStep 1626975 = 2440463) B2440463
theorem B1627003 : Blo 1626512 1627003 := bstep (se 1 (by rfl) ⟨1220252, by rfl⟩ : syracuseStep 1627003 = 2440505) B2440505
theorem B23466905 : Blo 1626512 23466905 := bstep (se 2 (by rfl) ⟨8800089, by rfl⟩ : syracuseStep 23466905 = 17600179) B17600179
theorem B1627055 : Blo 1626512 1627055 := bstep (se 1 (by rfl) ⟨1220291, by rfl⟩ : syracuseStep 1627055 = 2440583) B2440583
theorem B1831855 : Blo 1626512 1831855 := bstep (se 1 (by rfl) ⟨1373891, by rfl⟩ : syracuseStep 1831855 = 2747783) B2747783
theorem B1627079 : Blo 1626512 1627079 := bstep (se 1 (by rfl) ⟨1220309, by rfl⟩ : syracuseStep 1627079 = 2440619) B2440619
theorem B1627099 : Blo 1626512 1627099 := bstep (se 1 (by rfl) ⟨1220324, by rfl⟩ : syracuseStep 1627099 = 2440649) B2440649
theorem B1627175 : Blo 1626512 1627175 := bstep (se 1 (by rfl) ⟨1220381, by rfl⟩ : syracuseStep 1627175 = 2440763) B2440763
theorem B1627215 : Blo 1626512 1627215 := bstep (se 1 (by rfl) ⟨1220411, by rfl⟩ : syracuseStep 1627215 = 2440823) B2440823
theorem B1627231 : Blo 1626512 1627231 := bstep (se 1 (by rfl) ⟨1220423, by rfl⟩ : syracuseStep 1627231 = 2440847) B2440847
theorem B1627259 : Blo 1626512 1627259 := bstep (se 1 (by rfl) ⟨1220444, by rfl⟩ : syracuseStep 1627259 = 2440889) B2440889
theorem B6182041 : Blo 1626512 6182041 := bstep (se 2 (by rfl) ⟨2318265, by rfl⟩ : syracuseStep 6182041 = 4636531) B4636531
theorem B4117675 : Blo 1626512 4117675 := bstep (se 1 (by rfl) ⟨3088256, by rfl⟩ : syracuseStep 4117675 = 6176513) B6176513
theorem B1627311 : Blo 1626512 1627311 := bstep (se 1 (by rfl) ⟨1220483, by rfl⟩ : syracuseStep 1627311 = 2440967) B2440967
theorem B1627335 : Blo 1626512 1627335 := bstep (se 1 (by rfl) ⟨1220501, by rfl⟩ : syracuseStep 1627335 = 2441003) B2441003
theorem B1627355 : Blo 1626512 1627355 := bstep (se 1 (by rfl) ⟨1220516, by rfl⟩ : syracuseStep 1627355 = 2441033) B2441033
theorem B14841103 : Blo 1626512 14841103 := bstep (se 1 (by rfl) ⟨11130827, by rfl⟩ : syracuseStep 14841103 = 22261655) B22261655
theorem B11130149 : Blo 1626512 11130149 := bstep (se 4 (by rfl) ⟨1043451, by rfl⟩ : syracuseStep 11130149 = 2086903) B2086903
theorem B1627431 : Blo 1626512 1627431 := bstep (se 1 (by rfl) ⟨1220573, by rfl⟩ : syracuseStep 1627431 = 2441147) B2441147
theorem B1627471 : Blo 1626512 1627471 := bstep (se 1 (by rfl) ⟨1220603, by rfl⟩ : syracuseStep 1627471 = 2441207) B2441207
theorem B1627487 : Blo 1626512 1627487 := bstep (se 1 (by rfl) ⟨1220615, by rfl⟩ : syracuseStep 1627487 = 2441231) B2441231
theorem B5494121 : Blo 1626512 5494121 := bstep (se 2 (by rfl) ⟨2060295, by rfl⟩ : syracuseStep 5494121 = 4120591) B4120591
theorem B1627515 : Blo 1626512 1627515 := bstep (se 1 (by rfl) ⟨1220636, by rfl⟩ : syracuseStep 1627515 = 2441273) B2441273
theorem B8238509 : Blo 1626512 8238509 := bstep (se 3 (by rfl) ⟨1544720, by rfl⟩ : syracuseStep 8238509 = 3089441) B3089441
theorem B1627567 : Blo 1626512 1627567 := bstep (se 1 (by rfl) ⟨1220675, by rfl⟩ : syracuseStep 1627567 = 2441351) B2441351
theorem B1627591 : Blo 1626512 1627591 := bstep (se 1 (by rfl) ⟨1220693, by rfl⟩ : syracuseStep 1627591 = 2441387) B2441387
theorem B6182345 : Blo 1626512 6182345 := bstep (se 2 (by rfl) ⟨2318379, by rfl⟩ : syracuseStep 6182345 = 4636759) B4636759
theorem B4117979 : Blo 1626512 4117979 := bstep (se 1 (by rfl) ⟨3088484, by rfl⟩ : syracuseStep 4117979 = 6176969) B6176969
theorem B1627611 : Blo 1626512 1627611 := bstep (se 1 (by rfl) ⟨1220708, by rfl⟩ : syracuseStep 1627611 = 2441417) B2441417
theorem B13899275 : Blo 1626512 13899275 := bstep (se 1 (by rfl) ⟨10424456, by rfl⟩ : syracuseStep 13899275 = 20848913) B20848913
theorem B1627687 : Blo 1626512 1627687 := bstep (se 1 (by rfl) ⟨1220765, by rfl⟩ : syracuseStep 1627687 = 2441531) B2441531
theorem B1627727 : Blo 1626512 1627727 := bstep (se 1 (by rfl) ⟨1220795, by rfl⟩ : syracuseStep 1627727 = 2441591) B2441591
theorem B1627743 : Blo 1626512 1627743 := bstep (se 1 (by rfl) ⟨1220807, by rfl⟩ : syracuseStep 1627743 = 2441615) B2441615
theorem B1627771 : Blo 1626512 1627771 := bstep (se 1 (by rfl) ⟨1220828, by rfl⟩ : syracuseStep 1627771 = 2441657) B2441657
theorem B3176059 : Blo 1626512 3176059 := bstep (se 1 (by rfl) ⟨2382044, by rfl⟩ : syracuseStep 3176059 = 4764089) B4764089
theorem B1627823 : Blo 1626512 1627823 := bstep (se 1 (by rfl) ⟨1220867, by rfl⟩ : syracuseStep 1627823 = 2441735) B2441735
theorem B28169927 : Blo 1626512 28169927 := bstep (se 1 (by rfl) ⟨21127445, by rfl⟩ : syracuseStep 28169927 = 42254891) B42254891
theorem B1627847 : Blo 1626512 1627847 := bstep (se 1 (by rfl) ⟨1220885, by rfl⟩ : syracuseStep 1627847 = 2441771) B2441771
theorem B11130583 : Blo 1626512 11130583 := bstep (se 1 (by rfl) ⟨8347937, by rfl⟩ : syracuseStep 11130583 = 16695875) B16695875
theorem B1627867 : Blo 1626512 1627867 := bstep (se 1 (by rfl) ⟨1220900, by rfl⟩ : syracuseStep 1627867 = 2441801) B2441801
theorem B1627943 : Blo 1626512 1627943 := bstep (se 1 (by rfl) ⟨1220957, by rfl⟩ : syracuseStep 1627943 = 2441915) B2441915
theorem B5863211 : Blo 1626512 5863211 := bstep (se 1 (by rfl) ⟨4397408, by rfl⟩ : syracuseStep 5863211 = 8794817) B8794817
theorem B1627983 : Blo 1626512 1627983 := bstep (se 1 (by rfl) ⟨1220987, by rfl⟩ : syracuseStep 1627983 = 2441975) B2441975
theorem B1627999 : Blo 1626512 1627999 := bstep (se 1 (by rfl) ⟨1220999, by rfl⟩ : syracuseStep 1627999 = 2441999) B2441999
theorem B1628027 : Blo 1626512 1628027 := bstep (se 1 (by rfl) ⟨1221020, by rfl⟩ : syracuseStep 1628027 = 2442041) B2442041
theorem B1628079 : Blo 1626512 1628079 := bstep (se 1 (by rfl) ⟨1221059, by rfl⟩ : syracuseStep 1628079 = 2442119) B2442119
theorem B6182831 : Blo 1626512 6182831 := bstep (se 1 (by rfl) ⟨4637123, by rfl⟩ : syracuseStep 6182831 = 9274247) B9274247
theorem B5494715 : Blo 1626512 5494715 := bstep (se 1 (by rfl) ⟨4121036, by rfl⟩ : syracuseStep 5494715 = 8242073) B8242073
theorem B1628103 : Blo 1626512 1628103 := bstep (se 1 (by rfl) ⟨1221077, by rfl⟩ : syracuseStep 1628103 = 2442155) B2442155
theorem B1628123 : Blo 1626512 1628123 := bstep (se 1 (by rfl) ⟨1221092, by rfl⟩ : syracuseStep 1628123 = 2442185) B2442185
theorem B18528263 : Blo 1626512 18528263 := bstep (se 1 (by rfl) ⟨13896197, by rfl⟩ : syracuseStep 18528263 = 27792395) B27792395
theorem B3659795 : Blo 1626512 3659795 := bstep (se 1 (by rfl) ⟨2744846, by rfl⟩ : syracuseStep 3659795 = 5489693) B5489693
theorem B1628199 : Blo 1626512 1628199 := bstep (se 1 (by rfl) ⟨1221149, by rfl⟩ : syracuseStep 1628199 = 2442299) B2442299
theorem B8353849 : Blo 1626512 8353849 := bstep (se 2 (by rfl) ⟨3132693, by rfl⟩ : syracuseStep 8353849 = 6265387) B6265387
theorem B1628239 : Blo 1626512 1628239 := bstep (se 1 (by rfl) ⟨1221179, by rfl⟩ : syracuseStep 1628239 = 2442359) B2442359
theorem B37591127 : Blo 1626512 37591127 := bstep (se 1 (by rfl) ⟨28193345, by rfl⟩ : syracuseStep 37591127 = 56386691) B56386691
theorem B1628255 : Blo 1626512 1628255 := bstep (se 1 (by rfl) ⟨1221191, by rfl⟩ : syracuseStep 1628255 = 2442383) B2442383
theorem B1628283 : Blo 1626512 1628283 := bstep (se 1 (by rfl) ⟨1221212, by rfl⟩ : syracuseStep 1628283 = 2442425) B2442425
theorem B6690973 : Blo 1626512 6690973 := bstep (se 3 (by rfl) ⟨1254557, by rfl⟩ : syracuseStep 6690973 = 2509115) B2509115
theorem B1628335 : Blo 1626512 1628335 := bstep (se 1 (by rfl) ⟨1221251, by rfl⟩ : syracuseStep 1628335 = 2442503) B2442503
theorem B1628359 : Blo 1626512 1628359 := bstep (se 1 (by rfl) ⟨1221269, by rfl⟩ : syracuseStep 1628359 = 2442539) B2442539
theorem B1628379 : Blo 1626512 1628379 := bstep (se 1 (by rfl) ⟨1221284, by rfl⟩ : syracuseStep 1628379 = 2442569) B2442569
theorem B1628455 : Blo 1626512 1628455 := bstep (se 1 (by rfl) ⟨1221341, by rfl⟩ : syracuseStep 1628455 = 2442683) B2442683
theorem B1628495 : Blo 1626512 1628495 := bstep (se 1 (by rfl) ⟨1221371, by rfl⟩ : syracuseStep 1628495 = 2442743) B2442743
theorem B1628511 : Blo 1626512 1628511 := bstep (se 1 (by rfl) ⟨1221383, by rfl⟩ : syracuseStep 1628511 = 2442767) B2442767
theorem B3660137 : Blo 1626512 3660137 := bstep (se 2 (by rfl) ⟨1372551, by rfl⟩ : syracuseStep 3660137 = 2745103) B2745103
theorem B13195723 : Blo 1626512 13195723 := bstep (se 1 (by rfl) ⟨9896792, by rfl⟩ : syracuseStep 13195723 = 19793585) B19793585
theorem B14842349 : Blo 1626512 14842349 := bstep (se 3 (by rfl) ⟨2782940, by rfl⟩ : syracuseStep 14842349 = 5565881) B5565881
theorem B31717963 : Blo 1626512 31717963 := bstep (se 1 (by rfl) ⟨23788472, by rfl⟩ : syracuseStep 31717963 = 47576945) B47576945
theorem B2439803 : Blo 1626512 2439803 := bstep (se 1 (by rfl) ⟨1829852, by rfl⟩ : syracuseStep 2439803 = 3659705) B3659705
theorem B11737811 : Blo 1626512 11737811 := bstep (se 1 (by rfl) ⟨8803358, by rfl⟩ : syracuseStep 11737811 = 17606717) B17606717
theorem B2439929 : Blo 1626512 2439929 := bstep (se 2 (by rfl) ⟨914973, by rfl⟩ : syracuseStep 2439929 = 1829947) B1829947
theorem B2440031 : Blo 1626512 2440031 := bstep (se 1 (by rfl) ⟨1830023, by rfl⟩ : syracuseStep 2440031 = 3660047) B3660047
theorem B2440043 : Blo 1626512 2440043 := bstep (se 1 (by rfl) ⟨1830032, by rfl⟩ : syracuseStep 2440043 = 3660065) B3660065
theorem B4119457 : Blo 1626512 4119457 := bstep (se 2 (by rfl) ⟨1544796, by rfl⟩ : syracuseStep 4119457 = 3089593) B3089593
theorem B4635575 : Blo 1626512 4635575 := bstep (se 1 (by rfl) ⟨3476681, by rfl⟩ : syracuseStep 4635575 = 6953363) B6953363
theorem B3660731 : Blo 1626512 3660731 := bstep (se 1 (by rfl) ⟨2745548, by rfl⟩ : syracuseStep 3660731 = 5491097) B5491097
theorem B8240129 : Blo 1626512 8240129 := bstep (se 2 (by rfl) ⟨3090048, by rfl⟩ : syracuseStep 8240129 = 6180097) B6180097
theorem B3660857 : Blo 1626512 3660857 := bstep (se 2 (by rfl) ⟨1372821, by rfl⟩ : syracuseStep 3660857 = 2745643) B2745643
theorem B2440271 : Blo 1626512 2440271 := bstep (se 1 (by rfl) ⟨1830203, by rfl⟩ : syracuseStep 2440271 = 3660407) B3660407
theorem B9272515 : Blo 1626512 9272515 := bstep (se 1 (by rfl) ⟨6954386, by rfl⟩ : syracuseStep 9272515 = 13908773) B13908773
theorem B2440391 : Blo 1626512 2440391 := bstep (se 1 (by rfl) ⟨1830293, by rfl⟩ : syracuseStep 2440391 = 3660587) B3660587
theorem B10427737 : Blo 1626512 10427737 := bstep (se 2 (by rfl) ⟨3910401, by rfl⟩ : syracuseStep 10427737 = 7820803) B7820803
theorem B2440553 : Blo 1626512 2440553 := bstep (se 2 (by rfl) ⟨915207, by rfl⟩ : syracuseStep 2440553 = 1830415) B1830415
theorem B3661199 : Blo 1626512 3661199 := bstep (se 1 (by rfl) ⟨2745899, by rfl⟩ : syracuseStep 3661199 = 5491799) B5491799
theorem B4398479 : Blo 1626512 4398479 := bstep (se 1 (by rfl) ⟨3298859, by rfl⟩ : syracuseStep 4398479 = 6597719) B6597719
theorem B17603983 : Blo 1626512 17603983 := bstep (se 1 (by rfl) ⟨13202987, by rfl⟩ : syracuseStep 17603983 = 26405975) B26405975
theorem B2440631 : Blo 1626512 2440631 := bstep (se 1 (by rfl) ⟨1830473, by rfl⟩ : syracuseStep 2440631 = 3660947) B3660947
theorem B2440667 : Blo 1626512 2440667 := bstep (se 1 (by rfl) ⟨1830500, by rfl⟩ : syracuseStep 2440667 = 3661001) B3661001
theorem B12353147 : Blo 1626512 12353147 := bstep (se 1 (by rfl) ⟨9264860, by rfl⟩ : syracuseStep 12353147 = 18529721) B18529721
theorem B8797841 : Blo 1626512 8797841 := bstep (se 2 (by rfl) ⟨3299190, by rfl⟩ : syracuseStep 8797841 = 6598381) B6598381
theorem B4636349 : Blo 1626512 4636349 := bstep (se 3 (by rfl) ⟨869315, by rfl⟩ : syracuseStep 4636349 = 1738631) B1738631
theorem B3661523 : Blo 1626512 3661523 := bstep (se 1 (by rfl) ⟨2746142, by rfl⟩ : syracuseStep 3661523 = 5492285) B5492285
theorem B8240939 : Blo 1626512 8240939 := bstep (se 1 (by rfl) ⟨6180704, by rfl⟩ : syracuseStep 8240939 = 12361409) B12361409
theorem B4636577 : Blo 1626512 4636577 := bstep (se 2 (by rfl) ⟨1738716, by rfl⟩ : syracuseStep 4636577 = 3477433) B3477433
theorem B2441135 : Blo 1626512 2441135 := bstep (se 1 (by rfl) ⟨1830851, by rfl⟩ : syracuseStep 2441135 = 3661703) B3661703
theorem B6176695 : Blo 1626512 6176695 := bstep (se 1 (by rfl) ⟨4632521, by rfl⟩ : syracuseStep 6176695 = 9265043) B9265043
theorem B101638091 : Blo 1626512 101638091 := bstep (se 1 (by rfl) ⟨76228568, by rfl⟩ : syracuseStep 101638091 = 152457137) B152457137
theorem B8798233 : Blo 1626512 8798233 := bstep (se 2 (by rfl) ⟨3299337, by rfl⟩ : syracuseStep 8798233 = 6598675) B6598675
theorem B2441321 : Blo 1626512 2441321 := bstep (se 2 (by rfl) ⟨915495, by rfl⟩ : syracuseStep 2441321 = 1830991) B1830991
theorem B8921297 : Blo 1626512 8921297 := bstep (se 2 (by rfl) ⟨3345486, by rfl⟩ : syracuseStep 8921297 = 6690973) B6690973
theorem B3662153 : Blo 1626512 3662153 := bstep (se 2 (by rfl) ⟨1373307, by rfl⟩ : syracuseStep 3662153 = 2746615) B2746615
theorem B9265499 : Blo 1626512 9265499 := bstep (se 1 (by rfl) ⟨6949124, by rfl⟩ : syracuseStep 9265499 = 13898249) B13898249
theorem B3662171 : Blo 1626512 3662171 := bstep (se 1 (by rfl) ⟨2746628, by rfl⟩ : syracuseStep 3662171 = 5493257) B5493257
theorem B2441639 : Blo 1626512 2441639 := bstep (se 1 (by rfl) ⟨1831229, by rfl⟩ : syracuseStep 2441639 = 3662459) B3662459
theorem B4121057 : Blo 1626512 4121057 := bstep (se 2 (by rfl) ⟨1545396, by rfl⟩ : syracuseStep 4121057 = 3090793) B3090793
theorem B2441723 : Blo 1626512 2441723 := bstep (se 1 (by rfl) ⟨1831292, by rfl⟩ : syracuseStep 2441723 = 3662585) B3662585
theorem B12354119 : Blo 1626512 12354119 := bstep (se 1 (by rfl) ⟨9265589, by rfl⟩ : syracuseStep 12354119 = 18531179) B18531179
theorem B3473999 : Blo 1626512 3473999 := bstep (se 1 (by rfl) ⟨2605499, by rfl⟩ : syracuseStep 3473999 = 5210999) B5210999
theorem B33407587 : Blo 1626512 33407587 := bstep (se 1 (by rfl) ⟨25055690, by rfl⟩ : syracuseStep 33407587 = 50111381) B50111381
theorem B2441849 : Blo 1626512 2441849 := bstep (se 2 (by rfl) ⟨915693, by rfl⟩ : syracuseStep 2441849 = 1831387) B1831387
theorem B35684999 : Blo 1626512 35684999 := bstep (se 1 (by rfl) ⟨26763749, by rfl⟩ : syracuseStep 35684999 = 53527499) B53527499
theorem B2441903 : Blo 1626512 2441903 := bstep (se 1 (by rfl) ⟨1831427, by rfl⟩ : syracuseStep 2441903 = 3662855) B3662855
theorem B2441951 : Blo 1626512 2441951 := bstep (se 1 (by rfl) ⟨1831463, by rfl⟩ : syracuseStep 2441951 = 3662927) B3662927
theorem B8798969 : Blo 1626512 8798969 := bstep (se 2 (by rfl) ⟨3299613, by rfl⟩ : syracuseStep 8798969 = 6599227) B6599227
theorem B3662747 : Blo 1626512 3662747 := bstep (se 1 (by rfl) ⟨2747060, by rfl⟩ : syracuseStep 3662747 = 5494121) B5494121
theorem B4121563 : Blo 1626512 4121563 := bstep (se 1 (by rfl) ⟨3091172, by rfl⟩ : syracuseStep 4121563 = 6182345) B6182345
theorem B5489639 : Blo 1626512 5489639 := bstep (se 1 (by rfl) ⟨4117229, by rfl⟩ : syracuseStep 5489639 = 8234459) B8234459
theorem B2745319 : Blo 1626512 2745319 := bstep (se 1 (by rfl) ⟨2058989, by rfl⟩ : syracuseStep 2745319 = 4117979) B4117979
theorem B2442215 : Blo 1626512 2442215 := bstep (se 1 (by rfl) ⟨1831661, by rfl⟩ : syracuseStep 2442215 = 3663323) B3663323
theorem B9266183 : Blo 1626512 9266183 := bstep (se 1 (by rfl) ⟨6949637, by rfl⟩ : syracuseStep 9266183 = 13899275) B13899275
theorem B25044005 : Blo 1626512 25044005 := bstep (se 4 (by rfl) ⟨2347875, by rfl⟩ : syracuseStep 25044005 = 4695751) B4695751
theorem B7423073 : Blo 1626512 7423073 := bstep (se 2 (by rfl) ⟨2783652, by rfl⟩ : syracuseStep 7423073 = 5567305) B5567305
theorem B3662945 : Blo 1626512 3662945 := bstep (se 2 (by rfl) ⟨1373604, by rfl⟩ : syracuseStep 3662945 = 2747209) B2747209
theorem B3908807 : Blo 1626512 3908807 := bstep (se 1 (by rfl) ⟨2931605, by rfl⟩ : syracuseStep 3908807 = 5863211) B5863211
theorem B3474665 : Blo 1626512 3474665 := bstep (se 2 (by rfl) ⟨1302999, by rfl⟩ : syracuseStep 3474665 = 2605999) B2605999
theorem B2442473 : Blo 1626512 2442473 := bstep (se 2 (by rfl) ⟨915927, by rfl⟩ : syracuseStep 2442473 = 1831855) B1831855
theorem B2442527 : Blo 1626512 2442527 := bstep (se 1 (by rfl) ⟨1831895, by rfl⟩ : syracuseStep 2442527 = 3663791) B3663791
theorem B4121887 : Blo 1626512 4121887 := bstep (se 1 (by rfl) ⟨3091415, by rfl⟩ : syracuseStep 4121887 = 6182831) B6182831
theorem B3663143 : Blo 1626512 3663143 := bstep (se 1 (by rfl) ⟨2747357, by rfl⟩ : syracuseStep 3663143 = 5494715) B5494715
theorem B5489963 : Blo 1626512 5489963 := bstep (se 1 (by rfl) ⟨4117472, by rfl⟩ : syracuseStep 5489963 = 8234945) B8234945
theorem B25060751 : Blo 1626512 25060751 := bstep (se 1 (by rfl) ⟨18795563, by rfl⟩ : syracuseStep 25060751 = 37591127) B37591127
theorem B2442695 : Blo 1626512 2442695 := bstep (se 1 (by rfl) ⟨1832021, by rfl⟩ : syracuseStep 2442695 = 3664043) B3664043
theorem B61007305 : Blo 1626512 61007305 := bstep (se 2 (by rfl) ⟨22877739, by rfl⟩ : syracuseStep 61007305 = 45755479) B45755479
theorem B8242721 : Blo 1626512 8242721 := bstep (se 2 (by rfl) ⟨3091020, by rfl⟩ : syracuseStep 8242721 = 6182041) B6182041
theorem B5490233 : Blo 1626512 5490233 := bstep (se 2 (by rfl) ⟨2058837, by rfl⟩ : syracuseStep 5490233 = 4117675) B4117675
theorem B12363353 : Blo 1626512 12363353 := bstep (se 2 (by rfl) ⟨4636257, by rfl⟩ : syracuseStep 12363353 = 9272515) B9272515
theorem B3663521 : Blo 1626512 3663521 := bstep (se 2 (by rfl) ⟨1373820, by rfl⟩ : syracuseStep 3663521 = 2747641) B2747641
theorem B13903649 : Blo 1626512 13903649 := bstep (se 2 (by rfl) ⟨5213868, by rfl⟩ : syracuseStep 13903649 = 10427737) B10427737
theorem B7825207 : Blo 1626512 7825207 := bstep (se 1 (by rfl) ⟨5868905, by rfl⟩ : syracuseStep 7825207 = 11737811) B11737811
theorem B11724689 : Blo 1626512 11724689 := bstep (se 2 (by rfl) ⟨4396758, by rfl⟩ : syracuseStep 11724689 = 8793517) B8793517
theorem B3090383 : Blo 1626512 3090383 := bstep (se 1 (by rfl) ⟨2317787, by rfl⟩ : syracuseStep 3090383 = 4635575) B4635575
theorem B3663881 : Blo 1626512 3663881 := bstep (se 2 (by rfl) ⟨1373955, by rfl⟩ : syracuseStep 3663881 = 2747911) B2747911
theorem B18532637 : Blo 1626512 18532637 := bstep (se 3 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 18532637 = 6949739) B6949739
theorem B8235431 : Blo 1626512 8235431 := bstep (se 1 (by rfl) ⟨6176573, by rfl⟩ : syracuseStep 8235431 = 12353147) B12353147
theorem B3090899 : Blo 1626512 3090899 := bstep (se 1 (by rfl) ⟨2318174, by rfl⟩ : syracuseStep 3090899 = 4636349) B4636349
theorem B3475963 : Blo 1626512 3475963 := bstep (se 1 (by rfl) ⟨2606972, by rfl⟩ : syracuseStep 3475963 = 5213945) B5213945
theorem B271034909 : Blo 1626512 271034909 := bstep (se 3 (by rfl) ⟨50819045, by rfl⟩ : syracuseStep 271034909 = 101638091) B101638091
theorem B8235593 : Blo 1626512 8235593 := bstep (se 2 (by rfl) ⟨3088347, by rfl⟩ : syracuseStep 8235593 = 6176695) B6176695
theorem B3091051 : Blo 1626512 3091051 := bstep (se 1 (by rfl) ⟨2318288, by rfl⟩ : syracuseStep 3091051 = 4636577) B4636577
theorem B5868227 : Blo 1626512 5868227 := bstep (se 1 (by rfl) ⟨4401170, by rfl⟩ : syracuseStep 5868227 = 8802341) B8802341
theorem B9267959 : Blo 1626512 9267959 := bstep (se 1 (by rfl) ⟨6950969, by rfl⟩ : syracuseStep 9267959 = 13901939) B13901939
theorem B5491475 : Blo 1626512 5491475 := bstep (se 1 (by rfl) ⟨4118606, by rfl⟩ : syracuseStep 5491475 = 8237213) B8237213
theorem B3132239 : Blo 1626512 3132239 := bstep (se 1 (by rfl) ⟨2349179, by rfl⟩ : syracuseStep 3132239 = 4698359) B4698359
theorem B3091279 : Blo 1626512 3091279 := bstep (se 1 (by rfl) ⟨2318459, by rfl⟩ : syracuseStep 3091279 = 4636919) B4636919
theorem B3091355 : Blo 1626512 3091355 := bstep (se 1 (by rfl) ⟨2318516, by rfl⟩ : syracuseStep 3091355 = 4637033) B4637033
theorem B2608043 : Blo 1626512 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B1829839 : Blo 1626512 1829839 := bstep (se 1 (by rfl) ⟨1372379, by rfl⟩ : syracuseStep 1829839 = 2744759) B2744759
theorem B4459643 : Blo 1626512 4459643 := bstep (se 1 (by rfl) ⟨3344732, by rfl⟩ : syracuseStep 4459643 = 6689465) B6689465
theorem B31288589 : Blo 1626512 31288589 := bstep (se 3 (by rfl) ⟨5866610, by rfl⟩ : syracuseStep 31288589 = 11733221) B11733221
theorem B1830235 : Blo 1626512 1830235 := bstep (se 1 (by rfl) ⟨1372676, by rfl⟩ : syracuseStep 1830235 = 2745353) B2745353
theorem B9268667 : Blo 1626512 9268667 := bstep (se 1 (by rfl) ⟨6951500, by rfl⟩ : syracuseStep 9268667 = 13903001) B13903001
theorem B1830343 : Blo 1626512 1830343 := bstep (se 1 (by rfl) ⟨1372757, by rfl⟩ : syracuseStep 1830343 = 2745515) B2745515
theorem B2747999 : Blo 1626512 2747999 := bstep (se 1 (by rfl) ⟨2060999, by rfl⟩ : syracuseStep 2747999 = 4121999) B4121999
theorem B5492339 : Blo 1626512 5492339 := bstep (se 1 (by rfl) ⟨4119254, by rfl⟩ : syracuseStep 5492339 = 8238509) B8238509
theorem B11890385 : Blo 1626512 11890385 := bstep (se 2 (by rfl) ⟨4458894, by rfl⟩ : syracuseStep 11890385 = 8917789) B8917789
theorem B18779951 : Blo 1626512 18779951 := bstep (se 1 (by rfl) ⟨14084963, by rfl⟩ : syracuseStep 18779951 = 28169927) B28169927
theorem B1830703 : Blo 1626512 1830703 := bstep (se 1 (by rfl) ⟨1373027, by rfl⟩ : syracuseStep 1830703 = 2746055) B2746055
theorem B5492609 : Blo 1626512 5492609 := bstep (se 2 (by rfl) ⟨2059728, by rfl⟩ : syracuseStep 5492609 = 4119457) B4119457
theorem B1830811 : Blo 1626512 1830811 := bstep (se 1 (by rfl) ⟨1373108, by rfl⟩ : syracuseStep 1830811 = 2746217) B2746217
theorem B17592221 : Blo 1626512 17592221 := bstep (se 3 (by rfl) ⟨3298541, by rfl⟩ : syracuseStep 17592221 = 6597083) B6597083
theorem B3911689 : Blo 1626512 3911689 := bstep (se 2 (by rfl) ⟨1466883, by rfl⟩ : syracuseStep 3911689 = 2933767) B2933767
theorem B1831207 : Blo 1626512 1831207 := bstep (se 1 (by rfl) ⟨1373405, by rfl⟩ : syracuseStep 1831207 = 2746811) B2746811
theorem B2060635 : Blo 1626512 2060635 := bstep (se 1 (by rfl) ⟨1545476, by rfl⟩ : syracuseStep 2060635 = 3090953) B3090953
theorem B19788137 : Blo 1626512 19788137 := bstep (se 2 (by rfl) ⟨7420551, by rfl⟩ : syracuseStep 19788137 = 14841103) B14841103
theorem B1831279 : Blo 1626512 1831279 := bstep (se 1 (by rfl) ⟨1373459, by rfl⟩ : syracuseStep 1831279 = 2746919) B2746919
theorem B1626535 : Blo 1626512 1626535 := bstep (se 1 (by rfl) ⟨1219901, by rfl⟩ : syracuseStep 1626535 = 2439803) B2439803
theorem B8237537 : Blo 1626512 8237537 := bstep (se 2 (by rfl) ⟨3089076, by rfl⟩ : syracuseStep 8237537 = 6178153) B6178153
theorem B5214689 : Blo 1626512 5214689 := bstep (se 2 (by rfl) ⟨1955508, by rfl⟩ : syracuseStep 5214689 = 3911017) B3911017
theorem B1626619 : Blo 1626512 1626619 := bstep (se 1 (by rfl) ⟨1219964, by rfl⟩ : syracuseStep 1626619 = 2439929) B2439929
theorem B1626687 : Blo 1626512 1626687 := bstep (se 1 (by rfl) ⟨1220015, by rfl⟩ : syracuseStep 1626687 = 2440031) B2440031
theorem B1626695 : Blo 1626512 1626695 := bstep (se 1 (by rfl) ⟨1220021, by rfl⟩ : syracuseStep 1626695 = 2440043) B2440043
theorem B1831495 : Blo 1626512 1831495 := bstep (se 1 (by rfl) ⟨1373621, by rfl⟩ : syracuseStep 1831495 = 2747243) B2747243
theorem B5493419 : Blo 1626512 5493419 := bstep (se 1 (by rfl) ⟨4120064, by rfl⟩ : syracuseStep 5493419 = 8240129) B8240129
theorem B1626847 : Blo 1626512 1626847 := bstep (se 1 (by rfl) ⟨1220135, by rfl⟩ : syracuseStep 1626847 = 2440271) B2440271
theorem B1626927 : Blo 1626512 1626927 := bstep (se 1 (by rfl) ⟨1220195, by rfl⟩ : syracuseStep 1626927 = 2440391) B2440391
theorem B9270125 : Blo 1626512 9270125 := bstep (se 3 (by rfl) ⟨1738148, by rfl⟩ : syracuseStep 9270125 = 3476297) B3476297
theorem B1627035 : Blo 1626512 1627035 := bstep (se 1 (by rfl) ⟨1220276, by rfl⟩ : syracuseStep 1627035 = 2440553) B2440553
theorem B14840777 : Blo 1626512 14840777 := bstep (se 2 (by rfl) ⟨5565291, by rfl⟩ : syracuseStep 14840777 = 11130583) B11130583
theorem B1627087 : Blo 1626512 1627087 := bstep (se 1 (by rfl) ⟨1220315, by rfl⟩ : syracuseStep 1627087 = 2440631) B2440631
theorem B1627111 : Blo 1626512 1627111 := bstep (se 1 (by rfl) ⟨1220333, by rfl⟩ : syracuseStep 1627111 = 2440667) B2440667
theorem B2782351 : Blo 1626512 2782351 := bstep (se 1 (by rfl) ⟨2086763, by rfl⟩ : syracuseStep 2782351 = 4173527) B4173527
theorem B5493959 : Blo 1626512 5493959 := bstep (se 1 (by rfl) ⟨4120469, by rfl⟩ : syracuseStep 5493959 = 8240939) B8240939
theorem B4633843 : Blo 1626512 4633843 := bstep (se 1 (by rfl) ⟨3475382, by rfl⟩ : syracuseStep 4633843 = 6950765) B6950765
theorem B1627423 : Blo 1626512 1627423 := bstep (se 1 (by rfl) ⟨1220567, by rfl⟩ : syracuseStep 1627423 = 2441135) B2441135
theorem B1627483 : Blo 1626512 1627483 := bstep (se 1 (by rfl) ⟨1220612, by rfl⟩ : syracuseStep 1627483 = 2441225) B2441225
theorem B1627503 : Blo 1626512 1627503 := bstep (se 1 (by rfl) ⟨1220627, by rfl⟩ : syracuseStep 1627503 = 2441255) B2441255
theorem B8803723 : Blo 1626512 8803723 := bstep (se 1 (by rfl) ⟨6602792, by rfl⟩ : syracuseStep 8803723 = 13205585) B13205585
theorem B11138465 : Blo 1626512 11138465 := bstep (se 2 (by rfl) ⟨4176924, by rfl⟩ : syracuseStep 11138465 = 8353849) B8353849
theorem B1627559 : Blo 1626512 1627559 := bstep (se 1 (by rfl) ⟨1220669, by rfl⟩ : syracuseStep 1627559 = 2441339) B2441339
theorem B1627643 : Blo 1626512 1627643 := bstep (se 1 (by rfl) ⟨1220732, by rfl⟩ : syracuseStep 1627643 = 2441465) B2441465
theorem B114349603 : Blo 1626512 114349603 := bstep (se 1 (by rfl) ⟨85762202, by rfl⟩ : syracuseStep 114349603 = 171524405) B171524405
theorem B1627711 : Blo 1626512 1627711 := bstep (se 1 (by rfl) ⟨1220783, by rfl⟩ : syracuseStep 1627711 = 2441567) B2441567
theorem B1627719 : Blo 1626512 1627719 := bstep (se 1 (by rfl) ⟨1220789, by rfl⟩ : syracuseStep 1627719 = 2441579) B2441579
theorem B4118111 : Blo 1626512 4118111 := bstep (se 1 (by rfl) ⟨3088583, by rfl⟩ : syracuseStep 4118111 = 6177167) B6177167
theorem B1627871 : Blo 1626512 1627871 := bstep (se 1 (by rfl) ⟨1220903, by rfl⟩ : syracuseStep 1627871 = 2441807) B2441807
theorem B169162469 : Blo 1626512 169162469 := bstep (se 4 (by rfl) ⟨15858981, by rfl⟩ : syracuseStep 169162469 = 31717963) B31717963
theorem B1627951 : Blo 1626512 1627951 := bstep (se 1 (by rfl) ⟨1220963, by rfl⟩ : syracuseStep 1627951 = 2441927) B2441927
theorem B1628059 : Blo 1626512 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B17594297 : Blo 1626512 17594297 := bstep (se 2 (by rfl) ⟨6597861, by rfl⟩ : syracuseStep 17594297 = 13195723) B13195723
theorem B15644603 : Blo 1626512 15644603 := bstep (se 1 (by rfl) ⟨11733452, by rfl⟩ : syracuseStep 15644603 = 23466905) B23466905
theorem B1628111 : Blo 1626512 1628111 := bstep (se 1 (by rfl) ⟨1221083, by rfl⟩ : syracuseStep 1628111 = 2442167) B2442167
theorem B1628135 : Blo 1626512 1628135 := bstep (se 1 (by rfl) ⟨1221101, by rfl⟩ : syracuseStep 1628135 = 2442203) B2442203
theorem B7420099 : Blo 1626512 7420099 := bstep (se 1 (by rfl) ⟨5565074, by rfl⟩ : syracuseStep 7420099 = 11130149) B11130149
theorem B4118809 : Blo 1626512 4118809 := bstep (se 2 (by rfl) ⟨1544553, by rfl⟩ : syracuseStep 4118809 = 3089107) B3089107
theorem B1628447 : Blo 1626512 1628447 := bstep (se 1 (by rfl) ⟨1221335, by rfl⟩ : syracuseStep 1628447 = 2442671) B2442671
theorem B1628507 : Blo 1626512 1628507 := bstep (se 1 (by rfl) ⟨1221380, by rfl⟩ : syracuseStep 1628507 = 2442761) B2442761
theorem B4118951 : Blo 1626512 4118951 := bstep (se 1 (by rfl) ⟨3089213, by rfl⟩ : syracuseStep 4118951 = 6178427) B6178427
theorem B4119113 : Blo 1626512 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B12352175 : Blo 1626512 12352175 := bstep (se 1 (by rfl) ⟨9264131, by rfl⟩ : syracuseStep 12352175 = 18528263) B18528263
theorem B5495471 : Blo 1626512 5495471 := bstep (se 1 (by rfl) ⟨4121603, by rfl⟩ : syracuseStep 5495471 = 8243207) B8243207
theorem B2439863 : Blo 1626512 2439863 := bstep (se 1 (by rfl) ⟨1829897, by rfl⟩ : syracuseStep 2439863 = 3659795) B3659795
theorem B8239805 : Blo 1626512 8239805 := bstep (se 3 (by rfl) ⟨1544963, by rfl⟩ : syracuseStep 8239805 = 3089927) B3089927
theorem B3660623 : Blo 1626512 3660623 := bstep (se 1 (by rfl) ⟨2745467, by rfl⟩ : syracuseStep 3660623 = 5490935) B5490935
theorem B2440091 : Blo 1626512 2440091 := bstep (se 1 (by rfl) ⟨1830068, by rfl⟩ : syracuseStep 2440091 = 3660137) B3660137
theorem B9894899 : Blo 1626512 9894899 := bstep (se 1 (by rfl) ⟨7421174, by rfl⟩ : syracuseStep 9894899 = 14842349) B14842349
theorem B5495795 : Blo 1626512 5495795 := bstep (se 1 (by rfl) ⟨4121846, by rfl⟩ : syracuseStep 5495795 = 8243693) B8243693
theorem B3660839 : Blo 1626512 3660839 := bstep (se 1 (by rfl) ⟨2745629, by rfl⟩ : syracuseStep 3660839 = 5491259) B5491259
theorem B9264293 : Blo 1626512 9264293 := bstep (se 4 (by rfl) ⟨868527, by rfl⟩ : syracuseStep 9264293 = 1737055) B1737055
theorem B3661019 : Blo 1626512 3661019 := bstep (se 1 (by rfl) ⟨2745764, by rfl⟩ : syracuseStep 3661019 = 5491529) B5491529
theorem B24108299 : Blo 1626512 24108299 := bstep (se 1 (by rfl) ⟨18081224, by rfl⟩ : syracuseStep 24108299 = 36162449) B36162449
theorem B2440487 : Blo 1626512 2440487 := bstep (se 1 (by rfl) ⟨1830365, by rfl⟩ : syracuseStep 2440487 = 3660731) B3660731
theorem B12524867 : Blo 1626512 12524867 := bstep (se 1 (by rfl) ⟨9393650, by rfl⟩ : syracuseStep 12524867 = 18787301) B18787301
theorem B40705355 : Blo 1626512 40705355 := bstep (se 1 (by rfl) ⟨30529016, by rfl⟩ : syracuseStep 40705355 = 61058033) B61058033
theorem B2440571 : Blo 1626512 2440571 := bstep (se 1 (by rfl) ⟨1830428, by rfl⟩ : syracuseStep 2440571 = 3660857) B3660857
theorem B3661217 : Blo 1626512 3661217 := bstep (se 2 (by rfl) ⟨1372956, by rfl⟩ : syracuseStep 3661217 = 2745913) B2745913
theorem B93887909 : Blo 1626512 93887909 := bstep (se 4 (by rfl) ⟨8801991, by rfl⟩ : syracuseStep 93887909 = 17603983) B17603983
theorem B2440697 : Blo 1626512 2440697 := bstep (se 2 (by rfl) ⟨915261, by rfl⟩ : syracuseStep 2440697 = 1830523) B1830523
theorem B4234745 : Blo 1626512 4234745 := bstep (se 2 (by rfl) ⟨1588029, by rfl⟩ : syracuseStep 4234745 = 3176059) B3176059
theorem B2440799 : Blo 1626512 2440799 := bstep (se 1 (by rfl) ⟨1830599, by rfl⟩ : syracuseStep 2440799 = 3661199) B3661199
theorem B2932319 : Blo 1626512 2932319 := bstep (se 1 (by rfl) ⟨2199239, by rfl⟩ : syracuseStep 2932319 = 4398479) B4398479
theorem B3300959 : Blo 1626512 3300959 := bstep (se 1 (by rfl) ⟨2475719, by rfl⟩ : syracuseStep 3300959 = 4951439) B4951439
theorem B4398749 : Blo 1626512 4398749 := bstep (se 3 (by rfl) ⟨824765, by rfl⟩ : syracuseStep 4398749 = 1649531) B1649531
theorem B3088135 : Blo 1626512 3088135 := bstep (se 1 (by rfl) ⟨2316101, by rfl⟩ : syracuseStep 3088135 = 4632203) B4632203
theorem B5865227 : Blo 1626512 5865227 := bstep (se 1 (by rfl) ⟨4398920, by rfl⟩ : syracuseStep 5865227 = 8797841) B8797841
theorem B2441015 : Blo 1626512 2441015 := bstep (se 1 (by rfl) ⟨1830761, by rfl⟩ : syracuseStep 2441015 = 3661523) B3661523
theorem B3661775 : Blo 1626512 3661775 := bstep (se 1 (by rfl) ⟨2746331, by rfl⟩ : syracuseStep 3661775 = 5492663) B5492663
theorem B11730977 : Blo 1626512 11730977 := bstep (se 2 (by rfl) ⟨4399116, by rfl⟩ : syracuseStep 11730977 = 8798233) B8798233
theorem B2441435 : Blo 1626512 2441435 := bstep (se 1 (by rfl) ⟨1831076, by rfl⟩ : syracuseStep 2441435 = 3662153) B3662153
theorem B6176999 : Blo 1626512 6176999 := bstep (se 1 (by rfl) ⟨4632749, by rfl⟩ : syracuseStep 6176999 = 9265499) B9265499
theorem B2441447 : Blo 1626512 2441447 := bstep (se 1 (by rfl) ⟨1831085, by rfl⟩ : syracuseStep 2441447 = 3662171) B3662171
theorem B2441609 : Blo 1626512 2441609 := bstep (se 2 (by rfl) ⟨915603, by rfl⟩ : syracuseStep 2441609 = 1831207) B1831207
theorem B23789999 : Blo 1626512 23789999 := bstep (se 1 (by rfl) ⟨17842499, by rfl⟩ : syracuseStep 23789999 = 35684999) B35684999
theorem B3662279 : Blo 1626512 3662279 := bstep (se 1 (by rfl) ⟨2746709, by rfl⟩ : syracuseStep 3662279 = 5493419) B5493419
theorem B2441705 : Blo 1626512 2441705 := bstep (se 2 (by rfl) ⟨915639, by rfl⟩ : syracuseStep 2441705 = 1831279) B1831279
theorem B5865979 : Blo 1626512 5865979 := bstep (se 1 (by rfl) ⟨4399484, by rfl⟩ : syracuseStep 5865979 = 8798969) B8798969
theorem B23790125 : Blo 1626512 23790125 := bstep (se 3 (by rfl) ⟨4460648, by rfl⟩ : syracuseStep 23790125 = 8921297) B8921297
theorem B2441831 : Blo 1626512 2441831 := bstep (se 1 (by rfl) ⟨1831373, by rfl⟩ : syracuseStep 2441831 = 3662747) B3662747
theorem B6177455 : Blo 1626512 6177455 := bstep (se 1 (by rfl) ⟨4633091, by rfl⟩ : syracuseStep 6177455 = 9266183) B9266183
theorem B16696003 : Blo 1626512 16696003 := bstep (se 1 (by rfl) ⟨12522002, by rfl⟩ : syracuseStep 16696003 = 25044005) B25044005
theorem B4948715 : Blo 1626512 4948715 := bstep (se 1 (by rfl) ⟨3711536, by rfl⟩ : syracuseStep 4948715 = 7423073) B7423073
theorem B2441963 : Blo 1626512 2441963 := bstep (se 1 (by rfl) ⟨1831472, by rfl⟩ : syracuseStep 2441963 = 3662945) B3662945
theorem B2441993 : Blo 1626512 2441993 := bstep (se 2 (by rfl) ⟨915747, by rfl⟩ : syracuseStep 2441993 = 1831495) B1831495
theorem B2605871 : Blo 1626512 2605871 := bstep (se 1 (by rfl) ⟨1954403, by rfl⟩ : syracuseStep 2605871 = 3908807) B3908807
theorem B3662639 : Blo 1626512 3662639 := bstep (se 1 (by rfl) ⟨2746979, by rfl⟩ : syracuseStep 3662639 = 5493959) B5493959
theorem B4121401 : Blo 1626512 4121401 := bstep (se 2 (by rfl) ⟨1545525, by rfl⟩ : syracuseStep 4121401 = 3091051) B3091051
theorem B2442095 : Blo 1626512 2442095 := bstep (se 1 (by rfl) ⟨1831571, by rfl⟩ : syracuseStep 2442095 = 3663143) B3663143
theorem B8242235 : Blo 1626512 8242235 := bstep (se 1 (by rfl) ⟨6181676, by rfl⟩ : syracuseStep 8242235 = 12363353) B12363353
theorem B2745407 : Blo 1626512 2745407 := bstep (se 1 (by rfl) ⟨2059055, by rfl⟩ : syracuseStep 2745407 = 4118111) B4118111
theorem B4121705 : Blo 1626512 4121705 := bstep (se 2 (by rfl) ⟨1545639, by rfl⟩ : syracuseStep 4121705 = 3091279) B3091279
theorem B2442347 : Blo 1626512 2442347 := bstep (se 1 (by rfl) ⟨1831760, by rfl⟩ : syracuseStep 2442347 = 3663521) B3663521
theorem B8242397 : Blo 1626512 8242397 := bstep (se 3 (by rfl) ⟨1545449, by rfl⟩ : syracuseStep 8242397 = 3090899) B3090899
theorem B7816459 : Blo 1626512 7816459 := bstep (se 1 (by rfl) ⟨5862344, by rfl⟩ : syracuseStep 7816459 = 11724689) B11724689
theorem B10429735 : Blo 1626512 10429735 := bstep (se 1 (by rfl) ⟨7822301, by rfl⟩ : syracuseStep 10429735 = 15644603) B15644603
theorem B2442587 : Blo 1626512 2442587 := bstep (se 1 (by rfl) ⟨1831940, by rfl⟩ : syracuseStep 2442587 = 3663881) B3663881
theorem B12355091 : Blo 1626512 12355091 := bstep (se 1 (by rfl) ⟨9266318, by rfl⟩ : syracuseStep 12355091 = 18532637) B18532637
theorem B5490287 : Blo 1626512 5490287 := bstep (se 1 (by rfl) ⟨4117715, by rfl⟩ : syracuseStep 5490287 = 8235431) B8235431
theorem B2745967 : Blo 1626512 2745967 := bstep (se 1 (by rfl) ⟨2059475, by rfl⟩ : syracuseStep 2745967 = 4118951) B4118951
theorem B6178457 : Blo 1626512 6178457 := bstep (se 2 (by rfl) ⟨2316921, by rfl⟩ : syracuseStep 6178457 = 4633843) B4633843
theorem B5490395 : Blo 1626512 5490395 := bstep (se 1 (by rfl) ⟨4117796, by rfl⟩ : syracuseStep 5490395 = 8235593) B8235593
theorem B2746075 : Blo 1626512 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B8234783 : Blo 1626512 8234783 := bstep (se 1 (by rfl) ⟨6176087, by rfl⟩ : syracuseStep 8234783 = 12352175) B12352175
theorem B3663647 : Blo 1626512 3663647 := bstep (se 1 (by rfl) ⟨2747735, by rfl⟩ : syracuseStep 3663647 = 5495471) B5495471
theorem B6178639 : Blo 1626512 6178639 := bstep (se 1 (by rfl) ⟨4633979, by rfl⟩ : syracuseStep 6178639 = 9267959) B9267959
theorem B3663863 : Blo 1626512 3663863 := bstep (se 1 (by rfl) ⟨2747897, by rfl⟩ : syracuseStep 3663863 = 5495795) B5495795
theorem B20859059 : Blo 1626512 20859059 := bstep (se 1 (by rfl) ⟨15644294, by rfl⟩ : syracuseStep 20859059 = 31288589) B31288589
theorem B8349911 : Blo 1626512 8349911 := bstep (se 1 (by rfl) ⟨6262433, by rfl⟩ : syracuseStep 8349911 = 12524867) B12524867
theorem B6179111 : Blo 1626512 6179111 := bstep (se 1 (by rfl) ⟨4634333, by rfl⟩ : syracuseStep 6179111 = 9268667) B9268667
theorem B3910151 : Blo 1626512 3910151 := bstep (se 1 (by rfl) ⟨2932613, by rfl⟩ : syracuseStep 3910151 = 5865227) B5865227
theorem B12519967 : Blo 1626512 12519967 := bstep (se 1 (by rfl) ⟨9389975, by rfl⟩ : syracuseStep 12519967 = 18779951) B18779951
theorem B13192091 : Blo 1626512 13192091 := bstep (se 1 (by rfl) ⟨9894068, by rfl⟩ : syracuseStep 13192091 = 19788137) B19788137
theorem B5491691 : Blo 1626512 5491691 := bstep (se 1 (by rfl) ⟨4118768, by rfl⟩ : syracuseStep 5491691 = 8237537) B8237537
theorem B3476459 : Blo 1626512 3476459 := bstep (se 1 (by rfl) ⟨2607344, by rfl⟩ : syracuseStep 3476459 = 5214689) B5214689
theorem B2747371 : Blo 1626512 2747371 := bstep (se 1 (by rfl) ⟨2060528, by rfl⟩ : syracuseStep 2747371 = 4121057) B4121057
theorem B5491745 : Blo 1626512 5491745 := bstep (se 2 (by rfl) ⟨2059404, by rfl⟩ : syracuseStep 5491745 = 4118809) B4118809
theorem B8236079 : Blo 1626512 8236079 := bstep (se 1 (by rfl) ⟨6177059, by rfl⟩ : syracuseStep 8236079 = 12354119) B12354119
theorem B2747513 : Blo 1626512 2747513 := bstep (se 2 (by rfl) ⟨1030317, by rfl⟩ : syracuseStep 2747513 = 2060635) B2060635
theorem B6180083 : Blo 1626512 6180083 := bstep (se 1 (by rfl) ⟨4635062, by rfl⟩ : syracuseStep 6180083 = 9270125) B9270125
theorem B14839205 : Blo 1626512 14839205 := bstep (se 4 (by rfl) ⟨1391175, by rfl⟩ : syracuseStep 14839205 = 2782351) B2782351
theorem B44543449 : Blo 1626512 44543449 := bstep (se 2 (by rfl) ⟨16703793, by rfl⟩ : syracuseStep 44543449 = 33407587) B33407587
theorem B33410549 : Blo 1626512 33410549 := bstep (se 5 (by rfl) ⟨1566119, by rfl⟩ : syracuseStep 33410549 = 3132239) B3132239
theorem B108547613 : Blo 1626512 108547613 := bstep (se 3 (by rfl) ⟨20352677, by rfl⟩ : syracuseStep 108547613 = 40705355) B40705355
theorem B16707167 : Blo 1626512 16707167 := bstep (se 1 (by rfl) ⟨12530375, by rfl⟩ : syracuseStep 16707167 = 25060751) B25060751
theorem B7425643 : Blo 1626512 7425643 := bstep (se 1 (by rfl) ⟨5569232, by rfl⟩ : syracuseStep 7425643 = 11138465) B11138465
theorem B112774979 : Blo 1626512 112774979 := bstep (se 1 (by rfl) ⟨84581234, by rfl⟩ : syracuseStep 112774979 = 169162469) B169162469
theorem B9269099 : Blo 1626512 9269099 := bstep (se 1 (by rfl) ⟨6951824, by rfl⟩ : syracuseStep 9269099 = 13903649) B13903649
theorem B2060255 : Blo 1626512 2060255 := bstep (se 1 (by rfl) ⟨1545191, by rfl⟩ : syracuseStep 2060255 = 3090383) B3090383
theorem B7819517 : Blo 1626512 7819517 := bstep (se 3 (by rfl) ⟨1466159, by rfl⟩ : syracuseStep 7819517 = 2932319) B2932319
theorem B8802557 : Blo 1626512 8802557 := bstep (se 3 (by rfl) ⟨1650479, by rfl⟩ : syracuseStep 8802557 = 3300959) B3300959
theorem B1626575 : Blo 1626512 1626575 := bstep (se 1 (by rfl) ⟨1219931, by rfl⟩ : syracuseStep 1626575 = 2439863) B2439863
theorem B5493203 : Blo 1626512 5493203 := bstep (se 1 (by rfl) ⟨4119902, by rfl⟩ : syracuseStep 5493203 = 8239805) B8239805
theorem B3912151 : Blo 1626512 3912151 := bstep (se 1 (by rfl) ⟨2934113, by rfl⟩ : syracuseStep 3912151 = 5868227) B5868227
theorem B81343073 : Blo 1626512 81343073 := bstep (se 2 (by rfl) ⟨30503652, by rfl⟩ : syracuseStep 81343073 = 61007305) B61007305
theorem B1626727 : Blo 1626512 1626727 := bstep (se 1 (by rfl) ⟨1220045, by rfl⟩ : syracuseStep 1626727 = 2440091) B2440091
theorem B2060903 : Blo 1626512 2060903 := bstep (se 1 (by rfl) ⟨1545677, by rfl⟩ : syracuseStep 2060903 = 3091355) B3091355
theorem B152466137 : Blo 1626512 152466137 := bstep (se 2 (by rfl) ⟨57174801, by rfl⟩ : syracuseStep 152466137 = 114349603) B114349603
theorem B1626991 : Blo 1626512 1626991 := bstep (se 1 (by rfl) ⟨1220243, by rfl⟩ : syracuseStep 1626991 = 2440487) B2440487
theorem B1627047 : Blo 1626512 1627047 := bstep (se 1 (by rfl) ⟨1220285, by rfl⟩ : syracuseStep 1627047 = 2440571) B2440571
theorem B62591939 : Blo 1626512 62591939 := bstep (se 1 (by rfl) ⟨46943954, by rfl⟩ : syracuseStep 62591939 = 93887909) B93887909
theorem B1627131 : Blo 1626512 1627131 := bstep (se 1 (by rfl) ⟨1220348, by rfl⟩ : syracuseStep 1627131 = 2440697) B2440697
theorem B2823163 : Blo 1626512 2823163 := bstep (se 1 (by rfl) ⟨2117372, by rfl⟩ : syracuseStep 2823163 = 4234745) B4234745
theorem B4117513 : Blo 1626512 4117513 := bstep (se 2 (by rfl) ⟨1544067, by rfl⟩ : syracuseStep 4117513 = 3088135) B3088135
theorem B1627199 : Blo 1626512 1627199 := bstep (se 1 (by rfl) ⟨1220399, by rfl⟩ : syracuseStep 1627199 = 2440799) B2440799
theorem B1831999 : Blo 1626512 1831999 := bstep (se 1 (by rfl) ⟨1373999, by rfl⟩ : syracuseStep 1831999 = 2747999) B2747999
theorem B10433609 : Blo 1626512 10433609 := bstep (se 2 (by rfl) ⟨3912603, by rfl⟩ : syracuseStep 10433609 = 7825207) B7825207
theorem B7926923 : Blo 1626512 7926923 := bstep (se 1 (by rfl) ⟨5945192, by rfl⟩ : syracuseStep 7926923 = 11890385) B11890385
theorem B1627343 : Blo 1626512 1627343 := bstep (se 1 (by rfl) ⟨1220507, by rfl⟩ : syracuseStep 1627343 = 2441015) B2441015
theorem B11728147 : Blo 1626512 11728147 := bstep (se 1 (by rfl) ⟨8796110, by rfl⟩ : syracuseStep 11728147 = 17592221) B17592221
theorem B5215585 : Blo 1626512 5215585 := bstep (se 2 (by rfl) ⟨1955844, by rfl⟩ : syracuseStep 5215585 = 3911689) B3911689
theorem B1627547 : Blo 1626512 1627547 := bstep (se 1 (by rfl) ⟨1220660, by rfl⟩ : syracuseStep 1627547 = 2441321) B2441321
theorem B9893465 : Blo 1626512 9893465 := bstep (se 2 (by rfl) ⟨3710049, by rfl⟩ : syracuseStep 9893465 = 7420099) B7420099
theorem B1627759 : Blo 1626512 1627759 := bstep (se 1 (by rfl) ⟨1220819, by rfl⟩ : syracuseStep 1627759 = 2441639) B2441639
theorem B1627815 : Blo 1626512 1627815 := bstep (se 1 (by rfl) ⟨1220861, by rfl⟩ : syracuseStep 1627815 = 2441723) B2441723
theorem B2315999 : Blo 1626512 2315999 := bstep (se 1 (by rfl) ⟨1736999, by rfl⟩ : syracuseStep 2315999 = 3473999) B3473999
theorem B1627899 : Blo 1626512 1627899 := bstep (se 1 (by rfl) ⟨1220924, by rfl⟩ : syracuseStep 1627899 = 2441849) B2441849
theorem B1627935 : Blo 1626512 1627935 := bstep (se 1 (by rfl) ⟨1220951, by rfl⟩ : syracuseStep 1627935 = 2441903) B2441903
theorem B1627967 : Blo 1626512 1627967 := bstep (se 1 (by rfl) ⟨1220975, by rfl⟩ : syracuseStep 1627967 = 2441951) B2441951
theorem B3659759 : Blo 1626512 3659759 := bstep (se 1 (by rfl) ⟨2744819, by rfl⟩ : syracuseStep 3659759 = 5489639) B5489639
theorem B1628143 : Blo 1626512 1628143 := bstep (se 1 (by rfl) ⟨1221107, by rfl⟩ : syracuseStep 1628143 = 2442215) B2442215
theorem B2316443 : Blo 1626512 2316443 := bstep (se 1 (by rfl) ⟨1737332, by rfl⟩ : syracuseStep 2316443 = 3474665) B3474665
theorem B1628315 : Blo 1626512 1628315 := bstep (se 1 (by rfl) ⟨1221236, by rfl⟩ : syracuseStep 1628315 = 2442473) B2442473
theorem B1628351 : Blo 1626512 1628351 := bstep (se 1 (by rfl) ⟨1221263, by rfl⟩ : syracuseStep 1628351 = 2442527) B2442527
theorem B3659975 : Blo 1626512 3659975 := bstep (se 1 (by rfl) ⟨2744981, by rfl⟩ : syracuseStep 3659975 = 5489963) B5489963
theorem B1628463 : Blo 1626512 1628463 := bstep (se 1 (by rfl) ⟨1221347, by rfl⟩ : syracuseStep 1628463 = 2442695) B2442695
theorem B5495147 : Blo 1626512 5495147 := bstep (se 1 (by rfl) ⟨4121360, by rfl⟩ : syracuseStep 5495147 = 8242721) B8242721
theorem B3660155 : Blo 1626512 3660155 := bstep (se 1 (by rfl) ⟨2745116, by rfl⟩ : syracuseStep 3660155 = 5490233) B5490233
theorem B2439785 : Blo 1626512 2439785 := bstep (se 2 (by rfl) ⟨914919, by rfl⟩ : syracuseStep 2439785 = 1829839) B1829839
theorem B5495417 : Blo 1626512 5495417 := bstep (se 2 (by rfl) ⟨2060781, by rfl⟩ : syracuseStep 5495417 = 4121563) B4121563
theorem B11729531 : Blo 1626512 11729531 := bstep (se 1 (by rfl) ⟨8797148, by rfl⟩ : syracuseStep 11729531 = 17594297) B17594297
theorem B3660425 : Blo 1626512 3660425 := bstep (se 2 (by rfl) ⟨1372659, by rfl⟩ : syracuseStep 3660425 = 2745319) B2745319
theorem B180689939 : Blo 1626512 180689939 := bstep (se 1 (by rfl) ⟨135517454, by rfl⟩ : syracuseStep 180689939 = 271034909) B271034909
theorem B5495849 : Blo 1626512 5495849 := bstep (se 2 (by rfl) ⟨2060943, by rfl⟩ : syracuseStep 5495849 = 4121887) B4121887
theorem B2440313 : Blo 1626512 2440313 := bstep (se 2 (by rfl) ⟨915117, by rfl⟩ : syracuseStep 2440313 = 1830235) B1830235
theorem B3660983 : Blo 1626512 3660983 := bstep (se 1 (by rfl) ⟨2745737, by rfl⟩ : syracuseStep 3660983 = 5491475) B5491475
theorem B11738297 : Blo 1626512 11738297 := bstep (se 2 (by rfl) ⟨4401861, by rfl⟩ : syracuseStep 11738297 = 8803723) B8803723
theorem B2440415 : Blo 1626512 2440415 := bstep (se 1 (by rfl) ⟨1830311, by rfl⟩ : syracuseStep 2440415 = 3660623) B3660623
theorem B2440457 : Blo 1626512 2440457 := bstep (se 2 (by rfl) ⟨915171, by rfl⟩ : syracuseStep 2440457 = 1830343) B1830343
theorem B2440559 : Blo 1626512 2440559 := bstep (se 1 (by rfl) ⟨1830419, by rfl⟩ : syracuseStep 2440559 = 3660839) B3660839
theorem B2973095 : Blo 1626512 2973095 := bstep (se 1 (by rfl) ⟨2229821, by rfl⟩ : syracuseStep 2973095 = 4459643) B4459643
theorem B6176195 : Blo 1626512 6176195 := bstep (se 1 (by rfl) ⟨4632146, by rfl⟩ : syracuseStep 6176195 = 9264293) B9264293
theorem B2440679 : Blo 1626512 2440679 := bstep (se 1 (by rfl) ⟨1830509, by rfl⟩ : syracuseStep 2440679 = 3661019) B3661019
theorem B16072199 : Blo 1626512 16072199 := bstep (se 1 (by rfl) ⟨12054149, by rfl⟩ : syracuseStep 16072199 = 24108299) B24108299
theorem B2440811 : Blo 1626512 2440811 := bstep (se 1 (by rfl) ⟨1830608, by rfl⟩ : syracuseStep 2440811 = 3661217) B3661217
theorem B2440937 : Blo 1626512 2440937 := bstep (se 2 (by rfl) ⟨915351, by rfl⟩ : syracuseStep 2440937 = 1830703) B1830703
theorem B3661559 : Blo 1626512 3661559 := bstep (se 1 (by rfl) ⟨2746169, by rfl⟩ : syracuseStep 3661559 = 5492339) B5492339
theorem B2932499 : Blo 1626512 2932499 := bstep (se 1 (by rfl) ⟨2199374, by rfl⟩ : syracuseStep 2932499 = 4398749) B4398749
theorem B6954781 : Blo 1626512 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B39575405 : Blo 1626512 39575405 := bstep (se 3 (by rfl) ⟨7420388, by rfl⟩ : syracuseStep 39575405 = 14840777) B14840777
theorem B2441081 : Blo 1626512 2441081 := bstep (se 2 (by rfl) ⟨915405, by rfl⟩ : syracuseStep 2441081 = 1830811) B1830811
theorem B3661739 : Blo 1626512 3661739 := bstep (se 1 (by rfl) ⟨2746304, by rfl⟩ : syracuseStep 3661739 = 5492609) B5492609
theorem B26386397 : Blo 1626512 26386397 := bstep (se 3 (by rfl) ⟨4947449, by rfl⟩ : syracuseStep 26386397 = 9894899) B9894899
theorem B2441183 : Blo 1626512 2441183 := bstep (se 1 (by rfl) ⟨1830887, by rfl⟩ : syracuseStep 2441183 = 3661775) B3661775
theorem B18538469 : Blo 1626512 18538469 := bstep (se 4 (by rfl) ⟨1737981, by rfl⟩ : syracuseStep 18538469 = 3475963) B3475963
theorem B15859999 : Blo 1626512 15859999 := bstep (se 1 (by rfl) ⟨11894999, by rfl⟩ : syracuseStep 15859999 = 23789999) B23789999
theorem B2441519 : Blo 1626512 2441519 := bstep (se 1 (by rfl) ⟨1831139, by rfl⟩ : syracuseStep 2441519 = 3662279) B3662279
theorem B3662135 : Blo 1626512 3662135 := bstep (se 1 (by rfl) ⟨2746601, by rfl⟩ : syracuseStep 3662135 = 5493203) B5493203
theorem B15860083 : Blo 1626512 15860083 := bstep (se 1 (by rfl) ⟨11895062, by rfl⟩ : syracuseStep 15860083 = 23790125) B23790125
theorem B6177181 : Blo 1626512 6177181 := bstep (se 3 (by rfl) ⟨1158221, by rfl⟩ : syracuseStep 6177181 = 2316443) B2316443
theorem B2441759 : Blo 1626512 2441759 := bstep (se 1 (by rfl) ⟨1831319, by rfl⟩ : syracuseStep 2441759 = 3662639) B3662639
theorem B6955739 : Blo 1626512 6955739 := bstep (se 1 (by rfl) ⟨5216804, by rfl⟩ : syracuseStep 6955739 = 10433609) B10433609
theorem B5284615 : Blo 1626512 5284615 := bstep (se 1 (by rfl) ⟨3963461, by rfl⟩ : syracuseStep 5284615 = 7926923) B7926923
theorem B6595643 : Blo 1626512 6595643 := bstep (se 1 (by rfl) ⟨4946732, by rfl⟩ : syracuseStep 6595643 = 9893465) B9893465
theorem B5489855 : Blo 1626512 5489855 := bstep (se 1 (by rfl) ⟨4117391, by rfl⟩ : syracuseStep 5489855 = 8234783) B8234783
theorem B2442431 : Blo 1626512 2442431 := bstep (se 1 (by rfl) ⟨1831823, by rfl⟩ : syracuseStep 2442431 = 3663647) B3663647
theorem B3663161 : Blo 1626512 3663161 := bstep (se 2 (by rfl) ⟨1373685, by rfl⟩ : syracuseStep 3663161 = 2747371) B2747371
theorem B2442575 : Blo 1626512 2442575 := bstep (se 1 (by rfl) ⟨1831931, by rfl⟩ : syracuseStep 2442575 = 3663863) B3663863
theorem B5490017 : Blo 1626512 5490017 := bstep (se 2 (by rfl) ⟨2058756, by rfl⟩ : syracuseStep 5490017 = 4117513) B4117513
theorem B2442665 : Blo 1626512 2442665 := bstep (se 2 (by rfl) ⟨915999, by rfl⟩ : syracuseStep 2442665 = 1831999) B1831999
theorem B3663431 : Blo 1626512 3663431 := bstep (se 1 (by rfl) ⟨2747573, by rfl⟩ : syracuseStep 3663431 = 5495147) B5495147
theorem B10421945 : Blo 1626512 10421945 := bstep (se 2 (by rfl) ⟨3908229, by rfl⟩ : syracuseStep 10421945 = 7816459) B7816459
theorem B3663611 : Blo 1626512 3663611 := bstep (se 1 (by rfl) ⟨2747708, by rfl⟩ : syracuseStep 3663611 = 5495417) B5495417
theorem B3663899 : Blo 1626512 3663899 := bstep (se 1 (by rfl) ⟨2747924, by rfl⟩ : syracuseStep 3663899 = 5495849) B5495849
theorem B5490719 : Blo 1626512 5490719 := bstep (se 1 (by rfl) ⟨4118039, by rfl⟩ : syracuseStep 5490719 = 8236079) B8236079
theorem B7825531 : Blo 1626512 7825531 := bstep (se 1 (by rfl) ⟨5869148, by rfl⟩ : syracuseStep 7825531 = 11738297) B11738297
theorem B6948989 : Blo 1626512 6948989 := bstep (se 3 (by rfl) ⟨1302935, by rfl⟩ : syracuseStep 6948989 = 2605871) B2605871
theorem B6179399 : Blo 1626512 6179399 := bstep (se 1 (by rfl) ⟨4634549, by rfl⟩ : syracuseStep 6179399 = 9269099) B9269099
theorem B17590931 : Blo 1626512 17590931 := bstep (se 1 (by rfl) ⟨13193198, by rfl⟩ : syracuseStep 17590931 = 26386397) B26386397
theorem B5213011 : Blo 1626512 5213011 := bstep (se 1 (by rfl) ⟨3909758, by rfl⟩ : syracuseStep 5213011 = 7819517) B7819517
theorem B5868371 : Blo 1626512 5868371 := bstep (se 1 (by rfl) ⟨4401278, by rfl⟩ : syracuseStep 5868371 = 8802557) B8802557
theorem B1830271 : Blo 1626512 1830271 := bstep (se 1 (by rfl) ⟨1372703, by rfl⟩ : syracuseStep 1830271 = 2745407) B2745407
theorem B2747803 : Blo 1626512 2747803 := bstep (se 1 (by rfl) ⟨2060852, by rfl⟩ : syracuseStep 2747803 = 4121705) B4121705
theorem B22261337 : Blo 1626512 22261337 := bstep (se 2 (by rfl) ⟨8348001, by rfl⟩ : syracuseStep 22261337 = 16696003) B16696003
theorem B8236727 : Blo 1626512 8236727 := bstep (se 1 (by rfl) ⟨6177545, by rfl⟩ : syracuseStep 8236727 = 12355091) B12355091
theorem B39571213 : Blo 1626512 39571213 := bstep (se 3 (by rfl) ⟨7419602, by rfl⟩ : syracuseStep 39571213 = 14839205) B14839205
theorem B13906039 : Blo 1626512 13906039 := bstep (se 1 (by rfl) ⟨10429529, by rfl⟩ : syracuseStep 13906039 = 20859059) B20859059
theorem B5566607 : Blo 1626512 5566607 := bstep (se 1 (by rfl) ⟨4174955, by rfl⟩ : syracuseStep 5566607 = 8349911) B8349911
theorem B13906313 : Blo 1626512 13906313 := bstep (se 2 (by rfl) ⟨5214867, by rfl⟩ : syracuseStep 13906313 = 10429735) B10429735
theorem B1626523 : Blo 1626512 1626523 := bstep (se 1 (by rfl) ⟨1219892, by rfl⟩ : syracuseStep 1626523 = 2439785) B2439785
theorem B7819687 : Blo 1626512 7819687 := bstep (se 1 (by rfl) ⟨5864765, by rfl⟩ : syracuseStep 7819687 = 11729531) B11729531
theorem B8794727 : Blo 1626512 8794727 := bstep (se 1 (by rfl) ⟨6596045, by rfl⟩ : syracuseStep 8794727 = 13192091) B13192091
theorem B120459959 : Blo 1626512 120459959 := bstep (se 1 (by rfl) ⟨90344969, by rfl⟩ : syracuseStep 120459959 = 180689939) B180689939
theorem B1626875 : Blo 1626512 1626875 := bstep (se 1 (by rfl) ⟨1220156, by rfl⟩ : syracuseStep 1626875 = 2440313) B2440313
theorem B1831675 : Blo 1626512 1831675 := bstep (se 1 (by rfl) ⟨1373756, by rfl⟩ : syracuseStep 1831675 = 2747513) B2747513
theorem B9900857 : Blo 1626512 9900857 := bstep (se 2 (by rfl) ⟨3712821, by rfl⟩ : syracuseStep 9900857 = 7425643) B7425643
theorem B1626943 : Blo 1626512 1626943 := bstep (se 1 (by rfl) ⟨1220207, by rfl⟩ : syracuseStep 1626943 = 2440415) B2440415
theorem B1626971 : Blo 1626512 1626971 := bstep (se 1 (by rfl) ⟨1220228, by rfl⟩ : syracuseStep 1626971 = 2440457) B2440457
theorem B1627039 : Blo 1626512 1627039 := bstep (se 1 (by rfl) ⟨1220279, by rfl⟩ : syracuseStep 1627039 = 2440559) B2440559
theorem B4117463 : Blo 1626512 4117463 := bstep (se 1 (by rfl) ⟨3088097, by rfl⟩ : syracuseStep 4117463 = 6176195) B6176195
theorem B1627119 : Blo 1626512 1627119 := bstep (se 1 (by rfl) ⟨1220339, by rfl⟩ : syracuseStep 1627119 = 2440679) B2440679
theorem B72365075 : Blo 1626512 72365075 := bstep (se 1 (by rfl) ⟨54273806, by rfl⟩ : syracuseStep 72365075 = 108547613) B108547613
theorem B11138111 : Blo 1626512 11138111 := bstep (se 1 (by rfl) ⟨8353583, by rfl⟩ : syracuseStep 11138111 = 16707167) B16707167
theorem B1627207 : Blo 1626512 1627207 := bstep (se 1 (by rfl) ⟨1220405, by rfl⟩ : syracuseStep 1627207 = 2440811) B2440811
theorem B8238185 : Blo 1626512 8238185 := bstep (se 2 (by rfl) ⟨3089319, by rfl⟩ : syracuseStep 8238185 = 6178639) B6178639
theorem B1627291 : Blo 1626512 1627291 := bstep (se 1 (by rfl) ⟨1220468, by rfl⟩ : syracuseStep 1627291 = 2440937) B2440937
theorem B1954999 : Blo 1626512 1954999 := bstep (se 1 (by rfl) ⟨1466249, by rfl⟩ : syracuseStep 1954999 = 2932499) B2932499
theorem B75183319 : Blo 1626512 75183319 := bstep (se 1 (by rfl) ⟨56387489, by rfl⟩ : syracuseStep 75183319 = 112774979) B112774979
theorem B26383603 : Blo 1626512 26383603 := bstep (se 1 (by rfl) ⟨19787702, by rfl⟩ : syracuseStep 26383603 = 39575405) B39575405
theorem B1627387 : Blo 1626512 1627387 := bstep (se 1 (by rfl) ⟨1220540, by rfl⟩ : syracuseStep 1627387 = 2441081) B2441081
theorem B5494013 : Blo 1626512 5494013 := bstep (se 3 (by rfl) ⟨1030127, by rfl⟩ : syracuseStep 5494013 = 2060255) B2060255
theorem B9270557 : Blo 1626512 9270557 := bstep (se 3 (by rfl) ⟨1738229, by rfl⟩ : syracuseStep 9270557 = 3476459) B3476459
theorem B1627455 : Blo 1626512 1627455 := bstep (se 1 (by rfl) ⟨1220591, by rfl⟩ : syracuseStep 1627455 = 2441183) B2441183
theorem B12358979 : Blo 1626512 12358979 := bstep (se 1 (by rfl) ⟨9269234, by rfl⟩ : syracuseStep 12358979 = 18538469) B18538469
theorem B7820651 : Blo 1626512 7820651 := bstep (se 1 (by rfl) ⟨5865488, by rfl⟩ : syracuseStep 7820651 = 11730977) B11730977
theorem B1627623 : Blo 1626512 1627623 := bstep (se 1 (by rfl) ⟨1220717, by rfl⟩ : syracuseStep 1627623 = 2441435) B2441435
theorem B4117999 : Blo 1626512 4117999 := bstep (se 1 (by rfl) ⟨3088499, by rfl⟩ : syracuseStep 4117999 = 6176999) B6176999
theorem B1627631 : Blo 1626512 1627631 := bstep (se 1 (by rfl) ⟨1220723, by rfl⟩ : syracuseStep 1627631 = 2441447) B2441447
theorem B1627739 : Blo 1626512 1627739 := bstep (se 1 (by rfl) ⟨1220804, by rfl⟩ : syracuseStep 1627739 = 2441609) B2441609
theorem B1627803 : Blo 1626512 1627803 := bstep (se 1 (by rfl) ⟨1220852, by rfl⟩ : syracuseStep 1627803 = 2441705) B2441705
theorem B1627887 : Blo 1626512 1627887 := bstep (se 1 (by rfl) ⟨1220915, by rfl⟩ : syracuseStep 1627887 = 2441831) B2441831
theorem B4118303 : Blo 1626512 4118303 := bstep (se 1 (by rfl) ⟨3088727, by rfl⟩ : syracuseStep 4118303 = 6177455) B6177455
theorem B101644091 : Blo 1626512 101644091 := bstep (se 1 (by rfl) ⟨76233068, by rfl⟩ : syracuseStep 101644091 = 152466137) B152466137
theorem B3299143 : Blo 1626512 3299143 := bstep (se 1 (by rfl) ⟨2474357, by rfl⟩ : syracuseStep 3299143 = 4948715) B4948715
theorem B1627975 : Blo 1626512 1627975 := bstep (se 1 (by rfl) ⟨1220981, by rfl⟩ : syracuseStep 1627975 = 2441963) B2441963
theorem B1627995 : Blo 1626512 1627995 := bstep (se 1 (by rfl) ⟨1220996, by rfl⟩ : syracuseStep 1627995 = 2441993) B2441993
theorem B1628063 : Blo 1626512 1628063 := bstep (se 1 (by rfl) ⟨1221047, by rfl⟩ : syracuseStep 1628063 = 2442095) B2442095
theorem B5216201 : Blo 1626512 5216201 := bstep (se 2 (by rfl) ⟨1956075, by rfl⟩ : syracuseStep 5216201 = 3912151) B3912151
theorem B41727959 : Blo 1626512 41727959 := bstep (se 1 (by rfl) ⟨31295969, by rfl⟩ : syracuseStep 41727959 = 62591939) B62591939
theorem B7821305 : Blo 1626512 7821305 := bstep (se 2 (by rfl) ⟨2932989, by rfl⟩ : syracuseStep 7821305 = 5865979) B5865979
theorem B16693289 : Blo 1626512 16693289 := bstep (se 2 (by rfl) ⟨6259983, by rfl⟩ : syracuseStep 16693289 = 12519967) B12519967
theorem B5494823 : Blo 1626512 5494823 := bstep (se 1 (by rfl) ⟨4121117, by rfl⟩ : syracuseStep 5494823 = 8242235) B8242235
theorem B1628231 : Blo 1626512 1628231 := bstep (se 1 (by rfl) ⟨1221173, by rfl⟩ : syracuseStep 1628231 = 2442347) B2442347
theorem B5494931 : Blo 1626512 5494931 := bstep (se 1 (by rfl) ⟨4121198, by rfl⟩ : syracuseStep 5494931 = 8242397) B8242397
theorem B1628391 : Blo 1626512 1628391 := bstep (se 1 (by rfl) ⟨1221293, by rfl⟩ : syracuseStep 1628391 = 2442587) B2442587
theorem B3660191 : Blo 1626512 3660191 := bstep (se 1 (by rfl) ⟨2745143, by rfl⟩ : syracuseStep 3660191 = 5490287) B5490287
theorem B5495201 : Blo 1626512 5495201 := bstep (se 2 (by rfl) ⟨2060700, by rfl⟩ : syracuseStep 5495201 = 4121401) B4121401
theorem B4118971 : Blo 1626512 4118971 := bstep (se 1 (by rfl) ⟨3089228, by rfl⟩ : syracuseStep 4118971 = 6178457) B6178457
theorem B3660263 : Blo 1626512 3660263 := bstep (se 1 (by rfl) ⟨2745197, by rfl⟩ : syracuseStep 3660263 = 5490395) B5490395
theorem B2439839 : Blo 1626512 2439839 := bstep (se 1 (by rfl) ⟨1829879, by rfl⟩ : syracuseStep 2439839 = 3659759) B3659759
theorem B10427069 : Blo 1626512 10427069 := bstep (se 3 (by rfl) ⟨1955075, by rfl⟩ : syracuseStep 10427069 = 3910151) B3910151
theorem B2439983 : Blo 1626512 2439983 := bstep (se 1 (by rfl) ⟨1829987, by rfl⟩ : syracuseStep 2439983 = 3659975) B3659975
theorem B4119407 : Blo 1626512 4119407 := bstep (se 1 (by rfl) ⟨3089555, by rfl⟩ : syracuseStep 4119407 = 6179111) B6179111
theorem B2440103 : Blo 1626512 2440103 := bstep (se 1 (by rfl) ⟨1830077, by rfl⟩ : syracuseStep 2440103 = 3660155) B3660155
theorem B216914861 : Blo 1626512 216914861 := bstep (se 3 (by rfl) ⟨40671536, by rfl⟩ : syracuseStep 216914861 = 81343073) B81343073
theorem B5495741 : Blo 1626512 5495741 := bstep (se 3 (by rfl) ⟨1030451, by rfl⟩ : syracuseStep 5495741 = 2060903) B2060903
theorem B15637529 : Blo 1626512 15637529 := bstep (se 2 (by rfl) ⟨5864073, by rfl⟩ : syracuseStep 15637529 = 11728147) B11728147
theorem B2440283 : Blo 1626512 2440283 := bstep (se 1 (by rfl) ⟨1830212, by rfl⟩ : syracuseStep 2440283 = 3660425) B3660425
theorem B6954113 : Blo 1626512 6954113 := bstep (se 2 (by rfl) ⟨2607792, by rfl⟩ : syracuseStep 6954113 = 5215585) B5215585
theorem B6175997 : Blo 1626512 6175997 := bstep (se 3 (by rfl) ⟨1157999, by rfl⟩ : syracuseStep 6175997 = 2315999) B2315999
theorem B59391265 : Blo 1626512 59391265 := bstep (se 2 (by rfl) ⟨22271724, by rfl⟩ : syracuseStep 59391265 = 44543449) B44543449
theorem B3661127 : Blo 1626512 3661127 := bstep (se 1 (by rfl) ⟨2745845, by rfl⟩ : syracuseStep 3661127 = 5491691) B5491691
theorem B3661163 : Blo 1626512 3661163 := bstep (se 1 (by rfl) ⟨2745872, by rfl⟩ : syracuseStep 3661163 = 5491745) B5491745
theorem B2440655 : Blo 1626512 2440655 := bstep (se 1 (by rfl) ⟨1830491, by rfl⟩ : syracuseStep 2440655 = 3660983) B3660983
theorem B3661289 : Blo 1626512 3661289 := bstep (se 2 (by rfl) ⟨1372983, by rfl⟩ : syracuseStep 3661289 = 2745967) B2745967
theorem B4120055 : Blo 1626512 4120055 := bstep (se 1 (by rfl) ⟨3090041, by rfl⟩ : syracuseStep 4120055 = 6180083) B6180083
theorem B1982063 : Blo 1626512 1982063 := bstep (se 1 (by rfl) ⟨1486547, by rfl⟩ : syracuseStep 1982063 = 2973095) B2973095
theorem B3661433 : Blo 1626512 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B22273699 : Blo 1626512 22273699 := bstep (se 1 (by rfl) ⟨16705274, by rfl⟩ : syracuseStep 22273699 = 33410549) B33410549
theorem B10714799 : Blo 1626512 10714799 := bstep (se 1 (by rfl) ⟨8036099, by rfl⟩ : syracuseStep 10714799 = 16072199) B16072199
theorem B9273041 : Blo 1626512 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B2441039 : Blo 1626512 2441039 := bstep (se 1 (by rfl) ⟨1830779, by rfl⟩ : syracuseStep 2441039 = 3661559) B3661559
theorem B2441159 : Blo 1626512 2441159 := bstep (se 1 (by rfl) ⟨1830869, by rfl⟩ : syracuseStep 2441159 = 3661739) B3661739
theorem B15056869 : Blo 1626512 15056869 := bstep (se 4 (by rfl) ⟨1411581, by rfl⟩ : syracuseStep 15056869 = 2823163) B2823163
theorem B3711071 : Blo 1626512 3711071 := bstep (se 1 (by rfl) ⟨2783303, by rfl⟩ : syracuseStep 3711071 = 5566607) B5566607
theorem B2441423 : Blo 1626512 2441423 := bstep (se 1 (by rfl) ⟨1831067, by rfl⟩ : syracuseStep 2441423 = 3662135) B3662135
theorem B80306639 : Blo 1626512 80306639 := bstep (se 1 (by rfl) ⟨60229979, by rfl⟩ : syracuseStep 80306639 = 120459959) B120459959
theorem B4637159 : Blo 1626512 4637159 := bstep (se 1 (by rfl) ⟨3477869, by rfl⟩ : syracuseStep 4637159 = 6955739) B6955739
theorem B2744975 : Blo 1626512 2744975 := bstep (se 1 (by rfl) ⟨2058731, by rfl⟩ : syracuseStep 2744975 = 4117463) B4117463
theorem B48243383 : Blo 1626512 48243383 := bstep (se 1 (by rfl) ⟨36182537, by rfl⟩ : syracuseStep 48243383 = 72365075) B72365075
theorem B3662675 : Blo 1626512 3662675 := bstep (se 1 (by rfl) ⟨2747006, by rfl⟩ : syracuseStep 3662675 = 5494013) B5494013
theorem B2442107 : Blo 1626512 2442107 := bstep (se 1 (by rfl) ⟨1831580, by rfl⟩ : syracuseStep 2442107 = 3663161) B3663161
theorem B2442233 : Blo 1626512 2442233 := bstep (se 2 (by rfl) ⟨915837, by rfl⟩ : syracuseStep 2442233 = 1831675) B1831675
theorem B7046153 : Blo 1626512 7046153 := bstep (se 2 (by rfl) ⟨2642307, by rfl⟩ : syracuseStep 7046153 = 5284615) B5284615
theorem B2442287 : Blo 1626512 2442287 := bstep (se 1 (by rfl) ⟨1831715, by rfl⟩ : syracuseStep 2442287 = 3663431) B3663431
theorem B6947963 : Blo 1626512 6947963 := bstep (se 1 (by rfl) ⟨5210972, by rfl⟩ : syracuseStep 6947963 = 10421945) B10421945
theorem B2442407 : Blo 1626512 2442407 := bstep (se 1 (by rfl) ⟨1831805, by rfl⟩ : syracuseStep 2442407 = 3663611) B3663611
theorem B2745535 : Blo 1626512 2745535 := bstep (se 1 (by rfl) ⟨2059151, by rfl⟩ : syracuseStep 2745535 = 4118303) B4118303
theorem B2442599 : Blo 1626512 2442599 := bstep (se 1 (by rfl) ⟨1831949, by rfl⟩ : syracuseStep 2442599 = 3663899) B3663899
theorem B3663215 : Blo 1626512 3663215 := bstep (se 1 (by rfl) ⟨2747411, by rfl⟩ : syracuseStep 3663215 = 5494823) B5494823
theorem B3663287 : Blo 1626512 3663287 := bstep (se 1 (by rfl) ⟨2747465, by rfl⟩ : syracuseStep 3663287 = 5494931) B5494931
theorem B2606665 : Blo 1626512 2606665 := bstep (se 2 (by rfl) ⟨977499, by rfl⟩ : syracuseStep 2606665 = 1954999) B1954999
theorem B3663467 : Blo 1626512 3663467 := bstep (se 1 (by rfl) ⟨2747600, by rfl⟩ : syracuseStep 3663467 = 5495201) B5495201
theorem B5285501 : Blo 1626512 5285501 := bstep (se 3 (by rfl) ⟨991031, by rfl⟩ : syracuseStep 5285501 = 1982063) B1982063
theorem B35178137 : Blo 1626512 35178137 := bstep (se 2 (by rfl) ⟨13191801, by rfl⟩ : syracuseStep 35178137 = 26383603) B26383603
theorem B27805517 : Blo 1626512 27805517 := bstep (se 3 (by rfl) ⟨5213534, by rfl⟩ : syracuseStep 27805517 = 10427069) B10427069
theorem B3663737 : Blo 1626512 3663737 := bstep (se 2 (by rfl) ⟨1373901, by rfl⟩ : syracuseStep 3663737 = 2747803) B2747803
theorem B2746271 : Blo 1626512 2746271 := bstep (se 1 (by rfl) ⟨2059703, by rfl⟩ : syracuseStep 2746271 = 4119407) B4119407
theorem B3663827 : Blo 1626512 3663827 := bstep (se 1 (by rfl) ⟨2747870, by rfl⟩ : syracuseStep 3663827 = 5495741) B5495741
theorem B5490665 : Blo 1626512 5490665 := bstep (se 2 (by rfl) ⟨2058999, by rfl⟩ : syracuseStep 5490665 = 4117999) B4117999
theorem B29698265 : Blo 1626512 29698265 := bstep (se 2 (by rfl) ⟨11136849, by rfl⟩ : syracuseStep 29698265 = 22273699) B22273699
theorem B2746703 : Blo 1626512 2746703 := bstep (se 1 (by rfl) ⟨2060027, by rfl⟩ : syracuseStep 2746703 = 4120055) B4120055
theorem B578439629 : Blo 1626512 578439629 := bstep (se 3 (by rfl) ⟨108457430, by rfl⟩ : syracuseStep 578439629 = 216914861) B216914861
theorem B5491151 : Blo 1626512 5491151 := bstep (se 1 (by rfl) ⟨4118363, by rfl⟩ : syracuseStep 5491151 = 8236727) B8236727
theorem B18541385 : Blo 1626512 18541385 := bstep (se 2 (by rfl) ⟨6953019, by rfl⟩ : syracuseStep 18541385 = 13906039) B13906039
theorem B21146665 : Blo 1626512 21146665 := bstep (se 2 (by rfl) ⟨7929999, by rfl⟩ : syracuseStep 21146665 = 15859999) B15859999
theorem B21146777 : Blo 1626512 21146777 := bstep (se 2 (by rfl) ⟨7930041, by rfl⟩ : syracuseStep 21146777 = 15860083) B15860083
theorem B8236241 : Blo 1626512 8236241 := bstep (se 2 (by rfl) ⟨3088590, by rfl⟩ : syracuseStep 8236241 = 6177181) B6177181
theorem B5491961 : Blo 1626512 5491961 := bstep (se 2 (by rfl) ⟨2059485, by rfl⟩ : syracuseStep 5491961 = 4118971) B4118971
theorem B7425407 : Blo 1626512 7425407 := bstep (se 1 (by rfl) ⟨5569055, by rfl⟩ : syracuseStep 7425407 = 11138111) B11138111
theorem B5492123 : Blo 1626512 5492123 := bstep (se 1 (by rfl) ⟨4119092, by rfl⟩ : syracuseStep 5492123 = 8238185) B8238185
theorem B6180371 : Blo 1626512 6180371 := bstep (se 1 (by rfl) ⟨4635278, by rfl⟩ : syracuseStep 6180371 = 9270557) B9270557
theorem B5213767 : Blo 1626512 5213767 := bstep (se 1 (by rfl) ⟨3910325, by rfl⟩ : syracuseStep 5213767 = 7820651) B7820651
theorem B6950681 : Blo 1626512 6950681 := bstep (se 2 (by rfl) ⟨2606505, by rfl⟩ : syracuseStep 6950681 = 5213011) B5213011
theorem B400977701 : Blo 1626512 400977701 := bstep (se 4 (by rfl) ⟨37591659, by rfl⟩ : syracuseStep 400977701 = 75183319) B75183319
theorem B3477467 : Blo 1626512 3477467 := bstep (se 1 (by rfl) ⟨2608100, by rfl⟩ : syracuseStep 3477467 = 5216201) B5216201
theorem B5214203 : Blo 1626512 5214203 := bstep (se 1 (by rfl) ⟨3910652, by rfl⟩ : syracuseStep 5214203 = 7821305) B7821305
theorem B11128859 : Blo 1626512 11128859 := bstep (se 1 (by rfl) ⟨8346644, by rfl⟩ : syracuseStep 11128859 = 16693289) B16693289
theorem B4632659 : Blo 1626512 4632659 := bstep (se 1 (by rfl) ⟨3474494, by rfl⟩ : syracuseStep 4632659 = 6948989) B6948989
theorem B79188353 : Blo 1626512 79188353 := bstep (se 2 (by rfl) ⟨29695632, by rfl⟩ : syracuseStep 79188353 = 59391265) B59391265
theorem B11727287 : Blo 1626512 11727287 := bstep (se 1 (by rfl) ⟨8795465, by rfl⟩ : syracuseStep 11727287 = 17590931) B17590931
theorem B1626559 : Blo 1626512 1626559 := bstep (se 1 (by rfl) ⟨1219919, by rfl⟩ : syracuseStep 1626559 = 2439839) B2439839
theorem B1626655 : Blo 1626512 1626655 := bstep (se 1 (by rfl) ⟨1219991, by rfl⟩ : syracuseStep 1626655 = 2439983) B2439983
theorem B3912247 : Blo 1626512 3912247 := bstep (se 1 (by rfl) ⟨2934185, by rfl⟩ : syracuseStep 3912247 = 5868371) B5868371
theorem B1626735 : Blo 1626512 1626735 := bstep (se 1 (by rfl) ⟨1220051, by rfl⟩ : syracuseStep 1626735 = 2440103) B2440103
theorem B10425019 : Blo 1626512 10425019 := bstep (se 1 (by rfl) ⟨7818764, by rfl⟩ : syracuseStep 10425019 = 15637529) B15637529
theorem B1626855 : Blo 1626512 1626855 := bstep (se 1 (by rfl) ⟨1220141, by rfl⟩ : syracuseStep 1626855 = 2440283) B2440283
theorem B4117331 : Blo 1626512 4117331 := bstep (se 1 (by rfl) ⟨3087998, by rfl⟩ : syracuseStep 4117331 = 6175997) B6175997
theorem B1627103 : Blo 1626512 1627103 := bstep (se 1 (by rfl) ⟨1220327, by rfl⟩ : syracuseStep 1627103 = 2440655) B2440655
theorem B52761617 : Blo 1626512 52761617 := bstep (se 2 (by rfl) ⟨19785606, by rfl⟩ : syracuseStep 52761617 = 39571213) B39571213
theorem B14840891 : Blo 1626512 14840891 := bstep (se 1 (by rfl) ⟨11130668, by rfl⟩ : syracuseStep 14840891 = 22261337) B22261337
theorem B6182027 : Blo 1626512 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B1627359 : Blo 1626512 1627359 := bstep (se 1 (by rfl) ⟨1220519, by rfl⟩ : syracuseStep 1627359 = 2441039) B2441039
theorem B1627439 : Blo 1626512 1627439 := bstep (se 1 (by rfl) ⟨1220579, by rfl⟩ : syracuseStep 1627439 = 2441159) B2441159
theorem B20075825 : Blo 1626512 20075825 := bstep (se 2 (by rfl) ⟨7528434, by rfl⟩ : syracuseStep 20075825 = 15056869) B15056869
theorem B10434041 : Blo 1626512 10434041 := bstep (se 2 (by rfl) ⟨3912765, by rfl⟩ : syracuseStep 10434041 = 7825531) B7825531
theorem B1627679 : Blo 1626512 1627679 := bstep (se 1 (by rfl) ⟨1220759, by rfl⟩ : syracuseStep 1627679 = 2441519) B2441519
theorem B9270875 : Blo 1626512 9270875 := bstep (se 1 (by rfl) ⟨6953156, by rfl⟩ : syracuseStep 9270875 = 13906313) B13906313
theorem B18544301 : Blo 1626512 18544301 := bstep (se 3 (by rfl) ⟨3477056, by rfl⟩ : syracuseStep 18544301 = 6954113) B6954113
theorem B1627839 : Blo 1626512 1627839 := bstep (se 1 (by rfl) ⟨1220879, by rfl⟩ : syracuseStep 1627839 = 2441759) B2441759
theorem B5863151 : Blo 1626512 5863151 := bstep (se 1 (by rfl) ⟨4397363, by rfl⟩ : syracuseStep 5863151 = 8794727) B8794727
theorem B6600571 : Blo 1626512 6600571 := bstep (se 1 (by rfl) ⟨4950428, by rfl⟩ : syracuseStep 6600571 = 9900857) B9900857
theorem B10426249 : Blo 1626512 10426249 := bstep (se 2 (by rfl) ⟨3909843, by rfl⟩ : syracuseStep 10426249 = 7819687) B7819687
theorem B4397095 : Blo 1626512 4397095 := bstep (se 1 (by rfl) ⟨3297821, by rfl⟩ : syracuseStep 4397095 = 6595643) B6595643
theorem B3659903 : Blo 1626512 3659903 := bstep (se 1 (by rfl) ⟨2744927, by rfl⟩ : syracuseStep 3659903 = 5489855) B5489855
theorem B1628287 : Blo 1626512 1628287 := bstep (se 1 (by rfl) ⟨1221215, by rfl⟩ : syracuseStep 1628287 = 2442431) B2442431
theorem B8239319 : Blo 1626512 8239319 := bstep (se 1 (by rfl) ⟨6179489, by rfl⟩ : syracuseStep 8239319 = 12358979) B12358979
theorem B1628383 : Blo 1626512 1628383 := bstep (se 1 (by rfl) ⟨1221287, by rfl⟩ : syracuseStep 1628383 = 2442575) B2442575
theorem B3660011 : Blo 1626512 3660011 := bstep (se 1 (by rfl) ⟨2745008, by rfl⟩ : syracuseStep 3660011 = 5490017) B5490017
theorem B1628443 : Blo 1626512 1628443 := bstep (se 1 (by rfl) ⟨1221332, by rfl⟩ : syracuseStep 1628443 = 2442665) B2442665
theorem B67762727 : Blo 1626512 67762727 := bstep (se 1 (by rfl) ⟨50822045, by rfl⟩ : syracuseStep 67762727 = 101644091) B101644091
theorem B27818639 : Blo 1626512 27818639 := bstep (se 1 (by rfl) ⟨20863979, by rfl⟩ : syracuseStep 27818639 = 41727959) B41727959
theorem B3660479 : Blo 1626512 3660479 := bstep (se 1 (by rfl) ⟨2745359, by rfl⟩ : syracuseStep 3660479 = 5490719) B5490719
theorem B2440127 : Blo 1626512 2440127 := bstep (se 1 (by rfl) ⟨1830095, by rfl⟩ : syracuseStep 2440127 = 3660191) B3660191
theorem B2440175 : Blo 1626512 2440175 := bstep (se 1 (by rfl) ⟨1830131, by rfl⟩ : syracuseStep 2440175 = 3660263) B3660263
theorem B4119599 : Blo 1626512 4119599 := bstep (se 1 (by rfl) ⟨3089699, by rfl⟩ : syracuseStep 4119599 = 6179399) B6179399
theorem B28572797 : Blo 1626512 28572797 := bstep (se 3 (by rfl) ⟨5357399, by rfl⟩ : syracuseStep 28572797 = 10714799) B10714799
theorem B2440361 : Blo 1626512 2440361 := bstep (se 2 (by rfl) ⟨915135, by rfl⟩ : syracuseStep 2440361 = 1830271) B1830271
theorem B2440751 : Blo 1626512 2440751 := bstep (se 1 (by rfl) ⟨1830563, by rfl⟩ : syracuseStep 2440751 = 3661127) B3661127
theorem B2440775 : Blo 1626512 2440775 := bstep (se 1 (by rfl) ⟨1830581, by rfl⟩ : syracuseStep 2440775 = 3661163) B3661163
theorem B2440859 : Blo 1626512 2440859 := bstep (se 1 (by rfl) ⟨1830644, by rfl⟩ : syracuseStep 2440859 = 3661289) B3661289
theorem B2440955 : Blo 1626512 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B4398857 : Blo 1626512 4398857 := bstep (se 2 (by rfl) ⟨1649571, by rfl⟩ : syracuseStep 4398857 = 3299143) B3299143
theorem B3088439 : Blo 1626512 3088439 := bstep (se 1 (by rfl) ⟨2316329, by rfl⟩ : syracuseStep 3088439 = 4632659) B4632659
theorem B2474047 : Blo 1626512 2474047 := bstep (se 1 (by rfl) ⟨1855535, by rfl⟩ : syracuseStep 2474047 = 3711071) B3711071
theorem B32162255 : Blo 1626512 32162255 := bstep (se 1 (by rfl) ⟨24121691, by rfl⟩ : syracuseStep 32162255 = 48243383) B48243383
theorem B2744887 : Blo 1626512 2744887 := bstep (se 1 (by rfl) ⟨2058665, by rfl⟩ : syracuseStep 2744887 = 4117331) B4117331
theorem B2441783 : Blo 1626512 2441783 := bstep (se 1 (by rfl) ⟨1831337, by rfl⟩ : syracuseStep 2441783 = 3662675) B3662675
theorem B4121351 : Blo 1626512 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B2442143 : Blo 1626512 2442143 := bstep (se 1 (by rfl) ⟨1831607, by rfl⟩ : syracuseStep 2442143 = 3663215) B3663215
theorem B2442191 : Blo 1626512 2442191 := bstep (se 1 (by rfl) ⟨1831643, by rfl⟩ : syracuseStep 2442191 = 3663287) B3663287
theorem B6956027 : Blo 1626512 6956027 := bstep (se 1 (by rfl) ⟨5217020, by rfl⟩ : syracuseStep 6956027 = 10434041) B10434041
theorem B2442311 : Blo 1626512 2442311 := bstep (se 1 (by rfl) ⟨1831733, by rfl⟩ : syracuseStep 2442311 = 3663467) B3663467
theorem B3523667 : Blo 1626512 3523667 := bstep (se 1 (by rfl) ⟨2642750, by rfl⟩ : syracuseStep 3523667 = 5285501) B5285501
theorem B12362867 : Blo 1626512 12362867 := bstep (se 1 (by rfl) ⟨9272150, by rfl⟩ : syracuseStep 12362867 = 18544301) B18544301
theorem B2442491 : Blo 1626512 2442491 := bstep (se 1 (by rfl) ⟨1831868, by rfl⟩ : syracuseStep 2442491 = 3663737) B3663737
theorem B2442551 : Blo 1626512 2442551 := bstep (se 1 (by rfl) ⟨1831913, by rfl⟩ : syracuseStep 2442551 = 3663827) B3663827
theorem B35203045 : Blo 1626512 35203045 := bstep (se 4 (by rfl) ⟨3300285, by rfl⟩ : syracuseStep 35203045 = 6600571) B6600571
theorem B2746399 : Blo 1626512 2746399 := bstep (se 1 (by rfl) ⟨2059799, by rfl⟩ : syracuseStep 2746399 = 4119599) B4119599
theorem B19048531 : Blo 1626512 19048531 := bstep (se 1 (by rfl) ⟨14286398, by rfl⟩ : syracuseStep 19048531 = 28572797) B28572797
theorem B3475553 : Blo 1626512 3475553 := bstep (se 2 (by rfl) ⟨1303332, by rfl⟩ : syracuseStep 3475553 = 2606665) B2606665
theorem B5490827 : Blo 1626512 5490827 := bstep (se 1 (by rfl) ⟨4118120, by rfl⟩ : syracuseStep 5490827 = 8236241) B8236241
theorem B4950271 : Blo 1626512 4950271 := bstep (se 1 (by rfl) ⟨3712703, by rfl⟩ : syracuseStep 4950271 = 7425407) B7425407
theorem B3476135 : Blo 1626512 3476135 := bstep (se 1 (by rfl) ⟨2607101, by rfl⟩ : syracuseStep 3476135 = 5214203) B5214203
theorem B52792235 : Blo 1626512 52792235 := bstep (se 1 (by rfl) ⟨39594176, by rfl⟩ : syracuseStep 52792235 = 79188353) B79188353
theorem B7818191 : Blo 1626512 7818191 := bstep (se 1 (by rfl) ⟨5863643, by rfl⟩ : syracuseStep 7818191 = 11727287) B11727287
theorem B53537759 : Blo 1626512 53537759 := bstep (se 1 (by rfl) ⟨40153319, by rfl⟩ : syracuseStep 53537759 = 80306639) B80306639
theorem B3091439 : Blo 1626512 3091439 := bstep (se 1 (by rfl) ⟨2318579, by rfl⟩ : syracuseStep 3091439 = 4637159) B4637159
theorem B1829983 : Blo 1626512 1829983 := bstep (se 1 (by rfl) ⟨1372487, by rfl⟩ : syracuseStep 1829983 = 2744975) B2744975
theorem B4697435 : Blo 1626512 4697435 := bstep (se 1 (by rfl) ⟨3523076, by rfl⟩ : syracuseStep 4697435 = 7046153) B7046153
theorem B4631975 : Blo 1626512 4631975 := bstep (se 1 (by rfl) ⟨3473981, by rfl⟩ : syracuseStep 4631975 = 6947963) B6947963
theorem B6180583 : Blo 1626512 6180583 := bstep (se 1 (by rfl) ⟨4635437, by rfl⟩ : syracuseStep 6180583 = 9270875) B9270875
theorem B1830847 : Blo 1626512 1830847 := bstep (se 1 (by rfl) ⟨1373135, by rfl⟩ : syracuseStep 1830847 = 2746271) B2746271
theorem B5492879 : Blo 1626512 5492879 := bstep (se 1 (by rfl) ⟨4119659, by rfl⟩ : syracuseStep 5492879 = 8239319) B8239319
theorem B1831135 : Blo 1626512 1831135 := bstep (se 1 (by rfl) ⟨1373351, by rfl⟩ : syracuseStep 1831135 = 2746703) B2746703
theorem B385626419 : Blo 1626512 385626419 := bstep (se 1 (by rfl) ⟨289219814, by rfl⟩ : syracuseStep 385626419 = 578439629) B578439629
theorem B45175151 : Blo 1626512 45175151 := bstep (se 1 (by rfl) ⟨33881363, by rfl⟩ : syracuseStep 45175151 = 67762727) B67762727
theorem B15635069 : Blo 1626512 15635069 := bstep (se 3 (by rfl) ⟨2931575, by rfl⟩ : syracuseStep 15635069 = 5863151) B5863151
theorem B1626751 : Blo 1626512 1626751 := bstep (se 1 (by rfl) ⟨1220063, by rfl⟩ : syracuseStep 1626751 = 2440127) B2440127
theorem B1626783 : Blo 1626512 1626783 := bstep (se 1 (by rfl) ⟨1220087, by rfl⟩ : syracuseStep 1626783 = 2440175) B2440175
theorem B6951689 : Blo 1626512 6951689 := bstep (se 2 (by rfl) ⟨2606883, by rfl⟩ : syracuseStep 6951689 = 5213767) B5213767
theorem B1626907 : Blo 1626512 1626907 := bstep (se 1 (by rfl) ⟨1220180, by rfl⟩ : syracuseStep 1626907 = 2440361) B2440361
theorem B1627167 : Blo 1626512 1627167 := bstep (se 1 (by rfl) ⟨1220375, by rfl⟩ : syracuseStep 1627167 = 2440751) B2440751
theorem B1627183 : Blo 1626512 1627183 := bstep (se 1 (by rfl) ⟨1220387, by rfl⟩ : syracuseStep 1627183 = 2440775) B2440775
theorem B1627239 : Blo 1626512 1627239 := bstep (se 1 (by rfl) ⟨1220429, by rfl⟩ : syracuseStep 1627239 = 2440859) B2440859
theorem B1627303 : Blo 1626512 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B4633787 : Blo 1626512 4633787 := bstep (se 1 (by rfl) ⟨3475340, by rfl⟩ : syracuseStep 4633787 = 6950681) B6950681
theorem B267318467 : Blo 1626512 267318467 := bstep (se 1 (by rfl) ⟨200488850, by rfl⟩ : syracuseStep 267318467 = 400977701) B400977701
theorem B7419239 : Blo 1626512 7419239 := bstep (se 1 (by rfl) ⟨5564429, by rfl⟩ : syracuseStep 7419239 = 11128859) B11128859
theorem B5862793 : Blo 1626512 5862793 := bstep (se 2 (by rfl) ⟨2198547, by rfl⟩ : syracuseStep 5862793 = 4397095) B4397095
theorem B1627615 : Blo 1626512 1627615 := bstep (se 1 (by rfl) ⟨1220711, by rfl⟩ : syracuseStep 1627615 = 2441423) B2441423
theorem B1628071 : Blo 1626512 1628071 := bstep (se 1 (by rfl) ⟨1221053, by rfl⟩ : syracuseStep 1628071 = 2442107) B2442107
theorem B1628155 : Blo 1626512 1628155 := bstep (se 1 (by rfl) ⟨1221116, by rfl⟩ : syracuseStep 1628155 = 2442233) B2442233
theorem B35174411 : Blo 1626512 35174411 := bstep (se 1 (by rfl) ⟨26380808, by rfl⟩ : syracuseStep 35174411 = 52761617) B52761617
theorem B1628191 : Blo 1626512 1628191 := bstep (se 1 (by rfl) ⟨1221143, by rfl⟩ : syracuseStep 1628191 = 2442287) B2442287
theorem B9893927 : Blo 1626512 9893927 := bstep (se 1 (by rfl) ⟨7420445, by rfl⟩ : syracuseStep 9893927 = 14840891) B14840891
theorem B5216329 : Blo 1626512 5216329 := bstep (se 2 (by rfl) ⟨1956123, by rfl⟩ : syracuseStep 5216329 = 3912247) B3912247
theorem B1628271 : Blo 1626512 1628271 := bstep (se 1 (by rfl) ⟨1221203, by rfl⟩ : syracuseStep 1628271 = 2442407) B2442407
theorem B13383883 : Blo 1626512 13383883 := bstep (se 1 (by rfl) ⟨10037912, by rfl⟩ : syracuseStep 13383883 = 20075825) B20075825
theorem B1628399 : Blo 1626512 1628399 := bstep (se 1 (by rfl) ⟨1221299, by rfl⟩ : syracuseStep 1628399 = 2442599) B2442599
theorem B13900025 : Blo 1626512 13900025 := bstep (se 2 (by rfl) ⟨5212509, by rfl⟩ : syracuseStep 13900025 = 10425019) B10425019
theorem B23452091 : Blo 1626512 23452091 := bstep (se 1 (by rfl) ⟨17589068, by rfl⟩ : syracuseStep 23452091 = 35178137) B35178137
theorem B18537011 : Blo 1626512 18537011 := bstep (se 1 (by rfl) ⟨13902758, by rfl⟩ : syracuseStep 18537011 = 27805517) B27805517
theorem B3660443 : Blo 1626512 3660443 := bstep (se 1 (by rfl) ⟨2745332, by rfl⟩ : syracuseStep 3660443 = 5490665) B5490665
theorem B28195553 : Blo 1626512 28195553 := bstep (se 2 (by rfl) ⟨10573332, by rfl⟩ : syracuseStep 28195553 = 21146665) B21146665
theorem B2439935 : Blo 1626512 2439935 := bstep (se 1 (by rfl) ⟨1829951, by rfl⟩ : syracuseStep 2439935 = 3659903) B3659903
theorem B19798843 : Blo 1626512 19798843 := bstep (se 1 (by rfl) ⟨14849132, by rfl⟩ : syracuseStep 19798843 = 29698265) B29698265
theorem B2440007 : Blo 1626512 2440007 := bstep (se 1 (by rfl) ⟨1830005, by rfl⟩ : syracuseStep 2440007 = 3660011) B3660011
theorem B3660713 : Blo 1626512 3660713 := bstep (se 2 (by rfl) ⟨1372767, by rfl⟩ : syracuseStep 3660713 = 2745535) B2745535
theorem B3660767 : Blo 1626512 3660767 := bstep (se 1 (by rfl) ⟨2745575, by rfl⟩ : syracuseStep 3660767 = 5491151) B5491151
theorem B18545759 : Blo 1626512 18545759 := bstep (se 1 (by rfl) ⟨13909319, by rfl⟩ : syracuseStep 18545759 = 27818639) B27818639
theorem B2440319 : Blo 1626512 2440319 := bstep (se 1 (by rfl) ⟨1830239, by rfl⟩ : syracuseStep 2440319 = 3660479) B3660479
theorem B12360923 : Blo 1626512 12360923 := bstep (se 1 (by rfl) ⟨9270692, by rfl⟩ : syracuseStep 12360923 = 18541385) B18541385
theorem B14097851 : Blo 1626512 14097851 := bstep (se 1 (by rfl) ⟨10573388, by rfl⟩ : syracuseStep 14097851 = 21146777) B21146777
theorem B3661307 : Blo 1626512 3661307 := bstep (se 1 (by rfl) ⟨2745980, by rfl⟩ : syracuseStep 3661307 = 5491961) B5491961
theorem B3661415 : Blo 1626512 3661415 := bstep (se 1 (by rfl) ⟨2746061, by rfl⟩ : syracuseStep 3661415 = 5492123) B5492123
theorem B4120247 : Blo 1626512 4120247 := bstep (se 1 (by rfl) ⟨3090185, by rfl⟩ : syracuseStep 4120247 = 6180371) B6180371
theorem B2932571 : Blo 1626512 2932571 := bstep (se 1 (by rfl) ⟨2199428, by rfl⟩ : syracuseStep 2932571 = 4398857) B4398857
theorem B13901665 : Blo 1626512 13901665 := bstep (se 2 (by rfl) ⟨5213124, by rfl⟩ : syracuseStep 13901665 = 10426249) B10426249
theorem B2318311 : Blo 1626512 2318311 := bstep (se 1 (by rfl) ⟨1738733, by rfl⟩ : syracuseStep 2318311 = 3477467) B3477467
theorem B3661865 : Blo 1626512 3661865 := bstep (se 2 (by rfl) ⟨1373199, by rfl⟩ : syracuseStep 3661865 = 2746399) B2746399
theorem B3661919 : Blo 1626512 3661919 := bstep (se 1 (by rfl) ⟨2746439, by rfl⟩ : syracuseStep 3661919 = 5492879) B5492879
theorem B6955105 : Blo 1626512 6955105 := bstep (se 2 (by rfl) ⟨2608164, by rfl⟩ : syracuseStep 6955105 = 5216329) B5216329
theorem B9396445 : Blo 1626512 9396445 := bstep (se 3 (by rfl) ⟨1761833, by rfl⟩ : syracuseStep 9396445 = 3523667) B3523667
theorem B2441513 : Blo 1626512 2441513 := bstep (se 2 (by rfl) ⟨915567, by rfl⟩ : syracuseStep 2441513 = 1831135) B1831135
theorem B4637351 : Blo 1626512 4637351 := bstep (se 1 (by rfl) ⟨3478013, by rfl⟩ : syracuseStep 4637351 = 6956027) B6956027
theorem B8241911 : Blo 1626512 8241911 := bstep (se 1 (by rfl) ⟨6181433, by rfl⟩ : syracuseStep 8241911 = 12362867) B12362867
theorem B3089191 : Blo 1626512 3089191 := bstep (se 1 (by rfl) ⟨2316893, by rfl⟩ : syracuseStep 3089191 = 4633787) B4633787
theorem B6595951 : Blo 1626512 6595951 := bstep (se 1 (by rfl) ⟨4946963, by rfl⟩ : syracuseStep 6595951 = 9893927) B9893927
theorem B9266683 : Blo 1626512 9266683 := bstep (se 1 (by rfl) ⟨6950012, by rfl⟩ : syracuseStep 9266683 = 13900025) B13900025
theorem B7817057 : Blo 1626512 7817057 := bstep (se 2 (by rfl) ⟨2931396, by rfl⟩ : syracuseStep 7817057 = 5862793) B5862793
theorem B35194823 : Blo 1626512 35194823 := bstep (se 1 (by rfl) ⟨26396117, by rfl⟩ : syracuseStep 35194823 = 52792235) B52792235
theorem B5212127 : Blo 1626512 5212127 := bstep (se 1 (by rfl) ⟨3909095, by rfl⟩ : syracuseStep 5212127 = 7818191) B7818191
theorem B12363839 : Blo 1626512 12363839 := bstep (se 1 (by rfl) ⟨9272879, by rfl⟩ : syracuseStep 12363839 = 18545759) B18545759
theorem B3131623 : Blo 1626512 3131623 := bstep (se 1 (by rfl) ⟨2348717, by rfl⟩ : syracuseStep 3131623 = 4697435) B4697435
theorem B9398567 : Blo 1626512 9398567 := bstep (se 1 (by rfl) ⟨7048925, by rfl⟩ : syracuseStep 9398567 = 14097851) B14097851
theorem B2746831 : Blo 1626512 2746831 := bstep (se 1 (by rfl) ⟨2060123, by rfl⟩ : syracuseStep 2746831 = 4120247) B4120247
theorem B12364325 : Blo 1626512 12364325 := bstep (se 4 (by rfl) ⟨1159155, by rfl⟩ : syracuseStep 12364325 = 2318311) B2318311
theorem B2058959 : Blo 1626512 2058959 := bstep (se 1 (by rfl) ⟨1544219, by rfl⟩ : syracuseStep 2058959 = 3088439) B3088439
theorem B25398041 : Blo 1626512 25398041 := bstep (se 2 (by rfl) ⟨9524265, by rfl⟩ : syracuseStep 25398041 = 19048531) B19048531
theorem B257084279 : Blo 1626512 257084279 := bstep (se 1 (by rfl) ⟨192813209, by rfl⟩ : syracuseStep 257084279 = 385626419) B385626419
theorem B30116767 : Blo 1626512 30116767 := bstep (se 1 (by rfl) ⟨22587575, by rfl⟩ : syracuseStep 30116767 = 45175151) B45175151
theorem B9268141 : Blo 1626512 9268141 := bstep (se 3 (by rfl) ⟨1737776, by rfl⟩ : syracuseStep 9268141 = 3475553) B3475553
theorem B21441503 : Blo 1626512 21441503 := bstep (se 1 (by rfl) ⟨16081127, by rfl⟩ : syracuseStep 21441503 = 32162255) B32162255
theorem B10423379 : Blo 1626512 10423379 := bstep (se 1 (by rfl) ⟨7817534, by rfl⟩ : syracuseStep 10423379 = 15635069) B15635069
theorem B2747567 : Blo 1626512 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B178212311 : Blo 1626512 178212311 := bstep (se 1 (by rfl) ⟨133659233, by rfl⟩ : syracuseStep 178212311 = 267318467) B267318467
theorem B71380709 : Blo 1626512 71380709 := bstep (se 4 (by rfl) ⟨6691941, by rfl⟩ : syracuseStep 71380709 = 13383883) B13383883
theorem B26398457 : Blo 1626512 26398457 := bstep (se 2 (by rfl) ⟨9899421, by rfl⟩ : syracuseStep 26398457 = 19798843) B19798843
theorem B23449607 : Blo 1626512 23449607 := bstep (se 1 (by rfl) ⟨17587205, by rfl⟩ : syracuseStep 23449607 = 35174411) B35174411
theorem B15634727 : Blo 1626512 15634727 := bstep (se 1 (by rfl) ⟨11726045, by rfl⟩ : syracuseStep 15634727 = 23452091) B23452091
theorem B12358007 : Blo 1626512 12358007 := bstep (se 1 (by rfl) ⟨9268505, by rfl⟩ : syracuseStep 12358007 = 18537011) B18537011
theorem B18797035 : Blo 1626512 18797035 := bstep (se 1 (by rfl) ⟨14097776, by rfl⟩ : syracuseStep 18797035 = 28195553) B28195553
theorem B1626623 : Blo 1626512 1626623 := bstep (se 1 (by rfl) ⟨1219967, by rfl⟩ : syracuseStep 1626623 = 2439935) B2439935
theorem B1626671 : Blo 1626512 1626671 := bstep (se 1 (by rfl) ⟨1220003, by rfl⟩ : syracuseStep 1626671 = 2440007) B2440007
theorem B2060959 : Blo 1626512 2060959 := bstep (se 1 (by rfl) ⟨1545719, by rfl⟩ : syracuseStep 2060959 = 3091439) B3091439
theorem B1626879 : Blo 1626512 1626879 := bstep (se 1 (by rfl) ⟨1220159, by rfl⟩ : syracuseStep 1626879 = 2440319) B2440319
theorem B7820189 : Blo 1626512 7820189 := bstep (se 3 (by rfl) ⟨1466285, by rfl⟩ : syracuseStep 7820189 = 2932571) B2932571
theorem B18535553 : Blo 1626512 18535553 := bstep (se 2 (by rfl) ⟨6950832, by rfl⟩ : syracuseStep 18535553 = 13901665) B13901665
theorem B46937393 : Blo 1626512 46937393 := bstep (se 2 (by rfl) ⟨17601522, by rfl⟩ : syracuseStep 46937393 = 35203045) B35203045
theorem B3298729 : Blo 1626512 3298729 := bstep (se 2 (by rfl) ⟨1237023, by rfl⟩ : syracuseStep 3298729 = 2474047) B2474047
theorem B6600361 : Blo 1626512 6600361 := bstep (se 2 (by rfl) ⟨2475135, by rfl⟩ : syracuseStep 6600361 = 4950271) B4950271
theorem B1627855 : Blo 1626512 1627855 := bstep (se 1 (by rfl) ⟨1220891, by rfl⟩ : syracuseStep 1627855 = 2441783) B2441783
theorem B4634459 : Blo 1626512 4634459 := bstep (se 1 (by rfl) ⟨3475844, by rfl⟩ : syracuseStep 4634459 = 6951689) B6951689
theorem B1628095 : Blo 1626512 1628095 := bstep (se 1 (by rfl) ⟨1221071, by rfl⟩ : syracuseStep 1628095 = 2442143) B2442143
theorem B1628127 : Blo 1626512 1628127 := bstep (se 1 (by rfl) ⟨1221095, by rfl⟩ : syracuseStep 1628127 = 2442191) B2442191
theorem B1628207 : Blo 1626512 1628207 := bstep (se 1 (by rfl) ⟨1221155, by rfl⟩ : syracuseStep 1628207 = 2442311) B2442311
theorem B3659849 : Blo 1626512 3659849 := bstep (se 2 (by rfl) ⟨1372443, by rfl⟩ : syracuseStep 3659849 = 2744887) B2744887
theorem B1628327 : Blo 1626512 1628327 := bstep (se 1 (by rfl) ⟨1221245, by rfl⟩ : syracuseStep 1628327 = 2442491) B2442491
theorem B1628367 : Blo 1626512 1628367 := bstep (se 1 (by rfl) ⟨1221275, by rfl⟩ : syracuseStep 1628367 = 2442551) B2442551
theorem B4946159 : Blo 1626512 4946159 := bstep (se 1 (by rfl) ⟨3709619, by rfl⟩ : syracuseStep 4946159 = 7419239) B7419239
theorem B3660551 : Blo 1626512 3660551 := bstep (se 1 (by rfl) ⟨2745413, by rfl⟩ : syracuseStep 3660551 = 5490827) B5490827
theorem B2439977 : Blo 1626512 2439977 := bstep (se 2 (by rfl) ⟨914991, by rfl⟩ : syracuseStep 2439977 = 1829983) B1829983
theorem B2440295 : Blo 1626512 2440295 := bstep (se 1 (by rfl) ⟨1830221, by rfl⟩ : syracuseStep 2440295 = 3660443) B3660443
theorem B2317423 : Blo 1626512 2317423 := bstep (se 1 (by rfl) ⟨1738067, by rfl⟩ : syracuseStep 2317423 = 3476135) B3476135
theorem B2440475 : Blo 1626512 2440475 := bstep (se 1 (by rfl) ⟨1830356, by rfl⟩ : syracuseStep 2440475 = 3660713) B3660713
theorem B2440511 : Blo 1626512 2440511 := bstep (se 1 (by rfl) ⟨1830383, by rfl⟩ : syracuseStep 2440511 = 3660767) B3660767
theorem B35691839 : Blo 1626512 35691839 := bstep (se 1 (by rfl) ⟨26768879, by rfl⟩ : syracuseStep 35691839 = 53537759) B53537759
theorem B8240615 : Blo 1626512 8240615 := bstep (se 1 (by rfl) ⟨6180461, by rfl⟩ : syracuseStep 8240615 = 12360923) B12360923
theorem B3087983 : Blo 1626512 3087983 := bstep (se 1 (by rfl) ⟨2315987, by rfl⟩ : syracuseStep 3087983 = 4631975) B4631975
theorem B8240777 : Blo 1626512 8240777 := bstep (se 2 (by rfl) ⟨3090291, by rfl⟩ : syracuseStep 8240777 = 6180583) B6180583
theorem B2440871 : Blo 1626512 2440871 := bstep (se 1 (by rfl) ⟨1830653, by rfl⟩ : syracuseStep 2440871 = 3661307) B3661307
theorem B2440943 : Blo 1626512 2440943 := bstep (se 1 (by rfl) ⟨1830707, by rfl⟩ : syracuseStep 2440943 = 3661415) B3661415
theorem B2441129 : Blo 1626512 2441129 := bstep (se 2 (by rfl) ⟨915423, by rfl⟩ : syracuseStep 2441129 = 1830847) B1830847
theorem B2441243 : Blo 1626512 2441243 := bstep (se 1 (by rfl) ⟨1830932, by rfl⟩ : syracuseStep 2441243 = 3661865) B3661865
theorem B2441279 : Blo 1626512 2441279 := bstep (se 1 (by rfl) ⟨1830959, by rfl⟩ : syracuseStep 2441279 = 3661919) B3661919
theorem B9273473 : Blo 1626512 9273473 := bstep (se 2 (by rfl) ⟨3477552, by rfl⟩ : syracuseStep 9273473 = 6955105) B6955105
theorem B3662441 : Blo 1626512 3662441 := bstep (se 2 (by rfl) ⟨1373415, by rfl⟩ : syracuseStep 3662441 = 2746831) B2746831
theorem B3089639 : Blo 1626512 3089639 := bstep (se 1 (by rfl) ⟨2317229, by rfl⟩ : syracuseStep 3089639 = 4634459) B4634459
theorem B5211371 : Blo 1626512 5211371 := bstep (se 1 (by rfl) ⟨3908528, by rfl⟩ : syracuseStep 5211371 = 7817057) B7817057
theorem B23463215 : Blo 1626512 23463215 := bstep (se 1 (by rfl) ⟨17597411, by rfl⟩ : syracuseStep 23463215 = 35194823) B35194823
theorem B3474751 : Blo 1626512 3474751 := bstep (se 1 (by rfl) ⟨2606063, by rfl⟩ : syracuseStep 3474751 = 5212127) B5212127
theorem B8242559 : Blo 1626512 8242559 := bstep (se 1 (by rfl) ⟨6181919, by rfl⟩ : syracuseStep 8242559 = 12363839) B12363839
theorem B3089897 : Blo 1626512 3089897 := bstep (se 2 (by rfl) ⟨1158711, by rfl⟩ : syracuseStep 3089897 = 2317423) B2317423
theorem B8234621 : Blo 1626512 8234621 := bstep (se 3 (by rfl) ⟨1543991, by rfl⟩ : syracuseStep 8234621 = 3087983) B3087983
theorem B8242883 : Blo 1626512 8242883 := bstep (se 1 (by rfl) ⟨6182162, by rfl⟩ : syracuseStep 8242883 = 12364325) B12364325
theorem B5490557 : Blo 1626512 5490557 := bstep (se 3 (by rfl) ⟨1029479, by rfl⟩ : syracuseStep 5490557 = 2058959) B2058959
theorem B12355577 : Blo 1626512 12355577 := bstep (se 2 (by rfl) ⟨4633341, by rfl⟩ : syracuseStep 12355577 = 9266683) B9266683
theorem B6948919 : Blo 1626512 6948919 := bstep (se 1 (by rfl) ⟨5211689, by rfl⟩ : syracuseStep 6948919 = 10423379) B10423379
theorem B8800481 : Blo 1626512 8800481 := bstep (se 2 (by rfl) ⟨3300180, by rfl⟩ : syracuseStep 8800481 = 6600361) B6600361
theorem B17598971 : Blo 1626512 17598971 := bstep (se 1 (by rfl) ⟨13199228, by rfl⟩ : syracuseStep 17598971 = 26398457) B26398457
theorem B15633071 : Blo 1626512 15633071 := bstep (se 1 (by rfl) ⟨11724803, by rfl⟩ : syracuseStep 15633071 = 23449607) B23449607
theorem B10423151 : Blo 1626512 10423151 := bstep (se 1 (by rfl) ⟨7817363, by rfl⟩ : syracuseStep 10423151 = 15634727) B15634727
theorem B270912437 : Blo 1626512 270912437 := bstep (se 5 (by rfl) ⟨12699020, by rfl⟩ : syracuseStep 270912437 = 25398041) B25398041
theorem B12528593 : Blo 1626512 12528593 := bstep (se 2 (by rfl) ⟨4698222, by rfl⟩ : syracuseStep 12528593 = 9396445) B9396445
theorem B5213459 : Blo 1626512 5213459 := bstep (se 1 (by rfl) ⟨3910094, by rfl⟩ : syracuseStep 5213459 = 7820189) B7820189
theorem B25062713 : Blo 1626512 25062713 := bstep (se 2 (by rfl) ⟨9398517, by rfl⟩ : syracuseStep 25062713 = 18797035) B18797035
theorem B12357035 : Blo 1626512 12357035 := bstep (se 1 (by rfl) ⟨9267776, by rfl⟩ : syracuseStep 12357035 = 18535553) B18535553
theorem B2747945 : Blo 1626512 2747945 := bstep (se 2 (by rfl) ⟨1030479, by rfl⟩ : syracuseStep 2747945 = 2060959) B2060959
theorem B12357521 : Blo 1626512 12357521 := bstep (se 2 (by rfl) ⟨4634070, by rfl⟩ : syracuseStep 12357521 = 9268141) B9268141
theorem B3297439 : Blo 1626512 3297439 := bstep (se 1 (by rfl) ⟨2473079, by rfl⟩ : syracuseStep 3297439 = 4946159) B4946159
theorem B12366269 : Blo 1626512 12366269 := bstep (se 3 (by rfl) ⟨2318675, by rfl⟩ : syracuseStep 12366269 = 4637351) B4637351
theorem B8794601 : Blo 1626512 8794601 := bstep (se 2 (by rfl) ⟨3297975, by rfl⟩ : syracuseStep 8794601 = 6595951) B6595951
theorem B1626651 : Blo 1626512 1626651 := bstep (se 1 (by rfl) ⟨1219988, by rfl⟩ : syracuseStep 1626651 = 2439977) B2439977
theorem B171389519 : Blo 1626512 171389519 := bstep (se 1 (by rfl) ⟨128542139, by rfl⟩ : syracuseStep 171389519 = 257084279) B257084279
theorem B1626863 : Blo 1626512 1626863 := bstep (se 1 (by rfl) ⟨1220147, by rfl⟩ : syracuseStep 1626863 = 2440295) B2440295
theorem B1831711 : Blo 1626512 1831711 := bstep (se 1 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 1831711 = 2747567) B2747567
theorem B1626983 : Blo 1626512 1626983 := bstep (se 1 (by rfl) ⟨1220237, by rfl⟩ : syracuseStep 1626983 = 2440475) B2440475
theorem B1627007 : Blo 1626512 1627007 := bstep (se 1 (by rfl) ⟨1220255, by rfl⟩ : syracuseStep 1627007 = 2440511) B2440511
theorem B23794559 : Blo 1626512 23794559 := bstep (se 1 (by rfl) ⟨17845919, by rfl⟩ : syracuseStep 23794559 = 35691839) B35691839
theorem B5493743 : Blo 1626512 5493743 := bstep (se 1 (by rfl) ⟨4120307, by rfl⟩ : syracuseStep 5493743 = 8240615) B8240615
theorem B5493851 : Blo 1626512 5493851 := bstep (se 1 (by rfl) ⟨4120388, by rfl⟩ : syracuseStep 5493851 = 8240777) B8240777
theorem B1627247 : Blo 1626512 1627247 := bstep (se 1 (by rfl) ⟨1220435, by rfl⟩ : syracuseStep 1627247 = 2440871) B2440871
theorem B1627295 : Blo 1626512 1627295 := bstep (se 1 (by rfl) ⟨1220471, by rfl⟩ : syracuseStep 1627295 = 2440943) B2440943
theorem B1627419 : Blo 1626512 1627419 := bstep (se 1 (by rfl) ⟨1220564, by rfl⟩ : syracuseStep 1627419 = 2441129) B2441129
theorem B1627675 : Blo 1626512 1627675 := bstep (se 1 (by rfl) ⟨1220756, by rfl⟩ : syracuseStep 1627675 = 2441513) B2441513
theorem B8238671 : Blo 1626512 8238671 := bstep (se 1 (by rfl) ⟨6179003, by rfl⟩ : syracuseStep 8238671 = 12358007) B12358007
theorem B4175497 : Blo 1626512 4175497 := bstep (se 2 (by rfl) ⟨1565811, by rfl⟩ : syracuseStep 4175497 = 3131623) B3131623
theorem B5494607 : Blo 1626512 5494607 := bstep (se 1 (by rfl) ⟨4120955, by rfl⟩ : syracuseStep 5494607 = 8241911) B8241911
theorem B31291595 : Blo 1626512 31291595 := bstep (se 1 (by rfl) ⟨23468696, by rfl⟩ : syracuseStep 31291595 = 46937393) B46937393
theorem B4118921 : Blo 1626512 4118921 := bstep (se 2 (by rfl) ⟨1544595, by rfl⟩ : syracuseStep 4118921 = 3089191) B3089191
theorem B40155689 : Blo 1626512 40155689 := bstep (se 2 (by rfl) ⟨15058383, by rfl⟩ : syracuseStep 40155689 = 30116767) B30116767
theorem B2439899 : Blo 1626512 2439899 := bstep (se 1 (by rfl) ⟨1829924, by rfl⟩ : syracuseStep 2439899 = 3659849) B3659849
theorem B6265711 : Blo 1626512 6265711 := bstep (se 1 (by rfl) ⟨4699283, by rfl⟩ : syracuseStep 6265711 = 9398567) B9398567
theorem B2440367 : Blo 1626512 2440367 := bstep (se 1 (by rfl) ⟨1830275, by rfl⟩ : syracuseStep 2440367 = 3660551) B3660551
theorem B4398305 : Blo 1626512 4398305 := bstep (se 2 (by rfl) ⟨1649364, by rfl⟩ : syracuseStep 4398305 = 3298729) B3298729
theorem B14294335 : Blo 1626512 14294335 := bstep (se 1 (by rfl) ⟨10720751, by rfl⟩ : syracuseStep 14294335 = 21441503) B21441503
theorem B118808207 : Blo 1626512 118808207 := bstep (se 1 (by rfl) ⟨89106155, by rfl⟩ : syracuseStep 118808207 = 178212311) B178212311
theorem B47587139 : Blo 1626512 47587139 := bstep (se 1 (by rfl) ⟨35690354, by rfl⟩ : syracuseStep 47587139 = 71380709) B71380709
theorem B9265225 : Blo 1626512 9265225 := bstep (se 2 (by rfl) ⟨3474459, by rfl⟩ : syracuseStep 9265225 = 6948919) B6948919
theorem B2441627 : Blo 1626512 2441627 := bstep (se 1 (by rfl) ⟨1831220, by rfl⟩ : syracuseStep 2441627 = 3662441) B3662441
theorem B3662495 : Blo 1626512 3662495 := bstep (se 1 (by rfl) ⟨2746871, by rfl⟩ : syracuseStep 3662495 = 5493743) B5493743
theorem B3662567 : Blo 1626512 3662567 := bstep (se 1 (by rfl) ⟨2746925, by rfl⟩ : syracuseStep 3662567 = 5493851) B5493851
theorem B3474247 : Blo 1626512 3474247 := bstep (se 1 (by rfl) ⟨2605685, by rfl⟩ : syracuseStep 3474247 = 5211371) B5211371
theorem B2442281 : Blo 1626512 2442281 := bstep (se 2 (by rfl) ⟨915855, by rfl⟩ : syracuseStep 2442281 = 1831711) B1831711
theorem B5489747 : Blo 1626512 5489747 := bstep (se 1 (by rfl) ⟨4117310, by rfl⟩ : syracuseStep 5489747 = 8234621) B8234621
theorem B3663071 : Blo 1626512 3663071 := bstep (se 1 (by rfl) ⟨2747303, by rfl⟩ : syracuseStep 3663071 = 5494607) B5494607
theorem B5866987 : Blo 1626512 5866987 := bstep (se 1 (by rfl) ⟨4400240, by rfl⟩ : syracuseStep 5866987 = 8800481) B8800481
theorem B2745947 : Blo 1626512 2745947 := bstep (se 1 (by rfl) ⟨2059460, by rfl⟩ : syracuseStep 2745947 = 4118921) B4118921
theorem B11732647 : Blo 1626512 11732647 := bstep (se 1 (by rfl) ⟨8799485, by rfl⟩ : syracuseStep 11732647 = 17598971) B17598971
theorem B10422047 : Blo 1626512 10422047 := bstep (se 1 (by rfl) ⟨7816535, by rfl⟩ : syracuseStep 10422047 = 15633071) B15633071
theorem B6948767 : Blo 1626512 6948767 := bstep (se 1 (by rfl) ⟨5211575, by rfl⟩ : syracuseStep 6948767 = 10423151) B10423151
theorem B3475639 : Blo 1626512 3475639 := bstep (se 1 (by rfl) ⟨2606729, by rfl⟩ : syracuseStep 3475639 = 5213459) B5213459
theorem B8244179 : Blo 1626512 8244179 := bstep (se 1 (by rfl) ⟨6183134, by rfl⟩ : syracuseStep 8244179 = 12366269) B12366269
theorem B15863039 : Blo 1626512 15863039 := bstep (se 1 (by rfl) ⟨11897279, by rfl⟩ : syracuseStep 15863039 = 23794559) B23794559
theorem B2059759 : Blo 1626512 2059759 := bstep (se 1 (by rfl) ⟨1544819, by rfl⟩ : syracuseStep 2059759 = 3089639) B3089639
theorem B15642143 : Blo 1626512 15642143 := bstep (se 1 (by rfl) ⟨11731607, by rfl⟩ : syracuseStep 15642143 = 23463215) B23463215
theorem B2059931 : Blo 1626512 2059931 := bstep (se 1 (by rfl) ⟨1544948, by rfl⟩ : syracuseStep 2059931 = 3089897) B3089897
theorem B5492447 : Blo 1626512 5492447 := bstep (se 1 (by rfl) ⟨4119335, by rfl⟩ : syracuseStep 5492447 = 8238671) B8238671
theorem B8237051 : Blo 1626512 8237051 := bstep (se 1 (by rfl) ⟨6177788, by rfl⟩ : syracuseStep 8237051 = 12355577) B12355577
theorem B20861063 : Blo 1626512 20861063 := bstep (se 1 (by rfl) ⟨15645797, by rfl⟩ : syracuseStep 20861063 = 31291595) B31291595
theorem B4633001 : Blo 1626512 4633001 := bstep (se 2 (by rfl) ⟨1737375, by rfl⟩ : syracuseStep 4633001 = 3474751) B3474751
theorem B19059113 : Blo 1626512 19059113 := bstep (se 2 (by rfl) ⟨7147167, by rfl⟩ : syracuseStep 19059113 = 14294335) B14294335
theorem B1626599 : Blo 1626512 1626599 := bstep (se 1 (by rfl) ⟨1219949, by rfl⟩ : syracuseStep 1626599 = 2439899) B2439899
theorem B8352395 : Blo 1626512 8352395 := bstep (se 1 (by rfl) ⟨6264296, by rfl⟩ : syracuseStep 8352395 = 12528593) B12528593
theorem B1626911 : Blo 1626512 1626911 := bstep (se 1 (by rfl) ⟨1220183, by rfl⟩ : syracuseStep 1626911 = 2440367) B2440367
theorem B5567329 : Blo 1626512 5567329 := bstep (se 2 (by rfl) ⟨2087748, by rfl⟩ : syracuseStep 5567329 = 4175497) B4175497
theorem B16708475 : Blo 1626512 16708475 := bstep (se 1 (by rfl) ⟨12531356, by rfl⟩ : syracuseStep 16708475 = 25062713) B25062713
theorem B8238023 : Blo 1626512 8238023 := bstep (se 1 (by rfl) ⟨6178517, by rfl⟩ : syracuseStep 8238023 = 12357035) B12357035
theorem B1831963 : Blo 1626512 1831963 := bstep (se 1 (by rfl) ⟨1373972, by rfl⟩ : syracuseStep 1831963 = 2747945) B2747945
theorem B79205471 : Blo 1626512 79205471 := bstep (se 1 (by rfl) ⟨59404103, by rfl⟩ : syracuseStep 79205471 = 118808207) B118808207
theorem B31724759 : Blo 1626512 31724759 := bstep (se 1 (by rfl) ⟨23793569, by rfl⟩ : syracuseStep 31724759 = 47587139) B47587139
theorem B8238347 : Blo 1626512 8238347 := bstep (se 1 (by rfl) ⟨6178760, by rfl⟩ : syracuseStep 8238347 = 12357521) B12357521
theorem B1627495 : Blo 1626512 1627495 := bstep (se 1 (by rfl) ⟨1220621, by rfl⟩ : syracuseStep 1627495 = 2441243) B2441243
theorem B1627519 : Blo 1626512 1627519 := bstep (se 1 (by rfl) ⟨1220639, by rfl⟩ : syracuseStep 1627519 = 2441279) B2441279
theorem B6182315 : Blo 1626512 6182315 := bstep (se 1 (by rfl) ⟨4636736, by rfl⟩ : syracuseStep 6182315 = 9273473) B9273473
theorem B5863067 : Blo 1626512 5863067 := bstep (se 1 (by rfl) ⟨4397300, by rfl⟩ : syracuseStep 5863067 = 8794601) B8794601
theorem B114259679 : Blo 1626512 114259679 := bstep (se 1 (by rfl) ⟨85694759, by rfl⟩ : syracuseStep 114259679 = 171389519) B171389519
theorem B11728813 : Blo 1626512 11728813 := bstep (se 3 (by rfl) ⟨2199152, by rfl⟩ : syracuseStep 11728813 = 4398305) B4398305
theorem B17586341 : Blo 1626512 17586341 := bstep (se 4 (by rfl) ⟨1648719, by rfl⟩ : syracuseStep 17586341 = 3297439) B3297439
theorem B5495039 : Blo 1626512 5495039 := bstep (se 1 (by rfl) ⟨4121279, by rfl⟩ : syracuseStep 5495039 = 8242559) B8242559
theorem B5495255 : Blo 1626512 5495255 := bstep (se 1 (by rfl) ⟨4121441, by rfl⟩ : syracuseStep 5495255 = 8242883) B8242883
theorem B8354281 : Blo 1626512 8354281 := bstep (se 2 (by rfl) ⟨3132855, by rfl⟩ : syracuseStep 8354281 = 6265711) B6265711
theorem B3660371 : Blo 1626512 3660371 := bstep (se 1 (by rfl) ⟨2745278, by rfl⟩ : syracuseStep 3660371 = 5490557) B5490557
theorem B26770459 : Blo 1626512 26770459 := bstep (se 1 (by rfl) ⟨20077844, by rfl⟩ : syracuseStep 26770459 = 40155689) B40155689
theorem B180608291 : Blo 1626512 180608291 := bstep (se 1 (by rfl) ⟨135456218, by rfl⟩ : syracuseStep 180608291 = 270912437) B270912437
theorem B12353633 : Blo 1626512 12353633 := bstep (se 2 (by rfl) ⟨4632612, by rfl⟩ : syracuseStep 12353633 = 9265225) B9265225
theorem B3088667 : Blo 1626512 3088667 := bstep (se 1 (by rfl) ⟨2316500, by rfl⟩ : syracuseStep 3088667 = 4633001) B4633001
theorem B12706075 : Blo 1626512 12706075 := bstep (se 1 (by rfl) ⟨9529556, by rfl⟩ : syracuseStep 12706075 = 19059113) B19059113
theorem B2441663 : Blo 1626512 2441663 := bstep (se 1 (by rfl) ⟨1831247, by rfl⟩ : syracuseStep 2441663 = 3662495) B3662495
theorem B2441711 : Blo 1626512 2441711 := bstep (se 1 (by rfl) ⟨1831283, by rfl⟩ : syracuseStep 2441711 = 3662567) B3662567
theorem B2442047 : Blo 1626512 2442047 := bstep (se 1 (by rfl) ⟨1831535, by rfl⟩ : syracuseStep 2442047 = 3663071) B3663071
theorem B4121543 : Blo 1626512 4121543 := bstep (se 1 (by rfl) ⟨3091157, by rfl⟩ : syracuseStep 4121543 = 6182315) B6182315
theorem B3908711 : Blo 1626512 3908711 := bstep (se 1 (by rfl) ⟨2931533, by rfl⟩ : syracuseStep 3908711 = 5863067) B5863067
theorem B6948031 : Blo 1626512 6948031 := bstep (se 1 (by rfl) ⟨5211023, by rfl⟩ : syracuseStep 6948031 = 10422047) B10422047
theorem B2442617 : Blo 1626512 2442617 := bstep (se 2 (by rfl) ⟨915981, by rfl⟩ : syracuseStep 2442617 = 1831963) B1831963
theorem B35693945 : Blo 1626512 35693945 := bstep (se 2 (by rfl) ⟨13385229, by rfl⟩ : syracuseStep 35693945 = 26770459) B26770459
theorem B11724227 : Blo 1626512 11724227 := bstep (se 1 (by rfl) ⟨8793170, by rfl⟩ : syracuseStep 11724227 = 17586341) B17586341
theorem B3663359 : Blo 1626512 3663359 := bstep (se 1 (by rfl) ⟨2747519, by rfl⟩ : syracuseStep 3663359 = 5495039) B5495039
theorem B3663503 : Blo 1626512 3663503 := bstep (se 1 (by rfl) ⟨2747627, by rfl⟩ : syracuseStep 3663503 = 5495255) B5495255
theorem B2746345 : Blo 1626512 2746345 := bstep (se 2 (by rfl) ⟨1029879, by rfl⟩ : syracuseStep 2746345 = 2059759) B2059759
theorem B5491367 : Blo 1626512 5491367 := bstep (se 1 (by rfl) ⟨4118525, by rfl⟩ : syracuseStep 5491367 = 8237051) B8237051
theorem B5492015 : Blo 1626512 5492015 := bstep (se 1 (by rfl) ⟨4119011, by rfl⟩ : syracuseStep 5492015 = 8238023) B8238023
theorem B5492231 : Blo 1626512 5492231 := bstep (se 1 (by rfl) ⟨4119173, by rfl⟩ : syracuseStep 5492231 = 8238347) B8238347
theorem B1830631 : Blo 1626512 1830631 := bstep (se 1 (by rfl) ⟨1372973, by rfl⟩ : syracuseStep 1830631 = 2745947) B2745947
theorem B4632329 : Blo 1626512 4632329 := bstep (se 2 (by rfl) ⟨1737123, by rfl⟩ : syracuseStep 4632329 = 3474247) B3474247
theorem B76173119 : Blo 1626512 76173119 := bstep (se 1 (by rfl) ⟨57129839, by rfl⟩ : syracuseStep 76173119 = 114259679) B114259679
theorem B4632511 : Blo 1626512 4632511 := bstep (se 1 (by rfl) ⟨3474383, by rfl⟩ : syracuseStep 4632511 = 6948767) B6948767
theorem B5493149 : Blo 1626512 5493149 := bstep (se 3 (by rfl) ⟨1029965, by rfl⟩ : syracuseStep 5493149 = 2059931) B2059931
theorem B29692421 : Blo 1626512 29692421 := bstep (se 4 (by rfl) ⟨2783664, by rfl⟩ : syracuseStep 29692421 = 5567329) B5567329
theorem B15643529 : Blo 1626512 15643529 := bstep (se 2 (by rfl) ⟨5866323, by rfl⟩ : syracuseStep 15643529 = 11732647) B11732647
theorem B13907375 : Blo 1626512 13907375 := bstep (se 1 (by rfl) ⟨10430531, by rfl⟩ : syracuseStep 13907375 = 20861063) B20861063
theorem B4634185 : Blo 1626512 4634185 := bstep (se 2 (by rfl) ⟨1737819, by rfl⟩ : syracuseStep 4634185 = 3475639) B3475639
theorem B1627751 : Blo 1626512 1627751 := bstep (se 1 (by rfl) ⟨1220813, by rfl⟩ : syracuseStep 1627751 = 2441627) B2441627
theorem B5568263 : Blo 1626512 5568263 := bstep (se 1 (by rfl) ⟨4176197, by rfl⟩ : syracuseStep 5568263 = 8352395) B8352395
theorem B11139041 : Blo 1626512 11139041 := bstep (se 2 (by rfl) ⟨4177140, by rfl⟩ : syracuseStep 11139041 = 8354281) B8354281
theorem B1628187 : Blo 1626512 1628187 := bstep (se 1 (by rfl) ⟨1221140, by rfl⟩ : syracuseStep 1628187 = 2442281) B2442281
theorem B3659831 : Blo 1626512 3659831 := bstep (se 1 (by rfl) ⟨2744873, by rfl⟩ : syracuseStep 3659831 = 5489747) B5489747
theorem B52803647 : Blo 1626512 52803647 := bstep (se 1 (by rfl) ⟨39602735, by rfl⟩ : syracuseStep 52803647 = 79205471) B79205471
theorem B21149839 : Blo 1626512 21149839 := bstep (se 1 (by rfl) ⟨15862379, by rfl⟩ : syracuseStep 21149839 = 31724759) B31724759
theorem B2440247 : Blo 1626512 2440247 := bstep (se 1 (by rfl) ⟨1830185, by rfl⟩ : syracuseStep 2440247 = 3660371) B3660371
theorem B5496119 : Blo 1626512 5496119 := bstep (se 1 (by rfl) ⟨4122089, by rfl⟩ : syracuseStep 5496119 = 8244179) B8244179
theorem B7822649 : Blo 1626512 7822649 := bstep (se 2 (by rfl) ⟨2933493, by rfl⟩ : syracuseStep 7822649 = 5866987) B5866987
theorem B10575359 : Blo 1626512 10575359 := bstep (se 1 (by rfl) ⟨7931519, by rfl⟩ : syracuseStep 10575359 = 15863039) B15863039
theorem B120405527 : Blo 1626512 120405527 := bstep (se 1 (by rfl) ⟨90304145, by rfl⟩ : syracuseStep 120405527 = 180608291) B180608291
theorem B44555933 : Blo 1626512 44555933 := bstep (se 3 (by rfl) ⟨8354237, by rfl⟩ : syracuseStep 44555933 = 16708475) B16708475
theorem B10428095 : Blo 1626512 10428095 := bstep (se 1 (by rfl) ⟨7821071, by rfl⟩ : syracuseStep 10428095 = 15642143) B15642143
theorem B3661631 : Blo 1626512 3661631 := bstep (se 1 (by rfl) ⟨2746223, by rfl⟩ : syracuseStep 3661631 = 5492447) B5492447
theorem B15638417 : Blo 1626512 15638417 := bstep (se 2 (by rfl) ⟨5864406, by rfl⟩ : syracuseStep 15638417 = 11728813) B11728813
theorem B3662099 : Blo 1626512 3662099 := bstep (se 1 (by rfl) ⟨2746574, by rfl⟩ : syracuseStep 3662099 = 5493149) B5493149
theorem B16941433 : Blo 1626512 16941433 := bstep (se 2 (by rfl) ⟨6353037, by rfl⟩ : syracuseStep 16941433 = 12706075) B12706075
theorem B10429019 : Blo 1626512 10429019 := bstep (se 1 (by rfl) ⟨7821764, by rfl⟩ : syracuseStep 10429019 = 15643529) B15643529
theorem B2605807 : Blo 1626512 2605807 := bstep (se 1 (by rfl) ⟨1954355, by rfl⟩ : syracuseStep 2605807 = 3908711) B3908711
theorem B7816151 : Blo 1626512 7816151 := bstep (se 1 (by rfl) ⟨5862113, by rfl⟩ : syracuseStep 7816151 = 11724227) B11724227
theorem B2442239 : Blo 1626512 2442239 := bstep (se 1 (by rfl) ⟨1831679, by rfl⟩ : syracuseStep 2442239 = 3663359) B3663359
theorem B2442335 : Blo 1626512 2442335 := bstep (se 1 (by rfl) ⟨1831751, by rfl⟩ : syracuseStep 2442335 = 3663503) B3663503
theorem B3712175 : Blo 1626512 3712175 := bstep (se 1 (by rfl) ⟨2784131, by rfl⟩ : syracuseStep 3712175 = 5568263) B5568263
theorem B35202431 : Blo 1626512 35202431 := bstep (se 1 (by rfl) ⟨26401823, by rfl⟩ : syracuseStep 35202431 = 52803647) B52803647
theorem B6178913 : Blo 1626512 6178913 := bstep (se 2 (by rfl) ⟨2317092, by rfl⟩ : syracuseStep 6178913 = 4634185) B4634185
theorem B3664079 : Blo 1626512 3664079 := bstep (se 1 (by rfl) ⟨2748059, by rfl⟩ : syracuseStep 3664079 = 5496119) B5496119
theorem B8235755 : Blo 1626512 8235755 := bstep (se 1 (by rfl) ⟨6176816, by rfl⟩ : syracuseStep 8235755 = 12353633) B12353633
theorem B2059111 : Blo 1626512 2059111 := bstep (se 1 (by rfl) ⟨1544333, by rfl⟩ : syracuseStep 2059111 = 3088667) B3088667
theorem B19794947 : Blo 1626512 19794947 := bstep (se 1 (by rfl) ⟨14846210, by rfl⟩ : syracuseStep 19794947 = 29692421) B29692421
theorem B2747695 : Blo 1626512 2747695 := bstep (se 1 (by rfl) ⟨2060771, by rfl⟩ : syracuseStep 2747695 = 4121543) B4121543
theorem B112799141 : Blo 1626512 112799141 := bstep (se 4 (by rfl) ⟨10574919, by rfl⟩ : syracuseStep 112799141 = 21149839) B21149839
theorem B7426027 : Blo 1626512 7426027 := bstep (se 1 (by rfl) ⟨5569520, by rfl⟩ : syracuseStep 7426027 = 11139041) B11139041
theorem B1626831 : Blo 1626512 1626831 := bstep (se 1 (by rfl) ⟨1220123, by rfl⟩ : syracuseStep 1626831 = 2440247) B2440247
theorem B5215099 : Blo 1626512 5215099 := bstep (se 1 (by rfl) ⟨3911324, by rfl⟩ : syracuseStep 5215099 = 7822649) B7822649
theorem B7050239 : Blo 1626512 7050239 := bstep (se 1 (by rfl) ⟨5287679, by rfl⟩ : syracuseStep 7050239 = 10575359) B10575359
theorem B80270351 : Blo 1626512 80270351 := bstep (se 1 (by rfl) ⟨60202763, by rfl⟩ : syracuseStep 80270351 = 120405527) B120405527
theorem B6952063 : Blo 1626512 6952063 := bstep (se 1 (by rfl) ⟨5214047, by rfl⟩ : syracuseStep 6952063 = 10428095) B10428095
theorem B10425611 : Blo 1626512 10425611 := bstep (se 1 (by rfl) ⟨7819208, by rfl⟩ : syracuseStep 10425611 = 15638417) B15638417
theorem B1627775 : Blo 1626512 1627775 := bstep (se 1 (by rfl) ⟨1220831, by rfl⟩ : syracuseStep 1627775 = 2441663) B2441663
theorem B1627807 : Blo 1626512 1627807 := bstep (se 1 (by rfl) ⟨1220855, by rfl⟩ : syracuseStep 1627807 = 2441711) B2441711
theorem B1628031 : Blo 1626512 1628031 := bstep (se 1 (by rfl) ⟨1221023, by rfl⟩ : syracuseStep 1628031 = 2442047) B2442047
theorem B1628411 : Blo 1626512 1628411 := bstep (se 1 (by rfl) ⟨1221308, by rfl⟩ : syracuseStep 1628411 = 2442617) B2442617
theorem B23795963 : Blo 1626512 23795963 := bstep (se 1 (by rfl) ⟨17846972, by rfl⟩ : syracuseStep 23795963 = 35693945) B35693945
theorem B9271583 : Blo 1626512 9271583 := bstep (se 1 (by rfl) ⟨6953687, by rfl⟩ : syracuseStep 9271583 = 13907375) B13907375
theorem B2439887 : Blo 1626512 2439887 := bstep (se 1 (by rfl) ⟨1829915, by rfl⟩ : syracuseStep 2439887 = 3659831) B3659831
theorem B9264041 : Blo 1626512 9264041 := bstep (se 2 (by rfl) ⟨3474015, by rfl⟩ : syracuseStep 9264041 = 6948031) B6948031
theorem B3660911 : Blo 1626512 3660911 := bstep (se 1 (by rfl) ⟨2745683, by rfl⟩ : syracuseStep 3660911 = 5491367) B5491367
theorem B3661343 : Blo 1626512 3661343 := bstep (se 1 (by rfl) ⟨2746007, by rfl⟩ : syracuseStep 3661343 = 5492015) B5492015
theorem B2440841 : Blo 1626512 2440841 := bstep (se 2 (by rfl) ⟨915315, by rfl⟩ : syracuseStep 2440841 = 1830631) B1830631
theorem B3661487 : Blo 1626512 3661487 := bstep (se 1 (by rfl) ⟨2746115, by rfl⟩ : syracuseStep 3661487 = 5492231) B5492231
theorem B29703955 : Blo 1626512 29703955 := bstep (se 1 (by rfl) ⟨22277966, by rfl⟩ : syracuseStep 29703955 = 44555933) B44555933
theorem B3088219 : Blo 1626512 3088219 := bstep (se 1 (by rfl) ⟨2316164, by rfl⟩ : syracuseStep 3088219 = 4632329) B4632329
theorem B50782079 : Blo 1626512 50782079 := bstep (se 1 (by rfl) ⟨38086559, by rfl⟩ : syracuseStep 50782079 = 76173119) B76173119
theorem B2441087 : Blo 1626512 2441087 := bstep (se 1 (by rfl) ⟨1830815, by rfl⟩ : syracuseStep 2441087 = 3661631) B3661631
theorem B6176681 : Blo 1626512 6176681 := bstep (se 2 (by rfl) ⟨2316255, by rfl⟩ : syracuseStep 6176681 = 4632511) B4632511
theorem B3661793 : Blo 1626512 3661793 := bstep (se 2 (by rfl) ⟨1373172, by rfl⟩ : syracuseStep 3661793 = 2746345) B2746345
theorem B2441399 : Blo 1626512 2441399 := bstep (se 1 (by rfl) ⟨1831049, by rfl⟩ : syracuseStep 2441399 = 3662099) B3662099
theorem B5210767 : Blo 1626512 5210767 := bstep (se 1 (by rfl) ⟨3908075, by rfl⟩ : syracuseStep 5210767 = 7816151) B7816151
theorem B2474783 : Blo 1626512 2474783 := bstep (se 1 (by rfl) ⟨1856087, by rfl⟩ : syracuseStep 2474783 = 3712175) B3712175
theorem B3474409 : Blo 1626512 3474409 := bstep (se 2 (by rfl) ⟨1302903, by rfl⟩ : syracuseStep 3474409 = 2605807) B2605807
theorem B2745481 : Blo 1626512 2745481 := bstep (se 2 (by rfl) ⟨1029555, by rfl⟩ : syracuseStep 2745481 = 2059111) B2059111
theorem B2442719 : Blo 1626512 2442719 := bstep (se 1 (by rfl) ⟨1832039, by rfl⟩ : syracuseStep 2442719 = 3664079) B3664079
theorem B3663593 : Blo 1626512 3663593 := bstep (se 2 (by rfl) ⟨1373847, by rfl⟩ : syracuseStep 3663593 = 2747695) B2747695
theorem B5490503 : Blo 1626512 5490503 := bstep (se 1 (by rfl) ⟨4117877, by rfl⟩ : syracuseStep 5490503 = 8235755) B8235755
theorem B22588577 : Blo 1626512 22588577 := bstep (se 2 (by rfl) ⟨8470716, by rfl⟩ : syracuseStep 22588577 = 16941433) B16941433
theorem B53513567 : Blo 1626512 53513567 := bstep (se 1 (by rfl) ⟨40135175, by rfl⟩ : syracuseStep 53513567 = 80270351) B80270351
theorem B6950407 : Blo 1626512 6950407 := bstep (se 1 (by rfl) ⟨5212805, by rfl⟩ : syracuseStep 6950407 = 10425611) B10425611
theorem B15863975 : Blo 1626512 15863975 := bstep (se 1 (by rfl) ⟨11897981, by rfl⟩ : syracuseStep 15863975 = 23795963) B23795963
theorem B9269417 : Blo 1626512 9269417 := bstep (se 2 (by rfl) ⟨3476031, by rfl⟩ : syracuseStep 9269417 = 6952063) B6952063
theorem B6181055 : Blo 1626512 6181055 := bstep (se 1 (by rfl) ⟨4635791, by rfl⟩ : syracuseStep 6181055 = 9271583) B9271583
theorem B1626591 : Blo 1626512 1626591 := bstep (se 1 (by rfl) ⟨1219943, by rfl⟩ : syracuseStep 1626591 = 2439887) B2439887
theorem B75199427 : Blo 1626512 75199427 := bstep (se 1 (by rfl) ⟨56399570, by rfl⟩ : syracuseStep 75199427 = 112799141) B112799141
theorem B39605273 : Blo 1626512 39605273 := bstep (se 2 (by rfl) ⟨14851977, by rfl⟩ : syracuseStep 39605273 = 29703955) B29703955
theorem B1627227 : Blo 1626512 1627227 := bstep (se 1 (by rfl) ⟨1220420, by rfl⟩ : syracuseStep 1627227 = 2440841) B2440841
theorem B4117625 : Blo 1626512 4117625 := bstep (se 2 (by rfl) ⟨1544109, by rfl⟩ : syracuseStep 4117625 = 3088219) B3088219
theorem B33854719 : Blo 1626512 33854719 := bstep (se 1 (by rfl) ⟨25391039, by rfl⟩ : syracuseStep 33854719 = 50782079) B50782079
theorem B1627391 : Blo 1626512 1627391 := bstep (se 1 (by rfl) ⟨1220543, by rfl⟩ : syracuseStep 1627391 = 2441087) B2441087
theorem B4117787 : Blo 1626512 4117787 := bstep (se 1 (by rfl) ⟨3088340, by rfl⟩ : syracuseStep 4117787 = 6176681) B6176681
theorem B9901369 : Blo 1626512 9901369 := bstep (se 2 (by rfl) ⟨3713013, by rfl⟩ : syracuseStep 9901369 = 7426027) B7426027
theorem B52786525 : Blo 1626512 52786525 := bstep (se 3 (by rfl) ⟨9897473, by rfl⟩ : syracuseStep 52786525 = 19794947) B19794947
theorem B6952679 : Blo 1626512 6952679 := bstep (se 1 (by rfl) ⟨5214509, by rfl⟩ : syracuseStep 6952679 = 10429019) B10429019
theorem B1628159 : Blo 1626512 1628159 := bstep (se 1 (by rfl) ⟨1221119, by rfl⟩ : syracuseStep 1628159 = 2442239) B2442239
theorem B4700159 : Blo 1626512 4700159 := bstep (se 1 (by rfl) ⟨3525119, by rfl⟩ : syracuseStep 4700159 = 7050239) B7050239
theorem B1628223 : Blo 1626512 1628223 := bstep (se 1 (by rfl) ⟨1221167, by rfl⟩ : syracuseStep 1628223 = 2442335) B2442335
theorem B23468287 : Blo 1626512 23468287 := bstep (se 1 (by rfl) ⟨17601215, by rfl⟩ : syracuseStep 23468287 = 35202431) B35202431
theorem B6953465 : Blo 1626512 6953465 := bstep (se 2 (by rfl) ⟨2607549, by rfl⟩ : syracuseStep 6953465 = 5215099) B5215099
theorem B4119275 : Blo 1626512 4119275 := bstep (se 1 (by rfl) ⟨3089456, by rfl⟩ : syracuseStep 4119275 = 6178913) B6178913
theorem B6176027 : Blo 1626512 6176027 := bstep (se 1 (by rfl) ⟨4632020, by rfl⟩ : syracuseStep 6176027 = 9264041) B9264041
theorem B2440607 : Blo 1626512 2440607 := bstep (se 1 (by rfl) ⟨1830455, by rfl⟩ : syracuseStep 2440607 = 3660911) B3660911
theorem B2440895 : Blo 1626512 2440895 := bstep (se 1 (by rfl) ⟨1830671, by rfl⟩ : syracuseStep 2440895 = 3661343) B3661343
theorem B2440991 : Blo 1626512 2440991 := bstep (se 1 (by rfl) ⟨1830743, by rfl⟩ : syracuseStep 2440991 = 3661487) B3661487
theorem B2441195 : Blo 1626512 2441195 := bstep (se 1 (by rfl) ⟨1830896, by rfl⟩ : syracuseStep 2441195 = 3661793) B3661793
theorem B10575983 : Blo 1626512 10575983 := bstep (se 1 (by rfl) ⟨7931987, by rfl⟩ : syracuseStep 10575983 = 15863975) B15863975
theorem B4120703 : Blo 1626512 4120703 := bstep (se 1 (by rfl) ⟨3090527, by rfl⟩ : syracuseStep 4120703 = 6181055) B6181055
theorem B26403515 : Blo 1626512 26403515 := bstep (se 1 (by rfl) ⟨19802636, by rfl⟩ : syracuseStep 26403515 = 39605273) B39605273
theorem B2745083 : Blo 1626512 2745083 := bstep (se 1 (by rfl) ⟨2058812, by rfl⟩ : syracuseStep 2745083 = 4117625) B4117625
theorem B2745191 : Blo 1626512 2745191 := bstep (se 1 (by rfl) ⟨2058893, by rfl⟩ : syracuseStep 2745191 = 4117787) B4117787
theorem B6947689 : Blo 1626512 6947689 := bstep (se 2 (by rfl) ⟨2605383, by rfl⟩ : syracuseStep 6947689 = 5210767) B5210767
theorem B2442395 : Blo 1626512 2442395 := bstep (se 1 (by rfl) ⟨1831796, by rfl⟩ : syracuseStep 2442395 = 3663593) B3663593
theorem B45139625 : Blo 1626512 45139625 := bstep (se 2 (by rfl) ⟨16927359, by rfl⟩ : syracuseStep 45139625 = 33854719) B33854719
theorem B2746183 : Blo 1626512 2746183 := bstep (se 1 (by rfl) ⟨2059637, by rfl⟩ : syracuseStep 2746183 = 4119275) B4119275
theorem B9267209 : Blo 1626512 9267209 := bstep (se 2 (by rfl) ⟨3475203, by rfl⟩ : syracuseStep 9267209 = 6950407) B6950407
theorem B15059051 : Blo 1626512 15059051 := bstep (se 1 (by rfl) ⟨11294288, by rfl⟩ : syracuseStep 15059051 = 22588577) B22588577
theorem B6179611 : Blo 1626512 6179611 := bstep (se 1 (by rfl) ⟨4634708, by rfl⟩ : syracuseStep 6179611 = 9269417) B9269417
theorem B1649855 : Blo 1626512 1649855 := bstep (se 1 (by rfl) ⟨1237391, by rfl⟩ : syracuseStep 1649855 = 2474783) B2474783
theorem B4632545 : Blo 1626512 4632545 := bstep (se 2 (by rfl) ⟨1737204, by rfl⟩ : syracuseStep 4632545 = 3474409) B3474409
theorem B3133439 : Blo 1626512 3133439 := bstep (se 1 (by rfl) ⟨2350079, by rfl⟩ : syracuseStep 3133439 = 4700159) B4700159
theorem B13201825 : Blo 1626512 13201825 := bstep (se 2 (by rfl) ⟨4950684, by rfl⟩ : syracuseStep 13201825 = 9901369) B9901369
theorem B70382033 : Blo 1626512 70382033 := bstep (se 2 (by rfl) ⟨26393262, by rfl⟩ : syracuseStep 70382033 = 52786525) B52786525
theorem B4117351 : Blo 1626512 4117351 := bstep (se 1 (by rfl) ⟨3088013, by rfl⟩ : syracuseStep 4117351 = 6176027) B6176027
theorem B1627071 : Blo 1626512 1627071 := bstep (se 1 (by rfl) ⟨1220303, by rfl⟩ : syracuseStep 1627071 = 2440607) B2440607
theorem B1627263 : Blo 1626512 1627263 := bstep (se 1 (by rfl) ⟨1220447, by rfl⟩ : syracuseStep 1627263 = 2440895) B2440895
theorem B1627327 : Blo 1626512 1627327 := bstep (se 1 (by rfl) ⟨1220495, by rfl⟩ : syracuseStep 1627327 = 2440991) B2440991
theorem B1627463 : Blo 1626512 1627463 := bstep (se 1 (by rfl) ⟨1220597, by rfl⟩ : syracuseStep 1627463 = 2441195) B2441195
theorem B1627599 : Blo 1626512 1627599 := bstep (se 1 (by rfl) ⟨1220699, by rfl⟩ : syracuseStep 1627599 = 2441399) B2441399
theorem B31291049 : Blo 1626512 31291049 := bstep (se 2 (by rfl) ⟨11734143, by rfl⟩ : syracuseStep 31291049 = 23468287) B23468287
theorem B50132951 : Blo 1626512 50132951 := bstep (se 1 (by rfl) ⟨37599713, by rfl⟩ : syracuseStep 50132951 = 75199427) B75199427
theorem B1628479 : Blo 1626512 1628479 := bstep (se 1 (by rfl) ⟨1221359, by rfl⟩ : syracuseStep 1628479 = 2442719) B2442719
theorem B4635119 : Blo 1626512 4635119 := bstep (se 1 (by rfl) ⟨3476339, by rfl⟩ : syracuseStep 4635119 = 6952679) B6952679
theorem B3660335 : Blo 1626512 3660335 := bstep (se 1 (by rfl) ⟨2745251, by rfl⟩ : syracuseStep 3660335 = 5490503) B5490503
theorem B3660641 : Blo 1626512 3660641 := bstep (se 2 (by rfl) ⟨1372740, by rfl⟩ : syracuseStep 3660641 = 2745481) B2745481
theorem B4635643 : Blo 1626512 4635643 := bstep (se 1 (by rfl) ⟨3476732, by rfl⟩ : syracuseStep 4635643 = 6953465) B6953465
theorem B35675711 : Blo 1626512 35675711 := bstep (se 1 (by rfl) ⟨26756783, by rfl⟩ : syracuseStep 35675711 = 53513567) B53513567
theorem B4399613 : Blo 1626512 4399613 := bstep (se 3 (by rfl) ⟨824927, by rfl⟩ : syracuseStep 4399613 = 1649855) B1649855
theorem B5489801 : Blo 1626512 5489801 := bstep (se 2 (by rfl) ⟨2058675, by rfl⟩ : syracuseStep 5489801 = 4117351) B4117351
theorem B6178139 : Blo 1626512 6178139 := bstep (se 1 (by rfl) ⟨4633604, by rfl⟩ : syracuseStep 6178139 = 9267209) B9267209
theorem B3090079 : Blo 1626512 3090079 := bstep (se 1 (by rfl) ⟨2317559, by rfl⟩ : syracuseStep 3090079 = 4635119) B4635119
theorem B23783807 : Blo 1626512 23783807 := bstep (se 1 (by rfl) ⟨17837855, by rfl⟩ : syracuseStep 23783807 = 35675711) B35675711
theorem B2747135 : Blo 1626512 2747135 := bstep (se 1 (by rfl) ⟨2060351, by rfl⟩ : syracuseStep 2747135 = 4120703) B4120703
theorem B1830055 : Blo 1626512 1830055 := bstep (se 1 (by rfl) ⟨1372541, by rfl⟩ : syracuseStep 1830055 = 2745083) B2745083
theorem B1830127 : Blo 1626512 1830127 := bstep (se 1 (by rfl) ⟨1372595, by rfl⟩ : syracuseStep 1830127 = 2745191) B2745191
theorem B30093083 : Blo 1626512 30093083 := bstep (se 1 (by rfl) ⟨22569812, by rfl⟩ : syracuseStep 30093083 = 45139625) B45139625
theorem B20860699 : Blo 1626512 20860699 := bstep (se 1 (by rfl) ⟨15645524, by rfl⟩ : syracuseStep 20860699 = 31291049) B31291049
theorem B6180857 : Blo 1626512 6180857 := bstep (se 2 (by rfl) ⟨2317821, by rfl⟩ : syracuseStep 6180857 = 4635643) B4635643
theorem B10039367 : Blo 1626512 10039367 := bstep (se 1 (by rfl) ⟨7529525, by rfl⟩ : syracuseStep 10039367 = 15059051) B15059051
theorem B7050655 : Blo 1626512 7050655 := bstep (se 1 (by rfl) ⟨5287991, by rfl⟩ : syracuseStep 7050655 = 10575983) B10575983
theorem B46921355 : Blo 1626512 46921355 := bstep (se 1 (by rfl) ⟨35191016, by rfl⟩ : syracuseStep 46921355 = 70382033) B70382033
theorem B17602343 : Blo 1626512 17602343 := bstep (se 1 (by rfl) ⟨13201757, by rfl⟩ : syracuseStep 17602343 = 26403515) B26403515
theorem B17602433 : Blo 1626512 17602433 := bstep (se 2 (by rfl) ⟨6600912, by rfl⟩ : syracuseStep 17602433 = 13201825) B13201825
theorem B1628263 : Blo 1626512 1628263 := bstep (se 1 (by rfl) ⟨1221197, by rfl⟩ : syracuseStep 1628263 = 2442395) B2442395
theorem B8239481 : Blo 1626512 8239481 := bstep (se 2 (by rfl) ⟨3089805, by rfl⟩ : syracuseStep 8239481 = 6179611) B6179611
theorem B9263585 : Blo 1626512 9263585 := bstep (se 2 (by rfl) ⟨3473844, by rfl⟩ : syracuseStep 9263585 = 6947689) B6947689
theorem B33421967 : Blo 1626512 33421967 := bstep (se 1 (by rfl) ⟨25066475, by rfl⟩ : syracuseStep 33421967 = 50132951) B50132951
theorem B2440223 : Blo 1626512 2440223 := bstep (se 1 (by rfl) ⟨1830167, by rfl⟩ : syracuseStep 2440223 = 3660335) B3660335
theorem B2440427 : Blo 1626512 2440427 := bstep (se 1 (by rfl) ⟨1830320, by rfl⟩ : syracuseStep 2440427 = 3660641) B3660641
theorem B3661577 : Blo 1626512 3661577 := bstep (se 2 (by rfl) ⟨1373091, by rfl⟩ : syracuseStep 3661577 = 2746183) B2746183
theorem B3088363 : Blo 1626512 3088363 := bstep (se 1 (by rfl) ⟨2316272, by rfl⟩ : syracuseStep 3088363 = 4632545) B4632545
theorem B33423349 : Blo 1626512 33423349 := bstep (se 5 (by rfl) ⟨1566719, by rfl⟩ : syracuseStep 33423349 = 3133439) B3133439
theorem B6692911 : Blo 1626512 6692911 := bstep (se 1 (by rfl) ⟨5019683, by rfl⟩ : syracuseStep 6692911 = 10039367) B10039367
theorem B2933075 : Blo 1626512 2933075 := bstep (se 1 (by rfl) ⟨2199806, by rfl⟩ : syracuseStep 2933075 = 4399613) B4399613
theorem B27814265 : Blo 1626512 27814265 := bstep (se 2 (by rfl) ⟨10430349, by rfl⟩ : syracuseStep 27814265 = 20860699) B20860699
theorem B31280903 : Blo 1626512 31280903 := bstep (se 1 (by rfl) ⟨23460677, by rfl⟩ : syracuseStep 31280903 = 46921355) B46921355
theorem B11734895 : Blo 1626512 11734895 := bstep (se 1 (by rfl) ⟨8801171, by rfl⟩ : syracuseStep 11734895 = 17602343) B17602343
theorem B11734955 : Blo 1626512 11734955 := bstep (se 1 (by rfl) ⟨8801216, by rfl⟩ : syracuseStep 11734955 = 17602433) B17602433
theorem B5492987 : Blo 1626512 5492987 := bstep (se 1 (by rfl) ⟨4119740, by rfl⟩ : syracuseStep 5492987 = 8239481) B8239481
theorem B15855871 : Blo 1626512 15855871 := bstep (se 1 (by rfl) ⟨11891903, by rfl⟩ : syracuseStep 15855871 = 23783807) B23783807
theorem B1831423 : Blo 1626512 1831423 := bstep (se 1 (by rfl) ⟨1373567, by rfl⟩ : syracuseStep 1831423 = 2747135) B2747135
theorem B9400873 : Blo 1626512 9400873 := bstep (se 2 (by rfl) ⟨3525327, by rfl⟩ : syracuseStep 9400873 = 7050655) B7050655
theorem B1626815 : Blo 1626512 1626815 := bstep (se 1 (by rfl) ⟨1220111, by rfl⟩ : syracuseStep 1626815 = 2440223) B2440223
theorem B1626951 : Blo 1626512 1626951 := bstep (se 1 (by rfl) ⟨1220213, by rfl⟩ : syracuseStep 1626951 = 2440427) B2440427
theorem B4117817 : Blo 1626512 4117817 := bstep (se 2 (by rfl) ⟨1544181, by rfl⟩ : syracuseStep 4117817 = 3088363) B3088363
theorem B3659867 : Blo 1626512 3659867 := bstep (se 1 (by rfl) ⟨2744900, by rfl⟩ : syracuseStep 3659867 = 5489801) B5489801
theorem B4118759 : Blo 1626512 4118759 := bstep (se 1 (by rfl) ⟨3089069, by rfl⟩ : syracuseStep 4118759 = 6178139) B6178139
theorem B2440073 : Blo 1626512 2440073 := bstep (se 2 (by rfl) ⟨915027, by rfl⟩ : syracuseStep 2440073 = 1830055) B1830055
theorem B2440169 : Blo 1626512 2440169 := bstep (se 2 (by rfl) ⟨915063, by rfl⟩ : syracuseStep 2440169 = 1830127) B1830127
theorem B6175723 : Blo 1626512 6175723 := bstep (se 1 (by rfl) ⟨4631792, by rfl⟩ : syracuseStep 6175723 = 9263585) B9263585
theorem B22281311 : Blo 1626512 22281311 := bstep (se 1 (by rfl) ⟨16710983, by rfl⟩ : syracuseStep 22281311 = 33421967) B33421967
theorem B4120105 : Blo 1626512 4120105 := bstep (se 2 (by rfl) ⟨1545039, by rfl⟩ : syracuseStep 4120105 = 3090079) B3090079
theorem B2441051 : Blo 1626512 2441051 := bstep (se 1 (by rfl) ⟨1830788, by rfl⟩ : syracuseStep 2441051 = 3661577) B3661577
theorem B20062055 : Blo 1626512 20062055 := bstep (se 1 (by rfl) ⟨15046541, by rfl⟩ : syracuseStep 20062055 = 30093083) B30093083
theorem B44564465 : Blo 1626512 44564465 := bstep (se 2 (by rfl) ⟨16711674, by rfl⟩ : syracuseStep 44564465 = 33423349) B33423349
theorem B4120571 : Blo 1626512 4120571 := bstep (se 1 (by rfl) ⟨3090428, by rfl⟩ : syracuseStep 4120571 = 6180857) B6180857
theorem B3661991 : Blo 1626512 3661991 := bstep (se 1 (by rfl) ⟨2746493, by rfl⟩ : syracuseStep 3661991 = 5492987) B5492987
theorem B2441897 : Blo 1626512 2441897 := bstep (se 2 (by rfl) ⟨915711, by rfl⟩ : syracuseStep 2441897 = 1831423) B1831423
theorem B12534497 : Blo 1626512 12534497 := bstep (se 2 (by rfl) ⟨4700436, by rfl⟩ : syracuseStep 12534497 = 9400873) B9400873
theorem B2745211 : Blo 1626512 2745211 := bstep (se 1 (by rfl) ⟨2058908, by rfl⟩ : syracuseStep 2745211 = 4117817) B4117817
theorem B8234297 : Blo 1626512 8234297 := bstep (se 2 (by rfl) ⟨3087861, by rfl⟩ : syracuseStep 8234297 = 6175723) B6175723
theorem B2745839 : Blo 1626512 2745839 := bstep (se 1 (by rfl) ⟨2059379, by rfl⟩ : syracuseStep 2745839 = 4118759) B4118759
theorem B14854207 : Blo 1626512 14854207 := bstep (se 1 (by rfl) ⟨11140655, by rfl⟩ : syracuseStep 14854207 = 22281311) B22281311
theorem B2747047 : Blo 1626512 2747047 := bstep (se 1 (by rfl) ⟨2060285, by rfl⟩ : syracuseStep 2747047 = 4120571) B4120571
theorem B142782101 : Blo 1626512 142782101 := bstep (se 6 (by rfl) ⟨3346455, by rfl⟩ : syracuseStep 142782101 = 6692911) B6692911
theorem B18542843 : Blo 1626512 18542843 := bstep (se 1 (by rfl) ⟨13907132, by rfl⟩ : syracuseStep 18542843 = 27814265) B27814265
theorem B1626715 : Blo 1626512 1626715 := bstep (se 1 (by rfl) ⟨1220036, by rfl⟩ : syracuseStep 1626715 = 2440073) B2440073
theorem B1626779 : Blo 1626512 1626779 := bstep (se 1 (by rfl) ⟨1220084, by rfl⟩ : syracuseStep 1626779 = 2440169) B2440169
theorem B5493473 : Blo 1626512 5493473 := bstep (se 2 (by rfl) ⟨2060052, by rfl⟩ : syracuseStep 5493473 = 4120105) B4120105
theorem B20853935 : Blo 1626512 20853935 := bstep (se 1 (by rfl) ⟨15640451, by rfl⟩ : syracuseStep 20853935 = 31280903) B31280903
theorem B1627367 : Blo 1626512 1627367 := bstep (se 1 (by rfl) ⟨1220525, by rfl⟩ : syracuseStep 1627367 = 2441051) B2441051
theorem B13374703 : Blo 1626512 13374703 := bstep (se 1 (by rfl) ⟨10031027, by rfl⟩ : syracuseStep 13374703 = 20062055) B20062055
theorem B118838573 : Blo 1626512 118838573 := bstep (se 3 (by rfl) ⟨22282232, by rfl⟩ : syracuseStep 118838573 = 44564465) B44564465
theorem B1955383 : Blo 1626512 1955383 := bstep (se 1 (by rfl) ⟨1466537, by rfl⟩ : syracuseStep 1955383 = 2933075) B2933075
theorem B21141161 : Blo 1626512 21141161 := bstep (se 2 (by rfl) ⟨7927935, by rfl⟩ : syracuseStep 21141161 = 15855871) B15855871
theorem B2439911 : Blo 1626512 2439911 := bstep (se 1 (by rfl) ⟨1829933, by rfl⟩ : syracuseStep 2439911 = 3659867) B3659867
theorem B31293053 : Blo 1626512 31293053 := bstep (se 3 (by rfl) ⟨5867447, by rfl⟩ : syracuseStep 31293053 = 11734895) B11734895
theorem B7823303 : Blo 1626512 7823303 := bstep (se 1 (by rfl) ⟨5867477, by rfl⟩ : syracuseStep 7823303 = 11734955) B11734955
theorem B2441327 : Blo 1626512 2441327 := bstep (se 1 (by rfl) ⟨1830995, by rfl⟩ : syracuseStep 2441327 = 3661991) B3661991
theorem B12361895 : Blo 1626512 12361895 := bstep (se 1 (by rfl) ⟨9271421, by rfl⟩ : syracuseStep 12361895 = 18542843) B18542843
theorem B3662315 : Blo 1626512 3662315 := bstep (se 1 (by rfl) ⟨2746736, by rfl⟩ : syracuseStep 3662315 = 5493473) B5493473
theorem B8356331 : Blo 1626512 8356331 := bstep (se 1 (by rfl) ⟨6267248, by rfl⟩ : syracuseStep 8356331 = 12534497) B12534497
theorem B13902623 : Blo 1626512 13902623 := bstep (se 1 (by rfl) ⟨10426967, by rfl⟩ : syracuseStep 13902623 = 20853935) B20853935
theorem B79225715 : Blo 1626512 79225715 := bstep (se 1 (by rfl) ⟨59419286, by rfl⟩ : syracuseStep 79225715 = 118838573) B118838573
theorem B5489531 : Blo 1626512 5489531 := bstep (se 1 (by rfl) ⟨4117148, by rfl⟩ : syracuseStep 5489531 = 8234297) B8234297
theorem B3662729 : Blo 1626512 3662729 := bstep (se 2 (by rfl) ⟨1373523, by rfl⟩ : syracuseStep 3662729 = 2747047) B2747047
theorem B41714837 : Blo 1626512 41714837 := bstep (se 6 (by rfl) ⟨977691, by rfl⟩ : syracuseStep 41714837 = 1955383) B1955383
theorem B1830559 : Blo 1626512 1830559 := bstep (se 1 (by rfl) ⟨1372919, by rfl⟩ : syracuseStep 1830559 = 2745839) B2745839
theorem B14094107 : Blo 1626512 14094107 := bstep (se 1 (by rfl) ⟨10570580, by rfl⟩ : syracuseStep 14094107 = 21141161) B21141161
theorem B71331749 : Blo 1626512 71331749 := bstep (se 4 (by rfl) ⟨6687351, by rfl⟩ : syracuseStep 71331749 = 13374703) B13374703
theorem B1626607 : Blo 1626512 1626607 := bstep (se 1 (by rfl) ⟨1219955, by rfl⟩ : syracuseStep 1626607 = 2439911) B2439911
theorem B20862035 : Blo 1626512 20862035 := bstep (se 1 (by rfl) ⟨15646526, by rfl⟩ : syracuseStep 20862035 = 31293053) B31293053
theorem B95188067 : Blo 1626512 95188067 := bstep (se 1 (by rfl) ⟨71391050, by rfl⟩ : syracuseStep 95188067 = 142782101) B142782101
theorem B5215535 : Blo 1626512 5215535 := bstep (se 1 (by rfl) ⟨3911651, by rfl⟩ : syracuseStep 5215535 = 7823303) B7823303
theorem B19805609 : Blo 1626512 19805609 := bstep (se 2 (by rfl) ⟨7427103, by rfl⟩ : syracuseStep 19805609 = 14854207) B14854207
theorem B1627931 : Blo 1626512 1627931 := bstep (se 1 (by rfl) ⟨1220948, by rfl⟩ : syracuseStep 1627931 = 2441897) B2441897
theorem B3660281 : Blo 1626512 3660281 := bstep (se 2 (by rfl) ⟨1372605, by rfl⟩ : syracuseStep 3660281 = 2745211) B2745211
theorem B8241263 : Blo 1626512 8241263 := bstep (se 1 (by rfl) ⟨6180947, by rfl⟩ : syracuseStep 8241263 = 12361895) B12361895
theorem B2441543 : Blo 1626512 2441543 := bstep (se 1 (by rfl) ⟨1831157, by rfl⟩ : syracuseStep 2441543 = 3662315) B3662315
theorem B2441819 : Blo 1626512 2441819 := bstep (se 1 (by rfl) ⟨1831364, by rfl⟩ : syracuseStep 2441819 = 3662729) B3662729
theorem B22283549 : Blo 1626512 22283549 := bstep (se 3 (by rfl) ⟨4178165, by rfl⟩ : syracuseStep 22283549 = 8356331) B8356331
theorem B9268415 : Blo 1626512 9268415 := bstep (se 1 (by rfl) ⟨6951311, by rfl⟩ : syracuseStep 9268415 = 13902623) B13902623
theorem B52817143 : Blo 1626512 52817143 := bstep (se 1 (by rfl) ⟨39612857, by rfl⟩ : syracuseStep 52817143 = 79225715) B79225715
theorem B63458711 : Blo 1626512 63458711 := bstep (se 1 (by rfl) ⟨47594033, by rfl⟩ : syracuseStep 63458711 = 95188067) B95188067
theorem B3477023 : Blo 1626512 3477023 := bstep (se 1 (by rfl) ⟨2607767, by rfl⟩ : syracuseStep 3477023 = 5215535) B5215535
theorem B1627551 : Blo 1626512 1627551 := bstep (se 1 (by rfl) ⟨1220663, by rfl⟩ : syracuseStep 1627551 = 2441327) B2441327
theorem B3659687 : Blo 1626512 3659687 := bstep (se 1 (by rfl) ⟨2744765, by rfl⟩ : syracuseStep 3659687 = 5489531) B5489531
theorem B13908023 : Blo 1626512 13908023 := bstep (se 1 (by rfl) ⟨10431017, by rfl⟩ : syracuseStep 13908023 = 20862035) B20862035
theorem B27809891 : Blo 1626512 27809891 := bstep (se 1 (by rfl) ⟨20857418, by rfl⟩ : syracuseStep 27809891 = 41714837) B41714837
theorem B13203739 : Blo 1626512 13203739 := bstep (se 1 (by rfl) ⟨9902804, by rfl⟩ : syracuseStep 13203739 = 19805609) B19805609
theorem B2440187 : Blo 1626512 2440187 := bstep (se 1 (by rfl) ⟨1830140, by rfl⟩ : syracuseStep 2440187 = 3660281) B3660281
theorem B2440745 : Blo 1626512 2440745 := bstep (se 2 (by rfl) ⟨915279, by rfl⟩ : syracuseStep 2440745 = 1830559) B1830559
theorem B9396071 : Blo 1626512 9396071 := bstep (se 1 (by rfl) ⟨7047053, by rfl⟩ : syracuseStep 9396071 = 14094107) B14094107
theorem B47554499 : Blo 1626512 47554499 := bstep (se 1 (by rfl) ⟨35665874, by rfl⟩ : syracuseStep 47554499 = 71331749) B71331749
theorem B17604985 : Blo 1626512 17604985 := bstep (se 2 (by rfl) ⟨6601869, by rfl⟩ : syracuseStep 17604985 = 13203739) B13203739
theorem B18539927 : Blo 1626512 18539927 := bstep (se 1 (by rfl) ⟨13904945, by rfl⟩ : syracuseStep 18539927 = 27809891) B27809891
theorem B6178943 : Blo 1626512 6178943 := bstep (se 1 (by rfl) ⟨4634207, by rfl⟩ : syracuseStep 6178943 = 9268415) B9268415
theorem B42305807 : Blo 1626512 42305807 := bstep (se 1 (by rfl) ⟨31729355, by rfl⟩ : syracuseStep 42305807 = 63458711) B63458711
theorem B14855699 : Blo 1626512 14855699 := bstep (se 1 (by rfl) ⟨11141774, by rfl⟩ : syracuseStep 14855699 = 22283549) B22283549
theorem B70422857 : Blo 1626512 70422857 := bstep (se 2 (by rfl) ⟨26408571, by rfl⟩ : syracuseStep 70422857 = 52817143) B52817143
theorem B1626791 : Blo 1626512 1626791 := bstep (se 1 (by rfl) ⟨1220093, by rfl⟩ : syracuseStep 1626791 = 2440187) B2440187
theorem B1627163 : Blo 1626512 1627163 := bstep (se 1 (by rfl) ⟨1220372, by rfl⟩ : syracuseStep 1627163 = 2440745) B2440745
theorem B6264047 : Blo 1626512 6264047 := bstep (se 1 (by rfl) ⟨4698035, by rfl⟩ : syracuseStep 6264047 = 9396071) B9396071
theorem B5494175 : Blo 1626512 5494175 := bstep (se 1 (by rfl) ⟨4120631, by rfl⟩ : syracuseStep 5494175 = 8241263) B8241263
theorem B1627695 : Blo 1626512 1627695 := bstep (se 1 (by rfl) ⟨1220771, by rfl⟩ : syracuseStep 1627695 = 2441543) B2441543
theorem B1627879 : Blo 1626512 1627879 := bstep (se 1 (by rfl) ⟨1220909, by rfl⟩ : syracuseStep 1627879 = 2441819) B2441819
theorem B2439791 : Blo 1626512 2439791 := bstep (se 1 (by rfl) ⟨1829843, by rfl⟩ : syracuseStep 2439791 = 3659687) B3659687
theorem B9272015 : Blo 1626512 9272015 := bstep (se 1 (by rfl) ⟨6954011, by rfl⟩ : syracuseStep 9272015 = 13908023) B13908023
theorem B2318015 : Blo 1626512 2318015 := bstep (se 1 (by rfl) ⟨1738511, by rfl⟩ : syracuseStep 2318015 = 3477023) B3477023
theorem B31702999 : Blo 1626512 31702999 := bstep (se 1 (by rfl) ⟨23777249, by rfl⟩ : syracuseStep 31702999 = 47554499) B47554499
theorem B46948571 : Blo 1626512 46948571 := bstep (se 1 (by rfl) ⟨35211428, by rfl⟩ : syracuseStep 46948571 = 70422857) B70422857
theorem B3662783 : Blo 1626512 3662783 := bstep (se 1 (by rfl) ⟨2747087, by rfl⟩ : syracuseStep 3662783 = 5494175) B5494175
theorem B23473313 : Blo 1626512 23473313 := bstep (se 2 (by rfl) ⟨8802492, by rfl⟩ : syracuseStep 23473313 = 17604985) B17604985
theorem B1626527 : Blo 1626512 1626527 := bstep (se 1 (by rfl) ⟨1219895, by rfl⟩ : syracuseStep 1626527 = 2439791) B2439791
theorem B6181343 : Blo 1626512 6181343 := bstep (se 1 (by rfl) ⟨4636007, by rfl⟩ : syracuseStep 6181343 = 9272015) B9272015
theorem B6181373 : Blo 1626512 6181373 := bstep (se 3 (by rfl) ⟨1159007, by rfl⟩ : syracuseStep 6181373 = 2318015) B2318015
theorem B4176031 : Blo 1626512 4176031 := bstep (se 1 (by rfl) ⟨3132023, by rfl⟩ : syracuseStep 4176031 = 6264047) B6264047
theorem B12359951 : Blo 1626512 12359951 := bstep (se 1 (by rfl) ⟨9269963, by rfl⟩ : syracuseStep 12359951 = 18539927) B18539927
theorem B4119295 : Blo 1626512 4119295 := bstep (se 1 (by rfl) ⟨3089471, by rfl⟩ : syracuseStep 4119295 = 6178943) B6178943
theorem B28203871 : Blo 1626512 28203871 := bstep (se 1 (by rfl) ⟨21152903, by rfl⟩ : syracuseStep 28203871 = 42305807) B42305807
theorem B9903799 : Blo 1626512 9903799 := bstep (se 1 (by rfl) ⟨7427849, by rfl⟩ : syracuseStep 9903799 = 14855699) B14855699
theorem B42270665 : Blo 1626512 42270665 := bstep (se 2 (by rfl) ⟨15851499, by rfl⟩ : syracuseStep 42270665 = 31702999) B31702999
theorem B4120895 : Blo 1626512 4120895 := bstep (se 1 (by rfl) ⟨3090671, by rfl⟩ : syracuseStep 4120895 = 6181343) B6181343
theorem B4120915 : Blo 1626512 4120915 := bstep (se 1 (by rfl) ⟨3090686, by rfl⟩ : syracuseStep 4120915 = 6181373) B6181373
theorem B2441855 : Blo 1626512 2441855 := bstep (se 1 (by rfl) ⟨1831391, by rfl⟩ : syracuseStep 2441855 = 3662783) B3662783
theorem B15648875 : Blo 1626512 15648875 := bstep (se 1 (by rfl) ⟨11736656, by rfl⟩ : syracuseStep 15648875 = 23473313) B23473313
theorem B5492393 : Blo 1626512 5492393 := bstep (se 2 (by rfl) ⟨2059647, by rfl⟩ : syracuseStep 5492393 = 4119295) B4119295
theorem B37605161 : Blo 1626512 37605161 := bstep (se 2 (by rfl) ⟨14101935, by rfl⟩ : syracuseStep 37605161 = 28203871) B28203871
theorem B31299047 : Blo 1626512 31299047 := bstep (se 1 (by rfl) ⟨23474285, by rfl⟩ : syracuseStep 31299047 = 46948571) B46948571
theorem B5568041 : Blo 1626512 5568041 := bstep (se 2 (by rfl) ⟨2088015, by rfl⟩ : syracuseStep 5568041 = 4176031) B4176031
theorem B8239967 : Blo 1626512 8239967 := bstep (se 1 (by rfl) ⟨6179975, by rfl⟩ : syracuseStep 8239967 = 12359951) B12359951
theorem B450887093 : Blo 1626512 450887093 := bstep (se 5 (by rfl) ⟨21135332, by rfl⟩ : syracuseStep 450887093 = 42270665) B42270665
theorem B13205065 : Blo 1626512 13205065 := bstep (se 2 (by rfl) ⟨4951899, by rfl⟩ : syracuseStep 13205065 = 9903799) B9903799
theorem B20866031 : Blo 1626512 20866031 := bstep (se 1 (by rfl) ⟨15649523, by rfl⟩ : syracuseStep 20866031 = 31299047) B31299047
theorem B17606753 : Blo 1626512 17606753 := bstep (se 2 (by rfl) ⟨6602532, by rfl⟩ : syracuseStep 17606753 = 13205065) B13205065
theorem B100280429 : Blo 1626512 100280429 := bstep (se 3 (by rfl) ⟨18802580, by rfl⟩ : syracuseStep 100280429 = 37605161) B37605161
theorem B300591395 : Blo 1626512 300591395 := bstep (se 1 (by rfl) ⟨225443546, by rfl⟩ : syracuseStep 300591395 = 450887093) B450887093
theorem B2747263 : Blo 1626512 2747263 := bstep (se 1 (by rfl) ⟨2060447, by rfl⟩ : syracuseStep 2747263 = 4120895) B4120895
theorem B10432583 : Blo 1626512 10432583 := bstep (se 1 (by rfl) ⟨7824437, by rfl⟩ : syracuseStep 10432583 = 15648875) B15648875
theorem B14848109 : Blo 1626512 14848109 := bstep (se 3 (by rfl) ⟨2784020, by rfl⟩ : syracuseStep 14848109 = 5568041) B5568041
theorem B5493311 : Blo 1626512 5493311 := bstep (se 1 (by rfl) ⟨4119983, by rfl⟩ : syracuseStep 5493311 = 8239967) B8239967
theorem B1627903 : Blo 1626512 1627903 := bstep (se 1 (by rfl) ⟨1220927, by rfl⟩ : syracuseStep 1627903 = 2441855) B2441855
theorem B5494553 : Blo 1626512 5494553 := bstep (se 2 (by rfl) ⟨2060457, by rfl⟩ : syracuseStep 5494553 = 4120915) B4120915
theorem B3661595 : Blo 1626512 3661595 := bstep (se 1 (by rfl) ⟨2746196, by rfl⟩ : syracuseStep 3661595 = 5492393) B5492393
theorem B6955055 : Blo 1626512 6955055 := bstep (se 1 (by rfl) ⟨5216291, by rfl⟩ : syracuseStep 6955055 = 10432583) B10432583
theorem B3662207 : Blo 1626512 3662207 := bstep (se 1 (by rfl) ⟨2746655, by rfl⟩ : syracuseStep 3662207 = 5493311) B5493311
theorem B13910687 : Blo 1626512 13910687 := bstep (se 1 (by rfl) ⟨10433015, by rfl⟩ : syracuseStep 13910687 = 20866031) B20866031
theorem B3663017 : Blo 1626512 3663017 := bstep (se 2 (by rfl) ⟨1373631, by rfl⟩ : syracuseStep 3663017 = 2747263) B2747263
theorem B3663035 : Blo 1626512 3663035 := bstep (se 1 (by rfl) ⟨2747276, by rfl⟩ : syracuseStep 3663035 = 5494553) B5494553
theorem B200394263 : Blo 1626512 200394263 := bstep (se 1 (by rfl) ⟨150295697, by rfl⟩ : syracuseStep 200394263 = 300591395) B300591395
theorem B9898739 : Blo 1626512 9898739 := bstep (se 1 (by rfl) ⟨7424054, by rfl⟩ : syracuseStep 9898739 = 14848109) B14848109
theorem B11737835 : Blo 1626512 11737835 := bstep (se 1 (by rfl) ⟨8803376, by rfl⟩ : syracuseStep 11737835 = 17606753) B17606753
theorem B66853619 : Blo 1626512 66853619 := bstep (se 1 (by rfl) ⟨50140214, by rfl⟩ : syracuseStep 66853619 = 100280429) B100280429
theorem B2441063 : Blo 1626512 2441063 := bstep (se 1 (by rfl) ⟨1830797, by rfl⟩ : syracuseStep 2441063 = 3661595) B3661595
theorem B4636703 : Blo 1626512 4636703 := bstep (se 1 (by rfl) ⟨3477527, by rfl⟩ : syracuseStep 4636703 = 6955055) B6955055
theorem B2441471 : Blo 1626512 2441471 := bstep (se 1 (by rfl) ⟨1831103, by rfl⟩ : syracuseStep 2441471 = 3662207) B3662207
theorem B9273791 : Blo 1626512 9273791 := bstep (se 1 (by rfl) ⟨6955343, by rfl⟩ : syracuseStep 9273791 = 13910687) B13910687
theorem B2442011 : Blo 1626512 2442011 := bstep (se 1 (by rfl) ⟨1831508, by rfl⟩ : syracuseStep 2442011 = 3663017) B3663017
theorem B2442023 : Blo 1626512 2442023 := bstep (se 1 (by rfl) ⟨1831517, by rfl⟩ : syracuseStep 2442023 = 3663035) B3663035
theorem B133596175 : Blo 1626512 133596175 := bstep (se 1 (by rfl) ⟨100197131, by rfl⟩ : syracuseStep 133596175 = 200394263) B200394263
theorem B7825223 : Blo 1626512 7825223 := bstep (se 1 (by rfl) ⟨5868917, by rfl⟩ : syracuseStep 7825223 = 11737835) B11737835
theorem B6599159 : Blo 1626512 6599159 := bstep (se 1 (by rfl) ⟨4949369, by rfl⟩ : syracuseStep 6599159 = 9898739) B9898739
theorem B44569079 : Blo 1626512 44569079 := bstep (se 1 (by rfl) ⟨33426809, by rfl⟩ : syracuseStep 44569079 = 66853619) B66853619
theorem B1627375 : Blo 1626512 1627375 := bstep (se 1 (by rfl) ⟨1220531, by rfl⟩ : syracuseStep 1627375 = 2441063) B2441063
theorem B4399439 : Blo 1626512 4399439 := bstep (se 1 (by rfl) ⟨3299579, by rfl⟩ : syracuseStep 4399439 = 6599159) B6599159
theorem B29712719 : Blo 1626512 29712719 := bstep (se 1 (by rfl) ⟨22284539, by rfl⟩ : syracuseStep 29712719 = 44569079) B44569079
theorem B178128233 : Blo 1626512 178128233 := bstep (se 2 (by rfl) ⟨66798087, by rfl⟩ : syracuseStep 178128233 = 133596175) B133596175
theorem B3091135 : Blo 1626512 3091135 := bstep (se 1 (by rfl) ⟨2318351, by rfl⟩ : syracuseStep 3091135 = 4636703) B4636703
theorem B1627647 : Blo 1626512 1627647 := bstep (se 1 (by rfl) ⟨1220735, by rfl⟩ : syracuseStep 1627647 = 2441471) B2441471
theorem B6182527 : Blo 1626512 6182527 := bstep (se 1 (by rfl) ⟨4636895, by rfl⟩ : syracuseStep 6182527 = 9273791) B9273791
theorem B1628007 : Blo 1626512 1628007 := bstep (se 1 (by rfl) ⟨1221005, by rfl⟩ : syracuseStep 1628007 = 2442011) B2442011
theorem B1628015 : Blo 1626512 1628015 := bstep (se 1 (by rfl) ⟨1221011, by rfl⟩ : syracuseStep 1628015 = 2442023) B2442023
theorem B5216815 : Blo 1626512 5216815 := bstep (se 1 (by rfl) ⟨3912611, by rfl⟩ : syracuseStep 5216815 = 7825223) B7825223
theorem B19808479 : Blo 1626512 19808479 := bstep (se 1 (by rfl) ⟨14856359, by rfl⟩ : syracuseStep 19808479 = 29712719) B29712719
theorem B118752155 : Blo 1626512 118752155 := bstep (se 1 (by rfl) ⟨89064116, by rfl⟩ : syracuseStep 118752155 = 178128233) B178128233
theorem B4121513 : Blo 1626512 4121513 := bstep (se 2 (by rfl) ⟨1545567, by rfl⟩ : syracuseStep 4121513 = 3091135) B3091135
theorem B8243369 : Blo 1626512 8243369 := bstep (se 2 (by rfl) ⟨3091263, by rfl⟩ : syracuseStep 8243369 = 6182527) B6182527
theorem B27823013 : Blo 1626512 27823013 := bstep (se 4 (by rfl) ⟨2608407, by rfl⟩ : syracuseStep 27823013 = 5216815) B5216815
theorem B46927349 : Blo 1626512 46927349 := bstep (se 5 (by rfl) ⟨2199719, by rfl⟩ : syracuseStep 46927349 = 4399439) B4399439
theorem B26411305 : Blo 1626512 26411305 := bstep (se 2 (by rfl) ⟨9904239, by rfl⟩ : syracuseStep 26411305 = 19808479) B19808479
theorem B79168103 : Blo 1626512 79168103 := bstep (se 1 (by rfl) ⟨59376077, by rfl⟩ : syracuseStep 79168103 = 118752155) B118752155
theorem B18548675 : Blo 1626512 18548675 := bstep (se 1 (by rfl) ⟨13911506, by rfl⟩ : syracuseStep 18548675 = 27823013) B27823013
theorem B2747675 : Blo 1626512 2747675 := bstep (se 1 (by rfl) ⟨2060756, by rfl⟩ : syracuseStep 2747675 = 4121513) B4121513
theorem B5495579 : Blo 1626512 5495579 := bstep (se 1 (by rfl) ⟨4121684, by rfl⟩ : syracuseStep 5495579 = 8243369) B8243369
theorem B31284899 : Blo 1626512 31284899 := bstep (se 1 (by rfl) ⟨23463674, by rfl⟩ : syracuseStep 31284899 = 46927349) B46927349
theorem B3663719 : Blo 1626512 3663719 := bstep (se 1 (by rfl) ⟨2747789, by rfl⟩ : syracuseStep 3663719 = 5495579) B5495579
theorem B12365783 : Blo 1626512 12365783 := bstep (se 1 (by rfl) ⟨9274337, by rfl⟩ : syracuseStep 12365783 = 18548675) B18548675
theorem B1831783 : Blo 1626512 1831783 := bstep (se 1 (by rfl) ⟨1373837, by rfl⟩ : syracuseStep 1831783 = 2747675) B2747675
theorem B35215073 : Blo 1626512 35215073 := bstep (se 2 (by rfl) ⟨13205652, by rfl⟩ : syracuseStep 35215073 = 26411305) B26411305
theorem B52778735 : Blo 1626512 52778735 := bstep (se 1 (by rfl) ⟨39584051, by rfl⟩ : syracuseStep 52778735 = 79168103) B79168103
theorem B20856599 : Blo 1626512 20856599 := bstep (se 1 (by rfl) ⟨15642449, by rfl⟩ : syracuseStep 20856599 = 31284899) B31284899
theorem B2442377 : Blo 1626512 2442377 := bstep (se 2 (by rfl) ⟨915891, by rfl⟩ : syracuseStep 2442377 = 1831783) B1831783
theorem B35185823 : Blo 1626512 35185823 := bstep (se 1 (by rfl) ⟨26389367, by rfl⟩ : syracuseStep 35185823 = 52778735) B52778735
theorem B2442479 : Blo 1626512 2442479 := bstep (se 1 (by rfl) ⟨1831859, by rfl⟩ : syracuseStep 2442479 = 3663719) B3663719
theorem B13904399 : Blo 1626512 13904399 := bstep (se 1 (by rfl) ⟨10428299, by rfl⟩ : syracuseStep 13904399 = 20856599) B20856599
theorem B8243855 : Blo 1626512 8243855 := bstep (se 1 (by rfl) ⟨6182891, by rfl⟩ : syracuseStep 8243855 = 12365783) B12365783
theorem B23476715 : Blo 1626512 23476715 := bstep (se 1 (by rfl) ⟨17607536, by rfl⟩ : syracuseStep 23476715 = 35215073) B35215073
theorem B23457215 : Blo 1626512 23457215 := bstep (se 1 (by rfl) ⟨17592911, by rfl⟩ : syracuseStep 23457215 = 35185823) B35185823
theorem B15651143 : Blo 1626512 15651143 := bstep (se 1 (by rfl) ⟨11738357, by rfl⟩ : syracuseStep 15651143 = 23476715) B23476715
theorem B9269599 : Blo 1626512 9269599 := bstep (se 1 (by rfl) ⟨6952199, by rfl⟩ : syracuseStep 9269599 = 13904399) B13904399
theorem B1628251 : Blo 1626512 1628251 := bstep (se 1 (by rfl) ⟨1221188, by rfl⟩ : syracuseStep 1628251 = 2442377) B2442377
theorem B1628319 : Blo 1626512 1628319 := bstep (se 1 (by rfl) ⟨1221239, by rfl⟩ : syracuseStep 1628319 = 2442479) B2442479
theorem B5495903 : Blo 1626512 5495903 := bstep (se 1 (by rfl) ⟨4121927, by rfl⟩ : syracuseStep 5495903 = 8243855) B8243855
theorem B3663935 : Blo 1626512 3663935 := bstep (se 1 (by rfl) ⟨2747951, by rfl⟩ : syracuseStep 3663935 = 5495903) B5495903
theorem B10434095 : Blo 1626512 10434095 := bstep (se 1 (by rfl) ⟨7825571, by rfl⟩ : syracuseStep 10434095 = 15651143) B15651143
theorem B12359465 : Blo 1626512 12359465 := bstep (se 2 (by rfl) ⟨4634799, by rfl⟩ : syracuseStep 12359465 = 9269599) B9269599
theorem B62552573 : Blo 1626512 62552573 := bstep (se 3 (by rfl) ⟨11728607, by rfl⟩ : syracuseStep 62552573 = 23457215) B23457215
theorem B6956063 : Blo 1626512 6956063 := bstep (se 1 (by rfl) ⟨5217047, by rfl⟩ : syracuseStep 6956063 = 10434095) B10434095
theorem B2442623 : Blo 1626512 2442623 := bstep (se 1 (by rfl) ⟨1831967, by rfl⟩ : syracuseStep 2442623 = 3663935) B3663935
theorem B41701715 : Blo 1626512 41701715 := bstep (se 1 (by rfl) ⟨31276286, by rfl⟩ : syracuseStep 41701715 = 62552573) B62552573
theorem B8239643 : Blo 1626512 8239643 := bstep (se 1 (by rfl) ⟨6179732, by rfl⟩ : syracuseStep 8239643 = 12359465) B12359465
theorem B4637375 : Blo 1626512 4637375 := bstep (se 1 (by rfl) ⟨3478031, by rfl⟩ : syracuseStep 4637375 = 6956063) B6956063
theorem B5493095 : Blo 1626512 5493095 := bstep (se 1 (by rfl) ⟨4119821, by rfl⟩ : syracuseStep 5493095 = 8239643) B8239643
theorem B27801143 : Blo 1626512 27801143 := bstep (se 1 (by rfl) ⟨20850857, by rfl⟩ : syracuseStep 27801143 = 41701715) B41701715
theorem B1628415 : Blo 1626512 1628415 := bstep (se 1 (by rfl) ⟨1221311, by rfl⟩ : syracuseStep 1628415 = 2442623) B2442623
theorem B3662063 : Blo 1626512 3662063 := bstep (se 1 (by rfl) ⟨2746547, by rfl⟩ : syracuseStep 3662063 = 5493095) B5493095
theorem B3091583 : Blo 1626512 3091583 := bstep (se 1 (by rfl) ⟨2318687, by rfl⟩ : syracuseStep 3091583 = 4637375) B4637375
theorem B18534095 : Blo 1626512 18534095 := bstep (se 1 (by rfl) ⟨13900571, by rfl⟩ : syracuseStep 18534095 = 27801143) B27801143
theorem B2441375 : Blo 1626512 2441375 := bstep (se 1 (by rfl) ⟨1831031, by rfl⟩ : syracuseStep 2441375 = 3662063) B3662063
theorem B12356063 : Blo 1626512 12356063 := bstep (se 1 (by rfl) ⟨9267047, by rfl⟩ : syracuseStep 12356063 = 18534095) B18534095
theorem B2061055 : Blo 1626512 2061055 := bstep (se 1 (by rfl) ⟨1545791, by rfl⟩ : syracuseStep 2061055 = 3091583) B3091583
theorem B2748073 : Blo 1626512 2748073 := bstep (se 2 (by rfl) ⟨1030527, by rfl⟩ : syracuseStep 2748073 = 2061055) B2061055
theorem B8237375 : Blo 1626512 8237375 := bstep (se 1 (by rfl) ⟨6178031, by rfl⟩ : syracuseStep 8237375 = 12356063) B12356063
theorem B1627583 : Blo 1626512 1627583 := bstep (se 1 (by rfl) ⟨1220687, by rfl⟩ : syracuseStep 1627583 = 2441375) B2441375
theorem B3664097 : Blo 1626512 3664097 := bstep (se 2 (by rfl) ⟨1374036, by rfl⟩ : syracuseStep 3664097 = 2748073) B2748073
theorem B5491583 : Blo 1626512 5491583 := bstep (se 1 (by rfl) ⟨4118687, by rfl⟩ : syracuseStep 5491583 = 8237375) B8237375
theorem B2442731 : Blo 1626512 2442731 := bstep (se 1 (by rfl) ⟨1832048, by rfl⟩ : syracuseStep 2442731 = 3664097) B3664097
theorem B3661055 : Blo 1626512 3661055 := bstep (se 1 (by rfl) ⟨2745791, by rfl⟩ : syracuseStep 3661055 = 5491583) B5491583
theorem B1628487 : Blo 1626512 1628487 := bstep (se 1 (by rfl) ⟨1221365, by rfl⟩ : syracuseStep 1628487 = 2442731) B2442731
theorem B2440703 : Blo 1626512 2440703 := bstep (se 1 (by rfl) ⟨1830527, by rfl⟩ : syracuseStep 2440703 = 3661055) B3661055
theorem B1627135 : Blo 1626512 1627135 := bstep (se 1 (by rfl) ⟨1220351, by rfl⟩ : syracuseStep 1627135 = 2440703) B2440703

theorem C0 (j : ℕ) (h1 : 406628 ≤ j) (h2 : j ≤ 407127) : Blo 1626512 (4 * j + 3) := by
  interval_cases j
  · exact B1626515
  · exact B1626519
  · exact B1626523
  · exact B1626527
  · exact B1626531
  · exact B1626535
  · exact B1626539
  · exact B1626543
  · exact B1626547
  · exact B1626551
  · exact B1626555
  · exact B1626559
  · exact B1626563
  · exact B1626567
  · exact B1626571
  · exact B1626575
  · exact B1626579
  · exact B1626583
  · exact B1626587
  · exact B1626591
  · exact B1626595
  · exact B1626599
  · exact B1626603
  · exact B1626607
  · exact B1626611
  · exact B1626615
  · exact B1626619
  · exact B1626623
  · exact B1626627
  · exact B1626631
  · exact B1626635
  · exact B1626639
  · exact B1626643
  · exact B1626647
  · exact B1626651
  · exact B1626655
  · exact B1626659
  · exact B1626663
  · exact B1626667
  · exact B1626671
  · exact B1626675
  · exact B1626679
  · exact B1626683
  · exact B1626687
  · exact B1626691
  · exact B1626695
  · exact B1626699
  · exact B1626703
  · exact B1626707
  · exact B1626711
  · exact B1626715
  · exact B1626719
  · exact B1626723
  · exact B1626727
  · exact B1626731
  · exact B1626735
  · exact B1626739
  · exact B1626743
  · exact B1626747
  · exact B1626751
  · exact B1626755
  · exact B1626759
  · exact B1626763
  · exact B1626767
  · exact B1626771
  · exact B1626775
  · exact B1626779
  · exact B1626783
  · exact B1626787
  · exact B1626791
  · exact B1626795
  · exact B1626799
  · exact B1626803
  · exact B1626807
  · exact B1626811
  · exact B1626815
  · exact B1626819
  · exact B1626823
  · exact B1626827
  · exact B1626831
  · exact B1626835
  · exact B1626839
  · exact B1626843
  · exact B1626847
  · exact B1626851
  · exact B1626855
  · exact B1626859
  · exact B1626863
  · exact B1626867
  · exact B1626871
  · exact B1626875
  · exact B1626879
  · exact B1626883
  · exact B1626887
  · exact B1626891
  · exact B1626895
  · exact B1626899
  · exact B1626903
  · exact B1626907
  · exact B1626911
  · exact B1626915
  · exact B1626919
  · exact B1626923
  · exact B1626927
  · exact B1626931
  · exact B1626935
  · exact B1626939
  · exact B1626943
  · exact B1626947
  · exact B1626951
  · exact B1626955
  · exact B1626959
  · exact B1626963
  · exact B1626967
  · exact B1626971
  · exact B1626975
  · exact B1626979
  · exact B1626983
  · exact B1626987
  · exact B1626991
  · exact B1626995
  · exact B1626999
  · exact B1627003
  · exact B1627007
  · exact B1627011
  · exact B1627015
  · exact B1627019
  · exact B1627023
  · exact B1627027
  · exact B1627031
  · exact B1627035
  · exact B1627039
  · exact B1627043
  · exact B1627047
  · exact B1627051
  · exact B1627055
  · exact B1627059
  · exact B1627063
  · exact B1627067
  · exact B1627071
  · exact B1627075
  · exact B1627079
  · exact B1627083
  · exact B1627087
  · exact B1627091
  · exact B1627095
  · exact B1627099
  · exact B1627103
  · exact B1627107
  · exact B1627111
  · exact B1627115
  · exact B1627119
  · exact B1627123
  · exact B1627127
  · exact B1627131
  · exact B1627135
  · exact B1627139
  · exact B1627143
  · exact B1627147
  · exact B1627151
  · exact B1627155
  · exact B1627159
  · exact B1627163
  · exact B1627167
  · exact B1627171
  · exact B1627175
  · exact B1627179
  · exact B1627183
  · exact B1627187
  · exact B1627191
  · exact B1627195
  · exact B1627199
  · exact B1627203
  · exact B1627207
  · exact B1627211
  · exact B1627215
  · exact B1627219
  · exact B1627223
  · exact B1627227
  · exact B1627231
  · exact B1627235
  · exact B1627239
  · exact B1627243
  · exact B1627247
  · exact B1627251
  · exact B1627255
  · exact B1627259
  · exact B1627263
  · exact B1627267
  · exact B1627271
  · exact B1627275
  · exact B1627279
  · exact B1627283
  · exact B1627287
  · exact B1627291
  · exact B1627295
  · exact B1627299
  · exact B1627303
  · exact B1627307
  · exact B1627311
  · exact B1627315
  · exact B1627319
  · exact B1627323
  · exact B1627327
  · exact B1627331
  · exact B1627335
  · exact B1627339
  · exact B1627343
  · exact B1627347
  · exact B1627351
  · exact B1627355
  · exact B1627359
  · exact B1627363
  · exact B1627367
  · exact B1627371
  · exact B1627375
  · exact B1627379
  · exact B1627383
  · exact B1627387
  · exact B1627391
  · exact B1627395
  · exact B1627399
  · exact B1627403
  · exact B1627407
  · exact B1627411
  · exact B1627415
  · exact B1627419
  · exact B1627423
  · exact B1627427
  · exact B1627431
  · exact B1627435
  · exact B1627439
  · exact B1627443
  · exact B1627447
  · exact B1627451
  · exact B1627455
  · exact B1627459
  · exact B1627463
  · exact B1627467
  · exact B1627471
  · exact B1627475
  · exact B1627479
  · exact B1627483
  · exact B1627487
  · exact B1627491
  · exact B1627495
  · exact B1627499
  · exact B1627503
  · exact B1627507
  · exact B1627511
  · exact B1627515
  · exact B1627519
  · exact B1627523
  · exact B1627527
  · exact B1627531
  · exact B1627535
  · exact B1627539
  · exact B1627543
  · exact B1627547
  · exact B1627551
  · exact B1627555
  · exact B1627559
  · exact B1627563
  · exact B1627567
  · exact B1627571
  · exact B1627575
  · exact B1627579
  · exact B1627583
  · exact B1627587
  · exact B1627591
  · exact B1627595
  · exact B1627599
  · exact B1627603
  · exact B1627607
  · exact B1627611
  · exact B1627615
  · exact B1627619
  · exact B1627623
  · exact B1627627
  · exact B1627631
  · exact B1627635
  · exact B1627639
  · exact B1627643
  · exact B1627647
  · exact B1627651
  · exact B1627655
  · exact B1627659
  · exact B1627663
  · exact B1627667
  · exact B1627671
  · exact B1627675
  · exact B1627679
  · exact B1627683
  · exact B1627687
  · exact B1627691
  · exact B1627695
  · exact B1627699
  · exact B1627703
  · exact B1627707
  · exact B1627711
  · exact B1627715
  · exact B1627719
  · exact B1627723
  · exact B1627727
  · exact B1627731
  · exact B1627735
  · exact B1627739
  · exact B1627743
  · exact B1627747
  · exact B1627751
  · exact B1627755
  · exact B1627759
  · exact B1627763
  · exact B1627767
  · exact B1627771
  · exact B1627775
  · exact B1627779
  · exact B1627783
  · exact B1627787
  · exact B1627791
  · exact B1627795
  · exact B1627799
  · exact B1627803
  · exact B1627807
  · exact B1627811
  · exact B1627815
  · exact B1627819
  · exact B1627823
  · exact B1627827
  · exact B1627831
  · exact B1627835
  · exact B1627839
  · exact B1627843
  · exact B1627847
  · exact B1627851
  · exact B1627855
  · exact B1627859
  · exact B1627863
  · exact B1627867
  · exact B1627871
  · exact B1627875
  · exact B1627879
  · exact B1627883
  · exact B1627887
  · exact B1627891
  · exact B1627895
  · exact B1627899
  · exact B1627903
  · exact B1627907
  · exact B1627911
  · exact B1627915
  · exact B1627919
  · exact B1627923
  · exact B1627927
  · exact B1627931
  · exact B1627935
  · exact B1627939
  · exact B1627943
  · exact B1627947
  · exact B1627951
  · exact B1627955
  · exact B1627959
  · exact B1627963
  · exact B1627967
  · exact B1627971
  · exact B1627975
  · exact B1627979
  · exact B1627983
  · exact B1627987
  · exact B1627991
  · exact B1627995
  · exact B1627999
  · exact B1628003
  · exact B1628007
  · exact B1628011
  · exact B1628015
  · exact B1628019
  · exact B1628023
  · exact B1628027
  · exact B1628031
  · exact B1628035
  · exact B1628039
  · exact B1628043
  · exact B1628047
  · exact B1628051
  · exact B1628055
  · exact B1628059
  · exact B1628063
  · exact B1628067
  · exact B1628071
  · exact B1628075
  · exact B1628079
  · exact B1628083
  · exact B1628087
  · exact B1628091
  · exact B1628095
  · exact B1628099
  · exact B1628103
  · exact B1628107
  · exact B1628111
  · exact B1628115
  · exact B1628119
  · exact B1628123
  · exact B1628127
  · exact B1628131
  · exact B1628135
  · exact B1628139
  · exact B1628143
  · exact B1628147
  · exact B1628151
  · exact B1628155
  · exact B1628159
  · exact B1628163
  · exact B1628167
  · exact B1628171
  · exact B1628175
  · exact B1628179
  · exact B1628183
  · exact B1628187
  · exact B1628191
  · exact B1628195
  · exact B1628199
  · exact B1628203
  · exact B1628207
  · exact B1628211
  · exact B1628215
  · exact B1628219
  · exact B1628223
  · exact B1628227
  · exact B1628231
  · exact B1628235
  · exact B1628239
  · exact B1628243
  · exact B1628247
  · exact B1628251
  · exact B1628255
  · exact B1628259
  · exact B1628263
  · exact B1628267
  · exact B1628271
  · exact B1628275
  · exact B1628279
  · exact B1628283
  · exact B1628287
  · exact B1628291
  · exact B1628295
  · exact B1628299
  · exact B1628303
  · exact B1628307
  · exact B1628311
  · exact B1628315
  · exact B1628319
  · exact B1628323
  · exact B1628327
  · exact B1628331
  · exact B1628335
  · exact B1628339
  · exact B1628343
  · exact B1628347
  · exact B1628351
  · exact B1628355
  · exact B1628359
  · exact B1628363
  · exact B1628367
  · exact B1628371
  · exact B1628375
  · exact B1628379
  · exact B1628383
  · exact B1628387
  · exact B1628391
  · exact B1628395
  · exact B1628399
  · exact B1628403
  · exact B1628407
  · exact B1628411
  · exact B1628415
  · exact B1628419
  · exact B1628423
  · exact B1628427
  · exact B1628431
  · exact B1628435
  · exact B1628439
  · exact B1628443
  · exact B1628447
  · exact B1628451
  · exact B1628455
  · exact B1628459
  · exact B1628463
  · exact B1628467
  · exact B1628471
  · exact B1628475
  · exact B1628479
  · exact B1628483
  · exact B1628487
  · exact B1628491
  · exact B1628495
  · exact B1628499
  · exact B1628503
  · exact B1628507
  · exact B1628511

theorem solution (m : ℕ) (hlo : 1626512 ≤ m) (hhi : m ≤ 1628512) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 406628 ≤ j := by omega
    have hj2 : j ≤ 407127 := by omega
    have hb : Blo 1626512 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
