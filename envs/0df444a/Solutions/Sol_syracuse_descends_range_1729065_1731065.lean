-- Prove2me | solution 1 for syracuse_descends_range_1729065_1731065
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:31:37.598576+00:00
-- url     : https://prove2.me/submissions/018057b1-7ce2-4c9a-ae8b-1abaa4384f15

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


theorem B3891221 : Blo 1729065 3891221 := bbase (se 6 (by rfl) ⟨91200, by rfl⟩ : syracuseStep 3891221 = 182401) (by norm_num)
theorem B3891293 : Blo 1729065 3891293 := bbase (se 3 (by rfl) ⟨729617, by rfl⟩ : syracuseStep 3891293 = 1459235) (by norm_num)
theorem B7487653 : Blo 1729065 7487653 := bbase (se 4 (by rfl) ⟨701967, by rfl⟩ : syracuseStep 7487653 = 1403935) (by norm_num)
theorem B3891365 : Blo 1729065 3891365 := bbase (se 4 (by rfl) ⟨364815, by rfl⟩ : syracuseStep 3891365 = 729631) (by norm_num)
theorem B2220257 : Blo 1729065 2220257 := bbase (se 2 (by rfl) ⟨832596, by rfl⟩ : syracuseStep 2220257 = 1665193) (by norm_num)
theorem B5841125 : Blo 1729065 5841125 := bbase (se 4 (by rfl) ⟨547605, by rfl⟩ : syracuseStep 5841125 = 1095211) (by norm_num)
theorem B3891437 : Blo 1729065 3891437 := bbase (se 3 (by rfl) ⟨729644, by rfl⟩ : syracuseStep 3891437 = 1459289) (by norm_num)
theorem B3285269 : Blo 1729065 3285269 := bbase (se 6 (by rfl) ⟨76998, by rfl⟩ : syracuseStep 3285269 = 153997) (by norm_num)
theorem B8544533 : Blo 1729065 8544533 := bbase (se 6 (by rfl) ⟨200262, by rfl⟩ : syracuseStep 8544533 = 400525) (by norm_num)
theorem B3891509 : Blo 1729065 3891509 := bbase (se 5 (by rfl) ⟨182414, by rfl⟩ : syracuseStep 3891509 = 364829) (by norm_num)
theorem B7012661 : Blo 1729065 7012661 := bbase (se 5 (by rfl) ⟨328718, by rfl⟩ : syracuseStep 7012661 = 657437) (by norm_num)
theorem B8757557 : Blo 1729065 8757557 := bbase (se 5 (by rfl) ⟨410510, by rfl⟩ : syracuseStep 8757557 = 821021) (by norm_num)
theorem B1753421 : Blo 1729065 1753421 := bbase (se 3 (by rfl) ⟨328766, by rfl⟩ : syracuseStep 1753421 = 657533) (by norm_num)
theorem B18702677 : Blo 1729065 18702677 := bbase (se 10 (by rfl) ⟨27396, by rfl⟩ : syracuseStep 18702677 = 54793) (by norm_num)
theorem B6570341 : Blo 1729065 6570341 := bbase (se 4 (by rfl) ⟨615969, by rfl⟩ : syracuseStep 6570341 = 1231939) (by norm_num)
theorem B3891581 : Blo 1729065 3891581 := bbase (se 3 (by rfl) ⟨729671, by rfl⟩ : syracuseStep 3891581 = 1459343) (by norm_num)
theorem B3694997 : Blo 1729065 3694997 := bbase (se 6 (by rfl) ⟨86601, by rfl⟩ : syracuseStep 3694997 = 173203) (by norm_num)
theorem B3695005 : Blo 1729065 3695005 := bbase (se 3 (by rfl) ⟨692813, by rfl⟩ : syracuseStep 3695005 = 1385627) (by norm_num)
theorem B3891653 : Blo 1729065 3891653 := bbase (se 4 (by rfl) ⟨364842, by rfl⟩ : syracuseStep 3891653 = 729685) (by norm_num)
theorem B3891725 : Blo 1729065 3891725 := bbase (se 3 (by rfl) ⟨729698, by rfl⟩ : syracuseStep 3891725 = 1459397) (by norm_num)
theorem B3891797 : Blo 1729065 3891797 := bbase (se 8 (by rfl) ⟨22803, by rfl⟩ : syracuseStep 3891797 = 45607) (by norm_num)
theorem B6570629 : Blo 1729065 6570629 := bbase (se 4 (by rfl) ⟨615996, by rfl⟩ : syracuseStep 6570629 = 1231993) (by norm_num)
theorem B9355925 : Blo 1729065 9355925 := bbase (se 6 (by rfl) ⟨219279, by rfl⟩ : syracuseStep 9355925 = 438559) (by norm_num)
theorem B5841557 : Blo 1729065 5841557 := bbase (se 6 (by rfl) ⟨136911, by rfl⟩ : syracuseStep 5841557 = 273823) (by norm_num)
theorem B12477077 : Blo 1729065 12477077 := bbase (se 6 (by rfl) ⟨292431, by rfl⟩ : syracuseStep 12477077 = 584863) (by norm_num)
theorem B3891869 : Blo 1729065 3891869 := bbase (se 3 (by rfl) ⟨729725, by rfl⟩ : syracuseStep 3891869 = 1459451) (by norm_num)
theorem B4440781 : Blo 1729065 4440781 := bbase (se 3 (by rfl) ⟨832646, by rfl⟩ : syracuseStep 4440781 = 1665293) (by norm_num)
theorem B3891941 : Blo 1729065 3891941 := bbase (se 4 (by rfl) ⟨364869, by rfl⟩ : syracuseStep 3891941 = 729739) (by norm_num)
theorem B4440845 : Blo 1729065 4440845 := bbase (se 3 (by rfl) ⟨832658, by rfl⟩ : syracuseStep 4440845 = 1665317) (by norm_num)
theorem B3892013 : Blo 1729065 3892013 := bbase (se 3 (by rfl) ⟨729752, by rfl⟩ : syracuseStep 3892013 = 1459505) (by norm_num)
theorem B3892085 : Blo 1729065 3892085 := bbase (se 5 (by rfl) ⟨182441, by rfl⟩ : syracuseStep 3892085 = 364883) (by norm_num)
theorem B3892157 : Blo 1729065 3892157 := bbase (se 3 (by rfl) ⟨729779, by rfl⟩ : syracuseStep 3892157 = 1459559) (by norm_num)
theorem B9855989 : Blo 1729065 9855989 := bbase (se 5 (by rfl) ⟨461999, by rfl⟩ : syracuseStep 9855989 = 923999) (by norm_num)
theorem B3892229 : Blo 1729065 3892229 := bbase (se 4 (by rfl) ⟨364896, by rfl⟩ : syracuseStep 3892229 = 729793) (by norm_num)
theorem B3286021 : Blo 1729065 3286021 := bbase (se 4 (by rfl) ⟨308064, by rfl⟩ : syracuseStep 3286021 = 616129) (by norm_num)
theorem B5841989 : Blo 1729065 5841989 := bbase (se 4 (by rfl) ⟨547686, by rfl⟩ : syracuseStep 5841989 = 1095373) (by norm_num)
theorem B3892301 : Blo 1729065 3892301 := bbase (se 3 (by rfl) ⟨729806, by rfl⟩ : syracuseStep 3892301 = 1459613) (by norm_num)
theorem B5260373 : Blo 1729065 5260373 := bbase (se 8 (by rfl) ⟨30822, by rfl⟩ : syracuseStep 5260373 = 61645) (by norm_num)
theorem B2188397 : Blo 1729065 2188397 := bbase (se 3 (by rfl) ⟨410324, by rfl⟩ : syracuseStep 2188397 = 820649) (by norm_num)
theorem B9847925 : Blo 1729065 9847925 := bbase (se 5 (by rfl) ⟨461621, by rfl⟩ : syracuseStep 9847925 = 923243) (by norm_num)
theorem B1754245 : Blo 1729065 1754245 := bbase (se 4 (by rfl) ⟨164460, by rfl⟩ : syracuseStep 1754245 = 328921) (by norm_num)
theorem B3892373 : Blo 1729065 3892373 := bbase (se 6 (by rfl) ⟨91227, by rfl⟩ : syracuseStep 3892373 = 182455) (by norm_num)
theorem B8316053 : Blo 1729065 8316053 := bbase (se 6 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 8316053 = 389815) (by norm_num)
theorem B3286165 : Blo 1729065 3286165 := bbase (se 6 (by rfl) ⟨77019, by rfl⟩ : syracuseStep 3286165 = 154039) (by norm_num)
theorem B2188453 : Blo 1729065 2188453 := bbase (se 4 (by rfl) ⟨205167, by rfl⟩ : syracuseStep 2188453 = 410335) (by norm_num)
theorem B3892445 : Blo 1729065 3892445 := bbase (se 3 (by rfl) ⟨729833, by rfl⟩ : syracuseStep 3892445 = 1459667) (by norm_num)
theorem B2188549 : Blo 1729065 2188549 := bbase (se 4 (by rfl) ⟨205176, by rfl⟩ : syracuseStep 2188549 = 410353) (by norm_num)
theorem B3892517 : Blo 1729065 3892517 := bbase (se 4 (by rfl) ⟨364923, by rfl⟩ : syracuseStep 3892517 = 729847) (by norm_num)
theorem B2770229 : Blo 1729065 2770229 := bbase (se 5 (by rfl) ⟨129854, by rfl⟩ : syracuseStep 2770229 = 259709) (by norm_num)
theorem B3892589 : Blo 1729065 3892589 := bbase (se 3 (by rfl) ⟨729860, by rfl⟩ : syracuseStep 3892589 = 1459721) (by norm_num)
theorem B4441477 : Blo 1729065 4441477 := bbase (se 4 (by rfl) ⟨416388, by rfl⟩ : syracuseStep 4441477 = 832777) (by norm_num)
theorem B6235541 : Blo 1729065 6235541 := bbase (se 6 (by rfl) ⟨146145, by rfl⟩ : syracuseStep 6235541 = 292291) (by norm_num)
theorem B2188721 : Blo 1729065 2188721 := bbase (se 2 (by rfl) ⟨820770, by rfl⟩ : syracuseStep 2188721 = 1641541) (by norm_num)
theorem B2770357 : Blo 1729065 2770357 := bbase (se 5 (by rfl) ⟨129860, by rfl⟩ : syracuseStep 2770357 = 259721) (by norm_num)
theorem B3892661 : Blo 1729065 3892661 := bbase (se 5 (by rfl) ⟨182468, by rfl⟩ : syracuseStep 3892661 = 364937) (by norm_num)
theorem B2917829 : Blo 1729065 2917829 := bbase (se 4 (by rfl) ⟨273546, by rfl⟩ : syracuseStep 2917829 = 547093) (by norm_num)
theorem B7390693 : Blo 1729065 7390693 := bbase (se 4 (by rfl) ⟨692877, by rfl⟩ : syracuseStep 7390693 = 1385755) (by norm_num)
theorem B2188777 : Blo 1729065 2188777 := bbase (se 2 (by rfl) ⟨820791, by rfl⟩ : syracuseStep 2188777 = 1641583) (by norm_num)
theorem B3892733 : Blo 1729065 3892733 := bbase (se 3 (by rfl) ⟨729887, by rfl⟩ : syracuseStep 3892733 = 1459775) (by norm_num)
theorem B3696133 : Blo 1729065 3696133 := bbase (se 4 (by rfl) ⟨346512, by rfl⟩ : syracuseStep 3696133 = 693025) (by norm_num)
theorem B2917957 : Blo 1729065 2917957 := bbase (se 4 (by rfl) ⟨273558, by rfl⟩ : syracuseStep 2917957 = 547117) (by norm_num)
theorem B3892805 : Blo 1729065 3892805 := bbase (se 4 (by rfl) ⟨364950, by rfl⟩ : syracuseStep 3892805 = 729901) (by norm_num)
theorem B2188873 : Blo 1729065 2188873 := bbase (se 2 (by rfl) ⟨820827, by rfl⟩ : syracuseStep 2188873 = 1641655) (by norm_num)
theorem B8758853 : Blo 1729065 8758853 := bbase (se 4 (by rfl) ⟨821142, by rfl⟩ : syracuseStep 8758853 = 1642285) (by norm_num)
theorem B3892877 : Blo 1729065 3892877 := bbase (se 3 (by rfl) ⟨729914, by rfl⟩ : syracuseStep 3892877 = 1459829) (by norm_num)
theorem B2918045 : Blo 1729065 2918045 := bbase (se 3 (by rfl) ⟨547133, by rfl⟩ : syracuseStep 2918045 = 1094267) (by norm_num)
theorem B3892949 : Blo 1729065 3892949 := bbase (se 7 (by rfl) ⟨45620, by rfl⟩ : syracuseStep 3892949 = 91241) (by norm_num)
theorem B2631397 : Blo 1729065 2631397 := bbase (se 4 (by rfl) ⟨246693, by rfl⟩ : syracuseStep 2631397 = 493387) (by norm_num)
theorem B2189045 : Blo 1729065 2189045 := bbase (se 5 (by rfl) ⟨102611, by rfl⟩ : syracuseStep 2189045 = 205223) (by norm_num)
theorem B4155133 : Blo 1729065 4155133 := bbase (se 3 (by rfl) ⟨779087, by rfl⟩ : syracuseStep 4155133 = 1558175) (by norm_num)
theorem B2918173 : Blo 1729065 2918173 := bbase (se 3 (by rfl) ⟨547157, by rfl⟩ : syracuseStep 2918173 = 1094315) (by norm_num)
theorem B3893021 : Blo 1729065 3893021 := bbase (se 3 (by rfl) ⟨729941, by rfl⟩ : syracuseStep 3893021 = 1459883) (by norm_num)
theorem B6571813 : Blo 1729065 6571813 := bbase (se 4 (by rfl) ⟨616107, by rfl⟩ : syracuseStep 6571813 = 1232215) (by norm_num)
theorem B2189101 : Blo 1729065 2189101 := bbase (se 3 (by rfl) ⟨410456, by rfl⟩ : syracuseStep 2189101 = 820913) (by norm_num)
theorem B5539637 : Blo 1729065 5539637 := bbase (se 5 (by rfl) ⟨259670, by rfl⟩ : syracuseStep 5539637 = 519341) (by norm_num)
theorem B6235957 : Blo 1729065 6235957 := bbase (se 5 (by rfl) ⟨292310, by rfl⟩ : syracuseStep 6235957 = 584621) (by norm_num)
theorem B3893093 : Blo 1729065 3893093 := bbase (se 4 (by rfl) ⟨364977, by rfl⟩ : syracuseStep 3893093 = 729955) (by norm_num)
theorem B2918261 : Blo 1729065 2918261 := bbase (se 5 (by rfl) ⟨136793, by rfl⟩ : syracuseStep 2918261 = 273587) (by norm_num)
theorem B3696509 : Blo 1729065 3696509 := bbase (se 3 (by rfl) ⟨693095, by rfl⟩ : syracuseStep 3696509 = 1386191) (by norm_num)
theorem B2189197 : Blo 1729065 2189197 := bbase (se 3 (by rfl) ⟨410474, by rfl⟩ : syracuseStep 2189197 = 820949) (by norm_num)
theorem B3893165 : Blo 1729065 3893165 := bbase (se 3 (by rfl) ⟨729968, by rfl⟩ : syracuseStep 3893165 = 1459937) (by norm_num)
theorem B2918389 : Blo 1729065 2918389 := bbase (se 5 (by rfl) ⟨136799, by rfl⟩ : syracuseStep 2918389 = 273599) (by norm_num)
theorem B3893237 : Blo 1729065 3893237 := bbase (se 5 (by rfl) ⟨182495, by rfl⟩ : syracuseStep 3893237 = 364991) (by norm_num)
theorem B2189369 : Blo 1729065 2189369 := bbase (se 2 (by rfl) ⟨821013, by rfl⟩ : syracuseStep 2189369 = 1642027) (by norm_num)
theorem B3893309 : Blo 1729065 3893309 := bbase (se 3 (by rfl) ⟨729995, by rfl⟩ : syracuseStep 3893309 = 1459991) (by norm_num)
theorem B2918477 : Blo 1729065 2918477 := bbase (se 3 (by rfl) ⟨547214, by rfl⟩ : syracuseStep 2918477 = 1094429) (by norm_num)
theorem B6572117 : Blo 1729065 6572117 := bbase (se 8 (by rfl) ⟨38508, by rfl⟩ : syracuseStep 6572117 = 77017) (by norm_num)
theorem B2189425 : Blo 1729065 2189425 := bbase (se 2 (by rfl) ⟨821034, by rfl⟩ : syracuseStep 2189425 = 1642069) (by norm_num)
theorem B3893381 : Blo 1729065 3893381 := bbase (se 4 (by rfl) ⟨365004, by rfl⟩ : syracuseStep 3893381 = 730009) (by norm_num)
theorem B9857173 : Blo 1729065 9857173 := bbase (se 6 (by rfl) ⟨231027, by rfl⟩ : syracuseStep 9857173 = 462055) (by norm_num)
theorem B2918605 : Blo 1729065 2918605 := bbase (se 3 (by rfl) ⟨547238, by rfl⟩ : syracuseStep 2918605 = 1094477) (by norm_num)
theorem B3893453 : Blo 1729065 3893453 := bbase (se 3 (by rfl) ⟨730022, by rfl⟩ : syracuseStep 3893453 = 1460045) (by norm_num)
theorem B2189521 : Blo 1729065 2189521 := bbase (se 2 (by rfl) ⟨821070, by rfl⟩ : syracuseStep 2189521 = 1642141) (by norm_num)
theorem B2771165 : Blo 1729065 2771165 := bbase (se 3 (by rfl) ⟨519593, by rfl⟩ : syracuseStep 2771165 = 1039187) (by norm_num)
theorem B5335301 : Blo 1729065 5335301 := bbase (se 4 (by rfl) ⟨500184, by rfl⟩ : syracuseStep 5335301 = 1000369) (by norm_num)
theorem B4925717 : Blo 1729065 4925717 := bbase (se 6 (by rfl) ⟨115446, by rfl⟩ : syracuseStep 4925717 = 230893) (by norm_num)
theorem B3893525 : Blo 1729065 3893525 := bbase (se 6 (by rfl) ⟨91254, by rfl⟩ : syracuseStep 3893525 = 182509) (by norm_num)
theorem B2918693 : Blo 1729065 2918693 := bbase (se 4 (by rfl) ⟨273627, by rfl⟩ : syracuseStep 2918693 = 547255) (by norm_num)
theorem B3893597 : Blo 1729065 3893597 := bbase (se 3 (by rfl) ⟨730049, by rfl⟩ : syracuseStep 3893597 = 1460099) (by norm_num)
theorem B4155749 : Blo 1729065 4155749 := bbase (se 4 (by rfl) ⟨389601, by rfl⟩ : syracuseStep 4155749 = 779203) (by norm_num)
theorem B2189693 : Blo 1729065 2189693 := bbase (se 3 (by rfl) ⟨410567, by rfl⟩ : syracuseStep 2189693 = 821135) (by norm_num)
theorem B6752645 : Blo 1729065 6752645 := bbase (se 4 (by rfl) ⟨633060, by rfl⟩ : syracuseStep 6752645 = 1266121) (by norm_num)
theorem B2918821 : Blo 1729065 2918821 := bbase (se 4 (by rfl) ⟨273639, by rfl⟩ : syracuseStep 2918821 = 547279) (by norm_num)
theorem B3893669 : Blo 1729065 3893669 := bbase (se 4 (by rfl) ⟨365031, by rfl⟩ : syracuseStep 3893669 = 730063) (by norm_num)
theorem B2189749 : Blo 1729065 2189749 := bbase (se 5 (by rfl) ⟨102644, by rfl⟩ : syracuseStep 2189749 = 205289) (by norm_num)
theorem B4377037 : Blo 1729065 4377037 := bbase (se 3 (by rfl) ⟨820694, by rfl⟩ : syracuseStep 4377037 = 1641389) (by norm_num)
theorem B3893741 : Blo 1729065 3893741 := bbase (se 3 (by rfl) ⟨730076, by rfl⟩ : syracuseStep 3893741 = 1460153) (by norm_num)
theorem B2918909 : Blo 1729065 2918909 := bbase (se 3 (by rfl) ⟨547295, by rfl⟩ : syracuseStep 2918909 = 1094591) (by norm_num)
theorem B2771453 : Blo 1729065 2771453 := bbase (se 3 (by rfl) ⟨519647, by rfl⟩ : syracuseStep 2771453 = 1039295) (by norm_num)
theorem B2189845 : Blo 1729065 2189845 := bbase (se 6 (by rfl) ⟨51324, by rfl⟩ : syracuseStep 2189845 = 102649) (by norm_num)
theorem B2107949 : Blo 1729065 2107949 := bbase (se 3 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 2107949 = 790481) (by norm_num)
theorem B3893813 : Blo 1729065 3893813 := bbase (se 5 (by rfl) ⟨182522, by rfl⟩ : syracuseStep 3893813 = 365045) (by norm_num)
theorem B4377149 : Blo 1729065 4377149 := bbase (se 3 (by rfl) ⟨820715, by rfl⟩ : syracuseStep 4377149 = 1641431) (by norm_num)
theorem B63113813 : Blo 1729065 63113813 := bbase (se 8 (by rfl) ⟨369807, by rfl⟩ : syracuseStep 63113813 = 739615) (by norm_num)
theorem B2919037 : Blo 1729065 2919037 := bbase (se 3 (by rfl) ⟨547319, by rfl⟩ : syracuseStep 2919037 = 1094639) (by norm_num)
theorem B3893885 : Blo 1729065 3893885 := bbase (se 3 (by rfl) ⟨730103, by rfl⟩ : syracuseStep 3893885 = 1460207) (by norm_num)
theorem B3508861 : Blo 1729065 3508861 := bbase (se 3 (by rfl) ⟨657911, by rfl⟩ : syracuseStep 3508861 = 1315823) (by norm_num)
theorem B2190017 : Blo 1729065 2190017 := bbase (se 2 (by rfl) ⟨821256, by rfl⟩ : syracuseStep 2190017 = 1642513) (by norm_num)
theorem B3893957 : Blo 1729065 3893957 := bbase (se 4 (by rfl) ⟨365058, by rfl⟩ : syracuseStep 3893957 = 730117) (by norm_num)
theorem B2919125 : Blo 1729065 2919125 := bbase (se 7 (by rfl) ⟨34208, by rfl⟩ : syracuseStep 2919125 = 68417) (by norm_num)
theorem B2190073 : Blo 1729065 2190073 := bbase (se 2 (by rfl) ⟨821277, by rfl⟩ : syracuseStep 2190073 = 1642555) (by norm_num)
theorem B4377341 : Blo 1729065 4377341 := bbase (se 3 (by rfl) ⟨820751, by rfl⟩ : syracuseStep 4377341 = 1641503) (by norm_num)
theorem B3894029 : Blo 1729065 3894029 := bbase (se 3 (by rfl) ⟨730130, by rfl⟩ : syracuseStep 3894029 = 1460261) (by norm_num)
theorem B4156181 : Blo 1729065 4156181 := bbase (se 6 (by rfl) ⟨97410, by rfl⟩ : syracuseStep 4156181 = 194821) (by norm_num)
theorem B66489173 : Blo 1729065 66489173 := bbase (se 9 (by rfl) ⟨194792, by rfl⟩ : syracuseStep 66489173 = 389585) (by norm_num)
theorem B2919253 : Blo 1729065 2919253 := bbase (se 9 (by rfl) ⟨8552, by rfl⟩ : syracuseStep 2919253 = 17105) (by norm_num)
theorem B28060501 : Blo 1729065 28060501 := bbase (se 9 (by rfl) ⟨82208, by rfl⟩ : syracuseStep 28060501 = 164417) (by norm_num)
theorem B8760149 : Blo 1729065 8760149 := bbase (se 9 (by rfl) ⟨25664, by rfl⟩ : syracuseStep 8760149 = 51329) (by norm_num)
theorem B2190169 : Blo 1729065 2190169 := bbase (se 2 (by rfl) ⟨821313, by rfl⟩ : syracuseStep 2190169 = 1642627) (by norm_num)
theorem B3894101 : Blo 1729065 3894101 := bbase (se 9 (by rfl) ⟨11408, by rfl⟩ : syracuseStep 3894101 = 22817) (by norm_num)
theorem B3115925 : Blo 1729065 3115925 := bbase (se 6 (by rfl) ⟨73029, by rfl⟩ : syracuseStep 3115925 = 146059) (by norm_num)
theorem B4271005 : Blo 1729065 4271005 := bbase (se 3 (by rfl) ⟨800813, by rfl⟩ : syracuseStep 4271005 = 1601627) (by norm_num)
theorem B2771869 : Blo 1729065 2771869 := bbase (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) (by norm_num)
theorem B3894173 : Blo 1729065 3894173 := bbase (se 3 (by rfl) ⟨730157, by rfl⟩ : syracuseStep 3894173 = 1460315) (by norm_num)
theorem B2919341 : Blo 1729065 2919341 := bbase (se 3 (by rfl) ⟨547376, by rfl⟩ : syracuseStep 2919341 = 1094753) (by norm_num)
theorem B12643253 : Blo 1729065 12643253 := bbase (se 5 (by rfl) ⟨592652, by rfl⟩ : syracuseStep 12643253 = 1185305) (by norm_num)
theorem B7392181 : Blo 1729065 7392181 := bbase (se 5 (by rfl) ⟨346508, by rfl⟩ : syracuseStep 7392181 = 693017) (by norm_num)
theorem B7392197 : Blo 1729065 7392197 := bbase (se 4 (by rfl) ⟨693018, by rfl⟩ : syracuseStep 7392197 = 1386037) (by norm_num)
theorem B3894245 : Blo 1729065 3894245 := bbase (se 4 (by rfl) ⟨365085, by rfl⟩ : syracuseStep 3894245 = 730171) (by norm_num)
theorem B2190341 : Blo 1729065 2190341 := bbase (se 4 (by rfl) ⟨205344, by rfl⟩ : syracuseStep 2190341 = 410689) (by norm_num)
theorem B2919469 : Blo 1729065 2919469 := bbase (se 3 (by rfl) ⟨547400, by rfl⟩ : syracuseStep 2919469 = 1094801) (by norm_num)
theorem B3894317 : Blo 1729065 3894317 := bbase (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) (by norm_num)
theorem B2960437 : Blo 1729065 2960437 := bbase (se 5 (by rfl) ⟨138770, by rfl⟩ : syracuseStep 2960437 = 277541) (by norm_num)
theorem B2190397 : Blo 1729065 2190397 := bbase (se 3 (by rfl) ⟨410699, by rfl⟩ : syracuseStep 2190397 = 821399) (by norm_num)
theorem B4377685 : Blo 1729065 4377685 := bbase (se 8 (by rfl) ⟨25650, by rfl⟩ : syracuseStep 4377685 = 51301) (by norm_num)
theorem B9989237 : Blo 1729065 9989237 := bbase (se 5 (by rfl) ⟨468245, by rfl⟩ : syracuseStep 9989237 = 936491) (by norm_num)
theorem B3894389 : Blo 1729065 3894389 := bbase (se 5 (by rfl) ⟨182549, by rfl⟩ : syracuseStep 3894389 = 365099) (by norm_num)
theorem B2919557 : Blo 1729065 2919557 := bbase (se 4 (by rfl) ⟨273708, by rfl⟩ : syracuseStep 2919557 = 547417) (by norm_num)
theorem B18713749 : Blo 1729065 18713749 := bbase (se 6 (by rfl) ⟨438603, by rfl⟩ : syracuseStep 18713749 = 877207) (by norm_num)
theorem B2190493 : Blo 1729065 2190493 := bbase (se 3 (by rfl) ⟨410717, by rfl⟩ : syracuseStep 2190493 = 821435) (by norm_num)
theorem B5835941 : Blo 1729065 5835941 := bbase (se 4 (by rfl) ⟨547119, by rfl⟩ : syracuseStep 5835941 = 1094239) (by norm_num)
theorem B3894461 : Blo 1729065 3894461 := bbase (se 3 (by rfl) ⟨730211, by rfl⟩ : syracuseStep 3894461 = 1460423) (by norm_num)
theorem B4377797 : Blo 1729065 4377797 := bbase (se 4 (by rfl) ⟨410418, by rfl⟩ : syracuseStep 4377797 = 820837) (by norm_num)
theorem B5541061 : Blo 1729065 5541061 := bbase (se 4 (by rfl) ⟨519474, by rfl⟩ : syracuseStep 5541061 = 1038949) (by norm_num)
theorem B2919685 : Blo 1729065 2919685 := bbase (se 4 (by rfl) ⟨273720, by rfl⟩ : syracuseStep 2919685 = 547441) (by norm_num)
theorem B3894533 : Blo 1729065 3894533 := bbase (se 4 (by rfl) ⟨365112, by rfl⟩ : syracuseStep 3894533 = 730225) (by norm_num)
theorem B8310053 : Blo 1729065 8310053 := bbase (se 4 (by rfl) ⟨779067, by rfl⟩ : syracuseStep 8310053 = 1558135) (by norm_num)
theorem B2190665 : Blo 1729065 2190665 := bbase (se 2 (by rfl) ⟨821499, by rfl⟩ : syracuseStep 2190665 = 1642999) (by norm_num)
theorem B3894605 : Blo 1729065 3894605 := bbase (se 3 (by rfl) ⟨730238, by rfl⟩ : syracuseStep 3894605 = 1460477) (by norm_num)
theorem B2919773 : Blo 1729065 2919773 := bbase (se 3 (by rfl) ⟨547457, by rfl⟩ : syracuseStep 2919773 = 1094915) (by norm_num)
theorem B2190721 : Blo 1729065 2190721 := bbase (se 2 (by rfl) ⟨821520, by rfl⟩ : syracuseStep 2190721 = 1643041) (by norm_num)
theorem B4377989 : Blo 1729065 4377989 := bbase (se 4 (by rfl) ⟨410436, by rfl⟩ : syracuseStep 4377989 = 820873) (by norm_num)
theorem B6843797 : Blo 1729065 6843797 := bbase (se 6 (by rfl) ⟨160401, by rfl⟩ : syracuseStep 6843797 = 320803) (by norm_num)
theorem B3894677 : Blo 1729065 3894677 := bbase (se 6 (by rfl) ⟨91281, by rfl⟩ : syracuseStep 3894677 = 182563) (by norm_num)
theorem B4926901 : Blo 1729065 4926901 := bbase (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) (by norm_num)
theorem B23662037 : Blo 1729065 23662037 := bbase (se 7 (by rfl) ⟨277289, by rfl⟩ : syracuseStep 23662037 = 554579) (by norm_num)
theorem B2919901 : Blo 1729065 2919901 := bbase (se 3 (by rfl) ⟨547481, by rfl⟩ : syracuseStep 2919901 = 1094963) (by norm_num)
theorem B3894749 : Blo 1729065 3894749 := bbase (se 3 (by rfl) ⟨730265, by rfl⟩ : syracuseStep 3894749 = 1460531) (by norm_num)
theorem B2190817 : Blo 1729065 2190817 := bbase (se 2 (by rfl) ⟨821556, by rfl⟩ : syracuseStep 2190817 = 1643113) (by norm_num)
theorem B3894821 : Blo 1729065 3894821 := bbase (se 4 (by rfl) ⟨365139, by rfl⟩ : syracuseStep 3894821 = 730279) (by norm_num)
theorem B2919989 : Blo 1729065 2919989 := bbase (se 5 (by rfl) ⟨136874, by rfl⟩ : syracuseStep 2919989 = 273749) (by norm_num)
theorem B5836373 : Blo 1729065 5836373 := bbase (se 8 (by rfl) ⟨34197, by rfl⟩ : syracuseStep 5836373 = 68395) (by norm_num)
theorem B4927061 : Blo 1729065 4927061 := bbase (se 8 (by rfl) ⟨28869, by rfl⟩ : syracuseStep 4927061 = 57739) (by norm_num)
theorem B3894893 : Blo 1729065 3894893 := bbase (se 3 (by rfl) ⟨730292, by rfl⟩ : syracuseStep 3894893 = 1460585) (by norm_num)
theorem B1945201 : Blo 1729065 1945201 := bbase (se 2 (by rfl) ⟨729450, by rfl⟩ : syracuseStep 1945201 = 1458901) (by norm_num)
theorem B5541509 : Blo 1729065 5541509 := bbase (se 4 (by rfl) ⟨519516, by rfl⟩ : syracuseStep 5541509 = 1039033) (by norm_num)
theorem B1945237 : Blo 1729065 1945237 := bbase (se 6 (by rfl) ⟨45591, by rfl⟩ : syracuseStep 1945237 = 91183) (by norm_num)
theorem B2920117 : Blo 1729065 2920117 := bbase (se 5 (by rfl) ⟨136880, by rfl⟩ : syracuseStep 2920117 = 273761) (by norm_num)
theorem B1945273 : Blo 1729065 1945273 := bbase (se 2 (by rfl) ⟨729477, by rfl⟩ : syracuseStep 1945273 = 1458955) (by norm_num)
theorem B1846973 : Blo 1729065 1846973 := bbase (se 3 (by rfl) ⟨346307, by rfl⟩ : syracuseStep 1846973 = 692615) (by norm_num)
theorem B1945309 : Blo 1729065 1945309 := bbase (se 3 (by rfl) ⟨364745, by rfl⟩ : syracuseStep 1945309 = 729491) (by norm_num)
theorem B4378333 : Blo 1729065 4378333 := bbase (se 3 (by rfl) ⟨820937, by rfl⟩ : syracuseStep 4378333 = 1641875) (by norm_num)
theorem B7016165 : Blo 1729065 7016165 := bbase (se 4 (by rfl) ⟨657765, by rfl⟩ : syracuseStep 7016165 = 1315531) (by norm_num)
theorem B1945345 : Blo 1729065 1945345 := bbase (se 2 (by rfl) ⟨729504, by rfl⟩ : syracuseStep 1945345 = 1459009) (by norm_num)
theorem B2920205 : Blo 1729065 2920205 := bbase (se 3 (by rfl) ⟨547538, by rfl⟩ : syracuseStep 2920205 = 1095077) (by norm_num)
theorem B1945381 : Blo 1729065 1945381 := bbase (se 4 (by rfl) ⟨182379, by rfl⟩ : syracuseStep 1945381 = 364759) (by norm_num)
theorem B4927301 : Blo 1729065 4927301 := bbase (se 4 (by rfl) ⟨461934, by rfl⟩ : syracuseStep 4927301 = 923869) (by norm_num)
theorem B2772805 : Blo 1729065 2772805 := bbase (se 4 (by rfl) ⟨259950, by rfl⟩ : syracuseStep 2772805 = 519901) (by norm_num)
theorem B1945417 : Blo 1729065 1945417 := bbase (se 2 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 1945417 = 1459063) (by norm_num)
theorem B4378445 : Blo 1729065 4378445 := bbase (se 3 (by rfl) ⟨820958, by rfl⟩ : syracuseStep 4378445 = 1641917) (by norm_num)
theorem B1945453 : Blo 1729065 1945453 := bbase (se 3 (by rfl) ⟨364772, by rfl⟩ : syracuseStep 1945453 = 729545) (by norm_num)
theorem B1847161 : Blo 1729065 1847161 := bbase (se 2 (by rfl) ⟨692685, by rfl⟩ : syracuseStep 1847161 = 1385371) (by norm_num)
theorem B2920333 : Blo 1729065 2920333 := bbase (se 3 (by rfl) ⟨547562, by rfl⟩ : syracuseStep 2920333 = 1095125) (by norm_num)
theorem B1945489 : Blo 1729065 1945489 := bbase (se 2 (by rfl) ⟨729558, by rfl⟩ : syracuseStep 1945489 = 1459117) (by norm_num)
theorem B1945525 : Blo 1729065 1945525 := bbase (se 5 (by rfl) ⟨91196, by rfl⟩ : syracuseStep 1945525 = 182393) (by norm_num)
theorem B4157381 : Blo 1729065 4157381 := bbase (se 4 (by rfl) ⟨389754, by rfl⟩ : syracuseStep 4157381 = 779509) (by norm_num)
theorem B1945561 : Blo 1729065 1945561 := bbase (se 2 (by rfl) ⟨729585, by rfl⟩ : syracuseStep 1945561 = 1459171) (by norm_num)
theorem B2920421 : Blo 1729065 2920421 := bbase (se 4 (by rfl) ⟨273789, by rfl⟩ : syracuseStep 2920421 = 547579) (by norm_num)
theorem B1945597 : Blo 1729065 1945597 := bbase (se 3 (by rfl) ⟨364799, by rfl⟩ : syracuseStep 1945597 = 729599) (by norm_num)
theorem B5836805 : Blo 1729065 5836805 := bbase (se 4 (by rfl) ⟨547200, by rfl⟩ : syracuseStep 5836805 = 1094401) (by norm_num)
theorem B4927493 : Blo 1729065 4927493 := bbase (se 4 (by rfl) ⟨461952, by rfl⟩ : syracuseStep 4927493 = 923905) (by norm_num)
theorem B4378637 : Blo 1729065 4378637 := bbase (se 3 (by rfl) ⟨820994, by rfl⟩ : syracuseStep 4378637 = 1641989) (by norm_num)
theorem B3944477 : Blo 1729065 3944477 := bbase (se 3 (by rfl) ⟨739589, by rfl⟩ : syracuseStep 3944477 = 1479179) (by norm_num)
theorem B1945633 : Blo 1729065 1945633 := bbase (se 2 (by rfl) ⟨729612, by rfl⟩ : syracuseStep 1945633 = 1459225) (by norm_num)
theorem B1945669 : Blo 1729065 1945669 := bbase (se 4 (by rfl) ⟨182406, by rfl⟩ : syracuseStep 1945669 = 364813) (by norm_num)
theorem B8761445 : Blo 1729065 8761445 := bbase (se 4 (by rfl) ⟨821385, by rfl⟩ : syracuseStep 8761445 = 1642771) (by norm_num)
theorem B2920549 : Blo 1729065 2920549 := bbase (se 4 (by rfl) ⟨273801, by rfl⟩ : syracuseStep 2920549 = 547603) (by norm_num)
theorem B1945705 : Blo 1729065 1945705 := bbase (se 2 (by rfl) ⟨729639, by rfl⟩ : syracuseStep 1945705 = 1459279) (by norm_num)
theorem B1945741 : Blo 1729065 1945741 := bbase (se 3 (by rfl) ⟨364826, by rfl⟩ : syracuseStep 1945741 = 729653) (by norm_num)
theorem B1945777 : Blo 1729065 1945777 := bbase (se 2 (by rfl) ⟨729666, by rfl⟩ : syracuseStep 1945777 = 1459333) (by norm_num)
theorem B2920637 : Blo 1729065 2920637 := bbase (se 3 (by rfl) ⟨547619, by rfl⟩ : syracuseStep 2920637 = 1095239) (by norm_num)
theorem B1945813 : Blo 1729065 1945813 := bbase (se 7 (by rfl) ⟨22802, by rfl⟩ : syracuseStep 1945813 = 45605) (by norm_num)
theorem B5918933 : Blo 1729065 5918933 := bbase (se 7 (by rfl) ⟨69362, by rfl⟩ : syracuseStep 5918933 = 138725) (by norm_num)
theorem B1945849 : Blo 1729065 1945849 := bbase (se 2 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 1945849 = 1459387) (by norm_num)
theorem B1945885 : Blo 1729065 1945885 := bbase (se 3 (by rfl) ⟨364853, by rfl⟩ : syracuseStep 1945885 = 729707) (by norm_num)
theorem B2920765 : Blo 1729065 2920765 := bbase (se 3 (by rfl) ⟨547643, by rfl⟩ : syracuseStep 2920765 = 1095287) (by norm_num)
theorem B1945921 : Blo 1729065 1945921 := bbase (se 2 (by rfl) ⟨729720, by rfl⟩ : syracuseStep 1945921 = 1459441) (by norm_num)
theorem B1945957 : Blo 1729065 1945957 := bbase (se 4 (by rfl) ⟨182433, by rfl⟩ : syracuseStep 1945957 = 364867) (by norm_num)
theorem B4378981 : Blo 1729065 4378981 := bbase (se 4 (by rfl) ⟨410529, by rfl⟩ : syracuseStep 4378981 = 821059) (by norm_num)
theorem B1945993 : Blo 1729065 1945993 := bbase (se 2 (by rfl) ⟨729747, by rfl⟩ : syracuseStep 1945993 = 1459495) (by norm_num)
theorem B2920853 : Blo 1729065 2920853 := bbase (se 6 (by rfl) ⟨68457, by rfl⟩ : syracuseStep 2920853 = 136915) (by norm_num)
theorem B1946029 : Blo 1729065 1946029 := bbase (se 3 (by rfl) ⟨364880, by rfl⟩ : syracuseStep 1946029 = 729761) (by norm_num)
theorem B5837237 : Blo 1729065 5837237 := bbase (se 5 (by rfl) ⟨273620, by rfl⟩ : syracuseStep 5837237 = 547241) (by norm_num)
theorem B1946065 : Blo 1729065 1946065 := bbase (se 2 (by rfl) ⟨729774, by rfl⟩ : syracuseStep 1946065 = 1459549) (by norm_num)
theorem B4379093 : Blo 1729065 4379093 := bbase (se 7 (by rfl) ⟨51317, by rfl⟩ : syracuseStep 4379093 = 102635) (by norm_num)
theorem B1946101 : Blo 1729065 1946101 := bbase (se 5 (by rfl) ⟨91223, by rfl⟩ : syracuseStep 1946101 = 182447) (by norm_num)
theorem B8753669 : Blo 1729065 8753669 := bbase (se 4 (by rfl) ⟨820656, by rfl⟩ : syracuseStep 8753669 = 1641313) (by norm_num)
theorem B2920981 : Blo 1729065 2920981 := bbase (se 6 (by rfl) ⟨68460, by rfl⟩ : syracuseStep 2920981 = 136921) (by norm_num)
theorem B1946137 : Blo 1729065 1946137 := bbase (se 2 (by rfl) ⟨729801, by rfl⟩ : syracuseStep 1946137 = 1459603) (by norm_num)
theorem B6566453 : Blo 1729065 6566453 := bbase (se 5 (by rfl) ⟨307802, by rfl⟩ : syracuseStep 6566453 = 615605) (by norm_num)
theorem B1946173 : Blo 1729065 1946173 := bbase (se 3 (by rfl) ⟨364907, by rfl⟩ : syracuseStep 1946173 = 729815) (by norm_num)
theorem B1946209 : Blo 1729065 1946209 := bbase (se 2 (by rfl) ⟨729828, by rfl⟩ : syracuseStep 1946209 = 1459657) (by norm_num)
theorem B2921069 : Blo 1729065 2921069 := bbase (se 3 (by rfl) ⟨547700, by rfl⟩ : syracuseStep 2921069 = 1095401) (by norm_num)
theorem B16626293 : Blo 1729065 16626293 := bbase (se 5 (by rfl) ⟨779357, by rfl⟩ : syracuseStep 16626293 = 1558715) (by norm_num)
theorem B1946245 : Blo 1729065 1946245 := bbase (se 4 (by rfl) ⟨182460, by rfl⟩ : syracuseStep 1946245 = 364921) (by norm_num)
theorem B2462357 : Blo 1729065 2462357 := bbase (se 6 (by rfl) ⟨57711, by rfl⟩ : syracuseStep 2462357 = 115423) (by norm_num)
theorem B4379285 : Blo 1729065 4379285 := bbase (se 6 (by rfl) ⟨102639, by rfl⟩ : syracuseStep 4379285 = 205279) (by norm_num)
theorem B1946281 : Blo 1729065 1946281 := bbase (se 2 (by rfl) ⟨729855, by rfl⟩ : syracuseStep 1946281 = 1459711) (by norm_num)
theorem B3945133 : Blo 1729065 3945133 := bbase (se 3 (by rfl) ⟨739712, by rfl⟩ : syracuseStep 3945133 = 1479425) (by norm_num)
theorem B1847981 : Blo 1729065 1847981 := bbase (se 3 (by rfl) ⟨346496, by rfl⟩ : syracuseStep 1847981 = 692993) (by norm_num)
theorem B1946317 : Blo 1729065 1946317 := bbase (se 3 (by rfl) ⟨364934, by rfl⟩ : syracuseStep 1946317 = 729869) (by norm_num)
theorem B1872605 : Blo 1729065 1872605 := bbase (se 3 (by rfl) ⟨351113, by rfl⟩ : syracuseStep 1872605 = 702227) (by norm_num)
theorem B2462437 : Blo 1729065 2462437 := bbase (se 4 (by rfl) ⟨230853, by rfl⟩ : syracuseStep 2462437 = 461707) (by norm_num)
theorem B1946353 : Blo 1729065 1946353 := bbase (se 2 (by rfl) ⟨729882, by rfl⟩ : syracuseStep 1946353 = 1459765) (by norm_num)
theorem B1946389 : Blo 1729065 1946389 := bbase (se 6 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 1946389 = 91237) (by norm_num)
theorem B9351989 : Blo 1729065 9351989 := bbase (se 5 (by rfl) ⟨438374, by rfl⟩ : syracuseStep 9351989 = 876749) (by norm_num)
theorem B1946425 : Blo 1729065 1946425 := bbase (se 2 (by rfl) ⟨729909, by rfl⟩ : syracuseStep 1946425 = 1459819) (by norm_num)
theorem B4436797 : Blo 1729065 4436797 := bbase (se 3 (by rfl) ⟨831899, by rfl⟩ : syracuseStep 4436797 = 1663799) (by norm_num)
theorem B2593613 : Blo 1729065 2593613 := bbase (se 3 (by rfl) ⟨486302, by rfl⟩ : syracuseStep 2593613 = 972605) (by norm_num)
theorem B6566741 : Blo 1729065 6566741 := bbase (se 9 (by rfl) ⟨19238, by rfl⟩ : syracuseStep 6566741 = 38477) (by norm_num)
theorem B2462557 : Blo 1729065 2462557 := bbase (se 3 (by rfl) ⟨461729, by rfl⟩ : syracuseStep 2462557 = 923459) (by norm_num)
theorem B1946461 : Blo 1729065 1946461 := bbase (se 3 (by rfl) ⟨364961, by rfl⟩ : syracuseStep 1946461 = 729923) (by norm_num)
theorem B2593637 : Blo 1729065 2593637 := bbase (se 4 (by rfl) ⟨243153, by rfl⟩ : syracuseStep 2593637 = 486307) (by norm_num)
theorem B5837669 : Blo 1729065 5837669 := bbase (se 4 (by rfl) ⟨547281, by rfl⟩ : syracuseStep 5837669 = 1094563) (by norm_num)
theorem B2593661 : Blo 1729065 2593661 := bbase (se 3 (by rfl) ⟨486311, by rfl⟩ : syracuseStep 2593661 = 972623) (by norm_num)
theorem B1946497 : Blo 1729065 1946497 := bbase (se 2 (by rfl) ⟨729936, by rfl⟩ : syracuseStep 1946497 = 1459873) (by norm_num)
theorem B2593685 : Blo 1729065 2593685 := bbase (se 6 (by rfl) ⟨60789, by rfl⟩ : syracuseStep 2593685 = 121579) (by norm_num)
theorem B1946533 : Blo 1729065 1946533 := bbase (se 4 (by rfl) ⟨182487, by rfl⟩ : syracuseStep 1946533 = 364975) (by norm_num)
theorem B2593709 : Blo 1729065 2593709 := bbase (se 3 (by rfl) ⟨486320, by rfl⟩ : syracuseStep 2593709 = 972641) (by norm_num)
theorem B2462653 : Blo 1729065 2462653 := bbase (se 3 (by rfl) ⟨461747, by rfl⟩ : syracuseStep 2462653 = 923495) (by norm_num)
theorem B2077633 : Blo 1729065 2077633 := bbase (se 2 (by rfl) ⟨779112, by rfl⟩ : syracuseStep 2077633 = 1558225) (by norm_num)
theorem B2593733 : Blo 1729065 2593733 := bbase (se 4 (by rfl) ⟨243162, by rfl⟩ : syracuseStep 2593733 = 486325) (by norm_num)
theorem B1946569 : Blo 1729065 1946569 := bbase (se 2 (by rfl) ⟨729963, by rfl⟩ : syracuseStep 1946569 = 1459927) (by norm_num)
theorem B23663573 : Blo 1729065 23663573 := bbase (se 7 (by rfl) ⟨277307, by rfl⟩ : syracuseStep 23663573 = 554615) (by norm_num)
theorem B2593757 : Blo 1729065 2593757 := bbase (se 3 (by rfl) ⟨486329, by rfl⟩ : syracuseStep 2593757 = 972659) (by norm_num)
theorem B4928485 : Blo 1729065 4928485 := bbase (se 4 (by rfl) ⟨462045, by rfl⟩ : syracuseStep 4928485 = 924091) (by norm_num)
theorem B4379629 : Blo 1729065 4379629 := bbase (se 3 (by rfl) ⟨821180, by rfl⟩ : syracuseStep 4379629 = 1642361) (by norm_num)
theorem B1946605 : Blo 1729065 1946605 := bbase (se 3 (by rfl) ⟨364988, by rfl⟩ : syracuseStep 1946605 = 729977) (by norm_num)
theorem B2593781 : Blo 1729065 2593781 := bbase (se 5 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 2593781 = 243167) (by norm_num)
theorem B2593805 : Blo 1729065 2593805 := bbase (se 3 (by rfl) ⟨486338, by rfl⟩ : syracuseStep 2593805 = 972677) (by norm_num)
theorem B1946641 : Blo 1729065 1946641 := bbase (se 2 (by rfl) ⟨729990, by rfl⟩ : syracuseStep 1946641 = 1459981) (by norm_num)
theorem B4674581 : Blo 1729065 4674581 := bbase (se 6 (by rfl) ⟨109560, by rfl⟩ : syracuseStep 4674581 = 219121) (by norm_num)
theorem B2593829 : Blo 1729065 2593829 := bbase (se 4 (by rfl) ⟨243171, by rfl⟩ : syracuseStep 2593829 = 486343) (by norm_num)
theorem B1946677 : Blo 1729065 1946677 := bbase (se 5 (by rfl) ⟨91250, by rfl⟩ : syracuseStep 1946677 = 182501) (by norm_num)
theorem B2593853 : Blo 1729065 2593853 := bbase (se 3 (by rfl) ⟨486347, by rfl⟩ : syracuseStep 2593853 = 972695) (by norm_num)
theorem B2593877 : Blo 1729065 2593877 := bbase (se 8 (by rfl) ⟨15198, by rfl⟩ : syracuseStep 2593877 = 30397) (by norm_num)
theorem B14783573 : Blo 1729065 14783573 := bbase (se 8 (by rfl) ⟨86622, by rfl⟩ : syracuseStep 14783573 = 173245) (by norm_num)
theorem B1946713 : Blo 1729065 1946713 := bbase (se 2 (by rfl) ⟨730017, by rfl⟩ : syracuseStep 1946713 = 1460035) (by norm_num)
theorem B4379741 : Blo 1729065 4379741 := bbase (se 3 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 4379741 = 1642403) (by norm_num)
theorem B1848425 : Blo 1729065 1848425 := bbase (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) (by norm_num)
theorem B2593901 : Blo 1729065 2593901 := bbase (se 3 (by rfl) ⟨486356, by rfl⟩ : syracuseStep 2593901 = 972713) (by norm_num)
theorem B1946749 : Blo 1729065 1946749 := bbase (se 3 (by rfl) ⟨365015, by rfl⟩ : syracuseStep 1946749 = 730031) (by norm_num)
theorem B2593925 : Blo 1729065 2593925 := bbase (se 4 (by rfl) ⟨243180, by rfl⟩ : syracuseStep 2593925 = 486361) (by norm_num)
theorem B2593949 : Blo 1729065 2593949 := bbase (se 3 (by rfl) ⟨486365, by rfl⟩ : syracuseStep 2593949 = 972731) (by norm_num)
theorem B1946785 : Blo 1729065 1946785 := bbase (se 2 (by rfl) ⟨730044, by rfl⟩ : syracuseStep 1946785 = 1460089) (by norm_num)
theorem B2593973 : Blo 1729065 2593973 := bbase (se 5 (by rfl) ⟨121592, by rfl⟩ : syracuseStep 2593973 = 243185) (by norm_num)
theorem B1946821 : Blo 1729065 1946821 := bbase (se 4 (by rfl) ⟨182514, by rfl⟩ : syracuseStep 1946821 = 365029) (by norm_num)
theorem B2593997 : Blo 1729065 2593997 := bbase (se 3 (by rfl) ⟨486374, by rfl⟩ : syracuseStep 2593997 = 972749) (by norm_num)
theorem B2594021 : Blo 1729065 2594021 := bbase (se 4 (by rfl) ⟨243189, by rfl⟩ : syracuseStep 2594021 = 486379) (by norm_num)
theorem B1946857 : Blo 1729065 1946857 := bbase (se 2 (by rfl) ⟨730071, by rfl⟩ : syracuseStep 1946857 = 1460143) (by norm_num)
theorem B2594045 : Blo 1729065 2594045 := bbase (se 3 (by rfl) ⟨486383, by rfl⟩ : syracuseStep 2594045 = 972767) (by norm_num)
theorem B1946893 : Blo 1729065 1946893 := bbase (se 3 (by rfl) ⟨365042, by rfl⟩ : syracuseStep 1946893 = 730085) (by norm_num)
theorem B7386389 : Blo 1729065 7386389 := bbase (se 6 (by rfl) ⟨173118, by rfl⟩ : syracuseStep 7386389 = 346237) (by norm_num)
theorem B2594069 : Blo 1729065 2594069 := bbase (se 6 (by rfl) ⟨60798, by rfl⟩ : syracuseStep 2594069 = 121597) (by norm_num)
theorem B5838101 : Blo 1729065 5838101 := bbase (se 6 (by rfl) ⟨136830, by rfl⟩ : syracuseStep 5838101 = 273661) (by norm_num)
theorem B4379933 : Blo 1729065 4379933 := bbase (se 3 (by rfl) ⟨821237, by rfl⟩ : syracuseStep 4379933 = 1642475) (by norm_num)
theorem B2594093 : Blo 1729065 2594093 := bbase (se 3 (by rfl) ⟨486392, by rfl⟩ : syracuseStep 2594093 = 972785) (by norm_num)
theorem B1946929 : Blo 1729065 1946929 := bbase (se 2 (by rfl) ⟨730098, by rfl⟩ : syracuseStep 1946929 = 1460197) (by norm_num)
theorem B2594117 : Blo 1729065 2594117 := bbase (se 4 (by rfl) ⟨243198, by rfl⟩ : syracuseStep 2594117 = 486397) (by norm_num)
theorem B1946965 : Blo 1729065 1946965 := bbase (se 13 (by rfl) ⟨356, by rfl⟩ : syracuseStep 1946965 = 713) (by norm_num)
theorem B2594141 : Blo 1729065 2594141 := bbase (se 3 (by rfl) ⟨486401, by rfl⟩ : syracuseStep 2594141 = 972803) (by norm_num)
theorem B2594165 : Blo 1729065 2594165 := bbase (se 5 (by rfl) ⟨121601, by rfl⟩ : syracuseStep 2594165 = 243203) (by norm_num)
theorem B8762741 : Blo 1729065 8762741 := bbase (se 5 (by rfl) ⟨410753, by rfl⟩ : syracuseStep 8762741 = 821507) (by norm_num)
theorem B1947001 : Blo 1729065 1947001 := bbase (se 2 (by rfl) ⟨730125, by rfl⟩ : syracuseStep 1947001 = 1460251) (by norm_num)
theorem B2594189 : Blo 1729065 2594189 := bbase (se 3 (by rfl) ⟨486410, by rfl⟩ : syracuseStep 2594189 = 972821) (by norm_num)
theorem B1947037 : Blo 1729065 1947037 := bbase (se 3 (by rfl) ⟨365069, by rfl⟩ : syracuseStep 1947037 = 730139) (by norm_num)
theorem B2594213 : Blo 1729065 2594213 := bbase (se 4 (by rfl) ⟨243207, by rfl⟩ : syracuseStep 2594213 = 486415) (by norm_num)
theorem B2463149 : Blo 1729065 2463149 := bbase (se 3 (by rfl) ⟨461840, by rfl⟩ : syracuseStep 2463149 = 923681) (by norm_num)
theorem B2594237 : Blo 1729065 2594237 := bbase (se 3 (by rfl) ⟨486419, by rfl⟩ : syracuseStep 2594237 = 972839) (by norm_num)
theorem B1947073 : Blo 1729065 1947073 := bbase (se 2 (by rfl) ⟨730152, by rfl⟩ : syracuseStep 1947073 = 1460305) (by norm_num)
theorem B2594261 : Blo 1729065 2594261 := bbase (se 7 (by rfl) ⟨30401, by rfl⟩ : syracuseStep 2594261 = 60803) (by norm_num)
theorem B1947109 : Blo 1729065 1947109 := bbase (se 4 (by rfl) ⟨182541, by rfl⟩ : syracuseStep 1947109 = 365083) (by norm_num)
theorem B2594285 : Blo 1729065 2594285 := bbase (se 3 (by rfl) ⟨486428, by rfl⟩ : syracuseStep 2594285 = 972857) (by norm_num)
theorem B2594309 : Blo 1729065 2594309 := bbase (se 4 (by rfl) ⟨243216, by rfl⟩ : syracuseStep 2594309 = 486433) (by norm_num)
theorem B1947145 : Blo 1729065 1947145 := bbase (se 2 (by rfl) ⟨730179, by rfl⟩ : syracuseStep 1947145 = 1460359) (by norm_num)
theorem B2594333 : Blo 1729065 2594333 := bbase (se 3 (by rfl) ⟨486437, by rfl⟩ : syracuseStep 2594333 = 972875) (by norm_num)
theorem B1947181 : Blo 1729065 1947181 := bbase (se 3 (by rfl) ⟨365096, by rfl⟩ : syracuseStep 1947181 = 730193) (by norm_num)
theorem B2594357 : Blo 1729065 2594357 := bbase (se 5 (by rfl) ⟨121610, by rfl⟩ : syracuseStep 2594357 = 243221) (by norm_num)
theorem B2594381 : Blo 1729065 2594381 := bbase (se 3 (by rfl) ⟨486446, by rfl⟩ : syracuseStep 2594381 = 972893) (by norm_num)
theorem B1947217 : Blo 1729065 1947217 := bbase (se 2 (by rfl) ⟨730206, by rfl⟩ : syracuseStep 1947217 = 1460413) (by norm_num)
theorem B2594405 : Blo 1729065 2594405 := bbase (se 4 (by rfl) ⟨243225, by rfl⟩ : syracuseStep 2594405 = 486451) (by norm_num)
theorem B4380277 : Blo 1729065 4380277 := bbase (se 5 (by rfl) ⟨205325, by rfl⟩ : syracuseStep 4380277 = 410651) (by norm_num)
theorem B1947253 : Blo 1729065 1947253 := bbase (se 5 (by rfl) ⟨91277, by rfl⟩ : syracuseStep 1947253 = 182555) (by norm_num)
theorem B2594429 : Blo 1729065 2594429 := bbase (se 3 (by rfl) ⟨486455, by rfl⟩ : syracuseStep 2594429 = 972911) (by norm_num)
theorem B2078345 : Blo 1729065 2078345 := bbase (se 2 (by rfl) ⟨779379, by rfl⟩ : syracuseStep 2078345 = 1558759) (by norm_num)
theorem B3282581 : Blo 1729065 3282581 := bbase (se 6 (by rfl) ⟨76935, by rfl⟩ : syracuseStep 3282581 = 153871) (by norm_num)
theorem B5060245 : Blo 1729065 5060245 := bbase (se 6 (by rfl) ⟨118599, by rfl⟩ : syracuseStep 5060245 = 237199) (by norm_num)
theorem B2594453 : Blo 1729065 2594453 := bbase (se 6 (by rfl) ⟨60807, by rfl⟩ : syracuseStep 2594453 = 121615) (by norm_num)
theorem B1947289 : Blo 1729065 1947289 := bbase (se 2 (by rfl) ⟨730233, by rfl⟩ : syracuseStep 1947289 = 1460467) (by norm_num)
theorem B1971869 : Blo 1729065 1971869 := bbase (se 3 (by rfl) ⟨369725, by rfl⟩ : syracuseStep 1971869 = 739451) (by norm_num)
theorem B2594477 : Blo 1729065 2594477 := bbase (se 3 (by rfl) ⟨486464, by rfl⟩ : syracuseStep 2594477 = 972929) (by norm_num)
theorem B1947325 : Blo 1729065 1947325 := bbase (se 3 (by rfl) ⟨365123, by rfl⟩ : syracuseStep 1947325 = 730247) (by norm_num)
theorem B2594501 : Blo 1729065 2594501 := bbase (se 4 (by rfl) ⟨243234, by rfl⟩ : syracuseStep 2594501 = 486469) (by norm_num)
theorem B5838533 : Blo 1729065 5838533 := bbase (se 4 (by rfl) ⟨547362, by rfl⟩ : syracuseStep 5838533 = 1094725) (by norm_num)
theorem B2594525 : Blo 1729065 2594525 := bbase (se 3 (by rfl) ⟨486473, by rfl⟩ : syracuseStep 2594525 = 972947) (by norm_num)
theorem B1947361 : Blo 1729065 1947361 := bbase (se 2 (by rfl) ⟨730260, by rfl⟩ : syracuseStep 1947361 = 1460521) (by norm_num)
theorem B4380389 : Blo 1729065 4380389 := bbase (se 4 (by rfl) ⟨410661, by rfl⟩ : syracuseStep 4380389 = 821323) (by norm_num)
theorem B3118829 : Blo 1729065 3118829 := bbase (se 3 (by rfl) ⟨584780, by rfl⟩ : syracuseStep 3118829 = 1169561) (by norm_num)
theorem B2594549 : Blo 1729065 2594549 := bbase (se 5 (by rfl) ⟨121619, by rfl⟩ : syracuseStep 2594549 = 243239) (by norm_num)
theorem B8427269 : Blo 1729065 8427269 := bbase (se 4 (by rfl) ⟨790056, by rfl⟩ : syracuseStep 8427269 = 1580113) (by norm_num)
theorem B1947397 : Blo 1729065 1947397 := bbase (se 4 (by rfl) ⟨182568, by rfl⟩ : syracuseStep 1947397 = 365137) (by norm_num)
theorem B2594573 : Blo 1729065 2594573 := bbase (se 3 (by rfl) ⟨486482, by rfl⟩ : syracuseStep 2594573 = 972965) (by norm_num)
theorem B8754965 : Blo 1729065 8754965 := bbase (se 6 (by rfl) ⟨205194, by rfl⟩ : syracuseStep 8754965 = 410389) (by norm_num)
theorem B2594597 : Blo 1729065 2594597 := bbase (se 4 (by rfl) ⟨243243, by rfl⟩ : syracuseStep 2594597 = 486487) (by norm_num)
theorem B1947433 : Blo 1729065 1947433 := bbase (se 2 (by rfl) ⟨730287, by rfl⟩ : syracuseStep 1947433 = 1460575) (by norm_num)
theorem B2594621 : Blo 1729065 2594621 := bbase (se 3 (by rfl) ⟨486491, by rfl⟩ : syracuseStep 2594621 = 972983) (by norm_num)
theorem B2594645 : Blo 1729065 2594645 := bbase (se 9 (by rfl) ⟨7601, by rfl⟩ : syracuseStep 2594645 = 15203) (by norm_num)
theorem B5543765 : Blo 1729065 5543765 := bbase (se 9 (by rfl) ⟨16241, by rfl⟩ : syracuseStep 5543765 = 32483) (by norm_num)
theorem B2594669 : Blo 1729065 2594669 := bbase (se 3 (by rfl) ⟨486500, by rfl⟩ : syracuseStep 2594669 = 973001) (by norm_num)
theorem B4675445 : Blo 1729065 4675445 := bbase (se 5 (by rfl) ⟨219161, by rfl⟩ : syracuseStep 4675445 = 438323) (by norm_num)
theorem B2594693 : Blo 1729065 2594693 := bbase (se 4 (by rfl) ⟨243252, by rfl⟩ : syracuseStep 2594693 = 486505) (by norm_num)
theorem B3118981 : Blo 1729065 3118981 := bbase (se 4 (by rfl) ⟨292404, by rfl⟩ : syracuseStep 3118981 = 584809) (by norm_num)
theorem B2594717 : Blo 1729065 2594717 := bbase (se 3 (by rfl) ⟨486509, by rfl⟩ : syracuseStep 2594717 = 973019) (by norm_num)
theorem B4380581 : Blo 1729065 4380581 := bbase (se 4 (by rfl) ⟨410679, by rfl⟩ : syracuseStep 4380581 = 821359) (by norm_num)
theorem B3282869 : Blo 1729065 3282869 := bbase (se 5 (by rfl) ⟨153884, by rfl⟩ : syracuseStep 3282869 = 307769) (by norm_num)
theorem B2594741 : Blo 1729065 2594741 := bbase (se 5 (by rfl) ⟨121628, by rfl⟩ : syracuseStep 2594741 = 243257) (by norm_num)
theorem B2594765 : Blo 1729065 2594765 := bbase (se 3 (by rfl) ⟨486518, by rfl⟩ : syracuseStep 2594765 = 973037) (by norm_num)
theorem B2807765 : Blo 1729065 2807765 := bbase (se 7 (by rfl) ⟨32903, by rfl⟩ : syracuseStep 2807765 = 65807) (by norm_num)
theorem B2463701 : Blo 1729065 2463701 := bbase (se 7 (by rfl) ⟨28871, by rfl⟩ : syracuseStep 2463701 = 57743) (by norm_num)
theorem B2078681 : Blo 1729065 2078681 := bbase (se 2 (by rfl) ⟨779505, by rfl⟩ : syracuseStep 2078681 = 1559011) (by norm_num)
theorem B2594789 : Blo 1729065 2594789 := bbase (se 4 (by rfl) ⟨243261, by rfl⟩ : syracuseStep 2594789 = 486523) (by norm_num)
theorem B6567925 : Blo 1729065 6567925 := bbase (se 5 (by rfl) ⟨307871, by rfl⟩ : syracuseStep 6567925 = 615743) (by norm_num)
theorem B2594813 : Blo 1729065 2594813 := bbase (se 3 (by rfl) ⟨486527, by rfl⟩ : syracuseStep 2594813 = 973055) (by norm_num)
theorem B2594837 : Blo 1729065 2594837 := bbase (se 6 (by rfl) ⟨60816, by rfl⟩ : syracuseStep 2594837 = 121633) (by norm_num)
theorem B2594861 : Blo 1729065 2594861 := bbase (se 3 (by rfl) ⟨486536, by rfl⟩ : syracuseStep 2594861 = 973073) (by norm_num)
theorem B2594885 : Blo 1729065 2594885 := bbase (se 4 (by rfl) ⟨243270, by rfl⟩ : syracuseStep 2594885 = 486541) (by norm_num)
theorem B3283021 : Blo 1729065 3283021 := bbase (se 3 (by rfl) ⟨615566, by rfl⟩ : syracuseStep 3283021 = 1231133) (by norm_num)
theorem B2078797 : Blo 1729065 2078797 := bbase (se 3 (by rfl) ⟨389774, by rfl⟩ : syracuseStep 2078797 = 779549) (by norm_num)
theorem B2250841 : Blo 1729065 2250841 := bbase (se 2 (by rfl) ⟨844065, by rfl⟩ : syracuseStep 2250841 = 1688131) (by norm_num)
theorem B2594909 : Blo 1729065 2594909 := bbase (se 3 (by rfl) ⟨486545, by rfl⟩ : syracuseStep 2594909 = 973091) (by norm_num)
theorem B2078821 : Blo 1729065 2078821 := bbase (se 4 (by rfl) ⟨194889, by rfl⟩ : syracuseStep 2078821 = 389779) (by norm_num)
theorem B2594933 : Blo 1729065 2594933 := bbase (se 5 (by rfl) ⟨121637, by rfl⟩ : syracuseStep 2594933 = 243275) (by norm_num)
theorem B5838965 : Blo 1729065 5838965 := bbase (se 5 (by rfl) ⟨273701, by rfl⟩ : syracuseStep 5838965 = 547403) (by norm_num)
theorem B13138037 : Blo 1729065 13138037 := bbase (se 5 (by rfl) ⟨615845, by rfl⟩ : syracuseStep 13138037 = 1231691) (by norm_num)
theorem B2594957 : Blo 1729065 2594957 := bbase (se 3 (by rfl) ⟨486554, by rfl⟩ : syracuseStep 2594957 = 973109) (by norm_num)
theorem B2594981 : Blo 1729065 2594981 := bbase (se 4 (by rfl) ⟨243279, by rfl⟩ : syracuseStep 2594981 = 486559) (by norm_num)
theorem B2595005 : Blo 1729065 2595005 := bbase (se 3 (by rfl) ⟨486563, by rfl⟩ : syracuseStep 2595005 = 973127) (by norm_num)
theorem B2595029 : Blo 1729065 2595029 := bbase (se 7 (by rfl) ⟨30410, by rfl⟩ : syracuseStep 2595029 = 60821) (by norm_num)
theorem B2595053 : Blo 1729065 2595053 := bbase (se 3 (by rfl) ⟨486572, by rfl⟩ : syracuseStep 2595053 = 973145) (by norm_num)
theorem B4380925 : Blo 1729065 4380925 := bbase (se 3 (by rfl) ⟨821423, by rfl⟩ : syracuseStep 4380925 = 1642847) (by norm_num)
theorem B2595077 : Blo 1729065 2595077 := bbase (se 4 (by rfl) ⟨243288, by rfl⟩ : syracuseStep 2595077 = 486577) (by norm_num)
theorem B2595101 : Blo 1729065 2595101 := bbase (se 3 (by rfl) ⟨486581, by rfl⟩ : syracuseStep 2595101 = 973163) (by norm_num)
theorem B6568229 : Blo 1729065 6568229 := bbase (se 4 (by rfl) ⟨615771, by rfl⟩ : syracuseStep 6568229 = 1231543) (by norm_num)
theorem B2595125 : Blo 1729065 2595125 := bbase (se 5 (by rfl) ⟨121646, by rfl⟩ : syracuseStep 2595125 = 243293) (by norm_num)
theorem B4675909 : Blo 1729065 4675909 := bbase (se 4 (by rfl) ⟨438366, by rfl⟩ : syracuseStep 4675909 = 876733) (by norm_num)
theorem B2595149 : Blo 1729065 2595149 := bbase (se 3 (by rfl) ⟨486590, by rfl⟩ : syracuseStep 2595149 = 973181) (by norm_num)
theorem B2595173 : Blo 1729065 2595173 := bbase (se 4 (by rfl) ⟨243297, by rfl⟩ : syracuseStep 2595173 = 486595) (by norm_num)
theorem B4381037 : Blo 1729065 4381037 := bbase (se 3 (by rfl) ⟨821444, by rfl⟩ : syracuseStep 4381037 = 1642889) (by norm_num)
theorem B3283325 : Blo 1729065 3283325 := bbase (se 3 (by rfl) ⟨615623, by rfl⟩ : syracuseStep 3283325 = 1231247) (by norm_num)
theorem B2595197 : Blo 1729065 2595197 := bbase (se 3 (by rfl) ⟨486599, by rfl⟩ : syracuseStep 2595197 = 973199) (by norm_num)
theorem B2595221 : Blo 1729065 2595221 := bbase (se 6 (by rfl) ⟨60825, by rfl⟩ : syracuseStep 2595221 = 121651) (by norm_num)
theorem B2595245 : Blo 1729065 2595245 := bbase (se 3 (by rfl) ⟨486608, by rfl⟩ : syracuseStep 2595245 = 973217) (by norm_num)
theorem B3692989 : Blo 1729065 3692989 := bbase (se 3 (by rfl) ⟨692435, by rfl⟩ : syracuseStep 3692989 = 1384871) (by norm_num)
theorem B2595269 : Blo 1729065 2595269 := bbase (se 4 (by rfl) ⟨243306, by rfl⟩ : syracuseStep 2595269 = 486613) (by norm_num)
theorem B11082197 : Blo 1729065 11082197 := bbase (se 7 (by rfl) ⟨129869, by rfl⟩ : syracuseStep 11082197 = 259739) (by norm_num)
theorem B2595293 : Blo 1729065 2595293 := bbase (se 3 (by rfl) ⟨486617, by rfl⟩ : syracuseStep 2595293 = 973235) (by norm_num)
theorem B2218477 : Blo 1729065 2218477 := bbase (se 3 (by rfl) ⟨415964, by rfl⟩ : syracuseStep 2218477 = 831929) (by norm_num)
theorem B2595317 : Blo 1729065 2595317 := bbase (se 5 (by rfl) ⟨121655, by rfl⟩ : syracuseStep 2595317 = 243311) (by norm_num)
theorem B2595341 : Blo 1729065 2595341 := bbase (se 3 (by rfl) ⟨486626, by rfl⟩ : syracuseStep 2595341 = 973253) (by norm_num)
theorem B13130261 : Blo 1729065 13130261 := bbase (se 6 (by rfl) ⟨307740, by rfl⟩ : syracuseStep 13130261 = 615481) (by norm_num)
theorem B5839397 : Blo 1729065 5839397 := bbase (se 4 (by rfl) ⟨547443, by rfl⟩ : syracuseStep 5839397 = 1094887) (by norm_num)
theorem B2595365 : Blo 1729065 2595365 := bbase (se 4 (by rfl) ⟨243315, by rfl⟩ : syracuseStep 2595365 = 486631) (by norm_num)
theorem B4381229 : Blo 1729065 4381229 := bbase (se 3 (by rfl) ⟨821480, by rfl⟩ : syracuseStep 4381229 = 1642961) (by norm_num)
theorem B3693109 : Blo 1729065 3693109 := bbase (se 5 (by rfl) ⟨173114, by rfl⟩ : syracuseStep 3693109 = 346229) (by norm_num)
theorem B2595389 : Blo 1729065 2595389 := bbase (se 3 (by rfl) ⟨486635, by rfl⟩ : syracuseStep 2595389 = 973271) (by norm_num)
theorem B2808389 : Blo 1729065 2808389 := bbase (se 4 (by rfl) ⟨263286, by rfl⟩ : syracuseStep 2808389 = 526573) (by norm_num)
theorem B2595413 : Blo 1729065 2595413 := bbase (se 8 (by rfl) ⟨15207, by rfl⟩ : syracuseStep 2595413 = 30415) (by norm_num)
theorem B1972841 : Blo 1729065 1972841 := bbase (se 2 (by rfl) ⟨739815, by rfl⟩ : syracuseStep 1972841 = 1479631) (by norm_num)
theorem B2595437 : Blo 1729065 2595437 := bbase (se 3 (by rfl) ⟨486644, by rfl⟩ : syracuseStep 2595437 = 973289) (by norm_num)
theorem B2595461 : Blo 1729065 2595461 := bbase (se 4 (by rfl) ⟨243324, by rfl⟩ : syracuseStep 2595461 = 486649) (by norm_num)
theorem B2595485 : Blo 1729065 2595485 := bbase (se 3 (by rfl) ⟨486653, by rfl⟩ : syracuseStep 2595485 = 973307) (by norm_num)
theorem B2595509 : Blo 1729065 2595509 := bbase (se 5 (by rfl) ⟨121664, by rfl⟩ : syracuseStep 2595509 = 243329) (by norm_num)
theorem B5331653 : Blo 1729065 5331653 := bbase (se 4 (by rfl) ⟨499842, by rfl⟩ : syracuseStep 5331653 = 999685) (by norm_num)
theorem B2464453 : Blo 1729065 2464453 := bbase (se 4 (by rfl) ⟨231042, by rfl⟩ : syracuseStep 2464453 = 462085) (by norm_num)
theorem B2595533 : Blo 1729065 2595533 := bbase (se 3 (by rfl) ⟨486662, by rfl⟩ : syracuseStep 2595533 = 973325) (by norm_num)
theorem B2595557 : Blo 1729065 2595557 := bbase (se 4 (by rfl) ⟨243333, by rfl⟩ : syracuseStep 2595557 = 486667) (by norm_num)
theorem B2595581 : Blo 1729065 2595581 := bbase (se 3 (by rfl) ⟨486671, by rfl⟩ : syracuseStep 2595581 = 973343) (by norm_num)
theorem B2595605 : Blo 1729065 2595605 := bbase (se 6 (by rfl) ⟨60834, by rfl⟩ : syracuseStep 2595605 = 121669) (by norm_num)
theorem B2079517 : Blo 1729065 2079517 := bbase (se 3 (by rfl) ⟨389909, by rfl⟩ : syracuseStep 2079517 = 779819) (by norm_num)
theorem B2595629 : Blo 1729065 2595629 := bbase (se 3 (by rfl) ⟨486680, by rfl⟩ : syracuseStep 2595629 = 973361) (by norm_num)
theorem B3693365 : Blo 1729065 3693365 := bbase (se 5 (by rfl) ⟨173126, by rfl⟩ : syracuseStep 3693365 = 346253) (by norm_num)
theorem B2595653 : Blo 1729065 2595653 := bbase (se 4 (by rfl) ⟨243342, by rfl⟩ : syracuseStep 2595653 = 486685) (by norm_num)
theorem B2595677 : Blo 1729065 2595677 := bbase (se 3 (by rfl) ⟨486689, by rfl⟩ : syracuseStep 2595677 = 973379) (by norm_num)
theorem B11836277 : Blo 1729065 11836277 := bbase (se 5 (by rfl) ⟨554825, by rfl⟩ : syracuseStep 11836277 = 1109651) (by norm_num)
theorem B2595701 : Blo 1729065 2595701 := bbase (se 5 (by rfl) ⟨121673, by rfl⟩ : syracuseStep 2595701 = 243347) (by norm_num)
theorem B2079613 : Blo 1729065 2079613 := bbase (se 3 (by rfl) ⟨389927, by rfl⟩ : syracuseStep 2079613 = 779855) (by norm_num)
theorem B4381573 : Blo 1729065 4381573 := bbase (se 4 (by rfl) ⟨410772, by rfl⟩ : syracuseStep 4381573 = 821545) (by norm_num)
theorem B2595725 : Blo 1729065 2595725 := bbase (se 3 (by rfl) ⟨486698, by rfl⟩ : syracuseStep 2595725 = 973397) (by norm_num)
theorem B2595749 : Blo 1729065 2595749 := bbase (se 4 (by rfl) ⟨243351, by rfl⟩ : syracuseStep 2595749 = 486703) (by norm_num)
theorem B2595773 : Blo 1729065 2595773 := bbase (se 3 (by rfl) ⟨486707, by rfl⟩ : syracuseStep 2595773 = 973415) (by norm_num)
theorem B5839829 : Blo 1729065 5839829 := bbase (se 7 (by rfl) ⟨68435, by rfl⟩ : syracuseStep 5839829 = 136871) (by norm_num)
theorem B2595797 : Blo 1729065 2595797 := bbase (se 7 (by rfl) ⟨30419, by rfl⟩ : syracuseStep 2595797 = 60839) (by norm_num)
theorem B2595821 : Blo 1729065 2595821 := bbase (se 3 (by rfl) ⟨486716, by rfl⟩ : syracuseStep 2595821 = 973433) (by norm_num)
theorem B4381685 : Blo 1729065 4381685 := bbase (se 5 (by rfl) ⟨205391, by rfl⟩ : syracuseStep 4381685 = 410783) (by norm_num)
theorem B7388165 : Blo 1729065 7388165 := bbase (se 4 (by rfl) ⟨692640, by rfl⟩ : syracuseStep 7388165 = 1385281) (by norm_num)
theorem B2595845 : Blo 1729065 2595845 := bbase (se 4 (by rfl) ⟨243360, by rfl⟩ : syracuseStep 2595845 = 486721) (by norm_num)
theorem B2595869 : Blo 1729065 2595869 := bbase (se 3 (by rfl) ⟨486725, by rfl⟩ : syracuseStep 2595869 = 973451) (by norm_num)
theorem B8756261 : Blo 1729065 8756261 := bbase (se 4 (by rfl) ⟨820899, by rfl⟩ : syracuseStep 8756261 = 1641799) (by norm_num)
theorem B2595893 : Blo 1729065 2595893 := bbase (se 5 (by rfl) ⟨121682, by rfl⟩ : syracuseStep 2595893 = 243365) (by norm_num)
theorem B7011397 : Blo 1729065 7011397 := bbase (se 4 (by rfl) ⟨657318, by rfl⟩ : syracuseStep 7011397 = 1314637) (by norm_num)
theorem B2595917 : Blo 1729065 2595917 := bbase (se 3 (by rfl) ⟨486734, by rfl⟩ : syracuseStep 2595917 = 973469) (by norm_num)
theorem B48012373 : Blo 1729065 48012373 := bbase (se 8 (by rfl) ⟨281322, by rfl⟩ : syracuseStep 48012373 = 562645) (by norm_num)
theorem B2595941 : Blo 1729065 2595941 := bbase (se 4 (by rfl) ⟨243369, by rfl⟩ : syracuseStep 2595941 = 486739) (by norm_num)
theorem B3284077 : Blo 1729065 3284077 := bbase (se 3 (by rfl) ⟨615764, by rfl⟩ : syracuseStep 3284077 = 1231529) (by norm_num)
theorem B2595965 : Blo 1729065 2595965 := bbase (se 3 (by rfl) ⟨486743, by rfl⟩ : syracuseStep 2595965 = 973487) (by norm_num)
theorem B2595989 : Blo 1729065 2595989 := bbase (se 6 (by rfl) ⟨60843, by rfl⟩ : syracuseStep 2595989 = 121687) (by norm_num)
theorem B2596013 : Blo 1729065 2596013 := bbase (se 3 (by rfl) ⟨486752, by rfl⟩ : syracuseStep 2596013 = 973505) (by norm_num)
theorem B2596037 : Blo 1729065 2596037 := bbase (se 4 (by rfl) ⟨243378, by rfl⟩ : syracuseStep 2596037 = 486757) (by norm_num)
theorem B2596061 : Blo 1729065 2596061 := bbase (se 3 (by rfl) ⟨486761, by rfl⟩ : syracuseStep 2596061 = 973523) (by norm_num)
theorem B4676837 : Blo 1729065 4676837 := bbase (se 4 (by rfl) ⟨438453, by rfl⟩ : syracuseStep 4676837 = 876907) (by norm_num)
theorem B7388405 : Blo 1729065 7388405 := bbase (se 5 (by rfl) ⟨346331, by rfl⟩ : syracuseStep 7388405 = 692663) (by norm_num)
theorem B8428789 : Blo 1729065 8428789 := bbase (se 5 (by rfl) ⟨395099, by rfl⟩ : syracuseStep 8428789 = 790199) (by norm_num)
theorem B2596085 : Blo 1729065 2596085 := bbase (se 5 (by rfl) ⟨121691, by rfl⟩ : syracuseStep 2596085 = 243383) (by norm_num)
theorem B3890429 : Blo 1729065 3890429 := bbase (se 3 (by rfl) ⟨729455, by rfl⟩ : syracuseStep 3890429 = 1458911) (by norm_num)
theorem B3284221 : Blo 1729065 3284221 := bbase (se 3 (by rfl) ⟨615791, by rfl⟩ : syracuseStep 3284221 = 1231583) (by norm_num)
theorem B2596109 : Blo 1729065 2596109 := bbase (se 3 (by rfl) ⟨486770, by rfl⟩ : syracuseStep 2596109 = 973541) (by norm_num)
theorem B2596133 : Blo 1729065 2596133 := bbase (se 4 (by rfl) ⟨243387, by rfl⟩ : syracuseStep 2596133 = 486775) (by norm_num)
theorem B2596157 : Blo 1729065 2596157 := bbase (se 3 (by rfl) ⟨486779, by rfl⟩ : syracuseStep 2596157 = 973559) (by norm_num)
theorem B3890501 : Blo 1729065 3890501 := bbase (se 4 (by rfl) ⟨364734, by rfl⟩ : syracuseStep 3890501 = 729469) (by norm_num)
theorem B2596181 : Blo 1729065 2596181 := bbase (se 11 (by rfl) ⟨1901, by rfl⟩ : syracuseStep 2596181 = 3803) (by norm_num)
theorem B2596205 : Blo 1729065 2596205 := bbase (se 3 (by rfl) ⟨486788, by rfl⟩ : syracuseStep 2596205 = 973577) (by norm_num)
theorem B5840261 : Blo 1729065 5840261 := bbase (se 4 (by rfl) ⟨547524, by rfl⟩ : syracuseStep 5840261 = 1095049) (by norm_num)
theorem B2596229 : Blo 1729065 2596229 := bbase (se 4 (by rfl) ⟨243396, by rfl⟩ : syracuseStep 2596229 = 486793) (by norm_num)
theorem B3890573 : Blo 1729065 3890573 := bbase (se 3 (by rfl) ⟨729482, by rfl⟩ : syracuseStep 3890573 = 1458965) (by norm_num)
theorem B3284381 : Blo 1729065 3284381 := bbase (se 3 (by rfl) ⟨615821, by rfl⟩ : syracuseStep 3284381 = 1231643) (by norm_num)
theorem B2596253 : Blo 1729065 2596253 := bbase (se 3 (by rfl) ⟨486797, by rfl⟩ : syracuseStep 2596253 = 973595) (by norm_num)
theorem B2596277 : Blo 1729065 2596277 := bbase (se 5 (by rfl) ⟨121700, by rfl⟩ : syracuseStep 2596277 = 243401) (by norm_num)
theorem B2596301 : Blo 1729065 2596301 := bbase (se 3 (by rfl) ⟨486806, by rfl⟩ : syracuseStep 2596301 = 973613) (by norm_num)
theorem B3890645 : Blo 1729065 3890645 := bbase (se 7 (by rfl) ⟨45593, by rfl⟩ : syracuseStep 3890645 = 91187) (by norm_num)
theorem B2596325 : Blo 1729065 2596325 := bbase (se 4 (by rfl) ⟨243405, by rfl⟩ : syracuseStep 2596325 = 486811) (by norm_num)
theorem B2596349 : Blo 1729065 2596349 := bbase (se 3 (by rfl) ⟨486815, by rfl⟩ : syracuseStep 2596349 = 973631) (by norm_num)
theorem B3743237 : Blo 1729065 3743237 := bbase (se 4 (by rfl) ⟨350928, by rfl⟩ : syracuseStep 3743237 = 701857) (by norm_num)
theorem B2596373 : Blo 1729065 2596373 := bbase (se 6 (by rfl) ⟨60852, by rfl⟩ : syracuseStep 2596373 = 121705) (by norm_num)
theorem B3890717 : Blo 1729065 3890717 := bbase (se 3 (by rfl) ⟨729509, by rfl⟩ : syracuseStep 3890717 = 1459019) (by norm_num)
theorem B3284525 : Blo 1729065 3284525 := bbase (se 3 (by rfl) ⟨615848, by rfl⟩ : syracuseStep 3284525 = 1231697) (by norm_num)
theorem B2596397 : Blo 1729065 2596397 := bbase (se 3 (by rfl) ⟨486824, by rfl⟩ : syracuseStep 2596397 = 973649) (by norm_num)
theorem B2596421 : Blo 1729065 2596421 := bbase (se 4 (by rfl) ⟨243414, by rfl⟩ : syracuseStep 2596421 = 486829) (by norm_num)
theorem B2596445 : Blo 1729065 2596445 := bbase (se 3 (by rfl) ⟨486833, by rfl⟩ : syracuseStep 2596445 = 973667) (by norm_num)
theorem B3890789 : Blo 1729065 3890789 := bbase (se 4 (by rfl) ⟨364761, by rfl⟩ : syracuseStep 3890789 = 729523) (by norm_num)
theorem B2596469 : Blo 1729065 2596469 := bbase (se 5 (by rfl) ⟨121709, by rfl⟩ : syracuseStep 2596469 = 243419) (by norm_num)
theorem B2596493 : Blo 1729065 2596493 := bbase (se 3 (by rfl) ⟨486842, by rfl⟩ : syracuseStep 2596493 = 973685) (by norm_num)
theorem B2596517 : Blo 1729065 2596517 := bbase (se 4 (by rfl) ⟨243423, by rfl⟩ : syracuseStep 2596517 = 486847) (by norm_num)
theorem B3890861 : Blo 1729065 3890861 := bbase (se 3 (by rfl) ⟨729536, by rfl⟩ : syracuseStep 3890861 = 1459073) (by norm_num)
theorem B3694253 : Blo 1729065 3694253 := bbase (se 3 (by rfl) ⟨692672, by rfl⟩ : syracuseStep 3694253 = 1385345) (by norm_num)
theorem B2596541 : Blo 1729065 2596541 := bbase (se 3 (by rfl) ⟨486851, by rfl⟩ : syracuseStep 2596541 = 973703) (by norm_num)
theorem B1973953 : Blo 1729065 1973953 := bbase (se 2 (by rfl) ⟨740232, by rfl⟩ : syracuseStep 1973953 = 1480465) (by norm_num)
theorem B2596565 : Blo 1729065 2596565 := bbase (se 7 (by rfl) ⟨30428, by rfl⟩ : syracuseStep 2596565 = 60857) (by norm_num)
theorem B2596589 : Blo 1729065 2596589 := bbase (se 3 (by rfl) ⟨486860, by rfl⟩ : syracuseStep 2596589 = 973721) (by norm_num)
theorem B3890933 : Blo 1729065 3890933 := bbase (se 5 (by rfl) ⟨182387, by rfl⟩ : syracuseStep 3890933 = 364775) (by norm_num)
theorem B5840693 : Blo 1729065 5840693 := bbase (se 5 (by rfl) ⟨273782, by rfl⟩ : syracuseStep 5840693 = 547565) (by norm_num)
theorem B3891005 : Blo 1729065 3891005 := bbase (se 3 (by rfl) ⟨729563, by rfl⟩ : syracuseStep 3891005 = 1459127) (by norm_num)
theorem B3284813 : Blo 1729065 3284813 := bbase (se 3 (by rfl) ⟨615902, by rfl⟩ : syracuseStep 3284813 = 1231805) (by norm_num)
theorem B33259349 : Blo 1729065 33259349 := bbase (se 9 (by rfl) ⟨97439, by rfl⟩ : syracuseStep 33259349 = 194879) (by norm_num)
theorem B2629469 : Blo 1729065 2629469 := bbase (se 3 (by rfl) ⟨493025, by rfl⟩ : syracuseStep 2629469 = 986051) (by norm_num)
theorem B3891077 : Blo 1729065 3891077 := bbase (se 4 (by rfl) ⟨364788, by rfl⟩ : syracuseStep 3891077 = 729577) (by norm_num)
theorem B3694493 : Blo 1729065 3694493 := bbase (se 3 (by rfl) ⟨692717, by rfl⟩ : syracuseStep 3694493 = 1385435) (by norm_num)
theorem B15392693 : Blo 1729065 15392693 := bbase (se 5 (by rfl) ⟨721532, by rfl⟩ : syracuseStep 15392693 = 1443065) (by norm_num)
theorem B3891149 : Blo 1729065 3891149 := bbase (se 3 (by rfl) ⟨729590, by rfl⟩ : syracuseStep 3891149 = 1459181) (by norm_num)
theorem B3284965 : Blo 1729065 3284965 := bbase (se 4 (by rfl) ⟨307965, by rfl⟩ : syracuseStep 3284965 = 615931) (by norm_num)
theorem B14786549 : Blo 1729065 14786549 := bbase (se 5 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 14786549 = 1386239) (by norm_num)
theorem B3891203 : Blo 1729065 3891203 := bstep (se 1 (by rfl) ⟨2918402, by rfl⟩ : syracuseStep 3891203 = 5836805) B5836805
theorem B13139981 : Blo 1729065 13139981 := bstep (se 3 (by rfl) ⟨2463746, by rfl⟩ : syracuseStep 13139981 = 4927493) B4927493
theorem B5840909 : Blo 1729065 5840909 := bstep (se 3 (by rfl) ⟨1095170, by rfl⟩ : syracuseStep 5840909 = 2190341) B2190341
theorem B5840963 : Blo 1729065 5840963 := bstep (se 1 (by rfl) ⟨4380722, by rfl⟩ : syracuseStep 5840963 = 8761445) B8761445
theorem B10518605 : Blo 1729065 10518605 := bstep (se 3 (by rfl) ⟨1972238, by rfl⟩ : syracuseStep 10518605 = 3944477) B3944477
theorem B3891473 : Blo 1729065 3891473 := bstep (se 2 (by rfl) ⟨1459302, by rfl⟩ : syracuseStep 3891473 = 2918605) B2918605
theorem B3891491 : Blo 1729065 3891491 := bstep (se 1 (by rfl) ⟨2918618, by rfl⟩ : syracuseStep 3891491 = 5837237) B5837237
theorem B5841233 : Blo 1729065 5841233 := bstep (se 2 (by rfl) ⟨2190462, by rfl⟩ : syracuseStep 5841233 = 4380925) B4380925
theorem B11084195 : Blo 1729065 11084195 := bstep (se 1 (by rfl) ⟨8313146, by rfl⟩ : syracuseStep 11084195 = 16626293) B16626293
theorem B6234545 : Blo 1729065 6234545 := bstep (se 2 (by rfl) ⟨2337954, by rfl⟩ : syracuseStep 6234545 = 4675909) B4675909
theorem B6234659 : Blo 1729065 6234659 := bstep (se 1 (by rfl) ⟨4675994, by rfl⟩ : syracuseStep 6234659 = 9351989) B9351989
theorem B3891761 : Blo 1729065 3891761 := bstep (se 2 (by rfl) ⟨1459410, by rfl⟩ : syracuseStep 3891761 = 2918821) B2918821
theorem B1729075 : Blo 1729065 1729075 := bstep (se 1 (by rfl) ⟨1296806, by rfl⟩ : syracuseStep 1729075 = 2593613) B2593613
theorem B1729091 : Blo 1729065 1729091 := bstep (se 1 (by rfl) ⟨1296818, by rfl⟩ : syracuseStep 1729091 = 2593637) B2593637
theorem B3891779 : Blo 1729065 3891779 := bstep (se 1 (by rfl) ⟨2918834, by rfl⟩ : syracuseStep 3891779 = 5837669) B5837669
theorem B4923985 : Blo 1729065 4923985 := bstep (se 2 (by rfl) ⟨1846494, by rfl⟩ : syracuseStep 4923985 = 3692989) B3692989
theorem B1729107 : Blo 1729065 1729107 := bstep (se 1 (by rfl) ⟨1296830, by rfl⟩ : syracuseStep 1729107 = 2593661) B2593661
theorem B1729123 : Blo 1729065 1729123 := bstep (se 1 (by rfl) ⟨1296842, by rfl⟩ : syracuseStep 1729123 = 2593685) B2593685
theorem B1729139 : Blo 1729065 1729139 := bstep (se 1 (by rfl) ⟨1296854, by rfl⟩ : syracuseStep 1729139 = 2593709) B2593709
theorem B1729155 : Blo 1729065 1729155 := bstep (se 1 (by rfl) ⟨1296866, by rfl⟩ : syracuseStep 1729155 = 2593733) B2593733
theorem B2957969 : Blo 1729065 2957969 := bstep (se 2 (by rfl) ⟨1109238, by rfl⟩ : syracuseStep 2957969 = 2218477) B2218477
theorem B1729171 : Blo 1729065 1729171 := bstep (se 1 (by rfl) ⟨1296878, by rfl⟩ : syracuseStep 1729171 = 2593757) B2593757
theorem B1729187 : Blo 1729065 1729187 := bstep (se 1 (by rfl) ⟨1296890, by rfl⟩ : syracuseStep 1729187 = 2593781) B2593781
theorem B6570659 : Blo 1729065 6570659 := bstep (se 1 (by rfl) ⟨4927994, by rfl⟩ : syracuseStep 6570659 = 9855989) B9855989
theorem B1729203 : Blo 1729065 1729203 := bstep (se 1 (by rfl) ⟨1296902, by rfl⟩ : syracuseStep 1729203 = 2593805) B2593805
theorem B1729219 : Blo 1729065 1729219 := bstep (se 1 (by rfl) ⟨1296914, by rfl⟩ : syracuseStep 1729219 = 2593829) B2593829
theorem B1729235 : Blo 1729065 1729235 := bstep (se 1 (by rfl) ⟨1296926, by rfl⟩ : syracuseStep 1729235 = 2593853) B2593853
theorem B1729251 : Blo 1729065 1729251 := bstep (se 1 (by rfl) ⟨1296938, by rfl⟩ : syracuseStep 1729251 = 2593877) B2593877
theorem B3506915 : Blo 1729065 3506915 := bstep (se 1 (by rfl) ⟨2630186, by rfl⟩ : syracuseStep 3506915 = 5260373) B5260373
theorem B9855715 : Blo 1729065 9855715 := bstep (se 1 (by rfl) ⟨7391786, by rfl⟩ : syracuseStep 9855715 = 14783573) B14783573
theorem B4924145 : Blo 1729065 4924145 := bstep (se 2 (by rfl) ⟨1846554, by rfl⟩ : syracuseStep 4924145 = 3693109) B3693109
theorem B1729267 : Blo 1729065 1729267 := bstep (se 1 (by rfl) ⟨1296950, by rfl⟩ : syracuseStep 1729267 = 2593901) B2593901
theorem B1729283 : Blo 1729065 1729283 := bstep (se 1 (by rfl) ⟨1296962, by rfl⟩ : syracuseStep 1729283 = 2593925) B2593925
theorem B22160141 : Blo 1729065 22160141 := bstep (se 3 (by rfl) ⟨4155026, by rfl⟩ : syracuseStep 22160141 = 8310053) B8310053
theorem B1729299 : Blo 1729065 1729299 := bstep (se 1 (by rfl) ⟨1296974, by rfl⟩ : syracuseStep 1729299 = 2593949) B2593949
theorem B1729315 : Blo 1729065 1729315 := bstep (se 1 (by rfl) ⟨1296986, by rfl⟩ : syracuseStep 1729315 = 2593973) B2593973
theorem B1729331 : Blo 1729065 1729331 := bstep (se 1 (by rfl) ⟨1296998, by rfl⟩ : syracuseStep 1729331 = 2593997) B2593997
theorem B1729347 : Blo 1729065 1729347 := bstep (se 1 (by rfl) ⟨1297010, by rfl⟩ : syracuseStep 1729347 = 2594021) B2594021
theorem B3892049 : Blo 1729065 3892049 := bstep (se 2 (by rfl) ⟨1459518, by rfl⟩ : syracuseStep 3892049 = 2919037) B2919037
theorem B4678481 : Blo 1729065 4678481 := bstep (se 2 (by rfl) ⟨1754430, by rfl⟩ : syracuseStep 4678481 = 3508861) B3508861
theorem B1729363 : Blo 1729065 1729363 := bstep (se 1 (by rfl) ⟨1297022, by rfl⟩ : syracuseStep 1729363 = 2594045) B2594045
theorem B4924259 : Blo 1729065 4924259 := bstep (se 1 (by rfl) ⟨3693194, by rfl⟩ : syracuseStep 4924259 = 7386389) B7386389
theorem B1729379 : Blo 1729065 1729379 := bstep (se 1 (by rfl) ⟨1297034, by rfl⟩ : syracuseStep 1729379 = 2594069) B2594069
theorem B3892067 : Blo 1729065 3892067 := bstep (se 1 (by rfl) ⟨2919050, by rfl⟩ : syracuseStep 3892067 = 5838101) B5838101
theorem B5841773 : Blo 1729065 5841773 := bstep (se 3 (by rfl) ⟨1095332, by rfl⟩ : syracuseStep 5841773 = 2190665) B2190665
theorem B1729395 : Blo 1729065 1729395 := bstep (se 1 (by rfl) ⟨1297046, by rfl⟩ : syracuseStep 1729395 = 2594093) B2594093
theorem B1729411 : Blo 1729065 1729411 := bstep (se 1 (by rfl) ⟨1297058, by rfl⟩ : syracuseStep 1729411 = 2594117) B2594117
theorem B49873805 : Blo 1729065 49873805 := bstep (se 3 (by rfl) ⟨9351338, by rfl⟩ : syracuseStep 49873805 = 18702677) B18702677
theorem B5260177 : Blo 1729065 5260177 := bstep (se 2 (by rfl) ⟨1972566, by rfl⟩ : syracuseStep 5260177 = 3945133) B3945133
theorem B1729427 : Blo 1729065 1729427 := bstep (se 1 (by rfl) ⟨1297070, by rfl⟩ : syracuseStep 1729427 = 2594141) B2594141
theorem B1729443 : Blo 1729065 1729443 := bstep (se 1 (by rfl) ⟨1297082, by rfl⟩ : syracuseStep 1729443 = 2594165) B2594165
theorem B5841827 : Blo 1729065 5841827 := bstep (se 1 (by rfl) ⟨4381370, by rfl⟩ : syracuseStep 5841827 = 8762741) B8762741
theorem B3285937 : Blo 1729065 3285937 := bstep (se 2 (by rfl) ⟨1232226, by rfl⟩ : syracuseStep 3285937 = 2464453) B2464453
theorem B1729459 : Blo 1729065 1729459 := bstep (se 1 (by rfl) ⟨1297094, by rfl⟩ : syracuseStep 1729459 = 2594189) B2594189
theorem B1729475 : Blo 1729065 1729475 := bstep (se 1 (by rfl) ⟨1297106, by rfl⟩ : syracuseStep 1729475 = 2594213) B2594213
theorem B1729491 : Blo 1729065 1729491 := bstep (se 1 (by rfl) ⟨1297118, by rfl⟩ : syracuseStep 1729491 = 2594237) B2594237
theorem B1729507 : Blo 1729065 1729507 := bstep (se 1 (by rfl) ⟨1297130, by rfl⟩ : syracuseStep 1729507 = 2594261) B2594261
theorem B1729523 : Blo 1729065 1729523 := bstep (se 1 (by rfl) ⟨1297142, by rfl⟩ : syracuseStep 1729523 = 2594285) B2594285
theorem B1729539 : Blo 1729065 1729539 := bstep (se 1 (by rfl) ⟨1297154, by rfl⟩ : syracuseStep 1729539 = 2594309) B2594309
theorem B10527749 : Blo 1729065 10527749 := bstep (se 4 (by rfl) ⟨986976, by rfl⟩ : syracuseStep 10527749 = 1973953) B1973953
theorem B1729555 : Blo 1729065 1729555 := bstep (se 1 (by rfl) ⟨1297166, by rfl⟩ : syracuseStep 1729555 = 2594333) B2594333
theorem B1729571 : Blo 1729065 1729571 := bstep (se 1 (by rfl) ⟨1297178, by rfl⟩ : syracuseStep 1729571 = 2594357) B2594357
theorem B1729587 : Blo 1729065 1729587 := bstep (se 1 (by rfl) ⟨1297190, by rfl⟩ : syracuseStep 1729587 = 2594381) B2594381
theorem B1729603 : Blo 1729065 1729603 := bstep (se 1 (by rfl) ⟨1297202, by rfl⟩ : syracuseStep 1729603 = 2594405) B2594405
theorem B5915729 : Blo 1729065 5915729 := bstep (se 2 (by rfl) ⟨2218398, by rfl⟩ : syracuseStep 5915729 = 4436797) B4436797
theorem B1729619 : Blo 1729065 1729619 := bstep (se 1 (by rfl) ⟨1297214, by rfl⟩ : syracuseStep 1729619 = 2594429) B2594429
theorem B2188387 : Blo 1729065 2188387 := bstep (se 1 (by rfl) ⟨1641290, by rfl⟩ : syracuseStep 2188387 = 3282581) B3282581
theorem B1729635 : Blo 1729065 1729635 := bstep (se 1 (by rfl) ⟨1297226, by rfl⟩ : syracuseStep 1729635 = 2594453) B2594453
theorem B3892337 : Blo 1729065 3892337 := bstep (se 2 (by rfl) ⟨1459626, by rfl⟩ : syracuseStep 3892337 = 2919253) B2919253
theorem B37414001 : Blo 1729065 37414001 := bstep (se 2 (by rfl) ⟨14030250, by rfl⟩ : syracuseStep 37414001 = 28060501) B28060501
theorem B1729651 : Blo 1729065 1729651 := bstep (se 1 (by rfl) ⟨1297238, by rfl⟩ : syracuseStep 1729651 = 2594477) B2594477
theorem B1729667 : Blo 1729065 1729667 := bstep (se 1 (by rfl) ⟨1297250, by rfl⟩ : syracuseStep 1729667 = 2594501) B2594501
theorem B3892355 : Blo 1729065 3892355 := bstep (se 1 (by rfl) ⟨2919266, by rfl⟩ : syracuseStep 3892355 = 5838533) B5838533
theorem B1729683 : Blo 1729065 1729683 := bstep (se 1 (by rfl) ⟨1297262, by rfl⟩ : syracuseStep 1729683 = 2594525) B2594525
theorem B1729699 : Blo 1729065 1729699 := bstep (se 1 (by rfl) ⟨1297274, by rfl⟩ : syracuseStep 1729699 = 2594549) B2594549
theorem B5842097 : Blo 1729065 5842097 := bstep (se 2 (by rfl) ⟨2190786, by rfl⟩ : syracuseStep 5842097 = 4381573) B4381573
theorem B1729715 : Blo 1729065 1729715 := bstep (se 1 (by rfl) ⟨1297286, by rfl⟩ : syracuseStep 1729715 = 2594573) B2594573
theorem B1729731 : Blo 1729065 1729731 := bstep (se 1 (by rfl) ⟨1297298, by rfl⟩ : syracuseStep 1729731 = 2594597) B2594597
theorem B5694673 : Blo 1729065 5694673 := bstep (se 2 (by rfl) ⟨2135502, by rfl⟩ : syracuseStep 5694673 = 4271005) B4271005
theorem B3695825 : Blo 1729065 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B1729747 : Blo 1729065 1729747 := bstep (se 1 (by rfl) ⟨1297310, by rfl⟩ : syracuseStep 1729747 = 2594621) B2594621
theorem B1729763 : Blo 1729065 1729763 := bstep (se 1 (by rfl) ⟨1297322, by rfl⟩ : syracuseStep 1729763 = 2594645) B2594645
theorem B3695843 : Blo 1729065 3695843 := bstep (se 1 (by rfl) ⟨2771882, by rfl⟩ : syracuseStep 3695843 = 5543765) B5543765
theorem B9856241 : Blo 1729065 9856241 := bstep (se 2 (by rfl) ⟨3696090, by rfl⟩ : syracuseStep 9856241 = 7392181) B7392181
theorem B1729779 : Blo 1729065 1729779 := bstep (se 1 (by rfl) ⟨1297334, by rfl⟩ : syracuseStep 1729779 = 2594669) B2594669
theorem B1729795 : Blo 1729065 1729795 := bstep (se 1 (by rfl) ⟨1297346, by rfl⟩ : syracuseStep 1729795 = 2594693) B2594693
theorem B1729811 : Blo 1729065 1729811 := bstep (se 1 (by rfl) ⟨1297358, by rfl⟩ : syracuseStep 1729811 = 2594717) B2594717
theorem B1729827 : Blo 1729065 1729827 := bstep (se 1 (by rfl) ⟨1297370, by rfl⟩ : syracuseStep 1729827 = 2594741) B2594741
theorem B6571313 : Blo 1729065 6571313 := bstep (se 2 (by rfl) ⟨2464242, by rfl⟩ : syracuseStep 6571313 = 4928485) B4928485
theorem B1729843 : Blo 1729065 1729843 := bstep (se 1 (by rfl) ⟨1297382, by rfl⟩ : syracuseStep 1729843 = 2594765) B2594765
theorem B1729859 : Blo 1729065 1729859 := bstep (se 1 (by rfl) ⟨1297394, by rfl⟩ : syracuseStep 1729859 = 2594789) B2594789
theorem B7390541 : Blo 1729065 7390541 := bstep (se 3 (by rfl) ⟨1385726, by rfl⟩ : syracuseStep 7390541 = 2771453) B2771453
theorem B1729875 : Blo 1729065 1729875 := bstep (se 1 (by rfl) ⟨1297406, by rfl⟩ : syracuseStep 1729875 = 2594813) B2594813
theorem B1729891 : Blo 1729065 1729891 := bstep (se 1 (by rfl) ⟨1297418, by rfl⟩ : syracuseStep 1729891 = 2594837) B2594837
theorem B1729907 : Blo 1729065 1729907 := bstep (se 1 (by rfl) ⟨1297430, by rfl⟩ : syracuseStep 1729907 = 2594861) B2594861
theorem B1729923 : Blo 1729065 1729923 := bstep (se 1 (by rfl) ⟨1297442, by rfl⟩ : syracuseStep 1729923 = 2594885) B2594885
theorem B3892625 : Blo 1729065 3892625 := bstep (se 2 (by rfl) ⟨1459734, by rfl⟩ : syracuseStep 3892625 = 2919469) B2919469
theorem B1729939 : Blo 1729065 1729939 := bstep (se 1 (by rfl) ⟨1297454, by rfl⟩ : syracuseStep 1729939 = 2594909) B2594909
theorem B1729955 : Blo 1729065 1729955 := bstep (se 1 (by rfl) ⟨1297466, by rfl⟩ : syracuseStep 1729955 = 2594933) B2594933
theorem B3892643 : Blo 1729065 3892643 := bstep (se 1 (by rfl) ⟨2919482, by rfl⟩ : syracuseStep 3892643 = 5838965) B5838965
theorem B8758691 : Blo 1729065 8758691 := bstep (se 1 (by rfl) ⟨6569018, by rfl⟩ : syracuseStep 8758691 = 13138037) B13138037
theorem B9348529 : Blo 1729065 9348529 := bstep (se 2 (by rfl) ⟨3505698, by rfl⟩ : syracuseStep 9348529 = 7011397) B7011397
theorem B1729971 : Blo 1729065 1729971 := bstep (se 1 (by rfl) ⟨1297478, by rfl⟩ : syracuseStep 1729971 = 2594957) B2594957
theorem B1729987 : Blo 1729065 1729987 := bstep (se 1 (by rfl) ⟨1297490, by rfl⟩ : syracuseStep 1729987 = 2594981) B2594981
theorem B1730003 : Blo 1729065 1730003 := bstep (se 1 (by rfl) ⟨1297502, by rfl⟩ : syracuseStep 1730003 = 2595005) B2595005
theorem B1730019 : Blo 1729065 1730019 := bstep (se 1 (by rfl) ⟨1297514, by rfl⟩ : syracuseStep 1730019 = 2595029) B2595029
theorem B1730035 : Blo 1729065 1730035 := bstep (se 1 (by rfl) ⟨1297526, by rfl⟩ : syracuseStep 1730035 = 2595053) B2595053
theorem B1730051 : Blo 1729065 1730051 := bstep (se 1 (by rfl) ⟨1297538, by rfl⟩ : syracuseStep 1730051 = 2595077) B2595077
theorem B3556867 : Blo 1729065 3556867 := bstep (se 1 (by rfl) ⟨2667650, by rfl⟩ : syracuseStep 3556867 = 5335301) B5335301
theorem B7489037 : Blo 1729065 7489037 := bstep (se 3 (by rfl) ⟨1404194, by rfl⟩ : syracuseStep 7489037 = 2808389) B2808389
theorem B1730067 : Blo 1729065 1730067 := bstep (se 1 (by rfl) ⟨1297550, by rfl⟩ : syracuseStep 1730067 = 2595101) B2595101
theorem B1730083 : Blo 1729065 1730083 := bstep (se 1 (by rfl) ⟨1297562, by rfl⟩ : syracuseStep 1730083 = 2595125) B2595125
theorem B2917937 : Blo 1729065 2917937 := bstep (se 2 (by rfl) ⟨1094226, by rfl⟩ : syracuseStep 2917937 = 2188453) B2188453
theorem B1730099 : Blo 1729065 1730099 := bstep (se 1 (by rfl) ⟨1297574, by rfl⟩ : syracuseStep 1730099 = 2595149) B2595149
theorem B2770499 : Blo 1729065 2770499 := bstep (se 1 (by rfl) ⟨2077874, by rfl⟩ : syracuseStep 2770499 = 4155749) B4155749
theorem B1730115 : Blo 1729065 1730115 := bstep (se 1 (by rfl) ⟨1297586, by rfl⟩ : syracuseStep 1730115 = 2595173) B2595173
theorem B2188883 : Blo 1729065 2188883 := bstep (se 1 (by rfl) ⟨1641662, by rfl⟩ : syracuseStep 2188883 = 3283325) B3283325
theorem B1730131 : Blo 1729065 1730131 := bstep (se 1 (by rfl) ⟨1297598, by rfl⟩ : syracuseStep 1730131 = 2595197) B2595197
theorem B1730147 : Blo 1729065 1730147 := bstep (se 1 (by rfl) ⟨1297610, by rfl⟩ : syracuseStep 1730147 = 2595221) B2595221
theorem B5260909 : Blo 1729065 5260909 := bstep (se 3 (by rfl) ⟨986420, by rfl⟩ : syracuseStep 5260909 = 1972841) B1972841
theorem B1730163 : Blo 1729065 1730163 := bstep (se 1 (by rfl) ⟨1297622, by rfl⟩ : syracuseStep 1730163 = 2595245) B2595245
theorem B1730179 : Blo 1729065 1730179 := bstep (se 1 (by rfl) ⟨1297634, by rfl⟩ : syracuseStep 1730179 = 2595269) B2595269
theorem B1730195 : Blo 1729065 1730195 := bstep (se 1 (by rfl) ⟨1297646, by rfl⟩ : syracuseStep 1730195 = 2595293) B2595293
theorem B1730211 : Blo 1729065 1730211 := bstep (se 1 (by rfl) ⟨1297658, by rfl⟩ : syracuseStep 1730211 = 2595317) B2595317
theorem B2918065 : Blo 1729065 2918065 := bstep (se 2 (by rfl) ⟨1094274, by rfl⟩ : syracuseStep 2918065 = 2188549) B2188549
theorem B3892913 : Blo 1729065 3892913 := bstep (se 2 (by rfl) ⟨1459842, by rfl⟩ : syracuseStep 3892913 = 2919685) B2919685
theorem B1730227 : Blo 1729065 1730227 := bstep (se 1 (by rfl) ⟨1297670, by rfl⟩ : syracuseStep 1730227 = 2595341) B2595341
theorem B3892931 : Blo 1729065 3892931 := bstep (se 1 (by rfl) ⟨2919698, by rfl⟩ : syracuseStep 3892931 = 5839397) B5839397
theorem B1730243 : Blo 1729065 1730243 := bstep (se 1 (by rfl) ⟨1297682, by rfl⟩ : syracuseStep 1730243 = 2595365) B2595365
theorem B2918099 : Blo 1729065 2918099 := bstep (se 1 (by rfl) ⟨2188574, by rfl⟩ : syracuseStep 2918099 = 4377149) B4377149
theorem B1730259 : Blo 1729065 1730259 := bstep (se 1 (by rfl) ⟨1297694, by rfl⟩ : syracuseStep 1730259 = 2595389) B2595389
theorem B42075875 : Blo 1729065 42075875 := bstep (se 1 (by rfl) ⟨31556906, by rfl⟩ : syracuseStep 42075875 = 63113813) B63113813
theorem B1730275 : Blo 1729065 1730275 := bstep (se 1 (by rfl) ⟨1297706, by rfl⟩ : syracuseStep 1730275 = 2595413) B2595413
theorem B1730291 : Blo 1729065 1730291 := bstep (se 1 (by rfl) ⟨1297718, by rfl⟩ : syracuseStep 1730291 = 2595437) B2595437
theorem B1730307 : Blo 1729065 1730307 := bstep (se 1 (by rfl) ⟨1297730, by rfl⟩ : syracuseStep 1730307 = 2595461) B2595461
theorem B1730323 : Blo 1729065 1730323 := bstep (se 1 (by rfl) ⟨1297742, by rfl⟩ : syracuseStep 1730323 = 2595485) B2595485
theorem B1730339 : Blo 1729065 1730339 := bstep (se 1 (by rfl) ⟨1297754, by rfl⟩ : syracuseStep 1730339 = 2595509) B2595509
theorem B1730355 : Blo 1729065 1730355 := bstep (se 1 (by rfl) ⟨1297766, by rfl⟩ : syracuseStep 1730355 = 2595533) B2595533
theorem B1730371 : Blo 1729065 1730371 := bstep (se 1 (by rfl) ⟨1297778, by rfl⟩ : syracuseStep 1730371 = 2595557) B2595557
theorem B4925261 : Blo 1729065 4925261 := bstep (se 3 (by rfl) ⟨923486, by rfl⟩ : syracuseStep 4925261 = 1846973) B1846973
theorem B2918227 : Blo 1729065 2918227 := bstep (se 1 (by rfl) ⟨2188670, by rfl⟩ : syracuseStep 2918227 = 4377341) B4377341
theorem B1730387 : Blo 1729065 1730387 := bstep (se 1 (by rfl) ⟨1297790, by rfl⟩ : syracuseStep 1730387 = 2595581) B2595581
theorem B2770787 : Blo 1729065 2770787 := bstep (se 1 (by rfl) ⟨2078090, by rfl⟩ : syracuseStep 2770787 = 4156181) B4156181
theorem B1730403 : Blo 1729065 1730403 := bstep (se 1 (by rfl) ⟨1297802, by rfl⟩ : syracuseStep 1730403 = 2595605) B2595605
theorem B1730419 : Blo 1729065 1730419 := bstep (se 1 (by rfl) ⟨1297814, by rfl⟩ : syracuseStep 1730419 = 2595629) B2595629
theorem B1730435 : Blo 1729065 1730435 := bstep (se 1 (by rfl) ⟨1297826, by rfl⟩ : syracuseStep 1730435 = 2595653) B2595653
theorem B1730451 : Blo 1729065 1730451 := bstep (se 1 (by rfl) ⟨1297838, by rfl⟩ : syracuseStep 1730451 = 2595677) B2595677
theorem B7890851 : Blo 1729065 7890851 := bstep (se 1 (by rfl) ⟨5918138, by rfl⟩ : syracuseStep 7890851 = 11836277) B11836277
theorem B1730467 : Blo 1729065 1730467 := bstep (se 1 (by rfl) ⟨1297850, by rfl⟩ : syracuseStep 1730467 = 2595701) B2595701
theorem B1730483 : Blo 1729065 1730483 := bstep (se 1 (by rfl) ⟨1297862, by rfl⟩ : syracuseStep 1730483 = 2595725) B2595725
theorem B1730499 : Blo 1729065 1730499 := bstep (se 1 (by rfl) ⟨1297874, by rfl⟩ : syracuseStep 1730499 = 2595749) B2595749
theorem B8316877 : Blo 1729065 8316877 := bstep (se 3 (by rfl) ⟨1559414, by rfl⟩ : syracuseStep 8316877 = 3118829) B3118829
theorem B3893201 : Blo 1729065 3893201 := bstep (se 2 (by rfl) ⟨1459950, by rfl⟩ : syracuseStep 3893201 = 2919901) B2919901
theorem B1730515 : Blo 1729065 1730515 := bstep (se 1 (by rfl) ⟨1297886, by rfl⟩ : syracuseStep 1730515 = 2595773) B2595773
theorem B2918369 : Blo 1729065 2918369 := bstep (se 2 (by rfl) ⟨1094388, by rfl⟩ : syracuseStep 2918369 = 2188777) B2188777
theorem B3893219 : Blo 1729065 3893219 := bstep (se 1 (by rfl) ⟨2919914, by rfl⟩ : syracuseStep 3893219 = 5839829) B5839829
theorem B1730531 : Blo 1729065 1730531 := bstep (se 1 (by rfl) ⟨1297898, by rfl⟩ : syracuseStep 1730531 = 2595797) B2595797
theorem B1730547 : Blo 1729065 1730547 := bstep (se 1 (by rfl) ⟨1297910, by rfl⟩ : syracuseStep 1730547 = 2595821) B2595821
theorem B4925443 : Blo 1729065 4925443 := bstep (se 1 (by rfl) ⟨3694082, by rfl⟩ : syracuseStep 4925443 = 7388165) B7388165
theorem B1730563 : Blo 1729065 1730563 := bstep (se 1 (by rfl) ⟨1297922, by rfl⟩ : syracuseStep 1730563 = 2595845) B2595845
theorem B1730579 : Blo 1729065 1730579 := bstep (se 1 (by rfl) ⟨1297934, by rfl⟩ : syracuseStep 1730579 = 2595869) B2595869
theorem B1730595 : Blo 1729065 1730595 := bstep (se 1 (by rfl) ⟨1297946, by rfl⟩ : syracuseStep 1730595 = 2595893) B2595893
theorem B1730611 : Blo 1729065 1730611 := bstep (se 1 (by rfl) ⟨1297958, by rfl⟩ : syracuseStep 1730611 = 2595917) B2595917
theorem B1730627 : Blo 1729065 1730627 := bstep (se 1 (by rfl) ⟨1297970, by rfl⟩ : syracuseStep 1730627 = 2595941) B2595941
theorem B1730643 : Blo 1729065 1730643 := bstep (se 1 (by rfl) ⟨1297982, by rfl⟩ : syracuseStep 1730643 = 2595965) B2595965
theorem B2918497 : Blo 1729065 2918497 := bstep (se 2 (by rfl) ⟨1094436, by rfl⟩ : syracuseStep 2918497 = 2188873) B2188873
theorem B1730659 : Blo 1729065 1730659 := bstep (se 1 (by rfl) ⟨1297994, by rfl⟩ : syracuseStep 1730659 = 2595989) B2595989
theorem B1730675 : Blo 1729065 1730675 := bstep (se 1 (by rfl) ⟨1298006, by rfl⟩ : syracuseStep 1730675 = 2596013) B2596013
theorem B2918531 : Blo 1729065 2918531 := bstep (se 1 (by rfl) ⟨2188898, by rfl⟩ : syracuseStep 2918531 = 4377797) B4377797
theorem B1730691 : Blo 1729065 1730691 := bstep (se 1 (by rfl) ⟨1298018, by rfl⟩ : syracuseStep 1730691 = 2596037) B2596037
theorem B14772365 : Blo 1729065 14772365 := bstep (se 3 (by rfl) ⟨2769818, by rfl⟩ : syracuseStep 14772365 = 5539637) B5539637
theorem B1730707 : Blo 1729065 1730707 := bstep (se 1 (by rfl) ⟨1298030, by rfl⟩ : syracuseStep 1730707 = 2596061) B2596061
theorem B4925603 : Blo 1729065 4925603 := bstep (se 1 (by rfl) ⟨3694202, by rfl⟩ : syracuseStep 4925603 = 7388405) B7388405
theorem B1730723 : Blo 1729065 1730723 := bstep (se 1 (by rfl) ⟨1298042, by rfl⟩ : syracuseStep 1730723 = 2596085) B2596085
theorem B1730739 : Blo 1729065 1730739 := bstep (se 1 (by rfl) ⟨1298054, by rfl⟩ : syracuseStep 1730739 = 2596109) B2596109
theorem B1730755 : Blo 1729065 1730755 := bstep (se 1 (by rfl) ⟨1298066, by rfl⟩ : syracuseStep 1730755 = 2596133) B2596133
theorem B8759501 : Blo 1729065 8759501 := bstep (se 3 (by rfl) ⟨1642406, by rfl⟩ : syracuseStep 8759501 = 3284813) B3284813
theorem B1730771 : Blo 1729065 1730771 := bstep (se 1 (by rfl) ⟨1298078, by rfl⟩ : syracuseStep 1730771 = 2596157) B2596157
theorem B1730787 : Blo 1729065 1730787 := bstep (se 1 (by rfl) ⟨1298090, by rfl⟩ : syracuseStep 1730787 = 2596181) B2596181
theorem B3893489 : Blo 1729065 3893489 := bstep (se 2 (by rfl) ⟨1460058, by rfl⟩ : syracuseStep 3893489 = 2920117) B2920117
theorem B1730803 : Blo 1729065 1730803 := bstep (se 1 (by rfl) ⟨1298102, by rfl⟩ : syracuseStep 1730803 = 2596205) B2596205
theorem B2918659 : Blo 1729065 2918659 := bstep (se 1 (by rfl) ⟨2188994, by rfl⟩ : syracuseStep 2918659 = 4377989) B4377989
theorem B3893507 : Blo 1729065 3893507 := bstep (se 1 (by rfl) ⟨2920130, by rfl⟩ : syracuseStep 3893507 = 5840261) B5840261
theorem B1730819 : Blo 1729065 1730819 := bstep (se 1 (by rfl) ⟨1298114, by rfl⟩ : syracuseStep 1730819 = 2596229) B2596229
theorem B2189587 : Blo 1729065 2189587 := bstep (se 1 (by rfl) ⟨1642190, by rfl⟩ : syracuseStep 2189587 = 3284381) B3284381
theorem B1730835 : Blo 1729065 1730835 := bstep (se 1 (by rfl) ⟨1298126, by rfl⟩ : syracuseStep 1730835 = 2596253) B2596253
theorem B1730851 : Blo 1729065 1730851 := bstep (se 1 (by rfl) ⟨1298138, by rfl⟩ : syracuseStep 1730851 = 2596277) B2596277
theorem B3508529 : Blo 1729065 3508529 := bstep (se 2 (by rfl) ⟨1315698, by rfl⟩ : syracuseStep 3508529 = 2631397) B2631397
theorem B1730867 : Blo 1729065 1730867 := bstep (se 1 (by rfl) ⟨1298150, by rfl⟩ : syracuseStep 1730867 = 2596301) B2596301
theorem B1730883 : Blo 1729065 1730883 := bstep (se 1 (by rfl) ⟨1298162, by rfl⟩ : syracuseStep 1730883 = 2596325) B2596325
theorem B13134149 : Blo 1729065 13134149 := bstep (se 4 (by rfl) ⟨1231326, by rfl⟩ : syracuseStep 13134149 = 2462653) B2462653
theorem B5540177 : Blo 1729065 5540177 := bstep (se 2 (by rfl) ⟨2077566, by rfl⟩ : syracuseStep 5540177 = 4155133) B4155133
theorem B1730899 : Blo 1729065 1730899 := bstep (se 1 (by rfl) ⟨1298174, by rfl⟩ : syracuseStep 1730899 = 2596349) B2596349
theorem B1730915 : Blo 1729065 1730915 := bstep (se 1 (by rfl) ⟨1298186, by rfl⟩ : syracuseStep 1730915 = 2596373) B2596373
theorem B2189683 : Blo 1729065 2189683 := bstep (se 1 (by rfl) ⟨1642262, by rfl⟩ : syracuseStep 2189683 = 3284525) B3284525
theorem B1730931 : Blo 1729065 1730931 := bstep (se 1 (by rfl) ⟨1298198, by rfl⟩ : syracuseStep 1730931 = 2596397) B2596397
theorem B1730947 : Blo 1729065 1730947 := bstep (se 1 (by rfl) ⟨1298210, by rfl⟩ : syracuseStep 1730947 = 2596421) B2596421
theorem B2918801 : Blo 1729065 2918801 := bstep (se 2 (by rfl) ⟨1094550, by rfl⟩ : syracuseStep 2918801 = 2189101) B2189101
theorem B1730963 : Blo 1729065 1730963 := bstep (se 1 (by rfl) ⟨1298222, by rfl⟩ : syracuseStep 1730963 = 2596445) B2596445
theorem B1730979 : Blo 1729065 1730979 := bstep (se 1 (by rfl) ⟨1298234, by rfl⟩ : syracuseStep 1730979 = 2596469) B2596469
theorem B3697073 : Blo 1729065 3697073 := bstep (se 2 (by rfl) ⟨1386402, by rfl⟩ : syracuseStep 3697073 = 2772805) B2772805
theorem B1730995 : Blo 1729065 1730995 := bstep (se 1 (by rfl) ⟨1298246, by rfl⟩ : syracuseStep 1730995 = 2596493) B2596493
theorem B1731011 : Blo 1729065 1731011 := bstep (se 1 (by rfl) ⟨1298258, by rfl⟩ : syracuseStep 1731011 = 2596517) B2596517
theorem B1731027 : Blo 1729065 1731027 := bstep (se 1 (by rfl) ⟨1298270, by rfl⟩ : syracuseStep 1731027 = 2596541) B2596541
theorem B1731043 : Blo 1729065 1731043 := bstep (se 1 (by rfl) ⟨1298282, by rfl⟩ : syracuseStep 1731043 = 2596565) B2596565
theorem B1731059 : Blo 1729065 1731059 := bstep (se 1 (by rfl) ⟨1298294, by rfl⟩ : syracuseStep 1731059 = 2596589) B2596589
theorem B2918929 : Blo 1729065 2918929 := bstep (se 2 (by rfl) ⟨1094598, by rfl⟩ : syracuseStep 2918929 = 2189197) B2189197
theorem B3893777 : Blo 1729065 3893777 := bstep (se 2 (by rfl) ⟨1460166, by rfl⟩ : syracuseStep 3893777 = 2920333) B2920333
theorem B3893795 : Blo 1729065 3893795 := bstep (se 1 (by rfl) ⟨2920346, by rfl⟩ : syracuseStep 3893795 = 5840693) B5840693
theorem B2918963 : Blo 1729065 2918963 := bstep (se 1 (by rfl) ⟨2189222, by rfl⟩ : syracuseStep 2918963 = 4378445) B4378445
theorem B2771587 : Blo 1729065 2771587 := bstep (se 1 (by rfl) ⟨2078690, by rfl⟩ : syracuseStep 2771587 = 4157381) B4157381
theorem B9857699 : Blo 1729065 9857699 := bstep (se 1 (by rfl) ⟨7393274, by rfl⟩ : syracuseStep 9857699 = 14786549) B14786549
theorem B2919091 : Blo 1729065 2919091 := bstep (se 1 (by rfl) ⟨2189318, by rfl⟩ : syracuseStep 2919091 = 4378637) B4378637
theorem B4377361 : Blo 1729065 4377361 := bstep (se 2 (by rfl) ⟨1641510, by rfl⟩ : syracuseStep 4377361 = 3283021) B3283021
theorem B2771729 : Blo 1729065 2771729 := bstep (se 2 (by rfl) ⟨1039398, by rfl⟩ : syracuseStep 2771729 = 2078797) B2078797
theorem B3001121 : Blo 1729065 3001121 := bstep (se 2 (by rfl) ⟨1125420, by rfl⟩ : syracuseStep 3001121 = 2250841) B2250841
theorem B2771761 : Blo 1729065 2771761 := bstep (se 2 (by rfl) ⟨1039410, by rfl⟩ : syracuseStep 2771761 = 2078821) B2078821
theorem B3894065 : Blo 1729065 3894065 := bstep (se 2 (by rfl) ⟨1460274, by rfl⟩ : syracuseStep 3894065 = 2920549) B2920549
theorem B2919233 : Blo 1729065 2919233 := bstep (se 2 (by rfl) ⟨1094712, by rfl⟩ : syracuseStep 2919233 = 2189425) B2189425
theorem B3894083 : Blo 1729065 3894083 := bstep (se 1 (by rfl) ⟨2920562, by rfl⟩ : syracuseStep 3894083 = 5841125) B5841125
theorem B2190179 : Blo 1729065 2190179 := bstep (se 1 (by rfl) ⟨1642634, by rfl⟩ : syracuseStep 2190179 = 3285269) B3285269
theorem B13142897 : Blo 1729065 13142897 := bstep (se 2 (by rfl) ⟨4928586, by rfl⟩ : syracuseStep 13142897 = 9857173) B9857173
theorem B2919361 : Blo 1729065 2919361 := bstep (se 2 (by rfl) ⟨1094760, by rfl⟩ : syracuseStep 2919361 = 2189521) B2189521
theorem B5835725 : Blo 1729065 5835725 := bstep (se 3 (by rfl) ⟨1094198, by rfl⟩ : syracuseStep 5835725 = 2188397) B2188397
theorem B2919395 : Blo 1729065 2919395 := bstep (se 1 (by rfl) ⟨2189546, by rfl⟩ : syracuseStep 2919395 = 4379093) B4379093
theorem B5835779 : Blo 1729065 5835779 := bstep (se 1 (by rfl) ⟨4376834, by rfl⟩ : syracuseStep 5835779 = 8753669) B8753669
theorem B4377635 : Blo 1729065 4377635 := bstep (se 1 (by rfl) ⟨3283226, by rfl⟩ : syracuseStep 4377635 = 6566453) B6566453
theorem B3894353 : Blo 1729065 3894353 := bstep (se 2 (by rfl) ⟨1460382, by rfl⟩ : syracuseStep 3894353 = 2920765) B2920765
theorem B2919523 : Blo 1729065 2919523 := bstep (se 1 (by rfl) ⟨2189642, by rfl⟩ : syracuseStep 2919523 = 4379285) B4379285
theorem B6237283 : Blo 1729065 6237283 := bstep (se 1 (by rfl) ⟨4677962, by rfl⟩ : syracuseStep 6237283 = 9355925) B9355925
theorem B3894371 : Blo 1729065 3894371 := bstep (se 1 (by rfl) ⟨2920778, by rfl⟩ : syracuseStep 3894371 = 5841557) B5841557
theorem B8318051 : Blo 1729065 8318051 := bstep (se 1 (by rfl) ⟨6238538, by rfl⟩ : syracuseStep 8318051 = 12477077) B12477077
theorem B2960563 : Blo 1729065 2960563 := bstep (se 1 (by rfl) ⟨2220422, by rfl⟩ : syracuseStep 2960563 = 4440845) B4440845
theorem B4926673 : Blo 1729065 4926673 := bstep (se 2 (by rfl) ⟨1847502, by rfl⟩ : syracuseStep 4926673 = 3695005) B3695005
theorem B4377827 : Blo 1729065 4377827 := bstep (se 1 (by rfl) ⟨3283370, by rfl⟩ : syracuseStep 4377827 = 6566741) B6566741
theorem B2919665 : Blo 1729065 2919665 := bstep (se 2 (by rfl) ⟨1094874, by rfl⟩ : syracuseStep 2919665 = 2189749) B2189749
theorem B12471565 : Blo 1729065 12471565 := bstep (se 3 (by rfl) ⟨2338418, by rfl⟩ : syracuseStep 12471565 = 4676837) B4676837
theorem B5836049 : Blo 1729065 5836049 := bstep (se 2 (by rfl) ⟨2188518, by rfl⟩ : syracuseStep 5836049 = 4377037) B4377037
theorem B3116387 : Blo 1729065 3116387 := bstep (se 1 (by rfl) ⟨2337290, by rfl⟩ : syracuseStep 3116387 = 4674581) B4674581
theorem B2919793 : Blo 1729065 2919793 := bstep (se 2 (by rfl) ⟨1094922, by rfl⟩ : syracuseStep 2919793 = 2189845) B2189845
theorem B3894641 : Blo 1729065 3894641 := bstep (se 2 (by rfl) ⟨1460490, by rfl⟩ : syracuseStep 3894641 = 2920981) B2920981
theorem B3894659 : Blo 1729065 3894659 := bstep (se 1 (by rfl) ⟨2920994, by rfl⟩ : syracuseStep 3894659 = 5841989) B5841989
theorem B22785421 : Blo 1729065 22785421 := bstep (se 3 (by rfl) ⟨4272266, by rfl⟩ : syracuseStep 22785421 = 8544533) B8544533
theorem B2919827 : Blo 1729065 2919827 := bstep (se 1 (by rfl) ⟨2189870, by rfl⟩ : syracuseStep 2919827 = 4379741) B4379741
theorem B6565283 : Blo 1729065 6565283 := bstep (se 1 (by rfl) ⟨4923962, by rfl⟩ : syracuseStep 6565283 = 9847925) B9847925
theorem B2919955 : Blo 1729065 2919955 := bstep (se 1 (by rfl) ⟨2189966, by rfl⟩ : syracuseStep 2919955 = 4379933) B4379933
theorem B1846819 : Blo 1729065 1846819 := bstep (se 1 (by rfl) ⟨1385114, by rfl⟩ : syracuseStep 1846819 = 2770229) B2770229
theorem B4157027 : Blo 1729065 4157027 := bstep (se 1 (by rfl) ⟨3117770, by rfl⟩ : syracuseStep 4157027 = 6235541) B6235541
theorem B1945219 : Blo 1729065 1945219 := bstep (se 1 (by rfl) ⟨1458914, by rfl⟩ : syracuseStep 1945219 = 2917829) B2917829
theorem B2920097 : Blo 1729065 2920097 := bstep (se 2 (by rfl) ⟨1095036, by rfl⟩ : syracuseStep 2920097 = 2190073) B2190073
theorem B2772689 : Blo 1729065 2772689 := bstep (se 2 (by rfl) ⟨1039758, by rfl⟩ : syracuseStep 2772689 = 2079517) B2079517
theorem B1945363 : Blo 1729065 1945363 := bstep (se 1 (by rfl) ⟨1459022, by rfl⟩ : syracuseStep 1945363 = 2918045) B2918045
theorem B2920225 : Blo 1729065 2920225 := bstep (se 2 (by rfl) ⟨1095084, by rfl⟩ : syracuseStep 2920225 = 2190169) B2190169
theorem B5836589 : Blo 1729065 5836589 := bstep (se 3 (by rfl) ⟨1094360, by rfl⟩ : syracuseStep 5836589 = 2188721) B2188721
theorem B2920259 : Blo 1729065 2920259 := bstep (se 1 (by rfl) ⟨2190194, by rfl⟩ : syracuseStep 2920259 = 4380389) B4380389
theorem B5836643 : Blo 1729065 5836643 := bstep (se 1 (by rfl) ⟨4377482, by rfl⟩ : syracuseStep 5836643 = 8754965) B8754965
theorem B1945507 : Blo 1729065 1945507 := bstep (se 1 (by rfl) ⟨1459130, by rfl⟩ : syracuseStep 1945507 = 2918261) B2918261
theorem B3116963 : Blo 1729065 3116963 := bstep (se 1 (by rfl) ⟨2337722, by rfl⟩ : syracuseStep 3116963 = 4675445) B4675445
theorem B2920387 : Blo 1729065 2920387 := bstep (se 1 (by rfl) ⟨2190290, by rfl⟩ : syracuseStep 2920387 = 4380581) B4380581
theorem B1871843 : Blo 1729065 1871843 := bstep (se 1 (by rfl) ⟨1403882, by rfl⟩ : syracuseStep 1871843 = 2807765) B2807765
theorem B1945651 : Blo 1729065 1945651 := bstep (se 1 (by rfl) ⟨1459238, by rfl⟩ : syracuseStep 1945651 = 2918477) B2918477
theorem B2920529 : Blo 1729065 2920529 := bstep (se 2 (by rfl) ⟨1095198, by rfl⟩ : syracuseStep 2920529 = 2190397) B2190397
theorem B5836913 : Blo 1729065 5836913 := bstep (se 2 (by rfl) ⟨2188842, by rfl⟩ : syracuseStep 5836913 = 4377685) B4377685
theorem B64016497 : Blo 1729065 64016497 := bstep (se 2 (by rfl) ⟨24006186, by rfl⟩ : syracuseStep 64016497 = 48012373) B48012373
theorem B4378769 : Blo 1729065 4378769 := bstep (se 2 (by rfl) ⟨1642038, by rfl⟩ : syracuseStep 4378769 = 3284077) B3284077
theorem B1847443 : Blo 1729065 1847443 := bstep (se 1 (by rfl) ⟨1385582, by rfl⟩ : syracuseStep 1847443 = 2771165) B2771165
theorem B2338993 : Blo 1729065 2338993 := bstep (se 2 (by rfl) ⟨877122, by rfl⟩ : syracuseStep 2338993 = 1754245) B1754245
theorem B1945795 : Blo 1729065 1945795 := bstep (se 1 (by rfl) ⟨1459346, by rfl⟩ : syracuseStep 1945795 = 2918693) B2918693
theorem B4378819 : Blo 1729065 4378819 := bstep (se 1 (by rfl) ⟨3284114, by rfl⟩ : syracuseStep 4378819 = 6568229) B6568229
theorem B2920657 : Blo 1729065 2920657 := bstep (se 2 (by rfl) ⟨1095246, by rfl⟩ : syracuseStep 2920657 = 2190493) B2190493
theorem B2920691 : Blo 1729065 2920691 := bstep (se 1 (by rfl) ⟨2190518, by rfl⟩ : syracuseStep 2920691 = 4381037) B4381037
theorem B4501763 : Blo 1729065 4501763 := bstep (se 1 (by rfl) ⟨3376322, by rfl⟩ : syracuseStep 4501763 = 6752645) B6752645
theorem B21033269 : Blo 1729065 21033269 := bstep (se 5 (by rfl) ⟨985934, by rfl⟩ : syracuseStep 21033269 = 1971869) B1971869
theorem B4378961 : Blo 1729065 4378961 := bstep (se 2 (by rfl) ⟨1642110, by rfl⟩ : syracuseStep 4378961 = 3284221) B3284221
theorem B1945939 : Blo 1729065 1945939 := bstep (se 1 (by rfl) ⟨1459454, by rfl⟩ : syracuseStep 1945939 = 2918909) B2918909
theorem B8753507 : Blo 1729065 8753507 := bstep (se 1 (by rfl) ⟨6565130, by rfl⟩ : syracuseStep 8753507 = 13130261) B13130261
theorem B5542253 : Blo 1729065 5542253 := bstep (se 3 (by rfl) ⟨1039172, by rfl⟩ : syracuseStep 5542253 = 2078345) B2078345
theorem B2920819 : Blo 1729065 2920819 := bstep (se 1 (by rfl) ⟨2190614, by rfl⟩ : syracuseStep 2920819 = 4381229) B4381229
theorem B6566285 : Blo 1729065 6566285 := bstep (se 3 (by rfl) ⟨1231178, by rfl⟩ : syracuseStep 6566285 = 2462357) B2462357
theorem B9851341 : Blo 1729065 9851341 := bstep (se 3 (by rfl) ⟨1847126, by rfl⟩ : syracuseStep 9851341 = 3694253) B3694253
theorem B4927949 : Blo 1729065 4927949 := bstep (se 3 (by rfl) ⟨923990, by rfl⟩ : syracuseStep 4927949 = 1847981) B1847981
theorem B1946083 : Blo 1729065 1946083 := bstep (se 1 (by rfl) ⟨1459562, by rfl⟩ : syracuseStep 1946083 = 2919125) B2919125
theorem B2920961 : Blo 1729065 2920961 := bstep (se 2 (by rfl) ⟨1095360, by rfl⟩ : syracuseStep 2920961 = 2190721) B2190721
theorem B2462243 : Blo 1729065 2462243 := bstep (se 1 (by rfl) ⟨1846682, by rfl⟩ : syracuseStep 2462243 = 3693365) B3693365
theorem B4993613 : Blo 1729065 4993613 := bstep (se 3 (by rfl) ⟨936302, by rfl⟩ : syracuseStep 4993613 = 1872605) B1872605
theorem B2077283 : Blo 1729065 2077283 := bstep (se 1 (by rfl) ⟨1557962, by rfl⟩ : syracuseStep 2077283 = 3115925) B3115925
theorem B1946227 : Blo 1729065 1946227 := bstep (se 1 (by rfl) ⟨1459670, by rfl⟩ : syracuseStep 1946227 = 2919341) B2919341
theorem B2921089 : Blo 1729065 2921089 := bstep (se 2 (by rfl) ⟨1095408, by rfl⟩ : syracuseStep 2921089 = 2190817) B2190817
theorem B4928131 : Blo 1729065 4928131 := bstep (se 1 (by rfl) ⟨3696098, by rfl⟩ : syracuseStep 4928131 = 7392197) B7392197
theorem B5837453 : Blo 1729065 5837453 := bstep (se 3 (by rfl) ⟨1094522, by rfl⟩ : syracuseStep 5837453 = 2189045) B2189045
theorem B2921123 : Blo 1729065 2921123 := bstep (se 1 (by rfl) ⟨2190842, by rfl⟩ : syracuseStep 2921123 = 4381685) B4381685
theorem B4928177 : Blo 1729065 4928177 := bstep (se 2 (by rfl) ⟨1848066, by rfl⟩ : syracuseStep 4928177 = 3696133) B3696133
theorem B5837507 : Blo 1729065 5837507 := bstep (se 1 (by rfl) ⟨4378130, by rfl⟩ : syracuseStep 5837507 = 8756261) B8756261
theorem B1946371 : Blo 1729065 1946371 := bstep (se 1 (by rfl) ⟨1459778, by rfl⟩ : syracuseStep 1946371 = 2919557) B2919557
theorem B2593601 : Blo 1729065 2593601 := bstep (se 2 (by rfl) ⟨972600, by rfl⟩ : syracuseStep 2593601 = 1945201) B1945201
theorem B2593619 : Blo 1729065 2593619 := bstep (se 1 (by rfl) ⟨1945214, by rfl⟩ : syracuseStep 2593619 = 3890429) B3890429
theorem B2593649 : Blo 1729065 2593649 := bstep (se 2 (by rfl) ⟨972618, by rfl⟩ : syracuseStep 2593649 = 1945237) B1945237
theorem B6746993 : Blo 1729065 6746993 := bstep (se 2 (by rfl) ⟨2530122, by rfl⟩ : syracuseStep 6746993 = 5060245) B5060245
theorem B2593667 : Blo 1729065 2593667 := bstep (se 1 (by rfl) ⟨1945250, by rfl⟩ : syracuseStep 2593667 = 3890501) B3890501
theorem B1946515 : Blo 1729065 1946515 := bstep (se 1 (by rfl) ⟨1459886, by rfl⟩ : syracuseStep 1946515 = 2919773) B2919773
theorem B2593697 : Blo 1729065 2593697 := bstep (se 2 (by rfl) ⟨972636, by rfl⟩ : syracuseStep 2593697 = 1945273) B1945273
theorem B2593715 : Blo 1729065 2593715 := bstep (se 1 (by rfl) ⟨1945286, by rfl⟩ : syracuseStep 2593715 = 3890573) B3890573
theorem B2593745 : Blo 1729065 2593745 := bstep (se 2 (by rfl) ⟨972654, by rfl⟩ : syracuseStep 2593745 = 1945309) B1945309
theorem B5837777 : Blo 1729065 5837777 := bstep (se 2 (by rfl) ⟨2189166, by rfl⟩ : syracuseStep 5837777 = 4378333) B4378333
theorem B15774691 : Blo 1729065 15774691 := bstep (se 1 (by rfl) ⟨11831018, by rfl⟩ : syracuseStep 15774691 = 23662037) B23662037
theorem B2593763 : Blo 1729065 2593763 := bstep (se 1 (by rfl) ⟨1945322, by rfl⟩ : syracuseStep 2593763 = 3890645) B3890645
theorem B2593793 : Blo 1729065 2593793 := bstep (se 2 (by rfl) ⟨972672, by rfl⟩ : syracuseStep 2593793 = 1945345) B1945345
theorem B2495491 : Blo 1729065 2495491 := bstep (se 1 (by rfl) ⟨1871618, by rfl⟩ : syracuseStep 2495491 = 3743237) B3743237
theorem B11080709 : Blo 1729065 11080709 := bstep (se 4 (by rfl) ⟨1038816, by rfl⟩ : syracuseStep 11080709 = 2077633) B2077633
theorem B2593811 : Blo 1729065 2593811 := bstep (se 1 (by rfl) ⟨1945358, by rfl⟩ : syracuseStep 2593811 = 3890717) B3890717
theorem B1946659 : Blo 1729065 1946659 := bstep (se 1 (by rfl) ⟨1459994, by rfl⟩ : syracuseStep 1946659 = 2919989) B2919989
theorem B2593841 : Blo 1729065 2593841 := bstep (se 2 (by rfl) ⟨972690, by rfl⟩ : syracuseStep 2593841 = 1945381) B1945381
theorem B8762417 : Blo 1729065 8762417 := bstep (se 2 (by rfl) ⟨3285906, by rfl⟩ : syracuseStep 8762417 = 6571813) B6571813
theorem B2593859 : Blo 1729065 2593859 := bstep (se 1 (by rfl) ⟨1945394, by rfl⟩ : syracuseStep 2593859 = 3890789) B3890789
theorem B2593889 : Blo 1729065 2593889 := bstep (se 2 (by rfl) ⟨972708, by rfl⟩ : syracuseStep 2593889 = 1945417) B1945417
theorem B2593907 : Blo 1729065 2593907 := bstep (se 1 (by rfl) ⟨1945430, by rfl⟩ : syracuseStep 2593907 = 3890861) B3890861
theorem B8754317 : Blo 1729065 8754317 := bstep (se 3 (by rfl) ⟨1641434, by rfl⟩ : syracuseStep 8754317 = 3282869) B3282869
theorem B41047181 : Blo 1729065 41047181 := bstep (se 3 (by rfl) ⟨7696346, by rfl⟩ : syracuseStep 41047181 = 15392693) B15392693
theorem B2593937 : Blo 1729065 2593937 := bstep (se 2 (by rfl) ⟨972726, by rfl⟩ : syracuseStep 2593937 = 1945453) B1945453
theorem B2462881 : Blo 1729065 2462881 := bstep (se 2 (by rfl) ⟨923580, by rfl⟩ : syracuseStep 2462881 = 1847161) B1847161
theorem B2593955 : Blo 1729065 2593955 := bstep (se 1 (by rfl) ⟨1945466, by rfl⟩ : syracuseStep 2593955 = 3890933) B3890933
theorem B4158641 : Blo 1729065 4158641 := bstep (se 2 (by rfl) ⟨1559490, by rfl⟩ : syracuseStep 4158641 = 3118981) B3118981
theorem B1946803 : Blo 1729065 1946803 := bstep (se 1 (by rfl) ⟨1460102, by rfl⟩ : syracuseStep 1946803 = 2920205) B2920205
theorem B2593985 : Blo 1729065 2593985 := bstep (se 2 (by rfl) ⟨972744, by rfl⟩ : syracuseStep 2593985 = 1945489) B1945489
theorem B2594003 : Blo 1729065 2594003 := bstep (se 1 (by rfl) ⟨1945502, by rfl⟩ : syracuseStep 2594003 = 3891005) B3891005
theorem B22172899 : Blo 1729065 22172899 := bstep (se 1 (by rfl) ⟨16629674, by rfl⟩ : syracuseStep 22172899 = 33259349) B33259349
theorem B5543149 : Blo 1729065 5543149 := bstep (se 3 (by rfl) ⟨1039340, by rfl⟩ : syracuseStep 5543149 = 2078681) B2078681
theorem B2594033 : Blo 1729065 2594033 := bstep (se 2 (by rfl) ⟨972762, by rfl⟩ : syracuseStep 2594033 = 1945525) B1945525
theorem B2594051 : Blo 1729065 2594051 := bstep (se 1 (by rfl) ⟨1945538, by rfl⟩ : syracuseStep 2594051 = 3891077) B3891077
theorem B2462995 : Blo 1729065 2462995 := bstep (se 1 (by rfl) ⟨1847246, by rfl⟩ : syracuseStep 2462995 = 3694493) B3694493
theorem B2594081 : Blo 1729065 2594081 := bstep (se 2 (by rfl) ⟨972780, by rfl⟩ : syracuseStep 2594081 = 1945561) B1945561
theorem B4379953 : Blo 1729065 4379953 := bstep (se 2 (by rfl) ⟨1642482, by rfl⟩ : syracuseStep 4379953 = 3284965) B3284965
theorem B2594099 : Blo 1729065 2594099 := bstep (se 1 (by rfl) ⟨1945574, by rfl⟩ : syracuseStep 2594099 = 3891149) B3891149
theorem B1946947 : Blo 1729065 1946947 := bstep (se 1 (by rfl) ⟨1460210, by rfl⟩ : syracuseStep 1946947 = 2920421) B2920421
theorem B2594129 : Blo 1729065 2594129 := bstep (se 2 (by rfl) ⟨972798, by rfl⟩ : syracuseStep 2594129 = 1945597) B1945597
theorem B2594147 : Blo 1729065 2594147 := bstep (se 1 (by rfl) ⟨1945610, by rfl⟩ : syracuseStep 2594147 = 3891221) B3891221
theorem B2594177 : Blo 1729065 2594177 := bstep (se 2 (by rfl) ⟨972816, by rfl⟩ : syracuseStep 2594177 = 1945633) B1945633
theorem B2594195 : Blo 1729065 2594195 := bstep (se 1 (by rfl) ⟨1945646, by rfl⟩ : syracuseStep 2594195 = 3891293) B3891293
theorem B2594225 : Blo 1729065 2594225 := bstep (se 2 (by rfl) ⟨972834, by rfl⟩ : syracuseStep 2594225 = 1945669) B1945669
theorem B2594243 : Blo 1729065 2594243 := bstep (se 1 (by rfl) ⟨1945682, by rfl⟩ : syracuseStep 2594243 = 3891365) B3891365
theorem B1947091 : Blo 1729065 1947091 := bstep (se 1 (by rfl) ⟨1460318, by rfl⟩ : syracuseStep 1947091 = 2920637) B2920637
theorem B2594273 : Blo 1729065 2594273 := bstep (se 2 (by rfl) ⟨972852, by rfl⟩ : syracuseStep 2594273 = 1945705) B1945705
theorem B5838317 : Blo 1729065 5838317 := bstep (se 3 (by rfl) ⟨1094684, by rfl⟩ : syracuseStep 5838317 = 2189369) B2189369
theorem B2594291 : Blo 1729065 2594291 := bstep (se 1 (by rfl) ⟨1945718, by rfl⟩ : syracuseStep 2594291 = 3891437) B3891437
theorem B2594321 : Blo 1729065 2594321 := bstep (se 2 (by rfl) ⟨972870, by rfl⟩ : syracuseStep 2594321 = 1945741) B1945741
theorem B2594339 : Blo 1729065 2594339 := bstep (se 1 (by rfl) ⟨1945754, by rfl⟩ : syracuseStep 2594339 = 3891509) B3891509
theorem B5838371 : Blo 1729065 5838371 := bstep (se 1 (by rfl) ⟨4378778, by rfl⟩ : syracuseStep 5838371 = 8757557) B8757557
theorem B9983537 : Blo 1729065 9983537 := bstep (se 2 (by rfl) ⟨3743826, by rfl⟩ : syracuseStep 9983537 = 7487653) B7487653
theorem B2594369 : Blo 1729065 2594369 := bstep (se 2 (by rfl) ⟨972888, by rfl⟩ : syracuseStep 2594369 = 1945777) B1945777
theorem B4380227 : Blo 1729065 4380227 := bstep (se 1 (by rfl) ⟨3285170, by rfl⟩ : syracuseStep 4380227 = 6570341) B6570341
theorem B2594387 : Blo 1729065 2594387 := bstep (se 1 (by rfl) ⟨1945790, by rfl⟩ : syracuseStep 2594387 = 3891581) B3891581
theorem B1947235 : Blo 1729065 1947235 := bstep (se 1 (by rfl) ⟨1460426, by rfl⟩ : syracuseStep 1947235 = 2920853) B2920853
theorem B2594417 : Blo 1729065 2594417 := bstep (se 2 (by rfl) ⟨972906, by rfl⟩ : syracuseStep 2594417 = 1945813) B1945813
theorem B2594435 : Blo 1729065 2594435 := bstep (se 1 (by rfl) ⟨1945826, by rfl⟩ : syracuseStep 2594435 = 3891653) B3891653
theorem B2594465 : Blo 1729065 2594465 := bstep (se 2 (by rfl) ⟨972924, by rfl⟩ : syracuseStep 2594465 = 1945849) B1945849
theorem B2594483 : Blo 1729065 2594483 := bstep (se 1 (by rfl) ⟨1945862, by rfl⟩ : syracuseStep 2594483 = 3891725) B3891725
theorem B2594513 : Blo 1729065 2594513 := bstep (se 2 (by rfl) ⟨972942, by rfl⟩ : syracuseStep 2594513 = 1945885) B1945885
theorem B2594531 : Blo 1729065 2594531 := bstep (se 1 (by rfl) ⟨1945898, by rfl⟩ : syracuseStep 2594531 = 3891797) B3891797
theorem B1947379 : Blo 1729065 1947379 := bstep (se 1 (by rfl) ⟨1460534, by rfl⟩ : syracuseStep 1947379 = 2921069) B2921069
theorem B2594561 : Blo 1729065 2594561 := bstep (se 2 (by rfl) ⟨972960, by rfl⟩ : syracuseStep 2594561 = 1945921) B1945921
theorem B4380419 : Blo 1729065 4380419 := bstep (se 1 (by rfl) ⟨3285314, by rfl⟩ : syracuseStep 4380419 = 6570629) B6570629
theorem B2594579 : Blo 1729065 2594579 := bstep (se 1 (by rfl) ⟨1945934, by rfl⟩ : syracuseStep 2594579 = 3891869) B3891869
theorem B2594609 : Blo 1729065 2594609 := bstep (se 2 (by rfl) ⟨972978, by rfl⟩ : syracuseStep 2594609 = 1945957) B1945957
theorem B5838641 : Blo 1729065 5838641 := bstep (se 2 (by rfl) ⟨2189490, by rfl⟩ : syracuseStep 5838641 = 4378981) B4378981
theorem B22484789 : Blo 1729065 22484789 := bstep (se 5 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 22484789 = 2107949) B2107949
theorem B2594627 : Blo 1729065 2594627 := bstep (se 1 (by rfl) ⟨1945970, by rfl⟩ : syracuseStep 2594627 = 3891941) B3891941
theorem B2594657 : Blo 1729065 2594657 := bstep (se 2 (by rfl) ⟨972996, by rfl⟩ : syracuseStep 2594657 = 1945993) B1945993
theorem B2594675 : Blo 1729065 2594675 := bstep (se 1 (by rfl) ⟨1946006, by rfl⟩ : syracuseStep 2594675 = 3892013) B3892013
theorem B15783821 : Blo 1729065 15783821 := bstep (se 3 (by rfl) ⟨2959466, by rfl⟩ : syracuseStep 15783821 = 5918933) B5918933
theorem B2594705 : Blo 1729065 2594705 := bstep (se 2 (by rfl) ⟨973014, by rfl⟩ : syracuseStep 2594705 = 1946029) B1946029
theorem B2594723 : Blo 1729065 2594723 := bstep (se 1 (by rfl) ⟨1946042, by rfl⟩ : syracuseStep 2594723 = 3892085) B3892085
theorem B5920685 : Blo 1729065 5920685 := bstep (se 3 (by rfl) ⟨1110128, by rfl⟩ : syracuseStep 5920685 = 2220257) B2220257
theorem B2594753 : Blo 1729065 2594753 := bstep (se 2 (by rfl) ⟨973032, by rfl⟩ : syracuseStep 2594753 = 1946065) B1946065
theorem B2594771 : Blo 1729065 2594771 := bstep (se 1 (by rfl) ⟨1946078, by rfl⟩ : syracuseStep 2594771 = 3892157) B3892157
theorem B15775715 : Blo 1729065 15775715 := bstep (se 1 (by rfl) ⟨11831786, by rfl⟩ : syracuseStep 15775715 = 23663573) B23663573
theorem B2594801 : Blo 1729065 2594801 := bstep (se 2 (by rfl) ⟨973050, by rfl⟩ : syracuseStep 2594801 = 1946101) B1946101
theorem B2594819 : Blo 1729065 2594819 := bstep (se 1 (by rfl) ⟨1946114, by rfl⟩ : syracuseStep 2594819 = 3892229) B3892229
theorem B2594849 : Blo 1729065 2594849 := bstep (se 2 (by rfl) ⟨973068, by rfl⟩ : syracuseStep 2594849 = 1946137) B1946137
theorem B2594867 : Blo 1729065 2594867 := bstep (se 1 (by rfl) ⟨1946150, by rfl⟩ : syracuseStep 2594867 = 3892301) B3892301
theorem B2594897 : Blo 1729065 2594897 := bstep (se 2 (by rfl) ⟨973086, by rfl⟩ : syracuseStep 2594897 = 1946173) B1946173
theorem B2594915 : Blo 1729065 2594915 := bstep (se 1 (by rfl) ⟨1946186, by rfl⟩ : syracuseStep 2594915 = 3892373) B3892373
theorem B5544035 : Blo 1729065 5544035 := bstep (se 1 (by rfl) ⟨4158026, by rfl⟩ : syracuseStep 5544035 = 8316053) B8316053
theorem B2594945 : Blo 1729065 2594945 := bstep (se 2 (by rfl) ⟨973104, by rfl⟩ : syracuseStep 2594945 = 1946209) B1946209
theorem B18700429 : Blo 1729065 18700429 := bstep (se 3 (by rfl) ⟨3506330, by rfl⟩ : syracuseStep 18700429 = 7012661) B7012661
theorem B2594963 : Blo 1729065 2594963 := bstep (se 1 (by rfl) ⟨1946222, by rfl⟩ : syracuseStep 2594963 = 3892445) B3892445
theorem B2594993 : Blo 1729065 2594993 := bstep (se 2 (by rfl) ⟨973122, by rfl⟩ : syracuseStep 2594993 = 1946245) B1946245
theorem B2595011 : Blo 1729065 2595011 := bstep (se 1 (by rfl) ⟨1946258, by rfl⟩ : syracuseStep 2595011 = 3892517) B3892517
theorem B4675789 : Blo 1729065 4675789 := bstep (se 3 (by rfl) ⟨876710, by rfl⟩ : syracuseStep 4675789 = 1753421) B1753421
theorem B2595041 : Blo 1729065 2595041 := bstep (se 2 (by rfl) ⟨973140, by rfl⟩ : syracuseStep 2595041 = 1946281) B1946281
theorem B2595059 : Blo 1729065 2595059 := bstep (se 1 (by rfl) ⟨1946294, by rfl⟩ : syracuseStep 2595059 = 3892589) B3892589
theorem B2595089 : Blo 1729065 2595089 := bstep (se 2 (by rfl) ⟨973158, by rfl⟩ : syracuseStep 2595089 = 1946317) B1946317
theorem B5921041 : Blo 1729065 5921041 := bstep (se 2 (by rfl) ⟨2220390, by rfl⟩ : syracuseStep 5921041 = 4440781) B4440781
theorem B2595107 : Blo 1729065 2595107 := bstep (se 1 (by rfl) ⟨1946330, by rfl⟩ : syracuseStep 2595107 = 3892661) B3892661
theorem B3283249 : Blo 1729065 3283249 := bstep (se 2 (by rfl) ⟨1231218, by rfl⟩ : syracuseStep 3283249 = 2462437) B2462437
theorem B2595137 : Blo 1729065 2595137 := bstep (se 2 (by rfl) ⟨973176, by rfl⟩ : syracuseStep 2595137 = 1946353) B1946353
theorem B5839181 : Blo 1729065 5839181 := bstep (se 3 (by rfl) ⟨1094846, by rfl⟩ : syracuseStep 5839181 = 2189693) B2189693
theorem B2595155 : Blo 1729065 2595155 := bstep (se 1 (by rfl) ⟨1946366, by rfl⟩ : syracuseStep 2595155 = 3892733) B3892733
theorem B2595185 : Blo 1729065 2595185 := bstep (se 2 (by rfl) ⟨973194, by rfl⟩ : syracuseStep 2595185 = 1946389) B1946389
theorem B2595203 : Blo 1729065 2595203 := bstep (se 1 (by rfl) ⟨1946402, by rfl⟩ : syracuseStep 2595203 = 3892805) B3892805
theorem B5839235 : Blo 1729065 5839235 := bstep (se 1 (by rfl) ⟨4379426, by rfl⟩ : syracuseStep 5839235 = 8758853) B8758853
theorem B9853325 : Blo 1729065 9853325 := bstep (se 3 (by rfl) ⟨1847498, by rfl⟩ : syracuseStep 9853325 = 3694997) B3694997
theorem B2595233 : Blo 1729065 2595233 := bstep (se 2 (by rfl) ⟨973212, by rfl⟩ : syracuseStep 2595233 = 1946425) B1946425
theorem B2595251 : Blo 1729065 2595251 := bstep (se 1 (by rfl) ⟨1946438, by rfl⟩ : syracuseStep 2595251 = 3892877) B3892877
theorem B19716533 : Blo 1729065 19716533 := bstep (se 5 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 19716533 = 1848425) B1848425
theorem B6568397 : Blo 1729065 6568397 := bstep (se 3 (by rfl) ⟨1231574, by rfl⟩ : syracuseStep 6568397 = 2463149) B2463149
theorem B3283409 : Blo 1729065 3283409 := bstep (se 2 (by rfl) ⟨1231278, by rfl⟩ : syracuseStep 3283409 = 2462557) B2462557
theorem B2595281 : Blo 1729065 2595281 := bstep (se 2 (by rfl) ⟨973230, by rfl⟩ : syracuseStep 2595281 = 1946461) B1946461
theorem B2595299 : Blo 1729065 2595299 := bstep (se 1 (by rfl) ⟨1946474, by rfl⟩ : syracuseStep 2595299 = 3892949) B3892949
theorem B2595329 : Blo 1729065 2595329 := bstep (se 2 (by rfl) ⟨973248, by rfl⟩ : syracuseStep 2595329 = 1946497) B1946497
theorem B5618179 : Blo 1729065 5618179 := bstep (se 1 (by rfl) ⟨4213634, by rfl⟩ : syracuseStep 5618179 = 8427269) B8427269
theorem B2595347 : Blo 1729065 2595347 := bstep (se 1 (by rfl) ⟨1946510, by rfl⟩ : syracuseStep 2595347 = 3893021) B3893021
theorem B2595377 : Blo 1729065 2595377 := bstep (se 2 (by rfl) ⟨973266, by rfl⟩ : syracuseStep 2595377 = 1946533) B1946533
theorem B2595395 : Blo 1729065 2595395 := bstep (se 1 (by rfl) ⟨1946546, by rfl⟩ : syracuseStep 2595395 = 3893093) B3893093
theorem B2464339 : Blo 1729065 2464339 := bstep (se 1 (by rfl) ⟨1848254, by rfl⟩ : syracuseStep 2464339 = 3696509) B3696509
theorem B2595425 : Blo 1729065 2595425 := bstep (se 2 (by rfl) ⟨973284, by rfl⟩ : syracuseStep 2595425 = 1946569) B1946569
theorem B2595443 : Blo 1729065 2595443 := bstep (se 1 (by rfl) ⟨1946582, by rfl⟩ : syracuseStep 2595443 = 3893165) B3893165
theorem B5839505 : Blo 1729065 5839505 := bstep (se 2 (by rfl) ⟨2189814, by rfl⟩ : syracuseStep 5839505 = 4379629) B4379629
theorem B2595473 : Blo 1729065 2595473 := bstep (se 2 (by rfl) ⟨973302, by rfl⟩ : syracuseStep 2595473 = 1946605) B1946605
theorem B2595491 : Blo 1729065 2595491 := bstep (se 1 (by rfl) ⟨1946618, by rfl⟩ : syracuseStep 2595491 = 3893237) B3893237
theorem B4381361 : Blo 1729065 4381361 := bstep (se 2 (by rfl) ⟨1643010, by rfl⟩ : syracuseStep 4381361 = 3286021) B3286021
theorem B2595521 : Blo 1729065 2595521 := bstep (se 2 (by rfl) ⟨973320, by rfl⟩ : syracuseStep 2595521 = 1946641) B1946641
theorem B2595539 : Blo 1729065 2595539 := bstep (se 1 (by rfl) ⟨1946654, by rfl⟩ : syracuseStep 2595539 = 3893309) B3893309
theorem B4381411 : Blo 1729065 4381411 := bstep (se 1 (by rfl) ⟨3286058, by rfl⟩ : syracuseStep 4381411 = 6572117) B6572117
theorem B2595569 : Blo 1729065 2595569 := bstep (se 2 (by rfl) ⟨973338, by rfl⟩ : syracuseStep 2595569 = 1946677) B1946677
theorem B3947249 : Blo 1729065 3947249 := bstep (se 2 (by rfl) ⟨1480218, by rfl⟩ : syracuseStep 3947249 = 2960437) B2960437
theorem B2595587 : Blo 1729065 2595587 := bstep (se 1 (by rfl) ⟨1946690, by rfl⟩ : syracuseStep 2595587 = 3893381) B3893381
theorem B2595617 : Blo 1729065 2595617 := bstep (se 2 (by rfl) ⟨973356, by rfl⟩ : syracuseStep 2595617 = 1946713) B1946713
theorem B2595635 : Blo 1729065 2595635 := bstep (se 1 (by rfl) ⟨1946726, by rfl⟩ : syracuseStep 2595635 = 3893453) B3893453
theorem B2595665 : Blo 1729065 2595665 := bstep (se 2 (by rfl) ⟨973374, by rfl⟩ : syracuseStep 2595665 = 1946749) B1946749
theorem B3283811 : Blo 1729065 3283811 := bstep (se 1 (by rfl) ⟨2462858, by rfl⟩ : syracuseStep 3283811 = 4925717) B4925717
theorem B2595683 : Blo 1729065 2595683 := bstep (se 1 (by rfl) ⟨1946762, by rfl⟩ : syracuseStep 2595683 = 3893525) B3893525
theorem B24951665 : Blo 1729065 24951665 := bstep (se 2 (by rfl) ⟨9356874, by rfl⟩ : syracuseStep 24951665 = 18713749) B18713749
theorem B4381553 : Blo 1729065 4381553 := bstep (se 2 (by rfl) ⟨1643082, by rfl⟩ : syracuseStep 4381553 = 3286165) B3286165
theorem B2595713 : Blo 1729065 2595713 := bstep (se 2 (by rfl) ⟨973392, by rfl⟩ : syracuseStep 2595713 = 1946785) B1946785
theorem B2595731 : Blo 1729065 2595731 := bstep (se 1 (by rfl) ⟨1946798, by rfl⟩ : syracuseStep 2595731 = 3893597) B3893597
theorem B7388081 : Blo 1729065 7388081 := bstep (se 2 (by rfl) ⟨2770530, by rfl⟩ : syracuseStep 7388081 = 5541061) B5541061
theorem B2595761 : Blo 1729065 2595761 := bstep (se 2 (by rfl) ⟨973410, by rfl⟩ : syracuseStep 2595761 = 1946821) B1946821
theorem B2595779 : Blo 1729065 2595779 := bstep (se 1 (by rfl) ⟨1946834, by rfl⟩ : syracuseStep 2595779 = 3893669) B3893669
theorem B2595809 : Blo 1729065 2595809 := bstep (se 2 (by rfl) ⟨973428, by rfl⟩ : syracuseStep 2595809 = 1946857) B1946857
theorem B7388131 : Blo 1729065 7388131 := bstep (se 1 (by rfl) ⟨5541098, by rfl⟩ : syracuseStep 7388131 = 11082197) B11082197
theorem B11238385 : Blo 1729065 11238385 := bstep (se 2 (by rfl) ⟨4214394, by rfl⟩ : syracuseStep 11238385 = 8428789) B8428789
theorem B2595827 : Blo 1729065 2595827 := bstep (se 1 (by rfl) ⟨1946870, by rfl⟩ : syracuseStep 2595827 = 3893741) B3893741
theorem B2595857 : Blo 1729065 2595857 := bstep (se 2 (by rfl) ⟨973446, by rfl⟩ : syracuseStep 2595857 = 1946893) B1946893
theorem B2595875 : Blo 1729065 2595875 := bstep (se 1 (by rfl) ⟨1946906, by rfl⟩ : syracuseStep 2595875 = 3893813) B3893813
theorem B2595905 : Blo 1729065 2595905 := bstep (se 2 (by rfl) ⟨973464, by rfl⟩ : syracuseStep 2595905 = 1946929) B1946929
theorem B2595923 : Blo 1729065 2595923 := bstep (se 1 (by rfl) ⟨1946942, by rfl⟩ : syracuseStep 2595923 = 3893885) B3893885
theorem B2595953 : Blo 1729065 2595953 := bstep (se 2 (by rfl) ⟨973482, by rfl⟩ : syracuseStep 2595953 = 1946965) B1946965
theorem B3554435 : Blo 1729065 3554435 := bstep (se 1 (by rfl) ⟨2665826, by rfl⟩ : syracuseStep 3554435 = 5331653) B5331653
theorem B2595971 : Blo 1729065 2595971 := bstep (se 1 (by rfl) ⟨1946978, by rfl⟩ : syracuseStep 2595971 = 3893957) B3893957
theorem B2596001 : Blo 1729065 2596001 := bstep (se 2 (by rfl) ⟨973500, by rfl⟩ : syracuseStep 2596001 = 1947001) B1947001
theorem B5840045 : Blo 1729065 5840045 := bstep (se 3 (by rfl) ⟨1095008, by rfl⟩ : syracuseStep 5840045 = 2190017) B2190017
theorem B5921969 : Blo 1729065 5921969 := bstep (se 2 (by rfl) ⟨2220738, by rfl⟩ : syracuseStep 5921969 = 4441477) B4441477
theorem B2596019 : Blo 1729065 2596019 := bstep (se 1 (by rfl) ⟨1947014, by rfl⟩ : syracuseStep 2596019 = 3894029) B3894029
theorem B2596049 : Blo 1729065 2596049 := bstep (se 2 (by rfl) ⟨973518, by rfl⟩ : syracuseStep 2596049 = 1947037) B1947037
theorem B44326115 : Blo 1729065 44326115 := bstep (se 1 (by rfl) ⟨33244586, by rfl⟩ : syracuseStep 44326115 = 66489173) B66489173
theorem B5840099 : Blo 1729065 5840099 := bstep (se 1 (by rfl) ⟨4380074, by rfl⟩ : syracuseStep 5840099 = 8760149) B8760149
theorem B2596067 : Blo 1729065 2596067 := bstep (se 1 (by rfl) ⟨1947050, by rfl⟩ : syracuseStep 2596067 = 3894101) B3894101
theorem B3693809 : Blo 1729065 3693809 := bstep (se 2 (by rfl) ⟨1385178, by rfl⟩ : syracuseStep 3693809 = 2770357) B2770357
theorem B6569201 : Blo 1729065 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B2596097 : Blo 1729065 2596097 := bstep (se 2 (by rfl) ⟨973536, by rfl⟩ : syracuseStep 2596097 = 1947073) B1947073
theorem B2596115 : Blo 1729065 2596115 := bstep (se 1 (by rfl) ⟨1947086, by rfl⟩ : syracuseStep 2596115 = 3894173) B3894173
theorem B8428835 : Blo 1729065 8428835 := bstep (se 1 (by rfl) ⟨6321626, by rfl⟩ : syracuseStep 8428835 = 12643253) B12643253
theorem B9854257 : Blo 1729065 9854257 := bstep (se 2 (by rfl) ⟨3695346, by rfl⟩ : syracuseStep 9854257 = 7390693) B7390693
theorem B2596145 : Blo 1729065 2596145 := bstep (se 2 (by rfl) ⟨973554, by rfl⟩ : syracuseStep 2596145 = 1947109) B1947109
theorem B2596163 : Blo 1729065 2596163 := bstep (se 1 (by rfl) ⟨1947122, by rfl⟩ : syracuseStep 2596163 = 3894245) B3894245
theorem B11091269 : Blo 1729065 11091269 := bstep (se 4 (by rfl) ⟨1039806, by rfl⟩ : syracuseStep 11091269 = 2079613) B2079613
theorem B2596193 : Blo 1729065 2596193 := bstep (se 2 (by rfl) ⟨973572, by rfl⟩ : syracuseStep 2596193 = 1947145) B1947145
theorem B2596211 : Blo 1729065 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B2596241 : Blo 1729065 2596241 := bstep (se 2 (by rfl) ⟨973590, by rfl⟩ : syracuseStep 2596241 = 1947181) B1947181
theorem B6659491 : Blo 1729065 6659491 := bstep (se 1 (by rfl) ⟨4994618, by rfl⟩ : syracuseStep 6659491 = 9989237) B9989237
theorem B2596259 : Blo 1729065 2596259 := bstep (se 1 (by rfl) ⟨1947194, by rfl⟩ : syracuseStep 2596259 = 3894389) B3894389
theorem B3890609 : Blo 1729065 3890609 := bstep (se 2 (by rfl) ⟨1458978, by rfl⟩ : syracuseStep 3890609 = 2917957) B2917957
theorem B2596289 : Blo 1729065 2596289 := bstep (se 2 (by rfl) ⟨973608, by rfl⟩ : syracuseStep 2596289 = 1947217) B1947217
theorem B3890627 : Blo 1729065 3890627 := bstep (se 1 (by rfl) ⟨2917970, by rfl⟩ : syracuseStep 3890627 = 5835941) B5835941
theorem B2596307 : Blo 1729065 2596307 := bstep (se 1 (by rfl) ⟨1947230, by rfl⟩ : syracuseStep 2596307 = 3894461) B3894461
theorem B5840369 : Blo 1729065 5840369 := bstep (se 2 (by rfl) ⟨2190138, by rfl⟩ : syracuseStep 5840369 = 4380277) B4380277
theorem B2596337 : Blo 1729065 2596337 := bstep (se 2 (by rfl) ⟨973626, by rfl⟩ : syracuseStep 2596337 = 1947253) B1947253
theorem B2596355 : Blo 1729065 2596355 := bstep (se 1 (by rfl) ⟨1947266, by rfl⟩ : syracuseStep 2596355 = 3894533) B3894533
theorem B2596385 : Blo 1729065 2596385 := bstep (se 2 (by rfl) ⟨973644, by rfl⟩ : syracuseStep 2596385 = 1947289) B1947289
theorem B2596403 : Blo 1729065 2596403 := bstep (se 1 (by rfl) ⟨1947302, by rfl⟩ : syracuseStep 2596403 = 3894605) B3894605
theorem B2596433 : Blo 1729065 2596433 := bstep (se 2 (by rfl) ⟨973662, by rfl⟩ : syracuseStep 2596433 = 1947325) B1947325
theorem B4562531 : Blo 1729065 4562531 := bstep (se 1 (by rfl) ⟨3421898, by rfl⟩ : syracuseStep 4562531 = 6843797) B6843797
theorem B2596451 : Blo 1729065 2596451 := bstep (se 1 (by rfl) ⟨1947338, by rfl⟩ : syracuseStep 2596451 = 3894677) B3894677
theorem B2596481 : Blo 1729065 2596481 := bstep (se 2 (by rfl) ⟨973680, by rfl⟩ : syracuseStep 2596481 = 1947361) B1947361
theorem B2596499 : Blo 1729065 2596499 := bstep (se 1 (by rfl) ⟨1947374, by rfl⟩ : syracuseStep 2596499 = 3894749) B3894749
theorem B2596529 : Blo 1729065 2596529 := bstep (se 2 (by rfl) ⟨973698, by rfl⟩ : syracuseStep 2596529 = 1947397) B1947397
theorem B2596547 : Blo 1729065 2596547 := bstep (se 1 (by rfl) ⟨1947410, by rfl⟩ : syracuseStep 2596547 = 3894821) B3894821
theorem B3890897 : Blo 1729065 3890897 := bstep (se 2 (by rfl) ⟨1459086, by rfl⟩ : syracuseStep 3890897 = 2918173) B2918173
theorem B2596577 : Blo 1729065 2596577 := bstep (se 2 (by rfl) ⟨973716, by rfl⟩ : syracuseStep 2596577 = 1947433) B1947433
theorem B3890915 : Blo 1729065 3890915 := bstep (se 1 (by rfl) ⟨2918186, by rfl⟩ : syracuseStep 3890915 = 5836373) B5836373
theorem B3284707 : Blo 1729065 3284707 := bstep (se 1 (by rfl) ⟨2463530, by rfl⟩ : syracuseStep 3284707 = 4927061) B4927061
theorem B8314609 : Blo 1729065 8314609 := bstep (se 2 (by rfl) ⟨3117978, by rfl⟩ : syracuseStep 8314609 = 6235957) B6235957
theorem B2596595 : Blo 1729065 2596595 := bstep (se 1 (by rfl) ⟨1947446, by rfl⟩ : syracuseStep 2596595 = 3894893) B3894893
theorem B3694339 : Blo 1729065 3694339 := bstep (se 1 (by rfl) ⟨2770754, by rfl⟩ : syracuseStep 3694339 = 5541509) B5541509
theorem B4677443 : Blo 1729065 4677443 := bstep (se 1 (by rfl) ⟨3508082, by rfl⟩ : syracuseStep 4677443 = 7016165) B7016165
theorem B3284867 : Blo 1729065 3284867 := bstep (se 1 (by rfl) ⟨2463650, by rfl⟩ : syracuseStep 3284867 = 4927301) B4927301
theorem B6569869 : Blo 1729065 6569869 := bstep (se 3 (by rfl) ⟨1231850, by rfl⟩ : syracuseStep 6569869 = 2463701) B2463701
theorem B1752979 : Blo 1729065 1752979 := bstep (se 1 (by rfl) ⟨1314734, by rfl⟩ : syracuseStep 1752979 = 2629469) B2629469
theorem B3891185 : Blo 1729065 3891185 := bstep (se 2 (by rfl) ⟨1459194, by rfl⟩ : syracuseStep 3891185 = 2918389) B2918389
theorem B8757233 : Blo 1729065 8757233 := bstep (se 2 (by rfl) ⟨3283962, by rfl⟩ : syracuseStep 8757233 = 6567925) B6567925
theorem B7012403 : Blo 1729065 7012403 := bstep (se 1 (by rfl) ⟨5259302, by rfl⟩ : syracuseStep 7012403 = 10518605) B10518605
theorem B3891275 : Blo 1729065 3891275 := bstep (se 1 (by rfl) ⟨2918456, by rfl⟩ : syracuseStep 3891275 = 5836913) B5836913
theorem B3891329 : Blo 1729065 3891329 := bstep (se 2 (by rfl) ⟨1459248, by rfl⟩ : syracuseStep 3891329 = 2918497) B2918497
theorem B3694835 : Blo 1729065 3694835 := bstep (se 1 (by rfl) ⟨2771126, by rfl⟩ : syracuseStep 3694835 = 5542253) B5542253
theorem B7389463 : Blo 1729065 7389463 := bstep (se 1 (by rfl) ⟨5542097, by rfl⟩ : syracuseStep 7389463 = 11084195) B11084195
theorem B3285299 : Blo 1729065 3285299 := bstep (se 1 (by rfl) ⟨2463974, by rfl⟩ : syracuseStep 3285299 = 4927949) B4927949
theorem B3891545 : Blo 1729065 3891545 := bstep (se 2 (by rfl) ⟨1459329, by rfl⟩ : syracuseStep 3891545 = 2918659) B2918659
theorem B3891635 : Blo 1729065 3891635 := bstep (se 1 (by rfl) ⟨2918726, by rfl⟩ : syracuseStep 3891635 = 5837453) B5837453
theorem B3285451 : Blo 1729065 3285451 := bstep (se 1 (by rfl) ⟨2464088, by rfl⟩ : syracuseStep 3285451 = 4928177) B4928177
theorem B3891671 : Blo 1729065 3891671 := bstep (se 1 (by rfl) ⟨2918753, by rfl⟩ : syracuseStep 3891671 = 5837507) B5837507
theorem B1729067 : Blo 1729065 1729067 := bstep (se 1 (by rfl) ⟨1296800, by rfl⟩ : syracuseStep 1729067 = 2593601) B2593601
theorem B9855533 : Blo 1729065 9855533 := bstep (se 3 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 9855533 = 3695825) B3695825
theorem B1729079 : Blo 1729065 1729079 := bstep (se 1 (by rfl) ⟨1296809, by rfl⟩ : syracuseStep 1729079 = 2593619) B2593619
theorem B1729099 : Blo 1729065 1729099 := bstep (se 1 (by rfl) ⟨1296824, by rfl⟩ : syracuseStep 1729099 = 2593649) B2593649
theorem B4497995 : Blo 1729065 4497995 := bstep (se 1 (by rfl) ⟨3373496, by rfl⟩ : syracuseStep 4497995 = 6746993) B6746993
theorem B1729111 : Blo 1729065 1729111 := bstep (se 1 (by rfl) ⟨1296833, by rfl⟩ : syracuseStep 1729111 = 2593667) B2593667
theorem B1729131 : Blo 1729065 1729131 := bstep (se 1 (by rfl) ⟨1296848, by rfl⟩ : syracuseStep 1729131 = 2593697) B2593697
theorem B1729143 : Blo 1729065 1729143 := bstep (se 1 (by rfl) ⟨1296857, by rfl⟩ : syracuseStep 1729143 = 2593715) B2593715
theorem B1729163 : Blo 1729065 1729163 := bstep (se 1 (by rfl) ⟨1296872, by rfl⟩ : syracuseStep 1729163 = 2593745) B2593745
theorem B3891851 : Blo 1729065 3891851 := bstep (se 1 (by rfl) ⟨2918888, by rfl⟩ : syracuseStep 3891851 = 5837777) B5837777
theorem B1729175 : Blo 1729065 1729175 := bstep (se 1 (by rfl) ⟨1296881, by rfl⟩ : syracuseStep 1729175 = 2593763) B2593763
theorem B1729195 : Blo 1729065 1729195 := bstep (se 1 (by rfl) ⟨1296896, by rfl⟩ : syracuseStep 1729195 = 2593793) B2593793
theorem B1729207 : Blo 1729065 1729207 := bstep (se 1 (by rfl) ⟨1296905, by rfl⟩ : syracuseStep 1729207 = 2593811) B2593811
theorem B3891905 : Blo 1729065 3891905 := bstep (se 2 (by rfl) ⟨1459464, by rfl⟩ : syracuseStep 3891905 = 2918929) B2918929
theorem B1729227 : Blo 1729065 1729227 := bstep (se 1 (by rfl) ⟨1296920, by rfl⟩ : syracuseStep 1729227 = 2593841) B2593841
theorem B5841611 : Blo 1729065 5841611 := bstep (se 1 (by rfl) ⟨4381208, by rfl⟩ : syracuseStep 5841611 = 8762417) B8762417
theorem B1729239 : Blo 1729065 1729239 := bstep (se 1 (by rfl) ⟨1296929, by rfl⟩ : syracuseStep 1729239 = 2593859) B2593859
theorem B1729259 : Blo 1729065 1729259 := bstep (se 1 (by rfl) ⟨1296944, by rfl⟩ : syracuseStep 1729259 = 2593889) B2593889
theorem B1729271 : Blo 1729065 1729271 := bstep (se 1 (by rfl) ⟨1296953, by rfl⟩ : syracuseStep 1729271 = 2593907) B2593907
theorem B1729291 : Blo 1729065 1729291 := bstep (se 1 (by rfl) ⟨1296968, by rfl⟩ : syracuseStep 1729291 = 2593937) B2593937
theorem B1729303 : Blo 1729065 1729303 := bstep (se 1 (by rfl) ⟨1296977, by rfl⟩ : syracuseStep 1729303 = 2593955) B2593955
theorem B3285785 : Blo 1729065 3285785 := bstep (se 2 (by rfl) ⟨1232169, by rfl⟩ : syracuseStep 3285785 = 2464339) B2464339
theorem B1729323 : Blo 1729065 1729323 := bstep (se 1 (by rfl) ⟨1296992, by rfl⟩ : syracuseStep 1729323 = 2593985) B2593985
theorem B9356077 : Blo 1729065 9356077 := bstep (se 3 (by rfl) ⟨1754264, by rfl⟩ : syracuseStep 9356077 = 3508529) B3508529
theorem B1729335 : Blo 1729065 1729335 := bstep (se 1 (by rfl) ⟨1297001, by rfl⟩ : syracuseStep 1729335 = 2594003) B2594003
theorem B1729355 : Blo 1729065 1729355 := bstep (se 1 (by rfl) ⟨1297016, by rfl⟩ : syracuseStep 1729355 = 2594033) B2594033
theorem B6570827 : Blo 1729065 6570827 := bstep (se 1 (by rfl) ⟨4928120, by rfl⟩ : syracuseStep 6570827 = 9856241) B9856241
theorem B1729367 : Blo 1729065 1729367 := bstep (se 1 (by rfl) ⟨1297025, by rfl⟩ : syracuseStep 1729367 = 2594051) B2594051
theorem B6570841 : Blo 1729065 6570841 := bstep (se 2 (by rfl) ⟨2464065, by rfl⟩ : syracuseStep 6570841 = 4928131) B4928131
theorem B1729387 : Blo 1729065 1729387 := bstep (se 1 (by rfl) ⟨1297040, by rfl⟩ : syracuseStep 1729387 = 2594081) B2594081
theorem B1729399 : Blo 1729065 1729399 := bstep (se 1 (by rfl) ⟨1297049, by rfl⟩ : syracuseStep 1729399 = 2594099) B2594099
theorem B1729419 : Blo 1729065 1729419 := bstep (se 1 (by rfl) ⟨1297064, by rfl⟩ : syracuseStep 1729419 = 2594129) B2594129
theorem B1729431 : Blo 1729065 1729431 := bstep (se 1 (by rfl) ⟨1297073, by rfl⟩ : syracuseStep 1729431 = 2594147) B2594147
theorem B3892121 : Blo 1729065 3892121 := bstep (se 2 (by rfl) ⟨1459545, by rfl⟩ : syracuseStep 3892121 = 2919091) B2919091
theorem B1729451 : Blo 1729065 1729451 := bstep (se 1 (by rfl) ⟨1297088, by rfl⟩ : syracuseStep 1729451 = 2594177) B2594177
theorem B1729463 : Blo 1729065 1729463 := bstep (se 1 (by rfl) ⟨1297097, by rfl⟩ : syracuseStep 1729463 = 2594195) B2594195
theorem B1729483 : Blo 1729065 1729483 := bstep (se 1 (by rfl) ⟨1297112, by rfl⟩ : syracuseStep 1729483 = 2594225) B2594225
theorem B1729495 : Blo 1729065 1729495 := bstep (se 1 (by rfl) ⟨1297121, by rfl⟩ : syracuseStep 1729495 = 2594243) B2594243
theorem B13140953 : Blo 1729065 13140953 := bstep (se 2 (by rfl) ⟨4927857, by rfl⟩ : syracuseStep 13140953 = 9855715) B9855715
theorem B5841881 : Blo 1729065 5841881 := bstep (se 2 (by rfl) ⟨2190705, by rfl⟩ : syracuseStep 5841881 = 4381411) B4381411
theorem B1729515 : Blo 1729065 1729515 := bstep (se 1 (by rfl) ⟨1297136, by rfl⟩ : syracuseStep 1729515 = 2594273) B2594273
theorem B3892211 : Blo 1729065 3892211 := bstep (se 1 (by rfl) ⟨2919158, by rfl⟩ : syracuseStep 3892211 = 5838317) B5838317
theorem B1729527 : Blo 1729065 1729527 := bstep (se 1 (by rfl) ⟨1297145, by rfl⟩ : syracuseStep 1729527 = 2594291) B2594291
theorem B1729547 : Blo 1729065 1729547 := bstep (se 1 (by rfl) ⟨1297160, by rfl⟩ : syracuseStep 1729547 = 2594321) B2594321
theorem B1729559 : Blo 1729065 1729559 := bstep (se 1 (by rfl) ⟨1297169, by rfl⟩ : syracuseStep 1729559 = 2594339) B2594339
theorem B3892247 : Blo 1729065 3892247 := bstep (se 1 (by rfl) ⟨2919185, by rfl⟩ : syracuseStep 3892247 = 5838371) B5838371
theorem B1729579 : Blo 1729065 1729579 := bstep (se 1 (by rfl) ⟨1297184, by rfl⟩ : syracuseStep 1729579 = 2594369) B2594369
theorem B1729591 : Blo 1729065 1729591 := bstep (se 1 (by rfl) ⟨1297193, by rfl⟩ : syracuseStep 1729591 = 2594387) B2594387
theorem B3695681 : Blo 1729065 3695681 := bstep (se 2 (by rfl) ⟨1385880, by rfl⟩ : syracuseStep 3695681 = 2771761) B2771761
theorem B24937541 : Blo 1729065 24937541 := bstep (se 4 (by rfl) ⟨2337894, by rfl⟩ : syracuseStep 24937541 = 4675789) B4675789
theorem B1729611 : Blo 1729065 1729611 := bstep (se 1 (by rfl) ⟨1297208, by rfl⟩ : syracuseStep 1729611 = 2594417) B2594417
theorem B1729623 : Blo 1729065 1729623 := bstep (se 1 (by rfl) ⟨1297217, by rfl⟩ : syracuseStep 1729623 = 2594435) B2594435
theorem B1729643 : Blo 1729065 1729643 := bstep (se 1 (by rfl) ⟨1297232, by rfl⟩ : syracuseStep 1729643 = 2594465) B2594465
theorem B1729655 : Blo 1729065 1729655 := bstep (se 1 (by rfl) ⟨1297241, by rfl⟩ : syracuseStep 1729655 = 2594483) B2594483
theorem B1729675 : Blo 1729065 1729675 := bstep (se 1 (by rfl) ⟨1297256, by rfl⟩ : syracuseStep 1729675 = 2594513) B2594513
theorem B28050583 : Blo 1729065 28050583 := bstep (se 1 (by rfl) ⟨21037937, by rfl⟩ : syracuseStep 28050583 = 42075875) B42075875
theorem B1729687 : Blo 1729065 1729687 := bstep (se 1 (by rfl) ⟨1297265, by rfl⟩ : syracuseStep 1729687 = 2594531) B2594531
theorem B1729707 : Blo 1729065 1729707 := bstep (se 1 (by rfl) ⟨1297280, by rfl⟩ : syracuseStep 1729707 = 2594561) B2594561
theorem B1729719 : Blo 1729065 1729719 := bstep (se 1 (by rfl) ⟨1297289, by rfl⟩ : syracuseStep 1729719 = 2594579) B2594579
theorem B7013569 : Blo 1729065 7013569 := bstep (se 2 (by rfl) ⟨2630088, by rfl⟩ : syracuseStep 7013569 = 5260177) B5260177
theorem B1729739 : Blo 1729065 1729739 := bstep (se 1 (by rfl) ⟨1297304, by rfl⟩ : syracuseStep 1729739 = 2594609) B2594609
theorem B3892427 : Blo 1729065 3892427 := bstep (se 1 (by rfl) ⟨2919320, by rfl⟩ : syracuseStep 3892427 = 5838641) B5838641
theorem B1729751 : Blo 1729065 1729751 := bstep (se 1 (by rfl) ⟨1297313, by rfl⟩ : syracuseStep 1729751 = 2594627) B2594627
theorem B1729771 : Blo 1729065 1729771 := bstep (se 1 (by rfl) ⟨1297328, by rfl⟩ : syracuseStep 1729771 = 2594657) B2594657
theorem B1729783 : Blo 1729065 1729783 := bstep (se 1 (by rfl) ⟨1297337, by rfl⟩ : syracuseStep 1729783 = 2594675) B2594675
theorem B3892481 : Blo 1729065 3892481 := bstep (se 2 (by rfl) ⟨1459680, by rfl⟩ : syracuseStep 3892481 = 2919361) B2919361
theorem B1729803 : Blo 1729065 1729803 := bstep (se 1 (by rfl) ⟨1297352, by rfl⟩ : syracuseStep 1729803 = 2594705) B2594705
theorem B1729815 : Blo 1729065 1729815 := bstep (se 1 (by rfl) ⟨1297361, by rfl⟩ : syracuseStep 1729815 = 2594723) B2594723
theorem B5260567 : Blo 1729065 5260567 := bstep (se 1 (by rfl) ⟨3945425, by rfl⟩ : syracuseStep 5260567 = 7890851) B7890851
theorem B1729835 : Blo 1729065 1729835 := bstep (se 1 (by rfl) ⟨1297376, by rfl⟩ : syracuseStep 1729835 = 2594753) B2594753
theorem B1729847 : Blo 1729065 1729847 := bstep (se 1 (by rfl) ⟨1297385, by rfl⟩ : syracuseStep 1729847 = 2594771) B2594771
theorem B14984513 : Blo 1729065 14984513 := bstep (se 2 (by rfl) ⟨5619192, by rfl⟩ : syracuseStep 14984513 = 11238385) B11238385
theorem B1729867 : Blo 1729065 1729867 := bstep (se 1 (by rfl) ⟨1297400, by rfl⟩ : syracuseStep 1729867 = 2594801) B2594801
theorem B1729879 : Blo 1729065 1729879 := bstep (se 1 (by rfl) ⟨1297409, by rfl⟩ : syracuseStep 1729879 = 2594819) B2594819
theorem B1729899 : Blo 1729065 1729899 := bstep (se 1 (by rfl) ⟨1297424, by rfl⟩ : syracuseStep 1729899 = 2594849) B2594849
theorem B1729911 : Blo 1729065 1729911 := bstep (se 1 (by rfl) ⟨1297433, by rfl⟩ : syracuseStep 1729911 = 2594867) B2594867
theorem B1729931 : Blo 1729065 1729931 := bstep (se 1 (by rfl) ⟨1297448, by rfl⟩ : syracuseStep 1729931 = 2594897) B2594897
theorem B1729943 : Blo 1729065 1729943 := bstep (se 1 (by rfl) ⟨1297457, by rfl⟩ : syracuseStep 1729943 = 2594915) B2594915
theorem B3696023 : Blo 1729065 3696023 := bstep (se 1 (by rfl) ⟨2772017, by rfl⟩ : syracuseStep 3696023 = 5544035) B5544035
theorem B1729963 : Blo 1729065 1729963 := bstep (se 1 (by rfl) ⟨1297472, by rfl⟩ : syracuseStep 1729963 = 2594945) B2594945
theorem B9848243 : Blo 1729065 9848243 := bstep (se 1 (by rfl) ⟨7386182, by rfl⟩ : syracuseStep 9848243 = 14772365) B14772365
theorem B1729975 : Blo 1729065 1729975 := bstep (se 1 (by rfl) ⟨1297481, by rfl⟩ : syracuseStep 1729975 = 2594963) B2594963
theorem B1729995 : Blo 1729065 1729995 := bstep (se 1 (by rfl) ⟨1297496, by rfl⟩ : syracuseStep 1729995 = 2594993) B2594993
theorem B1730007 : Blo 1729065 1730007 := bstep (se 1 (by rfl) ⟨1297505, by rfl⟩ : syracuseStep 1730007 = 2595011) B2595011
theorem B2917849 : Blo 1729065 2917849 := bstep (se 2 (by rfl) ⟨1094193, by rfl⟩ : syracuseStep 2917849 = 2188387) B2188387
theorem B3892697 : Blo 1729065 3892697 := bstep (se 2 (by rfl) ⟨1459761, by rfl⟩ : syracuseStep 3892697 = 2919523) B2919523
theorem B8316377 : Blo 1729065 8316377 := bstep (se 2 (by rfl) ⟨3118641, by rfl⟩ : syracuseStep 8316377 = 6237283) B6237283
theorem B1730027 : Blo 1729065 1730027 := bstep (se 1 (by rfl) ⟨1297520, by rfl⟩ : syracuseStep 1730027 = 2595041) B2595041
theorem B1730039 : Blo 1729065 1730039 := bstep (se 1 (by rfl) ⟨1297529, by rfl⟩ : syracuseStep 1730039 = 2595059) B2595059
theorem B1730059 : Blo 1729065 1730059 := bstep (se 1 (by rfl) ⟨1297544, by rfl⟩ : syracuseStep 1730059 = 2595089) B2595089
theorem B1730071 : Blo 1729065 1730071 := bstep (se 1 (by rfl) ⟨1297553, by rfl⟩ : syracuseStep 1730071 = 2595107) B2595107
theorem B1730091 : Blo 1729065 1730091 := bstep (se 1 (by rfl) ⟨1297568, by rfl⟩ : syracuseStep 1730091 = 2595137) B2595137
theorem B3892787 : Blo 1729065 3892787 := bstep (se 1 (by rfl) ⟨2919590, by rfl⟩ : syracuseStep 3892787 = 5839181) B5839181
theorem B1730103 : Blo 1729065 1730103 := bstep (se 1 (by rfl) ⟨1297577, by rfl⟩ : syracuseStep 1730103 = 2595155) B2595155
theorem B1730123 : Blo 1729065 1730123 := bstep (se 1 (by rfl) ⟨1297592, by rfl⟩ : syracuseStep 1730123 = 2595185) B2595185
theorem B1730135 : Blo 1729065 1730135 := bstep (se 1 (by rfl) ⟨1297601, by rfl⟩ : syracuseStep 1730135 = 2595203) B2595203
theorem B3892823 : Blo 1729065 3892823 := bstep (se 1 (by rfl) ⟨2919617, by rfl⟩ : syracuseStep 3892823 = 5839235) B5839235
theorem B5539421 : Blo 1729065 5539421 := bstep (se 3 (by rfl) ⟨1038641, by rfl⟩ : syracuseStep 5539421 = 2077283) B2077283
theorem B1730155 : Blo 1729065 1730155 := bstep (se 1 (by rfl) ⟨1297616, by rfl⟩ : syracuseStep 1730155 = 2595233) B2595233
theorem B1730167 : Blo 1729065 1730167 := bstep (se 1 (by rfl) ⟨1297625, by rfl⟩ : syracuseStep 1730167 = 2595251) B2595251
theorem B2188939 : Blo 1729065 2188939 := bstep (se 1 (by rfl) ⟨1641704, by rfl⟩ : syracuseStep 2188939 = 3283409) B3283409
theorem B1730187 : Blo 1729065 1730187 := bstep (se 1 (by rfl) ⟨1297640, by rfl⟩ : syracuseStep 1730187 = 2595281) B2595281
theorem B7390865 : Blo 1729065 7390865 := bstep (se 2 (by rfl) ⟨2771574, by rfl⟩ : syracuseStep 7390865 = 5543149) B5543149
theorem B1730199 : Blo 1729065 1730199 := bstep (se 1 (by rfl) ⟨1297649, by rfl⟩ : syracuseStep 1730199 = 2595299) B2595299
theorem B1730219 : Blo 1729065 1730219 := bstep (se 1 (by rfl) ⟨1297664, by rfl⟩ : syracuseStep 1730219 = 2595329) B2595329
theorem B1730231 : Blo 1729065 1730231 := bstep (se 1 (by rfl) ⟨1297673, by rfl⟩ : syracuseStep 1730231 = 2595347) B2595347
theorem B1730251 : Blo 1729065 1730251 := bstep (se 1 (by rfl) ⟨1297688, by rfl⟩ : syracuseStep 1730251 = 2595377) B2595377
theorem B1730263 : Blo 1729065 1730263 := bstep (se 1 (by rfl) ⟨1297697, by rfl⟩ : syracuseStep 1730263 = 2595395) B2595395
theorem B1730283 : Blo 1729065 1730283 := bstep (se 1 (by rfl) ⟨1297712, by rfl⟩ : syracuseStep 1730283 = 2595425) B2595425
theorem B1730295 : Blo 1729065 1730295 := bstep (se 1 (by rfl) ⟨1297721, by rfl⟩ : syracuseStep 1730295 = 2595443) B2595443
theorem B3893003 : Blo 1729065 3893003 := bstep (se 1 (by rfl) ⟨2919752, by rfl⟩ : syracuseStep 3893003 = 5839505) B5839505
theorem B1730315 : Blo 1729065 1730315 := bstep (se 1 (by rfl) ⟨1297736, by rfl⟩ : syracuseStep 1730315 = 2595473) B2595473
theorem B1730327 : Blo 1729065 1730327 := bstep (se 1 (by rfl) ⟨1297745, by rfl⟩ : syracuseStep 1730327 = 2595491) B2595491
theorem B6571799 : Blo 1729065 6571799 := bstep (se 1 (by rfl) ⟨4928849, by rfl⟩ : syracuseStep 6571799 = 9857699) B9857699
theorem B1730347 : Blo 1729065 1730347 := bstep (se 1 (by rfl) ⟨1297760, by rfl⟩ : syracuseStep 1730347 = 2595521) B2595521
theorem B1730359 : Blo 1729065 1730359 := bstep (se 1 (by rfl) ⟨1297769, by rfl⟩ : syracuseStep 1730359 = 2595539) B2595539
theorem B3893057 : Blo 1729065 3893057 := bstep (se 2 (by rfl) ⟨1459896, by rfl⟩ : syracuseStep 3893057 = 2919793) B2919793
theorem B1730379 : Blo 1729065 1730379 := bstep (se 1 (by rfl) ⟨1297784, by rfl⟩ : syracuseStep 1730379 = 2595569) B2595569
theorem B1730391 : Blo 1729065 1730391 := bstep (se 1 (by rfl) ⟨1297793, by rfl⟩ : syracuseStep 1730391 = 2595587) B2595587
theorem B1730411 : Blo 1729065 1730411 := bstep (se 1 (by rfl) ⟨1297808, by rfl⟩ : syracuseStep 1730411 = 2595617) B2595617
theorem B2000747 : Blo 1729065 2000747 := bstep (se 1 (by rfl) ⟨1500560, by rfl⟩ : syracuseStep 2000747 = 3001121) B3001121
theorem B1730423 : Blo 1729065 1730423 := bstep (se 1 (by rfl) ⟨1297817, by rfl⟩ : syracuseStep 1730423 = 2595635) B2595635
theorem B1730443 : Blo 1729065 1730443 := bstep (se 1 (by rfl) ⟨1297832, by rfl⟩ : syracuseStep 1730443 = 2595665) B2595665
theorem B2189207 : Blo 1729065 2189207 := bstep (se 1 (by rfl) ⟨1641905, by rfl⟩ : syracuseStep 2189207 = 3283811) B3283811
theorem B1730455 : Blo 1729065 1730455 := bstep (se 1 (by rfl) ⟨1297841, by rfl⟩ : syracuseStep 1730455 = 2595683) B2595683
theorem B1730475 : Blo 1729065 1730475 := bstep (se 1 (by rfl) ⟨1297856, by rfl⟩ : syracuseStep 1730475 = 2595713) B2595713
theorem B1730487 : Blo 1729065 1730487 := bstep (se 1 (by rfl) ⟨1297865, by rfl⟩ : syracuseStep 1730487 = 2595731) B2595731
theorem B4925387 : Blo 1729065 4925387 := bstep (se 1 (by rfl) ⟨3694040, by rfl⟩ : syracuseStep 4925387 = 7388081) B7388081
theorem B1730507 : Blo 1729065 1730507 := bstep (se 1 (by rfl) ⟨1297880, by rfl⟩ : syracuseStep 1730507 = 2595761) B2595761
theorem B1730519 : Blo 1729065 1730519 := bstep (se 1 (by rfl) ⟨1297889, by rfl⟩ : syracuseStep 1730519 = 2595779) B2595779
theorem B1730539 : Blo 1729065 1730539 := bstep (se 1 (by rfl) ⟨1297904, by rfl⟩ : syracuseStep 1730539 = 2595809) B2595809
theorem B1730551 : Blo 1729065 1730551 := bstep (se 1 (by rfl) ⟨1297913, by rfl⟩ : syracuseStep 1730551 = 2595827) B2595827
theorem B1730571 : Blo 1729065 1730571 := bstep (se 1 (by rfl) ⟨1297928, by rfl⟩ : syracuseStep 1730571 = 2595857) B2595857
theorem B2918423 : Blo 1729065 2918423 := bstep (se 1 (by rfl) ⟨2188817, by rfl⟩ : syracuseStep 2918423 = 4377635) B4377635
theorem B1730583 : Blo 1729065 1730583 := bstep (se 1 (by rfl) ⟨1297937, by rfl⟩ : syracuseStep 1730583 = 2595875) B2595875
theorem B3893273 : Blo 1729065 3893273 := bstep (se 2 (by rfl) ⟨1459977, by rfl⟩ : syracuseStep 3893273 = 2919955) B2919955
theorem B1730603 : Blo 1729065 1730603 := bstep (se 1 (by rfl) ⟨1297952, by rfl⟩ : syracuseStep 1730603 = 2595905) B2595905
theorem B1730615 : Blo 1729065 1730615 := bstep (se 1 (by rfl) ⟨1297961, by rfl⟩ : syracuseStep 1730615 = 2595923) B2595923
theorem B1730635 : Blo 1729065 1730635 := bstep (se 1 (by rfl) ⟨1297976, by rfl⟩ : syracuseStep 1730635 = 2595953) B2595953
theorem B2369623 : Blo 1729065 2369623 := bstep (se 1 (by rfl) ⟨1777217, by rfl⟩ : syracuseStep 2369623 = 3554435) B3554435
theorem B1730647 : Blo 1729065 1730647 := bstep (se 1 (by rfl) ⟨1297985, by rfl⟩ : syracuseStep 1730647 = 2595971) B2595971
theorem B1730667 : Blo 1729065 1730667 := bstep (se 1 (by rfl) ⟨1298000, by rfl⟩ : syracuseStep 1730667 = 2596001) B2596001
theorem B3893363 : Blo 1729065 3893363 := bstep (se 1 (by rfl) ⟨2920022, by rfl⟩ : syracuseStep 3893363 = 5840045) B5840045
theorem B1730679 : Blo 1729065 1730679 := bstep (se 1 (by rfl) ⟨1298009, by rfl⟩ : syracuseStep 1730679 = 2596019) B2596019
theorem B1730699 : Blo 1729065 1730699 := bstep (se 1 (by rfl) ⟨1298024, by rfl⟩ : syracuseStep 1730699 = 2596049) B2596049
theorem B7014545 : Blo 1729065 7014545 := bstep (se 2 (by rfl) ⟨2630454, by rfl⟩ : syracuseStep 7014545 = 5260909) B5260909
theorem B2918551 : Blo 1729065 2918551 := bstep (se 1 (by rfl) ⟨2188913, by rfl⟩ : syracuseStep 2918551 = 4377827) B4377827
theorem B29550743 : Blo 1729065 29550743 := bstep (se 1 (by rfl) ⟨22163057, by rfl⟩ : syracuseStep 29550743 = 44326115) B44326115
theorem B3893399 : Blo 1729065 3893399 := bstep (se 1 (by rfl) ⟨2920049, by rfl⟩ : syracuseStep 3893399 = 5840099) B5840099
theorem B1730711 : Blo 1729065 1730711 := bstep (se 1 (by rfl) ⟨1298033, by rfl⟩ : syracuseStep 1730711 = 2596067) B2596067
theorem B1730731 : Blo 1729065 1730731 := bstep (se 1 (by rfl) ⟨1298048, by rfl⟩ : syracuseStep 1730731 = 2596097) B2596097
theorem B1730743 : Blo 1729065 1730743 := bstep (se 1 (by rfl) ⟨1298057, by rfl⟩ : syracuseStep 1730743 = 2596115) B2596115
theorem B1730763 : Blo 1729065 1730763 := bstep (se 1 (by rfl) ⟨1298072, by rfl⟩ : syracuseStep 1730763 = 2596145) B2596145
theorem B1730775 : Blo 1729065 1730775 := bstep (se 1 (by rfl) ⟨1298081, by rfl⟩ : syracuseStep 1730775 = 2596163) B2596163
theorem B1730795 : Blo 1729065 1730795 := bstep (se 1 (by rfl) ⟨1298096, by rfl⟩ : syracuseStep 1730795 = 2596193) B2596193
theorem B1730807 : Blo 1729065 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B1730827 : Blo 1729065 1730827 := bstep (se 1 (by rfl) ⟨1298120, by rfl⟩ : syracuseStep 1730827 = 2596241) B2596241
theorem B4376855 : Blo 1729065 4376855 := bstep (se 1 (by rfl) ⟨3282641, by rfl⟩ : syracuseStep 4376855 = 6565283) B6565283
theorem B1730839 : Blo 1729065 1730839 := bstep (se 1 (by rfl) ⟨1298129, by rfl⟩ : syracuseStep 1730839 = 2596259) B2596259
theorem B1730859 : Blo 1729065 1730859 := bstep (se 1 (by rfl) ⟨1298144, by rfl⟩ : syracuseStep 1730859 = 2596289) B2596289
theorem B1730871 : Blo 1729065 1730871 := bstep (se 1 (by rfl) ⟨1298153, by rfl⟩ : syracuseStep 1730871 = 2596307) B2596307
theorem B11086145 : Blo 1729065 11086145 := bstep (se 2 (by rfl) ⟨4157304, by rfl⟩ : syracuseStep 11086145 = 8314609) B8314609
theorem B3893579 : Blo 1729065 3893579 := bstep (se 1 (by rfl) ⟨2920184, by rfl⟩ : syracuseStep 3893579 = 5840369) B5840369
theorem B1730891 : Blo 1729065 1730891 := bstep (se 1 (by rfl) ⟨1298168, by rfl⟩ : syracuseStep 1730891 = 2596337) B2596337
theorem B1730903 : Blo 1729065 1730903 := bstep (se 1 (by rfl) ⟨1298177, by rfl⟩ : syracuseStep 1730903 = 2596355) B2596355
theorem B4925785 : Blo 1729065 4925785 := bstep (se 2 (by rfl) ⟨1847169, by rfl⟩ : syracuseStep 4925785 = 3694339) B3694339
theorem B1730923 : Blo 1729065 1730923 := bstep (se 1 (by rfl) ⟨1298192, by rfl⟩ : syracuseStep 1730923 = 2596385) B2596385
theorem B1730935 : Blo 1729065 1730935 := bstep (se 1 (by rfl) ⟨1298201, by rfl⟩ : syracuseStep 1730935 = 2596403) B2596403
theorem B3893633 : Blo 1729065 3893633 := bstep (se 2 (by rfl) ⟨1460112, by rfl⟩ : syracuseStep 3893633 = 2920225) B2920225
theorem B1730955 : Blo 1729065 1730955 := bstep (se 1 (by rfl) ⟨1298216, by rfl⟩ : syracuseStep 1730955 = 2596433) B2596433
theorem B2771351 : Blo 1729065 2771351 := bstep (se 1 (by rfl) ⟨2078513, by rfl⟩ : syracuseStep 2771351 = 4157027) B4157027
theorem B3041687 : Blo 1729065 3041687 := bstep (se 1 (by rfl) ⟨2281265, by rfl⟩ : syracuseStep 3041687 = 4562531) B4562531
theorem B1730967 : Blo 1729065 1730967 := bstep (se 1 (by rfl) ⟨1298225, by rfl⟩ : syracuseStep 1730967 = 2596451) B2596451
theorem B1730987 : Blo 1729065 1730987 := bstep (se 1 (by rfl) ⟨1298240, by rfl⟩ : syracuseStep 1730987 = 2596481) B2596481
theorem B1730999 : Blo 1729065 1730999 := bstep (se 1 (by rfl) ⟨1298249, by rfl⟩ : syracuseStep 1730999 = 2596499) B2596499
theorem B1731019 : Blo 1729065 1731019 := bstep (se 1 (by rfl) ⟨1298264, by rfl⟩ : syracuseStep 1731019 = 2596529) B2596529
theorem B1731031 : Blo 1729065 1731031 := bstep (se 1 (by rfl) ⟨1298273, by rfl⟩ : syracuseStep 1731031 = 2596547) B2596547
theorem B1731051 : Blo 1729065 1731051 := bstep (se 1 (by rfl) ⟨1298288, by rfl⟩ : syracuseStep 1731051 = 2596577) B2596577
theorem B1731063 : Blo 1729065 1731063 := bstep (se 1 (by rfl) ⟨1298297, by rfl⟩ : syracuseStep 1731063 = 2596595) B2596595
theorem B8759825 : Blo 1729065 8759825 := bstep (se 2 (by rfl) ⟨3284934, by rfl⟩ : syracuseStep 8759825 = 6569869) B6569869
theorem B2337305 : Blo 1729065 2337305 := bstep (se 2 (by rfl) ⟨876489, by rfl⟩ : syracuseStep 2337305 = 1752979) B1752979
theorem B2189911 : Blo 1729065 2189911 := bstep (se 1 (by rfl) ⟨1642433, by rfl⟩ : syracuseStep 2189911 = 3284867) B3284867
theorem B3893849 : Blo 1729065 3893849 := bstep (se 2 (by rfl) ⟨1460193, by rfl⟩ : syracuseStep 3893849 = 2920387) B2920387
theorem B4991581 : Blo 1729065 4991581 := bstep (se 3 (by rfl) ⟨935921, by rfl⟩ : syracuseStep 4991581 = 1871843) B1871843
theorem B8759987 : Blo 1729065 8759987 := bstep (se 1 (by rfl) ⟨6569990, by rfl⟩ : syracuseStep 8759987 = 13139981) B13139981
theorem B3893939 : Blo 1729065 3893939 := bstep (se 1 (by rfl) ⟨2920454, by rfl⟩ : syracuseStep 3893939 = 5840909) B5840909
theorem B3893975 : Blo 1729065 3893975 := bstep (se 1 (by rfl) ⟨2920481, by rfl⟩ : syracuseStep 3893975 = 5840963) B5840963
theorem B2919179 : Blo 1729065 2919179 := bstep (se 1 (by rfl) ⟨2189384, by rfl⟩ : syracuseStep 2919179 = 4378769) B4378769
theorem B85355329 : Blo 1729065 85355329 := bstep (se 2 (by rfl) ⟨32008248, by rfl⟩ : syracuseStep 85355329 = 64016497) B64016497
theorem B3001175 : Blo 1729065 3001175 := bstep (se 1 (by rfl) ⟨2250881, by rfl⟩ : syracuseStep 3001175 = 4501763) B4501763
theorem B9849701 : Blo 1729065 9849701 := bstep (se 4 (by rfl) ⟨923409, by rfl⟩ : syracuseStep 9849701 = 1846819) B1846819
theorem B2919307 : Blo 1729065 2919307 := bstep (se 1 (by rfl) ⟨2189480, by rfl⟩ : syracuseStep 2919307 = 4378961) B4378961
theorem B3894155 : Blo 1729065 3894155 := bstep (se 1 (by rfl) ⟨2920616, by rfl⟩ : syracuseStep 3894155 = 5841233) B5841233
theorem B5835671 : Blo 1729065 5835671 := bstep (se 1 (by rfl) ⟨4376753, by rfl⟩ : syracuseStep 5835671 = 8753507) B8753507
theorem B4377523 : Blo 1729065 4377523 := bstep (se 1 (by rfl) ⟨3283142, by rfl⟩ : syracuseStep 4377523 = 6566285) B6566285
theorem B3894209 : Blo 1729065 3894209 := bstep (se 2 (by rfl) ⟨1460328, by rfl⟩ : syracuseStep 3894209 = 2920657) B2920657
theorem B4156363 : Blo 1729065 4156363 := bstep (se 1 (by rfl) ⟨3117272, by rfl⟩ : syracuseStep 4156363 = 6234545) B6234545
theorem B4156439 : Blo 1729065 4156439 := bstep (se 1 (by rfl) ⟨3117329, by rfl⟩ : syracuseStep 4156439 = 6234659) B6234659
theorem B2919449 : Blo 1729065 2919449 := bstep (se 2 (by rfl) ⟨1094793, by rfl⟩ : syracuseStep 2919449 = 2189587) B2189587
theorem B3329075 : Blo 1729065 3329075 := bstep (se 1 (by rfl) ⟨2496806, by rfl⟩ : syracuseStep 3329075 = 4993613) B4993613
theorem B4377665 : Blo 1729065 4377665 := bstep (se 2 (by rfl) ⟨1641624, by rfl⟩ : syracuseStep 4377665 = 3283249) B3283249
theorem B2919577 : Blo 1729065 2919577 := bstep (se 2 (by rfl) ⟨1094841, by rfl⟩ : syracuseStep 2919577 = 2189683) B2189683
theorem B3894425 : Blo 1729065 3894425 := bstep (se 2 (by rfl) ⟨1460409, by rfl⟩ : syracuseStep 3894425 = 2920819) B2920819
theorem B14773427 : Blo 1729065 14773427 := bstep (se 1 (by rfl) ⟨11080070, by rfl⟩ : syracuseStep 14773427 = 22160141) B22160141
theorem B3894515 : Blo 1729065 3894515 := bstep (se 1 (by rfl) ⟨2920886, by rfl⟩ : syracuseStep 3894515 = 5841773) B5841773
theorem B13135121 : Blo 1729065 13135121 := bstep (se 2 (by rfl) ⟨4925670, by rfl⟩ : syracuseStep 13135121 = 9851341) B9851341
theorem B3894551 : Blo 1729065 3894551 := bstep (se 1 (by rfl) ⟨2920913, by rfl⟩ : syracuseStep 3894551 = 5841827) B5841827
theorem B9850157 : Blo 1729065 9850157 := bstep (se 3 (by rfl) ⟨1846904, by rfl⟩ : syracuseStep 9850157 = 3693809) B3693809
theorem B14781797 : Blo 1729065 14781797 := bstep (se 4 (by rfl) ⟨1385793, by rfl⟩ : syracuseStep 14781797 = 2771587) B2771587
theorem B3943819 : Blo 1729065 3943819 := bstep (se 1 (by rfl) ⟨2957864, by rfl⟩ : syracuseStep 3943819 = 5915729) B5915729
theorem B5836211 : Blo 1729065 5836211 := bstep (se 1 (by rfl) ⟨4377158, by rfl⟩ : syracuseStep 5836211 = 8754317) B8754317
theorem B27364787 : Blo 1729065 27364787 := bstep (se 1 (by rfl) ⟨20523590, by rfl⟩ : syracuseStep 27364787 = 41047181) B41047181
theorem B6565313 : Blo 1729065 6565313 := bstep (se 2 (by rfl) ⟨2461992, by rfl⟩ : syracuseStep 6565313 = 4923985) B4923985
theorem B3894731 : Blo 1729065 3894731 := bstep (se 1 (by rfl) ⟨2921048, by rfl⟩ : syracuseStep 3894731 = 5842097) B5842097
theorem B3894785 : Blo 1729065 3894785 := bstep (se 2 (by rfl) ⟨1460544, by rfl⟩ : syracuseStep 3894785 = 2921089) B2921089
theorem B4927027 : Blo 1729065 4927027 := bstep (se 1 (by rfl) ⟨3695270, by rfl⟩ : syracuseStep 4927027 = 7390541) B7390541
theorem B4992691 : Blo 1729065 4992691 := bstep (se 1 (by rfl) ⟨3744518, by rfl⟩ : syracuseStep 4992691 = 7489037) B7489037
theorem B5836481 : Blo 1729065 5836481 := bstep (se 2 (by rfl) ⟨2188680, by rfl⟩ : syracuseStep 5836481 = 4377361) B4377361
theorem B1945291 : Blo 1729065 1945291 := bstep (se 1 (by rfl) ⟨1458968, by rfl⟩ : syracuseStep 1945291 = 2917937) B2917937
theorem B6655691 : Blo 1729065 6655691 := bstep (se 1 (by rfl) ⟨4991768, by rfl⟩ : syracuseStep 6655691 = 9983537) B9983537
theorem B1846999 : Blo 1729065 1846999 := bstep (se 1 (by rfl) ⟨1385249, by rfl⟩ : syracuseStep 1846999 = 2770499) B2770499
theorem B2920151 : Blo 1729065 2920151 := bstep (se 1 (by rfl) ⟨2190113, by rfl⟩ : syracuseStep 2920151 = 4380227) B4380227
theorem B1945399 : Blo 1729065 1945399 := bstep (se 1 (by rfl) ⟨1459049, by rfl⟩ : syracuseStep 1945399 = 2918099) B2918099
theorem B2920279 : Blo 1729065 2920279 := bstep (se 1 (by rfl) ⟨2190209, by rfl⟩ : syracuseStep 2920279 = 4380419) B4380419
theorem B10522547 : Blo 1729065 10522547 := bstep (se 1 (by rfl) ⟨7891910, by rfl⟩ : syracuseStep 10522547 = 15783821) B15783821
theorem B21032921 : Blo 1729065 21032921 := bstep (se 2 (by rfl) ⟨7887345, by rfl⟩ : syracuseStep 21032921 = 15774691) B15774691
theorem B9850841 : Blo 1729065 9850841 := bstep (se 2 (by rfl) ⟨3694065, by rfl⟩ : syracuseStep 9850841 = 7388131) B7388131
theorem B1945579 : Blo 1729065 1945579 := bstep (se 1 (by rfl) ⟨1459184, by rfl⟩ : syracuseStep 1945579 = 2918369) B2918369
theorem B1945687 : Blo 1729065 1945687 := bstep (se 1 (by rfl) ⟨1459265, by rfl⟩ : syracuseStep 1945687 = 2918531) B2918531
theorem B6565981 : Blo 1729065 6565981 := bstep (se 3 (by rfl) ⟨1231121, by rfl⟩ : syracuseStep 6565981 = 2462243) B2462243
theorem B5837021 : Blo 1729065 5837021 := bstep (se 3 (by rfl) ⟨1094441, by rfl⟩ : syracuseStep 5837021 = 2188883) B2188883
theorem B1945867 : Blo 1729065 1945867 := bstep (se 1 (by rfl) ⟨1459400, by rfl⟩ : syracuseStep 1945867 = 2918801) B2918801
theorem B13144355 : Blo 1729065 13144355 := bstep (se 1 (by rfl) ⟨9858266, by rfl⟩ : syracuseStep 13144355 = 19716533) B19716533
theorem B4378931 : Blo 1729065 4378931 := bstep (se 1 (by rfl) ⟨3284198, by rfl⟩ : syracuseStep 4378931 = 6568397) B6568397
theorem B1945975 : Blo 1729065 1945975 := bstep (se 1 (by rfl) ⟨1459481, by rfl⟩ : syracuseStep 1945975 = 2918963) B2918963
theorem B2920907 : Blo 1729065 2920907 := bstep (se 1 (by rfl) ⟨2190680, by rfl⟩ : syracuseStep 2920907 = 4381361) B4381361
theorem B1847819 : Blo 1729065 1847819 := bstep (se 1 (by rfl) ⟨1385864, by rfl⟩ : syracuseStep 1847819 = 2771729) B2771729
theorem B30380561 : Blo 1729065 30380561 := bstep (se 2 (by rfl) ⟨11392710, by rfl⟩ : syracuseStep 30380561 = 22785421) B22785421
theorem B1946155 : Blo 1729065 1946155 := bstep (se 1 (by rfl) ⟨1459616, by rfl⟩ : syracuseStep 1946155 = 2919233) B2919233
theorem B7393837 : Blo 1729065 7393837 := bstep (se 3 (by rfl) ⟨1386344, by rfl⟩ : syracuseStep 7393837 = 2772689) B2772689
theorem B12464705 : Blo 1729065 12464705 := bstep (se 2 (by rfl) ⟨4674264, by rfl⟩ : syracuseStep 12464705 = 9348529) B9348529
theorem B8761931 : Blo 1729065 8761931 := bstep (se 1 (by rfl) ⟨6571448, by rfl⟩ : syracuseStep 8761931 = 13142897) B13142897
theorem B16634443 : Blo 1729065 16634443 := bstep (se 1 (by rfl) ⟨12475832, by rfl⟩ : syracuseStep 16634443 = 24951665) B24951665
theorem B2921035 : Blo 1729065 2921035 := bstep (se 1 (by rfl) ⟨2190776, by rfl⟩ : syracuseStep 2921035 = 4381553) B4381553
theorem B9351773 : Blo 1729065 9351773 := bstep (se 3 (by rfl) ⟨1753457, by rfl⟩ : syracuseStep 9351773 = 3506915) B3506915
theorem B1946263 : Blo 1729065 1946263 := bstep (se 1 (by rfl) ⟨1459697, by rfl⟩ : syracuseStep 1946263 = 2919395) B2919395
theorem B4379467 : Blo 1729065 4379467 := bstep (se 1 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 4379467 = 6569201) B6569201
theorem B1946443 : Blo 1729065 1946443 := bstep (se 1 (by rfl) ⟨1459832, by rfl⟩ : syracuseStep 1946443 = 2919665) B2919665
theorem B2593625 : Blo 1729065 2593625 := bstep (se 2 (by rfl) ⟨972609, by rfl⟩ : syracuseStep 2593625 = 1945219) B1945219
theorem B7394179 : Blo 1729065 7394179 := bstep (se 1 (by rfl) ⟨5545634, by rfl⟩ : syracuseStep 7394179 = 11091269) B11091269
theorem B2077591 : Blo 1729065 2077591 := bstep (se 1 (by rfl) ⟨1558193, by rfl⟩ : syracuseStep 2077591 = 3116387) B3116387
theorem B1946551 : Blo 1729065 1946551 := bstep (se 1 (by rfl) ⟨1459913, by rfl⟩ : syracuseStep 1946551 = 2919827) B2919827
theorem B2593739 : Blo 1729065 2593739 := bstep (se 1 (by rfl) ⟨1945304, by rfl⟩ : syracuseStep 2593739 = 3890609) B3890609
theorem B2593751 : Blo 1729065 2593751 := bstep (se 1 (by rfl) ⟨1945313, by rfl⟩ : syracuseStep 2593751 = 3890627) B3890627
theorem B4379609 : Blo 1729065 4379609 := bstep (se 2 (by rfl) ⟨1642353, by rfl⟩ : syracuseStep 4379609 = 3284707) B3284707
theorem B2593817 : Blo 1729065 2593817 := bstep (se 2 (by rfl) ⟨972681, by rfl⟩ : syracuseStep 2593817 = 1945363) B1945363
theorem B1946731 : Blo 1729065 1946731 := bstep (se 1 (by rfl) ⟨1460048, by rfl⟩ : syracuseStep 1946731 = 2920097) B2920097
theorem B2593931 : Blo 1729065 2593931 := bstep (se 1 (by rfl) ⟨1945448, by rfl⟩ : syracuseStep 2593931 = 3890897) B3890897
theorem B2593943 : Blo 1729065 2593943 := bstep (se 1 (by rfl) ⟨1945457, by rfl⟩ : syracuseStep 2593943 = 3890915) B3890915
theorem B3118295 : Blo 1729065 3118295 := bstep (se 1 (by rfl) ⟨2338721, by rfl⟩ : syracuseStep 3118295 = 4677443) B4677443
theorem B1946839 : Blo 1729065 1946839 := bstep (se 1 (by rfl) ⟨1460129, by rfl⟩ : syracuseStep 1946839 = 2920259) B2920259
theorem B2594009 : Blo 1729065 2594009 := bstep (se 2 (by rfl) ⟨972753, by rfl⟩ : syracuseStep 2594009 = 1945507) B1945507
theorem B11089169 : Blo 1729065 11089169 := bstep (se 2 (by rfl) ⟨4158438, by rfl⟩ : syracuseStep 11089169 = 8316877) B8316877
theorem B2077975 : Blo 1729065 2077975 := bstep (se 1 (by rfl) ⟨1558481, by rfl⟩ : syracuseStep 2077975 = 3116963) B3116963
theorem B2594123 : Blo 1729065 2594123 := bstep (se 1 (by rfl) ⟨1945592, by rfl⟩ : syracuseStep 2594123 = 3891185) B3891185
theorem B5838155 : Blo 1729065 5838155 := bstep (se 1 (by rfl) ⟨4378616, by rfl⟩ : syracuseStep 5838155 = 8757233) B8757233
theorem B2594135 : Blo 1729065 2594135 := bstep (se 1 (by rfl) ⟨1945601, by rfl⟩ : syracuseStep 2594135 = 3891203) B3891203
theorem B6567257 : Blo 1729065 6567257 := bstep (se 2 (by rfl) ⟨2462721, by rfl⟩ : syracuseStep 6567257 = 4925443) B4925443
theorem B13309285 : Blo 1729065 13309285 := bstep (se 4 (by rfl) ⟨1247745, by rfl⟩ : syracuseStep 13309285 = 2495491) B2495491
theorem B29963621 : Blo 1729065 29963621 := bstep (se 4 (by rfl) ⟨2809089, by rfl⟩ : syracuseStep 29963621 = 5618179) B5618179
theorem B1947019 : Blo 1729065 1947019 := bstep (se 1 (by rfl) ⟨1460264, by rfl⟩ : syracuseStep 1947019 = 2920529) B2920529
theorem B2594201 : Blo 1729065 2594201 := bstep (se 2 (by rfl) ⟨972825, by rfl⟩ : syracuseStep 2594201 = 1945651) B1945651
theorem B1947127 : Blo 1729065 1947127 := bstep (se 1 (by rfl) ⟨1460345, by rfl⟩ : syracuseStep 1947127 = 2920691) B2920691
theorem B2594315 : Blo 1729065 2594315 := bstep (se 1 (by rfl) ⟨1945736, by rfl⟩ : syracuseStep 2594315 = 3891473) B3891473
theorem B24933905 : Blo 1729065 24933905 := bstep (se 2 (by rfl) ⟨9350214, by rfl⟩ : syracuseStep 24933905 = 18700429) B18700429
theorem B2594327 : Blo 1729065 2594327 := bstep (se 1 (by rfl) ⟨1945745, by rfl⟩ : syracuseStep 2594327 = 3891491) B3891491
theorem B2463257 : Blo 1729065 2463257 := bstep (se 2 (by rfl) ⟨923721, by rfl⟩ : syracuseStep 2463257 = 1847443) B1847443
theorem B14022179 : Blo 1729065 14022179 := bstep (se 1 (by rfl) ⟨10516634, by rfl⟩ : syracuseStep 14022179 = 21033269) B21033269
theorem B3118657 : Blo 1729065 3118657 := bstep (se 2 (by rfl) ⟨1169496, by rfl⟩ : syracuseStep 3118657 = 2338993) B2338993
theorem B2594393 : Blo 1729065 2594393 := bstep (se 2 (by rfl) ⟨972897, by rfl⟩ : syracuseStep 2594393 = 1945795) B1945795
theorem B5838425 : Blo 1729065 5838425 := bstep (se 2 (by rfl) ⟨2189409, by rfl⟩ : syracuseStep 5838425 = 4378819) B4378819
theorem B1947307 : Blo 1729065 1947307 := bstep (se 1 (by rfl) ⟨1460480, by rfl⟩ : syracuseStep 1947307 = 2920961) B2920961
theorem B7894721 : Blo 1729065 7894721 := bstep (se 2 (by rfl) ⟨2960520, by rfl⟩ : syracuseStep 7894721 = 5921041) B5921041
theorem B2594507 : Blo 1729065 2594507 := bstep (se 1 (by rfl) ⟨1945880, by rfl⟩ : syracuseStep 2594507 = 3891761) B3891761
theorem B2594519 : Blo 1729065 2594519 := bstep (se 1 (by rfl) ⟨1945889, by rfl⟩ : syracuseStep 2594519 = 3891779) B3891779
theorem B4380439 : Blo 1729065 4380439 := bstep (se 1 (by rfl) ⟨3285329, by rfl⟩ : syracuseStep 4380439 = 6570659) B6570659
theorem B1947415 : Blo 1729065 1947415 := bstep (se 1 (by rfl) ⟨1460561, by rfl⟩ : syracuseStep 1947415 = 2921123) B2921123
theorem B2594585 : Blo 1729065 2594585 := bstep (se 2 (by rfl) ⟨972969, by rfl⟩ : syracuseStep 2594585 = 1945939) B1945939
theorem B11089709 : Blo 1729065 11089709 := bstep (se 3 (by rfl) ⟨2079320, by rfl⟩ : syracuseStep 11089709 = 4158641) B4158641
theorem B15791917 : Blo 1729065 15791917 := bstep (se 3 (by rfl) ⟨2960984, by rfl⟩ : syracuseStep 15791917 = 5921969) B5921969
theorem B3282763 : Blo 1729065 3282763 := bstep (se 1 (by rfl) ⟨2462072, by rfl⟩ : syracuseStep 3282763 = 4924145) B4924145
theorem B2594699 : Blo 1729065 2594699 := bstep (se 1 (by rfl) ⟨1946024, by rfl⟩ : syracuseStep 2594699 = 3892049) B3892049
theorem B3118987 : Blo 1729065 3118987 := bstep (se 1 (by rfl) ⟨2339240, by rfl⟩ : syracuseStep 3118987 = 4678481) B4678481
theorem B3282839 : Blo 1729065 3282839 := bstep (se 1 (by rfl) ⟨2462129, by rfl⟩ : syracuseStep 3282839 = 4924259) B4924259
theorem B2594711 : Blo 1729065 2594711 := bstep (se 1 (by rfl) ⟨1946033, by rfl⟩ : syracuseStep 2594711 = 3892067) B3892067
theorem B33249203 : Blo 1729065 33249203 := bstep (se 1 (by rfl) ⟨24936902, by rfl⟩ : syracuseStep 33249203 = 49873805) B49873805
theorem B2594777 : Blo 1729065 2594777 := bstep (se 2 (by rfl) ⟨973041, by rfl⟩ : syracuseStep 2594777 = 1946083) B1946083
theorem B7387139 : Blo 1729065 7387139 := bstep (se 1 (by rfl) ⟨5540354, by rfl⟩ : syracuseStep 7387139 = 11080709) B11080709
theorem B7018499 : Blo 1729065 7018499 := bstep (se 1 (by rfl) ⟨5263874, by rfl⟩ : syracuseStep 7018499 = 10527749) B10527749
theorem B2594891 : Blo 1729065 2594891 := bstep (se 1 (by rfl) ⟨1946168, by rfl⟩ : syracuseStep 2594891 = 3892337) B3892337
theorem B24942667 : Blo 1729065 24942667 := bstep (se 1 (by rfl) ⟨18707000, by rfl⟩ : syracuseStep 24942667 = 37414001) B37414001
theorem B2594903 : Blo 1729065 2594903 := bstep (se 1 (by rfl) ⟨1946177, by rfl⟩ : syracuseStep 2594903 = 3892355) B3892355
theorem B2463895 : Blo 1729065 2463895 := bstep (se 1 (by rfl) ⟨1847921, by rfl⟩ : syracuseStep 2463895 = 3695843) B3695843
theorem B2594969 : Blo 1729065 2594969 := bstep (se 2 (by rfl) ⟨973113, by rfl⟩ : syracuseStep 2594969 = 1946227) B1946227
theorem B4380875 : Blo 1729065 4380875 := bstep (se 1 (by rfl) ⟨3285656, by rfl⟩ : syracuseStep 4380875 = 6571313) B6571313
theorem B2595083 : Blo 1729065 2595083 := bstep (se 1 (by rfl) ⟨1946312, by rfl⟩ : syracuseStep 2595083 = 3892625) B3892625
theorem B2595095 : Blo 1729065 2595095 := bstep (se 1 (by rfl) ⟨1946321, by rfl⟩ : syracuseStep 2595095 = 3892643) B3892643
theorem B5839127 : Blo 1729065 5839127 := bstep (se 1 (by rfl) ⟨4379345, by rfl⟩ : syracuseStep 5839127 = 8758691) B8758691
theorem B2595161 : Blo 1729065 2595161 := bstep (se 2 (by rfl) ⟨973185, by rfl⟩ : syracuseStep 2595161 = 1946371) B1946371
theorem B2595275 : Blo 1729065 2595275 := bstep (se 1 (by rfl) ⟨1946456, by rfl⟩ : syracuseStep 2595275 = 3892913) B3892913
theorem B2595287 : Blo 1729065 2595287 := bstep (se 1 (by rfl) ⟨1946465, by rfl⟩ : syracuseStep 2595287 = 3892931) B3892931
theorem B2595353 : Blo 1729065 2595353 := bstep (se 2 (by rfl) ⟨973257, by rfl⟩ : syracuseStep 2595353 = 1946515) B1946515
theorem B14989859 : Blo 1729065 14989859 := bstep (se 1 (by rfl) ⟨11242394, by rfl⟩ : syracuseStep 14989859 = 22484789) B22484789
theorem B3283507 : Blo 1729065 3283507 := bstep (se 1 (by rfl) ⟨2462630, by rfl⟩ : syracuseStep 3283507 = 4925261) B4925261
theorem B4381249 : Blo 1729065 4381249 := bstep (se 2 (by rfl) ⟨1642968, by rfl⟩ : syracuseStep 4381249 = 3285937) B3285937
theorem B3947123 : Blo 1729065 3947123 := bstep (se 1 (by rfl) ⟨2960342, by rfl⟩ : syracuseStep 3947123 = 5920685) B5920685
theorem B2595467 : Blo 1729065 2595467 := bstep (se 1 (by rfl) ⟨1946600, by rfl⟩ : syracuseStep 2595467 = 3893201) B3893201
theorem B10517143 : Blo 1729065 10517143 := bstep (se 1 (by rfl) ⟨7887857, by rfl⟩ : syracuseStep 10517143 = 15775715) B15775715
theorem B2595479 : Blo 1729065 2595479 := bstep (se 1 (by rfl) ⟨1946609, by rfl⟩ : syracuseStep 2595479 = 3893219) B3893219
theorem B2595545 : Blo 1729065 2595545 := bstep (se 2 (by rfl) ⟨973329, by rfl⟩ : syracuseStep 2595545 = 1946659) B1946659
theorem B3283735 : Blo 1729065 3283735 := bstep (se 1 (by rfl) ⟨2462801, by rfl⟩ : syracuseStep 3283735 = 4925603) B4925603
theorem B5839667 : Blo 1729065 5839667 := bstep (se 1 (by rfl) ⟨4379750, by rfl⟩ : syracuseStep 5839667 = 8759501) B8759501
theorem B2595659 : Blo 1729065 2595659 := bstep (se 1 (by rfl) ⟨1946744, by rfl⟩ : syracuseStep 2595659 = 3893489) B3893489
theorem B2595671 : Blo 1729065 2595671 := bstep (se 1 (by rfl) ⟨1946753, by rfl⟩ : syracuseStep 2595671 = 3893507) B3893507
theorem B3283841 : Blo 1729065 3283841 := bstep (se 2 (by rfl) ⟨1231440, by rfl⟩ : syracuseStep 3283841 = 2462881) B2462881
theorem B8756099 : Blo 1729065 8756099 := bstep (se 1 (by rfl) ⟨6567074, by rfl⟩ : syracuseStep 8756099 = 13134149) B13134149
theorem B3693451 : Blo 1729065 3693451 := bstep (se 1 (by rfl) ⟨2770088, by rfl⟩ : syracuseStep 3693451 = 5540177) B5540177
theorem B2595737 : Blo 1729065 2595737 := bstep (se 2 (by rfl) ⟨973401, by rfl⟩ : syracuseStep 2595737 = 1946803) B1946803
theorem B3947417 : Blo 1729065 3947417 := bstep (se 2 (by rfl) ⟨1480281, by rfl⟩ : syracuseStep 3947417 = 2960563) B2960563
theorem B6568883 : Blo 1729065 6568883 := bstep (se 1 (by rfl) ⟨4926662, by rfl⟩ : syracuseStep 6568883 = 9853325) B9853325
theorem B7592897 : Blo 1729065 7592897 := bstep (se 2 (by rfl) ⟨2847336, by rfl⟩ : syracuseStep 7592897 = 5694673) B5694673
theorem B6568897 : Blo 1729065 6568897 := bstep (se 2 (by rfl) ⟨2463336, by rfl⟩ : syracuseStep 6568897 = 4926673) B4926673
theorem B2464715 : Blo 1729065 2464715 := bstep (se 1 (by rfl) ⟨1848536, by rfl⟩ : syracuseStep 2464715 = 3697073) B3697073
theorem B29563865 : Blo 1729065 29563865 := bstep (se 2 (by rfl) ⟨11086449, by rfl⟩ : syracuseStep 29563865 = 22172899) B22172899
theorem B2595851 : Blo 1729065 2595851 := bstep (se 1 (by rfl) ⟨1946888, by rfl⟩ : syracuseStep 2595851 = 3893777) B3893777
theorem B16628753 : Blo 1729065 16628753 := bstep (se 2 (by rfl) ⟨6235782, by rfl⟩ : syracuseStep 16628753 = 12471565) B12471565
theorem B2595863 : Blo 1729065 2595863 := bstep (se 1 (by rfl) ⟨1946897, by rfl⟩ : syracuseStep 2595863 = 3893795) B3893795
theorem B3283993 : Blo 1729065 3283993 := bstep (se 2 (by rfl) ⟨1231497, by rfl⟩ : syracuseStep 3283993 = 2462995) B2462995
theorem B7887917 : Blo 1729065 7887917 := bstep (se 3 (by rfl) ⟨1478984, by rfl⟩ : syracuseStep 7887917 = 2957969) B2957969
theorem B13139009 : Blo 1729065 13139009 := bstep (se 2 (by rfl) ⟨4927128, by rfl⟩ : syracuseStep 13139009 = 9854257) B9854257
theorem B5839937 : Blo 1729065 5839937 := bstep (se 2 (by rfl) ⟨2189976, by rfl⟩ : syracuseStep 5839937 = 4379953) B4379953
theorem B2595929 : Blo 1729065 2595929 := bstep (se 2 (by rfl) ⟨973473, by rfl⟩ : syracuseStep 2595929 = 1946947) B1946947
theorem B2596043 : Blo 1729065 2596043 := bstep (se 1 (by rfl) ⟨1947032, by rfl⟩ : syracuseStep 2596043 = 3894065) B3894065
theorem B2596055 : Blo 1729065 2596055 := bstep (se 1 (by rfl) ⟨1947041, by rfl⟩ : syracuseStep 2596055 = 3894083) B3894083
theorem B8879321 : Blo 1729065 8879321 := bstep (se 2 (by rfl) ⟨3329745, by rfl⟩ : syracuseStep 8879321 = 6659491) B6659491
theorem B2596121 : Blo 1729065 2596121 := bstep (se 2 (by rfl) ⟨973545, by rfl⟩ : syracuseStep 2596121 = 1947091) B1947091
theorem B10525997 : Blo 1729065 10525997 := bstep (se 3 (by rfl) ⟨1973624, by rfl⟩ : syracuseStep 10525997 = 3947249) B3947249
theorem B3890483 : Blo 1729065 3890483 := bstep (se 1 (by rfl) ⟨2917862, by rfl⟩ : syracuseStep 3890483 = 5835725) B5835725
theorem B3890519 : Blo 1729065 3890519 := bstep (se 1 (by rfl) ⟨2917889, by rfl⟩ : syracuseStep 3890519 = 5835779) B5835779
theorem B4742489 : Blo 1729065 4742489 := bstep (se 2 (by rfl) ⟨1778433, by rfl⟩ : syracuseStep 4742489 = 3556867) B3556867
theorem B2596235 : Blo 1729065 2596235 := bstep (se 1 (by rfl) ⟨1947176, by rfl⟩ : syracuseStep 2596235 = 3894353) B3894353
theorem B2596247 : Blo 1729065 2596247 := bstep (se 1 (by rfl) ⟨1947185, by rfl⟩ : syracuseStep 2596247 = 3894371) B3894371
theorem B5545367 : Blo 1729065 5545367 := bstep (se 1 (by rfl) ⟨4159025, by rfl⟩ : syracuseStep 5545367 = 8318051) B8318051
theorem B2596313 : Blo 1729065 2596313 := bstep (se 2 (by rfl) ⟨973617, by rfl⟩ : syracuseStep 2596313 = 1947235) B1947235
theorem B3890699 : Blo 1729065 3890699 := bstep (se 1 (by rfl) ⟨2918024, by rfl⟩ : syracuseStep 3890699 = 5836049) B5836049
theorem B5619223 : Blo 1729065 5619223 := bstep (se 1 (by rfl) ⟨4214417, by rfl⟩ : syracuseStep 5619223 = 8428835) B8428835
theorem B3890753 : Blo 1729065 3890753 := bstep (se 2 (by rfl) ⟨1459032, by rfl⟩ : syracuseStep 3890753 = 2918065) B2918065
theorem B2596427 : Blo 1729065 2596427 := bstep (se 1 (by rfl) ⟨1947320, by rfl⟩ : syracuseStep 2596427 = 3894641) B3894641
theorem B2596439 : Blo 1729065 2596439 := bstep (se 1 (by rfl) ⟨1947329, by rfl⟩ : syracuseStep 2596439 = 3894659) B3894659
theorem B7388765 : Blo 1729065 7388765 := bstep (se 3 (by rfl) ⟨1385393, by rfl⟩ : syracuseStep 7388765 = 2770787) B2770787
theorem B5840477 : Blo 1729065 5840477 := bstep (se 3 (by rfl) ⟨1095089, by rfl⟩ : syracuseStep 5840477 = 2190179) B2190179
theorem B2596505 : Blo 1729065 2596505 := bstep (se 2 (by rfl) ⟨973689, by rfl⟩ : syracuseStep 2596505 = 1947379) B1947379
theorem B3890969 : Blo 1729065 3890969 := bstep (se 2 (by rfl) ⟨1459113, by rfl⟩ : syracuseStep 3890969 = 2918227) B2918227
theorem B3891059 : Blo 1729065 3891059 := bstep (se 1 (by rfl) ⟨2918294, by rfl⟩ : syracuseStep 3891059 = 5836589) B5836589
theorem B3891095 : Blo 1729065 3891095 := bstep (se 1 (by rfl) ⟨2918321, by rfl⟩ : syracuseStep 3891095 = 5836643) B5836643
theorem B11083837 : Blo 1729065 11083837 := bstep (se 3 (by rfl) ⟨2078219, by rfl⟩ : syracuseStep 11083837 = 4156439) B4156439
theorem B3891347 : Blo 1729065 3891347 := bstep (se 1 (by rfl) ⟨2918510, by rfl⟩ : syracuseStep 3891347 = 5837021) B5837021
theorem B3891401 : Blo 1729065 3891401 := bstep (se 2 (by rfl) ⟨1459275, by rfl⟩ : syracuseStep 3891401 = 2918551) B2918551
theorem B3285193 : Blo 1729065 3285193 := bstep (se 2 (by rfl) ⟨1231947, by rfl⟩ : syracuseStep 3285193 = 2463895) B2463895
theorem B6570355 : Blo 1729065 6570355 := bstep (se 1 (by rfl) ⟨4927766, by rfl⟩ : syracuseStep 6570355 = 9855533) B9855533
theorem B2998663 : Blo 1729065 2998663 := bstep (se 1 (by rfl) ⟨2248997, by rfl⟩ : syracuseStep 2998663 = 4497995) B4497995
theorem B5841287 : Blo 1729065 5841287 := bstep (se 1 (by rfl) ⟨4380965, by rfl⟩ : syracuseStep 5841287 = 8761931) B8761931
theorem B6234515 : Blo 1729065 6234515 := bstep (se 1 (by rfl) ⟨4675886, by rfl⟩ : syracuseStep 6234515 = 9351773) B9351773
theorem B1729083 : Blo 1729065 1729083 := bstep (se 1 (by rfl) ⟨1296812, by rfl⟩ : syracuseStep 1729083 = 2593625) B2593625
theorem B8315453 : Blo 1729065 8315453 := bstep (se 3 (by rfl) ⟨1559147, by rfl⟩ : syracuseStep 8315453 = 3118295) B3118295
theorem B1729159 : Blo 1729065 1729159 := bstep (se 1 (by rfl) ⟨1296869, by rfl⟩ : syracuseStep 1729159 = 2593739) B2593739
theorem B1729167 : Blo 1729065 1729167 := bstep (se 1 (by rfl) ⟨1296875, by rfl⟩ : syracuseStep 1729167 = 2593751) B2593751
theorem B1729211 : Blo 1729065 1729211 := bstep (se 1 (by rfl) ⟨1296908, by rfl⟩ : syracuseStep 1729211 = 2593817) B2593817
theorem B5841665 : Blo 1729065 5841665 := bstep (se 2 (by rfl) ⟨2190624, by rfl⟩ : syracuseStep 5841665 = 4381249) B4381249
theorem B1729287 : Blo 1729065 1729287 := bstep (se 1 (by rfl) ⟨1296965, by rfl⟩ : syracuseStep 1729287 = 2593931) B2593931
theorem B1729295 : Blo 1729065 1729295 := bstep (se 1 (by rfl) ⟨1296971, by rfl⟩ : syracuseStep 1729295 = 2593943) B2593943
theorem B1729339 : Blo 1729065 1729339 := bstep (se 1 (by rfl) ⟨1297004, by rfl⟩ : syracuseStep 1729339 = 2594009) B2594009
theorem B1729415 : Blo 1729065 1729415 := bstep (se 1 (by rfl) ⟨1297061, by rfl⟩ : syracuseStep 1729415 = 2594123) B2594123
theorem B3892103 : Blo 1729065 3892103 := bstep (se 1 (by rfl) ⟨2919077, by rfl⟩ : syracuseStep 3892103 = 5838155) B5838155
theorem B1729423 : Blo 1729065 1729423 := bstep (se 1 (by rfl) ⟨1297067, by rfl⟩ : syracuseStep 1729423 = 2594135) B2594135
theorem B1729467 : Blo 1729065 1729467 := bstep (se 1 (by rfl) ⟨1297100, by rfl⟩ : syracuseStep 1729467 = 2594201) B2594201
theorem B1729543 : Blo 1729065 1729543 := bstep (se 1 (by rfl) ⟨1297157, by rfl⟩ : syracuseStep 1729543 = 2594315) B2594315
theorem B16622603 : Blo 1729065 16622603 := bstep (se 1 (by rfl) ⟨12466952, by rfl⟩ : syracuseStep 16622603 = 24933905) B24933905
theorem B1729551 : Blo 1729065 1729551 := bstep (se 1 (by rfl) ⟨1297163, by rfl⟩ : syracuseStep 1729551 = 2594327) B2594327
theorem B9348119 : Blo 1729065 9348119 := bstep (se 1 (by rfl) ⟨7011089, by rfl⟩ : syracuseStep 9348119 = 14022179) B14022179
theorem B1729595 : Blo 1729065 1729595 := bstep (se 1 (by rfl) ⟨1297196, by rfl⟩ : syracuseStep 1729595 = 2594393) B2594393
theorem B3892283 : Blo 1729065 3892283 := bstep (se 1 (by rfl) ⟨2919212, by rfl⟩ : syracuseStep 3892283 = 5838425) B5838425
theorem B1729671 : Blo 1729065 1729671 := bstep (se 1 (by rfl) ⟨1297253, by rfl⟩ : syracuseStep 1729671 = 2594507) B2594507
theorem B1729679 : Blo 1729065 1729679 := bstep (se 1 (by rfl) ⟨1297259, by rfl⟩ : syracuseStep 1729679 = 2594519) B2594519
theorem B4924601 : Blo 1729065 4924601 := bstep (se 2 (by rfl) ⟨1846725, by rfl⟩ : syracuseStep 4924601 = 3693451) B3693451
theorem B3892409 : Blo 1729065 3892409 := bstep (se 2 (by rfl) ⟨1459653, by rfl⟩ : syracuseStep 3892409 = 2919307) B2919307
theorem B1729723 : Blo 1729065 1729723 := bstep (se 1 (by rfl) ⟨1297292, by rfl⟩ : syracuseStep 1729723 = 2594585) B2594585
theorem B2770121 : Blo 1729065 2770121 := bstep (se 2 (by rfl) ⟨1038795, by rfl⟩ : syracuseStep 2770121 = 2077591) B2077591
theorem B8758529 : Blo 1729065 8758529 := bstep (se 2 (by rfl) ⟨3284448, by rfl⟩ : syracuseStep 8758529 = 6568897) B6568897
theorem B1729799 : Blo 1729065 1729799 := bstep (se 1 (by rfl) ⟨1297349, by rfl⟩ : syracuseStep 1729799 = 2594699) B2594699
theorem B2188559 : Blo 1729065 2188559 := bstep (se 1 (by rfl) ⟨1641419, by rfl⟩ : syracuseStep 2188559 = 3282839) B3282839
theorem B1729807 : Blo 1729065 1729807 := bstep (se 1 (by rfl) ⟨1297355, by rfl⟩ : syracuseStep 1729807 = 2594711) B2594711
theorem B1729851 : Blo 1729065 1729851 := bstep (se 1 (by rfl) ⟨1297388, by rfl⟩ : syracuseStep 1729851 = 2594777) B2594777
theorem B1729927 : Blo 1729065 1729927 := bstep (se 1 (by rfl) ⟨1297445, by rfl⟩ : syracuseStep 1729927 = 2594891) B2594891
theorem B1729935 : Blo 1729065 1729935 := bstep (se 1 (by rfl) ⟨1297451, by rfl⟩ : syracuseStep 1729935 = 2594903) B2594903
theorem B1729979 : Blo 1729065 1729979 := bstep (se 1 (by rfl) ⟨1297484, by rfl⟩ : syracuseStep 1729979 = 2594969) B2594969
theorem B1730055 : Blo 1729065 1730055 := bstep (se 1 (by rfl) ⟨1297541, by rfl⟩ : syracuseStep 1730055 = 2595083) B2595083
theorem B2917903 : Blo 1729065 2917903 := bstep (se 1 (by rfl) ⟨2188427, by rfl⟩ : syracuseStep 2917903 = 4376855) B4376855
theorem B1730063 : Blo 1729065 1730063 := bstep (se 1 (by rfl) ⟨1297547, by rfl⟩ : syracuseStep 1730063 = 2595095) B2595095
theorem B3892751 : Blo 1729065 3892751 := bstep (se 1 (by rfl) ⟨2919563, by rfl⟩ : syracuseStep 3892751 = 5839127) B5839127
theorem B3892769 : Blo 1729065 3892769 := bstep (se 2 (by rfl) ⟨1459788, by rfl⟩ : syracuseStep 3892769 = 2919577) B2919577
theorem B7390763 : Blo 1729065 7390763 := bstep (se 1 (by rfl) ⟨5543072, by rfl⟩ : syracuseStep 7390763 = 11086145) B11086145
theorem B1730107 : Blo 1729065 1730107 := bstep (se 1 (by rfl) ⟨1297580, by rfl⟩ : syracuseStep 1730107 = 2595161) B2595161
theorem B1730183 : Blo 1729065 1730183 := bstep (se 1 (by rfl) ⟨1297637, by rfl⟩ : syracuseStep 1730183 = 2595275) B2595275
theorem B1730191 : Blo 1729065 1730191 := bstep (se 1 (by rfl) ⟨1297643, by rfl⟩ : syracuseStep 1730191 = 2595287) B2595287
theorem B1730235 : Blo 1729065 1730235 := bstep (se 1 (by rfl) ⟨1297676, by rfl⟩ : syracuseStep 1730235 = 2595353) B2595353
theorem B2770633 : Blo 1729065 2770633 := bstep (se 2 (by rfl) ⟨1038987, by rfl⟩ : syracuseStep 2770633 = 2077975) B2077975
theorem B7014089 : Blo 1729065 7014089 := bstep (se 2 (by rfl) ⟨2630283, by rfl⟩ : syracuseStep 7014089 = 5260567) B5260567
theorem B2631415 : Blo 1729065 2631415 := bstep (se 1 (by rfl) ⟨1973561, by rfl⟩ : syracuseStep 2631415 = 3947123) B3947123
theorem B1730311 : Blo 1729065 1730311 := bstep (se 1 (by rfl) ⟨1297733, by rfl⟩ : syracuseStep 1730311 = 2595467) B2595467
theorem B1730319 : Blo 1729065 1730319 := bstep (se 1 (by rfl) ⟨1297739, by rfl⟩ : syracuseStep 1730319 = 2595479) B2595479
theorem B17745713 : Blo 1729065 17745713 := bstep (se 2 (by rfl) ⟨6654642, by rfl⟩ : syracuseStep 17745713 = 13309285) B13309285
theorem B1730363 : Blo 1729065 1730363 := bstep (se 1 (by rfl) ⟨1297772, by rfl⟩ : syracuseStep 1730363 = 2595545) B2595545
theorem B3893111 : Blo 1729065 3893111 := bstep (se 1 (by rfl) ⟨2919833, by rfl⟩ : syracuseStep 3893111 = 5839667) B5839667
theorem B1730439 : Blo 1729065 1730439 := bstep (se 1 (by rfl) ⟨1297829, by rfl⟩ : syracuseStep 1730439 = 2595659) B2595659
theorem B1730447 : Blo 1729065 1730447 := bstep (se 1 (by rfl) ⟨1297835, by rfl⟩ : syracuseStep 1730447 = 2595671) B2595671
theorem B2000783 : Blo 1729065 2000783 := bstep (se 1 (by rfl) ⟨1500587, by rfl⟩ : syracuseStep 2000783 = 3001175) B3001175
theorem B1730491 : Blo 1729065 1730491 := bstep (se 1 (by rfl) ⟨1297868, by rfl⟩ : syracuseStep 1730491 = 2595737) B2595737
theorem B2631611 : Blo 1729065 2631611 := bstep (se 1 (by rfl) ⟨1973708, by rfl⟩ : syracuseStep 2631611 = 3947417) B3947417
theorem B1730567 : Blo 1729065 1730567 := bstep (se 1 (by rfl) ⟨1297925, by rfl⟩ : syracuseStep 1730567 = 2595851) B2595851
theorem B11085835 : Blo 1729065 11085835 := bstep (se 1 (by rfl) ⟨8314376, by rfl⟩ : syracuseStep 11085835 = 16628753) B16628753
theorem B1730575 : Blo 1729065 1730575 := bstep (se 1 (by rfl) ⟨1297931, by rfl⟩ : syracuseStep 1730575 = 2595863) B2595863
theorem B2918443 : Blo 1729065 2918443 := bstep (se 1 (by rfl) ⟨2188832, by rfl⟩ : syracuseStep 2918443 = 4377665) B4377665
theorem B8759339 : Blo 1729065 8759339 := bstep (se 1 (by rfl) ⟨6569504, by rfl⟩ : syracuseStep 8759339 = 13139009) B13139009
theorem B3893291 : Blo 1729065 3893291 := bstep (se 1 (by rfl) ⟨2919968, by rfl⟩ : syracuseStep 3893291 = 5839937) B5839937
theorem B1730619 : Blo 1729065 1730619 := bstep (se 1 (by rfl) ⟨1297964, by rfl⟩ : syracuseStep 1730619 = 2595929) B2595929
theorem B9848951 : Blo 1729065 9848951 := bstep (se 1 (by rfl) ⟨7386713, by rfl⟩ : syracuseStep 9848951 = 14773427) B14773427
theorem B1730695 : Blo 1729065 1730695 := bstep (se 1 (by rfl) ⟨1298021, by rfl⟩ : syracuseStep 1730695 = 2596043) B2596043
theorem B1730703 : Blo 1729065 1730703 := bstep (se 1 (by rfl) ⟨1298027, by rfl⟩ : syracuseStep 1730703 = 2596055) B2596055
theorem B2918585 : Blo 1729065 2918585 := bstep (se 2 (by rfl) ⟨1094469, by rfl⟩ : syracuseStep 2918585 = 2188939) B2188939
theorem B1730747 : Blo 1729065 1730747 := bstep (se 1 (by rfl) ⟨1298060, by rfl⟩ : syracuseStep 1730747 = 2596121) B2596121
theorem B1730823 : Blo 1729065 1730823 := bstep (se 1 (by rfl) ⟨1298117, by rfl⟩ : syracuseStep 1730823 = 2596235) B2596235
theorem B1730831 : Blo 1729065 1730831 := bstep (se 1 (by rfl) ⟨1298123, by rfl⟩ : syracuseStep 1730831 = 2596247) B2596247
theorem B3696911 : Blo 1729065 3696911 := bstep (se 1 (by rfl) ⟨2772683, by rfl⟩ : syracuseStep 3696911 = 5545367) B5545367
theorem B5335325 : Blo 1729065 5335325 := bstep (se 3 (by rfl) ⟨1000373, by rfl⟩ : syracuseStep 5335325 = 2000747) B2000747
theorem B4376875 : Blo 1729065 4376875 := bstep (se 1 (by rfl) ⟨3282656, by rfl⟩ : syracuseStep 4376875 = 6565313) B6565313
theorem B1730875 : Blo 1729065 1730875 := bstep (se 1 (by rfl) ⟨1298156, by rfl⟩ : syracuseStep 1730875 = 2596313) B2596313
theorem B1730951 : Blo 1729065 1730951 := bstep (se 1 (by rfl) ⟨1298213, by rfl⟩ : syracuseStep 1730951 = 2596427) B2596427
theorem B1730959 : Blo 1729065 1730959 := bstep (se 1 (by rfl) ⟨1298219, by rfl⟩ : syracuseStep 1730959 = 2596439) B2596439
theorem B21055889 : Blo 1729065 21055889 := bstep (se 2 (by rfl) ⟨7895958, by rfl⟩ : syracuseStep 21055889 = 15791917) B15791917
theorem B4925843 : Blo 1729065 4925843 := bstep (se 1 (by rfl) ⟨3694382, by rfl⟩ : syracuseStep 4925843 = 7388765) B7388765
theorem B3893651 : Blo 1729065 3893651 := bstep (se 1 (by rfl) ⟨2920238, by rfl⟩ : syracuseStep 3893651 = 5840477) B5840477
theorem B4377017 : Blo 1729065 4377017 := bstep (se 2 (by rfl) ⟨1641381, by rfl⟩ : syracuseStep 4377017 = 3282763) B3282763
theorem B1731003 : Blo 1729065 1731003 := bstep (se 1 (by rfl) ⟨1298252, by rfl⟩ : syracuseStep 1731003 = 2596505) B2596505
theorem B3893705 : Blo 1729065 3893705 := bstep (se 2 (by rfl) ⟨1460139, by rfl⟩ : syracuseStep 3893705 = 2920279) B2920279
theorem B6572573 : Blo 1729065 6572573 := bstep (se 3 (by rfl) ⟨1232357, by rfl⟩ : syracuseStep 6572573 = 2464715) B2464715
theorem B7015031 : Blo 1729065 7015031 := bstep (se 1 (by rfl) ⟨5261273, by rfl⟩ : syracuseStep 7015031 = 10522547) B10522547
theorem B2919287 : Blo 1729065 2919287 := bstep (se 1 (by rfl) ⟨2189465, by rfl⟩ : syracuseStep 2919287 = 4378931) B4378931
theorem B24931253 : Blo 1729065 24931253 := bstep (se 5 (by rfl) ⟨1168652, by rfl⟩ : syracuseStep 24931253 = 2337305) B2337305
theorem B20253707 : Blo 1729065 20253707 := bstep (se 1 (by rfl) ⟨15190280, by rfl⟩ : syracuseStep 20253707 = 30380561) B30380561
theorem B8309803 : Blo 1729065 8309803 := bstep (se 1 (by rfl) ⟨6232352, by rfl⟩ : syracuseStep 8309803 = 12464705) B12464705
theorem B3894407 : Blo 1729065 3894407 := bstep (se 1 (by rfl) ⟨2920805, by rfl⟩ : syracuseStep 3894407 = 5841611) B5841611
theorem B23678189 : Blo 1729065 23678189 := bstep (se 3 (by rfl) ⟨4439660, by rfl⟩ : syracuseStep 23678189 = 8879321) B8879321
theorem B2919739 : Blo 1729065 2919739 := bstep (se 1 (by rfl) ⟨2189804, by rfl⟩ : syracuseStep 2919739 = 4379609) B4379609
theorem B8760635 : Blo 1729065 8760635 := bstep (se 1 (by rfl) ⟨6570476, by rfl⟩ : syracuseStep 8760635 = 13140953) B13140953
theorem B3894587 : Blo 1729065 3894587 := bstep (se 1 (by rfl) ⟨2920940, by rfl⟩ : syracuseStep 3894587 = 5841881) B5841881
theorem B16625027 : Blo 1729065 16625027 := bstep (se 1 (by rfl) ⟨12468770, by rfl⟩ : syracuseStep 16625027 = 24937541) B24937541
theorem B9858449 : Blo 1729065 9858449 := bstep (se 2 (by rfl) ⟨3696918, by rfl⟩ : syracuseStep 9858449 = 7393837) B7393837
theorem B4378009 : Blo 1729065 4378009 := bstep (se 2 (by rfl) ⟨1641753, by rfl⟩ : syracuseStep 4378009 = 3283507) B3283507
theorem B22179257 : Blo 1729065 22179257 := bstep (se 2 (by rfl) ⟨8317221, by rfl⟩ : syracuseStep 22179257 = 16634443) B16634443
theorem B3894713 : Blo 1729065 3894713 := bstep (se 2 (by rfl) ⟨1460517, by rfl⟩ : syracuseStep 3894713 = 2921035) B2921035
theorem B2919881 : Blo 1729065 2919881 := bstep (se 2 (by rfl) ⟨1094955, by rfl⟩ : syracuseStep 2919881 = 2189911) B2189911
theorem B28069325 : Blo 1729065 28069325 := bstep (se 3 (by rfl) ⟨5262998, by rfl⟩ : syracuseStep 28069325 = 10525997) B10525997
theorem B6655441 : Blo 1729065 6655441 := bstep (se 2 (by rfl) ⟨2495790, by rfl⟩ : syracuseStep 6655441 = 4991581) B4991581
theorem B8760797 : Blo 1729065 8760797 := bstep (se 3 (by rfl) ⟨1642649, by rfl⟩ : syracuseStep 8760797 = 3285299) B3285299
theorem B7392779 : Blo 1729065 7392779 := bstep (se 1 (by rfl) ⟨5544584, by rfl⟩ : syracuseStep 7392779 = 11089169) B11089169
theorem B9989675 : Blo 1729065 9989675 := bstep (se 1 (by rfl) ⟨7492256, by rfl⟩ : syracuseStep 9989675 = 14984513) B14984513
theorem B4378171 : Blo 1729065 4378171 := bstep (se 1 (by rfl) ⟨3283628, by rfl⟩ : syracuseStep 4378171 = 6567257) B6567257
theorem B19975747 : Blo 1729065 19975747 := bstep (se 1 (by rfl) ⟨14981810, by rfl⟩ : syracuseStep 19975747 = 29963621) B29963621
theorem B6565495 : Blo 1729065 6565495 := bstep (se 1 (by rfl) ⟨4924121, by rfl⟩ : syracuseStep 6565495 = 9848243) B9848243
theorem B4378313 : Blo 1729065 4378313 := bstep (se 2 (by rfl) ⟨1641867, by rfl⟩ : syracuseStep 4378313 = 3283735) B3283735
theorem B113807105 : Blo 1729065 113807105 := bstep (se 2 (by rfl) ⟨42677664, by rfl⟩ : syracuseStep 113807105 = 85355329) B85355329
theorem B4927243 : Blo 1729065 4927243 := bstep (se 1 (by rfl) ⟨3695432, by rfl⟩ : syracuseStep 4927243 = 7390865) B7390865
theorem B8761121 : Blo 1729065 8761121 := bstep (se 2 (by rfl) ⟨3285420, by rfl⟩ : syracuseStep 8761121 = 6570841) B6570841
theorem B5263147 : Blo 1729065 5263147 := bstep (se 1 (by rfl) ⟨3947360, by rfl⟩ : syracuseStep 5263147 = 7894721) B7894721
theorem B9858905 : Blo 1729065 9858905 := bstep (se 2 (by rfl) ⟨3697089, by rfl⟩ : syracuseStep 9858905 = 7394179) B7394179
theorem B7393139 : Blo 1729065 7393139 := bstep (se 1 (by rfl) ⟨5544854, by rfl⟩ : syracuseStep 7393139 = 11089709) B11089709
theorem B5836697 : Blo 1729065 5836697 := bstep (se 2 (by rfl) ⟨2188761, by rfl⟩ : syracuseStep 5836697 = 4377523) B4377523
theorem B5541817 : Blo 1729065 5541817 := bstep (se 2 (by rfl) ⟨2078181, by rfl⟩ : syracuseStep 5541817 = 4156363) B4156363
theorem B1945615 : Blo 1729065 1945615 := bstep (se 1 (by rfl) ⟨1459211, by rfl⟩ : syracuseStep 1945615 = 2918423) B2918423
theorem B4927517 : Blo 1729065 4927517 := bstep (se 3 (by rfl) ⟨923909, by rfl⟩ : syracuseStep 4927517 = 1847819) B1847819
theorem B4378657 : Blo 1729065 4378657 := bstep (se 2 (by rfl) ⟨1641996, by rfl⟩ : syracuseStep 4378657 = 3283993) B3283993
theorem B2920583 : Blo 1729065 2920583 := bstep (se 1 (by rfl) ⟨2190437, by rfl⟩ : syracuseStep 2920583 = 4380875) B4380875
theorem B37400777 : Blo 1729065 37400777 := bstep (se 2 (by rfl) ⟨14025291, by rfl⟩ : syracuseStep 37400777 = 28050583) B28050583
theorem B9351425 : Blo 1729065 9351425 := bstep (se 2 (by rfl) ⟨3506784, by rfl⟩ : syracuseStep 9351425 = 7013569) B7013569
theorem B1847567 : Blo 1729065 1847567 := bstep (se 1 (by rfl) ⟨1385675, by rfl⟩ : syracuseStep 1847567 = 2771351) B2771351
theorem B2027791 : Blo 1729065 2027791 := bstep (se 1 (by rfl) ⟨1520843, by rfl⟩ : syracuseStep 2027791 = 3041687) B3041687
theorem B1946119 : Blo 1729065 1946119 := bstep (se 1 (by rfl) ⟨1459589, by rfl⟩ : syracuseStep 1946119 = 2919179) B2919179
theorem B6566467 : Blo 1729065 6566467 := bstep (se 1 (by rfl) ⟨4924850, by rfl⟩ : syracuseStep 6566467 = 9849701) B9849701
theorem B5837399 : Blo 1729065 5837399 := bstep (se 1 (by rfl) ⟨4378049, by rfl⟩ : syracuseStep 5837399 = 8756099) B8756099
theorem B4379255 : Blo 1729065 4379255 := bstep (se 1 (by rfl) ⟨3284441, by rfl⟩ : syracuseStep 4379255 = 6568883) B6568883
theorem B1946299 : Blo 1729065 1946299 := bstep (se 1 (by rfl) ⟨1459724, by rfl⟩ : syracuseStep 1946299 = 2919449) B2919449
theorem B7492297 : Blo 1729065 7492297 := bstep (se 2 (by rfl) ⟨2809611, by rfl⟩ : syracuseStep 7492297 = 5619223) B5619223
theorem B21033701 : Blo 1729065 21033701 := bstep (se 4 (by rfl) ⟨1971909, by rfl⟩ : syracuseStep 21033701 = 3943819) B3943819
theorem B8762093 : Blo 1729065 8762093 := bstep (se 3 (by rfl) ⟨1642892, by rfl⟩ : syracuseStep 8762093 = 3285785) B3285785
theorem B4158209 : Blo 1729065 4158209 := bstep (se 2 (by rfl) ⟨1559328, by rfl⟩ : syracuseStep 4158209 = 3118657) B3118657
theorem B6566771 : Blo 1729065 6566771 := bstep (se 1 (by rfl) ⟨4925078, by rfl⟩ : syracuseStep 6566771 = 9850157) B9850157
theorem B2593655 : Blo 1729065 2593655 := bstep (se 1 (by rfl) ⟨1945241, by rfl⟩ : syracuseStep 2593655 = 3890483) B3890483
theorem B2593679 : Blo 1729065 2593679 := bstep (se 1 (by rfl) ⟨1945259, by rfl⟩ : syracuseStep 2593679 = 3890519) B3890519
theorem B6656921 : Blo 1729065 6656921 := bstep (se 2 (by rfl) ⟨2496345, by rfl⟩ : syracuseStep 6656921 = 4992691) B4992691
theorem B2593721 : Blo 1729065 2593721 := bstep (se 2 (by rfl) ⟨972645, by rfl⟩ : syracuseStep 2593721 = 1945291) B1945291
theorem B2462665 : Blo 1729065 2462665 := bstep (se 2 (by rfl) ⟨923499, by rfl⟩ : syracuseStep 2462665 = 1846999) B1846999
theorem B2593799 : Blo 1729065 2593799 := bstep (se 1 (by rfl) ⟨1945349, by rfl⟩ : syracuseStep 2593799 = 3890699) B3890699
theorem B2593835 : Blo 1729065 2593835 := bstep (se 1 (by rfl) ⟨1945376, by rfl⟩ : syracuseStep 2593835 = 3890753) B3890753
theorem B5837885 : Blo 1729065 5837885 := bstep (se 3 (by rfl) ⟨1094603, by rfl⟩ : syracuseStep 5837885 = 2189207) B2189207
theorem B2593865 : Blo 1729065 2593865 := bstep (se 2 (by rfl) ⟨972699, by rfl⟩ : syracuseStep 2593865 = 1945399) B1945399
theorem B4437127 : Blo 1729065 4437127 := bstep (se 1 (by rfl) ⟨3327845, by rfl⟩ : syracuseStep 4437127 = 6655691) B6655691
theorem B1946767 : Blo 1729065 1946767 := bstep (se 1 (by rfl) ⟨1460075, by rfl⟩ : syracuseStep 1946767 = 2920151) B2920151
theorem B20247725 : Blo 1729065 20247725 := bstep (se 3 (by rfl) ⟨3796448, by rfl⟩ : syracuseStep 20247725 = 7592897) B7592897
theorem B4158649 : Blo 1729065 4158649 := bstep (se 2 (by rfl) ⟨1559493, by rfl⟩ : syracuseStep 4158649 = 3118987) B3118987
theorem B2593979 : Blo 1729065 2593979 := bstep (se 1 (by rfl) ⟨1945484, by rfl⟩ : syracuseStep 2593979 = 3890969) B3890969
theorem B2594039 : Blo 1729065 2594039 := bstep (se 1 (by rfl) ⟨1945529, by rfl⟩ : syracuseStep 2594039 = 3891059) B3891059
theorem B2594063 : Blo 1729065 2594063 := bstep (se 1 (by rfl) ⟨1945547, by rfl⟩ : syracuseStep 2594063 = 3891095) B3891095
theorem B2594105 : Blo 1729065 2594105 := bstep (se 2 (by rfl) ⟨972789, by rfl⟩ : syracuseStep 2594105 = 1945579) B1945579
theorem B14021947 : Blo 1729065 14021947 := bstep (se 1 (by rfl) ⟨10516460, by rfl⟩ : syracuseStep 14021947 = 21032921) B21032921
theorem B6567227 : Blo 1729065 6567227 := bstep (se 1 (by rfl) ⟨4925420, by rfl⟩ : syracuseStep 6567227 = 9850841) B9850841
theorem B19699037 : Blo 1729065 19699037 := bstep (se 3 (by rfl) ⟨3693569, by rfl⟩ : syracuseStep 19699037 = 7387139) B7387139
theorem B18715997 : Blo 1729065 18715997 := bstep (se 3 (by rfl) ⟨3509249, by rfl⟩ : syracuseStep 18715997 = 7018499) B7018499
theorem B4674935 : Blo 1729065 4674935 := bstep (se 1 (by rfl) ⟨3506201, by rfl⟩ : syracuseStep 4674935 = 7012403) B7012403
theorem B2594183 : Blo 1729065 2594183 := bstep (se 1 (by rfl) ⟨1945637, by rfl⟩ : syracuseStep 2594183 = 3891275) B3891275
theorem B2594219 : Blo 1729065 2594219 := bstep (se 1 (by rfl) ⟨1945664, by rfl⟩ : syracuseStep 2594219 = 3891329) B3891329
theorem B33256889 : Blo 1729065 33256889 := bstep (se 2 (by rfl) ⟨12471333, by rfl⟩ : syracuseStep 33256889 = 24942667) B24942667
theorem B2594249 : Blo 1729065 2594249 := bstep (se 2 (by rfl) ⟨972843, by rfl⟩ : syracuseStep 2594249 = 1945687) B1945687
theorem B3159497 : Blo 1729065 3159497 := bstep (se 2 (by rfl) ⟨1184811, by rfl⟩ : syracuseStep 3159497 = 2369623) B2369623
theorem B8754641 : Blo 1729065 8754641 := bstep (se 2 (by rfl) ⟨3282990, by rfl⟩ : syracuseStep 8754641 = 6565981) B6565981
theorem B8877533 : Blo 1729065 8877533 := bstep (se 3 (by rfl) ⟨1664537, by rfl⟩ : syracuseStep 8877533 = 3329075) B3329075
theorem B2463223 : Blo 1729065 2463223 := bstep (se 1 (by rfl) ⟨1847417, by rfl⟩ : syracuseStep 2463223 = 3694835) B3694835
theorem B8762903 : Blo 1729065 8762903 := bstep (se 1 (by rfl) ⟨6572177, by rfl⟩ : syracuseStep 8762903 = 13144355) B13144355
theorem B2594363 : Blo 1729065 2594363 := bstep (se 1 (by rfl) ⟨1945772, by rfl⟩ : syracuseStep 2594363 = 3891545) B3891545
theorem B2594423 : Blo 1729065 2594423 := bstep (se 1 (by rfl) ⟨1945817, by rfl⟩ : syracuseStep 2594423 = 3891635) B3891635
theorem B1947271 : Blo 1729065 1947271 := bstep (se 1 (by rfl) ⟨1460453, by rfl⟩ : syracuseStep 1947271 = 2920907) B2920907
theorem B2594447 : Blo 1729065 2594447 := bstep (se 1 (by rfl) ⟨1945835, by rfl⟩ : syracuseStep 2594447 = 3891671) B3891671
theorem B2594489 : Blo 1729065 2594489 := bstep (se 2 (by rfl) ⟨972933, by rfl⟩ : syracuseStep 2594489 = 1945867) B1945867
theorem B9852617 : Blo 1729065 9852617 := bstep (se 2 (by rfl) ⟨3694731, by rfl⟩ : syracuseStep 9852617 = 7389463) B7389463
theorem B2594567 : Blo 1729065 2594567 := bstep (se 1 (by rfl) ⟨1945925, by rfl⟩ : syracuseStep 2594567 = 3891851) B3891851
theorem B6567713 : Blo 1729065 6567713 := bstep (se 2 (by rfl) ⟨2462892, by rfl⟩ : syracuseStep 6567713 = 4925785) B4925785
theorem B2594603 : Blo 1729065 2594603 := bstep (se 1 (by rfl) ⟨1945952, by rfl⟩ : syracuseStep 2594603 = 3891905) B3891905
theorem B2594633 : Blo 1729065 2594633 := bstep (se 2 (by rfl) ⟨972987, by rfl⟩ : syracuseStep 2594633 = 1945975) B1945975
theorem B4380551 : Blo 1729065 4380551 := bstep (se 1 (by rfl) ⟨3285413, by rfl⟩ : syracuseStep 4380551 = 6570827) B6570827
theorem B4380601 : Blo 1729065 4380601 := bstep (se 2 (by rfl) ⟨1642725, by rfl⟩ : syracuseStep 4380601 = 3285451) B3285451
theorem B2594747 : Blo 1729065 2594747 := bstep (se 1 (by rfl) ⟨1946060, by rfl⟩ : syracuseStep 2594747 = 3892121) B3892121
theorem B2594807 : Blo 1729065 2594807 := bstep (se 1 (by rfl) ⟨1946105, by rfl⟩ : syracuseStep 2594807 = 3892211) B3892211
theorem B2594831 : Blo 1729065 2594831 := bstep (se 1 (by rfl) ⟨1946123, by rfl⟩ : syracuseStep 2594831 = 3892247) B3892247
theorem B2463787 : Blo 1729065 2463787 := bstep (se 1 (by rfl) ⟨1847840, by rfl⟩ : syracuseStep 2463787 = 3695681) B3695681
theorem B2594873 : Blo 1729065 2594873 := bstep (se 2 (by rfl) ⟨973077, by rfl⟩ : syracuseStep 2594873 = 1946155) B1946155
theorem B2594951 : Blo 1729065 2594951 := bstep (se 1 (by rfl) ⟨1946213, by rfl⟩ : syracuseStep 2594951 = 3892427) B3892427
theorem B2594987 : Blo 1729065 2594987 := bstep (se 1 (by rfl) ⟨1946240, by rfl⟩ : syracuseStep 2594987 = 3892481) B3892481
theorem B14022857 : Blo 1729065 14022857 := bstep (se 2 (by rfl) ⟨5258571, by rfl⟩ : syracuseStep 14022857 = 10517143) B10517143
theorem B2595017 : Blo 1729065 2595017 := bstep (se 2 (by rfl) ⟨973131, by rfl⟩ : syracuseStep 2595017 = 1946263) B1946263
theorem B2464015 : Blo 1729065 2464015 := bstep (se 1 (by rfl) ⟨1848011, by rfl⟩ : syracuseStep 2464015 = 3696023) B3696023
theorem B2595131 : Blo 1729065 2595131 := bstep (se 1 (by rfl) ⟨1946348, by rfl⟩ : syracuseStep 2595131 = 3892697) B3892697
theorem B5544251 : Blo 1729065 5544251 := bstep (se 1 (by rfl) ⟨4158188, by rfl⟩ : syracuseStep 5544251 = 8316377) B8316377
theorem B2595191 : Blo 1729065 2595191 := bstep (se 1 (by rfl) ⟨1946393, by rfl⟩ : syracuseStep 2595191 = 3892787) B3892787
theorem B2595215 : Blo 1729065 2595215 := bstep (se 1 (by rfl) ⟨1946411, by rfl⟩ : syracuseStep 2595215 = 3892823) B3892823
theorem B12474769 : Blo 1729065 12474769 := bstep (se 2 (by rfl) ⟨4678038, by rfl⟩ : syracuseStep 12474769 = 9356077) B9356077
theorem B3692947 : Blo 1729065 3692947 := bstep (se 1 (by rfl) ⟨2769710, by rfl⟩ : syracuseStep 3692947 = 5539421) B5539421
theorem B5839289 : Blo 1729065 5839289 := bstep (se 2 (by rfl) ⟨2189733, by rfl⟩ : syracuseStep 5839289 = 4379467) B4379467
theorem B2595257 : Blo 1729065 2595257 := bstep (se 2 (by rfl) ⟨973221, by rfl⟩ : syracuseStep 2595257 = 1946443) B1946443
theorem B2595335 : Blo 1729065 2595335 := bstep (se 1 (by rfl) ⟨1946501, by rfl⟩ : syracuseStep 2595335 = 3893003) B3893003
theorem B4381199 : Blo 1729065 4381199 := bstep (se 1 (by rfl) ⟨3285899, by rfl⟩ : syracuseStep 4381199 = 6571799) B6571799
theorem B2595371 : Blo 1729065 2595371 := bstep (se 1 (by rfl) ⟨1946528, by rfl⟩ : syracuseStep 2595371 = 3893057) B3893057
theorem B2595401 : Blo 1729065 2595401 := bstep (se 2 (by rfl) ⟨973275, by rfl⟩ : syracuseStep 2595401 = 1946551) B1946551
theorem B22166135 : Blo 1729065 22166135 := bstep (se 1 (by rfl) ⟨16624601, by rfl⟩ : syracuseStep 22166135 = 33249203) B33249203
theorem B3283591 : Blo 1729065 3283591 := bstep (se 1 (by rfl) ⟨2462693, by rfl⟩ : syracuseStep 3283591 = 4925387) B4925387
theorem B2595515 : Blo 1729065 2595515 := bstep (se 1 (by rfl) ⟨1946636, by rfl⟩ : syracuseStep 2595515 = 3893273) B3893273
theorem B6568685 : Blo 1729065 6568685 := bstep (se 3 (by rfl) ⟨1231628, by rfl⟩ : syracuseStep 6568685 = 2463257) B2463257
theorem B2595575 : Blo 1729065 2595575 := bstep (se 1 (by rfl) ⟨1946681, by rfl⟩ : syracuseStep 2595575 = 3893363) B3893363
theorem B4676363 : Blo 1729065 4676363 := bstep (se 1 (by rfl) ⟨3507272, by rfl⟩ : syracuseStep 4676363 = 7014545) B7014545
theorem B19700495 : Blo 1729065 19700495 := bstep (se 1 (by rfl) ⟨14775371, by rfl⟩ : syracuseStep 19700495 = 29550743) B29550743
theorem B2595599 : Blo 1729065 2595599 := bstep (se 1 (by rfl) ⟨1946699, by rfl⟩ : syracuseStep 2595599 = 3893399) B3893399
theorem B2595641 : Blo 1729065 2595641 := bstep (se 2 (by rfl) ⟨973365, by rfl⟩ : syracuseStep 2595641 = 1946731) B1946731
theorem B2595719 : Blo 1729065 2595719 := bstep (se 1 (by rfl) ⟨1946789, by rfl⟩ : syracuseStep 2595719 = 3893579) B3893579
theorem B2595755 : Blo 1729065 2595755 := bstep (se 1 (by rfl) ⟨1946816, by rfl⟩ : syracuseStep 2595755 = 3893633) B3893633
theorem B2595785 : Blo 1729065 2595785 := bstep (se 2 (by rfl) ⟨973419, by rfl⟩ : syracuseStep 2595785 = 1946839) B1946839
theorem B5839883 : Blo 1729065 5839883 := bstep (se 1 (by rfl) ⟨4379912, by rfl⟩ : syracuseStep 5839883 = 8759825) B8759825
theorem B9993239 : Blo 1729065 9993239 := bstep (se 1 (by rfl) ⟨7494929, by rfl⟩ : syracuseStep 9993239 = 14989859) B14989859
theorem B2595899 : Blo 1729065 2595899 := bstep (se 1 (by rfl) ⟨1946924, by rfl⟩ : syracuseStep 2595899 = 3893849) B3893849
theorem B5839991 : Blo 1729065 5839991 := bstep (se 1 (by rfl) ⟨4379993, by rfl⟩ : syracuseStep 5839991 = 8759987) B8759987
theorem B2595959 : Blo 1729065 2595959 := bstep (se 1 (by rfl) ⟨1946969, by rfl⟩ : syracuseStep 2595959 = 3893939) B3893939
theorem B2595983 : Blo 1729065 2595983 := bstep (se 1 (by rfl) ⟨1946987, by rfl⟩ : syracuseStep 2595983 = 3893975) B3893975
theorem B2596025 : Blo 1729065 2596025 := bstep (se 2 (by rfl) ⟨973509, by rfl⟩ : syracuseStep 2596025 = 1947019) B1947019
theorem B2596103 : Blo 1729065 2596103 := bstep (se 1 (by rfl) ⟨1947077, by rfl⟩ : syracuseStep 2596103 = 3894155) B3894155
theorem B3890447 : Blo 1729065 3890447 := bstep (se 1 (by rfl) ⟨2917835, by rfl⟩ : syracuseStep 3890447 = 5835671) B5835671
theorem B3890465 : Blo 1729065 3890465 := bstep (se 2 (by rfl) ⟨1458924, by rfl⟩ : syracuseStep 3890465 = 2917849) B2917849
theorem B2596139 : Blo 1729065 2596139 := bstep (se 1 (by rfl) ⟨1947104, by rfl⟩ : syracuseStep 2596139 = 3894209) B3894209
theorem B19709243 : Blo 1729065 19709243 := bstep (se 1 (by rfl) ⟨14781932, by rfl⟩ : syracuseStep 19709243 = 29563865) B29563865
theorem B2596169 : Blo 1729065 2596169 := bstep (se 2 (by rfl) ⟨973563, by rfl⟩ : syracuseStep 2596169 = 1947127) B1947127
theorem B5258611 : Blo 1729065 5258611 := bstep (se 1 (by rfl) ⟨3943958, by rfl⟩ : syracuseStep 5258611 = 7887917) B7887917
theorem B6569369 : Blo 1729065 6569369 := bstep (se 2 (by rfl) ⟨2463513, by rfl⟩ : syracuseStep 6569369 = 4927027) B4927027
theorem B2596283 : Blo 1729065 2596283 := bstep (se 1 (by rfl) ⟨1947212, by rfl⟩ : syracuseStep 2596283 = 3894425) B3894425
theorem B2596343 : Blo 1729065 2596343 := bstep (se 1 (by rfl) ⟨1947257, by rfl⟩ : syracuseStep 2596343 = 3894515) B3894515
theorem B8756747 : Blo 1729065 8756747 := bstep (se 1 (by rfl) ⟨6567560, by rfl⟩ : syracuseStep 8756747 = 13135121) B13135121
theorem B2596367 : Blo 1729065 2596367 := bstep (se 1 (by rfl) ⟨1947275, by rfl⟩ : syracuseStep 2596367 = 3894551) B3894551
theorem B2596409 : Blo 1729065 2596409 := bstep (se 2 (by rfl) ⟨973653, by rfl⟩ : syracuseStep 2596409 = 1947307) B1947307
theorem B3161659 : Blo 1729065 3161659 := bstep (se 1 (by rfl) ⟨2371244, by rfl⟩ : syracuseStep 3161659 = 4742489) B4742489
theorem B9854531 : Blo 1729065 9854531 := bstep (se 1 (by rfl) ⟨7390898, by rfl⟩ : syracuseStep 9854531 = 14781797) B14781797
theorem B3890807 : Blo 1729065 3890807 := bstep (se 1 (by rfl) ⟨2918105, by rfl⟩ : syracuseStep 3890807 = 5836211) B5836211
theorem B18243191 : Blo 1729065 18243191 := bstep (se 1 (by rfl) ⟨13682393, by rfl⟩ : syracuseStep 18243191 = 27364787) B27364787
theorem B2596487 : Blo 1729065 2596487 := bstep (se 1 (by rfl) ⟨1947365, by rfl⟩ : syracuseStep 2596487 = 3894731) B3894731
theorem B2596523 : Blo 1729065 2596523 := bstep (se 1 (by rfl) ⟨1947392, by rfl⟩ : syracuseStep 2596523 = 3894785) B3894785
theorem B8756909 : Blo 1729065 8756909 := bstep (se 3 (by rfl) ⟨1641920, by rfl⟩ : syracuseStep 8756909 = 3283841) B3283841
theorem B5840585 : Blo 1729065 5840585 := bstep (se 2 (by rfl) ⟨2190219, by rfl⟩ : syracuseStep 5840585 = 4380439) B4380439
theorem B2596553 : Blo 1729065 2596553 := bstep (se 2 (by rfl) ⟨973707, by rfl⟩ : syracuseStep 2596553 = 1947415) B1947415
theorem B3890987 : Blo 1729065 3890987 := bstep (se 1 (by rfl) ⟨2918240, by rfl⟩ : syracuseStep 3890987 = 5836481) B5836481
theorem B3285011 : Blo 1729065 3285011 := bstep (se 1 (by rfl) ⟨2463758, by rfl⟩ : syracuseStep 3285011 = 4927517) B4927517
theorem B3891257 : Blo 1729065 3891257 := bstep (se 2 (by rfl) ⟨1459221, by rfl⟩ : syracuseStep 3891257 = 2918443) B2918443
theorem B3285049 : Blo 1729065 3285049 := bstep (se 2 (by rfl) ⟨1231893, by rfl⟩ : syracuseStep 3285049 = 2463787) B2463787
theorem B14778449 : Blo 1729065 14778449 := bstep (se 2 (by rfl) ⟨5541918, by rfl⟩ : syracuseStep 14778449 = 11083837) B11083837
theorem B63971477 : Blo 1729065 63971477 := bstep (se 6 (by rfl) ⟨1499331, by rfl⟩ : syracuseStep 63971477 = 2998663) B2998663
theorem B6234283 : Blo 1729065 6234283 := bstep (se 1 (by rfl) ⟨4675712, by rfl⟩ : syracuseStep 6234283 = 9351425) B9351425
theorem B3285353 : Blo 1729065 3285353 := bstep (se 2 (by rfl) ⟨1232007, by rfl⟩ : syracuseStep 3285353 = 2464015) B2464015
theorem B2703721 : Blo 1729065 2703721 := bstep (se 2 (by rfl) ⟨1013895, by rfl⟩ : syracuseStep 2703721 = 2027791) B2027791
theorem B3891599 : Blo 1729065 3891599 := bstep (se 1 (by rfl) ⟨2918699, by rfl⟩ : syracuseStep 3891599 = 5837399) B5837399
theorem B5841395 : Blo 1729065 5841395 := bstep (se 1 (by rfl) ⟨4381046, by rfl⟩ : syracuseStep 5841395 = 8762093) B8762093
theorem B4923929 : Blo 1729065 4923929 := bstep (se 2 (by rfl) ⟨1846473, by rfl⟩ : syracuseStep 4923929 = 3692947) B3692947
theorem B1729103 : Blo 1729065 1729103 := bstep (se 1 (by rfl) ⟨1296827, by rfl⟩ : syracuseStep 1729103 = 2593655) B2593655
theorem B1729119 : Blo 1729065 1729119 := bstep (se 1 (by rfl) ⟨1296839, by rfl⟩ : syracuseStep 1729119 = 2593679) B2593679
theorem B1729147 : Blo 1729065 1729147 := bstep (se 1 (by rfl) ⟨1296860, by rfl⟩ : syracuseStep 1729147 = 2593721) B2593721
theorem B1729199 : Blo 1729065 1729199 := bstep (se 1 (by rfl) ⟨1296899, by rfl⟩ : syracuseStep 1729199 = 2593799) B2593799
theorem B1729223 : Blo 1729065 1729223 := bstep (se 1 (by rfl) ⟨1296917, by rfl⟩ : syracuseStep 1729223 = 2593835) B2593835
theorem B3891923 : Blo 1729065 3891923 := bstep (se 1 (by rfl) ⟨2918942, by rfl⟩ : syracuseStep 3891923 = 5837885) B5837885
theorem B1729243 : Blo 1729065 1729243 := bstep (se 1 (by rfl) ⟨1296932, by rfl⟩ : syracuseStep 1729243 = 2593865) B2593865
theorem B1729319 : Blo 1729065 1729319 := bstep (se 1 (by rfl) ⟨1296989, by rfl⟩ : syracuseStep 1729319 = 2593979) B2593979
theorem B1729359 : Blo 1729065 1729359 := bstep (se 1 (by rfl) ⟨1297019, by rfl⟩ : syracuseStep 1729359 = 2594039) B2594039
theorem B1729375 : Blo 1729065 1729375 := bstep (se 1 (by rfl) ⟨1297031, by rfl⟩ : syracuseStep 1729375 = 2594063) B2594063
theorem B1729403 : Blo 1729065 1729403 := bstep (se 1 (by rfl) ⟨1297052, by rfl⟩ : syracuseStep 1729403 = 2594105) B2594105
theorem B13132691 : Blo 1729065 13132691 := bstep (se 1 (by rfl) ⟨9849518, by rfl⟩ : syracuseStep 13132691 = 19699037) B19699037
theorem B12477331 : Blo 1729065 12477331 := bstep (se 1 (by rfl) ⟨9357998, by rfl⟩ : syracuseStep 12477331 = 18715997) B18715997
theorem B1729455 : Blo 1729065 1729455 := bstep (se 1 (by rfl) ⟨1297091, by rfl⟩ : syracuseStep 1729455 = 2594183) B2594183
theorem B1729479 : Blo 1729065 1729479 := bstep (se 1 (by rfl) ⟨1297109, by rfl⟩ : syracuseStep 1729479 = 2594219) B2594219
theorem B1729499 : Blo 1729065 1729499 := bstep (se 1 (by rfl) ⟨1297124, by rfl⟩ : syracuseStep 1729499 = 2594249) B2594249
theorem B2106331 : Blo 1729065 2106331 := bstep (se 1 (by rfl) ⟨1579748, by rfl⟩ : syracuseStep 2106331 = 3159497) B3159497
theorem B5841935 : Blo 1729065 5841935 := bstep (se 1 (by rfl) ⟨4381451, by rfl⟩ : syracuseStep 5841935 = 8762903) B8762903
theorem B1729575 : Blo 1729065 1729575 := bstep (se 1 (by rfl) ⟨1297181, by rfl⟩ : syracuseStep 1729575 = 2594363) B2594363
theorem B56149037 : Blo 1729065 56149037 := bstep (se 3 (by rfl) ⟨10527944, by rfl⟩ : syracuseStep 56149037 = 21055889) B21055889
theorem B1729615 : Blo 1729065 1729615 := bstep (se 1 (by rfl) ⟨1297211, by rfl⟩ : syracuseStep 1729615 = 2594423) B2594423
theorem B1729631 : Blo 1729065 1729631 := bstep (se 1 (by rfl) ⟨1297223, by rfl⟩ : syracuseStep 1729631 = 2594447) B2594447
theorem B1729659 : Blo 1729065 1729659 := bstep (se 1 (by rfl) ⟨1297244, by rfl⟩ : syracuseStep 1729659 = 2594489) B2594489
theorem B1729711 : Blo 1729065 1729711 := bstep (se 1 (by rfl) ⟨1297283, by rfl⟩ : syracuseStep 1729711 = 2594567) B2594567
theorem B1729735 : Blo 1729065 1729735 := bstep (se 1 (by rfl) ⟨1297301, by rfl⟩ : syracuseStep 1729735 = 2594603) B2594603
theorem B11830475 : Blo 1729065 11830475 := bstep (se 1 (by rfl) ⟨8872856, by rfl⟩ : syracuseStep 11830475 = 17745713) B17745713
theorem B1729755 : Blo 1729065 1729755 := bstep (se 1 (by rfl) ⟨1297316, by rfl⟩ : syracuseStep 1729755 = 2594633) B2594633
theorem B1729831 : Blo 1729065 1729831 := bstep (se 1 (by rfl) ⟨1297373, by rfl⟩ : syracuseStep 1729831 = 2594747) B2594747
theorem B1754407 : Blo 1729065 1754407 := bstep (se 1 (by rfl) ⟨1315805, by rfl⟩ : syracuseStep 1754407 = 2631611) B2631611
theorem B1729871 : Blo 1729065 1729871 := bstep (se 1 (by rfl) ⟨1297403, by rfl⟩ : syracuseStep 1729871 = 2594807) B2594807
theorem B1729887 : Blo 1729065 1729887 := bstep (se 1 (by rfl) ⟨1297415, by rfl⟩ : syracuseStep 1729887 = 2594831) B2594831
theorem B1729915 : Blo 1729065 1729915 := bstep (se 1 (by rfl) ⟨1297436, by rfl⟩ : syracuseStep 1729915 = 2594873) B2594873
theorem B1729967 : Blo 1729065 1729967 := bstep (se 1 (by rfl) ⟨1297475, by rfl⟩ : syracuseStep 1729967 = 2594951) B2594951
theorem B1729991 : Blo 1729065 1729991 := bstep (se 1 (by rfl) ⟨1297493, by rfl⟩ : syracuseStep 1729991 = 2594987) B2594987
theorem B9348571 : Blo 1729065 9348571 := bstep (se 1 (by rfl) ⟨7011428, by rfl⟩ : syracuseStep 9348571 = 14022857) B14022857
theorem B1730011 : Blo 1729065 1730011 := bstep (se 1 (by rfl) ⟨1297508, by rfl⟩ : syracuseStep 1730011 = 2595017) B2595017
theorem B5916169 : Blo 1729065 5916169 := bstep (se 2 (by rfl) ⟨2218563, by rfl⟩ : syracuseStep 5916169 = 4437127) B4437127
theorem B3556883 : Blo 1729065 3556883 := bstep (se 1 (by rfl) ⟨2667662, by rfl⟩ : syracuseStep 3556883 = 5335325) B5335325
theorem B1730087 : Blo 1729065 1730087 := bstep (se 1 (by rfl) ⟨1297565, by rfl⟩ : syracuseStep 1730087 = 2595131) B2595131
theorem B3696167 : Blo 1729065 3696167 := bstep (se 1 (by rfl) ⟨2772125, by rfl⟩ : syracuseStep 3696167 = 5544251) B5544251
theorem B1730127 : Blo 1729065 1730127 := bstep (se 1 (by rfl) ⟨1297595, by rfl⟩ : syracuseStep 1730127 = 2595191) B2595191
theorem B1730143 : Blo 1729065 1730143 := bstep (se 1 (by rfl) ⟨1297607, by rfl⟩ : syracuseStep 1730143 = 2595215) B2595215
theorem B2918011 : Blo 1729065 2918011 := bstep (se 1 (by rfl) ⟨2188508, by rfl⟩ : syracuseStep 2918011 = 4377017) B4377017
theorem B3892859 : Blo 1729065 3892859 := bstep (se 1 (by rfl) ⟨2919644, by rfl⟩ : syracuseStep 3892859 = 5839289) B5839289
theorem B1730171 : Blo 1729065 1730171 := bstep (se 1 (by rfl) ⟨1297628, by rfl⟩ : syracuseStep 1730171 = 2595257) B2595257
theorem B1730223 : Blo 1729065 1730223 := bstep (se 1 (by rfl) ⟨1297667, by rfl⟩ : syracuseStep 1730223 = 2595335) B2595335
theorem B1730247 : Blo 1729065 1730247 := bstep (se 1 (by rfl) ⟨1297685, by rfl⟩ : syracuseStep 1730247 = 2595371) B2595371
theorem B1730267 : Blo 1729065 1730267 := bstep (se 1 (by rfl) ⟨1297700, by rfl⟩ : syracuseStep 1730267 = 2595401) B2595401
theorem B18695929 : Blo 1729065 18695929 := bstep (se 2 (by rfl) ⟨7010973, by rfl⟩ : syracuseStep 18695929 = 14021947) B14021947
theorem B3892985 : Blo 1729065 3892985 := bstep (se 2 (by rfl) ⟨1459869, by rfl⟩ : syracuseStep 3892985 = 2919739) B2919739
theorem B1730343 : Blo 1729065 1730343 := bstep (se 1 (by rfl) ⟨1297757, by rfl⟩ : syracuseStep 1730343 = 2595515) B2595515
theorem B1730383 : Blo 1729065 1730383 := bstep (se 1 (by rfl) ⟨1297787, by rfl⟩ : syracuseStep 1730383 = 2595575) B2595575
theorem B13133663 : Blo 1729065 13133663 := bstep (se 1 (by rfl) ⟨9850247, by rfl⟩ : syracuseStep 13133663 = 19700495) B19700495
theorem B1730399 : Blo 1729065 1730399 := bstep (se 1 (by rfl) ⟨1297799, by rfl⟩ : syracuseStep 1730399 = 2595599) B2595599
theorem B1730427 : Blo 1729065 1730427 := bstep (se 1 (by rfl) ⟨1297820, by rfl⟩ : syracuseStep 1730427 = 2595641) B2595641
theorem B1730479 : Blo 1729065 1730479 := bstep (se 1 (by rfl) ⟨1297859, by rfl⟩ : syracuseStep 1730479 = 2595719) B2595719
theorem B8873921 : Blo 1729065 8873921 := bstep (se 2 (by rfl) ⟨3327720, by rfl⟩ : syracuseStep 8873921 = 6655441) B6655441
theorem B1730503 : Blo 1729065 1730503 := bstep (se 1 (by rfl) ⟨1297877, by rfl⟩ : syracuseStep 1730503 = 2595755) B2595755
theorem B1730523 : Blo 1729065 1730523 := bstep (se 1 (by rfl) ⟨1297892, by rfl⟩ : syracuseStep 1730523 = 2595785) B2595785
theorem B3893255 : Blo 1729065 3893255 := bstep (se 1 (by rfl) ⟨2919941, by rfl⟩ : syracuseStep 3893255 = 5839883) B5839883
theorem B13502471 : Blo 1729065 13502471 := bstep (se 1 (by rfl) ⟨10126853, by rfl⟩ : syracuseStep 13502471 = 20253707) B20253707
theorem B6662159 : Blo 1729065 6662159 := bstep (se 1 (by rfl) ⟨4996619, by rfl⟩ : syracuseStep 6662159 = 9993239) B9993239
theorem B1730599 : Blo 1729065 1730599 := bstep (se 1 (by rfl) ⟨1297949, by rfl⟩ : syracuseStep 1730599 = 2595899) B2595899
theorem B3893327 : Blo 1729065 3893327 := bstep (se 1 (by rfl) ⟨2919995, by rfl⟩ : syracuseStep 3893327 = 5839991) B5839991
theorem B1730639 : Blo 1729065 1730639 := bstep (se 1 (by rfl) ⟨1297979, by rfl⟩ : syracuseStep 1730639 = 2595959) B2595959
theorem B26634329 : Blo 1729065 26634329 := bstep (se 2 (by rfl) ⟨9987873, by rfl⟩ : syracuseStep 26634329 = 19975747) B19975747
theorem B1730655 : Blo 1729065 1730655 := bstep (se 1 (by rfl) ⟨1297991, by rfl⟩ : syracuseStep 1730655 = 2595983) B2595983
theorem B1730683 : Blo 1729065 1730683 := bstep (se 1 (by rfl) ⟨1298012, by rfl⟩ : syracuseStep 1730683 = 2596025) B2596025
theorem B1730735 : Blo 1729065 1730735 := bstep (se 1 (by rfl) ⟨1298051, by rfl⟩ : syracuseStep 1730735 = 2596103) B2596103
theorem B1730759 : Blo 1729065 1730759 := bstep (se 1 (by rfl) ⟨1298069, by rfl⟩ : syracuseStep 1730759 = 2596139) B2596139
theorem B1730779 : Blo 1729065 1730779 := bstep (se 1 (by rfl) ⟨1298084, by rfl⟩ : syracuseStep 1730779 = 2596169) B2596169
theorem B6572299 : Blo 1729065 6572299 := bstep (se 1 (by rfl) ⟨4929224, by rfl⟩ : syracuseStep 6572299 = 9858449) B9858449
theorem B1730855 : Blo 1729065 1730855 := bstep (se 1 (by rfl) ⟨1298141, by rfl⟩ : syracuseStep 1730855 = 2596283) B2596283
theorem B18712883 : Blo 1729065 18712883 := bstep (se 1 (by rfl) ⟨14034662, by rfl⟩ : syracuseStep 18712883 = 28069325) B28069325
theorem B3508553 : Blo 1729065 3508553 := bstep (se 2 (by rfl) ⟨1315707, by rfl⟩ : syracuseStep 3508553 = 2631415) B2631415
theorem B1730895 : Blo 1729065 1730895 := bstep (se 1 (by rfl) ⟨1298171, by rfl⟩ : syracuseStep 1730895 = 2596343) B2596343
theorem B1730911 : Blo 1729065 1730911 := bstep (se 1 (by rfl) ⟨1298183, by rfl⟩ : syracuseStep 1730911 = 2596367) B2596367
theorem B1730939 : Blo 1729065 1730939 := bstep (se 1 (by rfl) ⟨1298204, by rfl⟩ : syracuseStep 1730939 = 2596409) B2596409
theorem B5335421 : Blo 1729065 5335421 := bstep (se 3 (by rfl) ⟨1000391, by rfl⟩ : syracuseStep 5335421 = 2000783) B2000783
theorem B1730991 : Blo 1729065 1730991 := bstep (se 1 (by rfl) ⟨1298243, by rfl⟩ : syracuseStep 1730991 = 2596487) B2596487
theorem B1731015 : Blo 1729065 1731015 := bstep (se 1 (by rfl) ⟨1298261, by rfl⟩ : syracuseStep 1731015 = 2596523) B2596523
theorem B2918875 : Blo 1729065 2918875 := bstep (se 1 (by rfl) ⟨2189156, by rfl⟩ : syracuseStep 2918875 = 4378313) B4378313
theorem B3893723 : Blo 1729065 3893723 := bstep (se 1 (by rfl) ⟨2920292, by rfl⟩ : syracuseStep 3893723 = 5840585) B5840585
theorem B1731035 : Blo 1729065 1731035 := bstep (se 1 (by rfl) ⟨1298276, by rfl⟩ : syracuseStep 1731035 = 2596553) B2596553
theorem B6572603 : Blo 1729065 6572603 := bstep (se 1 (by rfl) ⟨4929452, by rfl⟩ : syracuseStep 6572603 = 9858905) B9858905
theorem B14781113 : Blo 1729065 14781113 := bstep (se 2 (by rfl) ⟨5542917, by rfl⟩ : syracuseStep 14781113 = 11085835) B11085835
theorem B3894191 : Blo 1729065 3894191 := bstep (se 1 (by rfl) ⟨2920643, by rfl⟩ : syracuseStep 3894191 = 5841287) B5841287
theorem B4156343 : Blo 1729065 4156343 := bstep (se 1 (by rfl) ⟨3117257, by rfl⟩ : syracuseStep 4156343 = 6234515) B6234515
theorem B5835833 : Blo 1729065 5835833 := bstep (se 2 (by rfl) ⟨2188437, by rfl⟩ : syracuseStep 5835833 = 4376875) B4376875
theorem B2919503 : Blo 1729065 2919503 := bstep (se 1 (by rfl) ⟨2189627, by rfl⟩ : syracuseStep 2919503 = 4379255) B4379255
theorem B8760473 : Blo 1729065 8760473 := bstep (se 2 (by rfl) ⟨3285177, by rfl⟩ : syracuseStep 8760473 = 6570355) B6570355
theorem B2772139 : Blo 1729065 2772139 := bstep (se 1 (by rfl) ⟨2079104, by rfl⟩ : syracuseStep 2772139 = 4158209) B4158209
theorem B3894443 : Blo 1729065 3894443 := bstep (se 1 (by rfl) ⟨2920832, by rfl⟩ : syracuseStep 3894443 = 5841665) B5841665
theorem B16633025 : Blo 1729065 16633025 := bstep (se 2 (by rfl) ⟨6237384, by rfl⟩ : syracuseStep 16633025 = 12474769) B12474769
theorem B4377847 : Blo 1729065 4377847 := bstep (se 1 (by rfl) ⟨3283385, by rfl⟩ : syracuseStep 4377847 = 6566771) B6566771
theorem B5836157 : Blo 1729065 5836157 := bstep (se 3 (by rfl) ⟨1094279, by rfl⟩ : syracuseStep 5836157 = 2188559) B2188559
theorem B4926845 : Blo 1729065 4926845 := bstep (se 3 (by rfl) ⟨923783, by rfl⟩ : syracuseStep 4926845 = 1847567) B1847567
theorem B1846747 : Blo 1729065 1846747 := bstep (se 1 (by rfl) ⟨1385060, by rfl⟩ : syracuseStep 1846747 = 2770121) B2770121
theorem B4378121 : Blo 1729065 4378121 := bstep (se 2 (by rfl) ⟨1641795, by rfl⟩ : syracuseStep 4378121 = 3283591) B3283591
theorem B4378151 : Blo 1729065 4378151 := bstep (se 1 (by rfl) ⟨3283613, by rfl⟩ : syracuseStep 4378151 = 6567227) B6567227
theorem B9989729 : Blo 1729065 9989729 := bstep (se 2 (by rfl) ⟨3746148, by rfl⟩ : syracuseStep 9989729 = 7492297) B7492297
theorem B22171259 : Blo 1729065 22171259 := bstep (se 1 (by rfl) ⟨16628444, by rfl⟩ : syracuseStep 22171259 = 33256889) B33256889
theorem B5836427 : Blo 1729065 5836427 := bstep (se 1 (by rfl) ⟨4377320, by rfl⟩ : syracuseStep 5836427 = 8754641) B8754641
theorem B4927175 : Blo 1729065 4927175 := bstep (se 1 (by rfl) ⟨3695381, by rfl⟩ : syracuseStep 4927175 = 7390763) B7390763
theorem B4378475 : Blo 1729065 4378475 := bstep (se 1 (by rfl) ⟨3283856, by rfl⟩ : syracuseStep 4378475 = 6567713) B6567713
theorem B2920367 : Blo 1729065 2920367 := bstep (se 1 (by rfl) ⟨2190275, by rfl⟩ : syracuseStep 2920367 = 4380551) B4380551
theorem B11079737 : Blo 1729065 11079737 := bstep (se 2 (by rfl) ⟨4154901, by rfl⟩ : syracuseStep 11079737 = 8309803) B8309803
theorem B6565967 : Blo 1729065 6565967 := bstep (se 1 (by rfl) ⟨4924475, by rfl⟩ : syracuseStep 6565967 = 9848951) B9848951
theorem B1945723 : Blo 1729065 1945723 := bstep (se 1 (by rfl) ⟨1459292, by rfl⟩ : syracuseStep 1945723 = 2918585) B2918585
theorem B48648509 : Blo 1729065 48648509 := bstep (se 3 (by rfl) ⟨9121595, by rfl⟩ : syracuseStep 48648509 = 18243191) B18243191
theorem B2920799 : Blo 1729065 2920799 := bstep (se 1 (by rfl) ⟨2190599, by rfl⟩ : syracuseStep 2920799 = 4381199) B4381199
theorem B4379123 : Blo 1729065 4379123 := bstep (se 1 (by rfl) ⟨3284342, by rfl⟩ : syracuseStep 4379123 = 6568685) B6568685
theorem B3117575 : Blo 1729065 3117575 := bstep (se 1 (by rfl) ⟨2338181, by rfl⟩ : syracuseStep 3117575 = 4676363) B4676363
theorem B5837345 : Blo 1729065 5837345 := bstep (se 2 (by rfl) ⟨2189004, by rfl⟩ : syracuseStep 5837345 = 4378009) B4378009
theorem B1946191 : Blo 1729065 1946191 := bstep (se 1 (by rfl) ⟨1459643, by rfl⟩ : syracuseStep 1946191 = 2919287) B2919287
theorem B5837561 : Blo 1729065 5837561 := bstep (se 2 (by rfl) ⟨2189085, by rfl⟩ : syracuseStep 5837561 = 4378171) B4378171
theorem B4215545 : Blo 1729065 4215545 := bstep (se 2 (by rfl) ⟨1580829, by rfl⟩ : syracuseStep 4215545 = 3161659) B3161659
theorem B8753993 : Blo 1729065 8753993 := bstep (se 2 (by rfl) ⟨3282747, by rfl⟩ : syracuseStep 8753993 = 6565495) B6565495
theorem B2593631 : Blo 1729065 2593631 := bstep (se 1 (by rfl) ⟨1945223, by rfl⟩ : syracuseStep 2593631 = 3890447) B3890447
theorem B2593643 : Blo 1729065 2593643 := bstep (se 1 (by rfl) ⟨1945232, by rfl⟩ : syracuseStep 2593643 = 3890465) B3890465
theorem B4379579 : Blo 1729065 4379579 := bstep (se 1 (by rfl) ⟨3284684, by rfl⟩ : syracuseStep 4379579 = 6569369) B6569369
theorem B1946587 : Blo 1729065 1946587 := bstep (se 1 (by rfl) ⟨1459940, by rfl⟩ : syracuseStep 1946587 = 2919881) B2919881
theorem B5837831 : Blo 1729065 5837831 := bstep (se 1 (by rfl) ⟨4378373, by rfl⟩ : syracuseStep 5837831 = 8756747) B8756747
theorem B4928519 : Blo 1729065 4928519 := bstep (se 1 (by rfl) ⟨3696389, by rfl⟩ : syracuseStep 4928519 = 7392779) B7392779
theorem B7017529 : Blo 1729065 7017529 := bstep (se 2 (by rfl) ⟨2631573, by rfl⟩ : syracuseStep 7017529 = 5263147) B5263147
theorem B2593871 : Blo 1729065 2593871 := bstep (se 1 (by rfl) ⟨1945403, by rfl⟩ : syracuseStep 2593871 = 3890807) B3890807
theorem B5837939 : Blo 1729065 5837939 := bstep (se 1 (by rfl) ⟨4378454, by rfl⟩ : syracuseStep 5837939 = 8756909) B8756909
theorem B75871403 : Blo 1729065 75871403 := bstep (se 1 (by rfl) ⟨56903552, by rfl⟩ : syracuseStep 75871403 = 113807105) B113807105
theorem B2593991 : Blo 1729065 2593991 := bstep (se 1 (by rfl) ⟨1945493, by rfl⟩ : syracuseStep 2593991 = 3890987) B3890987
theorem B4928759 : Blo 1729065 4928759 := bstep (se 1 (by rfl) ⟨3696569, by rfl⟩ : syracuseStep 4928759 = 7393139) B7393139
theorem B2594153 : Blo 1729065 2594153 := bstep (se 2 (by rfl) ⟨972807, by rfl⟩ : syracuseStep 2594153 = 1945615) B1945615
theorem B5838209 : Blo 1729065 5838209 := bstep (se 2 (by rfl) ⟨2189328, by rfl⟩ : syracuseStep 5838209 = 4378657) B4378657
theorem B1947055 : Blo 1729065 1947055 := bstep (se 1 (by rfl) ⟨1460291, by rfl⟩ : syracuseStep 1947055 = 2920583) B2920583
theorem B2594231 : Blo 1729065 2594231 := bstep (se 1 (by rfl) ⟨1945673, by rfl⟩ : syracuseStep 2594231 = 3891347) B3891347
theorem B2594267 : Blo 1729065 2594267 := bstep (se 1 (by rfl) ⟨1945700, by rfl⟩ : syracuseStep 2594267 = 3891401) B3891401
theorem B24933851 : Blo 1729065 24933851 := bstep (se 1 (by rfl) ⟨18700388, by rfl⟩ : syracuseStep 24933851 = 37400777) B37400777
theorem B4380257 : Blo 1729065 4380257 := bstep (se 2 (by rfl) ⟨1642596, by rfl⟩ : syracuseStep 4380257 = 3285193) B3285193
theorem B5543635 : Blo 1729065 5543635 := bstep (se 1 (by rfl) ⟨4157726, by rfl⟩ : syracuseStep 5543635 = 8315453) B8315453
theorem B14022467 : Blo 1729065 14022467 := bstep (se 1 (by rfl) ⟨10516850, by rfl⟩ : syracuseStep 14022467 = 21033701) B21033701
theorem B2594735 : Blo 1729065 2594735 := bstep (se 1 (by rfl) ⟨1946051, by rfl⟩ : syracuseStep 2594735 = 3892103) B3892103
theorem B4437947 : Blo 1729065 4437947 := bstep (se 1 (by rfl) ⟨3328460, by rfl⟩ : syracuseStep 4437947 = 6656921) B6656921
theorem B11081735 : Blo 1729065 11081735 := bstep (se 1 (by rfl) ⟨8311301, by rfl⟩ : syracuseStep 11081735 = 16622603) B16622603
theorem B2594825 : Blo 1729065 2594825 := bstep (se 2 (by rfl) ⟨973059, by rfl⟩ : syracuseStep 2594825 = 1946119) B1946119
theorem B6232079 : Blo 1729065 6232079 := bstep (se 1 (by rfl) ⟨4674059, by rfl⟩ : syracuseStep 6232079 = 9348119) B9348119
theorem B2594855 : Blo 1729065 2594855 := bstep (se 1 (by rfl) ⟨1946141, by rfl⟩ : syracuseStep 2594855 = 3892283) B3892283
theorem B8755289 : Blo 1729065 8755289 := bstep (se 2 (by rfl) ⟨3283233, by rfl⟩ : syracuseStep 8755289 = 6566467) B6566467
theorem B13498483 : Blo 1729065 13498483 := bstep (se 1 (by rfl) ⟨10123862, by rfl⟩ : syracuseStep 13498483 = 20247725) B20247725
theorem B3283067 : Blo 1729065 3283067 := bstep (se 1 (by rfl) ⟨2462300, by rfl⟩ : syracuseStep 3283067 = 4924601) B4924601
theorem B2594939 : Blo 1729065 2594939 := bstep (se 1 (by rfl) ⟨1946204, by rfl⟩ : syracuseStep 2594939 = 3892409) B3892409
theorem B5839019 : Blo 1729065 5839019 := bstep (se 1 (by rfl) ⟨4379264, by rfl⟩ : syracuseStep 5839019 = 8758529) B8758529
theorem B2595065 : Blo 1729065 2595065 := bstep (se 2 (by rfl) ⟨973149, by rfl⟩ : syracuseStep 2595065 = 1946299) B1946299
theorem B12466493 : Blo 1729065 12466493 := bstep (se 3 (by rfl) ⟨2337467, by rfl⟩ : syracuseStep 12466493 = 4674935) B4674935
theorem B2595167 : Blo 1729065 2595167 := bstep (se 1 (by rfl) ⟨1946375, by rfl⟩ : syracuseStep 2595167 = 3892751) B3892751
theorem B2595179 : Blo 1729065 2595179 := bstep (se 1 (by rfl) ⟨1946384, by rfl⟩ : syracuseStep 2595179 = 3892769) B3892769
theorem B4676059 : Blo 1729065 4676059 := bstep (se 1 (by rfl) ⟨3507044, by rfl⟩ : syracuseStep 4676059 = 7014089) B7014089
theorem B6568411 : Blo 1729065 6568411 := bstep (se 1 (by rfl) ⟨4926308, by rfl⟩ : syracuseStep 6568411 = 9852617) B9852617
theorem B23673421 : Blo 1729065 23673421 := bstep (se 3 (by rfl) ⟨4438766, by rfl⟩ : syracuseStep 23673421 = 8877533) B8877533
theorem B2595407 : Blo 1729065 2595407 := bstep (se 1 (by rfl) ⟨1946555, by rfl⟩ : syracuseStep 2595407 = 3893111) B3893111
theorem B3283553 : Blo 1729065 3283553 := bstep (se 2 (by rfl) ⟨1231332, by rfl⟩ : syracuseStep 3283553 = 2462665) B2462665
theorem B5839559 : Blo 1729065 5839559 := bstep (se 1 (by rfl) ⟨4379669, by rfl⟩ : syracuseStep 5839559 = 8759339) B8759339
theorem B2595527 : Blo 1729065 2595527 := bstep (se 1 (by rfl) ⟨1946645, by rfl⟩ : syracuseStep 2595527 = 3893291) B3893291
theorem B2464607 : Blo 1729065 2464607 := bstep (se 1 (by rfl) ⟨1848455, by rfl⟩ : syracuseStep 2464607 = 3696911) B3696911
theorem B2595689 : Blo 1729065 2595689 := bstep (se 2 (by rfl) ⟨973383, by rfl⟩ : syracuseStep 2595689 = 1946767) B1946767
theorem B5544865 : Blo 1729065 5544865 := bstep (se 2 (by rfl) ⟨2079324, by rfl⟩ : syracuseStep 5544865 = 4158649) B4158649
theorem B3283895 : Blo 1729065 3283895 := bstep (se 1 (by rfl) ⟨2462921, by rfl⟩ : syracuseStep 3283895 = 4925843) B4925843
theorem B2595767 : Blo 1729065 2595767 := bstep (se 1 (by rfl) ⟨1946825, by rfl⟩ : syracuseStep 2595767 = 3893651) B3893651
theorem B2595803 : Blo 1729065 2595803 := bstep (se 1 (by rfl) ⟨1946852, by rfl⟩ : syracuseStep 2595803 = 3893705) B3893705
theorem B4381715 : Blo 1729065 4381715 := bstep (se 1 (by rfl) ⟨3286286, by rfl⟩ : syracuseStep 4381715 = 6572573) B6572573
theorem B14777423 : Blo 1729065 14777423 := bstep (se 1 (by rfl) ⟨11083067, by rfl⟩ : syracuseStep 14777423 = 22166135) B22166135
theorem B4676687 : Blo 1729065 4676687 := bstep (se 1 (by rfl) ⟨3507515, by rfl⟩ : syracuseStep 4676687 = 7015031) B7015031
theorem B7011481 : Blo 1729065 7011481 := bstep (se 2 (by rfl) ⟨2629305, by rfl⟩ : syracuseStep 7011481 = 5258611) B5258611
theorem B16620835 : Blo 1729065 16620835 := bstep (se 1 (by rfl) ⟨12465626, by rfl⟩ : syracuseStep 16620835 = 24931253) B24931253
theorem B3284297 : Blo 1729065 3284297 := bstep (se 2 (by rfl) ⟨1231611, by rfl⟩ : syracuseStep 3284297 = 2463223) B2463223
theorem B3890537 : Blo 1729065 3890537 := bstep (se 2 (by rfl) ⟨1458951, by rfl⟩ : syracuseStep 3890537 = 2917903) B2917903
theorem B2596271 : Blo 1729065 2596271 := bstep (se 1 (by rfl) ⟨1947203, by rfl⟩ : syracuseStep 2596271 = 3894407) B3894407
theorem B15785459 : Blo 1729065 15785459 := bstep (se 1 (by rfl) ⟨11839094, by rfl⟩ : syracuseStep 15785459 = 23678189) B23678189
theorem B2596361 : Blo 1729065 2596361 := bstep (se 2 (by rfl) ⟨973635, by rfl⟩ : syracuseStep 2596361 = 1947271) B1947271
theorem B13139495 : Blo 1729065 13139495 := bstep (se 1 (by rfl) ⟨9854621, by rfl⟩ : syracuseStep 13139495 = 19709243) B19709243
theorem B5840423 : Blo 1729065 5840423 := bstep (se 1 (by rfl) ⟨4380317, by rfl⟩ : syracuseStep 5840423 = 8760635) B8760635
theorem B2596391 : Blo 1729065 2596391 := bstep (se 1 (by rfl) ⟨1947293, by rfl⟩ : syracuseStep 2596391 = 3894587) B3894587
theorem B11083351 : Blo 1729065 11083351 := bstep (se 1 (by rfl) ⟨8312513, by rfl⟩ : syracuseStep 11083351 = 16625027) B16625027
theorem B3694177 : Blo 1729065 3694177 := bstep (se 2 (by rfl) ⟨1385316, by rfl⟩ : syracuseStep 3694177 = 2770633) B2770633
theorem B14786171 : Blo 1729065 14786171 := bstep (se 1 (by rfl) ⟨11089628, by rfl⟩ : syracuseStep 14786171 = 22179257) B22179257
theorem B2596475 : Blo 1729065 2596475 := bstep (se 1 (by rfl) ⟨1947356, by rfl⟩ : syracuseStep 2596475 = 3894713) B3894713
theorem B5840531 : Blo 1729065 5840531 := bstep (se 1 (by rfl) ⟨4380398, by rfl⟩ : syracuseStep 5840531 = 8760797) B8760797
theorem B6569657 : Blo 1729065 6569657 := bstep (se 2 (by rfl) ⟨2463621, by rfl⟩ : syracuseStep 6569657 = 4927243) B4927243
theorem B6659783 : Blo 1729065 6659783 := bstep (se 1 (by rfl) ⟨4994837, by rfl⟩ : syracuseStep 6659783 = 9989675) B9989675
theorem B6569687 : Blo 1729065 6569687 := bstep (se 1 (by rfl) ⟨4927265, by rfl⟩ : syracuseStep 6569687 = 9854531) B9854531
theorem B5840747 : Blo 1729065 5840747 := bstep (se 1 (by rfl) ⟨4380560, by rfl⟩ : syracuseStep 5840747 = 8761121) B8761121
theorem B7389089 : Blo 1729065 7389089 := bstep (se 2 (by rfl) ⟨2770908, by rfl⟩ : syracuseStep 7389089 = 5541817) B5541817
theorem B5840801 : Blo 1729065 5840801 := bstep (se 2 (by rfl) ⟨2190300, by rfl⟩ : syracuseStep 5840801 = 4380601) B4380601
theorem B3891131 : Blo 1729065 3891131 := bstep (se 1 (by rfl) ⟨2918348, by rfl⟩ : syracuseStep 3891131 = 5836697) B5836697
theorem B42647651 : Blo 1729065 42647651 := bstep (se 1 (by rfl) ⟨31985738, by rfl⟩ : syracuseStep 42647651 = 63971477) B63971477
theorem B17997977 : Blo 1729065 17997977 := bstep (se 2 (by rfl) ⟨6749241, by rfl⟩ : syracuseStep 17997977 = 13498483) B13498483
theorem B32432339 : Blo 1729065 32432339 := bstep (se 1 (by rfl) ⟨24324254, by rfl⟩ : syracuseStep 32432339 = 48648509) B48648509
theorem B3891563 : Blo 1729065 3891563 := bstep (se 1 (by rfl) ⟨2918672, by rfl⟩ : syracuseStep 3891563 = 5837345) B5837345
theorem B3604961 : Blo 1729065 3604961 := bstep (se 2 (by rfl) ⟨1351860, by rfl⟩ : syracuseStep 3604961 = 2703721) B2703721
theorem B3891707 : Blo 1729065 3891707 := bstep (se 1 (by rfl) ⟨2918780, by rfl⟩ : syracuseStep 3891707 = 5837561) B5837561
theorem B1729087 : Blo 1729065 1729087 := bstep (se 1 (by rfl) ⟨1296815, by rfl⟩ : syracuseStep 1729087 = 2593631) B2593631
theorem B1729095 : Blo 1729065 1729095 := bstep (se 1 (by rfl) ⟨1296821, by rfl⟩ : syracuseStep 1729095 = 2593643) B2593643
theorem B3891833 : Blo 1729065 3891833 := bstep (se 2 (by rfl) ⟨1459437, by rfl⟩ : syracuseStep 3891833 = 2918875) B2918875
theorem B6234745 : Blo 1729065 6234745 := bstep (se 2 (by rfl) ⟨2338029, by rfl⟩ : syracuseStep 6234745 = 4676059) B4676059
theorem B8757881 : Blo 1729065 8757881 := bstep (se 2 (by rfl) ⟨3284205, by rfl⟩ : syracuseStep 8757881 = 6568411) B6568411
theorem B3891887 : Blo 1729065 3891887 := bstep (se 1 (by rfl) ⟨2918915, by rfl⟩ : syracuseStep 3891887 = 5837831) B5837831
theorem B3285679 : Blo 1729065 3285679 := bstep (se 1 (by rfl) ⟨2464259, by rfl⟩ : syracuseStep 3285679 = 4928519) B4928519
theorem B1729247 : Blo 1729065 1729247 := bstep (se 1 (by rfl) ⟨1296935, by rfl⟩ : syracuseStep 1729247 = 2593871) B2593871
theorem B3891959 : Blo 1729065 3891959 := bstep (se 1 (by rfl) ⟨2918969, by rfl⟩ : syracuseStep 3891959 = 5837939) B5837939
theorem B31564561 : Blo 1729065 31564561 := bstep (se 2 (by rfl) ⟨11836710, by rfl⟩ : syracuseStep 31564561 = 23673421) B23673421
theorem B1729327 : Blo 1729065 1729327 := bstep (se 1 (by rfl) ⟨1296995, by rfl⟩ : syracuseStep 1729327 = 2593991) B2593991
theorem B3285839 : Blo 1729065 3285839 := bstep (se 1 (by rfl) ⟨2464379, by rfl⟩ : syracuseStep 3285839 = 4928759) B4928759
theorem B9356141 : Blo 1729065 9356141 := bstep (se 3 (by rfl) ⟨1754276, by rfl⟩ : syracuseStep 9356141 = 3508553) B3508553
theorem B1729435 : Blo 1729065 1729435 := bstep (se 1 (by rfl) ⟨1297076, by rfl⟩ : syracuseStep 1729435 = 2594153) B2594153
theorem B3892139 : Blo 1729065 3892139 := bstep (se 1 (by rfl) ⟨2919104, by rfl⟩ : syracuseStep 3892139 = 5838209) B5838209
theorem B1729487 : Blo 1729065 1729487 := bstep (se 1 (by rfl) ⟨1297115, by rfl⟩ : syracuseStep 1729487 = 2594231) B2594231
theorem B1729511 : Blo 1729065 1729511 := bstep (se 1 (by rfl) ⟨1297133, by rfl⟩ : syracuseStep 1729511 = 2594267) B2594267
theorem B16622567 : Blo 1729065 16622567 := bstep (se 1 (by rfl) ⟨12466925, by rfl⟩ : syracuseStep 16622567 = 24933851) B24933851
theorem B9348311 : Blo 1729065 9348311 := bstep (se 1 (by rfl) ⟨7011233, by rfl⟩ : syracuseStep 9348311 = 14022467) B14022467
theorem B1729823 : Blo 1729065 1729823 := bstep (se 1 (by rfl) ⟨1297367, by rfl⟩ : syracuseStep 1729823 = 2594735) B2594735
theorem B56911157 : Blo 1729065 56911157 := bstep (se 5 (by rfl) ⟨2667710, by rfl⟩ : syracuseStep 56911157 = 5335421) B5335421
theorem B1729883 : Blo 1729065 1729883 := bstep (se 1 (by rfl) ⟨1297412, by rfl⟩ : syracuseStep 1729883 = 2594825) B2594825
theorem B4441439 : Blo 1729065 4441439 := bstep (se 1 (by rfl) ⟨3331079, by rfl⟩ : syracuseStep 4441439 = 6662159) B6662159
theorem B1729903 : Blo 1729065 1729903 := bstep (se 1 (by rfl) ⟨1297427, by rfl⟩ : syracuseStep 1729903 = 2594855) B2594855
theorem B9356705 : Blo 1729065 9356705 := bstep (se 2 (by rfl) ⟨3508764, by rfl⟩ : syracuseStep 9356705 = 7017529) B7017529
theorem B2188711 : Blo 1729065 2188711 := bstep (se 1 (by rfl) ⟨1641533, by rfl⟩ : syracuseStep 2188711 = 3283067) B3283067
theorem B1729959 : Blo 1729065 1729959 := bstep (se 1 (by rfl) ⟨1297469, by rfl⟩ : syracuseStep 1729959 = 2594939) B2594939
theorem B3892679 : Blo 1729065 3892679 := bstep (se 1 (by rfl) ⟨2919509, by rfl⟩ : syracuseStep 3892679 = 5839019) B5839019
theorem B1730043 : Blo 1729065 1730043 := bstep (se 1 (by rfl) ⟨1297532, by rfl⟩ : syracuseStep 1730043 = 2595065) B2595065
theorem B9348641 : Blo 1729065 9348641 := bstep (se 2 (by rfl) ⟨3505740, by rfl⟩ : syracuseStep 9348641 = 7011481) B7011481
theorem B3696185 : Blo 1729065 3696185 := bstep (se 2 (by rfl) ⟨1386069, by rfl⟩ : syracuseStep 3696185 = 2772139) B2772139
theorem B1730111 : Blo 1729065 1730111 := bstep (se 1 (by rfl) ⟨1297583, by rfl⟩ : syracuseStep 1730111 = 2595167) B2595167
theorem B1730119 : Blo 1729065 1730119 := bstep (se 1 (by rfl) ⟨1297589, by rfl⟩ : syracuseStep 1730119 = 2595179) B2595179
theorem B22161113 : Blo 1729065 22161113 := bstep (se 2 (by rfl) ⟨8310417, by rfl⟩ : syracuseStep 22161113 = 16620835) B16620835
theorem B1730271 : Blo 1729065 1730271 := bstep (se 1 (by rfl) ⟨1297703, by rfl⟩ : syracuseStep 1730271 = 2595407) B2595407
theorem B2189035 : Blo 1729065 2189035 := bstep (se 1 (by rfl) ⟨1641776, by rfl⟩ : syracuseStep 2189035 = 3283553) B3283553
theorem B3893039 : Blo 1729065 3893039 := bstep (se 1 (by rfl) ⟨2919779, by rfl⟩ : syracuseStep 3893039 = 5839559) B5839559
theorem B1730351 : Blo 1729065 1730351 := bstep (se 1 (by rfl) ⟨1297763, by rfl⟩ : syracuseStep 1730351 = 2595527) B2595527
theorem B1730459 : Blo 1729065 1730459 := bstep (se 1 (by rfl) ⟨1297844, by rfl⟩ : syracuseStep 1730459 = 2595689) B2595689
theorem B2189263 : Blo 1729065 2189263 := bstep (se 1 (by rfl) ⟨1641947, by rfl⟩ : syracuseStep 2189263 = 3283895) B3283895
theorem B2770895 : Blo 1729065 2770895 := bstep (se 1 (by rfl) ⟨2078171, by rfl⟩ : syracuseStep 2770895 = 4156343) B4156343
theorem B1730511 : Blo 1729065 1730511 := bstep (se 1 (by rfl) ⟨1297883, by rfl⟩ : syracuseStep 1730511 = 2595767) B2595767
theorem B1730535 : Blo 1729065 1730535 := bstep (se 1 (by rfl) ⟨1297901, by rfl⟩ : syracuseStep 1730535 = 2595803) B2595803
theorem B4925569 : Blo 1729065 4925569 := bstep (se 2 (by rfl) ⟨1847088, by rfl⟩ : syracuseStep 4925569 = 3694177) B3694177
theorem B2189531 : Blo 1729065 2189531 := bstep (se 1 (by rfl) ⟨1642148, by rfl⟩ : syracuseStep 2189531 = 3284297) B3284297
theorem B6572285 : Blo 1729065 6572285 := bstep (se 3 (by rfl) ⟨1232303, by rfl⟩ : syracuseStep 6572285 = 2464607) B2464607
theorem B7391513 : Blo 1729065 7391513 := bstep (se 2 (by rfl) ⟨2771817, by rfl⟩ : syracuseStep 7391513 = 5543635) B5543635
theorem B1730847 : Blo 1729065 1730847 := bstep (se 1 (by rfl) ⟨1298135, by rfl⟩ : syracuseStep 1730847 = 2596271) B2596271
theorem B2918747 : Blo 1729065 2918747 := bstep (se 1 (by rfl) ⟨2189060, by rfl⟩ : syracuseStep 2918747 = 4378121) B4378121
theorem B1730907 : Blo 1729065 1730907 := bstep (se 1 (by rfl) ⟨1298180, by rfl⟩ : syracuseStep 1730907 = 2596361) B2596361
theorem B2918767 : Blo 1729065 2918767 := bstep (se 1 (by rfl) ⟨2189075, by rfl⟩ : syracuseStep 2918767 = 4378151) B4378151
theorem B8759663 : Blo 1729065 8759663 := bstep (se 1 (by rfl) ⟨6569747, by rfl⟩ : syracuseStep 8759663 = 13139495) B13139495
theorem B3893615 : Blo 1729065 3893615 := bstep (se 1 (by rfl) ⟨2920211, by rfl⟩ : syracuseStep 3893615 = 5840423) B5840423
theorem B1730927 : Blo 1729065 1730927 := bstep (se 1 (by rfl) ⟨1298195, by rfl⟩ : syracuseStep 1730927 = 2596391) B2596391
theorem B14780839 : Blo 1729065 14780839 := bstep (se 1 (by rfl) ⟨11085629, by rfl⟩ : syracuseStep 14780839 = 22171259) B22171259
theorem B9857447 : Blo 1729065 9857447 := bstep (se 1 (by rfl) ⟨7393085, by rfl⟩ : syracuseStep 9857447 = 14786171) B14786171
theorem B1730983 : Blo 1729065 1730983 := bstep (se 1 (by rfl) ⟨1298237, by rfl⟩ : syracuseStep 1730983 = 2596475) B2596475
theorem B3893687 : Blo 1729065 3893687 := bstep (se 1 (by rfl) ⟨2920265, by rfl⟩ : syracuseStep 3893687 = 5840531) B5840531
theorem B11233765 : Blo 1729065 11233765 := bstep (se 4 (by rfl) ⟨1053165, by rfl⟩ : syracuseStep 11233765 = 2106331) B2106331
theorem B2918983 : Blo 1729065 2918983 := bstep (se 1 (by rfl) ⟨2189237, by rfl⟩ : syracuseStep 2918983 = 4378475) B4378475
theorem B3893831 : Blo 1729065 3893831 := bstep (se 1 (by rfl) ⟨2920373, by rfl⟩ : syracuseStep 3893831 = 5840747) B5840747
theorem B4926059 : Blo 1729065 4926059 := bstep (se 1 (by rfl) ⟨3694544, by rfl⟩ : syracuseStep 4926059 = 7389089) B7389089
theorem B3893867 : Blo 1729065 3893867 := bstep (se 1 (by rfl) ⟨2920400, by rfl⟩ : syracuseStep 3893867 = 5840801) B5840801
theorem B2190007 : Blo 1729065 2190007 := bstep (se 1 (by rfl) ⟨1642505, by rfl⟩ : syracuseStep 2190007 = 3285011) B3285011
theorem B36006589 : Blo 1729065 36006589 := bstep (se 3 (by rfl) ⟨6751235, by rfl⟩ : syracuseStep 36006589 = 13502471) B13502471
theorem B4377311 : Blo 1729065 4377311 := bstep (se 1 (by rfl) ⟨3282983, by rfl⟩ : syracuseStep 4377311 = 6565967) B6565967
theorem B2190235 : Blo 1729065 2190235 := bstep (se 1 (by rfl) ⟨1642676, by rfl⟩ : syracuseStep 2190235 = 3285353) B3285353
theorem B2919415 : Blo 1729065 2919415 := bstep (se 1 (by rfl) ⟨2189561, by rfl⟩ : syracuseStep 2919415 = 4379123) B4379123
theorem B3894263 : Blo 1729065 3894263 := bstep (se 1 (by rfl) ⟨2920697, by rfl⟩ : syracuseStep 3894263 = 5841395) B5841395
theorem B5835995 : Blo 1729065 5835995 := bstep (se 1 (by rfl) ⟨4376996, by rfl⟩ : syracuseStep 5835995 = 8753993) B8753993
theorem B2919719 : Blo 1729065 2919719 := bstep (se 1 (by rfl) ⟨2189789, by rfl⟩ : syracuseStep 2919719 = 4379579) B4379579
theorem B3894623 : Blo 1729065 3894623 := bstep (se 1 (by rfl) ⟨2920967, by rfl⟩ : syracuseStep 3894623 = 5841935) B5841935
theorem B37432691 : Blo 1729065 37432691 := bstep (se 1 (by rfl) ⟨28074518, by rfl⟩ : syracuseStep 37432691 = 56149037) B56149037
theorem B50580935 : Blo 1729065 50580935 := bstep (se 1 (by rfl) ⟨37935701, by rfl⟩ : syracuseStep 50580935 = 75871403) B75871403
theorem B49901021 : Blo 1729065 49901021 := bstep (se 3 (by rfl) ⟨9356441, by rfl⟩ : syracuseStep 49901021 = 18712883) B18712883
theorem B2920171 : Blo 1729065 2920171 := bstep (se 1 (by rfl) ⟨2190128, by rfl⟩ : syracuseStep 2920171 = 4380257) B4380257
theorem B5836859 : Blo 1729065 5836859 := bstep (se 1 (by rfl) ⟨4377644, by rfl⟩ : syracuseStep 5836859 = 8755289) B8755289
theorem B17756219 : Blo 1729065 17756219 := bstep (se 1 (by rfl) ⟨13317164, by rfl⟩ : syracuseStep 17756219 = 26634329) B26634329
theorem B8310995 : Blo 1729065 8310995 := bstep (se 1 (by rfl) ⟨6233246, by rfl⟩ : syracuseStep 8310995 = 12466493) B12466493
theorem B5837129 : Blo 1729065 5837129 := bstep (se 2 (by rfl) ⟨2188923, by rfl⟩ : syracuseStep 5837129 = 4377847) B4377847
theorem B2339209 : Blo 1729065 2339209 := bstep (se 2 (by rfl) ⟨877203, by rfl⟩ : syracuseStep 2339209 = 1754407) B1754407
theorem B12464761 : Blo 1729065 12464761 := bstep (se 2 (by rfl) ⟨4674285, by rfl⟩ : syracuseStep 12464761 = 9348571) B9348571
theorem B2462329 : Blo 1729065 2462329 := bstep (se 2 (by rfl) ⟨923373, by rfl⟩ : syracuseStep 2462329 = 1846747) B1846747
theorem B2921143 : Blo 1729065 2921143 := bstep (se 1 (by rfl) ⟨2190857, by rfl⟩ : syracuseStep 2921143 = 4381715) B4381715
theorem B9851615 : Blo 1729065 9851615 := bstep (se 1 (by rfl) ⟨7388711, by rfl⟩ : syracuseStep 9851615 = 14777423) B14777423
theorem B1946335 : Blo 1729065 1946335 := bstep (se 1 (by rfl) ⟨1459751, by rfl⟩ : syracuseStep 1946335 = 2919503) B2919503
theorem B3117791 : Blo 1729065 3117791 := bstep (se 1 (by rfl) ⟨2338343, by rfl⟩ : syracuseStep 3117791 = 4676687) B4676687
theorem B11088683 : Blo 1729065 11088683 := bstep (se 1 (by rfl) ⟨8316512, by rfl⟩ : syracuseStep 11088683 = 16633025) B16633025
theorem B2593691 : Blo 1729065 2593691 := bstep (se 1 (by rfl) ⟨1945268, by rfl⟩ : syracuseStep 2593691 = 3890537) B3890537
theorem B10523639 : Blo 1729065 10523639 := bstep (se 1 (by rfl) ⟨7892729, by rfl⟩ : syracuseStep 10523639 = 15785459) B15785459
theorem B4379771 : Blo 1729065 4379771 := bstep (se 1 (by rfl) ⟨3284828, by rfl⟩ : syracuseStep 4379771 = 6569657) B6569657
theorem B4379791 : Blo 1729065 4379791 := bstep (se 1 (by rfl) ⟨3284843, by rfl⟩ : syracuseStep 4379791 = 6569687) B6569687
theorem B11834525 : Blo 1729065 11834525 := bstep (se 3 (by rfl) ⟨2218973, by rfl⟩ : syracuseStep 11834525 = 4437947) B4437947
theorem B23663789 : Blo 1729065 23663789 := bstep (se 3 (by rfl) ⟨4436960, by rfl⟩ : syracuseStep 23663789 = 8873921) B8873921
theorem B1946911 : Blo 1729065 1946911 := bstep (se 1 (by rfl) ⟨1460183, by rfl⟩ : syracuseStep 1946911 = 2920367) B2920367
theorem B2594087 : Blo 1729065 2594087 := bstep (se 1 (by rfl) ⟨1945565, by rfl⟩ : syracuseStep 2594087 = 3891131) B3891131
theorem B7386491 : Blo 1729065 7386491 := bstep (se 1 (by rfl) ⟨5539868, by rfl⟩ : syracuseStep 7386491 = 11079737) B11079737
theorem B2594171 : Blo 1729065 2594171 := bstep (se 1 (by rfl) ⟨1945628, by rfl⟩ : syracuseStep 2594171 = 3891257) B3891257
theorem B16618877 : Blo 1729065 16618877 := bstep (se 3 (by rfl) ⟨3116039, by rfl⟩ : syracuseStep 16618877 = 6232079) B6232079
theorem B9852299 : Blo 1729065 9852299 := bstep (se 1 (by rfl) ⟨7389224, by rfl⟩ : syracuseStep 9852299 = 14778449) B14778449
theorem B4380065 : Blo 1729065 4380065 := bstep (se 2 (by rfl) ⟨1642524, by rfl⟩ : syracuseStep 4380065 = 3285049) B3285049
theorem B2594297 : Blo 1729065 2594297 := bstep (se 2 (by rfl) ⟨972861, by rfl⟩ : syracuseStep 2594297 = 1945723) B1945723
theorem B8312377 : Blo 1729065 8312377 := bstep (se 2 (by rfl) ⟨3117141, by rfl⟩ : syracuseStep 8312377 = 6234283) B6234283
theorem B1947199 : Blo 1729065 1947199 := bstep (se 1 (by rfl) ⟨1460399, by rfl⟩ : syracuseStep 1947199 = 2920799) B2920799
theorem B2594399 : Blo 1729065 2594399 := bstep (se 1 (by rfl) ⟨1945799, by rfl⟩ : syracuseStep 2594399 = 3891599) B3891599
theorem B2078383 : Blo 1729065 2078383 := bstep (se 1 (by rfl) ⟨1558787, by rfl⟩ : syracuseStep 2078383 = 3117575) B3117575
theorem B8763065 : Blo 1729065 8763065 := bstep (se 2 (by rfl) ⟨3286149, by rfl⟩ : syracuseStep 8763065 = 6572299) B6572299
theorem B3282619 : Blo 1729065 3282619 := bstep (se 1 (by rfl) ⟨2461964, by rfl⟩ : syracuseStep 3282619 = 4923929) B4923929
theorem B2594615 : Blo 1729065 2594615 := bstep (se 1 (by rfl) ⟨1945961, by rfl⟩ : syracuseStep 2594615 = 3891923) B3891923
theorem B8755127 : Blo 1729065 8755127 := bstep (se 1 (by rfl) ⟨6566345, by rfl⟩ : syracuseStep 8755127 = 13132691) B13132691
theorem B2594921 : Blo 1729065 2594921 := bstep (se 2 (by rfl) ⟨973095, by rfl⟩ : syracuseStep 2594921 = 1946191) B1946191
theorem B7886983 : Blo 1729065 7886983 := bstep (se 1 (by rfl) ⟨5915237, by rfl⟩ : syracuseStep 7886983 = 11830475) B11830475
theorem B2464111 : Blo 1729065 2464111 := bstep (se 1 (by rfl) ⟨1848083, by rfl⟩ : syracuseStep 2464111 = 3696167) B3696167
theorem B2595239 : Blo 1729065 2595239 := bstep (se 1 (by rfl) ⟨1946429, by rfl⟩ : syracuseStep 2595239 = 3892859) B3892859
theorem B2595323 : Blo 1729065 2595323 := bstep (se 1 (by rfl) ⟨1946492, by rfl⟩ : syracuseStep 2595323 = 3892985) B3892985
theorem B16636441 : Blo 1729065 16636441 := bstep (se 2 (by rfl) ⟨6238665, by rfl⟩ : syracuseStep 16636441 = 12477331) B12477331
theorem B8755775 : Blo 1729065 8755775 := bstep (se 1 (by rfl) ⟨6566831, by rfl⟩ : syracuseStep 8755775 = 13133663) B13133663
theorem B2595449 : Blo 1729065 2595449 := bstep (se 2 (by rfl) ⟨973293, by rfl⟩ : syracuseStep 2595449 = 1946587) B1946587
theorem B7387823 : Blo 1729065 7387823 := bstep (se 1 (by rfl) ⟨5540867, by rfl⟩ : syracuseStep 7387823 = 11081735) B11081735
theorem B2595503 : Blo 1729065 2595503 := bstep (se 1 (by rfl) ⟨1946627, by rfl⟩ : syracuseStep 2595503 = 3893255) B3893255
theorem B9485021 : Blo 1729065 9485021 := bstep (se 3 (by rfl) ⟨1778441, by rfl⟩ : syracuseStep 9485021 = 3556883) B3556883
theorem B2595551 : Blo 1729065 2595551 := bstep (se 1 (by rfl) ⟨1946663, by rfl⟩ : syracuseStep 2595551 = 3893327) B3893327
theorem B2595815 : Blo 1729065 2595815 := bstep (se 1 (by rfl) ⟨1946861, by rfl⟩ : syracuseStep 2595815 = 3893723) B3893723
theorem B4381735 : Blo 1729065 4381735 := bstep (se 1 (by rfl) ⟨3286301, by rfl⟩ : syracuseStep 4381735 = 6572603) B6572603
theorem B9854075 : Blo 1729065 9854075 := bstep (se 1 (by rfl) ⟨7390556, by rfl⟩ : syracuseStep 9854075 = 14781113) B14781113
theorem B2596073 : Blo 1729065 2596073 := bstep (se 2 (by rfl) ⟨973527, by rfl⟩ : syracuseStep 2596073 = 1947055) B1947055
theorem B2596127 : Blo 1729065 2596127 := bstep (se 1 (by rfl) ⟨1947095, by rfl⟩ : syracuseStep 2596127 = 3894191) B3894191
theorem B7888225 : Blo 1729065 7888225 := bstep (se 2 (by rfl) ⟨2958084, by rfl⟩ : syracuseStep 7888225 = 5916169) B5916169
theorem B3890555 : Blo 1729065 3890555 := bstep (se 1 (by rfl) ⟨2917916, by rfl⟩ : syracuseStep 3890555 = 5835833) B5835833
theorem B5840315 : Blo 1729065 5840315 := bstep (se 1 (by rfl) ⟨4380236, by rfl⟩ : syracuseStep 5840315 = 8760473) B8760473
theorem B2596295 : Blo 1729065 2596295 := bstep (se 1 (by rfl) ⟨1947221, by rfl⟩ : syracuseStep 2596295 = 3894443) B3894443
theorem B14777801 : Blo 1729065 14777801 := bstep (se 2 (by rfl) ⟨5541675, by rfl⟩ : syracuseStep 14777801 = 11083351) B11083351
theorem B3890681 : Blo 1729065 3890681 := bstep (se 2 (by rfl) ⟨1459005, by rfl⟩ : syracuseStep 3890681 = 2918011) B2918011
theorem B29572613 : Blo 1729065 29572613 := bstep (se 4 (by rfl) ⟨2772432, by rfl⟩ : syracuseStep 29572613 = 5544865) B5544865
theorem B3890771 : Blo 1729065 3890771 := bstep (se 1 (by rfl) ⟨2918078, by rfl⟩ : syracuseStep 3890771 = 5836157) B5836157
theorem B3284563 : Blo 1729065 3284563 := bstep (se 1 (by rfl) ⟨2463422, by rfl⟩ : syracuseStep 3284563 = 4926845) B4926845
theorem B24927905 : Blo 1729065 24927905 := bstep (se 2 (by rfl) ⟨9347964, by rfl⟩ : syracuseStep 24927905 = 18695929) B18695929
theorem B6659819 : Blo 1729065 6659819 := bstep (se 1 (by rfl) ⟨4994864, by rfl⟩ : syracuseStep 6659819 = 9989729) B9989729
theorem B3890951 : Blo 1729065 3890951 := bstep (se 1 (by rfl) ⟨2918213, by rfl⟩ : syracuseStep 3890951 = 5836427) B5836427
theorem B3284783 : Blo 1729065 3284783 := bstep (se 1 (by rfl) ⟨2463587, by rfl⟩ : syracuseStep 3284783 = 4927175) B4927175
theorem B4439855 : Blo 1729065 4439855 := bstep (se 1 (by rfl) ⟨3329891, by rfl⟩ : syracuseStep 4439855 = 6659783) B6659783
theorem B44965813 : Blo 1729065 44965813 := bstep (se 5 (by rfl) ⟨2107772, by rfl⟩ : syracuseStep 44965813 = 4215545) B4215545
theorem B3891239 : Blo 1729065 3891239 := bstep (se 1 (by rfl) ⟨2918429, by rfl⟩ : syracuseStep 3891239 = 5836859) B5836859
theorem B47349917 : Blo 1729065 47349917 := bstep (se 3 (by rfl) ⟨8878109, by rfl⟩ : syracuseStep 47349917 = 17756219) B17756219
theorem B3891419 : Blo 1729065 3891419 := bstep (se 1 (by rfl) ⟨2918564, by rfl⟩ : syracuseStep 3891419 = 5837129) B5837129
theorem B3891689 : Blo 1729065 3891689 := bstep (se 2 (by rfl) ⟨1459383, by rfl⟩ : syracuseStep 3891689 = 2918767) B2918767
theorem B24928829 : Blo 1729065 24928829 := bstep (se 3 (by rfl) ⟨4674155, by rfl⟩ : syracuseStep 24928829 = 9348311) B9348311
theorem B1729127 : Blo 1729065 1729127 := bstep (se 1 (by rfl) ⟨1296845, by rfl⟩ : syracuseStep 1729127 = 2593691) B2593691
theorem B19710701 : Blo 1729065 19710701 := bstep (se 3 (by rfl) ⟨3695756, by rfl⟩ : syracuseStep 19710701 = 7391513) B7391513
theorem B3891977 : Blo 1729065 3891977 := bstep (se 2 (by rfl) ⟨1459491, by rfl⟩ : syracuseStep 3891977 = 2918983) B2918983
theorem B7889683 : Blo 1729065 7889683 := bstep (se 1 (by rfl) ⟨5917262, by rfl⟩ : syracuseStep 7889683 = 11834525) B11834525
theorem B1729391 : Blo 1729065 1729391 := bstep (se 1 (by rfl) ⟨1297043, by rfl⟩ : syracuseStep 1729391 = 2594087) B2594087
theorem B4924327 : Blo 1729065 4924327 := bstep (se 1 (by rfl) ⟨3693245, by rfl⟩ : syracuseStep 4924327 = 7386491) B7386491
theorem B1729447 : Blo 1729065 1729447 := bstep (se 1 (by rfl) ⟨1297085, by rfl⟩ : syracuseStep 1729447 = 2594171) B2594171
theorem B1729531 : Blo 1729065 1729531 := bstep (se 1 (by rfl) ⟨1297148, by rfl⟩ : syracuseStep 1729531 = 2594297) B2594297
theorem B1729599 : Blo 1729065 1729599 := bstep (se 1 (by rfl) ⟨1297199, by rfl⟩ : syracuseStep 1729599 = 2594399) B2594399
theorem B5842043 : Blo 1729065 5842043 := bstep (se 1 (by rfl) ⟨4381532, by rfl⟩ : syracuseStep 5842043 = 8763065) B8763065
theorem B1729743 : Blo 1729065 1729743 := bstep (se 1 (by rfl) ⟨1297307, by rfl⟩ : syracuseStep 1729743 = 2594615) B2594615
theorem B3892553 : Blo 1729065 3892553 := bstep (se 2 (by rfl) ⟨1459707, by rfl⟩ : syracuseStep 3892553 = 2919415) B2919415
theorem B5842313 : Blo 1729065 5842313 := bstep (se 2 (by rfl) ⟨2190867, by rfl⟩ : syracuseStep 5842313 = 4381735) B4381735
theorem B1729947 : Blo 1729065 1729947 := bstep (se 1 (by rfl) ⟨1297460, by rfl⟩ : syracuseStep 1729947 = 2594921) B2594921
theorem B1730159 : Blo 1729065 1730159 := bstep (se 1 (by rfl) ⟨1297619, by rfl⟩ : syracuseStep 1730159 = 2595239) B2595239
theorem B6571631 : Blo 1729065 6571631 := bstep (se 1 (by rfl) ⟨4928723, by rfl⟩ : syracuseStep 6571631 = 9857447) B9857447
theorem B1730215 : Blo 1729065 1730215 := bstep (se 1 (by rfl) ⟨1297661, by rfl⟩ : syracuseStep 1730215 = 2595323) B2595323
theorem B1730299 : Blo 1729065 1730299 := bstep (se 1 (by rfl) ⟨1297724, by rfl⟩ : syracuseStep 1730299 = 2595449) B2595449
theorem B4925215 : Blo 1729065 4925215 := bstep (se 1 (by rfl) ⟨3693911, by rfl⟩ : syracuseStep 4925215 = 7387823) B7387823
theorem B1730335 : Blo 1729065 1730335 := bstep (se 1 (by rfl) ⟨1297751, by rfl⟩ : syracuseStep 1730335 = 2595503) B2595503
theorem B2918207 : Blo 1729065 2918207 := bstep (se 1 (by rfl) ⟨2188655, by rfl⟩ : syracuseStep 2918207 = 4377311) B4377311
theorem B1730367 : Blo 1729065 1730367 := bstep (se 1 (by rfl) ⟨1297775, by rfl⟩ : syracuseStep 1730367 = 2595551) B2595551
theorem B2918281 : Blo 1729065 2918281 := bstep (se 2 (by rfl) ⟨1094355, by rfl⟩ : syracuseStep 2918281 = 2188711) B2188711
theorem B13141925 : Blo 1729065 13141925 := bstep (se 4 (by rfl) ⟨1232055, by rfl⟩ : syracuseStep 13141925 = 2464111) B2464111
theorem B1730543 : Blo 1729065 1730543 := bstep (se 1 (by rfl) ⟨1297907, by rfl⟩ : syracuseStep 1730543 = 2595815) B2595815
theorem B11839613 : Blo 1729065 11839613 := bstep (se 3 (by rfl) ⟨2219927, by rfl⟩ : syracuseStep 11839613 = 4439855) B4439855
theorem B1730715 : Blo 1729065 1730715 := bstep (se 1 (by rfl) ⟨1298036, by rfl⟩ : syracuseStep 1730715 = 2596073) B2596073
theorem B1730751 : Blo 1729065 1730751 := bstep (se 1 (by rfl) ⟨1298063, by rfl⟩ : syracuseStep 1730751 = 2596127) B2596127
theorem B2771177 : Blo 1729065 2771177 := bstep (se 2 (by rfl) ⟨1039191, by rfl⟩ : syracuseStep 2771177 = 2078383) B2078383
theorem B24955127 : Blo 1729065 24955127 := bstep (se 1 (by rfl) ⟨18716345, by rfl⟩ : syracuseStep 24955127 = 37432691) B37432691
theorem B4376825 : Blo 1729065 4376825 := bstep (se 2 (by rfl) ⟨1641309, by rfl⟩ : syracuseStep 4376825 = 3282619) B3282619
theorem B3893543 : Blo 1729065 3893543 := bstep (se 1 (by rfl) ⟨2920157, by rfl⟩ : syracuseStep 3893543 = 5840315) B5840315
theorem B33720623 : Blo 1729065 33720623 := bstep (se 1 (by rfl) ⟨25290467, by rfl⟩ : syracuseStep 33720623 = 50580935) B50580935
theorem B1730863 : Blo 1729065 1730863 := bstep (se 1 (by rfl) ⟨1298147, by rfl⟩ : syracuseStep 1730863 = 2596295) B2596295
theorem B2918713 : Blo 1729065 2918713 := bstep (se 2 (by rfl) ⟨1094517, by rfl⟩ : syracuseStep 2918713 = 2189035) B2189035
theorem B3893561 : Blo 1729065 3893561 := bstep (se 2 (by rfl) ⟨1460085, by rfl⟩ : syracuseStep 3893561 = 2920171) B2920171
theorem B2189855 : Blo 1729065 2189855 := bstep (se 1 (by rfl) ⟨1642391, by rfl⟩ : syracuseStep 2189855 = 3284783) B3284783
theorem B2919017 : Blo 1729065 2919017 := bstep (se 2 (by rfl) ⟨1094631, by rfl⟩ : syracuseStep 2919017 = 2189263) B2189263
theorem B5540663 : Blo 1729065 5540663 := bstep (se 1 (by rfl) ⟨4155497, by rfl⟩ : syracuseStep 5540663 = 8310995) B8310995
theorem B2403307 : Blo 1729065 2403307 := bstep (se 1 (by rfl) ⟨1802480, by rfl⟩ : syracuseStep 2403307 = 3604961) B3604961
theorem B7392455 : Blo 1729065 7392455 := bstep (se 1 (by rfl) ⟨5544341, by rfl⟩ : syracuseStep 7392455 = 11088683) B11088683
theorem B86486237 : Blo 1729065 86486237 := bstep (se 3 (by rfl) ⟨16216169, by rfl⟩ : syracuseStep 86486237 = 32432339) B32432339
theorem B2190559 : Blo 1729065 2190559 := bstep (se 1 (by rfl) ⟨1642919, by rfl⟩ : syracuseStep 2190559 = 3285839) B3285839
theorem B6237427 : Blo 1729065 6237427 := bstep (se 1 (by rfl) ⟨4678070, by rfl⟩ : syracuseStep 6237427 = 9356141) B9356141
theorem B14978353 : Blo 1729065 14978353 := bstep (se 2 (by rfl) ⟨5616882, by rfl⟩ : syracuseStep 14978353 = 11233765) B11233765
theorem B2919847 : Blo 1729065 2919847 := bstep (se 1 (by rfl) ⟨2189885, by rfl⟩ : syracuseStep 2919847 = 4379771) B4379771
theorem B37940771 : Blo 1729065 37940771 := bstep (se 1 (by rfl) ⟨28455578, by rfl⟩ : syracuseStep 37940771 = 56911157) B56911157
theorem B2960959 : Blo 1729065 2960959 := bstep (se 1 (by rfl) ⟨2220719, by rfl⟩ : syracuseStep 2960959 = 4441439) B4441439
theorem B2920009 : Blo 1729065 2920009 := bstep (se 2 (by rfl) ⟨1095003, by rfl⟩ : syracuseStep 2920009 = 2190007) B2190007
theorem B3894857 : Blo 1729065 3894857 := bstep (se 2 (by rfl) ⟨1460571, by rfl⟩ : syracuseStep 3894857 = 2921143) B2921143
theorem B48008785 : Blo 1729065 48008785 := bstep (se 2 (by rfl) ⟨18003294, by rfl⟩ : syracuseStep 48008785 = 36006589) B36006589
theorem B11079251 : Blo 1729065 11079251 := bstep (se 1 (by rfl) ⟨8309438, by rfl⟩ : syracuseStep 11079251 = 16618877) B16618877
theorem B2920043 : Blo 1729065 2920043 := bstep (se 1 (by rfl) ⟨2190032, by rfl⟩ : syracuseStep 2920043 = 4380065) B4380065
theorem B6237803 : Blo 1729065 6237803 := bstep (se 1 (by rfl) ⟨4678352, by rfl⟩ : syracuseStep 6237803 = 9356705) B9356705
theorem B42086081 : Blo 1729065 42086081 := bstep (se 2 (by rfl) ⟨15782280, by rfl⟩ : syracuseStep 42086081 = 31564561) B31564561
theorem B14774075 : Blo 1729065 14774075 := bstep (se 1 (by rfl) ⟨11080556, by rfl⟩ : syracuseStep 14774075 = 22161113) B22161113
theorem B2920313 : Blo 1729065 2920313 := bstep (se 2 (by rfl) ⟨1095117, by rfl⟩ : syracuseStep 2920313 = 2190235) B2190235
theorem B5836751 : Blo 1729065 5836751 := bstep (se 1 (by rfl) ⟨4377563, by rfl⟩ : syracuseStep 5836751 = 8755127) B8755127
theorem B1945831 : Blo 1729065 1945831 := bstep (se 1 (by rfl) ⟨1459373, by rfl⟩ : syracuseStep 1945831 = 2918747) B2918747
theorem B5837183 : Blo 1729065 5837183 := bstep (se 1 (by rfl) ⟨4377887, by rfl⟩ : syracuseStep 5837183 = 8755775) B8755775
theorem B4379417 : Blo 1729065 4379417 := bstep (se 2 (by rfl) ⟨1642281, by rfl⟩ : syracuseStep 4379417 = 3284563) B3284563
theorem B1946479 : Blo 1729065 1946479 := bstep (se 1 (by rfl) ⟨1459859, by rfl⟩ : syracuseStep 1946479 = 2919719) B2919719
theorem B2593703 : Blo 1729065 2593703 := bstep (se 1 (by rfl) ⟨1945277, by rfl⟩ : syracuseStep 2593703 = 3890555) B3890555
theorem B9851867 : Blo 1729065 9851867 := bstep (se 1 (by rfl) ⟨7388900, by rfl⟩ : syracuseStep 9851867 = 14777801) B14777801
theorem B2593787 : Blo 1729065 2593787 := bstep (se 1 (by rfl) ⟨1945340, by rfl⟩ : syracuseStep 2593787 = 3890681) B3890681
theorem B19715075 : Blo 1729065 19715075 := bstep (se 1 (by rfl) ⟨14786306, by rfl⟩ : syracuseStep 19715075 = 29572613) B29572613
theorem B2593847 : Blo 1729065 2593847 := bstep (se 1 (by rfl) ⟨1945385, by rfl⟩ : syracuseStep 2593847 = 3890771) B3890771
theorem B16618603 : Blo 1729065 16618603 := bstep (se 1 (by rfl) ⟨12463952, by rfl⟩ : syracuseStep 16618603 = 24927905) B24927905
theorem B2593967 : Blo 1729065 2593967 := bstep (se 1 (by rfl) ⟨1945475, by rfl⟩ : syracuseStep 2593967 = 3890951) B3890951
theorem B59954417 : Blo 1729065 59954417 := bstep (se 2 (by rfl) ⟨22482906, by rfl⟩ : syracuseStep 59954417 = 44965813) B44965813
theorem B28063037 : Blo 1729065 28063037 := bstep (se 3 (by rfl) ⟨5261819, by rfl⟩ : syracuseStep 28063037 = 10523639) B10523639
theorem B28431767 : Blo 1729065 28431767 := bstep (se 1 (by rfl) ⟨21323825, by rfl⟩ : syracuseStep 28431767 = 42647651) B42647651
theorem B6567425 : Blo 1729065 6567425 := bstep (se 2 (by rfl) ⟨2462784, by rfl⟩ : syracuseStep 6567425 = 4925569) B4925569
theorem B10515977 : Blo 1729065 10515977 := bstep (se 2 (by rfl) ⟨3943491, by rfl⟩ : syracuseStep 10515977 = 7886983) B7886983
theorem B2594375 : Blo 1729065 2594375 := bstep (se 1 (by rfl) ⟨1945781, by rfl⟩ : syracuseStep 2594375 = 3891563) B3891563
theorem B2594471 : Blo 1729065 2594471 := bstep (se 1 (by rfl) ⟨1945853, by rfl⟩ : syracuseStep 2594471 = 3891707) B3891707
theorem B47994605 : Blo 1729065 47994605 := bstep (se 3 (by rfl) ⟨8998988, by rfl⟩ : syracuseStep 47994605 = 17997977) B17997977
theorem B2594555 : Blo 1729065 2594555 := bstep (se 1 (by rfl) ⟨1945916, by rfl⟩ : syracuseStep 2594555 = 3891833) B3891833
theorem B5838587 : Blo 1729065 5838587 := bstep (se 1 (by rfl) ⟨4378940, by rfl⟩ : syracuseStep 5838587 = 8757881) B8757881
theorem B2594591 : Blo 1729065 2594591 := bstep (se 1 (by rfl) ⟨1945943, by rfl⟩ : syracuseStep 2594591 = 3891887) B3891887
theorem B6567743 : Blo 1729065 6567743 := bstep (se 1 (by rfl) ⟨4925807, by rfl⟩ : syracuseStep 6567743 = 9851615) B9851615
theorem B2594639 : Blo 1729065 2594639 := bstep (se 1 (by rfl) ⟨1945979, by rfl⟩ : syracuseStep 2594639 = 3891959) B3891959
theorem B3118945 : Blo 1729065 3118945 := bstep (se 2 (by rfl) ⟨1169604, by rfl⟩ : syracuseStep 3118945 = 2339209) B2339209
theorem B19707785 : Blo 1729065 19707785 := bstep (se 2 (by rfl) ⟨7390419, by rfl⟩ : syracuseStep 19707785 = 14780839) B14780839
theorem B5838749 : Blo 1729065 5838749 := bstep (se 3 (by rfl) ⟨1094765, by rfl⟩ : syracuseStep 5838749 = 2189531) B2189531
theorem B2594759 : Blo 1729065 2594759 := bstep (se 1 (by rfl) ⟨1946069, by rfl⟩ : syracuseStep 2594759 = 3892139) B3892139
theorem B11081711 : Blo 1729065 11081711 := bstep (se 1 (by rfl) ⟨8311283, by rfl⟩ : syracuseStep 11081711 = 16622567) B16622567
theorem B22181921 : Blo 1729065 22181921 := bstep (se 2 (by rfl) ⟨8318220, by rfl⟩ : syracuseStep 22181921 = 16636441) B16636441
theorem B15775859 : Blo 1729065 15775859 := bstep (se 1 (by rfl) ⟨11831894, by rfl⟩ : syracuseStep 15775859 = 23663789) B23663789
theorem B16619681 : Blo 1729065 16619681 := bstep (se 2 (by rfl) ⟨6232380, by rfl⟩ : syracuseStep 16619681 = 12464761) B12464761
theorem B3283105 : Blo 1729065 3283105 := bstep (se 2 (by rfl) ⟨1231164, by rfl⟩ : syracuseStep 3283105 = 2462329) B2462329
theorem B8312993 : Blo 1729065 8312993 := bstep (se 2 (by rfl) ⟨3117372, by rfl⟩ : syracuseStep 8312993 = 6234745) B6234745
theorem B4380905 : Blo 1729065 4380905 := bstep (se 2 (by rfl) ⟨1642839, by rfl⟩ : syracuseStep 4380905 = 3285679) B3285679
theorem B6568199 : Blo 1729065 6568199 := bstep (se 1 (by rfl) ⟨4926149, by rfl⟩ : syracuseStep 6568199 = 9852299) B9852299
theorem B2595113 : Blo 1729065 2595113 := bstep (se 2 (by rfl) ⟨973167, by rfl⟩ : syracuseStep 2595113 = 1946335) B1946335
theorem B2595119 : Blo 1729065 2595119 := bstep (se 1 (by rfl) ⟨1946339, by rfl⟩ : syracuseStep 2595119 = 3892679) B3892679
theorem B6232427 : Blo 1729065 6232427 := bstep (se 1 (by rfl) ⟨4674320, by rfl⟩ : syracuseStep 6232427 = 9348641) B9348641
theorem B2464123 : Blo 1729065 2464123 := bstep (se 1 (by rfl) ⟨1848092, by rfl⟩ : syracuseStep 2464123 = 3696185) B3696185
theorem B2595359 : Blo 1729065 2595359 := bstep (se 1 (by rfl) ⟨1946519, by rfl⟩ : syracuseStep 2595359 = 3893039) B3893039
theorem B4381523 : Blo 1729065 4381523 := bstep (se 1 (by rfl) ⟨3286142, by rfl⟩ : syracuseStep 4381523 = 6572285) B6572285
theorem B5839721 : Blo 1729065 5839721 := bstep (se 2 (by rfl) ⟨2189895, by rfl⟩ : syracuseStep 5839721 = 4379791) B4379791
theorem B5839775 : Blo 1729065 5839775 := bstep (se 1 (by rfl) ⟨4379831, by rfl⟩ : syracuseStep 5839775 = 8759663) B8759663
theorem B2595743 : Blo 1729065 2595743 := bstep (se 1 (by rfl) ⟨1946807, by rfl⟩ : syracuseStep 2595743 = 3893615) B3893615
theorem B2595791 : Blo 1729065 2595791 := bstep (se 1 (by rfl) ⟨1946843, by rfl⟩ : syracuseStep 2595791 = 3893687) B3893687
theorem B2595881 : Blo 1729065 2595881 := bstep (se 2 (by rfl) ⟨973455, by rfl⟩ : syracuseStep 2595881 = 1946911) B1946911
theorem B2595887 : Blo 1729065 2595887 := bstep (se 1 (by rfl) ⟨1946915, by rfl⟩ : syracuseStep 2595887 = 3893831) B3893831
theorem B3284039 : Blo 1729065 3284039 := bstep (se 1 (by rfl) ⟨2463029, by rfl⟩ : syracuseStep 3284039 = 4926059) B4926059
theorem B2595911 : Blo 1729065 2595911 := bstep (se 1 (by rfl) ⟨1946933, by rfl⟩ : syracuseStep 2595911 = 3893867) B3893867
theorem B10517633 : Blo 1729065 10517633 := bstep (se 2 (by rfl) ⟨3944112, by rfl⟩ : syracuseStep 10517633 = 7888225) B7888225
theorem B6323347 : Blo 1729065 6323347 := bstep (se 1 (by rfl) ⟨4742510, by rfl⟩ : syracuseStep 6323347 = 9485021) B9485021
theorem B8314109 : Blo 1729065 8314109 := bstep (se 3 (by rfl) ⟨1558895, by rfl⟩ : syracuseStep 8314109 = 3117791) B3117791
theorem B2596175 : Blo 1729065 2596175 := bstep (se 1 (by rfl) ⟨1947131, by rfl⟩ : syracuseStep 2596175 = 3894263) B3894263
theorem B11083169 : Blo 1729065 11083169 := bstep (se 2 (by rfl) ⟨4156188, by rfl⟩ : syracuseStep 11083169 = 8312377) B8312377
theorem B6569383 : Blo 1729065 6569383 := bstep (se 1 (by rfl) ⟨4927037, by rfl⟩ : syracuseStep 6569383 = 9854075) B9854075
theorem B2596265 : Blo 1729065 2596265 := bstep (se 2 (by rfl) ⟨973599, by rfl⟩ : syracuseStep 2596265 = 1947199) B1947199
theorem B3890663 : Blo 1729065 3890663 := bstep (se 1 (by rfl) ⟨2917997, by rfl⟩ : syracuseStep 3890663 = 5835995) B5835995
theorem B2596415 : Blo 1729065 2596415 := bstep (se 1 (by rfl) ⟨1947311, by rfl⟩ : syracuseStep 2596415 = 3894623) B3894623
theorem B33267347 : Blo 1729065 33267347 := bstep (se 1 (by rfl) ⟨24950510, by rfl⟩ : syracuseStep 33267347 = 49901021) B49901021
theorem B4439879 : Blo 1729065 4439879 := bstep (se 1 (by rfl) ⟨3329909, by rfl⟩ : syracuseStep 4439879 = 6659819) B6659819
theorem B7389053 : Blo 1729065 7389053 := bstep (se 3 (by rfl) ⟨1385447, by rfl⟩ : syracuseStep 7389053 = 2770895) B2770895
theorem B3891455 : Blo 1729065 3891455 := bstep (se 1 (by rfl) ⟨2918591, by rfl⟩ : syracuseStep 3891455 = 5837183) B5837183
theorem B3891617 : Blo 1729065 3891617 := bstep (se 2 (by rfl) ⟨1459356, by rfl⟩ : syracuseStep 3891617 = 2918713) B2918713
theorem B13140467 : Blo 1729065 13140467 := bstep (se 1 (by rfl) ⟨9855350, by rfl⟩ : syracuseStep 13140467 = 19710701) B19710701
theorem B3285497 : Blo 1729065 3285497 := bstep (se 2 (by rfl) ⟨1232061, by rfl⟩ : syracuseStep 3285497 = 2464123) B2464123
theorem B7389805 : Blo 1729065 7389805 := bstep (se 3 (by rfl) ⟨1385588, by rfl⟩ : syracuseStep 7389805 = 2771177) B2771177
theorem B1729135 : Blo 1729065 1729135 := bstep (se 1 (by rfl) ⟨1296851, by rfl⟩ : syracuseStep 1729135 = 2593703) B2593703
theorem B1729191 : Blo 1729065 1729191 := bstep (se 1 (by rfl) ⟨1296893, by rfl⟩ : syracuseStep 1729191 = 2593787) B2593787
theorem B1729231 : Blo 1729065 1729231 := bstep (se 1 (by rfl) ⟨1296923, by rfl⟩ : syracuseStep 1729231 = 2593847) B2593847
theorem B1729311 : Blo 1729065 1729311 := bstep (se 1 (by rfl) ⟨1296983, by rfl⟩ : syracuseStep 1729311 = 2593967) B2593967
theorem B74834765 : Blo 1729065 74834765 := bstep (se 3 (by rfl) ⟨14031518, by rfl⟩ : syracuseStep 74834765 = 28063037) B28063037
theorem B39969611 : Blo 1729065 39969611 := bstep (se 1 (by rfl) ⟨29977208, by rfl⟩ : syracuseStep 39969611 = 59954417) B59954417
theorem B10519577 : Blo 1729065 10519577 := bstep (se 2 (by rfl) ⟨3944841, by rfl⟩ : syracuseStep 10519577 = 7889683) B7889683
theorem B1729583 : Blo 1729065 1729583 := bstep (se 1 (by rfl) ⟨1297187, by rfl⟩ : syracuseStep 1729583 = 2594375) B2594375
theorem B75818045 : Blo 1729065 75818045 := bstep (se 3 (by rfl) ⟨14215883, by rfl⟩ : syracuseStep 75818045 = 28431767) B28431767
theorem B1729647 : Blo 1729065 1729647 := bstep (se 1 (by rfl) ⟨1297235, by rfl⟩ : syracuseStep 1729647 = 2594471) B2594471
theorem B1729703 : Blo 1729065 1729703 := bstep (se 1 (by rfl) ⟨1297277, by rfl⟩ : syracuseStep 1729703 = 2594555) B2594555
theorem B3892391 : Blo 1729065 3892391 := bstep (se 1 (by rfl) ⟨2919293, by rfl⟩ : syracuseStep 3892391 = 5838587) B5838587
theorem B1729727 : Blo 1729065 1729727 := bstep (se 1 (by rfl) ⟨1297295, by rfl⟩ : syracuseStep 1729727 = 2594591) B2594591
theorem B1729759 : Blo 1729065 1729759 := bstep (se 1 (by rfl) ⟨1297319, by rfl⟩ : syracuseStep 1729759 = 2594639) B2594639
theorem B3892499 : Blo 1729065 3892499 := bstep (se 1 (by rfl) ⟨2919374, by rfl⟩ : syracuseStep 3892499 = 5838749) B5838749
theorem B1729839 : Blo 1729065 1729839 := bstep (se 1 (by rfl) ⟨1297379, by rfl⟩ : syracuseStep 1729839 = 2594759) B2594759
theorem B126289205 : Blo 1729065 126289205 := bstep (se 5 (by rfl) ⟨5919806, by rfl⟩ : syracuseStep 126289205 = 11839613) B11839613
theorem B3204409 : Blo 1729065 3204409 := bstep (se 2 (by rfl) ⟨1201653, by rfl⟩ : syracuseStep 3204409 = 2403307) B2403307
theorem B14787947 : Blo 1729065 14787947 := bstep (se 1 (by rfl) ⟨11090960, by rfl⟩ : syracuseStep 14787947 = 22181921) B22181921
theorem B2917883 : Blo 1729065 2917883 := bstep (se 1 (by rfl) ⟨2188412, by rfl⟩ : syracuseStep 2917883 = 4376825) B4376825
theorem B8431129 : Blo 1729065 8431129 := bstep (se 2 (by rfl) ⟨3161673, by rfl⟩ : syracuseStep 8431129 = 6323347) B6323347
theorem B1730075 : Blo 1729065 1730075 := bstep (se 1 (by rfl) ⟨1297556, by rfl⟩ : syracuseStep 1730075 = 2595113) B2595113
theorem B1730079 : Blo 1729065 1730079 := bstep (se 1 (by rfl) ⟨1297559, by rfl⟩ : syracuseStep 1730079 = 2595119) B2595119
theorem B22480415 : Blo 1729065 22480415 := bstep (se 1 (by rfl) ⟨16860311, by rfl⟩ : syracuseStep 22480415 = 33720623) B33720623
theorem B4154951 : Blo 1729065 4154951 := bstep (se 1 (by rfl) ⟨3116213, by rfl⟩ : syracuseStep 4154951 = 6232427) B6232427
theorem B8316569 : Blo 1729065 8316569 := bstep (se 2 (by rfl) ⟨3118713, by rfl⟩ : syracuseStep 8316569 = 6237427) B6237427
theorem B1730239 : Blo 1729065 1730239 := bstep (se 1 (by rfl) ⟨1297679, by rfl⟩ : syracuseStep 1730239 = 2595359) B2595359
theorem B8759177 : Blo 1729065 8759177 := bstep (se 2 (by rfl) ⟨3284691, by rfl⟩ : syracuseStep 8759177 = 6569383) B6569383
theorem B3893129 : Blo 1729065 3893129 := bstep (se 2 (by rfl) ⟨1459923, by rfl⟩ : syracuseStep 3893129 = 2919847) B2919847
theorem B3893147 : Blo 1729065 3893147 := bstep (se 1 (by rfl) ⟨2919860, by rfl⟩ : syracuseStep 3893147 = 5839721) B5839721
theorem B3893183 : Blo 1729065 3893183 := bstep (se 1 (by rfl) ⟨2919887, by rfl⟩ : syracuseStep 3893183 = 5839775) B5839775
theorem B1730495 : Blo 1729065 1730495 := bstep (se 1 (by rfl) ⟨1297871, by rfl⟩ : syracuseStep 1730495 = 2595743) B2595743
theorem B1730527 : Blo 1729065 1730527 := bstep (se 1 (by rfl) ⟨1297895, by rfl⟩ : syracuseStep 1730527 = 2595791) B2595791
theorem B1730587 : Blo 1729065 1730587 := bstep (se 1 (by rfl) ⟨1297940, by rfl⟩ : syracuseStep 1730587 = 2595881) B2595881
theorem B1730591 : Blo 1729065 1730591 := bstep (se 1 (by rfl) ⟨1297943, by rfl⟩ : syracuseStep 1730591 = 2595887) B2595887
theorem B2189359 : Blo 1729065 2189359 := bstep (se 1 (by rfl) ⟨1642019, by rfl⟩ : syracuseStep 2189359 = 3284039) B3284039
theorem B1730607 : Blo 1729065 1730607 := bstep (se 1 (by rfl) ⟨1297955, by rfl⟩ : syracuseStep 1730607 = 2595911) B2595911
theorem B3893345 : Blo 1729065 3893345 := bstep (se 2 (by rfl) ⟨1460004, by rfl⟩ : syracuseStep 3893345 = 2920009) B2920009
theorem B57657491 : Blo 1729065 57657491 := bstep (se 1 (by rfl) ⟨43243118, by rfl⟩ : syracuseStep 57657491 = 86486237) B86486237
theorem B1730783 : Blo 1729065 1730783 := bstep (se 1 (by rfl) ⟨1298087, by rfl⟩ : syracuseStep 1730783 = 2596175) B2596175
theorem B1730843 : Blo 1729065 1730843 := bstep (se 1 (by rfl) ⟨1298132, by rfl⟩ : syracuseStep 1730843 = 2596265) B2596265
theorem B1730943 : Blo 1729065 1730943 := bstep (se 1 (by rfl) ⟨1298207, by rfl⟩ : syracuseStep 1730943 = 2596415) B2596415
theorem B22178231 : Blo 1729065 22178231 := bstep (se 1 (by rfl) ⟨16633673, by rfl⟩ : syracuseStep 22178231 = 33267347) B33267347
theorem B9849383 : Blo 1729065 9849383 := bstep (se 1 (by rfl) ⟨7387037, by rfl⟩ : syracuseStep 9849383 = 14774075) B14774075
theorem B2959919 : Blo 1729065 2959919 := bstep (se 1 (by rfl) ⟨2219939, by rfl⟩ : syracuseStep 2959919 = 4439879) B4439879
theorem B4926035 : Blo 1729065 4926035 := bstep (se 1 (by rfl) ⟨3694526, by rfl⟩ : syracuseStep 4926035 = 7389053) B7389053
theorem B31566611 : Blo 1729065 31566611 := bstep (se 1 (by rfl) ⟨23674958, by rfl⟩ : syracuseStep 31566611 = 47349917) B47349917
theorem B4377473 : Blo 1729065 4377473 := bstep (se 2 (by rfl) ⟨1641552, by rfl⟩ : syracuseStep 4377473 = 3283105) B3283105
theorem B2919611 : Blo 1729065 2919611 := bstep (se 1 (by rfl) ⟨2189708, by rfl⟩ : syracuseStep 2919611 = 4379417) B4379417
theorem B13143383 : Blo 1729065 13143383 := bstep (se 1 (by rfl) ⟨9857537, by rfl⟩ : syracuseStep 13143383 = 19715075) B19715075
theorem B3894695 : Blo 1729065 3894695 := bstep (se 1 (by rfl) ⟨2921021, by rfl⟩ : syracuseStep 3894695 = 5842043) B5842043
theorem B3894875 : Blo 1729065 3894875 := bstep (se 1 (by rfl) ⟨2921156, by rfl⟩ : syracuseStep 3894875 = 5842313) B5842313
theorem B4378283 : Blo 1729065 4378283 := bstep (se 1 (by rfl) ⟨3283712, by rfl⟩ : syracuseStep 4378283 = 6567425) B6567425
theorem B1945471 : Blo 1729065 1945471 := bstep (se 1 (by rfl) ⟨1459103, by rfl⟩ : syracuseStep 1945471 = 2918207) B2918207
theorem B4378495 : Blo 1729065 4378495 := bstep (se 1 (by rfl) ⟨3283871, by rfl⟩ : syracuseStep 4378495 = 6567743) B6567743
theorem B6565769 : Blo 1729065 6565769 := bstep (se 2 (by rfl) ⟨2462163, by rfl⟩ : syracuseStep 6565769 = 4924327) B4924327
theorem B8761283 : Blo 1729065 8761283 := bstep (se 1 (by rfl) ⟨6570962, by rfl⟩ : syracuseStep 8761283 = 13141925) B13141925
theorem B101175389 : Blo 1729065 101175389 := bstep (se 3 (by rfl) ⟨18970385, by rfl⟩ : syracuseStep 101175389 = 37940771) B37940771
theorem B11079787 : Blo 1729065 11079787 := bstep (se 1 (by rfl) ⟨8309840, by rfl⟩ : syracuseStep 11079787 = 16619681) B16619681
theorem B5541995 : Blo 1729065 5541995 := bstep (se 1 (by rfl) ⟨4156496, by rfl⟩ : syracuseStep 5541995 = 8312993) B8312993
theorem B2920603 : Blo 1729065 2920603 := bstep (se 1 (by rfl) ⟨2190452, by rfl⟩ : syracuseStep 2920603 = 4380905) B4380905
theorem B4378799 : Blo 1729065 4378799 := bstep (se 1 (by rfl) ⟨3284099, by rfl⟩ : syracuseStep 4378799 = 6568199) B6568199
theorem B2920745 : Blo 1729065 2920745 := bstep (se 2 (by rfl) ⟨1095279, by rfl⟩ : syracuseStep 2920745 = 2190559) B2190559
theorem B1946011 : Blo 1729065 1946011 := bstep (se 1 (by rfl) ⟨1459508, by rfl⟩ : syracuseStep 1946011 = 2919017) B2919017
theorem B2921015 : Blo 1729065 2921015 := bstep (se 1 (by rfl) ⟨2190761, by rfl⟩ : syracuseStep 2921015 = 4381523) B4381523
theorem B4928303 : Blo 1729065 4928303 := bstep (se 1 (by rfl) ⟨3696227, by rfl⟩ : syracuseStep 4928303 = 7392455) B7392455
theorem B5542739 : Blo 1729065 5542739 := bstep (se 1 (by rfl) ⟨4157054, by rfl⟩ : syracuseStep 5542739 = 8314109) B8314109
theorem B2593775 : Blo 1729065 2593775 := bstep (se 1 (by rfl) ⟨1945331, by rfl⟩ : syracuseStep 2593775 = 3890663) B3890663
theorem B6566953 : Blo 1729065 6566953 := bstep (se 2 (by rfl) ⟨2462607, by rfl⟩ : syracuseStep 6566953 = 4925215) B4925215
theorem B7386167 : Blo 1729065 7386167 := bstep (se 1 (by rfl) ⟨5539625, by rfl⟩ : syracuseStep 7386167 = 11079251) B11079251
theorem B1946695 : Blo 1729065 1946695 := bstep (se 1 (by rfl) ⟨1460021, by rfl⟩ : syracuseStep 1946695 = 2920043) B2920043
theorem B4158535 : Blo 1729065 4158535 := bstep (se 1 (by rfl) ⟨3118901, by rfl⟩ : syracuseStep 4158535 = 6237803) B6237803
theorem B4158593 : Blo 1729065 4158593 := bstep (se 2 (by rfl) ⟨1559472, by rfl⟩ : syracuseStep 4158593 = 3118945) B3118945
theorem B1946875 : Blo 1729065 1946875 := bstep (se 1 (by rfl) ⟨1460156, by rfl⟩ : syracuseStep 1946875 = 2920313) B2920313
theorem B2594159 : Blo 1729065 2594159 := bstep (se 1 (by rfl) ⟨1945619, by rfl⟩ : syracuseStep 2594159 = 3891239) B3891239
theorem B2594279 : Blo 1729065 2594279 := bstep (se 1 (by rfl) ⟨1945709, by rfl⟩ : syracuseStep 2594279 = 3891419) B3891419
theorem B2594441 : Blo 1729065 2594441 := bstep (se 2 (by rfl) ⟨972915, by rfl⟩ : syracuseStep 2594441 = 1945831) B1945831
theorem B2594459 : Blo 1729065 2594459 := bstep (se 1 (by rfl) ⟨1945844, by rfl⟩ : syracuseStep 2594459 = 3891689) B3891689
theorem B16619219 : Blo 1729065 16619219 := bstep (se 1 (by rfl) ⟨12464414, by rfl⟩ : syracuseStep 16619219 = 24928829) B24928829
theorem B2594651 : Blo 1729065 2594651 := bstep (se 1 (by rfl) ⟨1945988, by rfl⟩ : syracuseStep 2594651 = 3891977) B3891977
theorem B6567911 : Blo 1729065 6567911 := bstep (se 1 (by rfl) ⟨4925933, by rfl⟩ : syracuseStep 6567911 = 9851867) B9851867
theorem B2595035 : Blo 1729065 2595035 := bstep (se 1 (by rfl) ⟨1946276, by rfl⟩ : syracuseStep 2595035 = 3892553) B3892553
theorem B7010651 : Blo 1729065 7010651 := bstep (se 1 (by rfl) ⟨5257988, by rfl⟩ : syracuseStep 7010651 = 10515977) B10515977
theorem B4381087 : Blo 1729065 4381087 := bstep (se 1 (by rfl) ⟨3285815, by rfl⟩ : syracuseStep 4381087 = 6571631) B6571631
theorem B29555117 : Blo 1729065 29555117 := bstep (se 3 (by rfl) ⟨5541584, by rfl⟩ : syracuseStep 29555117 = 11083169) B11083169
theorem B2595305 : Blo 1729065 2595305 := bstep (se 2 (by rfl) ⟨973239, by rfl⟩ : syracuseStep 2595305 = 1946479) B1946479
theorem B31996403 : Blo 1729065 31996403 := bstep (se 1 (by rfl) ⟨23997302, by rfl⟩ : syracuseStep 31996403 = 47994605) B47994605
theorem B13138523 : Blo 1729065 13138523 := bstep (se 1 (by rfl) ⟨9853892, by rfl⟩ : syracuseStep 13138523 = 19707785) B19707785
theorem B7387807 : Blo 1729065 7387807 := bstep (se 1 (by rfl) ⟨5540855, by rfl⟩ : syracuseStep 7387807 = 11081711) B11081711
theorem B10517239 : Blo 1729065 10517239 := bstep (se 1 (by rfl) ⟨7887929, by rfl⟩ : syracuseStep 10517239 = 15775859) B15775859
theorem B5839613 : Blo 1729065 5839613 := bstep (se 3 (by rfl) ⟨1094927, by rfl⟩ : syracuseStep 5839613 = 2189855) B2189855
theorem B22158137 : Blo 1729065 22158137 := bstep (se 2 (by rfl) ⟨8309301, by rfl⟩ : syracuseStep 22158137 = 16618603) B16618603
theorem B16636751 : Blo 1729065 16636751 := bstep (se 1 (by rfl) ⟨12477563, by rfl⟩ : syracuseStep 16636751 = 24955127) B24955127
theorem B2595695 : Blo 1729065 2595695 := bstep (se 1 (by rfl) ⟨1946771, by rfl⟩ : syracuseStep 2595695 = 3893543) B3893543
theorem B2595707 : Blo 1729065 2595707 := bstep (se 1 (by rfl) ⟨1946780, by rfl⟩ : syracuseStep 2595707 = 3893561) B3893561
theorem B19971137 : Blo 1729065 19971137 := bstep (se 2 (by rfl) ⟨7489176, by rfl⟩ : syracuseStep 19971137 = 14978353) B14978353
theorem B112229549 : Blo 1729065 112229549 := bstep (se 3 (by rfl) ⟨21043040, by rfl⟩ : syracuseStep 112229549 = 42086081) B42086081
theorem B3693775 : Blo 1729065 3693775 := bstep (se 1 (by rfl) ⟨2770331, by rfl⟩ : syracuseStep 3693775 = 5540663) B5540663
theorem B3947945 : Blo 1729065 3947945 := bstep (se 2 (by rfl) ⟨1480479, by rfl⟩ : syracuseStep 3947945 = 2960959) B2960959
theorem B7011755 : Blo 1729065 7011755 := bstep (se 1 (by rfl) ⟨5258816, by rfl⟩ : syracuseStep 7011755 = 10517633) B10517633
theorem B64011713 : Blo 1729065 64011713 := bstep (se 2 (by rfl) ⟨24004392, by rfl⟩ : syracuseStep 64011713 = 48008785) B48008785
theorem B2596571 : Blo 1729065 2596571 := bstep (se 1 (by rfl) ⟨1947428, by rfl⟩ : syracuseStep 2596571 = 3894857) B3894857
theorem B3891041 : Blo 1729065 3891041 := bstep (se 2 (by rfl) ⟨1459140, by rfl⟩ : syracuseStep 3891041 = 2918281) B2918281
theorem B3891167 : Blo 1729065 3891167 := bstep (se 1 (by rfl) ⟨2918375, by rfl⟩ : syracuseStep 3891167 = 5836751) B5836751
theorem B3694663 : Blo 1729065 3694663 := bstep (se 1 (by rfl) ⟨2770997, by rfl⟩ : syracuseStep 3694663 = 5541995) B5541995
theorem B3285535 : Blo 1729065 3285535 := bstep (se 1 (by rfl) ⟨2464151, by rfl⟩ : syracuseStep 3285535 = 4928303) B4928303
theorem B5841449 : Blo 1729065 5841449 := bstep (se 2 (by rfl) ⟨2190543, by rfl⟩ : syracuseStep 5841449 = 4381087) B4381087
theorem B49889843 : Blo 1729065 49889843 := bstep (se 1 (by rfl) ⟨37417382, by rfl⟩ : syracuseStep 49889843 = 74834765) B74834765
theorem B3695159 : Blo 1729065 3695159 := bstep (se 1 (by rfl) ⟨2771369, by rfl⟩ : syracuseStep 3695159 = 5542739) B5542739
theorem B1729183 : Blo 1729065 1729183 := bstep (se 1 (by rfl) ⟨1296887, by rfl⟩ : syracuseStep 1729183 = 2593775) B2593775
theorem B7013051 : Blo 1729065 7013051 := bstep (se 1 (by rfl) ⟨5259788, by rfl⟩ : syracuseStep 7013051 = 10519577) B10519577
theorem B4924111 : Blo 1729065 4924111 := bstep (se 1 (by rfl) ⟨3693083, by rfl⟩ : syracuseStep 4924111 = 7386167) B7386167
theorem B18695069 : Blo 1729065 18695069 := bstep (se 3 (by rfl) ⟨3505325, by rfl⟩ : syracuseStep 18695069 = 7010651) B7010651
theorem B1729439 : Blo 1729065 1729439 := bstep (se 1 (by rfl) ⟨1297079, by rfl⟩ : syracuseStep 1729439 = 2594159) B2594159
theorem B1729519 : Blo 1729065 1729519 := bstep (se 1 (by rfl) ⟨1297139, by rfl⟩ : syracuseStep 1729519 = 2594279) B2594279
theorem B2769967 : Blo 1729065 2769967 := bstep (se 1 (by rfl) ⟨2077475, by rfl⟩ : syracuseStep 2769967 = 4154951) B4154951
theorem B1729627 : Blo 1729065 1729627 := bstep (se 1 (by rfl) ⟨1297220, by rfl⟩ : syracuseStep 1729627 = 2594441) B2594441
theorem B1729639 : Blo 1729065 1729639 := bstep (se 1 (by rfl) ⟨1297229, by rfl⟩ : syracuseStep 1729639 = 2594459) B2594459
theorem B10527853 : Blo 1729065 10527853 := bstep (se 3 (by rfl) ⟨1973972, by rfl⟩ : syracuseStep 10527853 = 3947945) B3947945
theorem B170697901 : Blo 1729065 170697901 := bstep (se 3 (by rfl) ⟨32005856, by rfl⟩ : syracuseStep 170697901 = 64011713) B64011713
theorem B1729767 : Blo 1729065 1729767 := bstep (se 1 (by rfl) ⟨1297325, by rfl⟩ : syracuseStep 1729767 = 2594651) B2594651
theorem B38438327 : Blo 1729065 38438327 := bstep (se 1 (by rfl) ⟨28828745, by rfl⟩ : syracuseStep 38438327 = 57657491) B57657491
theorem B1730023 : Blo 1729065 1730023 := bstep (se 1 (by rfl) ⟨1297517, by rfl⟩ : syracuseStep 1730023 = 2595035) B2595035
theorem B4925033 : Blo 1729065 4925033 := bstep (se 2 (by rfl) ⟨1846887, by rfl⟩ : syracuseStep 4925033 = 3693775) B3693775
theorem B19703411 : Blo 1729065 19703411 := bstep (se 1 (by rfl) ⟨14777558, by rfl⟩ : syracuseStep 19703411 = 29555117) B29555117
theorem B1730203 : Blo 1729065 1730203 := bstep (se 1 (by rfl) ⟨1297652, by rfl⟩ : syracuseStep 1730203 = 2595305) B2595305
theorem B8759015 : Blo 1729065 8759015 := bstep (se 1 (by rfl) ⟨6569261, by rfl⟩ : syracuseStep 8759015 = 13138523) B13138523
theorem B3893075 : Blo 1729065 3893075 := bstep (se 1 (by rfl) ⟨2919806, by rfl⟩ : syracuseStep 3893075 = 5839613) B5839613
theorem B14772091 : Blo 1729065 14772091 := bstep (se 1 (by rfl) ⟨11079068, by rfl⟩ : syracuseStep 14772091 = 22158137) B22158137
theorem B1730463 : Blo 1729065 1730463 := bstep (se 1 (by rfl) ⟨1297847, by rfl⟩ : syracuseStep 1730463 = 2595695) B2595695
theorem B1730471 : Blo 1729065 1730471 := bstep (se 1 (by rfl) ⟨1297853, by rfl⟩ : syracuseStep 1730471 = 2595707) B2595707
theorem B2918315 : Blo 1729065 2918315 := bstep (se 1 (by rfl) ⟨2188736, by rfl⟩ : syracuseStep 2918315 = 4377473) B4377473
theorem B11241505 : Blo 1729065 11241505 := bstep (se 2 (by rfl) ⟨4215564, by rfl⟩ : syracuseStep 11241505 = 8431129) B8431129
theorem B13314091 : Blo 1729065 13314091 := bstep (se 1 (by rfl) ⟨9985568, by rfl⟩ : syracuseStep 13314091 = 19971137) B19971137
theorem B74819699 : Blo 1729065 74819699 := bstep (se 1 (by rfl) ⟨56114774, by rfl⟩ : syracuseStep 74819699 = 112229549) B112229549
theorem B2918855 : Blo 1729065 2918855 := bstep (se 1 (by rfl) ⟨2189141, by rfl⟩ : syracuseStep 2918855 = 4378283) B4378283
theorem B1731047 : Blo 1729065 1731047 := bstep (se 1 (by rfl) ⟨1298285, by rfl⟩ : syracuseStep 1731047 = 2596571) B2596571
theorem B4377179 : Blo 1729065 4377179 := bstep (se 1 (by rfl) ⟨3282884, by rfl⟩ : syracuseStep 4377179 = 6565769) B6565769
theorem B2919145 : Blo 1729065 2919145 := bstep (se 2 (by rfl) ⟨1094679, by rfl⟩ : syracuseStep 2919145 = 2189359) B2189359
theorem B2919199 : Blo 1729065 2919199 := bstep (se 1 (by rfl) ⟨2189399, by rfl⟩ : syracuseStep 2919199 = 4378799) B4378799
theorem B14773049 : Blo 1729065 14773049 := bstep (se 2 (by rfl) ⟨5539893, by rfl⟩ : syracuseStep 14773049 = 11079787) B11079787
theorem B202181453 : Blo 1729065 202181453 := bstep (se 3 (by rfl) ⟨37909022, by rfl⟩ : syracuseStep 202181453 = 75818045) B75818045
theorem B3894137 : Blo 1729065 3894137 := bstep (se 2 (by rfl) ⟨1460301, by rfl⟩ : syracuseStep 3894137 = 2920603) B2920603
theorem B8760311 : Blo 1729065 8760311 := bstep (se 1 (by rfl) ⟨6570233, by rfl⟩ : syracuseStep 8760311 = 13140467) B13140467
theorem B2190331 : Blo 1729065 2190331 := bstep (se 1 (by rfl) ⟨1642748, by rfl⟩ : syracuseStep 2190331 = 3285497) B3285497
theorem B2772395 : Blo 1729065 2772395 := bstep (se 1 (by rfl) ⟨2079296, by rfl⟩ : syracuseStep 2772395 = 4158593) B4158593
theorem B84192803 : Blo 1729065 84192803 := bstep (se 1 (by rfl) ⟨63144602, by rfl⟩ : syracuseStep 84192803 = 126289205) B126289205
theorem B9850409 : Blo 1729065 9850409 := bstep (se 2 (by rfl) ⟨3693903, by rfl⟩ : syracuseStep 9850409 = 7387807) B7387807
theorem B9858631 : Blo 1729065 9858631 := bstep (se 1 (by rfl) ⟨7393973, by rfl⟩ : syracuseStep 9858631 = 14787947) B14787947
theorem B1945255 : Blo 1729065 1945255 := bstep (se 1 (by rfl) ⟨1458941, by rfl⟩ : syracuseStep 1945255 = 2917883) B2917883
theorem B14986943 : Blo 1729065 14986943 := bstep (se 1 (by rfl) ⟨11240207, by rfl⟩ : syracuseStep 14986943 = 22480415) B22480415
theorem B11079479 : Blo 1729065 11079479 := bstep (se 1 (by rfl) ⟨8309609, by rfl⟩ : syracuseStep 11079479 = 16619219) B16619219
theorem B4378607 : Blo 1729065 4378607 := bstep (se 1 (by rfl) ⟨3283955, by rfl⟩ : syracuseStep 4378607 = 6567911) B6567911
theorem B13136093 : Blo 1729065 13136093 := bstep (se 3 (by rfl) ⟨2463017, by rfl⟩ : syracuseStep 13136093 = 4926035) B4926035
theorem B6566255 : Blo 1729065 6566255 := bstep (se 1 (by rfl) ⟨4924691, by rfl⟩ : syracuseStep 6566255 = 9849383) B9849383
theorem B4272545 : Blo 1729065 4272545 := bstep (se 2 (by rfl) ⟨1602204, by rfl⟩ : syracuseStep 4272545 = 3204409) B3204409
theorem B84177629 : Blo 1729065 84177629 := bstep (se 3 (by rfl) ⟨15783305, by rfl⟩ : syracuseStep 84177629 = 31566611) B31566611
theorem B1946407 : Blo 1729065 1946407 := bstep (se 1 (by rfl) ⟨1459805, by rfl⟩ : syracuseStep 1946407 = 2919611) B2919611
theorem B8762255 : Blo 1729065 8762255 := bstep (se 1 (by rfl) ⟨6571691, by rfl⟩ : syracuseStep 8762255 = 13143383) B13143383
theorem B4674503 : Blo 1729065 4674503 := bstep (se 1 (by rfl) ⟨3505877, by rfl⟩ : syracuseStep 4674503 = 7011755) B7011755
theorem B2593961 : Blo 1729065 2593961 := bstep (se 2 (by rfl) ⟨972735, by rfl⟩ : syracuseStep 2593961 = 1945471) B1945471
theorem B5837993 : Blo 1729065 5837993 := bstep (se 2 (by rfl) ⟨2189247, by rfl⟩ : syracuseStep 5837993 = 4378495) B4378495
theorem B2594027 : Blo 1729065 2594027 := bstep (se 1 (by rfl) ⟨1945520, by rfl⟩ : syracuseStep 2594027 = 3891041) B3891041
theorem B2594111 : Blo 1729065 2594111 := bstep (se 1 (by rfl) ⟨1945583, by rfl⟩ : syracuseStep 2594111 = 3891167) B3891167
theorem B67450259 : Blo 1729065 67450259 := bstep (se 1 (by rfl) ⟨50587694, by rfl⟩ : syracuseStep 67450259 = 101175389) B101175389
theorem B2594303 : Blo 1729065 2594303 := bstep (se 1 (by rfl) ⟨1945727, by rfl⟩ : syracuseStep 2594303 = 3891455) B3891455
theorem B1947163 : Blo 1729065 1947163 := bstep (se 1 (by rfl) ⟨1460372, by rfl⟩ : syracuseStep 1947163 = 2920745) B2920745
theorem B2594411 : Blo 1729065 2594411 := bstep (se 1 (by rfl) ⟨1945808, by rfl⟩ : syracuseStep 2594411 = 3891617) B3891617
theorem B1947343 : Blo 1729065 1947343 := bstep (se 1 (by rfl) ⟨1460507, by rfl⟩ : syracuseStep 1947343 = 2921015) B2921015
theorem B2594681 : Blo 1729065 2594681 := bstep (se 2 (by rfl) ⟨973005, by rfl⟩ : syracuseStep 2594681 = 1946011) B1946011
theorem B26646407 : Blo 1729065 26646407 := bstep (se 1 (by rfl) ⟨19984805, by rfl⟩ : syracuseStep 26646407 = 39969611) B39969611
theorem B2594927 : Blo 1729065 2594927 := bstep (se 1 (by rfl) ⟨1946195, by rfl⟩ : syracuseStep 2594927 = 3892391) B3892391
theorem B9853073 : Blo 1729065 9853073 := bstep (se 2 (by rfl) ⟨3694902, by rfl⟩ : syracuseStep 9853073 = 7389805) B7389805
theorem B2594999 : Blo 1729065 2594999 := bstep (se 1 (by rfl) ⟨1946249, by rfl⟩ : syracuseStep 2594999 = 3892499) B3892499
theorem B14022985 : Blo 1729065 14022985 := bstep (se 2 (by rfl) ⟨5258619, by rfl⟩ : syracuseStep 14022985 = 10517239) B10517239
theorem B5544379 : Blo 1729065 5544379 := bstep (se 1 (by rfl) ⟨4158284, by rfl⟩ : syracuseStep 5544379 = 8316569) B8316569
theorem B5839451 : Blo 1729065 5839451 := bstep (se 1 (by rfl) ⟨4379588, by rfl⟩ : syracuseStep 5839451 = 8759177) B8759177
theorem B2595419 : Blo 1729065 2595419 := bstep (se 1 (by rfl) ⟨1946564, by rfl⟩ : syracuseStep 2595419 = 3893129) B3893129
theorem B2595431 : Blo 1729065 2595431 := bstep (se 1 (by rfl) ⟨1946573, by rfl⟩ : syracuseStep 2595431 = 3893147) B3893147
theorem B2595455 : Blo 1729065 2595455 := bstep (se 1 (by rfl) ⟨1946591, by rfl⟩ : syracuseStep 2595455 = 3893183) B3893183
theorem B8755937 : Blo 1729065 8755937 := bstep (se 2 (by rfl) ⟨3283476, by rfl⟩ : syracuseStep 8755937 = 6566953) B6566953
theorem B2595563 : Blo 1729065 2595563 := bstep (se 1 (by rfl) ⟨1946672, by rfl⟩ : syracuseStep 2595563 = 3893345) B3893345
theorem B2595593 : Blo 1729065 2595593 := bstep (se 2 (by rfl) ⟨973347, by rfl⟩ : syracuseStep 2595593 = 1946695) B1946695
theorem B5544713 : Blo 1729065 5544713 := bstep (se 2 (by rfl) ⟨2079267, by rfl⟩ : syracuseStep 5544713 = 4158535) B4158535
theorem B14785487 : Blo 1729065 14785487 := bstep (se 1 (by rfl) ⟨11089115, by rfl⟩ : syracuseStep 14785487 = 22178231) B22178231
theorem B21330935 : Blo 1729065 21330935 := bstep (se 1 (by rfl) ⟨15998201, by rfl⟩ : syracuseStep 21330935 = 31996403) B31996403
theorem B2595833 : Blo 1729065 2595833 := bstep (se 2 (by rfl) ⟨973437, by rfl⟩ : syracuseStep 2595833 = 1946875) B1946875
theorem B1973279 : Blo 1729065 1973279 := bstep (se 1 (by rfl) ⟨1479959, by rfl⟩ : syracuseStep 1973279 = 2959919) B2959919
theorem B11091167 : Blo 1729065 11091167 := bstep (se 1 (by rfl) ⟨8318375, by rfl⟩ : syracuseStep 11091167 = 16636751) B16636751
theorem B2596463 : Blo 1729065 2596463 := bstep (se 1 (by rfl) ⟨1947347, by rfl⟩ : syracuseStep 2596463 = 3894695) B3894695
theorem B2596583 : Blo 1729065 2596583 := bstep (se 1 (by rfl) ⟨1947437, by rfl⟩ : syracuseStep 2596583 = 3894875) B3894875
theorem B5840855 : Blo 1729065 5840855 := bstep (se 1 (by rfl) ⟨4380641, by rfl⟩ : syracuseStep 5840855 = 8761283) B8761283
theorem B17752121 : Blo 1729065 17752121 := bstep (se 2 (by rfl) ⟨6657045, by rfl⟩ : syracuseStep 17752121 = 13314091) B13314091
theorem B8757395 : Blo 1729065 8757395 := bstep (se 1 (by rfl) ⟨6568046, by rfl⟩ : syracuseStep 8757395 = 13136093) B13136093
theorem B33259895 : Blo 1729065 33259895 := bstep (se 1 (by rfl) ⟨24944921, by rfl⟩ : syracuseStep 33259895 = 49889843) B49889843
theorem B5841503 : Blo 1729065 5841503 := bstep (se 1 (by rfl) ⟨4381127, by rfl⟩ : syracuseStep 5841503 = 8762255) B8762255
theorem B1729307 : Blo 1729065 1729307 := bstep (se 1 (by rfl) ⟨1296980, by rfl⟩ : syracuseStep 1729307 = 2593961) B2593961
theorem B3891995 : Blo 1729065 3891995 := bstep (se 1 (by rfl) ⟨2918996, by rfl⟩ : syracuseStep 3891995 = 5837993) B5837993
theorem B1729351 : Blo 1729065 1729351 := bstep (se 1 (by rfl) ⟨1297013, by rfl⟩ : syracuseStep 1729351 = 2594027) B2594027
theorem B1729407 : Blo 1729065 1729407 := bstep (se 1 (by rfl) ⟨1297055, by rfl⟩ : syracuseStep 1729407 = 2594111) B2594111
theorem B44966839 : Blo 1729065 44966839 := bstep (se 1 (by rfl) ⟨33725129, by rfl⟩ : syracuseStep 44966839 = 67450259) B67450259
theorem B3892193 : Blo 1729065 3892193 := bstep (se 2 (by rfl) ⟨1459572, by rfl⟩ : syracuseStep 3892193 = 2919145) B2919145
theorem B1729535 : Blo 1729065 1729535 := bstep (se 1 (by rfl) ⟨1297151, by rfl⟩ : syracuseStep 1729535 = 2594303) B2594303
theorem B3892265 : Blo 1729065 3892265 := bstep (se 2 (by rfl) ⟨1459599, by rfl⟩ : syracuseStep 3892265 = 2919199) B2919199
theorem B1729607 : Blo 1729065 1729607 := bstep (se 1 (by rfl) ⟨1297205, by rfl⟩ : syracuseStep 1729607 = 2594411) B2594411
theorem B1729787 : Blo 1729065 1729787 := bstep (se 1 (by rfl) ⟨1297340, by rfl⟩ : syracuseStep 1729787 = 2594681) B2594681
theorem B1729951 : Blo 1729065 1729951 := bstep (se 1 (by rfl) ⟨1297463, by rfl⟩ : syracuseStep 1729951 = 2594927) B2594927
theorem B1729999 : Blo 1729065 1729999 := bstep (se 1 (by rfl) ⟨1297499, by rfl⟩ : syracuseStep 1729999 = 2594999) B2594999
theorem B2918119 : Blo 1729065 2918119 := bstep (se 1 (by rfl) ⟨2188589, by rfl⟩ : syracuseStep 2918119 = 4377179) B4377179
theorem B3892967 : Blo 1729065 3892967 := bstep (se 1 (by rfl) ⟨2919725, by rfl⟩ : syracuseStep 3892967 = 5839451) B5839451
theorem B1730279 : Blo 1729065 1730279 := bstep (se 1 (by rfl) ⟨1297709, by rfl⟩ : syracuseStep 1730279 = 2595419) B2595419
theorem B1730287 : Blo 1729065 1730287 := bstep (se 1 (by rfl) ⟨1297715, by rfl⟩ : syracuseStep 1730287 = 2595431) B2595431
theorem B1730303 : Blo 1729065 1730303 := bstep (se 1 (by rfl) ⟨1297727, by rfl⟩ : syracuseStep 1730303 = 2595455) B2595455
theorem B1730375 : Blo 1729065 1730375 := bstep (se 1 (by rfl) ⟨1297781, by rfl⟩ : syracuseStep 1730375 = 2595563) B2595563
theorem B1730395 : Blo 1729065 1730395 := bstep (se 1 (by rfl) ⟨1297796, by rfl⟩ : syracuseStep 1730395 = 2595593) B2595593
theorem B3696475 : Blo 1729065 3696475 := bstep (se 1 (by rfl) ⟨2772356, by rfl⟩ : syracuseStep 3696475 = 5544713) B5544713
theorem B9848699 : Blo 1729065 9848699 := bstep (se 1 (by rfl) ⟨7386524, by rfl⟩ : syracuseStep 9848699 = 14773049) B14773049
theorem B9856991 : Blo 1729065 9856991 := bstep (se 1 (by rfl) ⟨7392743, by rfl⟩ : syracuseStep 9856991 = 14785487) B14785487
theorem B1730555 : Blo 1729065 1730555 := bstep (se 1 (by rfl) ⟨1297916, by rfl⟩ : syracuseStep 1730555 = 2595833) B2595833
theorem B1730975 : Blo 1729065 1730975 := bstep (se 1 (by rfl) ⟨1298231, by rfl⟩ : syracuseStep 1730975 = 2596463) B2596463
theorem B1731055 : Blo 1729065 1731055 := bstep (se 1 (by rfl) ⟨1298291, by rfl⟩ : syracuseStep 1731055 = 2596583) B2596583
theorem B19696121 : Blo 1729065 19696121 := bstep (se 2 (by rfl) ⟨7386045, by rfl⟩ : syracuseStep 19696121 = 14772091) B14772091
theorem B3893903 : Blo 1729065 3893903 := bstep (se 1 (by rfl) ⟨2920427, by rfl⟩ : syracuseStep 3893903 = 5840855) B5840855
theorem B2919071 : Blo 1729065 2919071 := bstep (se 1 (by rfl) ⟨2189303, by rfl⟩ : syracuseStep 2919071 = 4378607) B4378607
theorem B5262077 : Blo 1729065 5262077 := bstep (se 3 (by rfl) ⟨986639, by rfl⟩ : syracuseStep 5262077 = 1973279) B1973279
theorem B4377503 : Blo 1729065 4377503 := bstep (se 1 (by rfl) ⟨3283127, by rfl⟩ : syracuseStep 4377503 = 6566255) B6566255
theorem B3894299 : Blo 1729065 3894299 := bstep (se 1 (by rfl) ⟨2920724, by rfl⟩ : syracuseStep 3894299 = 5841449) B5841449
theorem B19704869 : Blo 1729065 19704869 := bstep (se 4 (by rfl) ⟨1847331, by rfl⟩ : syracuseStep 19704869 = 3694663) B3694663
theorem B18697313 : Blo 1729065 18697313 := bstep (se 2 (by rfl) ⟨7011492, by rfl⟩ : syracuseStep 18697313 = 14022985) B14022985
theorem B56118419 : Blo 1729065 56118419 := bstep (se 1 (by rfl) ⟨42088814, by rfl⟩ : syracuseStep 56118419 = 84177629) B84177629
theorem B7392505 : Blo 1729065 7392505 := bstep (se 2 (by rfl) ⟨2772189, by rfl⟩ : syracuseStep 7392505 = 5544379) B5544379
theorem B12463379 : Blo 1729065 12463379 := bstep (se 1 (by rfl) ⟨9347534, by rfl⟩ : syracuseStep 12463379 = 18695069) B18695069
theorem B3116335 : Blo 1729065 3116335 := bstep (se 1 (by rfl) ⟨2337251, by rfl⟩ : syracuseStep 3116335 = 4674503) B4674503
theorem B6565481 : Blo 1729065 6565481 := bstep (se 2 (by rfl) ⟨2462055, by rfl⟩ : syracuseStep 6565481 = 4924111) B4924111
theorem B13135607 : Blo 1729065 13135607 := bstep (se 1 (by rfl) ⟨9851705, by rfl⟩ : syracuseStep 13135607 = 19703411) B19703411
theorem B102502205 : Blo 1729065 102502205 := bstep (se 3 (by rfl) ⟨19219163, by rfl⟩ : syracuseStep 102502205 = 38438327) B38438327
theorem B17764271 : Blo 1729065 17764271 := bstep (se 1 (by rfl) ⟨13323203, by rfl⟩ : syracuseStep 17764271 = 26646407) B26646407
theorem B1945543 : Blo 1729065 1945543 := bstep (se 1 (by rfl) ⟨1459157, by rfl⟩ : syracuseStep 1945543 = 2918315) B2918315
theorem B2920441 : Blo 1729065 2920441 := bstep (se 2 (by rfl) ⟨1095165, by rfl⟩ : syracuseStep 2920441 = 2190331) B2190331
theorem B14037137 : Blo 1729065 14037137 := bstep (se 2 (by rfl) ⟨5263926, by rfl⟩ : syracuseStep 14037137 = 10527853) B10527853
theorem B1945903 : Blo 1729065 1945903 := bstep (se 1 (by rfl) ⟨1459427, by rfl⟩ : syracuseStep 1945903 = 2918855) B2918855
theorem B5837291 : Blo 1729065 5837291 := bstep (se 1 (by rfl) ⟨4377968, by rfl⟩ : syracuseStep 5837291 = 8755937) B8755937
theorem B134787635 : Blo 1729065 134787635 := bstep (se 1 (by rfl) ⟨101090726, by rfl⟩ : syracuseStep 134787635 = 202181453) B202181453
theorem B13144841 : Blo 1729065 13144841 := bstep (se 2 (by rfl) ⟨4929315, by rfl⟩ : syracuseStep 13144841 = 9858631) B9858631
theorem B7394111 : Blo 1729065 7394111 := bstep (se 1 (by rfl) ⟨5545583, by rfl⟩ : syracuseStep 7394111 = 11091167) B11091167
theorem B2593673 : Blo 1729065 2593673 := bstep (se 2 (by rfl) ⟨972627, by rfl⟩ : syracuseStep 2593673 = 1945255) B1945255
theorem B1848263 : Blo 1729065 1848263 := bstep (se 1 (by rfl) ⟨1386197, by rfl⟩ : syracuseStep 1848263 = 2772395) B2772395
theorem B56128535 : Blo 1729065 56128535 := bstep (se 1 (by rfl) ⟨42096401, by rfl⟩ : syracuseStep 56128535 = 84192803) B84192803
theorem B6566939 : Blo 1729065 6566939 := bstep (se 1 (by rfl) ⟨4925204, by rfl⟩ : syracuseStep 6566939 = 9850409) B9850409
theorem B9991295 : Blo 1729065 9991295 := bstep (se 1 (by rfl) ⟨7493471, by rfl⟩ : syracuseStep 9991295 = 14986943) B14986943
theorem B7386319 : Blo 1729065 7386319 := bstep (se 1 (by rfl) ⟨5539739, by rfl⟩ : syracuseStep 7386319 = 11079479) B11079479
theorem B14988673 : Blo 1729065 14988673 := bstep (se 2 (by rfl) ⟨5620752, by rfl⟩ : syracuseStep 14988673 = 11241505) B11241505
theorem B4675367 : Blo 1729065 4675367 := bstep (se 1 (by rfl) ⟨3506525, by rfl⟩ : syracuseStep 4675367 = 7013051) B7013051
theorem B4380713 : Blo 1729065 4380713 := bstep (se 2 (by rfl) ⟨1642767, by rfl⟩ : syracuseStep 4380713 = 3285535) B3285535
theorem B2595209 : Blo 1729065 2595209 := bstep (se 2 (by rfl) ⟨973203, by rfl⟩ : syracuseStep 2595209 = 1946407) B1946407
theorem B3283355 : Blo 1729065 3283355 := bstep (se 1 (by rfl) ⟨2462516, by rfl⟩ : syracuseStep 3283355 = 4925033) B4925033
theorem B11393453 : Blo 1729065 11393453 := bstep (se 3 (by rfl) ⟨2136272, by rfl⟩ : syracuseStep 11393453 = 4272545) B4272545
theorem B5839343 : Blo 1729065 5839343 := bstep (se 1 (by rfl) ⟨4379507, by rfl⟩ : syracuseStep 5839343 = 8759015) B8759015
theorem B2595383 : Blo 1729065 2595383 := bstep (se 1 (by rfl) ⟨1946537, by rfl⟩ : syracuseStep 2595383 = 3893075) B3893075
theorem B3693289 : Blo 1729065 3693289 := bstep (se 2 (by rfl) ⟨1384983, by rfl⟩ : syracuseStep 3693289 = 2769967) B2769967
theorem B49879799 : Blo 1729065 49879799 := bstep (se 1 (by rfl) ⟨37409849, by rfl⟩ : syracuseStep 49879799 = 74819699) B74819699
theorem B6568715 : Blo 1729065 6568715 := bstep (se 1 (by rfl) ⟨4926536, by rfl⟩ : syracuseStep 6568715 = 9853073) B9853073
theorem B9853757 : Blo 1729065 9853757 := bstep (se 3 (by rfl) ⟨1847579, by rfl⟩ : syracuseStep 9853757 = 3695159) B3695159
theorem B227597201 : Blo 1729065 227597201 := bstep (se 2 (by rfl) ⟨85348950, by rfl⟩ : syracuseStep 227597201 = 170697901) B170697901
theorem B2596091 : Blo 1729065 2596091 := bstep (se 1 (by rfl) ⟨1947068, by rfl⟩ : syracuseStep 2596091 = 3894137) B3894137
theorem B14220623 : Blo 1729065 14220623 := bstep (se 1 (by rfl) ⟨10665467, by rfl⟩ : syracuseStep 14220623 = 21330935) B21330935
theorem B5840207 : Blo 1729065 5840207 := bstep (se 1 (by rfl) ⟨4380155, by rfl⟩ : syracuseStep 5840207 = 8760311) B8760311
theorem B2596217 : Blo 1729065 2596217 := bstep (se 2 (by rfl) ⟨973581, by rfl⟩ : syracuseStep 2596217 = 1947163) B1947163
theorem B2596457 : Blo 1729065 2596457 := bstep (se 2 (by rfl) ⟨973671, by rfl⟩ : syracuseStep 2596457 = 1947343) B1947343
theorem B3891527 : Blo 1729065 3891527 := bstep (se 1 (by rfl) ⟨2918645, by rfl⟩ : syracuseStep 3891527 = 5837291) B5837291
theorem B89858423 : Blo 1729065 89858423 := bstep (se 1 (by rfl) ⟨67393817, by rfl⟩ : syracuseStep 89858423 = 134787635) B134787635
theorem B1729115 : Blo 1729065 1729115 := bstep (se 1 (by rfl) ⟨1296836, by rfl⟩ : syracuseStep 1729115 = 2593673) B2593673
theorem B6660863 : Blo 1729065 6660863 := bstep (se 1 (by rfl) ⟨4995647, by rfl⟩ : syracuseStep 6660863 = 9991295) B9991295
theorem B4924385 : Blo 1729065 4924385 := bstep (se 2 (by rfl) ⟨1846644, by rfl⟩ : syracuseStep 4924385 = 3693289) B3693289
theorem B6571327 : Blo 1729065 6571327 := bstep (se 1 (by rfl) ⟨4928495, by rfl⟩ : syracuseStep 6571327 = 9856991) B9856991
theorem B1730139 : Blo 1729065 1730139 := bstep (se 1 (by rfl) ⟨1297604, by rfl⟩ : syracuseStep 1730139 = 2595209) B2595209
theorem B9848425 : Blo 1729065 9848425 := bstep (se 2 (by rfl) ⟨3693159, by rfl⟩ : syracuseStep 9848425 = 7386319) B7386319
theorem B7595635 : Blo 1729065 7595635 := bstep (se 1 (by rfl) ⟨5696726, by rfl⟩ : syracuseStep 7595635 = 11393453) B11393453
theorem B3892895 : Blo 1729065 3892895 := bstep (se 1 (by rfl) ⟨2919671, by rfl⟩ : syracuseStep 3892895 = 5839343) B5839343
theorem B9856673 : Blo 1729065 9856673 := bstep (se 2 (by rfl) ⟨3696252, by rfl⟩ : syracuseStep 9856673 = 7392505) B7392505
theorem B1730255 : Blo 1729065 1730255 := bstep (se 1 (by rfl) ⟨1297691, by rfl⟩ : syracuseStep 1730255 = 2595383) B2595383
theorem B4155113 : Blo 1729065 4155113 := bstep (se 2 (by rfl) ⟨1558167, by rfl⟩ : syracuseStep 4155113 = 3116335) B3116335
theorem B33253199 : Blo 1729065 33253199 := bstep (se 1 (by rfl) ⟨24939899, by rfl⟩ : syracuseStep 33253199 = 49879799) B49879799
theorem B3508051 : Blo 1729065 3508051 := bstep (se 1 (by rfl) ⟨2631038, by rfl⟩ : syracuseStep 3508051 = 5262077) B5262077
theorem B2918335 : Blo 1729065 2918335 := bstep (se 1 (by rfl) ⟨2188751, by rfl⟩ : syracuseStep 2918335 = 4377503) B4377503
theorem B1730727 : Blo 1729065 1730727 := bstep (se 1 (by rfl) ⟨1298045, by rfl⟩ : syracuseStep 1730727 = 2596091) B2596091
theorem B8308919 : Blo 1729065 8308919 := bstep (se 1 (by rfl) ⟨6231689, by rfl⟩ : syracuseStep 8308919 = 12463379) B12463379
theorem B9480415 : Blo 1729065 9480415 := bstep (se 1 (by rfl) ⟨7110311, by rfl⟩ : syracuseStep 9480415 = 14220623) B14220623
theorem B3893471 : Blo 1729065 3893471 := bstep (se 1 (by rfl) ⟨2920103, by rfl⟩ : syracuseStep 3893471 = 5840207) B5840207
theorem B1730811 : Blo 1729065 1730811 := bstep (se 1 (by rfl) ⟨1298108, by rfl⟩ : syracuseStep 1730811 = 2596217) B2596217
theorem B4376987 : Blo 1729065 4376987 := bstep (se 1 (by rfl) ⟨3282740, by rfl⟩ : syracuseStep 4376987 = 6565481) B6565481
theorem B1730971 : Blo 1729065 1730971 := bstep (se 1 (by rfl) ⟨1298228, by rfl⟩ : syracuseStep 1730971 = 2596457) B2596457
theorem B3893921 : Blo 1729065 3893921 := bstep (se 2 (by rfl) ⟨1460220, by rfl⟩ : syracuseStep 3893921 = 2920441) B2920441
theorem B9358091 : Blo 1729065 9358091 := bstep (se 1 (by rfl) ⟨7018568, by rfl⟩ : syracuseStep 9358091 = 14037137) B14037137
theorem B3894335 : Blo 1729065 3894335 := bstep (se 1 (by rfl) ⟨2920751, by rfl⟩ : syracuseStep 3894335 = 5841503) B5841503
theorem B4377959 : Blo 1729065 4377959 := bstep (se 1 (by rfl) ⟨3283469, by rfl⟩ : syracuseStep 4377959 = 6566939) B6566939
theorem B3116911 : Blo 1729065 3116911 := bstep (se 1 (by rfl) ⟨2337683, by rfl⟩ : syracuseStep 3116911 = 4675367) B4675367
theorem B6565799 : Blo 1729065 6565799 := bstep (se 1 (by rfl) ⟨4924349, by rfl⟩ : syracuseStep 6565799 = 9848699) B9848699
theorem B2920475 : Blo 1729065 2920475 := bstep (se 1 (by rfl) ⟨2190356, by rfl⟩ : syracuseStep 2920475 = 4380713) B4380713
theorem B1946047 : Blo 1729065 1946047 := bstep (se 1 (by rfl) ⟨1459535, by rfl⟩ : syracuseStep 1946047 = 2919071) B2919071
theorem B19984897 : Blo 1729065 19984897 := bstep (se 2 (by rfl) ⟨7494336, by rfl⟩ : syracuseStep 19984897 = 14988673) B14988673
theorem B4379143 : Blo 1729065 4379143 := bstep (se 1 (by rfl) ⟨3284357, by rfl⟩ : syracuseStep 4379143 = 6568715) B6568715
theorem B13136579 : Blo 1729065 13136579 := bstep (se 1 (by rfl) ⟨9852434, by rfl⟩ : syracuseStep 13136579 = 19704869) B19704869
theorem B12464875 : Blo 1729065 12464875 := bstep (se 1 (by rfl) ⟨9348656, by rfl⟩ : syracuseStep 12464875 = 18697313) B18697313
theorem B4928633 : Blo 1729065 4928633 := bstep (se 2 (by rfl) ⟨1848237, by rfl⟩ : syracuseStep 4928633 = 3696475) B3696475
theorem B4928701 : Blo 1729065 4928701 := bstep (se 3 (by rfl) ⟨924131, by rfl⟩ : syracuseStep 4928701 = 1848263) B1848263
theorem B68334803 : Blo 1729065 68334803 := bstep (se 1 (by rfl) ⟨51251102, by rfl⟩ : syracuseStep 68334803 = 102502205) B102502205
theorem B2594057 : Blo 1729065 2594057 := bstep (se 2 (by rfl) ⟨972771, by rfl⟩ : syracuseStep 2594057 = 1945543) B1945543
theorem B11842847 : Blo 1729065 11842847 := bstep (se 1 (by rfl) ⟨8882135, by rfl⟩ : syracuseStep 11842847 = 17764271) B17764271
theorem B11834747 : Blo 1729065 11834747 := bstep (se 1 (by rfl) ⟨8876060, by rfl⟩ : syracuseStep 11834747 = 17752121) B17752121
theorem B5838263 : Blo 1729065 5838263 := bstep (se 1 (by rfl) ⟨4378697, by rfl⟩ : syracuseStep 5838263 = 8757395) B8757395
theorem B22173263 : Blo 1729065 22173263 := bstep (se 1 (by rfl) ⟨16629947, by rfl⟩ : syracuseStep 22173263 = 33259895) B33259895
theorem B2594537 : Blo 1729065 2594537 := bstep (se 2 (by rfl) ⟨972951, by rfl⟩ : syracuseStep 2594537 = 1945903) B1945903
theorem B8763227 : Blo 1729065 8763227 := bstep (se 1 (by rfl) ⟨6572420, by rfl⟩ : syracuseStep 8763227 = 13144841) B13144841
theorem B2594663 : Blo 1729065 2594663 := bstep (se 1 (by rfl) ⟨1945997, by rfl⟩ : syracuseStep 2594663 = 3891995) B3891995
theorem B4929407 : Blo 1729065 4929407 := bstep (se 1 (by rfl) ⟨3697055, by rfl⟩ : syracuseStep 4929407 = 7394111) B7394111
theorem B2594795 : Blo 1729065 2594795 := bstep (se 1 (by rfl) ⟨1946096, by rfl⟩ : syracuseStep 2594795 = 3892193) B3892193
theorem B37419023 : Blo 1729065 37419023 := bstep (se 1 (by rfl) ⟨28064267, by rfl⟩ : syracuseStep 37419023 = 56128535) B56128535
theorem B2594843 : Blo 1729065 2594843 := bstep (se 1 (by rfl) ⟨1946132, by rfl⟩ : syracuseStep 2594843 = 3892265) B3892265
theorem B8755613 : Blo 1729065 8755613 := bstep (se 3 (by rfl) ⟨1641677, by rfl⟩ : syracuseStep 8755613 = 3283355) B3283355
theorem B2595311 : Blo 1729065 2595311 := bstep (se 1 (by rfl) ⟨1946483, by rfl⟩ : syracuseStep 2595311 = 3892967) B3892967
theorem B59955785 : Blo 1729065 59955785 := bstep (se 2 (by rfl) ⟨22483419, by rfl⟩ : syracuseStep 59955785 = 44966839) B44966839
theorem B13130747 : Blo 1729065 13130747 := bstep (se 1 (by rfl) ⟨9848060, by rfl⟩ : syracuseStep 13130747 = 19696121) B19696121
theorem B2595935 : Blo 1729065 2595935 := bstep (se 1 (by rfl) ⟨1946951, by rfl⟩ : syracuseStep 2595935 = 3893903) B3893903
theorem B6569171 : Blo 1729065 6569171 := bstep (se 1 (by rfl) ⟨4926878, by rfl⟩ : syracuseStep 6569171 = 9853757) B9853757
theorem B151731467 : Blo 1729065 151731467 := bstep (se 1 (by rfl) ⟨113798600, by rfl⟩ : syracuseStep 151731467 = 227597201) B227597201
theorem B2596199 : Blo 1729065 2596199 := bstep (se 1 (by rfl) ⟨1947149, by rfl⟩ : syracuseStep 2596199 = 3894299) B3894299
theorem B37412279 : Blo 1729065 37412279 := bstep (se 1 (by rfl) ⟨28059209, by rfl⟩ : syracuseStep 37412279 = 56118419) B56118419
theorem B3890825 : Blo 1729065 3890825 := bstep (se 2 (by rfl) ⟨1459059, by rfl⟩ : syracuseStep 3890825 = 2918119) B2918119
theorem B8757071 : Blo 1729065 8757071 := bstep (se 1 (by rfl) ⟨6567803, by rfl⟩ : syracuseStep 8757071 = 13135607) B13135607
theorem B12640553 : Blo 1729065 12640553 := bstep (se 2 (by rfl) ⟨4740207, by rfl⟩ : syracuseStep 12640553 = 9480415) B9480415
theorem B8757719 : Blo 1729065 8757719 := bstep (se 1 (by rfl) ⟨6568289, by rfl⟩ : syracuseStep 8757719 = 13136579) B13136579
theorem B4440575 : Blo 1729065 4440575 := bstep (se 1 (by rfl) ⟨3330431, by rfl⟩ : syracuseStep 4440575 = 6660863) B6660863
theorem B3285755 : Blo 1729065 3285755 := bstep (se 1 (by rfl) ⟨2464316, by rfl⟩ : syracuseStep 3285755 = 4928633) B4928633
theorem B45556535 : Blo 1729065 45556535 := bstep (se 1 (by rfl) ⟨34167401, by rfl⟩ : syracuseStep 45556535 = 68334803) B68334803
theorem B1729371 : Blo 1729065 1729371 := bstep (se 1 (by rfl) ⟨1297028, by rfl⟩ : syracuseStep 1729371 = 2594057) B2594057
theorem B7889831 : Blo 1729065 7889831 := bstep (se 1 (by rfl) ⟨5917373, by rfl⟩ : syracuseStep 7889831 = 11834747) B11834747
theorem B3892175 : Blo 1729065 3892175 := bstep (se 1 (by rfl) ⟨2919131, by rfl⟩ : syracuseStep 3892175 = 5838263) B5838263
theorem B6571115 : Blo 1729065 6571115 := bstep (se 1 (by rfl) ⟨4928336, by rfl⟩ : syracuseStep 6571115 = 9856673) B9856673
theorem B2770075 : Blo 1729065 2770075 := bstep (se 1 (by rfl) ⟨2077556, by rfl⟩ : syracuseStep 2770075 = 4155113) B4155113
theorem B1729691 : Blo 1729065 1729691 := bstep (se 1 (by rfl) ⟨1297268, by rfl⟩ : syracuseStep 1729691 = 2594537) B2594537
theorem B22168799 : Blo 1729065 22168799 := bstep (se 1 (by rfl) ⟨16626599, by rfl⟩ : syracuseStep 22168799 = 33253199) B33253199
theorem B5842151 : Blo 1729065 5842151 := bstep (se 1 (by rfl) ⟨4381613, by rfl⟩ : syracuseStep 5842151 = 8763227) B8763227
theorem B1729775 : Blo 1729065 1729775 := bstep (se 1 (by rfl) ⟨1297331, by rfl⟩ : syracuseStep 1729775 = 2594663) B2594663
theorem B3286271 : Blo 1729065 3286271 := bstep (se 1 (by rfl) ⟨2464703, by rfl⟩ : syracuseStep 3286271 = 4929407) B4929407
theorem B1729863 : Blo 1729065 1729863 := bstep (se 1 (by rfl) ⟨1297397, by rfl⟩ : syracuseStep 1729863 = 2594795) B2594795
theorem B24946015 : Blo 1729065 24946015 := bstep (se 1 (by rfl) ⟨18709511, by rfl⟩ : syracuseStep 24946015 = 37419023) B37419023
theorem B1729895 : Blo 1729065 1729895 := bstep (se 1 (by rfl) ⟨1297421, by rfl⟩ : syracuseStep 1729895 = 2594843) B2594843
theorem B5539279 : Blo 1729065 5539279 := bstep (se 1 (by rfl) ⟨4154459, by rfl⟩ : syracuseStep 5539279 = 8308919) B8308919
theorem B6571601 : Blo 1729065 6571601 := bstep (se 2 (by rfl) ⟨2464350, by rfl⟩ : syracuseStep 6571601 = 4928701) B4928701
theorem B2917991 : Blo 1729065 2917991 := bstep (se 1 (by rfl) ⟨2188493, by rfl⟩ : syracuseStep 2917991 = 4376987) B4376987
theorem B1730207 : Blo 1729065 1730207 := bstep (se 1 (by rfl) ⟨1297655, by rfl⟩ : syracuseStep 1730207 = 2595311) B2595311
theorem B39970523 : Blo 1729065 39970523 := bstep (se 1 (by rfl) ⟨29977892, by rfl⟩ : syracuseStep 39970523 = 59955785) B59955785
theorem B1730623 : Blo 1729065 1730623 := bstep (se 1 (by rfl) ⟨1297967, by rfl⟩ : syracuseStep 1730623 = 2595935) B2595935
theorem B10127513 : Blo 1729065 10127513 := bstep (se 2 (by rfl) ⟨3797817, by rfl⟩ : syracuseStep 10127513 = 7595635) B7595635
theorem B2918639 : Blo 1729065 2918639 := bstep (se 1 (by rfl) ⟨2188979, by rfl⟩ : syracuseStep 2918639 = 4377959) B4377959
theorem B1730799 : Blo 1729065 1730799 := bstep (se 1 (by rfl) ⟨1298099, by rfl⟩ : syracuseStep 1730799 = 2596199) B2596199
theorem B4155881 : Blo 1729065 4155881 := bstep (se 2 (by rfl) ⟨1558455, by rfl⟩ : syracuseStep 4155881 = 3116911) B3116911
theorem B4377199 : Blo 1729065 4377199 := bstep (se 1 (by rfl) ⟨3282899, by rfl⟩ : syracuseStep 4377199 = 6565799) B6565799
theorem B14782175 : Blo 1729065 14782175 := bstep (se 1 (by rfl) ⟨11086631, by rfl⟩ : syracuseStep 14782175 = 22173263) B22173263
theorem B5837075 : Blo 1729065 5837075 := bstep (se 1 (by rfl) ⟨4377806, by rfl⟩ : syracuseStep 5837075 = 8755613) B8755613
theorem B8761769 : Blo 1729065 8761769 := bstep (se 2 (by rfl) ⟨3285663, by rfl⟩ : syracuseStep 8761769 = 6571327) B6571327
theorem B6238727 : Blo 1729065 6238727 := bstep (se 1 (by rfl) ⟨4679045, by rfl⟩ : syracuseStep 6238727 = 9358091) B9358091
theorem B8753831 : Blo 1729065 8753831 := bstep (se 1 (by rfl) ⟨6565373, by rfl⟩ : syracuseStep 8753831 = 13130747) B13130747
theorem B4379447 : Blo 1729065 4379447 := bstep (se 1 (by rfl) ⟨3284585, by rfl⟩ : syracuseStep 4379447 = 6569171) B6569171
theorem B24941519 : Blo 1729065 24941519 := bstep (se 1 (by rfl) ⟨18706139, by rfl⟩ : syracuseStep 24941519 = 37412279) B37412279
theorem B2593883 : Blo 1729065 2593883 := bstep (se 1 (by rfl) ⟨1945412, by rfl⟩ : syracuseStep 2593883 = 3890825) B3890825
theorem B5838047 : Blo 1729065 5838047 := bstep (se 1 (by rfl) ⟨4378535, by rfl⟩ : syracuseStep 5838047 = 8757071) B8757071
theorem B1946983 : Blo 1729065 1946983 := bstep (se 1 (by rfl) ⟨1460237, by rfl⟩ : syracuseStep 1946983 = 2920475) B2920475
theorem B2594351 : Blo 1729065 2594351 := bstep (se 1 (by rfl) ⟨1945763, by rfl⟩ : syracuseStep 2594351 = 3891527) B3891527
theorem B2594729 : Blo 1729065 2594729 := bstep (se 2 (by rfl) ⟨973023, by rfl⟩ : syracuseStep 2594729 = 1946047) B1946047
theorem B3282923 : Blo 1729065 3282923 := bstep (se 1 (by rfl) ⟨2462192, by rfl⟩ : syracuseStep 3282923 = 4924385) B4924385
theorem B26646529 : Blo 1729065 26646529 := bstep (se 2 (by rfl) ⟨9992448, by rfl⟩ : syracuseStep 26646529 = 19984897) B19984897
theorem B5838857 : Blo 1729065 5838857 := bstep (se 2 (by rfl) ⟨2189571, by rfl⟩ : syracuseStep 5838857 = 4379143) B4379143
theorem B7895231 : Blo 1729065 7895231 := bstep (se 1 (by rfl) ⟨5921423, by rfl⟩ : syracuseStep 7895231 = 11842847) B11842847
theorem B16619833 : Blo 1729065 16619833 := bstep (se 2 (by rfl) ⟨6232437, by rfl⟩ : syracuseStep 16619833 = 12464875) B12464875
theorem B239622461 : Blo 1729065 239622461 := bstep (se 3 (by rfl) ⟨44929211, by rfl⟩ : syracuseStep 239622461 = 89858423) B89858423
theorem B2595263 : Blo 1729065 2595263 := bstep (se 1 (by rfl) ⟨1946447, by rfl⟩ : syracuseStep 2595263 = 3892895) B3892895
theorem B2595647 : Blo 1729065 2595647 := bstep (se 1 (by rfl) ⟨1946735, by rfl⟩ : syracuseStep 2595647 = 3893471) B3893471
theorem B2595947 : Blo 1729065 2595947 := bstep (se 1 (by rfl) ⟨1946960, by rfl⟩ : syracuseStep 2595947 = 3893921) B3893921
theorem B2596223 : Blo 1729065 2596223 := bstep (se 1 (by rfl) ⟨1947167, by rfl⟩ : syracuseStep 2596223 = 3894335) B3894335
theorem B13131233 : Blo 1729065 13131233 := bstep (se 2 (by rfl) ⟨4924212, by rfl⟩ : syracuseStep 13131233 = 9848425) B9848425
theorem B101154311 : Blo 1729065 101154311 := bstep (se 1 (by rfl) ⟨75865733, by rfl⟩ : syracuseStep 101154311 = 151731467) B151731467
theorem B4677401 : Blo 1729065 4677401 := bstep (se 2 (by rfl) ⟨1754025, by rfl⟩ : syracuseStep 4677401 = 3508051) B3508051
theorem B3891113 : Blo 1729065 3891113 := bstep (se 2 (by rfl) ⟨1459167, by rfl⟩ : syracuseStep 3891113 = 2918335) B2918335
theorem B35528705 : Blo 1729065 35528705 := bstep (se 2 (by rfl) ⟨13323264, by rfl⟩ : syracuseStep 35528705 = 26646529) B26646529
theorem B3891383 : Blo 1729065 3891383 := bstep (se 1 (by rfl) ⟨2918537, by rfl⟩ : syracuseStep 3891383 = 5837075) B5837075
theorem B5841179 : Blo 1729065 5841179 := bstep (se 1 (by rfl) ⟨4380884, by rfl⟩ : syracuseStep 5841179 = 8761769) B8761769
theorem B22159777 : Blo 1729065 22159777 := bstep (se 2 (by rfl) ⟨8309916, by rfl⟩ : syracuseStep 22159777 = 16619833) B16619833
theorem B5259887 : Blo 1729065 5259887 := bstep (se 1 (by rfl) ⟨3944915, by rfl⟩ : syracuseStep 5259887 = 7889831) B7889831
theorem B1729255 : Blo 1729065 1729255 := bstep (se 1 (by rfl) ⟨1296941, by rfl⟩ : syracuseStep 1729255 = 2593883) B2593883
theorem B3892031 : Blo 1729065 3892031 := bstep (se 1 (by rfl) ⟨2919023, by rfl⟩ : syracuseStep 3892031 = 5838047) B5838047
theorem B14779199 : Blo 1729065 14779199 := bstep (se 1 (by rfl) ⟨11084399, by rfl⟩ : syracuseStep 14779199 = 22168799) B22168799
theorem B1729567 : Blo 1729065 1729567 := bstep (se 1 (by rfl) ⟨1297175, by rfl⟩ : syracuseStep 1729567 = 2594351) B2594351
theorem B1729819 : Blo 1729065 1729819 := bstep (se 1 (by rfl) ⟨1297364, by rfl⟩ : syracuseStep 1729819 = 2594729) B2594729
theorem B2188615 : Blo 1729065 2188615 := bstep (se 1 (by rfl) ⟨1641461, by rfl⟩ : syracuseStep 2188615 = 3282923) B3282923
theorem B3892571 : Blo 1729065 3892571 := bstep (se 1 (by rfl) ⟨2919428, by rfl⟩ : syracuseStep 3892571 = 5838857) B5838857
theorem B1730175 : Blo 1729065 1730175 := bstep (se 1 (by rfl) ⟨1297631, by rfl⟩ : syracuseStep 1730175 = 2595263) B2595263
theorem B33261353 : Blo 1729065 33261353 := bstep (se 2 (by rfl) ⟨12473007, by rfl⟩ : syracuseStep 33261353 = 24946015) B24946015
theorem B1730431 : Blo 1729065 1730431 := bstep (se 1 (by rfl) ⟨1297823, by rfl⟩ : syracuseStep 1730431 = 2595647) B2595647
theorem B106588061 : Blo 1729065 106588061 := bstep (se 3 (by rfl) ⟨19985261, by rfl⟩ : syracuseStep 106588061 = 39970523) B39970523
theorem B1730631 : Blo 1729065 1730631 := bstep (se 1 (by rfl) ⟨1297973, by rfl⟩ : syracuseStep 1730631 = 2595947) B2595947
theorem B1730815 : Blo 1729065 1730815 := bstep (se 1 (by rfl) ⟨1298111, by rfl⟩ : syracuseStep 1730815 = 2596223) B2596223
theorem B2960383 : Blo 1729065 2960383 := bstep (se 1 (by rfl) ⟨2220287, by rfl⟩ : syracuseStep 2960383 = 4440575) B4440575
theorem B5835887 : Blo 1729065 5835887 := bstep (se 1 (by rfl) ⟨4376915, by rfl⟩ : syracuseStep 5835887 = 8753831) B8753831
theorem B2190503 : Blo 1729065 2190503 := bstep (se 1 (by rfl) ⟨1642877, by rfl⟩ : syracuseStep 2190503 = 3285755) B3285755
theorem B30371023 : Blo 1729065 30371023 := bstep (se 1 (by rfl) ⟨22778267, by rfl⟩ : syracuseStep 30371023 = 45556535) B45556535
theorem B2919631 : Blo 1729065 2919631 := bstep (se 1 (by rfl) ⟨2189723, by rfl⟩ : syracuseStep 2919631 = 4379447) B4379447
theorem B5836265 : Blo 1729065 5836265 := bstep (se 2 (by rfl) ⟨2188599, by rfl⟩ : syracuseStep 5836265 = 4377199) B4377199
theorem B3894767 : Blo 1729065 3894767 := bstep (se 1 (by rfl) ⟨2921075, by rfl⟩ : syracuseStep 3894767 = 5842151) B5842151
theorem B1945327 : Blo 1729065 1945327 := bstep (se 1 (by rfl) ⟨1458995, by rfl⟩ : syracuseStep 1945327 = 2917991) B2917991
theorem B5263487 : Blo 1729065 5263487 := bstep (se 1 (by rfl) ⟨3947615, by rfl⟩ : syracuseStep 5263487 = 7895231) B7895231
theorem B1945759 : Blo 1729065 1945759 := bstep (se 1 (by rfl) ⟨1459319, by rfl⟩ : syracuseStep 1945759 = 2918639) B2918639
theorem B159748307 : Blo 1729065 159748307 := bstep (se 1 (by rfl) ⟨119811230, by rfl⟩ : syracuseStep 159748307 = 239622461) B239622461
theorem B7385705 : Blo 1729065 7385705 := bstep (se 2 (by rfl) ⟨2769639, by rfl⟩ : syracuseStep 7385705 = 5539279) B5539279
theorem B8754155 : Blo 1729065 8754155 := bstep (se 1 (by rfl) ⟨6565616, by rfl⟩ : syracuseStep 8754155 = 13131233) B13131233
theorem B3118267 : Blo 1729065 3118267 := bstep (se 1 (by rfl) ⟨2338700, by rfl⟩ : syracuseStep 3118267 = 4677401) B4677401
theorem B2594075 : Blo 1729065 2594075 := bstep (se 1 (by rfl) ⟨1945556, by rfl⟩ : syracuseStep 2594075 = 3891113) B3891113
theorem B8427035 : Blo 1729065 8427035 := bstep (se 1 (by rfl) ⟨6320276, by rfl⟩ : syracuseStep 8427035 = 12640553) B12640553
theorem B5838479 : Blo 1729065 5838479 := bstep (se 1 (by rfl) ⟨4378859, by rfl⟩ : syracuseStep 5838479 = 8757719) B8757719
theorem B4159151 : Blo 1729065 4159151 := bstep (se 1 (by rfl) ⟨3119363, by rfl⟩ : syracuseStep 4159151 = 6238727) B6238727
theorem B27006701 : Blo 1729065 27006701 := bstep (se 3 (by rfl) ⟨5063756, by rfl⟩ : syracuseStep 27006701 = 10127513) B10127513
theorem B2594783 : Blo 1729065 2594783 := bstep (se 1 (by rfl) ⟨1946087, by rfl⟩ : syracuseStep 2594783 = 3892175) B3892175
theorem B16627679 : Blo 1729065 16627679 := bstep (se 1 (by rfl) ⟨12470759, by rfl⟩ : syracuseStep 16627679 = 24941519) B24941519
theorem B8763389 : Blo 1729065 8763389 := bstep (se 3 (by rfl) ⟨1643135, by rfl⟩ : syracuseStep 8763389 = 3286271) B3286271
theorem B4380743 : Blo 1729065 4380743 := bstep (se 1 (by rfl) ⟨3285557, by rfl⟩ : syracuseStep 4380743 = 6571115) B6571115
theorem B4381067 : Blo 1729065 4381067 := bstep (se 1 (by rfl) ⟨3285800, by rfl⟩ : syracuseStep 4381067 = 6571601) B6571601
theorem B11082349 : Blo 1729065 11082349 := bstep (se 3 (by rfl) ⟨2077940, by rfl⟩ : syracuseStep 11082349 = 4155881) B4155881
theorem B3693433 : Blo 1729065 3693433 := bstep (se 2 (by rfl) ⟨1385037, by rfl⟩ : syracuseStep 3693433 = 2770075) B2770075
theorem B2595977 : Blo 1729065 2595977 := bstep (se 2 (by rfl) ⟨973491, by rfl⟩ : syracuseStep 2595977 = 1946983) B1946983
theorem B67436207 : Blo 1729065 67436207 := bstep (se 1 (by rfl) ⟨50577155, by rfl⟩ : syracuseStep 67436207 = 101154311) B101154311
theorem B9854783 : Blo 1729065 9854783 := bstep (se 1 (by rfl) ⟨7391087, by rfl⟩ : syracuseStep 9854783 = 14782175) B14782175
theorem B4923803 : Blo 1729065 4923803 := bstep (se 1 (by rfl) ⟨3692852, by rfl⟩ : syracuseStep 4923803 = 7385705) B7385705
theorem B3506591 : Blo 1729065 3506591 := bstep (se 1 (by rfl) ⟨2629943, by rfl⟩ : syracuseStep 3506591 = 5259887) B5259887
theorem B5841341 : Blo 1729065 5841341 := bstep (se 3 (by rfl) ⟨1095251, by rfl⟩ : syracuseStep 5841341 = 2190503) B2190503
theorem B1729383 : Blo 1729065 1729383 := bstep (se 1 (by rfl) ⟨1297037, by rfl⟩ : syracuseStep 1729383 = 2594075) B2594075
theorem B3892319 : Blo 1729065 3892319 := bstep (se 1 (by rfl) ⟨2919239, by rfl⟩ : syracuseStep 3892319 = 5838479) B5838479
theorem B4924577 : Blo 1729065 4924577 := bstep (se 2 (by rfl) ⟨1846716, by rfl⟩ : syracuseStep 4924577 = 3693433) B3693433
theorem B71058707 : Blo 1729065 71058707 := bstep (se 1 (by rfl) ⟨53294030, by rfl⟩ : syracuseStep 71058707 = 106588061) B106588061
theorem B1729855 : Blo 1729065 1729855 := bstep (se 1 (by rfl) ⟨1297391, by rfl⟩ : syracuseStep 1729855 = 2594783) B2594783
theorem B11085119 : Blo 1729065 11085119 := bstep (se 1 (by rfl) ⟨8313839, by rfl⟩ : syracuseStep 11085119 = 16627679) B16627679
theorem B5842259 : Blo 1729065 5842259 := bstep (se 1 (by rfl) ⟨4381694, by rfl⟩ : syracuseStep 5842259 = 8763389) B8763389
theorem B22472093 : Blo 1729065 22472093 := bstep (se 3 (by rfl) ⟨4213517, by rfl⟩ : syracuseStep 22472093 = 8427035) B8427035
theorem B40494697 : Blo 1729065 40494697 := bstep (se 2 (by rfl) ⟨15185511, by rfl⟩ : syracuseStep 40494697 = 30371023) B30371023
theorem B3892841 : Blo 1729065 3892841 := bstep (se 2 (by rfl) ⟨1459815, by rfl⟩ : syracuseStep 3892841 = 2919631) B2919631
theorem B2918153 : Blo 1729065 2918153 := bstep (se 2 (by rfl) ⟨1094307, by rfl⟩ : syracuseStep 2918153 = 2188615) B2188615
theorem B72017869 : Blo 1729065 72017869 := bstep (se 3 (by rfl) ⟨13503350, by rfl⟩ : syracuseStep 72017869 = 27006701) B27006701
theorem B1730651 : Blo 1729065 1730651 := bstep (se 1 (by rfl) ⟨1297988, by rfl⟩ : syracuseStep 1730651 = 2595977) B2595977
theorem B23685803 : Blo 1729065 23685803 := bstep (se 1 (by rfl) ⟨17764352, by rfl⟩ : syracuseStep 23685803 = 35528705) B35528705
theorem B3508991 : Blo 1729065 3508991 := bstep (se 1 (by rfl) ⟨2631743, by rfl⟩ : syracuseStep 3508991 = 5263487) B5263487
theorem B106498871 : Blo 1729065 106498871 := bstep (se 1 (by rfl) ⟨79874153, by rfl⟩ : syracuseStep 106498871 = 159748307) B159748307
theorem B3894119 : Blo 1729065 3894119 := bstep (se 1 (by rfl) ⟨2920589, by rfl⟩ : syracuseStep 3894119 = 5841179) B5841179
theorem B5836103 : Blo 1729065 5836103 := bstep (se 1 (by rfl) ⟨4377077, by rfl⟩ : syracuseStep 5836103 = 8754155) B8754155
theorem B2772767 : Blo 1729065 2772767 := bstep (se 1 (by rfl) ⟨2079575, by rfl⟩ : syracuseStep 2772767 = 4159151) B4159151
theorem B2920495 : Blo 1729065 2920495 := bstep (se 1 (by rfl) ⟨2190371, by rfl⟩ : syracuseStep 2920495 = 4380743) B4380743
theorem B4157689 : Blo 1729065 4157689 := bstep (se 2 (by rfl) ⟨1559133, by rfl⟩ : syracuseStep 4157689 = 3118267) B3118267
theorem B2920711 : Blo 1729065 2920711 := bstep (se 1 (by rfl) ⟨2190533, by rfl⟩ : syracuseStep 2920711 = 4381067) B4381067
theorem B719319541 : Blo 1729065 719319541 := bstep (se 5 (by rfl) ⟨33718103, by rfl⟩ : syracuseStep 719319541 = 67436207) B67436207
theorem B2593769 : Blo 1729065 2593769 := bstep (se 2 (by rfl) ⟨972663, by rfl⟩ : syracuseStep 2593769 = 1945327) B1945327
theorem B2594255 : Blo 1729065 2594255 := bstep (se 1 (by rfl) ⟨1945691, by rfl⟩ : syracuseStep 2594255 = 3891383) B3891383
theorem B2594345 : Blo 1729065 2594345 := bstep (se 2 (by rfl) ⟨972879, by rfl⟩ : syracuseStep 2594345 = 1945759) B1945759
theorem B2594687 : Blo 1729065 2594687 := bstep (se 1 (by rfl) ⟨1946015, by rfl⟩ : syracuseStep 2594687 = 3892031) B3892031
theorem B9852799 : Blo 1729065 9852799 := bstep (se 1 (by rfl) ⟨7389599, by rfl⟩ : syracuseStep 9852799 = 14779199) B14779199
theorem B29546369 : Blo 1729065 29546369 := bstep (se 2 (by rfl) ⟨11079888, by rfl⟩ : syracuseStep 29546369 = 22159777) B22159777
theorem B14776465 : Blo 1729065 14776465 := bstep (se 2 (by rfl) ⟨5541174, by rfl⟩ : syracuseStep 14776465 = 11082349) B11082349
theorem B2595047 : Blo 1729065 2595047 := bstep (se 1 (by rfl) ⟨1946285, by rfl⟩ : syracuseStep 2595047 = 3892571) B3892571
theorem B22174235 : Blo 1729065 22174235 := bstep (se 1 (by rfl) ⟨16630676, by rfl⟩ : syracuseStep 22174235 = 33261353) B33261353
theorem B3947177 : Blo 1729065 3947177 := bstep (se 2 (by rfl) ⟨1480191, by rfl⟩ : syracuseStep 3947177 = 2960383) B2960383
theorem B3890591 : Blo 1729065 3890591 := bstep (se 1 (by rfl) ⟨2917943, by rfl⟩ : syracuseStep 3890591 = 5835887) B5835887
theorem B3890843 : Blo 1729065 3890843 := bstep (se 1 (by rfl) ⟨2918132, by rfl⟩ : syracuseStep 3890843 = 5836265) B5836265
theorem B2596511 : Blo 1729065 2596511 := bstep (se 1 (by rfl) ⟨1947383, by rfl⟩ : syracuseStep 2596511 = 3894767) B3894767
theorem B6569855 : Blo 1729065 6569855 := bstep (se 1 (by rfl) ⟨4927391, by rfl⟩ : syracuseStep 6569855 = 9854783) B9854783
theorem B19701953 : Blo 1729065 19701953 := bstep (se 2 (by rfl) ⟨7388232, by rfl⟩ : syracuseStep 19701953 = 14776465) B14776465
theorem B13132205 : Blo 1729065 13132205 := bstep (se 3 (by rfl) ⟨2462288, by rfl⟩ : syracuseStep 13132205 = 4924577) B4924577
theorem B1729179 : Blo 1729065 1729179 := bstep (se 1 (by rfl) ⟨1296884, by rfl⟩ : syracuseStep 1729179 = 2593769) B2593769
theorem B7390079 : Blo 1729065 7390079 := bstep (se 1 (by rfl) ⟨5542559, by rfl⟩ : syracuseStep 7390079 = 11085119) B11085119
theorem B1729503 : Blo 1729065 1729503 := bstep (se 1 (by rfl) ⟨1297127, by rfl⟩ : syracuseStep 1729503 = 2594255) B2594255
theorem B1729563 : Blo 1729065 1729563 := bstep (se 1 (by rfl) ⟨1297172, by rfl⟩ : syracuseStep 1729563 = 2594345) B2594345
theorem B1729791 : Blo 1729065 1729791 := bstep (se 1 (by rfl) ⟨1297343, by rfl⟩ : syracuseStep 1729791 = 2594687) B2594687
theorem B1730031 : Blo 1729065 1730031 := bstep (se 1 (by rfl) ⟨1297523, by rfl⟩ : syracuseStep 1730031 = 2595047) B2595047
theorem B2631451 : Blo 1729065 2631451 := bstep (se 1 (by rfl) ⟨1973588, by rfl⟩ : syracuseStep 2631451 = 3947177) B3947177
theorem B1731007 : Blo 1729065 1731007 := bstep (se 1 (by rfl) ⟨1298255, by rfl⟩ : syracuseStep 1731007 = 2596511) B2596511
theorem B3893993 : Blo 1729065 3893993 := bstep (se 2 (by rfl) ⟨1460247, by rfl⟩ : syracuseStep 3893993 = 2920495) B2920495
theorem B2337727 : Blo 1729065 2337727 := bstep (se 1 (by rfl) ⟨1753295, by rfl⟩ : syracuseStep 2337727 = 3506591) B3506591
theorem B3894227 : Blo 1729065 3894227 := bstep (se 1 (by rfl) ⟨2920670, by rfl⟩ : syracuseStep 3894227 = 5841341) B5841341
theorem B3894281 : Blo 1729065 3894281 := bstep (se 2 (by rfl) ⟨1460355, by rfl⟩ : syracuseStep 3894281 = 2920711) B2920711
theorem B3894839 : Blo 1729065 3894839 := bstep (se 1 (by rfl) ⟨2921129, by rfl⟩ : syracuseStep 3894839 = 5842259) B5842259
theorem B1945435 : Blo 1729065 1945435 := bstep (se 1 (by rfl) ⟨1459076, by rfl⟩ : syracuseStep 1945435 = 2918153) B2918153
theorem B19697579 : Blo 1729065 19697579 := bstep (se 1 (by rfl) ⟨14773184, by rfl⟩ : syracuseStep 19697579 = 29546369) B29546369
theorem B14782823 : Blo 1729065 14782823 := bstep (se 1 (by rfl) ⟨11087117, by rfl⟩ : syracuseStep 14782823 = 22174235) B22174235
theorem B15790535 : Blo 1729065 15790535 := bstep (se 1 (by rfl) ⟨11842901, by rfl⟩ : syracuseStep 15790535 = 23685803) B23685803
theorem B2339327 : Blo 1729065 2339327 := bstep (se 1 (by rfl) ⟨1754495, by rfl⟩ : syracuseStep 2339327 = 3508991) B3508991
theorem B2593727 : Blo 1729065 2593727 := bstep (se 1 (by rfl) ⟨1945295, by rfl⟩ : syracuseStep 2593727 = 3890591) B3890591
theorem B2593895 : Blo 1729065 2593895 := bstep (se 1 (by rfl) ⟨1945421, by rfl⟩ : syracuseStep 2593895 = 3890843) B3890843
theorem B13137065 : Blo 1729065 13137065 := bstep (se 2 (by rfl) ⟨4926399, by rfl⟩ : syracuseStep 13137065 = 9852799) B9852799
theorem B1848511 : Blo 1729065 1848511 := bstep (se 1 (by rfl) ⟨1386383, by rfl⟩ : syracuseStep 1848511 = 2772767) B2772767
theorem B4379903 : Blo 1729065 4379903 := bstep (se 1 (by rfl) ⟨3284927, by rfl⟩ : syracuseStep 4379903 = 6569855) B6569855
theorem B96023825 : Blo 1729065 96023825 := bstep (se 2 (by rfl) ⟨36008934, by rfl⟩ : syracuseStep 96023825 = 72017869) B72017869
theorem B3282535 : Blo 1729065 3282535 := bstep (se 1 (by rfl) ⟨2461901, by rfl⟩ : syracuseStep 3282535 = 4923803) B4923803
theorem B5543585 : Blo 1729065 5543585 := bstep (se 2 (by rfl) ⟨2078844, by rfl⟩ : syracuseStep 5543585 = 4157689) B4157689
theorem B215971717 : Blo 1729065 215971717 := bstep (se 4 (by rfl) ⟨20247348, by rfl⟩ : syracuseStep 215971717 = 40494697) B40494697
theorem B959092721 : Blo 1729065 959092721 := bstep (se 2 (by rfl) ⟨359659770, by rfl⟩ : syracuseStep 959092721 = 719319541) B719319541
theorem B2594879 : Blo 1729065 2594879 := bstep (se 1 (by rfl) ⟨1946159, by rfl⟩ : syracuseStep 2594879 = 3892319) B3892319
theorem B47372471 : Blo 1729065 47372471 := bstep (se 1 (by rfl) ⟨35529353, by rfl⟩ : syracuseStep 47372471 = 71058707) B71058707
theorem B14981395 : Blo 1729065 14981395 := bstep (se 1 (by rfl) ⟨11236046, by rfl⟩ : syracuseStep 14981395 = 22472093) B22472093
theorem B2595227 : Blo 1729065 2595227 := bstep (se 1 (by rfl) ⟨1946420, by rfl⟩ : syracuseStep 2595227 = 3892841) B3892841
theorem B70999247 : Blo 1729065 70999247 := bstep (se 1 (by rfl) ⟨53249435, by rfl⟩ : syracuseStep 70999247 = 106498871) B106498871
theorem B2596079 : Blo 1729065 2596079 := bstep (se 1 (by rfl) ⟨1947059, by rfl⟩ : syracuseStep 2596079 = 3894119) B3894119
theorem B3890735 : Blo 1729065 3890735 := bstep (se 1 (by rfl) ⟨2918051, by rfl⟩ : syracuseStep 3890735 = 5836103) B5836103
theorem B9855215 : Blo 1729065 9855215 := bstep (se 1 (by rfl) ⟨7391411, by rfl⟩ : syracuseStep 9855215 = 14782823) B14782823
theorem B10527023 : Blo 1729065 10527023 := bstep (se 1 (by rfl) ⟨7895267, by rfl⟩ : syracuseStep 10527023 = 15790535) B15790535
theorem B1729151 : Blo 1729065 1729151 := bstep (se 1 (by rfl) ⟨1296863, by rfl⟩ : syracuseStep 1729151 = 2593727) B2593727
theorem B1729263 : Blo 1729065 1729263 := bstep (se 1 (by rfl) ⟨1296947, by rfl⟩ : syracuseStep 1729263 = 2593895) B2593895
theorem B8758043 : Blo 1729065 8758043 := bstep (se 1 (by rfl) ⟨6568532, by rfl⟩ : syracuseStep 8758043 = 13137065) B13137065
theorem B3695723 : Blo 1729065 3695723 := bstep (se 1 (by rfl) ⟨2771792, by rfl⟩ : syracuseStep 3695723 = 5543585) B5543585
theorem B639395147 : Blo 1729065 639395147 := bstep (se 1 (by rfl) ⟨479546360, by rfl⟩ : syracuseStep 639395147 = 959092721) B959092721
theorem B1729919 : Blo 1729065 1729919 := bstep (se 1 (by rfl) ⟨1297439, by rfl⟩ : syracuseStep 1729919 = 2594879) B2594879
theorem B31581647 : Blo 1729065 31581647 := bstep (se 1 (by rfl) ⟨23686235, by rfl⟩ : syracuseStep 31581647 = 47372471) B47372471
theorem B1730151 : Blo 1729065 1730151 := bstep (se 1 (by rfl) ⟨1297613, by rfl⟩ : syracuseStep 1730151 = 2595227) B2595227
theorem B4376713 : Blo 1729065 4376713 := bstep (se 2 (by rfl) ⟨1641267, by rfl⟩ : syracuseStep 4376713 = 3282535) B3282535
theorem B1730719 : Blo 1729065 1730719 := bstep (se 1 (by rfl) ⟨1298039, by rfl⟩ : syracuseStep 1730719 = 2596079) B2596079
theorem B3508601 : Blo 1729065 3508601 := bstep (se 2 (by rfl) ⟨1315725, by rfl⟩ : syracuseStep 3508601 = 2631451) B2631451
theorem B13134635 : Blo 1729065 13134635 := bstep (se 1 (by rfl) ⟨9850976, by rfl⟩ : syracuseStep 13134635 = 19701953) B19701953
theorem B19975193 : Blo 1729065 19975193 := bstep (se 2 (by rfl) ⟨7490697, by rfl⟩ : syracuseStep 19975193 = 14981395) B14981395
theorem B4926719 : Blo 1729065 4926719 := bstep (se 1 (by rfl) ⟨3695039, by rfl⟩ : syracuseStep 4926719 = 7390079) B7390079
theorem B2919935 : Blo 1729065 2919935 := bstep (se 1 (by rfl) ⟨2189951, by rfl⟩ : syracuseStep 2919935 = 4379903) B4379903
theorem B64015883 : Blo 1729065 64015883 := bstep (se 1 (by rfl) ⟨48011912, by rfl⟩ : syracuseStep 64015883 = 96023825) B96023825
theorem B3116969 : Blo 1729065 3116969 := bstep (se 2 (by rfl) ⟨1168863, by rfl⟩ : syracuseStep 3116969 = 2337727) B2337727
theorem B6238205 : Blo 1729065 6238205 := bstep (se 3 (by rfl) ⟨1169663, by rfl⟩ : syracuseStep 6238205 = 2339327) B2339327
theorem B2593823 : Blo 1729065 2593823 := bstep (se 1 (by rfl) ⟨1945367, by rfl⟩ : syracuseStep 2593823 = 3890735) B3890735
theorem B2593913 : Blo 1729065 2593913 := bstep (se 2 (by rfl) ⟨972717, by rfl⟩ : syracuseStep 2593913 = 1945435) B1945435
theorem B287962289 : Blo 1729065 287962289 := bstep (se 2 (by rfl) ⟨107985858, by rfl⟩ : syracuseStep 287962289 = 215971717) B215971717
theorem B8754803 : Blo 1729065 8754803 := bstep (se 1 (by rfl) ⟨6566102, by rfl⟩ : syracuseStep 8754803 = 13132205) B13132205
theorem B2464681 : Blo 1729065 2464681 := bstep (se 2 (by rfl) ⟨924255, by rfl⟩ : syracuseStep 2464681 = 1848511) B1848511
theorem B2595995 : Blo 1729065 2595995 := bstep (se 1 (by rfl) ⟨1946996, by rfl⟩ : syracuseStep 2595995 = 3893993) B3893993
theorem B2596151 : Blo 1729065 2596151 := bstep (se 1 (by rfl) ⟨1947113, by rfl⟩ : syracuseStep 2596151 = 3894227) B3894227
theorem B2596187 : Blo 1729065 2596187 := bstep (se 1 (by rfl) ⟨1947140, by rfl⟩ : syracuseStep 2596187 = 3894281) B3894281
theorem B47332831 : Blo 1729065 47332831 := bstep (se 1 (by rfl) ⟨35499623, by rfl⟩ : syracuseStep 47332831 = 70999247) B70999247
theorem B2596559 : Blo 1729065 2596559 := bstep (se 1 (by rfl) ⟨1947419, by rfl⟩ : syracuseStep 2596559 = 3894839) B3894839
theorem B13131719 : Blo 1729065 13131719 := bstep (se 1 (by rfl) ⟨9848789, by rfl⟩ : syracuseStep 13131719 = 19697579) B19697579
theorem B6570143 : Blo 1729065 6570143 := bstep (se 1 (by rfl) ⟨4927607, by rfl⟩ : syracuseStep 6570143 = 9855215) B9855215
theorem B1729215 : Blo 1729065 1729215 := bstep (se 1 (by rfl) ⟨1296911, by rfl⟩ : syracuseStep 1729215 = 2593823) B2593823
theorem B1729275 : Blo 1729065 1729275 := bstep (se 1 (by rfl) ⟨1296956, by rfl⟩ : syracuseStep 1729275 = 2593913) B2593913
theorem B426263431 : Blo 1729065 426263431 := bstep (se 1 (by rfl) ⟨319697573, by rfl⟩ : syracuseStep 426263431 = 639395147) B639395147
theorem B21054431 : Blo 1729065 21054431 := bstep (se 1 (by rfl) ⟨15790823, by rfl⟩ : syracuseStep 21054431 = 31581647) B31581647
theorem B9356269 : Blo 1729065 9356269 := bstep (se 3 (by rfl) ⟨1754300, by rfl⟩ : syracuseStep 9356269 = 3508601) B3508601
theorem B3286241 : Blo 1729065 3286241 := bstep (se 2 (by rfl) ⟨1232340, by rfl⟩ : syracuseStep 3286241 = 2464681) B2464681
theorem B1730663 : Blo 1729065 1730663 := bstep (se 1 (by rfl) ⟨1297997, by rfl⟩ : syracuseStep 1730663 = 2595995) B2595995
theorem B1730767 : Blo 1729065 1730767 := bstep (se 1 (by rfl) ⟨1298075, by rfl⟩ : syracuseStep 1730767 = 2596151) B2596151
theorem B1730791 : Blo 1729065 1730791 := bstep (se 1 (by rfl) ⟨1298093, by rfl⟩ : syracuseStep 1730791 = 2596187) B2596187
theorem B1731039 : Blo 1729065 1731039 := bstep (se 1 (by rfl) ⟨1298279, by rfl⟩ : syracuseStep 1731039 = 2596559) B2596559
theorem B5835617 : Blo 1729065 5835617 := bstep (se 2 (by rfl) ⟨2188356, by rfl⟩ : syracuseStep 5835617 = 4376713) B4376713
theorem B191974859 : Blo 1729065 191974859 := bstep (se 1 (by rfl) ⟨143981144, by rfl⟩ : syracuseStep 191974859 = 287962289) B287962289
theorem B5836535 : Blo 1729065 5836535 := bstep (se 1 (by rfl) ⟨4377401, by rfl⟩ : syracuseStep 5836535 = 8754803) B8754803
theorem B13316795 : Blo 1729065 13316795 := bstep (se 1 (by rfl) ⟨9987596, by rfl⟩ : syracuseStep 13316795 = 19975193) B19975193
theorem B1946623 : Blo 1729065 1946623 := bstep (se 1 (by rfl) ⟨1459967, by rfl⟩ : syracuseStep 1946623 = 2919935) B2919935
theorem B42677255 : Blo 1729065 42677255 := bstep (se 1 (by rfl) ⟨32007941, by rfl⟩ : syracuseStep 42677255 = 64015883) B64015883
theorem B2077979 : Blo 1729065 2077979 := bstep (se 1 (by rfl) ⟨1558484, by rfl⟩ : syracuseStep 2077979 = 3116969) B3116969
theorem B8754479 : Blo 1729065 8754479 := bstep (se 1 (by rfl) ⟨6565859, by rfl⟩ : syracuseStep 8754479 = 13131719) B13131719
theorem B4158803 : Blo 1729065 4158803 := bstep (se 1 (by rfl) ⟨3119102, by rfl⟩ : syracuseStep 4158803 = 6238205) B6238205
theorem B7018015 : Blo 1729065 7018015 := bstep (se 1 (by rfl) ⟨5263511, by rfl⟩ : syracuseStep 7018015 = 10527023) B10527023
theorem B5838695 : Blo 1729065 5838695 := bstep (se 1 (by rfl) ⟨4379021, by rfl⟩ : syracuseStep 5838695 = 8758043) B8758043
theorem B2463815 : Blo 1729065 2463815 := bstep (se 1 (by rfl) ⟨1847861, by rfl⟩ : syracuseStep 2463815 = 3695723) B3695723
theorem B8756423 : Blo 1729065 8756423 := bstep (se 1 (by rfl) ⟨6567317, by rfl⟩ : syracuseStep 8756423 = 13134635) B13134635
theorem B63110441 : Blo 1729065 63110441 := bstep (se 2 (by rfl) ⟨23666415, by rfl⟩ : syracuseStep 63110441 = 47332831) B47332831
theorem B3284479 : Blo 1729065 3284479 := bstep (se 1 (by rfl) ⟨2463359, by rfl⟩ : syracuseStep 3284479 = 4926719) B4926719
theorem B6570173 : Blo 1729065 6570173 := bstep (se 3 (by rfl) ⟨1231907, by rfl⟩ : syracuseStep 6570173 = 2463815) B2463815
theorem B28451503 : Blo 1729065 28451503 := bstep (se 1 (by rfl) ⟨21338627, by rfl⟩ : syracuseStep 28451503 = 42677255) B42677255
theorem B3892463 : Blo 1729065 3892463 := bstep (se 1 (by rfl) ⟨2919347, by rfl⟩ : syracuseStep 3892463 = 5838695) B5838695
theorem B9357353 : Blo 1729065 9357353 := bstep (se 2 (by rfl) ⟨3509007, by rfl⟩ : syracuseStep 9357353 = 7018015) B7018015
theorem B14036287 : Blo 1729065 14036287 := bstep (se 1 (by rfl) ⟨10527215, by rfl⟩ : syracuseStep 14036287 = 21054431) B21054431
theorem B2190827 : Blo 1729065 2190827 := bstep (se 1 (by rfl) ⟨1643120, by rfl⟩ : syracuseStep 2190827 = 3286241) B3286241
theorem B5836319 : Blo 1729065 5836319 := bstep (se 1 (by rfl) ⟨4377239, by rfl⟩ : syracuseStep 5836319 = 8754479) B8754479
theorem B4379305 : Blo 1729065 4379305 := bstep (se 2 (by rfl) ⟨1642239, by rfl⟩ : syracuseStep 4379305 = 3284479) B3284479
theorem B5837615 : Blo 1729065 5837615 := bstep (se 1 (by rfl) ⟨4378211, by rfl⟩ : syracuseStep 5837615 = 8756423) B8756423
theorem B4380095 : Blo 1729065 4380095 := bstep (se 1 (by rfl) ⟨3285071, by rfl⟩ : syracuseStep 4380095 = 6570143) B6570143
theorem B22165109 : Blo 1729065 22165109 := bstep (se 5 (by rfl) ⟨1038989, by rfl⟩ : syracuseStep 22165109 = 2077979) B2077979
theorem B8877863 : Blo 1729065 8877863 := bstep (se 1 (by rfl) ⟨6658397, by rfl⟩ : syracuseStep 8877863 = 13316795) B13316795
theorem B11090141 : Blo 1729065 11090141 := bstep (se 3 (by rfl) ⟨2079401, by rfl⟩ : syracuseStep 11090141 = 4158803) B4158803
theorem B568351241 : Blo 1729065 568351241 := bstep (se 2 (by rfl) ⟨213131715, by rfl⟩ : syracuseStep 568351241 = 426263431) B426263431
theorem B12475025 : Blo 1729065 12475025 := bstep (se 2 (by rfl) ⟨4678134, by rfl⟩ : syracuseStep 12475025 = 9356269) B9356269
theorem B2595497 : Blo 1729065 2595497 := bstep (se 2 (by rfl) ⟨973311, by rfl⟩ : syracuseStep 2595497 = 1946623) B1946623
theorem B3890411 : Blo 1729065 3890411 := bstep (se 1 (by rfl) ⟨2917808, by rfl⟩ : syracuseStep 3890411 = 5835617) B5835617
theorem B42073627 : Blo 1729065 42073627 := bstep (se 1 (by rfl) ⟨31555220, by rfl⟩ : syracuseStep 42073627 = 63110441) B63110441
theorem B127983239 : Blo 1729065 127983239 := bstep (se 1 (by rfl) ⟨95987429, by rfl⟩ : syracuseStep 127983239 = 191974859) B191974859
theorem B3891023 : Blo 1729065 3891023 := bstep (se 1 (by rfl) ⟨2918267, by rfl⟩ : syracuseStep 3891023 = 5836535) B5836535
theorem B3891743 : Blo 1729065 3891743 := bstep (se 1 (by rfl) ⟨2918807, by rfl⟩ : syracuseStep 3891743 = 5837615) B5837615
theorem B5842205 : Blo 1729065 5842205 := bstep (se 3 (by rfl) ⟨1095413, by rfl⟩ : syracuseStep 5842205 = 2190827) B2190827
theorem B8316683 : Blo 1729065 8316683 := bstep (se 1 (by rfl) ⟨6237512, by rfl⟩ : syracuseStep 8316683 = 12475025) B12475025
theorem B1730331 : Blo 1729065 1730331 := bstep (se 1 (by rfl) ⟨1297748, by rfl⟩ : syracuseStep 1730331 = 2595497) B2595497
theorem B85322159 : Blo 1729065 85322159 := bstep (se 1 (by rfl) ⟨63991619, by rfl⟩ : syracuseStep 85322159 = 127983239) B127983239
theorem B2920063 : Blo 1729065 2920063 := bstep (se 1 (by rfl) ⟨2190047, by rfl⟩ : syracuseStep 2920063 = 4380095) B4380095
theorem B5918575 : Blo 1729065 5918575 := bstep (se 1 (by rfl) ⟨4438931, by rfl⟩ : syracuseStep 5918575 = 8877863) B8877863
theorem B6238235 : Blo 1729065 6238235 := bstep (se 1 (by rfl) ⟨4678676, by rfl⟩ : syracuseStep 6238235 = 9357353) B9357353
theorem B7393427 : Blo 1729065 7393427 := bstep (se 1 (by rfl) ⟨5545070, by rfl⟩ : syracuseStep 7393427 = 11090141) B11090141
theorem B378900827 : Blo 1729065 378900827 := bstep (se 1 (by rfl) ⟨284175620, by rfl⟩ : syracuseStep 378900827 = 568351241) B568351241
theorem B18715049 : Blo 1729065 18715049 := bstep (se 2 (by rfl) ⟨7018143, by rfl⟩ : syracuseStep 18715049 = 14036287) B14036287
theorem B2593607 : Blo 1729065 2593607 := bstep (se 1 (by rfl) ⟨1945205, by rfl⟩ : syracuseStep 2593607 = 3890411) B3890411
theorem B2594015 : Blo 1729065 2594015 := bstep (se 1 (by rfl) ⟨1945511, by rfl⟩ : syracuseStep 2594015 = 3891023) B3891023
theorem B4380115 : Blo 1729065 4380115 := bstep (se 1 (by rfl) ⟨3285086, by rfl⟩ : syracuseStep 4380115 = 6570173) B6570173
theorem B2594975 : Blo 1729065 2594975 := bstep (se 1 (by rfl) ⟨1946231, by rfl⟩ : syracuseStep 2594975 = 3892463) B3892463
theorem B5839073 : Blo 1729065 5839073 := bstep (se 2 (by rfl) ⟨2189652, by rfl⟩ : syracuseStep 5839073 = 4379305) B4379305
theorem B37935337 : Blo 1729065 37935337 := bstep (se 2 (by rfl) ⟨14225751, by rfl⟩ : syracuseStep 37935337 = 28451503) B28451503
theorem B14776739 : Blo 1729065 14776739 := bstep (se 1 (by rfl) ⟨11082554, by rfl⟩ : syracuseStep 14776739 = 22165109) B22165109
theorem B56098169 : Blo 1729065 56098169 := bstep (se 2 (by rfl) ⟨21036813, by rfl⟩ : syracuseStep 56098169 = 42073627) B42073627
theorem B3890879 : Blo 1729065 3890879 := bstep (se 1 (by rfl) ⟨2918159, by rfl⟩ : syracuseStep 3890879 = 5836319) B5836319
theorem B252600551 : Blo 1729065 252600551 := bstep (se 1 (by rfl) ⟨189450413, by rfl⟩ : syracuseStep 252600551 = 378900827) B378900827
theorem B12476699 : Blo 1729065 12476699 := bstep (se 1 (by rfl) ⟨9357524, by rfl⟩ : syracuseStep 12476699 = 18715049) B18715049
theorem B1729071 : Blo 1729065 1729071 := bstep (se 1 (by rfl) ⟨1296803, by rfl⟩ : syracuseStep 1729071 = 2593607) B2593607
theorem B1729343 : Blo 1729065 1729343 := bstep (se 1 (by rfl) ⟨1297007, by rfl⟩ : syracuseStep 1729343 = 2594015) B2594015
theorem B1729983 : Blo 1729065 1729983 := bstep (se 1 (by rfl) ⟨1297487, by rfl⟩ : syracuseStep 1729983 = 2594975) B2594975
theorem B3892715 : Blo 1729065 3892715 := bstep (se 1 (by rfl) ⟨2919536, by rfl⟩ : syracuseStep 3892715 = 5839073) B5839073
theorem B3893417 : Blo 1729065 3893417 := bstep (se 2 (by rfl) ⟨1460031, by rfl⟩ : syracuseStep 3893417 = 2920063) B2920063
theorem B37398779 : Blo 1729065 37398779 := bstep (se 1 (by rfl) ⟨28049084, by rfl⟩ : syracuseStep 37398779 = 56098169) B56098169
theorem B7891433 : Blo 1729065 7891433 := bstep (se 2 (by rfl) ⟨2959287, by rfl⟩ : syracuseStep 7891433 = 5918575) B5918575
theorem B50580449 : Blo 1729065 50580449 := bstep (se 2 (by rfl) ⟨18967668, by rfl⟩ : syracuseStep 50580449 = 37935337) B37935337
theorem B3894803 : Blo 1729065 3894803 := bstep (se 1 (by rfl) ⟨2921102, by rfl⟩ : syracuseStep 3894803 = 5842205) B5842205
theorem B9851159 : Blo 1729065 9851159 := bstep (se 1 (by rfl) ⟨7388369, by rfl⟩ : syracuseStep 9851159 = 14776739) B14776739
theorem B56881439 : Blo 1729065 56881439 := bstep (se 1 (by rfl) ⟨42661079, by rfl⟩ : syracuseStep 56881439 = 85322159) B85322159
theorem B2593919 : Blo 1729065 2593919 := bstep (se 1 (by rfl) ⟨1945439, by rfl⟩ : syracuseStep 2593919 = 3890879) B3890879
theorem B16635293 : Blo 1729065 16635293 := bstep (se 3 (by rfl) ⟨3119117, by rfl⟩ : syracuseStep 16635293 = 6238235) B6238235
theorem B4928951 : Blo 1729065 4928951 := bstep (se 1 (by rfl) ⟨3696713, by rfl⟩ : syracuseStep 4928951 = 7393427) B7393427
theorem B2594495 : Blo 1729065 2594495 := bstep (se 1 (by rfl) ⟨1945871, by rfl⟩ : syracuseStep 2594495 = 3891743) B3891743
theorem B5544455 : Blo 1729065 5544455 := bstep (se 1 (by rfl) ⟨4158341, by rfl⟩ : syracuseStep 5544455 = 8316683) B8316683
theorem B5840153 : Blo 1729065 5840153 := bstep (se 2 (by rfl) ⟨2190057, by rfl⟩ : syracuseStep 5840153 = 4380115) B4380115
theorem B37920959 : Blo 1729065 37920959 := bstep (se 1 (by rfl) ⟨28440719, by rfl⟩ : syracuseStep 37920959 = 56881439) B56881439
theorem B1729279 : Blo 1729065 1729279 := bstep (se 1 (by rfl) ⟨1296959, by rfl⟩ : syracuseStep 1729279 = 2593919) B2593919
theorem B1729663 : Blo 1729065 1729663 := bstep (se 1 (by rfl) ⟨1297247, by rfl⟩ : syracuseStep 1729663 = 2594495) B2594495
theorem B5260955 : Blo 1729065 5260955 := bstep (se 1 (by rfl) ⟨3945716, by rfl⟩ : syracuseStep 5260955 = 7891433) B7891433
theorem B33720299 : Blo 1729065 33720299 := bstep (se 1 (by rfl) ⟨25290224, by rfl⟩ : syracuseStep 33720299 = 50580449) B50580449
theorem B3893435 : Blo 1729065 3893435 := bstep (se 1 (by rfl) ⟨2920076, by rfl⟩ : syracuseStep 3893435 = 5840153) B5840153
theorem B8317799 : Blo 1729065 8317799 := bstep (se 1 (by rfl) ⟨6238349, by rfl⟩ : syracuseStep 8317799 = 12476699) B12476699
theorem B13143869 : Blo 1729065 13143869 := bstep (se 3 (by rfl) ⟨2464475, by rfl⟩ : syracuseStep 13143869 = 4928951) B4928951
theorem B24932519 : Blo 1729065 24932519 := bstep (se 1 (by rfl) ⟨18699389, by rfl⟩ : syracuseStep 24932519 = 37398779) B37398779
theorem B168400367 : Blo 1729065 168400367 := bstep (se 1 (by rfl) ⟨126300275, by rfl⟩ : syracuseStep 168400367 = 252600551) B252600551
theorem B6567439 : Blo 1729065 6567439 := bstep (se 1 (by rfl) ⟨4925579, by rfl⟩ : syracuseStep 6567439 = 9851159) B9851159
theorem B11090195 : Blo 1729065 11090195 := bstep (se 1 (by rfl) ⟨8317646, by rfl⟩ : syracuseStep 11090195 = 16635293) B16635293
theorem B2595143 : Blo 1729065 2595143 := bstep (se 1 (by rfl) ⟨1946357, by rfl⟩ : syracuseStep 2595143 = 3892715) B3892715
theorem B14785213 : Blo 1729065 14785213 := bstep (se 3 (by rfl) ⟨2772227, by rfl⟩ : syracuseStep 14785213 = 5544455) B5544455
theorem B2595611 : Blo 1729065 2595611 := bstep (se 1 (by rfl) ⟨1946708, by rfl⟩ : syracuseStep 2595611 = 3893417) B3893417
theorem B2596535 : Blo 1729065 2596535 := bstep (se 1 (by rfl) ⟨1947401, by rfl⟩ : syracuseStep 2596535 = 3894803) B3894803
theorem B16621679 : Blo 1729065 16621679 := bstep (se 1 (by rfl) ⟨12466259, by rfl⟩ : syracuseStep 16621679 = 24932519) B24932519
theorem B25280639 : Blo 1729065 25280639 := bstep (se 1 (by rfl) ⟨18960479, by rfl⟩ : syracuseStep 25280639 = 37920959) B37920959
theorem B22480199 : Blo 1729065 22480199 := bstep (se 1 (by rfl) ⟨16860149, by rfl⟩ : syracuseStep 22480199 = 33720299) B33720299
theorem B1730095 : Blo 1729065 1730095 := bstep (se 1 (by rfl) ⟨1297571, by rfl⟩ : syracuseStep 1730095 = 2595143) B2595143
theorem B1730407 : Blo 1729065 1730407 := bstep (se 1 (by rfl) ⟨1297805, by rfl⟩ : syracuseStep 1730407 = 2595611) B2595611
theorem B1731023 : Blo 1729065 1731023 := bstep (se 1 (by rfl) ⟨1298267, by rfl⟩ : syracuseStep 1731023 = 2596535) B2596535
theorem B19713617 : Blo 1729065 19713617 := bstep (se 2 (by rfl) ⟨7392606, by rfl⟩ : syracuseStep 19713617 = 14785213) B14785213
theorem B112266911 : Blo 1729065 112266911 := bstep (se 1 (by rfl) ⟨84200183, by rfl⟩ : syracuseStep 112266911 = 168400367) B168400367
theorem B7393463 : Blo 1729065 7393463 := bstep (se 1 (by rfl) ⟨5545097, by rfl⟩ : syracuseStep 7393463 = 11090195) B11090195
theorem B14029213 : Blo 1729065 14029213 := bstep (se 3 (by rfl) ⟨2630477, by rfl⟩ : syracuseStep 14029213 = 5260955) B5260955
theorem B8762579 : Blo 1729065 8762579 := bstep (se 1 (by rfl) ⟨6571934, by rfl⟩ : syracuseStep 8762579 = 13143869) B13143869
theorem B2595623 : Blo 1729065 2595623 := bstep (se 1 (by rfl) ⟨1946717, by rfl⟩ : syracuseStep 2595623 = 3893435) B3893435
theorem B5545199 : Blo 1729065 5545199 := bstep (se 1 (by rfl) ⟨4158899, by rfl⟩ : syracuseStep 5545199 = 8317799) B8317799
theorem B8756585 : Blo 1729065 8756585 := bstep (se 2 (by rfl) ⟨3283719, by rfl⟩ : syracuseStep 8756585 = 6567439) B6567439
theorem B14787197 : Blo 1729065 14787197 := bstep (se 3 (by rfl) ⟨2772599, by rfl⟩ : syracuseStep 14787197 = 5545199) B5545199
theorem B5841719 : Blo 1729065 5841719 := bstep (se 1 (by rfl) ⟨4381289, by rfl⟩ : syracuseStep 5841719 = 8762579) B8762579
theorem B1730415 : Blo 1729065 1730415 := bstep (se 1 (by rfl) ⟨1297811, by rfl⟩ : syracuseStep 1730415 = 2595623) B2595623
theorem B13142411 : Blo 1729065 13142411 := bstep (se 1 (by rfl) ⟨9856808, by rfl⟩ : syracuseStep 13142411 = 19713617) B19713617
theorem B74844607 : Blo 1729065 74844607 := bstep (se 1 (by rfl) ⟨56133455, by rfl⟩ : syracuseStep 74844607 = 112266911) B112266911
theorem B16853759 : Blo 1729065 16853759 := bstep (se 1 (by rfl) ⟨12640319, by rfl⟩ : syracuseStep 16853759 = 25280639) B25280639
theorem B18705617 : Blo 1729065 18705617 := bstep (se 2 (by rfl) ⟨7014606, by rfl⟩ : syracuseStep 18705617 = 14029213) B14029213
theorem B14986799 : Blo 1729065 14986799 := bstep (se 1 (by rfl) ⟨11240099, by rfl⟩ : syracuseStep 14986799 = 22480199) B22480199
theorem B5837723 : Blo 1729065 5837723 := bstep (se 1 (by rfl) ⟨4378292, by rfl⟩ : syracuseStep 5837723 = 8756585) B8756585
theorem B11081119 : Blo 1729065 11081119 := bstep (se 1 (by rfl) ⟨8310839, by rfl⟩ : syracuseStep 11081119 = 16621679) B16621679
theorem B4928975 : Blo 1729065 4928975 := bstep (se 1 (by rfl) ⟨3696731, by rfl⟩ : syracuseStep 4928975 = 7393463) B7393463
theorem B3891815 : Blo 1729065 3891815 := bstep (se 1 (by rfl) ⟨2918861, by rfl⟩ : syracuseStep 3891815 = 5837723) B5837723
theorem B3285983 : Blo 1729065 3285983 := bstep (se 1 (by rfl) ⟨2464487, by rfl⟩ : syracuseStep 3285983 = 4928975) B4928975
theorem B12470411 : Blo 1729065 12470411 := bstep (se 1 (by rfl) ⟨9352808, by rfl⟩ : syracuseStep 12470411 = 18705617) B18705617
theorem B9858131 : Blo 1729065 9858131 := bstep (se 1 (by rfl) ⟨7393598, by rfl⟩ : syracuseStep 9858131 = 14787197) B14787197
theorem B3894479 : Blo 1729065 3894479 := bstep (se 1 (by rfl) ⟨2920859, by rfl⟩ : syracuseStep 3894479 = 5841719) B5841719
theorem B8761607 : Blo 1729065 8761607 := bstep (se 1 (by rfl) ⟨6571205, by rfl⟩ : syracuseStep 8761607 = 13142411) B13142411
theorem B11235839 : Blo 1729065 11235839 := bstep (se 1 (by rfl) ⟨8426879, by rfl⟩ : syracuseStep 11235839 = 16853759) B16853759
theorem B14774825 : Blo 1729065 14774825 := bstep (se 2 (by rfl) ⟨5540559, by rfl⟩ : syracuseStep 14774825 = 11081119) B11081119
theorem B9991199 : Blo 1729065 9991199 := bstep (se 1 (by rfl) ⟨7493399, by rfl⟩ : syracuseStep 9991199 = 14986799) B14986799
theorem B99792809 : Blo 1729065 99792809 := bstep (se 2 (by rfl) ⟨37422303, by rfl⟩ : syracuseStep 99792809 = 74844607) B74844607
theorem B5841071 : Blo 1729065 5841071 := bstep (se 1 (by rfl) ⟨4380803, by rfl⟩ : syracuseStep 5841071 = 8761607) B8761607
theorem B6660799 : Blo 1729065 6660799 := bstep (se 1 (by rfl) ⟨4995599, by rfl⟩ : syracuseStep 6660799 = 9991199) B9991199
theorem B66528539 : Blo 1729065 66528539 := bstep (se 1 (by rfl) ⟨49896404, by rfl⟩ : syracuseStep 66528539 = 99792809) B99792809
theorem B6572087 : Blo 1729065 6572087 := bstep (se 1 (by rfl) ⟨4929065, by rfl⟩ : syracuseStep 6572087 = 9858131) B9858131
theorem B9849883 : Blo 1729065 9849883 := bstep (se 1 (by rfl) ⟨7387412, by rfl⟩ : syracuseStep 9849883 = 14774825) B14774825
theorem B2190655 : Blo 1729065 2190655 := bstep (se 1 (by rfl) ⟨1642991, by rfl⟩ : syracuseStep 2190655 = 3285983) B3285983
theorem B29962237 : Blo 1729065 29962237 := bstep (se 3 (by rfl) ⟨5617919, by rfl⟩ : syracuseStep 29962237 = 11235839) B11235839
theorem B2594543 : Blo 1729065 2594543 := bstep (se 1 (by rfl) ⟨1945907, by rfl⟩ : syracuseStep 2594543 = 3891815) B3891815
theorem B8313607 : Blo 1729065 8313607 := bstep (se 1 (by rfl) ⟨6235205, by rfl⟩ : syracuseStep 8313607 = 12470411) B12470411
theorem B2596319 : Blo 1729065 2596319 := bstep (se 1 (by rfl) ⟨1947239, by rfl⟩ : syracuseStep 2596319 = 3894479) B3894479
theorem B44352359 : Blo 1729065 44352359 := bstep (se 1 (by rfl) ⟨33264269, by rfl⟩ : syracuseStep 44352359 = 66528539) B66528539
theorem B1729695 : Blo 1729065 1729695 := bstep (se 1 (by rfl) ⟨1297271, by rfl⟩ : syracuseStep 1729695 = 2594543) B2594543
theorem B13133177 : Blo 1729065 13133177 := bstep (se 2 (by rfl) ⟨4924941, by rfl⟩ : syracuseStep 13133177 = 9849883) B9849883
theorem B1730879 : Blo 1729065 1730879 := bstep (se 1 (by rfl) ⟨1298159, by rfl⟩ : syracuseStep 1730879 = 2596319) B2596319
theorem B3894047 : Blo 1729065 3894047 := bstep (se 1 (by rfl) ⟨2920535, by rfl⟩ : syracuseStep 3894047 = 5841071) B5841071
theorem B35524261 : Blo 1729065 35524261 := bstep (se 4 (by rfl) ⟨3330399, by rfl⟩ : syracuseStep 35524261 = 6660799) B6660799
theorem B44339237 : Blo 1729065 44339237 := bstep (se 4 (by rfl) ⟨4156803, by rfl⟩ : syracuseStep 44339237 = 8313607) B8313607
theorem B2920873 : Blo 1729065 2920873 := bstep (se 2 (by rfl) ⟨1095327, by rfl⟩ : syracuseStep 2920873 = 2190655) B2190655
theorem B39949649 : Blo 1729065 39949649 := bstep (se 2 (by rfl) ⟨14981118, by rfl⟩ : syracuseStep 39949649 = 29962237) B29962237
theorem B4381391 : Blo 1729065 4381391 := bstep (se 1 (by rfl) ⟨3286043, by rfl⟩ : syracuseStep 4381391 = 6572087) B6572087
theorem B26633099 : Blo 1729065 26633099 := bstep (se 1 (by rfl) ⟨19974824, by rfl⟩ : syracuseStep 26633099 = 39949649) B39949649
theorem B29559491 : Blo 1729065 29559491 := bstep (se 1 (by rfl) ⟨22169618, by rfl⟩ : syracuseStep 29559491 = 44339237) B44339237
theorem B3894497 : Blo 1729065 3894497 := bstep (se 2 (by rfl) ⟨1460436, by rfl⟩ : syracuseStep 3894497 = 2920873) B2920873
theorem B29568239 : Blo 1729065 29568239 := bstep (se 1 (by rfl) ⟨22176179, by rfl⟩ : syracuseStep 29568239 = 44352359) B44352359
theorem B2920927 : Blo 1729065 2920927 := bstep (se 1 (by rfl) ⟨2190695, by rfl⟩ : syracuseStep 2920927 = 4381391) B4381391
theorem B8755451 : Blo 1729065 8755451 := bstep (se 1 (by rfl) ⟨6566588, by rfl⟩ : syracuseStep 8755451 = 13133177) B13133177
theorem B2596031 : Blo 1729065 2596031 := bstep (se 1 (by rfl) ⟨1947023, by rfl⟩ : syracuseStep 2596031 = 3894047) B3894047
theorem B47365681 : Blo 1729065 47365681 := bstep (se 2 (by rfl) ⟨17762130, by rfl⟩ : syracuseStep 47365681 = 35524261) B35524261
theorem B63154241 : Blo 1729065 63154241 := bstep (se 2 (by rfl) ⟨23682840, by rfl⟩ : syracuseStep 63154241 = 47365681) B47365681
theorem B1730687 : Blo 1729065 1730687 := bstep (se 1 (by rfl) ⟨1298015, by rfl⟩ : syracuseStep 1730687 = 2596031) B2596031
theorem B19712159 : Blo 1729065 19712159 := bstep (se 1 (by rfl) ⟨14784119, by rfl⟩ : syracuseStep 19712159 = 29568239) B29568239
theorem B17755399 : Blo 1729065 17755399 := bstep (se 1 (by rfl) ⟨13316549, by rfl⟩ : syracuseStep 17755399 = 26633099) B26633099
theorem B3894569 : Blo 1729065 3894569 := bstep (se 2 (by rfl) ⟨1460463, by rfl⟩ : syracuseStep 3894569 = 2920927) B2920927
theorem B5836967 : Blo 1729065 5836967 := bstep (se 1 (by rfl) ⟨4377725, by rfl⟩ : syracuseStep 5836967 = 8755451) B8755451
theorem B19706327 : Blo 1729065 19706327 := bstep (se 1 (by rfl) ⟨14779745, by rfl⟩ : syracuseStep 19706327 = 29559491) B29559491
theorem B2596331 : Blo 1729065 2596331 := bstep (se 1 (by rfl) ⟨1947248, by rfl⟩ : syracuseStep 2596331 = 3894497) B3894497
theorem B3891311 : Blo 1729065 3891311 := bstep (se 1 (by rfl) ⟨2918483, by rfl⟩ : syracuseStep 3891311 = 5836967) B5836967
theorem B13141439 : Blo 1729065 13141439 := bstep (se 1 (by rfl) ⟨9856079, by rfl⟩ : syracuseStep 13141439 = 19712159) B19712159
theorem B1730887 : Blo 1729065 1730887 := bstep (se 1 (by rfl) ⟨1298165, by rfl⟩ : syracuseStep 1730887 = 2596331) B2596331
theorem B42102827 : Blo 1729065 42102827 := bstep (se 1 (by rfl) ⟨31577120, by rfl⟩ : syracuseStep 42102827 = 63154241) B63154241
theorem B13137551 : Blo 1729065 13137551 := bstep (se 1 (by rfl) ⟨9853163, by rfl⟩ : syracuseStep 13137551 = 19706327) B19706327
theorem B23673865 : Blo 1729065 23673865 := bstep (se 2 (by rfl) ⟨8877699, by rfl⟩ : syracuseStep 23673865 = 17755399) B17755399
theorem B2596379 : Blo 1729065 2596379 := bstep (se 1 (by rfl) ⟨1947284, by rfl⟩ : syracuseStep 2596379 = 3894569) B3894569
theorem B8758367 : Blo 1729065 8758367 := bstep (se 1 (by rfl) ⟨6568775, by rfl⟩ : syracuseStep 8758367 = 13137551) B13137551
theorem B31565153 : Blo 1729065 31565153 := bstep (se 2 (by rfl) ⟨11836932, by rfl⟩ : syracuseStep 31565153 = 23673865) B23673865
theorem B1730919 : Blo 1729065 1730919 := bstep (se 1 (by rfl) ⟨1298189, by rfl⟩ : syracuseStep 1730919 = 2596379) B2596379
theorem B28068551 : Blo 1729065 28068551 := bstep (se 1 (by rfl) ⟨21051413, by rfl⟩ : syracuseStep 28068551 = 42102827) B42102827
theorem B8760959 : Blo 1729065 8760959 := bstep (se 1 (by rfl) ⟨6570719, by rfl⟩ : syracuseStep 8760959 = 13141439) B13141439
theorem B2594207 : Blo 1729065 2594207 := bstep (se 1 (by rfl) ⟨1945655, by rfl⟩ : syracuseStep 2594207 = 3891311) B3891311
theorem B1729471 : Blo 1729065 1729471 := bstep (se 1 (by rfl) ⟨1297103, by rfl⟩ : syracuseStep 1729471 = 2594207) B2594207
theorem B18712367 : Blo 1729065 18712367 := bstep (se 1 (by rfl) ⟨14034275, by rfl⟩ : syracuseStep 18712367 = 28068551) B28068551
theorem B5838911 : Blo 1729065 5838911 := bstep (se 1 (by rfl) ⟨4379183, by rfl⟩ : syracuseStep 5838911 = 8758367) B8758367
theorem B21043435 : Blo 1729065 21043435 := bstep (se 1 (by rfl) ⟨15782576, by rfl⟩ : syracuseStep 21043435 = 31565153) B31565153
theorem B5840639 : Blo 1729065 5840639 := bstep (se 1 (by rfl) ⟨4380479, by rfl⟩ : syracuseStep 5840639 = 8760959) B8760959
theorem B28057913 : Blo 1729065 28057913 := bstep (se 2 (by rfl) ⟨10521717, by rfl⟩ : syracuseStep 28057913 = 21043435) B21043435
theorem B3892607 : Blo 1729065 3892607 := bstep (se 1 (by rfl) ⟨2919455, by rfl⟩ : syracuseStep 3892607 = 5838911) B5838911
theorem B3893759 : Blo 1729065 3893759 := bstep (se 1 (by rfl) ⟨2920319, by rfl⟩ : syracuseStep 3893759 = 5840639) B5840639
theorem B12474911 : Blo 1729065 12474911 := bstep (se 1 (by rfl) ⟨9356183, by rfl⟩ : syracuseStep 12474911 = 18712367) B18712367
theorem B8316607 : Blo 1729065 8316607 := bstep (se 1 (by rfl) ⟨6237455, by rfl⟩ : syracuseStep 8316607 = 12474911) B12474911
theorem B18705275 : Blo 1729065 18705275 := bstep (se 1 (by rfl) ⟨14028956, by rfl⟩ : syracuseStep 18705275 = 28057913) B28057913
theorem B2595071 : Blo 1729065 2595071 := bstep (se 1 (by rfl) ⟨1946303, by rfl⟩ : syracuseStep 2595071 = 3892607) B3892607
theorem B2595839 : Blo 1729065 2595839 := bstep (se 1 (by rfl) ⟨1946879, by rfl⟩ : syracuseStep 2595839 = 3893759) B3893759
theorem B1730047 : Blo 1729065 1730047 := bstep (se 1 (by rfl) ⟨1297535, by rfl⟩ : syracuseStep 1730047 = 2595071) B2595071
theorem B12470183 : Blo 1729065 12470183 := bstep (se 1 (by rfl) ⟨9352637, by rfl⟩ : syracuseStep 12470183 = 18705275) B18705275
theorem B1730559 : Blo 1729065 1730559 := bstep (se 1 (by rfl) ⟨1297919, by rfl⟩ : syracuseStep 1730559 = 2595839) B2595839
theorem B11088809 : Blo 1729065 11088809 := bstep (se 2 (by rfl) ⟨4158303, by rfl⟩ : syracuseStep 11088809 = 8316607) B8316607
theorem B7392539 : Blo 1729065 7392539 := bstep (se 1 (by rfl) ⟨5544404, by rfl⟩ : syracuseStep 7392539 = 11088809) B11088809
theorem B8313455 : Blo 1729065 8313455 := bstep (se 1 (by rfl) ⟨6235091, by rfl⟩ : syracuseStep 8313455 = 12470183) B12470183
theorem B5542303 : Blo 1729065 5542303 := bstep (se 1 (by rfl) ⟨4156727, by rfl⟩ : syracuseStep 5542303 = 8313455) B8313455
theorem B4928359 : Blo 1729065 4928359 := bstep (se 1 (by rfl) ⟨3696269, by rfl⟩ : syracuseStep 4928359 = 7392539) B7392539
theorem B7389737 : Blo 1729065 7389737 := bstep (se 2 (by rfl) ⟨2771151, by rfl⟩ : syracuseStep 7389737 = 5542303) B5542303
theorem B6571145 : Blo 1729065 6571145 := bstep (se 2 (by rfl) ⟨2464179, by rfl⟩ : syracuseStep 6571145 = 4928359) B4928359
theorem B4926491 : Blo 1729065 4926491 := bstep (se 1 (by rfl) ⟨3694868, by rfl⟩ : syracuseStep 4926491 = 7389737) B7389737
theorem B4380763 : Blo 1729065 4380763 := bstep (se 1 (by rfl) ⟨3285572, by rfl⟩ : syracuseStep 4380763 = 6571145) B6571145
theorem B5841017 : Blo 1729065 5841017 := bstep (se 2 (by rfl) ⟨2190381, by rfl⟩ : syracuseStep 5841017 = 4380763) B4380763
theorem B3284327 : Blo 1729065 3284327 := bstep (se 1 (by rfl) ⟨2463245, by rfl⟩ : syracuseStep 3284327 = 4926491) B4926491
theorem B8758205 : Blo 1729065 8758205 := bstep (se 3 (by rfl) ⟨1642163, by rfl⟩ : syracuseStep 8758205 = 3284327) B3284327
theorem B3894011 : Blo 1729065 3894011 := bstep (se 1 (by rfl) ⟨2920508, by rfl⟩ : syracuseStep 3894011 = 5841017) B5841017
theorem B5838803 : Blo 1729065 5838803 := bstep (se 1 (by rfl) ⟨4379102, by rfl⟩ : syracuseStep 5838803 = 8758205) B8758205
theorem B2596007 : Blo 1729065 2596007 := bstep (se 1 (by rfl) ⟨1947005, by rfl⟩ : syracuseStep 2596007 = 3894011) B3894011
theorem B3892535 : Blo 1729065 3892535 := bstep (se 1 (by rfl) ⟨2919401, by rfl⟩ : syracuseStep 3892535 = 5838803) B5838803
theorem B1730671 : Blo 1729065 1730671 := bstep (se 1 (by rfl) ⟨1298003, by rfl⟩ : syracuseStep 1730671 = 2596007) B2596007
theorem B2595023 : Blo 1729065 2595023 := bstep (se 1 (by rfl) ⟨1946267, by rfl⟩ : syracuseStep 2595023 = 3892535) B3892535
theorem B1730015 : Blo 1729065 1730015 := bstep (se 1 (by rfl) ⟨1297511, by rfl⟩ : syracuseStep 1730015 = 2595023) B2595023

theorem C0 (j : ℕ) (h1 : 432266 ≤ j) (h2 : j ≤ 432765) : Blo 1729065 (4 * j + 3) := by
  interval_cases j
  · exact B1729067
  · exact B1729071
  · exact B1729075
  · exact B1729079
  · exact B1729083
  · exact B1729087
  · exact B1729091
  · exact B1729095
  · exact B1729099
  · exact B1729103
  · exact B1729107
  · exact B1729111
  · exact B1729115
  · exact B1729119
  · exact B1729123
  · exact B1729127
  · exact B1729131
  · exact B1729135
  · exact B1729139
  · exact B1729143
  · exact B1729147
  · exact B1729151
  · exact B1729155
  · exact B1729159
  · exact B1729163
  · exact B1729167
  · exact B1729171
  · exact B1729175
  · exact B1729179
  · exact B1729183
  · exact B1729187
  · exact B1729191
  · exact B1729195
  · exact B1729199
  · exact B1729203
  · exact B1729207
  · exact B1729211
  · exact B1729215
  · exact B1729219
  · exact B1729223
  · exact B1729227
  · exact B1729231
  · exact B1729235
  · exact B1729239
  · exact B1729243
  · exact B1729247
  · exact B1729251
  · exact B1729255
  · exact B1729259
  · exact B1729263
  · exact B1729267
  · exact B1729271
  · exact B1729275
  · exact B1729279
  · exact B1729283
  · exact B1729287
  · exact B1729291
  · exact B1729295
  · exact B1729299
  · exact B1729303
  · exact B1729307
  · exact B1729311
  · exact B1729315
  · exact B1729319
  · exact B1729323
  · exact B1729327
  · exact B1729331
  · exact B1729335
  · exact B1729339
  · exact B1729343
  · exact B1729347
  · exact B1729351
  · exact B1729355
  · exact B1729359
  · exact B1729363
  · exact B1729367
  · exact B1729371
  · exact B1729375
  · exact B1729379
  · exact B1729383
  · exact B1729387
  · exact B1729391
  · exact B1729395
  · exact B1729399
  · exact B1729403
  · exact B1729407
  · exact B1729411
  · exact B1729415
  · exact B1729419
  · exact B1729423
  · exact B1729427
  · exact B1729431
  · exact B1729435
  · exact B1729439
  · exact B1729443
  · exact B1729447
  · exact B1729451
  · exact B1729455
  · exact B1729459
  · exact B1729463
  · exact B1729467
  · exact B1729471
  · exact B1729475
  · exact B1729479
  · exact B1729483
  · exact B1729487
  · exact B1729491
  · exact B1729495
  · exact B1729499
  · exact B1729503
  · exact B1729507
  · exact B1729511
  · exact B1729515
  · exact B1729519
  · exact B1729523
  · exact B1729527
  · exact B1729531
  · exact B1729535
  · exact B1729539
  · exact B1729543
  · exact B1729547
  · exact B1729551
  · exact B1729555
  · exact B1729559
  · exact B1729563
  · exact B1729567
  · exact B1729571
  · exact B1729575
  · exact B1729579
  · exact B1729583
  · exact B1729587
  · exact B1729591
  · exact B1729595
  · exact B1729599
  · exact B1729603
  · exact B1729607
  · exact B1729611
  · exact B1729615
  · exact B1729619
  · exact B1729623
  · exact B1729627
  · exact B1729631
  · exact B1729635
  · exact B1729639
  · exact B1729643
  · exact B1729647
  · exact B1729651
  · exact B1729655
  · exact B1729659
  · exact B1729663
  · exact B1729667
  · exact B1729671
  · exact B1729675
  · exact B1729679
  · exact B1729683
  · exact B1729687
  · exact B1729691
  · exact B1729695
  · exact B1729699
  · exact B1729703
  · exact B1729707
  · exact B1729711
  · exact B1729715
  · exact B1729719
  · exact B1729723
  · exact B1729727
  · exact B1729731
  · exact B1729735
  · exact B1729739
  · exact B1729743
  · exact B1729747
  · exact B1729751
  · exact B1729755
  · exact B1729759
  · exact B1729763
  · exact B1729767
  · exact B1729771
  · exact B1729775
  · exact B1729779
  · exact B1729783
  · exact B1729787
  · exact B1729791
  · exact B1729795
  · exact B1729799
  · exact B1729803
  · exact B1729807
  · exact B1729811
  · exact B1729815
  · exact B1729819
  · exact B1729823
  · exact B1729827
  · exact B1729831
  · exact B1729835
  · exact B1729839
  · exact B1729843
  · exact B1729847
  · exact B1729851
  · exact B1729855
  · exact B1729859
  · exact B1729863
  · exact B1729867
  · exact B1729871
  · exact B1729875
  · exact B1729879
  · exact B1729883
  · exact B1729887
  · exact B1729891
  · exact B1729895
  · exact B1729899
  · exact B1729903
  · exact B1729907
  · exact B1729911
  · exact B1729915
  · exact B1729919
  · exact B1729923
  · exact B1729927
  · exact B1729931
  · exact B1729935
  · exact B1729939
  · exact B1729943
  · exact B1729947
  · exact B1729951
  · exact B1729955
  · exact B1729959
  · exact B1729963
  · exact B1729967
  · exact B1729971
  · exact B1729975
  · exact B1729979
  · exact B1729983
  · exact B1729987
  · exact B1729991
  · exact B1729995
  · exact B1729999
  · exact B1730003
  · exact B1730007
  · exact B1730011
  · exact B1730015
  · exact B1730019
  · exact B1730023
  · exact B1730027
  · exact B1730031
  · exact B1730035
  · exact B1730039
  · exact B1730043
  · exact B1730047
  · exact B1730051
  · exact B1730055
  · exact B1730059
  · exact B1730063
  · exact B1730067
  · exact B1730071
  · exact B1730075
  · exact B1730079
  · exact B1730083
  · exact B1730087
  · exact B1730091
  · exact B1730095
  · exact B1730099
  · exact B1730103
  · exact B1730107
  · exact B1730111
  · exact B1730115
  · exact B1730119
  · exact B1730123
  · exact B1730127
  · exact B1730131
  · exact B1730135
  · exact B1730139
  · exact B1730143
  · exact B1730147
  · exact B1730151
  · exact B1730155
  · exact B1730159
  · exact B1730163
  · exact B1730167
  · exact B1730171
  · exact B1730175
  · exact B1730179
  · exact B1730183
  · exact B1730187
  · exact B1730191
  · exact B1730195
  · exact B1730199
  · exact B1730203
  · exact B1730207
  · exact B1730211
  · exact B1730215
  · exact B1730219
  · exact B1730223
  · exact B1730227
  · exact B1730231
  · exact B1730235
  · exact B1730239
  · exact B1730243
  · exact B1730247
  · exact B1730251
  · exact B1730255
  · exact B1730259
  · exact B1730263
  · exact B1730267
  · exact B1730271
  · exact B1730275
  · exact B1730279
  · exact B1730283
  · exact B1730287
  · exact B1730291
  · exact B1730295
  · exact B1730299
  · exact B1730303
  · exact B1730307
  · exact B1730311
  · exact B1730315
  · exact B1730319
  · exact B1730323
  · exact B1730327
  · exact B1730331
  · exact B1730335
  · exact B1730339
  · exact B1730343
  · exact B1730347
  · exact B1730351
  · exact B1730355
  · exact B1730359
  · exact B1730363
  · exact B1730367
  · exact B1730371
  · exact B1730375
  · exact B1730379
  · exact B1730383
  · exact B1730387
  · exact B1730391
  · exact B1730395
  · exact B1730399
  · exact B1730403
  · exact B1730407
  · exact B1730411
  · exact B1730415
  · exact B1730419
  · exact B1730423
  · exact B1730427
  · exact B1730431
  · exact B1730435
  · exact B1730439
  · exact B1730443
  · exact B1730447
  · exact B1730451
  · exact B1730455
  · exact B1730459
  · exact B1730463
  · exact B1730467
  · exact B1730471
  · exact B1730475
  · exact B1730479
  · exact B1730483
  · exact B1730487
  · exact B1730491
  · exact B1730495
  · exact B1730499
  · exact B1730503
  · exact B1730507
  · exact B1730511
  · exact B1730515
  · exact B1730519
  · exact B1730523
  · exact B1730527
  · exact B1730531
  · exact B1730535
  · exact B1730539
  · exact B1730543
  · exact B1730547
  · exact B1730551
  · exact B1730555
  · exact B1730559
  · exact B1730563
  · exact B1730567
  · exact B1730571
  · exact B1730575
  · exact B1730579
  · exact B1730583
  · exact B1730587
  · exact B1730591
  · exact B1730595
  · exact B1730599
  · exact B1730603
  · exact B1730607
  · exact B1730611
  · exact B1730615
  · exact B1730619
  · exact B1730623
  · exact B1730627
  · exact B1730631
  · exact B1730635
  · exact B1730639
  · exact B1730643
  · exact B1730647
  · exact B1730651
  · exact B1730655
  · exact B1730659
  · exact B1730663
  · exact B1730667
  · exact B1730671
  · exact B1730675
  · exact B1730679
  · exact B1730683
  · exact B1730687
  · exact B1730691
  · exact B1730695
  · exact B1730699
  · exact B1730703
  · exact B1730707
  · exact B1730711
  · exact B1730715
  · exact B1730719
  · exact B1730723
  · exact B1730727
  · exact B1730731
  · exact B1730735
  · exact B1730739
  · exact B1730743
  · exact B1730747
  · exact B1730751
  · exact B1730755
  · exact B1730759
  · exact B1730763
  · exact B1730767
  · exact B1730771
  · exact B1730775
  · exact B1730779
  · exact B1730783
  · exact B1730787
  · exact B1730791
  · exact B1730795
  · exact B1730799
  · exact B1730803
  · exact B1730807
  · exact B1730811
  · exact B1730815
  · exact B1730819
  · exact B1730823
  · exact B1730827
  · exact B1730831
  · exact B1730835
  · exact B1730839
  · exact B1730843
  · exact B1730847
  · exact B1730851
  · exact B1730855
  · exact B1730859
  · exact B1730863
  · exact B1730867
  · exact B1730871
  · exact B1730875
  · exact B1730879
  · exact B1730883
  · exact B1730887
  · exact B1730891
  · exact B1730895
  · exact B1730899
  · exact B1730903
  · exact B1730907
  · exact B1730911
  · exact B1730915
  · exact B1730919
  · exact B1730923
  · exact B1730927
  · exact B1730931
  · exact B1730935
  · exact B1730939
  · exact B1730943
  · exact B1730947
  · exact B1730951
  · exact B1730955
  · exact B1730959
  · exact B1730963
  · exact B1730967
  · exact B1730971
  · exact B1730975
  · exact B1730979
  · exact B1730983
  · exact B1730987
  · exact B1730991
  · exact B1730995
  · exact B1730999
  · exact B1731003
  · exact B1731007
  · exact B1731011
  · exact B1731015
  · exact B1731019
  · exact B1731023
  · exact B1731027
  · exact B1731031
  · exact B1731035
  · exact B1731039
  · exact B1731043
  · exact B1731047
  · exact B1731051
  · exact B1731055
  · exact B1731059
  · exact B1731063

theorem solution (m : ℕ) (hlo : 1729065 ≤ m) (hhi : m ≤ 1731065) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 432266 ≤ j := by omega
    have hj2 : j ≤ 432765 := by omega
    have hb : Blo 1729065 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
