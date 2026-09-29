-- Prove2me | solution 1 for syracuse_descends_range_872567_876567
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:42.893355+00:00
-- url     : https://prove2.me/submissions/1c9d4392-bae9-4106-b579-31793446fff4

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


theorem B1966085 : Blo 872567 1966085 := bbase (se 4 (by rfl) ⟨184320, by rfl⟩ : syracuseStep 1966085 = 368641) (by norm_num)
theorem B1310741 : Blo 872567 1310741 := bbase (se 6 (by rfl) ⟨30720, by rfl⟩ : syracuseStep 1310741 = 61441) (by norm_num)
theorem B983065 : Blo 872567 983065 := bbase (se 2 (by rfl) ⟨368649, by rfl⟩ : syracuseStep 983065 = 737299) (by norm_num)
theorem B1310765 : Blo 872567 1310765 := bbase (se 3 (by rfl) ⟨245768, by rfl⟩ : syracuseStep 1310765 = 491537) (by norm_num)
theorem B4423733 : Blo 872567 4423733 := bbase (se 5 (by rfl) ⟨207362, by rfl⟩ : syracuseStep 4423733 = 414725) (by norm_num)
theorem B983101 : Blo 872567 983101 := bbase (se 3 (by rfl) ⟨184331, by rfl⟩ : syracuseStep 983101 = 368663) (by norm_num)
theorem B1310789 : Blo 872567 1310789 := bbase (se 4 (by rfl) ⟨122886, by rfl⟩ : syracuseStep 1310789 = 245773) (by norm_num)
theorem B1966157 : Blo 872567 1966157 := bbase (se 3 (by rfl) ⟨368654, by rfl⟩ : syracuseStep 1966157 = 737309) (by norm_num)
theorem B1867853 : Blo 872567 1867853 := bbase (se 3 (by rfl) ⟨350222, by rfl⟩ : syracuseStep 1867853 = 700445) (by norm_num)
theorem B1474645 : Blo 872567 1474645 := bbase (se 8 (by rfl) ⟨8640, by rfl⟩ : syracuseStep 1474645 = 17281) (by norm_num)
theorem B1310813 : Blo 872567 1310813 := bbase (se 3 (by rfl) ⟨245777, by rfl⟩ : syracuseStep 1310813 = 491555) (by norm_num)
theorem B983137 : Blo 872567 983137 := bbase (se 2 (by rfl) ⟨368676, by rfl⟩ : syracuseStep 983137 = 737353) (by norm_num)
theorem B1310837 : Blo 872567 1310837 := bbase (se 5 (by rfl) ⟨61445, by rfl⟩ : syracuseStep 1310837 = 122891) (by norm_num)
theorem B983173 : Blo 872567 983173 := bbase (se 4 (by rfl) ⟨92172, by rfl⟩ : syracuseStep 983173 = 184345) (by norm_num)
theorem B3997829 : Blo 872567 3997829 := bbase (se 4 (by rfl) ⟨374796, by rfl⟩ : syracuseStep 3997829 = 749593) (by norm_num)
theorem B1310861 : Blo 872567 1310861 := bbase (se 3 (by rfl) ⟨245786, by rfl⟩ : syracuseStep 1310861 = 491573) (by norm_num)
theorem B1966229 : Blo 872567 1966229 := bbase (se 6 (by rfl) ⟨46083, by rfl⟩ : syracuseStep 1966229 = 92167) (by norm_num)
theorem B1310885 : Blo 872567 1310885 := bbase (se 4 (by rfl) ⟨122895, by rfl⟩ : syracuseStep 1310885 = 245791) (by norm_num)
theorem B983209 : Blo 872567 983209 := bbase (se 2 (by rfl) ⟨368703, by rfl⟩ : syracuseStep 983209 = 737407) (by norm_num)
theorem B1474733 : Blo 872567 1474733 := bbase (se 3 (by rfl) ⟨276512, by rfl⟩ : syracuseStep 1474733 = 553025) (by norm_num)
theorem B1310909 : Blo 872567 1310909 := bbase (se 3 (by rfl) ⟨245795, by rfl⟩ : syracuseStep 1310909 = 491591) (by norm_num)
theorem B2949317 : Blo 872567 2949317 := bbase (se 4 (by rfl) ⟨276498, by rfl⟩ : syracuseStep 2949317 = 552997) (by norm_num)
theorem B983245 : Blo 872567 983245 := bbase (se 3 (by rfl) ⟨184358, by rfl⟩ : syracuseStep 983245 = 368717) (by norm_num)
theorem B1310933 : Blo 872567 1310933 := bbase (se 7 (by rfl) ⟨15362, by rfl⟩ : syracuseStep 1310933 = 30725) (by norm_num)
theorem B7798997 : Blo 872567 7798997 := bbase (se 7 (by rfl) ⟨91394, by rfl⟩ : syracuseStep 7798997 = 182789) (by norm_num)
theorem B1048793 : Blo 872567 1048793 := bbase (se 2 (by rfl) ⟨393297, by rfl⟩ : syracuseStep 1048793 = 786595) (by norm_num)
theorem B1769693 : Blo 872567 1769693 := bbase (se 3 (by rfl) ⟨331817, by rfl⟩ : syracuseStep 1769693 = 663635) (by norm_num)
theorem B1966301 : Blo 872567 1966301 := bbase (se 3 (by rfl) ⟨368681, by rfl⟩ : syracuseStep 1966301 = 737363) (by norm_num)
theorem B1310957 : Blo 872567 1310957 := bbase (se 3 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 1310957 = 491609) (by norm_num)
theorem B983281 : Blo 872567 983281 := bbase (se 2 (by rfl) ⟨368730, by rfl⟩ : syracuseStep 983281 = 737461) (by norm_num)
theorem B1310981 : Blo 872567 1310981 := bbase (se 4 (by rfl) ⟨122904, by rfl⟩ : syracuseStep 1310981 = 245809) (by norm_num)
theorem B983317 : Blo 872567 983317 := bbase (se 6 (by rfl) ⟨23046, by rfl⟩ : syracuseStep 983317 = 46093) (by norm_num)
theorem B3997973 : Blo 872567 3997973 := bbase (se 6 (by rfl) ⟨93702, by rfl⟩ : syracuseStep 3997973 = 187405) (by norm_num)
theorem B1311005 : Blo 872567 1311005 := bbase (se 3 (by rfl) ⟨245813, by rfl⟩ : syracuseStep 1311005 = 491627) (by norm_num)
theorem B1966373 : Blo 872567 1966373 := bbase (se 4 (by rfl) ⟨184347, by rfl⟩ : syracuseStep 1966373 = 368695) (by norm_num)
theorem B1474861 : Blo 872567 1474861 := bbase (se 3 (by rfl) ⟨276536, by rfl⟩ : syracuseStep 1474861 = 553073) (by norm_num)
theorem B1311029 : Blo 872567 1311029 := bbase (se 5 (by rfl) ⟨61454, by rfl⟩ : syracuseStep 1311029 = 122909) (by norm_num)
theorem B983353 : Blo 872567 983353 := bbase (se 2 (by rfl) ⟨368757, by rfl⟩ : syracuseStep 983353 = 737515) (by norm_num)
theorem B885065 : Blo 872567 885065 := bbase (se 2 (by rfl) ⟨331899, by rfl⟩ : syracuseStep 885065 = 663799) (by norm_num)
theorem B1311053 : Blo 872567 1311053 := bbase (se 3 (by rfl) ⟨245822, by rfl⟩ : syracuseStep 1311053 = 491645) (by norm_num)
theorem B2490709 : Blo 872567 2490709 := bbase (se 10 (by rfl) ⟨3648, by rfl⟩ : syracuseStep 2490709 = 7297) (by norm_num)
theorem B983389 : Blo 872567 983389 := bbase (se 3 (by rfl) ⟨184385, by rfl⟩ : syracuseStep 983389 = 368771) (by norm_num)
theorem B1311077 : Blo 872567 1311077 := bbase (se 4 (by rfl) ⟨122913, by rfl⟩ : syracuseStep 1311077 = 245827) (by norm_num)
theorem B1966445 : Blo 872567 1966445 := bbase (se 3 (by rfl) ⟨368708, by rfl⟩ : syracuseStep 1966445 = 737417) (by norm_num)
theorem B1311101 : Blo 872567 1311101 := bbase (se 3 (by rfl) ⟨245831, by rfl⟩ : syracuseStep 1311101 = 491663) (by norm_num)
theorem B1245565 : Blo 872567 1245565 := bbase (se 3 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 1245565 = 467087) (by norm_num)
theorem B983425 : Blo 872567 983425 := bbase (se 2 (by rfl) ⟨368784, by rfl⟩ : syracuseStep 983425 = 737569) (by norm_num)
theorem B1474949 : Blo 872567 1474949 := bbase (se 4 (by rfl) ⟨138276, by rfl⟩ : syracuseStep 1474949 = 276553) (by norm_num)
theorem B1311125 : Blo 872567 1311125 := bbase (se 6 (by rfl) ⟨30729, by rfl⟩ : syracuseStep 1311125 = 61459) (by norm_num)
theorem B983461 : Blo 872567 983461 := bbase (se 4 (by rfl) ⟨92199, by rfl⟩ : syracuseStep 983461 = 184399) (by norm_num)
theorem B1311149 : Blo 872567 1311149 := bbase (se 3 (by rfl) ⟨245840, by rfl⟩ : syracuseStep 1311149 = 491681) (by norm_num)
theorem B1966517 : Blo 872567 1966517 := bbase (se 5 (by rfl) ⟨92180, by rfl⟩ : syracuseStep 1966517 = 184361) (by norm_num)
theorem B1311173 : Blo 872567 1311173 := bbase (se 4 (by rfl) ⟨122922, by rfl⟩ : syracuseStep 1311173 = 245845) (by norm_num)
theorem B983497 : Blo 872567 983497 := bbase (se 2 (by rfl) ⟨368811, by rfl⟩ : syracuseStep 983497 = 737623) (by norm_num)
theorem B1180109 : Blo 872567 1180109 := bbase (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) (by norm_num)
theorem B1573333 : Blo 872567 1573333 := bbase (se 7 (by rfl) ⟨18437, by rfl⟩ : syracuseStep 1573333 = 36875) (by norm_num)
theorem B1311197 : Blo 872567 1311197 := bbase (se 3 (by rfl) ⟨245849, by rfl⟩ : syracuseStep 1311197 = 491699) (by norm_num)
theorem B983533 : Blo 872567 983533 := bbase (se 3 (by rfl) ⟨184412, by rfl⟩ : syracuseStep 983533 = 368825) (by norm_num)
theorem B1311221 : Blo 872567 1311221 := bbase (se 5 (by rfl) ⟨61463, by rfl⟩ : syracuseStep 1311221 = 122927) (by norm_num)
theorem B1966589 : Blo 872567 1966589 := bbase (se 3 (by rfl) ⟨368735, by rfl⟩ : syracuseStep 1966589 = 737471) (by norm_num)
theorem B1475077 : Blo 872567 1475077 := bbase (se 4 (by rfl) ⟨138288, by rfl⟩ : syracuseStep 1475077 = 276577) (by norm_num)
theorem B1311245 : Blo 872567 1311245 := bbase (se 3 (by rfl) ⟨245858, by rfl⟩ : syracuseStep 1311245 = 491717) (by norm_num)
theorem B983569 : Blo 872567 983569 := bbase (se 2 (by rfl) ⟨368838, by rfl⟩ : syracuseStep 983569 = 737677) (by norm_num)
theorem B1311269 : Blo 872567 1311269 := bbase (se 4 (by rfl) ⟨122931, by rfl⟩ : syracuseStep 1311269 = 245863) (by norm_num)
theorem B983605 : Blo 872567 983605 := bbase (se 5 (by rfl) ⟨46106, by rfl⟩ : syracuseStep 983605 = 92213) (by norm_num)
theorem B1311293 : Blo 872567 1311293 := bbase (se 3 (by rfl) ⟨245867, by rfl⟩ : syracuseStep 1311293 = 491735) (by norm_num)
theorem B3146309 : Blo 872567 3146309 := bbase (se 4 (by rfl) ⟨294966, by rfl⟩ : syracuseStep 3146309 = 589933) (by norm_num)
theorem B1966661 : Blo 872567 1966661 := bbase (se 4 (by rfl) ⟨184374, by rfl⟩ : syracuseStep 1966661 = 368749) (by norm_num)
theorem B1311317 : Blo 872567 1311317 := bbase (se 8 (by rfl) ⟨7683, by rfl⟩ : syracuseStep 1311317 = 15367) (by norm_num)
theorem B983641 : Blo 872567 983641 := bbase (se 2 (by rfl) ⟨368865, by rfl⟩ : syracuseStep 983641 = 737731) (by norm_num)
theorem B1475165 : Blo 872567 1475165 := bbase (se 3 (by rfl) ⟨276593, by rfl⟩ : syracuseStep 1475165 = 553187) (by norm_num)
theorem B1311341 : Blo 872567 1311341 := bbase (se 3 (by rfl) ⟨245876, by rfl⟩ : syracuseStep 1311341 = 491753) (by norm_num)
theorem B2949749 : Blo 872567 2949749 := bbase (se 5 (by rfl) ⟨138269, by rfl⟩ : syracuseStep 2949749 = 276539) (by norm_num)
theorem B983677 : Blo 872567 983677 := bbase (se 3 (by rfl) ⟨184439, by rfl⟩ : syracuseStep 983677 = 368879) (by norm_num)
theorem B1311365 : Blo 872567 1311365 := bbase (se 4 (by rfl) ⟨122940, by rfl⟩ : syracuseStep 1311365 = 245881) (by norm_num)
theorem B1966733 : Blo 872567 1966733 := bbase (se 3 (by rfl) ⟨368762, by rfl⟩ : syracuseStep 1966733 = 737525) (by norm_num)
theorem B1311389 : Blo 872567 1311389 := bbase (se 3 (by rfl) ⟨245885, by rfl⟩ : syracuseStep 1311389 = 491771) (by norm_num)
theorem B983713 : Blo 872567 983713 := bbase (se 2 (by rfl) ⟨368892, by rfl⟩ : syracuseStep 983713 = 737785) (by norm_num)
theorem B1311413 : Blo 872567 1311413 := bbase (se 5 (by rfl) ⟨61472, by rfl⟩ : syracuseStep 1311413 = 122945) (by norm_num)
theorem B983749 : Blo 872567 983749 := bbase (se 4 (by rfl) ⟨92226, by rfl⟩ : syracuseStep 983749 = 184453) (by norm_num)
theorem B1311437 : Blo 872567 1311437 := bbase (se 3 (by rfl) ⟨245894, by rfl⟩ : syracuseStep 1311437 = 491789) (by norm_num)
theorem B6292181 : Blo 872567 6292181 := bbase (se 7 (by rfl) ⟨73736, by rfl⟩ : syracuseStep 6292181 = 147473) (by norm_num)
theorem B1966805 : Blo 872567 1966805 := bbase (se 7 (by rfl) ⟨23048, by rfl⟩ : syracuseStep 1966805 = 46097) (by norm_num)
theorem B1475293 : Blo 872567 1475293 := bbase (se 3 (by rfl) ⟨276617, by rfl⟩ : syracuseStep 1475293 = 553235) (by norm_num)
theorem B1311461 : Blo 872567 1311461 := bbase (se 4 (by rfl) ⟨122949, by rfl⟩ : syracuseStep 1311461 = 245899) (by norm_num)
theorem B983785 : Blo 872567 983785 := bbase (se 2 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 983785 = 737839) (by norm_num)
theorem B1311485 : Blo 872567 1311485 := bbase (se 3 (by rfl) ⟨245903, by rfl⟩ : syracuseStep 1311485 = 491807) (by norm_num)
theorem B983821 : Blo 872567 983821 := bbase (se 3 (by rfl) ⟨184466, by rfl⟩ : syracuseStep 983821 = 368933) (by norm_num)
theorem B1311509 : Blo 872567 1311509 := bbase (se 6 (by rfl) ⟨30738, by rfl⟩ : syracuseStep 1311509 = 61477) (by norm_num)
theorem B1966877 : Blo 872567 1966877 := bbase (se 3 (by rfl) ⟨368789, by rfl⟩ : syracuseStep 1966877 = 737579) (by norm_num)
theorem B1311533 : Blo 872567 1311533 := bbase (se 3 (by rfl) ⟨245912, by rfl⟩ : syracuseStep 1311533 = 491825) (by norm_num)
theorem B983857 : Blo 872567 983857 := bbase (se 2 (by rfl) ⟨368946, by rfl⟩ : syracuseStep 983857 = 737893) (by norm_num)
theorem B1475381 : Blo 872567 1475381 := bbase (se 5 (by rfl) ⟨69158, by rfl⟩ : syracuseStep 1475381 = 138317) (by norm_num)
theorem B1311557 : Blo 872567 1311557 := bbase (se 4 (by rfl) ⟨122958, by rfl⟩ : syracuseStep 1311557 = 245917) (by norm_num)
theorem B983893 : Blo 872567 983893 := bbase (se 9 (by rfl) ⟨2882, by rfl⟩ : syracuseStep 983893 = 5765) (by norm_num)
theorem B1311581 : Blo 872567 1311581 := bbase (se 3 (by rfl) ⟨245921, by rfl⟩ : syracuseStep 1311581 = 491843) (by norm_num)
theorem B1966949 : Blo 872567 1966949 := bbase (se 4 (by rfl) ⟨184401, by rfl⟩ : syracuseStep 1966949 = 368803) (by norm_num)
theorem B1311605 : Blo 872567 1311605 := bbase (se 5 (by rfl) ⟨61481, by rfl⟩ : syracuseStep 1311605 = 122963) (by norm_num)
theorem B4981621 : Blo 872567 4981621 := bbase (se 5 (by rfl) ⟨233513, by rfl⟩ : syracuseStep 4981621 = 467027) (by norm_num)
theorem B983929 : Blo 872567 983929 := bbase (se 2 (by rfl) ⟨368973, by rfl⟩ : syracuseStep 983929 = 737947) (by norm_num)
theorem B1049485 : Blo 872567 1049485 := bbase (se 3 (by rfl) ⟨196778, by rfl⟩ : syracuseStep 1049485 = 393557) (by norm_num)
theorem B1311629 : Blo 872567 1311629 := bbase (se 3 (by rfl) ⟨245930, by rfl⟩ : syracuseStep 1311629 = 491861) (by norm_num)
theorem B885649 : Blo 872567 885649 := bbase (se 2 (by rfl) ⟨332118, by rfl⟩ : syracuseStep 885649 = 664237) (by norm_num)
theorem B2655125 : Blo 872567 2655125 := bbase (se 6 (by rfl) ⟨62229, by rfl⟩ : syracuseStep 2655125 = 124459) (by norm_num)
theorem B983965 : Blo 872567 983965 := bbase (se 3 (by rfl) ⟨184493, by rfl⟩ : syracuseStep 983965 = 368987) (by norm_num)
theorem B1311653 : Blo 872567 1311653 := bbase (se 4 (by rfl) ⟨122967, by rfl⟩ : syracuseStep 1311653 = 245935) (by norm_num)
theorem B1967021 : Blo 872567 1967021 := bbase (se 3 (by rfl) ⟨368816, by rfl⟩ : syracuseStep 1967021 = 737633) (by norm_num)
theorem B1475509 : Blo 872567 1475509 := bbase (se 5 (by rfl) ⟨69164, by rfl⟩ : syracuseStep 1475509 = 138329) (by norm_num)
theorem B6652853 : Blo 872567 6652853 := bbase (se 5 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 6652853 = 623705) (by norm_num)
theorem B1311677 : Blo 872567 1311677 := bbase (se 3 (by rfl) ⟨245939, by rfl⟩ : syracuseStep 1311677 = 491879) (by norm_num)
theorem B984001 : Blo 872567 984001 := bbase (se 2 (by rfl) ⟨369000, by rfl⟩ : syracuseStep 984001 = 738001) (by norm_num)
theorem B1868741 : Blo 872567 1868741 := bbase (se 4 (by rfl) ⟨175194, by rfl⟩ : syracuseStep 1868741 = 350389) (by norm_num)
theorem B1311701 : Blo 872567 1311701 := bbase (se 7 (by rfl) ⟨15371, by rfl⟩ : syracuseStep 1311701 = 30743) (by norm_num)
theorem B984037 : Blo 872567 984037 := bbase (se 4 (by rfl) ⟨92253, by rfl⟩ : syracuseStep 984037 = 184507) (by norm_num)
theorem B1049581 : Blo 872567 1049581 := bbase (se 3 (by rfl) ⟨196796, by rfl⟩ : syracuseStep 1049581 = 393593) (by norm_num)
theorem B1311725 : Blo 872567 1311725 := bbase (se 3 (by rfl) ⟨245948, by rfl⟩ : syracuseStep 1311725 = 491897) (by norm_num)
theorem B1967093 : Blo 872567 1967093 := bbase (se 5 (by rfl) ⟨92207, by rfl⟩ : syracuseStep 1967093 = 184415) (by norm_num)
theorem B1311749 : Blo 872567 1311749 := bbase (se 4 (by rfl) ⟨122976, by rfl⟩ : syracuseStep 1311749 = 245953) (by norm_num)
theorem B984073 : Blo 872567 984073 := bbase (se 2 (by rfl) ⟨369027, by rfl⟩ : syracuseStep 984073 = 738055) (by norm_num)
theorem B1475597 : Blo 872567 1475597 := bbase (se 3 (by rfl) ⟨276674, by rfl⟩ : syracuseStep 1475597 = 553349) (by norm_num)
theorem B1311773 : Blo 872567 1311773 := bbase (se 3 (by rfl) ⟨245957, by rfl⟩ : syracuseStep 1311773 = 491915) (by norm_num)
theorem B2950181 : Blo 872567 2950181 := bbase (se 4 (by rfl) ⟨276579, by rfl⟩ : syracuseStep 2950181 = 553159) (by norm_num)
theorem B984109 : Blo 872567 984109 := bbase (se 3 (by rfl) ⟨184520, by rfl⟩ : syracuseStep 984109 = 369041) (by norm_num)
theorem B1311797 : Blo 872567 1311797 := bbase (se 5 (by rfl) ⟨61490, by rfl⟩ : syracuseStep 1311797 = 122981) (by norm_num)
theorem B1967165 : Blo 872567 1967165 := bbase (se 3 (by rfl) ⟨368843, by rfl⟩ : syracuseStep 1967165 = 737687) (by norm_num)
theorem B1311821 : Blo 872567 1311821 := bbase (se 3 (by rfl) ⟨245966, by rfl⟩ : syracuseStep 1311821 = 491933) (by norm_num)
theorem B984145 : Blo 872567 984145 := bbase (se 2 (by rfl) ⟨369054, by rfl⟩ : syracuseStep 984145 = 738109) (by norm_num)
theorem B1311845 : Blo 872567 1311845 := bbase (se 4 (by rfl) ⟨122985, by rfl⟩ : syracuseStep 1311845 = 245971) (by norm_num)
theorem B984181 : Blo 872567 984181 := bbase (se 5 (by rfl) ⟨46133, by rfl⟩ : syracuseStep 984181 = 92267) (by norm_num)
theorem B1311869 : Blo 872567 1311869 := bbase (se 3 (by rfl) ⟨245975, by rfl⟩ : syracuseStep 1311869 = 491951) (by norm_num)
theorem B1967237 : Blo 872567 1967237 := bbase (se 4 (by rfl) ⟨184428, by rfl⟩ : syracuseStep 1967237 = 368857) (by norm_num)
theorem B1475725 : Blo 872567 1475725 := bbase (se 3 (by rfl) ⟨276698, by rfl⟩ : syracuseStep 1475725 = 553397) (by norm_num)
theorem B1311893 : Blo 872567 1311893 := bbase (se 6 (by rfl) ⟨30747, by rfl⟩ : syracuseStep 1311893 = 61495) (by norm_num)
theorem B1246357 : Blo 872567 1246357 := bbase (se 6 (by rfl) ⟨29211, by rfl⟩ : syracuseStep 1246357 = 58423) (by norm_num)
theorem B984217 : Blo 872567 984217 := bbase (se 2 (by rfl) ⟨369081, by rfl⟩ : syracuseStep 984217 = 738163) (by norm_num)
theorem B1311917 : Blo 872567 1311917 := bbase (se 3 (by rfl) ⟨245984, by rfl⟩ : syracuseStep 1311917 = 491969) (by norm_num)
theorem B984253 : Blo 872567 984253 := bbase (se 3 (by rfl) ⟨184547, by rfl⟩ : syracuseStep 984253 = 369095) (by norm_num)
theorem B1868989 : Blo 872567 1868989 := bbase (se 3 (by rfl) ⟨350435, by rfl⟩ : syracuseStep 1868989 = 700871) (by norm_num)
theorem B1311941 : Blo 872567 1311941 := bbase (se 4 (by rfl) ⟨122994, by rfl⟩ : syracuseStep 1311941 = 245989) (by norm_num)
theorem B1967309 : Blo 872567 1967309 := bbase (se 3 (by rfl) ⟨368870, by rfl⟩ : syracuseStep 1967309 = 737741) (by norm_num)
theorem B1311965 : Blo 872567 1311965 := bbase (se 3 (by rfl) ⟨245993, by rfl⟩ : syracuseStep 1311965 = 491987) (by norm_num)
theorem B984289 : Blo 872567 984289 := bbase (se 2 (by rfl) ⟨369108, by rfl⟩ : syracuseStep 984289 = 738217) (by norm_num)
theorem B1475813 : Blo 872567 1475813 := bbase (se 4 (by rfl) ⟨138357, by rfl⟩ : syracuseStep 1475813 = 276715) (by norm_num)
theorem B1311989 : Blo 872567 1311989 := bbase (se 5 (by rfl) ⟨61499, by rfl⟩ : syracuseStep 1311989 = 122999) (by norm_num)
theorem B984325 : Blo 872567 984325 := bbase (se 4 (by rfl) ⟨92280, by rfl⟩ : syracuseStep 984325 = 184561) (by norm_num)
theorem B1312013 : Blo 872567 1312013 := bbase (se 3 (by rfl) ⟨246002, by rfl⟩ : syracuseStep 1312013 = 492005) (by norm_num)
theorem B1967381 : Blo 872567 1967381 := bbase (se 6 (by rfl) ⟨46110, by rfl⟩ : syracuseStep 1967381 = 92221) (by norm_num)
theorem B1312037 : Blo 872567 1312037 := bbase (se 4 (by rfl) ⟨123003, by rfl⟩ : syracuseStep 1312037 = 246007) (by norm_num)
theorem B984361 : Blo 872567 984361 := bbase (se 2 (by rfl) ⟨369135, by rfl⟩ : syracuseStep 984361 = 738271) (by norm_num)
theorem B1312061 : Blo 872567 1312061 := bbase (se 3 (by rfl) ⟨246011, by rfl⟩ : syracuseStep 1312061 = 492023) (by norm_num)
theorem B1574213 : Blo 872567 1574213 := bbase (se 4 (by rfl) ⟨147582, by rfl⟩ : syracuseStep 1574213 = 295165) (by norm_num)
theorem B4425029 : Blo 872567 4425029 := bbase (se 4 (by rfl) ⟨414846, by rfl⟩ : syracuseStep 4425029 = 829693) (by norm_num)
theorem B984397 : Blo 872567 984397 := bbase (se 3 (by rfl) ⟨184574, by rfl⟩ : syracuseStep 984397 = 369149) (by norm_num)
theorem B1312085 : Blo 872567 1312085 := bbase (se 12 (by rfl) ⟨480, by rfl⟩ : syracuseStep 1312085 = 961) (by norm_num)
theorem B1967453 : Blo 872567 1967453 := bbase (se 3 (by rfl) ⟨368897, by rfl⟩ : syracuseStep 1967453 = 737795) (by norm_num)
theorem B1475941 : Blo 872567 1475941 := bbase (se 4 (by rfl) ⟨138369, by rfl⟩ : syracuseStep 1475941 = 276739) (by norm_num)
theorem B1049965 : Blo 872567 1049965 := bbase (se 3 (by rfl) ⟨196868, by rfl⟩ : syracuseStep 1049965 = 393737) (by norm_num)
theorem B1312109 : Blo 872567 1312109 := bbase (se 3 (by rfl) ⟨246020, by rfl⟩ : syracuseStep 1312109 = 492041) (by norm_num)
theorem B984433 : Blo 872567 984433 := bbase (se 2 (by rfl) ⟨369162, by rfl⟩ : syracuseStep 984433 = 738325) (by norm_num)
theorem B1312133 : Blo 872567 1312133 := bbase (se 4 (by rfl) ⟨123012, by rfl⟩ : syracuseStep 1312133 = 246025) (by norm_num)
theorem B984469 : Blo 872567 984469 := bbase (se 6 (by rfl) ⟨23073, by rfl⟩ : syracuseStep 984469 = 46147) (by norm_num)
theorem B1312157 : Blo 872567 1312157 := bbase (se 3 (by rfl) ⟨246029, by rfl⟩ : syracuseStep 1312157 = 492059) (by norm_num)
theorem B1967525 : Blo 872567 1967525 := bbase (se 4 (by rfl) ⟨184455, by rfl⟩ : syracuseStep 1967525 = 368911) (by norm_num)
theorem B2491813 : Blo 872567 2491813 := bbase (se 4 (by rfl) ⟨233607, by rfl⟩ : syracuseStep 2491813 = 467215) (by norm_num)
theorem B1312181 : Blo 872567 1312181 := bbase (se 5 (by rfl) ⟨61508, by rfl⟩ : syracuseStep 1312181 = 123017) (by norm_num)
theorem B984505 : Blo 872567 984505 := bbase (se 2 (by rfl) ⟨369189, by rfl⟩ : syracuseStep 984505 = 738379) (by norm_num)
theorem B1476029 : Blo 872567 1476029 := bbase (se 3 (by rfl) ⟨276755, by rfl⟩ : syracuseStep 1476029 = 553511) (by norm_num)
theorem B1312205 : Blo 872567 1312205 := bbase (se 3 (by rfl) ⟨246038, by rfl⟩ : syracuseStep 1312205 = 492077) (by norm_num)
theorem B2950613 : Blo 872567 2950613 := bbase (se 7 (by rfl) ⟨34577, by rfl⟩ : syracuseStep 2950613 = 69155) (by norm_num)
theorem B984541 : Blo 872567 984541 := bbase (se 3 (by rfl) ⟨184601, by rfl⟩ : syracuseStep 984541 = 369203) (by norm_num)
theorem B1312229 : Blo 872567 1312229 := bbase (se 4 (by rfl) ⟨123021, by rfl⟩ : syracuseStep 1312229 = 246043) (by norm_num)
theorem B1246693 : Blo 872567 1246693 := bbase (se 4 (by rfl) ⟨116877, by rfl⟩ : syracuseStep 1246693 = 233755) (by norm_num)
theorem B1967597 : Blo 872567 1967597 := bbase (se 3 (by rfl) ⟨368924, by rfl⟩ : syracuseStep 1967597 = 737849) (by norm_num)
theorem B1312253 : Blo 872567 1312253 := bbase (se 3 (by rfl) ⟨246047, by rfl⟩ : syracuseStep 1312253 = 492095) (by norm_num)
theorem B984577 : Blo 872567 984577 := bbase (se 2 (by rfl) ⟨369216, by rfl⟩ : syracuseStep 984577 = 738433) (by norm_num)
theorem B1312277 : Blo 872567 1312277 := bbase (se 6 (by rfl) ⟨30756, by rfl⟩ : syracuseStep 1312277 = 61513) (by norm_num)
theorem B984613 : Blo 872567 984613 := bbase (se 4 (by rfl) ⟨92307, by rfl⟩ : syracuseStep 984613 = 184615) (by norm_num)
theorem B1312301 : Blo 872567 1312301 := bbase (se 3 (by rfl) ⟨246056, by rfl⟩ : syracuseStep 1312301 = 492113) (by norm_num)
theorem B1967669 : Blo 872567 1967669 := bbase (se 5 (by rfl) ⟨92234, by rfl⟩ : syracuseStep 1967669 = 184469) (by norm_num)
theorem B1476157 : Blo 872567 1476157 := bbase (se 3 (by rfl) ⟨276779, by rfl⟩ : syracuseStep 1476157 = 553559) (by norm_num)
theorem B1312325 : Blo 872567 1312325 := bbase (se 4 (by rfl) ⟨123030, by rfl⟩ : syracuseStep 1312325 = 246061) (by norm_num)
theorem B984649 : Blo 872567 984649 := bbase (se 2 (by rfl) ⟨369243, by rfl⟩ : syracuseStep 984649 = 738487) (by norm_num)
theorem B3737173 : Blo 872567 3737173 := bbase (se 8 (by rfl) ⟨21897, by rfl⟩ : syracuseStep 3737173 = 43795) (by norm_num)
theorem B1312349 : Blo 872567 1312349 := bbase (se 3 (by rfl) ⟨246065, by rfl⟩ : syracuseStep 1312349 = 492131) (by norm_num)
theorem B984685 : Blo 872567 984685 := bbase (se 3 (by rfl) ⟨184628, by rfl⟩ : syracuseStep 984685 = 369257) (by norm_num)
theorem B1312373 : Blo 872567 1312373 := bbase (se 5 (by rfl) ⟨61517, by rfl⟩ : syracuseStep 1312373 = 123035) (by norm_num)
theorem B1967741 : Blo 872567 1967741 := bbase (se 3 (by rfl) ⟨368951, by rfl⟩ : syracuseStep 1967741 = 737903) (by norm_num)
theorem B1312397 : Blo 872567 1312397 := bbase (se 3 (by rfl) ⟨246074, by rfl⟩ : syracuseStep 1312397 = 492149) (by norm_num)
theorem B984721 : Blo 872567 984721 := bbase (se 2 (by rfl) ⟨369270, by rfl⟩ : syracuseStep 984721 = 738541) (by norm_num)
theorem B1476245 : Blo 872567 1476245 := bbase (se 6 (by rfl) ⟨34599, by rfl⟩ : syracuseStep 1476245 = 69199) (by norm_num)
theorem B1312421 : Blo 872567 1312421 := bbase (se 4 (by rfl) ⟨123039, by rfl⟩ : syracuseStep 1312421 = 246079) (by norm_num)
theorem B1869493 : Blo 872567 1869493 := bbase (se 5 (by rfl) ⟨87632, by rfl⟩ : syracuseStep 1869493 = 175265) (by norm_num)
theorem B984757 : Blo 872567 984757 := bbase (se 5 (by rfl) ⟨46160, by rfl⟩ : syracuseStep 984757 = 92321) (by norm_num)
theorem B1312445 : Blo 872567 1312445 := bbase (se 3 (by rfl) ⟨246083, by rfl⟩ : syracuseStep 1312445 = 492167) (by norm_num)
theorem B1246909 : Blo 872567 1246909 := bbase (se 3 (by rfl) ⟨233795, by rfl⟩ : syracuseStep 1246909 = 467591) (by norm_num)
theorem B1967813 : Blo 872567 1967813 := bbase (se 4 (by rfl) ⟨184482, by rfl⟩ : syracuseStep 1967813 = 368965) (by norm_num)
theorem B1312469 : Blo 872567 1312469 := bbase (se 7 (by rfl) ⟨15380, by rfl⟩ : syracuseStep 1312469 = 30761) (by norm_num)
theorem B984793 : Blo 872567 984793 := bbase (se 2 (by rfl) ⟨369297, by rfl⟩ : syracuseStep 984793 = 738595) (by norm_num)
theorem B2655973 : Blo 872567 2655973 := bbase (se 4 (by rfl) ⟨248997, by rfl⟩ : syracuseStep 2655973 = 497995) (by norm_num)
theorem B1312493 : Blo 872567 1312493 := bbase (se 3 (by rfl) ⟨246092, by rfl⟩ : syracuseStep 1312493 = 492185) (by norm_num)
theorem B5310197 : Blo 872567 5310197 := bbase (se 5 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 5310197 = 497831) (by norm_num)
theorem B984829 : Blo 872567 984829 := bbase (se 3 (by rfl) ⟨184655, by rfl⟩ : syracuseStep 984829 = 369311) (by norm_num)
theorem B1312517 : Blo 872567 1312517 := bbase (se 4 (by rfl) ⟨123048, by rfl⟩ : syracuseStep 1312517 = 246097) (by norm_num)
theorem B1967885 : Blo 872567 1967885 := bbase (se 3 (by rfl) ⟨368978, by rfl⟩ : syracuseStep 1967885 = 737957) (by norm_num)
theorem B1476373 : Blo 872567 1476373 := bbase (se 6 (by rfl) ⟨34602, by rfl⟩ : syracuseStep 1476373 = 69205) (by norm_num)
theorem B1312541 : Blo 872567 1312541 := bbase (se 3 (by rfl) ⟨246101, by rfl⟩ : syracuseStep 1312541 = 492203) (by norm_num)
theorem B984865 : Blo 872567 984865 := bbase (se 2 (by rfl) ⟨369324, by rfl⟩ : syracuseStep 984865 = 738649) (by norm_num)
theorem B2361125 : Blo 872567 2361125 := bbase (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) (by norm_num)
theorem B1312565 : Blo 872567 1312565 := bbase (se 5 (by rfl) ⟨61526, by rfl⟩ : syracuseStep 1312565 = 123053) (by norm_num)
theorem B3147589 : Blo 872567 3147589 := bbase (se 4 (by rfl) ⟨295086, by rfl⟩ : syracuseStep 3147589 = 590173) (by norm_num)
theorem B984901 : Blo 872567 984901 := bbase (se 4 (by rfl) ⟨92334, by rfl⟩ : syracuseStep 984901 = 184669) (by norm_num)
theorem B1312589 : Blo 872567 1312589 := bbase (se 3 (by rfl) ⟨246110, by rfl⟩ : syracuseStep 1312589 = 492221) (by norm_num)
theorem B1181525 : Blo 872567 1181525 := bbase (se 9 (by rfl) ⟨3461, by rfl⟩ : syracuseStep 1181525 = 6923) (by norm_num)
theorem B1967957 : Blo 872567 1967957 := bbase (se 9 (by rfl) ⟨5765, by rfl⟩ : syracuseStep 1967957 = 11531) (by norm_num)
theorem B9471829 : Blo 872567 9471829 := bbase (se 9 (by rfl) ⟨27749, by rfl⟩ : syracuseStep 9471829 = 55499) (by norm_num)
theorem B1312613 : Blo 872567 1312613 := bbase (se 4 (by rfl) ⟨123057, by rfl⟩ : syracuseStep 1312613 = 246115) (by norm_num)
theorem B984937 : Blo 872567 984937 := bbase (se 2 (by rfl) ⟨369351, by rfl⟩ : syracuseStep 984937 = 738703) (by norm_num)
theorem B1476461 : Blo 872567 1476461 := bbase (se 3 (by rfl) ⟨276836, by rfl⟩ : syracuseStep 1476461 = 553673) (by norm_num)
theorem B1312637 : Blo 872567 1312637 := bbase (se 3 (by rfl) ⟨246119, by rfl⟩ : syracuseStep 1312637 = 492239) (by norm_num)
theorem B2951045 : Blo 872567 2951045 := bbase (se 4 (by rfl) ⟨276660, by rfl⟩ : syracuseStep 2951045 = 553321) (by norm_num)
theorem B984973 : Blo 872567 984973 := bbase (se 3 (by rfl) ⟨184682, by rfl⟩ : syracuseStep 984973 = 369365) (by norm_num)
theorem B1312661 : Blo 872567 1312661 := bbase (se 6 (by rfl) ⟨30765, by rfl⟩ : syracuseStep 1312661 = 61531) (by norm_num)
theorem B1968029 : Blo 872567 1968029 := bbase (se 3 (by rfl) ⟨369005, by rfl⟩ : syracuseStep 1968029 = 738011) (by norm_num)
theorem B1312685 : Blo 872567 1312685 := bbase (se 3 (by rfl) ⟨246128, by rfl⟩ : syracuseStep 1312685 = 492257) (by norm_num)
theorem B985009 : Blo 872567 985009 := bbase (se 2 (by rfl) ⟨369378, by rfl⟩ : syracuseStep 985009 = 738757) (by norm_num)
theorem B1771445 : Blo 872567 1771445 := bbase (se 5 (by rfl) ⟨83036, by rfl⟩ : syracuseStep 1771445 = 166073) (by norm_num)
theorem B1312709 : Blo 872567 1312709 := bbase (se 4 (by rfl) ⟨123066, by rfl⟩ : syracuseStep 1312709 = 246133) (by norm_num)
theorem B985045 : Blo 872567 985045 := bbase (se 7 (by rfl) ⟨11543, by rfl⟩ : syracuseStep 985045 = 23087) (by norm_num)
theorem B1312733 : Blo 872567 1312733 := bbase (se 3 (by rfl) ⟨246137, by rfl⟩ : syracuseStep 1312733 = 492275) (by norm_num)
theorem B1968101 : Blo 872567 1968101 := bbase (se 4 (by rfl) ⟨184509, by rfl⟩ : syracuseStep 1968101 = 369019) (by norm_num)
theorem B1476589 : Blo 872567 1476589 := bbase (se 3 (by rfl) ⟨276860, by rfl⟩ : syracuseStep 1476589 = 553721) (by norm_num)
theorem B1312757 : Blo 872567 1312757 := bbase (se 5 (by rfl) ⟨61535, by rfl⟩ : syracuseStep 1312757 = 123071) (by norm_num)
theorem B985081 : Blo 872567 985081 := bbase (se 2 (by rfl) ⟨369405, by rfl⟩ : syracuseStep 985081 = 738811) (by norm_num)
theorem B1312781 : Blo 872567 1312781 := bbase (se 3 (by rfl) ⟨246146, by rfl⟩ : syracuseStep 1312781 = 492293) (by norm_num)
theorem B985117 : Blo 872567 985117 := bbase (se 3 (by rfl) ⟨184709, by rfl⟩ : syracuseStep 985117 = 369419) (by norm_num)
theorem B1312805 : Blo 872567 1312805 := bbase (se 4 (by rfl) ⟨123075, by rfl⟩ : syracuseStep 1312805 = 246151) (by norm_num)
theorem B1968173 : Blo 872567 1968173 := bbase (se 3 (by rfl) ⟨369032, by rfl⟩ : syracuseStep 1968173 = 738065) (by norm_num)
theorem B1247285 : Blo 872567 1247285 := bbase (se 5 (by rfl) ⟨58466, by rfl⟩ : syracuseStep 1247285 = 116933) (by norm_num)
theorem B1312829 : Blo 872567 1312829 := bbase (se 3 (by rfl) ⟨246155, by rfl⟩ : syracuseStep 1312829 = 492311) (by norm_num)
theorem B985153 : Blo 872567 985153 := bbase (se 2 (by rfl) ⟨369432, by rfl⟩ : syracuseStep 985153 = 738865) (by norm_num)
theorem B1476677 : Blo 872567 1476677 := bbase (se 4 (by rfl) ⟨138438, by rfl⟩ : syracuseStep 1476677 = 276877) (by norm_num)
theorem B1312853 : Blo 872567 1312853 := bbase (se 8 (by rfl) ⟨7692, by rfl⟩ : syracuseStep 1312853 = 15385) (by norm_num)
theorem B985189 : Blo 872567 985189 := bbase (se 4 (by rfl) ⟨92361, by rfl⟩ : syracuseStep 985189 = 184723) (by norm_num)
theorem B1312877 : Blo 872567 1312877 := bbase (se 3 (by rfl) ⟨246164, by rfl⟩ : syracuseStep 1312877 = 492329) (by norm_num)
theorem B1968245 : Blo 872567 1968245 := bbase (se 5 (by rfl) ⟨92261, by rfl⟩ : syracuseStep 1968245 = 184523) (by norm_num)
theorem B1312901 : Blo 872567 1312901 := bbase (se 4 (by rfl) ⟨123084, by rfl⟩ : syracuseStep 1312901 = 246169) (by norm_num)
theorem B985225 : Blo 872567 985225 := bbase (se 2 (by rfl) ⟨369459, by rfl⟩ : syracuseStep 985225 = 738919) (by norm_num)
theorem B1312925 : Blo 872567 1312925 := bbase (se 3 (by rfl) ⟨246173, by rfl⟩ : syracuseStep 1312925 = 492347) (by norm_num)
theorem B985261 : Blo 872567 985261 := bbase (se 3 (by rfl) ⟨184736, by rfl⟩ : syracuseStep 985261 = 369473) (by norm_num)
theorem B1312949 : Blo 872567 1312949 := bbase (se 5 (by rfl) ⟨61544, by rfl⟩ : syracuseStep 1312949 = 123089) (by norm_num)
theorem B1968317 : Blo 872567 1968317 := bbase (se 3 (by rfl) ⟨369059, by rfl⟩ : syracuseStep 1968317 = 738119) (by norm_num)
theorem B1476805 : Blo 872567 1476805 := bbase (se 4 (by rfl) ⟨138450, by rfl⟩ : syracuseStep 1476805 = 276901) (by norm_num)
theorem B1312973 : Blo 872567 1312973 := bbase (se 3 (by rfl) ⟨246182, by rfl⟩ : syracuseStep 1312973 = 492365) (by norm_num)
theorem B985297 : Blo 872567 985297 := bbase (se 2 (by rfl) ⟨369486, by rfl⟩ : syracuseStep 985297 = 738973) (by norm_num)
theorem B1312997 : Blo 872567 1312997 := bbase (se 4 (by rfl) ⟨123093, by rfl⟩ : syracuseStep 1312997 = 246187) (by norm_num)
theorem B985333 : Blo 872567 985333 := bbase (se 5 (by rfl) ⟨46187, by rfl⟩ : syracuseStep 985333 = 92375) (by norm_num)
theorem B1313021 : Blo 872567 1313021 := bbase (se 3 (by rfl) ⟨246191, by rfl⟩ : syracuseStep 1313021 = 492383) (by norm_num)
theorem B1968389 : Blo 872567 1968389 := bbase (se 4 (by rfl) ⟨184536, by rfl⟩ : syracuseStep 1968389 = 369073) (by norm_num)
theorem B1313045 : Blo 872567 1313045 := bbase (se 6 (by rfl) ⟨30774, by rfl⟩ : syracuseStep 1313045 = 61549) (by norm_num)
theorem B985369 : Blo 872567 985369 := bbase (se 2 (by rfl) ⟨369513, by rfl⟩ : syracuseStep 985369 = 739027) (by norm_num)
theorem B1476893 : Blo 872567 1476893 := bbase (se 3 (by rfl) ⟨276917, by rfl⟩ : syracuseStep 1476893 = 553835) (by norm_num)
theorem B1313069 : Blo 872567 1313069 := bbase (se 3 (by rfl) ⟨246200, by rfl⟩ : syracuseStep 1313069 = 492401) (by norm_num)
theorem B2951477 : Blo 872567 2951477 := bbase (se 5 (by rfl) ⟨138350, by rfl⟩ : syracuseStep 2951477 = 276701) (by norm_num)
theorem B985405 : Blo 872567 985405 := bbase (se 3 (by rfl) ⟨184763, by rfl⟩ : syracuseStep 985405 = 369527) (by norm_num)
theorem B887105 : Blo 872567 887105 := bbase (se 2 (by rfl) ⟨332664, by rfl⟩ : syracuseStep 887105 = 665329) (by norm_num)
theorem B1313093 : Blo 872567 1313093 := bbase (se 4 (by rfl) ⟨123102, by rfl⟩ : syracuseStep 1313093 = 246205) (by norm_num)
theorem B1968461 : Blo 872567 1968461 := bbase (se 3 (by rfl) ⟨369086, by rfl⟩ : syracuseStep 1968461 = 738173) (by norm_num)
theorem B887117 : Blo 872567 887117 := bbase (se 3 (by rfl) ⟨166334, by rfl⟩ : syracuseStep 887117 = 332669) (by norm_num)
theorem B1313117 : Blo 872567 1313117 := bbase (se 3 (by rfl) ⟨246209, by rfl⟩ : syracuseStep 1313117 = 492419) (by norm_num)
theorem B985441 : Blo 872567 985441 := bbase (se 2 (by rfl) ⟨369540, by rfl⟩ : syracuseStep 985441 = 739081) (by norm_num)
theorem B1313141 : Blo 872567 1313141 := bbase (se 5 (by rfl) ⟨61553, by rfl⟩ : syracuseStep 1313141 = 123107) (by norm_num)
theorem B1051013 : Blo 872567 1051013 := bbase (se 4 (by rfl) ⟨98532, by rfl⟩ : syracuseStep 1051013 = 197065) (by norm_num)
theorem B985477 : Blo 872567 985477 := bbase (se 4 (by rfl) ⟨92388, by rfl⟩ : syracuseStep 985477 = 184777) (by norm_num)
theorem B1313165 : Blo 872567 1313165 := bbase (se 3 (by rfl) ⟨246218, by rfl⟩ : syracuseStep 1313165 = 492437) (by norm_num)
theorem B1968533 : Blo 872567 1968533 := bbase (se 6 (by rfl) ⟨46137, by rfl⟩ : syracuseStep 1968533 = 92275) (by norm_num)
theorem B1477021 : Blo 872567 1477021 := bbase (se 3 (by rfl) ⟨276941, by rfl⟩ : syracuseStep 1477021 = 553883) (by norm_num)
theorem B1313189 : Blo 872567 1313189 := bbase (se 4 (by rfl) ⟨123111, by rfl⟩ : syracuseStep 1313189 = 246223) (by norm_num)
theorem B985513 : Blo 872567 985513 := bbase (se 2 (by rfl) ⟨369567, by rfl⟩ : syracuseStep 985513 = 739135) (by norm_num)
theorem B1313213 : Blo 872567 1313213 := bbase (se 3 (by rfl) ⟨246227, by rfl⟩ : syracuseStep 1313213 = 492455) (by norm_num)
theorem B985549 : Blo 872567 985549 := bbase (se 3 (by rfl) ⟨184790, by rfl⟩ : syracuseStep 985549 = 369581) (by norm_num)
theorem B1313237 : Blo 872567 1313237 := bbase (se 7 (by rfl) ⟨15389, by rfl⟩ : syracuseStep 1313237 = 30779) (by norm_num)
theorem B1968605 : Blo 872567 1968605 := bbase (se 3 (by rfl) ⟨369113, by rfl⟩ : syracuseStep 1968605 = 738227) (by norm_num)
theorem B1313261 : Blo 872567 1313261 := bbase (se 3 (by rfl) ⟨246236, by rfl⟩ : syracuseStep 1313261 = 492473) (by norm_num)
theorem B985585 : Blo 872567 985585 := bbase (se 2 (by rfl) ⟨369594, by rfl⟩ : syracuseStep 985585 = 739189) (by norm_num)
theorem B1477109 : Blo 872567 1477109 := bbase (se 5 (by rfl) ⟨69239, by rfl⟩ : syracuseStep 1477109 = 138479) (by norm_num)
theorem B1313285 : Blo 872567 1313285 := bbase (se 4 (by rfl) ⟨123120, by rfl⟩ : syracuseStep 1313285 = 246241) (by norm_num)
theorem B985621 : Blo 872567 985621 := bbase (se 6 (by rfl) ⟨23100, by rfl⟩ : syracuseStep 985621 = 46201) (by norm_num)
theorem B1313309 : Blo 872567 1313309 := bbase (se 3 (by rfl) ⟨246245, by rfl⟩ : syracuseStep 1313309 = 492491) (by norm_num)
theorem B1968677 : Blo 872567 1968677 := bbase (se 4 (by rfl) ⟨184563, by rfl⟩ : syracuseStep 1968677 = 369127) (by norm_num)
theorem B1870381 : Blo 872567 1870381 := bbase (se 3 (by rfl) ⟨350696, by rfl⟩ : syracuseStep 1870381 = 701393) (by norm_num)
theorem B1313333 : Blo 872567 1313333 := bbase (se 5 (by rfl) ⟨61562, by rfl⟩ : syracuseStep 1313333 = 123125) (by norm_num)
theorem B985657 : Blo 872567 985657 := bbase (se 2 (by rfl) ⟨369621, by rfl⟩ : syracuseStep 985657 = 739243) (by norm_num)
theorem B1313357 : Blo 872567 1313357 := bbase (se 3 (by rfl) ⟨246254, by rfl⟩ : syracuseStep 1313357 = 492509) (by norm_num)
theorem B4426325 : Blo 872567 4426325 := bbase (se 8 (by rfl) ⟨25935, by rfl⟩ : syracuseStep 4426325 = 51871) (by norm_num)
theorem B985693 : Blo 872567 985693 := bbase (se 3 (by rfl) ⟨184817, by rfl⟩ : syracuseStep 985693 = 369635) (by norm_num)
theorem B1313381 : Blo 872567 1313381 := bbase (se 4 (by rfl) ⟨123129, by rfl⟩ : syracuseStep 1313381 = 246259) (by norm_num)
theorem B1968749 : Blo 872567 1968749 := bbase (se 3 (by rfl) ⟨369140, by rfl⟩ : syracuseStep 1968749 = 738281) (by norm_num)
theorem B1477237 : Blo 872567 1477237 := bbase (se 5 (by rfl) ⟨69245, by rfl⟩ : syracuseStep 1477237 = 138491) (by norm_num)
theorem B1313405 : Blo 872567 1313405 := bbase (se 3 (by rfl) ⟨246263, by rfl⟩ : syracuseStep 1313405 = 492527) (by norm_num)
theorem B985729 : Blo 872567 985729 := bbase (se 2 (by rfl) ⟨369648, by rfl⟩ : syracuseStep 985729 = 739297) (by norm_num)
theorem B1313429 : Blo 872567 1313429 := bbase (se 6 (by rfl) ⟨30783, by rfl⟩ : syracuseStep 1313429 = 61567) (by norm_num)
theorem B985765 : Blo 872567 985765 := bbase (se 4 (by rfl) ⟨92415, by rfl⟩ : syracuseStep 985765 = 184831) (by norm_num)
theorem B1313453 : Blo 872567 1313453 := bbase (se 3 (by rfl) ⟨246272, by rfl⟩ : syracuseStep 1313453 = 492545) (by norm_num)
theorem B1968821 : Blo 872567 1968821 := bbase (se 5 (by rfl) ⟨92288, by rfl⟩ : syracuseStep 1968821 = 184577) (by norm_num)
theorem B1051321 : Blo 872567 1051321 := bbase (se 2 (by rfl) ⟨394245, by rfl⟩ : syracuseStep 1051321 = 788491) (by norm_num)
theorem B1313477 : Blo 872567 1313477 := bbase (se 4 (by rfl) ⟨123138, by rfl⟩ : syracuseStep 1313477 = 246277) (by norm_num)
theorem B985801 : Blo 872567 985801 := bbase (se 2 (by rfl) ⟨369675, by rfl⟩ : syracuseStep 985801 = 739351) (by norm_num)
theorem B1477325 : Blo 872567 1477325 := bbase (se 3 (by rfl) ⟨276998, by rfl⟩ : syracuseStep 1477325 = 553997) (by norm_num)
theorem B1051349 : Blo 872567 1051349 := bbase (se 7 (by rfl) ⟨12320, by rfl⟩ : syracuseStep 1051349 = 24641) (by norm_num)
theorem B1313501 : Blo 872567 1313501 := bbase (se 3 (by rfl) ⟨246281, by rfl⟩ : syracuseStep 1313501 = 492563) (by norm_num)
theorem B2951909 : Blo 872567 2951909 := bbase (se 4 (by rfl) ⟨276741, by rfl⟩ : syracuseStep 2951909 = 553483) (by norm_num)
theorem B985837 : Blo 872567 985837 := bbase (se 3 (by rfl) ⟨184844, by rfl⟩ : syracuseStep 985837 = 369689) (by norm_num)
theorem B1313525 : Blo 872567 1313525 := bbase (se 5 (by rfl) ⟨61571, by rfl⟩ : syracuseStep 1313525 = 123143) (by norm_num)
theorem B1968893 : Blo 872567 1968893 := bbase (se 3 (by rfl) ⟨369167, by rfl⟩ : syracuseStep 1968893 = 738335) (by norm_num)
theorem B1313549 : Blo 872567 1313549 := bbase (se 3 (by rfl) ⟨246290, by rfl⟩ : syracuseStep 1313549 = 492581) (by norm_num)
theorem B985873 : Blo 872567 985873 := bbase (se 2 (by rfl) ⟨369702, by rfl⟩ : syracuseStep 985873 = 739405) (by norm_num)
theorem B1313573 : Blo 872567 1313573 := bbase (se 4 (by rfl) ⟨123147, by rfl⟩ : syracuseStep 1313573 = 246295) (by norm_num)
theorem B4983605 : Blo 872567 4983605 := bbase (se 5 (by rfl) ⟨233606, by rfl⟩ : syracuseStep 4983605 = 467213) (by norm_num)
theorem B985909 : Blo 872567 985909 := bbase (se 5 (by rfl) ⟨46214, by rfl⟩ : syracuseStep 985909 = 92429) (by norm_num)
theorem B1313597 : Blo 872567 1313597 := bbase (se 3 (by rfl) ⟨246299, by rfl⟩ : syracuseStep 1313597 = 492599) (by norm_num)
theorem B1968965 : Blo 872567 1968965 := bbase (se 4 (by rfl) ⟨184590, by rfl⟩ : syracuseStep 1968965 = 369181) (by norm_num)
theorem B1477453 : Blo 872567 1477453 := bbase (se 3 (by rfl) ⟨277022, by rfl⟩ : syracuseStep 1477453 = 554045) (by norm_num)
theorem B1313621 : Blo 872567 1313621 := bbase (se 9 (by rfl) ⟨3848, by rfl⟩ : syracuseStep 1313621 = 7697) (by norm_num)
theorem B985945 : Blo 872567 985945 := bbase (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) (by norm_num)
theorem B1313645 : Blo 872567 1313645 := bbase (se 3 (by rfl) ⟨246308, by rfl⟩ : syracuseStep 1313645 = 492617) (by norm_num)
theorem B985981 : Blo 872567 985981 := bbase (se 3 (by rfl) ⟨184871, by rfl⟩ : syracuseStep 985981 = 369743) (by norm_num)
theorem B2493317 : Blo 872567 2493317 := bbase (se 4 (by rfl) ⟨233748, by rfl⟩ : syracuseStep 2493317 = 467497) (by norm_num)
theorem B1313669 : Blo 872567 1313669 := bbase (se 4 (by rfl) ⟨123156, by rfl⟩ : syracuseStep 1313669 = 246313) (by norm_num)
theorem B1969037 : Blo 872567 1969037 := bbase (se 3 (by rfl) ⟨369194, by rfl⟩ : syracuseStep 1969037 = 738389) (by norm_num)
theorem B1313693 : Blo 872567 1313693 := bbase (se 3 (by rfl) ⟨246317, by rfl⟩ : syracuseStep 1313693 = 492635) (by norm_num)
theorem B986017 : Blo 872567 986017 := bbase (se 2 (by rfl) ⟨369756, by rfl⟩ : syracuseStep 986017 = 739513) (by norm_num)
theorem B1477541 : Blo 872567 1477541 := bbase (se 4 (by rfl) ⟨138519, by rfl⟩ : syracuseStep 1477541 = 277039) (by norm_num)
theorem B1313717 : Blo 872567 1313717 := bbase (se 5 (by rfl) ⟨61580, by rfl⟩ : syracuseStep 1313717 = 123161) (by norm_num)
theorem B986053 : Blo 872567 986053 := bbase (se 4 (by rfl) ⟨92442, by rfl⟩ : syracuseStep 986053 = 184885) (by norm_num)
theorem B1313741 : Blo 872567 1313741 := bbase (se 3 (by rfl) ⟨246326, by rfl⟩ : syracuseStep 1313741 = 492653) (by norm_num)
theorem B2100181 : Blo 872567 2100181 := bbase (se 7 (by rfl) ⟨24611, by rfl⟩ : syracuseStep 2100181 = 49223) (by norm_num)
theorem B1969109 : Blo 872567 1969109 := bbase (se 7 (by rfl) ⟨23075, by rfl⟩ : syracuseStep 1969109 = 46151) (by norm_num)
theorem B1313765 : Blo 872567 1313765 := bbase (se 4 (by rfl) ⟨123165, by rfl⟩ : syracuseStep 1313765 = 246331) (by norm_num)
theorem B986089 : Blo 872567 986089 := bbase (se 2 (by rfl) ⟨369783, by rfl⟩ : syracuseStep 986089 = 739567) (by norm_num)
theorem B1313789 : Blo 872567 1313789 := bbase (se 3 (by rfl) ⟨246335, by rfl⟩ : syracuseStep 1313789 = 492671) (by norm_num)
theorem B986125 : Blo 872567 986125 := bbase (se 3 (by rfl) ⟨184898, by rfl⟩ : syracuseStep 986125 = 369797) (by norm_num)
theorem B1313813 : Blo 872567 1313813 := bbase (se 6 (by rfl) ⟨30792, by rfl⟩ : syracuseStep 1313813 = 61585) (by norm_num)
theorem B1969181 : Blo 872567 1969181 := bbase (se 3 (by rfl) ⟨369221, by rfl⟩ : syracuseStep 1969181 = 738443) (by norm_num)
theorem B1870877 : Blo 872567 1870877 := bbase (se 3 (by rfl) ⟨350789, by rfl⟩ : syracuseStep 1870877 = 701579) (by norm_num)
theorem B1477669 : Blo 872567 1477669 := bbase (se 4 (by rfl) ⟨138531, by rfl⟩ : syracuseStep 1477669 = 277063) (by norm_num)
theorem B1313837 : Blo 872567 1313837 := bbase (se 3 (by rfl) ⟨246344, by rfl⟩ : syracuseStep 1313837 = 492689) (by norm_num)
theorem B1313861 : Blo 872567 1313861 := bbase (se 4 (by rfl) ⟨123174, by rfl⟩ : syracuseStep 1313861 = 246349) (by norm_num)
theorem B1313885 : Blo 872567 1313885 := bbase (se 3 (by rfl) ⟨246353, by rfl⟩ : syracuseStep 1313885 = 492707) (by norm_num)
theorem B1969253 : Blo 872567 1969253 := bbase (se 4 (by rfl) ⟨184617, by rfl⟩ : syracuseStep 1969253 = 369235) (by norm_num)
theorem B1313909 : Blo 872567 1313909 := bbase (se 5 (by rfl) ⟨61589, by rfl⟩ : syracuseStep 1313909 = 123179) (by norm_num)
theorem B1477757 : Blo 872567 1477757 := bbase (se 3 (by rfl) ⟨277079, by rfl⟩ : syracuseStep 1477757 = 554159) (by norm_num)
theorem B1313933 : Blo 872567 1313933 := bbase (se 3 (by rfl) ⟨246362, by rfl⟩ : syracuseStep 1313933 = 492725) (by norm_num)
theorem B2952341 : Blo 872567 2952341 := bbase (se 6 (by rfl) ⟨69195, by rfl⟩ : syracuseStep 2952341 = 138391) (by norm_num)
theorem B1313957 : Blo 872567 1313957 := bbase (se 4 (by rfl) ⟨123183, by rfl⟩ : syracuseStep 1313957 = 246367) (by norm_num)
theorem B1969325 : Blo 872567 1969325 := bbase (se 3 (by rfl) ⟨369248, by rfl⟩ : syracuseStep 1969325 = 738497) (by norm_num)
theorem B1313981 : Blo 872567 1313981 := bbase (se 3 (by rfl) ⟨246371, by rfl⟩ : syracuseStep 1313981 = 492743) (by norm_num)
theorem B1051849 : Blo 872567 1051849 := bbase (se 2 (by rfl) ⟨394443, by rfl⟩ : syracuseStep 1051849 = 788887) (by norm_num)
theorem B888017 : Blo 872567 888017 := bbase (se 2 (by rfl) ⟨333006, by rfl⟩ : syracuseStep 888017 = 666013) (by norm_num)
theorem B1314005 : Blo 872567 1314005 := bbase (se 7 (by rfl) ⟨15398, by rfl⟩ : syracuseStep 1314005 = 30797) (by norm_num)
theorem B1314029 : Blo 872567 1314029 := bbase (se 3 (by rfl) ⟨246380, by rfl⟩ : syracuseStep 1314029 = 492761) (by norm_num)
theorem B1969397 : Blo 872567 1969397 := bbase (se 5 (by rfl) ⟨92315, by rfl⟩ : syracuseStep 1969397 = 184631) (by norm_num)
theorem B1477885 : Blo 872567 1477885 := bbase (se 3 (by rfl) ⟨277103, by rfl⟩ : syracuseStep 1477885 = 554207) (by norm_num)
theorem B1314053 : Blo 872567 1314053 := bbase (se 4 (by rfl) ⟨123192, by rfl⟩ : syracuseStep 1314053 = 246385) (by norm_num)
theorem B1314077 : Blo 872567 1314077 := bbase (se 3 (by rfl) ⟨246389, by rfl⟩ : syracuseStep 1314077 = 492779) (by norm_num)
theorem B1314101 : Blo 872567 1314101 := bbase (se 5 (by rfl) ⟨61598, by rfl⟩ : syracuseStep 1314101 = 123197) (by norm_num)
theorem B1969469 : Blo 872567 1969469 := bbase (se 3 (by rfl) ⟨369275, by rfl⟩ : syracuseStep 1969469 = 738551) (by norm_num)
theorem B1314125 : Blo 872567 1314125 := bbase (se 3 (by rfl) ⟨246398, by rfl⟩ : syracuseStep 1314125 = 492797) (by norm_num)
theorem B1477973 : Blo 872567 1477973 := bbase (se 11 (by rfl) ⟨1082, by rfl⟩ : syracuseStep 1477973 = 2165) (by norm_num)
theorem B1314149 : Blo 872567 1314149 := bbase (se 4 (by rfl) ⟨123201, by rfl⟩ : syracuseStep 1314149 = 246403) (by norm_num)
theorem B1314173 : Blo 872567 1314173 := bbase (se 3 (by rfl) ⟨246407, by rfl⟩ : syracuseStep 1314173 = 492815) (by norm_num)
theorem B1969541 : Blo 872567 1969541 := bbase (se 4 (by rfl) ⟨184644, by rfl⟩ : syracuseStep 1969541 = 369289) (by norm_num)
theorem B1314197 : Blo 872567 1314197 := bbase (se 6 (by rfl) ⟨30801, by rfl⟩ : syracuseStep 1314197 = 61603) (by norm_num)
theorem B1314221 : Blo 872567 1314221 := bbase (se 3 (by rfl) ⟨246416, by rfl⟩ : syracuseStep 1314221 = 492833) (by norm_num)
theorem B888241 : Blo 872567 888241 := bbase (se 2 (by rfl) ⟨333090, by rfl⟩ : syracuseStep 888241 = 666181) (by norm_num)
theorem B1314245 : Blo 872567 1314245 := bbase (se 4 (by rfl) ⟨123210, by rfl⟩ : syracuseStep 1314245 = 246421) (by norm_num)
theorem B1969613 : Blo 872567 1969613 := bbase (se 3 (by rfl) ⟨369302, by rfl⟩ : syracuseStep 1969613 = 738605) (by norm_num)
theorem B4197845 : Blo 872567 4197845 := bbase (se 7 (by rfl) ⟨49193, by rfl⟩ : syracuseStep 4197845 = 98387) (by norm_num)
theorem B1478101 : Blo 872567 1478101 := bbase (se 7 (by rfl) ⟨17321, by rfl⟩ : syracuseStep 1478101 = 34643) (by norm_num)
theorem B1314269 : Blo 872567 1314269 := bbase (se 3 (by rfl) ⟨246425, by rfl⟩ : syracuseStep 1314269 = 492851) (by norm_num)
theorem B1314293 : Blo 872567 1314293 := bbase (se 5 (by rfl) ⟨61607, by rfl⟩ : syracuseStep 1314293 = 123215) (by norm_num)
theorem B1314317 : Blo 872567 1314317 := bbase (se 3 (by rfl) ⟨246434, by rfl⟩ : syracuseStep 1314317 = 492869) (by norm_num)
theorem B7573013 : Blo 872567 7573013 := bbase (se 6 (by rfl) ⟨177492, by rfl⟩ : syracuseStep 7573013 = 354985) (by norm_num)
theorem B1969685 : Blo 872567 1969685 := bbase (se 6 (by rfl) ⟨46164, by rfl⟩ : syracuseStep 1969685 = 92329) (by norm_num)
theorem B1314341 : Blo 872567 1314341 := bbase (se 4 (by rfl) ⟨123219, by rfl⟩ : syracuseStep 1314341 = 246439) (by norm_num)
theorem B1478189 : Blo 872567 1478189 := bbase (se 3 (by rfl) ⟨277160, by rfl⟩ : syracuseStep 1478189 = 554321) (by norm_num)
theorem B4722229 : Blo 872567 4722229 := bbase (se 5 (by rfl) ⟨221354, by rfl⟩ : syracuseStep 4722229 = 442709) (by norm_num)
theorem B1314365 : Blo 872567 1314365 := bbase (se 3 (by rfl) ⟨246443, by rfl⟩ : syracuseStep 1314365 = 492887) (by norm_num)
theorem B2952773 : Blo 872567 2952773 := bbase (se 4 (by rfl) ⟨276822, by rfl⟩ : syracuseStep 2952773 = 553645) (by norm_num)
theorem B1314389 : Blo 872567 1314389 := bbase (se 8 (by rfl) ⟨7701, by rfl⟩ : syracuseStep 1314389 = 15403) (by norm_num)
theorem B1969757 : Blo 872567 1969757 := bbase (se 3 (by rfl) ⟨369329, by rfl⟩ : syracuseStep 1969757 = 738659) (by norm_num)
theorem B1314413 : Blo 872567 1314413 := bbase (se 3 (by rfl) ⟨246452, by rfl⟩ : syracuseStep 1314413 = 492905) (by norm_num)
theorem B2100853 : Blo 872567 2100853 := bbase (se 5 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 2100853 = 196955) (by norm_num)
theorem B1314437 : Blo 872567 1314437 := bbase (se 4 (by rfl) ⟨123228, by rfl⟩ : syracuseStep 1314437 = 246457) (by norm_num)
theorem B1314461 : Blo 872567 1314461 := bbase (se 3 (by rfl) ⟨246461, by rfl⟩ : syracuseStep 1314461 = 492923) (by norm_num)
theorem B1969829 : Blo 872567 1969829 := bbase (se 4 (by rfl) ⟨184671, by rfl⟩ : syracuseStep 1969829 = 369343) (by norm_num)
theorem B1478317 : Blo 872567 1478317 := bbase (se 3 (by rfl) ⟨277184, by rfl⟩ : syracuseStep 1478317 = 554369) (by norm_num)
theorem B1314485 : Blo 872567 1314485 := bbase (se 5 (by rfl) ⟨61616, by rfl⟩ : syracuseStep 1314485 = 123233) (by norm_num)
theorem B1314509 : Blo 872567 1314509 := bbase (se 3 (by rfl) ⟨246470, by rfl⟩ : syracuseStep 1314509 = 492941) (by norm_num)
theorem B1314533 : Blo 872567 1314533 := bbase (se 4 (by rfl) ⟨123237, by rfl⟩ : syracuseStep 1314533 = 246475) (by norm_num)
theorem B1969901 : Blo 872567 1969901 := bbase (se 3 (by rfl) ⟨369356, by rfl⟩ : syracuseStep 1969901 = 738713) (by norm_num)
theorem B1314557 : Blo 872567 1314557 := bbase (se 3 (by rfl) ⟨246479, by rfl⟩ : syracuseStep 1314557 = 492959) (by norm_num)
theorem B1478405 : Blo 872567 1478405 := bbase (se 4 (by rfl) ⟨138600, by rfl⟩ : syracuseStep 1478405 = 277201) (by norm_num)
theorem B1314581 : Blo 872567 1314581 := bbase (se 6 (by rfl) ⟨30810, by rfl⟩ : syracuseStep 1314581 = 61621) (by norm_num)
theorem B1314605 : Blo 872567 1314605 := bbase (se 3 (by rfl) ⟨246488, by rfl⟩ : syracuseStep 1314605 = 492977) (by norm_num)
theorem B1969973 : Blo 872567 1969973 := bbase (se 5 (by rfl) ⟨92342, by rfl⟩ : syracuseStep 1969973 = 184685) (by norm_num)
theorem B1314629 : Blo 872567 1314629 := bbase (se 4 (by rfl) ⟨123246, by rfl⟩ : syracuseStep 1314629 = 246493) (by norm_num)
theorem B2101085 : Blo 872567 2101085 := bbase (se 3 (by rfl) ⟨393953, by rfl⟩ : syracuseStep 2101085 = 787907) (by norm_num)
theorem B1314653 : Blo 872567 1314653 := bbase (se 3 (by rfl) ⟨246497, by rfl⟩ : syracuseStep 1314653 = 492995) (by norm_num)
theorem B4427621 : Blo 872567 4427621 := bbase (se 4 (by rfl) ⟨415089, by rfl⟩ : syracuseStep 4427621 = 830179) (by norm_num)
theorem B1314677 : Blo 872567 1314677 := bbase (se 5 (by rfl) ⟨61625, by rfl⟩ : syracuseStep 1314677 = 123251) (by norm_num)
theorem B1970045 : Blo 872567 1970045 := bbase (se 3 (by rfl) ⟨369383, by rfl⟩ : syracuseStep 1970045 = 738767) (by norm_num)
theorem B2527109 : Blo 872567 2527109 := bbase (se 4 (by rfl) ⟨236916, by rfl⟩ : syracuseStep 2527109 = 473833) (by norm_num)
theorem B1478533 : Blo 872567 1478533 := bbase (se 4 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 1478533 = 277225) (by norm_num)
theorem B1314701 : Blo 872567 1314701 := bbase (se 3 (by rfl) ⟨246506, by rfl⟩ : syracuseStep 1314701 = 493013) (by norm_num)
theorem B1871765 : Blo 872567 1871765 := bbase (se 6 (by rfl) ⟨43869, by rfl⟩ : syracuseStep 1871765 = 87739) (by norm_num)
theorem B1314725 : Blo 872567 1314725 := bbase (se 4 (by rfl) ⟨123255, by rfl⟩ : syracuseStep 1314725 = 246511) (by norm_num)
theorem B1314749 : Blo 872567 1314749 := bbase (se 3 (by rfl) ⟨246515, by rfl⟩ : syracuseStep 1314749 = 493031) (by norm_num)
theorem B1970117 : Blo 872567 1970117 := bbase (se 4 (by rfl) ⟨184698, by rfl⟩ : syracuseStep 1970117 = 369397) (by norm_num)
theorem B1314773 : Blo 872567 1314773 := bbase (se 7 (by rfl) ⟨15407, by rfl⟩ : syracuseStep 1314773 = 30815) (by norm_num)
theorem B1478621 : Blo 872567 1478621 := bbase (se 3 (by rfl) ⟨277241, by rfl⟩ : syracuseStep 1478621 = 554483) (by norm_num)
theorem B2101229 : Blo 872567 2101229 := bbase (se 3 (by rfl) ⟨393980, by rfl⟩ : syracuseStep 2101229 = 787961) (by norm_num)
theorem B1314797 : Blo 872567 1314797 := bbase (se 3 (by rfl) ⟨246524, by rfl⟩ : syracuseStep 1314797 = 493049) (by norm_num)
theorem B2953205 : Blo 872567 2953205 := bbase (se 5 (by rfl) ⟨138431, by rfl⟩ : syracuseStep 2953205 = 276863) (by norm_num)
theorem B3313669 : Blo 872567 3313669 := bbase (se 4 (by rfl) ⟨310656, by rfl⟩ : syracuseStep 3313669 = 621313) (by norm_num)
theorem B1314821 : Blo 872567 1314821 := bbase (se 4 (by rfl) ⟨123264, by rfl⟩ : syracuseStep 1314821 = 246529) (by norm_num)
theorem B1970189 : Blo 872567 1970189 := bbase (se 3 (by rfl) ⟨369410, by rfl⟩ : syracuseStep 1970189 = 738821) (by norm_num)
theorem B1871885 : Blo 872567 1871885 := bbase (se 3 (by rfl) ⟨350978, by rfl⟩ : syracuseStep 1871885 = 701957) (by norm_num)
theorem B2101277 : Blo 872567 2101277 := bbase (se 3 (by rfl) ⟨393989, by rfl⟩ : syracuseStep 2101277 = 787979) (by norm_num)
theorem B1314845 : Blo 872567 1314845 := bbase (se 3 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 1314845 = 493067) (by norm_num)
theorem B1970261 : Blo 872567 1970261 := bbase (se 8 (by rfl) ⟨11544, by rfl⟩ : syracuseStep 1970261 = 23089) (by norm_num)
theorem B1478749 : Blo 872567 1478749 := bbase (se 3 (by rfl) ⟨277265, by rfl⟩ : syracuseStep 1478749 = 554531) (by norm_num)
theorem B4198517 : Blo 872567 4198517 := bbase (se 5 (by rfl) ⟨196805, by rfl⟩ : syracuseStep 4198517 = 393611) (by norm_num)
theorem B1970333 : Blo 872567 1970333 := bbase (se 3 (by rfl) ⟨369437, by rfl⟩ : syracuseStep 1970333 = 738875) (by norm_num)
theorem B5607605 : Blo 872567 5607605 := bbase (se 5 (by rfl) ⟨262856, by rfl⟩ : syracuseStep 5607605 = 525713) (by norm_num)
theorem B1478837 : Blo 872567 1478837 := bbase (se 5 (by rfl) ⟨69320, by rfl⟩ : syracuseStep 1478837 = 138641) (by norm_num)
theorem B8523989 : Blo 872567 8523989 := bbase (se 7 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 8523989 = 199781) (by norm_num)
theorem B1970405 : Blo 872567 1970405 := bbase (se 4 (by rfl) ⟨184725, by rfl⟩ : syracuseStep 1970405 = 369451) (by norm_num)
theorem B1970477 : Blo 872567 1970477 := bbase (se 3 (by rfl) ⟨369464, by rfl⟩ : syracuseStep 1970477 = 738929) (by norm_num)
theorem B3313973 : Blo 872567 3313973 := bbase (se 5 (by rfl) ⟨155342, by rfl⟩ : syracuseStep 3313973 = 310685) (by norm_num)
theorem B1478965 : Blo 872567 1478965 := bbase (se 5 (by rfl) ⟨69326, by rfl⟩ : syracuseStep 1478965 = 138653) (by norm_num)
theorem B2101565 : Blo 872567 2101565 := bbase (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) (by norm_num)
theorem B1347925 : Blo 872567 1347925 := bbase (se 10 (by rfl) ⟨1974, by rfl⟩ : syracuseStep 1347925 = 3949) (by norm_num)
theorem B1053037 : Blo 872567 1053037 := bbase (se 3 (by rfl) ⟨197444, by rfl⟩ : syracuseStep 1053037 = 394889) (by norm_num)
theorem B1970549 : Blo 872567 1970549 := bbase (se 5 (by rfl) ⟨92369, by rfl⟩ : syracuseStep 1970549 = 184739) (by norm_num)
theorem B1479053 : Blo 872567 1479053 := bbase (se 3 (by rfl) ⟨277322, by rfl⟩ : syracuseStep 1479053 = 554645) (by norm_num)
theorem B2953637 : Blo 872567 2953637 := bbase (se 4 (by rfl) ⟨276903, by rfl⟩ : syracuseStep 2953637 = 553807) (by norm_num)
theorem B2494901 : Blo 872567 2494901 := bbase (se 5 (by rfl) ⟨116948, by rfl⟩ : syracuseStep 2494901 = 233897) (by norm_num)
theorem B1970621 : Blo 872567 1970621 := bbase (se 3 (by rfl) ⟨369491, by rfl⟩ : syracuseStep 1970621 = 738983) (by norm_num)
theorem B3740165 : Blo 872567 3740165 := bbase (se 4 (by rfl) ⟨350640, by rfl⟩ : syracuseStep 3740165 = 701281) (by norm_num)
theorem B1970693 : Blo 872567 1970693 := bbase (se 4 (by rfl) ⟨184752, by rfl⟩ : syracuseStep 1970693 = 369505) (by norm_num)
theorem B1577485 : Blo 872567 1577485 := bbase (se 3 (by rfl) ⟨295778, by rfl⟩ : syracuseStep 1577485 = 591557) (by norm_num)
theorem B1479181 : Blo 872567 1479181 := bbase (se 3 (by rfl) ⟨277346, by rfl⟩ : syracuseStep 1479181 = 554693) (by norm_num)
theorem B1970765 : Blo 872567 1970765 := bbase (se 3 (by rfl) ⟨369518, by rfl⟩ : syracuseStep 1970765 = 739037) (by norm_num)
theorem B1970837 : Blo 872567 1970837 := bbase (se 6 (by rfl) ⟨46191, by rfl⟩ : syracuseStep 1970837 = 92383) (by norm_num)
theorem B1970909 : Blo 872567 1970909 := bbase (se 3 (by rfl) ⟨369545, by rfl⟩ : syracuseStep 1970909 = 739091) (by norm_num)
theorem B1970981 : Blo 872567 1970981 := bbase (se 4 (by rfl) ⟨184779, by rfl⟩ : syracuseStep 1970981 = 369559) (by norm_num)
theorem B2954069 : Blo 872567 2954069 := bbase (se 9 (by rfl) ⟨8654, by rfl⟩ : syracuseStep 2954069 = 17309) (by norm_num)
theorem B1971053 : Blo 872567 1971053 := bbase (se 3 (by rfl) ⟨369572, by rfl⟩ : syracuseStep 1971053 = 739145) (by norm_num)
theorem B1774477 : Blo 872567 1774477 := bbase (se 3 (by rfl) ⟨332714, by rfl⟩ : syracuseStep 1774477 = 665429) (by norm_num)
theorem B1971125 : Blo 872567 1971125 := bbase (se 5 (by rfl) ⟨92396, by rfl⟩ : syracuseStep 1971125 = 184793) (by norm_num)
theorem B4985813 : Blo 872567 4985813 := bbase (se 7 (by rfl) ⟨58427, by rfl⟩ : syracuseStep 4985813 = 116855) (by norm_num)
theorem B1971197 : Blo 872567 1971197 := bbase (se 3 (by rfl) ⟨369599, by rfl⟩ : syracuseStep 1971197 = 739199) (by norm_num)
theorem B1971269 : Blo 872567 1971269 := bbase (se 4 (by rfl) ⟨184806, by rfl⟩ : syracuseStep 1971269 = 369613) (by norm_num)
theorem B2495573 : Blo 872567 2495573 := bbase (se 8 (by rfl) ⟨14622, by rfl⟩ : syracuseStep 2495573 = 29245) (by norm_num)
theorem B4428917 : Blo 872567 4428917 := bbase (se 5 (by rfl) ⟨207605, by rfl⟩ : syracuseStep 4428917 = 415211) (by norm_num)
theorem B1971341 : Blo 872567 1971341 := bbase (se 3 (by rfl) ⟨369626, by rfl⟩ : syracuseStep 1971341 = 739253) (by norm_num)
theorem B1971413 : Blo 872567 1971413 := bbase (se 7 (by rfl) ⟨23102, by rfl⟩ : syracuseStep 1971413 = 46205) (by norm_num)
theorem B2954501 : Blo 872567 2954501 := bbase (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) (by norm_num)
theorem B1119505 : Blo 872567 1119505 := bbase (se 2 (by rfl) ⟨419814, by rfl⟩ : syracuseStep 1119505 = 839629) (by norm_num)
theorem B1971485 : Blo 872567 1971485 := bbase (se 3 (by rfl) ⟨369653, by rfl⟩ : syracuseStep 1971485 = 739307) (by norm_num)
theorem B7476533 : Blo 872567 7476533 := bbase (se 5 (by rfl) ⟨350462, by rfl⟩ : syracuseStep 7476533 = 700925) (by norm_num)
theorem B1578293 : Blo 872567 1578293 := bbase (se 5 (by rfl) ⟨73982, by rfl⟩ : syracuseStep 1578293 = 147965) (by norm_num)
theorem B1971557 : Blo 872567 1971557 := bbase (se 4 (by rfl) ⟨184833, by rfl⟩ : syracuseStep 1971557 = 369667) (by norm_num)
theorem B1971629 : Blo 872567 1971629 := bbase (se 3 (by rfl) ⟨369680, by rfl⟩ : syracuseStep 1971629 = 739361) (by norm_num)
theorem B3741173 : Blo 872567 3741173 := bbase (se 5 (by rfl) ⟨175367, by rfl⟩ : syracuseStep 3741173 = 350735) (by norm_num)
theorem B1971701 : Blo 872567 1971701 := bbase (se 5 (by rfl) ⟨92423, by rfl⟩ : syracuseStep 1971701 = 184847) (by norm_num)
theorem B2496005 : Blo 872567 2496005 := bbase (se 4 (by rfl) ⟨234000, by rfl⟩ : syracuseStep 2496005 = 468001) (by norm_num)
theorem B1971773 : Blo 872567 1971773 := bbase (se 3 (by rfl) ⟨369707, by rfl⟩ : syracuseStep 1971773 = 739415) (by norm_num)
theorem B1971845 : Blo 872567 1971845 := bbase (se 4 (by rfl) ⟨184860, by rfl⟩ : syracuseStep 1971845 = 369721) (by norm_num)
theorem B2954933 : Blo 872567 2954933 := bbase (se 5 (by rfl) ⟨138512, by rfl⟩ : syracuseStep 2954933 = 277025) (by norm_num)
theorem B1971917 : Blo 872567 1971917 := bbase (se 3 (by rfl) ⟨369734, by rfl⟩ : syracuseStep 1971917 = 739469) (by norm_num)
theorem B1349357 : Blo 872567 1349357 := bbase (se 3 (by rfl) ⟨253004, by rfl⟩ : syracuseStep 1349357 = 506009) (by norm_num)
theorem B1971989 : Blo 872567 1971989 := bbase (se 6 (by rfl) ⟨46218, by rfl⟩ : syracuseStep 1971989 = 92437) (by norm_num)
theorem B1972061 : Blo 872567 1972061 := bbase (se 3 (by rfl) ⟨369761, by rfl⟩ : syracuseStep 1972061 = 739523) (by norm_num)
theorem B1972133 : Blo 872567 1972133 := bbase (se 4 (by rfl) ⟨184887, by rfl⟩ : syracuseStep 1972133 = 369775) (by norm_num)
theorem B1972205 : Blo 872567 1972205 := bbase (se 3 (by rfl) ⟨369788, by rfl⟩ : syracuseStep 1972205 = 739577) (by norm_num)
theorem B3545093 : Blo 872567 3545093 := bbase (se 4 (by rfl) ⟨332352, by rfl⟩ : syracuseStep 3545093 = 664705) (by norm_num)
theorem B1972277 : Blo 872567 1972277 := bbase (se 5 (by rfl) ⟨92450, by rfl⟩ : syracuseStep 1972277 = 184901) (by norm_num)
theorem B3151973 : Blo 872567 3151973 := bbase (se 4 (by rfl) ⟨295497, by rfl⟩ : syracuseStep 3151973 = 590995) (by norm_num)
theorem B2955365 : Blo 872567 2955365 := bbase (se 4 (by rfl) ⟨277065, by rfl⟩ : syracuseStep 2955365 = 554131) (by norm_num)
theorem B3152117 : Blo 872567 3152117 := bbase (se 5 (by rfl) ⟨147755, by rfl⟩ : syracuseStep 3152117 = 295511) (by norm_num)
theorem B3316085 : Blo 872567 3316085 := bbase (se 5 (by rfl) ⟨155441, by rfl⟩ : syracuseStep 3316085 = 310883) (by norm_num)
theorem B4430213 : Blo 872567 4430213 := bbase (se 4 (by rfl) ⟨415332, by rfl⟩ : syracuseStep 4430213 = 830665) (by norm_num)
theorem B2955797 : Blo 872567 2955797 := bbase (se 6 (by rfl) ⟨69276, by rfl⟩ : syracuseStep 2955797 = 138553) (by norm_num)
theorem B1776181 : Blo 872567 1776181 := bbase (se 5 (by rfl) ⟨83258, by rfl⟩ : syracuseStep 1776181 = 166517) (by norm_num)
theorem B3316373 : Blo 872567 3316373 := bbase (se 6 (by rfl) ⟨77727, by rfl⟩ : syracuseStep 3316373 = 155455) (by norm_num)
theorem B2103997 : Blo 872567 2103997 := bbase (se 3 (by rfl) ⟨394499, by rfl⟩ : syracuseStep 2103997 = 788999) (by norm_num)
theorem B2956229 : Blo 872567 2956229 := bbase (se 4 (by rfl) ⟨277146, by rfl⟩ : syracuseStep 2956229 = 554293) (by norm_num)
theorem B3742949 : Blo 872567 3742949 := bbase (se 4 (by rfl) ⟨350901, by rfl⟩ : syracuseStep 3742949 = 701803) (by norm_num)
theorem B2104613 : Blo 872567 2104613 := bbase (se 4 (by rfl) ⟨197307, by rfl⟩ : syracuseStep 2104613 = 394615) (by norm_num)
theorem B1121593 : Blo 872567 1121593 := bbase (se 2 (by rfl) ⟨420597, by rfl⟩ : syracuseStep 1121593 = 841195) (by norm_num)
theorem B2956661 : Blo 872567 2956661 := bbase (se 5 (by rfl) ⟨138593, by rfl⟩ : syracuseStep 2956661 = 277187) (by norm_num)
theorem B2104813 : Blo 872567 2104813 := bbase (se 3 (by rfl) ⟨394652, by rfl⟩ : syracuseStep 2104813 = 789305) (by norm_num)
theorem B2367029 : Blo 872567 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B4431509 : Blo 872567 4431509 := bbase (se 6 (by rfl) ⟨103863, by rfl⟩ : syracuseStep 4431509 = 207727) (by norm_num)
theorem B2989781 : Blo 872567 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B2957093 : Blo 872567 2957093 := bbase (se 4 (by rfl) ⟨277227, by rfl⟩ : syracuseStep 2957093 = 554455) (by norm_num)
theorem B3317557 : Blo 872567 3317557 := bbase (se 5 (by rfl) ⟨155510, by rfl⟩ : syracuseStep 3317557 = 311021) (by norm_num)
theorem B1122193 : Blo 872567 1122193 := bbase (se 2 (by rfl) ⟨420822, by rfl⟩ : syracuseStep 1122193 = 841645) (by norm_num)
theorem B2367397 : Blo 872567 2367397 := bbase (se 4 (by rfl) ⟨221943, by rfl⟩ : syracuseStep 2367397 = 443887) (by norm_num)
theorem B5611477 : Blo 872567 5611477 := bbase (se 7 (by rfl) ⟨65759, by rfl⟩ : syracuseStep 5611477 = 131519) (by norm_num)
theorem B3317861 : Blo 872567 3317861 := bbase (se 4 (by rfl) ⟨311049, by rfl⟩ : syracuseStep 3317861 = 622099) (by norm_num)
theorem B2957525 : Blo 872567 2957525 := bbase (se 7 (by rfl) ⟨34658, by rfl⟩ : syracuseStep 2957525 = 69317) (by norm_num)
theorem B2105621 : Blo 872567 2105621 := bbase (se 6 (by rfl) ⟨49350, by rfl⟩ : syracuseStep 2105621 = 98701) (by norm_num)
theorem B958777 : Blo 872567 958777 := bbase (se 2 (by rfl) ⟨359541, by rfl⟩ : syracuseStep 958777 = 719083) (by norm_num)
theorem B3547525 : Blo 872567 3547525 := bbase (se 4 (by rfl) ⟨332580, by rfl⟩ : syracuseStep 3547525 = 665161) (by norm_num)
theorem B2957957 : Blo 872567 2957957 := bbase (se 4 (by rfl) ⟨277308, by rfl⟩ : syracuseStep 2957957 = 554617) (by norm_num)
theorem B1680173 : Blo 872567 1680173 := bbase (se 3 (by rfl) ⟨315032, by rfl⟩ : syracuseStep 1680173 = 630065) (by norm_num)
theorem B4432805 : Blo 872567 4432805 := bbase (se 4 (by rfl) ⟨415575, by rfl⟩ : syracuseStep 4432805 = 831151) (by norm_num)
theorem B1680365 : Blo 872567 1680365 := bbase (se 3 (by rfl) ⟨315068, by rfl⟩ : syracuseStep 1680365 = 630137) (by norm_num)
theorem B2958389 : Blo 872567 2958389 := bbase (se 5 (by rfl) ⟨138674, by rfl⟩ : syracuseStep 2958389 = 277349) (by norm_num)
theorem B2368901 : Blo 872567 2368901 := bbase (se 4 (by rfl) ⟨222084, by rfl⟩ : syracuseStep 2368901 = 444169) (by norm_num)
theorem B1123733 : Blo 872567 1123733 := bbase (se 6 (by rfl) ⟨26337, by rfl⟩ : syracuseStep 1123733 = 52675) (by norm_num)
theorem B2368997 : Blo 872567 2368997 := bbase (se 4 (by rfl) ⟨222093, by rfl⟩ : syracuseStep 2368997 = 444187) (by norm_num)
theorem B1124057 : Blo 872567 1124057 := bbase (se 2 (by rfl) ⟨421521, by rfl⟩ : syracuseStep 1124057 = 843043) (by norm_num)
theorem B1419005 : Blo 872567 1419005 := bbase (se 3 (by rfl) ⟨266063, by rfl⟩ : syracuseStep 1419005 = 532127) (by norm_num)
theorem B1681165 : Blo 872567 1681165 := bbase (se 3 (by rfl) ⟨315218, by rfl⟩ : syracuseStep 1681165 = 630437) (by norm_num)
theorem B1124221 : Blo 872567 1124221 := bbase (se 3 (by rfl) ⟨210791, by rfl⟩ : syracuseStep 1124221 = 421583) (by norm_num)
theorem B6629525 : Blo 872567 6629525 := bbase (se 6 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 6629525 = 310759) (by norm_num)
theorem B3319973 : Blo 872567 3319973 := bbase (se 4 (by rfl) ⟨311247, by rfl⟩ : syracuseStep 3319973 = 622495) (by norm_num)
theorem B4434101 : Blo 872567 4434101 := bbase (se 5 (by rfl) ⟨207848, by rfl⟩ : syracuseStep 4434101 = 415697) (by norm_num)
theorem B3320261 : Blo 872567 3320261 := bbase (se 4 (by rfl) ⟨311274, by rfl⟩ : syracuseStep 3320261 = 622549) (by norm_num)
theorem B2238925 : Blo 872567 2238925 := bbase (se 3 (by rfl) ⟨419798, by rfl⟩ : syracuseStep 2238925 = 839597) (by norm_num)
theorem B11217365 : Blo 872567 11217365 := bbase (se 7 (by rfl) ⟨131453, by rfl⟩ : syracuseStep 11217365 = 262907) (by norm_num)
theorem B5974517 : Blo 872567 5974517 := bbase (se 5 (by rfl) ⟨280055, by rfl⟩ : syracuseStep 5974517 = 560111) (by norm_num)
theorem B5680277 : Blo 872567 5680277 := bbase (se 6 (by rfl) ⟨133131, by rfl⟩ : syracuseStep 5680277 = 266263) (by norm_num)
theorem B2239829 : Blo 872567 2239829 := bbase (se 11 (by rfl) ⟨1640, by rfl⟩ : syracuseStep 2239829 = 3281) (by norm_num)
theorem B4435397 : Blo 872567 4435397 := bbase (se 4 (by rfl) ⟨415818, by rfl⟩ : syracuseStep 4435397 = 831637) (by norm_num)
theorem B11185685 : Blo 872567 11185685 := bbase (se 6 (by rfl) ⟨262164, by rfl⟩ : syracuseStep 11185685 = 524329) (by norm_num)
theorem B3321445 : Blo 872567 3321445 := bbase (se 4 (by rfl) ⟨311385, by rfl⟩ : syracuseStep 3321445 = 622771) (by norm_num)
theorem B3321749 : Blo 872567 3321749 := bbase (se 6 (by rfl) ⟨77853, by rfl⟩ : syracuseStep 3321749 = 155707) (by norm_num)
theorem B995585 : Blo 872567 995585 := bbase (se 2 (by rfl) ⟨373344, by rfl⟩ : syracuseStep 995585 = 746689) (by norm_num)
theorem B5681621 : Blo 872567 5681621 := bbase (se 7 (by rfl) ⟨66581, by rfl⟩ : syracuseStep 5681621 = 133163) (by norm_num)
theorem B995809 : Blo 872567 995809 := bbase (se 2 (by rfl) ⟨373428, by rfl⟩ : syracuseStep 995809 = 746857) (by norm_num)
theorem B2798165 : Blo 872567 2798165 := bbase (se 8 (by rfl) ⟨16395, by rfl⟩ : syracuseStep 2798165 = 32791) (by norm_num)
theorem B7090901 : Blo 872567 7090901 := bbase (se 7 (by rfl) ⟨83096, by rfl⟩ : syracuseStep 7090901 = 166193) (by norm_num)
theorem B4436693 : Blo 872567 4436693 := bbase (se 7 (by rfl) ⟨51992, by rfl⟩ : syracuseStep 4436693 = 103985) (by norm_num)
theorem B2700101 : Blo 872567 2700101 := bbase (se 4 (by rfl) ⟨253134, by rfl⟩ : syracuseStep 2700101 = 506269) (by norm_num)
theorem B3552133 : Blo 872567 3552133 := bbase (se 4 (by rfl) ⟨333012, by rfl⟩ : syracuseStep 3552133 = 666025) (by norm_num)
theorem B2208829 : Blo 872567 2208829 := bbase (se 3 (by rfl) ⟨414155, by rfl⟩ : syracuseStep 2208829 = 828311) (by norm_num)
theorem B9942101 : Blo 872567 9942101 := bbase (se 8 (by rfl) ⟨58254, by rfl⟩ : syracuseStep 9942101 = 116509) (by norm_num)
theorem B4207781 : Blo 872567 4207781 := bbase (se 4 (by rfl) ⟨394479, by rfl⟩ : syracuseStep 4207781 = 788959) (by norm_num)
theorem B2208941 : Blo 872567 2208941 := bbase (se 3 (by rfl) ⟨414176, by rfl⟩ : syracuseStep 2208941 = 828353) (by norm_num)
theorem B2209133 : Blo 872567 2209133 := bbase (se 3 (by rfl) ⟨414212, by rfl⟩ : syracuseStep 2209133 = 828425) (by norm_num)
theorem B4208165 : Blo 872567 4208165 := bbase (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) (by norm_num)
theorem B2209477 : Blo 872567 2209477 := bbase (se 4 (by rfl) ⟨207138, by rfl⟩ : syracuseStep 2209477 = 414277) (by norm_num)
theorem B1685261 : Blo 872567 1685261 := bbase (se 3 (by rfl) ⟨315986, by rfl⟩ : syracuseStep 1685261 = 631973) (by norm_num)
theorem B2209589 : Blo 872567 2209589 := bbase (se 5 (by rfl) ⟨103574, by rfl⟩ : syracuseStep 2209589 = 207149) (by norm_num)
theorem B3323861 : Blo 872567 3323861 := bbase (se 7 (by rfl) ⟨38951, by rfl⟩ : syracuseStep 3323861 = 77903) (by norm_num)
theorem B931829 : Blo 872567 931829 := bbase (se 5 (by rfl) ⟨43679, by rfl⟩ : syracuseStep 931829 = 87359) (by norm_num)
theorem B2209781 : Blo 872567 2209781 := bbase (se 5 (by rfl) ⟨103583, by rfl⟩ : syracuseStep 2209781 = 207167) (by norm_num)
theorem B3553397 : Blo 872567 3553397 := bbase (se 5 (by rfl) ⟨166565, by rfl⟩ : syracuseStep 3553397 = 333131) (by norm_num)
theorem B3324149 : Blo 872567 3324149 := bbase (se 5 (by rfl) ⟨155819, by rfl⟩ : syracuseStep 3324149 = 311639) (by norm_num)
theorem B2210125 : Blo 872567 2210125 := bbase (se 3 (by rfl) ⟨414398, by rfl⟩ : syracuseStep 2210125 = 828797) (by norm_num)
theorem B1849717 : Blo 872567 1849717 := bbase (se 5 (by rfl) ⟨86705, by rfl⟩ : syracuseStep 1849717 = 173411) (by norm_num)
theorem B2210237 : Blo 872567 2210237 := bbase (se 3 (by rfl) ⟨414419, by rfl⟩ : syracuseStep 2210237 = 828839) (by norm_num)
theorem B1686029 : Blo 872567 1686029 := bbase (se 3 (by rfl) ⟨316130, by rfl⟩ : syracuseStep 1686029 = 632261) (by norm_num)
theorem B1915429 : Blo 872567 1915429 := bbase (se 4 (by rfl) ⟨179571, by rfl⟩ : syracuseStep 1915429 = 359143) (by norm_num)
theorem B2210429 : Blo 872567 2210429 := bbase (se 3 (by rfl) ⟨414455, by rfl⟩ : syracuseStep 2210429 = 828911) (by norm_num)
theorem B932581 : Blo 872567 932581 := bbase (se 4 (by rfl) ⟨87429, by rfl⟩ : syracuseStep 932581 = 174859) (by norm_num)
theorem B932653 : Blo 872567 932653 := bbase (se 3 (by rfl) ⟨174872, by rfl⟩ : syracuseStep 932653 = 349745) (by norm_num)
theorem B7093109 : Blo 872567 7093109 := bbase (se 5 (by rfl) ⟨332489, by rfl⟩ : syracuseStep 7093109 = 664979) (by norm_num)
theorem B2210773 : Blo 872567 2210773 := bbase (se 7 (by rfl) ⟨25907, by rfl⟩ : syracuseStep 2210773 = 51815) (by norm_num)
theorem B932833 : Blo 872567 932833 := bbase (se 2 (by rfl) ⟨349812, by rfl⟩ : syracuseStep 932833 = 699625) (by norm_num)
theorem B2210885 : Blo 872567 2210885 := bbase (se 4 (by rfl) ⟨207270, by rfl⟩ : syracuseStep 2210885 = 414541) (by norm_num)
theorem B1621061 : Blo 872567 1621061 := bbase (se 4 (by rfl) ⟨151974, by rfl⟩ : syracuseStep 1621061 = 303949) (by norm_num)
theorem B11943125 : Blo 872567 11943125 := bbase (se 7 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 11943125 = 279917) (by norm_num)
theorem B2211077 : Blo 872567 2211077 := bbase (se 4 (by rfl) ⟨207288, by rfl⟩ : syracuseStep 2211077 = 414577) (by norm_num)
theorem B3980677 : Blo 872567 3980677 := bbase (se 4 (by rfl) ⟨373188, by rfl⟩ : syracuseStep 3980677 = 746377) (by norm_num)
theorem B3325333 : Blo 872567 3325333 := bbase (se 6 (by rfl) ⟨77937, by rfl⟩ : syracuseStep 3325333 = 155875) (by norm_num)
theorem B933277 : Blo 872567 933277 := bbase (se 3 (by rfl) ⟨174989, by rfl⟩ : syracuseStep 933277 = 349979) (by norm_num)
theorem B4439573 : Blo 872567 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B933401 : Blo 872567 933401 := bbase (se 2 (by rfl) ⟨350025, by rfl⟩ : syracuseStep 933401 = 700051) (by norm_num)
theorem B2211421 : Blo 872567 2211421 := bbase (se 3 (by rfl) ⟨414641, by rfl⟩ : syracuseStep 2211421 = 829283) (by norm_num)
theorem B1064545 : Blo 872567 1064545 := bbase (se 2 (by rfl) ⟨399204, by rfl⟩ : syracuseStep 1064545 = 798409) (by norm_num)
theorem B7454389 : Blo 872567 7454389 := bbase (se 5 (by rfl) ⟨349424, by rfl⟩ : syracuseStep 7454389 = 698849) (by norm_num)
theorem B3325637 : Blo 872567 3325637 := bbase (se 4 (by rfl) ⟨311778, by rfl⟩ : syracuseStep 3325637 = 623557) (by norm_num)
theorem B2211533 : Blo 872567 2211533 := bbase (se 3 (by rfl) ⟨414662, by rfl⟩ : syracuseStep 2211533 = 829325) (by norm_num)
theorem B933653 : Blo 872567 933653 := bbase (se 6 (by rfl) ⟨21882, by rfl⟩ : syracuseStep 933653 = 43765) (by norm_num)
theorem B1326869 : Blo 872567 1326869 := bbase (se 6 (by rfl) ⟨31098, by rfl⟩ : syracuseStep 1326869 = 62197) (by norm_num)
theorem B1326917 : Blo 872567 1326917 := bbase (se 4 (by rfl) ⟨124398, by rfl⟩ : syracuseStep 1326917 = 248797) (by norm_num)
theorem B3030901 : Blo 872567 3030901 := bbase (se 5 (by rfl) ⟨142073, by rfl⟩ : syracuseStep 3030901 = 284147) (by norm_num)
theorem B2211725 : Blo 872567 2211725 := bbase (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) (by norm_num)
theorem B934097 : Blo 872567 934097 := bbase (se 2 (by rfl) ⟨350286, by rfl⟩ : syracuseStep 934097 = 700573) (by norm_num)
theorem B2212069 : Blo 872567 2212069 := bbase (se 4 (by rfl) ⟨207381, by rfl⟩ : syracuseStep 2212069 = 414763) (by norm_num)
theorem B2801957 : Blo 872567 2801957 := bbase (se 4 (by rfl) ⟨262683, by rfl⟩ : syracuseStep 2801957 = 525367) (by norm_num)
theorem B2212181 : Blo 872567 2212181 := bbase (se 10 (by rfl) ⟨3240, by rfl⟩ : syracuseStep 2212181 = 6481) (by norm_num)
theorem B934345 : Blo 872567 934345 := bbase (se 2 (by rfl) ⟨350379, by rfl⟩ : syracuseStep 934345 = 700759) (by norm_num)
theorem B2212373 : Blo 872567 2212373 := bbase (se 6 (by rfl) ⟨51852, by rfl⟩ : syracuseStep 2212373 = 103705) (by norm_num)
theorem B1065793 : Blo 872567 1065793 := bbase (se 2 (by rfl) ⟨399672, by rfl⟩ : syracuseStep 1065793 = 799345) (by norm_num)
theorem B2212717 : Blo 872567 2212717 := bbase (se 3 (by rfl) ⟨414884, by rfl⟩ : syracuseStep 2212717 = 829769) (by norm_num)
theorem B934789 : Blo 872567 934789 := bbase (se 4 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 934789 = 175273) (by norm_num)
theorem B934849 : Blo 872567 934849 := bbase (se 2 (by rfl) ⟨350568, by rfl⟩ : syracuseStep 934849 = 701137) (by norm_num)
theorem B2212829 : Blo 872567 2212829 := bbase (se 3 (by rfl) ⟨414905, by rfl⟩ : syracuseStep 2212829 = 829811) (by norm_num)
theorem B4310117 : Blo 872567 4310117 := bbase (se 4 (by rfl) ⟨404073, by rfl⟩ : syracuseStep 4310117 = 808147) (by norm_num)
theorem B2213021 : Blo 872567 2213021 := bbase (se 3 (by rfl) ⟨414941, by rfl⟩ : syracuseStep 2213021 = 829883) (by norm_num)
theorem B2802869 : Blo 872567 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B1328341 : Blo 872567 1328341 := bbase (se 7 (by rfl) ⟨15566, by rfl⟩ : syracuseStep 1328341 = 31133) (by norm_num)
theorem B27280597 : Blo 872567 27280597 := bbase (se 7 (by rfl) ⟨319694, by rfl⟩ : syracuseStep 27280597 = 639389) (by norm_num)
theorem B1262837 : Blo 872567 1262837 := bbase (se 5 (by rfl) ⟨59195, by rfl⟩ : syracuseStep 1262837 = 118391) (by norm_num)
theorem B935165 : Blo 872567 935165 := bbase (se 3 (by rfl) ⟨175343, by rfl⟩ : syracuseStep 935165 = 350687) (by norm_num)
theorem B2213365 : Blo 872567 2213365 := bbase (se 5 (by rfl) ⟨103751, by rfl⟩ : syracuseStep 2213365 = 207503) (by norm_num)
theorem B2213477 : Blo 872567 2213477 := bbase (se 4 (by rfl) ⟨207513, by rfl⟩ : syracuseStep 2213477 = 415027) (by norm_num)
theorem B7456373 : Blo 872567 7456373 := bbase (se 5 (by rfl) ⟨349517, by rfl⟩ : syracuseStep 7456373 = 699035) (by norm_num)
theorem B1328765 : Blo 872567 1328765 := bbase (se 3 (by rfl) ⟨249143, by rfl⟩ : syracuseStep 1328765 = 498287) (by norm_num)
theorem B935609 : Blo 872567 935609 := bbase (se 2 (by rfl) ⟨350853, by rfl⟩ : syracuseStep 935609 = 701707) (by norm_num)
theorem B2246357 : Blo 872567 2246357 := bbase (se 7 (by rfl) ⟨26324, by rfl⟩ : syracuseStep 2246357 = 52649) (by norm_num)
theorem B6637301 : Blo 872567 6637301 := bbase (se 5 (by rfl) ⟨311123, by rfl⟩ : syracuseStep 6637301 = 622247) (by norm_num)
theorem B935669 : Blo 872567 935669 := bbase (se 5 (by rfl) ⟨43859, by rfl⟩ : syracuseStep 935669 = 87719) (by norm_num)
theorem B3327749 : Blo 872567 3327749 := bbase (se 4 (by rfl) ⟨311976, by rfl⟩ : syracuseStep 3327749 = 623953) (by norm_num)
theorem B2213669 : Blo 872567 2213669 := bbase (se 4 (by rfl) ⟨207531, by rfl⟩ : syracuseStep 2213669 = 415063) (by norm_num)
theorem B15976277 : Blo 872567 15976277 := bbase (se 9 (by rfl) ⟨46805, by rfl⟩ : syracuseStep 15976277 = 93611) (by norm_num)
theorem B935797 : Blo 872567 935797 := bbase (se 5 (by rfl) ⟨43865, by rfl⟩ : syracuseStep 935797 = 87731) (by norm_num)
theorem B3328037 : Blo 872567 3328037 := bbase (se 4 (by rfl) ⟨312003, by rfl⟩ : syracuseStep 3328037 = 624007) (by norm_num)
theorem B2246725 : Blo 872567 2246725 := bbase (se 4 (by rfl) ⟨210630, by rfl⟩ : syracuseStep 2246725 = 421261) (by norm_num)
theorem B1656949 : Blo 872567 1656949 := bbase (se 5 (by rfl) ⟨77669, by rfl⟩ : syracuseStep 1656949 = 155339) (by norm_num)
theorem B2214013 : Blo 872567 2214013 := bbase (se 3 (by rfl) ⟨415127, by rfl⟩ : syracuseStep 2214013 = 830255) (by norm_num)
theorem B2214125 : Blo 872567 2214125 := bbase (se 3 (by rfl) ⟨415148, by rfl⟩ : syracuseStep 2214125 = 830297) (by norm_num)
theorem B1657093 : Blo 872567 1657093 := bbase (se 4 (by rfl) ⟨155352, by rfl⟩ : syracuseStep 1657093 = 310705) (by norm_num)
theorem B1329509 : Blo 872567 1329509 := bbase (se 4 (by rfl) ⟨124641, by rfl⟩ : syracuseStep 1329509 = 249283) (by norm_num)
theorem B2247053 : Blo 872567 2247053 := bbase (se 3 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 2247053 = 842645) (by norm_num)
theorem B1657253 : Blo 872567 1657253 := bbase (se 4 (by rfl) ⟨155367, by rfl⟩ : syracuseStep 1657253 = 310735) (by norm_num)
theorem B2214317 : Blo 872567 2214317 := bbase (se 3 (by rfl) ⟨415184, by rfl⟩ : syracuseStep 2214317 = 830369) (by norm_num)
theorem B1329637 : Blo 872567 1329637 := bbase (se 4 (by rfl) ⟨124653, by rfl⟩ : syracuseStep 1329637 = 249307) (by norm_num)
theorem B2804213 : Blo 872567 2804213 := bbase (se 5 (by rfl) ⟨131447, by rfl⟩ : syracuseStep 2804213 = 262895) (by norm_num)
theorem B1657397 : Blo 872567 1657397 := bbase (se 5 (by rfl) ⟨77690, by rfl⟩ : syracuseStep 1657397 = 155381) (by norm_num)
theorem B2214661 : Blo 872567 2214661 := bbase (se 4 (by rfl) ⟨207624, by rfl⟩ : syracuseStep 2214661 = 415249) (by norm_num)
theorem B1657685 : Blo 872567 1657685 := bbase (se 9 (by rfl) ⟨4856, by rfl⟩ : syracuseStep 1657685 = 9713) (by norm_num)
theorem B2214773 : Blo 872567 2214773 := bbase (se 5 (by rfl) ⟨103817, by rfl⟩ : syracuseStep 2214773 = 207635) (by norm_num)
theorem B15944597 : Blo 872567 15944597 := bbase (se 6 (by rfl) ⟨373701, by rfl⟩ : syracuseStep 15944597 = 747403) (by norm_num)
theorem B1657837 : Blo 872567 1657837 := bbase (se 3 (by rfl) ⟨310844, by rfl⟩ : syracuseStep 1657837 = 621689) (by norm_num)
theorem B2214965 : Blo 872567 2214965 := bbase (se 5 (by rfl) ⟨103826, by rfl⟩ : syracuseStep 2214965 = 207653) (by norm_num)
theorem B1658141 : Blo 872567 1658141 := bbase (se 3 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 1658141 = 621803) (by norm_num)
theorem B2215309 : Blo 872567 2215309 := bbase (se 3 (by rfl) ⟨415370, by rfl⟩ : syracuseStep 2215309 = 830741) (by norm_num)
theorem B2215421 : Blo 872567 2215421 := bbase (se 3 (by rfl) ⟨415391, by rfl⟩ : syracuseStep 2215421 = 830783) (by norm_num)
theorem B1330805 : Blo 872567 1330805 := bbase (se 5 (by rfl) ⟨62381, by rfl⟩ : syracuseStep 1330805 = 124763) (by norm_num)
theorem B2215613 : Blo 872567 2215613 := bbase (se 3 (by rfl) ⟨415427, by rfl⟩ : syracuseStep 2215613 = 830855) (by norm_num)
theorem B2805637 : Blo 872567 2805637 := bbase (se 4 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 2805637 = 526057) (by norm_num)
theorem B1331101 : Blo 872567 1331101 := bbase (se 3 (by rfl) ⟨249581, by rfl⟩ : syracuseStep 1331101 = 499163) (by norm_num)
theorem B1658893 : Blo 872567 1658893 := bbase (se 3 (by rfl) ⟨311042, by rfl⟩ : syracuseStep 1658893 = 622085) (by norm_num)
theorem B2215957 : Blo 872567 2215957 := bbase (se 6 (by rfl) ⟨51936, by rfl⟩ : syracuseStep 2215957 = 103873) (by norm_num)
theorem B2216069 : Blo 872567 2216069 := bbase (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) (by norm_num)
theorem B1659037 : Blo 872567 1659037 := bbase (se 3 (by rfl) ⟨311069, by rfl⟩ : syracuseStep 1659037 = 622139) (by norm_num)
theorem B1659197 : Blo 872567 1659197 := bbase (se 3 (by rfl) ⟨311099, by rfl⟩ : syracuseStep 1659197 = 622199) (by norm_num)
theorem B2216261 : Blo 872567 2216261 := bbase (se 4 (by rfl) ⟨207774, by rfl⟩ : syracuseStep 2216261 = 415549) (by norm_num)
theorem B1659341 : Blo 872567 1659341 := bbase (se 3 (by rfl) ⟨311126, by rfl⟩ : syracuseStep 1659341 = 622253) (by norm_num)
theorem B3986005 : Blo 872567 3986005 := bbase (se 8 (by rfl) ⟨23355, by rfl⟩ : syracuseStep 3986005 = 46711) (by norm_num)
theorem B2216605 : Blo 872567 2216605 := bbase (se 3 (by rfl) ⟨415613, by rfl⟩ : syracuseStep 2216605 = 831227) (by norm_num)
theorem B1594093 : Blo 872567 1594093 := bbase (se 3 (by rfl) ⟨298892, by rfl⟩ : syracuseStep 1594093 = 597785) (by norm_num)
theorem B1659629 : Blo 872567 1659629 := bbase (se 3 (by rfl) ⟨311180, by rfl⟩ : syracuseStep 1659629 = 622361) (by norm_num)
theorem B2216717 : Blo 872567 2216717 := bbase (se 3 (by rfl) ⟨415634, by rfl⟩ : syracuseStep 2216717 = 831269) (by norm_num)
theorem B8967029 : Blo 872567 8967029 := bbase (se 5 (by rfl) ⟨420329, by rfl⟩ : syracuseStep 8967029 = 840659) (by norm_num)
theorem B1659781 : Blo 872567 1659781 := bbase (se 4 (by rfl) ⟨155604, by rfl⟩ : syracuseStep 1659781 = 311209) (by norm_num)
theorem B2216909 : Blo 872567 2216909 := bbase (se 3 (by rfl) ⟨415670, by rfl⟩ : syracuseStep 2216909 = 831341) (by norm_num)
theorem B1332269 : Blo 872567 1332269 := bbase (se 3 (by rfl) ⟨249800, by rfl⟩ : syracuseStep 1332269 = 499601) (by norm_num)
theorem B1660085 : Blo 872567 1660085 := bbase (se 5 (by rfl) ⟨77816, by rfl⟩ : syracuseStep 1660085 = 155633) (by norm_num)
theorem B1397981 : Blo 872567 1397981 := bbase (se 3 (by rfl) ⟨262121, by rfl⟩ : syracuseStep 1397981 = 524243) (by norm_num)
theorem B2217253 : Blo 872567 2217253 := bbase (se 4 (by rfl) ⟨207867, by rfl⟩ : syracuseStep 2217253 = 415735) (by norm_num)
theorem B2217365 : Blo 872567 2217365 := bbase (se 6 (by rfl) ⟨51969, by rfl⟩ : syracuseStep 2217365 = 103939) (by norm_num)
theorem B2807237 : Blo 872567 2807237 := bbase (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) (by norm_num)
theorem B2217557 : Blo 872567 2217557 := bbase (se 8 (by rfl) ⟨12993, by rfl⟩ : syracuseStep 2217557 = 25987) (by norm_num)
theorem B1398365 : Blo 872567 1398365 := bbase (se 3 (by rfl) ⟨262193, by rfl⟩ : syracuseStep 1398365 = 524387) (by norm_num)
theorem B1398493 : Blo 872567 1398493 := bbase (se 3 (by rfl) ⟨262217, by rfl⟩ : syracuseStep 1398493 = 524435) (by norm_num)
theorem B3987317 : Blo 872567 3987317 := bbase (se 5 (by rfl) ⟨186905, by rfl⟩ : syracuseStep 3987317 = 373811) (by norm_num)
theorem B1660837 : Blo 872567 1660837 := bbase (se 4 (by rfl) ⟨155703, by rfl⟩ : syracuseStep 1660837 = 311407) (by norm_num)
theorem B2217901 : Blo 872567 2217901 := bbase (se 3 (by rfl) ⟨415856, by rfl⟩ : syracuseStep 2217901 = 831713) (by norm_num)
theorem B22763477 : Blo 872567 22763477 := bbase (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) (by norm_num)
theorem B2218013 : Blo 872567 2218013 := bbase (se 3 (by rfl) ⟨415877, by rfl⟩ : syracuseStep 2218013 = 831755) (by norm_num)
theorem B1660981 : Blo 872567 1660981 := bbase (se 5 (by rfl) ⟨77858, by rfl⟩ : syracuseStep 1660981 = 155717) (by norm_num)
theorem B1661141 : Blo 872567 1661141 := bbase (se 7 (by rfl) ⟨19466, by rfl⟩ : syracuseStep 1661141 = 38933) (by norm_num)
theorem B2218205 : Blo 872567 2218205 := bbase (se 3 (by rfl) ⟨415913, by rfl⟩ : syracuseStep 2218205 = 831827) (by norm_num)
theorem B1661285 : Blo 872567 1661285 := bbase (se 4 (by rfl) ⟨155745, by rfl⟩ : syracuseStep 1661285 = 311491) (by norm_num)
theorem B1104349 : Blo 872567 1104349 := bbase (se 3 (by rfl) ⟨207065, by rfl⟩ : syracuseStep 1104349 = 414131) (by norm_num)
theorem B2218549 : Blo 872567 2218549 := bbase (se 5 (by rfl) ⟨103994, by rfl⟩ : syracuseStep 2218549 = 207989) (by norm_num)
theorem B1104445 : Blo 872567 1104445 := bbase (se 3 (by rfl) ⟨207083, by rfl⟩ : syracuseStep 1104445 = 414167) (by norm_num)
theorem B1661573 : Blo 872567 1661573 := bbase (se 4 (by rfl) ⟨155772, by rfl⟩ : syracuseStep 1661573 = 311545) (by norm_num)
theorem B2218661 : Blo 872567 2218661 := bbase (se 4 (by rfl) ⟨207999, by rfl⟩ : syracuseStep 2218661 = 415999) (by norm_num)
theorem B1399493 : Blo 872567 1399493 := bbase (se 4 (by rfl) ⟨131202, by rfl⟩ : syracuseStep 1399493 = 262405) (by norm_num)
theorem B1104617 : Blo 872567 1104617 := bbase (se 2 (by rfl) ⟨414231, by rfl⟩ : syracuseStep 1104617 = 828463) (by norm_num)
theorem B1661725 : Blo 872567 1661725 := bbase (se 3 (by rfl) ⟨311573, by rfl⟩ : syracuseStep 1661725 = 623147) (by norm_num)
theorem B1104673 : Blo 872567 1104673 := bbase (se 2 (by rfl) ⟨414252, by rfl⟩ : syracuseStep 1104673 = 828505) (by norm_num)
theorem B1399621 : Blo 872567 1399621 := bbase (se 4 (by rfl) ⟨131214, by rfl⟩ : syracuseStep 1399621 = 262429) (by norm_num)
theorem B1104769 : Blo 872567 1104769 := bbase (se 2 (by rfl) ⟨414288, by rfl⟩ : syracuseStep 1104769 = 828577) (by norm_num)
theorem B3234725 : Blo 872567 3234725 := bbase (se 4 (by rfl) ⟨303255, by rfl⟩ : syracuseStep 3234725 = 606511) (by norm_num)
theorem B9460757 : Blo 872567 9460757 := bbase (se 6 (by rfl) ⟨221736, by rfl⟩ : syracuseStep 9460757 = 443473) (by norm_num)
theorem B1104941 : Blo 872567 1104941 := bbase (se 3 (by rfl) ⟨207176, by rfl⟩ : syracuseStep 1104941 = 414353) (by norm_num)
theorem B1662029 : Blo 872567 1662029 := bbase (se 3 (by rfl) ⟨311630, by rfl⟩ : syracuseStep 1662029 = 623261) (by norm_num)
theorem B1104997 : Blo 872567 1104997 := bbase (se 4 (by rfl) ⟨103593, by rfl⟩ : syracuseStep 1104997 = 207187) (by norm_num)
theorem B1105093 : Blo 872567 1105093 := bbase (se 4 (by rfl) ⟨103602, by rfl⟩ : syracuseStep 1105093 = 207205) (by norm_num)
theorem B1400005 : Blo 872567 1400005 := bbase (se 4 (by rfl) ⟨131250, by rfl⟩ : syracuseStep 1400005 = 262501) (by norm_num)
theorem B1105265 : Blo 872567 1105265 := bbase (se 2 (by rfl) ⟨414474, by rfl⟩ : syracuseStep 1105265 = 828949) (by norm_num)
theorem B1105321 : Blo 872567 1105321 := bbase (se 2 (by rfl) ⟨414495, by rfl⟩ : syracuseStep 1105321 = 828991) (by norm_num)
theorem B1400261 : Blo 872567 1400261 := bbase (se 4 (by rfl) ⟨131274, by rfl⟩ : syracuseStep 1400261 = 262549) (by norm_num)
theorem B1105417 : Blo 872567 1105417 := bbase (se 2 (by rfl) ⟨414531, by rfl⟩ : syracuseStep 1105417 = 829063) (by norm_num)
theorem B5594741 : Blo 872567 5594741 := bbase (se 5 (by rfl) ⟨262253, by rfl⟩ : syracuseStep 5594741 = 524507) (by norm_num)
theorem B1105589 : Blo 872567 1105589 := bbase (se 5 (by rfl) ⟨51824, by rfl⟩ : syracuseStep 1105589 = 103649) (by norm_num)
theorem B3366629 : Blo 872567 3366629 := bbase (se 4 (by rfl) ⟨315621, by rfl⟩ : syracuseStep 3366629 = 631243) (by norm_num)
theorem B1105645 : Blo 872567 1105645 := bbase (se 3 (by rfl) ⟨207308, by rfl⟩ : syracuseStep 1105645 = 414617) (by norm_num)
theorem B1662781 : Blo 872567 1662781 := bbase (se 3 (by rfl) ⟨311771, by rfl⟩ : syracuseStep 1662781 = 623543) (by norm_num)
theorem B1105741 : Blo 872567 1105741 := bbase (se 3 (by rfl) ⟨207326, by rfl⟩ : syracuseStep 1105741 = 414653) (by norm_num)
theorem B4972373 : Blo 872567 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B8085365 : Blo 872567 8085365 := bbase (se 5 (by rfl) ⟨379001, by rfl⟩ : syracuseStep 8085365 = 758003) (by norm_num)
theorem B1662925 : Blo 872567 1662925 := bbase (se 3 (by rfl) ⟨311798, by rfl⟩ : syracuseStep 1662925 = 623597) (by norm_num)
theorem B1105913 : Blo 872567 1105913 := bbase (se 2 (by rfl) ⟨414717, by rfl⟩ : syracuseStep 1105913 = 829435) (by norm_num)
theorem B2154533 : Blo 872567 2154533 := bbase (se 4 (by rfl) ⟨201987, by rfl⟩ : syracuseStep 2154533 = 403975) (by norm_num)
theorem B1105969 : Blo 872567 1105969 := bbase (se 2 (by rfl) ⟨414738, by rfl⟩ : syracuseStep 1105969 = 829477) (by norm_num)
theorem B1663085 : Blo 872567 1663085 := bbase (se 3 (by rfl) ⟨311828, by rfl⟩ : syracuseStep 1663085 = 623657) (by norm_num)
theorem B1106065 : Blo 872567 1106065 := bbase (se 2 (by rfl) ⟨414774, by rfl⟩ : syracuseStep 1106065 = 829549) (by norm_num)
theorem B1663229 : Blo 872567 1663229 := bbase (se 3 (by rfl) ⟨311855, by rfl⟩ : syracuseStep 1663229 = 623711) (by norm_num)
theorem B1401133 : Blo 872567 1401133 := bbase (se 3 (by rfl) ⟨262712, by rfl⟩ : syracuseStep 1401133 = 525425) (by norm_num)
theorem B1106237 : Blo 872567 1106237 := bbase (se 3 (by rfl) ⟨207419, by rfl⟩ : syracuseStep 1106237 = 414839) (by norm_num)
theorem B1106293 : Blo 872567 1106293 := bbase (se 5 (by rfl) ⟨51857, by rfl⟩ : syracuseStep 1106293 = 103715) (by norm_num)
theorem B1401229 : Blo 872567 1401229 := bbase (se 3 (by rfl) ⟨262730, by rfl⟩ : syracuseStep 1401229 = 525461) (by norm_num)
theorem B1106389 : Blo 872567 1106389 := bbase (se 7 (by rfl) ⟨12965, by rfl⟩ : syracuseStep 1106389 = 25931) (by norm_num)
theorem B1663517 : Blo 872567 1663517 := bbase (se 3 (by rfl) ⟨311909, by rfl⟩ : syracuseStep 1663517 = 623819) (by norm_num)
theorem B1401389 : Blo 872567 1401389 := bbase (se 3 (by rfl) ⟨262760, by rfl⟩ : syracuseStep 1401389 = 525521) (by norm_num)
theorem B1106561 : Blo 872567 1106561 := bbase (se 2 (by rfl) ⟨414960, by rfl⟩ : syracuseStep 1106561 = 829921) (by norm_num)
theorem B1663669 : Blo 872567 1663669 := bbase (se 5 (by rfl) ⟨77984, by rfl⟩ : syracuseStep 1663669 = 155969) (by norm_num)
theorem B1106617 : Blo 872567 1106617 := bbase (se 2 (by rfl) ⟨414981, by rfl⟩ : syracuseStep 1106617 = 829963) (by norm_num)
theorem B1106713 : Blo 872567 1106713 := bbase (se 2 (by rfl) ⟨415017, by rfl⟩ : syracuseStep 1106713 = 830035) (by norm_num)
theorem B3367813 : Blo 872567 3367813 := bbase (se 4 (by rfl) ⟨315732, by rfl⟩ : syracuseStep 3367813 = 631465) (by norm_num)
theorem B3990421 : Blo 872567 3990421 := bbase (se 6 (by rfl) ⟨93525, by rfl⟩ : syracuseStep 3990421 = 187051) (by norm_num)
theorem B1106885 : Blo 872567 1106885 := bbase (se 4 (by rfl) ⟨103770, by rfl⟩ : syracuseStep 1106885 = 207541) (by norm_num)
theorem B1663973 : Blo 872567 1663973 := bbase (se 4 (by rfl) ⟨155997, by rfl⟩ : syracuseStep 1663973 = 311995) (by norm_num)
theorem B1106941 : Blo 872567 1106941 := bbase (se 3 (by rfl) ⟨207551, by rfl⟩ : syracuseStep 1106941 = 415103) (by norm_num)
theorem B1107037 : Blo 872567 1107037 := bbase (se 3 (by rfl) ⟨207569, by rfl⟩ : syracuseStep 1107037 = 415139) (by norm_num)
theorem B1107209 : Blo 872567 1107209 := bbase (se 2 (by rfl) ⟨415203, by rfl⟩ : syracuseStep 1107209 = 830407) (by norm_num)
theorem B1107265 : Blo 872567 1107265 := bbase (se 2 (by rfl) ⟨415224, by rfl⟩ : syracuseStep 1107265 = 830449) (by norm_num)
theorem B6645077 : Blo 872567 6645077 := bbase (se 12 (by rfl) ⟨2433, by rfl⟩ : syracuseStep 6645077 = 4867) (by norm_num)
theorem B1107361 : Blo 872567 1107361 := bbase (se 2 (by rfl) ⟨415260, by rfl⟩ : syracuseStep 1107361 = 830521) (by norm_num)
theorem B1107533 : Blo 872567 1107533 := bbase (se 3 (by rfl) ⟨207662, by rfl⟩ : syracuseStep 1107533 = 415325) (by norm_num)
theorem B3368549 : Blo 872567 3368549 := bbase (se 4 (by rfl) ⟨315801, by rfl⟩ : syracuseStep 3368549 = 631603) (by norm_num)
theorem B1107589 : Blo 872567 1107589 := bbase (se 4 (by rfl) ⟨103836, by rfl⟩ : syracuseStep 1107589 = 207673) (by norm_num)
theorem B1402517 : Blo 872567 1402517 := bbase (se 6 (by rfl) ⟨32871, by rfl⟩ : syracuseStep 1402517 = 65743) (by norm_num)
theorem B1107685 : Blo 872567 1107685 := bbase (se 4 (by rfl) ⟨103845, by rfl⟩ : syracuseStep 1107685 = 207691) (by norm_num)
theorem B1009441 : Blo 872567 1009441 := bbase (se 2 (by rfl) ⟨378540, by rfl⟩ : syracuseStep 1009441 = 757081) (by norm_num)
theorem B1107857 : Blo 872567 1107857 := bbase (se 2 (by rfl) ⟨415446, by rfl⟩ : syracuseStep 1107857 = 830893) (by norm_num)
theorem B1107913 : Blo 872567 1107913 := bbase (se 2 (by rfl) ⟨415467, by rfl⟩ : syracuseStep 1107913 = 830935) (by norm_num)
theorem B14378965 : Blo 872567 14378965 := bbase (se 7 (by rfl) ⟨168503, by rfl⟩ : syracuseStep 14378965 = 337007) (by norm_num)
theorem B1108009 : Blo 872567 1108009 := bbase (se 2 (by rfl) ⟨415503, by rfl⟩ : syracuseStep 1108009 = 831007) (by norm_num)
theorem B1403029 : Blo 872567 1403029 := bbase (se 6 (by rfl) ⟨32883, by rfl⟩ : syracuseStep 1403029 = 65767) (by norm_num)
theorem B4548773 : Blo 872567 4548773 := bbase (se 4 (by rfl) ⟨426447, by rfl⟩ : syracuseStep 4548773 = 852895) (by norm_num)
theorem B1108181 : Blo 872567 1108181 := bbase (se 7 (by rfl) ⟨12986, by rfl⟩ : syracuseStep 1108181 = 25973) (by norm_num)
theorem B1108237 : Blo 872567 1108237 := bbase (se 3 (by rfl) ⟨207794, by rfl⟩ : syracuseStep 1108237 = 415589) (by norm_num)
theorem B1108333 : Blo 872567 1108333 := bbase (se 3 (by rfl) ⟨207812, by rfl⟩ : syracuseStep 1108333 = 415625) (by norm_num)
theorem B1108505 : Blo 872567 1108505 := bbase (se 2 (by rfl) ⟨415689, by rfl⟩ : syracuseStep 1108505 = 831379) (by norm_num)
theorem B1108561 : Blo 872567 1108561 := bbase (se 2 (by rfl) ⟨415710, by rfl⟩ : syracuseStep 1108561 = 831421) (by norm_num)
theorem B1108657 : Blo 872567 1108657 := bbase (se 2 (by rfl) ⟨415746, by rfl⟩ : syracuseStep 1108657 = 831493) (by norm_num)
theorem B8416021 : Blo 872567 8416021 := bbase (se 6 (by rfl) ⟨197250, by rfl⟩ : syracuseStep 8416021 = 394501) (by norm_num)
theorem B1108829 : Blo 872567 1108829 := bbase (se 3 (by rfl) ⟨207905, by rfl⟩ : syracuseStep 1108829 = 415811) (by norm_num)
theorem B2485093 : Blo 872567 2485093 := bbase (se 4 (by rfl) ⟨232977, by rfl⟩ : syracuseStep 2485093 = 465955) (by norm_num)
theorem B1108885 : Blo 872567 1108885 := bbase (se 6 (by rfl) ⟨25989, by rfl⟩ : syracuseStep 1108885 = 51979) (by norm_num)
theorem B2845589 : Blo 872567 2845589 := bbase (se 6 (by rfl) ⟨66693, by rfl⟩ : syracuseStep 2845589 = 133387) (by norm_num)
theorem B4418549 : Blo 872567 4418549 := bbase (se 5 (by rfl) ⟨207119, by rfl⟩ : syracuseStep 4418549 = 414239) (by norm_num)
theorem B1108981 : Blo 872567 1108981 := bbase (se 5 (by rfl) ⟨51983, by rfl⟩ : syracuseStep 1108981 = 103967) (by norm_num)
theorem B1404029 : Blo 872567 1404029 := bbase (se 3 (by rfl) ⟨263255, by rfl⟩ : syracuseStep 1404029 = 526511) (by norm_num)
theorem B1993877 : Blo 872567 1993877 := bbase (se 6 (by rfl) ⟨46731, by rfl⟩ : syracuseStep 1993877 = 93463) (by norm_num)
theorem B1109153 : Blo 872567 1109153 := bbase (se 2 (by rfl) ⟨415932, by rfl⟩ : syracuseStep 1109153 = 831865) (by norm_num)
theorem B1109209 : Blo 872567 1109209 := bbase (se 2 (by rfl) ⟨415953, by rfl⟩ : syracuseStep 1109209 = 831907) (by norm_num)
theorem B1109305 : Blo 872567 1109305 := bbase (se 2 (by rfl) ⟨415989, by rfl⟩ : syracuseStep 1109305 = 831979) (by norm_num)
theorem B1011133 : Blo 872567 1011133 := bbase (se 3 (by rfl) ⟨189587, by rfl⟩ : syracuseStep 1011133 = 379175) (by norm_num)
theorem B1535645 : Blo 872567 1535645 := bbase (se 3 (by rfl) ⟨287933, by rfl⟩ : syracuseStep 1535645 = 575867) (by norm_num)
theorem B2944997 : Blo 872567 2944997 := bbase (se 4 (by rfl) ⟨276093, by rfl⟩ : syracuseStep 2944997 = 552187) (by norm_num)
theorem B4419845 : Blo 872567 4419845 := bbase (se 4 (by rfl) ⟨414360, by rfl⟩ : syracuseStep 4419845 = 828721) (by norm_num)
theorem B2945429 : Blo 872567 2945429 := bbase (se 6 (by rfl) ⟨69033, by rfl⟩ : syracuseStep 2945429 = 138067) (by norm_num)
theorem B1896853 : Blo 872567 1896853 := bbase (se 6 (by rfl) ⟨44457, by rfl⟩ : syracuseStep 1896853 = 88915) (by norm_num)
theorem B1798573 : Blo 872567 1798573 := bbase (se 3 (by rfl) ⟨337232, by rfl⟩ : syracuseStep 1798573 = 674465) (by norm_num)
theorem B1864205 : Blo 872567 1864205 := bbase (se 3 (by rfl) ⟨349538, by rfl⟩ : syracuseStep 1864205 = 699077) (by norm_num)
theorem B3732101 : Blo 872567 3732101 := bbase (se 4 (by rfl) ⟨349884, by rfl⟩ : syracuseStep 3732101 = 699769) (by norm_num)
theorem B2945861 : Blo 872567 2945861 := bbase (se 4 (by rfl) ⟨276174, by rfl⟩ : syracuseStep 2945861 = 552349) (by norm_num)
theorem B3732389 : Blo 872567 3732389 := bbase (se 4 (by rfl) ⟨349911, by rfl⟩ : syracuseStep 3732389 = 699823) (by norm_num)
theorem B1078337 : Blo 872567 1078337 := bbase (se 2 (by rfl) ⟨404376, by rfl⟩ : syracuseStep 1078337 = 808753) (by norm_num)
theorem B2126965 : Blo 872567 2126965 := bbase (se 5 (by rfl) ⟨99701, by rfl⟩ : syracuseStep 2126965 = 199403) (by norm_num)
theorem B2946293 : Blo 872567 2946293 := bbase (se 5 (by rfl) ⟨138107, by rfl⟩ : syracuseStep 2946293 = 276215) (by norm_num)
theorem B1864957 : Blo 872567 1864957 := bbase (se 3 (by rfl) ⟨349679, by rfl⟩ : syracuseStep 1864957 = 699359) (by norm_num)
theorem B1963277 : Blo 872567 1963277 := bbase (se 3 (by rfl) ⟨368114, by rfl⟩ : syracuseStep 1963277 = 736229) (by norm_num)
theorem B1963349 : Blo 872567 1963349 := bbase (se 13 (by rfl) ⟨359, by rfl⟩ : syracuseStep 1963349 = 719) (by norm_num)
theorem B1865101 : Blo 872567 1865101 := bbase (se 3 (by rfl) ⟨349706, by rfl⟩ : syracuseStep 1865101 = 699413) (by norm_num)
theorem B1963421 : Blo 872567 1963421 := bbase (se 3 (by rfl) ⟨368141, by rfl⟩ : syracuseStep 1963421 = 736283) (by norm_num)
theorem B7468469 : Blo 872567 7468469 := bbase (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) (by norm_num)
theorem B1996213 : Blo 872567 1996213 := bbase (se 5 (by rfl) ⟨93572, by rfl⟩ : syracuseStep 1996213 = 187145) (by norm_num)
theorem B1963493 : Blo 872567 1963493 := bbase (se 4 (by rfl) ⟨184077, by rfl⟩ : syracuseStep 1963493 = 368155) (by norm_num)
theorem B4421141 : Blo 872567 4421141 := bbase (se 6 (by rfl) ⟨103620, by rfl⟩ : syracuseStep 4421141 = 207241) (by norm_num)
theorem B1963565 : Blo 872567 1963565 := bbase (se 3 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 1963565 = 736337) (by norm_num)
theorem B1078849 : Blo 872567 1078849 := bbase (se 2 (by rfl) ⟨404568, by rfl⟩ : syracuseStep 1078849 = 809137) (by norm_num)
theorem B3995237 : Blo 872567 3995237 := bbase (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) (by norm_num)
theorem B1963637 : Blo 872567 1963637 := bbase (se 5 (by rfl) ⟨92045, by rfl⟩ : syracuseStep 1963637 = 184091) (by norm_num)
theorem B2487941 : Blo 872567 2487941 := bbase (se 4 (by rfl) ⟨233244, by rfl⟩ : syracuseStep 2487941 = 466489) (by norm_num)
theorem B3733141 : Blo 872567 3733141 := bbase (se 6 (by rfl) ⟨87495, by rfl⟩ : syracuseStep 3733141 = 174991) (by norm_num)
theorem B2946725 : Blo 872567 2946725 := bbase (se 4 (by rfl) ⟨276255, by rfl⟩ : syracuseStep 2946725 = 552511) (by norm_num)
theorem B1963709 : Blo 872567 1963709 := bbase (se 3 (by rfl) ⟨368195, by rfl⟩ : syracuseStep 1963709 = 736391) (by norm_num)
theorem B1242877 : Blo 872567 1242877 := bbase (se 3 (by rfl) ⟨233039, by rfl⟩ : syracuseStep 1242877 = 466079) (by norm_num)
theorem B1963781 : Blo 872567 1963781 := bbase (se 4 (by rfl) ⟨184104, by rfl⟩ : syracuseStep 1963781 = 368209) (by norm_num)
theorem B1865477 : Blo 872567 1865477 := bbase (se 4 (by rfl) ⟨174888, by rfl⟩ : syracuseStep 1865477 = 349777) (by norm_num)
theorem B1963853 : Blo 872567 1963853 := bbase (se 3 (by rfl) ⟨368222, by rfl⟩ : syracuseStep 1963853 = 736445) (by norm_num)
theorem B1963925 : Blo 872567 1963925 := bbase (se 6 (by rfl) ⟨46029, by rfl⟩ : syracuseStep 1963925 = 92059) (by norm_num)
theorem B1963997 : Blo 872567 1963997 := bbase (se 3 (by rfl) ⟨368249, by rfl⟩ : syracuseStep 1963997 = 736499) (by norm_num)
theorem B1472485 : Blo 872567 1472485 := bbase (se 4 (by rfl) ⟨138045, by rfl⟩ : syracuseStep 1472485 = 276091) (by norm_num)
theorem B1964069 : Blo 872567 1964069 := bbase (se 4 (by rfl) ⟨184131, by rfl⟩ : syracuseStep 1964069 = 368263) (by norm_num)
theorem B1472573 : Blo 872567 1472573 := bbase (se 3 (by rfl) ⟨276107, by rfl⟩ : syracuseStep 1472573 = 552215) (by norm_num)
theorem B2947157 : Blo 872567 2947157 := bbase (se 8 (by rfl) ⟨17268, by rfl⟩ : syracuseStep 2947157 = 34537) (by norm_num)
theorem B1964141 : Blo 872567 1964141 := bbase (se 3 (by rfl) ⟨368276, by rfl⟩ : syracuseStep 1964141 = 736553) (by norm_num)
theorem B1865845 : Blo 872567 1865845 := bbase (se 5 (by rfl) ⟨87461, by rfl⟩ : syracuseStep 1865845 = 174923) (by norm_num)
theorem B1964213 : Blo 872567 1964213 := bbase (se 5 (by rfl) ⟨92072, by rfl⟩ : syracuseStep 1964213 = 184145) (by norm_num)
theorem B1472701 : Blo 872567 1472701 := bbase (se 3 (by rfl) ⟨276131, by rfl⟩ : syracuseStep 1472701 = 552263) (by norm_num)
theorem B1308869 : Blo 872567 1308869 := bbase (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) (by norm_num)
theorem B1308893 : Blo 872567 1308893 := bbase (se 3 (by rfl) ⟨245417, by rfl⟩ : syracuseStep 1308893 = 490835) (by norm_num)
theorem B1308917 : Blo 872567 1308917 := bbase (se 5 (by rfl) ⟨61355, by rfl⟩ : syracuseStep 1308917 = 122711) (by norm_num)
theorem B1964285 : Blo 872567 1964285 := bbase (se 3 (by rfl) ⟨368303, by rfl⟩ : syracuseStep 1964285 = 736607) (by norm_num)
theorem B1308941 : Blo 872567 1308941 := bbase (se 3 (by rfl) ⟨245426, by rfl⟩ : syracuseStep 1308941 = 490853) (by norm_num)
theorem B1472789 : Blo 872567 1472789 := bbase (se 6 (by rfl) ⟨34518, by rfl⟩ : syracuseStep 1472789 = 69037) (by norm_num)
theorem B1308965 : Blo 872567 1308965 := bbase (se 4 (by rfl) ⟨122715, by rfl⟩ : syracuseStep 1308965 = 245431) (by norm_num)
theorem B1308989 : Blo 872567 1308989 := bbase (se 3 (by rfl) ⟨245435, by rfl⟩ : syracuseStep 1308989 = 490871) (by norm_num)
theorem B1964357 : Blo 872567 1964357 := bbase (se 4 (by rfl) ⟨184158, by rfl⟩ : syracuseStep 1964357 = 368317) (by norm_num)
theorem B1243469 : Blo 872567 1243469 := bbase (se 3 (by rfl) ⟨233150, by rfl⟩ : syracuseStep 1243469 = 466301) (by norm_num)
theorem B1309013 : Blo 872567 1309013 := bbase (se 10 (by rfl) ⟨1917, by rfl⟩ : syracuseStep 1309013 = 3835) (by norm_num)
theorem B1309037 : Blo 872567 1309037 := bbase (se 3 (by rfl) ⟨245444, by rfl⟩ : syracuseStep 1309037 = 490889) (by norm_num)
theorem B3733877 : Blo 872567 3733877 := bbase (se 5 (by rfl) ⟨175025, by rfl⟩ : syracuseStep 3733877 = 350051) (by norm_num)
theorem B1309061 : Blo 872567 1309061 := bbase (se 4 (by rfl) ⟨122724, by rfl⟩ : syracuseStep 1309061 = 245449) (by norm_num)
theorem B1964429 : Blo 872567 1964429 := bbase (se 3 (by rfl) ⟨368330, by rfl⟩ : syracuseStep 1964429 = 736661) (by norm_num)
theorem B1472917 : Blo 872567 1472917 := bbase (se 6 (by rfl) ⟨34521, by rfl⟩ : syracuseStep 1472917 = 69043) (by norm_num)
theorem B1309085 : Blo 872567 1309085 := bbase (se 3 (by rfl) ⟨245453, by rfl⟩ : syracuseStep 1309085 = 490907) (by norm_num)
theorem B1243549 : Blo 872567 1243549 := bbase (se 3 (by rfl) ⟨233165, by rfl⟩ : syracuseStep 1243549 = 466331) (by norm_num)
theorem B1309109 : Blo 872567 1309109 := bbase (se 5 (by rfl) ⟨61364, by rfl⟩ : syracuseStep 1309109 = 122729) (by norm_num)
theorem B1309133 : Blo 872567 1309133 := bbase (se 3 (by rfl) ⟨245462, by rfl⟩ : syracuseStep 1309133 = 490925) (by norm_num)
theorem B1964501 : Blo 872567 1964501 := bbase (se 7 (by rfl) ⟨23021, by rfl⟩ : syracuseStep 1964501 = 46043) (by norm_num)
theorem B1309157 : Blo 872567 1309157 := bbase (se 4 (by rfl) ⟨122733, by rfl⟩ : syracuseStep 1309157 = 245467) (by norm_num)
theorem B1473005 : Blo 872567 1473005 := bbase (se 3 (by rfl) ⟨276188, by rfl⟩ : syracuseStep 1473005 = 552377) (by norm_num)
theorem B1309181 : Blo 872567 1309181 := bbase (se 3 (by rfl) ⟨245471, by rfl⟩ : syracuseStep 1309181 = 490943) (by norm_num)
theorem B2947589 : Blo 872567 2947589 := bbase (se 4 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 2947589 = 552673) (by norm_num)
theorem B1309205 : Blo 872567 1309205 := bbase (se 6 (by rfl) ⟨30684, by rfl⟩ : syracuseStep 1309205 = 61369) (by norm_num)
theorem B1243669 : Blo 872567 1243669 := bbase (se 6 (by rfl) ⟨29148, by rfl⟩ : syracuseStep 1243669 = 58297) (by norm_num)
theorem B1964573 : Blo 872567 1964573 := bbase (se 3 (by rfl) ⟨368357, by rfl⟩ : syracuseStep 1964573 = 736715) (by norm_num)
theorem B1309229 : Blo 872567 1309229 := bbase (se 3 (by rfl) ⟨245480, by rfl⟩ : syracuseStep 1309229 = 490961) (by norm_num)
theorem B1309253 : Blo 872567 1309253 := bbase (se 4 (by rfl) ⟨122742, by rfl⟩ : syracuseStep 1309253 = 245485) (by norm_num)
theorem B1309277 : Blo 872567 1309277 := bbase (se 3 (by rfl) ⟨245489, by rfl⟩ : syracuseStep 1309277 = 490979) (by norm_num)
theorem B1964645 : Blo 872567 1964645 := bbase (se 4 (by rfl) ⟨184185, by rfl⟩ : syracuseStep 1964645 = 368371) (by norm_num)
theorem B1473133 : Blo 872567 1473133 := bbase (se 3 (by rfl) ⟨276212, by rfl⟩ : syracuseStep 1473133 = 552425) (by norm_num)
theorem B1309301 : Blo 872567 1309301 := bbase (se 5 (by rfl) ⟨61373, by rfl⟩ : syracuseStep 1309301 = 122747) (by norm_num)
theorem B1243765 : Blo 872567 1243765 := bbase (se 5 (by rfl) ⟨58301, by rfl⟩ : syracuseStep 1243765 = 116603) (by norm_num)
theorem B1309325 : Blo 872567 1309325 := bbase (se 3 (by rfl) ⟨245498, by rfl⟩ : syracuseStep 1309325 = 490997) (by norm_num)
theorem B981661 : Blo 872567 981661 := bbase (se 3 (by rfl) ⟨184061, by rfl⟩ : syracuseStep 981661 = 368123) (by norm_num)
theorem B1309349 : Blo 872567 1309349 := bbase (se 4 (by rfl) ⟨122751, by rfl⟩ : syracuseStep 1309349 = 245503) (by norm_num)
theorem B1964717 : Blo 872567 1964717 := bbase (se 3 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 1964717 = 736769) (by norm_num)
theorem B1309373 : Blo 872567 1309373 := bbase (se 3 (by rfl) ⟨245507, by rfl⟩ : syracuseStep 1309373 = 491015) (by norm_num)
theorem B981697 : Blo 872567 981697 := bbase (se 2 (by rfl) ⟨368136, by rfl⟩ : syracuseStep 981697 = 736273) (by norm_num)
theorem B1473221 : Blo 872567 1473221 := bbase (se 4 (by rfl) ⟨138114, by rfl⟩ : syracuseStep 1473221 = 276229) (by norm_num)
theorem B1309397 : Blo 872567 1309397 := bbase (se 7 (by rfl) ⟨15344, by rfl⟩ : syracuseStep 1309397 = 30689) (by norm_num)
theorem B981733 : Blo 872567 981733 := bbase (se 4 (by rfl) ⟨92037, by rfl⟩ : syracuseStep 981733 = 184075) (by norm_num)
theorem B1309421 : Blo 872567 1309421 := bbase (se 3 (by rfl) ⟨245516, by rfl⟩ : syracuseStep 1309421 = 491033) (by norm_num)
theorem B1964789 : Blo 872567 1964789 := bbase (se 5 (by rfl) ⟨92099, by rfl⟩ : syracuseStep 1964789 = 184199) (by norm_num)
theorem B1309445 : Blo 872567 1309445 := bbase (se 4 (by rfl) ⟨122760, by rfl⟩ : syracuseStep 1309445 = 245521) (by norm_num)
theorem B981769 : Blo 872567 981769 := bbase (se 2 (by rfl) ⟨368163, by rfl⟩ : syracuseStep 981769 = 736327) (by norm_num)
theorem B1309469 : Blo 872567 1309469 := bbase (se 3 (by rfl) ⟨245525, by rfl⟩ : syracuseStep 1309469 = 491051) (by norm_num)
theorem B4422437 : Blo 872567 4422437 := bbase (se 4 (by rfl) ⟨414603, by rfl⟩ : syracuseStep 4422437 = 829207) (by norm_num)
theorem B2489125 : Blo 872567 2489125 := bbase (se 4 (by rfl) ⟨233355, by rfl⟩ : syracuseStep 2489125 = 466711) (by norm_num)
theorem B981805 : Blo 872567 981805 := bbase (se 3 (by rfl) ⟨184088, by rfl⟩ : syracuseStep 981805 = 368177) (by norm_num)
theorem B1309493 : Blo 872567 1309493 := bbase (se 5 (by rfl) ⟨61382, by rfl⟩ : syracuseStep 1309493 = 122765) (by norm_num)
theorem B1964861 : Blo 872567 1964861 := bbase (se 3 (by rfl) ⟨368411, by rfl⟩ : syracuseStep 1964861 = 736823) (by norm_num)
theorem B1473349 : Blo 872567 1473349 := bbase (se 4 (by rfl) ⟨138126, by rfl⟩ : syracuseStep 1473349 = 276253) (by norm_num)
theorem B1309517 : Blo 872567 1309517 := bbase (se 3 (by rfl) ⟨245534, by rfl⟩ : syracuseStep 1309517 = 491069) (by norm_num)
theorem B981841 : Blo 872567 981841 := bbase (se 2 (by rfl) ⟨368190, by rfl⟩ : syracuseStep 981841 = 736381) (by norm_num)
theorem B1309541 : Blo 872567 1309541 := bbase (se 4 (by rfl) ⟨122769, by rfl⟩ : syracuseStep 1309541 = 245539) (by norm_num)
theorem B3406693 : Blo 872567 3406693 := bbase (se 4 (by rfl) ⟨319377, by rfl⟩ : syracuseStep 3406693 = 638755) (by norm_num)
theorem B981877 : Blo 872567 981877 := bbase (se 5 (by rfl) ⟨46025, by rfl⟩ : syracuseStep 981877 = 92051) (by norm_num)
theorem B1309565 : Blo 872567 1309565 := bbase (se 3 (by rfl) ⟨245543, by rfl⟩ : syracuseStep 1309565 = 491087) (by norm_num)
theorem B1964933 : Blo 872567 1964933 := bbase (se 4 (by rfl) ⟨184212, by rfl⟩ : syracuseStep 1964933 = 368425) (by norm_num)
theorem B1309589 : Blo 872567 1309589 := bbase (se 6 (by rfl) ⟨30693, by rfl⟩ : syracuseStep 1309589 = 61387) (by norm_num)
theorem B981913 : Blo 872567 981913 := bbase (se 2 (by rfl) ⟨368217, by rfl⟩ : syracuseStep 981913 = 736435) (by norm_num)
theorem B1473437 : Blo 872567 1473437 := bbase (se 3 (by rfl) ⟨276269, by rfl⟩ : syracuseStep 1473437 = 552539) (by norm_num)
theorem B1309613 : Blo 872567 1309613 := bbase (se 3 (by rfl) ⟨245552, by rfl⟩ : syracuseStep 1309613 = 491105) (by norm_num)
theorem B2948021 : Blo 872567 2948021 := bbase (se 5 (by rfl) ⟨138188, by rfl⟩ : syracuseStep 2948021 = 276377) (by norm_num)
theorem B981949 : Blo 872567 981949 := bbase (se 3 (by rfl) ⟨184115, by rfl⟩ : syracuseStep 981949 = 368231) (by norm_num)
theorem B1309637 : Blo 872567 1309637 := bbase (se 4 (by rfl) ⟨122778, by rfl⟩ : syracuseStep 1309637 = 245557) (by norm_num)
theorem B2489285 : Blo 872567 2489285 := bbase (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) (by norm_num)
theorem B1965005 : Blo 872567 1965005 := bbase (se 3 (by rfl) ⟨368438, by rfl⟩ : syracuseStep 1965005 = 736877) (by norm_num)
theorem B11369429 : Blo 872567 11369429 := bbase (se 7 (by rfl) ⟨133235, by rfl⟩ : syracuseStep 11369429 = 266471) (by norm_num)
theorem B1309661 : Blo 872567 1309661 := bbase (se 3 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 1309661 = 491123) (by norm_num)
theorem B981985 : Blo 872567 981985 := bbase (se 2 (by rfl) ⟨368244, by rfl⟩ : syracuseStep 981985 = 736489) (by norm_num)
theorem B1309685 : Blo 872567 1309685 := bbase (se 5 (by rfl) ⟨61391, by rfl⟩ : syracuseStep 1309685 = 122783) (by norm_num)
theorem B982021 : Blo 872567 982021 := bbase (se 4 (by rfl) ⟨92064, by rfl⟩ : syracuseStep 982021 = 184129) (by norm_num)
theorem B1309709 : Blo 872567 1309709 := bbase (se 3 (by rfl) ⟨245570, by rfl⟩ : syracuseStep 1309709 = 491141) (by norm_num)
theorem B1965077 : Blo 872567 1965077 := bbase (se 6 (by rfl) ⟨46056, by rfl⟩ : syracuseStep 1965077 = 92113) (by norm_num)
theorem B1473565 : Blo 872567 1473565 := bbase (se 3 (by rfl) ⟨276293, by rfl⟩ : syracuseStep 1473565 = 552587) (by norm_num)
theorem B1309733 : Blo 872567 1309733 := bbase (se 4 (by rfl) ⟨122787, by rfl⟩ : syracuseStep 1309733 = 245575) (by norm_num)
theorem B982057 : Blo 872567 982057 := bbase (se 2 (by rfl) ⟨368271, by rfl⟩ : syracuseStep 982057 = 736543) (by norm_num)
theorem B1309757 : Blo 872567 1309757 := bbase (se 3 (by rfl) ⟨245579, by rfl⟩ : syracuseStep 1309757 = 491159) (by norm_num)
theorem B1997893 : Blo 872567 1997893 := bbase (se 4 (by rfl) ⟨187302, by rfl⟩ : syracuseStep 1997893 = 374605) (by norm_num)
theorem B982093 : Blo 872567 982093 := bbase (se 3 (by rfl) ⟨184142, by rfl⟩ : syracuseStep 982093 = 368285) (by norm_num)
theorem B1309781 : Blo 872567 1309781 := bbase (se 8 (by rfl) ⟨7674, by rfl⟩ : syracuseStep 1309781 = 15349) (by norm_num)
theorem B1965149 : Blo 872567 1965149 := bbase (se 3 (by rfl) ⟨368465, by rfl⟩ : syracuseStep 1965149 = 736931) (by norm_num)
theorem B1244261 : Blo 872567 1244261 := bbase (se 4 (by rfl) ⟨116649, by rfl⟩ : syracuseStep 1244261 = 233299) (by norm_num)
theorem B1309805 : Blo 872567 1309805 := bbase (se 3 (by rfl) ⟨245588, by rfl⟩ : syracuseStep 1309805 = 491177) (by norm_num)
theorem B982129 : Blo 872567 982129 := bbase (se 2 (by rfl) ⟨368298, by rfl⟩ : syracuseStep 982129 = 736597) (by norm_num)
theorem B1473653 : Blo 872567 1473653 := bbase (se 5 (by rfl) ⟨69077, by rfl⟩ : syracuseStep 1473653 = 138155) (by norm_num)
theorem B1309829 : Blo 872567 1309829 := bbase (se 4 (by rfl) ⟨122796, by rfl⟩ : syracuseStep 1309829 = 245593) (by norm_num)
theorem B982165 : Blo 872567 982165 := bbase (se 6 (by rfl) ⟨23019, by rfl⟩ : syracuseStep 982165 = 46039) (by norm_num)
theorem B1309853 : Blo 872567 1309853 := bbase (se 3 (by rfl) ⟨245597, by rfl⟩ : syracuseStep 1309853 = 491195) (by norm_num)
theorem B1965221 : Blo 872567 1965221 := bbase (se 4 (by rfl) ⟨184239, by rfl⟩ : syracuseStep 1965221 = 368479) (by norm_num)
theorem B1309877 : Blo 872567 1309877 := bbase (se 5 (by rfl) ⟨61400, by rfl⟩ : syracuseStep 1309877 = 122801) (by norm_num)
theorem B2489525 : Blo 872567 2489525 := bbase (se 5 (by rfl) ⟨116696, by rfl⟩ : syracuseStep 2489525 = 233393) (by norm_num)
theorem B982201 : Blo 872567 982201 := bbase (se 2 (by rfl) ⟨368325, by rfl⟩ : syracuseStep 982201 = 736651) (by norm_num)
theorem B1309901 : Blo 872567 1309901 := bbase (se 3 (by rfl) ⟨245606, by rfl⟩ : syracuseStep 1309901 = 491213) (by norm_num)
theorem B982237 : Blo 872567 982237 := bbase (se 3 (by rfl) ⟨184169, by rfl⟩ : syracuseStep 982237 = 368339) (by norm_num)
theorem B1309925 : Blo 872567 1309925 := bbase (se 4 (by rfl) ⟨122805, by rfl⟩ : syracuseStep 1309925 = 245611) (by norm_num)
theorem B1965293 : Blo 872567 1965293 := bbase (se 3 (by rfl) ⟨368492, by rfl⟩ : syracuseStep 1965293 = 736985) (by norm_num)
theorem B1473781 : Blo 872567 1473781 := bbase (se 5 (by rfl) ⟨69083, by rfl⟩ : syracuseStep 1473781 = 138167) (by norm_num)
theorem B1309949 : Blo 872567 1309949 := bbase (se 3 (by rfl) ⟨245615, by rfl⟩ : syracuseStep 1309949 = 491231) (by norm_num)
theorem B982273 : Blo 872567 982273 := bbase (se 2 (by rfl) ⟨368352, by rfl⟩ : syracuseStep 982273 = 736705) (by norm_num)
theorem B1309973 : Blo 872567 1309973 := bbase (se 6 (by rfl) ⟨30702, by rfl⟩ : syracuseStep 1309973 = 61405) (by norm_num)
theorem B982309 : Blo 872567 982309 := bbase (se 4 (by rfl) ⟨92091, by rfl⟩ : syracuseStep 982309 = 184183) (by norm_num)
theorem B1309997 : Blo 872567 1309997 := bbase (se 3 (by rfl) ⟨245624, by rfl⟩ : syracuseStep 1309997 = 491249) (by norm_num)
theorem B1965365 : Blo 872567 1965365 := bbase (se 5 (by rfl) ⟨92126, by rfl⟩ : syracuseStep 1965365 = 184253) (by norm_num)
theorem B1310021 : Blo 872567 1310021 := bbase (se 4 (by rfl) ⟨122814, by rfl⟩ : syracuseStep 1310021 = 245629) (by norm_num)
theorem B982345 : Blo 872567 982345 := bbase (se 2 (by rfl) ⟨368379, by rfl⟩ : syracuseStep 982345 = 736759) (by norm_num)
theorem B1473869 : Blo 872567 1473869 := bbase (se 3 (by rfl) ⟨276350, by rfl⟩ : syracuseStep 1473869 = 552701) (by norm_num)
theorem B1310045 : Blo 872567 1310045 := bbase (se 3 (by rfl) ⟨245633, by rfl⟩ : syracuseStep 1310045 = 491267) (by norm_num)
theorem B2948453 : Blo 872567 2948453 := bbase (se 4 (by rfl) ⟨276417, by rfl⟩ : syracuseStep 2948453 = 552835) (by norm_num)
theorem B982381 : Blo 872567 982381 := bbase (se 3 (by rfl) ⟨184196, by rfl⟩ : syracuseStep 982381 = 368393) (by norm_num)
theorem B1310069 : Blo 872567 1310069 := bbase (se 5 (by rfl) ⟨61409, by rfl⟩ : syracuseStep 1310069 = 122819) (by norm_num)
theorem B2489717 : Blo 872567 2489717 := bbase (se 5 (by rfl) ⟨116705, by rfl⟩ : syracuseStep 2489717 = 233411) (by norm_num)
theorem B1965437 : Blo 872567 1965437 := bbase (se 3 (by rfl) ⟨368519, by rfl⟩ : syracuseStep 1965437 = 737039) (by norm_num)
theorem B1310093 : Blo 872567 1310093 := bbase (se 3 (by rfl) ⟨245642, by rfl⟩ : syracuseStep 1310093 = 491285) (by norm_num)
theorem B982417 : Blo 872567 982417 := bbase (se 2 (by rfl) ⟨368406, by rfl⟩ : syracuseStep 982417 = 736813) (by norm_num)
theorem B1310117 : Blo 872567 1310117 := bbase (se 4 (by rfl) ⟨122823, by rfl⟩ : syracuseStep 1310117 = 245647) (by norm_num)
theorem B982453 : Blo 872567 982453 := bbase (se 5 (by rfl) ⟨46052, by rfl⟩ : syracuseStep 982453 = 92105) (by norm_num)
theorem B1310141 : Blo 872567 1310141 := bbase (se 3 (by rfl) ⟨245651, by rfl⟩ : syracuseStep 1310141 = 491303) (by norm_num)
theorem B2358725 : Blo 872567 2358725 := bbase (se 4 (by rfl) ⟨221130, by rfl⟩ : syracuseStep 2358725 = 442261) (by norm_num)
theorem B1965509 : Blo 872567 1965509 := bbase (se 4 (by rfl) ⟨184266, by rfl⟩ : syracuseStep 1965509 = 368533) (by norm_num)
theorem B1473997 : Blo 872567 1473997 := bbase (se 3 (by rfl) ⟨276374, by rfl⟩ : syracuseStep 1473997 = 552749) (by norm_num)
theorem B1310165 : Blo 872567 1310165 := bbase (se 7 (by rfl) ⟨15353, by rfl⟩ : syracuseStep 1310165 = 30707) (by norm_num)
theorem B982489 : Blo 872567 982489 := bbase (se 2 (by rfl) ⟨368433, by rfl⟩ : syracuseStep 982489 = 736867) (by norm_num)
theorem B1310189 : Blo 872567 1310189 := bbase (se 3 (by rfl) ⟨245660, by rfl⟩ : syracuseStep 1310189 = 491321) (by norm_num)
theorem B982525 : Blo 872567 982525 := bbase (se 3 (by rfl) ⟨184223, by rfl⟩ : syracuseStep 982525 = 368447) (by norm_num)
theorem B1310213 : Blo 872567 1310213 := bbase (se 4 (by rfl) ⟨122832, by rfl⟩ : syracuseStep 1310213 = 245665) (by norm_num)
theorem B4554245 : Blo 872567 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B1965581 : Blo 872567 1965581 := bbase (se 3 (by rfl) ⟨368546, by rfl⟩ : syracuseStep 1965581 = 737093) (by norm_num)
theorem B1310237 : Blo 872567 1310237 := bbase (se 3 (by rfl) ⟨245669, by rfl⟩ : syracuseStep 1310237 = 491339) (by norm_num)
theorem B982561 : Blo 872567 982561 := bbase (se 2 (by rfl) ⟨368460, by rfl⟩ : syracuseStep 982561 = 736921) (by norm_num)
theorem B1474085 : Blo 872567 1474085 := bbase (se 4 (by rfl) ⟨138195, by rfl⟩ : syracuseStep 1474085 = 276391) (by norm_num)
theorem B1310261 : Blo 872567 1310261 := bbase (se 5 (by rfl) ⟨61418, by rfl⟩ : syracuseStep 1310261 = 122837) (by norm_num)
theorem B982597 : Blo 872567 982597 := bbase (se 4 (by rfl) ⟨92118, by rfl⟩ : syracuseStep 982597 = 184237) (by norm_num)
theorem B1310285 : Blo 872567 1310285 := bbase (se 3 (by rfl) ⟨245678, by rfl⟩ : syracuseStep 1310285 = 491357) (by norm_num)
theorem B1965653 : Blo 872567 1965653 := bbase (se 8 (by rfl) ⟨11517, by rfl⟩ : syracuseStep 1965653 = 23035) (by norm_num)
theorem B1867349 : Blo 872567 1867349 := bbase (se 8 (by rfl) ⟨10941, by rfl⟩ : syracuseStep 1867349 = 21883) (by norm_num)
theorem B2096741 : Blo 872567 2096741 := bbase (se 4 (by rfl) ⟨196569, by rfl⟩ : syracuseStep 2096741 = 393139) (by norm_num)
theorem B1310309 : Blo 872567 1310309 := bbase (se 4 (by rfl) ⟨122841, by rfl⟩ : syracuseStep 1310309 = 245683) (by norm_num)
theorem B982633 : Blo 872567 982633 := bbase (se 2 (by rfl) ⟨368487, by rfl⟩ : syracuseStep 982633 = 736975) (by norm_num)
theorem B1310333 : Blo 872567 1310333 := bbase (se 3 (by rfl) ⟨245687, by rfl⟩ : syracuseStep 1310333 = 491375) (by norm_num)
theorem B982669 : Blo 872567 982669 := bbase (se 3 (by rfl) ⟨184250, by rfl⟩ : syracuseStep 982669 = 368501) (by norm_num)
theorem B1244813 : Blo 872567 1244813 := bbase (se 3 (by rfl) ⟨233402, by rfl⟩ : syracuseStep 1244813 = 466805) (by norm_num)
theorem B1310357 : Blo 872567 1310357 := bbase (se 6 (by rfl) ⟨30711, by rfl⟩ : syracuseStep 1310357 = 61423) (by norm_num)
theorem B1965725 : Blo 872567 1965725 := bbase (se 3 (by rfl) ⟨368573, by rfl⟩ : syracuseStep 1965725 = 737147) (by norm_num)
theorem B1474213 : Blo 872567 1474213 := bbase (se 4 (by rfl) ⟨138207, by rfl⟩ : syracuseStep 1474213 = 276415) (by norm_num)
theorem B1310381 : Blo 872567 1310381 := bbase (se 3 (by rfl) ⟨245696, by rfl⟩ : syracuseStep 1310381 = 491393) (by norm_num)
theorem B982705 : Blo 872567 982705 := bbase (se 2 (by rfl) ⟨368514, by rfl⟩ : syracuseStep 982705 = 737029) (by norm_num)
theorem B1310405 : Blo 872567 1310405 := bbase (se 4 (by rfl) ⟨122850, by rfl⟩ : syracuseStep 1310405 = 245701) (by norm_num)
theorem B982741 : Blo 872567 982741 := bbase (se 7 (by rfl) ⟨11516, by rfl⟩ : syracuseStep 982741 = 23033) (by norm_num)
theorem B4980437 : Blo 872567 4980437 := bbase (se 7 (by rfl) ⟨58364, by rfl⟩ : syracuseStep 4980437 = 116729) (by norm_num)
theorem B1310429 : Blo 872567 1310429 := bbase (se 3 (by rfl) ⟨245705, by rfl⟩ : syracuseStep 1310429 = 491411) (by norm_num)
theorem B1965797 : Blo 872567 1965797 := bbase (se 4 (by rfl) ⟨184293, by rfl⟩ : syracuseStep 1965797 = 368587) (by norm_num)
theorem B1867493 : Blo 872567 1867493 := bbase (se 4 (by rfl) ⟨175077, by rfl⟩ : syracuseStep 1867493 = 350155) (by norm_num)
theorem B1310453 : Blo 872567 1310453 := bbase (se 5 (by rfl) ⟨61427, by rfl⟩ : syracuseStep 1310453 = 122855) (by norm_num)
theorem B982777 : Blo 872567 982777 := bbase (se 2 (by rfl) ⟨368541, by rfl⟩ : syracuseStep 982777 = 737083) (by norm_num)
theorem B1474301 : Blo 872567 1474301 := bbase (se 3 (by rfl) ⟨276431, by rfl⟩ : syracuseStep 1474301 = 552863) (by norm_num)
theorem B1310477 : Blo 872567 1310477 := bbase (se 3 (by rfl) ⟨245714, by rfl⟩ : syracuseStep 1310477 = 491429) (by norm_num)
theorem B2948885 : Blo 872567 2948885 := bbase (se 6 (by rfl) ⟨69114, by rfl⟩ : syracuseStep 2948885 = 138229) (by norm_num)
theorem B982813 : Blo 872567 982813 := bbase (se 3 (by rfl) ⟨184277, by rfl⟩ : syracuseStep 982813 = 368555) (by norm_num)
theorem B1310501 : Blo 872567 1310501 := bbase (se 4 (by rfl) ⟨122859, by rfl⟩ : syracuseStep 1310501 = 245719) (by norm_num)
theorem B1965869 : Blo 872567 1965869 := bbase (se 3 (by rfl) ⟨368600, by rfl⟩ : syracuseStep 1965869 = 737201) (by norm_num)
theorem B1310525 : Blo 872567 1310525 := bbase (se 3 (by rfl) ⟨245723, by rfl⟩ : syracuseStep 1310525 = 491447) (by norm_num)
theorem B982849 : Blo 872567 982849 := bbase (se 2 (by rfl) ⟨368568, by rfl⟩ : syracuseStep 982849 = 737137) (by norm_num)
theorem B1310549 : Blo 872567 1310549 := bbase (se 9 (by rfl) ⟨3839, by rfl⟩ : syracuseStep 1310549 = 7679) (by norm_num)
theorem B982885 : Blo 872567 982885 := bbase (se 4 (by rfl) ⟨92145, by rfl⟩ : syracuseStep 982885 = 184291) (by norm_num)
theorem B1703789 : Blo 872567 1703789 := bbase (se 3 (by rfl) ⟨319460, by rfl⟩ : syracuseStep 1703789 = 638921) (by norm_num)
theorem B1310573 : Blo 872567 1310573 := bbase (se 3 (by rfl) ⟨245732, by rfl⟩ : syracuseStep 1310573 = 491465) (by norm_num)
theorem B1965941 : Blo 872567 1965941 := bbase (se 5 (by rfl) ⟨92153, by rfl⟩ : syracuseStep 1965941 = 184307) (by norm_num)
theorem B1474429 : Blo 872567 1474429 := bbase (se 3 (by rfl) ⟨276455, by rfl⟩ : syracuseStep 1474429 = 552911) (by norm_num)
theorem B2097029 : Blo 872567 2097029 := bbase (se 4 (by rfl) ⟨196596, by rfl⟩ : syracuseStep 2097029 = 393193) (by norm_num)
theorem B1310597 : Blo 872567 1310597 := bbase (se 4 (by rfl) ⟨122868, by rfl⟩ : syracuseStep 1310597 = 245737) (by norm_num)
theorem B982921 : Blo 872567 982921 := bbase (se 2 (by rfl) ⟨368595, by rfl⟩ : syracuseStep 982921 = 737191) (by norm_num)
theorem B1310621 : Blo 872567 1310621 := bbase (se 3 (by rfl) ⟨245741, by rfl⟩ : syracuseStep 1310621 = 491483) (by norm_num)
theorem B982957 : Blo 872567 982957 := bbase (se 3 (by rfl) ⟨184304, by rfl⟩ : syracuseStep 982957 = 368609) (by norm_num)
theorem B1310645 : Blo 872567 1310645 := bbase (se 5 (by rfl) ⟨61436, by rfl⟩ : syracuseStep 1310645 = 122873) (by norm_num)
theorem B1966013 : Blo 872567 1966013 := bbase (se 3 (by rfl) ⟨368627, by rfl⟩ : syracuseStep 1966013 = 737255) (by norm_num)
theorem B1310669 : Blo 872567 1310669 := bbase (se 3 (by rfl) ⟨245750, by rfl⟩ : syracuseStep 1310669 = 491501) (by norm_num)
theorem B982993 : Blo 872567 982993 := bbase (se 2 (by rfl) ⟨368622, by rfl⟩ : syracuseStep 982993 = 737245) (by norm_num)
theorem B1474517 : Blo 872567 1474517 := bbase (se 7 (by rfl) ⟨17279, by rfl⟩ : syracuseStep 1474517 = 34559) (by norm_num)
theorem B1310693 : Blo 872567 1310693 := bbase (se 4 (by rfl) ⟨122877, by rfl⟩ : syracuseStep 1310693 = 245755) (by norm_num)
theorem B983029 : Blo 872567 983029 := bbase (se 5 (by rfl) ⟨46079, by rfl⟩ : syracuseStep 983029 = 92159) (by norm_num)
theorem B1310717 : Blo 872567 1310717 := bbase (se 3 (by rfl) ⟨245759, by rfl⟩ : syracuseStep 1310717 = 491519) (by norm_num)
theorem B1310723 : Blo 872567 1310723 := bstep (se 1 (by rfl) ⟨983042, by rfl⟩ : syracuseStep 1310723 = 1966085) B1966085
theorem B1310753 : Blo 872567 1310753 := bstep (se 2 (by rfl) ⟨491532, by rfl⟩ : syracuseStep 1310753 = 983065) B983065
theorem B2949155 : Blo 872567 2949155 := bstep (se 1 (by rfl) ⟨2211866, by rfl⟩ : syracuseStep 2949155 = 4423733) B4423733
theorem B1310771 : Blo 872567 1310771 := bstep (se 1 (by rfl) ⟨983078, by rfl⟩ : syracuseStep 1310771 = 1966157) B1966157
theorem B1245235 : Blo 872567 1245235 := bstep (se 1 (by rfl) ⟨933926, by rfl⟩ : syracuseStep 1245235 = 1867853) B1867853
theorem B1474625 : Blo 872567 1474625 := bstep (se 2 (by rfl) ⟨552984, by rfl⟩ : syracuseStep 1474625 = 1105969) B1105969
theorem B1310801 : Blo 872567 1310801 := bstep (se 2 (by rfl) ⟨491550, by rfl⟩ : syracuseStep 1310801 = 983101) B983101
theorem B1310819 : Blo 872567 1310819 := bstep (se 1 (by rfl) ⟨983114, by rfl⟩ : syracuseStep 1310819 = 1966229) B1966229
theorem B1966193 : Blo 872567 1966193 := bstep (se 2 (by rfl) ⟨737322, by rfl⟩ : syracuseStep 1966193 = 1474645) B1474645
theorem B983155 : Blo 872567 983155 := bstep (se 1 (by rfl) ⟨737366, by rfl⟩ : syracuseStep 983155 = 1474733) B1474733
theorem B1310849 : Blo 872567 1310849 := bstep (se 2 (by rfl) ⟨491568, by rfl⟩ : syracuseStep 1310849 = 983137) B983137
theorem B1966211 : Blo 872567 1966211 := bstep (se 1 (by rfl) ⟨1474658, by rfl⟩ : syracuseStep 1966211 = 2949317) B2949317
theorem B1310867 : Blo 872567 1310867 := bstep (se 1 (by rfl) ⟨983150, by rfl⟩ : syracuseStep 1310867 = 1966301) B1966301
theorem B1310897 : Blo 872567 1310897 := bstep (se 2 (by rfl) ⟨491586, by rfl⟩ : syracuseStep 1310897 = 983173) B983173
theorem B1474753 : Blo 872567 1474753 := bstep (se 2 (by rfl) ⟨553032, by rfl⟩ : syracuseStep 1474753 = 1106065) B1106065
theorem B1310915 : Blo 872567 1310915 := bstep (se 1 (by rfl) ⟨983186, by rfl⟩ : syracuseStep 1310915 = 1966373) B1966373
theorem B1310945 : Blo 872567 1310945 := bstep (se 2 (by rfl) ⟨491604, by rfl⟩ : syracuseStep 1310945 = 983209) B983209
theorem B1474787 : Blo 872567 1474787 := bstep (se 1 (by rfl) ⟨1106090, by rfl⟩ : syracuseStep 1474787 = 2212181) B2212181
theorem B1310963 : Blo 872567 1310963 := bstep (se 1 (by rfl) ⟨983222, by rfl⟩ : syracuseStep 1310963 = 1966445) B1966445
theorem B983299 : Blo 872567 983299 := bstep (se 1 (by rfl) ⟨737474, by rfl⟩ : syracuseStep 983299 = 1474949) B1474949
theorem B1310993 : Blo 872567 1310993 := bstep (se 2 (by rfl) ⟨491622, by rfl⟩ : syracuseStep 1310993 = 983245) B983245
theorem B1311011 : Blo 872567 1311011 := bstep (se 1 (by rfl) ⟨983258, by rfl⟩ : syracuseStep 1311011 = 1966517) B1966517
theorem B2949425 : Blo 872567 2949425 := bstep (se 2 (by rfl) ⟨1106034, by rfl⟩ : syracuseStep 2949425 = 2212069) B2212069
theorem B1311041 : Blo 872567 1311041 := bstep (se 2 (by rfl) ⟨491640, by rfl⟩ : syracuseStep 1311041 = 983281) B983281
theorem B1311059 : Blo 872567 1311059 := bstep (se 1 (by rfl) ⟨983294, by rfl⟩ : syracuseStep 1311059 = 1966589) B1966589
theorem B1474915 : Blo 872567 1474915 := bstep (se 1 (by rfl) ⟨1106186, by rfl⟩ : syracuseStep 1474915 = 2212373) B2212373
theorem B1311089 : Blo 872567 1311089 := bstep (se 2 (by rfl) ⟨491658, by rfl⟩ : syracuseStep 1311089 = 983317) B983317
theorem B2097539 : Blo 872567 2097539 := bstep (se 1 (by rfl) ⟨1573154, by rfl⟩ : syracuseStep 2097539 = 3146309) B3146309
theorem B1311107 : Blo 872567 1311107 := bstep (se 1 (by rfl) ⟨983330, by rfl⟩ : syracuseStep 1311107 = 1966661) B1966661
theorem B1966481 : Blo 872567 1966481 := bstep (se 2 (by rfl) ⟨737430, by rfl⟩ : syracuseStep 1966481 = 1474861) B1474861
theorem B983443 : Blo 872567 983443 := bstep (se 1 (by rfl) ⟨737582, by rfl⟩ : syracuseStep 983443 = 1475165) B1475165
theorem B1868177 : Blo 872567 1868177 := bstep (se 2 (by rfl) ⟨700566, by rfl⟩ : syracuseStep 1868177 = 1401133) B1401133
theorem B1311137 : Blo 872567 1311137 := bstep (se 2 (by rfl) ⟨491676, by rfl⟩ : syracuseStep 1311137 = 983353) B983353
theorem B1966499 : Blo 872567 1966499 := bstep (se 1 (by rfl) ⟨1474874, by rfl⟩ : syracuseStep 1966499 = 2949749) B2949749
theorem B1311155 : Blo 872567 1311155 := bstep (se 1 (by rfl) ⟨983366, by rfl⟩ : syracuseStep 1311155 = 1966733) B1966733
theorem B1311185 : Blo 872567 1311185 := bstep (se 2 (by rfl) ⟨491694, by rfl⟩ : syracuseStep 1311185 = 983389) B983389
theorem B4194787 : Blo 872567 4194787 := bstep (se 1 (by rfl) ⟨3146090, by rfl⟩ : syracuseStep 4194787 = 6292181) B6292181
theorem B1311203 : Blo 872567 1311203 := bstep (se 1 (by rfl) ⟨983402, by rfl⟩ : syracuseStep 1311203 = 1966805) B1966805
theorem B1475057 : Blo 872567 1475057 := bstep (se 2 (by rfl) ⟨553146, by rfl⟩ : syracuseStep 1475057 = 1106293) B1106293
theorem B1311233 : Blo 872567 1311233 := bstep (se 2 (by rfl) ⟨491712, by rfl⟩ : syracuseStep 1311233 = 983425) B983425
theorem B1311251 : Blo 872567 1311251 := bstep (se 1 (by rfl) ⟨983438, by rfl⟩ : syracuseStep 1311251 = 1966877) B1966877
theorem B983587 : Blo 872567 983587 := bstep (se 1 (by rfl) ⟨737690, by rfl⟩ : syracuseStep 983587 = 1475381) B1475381
theorem B2490925 : Blo 872567 2490925 := bstep (se 3 (by rfl) ⟨467048, by rfl⟩ : syracuseStep 2490925 = 934097) B934097
theorem B1311281 : Blo 872567 1311281 := bstep (se 2 (by rfl) ⟨491730, by rfl⟩ : syracuseStep 1311281 = 983461) B983461
theorem B1311299 : Blo 872567 1311299 := bstep (se 1 (by rfl) ⟨983474, by rfl⟩ : syracuseStep 1311299 = 1966949) B1966949
theorem B4719181 : Blo 872567 4719181 := bstep (se 3 (by rfl) ⟨884846, by rfl⟩ : syracuseStep 4719181 = 1769693) B1769693
theorem B1311329 : Blo 872567 1311329 := bstep (se 2 (by rfl) ⟨491748, by rfl⟩ : syracuseStep 1311329 = 983497) B983497
theorem B1245793 : Blo 872567 1245793 := bstep (se 2 (by rfl) ⟨467172, by rfl⟩ : syracuseStep 1245793 = 934345) B934345
theorem B1770083 : Blo 872567 1770083 := bstep (se 1 (by rfl) ⟨1327562, by rfl⟩ : syracuseStep 1770083 = 2655125) B2655125
theorem B1475185 : Blo 872567 1475185 := bstep (se 2 (by rfl) ⟨553194, by rfl⟩ : syracuseStep 1475185 = 1106389) B1106389
theorem B1311347 : Blo 872567 1311347 := bstep (se 1 (by rfl) ⟨983510, by rfl⟩ : syracuseStep 1311347 = 1967021) B1967021
theorem B1245827 : Blo 872567 1245827 := bstep (se 1 (by rfl) ⟨934370, by rfl⟩ : syracuseStep 1245827 = 1868741) B1868741
theorem B1311377 : Blo 872567 1311377 := bstep (se 2 (by rfl) ⟨491766, by rfl⟩ : syracuseStep 1311377 = 983533) B983533
theorem B1475219 : Blo 872567 1475219 := bstep (se 1 (by rfl) ⟨1106414, by rfl⟩ : syracuseStep 1475219 = 2212829) B2212829
theorem B1311395 : Blo 872567 1311395 := bstep (se 1 (by rfl) ⟨983546, by rfl⟩ : syracuseStep 1311395 = 1967093) B1967093
theorem B2654893 : Blo 872567 2654893 := bstep (se 3 (by rfl) ⟨497792, by rfl⟩ : syracuseStep 2654893 = 995585) B995585
theorem B1966769 : Blo 872567 1966769 := bstep (se 2 (by rfl) ⟨737538, by rfl⟩ : syracuseStep 1966769 = 1475077) B1475077
theorem B983731 : Blo 872567 983731 := bstep (se 1 (by rfl) ⟨737798, by rfl⟩ : syracuseStep 983731 = 1475597) B1475597
theorem B1311425 : Blo 872567 1311425 := bstep (se 2 (by rfl) ⟨491784, by rfl⟩ : syracuseStep 1311425 = 983569) B983569
theorem B1966787 : Blo 872567 1966787 := bstep (se 1 (by rfl) ⟨1475090, by rfl⟩ : syracuseStep 1966787 = 2950181) B2950181
theorem B1311443 : Blo 872567 1311443 := bstep (se 1 (by rfl) ⟨983582, by rfl⟩ : syracuseStep 1311443 = 1967165) B1967165
theorem B1311473 : Blo 872567 1311473 := bstep (se 2 (by rfl) ⟨491802, by rfl⟩ : syracuseStep 1311473 = 983605) B983605
theorem B1311491 : Blo 872567 1311491 := bstep (se 1 (by rfl) ⟨983618, by rfl⟩ : syracuseStep 1311491 = 1967237) B1967237
theorem B7471885 : Blo 872567 7471885 := bstep (se 3 (by rfl) ⟨1400978, by rfl⟩ : syracuseStep 7471885 = 2801957) B2801957
theorem B1475347 : Blo 872567 1475347 := bstep (se 1 (by rfl) ⟨1106510, by rfl⟩ : syracuseStep 1475347 = 2213021) B2213021
theorem B40862485 : Blo 872567 40862485 := bstep (se 6 (by rfl) ⟨957714, by rfl⟩ : syracuseStep 40862485 = 1915429) B1915429
theorem B1311521 : Blo 872567 1311521 := bstep (se 2 (by rfl) ⟨491820, by rfl⟩ : syracuseStep 1311521 = 983641) B983641
theorem B1868579 : Blo 872567 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B1311539 : Blo 872567 1311539 := bstep (se 1 (by rfl) ⟨983654, by rfl⟩ : syracuseStep 1311539 = 1967309) B1967309
theorem B983875 : Blo 872567 983875 := bstep (se 1 (by rfl) ⟨737906, by rfl⟩ : syracuseStep 983875 = 1475813) B1475813
theorem B2949965 : Blo 872567 2949965 := bstep (se 3 (by rfl) ⟨553118, by rfl⟩ : syracuseStep 2949965 = 1106237) B1106237
theorem B5604173 : Blo 872567 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B1311569 : Blo 872567 1311569 := bstep (se 2 (by rfl) ⟨491838, by rfl⟩ : syracuseStep 1311569 = 983677) B983677
theorem B1311587 : Blo 872567 1311587 := bstep (se 1 (by rfl) ⟨983690, by rfl⟩ : syracuseStep 1311587 = 1967381) B1967381
theorem B2360173 : Blo 872567 2360173 := bstep (se 3 (by rfl) ⟨442532, by rfl⟩ : syracuseStep 2360173 = 885065) B885065
theorem B1311617 : Blo 872567 1311617 := bstep (se 2 (by rfl) ⟨491856, by rfl⟩ : syracuseStep 1311617 = 983713) B983713
theorem B2950019 : Blo 872567 2950019 := bstep (se 1 (by rfl) ⟨2212514, by rfl⟩ : syracuseStep 2950019 = 4425029) B4425029
theorem B1311635 : Blo 872567 1311635 := bstep (se 1 (by rfl) ⟨983726, by rfl⟩ : syracuseStep 1311635 = 1967453) B1967453
theorem B1475489 : Blo 872567 1475489 := bstep (se 2 (by rfl) ⟨553308, by rfl⟩ : syracuseStep 1475489 = 1106617) B1106617
theorem B1311665 : Blo 872567 1311665 := bstep (se 2 (by rfl) ⟨491874, by rfl⟩ : syracuseStep 1311665 = 983749) B983749
theorem B1311683 : Blo 872567 1311683 := bstep (se 1 (by rfl) ⟨983762, by rfl⟩ : syracuseStep 1311683 = 1967525) B1967525
theorem B1967057 : Blo 872567 1967057 := bstep (se 2 (by rfl) ⟨737646, by rfl⟩ : syracuseStep 1967057 = 1475293) B1475293
theorem B984019 : Blo 872567 984019 := bstep (se 1 (by rfl) ⟨738014, by rfl⟩ : syracuseStep 984019 = 1476029) B1476029
theorem B1311713 : Blo 872567 1311713 := bstep (se 2 (by rfl) ⟨491892, by rfl⟩ : syracuseStep 1311713 = 983785) B983785
theorem B1967075 : Blo 872567 1967075 := bstep (se 1 (by rfl) ⟨1475306, by rfl⟩ : syracuseStep 1967075 = 2950613) B2950613
theorem B1311731 : Blo 872567 1311731 := bstep (se 1 (by rfl) ⟨983798, by rfl⟩ : syracuseStep 1311731 = 1967597) B1967597
theorem B1311761 : Blo 872567 1311761 := bstep (se 2 (by rfl) ⟨491910, by rfl⟩ : syracuseStep 1311761 = 983821) B983821
theorem B1475617 : Blo 872567 1475617 := bstep (se 2 (by rfl) ⟨553356, by rfl⟩ : syracuseStep 1475617 = 1106713) B1106713
theorem B1311779 : Blo 872567 1311779 := bstep (se 1 (by rfl) ⟨983834, by rfl⟩ : syracuseStep 1311779 = 1967669) B1967669
theorem B1311809 : Blo 872567 1311809 := bstep (se 2 (by rfl) ⟨491928, by rfl⟩ : syracuseStep 1311809 = 983857) B983857
theorem B1475651 : Blo 872567 1475651 := bstep (se 1 (by rfl) ⟨1106738, by rfl⟩ : syracuseStep 1475651 = 2213477) B2213477
theorem B1311827 : Blo 872567 1311827 := bstep (se 1 (by rfl) ⟨983870, by rfl⟩ : syracuseStep 1311827 = 1967741) B1967741
theorem B984163 : Blo 872567 984163 := bstep (se 1 (by rfl) ⟨738122, by rfl⟩ : syracuseStep 984163 = 1476245) B1476245
theorem B1311857 : Blo 872567 1311857 := bstep (se 2 (by rfl) ⟨491946, by rfl⟩ : syracuseStep 1311857 = 983893) B983893
theorem B1311875 : Blo 872567 1311875 := bstep (se 1 (by rfl) ⟨983906, by rfl⟩ : syracuseStep 1311875 = 1967813) B1967813
theorem B2950289 : Blo 872567 2950289 := bstep (se 2 (by rfl) ⟨1106358, by rfl⟩ : syracuseStep 2950289 = 2212717) B2212717
theorem B1311905 : Blo 872567 1311905 := bstep (se 2 (by rfl) ⟨491964, by rfl⟩ : syracuseStep 1311905 = 983929) B983929
theorem B3540131 : Blo 872567 3540131 := bstep (se 1 (by rfl) ⟨2655098, by rfl⟩ : syracuseStep 3540131 = 5310197) B5310197
theorem B4424867 : Blo 872567 4424867 := bstep (se 1 (by rfl) ⟨3318650, by rfl⟩ : syracuseStep 4424867 = 6637301) B6637301
theorem B4490417 : Blo 872567 4490417 := bstep (se 2 (by rfl) ⟨1683906, by rfl⟩ : syracuseStep 4490417 = 3367813) B3367813
theorem B1246385 : Blo 872567 1246385 := bstep (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) B934789
theorem B1311923 : Blo 872567 1311923 := bstep (se 1 (by rfl) ⟨983942, by rfl⟩ : syracuseStep 1311923 = 1967885) B1967885
theorem B1180865 : Blo 872567 1180865 := bstep (se 2 (by rfl) ⟨442824, by rfl⟩ : syracuseStep 1180865 = 885649) B885649
theorem B1574083 : Blo 872567 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B1475779 : Blo 872567 1475779 := bstep (se 1 (by rfl) ⟨1106834, by rfl⟩ : syracuseStep 1475779 = 2213669) B2213669
theorem B3146957 : Blo 872567 3146957 := bstep (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) B1180109
theorem B1311953 : Blo 872567 1311953 := bstep (se 2 (by rfl) ⟨491982, by rfl⟩ : syracuseStep 1311953 = 983965) B983965
theorem B1311971 : Blo 872567 1311971 := bstep (se 1 (by rfl) ⟨983978, by rfl⟩ : syracuseStep 1311971 = 1967957) B1967957
theorem B10650851 : Blo 872567 10650851 := bstep (se 1 (by rfl) ⟨7988138, by rfl⟩ : syracuseStep 10650851 = 15976277) B15976277
theorem B1967345 : Blo 872567 1967345 := bstep (se 2 (by rfl) ⟨737754, by rfl⟩ : syracuseStep 1967345 = 1475509) B1475509
theorem B984307 : Blo 872567 984307 := bstep (se 1 (by rfl) ⟨738230, by rfl⟩ : syracuseStep 984307 = 1476461) B1476461
theorem B1312001 : Blo 872567 1312001 := bstep (se 2 (by rfl) ⟨492000, by rfl⟩ : syracuseStep 1312001 = 984001) B984001
theorem B1246465 : Blo 872567 1246465 := bstep (se 2 (by rfl) ⟨467424, by rfl⟩ : syracuseStep 1246465 = 934849) B934849
theorem B1967363 : Blo 872567 1967363 := bstep (se 1 (by rfl) ⟨1475522, by rfl⟩ : syracuseStep 1967363 = 2951045) B2951045
theorem B1312019 : Blo 872567 1312019 := bstep (se 1 (by rfl) ⟨984014, by rfl⟩ : syracuseStep 1312019 = 1968029) B1968029
theorem B1180963 : Blo 872567 1180963 := bstep (se 1 (by rfl) ⟨885722, by rfl⟩ : syracuseStep 1180963 = 1771445) B1771445
theorem B1312049 : Blo 872567 1312049 := bstep (se 2 (by rfl) ⟨492018, by rfl⟩ : syracuseStep 1312049 = 984037) B984037
theorem B1312067 : Blo 872567 1312067 := bstep (se 1 (by rfl) ⟨984050, by rfl⟩ : syracuseStep 1312067 = 1968101) B1968101
theorem B1475921 : Blo 872567 1475921 := bstep (se 2 (by rfl) ⟨553470, by rfl⟩ : syracuseStep 1475921 = 1106941) B1106941
theorem B1312097 : Blo 872567 1312097 := bstep (se 2 (by rfl) ⟨492036, by rfl⟩ : syracuseStep 1312097 = 984073) B984073
theorem B1312115 : Blo 872567 1312115 := bstep (se 1 (by rfl) ⟨984086, by rfl⟩ : syracuseStep 1312115 = 1968173) B1968173
theorem B984451 : Blo 872567 984451 := bstep (se 1 (by rfl) ⟨738338, by rfl⟩ : syracuseStep 984451 = 1476677) B1476677
theorem B1312145 : Blo 872567 1312145 := bstep (se 2 (by rfl) ⟨492054, by rfl⟩ : syracuseStep 1312145 = 984109) B984109
theorem B1312163 : Blo 872567 1312163 := bstep (se 1 (by rfl) ⟨984122, by rfl⟩ : syracuseStep 1312163 = 1968245) B1968245
theorem B1312193 : Blo 872567 1312193 := bstep (se 2 (by rfl) ⟨492072, by rfl⟩ : syracuseStep 1312193 = 984145) B984145
theorem B1476049 : Blo 872567 1476049 := bstep (se 2 (by rfl) ⟨553518, by rfl⟩ : syracuseStep 1476049 = 1107037) B1107037
theorem B1312211 : Blo 872567 1312211 := bstep (se 1 (by rfl) ⟨984158, by rfl⟩ : syracuseStep 1312211 = 1968317) B1968317
theorem B1312241 : Blo 872567 1312241 := bstep (se 2 (by rfl) ⟨492090, by rfl⟩ : syracuseStep 1312241 = 984181) B984181
theorem B1476083 : Blo 872567 1476083 := bstep (se 1 (by rfl) ⟨1107062, by rfl⟩ : syracuseStep 1476083 = 2214125) B2214125
theorem B1312259 : Blo 872567 1312259 := bstep (se 1 (by rfl) ⟨984194, by rfl⟩ : syracuseStep 1312259 = 1968389) B1968389
theorem B1967633 : Blo 872567 1967633 := bstep (se 2 (by rfl) ⟨737862, by rfl⟩ : syracuseStep 1967633 = 1475725) B1475725
theorem B984595 : Blo 872567 984595 := bstep (se 1 (by rfl) ⟨738446, by rfl⟩ : syracuseStep 984595 = 1476893) B1476893
theorem B1312289 : Blo 872567 1312289 := bstep (se 2 (by rfl) ⟨492108, by rfl⟩ : syracuseStep 1312289 = 984217) B984217
theorem B1967651 : Blo 872567 1967651 := bstep (se 1 (by rfl) ⟨1475738, by rfl⟩ : syracuseStep 1967651 = 2951477) B2951477
theorem B1312307 : Blo 872567 1312307 := bstep (se 1 (by rfl) ⟨984230, by rfl⟩ : syracuseStep 1312307 = 1968461) B1968461
theorem B21268021 : Blo 872567 21268021 := bstep (se 5 (by rfl) ⟨996938, by rfl⟩ : syracuseStep 21268021 = 1993877) B1993877
theorem B886339 : Blo 872567 886339 := bstep (se 1 (by rfl) ⟨664754, by rfl⟩ : syracuseStep 886339 = 1329509) B1329509
theorem B1312337 : Blo 872567 1312337 := bstep (se 2 (by rfl) ⟨492126, by rfl⟩ : syracuseStep 1312337 = 984253) B984253
theorem B2491985 : Blo 872567 2491985 := bstep (se 2 (by rfl) ⟨934494, by rfl⟩ : syracuseStep 2491985 = 1868989) B1868989
theorem B1312355 : Blo 872567 1312355 := bstep (se 1 (by rfl) ⟨984266, by rfl⟩ : syracuseStep 1312355 = 1968533) B1968533
theorem B1771121 : Blo 872567 1771121 := bstep (se 2 (by rfl) ⟨664170, by rfl⟩ : syracuseStep 1771121 = 1328341) B1328341
theorem B36374129 : Blo 872567 36374129 := bstep (se 2 (by rfl) ⟨13640298, by rfl⟩ : syracuseStep 36374129 = 27280597) B27280597
theorem B1476211 : Blo 872567 1476211 := bstep (se 1 (by rfl) ⟨1107158, by rfl⟩ : syracuseStep 1476211 = 2214317) B2214317
theorem B1312385 : Blo 872567 1312385 := bstep (se 2 (by rfl) ⟨492144, by rfl⟩ : syracuseStep 1312385 = 984289) B984289
theorem B5113477 : Blo 872567 5113477 := bstep (se 4 (by rfl) ⟨479388, by rfl⟩ : syracuseStep 5113477 = 958777) B958777
theorem B1312403 : Blo 872567 1312403 := bstep (se 1 (by rfl) ⟨984302, by rfl⟩ : syracuseStep 1312403 = 1968605) B1968605
theorem B984739 : Blo 872567 984739 := bstep (se 1 (by rfl) ⟨738554, by rfl⟩ : syracuseStep 984739 = 1477109) B1477109
theorem B1869475 : Blo 872567 1869475 := bstep (se 1 (by rfl) ⟨1402106, by rfl⟩ : syracuseStep 1869475 = 2804213) B2804213
theorem B2950829 : Blo 872567 2950829 := bstep (se 3 (by rfl) ⟨553280, by rfl⟩ : syracuseStep 2950829 = 1106561) B1106561
theorem B1312433 : Blo 872567 1312433 := bstep (se 2 (by rfl) ⟨492162, by rfl⟩ : syracuseStep 1312433 = 984325) B984325
theorem B1312451 : Blo 872567 1312451 := bstep (se 1 (by rfl) ⟨984338, by rfl⟩ : syracuseStep 1312451 = 1968677) B1968677
theorem B1312481 : Blo 872567 1312481 := bstep (se 2 (by rfl) ⟨492180, by rfl⟩ : syracuseStep 1312481 = 984361) B984361
theorem B2950883 : Blo 872567 2950883 := bstep (se 1 (by rfl) ⟨2213162, by rfl⟩ : syracuseStep 2950883 = 4426325) B4426325
theorem B1312499 : Blo 872567 1312499 := bstep (se 1 (by rfl) ⟨984374, by rfl⟩ : syracuseStep 1312499 = 1968749) B1968749
theorem B1476353 : Blo 872567 1476353 := bstep (se 2 (by rfl) ⟨553632, by rfl⟩ : syracuseStep 1476353 = 1107265) B1107265
theorem B1312529 : Blo 872567 1312529 := bstep (se 2 (by rfl) ⟨492198, by rfl⟩ : syracuseStep 1312529 = 984397) B984397
theorem B1312547 : Blo 872567 1312547 := bstep (se 1 (by rfl) ⟨984410, by rfl⟩ : syracuseStep 1312547 = 1968821) B1968821
theorem B1967921 : Blo 872567 1967921 := bstep (se 2 (by rfl) ⟨737970, by rfl⟩ : syracuseStep 1967921 = 1475941) B1475941
theorem B984883 : Blo 872567 984883 := bstep (se 1 (by rfl) ⟨738662, by rfl⟩ : syracuseStep 984883 = 1477325) B1477325
theorem B1312577 : Blo 872567 1312577 := bstep (se 2 (by rfl) ⟨492216, by rfl⟩ : syracuseStep 1312577 = 984433) B984433
theorem B1967939 : Blo 872567 1967939 := bstep (se 1 (by rfl) ⟨1475954, by rfl⟩ : syracuseStep 1967939 = 2951909) B2951909
theorem B1312595 : Blo 872567 1312595 := bstep (se 1 (by rfl) ⟨984446, by rfl⟩ : syracuseStep 1312595 = 1968893) B1968893
theorem B1312625 : Blo 872567 1312625 := bstep (se 2 (by rfl) ⟨492234, by rfl⟩ : syracuseStep 1312625 = 984469) B984469
theorem B1476481 : Blo 872567 1476481 := bstep (se 2 (by rfl) ⟨553680, by rfl⟩ : syracuseStep 1476481 = 1107361) B1107361
theorem B1312643 : Blo 872567 1312643 := bstep (se 1 (by rfl) ⟨984482, by rfl⟩ : syracuseStep 1312643 = 1968965) B1968965
theorem B1312673 : Blo 872567 1312673 := bstep (se 2 (by rfl) ⟨492252, by rfl⟩ : syracuseStep 1312673 = 984505) B984505
theorem B1476515 : Blo 872567 1476515 := bstep (se 1 (by rfl) ⟨1107386, by rfl⟩ : syracuseStep 1476515 = 2214773) B2214773
theorem B1312691 : Blo 872567 1312691 := bstep (se 1 (by rfl) ⟨984518, by rfl⟩ : syracuseStep 1312691 = 1969037) B1969037
theorem B985027 : Blo 872567 985027 := bstep (se 1 (by rfl) ⟨738770, by rfl⟩ : syracuseStep 985027 = 1477541) B1477541
theorem B4425677 : Blo 872567 4425677 := bstep (se 3 (by rfl) ⟨829814, by rfl⟩ : syracuseStep 4425677 = 1659629) B1659629
theorem B1312721 : Blo 872567 1312721 := bstep (se 2 (by rfl) ⟨492270, by rfl⟩ : syracuseStep 1312721 = 984541) B984541
theorem B1312739 : Blo 872567 1312739 := bstep (se 1 (by rfl) ⟨984554, by rfl⟩ : syracuseStep 1312739 = 1969109) B1969109
theorem B2951153 : Blo 872567 2951153 := bstep (se 2 (by rfl) ⟨1106682, by rfl⟩ : syracuseStep 2951153 = 2213365) B2213365
theorem B1312769 : Blo 872567 1312769 := bstep (se 2 (by rfl) ⟨492288, by rfl⟩ : syracuseStep 1312769 = 984577) B984577
theorem B1312787 : Blo 872567 1312787 := bstep (se 1 (by rfl) ⟨984590, by rfl⟩ : syracuseStep 1312787 = 1969181) B1969181
theorem B1247251 : Blo 872567 1247251 := bstep (se 1 (by rfl) ⟨935438, by rfl⟩ : syracuseStep 1247251 = 1870877) B1870877
theorem B1476643 : Blo 872567 1476643 := bstep (se 1 (by rfl) ⟨1107482, by rfl⟩ : syracuseStep 1476643 = 2214965) B2214965
theorem B1312817 : Blo 872567 1312817 := bstep (se 2 (by rfl) ⟨492306, by rfl⟩ : syracuseStep 1312817 = 984613) B984613
theorem B1312835 : Blo 872567 1312835 := bstep (se 1 (by rfl) ⟨984626, by rfl⟩ : syracuseStep 1312835 = 1969253) B1969253
theorem B7473221 : Blo 872567 7473221 := bstep (se 4 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 7473221 = 1401229) B1401229
theorem B1968209 : Blo 872567 1968209 := bstep (se 2 (by rfl) ⟨738078, by rfl⟩ : syracuseStep 1968209 = 1476157) B1476157
theorem B985171 : Blo 872567 985171 := bstep (se 1 (by rfl) ⟨738878, by rfl⟩ : syracuseStep 985171 = 1477757) B1477757
theorem B1312865 : Blo 872567 1312865 := bstep (se 2 (by rfl) ⟨492324, by rfl⟩ : syracuseStep 1312865 = 984649) B984649
theorem B1968227 : Blo 872567 1968227 := bstep (se 1 (by rfl) ⟨1476170, by rfl⟩ : syracuseStep 1968227 = 2952341) B2952341
theorem B4982897 : Blo 872567 4982897 := bstep (se 2 (by rfl) ⟨1868586, by rfl⟩ : syracuseStep 4982897 = 3737173) B3737173
theorem B1312883 : Blo 872567 1312883 := bstep (se 1 (by rfl) ⟨984662, by rfl⟩ : syracuseStep 1312883 = 1969325) B1969325
theorem B1312913 : Blo 872567 1312913 := bstep (se 2 (by rfl) ⟨492342, by rfl⟩ : syracuseStep 1312913 = 984685) B984685
theorem B1312931 : Blo 872567 1312931 := bstep (se 1 (by rfl) ⟨984698, by rfl⟩ : syracuseStep 1312931 = 1969397) B1969397
theorem B1476785 : Blo 872567 1476785 := bstep (se 2 (by rfl) ⟨553794, by rfl⟩ : syracuseStep 1476785 = 1107589) B1107589
theorem B1312961 : Blo 872567 1312961 := bstep (se 2 (by rfl) ⟨492360, by rfl⟩ : syracuseStep 1312961 = 984721) B984721
theorem B1312979 : Blo 872567 1312979 := bstep (se 1 (by rfl) ⟨984734, by rfl⟩ : syracuseStep 1312979 = 1969469) B1969469
theorem B985315 : Blo 872567 985315 := bstep (se 1 (by rfl) ⟨738986, by rfl⟩ : syracuseStep 985315 = 1477973) B1477973
theorem B2492657 : Blo 872567 2492657 := bstep (se 2 (by rfl) ⟨934746, by rfl⟩ : syracuseStep 2492657 = 1869493) B1869493
theorem B1313009 : Blo 872567 1313009 := bstep (se 2 (by rfl) ⟨492378, by rfl⟩ : syracuseStep 1313009 = 984757) B984757
theorem B1313027 : Blo 872567 1313027 := bstep (se 1 (by rfl) ⟨984770, by rfl⟩ : syracuseStep 1313027 = 1969541) B1969541
theorem B1313057 : Blo 872567 1313057 := bstep (se 2 (by rfl) ⟨492396, by rfl⟩ : syracuseStep 1313057 = 984793) B984793
theorem B1476913 : Blo 872567 1476913 := bstep (se 2 (by rfl) ⟨553842, by rfl⟩ : syracuseStep 1476913 = 1107685) B1107685
theorem B1313075 : Blo 872567 1313075 := bstep (se 1 (by rfl) ⟨984806, by rfl⟩ : syracuseStep 1313075 = 1969613) B1969613
theorem B1313105 : Blo 872567 1313105 := bstep (se 2 (by rfl) ⟨492414, by rfl⟩ : syracuseStep 1313105 = 984829) B984829
theorem B1476947 : Blo 872567 1476947 := bstep (se 1 (by rfl) ⟨1107710, by rfl⟩ : syracuseStep 1476947 = 2215421) B2215421
theorem B5048675 : Blo 872567 5048675 := bstep (se 1 (by rfl) ⟨3786506, by rfl⟩ : syracuseStep 5048675 = 7573013) B7573013
theorem B1313123 : Blo 872567 1313123 := bstep (se 1 (by rfl) ⟨984842, by rfl⟩ : syracuseStep 1313123 = 1969685) B1969685
theorem B1968497 : Blo 872567 1968497 := bstep (se 2 (by rfl) ⟨738186, by rfl⟩ : syracuseStep 1968497 = 1476373) B1476373
theorem B985459 : Blo 872567 985459 := bstep (se 1 (by rfl) ⟨739094, by rfl⟩ : syracuseStep 985459 = 1478189) B1478189
theorem B1345921 : Blo 872567 1345921 := bstep (se 2 (by rfl) ⟨504720, by rfl⟩ : syracuseStep 1345921 = 1009441) B1009441
theorem B1313153 : Blo 872567 1313153 := bstep (se 2 (by rfl) ⟨492432, by rfl⟩ : syracuseStep 1313153 = 984865) B984865
theorem B1968515 : Blo 872567 1968515 := bstep (se 1 (by rfl) ⟨1476386, by rfl⟩ : syracuseStep 1968515 = 2952773) B2952773
theorem B1313171 : Blo 872567 1313171 := bstep (se 1 (by rfl) ⟨984878, by rfl⟩ : syracuseStep 1313171 = 1969757) B1969757
theorem B887203 : Blo 872567 887203 := bstep (se 1 (by rfl) ⟨665402, by rfl⟩ : syracuseStep 887203 = 1330805) B1330805
theorem B4196785 : Blo 872567 4196785 := bstep (se 2 (by rfl) ⟨1573794, by rfl⟩ : syracuseStep 4196785 = 3147589) B3147589
theorem B1313201 : Blo 872567 1313201 := bstep (se 2 (by rfl) ⟨492450, by rfl⟩ : syracuseStep 1313201 = 984901) B984901
theorem B1313219 : Blo 872567 1313219 := bstep (se 1 (by rfl) ⟨984914, by rfl⟩ : syracuseStep 1313219 = 1969829) B1969829
theorem B8391109 : Blo 872567 8391109 := bstep (se 4 (by rfl) ⟨786666, by rfl⟩ : syracuseStep 8391109 = 1573333) B1573333
theorem B1477075 : Blo 872567 1477075 := bstep (se 1 (by rfl) ⟨1107806, by rfl⟩ : syracuseStep 1477075 = 2215613) B2215613
theorem B1313249 : Blo 872567 1313249 := bstep (se 2 (by rfl) ⟨492468, by rfl⟩ : syracuseStep 1313249 = 984937) B984937
theorem B1247729 : Blo 872567 1247729 := bstep (se 2 (by rfl) ⟨467898, by rfl⟩ : syracuseStep 1247729 = 935797) B935797
theorem B1313267 : Blo 872567 1313267 := bstep (se 1 (by rfl) ⟨984950, by rfl⟩ : syracuseStep 1313267 = 1969901) B1969901
theorem B985603 : Blo 872567 985603 := bstep (se 1 (by rfl) ⟨739202, by rfl⟩ : syracuseStep 985603 = 1478405) B1478405
theorem B2951693 : Blo 872567 2951693 := bstep (se 3 (by rfl) ⟨553442, by rfl⟩ : syracuseStep 2951693 = 1106885) B1106885
theorem B1313297 : Blo 872567 1313297 := bstep (se 2 (by rfl) ⟨492486, by rfl⟩ : syracuseStep 1313297 = 984973) B984973
theorem B1313315 : Blo 872567 1313315 := bstep (se 1 (by rfl) ⟨984986, by rfl⟩ : syracuseStep 1313315 = 1969973) B1969973
theorem B1313345 : Blo 872567 1313345 := bstep (se 2 (by rfl) ⟨492504, by rfl⟩ : syracuseStep 1313345 = 985009) B985009
theorem B2951747 : Blo 872567 2951747 := bstep (se 1 (by rfl) ⟨2213810, by rfl⟩ : syracuseStep 2951747 = 4427621) B4427621
theorem B1313363 : Blo 872567 1313363 := bstep (se 1 (by rfl) ⟨985022, by rfl⟩ : syracuseStep 1313363 = 1970045) B1970045
theorem B1477217 : Blo 872567 1477217 := bstep (se 2 (by rfl) ⟨553956, by rfl⟩ : syracuseStep 1477217 = 1107913) B1107913
theorem B1247843 : Blo 872567 1247843 := bstep (se 1 (by rfl) ⟨935882, by rfl⟩ : syracuseStep 1247843 = 1871765) B1871765
theorem B1313393 : Blo 872567 1313393 := bstep (se 2 (by rfl) ⟨492522, by rfl⟩ : syracuseStep 1313393 = 985045) B985045
theorem B1313411 : Blo 872567 1313411 := bstep (se 1 (by rfl) ⟨985058, by rfl⟩ : syracuseStep 1313411 = 1970117) B1970117
theorem B1968785 : Blo 872567 1968785 := bstep (se 2 (by rfl) ⟨738294, by rfl⟩ : syracuseStep 1968785 = 1476589) B1476589
theorem B985747 : Blo 872567 985747 := bstep (se 1 (by rfl) ⟨739310, by rfl⟩ : syracuseStep 985747 = 1478621) B1478621
theorem B1313441 : Blo 872567 1313441 := bstep (se 2 (by rfl) ⟨492540, by rfl⟩ : syracuseStep 1313441 = 985081) B985081
theorem B1968803 : Blo 872567 1968803 := bstep (se 1 (by rfl) ⟨1476602, by rfl⟩ : syracuseStep 1968803 = 2953205) B2953205
theorem B1313459 : Blo 872567 1313459 := bstep (se 1 (by rfl) ⟨985094, by rfl⟩ : syracuseStep 1313459 = 1970189) B1970189
theorem B1247923 : Blo 872567 1247923 := bstep (se 1 (by rfl) ⟨935942, by rfl⟩ : syracuseStep 1247923 = 1871885) B1871885
theorem B1313489 : Blo 872567 1313489 := bstep (se 2 (by rfl) ⟨492558, by rfl⟩ : syracuseStep 1313489 = 985117) B985117
theorem B1477345 : Blo 872567 1477345 := bstep (se 2 (by rfl) ⟨554004, by rfl⟩ : syracuseStep 1477345 = 1108009) B1108009
theorem B1313507 : Blo 872567 1313507 := bstep (se 1 (by rfl) ⟨985130, by rfl⟩ : syracuseStep 1313507 = 1970261) B1970261
theorem B1313537 : Blo 872567 1313537 := bstep (se 2 (by rfl) ⟨492576, by rfl⟩ : syracuseStep 1313537 = 985153) B985153
theorem B1477379 : Blo 872567 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B1313555 : Blo 872567 1313555 := bstep (se 1 (by rfl) ⟨985166, by rfl⟩ : syracuseStep 1313555 = 1970333) B1970333
theorem B3738403 : Blo 872567 3738403 := bstep (se 1 (by rfl) ⟨2803802, by rfl⟩ : syracuseStep 3738403 = 5607605) B5607605
theorem B985891 : Blo 872567 985891 := bstep (se 1 (by rfl) ⟨739418, by rfl⟩ : syracuseStep 985891 = 1478837) B1478837
theorem B1313585 : Blo 872567 1313585 := bstep (se 2 (by rfl) ⟨492594, by rfl⟩ : syracuseStep 1313585 = 985189) B985189
theorem B1313603 : Blo 872567 1313603 := bstep (se 1 (by rfl) ⟨985202, by rfl⟩ : syracuseStep 1313603 = 1970405) B1970405
theorem B2952017 : Blo 872567 2952017 := bstep (se 2 (by rfl) ⟨1107006, by rfl⟩ : syracuseStep 2952017 = 2214013) B2214013
theorem B1313633 : Blo 872567 1313633 := bstep (se 2 (by rfl) ⟨492612, by rfl⟩ : syracuseStep 1313633 = 985225) B985225
theorem B1870705 : Blo 872567 1870705 := bstep (se 2 (by rfl) ⟨701514, by rfl⟩ : syracuseStep 1870705 = 1403029) B1403029
theorem B1313651 : Blo 872567 1313651 := bstep (se 1 (by rfl) ⟨985238, by rfl⟩ : syracuseStep 1313651 = 1970477) B1970477
theorem B1477507 : Blo 872567 1477507 := bstep (se 1 (by rfl) ⟨1108130, by rfl⟩ : syracuseStep 1477507 = 2216261) B2216261
theorem B1313681 : Blo 872567 1313681 := bstep (se 2 (by rfl) ⟨492630, by rfl⟩ : syracuseStep 1313681 = 985261) B985261
theorem B1313699 : Blo 872567 1313699 := bstep (se 1 (by rfl) ⟨985274, by rfl⟩ : syracuseStep 1313699 = 1970549) B1970549
theorem B1969073 : Blo 872567 1969073 := bstep (se 2 (by rfl) ⟨738402, by rfl⟩ : syracuseStep 1969073 = 1476805) B1476805
theorem B986035 : Blo 872567 986035 := bstep (se 1 (by rfl) ⟨739526, by rfl⟩ : syracuseStep 986035 = 1479053) B1479053
theorem B1313729 : Blo 872567 1313729 := bstep (se 2 (by rfl) ⟨492648, by rfl⟩ : syracuseStep 1313729 = 985297) B985297
theorem B1969091 : Blo 872567 1969091 := bstep (se 1 (by rfl) ⟨1476818, by rfl⟩ : syracuseStep 1969091 = 2953637) B2953637
theorem B1313747 : Blo 872567 1313747 := bstep (se 1 (by rfl) ⟨985310, by rfl⟩ : syracuseStep 1313747 = 1970621) B1970621
theorem B1313777 : Blo 872567 1313777 := bstep (se 2 (by rfl) ⟨492666, by rfl⟩ : syracuseStep 1313777 = 985333) B985333
theorem B2493443 : Blo 872567 2493443 := bstep (se 1 (by rfl) ⟨1870082, by rfl⟩ : syracuseStep 2493443 = 3740165) B3740165
theorem B1313795 : Blo 872567 1313795 := bstep (se 1 (by rfl) ⟨985346, by rfl⟩ : syracuseStep 1313795 = 1970693) B1970693
theorem B1477649 : Blo 872567 1477649 := bstep (se 2 (by rfl) ⟨554118, by rfl⟩ : syracuseStep 1477649 = 1108237) B1108237
theorem B1313825 : Blo 872567 1313825 := bstep (se 2 (by rfl) ⟨492684, by rfl⟩ : syracuseStep 1313825 = 985369) B985369
theorem B1313843 : Blo 872567 1313843 := bstep (se 1 (by rfl) ⟨985382, by rfl⟩ : syracuseStep 1313843 = 1970765) B1970765
theorem B1313873 : Blo 872567 1313873 := bstep (se 2 (by rfl) ⟨492702, by rfl⟩ : syracuseStep 1313873 = 985405) B985405
theorem B1313891 : Blo 872567 1313891 := bstep (se 1 (by rfl) ⟨985418, by rfl⟩ : syracuseStep 1313891 = 1970837) B1970837
theorem B1313921 : Blo 872567 1313921 := bstep (se 2 (by rfl) ⟨492720, by rfl⟩ : syracuseStep 1313921 = 985441) B985441
theorem B1477777 : Blo 872567 1477777 := bstep (se 2 (by rfl) ⟨554166, by rfl⟩ : syracuseStep 1477777 = 1108333) B1108333
theorem B1313939 : Blo 872567 1313939 := bstep (se 1 (by rfl) ⟨985454, by rfl⟩ : syracuseStep 1313939 = 1970909) B1970909
theorem B1313969 : Blo 872567 1313969 := bstep (se 2 (by rfl) ⟨492738, by rfl⟩ : syracuseStep 1313969 = 985477) B985477
theorem B1477811 : Blo 872567 1477811 := bstep (se 1 (by rfl) ⟨1108358, by rfl⟩ : syracuseStep 1477811 = 2216717) B2216717
theorem B1313987 : Blo 872567 1313987 := bstep (se 1 (by rfl) ⟨985490, by rfl⟩ : syracuseStep 1313987 = 1970981) B1970981
theorem B1969361 : Blo 872567 1969361 := bstep (se 2 (by rfl) ⟨738510, by rfl⟩ : syracuseStep 1969361 = 1477021) B1477021
theorem B1314017 : Blo 872567 1314017 := bstep (se 2 (by rfl) ⟨492756, by rfl⟩ : syracuseStep 1314017 = 985513) B985513
theorem B1969379 : Blo 872567 1969379 := bstep (se 1 (by rfl) ⟨1477034, by rfl⟩ : syracuseStep 1969379 = 2954069) B2954069
theorem B1314035 : Blo 872567 1314035 := bstep (se 1 (by rfl) ⟨985526, by rfl⟩ : syracuseStep 1314035 = 1971053) B1971053
theorem B2985233 : Blo 872567 2985233 := bstep (se 2 (by rfl) ⟨1119462, by rfl⟩ : syracuseStep 2985233 = 2238925) B2238925
theorem B1314065 : Blo 872567 1314065 := bstep (se 2 (by rfl) ⟨492774, by rfl⟩ : syracuseStep 1314065 = 985549) B985549
theorem B1314083 : Blo 872567 1314083 := bstep (se 1 (by rfl) ⟨985562, by rfl⟩ : syracuseStep 1314083 = 1971125) B1971125
theorem B1772849 : Blo 872567 1772849 := bstep (se 2 (by rfl) ⟨664818, by rfl⟩ : syracuseStep 1772849 = 1329637) B1329637
theorem B1477939 : Blo 872567 1477939 := bstep (se 1 (by rfl) ⟨1108454, by rfl⟩ : syracuseStep 1477939 = 2216909) B2216909
theorem B1314113 : Blo 872567 1314113 := bstep (se 2 (by rfl) ⟨492792, by rfl⟩ : syracuseStep 1314113 = 985585) B985585
theorem B2493773 : Blo 872567 2493773 := bstep (se 3 (by rfl) ⟨467582, by rfl⟩ : syracuseStep 2493773 = 935165) B935165
theorem B1314131 : Blo 872567 1314131 := bstep (se 1 (by rfl) ⟨985598, by rfl⟩ : syracuseStep 1314131 = 1971197) B1971197
theorem B2952557 : Blo 872567 2952557 := bstep (se 3 (by rfl) ⟨553604, by rfl⟩ : syracuseStep 2952557 = 1107209) B1107209
theorem B1314161 : Blo 872567 1314161 := bstep (se 2 (by rfl) ⟨492810, by rfl⟩ : syracuseStep 1314161 = 985621) B985621
theorem B888179 : Blo 872567 888179 := bstep (se 1 (by rfl) ⟨666134, by rfl⟩ : syracuseStep 888179 = 1332269) B1332269
theorem B1314179 : Blo 872567 1314179 := bstep (se 1 (by rfl) ⟨985634, by rfl⟩ : syracuseStep 1314179 = 1971269) B1971269
theorem B2493841 : Blo 872567 2493841 := bstep (se 2 (by rfl) ⟨935190, by rfl⟩ : syracuseStep 2493841 = 1870381) B1870381
theorem B1314209 : Blo 872567 1314209 := bstep (se 2 (by rfl) ⟨492828, by rfl⟩ : syracuseStep 1314209 = 985657) B985657
theorem B2952611 : Blo 872567 2952611 := bstep (se 1 (by rfl) ⟨2214458, by rfl⟩ : syracuseStep 2952611 = 4428917) B4428917
theorem B1314227 : Blo 872567 1314227 := bstep (se 1 (by rfl) ⟨985670, by rfl⟩ : syracuseStep 1314227 = 1971341) B1971341
theorem B1478081 : Blo 872567 1478081 := bstep (se 2 (by rfl) ⟨554280, by rfl⟩ : syracuseStep 1478081 = 1108561) B1108561
theorem B1314257 : Blo 872567 1314257 := bstep (se 2 (by rfl) ⟨492846, by rfl⟩ : syracuseStep 1314257 = 985693) B985693
theorem B1314275 : Blo 872567 1314275 := bstep (se 1 (by rfl) ⟨985706, by rfl⟩ : syracuseStep 1314275 = 1971413) B1971413
theorem B1969649 : Blo 872567 1969649 := bstep (se 2 (by rfl) ⟨738618, by rfl⟩ : syracuseStep 1969649 = 1477237) B1477237
theorem B1314305 : Blo 872567 1314305 := bstep (se 2 (by rfl) ⟨492864, by rfl⟩ : syracuseStep 1314305 = 985729) B985729
theorem B1969667 : Blo 872567 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B4197901 : Blo 872567 4197901 := bstep (se 3 (by rfl) ⟨787106, by rfl⟩ : syracuseStep 4197901 = 1574213) B1574213
theorem B1314323 : Blo 872567 1314323 := bstep (se 1 (by rfl) ⟨985742, by rfl⟩ : syracuseStep 1314323 = 1971485) B1971485
theorem B4984355 : Blo 872567 4984355 := bstep (se 1 (by rfl) ⟨3738266, by rfl⟩ : syracuseStep 4984355 = 7476533) B7476533
theorem B1052195 : Blo 872567 1052195 := bstep (se 1 (by rfl) ⟨789146, by rfl⟩ : syracuseStep 1052195 = 1578293) B1578293
theorem B1314353 : Blo 872567 1314353 := bstep (se 2 (by rfl) ⟨492882, by rfl⟩ : syracuseStep 1314353 = 985765) B985765
theorem B1478209 : Blo 872567 1478209 := bstep (se 2 (by rfl) ⟨554328, by rfl⟩ : syracuseStep 1478209 = 1108657) B1108657
theorem B1314371 : Blo 872567 1314371 := bstep (se 1 (by rfl) ⟨985778, by rfl⟩ : syracuseStep 1314371 = 1971557) B1971557
theorem B1314401 : Blo 872567 1314401 := bstep (se 2 (by rfl) ⟨492900, by rfl⟩ : syracuseStep 1314401 = 985801) B985801
theorem B1478243 : Blo 872567 1478243 := bstep (se 1 (by rfl) ⟨1108682, by rfl⟩ : syracuseStep 1478243 = 2217365) B2217365
theorem B1314419 : Blo 872567 1314419 := bstep (se 1 (by rfl) ⟨985814, by rfl⟩ : syracuseStep 1314419 = 1971629) B1971629
theorem B1314449 : Blo 872567 1314449 := bstep (se 2 (by rfl) ⟨492918, by rfl⟩ : syracuseStep 1314449 = 985837) B985837
theorem B2494115 : Blo 872567 2494115 := bstep (se 1 (by rfl) ⟨1870586, by rfl⟩ : syracuseStep 2494115 = 3741173) B3741173
theorem B1314467 : Blo 872567 1314467 := bstep (se 1 (by rfl) ⟨985850, by rfl⟩ : syracuseStep 1314467 = 1971701) B1971701
theorem B2952881 : Blo 872567 2952881 := bstep (se 2 (by rfl) ⟨1107330, by rfl⟩ : syracuseStep 2952881 = 2214661) B2214661
theorem B1314497 : Blo 872567 1314497 := bstep (se 2 (by rfl) ⟨492936, by rfl⟩ : syracuseStep 1314497 = 985873) B985873
theorem B1314515 : Blo 872567 1314515 := bstep (se 1 (by rfl) ⟨985886, by rfl⟩ : syracuseStep 1314515 = 1971773) B1971773
theorem B1478371 : Blo 872567 1478371 := bstep (se 1 (by rfl) ⟨1108778, by rfl⟩ : syracuseStep 1478371 = 2217557) B2217557
theorem B1314545 : Blo 872567 1314545 := bstep (se 2 (by rfl) ⟨492954, by rfl⟩ : syracuseStep 1314545 = 985909) B985909
theorem B1314563 : Blo 872567 1314563 := bstep (se 1 (by rfl) ⟨985922, by rfl⟩ : syracuseStep 1314563 = 1971845) B1971845
theorem B1969937 : Blo 872567 1969937 := bstep (se 2 (by rfl) ⟨738726, by rfl⟩ : syracuseStep 1969937 = 1477453) B1477453
theorem B1314593 : Blo 872567 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B1969955 : Blo 872567 1969955 := bstep (se 1 (by rfl) ⟨1477466, by rfl⟩ : syracuseStep 1969955 = 2954933) B2954933
theorem B3313457 : Blo 872567 3313457 := bstep (se 2 (by rfl) ⟨1242546, by rfl⟩ : syracuseStep 3313457 = 2485093) B2485093
theorem B1314611 : Blo 872567 1314611 := bstep (se 1 (by rfl) ⟨985958, by rfl⟩ : syracuseStep 1314611 = 1971917) B1971917
theorem B1314641 : Blo 872567 1314641 := bstep (se 2 (by rfl) ⟨492990, by rfl⟩ : syracuseStep 1314641 = 985981) B985981
theorem B1314659 : Blo 872567 1314659 := bstep (se 1 (by rfl) ⟨985994, by rfl⟩ : syracuseStep 1314659 = 1971989) B1971989
theorem B1478513 : Blo 872567 1478513 := bstep (se 2 (by rfl) ⟨554442, by rfl⟩ : syracuseStep 1478513 = 1108885) B1108885
theorem B1314689 : Blo 872567 1314689 := bstep (se 2 (by rfl) ⟨493008, by rfl⟩ : syracuseStep 1314689 = 986017) B986017
theorem B1314707 : Blo 872567 1314707 := bstep (se 1 (by rfl) ⟨986030, by rfl⟩ : syracuseStep 1314707 = 1972061) B1972061
theorem B1314737 : Blo 872567 1314737 := bstep (se 2 (by rfl) ⟨493026, by rfl⟩ : syracuseStep 1314737 = 986053) B986053
theorem B1314755 : Blo 872567 1314755 := bstep (se 1 (by rfl) ⟨986066, by rfl⟩ : syracuseStep 1314755 = 1972133) B1972133
theorem B1314785 : Blo 872567 1314785 := bstep (se 2 (by rfl) ⟨493044, by rfl⟩ : syracuseStep 1314785 = 986089) B986089
theorem B1478641 : Blo 872567 1478641 := bstep (se 2 (by rfl) ⟨554490, by rfl⟩ : syracuseStep 1478641 = 1108981) B1108981
theorem B1314803 : Blo 872567 1314803 := bstep (se 1 (by rfl) ⟨986102, by rfl⟩ : syracuseStep 1314803 = 1972205) B1972205
theorem B1314833 : Blo 872567 1314833 := bstep (se 2 (by rfl) ⟨493062, by rfl⟩ : syracuseStep 1314833 = 986125) B986125
theorem B1478675 : Blo 872567 1478675 := bstep (se 1 (by rfl) ⟨1109006, by rfl⟩ : syracuseStep 1478675 = 2218013) B2218013
theorem B1314851 : Blo 872567 1314851 := bstep (se 1 (by rfl) ⟨986138, by rfl⟩ : syracuseStep 1314851 = 1972277) B1972277
theorem B1970225 : Blo 872567 1970225 := bstep (se 2 (by rfl) ⟨738834, by rfl⟩ : syracuseStep 1970225 = 1477669) B1477669
theorem B2101315 : Blo 872567 2101315 := bstep (se 1 (by rfl) ⟨1575986, by rfl⟩ : syracuseStep 2101315 = 3151973) B3151973
theorem B1970243 : Blo 872567 1970243 := bstep (se 1 (by rfl) ⟨1477682, by rfl⟩ : syracuseStep 1970243 = 2955365) B2955365
theorem B1478803 : Blo 872567 1478803 := bstep (se 1 (by rfl) ⟨1109102, by rfl⟩ : syracuseStep 1478803 = 2218205) B2218205
theorem B2101411 : Blo 872567 2101411 := bstep (se 1 (by rfl) ⟨1576058, by rfl⟩ : syracuseStep 2101411 = 3152117) B3152117
theorem B2953421 : Blo 872567 2953421 := bstep (se 3 (by rfl) ⟨553766, by rfl⟩ : syracuseStep 2953421 = 1107533) B1107533
theorem B2953475 : Blo 872567 2953475 := bstep (se 1 (by rfl) ⟨2215106, by rfl⟩ : syracuseStep 2953475 = 4430213) B4430213
theorem B1478945 : Blo 872567 1478945 := bstep (se 2 (by rfl) ⟨554604, by rfl⟩ : syracuseStep 1478945 = 1109209) B1109209
theorem B3543373 : Blo 872567 3543373 := bstep (se 3 (by rfl) ⟨664382, by rfl⟩ : syracuseStep 3543373 = 1328765) B1328765
theorem B1970513 : Blo 872567 1970513 := bstep (se 2 (by rfl) ⟨738942, by rfl⟩ : syracuseStep 1970513 = 1477885) B1477885
theorem B1970531 : Blo 872567 1970531 := bstep (se 1 (by rfl) ⟨1477898, by rfl⟩ : syracuseStep 1970531 = 2955797) B2955797
theorem B1479073 : Blo 872567 1479073 := bstep (se 2 (by rfl) ⟨554652, by rfl⟩ : syracuseStep 1479073 = 1109305) B1109305
theorem B1479107 : Blo 872567 1479107 := bstep (se 1 (by rfl) ⟨1109330, by rfl⟩ : syracuseStep 1479107 = 2218661) B2218661
theorem B2494957 : Blo 872567 2494957 := bstep (se 3 (by rfl) ⟨467804, by rfl⟩ : syracuseStep 2494957 = 935609) B935609
theorem B2953745 : Blo 872567 2953745 := bstep (se 2 (by rfl) ⟨1107654, by rfl⟩ : syracuseStep 2953745 = 2215309) B2215309
theorem B1184321 : Blo 872567 1184321 := bstep (se 2 (by rfl) ⟨444120, by rfl⟩ : syracuseStep 1184321 = 888241) B888241
theorem B1348177 : Blo 872567 1348177 := bstep (se 2 (by rfl) ⟨505566, by rfl⟩ : syracuseStep 1348177 = 1011133) B1011133
theorem B1970801 : Blo 872567 1970801 := bstep (se 2 (by rfl) ⟨739050, by rfl⟩ : syracuseStep 1970801 = 1478101) B1478101
theorem B1970819 : Blo 872567 1970819 := bstep (se 1 (by rfl) ⟨1478114, by rfl⟩ : syracuseStep 1970819 = 2956229) B2956229
theorem B2495117 : Blo 872567 2495117 := bstep (se 3 (by rfl) ⟨467834, by rfl⟩ : syracuseStep 2495117 = 935669) B935669
theorem B6296305 : Blo 872567 6296305 := bstep (se 2 (by rfl) ⟨2361114, by rfl⟩ : syracuseStep 6296305 = 4722229) B4722229
theorem B4428593 : Blo 872567 4428593 := bstep (se 2 (by rfl) ⟨1660722, by rfl⟩ : syracuseStep 4428593 = 3321445) B3321445
theorem B2495299 : Blo 872567 2495299 := bstep (se 1 (by rfl) ⟨1871474, by rfl⟩ : syracuseStep 2495299 = 3742949) B3742949
theorem B3150733 : Blo 872567 3150733 := bstep (se 3 (by rfl) ⟨590762, by rfl⟩ : syracuseStep 3150733 = 1181525) B1181525
theorem B1971089 : Blo 872567 1971089 := bstep (se 2 (by rfl) ⟨739158, by rfl⟩ : syracuseStep 1971089 = 1478317) B1478317
theorem B1971107 : Blo 872567 1971107 := bstep (se 1 (by rfl) ⟨1478330, by rfl⟩ : syracuseStep 1971107 = 2956661) B2956661
theorem B2954285 : Blo 872567 2954285 := bstep (se 3 (by rfl) ⟨553928, by rfl⟩ : syracuseStep 2954285 = 1107857) B1107857
theorem B2954339 : Blo 872567 2954339 := bstep (se 1 (by rfl) ⟨2215754, by rfl⟩ : syracuseStep 2954339 = 4431509) B4431509
theorem B3740849 : Blo 872567 3740849 := bstep (se 2 (by rfl) ⟨1402818, by rfl⟩ : syracuseStep 3740849 = 2805637) B2805637
theorem B1971377 : Blo 872567 1971377 := bstep (se 2 (by rfl) ⟨739266, by rfl⟩ : syracuseStep 1971377 = 1478533) B1478533
theorem B1971395 : Blo 872567 1971395 := bstep (se 1 (by rfl) ⟨1478546, by rfl⟩ : syracuseStep 1971395 = 2957093) B2957093
theorem B1774801 : Blo 872567 1774801 := bstep (se 2 (by rfl) ⟨665550, by rfl⟩ : syracuseStep 1774801 = 1331101) B1331101
theorem B3314915 : Blo 872567 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B2954609 : Blo 872567 2954609 := bstep (se 2 (by rfl) ⟨1107978, by rfl⟩ : syracuseStep 2954609 = 2215957) B2215957
theorem B1971665 : Blo 872567 1971665 := bstep (se 2 (by rfl) ⟨739374, by rfl⟩ : syracuseStep 1971665 = 1478749) B1478749
theorem B1971683 : Blo 872567 1971683 := bstep (se 1 (by rfl) ⟨1478762, by rfl⟩ : syracuseStep 1971683 = 2957525) B2957525
theorem B1971953 : Blo 872567 1971953 := bstep (se 2 (by rfl) ⟨739482, by rfl⟩ : syracuseStep 1971953 = 1478965) B1478965
theorem B1971971 : Blo 872567 1971971 := bstep (se 1 (by rfl) ⟨1478978, by rfl⟩ : syracuseStep 1971971 = 2957957) B2957957
theorem B2529137 : Blo 872567 2529137 := bstep (se 2 (by rfl) ⟨948426, by rfl⟩ : syracuseStep 2529137 = 1896853) B1896853
theorem B1120115 : Blo 872567 1120115 := bstep (se 1 (by rfl) ⟨840086, by rfl⟩ : syracuseStep 1120115 = 1680173) B1680173
theorem B2955149 : Blo 872567 2955149 := bstep (se 3 (by rfl) ⟨554090, by rfl⟩ : syracuseStep 2955149 = 1108181) B1108181
theorem B2398097 : Blo 872567 2398097 := bstep (se 2 (by rfl) ⟨899286, by rfl⟩ : syracuseStep 2398097 = 1798573) B1798573
theorem B2955203 : Blo 872567 2955203 := bstep (se 1 (by rfl) ⟨2216402, by rfl⟩ : syracuseStep 2955203 = 4432805) B4432805
theorem B1120243 : Blo 872567 1120243 := bstep (se 1 (by rfl) ⟨840182, by rfl⟩ : syracuseStep 1120243 = 1680365) B1680365
theorem B1972241 : Blo 872567 1972241 := bstep (se 2 (by rfl) ⟨739590, by rfl⟩ : syracuseStep 1972241 = 1479181) B1479181
theorem B1972259 : Blo 872567 1972259 := bstep (se 1 (by rfl) ⟨1479194, by rfl⟩ : syracuseStep 1972259 = 2958389) B2958389
theorem B5314673 : Blo 872567 5314673 := bstep (se 2 (by rfl) ⟨1993002, by rfl⟩ : syracuseStep 5314673 = 3986005) B3986005
theorem B2365613 : Blo 872567 2365613 := bstep (se 3 (by rfl) ⟨443552, by rfl⟩ : syracuseStep 2365613 = 887105) B887105
theorem B3315917 : Blo 872567 3315917 := bstep (se 3 (by rfl) ⟨621734, by rfl⟩ : syracuseStep 3315917 = 1243469) B1243469
theorem B2955473 : Blo 872567 2955473 := bstep (se 2 (by rfl) ⟨1108302, by rfl⟩ : syracuseStep 2955473 = 2216605) B2216605
theorem B4430051 : Blo 872567 4430051 := bstep (se 1 (by rfl) ⟨3322538, by rfl⟩ : syracuseStep 4430051 = 6645077) B6645077
theorem B1579267 : Blo 872567 1579267 := bstep (se 1 (by rfl) ⟨1184450, by rfl⟩ : syracuseStep 1579267 = 2368901) B2368901
theorem B1579331 : Blo 872567 1579331 := bstep (se 1 (by rfl) ⟨1184498, by rfl⟩ : syracuseStep 1579331 = 2368997) B2368997
theorem B5609861 : Blo 872567 5609861 := bstep (se 4 (by rfl) ⟨525924, by rfl⟩ : syracuseStep 5609861 = 1051849) B1051849
theorem B15932045 : Blo 872567 15932045 := bstep (se 3 (by rfl) ⟨2987258, by rfl⟩ : syracuseStep 15932045 = 5974517) B5974517
theorem B4496077 : Blo 872567 4496077 := bstep (se 3 (by rfl) ⟨843014, by rfl⟩ : syracuseStep 4496077 = 1686029) B1686029
theorem B2956013 : Blo 872567 2956013 := bstep (se 3 (by rfl) ⟨554252, by rfl⟩ : syracuseStep 2956013 = 1108505) B1108505
theorem B2956067 : Blo 872567 2956067 := bstep (se 1 (by rfl) ⟨2217050, by rfl⟩ : syracuseStep 2956067 = 4434101) B4434101
theorem B7478243 : Blo 872567 7478243 := bstep (se 1 (by rfl) ⟨5608682, by rfl⟩ : syracuseStep 7478243 = 11217365) B11217365
theorem B4430861 : Blo 872567 4430861 := bstep (se 3 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 4430861 = 1661573) B1661573
theorem B2956337 : Blo 872567 2956337 := bstep (se 2 (by rfl) ⟨1108626, by rfl⟩ : syracuseStep 2956337 = 2217253) B2217253
theorem B2661617 : Blo 872567 2661617 := bstep (se 2 (by rfl) ⟨998106, by rfl⟩ : syracuseStep 2661617 = 1996213) B1996213
theorem B11214389 : Blo 872567 11214389 := bstep (se 5 (by rfl) ⟨525674, by rfl⟩ : syracuseStep 11214389 = 1051349) B1051349
theorem B2956877 : Blo 872567 2956877 := bstep (se 3 (by rfl) ⟨554414, by rfl⟩ : syracuseStep 2956877 = 1108829) B1108829
theorem B2956931 : Blo 872567 2956931 := bstep (se 1 (by rfl) ⟨2217698, by rfl⟩ : syracuseStep 2956931 = 4435397) B4435397
theorem B1023763 : Blo 872567 1023763 := bstep (se 1 (by rfl) ⟨767822, by rfl⟩ : syracuseStep 1023763 = 1535645) B1535645
theorem B64659221 : Blo 872567 64659221 := bstep (se 6 (by rfl) ⟨1515450, by rfl⟩ : syracuseStep 64659221 = 3030901) B3030901
theorem B2957201 : Blo 872567 2957201 := bstep (se 2 (by rfl) ⟨1108950, by rfl⟩ : syracuseStep 2957201 = 2217901) B2217901
theorem B3318029 : Blo 872567 3318029 := bstep (se 3 (by rfl) ⟨622130, by rfl⟩ : syracuseStep 3318029 = 1244261) B1244261
theorem B2957741 : Blo 872567 2957741 := bstep (se 3 (by rfl) ⟨554576, by rfl⟩ : syracuseStep 2957741 = 1109153) B1109153
theorem B4727267 : Blo 872567 4727267 := bstep (se 1 (by rfl) ⟨3545450, by rfl⟩ : syracuseStep 4727267 = 7090901) B7090901
theorem B2957795 : Blo 872567 2957795 := bstep (se 1 (by rfl) ⟨2218346, by rfl⟩ : syracuseStep 2957795 = 4436693) B4436693
theorem B2466289 : Blo 872567 2466289 := bstep (se 2 (by rfl) ⟨924858, by rfl⟩ : syracuseStep 2466289 = 1849717) B1849717
theorem B5677573 : Blo 872567 5677573 := bstep (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) B1064545
theorem B2368045 : Blo 872567 2368045 := bstep (se 3 (by rfl) ⟨444008, by rfl⟩ : syracuseStep 2368045 = 888017) B888017
theorem B6628067 : Blo 872567 6628067 := bstep (se 1 (by rfl) ⟨4971050, by rfl⟩ : syracuseStep 6628067 = 9942101) B9942101
theorem B2368241 : Blo 872567 2368241 := bstep (se 2 (by rfl) ⟨888090, by rfl⟩ : syracuseStep 2368241 = 1776181) B1776181
theorem B2958065 : Blo 872567 2958065 := bstep (se 2 (by rfl) ⟨1109274, by rfl⟩ : syracuseStep 2958065 = 2218549) B2218549
theorem B3318833 : Blo 872567 3318833 := bstep (se 2 (by rfl) ⟨1244562, by rfl⟩ : syracuseStep 3318833 = 2489125) B2489125
theorem B2663491 : Blo 872567 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B1123507 : Blo 872567 1123507 := bstep (se 1 (by rfl) ⟨842630, by rfl⟩ : syracuseStep 1123507 = 1685261) B1685261
theorem B14165189 : Blo 872567 14165189 := bstep (se 4 (by rfl) ⟨1327986, by rfl⟩ : syracuseStep 14165189 = 2655973) B2655973
theorem B2368931 : Blo 872567 2368931 := bstep (se 1 (by rfl) ⟨1776698, by rfl⟩ : syracuseStep 2368931 = 3553397) B3553397
theorem B2663857 : Blo 872567 2663857 := bstep (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) B1997893
theorem B3319501 : Blo 872567 3319501 := bstep (se 3 (by rfl) ⟨622406, by rfl⟩ : syracuseStep 3319501 = 1244813) B1244813
theorem B4433777 : Blo 872567 4433777 := bstep (se 2 (by rfl) ⟨1662666, by rfl⟩ : syracuseStep 4433777 = 3325333) B3325333
theorem B4728739 : Blo 872567 4728739 := bstep (se 1 (by rfl) ⟨3546554, by rfl⟩ : syracuseStep 4728739 = 7093109) B7093109
theorem B7579619 : Blo 872567 7579619 := bstep (se 1 (by rfl) ⟨5684714, by rfl⟩ : syracuseStep 7579619 = 11369429) B11369429
theorem B9939185 : Blo 872567 9939185 := bstep (se 2 (by rfl) ⟨3727194, by rfl⟩ : syracuseStep 9939185 = 7454389) B7454389
theorem B2959715 : Blo 872567 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B76687813 : Blo 872567 76687813 := bstep (se 4 (by rfl) ⟨7189482, by rfl⟩ : syracuseStep 76687813 = 14378965) B14378965
theorem B3320291 : Blo 872567 3320291 := bstep (se 1 (by rfl) ⟨2490218, by rfl⟩ : syracuseStep 3320291 = 4980437) B4980437
theorem B3156529 : Blo 872567 3156529 := bstep (se 2 (by rfl) ⟨1183698, by rfl⟩ : syracuseStep 3156529 = 2367397) B2367397
theorem B7481969 : Blo 872567 7481969 := bstep (se 2 (by rfl) ⟨2805738, by rfl⟩ : syracuseStep 7481969 = 5611477) B5611477
theorem B2665219 : Blo 872567 2665219 := bstep (se 1 (by rfl) ⟨1998914, by rfl⟩ : syracuseStep 2665219 = 3997829) B3997829
theorem B5745421 : Blo 872567 5745421 := bstep (se 3 (by rfl) ⟨1077266, by rfl⟩ : syracuseStep 5745421 = 2154533) B2154533
theorem B2665315 : Blo 872567 2665315 := bstep (se 1 (by rfl) ⟨1998986, by rfl⟩ : syracuseStep 2665315 = 3997973) B3997973
theorem B3320945 : Blo 872567 3320945 := bstep (se 2 (by rfl) ⟨1245354, by rfl⟩ : syracuseStep 3320945 = 2490709) B2490709
theorem B4730033 : Blo 872567 4730033 := bstep (se 2 (by rfl) ⟨1773762, by rfl⟩ : syracuseStep 4730033 = 3547525) B3547525
theorem B2796781 : Blo 872567 2796781 := bstep (se 3 (by rfl) ⟨524396, by rfl⟩ : syracuseStep 2796781 = 1048793) B1048793
theorem B4435235 : Blo 872567 4435235 := bstep (se 1 (by rfl) ⟨3326426, by rfl⟩ : syracuseStep 4435235 = 6652853) B6652853
theorem B1421057 : Blo 872567 1421057 := bstep (se 2 (by rfl) ⟨532896, by rfl⟩ : syracuseStep 1421057 = 1065793) B1065793
theorem B5320561 : Blo 872567 5320561 := bstep (se 2 (by rfl) ⟨1995210, by rfl⟩ : syracuseStep 5320561 = 3990421) B3990421
theorem B15150989 : Blo 872567 15150989 := bstep (se 3 (by rfl) ⟨2840810, by rfl⟩ : syracuseStep 15150989 = 5681621) B5681621
theorem B4436045 : Blo 872567 4436045 := bstep (se 3 (by rfl) ⟨831758, by rfl⟩ : syracuseStep 4436045 = 1663517) B1663517
theorem B3322403 : Blo 872567 3322403 := bstep (se 1 (by rfl) ⟨2491802, by rfl⟩ : syracuseStep 3322403 = 4983605) B4983605
theorem B3322417 : Blo 872567 3322417 := bstep (se 2 (by rfl) ⟨1245906, by rfl⟩ : syracuseStep 3322417 = 2491813) B2491813
theorem B10629731 : Blo 872567 10629731 := bstep (se 1 (by rfl) ⟨7972298, by rfl⟩ : syracuseStep 10629731 = 15944597) B15944597
theorem B2798563 : Blo 872567 2798563 := bstep (se 1 (by rfl) ⟨2098922, by rfl⟩ : syracuseStep 2798563 = 4197845) B4197845
theorem B12629105 : Blo 872567 12629105 := bstep (se 2 (by rfl) ⟨4735914, by rfl⟩ : syracuseStep 12629105 = 9471829) B9471829
theorem B1684739 : Blo 872567 1684739 := bstep (se 1 (by rfl) ⟨1263554, by rfl⟩ : syracuseStep 1684739 = 2527109) B2527109
theorem B2799011 : Blo 872567 2799011 := bstep (se 1 (by rfl) ⟨2099258, by rfl⟩ : syracuseStep 2799011 = 4198517) B4198517
theorem B2995633 : Blo 872567 2995633 := bstep (se 2 (by rfl) ⟨1123362, by rfl⟩ : syracuseStep 2995633 = 2246725) B2246725
theorem B5682659 : Blo 872567 5682659 := bstep (se 1 (by rfl) ⟨4261994, by rfl⟩ : syracuseStep 5682659 = 8523989) B8523989
theorem B2209265 : Blo 872567 2209265 := bstep (se 2 (by rfl) ⟨828474, by rfl⟩ : syracuseStep 2209265 = 1656949) B1656949
theorem B2209315 : Blo 872567 2209315 := bstep (se 1 (by rfl) ⟨1656986, by rfl⟩ : syracuseStep 2209315 = 3313973) B3313973
theorem B2209457 : Blo 872567 2209457 := bstep (se 2 (by rfl) ⟨828546, by rfl⟩ : syracuseStep 2209457 = 1657093) B1657093
theorem B6633413 : Blo 872567 6633413 := bstep (se 4 (by rfl) ⟨621882, by rfl⟩ : syracuseStep 6633413 = 1243765) B1243765
theorem B3323875 : Blo 872567 3323875 := bstep (se 1 (by rfl) ⟨2492906, by rfl⟩ : syracuseStep 3323875 = 4985813) B4985813
theorem B931987 : Blo 872567 931987 := bstep (se 1 (by rfl) ⟨698990, by rfl⟩ : syracuseStep 931987 = 1397981) B1397981
theorem B11221361 : Blo 872567 11221361 := bstep (se 2 (by rfl) ⟨4208010, by rfl⟩ : syracuseStep 11221361 = 8416021) B8416021
theorem B2996621 : Blo 872567 2996621 := bstep (se 3 (by rfl) ⟨561866, by rfl⟩ : syracuseStep 2996621 = 1123733) B1123733
theorem B932243 : Blo 872567 932243 := bstep (se 1 (by rfl) ⟨699182, by rfl⟩ : syracuseStep 932243 = 1398365) B1398365
theorem B7485965 : Blo 872567 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B2800241 : Blo 872567 2800241 := bstep (se 2 (by rfl) ⟨1050090, by rfl⟩ : syracuseStep 2800241 = 2100181) B2100181
theorem B2210449 : Blo 872567 2210449 := bstep (se 2 (by rfl) ⟨828918, by rfl⟩ : syracuseStep 2210449 = 1657837) B1657837
theorem B2210723 : Blo 872567 2210723 := bstep (se 1 (by rfl) ⟨1658042, by rfl⟩ : syracuseStep 2210723 = 3316085) B3316085
theorem B2210915 : Blo 872567 2210915 := bstep (se 1 (by rfl) ⟨1658186, by rfl⟩ : syracuseStep 2210915 = 3316373) B3316373
theorem B932995 : Blo 872567 932995 := bstep (se 1 (by rfl) ⟨699746, by rfl⟩ : syracuseStep 932995 = 1399493) B1399493
theorem B2997485 : Blo 872567 2997485 := bstep (se 3 (by rfl) ⟨562028, by rfl⟩ : syracuseStep 2997485 = 1124057) B1124057
theorem B2801137 : Blo 872567 2801137 := bstep (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) B2100853
theorem B10632845 : Blo 872567 10632845 := bstep (se 3 (by rfl) ⟨1993658, by rfl⟩ : syracuseStep 10632845 = 3987317) B3987317
theorem B2244419 : Blo 872567 2244419 := bstep (se 1 (by rfl) ⟨1683314, by rfl⟩ : syracuseStep 2244419 = 3366629) B3366629
theorem B60702605 : Blo 872567 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B5390243 : Blo 872567 5390243 := bstep (se 1 (by rfl) ⟨4042682, by rfl⟩ : syracuseStep 5390243 = 8085365) B8085365
theorem B9453581 : Blo 872567 9453581 := bstep (se 3 (by rfl) ⟨1772546, by rfl⟩ : syracuseStep 9453581 = 3545093) B3545093
theorem B2211857 : Blo 872567 2211857 := bstep (se 2 (by rfl) ⟨829446, by rfl⟩ : syracuseStep 2211857 = 1658893) B1658893
theorem B2211907 : Blo 872567 2211907 := bstep (se 1 (by rfl) ⟨1658930, by rfl⟩ : syracuseStep 2211907 = 3317861) B3317861
theorem B3326093 : Blo 872567 3326093 := bstep (se 3 (by rfl) ⟨623642, by rfl⟩ : syracuseStep 3326093 = 1247285) B1247285
theorem B2212049 : Blo 872567 2212049 := bstep (se 2 (by rfl) ⟨829518, by rfl⟩ : syracuseStep 2212049 = 1659037) B1659037
theorem B934259 : Blo 872567 934259 := bstep (se 1 (by rfl) ⟨700694, by rfl⟩ : syracuseStep 934259 = 1401389) B1401389
theorem B1327745 : Blo 872567 1327745 := bstep (se 2 (by rfl) ⟨497904, by rfl⟩ : syracuseStep 1327745 = 995809) B995809
theorem B2802701 : Blo 872567 2802701 := bstep (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) B1051013
theorem B2245699 : Blo 872567 2245699 := bstep (se 1 (by rfl) ⟨1684274, by rfl⟩ : syracuseStep 2245699 = 3368549) B3368549
theorem B935011 : Blo 872567 935011 := bstep (se 1 (by rfl) ⟨701258, by rfl⟩ : syracuseStep 935011 = 1402517) B1402517
theorem B2213041 : Blo 872567 2213041 := bstep (se 2 (by rfl) ⟨829890, by rfl⟩ : syracuseStep 2213041 = 1659781) B1659781
theorem B4736177 : Blo 872567 4736177 := bstep (se 2 (by rfl) ⟨1776066, by rfl⟩ : syracuseStep 4736177 = 3552133) B3552133
theorem B2213315 : Blo 872567 2213315 := bstep (se 1 (by rfl) ⟨1659986, by rfl⟩ : syracuseStep 2213315 = 3319973) B3319973
theorem B3032515 : Blo 872567 3032515 := bstep (se 1 (by rfl) ⟨2274386, by rfl⟩ : syracuseStep 3032515 = 4548773) B4548773
theorem B2835953 : Blo 872567 2835953 := bstep (se 2 (by rfl) ⟨1063482, by rfl⟩ : syracuseStep 2835953 = 2126965) B2126965
theorem B2213507 : Blo 872567 2213507 := bstep (se 1 (by rfl) ⟨1660130, by rfl⟩ : syracuseStep 2213507 = 3320261) B3320261
theorem B1492673 : Blo 872567 1492673 := bstep (se 2 (by rfl) ⟨559752, by rfl⟩ : syracuseStep 1492673 = 1119505) B1119505
theorem B936019 : Blo 872567 936019 := bstep (se 1 (by rfl) ⟨702014, by rfl⟩ : syracuseStep 936019 = 1404029) B1404029
theorem B3786851 : Blo 872567 3786851 := bstep (se 1 (by rfl) ⟨2840138, by rfl⟩ : syracuseStep 3786851 = 5680277) B5680277
theorem B1493219 : Blo 872567 1493219 := bstep (se 1 (by rfl) ⟨1119914, by rfl⟩ : syracuseStep 1493219 = 2239829) B2239829
theorem B22399253 : Blo 872567 22399253 := bstep (se 6 (by rfl) ⟨524982, by rfl⟩ : syracuseStep 22399253 = 1049965) B1049965
theorem B1657169 : Blo 872567 1657169 := bstep (se 2 (by rfl) ⟨621438, by rfl⟩ : syracuseStep 1657169 = 1242877) B1242877
theorem B7457123 : Blo 872567 7457123 := bstep (se 1 (by rfl) ⟨5592842, by rfl⟩ : syracuseStep 7457123 = 11185685) B11185685
theorem B7588237 : Blo 872567 7588237 := bstep (se 3 (by rfl) ⟨1422794, by rfl⟩ : syracuseStep 7588237 = 2845589) B2845589
theorem B2214449 : Blo 872567 2214449 := bstep (se 2 (by rfl) ⟨830418, by rfl⟩ : syracuseStep 2214449 = 1660837) B1660837
theorem B2214499 : Blo 872567 2214499 := bstep (se 1 (by rfl) ⟨1660874, by rfl⟩ : syracuseStep 2214499 = 3321749) B3321749
theorem B2214641 : Blo 872567 2214641 := bstep (se 2 (by rfl) ⟨830490, by rfl⟩ : syracuseStep 2214641 = 1660981) B1660981
theorem B5753861 : Blo 872567 5753861 := bstep (se 4 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 5753861 = 1078849) B1078849
theorem B1658065 : Blo 872567 1658065 := bstep (se 2 (by rfl) ⟨621774, by rfl⟩ : syracuseStep 1658065 = 1243549) B1243549
theorem B1658225 : Blo 872567 1658225 := bstep (se 2 (by rfl) ⟨621834, by rfl⟩ : syracuseStep 1658225 = 1243669) B1243669
theorem B2805187 : Blo 872567 2805187 := bstep (se 1 (by rfl) ⟨2103890, by rfl⟩ : syracuseStep 2805187 = 4207781) B4207781
theorem B2805329 : Blo 872567 2805329 := bstep (se 2 (by rfl) ⟨1051998, by rfl⟩ : syracuseStep 2805329 = 2103997) B2103997
theorem B6639245 : Blo 872567 6639245 := bstep (se 3 (by rfl) ⟨1244858, by rfl⟩ : syracuseStep 6639245 = 2489717) B2489717
theorem B2805443 : Blo 872567 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B2215633 : Blo 872567 2215633 := bstep (se 2 (by rfl) ⟨830862, by rfl⟩ : syracuseStep 2215633 = 1661725) B1661725
theorem B1658627 : Blo 872567 1658627 := bstep (se 1 (by rfl) ⟨1243970, by rfl⟩ : syracuseStep 1658627 = 2487941) B2487941
theorem B4542257 : Blo 872567 4542257 := bstep (se 2 (by rfl) ⟨1703346, by rfl⟩ : syracuseStep 4542257 = 3406693) B3406693
theorem B2215907 : Blo 872567 2215907 := bstep (se 1 (by rfl) ⟨1661930, by rfl⟩ : syracuseStep 2215907 = 3323861) B3323861
theorem B12144653 : Blo 872567 12144653 := bstep (se 3 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 12144653 = 4554245) B4554245
theorem B8966213 : Blo 872567 8966213 := bstep (se 4 (by rfl) ⟨840582, by rfl⟩ : syracuseStep 8966213 = 1681165) B1681165
theorem B872579 : Blo 872567 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B6312077 : Blo 872567 6312077 := bstep (se 3 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 6312077 = 2367029) B2367029
theorem B872595 : Blo 872567 872595 := bstep (se 1 (by rfl) ⟨654446, by rfl⟩ : syracuseStep 872595 = 1308893) B1308893
theorem B872611 : Blo 872567 872611 := bstep (se 1 (by rfl) ⟨654458, by rfl⟩ : syracuseStep 872611 = 1308917) B1308917
theorem B2216099 : Blo 872567 2216099 := bstep (se 1 (by rfl) ⟨1662074, by rfl⟩ : syracuseStep 2216099 = 3324149) B3324149
theorem B872627 : Blo 872567 872627 := bstep (se 1 (by rfl) ⟨654470, by rfl⟩ : syracuseStep 872627 = 1308941) B1308941
theorem B872643 : Blo 872567 872643 := bstep (se 1 (by rfl) ⟨654482, by rfl⟩ : syracuseStep 872643 = 1308965) B1308965
theorem B872659 : Blo 872567 872659 := bstep (se 1 (by rfl) ⟨654494, by rfl⟩ : syracuseStep 872659 = 1308989) B1308989
theorem B872675 : Blo 872567 872675 := bstep (se 1 (by rfl) ⟨654506, by rfl⟩ : syracuseStep 872675 = 1309013) B1309013
theorem B872691 : Blo 872567 872691 := bstep (se 1 (by rfl) ⟨654518, by rfl⟩ : syracuseStep 872691 = 1309037) B1309037
theorem B872707 : Blo 872567 872707 := bstep (se 1 (by rfl) ⟨654530, by rfl⟩ : syracuseStep 872707 = 1309061) B1309061
theorem B872723 : Blo 872567 872723 := bstep (se 1 (by rfl) ⟨654542, by rfl⟩ : syracuseStep 872723 = 1309085) B1309085
theorem B872739 : Blo 872567 872739 := bstep (se 1 (by rfl) ⟨654554, by rfl⟩ : syracuseStep 872739 = 1309109) B1309109
theorem B872755 : Blo 872567 872755 := bstep (se 1 (by rfl) ⟨654566, by rfl⟩ : syracuseStep 872755 = 1309133) B1309133
theorem B872771 : Blo 872567 872771 := bstep (se 1 (by rfl) ⟨654578, by rfl⟩ : syracuseStep 872771 = 1309157) B1309157
theorem B872787 : Blo 872567 872787 := bstep (se 1 (by rfl) ⟨654590, by rfl⟩ : syracuseStep 872787 = 1309181) B1309181
theorem B872803 : Blo 872567 872803 := bstep (se 1 (by rfl) ⟨654602, by rfl⟩ : syracuseStep 872803 = 1309205) B1309205
theorem B872819 : Blo 872567 872819 := bstep (se 1 (by rfl) ⟨654614, by rfl⟩ : syracuseStep 872819 = 1309229) B1309229
theorem B872835 : Blo 872567 872835 := bstep (se 1 (by rfl) ⟨654626, by rfl⟩ : syracuseStep 872835 = 1309253) B1309253
theorem B872851 : Blo 872567 872851 := bstep (se 1 (by rfl) ⟨654638, by rfl⟩ : syracuseStep 872851 = 1309277) B1309277
theorem B1495457 : Blo 872567 1495457 := bstep (se 2 (by rfl) ⟨560796, by rfl⟩ : syracuseStep 1495457 = 1121593) B1121593
theorem B872867 : Blo 872567 872867 := bstep (se 1 (by rfl) ⟨654650, by rfl⟩ : syracuseStep 872867 = 1309301) B1309301
theorem B872883 : Blo 872567 872883 := bstep (se 1 (by rfl) ⟨654662, by rfl⟩ : syracuseStep 872883 = 1309325) B1309325
theorem B872899 : Blo 872567 872899 := bstep (se 1 (by rfl) ⟨654674, by rfl⟩ : syracuseStep 872899 = 1309349) B1309349
theorem B872915 : Blo 872567 872915 := bstep (se 1 (by rfl) ⟨654686, by rfl⟩ : syracuseStep 872915 = 1309373) B1309373
theorem B872931 : Blo 872567 872931 := bstep (se 1 (by rfl) ⟨654698, by rfl⟩ : syracuseStep 872931 = 1309397) B1309397
theorem B872947 : Blo 872567 872947 := bstep (se 1 (by rfl) ⟨654710, by rfl⟩ : syracuseStep 872947 = 1309421) B1309421
theorem B872963 : Blo 872567 872963 := bstep (se 1 (by rfl) ⟨654722, by rfl⟩ : syracuseStep 872963 = 1309445) B1309445
theorem B872979 : Blo 872567 872979 := bstep (se 1 (by rfl) ⟨654734, by rfl⟩ : syracuseStep 872979 = 1309469) B1309469
theorem B872995 : Blo 872567 872995 := bstep (se 1 (by rfl) ⟨654746, by rfl⟩ : syracuseStep 872995 = 1309493) B1309493
theorem B873011 : Blo 872567 873011 := bstep (se 1 (by rfl) ⟨654758, by rfl⟩ : syracuseStep 873011 = 1309517) B1309517
theorem B873027 : Blo 872567 873027 := bstep (se 1 (by rfl) ⟨654770, by rfl⟩ : syracuseStep 873027 = 1309541) B1309541
theorem B873043 : Blo 872567 873043 := bstep (se 1 (by rfl) ⟨654782, by rfl⟩ : syracuseStep 873043 = 1309565) B1309565
theorem B873059 : Blo 872567 873059 := bstep (se 1 (by rfl) ⟨654794, by rfl⟩ : syracuseStep 873059 = 1309589) B1309589
theorem B873075 : Blo 872567 873075 := bstep (se 1 (by rfl) ⟨654806, by rfl⟩ : syracuseStep 873075 = 1309613) B1309613
theorem B873091 : Blo 872567 873091 := bstep (se 1 (by rfl) ⟨654818, by rfl⟩ : syracuseStep 873091 = 1309637) B1309637
theorem B1659523 : Blo 872567 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B2806417 : Blo 872567 2806417 := bstep (se 2 (by rfl) ⟨1052406, by rfl⟩ : syracuseStep 2806417 = 2104813) B2104813
theorem B873107 : Blo 872567 873107 := bstep (se 1 (by rfl) ⟨654830, by rfl⟩ : syracuseStep 873107 = 1309661) B1309661
theorem B873123 : Blo 872567 873123 := bstep (se 1 (by rfl) ⟨654842, by rfl⟩ : syracuseStep 873123 = 1309685) B1309685
theorem B873139 : Blo 872567 873139 := bstep (se 1 (by rfl) ⟨654854, by rfl⟩ : syracuseStep 873139 = 1309709) B1309709
theorem B873155 : Blo 872567 873155 := bstep (se 1 (by rfl) ⟨654866, by rfl⟩ : syracuseStep 873155 = 1309733) B1309733
theorem B873171 : Blo 872567 873171 := bstep (se 1 (by rfl) ⟨654878, by rfl⟩ : syracuseStep 873171 = 1309757) B1309757
theorem B873187 : Blo 872567 873187 := bstep (se 1 (by rfl) ⟨654890, by rfl⟩ : syracuseStep 873187 = 1309781) B1309781
theorem B873203 : Blo 872567 873203 := bstep (se 1 (by rfl) ⟨654902, by rfl⟩ : syracuseStep 873203 = 1309805) B1309805
theorem B873219 : Blo 872567 873219 := bstep (se 1 (by rfl) ⟨654914, by rfl⟩ : syracuseStep 873219 = 1309829) B1309829
theorem B5985029 : Blo 872567 5985029 := bstep (se 4 (by rfl) ⟨561096, by rfl⟩ : syracuseStep 5985029 = 1122193) B1122193
theorem B873235 : Blo 872567 873235 := bstep (se 1 (by rfl) ⟨654926, by rfl⟩ : syracuseStep 873235 = 1309853) B1309853
theorem B873251 : Blo 872567 873251 := bstep (se 1 (by rfl) ⟨654938, by rfl⟩ : syracuseStep 873251 = 1309877) B1309877
theorem B1659683 : Blo 872567 1659683 := bstep (se 1 (by rfl) ⟨1244762, by rfl⟩ : syracuseStep 1659683 = 2489525) B2489525
theorem B873267 : Blo 872567 873267 := bstep (se 1 (by rfl) ⟨654950, by rfl⟩ : syracuseStep 873267 = 1309901) B1309901
theorem B873283 : Blo 872567 873283 := bstep (se 1 (by rfl) ⟨654962, by rfl⟩ : syracuseStep 873283 = 1309925) B1309925
theorem B873299 : Blo 872567 873299 := bstep (se 1 (by rfl) ⟨654974, by rfl⟩ : syracuseStep 873299 = 1309949) B1309949
theorem B873315 : Blo 872567 873315 := bstep (se 1 (by rfl) ⟨654986, by rfl⟩ : syracuseStep 873315 = 1309973) B1309973
theorem B873331 : Blo 872567 873331 := bstep (se 1 (by rfl) ⟨654998, by rfl⟩ : syracuseStep 873331 = 1309997) B1309997
theorem B873347 : Blo 872567 873347 := bstep (se 1 (by rfl) ⟨655010, by rfl⟩ : syracuseStep 873347 = 1310021) B1310021
theorem B873363 : Blo 872567 873363 := bstep (se 1 (by rfl) ⟨655022, by rfl⟩ : syracuseStep 873363 = 1310045) B1310045
theorem B873379 : Blo 872567 873379 := bstep (se 1 (by rfl) ⟨655034, by rfl⟩ : syracuseStep 873379 = 1310069) B1310069
theorem B873395 : Blo 872567 873395 := bstep (se 1 (by rfl) ⟨655046, by rfl⟩ : syracuseStep 873395 = 1310093) B1310093
theorem B873411 : Blo 872567 873411 := bstep (se 1 (by rfl) ⟨655058, by rfl⟩ : syracuseStep 873411 = 1310117) B1310117
theorem B873427 : Blo 872567 873427 := bstep (se 1 (by rfl) ⟨655070, by rfl⟩ : syracuseStep 873427 = 1310141) B1310141
theorem B873443 : Blo 872567 873443 := bstep (se 1 (by rfl) ⟨655082, by rfl⟩ : syracuseStep 873443 = 1310165) B1310165
theorem B873459 : Blo 872567 873459 := bstep (se 1 (by rfl) ⟨655094, by rfl⟩ : syracuseStep 873459 = 1310189) B1310189
theorem B873475 : Blo 872567 873475 := bstep (se 1 (by rfl) ⟨655106, by rfl⟩ : syracuseStep 873475 = 1310213) B1310213
theorem B5592077 : Blo 872567 5592077 := bstep (se 3 (by rfl) ⟨1048514, by rfl⟩ : syracuseStep 5592077 = 2097029) B2097029
theorem B873491 : Blo 872567 873491 := bstep (se 1 (by rfl) ⟨655118, by rfl⟩ : syracuseStep 873491 = 1310237) B1310237
theorem B873507 : Blo 872567 873507 := bstep (se 1 (by rfl) ⟨655130, by rfl⟩ : syracuseStep 873507 = 1310261) B1310261
theorem B873523 : Blo 872567 873523 := bstep (se 1 (by rfl) ⟨655142, by rfl⟩ : syracuseStep 873523 = 1310285) B1310285
theorem B1397827 : Blo 872567 1397827 := bstep (se 1 (by rfl) ⟨1048370, by rfl⟩ : syracuseStep 1397827 = 2096741) B2096741
theorem B873539 : Blo 872567 873539 := bstep (se 1 (by rfl) ⟨655154, by rfl⟩ : syracuseStep 873539 = 1310309) B1310309
theorem B2217041 : Blo 872567 2217041 := bstep (se 2 (by rfl) ⟨831390, by rfl⟩ : syracuseStep 2217041 = 1662781) B1662781
theorem B873555 : Blo 872567 873555 := bstep (se 1 (by rfl) ⟨655166, by rfl⟩ : syracuseStep 873555 = 1310333) B1310333
theorem B873571 : Blo 872567 873571 := bstep (se 1 (by rfl) ⟨655178, by rfl⟩ : syracuseStep 873571 = 1310357) B1310357
theorem B873587 : Blo 872567 873587 := bstep (se 1 (by rfl) ⟨655190, by rfl⟩ : syracuseStep 873587 = 1310381) B1310381
theorem B873603 : Blo 872567 873603 := bstep (se 1 (by rfl) ⟨655202, by rfl⟩ : syracuseStep 873603 = 1310405) B1310405
theorem B2217091 : Blo 872567 2217091 := bstep (se 1 (by rfl) ⟨1662818, by rfl⟩ : syracuseStep 2217091 = 3325637) B3325637
theorem B873619 : Blo 872567 873619 := bstep (se 1 (by rfl) ⟨655214, by rfl⟩ : syracuseStep 873619 = 1310429) B1310429
theorem B873635 : Blo 872567 873635 := bstep (se 1 (by rfl) ⟨655226, by rfl⟩ : syracuseStep 873635 = 1310453) B1310453
theorem B873651 : Blo 872567 873651 := bstep (se 1 (by rfl) ⟨655238, by rfl⟩ : syracuseStep 873651 = 1310477) B1310477
theorem B873667 : Blo 872567 873667 := bstep (se 1 (by rfl) ⟨655250, by rfl⟩ : syracuseStep 873667 = 1310501) B1310501
theorem B873683 : Blo 872567 873683 := bstep (se 1 (by rfl) ⟨655262, by rfl⟩ : syracuseStep 873683 = 1310525) B1310525
theorem B873699 : Blo 872567 873699 := bstep (se 1 (by rfl) ⟨655274, by rfl⟩ : syracuseStep 873699 = 1310549) B1310549
theorem B1135859 : Blo 872567 1135859 := bstep (se 1 (by rfl) ⟨851894, by rfl⟩ : syracuseStep 1135859 = 1703789) B1703789
theorem B873715 : Blo 872567 873715 := bstep (se 1 (by rfl) ⟨655286, by rfl⟩ : syracuseStep 873715 = 1310573) B1310573
theorem B873731 : Blo 872567 873731 := bstep (se 1 (by rfl) ⟨655298, by rfl⟩ : syracuseStep 873731 = 1310597) B1310597
theorem B2217233 : Blo 872567 2217233 := bstep (se 2 (by rfl) ⟨831462, by rfl⟩ : syracuseStep 2217233 = 1662925) B1662925
theorem B873747 : Blo 872567 873747 := bstep (se 1 (by rfl) ⟨655310, by rfl⟩ : syracuseStep 873747 = 1310621) B1310621
theorem B873763 : Blo 872567 873763 := bstep (se 1 (by rfl) ⟨655322, by rfl⟩ : syracuseStep 873763 = 1310645) B1310645
theorem B873779 : Blo 872567 873779 := bstep (se 1 (by rfl) ⟨655334, by rfl⟩ : syracuseStep 873779 = 1310669) B1310669
theorem B873795 : Blo 872567 873795 := bstep (se 1 (by rfl) ⟨655346, by rfl⟩ : syracuseStep 873795 = 1310693) B1310693
theorem B873811 : Blo 872567 873811 := bstep (se 1 (by rfl) ⟨655358, by rfl⟩ : syracuseStep 873811 = 1310717) B1310717
theorem B873827 : Blo 872567 873827 := bstep (se 1 (by rfl) ⟨655370, by rfl⟩ : syracuseStep 873827 = 1310741) B1310741
theorem B873843 : Blo 872567 873843 := bstep (se 1 (by rfl) ⟨655382, by rfl⟩ : syracuseStep 873843 = 1310765) B1310765
theorem B873859 : Blo 872567 873859 := bstep (se 1 (by rfl) ⟨655394, by rfl⟩ : syracuseStep 873859 = 1310789) B1310789
theorem B873875 : Blo 872567 873875 := bstep (se 1 (by rfl) ⟨655406, by rfl⟩ : syracuseStep 873875 = 1310813) B1310813
theorem B873891 : Blo 872567 873891 := bstep (se 1 (by rfl) ⟨655418, by rfl⟩ : syracuseStep 873891 = 1310837) B1310837
theorem B873907 : Blo 872567 873907 := bstep (se 1 (by rfl) ⟨655430, by rfl⟩ : syracuseStep 873907 = 1310861) B1310861
theorem B873923 : Blo 872567 873923 := bstep (se 1 (by rfl) ⟨655442, by rfl⟩ : syracuseStep 873923 = 1310885) B1310885
theorem B873939 : Blo 872567 873939 := bstep (se 1 (by rfl) ⟨655454, by rfl⟩ : syracuseStep 873939 = 1310909) B1310909
theorem B873955 : Blo 872567 873955 := bstep (se 1 (by rfl) ⟨655466, by rfl⟩ : syracuseStep 873955 = 1310933) B1310933
theorem B5199331 : Blo 872567 5199331 := bstep (se 1 (by rfl) ⟨3899498, by rfl⟩ : syracuseStep 5199331 = 7798997) B7798997
theorem B873971 : Blo 872567 873971 := bstep (se 1 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 873971 = 1310957) B1310957
theorem B873987 : Blo 872567 873987 := bstep (se 1 (by rfl) ⟨655490, by rfl⟩ : syracuseStep 873987 = 1310981) B1310981
theorem B874003 : Blo 872567 874003 := bstep (se 1 (by rfl) ⟨655502, by rfl⟩ : syracuseStep 874003 = 1311005) B1311005
theorem B874019 : Blo 872567 874019 := bstep (se 1 (by rfl) ⟨655514, by rfl⟩ : syracuseStep 874019 = 1311029) B1311029
theorem B874035 : Blo 872567 874035 := bstep (se 1 (by rfl) ⟨655526, by rfl⟩ : syracuseStep 874035 = 1311053) B1311053
theorem B874051 : Blo 872567 874051 := bstep (se 1 (by rfl) ⟨655538, by rfl⟩ : syracuseStep 874051 = 1311077) B1311077
theorem B874067 : Blo 872567 874067 := bstep (se 1 (by rfl) ⟨655550, by rfl⟩ : syracuseStep 874067 = 1311101) B1311101
theorem B874083 : Blo 872567 874083 := bstep (se 1 (by rfl) ⟨655562, by rfl⟩ : syracuseStep 874083 = 1311125) B1311125
theorem B874099 : Blo 872567 874099 := bstep (se 1 (by rfl) ⟨655574, by rfl⟩ : syracuseStep 874099 = 1311149) B1311149
theorem B874115 : Blo 872567 874115 := bstep (se 1 (by rfl) ⟨655586, by rfl⟩ : syracuseStep 874115 = 1311173) B1311173
theorem B874131 : Blo 872567 874131 := bstep (se 1 (by rfl) ⟨655598, by rfl⟩ : syracuseStep 874131 = 1311197) B1311197
theorem B874147 : Blo 872567 874147 := bstep (se 1 (by rfl) ⟨655610, by rfl⟩ : syracuseStep 874147 = 1311221) B1311221
theorem B874163 : Blo 872567 874163 := bstep (se 1 (by rfl) ⟨655622, by rfl⟩ : syracuseStep 874163 = 1311245) B1311245
theorem B874179 : Blo 872567 874179 := bstep (se 1 (by rfl) ⟨655634, by rfl⟩ : syracuseStep 874179 = 1311269) B1311269
theorem B874195 : Blo 872567 874195 := bstep (se 1 (by rfl) ⟨655646, by rfl⟩ : syracuseStep 874195 = 1311293) B1311293
theorem B874211 : Blo 872567 874211 := bstep (se 1 (by rfl) ⟨655658, by rfl⟩ : syracuseStep 874211 = 1311317) B1311317
theorem B874227 : Blo 872567 874227 := bstep (se 1 (by rfl) ⟨655670, by rfl⟩ : syracuseStep 874227 = 1311341) B1311341
theorem B874243 : Blo 872567 874243 := bstep (se 1 (by rfl) ⟨655682, by rfl⟩ : syracuseStep 874243 = 1311365) B1311365
theorem B874259 : Blo 872567 874259 := bstep (se 1 (by rfl) ⟨655694, by rfl⟩ : syracuseStep 874259 = 1311389) B1311389
theorem B874275 : Blo 872567 874275 := bstep (se 1 (by rfl) ⟨655706, by rfl⟩ : syracuseStep 874275 = 1311413) B1311413
theorem B874291 : Blo 872567 874291 := bstep (se 1 (by rfl) ⟨655718, by rfl⟩ : syracuseStep 874291 = 1311437) B1311437
theorem B874307 : Blo 872567 874307 := bstep (se 1 (by rfl) ⟨655730, by rfl⟩ : syracuseStep 874307 = 1311461) B1311461
theorem B1660753 : Blo 872567 1660753 := bstep (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) B1245565
theorem B874323 : Blo 872567 874323 := bstep (se 1 (by rfl) ⟨655742, by rfl⟩ : syracuseStep 874323 = 1311485) B1311485
theorem B874339 : Blo 872567 874339 := bstep (se 1 (by rfl) ⟨655754, by rfl⟩ : syracuseStep 874339 = 1311509) B1311509
theorem B874355 : Blo 872567 874355 := bstep (se 1 (by rfl) ⟨655766, by rfl⟩ : syracuseStep 874355 = 1311533) B1311533
theorem B874371 : Blo 872567 874371 := bstep (se 1 (by rfl) ⟨655778, by rfl⟩ : syracuseStep 874371 = 1311557) B1311557
theorem B874387 : Blo 872567 874387 := bstep (se 1 (by rfl) ⟨655790, by rfl⟩ : syracuseStep 874387 = 1311581) B1311581
theorem B874403 : Blo 872567 874403 := bstep (se 1 (by rfl) ⟨655802, by rfl⟩ : syracuseStep 874403 = 1311605) B1311605
theorem B874419 : Blo 872567 874419 := bstep (se 1 (by rfl) ⟨655814, by rfl⟩ : syracuseStep 874419 = 1311629) B1311629
theorem B874435 : Blo 872567 874435 := bstep (se 1 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 874435 = 1311653) B1311653
theorem B874451 : Blo 872567 874451 := bstep (se 1 (by rfl) ⟨655838, by rfl⟩ : syracuseStep 874451 = 1311677) B1311677
theorem B874467 : Blo 872567 874467 := bstep (se 1 (by rfl) ⟨655850, by rfl⟩ : syracuseStep 874467 = 1311701) B1311701
theorem B874483 : Blo 872567 874483 := bstep (se 1 (by rfl) ⟨655862, by rfl⟩ : syracuseStep 874483 = 1311725) B1311725
theorem B874499 : Blo 872567 874499 := bstep (se 1 (by rfl) ⟨655874, by rfl⟩ : syracuseStep 874499 = 1311749) B1311749
theorem B874515 : Blo 872567 874515 := bstep (se 1 (by rfl) ⟨655886, by rfl⟩ : syracuseStep 874515 = 1311773) B1311773
theorem B874531 : Blo 872567 874531 := bstep (se 1 (by rfl) ⟨655898, by rfl⟩ : syracuseStep 874531 = 1311797) B1311797
theorem B874547 : Blo 872567 874547 := bstep (se 1 (by rfl) ⟨655910, by rfl⟩ : syracuseStep 874547 = 1311821) B1311821
theorem B2873411 : Blo 872567 2873411 := bstep (se 1 (by rfl) ⟨2155058, by rfl⟩ : syracuseStep 2873411 = 4310117) B4310117
theorem B874563 : Blo 872567 874563 := bstep (se 1 (by rfl) ⟨655922, by rfl⟩ : syracuseStep 874563 = 1311845) B1311845
theorem B874579 : Blo 872567 874579 := bstep (se 1 (by rfl) ⟨655934, by rfl⟩ : syracuseStep 874579 = 1311869) B1311869
theorem B874595 : Blo 872567 874595 := bstep (se 1 (by rfl) ⟨655946, by rfl⟩ : syracuseStep 874595 = 1311893) B1311893
theorem B874611 : Blo 872567 874611 := bstep (se 1 (by rfl) ⟨655958, by rfl⟩ : syracuseStep 874611 = 1311917) B1311917
theorem B874627 : Blo 872567 874627 := bstep (se 1 (by rfl) ⟨655970, by rfl⟩ : syracuseStep 874627 = 1311941) B1311941
theorem B874643 : Blo 872567 874643 := bstep (se 1 (by rfl) ⟨655982, by rfl⟩ : syracuseStep 874643 = 1311965) B1311965
theorem B874659 : Blo 872567 874659 := bstep (se 1 (by rfl) ⟨655994, by rfl⟩ : syracuseStep 874659 = 1311989) B1311989
theorem B874675 : Blo 872567 874675 := bstep (se 1 (by rfl) ⟨656006, by rfl⟩ : syracuseStep 874675 = 1312013) B1312013
theorem B874691 : Blo 872567 874691 := bstep (se 1 (by rfl) ⟨656018, by rfl⟩ : syracuseStep 874691 = 1312037) B1312037
theorem B874707 : Blo 872567 874707 := bstep (se 1 (by rfl) ⟨656030, by rfl⟩ : syracuseStep 874707 = 1312061) B1312061
theorem B874723 : Blo 872567 874723 := bstep (se 1 (by rfl) ⟨656042, by rfl⟩ : syracuseStep 874723 = 1312085) B1312085
theorem B2218225 : Blo 872567 2218225 := bstep (se 2 (by rfl) ⟨831834, by rfl⟩ : syracuseStep 2218225 = 1663669) B1663669
theorem B874739 : Blo 872567 874739 := bstep (se 1 (by rfl) ⟨656054, by rfl⟩ : syracuseStep 874739 = 1312109) B1312109
theorem B874755 : Blo 872567 874755 := bstep (se 1 (by rfl) ⟨656066, by rfl⟩ : syracuseStep 874755 = 1312133) B1312133
theorem B874771 : Blo 872567 874771 := bstep (se 1 (by rfl) ⟨656078, by rfl⟩ : syracuseStep 874771 = 1312157) B1312157
theorem B874787 : Blo 872567 874787 := bstep (se 1 (by rfl) ⟨656090, by rfl⟩ : syracuseStep 874787 = 1312181) B1312181
theorem B874803 : Blo 872567 874803 := bstep (se 1 (by rfl) ⟨656102, by rfl⟩ : syracuseStep 874803 = 1312205) B1312205
theorem B874819 : Blo 872567 874819 := bstep (se 1 (by rfl) ⟨656114, by rfl⟩ : syracuseStep 874819 = 1312229) B1312229
theorem B874835 : Blo 872567 874835 := bstep (se 1 (by rfl) ⟨656126, by rfl⟩ : syracuseStep 874835 = 1312253) B1312253
theorem B874851 : Blo 872567 874851 := bstep (se 1 (by rfl) ⟨656138, by rfl⟩ : syracuseStep 874851 = 1312277) B1312277
theorem B874867 : Blo 872567 874867 := bstep (se 1 (by rfl) ⟨656150, by rfl⟩ : syracuseStep 874867 = 1312301) B1312301
theorem B874883 : Blo 872567 874883 := bstep (se 1 (by rfl) ⟨656162, by rfl⟩ : syracuseStep 874883 = 1312325) B1312325
theorem B874899 : Blo 872567 874899 := bstep (se 1 (by rfl) ⟨656174, by rfl⟩ : syracuseStep 874899 = 1312349) B1312349
theorem B4970915 : Blo 872567 4970915 := bstep (se 1 (by rfl) ⟨3728186, by rfl⟩ : syracuseStep 4970915 = 7456373) B7456373
theorem B874915 : Blo 872567 874915 := bstep (se 1 (by rfl) ⟨656186, by rfl⟩ : syracuseStep 874915 = 1312373) B1312373
theorem B874931 : Blo 872567 874931 := bstep (se 1 (by rfl) ⟨656198, by rfl⟩ : syracuseStep 874931 = 1312397) B1312397
theorem B874947 : Blo 872567 874947 := bstep (se 1 (by rfl) ⟨656210, by rfl⟩ : syracuseStep 874947 = 1312421) B1312421
theorem B874963 : Blo 872567 874963 := bstep (se 1 (by rfl) ⟨656222, by rfl⟩ : syracuseStep 874963 = 1312445) B1312445
theorem B874979 : Blo 872567 874979 := bstep (se 1 (by rfl) ⟨656234, by rfl⟩ : syracuseStep 874979 = 1312469) B1312469
theorem B1497571 : Blo 872567 1497571 := bstep (se 1 (by rfl) ⟨1123178, by rfl⟩ : syracuseStep 1497571 = 2246357) B2246357
theorem B6642161 : Blo 872567 6642161 := bstep (se 2 (by rfl) ⟨2490810, by rfl⟩ : syracuseStep 6642161 = 4981621) B4981621
theorem B874995 : Blo 872567 874995 := bstep (se 1 (by rfl) ⟨656246, by rfl⟩ : syracuseStep 874995 = 1312493) B1312493
theorem B875011 : Blo 872567 875011 := bstep (se 1 (by rfl) ⟨656258, by rfl⟩ : syracuseStep 875011 = 1312517) B1312517
theorem B2218499 : Blo 872567 2218499 := bstep (se 1 (by rfl) ⟨1663874, by rfl⟩ : syracuseStep 2218499 = 3327749) B3327749
theorem B1399313 : Blo 872567 1399313 := bstep (se 2 (by rfl) ⟨524742, by rfl⟩ : syracuseStep 1399313 = 1049485) B1049485
theorem B875027 : Blo 872567 875027 := bstep (se 1 (by rfl) ⟨656270, by rfl⟩ : syracuseStep 875027 = 1312541) B1312541
theorem B875043 : Blo 872567 875043 := bstep (se 1 (by rfl) ⟨656282, by rfl⟩ : syracuseStep 875043 = 1312565) B1312565
theorem B875059 : Blo 872567 875059 := bstep (se 1 (by rfl) ⟨656294, by rfl⟩ : syracuseStep 875059 = 1312589) B1312589
theorem B875075 : Blo 872567 875075 := bstep (se 1 (by rfl) ⟨656306, by rfl⟩ : syracuseStep 875075 = 1312613) B1312613
theorem B875091 : Blo 872567 875091 := bstep (se 1 (by rfl) ⟨656318, by rfl⟩ : syracuseStep 875091 = 1312637) B1312637
theorem B875107 : Blo 872567 875107 := bstep (se 1 (by rfl) ⟨656330, by rfl⟩ : syracuseStep 875107 = 1312661) B1312661
theorem B875123 : Blo 872567 875123 := bstep (se 1 (by rfl) ⟨656342, by rfl⟩ : syracuseStep 875123 = 1312685) B1312685
theorem B875139 : Blo 872567 875139 := bstep (se 1 (by rfl) ⟨656354, by rfl⟩ : syracuseStep 875139 = 1312709) B1312709
theorem B1399441 : Blo 872567 1399441 := bstep (se 2 (by rfl) ⟨524790, by rfl⟩ : syracuseStep 1399441 = 1049581) B1049581
theorem B875155 : Blo 872567 875155 := bstep (se 1 (by rfl) ⟨656366, by rfl⟩ : syracuseStep 875155 = 1312733) B1312733
theorem B875171 : Blo 872567 875171 := bstep (se 1 (by rfl) ⟨656378, by rfl⟩ : syracuseStep 875171 = 1312757) B1312757
theorem B875187 : Blo 872567 875187 := bstep (se 1 (by rfl) ⟨656390, by rfl⟩ : syracuseStep 875187 = 1312781) B1312781
theorem B875203 : Blo 872567 875203 := bstep (se 1 (by rfl) ⟨656402, by rfl⟩ : syracuseStep 875203 = 1312805) B1312805
theorem B2218691 : Blo 872567 2218691 := bstep (se 1 (by rfl) ⟨1664018, by rfl⟩ : syracuseStep 2218691 = 3328037) B3328037
theorem B875219 : Blo 872567 875219 := bstep (se 1 (by rfl) ⟨656414, by rfl⟩ : syracuseStep 875219 = 1312829) B1312829
theorem B875235 : Blo 872567 875235 := bstep (se 1 (by rfl) ⟨656426, by rfl⟩ : syracuseStep 875235 = 1312853) B1312853
theorem B875251 : Blo 872567 875251 := bstep (se 1 (by rfl) ⟨656438, by rfl⟩ : syracuseStep 875251 = 1312877) B1312877
theorem B875267 : Blo 872567 875267 := bstep (se 1 (by rfl) ⟨656450, by rfl⟩ : syracuseStep 875267 = 1312901) B1312901
theorem B875283 : Blo 872567 875283 := bstep (se 1 (by rfl) ⟨656462, by rfl⟩ : syracuseStep 875283 = 1312925) B1312925
theorem B875299 : Blo 872567 875299 := bstep (se 1 (by rfl) ⟨656474, by rfl⟩ : syracuseStep 875299 = 1312949) B1312949
theorem B875315 : Blo 872567 875315 := bstep (se 1 (by rfl) ⟨656486, by rfl⟩ : syracuseStep 875315 = 1312973) B1312973
theorem B875331 : Blo 872567 875331 := bstep (se 1 (by rfl) ⟨656498, by rfl⟩ : syracuseStep 875331 = 1312997) B1312997
theorem B875347 : Blo 872567 875347 := bstep (se 1 (by rfl) ⟨656510, by rfl⟩ : syracuseStep 875347 = 1313021) B1313021
theorem B875363 : Blo 872567 875363 := bstep (se 1 (by rfl) ⟨656522, by rfl⟩ : syracuseStep 875363 = 1313045) B1313045
theorem B1661809 : Blo 872567 1661809 := bstep (se 2 (by rfl) ⟨623178, by rfl⟩ : syracuseStep 1661809 = 1246357) B1246357
theorem B875379 : Blo 872567 875379 := bstep (se 1 (by rfl) ⟨656534, by rfl⟩ : syracuseStep 875379 = 1313069) B1313069
theorem B875395 : Blo 872567 875395 := bstep (se 1 (by rfl) ⟨656546, by rfl⟩ : syracuseStep 875395 = 1313093) B1313093
theorem B875411 : Blo 872567 875411 := bstep (se 1 (by rfl) ⟨656558, by rfl⟩ : syracuseStep 875411 = 1313117) B1313117
theorem B875427 : Blo 872567 875427 := bstep (se 1 (by rfl) ⟨656570, by rfl⟩ : syracuseStep 875427 = 1313141) B1313141
theorem B875443 : Blo 872567 875443 := bstep (se 1 (by rfl) ⟨656582, by rfl⟩ : syracuseStep 875443 = 1313165) B1313165
theorem B1104835 : Blo 872567 1104835 := bstep (se 1 (by rfl) ⟨828626, by rfl⟩ : syracuseStep 1104835 = 1657253) B1657253
theorem B875459 : Blo 872567 875459 := bstep (se 1 (by rfl) ⟨656594, by rfl⟩ : syracuseStep 875459 = 1313189) B1313189
theorem B875475 : Blo 872567 875475 := bstep (se 1 (by rfl) ⟨656606, by rfl⟩ : syracuseStep 875475 = 1313213) B1313213
theorem B875491 : Blo 872567 875491 := bstep (se 1 (by rfl) ⟨656618, by rfl⟩ : syracuseStep 875491 = 1313237) B1313237
theorem B875507 : Blo 872567 875507 := bstep (se 1 (by rfl) ⟨656630, by rfl⟩ : syracuseStep 875507 = 1313261) B1313261
theorem B875523 : Blo 872567 875523 := bstep (se 1 (by rfl) ⟨656642, by rfl⟩ : syracuseStep 875523 = 1313285) B1313285
theorem B875539 : Blo 872567 875539 := bstep (se 1 (by rfl) ⟨656654, by rfl⟩ : syracuseStep 875539 = 1313309) B1313309
theorem B1104931 : Blo 872567 1104931 := bstep (se 1 (by rfl) ⟨828698, by rfl⟩ : syracuseStep 1104931 = 1657397) B1657397
theorem B875555 : Blo 872567 875555 := bstep (se 1 (by rfl) ⟨656666, by rfl⟩ : syracuseStep 875555 = 1313333) B1313333
theorem B875571 : Blo 872567 875571 := bstep (se 1 (by rfl) ⟨656678, by rfl⟩ : syracuseStep 875571 = 1313357) B1313357
theorem B875587 : Blo 872567 875587 := bstep (se 1 (by rfl) ⟨656690, by rfl⟩ : syracuseStep 875587 = 1313381) B1313381
theorem B875603 : Blo 872567 875603 := bstep (se 1 (by rfl) ⟨656702, by rfl⟩ : syracuseStep 875603 = 1313405) B1313405
theorem B875619 : Blo 872567 875619 := bstep (se 1 (by rfl) ⟨656714, by rfl⟩ : syracuseStep 875619 = 1313429) B1313429
theorem B875635 : Blo 872567 875635 := bstep (se 1 (by rfl) ⟨656726, by rfl⟩ : syracuseStep 875635 = 1313453) B1313453
theorem B875651 : Blo 872567 875651 := bstep (se 1 (by rfl) ⟨656738, by rfl⟩ : syracuseStep 875651 = 1313477) B1313477
theorem B875667 : Blo 872567 875667 := bstep (se 1 (by rfl) ⟨656750, by rfl⟩ : syracuseStep 875667 = 1313501) B1313501
theorem B875683 : Blo 872567 875683 := bstep (se 1 (by rfl) ⟨656762, by rfl⟩ : syracuseStep 875683 = 1313525) B1313525
theorem B875699 : Blo 872567 875699 := bstep (se 1 (by rfl) ⟨656774, by rfl⟩ : syracuseStep 875699 = 1313549) B1313549
theorem B875715 : Blo 872567 875715 := bstep (se 1 (by rfl) ⟨656786, by rfl⟩ : syracuseStep 875715 = 1313573) B1313573
theorem B875731 : Blo 872567 875731 := bstep (se 1 (by rfl) ⟨656798, by rfl⟩ : syracuseStep 875731 = 1313597) B1313597
theorem B875747 : Blo 872567 875747 := bstep (se 1 (by rfl) ⟨656810, by rfl⟩ : syracuseStep 875747 = 1313621) B1313621
theorem B875763 : Blo 872567 875763 := bstep (se 1 (by rfl) ⟨656822, by rfl⟩ : syracuseStep 875763 = 1313645) B1313645
theorem B1662211 : Blo 872567 1662211 := bstep (se 1 (by rfl) ⟨1246658, by rfl⟩ : syracuseStep 1662211 = 2493317) B2493317
theorem B875779 : Blo 872567 875779 := bstep (se 1 (by rfl) ⟨656834, by rfl⟩ : syracuseStep 875779 = 1313669) B1313669
theorem B875795 : Blo 872567 875795 := bstep (se 1 (by rfl) ⟨656846, by rfl⟩ : syracuseStep 875795 = 1313693) B1313693
theorem B875811 : Blo 872567 875811 := bstep (se 1 (by rfl) ⟨656858, by rfl⟩ : syracuseStep 875811 = 1313717) B1313717
theorem B1662257 : Blo 872567 1662257 := bstep (se 2 (by rfl) ⟨623346, by rfl⟩ : syracuseStep 1662257 = 1246693) B1246693
theorem B875827 : Blo 872567 875827 := bstep (se 1 (by rfl) ⟨656870, by rfl⟩ : syracuseStep 875827 = 1313741) B1313741
theorem B875843 : Blo 872567 875843 := bstep (se 1 (by rfl) ⟨656882, by rfl⟩ : syracuseStep 875843 = 1313765) B1313765
theorem B875859 : Blo 872567 875859 := bstep (se 1 (by rfl) ⟨656894, by rfl⟩ : syracuseStep 875859 = 1313789) B1313789
theorem B875875 : Blo 872567 875875 := bstep (se 1 (by rfl) ⟨656906, by rfl⟩ : syracuseStep 875875 = 1313813) B1313813
theorem B875891 : Blo 872567 875891 := bstep (se 1 (by rfl) ⟨656918, by rfl⟩ : syracuseStep 875891 = 1313837) B1313837
theorem B875907 : Blo 872567 875907 := bstep (se 1 (by rfl) ⟨656930, by rfl⟩ : syracuseStep 875907 = 1313861) B1313861
theorem B875923 : Blo 872567 875923 := bstep (se 1 (by rfl) ⟨656942, by rfl⟩ : syracuseStep 875923 = 1313885) B1313885
theorem B875939 : Blo 872567 875939 := bstep (se 1 (by rfl) ⟨656954, by rfl⟩ : syracuseStep 875939 = 1313909) B1313909
theorem B875955 : Blo 872567 875955 := bstep (se 1 (by rfl) ⟨656966, by rfl⟩ : syracuseStep 875955 = 1313933) B1313933
theorem B875971 : Blo 872567 875971 := bstep (se 1 (by rfl) ⟨656978, by rfl⟩ : syracuseStep 875971 = 1313957) B1313957
theorem B875987 : Blo 872567 875987 := bstep (se 1 (by rfl) ⟨656990, by rfl⟩ : syracuseStep 875987 = 1313981) B1313981
theorem B876003 : Blo 872567 876003 := bstep (se 1 (by rfl) ⟨657002, by rfl⟩ : syracuseStep 876003 = 1314005) B1314005
theorem B876019 : Blo 872567 876019 := bstep (se 1 (by rfl) ⟨657014, by rfl⟩ : syracuseStep 876019 = 1314029) B1314029
theorem B876035 : Blo 872567 876035 := bstep (se 1 (by rfl) ⟨657026, by rfl⟩ : syracuseStep 876035 = 1314053) B1314053
theorem B7200269 : Blo 872567 7200269 := bstep (se 3 (by rfl) ⟨1350050, by rfl⟩ : syracuseStep 7200269 = 2700101) B2700101
theorem B1105427 : Blo 872567 1105427 := bstep (se 1 (by rfl) ⟨829070, by rfl⟩ : syracuseStep 1105427 = 1658141) B1658141
theorem B876051 : Blo 872567 876051 := bstep (se 1 (by rfl) ⟨657038, by rfl⟩ : syracuseStep 876051 = 1314077) B1314077
theorem B876067 : Blo 872567 876067 := bstep (se 1 (by rfl) ⟨657050, by rfl⟩ : syracuseStep 876067 = 1314101) B1314101
theorem B876083 : Blo 872567 876083 := bstep (se 1 (by rfl) ⟨657062, by rfl⟩ : syracuseStep 876083 = 1314125) B1314125
theorem B876099 : Blo 872567 876099 := bstep (se 1 (by rfl) ⟨657074, by rfl⟩ : syracuseStep 876099 = 1314149) B1314149
theorem B1662545 : Blo 872567 1662545 := bstep (se 2 (by rfl) ⟨623454, by rfl⟩ : syracuseStep 1662545 = 1246909) B1246909
theorem B876115 : Blo 872567 876115 := bstep (se 1 (by rfl) ⟨657086, by rfl⟩ : syracuseStep 876115 = 1314173) B1314173
theorem B876131 : Blo 872567 876131 := bstep (se 1 (by rfl) ⟨657098, by rfl⟩ : syracuseStep 876131 = 1314197) B1314197
theorem B876147 : Blo 872567 876147 := bstep (se 1 (by rfl) ⟨657110, by rfl⟩ : syracuseStep 876147 = 1314221) B1314221
theorem B876163 : Blo 872567 876163 := bstep (se 1 (by rfl) ⟨657122, by rfl⟩ : syracuseStep 876163 = 1314245) B1314245
theorem B876179 : Blo 872567 876179 := bstep (se 1 (by rfl) ⟨657134, by rfl⟩ : syracuseStep 876179 = 1314269) B1314269
theorem B876195 : Blo 872567 876195 := bstep (se 1 (by rfl) ⟨657146, by rfl⟩ : syracuseStep 876195 = 1314293) B1314293
theorem B876211 : Blo 872567 876211 := bstep (se 1 (by rfl) ⟨657158, by rfl⟩ : syracuseStep 876211 = 1314317) B1314317
theorem B876227 : Blo 872567 876227 := bstep (se 1 (by rfl) ⟨657170, by rfl⟩ : syracuseStep 876227 = 1314341) B1314341
theorem B876243 : Blo 872567 876243 := bstep (se 1 (by rfl) ⟨657182, by rfl⟩ : syracuseStep 876243 = 1314365) B1314365
theorem B876259 : Blo 872567 876259 := bstep (se 1 (by rfl) ⟨657194, by rfl⟩ : syracuseStep 876259 = 1314389) B1314389
theorem B876275 : Blo 872567 876275 := bstep (se 1 (by rfl) ⟨657206, by rfl⟩ : syracuseStep 876275 = 1314413) B1314413
theorem B876291 : Blo 872567 876291 := bstep (se 1 (by rfl) ⟨657218, by rfl⟩ : syracuseStep 876291 = 1314437) B1314437
theorem B876307 : Blo 872567 876307 := bstep (se 1 (by rfl) ⟨657230, by rfl⟩ : syracuseStep 876307 = 1314461) B1314461
theorem B876323 : Blo 872567 876323 := bstep (se 1 (by rfl) ⟨657242, by rfl⟩ : syracuseStep 876323 = 1314485) B1314485
theorem B876339 : Blo 872567 876339 := bstep (se 1 (by rfl) ⟨657254, by rfl⟩ : syracuseStep 876339 = 1314509) B1314509
theorem B876355 : Blo 872567 876355 := bstep (se 1 (by rfl) ⟨657266, by rfl⟩ : syracuseStep 876355 = 1314533) B1314533
theorem B1498961 : Blo 872567 1498961 := bstep (se 2 (by rfl) ⟨562110, by rfl⟩ : syracuseStep 1498961 = 1124221) B1124221
theorem B876371 : Blo 872567 876371 := bstep (se 1 (by rfl) ⟨657278, by rfl⟩ : syracuseStep 876371 = 1314557) B1314557
theorem B876387 : Blo 872567 876387 := bstep (se 1 (by rfl) ⟨657290, by rfl⟩ : syracuseStep 876387 = 1314581) B1314581
theorem B876403 : Blo 872567 876403 := bstep (se 1 (by rfl) ⟨657302, by rfl⟩ : syracuseStep 876403 = 1314605) B1314605
theorem B876419 : Blo 872567 876419 := bstep (se 1 (by rfl) ⟨657314, by rfl⟩ : syracuseStep 876419 = 1314629) B1314629
theorem B1400723 : Blo 872567 1400723 := bstep (se 1 (by rfl) ⟨1050542, by rfl⟩ : syracuseStep 1400723 = 2101085) B2101085
theorem B876435 : Blo 872567 876435 := bstep (se 1 (by rfl) ⟨657326, by rfl⟩ : syracuseStep 876435 = 1314653) B1314653
theorem B876451 : Blo 872567 876451 := bstep (se 1 (by rfl) ⟨657338, by rfl⟩ : syracuseStep 876451 = 1314677) B1314677
theorem B876467 : Blo 872567 876467 := bstep (se 1 (by rfl) ⟨657350, by rfl⟩ : syracuseStep 876467 = 1314701) B1314701
theorem B876483 : Blo 872567 876483 := bstep (se 1 (by rfl) ⟨657362, by rfl⟩ : syracuseStep 876483 = 1314725) B1314725
theorem B876499 : Blo 872567 876499 := bstep (se 1 (by rfl) ⟨657374, by rfl⟩ : syracuseStep 876499 = 1314749) B1314749
theorem B876515 : Blo 872567 876515 := bstep (se 1 (by rfl) ⟨657386, by rfl⟩ : syracuseStep 876515 = 1314773) B1314773
theorem B1400819 : Blo 872567 1400819 := bstep (se 1 (by rfl) ⟨1050614, by rfl⟩ : syracuseStep 1400819 = 2101229) B2101229
theorem B876531 : Blo 872567 876531 := bstep (se 1 (by rfl) ⟨657398, by rfl⟩ : syracuseStep 876531 = 1314797) B1314797
theorem B876547 : Blo 872567 876547 := bstep (se 1 (by rfl) ⟨657410, by rfl⟩ : syracuseStep 876547 = 1314821) B1314821
theorem B1400851 : Blo 872567 1400851 := bstep (se 1 (by rfl) ⟨1050638, by rfl⟩ : syracuseStep 1400851 = 2101277) B2101277
theorem B876563 : Blo 872567 876563 := bstep (se 1 (by rfl) ⟨657422, by rfl⟩ : syracuseStep 876563 = 1314845) B1314845
theorem B8413253 : Blo 872567 8413253 := bstep (se 4 (by rfl) ⟨788742, by rfl⟩ : syracuseStep 8413253 = 1577485) B1577485
theorem B2875565 : Blo 872567 2875565 := bstep (se 3 (by rfl) ⟨539168, by rfl⟩ : syracuseStep 2875565 = 1078337) B1078337
theorem B1106131 : Blo 872567 1106131 := bstep (se 1 (by rfl) ⟨829598, by rfl⟩ : syracuseStep 1106131 = 1659197) B1659197
theorem B1663267 : Blo 872567 1663267 := bstep (se 1 (by rfl) ⟨1247450, by rfl⟩ : syracuseStep 1663267 = 2494901) B2494901
theorem B1106227 : Blo 872567 1106227 := bstep (se 1 (by rfl) ⟨829670, by rfl⟩ : syracuseStep 1106227 = 1659341) B1659341
theorem B3367565 : Blo 872567 3367565 := bstep (se 3 (by rfl) ⟨631418, by rfl⟩ : syracuseStep 3367565 = 1262837) B1262837
theorem B1663715 : Blo 872567 1663715 := bstep (se 1 (by rfl) ⟨1247786, by rfl⟩ : syracuseStep 1663715 = 2495573) B2495573
theorem B1106723 : Blo 872567 1106723 := bstep (se 1 (by rfl) ⟨830042, by rfl⟩ : syracuseStep 1106723 = 1660085) B1660085
theorem B9462581 : Blo 872567 9462581 := bstep (se 5 (by rfl) ⟨443558, by rfl⟩ : syracuseStep 9462581 = 887117) B887117
theorem B1401761 : Blo 872567 1401761 := bstep (se 2 (by rfl) ⟨525660, by rfl⟩ : syracuseStep 1401761 = 1051321) B1051321
theorem B1664003 : Blo 872567 1664003 := bstep (se 1 (by rfl) ⟨1248002, by rfl⟩ : syracuseStep 1664003 = 2496005) B2496005
theorem B1107427 : Blo 872567 1107427 := bstep (se 1 (by rfl) ⟨830570, by rfl⟩ : syracuseStep 1107427 = 1661141) B1661141
theorem B1107523 : Blo 872567 1107523 := bstep (se 1 (by rfl) ⟨830642, by rfl⟩ : syracuseStep 1107523 = 1661285) B1661285
theorem B4974149 : Blo 872567 4974149 := bstep (se 4 (by rfl) ⟨466326, by rfl⟩ : syracuseStep 4974149 = 932653) B932653
theorem B2156483 : Blo 872567 2156483 := bstep (se 1 (by rfl) ⟨1617362, by rfl⟩ : syracuseStep 2156483 = 3234725) B3234725
theorem B3598285 : Blo 872567 3598285 := bstep (se 3 (by rfl) ⟨674678, by rfl⟩ : syracuseStep 3598285 = 1349357) B1349357
theorem B4974605 : Blo 872567 4974605 := bstep (se 3 (by rfl) ⟨932738, by rfl⟩ : syracuseStep 4974605 = 1865477) B1865477
theorem B1108019 : Blo 872567 1108019 := bstep (se 1 (by rfl) ⟨831014, by rfl⟩ : syracuseStep 1108019 = 1662029) B1662029
theorem B9463877 : Blo 872567 9463877 := bstep (se 4 (by rfl) ⟨887238, by rfl⟩ : syracuseStep 9463877 = 1774477) B1774477
theorem B1403075 : Blo 872567 1403075 := bstep (se 1 (by rfl) ⟨1052306, by rfl⟩ : syracuseStep 1403075 = 2104613) B2104613
theorem B3729827 : Blo 872567 3729827 := bstep (se 1 (by rfl) ⟨2797370, by rfl⟩ : syracuseStep 3729827 = 5594741) B5594741
theorem B1993187 : Blo 872567 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B2484877 : Blo 872567 2484877 := bstep (se 3 (by rfl) ⟨465914, by rfl⟩ : syracuseStep 2484877 = 931829) B931829
theorem B4418225 : Blo 872567 4418225 := bstep (se 2 (by rfl) ⟨1656834, by rfl⟩ : syracuseStep 4418225 = 3313669) B3313669
theorem B1108723 : Blo 872567 1108723 := bstep (se 1 (by rfl) ⟨831542, by rfl⟩ : syracuseStep 1108723 = 1663085) B1663085
theorem B1108819 : Blo 872567 1108819 := bstep (se 1 (by rfl) ⟨831614, by rfl⟩ : syracuseStep 1108819 = 1663229) B1663229
theorem B1403747 : Blo 872567 1403747 := bstep (se 1 (by rfl) ⟨1052810, by rfl⟩ : syracuseStep 1403747 = 2105621) B2105621
theorem B1797233 : Blo 872567 1797233 := bstep (se 2 (by rfl) ⟨673962, by rfl⟩ : syracuseStep 1797233 = 1347925) B1347925
theorem B1404049 : Blo 872567 1404049 := bstep (se 2 (by rfl) ⟨526518, by rfl⟩ : syracuseStep 1404049 = 1053037) B1053037
theorem B1109315 : Blo 872567 1109315 := bstep (se 1 (by rfl) ⟨831986, by rfl⟩ : syracuseStep 1109315 = 1663973) B1663973
theorem B2125457 : Blo 872567 2125457 := bstep (se 2 (by rfl) ⟨797046, by rfl⟩ : syracuseStep 2125457 = 1594093) B1594093
theorem B5992141 : Blo 872567 5992141 := bstep (se 3 (by rfl) ⟨1123526, by rfl⟩ : syracuseStep 5992141 = 2247053) B2247053
theorem B946003 : Blo 872567 946003 := bstep (se 1 (by rfl) ⟨709502, by rfl⟩ : syracuseStep 946003 = 1419005) B1419005
theorem B2945105 : Blo 872567 2945105 := bstep (se 2 (by rfl) ⟨1104414, by rfl⟩ : syracuseStep 2945105 = 2208829) B2208829
theorem B4419683 : Blo 872567 4419683 := bstep (se 1 (by rfl) ⟨3314762, by rfl⟩ : syracuseStep 4419683 = 6629525) B6629525
theorem B2486609 : Blo 872567 2486609 := bstep (se 2 (by rfl) ⟨932478, by rfl⟩ : syracuseStep 2486609 = 1864957) B1864957
theorem B2486801 : Blo 872567 2486801 := bstep (se 2 (by rfl) ⟨932550, by rfl⟩ : syracuseStep 2486801 = 1865101) B1865101
theorem B2945645 : Blo 872567 2945645 := bstep (se 3 (by rfl) ⟨552308, by rfl⟩ : syracuseStep 2945645 = 1104617) B1104617
theorem B2945699 : Blo 872567 2945699 := bstep (se 1 (by rfl) ⟨2209274, by rfl⟩ : syracuseStep 2945699 = 4418549) B4418549
theorem B4977521 : Blo 872567 4977521 := bstep (se 2 (by rfl) ⟨1866570, by rfl⟩ : syracuseStep 4977521 = 3733141) B3733141
theorem B4420493 : Blo 872567 4420493 := bstep (se 3 (by rfl) ⟨828842, by rfl⟩ : syracuseStep 4420493 = 1657685) B1657685
theorem B2945969 : Blo 872567 2945969 := bstep (se 2 (by rfl) ⟨1104738, by rfl⟩ : syracuseStep 2945969 = 2209477) B2209477
theorem B1864657 : Blo 872567 1864657 := bstep (se 2 (by rfl) ⟨699246, by rfl⟩ : syracuseStep 1864657 = 1398493) B1398493
theorem B1963313 : Blo 872567 1963313 := bstep (se 2 (by rfl) ⟨736242, by rfl⟩ : syracuseStep 1963313 = 1472485) B1472485
theorem B1963331 : Blo 872567 1963331 := bstep (se 1 (by rfl) ⟨1472498, by rfl⟩ : syracuseStep 1963331 = 2944997) B2944997
theorem B25228685 : Blo 872567 25228685 := bstep (se 3 (by rfl) ⟨4730378, by rfl⟩ : syracuseStep 25228685 = 9460757) B9460757
theorem B2946509 : Blo 872567 2946509 := bstep (se 3 (by rfl) ⟨552470, by rfl⟩ : syracuseStep 2946509 = 1104941) B1104941
theorem B2487793 : Blo 872567 2487793 := bstep (se 2 (by rfl) ⟨932922, by rfl⟩ : syracuseStep 2487793 = 1865845) B1865845
theorem B2946563 : Blo 872567 2946563 := bstep (se 1 (by rfl) ⟨2209922, by rfl⟩ : syracuseStep 2946563 = 4419845) B4419845
theorem B1963601 : Blo 872567 1963601 := bstep (se 2 (by rfl) ⟨736350, by rfl⟩ : syracuseStep 1963601 = 1472701) B1472701
theorem B1963619 : Blo 872567 1963619 := bstep (se 1 (by rfl) ⟨1472714, by rfl⟩ : syracuseStep 1963619 = 2945429) B2945429
theorem B1242803 : Blo 872567 1242803 := bstep (se 1 (by rfl) ⟨932102, by rfl⟩ : syracuseStep 1242803 = 1864205) B1864205
theorem B1865443 : Blo 872567 1865443 := bstep (se 1 (by rfl) ⟨1399082, by rfl⟩ : syracuseStep 1865443 = 2798165) B2798165
theorem B2488067 : Blo 872567 2488067 := bstep (se 1 (by rfl) ⟨1866050, by rfl⟩ : syracuseStep 2488067 = 3732101) B3732101
theorem B2946833 : Blo 872567 2946833 := bstep (se 2 (by rfl) ⟨1105062, by rfl⟩ : syracuseStep 2946833 = 2210125) B2210125
theorem B1963889 : Blo 872567 1963889 := bstep (se 2 (by rfl) ⟨736458, by rfl⟩ : syracuseStep 1963889 = 1472917) B1472917
theorem B1963907 : Blo 872567 1963907 := bstep (se 1 (by rfl) ⟨1472930, by rfl⟩ : syracuseStep 1963907 = 2945861) B2945861
theorem B2488259 : Blo 872567 2488259 := bstep (se 1 (by rfl) ⟨1866194, by rfl⟩ : syracuseStep 2488259 = 3732389) B3732389
theorem B1472465 : Blo 872567 1472465 := bstep (se 2 (by rfl) ⟨552174, by rfl⟩ : syracuseStep 1472465 = 1104349) B1104349
theorem B1472593 : Blo 872567 1472593 := bstep (se 2 (by rfl) ⟨552222, by rfl⟩ : syracuseStep 1472593 = 1104445) B1104445
theorem B1472627 : Blo 872567 1472627 := bstep (se 1 (by rfl) ⟨1104470, by rfl⟩ : syracuseStep 1472627 = 2208941) B2208941
theorem B1964177 : Blo 872567 1964177 := bstep (se 2 (by rfl) ⟨736566, by rfl⟩ : syracuseStep 1964177 = 1473133) B1473133
theorem B1964195 : Blo 872567 1964195 := bstep (se 1 (by rfl) ⟨1473146, by rfl⟩ : syracuseStep 1964195 = 2946293) B2946293
theorem B1308851 : Blo 872567 1308851 := bstep (se 1 (by rfl) ⟨981638, by rfl⟩ : syracuseStep 1308851 = 1963277) B1963277
theorem B1308881 : Blo 872567 1308881 := bstep (se 2 (by rfl) ⟨490830, by rfl⟩ : syracuseStep 1308881 = 981661) B981661
theorem B1308899 : Blo 872567 1308899 := bstep (se 1 (by rfl) ⟨981674, by rfl⟩ : syracuseStep 1308899 = 1963349) B1963349
theorem B1472755 : Blo 872567 1472755 := bstep (se 1 (by rfl) ⟨1104566, by rfl⟩ : syracuseStep 1472755 = 2209133) B2209133
theorem B1308929 : Blo 872567 1308929 := bstep (se 2 (by rfl) ⟨490848, by rfl⟩ : syracuseStep 1308929 = 981697) B981697
theorem B1308947 : Blo 872567 1308947 := bstep (se 1 (by rfl) ⟨981710, by rfl⟩ : syracuseStep 1308947 = 1963421) B1963421
theorem B4978979 : Blo 872567 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B2947373 : Blo 872567 2947373 := bstep (se 3 (by rfl) ⟨552632, by rfl⟩ : syracuseStep 2947373 = 1105265) B1105265
theorem B1308977 : Blo 872567 1308977 := bstep (se 2 (by rfl) ⟨490866, by rfl⟩ : syracuseStep 1308977 = 981733) B981733
theorem B1243441 : Blo 872567 1243441 := bstep (se 2 (by rfl) ⟨466290, by rfl⟩ : syracuseStep 1243441 = 932581) B932581
theorem B1308995 : Blo 872567 1308995 := bstep (se 1 (by rfl) ⟨981746, by rfl⟩ : syracuseStep 1308995 = 1963493) B1963493
theorem B1309025 : Blo 872567 1309025 := bstep (se 2 (by rfl) ⟨490884, by rfl⟩ : syracuseStep 1309025 = 981769) B981769
theorem B2947427 : Blo 872567 2947427 := bstep (se 1 (by rfl) ⟨2210570, by rfl⟩ : syracuseStep 2947427 = 4421141) B4421141
theorem B1309043 : Blo 872567 1309043 := bstep (se 1 (by rfl) ⟨981782, by rfl⟩ : syracuseStep 1309043 = 1963565) B1963565
theorem B1472897 : Blo 872567 1472897 := bstep (se 2 (by rfl) ⟨552336, by rfl⟩ : syracuseStep 1472897 = 1104673) B1104673
theorem B1309073 : Blo 872567 1309073 := bstep (se 2 (by rfl) ⟨490902, by rfl⟩ : syracuseStep 1309073 = 981805) B981805
theorem B1309091 : Blo 872567 1309091 := bstep (se 1 (by rfl) ⟨981818, by rfl⟩ : syracuseStep 1309091 = 1963637) B1963637
theorem B1964465 : Blo 872567 1964465 := bstep (se 2 (by rfl) ⟨736674, by rfl⟩ : syracuseStep 1964465 = 1473349) B1473349
theorem B1866161 : Blo 872567 1866161 := bstep (se 2 (by rfl) ⟨699810, by rfl⟩ : syracuseStep 1866161 = 1399621) B1399621
theorem B1309121 : Blo 872567 1309121 := bstep (se 2 (by rfl) ⟨490920, by rfl⟩ : syracuseStep 1309121 = 981841) B981841
theorem B1964483 : Blo 872567 1964483 := bstep (se 1 (by rfl) ⟨1473362, by rfl⟩ : syracuseStep 1964483 = 2946725) B2946725
theorem B1309139 : Blo 872567 1309139 := bstep (se 1 (by rfl) ⟨981854, by rfl⟩ : syracuseStep 1309139 = 1963709) B1963709
theorem B1309169 : Blo 872567 1309169 := bstep (se 2 (by rfl) ⟨490938, by rfl⟩ : syracuseStep 1309169 = 981877) B981877
theorem B1473025 : Blo 872567 1473025 := bstep (se 2 (by rfl) ⟨552384, by rfl⟩ : syracuseStep 1473025 = 1104769) B1104769
theorem B1309187 : Blo 872567 1309187 := bstep (se 1 (by rfl) ⟨981890, by rfl⟩ : syracuseStep 1309187 = 1963781) B1963781
theorem B6289933 : Blo 872567 6289933 := bstep (se 3 (by rfl) ⟨1179362, by rfl⟩ : syracuseStep 6289933 = 2358725) B2358725
theorem B3734029 : Blo 872567 3734029 := bstep (se 3 (by rfl) ⟨700130, by rfl⟩ : syracuseStep 3734029 = 1400261) B1400261
theorem B1309217 : Blo 872567 1309217 := bstep (se 2 (by rfl) ⟨490956, by rfl⟩ : syracuseStep 1309217 = 981913) B981913
theorem B1473059 : Blo 872567 1473059 := bstep (se 1 (by rfl) ⟨1104794, by rfl⟩ : syracuseStep 1473059 = 2209589) B2209589
theorem B1309235 : Blo 872567 1309235 := bstep (se 1 (by rfl) ⟨981926, by rfl⟩ : syracuseStep 1309235 = 1963853) B1963853
theorem B95648309 : Blo 872567 95648309 := bstep (se 5 (by rfl) ⟨4483514, by rfl⟩ : syracuseStep 95648309 = 8967029) B8967029
theorem B1309265 : Blo 872567 1309265 := bstep (se 2 (by rfl) ⟨490974, by rfl⟩ : syracuseStep 1309265 = 981949) B981949
theorem B1309283 : Blo 872567 1309283 := bstep (se 1 (by rfl) ⟨981962, by rfl⟩ : syracuseStep 1309283 = 1963925) B1963925
theorem B2947697 : Blo 872567 2947697 := bstep (se 2 (by rfl) ⟨1105386, by rfl⟩ : syracuseStep 2947697 = 2210773) B2210773
theorem B1309313 : Blo 872567 1309313 := bstep (se 2 (by rfl) ⟨490992, by rfl⟩ : syracuseStep 1309313 = 981985) B981985
theorem B1243777 : Blo 872567 1243777 := bstep (se 2 (by rfl) ⟨466416, by rfl⟩ : syracuseStep 1243777 = 932833) B932833
theorem B1309331 : Blo 872567 1309331 := bstep (se 1 (by rfl) ⟨981998, by rfl⟩ : syracuseStep 1309331 = 1963997) B1963997
theorem B1473187 : Blo 872567 1473187 := bstep (se 1 (by rfl) ⟨1104890, by rfl⟩ : syracuseStep 1473187 = 2209781) B2209781
theorem B1309361 : Blo 872567 1309361 := bstep (se 2 (by rfl) ⟨491010, by rfl⟩ : syracuseStep 1309361 = 982021) B982021
theorem B1309379 : Blo 872567 1309379 := bstep (se 1 (by rfl) ⟨982034, by rfl⟩ : syracuseStep 1309379 = 1964069) B1964069
theorem B1964753 : Blo 872567 1964753 := bstep (se 2 (by rfl) ⟨736782, by rfl⟩ : syracuseStep 1964753 = 1473565) B1473565
theorem B981715 : Blo 872567 981715 := bstep (se 1 (by rfl) ⟨736286, by rfl⟩ : syracuseStep 981715 = 1472573) B1472573
theorem B1309409 : Blo 872567 1309409 := bstep (se 2 (by rfl) ⟨491028, by rfl⟩ : syracuseStep 1309409 = 982057) B982057
theorem B1964771 : Blo 872567 1964771 := bstep (se 1 (by rfl) ⟨1473578, by rfl⟩ : syracuseStep 1964771 = 2947157) B2947157
theorem B2489069 : Blo 872567 2489069 := bstep (se 3 (by rfl) ⟨466700, by rfl⟩ : syracuseStep 2489069 = 933401) B933401
theorem B1309427 : Blo 872567 1309427 := bstep (se 1 (by rfl) ⟨982070, by rfl⟩ : syracuseStep 1309427 = 1964141) B1964141
theorem B1309457 : Blo 872567 1309457 := bstep (se 2 (by rfl) ⟨491046, by rfl⟩ : syracuseStep 1309457 = 982093) B982093
theorem B1309475 : Blo 872567 1309475 := bstep (se 1 (by rfl) ⟨982106, by rfl⟩ : syracuseStep 1309475 = 1964213) B1964213
theorem B1473329 : Blo 872567 1473329 := bstep (se 2 (by rfl) ⟨552498, by rfl⟩ : syracuseStep 1473329 = 1104997) B1104997
theorem B1309505 : Blo 872567 1309505 := bstep (se 2 (by rfl) ⟨491064, by rfl⟩ : syracuseStep 1309505 = 982129) B982129
theorem B1309523 : Blo 872567 1309523 := bstep (se 1 (by rfl) ⟨982142, by rfl⟩ : syracuseStep 1309523 = 1964285) B1964285
theorem B981859 : Blo 872567 981859 := bstep (se 1 (by rfl) ⟨736394, by rfl⟩ : syracuseStep 981859 = 1472789) B1472789
theorem B1309553 : Blo 872567 1309553 := bstep (se 2 (by rfl) ⟨491082, by rfl⟩ : syracuseStep 1309553 = 982165) B982165
theorem B1309571 : Blo 872567 1309571 := bstep (se 1 (by rfl) ⟨982178, by rfl⟩ : syracuseStep 1309571 = 1964357) B1964357
theorem B1309601 : Blo 872567 1309601 := bstep (se 2 (by rfl) ⟨491100, by rfl⟩ : syracuseStep 1309601 = 982201) B982201
theorem B2489251 : Blo 872567 2489251 := bstep (se 1 (by rfl) ⟨1866938, by rfl⟩ : syracuseStep 2489251 = 3733877) B3733877
theorem B1473457 : Blo 872567 1473457 := bstep (se 2 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 1473457 = 1105093) B1105093
theorem B1866673 : Blo 872567 1866673 := bstep (se 2 (by rfl) ⟨700002, by rfl⟩ : syracuseStep 1866673 = 1400005) B1400005
theorem B1309619 : Blo 872567 1309619 := bstep (se 1 (by rfl) ⟨982214, by rfl⟩ : syracuseStep 1309619 = 1964429) B1964429
theorem B1309649 : Blo 872567 1309649 := bstep (se 2 (by rfl) ⟨491118, by rfl⟩ : syracuseStep 1309649 = 982237) B982237
theorem B1473491 : Blo 872567 1473491 := bstep (se 1 (by rfl) ⟨1105118, by rfl⟩ : syracuseStep 1473491 = 2210237) B2210237
theorem B1309667 : Blo 872567 1309667 := bstep (se 1 (by rfl) ⟨982250, by rfl⟩ : syracuseStep 1309667 = 1964501) B1964501
theorem B1965041 : Blo 872567 1965041 := bstep (se 2 (by rfl) ⟨736890, by rfl⟩ : syracuseStep 1965041 = 1473781) B1473781
theorem B982003 : Blo 872567 982003 := bstep (se 1 (by rfl) ⟨736502, by rfl⟩ : syracuseStep 982003 = 1473005) B1473005
theorem B1309697 : Blo 872567 1309697 := bstep (se 2 (by rfl) ⟨491136, by rfl⟩ : syracuseStep 1309697 = 982273) B982273
theorem B1965059 : Blo 872567 1965059 := bstep (se 1 (by rfl) ⟨1473794, by rfl⟩ : syracuseStep 1965059 = 2947589) B2947589
theorem B1309715 : Blo 872567 1309715 := bstep (se 1 (by rfl) ⟨982286, by rfl⟩ : syracuseStep 1309715 = 1964573) B1964573
theorem B1309745 : Blo 872567 1309745 := bstep (se 2 (by rfl) ⟨491154, by rfl⟩ : syracuseStep 1309745 = 982309) B982309
theorem B1309763 : Blo 872567 1309763 := bstep (se 1 (by rfl) ⟨982322, by rfl⟩ : syracuseStep 1309763 = 1964645) B1964645
theorem B1473619 : Blo 872567 1473619 := bstep (se 1 (by rfl) ⟨1105214, by rfl⟩ : syracuseStep 1473619 = 2210429) B2210429
theorem B1309793 : Blo 872567 1309793 := bstep (se 2 (by rfl) ⟨491172, by rfl⟩ : syracuseStep 1309793 = 982345) B982345
theorem B1309811 : Blo 872567 1309811 := bstep (se 1 (by rfl) ⟨982358, by rfl⟩ : syracuseStep 1309811 = 1964717) B1964717
theorem B982147 : Blo 872567 982147 := bstep (se 1 (by rfl) ⟨736610, by rfl⟩ : syracuseStep 982147 = 1473221) B1473221
theorem B2948237 : Blo 872567 2948237 := bstep (se 3 (by rfl) ⟨552794, by rfl⟩ : syracuseStep 2948237 = 1105589) B1105589
theorem B1309841 : Blo 872567 1309841 := bstep (se 2 (by rfl) ⟨491190, by rfl⟩ : syracuseStep 1309841 = 982381) B982381
theorem B1309859 : Blo 872567 1309859 := bstep (se 1 (by rfl) ⟨982394, by rfl⟩ : syracuseStep 1309859 = 1964789) B1964789
theorem B5307569 : Blo 872567 5307569 := bstep (se 2 (by rfl) ⟨1990338, by rfl⟩ : syracuseStep 5307569 = 3980677) B3980677
theorem B1309889 : Blo 872567 1309889 := bstep (se 2 (by rfl) ⟨491208, by rfl⟩ : syracuseStep 1309889 = 982417) B982417
theorem B2948291 : Blo 872567 2948291 := bstep (se 1 (by rfl) ⟨2211218, by rfl⟩ : syracuseStep 2948291 = 4422437) B4422437
theorem B1244369 : Blo 872567 1244369 := bstep (se 2 (by rfl) ⟨466638, by rfl⟩ : syracuseStep 1244369 = 933277) B933277
theorem B1309907 : Blo 872567 1309907 := bstep (se 1 (by rfl) ⟨982430, by rfl⟩ : syracuseStep 1309907 = 1964861) B1964861
theorem B1473761 : Blo 872567 1473761 := bstep (se 2 (by rfl) ⟨552660, by rfl⟩ : syracuseStep 1473761 = 1105321) B1105321
theorem B1309937 : Blo 872567 1309937 := bstep (se 2 (by rfl) ⟨491226, by rfl⟩ : syracuseStep 1309937 = 982453) B982453
theorem B1309955 : Blo 872567 1309955 := bstep (se 1 (by rfl) ⟨982466, by rfl⟩ : syracuseStep 1309955 = 1964933) B1964933
theorem B4979981 : Blo 872567 4979981 := bstep (se 3 (by rfl) ⟨933746, by rfl⟩ : syracuseStep 4979981 = 1867493) B1867493
theorem B1965329 : Blo 872567 1965329 := bstep (se 2 (by rfl) ⟨736998, by rfl⟩ : syracuseStep 1965329 = 1473997) B1473997
theorem B982291 : Blo 872567 982291 := bstep (se 1 (by rfl) ⟨736718, by rfl⟩ : syracuseStep 982291 = 1473437) B1473437
theorem B1309985 : Blo 872567 1309985 := bstep (se 2 (by rfl) ⟨491244, by rfl⟩ : syracuseStep 1309985 = 982489) B982489
theorem B1965347 : Blo 872567 1965347 := bstep (se 1 (by rfl) ⟨1474010, by rfl⟩ : syracuseStep 1965347 = 2948021) B2948021
theorem B1310003 : Blo 872567 1310003 := bstep (se 1 (by rfl) ⟨982502, by rfl⟩ : syracuseStep 1310003 = 1965005) B1965005
theorem B1310033 : Blo 872567 1310033 := bstep (se 2 (by rfl) ⟨491262, by rfl⟩ : syracuseStep 1310033 = 982525) B982525
theorem B1473889 : Blo 872567 1473889 := bstep (se 2 (by rfl) ⟨552708, by rfl⟩ : syracuseStep 1473889 = 1105417) B1105417
theorem B1310051 : Blo 872567 1310051 := bstep (se 1 (by rfl) ⟨982538, by rfl⟩ : syracuseStep 1310051 = 1965077) B1965077
theorem B1310081 : Blo 872567 1310081 := bstep (se 2 (by rfl) ⟨491280, by rfl⟩ : syracuseStep 1310081 = 982561) B982561
theorem B1473923 : Blo 872567 1473923 := bstep (se 1 (by rfl) ⟨1105442, by rfl⟩ : syracuseStep 1473923 = 2210885) B2210885
theorem B1080707 : Blo 872567 1080707 := bstep (se 1 (by rfl) ⟨810530, by rfl⟩ : syracuseStep 1080707 = 1621061) B1621061
theorem B2489741 : Blo 872567 2489741 := bstep (se 3 (by rfl) ⟨466826, by rfl⟩ : syracuseStep 2489741 = 933653) B933653
theorem B1310099 : Blo 872567 1310099 := bstep (se 1 (by rfl) ⟨982574, by rfl⟩ : syracuseStep 1310099 = 1965149) B1965149
theorem B982435 : Blo 872567 982435 := bstep (se 1 (by rfl) ⟨736826, by rfl⟩ : syracuseStep 982435 = 1473653) B1473653
theorem B1310129 : Blo 872567 1310129 := bstep (se 2 (by rfl) ⟨491298, by rfl⟩ : syracuseStep 1310129 = 982597) B982597
theorem B1310147 : Blo 872567 1310147 := bstep (se 1 (by rfl) ⟨982610, by rfl⟩ : syracuseStep 1310147 = 1965221) B1965221
theorem B2948561 : Blo 872567 2948561 := bstep (se 2 (by rfl) ⟨1105710, by rfl⟩ : syracuseStep 2948561 = 2211421) B2211421
theorem B1310177 : Blo 872567 1310177 := bstep (se 2 (by rfl) ⟨491316, by rfl⟩ : syracuseStep 1310177 = 982633) B982633
theorem B7962083 : Blo 872567 7962083 := bstep (se 1 (by rfl) ⟨5971562, by rfl⟩ : syracuseStep 7962083 = 11943125) B11943125
theorem B1310195 : Blo 872567 1310195 := bstep (se 1 (by rfl) ⟨982646, by rfl⟩ : syracuseStep 1310195 = 1965293) B1965293
theorem B1474051 : Blo 872567 1474051 := bstep (se 1 (by rfl) ⟨1105538, by rfl⟩ : syracuseStep 1474051 = 2211077) B2211077
theorem B1310225 : Blo 872567 1310225 := bstep (se 2 (by rfl) ⟨491334, by rfl⟩ : syracuseStep 1310225 = 982669) B982669
theorem B1310243 : Blo 872567 1310243 := bstep (se 1 (by rfl) ⟨982682, by rfl⟩ : syracuseStep 1310243 = 1965365) B1965365
theorem B1965617 : Blo 872567 1965617 := bstep (se 2 (by rfl) ⟨737106, by rfl⟩ : syracuseStep 1965617 = 1474213) B1474213
theorem B982579 : Blo 872567 982579 := bstep (se 1 (by rfl) ⟨736934, by rfl⟩ : syracuseStep 982579 = 1473869) B1473869
theorem B1310273 : Blo 872567 1310273 := bstep (se 2 (by rfl) ⟨491352, by rfl⟩ : syracuseStep 1310273 = 982705) B982705
theorem B1965635 : Blo 872567 1965635 := bstep (se 1 (by rfl) ⟨1474226, by rfl⟩ : syracuseStep 1965635 = 2948453) B2948453
theorem B1310291 : Blo 872567 1310291 := bstep (se 1 (by rfl) ⟨982718, by rfl⟩ : syracuseStep 1310291 = 1965437) B1965437
theorem B1310321 : Blo 872567 1310321 := bstep (se 2 (by rfl) ⟨491370, by rfl⟩ : syracuseStep 1310321 = 982741) B982741
theorem B1310339 : Blo 872567 1310339 := bstep (se 1 (by rfl) ⟨982754, by rfl⟩ : syracuseStep 1310339 = 1965509) B1965509
theorem B1474193 : Blo 872567 1474193 := bstep (se 2 (by rfl) ⟨552822, by rfl⟩ : syracuseStep 1474193 = 1105645) B1105645
theorem B1310369 : Blo 872567 1310369 := bstep (se 2 (by rfl) ⟨491388, by rfl⟩ : syracuseStep 1310369 = 982777) B982777
theorem B1310387 : Blo 872567 1310387 := bstep (se 1 (by rfl) ⟨982790, by rfl⟩ : syracuseStep 1310387 = 1965581) B1965581
theorem B982723 : Blo 872567 982723 := bstep (se 1 (by rfl) ⟨737042, by rfl⟩ : syracuseStep 982723 = 1474085) B1474085
theorem B1310417 : Blo 872567 1310417 := bstep (se 2 (by rfl) ⟨491406, by rfl⟩ : syracuseStep 1310417 = 982813) B982813
theorem B1310435 : Blo 872567 1310435 := bstep (se 1 (by rfl) ⟨982826, by rfl⟩ : syracuseStep 1310435 = 1965653) B1965653
theorem B1244899 : Blo 872567 1244899 := bstep (se 1 (by rfl) ⟨933674, by rfl⟩ : syracuseStep 1244899 = 1867349) B1867349
theorem B4423409 : Blo 872567 4423409 := bstep (se 2 (by rfl) ⟨1658778, by rfl⟩ : syracuseStep 4423409 = 3317557) B3317557
theorem B1310465 : Blo 872567 1310465 := bstep (se 2 (by rfl) ⟨491424, by rfl⟩ : syracuseStep 1310465 = 982849) B982849
theorem B1474321 : Blo 872567 1474321 := bstep (se 2 (by rfl) ⟨552870, by rfl⟩ : syracuseStep 1474321 = 1105741) B1105741
theorem B1310483 : Blo 872567 1310483 := bstep (se 1 (by rfl) ⟨982862, by rfl⟩ : syracuseStep 1310483 = 1965725) B1965725
theorem B1310513 : Blo 872567 1310513 := bstep (se 2 (by rfl) ⟨491442, by rfl⟩ : syracuseStep 1310513 = 982885) B982885
theorem B1474355 : Blo 872567 1474355 := bstep (se 1 (by rfl) ⟨1105766, by rfl⟩ : syracuseStep 1474355 = 2211533) B2211533
theorem B1310531 : Blo 872567 1310531 := bstep (se 1 (by rfl) ⟨982898, by rfl⟩ : syracuseStep 1310531 = 1965797) B1965797
theorem B1965905 : Blo 872567 1965905 := bstep (se 2 (by rfl) ⟨737214, by rfl⟩ : syracuseStep 1965905 = 1474429) B1474429
theorem B982867 : Blo 872567 982867 := bstep (se 1 (by rfl) ⟨737150, by rfl⟩ : syracuseStep 982867 = 1474301) B1474301
theorem B1310561 : Blo 872567 1310561 := bstep (se 2 (by rfl) ⟨491460, by rfl⟩ : syracuseStep 1310561 = 982921) B982921
theorem B884579 : Blo 872567 884579 := bstep (se 1 (by rfl) ⟨663434, by rfl⟩ : syracuseStep 884579 = 1326869) B1326869
theorem B1965923 : Blo 872567 1965923 := bstep (se 1 (by rfl) ⟨1474442, by rfl⟩ : syracuseStep 1965923 = 2948885) B2948885
theorem B1310579 : Blo 872567 1310579 := bstep (se 1 (by rfl) ⟨982934, by rfl⟩ : syracuseStep 1310579 = 1965869) B1965869
theorem B884611 : Blo 872567 884611 := bstep (se 1 (by rfl) ⟨663458, by rfl⟩ : syracuseStep 884611 = 1326917) B1326917
theorem B1310609 : Blo 872567 1310609 := bstep (se 2 (by rfl) ⟨491478, by rfl⟩ : syracuseStep 1310609 = 982957) B982957
theorem B1310627 : Blo 872567 1310627 := bstep (se 1 (by rfl) ⟨982970, by rfl⟩ : syracuseStep 1310627 = 1965941) B1965941
theorem B1474483 : Blo 872567 1474483 := bstep (se 1 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 1474483 = 2211725) B2211725
theorem B1310657 : Blo 872567 1310657 := bstep (se 2 (by rfl) ⟨491496, by rfl⟩ : syracuseStep 1310657 = 982993) B982993
theorem B1310675 : Blo 872567 1310675 := bstep (se 1 (by rfl) ⟨983006, by rfl⟩ : syracuseStep 1310675 = 1966013) B1966013
theorem B983011 : Blo 872567 983011 := bstep (se 1 (by rfl) ⟨737258, by rfl⟩ : syracuseStep 983011 = 1474517) B1474517
theorem B2949101 : Blo 872567 2949101 := bstep (se 3 (by rfl) ⟨552956, by rfl⟩ : syracuseStep 2949101 = 1105913) B1105913
theorem B1310705 : Blo 872567 1310705 := bstep (se 2 (by rfl) ⟨491514, by rfl⟩ : syracuseStep 1310705 = 983029) B983029
theorem B1474571 : Blo 872567 1474571 := bstep (se 1 (by rfl) ⟨1105928, by rfl⟩ : syracuseStep 1474571 = 2211857) B2211857
theorem B1966103 : Blo 872567 1966103 := bstep (se 1 (by rfl) ⟨1474577, by rfl⟩ : syracuseStep 1966103 = 2949155) B2949155
theorem B1867801 : Blo 872567 1867801 := bstep (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) B1400851
theorem B983083 : Blo 872567 983083 := bstep (se 1 (by rfl) ⟨737312, by rfl⟩ : syracuseStep 983083 = 1474625) B1474625
theorem B1310795 : Blo 872567 1310795 := bstep (se 1 (by rfl) ⟨983096, by rfl⟩ : syracuseStep 1310795 = 1966193) B1966193
theorem B1310807 : Blo 872567 1310807 := bstep (se 1 (by rfl) ⟨983105, by rfl⟩ : syracuseStep 1310807 = 1966211) B1966211
theorem B2949209 : Blo 872567 2949209 := bstep (se 2 (by rfl) ⟨1105953, by rfl⟩ : syracuseStep 2949209 = 2211907) B2211907
theorem B1474699 : Blo 872567 1474699 := bstep (se 1 (by rfl) ⟨1106024, by rfl⟩ : syracuseStep 1474699 = 2212049) B2212049
theorem B983191 : Blo 872567 983191 := bstep (se 1 (by rfl) ⟨737393, by rfl⟩ : syracuseStep 983191 = 1474787) B1474787
theorem B1310873 : Blo 872567 1310873 := bstep (se 2 (by rfl) ⟨491577, by rfl⟩ : syracuseStep 1310873 = 983155) B983155
theorem B1966283 : Blo 872567 1966283 := bstep (se 1 (by rfl) ⟨1474712, by rfl⟩ : syracuseStep 1966283 = 2949425) B2949425
theorem B1966337 : Blo 872567 1966337 := bstep (se 2 (by rfl) ⟨737376, by rfl⟩ : syracuseStep 1966337 = 1474753) B1474753
theorem B1310987 : Blo 872567 1310987 := bstep (se 1 (by rfl) ⟨983240, by rfl⟩ : syracuseStep 1310987 = 1966481) B1966481
theorem B1245451 : Blo 872567 1245451 := bstep (se 1 (by rfl) ⟨934088, by rfl⟩ : syracuseStep 1245451 = 1868177) B1868177
theorem B1310999 : Blo 872567 1310999 := bstep (se 1 (by rfl) ⟨983249, by rfl⟩ : syracuseStep 1310999 = 1966499) B1966499
theorem B1474841 : Blo 872567 1474841 := bstep (se 2 (by rfl) ⟨553065, by rfl⟩ : syracuseStep 1474841 = 1106131) B1106131
theorem B983371 : Blo 872567 983371 := bstep (se 1 (by rfl) ⟨737528, by rfl⟩ : syracuseStep 983371 = 1475057) B1475057
theorem B1311065 : Blo 872567 1311065 := bstep (se 2 (by rfl) ⟨491649, by rfl⟩ : syracuseStep 1311065 = 983299) B983299
theorem B1180055 : Blo 872567 1180055 := bstep (se 1 (by rfl) ⟨885041, by rfl⟩ : syracuseStep 1180055 = 1770083) B1770083
theorem B1474969 : Blo 872567 1474969 := bstep (se 2 (by rfl) ⟨553113, by rfl⟩ : syracuseStep 1474969 = 1106227) B1106227
theorem B885163 : Blo 872567 885163 := bstep (se 1 (by rfl) ⟨663872, by rfl⟩ : syracuseStep 885163 = 1327745) B1327745
theorem B983479 : Blo 872567 983479 := bstep (se 1 (by rfl) ⟨737609, by rfl⟩ : syracuseStep 983479 = 1475219) B1475219
theorem B1311179 : Blo 872567 1311179 := bstep (se 1 (by rfl) ⟨983384, by rfl⟩ : syracuseStep 1311179 = 1966769) B1966769
theorem B7668173 : Blo 872567 7668173 := bstep (se 3 (by rfl) ⟨1437782, by rfl⟩ : syracuseStep 7668173 = 2875565) B2875565
theorem B1311191 : Blo 872567 1311191 := bstep (se 1 (by rfl) ⟨983393, by rfl⟩ : syracuseStep 1311191 = 1966787) B1966787
theorem B1966553 : Blo 872567 1966553 := bstep (se 2 (by rfl) ⟨737457, by rfl⟩ : syracuseStep 1966553 = 1474915) B1474915
theorem B1245719 : Blo 872567 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B1311257 : Blo 872567 1311257 := bstep (se 2 (by rfl) ⟨491721, by rfl⟩ : syracuseStep 1311257 = 983443) B983443
theorem B1966643 : Blo 872567 1966643 := bstep (se 1 (by rfl) ⟨1474982, by rfl⟩ : syracuseStep 1966643 = 2949965) B2949965
theorem B3736115 : Blo 872567 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B1966679 : Blo 872567 1966679 := bstep (se 1 (by rfl) ⟨1475009, by rfl⟩ : syracuseStep 1966679 = 2950019) B2950019
theorem B983659 : Blo 872567 983659 := bstep (se 1 (by rfl) ⟨737744, by rfl⟩ : syracuseStep 983659 = 1475489) B1475489
theorem B1311371 : Blo 872567 1311371 := bstep (se 1 (by rfl) ⟨983528, by rfl⟩ : syracuseStep 1311371 = 1967057) B1967057
theorem B1311383 : Blo 872567 1311383 := bstep (se 1 (by rfl) ⟨983537, by rfl⟩ : syracuseStep 1311383 = 1967075) B1967075
theorem B7570097 : Blo 872567 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B983767 : Blo 872567 983767 := bstep (se 1 (by rfl) ⟨737825, by rfl⟩ : syracuseStep 983767 = 1475651) B1475651
theorem B1311449 : Blo 872567 1311449 := bstep (se 2 (by rfl) ⟨491793, by rfl⟩ : syracuseStep 1311449 = 983587) B983587
theorem B1966859 : Blo 872567 1966859 := bstep (se 1 (by rfl) ⟨1475144, by rfl⟩ : syracuseStep 1966859 = 2950289) B2950289
theorem B6292241 : Blo 872567 6292241 := bstep (se 2 (by rfl) ⟨2359590, by rfl⟩ : syracuseStep 6292241 = 4719181) B4719181
theorem B2360087 : Blo 872567 2360087 := bstep (se 1 (by rfl) ⟨1770065, by rfl⟩ : syracuseStep 2360087 = 3540131) B3540131
theorem B2949911 : Blo 872567 2949911 := bstep (se 1 (by rfl) ⟨2212433, by rfl⟩ : syracuseStep 2949911 = 4424867) B4424867
theorem B2097971 : Blo 872567 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B1966913 : Blo 872567 1966913 := bstep (se 2 (by rfl) ⟨737592, by rfl⟩ : syracuseStep 1966913 = 1475185) B1475185
theorem B1311563 : Blo 872567 1311563 := bstep (se 1 (by rfl) ⟨983672, by rfl⟩ : syracuseStep 1311563 = 1967345) B1967345
theorem B1311575 : Blo 872567 1311575 := bstep (se 1 (by rfl) ⟨983681, by rfl⟩ : syracuseStep 1311575 = 1967363) B1967363
theorem B983947 : Blo 872567 983947 := bstep (se 1 (by rfl) ⟨737960, by rfl⟩ : syracuseStep 983947 = 1475921) B1475921
theorem B3539857 : Blo 872567 3539857 := bstep (se 2 (by rfl) ⟨1327446, by rfl⟩ : syracuseStep 3539857 = 2654893) B2654893
theorem B1311641 : Blo 872567 1311641 := bstep (se 2 (by rfl) ⟨491865, by rfl⟩ : syracuseStep 1311641 = 983731) B983731
theorem B1475543 : Blo 872567 1475543 := bstep (se 1 (by rfl) ⟨1106657, by rfl⟩ : syracuseStep 1475543 = 2213315) B2213315
theorem B984055 : Blo 872567 984055 := bstep (se 1 (by rfl) ⟨738041, by rfl⟩ : syracuseStep 984055 = 1476083) B1476083
theorem B1311755 : Blo 872567 1311755 := bstep (se 1 (by rfl) ⟨983816, by rfl⟩ : syracuseStep 1311755 = 1967633) B1967633
theorem B9962513 : Blo 872567 9962513 := bstep (se 2 (by rfl) ⟨3735942, by rfl⟩ : syracuseStep 9962513 = 7471885) B7471885
theorem B1311767 : Blo 872567 1311767 := bstep (se 1 (by rfl) ⟨983825, by rfl⟩ : syracuseStep 1311767 = 1967651) B1967651
theorem B1967129 : Blo 872567 1967129 := bstep (se 2 (by rfl) ⟨737673, by rfl⟩ : syracuseStep 1967129 = 1475347) B1475347
theorem B1180747 : Blo 872567 1180747 := bstep (se 1 (by rfl) ⟨885560, by rfl⟩ : syracuseStep 1180747 = 1771121) B1771121
theorem B24249419 : Blo 872567 24249419 := bstep (se 1 (by rfl) ⟨18187064, by rfl⟩ : syracuseStep 24249419 = 36374129) B36374129
theorem B1475671 : Blo 872567 1475671 := bstep (se 1 (by rfl) ⟨1106753, by rfl⟩ : syracuseStep 1475671 = 2213507) B2213507
theorem B1311833 : Blo 872567 1311833 := bstep (se 2 (by rfl) ⟨491937, by rfl⟩ : syracuseStep 1311833 = 983875) B983875
theorem B1967219 : Blo 872567 1967219 := bstep (se 1 (by rfl) ⟨1475414, by rfl⟩ : syracuseStep 1967219 = 2950829) B2950829
theorem B3146897 : Blo 872567 3146897 := bstep (se 2 (by rfl) ⟨1180086, by rfl⟩ : syracuseStep 3146897 = 2360173) B2360173
theorem B1967255 : Blo 872567 1967255 := bstep (se 1 (by rfl) ⟨1475441, by rfl⟩ : syracuseStep 1967255 = 2950883) B2950883
theorem B984235 : Blo 872567 984235 := bstep (se 1 (by rfl) ⟨738176, by rfl⟩ : syracuseStep 984235 = 1476353) B1476353
theorem B1311947 : Blo 872567 1311947 := bstep (se 1 (by rfl) ⟨983960, by rfl⟩ : syracuseStep 1311947 = 1967921) B1967921
theorem B1311959 : Blo 872567 1311959 := bstep (se 1 (by rfl) ⟨983969, by rfl⟩ : syracuseStep 1311959 = 1967939) B1967939
theorem B984343 : Blo 872567 984343 := bstep (se 1 (by rfl) ⟨738257, by rfl⟩ : syracuseStep 984343 = 1476515) B1476515
theorem B1312025 : Blo 872567 1312025 := bstep (se 2 (by rfl) ⟨492009, by rfl⟩ : syracuseStep 1312025 = 984019) B984019
theorem B2950451 : Blo 872567 2950451 := bstep (se 1 (by rfl) ⟨2212838, by rfl⟩ : syracuseStep 2950451 = 4425677) B4425677
theorem B1967435 : Blo 872567 1967435 := bstep (se 1 (by rfl) ⟨1475576, by rfl⟩ : syracuseStep 1967435 = 2951153) B2951153
theorem B1967489 : Blo 872567 1967489 := bstep (se 2 (by rfl) ⟨737808, by rfl⟩ : syracuseStep 1967489 = 1475617) B1475617
theorem B4982147 : Blo 872567 4982147 := bstep (se 1 (by rfl) ⟨3736610, by rfl⟩ : syracuseStep 4982147 = 7473221) B7473221
theorem B1312139 : Blo 872567 1312139 := bstep (se 1 (by rfl) ⟨984104, by rfl⟩ : syracuseStep 1312139 = 1968209) B1968209
theorem B1312151 : Blo 872567 1312151 := bstep (se 1 (by rfl) ⟨984113, by rfl⟩ : syracuseStep 1312151 = 1968227) B1968227
theorem B984523 : Blo 872567 984523 := bstep (se 1 (by rfl) ⟨738392, by rfl⟩ : syracuseStep 984523 = 1476785) B1476785
theorem B1312217 : Blo 872567 1312217 := bstep (se 2 (by rfl) ⟨492081, by rfl⟩ : syracuseStep 1312217 = 984163) B984163
theorem B1246681 : Blo 872567 1246681 := bstep (se 2 (by rfl) ⟨467505, by rfl⟩ : syracuseStep 1246681 = 935011) B935011
theorem B984631 : Blo 872567 984631 := bstep (se 1 (by rfl) ⟨738473, by rfl⟩ : syracuseStep 984631 = 1476947) B1476947
theorem B2950721 : Blo 872567 2950721 := bstep (se 2 (by rfl) ⟨1106520, by rfl⟩ : syracuseStep 2950721 = 2213041) B2213041
theorem B1312331 : Blo 872567 1312331 := bstep (se 1 (by rfl) ⟨984248, by rfl⟩ : syracuseStep 1312331 = 1968497) B1968497
theorem B1312343 : Blo 872567 1312343 := bstep (se 1 (by rfl) ⟨984257, by rfl⟩ : syracuseStep 1312343 = 1968515) B1968515
theorem B1967705 : Blo 872567 1967705 := bstep (se 2 (by rfl) ⟨737889, by rfl⟩ : syracuseStep 1967705 = 1475779) B1475779
theorem B28345949 : Blo 872567 28345949 := bstep (se 3 (by rfl) ⟨5314865, by rfl⟩ : syracuseStep 28345949 = 10629731) B10629731
theorem B1312409 : Blo 872567 1312409 := bstep (se 2 (by rfl) ⟨492153, by rfl⟩ : syracuseStep 1312409 = 984307) B984307
theorem B1967795 : Blo 872567 1967795 := bstep (se 1 (by rfl) ⟨1475846, by rfl⟩ : syracuseStep 1967795 = 2951693) B2951693
theorem B1476299 : Blo 872567 1476299 := bstep (se 1 (by rfl) ⟨1107224, by rfl⟩ : syracuseStep 1476299 = 2214449) B2214449
theorem B1967831 : Blo 872567 1967831 := bstep (se 1 (by rfl) ⟨1475873, by rfl⟩ : syracuseStep 1967831 = 2951747) B2951747
theorem B984811 : Blo 872567 984811 := bstep (se 1 (by rfl) ⟨738608, by rfl⟩ : syracuseStep 984811 = 1477217) B1477217
theorem B1312523 : Blo 872567 1312523 := bstep (se 1 (by rfl) ⟨984392, by rfl⟩ : syracuseStep 1312523 = 1968785) B1968785
theorem B1312535 : Blo 872567 1312535 := bstep (se 1 (by rfl) ⟨984401, by rfl⟩ : syracuseStep 1312535 = 1968803) B1968803
theorem B1476427 : Blo 872567 1476427 := bstep (se 1 (by rfl) ⟨1107320, by rfl⟩ : syracuseStep 1476427 = 2214641) B2214641
theorem B984919 : Blo 872567 984919 := bstep (se 1 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 984919 = 1477379) B1477379
theorem B1312601 : Blo 872567 1312601 := bstep (se 2 (by rfl) ⟨492225, by rfl⟩ : syracuseStep 1312601 = 984451) B984451
theorem B1968011 : Blo 872567 1968011 := bstep (se 1 (by rfl) ⟨1476008, by rfl⟩ : syracuseStep 1968011 = 2952017) B2952017
theorem B1968065 : Blo 872567 1968065 := bstep (se 2 (by rfl) ⟨738024, by rfl⟩ : syracuseStep 1968065 = 1476049) B1476049
theorem B1312715 : Blo 872567 1312715 := bstep (se 1 (by rfl) ⟨984536, by rfl⟩ : syracuseStep 1312715 = 1969073) B1969073
theorem B1312727 : Blo 872567 1312727 := bstep (se 1 (by rfl) ⟨984545, by rfl⟩ : syracuseStep 1312727 = 1969091) B1969091
theorem B1476569 : Blo 872567 1476569 := bstep (se 2 (by rfl) ⟨553713, by rfl⟩ : syracuseStep 1476569 = 1107427) B1107427
theorem B3835907 : Blo 872567 3835907 := bstep (se 1 (by rfl) ⟨2876930, by rfl⟩ : syracuseStep 3835907 = 5753861) B5753861
theorem B985099 : Blo 872567 985099 := bstep (se 1 (by rfl) ⟨738824, by rfl⟩ : syracuseStep 985099 = 1477649) B1477649
theorem B1312793 : Blo 872567 1312793 := bstep (se 2 (by rfl) ⟨492297, by rfl⟩ : syracuseStep 1312793 = 984595) B984595
theorem B1181785 : Blo 872567 1181785 := bstep (se 2 (by rfl) ⟨443169, by rfl⟩ : syracuseStep 1181785 = 886339) B886339
theorem B1476697 : Blo 872567 1476697 := bstep (se 2 (by rfl) ⟨553761, by rfl⟩ : syracuseStep 1476697 = 1107523) B1107523
theorem B2951261 : Blo 872567 2951261 := bstep (se 3 (by rfl) ⟨553361, by rfl⟩ : syracuseStep 2951261 = 1106723) B1106723
theorem B985207 : Blo 872567 985207 := bstep (se 1 (by rfl) ⟨738905, by rfl⟩ : syracuseStep 985207 = 1477811) B1477811
theorem B1312907 : Blo 872567 1312907 := bstep (se 1 (by rfl) ⟨984680, by rfl⟩ : syracuseStep 1312907 = 1969361) B1969361
theorem B1312919 : Blo 872567 1312919 := bstep (se 1 (by rfl) ⟨984689, by rfl⟩ : syracuseStep 1312919 = 1969379) B1969379
theorem B1968281 : Blo 872567 1968281 := bstep (se 2 (by rfl) ⟨738105, by rfl⟩ : syracuseStep 1968281 = 1476211) B1476211
theorem B6817969 : Blo 872567 6817969 := bstep (se 2 (by rfl) ⟨2556738, by rfl⟩ : syracuseStep 6817969 = 5113477) B5113477
theorem B1181899 : Blo 872567 1181899 := bstep (se 1 (by rfl) ⟨886424, by rfl⟩ : syracuseStep 1181899 = 1772849) B1772849
theorem B1312985 : Blo 872567 1312985 := bstep (se 2 (by rfl) ⟨492369, by rfl⟩ : syracuseStep 1312985 = 984739) B984739
theorem B2492633 : Blo 872567 2492633 := bstep (se 2 (by rfl) ⟨934737, by rfl⟩ : syracuseStep 2492633 = 1869475) B1869475
theorem B1968371 : Blo 872567 1968371 := bstep (se 1 (by rfl) ⟨1476278, by rfl⟩ : syracuseStep 1968371 = 2952557) B2952557
theorem B4426001 : Blo 872567 4426001 := bstep (se 2 (by rfl) ⟨1659750, by rfl⟩ : syracuseStep 4426001 = 3319501) B3319501
theorem B1968407 : Blo 872567 1968407 := bstep (se 1 (by rfl) ⟨1476305, by rfl⟩ : syracuseStep 1968407 = 2952611) B2952611
theorem B985387 : Blo 872567 985387 := bstep (se 1 (by rfl) ⟨739040, by rfl⟩ : syracuseStep 985387 = 1478081) B1478081
theorem B1313099 : Blo 872567 1313099 := bstep (se 1 (by rfl) ⟨984824, by rfl⟩ : syracuseStep 1313099 = 1969649) B1969649
theorem B1313111 : Blo 872567 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B1870219 : Blo 872567 1870219 := bstep (se 1 (by rfl) ⟨1402664, by rfl⟩ : syracuseStep 1870219 = 2805329) B2805329
theorem B985495 : Blo 872567 985495 := bstep (se 1 (by rfl) ⟨739121, by rfl⟩ : syracuseStep 985495 = 1478243) B1478243
theorem B1313177 : Blo 872567 1313177 := bstep (se 2 (by rfl) ⟨492441, by rfl⟩ : syracuseStep 1313177 = 984883) B984883
theorem B4426163 : Blo 872567 4426163 := bstep (se 1 (by rfl) ⟨3319622, by rfl⟩ : syracuseStep 4426163 = 6639245) B6639245
theorem B1968587 : Blo 872567 1968587 := bstep (se 1 (by rfl) ⟨1476440, by rfl⟩ : syracuseStep 1968587 = 2952881) B2952881
theorem B1870295 : Blo 872567 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B1968641 : Blo 872567 1968641 := bstep (se 2 (by rfl) ⟨738240, by rfl⟩ : syracuseStep 1968641 = 1476481) B1476481
theorem B1313291 : Blo 872567 1313291 := bstep (se 1 (by rfl) ⟨984968, by rfl⟩ : syracuseStep 1313291 = 1969937) B1969937
theorem B1313303 : Blo 872567 1313303 := bstep (se 1 (by rfl) ⟨984977, by rfl⟩ : syracuseStep 1313303 = 1969955) B1969955
theorem B985675 : Blo 872567 985675 := bstep (se 1 (by rfl) ⟨739256, by rfl⟩ : syracuseStep 985675 = 1478513) B1478513
theorem B1313369 : Blo 872567 1313369 := bstep (se 2 (by rfl) ⟨492513, by rfl⟩ : syracuseStep 1313369 = 985027) B985027
theorem B1477271 : Blo 872567 1477271 := bstep (se 1 (by rfl) ⟨1107953, by rfl⟩ : syracuseStep 1477271 = 2215907) B2215907
theorem B8096435 : Blo 872567 8096435 := bstep (se 1 (by rfl) ⟨6072326, by rfl⟩ : syracuseStep 8096435 = 12144653) B12144653
theorem B985783 : Blo 872567 985783 := bstep (se 1 (by rfl) ⟨739337, by rfl⟩ : syracuseStep 985783 = 1478675) B1478675
theorem B1313483 : Blo 872567 1313483 := bstep (se 1 (by rfl) ⟨985112, by rfl⟩ : syracuseStep 1313483 = 1970225) B1970225
theorem B7473869 : Blo 872567 7473869 := bstep (se 3 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 7473869 = 2802701) B2802701
theorem B1313495 : Blo 872567 1313495 := bstep (se 1 (by rfl) ⟨985121, by rfl⟩ : syracuseStep 1313495 = 1970243) B1970243
theorem B1968857 : Blo 872567 1968857 := bstep (se 2 (by rfl) ⟨738321, by rfl⟩ : syracuseStep 1968857 = 1476643) B1476643
theorem B1477399 : Blo 872567 1477399 := bstep (se 1 (by rfl) ⟨1108049, by rfl⟩ : syracuseStep 1477399 = 2216099) B2216099
theorem B1313561 : Blo 872567 1313561 := bstep (se 2 (by rfl) ⟨492585, by rfl⟩ : syracuseStep 1313561 = 985171) B985171
theorem B1968947 : Blo 872567 1968947 := bstep (se 1 (by rfl) ⟨1476710, by rfl⟩ : syracuseStep 1968947 = 2953421) B2953421
theorem B1968983 : Blo 872567 1968983 := bstep (se 1 (by rfl) ⟨1476737, by rfl⟩ : syracuseStep 1968983 = 2953475) B2953475
theorem B985963 : Blo 872567 985963 := bstep (se 1 (by rfl) ⟨739472, by rfl⟩ : syracuseStep 985963 = 1478945) B1478945
theorem B1313675 : Blo 872567 1313675 := bstep (se 1 (by rfl) ⟨985256, by rfl⟩ : syracuseStep 1313675 = 1970513) B1970513
theorem B1313687 : Blo 872567 1313687 := bstep (se 1 (by rfl) ⟨985265, by rfl⟩ : syracuseStep 1313687 = 1970531) B1970531
theorem B986071 : Blo 872567 986071 := bstep (se 1 (by rfl) ⟨739553, by rfl⟩ : syracuseStep 986071 = 1479107) B1479107
theorem B1313753 : Blo 872567 1313753 := bstep (se 2 (by rfl) ⟨492657, by rfl⟩ : syracuseStep 1313753 = 985315) B985315
theorem B1969163 : Blo 872567 1969163 := bstep (se 1 (by rfl) ⟨1476872, by rfl⟩ : syracuseStep 1969163 = 2953745) B2953745
theorem B1969217 : Blo 872567 1969217 := bstep (se 2 (by rfl) ⟨738456, by rfl⟩ : syracuseStep 1969217 = 1476913) B1476913
theorem B1313867 : Blo 872567 1313867 := bstep (se 1 (by rfl) ⟨985400, by rfl⟩ : syracuseStep 1313867 = 1970801) B1970801
theorem B1313879 : Blo 872567 1313879 := bstep (se 1 (by rfl) ⟨985409, by rfl⟩ : syracuseStep 1313879 = 1970819) B1970819
theorem B1313945 : Blo 872567 1313945 := bstep (se 2 (by rfl) ⟨492729, by rfl⟩ : syracuseStep 1313945 = 985459) B985459
theorem B3148973 : Blo 872567 3148973 := bstep (se 3 (by rfl) ⟨590432, by rfl⟩ : syracuseStep 3148973 = 1180865) B1180865
theorem B2952395 : Blo 872567 2952395 := bstep (se 1 (by rfl) ⟨2214296, by rfl⟩ : syracuseStep 2952395 = 4428593) B4428593
theorem B1182937 : Blo 872567 1182937 := bstep (se 2 (by rfl) ⟨443601, by rfl⟩ : syracuseStep 1182937 = 887203) B887203
theorem B1314059 : Blo 872567 1314059 := bstep (se 1 (by rfl) ⟨985544, by rfl⟩ : syracuseStep 1314059 = 1971089) B1971089
theorem B1314071 : Blo 872567 1314071 := bstep (se 1 (by rfl) ⟨985553, by rfl⟩ : syracuseStep 1314071 = 1971107) B1971107
theorem B1969433 : Blo 872567 1969433 := bstep (se 2 (by rfl) ⟨738537, by rfl⟩ : syracuseStep 1969433 = 1477075) B1477075
theorem B1314137 : Blo 872567 1314137 := bstep (se 2 (by rfl) ⟨492801, by rfl⟩ : syracuseStep 1314137 = 985603) B985603
theorem B1969523 : Blo 872567 1969523 := bstep (se 1 (by rfl) ⟨1477142, by rfl⟩ : syracuseStep 1969523 = 2954285) B2954285
theorem B1478027 : Blo 872567 1478027 := bstep (se 1 (by rfl) ⟨1108520, by rfl⟩ : syracuseStep 1478027 = 2217041) B2217041
theorem B1969559 : Blo 872567 1969559 := bstep (se 1 (by rfl) ⟨1477169, by rfl⟩ : syracuseStep 1969559 = 2954339) B2954339
theorem B2493899 : Blo 872567 2493899 := bstep (se 1 (by rfl) ⟨1870424, by rfl⟩ : syracuseStep 2493899 = 3740849) B3740849
theorem B1314251 : Blo 872567 1314251 := bstep (se 1 (by rfl) ⟨985688, by rfl⟩ : syracuseStep 1314251 = 1971377) B1971377
theorem B1314263 : Blo 872567 1314263 := bstep (se 1 (by rfl) ⟨985697, by rfl⟩ : syracuseStep 1314263 = 1971395) B1971395
theorem B2952665 : Blo 872567 2952665 := bstep (se 2 (by rfl) ⟨1107249, by rfl⟩ : syracuseStep 2952665 = 2214499) B2214499
theorem B1478155 : Blo 872567 1478155 := bstep (se 1 (by rfl) ⟨1108616, by rfl⟩ : syracuseStep 1478155 = 2217233) B2217233
theorem B3313169 : Blo 872567 3313169 := bstep (se 2 (by rfl) ⟨1242438, by rfl⟩ : syracuseStep 3313169 = 2484877) B2484877
theorem B1314329 : Blo 872567 1314329 := bstep (se 2 (by rfl) ⟨492873, by rfl⟩ : syracuseStep 1314329 = 985747) B985747
theorem B1969739 : Blo 872567 1969739 := bstep (se 1 (by rfl) ⟨1477304, by rfl⟩ : syracuseStep 1969739 = 2954609) B2954609
theorem B1969793 : Blo 872567 1969793 := bstep (se 2 (by rfl) ⟨738672, by rfl⟩ : syracuseStep 1969793 = 1477345) B1477345
theorem B1314443 : Blo 872567 1314443 := bstep (se 1 (by rfl) ⟨985832, by rfl⟩ : syracuseStep 1314443 = 1971665) B1971665
theorem B1314455 : Blo 872567 1314455 := bstep (se 1 (by rfl) ⟨985841, by rfl⟩ : syracuseStep 1314455 = 1971683) B1971683
theorem B1478297 : Blo 872567 1478297 := bstep (se 2 (by rfl) ⟨554361, by rfl⟩ : syracuseStep 1478297 = 1108723) B1108723
theorem B4984537 : Blo 872567 4984537 := bstep (se 2 (by rfl) ⟨1869201, by rfl⟩ : syracuseStep 4984537 = 3738403) B3738403
theorem B1314521 : Blo 872567 1314521 := bstep (se 2 (by rfl) ⟨492945, by rfl⟩ : syracuseStep 1314521 = 985891) B985891
theorem B1478425 : Blo 872567 1478425 := bstep (se 2 (by rfl) ⟨554409, by rfl⟩ : syracuseStep 1478425 = 1108819) B1108819
theorem B1314635 : Blo 872567 1314635 := bstep (se 1 (by rfl) ⟨985976, by rfl⟩ : syracuseStep 1314635 = 1971953) B1971953
theorem B1314647 : Blo 872567 1314647 := bstep (se 1 (by rfl) ⟨985985, by rfl⟩ : syracuseStep 1314647 = 1971971) B1971971
theorem B1970009 : Blo 872567 1970009 := bstep (se 2 (by rfl) ⟨738753, by rfl⟩ : syracuseStep 1970009 = 1477507) B1477507
theorem B9965429 : Blo 872567 9965429 := bstep (se 5 (by rfl) ⟨467129, by rfl⟩ : syracuseStep 9965429 = 934259) B934259
theorem B1314713 : Blo 872567 1314713 := bstep (se 2 (by rfl) ⟨493017, by rfl⟩ : syracuseStep 1314713 = 986035) B986035
theorem B1970099 : Blo 872567 1970099 := bstep (se 1 (by rfl) ⟨1477574, by rfl⟩ : syracuseStep 1970099 = 2955149) B2955149
theorem B1970135 : Blo 872567 1970135 := bstep (se 1 (by rfl) ⟨1477601, by rfl⟩ : syracuseStep 1970135 = 2955203) B2955203
theorem B1314827 : Blo 872567 1314827 := bstep (se 1 (by rfl) ⟨986120, by rfl⟩ : syracuseStep 1314827 = 1972241) B1972241
theorem B1314839 : Blo 872567 1314839 := bstep (se 1 (by rfl) ⟨986129, by rfl⟩ : syracuseStep 1314839 = 1972259) B1972259
theorem B30642245 : Blo 872567 30642245 := bstep (se 4 (by rfl) ⟨2872710, by rfl⟩ : syracuseStep 30642245 = 5745421) B5745421
theorem B3543115 : Blo 872567 3543115 := bstep (se 1 (by rfl) ⟨2657336, by rfl⟩ : syracuseStep 3543115 = 5314673) B5314673
theorem B1577075 : Blo 872567 1577075 := bstep (se 1 (by rfl) ⟨1182806, by rfl⟩ : syracuseStep 1577075 = 2365613) B2365613
theorem B1970315 : Blo 872567 1970315 := bstep (se 1 (by rfl) ⟨1477736, by rfl⟩ : syracuseStep 1970315 = 2955473) B2955473
theorem B2953367 : Blo 872567 2953367 := bstep (se 1 (by rfl) ⟨2215025, by rfl⟩ : syracuseStep 2953367 = 4430051) B4430051
theorem B1970369 : Blo 872567 1970369 := bstep (se 2 (by rfl) ⟨738888, by rfl⟩ : syracuseStep 1970369 = 1477777) B1477777
theorem B1872065 : Blo 872567 1872065 := bstep (se 2 (by rfl) ⟨702024, by rfl⟩ : syracuseStep 1872065 = 1404049) B1404049
theorem B1052887 : Blo 872567 1052887 := bstep (se 1 (by rfl) ⟨789665, by rfl⟩ : syracuseStep 1052887 = 1579331) B1579331
theorem B3739907 : Blo 872567 3739907 := bstep (se 1 (by rfl) ⟨2804930, by rfl⟩ : syracuseStep 3739907 = 5609861) B5609861
theorem B3313943 : Blo 872567 3313943 := bstep (se 1 (by rfl) ⟨2485457, by rfl⟩ : syracuseStep 3313943 = 4970915) B4970915
theorem B4428107 : Blo 872567 4428107 := bstep (se 1 (by rfl) ⟨3321080, by rfl⟩ : syracuseStep 4428107 = 6642161) B6642161
theorem B1478999 : Blo 872567 1478999 := bstep (se 1 (by rfl) ⟨1109249, by rfl⟩ : syracuseStep 1478999 = 2218499) B2218499
theorem B25268597 : Blo 872567 25268597 := bstep (se 5 (by rfl) ⟨1184465, by rfl⟩ : syracuseStep 25268597 = 2368931) B2368931
theorem B1970585 : Blo 872567 1970585 := bstep (se 2 (by rfl) ⟨738969, by rfl⟩ : syracuseStep 1970585 = 1477939) B1477939
theorem B10621363 : Blo 872567 10621363 := bstep (se 1 (by rfl) ⟨7966022, by rfl⟩ : syracuseStep 10621363 = 15932045) B15932045
theorem B1479127 : Blo 872567 1479127 := bstep (se 1 (by rfl) ⟨1109345, by rfl⟩ : syracuseStep 1479127 = 2218691) B2218691
theorem B3314141 : Blo 872567 3314141 := bstep (se 3 (by rfl) ⟨621401, by rfl⟩ : syracuseStep 3314141 = 1242803) B1242803
theorem B1970675 : Blo 872567 1970675 := bstep (se 1 (by rfl) ⟨1478006, by rfl⟩ : syracuseStep 1970675 = 2956013) B2956013
theorem B1970711 : Blo 872567 1970711 := bstep (se 1 (by rfl) ⟨1478033, by rfl⟩ : syracuseStep 1970711 = 2956067) B2956067
theorem B3740249 : Blo 872567 3740249 := bstep (se 2 (by rfl) ⟨1402593, by rfl⟩ : syracuseStep 3740249 = 2805187) B2805187
theorem B4985495 : Blo 872567 4985495 := bstep (se 1 (by rfl) ⟨3739121, by rfl⟩ : syracuseStep 4985495 = 7478243) B7478243
theorem B2953907 : Blo 872567 2953907 := bstep (se 1 (by rfl) ⟨2215430, by rfl⟩ : syracuseStep 2953907 = 4430861) B4430861
theorem B1970891 : Blo 872567 1970891 := bstep (se 1 (by rfl) ⟨1478168, by rfl⟩ : syracuseStep 1970891 = 2956337) B2956337
theorem B1970945 : Blo 872567 1970945 := bstep (se 2 (by rfl) ⟨739104, by rfl⟩ : syracuseStep 1970945 = 1478209) B1478209
theorem B2954177 : Blo 872567 2954177 := bstep (se 2 (by rfl) ⟨1107816, by rfl⟩ : syracuseStep 2954177 = 2215633) B2215633
theorem B1971161 : Blo 872567 1971161 := bstep (se 2 (by rfl) ⟨739185, by rfl⟩ : syracuseStep 1971161 = 1478371) B1478371
theorem B2986973 : Blo 872567 2986973 := bstep (se 3 (by rfl) ⟨560057, by rfl⟩ : syracuseStep 2986973 = 1120115) B1120115
theorem B7476259 : Blo 872567 7476259 := bstep (se 1 (by rfl) ⟨5607194, by rfl⟩ : syracuseStep 7476259 = 11214389) B11214389
theorem B6394925 : Blo 872567 6394925 := bstep (se 3 (by rfl) ⟨1199048, by rfl⟩ : syracuseStep 6394925 = 2398097) B2398097
theorem B1971251 : Blo 872567 1971251 := bstep (se 1 (by rfl) ⟨1478438, by rfl⟩ : syracuseStep 1971251 = 2956877) B2956877
theorem B1971287 : Blo 872567 1971287 := bstep (se 1 (by rfl) ⟨1478465, by rfl⟩ : syracuseStep 1971287 = 2956931) B2956931
theorem B1971467 : Blo 872567 1971467 := bstep (se 1 (by rfl) ⟨1478600, by rfl⟩ : syracuseStep 1971467 = 2957201) B2957201
theorem B1971521 : Blo 872567 1971521 := bstep (se 2 (by rfl) ⟨739320, by rfl⟩ : syracuseStep 1971521 = 1478641) B1478641
theorem B5608835 : Blo 872567 5608835 := bstep (se 1 (by rfl) ⟨4206626, by rfl⟩ : syracuseStep 5608835 = 8413253) B8413253
theorem B2954717 : Blo 872567 2954717 := bstep (se 3 (by rfl) ⟨554009, by rfl⟩ : syracuseStep 2954717 = 1108019) B1108019
theorem B1971737 : Blo 872567 1971737 := bstep (se 2 (by rfl) ⟨739401, by rfl⟩ : syracuseStep 1971737 = 1478803) B1478803
theorem B10098269 : Blo 872567 10098269 := bstep (se 3 (by rfl) ⟨1893425, by rfl⟩ : syracuseStep 10098269 = 3786851) B3786851
theorem B1971827 : Blo 872567 1971827 := bstep (se 1 (by rfl) ⟨1478870, by rfl⟩ : syracuseStep 1971827 = 2957741) B2957741
theorem B3151511 : Blo 872567 3151511 := bstep (se 1 (by rfl) ⟨2363633, by rfl⟩ : syracuseStep 3151511 = 4727267) B4727267
theorem B1971863 : Blo 872567 1971863 := bstep (se 1 (by rfl) ⟨1478897, by rfl⟩ : syracuseStep 1971863 = 2957795) B2957795
theorem B4724497 : Blo 872567 4724497 := bstep (se 2 (by rfl) ⟨1771686, by rfl⟩ : syracuseStep 4724497 = 3543373) B3543373
theorem B1578827 : Blo 872567 1578827 := bstep (se 1 (by rfl) ⟨1184120, by rfl⟩ : syracuseStep 1578827 = 2368241) B2368241
theorem B1972043 : Blo 872567 1972043 := bstep (se 1 (by rfl) ⟨1479032, by rfl⟩ : syracuseStep 1972043 = 2958065) B2958065
theorem B1972097 : Blo 872567 1972097 := bstep (se 2 (by rfl) ⟨739536, by rfl⟩ : syracuseStep 1972097 = 1479073) B1479073
theorem B4429889 : Blo 872567 4429889 := bstep (se 2 (by rfl) ⟨1661208, by rfl⟩ : syracuseStep 4429889 = 3322417) B3322417
theorem B9443459 : Blo 872567 9443459 := bstep (se 1 (by rfl) ⟨7082594, by rfl⟩ : syracuseStep 9443459 = 14165189) B14165189
theorem B3741889 : Blo 872567 3741889 := bstep (se 2 (by rfl) ⟨1403208, by rfl⟩ : syracuseStep 3741889 = 2806417) B2806417
theorem B8395073 : Blo 872567 8395073 := bstep (se 2 (by rfl) ⟨3148152, by rfl⟩ : syracuseStep 8395073 = 6296305) B6296305
theorem B8395109 : Blo 872567 8395109 := bstep (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) B1574083
theorem B3316099 : Blo 872567 3316099 := bstep (se 1 (by rfl) ⟨2487074, by rfl⟩ : syracuseStep 3316099 = 4974149) B4974149
theorem B4200977 : Blo 872567 4200977 := bstep (se 2 (by rfl) ⟨1575366, by rfl⟩ : syracuseStep 4200977 = 3150733) B3150733
theorem B2955851 : Blo 872567 2955851 := bstep (se 1 (by rfl) ⟨2216888, by rfl⟩ : syracuseStep 2955851 = 4433777) B4433777
theorem B5053079 : Blo 872567 5053079 := bstep (se 1 (by rfl) ⟨3789809, by rfl⟩ : syracuseStep 5053079 = 7579619) B7579619
theorem B3316403 : Blo 872567 3316403 := bstep (se 1 (by rfl) ⟨2487302, by rfl⟩ : syracuseStep 3316403 = 4974605) B4974605
theorem B6626123 : Blo 872567 6626123 := bstep (se 1 (by rfl) ⟨4969592, by rfl⟩ : syracuseStep 6626123 = 9939185) B9939185
theorem B2956121 : Blo 872567 2956121 := bstep (se 2 (by rfl) ⟨1108545, by rfl⟩ : syracuseStep 2956121 = 2217091) B2217091
theorem B6298469 : Blo 872567 6298469 := bstep (se 4 (by rfl) ⟨590481, by rfl⟩ : syracuseStep 6298469 = 1180963) B1180963
theorem B1973143 : Blo 872567 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B2366401 : Blo 872567 2366401 := bstep (se 2 (by rfl) ⟨887400, by rfl⟩ : syracuseStep 2366401 = 1774801) B1774801
theorem B4987979 : Blo 872567 4987979 := bstep (se 1 (by rfl) ⟨3740984, by rfl⟩ : syracuseStep 4987979 = 7481969) B7481969
theorem B3317057 : Blo 872567 3317057 := bstep (se 2 (by rfl) ⟨1243896, by rfl⟩ : syracuseStep 3317057 = 2487793) B2487793
theorem B2956823 : Blo 872567 2956823 := bstep (se 1 (by rfl) ⟨2217617, by rfl⟩ : syracuseStep 2956823 = 4435235) B4435235
theorem B1416971 : Blo 872567 1416971 := bstep (se 1 (by rfl) ⟨1062728, by rfl⟩ : syracuseStep 1416971 = 2125457) B2125457
theorem B4431833 : Blo 872567 4431833 := bstep (se 2 (by rfl) ⟨1661937, by rfl⟩ : syracuseStep 4431833 = 3323875) B3323875
theorem B28712981 : Blo 872567 28712981 := bstep (se 6 (by rfl) ⟨672960, by rfl⟩ : syracuseStep 28712981 = 1345921) B1345921
theorem B2957363 : Blo 872567 2957363 := bstep (se 1 (by rfl) ⟨2218022, by rfl⟩ : syracuseStep 2957363 = 4436045) B4436045
theorem B4792621 : Blo 872567 4792621 := bstep (se 3 (by rfl) ⟨898616, by rfl⟩ : syracuseStep 4792621 = 1797233) B1797233
theorem B2957633 : Blo 872567 2957633 := bstep (se 2 (by rfl) ⟨1109112, by rfl⟩ : syracuseStep 2957633 = 2218225) B2218225
theorem B2105689 : Blo 872567 2105689 := bstep (se 2 (by rfl) ⟨789633, by rfl⟩ : syracuseStep 2105689 = 1579267) B1579267
theorem B3318317 : Blo 872567 3318317 := bstep (se 3 (by rfl) ⟨622184, by rfl⟩ : syracuseStep 3318317 = 1244369) B1244369
theorem B3318347 : Blo 872567 3318347 := bstep (se 1 (by rfl) ⟨2488760, by rfl⟩ : syracuseStep 3318347 = 4977521) B4977521
theorem B1123159 : Blo 872567 1123159 := bstep (se 1 (by rfl) ⟨842369, by rfl⟩ : syracuseStep 1123159 = 1684739) B1684739
theorem B2958173 : Blo 872567 2958173 := bstep (se 3 (by rfl) ⟨554657, by rfl⟩ : syracuseStep 2958173 = 1109315) B1109315
theorem B16819123 : Blo 872567 16819123 := bstep (se 1 (by rfl) ⟨12614342, by rfl⟩ : syracuseStep 16819123 = 25228685) B25228685
theorem B2368477 : Blo 872567 2368477 := bstep (se 3 (by rfl) ⟨444089, by rfl⟩ : syracuseStep 2368477 = 888179) B888179
theorem B3319001 : Blo 872567 3319001 := bstep (se 2 (by rfl) ⟨1244625, by rfl⟩ : syracuseStep 3319001 = 2489251) B2489251
theorem B3319319 : Blo 872567 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B4433453 : Blo 872567 4433453 := bstep (se 3 (by rfl) ⟨831272, by rfl⟩ : syracuseStep 4433453 = 1662545) B1662545
theorem B7480907 : Blo 872567 7480907 := bstep (se 1 (by rfl) ⟨5610680, by rfl⟩ : syracuseStep 7480907 = 11221361) B11221361
theorem B4990643 : Blo 872567 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B3319987 : Blo 872567 3319987 := bstep (se 1 (by rfl) ⟨2489990, by rfl⟩ : syracuseStep 3319987 = 4979981) B4979981
theorem B7088563 : Blo 872567 7088563 := bstep (se 1 (by rfl) ⟨5316422, by rfl⟩ : syracuseStep 7088563 = 10632845) B10632845
theorem B6302387 : Blo 872567 6302387 := bstep (se 1 (by rfl) ⟨4726790, by rfl⟩ : syracuseStep 6302387 = 9453581) B9453581
theorem B4992101 : Blo 872567 4992101 := bstep (se 4 (by rfl) ⟨468009, by rfl⟩ : syracuseStep 4992101 = 936019) B936019
theorem B3288385 : Blo 872567 3288385 := bstep (se 2 (by rfl) ⟨1233144, by rfl⟩ : syracuseStep 3288385 = 2466289) B2466289
theorem B3321233 : Blo 872567 3321233 := bstep (se 2 (by rfl) ⟨1245462, by rfl⟩ : syracuseStep 3321233 = 2490925) B2490925
theorem B3157393 : Blo 872567 3157393 := bstep (se 2 (by rfl) ⟨1184022, by rfl⟩ : syracuseStep 3157393 = 2368045) B2368045
theorem B2993611 : Blo 872567 2993611 := bstep (se 1 (by rfl) ⟨2245208, by rfl⟩ : syracuseStep 2993611 = 4490417) B4490417
theorem B3157451 : Blo 872567 3157451 := bstep (se 1 (by rfl) ⟨2368088, by rfl⟩ : syracuseStep 3157451 = 4736177) B4736177
theorem B6631469 : Blo 872567 6631469 := bstep (se 3 (by rfl) ⟨1243400, by rfl⟩ : syracuseStep 6631469 = 2486801) B2486801
theorem B3321931 : Blo 872567 3321931 := bstep (se 1 (by rfl) ⟨2491448, by rfl⟩ : syracuseStep 3321931 = 4982897) B4982897
theorem B2994265 : Blo 872567 2994265 := bstep (se 2 (by rfl) ⟨1122849, by rfl⟩ : syracuseStep 2994265 = 2245699) B2245699
theorem B3551321 : Blo 872567 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B995479 : Blo 872567 995479 := bstep (se 1 (by rfl) ⟨746609, by rfl⟩ : syracuseStep 995479 = 1493219) B1493219
theorem B3158189 : Blo 872567 3158189 := bstep (se 3 (by rfl) ⟨592160, by rfl⟩ : syracuseStep 3158189 = 1184321) B1184321
theorem B3322205 : Blo 872567 3322205 := bstep (se 3 (by rfl) ⟨622913, by rfl⟩ : syracuseStep 3322205 = 1245827) B1245827
theorem B3551809 : Blo 872567 3551809 := bstep (se 2 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 3551809 = 2663857) B2663857
theorem B4043353 : Blo 872567 4043353 := bstep (se 2 (by rfl) ⟨1516257, by rfl⟩ : syracuseStep 4043353 = 3032515) B3032515
theorem B28357361 : Blo 872567 28357361 := bstep (se 2 (by rfl) ⟨10634010, by rfl⟩ : syracuseStep 28357361 = 21268021) B21268021
theorem B3322903 : Blo 872567 3322903 := bstep (se 1 (by rfl) ⟨2492177, by rfl⟩ : syracuseStep 3322903 = 4984355) B4984355
theorem B2208971 : Blo 872567 2208971 := bstep (se 1 (by rfl) ⟨1656728, by rfl⟩ : syracuseStep 2208971 = 3313457) B3313457
theorem B6304985 : Blo 872567 6304985 := bstep (se 2 (by rfl) ⟨2364369, by rfl⟩ : syracuseStep 6304985 = 4728739) B4728739
theorem B4797713 : Blo 872567 4797713 := bstep (se 2 (by rfl) ⟨1799142, by rfl⟩ : syracuseStep 4797713 = 3598285) B3598285
theorem B4437341 : Blo 872567 4437341 := bstep (se 3 (by rfl) ⟨832001, by rfl⟩ : syracuseStep 4437341 = 1664003) B1664003
theorem B5977475 : Blo 872567 5977475 := bstep (se 1 (by rfl) ⟨4483106, by rfl⟩ : syracuseStep 5977475 = 8966213) B8966213
theorem B4208051 : Blo 872567 4208051 := bstep (se 1 (by rfl) ⟨3156038, by rfl⟩ : syracuseStep 4208051 = 6312077) B6312077
theorem B996971 : Blo 872567 996971 := bstep (se 1 (by rfl) ⟨747728, by rfl⟩ : syracuseStep 996971 = 1495457) B1495457
theorem B3323693 : Blo 872567 3323693 := bstep (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) B1246385
theorem B11188145 : Blo 872567 11188145 := bstep (se 2 (by rfl) ⟨4195554, by rfl⟩ : syracuseStep 11188145 = 8391109) B8391109
theorem B4208705 : Blo 872567 4208705 := bstep (se 2 (by rfl) ⟨1578264, by rfl⟩ : syracuseStep 4208705 = 3156529) B3156529
theorem B2209943 : Blo 872567 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B3553625 : Blo 872567 3553625 := bstep (se 2 (by rfl) ⟨1332609, by rfl⟩ : syracuseStep 3553625 = 2665219) B2665219
theorem B1686091 : Blo 872567 1686091 := bstep (se 1 (by rfl) ⟨1264568, by rfl⟩ : syracuseStep 1686091 = 2529137) B2529137
theorem B1915607 : Blo 872567 1915607 := bstep (se 1 (by rfl) ⟨1436705, by rfl⟩ : syracuseStep 1915607 = 2873411) B2873411
theorem B2210611 : Blo 872567 2210611 := bstep (se 1 (by rfl) ⟨1657958, by rfl⟩ : syracuseStep 2210611 = 3315917) B3315917
theorem B2210753 : Blo 872567 2210753 := bstep (se 2 (by rfl) ⟨829032, by rfl⟩ : syracuseStep 2210753 = 1658065) B1658065
theorem B3980461 : Blo 872567 3980461 := bstep (se 3 (by rfl) ⟨746336, by rfl⟩ : syracuseStep 3980461 = 1492673) B1492673
theorem B3325121 : Blo 872567 3325121 := bstep (se 2 (by rfl) ⟨1246920, by rfl⟩ : syracuseStep 3325121 = 2493841) B2493841
theorem B9977093 : Blo 872567 9977093 := bstep (se 4 (by rfl) ⟨935352, by rfl⟩ : syracuseStep 9977093 = 1870705) B1870705
theorem B4800179 : Blo 872567 4800179 := bstep (se 1 (by rfl) ⟨3600134, by rfl⟩ : syracuseStep 4800179 = 7200269) B7200269
theorem B1261337 : Blo 872567 1261337 := bstep (se 2 (by rfl) ⟨473001, by rfl⟩ : syracuseStep 1261337 = 946003) B946003
theorem B7094081 : Blo 872567 7094081 := bstep (se 2 (by rfl) ⟨2660280, by rfl⟩ : syracuseStep 7094081 = 5320561) B5320561
theorem B6635357 : Blo 872567 6635357 := bstep (se 3 (by rfl) ⟨1244129, by rfl⟩ : syracuseStep 6635357 = 2488259) B2488259
theorem B43106147 : Blo 872567 43106147 := bstep (se 1 (by rfl) ⟨32329610, by rfl⟩ : syracuseStep 43106147 = 64659221) B64659221
theorem B999307 : Blo 872567 999307 := bstep (se 1 (by rfl) ⟨749480, by rfl⟩ : syracuseStep 999307 = 1498961) B1498961
theorem B933815 : Blo 872567 933815 := bstep (se 1 (by rfl) ⟨700361, by rfl⟩ : syracuseStep 933815 = 1400723) B1400723
theorem B2801753 : Blo 872567 2801753 := bstep (se 2 (by rfl) ⟨1050657, by rfl⟩ : syracuseStep 2801753 = 2101315) B2101315
theorem B2212019 : Blo 872567 2212019 := bstep (se 1 (by rfl) ⟨1659014, by rfl⟩ : syracuseStep 2212019 = 3318029) B3318029
theorem B2801881 : Blo 872567 2801881 := bstep (se 2 (by rfl) ⟨1050705, by rfl⟩ : syracuseStep 2801881 = 2101411) B2101411
theorem B2245043 : Blo 872567 2245043 := bstep (se 1 (by rfl) ⟨1683782, by rfl⟩ : syracuseStep 2245043 = 3367565) B3367565
theorem B6308387 : Blo 872567 6308387 := bstep (se 1 (by rfl) ⟨4731290, by rfl⟩ : syracuseStep 6308387 = 9462581) B9462581
theorem B934507 : Blo 872567 934507 := bstep (se 1 (by rfl) ⟨700880, by rfl⟩ : syracuseStep 934507 = 1401761) B1401761
theorem B3326609 : Blo 872567 3326609 := bstep (se 2 (by rfl) ⟨1247478, by rfl⟩ : syracuseStep 3326609 = 2494957) B2494957
theorem B2212555 : Blo 872567 2212555 := bstep (se 1 (by rfl) ⟨1659416, by rfl⟩ : syracuseStep 2212555 = 3318833) B3318833
theorem B2212697 : Blo 872567 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B3327065 : Blo 872567 3327065 := bstep (se 2 (by rfl) ⟨1247649, by rfl⟩ : syracuseStep 3327065 = 2495299) B2495299
theorem B3327277 : Blo 872567 3327277 := bstep (se 3 (by rfl) ⟨623864, by rfl⟩ : syracuseStep 3327277 = 1247729) B1247729
theorem B6309251 : Blo 872567 6309251 := bstep (se 1 (by rfl) ⟨4731938, by rfl⟩ : syracuseStep 6309251 = 9463877) B9463877
theorem B935383 : Blo 872567 935383 := bstep (se 1 (by rfl) ⟨701537, by rfl⟩ : syracuseStep 935383 = 1403075) B1403075
theorem B3327581 : Blo 872567 3327581 := bstep (se 3 (by rfl) ⟨623921, by rfl⟩ : syracuseStep 3327581 = 1247843) B1247843
theorem B1328791 : Blo 872567 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B2213527 : Blo 872567 2213527 := bstep (se 1 (by rfl) ⟨1660145, by rfl⟩ : syracuseStep 2213527 = 3320291) B3320291
theorem B935831 : Blo 872567 935831 := bstep (se 1 (by rfl) ⟨701873, by rfl⟩ : syracuseStep 935831 = 1403747) B1403747
theorem B6932441 : Blo 872567 6932441 := bstep (se 2 (by rfl) ⟨2599665, by rfl⟩ : syracuseStep 6932441 = 5199331) B5199331
theorem B2213963 : Blo 872567 2213963 := bstep (se 1 (by rfl) ⟨1660472, by rfl⟩ : syracuseStep 2213963 = 3320945) B3320945
theorem B15976709 : Blo 872567 15976709 := bstep (se 4 (by rfl) ⟨1497816, by rfl⟩ : syracuseStep 15976709 = 2995633) B2995633
theorem B2214337 : Blo 872567 2214337 := bstep (se 2 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 2214337 = 1660753) B1660753
theorem B1493657 : Blo 872567 1493657 := bstep (se 2 (by rfl) ⟨560121, by rfl⟩ : syracuseStep 1493657 = 1120243) B1120243
theorem B1657739 : Blo 872567 1657739 := bstep (se 1 (by rfl) ⟨1243304, by rfl⟩ : syracuseStep 1657739 = 2486609) B2486609
theorem B2214935 : Blo 872567 2214935 := bstep (se 1 (by rfl) ⟨1661201, by rfl⟩ : syracuseStep 2214935 = 3322403) B3322403
theorem B1657921 : Blo 872567 1657921 := bstep (se 2 (by rfl) ⟨621720, by rfl⟩ : syracuseStep 1657921 = 1243441) B1243441
theorem B7097645 : Blo 872567 7097645 := bstep (se 3 (by rfl) ⟨1330808, by rfl⟩ : syracuseStep 7097645 = 2661617) B2661617
theorem B1658369 : Blo 872567 1658369 := bstep (se 2 (by rfl) ⟨621888, by rfl⟩ : syracuseStep 1658369 = 1243777) B1243777
theorem B2215745 : Blo 872567 2215745 := bstep (se 2 (by rfl) ⟨830904, by rfl⟩ : syracuseStep 2215745 = 1661809) B1661809
theorem B1658711 : Blo 872567 1658711 := bstep (se 1 (by rfl) ⟨1244033, by rfl⟩ : syracuseStep 1658711 = 2488067) B2488067
theorem B2805853 : Blo 872567 2805853 := bstep (se 3 (by rfl) ⟨526097, by rfl⟩ : syracuseStep 2805853 = 1052195) B1052195
theorem B872567 : Blo 872567 872567 := bstep (se 1 (by rfl) ⟨654425, by rfl⟩ : syracuseStep 872567 = 1308851) B1308851
theorem B872587 : Blo 872567 872587 := bstep (se 1 (by rfl) ⟨654440, by rfl⟩ : syracuseStep 872587 = 1308881) B1308881
theorem B872599 : Blo 872567 872599 := bstep (se 1 (by rfl) ⟨654449, by rfl⟩ : syracuseStep 872599 = 1308899) B1308899
theorem B872619 : Blo 872567 872619 := bstep (se 1 (by rfl) ⟨654464, by rfl⟩ : syracuseStep 872619 = 1308929) B1308929
theorem B872631 : Blo 872567 872631 := bstep (se 1 (by rfl) ⟨654473, by rfl⟩ : syracuseStep 872631 = 1308947) B1308947
theorem B872651 : Blo 872567 872651 := bstep (se 1 (by rfl) ⟨654488, by rfl⟩ : syracuseStep 872651 = 1308977) B1308977
theorem B872663 : Blo 872567 872663 := bstep (se 1 (by rfl) ⟨654497, by rfl⟩ : syracuseStep 872663 = 1308995) B1308995
theorem B872683 : Blo 872567 872683 := bstep (se 1 (by rfl) ⟨654512, by rfl⟩ : syracuseStep 872683 = 1309025) B1309025
theorem B872695 : Blo 872567 872695 := bstep (se 1 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 872695 = 1309043) B1309043
theorem B872715 : Blo 872567 872715 := bstep (se 1 (by rfl) ⟨654536, by rfl⟩ : syracuseStep 872715 = 1309073) B1309073
theorem B872727 : Blo 872567 872727 := bstep (se 1 (by rfl) ⟨654545, by rfl⟩ : syracuseStep 872727 = 1309091) B1309091
theorem B872747 : Blo 872567 872747 := bstep (se 1 (by rfl) ⟨654560, by rfl⟩ : syracuseStep 872747 = 1309121) B1309121
theorem B872759 : Blo 872567 872759 := bstep (se 1 (by rfl) ⟨654569, by rfl⟩ : syracuseStep 872759 = 1309139) B1309139
theorem B872779 : Blo 872567 872779 := bstep (se 1 (by rfl) ⟨654584, by rfl⟩ : syracuseStep 872779 = 1309169) B1309169
theorem B872791 : Blo 872567 872791 := bstep (se 1 (by rfl) ⟨654593, by rfl⟩ : syracuseStep 872791 = 1309187) B1309187
theorem B2216281 : Blo 872567 2216281 := bstep (se 2 (by rfl) ⟨831105, by rfl⟩ : syracuseStep 2216281 = 1662211) B1662211
theorem B872811 : Blo 872567 872811 := bstep (se 1 (by rfl) ⟨654608, by rfl⟩ : syracuseStep 872811 = 1309217) B1309217
theorem B872823 : Blo 872567 872823 := bstep (se 1 (by rfl) ⟨654617, by rfl⟩ : syracuseStep 872823 = 1309235) B1309235
theorem B872843 : Blo 872567 872843 := bstep (se 1 (by rfl) ⟨654632, by rfl⟩ : syracuseStep 872843 = 1309265) B1309265
theorem B872855 : Blo 872567 872855 := bstep (se 1 (by rfl) ⟨654641, by rfl⟩ : syracuseStep 872855 = 1309283) B1309283
theorem B872875 : Blo 872567 872875 := bstep (se 1 (by rfl) ⟨654656, by rfl⟩ : syracuseStep 872875 = 1309313) B1309313
theorem B872887 : Blo 872567 872887 := bstep (se 1 (by rfl) ⟨654665, by rfl⟩ : syracuseStep 872887 = 1309331) B1309331
theorem B872907 : Blo 872567 872907 := bstep (se 1 (by rfl) ⟨654680, by rfl⟩ : syracuseStep 872907 = 1309361) B1309361
theorem B872919 : Blo 872567 872919 := bstep (se 1 (by rfl) ⟨654689, by rfl⟩ : syracuseStep 872919 = 1309379) B1309379
theorem B872939 : Blo 872567 872939 := bstep (se 1 (by rfl) ⟨654704, by rfl⟩ : syracuseStep 872939 = 1309409) B1309409
theorem B1659379 : Blo 872567 1659379 := bstep (se 1 (by rfl) ⟨1244534, by rfl⟩ : syracuseStep 1659379 = 2489069) B2489069
theorem B872951 : Blo 872567 872951 := bstep (se 1 (by rfl) ⟨654713, by rfl⟩ : syracuseStep 872951 = 1309427) B1309427
theorem B872971 : Blo 872567 872971 := bstep (se 1 (by rfl) ⟨654728, by rfl⟩ : syracuseStep 872971 = 1309457) B1309457
theorem B872983 : Blo 872567 872983 := bstep (se 1 (by rfl) ⟨654737, by rfl⟩ : syracuseStep 872983 = 1309475) B1309475
theorem B873003 : Blo 872567 873003 := bstep (se 1 (by rfl) ⟨654752, by rfl⟩ : syracuseStep 873003 = 1309505) B1309505
theorem B873015 : Blo 872567 873015 := bstep (se 1 (by rfl) ⟨654761, by rfl⟩ : syracuseStep 873015 = 1309523) B1309523
theorem B873035 : Blo 872567 873035 := bstep (se 1 (by rfl) ⟨654776, by rfl⟩ : syracuseStep 873035 = 1309553) B1309553
theorem B873047 : Blo 872567 873047 := bstep (se 1 (by rfl) ⟨654785, by rfl⟩ : syracuseStep 873047 = 1309571) B1309571
theorem B873067 : Blo 872567 873067 := bstep (se 1 (by rfl) ⟨654800, by rfl⟩ : syracuseStep 873067 = 1309601) B1309601
theorem B873079 : Blo 872567 873079 := bstep (se 1 (by rfl) ⟨654809, by rfl⟩ : syracuseStep 873079 = 1309619) B1309619
theorem B873099 : Blo 872567 873099 := bstep (se 1 (by rfl) ⟨654824, by rfl⟩ : syracuseStep 873099 = 1309649) B1309649
theorem B873111 : Blo 872567 873111 := bstep (se 1 (by rfl) ⟨654833, by rfl⟩ : syracuseStep 873111 = 1309667) B1309667
theorem B873131 : Blo 872567 873131 := bstep (se 1 (by rfl) ⟨654848, by rfl⟩ : syracuseStep 873131 = 1309697) B1309697
theorem B873143 : Blo 872567 873143 := bstep (se 1 (by rfl) ⟨654857, by rfl⟩ : syracuseStep 873143 = 1309715) B1309715
theorem B873163 : Blo 872567 873163 := bstep (se 1 (by rfl) ⟨654872, by rfl⟩ : syracuseStep 873163 = 1309745) B1309745
theorem B873175 : Blo 872567 873175 := bstep (se 1 (by rfl) ⟨654881, by rfl⟩ : syracuseStep 873175 = 1309763) B1309763
theorem B873195 : Blo 872567 873195 := bstep (se 1 (by rfl) ⟨654896, by rfl⟩ : syracuseStep 873195 = 1309793) B1309793
theorem B873207 : Blo 872567 873207 := bstep (se 1 (by rfl) ⟨654905, by rfl⟩ : syracuseStep 873207 = 1309811) B1309811
theorem B873227 : Blo 872567 873227 := bstep (se 1 (by rfl) ⟨654920, by rfl⟩ : syracuseStep 873227 = 1309841) B1309841
theorem B873239 : Blo 872567 873239 := bstep (se 1 (by rfl) ⟨654929, by rfl⟩ : syracuseStep 873239 = 1309859) B1309859
theorem B873259 : Blo 872567 873259 := bstep (se 1 (by rfl) ⟨654944, by rfl⟩ : syracuseStep 873259 = 1309889) B1309889
theorem B12112685 : Blo 872567 12112685 := bstep (se 3 (by rfl) ⟨2271128, by rfl⟩ : syracuseStep 12112685 = 4542257) B4542257
theorem B873271 : Blo 872567 873271 := bstep (se 1 (by rfl) ⟨654953, by rfl⟩ : syracuseStep 873271 = 1309907) B1309907
theorem B873291 : Blo 872567 873291 := bstep (se 1 (by rfl) ⟨654968, by rfl⟩ : syracuseStep 873291 = 1309937) B1309937
theorem B873303 : Blo 872567 873303 := bstep (se 1 (by rfl) ⟨654977, by rfl⟩ : syracuseStep 873303 = 1309955) B1309955
theorem B873323 : Blo 872567 873323 := bstep (se 1 (by rfl) ⟨654992, by rfl⟩ : syracuseStep 873323 = 1309985) B1309985
theorem B873335 : Blo 872567 873335 := bstep (se 1 (by rfl) ⟨655001, by rfl⟩ : syracuseStep 873335 = 1310003) B1310003
theorem B873355 : Blo 872567 873355 := bstep (se 1 (by rfl) ⟨655016, by rfl⟩ : syracuseStep 873355 = 1310033) B1310033
theorem B873367 : Blo 872567 873367 := bstep (se 1 (by rfl) ⟨655025, by rfl⟩ : syracuseStep 873367 = 1310051) B1310051
theorem B873387 : Blo 872567 873387 := bstep (se 1 (by rfl) ⟨655040, by rfl⟩ : syracuseStep 873387 = 1310081) B1310081
theorem B1659827 : Blo 872567 1659827 := bstep (se 1 (by rfl) ⟨1244870, by rfl⟩ : syracuseStep 1659827 = 2489741) B2489741
theorem B873399 : Blo 872567 873399 := bstep (se 1 (by rfl) ⟨655049, by rfl⟩ : syracuseStep 873399 = 1310099) B1310099
theorem B873419 : Blo 872567 873419 := bstep (se 1 (by rfl) ⟨655064, by rfl⟩ : syracuseStep 873419 = 1310129) B1310129
theorem B873431 : Blo 872567 873431 := bstep (se 1 (by rfl) ⟨655073, by rfl⟩ : syracuseStep 873431 = 1310147) B1310147
theorem B1659865 : Blo 872567 1659865 := bstep (se 2 (by rfl) ⟨622449, by rfl⟩ : syracuseStep 1659865 = 1244899) B1244899
theorem B873451 : Blo 872567 873451 := bstep (se 1 (by rfl) ⟨655088, by rfl⟩ : syracuseStep 873451 = 1310177) B1310177
theorem B873463 : Blo 872567 873463 := bstep (se 1 (by rfl) ⟨655097, by rfl⟩ : syracuseStep 873463 = 1310195) B1310195
theorem B873483 : Blo 872567 873483 := bstep (se 1 (by rfl) ⟨655112, by rfl⟩ : syracuseStep 873483 = 1310225) B1310225
theorem B873495 : Blo 872567 873495 := bstep (se 1 (by rfl) ⟨655121, by rfl⟩ : syracuseStep 873495 = 1310243) B1310243
theorem B1365017 : Blo 872567 1365017 := bstep (se 2 (by rfl) ⟨511881, by rfl⟩ : syracuseStep 1365017 = 1023763) B1023763
theorem B873515 : Blo 872567 873515 := bstep (se 1 (by rfl) ⟨655136, by rfl⟩ : syracuseStep 873515 = 1310273) B1310273
theorem B873527 : Blo 872567 873527 := bstep (se 1 (by rfl) ⟨655145, by rfl⟩ : syracuseStep 873527 = 1310291) B1310291
theorem B873547 : Blo 872567 873547 := bstep (se 1 (by rfl) ⟨655160, by rfl⟩ : syracuseStep 873547 = 1310321) B1310321
theorem B873559 : Blo 872567 873559 := bstep (se 1 (by rfl) ⟨655169, by rfl⟩ : syracuseStep 873559 = 1310339) B1310339
theorem B873579 : Blo 872567 873579 := bstep (se 1 (by rfl) ⟨655184, by rfl⟩ : syracuseStep 873579 = 1310369) B1310369
theorem B873591 : Blo 872567 873591 := bstep (se 1 (by rfl) ⟨655193, by rfl⟩ : syracuseStep 873591 = 1310387) B1310387
theorem B873611 : Blo 872567 873611 := bstep (se 1 (by rfl) ⟨655208, by rfl⟩ : syracuseStep 873611 = 1310417) B1310417
theorem B873623 : Blo 872567 873623 := bstep (se 1 (by rfl) ⟨655217, by rfl⟩ : syracuseStep 873623 = 1310435) B1310435
theorem B873643 : Blo 872567 873643 := bstep (se 1 (by rfl) ⟨655232, by rfl⟩ : syracuseStep 873643 = 1310465) B1310465
theorem B873655 : Blo 872567 873655 := bstep (se 1 (by rfl) ⟨655241, by rfl⟩ : syracuseStep 873655 = 1310483) B1310483
theorem B873675 : Blo 872567 873675 := bstep (se 1 (by rfl) ⟨655256, by rfl⟩ : syracuseStep 873675 = 1310513) B1310513
theorem B873687 : Blo 872567 873687 := bstep (se 1 (by rfl) ⟨655265, by rfl⟩ : syracuseStep 873687 = 1310531) B1310531
theorem B1496279 : Blo 872567 1496279 := bstep (se 1 (by rfl) ⟨1122209, by rfl⟩ : syracuseStep 1496279 = 2244419) B2244419
theorem B873707 : Blo 872567 873707 := bstep (se 1 (by rfl) ⟨655280, by rfl⟩ : syracuseStep 873707 = 1310561) B1310561
theorem B873719 : Blo 872567 873719 := bstep (se 1 (by rfl) ⟨655289, by rfl⟩ : syracuseStep 873719 = 1310579) B1310579
theorem B873739 : Blo 872567 873739 := bstep (se 1 (by rfl) ⟨655304, by rfl⟩ : syracuseStep 873739 = 1310609) B1310609
theorem B873751 : Blo 872567 873751 := bstep (se 1 (by rfl) ⟨655313, by rfl⟩ : syracuseStep 873751 = 1310627) B1310627
theorem B3593495 : Blo 872567 3593495 := bstep (se 1 (by rfl) ⟨2695121, by rfl⟩ : syracuseStep 3593495 = 5390243) B5390243
theorem B873771 : Blo 872567 873771 := bstep (se 1 (by rfl) ⟨655328, by rfl⟩ : syracuseStep 873771 = 1310657) B1310657
theorem B873783 : Blo 872567 873783 := bstep (se 1 (by rfl) ⟨655337, by rfl⟩ : syracuseStep 873783 = 1310675) B1310675
theorem B873803 : Blo 872567 873803 := bstep (se 1 (by rfl) ⟨655352, by rfl⟩ : syracuseStep 873803 = 1310705) B1310705
theorem B873815 : Blo 872567 873815 := bstep (se 1 (by rfl) ⟨655361, by rfl⟩ : syracuseStep 873815 = 1310723) B1310723
theorem B873835 : Blo 872567 873835 := bstep (se 1 (by rfl) ⟨655376, by rfl⟩ : syracuseStep 873835 = 1310753) B1310753
theorem B873847 : Blo 872567 873847 := bstep (se 1 (by rfl) ⟨655385, by rfl⟩ : syracuseStep 873847 = 1310771) B1310771
theorem B873867 : Blo 872567 873867 := bstep (se 1 (by rfl) ⟨655400, by rfl⟩ : syracuseStep 873867 = 1310801) B1310801
theorem B873879 : Blo 872567 873879 := bstep (se 1 (by rfl) ⟨655409, by rfl⟩ : syracuseStep 873879 = 1310819) B1310819
theorem B1660313 : Blo 872567 1660313 := bstep (se 2 (by rfl) ⟨622617, by rfl⟩ : syracuseStep 1660313 = 1245235) B1245235
theorem B873899 : Blo 872567 873899 := bstep (se 1 (by rfl) ⟨655424, by rfl⟩ : syracuseStep 873899 = 1310849) B1310849
theorem B2217395 : Blo 872567 2217395 := bstep (se 1 (by rfl) ⟨1663046, by rfl⟩ : syracuseStep 2217395 = 3326093) B3326093
theorem B873911 : Blo 872567 873911 := bstep (se 1 (by rfl) ⟨655433, by rfl⟩ : syracuseStep 873911 = 1310867) B1310867
theorem B873931 : Blo 872567 873931 := bstep (se 1 (by rfl) ⟨655448, by rfl⟩ : syracuseStep 873931 = 1310897) B1310897
theorem B873943 : Blo 872567 873943 := bstep (se 1 (by rfl) ⟨655457, by rfl⟩ : syracuseStep 873943 = 1310915) B1310915
theorem B873963 : Blo 872567 873963 := bstep (se 1 (by rfl) ⟨655472, by rfl⟩ : syracuseStep 873963 = 1310945) B1310945
theorem B873975 : Blo 872567 873975 := bstep (se 1 (by rfl) ⟨655481, by rfl⟩ : syracuseStep 873975 = 1310963) B1310963
theorem B873995 : Blo 872567 873995 := bstep (se 1 (by rfl) ⟨655496, by rfl⟩ : syracuseStep 873995 = 1310993) B1310993
theorem B874007 : Blo 872567 874007 := bstep (se 1 (by rfl) ⟨655505, by rfl⟩ : syracuseStep 874007 = 1311011) B1311011
theorem B874027 : Blo 872567 874027 := bstep (se 1 (by rfl) ⟨655520, by rfl⟩ : syracuseStep 874027 = 1311041) B1311041
theorem B874039 : Blo 872567 874039 := bstep (se 1 (by rfl) ⟨655529, by rfl⟩ : syracuseStep 874039 = 1311059) B1311059
theorem B874059 : Blo 872567 874059 := bstep (se 1 (by rfl) ⟨655544, by rfl⟩ : syracuseStep 874059 = 1311089) B1311089
theorem B1398359 : Blo 872567 1398359 := bstep (se 1 (by rfl) ⟨1048769, by rfl⟩ : syracuseStep 1398359 = 2097539) B2097539
theorem B874071 : Blo 872567 874071 := bstep (se 1 (by rfl) ⟨655553, by rfl⟩ : syracuseStep 874071 = 1311107) B1311107
theorem B874091 : Blo 872567 874091 := bstep (se 1 (by rfl) ⟨655568, by rfl⟩ : syracuseStep 874091 = 1311137) B1311137
theorem B874103 : Blo 872567 874103 := bstep (se 1 (by rfl) ⟨655577, by rfl⟩ : syracuseStep 874103 = 1311155) B1311155
theorem B874123 : Blo 872567 874123 := bstep (se 1 (by rfl) ⟨655592, by rfl⟩ : syracuseStep 874123 = 1311185) B1311185
theorem B874135 : Blo 872567 874135 := bstep (se 1 (by rfl) ⟨655601, by rfl⟩ : syracuseStep 874135 = 1311203) B1311203
theorem B874155 : Blo 872567 874155 := bstep (se 1 (by rfl) ⟨655616, by rfl⟩ : syracuseStep 874155 = 1311233) B1311233
theorem B874167 : Blo 872567 874167 := bstep (se 1 (by rfl) ⟨655625, by rfl⟩ : syracuseStep 874167 = 1311251) B1311251
theorem B874187 : Blo 872567 874187 := bstep (se 1 (by rfl) ⟨655640, by rfl⟩ : syracuseStep 874187 = 1311281) B1311281
theorem B874199 : Blo 872567 874199 := bstep (se 1 (by rfl) ⟨655649, by rfl⟩ : syracuseStep 874199 = 1311299) B1311299
theorem B2217689 : Blo 872567 2217689 := bstep (se 2 (by rfl) ⟨831633, by rfl⟩ : syracuseStep 2217689 = 1663267) B1663267
theorem B874219 : Blo 872567 874219 := bstep (se 1 (by rfl) ⟨655664, by rfl⟩ : syracuseStep 874219 = 1311329) B1311329
theorem B874231 : Blo 872567 874231 := bstep (se 1 (by rfl) ⟨655673, by rfl⟩ : syracuseStep 874231 = 1311347) B1311347
theorem B874251 : Blo 872567 874251 := bstep (se 1 (by rfl) ⟨655688, by rfl⟩ : syracuseStep 874251 = 1311377) B1311377
theorem B874263 : Blo 872567 874263 := bstep (se 1 (by rfl) ⟨655697, by rfl⟩ : syracuseStep 874263 = 1311395) B1311395
theorem B874283 : Blo 872567 874283 := bstep (se 1 (by rfl) ⟨655712, by rfl⟩ : syracuseStep 874283 = 1311425) B1311425
theorem B874295 : Blo 872567 874295 := bstep (se 1 (by rfl) ⟨655721, by rfl⟩ : syracuseStep 874295 = 1311443) B1311443
theorem B874315 : Blo 872567 874315 := bstep (se 1 (by rfl) ⟨655736, by rfl⟩ : syracuseStep 874315 = 1311473) B1311473
theorem B874327 : Blo 872567 874327 := bstep (se 1 (by rfl) ⟨655745, by rfl⟩ : syracuseStep 874327 = 1311491) B1311491
theorem B874347 : Blo 872567 874347 := bstep (se 1 (by rfl) ⟨655760, by rfl⟩ : syracuseStep 874347 = 1311521) B1311521
theorem B874359 : Blo 872567 874359 := bstep (se 1 (by rfl) ⟨655769, by rfl⟩ : syracuseStep 874359 = 1311539) B1311539
theorem B874379 : Blo 872567 874379 := bstep (se 1 (by rfl) ⟨655784, by rfl⟩ : syracuseStep 874379 = 1311569) B1311569
theorem B874391 : Blo 872567 874391 := bstep (se 1 (by rfl) ⟨655793, by rfl⟩ : syracuseStep 874391 = 1311587) B1311587
theorem B874411 : Blo 872567 874411 := bstep (se 1 (by rfl) ⟨655808, by rfl⟩ : syracuseStep 874411 = 1311617) B1311617
theorem B874423 : Blo 872567 874423 := bstep (se 1 (by rfl) ⟨655817, by rfl⟩ : syracuseStep 874423 = 1311635) B1311635
theorem B874443 : Blo 872567 874443 := bstep (se 1 (by rfl) ⟨655832, by rfl⟩ : syracuseStep 874443 = 1311665) B1311665
theorem B874455 : Blo 872567 874455 := bstep (se 1 (by rfl) ⟨655841, by rfl⟩ : syracuseStep 874455 = 1311683) B1311683
theorem B5593049 : Blo 872567 5593049 := bstep (se 2 (by rfl) ⟨2097393, by rfl⟩ : syracuseStep 5593049 = 4194787) B4194787
theorem B874475 : Blo 872567 874475 := bstep (se 1 (by rfl) ⟨655856, by rfl⟩ : syracuseStep 874475 = 1311713) B1311713
theorem B874487 : Blo 872567 874487 := bstep (se 1 (by rfl) ⟨655865, by rfl⟩ : syracuseStep 874487 = 1311731) B1311731
theorem B874507 : Blo 872567 874507 := bstep (se 1 (by rfl) ⟨655880, by rfl⟩ : syracuseStep 874507 = 1311761) B1311761
theorem B874519 : Blo 872567 874519 := bstep (se 1 (by rfl) ⟨655889, by rfl⟩ : syracuseStep 874519 = 1311779) B1311779
theorem B874539 : Blo 872567 874539 := bstep (se 1 (by rfl) ⟨655904, by rfl⟩ : syracuseStep 874539 = 1311809) B1311809
theorem B874551 : Blo 872567 874551 := bstep (se 1 (by rfl) ⟨655913, by rfl⟩ : syracuseStep 874551 = 1311827) B1311827
theorem B874571 : Blo 872567 874571 := bstep (se 1 (by rfl) ⟨655928, by rfl⟩ : syracuseStep 874571 = 1311857) B1311857
theorem B874583 : Blo 872567 874583 := bstep (se 1 (by rfl) ⟨655937, by rfl⟩ : syracuseStep 874583 = 1311875) B1311875
theorem B874603 : Blo 872567 874603 := bstep (se 1 (by rfl) ⟨655952, by rfl⟩ : syracuseStep 874603 = 1311905) B1311905
theorem B874615 : Blo 872567 874615 := bstep (se 1 (by rfl) ⟨655961, by rfl⟩ : syracuseStep 874615 = 1311923) B1311923
theorem B1661057 : Blo 872567 1661057 := bstep (se 2 (by rfl) ⟨622896, by rfl⟩ : syracuseStep 1661057 = 1245793) B1245793
theorem B874635 : Blo 872567 874635 := bstep (se 1 (by rfl) ⟨655976, by rfl⟩ : syracuseStep 874635 = 1311953) B1311953
theorem B874647 : Blo 872567 874647 := bstep (se 1 (by rfl) ⟨655985, by rfl⟩ : syracuseStep 874647 = 1311971) B1311971
theorem B7100567 : Blo 872567 7100567 := bstep (se 1 (by rfl) ⟨5325425, by rfl⟩ : syracuseStep 7100567 = 10650851) B10650851
theorem B874667 : Blo 872567 874667 := bstep (se 1 (by rfl) ⟨656000, by rfl⟩ : syracuseStep 874667 = 1312001) B1312001
theorem B874679 : Blo 872567 874679 := bstep (se 1 (by rfl) ⟨656009, by rfl⟩ : syracuseStep 874679 = 1312019) B1312019
theorem B874699 : Blo 872567 874699 := bstep (se 1 (by rfl) ⟨656024, by rfl⟩ : syracuseStep 874699 = 1312049) B1312049
theorem B874711 : Blo 872567 874711 := bstep (se 1 (by rfl) ⟨656033, by rfl⟩ : syracuseStep 874711 = 1312067) B1312067
theorem B874731 : Blo 872567 874731 := bstep (se 1 (by rfl) ⟨656048, by rfl⟩ : syracuseStep 874731 = 1312097) B1312097
theorem B874743 : Blo 872567 874743 := bstep (se 1 (by rfl) ⟨656057, by rfl⟩ : syracuseStep 874743 = 1312115) B1312115
theorem B874763 : Blo 872567 874763 := bstep (se 1 (by rfl) ⟨656072, by rfl⟩ : syracuseStep 874763 = 1312145) B1312145
theorem B874775 : Blo 872567 874775 := bstep (se 1 (by rfl) ⟨656081, by rfl⟩ : syracuseStep 874775 = 1312163) B1312163
theorem B874795 : Blo 872567 874795 := bstep (se 1 (by rfl) ⟨656096, by rfl⟩ : syracuseStep 874795 = 1312193) B1312193
theorem B874807 : Blo 872567 874807 := bstep (se 1 (by rfl) ⟨656105, by rfl⟩ : syracuseStep 874807 = 1312211) B1312211
theorem B1890635 : Blo 872567 1890635 := bstep (se 1 (by rfl) ⟨1417976, by rfl⟩ : syracuseStep 1890635 = 2835953) B2835953
theorem B874827 : Blo 872567 874827 := bstep (se 1 (by rfl) ⟨656120, by rfl⟩ : syracuseStep 874827 = 1312241) B1312241
theorem B874839 : Blo 872567 874839 := bstep (se 1 (by rfl) ⟨656129, by rfl⟩ : syracuseStep 874839 = 1312259) B1312259
theorem B874859 : Blo 872567 874859 := bstep (se 1 (by rfl) ⟨656144, by rfl⟩ : syracuseStep 874859 = 1312289) B1312289
theorem B874871 : Blo 872567 874871 := bstep (se 1 (by rfl) ⟨656153, by rfl⟩ : syracuseStep 874871 = 1312307) B1312307
theorem B874891 : Blo 872567 874891 := bstep (se 1 (by rfl) ⟨656168, by rfl⟩ : syracuseStep 874891 = 1312337) B1312337
theorem B1661323 : Blo 872567 1661323 := bstep (se 1 (by rfl) ⟨1245992, by rfl⟩ : syracuseStep 1661323 = 2491985) B2491985
theorem B874903 : Blo 872567 874903 := bstep (se 1 (by rfl) ⟨656177, by rfl⟩ : syracuseStep 874903 = 1312355) B1312355
theorem B874923 : Blo 872567 874923 := bstep (se 1 (by rfl) ⟨656192, by rfl⟩ : syracuseStep 874923 = 1312385) B1312385
theorem B874935 : Blo 872567 874935 := bstep (se 1 (by rfl) ⟨656201, by rfl⟩ : syracuseStep 874935 = 1312403) B1312403
theorem B874955 : Blo 872567 874955 := bstep (se 1 (by rfl) ⟨656216, by rfl⟩ : syracuseStep 874955 = 1312433) B1312433
theorem B874967 : Blo 872567 874967 := bstep (se 1 (by rfl) ⟨656225, by rfl⟩ : syracuseStep 874967 = 1312451) B1312451
theorem B874987 : Blo 872567 874987 := bstep (se 1 (by rfl) ⟨656240, by rfl⟩ : syracuseStep 874987 = 1312481) B1312481
theorem B874999 : Blo 872567 874999 := bstep (se 1 (by rfl) ⟨656249, by rfl⟩ : syracuseStep 874999 = 1312499) B1312499
theorem B875019 : Blo 872567 875019 := bstep (se 1 (by rfl) ⟨656264, by rfl⟩ : syracuseStep 875019 = 1312529) B1312529
theorem B875031 : Blo 872567 875031 := bstep (se 1 (by rfl) ⟨656273, by rfl⟩ : syracuseStep 875031 = 1312547) B1312547
theorem B875051 : Blo 872567 875051 := bstep (se 1 (by rfl) ⟨656288, by rfl⟩ : syracuseStep 875051 = 1312577) B1312577
theorem B875063 : Blo 872567 875063 := bstep (se 1 (by rfl) ⟨656297, by rfl⟩ : syracuseStep 875063 = 1312595) B1312595
theorem B875083 : Blo 872567 875083 := bstep (se 1 (by rfl) ⟨656312, by rfl⟩ : syracuseStep 875083 = 1312625) B1312625
theorem B875095 : Blo 872567 875095 := bstep (se 1 (by rfl) ⟨656321, by rfl⟩ : syracuseStep 875095 = 1312643) B1312643
theorem B875115 : Blo 872567 875115 := bstep (se 1 (by rfl) ⟨656336, by rfl⟩ : syracuseStep 875115 = 1312673) B1312673
theorem B875127 : Blo 872567 875127 := bstep (se 1 (by rfl) ⟨656345, by rfl⟩ : syracuseStep 875127 = 1312691) B1312691
theorem B875147 : Blo 872567 875147 := bstep (se 1 (by rfl) ⟨656360, by rfl⟩ : syracuseStep 875147 = 1312721) B1312721
theorem B875159 : Blo 872567 875159 := bstep (se 1 (by rfl) ⟨656369, by rfl⟩ : syracuseStep 875159 = 1312739) B1312739
theorem B875179 : Blo 872567 875179 := bstep (se 1 (by rfl) ⟨656384, by rfl⟩ : syracuseStep 875179 = 1312769) B1312769
theorem B875191 : Blo 872567 875191 := bstep (se 1 (by rfl) ⟨656393, by rfl⟩ : syracuseStep 875191 = 1312787) B1312787
theorem B875211 : Blo 872567 875211 := bstep (se 1 (by rfl) ⟨656408, by rfl⟩ : syracuseStep 875211 = 1312817) B1312817
theorem B875223 : Blo 872567 875223 := bstep (se 1 (by rfl) ⟨656417, by rfl⟩ : syracuseStep 875223 = 1312835) B1312835
theorem B875243 : Blo 872567 875243 := bstep (se 1 (by rfl) ⟨656432, by rfl⟩ : syracuseStep 875243 = 1312865) B1312865
theorem B875255 : Blo 872567 875255 := bstep (se 1 (by rfl) ⟨656441, by rfl⟩ : syracuseStep 875255 = 1312883) B1312883
theorem B875275 : Blo 872567 875275 := bstep (se 1 (by rfl) ⟨656456, by rfl⟩ : syracuseStep 875275 = 1312913) B1312913
theorem B875287 : Blo 872567 875287 := bstep (se 1 (by rfl) ⟨656465, by rfl⟩ : syracuseStep 875287 = 1312931) B1312931
theorem B875307 : Blo 872567 875307 := bstep (se 1 (by rfl) ⟨656480, by rfl⟩ : syracuseStep 875307 = 1312961) B1312961
theorem B875319 : Blo 872567 875319 := bstep (se 1 (by rfl) ⟨656489, by rfl⟩ : syracuseStep 875319 = 1312979) B1312979
theorem B1661771 : Blo 872567 1661771 := bstep (se 1 (by rfl) ⟨1246328, by rfl⟩ : syracuseStep 1661771 = 2492657) B2492657
theorem B875339 : Blo 872567 875339 := bstep (se 1 (by rfl) ⟨656504, by rfl⟩ : syracuseStep 875339 = 1313009) B1313009
theorem B875351 : Blo 872567 875351 := bstep (se 1 (by rfl) ⟨656513, by rfl⟩ : syracuseStep 875351 = 1313027) B1313027
theorem B14932835 : Blo 872567 14932835 := bstep (se 1 (by rfl) ⟨11199626, by rfl⟩ : syracuseStep 14932835 = 22399253) B22399253
theorem B875371 : Blo 872567 875371 := bstep (se 1 (by rfl) ⟨656528, by rfl⟩ : syracuseStep 875371 = 1313057) B1313057
theorem B875383 : Blo 872567 875383 := bstep (se 1 (by rfl) ⟨656537, by rfl⟩ : syracuseStep 875383 = 1313075) B1313075
theorem B1104779 : Blo 872567 1104779 := bstep (se 1 (by rfl) ⟨828584, by rfl⟩ : syracuseStep 1104779 = 1657169) B1657169
theorem B875403 : Blo 872567 875403 := bstep (se 1 (by rfl) ⟨656552, by rfl⟩ : syracuseStep 875403 = 1313105) B1313105
theorem B4971415 : Blo 872567 4971415 := bstep (se 1 (by rfl) ⟨3728561, by rfl⟩ : syracuseStep 4971415 = 7457123) B7457123
theorem B3365783 : Blo 872567 3365783 := bstep (se 1 (by rfl) ⟨2524337, by rfl⟩ : syracuseStep 3365783 = 5048675) B5048675
theorem B1498009 : Blo 872567 1498009 := bstep (se 2 (by rfl) ⟨561753, by rfl⟩ : syracuseStep 1498009 = 1123507) B1123507
theorem B875415 : Blo 872567 875415 := bstep (se 1 (by rfl) ⟨656561, by rfl⟩ : syracuseStep 875415 = 1313123) B1313123
theorem B875435 : Blo 872567 875435 := bstep (se 1 (by rfl) ⟨656576, by rfl⟩ : syracuseStep 875435 = 1313153) B1313153
theorem B875447 : Blo 872567 875447 := bstep (se 1 (by rfl) ⟨656585, by rfl⟩ : syracuseStep 875447 = 1313171) B1313171
theorem B875467 : Blo 872567 875467 := bstep (se 1 (by rfl) ⟨656600, by rfl⟩ : syracuseStep 875467 = 1313201) B1313201
theorem B875479 : Blo 872567 875479 := bstep (se 1 (by rfl) ⟨656609, by rfl⟩ : syracuseStep 875479 = 1313219) B1313219
theorem B875499 : Blo 872567 875499 := bstep (se 1 (by rfl) ⟨656624, by rfl⟩ : syracuseStep 875499 = 1313249) B1313249
theorem B875511 : Blo 872567 875511 := bstep (se 1 (by rfl) ⟨656633, by rfl⟩ : syracuseStep 875511 = 1313267) B1313267
theorem B1661953 : Blo 872567 1661953 := bstep (se 2 (by rfl) ⟨623232, by rfl⟩ : syracuseStep 1661953 = 1246465) B1246465
theorem B875531 : Blo 872567 875531 := bstep (se 1 (by rfl) ⟨656648, by rfl⟩ : syracuseStep 875531 = 1313297) B1313297
theorem B875543 : Blo 872567 875543 := bstep (se 1 (by rfl) ⟨656657, by rfl⟩ : syracuseStep 875543 = 1313315) B1313315
theorem B875563 : Blo 872567 875563 := bstep (se 1 (by rfl) ⟨656672, by rfl⟩ : syracuseStep 875563 = 1313345) B1313345
theorem B875575 : Blo 872567 875575 := bstep (se 1 (by rfl) ⟨656681, by rfl⟩ : syracuseStep 875575 = 1313363) B1313363
theorem B875595 : Blo 872567 875595 := bstep (se 1 (by rfl) ⟨656696, by rfl⟩ : syracuseStep 875595 = 1313393) B1313393
theorem B875607 : Blo 872567 875607 := bstep (se 1 (by rfl) ⟨656705, by rfl⟩ : syracuseStep 875607 = 1313411) B1313411
theorem B875627 : Blo 872567 875627 := bstep (se 1 (by rfl) ⟨656720, by rfl⟩ : syracuseStep 875627 = 1313441) B1313441
theorem B875639 : Blo 872567 875639 := bstep (se 1 (by rfl) ⟨656729, by rfl⟩ : syracuseStep 875639 = 1313459) B1313459
theorem B875659 : Blo 872567 875659 := bstep (se 1 (by rfl) ⟨656744, by rfl⟩ : syracuseStep 875659 = 1313489) B1313489
theorem B875671 : Blo 872567 875671 := bstep (se 1 (by rfl) ⟨656753, by rfl⟩ : syracuseStep 875671 = 1313507) B1313507
theorem B875691 : Blo 872567 875691 := bstep (se 1 (by rfl) ⟨656768, by rfl⟩ : syracuseStep 875691 = 1313537) B1313537
theorem B875703 : Blo 872567 875703 := bstep (se 1 (by rfl) ⟨656777, by rfl⟩ : syracuseStep 875703 = 1313555) B1313555
theorem B875723 : Blo 872567 875723 := bstep (se 1 (by rfl) ⟨656792, by rfl⟩ : syracuseStep 875723 = 1313585) B1313585
theorem B875735 : Blo 872567 875735 := bstep (se 1 (by rfl) ⟨656801, by rfl⟩ : syracuseStep 875735 = 1313603) B1313603
theorem B875755 : Blo 872567 875755 := bstep (se 1 (by rfl) ⟨656816, by rfl⟩ : syracuseStep 875755 = 1313633) B1313633
theorem B875767 : Blo 872567 875767 := bstep (se 1 (by rfl) ⟨656825, by rfl⟩ : syracuseStep 875767 = 1313651) B1313651
theorem B875787 : Blo 872567 875787 := bstep (se 1 (by rfl) ⟨656840, by rfl⟩ : syracuseStep 875787 = 1313681) B1313681
theorem B875799 : Blo 872567 875799 := bstep (se 1 (by rfl) ⟨656849, by rfl⟩ : syracuseStep 875799 = 1313699) B1313699
theorem B875819 : Blo 872567 875819 := bstep (se 1 (by rfl) ⟨656864, by rfl⟩ : syracuseStep 875819 = 1313729) B1313729
theorem B875831 : Blo 872567 875831 := bstep (se 1 (by rfl) ⟨656873, by rfl⟩ : syracuseStep 875831 = 1313747) B1313747
theorem B875851 : Blo 872567 875851 := bstep (se 1 (by rfl) ⟨656888, by rfl⟩ : syracuseStep 875851 = 1313777) B1313777
theorem B1662295 : Blo 872567 1662295 := bstep (se 1 (by rfl) ⟨1246721, by rfl⟩ : syracuseStep 1662295 = 2493443) B2493443
theorem B875863 : Blo 872567 875863 := bstep (se 1 (by rfl) ⟨656897, by rfl⟩ : syracuseStep 875863 = 1313795) B1313795
theorem B875883 : Blo 872567 875883 := bstep (se 1 (by rfl) ⟨656912, by rfl⟩ : syracuseStep 875883 = 1313825) B1313825
theorem B875895 : Blo 872567 875895 := bstep (se 1 (by rfl) ⟨656921, by rfl⟩ : syracuseStep 875895 = 1313843) B1313843
theorem B875915 : Blo 872567 875915 := bstep (se 1 (by rfl) ⟨656936, by rfl⟩ : syracuseStep 875915 = 1313873) B1313873
theorem B875927 : Blo 872567 875927 := bstep (se 1 (by rfl) ⟨656945, by rfl⟩ : syracuseStep 875927 = 1313891) B1313891
theorem B875947 : Blo 872567 875947 := bstep (se 1 (by rfl) ⟨656960, by rfl⟩ : syracuseStep 875947 = 1313921) B1313921
theorem B875959 : Blo 872567 875959 := bstep (se 1 (by rfl) ⟨656969, by rfl⟩ : syracuseStep 875959 = 1313939) B1313939
theorem B875979 : Blo 872567 875979 := bstep (se 1 (by rfl) ⟨656984, by rfl⟩ : syracuseStep 875979 = 1313969) B1313969
theorem B875991 : Blo 872567 875991 := bstep (se 1 (by rfl) ⟨656993, by rfl⟩ : syracuseStep 875991 = 1313987) B1313987
theorem B876011 : Blo 872567 876011 := bstep (se 1 (by rfl) ⟨657008, by rfl⟩ : syracuseStep 876011 = 1314017) B1314017
theorem B876023 : Blo 872567 876023 := bstep (se 1 (by rfl) ⟨657017, by rfl⟩ : syracuseStep 876023 = 1314035) B1314035
theorem B876043 : Blo 872567 876043 := bstep (se 1 (by rfl) ⟨657032, by rfl⟩ : syracuseStep 876043 = 1314065) B1314065
theorem B876055 : Blo 872567 876055 := bstep (se 1 (by rfl) ⟨657041, by rfl⟩ : syracuseStep 876055 = 1314083) B1314083
theorem B876075 : Blo 872567 876075 := bstep (se 1 (by rfl) ⟨657056, by rfl⟩ : syracuseStep 876075 = 1314113) B1314113
theorem B1662515 : Blo 872567 1662515 := bstep (se 1 (by rfl) ⟨1246886, by rfl⟩ : syracuseStep 1662515 = 2493773) B2493773
theorem B876087 : Blo 872567 876087 := bstep (se 1 (by rfl) ⟨657065, by rfl⟩ : syracuseStep 876087 = 1314131) B1314131
theorem B1105483 : Blo 872567 1105483 := bstep (se 1 (by rfl) ⟨829112, by rfl⟩ : syracuseStep 1105483 = 1658225) B1658225
theorem B876107 : Blo 872567 876107 := bstep (se 1 (by rfl) ⟨657080, by rfl⟩ : syracuseStep 876107 = 1314161) B1314161
theorem B876119 : Blo 872567 876119 := bstep (se 1 (by rfl) ⟨657089, by rfl⟩ : syracuseStep 876119 = 1314179) B1314179
theorem B876139 : Blo 872567 876139 := bstep (se 1 (by rfl) ⟨657104, by rfl⟩ : syracuseStep 876139 = 1314209) B1314209
theorem B876151 : Blo 872567 876151 := bstep (se 1 (by rfl) ⟨657113, by rfl⟩ : syracuseStep 876151 = 1314227) B1314227
theorem B876171 : Blo 872567 876171 := bstep (se 1 (by rfl) ⟨657128, by rfl⟩ : syracuseStep 876171 = 1314257) B1314257
theorem B876183 : Blo 872567 876183 := bstep (se 1 (by rfl) ⟨657137, by rfl⟩ : syracuseStep 876183 = 1314275) B1314275
theorem B876203 : Blo 872567 876203 := bstep (se 1 (by rfl) ⟨657152, by rfl⟩ : syracuseStep 876203 = 1314305) B1314305
theorem B876215 : Blo 872567 876215 := bstep (se 1 (by rfl) ⟨657161, by rfl⟩ : syracuseStep 876215 = 1314323) B1314323
theorem B409001669 : Blo 872567 409001669 := bstep (se 4 (by rfl) ⟨38343906, by rfl⟩ : syracuseStep 409001669 = 76687813) B76687813
theorem B876235 : Blo 872567 876235 := bstep (se 1 (by rfl) ⟨657176, by rfl⟩ : syracuseStep 876235 = 1314353) B1314353
theorem B876247 : Blo 872567 876247 := bstep (se 1 (by rfl) ⟨657185, by rfl⟩ : syracuseStep 876247 = 1314371) B1314371
theorem B876267 : Blo 872567 876267 := bstep (se 1 (by rfl) ⟨657200, by rfl⟩ : syracuseStep 876267 = 1314401) B1314401
theorem B876279 : Blo 872567 876279 := bstep (se 1 (by rfl) ⟨657209, by rfl⟩ : syracuseStep 876279 = 1314419) B1314419
theorem B876299 : Blo 872567 876299 := bstep (se 1 (by rfl) ⟨657224, by rfl⟩ : syracuseStep 876299 = 1314449) B1314449
theorem B1662743 : Blo 872567 1662743 := bstep (se 1 (by rfl) ⟨1247057, by rfl⟩ : syracuseStep 1662743 = 2494115) B2494115
theorem B876311 : Blo 872567 876311 := bstep (se 1 (by rfl) ⟨657233, by rfl⟩ : syracuseStep 876311 = 1314467) B1314467
theorem B876331 : Blo 872567 876331 := bstep (se 1 (by rfl) ⟨657248, by rfl⟩ : syracuseStep 876331 = 1314497) B1314497
theorem B876343 : Blo 872567 876343 := bstep (se 1 (by rfl) ⟨657257, by rfl⟩ : syracuseStep 876343 = 1314515) B1314515
theorem B876363 : Blo 872567 876363 := bstep (se 1 (by rfl) ⟨657272, by rfl⟩ : syracuseStep 876363 = 1314545) B1314545
theorem B1105751 : Blo 872567 1105751 := bstep (se 1 (by rfl) ⟨829313, by rfl⟩ : syracuseStep 1105751 = 1658627) B1658627
theorem B876375 : Blo 872567 876375 := bstep (se 1 (by rfl) ⟨657281, by rfl⟩ : syracuseStep 876375 = 1314563) B1314563
theorem B7987045 : Blo 872567 7987045 := bstep (se 4 (by rfl) ⟨748785, by rfl⟩ : syracuseStep 7987045 = 1497571) B1497571
theorem B876395 : Blo 872567 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B12115829 : Blo 872567 12115829 := bstep (se 5 (by rfl) ⟨567929, by rfl⟩ : syracuseStep 12115829 = 1135859) B1135859
theorem B876407 : Blo 872567 876407 := bstep (se 1 (by rfl) ⟨657305, by rfl⟩ : syracuseStep 876407 = 1314611) B1314611
theorem B876427 : Blo 872567 876427 := bstep (se 1 (by rfl) ⟨657320, by rfl⟩ : syracuseStep 876427 = 1314641) B1314641
theorem B876439 : Blo 872567 876439 := bstep (se 1 (by rfl) ⟨657329, by rfl⟩ : syracuseStep 876439 = 1314659) B1314659
theorem B876459 : Blo 872567 876459 := bstep (se 1 (by rfl) ⟨657344, by rfl⟩ : syracuseStep 876459 = 1314689) B1314689
theorem B876471 : Blo 872567 876471 := bstep (se 1 (by rfl) ⟨657353, by rfl⟩ : syracuseStep 876471 = 1314707) B1314707
theorem B876491 : Blo 872567 876491 := bstep (se 1 (by rfl) ⟨657368, by rfl⟩ : syracuseStep 876491 = 1314737) B1314737
theorem B876503 : Blo 872567 876503 := bstep (se 1 (by rfl) ⟨657377, by rfl⟩ : syracuseStep 876503 = 1314755) B1314755
theorem B876523 : Blo 872567 876523 := bstep (se 1 (by rfl) ⟨657392, by rfl⟩ : syracuseStep 876523 = 1314785) B1314785
theorem B876535 : Blo 872567 876535 := bstep (se 1 (by rfl) ⟨657401, by rfl⟩ : syracuseStep 876535 = 1314803) B1314803
theorem B876555 : Blo 872567 876555 := bstep (se 1 (by rfl) ⟨657416, by rfl⟩ : syracuseStep 876555 = 1314833) B1314833
theorem B876567 : Blo 872567 876567 := bstep (se 1 (by rfl) ⟨657425, by rfl⟩ : syracuseStep 876567 = 1314851) B1314851
theorem B1663001 : Blo 872567 1663001 := bstep (se 2 (by rfl) ⟨623625, by rfl⟩ : syracuseStep 1663001 = 1247251) B1247251
theorem B1663411 : Blo 872567 1663411 := bstep (se 1 (by rfl) ⟨1247558, by rfl⟩ : syracuseStep 1663411 = 2495117) B2495117
theorem B3990019 : Blo 872567 3990019 := bstep (se 1 (by rfl) ⟨2992514, by rfl⟩ : syracuseStep 3990019 = 5985029) B5985029
theorem B10117649 : Blo 872567 10117649 := bstep (se 2 (by rfl) ⟨3794118, by rfl⟩ : syracuseStep 10117649 = 7588237) B7588237
theorem B1106455 : Blo 872567 1106455 := bstep (se 1 (by rfl) ⟨829841, by rfl⟩ : syracuseStep 1106455 = 1659683) B1659683
theorem B5595713 : Blo 872567 5595713 := bstep (se 2 (by rfl) ⟨2098392, by rfl⟩ : syracuseStep 5595713 = 4196785) B4196785
theorem B3728051 : Blo 872567 3728051 := bstep (se 1 (by rfl) ⟨2796038, by rfl⟩ : syracuseStep 3728051 = 5592077) B5592077
theorem B1663897 : Blo 872567 1663897 := bstep (se 2 (by rfl) ⟨623961, by rfl⟩ : syracuseStep 1663897 = 1247923) B1247923
theorem B217933253 : Blo 872567 217933253 := bstep (se 4 (by rfl) ⟨20431242, by rfl⟩ : syracuseStep 217933253 = 40862485) B40862485
theorem B3729041 : Blo 872567 3729041 := bstep (se 2 (by rfl) ⟨1398390, by rfl⟩ : syracuseStep 3729041 = 2796781) B2796781
theorem B14215013 : Blo 872567 14215013 := bstep (se 4 (by rfl) ⟨1332657, by rfl⟩ : syracuseStep 14215013 = 2665315) B2665315
theorem B5597201 : Blo 872567 5597201 := bstep (se 2 (by rfl) ⟨2098950, by rfl⟩ : syracuseStep 5597201 = 4197901) B4197901
theorem B1108171 : Blo 872567 1108171 := bstep (se 1 (by rfl) ⟨831128, by rfl⟩ : syracuseStep 1108171 = 1662257) B1662257
theorem B7989521 : Blo 872567 7989521 := bstep (se 2 (by rfl) ⟨2996070, by rfl⟩ : syracuseStep 7989521 = 5992141) B5992141
theorem B60615029 : Blo 872567 60615029 := bstep (se 5 (by rfl) ⟨2841329, by rfl⟩ : syracuseStep 60615029 = 5682659) B5682659
theorem B4418711 : Blo 872567 4418711 := bstep (se 1 (by rfl) ⟨3314033, by rfl⟩ : syracuseStep 4418711 = 6628067) B6628067
theorem B1109143 : Blo 872567 1109143 := bstep (se 1 (by rfl) ⟨831857, by rfl⟩ : syracuseStep 1109143 = 1663715) B1663715
theorem B1797569 : Blo 872567 1797569 := bstep (se 2 (by rfl) ⟨674088, by rfl⟩ : syracuseStep 1797569 = 1348177) B1348177
theorem B2485981 : Blo 872567 2485981 := bstep (se 3 (by rfl) ⟨466121, by rfl⟩ : syracuseStep 2485981 = 932243) B932243
theorem B2486209 : Blo 872567 2486209 := bstep (se 2 (by rfl) ⟨932328, by rfl⟩ : syracuseStep 2486209 = 1864657) B1864657
theorem B1437655 : Blo 872567 1437655 := bstep (se 1 (by rfl) ⟨1078241, by rfl⟩ : syracuseStep 1437655 = 2156483) B2156483
theorem B3731417 : Blo 872567 3731417 := bstep (se 2 (by rfl) ⟨1399281, by rfl⟩ : syracuseStep 3731417 = 2798563) B2798563
theorem B3731501 : Blo 872567 3731501 := bstep (se 3 (by rfl) ⟨699656, by rfl⟩ : syracuseStep 3731501 = 1399313) B1399313
theorem B1863769 : Blo 872567 1863769 := bstep (se 2 (by rfl) ⟨698913, by rfl⟩ : syracuseStep 1863769 = 1397827) B1397827
theorem B2486551 : Blo 872567 2486551 := bstep (se 1 (by rfl) ⟨1864913, by rfl⟩ : syracuseStep 2486551 = 3729827) B3729827
theorem B2945483 : Blo 872567 2945483 := bstep (se 1 (by rfl) ⟨2209112, by rfl⟩ : syracuseStep 2945483 = 4418225) B4418225
theorem B2945753 : Blo 872567 2945753 := bstep (se 2 (by rfl) ⟨1104657, by rfl⟩ : syracuseStep 2945753 = 2209315) B2209315
theorem B2487257 : Blo 872567 2487257 := bstep (se 2 (by rfl) ⟨932721, by rfl⟩ : syracuseStep 2487257 = 1865443) B1865443
theorem B947371 : Blo 872567 947371 := bstep (se 1 (by rfl) ⟨710528, by rfl⟩ : syracuseStep 947371 = 1421057) B1421057
theorem B1963403 : Blo 872567 1963403 := bstep (se 1 (by rfl) ⟨1472552, by rfl⟩ : syracuseStep 1963403 = 2945105) B2945105
theorem B2946455 : Blo 872567 2946455 := bstep (se 1 (by rfl) ⟨2209841, by rfl⟩ : syracuseStep 2946455 = 4419683) B4419683
theorem B1963457 : Blo 872567 1963457 := bstep (se 2 (by rfl) ⟨736296, by rfl⟩ : syracuseStep 1963457 = 1472593) B1472593
theorem B1242649 : Blo 872567 1242649 := bstep (se 2 (by rfl) ⟨465993, by rfl⟩ : syracuseStep 1242649 = 931987) B931987
theorem B1963673 : Blo 872567 1963673 := bstep (se 2 (by rfl) ⟨736377, by rfl⟩ : syracuseStep 1963673 = 1472755) B1472755
theorem B1963763 : Blo 872567 1963763 := bstep (se 1 (by rfl) ⟨1472822, by rfl⟩ : syracuseStep 1963763 = 2945645) B2945645
theorem B1963799 : Blo 872567 1963799 := bstep (se 1 (by rfl) ⟨1472849, by rfl⟩ : syracuseStep 1963799 = 2945699) B2945699
theorem B12613421 : Blo 872567 12613421 := bstep (se 3 (by rfl) ⟨2365016, by rfl⟩ : syracuseStep 12613421 = 4730033) B4730033
theorem B2946995 : Blo 872567 2946995 := bstep (se 1 (by rfl) ⟨2210246, by rfl⟩ : syracuseStep 2946995 = 4420493) B4420493
theorem B1963979 : Blo 872567 1963979 := bstep (se 1 (by rfl) ⟨1472984, by rfl⟩ : syracuseStep 1963979 = 2945969) B2945969
theorem B1964033 : Blo 872567 1964033 := bstep (se 2 (by rfl) ⟨736512, by rfl⟩ : syracuseStep 1964033 = 1473025) B1473025
theorem B8386577 : Blo 872567 8386577 := bstep (se 2 (by rfl) ⟨3144966, by rfl⟩ : syracuseStep 8386577 = 6289933) B6289933
theorem B4978705 : Blo 872567 4978705 := bstep (se 2 (by rfl) ⟨1867014, by rfl⟩ : syracuseStep 4978705 = 3734029) B3734029
theorem B7960621 : Blo 872567 7960621 := bstep (se 3 (by rfl) ⟨1492616, by rfl⟩ : syracuseStep 7960621 = 2985233) B2985233
theorem B8419403 : Blo 872567 8419403 := bstep (se 1 (by rfl) ⟨6314552, by rfl⟩ : syracuseStep 8419403 = 12629105) B12629105
theorem B2947265 : Blo 872567 2947265 := bstep (se 2 (by rfl) ⟨1105224, by rfl⟩ : syracuseStep 2947265 = 2210449) B2210449
theorem B1865921 : Blo 872567 1865921 := bstep (se 2 (by rfl) ⟨699720, by rfl⟩ : syracuseStep 1865921 = 1399441) B1399441
theorem B1308875 : Blo 872567 1308875 := bstep (se 1 (by rfl) ⟨981656, by rfl⟩ : syracuseStep 1308875 = 1963313) B1963313
theorem B1308887 : Blo 872567 1308887 := bstep (se 1 (by rfl) ⟨981665, by rfl⟩ : syracuseStep 1308887 = 1963331) B1963331
theorem B1964249 : Blo 872567 1964249 := bstep (se 2 (by rfl) ⟨736593, by rfl⟩ : syracuseStep 1964249 = 1473187) B1473187
theorem B5994769 : Blo 872567 5994769 := bstep (se 2 (by rfl) ⟨2248038, by rfl⟩ : syracuseStep 5994769 = 4496077) B4496077
theorem B1866007 : Blo 872567 1866007 := bstep (se 1 (by rfl) ⟨1399505, by rfl⟩ : syracuseStep 1866007 = 2799011) B2799011
theorem B1308953 : Blo 872567 1308953 := bstep (se 2 (by rfl) ⟨490857, by rfl⟩ : syracuseStep 1308953 = 981715) B981715
theorem B1964339 : Blo 872567 1964339 := bstep (se 1 (by rfl) ⟨1473254, by rfl⟩ : syracuseStep 1964339 = 2946509) B2946509
theorem B1472843 : Blo 872567 1472843 := bstep (se 1 (by rfl) ⟨1104632, by rfl⟩ : syracuseStep 1472843 = 2209265) B2209265
theorem B1964375 : Blo 872567 1964375 := bstep (se 1 (by rfl) ⟨1473281, by rfl⟩ : syracuseStep 1964375 = 2946563) B2946563
theorem B2881885 : Blo 872567 2881885 := bstep (se 3 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 2881885 = 1080707) B1080707
theorem B1309067 : Blo 872567 1309067 := bstep (se 1 (by rfl) ⟨981800, by rfl⟩ : syracuseStep 1309067 = 1963601) B1963601
theorem B1309079 : Blo 872567 1309079 := bstep (se 1 (by rfl) ⟨981809, by rfl⟩ : syracuseStep 1309079 = 1963619) B1963619
theorem B1472971 : Blo 872567 1472971 := bstep (se 1 (by rfl) ⟨1104728, by rfl⟩ : syracuseStep 1472971 = 2209457) B2209457
theorem B1309145 : Blo 872567 1309145 := bstep (se 2 (by rfl) ⟨490929, by rfl⟩ : syracuseStep 1309145 = 981859) B981859
theorem B1964555 : Blo 872567 1964555 := bstep (se 1 (by rfl) ⟨1473416, by rfl⟩ : syracuseStep 1964555 = 2946833) B2946833
theorem B1964609 : Blo 872567 1964609 := bstep (se 2 (by rfl) ⟨736728, by rfl⟩ : syracuseStep 1964609 = 1473457) B1473457
theorem B2488897 : Blo 872567 2488897 := bstep (se 2 (by rfl) ⟨933336, by rfl⟩ : syracuseStep 2488897 = 1866673) B1866673
theorem B1309259 : Blo 872567 1309259 := bstep (se 1 (by rfl) ⟨981944, by rfl⟩ : syracuseStep 1309259 = 1963889) B1963889
theorem B1309271 : Blo 872567 1309271 := bstep (se 1 (by rfl) ⟨981953, by rfl⟩ : syracuseStep 1309271 = 1963907) B1963907
theorem B1473113 : Blo 872567 1473113 := bstep (se 2 (by rfl) ⟨552417, by rfl⟩ : syracuseStep 1473113 = 1104835) B1104835
theorem B4422275 : Blo 872567 4422275 := bstep (se 1 (by rfl) ⟨3316706, by rfl⟩ : syracuseStep 4422275 = 6633413) B6633413
theorem B981643 : Blo 872567 981643 := bstep (se 1 (by rfl) ⟨736232, by rfl⟩ : syracuseStep 981643 = 1472465) B1472465
theorem B1309337 : Blo 872567 1309337 := bstep (se 2 (by rfl) ⟨491001, by rfl⟩ : syracuseStep 1309337 = 982003) B982003
theorem B1473241 : Blo 872567 1473241 := bstep (se 2 (by rfl) ⟨552465, by rfl⟩ : syracuseStep 1473241 = 1104931) B1104931
theorem B2947805 : Blo 872567 2947805 := bstep (se 3 (by rfl) ⟨552713, by rfl⟩ : syracuseStep 2947805 = 1105427) B1105427
theorem B981751 : Blo 872567 981751 := bstep (se 1 (by rfl) ⟨736313, by rfl⟩ : syracuseStep 981751 = 1472627) B1472627
theorem B1309451 : Blo 872567 1309451 := bstep (se 1 (by rfl) ⟨982088, by rfl⟩ : syracuseStep 1309451 = 1964177) B1964177
theorem B1309463 : Blo 872567 1309463 := bstep (se 1 (by rfl) ⟨982097, by rfl⟩ : syracuseStep 1309463 = 1964195) B1964195
theorem B1964825 : Blo 872567 1964825 := bstep (se 2 (by rfl) ⟨736809, by rfl⟩ : syracuseStep 1964825 = 1473619) B1473619
theorem B1309529 : Blo 872567 1309529 := bstep (se 2 (by rfl) ⟨491073, by rfl⟩ : syracuseStep 1309529 = 982147) B982147
theorem B1243993 : Blo 872567 1243993 := bstep (se 2 (by rfl) ⟨466497, by rfl⟩ : syracuseStep 1243993 = 932995) B932995
theorem B1964915 : Blo 872567 1964915 := bstep (se 1 (by rfl) ⟨1473686, by rfl⟩ : syracuseStep 1964915 = 2947373) B2947373
theorem B1964951 : Blo 872567 1964951 := bstep (se 1 (by rfl) ⟨1473713, by rfl⟩ : syracuseStep 1964951 = 2947427) B2947427
theorem B981931 : Blo 872567 981931 := bstep (se 1 (by rfl) ⟨736448, by rfl⟩ : syracuseStep 981931 = 1472897) B1472897
theorem B1997747 : Blo 872567 1997747 := bstep (se 1 (by rfl) ⟨1498310, by rfl⟩ : syracuseStep 1997747 = 2996621) B2996621
theorem B1309643 : Blo 872567 1309643 := bstep (se 1 (by rfl) ⟨982232, by rfl⟩ : syracuseStep 1309643 = 1964465) B1964465
theorem B1244107 : Blo 872567 1244107 := bstep (se 1 (by rfl) ⟨933080, by rfl⟩ : syracuseStep 1244107 = 1866161) B1866161
theorem B1309655 : Blo 872567 1309655 := bstep (se 1 (by rfl) ⟨982241, by rfl⟩ : syracuseStep 1309655 = 1964483) B1964483
theorem B982039 : Blo 872567 982039 := bstep (se 1 (by rfl) ⟨736529, by rfl⟩ : syracuseStep 982039 = 1473059) B1473059
theorem B1309721 : Blo 872567 1309721 := bstep (se 2 (by rfl) ⟨491145, by rfl⟩ : syracuseStep 1309721 = 982291) B982291
theorem B63765539 : Blo 872567 63765539 := bstep (se 1 (by rfl) ⟨47824154, by rfl⟩ : syracuseStep 63765539 = 95648309) B95648309
theorem B1965131 : Blo 872567 1965131 := bstep (se 1 (by rfl) ⟨1473848, by rfl⟩ : syracuseStep 1965131 = 2947697) B2947697
theorem B1866827 : Blo 872567 1866827 := bstep (se 1 (by rfl) ⟨1400120, by rfl⟩ : syracuseStep 1866827 = 2800241) B2800241
theorem B1965185 : Blo 872567 1965185 := bstep (se 2 (by rfl) ⟨736944, by rfl⟩ : syracuseStep 1965185 = 1473889) B1473889
theorem B1309835 : Blo 872567 1309835 := bstep (se 1 (by rfl) ⟨982376, by rfl⟩ : syracuseStep 1309835 = 1964753) B1964753
theorem B1309847 : Blo 872567 1309847 := bstep (se 1 (by rfl) ⟨982385, by rfl⟩ : syracuseStep 1309847 = 1964771) B1964771
theorem B982219 : Blo 872567 982219 := bstep (se 1 (by rfl) ⟨736664, by rfl⟩ : syracuseStep 982219 = 1473329) B1473329
theorem B1309913 : Blo 872567 1309913 := bstep (se 2 (by rfl) ⟨491217, by rfl⟩ : syracuseStep 1309913 = 982435) B982435
theorem B1473815 : Blo 872567 1473815 := bstep (se 1 (by rfl) ⟨1105361, by rfl⟩ : syracuseStep 1473815 = 2210723) B2210723
theorem B982327 : Blo 872567 982327 := bstep (se 1 (by rfl) ⟨736745, by rfl⟩ : syracuseStep 982327 = 1473491) B1473491
theorem B3734849 : Blo 872567 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B1310027 : Blo 872567 1310027 := bstep (se 1 (by rfl) ⟨982520, by rfl⟩ : syracuseStep 1310027 = 1965041) B1965041
theorem B1310039 : Blo 872567 1310039 := bstep (se 1 (by rfl) ⟨982529, by rfl⟩ : syracuseStep 1310039 = 1965059) B1965059
theorem B1965401 : Blo 872567 1965401 := bstep (se 2 (by rfl) ⟨737025, by rfl⟩ : syracuseStep 1965401 = 1474051) B1474051
theorem B4717925 : Blo 872567 4717925 := bstep (se 4 (by rfl) ⟨442305, by rfl⟩ : syracuseStep 4717925 = 884611) B884611
theorem B1473943 : Blo 872567 1473943 := bstep (se 1 (by rfl) ⟨1105457, by rfl⟩ : syracuseStep 1473943 = 2210915) B2210915
theorem B1310105 : Blo 872567 1310105 := bstep (se 2 (by rfl) ⟨491289, by rfl⟩ : syracuseStep 1310105 = 982579) B982579
theorem B1965491 : Blo 872567 1965491 := bstep (se 1 (by rfl) ⟨1474118, by rfl⟩ : syracuseStep 1965491 = 2948237) B2948237
theorem B3538379 : Blo 872567 3538379 := bstep (se 1 (by rfl) ⟨2653784, by rfl⟩ : syracuseStep 3538379 = 5307569) B5307569
theorem B1965527 : Blo 872567 1965527 := bstep (se 1 (by rfl) ⟨1474145, by rfl⟩ : syracuseStep 1965527 = 2948291) B2948291
theorem B982507 : Blo 872567 982507 := bstep (se 1 (by rfl) ⟨736880, by rfl⟩ : syracuseStep 982507 = 1473761) B1473761
theorem B1998323 : Blo 872567 1998323 := bstep (se 1 (by rfl) ⟨1498742, by rfl⟩ : syracuseStep 1998323 = 2997485) B2997485
theorem B1310219 : Blo 872567 1310219 := bstep (se 1 (by rfl) ⟨982664, by rfl⟩ : syracuseStep 1310219 = 1965329) B1965329
theorem B1310231 : Blo 872567 1310231 := bstep (se 1 (by rfl) ⟨982673, by rfl⟩ : syracuseStep 1310231 = 1965347) B1965347
theorem B982615 : Blo 872567 982615 := bstep (se 1 (by rfl) ⟨736961, by rfl⟩ : syracuseStep 982615 = 1473923) B1473923
theorem B1310297 : Blo 872567 1310297 := bstep (se 2 (by rfl) ⟨491361, by rfl⟩ : syracuseStep 1310297 = 982723) B982723
theorem B2358877 : Blo 872567 2358877 := bstep (se 3 (by rfl) ⟨442289, by rfl⟩ : syracuseStep 2358877 = 884579) B884579
theorem B1965707 : Blo 872567 1965707 := bstep (se 1 (by rfl) ⟨1474280, by rfl⟩ : syracuseStep 1965707 = 2948561) B2948561
theorem B5308055 : Blo 872567 5308055 := bstep (se 1 (by rfl) ⟨3981041, by rfl⟩ : syracuseStep 5308055 = 7962083) B7962083
theorem B1965761 : Blo 872567 1965761 := bstep (se 2 (by rfl) ⟨737160, by rfl⟩ : syracuseStep 1965761 = 1474321) B1474321
theorem B1310411 : Blo 872567 1310411 := bstep (se 1 (by rfl) ⟨982808, by rfl⟩ : syracuseStep 1310411 = 1965617) B1965617
theorem B40402637 : Blo 872567 40402637 := bstep (se 3 (by rfl) ⟨7575494, by rfl⟩ : syracuseStep 40402637 = 15150989) B15150989
theorem B1310423 : Blo 872567 1310423 := bstep (se 1 (by rfl) ⟨982817, by rfl⟩ : syracuseStep 1310423 = 1965635) B1965635
theorem B982795 : Blo 872567 982795 := bstep (se 1 (by rfl) ⟨737096, by rfl⟩ : syracuseStep 982795 = 1474193) B1474193
theorem B1310489 : Blo 872567 1310489 := bstep (se 2 (by rfl) ⟨491433, by rfl⟩ : syracuseStep 1310489 = 982867) B982867
theorem B2948939 : Blo 872567 2948939 := bstep (se 1 (by rfl) ⟨2211704, by rfl⟩ : syracuseStep 2948939 = 4423409) B4423409
theorem B982903 : Blo 872567 982903 := bstep (se 1 (by rfl) ⟨737177, by rfl⟩ : syracuseStep 982903 = 1474355) B1474355
theorem B1310603 : Blo 872567 1310603 := bstep (se 1 (by rfl) ⟨982952, by rfl⟩ : syracuseStep 1310603 = 1965905) B1965905
theorem B1310615 : Blo 872567 1310615 := bstep (se 1 (by rfl) ⟨982961, by rfl⟩ : syracuseStep 1310615 = 1965923) B1965923
theorem B1965977 : Blo 872567 1965977 := bstep (se 2 (by rfl) ⟨737241, by rfl⟩ : syracuseStep 1965977 = 1474483) B1474483
theorem B40468403 : Blo 872567 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B1310681 : Blo 872567 1310681 := bstep (se 2 (by rfl) ⟨491505, by rfl⟩ : syracuseStep 1310681 = 983011) B983011
theorem B3735517 : Blo 872567 3735517 := bstep (se 3 (by rfl) ⟨700409, by rfl⟩ : syracuseStep 3735517 = 1400819) B1400819
theorem B1966067 : Blo 872567 1966067 := bstep (se 1 (by rfl) ⟨1474550, by rfl⟩ : syracuseStep 1966067 = 2949101) B2949101
theorem B983047 : Blo 872567 983047 := bstep (se 1 (by rfl) ⟨737285, by rfl⟩ : syracuseStep 983047 = 1474571) B1474571
theorem B1310735 : Blo 872567 1310735 := bstep (se 1 (by rfl) ⟨983051, by rfl⟩ : syracuseStep 1310735 = 1966103) B1966103
theorem B2490401 : Blo 872567 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B1310777 : Blo 872567 1310777 := bstep (se 2 (by rfl) ⟨491541, by rfl⟩ : syracuseStep 1310777 = 983083) B983083
theorem B1966139 : Blo 872567 1966139 := bstep (se 1 (by rfl) ⟨1474604, by rfl⟩ : syracuseStep 1966139 = 2949209) B2949209
theorem B1867835 : Blo 872567 1867835 := bstep (se 1 (by rfl) ⟨1400876, by rfl⟩ : syracuseStep 1867835 = 2801753) B2801753
theorem B1474679 : Blo 872567 1474679 := bstep (se 1 (by rfl) ⟨1106009, by rfl⟩ : syracuseStep 1474679 = 2212019) B2212019
theorem B1310855 : Blo 872567 1310855 := bstep (se 1 (by rfl) ⟨983141, by rfl⟩ : syracuseStep 1310855 = 1966283) B1966283
theorem B1310891 : Blo 872567 1310891 := bstep (se 1 (by rfl) ⟨983168, by rfl⟩ : syracuseStep 1310891 = 1966337) B1966337
theorem B1966265 : Blo 872567 1966265 := bstep (se 2 (by rfl) ⟨737349, by rfl⟩ : syracuseStep 1966265 = 1474699) B1474699
theorem B983227 : Blo 872567 983227 := bstep (se 1 (by rfl) ⟨737420, by rfl⟩ : syracuseStep 983227 = 1474841) B1474841
theorem B1310921 : Blo 872567 1310921 := bstep (se 2 (by rfl) ⟨491595, by rfl⟩ : syracuseStep 1310921 = 983191) B983191
theorem B9470189 : Blo 872567 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B3735841 : Blo 872567 3735841 := bstep (se 2 (by rfl) ⟨1400940, by rfl⟩ : syracuseStep 3735841 = 2801881) B2801881
theorem B5112115 : Blo 872567 5112115 := bstep (se 1 (by rfl) ⟨3834086, by rfl⟩ : syracuseStep 5112115 = 7668173) B7668173
theorem B1311035 : Blo 872567 1311035 := bstep (se 1 (by rfl) ⟨983276, by rfl⟩ : syracuseStep 1311035 = 1966553) B1966553
theorem B1311095 : Blo 872567 1311095 := bstep (se 1 (by rfl) ⟨983321, by rfl⟩ : syracuseStep 1311095 = 1966643) B1966643
theorem B2490743 : Blo 872567 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B1311119 : Blo 872567 1311119 := bstep (se 1 (by rfl) ⟨983339, by rfl⟩ : syracuseStep 1311119 = 1966679) B1966679
theorem B6390161 : Blo 872567 6390161 := bstep (se 2 (by rfl) ⟨2396310, by rfl⟩ : syracuseStep 6390161 = 4792621) B4792621
theorem B1311161 : Blo 872567 1311161 := bstep (se 2 (by rfl) ⟨491685, by rfl⟩ : syracuseStep 1311161 = 983371) B983371
theorem B5046731 : Blo 872567 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B1311239 : Blo 872567 1311239 := bstep (se 1 (by rfl) ⟨983429, by rfl⟩ : syracuseStep 1311239 = 1966859) B1966859
theorem B4194827 : Blo 872567 4194827 := bstep (se 1 (by rfl) ⟨3146120, by rfl⟩ : syracuseStep 4194827 = 6292241) B6292241
theorem B1573391 : Blo 872567 1573391 := bstep (se 1 (by rfl) ⟨1180043, by rfl⟩ : syracuseStep 1573391 = 2360087) B2360087
theorem B1966607 : Blo 872567 1966607 := bstep (se 1 (by rfl) ⟨1474955, by rfl⟩ : syracuseStep 1966607 = 2949911) B2949911
theorem B1966625 : Blo 872567 1966625 := bstep (se 2 (by rfl) ⟨737484, by rfl⟩ : syracuseStep 1966625 = 1474969) B1474969
theorem B1311275 : Blo 872567 1311275 := bstep (se 1 (by rfl) ⟨983456, by rfl⟩ : syracuseStep 1311275 = 1966913) B1966913
theorem B1180217 : Blo 872567 1180217 := bstep (se 2 (by rfl) ⟨442581, by rfl⟩ : syracuseStep 1180217 = 885163) B885163
theorem B1475131 : Blo 872567 1475131 := bstep (se 1 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 1475131 = 2212697) B2212697
theorem B1311305 : Blo 872567 1311305 := bstep (se 2 (by rfl) ⟨491739, by rfl⟩ : syracuseStep 1311305 = 983479) B983479
theorem B983695 : Blo 872567 983695 := bstep (se 1 (by rfl) ⟨737771, by rfl⟩ : syracuseStep 983695 = 1475543) B1475543
theorem B1311419 : Blo 872567 1311419 := bstep (se 1 (by rfl) ⟨983564, by rfl⟩ : syracuseStep 1311419 = 1967129) B1967129
theorem B1475273 : Blo 872567 1475273 := bstep (se 2 (by rfl) ⟨553227, by rfl⟩ : syracuseStep 1475273 = 1106455) B1106455
theorem B1311479 : Blo 872567 1311479 := bstep (se 1 (by rfl) ⟨983609, by rfl⟩ : syracuseStep 1311479 = 1967219) B1967219
theorem B1311503 : Blo 872567 1311503 := bstep (se 1 (by rfl) ⟨983627, by rfl⟩ : syracuseStep 1311503 = 1967255) B1967255
theorem B5309221 : Blo 872567 5309221 := bstep (se 4 (by rfl) ⟨497739, by rfl⟩ : syracuseStep 5309221 = 995479) B995479
theorem B1311545 : Blo 872567 1311545 := bstep (se 2 (by rfl) ⟨491829, by rfl⟩ : syracuseStep 1311545 = 983659) B983659
theorem B1966967 : Blo 872567 1966967 := bstep (se 1 (by rfl) ⟨1475225, by rfl⟩ : syracuseStep 1966967 = 2950451) B2950451
theorem B1311623 : Blo 872567 1311623 := bstep (se 1 (by rfl) ⟨983717, by rfl⟩ : syracuseStep 1311623 = 1967435) B1967435
theorem B1311659 : Blo 872567 1311659 := bstep (se 1 (by rfl) ⟨983744, by rfl⟩ : syracuseStep 1311659 = 1967489) B1967489
theorem B2950073 : Blo 872567 2950073 := bstep (se 2 (by rfl) ⟨1106277, by rfl⟩ : syracuseStep 2950073 = 2212555) B2212555
theorem B1311689 : Blo 872567 1311689 := bstep (se 2 (by rfl) ⟨491883, by rfl⟩ : syracuseStep 1311689 = 983767) B983767
theorem B1967147 : Blo 872567 1967147 := bstep (se 1 (by rfl) ⟨1475360, by rfl⟩ : syracuseStep 1967147 = 2950721) B2950721
theorem B1311803 : Blo 872567 1311803 := bstep (se 1 (by rfl) ⟨983852, by rfl⟩ : syracuseStep 1311803 = 1967705) B1967705
theorem B3146813 : Blo 872567 3146813 := bstep (se 3 (by rfl) ⟨590027, by rfl⟩ : syracuseStep 3146813 = 1180055) B1180055
theorem B1311863 : Blo 872567 1311863 := bstep (se 1 (by rfl) ⟨983897, by rfl⟩ : syracuseStep 1311863 = 1967795) B1967795
theorem B984199 : Blo 872567 984199 := bstep (se 1 (by rfl) ⟨738149, by rfl⟩ : syracuseStep 984199 = 1476299) B1476299
theorem B1311887 : Blo 872567 1311887 := bstep (se 1 (by rfl) ⟨983915, by rfl⟩ : syracuseStep 1311887 = 1967831) B1967831
theorem B1311929 : Blo 872567 1311929 := bstep (se 2 (by rfl) ⟨491973, by rfl⟩ : syracuseStep 1311929 = 983947) B983947
theorem B4719809 : Blo 872567 4719809 := bstep (se 2 (by rfl) ⟨1769928, by rfl⟩ : syracuseStep 4719809 = 3539857) B3539857
theorem B1312007 : Blo 872567 1312007 := bstep (se 1 (by rfl) ⟨984005, by rfl⟩ : syracuseStep 1312007 = 1968011) B1968011
theorem B1312043 : Blo 872567 1312043 := bstep (se 1 (by rfl) ⟨984032, by rfl⟩ : syracuseStep 1312043 = 1968065) B1968065
theorem B984379 : Blo 872567 984379 := bstep (se 1 (by rfl) ⟨738284, by rfl⟩ : syracuseStep 984379 = 1476569) B1476569
theorem B4621627 : Blo 872567 4621627 := bstep (se 1 (by rfl) ⟨3466220, by rfl⟩ : syracuseStep 4621627 = 6932441) B6932441
theorem B1312073 : Blo 872567 1312073 := bstep (se 2 (by rfl) ⟨492027, by rfl⟩ : syracuseStep 1312073 = 984055) B984055
theorem B2557271 : Blo 872567 2557271 := bstep (se 1 (by rfl) ⟨1917953, by rfl⟩ : syracuseStep 2557271 = 3835907) B3835907
theorem B1475975 : Blo 872567 1475975 := bstep (se 1 (by rfl) ⟨1106981, by rfl⟩ : syracuseStep 1475975 = 2213963) B2213963
theorem B1967507 : Blo 872567 1967507 := bstep (se 1 (by rfl) ⟨1475630, by rfl⟩ : syracuseStep 1967507 = 2951261) B2951261
theorem B1574329 : Blo 872567 1574329 := bstep (se 2 (by rfl) ⟨590373, by rfl⟩ : syracuseStep 1574329 = 1180747) B1180747
theorem B1312187 : Blo 872567 1312187 := bstep (se 1 (by rfl) ⟨984140, by rfl⟩ : syracuseStep 1312187 = 1968281) B1968281
theorem B1967561 : Blo 872567 1967561 := bstep (se 2 (by rfl) ⟨737835, by rfl⟩ : syracuseStep 1967561 = 1475671) B1475671
theorem B1312247 : Blo 872567 1312247 := bstep (se 1 (by rfl) ⟨984185, by rfl⟩ : syracuseStep 1312247 = 1968371) B1968371
theorem B10651139 : Blo 872567 10651139 := bstep (se 1 (by rfl) ⟨7988354, by rfl⟩ : syracuseStep 10651139 = 15976709) B15976709
theorem B2950667 : Blo 872567 2950667 := bstep (se 1 (by rfl) ⟨2213000, by rfl⟩ : syracuseStep 2950667 = 4426001) B4426001
theorem B1312271 : Blo 872567 1312271 := bstep (se 1 (by rfl) ⟨984203, by rfl⟩ : syracuseStep 1312271 = 1968407) B1968407
theorem B1312313 : Blo 872567 1312313 := bstep (se 2 (by rfl) ⟨492117, by rfl⟩ : syracuseStep 1312313 = 984235) B984235
theorem B2950775 : Blo 872567 2950775 := bstep (se 1 (by rfl) ⟨2213081, by rfl⟩ : syracuseStep 2950775 = 4426163) B4426163
theorem B1312391 : Blo 872567 1312391 := bstep (se 1 (by rfl) ⟨984293, by rfl⟩ : syracuseStep 1312391 = 1968587) B1968587
theorem B1312427 : Blo 872567 1312427 := bstep (se 1 (by rfl) ⟨984320, by rfl⟩ : syracuseStep 1312427 = 1968641) B1968641
theorem B1312457 : Blo 872567 1312457 := bstep (se 2 (by rfl) ⟨492171, by rfl⟩ : syracuseStep 1312457 = 984343) B984343
theorem B984847 : Blo 872567 984847 := bstep (se 1 (by rfl) ⟨738635, by rfl⟩ : syracuseStep 984847 = 1477271) B1477271
theorem B4982579 : Blo 872567 4982579 := bstep (se 1 (by rfl) ⟨3736934, by rfl⟩ : syracuseStep 4982579 = 7473869) B7473869
theorem B1312571 : Blo 872567 1312571 := bstep (se 1 (by rfl) ⟨984428, by rfl⟩ : syracuseStep 1312571 = 1968857) B1968857
theorem B1312631 : Blo 872567 1312631 := bstep (se 1 (by rfl) ⟨984473, by rfl⟩ : syracuseStep 1312631 = 1968947) B1968947
theorem B1312655 : Blo 872567 1312655 := bstep (se 1 (by rfl) ⟨984491, by rfl⟩ : syracuseStep 1312655 = 1968983) B1968983
theorem B1312697 : Blo 872567 1312697 := bstep (se 2 (by rfl) ⟨492261, by rfl⟩ : syracuseStep 1312697 = 984523) B984523
theorem B1247177 : Blo 872567 1247177 := bstep (se 2 (by rfl) ⟨467691, by rfl⟩ : syracuseStep 1247177 = 935383) B935383
theorem B1312775 : Blo 872567 1312775 := bstep (se 1 (by rfl) ⟨984581, by rfl⟩ : syracuseStep 1312775 = 1969163) B1969163
theorem B1476623 : Blo 872567 1476623 := bstep (se 1 (by rfl) ⟨1107467, by rfl⟩ : syracuseStep 1476623 = 2214935) B2214935
theorem B1312811 : Blo 872567 1312811 := bstep (se 1 (by rfl) ⟨984608, by rfl⟩ : syracuseStep 1312811 = 1969217) B1969217
theorem B1312841 : Blo 872567 1312841 := bstep (se 2 (by rfl) ⟨492315, by rfl⟩ : syracuseStep 1312841 = 984631) B984631
theorem B2099315 : Blo 872567 2099315 := bstep (se 1 (by rfl) ⟨1574486, by rfl⟩ : syracuseStep 2099315 = 3148973) B3148973
theorem B1968263 : Blo 872567 1968263 := bstep (se 1 (by rfl) ⟨1476197, by rfl⟩ : syracuseStep 1968263 = 2952395) B2952395
theorem B1312955 : Blo 872567 1312955 := bstep (se 1 (by rfl) ⟨984716, by rfl⟩ : syracuseStep 1312955 = 1969433) B1969433
theorem B1771721 : Blo 872567 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B2951369 : Blo 872567 2951369 := bstep (se 2 (by rfl) ⟨1106763, by rfl⟩ : syracuseStep 2951369 = 2213527) B2213527
theorem B1313015 : Blo 872567 1313015 := bstep (se 1 (by rfl) ⟨984761, by rfl⟩ : syracuseStep 1313015 = 1969523) B1969523
theorem B985351 : Blo 872567 985351 := bstep (se 1 (by rfl) ⟨739013, by rfl⟩ : syracuseStep 985351 = 1478027) B1478027
theorem B1313039 : Blo 872567 1313039 := bstep (se 1 (by rfl) ⟨984779, by rfl⟩ : syracuseStep 1313039 = 1969559) B1969559
theorem B1313081 : Blo 872567 1313081 := bstep (se 2 (by rfl) ⟨492405, by rfl⟩ : syracuseStep 1313081 = 984811) B984811
theorem B1968443 : Blo 872567 1968443 := bstep (se 1 (by rfl) ⟨1476332, by rfl⟩ : syracuseStep 1968443 = 2952665) B2952665
theorem B1313159 : Blo 872567 1313159 := bstep (se 1 (by rfl) ⟨984869, by rfl⟩ : syracuseStep 1313159 = 1969739) B1969739
theorem B1313195 : Blo 872567 1313195 := bstep (se 1 (by rfl) ⟨984896, by rfl⟩ : syracuseStep 1313195 = 1969793) B1969793
theorem B1968569 : Blo 872567 1968569 := bstep (se 2 (by rfl) ⟨738213, by rfl⟩ : syracuseStep 1968569 = 1476427) B1476427
theorem B985531 : Blo 872567 985531 := bstep (se 1 (by rfl) ⟨739148, by rfl⟩ : syracuseStep 985531 = 1478297) B1478297
theorem B1313225 : Blo 872567 1313225 := bstep (se 2 (by rfl) ⟨492459, by rfl⟩ : syracuseStep 1313225 = 984919) B984919
theorem B1477163 : Blo 872567 1477163 := bstep (se 1 (by rfl) ⟨1107872, by rfl⟩ : syracuseStep 1477163 = 2215745) B2215745
theorem B1313339 : Blo 872567 1313339 := bstep (se 1 (by rfl) ⟨985004, by rfl⟩ : syracuseStep 1313339 = 1970009) B1970009
theorem B1313399 : Blo 872567 1313399 := bstep (se 1 (by rfl) ⟨985049, by rfl⟩ : syracuseStep 1313399 = 1970099) B1970099
theorem B1313423 : Blo 872567 1313423 := bstep (se 1 (by rfl) ⟨985067, by rfl⟩ : syracuseStep 1313423 = 1970135) B1970135
theorem B1313465 : Blo 872567 1313465 := bstep (se 2 (by rfl) ⟨492549, by rfl⟩ : syracuseStep 1313465 = 985099) B985099
theorem B1313543 : Blo 872567 1313543 := bstep (se 1 (by rfl) ⟨985157, by rfl⟩ : syracuseStep 1313543 = 1970315) B1970315
theorem B1968911 : Blo 872567 1968911 := bstep (se 1 (by rfl) ⟨1476683, by rfl⟩ : syracuseStep 1968911 = 2953367) B2953367
theorem B1575713 : Blo 872567 1575713 := bstep (se 2 (by rfl) ⟨590892, by rfl⟩ : syracuseStep 1575713 = 1181785) B1181785
theorem B1968929 : Blo 872567 1968929 := bstep (se 2 (by rfl) ⟨738348, by rfl⟩ : syracuseStep 1968929 = 1476697) B1476697
theorem B1313579 : Blo 872567 1313579 := bstep (se 1 (by rfl) ⟨985184, by rfl⟩ : syracuseStep 1313579 = 1970369) B1970369
theorem B1248043 : Blo 872567 1248043 := bstep (se 1 (by rfl) ⟨936032, by rfl⟩ : syracuseStep 1248043 = 1872065) B1872065
theorem B1313609 : Blo 872567 1313609 := bstep (se 2 (by rfl) ⟨492603, by rfl⟩ : syracuseStep 1313609 = 985207) B985207
theorem B2493271 : Blo 872567 2493271 := bstep (se 1 (by rfl) ⟨1869953, by rfl⟩ : syracuseStep 2493271 = 3739907) B3739907
theorem B2952071 : Blo 872567 2952071 := bstep (se 1 (by rfl) ⟨2214053, by rfl⟩ : syracuseStep 2952071 = 4428107) B4428107
theorem B985999 : Blo 872567 985999 := bstep (se 1 (by rfl) ⟨739499, by rfl⟩ : syracuseStep 985999 = 1478999) B1478999
theorem B4426649 : Blo 872567 4426649 := bstep (se 2 (by rfl) ⟨1659993, by rfl⟩ : syracuseStep 4426649 = 3319987) B3319987
theorem B16845731 : Blo 872567 16845731 := bstep (se 1 (by rfl) ⟨12634298, by rfl⟩ : syracuseStep 16845731 = 25268597) B25268597
theorem B1575865 : Blo 872567 1575865 := bstep (se 2 (by rfl) ⟨590949, by rfl⟩ : syracuseStep 1575865 = 1181899) B1181899
theorem B1477561 : Blo 872567 1477561 := bstep (se 2 (by rfl) ⟨554085, by rfl⟩ : syracuseStep 1477561 = 1108171) B1108171
theorem B1313723 : Blo 872567 1313723 := bstep (se 1 (by rfl) ⟨985292, by rfl⟩ : syracuseStep 1313723 = 1970585) B1970585
theorem B1313783 : Blo 872567 1313783 := bstep (se 1 (by rfl) ⟨985337, by rfl⟩ : syracuseStep 1313783 = 1970675) B1970675
theorem B1313807 : Blo 872567 1313807 := bstep (se 1 (by rfl) ⟨985355, by rfl⟩ : syracuseStep 1313807 = 1970711) B1970711
theorem B8391725 : Blo 872567 8391725 := bstep (se 3 (by rfl) ⟨1573448, by rfl⟩ : syracuseStep 8391725 = 3146897) B3146897
theorem B1313849 : Blo 872567 1313849 := bstep (se 2 (by rfl) ⟨492693, by rfl⟩ : syracuseStep 1313849 = 985387) B985387
theorem B2493499 : Blo 872567 2493499 := bstep (se 1 (by rfl) ⟨1870124, by rfl⟩ : syracuseStep 2493499 = 3740249) B3740249
theorem B1969271 : Blo 872567 1969271 := bstep (se 1 (by rfl) ⟨1476953, by rfl⟩ : syracuseStep 1969271 = 2953907) B2953907
theorem B1313927 : Blo 872567 1313927 := bstep (se 1 (by rfl) ⟨985445, by rfl⟩ : syracuseStep 1313927 = 1970891) B1970891
theorem B1313963 : Blo 872567 1313963 := bstep (se 1 (by rfl) ⟨985472, by rfl⟩ : syracuseStep 1313963 = 1970945) B1970945
theorem B2493625 : Blo 872567 2493625 := bstep (se 2 (by rfl) ⟨935109, by rfl⟩ : syracuseStep 2493625 = 1870219) B1870219
theorem B1313993 : Blo 872567 1313993 := bstep (se 2 (by rfl) ⟨492747, by rfl⟩ : syracuseStep 1313993 = 985495) B985495
theorem B4984037 : Blo 872567 4984037 := bstep (se 4 (by rfl) ⟨467253, by rfl⟩ : syracuseStep 4984037 = 934507) B934507
theorem B2952449 : Blo 872567 2952449 := bstep (se 2 (by rfl) ⟨1107168, by rfl⟩ : syracuseStep 2952449 = 2214337) B2214337
theorem B1969451 : Blo 872567 1969451 := bstep (se 1 (by rfl) ⟨1477088, by rfl⟩ : syracuseStep 1969451 = 2954177) B2954177
theorem B1314107 : Blo 872567 1314107 := bstep (se 1 (by rfl) ⟨985580, by rfl⟩ : syracuseStep 1314107 = 1971161) B1971161
theorem B4263283 : Blo 872567 4263283 := bstep (se 1 (by rfl) ⟨3197462, by rfl⟩ : syracuseStep 4263283 = 6394925) B6394925
theorem B1314167 : Blo 872567 1314167 := bstep (se 1 (by rfl) ⟨985625, by rfl⟩ : syracuseStep 1314167 = 1971251) B1971251
theorem B1314191 : Blo 872567 1314191 := bstep (se 1 (by rfl) ⟨985643, by rfl⟩ : syracuseStep 1314191 = 1971287) B1971287
theorem B1314233 : Blo 872567 1314233 := bstep (se 2 (by rfl) ⟨492837, by rfl⟩ : syracuseStep 1314233 = 985675) B985675
theorem B1314311 : Blo 872567 1314311 := bstep (se 1 (by rfl) ⟨985733, by rfl⟩ : syracuseStep 1314311 = 1971467) B1971467
theorem B2395663 : Blo 872567 2395663 := bstep (se 1 (by rfl) ⟨1796747, by rfl⟩ : syracuseStep 2395663 = 3593495) B3593495
theorem B1314347 : Blo 872567 1314347 := bstep (se 1 (by rfl) ⟨985760, by rfl⟩ : syracuseStep 1314347 = 1971521) B1971521
theorem B1314377 : Blo 872567 1314377 := bstep (se 2 (by rfl) ⟨492891, by rfl⟩ : syracuseStep 1314377 = 985783) B985783
theorem B3739223 : Blo 872567 3739223 := bstep (se 1 (by rfl) ⟨2804417, by rfl⟩ : syracuseStep 3739223 = 5608835) B5608835
theorem B1478263 : Blo 872567 1478263 := bstep (se 1 (by rfl) ⟨1108697, by rfl⟩ : syracuseStep 1478263 = 2217395) B2217395
theorem B1969811 : Blo 872567 1969811 := bstep (se 1 (by rfl) ⟨1477358, by rfl⟩ : syracuseStep 1969811 = 2954717) B2954717
theorem B1314491 : Blo 872567 1314491 := bstep (se 1 (by rfl) ⟨985868, by rfl⟩ : syracuseStep 1314491 = 1971737) B1971737
theorem B1969865 : Blo 872567 1969865 := bstep (se 2 (by rfl) ⟨738699, by rfl⟩ : syracuseStep 1969865 = 1477399) B1477399
theorem B1314551 : Blo 872567 1314551 := bstep (se 1 (by rfl) ⟨985913, by rfl⟩ : syracuseStep 1314551 = 1971827) B1971827
theorem B2101007 : Blo 872567 2101007 := bstep (se 1 (by rfl) ⟨1575755, by rfl⟩ : syracuseStep 2101007 = 3151511) B3151511
theorem B1314575 : Blo 872567 1314575 := bstep (se 1 (by rfl) ⟨985931, by rfl⟩ : syracuseStep 1314575 = 1971863) B1971863
theorem B1314617 : Blo 872567 1314617 := bstep (se 2 (by rfl) ⟨492981, by rfl⟩ : syracuseStep 1314617 = 985963) B985963
theorem B1478459 : Blo 872567 1478459 := bstep (se 1 (by rfl) ⟨1108844, by rfl⟩ : syracuseStep 1478459 = 2217689) B2217689
theorem B1052551 : Blo 872567 1052551 := bstep (se 1 (by rfl) ⟨789413, by rfl⟩ : syracuseStep 1052551 = 1578827) B1578827
theorem B1314695 : Blo 872567 1314695 := bstep (se 1 (by rfl) ⟨986021, by rfl⟩ : syracuseStep 1314695 = 1972043) B1972043
theorem B1314731 : Blo 872567 1314731 := bstep (se 1 (by rfl) ⟨986048, by rfl⟩ : syracuseStep 1314731 = 1972097) B1972097
theorem B1314761 : Blo 872567 1314761 := bstep (se 2 (by rfl) ⟨493035, by rfl⟩ : syracuseStep 1314761 = 986071) B986071
theorem B2953259 : Blo 872567 2953259 := bstep (se 1 (by rfl) ⟨2214944, by rfl⟩ : syracuseStep 2953259 = 4429889) B4429889
theorem B6295639 : Blo 872567 6295639 := bstep (se 1 (by rfl) ⟨4721729, by rfl⟩ : syracuseStep 6295639 = 9443459) B9443459
theorem B1478857 : Blo 872567 1478857 := bstep (se 2 (by rfl) ⟨554571, by rfl⟩ : syracuseStep 1478857 = 1109143) B1109143
theorem B2658589 : Blo 872567 2658589 := bstep (se 3 (by rfl) ⟨498485, by rfl⟩ : syracuseStep 2658589 = 996971) B996971
theorem B1577249 : Blo 872567 1577249 := bstep (se 2 (by rfl) ⟨591468, by rfl⟩ : syracuseStep 1577249 = 1182937) B1182937
theorem B1970567 : Blo 872567 1970567 := bstep (se 1 (by rfl) ⟨1477925, by rfl⟩ : syracuseStep 1970567 = 2955851) B2955851
theorem B1970747 : Blo 872567 1970747 := bstep (se 1 (by rfl) ⟨1478060, by rfl⟩ : syracuseStep 1970747 = 2956121) B2956121
theorem B4198979 : Blo 872567 4198979 := bstep (se 1 (by rfl) ⟨3149234, by rfl⟩ : syracuseStep 4198979 = 6298469) B6298469
theorem B1970873 : Blo 872567 1970873 := bstep (se 2 (by rfl) ⟨739077, by rfl⟩ : syracuseStep 1970873 = 1478155) B1478155
theorem B10523429 : Blo 872567 10523429 := bstep (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) B1973143
theorem B3314641 : Blo 872567 3314641 := bstep (se 2 (by rfl) ⟨1242990, by rfl⟩ : syracuseStep 3314641 = 2485981) B2485981
theorem B1971215 : Blo 872567 1971215 := bstep (se 1 (by rfl) ⟨1478411, by rfl⟩ : syracuseStep 1971215 = 2956823) B2956823
theorem B1971233 : Blo 872567 1971233 := bstep (se 2 (by rfl) ⟨739212, by rfl⟩ : syracuseStep 1971233 = 1478425) B1478425
theorem B2495549 : Blo 872567 2495549 := bstep (se 3 (by rfl) ⟨467915, by rfl⟩ : syracuseStep 2495549 = 935831) B935831
theorem B272667779 : Blo 872567 272667779 := bstep (se 1 (by rfl) ⟨204500834, by rfl⟩ : syracuseStep 272667779 = 409001669) B409001669
theorem B3314945 : Blo 872567 3314945 := bstep (se 2 (by rfl) ⟨1243104, by rfl⟩ : syracuseStep 3314945 = 2486209) B2486209
theorem B2954555 : Blo 872567 2954555 := bstep (se 1 (by rfl) ⟨2215916, by rfl⟩ : syracuseStep 2954555 = 4431833) B4431833
theorem B1971575 : Blo 872567 1971575 := bstep (se 1 (by rfl) ⟨1478681, by rfl⟩ : syracuseStep 1971575 = 2957363) B2957363
theorem B4724153 : Blo 872567 4724153 := bstep (se 2 (by rfl) ⟨1771557, by rfl⟩ : syracuseStep 4724153 = 3543115) B3543115
theorem B4429241 : Blo 872567 4429241 := bstep (se 2 (by rfl) ⟨1660965, by rfl⟩ : syracuseStep 4429241 = 3321931) B3321931
theorem B3741137 : Blo 872567 3741137 := bstep (se 2 (by rfl) ⟨1402926, by rfl⟩ : syracuseStep 3741137 = 2805853) B2805853
theorem B22451741 : Blo 872567 22451741 := bstep (se 3 (by rfl) ⟨4209701, by rfl⟩ : syracuseStep 22451741 = 8419403) B8419403
theorem B1971755 : Blo 872567 1971755 := bstep (se 1 (by rfl) ⟨1478816, by rfl⟩ : syracuseStep 1971755 = 2957633) B2957633
theorem B3315401 : Blo 872567 3315401 := bstep (se 2 (by rfl) ⟨1243275, by rfl⟩ : syracuseStep 3315401 = 2486551) B2486551
theorem B2955041 : Blo 872567 2955041 := bstep (se 2 (by rfl) ⟨1108140, by rfl⟩ : syracuseStep 2955041 = 2216281) B2216281
theorem B1972115 : Blo 872567 1972115 := bstep (se 1 (by rfl) ⟨1479086, by rfl⟩ : syracuseStep 1972115 = 2958173) B2958173
theorem B14161817 : Blo 872567 14161817 := bstep (se 2 (by rfl) ⟨5310681, by rfl⟩ : syracuseStep 14161817 = 10621363) B10621363
theorem B1972169 : Blo 872567 1972169 := bstep (se 2 (by rfl) ⟨739563, by rfl⟩ : syracuseStep 1972169 = 1479127) B1479127
theorem B21305389 : Blo 872567 21305389 := bstep (se 3 (by rfl) ⟨3994760, by rfl⟩ : syracuseStep 21305389 = 7989521) B7989521
theorem B2955635 : Blo 872567 2955635 := bstep (se 1 (by rfl) ⟨2216726, by rfl⟩ : syracuseStep 2955635 = 4433453) B4433453
theorem B4987271 : Blo 872567 4987271 := bstep (se 1 (by rfl) ⟨3740453, by rfl⟩ : syracuseStep 4987271 = 7480907) B7480907
theorem B4987453 : Blo 872567 4987453 := bstep (se 3 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 4987453 = 1870295) B1870295
theorem B9476675 : Blo 872567 9476675 := bstep (se 1 (by rfl) ⟨7107506, by rfl⟩ : syracuseStep 9476675 = 14215013) B14215013
theorem B4430537 : Blo 872567 4430537 := bstep (se 2 (by rfl) ⟨1661451, by rfl⟩ : syracuseStep 4430537 = 3322903) B3322903
theorem B9968345 : Blo 872567 9968345 := bstep (se 2 (by rfl) ⟨3738129, by rfl⟩ : syracuseStep 9968345 = 7476259) B7476259
theorem B40410019 : Blo 872567 40410019 := bstep (se 1 (by rfl) ⟨30307514, by rfl⟩ : syracuseStep 40410019 = 60615029) B60615029
theorem B17538053 : Blo 872567 17538053 := bstep (se 4 (by rfl) ⟨1644192, by rfl⟩ : syracuseStep 17538053 = 3288385) B3288385
theorem B2104967 : Blo 872567 2104967 := bstep (se 1 (by rfl) ⟨1578725, by rfl⟩ : syracuseStep 2104967 = 3157451) B3157451
theorem B2105459 : Blo 872567 2105459 := bstep (se 1 (by rfl) ⟨1579094, by rfl⟩ : syracuseStep 2105459 = 3158189) B3158189
theorem B4989185 : Blo 872567 4989185 := bstep (se 2 (by rfl) ⟨1870944, by rfl⟩ : syracuseStep 4989185 = 3741889) B3741889
theorem B3842513 : Blo 872567 3842513 := bstep (se 2 (by rfl) ⟨1440942, by rfl⟩ : syracuseStep 3842513 = 2881885) B2881885
theorem B3318529 : Blo 872567 3318529 := bstep (se 2 (by rfl) ⟨1244448, by rfl⟩ : syracuseStep 3318529 = 2488897) B2488897
theorem B4203323 : Blo 872567 4203323 := bstep (se 1 (by rfl) ⟨3152492, by rfl⟩ : syracuseStep 4203323 = 6304985) B6304985
theorem B2958227 : Blo 872567 2958227 := bstep (se 1 (by rfl) ⟨2218670, by rfl⟩ : syracuseStep 2958227 = 4437341) B4437341
theorem B6628553 : Blo 872567 6628553 := bstep (se 2 (by rfl) ⟨2485707, by rfl⟩ : syracuseStep 6628553 = 4971415) B4971415
theorem B3155201 : Blo 872567 3155201 := bstep (se 2 (by rfl) ⟨1183200, by rfl⟩ : syracuseStep 3155201 = 2366401) B2366401
theorem B2369083 : Blo 872567 2369083 := bstep (se 1 (by rfl) ⟨1776812, by rfl⟩ : syracuseStep 2369083 = 3553625) B3553625
theorem B42510359 : Blo 872567 42510359 := bstep (se 1 (by rfl) ⟨31882769, by rfl⟩ : syracuseStep 42510359 = 63765539) B63765539
theorem B3778589 : Blo 872567 3778589 := bstep (se 3 (by rfl) ⟨708485, by rfl⟩ : syracuseStep 3778589 = 1416971) B1416971
theorem B18917549 : Blo 872567 18917549 := bstep (se 3 (by rfl) ⟨3547040, by rfl⟩ : syracuseStep 18917549 = 7094081) B7094081
theorem B26978935 : Blo 872567 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B14560181 : Blo 872567 14560181 := bstep (se 5 (by rfl) ⟨682508, by rfl⟩ : syracuseStep 14560181 = 1365017) B1365017
theorem B4205533 : Blo 872567 4205533 := bstep (se 3 (by rfl) ⟨788537, by rfl⟩ : syracuseStep 4205533 = 1577075) B1577075
theorem B4205591 : Blo 872567 4205591 := bstep (se 1 (by rfl) ⟨3154193, by rfl⟩ : syracuseStep 4205591 = 6308387) B6308387
theorem B15969413 : Blo 872567 15969413 := bstep (se 4 (by rfl) ⟨1497132, by rfl⟩ : syracuseStep 15969413 = 2994265) B2994265
theorem B5320025 : Blo 872567 5320025 := bstep (se 2 (by rfl) ⟨1995009, by rfl⟩ : syracuseStep 5320025 = 3990019) B3990019
theorem B16166279 : Blo 872567 16166279 := bstep (se 1 (by rfl) ⟨12124709, by rfl⟩ : syracuseStep 16166279 = 24249419) B24249419
theorem B3321431 : Blo 872567 3321431 := bstep (se 1 (by rfl) ⟨2491073, by rfl⟩ : syracuseStep 3321431 = 4982147) B4982147
theorem B4206167 : Blo 872567 4206167 := bstep (se 1 (by rfl) ⟨3154625, by rfl⟩ : syracuseStep 4206167 = 6309251) B6309251
theorem B22425497 : Blo 872567 22425497 := bstep (se 2 (by rfl) ⟨8409561, by rfl⟩ : syracuseStep 22425497 = 16819123) B16819123
theorem B3157969 : Blo 872567 3157969 := bstep (se 2 (by rfl) ⟨1184238, by rfl⟩ : syracuseStep 3157969 = 2368477) B2368477
theorem B26980397 : Blo 872567 26980397 := bstep (se 3 (by rfl) ⟨5058824, by rfl⟩ : syracuseStep 26980397 = 10117649) B10117649
theorem B3321917 : Blo 872567 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B4436369 : Blo 872567 4436369 := bstep (se 2 (by rfl) ⟨1663638, by rfl⟩ : syracuseStep 4436369 = 3327277) B3327277
theorem B995771 : Blo 872567 995771 := bstep (se 1 (by rfl) ⟨746828, by rfl⟩ : syracuseStep 995771 = 1493657) B1493657
theorem B4731763 : Blo 872567 4731763 := bstep (se 1 (by rfl) ⟨3548822, by rfl⟩ : syracuseStep 4731763 = 7097645) B7097645
theorem B2208779 : Blo 872567 2208779 := bstep (se 1 (by rfl) ⟨1656584, by rfl⟩ : syracuseStep 2208779 = 3313169) B3313169
theorem B20428163 : Blo 872567 20428163 := bstep (se 1 (by rfl) ⟨15321122, by rfl⟩ : syracuseStep 20428163 = 30642245) B30642245
theorem B2209295 : Blo 872567 2209295 := bstep (se 1 (by rfl) ⟨1656971, by rfl⟩ : syracuseStep 2209295 = 3313943) B3313943
theorem B9090625 : Blo 872567 9090625 := bstep (se 2 (by rfl) ⟨3408984, by rfl⟩ : syracuseStep 9090625 = 6817969) B6817969
theorem B2209427 : Blo 872567 2209427 := bstep (se 1 (by rfl) ⟨1657070, by rfl⟩ : syracuseStep 2209427 = 3314141) B3314141
theorem B3323663 : Blo 872567 3323663 := bstep (se 1 (by rfl) ⟨2492747, by rfl⟩ : syracuseStep 3323663 = 4985495) B4985495
theorem B8075123 : Blo 872567 8075123 := bstep (se 1 (by rfl) ⟨6056342, by rfl⟩ : syracuseStep 8075123 = 12112685) B12112685
theorem B9451417 : Blo 872567 9451417 := bstep (se 2 (by rfl) ⟨3544281, by rfl⟩ : syracuseStep 9451417 = 7088563) B7088563
theorem B997519 : Blo 872567 997519 := bstep (se 1 (by rfl) ⟨748139, by rfl⟩ : syracuseStep 997519 = 1496279) B1496279
theorem B932239 : Blo 872567 932239 := bstep (se 1 (by rfl) ⟨699179, by rfl⟩ : syracuseStep 932239 = 1398359) B1398359
theorem B6732179 : Blo 872567 6732179 := bstep (se 1 (by rfl) ⟨5049134, by rfl⟩ : syracuseStep 6732179 = 10098269) B10098269
theorem B2210561 : Blo 872567 2210561 := bstep (se 2 (by rfl) ⟨828960, by rfl⟩ : syracuseStep 2210561 = 1657921) B1657921
theorem B4733711 : Blo 872567 4733711 := bstep (se 1 (by rfl) ⟨3550283, by rfl⟩ : syracuseStep 4733711 = 7100567) B7100567
theorem B2800651 : Blo 872567 2800651 := bstep (se 1 (by rfl) ⟨2100488, by rfl⟩ : syracuseStep 2800651 = 4200977) B4200977
theorem B2210935 : Blo 872567 2210935 := bstep (se 1 (by rfl) ⟨1658201, by rfl⟩ : syracuseStep 2210935 = 3316403) B3316403
theorem B4209857 : Blo 872567 4209857 := bstep (se 2 (by rfl) ⟨1578696, by rfl⟩ : syracuseStep 4209857 = 3157393) B3157393
theorem B2243855 : Blo 872567 2243855 := bstep (se 1 (by rfl) ⟨1682891, by rfl⟩ : syracuseStep 2243855 = 3365783) B3365783
theorem B3325319 : Blo 872567 3325319 := bstep (se 1 (by rfl) ⟨2493989, by rfl⟩ : syracuseStep 3325319 = 4987979) B4987979
theorem B2211371 : Blo 872567 2211371 := bstep (se 1 (by rfl) ⟨1658528, by rfl⟩ : syracuseStep 2211371 = 3317057) B3317057
theorem B8077219 : Blo 872567 8077219 := bstep (se 1 (by rfl) ⟨6057914, by rfl⟩ : syracuseStep 8077219 = 12115829) B12115829
theorem B1916873 : Blo 872567 1916873 := bstep (se 2 (by rfl) ⟨718827, by rfl⟩ : syracuseStep 1916873 = 1437655) B1437655
theorem B2212211 : Blo 872567 2212211 := bstep (se 1 (by rfl) ⟨1659158, by rfl⟩ : syracuseStep 2212211 = 3318317) B3318317
theorem B2212231 : Blo 872567 2212231 := bstep (se 1 (by rfl) ⟨1659173, by rfl⟩ : syracuseStep 2212231 = 3318347) B3318347
theorem B2212505 : Blo 872567 2212505 := bstep (se 2 (by rfl) ⟨829689, by rfl⟩ : syracuseStep 2212505 = 1659379) B1659379
theorem B4735745 : Blo 872567 4735745 := bstep (se 2 (by rfl) ⟨1775904, by rfl⟩ : syracuseStep 4735745 = 3551809) B3551809
theorem B5391137 : Blo 872567 5391137 := bstep (se 2 (by rfl) ⟨2021676, by rfl⟩ : syracuseStep 5391137 = 4043353) B4043353
theorem B2212667 : Blo 872567 2212667 := bstep (se 1 (by rfl) ⟨1659500, by rfl⟩ : syracuseStep 2212667 = 3319001) B3319001
theorem B2212879 : Blo 872567 2212879 := bstep (se 1 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 2212879 = 3319319) B3319319
theorem B3327095 : Blo 872567 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B2213153 : Blo 872567 2213153 := bstep (se 2 (by rfl) ⟨829932, by rfl⟩ : syracuseStep 2213153 = 1659865) B1659865
theorem B1263161 : Blo 872567 1263161 := bstep (se 2 (by rfl) ⟨473685, by rfl⟩ : syracuseStep 1263161 = 947371) B947371
theorem B1656865 : Blo 872567 1656865 := bstep (se 2 (by rfl) ⟨621324, by rfl⟩ : syracuseStep 1656865 = 1242649) B1242649
theorem B3328067 : Blo 872567 3328067 := bstep (se 1 (by rfl) ⟨2496050, by rfl⟩ : syracuseStep 3328067 = 4992101) B4992101
theorem B2214155 : Blo 872567 2214155 := bstep (se 1 (by rfl) ⟨1660616, by rfl⟩ : syracuseStep 2214155 = 3321233) B3321233
theorem B1198379 : Blo 872567 1198379 := bstep (se 1 (by rfl) ⟨898784, by rfl⟩ : syracuseStep 1198379 = 1797569) B1797569
theorem B6638273 : Blo 872567 6638273 := bstep (se 2 (by rfl) ⟨2489352, by rfl⟩ : syracuseStep 6638273 = 4978705) B4978705
theorem B2214803 : Blo 872567 2214803 := bstep (se 1 (by rfl) ⟨1661102, by rfl⟩ : syracuseStep 2214803 = 3322205) B3322205
theorem B2215097 : Blo 872567 2215097 := bstep (se 2 (by rfl) ⟨830661, by rfl⟩ : syracuseStep 2215097 = 1661323) B1661323
theorem B1658171 : Blo 872567 1658171 := bstep (se 1 (by rfl) ⟨1243628, by rfl⟩ : syracuseStep 1658171 = 2487257) B2487257
theorem B2248121 : Blo 872567 2248121 := bstep (se 2 (by rfl) ⟨843045, by rfl⟩ : syracuseStep 2248121 = 1686091) B1686091
theorem B3198475 : Blo 872567 3198475 := bstep (se 1 (by rfl) ⟨2398856, by rfl⟩ : syracuseStep 3198475 = 4797713) B4797713
theorem B3984983 : Blo 872567 3984983 := bstep (se 1 (by rfl) ⟨2988737, by rfl⟩ : syracuseStep 3984983 = 5977475) B5977475
theorem B2805367 : Blo 872567 2805367 := bstep (se 1 (by rfl) ⟨2104025, by rfl⟩ : syracuseStep 2805367 = 4208051) B4208051
theorem B1658657 : Blo 872567 1658657 := bstep (se 2 (by rfl) ⟨621996, by rfl⟩ : syracuseStep 1658657 = 1243993) B1243993
theorem B8408947 : Blo 872567 8408947 := bstep (se 1 (by rfl) ⟨6306710, by rfl⟩ : syracuseStep 8408947 = 12613421) B12613421
theorem B2215795 : Blo 872567 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B1658809 : Blo 872567 1658809 := bstep (se 2 (by rfl) ⟨622053, by rfl⟩ : syracuseStep 1658809 = 1244107) B1244107
theorem B7458763 : Blo 872567 7458763 := bstep (se 1 (by rfl) ⟨5594072, by rfl⟩ : syracuseStep 7458763 = 11188145) B11188145
theorem B2215937 : Blo 872567 2215937 := bstep (se 2 (by rfl) ⟨830976, by rfl⟩ : syracuseStep 2215937 = 1661953) B1661953
theorem B5591051 : Blo 872567 5591051 := bstep (se 1 (by rfl) ⟨4193288, by rfl⟩ : syracuseStep 5591051 = 8386577) B8386577
theorem B2805803 : Blo 872567 2805803 := bstep (se 1 (by rfl) ⟨2104352, by rfl⟩ : syracuseStep 2805803 = 4208705) B4208705
theorem B872583 : Blo 872567 872583 := bstep (se 1 (by rfl) ⟨654437, by rfl⟩ : syracuseStep 872583 = 1308875) B1308875
theorem B872591 : Blo 872567 872591 := bstep (se 1 (by rfl) ⟨654443, by rfl⟩ : syracuseStep 872591 = 1308887) B1308887
theorem B872635 : Blo 872567 872635 := bstep (se 1 (by rfl) ⟨654476, by rfl⟩ : syracuseStep 872635 = 1308953) B1308953
theorem B872711 : Blo 872567 872711 := bstep (se 1 (by rfl) ⟨654533, by rfl⟩ : syracuseStep 872711 = 1309067) B1309067
theorem B872719 : Blo 872567 872719 := bstep (se 1 (by rfl) ⟨654539, by rfl⟩ : syracuseStep 872719 = 1309079) B1309079
theorem B872763 : Blo 872567 872763 := bstep (se 1 (by rfl) ⟨654572, by rfl⟩ : syracuseStep 872763 = 1309145) B1309145
theorem B872839 : Blo 872567 872839 := bstep (se 1 (by rfl) ⟨654629, by rfl⟩ : syracuseStep 872839 = 1309259) B1309259
theorem B872847 : Blo 872567 872847 := bstep (se 1 (by rfl) ⟨654635, by rfl⟩ : syracuseStep 872847 = 1309271) B1309271
theorem B872891 : Blo 872567 872891 := bstep (se 1 (by rfl) ⟨654668, by rfl⟩ : syracuseStep 872891 = 1309337) B1309337
theorem B2216393 : Blo 872567 2216393 := bstep (se 2 (by rfl) ⟨831147, by rfl⟩ : syracuseStep 2216393 = 1662295) B1662295
theorem B12800477 : Blo 872567 12800477 := bstep (se 3 (by rfl) ⟨2400089, by rfl⟩ : syracuseStep 12800477 = 4800179) B4800179
theorem B872967 : Blo 872567 872967 := bstep (se 1 (by rfl) ⟨654725, by rfl⟩ : syracuseStep 872967 = 1309451) B1309451
theorem B872975 : Blo 872567 872975 := bstep (se 1 (by rfl) ⟨654731, by rfl⟩ : syracuseStep 872975 = 1309463) B1309463
theorem B873019 : Blo 872567 873019 := bstep (se 1 (by rfl) ⟨654764, by rfl⟩ : syracuseStep 873019 = 1309529) B1309529
theorem B1331831 : Blo 872567 1331831 := bstep (se 1 (by rfl) ⟨998873, by rfl⟩ : syracuseStep 1331831 = 1997747) B1997747
theorem B873095 : Blo 872567 873095 := bstep (se 1 (by rfl) ⟨654821, by rfl⟩ : syracuseStep 873095 = 1309643) B1309643
theorem B873103 : Blo 872567 873103 := bstep (se 1 (by rfl) ⟨654827, by rfl⟩ : syracuseStep 873103 = 1309655) B1309655
theorem B873147 : Blo 872567 873147 := bstep (se 1 (by rfl) ⟨654860, by rfl⟩ : syracuseStep 873147 = 1309721) B1309721
theorem B3363565 : Blo 872567 3363565 := bstep (se 3 (by rfl) ⟨630668, by rfl⟩ : syracuseStep 3363565 = 1261337) B1261337
theorem B873223 : Blo 872567 873223 := bstep (se 1 (by rfl) ⟨654917, by rfl⟩ : syracuseStep 873223 = 1309835) B1309835
theorem B873231 : Blo 872567 873231 := bstep (se 1 (by rfl) ⟨654923, by rfl⟩ : syracuseStep 873231 = 1309847) B1309847
theorem B2216747 : Blo 872567 2216747 := bstep (se 1 (by rfl) ⟨1662560, by rfl⟩ : syracuseStep 2216747 = 3325121) B3325121
theorem B873275 : Blo 872567 873275 := bstep (se 1 (by rfl) ⟨654956, by rfl⟩ : syracuseStep 873275 = 1309913) B1309913
theorem B873351 : Blo 872567 873351 := bstep (se 1 (by rfl) ⟨655013, by rfl⟩ : syracuseStep 873351 = 1310027) B1310027
theorem B873359 : Blo 872567 873359 := bstep (se 1 (by rfl) ⟨655019, by rfl⟩ : syracuseStep 873359 = 1310039) B1310039
theorem B873403 : Blo 872567 873403 := bstep (se 1 (by rfl) ⟨655052, by rfl⟩ : syracuseStep 873403 = 1310105) B1310105
theorem B1332215 : Blo 872567 1332215 := bstep (se 1 (by rfl) ⟨999161, by rfl⟩ : syracuseStep 1332215 = 1998323) B1998323
theorem B873479 : Blo 872567 873479 := bstep (se 1 (by rfl) ⟨655109, by rfl⟩ : syracuseStep 873479 = 1310219) B1310219
theorem B873487 : Blo 872567 873487 := bstep (se 1 (by rfl) ⟨655115, by rfl⟩ : syracuseStep 873487 = 1310231) B1310231
theorem B873531 : Blo 872567 873531 := bstep (se 1 (by rfl) ⟨655148, by rfl⟩ : syracuseStep 873531 = 1310297) B1310297
theorem B873607 : Blo 872567 873607 := bstep (se 1 (by rfl) ⟨655205, by rfl⟩ : syracuseStep 873607 = 1310411) B1310411
theorem B873615 : Blo 872567 873615 := bstep (se 1 (by rfl) ⟨655211, by rfl⟩ : syracuseStep 873615 = 1310423) B1310423
theorem B1332409 : Blo 872567 1332409 := bstep (se 2 (by rfl) ⟨499653, by rfl⟩ : syracuseStep 1332409 = 999307) B999307
theorem B873659 : Blo 872567 873659 := bstep (se 1 (by rfl) ⟨655244, by rfl⟩ : syracuseStep 873659 = 1310489) B1310489
theorem B873735 : Blo 872567 873735 := bstep (se 1 (by rfl) ⟨655301, by rfl⟩ : syracuseStep 873735 = 1310603) B1310603
theorem B873743 : Blo 872567 873743 := bstep (se 1 (by rfl) ⟨655307, by rfl⟩ : syracuseStep 873743 = 1310615) B1310615
theorem B873787 : Blo 872567 873787 := bstep (se 1 (by rfl) ⟨655340, by rfl⟩ : syracuseStep 873787 = 1310681) B1310681
theorem B873863 : Blo 872567 873863 := bstep (se 1 (by rfl) ⟨655397, by rfl⟩ : syracuseStep 873863 = 1310795) B1310795
theorem B76567949 : Blo 872567 76567949 := bstep (se 3 (by rfl) ⟨14356490, by rfl⟩ : syracuseStep 76567949 = 28712981) B28712981
theorem B873871 : Blo 872567 873871 := bstep (se 1 (by rfl) ⟨655403, by rfl⟩ : syracuseStep 873871 = 1310807) B1310807
theorem B873915 : Blo 872567 873915 := bstep (se 1 (by rfl) ⟨655436, by rfl⟩ : syracuseStep 873915 = 1310873) B1310873
theorem B873991 : Blo 872567 873991 := bstep (se 1 (by rfl) ⟨655493, by rfl⟩ : syracuseStep 873991 = 1310987) B1310987
theorem B873999 : Blo 872567 873999 := bstep (se 1 (by rfl) ⟨655499, by rfl⟩ : syracuseStep 873999 = 1310999) B1310999
theorem B874043 : Blo 872567 874043 := bstep (se 1 (by rfl) ⟨655532, by rfl⟩ : syracuseStep 874043 = 1311065) B1311065
theorem B874119 : Blo 872567 874119 := bstep (se 1 (by rfl) ⟨655589, by rfl⟩ : syracuseStep 874119 = 1311179) B1311179
theorem B874127 : Blo 872567 874127 := bstep (se 1 (by rfl) ⟨655595, by rfl⟩ : syracuseStep 874127 = 1311191) B1311191
theorem B1660601 : Blo 872567 1660601 := bstep (se 2 (by rfl) ⟨622725, by rfl⟩ : syracuseStep 1660601 = 1245451) B1245451
theorem B874171 : Blo 872567 874171 := bstep (se 1 (by rfl) ⟨655628, by rfl⟩ : syracuseStep 874171 = 1311257) B1311257
theorem B874247 : Blo 872567 874247 := bstep (se 1 (by rfl) ⟨655685, by rfl⟩ : syracuseStep 874247 = 1311371) B1311371
theorem B2217739 : Blo 872567 2217739 := bstep (se 1 (by rfl) ⟨1663304, by rfl⟩ : syracuseStep 2217739 = 3326609) B3326609
theorem B874255 : Blo 872567 874255 := bstep (se 1 (by rfl) ⟨655691, by rfl⟩ : syracuseStep 874255 = 1311383) B1311383
theorem B2807585 : Blo 872567 2807585 := bstep (se 2 (by rfl) ⟨1052844, by rfl⟩ : syracuseStep 2807585 = 2105689) B2105689
theorem B874299 : Blo 872567 874299 := bstep (se 1 (by rfl) ⟨655724, by rfl⟩ : syracuseStep 874299 = 1311449) B1311449
theorem B1398647 : Blo 872567 1398647 := bstep (se 1 (by rfl) ⟨1048985, by rfl⟩ : syracuseStep 1398647 = 2097971) B2097971
theorem B874375 : Blo 872567 874375 := bstep (se 1 (by rfl) ⟨655781, by rfl⟩ : syracuseStep 874375 = 1311563) B1311563
theorem B874383 : Blo 872567 874383 := bstep (se 1 (by rfl) ⟨655787, by rfl⟩ : syracuseStep 874383 = 1311575) B1311575
theorem B2217881 : Blo 872567 2217881 := bstep (se 2 (by rfl) ⟨831705, by rfl⟩ : syracuseStep 2217881 = 1663411) B1663411
theorem B874427 : Blo 872567 874427 := bstep (se 1 (by rfl) ⟨655820, by rfl⟩ : syracuseStep 874427 = 1311641) B1311641
theorem B874503 : Blo 872567 874503 := bstep (se 1 (by rfl) ⟨655877, by rfl⟩ : syracuseStep 874503 = 1311755) B1311755
theorem B6641675 : Blo 872567 6641675 := bstep (se 1 (by rfl) ⟨4981256, by rfl⟩ : syracuseStep 6641675 = 9962513) B9962513
theorem B874511 : Blo 872567 874511 := bstep (se 1 (by rfl) ⟨655883, by rfl⟩ : syracuseStep 874511 = 1311767) B1311767
theorem B874555 : Blo 872567 874555 := bstep (se 1 (by rfl) ⟨655916, by rfl⟩ : syracuseStep 874555 = 1311833) B1311833
theorem B2218043 : Blo 872567 2218043 := bstep (se 1 (by rfl) ⟨1663532, by rfl⟩ : syracuseStep 2218043 = 3327065) B3327065
theorem B874631 : Blo 872567 874631 := bstep (se 1 (by rfl) ⟨655973, by rfl⟩ : syracuseStep 874631 = 1311947) B1311947
theorem B874639 : Blo 872567 874639 := bstep (se 1 (by rfl) ⟨655979, by rfl⟩ : syracuseStep 874639 = 1311959) B1311959
theorem B874683 : Blo 872567 874683 := bstep (se 1 (by rfl) ⟨656012, by rfl⟩ : syracuseStep 874683 = 1312025) B1312025
theorem B874759 : Blo 872567 874759 := bstep (se 1 (by rfl) ⟨656069, by rfl⟩ : syracuseStep 874759 = 1312139) B1312139
theorem B874767 : Blo 872567 874767 := bstep (se 1 (by rfl) ⟨656075, by rfl⟩ : syracuseStep 874767 = 1312151) B1312151
theorem B874811 : Blo 872567 874811 := bstep (se 1 (by rfl) ⟨656108, by rfl⟩ : syracuseStep 874811 = 1312217) B1312217
theorem B874887 : Blo 872567 874887 := bstep (se 1 (by rfl) ⟨656165, by rfl⟩ : syracuseStep 874887 = 1312331) B1312331
theorem B874895 : Blo 872567 874895 := bstep (se 1 (by rfl) ⟨656171, by rfl⟩ : syracuseStep 874895 = 1312343) B1312343
theorem B18897299 : Blo 872567 18897299 := bstep (se 1 (by rfl) ⟨14172974, by rfl⟩ : syracuseStep 18897299 = 28345949) B28345949
theorem B2218387 : Blo 872567 2218387 := bstep (se 1 (by rfl) ⟨1663790, by rfl⟩ : syracuseStep 2218387 = 3327581) B3327581
theorem B874939 : Blo 872567 874939 := bstep (se 1 (by rfl) ⟨656204, by rfl⟩ : syracuseStep 874939 = 1312409) B1312409
theorem B1497545 : Blo 872567 1497545 := bstep (se 2 (by rfl) ⟨561579, by rfl⟩ : syracuseStep 1497545 = 1123159) B1123159
theorem B5986781 : Blo 872567 5986781 := bstep (se 3 (by rfl) ⟨1122521, by rfl⟩ : syracuseStep 5986781 = 2245043) B2245043
theorem B875015 : Blo 872567 875015 := bstep (se 1 (by rfl) ⟨656261, by rfl⟩ : syracuseStep 875015 = 1312523) B1312523
theorem B875023 : Blo 872567 875023 := bstep (se 1 (by rfl) ⟨656267, by rfl⟩ : syracuseStep 875023 = 1312535) B1312535
theorem B2218529 : Blo 872567 2218529 := bstep (se 2 (by rfl) ⟨831948, by rfl⟩ : syracuseStep 2218529 = 1663897) B1663897
theorem B875067 : Blo 872567 875067 := bstep (se 1 (by rfl) ⟨656300, by rfl⟩ : syracuseStep 875067 = 1312601) B1312601
theorem B875143 : Blo 872567 875143 := bstep (se 1 (by rfl) ⟨656357, by rfl⟩ : syracuseStep 875143 = 1312715) B1312715
theorem B875151 : Blo 872567 875151 := bstep (se 1 (by rfl) ⟨656363, by rfl⟩ : syracuseStep 875151 = 1312727) B1312727
theorem B875195 : Blo 872567 875195 := bstep (se 1 (by rfl) ⟨656396, by rfl⟩ : syracuseStep 875195 = 1312793) B1312793
theorem B875271 : Blo 872567 875271 := bstep (se 1 (by rfl) ⟨656453, by rfl⟩ : syracuseStep 875271 = 1312907) B1312907
theorem B875279 : Blo 872567 875279 := bstep (se 1 (by rfl) ⟨656459, by rfl⟩ : syracuseStep 875279 = 1312919) B1312919
theorem B875323 : Blo 872567 875323 := bstep (se 1 (by rfl) ⟨656492, by rfl⟩ : syracuseStep 875323 = 1312985) B1312985
theorem B875399 : Blo 872567 875399 := bstep (se 1 (by rfl) ⟨656549, by rfl⟩ : syracuseStep 875399 = 1313099) B1313099
theorem B875407 : Blo 872567 875407 := bstep (se 1 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 875407 = 1313111) B1313111
theorem B875451 : Blo 872567 875451 := bstep (se 1 (by rfl) ⟨656588, by rfl⟩ : syracuseStep 875451 = 1313177) B1313177
theorem B875527 : Blo 872567 875527 := bstep (se 1 (by rfl) ⟨656645, by rfl⟩ : syracuseStep 875527 = 1313291) B1313291
theorem B875535 : Blo 872567 875535 := bstep (se 1 (by rfl) ⟨656651, by rfl⟩ : syracuseStep 875535 = 1313303) B1313303
theorem B875579 : Blo 872567 875579 := bstep (se 1 (by rfl) ⟨656684, by rfl⟩ : syracuseStep 875579 = 1313369) B1313369
theorem B5397623 : Blo 872567 5397623 := bstep (se 1 (by rfl) ⟨4048217, by rfl⟩ : syracuseStep 5397623 = 8096435) B8096435
theorem B875655 : Blo 872567 875655 := bstep (se 1 (by rfl) ⟨656741, by rfl⟩ : syracuseStep 875655 = 1313483) B1313483
theorem B875663 : Blo 872567 875663 := bstep (se 1 (by rfl) ⟨656747, by rfl⟩ : syracuseStep 875663 = 1313495) B1313495
theorem B875707 : Blo 872567 875707 := bstep (se 1 (by rfl) ⟨656780, by rfl⟩ : syracuseStep 875707 = 1313561) B1313561
theorem B1105159 : Blo 872567 1105159 := bstep (se 1 (by rfl) ⟨828869, by rfl⟩ : syracuseStep 1105159 = 1657739) B1657739
theorem B875783 : Blo 872567 875783 := bstep (se 1 (by rfl) ⟨656837, by rfl⟩ : syracuseStep 875783 = 1313675) B1313675
theorem B875791 : Blo 872567 875791 := bstep (se 1 (by rfl) ⟨656843, by rfl⟩ : syracuseStep 875791 = 1313687) B1313687
theorem B875835 : Blo 872567 875835 := bstep (se 1 (by rfl) ⟨656876, by rfl⟩ : syracuseStep 875835 = 1313753) B1313753
theorem B875911 : Blo 872567 875911 := bstep (se 1 (by rfl) ⟨656933, by rfl⟩ : syracuseStep 875911 = 1313867) B1313867
theorem B875919 : Blo 872567 875919 := bstep (se 1 (by rfl) ⟨656939, by rfl⟩ : syracuseStep 875919 = 1313879) B1313879
theorem B875963 : Blo 872567 875963 := bstep (se 1 (by rfl) ⟨656972, by rfl⟩ : syracuseStep 875963 = 1313945) B1313945
theorem B876039 : Blo 872567 876039 := bstep (se 1 (by rfl) ⟨657029, by rfl⟩ : syracuseStep 876039 = 1314059) B1314059
theorem B876047 : Blo 872567 876047 := bstep (se 1 (by rfl) ⟨657035, by rfl⟩ : syracuseStep 876047 = 1314071) B1314071
theorem B876091 : Blo 872567 876091 := bstep (se 1 (by rfl) ⟨657068, by rfl⟩ : syracuseStep 876091 = 1314137) B1314137
theorem B1662599 : Blo 872567 1662599 := bstep (se 1 (by rfl) ⟨1246949, by rfl⟩ : syracuseStep 1662599 = 2493899) B2493899
theorem B876167 : Blo 872567 876167 := bstep (se 1 (by rfl) ⟨657125, by rfl⟩ : syracuseStep 876167 = 1314251) B1314251
theorem B876175 : Blo 872567 876175 := bstep (se 1 (by rfl) ⟨657131, by rfl⟩ : syracuseStep 876175 = 1314263) B1314263
theorem B1105579 : Blo 872567 1105579 := bstep (se 1 (by rfl) ⟨829184, by rfl⟩ : syracuseStep 1105579 = 1658369) B1658369
theorem B876219 : Blo 872567 876219 := bstep (se 1 (by rfl) ⟨657164, by rfl⟩ : syracuseStep 876219 = 1314329) B1314329
theorem B876295 : Blo 872567 876295 := bstep (se 1 (by rfl) ⟨657221, by rfl⟩ : syracuseStep 876295 = 1314443) B1314443
theorem B876303 : Blo 872567 876303 := bstep (se 1 (by rfl) ⟨657227, by rfl⟩ : syracuseStep 876303 = 1314455) B1314455
theorem B876347 : Blo 872567 876347 := bstep (se 1 (by rfl) ⟨657260, by rfl⟩ : syracuseStep 876347 = 1314521) B1314521
theorem B876423 : Blo 872567 876423 := bstep (se 1 (by rfl) ⟨657317, by rfl⟩ : syracuseStep 876423 = 1314635) B1314635
theorem B1105807 : Blo 872567 1105807 := bstep (se 1 (by rfl) ⟨829355, by rfl⟩ : syracuseStep 1105807 = 1658711) B1658711
theorem B876431 : Blo 872567 876431 := bstep (se 1 (by rfl) ⟨657323, by rfl⟩ : syracuseStep 876431 = 1314647) B1314647
theorem B6643619 : Blo 872567 6643619 := bstep (se 1 (by rfl) ⟨4982714, by rfl⟩ : syracuseStep 6643619 = 9965429) B9965429
theorem B876475 : Blo 872567 876475 := bstep (se 1 (by rfl) ⟨657356, by rfl⟩ : syracuseStep 876475 = 1314713) B1314713
theorem B876551 : Blo 872567 876551 := bstep (se 1 (by rfl) ⟨657413, by rfl⟩ : syracuseStep 876551 = 1314827) B1314827
theorem B876559 : Blo 872567 876559 := bstep (se 1 (by rfl) ⟨657419, by rfl⟩ : syracuseStep 876559 = 1314839) B1314839
theorem B1106551 : Blo 872567 1106551 := bstep (se 1 (by rfl) ⟨829913, by rfl⟩ : syracuseStep 1106551 = 1659827) B1659827
theorem B1991315 : Blo 872567 1991315 := bstep (se 1 (by rfl) ⟨1493486, by rfl⟩ : syracuseStep 1991315 = 2986973) B2986973
theorem B1106875 : Blo 872567 1106875 := bstep (se 1 (by rfl) ⟨830156, by rfl⟩ : syracuseStep 1106875 = 1660313) B1660313
theorem B3728699 : Blo 872567 3728699 := bstep (se 1 (by rfl) ⟨2796524, by rfl⟩ : syracuseStep 3728699 = 5593049) B5593049
theorem B1107371 : Blo 872567 1107371 := bstep (se 1 (by rfl) ⟨830528, by rfl⟩ : syracuseStep 1107371 = 1661057) B1661057
theorem B5596715 : Blo 872567 5596715 := bstep (se 1 (by rfl) ⟨4197536, by rfl⟩ : syracuseStep 5596715 = 8395073) B8395073
theorem B5596739 : Blo 872567 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B3368719 : Blo 872567 3368719 := bstep (se 1 (by rfl) ⟨2526539, by rfl⟩ : syracuseStep 3368719 = 5053079) B5053079
theorem B4417415 : Blo 872567 4417415 := bstep (se 1 (by rfl) ⟨3313061, by rfl⟩ : syracuseStep 4417415 = 6626123) B6626123
theorem B1107847 : Blo 872567 1107847 := bstep (se 1 (by rfl) ⟨830885, by rfl⟩ : syracuseStep 1107847 = 1661771) B1661771
theorem B9955223 : Blo 872567 9955223 := bstep (se 1 (by rfl) ⟨7466417, by rfl⟩ : syracuseStep 9955223 = 14932835) B14932835
theorem B3991481 : Blo 872567 3991481 := bstep (se 2 (by rfl) ⟨1496805, by rfl⟩ : syracuseStep 3991481 = 2993611) B2993611
theorem B6646049 : Blo 872567 6646049 := bstep (se 2 (by rfl) ⟨2492268, by rfl⟩ : syracuseStep 6646049 = 4984537) B4984537
theorem B1108343 : Blo 872567 1108343 := bstep (se 1 (by rfl) ⟨831257, by rfl⟩ : syracuseStep 1108343 = 1662515) B1662515
theorem B1108495 : Blo 872567 1108495 := bstep (se 1 (by rfl) ⟨831371, by rfl⟩ : syracuseStep 1108495 = 1662743) B1662743
theorem B1108667 : Blo 872567 1108667 := bstep (se 1 (by rfl) ⟨831500, by rfl⟩ : syracuseStep 1108667 = 1663001) B1663001
theorem B2485025 : Blo 872567 2485025 := bstep (se 2 (by rfl) ⟨931884, by rfl⟩ : syracuseStep 2485025 = 1863769) B1863769
theorem B1403849 : Blo 872567 1403849 := bstep (se 2 (by rfl) ⟨526443, by rfl⟩ : syracuseStep 1403849 = 1052887) B1052887
theorem B3730475 : Blo 872567 3730475 := bstep (se 1 (by rfl) ⟨2797856, by rfl⟩ : syracuseStep 3730475 = 5595713) B5595713
theorem B2485367 : Blo 872567 2485367 := bstep (se 1 (by rfl) ⟨1864025, by rfl⟩ : syracuseStep 2485367 = 3728051) B3728051
theorem B4975789 : Blo 872567 4975789 := bstep (se 3 (by rfl) ⟨932960, by rfl⟩ : syracuseStep 4975789 = 1865921) B1865921
theorem B6647021 : Blo 872567 6647021 := bstep (se 3 (by rfl) ⟨1246316, by rfl⟩ : syracuseStep 6647021 = 2492633) B2492633
theorem B5041693 : Blo 872567 5041693 := bstep (se 3 (by rfl) ⟨945317, by rfl⟩ : syracuseStep 5041693 = 1890635) B1890635
theorem B145288835 : Blo 872567 145288835 := bstep (se 1 (by rfl) ⟨108966626, by rfl⟩ : syracuseStep 145288835 = 217933253) B217933253
theorem B2486027 : Blo 872567 2486027 := bstep (se 1 (by rfl) ⟨1864520, by rfl⟩ : syracuseStep 2486027 = 3729041) B3729041
theorem B3731467 : Blo 872567 3731467 := bstep (se 1 (by rfl) ⟨2798600, by rfl⟩ : syracuseStep 3731467 = 5597201) B5597201
theorem B16806365 : Blo 872567 16806365 := bstep (se 3 (by rfl) ⟨3151193, by rfl⟩ : syracuseStep 16806365 = 6302387) B6302387
theorem B5108285 : Blo 872567 5108285 := bstep (se 3 (by rfl) ⟨957803, by rfl⟩ : syracuseStep 5108285 = 1915607) B1915607
theorem B2945807 : Blo 872567 2945807 := bstep (se 1 (by rfl) ⟨2209355, by rfl⟩ : syracuseStep 2945807 = 4418711) B4418711
theorem B2946077 : Blo 872567 2946077 := bstep (se 3 (by rfl) ⟨552389, by rfl⟩ : syracuseStep 2946077 = 1104779) B1104779
theorem B6648965 : Blo 872567 6648965 := bstep (se 4 (by rfl) ⟨623340, by rfl⟩ : syracuseStep 6648965 = 1246681) B1246681
theorem B2487611 : Blo 872567 2487611 := bstep (se 1 (by rfl) ⟨1865708, by rfl⟩ : syracuseStep 2487611 = 3731417) B3731417
theorem B4420979 : Blo 872567 4420979 := bstep (se 1 (by rfl) ⟨3315734, by rfl⟩ : syracuseStep 4420979 = 6631469) B6631469
theorem B2487667 : Blo 872567 2487667 := bstep (se 1 (by rfl) ⟨1865750, by rfl⟩ : syracuseStep 2487667 = 3731501) B3731501
theorem B10614161 : Blo 872567 10614161 := bstep (se 2 (by rfl) ⟨3980310, by rfl⟩ : syracuseStep 10614161 = 7960621) B7960621
theorem B4978205 : Blo 872567 4978205 := bstep (se 3 (by rfl) ⟨933413, by rfl⟩ : syracuseStep 4978205 = 1866827) B1866827
theorem B1963655 : Blo 872567 1963655 := bstep (se 1 (by rfl) ⟨1472741, by rfl⟩ : syracuseStep 1963655 = 2945483) B2945483
theorem B7993025 : Blo 872567 7993025 := bstep (se 2 (by rfl) ⟨2997384, by rfl⟩ : syracuseStep 7993025 = 5994769) B5994769
theorem B2488009 : Blo 872567 2488009 := bstep (se 2 (by rfl) ⟨933003, by rfl⟩ : syracuseStep 2488009 = 1866007) B1866007
theorem B1963835 : Blo 872567 1963835 := bstep (se 1 (by rfl) ⟨1472876, by rfl⟩ : syracuseStep 1963835 = 2945753) B2945753
theorem B18904907 : Blo 872567 18904907 := bstep (se 1 (by rfl) ⟨14178680, by rfl⟩ : syracuseStep 18904907 = 28357361) B28357361
theorem B4421465 : Blo 872567 4421465 := bstep (se 2 (by rfl) ⟨1658049, by rfl⟩ : syracuseStep 4421465 = 3316099) B3316099
theorem B1963961 : Blo 872567 1963961 := bstep (se 2 (by rfl) ⟨736485, by rfl⟩ : syracuseStep 1963961 = 1472971) B1472971
theorem B1472647 : Blo 872567 1472647 := bstep (se 1 (by rfl) ⟨1104485, by rfl⟩ : syracuseStep 1472647 = 2208971) B2208971
theorem B9959597 : Blo 872567 9959597 := bstep (se 3 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 9959597 = 3734849) B3734849
theorem B1308857 : Blo 872567 1308857 := bstep (se 2 (by rfl) ⟨490821, by rfl⟩ : syracuseStep 1308857 = 981643) B981643
theorem B1308935 : Blo 872567 1308935 := bstep (se 1 (by rfl) ⟨981701, by rfl⟩ : syracuseStep 1308935 = 1963403) B1963403
theorem B1964303 : Blo 872567 1964303 := bstep (se 1 (by rfl) ⟨1473227, by rfl⟩ : syracuseStep 1964303 = 2946455) B2946455
theorem B1964321 : Blo 872567 1964321 := bstep (se 2 (by rfl) ⟨736620, by rfl⟩ : syracuseStep 1964321 = 1473241) B1473241
theorem B1308971 : Blo 872567 1308971 := bstep (se 1 (by rfl) ⟨981728, by rfl⟩ : syracuseStep 1308971 = 1963457) B1963457
theorem B1309001 : Blo 872567 1309001 := bstep (se 2 (by rfl) ⟨490875, by rfl⟩ : syracuseStep 1309001 = 981751) B981751
theorem B2947481 : Blo 872567 2947481 := bstep (se 2 (by rfl) ⟨1105305, by rfl⟩ : syracuseStep 2947481 = 2210611) B2210611
theorem B1309115 : Blo 872567 1309115 := bstep (se 1 (by rfl) ⟨981836, by rfl⟩ : syracuseStep 1309115 = 1963673) B1963673
theorem B1309175 : Blo 872567 1309175 := bstep (se 1 (by rfl) ⟨981881, by rfl⟩ : syracuseStep 1309175 = 1963763) B1963763
theorem B1309199 : Blo 872567 1309199 := bstep (se 1 (by rfl) ⟨981899, by rfl⟩ : syracuseStep 1309199 = 1963799) B1963799
theorem B1997345 : Blo 872567 1997345 := bstep (se 2 (by rfl) ⟨749004, by rfl⟩ : syracuseStep 1997345 = 1498009) B1498009
theorem B1309241 : Blo 872567 1309241 := bstep (se 2 (by rfl) ⟨490965, by rfl⟩ : syracuseStep 1309241 = 981931) B981931
theorem B1964663 : Blo 872567 1964663 := bstep (se 1 (by rfl) ⟨1473497, by rfl⟩ : syracuseStep 1964663 = 2946995) B2946995
theorem B1309319 : Blo 872567 1309319 := bstep (se 1 (by rfl) ⟨981989, by rfl⟩ : syracuseStep 1309319 = 1963979) B1963979
theorem B1309355 : Blo 872567 1309355 := bstep (se 1 (by rfl) ⟨982016, by rfl⟩ : syracuseStep 1309355 = 1964033) B1964033
theorem B1309385 : Blo 872567 1309385 := bstep (se 2 (by rfl) ⟨491019, by rfl⟩ : syracuseStep 1309385 = 982039) B982039
theorem B25197317 : Blo 872567 25197317 := bstep (se 4 (by rfl) ⟨2362248, by rfl⟩ : syracuseStep 25197317 = 4724497) B4724497
theorem B1473295 : Blo 872567 1473295 := bstep (se 1 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 1473295 = 2209943) B2209943
theorem B1964843 : Blo 872567 1964843 := bstep (se 1 (by rfl) ⟨1473632, by rfl⟩ : syracuseStep 1964843 = 2947265) B2947265
theorem B1309499 : Blo 872567 1309499 := bstep (se 1 (by rfl) ⟨982124, by rfl⟩ : syracuseStep 1309499 = 1964249) B1964249
theorem B1309559 : Blo 872567 1309559 := bstep (se 1 (by rfl) ⟨982169, by rfl⟩ : syracuseStep 1309559 = 1964339) B1964339
theorem B981895 : Blo 872567 981895 := bstep (se 1 (by rfl) ⟨736421, by rfl⟩ : syracuseStep 981895 = 1472843) B1472843
theorem B1309583 : Blo 872567 1309583 := bstep (se 1 (by rfl) ⟨982187, by rfl⟩ : syracuseStep 1309583 = 1964375) B1964375
theorem B5307281 : Blo 872567 5307281 := bstep (se 2 (by rfl) ⟨1990230, by rfl⟩ : syracuseStep 5307281 = 3980461) B3980461
theorem B1309625 : Blo 872567 1309625 := bstep (se 2 (by rfl) ⟨491109, by rfl⟩ : syracuseStep 1309625 = 982219) B982219
theorem B1309703 : Blo 872567 1309703 := bstep (se 1 (by rfl) ⟨982277, by rfl⟩ : syracuseStep 1309703 = 1964555) B1964555
theorem B1309739 : Blo 872567 1309739 := bstep (se 1 (by rfl) ⟨982304, by rfl⟩ : syracuseStep 1309739 = 1964609) B1964609
theorem B982075 : Blo 872567 982075 := bstep (se 1 (by rfl) ⟨736556, by rfl⟩ : syracuseStep 982075 = 1473113) B1473113
theorem B1309769 : Blo 872567 1309769 := bstep (se 2 (by rfl) ⟨491163, by rfl⟩ : syracuseStep 1309769 = 982327) B982327
theorem B2948183 : Blo 872567 2948183 := bstep (se 1 (by rfl) ⟨2211137, by rfl⟩ : syracuseStep 2948183 = 4422275) B4422275
theorem B1965203 : Blo 872567 1965203 := bstep (se 1 (by rfl) ⟨1473902, by rfl⟩ : syracuseStep 1965203 = 2947805) B2947805
theorem B1309883 : Blo 872567 1309883 := bstep (se 1 (by rfl) ⟨982412, by rfl⟩ : syracuseStep 1309883 = 1964825) B1964825
theorem B1965257 : Blo 872567 1965257 := bstep (se 2 (by rfl) ⟨736971, by rfl⟩ : syracuseStep 1965257 = 1473943) B1473943
theorem B1309943 : Blo 872567 1309943 := bstep (se 1 (by rfl) ⟨982457, by rfl⟩ : syracuseStep 1309943 = 1964915) B1964915
theorem B1309967 : Blo 872567 1309967 := bstep (se 1 (by rfl) ⟨982475, by rfl⟩ : syracuseStep 1309967 = 1964951) B1964951
theorem B1473835 : Blo 872567 1473835 := bstep (se 1 (by rfl) ⟨1105376, by rfl⟩ : syracuseStep 1473835 = 2210753) B2210753
theorem B1310009 : Blo 872567 1310009 := bstep (se 2 (by rfl) ⟨491253, by rfl⟩ : syracuseStep 1310009 = 982507) B982507
theorem B1310087 : Blo 872567 1310087 := bstep (se 1 (by rfl) ⟨982565, by rfl⟩ : syracuseStep 1310087 = 1965131) B1965131
theorem B1310123 : Blo 872567 1310123 := bstep (se 1 (by rfl) ⟨982592, by rfl⟩ : syracuseStep 1310123 = 1965185) B1965185
theorem B1473977 : Blo 872567 1473977 := bstep (se 2 (by rfl) ⟨552741, by rfl⟩ : syracuseStep 1473977 = 1105483) B1105483
theorem B1310153 : Blo 872567 1310153 := bstep (se 2 (by rfl) ⟨491307, by rfl⟩ : syracuseStep 1310153 = 982615) B982615
theorem B3145169 : Blo 872567 3145169 := bstep (se 2 (by rfl) ⟨1179438, by rfl⟩ : syracuseStep 3145169 = 2358877) B2358877
theorem B6651395 : Blo 872567 6651395 := bstep (se 1 (by rfl) ⟨4988546, by rfl⟩ : syracuseStep 6651395 = 9977093) B9977093
theorem B982543 : Blo 872567 982543 := bstep (se 1 (by rfl) ⟨736907, by rfl⟩ : syracuseStep 982543 = 1473815) B1473815
theorem B1310267 : Blo 872567 1310267 := bstep (se 1 (by rfl) ⟨982700, by rfl⟩ : syracuseStep 1310267 = 1965401) B1965401
theorem B2948669 : Blo 872567 2948669 := bstep (se 3 (by rfl) ⟨552875, by rfl⟩ : syracuseStep 2948669 = 1105751) B1105751
theorem B3145283 : Blo 872567 3145283 := bstep (se 1 (by rfl) ⟨2358962, by rfl⟩ : syracuseStep 3145283 = 4717925) B4717925
theorem B1310327 : Blo 872567 1310327 := bstep (se 1 (by rfl) ⟨982745, by rfl⟩ : syracuseStep 1310327 = 1965491) B1965491
theorem B2358919 : Blo 872567 2358919 := bstep (se 1 (by rfl) ⟨1769189, by rfl⟩ : syracuseStep 2358919 = 3538379) B3538379
theorem B1310351 : Blo 872567 1310351 := bstep (se 1 (by rfl) ⟨982763, by rfl⟩ : syracuseStep 1310351 = 1965527) B1965527
theorem B1310393 : Blo 872567 1310393 := bstep (se 2 (by rfl) ⟨491397, by rfl⟩ : syracuseStep 1310393 = 982795) B982795
theorem B1310471 : Blo 872567 1310471 := bstep (se 1 (by rfl) ⟨982853, by rfl⟩ : syracuseStep 1310471 = 1965707) B1965707
theorem B3538703 : Blo 872567 3538703 := bstep (se 1 (by rfl) ⟨2654027, by rfl⟩ : syracuseStep 3538703 = 5308055) B5308055
theorem B1310507 : Blo 872567 1310507 := bstep (se 1 (by rfl) ⟨982880, by rfl⟩ : syracuseStep 1310507 = 1965761) B1965761
theorem B10649393 : Blo 872567 10649393 := bstep (se 2 (by rfl) ⟨3993522, by rfl⟩ : syracuseStep 10649393 = 7987045) B7987045
theorem B26935091 : Blo 872567 26935091 := bstep (se 1 (by rfl) ⟨20201318, by rfl⟩ : syracuseStep 26935091 = 40402637) B40402637
theorem B2490173 : Blo 872567 2490173 := bstep (se 3 (by rfl) ⟨466907, by rfl⟩ : syracuseStep 2490173 = 933815) B933815
theorem B1310537 : Blo 872567 1310537 := bstep (se 2 (by rfl) ⟨491451, by rfl⟩ : syracuseStep 1310537 = 982903) B982903
theorem B1965959 : Blo 872567 1965959 := bstep (se 1 (by rfl) ⟨1474469, by rfl⟩ : syracuseStep 1965959 = 2948939) B2948939
theorem B4423571 : Blo 872567 4423571 := bstep (se 1 (by rfl) ⟨3317678, by rfl⟩ : syracuseStep 4423571 = 6635357) B6635357
theorem B28737431 : Blo 872567 28737431 := bstep (se 1 (by rfl) ⟨21553073, by rfl⟩ : syracuseStep 28737431 = 43106147) B43106147
theorem B1310651 : Blo 872567 1310651 := bstep (se 1 (by rfl) ⟨982988, by rfl⟩ : syracuseStep 1310651 = 1965977) B1965977
theorem B4980689 : Blo 872567 4980689 := bstep (se 2 (by rfl) ⟨1867758, by rfl⟩ : syracuseStep 4980689 = 3735517) B3735517
theorem B1310711 : Blo 872567 1310711 := bstep (se 1 (by rfl) ⟨983033, by rfl⟩ : syracuseStep 1310711 = 1966067) B1966067
theorem B1310729 : Blo 872567 1310729 := bstep (se 2 (by rfl) ⟨491523, by rfl⟩ : syracuseStep 1310729 = 983047) B983047
theorem B1310759 : Blo 872567 1310759 := bstep (se 1 (by rfl) ⟨983069, by rfl⟩ : syracuseStep 1310759 = 1966139) B1966139
theorem B1245223 : Blo 872567 1245223 := bstep (se 1 (by rfl) ⟨933917, by rfl⟩ : syracuseStep 1245223 = 1867835) B1867835
theorem B983119 : Blo 872567 983119 := bstep (se 1 (by rfl) ⟨737339, by rfl⟩ : syracuseStep 983119 = 1474679) B1474679
theorem B1310843 : Blo 872567 1310843 := bstep (se 1 (by rfl) ⟨983132, by rfl⟩ : syracuseStep 1310843 = 1966265) B1966265
theorem B1474807 : Blo 872567 1474807 := bstep (se 1 (by rfl) ⟨1106105, by rfl⟩ : syracuseStep 1474807 = 2212211) B2212211
theorem B1310969 : Blo 872567 1310969 := bstep (se 2 (by rfl) ⟨491613, by rfl⟩ : syracuseStep 1310969 = 983227) B983227
theorem B4260107 : Blo 872567 4260107 := bstep (se 1 (by rfl) ⟨3195080, by rfl⟩ : syracuseStep 4260107 = 6390161) B6390161
theorem B1311071 : Blo 872567 1311071 := bstep (se 1 (by rfl) ⟨983303, by rfl⟩ : syracuseStep 1311071 = 1966607) B1966607
theorem B1311083 : Blo 872567 1311083 := bstep (se 1 (by rfl) ⟨983312, by rfl⟩ : syracuseStep 1311083 = 1966625) B1966625
theorem B4981121 : Blo 872567 4981121 := bstep (se 2 (by rfl) ⟨1867920, by rfl⟩ : syracuseStep 4981121 = 3735841) B3735841
theorem B1475003 : Blo 872567 1475003 := bstep (se 1 (by rfl) ⟨1106252, by rfl⟩ : syracuseStep 1475003 = 2212505) B2212505
theorem B983515 : Blo 872567 983515 := bstep (se 1 (by rfl) ⟨737636, by rfl⟩ : syracuseStep 983515 = 1475273) B1475273
theorem B2949641 : Blo 872567 2949641 := bstep (se 2 (by rfl) ⟨1106115, by rfl⟩ : syracuseStep 2949641 = 2212231) B2212231
theorem B1475111 : Blo 872567 1475111 := bstep (se 1 (by rfl) ⟨1106333, by rfl⟩ : syracuseStep 1475111 = 2212667) B2212667
theorem B1311311 : Blo 872567 1311311 := bstep (se 1 (by rfl) ⟨983483, by rfl⟩ : syracuseStep 1311311 = 1966967) B1966967
theorem B1966715 : Blo 872567 1966715 := bstep (se 1 (by rfl) ⟨1475036, by rfl⟩ : syracuseStep 1966715 = 2950073) B2950073
theorem B1311431 : Blo 872567 1311431 := bstep (se 1 (by rfl) ⟨983573, by rfl⟩ : syracuseStep 1311431 = 1967147) B1967147
theorem B2097875 : Blo 872567 2097875 := bstep (se 1 (by rfl) ⟨1573406, by rfl⟩ : syracuseStep 2097875 = 3146813) B3146813
theorem B1966841 : Blo 872567 1966841 := bstep (se 2 (by rfl) ⟨737565, by rfl⟩ : syracuseStep 1966841 = 1475131) B1475131
theorem B3146539 : Blo 872567 3146539 := bstep (se 1 (by rfl) ⟨2359904, by rfl⟩ : syracuseStep 3146539 = 4719809) B4719809
theorem B1475401 : Blo 872567 1475401 := bstep (se 2 (by rfl) ⟨553275, by rfl⟩ : syracuseStep 1475401 = 1106551) B1106551
theorem B1311593 : Blo 872567 1311593 := bstep (se 2 (by rfl) ⟨491847, by rfl⟩ : syracuseStep 1311593 = 983695) B983695
theorem B1475435 : Blo 872567 1475435 := bstep (se 1 (by rfl) ⟨1106576, by rfl⟩ : syracuseStep 1475435 = 2213153) B2213153
theorem B1704847 : Blo 872567 1704847 := bstep (se 1 (by rfl) ⟨1278635, by rfl⟩ : syracuseStep 1704847 = 2557271) B2557271
theorem B983983 : Blo 872567 983983 := bstep (se 1 (by rfl) ⟨737987, by rfl⟩ : syracuseStep 983983 = 1475975) B1475975
theorem B1311671 : Blo 872567 1311671 := bstep (se 1 (by rfl) ⟨983753, by rfl⟩ : syracuseStep 1311671 = 1967507) B1967507
theorem B1311707 : Blo 872567 1311707 := bstep (se 1 (by rfl) ⟨983780, by rfl⟩ : syracuseStep 1311707 = 1967561) B1967561
theorem B4424705 : Blo 872567 4424705 := bstep (se 2 (by rfl) ⟨1659264, by rfl⟩ : syracuseStep 4424705 = 3318529) B3318529
theorem B1967111 : Blo 872567 1967111 := bstep (se 1 (by rfl) ⟨1475333, by rfl⟩ : syracuseStep 1967111 = 2950667) B2950667
theorem B7078961 : Blo 872567 7078961 := bstep (se 2 (by rfl) ⟨2654610, by rfl⟩ : syracuseStep 7078961 = 5309221) B5309221
theorem B1967183 : Blo 872567 1967183 := bstep (se 1 (by rfl) ⟨1475387, by rfl⟩ : syracuseStep 1967183 = 2950775) B2950775
theorem B2655389 : Blo 872567 2655389 := bstep (se 3 (by rfl) ⟨497885, by rfl⟩ : syracuseStep 2655389 = 995771) B995771
theorem B1475833 : Blo 872567 1475833 := bstep (se 2 (by rfl) ⟨553437, by rfl⟩ : syracuseStep 1475833 = 1106875) B1106875
theorem B984415 : Blo 872567 984415 := bstep (se 1 (by rfl) ⟨738311, by rfl⟩ : syracuseStep 984415 = 1476623) B1476623
theorem B2950505 : Blo 872567 2950505 := bstep (se 2 (by rfl) ⟨1106439, by rfl⟩ : syracuseStep 2950505 = 2212879) B2212879
theorem B4195709 : Blo 872567 4195709 := bstep (se 3 (by rfl) ⟨786695, by rfl⟩ : syracuseStep 4195709 = 1573391) B1573391
theorem B1312175 : Blo 872567 1312175 := bstep (se 1 (by rfl) ⟨984131, by rfl⟩ : syracuseStep 1312175 = 1968263) B1968263
theorem B1181147 : Blo 872567 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B1967579 : Blo 872567 1967579 := bstep (se 1 (by rfl) ⟨1475684, by rfl⟩ : syracuseStep 1967579 = 2951369) B2951369
theorem B3147245 : Blo 872567 3147245 := bstep (se 3 (by rfl) ⟨590108, by rfl⟩ : syracuseStep 3147245 = 1180217) B1180217
theorem B1476103 : Blo 872567 1476103 := bstep (se 1 (by rfl) ⟨1107077, by rfl⟩ : syracuseStep 1476103 = 2214155) B2214155
theorem B1312265 : Blo 872567 1312265 := bstep (se 2 (by rfl) ⟨492099, by rfl⟩ : syracuseStep 1312265 = 984199) B984199
theorem B1312295 : Blo 872567 1312295 := bstep (se 1 (by rfl) ⟨984221, by rfl⟩ : syracuseStep 1312295 = 1968443) B1968443
theorem B27264613 : Blo 872567 27264613 := bstep (se 4 (by rfl) ⟨2556057, by rfl⟩ : syracuseStep 27264613 = 5112115) B5112115
theorem B1312379 : Blo 872567 1312379 := bstep (se 1 (by rfl) ⟨984284, by rfl⟩ : syracuseStep 1312379 = 1968569) B1968569
theorem B984775 : Blo 872567 984775 := bstep (se 1 (by rfl) ⟨738581, by rfl⟩ : syracuseStep 984775 = 1477163) B1477163
theorem B5310173 : Blo 872567 5310173 := bstep (se 3 (by rfl) ⟨995657, by rfl⟩ : syracuseStep 5310173 = 1991315) B1991315
theorem B1312505 : Blo 872567 1312505 := bstep (se 2 (by rfl) ⟨492189, by rfl⟩ : syracuseStep 1312505 = 984379) B984379
theorem B6162169 : Blo 872567 6162169 := bstep (se 2 (by rfl) ⟨2310813, by rfl⟩ : syracuseStep 6162169 = 4621627) B4621627
theorem B4425515 : Blo 872567 4425515 := bstep (se 1 (by rfl) ⟨3319136, by rfl⟩ : syracuseStep 4425515 = 6638273) B6638273
theorem B1312607 : Blo 872567 1312607 := bstep (se 1 (by rfl) ⟨984455, by rfl⟩ : syracuseStep 1312607 = 1968911) B1968911
theorem B1312619 : Blo 872567 1312619 := bstep (se 1 (by rfl) ⟨984464, by rfl⟩ : syracuseStep 1312619 = 1968929) B1968929
theorem B2099105 : Blo 872567 2099105 := bstep (se 2 (by rfl) ⟨787164, by rfl⟩ : syracuseStep 2099105 = 1574329) B1574329
theorem B1968047 : Blo 872567 1968047 := bstep (se 1 (by rfl) ⟨1476035, by rfl⟩ : syracuseStep 1968047 = 2952071) B2952071
theorem B1476535 : Blo 872567 1476535 := bstep (se 1 (by rfl) ⟨1107401, by rfl⟩ : syracuseStep 1476535 = 2214803) B2214803
theorem B2951099 : Blo 872567 2951099 := bstep (se 1 (by rfl) ⟨2213324, by rfl⟩ : syracuseStep 2951099 = 4426649) B4426649
theorem B1312847 : Blo 872567 1312847 := bstep (se 1 (by rfl) ⟨984635, by rfl⟩ : syracuseStep 1312847 = 1969271) B1969271
theorem B1476731 : Blo 872567 1476731 := bstep (se 1 (by rfl) ⟨1107548, by rfl⟩ : syracuseStep 1476731 = 2215097) B2215097
theorem B1968299 : Blo 872567 1968299 := bstep (se 1 (by rfl) ⟨1476224, by rfl⟩ : syracuseStep 1968299 = 2952449) B2952449
theorem B1312967 : Blo 872567 1312967 := bstep (se 1 (by rfl) ⟨984725, by rfl⟩ : syracuseStep 1312967 = 1969451) B1969451
theorem B4491625 : Blo 872567 4491625 := bstep (se 2 (by rfl) ⟨1684359, by rfl⟩ : syracuseStep 4491625 = 3368719) B3368719
theorem B1313129 : Blo 872567 1313129 := bstep (se 2 (by rfl) ⟨492423, by rfl⟩ : syracuseStep 1313129 = 984847) B984847
theorem B2656655 : Blo 872567 2656655 := bstep (se 1 (by rfl) ⟨1992491, by rfl⟩ : syracuseStep 2656655 = 3984983) B3984983
theorem B1313207 : Blo 872567 1313207 := bstep (se 1 (by rfl) ⟨984905, by rfl⟩ : syracuseStep 1313207 = 1969811) B1969811
theorem B1313243 : Blo 872567 1313243 := bstep (se 1 (by rfl) ⟨984932, by rfl⟩ : syracuseStep 1313243 = 1969865) B1969865
theorem B1477129 : Blo 872567 1477129 := bstep (se 2 (by rfl) ⟨553923, by rfl⟩ : syracuseStep 1477129 = 1107847) B1107847
theorem B985639 : Blo 872567 985639 := bstep (se 1 (by rfl) ⟨739229, by rfl⟩ : syracuseStep 985639 = 1478459) B1478459
theorem B1477291 : Blo 872567 1477291 := bstep (se 1 (by rfl) ⟨1107968, by rfl⟩ : syracuseStep 1477291 = 2215937) B2215937
theorem B1968839 : Blo 872567 1968839 := bstep (se 1 (by rfl) ⟨1476629, by rfl⟩ : syracuseStep 1968839 = 2953259) B2953259
theorem B1870535 : Blo 872567 1870535 := bstep (se 1 (by rfl) ⟨1402901, by rfl⟩ : syracuseStep 1870535 = 2805803) B2805803
theorem B6654797 : Blo 872567 6654797 := bstep (se 3 (by rfl) ⟨1247774, by rfl⟩ : syracuseStep 6654797 = 2495549) B2495549
theorem B1051499 : Blo 872567 1051499 := bstep (se 1 (by rfl) ⟨788624, by rfl⟩ : syracuseStep 1051499 = 1577249) B1577249
theorem B1313711 : Blo 872567 1313711 := bstep (se 1 (by rfl) ⟨985283, by rfl⟩ : syracuseStep 1313711 = 1970567) B1970567
theorem B1477595 : Blo 872567 1477595 := bstep (se 1 (by rfl) ⟨1108196, by rfl⟩ : syracuseStep 1477595 = 2216393) B2216393
theorem B1313801 : Blo 872567 1313801 := bstep (se 2 (by rfl) ⟨492675, by rfl⟩ : syracuseStep 1313801 = 985351) B985351
theorem B1313831 : Blo 872567 1313831 := bstep (se 1 (by rfl) ⟨985373, by rfl⟩ : syracuseStep 1313831 = 1970747) B1970747
theorem B887887 : Blo 872567 887887 := bstep (se 1 (by rfl) ⟨665915, by rfl⟩ : syracuseStep 887887 = 1331831) B1331831
theorem B1313915 : Blo 872567 1313915 := bstep (se 1 (by rfl) ⟨985436, by rfl⟩ : syracuseStep 1313915 = 1970873) B1970873
theorem B7015619 : Blo 872567 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B1477831 : Blo 872567 1477831 := bstep (se 1 (by rfl) ⟨1108373, by rfl⟩ : syracuseStep 1477831 = 2216747) B2216747
theorem B1314041 : Blo 872567 1314041 := bstep (se 2 (by rfl) ⟨492765, by rfl⟩ : syracuseStep 1314041 = 985531) B985531
theorem B888143 : Blo 872567 888143 := bstep (se 1 (by rfl) ⟨666107, by rfl⟩ : syracuseStep 888143 = 1332215) B1332215
theorem B1314143 : Blo 872567 1314143 := bstep (se 1 (by rfl) ⟨985607, by rfl⟩ : syracuseStep 1314143 = 1971215) B1971215
theorem B1477993 : Blo 872567 1477993 := bstep (se 2 (by rfl) ⟨554247, by rfl⟩ : syracuseStep 1477993 = 1108495) B1108495
theorem B1314155 : Blo 872567 1314155 := bstep (se 1 (by rfl) ⟨985616, by rfl⟩ : syracuseStep 1314155 = 1971233) B1971233
theorem B1969703 : Blo 872567 1969703 := bstep (se 1 (by rfl) ⟨1477277, by rfl⟩ : syracuseStep 1969703 = 2954555) B2954555
theorem B1314383 : Blo 872567 1314383 := bstep (se 1 (by rfl) ⟨985787, by rfl⟩ : syracuseStep 1314383 = 1971575) B1971575
theorem B3149435 : Blo 872567 3149435 := bstep (se 1 (by rfl) ⟨2362076, by rfl⟩ : syracuseStep 3149435 = 4724153) B4724153
theorem B2952827 : Blo 872567 2952827 := bstep (se 1 (by rfl) ⟨2214620, by rfl⟩ : syracuseStep 2952827 = 4429241) B4429241
theorem B2494091 : Blo 872567 2494091 := bstep (se 1 (by rfl) ⟨1870568, by rfl⟩ : syracuseStep 2494091 = 3741137) B3741137
theorem B1314503 : Blo 872567 1314503 := bstep (se 1 (by rfl) ⟨985877, by rfl⟩ : syracuseStep 1314503 = 1971755) B1971755
theorem B2952989 : Blo 872567 2952989 := bstep (se 3 (by rfl) ⟨553685, by rfl⟩ : syracuseStep 2952989 = 1107371) B1107371
theorem B1314665 : Blo 872567 1314665 := bstep (se 2 (by rfl) ⟨492999, by rfl⟩ : syracuseStep 1314665 = 985999) B985999
theorem B1970027 : Blo 872567 1970027 := bstep (se 1 (by rfl) ⟨1477520, by rfl⟩ : syracuseStep 1970027 = 2955041) B2955041
theorem B1871723 : Blo 872567 1871723 := bstep (se 1 (by rfl) ⟨1403792, by rfl⟩ : syracuseStep 1871723 = 2807585) B2807585
theorem B2101153 : Blo 872567 2101153 := bstep (se 2 (by rfl) ⟨787932, by rfl⟩ : syracuseStep 2101153 = 1575865) B1575865
theorem B1970081 : Blo 872567 1970081 := bstep (se 2 (by rfl) ⟨738780, by rfl⟩ : syracuseStep 1970081 = 1477561) B1477561
theorem B1314743 : Blo 872567 1314743 := bstep (se 1 (by rfl) ⟨986057, by rfl⟩ : syracuseStep 1314743 = 1972115) B1972115
theorem B9441211 : Blo 872567 9441211 := bstep (se 1 (by rfl) ⟨7080908, by rfl⟩ : syracuseStep 9441211 = 14161817) B14161817
theorem B1478587 : Blo 872567 1478587 := bstep (se 1 (by rfl) ⟨1108940, by rfl⟩ : syracuseStep 1478587 = 2217881) B2217881
theorem B5607377 : Blo 872567 5607377 := bstep (se 2 (by rfl) ⟨2102766, by rfl⟩ : syracuseStep 5607377 = 4205533) B4205533
theorem B1314779 : Blo 872567 1314779 := bstep (se 1 (by rfl) ⟨986084, by rfl⟩ : syracuseStep 1314779 = 1972169) B1972169
theorem B4427783 : Blo 872567 4427783 := bstep (se 1 (by rfl) ⟨3320837, by rfl⟩ : syracuseStep 4427783 = 6641675) B6641675
theorem B1478695 : Blo 872567 1478695 := bstep (se 1 (by rfl) ⟨1109021, by rfl⟩ : syracuseStep 1478695 = 2218043) B2218043
theorem B1970423 : Blo 872567 1970423 := bstep (se 1 (by rfl) ⟨1477817, by rfl⟩ : syracuseStep 1970423 = 2955635) B2955635
theorem B1479019 : Blo 872567 1479019 := bstep (se 1 (by rfl) ⟨1109264, by rfl⟩ : syracuseStep 1479019 = 2218529) B2218529
theorem B2953691 : Blo 872567 2953691 := bstep (se 1 (by rfl) ⟨2215268, by rfl⟩ : syracuseStep 2953691 = 4430537) B4430537
theorem B4428269 : Blo 872567 4428269 := bstep (se 3 (by rfl) ⟨830300, by rfl⟩ : syracuseStep 4428269 = 1660601) B1660601
theorem B4264633 : Blo 872567 4264633 := bstep (se 2 (by rfl) ⟨1599237, by rfl⟩ : syracuseStep 4264633 = 3198475) B3198475
theorem B3740489 : Blo 872567 3740489 := bstep (se 2 (by rfl) ⟨1402683, by rfl⟩ : syracuseStep 3740489 = 2805367) B2805367
theorem B1971017 : Blo 872567 1971017 := bstep (se 2 (by rfl) ⟨739131, by rfl⟩ : syracuseStep 1971017 = 1478263) B1478263
theorem B11211929 : Blo 872567 11211929 := bstep (se 2 (by rfl) ⟨4204473, by rfl⟩ : syracuseStep 11211929 = 8408947) B8408947
theorem B2954393 : Blo 872567 2954393 := bstep (se 2 (by rfl) ⟨1107897, by rfl⟩ : syracuseStep 2954393 = 2215795) B2215795
theorem B4429079 : Blo 872567 4429079 := bstep (se 1 (by rfl) ⟨3321809, by rfl⟩ : syracuseStep 4429079 = 6643619) B6643619
theorem B8394185 : Blo 872567 8394185 := bstep (se 2 (by rfl) ⟨3147819, by rfl⟩ : syracuseStep 8394185 = 6295639) B6295639
theorem B1971809 : Blo 872567 1971809 := bstep (se 2 (by rfl) ⟨739428, by rfl⟩ : syracuseStep 1971809 = 1478857) B1478857
theorem B2561675 : Blo 872567 2561675 := bstep (se 1 (by rfl) ⟨1921256, by rfl⟩ : syracuseStep 2561675 = 3842513) B3842513
theorem B1972151 : Blo 872567 1972151 := bstep (se 1 (by rfl) ⟨1479113, by rfl⟩ : syracuseStep 1972151 = 2958227) B2958227
theorem B2103467 : Blo 872567 2103467 := bstep (se 1 (by rfl) ⟨1577600, by rfl⟩ : syracuseStep 2103467 = 3155201) B3155201
theorem B2955581 : Blo 872567 2955581 := bstep (se 3 (by rfl) ⟨554171, by rfl⟩ : syracuseStep 2955581 = 1108343) B1108343
theorem B2660987 : Blo 872567 2660987 := bstep (se 1 (by rfl) ⟨1995740, by rfl⟩ : syracuseStep 2660987 = 3991481) B3991481
theorem B4430699 : Blo 872567 4430699 := bstep (se 1 (by rfl) ⟨3323024, by rfl⟩ : syracuseStep 4430699 = 6646049) B6646049
theorem B1776545 : Blo 872567 1776545 := bstep (se 2 (by rfl) ⟨666204, by rfl⟩ : syracuseStep 1776545 = 1332409) B1332409
theorem B3316889 : Blo 872567 3316889 := bstep (se 2 (by rfl) ⟨1243833, by rfl⟩ : syracuseStep 3316889 = 2487667) B2487667
theorem B2956445 : Blo 872567 2956445 := bstep (se 3 (by rfl) ⟨554333, by rfl⟩ : syracuseStep 2956445 = 1108667) B1108667
theorem B9706787 : Blo 872567 9706787 := bstep (se 1 (by rfl) ⟨7280090, by rfl⟩ : syracuseStep 9706787 = 14560181) B14560181
theorem B4201901 : Blo 872567 4201901 := bstep (se 3 (by rfl) ⟨787856, by rfl⟩ : syracuseStep 4201901 = 1575713) B1575713
theorem B4431347 : Blo 872567 4431347 := bstep (se 1 (by rfl) ⟨3323510, by rfl⟩ : syracuseStep 4431347 = 6647021) B6647021
theorem B3546683 : Blo 872567 3546683 := bstep (se 1 (by rfl) ⟨2660012, by rfl⟩ : syracuseStep 3546683 = 5320025) B5320025
theorem B3317345 : Blo 872567 3317345 := bstep (se 2 (by rfl) ⟨1244004, by rfl⟩ : syracuseStep 3317345 = 2488009) B2488009
theorem B2956985 : Blo 872567 2956985 := bstep (se 2 (by rfl) ⟨1108869, by rfl⟩ : syracuseStep 2956985 = 2217739) B2217739
theorem B3743597 : Blo 872567 3743597 := bstep (se 3 (by rfl) ⟨701924, by rfl⟩ : syracuseStep 3743597 = 1403849) B1403849
theorem B14950331 : Blo 872567 14950331 := bstep (se 1 (by rfl) ⟨11212748, by rfl⟩ : syracuseStep 14950331 = 22425497) B22425497
theorem B46768141 : Blo 872567 46768141 := bstep (se 3 (by rfl) ⟨8769026, by rfl⟩ : syracuseStep 46768141 = 17538053) B17538053
theorem B2957579 : Blo 872567 2957579 := bstep (se 1 (by rfl) ⟨2218184, by rfl⟩ : syracuseStep 2957579 = 4436369) B4436369
theorem B2957849 : Blo 872567 2957849 := bstep (se 2 (by rfl) ⟨1109193, by rfl⟩ : syracuseStep 2957849 = 2218387) B2218387
theorem B4432643 : Blo 872567 4432643 := bstep (se 1 (by rfl) ⟨3324482, by rfl⟩ : syracuseStep 4432643 = 6648965) B6648965
theorem B3318803 : Blo 872567 3318803 := bstep (se 1 (by rfl) ⟨2489102, by rfl⟩ : syracuseStep 3318803 = 4978205) B4978205
theorem B53880025 : Blo 872567 53880025 := bstep (se 2 (by rfl) ⟨20205009, by rfl⟩ : syracuseStep 53880025 = 40410019) B40410019
theorem B5383415 : Blo 872567 5383415 := bstep (se 1 (by rfl) ⟨4037561, by rfl⟩ : syracuseStep 5383415 = 8075123) B8075123
theorem B9971261 : Blo 872567 9971261 := bstep (se 3 (by rfl) ⟨1869611, by rfl⟩ : syracuseStep 9971261 = 3739223) B3739223
theorem B5613245 : Blo 872567 5613245 := bstep (se 3 (by rfl) ⟨1052483, by rfl⟩ : syracuseStep 5613245 = 2104967) B2104967
theorem B3155807 : Blo 872567 3155807 := bstep (se 1 (by rfl) ⟨2366855, by rfl⟩ : syracuseStep 3155807 = 4733711) B4733711
theorem B4434263 : Blo 872567 4434263 := bstep (se 1 (by rfl) ⟨3325697, by rfl⟩ : syracuseStep 4434263 = 6651395) B6651395
theorem B3320459 : Blo 872567 3320459 := bstep (se 1 (by rfl) ⟨2490344, by rfl⟩ : syracuseStep 3320459 = 4980689) B4980689
theorem B2796551 : Blo 872567 2796551 := bstep (se 1 (by rfl) ⟨2097413, by rfl⟩ : syracuseStep 2796551 = 4194827) B4194827
theorem B3157163 : Blo 872567 3157163 := bstep (se 1 (by rfl) ⟨2367872, by rfl⟩ : syracuseStep 3157163 = 4735745) B4735745
theorem B3321719 : Blo 872567 3321719 := bstep (se 1 (by rfl) ⟨2491289, by rfl⟩ : syracuseStep 3321719 = 4982579) B4982579
theorem B3158777 : Blo 872567 3158777 := bstep (se 2 (by rfl) ⟨1184541, by rfl⟩ : syracuseStep 3158777 = 2369083) B2369083
theorem B3322691 : Blo 872567 3322691 := bstep (se 1 (by rfl) ⟨2492018, by rfl⟩ : syracuseStep 3322691 = 4984037) B4984037
theorem B2209153 : Blo 872567 2209153 := bstep (se 2 (by rfl) ⟨828432, by rfl⟩ : syracuseStep 2209153 = 1656865) B1656865
theorem B2799319 : Blo 872567 2799319 := bstep (se 1 (by rfl) ⟨2099489, by rfl⟩ : syracuseStep 2799319 = 4198979) B4198979
theorem B181778519 : Blo 872567 181778519 := bstep (se 1 (by rfl) ⟨136333889, by rfl⟩ : syracuseStep 181778519 = 272667779) B272667779
theorem B2209963 : Blo 872567 2209963 := bstep (se 1 (by rfl) ⟨1657472, by rfl⟩ : syracuseStep 2209963 = 3314945) B3314945
theorem B3324361 : Blo 872567 3324361 := bstep (se 2 (by rfl) ⟨1246635, by rfl⟩ : syracuseStep 3324361 = 2493271) B2493271
theorem B2210267 : Blo 872567 2210267 := bstep (se 1 (by rfl) ⟨1657700, by rfl⟩ : syracuseStep 2210267 = 3315401) B3315401
theorem B3324665 : Blo 872567 3324665 := bstep (se 2 (by rfl) ⟨1246749, by rfl⟩ : syracuseStep 3324665 = 2493499) B2493499
theorem B6634385 : Blo 872567 6634385 := bstep (se 2 (by rfl) ⟨2487894, by rfl⟩ : syracuseStep 6634385 = 4975789) B4975789
theorem B3324833 : Blo 872567 3324833 := bstep (se 2 (by rfl) ⟨1246812, by rfl⟩ : syracuseStep 3324833 = 2493625) B2493625
theorem B3324847 : Blo 872567 3324847 := bstep (se 1 (by rfl) ⟨2493635, by rfl⟩ : syracuseStep 3324847 = 4987271) B4987271
theorem B12598199 : Blo 872567 12598199 := bstep (se 1 (by rfl) ⟨9448649, by rfl⟩ : syracuseStep 12598199 = 18897299) B18897299
theorem B998363 : Blo 872567 998363 := bstep (se 1 (by rfl) ⟨748772, by rfl⟩ : syracuseStep 998363 = 1497545) B1497545
theorem B3325805 : Blo 872567 3325805 := bstep (se 3 (by rfl) ⟨623588, by rfl⟩ : syracuseStep 3325805 = 1247177) B1247177
theorem B2211745 : Blo 872567 2211745 := bstep (se 2 (by rfl) ⟨829404, by rfl⟩ : syracuseStep 2211745 = 1658809) B1658809
theorem B9945017 : Blo 872567 9945017 := bstep (se 2 (by rfl) ⟨3729381, by rfl⟩ : syracuseStep 9945017 = 7458763) B7458763
theorem B4210625 : Blo 872567 4210625 := bstep (se 2 (by rfl) ⟨1578984, by rfl⟩ : syracuseStep 4210625 = 3157969) B3157969
theorem B10076237 : Blo 872567 10076237 := bstep (se 3 (by rfl) ⟨1889294, by rfl⟩ : syracuseStep 10076237 = 3778589) B3778589
theorem B3326123 : Blo 872567 3326123 := bstep (se 1 (by rfl) ⟨2494592, by rfl⟩ : syracuseStep 3326123 = 4989185) B4989185
theorem B2802215 : Blo 872567 2802215 := bstep (se 1 (by rfl) ⟨2101661, by rfl⟩ : syracuseStep 2802215 = 4203323) B4203323
theorem B3195677 : Blo 872567 3195677 := bstep (se 3 (by rfl) ⟨599189, by rfl⟩ : syracuseStep 3195677 = 1198379) B1198379
theorem B6309017 : Blo 872567 6309017 := bstep (se 2 (by rfl) ⟨2365881, by rfl⟩ : syracuseStep 6309017 = 4731763) B4731763
theorem B6636815 : Blo 872567 6636815 := bstep (se 1 (by rfl) ⟨4977611, by rfl⟩ : syracuseStep 6636815 = 9955223) B9955223
theorem B1656683 : Blo 872567 1656683 := bstep (se 1 (by rfl) ⟨1242512, by rfl⟩ : syracuseStep 1656683 = 2485025) B2485025
theorem B2803727 : Blo 872567 2803727 := bstep (se 1 (by rfl) ⟨2102795, by rfl⟩ : syracuseStep 2803727 = 4205591) B4205591
theorem B1656911 : Blo 872567 1656911 := bstep (se 1 (by rfl) ⟨1242683, by rfl⟩ : syracuseStep 1656911 = 2485367) B2485367
theorem B2214287 : Blo 872567 2214287 := bstep (se 1 (by rfl) ⟨1660715, by rfl⟩ : syracuseStep 2214287 = 3321431) B3321431
theorem B2804111 : Blo 872567 2804111 := bstep (se 1 (by rfl) ⟨2103083, by rfl⟩ : syracuseStep 2804111 = 4206167) B4206167
theorem B1657351 : Blo 872567 1657351 := bstep (se 1 (by rfl) ⟨1243013, by rfl⟩ : syracuseStep 1657351 = 2486027) B2486027
theorem B12601889 : Blo 872567 12601889 := bstep (se 2 (by rfl) ⟨4725708, by rfl⟩ : syracuseStep 12601889 = 9451417) B9451417
theorem B2214611 : Blo 872567 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B9947933 : Blo 872567 9947933 := bstep (se 3 (by rfl) ⟨1865237, by rfl⟩ : syracuseStep 9947933 = 3730475) B3730475
theorem B26889029 : Blo 872567 26889029 := bstep (se 4 (by rfl) ⟨2520846, by rfl⟩ : syracuseStep 26889029 = 5041693) B5041693
theorem B1330025 : Blo 872567 1330025 := bstep (se 2 (by rfl) ⟨498759, by rfl⟩ : syracuseStep 1330025 = 997519) B997519
theorem B1658407 : Blo 872567 1658407 := bstep (se 1 (by rfl) ⟨1243805, by rfl⟩ : syracuseStep 1658407 = 2487611) B2487611
theorem B13618775 : Blo 872567 13618775 := bstep (se 1 (by rfl) ⟨10214081, by rfl⟩ : syracuseStep 13618775 = 20428163) B20428163
theorem B5328683 : Blo 872567 5328683 := bstep (se 1 (by rfl) ⟨3996512, by rfl⟩ : syracuseStep 5328683 = 7993025) B7993025
theorem B2215775 : Blo 872567 2215775 := bstep (se 1 (by rfl) ⟨1661831, by rfl⟩ : syracuseStep 2215775 = 3323663) B3323663
theorem B12603271 : Blo 872567 12603271 := bstep (se 1 (by rfl) ⟨9452453, by rfl⟩ : syracuseStep 12603271 = 18904907) B18904907
theorem B6639731 : Blo 872567 6639731 := bstep (se 1 (by rfl) ⟨4979798, by rfl⟩ : syracuseStep 6639731 = 9959597) B9959597
theorem B872571 : Blo 872567 872571 := bstep (se 1 (by rfl) ⟨654428, by rfl⟩ : syracuseStep 872571 = 1308857) B1308857
theorem B872623 : Blo 872567 872623 := bstep (se 1 (by rfl) ⟨654467, by rfl⟩ : syracuseStep 872623 = 1308935) B1308935
theorem B872647 : Blo 872567 872647 := bstep (se 1 (by rfl) ⟨654485, by rfl⟩ : syracuseStep 872647 = 1308971) B1308971
theorem B872667 : Blo 872567 872667 := bstep (se 1 (by rfl) ⟨654500, by rfl⟩ : syracuseStep 872667 = 1309001) B1309001
theorem B872743 : Blo 872567 872743 := bstep (se 1 (by rfl) ⟨654557, by rfl⟩ : syracuseStep 872743 = 1309115) B1309115
theorem B872783 : Blo 872567 872783 := bstep (se 1 (by rfl) ⟨654587, by rfl⟩ : syracuseStep 872783 = 1309175) B1309175
theorem B872799 : Blo 872567 872799 := bstep (se 1 (by rfl) ⟨654599, by rfl⟩ : syracuseStep 872799 = 1309199) B1309199
theorem B1331563 : Blo 872567 1331563 := bstep (se 1 (by rfl) ⟨998672, by rfl⟩ : syracuseStep 1331563 = 1997345) B1997345
theorem B872827 : Blo 872567 872827 := bstep (se 1 (by rfl) ⟨654620, by rfl⟩ : syracuseStep 872827 = 1309241) B1309241
theorem B872879 : Blo 872567 872879 := bstep (se 1 (by rfl) ⟨654659, by rfl⟩ : syracuseStep 872879 = 1309319) B1309319
theorem B872903 : Blo 872567 872903 := bstep (se 1 (by rfl) ⟨654677, by rfl⟩ : syracuseStep 872903 = 1309355) B1309355
theorem B872923 : Blo 872567 872923 := bstep (se 1 (by rfl) ⟨654692, by rfl⟩ : syracuseStep 872923 = 1309385) B1309385
theorem B16798211 : Blo 872567 16798211 := bstep (se 1 (by rfl) ⟨12598658, by rfl⟩ : syracuseStep 16798211 = 25197317) B25197317
theorem B872999 : Blo 872567 872999 := bstep (se 1 (by rfl) ⟨654749, by rfl⟩ : syracuseStep 872999 = 1309499) B1309499
theorem B873039 : Blo 872567 873039 := bstep (se 1 (by rfl) ⟨654779, by rfl⟩ : syracuseStep 873039 = 1309559) B1309559
theorem B873055 : Blo 872567 873055 := bstep (se 1 (by rfl) ⟨654791, by rfl⟩ : syracuseStep 873055 = 1309583) B1309583
theorem B873083 : Blo 872567 873083 := bstep (se 1 (by rfl) ⟨654812, by rfl⟩ : syracuseStep 873083 = 1309625) B1309625
theorem B873135 : Blo 872567 873135 := bstep (se 1 (by rfl) ⟨654851, by rfl⟩ : syracuseStep 873135 = 1309703) B1309703
theorem B873159 : Blo 872567 873159 := bstep (se 1 (by rfl) ⟨654869, by rfl⟩ : syracuseStep 873159 = 1309739) B1309739
theorem B873179 : Blo 872567 873179 := bstep (se 1 (by rfl) ⟨654884, by rfl⟩ : syracuseStep 873179 = 1309769) B1309769
theorem B873255 : Blo 872567 873255 := bstep (se 1 (by rfl) ⟨654941, by rfl⟩ : syracuseStep 873255 = 1309883) B1309883
theorem B2806571 : Blo 872567 2806571 := bstep (se 1 (by rfl) ⟨2104928, by rfl⟩ : syracuseStep 2806571 = 4209857) B4209857
theorem B873295 : Blo 872567 873295 := bstep (se 1 (by rfl) ⟨654971, by rfl⟩ : syracuseStep 873295 = 1309943) B1309943
theorem B873311 : Blo 872567 873311 := bstep (se 1 (by rfl) ⟨654983, by rfl⟩ : syracuseStep 873311 = 1309967) B1309967
theorem B1495903 : Blo 872567 1495903 := bstep (se 1 (by rfl) ⟨1121927, by rfl⟩ : syracuseStep 1495903 = 2243855) B2243855
theorem B43078501 : Blo 872567 43078501 := bstep (se 4 (by rfl) ⟨4038609, by rfl⟩ : syracuseStep 43078501 = 8077219) B8077219
theorem B873339 : Blo 872567 873339 := bstep (se 1 (by rfl) ⟨655004, by rfl⟩ : syracuseStep 873339 = 1310009) B1310009
theorem B873391 : Blo 872567 873391 := bstep (se 1 (by rfl) ⟨655043, by rfl⟩ : syracuseStep 873391 = 1310087) B1310087
theorem B2216879 : Blo 872567 2216879 := bstep (se 1 (by rfl) ⟨1662659, by rfl⟩ : syracuseStep 2216879 = 3325319) B3325319
theorem B873415 : Blo 872567 873415 := bstep (se 1 (by rfl) ⟨655061, by rfl⟩ : syracuseStep 873415 = 1310123) B1310123
theorem B873435 : Blo 872567 873435 := bstep (se 1 (by rfl) ⟨655076, by rfl⟩ : syracuseStep 873435 = 1310153) B1310153
theorem B873511 : Blo 872567 873511 := bstep (se 1 (by rfl) ⟨655133, by rfl⟩ : syracuseStep 873511 = 1310267) B1310267
theorem B873551 : Blo 872567 873551 := bstep (se 1 (by rfl) ⟨655163, by rfl⟩ : syracuseStep 873551 = 1310327) B1310327
theorem B873567 : Blo 872567 873567 := bstep (se 1 (by rfl) ⟨655175, by rfl⟩ : syracuseStep 873567 = 1310351) B1310351
theorem B873595 : Blo 872567 873595 := bstep (se 1 (by rfl) ⟨655196, by rfl⟩ : syracuseStep 873595 = 1310393) B1310393
theorem B873647 : Blo 872567 873647 := bstep (se 1 (by rfl) ⟨655235, by rfl⟩ : syracuseStep 873647 = 1310471) B1310471
theorem B873671 : Blo 872567 873671 := bstep (se 1 (by rfl) ⟨655253, by rfl⟩ : syracuseStep 873671 = 1310507) B1310507
theorem B7099595 : Blo 872567 7099595 := bstep (se 1 (by rfl) ⟨5324696, by rfl⟩ : syracuseStep 7099595 = 10649393) B10649393
theorem B1660115 : Blo 872567 1660115 := bstep (se 1 (by rfl) ⟨1245086, by rfl⟩ : syracuseStep 1660115 = 2490173) B2490173
theorem B873691 : Blo 872567 873691 := bstep (se 1 (by rfl) ⟨655268, by rfl⟩ : syracuseStep 873691 = 1310537) B1310537
theorem B19158287 : Blo 872567 19158287 := bstep (se 1 (by rfl) ⟨14368715, by rfl⟩ : syracuseStep 19158287 = 28737431) B28737431
theorem B873767 : Blo 872567 873767 := bstep (se 1 (by rfl) ⟨655325, by rfl⟩ : syracuseStep 873767 = 1310651) B1310651
theorem B873807 : Blo 872567 873807 := bstep (se 1 (by rfl) ⟨655355, by rfl⟩ : syracuseStep 873807 = 1310711) B1310711
theorem B873823 : Blo 872567 873823 := bstep (se 1 (by rfl) ⟨655367, by rfl⟩ : syracuseStep 873823 = 1310735) B1310735
theorem B1660267 : Blo 872567 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B873851 : Blo 872567 873851 := bstep (se 1 (by rfl) ⟨655388, by rfl⟩ : syracuseStep 873851 = 1310777) B1310777
theorem B873903 : Blo 872567 873903 := bstep (se 1 (by rfl) ⟨655427, by rfl⟩ : syracuseStep 873903 = 1310855) B1310855
theorem B873927 : Blo 872567 873927 := bstep (se 1 (by rfl) ⟨655445, by rfl⟩ : syracuseStep 873927 = 1310891) B1310891
theorem B873947 : Blo 872567 873947 := bstep (se 1 (by rfl) ⟨655460, by rfl⟩ : syracuseStep 873947 = 1310921) B1310921
theorem B6313459 : Blo 872567 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B874023 : Blo 872567 874023 := bstep (se 1 (by rfl) ⟨655517, by rfl⟩ : syracuseStep 874023 = 1311035) B1311035
theorem B874063 : Blo 872567 874063 := bstep (se 1 (by rfl) ⟨655547, by rfl⟩ : syracuseStep 874063 = 1311095) B1311095
theorem B1660495 : Blo 872567 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B874079 : Blo 872567 874079 := bstep (se 1 (by rfl) ⟨655559, by rfl⟩ : syracuseStep 874079 = 1311119) B1311119
theorem B874107 : Blo 872567 874107 := bstep (se 1 (by rfl) ⟨655580, by rfl⟩ : syracuseStep 874107 = 1311161) B1311161
theorem B3364487 : Blo 872567 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B874159 : Blo 872567 874159 := bstep (se 1 (by rfl) ⟨655619, by rfl⟩ : syracuseStep 874159 = 1311239) B1311239
theorem B874183 : Blo 872567 874183 := bstep (se 1 (by rfl) ⟨655637, by rfl⟩ : syracuseStep 874183 = 1311275) B1311275
theorem B874203 : Blo 872567 874203 := bstep (se 1 (by rfl) ⟨655652, by rfl⟩ : syracuseStep 874203 = 1311305) B1311305
theorem B874279 : Blo 872567 874279 := bstep (se 1 (by rfl) ⟨655709, by rfl⟩ : syracuseStep 874279 = 1311419) B1311419
theorem B874319 : Blo 872567 874319 := bstep (se 1 (by rfl) ⟨655739, by rfl⟩ : syracuseStep 874319 = 1311479) B1311479
theorem B874335 : Blo 872567 874335 := bstep (se 1 (by rfl) ⟨655751, by rfl⟩ : syracuseStep 874335 = 1311503) B1311503
theorem B3594091 : Blo 872567 3594091 := bstep (se 1 (by rfl) ⟨2695568, by rfl⟩ : syracuseStep 3594091 = 5391137) B5391137
theorem B874363 : Blo 872567 874363 := bstep (se 1 (by rfl) ⟨655772, by rfl⟩ : syracuseStep 874363 = 1311545) B1311545
theorem B874415 : Blo 872567 874415 := bstep (se 1 (by rfl) ⟨655811, by rfl⟩ : syracuseStep 874415 = 1311623) B1311623
theorem B874439 : Blo 872567 874439 := bstep (se 1 (by rfl) ⟨655829, by rfl⟩ : syracuseStep 874439 = 1311659) B1311659
theorem B874459 : Blo 872567 874459 := bstep (se 1 (by rfl) ⟨655844, by rfl⟩ : syracuseStep 874459 = 1311689) B1311689
theorem B874535 : Blo 872567 874535 := bstep (se 1 (by rfl) ⟨655901, by rfl⟩ : syracuseStep 874535 = 1311803) B1311803
theorem B874575 : Blo 872567 874575 := bstep (se 1 (by rfl) ⟨655931, by rfl⟩ : syracuseStep 874575 = 1311863) B1311863
theorem B2218063 : Blo 872567 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B874591 : Blo 872567 874591 := bstep (se 1 (by rfl) ⟨655943, by rfl⟩ : syracuseStep 874591 = 1311887) B1311887
theorem B874619 : Blo 872567 874619 := bstep (se 1 (by rfl) ⟨655964, by rfl⟩ : syracuseStep 874619 = 1311929) B1311929
theorem B874671 : Blo 872567 874671 := bstep (se 1 (by rfl) ⟨656003, by rfl⟩ : syracuseStep 874671 = 1312007) B1312007
theorem B874695 : Blo 872567 874695 := bstep (se 1 (by rfl) ⟨656021, by rfl⟩ : syracuseStep 874695 = 1312043) B1312043
theorem B874715 : Blo 872567 874715 := bstep (se 1 (by rfl) ⟨656036, by rfl⟩ : syracuseStep 874715 = 1312073) B1312073
theorem B874791 : Blo 872567 874791 := bstep (se 1 (by rfl) ⟨656093, by rfl⟩ : syracuseStep 874791 = 1312187) B1312187
theorem B874831 : Blo 872567 874831 := bstep (se 1 (by rfl) ⟨656123, by rfl⟩ : syracuseStep 874831 = 1312247) B1312247
theorem B7100759 : Blo 872567 7100759 := bstep (se 1 (by rfl) ⟨5325569, by rfl⟩ : syracuseStep 7100759 = 10651139) B10651139
theorem B874847 : Blo 872567 874847 := bstep (se 1 (by rfl) ⟨656135, by rfl⟩ : syracuseStep 874847 = 1312271) B1312271
theorem B874875 : Blo 872567 874875 := bstep (se 1 (by rfl) ⟨656156, by rfl⟩ : syracuseStep 874875 = 1312313) B1312313
theorem B874927 : Blo 872567 874927 := bstep (se 1 (by rfl) ⟨656195, by rfl⟩ : syracuseStep 874927 = 1312391) B1312391
theorem B874951 : Blo 872567 874951 := bstep (se 1 (by rfl) ⟨656213, by rfl⟩ : syracuseStep 874951 = 1312427) B1312427
theorem B874971 : Blo 872567 874971 := bstep (se 1 (by rfl) ⟨656228, by rfl⟩ : syracuseStep 874971 = 1312457) B1312457
theorem B875047 : Blo 872567 875047 := bstep (se 1 (by rfl) ⟨656285, by rfl⟩ : syracuseStep 875047 = 1312571) B1312571
theorem B34134605 : Blo 872567 34134605 := bstep (se 3 (by rfl) ⟨6400238, by rfl⟩ : syracuseStep 34134605 = 12800477) B12800477
theorem B875087 : Blo 872567 875087 := bstep (se 1 (by rfl) ⟨656315, by rfl⟩ : syracuseStep 875087 = 1312631) B1312631
theorem B875103 : Blo 872567 875103 := bstep (se 1 (by rfl) ⟨656327, by rfl⟩ : syracuseStep 875103 = 1312655) B1312655
theorem B875131 : Blo 872567 875131 := bstep (se 1 (by rfl) ⟨656348, by rfl⟩ : syracuseStep 875131 = 1312697) B1312697
theorem B875183 : Blo 872567 875183 := bstep (se 1 (by rfl) ⟨656387, by rfl⟩ : syracuseStep 875183 = 1312775) B1312775
theorem B875207 : Blo 872567 875207 := bstep (se 1 (by rfl) ⟨656405, by rfl⟩ : syracuseStep 875207 = 1312811) B1312811
theorem B2218711 : Blo 872567 2218711 := bstep (se 1 (by rfl) ⟨1664033, by rfl⟩ : syracuseStep 2218711 = 3328067) B3328067
theorem B875227 : Blo 872567 875227 := bstep (se 1 (by rfl) ⟨656420, by rfl⟩ : syracuseStep 875227 = 1312841) B1312841
theorem B875303 : Blo 872567 875303 := bstep (se 1 (by rfl) ⟨656477, by rfl⟩ : syracuseStep 875303 = 1312955) B1312955
theorem B14179141 : Blo 872567 14179141 := bstep (se 4 (by rfl) ⟨1329294, by rfl⟩ : syracuseStep 14179141 = 2658589) B2658589
theorem B875343 : Blo 872567 875343 := bstep (se 1 (by rfl) ⟨656507, by rfl⟩ : syracuseStep 875343 = 1313015) B1313015
theorem B875359 : Blo 872567 875359 := bstep (se 1 (by rfl) ⟨656519, by rfl⟩ : syracuseStep 875359 = 1313039) B1313039
theorem B875387 : Blo 872567 875387 := bstep (se 1 (by rfl) ⟨656540, by rfl⟩ : syracuseStep 875387 = 1313081) B1313081
theorem B875439 : Blo 872567 875439 := bstep (se 1 (by rfl) ⟨656579, by rfl⟩ : syracuseStep 875439 = 1313159) B1313159
theorem B875463 : Blo 872567 875463 := bstep (se 1 (by rfl) ⟨656597, by rfl⟩ : syracuseStep 875463 = 1313195) B1313195
theorem B875483 : Blo 872567 875483 := bstep (se 1 (by rfl) ⟨656612, by rfl⟩ : syracuseStep 875483 = 1313225) B1313225
theorem B875559 : Blo 872567 875559 := bstep (se 1 (by rfl) ⟨656669, by rfl⟩ : syracuseStep 875559 = 1313339) B1313339
theorem B875599 : Blo 872567 875599 := bstep (se 1 (by rfl) ⟨656699, by rfl⟩ : syracuseStep 875599 = 1313399) B1313399
theorem B875615 : Blo 872567 875615 := bstep (se 1 (by rfl) ⟨656711, by rfl⟩ : syracuseStep 875615 = 1313423) B1313423
theorem B875643 : Blo 872567 875643 := bstep (se 1 (by rfl) ⟨656732, by rfl⟩ : syracuseStep 875643 = 1313465) B1313465
theorem B875695 : Blo 872567 875695 := bstep (se 1 (by rfl) ⟨656771, by rfl⟩ : syracuseStep 875695 = 1313543) B1313543
theorem B875719 : Blo 872567 875719 := bstep (se 1 (by rfl) ⟨656789, by rfl⟩ : syracuseStep 875719 = 1313579) B1313579
theorem B875739 : Blo 872567 875739 := bstep (se 1 (by rfl) ⟨656804, by rfl⟩ : syracuseStep 875739 = 1313609) B1313609
theorem B11230487 : Blo 872567 11230487 := bstep (se 1 (by rfl) ⟨8422865, by rfl⟩ : syracuseStep 11230487 = 16845731) B16845731
theorem B875815 : Blo 872567 875815 := bstep (se 1 (by rfl) ⟨656861, by rfl⟩ : syracuseStep 875815 = 1313723) B1313723
theorem B875855 : Blo 872567 875855 := bstep (se 1 (by rfl) ⟨656891, by rfl⟩ : syracuseStep 875855 = 1313783) B1313783
theorem B875871 : Blo 872567 875871 := bstep (se 1 (by rfl) ⟨656903, by rfl⟩ : syracuseStep 875871 = 1313807) B1313807
theorem B5594483 : Blo 872567 5594483 := bstep (se 1 (by rfl) ⟨4195862, by rfl⟩ : syracuseStep 5594483 = 8391725) B8391725
theorem B875899 : Blo 872567 875899 := bstep (se 1 (by rfl) ⟨656924, by rfl⟩ : syracuseStep 875899 = 1313849) B1313849
theorem B4971941 : Blo 872567 4971941 := bstep (se 4 (by rfl) ⟨466119, by rfl⟩ : syracuseStep 4971941 = 932239) B932239
theorem B875951 : Blo 872567 875951 := bstep (se 1 (by rfl) ⟨656963, by rfl⟩ : syracuseStep 875951 = 1313927) B1313927
theorem B875975 : Blo 872567 875975 := bstep (se 1 (by rfl) ⟨656981, by rfl⟩ : syracuseStep 875975 = 1313963) B1313963
theorem B875995 : Blo 872567 875995 := bstep (se 1 (by rfl) ⟨656996, by rfl⟩ : syracuseStep 875995 = 1313993) B1313993
theorem B876071 : Blo 872567 876071 := bstep (se 1 (by rfl) ⟨657053, by rfl⟩ : syracuseStep 876071 = 1314107) B1314107
theorem B876111 : Blo 872567 876111 := bstep (se 1 (by rfl) ⟨657083, by rfl⟩ : syracuseStep 876111 = 1314167) B1314167
theorem B876127 : Blo 872567 876127 := bstep (se 1 (by rfl) ⟨657095, by rfl⟩ : syracuseStep 876127 = 1314191) B1314191
theorem B876155 : Blo 872567 876155 := bstep (se 1 (by rfl) ⟨657116, by rfl⟩ : syracuseStep 876155 = 1314233) B1314233
theorem B876207 : Blo 872567 876207 := bstep (se 1 (by rfl) ⟨657155, by rfl⟩ : syracuseStep 876207 = 1314311) B1314311
theorem B876231 : Blo 872567 876231 := bstep (se 1 (by rfl) ⟨657173, by rfl⟩ : syracuseStep 876231 = 1314347) B1314347
theorem B876251 : Blo 872567 876251 := bstep (se 1 (by rfl) ⟨657188, by rfl⟩ : syracuseStep 876251 = 1314377) B1314377
theorem B876327 : Blo 872567 876327 := bstep (se 1 (by rfl) ⟨657245, by rfl⟩ : syracuseStep 876327 = 1314491) B1314491
theorem B876367 : Blo 872567 876367 := bstep (se 1 (by rfl) ⟨657275, by rfl⟩ : syracuseStep 876367 = 1314551) B1314551
theorem B1400671 : Blo 872567 1400671 := bstep (se 1 (by rfl) ⟨1050503, by rfl⟩ : syracuseStep 1400671 = 2101007) B2101007
theorem B876383 : Blo 872567 876383 := bstep (se 1 (by rfl) ⟨657287, by rfl⟩ : syracuseStep 876383 = 1314575) B1314575
theorem B876411 : Blo 872567 876411 := bstep (se 1 (by rfl) ⟨657308, by rfl⟩ : syracuseStep 876411 = 1314617) B1314617
theorem B876463 : Blo 872567 876463 := bstep (se 1 (by rfl) ⟨657347, by rfl⟩ : syracuseStep 876463 = 1314695) B1314695
theorem B876487 : Blo 872567 876487 := bstep (se 1 (by rfl) ⟨657365, by rfl⟩ : syracuseStep 876487 = 1314731) B1314731
theorem B876507 : Blo 872567 876507 := bstep (se 1 (by rfl) ⟨657380, by rfl⟩ : syracuseStep 876507 = 1314761) B1314761
theorem B3727367 : Blo 872567 3727367 := bstep (se 1 (by rfl) ⟨2795525, by rfl⟩ : syracuseStep 3727367 = 5591051) B5591051
theorem B35971913 : Blo 872567 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B51045299 : Blo 872567 51045299 := bstep (se 1 (by rfl) ⟨38283974, by rfl⟩ : syracuseStep 51045299 = 76567949) B76567949
theorem B14967827 : Blo 872567 14967827 := bstep (se 1 (by rfl) ⟨11225870, by rfl⟩ : syracuseStep 14967827 = 22451741) B22451741
theorem B1664057 : Blo 872567 1664057 := bstep (se 2 (by rfl) ⟨624021, by rfl⟩ : syracuseStep 1664057 = 1248043) B1248043
theorem B3368429 : Blo 872567 3368429 := bstep (se 3 (by rfl) ⟨631580, by rfl⟩ : syracuseStep 3368429 = 1263161) B1263161
theorem B3991187 : Blo 872567 3991187 := bstep (se 1 (by rfl) ⟨2993390, by rfl⟩ : syracuseStep 3991187 = 5986781) B5986781
theorem B6317783 : Blo 872567 6317783 := bstep (se 1 (by rfl) ⟨4738337, by rfl⟩ : syracuseStep 6317783 = 9476675) B9476675
theorem B6645563 : Blo 872567 6645563 := bstep (se 1 (by rfl) ⟨4984172, by rfl⟩ : syracuseStep 6645563 = 9968345) B9968345
theorem B3598415 : Blo 872567 3598415 := bstep (se 1 (by rfl) ⟨2698811, by rfl⟩ : syracuseStep 3598415 = 5397623) B5397623
theorem B3729725 : Blo 872567 3729725 := bstep (se 3 (by rfl) ⟨699323, by rfl⟩ : syracuseStep 3729725 = 1398647) B1398647
theorem B1108399 : Blo 872567 1108399 := bstep (se 1 (by rfl) ⟨831299, by rfl⟩ : syracuseStep 1108399 = 1662599) B1662599
theorem B1403401 : Blo 872567 1403401 := bstep (se 2 (by rfl) ⟨526275, by rfl⟩ : syracuseStep 1403401 = 1052551) B1052551
theorem B4975289 : Blo 872567 4975289 := bstep (se 2 (by rfl) ⟨1865733, by rfl⟩ : syracuseStep 4975289 = 3731467) B3731467
theorem B1403639 : Blo 872567 1403639 := bstep (se 1 (by rfl) ⟨1052729, by rfl⟩ : syracuseStep 1403639 = 2105459) B2105459
theorem B5598173 : Blo 872567 5598173 := bstep (se 3 (by rfl) ⟨1049657, by rfl⟩ : syracuseStep 5598173 = 2099315) B2099315
theorem B4419035 : Blo 872567 4419035 := bstep (se 1 (by rfl) ⟨3314276, by rfl⟩ : syracuseStep 4419035 = 6628553) B6628553
theorem B2485799 : Blo 872567 2485799 := bstep (se 1 (by rfl) ⟨1864349, by rfl⟩ : syracuseStep 2485799 = 3728699) B3728699
theorem B4484753 : Blo 872567 4484753 := bstep (se 2 (by rfl) ⟨1681782, by rfl⟩ : syracuseStep 4484753 = 3363565) B3363565
theorem B3731143 : Blo 872567 3731143 := bstep (se 1 (by rfl) ⟨2798357, by rfl⟩ : syracuseStep 3731143 = 5596715) B5596715
theorem B3731159 : Blo 872567 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B2944943 : Blo 872567 2944943 := bstep (se 1 (by rfl) ⟨2208707, by rfl⟩ : syracuseStep 2944943 = 4417415) B4417415
theorem B4419521 : Blo 872567 4419521 := bstep (se 2 (by rfl) ⟨1657320, by rfl⟩ : syracuseStep 4419521 = 3314641) B3314641
theorem B28340239 : Blo 872567 28340239 := bstep (se 1 (by rfl) ⟨21255179, by rfl⟩ : syracuseStep 28340239 = 42510359) B42510359
theorem B12611699 : Blo 872567 12611699 := bstep (se 1 (by rfl) ⟨9458774, by rfl⟩ : syracuseStep 12611699 = 18917549) B18917549
theorem B22737509 : Blo 872567 22737509 := bstep (se 4 (by rfl) ⟨2131641, by rfl⟩ : syracuseStep 22737509 = 4263283) B4263283
theorem B12120833 : Blo 872567 12120833 := bstep (se 2 (by rfl) ⟨4545312, by rfl⟩ : syracuseStep 12120833 = 9090625) B9090625
theorem B10646275 : Blo 872567 10646275 := bstep (se 1 (by rfl) ⟨7984706, by rfl⟩ : syracuseStep 10646275 = 15969413) B15969413
theorem B10777519 : Blo 872567 10777519 := bstep (se 1 (by rfl) ⟨8083139, by rfl⟩ : syracuseStep 10777519 = 16166279) B16166279
theorem B96859223 : Blo 872567 96859223 := bstep (se 1 (by rfl) ⟨72644417, by rfl⟩ : syracuseStep 96859223 = 145288835) B145288835
theorem B17986931 : Blo 872567 17986931 := bstep (se 1 (by rfl) ⟨13490198, by rfl⟩ : syracuseStep 17986931 = 26980397) B26980397
theorem B28407185 : Blo 872567 28407185 := bstep (se 2 (by rfl) ⟨10652694, by rfl⟩ : syracuseStep 28407185 = 21305389) B21305389
theorem B12776869 : Blo 872567 12776869 := bstep (se 4 (by rfl) ⟨1197831, by rfl⟩ : syracuseStep 12776869 = 2395663) B2395663
theorem B1963529 : Blo 872567 1963529 := bstep (se 2 (by rfl) ⟨736323, by rfl⟩ : syracuseStep 1963529 = 1472647) B1472647
theorem B11204243 : Blo 872567 11204243 := bstep (se 1 (by rfl) ⟨8403182, by rfl⟩ : syracuseStep 11204243 = 16806365) B16806365
theorem B3405523 : Blo 872567 3405523 := bstep (se 1 (by rfl) ⟨2554142, by rfl⟩ : syracuseStep 3405523 = 5108285) B5108285
theorem B1963871 : Blo 872567 1963871 := bstep (se 1 (by rfl) ⟨1472903, by rfl⟩ : syracuseStep 1963871 = 2945807) B2945807
theorem B1472519 : Blo 872567 1472519 := bstep (se 1 (by rfl) ⟨1104389, by rfl⟩ : syracuseStep 1472519 = 2208779) B2208779
theorem B1964051 : Blo 872567 1964051 := bstep (se 1 (by rfl) ⟨1473038, by rfl⟩ : syracuseStep 1964051 = 2946077) B2946077
theorem B6649937 : Blo 872567 6649937 := bstep (se 2 (by rfl) ⟨2493726, by rfl⟩ : syracuseStep 6649937 = 4987453) B4987453
theorem B4421789 : Blo 872567 4421789 := bstep (se 3 (by rfl) ⟨829085, by rfl⟩ : syracuseStep 4421789 = 1658171) B1658171
theorem B2947319 : Blo 872567 2947319 := bstep (se 1 (by rfl) ⟨2210489, by rfl⟩ : syracuseStep 2947319 = 4420979) B4420979
theorem B7076107 : Blo 872567 7076107 := bstep (se 1 (by rfl) ⟨5307080, by rfl⟩ : syracuseStep 7076107 = 10614161) B10614161
theorem B1472863 : Blo 872567 1472863 := bstep (se 1 (by rfl) ⟨1104647, by rfl⟩ : syracuseStep 1472863 = 2209295) B2209295
theorem B1964393 : Blo 872567 1964393 := bstep (se 2 (by rfl) ⟨736647, by rfl⟩ : syracuseStep 1964393 = 1473295) B1473295
theorem B1309103 : Blo 872567 1309103 := bstep (se 1 (by rfl) ⟨981827, by rfl⟩ : syracuseStep 1309103 = 1963655) B1963655
theorem B1472951 : Blo 872567 1472951 := bstep (se 1 (by rfl) ⟨1104713, by rfl⟩ : syracuseStep 1472951 = 2209427) B2209427
theorem B5994989 : Blo 872567 5994989 := bstep (se 3 (by rfl) ⟨1124060, by rfl⟩ : syracuseStep 5994989 = 2248121) B2248121
theorem B1309193 : Blo 872567 1309193 := bstep (se 2 (by rfl) ⟨490947, by rfl⟩ : syracuseStep 1309193 = 981895) B981895
theorem B1309223 : Blo 872567 1309223 := bstep (se 1 (by rfl) ⟨981917, by rfl⟩ : syracuseStep 1309223 = 1963835) B1963835
theorem B2947643 : Blo 872567 2947643 := bstep (se 1 (by rfl) ⟨2210732, by rfl⟩ : syracuseStep 2947643 = 4421465) B4421465
theorem B1309307 : Blo 872567 1309307 := bstep (se 1 (by rfl) ⟨981980, by rfl⟩ : syracuseStep 1309307 = 1963961) B1963961
theorem B3734201 : Blo 872567 3734201 := bstep (se 2 (by rfl) ⟨1400325, by rfl⟩ : syracuseStep 3734201 = 2800651) B2800651
theorem B1309433 : Blo 872567 1309433 := bstep (se 2 (by rfl) ⟨491037, by rfl⟩ : syracuseStep 1309433 = 982075) B982075
theorem B2947913 : Blo 872567 2947913 := bstep (se 2 (by rfl) ⟨1105467, by rfl⟩ : syracuseStep 2947913 = 2210935) B2210935
theorem B1309535 : Blo 872567 1309535 := bstep (se 1 (by rfl) ⟨982151, by rfl⟩ : syracuseStep 1309535 = 1964303) B1964303
theorem B1309547 : Blo 872567 1309547 := bstep (se 1 (by rfl) ⟨982160, by rfl⟩ : syracuseStep 1309547 = 1964321) B1964321
theorem B4488119 : Blo 872567 4488119 := bstep (se 1 (by rfl) ⟨3366089, by rfl⟩ : syracuseStep 4488119 = 6732179) B6732179
theorem B1964987 : Blo 872567 1964987 := bstep (se 1 (by rfl) ⟨1473740, by rfl⟩ : syracuseStep 1964987 = 2947481) B2947481
theorem B1473545 : Blo 872567 1473545 := bstep (se 2 (by rfl) ⟨552579, by rfl⟩ : syracuseStep 1473545 = 1105159) B1105159
theorem B1965113 : Blo 872567 1965113 := bstep (se 2 (by rfl) ⟨736917, by rfl⟩ : syracuseStep 1965113 = 1473835) B1473835
theorem B1309775 : Blo 872567 1309775 := bstep (se 1 (by rfl) ⟨982331, by rfl⟩ : syracuseStep 1309775 = 1964663) B1964663
theorem B1473707 : Blo 872567 1473707 := bstep (se 1 (by rfl) ⟨1105280, by rfl⟩ : syracuseStep 1473707 = 2210561) B2210561
theorem B1309895 : Blo 872567 1309895 := bstep (se 1 (by rfl) ⟨982421, by rfl⟩ : syracuseStep 1309895 = 1964843) B1964843
theorem B3538187 : Blo 872567 3538187 := bstep (se 1 (by rfl) ⟨2653640, by rfl⟩ : syracuseStep 3538187 = 5307281) B5307281
theorem B1310057 : Blo 872567 1310057 := bstep (se 2 (by rfl) ⟨491271, by rfl⟩ : syracuseStep 1310057 = 982543) B982543
theorem B1965455 : Blo 872567 1965455 := bstep (se 1 (by rfl) ⟨1474091, by rfl⟩ : syracuseStep 1965455 = 2948183) B2948183
theorem B4423085 : Blo 872567 4423085 := bstep (se 3 (by rfl) ⟨829328, by rfl⟩ : syracuseStep 4423085 = 1658657) B1658657
theorem B1310135 : Blo 872567 1310135 := bstep (se 1 (by rfl) ⟨982601, by rfl⟩ : syracuseStep 1310135 = 1965203) B1965203
theorem B1310171 : Blo 872567 1310171 := bstep (se 1 (by rfl) ⟨982628, by rfl⟩ : syracuseStep 1310171 = 1965257) B1965257
theorem B3145225 : Blo 872567 3145225 := bstep (se 2 (by rfl) ⟨1179459, by rfl⟩ : syracuseStep 3145225 = 2358919) B2358919
theorem B1474105 : Blo 872567 1474105 := bstep (se 2 (by rfl) ⟨552789, by rfl⟩ : syracuseStep 1474105 = 1105579) B1105579
theorem B982651 : Blo 872567 982651 := bstep (se 1 (by rfl) ⟨736988, by rfl⟩ : syracuseStep 982651 = 1473977) B1473977
theorem B2096779 : Blo 872567 2096779 := bstep (se 1 (by rfl) ⟨1572584, by rfl⟩ : syracuseStep 2096779 = 3145169) B3145169
theorem B1474247 : Blo 872567 1474247 := bstep (se 1 (by rfl) ⟨1105685, by rfl⟩ : syracuseStep 1474247 = 2211371) B2211371
theorem B1965779 : Blo 872567 1965779 := bstep (se 1 (by rfl) ⟨1474334, by rfl⟩ : syracuseStep 1965779 = 2948669) B2948669
theorem B2096855 : Blo 872567 2096855 := bstep (se 1 (by rfl) ⟨1572641, by rfl⟩ : syracuseStep 2096855 = 3145283) B3145283
theorem B2359135 : Blo 872567 2359135 := bstep (se 1 (by rfl) ⟨1769351, by rfl⟩ : syracuseStep 2359135 = 3538703) B3538703
theorem B1474409 : Blo 872567 1474409 := bstep (se 2 (by rfl) ⟨552903, by rfl⟩ : syracuseStep 1474409 = 1105807) B1105807
theorem B17956727 : Blo 872567 17956727 := bstep (se 1 (by rfl) ⟨13467545, by rfl⟩ : syracuseStep 17956727 = 26935091) B26935091
theorem B1310639 : Blo 872567 1310639 := bstep (se 1 (by rfl) ⟨982979, by rfl⟩ : syracuseStep 1310639 = 1965959) B1965959
theorem B2949047 : Blo 872567 2949047 := bstep (se 1 (by rfl) ⟨2211785, by rfl⟩ : syracuseStep 2949047 = 4423571) B4423571
theorem B1277915 : Blo 872567 1277915 := bstep (se 1 (by rfl) ⟨958436, by rfl⟩ : syracuseStep 1277915 = 1916873) B1916873
theorem B62357521 : Blo 872567 62357521 := bstep (se 2 (by rfl) ⟨23384070, by rfl⟩ : syracuseStep 62357521 = 46768141) B46768141
theorem B6717491 : Blo 872567 6717491 := bstep (se 1 (by rfl) ⟨5038118, by rfl⟩ : syracuseStep 6717491 = 10076237) B10076237
theorem B1310825 : Blo 872567 1310825 := bstep (se 2 (by rfl) ⟨491559, by rfl⟩ : syracuseStep 1310825 = 983119) B983119
theorem B983335 : Blo 872567 983335 := bstep (se 1 (by rfl) ⟨737501, by rfl⟩ : syracuseStep 983335 = 1475003) B1475003
theorem B1966409 : Blo 872567 1966409 := bstep (se 2 (by rfl) ⟨737403, by rfl⟩ : syracuseStep 1966409 = 1474807) B1474807
theorem B1966427 : Blo 872567 1966427 := bstep (se 1 (by rfl) ⟨1474820, by rfl⟩ : syracuseStep 1966427 = 2949641) B2949641
theorem B983407 : Blo 872567 983407 := bstep (se 1 (by rfl) ⟨737555, by rfl⟩ : syracuseStep 983407 = 1475111) B1475111
theorem B1868143 : Blo 872567 1868143 := bstep (se 1 (by rfl) ⟨1401107, by rfl⟩ : syracuseStep 1868143 = 2802215) B2802215
theorem B1311143 : Blo 872567 1311143 := bstep (se 1 (by rfl) ⟨983357, by rfl⟩ : syracuseStep 1311143 = 1966715) B1966715
theorem B1311227 : Blo 872567 1311227 := bstep (se 1 (by rfl) ⟨983420, by rfl⟩ : syracuseStep 1311227 = 1966841) B1966841
theorem B983623 : Blo 872567 983623 := bstep (se 1 (by rfl) ⟨737717, by rfl⟩ : syracuseStep 983623 = 1475435) B1475435
theorem B1311353 : Blo 872567 1311353 := bstep (se 2 (by rfl) ⟨491757, by rfl⟩ : syracuseStep 1311353 = 983515) B983515
theorem B2949803 : Blo 872567 2949803 := bstep (se 1 (by rfl) ⟨2212352, by rfl⟩ : syracuseStep 2949803 = 4424705) B4424705
theorem B1311407 : Blo 872567 1311407 := bstep (se 1 (by rfl) ⟨983555, by rfl⟩ : syracuseStep 1311407 = 1967111) B1967111
theorem B4719307 : Blo 872567 4719307 := bstep (se 1 (by rfl) ⟨3539480, by rfl⟩ : syracuseStep 4719307 = 7078961) B7078961
theorem B1311455 : Blo 872567 1311455 := bstep (se 1 (by rfl) ⟨983591, by rfl⟩ : syracuseStep 1311455 = 1967183) B1967183
theorem B4424543 : Blo 872567 4424543 := bstep (se 1 (by rfl) ⟨3318407, by rfl⟩ : syracuseStep 4424543 = 6636815) B6636815
theorem B1967003 : Blo 872567 1967003 := bstep (se 1 (by rfl) ⟨1475252, by rfl⟩ : syracuseStep 1967003 = 2950505) B2950505
theorem B1311719 : Blo 872567 1311719 := bstep (se 1 (by rfl) ⟨983789, by rfl⟩ : syracuseStep 1311719 = 1967579) B1967579
theorem B2098163 : Blo 872567 2098163 := bstep (se 1 (by rfl) ⟨1573622, by rfl⟩ : syracuseStep 2098163 = 3147245) B3147245
theorem B4195385 : Blo 872567 4195385 := bstep (se 2 (by rfl) ⟨1573269, by rfl⟩ : syracuseStep 4195385 = 3146539) B3146539
theorem B1967201 : Blo 872567 1967201 := bstep (se 2 (by rfl) ⟨737700, by rfl⟩ : syracuseStep 1967201 = 1475401) B1475401
theorem B3540115 : Blo 872567 3540115 := bstep (se 1 (by rfl) ⟨2655086, by rfl⟩ : syracuseStep 3540115 = 5310173) B5310173
theorem B2950343 : Blo 872567 2950343 := bstep (se 1 (by rfl) ⟨2212757, by rfl⟩ : syracuseStep 2950343 = 4425515) B4425515
theorem B1311977 : Blo 872567 1311977 := bstep (se 2 (by rfl) ⟨491991, by rfl⟩ : syracuseStep 1311977 = 983983) B983983
theorem B1312031 : Blo 872567 1312031 := bstep (se 1 (by rfl) ⟨984023, by rfl⟩ : syracuseStep 1312031 = 1968047) B1968047
theorem B1967399 : Blo 872567 1967399 := bstep (se 1 (by rfl) ⟨1475549, by rfl⟩ : syracuseStep 1967399 = 2951099) B2951099
theorem B1869151 : Blo 872567 1869151 := bstep (se 1 (by rfl) ⟨1401863, by rfl⟩ : syracuseStep 1869151 = 2803727) B2803727
theorem B984487 : Blo 872567 984487 := bstep (se 1 (by rfl) ⟨738365, by rfl⟩ : syracuseStep 984487 = 1476731) B1476731
theorem B1312199 : Blo 872567 1312199 := bstep (se 1 (by rfl) ⟨984149, by rfl⟩ : syracuseStep 1312199 = 1968299) B1968299
theorem B1771103 : Blo 872567 1771103 := bstep (se 1 (by rfl) ⟨1328327, by rfl⟩ : syracuseStep 1771103 = 2656655) B2656655
theorem B1476191 : Blo 872567 1476191 := bstep (se 1 (by rfl) ⟨1107143, by rfl⟩ : syracuseStep 1476191 = 2214287) B2214287
theorem B1869407 : Blo 872567 1869407 := bstep (se 1 (by rfl) ⟨1402055, by rfl⟩ : syracuseStep 1869407 = 2804111) B2804111
theorem B1967777 : Blo 872567 1967777 := bstep (se 2 (by rfl) ⟨737916, by rfl⟩ : syracuseStep 1967777 = 1475833) B1475833
theorem B1312553 : Blo 872567 1312553 := bstep (se 2 (by rfl) ⟨492207, by rfl⟩ : syracuseStep 1312553 = 984415) B984415
theorem B1312559 : Blo 872567 1312559 := bstep (se 1 (by rfl) ⟨984419, by rfl⟩ : syracuseStep 1312559 = 1968839) B1968839
theorem B1247023 : Blo 872567 1247023 := bstep (se 1 (by rfl) ⟨935267, by rfl⟩ : syracuseStep 1247023 = 1870535) B1870535
theorem B1476407 : Blo 872567 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B17926019 : Blo 872567 17926019 := bstep (se 1 (by rfl) ⟨13444514, by rfl⟩ : syracuseStep 17926019 = 26889029) B26889029
theorem B985063 : Blo 872567 985063 := bstep (se 1 (by rfl) ⟨738797, by rfl⟩ : syracuseStep 985063 = 1477595) B1477595
theorem B1968137 : Blo 872567 1968137 := bstep (se 2 (by rfl) ⟨738051, by rfl⟩ : syracuseStep 1968137 = 1476103) B1476103
theorem B8521805 : Blo 872567 8521805 := bstep (se 3 (by rfl) ⟨1597838, by rfl⟩ : syracuseStep 8521805 = 3195677) B3195677
theorem B1313033 : Blo 872567 1313033 := bstep (se 2 (by rfl) ⟨492387, by rfl⟩ : syracuseStep 1313033 = 984775) B984775
theorem B1313135 : Blo 872567 1313135 := bstep (se 1 (by rfl) ⟨984851, by rfl⟩ : syracuseStep 1313135 = 1969703) B1969703
theorem B9079183 : Blo 872567 9079183 := bstep (se 1 (by rfl) ⟨6809387, by rfl⟩ : syracuseStep 9079183 = 13618775) B13618775
theorem B2099623 : Blo 872567 2099623 := bstep (se 1 (by rfl) ⟨1574717, by rfl⟩ : syracuseStep 2099623 = 3149435) B3149435
theorem B1968551 : Blo 872567 1968551 := bstep (se 1 (by rfl) ⟨1476413, by rfl⟩ : syracuseStep 1968551 = 2952827) B2952827
theorem B1968659 : Blo 872567 1968659 := bstep (se 1 (by rfl) ⟨1476494, by rfl⟩ : syracuseStep 1968659 = 2952989) B2952989
theorem B1477183 : Blo 872567 1477183 := bstep (se 1 (by rfl) ⟨1107887, by rfl⟩ : syracuseStep 1477183 = 2215775) B2215775
theorem B1313351 : Blo 872567 1313351 := bstep (se 1 (by rfl) ⟨985013, by rfl⟩ : syracuseStep 1313351 = 1970027) B1970027
theorem B1247815 : Blo 872567 1247815 := bstep (se 1 (by rfl) ⟨935861, by rfl⟩ : syracuseStep 1247815 = 1871723) B1871723
theorem B1968713 : Blo 872567 1968713 := bstep (se 2 (by rfl) ⟨738267, by rfl⟩ : syracuseStep 1968713 = 1476535) B1476535
theorem B1313387 : Blo 872567 1313387 := bstep (se 1 (by rfl) ⟨985040, by rfl⟩ : syracuseStep 1313387 = 1970081) B1970081
theorem B3738251 : Blo 872567 3738251 := bstep (se 1 (by rfl) ⟨2803688, by rfl⟩ : syracuseStep 3738251 = 5607377) B5607377
theorem B2951855 : Blo 872567 2951855 := bstep (se 1 (by rfl) ⟨2213891, by rfl⟩ : syracuseStep 2951855 = 4427783) B4427783
theorem B4426487 : Blo 872567 4426487 := bstep (se 1 (by rfl) ⟨3319865, by rfl⟩ : syracuseStep 4426487 = 6639731) B6639731
theorem B1313615 : Blo 872567 1313615 := bstep (se 1 (by rfl) ⟨985211, by rfl⟩ : syracuseStep 1313615 = 1970423) B1970423
theorem B1969127 : Blo 872567 1969127 := bstep (se 1 (by rfl) ⟨1476845, by rfl⟩ : syracuseStep 1969127 = 2953691) B2953691
theorem B2952179 : Blo 872567 2952179 := bstep (se 1 (by rfl) ⟨2214134, by rfl⟩ : syracuseStep 2952179 = 4428269) B4428269
theorem B7081037 : Blo 872567 7081037 := bstep (se 3 (by rfl) ⟨1327694, by rfl⟩ : syracuseStep 7081037 = 2655389) B2655389
theorem B1871047 : Blo 872567 1871047 := bstep (se 1 (by rfl) ⟨1403285, by rfl⟩ : syracuseStep 1871047 = 2806571) B2806571
theorem B2493659 : Blo 872567 2493659 := bstep (se 1 (by rfl) ⟨1870244, by rfl⟩ : syracuseStep 2493659 = 3740489) B3740489
theorem B1314011 : Blo 872567 1314011 := bstep (se 1 (by rfl) ⟨985508, by rfl⟩ : syracuseStep 1314011 = 1971017) B1971017
theorem B4426973 : Blo 872567 4426973 := bstep (se 3 (by rfl) ⟨830057, by rfl⟩ : syracuseStep 4426973 = 1660115) B1660115
theorem B1477865 : Blo 872567 1477865 := bstep (se 2 (by rfl) ⟨554199, by rfl⟩ : syracuseStep 1477865 = 1108399) B1108399
theorem B1477919 : Blo 872567 1477919 := bstep (se 1 (by rfl) ⟨1108439, by rfl⟩ : syracuseStep 1477919 = 2216879) B2216879
theorem B1969505 : Blo 872567 1969505 := bstep (se 2 (by rfl) ⟨738564, by rfl⟩ : syracuseStep 1969505 = 1477129) B1477129
theorem B1871201 : Blo 872567 1871201 := bstep (se 2 (by rfl) ⟨701700, by rfl⟩ : syracuseStep 1871201 = 1403401) B1403401
theorem B51088765 : Blo 872567 51088765 := bstep (se 3 (by rfl) ⟨9579143, by rfl⟩ : syracuseStep 51088765 = 19158287) B19158287
theorem B1314185 : Blo 872567 1314185 := bstep (se 2 (by rfl) ⟨492819, by rfl⟩ : syracuseStep 1314185 = 985639) B985639
theorem B7474619 : Blo 872567 7474619 := bstep (se 1 (by rfl) ⟨5605964, by rfl⟩ : syracuseStep 7474619 = 11211929) B11211929
theorem B1969595 : Blo 872567 1969595 := bstep (se 1 (by rfl) ⟨1477196, by rfl⟩ : syracuseStep 1969595 = 2954393) B2954393
theorem B2952719 : Blo 872567 2952719 := bstep (se 1 (by rfl) ⟨2214539, by rfl⟩ : syracuseStep 2952719 = 4429079) B4429079
theorem B1969721 : Blo 872567 1969721 := bstep (se 2 (by rfl) ⟨738645, by rfl⟩ : syracuseStep 1969721 = 1477291) B1477291
theorem B22744709 : Blo 872567 22744709 := bstep (se 4 (by rfl) ⟨2132316, by rfl⟩ : syracuseStep 22744709 = 4264633) B4264633
theorem B1314539 : Blo 872567 1314539 := bstep (se 1 (by rfl) ⟨985904, by rfl⟩ : syracuseStep 1314539 = 1971809) B1971809
theorem B3149725 : Blo 872567 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B1314767 : Blo 872567 1314767 := bstep (se 1 (by rfl) ⟨986075, by rfl⟩ : syracuseStep 1314767 = 1972151) B1972151
theorem B1970387 : Blo 872567 1970387 := bstep (se 1 (by rfl) ⟨1477790, by rfl⟩ : syracuseStep 1970387 = 2955581) B2955581
theorem B1970441 : Blo 872567 1970441 := bstep (se 2 (by rfl) ⟨738915, by rfl⟩ : syracuseStep 1970441 = 1477831) B1477831
theorem B1773991 : Blo 872567 1773991 := bstep (se 1 (by rfl) ⟨1330493, by rfl⟩ : syracuseStep 1773991 = 2660987) B2660987
theorem B1970657 : Blo 872567 1970657 := bstep (se 2 (by rfl) ⟨738996, by rfl⟩ : syracuseStep 1970657 = 1477993) B1477993
theorem B2953799 : Blo 872567 2953799 := bstep (se 1 (by rfl) ⟨2215349, by rfl⟩ : syracuseStep 2953799 = 4430699) B4430699
theorem B1184363 : Blo 872567 1184363 := bstep (se 1 (by rfl) ⟨888272, by rfl⟩ : syracuseStep 1184363 = 1776545) B1776545
theorem B1970963 : Blo 872567 1970963 := bstep (se 1 (by rfl) ⟨1478222, by rfl⟩ : syracuseStep 1970963 = 2956445) B2956445
theorem B57480101 : Blo 872567 57480101 := bstep (se 4 (by rfl) ⟨5388759, by rfl⟩ : syracuseStep 57480101 = 10777519) B10777519
theorem B3314627 : Blo 872567 3314627 := bstep (se 1 (by rfl) ⟨2485970, by rfl⟩ : syracuseStep 3314627 = 4971941) B4971941
theorem B2954231 : Blo 872567 2954231 := bstep (se 1 (by rfl) ⟨2215673, by rfl⟩ : syracuseStep 2954231 = 4431347) B4431347
theorem B2364455 : Blo 872567 2364455 := bstep (se 1 (by rfl) ⟨1773341, by rfl⟩ : syracuseStep 2364455 = 3546683) B3546683
theorem B1971323 : Blo 872567 1971323 := bstep (se 1 (by rfl) ⟨1478492, by rfl⟩ : syracuseStep 1971323 = 2956985) B2956985
theorem B12588281 : Blo 872567 12588281 := bstep (se 2 (by rfl) ⟨4720605, by rfl⟩ : syracuseStep 12588281 = 9441211) B9441211
theorem B1971449 : Blo 872567 1971449 := bstep (se 2 (by rfl) ⟨739293, by rfl⟩ : syracuseStep 1971449 = 1478587) B1478587
theorem B9966887 : Blo 872567 9966887 := bstep (se 1 (by rfl) ⟨7475165, by rfl⟩ : syracuseStep 9966887 = 14950331) B14950331
theorem B37786985 : Blo 872567 37786985 := bstep (se 2 (by rfl) ⟨14170119, by rfl⟩ : syracuseStep 37786985 = 28340239) B28340239
theorem B1971593 : Blo 872567 1971593 := bstep (se 2 (by rfl) ⟨739347, by rfl⟩ : syracuseStep 1971593 = 1478695) B1478695
theorem B1971719 : Blo 872567 1971719 := bstep (se 1 (by rfl) ⟨1478789, by rfl⟩ : syracuseStep 1971719 = 2957579) B2957579
theorem B1971899 : Blo 872567 1971899 := bstep (se 1 (by rfl) ⟨1478924, by rfl⟩ : syracuseStep 1971899 = 2957849) B2957849
theorem B5609245 : Blo 872567 5609245 := bstep (se 3 (by rfl) ⟨1051733, by rfl⟩ : syracuseStep 5609245 = 2103467) B2103467
theorem B1775417 : Blo 872567 1775417 := bstep (se 2 (by rfl) ⟨665781, by rfl⟩ : syracuseStep 1775417 = 1331563) B1331563
theorem B1972025 : Blo 872567 1972025 := bstep (se 2 (by rfl) ⟨739509, by rfl⟩ : syracuseStep 1972025 = 1479019) B1479019
theorem B2955095 : Blo 872567 2955095 := bstep (se 1 (by rfl) ⟨2216321, by rfl⟩ : syracuseStep 2955095 = 4432643) B4432643
theorem B14195033 : Blo 872567 14195033 := bstep (se 2 (by rfl) ⟨5323137, by rfl⟩ : syracuseStep 14195033 = 10646275) B10646275
theorem B2660791 : Blo 872567 2660791 := bstep (se 1 (by rfl) ⟨1995593, by rfl⟩ : syracuseStep 2660791 = 3991187) B3991187
theorem B3742163 : Blo 872567 3742163 := bstep (se 1 (by rfl) ⟨2806622, by rfl⟩ : syracuseStep 3742163 = 5613245) B5613245
theorem B4430375 : Blo 872567 4430375 := bstep (se 1 (by rfl) ⟨3322781, by rfl⟩ : syracuseStep 4430375 = 6645563) B6645563
theorem B2398943 : Blo 872567 2398943 := bstep (se 1 (by rfl) ⟨1799207, by rfl⟩ : syracuseStep 2398943 = 3598415) B3598415
theorem B2956175 : Blo 872567 2956175 := bstep (se 1 (by rfl) ⟨2217131, by rfl⟩ : syracuseStep 2956175 = 4434263) B4434263
theorem B3316859 : Blo 872567 3316859 := bstep (se 1 (by rfl) ⟨2487644, by rfl⟩ : syracuseStep 3316859 = 4975289) B4975289
theorem B2104775 : Blo 872567 2104775 := bstep (se 1 (by rfl) ⟨1578581, by rfl⟩ : syracuseStep 2104775 = 3157163) B3157163
theorem B2989835 : Blo 872567 2989835 := bstep (se 1 (by rfl) ⟨2242376, by rfl⟩ : syracuseStep 2989835 = 4484753) B4484753
theorem B4792121 : Blo 872567 4792121 := bstep (se 2 (by rfl) ⟨1797045, by rfl⟩ : syracuseStep 4792121 = 3594091) B3594091
theorem B2662301 : Blo 872567 2662301 := bstep (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) B998363
theorem B2957417 : Blo 872567 2957417 := bstep (se 2 (by rfl) ⟨1109031, by rfl⟩ : syracuseStep 2957417 = 2218063) B2218063
theorem B2105851 : Blo 872567 2105851 := bstep (se 1 (by rfl) ⟨1579388, by rfl⟩ : syracuseStep 2105851 = 3158777) B3158777
theorem B4432481 : Blo 872567 4432481 := bstep (se 2 (by rfl) ⟨1662180, by rfl⟩ : syracuseStep 4432481 = 3324361) B3324361
theorem B2368381 : Blo 872567 2368381 := bstep (se 3 (by rfl) ⟨444071, by rfl⟩ : syracuseStep 2368381 = 888143) B888143
theorem B2958281 : Blo 872567 2958281 := bstep (se 2 (by rfl) ⟨1109355, by rfl⟩ : syracuseStep 2958281 = 2218711) B2218711
theorem B4433129 : Blo 872567 4433129 := bstep (se 2 (by rfl) ⟨1662423, by rfl⟩ : syracuseStep 4433129 = 3324847) B3324847
theorem B4433291 : Blo 872567 4433291 := bstep (se 1 (by rfl) ⟨3324968, by rfl⟩ : syracuseStep 4433291 = 6649937) B6649937
theorem B121185679 : Blo 872567 121185679 := bstep (se 1 (by rfl) ⟨90889259, by rfl⟩ : syracuseStep 121185679 = 181778519) B181778519
theorem B8398799 : Blo 872567 8398799 := bstep (se 1 (by rfl) ⟨6299099, by rfl⟩ : syracuseStep 8398799 = 12598199) B12598199
theorem B2992079 : Blo 872567 2992079 := bstep (se 1 (by rfl) ⟨2244059, by rfl⟩ : syracuseStep 2992079 = 4488119) B4488119
theorem B2795705 : Blo 872567 2795705 := bstep (se 2 (by rfl) ⟨1048389, by rfl⟩ : syracuseStep 2795705 = 2096779) B2096779
theorem B11971151 : Blo 872567 11971151 := bstep (se 1 (by rfl) ⟨8978363, by rfl⟩ : syracuseStep 11971151 = 17956727) B17956727
theorem B6630011 : Blo 872567 6630011 := bstep (se 1 (by rfl) ⟨4972508, by rfl⟩ : syracuseStep 6630011 = 9945017) B9945017
theorem B3320747 : Blo 872567 3320747 := bstep (se 1 (by rfl) ⟨2490560, by rfl⟩ : syracuseStep 3320747 = 4981121) B4981121
theorem B4206011 : Blo 872567 4206011 := bstep (se 1 (by rfl) ⟨3154508, by rfl⟩ : syracuseStep 4206011 = 6309017) B6309017
theorem B2797139 : Blo 872567 2797139 := bstep (se 1 (by rfl) ⟨2097854, by rfl⟩ : syracuseStep 2797139 = 4195709) B4195709
theorem B2273129 : Blo 872567 2273129 := bstep (se 2 (by rfl) ⟨852423, by rfl⟩ : syracuseStep 2273129 = 1704847) B1704847
theorem B71840033 : Blo 872567 71840033 := bstep (se 2 (by rfl) ⟨26940012, by rfl⟩ : syracuseStep 71840033 = 53880025) B53880025
theorem B8401259 : Blo 872567 8401259 := bstep (se 1 (by rfl) ⟨6300944, by rfl⟩ : syracuseStep 8401259 = 12601889) B12601889
theorem B6631955 : Blo 872567 6631955 := bstep (se 1 (by rfl) ⟨4973966, by rfl⟩ : syracuseStep 6631955 = 9947933) B9947933
theorem B4436531 : Blo 872567 4436531 := bstep (se 1 (by rfl) ⟨3327398, by rfl⟩ : syracuseStep 4436531 = 6654797) B6654797
theorem B36352817 : Blo 872567 36352817 := bstep (se 2 (by rfl) ⟨13632306, by rfl⟩ : syracuseStep 36352817 = 27264613) B27264613
theorem B3552455 : Blo 872567 3552455 := bstep (se 1 (by rfl) ⟨2664341, by rfl⟩ : syracuseStep 3552455 = 5328683) B5328683
theorem B2209801 : Blo 872567 2209801 := bstep (se 2 (by rfl) ⟨828675, by rfl⟩ : syracuseStep 2209801 = 1657351) B1657351
theorem B4733063 : Blo 872567 4733063 := bstep (se 1 (by rfl) ⟨3549797, by rfl⟩ : syracuseStep 4733063 = 7099595) B7099595
theorem B2242991 : Blo 872567 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B4733839 : Blo 872567 4733839 := bstep (se 1 (by rfl) ⟨3550379, by rfl⟩ : syracuseStep 4733839 = 7100759) B7100759
theorem B22756403 : Blo 872567 22756403 := bstep (se 1 (by rfl) ⟨17067302, by rfl⟩ : syracuseStep 22756403 = 34134605) B34134605
theorem B2211209 : Blo 872567 2211209 := bstep (se 2 (by rfl) ⟨829203, by rfl⟩ : syracuseStep 2211209 = 1658407) B1658407
theorem B2211259 : Blo 872567 2211259 := bstep (se 1 (by rfl) ⟨1658444, by rfl⟩ : syracuseStep 2211259 = 3316889) B3316889
theorem B7486991 : Blo 872567 7486991 := bstep (se 1 (by rfl) ⟨5615243, by rfl⟩ : syracuseStep 7486991 = 11230487) B11230487
theorem B6471191 : Blo 872567 6471191 := bstep (se 1 (by rfl) ⟨4853393, by rfl⟩ : syracuseStep 6471191 = 9706787) B9706787
theorem B2801267 : Blo 872567 2801267 := bstep (se 1 (by rfl) ⟨2100950, by rfl⟩ : syracuseStep 2801267 = 4201901) B4201901
theorem B2211563 : Blo 872567 2211563 := bstep (se 1 (by rfl) ⟨1658672, by rfl⟩ : syracuseStep 2211563 = 3317345) B3317345
theorem B2801537 : Blo 872567 2801537 := bstep (se 2 (by rfl) ⟨1050576, by rfl⟩ : syracuseStep 2801537 = 2101153) B2101153
theorem B4735397 : Blo 872567 4735397 := bstep (se 4 (by rfl) ⟨443943, by rfl⟩ : syracuseStep 4735397 = 887887) B887887
theorem B34030199 : Blo 872567 34030199 := bstep (se 1 (by rfl) ⟨25522649, by rfl⟩ : syracuseStep 34030199 = 51045299) B51045299
theorem B2212535 : Blo 872567 2212535 := bstep (se 1 (by rfl) ⟨1659401, by rfl⟩ : syracuseStep 2212535 = 3318803) B3318803
theorem B9978551 : Blo 872567 9978551 := bstep (se 1 (by rfl) ⟨7483913, by rfl⟩ : syracuseStep 9978551 = 14967827) B14967827
theorem B3588943 : Blo 872567 3588943 := bstep (se 1 (by rfl) ⟨2691707, by rfl⟩ : syracuseStep 3588943 = 5383415) B5383415
theorem B2245619 : Blo 872567 2245619 := bstep (se 1 (by rfl) ⟨1684214, by rfl⟩ : syracuseStep 2245619 = 3368429) B3368429
theorem B4211855 : Blo 872567 4211855 := bstep (se 1 (by rfl) ⟨3158891, by rfl⟩ : syracuseStep 4211855 = 6317783) B6317783
theorem B2213639 : Blo 872567 2213639 := bstep (se 1 (by rfl) ⟨1660229, by rfl⟩ : syracuseStep 2213639 = 3320459) B3320459
theorem B2213689 : Blo 872567 2213689 := bstep (se 2 (by rfl) ⟨830133, by rfl⟩ : syracuseStep 2213689 = 1660267) B1660267
theorem B935759 : Blo 872567 935759 := bstep (se 1 (by rfl) ⟨701819, by rfl⟩ : syracuseStep 935759 = 1403639) B1403639
theorem B2213993 : Blo 872567 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B4540697 : Blo 872567 4540697 := bstep (se 2 (by rfl) ⟨1702761, by rfl⟩ : syracuseStep 4540697 = 3405523) B3405523
theorem B2803997 : Blo 872567 2803997 := bstep (se 3 (by rfl) ⟨525749, by rfl⟩ : syracuseStep 2803997 = 1051499) B1051499
theorem B1657199 : Blo 872567 1657199 := bstep (se 1 (by rfl) ⟨1242899, by rfl⟩ : syracuseStep 1657199 = 2485799) B2485799
theorem B14928461 : Blo 872567 14928461 := bstep (se 3 (by rfl) ⟨2799086, by rfl⟩ : syracuseStep 14928461 = 5598173) B5598173
theorem B2214479 : Blo 872567 2214479 := bstep (se 1 (by rfl) ⟨1660859, by rfl⟩ : syracuseStep 2214479 = 3321719) B3321719
theorem B8407799 : Blo 872567 8407799 := bstep (se 1 (by rfl) ⟨6305849, by rfl⟩ : syracuseStep 8407799 = 12611699) B12611699
theorem B15158339 : Blo 872567 15158339 := bstep (se 1 (by rfl) ⟨11368754, by rfl⟩ : syracuseStep 15158339 = 22737509) B22737509
theorem B8080555 : Blo 872567 8080555 := bstep (se 1 (by rfl) ⟨6060416, by rfl⟩ : syracuseStep 8080555 = 12120833) B12120833
theorem B2215127 : Blo 872567 2215127 := bstep (se 1 (by rfl) ⟨1661345, by rfl⟩ : syracuseStep 2215127 = 3322691) B3322691
theorem B64572815 : Blo 872567 64572815 := bstep (se 1 (by rfl) ⟨48429611, by rfl⟩ : syracuseStep 64572815 = 96859223) B96859223
theorem B872735 : Blo 872567 872735 := bstep (se 1 (by rfl) ⟨654551, by rfl⟩ : syracuseStep 872735 = 1309103) B1309103
theorem B872795 : Blo 872567 872795 := bstep (se 1 (by rfl) ⟨654596, by rfl⟩ : syracuseStep 872795 = 1309193) B1309193
theorem B872815 : Blo 872567 872815 := bstep (se 1 (by rfl) ⟨654611, by rfl⟩ : syracuseStep 872815 = 1309223) B1309223
theorem B872871 : Blo 872567 872871 := bstep (se 1 (by rfl) ⟨654653, by rfl⟩ : syracuseStep 872871 = 1309307) B1309307
theorem B872955 : Blo 872567 872955 := bstep (se 1 (by rfl) ⟨654716, by rfl⟩ : syracuseStep 872955 = 1309433) B1309433
theorem B2216443 : Blo 872567 2216443 := bstep (se 1 (by rfl) ⟨1662332, by rfl⟩ : syracuseStep 2216443 = 3324665) B3324665
theorem B873023 : Blo 872567 873023 := bstep (se 1 (by rfl) ⟨654767, by rfl⟩ : syracuseStep 873023 = 1309535) B1309535
theorem B873031 : Blo 872567 873031 := bstep (se 1 (by rfl) ⟨654773, by rfl⟩ : syracuseStep 873031 = 1309547) B1309547
theorem B2216555 : Blo 872567 2216555 := bstep (se 1 (by rfl) ⟨1662416, by rfl⟩ : syracuseStep 2216555 = 3324833) B3324833
theorem B873183 : Blo 872567 873183 := bstep (se 1 (by rfl) ⟨654887, by rfl⟩ : syracuseStep 873183 = 1309775) B1309775
theorem B873263 : Blo 872567 873263 := bstep (se 1 (by rfl) ⟨654947, by rfl⟩ : syracuseStep 873263 = 1309895) B1309895
theorem B873371 : Blo 872567 873371 := bstep (se 1 (by rfl) ⟨655028, by rfl⟩ : syracuseStep 873371 = 1310057) B1310057
theorem B9982925 : Blo 872567 9982925 := bstep (se 3 (by rfl) ⟨1871798, by rfl⟩ : syracuseStep 9982925 = 3743597) B3743597
theorem B873423 : Blo 872567 873423 := bstep (se 1 (by rfl) ⟨655067, by rfl⟩ : syracuseStep 873423 = 1310135) B1310135
theorem B873447 : Blo 872567 873447 := bstep (se 1 (by rfl) ⟨655085, by rfl⟩ : syracuseStep 873447 = 1310171) B1310171
theorem B1397903 : Blo 872567 1397903 := bstep (se 1 (by rfl) ⟨1048427, by rfl⟩ : syracuseStep 1397903 = 2096855) B2096855
theorem B2217203 : Blo 872567 2217203 := bstep (se 1 (by rfl) ⟨1662902, by rfl⟩ : syracuseStep 2217203 = 3325805) B3325805
theorem B873759 : Blo 872567 873759 := bstep (se 1 (by rfl) ⟨655319, by rfl⟩ : syracuseStep 873759 = 1310639) B1310639
theorem B2807083 : Blo 872567 2807083 := bstep (se 1 (by rfl) ⟨2105312, by rfl⟩ : syracuseStep 2807083 = 4210625) B4210625
theorem B873819 : Blo 872567 873819 := bstep (se 1 (by rfl) ⟨655364, by rfl⟩ : syracuseStep 873819 = 1310729) B1310729
theorem B873839 : Blo 872567 873839 := bstep (se 1 (by rfl) ⟨655379, by rfl⟩ : syracuseStep 873839 = 1310759) B1310759
theorem B873895 : Blo 872567 873895 := bstep (se 1 (by rfl) ⟨655421, by rfl⟩ : syracuseStep 873895 = 1310843) B1310843
theorem B2217415 : Blo 872567 2217415 := bstep (se 1 (by rfl) ⟨1663061, by rfl⟩ : syracuseStep 2217415 = 3326123) B3326123
theorem B873979 : Blo 872567 873979 := bstep (se 1 (by rfl) ⟨655484, by rfl⟩ : syracuseStep 873979 = 1310969) B1310969
theorem B2840071 : Blo 872567 2840071 := bstep (se 1 (by rfl) ⟨2130053, by rfl⟩ : syracuseStep 2840071 = 4260107) B4260107
theorem B6641189 : Blo 872567 6641189 := bstep (se 4 (by rfl) ⟨622611, by rfl⟩ : syracuseStep 6641189 = 1245223) B1245223
theorem B874047 : Blo 872567 874047 := bstep (se 1 (by rfl) ⟨655535, by rfl⟩ : syracuseStep 874047 = 1311071) B1311071
theorem B874055 : Blo 872567 874055 := bstep (se 1 (by rfl) ⟨655541, by rfl⟩ : syracuseStep 874055 = 1311083) B1311083
theorem B874207 : Blo 872567 874207 := bstep (se 1 (by rfl) ⟨655655, by rfl⟩ : syracuseStep 874207 = 1311311) B1311311
theorem B874287 : Blo 872567 874287 := bstep (se 1 (by rfl) ⟨655715, by rfl⟩ : syracuseStep 874287 = 1311431) B1311431
theorem B1398583 : Blo 872567 1398583 := bstep (se 1 (by rfl) ⟨1048937, by rfl⟩ : syracuseStep 1398583 = 2097875) B2097875
theorem B874395 : Blo 872567 874395 := bstep (se 1 (by rfl) ⟨655796, by rfl⟩ : syracuseStep 874395 = 1311593) B1311593
theorem B874447 : Blo 872567 874447 := bstep (se 1 (by rfl) ⟨655835, by rfl⟩ : syracuseStep 874447 = 1311671) B1311671
theorem B874471 : Blo 872567 874471 := bstep (se 1 (by rfl) ⟨655853, by rfl⟩ : syracuseStep 874471 = 1311707) B1311707
theorem B874783 : Blo 872567 874783 := bstep (se 1 (by rfl) ⟨656087, by rfl⟩ : syracuseStep 874783 = 1312175) B1312175
theorem B874843 : Blo 872567 874843 := bstep (se 1 (by rfl) ⟨656132, by rfl⟩ : syracuseStep 874843 = 1312265) B1312265
theorem B874863 : Blo 872567 874863 := bstep (se 1 (by rfl) ⟨656147, by rfl⟩ : syracuseStep 874863 = 1312295) B1312295
theorem B874919 : Blo 872567 874919 := bstep (se 1 (by rfl) ⟨656189, by rfl⟩ : syracuseStep 874919 = 1312379) B1312379
theorem B875003 : Blo 872567 875003 := bstep (se 1 (by rfl) ⟨656252, by rfl⟩ : syracuseStep 875003 = 1312505) B1312505
theorem B875071 : Blo 872567 875071 := bstep (se 1 (by rfl) ⟨656303, by rfl⟩ : syracuseStep 875071 = 1312607) B1312607
theorem B1104455 : Blo 872567 1104455 := bstep (se 1 (by rfl) ⟨828341, by rfl⟩ : syracuseStep 1104455 = 1656683) B1656683
theorem B875079 : Blo 872567 875079 := bstep (se 1 (by rfl) ⟨656309, by rfl⟩ : syracuseStep 875079 = 1312619) B1312619
theorem B1399403 : Blo 872567 1399403 := bstep (se 1 (by rfl) ⟨1049552, by rfl⟩ : syracuseStep 1399403 = 2099105) B2099105
theorem B1104607 : Blo 872567 1104607 := bstep (se 1 (by rfl) ⟨828455, by rfl⟩ : syracuseStep 1104607 = 1656911) B1656911
theorem B875231 : Blo 872567 875231 := bstep (se 1 (by rfl) ⟨656423, by rfl⟩ : syracuseStep 875231 = 1312847) B1312847
theorem B875311 : Blo 872567 875311 := bstep (se 1 (by rfl) ⟨656483, by rfl⟩ : syracuseStep 875311 = 1312967) B1312967
theorem B875419 : Blo 872567 875419 := bstep (se 1 (by rfl) ⟨656564, by rfl⟩ : syracuseStep 875419 = 1313129) B1313129
theorem B875471 : Blo 872567 875471 := bstep (se 1 (by rfl) ⟨656603, by rfl⟩ : syracuseStep 875471 = 1313207) B1313207
theorem B875495 : Blo 872567 875495 := bstep (se 1 (by rfl) ⟨656621, by rfl⟩ : syracuseStep 875495 = 1313243) B1313243
theorem B875807 : Blo 872567 875807 := bstep (se 1 (by rfl) ⟨656855, by rfl⟩ : syracuseStep 875807 = 1313711) B1313711
theorem B875867 : Blo 872567 875867 := bstep (se 1 (by rfl) ⟨656900, by rfl⟩ : syracuseStep 875867 = 1313801) B1313801
theorem B875887 : Blo 872567 875887 := bstep (se 1 (by rfl) ⟨656915, by rfl⟩ : syracuseStep 875887 = 1313831) B1313831
theorem B875943 : Blo 872567 875943 := bstep (se 1 (by rfl) ⟨656957, by rfl⟩ : syracuseStep 875943 = 1313915) B1313915
theorem B876027 : Blo 872567 876027 := bstep (se 1 (by rfl) ⟨657020, by rfl⟩ : syracuseStep 876027 = 1314041) B1314041
theorem B876095 : Blo 872567 876095 := bstep (se 1 (by rfl) ⟨657071, by rfl⟩ : syracuseStep 876095 = 1314143) B1314143
theorem B876103 : Blo 872567 876103 := bstep (se 1 (by rfl) ⟨657077, by rfl⟩ : syracuseStep 876103 = 1314155) B1314155
theorem B8216225 : Blo 872567 8216225 := bstep (se 2 (by rfl) ⟨3081084, by rfl⟩ : syracuseStep 8216225 = 6162169) B6162169
theorem B876255 : Blo 872567 876255 := bstep (se 1 (by rfl) ⟨657191, by rfl⟩ : syracuseStep 876255 = 1314383) B1314383
theorem B876335 : Blo 872567 876335 := bstep (se 1 (by rfl) ⟨657251, by rfl⟩ : syracuseStep 876335 = 1314503) B1314503
theorem B876443 : Blo 872567 876443 := bstep (se 1 (by rfl) ⟨657332, by rfl⟩ : syracuseStep 876443 = 1314665) B1314665
theorem B876495 : Blo 872567 876495 := bstep (se 1 (by rfl) ⟨657371, by rfl⟩ : syracuseStep 876495 = 1314743) B1314743
theorem B876519 : Blo 872567 876519 := bstep (se 1 (by rfl) ⟨657389, by rfl⟩ : syracuseStep 876519 = 1314779) B1314779
theorem B11198807 : Blo 872567 11198807 := bstep (se 1 (by rfl) ⟨8399105, by rfl⟩ : syracuseStep 11198807 = 16798211) B16798211
theorem B5988833 : Blo 872567 5988833 := bstep (se 2 (by rfl) ⟨2245812, by rfl⟩ : syracuseStep 5988833 = 4491625) B4491625
theorem B5596123 : Blo 872567 5596123 := bstep (se 1 (by rfl) ⟨4197092, by rfl⟩ : syracuseStep 5596123 = 8394185) B8394185
theorem B3729655 : Blo 872567 3729655 := bstep (se 1 (by rfl) ⟨2797241, by rfl⟩ : syracuseStep 3729655 = 5594483) B5594483
theorem B8415485 : Blo 872567 8415485 := bstep (se 3 (by rfl) ⟨1577903, by rfl⟩ : syracuseStep 8415485 = 3155807) B3155807
theorem B4974857 : Blo 872567 4974857 := bstep (se 2 (by rfl) ⟨1865571, by rfl⟩ : syracuseStep 4974857 = 3731143) B3731143
theorem B16804361 : Blo 872567 16804361 := bstep (se 2 (by rfl) ⟨6301635, by rfl⟩ : syracuseStep 16804361 = 12603271) B12603271
theorem B2484911 : Blo 872567 2484911 := bstep (se 1 (by rfl) ⟨1863683, by rfl⟩ : syracuseStep 2484911 = 3727367) B3727367
theorem B23981275 : Blo 872567 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B1109371 : Blo 872567 1109371 := bstep (se 1 (by rfl) ⟨832028, by rfl⟩ : syracuseStep 1109371 = 1664057) B1664057
theorem B6647507 : Blo 872567 6647507 := bstep (se 1 (by rfl) ⟨4985630, by rfl⟩ : syracuseStep 6647507 = 9971261) B9971261
theorem B1994537 : Blo 872567 1994537 := bstep (se 2 (by rfl) ⟨747951, by rfl⟩ : syracuseStep 1994537 = 1495903) B1495903
theorem B57438001 : Blo 872567 57438001 := bstep (se 2 (by rfl) ⟨21539250, by rfl⟩ : syracuseStep 57438001 = 43078501) B43078501
theorem B27324533 : Blo 872567 27324533 := bstep (se 5 (by rfl) ⟨1280837, by rfl⟩ : syracuseStep 27324533 = 2561675) B2561675
theorem B2486483 : Blo 872567 2486483 := bstep (se 1 (by rfl) ⟨1864862, by rfl⟩ : syracuseStep 2486483 = 3729725) B3729725
theorem B2945537 : Blo 872567 2945537 := bstep (se 2 (by rfl) ⟨1104576, by rfl⟩ : syracuseStep 2945537 = 2209153) B2209153
theorem B17035825 : Blo 872567 17035825 := bstep (se 2 (by rfl) ⟨6388434, by rfl⟩ : syracuseStep 17035825 = 12776869) B12776869
theorem B8417945 : Blo 872567 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B1864367 : Blo 872567 1864367 := bstep (se 1 (by rfl) ⟨1398275, by rfl⟩ : syracuseStep 1864367 = 2796551) B2796551
theorem B3732425 : Blo 872567 3732425 := bstep (se 2 (by rfl) ⟨1399659, by rfl⟩ : syracuseStep 3732425 = 2799319) B2799319
theorem B2946023 : Blo 872567 2946023 := bstep (se 1 (by rfl) ⟨2209517, by rfl⟩ : syracuseStep 2946023 = 4419035) B4419035
theorem B2487439 : Blo 872567 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B1963295 : Blo 872567 1963295 := bstep (se 1 (by rfl) ⟨1472471, by rfl⟩ : syracuseStep 1963295 = 2944943) B2944943
theorem B2946347 : Blo 872567 2946347 := bstep (se 1 (by rfl) ⟨2209760, by rfl⟩ : syracuseStep 2946347 = 4419521) B4419521
theorem B2946617 : Blo 872567 2946617 := bstep (se 2 (by rfl) ⟨1104981, by rfl⟩ : syracuseStep 2946617 = 2209963) B2209963
theorem B9434809 : Blo 872567 9434809 := bstep (se 2 (by rfl) ⟨3538053, by rfl⟩ : syracuseStep 9434809 = 7076107) B7076107
theorem B1963817 : Blo 872567 1963817 := bstep (se 2 (by rfl) ⟨736431, by rfl⟩ : syracuseStep 1963817 = 1472863) B1472863
theorem B18708317 : Blo 872567 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B11991287 : Blo 872567 11991287 := bstep (se 1 (by rfl) ⟨8993465, by rfl⟩ : syracuseStep 11991287 = 17986931) B17986931
theorem B18938123 : Blo 872567 18938123 := bstep (se 1 (by rfl) ⟨14203592, by rfl⟩ : syracuseStep 18938123 = 28407185) B28407185
theorem B1309019 : Blo 872567 1309019 := bstep (se 1 (by rfl) ⟨981764, by rfl⟩ : syracuseStep 1309019 = 1963529) B1963529
theorem B18905521 : Blo 872567 18905521 := bstep (se 2 (by rfl) ⟨7089570, by rfl⟩ : syracuseStep 18905521 = 14179141) B14179141
theorem B14186933 : Blo 872567 14186933 := bstep (se 5 (by rfl) ⟨665012, by rfl⟩ : syracuseStep 14186933 = 1330025) B1330025
theorem B7469495 : Blo 872567 7469495 := bstep (se 1 (by rfl) ⟨5602121, by rfl⟩ : syracuseStep 7469495 = 11204243) B11204243
theorem B1309247 : Blo 872567 1309247 := bstep (se 1 (by rfl) ⟨981935, by rfl⟩ : syracuseStep 1309247 = 1963871) B1963871
theorem B981679 : Blo 872567 981679 := bstep (se 1 (by rfl) ⟨736259, by rfl⟩ : syracuseStep 981679 = 1472519) B1472519
theorem B1309367 : Blo 872567 1309367 := bstep (se 1 (by rfl) ⟨982025, by rfl⟩ : syracuseStep 1309367 = 1964051) B1964051
theorem B2947859 : Blo 872567 2947859 := bstep (se 1 (by rfl) ⟨2210894, by rfl⟩ : syracuseStep 2947859 = 4421789) B4421789
theorem B1964879 : Blo 872567 1964879 := bstep (se 1 (by rfl) ⟨1473659, by rfl⟩ : syracuseStep 1964879 = 2947319) B2947319
theorem B1309595 : Blo 872567 1309595 := bstep (se 1 (by rfl) ⟨982196, by rfl⟩ : syracuseStep 1309595 = 1964393) B1964393
theorem B981967 : Blo 872567 981967 := bstep (se 1 (by rfl) ⟨736475, by rfl⟩ : syracuseStep 981967 = 1472951) B1472951
theorem B1473511 : Blo 872567 1473511 := bstep (se 1 (by rfl) ⟨1105133, by rfl⟩ : syracuseStep 1473511 = 2210267) B2210267
theorem B3996659 : Blo 872567 3996659 := bstep (se 1 (by rfl) ⟨2997494, by rfl⟩ : syracuseStep 3996659 = 5994989) B5994989
theorem B6650909 : Blo 872567 6650909 := bstep (se 3 (by rfl) ⟨1247045, by rfl⟩ : syracuseStep 6650909 = 2494091) B2494091
theorem B1965095 : Blo 872567 1965095 := bstep (se 1 (by rfl) ⟨1473821, by rfl⟩ : syracuseStep 1965095 = 2947643) B2947643
theorem B2489467 : Blo 872567 2489467 := bstep (se 1 (by rfl) ⟨1867100, by rfl⟩ : syracuseStep 2489467 = 3734201) B3734201
theorem B12582053 : Blo 872567 12582053 := bstep (se 4 (by rfl) ⟨1179567, by rfl⟩ : syracuseStep 12582053 = 2359135) B2359135
theorem B7470245 : Blo 872567 7470245 := bstep (se 4 (by rfl) ⟨700335, by rfl⟩ : syracuseStep 7470245 = 1400671) B1400671
theorem B1965275 : Blo 872567 1965275 := bstep (se 1 (by rfl) ⟨1473956, by rfl⟩ : syracuseStep 1965275 = 2947913) B2947913
theorem B4422923 : Blo 872567 4422923 := bstep (se 1 (by rfl) ⟨3317192, by rfl⟩ : syracuseStep 4422923 = 6634385) B6634385
theorem B1309991 : Blo 872567 1309991 := bstep (se 1 (by rfl) ⟨982493, by rfl⟩ : syracuseStep 1309991 = 1964987) B1964987
theorem B982363 : Blo 872567 982363 := bstep (se 1 (by rfl) ⟨736772, by rfl⟩ : syracuseStep 982363 = 1473545) B1473545
theorem B4193633 : Blo 872567 4193633 := bstep (se 2 (by rfl) ⟨1572612, by rfl⟩ : syracuseStep 4193633 = 3145225) B3145225
theorem B1310075 : Blo 872567 1310075 := bstep (se 1 (by rfl) ⟨982556, by rfl⟩ : syracuseStep 1310075 = 1965113) B1965113
theorem B1965473 : Blo 872567 1965473 := bstep (se 2 (by rfl) ⟨737052, by rfl⟩ : syracuseStep 1965473 = 1474105) B1474105
theorem B982471 : Blo 872567 982471 := bstep (se 1 (by rfl) ⟨736853, by rfl⟩ : syracuseStep 982471 = 1473707) B1473707
theorem B1310201 : Blo 872567 1310201 := bstep (se 2 (by rfl) ⟨491325, by rfl⟩ : syracuseStep 1310201 = 982651) B982651
theorem B2358791 : Blo 872567 2358791 := bstep (se 1 (by rfl) ⟨1769093, by rfl⟩ : syracuseStep 2358791 = 3538187) B3538187
theorem B1310303 : Blo 872567 1310303 := bstep (se 1 (by rfl) ⟨982727, by rfl⟩ : syracuseStep 1310303 = 1965455) B1965455
theorem B2948723 : Blo 872567 2948723 := bstep (se 1 (by rfl) ⟨2211542, by rfl⟩ : syracuseStep 2948723 = 4423085) B4423085
theorem B13631093 : Blo 872567 13631093 := bstep (se 5 (by rfl) ⟨638957, by rfl⟩ : syracuseStep 13631093 = 1277915) B1277915
theorem B982831 : Blo 872567 982831 := bstep (se 1 (by rfl) ⟨737123, by rfl⟩ : syracuseStep 982831 = 1474247) B1474247
theorem B1310519 : Blo 872567 1310519 := bstep (se 1 (by rfl) ⟨982889, by rfl⟩ : syracuseStep 1310519 = 1965779) B1965779
theorem B2948993 : Blo 872567 2948993 := bstep (se 2 (by rfl) ⟨1105872, by rfl⟩ : syracuseStep 2948993 = 2211745) B2211745
theorem B982939 : Blo 872567 982939 := bstep (se 1 (by rfl) ⟨737204, by rfl⟩ : syracuseStep 982939 = 1474409) B1474409
theorem B1966031 : Blo 872567 1966031 := bstep (se 1 (by rfl) ⟨1474523, by rfl⟩ : syracuseStep 1966031 = 2949047) B2949047
theorem B1310939 : Blo 872567 1310939 := bstep (se 1 (by rfl) ⟨983204, by rfl⟩ : syracuseStep 1310939 = 1966409) B1966409
theorem B1310951 : Blo 872567 1310951 := bstep (se 1 (by rfl) ⟨983213, by rfl⟩ : syracuseStep 1310951 = 1966427) B1966427
theorem B1311113 : Blo 872567 1311113 := bstep (se 2 (by rfl) ⟨491667, by rfl⟩ : syracuseStep 1311113 = 983335) B983335
theorem B1966535 : Blo 872567 1966535 := bstep (se 1 (by rfl) ⟨1474901, by rfl⟩ : syracuseStep 1966535 = 2949803) B2949803
theorem B1475023 : Blo 872567 1475023 := bstep (se 1 (by rfl) ⟨1106267, by rfl⟩ : syracuseStep 1475023 = 2212535) B2212535
theorem B6652367 : Blo 872567 6652367 := bstep (se 1 (by rfl) ⟨4989275, by rfl⟩ : syracuseStep 6652367 = 9978551) B9978551
theorem B1311209 : Blo 872567 1311209 := bstep (se 2 (by rfl) ⟨491703, by rfl⟩ : syracuseStep 1311209 = 983407) B983407
theorem B2490857 : Blo 872567 2490857 := bstep (se 2 (by rfl) ⟨934071, by rfl⟩ : syracuseStep 2490857 = 1868143) B1868143
theorem B2949695 : Blo 872567 2949695 := bstep (se 1 (by rfl) ⟨2212271, by rfl⟩ : syracuseStep 2949695 = 4424543) B4424543
theorem B1311335 : Blo 872567 1311335 := bstep (se 1 (by rfl) ⟨983501, by rfl⟩ : syracuseStep 1311335 = 1967003) B1967003
theorem B1311467 : Blo 872567 1311467 := bstep (se 1 (by rfl) ⟨983600, by rfl⟩ : syracuseStep 1311467 = 1967201) B1967201
theorem B1311497 : Blo 872567 1311497 := bstep (se 2 (by rfl) ⟨491811, by rfl⟩ : syracuseStep 1311497 = 983623) B983623
theorem B1966895 : Blo 872567 1966895 := bstep (se 1 (by rfl) ⟨1475171, by rfl⟩ : syracuseStep 1966895 = 2950343) B2950343
theorem B1311599 : Blo 872567 1311599 := bstep (se 1 (by rfl) ⟨983699, by rfl⟩ : syracuseStep 1311599 = 1967399) B1967399
theorem B6292409 : Blo 872567 6292409 := bstep (se 2 (by rfl) ⟨2359653, by rfl⟩ : syracuseStep 6292409 = 4719307) B4719307
theorem B984127 : Blo 872567 984127 := bstep (se 1 (by rfl) ⟨738095, by rfl⟩ : syracuseStep 984127 = 1476191) B1476191
theorem B1246271 : Blo 872567 1246271 := bstep (se 1 (by rfl) ⟨934703, by rfl⟩ : syracuseStep 1246271 = 1869407) B1869407
theorem B4785257 : Blo 872567 4785257 := bstep (se 2 (by rfl) ⟨1794471, by rfl⟩ : syracuseStep 4785257 = 3588943) B3588943
theorem B1311851 : Blo 872567 1311851 := bstep (se 1 (by rfl) ⟨983888, by rfl⟩ : syracuseStep 1311851 = 1967777) B1967777
theorem B1475759 : Blo 872567 1475759 := bstep (se 1 (by rfl) ⟨1106819, by rfl⟩ : syracuseStep 1475759 = 2213639) B2213639
theorem B984271 : Blo 872567 984271 := bstep (se 1 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 984271 = 1476407) B1476407
theorem B1312091 : Blo 872567 1312091 := bstep (se 1 (by rfl) ⟨984068, by rfl⟩ : syracuseStep 1312091 = 1968137) B1968137
theorem B1475995 : Blo 872567 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B14910965 : Blo 872567 14910965 := bstep (se 5 (by rfl) ⟨698951, by rfl⟩ : syracuseStep 14910965 = 1397903) B1397903
theorem B1869331 : Blo 872567 1869331 := bstep (se 1 (by rfl) ⟨1401998, by rfl⟩ : syracuseStep 1869331 = 2803997) B2803997
theorem B1312367 : Blo 872567 1312367 := bstep (se 1 (by rfl) ⟨984275, by rfl⟩ : syracuseStep 1312367 = 1968551) B1968551
theorem B1312439 : Blo 872567 1312439 := bstep (se 1 (by rfl) ⟨984329, by rfl⟩ : syracuseStep 1312439 = 1968659) B1968659
theorem B1312475 : Blo 872567 1312475 := bstep (se 1 (by rfl) ⟨984356, by rfl⟩ : syracuseStep 1312475 = 1968713) B1968713
theorem B1476319 : Blo 872567 1476319 := bstep (se 1 (by rfl) ⟨1107239, by rfl⟩ : syracuseStep 1476319 = 2214479) B2214479
theorem B2492167 : Blo 872567 2492167 := bstep (se 1 (by rfl) ⟨1869125, by rfl⟩ : syracuseStep 2492167 = 3738251) B3738251
theorem B1967903 : Blo 872567 1967903 := bstep (se 1 (by rfl) ⟨1475927, by rfl⟩ : syracuseStep 1967903 = 2951855) B2951855
theorem B2492201 : Blo 872567 2492201 := bstep (se 2 (by rfl) ⟨934575, by rfl⟩ : syracuseStep 2492201 = 1869151) B1869151
theorem B2950991 : Blo 872567 2950991 := bstep (se 1 (by rfl) ⟨2213243, by rfl⟩ : syracuseStep 2950991 = 4426487) B4426487
theorem B5605199 : Blo 872567 5605199 := bstep (se 1 (by rfl) ⟨4203899, by rfl⟩ : syracuseStep 5605199 = 8407799) B8407799
theorem B161580905 : Blo 872567 161580905 := bstep (se 2 (by rfl) ⟨60592839, by rfl⟩ : syracuseStep 161580905 = 121185679) B121185679
theorem B1312649 : Blo 872567 1312649 := bstep (se 2 (by rfl) ⟨492243, by rfl⟩ : syracuseStep 1312649 = 984487) B984487
theorem B1312751 : Blo 872567 1312751 := bstep (se 1 (by rfl) ⟨984563, by rfl⟩ : syracuseStep 1312751 = 1969127) B1969127
theorem B1968119 : Blo 872567 1968119 := bstep (se 1 (by rfl) ⟨1476089, by rfl⟩ : syracuseStep 1968119 = 2952179) B2952179
theorem B4720691 : Blo 872567 4720691 := bstep (se 1 (by rfl) ⟨3540518, by rfl⟩ : syracuseStep 4720691 = 7081037) B7081037
theorem B1476751 : Blo 872567 1476751 := bstep (se 1 (by rfl) ⟨1107563, by rfl⟩ : syracuseStep 1476751 = 2215127) B2215127
theorem B2951315 : Blo 872567 2951315 := bstep (se 1 (by rfl) ⟨2213486, by rfl⟩ : syracuseStep 2951315 = 4426973) B4426973
theorem B985243 : Blo 872567 985243 := bstep (se 1 (by rfl) ⟨738932, by rfl⟩ : syracuseStep 985243 = 1477865) B1477865
theorem B985279 : Blo 872567 985279 := bstep (se 1 (by rfl) ⟨738959, by rfl⟩ : syracuseStep 985279 = 1477919) B1477919
theorem B1313003 : Blo 872567 1313003 := bstep (se 1 (by rfl) ⟨984752, by rfl⟩ : syracuseStep 1313003 = 1969505) B1969505
theorem B4983079 : Blo 872567 4983079 := bstep (se 1 (by rfl) ⟨3737309, by rfl⟩ : syracuseStep 4983079 = 7474619) B7474619
theorem B1313063 : Blo 872567 1313063 := bstep (se 1 (by rfl) ⟨984797, by rfl⟩ : syracuseStep 1313063 = 1969595) B1969595
theorem B1968479 : Blo 872567 1968479 := bstep (se 1 (by rfl) ⟨1476359, by rfl⟩ : syracuseStep 1968479 = 2952719) B2952719
theorem B1313147 : Blo 872567 1313147 := bstep (se 1 (by rfl) ⟨984860, by rfl⟩ : syracuseStep 1313147 = 1969721) B1969721
theorem B2951585 : Blo 872567 2951585 := bstep (se 2 (by rfl) ⟨1106844, by rfl⟩ : syracuseStep 2951585 = 2213689) B2213689
theorem B1313417 : Blo 872567 1313417 := bstep (se 2 (by rfl) ⟨492531, by rfl⟩ : syracuseStep 1313417 = 985063) B985063
theorem B1313591 : Blo 872567 1313591 := bstep (se 1 (by rfl) ⟨985193, by rfl⟩ : syracuseStep 1313591 = 1970387) B1970387
theorem B1313627 : Blo 872567 1313627 := bstep (se 1 (by rfl) ⟨985220, by rfl⟩ : syracuseStep 1313627 = 1970441) B1970441
theorem B1313771 : Blo 872567 1313771 := bstep (se 1 (by rfl) ⟨985328, by rfl⟩ : syracuseStep 1313771 = 1970657) B1970657
theorem B1969199 : Blo 872567 1969199 := bstep (se 1 (by rfl) ⟨1476899, by rfl⟩ : syracuseStep 1969199 = 2953799) B2953799
theorem B1477703 : Blo 872567 1477703 := bstep (se 1 (by rfl) ⟨1108277, by rfl⟩ : syracuseStep 1477703 = 2216555) B2216555
theorem B1313975 : Blo 872567 1313975 := bstep (se 1 (by rfl) ⟨985481, by rfl⟩ : syracuseStep 1313975 = 1970963) B1970963
theorem B9473213 : Blo 872567 9473213 := bstep (se 3 (by rfl) ⟨1776227, by rfl⟩ : syracuseStep 9473213 = 3552455) B3552455
theorem B6655283 : Blo 872567 6655283 := bstep (se 1 (by rfl) ⟨4991462, by rfl⟩ : syracuseStep 6655283 = 9982925) B9982925
theorem B1969487 : Blo 872567 1969487 := bstep (se 1 (by rfl) ⟨1477115, by rfl⟩ : syracuseStep 1969487 = 2954231) B2954231
theorem B1576303 : Blo 872567 1576303 := bstep (se 1 (by rfl) ⟨1182227, by rfl⟩ : syracuseStep 1576303 = 2364455) B2364455
theorem B1314215 : Blo 872567 1314215 := bstep (se 1 (by rfl) ⟨985661, by rfl⟩ : syracuseStep 1314215 = 1971323) B1971323
theorem B1969577 : Blo 872567 1969577 := bstep (se 2 (by rfl) ⟨738591, by rfl⟩ : syracuseStep 1969577 = 1477183) B1477183
theorem B1478135 : Blo 872567 1478135 := bstep (se 1 (by rfl) ⟨1108601, by rfl⟩ : syracuseStep 1478135 = 2217203) B2217203
theorem B8392187 : Blo 872567 8392187 := bstep (se 1 (by rfl) ⟨6294140, by rfl⟩ : syracuseStep 8392187 = 12588281) B12588281
theorem B1314299 : Blo 872567 1314299 := bstep (se 1 (by rfl) ⟨985724, by rfl⟩ : syracuseStep 1314299 = 1971449) B1971449
theorem B1314395 : Blo 872567 1314395 := bstep (se 1 (by rfl) ⟨985796, by rfl⟩ : syracuseStep 1314395 = 1971593) B1971593
theorem B1314479 : Blo 872567 1314479 := bstep (se 1 (by rfl) ⟨985859, by rfl⟩ : syracuseStep 1314479 = 1971719) B1971719
theorem B4427459 : Blo 872567 4427459 := bstep (se 1 (by rfl) ⟨3320594, by rfl⟩ : syracuseStep 4427459 = 6641189) B6641189
theorem B1314599 : Blo 872567 1314599 := bstep (se 1 (by rfl) ⟨985949, by rfl⟩ : syracuseStep 1314599 = 1971899) B1971899
theorem B1314683 : Blo 872567 1314683 := bstep (se 1 (by rfl) ⟨986012, by rfl⟩ : syracuseStep 1314683 = 1972025) B1972025
theorem B1970063 : Blo 872567 1970063 := bstep (se 1 (by rfl) ⟨1477547, by rfl⟩ : syracuseStep 1970063 = 2955095) B2955095
theorem B4722941 : Blo 872567 4722941 := bstep (se 3 (by rfl) ⟨885551, by rfl⟩ : syracuseStep 4722941 = 1771103) B1771103
theorem B2494729 : Blo 872567 2494729 := bstep (se 2 (by rfl) ⟨935523, by rfl⟩ : syracuseStep 2494729 = 1871047) B1871047
theorem B2494775 : Blo 872567 2494775 := bstep (se 1 (by rfl) ⟨1871081, by rfl⟩ : syracuseStep 2494775 = 3742163) B3742163
theorem B2953583 : Blo 872567 2953583 := bstep (se 1 (by rfl) ⟨2215187, by rfl⟩ : syracuseStep 2953583 = 4430375) B4430375
theorem B1479161 : Blo 872567 1479161 := bstep (se 2 (by rfl) ⟨554685, by rfl⟩ : syracuseStep 1479161 = 1109371) B1109371
theorem B1970783 : Blo 872567 1970783 := bstep (se 1 (by rfl) ⟨1478087, by rfl⟩ : syracuseStep 1970783 = 2956175) B2956175
theorem B2495357 : Blo 872567 2495357 := bstep (se 3 (by rfl) ⟨467879, by rfl⟩ : syracuseStep 2495357 = 935759) B935759
theorem B76584001 : Blo 872567 76584001 := bstep (se 2 (by rfl) ⟨28719000, by rfl⟩ : syracuseStep 76584001 = 57438001) B57438001
theorem B5477483 : Blo 872567 5477483 := bstep (se 1 (by rfl) ⟨4108112, by rfl⟩ : syracuseStep 5477483 = 8216225) B8216225
theorem B4199633 : Blo 872567 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B1774867 : Blo 872567 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B1971611 : Blo 872567 1971611 := bstep (se 1 (by rfl) ⟨1478708, by rfl⟩ : syracuseStep 1971611 = 2957417) B2957417
theorem B2954987 : Blo 872567 2954987 := bstep (se 1 (by rfl) ⟨2216240, by rfl⟩ : syracuseStep 2954987 = 4432481) B4432481
theorem B2365321 : Blo 872567 2365321 := bstep (se 2 (by rfl) ⟨886995, by rfl⟩ : syracuseStep 2365321 = 1773991) B1773991
theorem B1972187 : Blo 872567 1972187 := bstep (se 1 (by rfl) ⟨1479140, by rfl⟩ : syracuseStep 1972187 = 2958281) B2958281
theorem B2955257 : Blo 872567 2955257 := bstep (se 2 (by rfl) ⟨1108221, by rfl⟩ : syracuseStep 2955257 = 2216443) B2216443
theorem B22714433 : Blo 872567 22714433 := bstep (se 2 (by rfl) ⟨8517912, by rfl⟩ : syracuseStep 22714433 = 17035825) B17035825
theorem B18880613 : Blo 872567 18880613 := bstep (se 4 (by rfl) ⟨1770057, by rfl⟩ : syracuseStep 18880613 = 3540115) B3540115
theorem B2955419 : Blo 872567 2955419 := bstep (se 1 (by rfl) ⟨2216564, by rfl⟩ : syracuseStep 2955419 = 4433129) B4433129
theorem B2955527 : Blo 872567 2955527 := bstep (se 1 (by rfl) ⟨2216645, by rfl⟩ : syracuseStep 2955527 = 4433291) B4433291
theorem B5610323 : Blo 872567 5610323 := bstep (se 1 (by rfl) ⟨4207742, by rfl⟩ : syracuseStep 5610323 = 8415485) B8415485
theorem B3316571 : Blo 872567 3316571 := bstep (se 1 (by rfl) ⟨2487428, by rfl⟩ : syracuseStep 3316571 = 4974857) B4974857
theorem B3316585 : Blo 872567 3316585 := bstep (se 2 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 3316585 = 2487439) B2487439
theorem B3742777 : Blo 872567 3742777 := bstep (se 2 (by rfl) ⟨1403541, by rfl⟩ : syracuseStep 3742777 = 2807083) B2807083
theorem B6397181 : Blo 872567 6397181 := bstep (se 3 (by rfl) ⟨1199471, by rfl⟩ : syracuseStep 6397181 = 2398943) B2398943
theorem B2956553 : Blo 872567 2956553 := bstep (se 2 (by rfl) ⟨1108707, by rfl⟩ : syracuseStep 2956553 = 2217415) B2217415
theorem B7478993 : Blo 872567 7478993 := bstep (se 2 (by rfl) ⟨2804622, by rfl⟩ : syracuseStep 7478993 = 5609245) B5609245
theorem B4431671 : Blo 872567 4431671 := bstep (se 1 (by rfl) ⟨3323753, by rfl⟩ : syracuseStep 4431671 = 6647507) B6647507
theorem B1515419 : Blo 872567 1515419 := bstep (se 1 (by rfl) ⟨1136564, by rfl⟩ : syracuseStep 1515419 = 2273129) B2273129
theorem B10657757 : Blo 872567 10657757 := bstep (se 3 (by rfl) ⟨1998329, by rfl⟩ : syracuseStep 10657757 = 3996659) B3996659
theorem B2957687 : Blo 872567 2957687 := bstep (se 1 (by rfl) ⟨2218265, by rfl⟩ : syracuseStep 2957687 = 4436531) B4436531
theorem B5611963 : Blo 872567 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B25207361 : Blo 872567 25207361 := bstep (se 2 (by rfl) ⟨9452760, by rfl⟩ : syracuseStep 25207361 = 18905521) B18905521
theorem B3547721 : Blo 872567 3547721 := bstep (se 2 (by rfl) ⟨1330395, by rfl⟩ : syracuseStep 3547721 = 2660791) B2660791
theorem B11183021 : Blo 872567 11183021 := bstep (se 3 (by rfl) ⟨2096816, by rfl⟩ : syracuseStep 11183021 = 4193633) B4193633
theorem B4989869 : Blo 872567 4989869 := bstep (se 3 (by rfl) ⟨935600, by rfl⟩ : syracuseStep 4989869 = 1871201) B1871201
theorem B11216029 : Blo 872567 11216029 := bstep (se 3 (by rfl) ⟨2103005, by rfl⟩ : syracuseStep 11216029 = 4206011) B4206011
theorem B3155375 : Blo 872567 3155375 := bstep (se 1 (by rfl) ⟨2366531, by rfl⟩ : syracuseStep 3155375 = 4733063) B4733063
theorem B3319289 : Blo 872567 3319289 := bstep (se 2 (by rfl) ⟨1244733, by rfl⟩ : syracuseStep 3319289 = 2489467) B2489467
theorem B12625415 : Blo 872567 12625415 := bstep (se 1 (by rfl) ⟨9469061, by rfl⟩ : syracuseStep 12625415 = 18938123) B18938123
theorem B4433939 : Blo 872567 4433939 := bstep (se 1 (by rfl) ⟨3325454, by rfl⟩ : syracuseStep 4433939 = 6650909) B6650909
theorem B4991327 : Blo 872567 4991327 := bstep (se 1 (by rfl) ⟨3743495, by rfl⟩ : syracuseStep 4991327 = 7486991) B7486991
theorem B9087395 : Blo 872567 9087395 := bstep (se 1 (by rfl) ⟨6815546, by rfl⟩ : syracuseStep 9087395 = 13631093) B13631093
theorem B83143361 : Blo 872567 83143361 := bstep (se 2 (by rfl) ⟨31178760, by rfl⟩ : syracuseStep 83143361 = 62357521) B62357521
theorem B3156931 : Blo 872567 3156931 := bstep (se 1 (by rfl) ⟨2367698, by rfl⟩ : syracuseStep 3156931 = 4735397) B4735397
theorem B22686799 : Blo 872567 22686799 := bstep (se 1 (by rfl) ⟨17015099, by rfl⟩ : syracuseStep 22686799 = 34030199) B34030199
theorem B2796923 : Blo 872567 2796923 := bstep (se 1 (by rfl) ⟨2097692, by rfl⟩ : syracuseStep 2796923 = 4195385) B4195385
theorem B3157841 : Blo 872567 3157841 := bstep (se 2 (by rfl) ⟨1184190, by rfl⟩ : syracuseStep 3157841 = 2368381) B2368381
theorem B3027131 : Blo 872567 3027131 := bstep (se 1 (by rfl) ⟨2270348, by rfl⟩ : syracuseStep 3027131 = 4540697) B4540697
theorem B10105559 : Blo 872567 10105559 := bstep (se 1 (by rfl) ⟨7579169, by rfl⟩ : syracuseStep 10105559 = 15158339) B15158339
theorem B12105577 : Blo 872567 12105577 := bstep (se 2 (by rfl) ⟨4539591, by rfl⟩ : syracuseStep 12105577 = 9079183) B9079183
theorem B2799497 : Blo 872567 2799497 := bstep (se 2 (by rfl) ⟨1049811, by rfl⟩ : syracuseStep 2799497 = 2099623) B2099623
theorem B38320067 : Blo 872567 38320067 := bstep (se 1 (by rfl) ⟨28740050, by rfl⟩ : syracuseStep 38320067 = 57480101) B57480101
theorem B2209751 : Blo 872567 2209751 := bstep (se 1 (by rfl) ⟨1657313, by rfl⟩ : syracuseStep 2209751 = 3314627) B3314627
theorem B2211239 : Blo 872567 2211239 := bstep (se 1 (by rfl) ⟨1658429, by rfl⟩ : syracuseStep 2211239 = 3316859) B3316859
theorem B4734445 : Blo 872567 4734445 := bstep (se 3 (by rfl) ⟨887708, by rfl⟩ : syracuseStep 4734445 = 1775417) B1775417
theorem B3194747 : Blo 872567 3194747 := bstep (se 1 (by rfl) ⟨2396060, by rfl⟩ : syracuseStep 3194747 = 4792121) B4792121
theorem B22724813 : Blo 872567 22724813 := bstep (se 3 (by rfl) ⟨4260902, by rfl⟩ : syracuseStep 22724813 = 8521805) B8521805
theorem B12633205 : Blo 872567 12633205 := bstep (se 5 (by rfl) ⟨592181, by rfl⟩ : syracuseStep 12633205 = 1184363) B1184363
theorem B5981309 : Blo 872567 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B7980767 : Blo 872567 7980767 := bstep (se 1 (by rfl) ⟨5985575, by rfl⟩ : syracuseStep 7980767 = 11971151) B11971151
theorem B1656607 : Blo 872567 1656607 := bstep (se 1 (by rfl) ⟨1242455, by rfl⟩ : syracuseStep 1656607 = 2484911) B2484911
theorem B2213831 : Blo 872567 2213831 := bstep (se 1 (by rfl) ⟨1660373, by rfl⟩ : syracuseStep 2213831 = 3320747) B3320747
theorem B3786761 : Blo 872567 3786761 := bstep (se 2 (by rfl) ⟨1420035, by rfl⟩ : syracuseStep 3786761 = 2840071) B2840071
theorem B1329691 : Blo 872567 1329691 := bstep (se 1 (by rfl) ⟨997268, by rfl⟩ : syracuseStep 1329691 = 1994537) B1994537
theorem B1657655 : Blo 872567 1657655 := bstep (se 1 (by rfl) ⟨1243241, by rfl⟩ : syracuseStep 1657655 = 2486483) B2486483
theorem B47893355 : Blo 872567 47893355 := bstep (se 1 (by rfl) ⟨35920016, by rfl⟩ : syracuseStep 47893355 = 71840033) B71840033
theorem B24235211 : Blo 872567 24235211 := bstep (se 1 (by rfl) ⟨18176408, by rfl⟩ : syracuseStep 24235211 = 36352817) B36352817
theorem B6311785 : Blo 872567 6311785 := bstep (se 2 (by rfl) ⟨2366919, by rfl⟩ : syracuseStep 6311785 = 4733839) B4733839
theorem B12472211 : Blo 872567 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B17256509 : Blo 872567 17256509 := bstep (se 3 (by rfl) ⟨3235595, by rfl⟩ : syracuseStep 17256509 = 6471191) B6471191
theorem B7459037 : Blo 872567 7459037 := bstep (se 3 (by rfl) ⟨1398569, by rfl⟩ : syracuseStep 7459037 = 2797139) B2797139
theorem B872679 : Blo 872567 872679 := bstep (se 1 (by rfl) ⟨654509, by rfl⟩ : syracuseStep 872679 = 1309019) B1309019
theorem B9457955 : Blo 872567 9457955 := bstep (se 1 (by rfl) ⟨7093466, by rfl⟩ : syracuseStep 9457955 = 14186933) B14186933
theorem B872831 : Blo 872567 872831 := bstep (se 1 (by rfl) ⟨654623, by rfl⟩ : syracuseStep 872831 = 1309247) B1309247
theorem B872911 : Blo 872567 872911 := bstep (se 1 (by rfl) ⟨654683, by rfl⟩ : syracuseStep 872911 = 1309367) B1309367
theorem B873063 : Blo 872567 873063 := bstep (se 1 (by rfl) ⟨654797, by rfl⟩ : syracuseStep 873063 = 1309595) B1309595
theorem B873327 : Blo 872567 873327 := bstep (se 1 (by rfl) ⟨654995, by rfl⟩ : syracuseStep 873327 = 1309991) B1309991
theorem B873383 : Blo 872567 873383 := bstep (se 1 (by rfl) ⟨655037, by rfl⟩ : syracuseStep 873383 = 1310075) B1310075
theorem B873467 : Blo 872567 873467 := bstep (se 1 (by rfl) ⟨655100, by rfl⟩ : syracuseStep 873467 = 1310201) B1310201
theorem B873535 : Blo 872567 873535 := bstep (se 1 (by rfl) ⟨655151, by rfl⟩ : syracuseStep 873535 = 1310303) B1310303
theorem B873679 : Blo 872567 873679 := bstep (se 1 (by rfl) ⟨655259, by rfl⟩ : syracuseStep 873679 = 1310519) B1310519
theorem B4478327 : Blo 872567 4478327 := bstep (se 1 (by rfl) ⟨3358745, by rfl⟩ : syracuseStep 4478327 = 6717491) B6717491
theorem B873883 : Blo 872567 873883 := bstep (se 1 (by rfl) ⟨655412, by rfl⟩ : syracuseStep 873883 = 1310825) B1310825
theorem B874095 : Blo 872567 874095 := bstep (se 1 (by rfl) ⟨655571, by rfl⟩ : syracuseStep 874095 = 1311143) B1311143
theorem B874151 : Blo 872567 874151 := bstep (se 1 (by rfl) ⟨655613, by rfl⟩ : syracuseStep 874151 = 1311227) B1311227
theorem B874235 : Blo 872567 874235 := bstep (se 1 (by rfl) ⟨655676, by rfl⟩ : syracuseStep 874235 = 1311353) B1311353
theorem B874271 : Blo 872567 874271 := bstep (se 1 (by rfl) ⟨655703, by rfl⟩ : syracuseStep 874271 = 1311407) B1311407
theorem B874303 : Blo 872567 874303 := bstep (se 1 (by rfl) ⟨655727, by rfl⟩ : syracuseStep 874303 = 1311455) B1311455
theorem B874479 : Blo 872567 874479 := bstep (se 1 (by rfl) ⟨655859, by rfl⟩ : syracuseStep 874479 = 1311719) B1311719
theorem B1398775 : Blo 872567 1398775 := bstep (se 1 (by rfl) ⟨1049081, by rfl⟩ : syracuseStep 1398775 = 2098163) B2098163
theorem B1497079 : Blo 872567 1497079 := bstep (se 1 (by rfl) ⟨1122809, by rfl⟩ : syracuseStep 1497079 = 2245619) B2245619
theorem B2807801 : Blo 872567 2807801 := bstep (se 2 (by rfl) ⟨1052925, by rfl⟩ : syracuseStep 2807801 = 2105851) B2105851
theorem B2807903 : Blo 872567 2807903 := bstep (se 1 (by rfl) ⟨2105927, by rfl⟩ : syracuseStep 2807903 = 4211855) B4211855
theorem B874651 : Blo 872567 874651 := bstep (se 1 (by rfl) ⟨655988, by rfl⟩ : syracuseStep 874651 = 1311977) B1311977
theorem B874687 : Blo 872567 874687 := bstep (se 1 (by rfl) ⟨656015, by rfl⟩ : syracuseStep 874687 = 1312031) B1312031
theorem B874799 : Blo 872567 874799 := bstep (se 1 (by rfl) ⟨656099, by rfl⟩ : syracuseStep 874799 = 1312199) B1312199
theorem B875035 : Blo 872567 875035 := bstep (se 1 (by rfl) ⟨656276, by rfl⟩ : syracuseStep 875035 = 1312553) B1312553
theorem B875039 : Blo 872567 875039 := bstep (se 1 (by rfl) ⟨656279, by rfl⟩ : syracuseStep 875039 = 1312559) B1312559
theorem B11950679 : Blo 872567 11950679 := bstep (se 1 (by rfl) ⟨8963009, by rfl⟩ : syracuseStep 11950679 = 17926019) B17926019
theorem B7461497 : Blo 872567 7461497 := bstep (se 2 (by rfl) ⟨2798061, by rfl⟩ : syracuseStep 7461497 = 5596123) B5596123
theorem B875355 : Blo 872567 875355 := bstep (se 1 (by rfl) ⟨656516, by rfl⟩ : syracuseStep 875355 = 1313033) B1313033
theorem B875423 : Blo 872567 875423 := bstep (se 1 (by rfl) ⟨656567, by rfl⟩ : syracuseStep 875423 = 1313135) B1313135
theorem B875567 : Blo 872567 875567 := bstep (se 1 (by rfl) ⟨656675, by rfl⟩ : syracuseStep 875567 = 1313351) B1313351
theorem B9952307 : Blo 872567 9952307 := bstep (se 1 (by rfl) ⟨7464230, by rfl⟩ : syracuseStep 9952307 = 14928461) B14928461
theorem B875591 : Blo 872567 875591 := bstep (se 1 (by rfl) ⟨656693, by rfl⟩ : syracuseStep 875591 = 1313387) B1313387
theorem B875743 : Blo 872567 875743 := bstep (se 1 (by rfl) ⟨656807, by rfl⟩ : syracuseStep 875743 = 1313615) B1313615
theorem B1662439 : Blo 872567 1662439 := bstep (se 1 (by rfl) ⟨1246829, by rfl⟩ : syracuseStep 1662439 = 2493659) B2493659
theorem B876007 : Blo 872567 876007 := bstep (se 1 (by rfl) ⟨657005, by rfl⟩ : syracuseStep 876007 = 1314011) B1314011
theorem B876123 : Blo 872567 876123 := bstep (se 1 (by rfl) ⟨657092, by rfl⟩ : syracuseStep 876123 = 1314185) B1314185
theorem B43048543 : Blo 872567 43048543 := bstep (se 1 (by rfl) ⟨32286407, by rfl⟩ : syracuseStep 43048543 = 64572815) B64572815
theorem B1662697 : Blo 872567 1662697 := bstep (se 2 (by rfl) ⟨623511, by rfl⟩ : syracuseStep 1662697 = 1247023) B1247023
theorem B15163139 : Blo 872567 15163139 := bstep (se 1 (by rfl) ⟨11372354, by rfl⟩ : syracuseStep 15163139 = 22744709) B22744709
theorem B876359 : Blo 872567 876359 := bstep (se 1 (by rfl) ⟨657269, by rfl⟩ : syracuseStep 876359 = 1314539) B1314539
theorem B876511 : Blo 872567 876511 := bstep (se 1 (by rfl) ⟨657383, by rfl⟩ : syracuseStep 876511 = 1314767) B1314767
theorem B4972873 : Blo 872567 4972873 := bstep (se 2 (by rfl) ⟨1864827, by rfl⟩ : syracuseStep 4972873 = 3729655) B3729655
theorem B1663753 : Blo 872567 1663753 := bstep (se 2 (by rfl) ⟨623907, by rfl⟩ : syracuseStep 1663753 = 1247815) B1247815
theorem B6644591 : Blo 872567 6644591 := bstep (se 1 (by rfl) ⟨4983443, by rfl⟩ : syracuseStep 6644591 = 9966887) B9966887
theorem B25191323 : Blo 872567 25191323 := bstep (se 1 (by rfl) ⟨18893492, by rfl⟩ : syracuseStep 25191323 = 37786985) B37786985
theorem B10774073 : Blo 872567 10774073 := bstep (se 2 (by rfl) ⟨4040277, by rfl⟩ : syracuseStep 10774073 = 8080555) B8080555
theorem B9463355 : Blo 872567 9463355 := bstep (se 1 (by rfl) ⟨7097516, by rfl⟩ : syracuseStep 9463355 = 14195033) B14195033
theorem B31975033 : Blo 872567 31975033 := bstep (se 2 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 31975033 = 23981275) B23981275
theorem B68118353 : Blo 872567 68118353 := bstep (se 2 (by rfl) ⟨25544382, by rfl⟩ : syracuseStep 68118353 = 51088765) B51088765
theorem B1403183 : Blo 872567 1403183 := bstep (se 1 (by rfl) ⟨1052387, by rfl⟩ : syracuseStep 1403183 = 2104775) B2104775
theorem B1993223 : Blo 872567 1993223 := bstep (se 1 (by rfl) ⟨1494917, by rfl⟩ : syracuseStep 1993223 = 2989835) B2989835
theorem B7465871 : Blo 872567 7465871 := bstep (se 1 (by rfl) ⟨5599403, by rfl⟩ : syracuseStep 7465871 = 11198807) B11198807
theorem B3992555 : Blo 872567 3992555 := bstep (se 1 (by rfl) ⟨2994416, by rfl⟩ : syracuseStep 3992555 = 5988833) B5988833
theorem B31976765 : Blo 872567 31976765 := bstep (se 3 (by rfl) ⟨5995643, by rfl⟩ : syracuseStep 31976765 = 11991287) B11991287
theorem B4419197 : Blo 872567 4419197 := bstep (se 3 (by rfl) ⟨828599, by rfl⟩ : syracuseStep 4419197 = 1657199) B1657199
theorem B5599199 : Blo 872567 5599199 := bstep (se 1 (by rfl) ⟨4199399, by rfl⟩ : syracuseStep 5599199 = 8398799) B8398799
theorem B1994719 : Blo 872567 1994719 := bstep (se 1 (by rfl) ⟨1496039, by rfl⟩ : syracuseStep 1994719 = 2992079) B2992079
theorem B1863803 : Blo 872567 1863803 := bstep (se 1 (by rfl) ⟨1397852, by rfl⟩ : syracuseStep 1863803 = 2795705) B2795705
theorem B2945213 : Blo 872567 2945213 := bstep (se 3 (by rfl) ⟨552227, by rfl⟩ : syracuseStep 2945213 = 1104455) B1104455
theorem B3731741 : Blo 872567 3731741 := bstep (se 3 (by rfl) ⟨699701, by rfl⟩ : syracuseStep 3731741 = 1399403) B1399403
theorem B11202907 : Blo 872567 11202907 := bstep (se 1 (by rfl) ⟨8402180, by rfl⟩ : syracuseStep 11202907 = 16804361) B16804361
theorem B4420007 : Blo 872567 4420007 := bstep (se 1 (by rfl) ⟨3315005, by rfl⟩ : syracuseStep 4420007 = 6630011) B6630011
theorem B12579745 : Blo 872567 12579745 := bstep (se 2 (by rfl) ⟨4717404, by rfl⟩ : syracuseStep 12579745 = 9434809) B9434809
theorem B1864777 : Blo 872567 1864777 := bstep (se 2 (by rfl) ⟨699291, by rfl⟩ : syracuseStep 1864777 = 1398583) B1398583
theorem B2946401 : Blo 872567 2946401 := bstep (se 2 (by rfl) ⟨1104900, by rfl⟩ : syracuseStep 2946401 = 2209801) B2209801
theorem B18216355 : Blo 872567 18216355 := bstep (se 1 (by rfl) ⟨13662266, by rfl⟩ : syracuseStep 18216355 = 27324533) B27324533
theorem B5600839 : Blo 872567 5600839 := bstep (se 1 (by rfl) ⟨4200629, by rfl⟩ : syracuseStep 5600839 = 8401259) B8401259
theorem B1963691 : Blo 872567 1963691 := bstep (se 1 (by rfl) ⟨1472768, by rfl⟩ : syracuseStep 1963691 = 2945537) B2945537
theorem B4421303 : Blo 872567 4421303 := bstep (se 1 (by rfl) ⟨3315977, by rfl⟩ : syracuseStep 4421303 = 6631955) B6631955
theorem B1242911 : Blo 872567 1242911 := bstep (se 1 (by rfl) ⟨932183, by rfl⟩ : syracuseStep 1242911 = 1864367) B1864367
theorem B2488283 : Blo 872567 2488283 := bstep (se 1 (by rfl) ⟨1866212, by rfl⟩ : syracuseStep 2488283 = 3732425) B3732425
theorem B1964015 : Blo 872567 1964015 := bstep (se 1 (by rfl) ⟨1473011, by rfl⟩ : syracuseStep 1964015 = 2946023) B2946023
theorem B1308863 : Blo 872567 1308863 := bstep (se 1 (by rfl) ⟨981647, by rfl⟩ : syracuseStep 1308863 = 1963295) B1963295
theorem B1964231 : Blo 872567 1964231 := bstep (se 1 (by rfl) ⟨1473173, by rfl⟩ : syracuseStep 1964231 = 2946347) B2946347
theorem B1308905 : Blo 872567 1308905 := bstep (se 2 (by rfl) ⟨490839, by rfl⟩ : syracuseStep 1308905 = 981679) B981679
theorem B1472809 : Blo 872567 1472809 := bstep (se 2 (by rfl) ⟨552303, by rfl⟩ : syracuseStep 1472809 = 1104607) B1104607
theorem B1964411 : Blo 872567 1964411 := bstep (se 1 (by rfl) ⟨1473308, by rfl⟩ : syracuseStep 1964411 = 2946617) B2946617
theorem B1309211 : Blo 872567 1309211 := bstep (se 1 (by rfl) ⟨981908, by rfl⟩ : syracuseStep 1309211 = 1963817) B1963817
theorem B1309289 : Blo 872567 1309289 := bstep (se 2 (by rfl) ⟨490983, by rfl⟩ : syracuseStep 1309289 = 981967) B981967
theorem B1964681 : Blo 872567 1964681 := bstep (se 2 (by rfl) ⟨736755, by rfl⟩ : syracuseStep 1964681 = 1473511) B1473511
theorem B4979663 : Blo 872567 4979663 := bstep (se 1 (by rfl) ⟨3734747, by rfl⟩ : syracuseStep 4979663 = 7469495) B7469495
theorem B1309817 : Blo 872567 1309817 := bstep (se 2 (by rfl) ⟨491181, by rfl⟩ : syracuseStep 1309817 = 982363) B982363
theorem B1965239 : Blo 872567 1965239 := bstep (se 1 (by rfl) ⟨1473929, by rfl⟩ : syracuseStep 1965239 = 2947859) B2947859
theorem B1309919 : Blo 872567 1309919 := bstep (se 1 (by rfl) ⟨982439, by rfl⟩ : syracuseStep 1309919 = 1964879) B1964879
theorem B2948345 : Blo 872567 2948345 := bstep (se 2 (by rfl) ⟨1105629, by rfl⟩ : syracuseStep 2948345 = 2211259) B2211259
theorem B1309961 : Blo 872567 1309961 := bstep (se 2 (by rfl) ⟨491235, by rfl⟩ : syracuseStep 1309961 = 982471) B982471
theorem B1310063 : Blo 872567 1310063 := bstep (se 1 (by rfl) ⟨982547, by rfl⟩ : syracuseStep 1310063 = 1965095) B1965095
theorem B15170935 : Blo 872567 15170935 := bstep (se 1 (by rfl) ⟨11378201, by rfl⟩ : syracuseStep 15170935 = 22756403) B22756403
theorem B8388035 : Blo 872567 8388035 := bstep (se 1 (by rfl) ⟨6291026, by rfl⟩ : syracuseStep 8388035 = 12582053) B12582053
theorem B4980163 : Blo 872567 4980163 := bstep (se 1 (by rfl) ⟨3735122, by rfl⟩ : syracuseStep 4980163 = 7470245) B7470245
theorem B1310183 : Blo 872567 1310183 := bstep (se 1 (by rfl) ⟨982637, by rfl⟩ : syracuseStep 1310183 = 1965275) B1965275
theorem B2948615 : Blo 872567 2948615 := bstep (se 1 (by rfl) ⟨2211461, by rfl⟩ : syracuseStep 2948615 = 4422923) B4422923
theorem B1474139 : Blo 872567 1474139 := bstep (se 1 (by rfl) ⟨1105604, by rfl⟩ : syracuseStep 1474139 = 2211209) B2211209
theorem B1310315 : Blo 872567 1310315 := bstep (se 1 (by rfl) ⟨982736, by rfl⟩ : syracuseStep 1310315 = 1965473) B1965473
theorem B1572527 : Blo 872567 1572527 := bstep (se 1 (by rfl) ⟨1179395, by rfl⟩ : syracuseStep 1572527 = 2358791) B2358791
theorem B1310441 : Blo 872567 1310441 := bstep (se 2 (by rfl) ⟨491415, by rfl⟩ : syracuseStep 1310441 = 982831) B982831
theorem B1965815 : Blo 872567 1965815 := bstep (se 1 (by rfl) ⟨1474361, by rfl⟩ : syracuseStep 1965815 = 2948723) B2948723
theorem B1867511 : Blo 872567 1867511 := bstep (se 1 (by rfl) ⟨1400633, by rfl⟩ : syracuseStep 1867511 = 2801267) B2801267
theorem B1474375 : Blo 872567 1474375 := bstep (se 1 (by rfl) ⟨1105781, by rfl⟩ : syracuseStep 1474375 = 2211563) B2211563
theorem B1310585 : Blo 872567 1310585 := bstep (se 2 (by rfl) ⟨491469, by rfl⟩ : syracuseStep 1310585 = 982939) B982939
theorem B1965995 : Blo 872567 1965995 := bstep (se 1 (by rfl) ⟨1474496, by rfl⟩ : syracuseStep 1965995 = 2948993) B2948993
theorem B1867691 : Blo 872567 1867691 := bstep (se 1 (by rfl) ⟨1400768, by rfl⟩ : syracuseStep 1867691 = 2801537) B2801537
theorem B1310687 : Blo 872567 1310687 := bstep (se 1 (by rfl) ⟨983015, by rfl⟩ : syracuseStep 1310687 = 1966031) B1966031
theorem B1311023 : Blo 872567 1311023 := bstep (se 1 (by rfl) ⟨983267, by rfl⟩ : syracuseStep 1311023 = 1966535) B1966535
theorem B1966463 : Blo 872567 1966463 := bstep (se 1 (by rfl) ⟨1474847, by rfl⟩ : syracuseStep 1966463 = 2949695) B2949695
theorem B1311263 : Blo 872567 1311263 := bstep (se 1 (by rfl) ⟨983447, by rfl⟩ : syracuseStep 1311263 = 1966895) B1966895
theorem B1966697 : Blo 872567 1966697 := bstep (se 2 (by rfl) ⟨737511, by rfl⟩ : syracuseStep 1966697 = 1475023) B1475023
theorem B983839 : Blo 872567 983839 := bstep (se 1 (by rfl) ⟨737879, by rfl⟩ : syracuseStep 983839 = 1475759) B1475759
theorem B1311935 : Blo 872567 1311935 := bstep (se 1 (by rfl) ⟨983951, by rfl⟩ : syracuseStep 1311935 = 1967903) B1967903
theorem B1967327 : Blo 872567 1967327 := bstep (se 1 (by rfl) ⟨1475495, by rfl⟩ : syracuseStep 1967327 = 2950991) B2950991
theorem B3736799 : Blo 872567 3736799 := bstep (se 1 (by rfl) ⟨2802599, by rfl⟩ : syracuseStep 3736799 = 5605199) B5605199
theorem B1475887 : Blo 872567 1475887 := bstep (se 1 (by rfl) ⟨1106915, by rfl⟩ : syracuseStep 1475887 = 2213831) B2213831
theorem B1312079 : Blo 872567 1312079 := bstep (se 1 (by rfl) ⟨984059, by rfl⟩ : syracuseStep 1312079 = 1968119) B1968119
theorem B1312169 : Blo 872567 1312169 := bstep (se 2 (by rfl) ⟨492063, by rfl⟩ : syracuseStep 1312169 = 984127) B984127
theorem B1967543 : Blo 872567 1967543 := bstep (se 1 (by rfl) ⟨1475657, by rfl⟩ : syracuseStep 1967543 = 2951315) B2951315
theorem B16844273 : Blo 872567 16844273 := bstep (se 2 (by rfl) ⟨6316602, by rfl⟩ : syracuseStep 16844273 = 12633205) B12633205
theorem B1312319 : Blo 872567 1312319 := bstep (se 1 (by rfl) ⟨984239, by rfl⟩ : syracuseStep 1312319 = 1968479) B1968479
theorem B1312361 : Blo 872567 1312361 := bstep (se 2 (by rfl) ⟨492135, by rfl⟩ : syracuseStep 1312361 = 984271) B984271
theorem B1967723 : Blo 872567 1967723 := bstep (se 1 (by rfl) ⟨1475792, by rfl⟩ : syracuseStep 1967723 = 2951585) B2951585
theorem B1967993 : Blo 872567 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B2492441 : Blo 872567 2492441 := bstep (se 2 (by rfl) ⟨934665, by rfl⟩ : syracuseStep 2492441 = 1869331) B1869331
theorem B1312799 : Blo 872567 1312799 := bstep (se 1 (by rfl) ⟨984599, by rfl⟩ : syracuseStep 1312799 = 1969199) B1969199
theorem B985135 : Blo 872567 985135 := bstep (se 1 (by rfl) ⟨738851, by rfl⟩ : syracuseStep 985135 = 1477703) B1477703
theorem B42633377 : Blo 872567 42633377 := bstep (se 2 (by rfl) ⟨15987516, by rfl⟩ : syracuseStep 42633377 = 31975033) B31975033
theorem B1312991 : Blo 872567 1312991 := bstep (se 1 (by rfl) ⟨984743, by rfl⟩ : syracuseStep 1312991 = 1969487) B1969487
theorem B1313051 : Blo 872567 1313051 := bstep (se 1 (by rfl) ⟨984788, by rfl⟩ : syracuseStep 1313051 = 1969577) B1969577
theorem B1968425 : Blo 872567 1968425 := bstep (se 2 (by rfl) ⟨738159, by rfl⟩ : syracuseStep 1968425 = 1476319) B1476319
theorem B985423 : Blo 872567 985423 := bstep (se 1 (by rfl) ⟨739067, by rfl⟩ : syracuseStep 985423 = 1478135) B1478135
theorem B2951639 : Blo 872567 2951639 := bstep (se 1 (by rfl) ⟨2213729, by rfl⟩ : syracuseStep 2951639 = 4427459) B4427459
theorem B16779757 : Blo 872567 16779757 := bstep (se 3 (by rfl) ⟨3146204, by rfl⟩ : syracuseStep 16779757 = 6292409) B6292409
theorem B1313375 : Blo 872567 1313375 := bstep (se 1 (by rfl) ⟨985031, by rfl⟩ : syracuseStep 1313375 = 1970063) B1970063
theorem B11504339 : Blo 872567 11504339 := bstep (se 1 (by rfl) ⟨8628254, by rfl⟩ : syracuseStep 11504339 = 17256509) B17256509
theorem B3148627 : Blo 872567 3148627 := bstep (se 1 (by rfl) ⟨2361470, by rfl⟩ : syracuseStep 3148627 = 4722941) B4722941
theorem B1969001 : Blo 872567 1969001 := bstep (se 2 (by rfl) ⟨738375, by rfl⟩ : syracuseStep 1969001 = 1476751) B1476751
theorem B1313657 : Blo 872567 1313657 := bstep (se 2 (by rfl) ⟨492621, by rfl⟩ : syracuseStep 1313657 = 985243) B985243
theorem B1969055 : Blo 872567 1969055 := bstep (se 1 (by rfl) ⟨1476791, by rfl⟩ : syracuseStep 1969055 = 2953583) B2953583
theorem B1313705 : Blo 872567 1313705 := bstep (se 2 (by rfl) ⟨492639, by rfl⟩ : syracuseStep 1313705 = 985279) B985279
theorem B986107 : Blo 872567 986107 := bstep (se 1 (by rfl) ⟨739580, by rfl⟩ : syracuseStep 986107 = 1479161) B1479161
theorem B1313855 : Blo 872567 1313855 := bstep (se 1 (by rfl) ⟨985391, by rfl⟩ : syracuseStep 1313855 = 1970783) B1970783
theorem B1772921 : Blo 872567 1772921 := bstep (se 2 (by rfl) ⟨664845, by rfl⟩ : syracuseStep 1772921 = 1329691) B1329691
theorem B2985551 : Blo 872567 2985551 := bstep (se 1 (by rfl) ⟨2239163, by rfl⟩ : syracuseStep 2985551 = 4478327) B4478327
theorem B1314407 : Blo 872567 1314407 := bstep (se 1 (by rfl) ⟨985805, by rfl⟩ : syracuseStep 1314407 = 1971611) B1971611
theorem B1969991 : Blo 872567 1969991 := bstep (se 1 (by rfl) ⟨1477493, by rfl⟩ : syracuseStep 1969991 = 2954987) B2954987
theorem B1314791 : Blo 872567 1314791 := bstep (se 1 (by rfl) ⟨986093, by rfl⟩ : syracuseStep 1314791 = 1972187) B1972187
theorem B1970171 : Blo 872567 1970171 := bstep (se 1 (by rfl) ⟨1477628, by rfl⟩ : syracuseStep 1970171 = 2955257) B2955257
theorem B1871867 : Blo 872567 1871867 := bstep (se 1 (by rfl) ⟨1403900, by rfl⟩ : syracuseStep 1871867 = 2807801) B2807801
theorem B15142955 : Blo 872567 15142955 := bstep (se 1 (by rfl) ⟨11357216, by rfl⟩ : syracuseStep 15142955 = 22714433) B22714433
theorem B12587075 : Blo 872567 12587075 := bstep (se 1 (by rfl) ⟨9440306, by rfl⟩ : syracuseStep 12587075 = 18880613) B18880613
theorem B1970279 : Blo 872567 1970279 := bstep (se 1 (by rfl) ⟨1477709, by rfl⟩ : syracuseStep 1970279 = 2955419) B2955419
theorem B30249065 : Blo 872567 30249065 := bstep (se 2 (by rfl) ⟨11343399, by rfl⟩ : syracuseStep 30249065 = 22686799) B22686799
theorem B1970351 : Blo 872567 1970351 := bstep (se 1 (by rfl) ⟨1477763, by rfl⟩ : syracuseStep 1970351 = 2955527) B2955527
theorem B96932213 : Blo 872567 96932213 := bstep (se 5 (by rfl) ⟨4543697, by rfl⟩ : syracuseStep 96932213 = 9087395) B9087395
theorem B7967119 : Blo 872567 7967119 := bstep (se 1 (by rfl) ⟨5975339, by rfl⟩ : syracuseStep 7967119 = 11950679) B11950679
theorem B3740215 : Blo 872567 3740215 := bstep (se 1 (by rfl) ⟨2805161, by rfl⟩ : syracuseStep 3740215 = 5610323) B5610323
theorem B3314429 : Blo 872567 3314429 := bstep (se 3 (by rfl) ⟨621455, by rfl⟩ : syracuseStep 3314429 = 1242911) B1242911
theorem B4264787 : Blo 872567 4264787 := bstep (se 1 (by rfl) ⟨3198590, by rfl⟩ : syracuseStep 4264787 = 6397181) B6397181
theorem B1971035 : Blo 872567 1971035 := bstep (se 1 (by rfl) ⟨1478276, by rfl⟩ : syracuseStep 1971035 = 2956553) B2956553
theorem B4985995 : Blo 872567 4985995 := bstep (se 1 (by rfl) ⟨3739496, by rfl⟩ : syracuseStep 4985995 = 7478993) B7478993
theorem B2954447 : Blo 872567 2954447 := bstep (se 1 (by rfl) ⟨2215835, by rfl⟩ : syracuseStep 2954447 = 4431671) B4431671
theorem B2659625 : Blo 872567 2659625 := bstep (se 2 (by rfl) ⟨997359, by rfl⟩ : syracuseStep 2659625 = 1994719) B1994719
theorem B10098029 : Blo 872567 10098029 := bstep (se 3 (by rfl) ⟨1893380, by rfl⟩ : syracuseStep 10098029 = 3786761) B3786761
theorem B12588509 : Blo 872567 12588509 := bstep (se 3 (by rfl) ⟨2360345, by rfl⟩ : syracuseStep 12588509 = 4720691) B4720691
theorem B1971791 : Blo 872567 1971791 := bstep (se 1 (by rfl) ⟨1478843, by rfl⟩ : syracuseStep 1971791 = 2957687) B2957687
theorem B2365147 : Blo 872567 2365147 := bstep (se 1 (by rfl) ⟨1773860, by rfl⟩ : syracuseStep 2365147 = 3547721) B3547721
theorem B4429727 : Blo 872567 4429727 := bstep (se 1 (by rfl) ⟨3322295, by rfl⟩ : syracuseStep 4429727 = 6644591) B6644591
theorem B3741821 : Blo 872567 3741821 := bstep (se 3 (by rfl) ⟨701591, by rfl⟩ : syracuseStep 3741821 = 1403183) B1403183
theorem B2103583 : Blo 872567 2103583 := bstep (se 1 (by rfl) ⟨1577687, by rfl⟩ : syracuseStep 2103583 = 3155375) B3155375
theorem B2955959 : Blo 872567 2955959 := bstep (se 1 (by rfl) ⟨2216969, by rfl⟩ : syracuseStep 2955959 = 4433939) B4433939
theorem B102112001 : Blo 872567 102112001 := bstep (se 2 (by rfl) ⟨38292000, by rfl⟩ : syracuseStep 102112001 = 76584001) B76584001
theorem B2366489 : Blo 872567 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B24288473 : Blo 872567 24288473 := bstep (se 2 (by rfl) ⟨9108177, by rfl⟩ : syracuseStep 24288473 = 18216355) B18216355
theorem B2661703 : Blo 872567 2661703 := bstep (se 1 (by rfl) ⟨1996277, by rfl⟩ : syracuseStep 2661703 = 3992555) B3992555
theorem B3153761 : Blo 872567 3153761 := bstep (se 2 (by rfl) ⟨1182660, by rfl⟩ : syracuseStep 3153761 = 2365321) B2365321
theorem B2105227 : Blo 872567 2105227 := bstep (se 1 (by rfl) ⟨1578920, by rfl⟩ : syracuseStep 2105227 = 3157841) B3157841
theorem B64627229 : Blo 872567 64627229 := bstep (se 3 (by rfl) ⟨12117605, by rfl⟩ : syracuseStep 64627229 = 24235211) B24235211
theorem B4990369 : Blo 872567 4990369 := bstep (se 2 (by rfl) ⟨1871388, by rfl⟩ : syracuseStep 4990369 = 3742777) B3742777
theorem B20227913 : Blo 872567 20227913 := bstep (se 2 (by rfl) ⟨7585467, by rfl⟩ : syracuseStep 20227913 = 15170935) B15170935
theorem B64563077 : Blo 872567 64563077 := bstep (se 4 (by rfl) ⟨6052788, by rfl⟩ : syracuseStep 64563077 = 12105577) B12105577
theorem B3319775 : Blo 872567 3319775 := bstep (se 1 (by rfl) ⟨2489831, by rfl⟩ : syracuseStep 3319775 = 4979663) B4979663
theorem B4434911 : Blo 872567 4434911 := bstep (se 1 (by rfl) ⟨3326183, by rfl⟩ : syracuseStep 4434911 = 6652367) B6652367
theorem B6630497 : Blo 872567 6630497 := bstep (se 2 (by rfl) ⟨2486436, by rfl⟩ : syracuseStep 6630497 = 4972873) B4972873
theorem B60599501 : Blo 872567 60599501 := bstep (se 3 (by rfl) ⟨11362406, by rfl⟩ : syracuseStep 60599501 = 22724813) B22724813
theorem B7482617 : Blo 872567 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B9940643 : Blo 872567 9940643 := bstep (se 1 (by rfl) ⟨7455482, by rfl⟩ : syracuseStep 9940643 = 14910965) B14910965
theorem B5320511 : Blo 872567 5320511 := bstep (se 1 (by rfl) ⟨3990383, by rfl⟩ : syracuseStep 5320511 = 7980767) B7980767
theorem B107720603 : Blo 872567 107720603 := bstep (se 1 (by rfl) ⟨80790452, by rfl⟩ : syracuseStep 107720603 = 161580905) B161580905
theorem B14954705 : Blo 872567 14954705 := bstep (se 2 (by rfl) ⟨5608014, by rfl⟩ : syracuseStep 14954705 = 11216029) B11216029
theorem B31928903 : Blo 872567 31928903 := bstep (se 1 (by rfl) ⟨23946677, by rfl⟩ : syracuseStep 31928903 = 47893355) B47893355
theorem B4436855 : Blo 872567 4436855 := bstep (se 1 (by rfl) ⟨3327641, by rfl⟩ : syracuseStep 4436855 = 6655283) B6655283
theorem B3322889 : Blo 872567 3322889 := bstep (se 2 (by rfl) ⟨1246083, by rfl⟩ : syracuseStep 3322889 = 2492167) B2492167
theorem B2208809 : Blo 872567 2208809 := bstep (se 2 (by rfl) ⟨828303, by rfl⟩ : syracuseStep 2208809 = 1656607) B1656607
theorem B3323389 : Blo 872567 3323389 := bstep (se 3 (by rfl) ⟨623135, by rfl⟩ : syracuseStep 3323389 = 1246271) B1246271
theorem B6305303 : Blo 872567 6305303 := bstep (se 1 (by rfl) ⟨4728977, by rfl⟩ : syracuseStep 6305303 = 9457955) B9457955
theorem B12760685 : Blo 872567 12760685 := bstep (se 3 (by rfl) ⟨2392628, by rfl⟩ : syracuseStep 12760685 = 4785257) B4785257
theorem B3651655 : Blo 872567 3651655 := bstep (se 1 (by rfl) ⟨2738741, by rfl⟩ : syracuseStep 3651655 = 5477483) B5477483
theorem B2799755 : Blo 872567 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B4209241 : Blo 872567 4209241 := bstep (se 2 (by rfl) ⟨1578465, by rfl⟩ : syracuseStep 4209241 = 3156931) B3156931
theorem B2211047 : Blo 872567 2211047 := bstep (se 1 (by rfl) ⟨1658285, by rfl⟩ : syracuseStep 2211047 = 3316571) B3316571
theorem B6634871 : Blo 872567 6634871 := bstep (se 1 (by rfl) ⟨4976153, by rfl⟩ : syracuseStep 6634871 = 9952307) B9952307
theorem B10108759 : Blo 872567 10108759 := bstep (se 1 (by rfl) ⟨7581569, by rfl⟩ : syracuseStep 10108759 = 15163139) B15163139
theorem B7487741 : Blo 872567 7487741 := bstep (se 3 (by rfl) ⟨1403951, by rfl⟩ : syracuseStep 7487741 = 2807903) B2807903
theorem B3326305 : Blo 872567 3326305 := bstep (se 2 (by rfl) ⟨1247364, by rfl⟩ : syracuseStep 3326305 = 2494729) B2494729
theorem B16794215 : Blo 872567 16794215 := bstep (se 1 (by rfl) ⟨12595661, by rfl⟩ : syracuseStep 16794215 = 25191323) B25191323
theorem B7455347 : Blo 872567 7455347 := bstep (se 1 (by rfl) ⟨5591510, by rfl⟩ : syracuseStep 7455347 = 11183021) B11183021
theorem B3326579 : Blo 872567 3326579 := bstep (se 1 (by rfl) ⟨2494934, by rfl⟩ : syracuseStep 3326579 = 4989869) B4989869
theorem B2212859 : Blo 872567 2212859 := bstep (se 1 (by rfl) ⟨1659644, by rfl⟩ : syracuseStep 2212859 = 3319289) B3319289
theorem B6308903 : Blo 872567 6308903 := bstep (se 1 (by rfl) ⟨4731677, by rfl⟩ : syracuseStep 6308903 = 9463355) B9463355
theorem B3327551 : Blo 872567 3327551 := bstep (se 1 (by rfl) ⟨2495663, by rfl⟩ : syracuseStep 3327551 = 4991327) B4991327
theorem B1328815 : Blo 872567 1328815 := bstep (se 1 (by rfl) ⟨996611, by rfl⟩ : syracuseStep 1328815 = 1993223) B1993223
theorem B55428907 : Blo 872567 55428907 := bstep (se 1 (by rfl) ⟨41571680, by rfl⟩ : syracuseStep 55428907 = 83143361) B83143361
theorem B8406949 : Blo 872567 8406949 := bstep (se 4 (by rfl) ⟨788151, by rfl⟩ : syracuseStep 8406949 = 1576303) B1576303
theorem B21317843 : Blo 872567 21317843 := bstep (se 1 (by rfl) ⟨15988382, by rfl⟩ : syracuseStep 21317843 = 31976765) B31976765
theorem B2018087 : Blo 872567 2018087 := bstep (se 1 (by rfl) ⟨1513565, by rfl⟩ : syracuseStep 2018087 = 3027131) B3027131
theorem B6737039 : Blo 872567 6737039 := bstep (se 1 (by rfl) ⟨5052779, by rfl⟩ : syracuseStep 6737039 = 10105559) B10105559
theorem B25546711 : Blo 872567 25546711 := bstep (se 1 (by rfl) ⟨19160033, by rfl⟩ : syracuseStep 25546711 = 38320067) B38320067
theorem B1658855 : Blo 872567 1658855 := bstep (se 1 (by rfl) ⟨1244141, by rfl⟩ : syracuseStep 1658855 = 2488283) B2488283
theorem B872575 : Blo 872567 872575 := bstep (se 1 (by rfl) ⟨654431, by rfl⟩ : syracuseStep 872575 = 1308863) B1308863
theorem B872603 : Blo 872567 872603 := bstep (se 1 (by rfl) ⟨654452, by rfl⟩ : syracuseStep 872603 = 1308905) B1308905
theorem B872807 : Blo 872567 872807 := bstep (se 1 (by rfl) ⟨654605, by rfl⟩ : syracuseStep 872807 = 1309211) B1309211
theorem B872859 : Blo 872567 872859 := bstep (se 1 (by rfl) ⟨654644, by rfl⟩ : syracuseStep 872859 = 1309289) B1309289
theorem B6640217 : Blo 872567 6640217 := bstep (se 2 (by rfl) ⟨2490081, by rfl⟩ : syracuseStep 6640217 = 4980163) B4980163
theorem B2216585 : Blo 872567 2216585 := bstep (se 2 (by rfl) ⟨831219, by rfl⟩ : syracuseStep 2216585 = 1662439) B1662439
theorem B6312593 : Blo 872567 6312593 := bstep (se 2 (by rfl) ⟨2367222, by rfl⟩ : syracuseStep 6312593 = 4734445) B4734445
theorem B873211 : Blo 872567 873211 := bstep (se 1 (by rfl) ⟨654908, by rfl⟩ : syracuseStep 873211 = 1309817) B1309817
theorem B57398057 : Blo 872567 57398057 := bstep (se 2 (by rfl) ⟨21524271, by rfl⟩ : syracuseStep 57398057 = 43048543) B43048543
theorem B873279 : Blo 872567 873279 := bstep (se 1 (by rfl) ⟨654959, by rfl⟩ : syracuseStep 873279 = 1309919) B1309919
theorem B873307 : Blo 872567 873307 := bstep (se 1 (by rfl) ⟨654980, by rfl⟩ : syracuseStep 873307 = 1309961) B1309961
theorem B873375 : Blo 872567 873375 := bstep (se 1 (by rfl) ⟨655031, by rfl⟩ : syracuseStep 873375 = 1310063) B1310063
theorem B5592023 : Blo 872567 5592023 := bstep (se 1 (by rfl) ⟨4194017, by rfl⟩ : syracuseStep 5592023 = 8388035) B8388035
theorem B2216929 : Blo 872567 2216929 := bstep (se 2 (by rfl) ⟨831348, by rfl⟩ : syracuseStep 2216929 = 1662697) B1662697
theorem B873455 : Blo 872567 873455 := bstep (se 1 (by rfl) ⟨655091, by rfl⟩ : syracuseStep 873455 = 1310183) B1310183
theorem B873543 : Blo 872567 873543 := bstep (se 1 (by rfl) ⟨655157, by rfl⟩ : syracuseStep 873543 = 1310315) B1310315
theorem B873627 : Blo 872567 873627 := bstep (se 1 (by rfl) ⟨655220, by rfl⟩ : syracuseStep 873627 = 1310441) B1310441
theorem B873723 : Blo 872567 873723 := bstep (se 1 (by rfl) ⟨655292, by rfl⟩ : syracuseStep 873723 = 1310585) B1310585
theorem B873791 : Blo 872567 873791 := bstep (se 1 (by rfl) ⟨655343, by rfl⟩ : syracuseStep 873791 = 1310687) B1310687
theorem B873959 : Blo 872567 873959 := bstep (se 1 (by rfl) ⟨655469, by rfl⟩ : syracuseStep 873959 = 1310939) B1310939
theorem B873967 : Blo 872567 873967 := bstep (se 1 (by rfl) ⟨655475, by rfl⟩ : syracuseStep 873967 = 1310951) B1310951
theorem B874075 : Blo 872567 874075 := bstep (se 1 (by rfl) ⟨655556, by rfl⟩ : syracuseStep 874075 = 1311113) B1311113
theorem B874139 : Blo 872567 874139 := bstep (se 1 (by rfl) ⟨655604, by rfl⟩ : syracuseStep 874139 = 1311209) B1311209
theorem B1660571 : Blo 872567 1660571 := bstep (se 1 (by rfl) ⟨1245428, by rfl⟩ : syracuseStep 1660571 = 2490857) B2490857
theorem B874223 : Blo 872567 874223 := bstep (se 1 (by rfl) ⟨655667, by rfl⟩ : syracuseStep 874223 = 1311335) B1311335
theorem B874311 : Blo 872567 874311 := bstep (se 1 (by rfl) ⟨655733, by rfl⟩ : syracuseStep 874311 = 1311467) B1311467
theorem B874331 : Blo 872567 874331 := bstep (se 1 (by rfl) ⟨655748, by rfl⟩ : syracuseStep 874331 = 1311497) B1311497
theorem B874399 : Blo 872567 874399 := bstep (se 1 (by rfl) ⟨655799, by rfl⟩ : syracuseStep 874399 = 1311599) B1311599
theorem B874567 : Blo 872567 874567 := bstep (se 1 (by rfl) ⟨655925, by rfl⟩ : syracuseStep 874567 = 1311851) B1311851
theorem B3987539 : Blo 872567 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B874727 : Blo 872567 874727 := bstep (se 1 (by rfl) ⟨656045, by rfl⟩ : syracuseStep 874727 = 1312091) B1312091
theorem B2218337 : Blo 872567 2218337 := bstep (se 2 (by rfl) ⟨831876, by rfl⟩ : syracuseStep 2218337 = 1663753) B1663753
theorem B874911 : Blo 872567 874911 := bstep (se 1 (by rfl) ⟨656183, by rfl⟩ : syracuseStep 874911 = 1312367) B1312367
theorem B874959 : Blo 872567 874959 := bstep (se 1 (by rfl) ⟨656219, by rfl⟩ : syracuseStep 874959 = 1312439) B1312439
theorem B874983 : Blo 872567 874983 := bstep (se 1 (by rfl) ⟨656237, by rfl⟩ : syracuseStep 874983 = 1312475) B1312475
theorem B1661467 : Blo 872567 1661467 := bstep (se 1 (by rfl) ⟨1246100, by rfl⟩ : syracuseStep 1661467 = 2492201) B2492201
theorem B875099 : Blo 872567 875099 := bstep (se 1 (by rfl) ⟨656324, by rfl⟩ : syracuseStep 875099 = 1312649) B1312649
theorem B875167 : Blo 872567 875167 := bstep (se 1 (by rfl) ⟨656375, by rfl⟩ : syracuseStep 875167 = 1312751) B1312751
theorem B875335 : Blo 872567 875335 := bstep (se 1 (by rfl) ⟨656501, by rfl⟩ : syracuseStep 875335 = 1313003) B1313003
theorem B875375 : Blo 872567 875375 := bstep (se 1 (by rfl) ⟨656531, by rfl⟩ : syracuseStep 875375 = 1313063) B1313063
theorem B875431 : Blo 872567 875431 := bstep (se 1 (by rfl) ⟨656573, by rfl⟩ : syracuseStep 875431 = 1313147) B1313147
theorem B875611 : Blo 872567 875611 := bstep (se 1 (by rfl) ⟨656708, by rfl⟩ : syracuseStep 875611 = 1313417) B1313417
theorem B1105103 : Blo 872567 1105103 := bstep (se 1 (by rfl) ⟨828827, by rfl⟩ : syracuseStep 1105103 = 1657655) B1657655
theorem B875727 : Blo 872567 875727 := bstep (se 1 (by rfl) ⟨656795, by rfl⟩ : syracuseStep 875727 = 1313591) B1313591
theorem B875751 : Blo 872567 875751 := bstep (se 1 (by rfl) ⟨656813, by rfl⟩ : syracuseStep 875751 = 1313627) B1313627
theorem B875847 : Blo 872567 875847 := bstep (se 1 (by rfl) ⟨656885, by rfl⟩ : syracuseStep 875847 = 1313771) B1313771
theorem B875983 : Blo 872567 875983 := bstep (se 1 (by rfl) ⟨656987, by rfl⟩ : syracuseStep 875983 = 1313975) B1313975
theorem B876143 : Blo 872567 876143 := bstep (se 1 (by rfl) ⟨657107, by rfl⟩ : syracuseStep 876143 = 1314215) B1314215
theorem B5594791 : Blo 872567 5594791 := bstep (se 1 (by rfl) ⟨4196093, by rfl⟩ : syracuseStep 5594791 = 8392187) B8392187
theorem B876199 : Blo 872567 876199 := bstep (se 1 (by rfl) ⟨657149, by rfl⟩ : syracuseStep 876199 = 1314299) B1314299
theorem B876263 : Blo 872567 876263 := bstep (se 1 (by rfl) ⟨657197, by rfl⟩ : syracuseStep 876263 = 1314395) B1314395
theorem B876319 : Blo 872567 876319 := bstep (se 1 (by rfl) ⟨657239, by rfl⟩ : syracuseStep 876319 = 1314479) B1314479
theorem B876399 : Blo 872567 876399 := bstep (se 1 (by rfl) ⟨657299, by rfl⟩ : syracuseStep 876399 = 1314599) B1314599
theorem B876455 : Blo 872567 876455 := bstep (se 1 (by rfl) ⟨657341, by rfl⟩ : syracuseStep 876455 = 1314683) B1314683
theorem B8314807 : Blo 872567 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B4972691 : Blo 872567 4972691 := bstep (se 1 (by rfl) ⟨3729518, by rfl⟩ : syracuseStep 4972691 = 7459037) B7459037
theorem B1663183 : Blo 872567 1663183 := bstep (se 1 (by rfl) ⟨1247387, by rfl⟩ : syracuseStep 1663183 = 2494775) B2494775
theorem B6644105 : Blo 872567 6644105 := bstep (se 2 (by rfl) ⟨2491539, by rfl⟩ : syracuseStep 6644105 = 4983079) B4983079
theorem B1663571 : Blo 872567 1663571 := bstep (se 1 (by rfl) ⟨1247678, by rfl⟩ : syracuseStep 1663571 = 2495357) B2495357
theorem B28730861 : Blo 872567 28730861 := bstep (se 3 (by rfl) ⟨5387036, by rfl⟩ : syracuseStep 28730861 = 10774073) B10774073
theorem B4974331 : Blo 872567 4974331 := bstep (se 1 (by rfl) ⟨3730748, by rfl⟩ : syracuseStep 4974331 = 7461497) B7461497
theorem B8415713 : Blo 872567 8415713 := bstep (se 2 (by rfl) ⟨3155892, by rfl⟩ : syracuseStep 8415713 = 6311785) B6311785
theorem B1010279 : Blo 872567 1010279 := bstep (se 1 (by rfl) ⟨757709, by rfl⟩ : syracuseStep 1010279 = 1515419) B1515419
theorem B7105171 : Blo 872567 7105171 := bstep (se 1 (by rfl) ⟨5328878, by rfl⟩ : syracuseStep 7105171 = 10657757) B10657757
theorem B16804907 : Blo 872567 16804907 := bstep (se 1 (by rfl) ⟨12603680, by rfl⟩ : syracuseStep 16804907 = 25207361) B25207361
theorem B14937209 : Blo 872567 14937209 := bstep (se 2 (by rfl) ⟨5601453, by rfl⟩ : syracuseStep 14937209 = 11202907) B11202907
theorem B8416943 : Blo 872567 8416943 := bstep (se 1 (by rfl) ⟨6312707, by rfl⟩ : syracuseStep 8416943 = 12625415) B12625415
theorem B16772993 : Blo 872567 16772993 := bstep (se 2 (by rfl) ⟨6289872, by rfl⟩ : syracuseStep 16772993 = 12579745) B12579745
theorem B45412235 : Blo 872567 45412235 := bstep (se 1 (by rfl) ⟨34059176, by rfl⟩ : syracuseStep 45412235 = 68118353) B68118353
theorem B2486369 : Blo 872567 2486369 := bstep (se 2 (by rfl) ⟨932388, by rfl⟩ : syracuseStep 2486369 = 1864777) B1864777
theorem B4977247 : Blo 872567 4977247 := bstep (se 1 (by rfl) ⟨3732935, by rfl⟩ : syracuseStep 4977247 = 7465871) B7465871
theorem B7467785 : Blo 872567 7467785 := bstep (se 2 (by rfl) ⟨2800419, by rfl⟩ : syracuseStep 7467785 = 5600839) B5600839
theorem B1864615 : Blo 872567 1864615 := bstep (se 1 (by rfl) ⟨1398461, by rfl⟩ : syracuseStep 1864615 = 2796923) B2796923
theorem B2946131 : Blo 872567 2946131 := bstep (se 1 (by rfl) ⟨2209598, by rfl⟩ : syracuseStep 2946131 = 4419197) B4419197
theorem B3732799 : Blo 872567 3732799 := bstep (se 1 (by rfl) ⟨2799599, by rfl⟩ : syracuseStep 3732799 = 5599199) B5599199
theorem B1865033 : Blo 872567 1865033 := bstep (se 2 (by rfl) ⟨699387, by rfl⟩ : syracuseStep 1865033 = 1398775) B1398775
theorem B1996105 : Blo 872567 1996105 := bstep (se 2 (by rfl) ⟨748539, by rfl⟩ : syracuseStep 1996105 = 1497079) B1497079
theorem B1242535 : Blo 872567 1242535 := bstep (se 1 (by rfl) ⟨931901, by rfl⟩ : syracuseStep 1242535 = 1863803) B1863803
theorem B1963475 : Blo 872567 1963475 := bstep (se 1 (by rfl) ⟨1472606, by rfl⟩ : syracuseStep 1963475 = 2945213) B2945213
theorem B2487827 : Blo 872567 2487827 := bstep (se 1 (by rfl) ⟨1865870, by rfl⟩ : syracuseStep 2487827 = 3731741) B3731741
theorem B2946671 : Blo 872567 2946671 := bstep (se 1 (by rfl) ⟨2210003, by rfl⟩ : syracuseStep 2946671 = 4420007) B4420007
theorem B1963745 : Blo 872567 1963745 := bstep (se 2 (by rfl) ⟨736404, by rfl⟩ : syracuseStep 1963745 = 1472809) B1472809
theorem B25261901 : Blo 872567 25261901 := bstep (se 3 (by rfl) ⟨4736606, by rfl⟩ : syracuseStep 25261901 = 9473213) B9473213
theorem B1964267 : Blo 872567 1964267 := bstep (se 1 (by rfl) ⟨1473200, by rfl⟩ : syracuseStep 1964267 = 2946401) B2946401
theorem B1309127 : Blo 872567 1309127 := bstep (se 1 (by rfl) ⟨981845, by rfl⟩ : syracuseStep 1309127 = 1963691) B1963691
theorem B2947535 : Blo 872567 2947535 := bstep (se 1 (by rfl) ⟨2210651, by rfl⟩ : syracuseStep 2947535 = 4421303) B4421303
theorem B4422113 : Blo 872567 4422113 := bstep (se 2 (by rfl) ⟨1658292, by rfl⟩ : syracuseStep 4422113 = 3316585) B3316585
theorem B1866331 : Blo 872567 1866331 := bstep (se 1 (by rfl) ⟨1399748, by rfl⟩ : syracuseStep 1866331 = 2799497) B2799497
theorem B1473167 : Blo 872567 1473167 := bstep (se 1 (by rfl) ⟨1104875, by rfl⟩ : syracuseStep 1473167 = 2209751) B2209751
theorem B1309343 : Blo 872567 1309343 := bstep (se 1 (by rfl) ⟨982007, by rfl⟩ : syracuseStep 1309343 = 1964015) B1964015
theorem B1309487 : Blo 872567 1309487 := bstep (se 1 (by rfl) ⟨982115, by rfl⟩ : syracuseStep 1309487 = 1964231) B1964231
theorem B1309607 : Blo 872567 1309607 := bstep (se 1 (by rfl) ⟨982205, by rfl⟩ : syracuseStep 1309607 = 1964411) B1964411
theorem B1309787 : Blo 872567 1309787 := bstep (se 1 (by rfl) ⟨982340, by rfl⟩ : syracuseStep 1309787 = 1964681) B1964681
theorem B1310159 : Blo 872567 1310159 := bstep (se 1 (by rfl) ⟨982619, by rfl⟩ : syracuseStep 1310159 = 1965239) B1965239
theorem B1965563 : Blo 872567 1965563 := bstep (se 1 (by rfl) ⟨1474172, by rfl⟩ : syracuseStep 1965563 = 2948345) B2948345
theorem B1474159 : Blo 872567 1474159 := bstep (se 1 (by rfl) ⟨1105619, by rfl⟩ : syracuseStep 1474159 = 2211239) B2211239
theorem B1965743 : Blo 872567 1965743 := bstep (se 1 (by rfl) ⟨1474307, by rfl⟩ : syracuseStep 1965743 = 2948615) B2948615
theorem B982759 : Blo 872567 982759 := bstep (se 1 (by rfl) ⟨737069, by rfl⟩ : syracuseStep 982759 = 1474139) B1474139
theorem B1965833 : Blo 872567 1965833 := bstep (se 2 (by rfl) ⟨737187, by rfl⟩ : syracuseStep 1965833 = 1474375) B1474375
theorem B1048351 : Blo 872567 1048351 := bstep (se 1 (by rfl) ⟨786263, by rfl⟩ : syracuseStep 1048351 = 1572527) B1572527
theorem B1310543 : Blo 872567 1310543 := bstep (se 1 (by rfl) ⟨982907, by rfl⟩ : syracuseStep 1310543 = 1965815) B1965815
theorem B1245007 : Blo 872567 1245007 := bstep (se 1 (by rfl) ⟨933755, by rfl⟩ : syracuseStep 1245007 = 1867511) B1867511
theorem B2129831 : Blo 872567 2129831 := bstep (se 1 (by rfl) ⟨1597373, by rfl⟩ : syracuseStep 2129831 = 3194747) B3194747
theorem B1310663 : Blo 872567 1310663 := bstep (se 1 (by rfl) ⟨982997, by rfl⟩ : syracuseStep 1310663 = 1965995) B1965995
theorem B1245127 : Blo 872567 1245127 := bstep (se 1 (by rfl) ⟨933845, by rfl⟩ : syracuseStep 1245127 = 1867691) B1867691
theorem B1310975 : Blo 872567 1310975 := bstep (se 1 (by rfl) ⟨983231, by rfl⟩ : syracuseStep 1310975 = 1966463) B1966463
theorem B1311131 : Blo 872567 1311131 := bstep (se 1 (by rfl) ⟨983348, by rfl⟩ : syracuseStep 1311131 = 1966697) B1966697
theorem B1475239 : Blo 872567 1475239 := bstep (se 1 (by rfl) ⟨1106429, by rfl⟩ : syracuseStep 1475239 = 2212859) B2212859
theorem B1311551 : Blo 872567 1311551 := bstep (se 1 (by rfl) ⟨983663, by rfl⟩ : syracuseStep 1311551 = 1967327) B1967327
theorem B2491199 : Blo 872567 2491199 := bstep (se 1 (by rfl) ⟨1868399, by rfl⟩ : syracuseStep 2491199 = 3736799) B3736799
theorem B1311695 : Blo 872567 1311695 := bstep (se 1 (by rfl) ⟨983771, by rfl⟩ : syracuseStep 1311695 = 1967543) B1967543
theorem B1311785 : Blo 872567 1311785 := bstep (se 2 (by rfl) ⟨491919, by rfl⟩ : syracuseStep 1311785 = 983839) B983839
theorem B1311815 : Blo 872567 1311815 := bstep (se 1 (by rfl) ⟨983861, by rfl⟩ : syracuseStep 1311815 = 1967723) B1967723
theorem B1311995 : Blo 872567 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B1312283 : Blo 872567 1312283 := bstep (se 1 (by rfl) ⟨984212, by rfl⟩ : syracuseStep 1312283 = 1968425) B1968425
theorem B1967759 : Blo 872567 1967759 := bstep (se 1 (by rfl) ⟨1475819, by rfl⟩ : syracuseStep 1967759 = 2951639) B2951639
theorem B1967849 : Blo 872567 1967849 := bstep (se 2 (by rfl) ⟨737943, by rfl⟩ : syracuseStep 1967849 = 1475887) B1475887
theorem B7669559 : Blo 872567 7669559 := bstep (se 1 (by rfl) ⟨5752169, by rfl⟩ : syracuseStep 7669559 = 11504339) B11504339
theorem B1345391 : Blo 872567 1345391 := bstep (se 1 (by rfl) ⟨1009043, by rfl⟩ : syracuseStep 1345391 = 2018087) B2018087
theorem B6653825 : Blo 872567 6653825 := bstep (se 2 (by rfl) ⟨2495184, by rfl⟩ : syracuseStep 6653825 = 4990369) B4990369
theorem B1312667 : Blo 872567 1312667 := bstep (se 1 (by rfl) ⟨984500, by rfl⟩ : syracuseStep 1312667 = 1969001) B1969001
theorem B1312703 : Blo 872567 1312703 := bstep (se 1 (by rfl) ⟨984527, by rfl⟩ : syracuseStep 1312703 = 1969055) B1969055
theorem B4491359 : Blo 872567 4491359 := bstep (se 1 (by rfl) ⟨3368519, by rfl⟩ : syracuseStep 4491359 = 6737039) B6737039
theorem B1771753 : Blo 872567 1771753 := bstep (se 2 (by rfl) ⟨664407, by rfl⟩ : syracuseStep 1771753 = 1328815) B1328815
theorem B1181947 : Blo 872567 1181947 := bstep (se 1 (by rfl) ⟨886460, by rfl⟩ : syracuseStep 1181947 = 1772921) B1772921
theorem B1313327 : Blo 872567 1313327 := bstep (se 1 (by rfl) ⟨984995, by rfl⟩ : syracuseStep 1313327 = 1969991) B1969991
theorem B11209265 : Blo 872567 11209265 := bstep (se 2 (by rfl) ⟨4203474, by rfl⟩ : syracuseStep 11209265 = 8406949) B8406949
theorem B1313447 : Blo 872567 1313447 := bstep (se 1 (by rfl) ⟨985085, by rfl⟩ : syracuseStep 1313447 = 1970171) B1970171
theorem B8391383 : Blo 872567 8391383 := bstep (se 1 (by rfl) ⟨6293537, by rfl⟩ : syracuseStep 8391383 = 12587075) B12587075
theorem B1313513 : Blo 872567 1313513 := bstep (se 2 (by rfl) ⟨492567, by rfl⟩ : syracuseStep 1313513 = 985135) B985135
theorem B1313519 : Blo 872567 1313519 := bstep (se 1 (by rfl) ⟨985139, by rfl⟩ : syracuseStep 1313519 = 1970279) B1970279
theorem B1313567 : Blo 872567 1313567 := bstep (se 1 (by rfl) ⟨985175, by rfl⟩ : syracuseStep 1313567 = 1970351) B1970351
theorem B64621475 : Blo 872567 64621475 := bstep (se 1 (by rfl) ⟨48466106, by rfl⟩ : syracuseStep 64621475 = 96932213) B96932213
theorem B4426811 : Blo 872567 4426811 := bstep (se 1 (by rfl) ⟨3320108, by rfl⟩ : syracuseStep 4426811 = 6640217) B6640217
theorem B1477723 : Blo 872567 1477723 := bstep (se 1 (by rfl) ⟨1108292, by rfl⟩ : syracuseStep 1477723 = 2216585) B2216585
theorem B1313897 : Blo 872567 1313897 := bstep (se 2 (by rfl) ⟨492711, by rfl⟩ : syracuseStep 1313897 = 985423) B985423
theorem B1314023 : Blo 872567 1314023 := bstep (se 1 (by rfl) ⟨985517, by rfl⟩ : syracuseStep 1314023 = 1971035) B1971035
theorem B1969631 : Blo 872567 1969631 := bstep (se 1 (by rfl) ⟨1477223, by rfl⟩ : syracuseStep 1969631 = 2954447) B2954447
theorem B9473561 : Blo 872567 9473561 := bstep (se 2 (by rfl) ⟨3552585, by rfl⟩ : syracuseStep 9473561 = 7105171) B7105171
theorem B1773083 : Blo 872567 1773083 := bstep (se 1 (by rfl) ⟨1329812, by rfl⟩ : syracuseStep 1773083 = 2659625) B2659625
theorem B8392339 : Blo 872567 8392339 := bstep (se 1 (by rfl) ⟨6294254, by rfl⟩ : syracuseStep 8392339 = 12588509) B12588509
theorem B1314527 : Blo 872567 1314527 := bstep (se 1 (by rfl) ⟨985895, by rfl⟩ : syracuseStep 1314527 = 1971791) B1971791
theorem B4198169 : Blo 872567 4198169 := bstep (se 2 (by rfl) ⟨1574313, by rfl⟩ : syracuseStep 4198169 = 3148627) B3148627
theorem B2953151 : Blo 872567 2953151 := bstep (se 1 (by rfl) ⟨2214863, by rfl⟩ : syracuseStep 2953151 = 4429727) B4429727
theorem B1314809 : Blo 872567 1314809 := bstep (se 2 (by rfl) ⟨493053, by rfl⟩ : syracuseStep 1314809 = 986107) B986107
theorem B2658359 : Blo 872567 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B2494547 : Blo 872567 2494547 := bstep (se 1 (by rfl) ⟨1870910, by rfl⟩ : syracuseStep 2494547 = 3741821) B3741821
theorem B1478891 : Blo 872567 1478891 := bstep (se 1 (by rfl) ⟨1109168, by rfl⟩ : syracuseStep 1478891 = 2218337) B2218337
theorem B1970639 : Blo 872567 1970639 := bstep (se 1 (by rfl) ⟨1477979, by rfl⟩ : syracuseStep 1970639 = 2955959) B2955959
theorem B1577659 : Blo 872567 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B16192315 : Blo 872567 16192315 := bstep (se 1 (by rfl) ⟨12144236, by rfl⟩ : syracuseStep 16192315 = 24288473) B24288473
theorem B2102507 : Blo 872567 2102507 := bstep (se 1 (by rfl) ⟨1576880, by rfl⟩ : syracuseStep 2102507 = 3153761) B3153761
theorem B3315127 : Blo 872567 3315127 := bstep (se 1 (by rfl) ⟨2486345, by rfl⟩ : syracuseStep 3315127 = 4972691) B4972691
theorem B4429403 : Blo 872567 4429403 := bstep (se 1 (by rfl) ⟨3322052, by rfl⟩ : syracuseStep 4429403 = 6644105) B6644105
theorem B10622825 : Blo 872567 10622825 := bstep (se 2 (by rfl) ⟨3983559, by rfl⟩ : syracuseStep 10622825 = 7967119) B7967119
theorem B4986953 : Blo 872567 4986953 := bstep (se 2 (by rfl) ⟨1870107, by rfl⟩ : syracuseStep 4986953 = 3740215) B3740215
theorem B2955905 : Blo 872567 2955905 := bstep (se 2 (by rfl) ⟨1108464, by rfl⟩ : syracuseStep 2955905 = 2216929) B2216929
theorem B2694077 : Blo 872567 2694077 := bstep (se 3 (by rfl) ⟨505139, by rfl⟩ : syracuseStep 2694077 = 1010279) B1010279
theorem B5610475 : Blo 872567 5610475 := bstep (se 1 (by rfl) ⟨4207856, by rfl⟩ : syracuseStep 5610475 = 8415713) B8415713
theorem B14195749 : Blo 872567 14195749 := bstep (se 4 (by rfl) ⟨1330851, by rfl⟩ : syracuseStep 14195749 = 2661703) B2661703
theorem B2661473 : Blo 872567 2661473 := bstep (se 2 (by rfl) ⟨998052, by rfl⟩ : syracuseStep 2661473 = 1996105) B1996105
theorem B2956607 : Blo 872567 2956607 := bstep (se 1 (by rfl) ⟨2217455, by rfl⟩ : syracuseStep 2956607 = 4434911) B4434911
theorem B4431185 : Blo 872567 4431185 := bstep (se 2 (by rfl) ⟨1661694, by rfl⟩ : syracuseStep 4431185 = 3323389) B3323389
theorem B4988411 : Blo 872567 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B3153529 : Blo 872567 3153529 := bstep (se 2 (by rfl) ⟨1182573, by rfl⟩ : syracuseStep 3153529 = 2365147) B2365147
theorem B6627095 : Blo 872567 6627095 := bstep (se 1 (by rfl) ⟨4970321, by rfl⟩ : syracuseStep 6627095 = 9940643) B9940643
theorem B5611295 : Blo 872567 5611295 := bstep (se 1 (by rfl) ⟨4208471, by rfl⟩ : syracuseStep 5611295 = 8416943) B8416943
theorem B3547007 : Blo 872567 3547007 := bstep (se 1 (by rfl) ⟨2660255, by rfl⟩ : syracuseStep 3547007 = 5320511) B5320511
theorem B11181995 : Blo 872567 11181995 := bstep (se 1 (by rfl) ⟨8386496, by rfl⟩ : syracuseStep 11181995 = 16772993) B16772993
theorem B9969803 : Blo 872567 9969803 := bstep (se 1 (by rfl) ⟨7477352, by rfl⟩ : syracuseStep 9969803 = 14954705) B14954705
theorem B2957903 : Blo 872567 2957903 := bstep (se 1 (by rfl) ⟨2218427, by rfl⟩ : syracuseStep 2957903 = 4436855) B4436855
theorem B5612321 : Blo 872567 5612321 := bstep (se 2 (by rfl) ⟨2104620, by rfl⟩ : syracuseStep 5612321 = 4209241) B4209241
theorem B4203535 : Blo 872567 4203535 := bstep (se 1 (by rfl) ⟨3152651, by rfl⟩ : syracuseStep 4203535 = 6305303) B6305303
theorem B13478345 : Blo 872567 13478345 := bstep (se 2 (by rfl) ⟨5054379, by rfl⟩ : syracuseStep 13478345 = 10108759) B10108759
theorem B11086409 : Blo 872567 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B1419887 : Blo 872567 1419887 := bstep (se 1 (by rfl) ⟨1064915, by rfl⟩ : syracuseStep 1419887 = 2129831) B2129831
theorem B4991645 : Blo 872567 4991645 := bstep (se 3 (by rfl) ⟨935933, by rfl⟩ : syracuseStep 4991645 = 1871867) B1871867
theorem B40381213 : Blo 872567 40381213 := bstep (se 3 (by rfl) ⟨7571477, by rfl⟩ : syracuseStep 40381213 = 15142955) B15142955
theorem B4991827 : Blo 872567 4991827 := bstep (se 1 (by rfl) ⟨3743870, by rfl⟩ : syracuseStep 4991827 = 7487741) B7487741
theorem B4435073 : Blo 872567 4435073 := bstep (se 2 (by rfl) ⟨1663152, by rfl⟩ : syracuseStep 4435073 = 3326305) B3326305
theorem B4205935 : Blo 872567 4205935 := bstep (se 1 (by rfl) ⟨3154451, by rfl⟩ : syracuseStep 4205935 = 6308903) B6308903
theorem B28422251 : Blo 872567 28422251 := bstep (se 1 (by rfl) ⟨21316688, by rfl⟩ : syracuseStep 28422251 = 42633377) B42633377
theorem B6632441 : Blo 872567 6632441 := bstep (se 2 (by rfl) ⟨2487165, by rfl⟩ : syracuseStep 6632441 = 4974331) B4974331
theorem B73905209 : Blo 872567 73905209 := bstep (se 2 (by rfl) ⟨27714453, by rfl⟩ : syracuseStep 73905209 = 55428907) B55428907
theorem B20166043 : Blo 872567 20166043 := bstep (se 1 (by rfl) ⟨15124532, by rfl⟩ : syracuseStep 20166043 = 30249065) B30249065
theorem B2209619 : Blo 872567 2209619 := bstep (se 1 (by rfl) ⟨1657214, by rfl⟩ : syracuseStep 2209619 = 3314429) B3314429
theorem B6732019 : Blo 872567 6732019 := bstep (se 1 (by rfl) ⟨5049014, by rfl⟩ : syracuseStep 6732019 = 10098029) B10098029
theorem B68074667 : Blo 872567 68074667 := bstep (se 1 (by rfl) ⟨51056000, by rfl⟩ : syracuseStep 68074667 = 102112001) B102112001
theorem B34062281 : Blo 872567 34062281 := bstep (se 2 (by rfl) ⟨12773355, by rfl⟩ : syracuseStep 34062281 = 25546711) B25546711
theorem B6636329 : Blo 872567 6636329 := bstep (se 2 (by rfl) ⟨2488623, by rfl⟩ : syracuseStep 6636329 = 4977247) B4977247
theorem B19153907 : Blo 872567 19153907 := bstep (se 1 (by rfl) ⟨14365430, by rfl⟩ : syracuseStep 19153907 = 28730861) B28730861
theorem B13485275 : Blo 872567 13485275 := bstep (se 1 (by rfl) ⟨10113956, by rfl⟩ : syracuseStep 13485275 = 20227913) B20227913
theorem B43042051 : Blo 872567 43042051 := bstep (se 1 (by rfl) ⟨32281538, by rfl⟩ : syracuseStep 43042051 = 64563077) B64563077
theorem B2213183 : Blo 872567 2213183 := bstep (se 1 (by rfl) ⟨1659887, by rfl⟩ : syracuseStep 2213183 = 3319775) B3319775
theorem B1656713 : Blo 872567 1656713 := bstep (se 2 (by rfl) ⟨621267, by rfl⟩ : syracuseStep 1656713 = 1242535) B1242535
theorem B71813735 : Blo 872567 71813735 := bstep (se 1 (by rfl) ⟨53860301, by rfl⟩ : syracuseStep 71813735 = 107720603) B107720603
theorem B1657579 : Blo 872567 1657579 := bstep (se 1 (by rfl) ⟨1243184, by rfl⟩ : syracuseStep 1657579 = 2486369) B2486369
theorem B4868873 : Blo 872567 4868873 := bstep (se 2 (by rfl) ⟨1825827, by rfl⟩ : syracuseStep 4868873 = 3651655) B3651655
theorem B2804777 : Blo 872567 2804777 := bstep (se 2 (by rfl) ⟨1051791, by rfl⟩ : syracuseStep 2804777 = 2103583) B2103583
theorem B21285935 : Blo 872567 21285935 := bstep (se 1 (by rfl) ⟨15964451, by rfl⟩ : syracuseStep 21285935 = 31928903) B31928903
theorem B2215259 : Blo 872567 2215259 := bstep (se 1 (by rfl) ⟨1661444, by rfl⟩ : syracuseStep 2215259 = 3322889) B3322889
theorem B2215289 : Blo 872567 2215289 := bstep (se 2 (by rfl) ⟨830733, by rfl⟩ : syracuseStep 2215289 = 1661467) B1661467
theorem B1658551 : Blo 872567 1658551 := bstep (se 1 (by rfl) ⟨1243913, by rfl⟩ : syracuseStep 1658551 = 2487827) B2487827
theorem B8507123 : Blo 872567 8507123 := bstep (se 1 (by rfl) ⟨6380342, by rfl⟩ : syracuseStep 8507123 = 12760685) B12760685
theorem B872751 : Blo 872567 872751 := bstep (se 1 (by rfl) ⟨654563, by rfl⟩ : syracuseStep 872751 = 1309127) B1309127
theorem B872895 : Blo 872567 872895 := bstep (se 1 (by rfl) ⟨654671, by rfl⟩ : syracuseStep 872895 = 1309343) B1309343
theorem B872991 : Blo 872567 872991 := bstep (se 1 (by rfl) ⟨654743, by rfl⟩ : syracuseStep 872991 = 1309487) B1309487
theorem B873071 : Blo 872567 873071 := bstep (se 1 (by rfl) ⟨654803, by rfl⟩ : syracuseStep 873071 = 1309607) B1309607
theorem B873191 : Blo 872567 873191 := bstep (se 1 (by rfl) ⟨654893, by rfl⟩ : syracuseStep 873191 = 1309787) B1309787
theorem B7459721 : Blo 872567 7459721 := bstep (se 2 (by rfl) ⟨2797395, by rfl⟩ : syracuseStep 7459721 = 5594791) B5594791
theorem B873439 : Blo 872567 873439 := bstep (se 1 (by rfl) ⟨655079, by rfl⟩ : syracuseStep 873439 = 1310159) B1310159
theorem B1397801 : Blo 872567 1397801 := bstep (se 2 (by rfl) ⟨524175, by rfl⟩ : syracuseStep 1397801 = 1048351) B1048351
theorem B1660009 : Blo 872567 1660009 := bstep (se 2 (by rfl) ⟨622503, by rfl⟩ : syracuseStep 1660009 = 1245007) B1245007
theorem B2806969 : Blo 872567 2806969 := bstep (se 2 (by rfl) ⟨1052613, by rfl⟩ : syracuseStep 2806969 = 2105227) B2105227
theorem B873695 : Blo 872567 873695 := bstep (se 1 (by rfl) ⟨655271, by rfl⟩ : syracuseStep 873695 = 1310543) B1310543
theorem B1660169 : Blo 872567 1660169 := bstep (se 2 (by rfl) ⟨622563, by rfl⟩ : syracuseStep 1660169 = 1245127) B1245127
theorem B873775 : Blo 872567 873775 := bstep (se 1 (by rfl) ⟨655331, by rfl⟩ : syracuseStep 873775 = 1310663) B1310663
theorem B874015 : Blo 872567 874015 := bstep (se 1 (by rfl) ⟨655511, by rfl⟩ : syracuseStep 874015 = 1311023) B1311023
theorem B2217577 : Blo 872567 2217577 := bstep (se 2 (by rfl) ⟨831591, by rfl⟩ : syracuseStep 2217577 = 1663183) B1663183
theorem B874175 : Blo 872567 874175 := bstep (se 1 (by rfl) ⟨655631, by rfl⟩ : syracuseStep 874175 = 1311263) B1311263
theorem B11196143 : Blo 872567 11196143 := bstep (se 1 (by rfl) ⟨8397107, by rfl⟩ : syracuseStep 11196143 = 16794215) B16794215
theorem B4970231 : Blo 872567 4970231 := bstep (se 1 (by rfl) ⟨3727673, by rfl⟩ : syracuseStep 4970231 = 7455347) B7455347
theorem B2217719 : Blo 872567 2217719 := bstep (se 1 (by rfl) ⟨1663289, by rfl⟩ : syracuseStep 2217719 = 3326579) B3326579
theorem B874623 : Blo 872567 874623 := bstep (se 1 (by rfl) ⟨655967, by rfl⟩ : syracuseStep 874623 = 1311935) B1311935
theorem B874719 : Blo 872567 874719 := bstep (se 1 (by rfl) ⟨656039, by rfl⟩ : syracuseStep 874719 = 1312079) B1312079
theorem B874779 : Blo 872567 874779 := bstep (se 1 (by rfl) ⟨656084, by rfl⟩ : syracuseStep 874779 = 1312169) B1312169
theorem B11229515 : Blo 872567 11229515 := bstep (se 1 (by rfl) ⟨8422136, by rfl⟩ : syracuseStep 11229515 = 16844273) B16844273
theorem B874879 : Blo 872567 874879 := bstep (se 1 (by rfl) ⟨656159, by rfl⟩ : syracuseStep 874879 = 1312319) B1312319
theorem B2218367 : Blo 872567 2218367 := bstep (se 1 (by rfl) ⟨1663775, by rfl⟩ : syracuseStep 2218367 = 3327551) B3327551
theorem B874907 : Blo 872567 874907 := bstep (se 1 (by rfl) ⟨656180, by rfl⟩ : syracuseStep 874907 = 1312361) B1312361
theorem B1661627 : Blo 872567 1661627 := bstep (se 1 (by rfl) ⟨1246220, by rfl⟩ : syracuseStep 1661627 = 2492441) B2492441
theorem B875199 : Blo 872567 875199 := bstep (se 1 (by rfl) ⟨656399, by rfl⟩ : syracuseStep 875199 = 1312799) B1312799
theorem B875327 : Blo 872567 875327 := bstep (se 1 (by rfl) ⟨656495, by rfl⟩ : syracuseStep 875327 = 1312991) B1312991
theorem B875367 : Blo 872567 875367 := bstep (se 1 (by rfl) ⟨656525, by rfl⟩ : syracuseStep 875367 = 1313051) B1313051
theorem B16833581 : Blo 872567 16833581 := bstep (se 3 (by rfl) ⟨3156296, by rfl⟩ : syracuseStep 16833581 = 6312593) B6312593
theorem B875583 : Blo 872567 875583 := bstep (se 1 (by rfl) ⟨656687, by rfl⟩ : syracuseStep 875583 = 1313375) B1313375
theorem B875771 : Blo 872567 875771 := bstep (se 1 (by rfl) ⟨656828, by rfl⟩ : syracuseStep 875771 = 1313657) B1313657
theorem B875803 : Blo 872567 875803 := bstep (se 1 (by rfl) ⟨656852, by rfl⟩ : syracuseStep 875803 = 1313705) B1313705
theorem B875903 : Blo 872567 875903 := bstep (se 1 (by rfl) ⟨656927, by rfl⟩ : syracuseStep 875903 = 1313855) B1313855
theorem B1990367 : Blo 872567 1990367 := bstep (se 1 (by rfl) ⟨1492775, by rfl⟩ : syracuseStep 1990367 = 2985551) B2985551
theorem B876271 : Blo 872567 876271 := bstep (se 1 (by rfl) ⟨657203, by rfl⟩ : syracuseStep 876271 = 1314407) B1314407
theorem B1105903 : Blo 872567 1105903 := bstep (se 1 (by rfl) ⟨829427, by rfl⟩ : syracuseStep 1105903 = 1658855) B1658855
theorem B876527 : Blo 872567 876527 := bstep (se 1 (by rfl) ⟨657395, by rfl⟩ : syracuseStep 876527 = 1314791) B1314791
theorem B9953765 : Blo 872567 9953765 := bstep (se 4 (by rfl) ⟨933165, by rfl⟩ : syracuseStep 9953765 = 1866331) B1866331
theorem B38265371 : Blo 872567 38265371 := bstep (se 1 (by rfl) ⟨28699028, by rfl⟩ : syracuseStep 38265371 = 57398057) B57398057
theorem B2843191 : Blo 872567 2843191 := bstep (se 1 (by rfl) ⟨2132393, by rfl⟩ : syracuseStep 2843191 = 4264787) B4264787
theorem B3728015 : Blo 872567 3728015 := bstep (se 1 (by rfl) ⟨2796011, by rfl⟩ : syracuseStep 3728015 = 5592023) B5592023
theorem B22373009 : Blo 872567 22373009 := bstep (se 2 (by rfl) ⟨8389878, by rfl⟩ : syracuseStep 22373009 = 16779757) B16779757
theorem B1107047 : Blo 872567 1107047 := bstep (se 1 (by rfl) ⟨830285, by rfl⟩ : syracuseStep 1107047 = 1660571) B1660571
theorem B43084819 : Blo 872567 43084819 := bstep (se 1 (by rfl) ⟨32313614, by rfl⟩ : syracuseStep 43084819 = 64627229) B64627229
theorem B1109047 : Blo 872567 1109047 := bstep (se 1 (by rfl) ⟨831785, by rfl⟩ : syracuseStep 1109047 = 1663571) B1663571
theorem B56847581 : Blo 872567 56847581 := bstep (se 3 (by rfl) ⟨10658921, by rfl⟩ : syracuseStep 56847581 = 21317843) B21317843
theorem B2486153 : Blo 872567 2486153 := bstep (se 2 (by rfl) ⟨932307, by rfl⟩ : syracuseStep 2486153 = 1864615) B1864615
theorem B6647993 : Blo 872567 6647993 := bstep (se 2 (by rfl) ⟨2492997, by rfl⟩ : syracuseStep 6647993 = 4985995) B4985995
theorem B4977065 : Blo 872567 4977065 := bstep (se 2 (by rfl) ⟨1866399, by rfl⟩ : syracuseStep 4977065 = 3732799) B3732799
theorem B11203271 : Blo 872567 11203271 := bstep (se 1 (by rfl) ⟨8402453, by rfl⟩ : syracuseStep 11203271 = 16804907) B16804907
theorem B4420331 : Blo 872567 4420331 := bstep (se 1 (by rfl) ⟨3315248, by rfl⟩ : syracuseStep 4420331 = 6630497) B6630497
theorem B9958139 : Blo 872567 9958139 := bstep (se 1 (by rfl) ⟨7468604, by rfl⟩ : syracuseStep 9958139 = 14937209) B14937209
theorem B40399667 : Blo 872567 40399667 := bstep (se 1 (by rfl) ⟨30299750, by rfl⟩ : syracuseStep 40399667 = 60599501) B60599501
theorem B30274823 : Blo 872567 30274823 := bstep (se 1 (by rfl) ⟨22706117, by rfl⟩ : syracuseStep 30274823 = 45412235) B45412235
theorem B4978523 : Blo 872567 4978523 := bstep (se 1 (by rfl) ⟨3733892, by rfl⟩ : syracuseStep 4978523 = 7467785) B7467785
theorem B2946941 : Blo 872567 2946941 := bstep (se 3 (by rfl) ⟨552551, by rfl⟩ : syracuseStep 2946941 = 1105103) B1105103
theorem B1472539 : Blo 872567 1472539 := bstep (se 1 (by rfl) ⟨1104404, by rfl⟩ : syracuseStep 1472539 = 2208809) B2208809
theorem B1964087 : Blo 872567 1964087 := bstep (se 1 (by rfl) ⟨1473065, by rfl⟩ : syracuseStep 1964087 = 2946131) B2946131
theorem B1243355 : Blo 872567 1243355 := bstep (se 1 (by rfl) ⟨932516, by rfl⟩ : syracuseStep 1243355 = 1865033) B1865033
theorem B1308983 : Blo 872567 1308983 := bstep (se 1 (by rfl) ⟨981737, by rfl⟩ : syracuseStep 1308983 = 1963475) B1963475
theorem B1964447 : Blo 872567 1964447 := bstep (se 1 (by rfl) ⟨1473335, by rfl⟩ : syracuseStep 1964447 = 2946671) B2946671
theorem B1309163 : Blo 872567 1309163 := bstep (se 1 (by rfl) ⟨981872, by rfl⟩ : syracuseStep 1309163 = 1963745) B1963745
theorem B16841267 : Blo 872567 16841267 := bstep (se 1 (by rfl) ⟨12630950, by rfl⟩ : syracuseStep 16841267 = 25261901) B25261901
theorem B1866503 : Blo 872567 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B1309511 : Blo 872567 1309511 := bstep (se 1 (by rfl) ⟨982133, by rfl⟩ : syracuseStep 1309511 = 1964267) B1964267
theorem B1965023 : Blo 872567 1965023 := bstep (se 1 (by rfl) ⟨1473767, by rfl⟩ : syracuseStep 1965023 = 2947535) B2947535
theorem B2948075 : Blo 872567 2948075 := bstep (se 1 (by rfl) ⟨2211056, by rfl⟩ : syracuseStep 2948075 = 4422113) B4422113
theorem B982111 : Blo 872567 982111 := bstep (se 1 (by rfl) ⟨736583, by rfl⟩ : syracuseStep 982111 = 1473167) B1473167
theorem B1965545 : Blo 872567 1965545 := bstep (se 2 (by rfl) ⟨737079, by rfl⟩ : syracuseStep 1965545 = 1474159) B1474159
theorem B1474031 : Blo 872567 1474031 := bstep (se 1 (by rfl) ⟨1105523, by rfl⟩ : syracuseStep 1474031 = 2211047) B2211047
theorem B4423247 : Blo 872567 4423247 := bstep (se 1 (by rfl) ⟨3317435, by rfl⟩ : syracuseStep 4423247 = 6634871) B6634871
theorem B1310345 : Blo 872567 1310345 := bstep (se 2 (by rfl) ⟨491379, by rfl⟩ : syracuseStep 1310345 = 982759) B982759
theorem B1310375 : Blo 872567 1310375 := bstep (se 1 (by rfl) ⟨982781, by rfl⟩ : syracuseStep 1310375 = 1965563) B1965563
theorem B1310495 : Blo 872567 1310495 := bstep (se 1 (by rfl) ⟨982871, by rfl⟩ : syracuseStep 1310495 = 1965743) B1965743
theorem B1310555 : Blo 872567 1310555 := bstep (se 1 (by rfl) ⟨982916, by rfl⟩ : syracuseStep 1310555 = 1965833) B1965833
theorem B4424219 : Blo 872567 4424219 := bstep (se 1 (by rfl) ⟨3318164, by rfl⟩ : syracuseStep 4424219 = 6636329) B6636329
theorem B1475455 : Blo 872567 1475455 := bstep (se 1 (by rfl) ⟨1106591, by rfl⟩ : syracuseStep 1475455 = 2213183) B2213183
theorem B1966985 : Blo 872567 1966985 := bstep (se 2 (by rfl) ⟨737619, by rfl⟩ : syracuseStep 1966985 = 1475239) B1475239
theorem B1311839 : Blo 872567 1311839 := bstep (se 1 (by rfl) ⟨983879, by rfl⟩ : syracuseStep 1311839 = 1967759) B1967759
theorem B1311899 : Blo 872567 1311899 := bstep (se 1 (by rfl) ⟨983924, by rfl⟩ : syracuseStep 1311899 = 1967849) B1967849
theorem B5113039 : Blo 872567 5113039 := bstep (se 1 (by rfl) ⟨3834779, by rfl⟩ : syracuseStep 5113039 = 7669559) B7669559
theorem B5604713 : Blo 872567 5604713 := bstep (se 2 (by rfl) ⟨2101767, by rfl⟩ : syracuseStep 5604713 = 4203535) B4203535
theorem B7472843 : Blo 872567 7472843 := bstep (se 1 (by rfl) ⟨5604632, by rfl⟩ : syracuseStep 7472843 = 11209265) B11209265
theorem B47875823 : Blo 872567 47875823 := bstep (se 1 (by rfl) ⟨35906867, by rfl⟩ : syracuseStep 47875823 = 71813735) B71813735
theorem B3245915 : Blo 872567 3245915 := bstep (se 1 (by rfl) ⟨2434436, by rfl⟩ : syracuseStep 3245915 = 4868873) B4868873
theorem B1869851 : Blo 872567 1869851 := bstep (se 1 (by rfl) ⟨1402388, by rfl⟩ : syracuseStep 1869851 = 2804777) B2804777
theorem B14190623 : Blo 872567 14190623 := bstep (se 1 (by rfl) ⟨10642967, by rfl⟩ : syracuseStep 14190623 = 21285935) B21285935
theorem B2951207 : Blo 872567 2951207 := bstep (se 1 (by rfl) ⟨2213405, by rfl⟩ : syracuseStep 2951207 = 4426811) B4426811
theorem B1476839 : Blo 872567 1476839 := bstep (se 1 (by rfl) ⟨1107629, by rfl⟩ : syracuseStep 1476839 = 2215259) B2215259
theorem B1476859 : Blo 872567 1476859 := bstep (se 1 (by rfl) ⟨1107644, by rfl⟩ : syracuseStep 1476859 = 2215289) B2215289
theorem B1313087 : Blo 872567 1313087 := bstep (se 1 (by rfl) ⟨984815, by rfl⟩ : syracuseStep 1313087 = 1969631) B1969631
theorem B1182055 : Blo 872567 1182055 := bstep (se 1 (by rfl) ⟨886541, by rfl⟩ : syracuseStep 1182055 = 1773083) B1773083
theorem B5671415 : Blo 872567 5671415 := bstep (se 1 (by rfl) ⟨4253561, by rfl⟩ : syracuseStep 5671415 = 8507123) B8507123
theorem B1968767 : Blo 872567 1968767 := bstep (se 1 (by rfl) ⟨1476575, by rfl⟩ : syracuseStep 1968767 = 2953151) B2953151
theorem B985927 : Blo 872567 985927 := bstep (se 1 (by rfl) ⟨739445, by rfl⟩ : syracuseStep 985927 = 1478891) B1478891
theorem B2952125 : Blo 872567 2952125 := bstep (se 3 (by rfl) ⟨553523, by rfl⟩ : syracuseStep 2952125 = 1107047) B1107047
theorem B1313759 : Blo 872567 1313759 := bstep (se 1 (by rfl) ⟨985319, by rfl⟩ : syracuseStep 1313759 = 1970639) B1970639
theorem B2362337 : Blo 872567 2362337 := bstep (se 2 (by rfl) ⟨885876, by rfl⟩ : syracuseStep 2362337 = 1771753) B1771753
theorem B1575929 : Blo 872567 1575929 := bstep (se 2 (by rfl) ⟨590973, by rfl⟩ : syracuseStep 1575929 = 1181947) B1181947
theorem B53841617 : Blo 872567 53841617 := bstep (se 2 (by rfl) ⟨20190606, by rfl⟩ : syracuseStep 53841617 = 40381213) B40381213
theorem B2952935 : Blo 872567 2952935 := bstep (se 1 (by rfl) ⟨2214701, by rfl⟩ : syracuseStep 2952935 = 4429403) B4429403
theorem B6655769 : Blo 872567 6655769 := bstep (se 2 (by rfl) ⟨2495913, by rfl⟩ : syracuseStep 6655769 = 4991827) B4991827
theorem B3313487 : Blo 872567 3313487 := bstep (se 1 (by rfl) ⟨2485115, by rfl⟩ : syracuseStep 3313487 = 4970231) B4970231
theorem B1478479 : Blo 872567 1478479 := bstep (se 1 (by rfl) ⟨1108859, by rfl⟩ : syracuseStep 1478479 = 2217719) B2217719
theorem B7081883 : Blo 872567 7081883 := bstep (se 1 (by rfl) ⟨5311412, by rfl⟩ : syracuseStep 7081883 = 10622825) B10622825
theorem B57446425 : Blo 872567 57446425 := bstep (se 2 (by rfl) ⟨21542409, by rfl⟩ : syracuseStep 57446425 = 43084819) B43084819
theorem B1478729 : Blo 872567 1478729 := bstep (se 2 (by rfl) ⟨554523, by rfl⟩ : syracuseStep 1478729 = 1109047) B1109047
theorem B1970297 : Blo 872567 1970297 := bstep (se 2 (by rfl) ⟨738861, by rfl⟩ : syracuseStep 1970297 = 1477723) B1477723
theorem B1478911 : Blo 872567 1478911 := bstep (se 1 (by rfl) ⟨1109183, by rfl⟩ : syracuseStep 1478911 = 2218367) B2218367
theorem B1970603 : Blo 872567 1970603 := bstep (se 1 (by rfl) ⟨1477952, by rfl⟩ : syracuseStep 1970603 = 2955905) B2955905
theorem B5607913 : Blo 872567 5607913 := bstep (se 2 (by rfl) ⟨2102967, by rfl⟩ : syracuseStep 5607913 = 4205935) B4205935
theorem B1774315 : Blo 872567 1774315 := bstep (se 1 (by rfl) ⟨1330736, by rfl⟩ : syracuseStep 1774315 = 2661473) B2661473
theorem B1971071 : Blo 872567 1971071 := bstep (se 1 (by rfl) ⟨1478303, by rfl⟩ : syracuseStep 1971071 = 2956607) B2956607
theorem B2954123 : Blo 872567 2954123 := bstep (se 1 (by rfl) ⟨2215592, by rfl⟩ : syracuseStep 2954123 = 4431185) B4431185
theorem B2364671 : Blo 872567 2364671 := bstep (se 1 (by rfl) ⟨1773503, by rfl⟩ : syracuseStep 2364671 = 3547007) B3547007
theorem B1971935 : Blo 872567 1971935 := bstep (se 1 (by rfl) ⟨1478951, by rfl⟩ : syracuseStep 1971935 = 2957903) B2957903
theorem B14915339 : Blo 872567 14915339 := bstep (se 1 (by rfl) ⟨11186504, by rfl⟩ : syracuseStep 14915339 = 22373009) B22373009
theorem B3741547 : Blo 872567 3741547 := bstep (se 1 (by rfl) ⟨2806160, by rfl⟩ : syracuseStep 3741547 = 5612321) B5612321
theorem B3315613 : Blo 872567 3315613 := bstep (se 3 (by rfl) ⟨621677, by rfl⟩ : syracuseStep 3315613 = 1243355) B1243355
theorem B2103545 : Blo 872567 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B3742625 : Blo 872567 3742625 := bstep (se 2 (by rfl) ⟨1403484, by rfl⟩ : syracuseStep 3742625 = 2806969) B2806969
theorem B8985563 : Blo 872567 8985563 := bstep (se 1 (by rfl) ⟨6739172, by rfl⟩ : syracuseStep 8985563 = 13478345) B13478345
theorem B2956715 : Blo 872567 2956715 := bstep (se 1 (by rfl) ⟨2217536, by rfl⟩ : syracuseStep 2956715 = 4435073) B4435073
theorem B2956769 : Blo 872567 2956769 := bstep (se 2 (by rfl) ⟨1108788, by rfl⟩ : syracuseStep 2956769 = 2217577) B2217577
theorem B18948167 : Blo 872567 18948167 := bstep (se 1 (by rfl) ⟨14211125, by rfl⟩ : syracuseStep 18948167 = 28422251) B28422251
theorem B4431995 : Blo 872567 4431995 := bstep (se 1 (by rfl) ⟨3323996, by rfl⟩ : syracuseStep 4431995 = 6647993) B6647993
theorem B3318043 : Blo 872567 3318043 := bstep (se 1 (by rfl) ⟨2488532, by rfl⟩ : syracuseStep 3318043 = 4977065) B4977065
theorem B3319015 : Blo 872567 3319015 := bstep (se 1 (by rfl) ⟨2489261, by rfl⟩ : syracuseStep 3319015 = 4978523) B4978523
theorem B7480633 : Blo 872567 7480633 := bstep (se 2 (by rfl) ⟨2805237, by rfl⟩ : syracuseStep 7480633 = 5610475) B5610475
theorem B4204705 : Blo 872567 4204705 := bstep (se 2 (by rfl) ⟨1576764, by rfl⟩ : syracuseStep 4204705 = 3153529) B3153529
theorem B7088957 : Blo 872567 7088957 := bstep (se 3 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 7088957 = 2658359) B2658359
theorem B8990183 : Blo 872567 8990183 := bstep (se 1 (by rfl) ⟨6742637, by rfl⟩ : syracuseStep 8990183 = 13485275) B13485275
theorem B896927 : Blo 872567 896927 := bstep (se 1 (by rfl) ⟨672695, by rfl⟩ : syracuseStep 896927 = 1345391) B1345391
theorem B4435883 : Blo 872567 4435883 := bstep (se 1 (by rfl) ⟨3326912, by rfl⟩ : syracuseStep 4435883 = 6653825) B6653825
theorem B2994239 : Blo 872567 2994239 := bstep (se 1 (by rfl) ⟨2245679, by rfl⟩ : syracuseStep 2994239 = 4491359) B4491359
theorem B57389401 : Blo 872567 57389401 := bstep (se 2 (by rfl) ⟨21521025, by rfl⟩ : syracuseStep 57389401 = 43042051) B43042051
theorem B931867 : Blo 872567 931867 := bstep (se 1 (by rfl) ⟨698900, by rfl⟩ : syracuseStep 931867 = 1397801) B1397801
theorem B2210105 : Blo 872567 2210105 := bstep (se 2 (by rfl) ⟨828789, by rfl⟩ : syracuseStep 2210105 = 1657579) B1657579
theorem B3324635 : Blo 872567 3324635 := bstep (se 1 (by rfl) ⟨2493476, by rfl⟩ : syracuseStep 3324635 = 4986953) B4986953
theorem B7486343 : Blo 872567 7486343 := bstep (se 1 (by rfl) ⟨5614757, by rfl⟩ : syracuseStep 7486343 = 11229515) B11229515
theorem B11222387 : Blo 872567 11222387 := bstep (se 1 (by rfl) ⟨8416790, by rfl⟩ : syracuseStep 11222387 = 16833581) B16833581
theorem B11189785 : Blo 872567 11189785 := bstep (se 2 (by rfl) ⟨4196169, by rfl⟩ : syracuseStep 11189785 = 8392339) B8392339
theorem B2211401 : Blo 872567 2211401 := bstep (se 2 (by rfl) ⟨829275, by rfl⟩ : syracuseStep 2211401 = 1658551) B1658551
theorem B3325607 : Blo 872567 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B1326911 : Blo 872567 1326911 := bstep (se 1 (by rfl) ⟨995183, by rfl⟩ : syracuseStep 1326911 = 1990367) B1990367
theorem B7454663 : Blo 872567 7454663 := bstep (se 1 (by rfl) ⟨5590997, by rfl⟩ : syracuseStep 7454663 = 11181995) B11181995
theorem B6635843 : Blo 872567 6635843 := bstep (se 1 (by rfl) ⟨4976882, by rfl⟩ : syracuseStep 6635843 = 9953765) B9953765
theorem B25510247 : Blo 872567 25510247 := bstep (se 1 (by rfl) ⟨19132685, by rfl⟩ : syracuseStep 25510247 = 38265371) B38265371
theorem B2213345 : Blo 872567 2213345 := bstep (se 2 (by rfl) ⟨830004, by rfl⟩ : syracuseStep 2213345 = 1660009) B1660009
theorem B3786365 : Blo 872567 3786365 := bstep (se 3 (by rfl) ⟨709943, by rfl⟩ : syracuseStep 3786365 = 1419887) B1419887
theorem B7390939 : Blo 872567 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B3327763 : Blo 872567 3327763 := bstep (se 1 (by rfl) ⟨2495822, by rfl⟩ : syracuseStep 3327763 = 4991645) B4991645
theorem B26888057 : Blo 872567 26888057 := bstep (se 2 (by rfl) ⟨10083021, by rfl⟩ : syracuseStep 26888057 = 20166043) B20166043
theorem B37898387 : Blo 872567 37898387 := bstep (se 1 (by rfl) ⟨28423790, by rfl⟩ : syracuseStep 37898387 = 56847581) B56847581
theorem B1657435 : Blo 872567 1657435 := bstep (se 1 (by rfl) ⟨1243076, by rfl⟩ : syracuseStep 1657435 = 2486153) B2486153
theorem B6638759 : Blo 872567 6638759 := bstep (se 1 (by rfl) ⟨4979069, by rfl⟩ : syracuseStep 6638759 = 9958139) B9958139
theorem B49270139 : Blo 872567 49270139 := bstep (se 1 (by rfl) ⟨36952604, by rfl⟩ : syracuseStep 49270139 = 73905209) B73905209
theorem B18927665 : Blo 872567 18927665 := bstep (se 2 (by rfl) ⟨7097874, by rfl⟩ : syracuseStep 18927665 = 14195749) B14195749
theorem B872655 : Blo 872567 872655 := bstep (se 1 (by rfl) ⟨654491, by rfl⟩ : syracuseStep 872655 = 1308983) B1308983
theorem B872775 : Blo 872567 872775 := bstep (se 1 (by rfl) ⟨654581, by rfl⟩ : syracuseStep 872775 = 1309163) B1309163
theorem B11227511 : Blo 872567 11227511 := bstep (se 1 (by rfl) ⟨8420633, by rfl⟩ : syracuseStep 11227511 = 16841267) B16841267
theorem B873007 : Blo 872567 873007 := bstep (se 1 (by rfl) ⟨654755, by rfl⟩ : syracuseStep 873007 = 1309511) B1309511
theorem B11195117 : Blo 872567 11195117 := bstep (se 3 (by rfl) ⟨2099084, by rfl⟩ : syracuseStep 11195117 = 4198169) B4198169
theorem B14963453 : Blo 872567 14963453 := bstep (se 3 (by rfl) ⟨2805647, by rfl⟩ : syracuseStep 14963453 = 5611295) B5611295
theorem B873563 : Blo 872567 873563 := bstep (se 1 (by rfl) ⟨655172, by rfl⟩ : syracuseStep 873563 = 1310345) B1310345
theorem B873583 : Blo 872567 873583 := bstep (se 1 (by rfl) ⟨655187, by rfl⟩ : syracuseStep 873583 = 1310375) B1310375
theorem B873663 : Blo 872567 873663 := bstep (se 1 (by rfl) ⟨655247, by rfl⟩ : syracuseStep 873663 = 1310495) B1310495
theorem B873703 : Blo 872567 873703 := bstep (se 1 (by rfl) ⟨655277, by rfl⟩ : syracuseStep 873703 = 1310555) B1310555
theorem B873983 : Blo 872567 873983 := bstep (se 1 (by rfl) ⟨655487, by rfl⟩ : syracuseStep 873983 = 1310975) B1310975
theorem B874087 : Blo 872567 874087 := bstep (se 1 (by rfl) ⟨655565, by rfl⟩ : syracuseStep 874087 = 1311131) B1311131
theorem B874367 : Blo 872567 874367 := bstep (se 1 (by rfl) ⟨655775, by rfl⟩ : syracuseStep 874367 = 1311551) B1311551
theorem B1660799 : Blo 872567 1660799 := bstep (se 1 (by rfl) ⟨1245599, by rfl⟩ : syracuseStep 1660799 = 2491199) B2491199
theorem B874463 : Blo 872567 874463 := bstep (se 1 (by rfl) ⟨655847, by rfl⟩ : syracuseStep 874463 = 1311695) B1311695
theorem B12769271 : Blo 872567 12769271 := bstep (se 1 (by rfl) ⟨9576953, by rfl⟩ : syracuseStep 12769271 = 19153907) B19153907
theorem B874523 : Blo 872567 874523 := bstep (se 1 (by rfl) ⟨655892, by rfl⟩ : syracuseStep 874523 = 1311785) B1311785
theorem B874543 : Blo 872567 874543 := bstep (se 1 (by rfl) ⟨655907, by rfl⟩ : syracuseStep 874543 = 1311815) B1311815
theorem B3790921 : Blo 872567 3790921 := bstep (se 2 (by rfl) ⟨1421595, by rfl⟩ : syracuseStep 3790921 = 2843191) B2843191
theorem B874663 : Blo 872567 874663 := bstep (se 1 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 874663 = 1311995) B1311995
theorem B874855 : Blo 872567 874855 := bstep (se 1 (by rfl) ⟨656141, by rfl⟩ : syracuseStep 874855 = 1312283) B1312283
theorem B875111 : Blo 872567 875111 := bstep (se 1 (by rfl) ⟨656333, by rfl⟩ : syracuseStep 875111 = 1312667) B1312667
theorem B875135 : Blo 872567 875135 := bstep (se 1 (by rfl) ⟨656351, by rfl⟩ : syracuseStep 875135 = 1312703) B1312703
theorem B875551 : Blo 872567 875551 := bstep (se 1 (by rfl) ⟨656663, by rfl⟩ : syracuseStep 875551 = 1313327) B1313327
theorem B875631 : Blo 872567 875631 := bstep (se 1 (by rfl) ⟨656723, by rfl⟩ : syracuseStep 875631 = 1313447) B1313447
theorem B5594255 : Blo 872567 5594255 := bstep (se 1 (by rfl) ⟨4195691, by rfl⟩ : syracuseStep 5594255 = 8391383) B8391383
theorem B875675 : Blo 872567 875675 := bstep (se 1 (by rfl) ⟨656756, by rfl⟩ : syracuseStep 875675 = 1313513) B1313513
theorem B875679 : Blo 872567 875679 := bstep (se 1 (by rfl) ⟨656759, by rfl⟩ : syracuseStep 875679 = 1313519) B1313519
theorem B875711 : Blo 872567 875711 := bstep (se 1 (by rfl) ⟨656783, by rfl⟩ : syracuseStep 875711 = 1313567) B1313567
theorem B43080983 : Blo 872567 43080983 := bstep (se 1 (by rfl) ⟨32310737, by rfl⟩ : syracuseStep 43080983 = 64621475) B64621475
theorem B875931 : Blo 872567 875931 := bstep (se 1 (by rfl) ⟨656948, by rfl⟩ : syracuseStep 875931 = 1313897) B1313897
theorem B876015 : Blo 872567 876015 := bstep (se 1 (by rfl) ⟨657011, by rfl⟩ : syracuseStep 876015 = 1314023) B1314023
theorem B6315707 : Blo 872567 6315707 := bstep (se 1 (by rfl) ⟨4736780, by rfl⟩ : syracuseStep 6315707 = 9473561) B9473561
theorem B876351 : Blo 872567 876351 := bstep (se 1 (by rfl) ⟨657263, by rfl⟩ : syracuseStep 876351 = 1314527) B1314527
theorem B876539 : Blo 872567 876539 := bstep (se 1 (by rfl) ⟨657404, by rfl⟩ : syracuseStep 876539 = 1314809) B1314809
theorem B1663031 : Blo 872567 1663031 := bstep (se 1 (by rfl) ⟨1247273, by rfl⟩ : syracuseStep 1663031 = 2494547) B2494547
theorem B4973147 : Blo 872567 4973147 := bstep (se 1 (by rfl) ⟨3729860, by rfl⟩ : syracuseStep 4973147 = 7459721) B7459721
theorem B1401671 : Blo 872567 1401671 := bstep (se 1 (by rfl) ⟨1051253, by rfl⟩ : syracuseStep 1401671 = 2102507) B2102507
theorem B1106779 : Blo 872567 1106779 := bstep (se 1 (by rfl) ⟨830084, by rfl⟩ : syracuseStep 1106779 = 1660169) B1660169
theorem B7464095 : Blo 872567 7464095 := bstep (se 1 (by rfl) ⟨5598071, by rfl⟩ : syracuseStep 7464095 = 11196143) B11196143
theorem B1107751 : Blo 872567 1107751 := bstep (se 1 (by rfl) ⟨830813, by rfl⟩ : syracuseStep 1107751 = 1661627) B1661627
theorem B1796051 : Blo 872567 1796051 := bstep (se 1 (by rfl) ⟨1347038, by rfl⟩ : syracuseStep 1796051 = 2694077) B2694077
theorem B4417901 : Blo 872567 4417901 := bstep (se 3 (by rfl) ⟨828356, by rfl⟩ : syracuseStep 4417901 = 1656713) B1656713
theorem B4418063 : Blo 872567 4418063 := bstep (se 1 (by rfl) ⟨3313547, by rfl⟩ : syracuseStep 4418063 = 6627095) B6627095
theorem B6646535 : Blo 872567 6646535 := bstep (se 1 (by rfl) ⟨4984901, by rfl⟩ : syracuseStep 6646535 = 9969803) B9969803
theorem B2485343 : Blo 872567 2485343 := bstep (se 1 (by rfl) ⟨1864007, by rfl⟩ : syracuseStep 2485343 = 3728015) B3728015
theorem B21589753 : Blo 872567 21589753 := bstep (se 2 (by rfl) ⟨8096157, by rfl⟩ : syracuseStep 21589753 = 16192315) B16192315
theorem B4420169 : Blo 872567 4420169 := bstep (se 2 (by rfl) ⟨1657563, by rfl⟩ : syracuseStep 4420169 = 3315127) B3315127
theorem B1963385 : Blo 872567 1963385 := bstep (se 2 (by rfl) ⟨736269, by rfl⟩ : syracuseStep 1963385 = 1472539) B1472539
theorem B8976025 : Blo 872567 8976025 := bstep (se 2 (by rfl) ⟨3366009, by rfl⟩ : syracuseStep 8976025 = 6732019) B6732019
theorem B7468847 : Blo 872567 7468847 := bstep (se 1 (by rfl) ⟨5601635, by rfl⟩ : syracuseStep 7468847 = 11203271) B11203271
theorem B2946887 : Blo 872567 2946887 := bstep (se 1 (by rfl) ⟨2210165, by rfl⟩ : syracuseStep 2946887 = 4420331) B4420331
theorem B26933111 : Blo 872567 26933111 := bstep (se 1 (by rfl) ⟨20199833, by rfl⟩ : syracuseStep 26933111 = 40399667) B40399667
theorem B4421627 : Blo 872567 4421627 := bstep (se 1 (by rfl) ⟨3316220, by rfl⟩ : syracuseStep 4421627 = 6632441) B6632441
theorem B20183215 : Blo 872567 20183215 := bstep (se 1 (by rfl) ⟨15137411, by rfl⟩ : syracuseStep 20183215 = 30274823) B30274823
theorem B1473079 : Blo 872567 1473079 := bstep (se 1 (by rfl) ⟨1104809, by rfl⟩ : syracuseStep 1473079 = 2209619) B2209619
theorem B1964627 : Blo 872567 1964627 := bstep (se 1 (by rfl) ⟨1473470, by rfl⟩ : syracuseStep 1964627 = 2946941) B2946941
theorem B1309391 : Blo 872567 1309391 := bstep (se 1 (by rfl) ⟨982043, by rfl⟩ : syracuseStep 1309391 = 1964087) B1964087
theorem B1309481 : Blo 872567 1309481 := bstep (se 2 (by rfl) ⟨491055, by rfl⟩ : syracuseStep 1309481 = 982111) B982111
theorem B1309631 : Blo 872567 1309631 := bstep (se 1 (by rfl) ⟨982223, by rfl⟩ : syracuseStep 1309631 = 1964447) B1964447
theorem B1244335 : Blo 872567 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B1310015 : Blo 872567 1310015 := bstep (se 1 (by rfl) ⟨982511, by rfl⟩ : syracuseStep 1310015 = 1965023) B1965023
theorem B1965383 : Blo 872567 1965383 := bstep (se 1 (by rfl) ⟨1474037, by rfl⟩ : syracuseStep 1965383 = 2948075) B2948075
theorem B45383111 : Blo 872567 45383111 := bstep (se 1 (by rfl) ⟨34037333, by rfl⟩ : syracuseStep 45383111 = 68074667) B68074667
theorem B1310363 : Blo 872567 1310363 := bstep (se 1 (by rfl) ⟨982772, by rfl⟩ : syracuseStep 1310363 = 1965545) B1965545
theorem B982687 : Blo 872567 982687 := bstep (se 1 (by rfl) ⟨737015, by rfl⟩ : syracuseStep 982687 = 1474031) B1474031
theorem B2948831 : Blo 872567 2948831 := bstep (se 1 (by rfl) ⟨2211623, by rfl⟩ : syracuseStep 2948831 = 4423247) B4423247
theorem B22708187 : Blo 872567 22708187 := bstep (se 1 (by rfl) ⟨17031140, by rfl⟩ : syracuseStep 22708187 = 34062281) B34062281
theorem B1474537 : Blo 872567 1474537 := bstep (se 2 (by rfl) ⟨552951, by rfl⟩ : syracuseStep 1474537 = 1105903) B1105903
theorem B4423895 : Blo 872567 4423895 := bstep (se 1 (by rfl) ⟨3317921, by rfl⟩ : syracuseStep 4423895 = 6635843) B6635843
theorem B17006831 : Blo 872567 17006831 := bstep (se 1 (by rfl) ⟨12755123, by rfl⟩ : syracuseStep 17006831 = 25510247) B25510247
theorem B2949479 : Blo 872567 2949479 := bstep (se 1 (by rfl) ⟨2212109, by rfl⟩ : syracuseStep 2949479 = 4424219) B4424219
theorem B4424057 : Blo 872567 4424057 := bstep (se 2 (by rfl) ⟨1659021, by rfl⟩ : syracuseStep 4424057 = 3318043) B3318043
theorem B1311323 : Blo 872567 1311323 := bstep (se 1 (by rfl) ⟨983492, by rfl⟩ : syracuseStep 1311323 = 1966985) B1966985
theorem B3736475 : Blo 872567 3736475 := bstep (se 1 (by rfl) ⟨2802356, by rfl⟩ : syracuseStep 3736475 = 5604713) B5604713
theorem B1475563 : Blo 872567 1475563 := bstep (se 1 (by rfl) ⟨1106672, by rfl⟩ : syracuseStep 1475563 = 2213345) B2213345
theorem B2524243 : Blo 872567 2524243 := bstep (se 1 (by rfl) ⟨1893182, by rfl⟩ : syracuseStep 2524243 = 3786365) B3786365
theorem B1475705 : Blo 872567 1475705 := bstep (se 2 (by rfl) ⟨553389, by rfl⟩ : syracuseStep 1475705 = 1106779) B1106779
theorem B4981895 : Blo 872567 4981895 := bstep (se 1 (by rfl) ⟨3736421, by rfl⟩ : syracuseStep 4981895 = 7472843) B7472843
theorem B31917215 : Blo 872567 31917215 := bstep (se 1 (by rfl) ⟨23937911, by rfl⟩ : syracuseStep 31917215 = 47875823) B47875823
theorem B1967273 : Blo 872567 1967273 := bstep (se 2 (by rfl) ⟨737727, by rfl⟩ : syracuseStep 1967273 = 1475455) B1475455
theorem B2163943 : Blo 872567 2163943 := bstep (se 1 (by rfl) ⟨1622957, by rfl⟩ : syracuseStep 2163943 = 3245915) B3245915
theorem B17925371 : Blo 872567 17925371 := bstep (se 1 (by rfl) ⟨13444028, by rfl⟩ : syracuseStep 17925371 = 26888057) B26888057
theorem B1967471 : Blo 872567 1967471 := bstep (se 1 (by rfl) ⟨1475603, by rfl⟩ : syracuseStep 1967471 = 2951207) B2951207
theorem B25265591 : Blo 872567 25265591 := bstep (se 1 (by rfl) ⟨18949193, by rfl⟩ : syracuseStep 25265591 = 37898387) B37898387
theorem B984559 : Blo 872567 984559 := bstep (se 1 (by rfl) ⟨738419, by rfl⟩ : syracuseStep 984559 = 1476839) B1476839
theorem B6817385 : Blo 872567 6817385 := bstep (se 2 (by rfl) ⟨2556519, by rfl⟩ : syracuseStep 6817385 = 5113039) B5113039
theorem B4425353 : Blo 872567 4425353 := bstep (se 2 (by rfl) ⟨1659507, by rfl⟩ : syracuseStep 4425353 = 3319015) B3319015
theorem B1312511 : Blo 872567 1312511 := bstep (se 1 (by rfl) ⟨984383, by rfl⟩ : syracuseStep 1312511 = 1968767) B1968767
theorem B1968083 : Blo 872567 1968083 := bstep (se 1 (by rfl) ⟨1476062, by rfl⟩ : syracuseStep 1968083 = 2952125) B2952125
theorem B1574891 : Blo 872567 1574891 := bstep (se 1 (by rfl) ⟨1181168, by rfl⟩ : syracuseStep 1574891 = 2362337) B2362337
theorem B1050619 : Blo 872567 1050619 := bstep (se 1 (by rfl) ⟨787964, by rfl⟩ : syracuseStep 1050619 = 1575929) B1575929
theorem B4425839 : Blo 872567 4425839 := bstep (se 1 (by rfl) ⟨3319379, by rfl⟩ : syracuseStep 4425839 = 6638759) B6638759
theorem B3737789 : Blo 872567 3737789 := bstep (se 3 (by rfl) ⟨700835, by rfl⟩ : syracuseStep 3737789 = 1401671) B1401671
theorem B1477001 : Blo 872567 1477001 := bstep (se 2 (by rfl) ⟨553875, by rfl⟩ : syracuseStep 1477001 = 1107751) B1107751
theorem B1968623 : Blo 872567 1968623 := bstep (se 1 (by rfl) ⟨1476467, by rfl⟩ : syracuseStep 1968623 = 2952935) B2952935
theorem B4721255 : Blo 872567 4721255 := bstep (se 1 (by rfl) ⟨3540941, by rfl⟩ : syracuseStep 4721255 = 7081883) B7081883
theorem B12618443 : Blo 872567 12618443 := bstep (se 1 (by rfl) ⟨9463832, by rfl⟩ : syracuseStep 12618443 = 18927665) B18927665
theorem B985819 : Blo 872567 985819 := bstep (se 1 (by rfl) ⟨739364, by rfl⟩ : syracuseStep 985819 = 1478729) B1478729
theorem B1313531 : Blo 872567 1313531 := bstep (se 1 (by rfl) ⟨985148, by rfl⟩ : syracuseStep 1313531 = 1970297) B1970297
theorem B5606273 : Blo 872567 5606273 := bstep (se 2 (by rfl) ⟨2102352, by rfl⟩ : syracuseStep 5606273 = 4204705) B4204705
theorem B1313735 : Blo 872567 1313735 := bstep (se 1 (by rfl) ⟨985301, by rfl⟩ : syracuseStep 1313735 = 1970603) B1970603
theorem B1969145 : Blo 872567 1969145 := bstep (se 2 (by rfl) ⟨738429, by rfl⟩ : syracuseStep 1969145 = 1476859) B1476859
theorem B1576073 : Blo 872567 1576073 := bstep (se 2 (by rfl) ⟨591027, by rfl⟩ : syracuseStep 1576073 = 1182055) B1182055
theorem B1314047 : Blo 872567 1314047 := bstep (se 1 (by rfl) ⟨985535, by rfl⟩ : syracuseStep 1314047 = 1971071) B1971071
theorem B1969415 : Blo 872567 1969415 := bstep (se 1 (by rfl) ⟨1477061, by rfl⟩ : syracuseStep 1969415 = 2954123) B2954123
theorem B1314569 : Blo 872567 1314569 := bstep (se 2 (by rfl) ⟨492963, by rfl⟩ : syracuseStep 1314569 = 985927) B985927
theorem B1314623 : Blo 872567 1314623 := bstep (se 1 (by rfl) ⟨985967, by rfl⟩ : syracuseStep 1314623 = 1971935) B1971935
theorem B2495083 : Blo 872567 2495083 := bstep (se 1 (by rfl) ⟨1871312, by rfl⟩ : syracuseStep 2495083 = 3742625) B3742625
theorem B1971143 : Blo 872567 1971143 := bstep (se 1 (by rfl) ⟨1478357, by rfl⟩ : syracuseStep 1971143 = 2956715) B2956715
theorem B1971179 : Blo 872567 1971179 := bstep (se 1 (by rfl) ⟨1478384, by rfl⟩ : syracuseStep 1971179 = 2956769) B2956769
theorem B1971305 : Blo 872567 1971305 := bstep (se 2 (by rfl) ⟨739239, by rfl⟩ : syracuseStep 1971305 = 1478479) B1478479
theorem B4789469 : Blo 872567 4789469 := bstep (se 3 (by rfl) ⟨898025, by rfl⟩ : syracuseStep 4789469 = 1796051) B1796051
theorem B4986269 : Blo 872567 4986269 := bstep (se 3 (by rfl) ⟨934925, by rfl⟩ : syracuseStep 4986269 = 1869851) B1869851
theorem B2954663 : Blo 872567 2954663 := bstep (se 1 (by rfl) ⟨2215997, by rfl⟩ : syracuseStep 2954663 = 4431995) B4431995
theorem B1971881 : Blo 872567 1971881 := bstep (se 2 (by rfl) ⟨739455, by rfl⟩ : syracuseStep 1971881 = 1478911) B1478911
theorem B3315431 : Blo 872567 3315431 := bstep (se 1 (by rfl) ⟨2486573, by rfl⟩ : syracuseStep 3315431 = 4973147) B4973147
theorem B76519201 : Blo 872567 76519201 := bstep (se 2 (by rfl) ⟨28694700, by rfl⟩ : syracuseStep 76519201 = 57389401) B57389401
theorem B7477217 : Blo 872567 7477217 := bstep (se 2 (by rfl) ⟨2803956, by rfl⟩ : syracuseStep 7477217 = 5607913) B5607913
theorem B4431023 : Blo 872567 4431023 := bstep (se 1 (by rfl) ⟨3323267, by rfl⟩ : syracuseStep 4431023 = 6646535) B6646535
theorem B4725971 : Blo 872567 4725971 := bstep (se 1 (by rfl) ⟨3544478, by rfl⟩ : syracuseStep 4725971 = 7088957) B7088957
theorem B4988729 : Blo 872567 4988729 := bstep (se 2 (by rfl) ⟨1870773, by rfl⟩ : syracuseStep 4988729 = 3741547) B3741547
theorem B2957255 : Blo 872567 2957255 := bstep (se 1 (by rfl) ⟨2217941, by rfl⟩ : syracuseStep 2957255 = 4435883) B4435883
theorem B5054561 : Blo 872567 5054561 := bstep (se 2 (by rfl) ⟨1895460, by rfl⟩ : syracuseStep 5054561 = 3790921) B3790921
theorem B26910953 : Blo 872567 26910953 := bstep (se 2 (by rfl) ⟨10091607, by rfl⟩ : syracuseStep 26910953 = 20183215) B20183215
theorem B6627581 : Blo 872567 6627581 := bstep (se 3 (by rfl) ⟨1242671, by rfl⟩ : syracuseStep 6627581 = 2485343) B2485343
theorem B4990895 : Blo 872567 4990895 := bstep (se 1 (by rfl) ⟨3743171, by rfl⟩ : syracuseStep 4990895 = 7486343) B7486343
theorem B14919713 : Blo 872567 14919713 := bstep (se 2 (by rfl) ⟨5594892, by rfl⟩ : syracuseStep 14919713 = 11189785) B11189785
theorem B7481591 : Blo 872567 7481591 := bstep (se 1 (by rfl) ⟨5611193, by rfl⟩ : syracuseStep 7481591 = 11222387) B11222387
theorem B30255407 : Blo 872567 30255407 := bstep (se 1 (by rfl) ⟨22691555, by rfl⟩ : syracuseStep 30255407 = 45383111) B45383111
theorem B4434749 : Blo 872567 4434749 := bstep (se 3 (by rfl) ⟨831515, by rfl⟩ : syracuseStep 4434749 = 1663031) B1663031
theorem B9974177 : Blo 872567 9974177 := bstep (se 2 (by rfl) ⟨3740316, by rfl⟩ : syracuseStep 9974177 = 7480633) B7480633
theorem B32846759 : Blo 872567 32846759 := bstep (se 1 (by rfl) ⟨24635069, by rfl⟩ : syracuseStep 32846759 = 49270139) B49270139
theorem B4437017 : Blo 872567 4437017 := bstep (se 2 (by rfl) ⟨1663881, by rfl⟩ : syracuseStep 4437017 = 3327763) B3327763
theorem B35894411 : Blo 872567 35894411 := bstep (se 1 (by rfl) ⟨26920808, by rfl⟩ : syracuseStep 35894411 = 53841617) B53841617
theorem B4437179 : Blo 872567 4437179 := bstep (se 1 (by rfl) ⟨3327884, by rfl⟩ : syracuseStep 4437179 = 6655769) B6655769
theorem B2208991 : Blo 872567 2208991 := bstep (se 1 (by rfl) ⟨1656743, by rfl⟩ : syracuseStep 2208991 = 3313487) B3313487
theorem B7485007 : Blo 872567 7485007 := bstep (se 1 (by rfl) ⟨5613755, by rfl⟩ : syracuseStep 7485007 = 11227511) B11227511
theorem B9975635 : Blo 872567 9975635 := bstep (se 1 (by rfl) ⟨7481726, by rfl⟩ : syracuseStep 9975635 = 14963453) B14963453
theorem B6305789 : Blo 872567 6305789 := bstep (se 3 (by rfl) ⟨1182335, by rfl⟩ : syracuseStep 6305789 = 2364671) B2364671
theorem B2209913 : Blo 872567 2209913 := bstep (se 2 (by rfl) ⟨828717, by rfl⟩ : syracuseStep 2209913 = 1657435) B1657435
theorem B9943559 : Blo 872567 9943559 := bstep (se 1 (by rfl) ⟨7457669, by rfl⟩ : syracuseStep 9943559 = 14915339) B14915339
theorem B28720655 : Blo 872567 28720655 := bstep (se 1 (by rfl) ⟨21540491, by rfl⟩ : syracuseStep 28720655 = 43080983) B43080983
theorem B28786337 : Blo 872567 28786337 := bstep (se 2 (by rfl) ⟨10794876, by rfl⟩ : syracuseStep 28786337 = 21589753) B21589753
theorem B4210471 : Blo 872567 4210471 := bstep (se 1 (by rfl) ⟨3157853, by rfl⟩ : syracuseStep 4210471 = 6315707) B6315707
theorem B76595233 : Blo 872567 76595233 := bstep (se 2 (by rfl) ⟨28723212, by rfl⟩ : syracuseStep 76595233 = 57446425) B57446425
theorem B12632111 : Blo 872567 12632111 := bstep (se 1 (by rfl) ⟨9474083, by rfl⟩ : syracuseStep 12632111 = 18948167) B18948167
theorem B15123773 : Blo 872567 15123773 := bstep (se 3 (by rfl) ⟨2835707, by rfl⟩ : syracuseStep 15123773 = 5671415) B5671415
theorem B1659113 : Blo 872567 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B872927 : Blo 872567 872927 := bstep (se 1 (by rfl) ⟨654695, by rfl⟩ : syracuseStep 872927 = 1309391) B1309391
theorem B2216423 : Blo 872567 2216423 := bstep (se 1 (by rfl) ⟨1662317, by rfl⟩ : syracuseStep 2216423 = 3324635) B3324635
theorem B872987 : Blo 872567 872987 := bstep (se 1 (by rfl) ⟨654740, by rfl⟩ : syracuseStep 872987 = 1309481) B1309481
theorem B873087 : Blo 872567 873087 := bstep (se 1 (by rfl) ⟨654815, by rfl⟩ : syracuseStep 873087 = 1309631) B1309631
theorem B873343 : Blo 872567 873343 := bstep (se 1 (by rfl) ⟨655007, by rfl⟩ : syracuseStep 873343 = 1310015) B1310015
theorem B873575 : Blo 872567 873575 := bstep (se 1 (by rfl) ⟨655181, by rfl⟩ : syracuseStep 873575 = 1310363) B1310363
theorem B2217071 : Blo 872567 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B4969775 : Blo 872567 4969775 := bstep (se 1 (by rfl) ⟨3727331, by rfl⟩ : syracuseStep 4969775 = 7454663) B7454663
theorem B4969957 : Blo 872567 4969957 := bstep (se 4 (by rfl) ⟨465933, by rfl⟩ : syracuseStep 4969957 = 931867) B931867
theorem B874559 : Blo 872567 874559 := bstep (se 1 (by rfl) ⟨655919, by rfl⟩ : syracuseStep 874559 = 1311839) B1311839
theorem B874599 : Blo 872567 874599 := bstep (se 1 (by rfl) ⟨655949, by rfl⟩ : syracuseStep 874599 = 1311899) B1311899
theorem B9460415 : Blo 872567 9460415 := bstep (se 1 (by rfl) ⟨7095311, by rfl⟩ : syracuseStep 9460415 = 14190623) B14190623
theorem B875391 : Blo 872567 875391 := bstep (se 1 (by rfl) ⟨656543, by rfl⟩ : syracuseStep 875391 = 1313087) B1313087
theorem B875839 : Blo 872567 875839 := bstep (se 1 (by rfl) ⟨656879, by rfl⟩ : syracuseStep 875839 = 1313759) B1313759
theorem B9854585 : Blo 872567 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B7463411 : Blo 872567 7463411 := bstep (se 1 (by rfl) ⟨5597558, by rfl⟩ : syracuseStep 7463411 = 11195117) B11195117
theorem B9463013 : Blo 872567 9463013 := bstep (se 4 (by rfl) ⟨887157, by rfl⟩ : syracuseStep 9463013 = 1774315) B1774315
theorem B1107199 : Blo 872567 1107199 := bstep (se 1 (by rfl) ⟨830399, by rfl⟩ : syracuseStep 1107199 = 1660799) B1660799
theorem B8512847 : Blo 872567 8512847 := bstep (se 1 (by rfl) ⟨6384635, by rfl⟩ : syracuseStep 8512847 = 12769271) B12769271
theorem B1402363 : Blo 872567 1402363 := bstep (se 1 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 1402363 = 2103545) B2103545
theorem B5990375 : Blo 872567 5990375 := bstep (se 1 (by rfl) ⟨4492781, by rfl⟩ : syracuseStep 5990375 = 8985563) B8985563
theorem B3729503 : Blo 872567 3729503 := bstep (se 1 (by rfl) ⟨2797127, by rfl⟩ : syracuseStep 3729503 = 5594255) B5594255
theorem B4976063 : Blo 872567 4976063 := bstep (se 1 (by rfl) ⟨3732047, by rfl⟩ : syracuseStep 4976063 = 7464095) B7464095
theorem B2945267 : Blo 872567 2945267 := bstep (se 1 (by rfl) ⟨2208950, by rfl⟩ : syracuseStep 2945267 = 4417901) B4417901
theorem B2945375 : Blo 872567 2945375 := bstep (se 1 (by rfl) ⟨2209031, by rfl⟩ : syracuseStep 2945375 = 4418063) B4418063
theorem B5993455 : Blo 872567 5993455 := bstep (se 1 (by rfl) ⟨4495091, by rfl⟩ : syracuseStep 5993455 = 8990183) B8990183
theorem B4420817 : Blo 872567 4420817 := bstep (se 2 (by rfl) ⟨1657806, by rfl⟩ : syracuseStep 4420817 = 3315613) B3315613
theorem B1996159 : Blo 872567 1996159 := bstep (se 1 (by rfl) ⟨1497119, by rfl⟩ : syracuseStep 1996159 = 2994239) B2994239
theorem B2946779 : Blo 872567 2946779 := bstep (se 1 (by rfl) ⟨2210084, by rfl⟩ : syracuseStep 2946779 = 4420169) B4420169
theorem B14153717 : Blo 872567 14153717 := bstep (se 5 (by rfl) ⟨663455, by rfl⟩ : syracuseStep 14153717 = 1326911) B1326911
theorem B1964105 : Blo 872567 1964105 := bstep (se 2 (by rfl) ⟨736539, by rfl⟩ : syracuseStep 1964105 = 1473079) B1473079
theorem B47872133 : Blo 872567 47872133 := bstep (se 4 (by rfl) ⟨4488012, by rfl⟩ : syracuseStep 47872133 = 8976025) B8976025
theorem B1308923 : Blo 872567 1308923 := bstep (se 1 (by rfl) ⟨981692, by rfl⟩ : syracuseStep 1308923 = 1963385) B1963385
theorem B4979231 : Blo 872567 4979231 := bstep (se 1 (by rfl) ⟨3734423, by rfl⟩ : syracuseStep 4979231 = 7468847) B7468847
theorem B1964591 : Blo 872567 1964591 := bstep (se 1 (by rfl) ⟨1473443, by rfl⟩ : syracuseStep 1964591 = 2946887) B2946887
theorem B17955407 : Blo 872567 17955407 := bstep (se 1 (by rfl) ⟨13466555, by rfl⟩ : syracuseStep 17955407 = 26933111) B26933111
theorem B2947751 : Blo 872567 2947751 := bstep (se 1 (by rfl) ⟨2210813, by rfl⟩ : syracuseStep 2947751 = 4421627) B4421627
theorem B1473403 : Blo 872567 1473403 := bstep (se 1 (by rfl) ⟨1105052, by rfl⟩ : syracuseStep 1473403 = 2210105) B2210105
theorem B1309751 : Blo 872567 1309751 := bstep (se 1 (by rfl) ⟨982313, by rfl⟩ : syracuseStep 1309751 = 1964627) B1964627
theorem B1310249 : Blo 872567 1310249 := bstep (se 2 (by rfl) ⟨491343, by rfl⟩ : syracuseStep 1310249 = 982687) B982687
theorem B1310255 : Blo 872567 1310255 := bstep (se 1 (by rfl) ⟨982691, by rfl⟩ : syracuseStep 1310255 = 1965383) B1965383
theorem B1474267 : Blo 872567 1474267 := bstep (se 1 (by rfl) ⟨1105700, by rfl⟩ : syracuseStep 1474267 = 2211401) B2211401
theorem B2391805 : Blo 872567 2391805 := bstep (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) B896927
theorem B1965887 : Blo 872567 1965887 := bstep (se 1 (by rfl) ⟨1474415, by rfl⟩ : syracuseStep 1965887 = 2948831) B2948831
theorem B1966049 : Blo 872567 1966049 := bstep (se 2 (by rfl) ⟨737268, by rfl⟩ : syracuseStep 1966049 = 1474537) B1474537
theorem B15138791 : Blo 872567 15138791 := bstep (se 1 (by rfl) ⟨11354093, by rfl⟩ : syracuseStep 15138791 = 22708187) B22708187
theorem B8421407 : Blo 872567 8421407 := bstep (se 1 (by rfl) ⟨6316055, by rfl⟩ : syracuseStep 8421407 = 12632111) B12632111
theorem B2949263 : Blo 872567 2949263 := bstep (se 1 (by rfl) ⟨2211947, by rfl⟩ : syracuseStep 2949263 = 4423895) B4423895
theorem B11337887 : Blo 872567 11337887 := bstep (se 1 (by rfl) ⟨8503415, by rfl⟩ : syracuseStep 11337887 = 17006831) B17006831
theorem B1966319 : Blo 872567 1966319 := bstep (se 1 (by rfl) ⟨1474739, by rfl⟩ : syracuseStep 1966319 = 2949479) B2949479
theorem B2949371 : Blo 872567 2949371 := bstep (se 1 (by rfl) ⟨2212028, by rfl⟩ : syracuseStep 2949371 = 4424057) B4424057
theorem B2490983 : Blo 872567 2490983 := bstep (se 1 (by rfl) ⟨1868237, by rfl⟩ : syracuseStep 2490983 = 3736475) B3736475
theorem B983803 : Blo 872567 983803 := bstep (se 1 (by rfl) ⟨737852, by rfl⟩ : syracuseStep 983803 = 1475705) B1475705
theorem B1311515 : Blo 872567 1311515 := bstep (se 1 (by rfl) ⟨983636, by rfl⟩ : syracuseStep 1311515 = 1967273) B1967273
theorem B1311647 : Blo 872567 1311647 := bstep (se 1 (by rfl) ⟨983735, by rfl⟩ : syracuseStep 1311647 = 1967471) B1967471
theorem B16843727 : Blo 872567 16843727 := bstep (se 1 (by rfl) ⟨12632795, by rfl⟩ : syracuseStep 16843727 = 25265591) B25265591
theorem B2950235 : Blo 872567 2950235 := bstep (se 1 (by rfl) ⟨2212676, by rfl⟩ : syracuseStep 2950235 = 4425353) B4425353
theorem B1312055 : Blo 872567 1312055 := bstep (se 1 (by rfl) ⟨984041, by rfl⟩ : syracuseStep 1312055 = 1968083) B1968083
theorem B1967417 : Blo 872567 1967417 := bstep (se 2 (by rfl) ⟨737781, by rfl⟩ : syracuseStep 1967417 = 1475563) B1475563
theorem B1049927 : Blo 872567 1049927 := bstep (se 1 (by rfl) ⟨787445, by rfl⟩ : syracuseStep 1049927 = 1574891) B1574891
theorem B2950559 : Blo 872567 2950559 := bstep (se 1 (by rfl) ⟨2212919, by rfl⟩ : syracuseStep 2950559 = 4425839) B4425839
theorem B2491859 : Blo 872567 2491859 := bstep (se 1 (by rfl) ⟨1868894, by rfl⟩ : syracuseStep 2491859 = 3737789) B3737789
theorem B984667 : Blo 872567 984667 := bstep (se 1 (by rfl) ⟨738500, by rfl⟩ : syracuseStep 984667 = 1477001) B1477001
theorem B2885257 : Blo 872567 2885257 := bstep (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) B2163943
theorem B1312415 : Blo 872567 1312415 := bstep (se 1 (by rfl) ⟨984311, by rfl⟩ : syracuseStep 1312415 = 1968623) B1968623
theorem B1476265 : Blo 872567 1476265 := bstep (se 2 (by rfl) ⟨553599, by rfl⟩ : syracuseStep 1476265 = 1107199) B1107199
theorem B3147503 : Blo 872567 3147503 := bstep (se 1 (by rfl) ⟨2360627, by rfl⟩ : syracuseStep 3147503 = 4721255) B4721255
theorem B3737515 : Blo 872567 3737515 := bstep (se 1 (by rfl) ⟨2803136, by rfl⟩ : syracuseStep 3737515 = 5606273) B5606273
theorem B1312745 : Blo 872567 1312745 := bstep (se 2 (by rfl) ⟨492279, by rfl⟩ : syracuseStep 1312745 = 984559) B984559
theorem B1869817 : Blo 872567 1869817 := bstep (se 2 (by rfl) ⟨701181, by rfl⟩ : syracuseStep 1869817 = 1402363) B1402363
theorem B1312763 : Blo 872567 1312763 := bstep (se 1 (by rfl) ⟨984572, by rfl⟩ : syracuseStep 1312763 = 1969145) B1969145
theorem B1050715 : Blo 872567 1050715 := bstep (se 1 (by rfl) ⟨788036, by rfl⟩ : syracuseStep 1050715 = 1576073) B1576073
theorem B1312943 : Blo 872567 1312943 := bstep (se 1 (by rfl) ⟨984707, by rfl⟩ : syracuseStep 1312943 = 1969415) B1969415
theorem B1477615 : Blo 872567 1477615 := bstep (se 1 (by rfl) ⟨1108211, by rfl⟩ : syracuseStep 1477615 = 2216423) B2216423
theorem B1314095 : Blo 872567 1314095 := bstep (se 1 (by rfl) ⟨985571, by rfl⟩ : syracuseStep 1314095 = 1971143) B1971143
theorem B1314119 : Blo 872567 1314119 := bstep (se 1 (by rfl) ⟨985589, by rfl⟩ : syracuseStep 1314119 = 1971179) B1971179
theorem B1314203 : Blo 872567 1314203 := bstep (se 1 (by rfl) ⟨985652, by rfl⟩ : syracuseStep 1314203 = 1971305) B1971305
theorem B1478047 : Blo 872567 1478047 := bstep (se 1 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 1478047 = 2217071) B2217071
theorem B3313183 : Blo 872567 3313183 := bstep (se 1 (by rfl) ⟨2484887, by rfl⟩ : syracuseStep 3313183 = 4969775) B4969775
theorem B1969775 : Blo 872567 1969775 := bstep (se 1 (by rfl) ⟨1477331, by rfl⟩ : syracuseStep 1969775 = 2954663) B2954663
theorem B1314425 : Blo 872567 1314425 := bstep (se 2 (by rfl) ⟨492909, by rfl⟩ : syracuseStep 1314425 = 985819) B985819
theorem B1314587 : Blo 872567 1314587 := bstep (se 1 (by rfl) ⟨985940, by rfl⟩ : syracuseStep 1314587 = 1971881) B1971881
theorem B4984811 : Blo 872567 4984811 := bstep (se 1 (by rfl) ⟨3738608, by rfl⟩ : syracuseStep 4984811 = 7477217) B7477217
theorem B2954015 : Blo 872567 2954015 := bstep (se 1 (by rfl) ⟨2215511, by rfl⟩ : syracuseStep 2954015 = 4431023) B4431023
theorem B3150647 : Blo 872567 3150647 := bstep (se 1 (by rfl) ⟨2362985, by rfl⟩ : syracuseStep 3150647 = 4725971) B4725971
theorem B1971503 : Blo 872567 1971503 := bstep (se 1 (by rfl) ⟨1478627, by rfl⟩ : syracuseStep 1971503 = 2957255) B2957255
theorem B5675231 : Blo 872567 5675231 := bstep (se 1 (by rfl) ⟨4256423, by rfl⟩ : syracuseStep 5675231 = 8512847) B8512847
theorem B4987727 : Blo 872567 4987727 := bstep (se 1 (by rfl) ⟨3740795, by rfl⟩ : syracuseStep 4987727 = 7481591) B7481591
theorem B2661545 : Blo 872567 2661545 := bstep (se 2 (by rfl) ⟨998079, by rfl⟩ : syracuseStep 2661545 = 1996159) B1996159
theorem B2956499 : Blo 872567 2956499 := bstep (se 1 (by rfl) ⟨2217374, by rfl⟩ : syracuseStep 2956499 = 4434749) B4434749
theorem B6626609 : Blo 872567 6626609 := bstep (se 2 (by rfl) ⟨2484978, by rfl⟩ : syracuseStep 6626609 = 4969957) B4969957
theorem B3317375 : Blo 872567 3317375 := bstep (se 1 (by rfl) ⟨2488031, by rfl⟩ : syracuseStep 3317375 = 4976063) B4976063
theorem B21897839 : Blo 872567 21897839 := bstep (se 1 (by rfl) ⟨16423379, by rfl⟩ : syracuseStep 21897839 = 32846759) B32846759
theorem B2958011 : Blo 872567 2958011 := bstep (se 1 (by rfl) ⟨2218508, by rfl⟩ : syracuseStep 2958011 = 4437017) B4437017
theorem B23929607 : Blo 872567 23929607 := bstep (se 1 (by rfl) ⟨17947205, by rfl⟩ : syracuseStep 23929607 = 35894411) B35894411
theorem B2958119 : Blo 872567 2958119 := bstep (se 1 (by rfl) ⟨2218589, by rfl⟩ : syracuseStep 2958119 = 4437179) B4437179
theorem B4203859 : Blo 872567 4203859 := bstep (se 1 (by rfl) ⟨3152894, by rfl⟩ : syracuseStep 4203859 = 6305789) B6305789
theorem B6629039 : Blo 872567 6629039 := bstep (se 1 (by rfl) ⟨4971779, by rfl⟩ : syracuseStep 6629039 = 9943559) B9943559
theorem B3319487 : Blo 872567 3319487 := bstep (se 1 (by rfl) ⟨2489615, by rfl⟩ : syracuseStep 3319487 = 4979231) B4979231
theorem B11970271 : Blo 872567 11970271 := bstep (se 1 (by rfl) ⟨8977703, by rfl⟩ : syracuseStep 11970271 = 17955407) B17955407
theorem B3189073 : Blo 872567 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B19147103 : Blo 872567 19147103 := bstep (se 1 (by rfl) ⟨14360327, by rfl⟩ : syracuseStep 19147103 = 28720655) B28720655
theorem B5613961 : Blo 872567 5613961 := bstep (se 2 (by rfl) ⟨2105235, by rfl⟩ : syracuseStep 5613961 = 4210471) B4210471
theorem B3321263 : Blo 872567 3321263 := bstep (se 1 (by rfl) ⟨2490947, by rfl⟩ : syracuseStep 3321263 = 4981895) B4981895
theorem B21278143 : Blo 872567 21278143 := bstep (se 1 (by rfl) ⟨15958607, by rfl⟩ : syracuseStep 21278143 = 31917215) B31917215
theorem B3192979 : Blo 872567 3192979 := bstep (se 1 (by rfl) ⟨2394734, by rfl⟩ : syracuseStep 3192979 = 4789469) B4789469
theorem B3324179 : Blo 872567 3324179 := bstep (se 1 (by rfl) ⟨2493134, by rfl⟩ : syracuseStep 3324179 = 4986269) B4986269
theorem B2210287 : Blo 872567 2210287 := bstep (se 1 (by rfl) ⟨1657715, by rfl⟩ : syracuseStep 2210287 = 3315431) B3315431
theorem B6306943 : Blo 872567 6306943 := bstep (se 1 (by rfl) ⟨4730207, by rfl⟩ : syracuseStep 6306943 = 9460415) B9460415
theorem B6569723 : Blo 872567 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B3325819 : Blo 872567 3325819 := bstep (se 1 (by rfl) ⟨2494364, by rfl⟩ : syracuseStep 3325819 = 4988729) B4988729
theorem B17940635 : Blo 872567 17940635 := bstep (se 1 (by rfl) ⟨13455476, by rfl⟩ : syracuseStep 17940635 = 26910953) B26910953
theorem B3326777 : Blo 872567 3326777 := bstep (se 2 (by rfl) ⟨1247541, by rfl⟩ : syracuseStep 3326777 = 2495083) B2495083
theorem B6308675 : Blo 872567 6308675 := bstep (se 1 (by rfl) ⟨4731506, by rfl⟩ : syracuseStep 6308675 = 9463013) B9463013
theorem B3327263 : Blo 872567 3327263 := bstep (se 1 (by rfl) ⟨2495447, by rfl⟩ : syracuseStep 3327263 = 4990895) B4990895
theorem B9946475 : Blo 872567 9946475 := bstep (se 1 (by rfl) ⟨7459856, by rfl⟩ : syracuseStep 9946475 = 14919713) B14919713
theorem B20170271 : Blo 872567 20170271 := bstep (se 1 (by rfl) ⟨15127703, by rfl⟩ : syracuseStep 20170271 = 30255407) B30255407
theorem B9980009 : Blo 872567 9980009 := bstep (se 2 (by rfl) ⟨3742503, by rfl⟩ : syracuseStep 9980009 = 7485007) B7485007
theorem B102025601 : Blo 872567 102025601 := bstep (se 2 (by rfl) ⟨38259600, by rfl⟩ : syracuseStep 102025601 = 76519201) B76519201
theorem B872615 : Blo 872567 872615 := bstep (se 1 (by rfl) ⟨654461, by rfl⟩ : syracuseStep 872615 = 1308923) B1308923
theorem B873167 : Blo 872567 873167 := bstep (se 1 (by rfl) ⟨654875, by rfl⟩ : syracuseStep 873167 = 1309751) B1309751
theorem B873499 : Blo 872567 873499 := bstep (se 1 (by rfl) ⟨655124, by rfl⟩ : syracuseStep 873499 = 1310249) B1310249
theorem B873503 : Blo 872567 873503 := bstep (se 1 (by rfl) ⟨655127, by rfl⟩ : syracuseStep 873503 = 1310255) B1310255
theorem B19190891 : Blo 872567 19190891 := bstep (se 1 (by rfl) ⟨14393168, by rfl⟩ : syracuseStep 19190891 = 28786337) B28786337
theorem B102126977 : Blo 872567 102126977 := bstep (se 2 (by rfl) ⟨38297616, by rfl⟩ : syracuseStep 102126977 = 76595233) B76595233
theorem B874215 : Blo 872567 874215 := bstep (se 1 (by rfl) ⟨655661, by rfl⟩ : syracuseStep 874215 = 1311323) B1311323
theorem B11950247 : Blo 872567 11950247 := bstep (se 1 (by rfl) ⟨8962685, by rfl⟩ : syracuseStep 11950247 = 17925371) B17925371
theorem B10082515 : Blo 872567 10082515 := bstep (se 1 (by rfl) ⟨7561886, by rfl⟩ : syracuseStep 10082515 = 15123773) B15123773
theorem B4544923 : Blo 872567 4544923 := bstep (se 1 (by rfl) ⟨3408692, by rfl⟩ : syracuseStep 4544923 = 6817385) B6817385
theorem B875007 : Blo 872567 875007 := bstep (se 1 (by rfl) ⟨656255, by rfl⟩ : syracuseStep 875007 = 1312511) B1312511
theorem B3365657 : Blo 872567 3365657 := bstep (se 2 (by rfl) ⟨1262121, by rfl⟩ : syracuseStep 3365657 = 2524243) B2524243
theorem B8412295 : Blo 872567 8412295 := bstep (se 1 (by rfl) ⟨6309221, by rfl⟩ : syracuseStep 8412295 = 12618443) B12618443
theorem B875687 : Blo 872567 875687 := bstep (se 1 (by rfl) ⟨656765, by rfl⟩ : syracuseStep 875687 = 1313531) B1313531
theorem B875823 : Blo 872567 875823 := bstep (se 1 (by rfl) ⟨656867, by rfl⟩ : syracuseStep 875823 = 1313735) B1313735
theorem B876031 : Blo 872567 876031 := bstep (se 1 (by rfl) ⟨657023, by rfl⟩ : syracuseStep 876031 = 1314047) B1314047
theorem B876379 : Blo 872567 876379 := bstep (se 1 (by rfl) ⟨657284, by rfl⟩ : syracuseStep 876379 = 1314569) B1314569
theorem B876415 : Blo 872567 876415 := bstep (se 1 (by rfl) ⟨657311, by rfl⟩ : syracuseStep 876415 = 1314623) B1314623
theorem B1400825 : Blo 872567 1400825 := bstep (se 2 (by rfl) ⟨525309, by rfl⟩ : syracuseStep 1400825 = 1050619) B1050619
theorem B1106075 : Blo 872567 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B3369707 : Blo 872567 3369707 := bstep (se 1 (by rfl) ⟨2527280, by rfl⟩ : syracuseStep 3369707 = 5054561) B5054561
theorem B4418387 : Blo 872567 4418387 := bstep (se 1 (by rfl) ⟨3313790, by rfl⟩ : syracuseStep 4418387 = 6627581) B6627581
theorem B4975607 : Blo 872567 4975607 := bstep (se 1 (by rfl) ⟨3731705, by rfl⟩ : syracuseStep 4975607 = 7463411) B7463411
theorem B7991273 : Blo 872567 7991273 := bstep (se 2 (by rfl) ⟨2996727, by rfl⟩ : syracuseStep 7991273 = 5993455) B5993455
theorem B3993583 : Blo 872567 3993583 := bstep (se 1 (by rfl) ⟨2995187, by rfl⟩ : syracuseStep 3993583 = 5990375) B5990375
theorem B2486335 : Blo 872567 2486335 := bstep (se 1 (by rfl) ⟨1864751, by rfl⟩ : syracuseStep 2486335 = 3729503) B3729503
theorem B2945321 : Blo 872567 2945321 := bstep (se 2 (by rfl) ⟨1104495, by rfl⟩ : syracuseStep 2945321 = 2208991) B2208991
theorem B1963511 : Blo 872567 1963511 := bstep (se 1 (by rfl) ⟨1472633, by rfl⟩ : syracuseStep 1963511 = 2945267) B2945267
theorem B1963583 : Blo 872567 1963583 := bstep (se 1 (by rfl) ⟨1472687, by rfl⟩ : syracuseStep 1963583 = 2945375) B2945375
theorem B6649451 : Blo 872567 6649451 := bstep (se 1 (by rfl) ⟨4987088, by rfl⟩ : syracuseStep 6649451 = 9974177) B9974177
theorem B2947211 : Blo 872567 2947211 := bstep (se 1 (by rfl) ⟨2210408, by rfl⟩ : syracuseStep 2947211 = 4420817) B4420817
theorem B1964519 : Blo 872567 1964519 := bstep (se 1 (by rfl) ⟨1473389, by rfl⟩ : syracuseStep 1964519 = 2946779) B2946779
theorem B1964537 : Blo 872567 1964537 := bstep (se 2 (by rfl) ⟨736701, by rfl⟩ : syracuseStep 1964537 = 1473403) B1473403
theorem B6650423 : Blo 872567 6650423 := bstep (se 1 (by rfl) ⟨4987817, by rfl⟩ : syracuseStep 6650423 = 9975635) B9975635
theorem B9435811 : Blo 872567 9435811 := bstep (se 1 (by rfl) ⟨7076858, by rfl⟩ : syracuseStep 9435811 = 14153717) B14153717
theorem B1309403 : Blo 872567 1309403 := bstep (se 1 (by rfl) ⟨982052, by rfl⟩ : syracuseStep 1309403 = 1964105) B1964105
theorem B1473275 : Blo 872567 1473275 := bstep (se 1 (by rfl) ⟨1104956, by rfl⟩ : syracuseStep 1473275 = 2209913) B2209913
theorem B31914755 : Blo 872567 31914755 := bstep (se 1 (by rfl) ⟨23936066, by rfl⟩ : syracuseStep 31914755 = 47872133) B47872133
theorem B1309727 : Blo 872567 1309727 := bstep (se 1 (by rfl) ⟨982295, by rfl⟩ : syracuseStep 1309727 = 1964591) B1964591
theorem B1965167 : Blo 872567 1965167 := bstep (se 1 (by rfl) ⟨1473875, by rfl⟩ : syracuseStep 1965167 = 2947751) B2947751
theorem B1965689 : Blo 872567 1965689 := bstep (se 2 (by rfl) ⟨737133, by rfl⟩ : syracuseStep 1965689 = 1474267) B1474267
theorem B1310591 : Blo 872567 1310591 := bstep (se 1 (by rfl) ⟨982943, by rfl⟩ : syracuseStep 1310591 = 1965887) B1965887
theorem B1310699 : Blo 872567 1310699 := bstep (se 1 (by rfl) ⟨983024, by rfl⟩ : syracuseStep 1310699 = 1966049) B1966049
theorem B10092527 : Blo 872567 10092527 := bstep (se 1 (by rfl) ⟨7569395, by rfl⟩ : syracuseStep 10092527 = 15138791) B15138791
theorem B1966175 : Blo 872567 1966175 := bstep (se 1 (by rfl) ⟨1474631, by rfl⟩ : syracuseStep 1966175 = 2949263) B2949263
theorem B11960423 : Blo 872567 11960423 := bstep (se 1 (by rfl) ⟨8970317, by rfl⟩ : syracuseStep 11960423 = 17940635) B17940635
theorem B1310879 : Blo 872567 1310879 := bstep (se 1 (by rfl) ⟨983159, by rfl⟩ : syracuseStep 1310879 = 1966319) B1966319
theorem B1966247 : Blo 872567 1966247 := bstep (se 1 (by rfl) ⟨1474685, by rfl⟩ : syracuseStep 1966247 = 2949371) B2949371
theorem B2949533 : Blo 872567 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B5603813 : Blo 872567 5603813 := bstep (se 4 (by rfl) ⟨525357, by rfl⟩ : syracuseStep 5603813 = 1050715) B1050715
theorem B1966823 : Blo 872567 1966823 := bstep (se 1 (by rfl) ⟨1475117, by rfl⟩ : syracuseStep 1966823 = 2950235) B2950235
theorem B1311611 : Blo 872567 1311611 := bstep (se 1 (by rfl) ⟨983708, by rfl⟩ : syracuseStep 1311611 = 1967417) B1967417
theorem B1967039 : Blo 872567 1967039 := bstep (se 1 (by rfl) ⟨1475279, by rfl⟩ : syracuseStep 1967039 = 2950559) B2950559
theorem B1311737 : Blo 872567 1311737 := bstep (se 2 (by rfl) ⟨491901, by rfl⟩ : syracuseStep 1311737 = 983803) B983803
theorem B6653339 : Blo 872567 6653339 := bstep (se 1 (by rfl) ⟨4990004, by rfl⟩ : syracuseStep 6653339 = 9980009) B9980009
theorem B5605145 : Blo 872567 5605145 := bstep (se 2 (by rfl) ⟨2101929, by rfl⟩ : syracuseStep 5605145 = 4203859) B4203859
theorem B1312889 : Blo 872567 1312889 := bstep (se 2 (by rfl) ⟨492333, by rfl⟩ : syracuseStep 1312889 = 984667) B984667
theorem B1968353 : Blo 872567 1968353 := bstep (se 2 (by rfl) ⟨738132, by rfl⟩ : syracuseStep 1968353 = 1476265) B1476265
theorem B15960361 : Blo 872567 15960361 := bstep (se 2 (by rfl) ⟨5985135, by rfl⟩ : syracuseStep 15960361 = 11970271) B11970271
theorem B1313183 : Blo 872567 1313183 := bstep (se 1 (by rfl) ⟨984887, by rfl⟩ : syracuseStep 1313183 = 1969775) B1969775
theorem B4983353 : Blo 872567 4983353 := bstep (se 2 (by rfl) ⟨1868757, by rfl⟩ : syracuseStep 4983353 = 3737515) B3737515
theorem B2493089 : Blo 872567 2493089 := bstep (se 2 (by rfl) ⟨934908, by rfl⟩ : syracuseStep 2493089 = 1869817) B1869817
theorem B1969343 : Blo 872567 1969343 := bstep (se 1 (by rfl) ⟨1477007, by rfl⟩ : syracuseStep 1969343 = 2954015) B2954015
theorem B2100431 : Blo 872567 2100431 := bstep (se 1 (by rfl) ⟨1575323, by rfl⟩ : syracuseStep 2100431 = 3150647) B3150647
theorem B1314335 : Blo 872567 1314335 := bstep (se 1 (by rfl) ⟨985751, by rfl⟩ : syracuseStep 1314335 = 1971503) B1971503
theorem B1970153 : Blo 872567 1970153 := bstep (se 2 (by rfl) ⟨738807, by rfl⟩ : syracuseStep 1970153 = 1477615) B1477615
theorem B7966831 : Blo 872567 7966831 := bstep (se 1 (by rfl) ⟨5975123, by rfl⟩ : syracuseStep 7966831 = 11950247) B11950247
theorem B1970729 : Blo 872567 1970729 := bstep (se 2 (by rfl) ⟨739023, by rfl⟩ : syracuseStep 1970729 = 1478047) B1478047
theorem B8393341 : Blo 872567 8393341 := bstep (se 3 (by rfl) ⟨1573751, by rfl⟩ : syracuseStep 8393341 = 3147503) B3147503
theorem B1970999 : Blo 872567 1970999 := bstep (se 1 (by rfl) ⟨1478249, by rfl⟩ : syracuseStep 1970999 = 2956499) B2956499
theorem B3315113 : Blo 872567 3315113 := bstep (se 2 (by rfl) ⟨1243167, by rfl⟩ : syracuseStep 3315113 = 2486335) B2486335
theorem B1972007 : Blo 872567 1972007 := bstep (se 1 (by rfl) ⟨1479005, by rfl⟩ : syracuseStep 1972007 = 2958011) B2958011
theorem B1972079 : Blo 872567 1972079 := bstep (se 1 (by rfl) ⟨1479059, by rfl⟩ : syracuseStep 1972079 = 2958119) B2958119
theorem B3317071 : Blo 872567 3317071 := bstep (se 1 (by rfl) ⟨2487803, by rfl⟩ : syracuseStep 3317071 = 4975607) B4975607
theorem B13443353 : Blo 872567 13443353 := bstep (se 2 (by rfl) ⟨5041257, by rfl⟩ : syracuseStep 13443353 = 10082515) B10082515
theorem B4432967 : Blo 872567 4432967 := bstep (se 1 (by rfl) ⟨3324725, by rfl⟩ : syracuseStep 4432967 = 6649451) B6649451
theorem B11216393 : Blo 872567 11216393 := bstep (se 2 (by rfl) ⟨4206147, by rfl⟩ : syracuseStep 11216393 = 8412295) B8412295
theorem B4433615 : Blo 872567 4433615 := bstep (se 1 (by rfl) ⟨3325211, by rfl⟩ : syracuseStep 4433615 = 6650423) B6650423
theorem B21276503 : Blo 872567 21276503 := bstep (se 1 (by rfl) ⟨15957377, by rfl⟩ : syracuseStep 21276503 = 31914755) B31914755
theorem B4434425 : Blo 872567 4434425 := bstep (se 2 (by rfl) ⟨1662909, by rfl⟩ : syracuseStep 4434425 = 3325819) B3325819
theorem B6728351 : Blo 872567 6728351 := bstep (se 1 (by rfl) ⟨5046263, by rfl⟩ : syracuseStep 6728351 = 10092527) B10092527
theorem B5614271 : Blo 872567 5614271 := bstep (se 1 (by rfl) ⟨4210703, by rfl⟩ : syracuseStep 5614271 = 8421407) B8421407
theorem B4205783 : Blo 872567 4205783 := bstep (se 1 (by rfl) ⟨3154337, by rfl⟩ : syracuseStep 4205783 = 6308675) B6308675
theorem B6630983 : Blo 872567 6630983 := bstep (se 1 (by rfl) ⟨4973237, by rfl⟩ : syracuseStep 6630983 = 9946475) B9946475
theorem B13446847 : Blo 872567 13446847 := bstep (se 1 (by rfl) ⟨10085135, by rfl⟩ : syracuseStep 13446847 = 20170271) B20170271
theorem B3847009 : Blo 872567 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B3323207 : Blo 872567 3323207 := bstep (se 1 (by rfl) ⟨2492405, by rfl⟩ : syracuseStep 3323207 = 4984811) B4984811
theorem B7485281 : Blo 872567 7485281 := bstep (se 2 (by rfl) ⟨2806980, by rfl⟩ : syracuseStep 7485281 = 5613961) B5613961
theorem B2799805 : Blo 872567 2799805 := bstep (se 3 (by rfl) ⟨524963, by rfl⟩ : syracuseStep 2799805 = 1049927) B1049927
theorem B2243771 : Blo 872567 2243771 := bstep (se 1 (by rfl) ⟨1682828, by rfl⟩ : syracuseStep 2243771 = 3365657) B3365657
theorem B3325151 : Blo 872567 3325151 := bstep (se 1 (by rfl) ⟨2493863, by rfl⟩ : syracuseStep 3325151 = 4987727) B4987727
theorem B2211583 : Blo 872567 2211583 := bstep (se 1 (by rfl) ⟨1658687, by rfl⟩ : syracuseStep 2211583 = 3317375) B3317375
theorem B5324777 : Blo 872567 5324777 := bstep (se 2 (by rfl) ⟨1996791, by rfl⟩ : syracuseStep 5324777 = 3993583) B3993583
theorem B14598559 : Blo 872567 14598559 := bstep (se 1 (by rfl) ⟨10948919, by rfl⟩ : syracuseStep 14598559 = 21897839) B21897839
theorem B2212991 : Blo 872567 2212991 := bstep (se 1 (by rfl) ⟨1659743, by rfl⟩ : syracuseStep 2212991 = 3319487) B3319487
theorem B12764735 : Blo 872567 12764735 := bstep (se 1 (by rfl) ⟨9573551, by rfl⟩ : syracuseStep 12764735 = 19147103) B19147103
theorem B2246471 : Blo 872567 2246471 := bstep (se 1 (by rfl) ⟨1684853, by rfl⟩ : syracuseStep 2246471 = 3369707) B3369707
theorem B2214175 : Blo 872567 2214175 := bstep (se 1 (by rfl) ⟨1660631, by rfl⟩ : syracuseStep 2214175 = 3321263) B3321263
theorem B5327515 : Blo 872567 5327515 := bstep (se 1 (by rfl) ⟨3995636, by rfl⟩ : syracuseStep 5327515 = 7991273) B7991273
theorem B7097453 : Blo 872567 7097453 := bstep (se 3 (by rfl) ⟨1330772, by rfl⟩ : syracuseStep 7097453 = 2661545) B2661545
theorem B8409257 : Blo 872567 8409257 := bstep (se 2 (by rfl) ⟨3153471, by rfl⟩ : syracuseStep 8409257 = 6306943) B6306943
theorem B2216119 : Blo 872567 2216119 := bstep (se 1 (by rfl) ⟨1662089, by rfl⟩ : syracuseStep 2216119 = 3324179) B3324179
theorem B872935 : Blo 872567 872935 := bstep (se 1 (by rfl) ⟨654701, by rfl⟩ : syracuseStep 872935 = 1309403) B1309403
theorem B873151 : Blo 872567 873151 := bstep (se 1 (by rfl) ⟨654863, by rfl⟩ : syracuseStep 873151 = 1309727) B1309727
theorem B4379815 : Blo 872567 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B873727 : Blo 872567 873727 := bstep (se 1 (by rfl) ⟨655295, by rfl⟩ : syracuseStep 873727 = 1310591) B1310591
theorem B873799 : Blo 872567 873799 := bstep (se 1 (by rfl) ⟨655349, by rfl⟩ : syracuseStep 873799 = 1310699) B1310699
theorem B7558591 : Blo 872567 7558591 := bstep (se 1 (by rfl) ⟨5668943, by rfl⟩ : syracuseStep 7558591 = 11337887) B11337887
theorem B1660655 : Blo 872567 1660655 := bstep (se 1 (by rfl) ⟨1245491, by rfl⟩ : syracuseStep 1660655 = 2490983) B2490983
theorem B874343 : Blo 872567 874343 := bstep (se 1 (by rfl) ⟨655757, by rfl⟩ : syracuseStep 874343 = 1311515) B1311515
theorem B2217851 : Blo 872567 2217851 := bstep (se 1 (by rfl) ⟨1663388, by rfl⟩ : syracuseStep 2217851 = 3326777) B3326777
theorem B874431 : Blo 872567 874431 := bstep (se 1 (by rfl) ⟨655823, by rfl⟩ : syracuseStep 874431 = 1311647) B1311647
theorem B11229151 : Blo 872567 11229151 := bstep (se 1 (by rfl) ⟨8421863, by rfl⟩ : syracuseStep 11229151 = 16843727) B16843727
theorem B2218175 : Blo 872567 2218175 := bstep (se 1 (by rfl) ⟨1663631, by rfl⟩ : syracuseStep 2218175 = 3327263) B3327263
theorem B874703 : Blo 872567 874703 := bstep (se 1 (by rfl) ⟨656027, by rfl⟩ : syracuseStep 874703 = 1312055) B1312055
theorem B1661239 : Blo 872567 1661239 := bstep (se 1 (by rfl) ⟨1245929, by rfl⟩ : syracuseStep 1661239 = 2491859) B2491859
theorem B874943 : Blo 872567 874943 := bstep (se 1 (by rfl) ⟨656207, by rfl⟩ : syracuseStep 874943 = 1312415) B1312415
theorem B875163 : Blo 872567 875163 := bstep (se 1 (by rfl) ⟨656372, by rfl⟩ : syracuseStep 875163 = 1312745) B1312745
theorem B875175 : Blo 872567 875175 := bstep (se 1 (by rfl) ⟨656381, by rfl⟩ : syracuseStep 875175 = 1312763) B1312763
theorem B875295 : Blo 872567 875295 := bstep (se 1 (by rfl) ⟨656471, by rfl⟩ : syracuseStep 875295 = 1312943) B1312943
theorem B68017067 : Blo 872567 68017067 := bstep (se 1 (by rfl) ⟨51012800, by rfl⟩ : syracuseStep 68017067 = 102025601) B102025601
theorem B876063 : Blo 872567 876063 := bstep (se 1 (by rfl) ⟨657047, by rfl⟩ : syracuseStep 876063 = 1314095) B1314095
theorem B876079 : Blo 872567 876079 := bstep (se 1 (by rfl) ⟨657059, by rfl⟩ : syracuseStep 876079 = 1314119) B1314119
theorem B876135 : Blo 872567 876135 := bstep (se 1 (by rfl) ⟨657101, by rfl⟩ : syracuseStep 876135 = 1314203) B1314203
theorem B876283 : Blo 872567 876283 := bstep (se 1 (by rfl) ⟨657212, by rfl⟩ : syracuseStep 876283 = 1314425) B1314425
theorem B876391 : Blo 872567 876391 := bstep (se 1 (by rfl) ⟨657293, by rfl⟩ : syracuseStep 876391 = 1314587) B1314587
theorem B51175709 : Blo 872567 51175709 := bstep (se 3 (by rfl) ⟨9595445, by rfl⟩ : syracuseStep 51175709 = 19190891) B19190891
theorem B4252097 : Blo 872567 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B68084651 : Blo 872567 68084651 := bstep (se 1 (by rfl) ⟨51063488, by rfl⟩ : syracuseStep 68084651 = 102126977) B102126977
theorem B28370857 : Blo 872567 28370857 := bstep (se 2 (by rfl) ⟨10639071, by rfl⟩ : syracuseStep 28370857 = 21278143) B21278143
theorem B4417577 : Blo 872567 4417577 := bstep (se 2 (by rfl) ⟨1656591, by rfl⟩ : syracuseStep 4417577 = 3313183) B3313183
theorem B4417739 : Blo 872567 4417739 := bstep (se 1 (by rfl) ⟨3313304, by rfl⟩ : syracuseStep 4417739 = 6626609) B6626609
theorem B15953071 : Blo 872567 15953071 := bstep (se 1 (by rfl) ⟨11964803, by rfl⟩ : syracuseStep 15953071 = 23929607) B23929607
theorem B15133949 : Blo 872567 15133949 := bstep (se 3 (by rfl) ⟨2837615, by rfl⟩ : syracuseStep 15133949 = 5675231) B5675231
theorem B4419359 : Blo 872567 4419359 := bstep (se 1 (by rfl) ⟨3314519, by rfl⟩ : syracuseStep 4419359 = 6629039) B6629039
theorem B2945591 : Blo 872567 2945591 := bstep (se 1 (by rfl) ⟨2209193, by rfl⟩ : syracuseStep 2945591 = 4418387) B4418387
theorem B4257305 : Blo 872567 4257305 := bstep (se 2 (by rfl) ⟨1596489, by rfl⟩ : syracuseStep 4257305 = 3192979) B3192979
theorem B1963547 : Blo 872567 1963547 := bstep (se 1 (by rfl) ⟨1472660, by rfl⟩ : syracuseStep 1963547 = 2945321) B2945321
theorem B6059897 : Blo 872567 6059897 := bstep (se 2 (by rfl) ⟨2272461, by rfl⟩ : syracuseStep 6059897 = 4544923) B4544923
theorem B2947049 : Blo 872567 2947049 := bstep (se 2 (by rfl) ⟨1105143, by rfl⟩ : syracuseStep 2947049 = 2210287) B2210287
theorem B12581081 : Blo 872567 12581081 := bstep (se 2 (by rfl) ⟨4717905, by rfl⟩ : syracuseStep 12581081 = 9435811) B9435811
theorem B1309007 : Blo 872567 1309007 := bstep (se 1 (by rfl) ⟨981755, by rfl⟩ : syracuseStep 1309007 = 1963511) B1963511
theorem B1309055 : Blo 872567 1309055 := bstep (se 1 (by rfl) ⟨981791, by rfl⟩ : syracuseStep 1309055 = 1963583) B1963583
theorem B1964807 : Blo 872567 1964807 := bstep (se 1 (by rfl) ⟨1473605, by rfl⟩ : syracuseStep 1964807 = 2947211) B2947211
theorem B1309679 : Blo 872567 1309679 := bstep (se 1 (by rfl) ⟨982259, by rfl⟩ : syracuseStep 1309679 = 1964519) B1964519
theorem B1309691 : Blo 872567 1309691 := bstep (se 1 (by rfl) ⟨982268, by rfl⟩ : syracuseStep 1309691 = 1964537) B1964537
theorem B982183 : Blo 872567 982183 := bstep (se 1 (by rfl) ⟨736637, by rfl⟩ : syracuseStep 982183 = 1473275) B1473275
theorem B1310111 : Blo 872567 1310111 := bstep (se 1 (by rfl) ⟨982583, by rfl⟩ : syracuseStep 1310111 = 1965167) B1965167
theorem B1310459 : Blo 872567 1310459 := bstep (se 1 (by rfl) ⟨982844, by rfl⟩ : syracuseStep 1310459 = 1965689) B1965689
theorem B3735533 : Blo 872567 3735533 := bstep (se 3 (by rfl) ⟨700412, by rfl⟩ : syracuseStep 3735533 = 1400825) B1400825
theorem B1310783 : Blo 872567 1310783 := bstep (se 1 (by rfl) ⟨983087, by rfl⟩ : syracuseStep 1310783 = 1966175) B1966175
theorem B1310831 : Blo 872567 1310831 := bstep (se 1 (by rfl) ⟨983123, by rfl⟩ : syracuseStep 1310831 = 1966247) B1966247
theorem B1966355 : Blo 872567 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B3735875 : Blo 872567 3735875 := bstep (se 1 (by rfl) ⟨2801906, by rfl⟩ : syracuseStep 3735875 = 5603813) B5603813
theorem B1311215 : Blo 872567 1311215 := bstep (se 1 (by rfl) ⟨983411, by rfl⟩ : syracuseStep 1311215 = 1966823) B1966823
theorem B19464745 : Blo 872567 19464745 := bstep (se 2 (by rfl) ⟨7299279, by rfl⟩ : syracuseStep 19464745 = 14598559) B14598559
theorem B1311359 : Blo 872567 1311359 := bstep (se 1 (by rfl) ⟨983519, by rfl⟩ : syracuseStep 1311359 = 1967039) B1967039
theorem B1475327 : Blo 872567 1475327 := bstep (se 1 (by rfl) ⟨1106495, by rfl⟩ : syracuseStep 1475327 = 2212991) B2212991
theorem B3736763 : Blo 872567 3736763 := bstep (se 1 (by rfl) ⟨2802572, by rfl⟩ : syracuseStep 3736763 = 5605145) B5605145
theorem B1312235 : Blo 872567 1312235 := bstep (se 1 (by rfl) ⟨984176, by rfl⟩ : syracuseStep 1312235 = 1968353) B1968353
theorem B1312895 : Blo 872567 1312895 := bstep (se 1 (by rfl) ⟨984671, by rfl⟩ : syracuseStep 1312895 = 1969343) B1969343
theorem B1313435 : Blo 872567 1313435 := bstep (se 1 (by rfl) ⟨985076, by rfl⟩ : syracuseStep 1313435 = 1970153) B1970153
theorem B5606171 : Blo 872567 5606171 := bstep (se 1 (by rfl) ⟨4204628, by rfl⟩ : syracuseStep 5606171 = 8409257) B8409257
theorem B1313819 : Blo 872567 1313819 := bstep (se 1 (by rfl) ⟨985364, by rfl⟩ : syracuseStep 1313819 = 1970729) B1970729
theorem B2952233 : Blo 872567 2952233 := bstep (se 2 (by rfl) ⟨1107087, by rfl⟩ : syracuseStep 2952233 = 2214175) B2214175
theorem B1313999 : Blo 872567 1313999 := bstep (se 1 (by rfl) ⟨985499, by rfl⟩ : syracuseStep 1313999 = 1970999) B1970999
theorem B28413413 : Blo 872567 28413413 := bstep (se 4 (by rfl) ⟨2663757, by rfl⟩ : syracuseStep 28413413 = 5327515) B5327515
theorem B1314671 : Blo 872567 1314671 := bstep (se 1 (by rfl) ⟨986003, by rfl⟩ : syracuseStep 1314671 = 1972007) B1972007
theorem B1314719 : Blo 872567 1314719 := bstep (se 1 (by rfl) ⟨986039, by rfl⟩ : syracuseStep 1314719 = 1972079) B1972079
theorem B1478567 : Blo 872567 1478567 := bstep (se 1 (by rfl) ⟨1108925, by rfl⟩ : syracuseStep 1478567 = 2217851) B2217851
theorem B1478783 : Blo 872567 1478783 := bstep (se 1 (by rfl) ⟨1109087, by rfl⟩ : syracuseStep 1478783 = 2218175) B2218175
theorem B21270761 : Blo 872567 21270761 := bstep (se 2 (by rfl) ⟨7976535, by rfl⟩ : syracuseStep 21270761 = 15953071) B15953071
theorem B17929129 : Blo 872567 17929129 := bstep (se 2 (by rfl) ⟨6723423, by rfl⟩ : syracuseStep 17929129 = 13446847) B13446847
theorem B10622441 : Blo 872567 10622441 := bstep (se 2 (by rfl) ⟨3983415, by rfl⟩ : syracuseStep 10622441 = 7966831) B7966831
theorem B34117139 : Blo 872567 34117139 := bstep (se 1 (by rfl) ⟨25587854, by rfl⟩ : syracuseStep 34117139 = 51175709) B51175709
theorem B2954825 : Blo 872567 2954825 := bstep (se 2 (by rfl) ⟨1108059, by rfl⟩ : syracuseStep 2954825 = 2216119) B2216119
theorem B2955311 : Blo 872567 2955311 := bstep (se 1 (by rfl) ⟨2216483, by rfl⟩ : syracuseStep 2955311 = 4432967) B4432967
theorem B7477595 : Blo 872567 7477595 := bstep (se 1 (by rfl) ⟨5608196, by rfl⟩ : syracuseStep 7477595 = 11216393) B11216393
theorem B2955743 : Blo 872567 2955743 := bstep (se 1 (by rfl) ⟨2216807, by rfl⟩ : syracuseStep 2955743 = 4433615) B4433615
theorem B2956283 : Blo 872567 2956283 := bstep (se 1 (by rfl) ⟨2217212, by rfl⟩ : syracuseStep 2956283 = 4434425) B4434425
theorem B3742847 : Blo 872567 3742847 := bstep (se 1 (by rfl) ⟨2807135, by rfl⟩ : syracuseStep 3742847 = 5614271) B5614271
theorem B4990187 : Blo 872567 4990187 := bstep (se 1 (by rfl) ⟨3742640, by rfl⟩ : syracuseStep 4990187 = 7485281) B7485281
theorem B4039931 : Blo 872567 4039931 := bstep (se 1 (by rfl) ⟨3029948, by rfl⟩ : syracuseStep 4039931 = 6059897) B6059897
theorem B3549851 : Blo 872567 3549851 := bstep (se 1 (by rfl) ⟨2662388, by rfl⟩ : syracuseStep 3549851 = 5324777) B5324777
theorem B7973615 : Blo 872567 7973615 := bstep (se 1 (by rfl) ⟨5980211, by rfl⟩ : syracuseStep 7973615 = 11960423) B11960423
theorem B4435559 : Blo 872567 4435559 := bstep (se 1 (by rfl) ⟨3326669, by rfl⟩ : syracuseStep 4435559 = 6653339) B6653339
theorem B3322235 : Blo 872567 3322235 := bstep (se 1 (by rfl) ⟨2491676, by rfl⟩ : syracuseStep 3322235 = 4983353) B4983353
theorem B4731635 : Blo 872567 4731635 := bstep (se 1 (by rfl) ⟨3548726, by rfl⟩ : syracuseStep 4731635 = 7097453) B7097453
theorem B37827809 : Blo 872567 37827809 := bstep (se 2 (by rfl) ⟨14185428, by rfl⟩ : syracuseStep 37827809 = 28370857) B28370857
theorem B21280481 : Blo 872567 21280481 := bstep (se 2 (by rfl) ⟨7980180, by rfl⟩ : syracuseStep 21280481 = 15960361) B15960361
theorem B2210075 : Blo 872567 2210075 := bstep (se 1 (by rfl) ⟨1657556, by rfl⟩ : syracuseStep 2210075 = 3315113) B3315113
theorem B8962235 : Blo 872567 8962235 := bstep (se 1 (by rfl) ⟨6721676, by rfl⟩ : syracuseStep 8962235 = 13443353) B13443353
theorem B2834731 : Blo 872567 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B11191121 : Blo 872567 11191121 := bstep (se 2 (by rfl) ⟨4196670, by rfl⟩ : syracuseStep 11191121 = 8393341) B8393341
theorem B5129345 : Blo 872567 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B17942269 : Blo 872567 17942269 := bstep (se 3 (by rfl) ⟨3364175, by rfl⟩ : syracuseStep 17942269 = 6728351) B6728351
theorem B10078121 : Blo 872567 10078121 := bstep (se 2 (by rfl) ⟨3779295, by rfl⟩ : syracuseStep 10078121 = 7558591) B7558591
theorem B2803855 : Blo 872567 2803855 := bstep (se 1 (by rfl) ⟨2102891, by rfl⟩ : syracuseStep 2803855 = 4205783) B4205783
theorem B2214985 : Blo 872567 2214985 := bstep (se 2 (by rfl) ⟨830619, by rfl⟩ : syracuseStep 2214985 = 1661239) B1661239
theorem B2215471 : Blo 872567 2215471 := bstep (se 1 (by rfl) ⟨1661603, by rfl⟩ : syracuseStep 2215471 = 3323207) B3323207
theorem B2838203 : Blo 872567 2838203 := bstep (se 1 (by rfl) ⟨2128652, by rfl⟩ : syracuseStep 2838203 = 4257305) B4257305
theorem B872671 : Blo 872567 872671 := bstep (se 1 (by rfl) ⟨654503, by rfl⟩ : syracuseStep 872671 = 1309007) B1309007
theorem B872703 : Blo 872567 872703 := bstep (se 1 (by rfl) ⟨654527, by rfl⟩ : syracuseStep 872703 = 1309055) B1309055
theorem B873119 : Blo 872567 873119 := bstep (se 1 (by rfl) ⟨654839, by rfl⟩ : syracuseStep 873119 = 1309679) B1309679
theorem B873127 : Blo 872567 873127 := bstep (se 1 (by rfl) ⟨654845, by rfl⟩ : syracuseStep 873127 = 1309691) B1309691
theorem B1495847 : Blo 872567 1495847 := bstep (se 1 (by rfl) ⟨1121885, by rfl⟩ : syracuseStep 1495847 = 2243771) B2243771
theorem B2216767 : Blo 872567 2216767 := bstep (se 1 (by rfl) ⟨1662575, by rfl⟩ : syracuseStep 2216767 = 3325151) B3325151
theorem B873407 : Blo 872567 873407 := bstep (se 1 (by rfl) ⟨655055, by rfl⟩ : syracuseStep 873407 = 1310111) B1310111
theorem B873639 : Blo 872567 873639 := bstep (se 1 (by rfl) ⟨655229, by rfl⟩ : syracuseStep 873639 = 1310459) B1310459
theorem B873919 : Blo 872567 873919 := bstep (se 1 (by rfl) ⟨655439, by rfl⟩ : syracuseStep 873919 = 1310879) B1310879
theorem B874407 : Blo 872567 874407 := bstep (se 1 (by rfl) ⟨655805, by rfl⟩ : syracuseStep 874407 = 1311611) B1311611
theorem B874491 : Blo 872567 874491 := bstep (se 1 (by rfl) ⟨655868, by rfl⟩ : syracuseStep 874491 = 1311737) B1311737
theorem B8509823 : Blo 872567 8509823 := bstep (se 1 (by rfl) ⟨6382367, by rfl⟩ : syracuseStep 8509823 = 12764735) B12764735
theorem B1497647 : Blo 872567 1497647 := bstep (se 1 (by rfl) ⟨1123235, by rfl⟩ : syracuseStep 1497647 = 2246471) B2246471
theorem B875259 : Blo 872567 875259 := bstep (se 1 (by rfl) ⟨656444, by rfl⟩ : syracuseStep 875259 = 1312889) B1312889
theorem B875455 : Blo 872567 875455 := bstep (se 1 (by rfl) ⟨656591, by rfl⟩ : syracuseStep 875455 = 1313183) B1313183
theorem B1662059 : Blo 872567 1662059 := bstep (se 1 (by rfl) ⟨1246544, by rfl⟩ : syracuseStep 1662059 = 2493089) B2493089
theorem B876223 : Blo 872567 876223 := bstep (se 1 (by rfl) ⟨657167, by rfl⟩ : syracuseStep 876223 = 1314335) B1314335
theorem B181559069 : Blo 872567 181559069 := bstep (se 3 (by rfl) ⟨34042325, by rfl⟩ : syracuseStep 181559069 = 68084651) B68084651
theorem B1107103 : Blo 872567 1107103 := bstep (se 1 (by rfl) ⟨830327, by rfl⟩ : syracuseStep 1107103 = 1660655) B1660655
theorem B45344711 : Blo 872567 45344711 := bstep (se 1 (by rfl) ⟨34008533, by rfl⟩ : syracuseStep 45344711 = 68017067) B68017067
theorem B23359013 : Blo 872567 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B14184335 : Blo 872567 14184335 := bstep (se 1 (by rfl) ⟨10638251, by rfl⟩ : syracuseStep 14184335 = 21276503) B21276503
theorem B2945051 : Blo 872567 2945051 := bstep (se 1 (by rfl) ⟨2208788, by rfl⟩ : syracuseStep 2945051 = 4417577) B4417577
theorem B2945159 : Blo 872567 2945159 := bstep (se 1 (by rfl) ⟨2208869, by rfl⟩ : syracuseStep 2945159 = 4417739) B4417739
theorem B10089299 : Blo 872567 10089299 := bstep (se 1 (by rfl) ⟨7566974, by rfl⟩ : syracuseStep 10089299 = 15133949) B15133949
theorem B4420655 : Blo 872567 4420655 := bstep (se 1 (by rfl) ⟨3315491, by rfl⟩ : syracuseStep 4420655 = 6630983) B6630983
theorem B2946239 : Blo 872567 2946239 := bstep (se 1 (by rfl) ⟨2209679, by rfl⟩ : syracuseStep 2946239 = 4419359) B4419359
theorem B14972201 : Blo 872567 14972201 := bstep (se 2 (by rfl) ⟨5614575, by rfl⟩ : syracuseStep 14972201 = 11229151) B11229151
theorem B3733073 : Blo 872567 3733073 := bstep (se 2 (by rfl) ⟨1399902, by rfl⟩ : syracuseStep 3733073 = 2799805) B2799805
theorem B1963727 : Blo 872567 1963727 := bstep (se 1 (by rfl) ⟨1472795, by rfl⟩ : syracuseStep 1963727 = 2945591) B2945591
theorem B5601149 : Blo 872567 5601149 := bstep (se 3 (by rfl) ⟨1050215, by rfl⟩ : syracuseStep 5601149 = 2100431) B2100431
theorem B1309031 : Blo 872567 1309031 := bstep (se 1 (by rfl) ⟨981773, by rfl⟩ : syracuseStep 1309031 = 1963547) B1963547
theorem B1964699 : Blo 872567 1964699 := bstep (se 1 (by rfl) ⟨1473524, by rfl⟩ : syracuseStep 1964699 = 2947049) B2947049
theorem B8387387 : Blo 872567 8387387 := bstep (se 1 (by rfl) ⟨6290540, by rfl⟩ : syracuseStep 8387387 = 12581081) B12581081
theorem B1309577 : Blo 872567 1309577 := bstep (se 2 (by rfl) ⟨491091, by rfl⟩ : syracuseStep 1309577 = 982183) B982183
theorem B4422761 : Blo 872567 4422761 := bstep (se 2 (by rfl) ⟨1658535, by rfl⟩ : syracuseStep 4422761 = 3317071) B3317071
theorem B1309871 : Blo 872567 1309871 := bstep (se 1 (by rfl) ⟨982403, by rfl⟩ : syracuseStep 1309871 = 1964807) B1964807
theorem B2948777 : Blo 872567 2948777 := bstep (se 2 (by rfl) ⟨1105791, by rfl⟩ : syracuseStep 2948777 = 2211583) B2211583
theorem B2490355 : Blo 872567 2490355 := bstep (se 1 (by rfl) ⟨1867766, by rfl⟩ : syracuseStep 2490355 = 3735533) B3735533
theorem B1310903 : Blo 872567 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B2490583 : Blo 872567 2490583 := bstep (se 1 (by rfl) ⟨1867937, by rfl⟩ : syracuseStep 2490583 = 3735875) B3735875
theorem B983551 : Blo 872567 983551 := bstep (se 1 (by rfl) ⟨737663, by rfl⟩ : syracuseStep 983551 = 1475327) B1475327
theorem B25952993 : Blo 872567 25952993 := bstep (se 2 (by rfl) ⟨9732372, by rfl⟩ : syracuseStep 25952993 = 19464745) B19464745
theorem B2491175 : Blo 872567 2491175 := bstep (se 1 (by rfl) ⟨1868381, by rfl⟩ : syracuseStep 2491175 = 3736763) B3736763
theorem B6718747 : Blo 872567 6718747 := bstep (se 1 (by rfl) ⟨5039060, by rfl⟩ : syracuseStep 6718747 = 10078121) B10078121
theorem B1476137 : Blo 872567 1476137 := bstep (se 2 (by rfl) ⟨553551, by rfl⟩ : syracuseStep 1476137 = 1107103) B1107103
theorem B3737447 : Blo 872567 3737447 := bstep (se 1 (by rfl) ⟨2803085, by rfl⟩ : syracuseStep 3737447 = 5606171) B5606171
theorem B12617693 : Blo 872567 12617693 := bstep (se 3 (by rfl) ⟨2365817, by rfl⟩ : syracuseStep 12617693 = 4731635) B4731635
theorem B1968155 : Blo 872567 1968155 := bstep (se 1 (by rfl) ⟨1476116, by rfl⟩ : syracuseStep 1968155 = 2952233) B2952233
theorem B18942275 : Blo 872567 18942275 := bstep (se 1 (by rfl) ⟨14206706, by rfl⟩ : syracuseStep 18942275 = 28413413) B28413413
theorem B23923025 : Blo 872567 23923025 := bstep (se 2 (by rfl) ⟨8971134, by rfl⟩ : syracuseStep 23923025 = 17942269) B17942269
theorem B985711 : Blo 872567 985711 := bstep (se 1 (by rfl) ⟨739283, by rfl⟩ : syracuseStep 985711 = 1478567) B1478567
theorem B985855 : Blo 872567 985855 := bstep (se 1 (by rfl) ⟨739391, by rfl⟩ : syracuseStep 985855 = 1478783) B1478783
theorem B3738473 : Blo 872567 3738473 := bstep (se 2 (by rfl) ⟨1401927, by rfl⟩ : syracuseStep 3738473 = 2803855) B2803855
theorem B7081627 : Blo 872567 7081627 := bstep (se 1 (by rfl) ⟨5311220, by rfl⟩ : syracuseStep 7081627 = 10622441) B10622441
theorem B22744759 : Blo 872567 22744759 := bstep (se 1 (by rfl) ⟨17058569, by rfl⟩ : syracuseStep 22744759 = 34117139) B34117139
theorem B1969883 : Blo 872567 1969883 := bstep (se 1 (by rfl) ⟨1477412, by rfl⟩ : syracuseStep 1969883 = 2954825) B2954825
theorem B1970207 : Blo 872567 1970207 := bstep (se 1 (by rfl) ⟨1477655, by rfl⟩ : syracuseStep 1970207 = 2955311) B2955311
theorem B2953313 : Blo 872567 2953313 := bstep (se 2 (by rfl) ⟨1107492, by rfl⟩ : syracuseStep 2953313 = 2214985) B2214985
theorem B4985063 : Blo 872567 4985063 := bstep (se 1 (by rfl) ⟨3738797, by rfl⟩ : syracuseStep 4985063 = 7477595) B7477595
theorem B5673215 : Blo 872567 5673215 := bstep (se 1 (by rfl) ⟨4254911, by rfl⟩ : syracuseStep 5673215 = 8509823) B8509823
theorem B1970495 : Blo 872567 1970495 := bstep (se 1 (by rfl) ⟨1477871, by rfl⟩ : syracuseStep 1970495 = 2955743) B2955743
theorem B1970855 : Blo 872567 1970855 := bstep (se 1 (by rfl) ⟨1478141, by rfl⟩ : syracuseStep 1970855 = 2956283) B2956283
theorem B2953961 : Blo 872567 2953961 := bstep (se 2 (by rfl) ⟨1107735, by rfl⟩ : syracuseStep 2953961 = 2215471) B2215471
theorem B2495231 : Blo 872567 2495231 := bstep (se 1 (by rfl) ⟨1871423, by rfl⟩ : syracuseStep 2495231 = 3742847) B3742847
theorem B2693287 : Blo 872567 2693287 := bstep (se 1 (by rfl) ⟨2019965, by rfl⟩ : syracuseStep 2693287 = 4039931) B4039931
theorem B2955689 : Blo 872567 2955689 := bstep (se 2 (by rfl) ⟨1108383, by rfl⟩ : syracuseStep 2955689 = 2216767) B2216767
theorem B2366567 : Blo 872567 2366567 := bstep (se 1 (by rfl) ⟨1774925, by rfl⟩ : syracuseStep 2366567 = 3549851) B3549851
theorem B5315743 : Blo 872567 5315743 := bstep (se 1 (by rfl) ⟨3986807, by rfl⟩ : syracuseStep 5315743 = 7973615) B7973615
theorem B15572675 : Blo 872567 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B2957039 : Blo 872567 2957039 := bstep (se 1 (by rfl) ⟨2217779, by rfl⟩ : syracuseStep 2957039 = 4435559) B4435559
theorem B4432157 : Blo 872567 4432157 := bstep (se 3 (by rfl) ⟨831029, by rfl⟩ : syracuseStep 4432157 = 1662059) B1662059
theorem B6726199 : Blo 872567 6726199 := bstep (se 1 (by rfl) ⟨5044649, by rfl⟩ : syracuseStep 6726199 = 10089299) B10089299
theorem B3320473 : Blo 872567 3320473 := bstep (se 2 (by rfl) ⟨1245177, by rfl⟩ : syracuseStep 3320473 = 2490355) B2490355
theorem B5974823 : Blo 872567 5974823 := bstep (se 1 (by rfl) ⟨4481117, by rfl⟩ : syracuseStep 5974823 = 8962235) B8962235
theorem B3779641 : Blo 872567 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B3419563 : Blo 872567 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B997231 : Blo 872567 997231 := bstep (se 1 (by rfl) ⟨747923, by rfl⟩ : syracuseStep 997231 = 1495847) B1495847
theorem B3326791 : Blo 872567 3326791 := bstep (se 1 (by rfl) ⟨2495093, by rfl⟩ : syracuseStep 3326791 = 4990187) B4990187
theorem B23905505 : Blo 872567 23905505 := bstep (se 2 (by rfl) ⟨8964564, by rfl⟩ : syracuseStep 23905505 = 17929129) B17929129
theorem B30229807 : Blo 872567 30229807 := bstep (se 1 (by rfl) ⟨22672355, by rfl⟩ : syracuseStep 30229807 = 45344711) B45344711
theorem B9456223 : Blo 872567 9456223 := bstep (se 1 (by rfl) ⟨7092167, by rfl⟩ : syracuseStep 9456223 = 14184335) B14184335
theorem B2214823 : Blo 872567 2214823 := bstep (se 1 (by rfl) ⟨1661117, by rfl⟩ : syracuseStep 2214823 = 3322235) B3322235
theorem B25218539 : Blo 872567 25218539 := bstep (se 1 (by rfl) ⟨18913904, by rfl⟩ : syracuseStep 25218539 = 37827809) B37827809
theorem B9981467 : Blo 872567 9981467 := bstep (se 1 (by rfl) ⟨7486100, by rfl⟩ : syracuseStep 9981467 = 14972201) B14972201
theorem B872687 : Blo 872567 872687 := bstep (se 1 (by rfl) ⟨654515, by rfl⟩ : syracuseStep 872687 = 1309031) B1309031
theorem B5591591 : Blo 872567 5591591 := bstep (se 1 (by rfl) ⟨4193693, by rfl⟩ : syracuseStep 5591591 = 8387387) B8387387
theorem B873051 : Blo 872567 873051 := bstep (se 1 (by rfl) ⟨654788, by rfl⟩ : syracuseStep 873051 = 1309577) B1309577
theorem B873247 : Blo 872567 873247 := bstep (se 1 (by rfl) ⟨654935, by rfl⟩ : syracuseStep 873247 = 1309871) B1309871
theorem B873855 : Blo 872567 873855 := bstep (se 1 (by rfl) ⟨655391, by rfl⟩ : syracuseStep 873855 = 1310783) B1310783
theorem B873887 : Blo 872567 873887 := bstep (se 1 (by rfl) ⟨655415, by rfl⟩ : syracuseStep 873887 = 1310831) B1310831
theorem B874143 : Blo 872567 874143 := bstep (se 1 (by rfl) ⟨655607, by rfl⟩ : syracuseStep 874143 = 1311215) B1311215
theorem B874239 : Blo 872567 874239 := bstep (se 1 (by rfl) ⟨655679, by rfl⟩ : syracuseStep 874239 = 1311359) B1311359
theorem B7460747 : Blo 872567 7460747 := bstep (se 1 (by rfl) ⟨5595560, by rfl⟩ : syracuseStep 7460747 = 11191121) B11191121
theorem B874823 : Blo 872567 874823 := bstep (se 1 (by rfl) ⟨656117, by rfl⟩ : syracuseStep 874823 = 1312235) B1312235
theorem B875263 : Blo 872567 875263 := bstep (se 1 (by rfl) ⟨656447, by rfl⟩ : syracuseStep 875263 = 1312895) B1312895
theorem B875623 : Blo 872567 875623 := bstep (se 1 (by rfl) ⟨656717, by rfl⟩ : syracuseStep 875623 = 1313435) B1313435
theorem B875879 : Blo 872567 875879 := bstep (se 1 (by rfl) ⟨656909, by rfl⟩ : syracuseStep 875879 = 1313819) B1313819
theorem B875999 : Blo 872567 875999 := bstep (se 1 (by rfl) ⟨656999, by rfl⟩ : syracuseStep 875999 = 1313999) B1313999
theorem B1892135 : Blo 872567 1892135 := bstep (se 1 (by rfl) ⟨1419101, by rfl⟩ : syracuseStep 1892135 = 2838203) B2838203
theorem B876447 : Blo 872567 876447 := bstep (se 1 (by rfl) ⟨657335, by rfl⟩ : syracuseStep 876447 = 1314671) B1314671
theorem B876479 : Blo 872567 876479 := bstep (se 1 (by rfl) ⟨657359, by rfl⟩ : syracuseStep 876479 = 1314719) B1314719
theorem B14180507 : Blo 872567 14180507 := bstep (se 1 (by rfl) ⟨10635380, by rfl⟩ : syracuseStep 14180507 = 21270761) B21270761
theorem B121039379 : Blo 872567 121039379 := bstep (se 1 (by rfl) ⟨90779534, by rfl⟩ : syracuseStep 121039379 = 181559069) B181559069
theorem B3993725 : Blo 872567 3993725 := bstep (se 3 (by rfl) ⟨748823, by rfl⟩ : syracuseStep 3993725 = 1497647) B1497647
theorem B1963367 : Blo 872567 1963367 := bstep (se 1 (by rfl) ⟨1472525, by rfl⟩ : syracuseStep 1963367 = 2945051) B2945051
theorem B1963439 : Blo 872567 1963439 := bstep (se 1 (by rfl) ⟨1472579, by rfl⟩ : syracuseStep 1963439 = 2945159) B2945159
theorem B2947103 : Blo 872567 2947103 := bstep (se 1 (by rfl) ⟨2210327, by rfl⟩ : syracuseStep 2947103 = 4420655) B4420655
theorem B1964159 : Blo 872567 1964159 := bstep (se 1 (by rfl) ⟨1473119, by rfl⟩ : syracuseStep 1964159 = 2946239) B2946239
theorem B2488715 : Blo 872567 2488715 := bstep (se 1 (by rfl) ⟨1866536, by rfl⟩ : syracuseStep 2488715 = 3733073) B3733073
theorem B1309151 : Blo 872567 1309151 := bstep (se 1 (by rfl) ⟨981863, by rfl⟩ : syracuseStep 1309151 = 1963727) B1963727
theorem B14186987 : Blo 872567 14186987 := bstep (se 1 (by rfl) ⟨10640240, by rfl⟩ : syracuseStep 14186987 = 21280481) B21280481
theorem B3734099 : Blo 872567 3734099 := bstep (se 1 (by rfl) ⟨2800574, by rfl⟩ : syracuseStep 3734099 = 5601149) B5601149
theorem B1473383 : Blo 872567 1473383 := bstep (se 1 (by rfl) ⟨1105037, by rfl⟩ : syracuseStep 1473383 = 2210075) B2210075
theorem B1309799 : Blo 872567 1309799 := bstep (se 1 (by rfl) ⟨982349, by rfl⟩ : syracuseStep 1309799 = 1964699) B1964699
theorem B2948507 : Blo 872567 2948507 := bstep (se 1 (by rfl) ⟨2211380, by rfl⟩ : syracuseStep 2948507 = 4422761) B4422761
theorem B1965851 : Blo 872567 1965851 := bstep (se 1 (by rfl) ⟨1474388, by rfl⟩ : syracuseStep 1965851 = 2948777) B2948777
theorem B17301995 : Blo 872567 17301995 := bstep (se 1 (by rfl) ⟨12976496, by rfl⟩ : syracuseStep 17301995 = 25952993) B25952993
theorem B1311401 : Blo 872567 1311401 := bstep (se 2 (by rfl) ⟨491775, by rfl⟩ : syracuseStep 1311401 = 983551) B983551
theorem B984091 : Blo 872567 984091 := bstep (se 1 (by rfl) ⟨738068, by rfl⟩ : syracuseStep 984091 = 1476137) B1476137
theorem B2491631 : Blo 872567 2491631 := bstep (se 1 (by rfl) ⟨1868723, by rfl⟩ : syracuseStep 2491631 = 3737447) B3737447
theorem B1312103 : Blo 872567 1312103 := bstep (se 1 (by rfl) ⟨984077, by rfl⟩ : syracuseStep 1312103 = 1968155) B1968155
theorem B40306409 : Blo 872567 40306409 := bstep (se 2 (by rfl) ⟨15114903, by rfl⟩ : syracuseStep 40306409 = 30229807) B30229807
theorem B2492315 : Blo 872567 2492315 := bstep (se 1 (by rfl) ⟨1869236, by rfl⟩ : syracuseStep 2492315 = 3738473) B3738473
theorem B16812359 : Blo 872567 16812359 := bstep (se 1 (by rfl) ⟨12609269, by rfl⟩ : syracuseStep 16812359 = 25218539) B25218539
theorem B6654311 : Blo 872567 6654311 := bstep (se 1 (by rfl) ⟨4990733, by rfl⟩ : syracuseStep 6654311 = 9981467) B9981467
theorem B1313255 : Blo 872567 1313255 := bstep (se 1 (by rfl) ⟨984941, by rfl⟩ : syracuseStep 1313255 = 1969883) B1969883
theorem B1313471 : Blo 872567 1313471 := bstep (se 1 (by rfl) ⟨985103, by rfl⟩ : syracuseStep 1313471 = 1970207) B1970207
theorem B1968875 : Blo 872567 1968875 := bstep (se 1 (by rfl) ⟨1476656, by rfl⟩ : syracuseStep 1968875 = 2953313) B2953313
theorem B1313663 : Blo 872567 1313663 := bstep (se 1 (by rfl) ⟨985247, by rfl⟩ : syracuseStep 1313663 = 1970495) B1970495
theorem B1313903 : Blo 872567 1313903 := bstep (se 1 (by rfl) ⟨985427, by rfl⟩ : syracuseStep 1313903 = 1970855) B1970855
theorem B1969307 : Blo 872567 1969307 := bstep (se 1 (by rfl) ⟨1476980, by rfl⟩ : syracuseStep 1969307 = 2953961) B2953961
theorem B1314281 : Blo 872567 1314281 := bstep (se 2 (by rfl) ⟨492855, by rfl⟩ : syracuseStep 1314281 = 985711) B985711
theorem B4427297 : Blo 872567 4427297 := bstep (se 2 (by rfl) ⟨1660236, by rfl⟩ : syracuseStep 4427297 = 3320473) B3320473
theorem B1314473 : Blo 872567 1314473 := bstep (se 2 (by rfl) ⟨492927, by rfl⟩ : syracuseStep 1314473 = 985855) B985855
theorem B2953097 : Blo 872567 2953097 := bstep (se 2 (by rfl) ⟨1107411, by rfl⟩ : syracuseStep 2953097 = 2214823) B2214823
theorem B1970459 : Blo 872567 1970459 := bstep (se 1 (by rfl) ⟨1477844, by rfl⟩ : syracuseStep 1970459 = 2955689) B2955689
theorem B4559417 : Blo 872567 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B1577711 : Blo 872567 1577711 := bstep (se 1 (by rfl) ⟨1183283, by rfl⟩ : syracuseStep 1577711 = 2366567) B2366567
theorem B9442169 : Blo 872567 9442169 := bstep (se 2 (by rfl) ⟨3540813, by rfl⟩ : syracuseStep 9442169 = 7081627) B7081627
theorem B1971359 : Blo 872567 1971359 := bstep (se 1 (by rfl) ⟨1478519, by rfl⟩ : syracuseStep 1971359 = 2957039) B2957039
theorem B2954771 : Blo 872567 2954771 := bstep (se 1 (by rfl) ⟨2216078, by rfl⟩ : syracuseStep 2954771 = 4432157) B4432157
theorem B20158085 : Blo 872567 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B2662483 : Blo 872567 2662483 := bstep (se 1 (by rfl) ⟨1996862, by rfl⟩ : syracuseStep 2662483 = 3993725) B3993725
theorem B7087657 : Blo 872567 7087657 := bstep (se 2 (by rfl) ⟨2657871, by rfl⟩ : syracuseStep 7087657 = 5315743) B5315743
theorem B41527133 : Blo 872567 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B3320777 : Blo 872567 3320777 := bstep (se 2 (by rfl) ⟨1245291, by rfl⟩ : syracuseStep 3320777 = 2490583) B2490583
theorem B15937003 : Blo 872567 15937003 := bstep (se 1 (by rfl) ⟨11952752, by rfl⟩ : syracuseStep 15937003 = 23905505) B23905505
theorem B4435721 : Blo 872567 4435721 := bstep (se 2 (by rfl) ⟨1663395, by rfl⟩ : syracuseStep 4435721 = 3326791) B3326791
theorem B12628183 : Blo 872567 12628183 := bstep (se 1 (by rfl) ⟨9471137, by rfl⟩ : syracuseStep 12628183 = 18942275) B18942275
theorem B8958329 : Blo 872567 8958329 := bstep (se 2 (by rfl) ⟨3359373, by rfl⟩ : syracuseStep 8958329 = 6718747) B6718747
theorem B3323375 : Blo 872567 3323375 := bstep (se 1 (by rfl) ⟨2492531, by rfl⟩ : syracuseStep 3323375 = 4985063) B4985063
theorem B3782143 : Blo 872567 3782143 := bstep (se 1 (by rfl) ⟨2836607, by rfl⟩ : syracuseStep 3782143 = 5673215) B5673215
theorem B30326345 : Blo 872567 30326345 := bstep (se 2 (by rfl) ⟨11372379, by rfl⟩ : syracuseStep 30326345 = 22744759) B22744759
theorem B1261423 : Blo 872567 1261423 := bstep (se 1 (by rfl) ⟨946067, by rfl⟩ : syracuseStep 1261423 = 1892135) B1892135
theorem B9453671 : Blo 872567 9453671 := bstep (se 1 (by rfl) ⟨7090253, by rfl⟩ : syracuseStep 9453671 = 14180507) B14180507
theorem B80692919 : Blo 872567 80692919 := bstep (se 1 (by rfl) ⟨60519689, by rfl⟩ : syracuseStep 80692919 = 121039379) B121039379
theorem B3983215 : Blo 872567 3983215 := bstep (se 1 (by rfl) ⟨2987411, by rfl⟩ : syracuseStep 3983215 = 5974823) B5974823
theorem B1329641 : Blo 872567 1329641 := bstep (se 2 (by rfl) ⟨498615, by rfl⟩ : syracuseStep 1329641 = 997231) B997231
theorem B3591049 : Blo 872567 3591049 := bstep (se 2 (by rfl) ⟨1346643, by rfl⟩ : syracuseStep 3591049 = 2693287) B2693287
theorem B1659143 : Blo 872567 1659143 := bstep (se 1 (by rfl) ⟨1244357, by rfl⟩ : syracuseStep 1659143 = 2488715) B2488715
theorem B872767 : Blo 872567 872767 := bstep (se 1 (by rfl) ⟨654575, by rfl⟩ : syracuseStep 872767 = 1309151) B1309151
theorem B9457991 : Blo 872567 9457991 := bstep (se 1 (by rfl) ⟨7093493, by rfl⟩ : syracuseStep 9457991 = 14186987) B14186987
theorem B873199 : Blo 872567 873199 := bstep (se 1 (by rfl) ⟨654899, by rfl⟩ : syracuseStep 873199 = 1309799) B1309799
theorem B873935 : Blo 872567 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B8968265 : Blo 872567 8968265 := bstep (se 2 (by rfl) ⟨3363099, by rfl⟩ : syracuseStep 8968265 = 6726199) B6726199
theorem B8411795 : Blo 872567 8411795 := bstep (se 1 (by rfl) ⟨6308846, by rfl⟩ : syracuseStep 8411795 = 12617693) B12617693
theorem B15948683 : Blo 872567 15948683 := bstep (se 1 (by rfl) ⟨11961512, by rfl⟩ : syracuseStep 15948683 = 23923025) B23923025
theorem B6643133 : Blo 872567 6643133 := bstep (se 3 (by rfl) ⟨1245587, by rfl⟩ : syracuseStep 6643133 = 2491175) B2491175
theorem B3727727 : Blo 872567 3727727 := bstep (se 1 (by rfl) ⟨2795795, by rfl⟩ : syracuseStep 3727727 = 5591591) B5591591
theorem B1663487 : Blo 872567 1663487 := bstep (se 1 (by rfl) ⟨1247615, by rfl⟩ : syracuseStep 1663487 = 2495231) B2495231
theorem B12608297 : Blo 872567 12608297 := bstep (se 2 (by rfl) ⟨4728111, by rfl⟩ : syracuseStep 12608297 = 9456223) B9456223
theorem B4973831 : Blo 872567 4973831 := bstep (se 1 (by rfl) ⟨3730373, by rfl⟩ : syracuseStep 4973831 = 7460747) B7460747
theorem B1308911 : Blo 872567 1308911 := bstep (se 1 (by rfl) ⟨981683, by rfl⟩ : syracuseStep 1308911 = 1963367) B1963367
theorem B1308959 : Blo 872567 1308959 := bstep (se 1 (by rfl) ⟨981719, by rfl⟩ : syracuseStep 1308959 = 1963439) B1963439
theorem B1964735 : Blo 872567 1964735 := bstep (se 1 (by rfl) ⟨1473551, by rfl⟩ : syracuseStep 1964735 = 2947103) B2947103
theorem B1309439 : Blo 872567 1309439 := bstep (se 1 (by rfl) ⟨982079, by rfl⟩ : syracuseStep 1309439 = 1964159) B1964159
theorem B2489399 : Blo 872567 2489399 := bstep (se 1 (by rfl) ⟨1867049, by rfl⟩ : syracuseStep 2489399 = 3734099) B3734099
theorem B982255 : Blo 872567 982255 := bstep (se 1 (by rfl) ⟨736691, by rfl⟩ : syracuseStep 982255 = 1473383) B1473383
theorem B1965671 : Blo 872567 1965671 := bstep (se 1 (by rfl) ⟨1474253, by rfl⟩ : syracuseStep 1965671 = 2948507) B2948507
theorem B1310567 : Blo 872567 1310567 := bstep (se 1 (by rfl) ⟨982925, by rfl⟩ : syracuseStep 1310567 = 1965851) B1965851
theorem B11534663 : Blo 872567 11534663 := bstep (se 1 (by rfl) ⟨8650997, by rfl⟩ : syracuseStep 11534663 = 17301995) B17301995
theorem B4424381 : Blo 872567 4424381 := bstep (se 3 (by rfl) ⟨829571, by rfl⟩ : syracuseStep 4424381 = 1659143) B1659143
theorem B26870939 : Blo 872567 26870939 := bstep (se 1 (by rfl) ⟨20153204, by rfl⟩ : syracuseStep 26870939 = 40306409) B40306409
theorem B1312121 : Blo 872567 1312121 := bstep (se 2 (by rfl) ⟨492045, by rfl⟩ : syracuseStep 1312121 = 984091) B984091
theorem B11208239 : Blo 872567 11208239 := bstep (se 1 (by rfl) ⟨8406179, by rfl⟩ : syracuseStep 11208239 = 16812359) B16812359
theorem B886427 : Blo 872567 886427 := bstep (se 1 (by rfl) ⟨664820, by rfl⟩ : syracuseStep 886427 = 1329641) B1329641
theorem B1312583 : Blo 872567 1312583 := bstep (se 1 (by rfl) ⟨984437, by rfl⟩ : syracuseStep 1312583 = 1968875) B1968875
theorem B1312871 : Blo 872567 1312871 := bstep (se 1 (by rfl) ⟨984653, by rfl⟩ : syracuseStep 1312871 = 1969307) B1969307
theorem B2951531 : Blo 872567 2951531 := bstep (se 1 (by rfl) ⟨2213648, by rfl⟩ : syracuseStep 2951531 = 4427297) B4427297
theorem B5310953 : Blo 872567 5310953 := bstep (se 2 (by rfl) ⟨1991607, by rfl⟩ : syracuseStep 5310953 = 3983215) B3983215
theorem B1968731 : Blo 872567 1968731 := bstep (se 1 (by rfl) ⟨1476548, by rfl⟩ : syracuseStep 1968731 = 2953097) B2953097
theorem B1313639 : Blo 872567 1313639 := bstep (se 1 (by rfl) ⟨985229, by rfl⟩ : syracuseStep 1313639 = 1970459) B1970459
theorem B1051807 : Blo 872567 1051807 := bstep (se 1 (by rfl) ⟨788855, by rfl⟩ : syracuseStep 1051807 = 1577711) B1577711
theorem B6294779 : Blo 872567 6294779 := bstep (se 1 (by rfl) ⟨4721084, by rfl⟩ : syracuseStep 6294779 = 9442169) B9442169
theorem B1314239 : Blo 872567 1314239 := bstep (se 1 (by rfl) ⟨985679, by rfl⟩ : syracuseStep 1314239 = 1971359) B1971359
theorem B1969847 : Blo 872567 1969847 := bstep (se 1 (by rfl) ⟨1477385, by rfl⟩ : syracuseStep 1969847 = 2954771) B2954771
theorem B13438723 : Blo 872567 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B4788065 : Blo 872567 4788065 := bstep (se 2 (by rfl) ⟨1795524, by rfl⟩ : syracuseStep 4788065 = 3591049) B3591049
theorem B5607863 : Blo 872567 5607863 := bstep (se 1 (by rfl) ⟨4205897, by rfl⟩ : syracuseStep 5607863 = 8411795) B8411795
theorem B4428755 : Blo 872567 4428755 := bstep (se 1 (by rfl) ⟨3321566, by rfl⟩ : syracuseStep 4428755 = 6643133) B6643133
theorem B3315887 : Blo 872567 3315887 := bstep (se 1 (by rfl) ⟨2486915, by rfl⟩ : syracuseStep 3315887 = 4973831) B4973831
theorem B2957147 : Blo 872567 2957147 := bstep (se 1 (by rfl) ⟨2217860, by rfl⟩ : syracuseStep 2957147 = 4435721) B4435721
theorem B5972219 : Blo 872567 5972219 := bstep (se 1 (by rfl) ⟨4479164, by rfl⟩ : syracuseStep 5972219 = 8958329) B8958329
theorem B6727589 : Blo 872567 6727589 := bstep (se 4 (by rfl) ⟨630711, by rfl⟩ : syracuseStep 6727589 = 1261423) B1261423
theorem B6302447 : Blo 872567 6302447 := bstep (se 1 (by rfl) ⟨4726835, by rfl⟩ : syracuseStep 6302447 = 9453671) B9453671
theorem B3549977 : Blo 872567 3549977 := bstep (se 2 (by rfl) ⟨1331241, by rfl⟩ : syracuseStep 3549977 = 2662483) B2662483
theorem B4436207 : Blo 872567 4436207 := bstep (se 1 (by rfl) ⟨3327155, by rfl⟩ : syracuseStep 4436207 = 6654311) B6654311
theorem B9450209 : Blo 872567 9450209 := bstep (se 2 (by rfl) ⟨3543828, by rfl⟩ : syracuseStep 9450209 = 7087657) B7087657
theorem B6305327 : Blo 872567 6305327 := bstep (se 1 (by rfl) ⟨4728995, by rfl⟩ : syracuseStep 6305327 = 9457991) B9457991
theorem B5978843 : Blo 872567 5978843 := bstep (se 1 (by rfl) ⟨4484132, by rfl⟩ : syracuseStep 5978843 = 8968265) B8968265
theorem B10632455 : Blo 872567 10632455 := bstep (se 1 (by rfl) ⟨7974341, by rfl⟩ : syracuseStep 10632455 = 15948683) B15948683
theorem B21249337 : Blo 872567 21249337 := bstep (se 2 (by rfl) ⟨7968501, by rfl⟩ : syracuseStep 21249337 = 15937003) B15937003
theorem B8405531 : Blo 872567 8405531 := bstep (se 1 (by rfl) ⟨6304148, by rfl⟩ : syracuseStep 8405531 = 12608297) B12608297
theorem B2213851 : Blo 872567 2213851 := bstep (se 1 (by rfl) ⟨1660388, by rfl⟩ : syracuseStep 2213851 = 3320777) B3320777
theorem B2215583 : Blo 872567 2215583 := bstep (se 1 (by rfl) ⟨1661687, by rfl⟩ : syracuseStep 2215583 = 3323375) B3323375
theorem B872607 : Blo 872567 872607 := bstep (se 1 (by rfl) ⟨654455, by rfl⟩ : syracuseStep 872607 = 1308911) B1308911
theorem B872639 : Blo 872567 872639 := bstep (se 1 (by rfl) ⟨654479, by rfl⟩ : syracuseStep 872639 = 1308959) B1308959
theorem B872959 : Blo 872567 872959 := bstep (se 1 (by rfl) ⟨654719, by rfl⟩ : syracuseStep 872959 = 1309439) B1309439
theorem B1659599 : Blo 872567 1659599 := bstep (se 1 (by rfl) ⟨1244699, by rfl⟩ : syracuseStep 1659599 = 2489399) B2489399
theorem B873711 : Blo 872567 873711 := bstep (se 1 (by rfl) ⟨655283, by rfl⟩ : syracuseStep 873711 = 1310567) B1310567
theorem B874267 : Blo 872567 874267 := bstep (se 1 (by rfl) ⟨655700, by rfl⟩ : syracuseStep 874267 = 1311401) B1311401
theorem B1661087 : Blo 872567 1661087 := bstep (se 1 (by rfl) ⟨1245815, by rfl⟩ : syracuseStep 1661087 = 2491631) B2491631
theorem B874735 : Blo 872567 874735 := bstep (se 1 (by rfl) ⟨656051, by rfl⟩ : syracuseStep 874735 = 1312103) B1312103
theorem B53795279 : Blo 872567 53795279 := bstep (se 1 (by rfl) ⟨40346459, by rfl⟩ : syracuseStep 53795279 = 80692919) B80692919
theorem B1661543 : Blo 872567 1661543 := bstep (se 1 (by rfl) ⟨1246157, by rfl⟩ : syracuseStep 1661543 = 2492315) B2492315
theorem B875503 : Blo 872567 875503 := bstep (se 1 (by rfl) ⟨656627, by rfl⟩ : syracuseStep 875503 = 1313255) B1313255
theorem B875647 : Blo 872567 875647 := bstep (se 1 (by rfl) ⟨656735, by rfl⟩ : syracuseStep 875647 = 1313471) B1313471
theorem B875775 : Blo 872567 875775 := bstep (se 1 (by rfl) ⟨656831, by rfl⟩ : syracuseStep 875775 = 1313663) B1313663
theorem B875935 : Blo 872567 875935 := bstep (se 1 (by rfl) ⟨656951, by rfl⟩ : syracuseStep 875935 = 1313903) B1313903
theorem B876187 : Blo 872567 876187 := bstep (se 1 (by rfl) ⟨657140, by rfl⟩ : syracuseStep 876187 = 1314281) B1314281
theorem B876315 : Blo 872567 876315 := bstep (se 1 (by rfl) ⟨657236, by rfl⟩ : syracuseStep 876315 = 1314473) B1314473
theorem B3039611 : Blo 872567 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B2485151 : Blo 872567 2485151 := bstep (se 1 (by rfl) ⟨1863863, by rfl⟩ : syracuseStep 2485151 = 3727727) B3727727
theorem B16837577 : Blo 872567 16837577 := bstep (se 2 (by rfl) ⟨6314091, by rfl⟩ : syracuseStep 16837577 = 12628183) B12628183
theorem B1108991 : Blo 872567 1108991 := bstep (se 1 (by rfl) ⟨831743, by rfl⟩ : syracuseStep 1108991 = 1663487) B1663487
theorem B27684755 : Blo 872567 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B5042857 : Blo 872567 5042857 := bstep (se 2 (by rfl) ⟨1891071, by rfl⟩ : syracuseStep 5042857 = 3782143) B3782143
theorem B1309673 : Blo 872567 1309673 := bstep (se 2 (by rfl) ⟨491127, by rfl⟩ : syracuseStep 1309673 = 982255) B982255
theorem B1309823 : Blo 872567 1309823 := bstep (se 1 (by rfl) ⟨982367, by rfl⟩ : syracuseStep 1309823 = 1964735) B1964735
theorem B20217563 : Blo 872567 20217563 := bstep (se 1 (by rfl) ⟨15163172, by rfl⟩ : syracuseStep 20217563 = 30326345) B30326345
theorem B1310447 : Blo 872567 1310447 := bstep (se 1 (by rfl) ⟨982835, by rfl⟩ : syracuseStep 1310447 = 1965671) B1965671
theorem B5603687 : Blo 872567 5603687 := bstep (se 1 (by rfl) ⟨4202765, by rfl⟩ : syracuseStep 5603687 = 8405531) B8405531
theorem B2949587 : Blo 872567 2949587 := bstep (se 1 (by rfl) ⟨2212190, by rfl⟩ : syracuseStep 2949587 = 4424381) B4424381
theorem B7472159 : Blo 872567 7472159 := bstep (se 1 (by rfl) ⟨5604119, by rfl⟩ : syracuseStep 7472159 = 11208239) B11208239
theorem B1967687 : Blo 872567 1967687 := bstep (se 1 (by rfl) ⟨1475765, by rfl⟩ : syracuseStep 1967687 = 2951531) B2951531
theorem B3540635 : Blo 872567 3540635 := bstep (se 1 (by rfl) ⟨2655476, by rfl⟩ : syracuseStep 3540635 = 5310953) B5310953
theorem B1312487 : Blo 872567 1312487 := bstep (se 1 (by rfl) ⟨984365, by rfl⟩ : syracuseStep 1312487 = 1968731) B1968731
theorem B4196519 : Blo 872567 4196519 := bstep (se 1 (by rfl) ⟨3147389, by rfl⟩ : syracuseStep 4196519 = 6294779) B6294779
theorem B1477055 : Blo 872567 1477055 := bstep (se 1 (by rfl) ⟨1107791, by rfl⟩ : syracuseStep 1477055 = 2215583) B2215583
theorem B1313231 : Blo 872567 1313231 := bstep (se 1 (by rfl) ⟨984923, by rfl⟩ : syracuseStep 1313231 = 1969847) B1969847
theorem B2951801 : Blo 872567 2951801 := bstep (se 2 (by rfl) ⟨1106925, by rfl⟩ : syracuseStep 2951801 = 2213851) B2213851
theorem B3738575 : Blo 872567 3738575 := bstep (se 1 (by rfl) ⟨2803931, by rfl⟩ : syracuseStep 3738575 = 5607863) B5607863
theorem B2952503 : Blo 872567 2952503 := bstep (se 1 (by rfl) ⟨2214377, by rfl⟩ : syracuseStep 2952503 = 4428755) B4428755
theorem B1971431 : Blo 872567 1971431 := bstep (se 1 (by rfl) ⟨1478573, by rfl⟩ : syracuseStep 1971431 = 2957147) B2957147
theorem B4429565 : Blo 872567 4429565 := bstep (se 3 (by rfl) ⟨830543, by rfl⟩ : syracuseStep 4429565 = 1661087) B1661087
theorem B6723809 : Blo 872567 6723809 := bstep (se 2 (by rfl) ⟨2521428, by rfl⟩ : syracuseStep 6723809 = 5042857) B5042857
theorem B4201631 : Blo 872567 4201631 := bstep (se 1 (by rfl) ⟨3151223, by rfl⟩ : syracuseStep 4201631 = 6302447) B6302447
theorem B2366651 : Blo 872567 2366651 := bstep (se 1 (by rfl) ⟨1774988, by rfl⟩ : syracuseStep 2366651 = 3549977) B3549977
theorem B18456503 : Blo 872567 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B2957309 : Blo 872567 2957309 := bstep (se 3 (by rfl) ⟨554495, by rfl⟩ : syracuseStep 2957309 = 1108991) B1108991
theorem B2957471 : Blo 872567 2957471 := bstep (se 1 (by rfl) ⟨2218103, by rfl⟩ : syracuseStep 2957471 = 4436207) B4436207
theorem B6300139 : Blo 872567 6300139 := bstep (se 1 (by rfl) ⟨4725104, by rfl⟩ : syracuseStep 6300139 = 9450209) B9450209
theorem B4203551 : Blo 872567 4203551 := bstep (se 1 (by rfl) ⟨3152663, by rfl⟩ : syracuseStep 4203551 = 6305327) B6305327
theorem B7088303 : Blo 872567 7088303 := bstep (se 1 (by rfl) ⟨5316227, by rfl⟩ : syracuseStep 7088303 = 10632455) B10632455
theorem B13478375 : Blo 872567 13478375 := bstep (se 1 (by rfl) ⟨10108781, by rfl⟩ : syracuseStep 13478375 = 20217563) B20217563
theorem B3192043 : Blo 872567 3192043 := bstep (se 1 (by rfl) ⟨2394032, by rfl⟩ : syracuseStep 3192043 = 4788065) B4788065
theorem B32422517 : Blo 872567 32422517 := bstep (se 5 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 32422517 = 3039611) B3039611
theorem B2210591 : Blo 872567 2210591 := bstep (se 1 (by rfl) ⟨1657943, by rfl⟩ : syracuseStep 2210591 = 3315887) B3315887
theorem B35863519 : Blo 872567 35863519 := bstep (se 1 (by rfl) ⟨26897639, by rfl⟩ : syracuseStep 35863519 = 53795279) B53795279
theorem B3981479 : Blo 872567 3981479 := bstep (se 1 (by rfl) ⟨2986109, by rfl⟩ : syracuseStep 3981479 = 5972219) B5972219
theorem B9455221 : Blo 872567 9455221 := bstep (se 5 (by rfl) ⟨443213, by rfl⟩ : syracuseStep 9455221 = 886427) B886427
theorem B1656767 : Blo 872567 1656767 := bstep (se 1 (by rfl) ⟨1242575, by rfl⟩ : syracuseStep 1656767 = 2485151) B2485151
theorem B11225051 : Blo 872567 11225051 := bstep (se 1 (by rfl) ⟨8418788, by rfl⟩ : syracuseStep 11225051 = 16837577) B16837577
theorem B28332449 : Blo 872567 28332449 := bstep (se 2 (by rfl) ⟨10624668, by rfl⟩ : syracuseStep 28332449 = 21249337) B21249337
theorem B3985895 : Blo 872567 3985895 := bstep (se 1 (by rfl) ⟨2989421, by rfl⟩ : syracuseStep 3985895 = 5978843) B5978843
theorem B873115 : Blo 872567 873115 := bstep (se 1 (by rfl) ⟨654836, by rfl⟩ : syracuseStep 873115 = 1309673) B1309673
theorem B873215 : Blo 872567 873215 := bstep (se 1 (by rfl) ⟨654911, by rfl⟩ : syracuseStep 873215 = 1309823) B1309823
theorem B873631 : Blo 872567 873631 := bstep (se 1 (by rfl) ⟨655223, by rfl⟩ : syracuseStep 873631 = 1310447) B1310447
theorem B7689775 : Blo 872567 7689775 := bstep (se 1 (by rfl) ⟨5767331, by rfl⟩ : syracuseStep 7689775 = 11534663) B11534663
theorem B17913959 : Blo 872567 17913959 := bstep (se 1 (by rfl) ⟨13435469, by rfl⟩ : syracuseStep 17913959 = 26870939) B26870939
theorem B874747 : Blo 872567 874747 := bstep (se 1 (by rfl) ⟨656060, by rfl⟩ : syracuseStep 874747 = 1312121) B1312121
theorem B875055 : Blo 872567 875055 := bstep (se 1 (by rfl) ⟨656291, by rfl⟩ : syracuseStep 875055 = 1312583) B1312583
theorem B875247 : Blo 872567 875247 := bstep (se 1 (by rfl) ⟨656435, by rfl⟩ : syracuseStep 875247 = 1312871) B1312871
theorem B875759 : Blo 872567 875759 := bstep (se 1 (by rfl) ⟨656819, by rfl⟩ : syracuseStep 875759 = 1313639) B1313639
theorem B876159 : Blo 872567 876159 := bstep (se 1 (by rfl) ⟨657119, by rfl⟩ : syracuseStep 876159 = 1314239) B1314239
theorem B1106399 : Blo 872567 1106399 := bstep (se 1 (by rfl) ⟨829799, by rfl⟩ : syracuseStep 1106399 = 1659599) B1659599
theorem B1402409 : Blo 872567 1402409 := bstep (se 2 (by rfl) ⟨525903, by rfl⟩ : syracuseStep 1402409 = 1051807) B1051807
theorem B1107695 : Blo 872567 1107695 := bstep (se 1 (by rfl) ⟨830771, by rfl⟩ : syracuseStep 1107695 = 1661543) B1661543
theorem B17918297 : Blo 872567 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B4485059 : Blo 872567 4485059 := bstep (se 1 (by rfl) ⟨3363794, by rfl⟩ : syracuseStep 4485059 = 6727589) B6727589
theorem B3735791 : Blo 872567 3735791 := bstep (se 1 (by rfl) ⟨2801843, by rfl⟩ : syracuseStep 3735791 = 5603687) B5603687
theorem B1966391 : Blo 872567 1966391 := bstep (se 1 (by rfl) ⟨1474793, by rfl⟩ : syracuseStep 1966391 = 2949587) B2949587
theorem B10617277 : Blo 872567 10617277 := bstep (se 3 (by rfl) ⟨1990739, by rfl⟩ : syracuseStep 10617277 = 3981479) B3981479
theorem B4981439 : Blo 872567 4981439 := bstep (se 1 (by rfl) ⟨3736079, by rfl⟩ : syracuseStep 4981439 = 7472159) B7472159
theorem B1311791 : Blo 872567 1311791 := bstep (se 1 (by rfl) ⟨983843, by rfl⟩ : syracuseStep 1311791 = 1967687) B1967687
theorem B2360423 : Blo 872567 2360423 := bstep (se 1 (by rfl) ⟨1770317, by rfl⟩ : syracuseStep 2360423 = 3540635) B3540635
theorem B2950397 : Blo 872567 2950397 := bstep (se 3 (by rfl) ⟨553199, by rfl⟩ : syracuseStep 2950397 = 1106399) B1106399
theorem B984703 : Blo 872567 984703 := bstep (se 1 (by rfl) ⟨738527, by rfl⟩ : syracuseStep 984703 = 1477055) B1477055
theorem B1967867 : Blo 872567 1967867 := bstep (se 1 (by rfl) ⟨1475900, by rfl⟩ : syracuseStep 1967867 = 2951801) B2951801
theorem B2492383 : Blo 872567 2492383 := bstep (se 1 (by rfl) ⟨1869287, by rfl⟩ : syracuseStep 2492383 = 3738575) B3738575
theorem B1968335 : Blo 872567 1968335 := bstep (se 1 (by rfl) ⟨1476251, by rfl⟩ : syracuseStep 1968335 = 2952503) B2952503
theorem B1314287 : Blo 872567 1314287 := bstep (se 1 (by rfl) ⟨985715, by rfl⟩ : syracuseStep 1314287 = 1971431) B1971431
theorem B2953043 : Blo 872567 2953043 := bstep (se 1 (by rfl) ⟨2214782, by rfl⟩ : syracuseStep 2953043 = 4429565) B4429565
theorem B2953853 : Blo 872567 2953853 := bstep (se 3 (by rfl) ⟨553847, by rfl⟩ : syracuseStep 2953853 = 1107695) B1107695
theorem B1577767 : Blo 872567 1577767 := bstep (se 1 (by rfl) ⟨1183325, by rfl⟩ : syracuseStep 1577767 = 2366651) B2366651
theorem B1971539 : Blo 872567 1971539 := bstep (se 1 (by rfl) ⟨1478654, by rfl⟩ : syracuseStep 1971539 = 2957309) B2957309
theorem B1971647 : Blo 872567 1971647 := bstep (se 1 (by rfl) ⟨1478735, by rfl⟩ : syracuseStep 1971647 = 2957471) B2957471
theorem B4725535 : Blo 872567 4725535 := bstep (se 1 (by rfl) ⟨3544151, by rfl⟩ : syracuseStep 4725535 = 7088303) B7088303
theorem B8985583 : Blo 872567 8985583 := bstep (se 1 (by rfl) ⟨6739187, by rfl⟩ : syracuseStep 8985583 = 13478375) B13478375
theorem B2990039 : Blo 872567 2990039 := bstep (se 1 (by rfl) ⟨2242529, by rfl⟩ : syracuseStep 2990039 = 4485059) B4485059
theorem B47818025 : Blo 872567 47818025 := bstep (se 2 (by rfl) ⟨17931759, by rfl⟩ : syracuseStep 47818025 = 35863519) B35863519
theorem B8400185 : Blo 872567 8400185 := bstep (se 2 (by rfl) ⟨3150069, by rfl⟩ : syracuseStep 8400185 = 6300139) B6300139
theorem B10629053 : Blo 872567 10629053 := bstep (se 3 (by rfl) ⟨1992947, by rfl⟩ : syracuseStep 10629053 = 3985895) B3985895
theorem B7483367 : Blo 872567 7483367 := bstep (se 1 (by rfl) ⟨5612525, by rfl⟩ : syracuseStep 7483367 = 11225051) B11225051
theorem B2797679 : Blo 872567 2797679 := bstep (se 1 (by rfl) ⟨2098259, by rfl⟩ : syracuseStep 2797679 = 4196519) B4196519
theorem B18888299 : Blo 872567 18888299 := bstep (se 1 (by rfl) ⟨14166224, by rfl⟩ : syracuseStep 18888299 = 28332449) B28332449
theorem B11942639 : Blo 872567 11942639 := bstep (se 1 (by rfl) ⟨8956979, by rfl⟩ : syracuseStep 11942639 = 17913959) B17913959
theorem B2801087 : Blo 872567 2801087 := bstep (se 1 (by rfl) ⟨2100815, by rfl⟩ : syracuseStep 2801087 = 4201631) B4201631
theorem B2802367 : Blo 872567 2802367 := bstep (se 1 (by rfl) ⟨2101775, by rfl⟩ : syracuseStep 2802367 = 4203551) B4203551
theorem B934939 : Blo 872567 934939 := bstep (se 1 (by rfl) ⟨701204, by rfl⟩ : syracuseStep 934939 = 1402409) B1402409
theorem B11945531 : Blo 872567 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B21615011 : Blo 872567 21615011 := bstep (se 1 (by rfl) ⟨16211258, by rfl⟩ : syracuseStep 21615011 = 32422517) B32422517
theorem B874991 : Blo 872567 874991 := bstep (se 1 (by rfl) ⟨656243, by rfl⟩ : syracuseStep 874991 = 1312487) B1312487
theorem B1104511 : Blo 872567 1104511 := bstep (se 1 (by rfl) ⟨828383, by rfl⟩ : syracuseStep 1104511 = 1656767) B1656767
theorem B875487 : Blo 872567 875487 := bstep (se 1 (by rfl) ⟨656615, by rfl⟩ : syracuseStep 875487 = 1313231) B1313231
theorem B4482539 : Blo 872567 4482539 := bstep (se 1 (by rfl) ⟨3361904, by rfl⟩ : syracuseStep 4482539 = 6723809) B6723809
theorem B4256057 : Blo 872567 4256057 := bstep (se 2 (by rfl) ⟨1596021, by rfl⟩ : syracuseStep 4256057 = 3192043) B3192043
theorem B10253033 : Blo 872567 10253033 := bstep (se 2 (by rfl) ⟨3844887, by rfl⟩ : syracuseStep 10253033 = 7689775) B7689775
theorem B50427845 : Blo 872567 50427845 := bstep (se 4 (by rfl) ⟨4727610, by rfl⟩ : syracuseStep 50427845 = 9455221) B9455221
theorem B1473727 : Blo 872567 1473727 := bstep (se 1 (by rfl) ⟨1105295, by rfl⟩ : syracuseStep 1473727 = 2210591) B2210591
theorem B49217341 : Blo 872567 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B2490527 : Blo 872567 2490527 := bstep (se 1 (by rfl) ⟨1867895, by rfl⟩ : syracuseStep 2490527 = 3735791) B3735791
theorem B1310927 : Blo 872567 1310927 := bstep (se 1 (by rfl) ⟨983195, by rfl⟩ : syracuseStep 1310927 = 1966391) B1966391
theorem B14156369 : Blo 872567 14156369 := bstep (se 2 (by rfl) ⟨5308638, by rfl⟩ : syracuseStep 14156369 = 10617277) B10617277
theorem B1573615 : Blo 872567 1573615 := bstep (se 1 (by rfl) ⟨1180211, by rfl⟩ : syracuseStep 1573615 = 2360423) B2360423
theorem B1966931 : Blo 872567 1966931 := bstep (se 1 (by rfl) ⟨1475198, by rfl⟩ : syracuseStep 1966931 = 2950397) B2950397
theorem B7963687 : Blo 872567 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B1311911 : Blo 872567 1311911 := bstep (se 1 (by rfl) ⟨983933, by rfl⟩ : syracuseStep 1311911 = 1967867) B1967867
theorem B1246585 : Blo 872567 1246585 := bstep (se 2 (by rfl) ⟨467469, by rfl⟩ : syracuseStep 1246585 = 934939) B934939
theorem B1312223 : Blo 872567 1312223 := bstep (se 1 (by rfl) ⟨984167, by rfl⟩ : syracuseStep 1312223 = 1968335) B1968335
theorem B1312937 : Blo 872567 1312937 := bstep (se 2 (by rfl) ⟨492351, by rfl⟩ : syracuseStep 1312937 = 984703) B984703
theorem B1968695 : Blo 872567 1968695 := bstep (se 1 (by rfl) ⟨1476521, by rfl⟩ : syracuseStep 1968695 = 2953043) B2953043
theorem B1969235 : Blo 872567 1969235 := bstep (se 1 (by rfl) ⟨1476926, by rfl⟩ : syracuseStep 1969235 = 2953853) B2953853
theorem B1314359 : Blo 872567 1314359 := bstep (se 1 (by rfl) ⟨985769, by rfl⟩ : syracuseStep 1314359 = 1971539) B1971539
theorem B1314431 : Blo 872567 1314431 := bstep (se 1 (by rfl) ⟨985823, by rfl⟩ : syracuseStep 1314431 = 1971647) B1971647
theorem B14945957 : Blo 872567 14945957 := bstep (se 4 (by rfl) ⟨1401183, by rfl⟩ : syracuseStep 14945957 = 2802367) B2802367
theorem B2988359 : Blo 872567 2988359 := bstep (se 1 (by rfl) ⟨2241269, by rfl⟩ : syracuseStep 2988359 = 4482539) B4482539
theorem B2103689 : Blo 872567 2103689 := bstep (se 2 (by rfl) ⟨788883, by rfl⟩ : syracuseStep 2103689 = 1577767) B1577767
theorem B7086035 : Blo 872567 7086035 := bstep (se 1 (by rfl) ⟨5314526, by rfl⟩ : syracuseStep 7086035 = 10629053) B10629053
theorem B4988911 : Blo 872567 4988911 := bstep (se 1 (by rfl) ⟨3741683, by rfl⟩ : syracuseStep 4988911 = 7483367) B7483367
theorem B6300713 : Blo 872567 6300713 := bstep (se 2 (by rfl) ⟨2362767, by rfl⟩ : syracuseStep 6300713 = 4725535) B4725535
theorem B12592199 : Blo 872567 12592199 := bstep (se 1 (by rfl) ⟨9444149, by rfl⟩ : syracuseStep 12592199 = 18888299) B18888299
theorem B7973437 : Blo 872567 7973437 := bstep (se 3 (by rfl) ⟨1495019, by rfl⟩ : syracuseStep 7973437 = 2990039) B2990039
theorem B3320959 : Blo 872567 3320959 := bstep (se 1 (by rfl) ⟨2490719, by rfl⟩ : syracuseStep 3320959 = 4981439) B4981439
theorem B3323177 : Blo 872567 3323177 := bstep (se 2 (by rfl) ⟨1246191, by rfl⟩ : syracuseStep 3323177 = 2492383) B2492383
theorem B47923109 : Blo 872567 47923109 := bstep (se 4 (by rfl) ⟨4492791, by rfl⟩ : syracuseStep 47923109 = 8985583) B8985583
theorem B2837371 : Blo 872567 2837371 := bstep (se 1 (by rfl) ⟨2128028, by rfl⟩ : syracuseStep 2837371 = 4256057) B4256057
theorem B6835355 : Blo 872567 6835355 := bstep (se 1 (by rfl) ⟨5126516, by rfl⟩ : syracuseStep 6835355 = 10253033) B10253033
theorem B65623121 : Blo 872567 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B874527 : Blo 872567 874527 := bstep (se 1 (by rfl) ⟨655895, by rfl⟩ : syracuseStep 874527 = 1311791) B1311791
theorem B876191 : Blo 872567 876191 := bstep (se 1 (by rfl) ⟨657143, by rfl⟩ : syracuseStep 876191 = 1314287) B1314287
theorem B14410007 : Blo 872567 14410007 := bstep (se 1 (by rfl) ⟨10807505, by rfl⟩ : syracuseStep 14410007 = 21615011) B21615011
theorem B31878683 : Blo 872567 31878683 := bstep (se 1 (by rfl) ⟨23909012, by rfl⟩ : syracuseStep 31878683 = 47818025) B47818025
theorem B5600123 : Blo 872567 5600123 := bstep (se 1 (by rfl) ⟨4200092, by rfl⟩ : syracuseStep 5600123 = 8400185) B8400185
theorem B1865119 : Blo 872567 1865119 := bstep (se 1 (by rfl) ⟨1398839, by rfl⟩ : syracuseStep 1865119 = 2797679) B2797679
theorem B1472681 : Blo 872567 1472681 := bstep (se 2 (by rfl) ⟨552255, by rfl⟩ : syracuseStep 1472681 = 1104511) B1104511
theorem B33618563 : Blo 872567 33618563 := bstep (se 1 (by rfl) ⟨25213922, by rfl⟩ : syracuseStep 33618563 = 50427845) B50427845
theorem B1964969 : Blo 872567 1964969 := bstep (se 2 (by rfl) ⟨736863, by rfl⟩ : syracuseStep 1964969 = 1473727) B1473727
theorem B7961759 : Blo 872567 7961759 := bstep (se 1 (by rfl) ⟨5971319, by rfl⟩ : syracuseStep 7961759 = 11942639) B11942639
theorem B1867391 : Blo 872567 1867391 := bstep (se 1 (by rfl) ⟨1400543, by rfl⟩ : syracuseStep 1867391 = 2801087) B2801087
theorem B9437579 : Blo 872567 9437579 := bstep (se 1 (by rfl) ⟨7078184, by rfl⟩ : syracuseStep 9437579 = 14156369) B14156369
theorem B1311287 : Blo 872567 1311287 := bstep (se 1 (by rfl) ⟨983465, by rfl⟩ : syracuseStep 1311287 = 1966931) B1966931
theorem B2098153 : Blo 872567 2098153 := bstep (se 2 (by rfl) ⟨786807, by rfl⟩ : syracuseStep 2098153 = 1573615) B1573615
theorem B1312463 : Blo 872567 1312463 := bstep (se 1 (by rfl) ⟨984347, by rfl⟩ : syracuseStep 1312463 = 1968695) B1968695
theorem B1312823 : Blo 872567 1312823 := bstep (se 1 (by rfl) ⟨984617, by rfl⟩ : syracuseStep 1312823 = 1969235) B1969235
theorem B4556903 : Blo 872567 4556903 := bstep (se 1 (by rfl) ⟨3417677, by rfl⟩ : syracuseStep 4556903 = 6835355) B6835355
theorem B9963971 : Blo 872567 9963971 := bstep (se 1 (by rfl) ⟨7472978, by rfl⟩ : syracuseStep 9963971 = 14945957) B14945957
theorem B43748747 : Blo 872567 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B4427945 : Blo 872567 4427945 := bstep (se 2 (by rfl) ⟨1660479, by rfl⟩ : syracuseStep 4427945 = 3320959) B3320959
theorem B4724023 : Blo 872567 4724023 := bstep (se 1 (by rfl) ⟨3543017, by rfl⟩ : syracuseStep 4724023 = 7086035) B7086035
theorem B9606671 : Blo 872567 9606671 := bstep (se 1 (by rfl) ⟨7205003, by rfl⟩ : syracuseStep 9606671 = 14410007) B14410007
theorem B42472997 : Blo 872567 42472997 := bstep (se 4 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 42472997 = 7963687) B7963687
theorem B5609837 : Blo 872567 5609837 := bstep (se 3 (by rfl) ⟨1051844, by rfl⟩ : syracuseStep 5609837 = 2103689) B2103689
theorem B10631249 : Blo 872567 10631249 := bstep (se 2 (by rfl) ⟨3986718, by rfl⟩ : syracuseStep 10631249 = 7973437) B7973437
theorem B3783161 : Blo 872567 3783161 := bstep (se 2 (by rfl) ⟨1418685, by rfl⟩ : syracuseStep 3783161 = 2837371) B2837371
theorem B21252455 : Blo 872567 21252455 := bstep (se 1 (by rfl) ⟨15939341, by rfl⟩ : syracuseStep 21252455 = 31878683) B31878683
theorem B2215451 : Blo 872567 2215451 := bstep (se 1 (by rfl) ⟨1661588, by rfl⟩ : syracuseStep 2215451 = 3323177) B3323177
theorem B1660351 : Blo 872567 1660351 := bstep (se 1 (by rfl) ⟨1245263, by rfl⟩ : syracuseStep 1660351 = 2490527) B2490527
theorem B873951 : Blo 872567 873951 := bstep (se 1 (by rfl) ⟨655463, by rfl⟩ : syracuseStep 873951 = 1310927) B1310927
theorem B874607 : Blo 872567 874607 := bstep (se 1 (by rfl) ⟨655955, by rfl⟩ : syracuseStep 874607 = 1311911) B1311911
theorem B874815 : Blo 872567 874815 := bstep (se 1 (by rfl) ⟨656111, by rfl⟩ : syracuseStep 874815 = 1312223) B1312223
theorem B875291 : Blo 872567 875291 := bstep (se 1 (by rfl) ⟨656468, by rfl⟩ : syracuseStep 875291 = 1312937) B1312937
theorem B1662113 : Blo 872567 1662113 := bstep (se 2 (by rfl) ⟨623292, by rfl⟩ : syracuseStep 1662113 = 1246585) B1246585
theorem B876239 : Blo 872567 876239 := bstep (se 1 (by rfl) ⟨657179, by rfl⟩ : syracuseStep 876239 = 1314359) B1314359
theorem B876287 : Blo 872567 876287 := bstep (se 1 (by rfl) ⟨657215, by rfl⟩ : syracuseStep 876287 = 1314431) B1314431
theorem B16801901 : Blo 872567 16801901 := bstep (se 3 (by rfl) ⟨3150356, by rfl⟩ : syracuseStep 16801901 = 6300713) B6300713
theorem B33579197 : Blo 872567 33579197 := bstep (se 3 (by rfl) ⟨6296099, by rfl⟩ : syracuseStep 33579197 = 12592199) B12592199
theorem B1992239 : Blo 872567 1992239 := bstep (se 1 (by rfl) ⟨1494179, by rfl⟩ : syracuseStep 1992239 = 2988359) B2988359
theorem B2486825 : Blo 872567 2486825 := bstep (se 2 (by rfl) ⟨932559, by rfl⟩ : syracuseStep 2486825 = 1865119) B1865119
theorem B3733415 : Blo 872567 3733415 := bstep (se 1 (by rfl) ⟨2800061, by rfl⟩ : syracuseStep 3733415 = 5600123) B5600123
theorem B981787 : Blo 872567 981787 := bstep (se 1 (by rfl) ⟨736340, by rfl⟩ : syracuseStep 981787 = 1472681) B1472681
theorem B22412375 : Blo 872567 22412375 := bstep (se 1 (by rfl) ⟨16809281, by rfl⟩ : syracuseStep 22412375 = 33618563) B33618563
theorem B1309979 : Blo 872567 1309979 := bstep (se 1 (by rfl) ⟨982484, by rfl⟩ : syracuseStep 1309979 = 1964969) B1964969
theorem B5307839 : Blo 872567 5307839 := bstep (se 1 (by rfl) ⟨3980879, by rfl⟩ : syracuseStep 5307839 = 7961759) B7961759
theorem B1244927 : Blo 872567 1244927 := bstep (se 1 (by rfl) ⟨933695, by rfl⟩ : syracuseStep 1244927 = 1867391) B1867391
theorem B31948739 : Blo 872567 31948739 := bstep (se 1 (by rfl) ⟨23961554, by rfl⟩ : syracuseStep 31948739 = 47923109) B47923109
theorem B6651881 : Blo 872567 6651881 := bstep (se 2 (by rfl) ⟨2494455, by rfl⟩ : syracuseStep 6651881 = 4988911) B4988911
theorem B6291719 : Blo 872567 6291719 := bstep (se 1 (by rfl) ⟨4718789, by rfl⟩ : syracuseStep 6291719 = 9437579) B9437579
theorem B29165831 : Blo 872567 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B1476967 : Blo 872567 1476967 := bstep (se 1 (by rfl) ⟨1107725, by rfl⟩ : syracuseStep 1476967 = 2215451) B2215451
theorem B2951963 : Blo 872567 2951963 := bstep (se 1 (by rfl) ⟨2213972, by rfl⟩ : syracuseStep 2951963 = 4427945) B4427945
theorem B28315331 : Blo 872567 28315331 := bstep (se 1 (by rfl) ⟨21236498, by rfl⟩ : syracuseStep 28315331 = 42472997) B42472997
theorem B3739891 : Blo 872567 3739891 := bstep (se 1 (by rfl) ⟨2804918, by rfl⟩ : syracuseStep 3739891 = 5609837) B5609837
theorem B22386131 : Blo 872567 22386131 := bstep (se 1 (by rfl) ⟨16789598, by rfl⟩ : syracuseStep 22386131 = 33579197) B33579197
theorem B6298697 : Blo 872567 6298697 := bstep (se 2 (by rfl) ⟨2362011, by rfl⟩ : syracuseStep 6298697 = 4724023) B4724023
theorem B7087499 : Blo 872567 7087499 := bstep (se 1 (by rfl) ⟨5315624, by rfl⟩ : syracuseStep 7087499 = 10631249) B10631249
theorem B3319805 : Blo 872567 3319805 := bstep (se 3 (by rfl) ⟨622463, by rfl⟩ : syracuseStep 3319805 = 1244927) B1244927
theorem B4434587 : Blo 872567 4434587 := bstep (se 1 (by rfl) ⟨3325940, by rfl⟩ : syracuseStep 4434587 = 6651881) B6651881
theorem B48606965 : Blo 872567 48606965 := bstep (se 5 (by rfl) ⟨2278451, by rfl⟩ : syracuseStep 48606965 = 4556903) B4556903
theorem B14168303 : Blo 872567 14168303 := bstep (se 1 (by rfl) ⟨10626227, by rfl⟩ : syracuseStep 14168303 = 21252455) B21252455
theorem B6404447 : Blo 872567 6404447 := bstep (se 1 (by rfl) ⟨4803335, by rfl⟩ : syracuseStep 6404447 = 9606671) B9606671
theorem B11190149 : Blo 872567 11190149 := bstep (se 4 (by rfl) ⟨1049076, by rfl⟩ : syracuseStep 11190149 = 2098153) B2098153
theorem B1328159 : Blo 872567 1328159 := bstep (se 1 (by rfl) ⟨996119, by rfl⟩ : syracuseStep 1328159 = 1992239) B1992239
theorem B2213801 : Blo 872567 2213801 := bstep (se 2 (by rfl) ⟨830175, by rfl⟩ : syracuseStep 2213801 = 1660351) B1660351
theorem B1657883 : Blo 872567 1657883 := bstep (se 1 (by rfl) ⟨1243412, by rfl⟩ : syracuseStep 1657883 = 2486825) B2486825
theorem B873319 : Blo 872567 873319 := bstep (se 1 (by rfl) ⟨654989, by rfl⟩ : syracuseStep 873319 = 1309979) B1309979
theorem B874191 : Blo 872567 874191 := bstep (se 1 (by rfl) ⟨655643, by rfl⟩ : syracuseStep 874191 = 1311287) B1311287
theorem B874975 : Blo 872567 874975 := bstep (se 1 (by rfl) ⟨656231, by rfl⟩ : syracuseStep 874975 = 1312463) B1312463
theorem B875215 : Blo 872567 875215 := bstep (se 1 (by rfl) ⟨656411, by rfl⟩ : syracuseStep 875215 = 1312823) B1312823
theorem B6642647 : Blo 872567 6642647 := bstep (se 1 (by rfl) ⟨4981985, by rfl⟩ : syracuseStep 6642647 = 9963971) B9963971
theorem B1108075 : Blo 872567 1108075 := bstep (se 1 (by rfl) ⟨831056, by rfl⟩ : syracuseStep 1108075 = 1662113) B1662113
theorem B11201267 : Blo 872567 11201267 := bstep (se 1 (by rfl) ⟨8400950, by rfl⟩ : syracuseStep 11201267 = 16801901) B16801901
theorem B1309049 : Blo 872567 1309049 := bstep (se 2 (by rfl) ⟨490893, by rfl⟩ : syracuseStep 1309049 = 981787) B981787
theorem B2488943 : Blo 872567 2488943 := bstep (se 1 (by rfl) ⟨1866707, by rfl⟩ : syracuseStep 2488943 = 3733415) B3733415
theorem B2522107 : Blo 872567 2522107 := bstep (se 1 (by rfl) ⟨1891580, by rfl⟩ : syracuseStep 2522107 = 3783161) B3783161
theorem B14941583 : Blo 872567 14941583 := bstep (se 1 (by rfl) ⟨11206187, by rfl⟩ : syracuseStep 14941583 = 22412375) B22412375
theorem B3538559 : Blo 872567 3538559 := bstep (se 1 (by rfl) ⟨2653919, by rfl⟩ : syracuseStep 3538559 = 5307839) B5307839
theorem B21299159 : Blo 872567 21299159 := bstep (se 1 (by rfl) ⟨15974369, by rfl⟩ : syracuseStep 21299159 = 31948739) B31948739
theorem B4194479 : Blo 872567 4194479 := bstep (se 1 (by rfl) ⟨3145859, by rfl⟩ : syracuseStep 4194479 = 6291719) B6291719
theorem B885439 : Blo 872567 885439 := bstep (se 1 (by rfl) ⟨664079, by rfl⟩ : syracuseStep 885439 = 1328159) B1328159
theorem B1475867 : Blo 872567 1475867 := bstep (se 1 (by rfl) ⟨1106900, by rfl⟩ : syracuseStep 1475867 = 2213801) B2213801
theorem B1967975 : Blo 872567 1967975 := bstep (se 1 (by rfl) ⟨1475981, by rfl⟩ : syracuseStep 1967975 = 2951963) B2951963
theorem B18876887 : Blo 872567 18876887 := bstep (se 1 (by rfl) ⟨14157665, by rfl⟩ : syracuseStep 18876887 = 28315331) B28315331
theorem B1477433 : Blo 872567 1477433 := bstep (se 2 (by rfl) ⟨554037, by rfl⟩ : syracuseStep 1477433 = 1108075) B1108075
theorem B1969289 : Blo 872567 1969289 := bstep (se 2 (by rfl) ⟨738483, by rfl⟩ : syracuseStep 1969289 = 1476967) B1476967
theorem B4428431 : Blo 872567 4428431 := bstep (se 1 (by rfl) ⟨3321323, by rfl⟩ : syracuseStep 4428431 = 6642647) B6642647
theorem B4199131 : Blo 872567 4199131 := bstep (se 1 (by rfl) ⟨3149348, by rfl⟩ : syracuseStep 4199131 = 6298697) B6298697
theorem B4986521 : Blo 872567 4986521 := bstep (se 2 (by rfl) ⟨1869945, by rfl⟩ : syracuseStep 4986521 = 3739891) B3739891
theorem B17078525 : Blo 872567 17078525 := bstep (se 3 (by rfl) ⟨3202223, by rfl⟩ : syracuseStep 17078525 = 6404447) B6404447
theorem B4724999 : Blo 872567 4724999 := bstep (se 1 (by rfl) ⟨3543749, by rfl⟩ : syracuseStep 4724999 = 7087499) B7087499
theorem B2956391 : Blo 872567 2956391 := bstep (se 1 (by rfl) ⟨2217293, by rfl⟩ : syracuseStep 2956391 = 4434587) B4434587
theorem B9445535 : Blo 872567 9445535 := bstep (se 1 (by rfl) ⟨7084151, by rfl⟩ : syracuseStep 9445535 = 14168303) B14168303
theorem B56797757 : Blo 872567 56797757 := bstep (se 3 (by rfl) ⟨10649579, by rfl⟩ : syracuseStep 56797757 = 21299159) B21299159
theorem B19443887 : Blo 872567 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B14924087 : Blo 872567 14924087 := bstep (se 1 (by rfl) ⟨11193065, by rfl⟩ : syracuseStep 14924087 = 22386131) B22386131
theorem B2213203 : Blo 872567 2213203 := bstep (se 1 (by rfl) ⟨1659902, by rfl⟩ : syracuseStep 2213203 = 3319805) B3319805
theorem B3362809 : Blo 872567 3362809 := bstep (se 2 (by rfl) ⟨1261053, by rfl⟩ : syracuseStep 3362809 = 2522107) B2522107
theorem B872699 : Blo 872567 872699 := bstep (se 1 (by rfl) ⟨654524, by rfl⟩ : syracuseStep 872699 = 1309049) B1309049
theorem B1659295 : Blo 872567 1659295 := bstep (se 1 (by rfl) ⟨1244471, by rfl⟩ : syracuseStep 1659295 = 2488943) B2488943
theorem B7460099 : Blo 872567 7460099 := bstep (se 1 (by rfl) ⟨5595074, by rfl⟩ : syracuseStep 7460099 = 11190149) B11190149
theorem B1105255 : Blo 872567 1105255 := bstep (se 1 (by rfl) ⟨828941, by rfl⟩ : syracuseStep 1105255 = 1657883) B1657883
theorem B7467511 : Blo 872567 7467511 := bstep (se 1 (by rfl) ⟨5600633, by rfl⟩ : syracuseStep 7467511 = 11201267) B11201267
theorem B32404643 : Blo 872567 32404643 := bstep (se 1 (by rfl) ⟨24303482, by rfl⟩ : syracuseStep 32404643 = 48606965) B48606965
theorem B9961055 : Blo 872567 9961055 := bstep (se 1 (by rfl) ⟨7470791, by rfl⟩ : syracuseStep 9961055 = 14941583) B14941583
theorem B2359039 : Blo 872567 2359039 := bstep (se 1 (by rfl) ⟨1769279, by rfl⟩ : syracuseStep 2359039 = 3538559) B3538559
theorem B983911 : Blo 872567 983911 := bstep (se 1 (by rfl) ⟨737933, by rfl⟩ : syracuseStep 983911 = 1475867) B1475867
theorem B1180585 : Blo 872567 1180585 := bstep (se 2 (by rfl) ⟨442719, by rfl⟩ : syracuseStep 1180585 = 885439) B885439
theorem B1311983 : Blo 872567 1311983 := bstep (se 1 (by rfl) ⟨983987, by rfl⟩ : syracuseStep 1311983 = 1967975) B1967975
theorem B12584591 : Blo 872567 12584591 := bstep (se 1 (by rfl) ⟨9438443, by rfl⟩ : syracuseStep 12584591 = 18876887) B18876887
theorem B2950937 : Blo 872567 2950937 := bstep (se 2 (by rfl) ⟨1106601, by rfl⟩ : syracuseStep 2950937 = 2213203) B2213203
theorem B984955 : Blo 872567 984955 := bstep (se 1 (by rfl) ⟨738716, by rfl⟩ : syracuseStep 984955 = 1477433) B1477433
theorem B1312859 : Blo 872567 1312859 := bstep (se 1 (by rfl) ⟨984644, by rfl⟩ : syracuseStep 1312859 = 1969289) B1969289
theorem B2952287 : Blo 872567 2952287 := bstep (se 1 (by rfl) ⟨2214215, by rfl⟩ : syracuseStep 2952287 = 4428431) B4428431
theorem B3149999 : Blo 872567 3149999 := bstep (se 1 (by rfl) ⟨2362499, by rfl⟩ : syracuseStep 3149999 = 4724999) B4724999
theorem B1970927 : Blo 872567 1970927 := bstep (se 1 (by rfl) ⟨1478195, by rfl⟩ : syracuseStep 1970927 = 2956391) B2956391
theorem B6297023 : Blo 872567 6297023 := bstep (se 1 (by rfl) ⟨4722767, by rfl⟩ : syracuseStep 6297023 = 9445535) B9445535
theorem B21603095 : Blo 872567 21603095 := bstep (se 1 (by rfl) ⟨16202321, by rfl⟩ : syracuseStep 21603095 = 32404643) B32404643
theorem B2796319 : Blo 872567 2796319 := bstep (se 1 (by rfl) ⟨2097239, by rfl⟩ : syracuseStep 2796319 = 4194479) B4194479
theorem B3324347 : Blo 872567 3324347 := bstep (se 1 (by rfl) ⟨2493260, by rfl⟩ : syracuseStep 3324347 = 4986521) B4986521
theorem B11385683 : Blo 872567 11385683 := bstep (se 1 (by rfl) ⟨8539262, by rfl⟩ : syracuseStep 11385683 = 17078525) B17078525
theorem B2212393 : Blo 872567 2212393 := bstep (se 2 (by rfl) ⟨829647, by rfl⟩ : syracuseStep 2212393 = 1659295) B1659295
theorem B37865171 : Blo 872567 37865171 := bstep (se 1 (by rfl) ⟨28398878, by rfl⟩ : syracuseStep 37865171 = 56797757) B56797757
theorem B12962591 : Blo 872567 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B9949391 : Blo 872567 9949391 := bstep (se 1 (by rfl) ⟨7462043, by rfl⟩ : syracuseStep 9949391 = 14924087) B14924087
theorem B6640703 : Blo 872567 6640703 := bstep (se 1 (by rfl) ⟨4980527, by rfl⟩ : syracuseStep 6640703 = 9961055) B9961055
theorem B4973399 : Blo 872567 4973399 := bstep (se 1 (by rfl) ⟨3730049, by rfl⟩ : syracuseStep 4973399 = 7460099) B7460099
theorem B4483745 : Blo 872567 4483745 := bstep (se 2 (by rfl) ⟨1681404, by rfl⟩ : syracuseStep 4483745 = 3362809) B3362809
theorem B9956681 : Blo 872567 9956681 := bstep (se 2 (by rfl) ⟨3733755, by rfl⟩ : syracuseStep 9956681 = 7467511) B7467511
theorem B5598841 : Blo 872567 5598841 := bstep (se 2 (by rfl) ⟨2099565, by rfl⟩ : syracuseStep 5598841 = 4199131) B4199131
theorem B1473673 : Blo 872567 1473673 := bstep (se 2 (by rfl) ⟨552627, by rfl⟩ : syracuseStep 1473673 = 1105255) B1105255
theorem B3145385 : Blo 872567 3145385 := bstep (se 2 (by rfl) ⟨1179519, by rfl⟩ : syracuseStep 3145385 = 2359039) B2359039
theorem B2949857 : Blo 872567 2949857 := bstep (se 2 (by rfl) ⟨1106196, by rfl⟩ : syracuseStep 2949857 = 2212393) B2212393
theorem B8389727 : Blo 872567 8389727 := bstep (se 1 (by rfl) ⟨6292295, by rfl⟩ : syracuseStep 8389727 = 12584591) B12584591
theorem B1311881 : Blo 872567 1311881 := bstep (se 2 (by rfl) ⟨491955, by rfl⟩ : syracuseStep 1311881 = 983911) B983911
theorem B1967291 : Blo 872567 1967291 := bstep (se 1 (by rfl) ⟨1475468, by rfl⟩ : syracuseStep 1967291 = 2950937) B2950937
theorem B1574113 : Blo 872567 1574113 := bstep (se 2 (by rfl) ⟨590292, by rfl⟩ : syracuseStep 1574113 = 1180585) B1180585
theorem B1968191 : Blo 872567 1968191 := bstep (se 1 (by rfl) ⟨1476143, by rfl⟩ : syracuseStep 1968191 = 2952287) B2952287
theorem B1313273 : Blo 872567 1313273 := bstep (se 2 (by rfl) ⟨492477, by rfl⟩ : syracuseStep 1313273 = 984955) B984955
theorem B2099999 : Blo 872567 2099999 := bstep (se 1 (by rfl) ⟨1574999, by rfl⟩ : syracuseStep 2099999 = 3149999) B3149999
theorem B1313951 : Blo 872567 1313951 := bstep (se 1 (by rfl) ⟨985463, by rfl⟩ : syracuseStep 1313951 = 1970927) B1970927
theorem B4427135 : Blo 872567 4427135 := bstep (se 1 (by rfl) ⟨3320351, by rfl⟩ : syracuseStep 4427135 = 6640703) B6640703
theorem B4198015 : Blo 872567 4198015 := bstep (se 1 (by rfl) ⟨3148511, by rfl⟩ : syracuseStep 4198015 = 6297023) B6297023
theorem B3315599 : Blo 872567 3315599 := bstep (se 1 (by rfl) ⟨2486699, by rfl⟩ : syracuseStep 3315599 = 4973399) B4973399
theorem B2989163 : Blo 872567 2989163 := bstep (se 1 (by rfl) ⟨2241872, by rfl⟩ : syracuseStep 2989163 = 4483745) B4483745
theorem B25243447 : Blo 872567 25243447 := bstep (se 1 (by rfl) ⟨18932585, by rfl⟩ : syracuseStep 25243447 = 37865171) B37865171
theorem B6632927 : Blo 872567 6632927 := bstep (se 1 (by rfl) ⟨4974695, by rfl⟩ : syracuseStep 6632927 = 9949391) B9949391
theorem B14402063 : Blo 872567 14402063 := bstep (se 1 (by rfl) ⟨10801547, by rfl⟩ : syracuseStep 14402063 = 21603095) B21603095
theorem B6637787 : Blo 872567 6637787 := bstep (se 1 (by rfl) ⟨4978340, by rfl⟩ : syracuseStep 6637787 = 9956681) B9956681
theorem B2216231 : Blo 872567 2216231 := bstep (se 1 (by rfl) ⟨1662173, by rfl⟩ : syracuseStep 2216231 = 3324347) B3324347
theorem B7590455 : Blo 872567 7590455 := bstep (se 1 (by rfl) ⟨5692841, by rfl⟩ : syracuseStep 7590455 = 11385683) B11385683
theorem B874655 : Blo 872567 874655 := bstep (se 1 (by rfl) ⟨655991, by rfl⟩ : syracuseStep 874655 = 1311983) B1311983
theorem B875239 : Blo 872567 875239 := bstep (se 1 (by rfl) ⟨656429, by rfl⟩ : syracuseStep 875239 = 1312859) B1312859
theorem B8641727 : Blo 872567 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B3728425 : Blo 872567 3728425 := bstep (se 2 (by rfl) ⟨1398159, by rfl⟩ : syracuseStep 3728425 = 2796319) B2796319
theorem B7465121 : Blo 872567 7465121 := bstep (se 2 (by rfl) ⟨2799420, by rfl⟩ : syracuseStep 7465121 = 5598841) B5598841
theorem B1964897 : Blo 872567 1964897 := bstep (se 2 (by rfl) ⟨736836, by rfl⟩ : syracuseStep 1964897 = 1473673) B1473673
theorem B2096923 : Blo 872567 2096923 := bstep (se 1 (by rfl) ⟨1572692, by rfl⟩ : syracuseStep 2096923 = 3145385) B3145385
theorem B9601375 : Blo 872567 9601375 := bstep (se 1 (by rfl) ⟨7201031, by rfl⟩ : syracuseStep 9601375 = 14402063) B14402063
theorem B1966571 : Blo 872567 1966571 := bstep (se 1 (by rfl) ⟨1474928, by rfl⟩ : syracuseStep 1966571 = 2949857) B2949857
theorem B1311527 : Blo 872567 1311527 := bstep (se 1 (by rfl) ⟨983645, by rfl⟩ : syracuseStep 1311527 = 1967291) B1967291
theorem B1312127 : Blo 872567 1312127 := bstep (se 1 (by rfl) ⟨984095, by rfl⟩ : syracuseStep 1312127 = 1968191) B1968191
theorem B4425191 : Blo 872567 4425191 := bstep (se 1 (by rfl) ⟨3318893, by rfl⟩ : syracuseStep 4425191 = 6637787) B6637787
theorem B2098817 : Blo 872567 2098817 := bstep (se 2 (by rfl) ⟨787056, by rfl⟩ : syracuseStep 2098817 = 1574113) B1574113
theorem B2951423 : Blo 872567 2951423 := bstep (se 1 (by rfl) ⟨2213567, by rfl⟩ : syracuseStep 2951423 = 4427135) B4427135
theorem B1477487 : Blo 872567 1477487 := bstep (se 1 (by rfl) ⟨1108115, by rfl⟩ : syracuseStep 1477487 = 2216231) B2216231
theorem B33657929 : Blo 872567 33657929 := bstep (se 2 (by rfl) ⟨12621723, by rfl⟩ : syracuseStep 33657929 = 25243447) B25243447
theorem B2795897 : Blo 872567 2795897 := bstep (se 2 (by rfl) ⟨1048461, by rfl⟩ : syracuseStep 2795897 = 2096923) B2096923
theorem B5060303 : Blo 872567 5060303 := bstep (se 1 (by rfl) ⟨3795227, by rfl⟩ : syracuseStep 5060303 = 7590455) B7590455
theorem B2210399 : Blo 872567 2210399 := bstep (se 1 (by rfl) ⟨1657799, by rfl⟩ : syracuseStep 2210399 = 3315599) B3315599
theorem B5593151 : Blo 872567 5593151 := bstep (se 1 (by rfl) ⟨4194863, by rfl⟩ : syracuseStep 5593151 = 8389727) B8389727
theorem B874587 : Blo 872567 874587 := bstep (se 1 (by rfl) ⟨655940, by rfl⟩ : syracuseStep 874587 = 1311881) B1311881
theorem B4971233 : Blo 872567 4971233 := bstep (se 2 (by rfl) ⟨1864212, by rfl⟩ : syracuseStep 4971233 = 3728425) B3728425
theorem B875515 : Blo 872567 875515 := bstep (se 1 (by rfl) ⟨656636, by rfl⟩ : syracuseStep 875515 = 1313273) B1313273
theorem B1399999 : Blo 872567 1399999 := bstep (se 1 (by rfl) ⟨1049999, by rfl⟩ : syracuseStep 1399999 = 2099999) B2099999
theorem B875967 : Blo 872567 875967 := bstep (se 1 (by rfl) ⟨656975, by rfl⟩ : syracuseStep 875967 = 1313951) B1313951
theorem B1992775 : Blo 872567 1992775 := bstep (se 1 (by rfl) ⟨1494581, by rfl⟩ : syracuseStep 1992775 = 2989163) B2989163
theorem B5761151 : Blo 872567 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B5597353 : Blo 872567 5597353 := bstep (se 2 (by rfl) ⟨2099007, by rfl⟩ : syracuseStep 5597353 = 4198015) B4198015
theorem B4976747 : Blo 872567 4976747 := bstep (se 1 (by rfl) ⟨3732560, by rfl⟩ : syracuseStep 4976747 = 7465121) B7465121
theorem B4421951 : Blo 872567 4421951 := bstep (se 1 (by rfl) ⟨3316463, by rfl⟩ : syracuseStep 4421951 = 6632927) B6632927
theorem B1309931 : Blo 872567 1309931 := bstep (se 1 (by rfl) ⟨982448, by rfl⟩ : syracuseStep 1309931 = 1964897) B1964897
theorem B1311047 : Blo 872567 1311047 := bstep (se 1 (by rfl) ⟨983285, by rfl⟩ : syracuseStep 1311047 = 1966571) B1966571
theorem B2950127 : Blo 872567 2950127 := bstep (se 1 (by rfl) ⟨2212595, by rfl⟩ : syracuseStep 2950127 = 4425191) B4425191
theorem B1967615 : Blo 872567 1967615 := bstep (se 1 (by rfl) ⟨1475711, by rfl⟩ : syracuseStep 1967615 = 2951423) B2951423
theorem B984991 : Blo 872567 984991 := bstep (se 1 (by rfl) ⟨738743, by rfl⟩ : syracuseStep 984991 = 1477487) B1477487
theorem B2657033 : Blo 872567 2657033 := bstep (se 2 (by rfl) ⟨996387, by rfl⟩ : syracuseStep 2657033 = 1992775) B1992775
theorem B3314155 : Blo 872567 3314155 := bstep (se 1 (by rfl) ⟨2485616, by rfl⟩ : syracuseStep 3314155 = 4971233) B4971233
theorem B3840767 : Blo 872567 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B3317831 : Blo 872567 3317831 := bstep (se 1 (by rfl) ⟨2488373, by rfl⟩ : syracuseStep 3317831 = 4976747) B4976747
theorem B7455725 : Blo 872567 7455725 := bstep (se 3 (by rfl) ⟨1397948, by rfl⟩ : syracuseStep 7455725 = 2795897) B2795897
theorem B873287 : Blo 872567 873287 := bstep (se 1 (by rfl) ⟨654965, by rfl⟩ : syracuseStep 873287 = 1309931) B1309931
theorem B12801833 : Blo 872567 12801833 := bstep (se 2 (by rfl) ⟨4800687, by rfl⟩ : syracuseStep 12801833 = 9601375) B9601375
theorem B874351 : Blo 872567 874351 := bstep (se 1 (by rfl) ⟨655763, by rfl⟩ : syracuseStep 874351 = 1311527) B1311527
theorem B874751 : Blo 872567 874751 := bstep (se 1 (by rfl) ⟨656063, by rfl⟩ : syracuseStep 874751 = 1312127) B1312127
theorem B1399211 : Blo 872567 1399211 := bstep (se 1 (by rfl) ⟨1049408, by rfl⟩ : syracuseStep 1399211 = 2098817) B2098817
theorem B7463137 : Blo 872567 7463137 := bstep (se 2 (by rfl) ⟨2798676, by rfl⟩ : syracuseStep 7463137 = 5597353) B5597353
theorem B22438619 : Blo 872567 22438619 := bstep (se 1 (by rfl) ⟨16828964, by rfl⟩ : syracuseStep 22438619 = 33657929) B33657929
theorem B3728767 : Blo 872567 3728767 := bstep (se 1 (by rfl) ⟨2796575, by rfl⟩ : syracuseStep 3728767 = 5593151) B5593151
theorem B3373535 : Blo 872567 3373535 := bstep (se 1 (by rfl) ⟨2530151, by rfl⟩ : syracuseStep 3373535 = 5060303) B5060303
theorem B2947967 : Blo 872567 2947967 := bstep (se 1 (by rfl) ⟨2210975, by rfl⟩ : syracuseStep 2947967 = 4421951) B4421951
theorem B1866665 : Blo 872567 1866665 := bstep (se 2 (by rfl) ⟨699999, by rfl⟩ : syracuseStep 1866665 = 1399999) B1399999
theorem B1473599 : Blo 872567 1473599 := bstep (se 1 (by rfl) ⟨1105199, by rfl⟩ : syracuseStep 1473599 = 2210399) B2210399
theorem B1966751 : Blo 872567 1966751 := bstep (se 1 (by rfl) ⟨1475063, by rfl⟩ : syracuseStep 1966751 = 2950127) B2950127
theorem B1311743 : Blo 872567 1311743 := bstep (se 1 (by rfl) ⟨983807, by rfl⟩ : syracuseStep 1311743 = 1967615) B1967615
theorem B1771355 : Blo 872567 1771355 := bstep (se 1 (by rfl) ⟨1328516, by rfl⟩ : syracuseStep 1771355 = 2657033) B2657033
theorem B1313321 : Blo 872567 1313321 := bstep (se 2 (by rfl) ⟨492495, by rfl⟩ : syracuseStep 1313321 = 984991) B984991
theorem B2560511 : Blo 872567 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B8534555 : Blo 872567 8534555 := bstep (se 1 (by rfl) ⟨6400916, by rfl⟩ : syracuseStep 8534555 = 12801833) B12801833
theorem B932807 : Blo 872567 932807 := bstep (se 1 (by rfl) ⟨699605, by rfl⟩ : syracuseStep 932807 = 1399211) B1399211
theorem B2211887 : Blo 872567 2211887 := bstep (se 1 (by rfl) ⟨1658915, by rfl⟩ : syracuseStep 2211887 = 3317831) B3317831
theorem B14959079 : Blo 872567 14959079 := bstep (se 1 (by rfl) ⟨11219309, by rfl⟩ : syracuseStep 14959079 = 22438619) B22438619
theorem B8996093 : Blo 872567 8996093 := bstep (se 3 (by rfl) ⟨1686767, by rfl⟩ : syracuseStep 8996093 = 3373535) B3373535
theorem B874031 : Blo 872567 874031 := bstep (se 1 (by rfl) ⟨655523, by rfl⟩ : syracuseStep 874031 = 1311047) B1311047
theorem B9950849 : Blo 872567 9950849 := bstep (se 2 (by rfl) ⟨3731568, by rfl⟩ : syracuseStep 9950849 = 7463137) B7463137
theorem B4970483 : Blo 872567 4970483 := bstep (se 1 (by rfl) ⟨3727862, by rfl⟩ : syracuseStep 4970483 = 7455725) B7455725
theorem B4971689 : Blo 872567 4971689 := bstep (se 2 (by rfl) ⟨1864383, by rfl⟩ : syracuseStep 4971689 = 3728767) B3728767
theorem B4418873 : Blo 872567 4418873 := bstep (se 2 (by rfl) ⟨1657077, by rfl⟩ : syracuseStep 4418873 = 3314155) B3314155
theorem B4977773 : Blo 872567 4977773 := bstep (se 3 (by rfl) ⟨933332, by rfl⟩ : syracuseStep 4977773 = 1866665) B1866665
theorem B1965311 : Blo 872567 1965311 := bstep (se 1 (by rfl) ⟨1473983, by rfl⟩ : syracuseStep 1965311 = 2947967) B2947967
theorem B982399 : Blo 872567 982399 := bstep (se 1 (by rfl) ⟨736799, by rfl⟩ : syracuseStep 982399 = 1473599) B1473599
theorem B1474591 : Blo 872567 1474591 := bstep (se 1 (by rfl) ⟨1105943, by rfl⟩ : syracuseStep 1474591 = 2211887) B2211887
theorem B1311167 : Blo 872567 1311167 := bstep (se 1 (by rfl) ⟨983375, by rfl⟩ : syracuseStep 1311167 = 1966751) B1966751
theorem B5997395 : Blo 872567 5997395 := bstep (se 1 (by rfl) ⟨4498046, by rfl⟩ : syracuseStep 5997395 = 8996093) B8996093
theorem B1707007 : Blo 872567 1707007 := bstep (se 1 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 1707007 = 2560511) B2560511
theorem B3313655 : Blo 872567 3313655 := bstep (se 1 (by rfl) ⟨2485241, by rfl⟩ : syracuseStep 3313655 = 4970483) B4970483
theorem B3314459 : Blo 872567 3314459 := bstep (se 1 (by rfl) ⟨2485844, by rfl⟩ : syracuseStep 3314459 = 4971689) B4971689
theorem B4723613 : Blo 872567 4723613 := bstep (se 3 (by rfl) ⟨885677, by rfl⟩ : syracuseStep 4723613 = 1771355) B1771355
theorem B3318515 : Blo 872567 3318515 := bstep (se 1 (by rfl) ⟨2488886, by rfl⟩ : syracuseStep 3318515 = 4977773) B4977773
theorem B9972719 : Blo 872567 9972719 := bstep (se 1 (by rfl) ⟨7479539, by rfl⟩ : syracuseStep 9972719 = 14959079) B14959079
theorem B6633899 : Blo 872567 6633899 := bstep (se 1 (by rfl) ⟨4975424, by rfl⟩ : syracuseStep 6633899 = 9950849) B9950849
theorem B5689703 : Blo 872567 5689703 := bstep (se 1 (by rfl) ⟨4267277, by rfl⟩ : syracuseStep 5689703 = 8534555) B8534555
theorem B874495 : Blo 872567 874495 := bstep (se 1 (by rfl) ⟨655871, by rfl⟩ : syracuseStep 874495 = 1311743) B1311743
theorem B875547 : Blo 872567 875547 := bstep (se 1 (by rfl) ⟨656660, by rfl⟩ : syracuseStep 875547 = 1313321) B1313321
theorem B2945915 : Blo 872567 2945915 := bstep (se 1 (by rfl) ⟨2209436, by rfl⟩ : syracuseStep 2945915 = 4418873) B4418873
theorem B2487485 : Blo 872567 2487485 := bstep (se 3 (by rfl) ⟨466403, by rfl⟩ : syracuseStep 2487485 = 932807) B932807
theorem B1309865 : Blo 872567 1309865 := bstep (se 2 (by rfl) ⟨491199, by rfl⟩ : syracuseStep 1309865 = 982399) B982399
theorem B1310207 : Blo 872567 1310207 := bstep (se 1 (by rfl) ⟨982655, by rfl⟩ : syracuseStep 1310207 = 1965311) B1965311
theorem B1966121 : Blo 872567 1966121 := bstep (se 2 (by rfl) ⟨737295, by rfl⟩ : syracuseStep 1966121 = 1474591) B1474591
theorem B15172541 : Blo 872567 15172541 := bstep (se 3 (by rfl) ⟨2844851, by rfl⟩ : syracuseStep 15172541 = 5689703) B5689703
theorem B15993053 : Blo 872567 15993053 := bstep (se 3 (by rfl) ⟨2998697, by rfl⟩ : syracuseStep 15993053 = 5997395) B5997395
theorem B3149075 : Blo 872567 3149075 := bstep (se 1 (by rfl) ⟨2361806, by rfl⟩ : syracuseStep 3149075 = 4723613) B4723613
theorem B2209103 : Blo 872567 2209103 := bstep (se 1 (by rfl) ⟨1656827, by rfl⟩ : syracuseStep 2209103 = 3313655) B3313655
theorem B2209639 : Blo 872567 2209639 := bstep (se 1 (by rfl) ⟨1657229, by rfl⟩ : syracuseStep 2209639 = 3314459) B3314459
theorem B2276009 : Blo 872567 2276009 := bstep (se 2 (by rfl) ⟨853503, by rfl⟩ : syracuseStep 2276009 = 1707007) B1707007
theorem B2212343 : Blo 872567 2212343 := bstep (se 1 (by rfl) ⟨1659257, by rfl⟩ : syracuseStep 2212343 = 3318515) B3318515
theorem B1658323 : Blo 872567 1658323 := bstep (se 1 (by rfl) ⟨1243742, by rfl⟩ : syracuseStep 1658323 = 2487485) B2487485
theorem B873243 : Blo 872567 873243 := bstep (se 1 (by rfl) ⟨654932, by rfl⟩ : syracuseStep 873243 = 1309865) B1309865
theorem B873471 : Blo 872567 873471 := bstep (se 1 (by rfl) ⟨655103, by rfl⟩ : syracuseStep 873471 = 1310207) B1310207
theorem B874111 : Blo 872567 874111 := bstep (se 1 (by rfl) ⟨655583, by rfl⟩ : syracuseStep 874111 = 1311167) B1311167
theorem B6648479 : Blo 872567 6648479 := bstep (se 1 (by rfl) ⟨4986359, by rfl⟩ : syracuseStep 6648479 = 9972719) B9972719
theorem B1963943 : Blo 872567 1963943 := bstep (se 1 (by rfl) ⟨1472957, by rfl⟩ : syracuseStep 1963943 = 2945915) B2945915
theorem B4422599 : Blo 872567 4422599 := bstep (se 1 (by rfl) ⟨3316949, by rfl⟩ : syracuseStep 4422599 = 6633899) B6633899
theorem B1310747 : Blo 872567 1310747 := bstep (se 1 (by rfl) ⟨983060, by rfl⟩ : syracuseStep 1310747 = 1966121) B1966121
theorem B1474895 : Blo 872567 1474895 := bstep (se 1 (by rfl) ⟨1106171, by rfl⟩ : syracuseStep 1474895 = 2212343) B2212343
theorem B4432319 : Blo 872567 4432319 := bstep (se 1 (by rfl) ⟨3324239, by rfl⟩ : syracuseStep 4432319 = 6648479) B6648479
theorem B8397533 : Blo 872567 8397533 := bstep (se 3 (by rfl) ⟨1574537, by rfl⟩ : syracuseStep 8397533 = 3149075) B3149075
theorem B1517339 : Blo 872567 1517339 := bstep (se 1 (by rfl) ⟨1138004, by rfl⟩ : syracuseStep 1517339 = 2276009) B2276009
theorem B10662035 : Blo 872567 10662035 := bstep (se 1 (by rfl) ⟨7996526, by rfl⟩ : syracuseStep 10662035 = 15993053) B15993053
theorem B2211097 : Blo 872567 2211097 := bstep (se 2 (by rfl) ⟨829161, by rfl⟩ : syracuseStep 2211097 = 1658323) B1658323
theorem B10115027 : Blo 872567 10115027 := bstep (se 1 (by rfl) ⟨7586270, by rfl⟩ : syracuseStep 10115027 = 15172541) B15172541
theorem B2946185 : Blo 872567 2946185 := bstep (se 2 (by rfl) ⟨1104819, by rfl⟩ : syracuseStep 2946185 = 2209639) B2209639
theorem B1472735 : Blo 872567 1472735 := bstep (se 1 (by rfl) ⟨1104551, by rfl⟩ : syracuseStep 1472735 = 2209103) B2209103
theorem B1309295 : Blo 872567 1309295 := bstep (se 1 (by rfl) ⟨981971, by rfl⟩ : syracuseStep 1309295 = 1963943) B1963943
theorem B2948399 : Blo 872567 2948399 := bstep (se 1 (by rfl) ⟨2211299, by rfl⟩ : syracuseStep 2948399 = 4422599) B4422599
theorem B983263 : Blo 872567 983263 := bstep (se 1 (by rfl) ⟨737447, by rfl⟩ : syracuseStep 983263 = 1474895) B1474895
theorem B2954879 : Blo 872567 2954879 := bstep (se 1 (by rfl) ⟨2216159, by rfl⟩ : syracuseStep 2954879 = 4432319) B4432319
theorem B872863 : Blo 872567 872863 := bstep (se 1 (by rfl) ⟨654647, by rfl⟩ : syracuseStep 872863 = 1309295) B1309295
theorem B873831 : Blo 872567 873831 := bstep (se 1 (by rfl) ⟨655373, by rfl⟩ : syracuseStep 873831 = 1310747) B1310747
theorem B113728373 : Blo 872567 113728373 := bstep (se 5 (by rfl) ⟨5331017, by rfl⟩ : syracuseStep 113728373 = 10662035) B10662035
theorem B6743351 : Blo 872567 6743351 := bstep (se 1 (by rfl) ⟨5057513, by rfl⟩ : syracuseStep 6743351 = 10115027) B10115027
theorem B5598355 : Blo 872567 5598355 := bstep (se 1 (by rfl) ⟨4198766, by rfl⟩ : syracuseStep 5598355 = 8397533) B8397533
theorem B1011559 : Blo 872567 1011559 := bstep (se 1 (by rfl) ⟨758669, by rfl⟩ : syracuseStep 1011559 = 1517339) B1517339
theorem B1964123 : Blo 872567 1964123 := bstep (se 1 (by rfl) ⟨1473092, by rfl⟩ : syracuseStep 1964123 = 2946185) B2946185
theorem B981823 : Blo 872567 981823 := bstep (se 1 (by rfl) ⟨736367, by rfl⟩ : syracuseStep 981823 = 1472735) B1472735
theorem B2948129 : Blo 872567 2948129 := bstep (se 2 (by rfl) ⟨1105548, by rfl⟩ : syracuseStep 2948129 = 2211097) B2211097
theorem B1965599 : Blo 872567 1965599 := bstep (se 1 (by rfl) ⟨1474199, by rfl⟩ : syracuseStep 1965599 = 2948399) B2948399
theorem B1311017 : Blo 872567 1311017 := bstep (se 2 (by rfl) ⟨491631, by rfl⟩ : syracuseStep 1311017 = 983263) B983263
theorem B1969919 : Blo 872567 1969919 := bstep (se 1 (by rfl) ⟨1477439, by rfl⟩ : syracuseStep 1969919 = 2954879) B2954879
theorem B1348745 : Blo 872567 1348745 := bstep (se 2 (by rfl) ⟨505779, by rfl⟩ : syracuseStep 1348745 = 1011559) B1011559
theorem B4495567 : Blo 872567 4495567 := bstep (se 1 (by rfl) ⟨3371675, by rfl⟩ : syracuseStep 4495567 = 6743351) B6743351
theorem B7464473 : Blo 872567 7464473 := bstep (se 2 (by rfl) ⟨2799177, by rfl⟩ : syracuseStep 7464473 = 5598355) B5598355
theorem B75818915 : Blo 872567 75818915 := bstep (se 1 (by rfl) ⟨56864186, by rfl⟩ : syracuseStep 75818915 = 113728373) B113728373
theorem B1309097 : Blo 872567 1309097 := bstep (se 2 (by rfl) ⟨490911, by rfl⟩ : syracuseStep 1309097 = 981823) B981823
theorem B1309415 : Blo 872567 1309415 := bstep (se 1 (by rfl) ⟨982061, by rfl⟩ : syracuseStep 1309415 = 1964123) B1964123
theorem B1965419 : Blo 872567 1965419 := bstep (se 1 (by rfl) ⟨1474064, by rfl⟩ : syracuseStep 1965419 = 2948129) B2948129
theorem B1310399 : Blo 872567 1310399 := bstep (se 1 (by rfl) ⟨982799, by rfl⟩ : syracuseStep 1310399 = 1965599) B1965599
theorem B1313279 : Blo 872567 1313279 := bstep (se 1 (by rfl) ⟨984959, by rfl⟩ : syracuseStep 1313279 = 1969919) B1969919
theorem B50545943 : Blo 872567 50545943 := bstep (se 1 (by rfl) ⟨37909457, by rfl⟩ : syracuseStep 50545943 = 75818915) B75818915
theorem B872731 : Blo 872567 872731 := bstep (se 1 (by rfl) ⟨654548, by rfl⟩ : syracuseStep 872731 = 1309097) B1309097
theorem B872943 : Blo 872567 872943 := bstep (se 1 (by rfl) ⟨654707, by rfl⟩ : syracuseStep 872943 = 1309415) B1309415
theorem B873599 : Blo 872567 873599 := bstep (se 1 (by rfl) ⟨655199, by rfl⟩ : syracuseStep 873599 = 1310399) B1310399
theorem B874011 : Blo 872567 874011 := bstep (se 1 (by rfl) ⟨655508, by rfl⟩ : syracuseStep 874011 = 1311017) B1311017
theorem B3596653 : Blo 872567 3596653 := bstep (se 3 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 3596653 = 1348745) B1348745
theorem B4976315 : Blo 872567 4976315 := bstep (se 1 (by rfl) ⟨3732236, by rfl⟩ : syracuseStep 4976315 = 7464473) B7464473
theorem B5994089 : Blo 872567 5994089 := bstep (se 2 (by rfl) ⟨2247783, by rfl⟩ : syracuseStep 5994089 = 4495567) B4495567
theorem B1310279 : Blo 872567 1310279 := bstep (se 1 (by rfl) ⟨982709, by rfl⟩ : syracuseStep 1310279 = 1965419) B1965419
theorem B3317543 : Blo 872567 3317543 := bstep (se 1 (by rfl) ⟨2488157, by rfl⟩ : syracuseStep 3317543 = 4976315) B4976315
theorem B4795537 : Blo 872567 4795537 := bstep (se 2 (by rfl) ⟨1798326, by rfl⟩ : syracuseStep 4795537 = 3596653) B3596653
theorem B33697295 : Blo 872567 33697295 := bstep (se 1 (by rfl) ⟨25272971, by rfl⟩ : syracuseStep 33697295 = 50545943) B50545943
theorem B873519 : Blo 872567 873519 := bstep (se 1 (by rfl) ⟨655139, by rfl⟩ : syracuseStep 873519 = 1310279) B1310279
theorem B875519 : Blo 872567 875519 := bstep (se 1 (by rfl) ⟨656639, by rfl⟩ : syracuseStep 875519 = 1313279) B1313279
theorem B3996059 : Blo 872567 3996059 := bstep (se 1 (by rfl) ⟨2997044, by rfl⟩ : syracuseStep 3996059 = 5994089) B5994089
theorem B6394049 : Blo 872567 6394049 := bstep (se 2 (by rfl) ⟨2397768, by rfl⟩ : syracuseStep 6394049 = 4795537) B4795537
theorem B10656157 : Blo 872567 10656157 := bstep (se 3 (by rfl) ⟨1998029, by rfl⟩ : syracuseStep 10656157 = 3996059) B3996059
theorem B2211695 : Blo 872567 2211695 := bstep (se 1 (by rfl) ⟨1658771, by rfl⟩ : syracuseStep 2211695 = 3317543) B3317543
theorem B22464863 : Blo 872567 22464863 := bstep (se 1 (by rfl) ⟨16848647, by rfl⟩ : syracuseStep 22464863 = 33697295) B33697295
theorem B14976575 : Blo 872567 14976575 := bstep (se 1 (by rfl) ⟨11232431, by rfl⟩ : syracuseStep 14976575 = 22464863) B22464863
theorem B4262699 : Blo 872567 4262699 := bstep (se 1 (by rfl) ⟨3197024, by rfl⟩ : syracuseStep 4262699 = 6394049) B6394049
theorem B14208209 : Blo 872567 14208209 := bstep (se 2 (by rfl) ⟨5328078, by rfl⟩ : syracuseStep 14208209 = 10656157) B10656157
theorem B1474463 : Blo 872567 1474463 := bstep (se 1 (by rfl) ⟨1105847, by rfl⟩ : syracuseStep 1474463 = 2211695) B2211695
theorem B9472139 : Blo 872567 9472139 := bstep (se 1 (by rfl) ⟨7104104, by rfl⟩ : syracuseStep 9472139 = 14208209) B14208209
theorem B9984383 : Blo 872567 9984383 := bstep (se 1 (by rfl) ⟨7488287, by rfl⟩ : syracuseStep 9984383 = 14976575) B14976575
theorem B2841799 : Blo 872567 2841799 := bstep (se 1 (by rfl) ⟨2131349, by rfl⟩ : syracuseStep 2841799 = 4262699) B4262699
theorem B982975 : Blo 872567 982975 := bstep (se 1 (by rfl) ⟨737231, by rfl⟩ : syracuseStep 982975 = 1474463) B1474463
theorem B6656255 : Blo 872567 6656255 := bstep (se 1 (by rfl) ⟨4992191, by rfl⟩ : syracuseStep 6656255 = 9984383) B9984383
theorem B3789065 : Blo 872567 3789065 := bstep (se 2 (by rfl) ⟨1420899, by rfl⟩ : syracuseStep 3789065 = 2841799) B2841799
theorem B6314759 : Blo 872567 6314759 := bstep (se 1 (by rfl) ⟨4736069, by rfl⟩ : syracuseStep 6314759 = 9472139) B9472139
theorem B1310633 : Blo 872567 1310633 := bstep (se 2 (by rfl) ⟨491487, by rfl⟩ : syracuseStep 1310633 = 982975) B982975
theorem B10104173 : Blo 872567 10104173 := bstep (se 3 (by rfl) ⟨1894532, by rfl⟩ : syracuseStep 10104173 = 3789065) B3789065
theorem B4437503 : Blo 872567 4437503 := bstep (se 1 (by rfl) ⟨3328127, by rfl⟩ : syracuseStep 4437503 = 6656255) B6656255
theorem B4209839 : Blo 872567 4209839 := bstep (se 1 (by rfl) ⟨3157379, by rfl⟩ : syracuseStep 4209839 = 6314759) B6314759
theorem B873755 : Blo 872567 873755 := bstep (se 1 (by rfl) ⟨655316, by rfl⟩ : syracuseStep 873755 = 1310633) B1310633
theorem B2958335 : Blo 872567 2958335 := bstep (se 1 (by rfl) ⟨2218751, by rfl⟩ : syracuseStep 2958335 = 4437503) B4437503
theorem B6736115 : Blo 872567 6736115 := bstep (se 1 (by rfl) ⟨5052086, by rfl⟩ : syracuseStep 6736115 = 10104173) B10104173
theorem B2806559 : Blo 872567 2806559 := bstep (se 1 (by rfl) ⟨2104919, by rfl⟩ : syracuseStep 2806559 = 4209839) B4209839
theorem B4490743 : Blo 872567 4490743 := bstep (se 1 (by rfl) ⟨3368057, by rfl⟩ : syracuseStep 4490743 = 6736115) B6736115
theorem B1871039 : Blo 872567 1871039 := bstep (se 1 (by rfl) ⟨1403279, by rfl⟩ : syracuseStep 1871039 = 2806559) B2806559
theorem B1972223 : Blo 872567 1972223 := bstep (se 1 (by rfl) ⟨1479167, by rfl⟩ : syracuseStep 1972223 = 2958335) B2958335
theorem B1314815 : Blo 872567 1314815 := bstep (se 1 (by rfl) ⟨986111, by rfl⟩ : syracuseStep 1314815 = 1972223) B1972223
theorem B4989437 : Blo 872567 4989437 := bstep (se 3 (by rfl) ⟨935519, by rfl⟩ : syracuseStep 4989437 = 1871039) B1871039
theorem B5987657 : Blo 872567 5987657 := bstep (se 2 (by rfl) ⟨2245371, by rfl⟩ : syracuseStep 5987657 = 4490743) B4490743
theorem B3326291 : Blo 872567 3326291 := bstep (se 1 (by rfl) ⟨2494718, by rfl⟩ : syracuseStep 3326291 = 4989437) B4989437
theorem B876543 : Blo 872567 876543 := bstep (se 1 (by rfl) ⟨657407, by rfl⟩ : syracuseStep 876543 = 1314815) B1314815
theorem B3991771 : Blo 872567 3991771 := bstep (se 1 (by rfl) ⟨2993828, by rfl⟩ : syracuseStep 3991771 = 5987657) B5987657
theorem B5322361 : Blo 872567 5322361 := bstep (se 2 (by rfl) ⟨1995885, by rfl⟩ : syracuseStep 5322361 = 3991771) B3991771
theorem B2217527 : Blo 872567 2217527 := bstep (se 1 (by rfl) ⟨1663145, by rfl⟩ : syracuseStep 2217527 = 3326291) B3326291
theorem B1478351 : Blo 872567 1478351 := bstep (se 1 (by rfl) ⟨1108763, by rfl⟩ : syracuseStep 1478351 = 2217527) B2217527
theorem B7096481 : Blo 872567 7096481 := bstep (se 2 (by rfl) ⟨2661180, by rfl⟩ : syracuseStep 7096481 = 5322361) B5322361
theorem B985567 : Blo 872567 985567 := bstep (se 1 (by rfl) ⟨739175, by rfl⟩ : syracuseStep 985567 = 1478351) B1478351
theorem B4730987 : Blo 872567 4730987 := bstep (se 1 (by rfl) ⟨3548240, by rfl⟩ : syracuseStep 4730987 = 7096481) B7096481
theorem B1314089 : Blo 872567 1314089 := bstep (se 2 (by rfl) ⟨492783, by rfl⟩ : syracuseStep 1314089 = 985567) B985567
theorem B3153991 : Blo 872567 3153991 := bstep (se 1 (by rfl) ⟨2365493, by rfl⟩ : syracuseStep 3153991 = 4730987) B4730987
theorem B4205321 : Blo 872567 4205321 := bstep (se 2 (by rfl) ⟨1576995, by rfl⟩ : syracuseStep 4205321 = 3153991) B3153991
theorem B876059 : Blo 872567 876059 := bstep (se 1 (by rfl) ⟨657044, by rfl⟩ : syracuseStep 876059 = 1314089) B1314089
theorem B2803547 : Blo 872567 2803547 := bstep (se 1 (by rfl) ⟨2102660, by rfl⟩ : syracuseStep 2803547 = 4205321) B4205321
theorem B1869031 : Blo 872567 1869031 := bstep (se 1 (by rfl) ⟨1401773, by rfl⟩ : syracuseStep 1869031 = 2803547) B2803547
theorem B2492041 : Blo 872567 2492041 := bstep (se 2 (by rfl) ⟨934515, by rfl⟩ : syracuseStep 2492041 = 1869031) B1869031
theorem B3322721 : Blo 872567 3322721 := bstep (se 2 (by rfl) ⟨1246020, by rfl⟩ : syracuseStep 3322721 = 2492041) B2492041
theorem B2215147 : Blo 872567 2215147 := bstep (se 1 (by rfl) ⟨1661360, by rfl⟩ : syracuseStep 2215147 = 3322721) B3322721
theorem B2953529 : Blo 872567 2953529 := bstep (se 2 (by rfl) ⟨1107573, by rfl⟩ : syracuseStep 2953529 = 2215147) B2215147
theorem B1969019 : Blo 872567 1969019 := bstep (se 1 (by rfl) ⟨1476764, by rfl⟩ : syracuseStep 1969019 = 2953529) B2953529
theorem B1312679 : Blo 872567 1312679 := bstep (se 1 (by rfl) ⟨984509, by rfl⟩ : syracuseStep 1312679 = 1969019) B1969019
theorem B875119 : Blo 872567 875119 := bstep (se 1 (by rfl) ⟨656339, by rfl⟩ : syracuseStep 875119 = 1312679) B1312679

theorem C0 (j : ℕ) (h1 : 218141 ≤ j) (h2 : j ≤ 218840) : Blo 872567 (4 * j + 3) := by
  interval_cases j
  · exact B872567
  · exact B872571
  · exact B872575
  · exact B872579
  · exact B872583
  · exact B872587
  · exact B872591
  · exact B872595
  · exact B872599
  · exact B872603
  · exact B872607
  · exact B872611
  · exact B872615
  · exact B872619
  · exact B872623
  · exact B872627
  · exact B872631
  · exact B872635
  · exact B872639
  · exact B872643
  · exact B872647
  · exact B872651
  · exact B872655
  · exact B872659
  · exact B872663
  · exact B872667
  · exact B872671
  · exact B872675
  · exact B872679
  · exact B872683
  · exact B872687
  · exact B872691
  · exact B872695
  · exact B872699
  · exact B872703
  · exact B872707
  · exact B872711
  · exact B872715
  · exact B872719
  · exact B872723
  · exact B872727
  · exact B872731
  · exact B872735
  · exact B872739
  · exact B872743
  · exact B872747
  · exact B872751
  · exact B872755
  · exact B872759
  · exact B872763
  · exact B872767
  · exact B872771
  · exact B872775
  · exact B872779
  · exact B872783
  · exact B872787
  · exact B872791
  · exact B872795
  · exact B872799
  · exact B872803
  · exact B872807
  · exact B872811
  · exact B872815
  · exact B872819
  · exact B872823
  · exact B872827
  · exact B872831
  · exact B872835
  · exact B872839
  · exact B872843
  · exact B872847
  · exact B872851
  · exact B872855
  · exact B872859
  · exact B872863
  · exact B872867
  · exact B872871
  · exact B872875
  · exact B872879
  · exact B872883
  · exact B872887
  · exact B872891
  · exact B872895
  · exact B872899
  · exact B872903
  · exact B872907
  · exact B872911
  · exact B872915
  · exact B872919
  · exact B872923
  · exact B872927
  · exact B872931
  · exact B872935
  · exact B872939
  · exact B872943
  · exact B872947
  · exact B872951
  · exact B872955
  · exact B872959
  · exact B872963
  · exact B872967
  · exact B872971
  · exact B872975
  · exact B872979
  · exact B872983
  · exact B872987
  · exact B872991
  · exact B872995
  · exact B872999
  · exact B873003
  · exact B873007
  · exact B873011
  · exact B873015
  · exact B873019
  · exact B873023
  · exact B873027
  · exact B873031
  · exact B873035
  · exact B873039
  · exact B873043
  · exact B873047
  · exact B873051
  · exact B873055
  · exact B873059
  · exact B873063
  · exact B873067
  · exact B873071
  · exact B873075
  · exact B873079
  · exact B873083
  · exact B873087
  · exact B873091
  · exact B873095
  · exact B873099
  · exact B873103
  · exact B873107
  · exact B873111
  · exact B873115
  · exact B873119
  · exact B873123
  · exact B873127
  · exact B873131
  · exact B873135
  · exact B873139
  · exact B873143
  · exact B873147
  · exact B873151
  · exact B873155
  · exact B873159
  · exact B873163
  · exact B873167
  · exact B873171
  · exact B873175
  · exact B873179
  · exact B873183
  · exact B873187
  · exact B873191
  · exact B873195
  · exact B873199
  · exact B873203
  · exact B873207
  · exact B873211
  · exact B873215
  · exact B873219
  · exact B873223
  · exact B873227
  · exact B873231
  · exact B873235
  · exact B873239
  · exact B873243
  · exact B873247
  · exact B873251
  · exact B873255
  · exact B873259
  · exact B873263
  · exact B873267
  · exact B873271
  · exact B873275
  · exact B873279
  · exact B873283
  · exact B873287
  · exact B873291
  · exact B873295
  · exact B873299
  · exact B873303
  · exact B873307
  · exact B873311
  · exact B873315
  · exact B873319
  · exact B873323
  · exact B873327
  · exact B873331
  · exact B873335
  · exact B873339
  · exact B873343
  · exact B873347
  · exact B873351
  · exact B873355
  · exact B873359
  · exact B873363
  · exact B873367
  · exact B873371
  · exact B873375
  · exact B873379
  · exact B873383
  · exact B873387
  · exact B873391
  · exact B873395
  · exact B873399
  · exact B873403
  · exact B873407
  · exact B873411
  · exact B873415
  · exact B873419
  · exact B873423
  · exact B873427
  · exact B873431
  · exact B873435
  · exact B873439
  · exact B873443
  · exact B873447
  · exact B873451
  · exact B873455
  · exact B873459
  · exact B873463
  · exact B873467
  · exact B873471
  · exact B873475
  · exact B873479
  · exact B873483
  · exact B873487
  · exact B873491
  · exact B873495
  · exact B873499
  · exact B873503
  · exact B873507
  · exact B873511
  · exact B873515
  · exact B873519
  · exact B873523
  · exact B873527
  · exact B873531
  · exact B873535
  · exact B873539
  · exact B873543
  · exact B873547
  · exact B873551
  · exact B873555
  · exact B873559
  · exact B873563
  · exact B873567
  · exact B873571
  · exact B873575
  · exact B873579
  · exact B873583
  · exact B873587
  · exact B873591
  · exact B873595
  · exact B873599
  · exact B873603
  · exact B873607
  · exact B873611
  · exact B873615
  · exact B873619
  · exact B873623
  · exact B873627
  · exact B873631
  · exact B873635
  · exact B873639
  · exact B873643
  · exact B873647
  · exact B873651
  · exact B873655
  · exact B873659
  · exact B873663
  · exact B873667
  · exact B873671
  · exact B873675
  · exact B873679
  · exact B873683
  · exact B873687
  · exact B873691
  · exact B873695
  · exact B873699
  · exact B873703
  · exact B873707
  · exact B873711
  · exact B873715
  · exact B873719
  · exact B873723
  · exact B873727
  · exact B873731
  · exact B873735
  · exact B873739
  · exact B873743
  · exact B873747
  · exact B873751
  · exact B873755
  · exact B873759
  · exact B873763
  · exact B873767
  · exact B873771
  · exact B873775
  · exact B873779
  · exact B873783
  · exact B873787
  · exact B873791
  · exact B873795
  · exact B873799
  · exact B873803
  · exact B873807
  · exact B873811
  · exact B873815
  · exact B873819
  · exact B873823
  · exact B873827
  · exact B873831
  · exact B873835
  · exact B873839
  · exact B873843
  · exact B873847
  · exact B873851
  · exact B873855
  · exact B873859
  · exact B873863
  · exact B873867
  · exact B873871
  · exact B873875
  · exact B873879
  · exact B873883
  · exact B873887
  · exact B873891
  · exact B873895
  · exact B873899
  · exact B873903
  · exact B873907
  · exact B873911
  · exact B873915
  · exact B873919
  · exact B873923
  · exact B873927
  · exact B873931
  · exact B873935
  · exact B873939
  · exact B873943
  · exact B873947
  · exact B873951
  · exact B873955
  · exact B873959
  · exact B873963
  · exact B873967
  · exact B873971
  · exact B873975
  · exact B873979
  · exact B873983
  · exact B873987
  · exact B873991
  · exact B873995
  · exact B873999
  · exact B874003
  · exact B874007
  · exact B874011
  · exact B874015
  · exact B874019
  · exact B874023
  · exact B874027
  · exact B874031
  · exact B874035
  · exact B874039
  · exact B874043
  · exact B874047
  · exact B874051
  · exact B874055
  · exact B874059
  · exact B874063
  · exact B874067
  · exact B874071
  · exact B874075
  · exact B874079
  · exact B874083
  · exact B874087
  · exact B874091
  · exact B874095
  · exact B874099
  · exact B874103
  · exact B874107
  · exact B874111
  · exact B874115
  · exact B874119
  · exact B874123
  · exact B874127
  · exact B874131
  · exact B874135
  · exact B874139
  · exact B874143
  · exact B874147
  · exact B874151
  · exact B874155
  · exact B874159
  · exact B874163
  · exact B874167
  · exact B874171
  · exact B874175
  · exact B874179
  · exact B874183
  · exact B874187
  · exact B874191
  · exact B874195
  · exact B874199
  · exact B874203
  · exact B874207
  · exact B874211
  · exact B874215
  · exact B874219
  · exact B874223
  · exact B874227
  · exact B874231
  · exact B874235
  · exact B874239
  · exact B874243
  · exact B874247
  · exact B874251
  · exact B874255
  · exact B874259
  · exact B874263
  · exact B874267
  · exact B874271
  · exact B874275
  · exact B874279
  · exact B874283
  · exact B874287
  · exact B874291
  · exact B874295
  · exact B874299
  · exact B874303
  · exact B874307
  · exact B874311
  · exact B874315
  · exact B874319
  · exact B874323
  · exact B874327
  · exact B874331
  · exact B874335
  · exact B874339
  · exact B874343
  · exact B874347
  · exact B874351
  · exact B874355
  · exact B874359
  · exact B874363
  · exact B874367
  · exact B874371
  · exact B874375
  · exact B874379
  · exact B874383
  · exact B874387
  · exact B874391
  · exact B874395
  · exact B874399
  · exact B874403
  · exact B874407
  · exact B874411
  · exact B874415
  · exact B874419
  · exact B874423
  · exact B874427
  · exact B874431
  · exact B874435
  · exact B874439
  · exact B874443
  · exact B874447
  · exact B874451
  · exact B874455
  · exact B874459
  · exact B874463
  · exact B874467
  · exact B874471
  · exact B874475
  · exact B874479
  · exact B874483
  · exact B874487
  · exact B874491
  · exact B874495
  · exact B874499
  · exact B874503
  · exact B874507
  · exact B874511
  · exact B874515
  · exact B874519
  · exact B874523
  · exact B874527
  · exact B874531
  · exact B874535
  · exact B874539
  · exact B874543
  · exact B874547
  · exact B874551
  · exact B874555
  · exact B874559
  · exact B874563
  · exact B874567
  · exact B874571
  · exact B874575
  · exact B874579
  · exact B874583
  · exact B874587
  · exact B874591
  · exact B874595
  · exact B874599
  · exact B874603
  · exact B874607
  · exact B874611
  · exact B874615
  · exact B874619
  · exact B874623
  · exact B874627
  · exact B874631
  · exact B874635
  · exact B874639
  · exact B874643
  · exact B874647
  · exact B874651
  · exact B874655
  · exact B874659
  · exact B874663
  · exact B874667
  · exact B874671
  · exact B874675
  · exact B874679
  · exact B874683
  · exact B874687
  · exact B874691
  · exact B874695
  · exact B874699
  · exact B874703
  · exact B874707
  · exact B874711
  · exact B874715
  · exact B874719
  · exact B874723
  · exact B874727
  · exact B874731
  · exact B874735
  · exact B874739
  · exact B874743
  · exact B874747
  · exact B874751
  · exact B874755
  · exact B874759
  · exact B874763
  · exact B874767
  · exact B874771
  · exact B874775
  · exact B874779
  · exact B874783
  · exact B874787
  · exact B874791
  · exact B874795
  · exact B874799
  · exact B874803
  · exact B874807
  · exact B874811
  · exact B874815
  · exact B874819
  · exact B874823
  · exact B874827
  · exact B874831
  · exact B874835
  · exact B874839
  · exact B874843
  · exact B874847
  · exact B874851
  · exact B874855
  · exact B874859
  · exact B874863
  · exact B874867
  · exact B874871
  · exact B874875
  · exact B874879
  · exact B874883
  · exact B874887
  · exact B874891
  · exact B874895
  · exact B874899
  · exact B874903
  · exact B874907
  · exact B874911
  · exact B874915
  · exact B874919
  · exact B874923
  · exact B874927
  · exact B874931
  · exact B874935
  · exact B874939
  · exact B874943
  · exact B874947
  · exact B874951
  · exact B874955
  · exact B874959
  · exact B874963
  · exact B874967
  · exact B874971
  · exact B874975
  · exact B874979
  · exact B874983
  · exact B874987
  · exact B874991
  · exact B874995
  · exact B874999
  · exact B875003
  · exact B875007
  · exact B875011
  · exact B875015
  · exact B875019
  · exact B875023
  · exact B875027
  · exact B875031
  · exact B875035
  · exact B875039
  · exact B875043
  · exact B875047
  · exact B875051
  · exact B875055
  · exact B875059
  · exact B875063
  · exact B875067
  · exact B875071
  · exact B875075
  · exact B875079
  · exact B875083
  · exact B875087
  · exact B875091
  · exact B875095
  · exact B875099
  · exact B875103
  · exact B875107
  · exact B875111
  · exact B875115
  · exact B875119
  · exact B875123
  · exact B875127
  · exact B875131
  · exact B875135
  · exact B875139
  · exact B875143
  · exact B875147
  · exact B875151
  · exact B875155
  · exact B875159
  · exact B875163
  · exact B875167
  · exact B875171
  · exact B875175
  · exact B875179
  · exact B875183
  · exact B875187
  · exact B875191
  · exact B875195
  · exact B875199
  · exact B875203
  · exact B875207
  · exact B875211
  · exact B875215
  · exact B875219
  · exact B875223
  · exact B875227
  · exact B875231
  · exact B875235
  · exact B875239
  · exact B875243
  · exact B875247
  · exact B875251
  · exact B875255
  · exact B875259
  · exact B875263
  · exact B875267
  · exact B875271
  · exact B875275
  · exact B875279
  · exact B875283
  · exact B875287
  · exact B875291
  · exact B875295
  · exact B875299
  · exact B875303
  · exact B875307
  · exact B875311
  · exact B875315
  · exact B875319
  · exact B875323
  · exact B875327
  · exact B875331
  · exact B875335
  · exact B875339
  · exact B875343
  · exact B875347
  · exact B875351
  · exact B875355
  · exact B875359
  · exact B875363

theorem C1 (j : ℕ) (h1 : 218841 ≤ j) (h2 : j ≤ 219141) : Blo 872567 (4 * j + 3) := by
  interval_cases j
  · exact B875367
  · exact B875371
  · exact B875375
  · exact B875379
  · exact B875383
  · exact B875387
  · exact B875391
  · exact B875395
  · exact B875399
  · exact B875403
  · exact B875407
  · exact B875411
  · exact B875415
  · exact B875419
  · exact B875423
  · exact B875427
  · exact B875431
  · exact B875435
  · exact B875439
  · exact B875443
  · exact B875447
  · exact B875451
  · exact B875455
  · exact B875459
  · exact B875463
  · exact B875467
  · exact B875471
  · exact B875475
  · exact B875479
  · exact B875483
  · exact B875487
  · exact B875491
  · exact B875495
  · exact B875499
  · exact B875503
  · exact B875507
  · exact B875511
  · exact B875515
  · exact B875519
  · exact B875523
  · exact B875527
  · exact B875531
  · exact B875535
  · exact B875539
  · exact B875543
  · exact B875547
  · exact B875551
  · exact B875555
  · exact B875559
  · exact B875563
  · exact B875567
  · exact B875571
  · exact B875575
  · exact B875579
  · exact B875583
  · exact B875587
  · exact B875591
  · exact B875595
  · exact B875599
  · exact B875603
  · exact B875607
  · exact B875611
  · exact B875615
  · exact B875619
  · exact B875623
  · exact B875627
  · exact B875631
  · exact B875635
  · exact B875639
  · exact B875643
  · exact B875647
  · exact B875651
  · exact B875655
  · exact B875659
  · exact B875663
  · exact B875667
  · exact B875671
  · exact B875675
  · exact B875679
  · exact B875683
  · exact B875687
  · exact B875691
  · exact B875695
  · exact B875699
  · exact B875703
  · exact B875707
  · exact B875711
  · exact B875715
  · exact B875719
  · exact B875723
  · exact B875727
  · exact B875731
  · exact B875735
  · exact B875739
  · exact B875743
  · exact B875747
  · exact B875751
  · exact B875755
  · exact B875759
  · exact B875763
  · exact B875767
  · exact B875771
  · exact B875775
  · exact B875779
  · exact B875783
  · exact B875787
  · exact B875791
  · exact B875795
  · exact B875799
  · exact B875803
  · exact B875807
  · exact B875811
  · exact B875815
  · exact B875819
  · exact B875823
  · exact B875827
  · exact B875831
  · exact B875835
  · exact B875839
  · exact B875843
  · exact B875847
  · exact B875851
  · exact B875855
  · exact B875859
  · exact B875863
  · exact B875867
  · exact B875871
  · exact B875875
  · exact B875879
  · exact B875883
  · exact B875887
  · exact B875891
  · exact B875895
  · exact B875899
  · exact B875903
  · exact B875907
  · exact B875911
  · exact B875915
  · exact B875919
  · exact B875923
  · exact B875927
  · exact B875931
  · exact B875935
  · exact B875939
  · exact B875943
  · exact B875947
  · exact B875951
  · exact B875955
  · exact B875959
  · exact B875963
  · exact B875967
  · exact B875971
  · exact B875975
  · exact B875979
  · exact B875983
  · exact B875987
  · exact B875991
  · exact B875995
  · exact B875999
  · exact B876003
  · exact B876007
  · exact B876011
  · exact B876015
  · exact B876019
  · exact B876023
  · exact B876027
  · exact B876031
  · exact B876035
  · exact B876039
  · exact B876043
  · exact B876047
  · exact B876051
  · exact B876055
  · exact B876059
  · exact B876063
  · exact B876067
  · exact B876071
  · exact B876075
  · exact B876079
  · exact B876083
  · exact B876087
  · exact B876091
  · exact B876095
  · exact B876099
  · exact B876103
  · exact B876107
  · exact B876111
  · exact B876115
  · exact B876119
  · exact B876123
  · exact B876127
  · exact B876131
  · exact B876135
  · exact B876139
  · exact B876143
  · exact B876147
  · exact B876151
  · exact B876155
  · exact B876159
  · exact B876163
  · exact B876167
  · exact B876171
  · exact B876175
  · exact B876179
  · exact B876183
  · exact B876187
  · exact B876191
  · exact B876195
  · exact B876199
  · exact B876203
  · exact B876207
  · exact B876211
  · exact B876215
  · exact B876219
  · exact B876223
  · exact B876227
  · exact B876231
  · exact B876235
  · exact B876239
  · exact B876243
  · exact B876247
  · exact B876251
  · exact B876255
  · exact B876259
  · exact B876263
  · exact B876267
  · exact B876271
  · exact B876275
  · exact B876279
  · exact B876283
  · exact B876287
  · exact B876291
  · exact B876295
  · exact B876299
  · exact B876303
  · exact B876307
  · exact B876311
  · exact B876315
  · exact B876319
  · exact B876323
  · exact B876327
  · exact B876331
  · exact B876335
  · exact B876339
  · exact B876343
  · exact B876347
  · exact B876351
  · exact B876355
  · exact B876359
  · exact B876363
  · exact B876367
  · exact B876371
  · exact B876375
  · exact B876379
  · exact B876383
  · exact B876387
  · exact B876391
  · exact B876395
  · exact B876399
  · exact B876403
  · exact B876407
  · exact B876411
  · exact B876415
  · exact B876419
  · exact B876423
  · exact B876427
  · exact B876431
  · exact B876435
  · exact B876439
  · exact B876443
  · exact B876447
  · exact B876451
  · exact B876455
  · exact B876459
  · exact B876463
  · exact B876467
  · exact B876471
  · exact B876475
  · exact B876479
  · exact B876483
  · exact B876487
  · exact B876491
  · exact B876495
  · exact B876499
  · exact B876503
  · exact B876507
  · exact B876511
  · exact B876515
  · exact B876519
  · exact B876523
  · exact B876527
  · exact B876531
  · exact B876535
  · exact B876539
  · exact B876543
  · exact B876547
  · exact B876551
  · exact B876555
  · exact B876559
  · exact B876563
  · exact B876567

theorem solution (m : ℕ) (hlo : 872567 ≤ m) (hhi : m ≤ 876567) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 218141 ≤ j := by omega
    have hj2 : j ≤ 219141 := by omega
    have hb : Blo 872567 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 218841 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
