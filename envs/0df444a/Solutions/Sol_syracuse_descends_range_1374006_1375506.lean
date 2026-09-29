-- Prove2me | solution 1 for syracuse_descends_range_1374006_1375506
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:13:01.066731+00:00
-- url     : https://prove2.me/submissions/57b213a0-88c7-40c7-969b-66efe298ff7e

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


theorem B3481613 : Blo 1374006 3481613 := bbase (se 3 (by rfl) ⟨652802, by rfl⟩ : syracuseStep 3481613 = 1305605) (by norm_num)
theorem B2293805 : Blo 1374006 2293805 := bbase (se 3 (by rfl) ⟨430088, by rfl⟩ : syracuseStep 2293805 = 860177) (by norm_num)
theorem B1589317 : Blo 1374006 1589317 := bbase (se 4 (by rfl) ⟨148998, by rfl⟩ : syracuseStep 1589317 = 297997) (by norm_num)
theorem B2351381 : Blo 1374006 2351381 := bbase (se 6 (by rfl) ⟨55110, by rfl⟩ : syracuseStep 2351381 = 110221) (by norm_num)
theorem B7831829 : Blo 1374006 7831829 := bbase (se 6 (by rfl) ⟨183558, by rfl⟩ : syracuseStep 7831829 = 367117) (by norm_num)
theorem B2318645 : Blo 1374006 2318645 := bbase (se 5 (by rfl) ⟨108686, by rfl⟩ : syracuseStep 2318645 = 217373) (by norm_num)
theorem B1958197 : Blo 1374006 1958197 := bbase (se 5 (by rfl) ⟨91790, by rfl⟩ : syracuseStep 1958197 = 183581) (by norm_num)
theorem B2318773 : Blo 1374006 2318773 := bbase (se 5 (by rfl) ⟨108692, by rfl⟩ : syracuseStep 2318773 = 217385) (by norm_num)
theorem B14107061 : Blo 1374006 14107061 := bbase (se 5 (by rfl) ⟨661268, by rfl⟩ : syracuseStep 14107061 = 1322537) (by norm_num)
theorem B5218789 : Blo 1374006 5218789 := bbase (se 4 (by rfl) ⟨489261, by rfl⟩ : syracuseStep 5218789 = 978523) (by norm_num)
theorem B2318861 : Blo 1374006 2318861 := bbase (se 3 (by rfl) ⟨434786, by rfl⟩ : syracuseStep 2318861 = 869573) (by norm_num)
theorem B3301901 : Blo 1374006 3301901 := bbase (se 3 (by rfl) ⟨619106, by rfl⟩ : syracuseStep 3301901 = 1238213) (by norm_num)
theorem B1958413 : Blo 1374006 1958413 := bbase (se 3 (by rfl) ⟨367202, by rfl⟩ : syracuseStep 1958413 = 734405) (by norm_num)
theorem B3916325 : Blo 1374006 3916325 := bbase (se 4 (by rfl) ⟨367155, by rfl⟩ : syracuseStep 3916325 = 734311) (by norm_num)
theorem B2318989 : Blo 1374006 2318989 := bbase (se 3 (by rfl) ⟨434810, by rfl⟩ : syracuseStep 2318989 = 869621) (by norm_num)
theorem B26411669 : Blo 1374006 26411669 := bbase (se 6 (by rfl) ⟨619023, by rfl⟩ : syracuseStep 26411669 = 1238047) (by norm_num)
theorem B3302093 : Blo 1374006 3302093 := bbase (se 3 (by rfl) ⟨619142, by rfl⟩ : syracuseStep 3302093 = 1238285) (by norm_num)
theorem B1696465 : Blo 1374006 1696465 := bbase (se 2 (by rfl) ⟨636174, by rfl⟩ : syracuseStep 1696465 = 1272349) (by norm_num)
theorem B2319077 : Blo 1374006 2319077 := bbase (se 4 (by rfl) ⟨217413, by rfl⟩ : syracuseStep 2319077 = 434827) (by norm_num)
theorem B5219093 : Blo 1374006 5219093 := bbase (se 6 (by rfl) ⟨122322, by rfl⟩ : syracuseStep 5219093 = 244645) (by norm_num)
theorem B2319205 : Blo 1374006 2319205 := bbase (se 4 (by rfl) ⟨217425, by rfl⟩ : syracuseStep 2319205 = 434851) (by norm_num)
theorem B4637573 : Blo 1374006 4637573 := bbase (se 4 (by rfl) ⟨434772, by rfl⟩ : syracuseStep 4637573 = 869545) (by norm_num)
theorem B1467281 : Blo 1374006 1467281 := bbase (se 2 (by rfl) ⟨550230, by rfl⟩ : syracuseStep 1467281 = 1100461) (by norm_num)
theorem B2319293 : Blo 1374006 2319293 := bbase (se 3 (by rfl) ⟨434867, by rfl⟩ : syracuseStep 2319293 = 869735) (by norm_num)
theorem B5874677 : Blo 1374006 5874677 := bbase (se 5 (by rfl) ⟨275375, by rfl⟩ : syracuseStep 5874677 = 550751) (by norm_num)
theorem B2319421 : Blo 1374006 2319421 := bbase (se 3 (by rfl) ⟨434891, by rfl⟩ : syracuseStep 2319421 = 869783) (by norm_num)
theorem B6956117 : Blo 1374006 6956117 := bbase (se 8 (by rfl) ⟨40758, by rfl⟩ : syracuseStep 6956117 = 81517) (by norm_num)
theorem B2319509 : Blo 1374006 2319509 := bbase (se 6 (by rfl) ⟨54363, by rfl⟩ : syracuseStep 2319509 = 108727) (by norm_num)
theorem B2352341 : Blo 1374006 2352341 := bbase (se 7 (by rfl) ⟨27566, by rfl⟩ : syracuseStep 2352341 = 55133) (by norm_num)
theorem B2319637 : Blo 1374006 2319637 := bbase (se 6 (by rfl) ⟨54366, by rfl⟩ : syracuseStep 2319637 = 108733) (by norm_num)
theorem B4638005 : Blo 1374006 4638005 := bbase (se 5 (by rfl) ⟨217406, by rfl⟩ : syracuseStep 4638005 = 434813) (by norm_num)
theorem B1467725 : Blo 1374006 1467725 := bbase (se 3 (by rfl) ⟨275198, by rfl⟩ : syracuseStep 1467725 = 550397) (by norm_num)
theorem B2786645 : Blo 1374006 2786645 := bbase (se 12 (by rfl) ⟨1020, by rfl⟩ : syracuseStep 2786645 = 2041) (by norm_num)
theorem B2319725 : Blo 1374006 2319725 := bbase (se 3 (by rfl) ⟨434948, by rfl⟩ : syracuseStep 2319725 = 869897) (by norm_num)
theorem B6694373 : Blo 1374006 6694373 := bbase (se 4 (by rfl) ⟨627597, by rfl⟩ : syracuseStep 6694373 = 1255195) (by norm_num)
theorem B2319853 : Blo 1374006 2319853 := bbase (se 3 (by rfl) ⟨434972, by rfl⟩ : syracuseStep 2319853 = 869945) (by norm_num)
theorem B1467973 : Blo 1374006 1467973 := bbase (se 4 (by rfl) ⟨137622, by rfl⟩ : syracuseStep 1467973 = 275245) (by norm_num)
theorem B2319941 : Blo 1374006 2319941 := bbase (se 4 (by rfl) ⟨217494, by rfl⟩ : syracuseStep 2319941 = 434989) (by norm_num)
theorem B1762961 : Blo 1374006 1762961 := bbase (se 2 (by rfl) ⟨661110, by rfl⟩ : syracuseStep 1762961 = 1322221) (by norm_num)
theorem B9914005 : Blo 1374006 9914005 := bbase (se 6 (by rfl) ⟨232359, by rfl⟩ : syracuseStep 9914005 = 464719) (by norm_num)
theorem B2320069 : Blo 1374006 2320069 := bbase (se 4 (by rfl) ⟨217506, by rfl⟩ : syracuseStep 2320069 = 435013) (by norm_num)
theorem B2090701 : Blo 1374006 2090701 := bbase (se 3 (by rfl) ⟨392006, by rfl⟩ : syracuseStep 2090701 = 784013) (by norm_num)
theorem B4638437 : Blo 1374006 4638437 := bbase (se 4 (by rfl) ⟨434853, by rfl⟩ : syracuseStep 4638437 = 869707) (by norm_num)
theorem B2320157 : Blo 1374006 2320157 := bbase (se 3 (by rfl) ⟨435029, by rfl⟩ : syracuseStep 2320157 = 870059) (by norm_num)
theorem B2934605 : Blo 1374006 2934605 := bbase (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) (by norm_num)
theorem B1812325 : Blo 1374006 1812325 := bbase (se 4 (by rfl) ⟨169905, by rfl⟩ : syracuseStep 1812325 = 339811) (by norm_num)
theorem B4179845 : Blo 1374006 4179845 := bbase (se 4 (by rfl) ⟨391860, by rfl⟩ : syracuseStep 4179845 = 783721) (by norm_num)
theorem B2320285 : Blo 1374006 2320285 := bbase (se 3 (by rfl) ⟨435053, by rfl⟩ : syracuseStep 2320285 = 870107) (by norm_num)
theorem B2787269 : Blo 1374006 2787269 := bbase (se 4 (by rfl) ⟨261306, by rfl⟩ : syracuseStep 2787269 = 522613) (by norm_num)
theorem B2934749 : Blo 1374006 2934749 := bbase (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) (by norm_num)
theorem B2320373 : Blo 1374006 2320373 := bbase (se 5 (by rfl) ⟨108767, by rfl⟩ : syracuseStep 2320373 = 217535) (by norm_num)
theorem B1468417 : Blo 1374006 1468417 := bbase (se 2 (by rfl) ⟨550656, by rfl⟩ : syracuseStep 1468417 = 1101313) (by norm_num)
theorem B4769813 : Blo 1374006 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B1468477 : Blo 1374006 1468477 := bbase (se 3 (by rfl) ⟨275339, by rfl⟩ : syracuseStep 1468477 = 550679) (by norm_num)
theorem B2476109 : Blo 1374006 2476109 := bbase (se 3 (by rfl) ⟨464270, by rfl⟩ : syracuseStep 2476109 = 928541) (by norm_num)
theorem B2320501 : Blo 1374006 2320501 := bbase (se 5 (by rfl) ⟨108773, by rfl⟩ : syracuseStep 2320501 = 217547) (by norm_num)
theorem B7940213 : Blo 1374006 7940213 := bbase (se 5 (by rfl) ⟨372197, by rfl⟩ : syracuseStep 7940213 = 744395) (by norm_num)
theorem B4638869 : Blo 1374006 4638869 := bbase (se 6 (by rfl) ⟨108723, by rfl⟩ : syracuseStep 4638869 = 217447) (by norm_num)
theorem B2320589 : Blo 1374006 2320589 := bbase (se 3 (by rfl) ⟨435110, by rfl⟩ : syracuseStep 2320589 = 870221) (by norm_num)
theorem B2476253 : Blo 1374006 2476253 := bbase (se 3 (by rfl) ⟨464297, by rfl⟩ : syracuseStep 2476253 = 928595) (by norm_num)
theorem B3303661 : Blo 1374006 3303661 := bbase (se 3 (by rfl) ⟨619436, by rfl⟩ : syracuseStep 3303661 = 1238873) (by norm_num)
theorem B5572853 : Blo 1374006 5572853 := bbase (se 5 (by rfl) ⟨261227, by rfl⟩ : syracuseStep 5572853 = 522455) (by norm_num)
theorem B1739009 : Blo 1374006 1739009 := bbase (se 2 (by rfl) ⟨652128, by rfl⟩ : syracuseStep 1739009 = 1304257) (by norm_num)
theorem B1566977 : Blo 1374006 1566977 := bbase (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) (by norm_num)
theorem B1739065 : Blo 1374006 1739065 := bbase (se 2 (by rfl) ⟨652149, by rfl⟩ : syracuseStep 1739065 = 1304299) (by norm_num)
theorem B2935109 : Blo 1374006 2935109 := bbase (se 4 (by rfl) ⟨275166, by rfl⟩ : syracuseStep 2935109 = 550333) (by norm_num)
theorem B2320717 : Blo 1374006 2320717 := bbase (se 3 (by rfl) ⟨435134, by rfl⟩ : syracuseStep 2320717 = 870269) (by norm_num)
theorem B44607829 : Blo 1374006 44607829 := bbase (se 10 (by rfl) ⟨65343, by rfl⟩ : syracuseStep 44607829 = 130687) (by norm_num)
theorem B6957413 : Blo 1374006 6957413 := bbase (se 4 (by rfl) ⟨652257, by rfl⟩ : syracuseStep 6957413 = 1304515) (by norm_num)
theorem B1468793 : Blo 1374006 1468793 := bbase (se 2 (by rfl) ⟨550797, by rfl⟩ : syracuseStep 1468793 = 1101595) (by norm_num)
theorem B1739161 : Blo 1374006 1739161 := bbase (se 2 (by rfl) ⟨652185, by rfl⟩ : syracuseStep 1739161 = 1304371) (by norm_num)
theorem B2320805 : Blo 1374006 2320805 := bbase (se 4 (by rfl) ⟨217575, by rfl⟩ : syracuseStep 2320805 = 435151) (by norm_num)
theorem B1763753 : Blo 1374006 1763753 := bbase (se 2 (by rfl) ⟨661407, by rfl⟩ : syracuseStep 1763753 = 1322815) (by norm_num)
theorem B2320933 : Blo 1374006 2320933 := bbase (se 4 (by rfl) ⟨217587, by rfl⟩ : syracuseStep 2320933 = 435175) (by norm_num)
theorem B9054773 : Blo 1374006 9054773 := bbase (se 5 (by rfl) ⟨424442, by rfl⟩ : syracuseStep 9054773 = 848885) (by norm_num)
theorem B1739333 : Blo 1374006 1739333 := bbase (se 4 (by rfl) ⟨163062, by rfl⟩ : syracuseStep 1739333 = 326125) (by norm_num)
theorem B4639301 : Blo 1374006 4639301 := bbase (se 4 (by rfl) ⟨434934, by rfl⟩ : syracuseStep 4639301 = 869869) (by norm_num)
theorem B3820117 : Blo 1374006 3820117 := bbase (se 8 (by rfl) ⟨22383, by rfl⟩ : syracuseStep 3820117 = 44767) (by norm_num)
theorem B1567333 : Blo 1374006 1567333 := bbase (se 4 (by rfl) ⟨146937, by rfl⟩ : syracuseStep 1567333 = 293875) (by norm_num)
theorem B1739389 : Blo 1374006 1739389 := bbase (se 3 (by rfl) ⟨326135, by rfl⟩ : syracuseStep 1739389 = 652271) (by norm_num)
theorem B2321021 : Blo 1374006 2321021 := bbase (se 3 (by rfl) ⟨435191, by rfl⟩ : syracuseStep 2321021 = 870383) (by norm_num)
theorem B1739485 : Blo 1374006 1739485 := bbase (se 3 (by rfl) ⟨326153, by rfl⟩ : syracuseStep 1739485 = 652307) (by norm_num)
theorem B2321149 : Blo 1374006 2321149 := bbase (se 3 (by rfl) ⟨435215, by rfl⟩ : syracuseStep 2321149 = 870431) (by norm_num)
theorem B2476829 : Blo 1374006 2476829 := bbase (se 3 (by rfl) ⟨464405, by rfl⟩ : syracuseStep 2476829 = 928811) (by norm_num)
theorem B5221205 : Blo 1374006 5221205 := bbase (se 9 (by rfl) ⟨15296, by rfl⟩ : syracuseStep 5221205 = 30593) (by norm_num)
theorem B3304277 : Blo 1374006 3304277 := bbase (se 9 (by rfl) ⟨9680, by rfl⟩ : syracuseStep 3304277 = 19361) (by norm_num)
theorem B4402021 : Blo 1374006 4402021 := bbase (se 4 (by rfl) ⟨412689, by rfl⟩ : syracuseStep 4402021 = 825379) (by norm_num)
theorem B1739657 : Blo 1374006 1739657 := bbase (se 2 (by rfl) ⟨652371, by rfl⟩ : syracuseStep 1739657 = 1304743) (by norm_num)
theorem B1739713 : Blo 1374006 1739713 := bbase (se 2 (by rfl) ⟨652392, by rfl⟩ : syracuseStep 1739713 = 1304785) (by norm_num)
theorem B4639733 : Blo 1374006 4639733 := bbase (se 5 (by rfl) ⟨217487, by rfl⟩ : syracuseStep 4639733 = 434975) (by norm_num)
theorem B7826453 : Blo 1374006 7826453 := bbase (se 6 (by rfl) ⟨183432, by rfl⟩ : syracuseStep 7826453 = 366865) (by norm_num)
theorem B1739809 : Blo 1374006 1739809 := bbase (se 2 (by rfl) ⟨652428, by rfl⟩ : syracuseStep 1739809 = 1304857) (by norm_num)
theorem B3091517 : Blo 1374006 3091517 := bbase (se 3 (by rfl) ⟨579659, by rfl⟩ : syracuseStep 3091517 = 1159319) (by norm_num)
theorem B10439765 : Blo 1374006 10439765 := bbase (se 8 (by rfl) ⟨61170, by rfl⟩ : syracuseStep 10439765 = 122341) (by norm_num)
theorem B8154229 : Blo 1374006 8154229 := bbase (se 5 (by rfl) ⟨382229, by rfl⟩ : syracuseStep 8154229 = 764459) (by norm_num)
theorem B5221493 : Blo 1374006 5221493 := bbase (se 5 (by rfl) ⟨244757, by rfl⟩ : syracuseStep 5221493 = 489515) (by norm_num)
theorem B3091589 : Blo 1374006 3091589 := bbase (se 4 (by rfl) ⟨289836, by rfl⟩ : syracuseStep 3091589 = 579673) (by norm_num)
theorem B2935997 : Blo 1374006 2935997 := bbase (se 3 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 2935997 = 1100999) (by norm_num)
theorem B1739981 : Blo 1374006 1739981 := bbase (se 3 (by rfl) ⟨326246, by rfl⟩ : syracuseStep 1739981 = 652493) (by norm_num)
theorem B3091661 : Blo 1374006 3091661 := bbase (se 3 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 3091661 = 1159373) (by norm_num)
theorem B11144405 : Blo 1374006 11144405 := bbase (se 7 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 11144405 = 261197) (by norm_num)
theorem B4402421 : Blo 1374006 4402421 := bbase (se 5 (by rfl) ⟨206363, by rfl⟩ : syracuseStep 4402421 = 412727) (by norm_num)
theorem B1740037 : Blo 1374006 1740037 := bbase (se 4 (by rfl) ⟨163128, by rfl⟩ : syracuseStep 1740037 = 326257) (by norm_num)
theorem B3091733 : Blo 1374006 3091733 := bbase (se 6 (by rfl) ⟨72462, by rfl⟩ : syracuseStep 3091733 = 144925) (by norm_num)
theorem B3091805 : Blo 1374006 3091805 := bbase (se 3 (by rfl) ⟨579713, by rfl⟩ : syracuseStep 3091805 = 1159427) (by norm_num)
theorem B1740133 : Blo 1374006 1740133 := bbase (se 4 (by rfl) ⟨163137, by rfl⟩ : syracuseStep 1740133 = 326275) (by norm_num)
theorem B3091877 : Blo 1374006 3091877 := bbase (se 4 (by rfl) ⟨289863, by rfl⟩ : syracuseStep 3091877 = 579727) (by norm_num)
theorem B4640165 : Blo 1374006 4640165 := bbase (se 4 (by rfl) ⟨435015, by rfl⟩ : syracuseStep 4640165 = 870031) (by norm_num)
theorem B2936245 : Blo 1374006 2936245 := bbase (se 5 (by rfl) ⟨137636, by rfl⟩ : syracuseStep 2936245 = 275273) (by norm_num)
theorem B3091949 : Blo 1374006 3091949 := bbase (se 3 (by rfl) ⟨579740, by rfl⟩ : syracuseStep 3091949 = 1159481) (by norm_num)
theorem B2977285 : Blo 1374006 2977285 := bbase (se 4 (by rfl) ⟨279120, by rfl⟩ : syracuseStep 2977285 = 558241) (by norm_num)
theorem B1740305 : Blo 1374006 1740305 := bbase (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) (by norm_num)
theorem B3092021 : Blo 1374006 3092021 := bbase (se 5 (by rfl) ⟨144938, by rfl⟩ : syracuseStep 3092021 = 289877) (by norm_num)
theorem B1740361 : Blo 1374006 1740361 := bbase (se 2 (by rfl) ⟨652635, by rfl⟩ : syracuseStep 1740361 = 1305271) (by norm_num)
theorem B2608757 : Blo 1374006 2608757 := bbase (se 5 (by rfl) ⟨122285, by rfl⟩ : syracuseStep 2608757 = 244571) (by norm_num)
theorem B6958709 : Blo 1374006 6958709 := bbase (se 5 (by rfl) ⟨326189, by rfl⟩ : syracuseStep 6958709 = 652379) (by norm_num)
theorem B3092093 : Blo 1374006 3092093 := bbase (se 3 (by rfl) ⟨579767, by rfl⟩ : syracuseStep 3092093 = 1159535) (by norm_num)
theorem B1740457 : Blo 1374006 1740457 := bbase (se 2 (by rfl) ⟨652671, by rfl⟩ : syracuseStep 1740457 = 1305343) (by norm_num)
theorem B3092165 : Blo 1374006 3092165 := bbase (se 4 (by rfl) ⟨289890, by rfl⟩ : syracuseStep 3092165 = 579781) (by norm_num)
theorem B3092237 : Blo 1374006 3092237 := bbase (se 3 (by rfl) ⟨579794, by rfl⟩ : syracuseStep 3092237 = 1159589) (by norm_num)
theorem B1568533 : Blo 1374006 1568533 := bbase (se 6 (by rfl) ⟨36762, by rfl⟩ : syracuseStep 1568533 = 73525) (by norm_num)
theorem B3092309 : Blo 1374006 3092309 := bbase (se 9 (by rfl) ⟨9059, by rfl⟩ : syracuseStep 3092309 = 18119) (by norm_num)
theorem B4640597 : Blo 1374006 4640597 := bbase (se 9 (by rfl) ⟨13595, by rfl⟩ : syracuseStep 4640597 = 27191) (by norm_num)
theorem B25431893 : Blo 1374006 25431893 := bbase (se 9 (by rfl) ⟨74507, by rfl⟩ : syracuseStep 25431893 = 149015) (by norm_num)
theorem B1740629 : Blo 1374006 1740629 := bbase (se 9 (by rfl) ⟨5099, by rfl⟩ : syracuseStep 1740629 = 10199) (by norm_num)
theorem B1740685 : Blo 1374006 1740685 := bbase (se 3 (by rfl) ⟨326378, by rfl⟩ : syracuseStep 1740685 = 652757) (by norm_num)
theorem B3092381 : Blo 1374006 3092381 := bbase (se 3 (by rfl) ⟨579821, by rfl⟩ : syracuseStep 3092381 = 1159643) (by norm_num)
theorem B2936749 : Blo 1374006 2936749 := bbase (se 3 (by rfl) ⟨550640, by rfl⟩ : syracuseStep 2936749 = 1101281) (by norm_num)
theorem B3092453 : Blo 1374006 3092453 := bbase (se 4 (by rfl) ⟨289917, by rfl⟩ : syracuseStep 3092453 = 579835) (by norm_num)
theorem B1740781 : Blo 1374006 1740781 := bbase (se 3 (by rfl) ⟨326396, by rfl⟩ : syracuseStep 1740781 = 652793) (by norm_num)
theorem B3092525 : Blo 1374006 3092525 := bbase (se 3 (by rfl) ⟨579848, by rfl⟩ : syracuseStep 3092525 = 1159697) (by norm_num)
theorem B2510909 : Blo 1374006 2510909 := bbase (se 3 (by rfl) ⟨470795, by rfl⟩ : syracuseStep 2510909 = 941591) (by norm_num)
theorem B6606917 : Blo 1374006 6606917 := bbase (se 4 (by rfl) ⟨619398, by rfl⟩ : syracuseStep 6606917 = 1238797) (by norm_num)
theorem B3092597 : Blo 1374006 3092597 := bbase (se 5 (by rfl) ⟨144965, by rfl⟩ : syracuseStep 3092597 = 289931) (by norm_num)
theorem B7827637 : Blo 1374006 7827637 := bbase (se 5 (by rfl) ⟨366920, by rfl⟩ : syracuseStep 7827637 = 733841) (by norm_num)
theorem B3092669 : Blo 1374006 3092669 := bbase (se 3 (by rfl) ⟨579875, by rfl⟩ : syracuseStep 3092669 = 1159751) (by norm_num)
theorem B7057637 : Blo 1374006 7057637 := bbase (se 4 (by rfl) ⟨661653, by rfl⟩ : syracuseStep 7057637 = 1323307) (by norm_num)
theorem B3092741 : Blo 1374006 3092741 := bbase (se 4 (by rfl) ⟨289944, by rfl⟩ : syracuseStep 3092741 = 579889) (by norm_num)
theorem B6607109 : Blo 1374006 6607109 := bbase (se 4 (by rfl) ⟨619416, by rfl⟩ : syracuseStep 6607109 = 1238833) (by norm_num)
theorem B4641029 : Blo 1374006 4641029 := bbase (se 4 (by rfl) ⟨435096, by rfl⟩ : syracuseStep 4641029 = 870193) (by norm_num)
theorem B1650989 : Blo 1374006 1650989 := bbase (se 3 (by rfl) ⟨309560, by rfl⟩ : syracuseStep 1650989 = 619121) (by norm_num)
theorem B3092813 : Blo 1374006 3092813 := bbase (se 3 (by rfl) ⟨579902, by rfl⟩ : syracuseStep 3092813 = 1159805) (by norm_num)
theorem B1651037 : Blo 1374006 1651037 := bbase (se 3 (by rfl) ⟨309569, by rfl⟩ : syracuseStep 1651037 = 619139) (by norm_num)
theorem B2609509 : Blo 1374006 2609509 := bbase (se 4 (by rfl) ⟨244641, by rfl⟩ : syracuseStep 2609509 = 489283) (by norm_num)
theorem B3092885 : Blo 1374006 3092885 := bbase (se 6 (by rfl) ⟨72489, by rfl⟩ : syracuseStep 3092885 = 144979) (by norm_num)
theorem B3092957 : Blo 1374006 3092957 := bbase (se 3 (by rfl) ⟨579929, by rfl⟩ : syracuseStep 3092957 = 1159859) (by norm_num)
theorem B2609653 : Blo 1374006 2609653 := bbase (se 5 (by rfl) ⟨122327, by rfl⟩ : syracuseStep 2609653 = 244655) (by norm_num)
theorem B3093029 : Blo 1374006 3093029 := bbase (se 4 (by rfl) ⟨289971, by rfl⟩ : syracuseStep 3093029 = 579943) (by norm_num)
theorem B3093101 : Blo 1374006 3093101 := bbase (se 3 (by rfl) ⟨579956, by rfl⟩ : syracuseStep 3093101 = 1159913) (by norm_num)
theorem B6607493 : Blo 1374006 6607493 := bbase (se 4 (by rfl) ⟨619452, by rfl⟩ : syracuseStep 6607493 = 1238905) (by norm_num)
theorem B2609813 : Blo 1374006 2609813 := bbase (se 6 (by rfl) ⟨61167, by rfl⟩ : syracuseStep 2609813 = 122335) (by norm_num)
theorem B3093173 : Blo 1374006 3093173 := bbase (se 5 (by rfl) ⟨144992, by rfl⟩ : syracuseStep 3093173 = 289985) (by norm_num)
theorem B4641461 : Blo 1374006 4641461 := bbase (se 5 (by rfl) ⟨217568, by rfl⟩ : syracuseStep 4641461 = 435137) (by norm_num)
theorem B7533269 : Blo 1374006 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B2061029 : Blo 1374006 2061029 := bbase (se 4 (by rfl) ⟨193221, by rfl⟩ : syracuseStep 2061029 = 386443) (by norm_num)
theorem B3478261 : Blo 1374006 3478261 := bbase (se 5 (by rfl) ⟨163043, by rfl⟩ : syracuseStep 3478261 = 326087) (by norm_num)
theorem B2061053 : Blo 1374006 2061053 := bbase (se 3 (by rfl) ⟨386447, by rfl⟩ : syracuseStep 2061053 = 772895) (by norm_num)
theorem B3093245 : Blo 1374006 3093245 := bbase (se 3 (by rfl) ⟨579983, by rfl⟩ : syracuseStep 3093245 = 1159967) (by norm_num)
theorem B2061077 : Blo 1374006 2061077 := bbase (se 6 (by rfl) ⟨48306, by rfl⟩ : syracuseStep 2061077 = 96613) (by norm_num)
theorem B2609957 : Blo 1374006 2609957 := bbase (se 4 (by rfl) ⟨244683, by rfl⟩ : syracuseStep 2609957 = 489367) (by norm_num)
theorem B2937637 : Blo 1374006 2937637 := bbase (se 4 (by rfl) ⟨275403, by rfl⟩ : syracuseStep 2937637 = 550807) (by norm_num)
theorem B2061101 : Blo 1374006 2061101 := bbase (se 3 (by rfl) ⟨386456, by rfl⟩ : syracuseStep 2061101 = 772913) (by norm_num)
theorem B2061125 : Blo 1374006 2061125 := bbase (se 4 (by rfl) ⟨193230, by rfl⟩ : syracuseStep 2061125 = 386461) (by norm_num)
theorem B3093317 : Blo 1374006 3093317 := bbase (se 4 (by rfl) ⟨289998, by rfl⟩ : syracuseStep 3093317 = 579997) (by norm_num)
theorem B2061149 : Blo 1374006 2061149 := bbase (se 3 (by rfl) ⟨386465, by rfl⟩ : syracuseStep 2061149 = 772931) (by norm_num)
theorem B3478373 : Blo 1374006 3478373 := bbase (se 4 (by rfl) ⟨326097, by rfl⟩ : syracuseStep 3478373 = 652195) (by norm_num)
theorem B3527525 : Blo 1374006 3527525 := bbase (se 4 (by rfl) ⟨330705, by rfl⟩ : syracuseStep 3527525 = 661411) (by norm_num)
theorem B2061173 : Blo 1374006 2061173 := bbase (se 5 (by rfl) ⟨96617, by rfl⟩ : syracuseStep 2061173 = 193235) (by norm_num)
theorem B1651585 : Blo 1374006 1651585 := bbase (se 2 (by rfl) ⟨619344, by rfl⟩ : syracuseStep 1651585 = 1238689) (by norm_num)
theorem B6960005 : Blo 1374006 6960005 := bbase (se 4 (by rfl) ⟨652500, by rfl⟩ : syracuseStep 6960005 = 1305001) (by norm_num)
theorem B2511749 : Blo 1374006 2511749 := bbase (se 4 (by rfl) ⟨235476, by rfl⟩ : syracuseStep 2511749 = 470953) (by norm_num)
theorem B2061197 : Blo 1374006 2061197 := bbase (se 3 (by rfl) ⟨386474, by rfl⟩ : syracuseStep 2061197 = 772949) (by norm_num)
theorem B3093389 : Blo 1374006 3093389 := bbase (se 3 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 3093389 = 1160021) (by norm_num)
theorem B2061221 : Blo 1374006 2061221 := bbase (se 4 (by rfl) ⟨193239, by rfl⟩ : syracuseStep 2061221 = 386479) (by norm_num)
theorem B2061245 : Blo 1374006 2061245 := bbase (se 3 (by rfl) ⟨386483, by rfl⟩ : syracuseStep 2061245 = 772967) (by norm_num)
theorem B2061269 : Blo 1374006 2061269 := bbase (se 7 (by rfl) ⟨24155, by rfl⟩ : syracuseStep 2061269 = 48311) (by norm_num)
theorem B3093461 : Blo 1374006 3093461 := bbase (se 7 (by rfl) ⟨36251, by rfl⟩ : syracuseStep 3093461 = 72503) (by norm_num)
theorem B2061293 : Blo 1374006 2061293 := bbase (se 3 (by rfl) ⟨386492, by rfl⟩ : syracuseStep 2061293 = 772985) (by norm_num)
theorem B2061317 : Blo 1374006 2061317 := bbase (se 4 (by rfl) ⟨193248, by rfl⟩ : syracuseStep 2061317 = 386497) (by norm_num)
theorem B3912725 : Blo 1374006 3912725 := bbase (se 6 (by rfl) ⟨91704, by rfl⟩ : syracuseStep 3912725 = 183409) (by norm_num)
theorem B2061341 : Blo 1374006 2061341 := bbase (se 3 (by rfl) ⟨386501, by rfl⟩ : syracuseStep 2061341 = 773003) (by norm_num)
theorem B3093533 : Blo 1374006 3093533 := bbase (se 3 (by rfl) ⟨580037, by rfl⟩ : syracuseStep 3093533 = 1160075) (by norm_num)
theorem B3478565 : Blo 1374006 3478565 := bbase (se 4 (by rfl) ⟨326115, by rfl⟩ : syracuseStep 3478565 = 652231) (by norm_num)
theorem B2061365 : Blo 1374006 2061365 := bbase (se 5 (by rfl) ⟨96626, by rfl⟩ : syracuseStep 2061365 = 193253) (by norm_num)
theorem B2610245 : Blo 1374006 2610245 := bbase (se 4 (by rfl) ⟨244710, by rfl⟩ : syracuseStep 2610245 = 489421) (by norm_num)
theorem B2061389 : Blo 1374006 2061389 := bbase (se 3 (by rfl) ⟨386510, by rfl⟩ : syracuseStep 2061389 = 773021) (by norm_num)
theorem B8811605 : Blo 1374006 8811605 := bbase (se 8 (by rfl) ⟨51630, by rfl⟩ : syracuseStep 8811605 = 103261) (by norm_num)
theorem B2061413 : Blo 1374006 2061413 := bbase (se 4 (by rfl) ⟨193257, by rfl⟩ : syracuseStep 2061413 = 386515) (by norm_num)
theorem B3093605 : Blo 1374006 3093605 := bbase (se 4 (by rfl) ⟨290025, by rfl⟩ : syracuseStep 3093605 = 580051) (by norm_num)
theorem B4641893 : Blo 1374006 4641893 := bbase (se 4 (by rfl) ⟨435177, by rfl⟩ : syracuseStep 4641893 = 870355) (by norm_num)
theorem B2061437 : Blo 1374006 2061437 := bbase (se 3 (by rfl) ⟨386519, by rfl⟩ : syracuseStep 2061437 = 773039) (by norm_num)
theorem B2061461 : Blo 1374006 2061461 := bbase (se 6 (by rfl) ⟨48315, by rfl⟩ : syracuseStep 2061461 = 96631) (by norm_num)
theorem B3134629 : Blo 1374006 3134629 := bbase (se 4 (by rfl) ⟨293871, by rfl⟩ : syracuseStep 3134629 = 587743) (by norm_num)
theorem B2061485 : Blo 1374006 2061485 := bbase (se 3 (by rfl) ⟨386528, by rfl⟩ : syracuseStep 2061485 = 773057) (by norm_num)
theorem B3093677 : Blo 1374006 3093677 := bbase (se 3 (by rfl) ⟨580064, by rfl⟩ : syracuseStep 3093677 = 1160129) (by norm_num)
theorem B2061509 : Blo 1374006 2061509 := bbase (se 4 (by rfl) ⟨193266, by rfl⟩ : syracuseStep 2061509 = 386533) (by norm_num)
theorem B3527893 : Blo 1374006 3527893 := bbase (se 7 (by rfl) ⟨41342, by rfl⟩ : syracuseStep 3527893 = 82685) (by norm_num)
theorem B2061533 : Blo 1374006 2061533 := bbase (se 3 (by rfl) ⟨386537, by rfl⟩ : syracuseStep 2061533 = 773075) (by norm_num)
theorem B2610397 : Blo 1374006 2610397 := bbase (se 3 (by rfl) ⟨489449, by rfl⟩ : syracuseStep 2610397 = 978899) (by norm_num)
theorem B3134701 : Blo 1374006 3134701 := bbase (se 3 (by rfl) ⟨587756, by rfl⟩ : syracuseStep 3134701 = 1175513) (by norm_num)
theorem B2061557 : Blo 1374006 2061557 := bbase (se 5 (by rfl) ⟨96635, by rfl⟩ : syracuseStep 2061557 = 193271) (by norm_num)
theorem B3093749 : Blo 1374006 3093749 := bbase (se 5 (by rfl) ⟨145019, by rfl⟩ : syracuseStep 3093749 = 290039) (by norm_num)
theorem B2061581 : Blo 1374006 2061581 := bbase (se 3 (by rfl) ⟨386546, by rfl⟩ : syracuseStep 2061581 = 773093) (by norm_num)
theorem B2061605 : Blo 1374006 2061605 := bbase (se 4 (by rfl) ⟨193275, by rfl⟩ : syracuseStep 2061605 = 386551) (by norm_num)
theorem B12711221 : Blo 1374006 12711221 := bbase (se 5 (by rfl) ⟨595838, by rfl⟩ : syracuseStep 12711221 = 1191677) (by norm_num)
theorem B2061629 : Blo 1374006 2061629 := bbase (se 3 (by rfl) ⟨386555, by rfl⟩ : syracuseStep 2061629 = 773111) (by norm_num)
theorem B3093821 : Blo 1374006 3093821 := bbase (se 3 (by rfl) ⟨580091, by rfl⟩ : syracuseStep 3093821 = 1160183) (by norm_num)
theorem B2061653 : Blo 1374006 2061653 := bbase (se 13 (by rfl) ⟨377, by rfl⟩ : syracuseStep 2061653 = 755) (by norm_num)
theorem B1652065 : Blo 1374006 1652065 := bbase (se 2 (by rfl) ⟨619524, by rfl⟩ : syracuseStep 1652065 = 1239049) (by norm_num)
theorem B2061677 : Blo 1374006 2061677 := bbase (se 3 (by rfl) ⟨386564, by rfl⟩ : syracuseStep 2061677 = 773129) (by norm_num)
theorem B3478909 : Blo 1374006 3478909 := bbase (se 3 (by rfl) ⟨652295, by rfl⟩ : syracuseStep 3478909 = 1304591) (by norm_num)
theorem B2061701 : Blo 1374006 2061701 := bbase (se 4 (by rfl) ⟨193284, by rfl⟩ : syracuseStep 2061701 = 386569) (by norm_num)
theorem B3093893 : Blo 1374006 3093893 := bbase (se 4 (by rfl) ⟨290052, by rfl⟩ : syracuseStep 3093893 = 580105) (by norm_num)
theorem B2061725 : Blo 1374006 2061725 := bbase (se 3 (by rfl) ⟨386573, by rfl⟩ : syracuseStep 2061725 = 773147) (by norm_num)
theorem B2061749 : Blo 1374006 2061749 := bbase (se 5 (by rfl) ⟨96644, by rfl⟩ : syracuseStep 2061749 = 193289) (by norm_num)
theorem B2061773 : Blo 1374006 2061773 := bbase (se 3 (by rfl) ⟨386582, by rfl⟩ : syracuseStep 2061773 = 773165) (by norm_num)
theorem B3093965 : Blo 1374006 3093965 := bbase (se 3 (by rfl) ⟨580118, by rfl⟩ : syracuseStep 3093965 = 1160237) (by norm_num)
theorem B2061797 : Blo 1374006 2061797 := bbase (se 4 (by rfl) ⟨193293, by rfl⟩ : syracuseStep 2061797 = 386587) (by norm_num)
theorem B3479021 : Blo 1374006 3479021 := bbase (se 3 (by rfl) ⟨652316, by rfl⟩ : syracuseStep 3479021 = 1304633) (by norm_num)
theorem B2061821 : Blo 1374006 2061821 := bbase (se 3 (by rfl) ⟨386591, by rfl⟩ : syracuseStep 2061821 = 773183) (by norm_num)
theorem B2610701 : Blo 1374006 2610701 := bbase (se 3 (by rfl) ⟨489506, by rfl⟩ : syracuseStep 2610701 = 979013) (by norm_num)
theorem B2061845 : Blo 1374006 2061845 := bbase (se 6 (by rfl) ⟨48324, by rfl⟩ : syracuseStep 2061845 = 96649) (by norm_num)
theorem B3094037 : Blo 1374006 3094037 := bbase (se 6 (by rfl) ⟨72516, by rfl⟩ : syracuseStep 3094037 = 145033) (by norm_num)
theorem B4642325 : Blo 1374006 4642325 := bbase (se 6 (by rfl) ⟨108804, by rfl⟩ : syracuseStep 4642325 = 217609) (by norm_num)
theorem B2061869 : Blo 1374006 2061869 := bbase (se 3 (by rfl) ⟨386600, by rfl⟩ : syracuseStep 2061869 = 773201) (by norm_num)
theorem B1545781 : Blo 1374006 1545781 := bbase (se 5 (by rfl) ⟨72458, by rfl⟩ : syracuseStep 1545781 = 144917) (by norm_num)
theorem B2061893 : Blo 1374006 2061893 := bbase (se 4 (by rfl) ⟨193302, by rfl⟩ : syracuseStep 2061893 = 386605) (by norm_num)
theorem B2201165 : Blo 1374006 2201165 := bbase (se 3 (by rfl) ⟨412718, by rfl⟩ : syracuseStep 2201165 = 825437) (by norm_num)
theorem B1545817 : Blo 1374006 1545817 := bbase (se 2 (by rfl) ⟨579681, by rfl⟩ : syracuseStep 1545817 = 1159363) (by norm_num)
theorem B2061917 : Blo 1374006 2061917 := bbase (se 3 (by rfl) ⟨386609, by rfl⟩ : syracuseStep 2061917 = 773219) (by norm_num)
theorem B3094109 : Blo 1374006 3094109 := bbase (se 3 (by rfl) ⟨580145, by rfl⟩ : syracuseStep 3094109 = 1160291) (by norm_num)
theorem B2061941 : Blo 1374006 2061941 := bbase (se 5 (by rfl) ⟨96653, by rfl⟩ : syracuseStep 2061941 = 193307) (by norm_num)
theorem B1545853 : Blo 1374006 1545853 := bbase (se 3 (by rfl) ⟨289847, by rfl⟩ : syracuseStep 1545853 = 579695) (by norm_num)
theorem B2061965 : Blo 1374006 2061965 := bbase (se 3 (by rfl) ⟨386618, by rfl⟩ : syracuseStep 2061965 = 773237) (by norm_num)
theorem B1545889 : Blo 1374006 1545889 := bbase (se 2 (by rfl) ⟨579708, by rfl⟩ : syracuseStep 1545889 = 1159417) (by norm_num)
theorem B2061989 : Blo 1374006 2061989 := bbase (se 4 (by rfl) ⟨193311, by rfl⟩ : syracuseStep 2061989 = 386623) (by norm_num)
theorem B3094181 : Blo 1374006 3094181 := bbase (se 4 (by rfl) ⟨290079, by rfl⟩ : syracuseStep 3094181 = 580159) (by norm_num)
theorem B2201261 : Blo 1374006 2201261 := bbase (se 3 (by rfl) ⟨412736, by rfl⟩ : syracuseStep 2201261 = 825473) (by norm_num)
theorem B3479213 : Blo 1374006 3479213 := bbase (se 3 (by rfl) ⟨652352, by rfl⟩ : syracuseStep 3479213 = 1304705) (by norm_num)
theorem B2062013 : Blo 1374006 2062013 := bbase (se 3 (by rfl) ⟨386627, by rfl⟩ : syracuseStep 2062013 = 773255) (by norm_num)
theorem B1545925 : Blo 1374006 1545925 := bbase (se 4 (by rfl) ⟨144930, by rfl⟩ : syracuseStep 1545925 = 289861) (by norm_num)
theorem B2201293 : Blo 1374006 2201293 := bbase (se 3 (by rfl) ⟨412742, by rfl⟩ : syracuseStep 2201293 = 825485) (by norm_num)
theorem B2062037 : Blo 1374006 2062037 := bbase (se 7 (by rfl) ⟨24164, by rfl⟩ : syracuseStep 2062037 = 48329) (by norm_num)
theorem B1545961 : Blo 1374006 1545961 := bbase (se 2 (by rfl) ⟨579735, by rfl⟩ : syracuseStep 1545961 = 1159471) (by norm_num)
theorem B2062061 : Blo 1374006 2062061 := bbase (se 3 (by rfl) ⟨386636, by rfl⟩ : syracuseStep 2062061 = 773273) (by norm_num)
theorem B3094253 : Blo 1374006 3094253 := bbase (se 3 (by rfl) ⟨580172, by rfl⟩ : syracuseStep 3094253 = 1160345) (by norm_num)
theorem B2062085 : Blo 1374006 2062085 := bbase (se 4 (by rfl) ⟨193320, by rfl⟩ : syracuseStep 2062085 = 386641) (by norm_num)
theorem B1545997 : Blo 1374006 1545997 := bbase (se 3 (by rfl) ⟨289874, by rfl⟩ : syracuseStep 1545997 = 579749) (by norm_num)
theorem B2062109 : Blo 1374006 2062109 := bbase (se 3 (by rfl) ⟨386645, by rfl⟩ : syracuseStep 2062109 = 773291) (by norm_num)
theorem B1546033 : Blo 1374006 1546033 := bbase (se 2 (by rfl) ⟨579762, by rfl⟩ : syracuseStep 1546033 = 1159525) (by norm_num)
theorem B2062133 : Blo 1374006 2062133 := bbase (se 5 (by rfl) ⟨96662, by rfl⟩ : syracuseStep 2062133 = 193325) (by norm_num)
theorem B3094325 : Blo 1374006 3094325 := bbase (se 5 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 3094325 = 290093) (by norm_num)
theorem B2062157 : Blo 1374006 2062157 := bbase (se 3 (by rfl) ⟨386654, by rfl⟩ : syracuseStep 2062157 = 773309) (by norm_num)
theorem B1546069 : Blo 1374006 1546069 := bbase (se 9 (by rfl) ⟨4529, by rfl⟩ : syracuseStep 1546069 = 9059) (by norm_num)
theorem B19822421 : Blo 1374006 19822421 := bbase (se 9 (by rfl) ⟨58073, by rfl⟩ : syracuseStep 19822421 = 116147) (by norm_num)
theorem B2062181 : Blo 1374006 2062181 := bbase (se 4 (by rfl) ⟨193329, by rfl⟩ : syracuseStep 2062181 = 386659) (by norm_num)
theorem B1546105 : Blo 1374006 1546105 := bbase (se 2 (by rfl) ⟨579789, by rfl⟩ : syracuseStep 1546105 = 1159579) (by norm_num)
theorem B2062205 : Blo 1374006 2062205 := bbase (se 3 (by rfl) ⟨386663, by rfl⟩ : syracuseStep 2062205 = 773327) (by norm_num)
theorem B3094397 : Blo 1374006 3094397 := bbase (se 3 (by rfl) ⟨580199, by rfl⟩ : syracuseStep 3094397 = 1160399) (by norm_num)
theorem B2062229 : Blo 1374006 2062229 := bbase (se 6 (by rfl) ⟨48333, by rfl⟩ : syracuseStep 2062229 = 96667) (by norm_num)
theorem B1546141 : Blo 1374006 1546141 := bbase (se 3 (by rfl) ⟨289901, by rfl⟩ : syracuseStep 1546141 = 579803) (by norm_num)
theorem B2062253 : Blo 1374006 2062253 := bbase (se 3 (by rfl) ⟨386672, by rfl⟩ : syracuseStep 2062253 = 773345) (by norm_num)
theorem B1546177 : Blo 1374006 1546177 := bbase (se 2 (by rfl) ⟨579816, by rfl⟩ : syracuseStep 1546177 = 1159633) (by norm_num)
theorem B2062277 : Blo 1374006 2062277 := bbase (se 4 (by rfl) ⟨193338, by rfl⟩ : syracuseStep 2062277 = 386677) (by norm_num)
theorem B3094469 : Blo 1374006 3094469 := bbase (se 4 (by rfl) ⟨290106, by rfl⟩ : syracuseStep 3094469 = 580213) (by norm_num)
theorem B2062301 : Blo 1374006 2062301 := bbase (se 3 (by rfl) ⟨386681, by rfl⟩ : syracuseStep 2062301 = 773363) (by norm_num)
theorem B1546213 : Blo 1374006 1546213 := bbase (se 4 (by rfl) ⟨144957, by rfl⟩ : syracuseStep 1546213 = 289915) (by norm_num)
theorem B3913717 : Blo 1374006 3913717 := bbase (se 5 (by rfl) ⟨183455, by rfl⟩ : syracuseStep 3913717 = 366911) (by norm_num)
theorem B2062325 : Blo 1374006 2062325 := bbase (se 5 (by rfl) ⟨96671, by rfl⟩ : syracuseStep 2062325 = 193343) (by norm_num)
theorem B3479557 : Blo 1374006 3479557 := bbase (se 4 (by rfl) ⟨326208, by rfl⟩ : syracuseStep 3479557 = 652417) (by norm_num)
theorem B1546249 : Blo 1374006 1546249 := bbase (se 2 (by rfl) ⟨579843, by rfl⟩ : syracuseStep 1546249 = 1159687) (by norm_num)
theorem B2062349 : Blo 1374006 2062349 := bbase (se 3 (by rfl) ⟨386690, by rfl⟩ : syracuseStep 2062349 = 773381) (by norm_num)
theorem B3094541 : Blo 1374006 3094541 := bbase (se 3 (by rfl) ⟨580226, by rfl⟩ : syracuseStep 3094541 = 1160453) (by norm_num)
theorem B2062373 : Blo 1374006 2062373 := bbase (se 4 (by rfl) ⟨193347, by rfl⟩ : syracuseStep 2062373 = 386695) (by norm_num)
theorem B1546285 : Blo 1374006 1546285 := bbase (se 3 (by rfl) ⟨289928, by rfl⟩ : syracuseStep 1546285 = 579857) (by norm_num)
theorem B2062397 : Blo 1374006 2062397 := bbase (se 3 (by rfl) ⟨386699, by rfl⟩ : syracuseStep 2062397 = 773399) (by norm_num)
theorem B5871685 : Blo 1374006 5871685 := bbase (se 4 (by rfl) ⟨550470, by rfl⟩ : syracuseStep 5871685 = 1100941) (by norm_num)
theorem B1546321 : Blo 1374006 1546321 := bbase (se 2 (by rfl) ⟨579870, by rfl⟩ : syracuseStep 1546321 = 1159741) (by norm_num)
theorem B12064853 : Blo 1374006 12064853 := bbase (se 8 (by rfl) ⟨70692, by rfl⟩ : syracuseStep 12064853 = 141385) (by norm_num)
theorem B2062421 : Blo 1374006 2062421 := bbase (se 8 (by rfl) ⟨12084, by rfl⟩ : syracuseStep 2062421 = 24169) (by norm_num)
theorem B3094613 : Blo 1374006 3094613 := bbase (se 8 (by rfl) ⟨18132, by rfl⟩ : syracuseStep 3094613 = 36265) (by norm_num)
theorem B2062445 : Blo 1374006 2062445 := bbase (se 3 (by rfl) ⟨386708, by rfl⟩ : syracuseStep 2062445 = 773417) (by norm_num)
theorem B1546357 : Blo 1374006 1546357 := bbase (se 5 (by rfl) ⟨72485, by rfl⟩ : syracuseStep 1546357 = 144971) (by norm_num)
theorem B3479669 : Blo 1374006 3479669 := bbase (se 5 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 3479669 = 326219) (by norm_num)
theorem B7829621 : Blo 1374006 7829621 := bbase (se 5 (by rfl) ⟨367013, by rfl⟩ : syracuseStep 7829621 = 734027) (by norm_num)
theorem B2062469 : Blo 1374006 2062469 := bbase (se 4 (by rfl) ⟨193356, by rfl⟩ : syracuseStep 2062469 = 386713) (by norm_num)
theorem B6961301 : Blo 1374006 6961301 := bbase (se 6 (by rfl) ⟨163155, by rfl⟩ : syracuseStep 6961301 = 326311) (by norm_num)
theorem B1546393 : Blo 1374006 1546393 := bbase (se 2 (by rfl) ⟨579897, by rfl⟩ : syracuseStep 1546393 = 1159795) (by norm_num)
theorem B2062493 : Blo 1374006 2062493 := bbase (se 3 (by rfl) ⟨386717, by rfl⟩ : syracuseStep 2062493 = 773435) (by norm_num)
theorem B3094685 : Blo 1374006 3094685 := bbase (se 3 (by rfl) ⟨580253, by rfl⟩ : syracuseStep 3094685 = 1160507) (by norm_num)
theorem B2062517 : Blo 1374006 2062517 := bbase (se 5 (by rfl) ⟨96680, by rfl⟩ : syracuseStep 2062517 = 193361) (by norm_num)
theorem B1546429 : Blo 1374006 1546429 := bbase (se 3 (by rfl) ⟨289955, by rfl⟩ : syracuseStep 1546429 = 579911) (by norm_num)
theorem B2062541 : Blo 1374006 2062541 := bbase (se 3 (by rfl) ⟨386726, by rfl⟩ : syracuseStep 2062541 = 773453) (by norm_num)
theorem B1546465 : Blo 1374006 1546465 := bbase (se 2 (by rfl) ⟨579924, by rfl⟩ : syracuseStep 1546465 = 1159849) (by norm_num)
theorem B2062565 : Blo 1374006 2062565 := bbase (se 4 (by rfl) ⟨193365, by rfl⟩ : syracuseStep 2062565 = 386731) (by norm_num)
theorem B3094757 : Blo 1374006 3094757 := bbase (se 4 (by rfl) ⟨290133, by rfl⟩ : syracuseStep 3094757 = 580267) (by norm_num)
theorem B2062589 : Blo 1374006 2062589 := bbase (se 3 (by rfl) ⟨386735, by rfl⟩ : syracuseStep 2062589 = 773471) (by norm_num)
theorem B1546501 : Blo 1374006 1546501 := bbase (se 4 (by rfl) ⟨144984, by rfl⟩ : syracuseStep 1546501 = 289969) (by norm_num)
theorem B11745557 : Blo 1374006 11745557 := bbase (se 6 (by rfl) ⟨275286, by rfl⟩ : syracuseStep 11745557 = 550573) (by norm_num)
theorem B2062613 : Blo 1374006 2062613 := bbase (se 6 (by rfl) ⟨48342, by rfl⟩ : syracuseStep 2062613 = 96685) (by norm_num)
theorem B1546537 : Blo 1374006 1546537 := bbase (se 2 (by rfl) ⟨579951, by rfl⟩ : syracuseStep 1546537 = 1159903) (by norm_num)
theorem B2062637 : Blo 1374006 2062637 := bbase (se 3 (by rfl) ⟨386744, by rfl⟩ : syracuseStep 2062637 = 773489) (by norm_num)
theorem B3094829 : Blo 1374006 3094829 := bbase (se 3 (by rfl) ⟨580280, by rfl⟩ : syracuseStep 3094829 = 1160561) (by norm_num)
theorem B3479861 : Blo 1374006 3479861 := bbase (se 5 (by rfl) ⟨163118, by rfl⟩ : syracuseStep 3479861 = 326237) (by norm_num)
theorem B2062661 : Blo 1374006 2062661 := bbase (se 4 (by rfl) ⟨193374, by rfl⟩ : syracuseStep 2062661 = 386749) (by norm_num)
theorem B1546573 : Blo 1374006 1546573 := bbase (se 3 (by rfl) ⟨289982, by rfl⟩ : syracuseStep 1546573 = 579965) (by norm_num)
theorem B2062685 : Blo 1374006 2062685 := bbase (se 3 (by rfl) ⟨386753, by rfl⟩ : syracuseStep 2062685 = 773507) (by norm_num)
theorem B1546609 : Blo 1374006 1546609 := bbase (se 2 (by rfl) ⟨579978, by rfl⟩ : syracuseStep 1546609 = 1159957) (by norm_num)
theorem B2062709 : Blo 1374006 2062709 := bbase (se 5 (by rfl) ⟨96689, by rfl⟩ : syracuseStep 2062709 = 193379) (by norm_num)
theorem B1857925 : Blo 1374006 1857925 := bbase (se 4 (by rfl) ⟨174180, by rfl⟩ : syracuseStep 1857925 = 348361) (by norm_num)
theorem B2062733 : Blo 1374006 2062733 := bbase (se 3 (by rfl) ⟨386762, by rfl⟩ : syracuseStep 2062733 = 773525) (by norm_num)
theorem B1546645 : Blo 1374006 1546645 := bbase (se 6 (by rfl) ⟨36249, by rfl⟩ : syracuseStep 1546645 = 72499) (by norm_num)
theorem B2062757 : Blo 1374006 2062757 := bbase (se 4 (by rfl) ⟨193383, by rfl⟩ : syracuseStep 2062757 = 386767) (by norm_num)
theorem B1546681 : Blo 1374006 1546681 := bbase (se 2 (by rfl) ⟨580005, by rfl⟩ : syracuseStep 1546681 = 1160011) (by norm_num)
theorem B2062781 : Blo 1374006 2062781 := bbase (se 3 (by rfl) ⟨386771, by rfl⟩ : syracuseStep 2062781 = 773543) (by norm_num)
theorem B2062805 : Blo 1374006 2062805 := bbase (se 7 (by rfl) ⟨24173, by rfl⟩ : syracuseStep 2062805 = 48347) (by norm_num)
theorem B1546717 : Blo 1374006 1546717 := bbase (se 3 (by rfl) ⟨290009, by rfl⟩ : syracuseStep 1546717 = 580019) (by norm_num)
theorem B2062829 : Blo 1374006 2062829 := bbase (se 3 (by rfl) ⟨386780, by rfl⟩ : syracuseStep 2062829 = 773561) (by norm_num)
theorem B1546753 : Blo 1374006 1546753 := bbase (se 2 (by rfl) ⟨580032, by rfl⟩ : syracuseStep 1546753 = 1160065) (by norm_num)
theorem B2062853 : Blo 1374006 2062853 := bbase (se 4 (by rfl) ⟨193392, by rfl⟩ : syracuseStep 2062853 = 386785) (by norm_num)
theorem B2062877 : Blo 1374006 2062877 := bbase (se 3 (by rfl) ⟨386789, by rfl⟩ : syracuseStep 2062877 = 773579) (by norm_num)
theorem B1546789 : Blo 1374006 1546789 := bbase (se 4 (by rfl) ⟨145011, by rfl⟩ : syracuseStep 1546789 = 290023) (by norm_num)
theorem B2062901 : Blo 1374006 2062901 := bbase (se 5 (by rfl) ⟨96698, by rfl⟩ : syracuseStep 2062901 = 193397) (by norm_num)
theorem B1546825 : Blo 1374006 1546825 := bbase (se 2 (by rfl) ⟨580059, by rfl⟩ : syracuseStep 1546825 = 1160119) (by norm_num)
theorem B2062925 : Blo 1374006 2062925 := bbase (se 3 (by rfl) ⟨386798, by rfl⟩ : syracuseStep 2062925 = 773597) (by norm_num)
theorem B1858141 : Blo 1374006 1858141 := bbase (se 3 (by rfl) ⟨348401, by rfl⟩ : syracuseStep 1858141 = 696803) (by norm_num)
theorem B2062949 : Blo 1374006 2062949 := bbase (se 4 (by rfl) ⟨193401, by rfl⟩ : syracuseStep 2062949 = 386803) (by norm_num)
theorem B1546861 : Blo 1374006 1546861 := bbase (se 3 (by rfl) ⟨290036, by rfl⟩ : syracuseStep 1546861 = 580073) (by norm_num)
theorem B2062973 : Blo 1374006 2062973 := bbase (se 3 (by rfl) ⟨386807, by rfl⟩ : syracuseStep 2062973 = 773615) (by norm_num)
theorem B3480205 : Blo 1374006 3480205 := bbase (se 3 (by rfl) ⟨652538, by rfl⟩ : syracuseStep 3480205 = 1305077) (by norm_num)
theorem B1546897 : Blo 1374006 1546897 := bbase (se 2 (by rfl) ⟨580086, by rfl⟩ : syracuseStep 1546897 = 1160173) (by norm_num)
theorem B2062997 : Blo 1374006 2062997 := bbase (se 6 (by rfl) ⟨48351, by rfl⟩ : syracuseStep 2062997 = 96703) (by norm_num)
theorem B2063021 : Blo 1374006 2063021 := bbase (se 3 (by rfl) ⟨386816, by rfl⟩ : syracuseStep 2063021 = 773633) (by norm_num)
theorem B1546933 : Blo 1374006 1546933 := bbase (se 5 (by rfl) ⟨72512, by rfl⟩ : syracuseStep 1546933 = 145025) (by norm_num)
theorem B2063045 : Blo 1374006 2063045 := bbase (se 4 (by rfl) ⟨193410, by rfl⟩ : syracuseStep 2063045 = 386821) (by norm_num)
theorem B1546969 : Blo 1374006 1546969 := bbase (se 2 (by rfl) ⟨580113, by rfl⟩ : syracuseStep 1546969 = 1160227) (by norm_num)
theorem B2063069 : Blo 1374006 2063069 := bbase (se 3 (by rfl) ⟨386825, by rfl⟩ : syracuseStep 2063069 = 773651) (by norm_num)
theorem B2063093 : Blo 1374006 2063093 := bbase (se 5 (by rfl) ⟨96707, by rfl⟩ : syracuseStep 2063093 = 193415) (by norm_num)
theorem B3480317 : Blo 1374006 3480317 := bbase (se 3 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 3480317 = 1305119) (by norm_num)
theorem B1547005 : Blo 1374006 1547005 := bbase (se 3 (by rfl) ⟨290063, by rfl⟩ : syracuseStep 1547005 = 580127) (by norm_num)
theorem B2063117 : Blo 1374006 2063117 := bbase (se 3 (by rfl) ⟨386834, by rfl⟩ : syracuseStep 2063117 = 773669) (by norm_num)
theorem B1547041 : Blo 1374006 1547041 := bbase (se 2 (by rfl) ⟨580140, by rfl⟩ : syracuseStep 1547041 = 1160281) (by norm_num)
theorem B2063141 : Blo 1374006 2063141 := bbase (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) (by norm_num)
theorem B2063165 : Blo 1374006 2063165 := bbase (se 3 (by rfl) ⟨386843, by rfl⟩ : syracuseStep 2063165 = 773687) (by norm_num)
theorem B1547077 : Blo 1374006 1547077 := bbase (se 4 (by rfl) ⟨145038, by rfl⟩ : syracuseStep 1547077 = 290077) (by norm_num)
theorem B2063189 : Blo 1374006 2063189 := bbase (se 9 (by rfl) ⟨6044, by rfl⟩ : syracuseStep 2063189 = 12089) (by norm_num)
theorem B1547113 : Blo 1374006 1547113 := bbase (se 2 (by rfl) ⟨580167, by rfl⟩ : syracuseStep 1547113 = 1160335) (by norm_num)
theorem B2063213 : Blo 1374006 2063213 := bbase (se 3 (by rfl) ⟨386852, by rfl⟩ : syracuseStep 2063213 = 773705) (by norm_num)
theorem B2063237 : Blo 1374006 2063237 := bbase (se 4 (by rfl) ⟨193428, by rfl⟩ : syracuseStep 2063237 = 386857) (by norm_num)
theorem B1547149 : Blo 1374006 1547149 := bbase (se 3 (by rfl) ⟨290090, by rfl⟩ : syracuseStep 1547149 = 580181) (by norm_num)
theorem B1547185 : Blo 1374006 1547185 := bbase (se 2 (by rfl) ⟨580194, by rfl⟩ : syracuseStep 1547185 = 1160389) (by norm_num)
theorem B3480509 : Blo 1374006 3480509 := bbase (se 3 (by rfl) ⟨652595, by rfl⟩ : syracuseStep 3480509 = 1305191) (by norm_num)
theorem B4406213 : Blo 1374006 4406213 := bbase (se 4 (by rfl) ⟨413082, by rfl⟩ : syracuseStep 4406213 = 826165) (by norm_num)
theorem B1547221 : Blo 1374006 1547221 := bbase (se 7 (by rfl) ⟨18131, by rfl⟩ : syracuseStep 1547221 = 36263) (by norm_num)
theorem B1547257 : Blo 1374006 1547257 := bbase (se 2 (by rfl) ⟨580221, by rfl⟩ : syracuseStep 1547257 = 1160443) (by norm_num)
theorem B1547293 : Blo 1374006 1547293 := bbase (se 3 (by rfl) ⟨290117, by rfl⟩ : syracuseStep 1547293 = 580235) (by norm_num)
theorem B5217317 : Blo 1374006 5217317 := bbase (se 4 (by rfl) ⟨489123, by rfl⟩ : syracuseStep 5217317 = 978247) (by norm_num)
theorem B1547329 : Blo 1374006 1547329 := bbase (se 2 (by rfl) ⟨580248, by rfl⟩ : syracuseStep 1547329 = 1160497) (by norm_num)
theorem B3914821 : Blo 1374006 3914821 := bbase (se 4 (by rfl) ⟨367014, by rfl⟩ : syracuseStep 3914821 = 734029) (by norm_num)
theorem B1547365 : Blo 1374006 1547365 := bbase (se 4 (by rfl) ⟨145065, by rfl⟩ : syracuseStep 1547365 = 290131) (by norm_num)
theorem B3136637 : Blo 1374006 3136637 := bbase (se 3 (by rfl) ⟨588119, by rfl⟩ : syracuseStep 3136637 = 1176239) (by norm_num)
theorem B1547401 : Blo 1374006 1547401 := bbase (se 2 (by rfl) ⟨580275, by rfl⟩ : syracuseStep 1547401 = 1160551) (by norm_num)
theorem B1547437 : Blo 1374006 1547437 := bbase (se 3 (by rfl) ⟨290144, by rfl⟩ : syracuseStep 1547437 = 580289) (by norm_num)
theorem B2202805 : Blo 1374006 2202805 := bbase (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) (by norm_num)
theorem B1957069 : Blo 1374006 1957069 := bbase (se 3 (by rfl) ⟨366950, by rfl⟩ : syracuseStep 1957069 = 733901) (by norm_num)
theorem B3136781 : Blo 1374006 3136781 := bbase (se 3 (by rfl) ⟨588146, by rfl⟩ : syracuseStep 3136781 = 1176293) (by norm_num)
theorem B3480853 : Blo 1374006 3480853 := bbase (se 6 (by rfl) ⟨81582, by rfl⟩ : syracuseStep 3480853 = 163165) (by norm_num)
theorem B5217605 : Blo 1374006 5217605 := bbase (se 4 (by rfl) ⟨489150, by rfl⟩ : syracuseStep 5217605 = 978301) (by norm_num)
theorem B5954917 : Blo 1374006 5954917 := bbase (se 4 (by rfl) ⟨558273, by rfl⟩ : syracuseStep 5954917 = 1116547) (by norm_num)
theorem B3480965 : Blo 1374006 3480965 := bbase (se 4 (by rfl) ⟨326340, by rfl⟩ : syracuseStep 3480965 = 652681) (by norm_num)
theorem B6962597 : Blo 1374006 6962597 := bbase (se 4 (by rfl) ⟨652743, by rfl⟩ : syracuseStep 6962597 = 1305487) (by norm_num)
theorem B8805941 : Blo 1374006 8805941 := bbase (se 5 (by rfl) ⟨412778, by rfl⟩ : syracuseStep 8805941 = 825557) (by norm_num)
theorem B3481157 : Blo 1374006 3481157 := bbase (se 4 (by rfl) ⟨326358, by rfl⟩ : syracuseStep 3481157 = 652717) (by norm_num)
theorem B3481501 : Blo 1374006 3481501 := bbase (se 3 (by rfl) ⟨652781, by rfl⟩ : syracuseStep 3481501 = 1305563) (by norm_num)
theorem B1957861 : Blo 1374006 1957861 := bbase (se 4 (by rfl) ⟨183549, by rfl⟩ : syracuseStep 1957861 = 367099) (by norm_num)
theorem B1957889 : Blo 1374006 1957889 := bstep (se 2 (by rfl) ⟨734208, by rfl⟩ : syracuseStep 1957889 = 1468417) B1468417
theorem B1957969 : Blo 1374006 1957969 := bstep (se 2 (by rfl) ⟨734238, by rfl⟩ : syracuseStep 1957969 = 1468477) B1468477
theorem B6602957 : Blo 1374006 6602957 := bstep (se 3 (by rfl) ⟨1238054, by rfl⟩ : syracuseStep 6602957 = 2476109) B2476109
theorem B10436849 : Blo 1374006 10436849 := bstep (se 2 (by rfl) ⟨3913818, by rfl⟩ : syracuseStep 10436849 = 7827637) B7827637
theorem B2318753 : Blo 1374006 2318753 := bstep (se 2 (by rfl) ⟨869532, by rfl⟩ : syracuseStep 2318753 = 1739065) B1739065
theorem B5022179 : Blo 1374006 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B2318881 : Blo 1374006 2318881 := bstep (se 2 (by rfl) ⟨869580, by rfl⟩ : syracuseStep 2318881 = 1739161) B1739161
theorem B2318915 : Blo 1374006 2318915 := bstep (se 1 (by rfl) ⟨1739186, by rfl⟩ : syracuseStep 2318915 = 3478373) B3478373
theorem B2351683 : Blo 1374006 2351683 := bstep (se 1 (by rfl) ⟨1763762, by rfl⟩ : syracuseStep 2351683 = 3527525) B3527525
theorem B3916451 : Blo 1374006 3916451 := bstep (se 1 (by rfl) ⟨2937338, by rfl⟩ : syracuseStep 3916451 = 5874677) B5874677
theorem B4637357 : Blo 1374006 4637357 := bstep (se 3 (by rfl) ⟨869504, by rfl⟩ : syracuseStep 4637357 = 1739009) B1739009
theorem B2319043 : Blo 1374006 2319043 := bstep (se 1 (by rfl) ⟨1739282, by rfl⟩ : syracuseStep 2319043 = 3478565) B3478565
theorem B4637411 : Blo 1374006 4637411 := bstep (se 1 (by rfl) ⟨3478058, by rfl⟩ : syracuseStep 4637411 = 6956117) B6956117
theorem B5874403 : Blo 1374006 5874403 := bstep (se 1 (by rfl) ⟨4405802, by rfl⟩ : syracuseStep 5874403 = 8811605) B8811605
theorem B2319185 : Blo 1374006 2319185 := bstep (se 2 (by rfl) ⟨869694, by rfl⟩ : syracuseStep 2319185 = 1739389) B1739389
theorem B2261953 : Blo 1374006 2261953 := bstep (se 2 (by rfl) ⟨848232, by rfl⟩ : syracuseStep 2261953 = 1696465) B1696465
theorem B2319313 : Blo 1374006 2319313 := bstep (se 2 (by rfl) ⟨869742, by rfl⟩ : syracuseStep 2319313 = 1739485) B1739485
theorem B3916781 : Blo 1374006 3916781 := bstep (se 3 (by rfl) ⟨734396, by rfl⟩ : syracuseStep 3916781 = 1468793) B1468793
theorem B4637681 : Blo 1374006 4637681 := bstep (se 2 (by rfl) ⟨1739130, by rfl⟩ : syracuseStep 4637681 = 3478261) B3478261
theorem B2319347 : Blo 1374006 2319347 := bstep (se 1 (by rfl) ⟨1739510, by rfl⟩ : syracuseStep 2319347 = 3479021) B3479021
theorem B3916849 : Blo 1374006 3916849 := bstep (se 2 (by rfl) ⟨1468818, by rfl⟩ : syracuseStep 3916849 = 2937637) B2937637
theorem B1467443 : Blo 1374006 1467443 := bstep (se 1 (by rfl) ⟨1100582, by rfl⟩ : syracuseStep 1467443 = 2201165) B2201165
theorem B11150405 : Blo 1374006 11150405 := bstep (se 4 (by rfl) ⟨1045350, by rfl⟩ : syracuseStep 11150405 = 2090701) B2090701
theorem B4703341 : Blo 1374006 4703341 := bstep (se 3 (by rfl) ⟨881876, by rfl⟩ : syracuseStep 4703341 = 1763753) B1763753
theorem B2319475 : Blo 1374006 2319475 := bstep (se 1 (by rfl) ⟨1739606, by rfl⟩ : syracuseStep 2319475 = 3479213) B3479213
theorem B37618829 : Blo 1374006 37618829 := bstep (se 3 (by rfl) ⟨7053530, by rfl⟩ : syracuseStep 37618829 = 14107061) B14107061
theorem B13214947 : Blo 1374006 13214947 := bstep (se 1 (by rfl) ⟨9911210, by rfl⟩ : syracuseStep 13214947 = 19822421) B19822421
theorem B2319617 : Blo 1374006 2319617 := bstep (se 2 (by rfl) ⟨869856, by rfl⟩ : syracuseStep 2319617 = 1739713) B1739713
theorem B2786563 : Blo 1374006 2786563 := bstep (se 1 (by rfl) ⟨2089922, by rfl⟩ : syracuseStep 2786563 = 4179845) B4179845
theorem B17851661 : Blo 1374006 17851661 := bstep (se 3 (by rfl) ⟨3347186, by rfl⟩ : syracuseStep 17851661 = 6694373) B6694373
theorem B2319745 : Blo 1374006 2319745 := bstep (se 2 (by rfl) ⟨869904, by rfl⟩ : syracuseStep 2319745 = 1739809) B1739809
theorem B2319779 : Blo 1374006 2319779 := bstep (se 1 (by rfl) ⟨1739834, by rfl⟩ : syracuseStep 2319779 = 3479669) B3479669
theorem B5219747 : Blo 1374006 5219747 := bstep (se 1 (by rfl) ⟨3914810, by rfl⟩ : syracuseStep 5219747 = 7829621) B7829621
theorem B5293475 : Blo 1374006 5293475 := bstep (se 1 (by rfl) ⟨3970106, by rfl⟩ : syracuseStep 5293475 = 7940213) B7940213
theorem B5219761 : Blo 1374006 5219761 := bstep (se 2 (by rfl) ⟨1957410, by rfl⟩ : syracuseStep 5219761 = 3914821) B3914821
theorem B10872305 : Blo 1374006 10872305 := bstep (se 2 (by rfl) ⟨4077114, by rfl⟩ : syracuseStep 10872305 = 8154229) B8154229
theorem B4638221 : Blo 1374006 4638221 := bstep (se 3 (by rfl) ⟨869666, by rfl⟩ : syracuseStep 4638221 = 1739333) B1739333
theorem B2319907 : Blo 1374006 2319907 := bstep (se 1 (by rfl) ⟨1739930, by rfl⟩ : syracuseStep 2319907 = 3479861) B3479861
theorem B4638275 : Blo 1374006 4638275 := bstep (se 1 (by rfl) ⟨3478706, by rfl⟩ : syracuseStep 4638275 = 6957413) B6957413
theorem B4179601 : Blo 1374006 4179601 := bstep (se 2 (by rfl) ⟨1567350, by rfl⟩ : syracuseStep 4179601 = 3134701) B3134701
theorem B2320049 : Blo 1374006 2320049 := bstep (se 2 (by rfl) ⟨870018, by rfl⟩ : syracuseStep 2320049 = 1740037) B1740037
theorem B2320177 : Blo 1374006 2320177 := bstep (se 2 (by rfl) ⟨870066, by rfl⟩ : syracuseStep 2320177 = 1740133) B1740133
theorem B7939889 : Blo 1374006 7939889 := bstep (se 2 (by rfl) ⟨2977458, by rfl⟩ : syracuseStep 7939889 = 5954917) B5954917
theorem B4638545 : Blo 1374006 4638545 := bstep (se 2 (by rfl) ⟨1739454, by rfl⟩ : syracuseStep 4638545 = 3478909) B3478909
theorem B2320211 : Blo 1374006 2320211 := bstep (se 1 (by rfl) ⟨1740158, by rfl⟩ : syracuseStep 2320211 = 3480317) B3480317
theorem B2320339 : Blo 1374006 2320339 := bstep (se 1 (by rfl) ⟨1740254, by rfl⟩ : syracuseStep 2320339 = 3480509) B3480509
theorem B6604877 : Blo 1374006 6604877 := bstep (se 3 (by rfl) ⟨1238414, by rfl⟩ : syracuseStep 6604877 = 2476829) B2476829
theorem B2091091 : Blo 1374006 2091091 := bstep (se 1 (by rfl) ⟨1568318, by rfl⟩ : syracuseStep 2091091 = 3136637) B3136637
theorem B2320481 : Blo 1374006 2320481 := bstep (se 2 (by rfl) ⟨870180, by rfl⟩ : syracuseStep 2320481 = 1740361) B1740361
theorem B2934947 : Blo 1374006 2934947 := bstep (se 1 (by rfl) ⟨2201210, by rfl⟩ : syracuseStep 2934947 = 4402421) B4402421
theorem B2091187 : Blo 1374006 2091187 := bstep (se 1 (by rfl) ⟨1568390, by rfl⟩ : syracuseStep 2091187 = 3136781) B3136781
theorem B2320609 : Blo 1374006 2320609 := bstep (se 2 (by rfl) ⟨870228, by rfl⟩ : syracuseStep 2320609 = 1740457) B1740457
theorem B2320643 : Blo 1374006 2320643 := bstep (se 1 (by rfl) ⟨1740482, by rfl⟩ : syracuseStep 2320643 = 3480965) B3480965
theorem B2935057 : Blo 1374006 2935057 := bstep (se 2 (by rfl) ⟨1100646, by rfl⟩ : syracuseStep 2935057 = 2201293) B2201293
theorem B4639085 : Blo 1374006 4639085 := bstep (se 3 (by rfl) ⟨869828, by rfl⟩ : syracuseStep 4639085 = 1739657) B1739657
theorem B2091377 : Blo 1374006 2091377 := bstep (se 2 (by rfl) ⟨784266, by rfl⟩ : syracuseStep 2091377 = 1568533) B1568533
theorem B2320771 : Blo 1374006 2320771 := bstep (se 1 (by rfl) ⟨1740578, by rfl⟩ : syracuseStep 2320771 = 3481157) B3481157
theorem B1739171 : Blo 1374006 1739171 := bstep (se 1 (by rfl) ⟨1304378, by rfl⟩ : syracuseStep 1739171 = 2608757) B2608757
theorem B4639139 : Blo 1374006 4639139 := bstep (se 1 (by rfl) ⟨3479354, by rfl⟩ : syracuseStep 4639139 = 6958709) B6958709
theorem B7432717 : Blo 1374006 7432717 := bstep (se 3 (by rfl) ⟨1393634, by rfl⟩ : syracuseStep 7432717 = 2787269) B2787269
theorem B2320913 : Blo 1374006 2320913 := bstep (se 2 (by rfl) ⟨870342, by rfl⟩ : syracuseStep 2320913 = 1740685) B1740685
theorem B7825997 : Blo 1374006 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B2321041 : Blo 1374006 2321041 := bstep (se 2 (by rfl) ⟨870390, by rfl⟩ : syracuseStep 2321041 = 1740781) B1740781
theorem B4639409 : Blo 1374006 4639409 := bstep (se 2 (by rfl) ⟨1739778, by rfl⟩ : syracuseStep 4639409 = 3479557) B3479557
theorem B2321075 : Blo 1374006 2321075 := bstep (se 1 (by rfl) ⟨1740806, by rfl⟩ : syracuseStep 2321075 = 3481613) B3481613
theorem B16714421 : Blo 1374006 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B1673939 : Blo 1374006 1673939 := bstep (se 1 (by rfl) ⟨1255454, by rfl⟩ : syracuseStep 1673939 = 2510909) B2510909
theorem B4705091 : Blo 1374006 4705091 := bstep (se 1 (by rfl) ⟨3528818, by rfl⟩ : syracuseStep 4705091 = 7057637) B7057637
theorem B5221219 : Blo 1374006 5221219 := bstep (se 1 (by rfl) ⟨3915914, by rfl⟩ : syracuseStep 5221219 = 7831829) B7831829
theorem B17607779 : Blo 1374006 17607779 := bstep (se 1 (by rfl) ⟨13205834, by rfl⟩ : syracuseStep 17607779 = 26411669) B26411669
theorem B1739875 : Blo 1374006 1739875 := bstep (se 1 (by rfl) ⟨1304906, by rfl⟩ : syracuseStep 1739875 = 2609813) B2609813
theorem B59477105 : Blo 1374006 59477105 := bstep (se 2 (by rfl) ⟨22303914, by rfl⟩ : syracuseStep 59477105 = 44607829) B44607829
theorem B2477233 : Blo 1374006 2477233 := bstep (se 2 (by rfl) ⟨928962, by rfl⟩ : syracuseStep 2477233 = 1857925) B1857925
theorem B1739971 : Blo 1374006 1739971 := bstep (se 1 (by rfl) ⟨1304978, by rfl⟩ : syracuseStep 1739971 = 2609957) B2609957
theorem B8359109 : Blo 1374006 8359109 := bstep (se 4 (by rfl) ⟨783666, by rfl⟩ : syracuseStep 8359109 = 1567333) B1567333
theorem B4639949 : Blo 1374006 4639949 := bstep (se 3 (by rfl) ⟨869990, by rfl⟩ : syracuseStep 4639949 = 1739981) B1739981
theorem B3091697 : Blo 1374006 3091697 := bstep (se 2 (by rfl) ⟨1159386, by rfl⟩ : syracuseStep 3091697 = 2318773) B2318773
theorem B3091715 : Blo 1374006 3091715 := bstep (se 1 (by rfl) ⟨2318786, by rfl⟩ : syracuseStep 3091715 = 4637573) B4637573
theorem B4640003 : Blo 1374006 4640003 := bstep (se 1 (by rfl) ⟨3480002, by rfl⟩ : syracuseStep 4640003 = 6960005) B6960005
theorem B1674499 : Blo 1374006 1674499 := bstep (se 1 (by rfl) ⟨1255874, by rfl⟩ : syracuseStep 1674499 = 2511749) B2511749
theorem B6958385 : Blo 1374006 6958385 := bstep (se 2 (by rfl) ⟨2609394, by rfl⟩ : syracuseStep 6958385 = 5218789) B5218789
theorem B4402637 : Blo 1374006 4402637 := bstep (se 3 (by rfl) ⟨825494, by rfl⟩ : syracuseStep 4402637 = 1650989) B1650989
theorem B2477521 : Blo 1374006 2477521 := bstep (se 2 (by rfl) ⟨929070, by rfl⟩ : syracuseStep 2477521 = 1858141) B1858141
theorem B3091985 : Blo 1374006 3091985 := bstep (se 2 (by rfl) ⟨1159494, by rfl⟩ : syracuseStep 3091985 = 2318989) B2318989
theorem B4640273 : Blo 1374006 4640273 := bstep (se 2 (by rfl) ⟨1740102, by rfl⟩ : syracuseStep 4640273 = 3480205) B3480205
theorem B3092003 : Blo 1374006 3092003 := bstep (se 1 (by rfl) ⟨2319002, by rfl⟩ : syracuseStep 3092003 = 4638005) B4638005
theorem B8474147 : Blo 1374006 8474147 := bstep (se 1 (by rfl) ⟨6355610, by rfl⟩ : syracuseStep 8474147 = 12711221) B12711221
theorem B4402765 : Blo 1374006 4402765 := bstep (se 3 (by rfl) ⟨825518, by rfl⟩ : syracuseStep 4402765 = 1651037) B1651037
theorem B1740467 : Blo 1374006 1740467 := bstep (se 1 (by rfl) ⟨1305350, by rfl⟩ : syracuseStep 1740467 = 2610701) B2610701
theorem B5869361 : Blo 1374006 5869361 := bstep (se 2 (by rfl) ⟨2201010, by rfl⟩ : syracuseStep 5869361 = 4402021) B4402021
theorem B3092273 : Blo 1374006 3092273 := bstep (se 2 (by rfl) ⟨1159602, by rfl⟩ : syracuseStep 3092273 = 2319205) B2319205
theorem B3092291 : Blo 1374006 3092291 := bstep (se 1 (by rfl) ⟨2319218, by rfl⟩ : syracuseStep 3092291 = 4638437) B4638437
theorem B4640813 : Blo 1374006 4640813 := bstep (se 3 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 4640813 = 1740305) B1740305
theorem B3092561 : Blo 1374006 3092561 := bstep (se 2 (by rfl) ⟨1159710, by rfl⟩ : syracuseStep 3092561 = 2319421) B2319421
theorem B3092579 : Blo 1374006 3092579 := bstep (se 1 (by rfl) ⟨2319434, by rfl⟩ : syracuseStep 3092579 = 4638869) B4638869
theorem B4640867 : Blo 1374006 4640867 := bstep (se 1 (by rfl) ⟨3480650, by rfl⟩ : syracuseStep 4640867 = 6961301) B6961301
theorem B1650835 : Blo 1374006 1650835 := bstep (se 1 (by rfl) ⟨1238126, by rfl⟩ : syracuseStep 1650835 = 2476253) B2476253
theorem B3715235 : Blo 1374006 3715235 := bstep (se 1 (by rfl) ⟨2786426, by rfl⟩ : syracuseStep 3715235 = 5572853) B5572853
theorem B2937073 : Blo 1374006 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B2609425 : Blo 1374006 2609425 := bstep (se 2 (by rfl) ⟨978534, by rfl⟩ : syracuseStep 2609425 = 1957069) B1957069
theorem B3092849 : Blo 1374006 3092849 := bstep (se 2 (by rfl) ⟨1159818, by rfl⟩ : syracuseStep 3092849 = 2319637) B2319637
theorem B4641137 : Blo 1374006 4641137 := bstep (se 2 (by rfl) ⟨1740426, by rfl⟩ : syracuseStep 4641137 = 3480853) B3480853
theorem B3092867 : Blo 1374006 3092867 := bstep (se 1 (by rfl) ⟨2319650, by rfl⟩ : syracuseStep 3092867 = 4639301) B4639301
theorem B5870029 : Blo 1374006 5870029 := bstep (se 3 (by rfl) ⟨1100630, by rfl⟩ : syracuseStep 5870029 = 2201261) B2201261
theorem B8811013 : Blo 1374006 8811013 := bstep (se 4 (by rfl) ⟨826032, by rfl⟩ : syracuseStep 8811013 = 1652065) B1652065
theorem B2937475 : Blo 1374006 2937475 := bstep (se 1 (by rfl) ⟨2203106, by rfl⟩ : syracuseStep 2937475 = 4406213) B4406213
theorem B3093137 : Blo 1374006 3093137 := bstep (se 2 (by rfl) ⟨1159926, by rfl⟩ : syracuseStep 3093137 = 2319853) B2319853
theorem B3093155 : Blo 1374006 3093155 := bstep (se 1 (by rfl) ⟨2319866, by rfl⟩ : syracuseStep 3093155 = 4639733) B4639733
theorem B3969713 : Blo 1374006 3969713 := bstep (se 2 (by rfl) ⟨1488642, by rfl⟩ : syracuseStep 3969713 = 2977285) B2977285
theorem B3478211 : Blo 1374006 3478211 := bstep (se 1 (by rfl) ⟨2608658, by rfl⟩ : syracuseStep 3478211 = 5217317) B5217317
theorem B2061011 : Blo 1374006 2061011 := bstep (se 1 (by rfl) ⟨1545758, by rfl⟩ : syracuseStep 2061011 = 3091517) B3091517
theorem B6959843 : Blo 1374006 6959843 := bstep (se 1 (by rfl) ⟨5219882, by rfl⟩ : syracuseStep 6959843 = 10439765) B10439765
theorem B2061041 : Blo 1374006 2061041 := bstep (se 2 (by rfl) ⟨772890, by rfl⟩ : syracuseStep 2061041 = 1545781) B1545781
theorem B2061059 : Blo 1374006 2061059 := bstep (se 1 (by rfl) ⟨1545794, by rfl⟩ : syracuseStep 2061059 = 3091589) B3091589
theorem B2061089 : Blo 1374006 2061089 := bstep (se 2 (by rfl) ⟨772908, by rfl⟩ : syracuseStep 2061089 = 1545817) B1545817
theorem B2061107 : Blo 1374006 2061107 := bstep (se 1 (by rfl) ⟨1545830, by rfl⟩ : syracuseStep 2061107 = 3091661) B3091661
theorem B2061137 : Blo 1374006 2061137 := bstep (se 2 (by rfl) ⟨772926, by rfl⟩ : syracuseStep 2061137 = 1545853) B1545853
theorem B2061155 : Blo 1374006 2061155 := bstep (se 1 (by rfl) ⟨1545866, by rfl⟩ : syracuseStep 2061155 = 3091733) B3091733
theorem B13218673 : Blo 1374006 13218673 := bstep (se 2 (by rfl) ⟨4957002, by rfl⟩ : syracuseStep 13218673 = 9914005) B9914005
theorem B2061185 : Blo 1374006 2061185 := bstep (se 2 (by rfl) ⟨772944, by rfl⟩ : syracuseStep 2061185 = 1545889) B1545889
theorem B3478403 : Blo 1374006 3478403 := bstep (se 1 (by rfl) ⟨2608802, by rfl⟩ : syracuseStep 3478403 = 5217605) B5217605
theorem B4641677 : Blo 1374006 4641677 := bstep (se 3 (by rfl) ⟨870314, by rfl⟩ : syracuseStep 4641677 = 1740629) B1740629
theorem B2061203 : Blo 1374006 2061203 := bstep (se 1 (by rfl) ⟨1545902, by rfl⟩ : syracuseStep 2061203 = 3091805) B3091805
theorem B2061233 : Blo 1374006 2061233 := bstep (se 2 (by rfl) ⟨772962, by rfl⟩ : syracuseStep 2061233 = 1545925) B1545925
theorem B3093425 : Blo 1374006 3093425 := bstep (se 2 (by rfl) ⟨1160034, by rfl⟩ : syracuseStep 3093425 = 2320069) B2320069
theorem B2061251 : Blo 1374006 2061251 := bstep (se 1 (by rfl) ⟨1545938, by rfl⟩ : syracuseStep 2061251 = 3091877) B3091877
theorem B3093443 : Blo 1374006 3093443 := bstep (se 1 (by rfl) ⟨2320082, by rfl⟩ : syracuseStep 3093443 = 4640165) B4640165
theorem B4641731 : Blo 1374006 4641731 := bstep (se 1 (by rfl) ⟨3481298, by rfl⟩ : syracuseStep 4641731 = 6962597) B6962597
theorem B2061281 : Blo 1374006 2061281 := bstep (se 2 (by rfl) ⟨772980, by rfl⟩ : syracuseStep 2061281 = 1545961) B1545961
theorem B2061299 : Blo 1374006 2061299 := bstep (se 1 (by rfl) ⟨1545974, by rfl⟩ : syracuseStep 2061299 = 3091949) B3091949
theorem B2061329 : Blo 1374006 2061329 := bstep (se 2 (by rfl) ⟨772998, by rfl⟩ : syracuseStep 2061329 = 1545997) B1545997
theorem B2061347 : Blo 1374006 2061347 := bstep (se 1 (by rfl) ⟨1546010, by rfl⟩ : syracuseStep 2061347 = 3092021) B3092021
theorem B5870627 : Blo 1374006 5870627 := bstep (se 1 (by rfl) ⟨4402970, by rfl⟩ : syracuseStep 5870627 = 8805941) B8805941
theorem B3912749 : Blo 1374006 3912749 := bstep (se 3 (by rfl) ⟨733640, by rfl⟩ : syracuseStep 3912749 = 1467281) B1467281
theorem B2061377 : Blo 1374006 2061377 := bstep (se 2 (by rfl) ⟨773016, by rfl⟩ : syracuseStep 2061377 = 1546033) B1546033
theorem B2061395 : Blo 1374006 2061395 := bstep (se 1 (by rfl) ⟨1546046, by rfl⟩ : syracuseStep 2061395 = 3092093) B3092093
theorem B2061425 : Blo 1374006 2061425 := bstep (se 2 (by rfl) ⟨773034, by rfl⟩ : syracuseStep 2061425 = 1546069) B1546069
theorem B2061443 : Blo 1374006 2061443 := bstep (se 1 (by rfl) ⟨1546082, by rfl⟩ : syracuseStep 2061443 = 3092165) B3092165
theorem B2061473 : Blo 1374006 2061473 := bstep (se 2 (by rfl) ⟨773052, by rfl⟩ : syracuseStep 2061473 = 1546105) B1546105
theorem B2061491 : Blo 1374006 2061491 := bstep (se 1 (by rfl) ⟨1546118, by rfl⟩ : syracuseStep 2061491 = 3092237) B3092237
theorem B2061521 : Blo 1374006 2061521 := bstep (se 2 (by rfl) ⟨773070, by rfl⟩ : syracuseStep 2061521 = 1546141) B1546141
theorem B3093713 : Blo 1374006 3093713 := bstep (se 2 (by rfl) ⟨1160142, by rfl⟩ : syracuseStep 3093713 = 2320285) B2320285
theorem B4642001 : Blo 1374006 4642001 := bstep (se 2 (by rfl) ⟨1740750, by rfl⟩ : syracuseStep 4642001 = 3481501) B3481501
theorem B2061539 : Blo 1374006 2061539 := bstep (se 1 (by rfl) ⟨1546154, by rfl⟩ : syracuseStep 2061539 = 3092309) B3092309
theorem B3093731 : Blo 1374006 3093731 := bstep (se 1 (by rfl) ⟨2320298, by rfl⟩ : syracuseStep 3093731 = 4640597) B4640597
theorem B16954595 : Blo 1374006 16954595 := bstep (se 1 (by rfl) ⟨12715946, by rfl⟩ : syracuseStep 16954595 = 25431893) B25431893
theorem B2061569 : Blo 1374006 2061569 := bstep (se 2 (by rfl) ⟨773088, by rfl⟩ : syracuseStep 2061569 = 1546177) B1546177
theorem B2061587 : Blo 1374006 2061587 := bstep (se 1 (by rfl) ⟨1546190, by rfl⟩ : syracuseStep 2061587 = 3092381) B3092381
theorem B2061617 : Blo 1374006 2061617 := bstep (se 2 (by rfl) ⟨773106, by rfl⟩ : syracuseStep 2061617 = 1546213) B1546213
theorem B2610481 : Blo 1374006 2610481 := bstep (se 2 (by rfl) ⟨978930, by rfl⟩ : syracuseStep 2610481 = 1957861) B1957861
theorem B2061635 : Blo 1374006 2061635 := bstep (se 1 (by rfl) ⟨1546226, by rfl⟩ : syracuseStep 2061635 = 3092453) B3092453
theorem B2061665 : Blo 1374006 2061665 := bstep (se 2 (by rfl) ⟨773124, by rfl⟩ : syracuseStep 2061665 = 1546249) B1546249
theorem B2061683 : Blo 1374006 2061683 := bstep (se 1 (by rfl) ⟨1546262, by rfl⟩ : syracuseStep 2061683 = 3092525) B3092525
theorem B1529203 : Blo 1374006 1529203 := bstep (se 1 (by rfl) ⟨1146902, by rfl⟩ : syracuseStep 1529203 = 2293805) B2293805
theorem B4404611 : Blo 1374006 4404611 := bstep (se 1 (by rfl) ⟨3303458, by rfl⟩ : syracuseStep 4404611 = 6606917) B6606917
theorem B10433933 : Blo 1374006 10433933 := bstep (se 3 (by rfl) ⟨1956362, by rfl⟩ : syracuseStep 10433933 = 3912725) B3912725
theorem B12719501 : Blo 1374006 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B2061713 : Blo 1374006 2061713 := bstep (se 2 (by rfl) ⟨773142, by rfl⟩ : syracuseStep 2061713 = 1546285) B1546285
theorem B2061731 : Blo 1374006 2061731 := bstep (se 1 (by rfl) ⟨1546298, by rfl⟩ : syracuseStep 2061731 = 3092597) B3092597
theorem B7828913 : Blo 1374006 7828913 := bstep (se 2 (by rfl) ⟨2935842, by rfl⟩ : syracuseStep 7828913 = 5871685) B5871685
theorem B2061761 : Blo 1374006 2061761 := bstep (se 2 (by rfl) ⟨773160, by rfl⟩ : syracuseStep 2061761 = 1546321) B1546321
theorem B2061779 : Blo 1374006 2061779 := bstep (se 1 (by rfl) ⟨1546334, by rfl⟩ : syracuseStep 2061779 = 3092669) B3092669
theorem B2061809 : Blo 1374006 2061809 := bstep (se 2 (by rfl) ⟨773178, by rfl⟩ : syracuseStep 2061809 = 1546357) B1546357
theorem B3094001 : Blo 1374006 3094001 := bstep (se 2 (by rfl) ⟨1160250, by rfl⟩ : syracuseStep 3094001 = 2320501) B2320501
theorem B2061827 : Blo 1374006 2061827 := bstep (se 1 (by rfl) ⟨1546370, by rfl⟩ : syracuseStep 2061827 = 3092741) B3092741
theorem B4404739 : Blo 1374006 4404739 := bstep (se 1 (by rfl) ⟨3303554, by rfl⟩ : syracuseStep 4404739 = 6607109) B6607109
theorem B3094019 : Blo 1374006 3094019 := bstep (se 1 (by rfl) ⟨2320514, by rfl⟩ : syracuseStep 3094019 = 4641029) B4641029
theorem B6960653 : Blo 1374006 6960653 := bstep (se 3 (by rfl) ⟨1305122, by rfl⟩ : syracuseStep 6960653 = 2610245) B2610245
theorem B2061857 : Blo 1374006 2061857 := bstep (se 2 (by rfl) ⟨773196, by rfl⟩ : syracuseStep 2061857 = 1546393) B1546393
theorem B1545763 : Blo 1374006 1545763 := bstep (se 1 (by rfl) ⟨1159322, by rfl⟩ : syracuseStep 1545763 = 2318645) B2318645
theorem B2061875 : Blo 1374006 2061875 := bstep (se 1 (by rfl) ⟨1546406, by rfl⟩ : syracuseStep 2061875 = 3092813) B3092813
theorem B25081397 : Blo 1374006 25081397 := bstep (se 5 (by rfl) ⟨1175690, by rfl⟩ : syracuseStep 25081397 = 2351381) B2351381
theorem B2061905 : Blo 1374006 2061905 := bstep (se 2 (by rfl) ⟨773214, by rfl⟩ : syracuseStep 2061905 = 1546429) B1546429
theorem B2061923 : Blo 1374006 2061923 := bstep (se 1 (by rfl) ⟨1546442, by rfl⟩ : syracuseStep 2061923 = 3092885) B3092885
theorem B2061953 : Blo 1374006 2061953 := bstep (se 2 (by rfl) ⟨773232, by rfl⟩ : syracuseStep 2061953 = 1546465) B1546465
theorem B4404881 : Blo 1374006 4404881 := bstep (se 2 (by rfl) ⟨1651830, by rfl⟩ : syracuseStep 4404881 = 3303661) B3303661
theorem B2061971 : Blo 1374006 2061971 := bstep (se 1 (by rfl) ⟨1546478, by rfl⟩ : syracuseStep 2061971 = 3092957) B3092957
theorem B2062001 : Blo 1374006 2062001 := bstep (se 2 (by rfl) ⟨773250, by rfl⟩ : syracuseStep 2062001 = 1546501) B1546501
theorem B1545907 : Blo 1374006 1545907 := bstep (se 1 (by rfl) ⟨1159430, by rfl⟩ : syracuseStep 1545907 = 2318861) B2318861
theorem B2201267 : Blo 1374006 2201267 := bstep (se 1 (by rfl) ⟨1650950, by rfl⟩ : syracuseStep 2201267 = 3301901) B3301901
theorem B2062019 : Blo 1374006 2062019 := bstep (se 1 (by rfl) ⟨1546514, by rfl⟩ : syracuseStep 2062019 = 3093029) B3093029
theorem B2610883 : Blo 1374006 2610883 := bstep (se 1 (by rfl) ⟨1958162, by rfl⟩ : syracuseStep 2610883 = 3916325) B3916325
theorem B2062049 : Blo 1374006 2062049 := bstep (se 2 (by rfl) ⟨773268, by rfl⟩ : syracuseStep 2062049 = 1546537) B1546537
theorem B2610929 : Blo 1374006 2610929 := bstep (se 2 (by rfl) ⟨979098, by rfl⟩ : syracuseStep 2610929 = 1958197) B1958197
theorem B2062067 : Blo 1374006 2062067 := bstep (se 1 (by rfl) ⟨1546550, by rfl⟩ : syracuseStep 2062067 = 3093101) B3093101
theorem B4404995 : Blo 1374006 4404995 := bstep (se 1 (by rfl) ⟨3303746, by rfl⟩ : syracuseStep 4404995 = 6607493) B6607493
theorem B2062097 : Blo 1374006 2062097 := bstep (se 2 (by rfl) ⟨773286, by rfl⟩ : syracuseStep 2062097 = 1546573) B1546573
theorem B3094289 : Blo 1374006 3094289 := bstep (se 2 (by rfl) ⟨1160358, by rfl⟩ : syracuseStep 3094289 = 2320717) B2320717
theorem B2062115 : Blo 1374006 2062115 := bstep (se 1 (by rfl) ⟨1546586, by rfl⟩ : syracuseStep 2062115 = 3093173) B3093173
theorem B3094307 : Blo 1374006 3094307 := bstep (se 1 (by rfl) ⟨2320730, by rfl⟩ : syracuseStep 3094307 = 4641461) B4641461
theorem B3479345 : Blo 1374006 3479345 := bstep (se 2 (by rfl) ⟨1304754, by rfl⟩ : syracuseStep 3479345 = 2609509) B2609509
theorem B2062145 : Blo 1374006 2062145 := bstep (se 2 (by rfl) ⟨773304, by rfl⟩ : syracuseStep 2062145 = 1546609) B1546609
theorem B1374019 : Blo 1374006 1374019 := bstep (se 1 (by rfl) ⟨1030514, by rfl⟩ : syracuseStep 1374019 = 2061029) B2061029
theorem B1546051 : Blo 1374006 1546051 := bstep (se 1 (by rfl) ⟨1159538, by rfl⟩ : syracuseStep 1546051 = 2319077) B2319077
theorem B1374035 : Blo 1374006 1374035 := bstep (se 1 (by rfl) ⟨1030526, by rfl⟩ : syracuseStep 1374035 = 2061053) B2061053
theorem B2062163 : Blo 1374006 2062163 := bstep (se 1 (by rfl) ⟨1546622, by rfl⟩ : syracuseStep 2062163 = 3093245) B3093245
theorem B1374051 : Blo 1374006 1374051 := bstep (se 1 (by rfl) ⟨1030538, by rfl⟩ : syracuseStep 1374051 = 2061077) B2061077
theorem B3479395 : Blo 1374006 3479395 := bstep (se 1 (by rfl) ⟨2609546, by rfl⟩ : syracuseStep 3479395 = 5219093) B5219093
theorem B2062193 : Blo 1374006 2062193 := bstep (se 2 (by rfl) ⟨773322, by rfl⟩ : syracuseStep 2062193 = 1546645) B1546645
theorem B1374067 : Blo 1374006 1374067 := bstep (se 1 (by rfl) ⟨1030550, by rfl⟩ : syracuseStep 1374067 = 2061101) B2061101
theorem B1374083 : Blo 1374006 1374083 := bstep (se 1 (by rfl) ⟨1030562, by rfl⟩ : syracuseStep 1374083 = 2061125) B2061125
theorem B2062211 : Blo 1374006 2062211 := bstep (se 1 (by rfl) ⟨1546658, by rfl⟩ : syracuseStep 2062211 = 3093317) B3093317
theorem B29718413 : Blo 1374006 29718413 := bstep (se 3 (by rfl) ⟨5572202, by rfl⟩ : syracuseStep 29718413 = 11144405) B11144405
theorem B6272909 : Blo 1374006 6272909 := bstep (se 3 (by rfl) ⟨1176170, by rfl⟩ : syracuseStep 6272909 = 2352341) B2352341
theorem B1374099 : Blo 1374006 1374099 := bstep (se 1 (by rfl) ⟨1030574, by rfl⟩ : syracuseStep 1374099 = 2061149) B2061149
theorem B2062241 : Blo 1374006 2062241 := bstep (se 2 (by rfl) ⟨773340, by rfl⟩ : syracuseStep 2062241 = 1546681) B1546681
theorem B1374115 : Blo 1374006 1374115 := bstep (se 1 (by rfl) ⟨1030586, by rfl⟩ : syracuseStep 1374115 = 2061173) B2061173
theorem B1374131 : Blo 1374006 1374131 := bstep (se 1 (by rfl) ⟨1030598, by rfl⟩ : syracuseStep 1374131 = 2061197) B2061197
theorem B2062259 : Blo 1374006 2062259 := bstep (se 1 (by rfl) ⟨1546694, by rfl⟩ : syracuseStep 2062259 = 3093389) B3093389
theorem B1374147 : Blo 1374006 1374147 := bstep (se 1 (by rfl) ⟨1030610, by rfl⟩ : syracuseStep 1374147 = 2061221) B2061221
theorem B2062289 : Blo 1374006 2062289 := bstep (se 2 (by rfl) ⟨773358, by rfl⟩ : syracuseStep 2062289 = 1546717) B1546717
theorem B1374163 : Blo 1374006 1374163 := bstep (se 1 (by rfl) ⟨1030622, by rfl⟩ : syracuseStep 1374163 = 2061245) B2061245
theorem B1546195 : Blo 1374006 1546195 := bstep (se 1 (by rfl) ⟨1159646, by rfl⟩ : syracuseStep 1546195 = 2319293) B2319293
theorem B1374179 : Blo 1374006 1374179 := bstep (se 1 (by rfl) ⟨1030634, by rfl⟩ : syracuseStep 1374179 = 2061269) B2061269
theorem B2062307 : Blo 1374006 2062307 := bstep (se 1 (by rfl) ⟨1546730, by rfl⟩ : syracuseStep 2062307 = 3093461) B3093461
theorem B3479537 : Blo 1374006 3479537 := bstep (se 2 (by rfl) ⟨1304826, by rfl⟩ : syracuseStep 3479537 = 2609653) B2609653
theorem B1374195 : Blo 1374006 1374195 := bstep (se 1 (by rfl) ⟨1030646, by rfl⟩ : syracuseStep 1374195 = 2061293) B2061293
theorem B2062337 : Blo 1374006 2062337 := bstep (se 2 (by rfl) ⟨773376, by rfl⟩ : syracuseStep 2062337 = 1546753) B1546753
theorem B1374211 : Blo 1374006 1374211 := bstep (se 1 (by rfl) ⟨1030658, by rfl⟩ : syracuseStep 1374211 = 2061317) B2061317
theorem B2611217 : Blo 1374006 2611217 := bstep (se 2 (by rfl) ⟨979206, by rfl⟩ : syracuseStep 2611217 = 1958413) B1958413
theorem B1374227 : Blo 1374006 1374227 := bstep (se 1 (by rfl) ⟨1030670, by rfl⟩ : syracuseStep 1374227 = 2061341) B2061341
theorem B2062355 : Blo 1374006 2062355 := bstep (se 1 (by rfl) ⟨1546766, by rfl⟩ : syracuseStep 2062355 = 3093533) B3093533
theorem B1374243 : Blo 1374006 1374243 := bstep (se 1 (by rfl) ⟨1030682, by rfl⟩ : syracuseStep 1374243 = 2061365) B2061365
theorem B2062385 : Blo 1374006 2062385 := bstep (se 2 (by rfl) ⟨773394, by rfl⟩ : syracuseStep 2062385 = 1546789) B1546789
theorem B3094577 : Blo 1374006 3094577 := bstep (se 2 (by rfl) ⟨1160466, by rfl⟩ : syracuseStep 3094577 = 2320933) B2320933
theorem B1374259 : Blo 1374006 1374259 := bstep (se 1 (by rfl) ⟨1030694, by rfl⟩ : syracuseStep 1374259 = 2061389) B2061389
theorem B1374275 : Blo 1374006 1374275 := bstep (se 1 (by rfl) ⟨1030706, by rfl⟩ : syracuseStep 1374275 = 2061413) B2061413
theorem B2062403 : Blo 1374006 2062403 := bstep (se 1 (by rfl) ⟨1546802, by rfl⟩ : syracuseStep 2062403 = 3093605) B3093605
theorem B3094595 : Blo 1374006 3094595 := bstep (se 1 (by rfl) ⟨2320946, by rfl⟩ : syracuseStep 3094595 = 4641893) B4641893
theorem B1374291 : Blo 1374006 1374291 := bstep (se 1 (by rfl) ⟨1030718, by rfl⟩ : syracuseStep 1374291 = 2061437) B2061437
theorem B2062433 : Blo 1374006 2062433 := bstep (se 2 (by rfl) ⟨773412, by rfl⟩ : syracuseStep 2062433 = 1546825) B1546825
theorem B1374307 : Blo 1374006 1374307 := bstep (se 1 (by rfl) ⟨1030730, by rfl⟩ : syracuseStep 1374307 = 2061461) B2061461
theorem B1546339 : Blo 1374006 1546339 := bstep (se 1 (by rfl) ⟨1159754, by rfl⟩ : syracuseStep 1546339 = 2319509) B2319509
theorem B5093489 : Blo 1374006 5093489 := bstep (se 2 (by rfl) ⟨1910058, by rfl⟩ : syracuseStep 5093489 = 3820117) B3820117
theorem B1374323 : Blo 1374006 1374323 := bstep (se 1 (by rfl) ⟨1030742, by rfl⟩ : syracuseStep 1374323 = 2061485) B2061485
theorem B2062451 : Blo 1374006 2062451 := bstep (se 1 (by rfl) ⟨1546838, by rfl⟩ : syracuseStep 2062451 = 3093677) B3093677
theorem B1374339 : Blo 1374006 1374339 := bstep (se 1 (by rfl) ⟨1030754, by rfl⟩ : syracuseStep 1374339 = 2061509) B2061509
theorem B2062481 : Blo 1374006 2062481 := bstep (se 2 (by rfl) ⟨773430, by rfl⟩ : syracuseStep 2062481 = 1546861) B1546861
theorem B1374355 : Blo 1374006 1374355 := bstep (se 1 (by rfl) ⟨1030766, by rfl⟩ : syracuseStep 1374355 = 2061533) B2061533
theorem B1374371 : Blo 1374006 1374371 := bstep (se 1 (by rfl) ⟨1030778, by rfl⟩ : syracuseStep 1374371 = 2061557) B2061557
theorem B2062499 : Blo 1374006 2062499 := bstep (se 1 (by rfl) ⟨1546874, by rfl⟩ : syracuseStep 2062499 = 3093749) B3093749
theorem B1374387 : Blo 1374006 1374387 := bstep (se 1 (by rfl) ⟨1030790, by rfl⟩ : syracuseStep 1374387 = 2061581) B2061581
theorem B2062529 : Blo 1374006 2062529 := bstep (se 2 (by rfl) ⟨773448, by rfl⟩ : syracuseStep 2062529 = 1546897) B1546897
theorem B1374403 : Blo 1374006 1374403 := bstep (se 1 (by rfl) ⟨1030802, by rfl⟩ : syracuseStep 1374403 = 2061605) B2061605
theorem B16718021 : Blo 1374006 16718021 := bstep (se 4 (by rfl) ⟨1567314, by rfl⟩ : syracuseStep 16718021 = 3134629) B3134629
theorem B3913933 : Blo 1374006 3913933 := bstep (se 3 (by rfl) ⟨733862, by rfl⟩ : syracuseStep 3913933 = 1467725) B1467725
theorem B1374419 : Blo 1374006 1374419 := bstep (se 1 (by rfl) ⟨1030814, by rfl⟩ : syracuseStep 1374419 = 2061629) B2061629
theorem B2062547 : Blo 1374006 2062547 := bstep (se 1 (by rfl) ⟨1546910, by rfl⟩ : syracuseStep 2062547 = 3093821) B3093821
theorem B1374435 : Blo 1374006 1374435 := bstep (se 1 (by rfl) ⟨1030826, by rfl⟩ : syracuseStep 1374435 = 2061653) B2061653
theorem B1857763 : Blo 1374006 1857763 := bstep (se 1 (by rfl) ⟨1393322, by rfl⟩ : syracuseStep 1857763 = 2786645) B2786645
theorem B2062577 : Blo 1374006 2062577 := bstep (se 2 (by rfl) ⟨773466, by rfl⟩ : syracuseStep 2062577 = 1546933) B1546933
theorem B1374451 : Blo 1374006 1374451 := bstep (se 1 (by rfl) ⟨1030838, by rfl⟩ : syracuseStep 1374451 = 2061677) B2061677
theorem B1546483 : Blo 1374006 1546483 := bstep (se 1 (by rfl) ⟨1159862, by rfl⟩ : syracuseStep 1546483 = 2319725) B2319725
theorem B1374467 : Blo 1374006 1374467 := bstep (se 1 (by rfl) ⟨1030850, by rfl⟩ : syracuseStep 1374467 = 2061701) B2061701
theorem B2062595 : Blo 1374006 2062595 := bstep (se 1 (by rfl) ⟨1546946, by rfl⟩ : syracuseStep 2062595 = 3093893) B3093893
theorem B1374483 : Blo 1374006 1374483 := bstep (se 1 (by rfl) ⟨1030862, by rfl⟩ : syracuseStep 1374483 = 2061725) B2061725
theorem B2062625 : Blo 1374006 2062625 := bstep (se 2 (by rfl) ⟨773484, by rfl⟩ : syracuseStep 2062625 = 1546969) B1546969
theorem B1374499 : Blo 1374006 1374499 := bstep (se 1 (by rfl) ⟨1030874, by rfl⟩ : syracuseStep 1374499 = 2061749) B2061749
theorem B1374515 : Blo 1374006 1374515 := bstep (se 1 (by rfl) ⟨1030886, by rfl⟩ : syracuseStep 1374515 = 2061773) B2061773
theorem B2062643 : Blo 1374006 2062643 := bstep (se 1 (by rfl) ⟨1546982, by rfl⟩ : syracuseStep 2062643 = 3093965) B3093965
theorem B1374531 : Blo 1374006 1374531 := bstep (se 1 (by rfl) ⟨1030898, by rfl⟩ : syracuseStep 1374531 = 2061797) B2061797
theorem B2062673 : Blo 1374006 2062673 := bstep (se 2 (by rfl) ⟨773502, by rfl⟩ : syracuseStep 2062673 = 1547005) B1547005
theorem B3094865 : Blo 1374006 3094865 := bstep (se 2 (by rfl) ⟨1160574, by rfl⟩ : syracuseStep 3094865 = 2321149) B2321149
theorem B1374547 : Blo 1374006 1374547 := bstep (se 1 (by rfl) ⟨1030910, by rfl⟩ : syracuseStep 1374547 = 2061821) B2061821
theorem B1374563 : Blo 1374006 1374563 := bstep (se 1 (by rfl) ⟨1030922, by rfl⟩ : syracuseStep 1374563 = 2061845) B2061845
theorem B2062691 : Blo 1374006 2062691 := bstep (se 1 (by rfl) ⟨1547018, by rfl⟩ : syracuseStep 2062691 = 3094037) B3094037
theorem B3094883 : Blo 1374006 3094883 := bstep (se 1 (by rfl) ⟨2321162, by rfl⟩ : syracuseStep 3094883 = 4642325) B4642325
theorem B1374579 : Blo 1374006 1374579 := bstep (se 1 (by rfl) ⟨1030934, by rfl⟩ : syracuseStep 1374579 = 2061869) B2061869
theorem B2062721 : Blo 1374006 2062721 := bstep (se 2 (by rfl) ⟨773520, by rfl⟩ : syracuseStep 2062721 = 1547041) B1547041
theorem B1374595 : Blo 1374006 1374595 := bstep (se 1 (by rfl) ⟨1030946, by rfl⟩ : syracuseStep 1374595 = 2061893) B2061893
theorem B1546627 : Blo 1374006 1546627 := bstep (se 1 (by rfl) ⟨1159970, by rfl⟩ : syracuseStep 1546627 = 2319941) B2319941
theorem B1374611 : Blo 1374006 1374611 := bstep (se 1 (by rfl) ⟨1030958, by rfl⟩ : syracuseStep 1374611 = 2061917) B2061917
theorem B2062739 : Blo 1374006 2062739 := bstep (se 1 (by rfl) ⟨1547054, by rfl⟩ : syracuseStep 2062739 = 3094109) B3094109
theorem B1374627 : Blo 1374006 1374627 := bstep (se 1 (by rfl) ⟨1030970, by rfl⟩ : syracuseStep 1374627 = 2061941) B2061941
theorem B2062769 : Blo 1374006 2062769 := bstep (se 2 (by rfl) ⟨773538, by rfl⟩ : syracuseStep 2062769 = 1547077) B1547077
theorem B1374643 : Blo 1374006 1374643 := bstep (se 1 (by rfl) ⟨1030982, by rfl⟩ : syracuseStep 1374643 = 2061965) B2061965
theorem B1374659 : Blo 1374006 1374659 := bstep (se 1 (by rfl) ⟨1030994, by rfl⟩ : syracuseStep 1374659 = 2061989) B2061989
theorem B18815429 : Blo 1374006 18815429 := bstep (se 4 (by rfl) ⟨1763946, by rfl⟩ : syracuseStep 18815429 = 3527893) B3527893
theorem B2062787 : Blo 1374006 2062787 := bstep (se 1 (by rfl) ⟨1547090, by rfl⟩ : syracuseStep 2062787 = 3094181) B3094181
theorem B1374675 : Blo 1374006 1374675 := bstep (se 1 (by rfl) ⟨1031006, by rfl⟩ : syracuseStep 1374675 = 2062013) B2062013
theorem B2062817 : Blo 1374006 2062817 := bstep (se 2 (by rfl) ⟨773556, by rfl⟩ : syracuseStep 2062817 = 1547113) B1547113
theorem B1374691 : Blo 1374006 1374691 := bstep (se 1 (by rfl) ⟨1031018, by rfl⟩ : syracuseStep 1374691 = 2062037) B2062037
theorem B1374707 : Blo 1374006 1374707 := bstep (se 1 (by rfl) ⟨1031030, by rfl⟩ : syracuseStep 1374707 = 2062061) B2062061
theorem B2062835 : Blo 1374006 2062835 := bstep (se 1 (by rfl) ⟨1547126, by rfl⟩ : syracuseStep 2062835 = 3094253) B3094253
theorem B2202113 : Blo 1374006 2202113 := bstep (se 2 (by rfl) ⟨825792, by rfl⟩ : syracuseStep 2202113 = 1651585) B1651585
theorem B1374723 : Blo 1374006 1374723 := bstep (se 1 (by rfl) ⟨1031042, by rfl⟩ : syracuseStep 1374723 = 2062085) B2062085
theorem B2062865 : Blo 1374006 2062865 := bstep (se 2 (by rfl) ⟨773574, by rfl⟩ : syracuseStep 2062865 = 1547149) B1547149
theorem B1374739 : Blo 1374006 1374739 := bstep (se 1 (by rfl) ⟨1031054, by rfl⟩ : syracuseStep 1374739 = 2062109) B2062109
theorem B1546771 : Blo 1374006 1546771 := bstep (se 1 (by rfl) ⟨1160078, by rfl⟩ : syracuseStep 1546771 = 2320157) B2320157
theorem B1374755 : Blo 1374006 1374755 := bstep (se 1 (by rfl) ⟨1031066, by rfl⟩ : syracuseStep 1374755 = 2062133) B2062133
theorem B2062883 : Blo 1374006 2062883 := bstep (se 1 (by rfl) ⟨1547162, by rfl⟩ : syracuseStep 2062883 = 3094325) B3094325
theorem B1956403 : Blo 1374006 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B1374771 : Blo 1374006 1374771 := bstep (se 1 (by rfl) ⟨1031078, by rfl⟩ : syracuseStep 1374771 = 2062157) B2062157
theorem B2062913 : Blo 1374006 2062913 := bstep (se 2 (by rfl) ⟨773592, by rfl⟩ : syracuseStep 2062913 = 1547185) B1547185
theorem B1374787 : Blo 1374006 1374787 := bstep (se 1 (by rfl) ⟨1031090, by rfl⟩ : syracuseStep 1374787 = 2062181) B2062181
theorem B1374803 : Blo 1374006 1374803 := bstep (se 1 (by rfl) ⟨1031102, by rfl⟩ : syracuseStep 1374803 = 2062205) B2062205
theorem B2062931 : Blo 1374006 2062931 := bstep (se 1 (by rfl) ⟨1547198, by rfl⟩ : syracuseStep 2062931 = 3094397) B3094397
theorem B1374819 : Blo 1374006 1374819 := bstep (se 1 (by rfl) ⟨1031114, by rfl⟩ : syracuseStep 1374819 = 2062229) B2062229
theorem B2062961 : Blo 1374006 2062961 := bstep (se 2 (by rfl) ⟨773610, by rfl⟩ : syracuseStep 2062961 = 1547221) B1547221
theorem B1374835 : Blo 1374006 1374835 := bstep (se 1 (by rfl) ⟨1031126, by rfl⟩ : syracuseStep 1374835 = 2062253) B2062253
theorem B1374851 : Blo 1374006 1374851 := bstep (se 1 (by rfl) ⟨1031138, by rfl⟩ : syracuseStep 1374851 = 2062277) B2062277
theorem B2062979 : Blo 1374006 2062979 := bstep (se 1 (by rfl) ⟨1547234, by rfl⟩ : syracuseStep 2062979 = 3094469) B3094469
theorem B1374867 : Blo 1374006 1374867 := bstep (se 1 (by rfl) ⟨1031150, by rfl⟩ : syracuseStep 1374867 = 2062301) B2062301
theorem B2063009 : Blo 1374006 2063009 := bstep (se 2 (by rfl) ⟨773628, by rfl⟩ : syracuseStep 2063009 = 1547257) B1547257
theorem B1374883 : Blo 1374006 1374883 := bstep (se 1 (by rfl) ⟨1031162, by rfl⟩ : syracuseStep 1374883 = 2062325) B2062325
theorem B1546915 : Blo 1374006 1546915 := bstep (se 1 (by rfl) ⟨1160186, by rfl⟩ : syracuseStep 1546915 = 2320373) B2320373
theorem B1374899 : Blo 1374006 1374899 := bstep (se 1 (by rfl) ⟨1031174, by rfl⟩ : syracuseStep 1374899 = 2062349) B2062349
theorem B2063027 : Blo 1374006 2063027 := bstep (se 1 (by rfl) ⟨1547270, by rfl⟩ : syracuseStep 2063027 = 3094541) B3094541
theorem B1374915 : Blo 1374006 1374915 := bstep (se 1 (by rfl) ⟨1031186, by rfl⟩ : syracuseStep 1374915 = 2062373) B2062373
theorem B2063057 : Blo 1374006 2063057 := bstep (se 2 (by rfl) ⟨773646, by rfl⟩ : syracuseStep 2063057 = 1547293) B1547293
theorem B1374931 : Blo 1374006 1374931 := bstep (se 1 (by rfl) ⟨1031198, by rfl⟩ : syracuseStep 1374931 = 2062397) B2062397
theorem B8043235 : Blo 1374006 8043235 := bstep (se 1 (by rfl) ⟨6032426, by rfl⟩ : syracuseStep 8043235 = 12064853) B12064853
theorem B1374947 : Blo 1374006 1374947 := bstep (se 1 (by rfl) ⟨1031210, by rfl⟩ : syracuseStep 1374947 = 2062421) B2062421
theorem B2063075 : Blo 1374006 2063075 := bstep (se 1 (by rfl) ⟨1547306, by rfl⟩ : syracuseStep 2063075 = 3094613) B3094613
theorem B1374963 : Blo 1374006 1374963 := bstep (se 1 (by rfl) ⟨1031222, by rfl⟩ : syracuseStep 1374963 = 2062445) B2062445
theorem B2063105 : Blo 1374006 2063105 := bstep (se 2 (by rfl) ⟨773664, by rfl⟩ : syracuseStep 2063105 = 1547329) B1547329
theorem B1374979 : Blo 1374006 1374979 := bstep (se 1 (by rfl) ⟨1031234, by rfl⟩ : syracuseStep 1374979 = 2062469) B2062469
theorem B1374995 : Blo 1374006 1374995 := bstep (se 1 (by rfl) ⟨1031246, by rfl⟩ : syracuseStep 1374995 = 2062493) B2062493
theorem B2063123 : Blo 1374006 2063123 := bstep (se 1 (by rfl) ⟨1547342, by rfl⟩ : syracuseStep 2063123 = 3094685) B3094685
theorem B33905429 : Blo 1374006 33905429 := bstep (se 6 (by rfl) ⟨794658, by rfl⟩ : syracuseStep 33905429 = 1589317) B1589317
theorem B1375011 : Blo 1374006 1375011 := bstep (se 1 (by rfl) ⟨1031258, by rfl⟩ : syracuseStep 1375011 = 2062517) B2062517
theorem B2063153 : Blo 1374006 2063153 := bstep (se 2 (by rfl) ⟨773682, by rfl⟩ : syracuseStep 2063153 = 1547365) B1547365
theorem B1375027 : Blo 1374006 1375027 := bstep (se 1 (by rfl) ⟨1031270, by rfl⟩ : syracuseStep 1375027 = 2062541) B2062541
theorem B1547059 : Blo 1374006 1547059 := bstep (se 1 (by rfl) ⟨1160294, by rfl⟩ : syracuseStep 1547059 = 2320589) B2320589
theorem B1375043 : Blo 1374006 1375043 := bstep (se 1 (by rfl) ⟨1031282, by rfl⟩ : syracuseStep 1375043 = 2062565) B2062565
theorem B2063171 : Blo 1374006 2063171 := bstep (se 1 (by rfl) ⟨1547378, by rfl⟩ : syracuseStep 2063171 = 3094757) B3094757
theorem B1375059 : Blo 1374006 1375059 := bstep (se 1 (by rfl) ⟨1031294, by rfl⟩ : syracuseStep 1375059 = 2062589) B2062589
theorem B2063201 : Blo 1374006 2063201 := bstep (se 2 (by rfl) ⟨773700, by rfl⟩ : syracuseStep 2063201 = 1547401) B1547401
theorem B7830371 : Blo 1374006 7830371 := bstep (se 1 (by rfl) ⟨5872778, by rfl⟩ : syracuseStep 7830371 = 11745557) B11745557
theorem B1375075 : Blo 1374006 1375075 := bstep (se 1 (by rfl) ⟨1031306, by rfl⟩ : syracuseStep 1375075 = 2062613) B2062613
theorem B1375091 : Blo 1374006 1375091 := bstep (se 1 (by rfl) ⟨1031318, by rfl⟩ : syracuseStep 1375091 = 2062637) B2062637
theorem B2063219 : Blo 1374006 2063219 := bstep (se 1 (by rfl) ⟨1547414, by rfl⟩ : syracuseStep 2063219 = 3094829) B3094829
theorem B1956739 : Blo 1374006 1956739 := bstep (se 1 (by rfl) ⟨1467554, by rfl⟩ : syracuseStep 1956739 = 2935109) B2935109
theorem B1375107 : Blo 1374006 1375107 := bstep (se 1 (by rfl) ⟨1031330, by rfl⟩ : syracuseStep 1375107 = 2062661) B2062661
theorem B2063249 : Blo 1374006 2063249 := bstep (se 2 (by rfl) ⟨773718, by rfl⟩ : syracuseStep 2063249 = 1547437) B1547437
theorem B1375123 : Blo 1374006 1375123 := bstep (se 1 (by rfl) ⟨1031342, by rfl⟩ : syracuseStep 1375123 = 2062685) B2062685
theorem B1375139 : Blo 1374006 1375139 := bstep (se 1 (by rfl) ⟨1031354, by rfl⟩ : syracuseStep 1375139 = 2062709) B2062709
theorem B1375155 : Blo 1374006 1375155 := bstep (se 1 (by rfl) ⟨1031366, by rfl⟩ : syracuseStep 1375155 = 2062733) B2062733
theorem B1375171 : Blo 1374006 1375171 := bstep (se 1 (by rfl) ⟨1031378, by rfl⟩ : syracuseStep 1375171 = 2062757) B2062757
theorem B1547203 : Blo 1374006 1547203 := bstep (se 1 (by rfl) ⟨1160402, by rfl⟩ : syracuseStep 1547203 = 2320805) B2320805
theorem B3480529 : Blo 1374006 3480529 := bstep (se 2 (by rfl) ⟨1305198, by rfl⟩ : syracuseStep 3480529 = 2610397) B2610397
theorem B1375187 : Blo 1374006 1375187 := bstep (se 1 (by rfl) ⟨1031390, by rfl⟩ : syracuseStep 1375187 = 2062781) B2062781
theorem B1375203 : Blo 1374006 1375203 := bstep (se 1 (by rfl) ⟨1031402, by rfl⟩ : syracuseStep 1375203 = 2062805) B2062805
theorem B1375219 : Blo 1374006 1375219 := bstep (se 1 (by rfl) ⟨1031414, by rfl⟩ : syracuseStep 1375219 = 2062829) B2062829
theorem B1375235 : Blo 1374006 1375235 := bstep (se 1 (by rfl) ⟨1031426, by rfl⟩ : syracuseStep 1375235 = 2062853) B2062853
theorem B1375251 : Blo 1374006 1375251 := bstep (se 1 (by rfl) ⟨1031438, by rfl⟩ : syracuseStep 1375251 = 2062877) B2062877
theorem B1375267 : Blo 1374006 1375267 := bstep (se 1 (by rfl) ⟨1031450, by rfl⟩ : syracuseStep 1375267 = 2062901) B2062901
theorem B6036515 : Blo 1374006 6036515 := bstep (se 1 (by rfl) ⟨4527386, by rfl⟩ : syracuseStep 6036515 = 9054773) B9054773
theorem B4701229 : Blo 1374006 4701229 := bstep (se 3 (by rfl) ⟨881480, by rfl⟩ : syracuseStep 4701229 = 1762961) B1762961
theorem B1375283 : Blo 1374006 1375283 := bstep (se 1 (by rfl) ⟨1031462, by rfl⟩ : syracuseStep 1375283 = 2062925) B2062925
theorem B1375299 : Blo 1374006 1375299 := bstep (se 1 (by rfl) ⟨1031474, by rfl⟩ : syracuseStep 1375299 = 2062949) B2062949
theorem B1375315 : Blo 1374006 1375315 := bstep (se 1 (by rfl) ⟨1031486, by rfl⟩ : syracuseStep 1375315 = 2062973) B2062973
theorem B1547347 : Blo 1374006 1547347 := bstep (se 1 (by rfl) ⟨1160510, by rfl⟩ : syracuseStep 1547347 = 2321021) B2321021
theorem B1375331 : Blo 1374006 1375331 := bstep (se 1 (by rfl) ⟨1031498, by rfl⟩ : syracuseStep 1375331 = 2062997) B2062997
theorem B1375347 : Blo 1374006 1375347 := bstep (se 1 (by rfl) ⟨1031510, by rfl⟩ : syracuseStep 1375347 = 2063021) B2063021
theorem B1375363 : Blo 1374006 1375363 := bstep (se 1 (by rfl) ⟨1031522, by rfl⟩ : syracuseStep 1375363 = 2063045) B2063045
theorem B1375379 : Blo 1374006 1375379 := bstep (se 1 (by rfl) ⟨1031534, by rfl⟩ : syracuseStep 1375379 = 2063069) B2063069
theorem B1375395 : Blo 1374006 1375395 := bstep (se 1 (by rfl) ⟨1031546, by rfl⟩ : syracuseStep 1375395 = 2063093) B2063093
theorem B1375411 : Blo 1374006 1375411 := bstep (se 1 (by rfl) ⟨1031558, by rfl⟩ : syracuseStep 1375411 = 2063117) B2063117
theorem B1375427 : Blo 1374006 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B8805581 : Blo 1374006 8805581 := bstep (se 3 (by rfl) ⟨1651046, by rfl⟩ : syracuseStep 8805581 = 3302093) B3302093
theorem B1375443 : Blo 1374006 1375443 := bstep (se 1 (by rfl) ⟨1031582, by rfl⟩ : syracuseStep 1375443 = 2063165) B2063165
theorem B3480803 : Blo 1374006 3480803 := bstep (se 1 (by rfl) ⟨2610602, by rfl⟩ : syracuseStep 3480803 = 5221205) B5221205
theorem B2202851 : Blo 1374006 2202851 := bstep (se 1 (by rfl) ⟨1652138, by rfl⟩ : syracuseStep 2202851 = 3304277) B3304277
theorem B1375459 : Blo 1374006 1375459 := bstep (se 1 (by rfl) ⟨1031594, by rfl⟩ : syracuseStep 1375459 = 2063189) B2063189
theorem B3914993 : Blo 1374006 3914993 := bstep (se 2 (by rfl) ⟨1468122, by rfl⟩ : syracuseStep 3914993 = 2936245) B2936245
theorem B1375475 : Blo 1374006 1375475 := bstep (se 1 (by rfl) ⟨1031606, by rfl⟩ : syracuseStep 1375475 = 2063213) B2063213
theorem B1375491 : Blo 1374006 1375491 := bstep (se 1 (by rfl) ⟨1031618, by rfl⟩ : syracuseStep 1375491 = 2063237) B2063237
theorem B5217635 : Blo 1374006 5217635 := bstep (se 1 (by rfl) ⟨3913226, by rfl⟩ : syracuseStep 5217635 = 7826453) B7826453
theorem B3480995 : Blo 1374006 3480995 := bstep (se 1 (by rfl) ⟨2610746, by rfl⟩ : syracuseStep 3480995 = 5221493) B5221493
theorem B1957297 : Blo 1374006 1957297 := bstep (se 2 (by rfl) ⟨733986, by rfl⟩ : syracuseStep 1957297 = 1467973) B1467973
theorem B1957331 : Blo 1374006 1957331 := bstep (se 1 (by rfl) ⟨1467998, by rfl⟩ : syracuseStep 1957331 = 2935997) B2935997
theorem B2416433 : Blo 1374006 2416433 := bstep (se 2 (by rfl) ⟨906162, by rfl⟩ : syracuseStep 2416433 = 1812325) B1812325
theorem B3915665 : Blo 1374006 3915665 := bstep (se 2 (by rfl) ⟨1468374, by rfl⟩ : syracuseStep 3915665 = 2936749) B2936749
theorem B5218289 : Blo 1374006 5218289 := bstep (se 2 (by rfl) ⟨1956858, by rfl⟩ : syracuseStep 5218289 = 3913717) B3913717
theorem B6963245 : Blo 1374006 6963245 := bstep (se 3 (by rfl) ⟨1305608, by rfl⟩ : syracuseStep 6963245 = 2611217) B2611217
theorem B5218577 : Blo 1374006 5218577 := bstep (se 2 (by rfl) ⟨1956966, by rfl⟩ : syracuseStep 5218577 = 3913933) B3913933
theorem B13582637 : Blo 1374006 13582637 := bstep (se 3 (by rfl) ⟨2546744, by rfl⟩ : syracuseStep 13582637 = 5093489) B5093489
theorem B3916097 : Blo 1374006 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B12542309 : Blo 1374006 12542309 := bstep (se 4 (by rfl) ⟨1175841, by rfl⟩ : syracuseStep 12542309 = 2351683) B2351683
theorem B2646475 : Blo 1374006 2646475 := bstep (se 1 (by rfl) ⟨1984856, by rfl⟩ : syracuseStep 2646475 = 3969713) B3969713
theorem B2318807 : Blo 1374006 2318807 := bstep (se 1 (by rfl) ⟨1739105, by rfl⟩ : syracuseStep 2318807 = 3478211) B3478211
theorem B2318935 : Blo 1374006 2318935 := bstep (se 1 (by rfl) ⟨1739201, by rfl⟩ : syracuseStep 2318935 = 3478403) B3478403
theorem B11748017 : Blo 1374006 11748017 := bstep (se 2 (by rfl) ⟨4405506, by rfl⟩ : syracuseStep 11748017 = 8811013) B8811013
theorem B3916633 : Blo 1374006 3916633 := bstep (se 2 (by rfl) ⟨1468737, by rfl⟩ : syracuseStep 3916633 = 2937475) B2937475
theorem B6955955 : Blo 1374006 6955955 := bstep (se 1 (by rfl) ⟨5216966, by rfl⟩ : syracuseStep 6955955 = 10433933) B10433933
theorem B8479667 : Blo 1374006 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B5219275 : Blo 1374006 5219275 := bstep (se 1 (by rfl) ⟨3914456, by rfl⟩ : syracuseStep 5219275 = 7828913) B7828913
theorem B7832537 : Blo 1374006 7832537 := bstep (se 2 (by rfl) ⟨2937201, by rfl⟩ : syracuseStep 7832537 = 5874403) B5874403
theorem B16720931 : Blo 1374006 16720931 := bstep (se 1 (by rfl) ⟨12540698, by rfl⟩ : syracuseStep 16720931 = 25081397) B25081397
theorem B4637789 : Blo 1374006 4637789 := bstep (se 3 (by rfl) ⟨869585, by rfl⟩ : syracuseStep 4637789 = 1739171) B1739171
theorem B2319563 : Blo 1374006 2319563 := bstep (se 1 (by rfl) ⟨1739672, by rfl⟩ : syracuseStep 2319563 = 3479345) B3479345
theorem B5293259 : Blo 1374006 5293259 := bstep (se 1 (by rfl) ⟨3969944, by rfl⟩ : syracuseStep 5293259 = 7939889) B7939889
theorem B5219549 : Blo 1374006 5219549 := bstep (se 3 (by rfl) ⟨978665, by rfl⟩ : syracuseStep 5219549 = 1957331) B1957331
theorem B3015937 : Blo 1374006 3015937 := bstep (se 2 (by rfl) ⟨1130976, by rfl⟩ : syracuseStep 3015937 = 2261953) B2261953
theorem B2319691 : Blo 1374006 2319691 := bstep (se 1 (by rfl) ⟨1739768, by rfl⟩ : syracuseStep 2319691 = 3479537) B3479537
theorem B2319833 : Blo 1374006 2319833 := bstep (se 2 (by rfl) ⟨869937, by rfl⟩ : syracuseStep 2319833 = 1739875) B1739875
theorem B2319961 : Blo 1374006 2319961 := bstep (se 2 (by rfl) ⟨869985, by rfl⟩ : syracuseStep 2319961 = 1739971) B1739971
theorem B12543619 : Blo 1374006 12543619 := bstep (se 1 (by rfl) ⟨9407714, by rfl⟩ : syracuseStep 12543619 = 18815429) B18815429
theorem B11142947 : Blo 1374006 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B22603619 : Blo 1374006 22603619 := bstep (se 1 (by rfl) ⟨16952714, by rfl⟩ : syracuseStep 22603619 = 33905429) B33905429
theorem B5220247 : Blo 1374006 5220247 := bstep (se 1 (by rfl) ⟨3915185, by rfl⟩ : syracuseStep 5220247 = 7830371) B7830371
theorem B3303361 : Blo 1374006 3303361 := bstep (se 2 (by rfl) ⟨1238760, by rfl⟩ : syracuseStep 3303361 = 2477521) B2477521
theorem B4024343 : Blo 1374006 4024343 := bstep (se 1 (by rfl) ⟨3018257, by rfl⟩ : syracuseStep 4024343 = 6036515) B6036515
theorem B39651403 : Blo 1374006 39651403 := bstep (se 1 (by rfl) ⟨29738552, by rfl⟩ : syracuseStep 39651403 = 59477105) B59477105
theorem B5572739 : Blo 1374006 5572739 := bstep (se 1 (by rfl) ⟨4179554, by rfl⟩ : syracuseStep 5572739 = 8359109) B8359109
theorem B2320535 : Blo 1374006 2320535 := bstep (se 1 (by rfl) ⟨1740401, by rfl⟩ : syracuseStep 2320535 = 3480803) B3480803
theorem B1468567 : Blo 1374006 1468567 := bstep (se 1 (by rfl) ⟨1101425, by rfl⟩ : syracuseStep 1468567 = 2202851) B2202851
theorem B5572801 : Blo 1374006 5572801 := bstep (se 2 (by rfl) ⟨2089800, by rfl⟩ : syracuseStep 5572801 = 4179601) B4179601
theorem B4638923 : Blo 1374006 4638923 := bstep (se 1 (by rfl) ⟨3479192, by rfl⟩ : syracuseStep 4638923 = 6958385) B6958385
theorem B2320663 : Blo 1374006 2320663 := bstep (se 1 (by rfl) ⟨1740497, by rfl⟩ : syracuseStep 2320663 = 3480995) B3480995
theorem B2935091 : Blo 1374006 2935091 := bstep (se 1 (by rfl) ⟨2201318, by rfl⟩ : syracuseStep 2935091 = 4402637) B4402637
theorem B4639193 : Blo 1374006 4639193 := bstep (se 2 (by rfl) ⟨1739697, by rfl⟩ : syracuseStep 4639193 = 3479395) B3479395
theorem B5221037 : Blo 1374006 5221037 := bstep (se 3 (by rfl) ⟨978944, by rfl⟩ : syracuseStep 5221037 = 1957889) B1957889
theorem B2476823 : Blo 1374006 2476823 := bstep (se 1 (by rfl) ⟨1857617, by rfl⟩ : syracuseStep 2476823 = 3715235) B3715235
theorem B2788121 : Blo 1374006 2788121 := bstep (se 2 (by rfl) ⟨1045545, by rfl⟩ : syracuseStep 2788121 = 2091091) B2091091
theorem B4401971 : Blo 1374006 4401971 := bstep (se 1 (by rfl) ⟨3301478, by rfl⟩ : syracuseStep 4401971 = 6602957) B6602957
theorem B6957899 : Blo 1374006 6957899 := bstep (se 1 (by rfl) ⟨5218424, by rfl⟩ : syracuseStep 6957899 = 10436849) B10436849
theorem B2477017 : Blo 1374006 2477017 := bstep (se 2 (by rfl) ⟨928881, by rfl⟩ : syracuseStep 2477017 = 1857763) B1857763
theorem B3091571 : Blo 1374006 3091571 := bstep (se 1 (by rfl) ⟨2318678, by rfl⟩ : syracuseStep 3091571 = 4637357) B4637357
theorem B3091607 : Blo 1374006 3091607 := bstep (se 1 (by rfl) ⟨2318705, by rfl⟩ : syracuseStep 3091607 = 4637411) B4637411
theorem B4639895 : Blo 1374006 4639895 := bstep (se 1 (by rfl) ⟨3479921, by rfl⟩ : syracuseStep 4639895 = 6959843) B6959843
theorem B7826705 : Blo 1374006 7826705 := bstep (se 2 (by rfl) ⟨2935014, by rfl⟩ : syracuseStep 7826705 = 5870029) B5870029
theorem B3091787 : Blo 1374006 3091787 := bstep (se 1 (by rfl) ⟨2318840, by rfl⟩ : syracuseStep 3091787 = 4637681) B4637681
theorem B2608499 : Blo 1374006 2608499 := bstep (se 1 (by rfl) ⟨1956374, by rfl⟩ : syracuseStep 2608499 = 3912749) B3912749
theorem B3091841 : Blo 1374006 3091841 := bstep (se 2 (by rfl) ⟨1159440, by rfl⟩ : syracuseStep 3091841 = 2318881) B2318881
theorem B7433603 : Blo 1374006 7433603 := bstep (se 1 (by rfl) ⟨5575202, by rfl⟩ : syracuseStep 7433603 = 11150405) B11150405
theorem B2608537 : Blo 1374006 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B25079219 : Blo 1374006 25079219 := bstep (se 1 (by rfl) ⟨18809414, by rfl⟩ : syracuseStep 25079219 = 37618829) B37618829
theorem B2936407 : Blo 1374006 2936407 := bstep (se 1 (by rfl) ⟨2202305, by rfl⟩ : syracuseStep 2936407 = 4404611) B4404611
theorem B3092057 : Blo 1374006 3092057 := bstep (se 2 (by rfl) ⟨1159521, by rfl⟩ : syracuseStep 3092057 = 2319043) B2319043
theorem B11152997 : Blo 1374006 11152997 := bstep (se 4 (by rfl) ⟨1045593, by rfl⟩ : syracuseStep 11152997 = 2091187) B2091187
theorem B3092147 : Blo 1374006 3092147 := bstep (se 1 (by rfl) ⟨2319110, by rfl⟩ : syracuseStep 3092147 = 4638221) B4638221
theorem B4640435 : Blo 1374006 4640435 := bstep (se 1 (by rfl) ⟨3480326, by rfl⟩ : syracuseStep 4640435 = 6960653) B6960653
theorem B3092183 : Blo 1374006 3092183 := bstep (se 1 (by rfl) ⟨2319137, by rfl⟩ : syracuseStep 3092183 = 4638275) B4638275
theorem B2936587 : Blo 1374006 2936587 := bstep (se 1 (by rfl) ⟨2202440, by rfl⟩ : syracuseStep 2936587 = 4404881) B4404881
theorem B17624897 : Blo 1374006 17624897 := bstep (se 2 (by rfl) ⟨6609336, by rfl⟩ : syracuseStep 17624897 = 13218673) B13218673
theorem B1740619 : Blo 1374006 1740619 := bstep (se 1 (by rfl) ⟨1305464, by rfl⟩ : syracuseStep 1740619 = 2610929) B2610929
theorem B2936663 : Blo 1374006 2936663 := bstep (se 1 (by rfl) ⟨2202497, by rfl⟩ : syracuseStep 2936663 = 4404995) B4404995
theorem B2608985 : Blo 1374006 2608985 := bstep (se 2 (by rfl) ⟨978369, by rfl⟩ : syracuseStep 2608985 = 1956739) B1956739
theorem B3092363 : Blo 1374006 3092363 := bstep (se 1 (by rfl) ⟨2319272, by rfl⟩ : syracuseStep 3092363 = 4638545) B4638545
theorem B19812275 : Blo 1374006 19812275 := bstep (se 1 (by rfl) ⟨14859206, by rfl⟩ : syracuseStep 19812275 = 29718413) B29718413
theorem B4181939 : Blo 1374006 4181939 := bstep (se 1 (by rfl) ⟨3136454, by rfl⟩ : syracuseStep 4181939 = 6272909) B6272909
theorem B3092417 : Blo 1374006 3092417 := bstep (se 2 (by rfl) ⟨1159656, by rfl⟩ : syracuseStep 3092417 = 2319313) B2319313
theorem B4640705 : Blo 1374006 4640705 := bstep (se 2 (by rfl) ⟨1740264, by rfl⟩ : syracuseStep 4640705 = 3480529) B3480529
theorem B4403251 : Blo 1374006 4403251 := bstep (se 1 (by rfl) ⟨3302438, by rfl⟩ : syracuseStep 4403251 = 6604877) B6604877
theorem B5222465 : Blo 1374006 5222465 := bstep (se 2 (by rfl) ⟨1958424, by rfl⟩ : syracuseStep 5222465 = 3916849) B3916849
theorem B11145347 : Blo 1374006 11145347 := bstep (se 1 (by rfl) ⟨8359010, by rfl⟩ : syracuseStep 11145347 = 16718021) B16718021
theorem B6271121 : Blo 1374006 6271121 := bstep (se 2 (by rfl) ⟨2351670, by rfl⟩ : syracuseStep 6271121 = 4703341) B4703341
theorem B3092633 : Blo 1374006 3092633 := bstep (se 2 (by rfl) ⟨1159737, by rfl⟩ : syracuseStep 3092633 = 2319475) B2319475
theorem B3092723 : Blo 1374006 3092723 := bstep (se 1 (by rfl) ⟨2319542, by rfl⟩ : syracuseStep 3092723 = 4639085) B4639085
theorem B3092759 : Blo 1374006 3092759 := bstep (se 1 (by rfl) ⟨2319569, by rfl⟩ : syracuseStep 3092759 = 4639139) B4639139
theorem B3715417 : Blo 1374006 3715417 := bstep (se 2 (by rfl) ⟨1393281, by rfl⟩ : syracuseStep 3715417 = 2786563) B2786563
theorem B2232665 : Blo 1374006 2232665 := bstep (se 2 (by rfl) ⟨837249, by rfl⟩ : syracuseStep 2232665 = 1674499) B1674499
theorem B3092939 : Blo 1374006 3092939 := bstep (se 1 (by rfl) ⟨2319704, by rfl⟩ : syracuseStep 3092939 = 4639409) B4639409
theorem B5870045 : Blo 1374006 5870045 := bstep (se 3 (by rfl) ⟨1100633, by rfl⟩ : syracuseStep 5870045 = 2201267) B2201267
theorem B4641245 : Blo 1374006 4641245 := bstep (se 3 (by rfl) ⟨870233, by rfl⟩ : syracuseStep 4641245 = 1740467) B1740467
theorem B3092993 : Blo 1374006 3092993 := bstep (se 2 (by rfl) ⟨1159872, by rfl⟩ : syracuseStep 3092993 = 2319745) B2319745
theorem B2609729 : Blo 1374006 2609729 := bstep (se 2 (by rfl) ⟨978648, by rfl⟩ : syracuseStep 2609729 = 1957297) B1957297
theorem B6959681 : Blo 1374006 6959681 := bstep (se 2 (by rfl) ⟨2609880, by rfl⟩ : syracuseStep 6959681 = 5219761) B5219761
theorem B2061017 : Blo 1374006 2061017 := bstep (se 2 (by rfl) ⟨772881, by rfl⟩ : syracuseStep 2061017 = 1545763) B1545763
theorem B3093209 : Blo 1374006 3093209 := bstep (se 2 (by rfl) ⟨1159953, by rfl⟩ : syracuseStep 3093209 = 2319907) B2319907
theorem B5870353 : Blo 1374006 5870353 := bstep (se 2 (by rfl) ⟨2201382, by rfl⟩ : syracuseStep 5870353 = 4402765) B4402765
theorem B15651629 : Blo 1374006 15651629 := bstep (se 3 (by rfl) ⟨2934680, by rfl⟩ : syracuseStep 15651629 = 5869361) B5869361
theorem B6443821 : Blo 1374006 6443821 := bstep (se 3 (by rfl) ⟨1208216, by rfl⟩ : syracuseStep 6443821 = 2416433) B2416433
theorem B5870387 : Blo 1374006 5870387 := bstep (se 1 (by rfl) ⟨4402790, by rfl⟩ : syracuseStep 5870387 = 8805581) B8805581
theorem B3093299 : Blo 1374006 3093299 := bstep (se 1 (by rfl) ⟨2319974, by rfl⟩ : syracuseStep 3093299 = 4639949) B4639949
theorem B2061131 : Blo 1374006 2061131 := bstep (se 1 (by rfl) ⟨1545848, by rfl⟩ : syracuseStep 2061131 = 3091697) B3091697
theorem B2609995 : Blo 1374006 2609995 := bstep (se 1 (by rfl) ⟨1957496, by rfl⟩ : syracuseStep 2609995 = 3914993) B3914993
theorem B2061143 : Blo 1374006 2061143 := bstep (se 1 (by rfl) ⟨1545857, by rfl⟩ : syracuseStep 2061143 = 3091715) B3091715
theorem B3093335 : Blo 1374006 3093335 := bstep (se 1 (by rfl) ⟨2320001, by rfl⟩ : syracuseStep 3093335 = 4640003) B4640003
theorem B3478423 : Blo 1374006 3478423 := bstep (se 1 (by rfl) ⟨2608817, by rfl⟩ : syracuseStep 3478423 = 5217635) B5217635
theorem B2061209 : Blo 1374006 2061209 := bstep (se 2 (by rfl) ⟨772953, by rfl⟩ : syracuseStep 2061209 = 1545907) B1545907
theorem B2061323 : Blo 1374006 2061323 := bstep (se 1 (by rfl) ⟨1545992, by rfl⟩ : syracuseStep 2061323 = 3091985) B3091985
theorem B3093515 : Blo 1374006 3093515 := bstep (se 1 (by rfl) ⟨2320136, by rfl⟩ : syracuseStep 3093515 = 4640273) B4640273
theorem B2061335 : Blo 1374006 2061335 := bstep (se 1 (by rfl) ⟨1546001, by rfl⟩ : syracuseStep 2061335 = 3092003) B3092003
theorem B5649431 : Blo 1374006 5649431 := bstep (se 1 (by rfl) ⟨4237073, by rfl⟩ : syracuseStep 5649431 = 8474147) B8474147
theorem B3093569 : Blo 1374006 3093569 := bstep (se 2 (by rfl) ⟨1160088, by rfl⟩ : syracuseStep 3093569 = 2320177) B2320177
theorem B2061401 : Blo 1374006 2061401 := bstep (se 2 (by rfl) ⟨773025, by rfl⟩ : syracuseStep 2061401 = 1546051) B1546051
theorem B2061515 : Blo 1374006 2061515 := bstep (se 1 (by rfl) ⟨1546136, by rfl⟩ : syracuseStep 2061515 = 3092273) B3092273
theorem B2061527 : Blo 1374006 2061527 := bstep (se 1 (by rfl) ⟨1546145, by rfl⟩ : syracuseStep 2061527 = 3092291) B3092291
theorem B2610443 : Blo 1374006 2610443 := bstep (se 1 (by rfl) ⟨1957832, by rfl⟩ : syracuseStep 2610443 = 3915665) B3915665
theorem B2061593 : Blo 1374006 2061593 := bstep (se 2 (by rfl) ⟨773097, by rfl⟩ : syracuseStep 2061593 = 1546195) B1546195
theorem B3093785 : Blo 1374006 3093785 := bstep (se 2 (by rfl) ⟨1160169, by rfl⟩ : syracuseStep 3093785 = 2320339) B2320339
theorem B3478859 : Blo 1374006 3478859 := bstep (se 1 (by rfl) ⟨2609144, by rfl⟩ : syracuseStep 3478859 = 5218289) B5218289
theorem B3093875 : Blo 1374006 3093875 := bstep (se 1 (by rfl) ⟨2320406, by rfl⟩ : syracuseStep 3093875 = 4640813) B4640813
theorem B2061707 : Blo 1374006 2061707 := bstep (se 1 (by rfl) ⟨1546280, by rfl⟩ : syracuseStep 2061707 = 3092561) B3092561
theorem B2061719 : Blo 1374006 2061719 := bstep (se 1 (by rfl) ⟨1546289, by rfl⟩ : syracuseStep 2061719 = 3092579) B3092579
theorem B3093911 : Blo 1374006 3093911 := bstep (se 1 (by rfl) ⟨2320433, by rfl⟩ : syracuseStep 3093911 = 4640867) B4640867
theorem B2610625 : Blo 1374006 2610625 := bstep (se 2 (by rfl) ⟨978984, by rfl⟩ : syracuseStep 2610625 = 1957969) B1957969
theorem B2061785 : Blo 1374006 2061785 := bstep (se 2 (by rfl) ⟨773169, by rfl⟩ : syracuseStep 2061785 = 1546339) B1546339
theorem B3913181 : Blo 1374006 3913181 := bstep (se 3 (by rfl) ⟨733721, by rfl⟩ : syracuseStep 3913181 = 1467443) B1467443
theorem B2201113 : Blo 1374006 2201113 := bstep (se 2 (by rfl) ⟨825417, by rfl⟩ : syracuseStep 2201113 = 1650835) B1650835
theorem B25073221 : Blo 1374006 25073221 := bstep (se 4 (by rfl) ⟨2350614, by rfl⟩ : syracuseStep 25073221 = 4701229) B4701229
theorem B2061899 : Blo 1374006 2061899 := bstep (se 1 (by rfl) ⟨1546424, by rfl⟩ : syracuseStep 2061899 = 3092849) B3092849
theorem B3094091 : Blo 1374006 3094091 := bstep (se 1 (by rfl) ⟨2320568, by rfl⟩ : syracuseStep 3094091 = 4641137) B4641137
theorem B2061911 : Blo 1374006 2061911 := bstep (se 1 (by rfl) ⟨1546433, by rfl⟩ : syracuseStep 2061911 = 3092867) B3092867
theorem B1545835 : Blo 1374006 1545835 := bstep (se 1 (by rfl) ⟨1159376, by rfl⟩ : syracuseStep 1545835 = 2318753) B2318753
theorem B3094145 : Blo 1374006 3094145 := bstep (se 2 (by rfl) ⟨1160304, by rfl⟩ : syracuseStep 3094145 = 2320609) B2320609
theorem B3348119 : Blo 1374006 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B2061977 : Blo 1374006 2061977 := bstep (se 2 (by rfl) ⟨773241, by rfl⟩ : syracuseStep 2061977 = 1546483) B1546483
theorem B3913409 : Blo 1374006 3913409 := bstep (se 2 (by rfl) ⟨1467528, by rfl⟩ : syracuseStep 3913409 = 2935057) B2935057
theorem B3479233 : Blo 1374006 3479233 := bstep (se 2 (by rfl) ⟨1304712, by rfl⟩ : syracuseStep 3479233 = 2609425) B2609425
theorem B1545943 : Blo 1374006 1545943 := bstep (se 1 (by rfl) ⟨1159457, by rfl⟩ : syracuseStep 1545943 = 2318915) B2318915
theorem B2062091 : Blo 1374006 2062091 := bstep (se 1 (by rfl) ⟨1546568, by rfl⟩ : syracuseStep 2062091 = 3093137) B3093137
theorem B2062103 : Blo 1374006 2062103 := bstep (se 1 (by rfl) ⟨1546577, by rfl⟩ : syracuseStep 2062103 = 3093155) B3093155
theorem B2610967 : Blo 1374006 2610967 := bstep (se 1 (by rfl) ⟨1958225, by rfl⟩ : syracuseStep 2610967 = 3916451) B3916451
theorem B1374007 : Blo 1374006 1374007 := bstep (se 1 (by rfl) ⟨1030505, by rfl⟩ : syracuseStep 1374007 = 2061011) B2061011
theorem B1374027 : Blo 1374006 1374027 := bstep (se 1 (by rfl) ⟨1030520, by rfl⟩ : syracuseStep 1374027 = 2061041) B2061041
theorem B1374039 : Blo 1374006 1374039 := bstep (se 1 (by rfl) ⟨1030529, by rfl⟩ : syracuseStep 1374039 = 2061059) B2061059
theorem B2062169 : Blo 1374006 2062169 := bstep (se 2 (by rfl) ⟨773313, by rfl⟩ : syracuseStep 2062169 = 1546627) B1546627
theorem B3094361 : Blo 1374006 3094361 := bstep (se 2 (by rfl) ⟨1160385, by rfl⟩ : syracuseStep 3094361 = 2320771) B2320771
theorem B1374059 : Blo 1374006 1374059 := bstep (se 1 (by rfl) ⟨1030544, by rfl⟩ : syracuseStep 1374059 = 2061089) B2061089
theorem B1374071 : Blo 1374006 1374071 := bstep (se 1 (by rfl) ⟨1030553, by rfl⟩ : syracuseStep 1374071 = 2061107) B2061107
theorem B1374091 : Blo 1374006 1374091 := bstep (se 1 (by rfl) ⟨1030568, by rfl⟩ : syracuseStep 1374091 = 2061137) B2061137
theorem B1546123 : Blo 1374006 1546123 := bstep (se 1 (by rfl) ⟨1159592, by rfl⟩ : syracuseStep 1546123 = 2319185) B2319185
theorem B1374103 : Blo 1374006 1374103 := bstep (se 1 (by rfl) ⟨1030577, by rfl⟩ : syracuseStep 1374103 = 2061155) B2061155
theorem B1374123 : Blo 1374006 1374123 := bstep (se 1 (by rfl) ⟨1030592, by rfl⟩ : syracuseStep 1374123 = 2061185) B2061185
theorem B3094451 : Blo 1374006 3094451 := bstep (se 1 (by rfl) ⟨2320838, by rfl⟩ : syracuseStep 3094451 = 4641677) B4641677
theorem B1374135 : Blo 1374006 1374135 := bstep (se 1 (by rfl) ⟨1030601, by rfl⟩ : syracuseStep 1374135 = 2061203) B2061203
theorem B1374155 : Blo 1374006 1374155 := bstep (se 1 (by rfl) ⟨1030616, by rfl⟩ : syracuseStep 1374155 = 2061233) B2061233
theorem B2062283 : Blo 1374006 2062283 := bstep (se 1 (by rfl) ⟨1546712, by rfl⟩ : syracuseStep 2062283 = 3093425) B3093425
theorem B1374167 : Blo 1374006 1374167 := bstep (se 1 (by rfl) ⟨1030625, by rfl⟩ : syracuseStep 1374167 = 2061251) B2061251
theorem B2062295 : Blo 1374006 2062295 := bstep (se 1 (by rfl) ⟨1546721, by rfl⟩ : syracuseStep 2062295 = 3093443) B3093443
theorem B3094487 : Blo 1374006 3094487 := bstep (se 1 (by rfl) ⟨2320865, by rfl⟩ : syracuseStep 3094487 = 4641731) B4641731
theorem B1374187 : Blo 1374006 1374187 := bstep (se 1 (by rfl) ⟨1030640, by rfl⟩ : syracuseStep 1374187 = 2061281) B2061281
theorem B1546231 : Blo 1374006 1546231 := bstep (se 1 (by rfl) ⟨1159673, by rfl⟩ : syracuseStep 1546231 = 2319347) B2319347
theorem B1374199 : Blo 1374006 1374199 := bstep (se 1 (by rfl) ⟨1030649, by rfl⟩ : syracuseStep 1374199 = 2061299) B2061299
theorem B2611187 : Blo 1374006 2611187 := bstep (se 1 (by rfl) ⟨1958390, by rfl⟩ : syracuseStep 2611187 = 3916781) B3916781
theorem B1374219 : Blo 1374006 1374219 := bstep (se 1 (by rfl) ⟨1030664, by rfl⟩ : syracuseStep 1374219 = 2061329) B2061329
theorem B9910289 : Blo 1374006 9910289 := bstep (se 2 (by rfl) ⟨3716358, by rfl⟩ : syracuseStep 9910289 = 7432717) B7432717
theorem B1374231 : Blo 1374006 1374231 := bstep (se 1 (by rfl) ⟨1030673, by rfl⟩ : syracuseStep 1374231 = 2061347) B2061347
theorem B3913751 : Blo 1374006 3913751 := bstep (se 1 (by rfl) ⟨2935313, by rfl⟩ : syracuseStep 3913751 = 5870627) B5870627
theorem B2062361 : Blo 1374006 2062361 := bstep (se 2 (by rfl) ⟨773385, by rfl⟩ : syracuseStep 2062361 = 1546771) B1546771
theorem B1374251 : Blo 1374006 1374251 := bstep (se 1 (by rfl) ⟨1030688, by rfl⟩ : syracuseStep 1374251 = 2061377) B2061377
theorem B1374263 : Blo 1374006 1374263 := bstep (se 1 (by rfl) ⟨1030697, by rfl⟩ : syracuseStep 1374263 = 2061395) B2061395
theorem B1374283 : Blo 1374006 1374283 := bstep (se 1 (by rfl) ⟨1030712, by rfl⟩ : syracuseStep 1374283 = 2061425) B2061425
theorem B1374295 : Blo 1374006 1374295 := bstep (se 1 (by rfl) ⟨1030721, by rfl⟩ : syracuseStep 1374295 = 2061443) B2061443
theorem B1374315 : Blo 1374006 1374315 := bstep (se 1 (by rfl) ⟨1030736, by rfl⟩ : syracuseStep 1374315 = 2061473) B2061473
theorem B1374327 : Blo 1374006 1374327 := bstep (se 1 (by rfl) ⟨1030745, by rfl⟩ : syracuseStep 1374327 = 2061491) B2061491
theorem B1374347 : Blo 1374006 1374347 := bstep (se 1 (by rfl) ⟨1030760, by rfl⟩ : syracuseStep 1374347 = 2061521) B2061521
theorem B2062475 : Blo 1374006 2062475 := bstep (se 1 (by rfl) ⟨1546856, by rfl⟩ : syracuseStep 2062475 = 3093713) B3093713
theorem B3094667 : Blo 1374006 3094667 := bstep (se 1 (by rfl) ⟨2321000, by rfl⟩ : syracuseStep 3094667 = 4642001) B4642001
theorem B1374359 : Blo 1374006 1374359 := bstep (se 1 (by rfl) ⟨1030769, by rfl⟩ : syracuseStep 1374359 = 2061539) B2061539
theorem B2062487 : Blo 1374006 2062487 := bstep (se 1 (by rfl) ⟨1546865, by rfl⟩ : syracuseStep 2062487 = 3093731) B3093731
theorem B11303063 : Blo 1374006 11303063 := bstep (se 1 (by rfl) ⟨8477297, by rfl⟩ : syracuseStep 11303063 = 16954595) B16954595
theorem B1374379 : Blo 1374006 1374379 := bstep (se 1 (by rfl) ⟨1030784, by rfl⟩ : syracuseStep 1374379 = 2061569) B2061569
theorem B1546411 : Blo 1374006 1546411 := bstep (se 1 (by rfl) ⟨1159808, by rfl⟩ : syracuseStep 1546411 = 2319617) B2319617
theorem B11901107 : Blo 1374006 11901107 := bstep (se 1 (by rfl) ⟨8925830, by rfl⟩ : syracuseStep 11901107 = 17851661) B17851661
theorem B1374391 : Blo 1374006 1374391 := bstep (se 1 (by rfl) ⟨1030793, by rfl⟩ : syracuseStep 1374391 = 2061587) B2061587
theorem B3094721 : Blo 1374006 3094721 := bstep (se 2 (by rfl) ⟨1160520, by rfl⟩ : syracuseStep 3094721 = 2321041) B2321041
theorem B1374411 : Blo 1374006 1374411 := bstep (se 1 (by rfl) ⟨1030808, by rfl⟩ : syracuseStep 1374411 = 2061617) B2061617
theorem B1374423 : Blo 1374006 1374423 := bstep (se 1 (by rfl) ⟨1030817, by rfl⟩ : syracuseStep 1374423 = 2061635) B2061635
theorem B2062553 : Blo 1374006 2062553 := bstep (se 2 (by rfl) ⟨773457, by rfl⟩ : syracuseStep 2062553 = 1546915) B1546915
theorem B1374443 : Blo 1374006 1374443 := bstep (se 1 (by rfl) ⟨1030832, by rfl⟩ : syracuseStep 1374443 = 2061665) B2061665
theorem B1374455 : Blo 1374006 1374455 := bstep (se 1 (by rfl) ⟨1030841, by rfl⟩ : syracuseStep 1374455 = 2061683) B2061683
theorem B13211909 : Blo 1374006 13211909 := bstep (se 4 (by rfl) ⟨1238616, by rfl⟩ : syracuseStep 13211909 = 2477233) B2477233
theorem B1374475 : Blo 1374006 1374475 := bstep (se 1 (by rfl) ⟨1030856, by rfl⟩ : syracuseStep 1374475 = 2061713) B2061713
theorem B1374487 : Blo 1374006 1374487 := bstep (se 1 (by rfl) ⟨1030865, by rfl⟩ : syracuseStep 1374487 = 2061731) B2061731
theorem B1546519 : Blo 1374006 1546519 := bstep (se 1 (by rfl) ⟨1159889, by rfl⟩ : syracuseStep 1546519 = 2319779) B2319779
theorem B3479831 : Blo 1374006 3479831 := bstep (se 1 (by rfl) ⟨2609873, by rfl⟩ : syracuseStep 3479831 = 5219747) B5219747
theorem B3528983 : Blo 1374006 3528983 := bstep (se 1 (by rfl) ⟨2646737, by rfl⟩ : syracuseStep 3528983 = 5293475) B5293475
theorem B1374507 : Blo 1374006 1374507 := bstep (se 1 (by rfl) ⟨1030880, by rfl⟩ : syracuseStep 1374507 = 2061761) B2061761
theorem B5577005 : Blo 1374006 5577005 := bstep (se 3 (by rfl) ⟨1045688, by rfl⟩ : syracuseStep 5577005 = 2091377) B2091377
theorem B1374519 : Blo 1374006 1374519 := bstep (se 1 (by rfl) ⟨1030889, by rfl⟩ : syracuseStep 1374519 = 2061779) B2061779
theorem B1374539 : Blo 1374006 1374539 := bstep (se 1 (by rfl) ⟨1030904, by rfl⟩ : syracuseStep 1374539 = 2061809) B2061809
theorem B7248203 : Blo 1374006 7248203 := bstep (se 1 (by rfl) ⟨5436152, by rfl⟩ : syracuseStep 7248203 = 10872305) B10872305
theorem B2062667 : Blo 1374006 2062667 := bstep (se 1 (by rfl) ⟨1547000, by rfl⟩ : syracuseStep 2062667 = 3094001) B3094001
theorem B1374551 : Blo 1374006 1374551 := bstep (se 1 (by rfl) ⟨1030913, by rfl⟩ : syracuseStep 1374551 = 2061827) B2061827
theorem B2062679 : Blo 1374006 2062679 := bstep (se 1 (by rfl) ⟨1547009, by rfl⟩ : syracuseStep 2062679 = 3094019) B3094019
theorem B1374571 : Blo 1374006 1374571 := bstep (se 1 (by rfl) ⟨1030928, by rfl⟩ : syracuseStep 1374571 = 2061857) B2061857
theorem B1374583 : Blo 1374006 1374583 := bstep (se 1 (by rfl) ⟨1030937, by rfl⟩ : syracuseStep 1374583 = 2061875) B2061875
theorem B1374603 : Blo 1374006 1374603 := bstep (se 1 (by rfl) ⟨1030952, by rfl⟩ : syracuseStep 1374603 = 2061905) B2061905
theorem B1374615 : Blo 1374006 1374615 := bstep (se 1 (by rfl) ⟨1030961, by rfl⟩ : syracuseStep 1374615 = 2061923) B2061923
theorem B2062745 : Blo 1374006 2062745 := bstep (se 2 (by rfl) ⟨773529, by rfl⟩ : syracuseStep 2062745 = 1547059) B1547059
theorem B1374635 : Blo 1374006 1374635 := bstep (se 1 (by rfl) ⟨1030976, by rfl⟩ : syracuseStep 1374635 = 2061953) B2061953
theorem B1374647 : Blo 1374006 1374647 := bstep (se 1 (by rfl) ⟨1030985, by rfl⟩ : syracuseStep 1374647 = 2061971) B2061971
theorem B1374667 : Blo 1374006 1374667 := bstep (se 1 (by rfl) ⟨1031000, by rfl⟩ : syracuseStep 1374667 = 2062001) B2062001
theorem B1546699 : Blo 1374006 1546699 := bstep (se 1 (by rfl) ⟨1160024, by rfl⟩ : syracuseStep 1546699 = 2320049) B2320049
theorem B1374679 : Blo 1374006 1374679 := bstep (se 1 (by rfl) ⟨1031009, by rfl⟩ : syracuseStep 1374679 = 2062019) B2062019
theorem B6961625 : Blo 1374006 6961625 := bstep (se 2 (by rfl) ⟨2610609, by rfl⟩ : syracuseStep 6961625 = 5221219) B5221219
theorem B1374699 : Blo 1374006 1374699 := bstep (se 1 (by rfl) ⟨1031024, by rfl⟩ : syracuseStep 1374699 = 2062049) B2062049
theorem B1374711 : Blo 1374006 1374711 := bstep (se 1 (by rfl) ⟨1031033, by rfl⟩ : syracuseStep 1374711 = 2062067) B2062067
theorem B1374731 : Blo 1374006 1374731 := bstep (se 1 (by rfl) ⟨1031048, by rfl⟩ : syracuseStep 1374731 = 2062097) B2062097
theorem B2062859 : Blo 1374006 2062859 := bstep (se 1 (by rfl) ⟨1547144, by rfl⟩ : syracuseStep 2062859 = 3094289) B3094289
theorem B1374743 : Blo 1374006 1374743 := bstep (se 1 (by rfl) ⟨1031057, by rfl⟩ : syracuseStep 1374743 = 2062115) B2062115
theorem B2062871 : Blo 1374006 2062871 := bstep (se 1 (by rfl) ⟨1547153, by rfl⟩ : syracuseStep 2062871 = 3094307) B3094307
theorem B1374763 : Blo 1374006 1374763 := bstep (se 1 (by rfl) ⟨1031072, by rfl⟩ : syracuseStep 1374763 = 2062145) B2062145
theorem B1374775 : Blo 1374006 1374775 := bstep (se 1 (by rfl) ⟨1031081, by rfl⟩ : syracuseStep 1374775 = 2062163) B2062163
theorem B1546807 : Blo 1374006 1546807 := bstep (se 1 (by rfl) ⟨1160105, by rfl⟩ : syracuseStep 1546807 = 2320211) B2320211
theorem B1374795 : Blo 1374006 1374795 := bstep (se 1 (by rfl) ⟨1031096, by rfl⟩ : syracuseStep 1374795 = 2062193) B2062193
theorem B1374807 : Blo 1374006 1374807 := bstep (se 1 (by rfl) ⟨1031105, by rfl⟩ : syracuseStep 1374807 = 2062211) B2062211
theorem B2062937 : Blo 1374006 2062937 := bstep (se 2 (by rfl) ⟨773601, by rfl⟩ : syracuseStep 2062937 = 1547203) B1547203
theorem B1374827 : Blo 1374006 1374827 := bstep (se 1 (by rfl) ⟨1031120, by rfl⟩ : syracuseStep 1374827 = 2062241) B2062241
theorem B1374839 : Blo 1374006 1374839 := bstep (se 1 (by rfl) ⟨1031129, by rfl⟩ : syracuseStep 1374839 = 2062259) B2062259
theorem B1374859 : Blo 1374006 1374859 := bstep (se 1 (by rfl) ⟨1031144, by rfl⟩ : syracuseStep 1374859 = 2062289) B2062289
theorem B1374871 : Blo 1374006 1374871 := bstep (se 1 (by rfl) ⟨1031153, by rfl⟩ : syracuseStep 1374871 = 2062307) B2062307
theorem B1374891 : Blo 1374006 1374891 := bstep (se 1 (by rfl) ⟨1031168, by rfl⟩ : syracuseStep 1374891 = 2062337) B2062337
theorem B5872301 : Blo 1374006 5872301 := bstep (se 3 (by rfl) ⟨1101056, by rfl⟩ : syracuseStep 5872301 = 2202113) B2202113
theorem B1374903 : Blo 1374006 1374903 := bstep (se 1 (by rfl) ⟨1031177, by rfl⟩ : syracuseStep 1374903 = 2062355) B2062355
theorem B1374923 : Blo 1374006 1374923 := bstep (se 1 (by rfl) ⟨1031192, by rfl⟩ : syracuseStep 1374923 = 2062385) B2062385
theorem B2063051 : Blo 1374006 2063051 := bstep (se 1 (by rfl) ⟨1547288, by rfl⟩ : syracuseStep 2063051 = 3094577) B3094577
theorem B1374935 : Blo 1374006 1374935 := bstep (se 1 (by rfl) ⟨1031201, by rfl⟩ : syracuseStep 1374935 = 2062403) B2062403
theorem B2063063 : Blo 1374006 2063063 := bstep (se 1 (by rfl) ⟨1547297, by rfl⟩ : syracuseStep 2063063 = 3094595) B3094595
theorem B1374955 : Blo 1374006 1374955 := bstep (se 1 (by rfl) ⟨1031216, by rfl⟩ : syracuseStep 1374955 = 2062433) B2062433
theorem B1546987 : Blo 1374006 1546987 := bstep (se 1 (by rfl) ⟨1160240, by rfl⟩ : syracuseStep 1546987 = 2320481) B2320481
theorem B1374967 : Blo 1374006 1374967 := bstep (se 1 (by rfl) ⟨1031225, by rfl⟩ : syracuseStep 1374967 = 2062451) B2062451
theorem B1374987 : Blo 1374006 1374987 := bstep (se 1 (by rfl) ⟨1031240, by rfl⟩ : syracuseStep 1374987 = 2062481) B2062481
theorem B1956631 : Blo 1374006 1956631 := bstep (se 1 (by rfl) ⟨1467473, by rfl⟩ : syracuseStep 1956631 = 2934947) B2934947
theorem B1374999 : Blo 1374006 1374999 := bstep (se 1 (by rfl) ⟨1031249, by rfl⟩ : syracuseStep 1374999 = 2062499) B2062499
theorem B2063129 : Blo 1374006 2063129 := bstep (se 2 (by rfl) ⟨773673, by rfl⟩ : syracuseStep 2063129 = 1547347) B1547347
theorem B1375019 : Blo 1374006 1375019 := bstep (se 1 (by rfl) ⟨1031264, by rfl⟩ : syracuseStep 1375019 = 2062529) B2062529
theorem B1375031 : Blo 1374006 1375031 := bstep (se 1 (by rfl) ⟨1031273, by rfl⟩ : syracuseStep 1375031 = 2062547) B2062547
theorem B1375051 : Blo 1374006 1375051 := bstep (se 1 (by rfl) ⟨1031288, by rfl⟩ : syracuseStep 1375051 = 2062577) B2062577
theorem B1375063 : Blo 1374006 1375063 := bstep (se 1 (by rfl) ⟨1031297, by rfl⟩ : syracuseStep 1375063 = 2062595) B2062595
theorem B1547095 : Blo 1374006 1547095 := bstep (se 1 (by rfl) ⟨1160321, by rfl⟩ : syracuseStep 1547095 = 2320643) B2320643
theorem B1375083 : Blo 1374006 1375083 := bstep (se 1 (by rfl) ⟨1031312, by rfl⟩ : syracuseStep 1375083 = 2062625) B2062625
theorem B1375095 : Blo 1374006 1375095 := bstep (se 1 (by rfl) ⟨1031321, by rfl⟩ : syracuseStep 1375095 = 2062643) B2062643
theorem B1375115 : Blo 1374006 1375115 := bstep (se 1 (by rfl) ⟨1031336, by rfl⟩ : syracuseStep 1375115 = 2062673) B2062673
theorem B2063243 : Blo 1374006 2063243 := bstep (se 1 (by rfl) ⟨1547432, by rfl⟩ : syracuseStep 2063243 = 3094865) B3094865
theorem B1375127 : Blo 1374006 1375127 := bstep (se 1 (by rfl) ⟨1031345, by rfl⟩ : syracuseStep 1375127 = 2062691) B2062691
theorem B2063255 : Blo 1374006 2063255 := bstep (se 1 (by rfl) ⟨1547441, by rfl⟩ : syracuseStep 2063255 = 3094883) B3094883
theorem B1375147 : Blo 1374006 1375147 := bstep (se 1 (by rfl) ⟨1031360, by rfl⟩ : syracuseStep 1375147 = 2062721) B2062721
theorem B1375159 : Blo 1374006 1375159 := bstep (se 1 (by rfl) ⟨1031369, by rfl⟩ : syracuseStep 1375159 = 2062739) B2062739
theorem B1375179 : Blo 1374006 1375179 := bstep (se 1 (by rfl) ⟨1031384, by rfl⟩ : syracuseStep 1375179 = 2062769) B2062769
theorem B1375191 : Blo 1374006 1375191 := bstep (se 1 (by rfl) ⟨1031393, by rfl⟩ : syracuseStep 1375191 = 2062787) B2062787
theorem B17619929 : Blo 1374006 17619929 := bstep (se 2 (by rfl) ⟨6607473, by rfl⟩ : syracuseStep 17619929 = 13214947) B13214947
theorem B1375211 : Blo 1374006 1375211 := bstep (se 1 (by rfl) ⟨1031408, by rfl⟩ : syracuseStep 1375211 = 2062817) B2062817
theorem B1375223 : Blo 1374006 1375223 := bstep (se 1 (by rfl) ⟨1031417, by rfl⟩ : syracuseStep 1375223 = 2062835) B2062835
theorem B1375243 : Blo 1374006 1375243 := bstep (se 1 (by rfl) ⟨1031432, by rfl⟩ : syracuseStep 1375243 = 2062865) B2062865
theorem B1547275 : Blo 1374006 1547275 := bstep (se 1 (by rfl) ⟨1160456, by rfl⟩ : syracuseStep 1547275 = 2320913) B2320913
theorem B1375255 : Blo 1374006 1375255 := bstep (se 1 (by rfl) ⟨1031441, by rfl⟩ : syracuseStep 1375255 = 2062883) B2062883
theorem B1375275 : Blo 1374006 1375275 := bstep (se 1 (by rfl) ⟨1031456, by rfl⟩ : syracuseStep 1375275 = 2062913) B2062913
theorem B5217331 : Blo 1374006 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B1375287 : Blo 1374006 1375287 := bstep (se 1 (by rfl) ⟨1031465, by rfl⟩ : syracuseStep 1375287 = 2062931) B2062931
theorem B3480641 : Blo 1374006 3480641 := bstep (se 2 (by rfl) ⟨1305240, by rfl⟩ : syracuseStep 3480641 = 2610481) B2610481
theorem B1375307 : Blo 1374006 1375307 := bstep (se 1 (by rfl) ⟨1031480, by rfl⟩ : syracuseStep 1375307 = 2062961) B2062961
theorem B1375319 : Blo 1374006 1375319 := bstep (se 1 (by rfl) ⟨1031489, by rfl⟩ : syracuseStep 1375319 = 2062979) B2062979
theorem B1375339 : Blo 1374006 1375339 := bstep (se 1 (by rfl) ⟨1031504, by rfl⟩ : syracuseStep 1375339 = 2063009) B2063009
theorem B1375351 : Blo 1374006 1375351 := bstep (se 1 (by rfl) ⟨1031513, by rfl⟩ : syracuseStep 1375351 = 2063027) B2063027
theorem B1547383 : Blo 1374006 1547383 := bstep (se 1 (by rfl) ⟨1160537, by rfl⟩ : syracuseStep 1547383 = 2321075) B2321075
theorem B1375371 : Blo 1374006 1375371 := bstep (se 1 (by rfl) ⟨1031528, by rfl⟩ : syracuseStep 1375371 = 2063057) B2063057
theorem B1375383 : Blo 1374006 1375383 := bstep (se 1 (by rfl) ⟨1031537, by rfl⟩ : syracuseStep 1375383 = 2063075) B2063075
theorem B2038937 : Blo 1374006 2038937 := bstep (se 2 (by rfl) ⟨764601, by rfl⟩ : syracuseStep 2038937 = 1529203) B1529203
theorem B1375403 : Blo 1374006 1375403 := bstep (se 1 (by rfl) ⟨1031552, by rfl⟩ : syracuseStep 1375403 = 2063105) B2063105
theorem B1375415 : Blo 1374006 1375415 := bstep (se 1 (by rfl) ⟨1031561, by rfl⟩ : syracuseStep 1375415 = 2063123) B2063123
theorem B1375435 : Blo 1374006 1375435 := bstep (se 1 (by rfl) ⟨1031576, by rfl⟩ : syracuseStep 1375435 = 2063153) B2063153
theorem B3136727 : Blo 1374006 3136727 := bstep (se 1 (by rfl) ⟨2352545, by rfl⟩ : syracuseStep 3136727 = 4705091) B4705091
theorem B1375447 : Blo 1374006 1375447 := bstep (se 1 (by rfl) ⟨1031585, by rfl⟩ : syracuseStep 1375447 = 2063171) B2063171
theorem B4463837 : Blo 1374006 4463837 := bstep (se 3 (by rfl) ⟨836969, by rfl⟩ : syracuseStep 4463837 = 1673939) B1673939
theorem B1375467 : Blo 1374006 1375467 := bstep (se 1 (by rfl) ⟨1031600, by rfl⟩ : syracuseStep 1375467 = 2063201) B2063201
theorem B1375479 : Blo 1374006 1375479 := bstep (se 1 (by rfl) ⟨1031609, by rfl⟩ : syracuseStep 1375479 = 2063219) B2063219
theorem B1375499 : Blo 1374006 1375499 := bstep (se 1 (by rfl) ⟨1031624, by rfl⟩ : syracuseStep 1375499 = 2063249) B2063249
theorem B5872985 : Blo 1374006 5872985 := bstep (se 2 (by rfl) ⟨2202369, by rfl⟩ : syracuseStep 5872985 = 4404739) B4404739
theorem B171589013 : Blo 1374006 171589013 := bstep (se 6 (by rfl) ⟨4021617, by rfl⟩ : syracuseStep 171589013 = 8043235) B8043235
theorem B11738519 : Blo 1374006 11738519 := bstep (se 1 (by rfl) ⟨8803889, by rfl⟩ : syracuseStep 11738519 = 17607779) B17607779
theorem B3481177 : Blo 1374006 3481177 := bstep (se 2 (by rfl) ⟨1305441, by rfl⟩ : syracuseStep 3481177 = 2610883) B2610883
theorem B3481643 : Blo 1374006 3481643 := bstep (se 1 (by rfl) ⟨2611232, by rfl⟩ : syracuseStep 3481643 = 5222465) B5222465
theorem B15065149 : Blo 1374006 15065149 := bstep (se 3 (by rfl) ⟨2824715, by rfl⟩ : syracuseStep 15065149 = 5649431) B5649431
theorem B7430231 : Blo 1374006 7430231 := bstep (se 1 (by rfl) ⟨5572673, by rfl⟩ : syracuseStep 7430231 = 11145347) B11145347
theorem B44589149 : Blo 1374006 44589149 := bstep (se 3 (by rfl) ⟨8360465, by rfl⟩ : syracuseStep 44589149 = 16720931) B16720931
theorem B11739269 : Blo 1374006 11739269 := bstep (se 4 (by rfl) ⟨1100556, by rfl⟩ : syracuseStep 11739269 = 2201113) B2201113
theorem B1958089 : Blo 1374006 1958089 := bstep (se 2 (by rfl) ⟨734283, by rfl⟩ : syracuseStep 1958089 = 1468567) B1468567
theorem B7430401 : Blo 1374006 7430401 := bstep (se 2 (by rfl) ⟨2786400, by rfl⟩ : syracuseStep 7430401 = 5572801) B5572801
theorem B7832011 : Blo 1374006 7832011 := bstep (se 1 (by rfl) ⟨5874008, by rfl⟩ : syracuseStep 7832011 = 11748017) B11748017
theorem B4637303 : Blo 1374006 4637303 := bstep (se 1 (by rfl) ⟨3477977, by rfl⟩ : syracuseStep 4637303 = 6955955) B6955955
theorem B5653111 : Blo 1374006 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B2319239 : Blo 1374006 2319239 := bstep (se 1 (by rfl) ⟨1739429, by rfl⟩ : syracuseStep 2319239 = 3478859) B3478859
theorem B4637897 : Blo 1374006 4637897 := bstep (se 2 (by rfl) ⟨1739211, by rfl⟩ : syracuseStep 4637897 = 3478423) B3478423
theorem B3302689 : Blo 1374006 3302689 := bstep (se 2 (by rfl) ⟨1238508, by rfl⟩ : syracuseStep 3302689 = 2477017) B2477017
theorem B6956441 : Blo 1374006 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B8807939 : Blo 1374006 8807939 := bstep (se 1 (by rfl) ⟨6605954, by rfl⟩ : syracuseStep 8807939 = 13211909) B13211909
theorem B2319887 : Blo 1374006 2319887 := bstep (se 1 (by rfl) ⟨1739915, by rfl⟩ : syracuseStep 2319887 = 3479831) B3479831
theorem B2352655 : Blo 1374006 2352655 := bstep (se 1 (by rfl) ⟨1764491, by rfl⟩ : syracuseStep 2352655 = 3528983) B3528983
theorem B2934647 : Blo 1374006 2934647 := bstep (se 1 (by rfl) ⟨2200985, by rfl⟩ : syracuseStep 2934647 = 4401971) B4401971
theorem B4638599 : Blo 1374006 4638599 := bstep (se 1 (by rfl) ⟨3478949, by rfl⟩ : syracuseStep 4638599 = 6957899) B6957899
theorem B2320427 : Blo 1374006 2320427 := bstep (se 1 (by rfl) ⟨1740320, by rfl⟩ : syracuseStep 2320427 = 3480641) B3480641
theorem B6604861 : Blo 1374006 6604861 := bstep (se 3 (by rfl) ⟨1238411, by rfl⟩ : syracuseStep 6604861 = 2476823) B2476823
theorem B2091151 : Blo 1374006 2091151 := bstep (se 1 (by rfl) ⟨1568363, by rfl⟩ : syracuseStep 2091151 = 3136727) B3136727
theorem B2975891 : Blo 1374006 2975891 := bstep (se 1 (by rfl) ⟨2231918, by rfl⟩ : syracuseStep 2975891 = 4463837) B4463837
theorem B1738999 : Blo 1374006 1738999 := bstep (se 1 (by rfl) ⟨1304249, by rfl⟩ : syracuseStep 1738999 = 2608499) B2608499
theorem B4638977 : Blo 1374006 4638977 := bstep (se 2 (by rfl) ⟨1739616, by rfl⟩ : syracuseStep 4638977 = 3479233) B3479233
theorem B7825679 : Blo 1374006 7825679 := bstep (se 1 (by rfl) ⟨5869259, by rfl⟩ : syracuseStep 7825679 = 11738519) B11738519
theorem B2320825 : Blo 1374006 2320825 := bstep (se 2 (by rfl) ⟨870309, by rfl⟩ : syracuseStep 2320825 = 1740619) B1740619
theorem B11749931 : Blo 1374006 11749931 := bstep (se 1 (by rfl) ⟨8812448, by rfl⟩ : syracuseStep 11749931 = 17624897) B17624897
theorem B1739323 : Blo 1374006 1739323 := bstep (se 1 (by rfl) ⟨1304492, by rfl⟩ : syracuseStep 1739323 = 2608985) B2608985
theorem B13208183 : Blo 1374006 13208183 := bstep (se 1 (by rfl) ⟨9906137, by rfl⟩ : syracuseStep 13208183 = 19812275) B19812275
theorem B2787959 : Blo 1374006 2787959 := bstep (se 1 (by rfl) ⟨2090969, by rfl⟩ : syracuseStep 2787959 = 4181939) B4181939
theorem B4180747 : Blo 1374006 4180747 := bstep (se 1 (by rfl) ⟨3135560, by rfl⟩ : syracuseStep 4180747 = 6271121) B6271121
theorem B9055091 : Blo 1374006 9055091 := bstep (se 1 (by rfl) ⟨6791318, by rfl⟩ : syracuseStep 9055091 = 13582637) B13582637
theorem B1739819 : Blo 1374006 1739819 := bstep (se 1 (by rfl) ⟨1304864, by rfl⟩ : syracuseStep 1739819 = 2609729) B2609729
theorem B4639787 : Blo 1374006 4639787 := bstep (se 1 (by rfl) ⟨3479840, by rfl⟩ : syracuseStep 4639787 = 6959681) B6959681
theorem B5221691 : Blo 1374006 5221691 := bstep (se 1 (by rfl) ⟨3916268, by rfl⟩ : syracuseStep 5221691 = 7832537) B7832537
theorem B3091859 : Blo 1374006 3091859 := bstep (se 1 (by rfl) ⟨2318894, by rfl⟩ : syracuseStep 3091859 = 4637789) B4637789
theorem B3091913 : Blo 1374006 3091913 := bstep (se 2 (by rfl) ⟨1159467, by rfl⟩ : syracuseStep 3091913 = 2318935) B2318935
theorem B1740295 : Blo 1374006 1740295 := bstep (se 1 (by rfl) ⟨1305221, by rfl⟩ : syracuseStep 1740295 = 2610443) B2610443
theorem B2608787 : Blo 1374006 2608787 := bstep (se 1 (by rfl) ⟨1956590, by rfl⟩ : syracuseStep 2608787 = 3913181) B3913181
theorem B7827137 : Blo 1374006 7827137 := bstep (se 2 (by rfl) ⟨2935176, by rfl⟩ : syracuseStep 7827137 = 5870353) B5870353
theorem B2608841 : Blo 1374006 2608841 := bstep (se 2 (by rfl) ⟨978315, by rfl⟩ : syracuseStep 2608841 = 1956631) B1956631
theorem B2232079 : Blo 1374006 2232079 := bstep (se 1 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 2232079 = 3348119) B3348119
theorem B5222177 : Blo 1374006 5222177 := bstep (se 2 (by rfl) ⟨1958316, by rfl⟩ : syracuseStep 5222177 = 3916633) B3916633
theorem B2608939 : Blo 1374006 2608939 := bstep (se 1 (by rfl) ⟨1956704, by rfl⟩ : syracuseStep 2608939 = 3913409) B3913409
theorem B15069079 : Blo 1374006 15069079 := bstep (se 1 (by rfl) ⟨11301809, by rfl⟩ : syracuseStep 15069079 = 22603619) B22603619
theorem B6959033 : Blo 1374006 6959033 := bstep (se 2 (by rfl) ⟨2609637, by rfl⟩ : syracuseStep 6959033 = 5219275) B5219275
theorem B1740791 : Blo 1374006 1740791 := bstep (se 1 (by rfl) ⟨1305593, by rfl⟩ : syracuseStep 1740791 = 2611187) B2611187
theorem B6606859 : Blo 1374006 6606859 := bstep (se 1 (by rfl) ⟨4955144, by rfl⟩ : syracuseStep 6606859 = 9910289) B9910289
theorem B2609167 : Blo 1374006 2609167 := bstep (se 1 (by rfl) ⟨1956875, by rfl⟩ : syracuseStep 2609167 = 3913751) B3913751
theorem B2682895 : Blo 1374006 2682895 := bstep (se 1 (by rfl) ⟨2012171, by rfl⟩ : syracuseStep 2682895 = 4024343) B4024343
theorem B3715159 : Blo 1374006 3715159 := bstep (se 1 (by rfl) ⟨2786369, by rfl⟩ : syracuseStep 3715159 = 5572739) B5572739
theorem B7934071 : Blo 1374006 7934071 := bstep (se 1 (by rfl) ⟨5950553, by rfl⟩ : syracuseStep 7934071 = 11901107) B11901107
theorem B3092615 : Blo 1374006 3092615 := bstep (se 1 (by rfl) ⟨2319461, by rfl⟩ : syracuseStep 3092615 = 4638923) B4638923
theorem B3092795 : Blo 1374006 3092795 := bstep (se 1 (by rfl) ⟨2319596, by rfl⟩ : syracuseStep 3092795 = 4639193) B4639193
theorem B4641083 : Blo 1374006 4641083 := bstep (se 1 (by rfl) ⟨3480812, by rfl⟩ : syracuseStep 4641083 = 6961625) B6961625
theorem B3092921 : Blo 1374006 3092921 := bstep (se 2 (by rfl) ⟨1159845, by rfl⟩ : syracuseStep 3092921 = 2319691) B2319691
theorem B3478049 : Blo 1374006 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B7434989 : Blo 1374006 7434989 := bstep (se 3 (by rfl) ⟨1394060, by rfl⟩ : syracuseStep 7434989 = 2788121) B2788121
theorem B2061047 : Blo 1374006 2061047 := bstep (se 1 (by rfl) ⟨1545785, by rfl⟩ : syracuseStep 2061047 = 3091571) B3091571
theorem B2061071 : Blo 1374006 2061071 := bstep (se 1 (by rfl) ⟨1545803, by rfl⟩ : syracuseStep 2061071 = 3091607) B3091607
theorem B3093263 : Blo 1374006 3093263 := bstep (se 1 (by rfl) ⟨2319947, by rfl⟩ : syracuseStep 3093263 = 4639895) B4639895
theorem B3093281 : Blo 1374006 3093281 := bstep (se 2 (by rfl) ⟨1159980, by rfl⟩ : syracuseStep 3093281 = 2319961) B2319961
theorem B4641569 : Blo 1374006 4641569 := bstep (se 2 (by rfl) ⟨1740588, by rfl⟩ : syracuseStep 4641569 = 3481177) B3481177
theorem B2061113 : Blo 1374006 2061113 := bstep (se 2 (by rfl) ⟨772917, by rfl⟩ : syracuseStep 2061113 = 1545835) B1545835
theorem B16724825 : Blo 1374006 16724825 := bstep (se 2 (by rfl) ⟨6271809, by rfl⟩ : syracuseStep 16724825 = 12543619) B12543619
theorem B2061191 : Blo 1374006 2061191 := bstep (se 1 (by rfl) ⟨1545893, by rfl⟩ : syracuseStep 2061191 = 3091787) B3091787
theorem B2061227 : Blo 1374006 2061227 := bstep (se 1 (by rfl) ⟨1545920, by rfl⟩ : syracuseStep 2061227 = 3091841) B3091841
theorem B2061257 : Blo 1374006 2061257 := bstep (se 2 (by rfl) ⟨772971, by rfl⟩ : syracuseStep 2061257 = 1545943) B1545943
theorem B17617925 : Blo 1374006 17617925 := bstep (se 4 (by rfl) ⟨1651680, by rfl⟩ : syracuseStep 17617925 = 3303361) B3303361
theorem B2061371 : Blo 1374006 2061371 := bstep (se 1 (by rfl) ⟨1546028, by rfl⟩ : syracuseStep 2061371 = 3092057) B3092057
theorem B7435331 : Blo 1374006 7435331 := bstep (se 1 (by rfl) ⟨5576498, by rfl⟩ : syracuseStep 7435331 = 11152997) B11152997
theorem B2061431 : Blo 1374006 2061431 := bstep (se 1 (by rfl) ⟨1546073, by rfl⟩ : syracuseStep 2061431 = 3092147) B3092147
theorem B3093623 : Blo 1374006 3093623 := bstep (se 1 (by rfl) ⟨2320217, by rfl⟩ : syracuseStep 3093623 = 4640435) B4640435
theorem B2061455 : Blo 1374006 2061455 := bstep (se 1 (by rfl) ⟨1546091, by rfl⟩ : syracuseStep 2061455 = 3092183) B3092183
theorem B2061497 : Blo 1374006 2061497 := bstep (se 2 (by rfl) ⟨773061, by rfl⟩ : syracuseStep 2061497 = 1546123) B1546123
theorem B6960329 : Blo 1374006 6960329 := bstep (se 2 (by rfl) ⟨2610123, by rfl⟩ : syracuseStep 6960329 = 5220247) B5220247
theorem B2061575 : Blo 1374006 2061575 := bstep (se 1 (by rfl) ⟨1546181, by rfl⟩ : syracuseStep 2061575 = 3092363) B3092363
theorem B2061611 : Blo 1374006 2061611 := bstep (se 1 (by rfl) ⟨1546208, by rfl⟩ : syracuseStep 2061611 = 3092417) B3092417
theorem B3093803 : Blo 1374006 3093803 := bstep (se 1 (by rfl) ⟨2320352, by rfl⟩ : syracuseStep 3093803 = 4640705) B4640705
theorem B2061641 : Blo 1374006 2061641 := bstep (se 2 (by rfl) ⟨773115, by rfl⟩ : syracuseStep 2061641 = 1546231) B1546231
theorem B4642163 : Blo 1374006 4642163 := bstep (se 1 (by rfl) ⟨3481622, by rfl⟩ : syracuseStep 4642163 = 6963245) B6963245
theorem B52868537 : Blo 1374006 52868537 := bstep (se 2 (by rfl) ⟨19825701, by rfl⟩ : syracuseStep 52868537 = 39651403) B39651403
theorem B2061755 : Blo 1374006 2061755 := bstep (se 1 (by rfl) ⟨1546316, by rfl⟩ : syracuseStep 2061755 = 3092633) B3092633
theorem B2061815 : Blo 1374006 2061815 := bstep (se 1 (by rfl) ⟨1546361, by rfl⟩ : syracuseStep 2061815 = 3092723) B3092723
theorem B3479051 : Blo 1374006 3479051 := bstep (se 1 (by rfl) ⟨2609288, by rfl⟩ : syracuseStep 3479051 = 5218577) B5218577
theorem B2061839 : Blo 1374006 2061839 := bstep (se 1 (by rfl) ⟨1546379, by rfl⟩ : syracuseStep 2061839 = 3092759) B3092759
theorem B2610731 : Blo 1374006 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B2061881 : Blo 1374006 2061881 := bstep (se 2 (by rfl) ⟨773205, by rfl⟩ : syracuseStep 2061881 = 1546411) B1546411
theorem B1488443 : Blo 1374006 1488443 := bstep (se 1 (by rfl) ⟨1116332, by rfl⟩ : syracuseStep 1488443 = 2232665) B2232665
theorem B8361539 : Blo 1374006 8361539 := bstep (se 1 (by rfl) ⟨6271154, by rfl⟩ : syracuseStep 8361539 = 12542309) B12542309
theorem B23484005 : Blo 1374006 23484005 := bstep (se 4 (by rfl) ⟨2201625, by rfl⟩ : syracuseStep 23484005 = 4403251) B4403251
theorem B2061959 : Blo 1374006 2061959 := bstep (se 1 (by rfl) ⟨1546469, by rfl⟩ : syracuseStep 2061959 = 3092939) B3092939
theorem B1545871 : Blo 1374006 1545871 := bstep (se 1 (by rfl) ⟨1159403, by rfl⟩ : syracuseStep 1545871 = 2318807) B2318807
theorem B3913363 : Blo 1374006 3913363 := bstep (se 1 (by rfl) ⟨2935022, by rfl⟩ : syracuseStep 3913363 = 5870045) B5870045
theorem B3094163 : Blo 1374006 3094163 := bstep (se 1 (by rfl) ⟨2320622, by rfl⟩ : syracuseStep 3094163 = 4641245) B4641245
theorem B2061995 : Blo 1374006 2061995 := bstep (se 1 (by rfl) ⟨1546496, by rfl⟩ : syracuseStep 2061995 = 3092993) B3092993
theorem B2062025 : Blo 1374006 2062025 := bstep (se 2 (by rfl) ⟨773259, by rfl⟩ : syracuseStep 2062025 = 1546519) B1546519
theorem B3094217 : Blo 1374006 3094217 := bstep (se 2 (by rfl) ⟨1160331, by rfl⟩ : syracuseStep 3094217 = 2320663) B2320663
theorem B4953889 : Blo 1374006 4953889 := bstep (se 2 (by rfl) ⟨1857708, by rfl⟩ : syracuseStep 4953889 = 3715417) B3715417
theorem B1374011 : Blo 1374006 1374011 := bstep (se 1 (by rfl) ⟨1030508, by rfl⟩ : syracuseStep 1374011 = 2061017) B2061017
theorem B2062139 : Blo 1374006 2062139 := bstep (se 1 (by rfl) ⟨1546604, by rfl⟩ : syracuseStep 2062139 = 3093209) B3093209
theorem B10434419 : Blo 1374006 10434419 := bstep (se 1 (by rfl) ⟨7825814, by rfl⟩ : syracuseStep 10434419 = 15651629) B15651629
theorem B2062199 : Blo 1374006 2062199 := bstep (se 1 (by rfl) ⟨1546649, by rfl⟩ : syracuseStep 2062199 = 3093299) B3093299
theorem B3913591 : Blo 1374006 3913591 := bstep (se 1 (by rfl) ⟨2935193, by rfl⟩ : syracuseStep 3913591 = 5870387) B5870387
theorem B1374087 : Blo 1374006 1374087 := bstep (se 1 (by rfl) ⟨1030565, by rfl⟩ : syracuseStep 1374087 = 2061131) B2061131
theorem B1374095 : Blo 1374006 1374095 := bstep (se 1 (by rfl) ⟨1030571, by rfl⟩ : syracuseStep 1374095 = 2061143) B2061143
theorem B2062223 : Blo 1374006 2062223 := bstep (se 1 (by rfl) ⟨1546667, by rfl⟩ : syracuseStep 2062223 = 3093335) B3093335
theorem B2062265 : Blo 1374006 2062265 := bstep (se 2 (by rfl) ⟨773349, by rfl⟩ : syracuseStep 2062265 = 1546699) B1546699
theorem B1374139 : Blo 1374006 1374139 := bstep (se 1 (by rfl) ⟨1030604, by rfl⟩ : syracuseStep 1374139 = 2061209) B2061209
theorem B1374215 : Blo 1374006 1374215 := bstep (se 1 (by rfl) ⟨1030661, by rfl⟩ : syracuseStep 1374215 = 2061323) B2061323
theorem B2062343 : Blo 1374006 2062343 := bstep (se 1 (by rfl) ⟨1546757, by rfl⟩ : syracuseStep 2062343 = 3093515) B3093515
theorem B1374223 : Blo 1374006 1374223 := bstep (se 1 (by rfl) ⟨1030667, by rfl⟩ : syracuseStep 1374223 = 2061335) B2061335
theorem B2062379 : Blo 1374006 2062379 := bstep (se 1 (by rfl) ⟨1546784, by rfl⟩ : syracuseStep 2062379 = 3093569) B3093569
theorem B1374267 : Blo 1374006 1374267 := bstep (se 1 (by rfl) ⟨1030700, by rfl⟩ : syracuseStep 1374267 = 2061401) B2061401
theorem B2062409 : Blo 1374006 2062409 := bstep (se 2 (by rfl) ⟨773403, by rfl⟩ : syracuseStep 2062409 = 1546807) B1546807
theorem B1374343 : Blo 1374006 1374343 := bstep (se 1 (by rfl) ⟨1030757, by rfl⟩ : syracuseStep 1374343 = 2061515) B2061515
theorem B1546375 : Blo 1374006 1546375 := bstep (se 1 (by rfl) ⟨1159781, by rfl⟩ : syracuseStep 1546375 = 2319563) B2319563
theorem B3528839 : Blo 1374006 3528839 := bstep (se 1 (by rfl) ⟨2646629, by rfl⟩ : syracuseStep 3528839 = 5293259) B5293259
theorem B1374351 : Blo 1374006 1374351 := bstep (se 1 (by rfl) ⟨1030763, by rfl⟩ : syracuseStep 1374351 = 2061527) B2061527
theorem B3479699 : Blo 1374006 3479699 := bstep (se 1 (by rfl) ⟨2609774, by rfl⟩ : syracuseStep 3479699 = 5219549) B5219549
theorem B1374395 : Blo 1374006 1374395 := bstep (se 1 (by rfl) ⟨1030796, by rfl⟩ : syracuseStep 1374395 = 2061593) B2061593
theorem B2062523 : Blo 1374006 2062523 := bstep (se 1 (by rfl) ⟨1546892, by rfl⟩ : syracuseStep 2062523 = 3093785) B3093785
theorem B2062583 : Blo 1374006 2062583 := bstep (se 1 (by rfl) ⟨1546937, by rfl⟩ : syracuseStep 2062583 = 3093875) B3093875
theorem B1374471 : Blo 1374006 1374471 := bstep (se 1 (by rfl) ⟨1030853, by rfl⟩ : syracuseStep 1374471 = 2061707) B2061707
theorem B1374479 : Blo 1374006 1374479 := bstep (se 1 (by rfl) ⟨1030859, by rfl⟩ : syracuseStep 1374479 = 2061719) B2061719
theorem B2062607 : Blo 1374006 2062607 := bstep (se 1 (by rfl) ⟨1546955, by rfl⟩ : syracuseStep 2062607 = 3093911) B3093911
theorem B2062649 : Blo 1374006 2062649 := bstep (se 2 (by rfl) ⟨773493, by rfl⟩ : syracuseStep 2062649 = 1546987) B1546987
theorem B1374523 : Blo 1374006 1374523 := bstep (se 1 (by rfl) ⟨1030892, by rfl⟩ : syracuseStep 1374523 = 2061785) B2061785
theorem B1546555 : Blo 1374006 1546555 := bstep (se 1 (by rfl) ⟨1159916, by rfl⟩ : syracuseStep 1546555 = 2319833) B2319833
theorem B1374599 : Blo 1374006 1374599 := bstep (se 1 (by rfl) ⟨1030949, by rfl⟩ : syracuseStep 1374599 = 2061899) B2061899
theorem B2062727 : Blo 1374006 2062727 := bstep (se 1 (by rfl) ⟨1547045, by rfl⟩ : syracuseStep 2062727 = 3094091) B3094091
theorem B1374607 : Blo 1374006 1374607 := bstep (se 1 (by rfl) ⟨1030955, by rfl⟩ : syracuseStep 1374607 = 2061911) B2061911
theorem B8591761 : Blo 1374006 8591761 := bstep (se 2 (by rfl) ⟨3221910, by rfl⟩ : syracuseStep 8591761 = 6443821) B6443821
theorem B2062763 : Blo 1374006 2062763 := bstep (se 1 (by rfl) ⟨1547072, by rfl⟩ : syracuseStep 2062763 = 3094145) B3094145
theorem B3479993 : Blo 1374006 3479993 := bstep (se 2 (by rfl) ⟨1304997, by rfl⟩ : syracuseStep 3479993 = 2609995) B2609995
theorem B1374651 : Blo 1374006 1374651 := bstep (se 1 (by rfl) ⟨1030988, by rfl⟩ : syracuseStep 1374651 = 2061977) B2061977
theorem B2062793 : Blo 1374006 2062793 := bstep (se 2 (by rfl) ⟨773547, by rfl⟩ : syracuseStep 2062793 = 1547095) B1547095
theorem B1374727 : Blo 1374006 1374727 := bstep (se 1 (by rfl) ⟨1031045, by rfl⟩ : syracuseStep 1374727 = 2062091) B2062091
theorem B1374735 : Blo 1374006 1374735 := bstep (se 1 (by rfl) ⟨1031051, by rfl⟩ : syracuseStep 1374735 = 2062103) B2062103
theorem B7428631 : Blo 1374006 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B1374779 : Blo 1374006 1374779 := bstep (se 1 (by rfl) ⟨1031084, by rfl⟩ : syracuseStep 1374779 = 2062169) B2062169
theorem B2062907 : Blo 1374006 2062907 := bstep (se 1 (by rfl) ⟨1547180, by rfl⟩ : syracuseStep 2062907 = 3094361) B3094361
theorem B2062967 : Blo 1374006 2062967 := bstep (se 1 (by rfl) ⟨1547225, by rfl⟩ : syracuseStep 2062967 = 3094451) B3094451
theorem B1374855 : Blo 1374006 1374855 := bstep (se 1 (by rfl) ⟨1031141, by rfl⟩ : syracuseStep 1374855 = 2062283) B2062283
theorem B1374863 : Blo 1374006 1374863 := bstep (se 1 (by rfl) ⟨1031147, by rfl⟩ : syracuseStep 1374863 = 2062295) B2062295
theorem B2062991 : Blo 1374006 2062991 := bstep (se 1 (by rfl) ⟨1547243, by rfl⟩ : syracuseStep 2062991 = 3094487) B3094487
theorem B2063033 : Blo 1374006 2063033 := bstep (se 2 (by rfl) ⟨773637, by rfl⟩ : syracuseStep 2063033 = 1547275) B1547275
theorem B1374907 : Blo 1374006 1374907 := bstep (se 1 (by rfl) ⟨1031180, by rfl⟩ : syracuseStep 1374907 = 2062361) B2062361
theorem B1374983 : Blo 1374006 1374983 := bstep (se 1 (by rfl) ⟨1031237, by rfl⟩ : syracuseStep 1374983 = 2062475) B2062475
theorem B2063111 : Blo 1374006 2063111 := bstep (se 1 (by rfl) ⟨1547333, by rfl⟩ : syracuseStep 2063111 = 3094667) B3094667
theorem B1374991 : Blo 1374006 1374991 := bstep (se 1 (by rfl) ⟨1031243, by rfl⟩ : syracuseStep 1374991 = 2062487) B2062487
theorem B7535375 : Blo 1374006 7535375 := bstep (se 1 (by rfl) ⟨5651531, by rfl⟩ : syracuseStep 7535375 = 11303063) B11303063
theorem B1547023 : Blo 1374006 1547023 := bstep (se 1 (by rfl) ⟨1160267, by rfl⟩ : syracuseStep 1547023 = 2320535) B2320535
theorem B2063147 : Blo 1374006 2063147 := bstep (se 1 (by rfl) ⟨1547360, by rfl⟩ : syracuseStep 2063147 = 3094721) B3094721
theorem B1375035 : Blo 1374006 1375035 := bstep (se 1 (by rfl) ⟨1031276, by rfl⟩ : syracuseStep 1375035 = 2062553) B2062553
theorem B2063177 : Blo 1374006 2063177 := bstep (se 2 (by rfl) ⟨773691, by rfl⟩ : syracuseStep 2063177 = 1547383) B1547383
theorem B3718003 : Blo 1374006 3718003 := bstep (se 1 (by rfl) ⟨2788502, by rfl⟩ : syracuseStep 3718003 = 5577005) B5577005
theorem B1956727 : Blo 1374006 1956727 := bstep (se 1 (by rfl) ⟨1467545, by rfl⟩ : syracuseStep 1956727 = 2935091) B2935091
theorem B4832135 : Blo 1374006 4832135 := bstep (se 1 (by rfl) ⟨3624101, by rfl⟩ : syracuseStep 4832135 = 7248203) B7248203
theorem B1375111 : Blo 1374006 1375111 := bstep (se 1 (by rfl) ⟨1031333, by rfl⟩ : syracuseStep 1375111 = 2062667) B2062667
theorem B1375119 : Blo 1374006 1375119 := bstep (se 1 (by rfl) ⟨1031339, by rfl⟩ : syracuseStep 1375119 = 2062679) B2062679
theorem B21748661 : Blo 1374006 21748661 := bstep (se 5 (by rfl) ⟨1019468, by rfl⟩ : syracuseStep 21748661 = 2038937) B2038937
theorem B1375163 : Blo 1374006 1375163 := bstep (se 1 (by rfl) ⟨1031372, by rfl⟩ : syracuseStep 1375163 = 2062745) B2062745
theorem B4021249 : Blo 1374006 4021249 := bstep (se 2 (by rfl) ⟨1507968, by rfl⟩ : syracuseStep 4021249 = 3015937) B3015937
theorem B1375239 : Blo 1374006 1375239 := bstep (se 1 (by rfl) ⟨1031429, by rfl⟩ : syracuseStep 1375239 = 2062859) B2062859
theorem B1375247 : Blo 1374006 1375247 := bstep (se 1 (by rfl) ⟨1031435, by rfl⟩ : syracuseStep 1375247 = 2062871) B2062871
theorem B1375291 : Blo 1374006 1375291 := bstep (se 1 (by rfl) ⟨1031468, by rfl⟩ : syracuseStep 1375291 = 2062937) B2062937
theorem B3914867 : Blo 1374006 3914867 := bstep (se 1 (by rfl) ⟨2936150, by rfl⟩ : syracuseStep 3914867 = 5872301) B5872301
theorem B3480691 : Blo 1374006 3480691 := bstep (se 1 (by rfl) ⟨2610518, by rfl⟩ : syracuseStep 3480691 = 5221037) B5221037
theorem B1375367 : Blo 1374006 1375367 := bstep (se 1 (by rfl) ⟨1031525, by rfl⟩ : syracuseStep 1375367 = 2063051) B2063051
theorem B1375375 : Blo 1374006 1375375 := bstep (se 1 (by rfl) ⟨1031531, by rfl⟩ : syracuseStep 1375375 = 2063063) B2063063
theorem B1375419 : Blo 1374006 1375419 := bstep (se 1 (by rfl) ⟨1031564, by rfl⟩ : syracuseStep 1375419 = 2063129) B2063129
theorem B3480833 : Blo 1374006 3480833 := bstep (se 2 (by rfl) ⟨1305312, by rfl⟩ : syracuseStep 3480833 = 2610625) B2610625
theorem B1375495 : Blo 1374006 1375495 := bstep (se 1 (by rfl) ⟨1031621, by rfl⟩ : syracuseStep 1375495 = 2063243) B2063243
theorem B1375503 : Blo 1374006 1375503 := bstep (se 1 (by rfl) ⟨1031627, by rfl⟩ : syracuseStep 1375503 = 2063255) B2063255
theorem B11746619 : Blo 1374006 11746619 := bstep (se 1 (by rfl) ⟨8809964, by rfl⟩ : syracuseStep 11746619 = 17619929) B17619929
theorem B33430961 : Blo 1374006 33430961 := bstep (se 2 (by rfl) ⟨12536610, by rfl⟩ : syracuseStep 33430961 = 25073221) B25073221
theorem B3915209 : Blo 1374006 3915209 := bstep (se 2 (by rfl) ⟨1468203, by rfl⟩ : syracuseStep 3915209 = 2936407) B2936407
theorem B5217803 : Blo 1374006 5217803 := bstep (se 1 (by rfl) ⟨3913352, by rfl⟩ : syracuseStep 5217803 = 7826705) B7826705
theorem B3915323 : Blo 1374006 3915323 := bstep (se 1 (by rfl) ⟨2936492, by rfl⟩ : syracuseStep 3915323 = 5872985) B5872985
theorem B4955735 : Blo 1374006 4955735 := bstep (se 1 (by rfl) ⟨3716801, by rfl⟩ : syracuseStep 4955735 = 7433603) B7433603
theorem B114392675 : Blo 1374006 114392675 := bstep (se 1 (by rfl) ⟨85794506, by rfl⟩ : syracuseStep 114392675 = 171589013) B171589013
theorem B16719479 : Blo 1374006 16719479 := bstep (se 1 (by rfl) ⟨12539609, by rfl⟩ : syracuseStep 16719479 = 25079219) B25079219
theorem B3915449 : Blo 1374006 3915449 := bstep (se 2 (by rfl) ⟨1468293, by rfl⟩ : syracuseStep 3915449 = 2936587) B2936587
theorem B3481289 : Blo 1374006 3481289 := bstep (se 2 (by rfl) ⟨1305483, by rfl⟩ : syracuseStep 3481289 = 2610967) B2610967
theorem B14114533 : Blo 1374006 14114533 := bstep (se 4 (by rfl) ⟨1323237, by rfl⟩ : syracuseStep 14114533 = 2646475) B2646475
theorem B1957775 : Blo 1374006 1957775 := bstep (se 1 (by rfl) ⟨1468331, by rfl⟩ : syracuseStep 1957775 = 2936663) B2936663
theorem B8806481 : Blo 1374006 8806481 := bstep (se 2 (by rfl) ⟨3302430, by rfl⟩ : syracuseStep 8806481 = 6604861) B6604861
theorem B20086865 : Blo 1374006 20086865 := bstep (se 2 (by rfl) ⟨7532574, by rfl⟩ : syracuseStep 20086865 = 15065149) B15065149
theorem B2318665 : Blo 1374006 2318665 := bstep (se 2 (by rfl) ⟨869499, by rfl⟩ : syracuseStep 2318665 = 1738999) B1738999
theorem B2318699 : Blo 1374006 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B4956659 : Blo 1374006 4956659 := bstep (se 1 (by rfl) ⟨3717494, by rfl⟩ : syracuseStep 4956659 = 7434989) B7434989
theorem B11149883 : Blo 1374006 11149883 := bstep (se 1 (by rfl) ⟨8362412, by rfl⟩ : syracuseStep 11149883 = 16724825) B16724825
theorem B9904841 : Blo 1374006 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B4956887 : Blo 1374006 4956887 := bstep (se 1 (by rfl) ⟨3717665, by rfl⟩ : syracuseStep 4956887 = 7435331) B7435331
theorem B2319097 : Blo 1374006 2319097 := bstep (se 2 (by rfl) ⟨869661, by rfl⟩ : syracuseStep 2319097 = 1739323) B1739323
theorem B7537481 : Blo 1374006 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B4637627 : Blo 1374006 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B2319367 : Blo 1374006 2319367 := bstep (se 1 (by rfl) ⟨1739525, by rfl⟩ : syracuseStep 2319367 = 3479051) B3479051
theorem B15656003 : Blo 1374006 15656003 := bstep (se 1 (by rfl) ⟨11742002, by rfl⟩ : syracuseStep 15656003 = 23484005) B23484005
theorem B4957337 : Blo 1374006 4957337 := bstep (se 2 (by rfl) ⟨1859001, by rfl⟩ : syracuseStep 4957337 = 3718003) B3718003
theorem B6956279 : Blo 1374006 6956279 := bstep (se 1 (by rfl) ⟨5217209, by rfl⟩ : syracuseStep 6956279 = 10434419) B10434419
theorem B11904421 : Blo 1374006 11904421 := bstep (se 4 (by rfl) ⟨1116039, by rfl⟩ : syracuseStep 11904421 = 2232079) B2232079
theorem B2352559 : Blo 1374006 2352559 := bstep (se 1 (by rfl) ⟨1764419, by rfl⟩ : syracuseStep 2352559 = 3528839) B3528839
theorem B2319799 : Blo 1374006 2319799 := bstep (se 1 (by rfl) ⟨1739849, by rfl⟩ : syracuseStep 2319799 = 3479699) B3479699
theorem B2319995 : Blo 1374006 2319995 := bstep (se 1 (by rfl) ⟨1739996, by rfl⟩ : syracuseStep 2319995 = 3479993) B3479993
theorem B7833287 : Blo 1374006 7833287 := bstep (se 1 (by rfl) ⟨5874965, by rfl⟩ : syracuseStep 7833287 = 11749931) B11749931
theorem B6956765 : Blo 1374006 6956765 := bstep (se 3 (by rfl) ⟨1304393, by rfl⟩ : syracuseStep 6956765 = 2608787) B2608787
theorem B5023583 : Blo 1374006 5023583 := bstep (se 1 (by rfl) ⟨3767687, by rfl⟩ : syracuseStep 5023583 = 7535375) B7535375
theorem B3221423 : Blo 1374006 3221423 := bstep (se 1 (by rfl) ⟨2416067, by rfl⟩ : syracuseStep 3221423 = 4832135) B4832135
theorem B2320393 : Blo 1374006 2320393 := bstep (se 2 (by rfl) ⟨870147, by rfl⟩ : syracuseStep 2320393 = 1740295) B1740295
theorem B2320555 : Blo 1374006 2320555 := bstep (se 1 (by rfl) ⟨1740416, by rfl⟩ : syracuseStep 2320555 = 3480833) B3480833
theorem B18819377 : Blo 1374006 18819377 := bstep (se 2 (by rfl) ⟨7057266, by rfl⟩ : syracuseStep 18819377 = 14114533) B14114533
theorem B5220733 : Blo 1374006 5220733 := bstep (se 3 (by rfl) ⟨978887, by rfl⟩ : syracuseStep 5220733 = 1957775) B1957775
theorem B6605185 : Blo 1374006 6605185 := bstep (se 2 (by rfl) ⟨2476944, by rfl⟩ : syracuseStep 6605185 = 4953889) B4953889
theorem B3303823 : Blo 1374006 3303823 := bstep (se 1 (by rfl) ⟨2477867, by rfl⟩ : syracuseStep 3303823 = 4955735) B4955735
theorem B76261783 : Blo 1374006 76261783 := bstep (se 1 (by rfl) ⟨57196337, by rfl⟩ : syracuseStep 76261783 = 114392675) B114392675
theorem B1739227 : Blo 1374006 1739227 := bstep (se 1 (by rfl) ⟨1304420, by rfl⟩ : syracuseStep 1739227 = 2608841) B2608841
theorem B2320859 : Blo 1374006 2320859 := bstep (se 1 (by rfl) ⟨1740644, by rfl⟩ : syracuseStep 2320859 = 3481289) B3481289
theorem B4639355 : Blo 1374006 4639355 := bstep (se 1 (by rfl) ⟨3479516, by rfl⟩ : syracuseStep 4639355 = 6959033) B6959033
theorem B8809145 : Blo 1374006 8809145 := bstep (se 2 (by rfl) ⟨3303429, by rfl⟩ : syracuseStep 8809145 = 6606859) B6606859
theorem B2321095 : Blo 1374006 2321095 := bstep (se 1 (by rfl) ⟨1740821, by rfl⟩ : syracuseStep 2321095 = 3481643) B3481643
theorem B7826179 : Blo 1374006 7826179 := bstep (se 1 (by rfl) ⟨5869634, by rfl⟩ : syracuseStep 7826179 = 11739269) B11739269
theorem B4639517 : Blo 1374006 4639517 := bstep (se 3 (by rfl) ⟨869909, by rfl⟩ : syracuseStep 4639517 = 1739819) B1739819
theorem B10578761 : Blo 1374006 10578761 := bstep (se 2 (by rfl) ⟨3967035, by rfl⟩ : syracuseStep 10578761 = 7934071) B7934071
theorem B2788201 : Blo 1374006 2788201 := bstep (se 2 (by rfl) ⟨1045575, by rfl⟩ : syracuseStep 2788201 = 2091151) B2091151
theorem B9907201 : Blo 1374006 9907201 := bstep (se 2 (by rfl) ⟨3715200, by rfl⟩ : syracuseStep 9907201 = 7430401) B7430401
theorem B3091535 : Blo 1374006 3091535 := bstep (se 1 (by rfl) ⟨2318651, by rfl⟩ : syracuseStep 3091535 = 4637303) B4637303
theorem B11455681 : Blo 1374006 11455681 := bstep (se 2 (by rfl) ⟨4295880, by rfl⟩ : syracuseStep 11455681 = 8591761) B8591761
theorem B3091931 : Blo 1374006 3091931 := bstep (se 1 (by rfl) ⟨2318948, by rfl⟩ : syracuseStep 3091931 = 4637897) B4637897
theorem B4640219 : Blo 1374006 4640219 := bstep (se 1 (by rfl) ⟨3480164, by rfl⟩ : syracuseStep 4640219 = 6960329) B6960329
theorem B35245691 : Blo 1374006 35245691 := bstep (se 1 (by rfl) ⟨26434268, by rfl⟩ : syracuseStep 35245691 = 52868537) B52868537
theorem B5574329 : Blo 1374006 5574329 := bstep (se 2 (by rfl) ⟨2090373, by rfl⟩ : syracuseStep 5574329 = 4180747) B4180747
theorem B5574359 : Blo 1374006 5574359 := bstep (se 1 (by rfl) ⟨4180769, by rfl⟩ : syracuseStep 5574359 = 8361539) B8361539
theorem B3092399 : Blo 1374006 3092399 := bstep (se 1 (by rfl) ⟨2319299, by rfl⟩ : syracuseStep 3092399 = 4638599) B4638599
theorem B5361665 : Blo 1374006 5361665 := bstep (se 2 (by rfl) ⟨2010624, by rfl⟩ : syracuseStep 5361665 = 4021249) B4021249
theorem B4640921 : Blo 1374006 4640921 := bstep (se 2 (by rfl) ⟨1740345, by rfl⟩ : syracuseStep 4640921 = 3480691) B3480691
theorem B3969181 : Blo 1374006 3969181 := bstep (se 3 (by rfl) ⟨744221, by rfl⟩ : syracuseStep 3969181 = 1488443) B1488443
theorem B3092651 : Blo 1374006 3092651 := bstep (se 1 (by rfl) ⟨2319488, by rfl⟩ : syracuseStep 3092651 = 4638977) B4638977
theorem B4403585 : Blo 1374006 4403585 := bstep (se 2 (by rfl) ⟨1651344, by rfl⟩ : syracuseStep 4403585 = 3302689) B3302689
theorem B3093191 : Blo 1374006 3093191 := bstep (se 1 (by rfl) ⟨2319893, by rfl⟩ : syracuseStep 3093191 = 4639787) B4639787
theorem B2609911 : Blo 1374006 2609911 := bstep (se 1 (by rfl) ⟨1957433, by rfl⟩ : syracuseStep 2609911 = 3914867) B3914867
theorem B2061161 : Blo 1374006 2061161 := bstep (se 2 (by rfl) ⟨772935, by rfl⟩ : syracuseStep 2061161 = 1545871) B1545871
theorem B2061239 : Blo 1374006 2061239 := bstep (se 1 (by rfl) ⟨1545929, by rfl⟩ : syracuseStep 2061239 = 3091859) B3091859
theorem B22287307 : Blo 1374006 22287307 := bstep (se 1 (by rfl) ⟨16715480, by rfl⟩ : syracuseStep 22287307 = 33430961) B33430961
theorem B2061275 : Blo 1374006 2061275 := bstep (se 1 (by rfl) ⟨1545956, by rfl⟩ : syracuseStep 2061275 = 3091913) B3091913
theorem B2610139 : Blo 1374006 2610139 := bstep (se 1 (by rfl) ⟨1957604, by rfl⟩ : syracuseStep 2610139 = 3915209) B3915209
theorem B24146909 : Blo 1374006 24146909 := bstep (se 3 (by rfl) ⟨4527545, by rfl⟩ : syracuseStep 24146909 = 9055091) B9055091
theorem B3478535 : Blo 1374006 3478535 := bstep (se 1 (by rfl) ⟨2608901, by rfl⟩ : syracuseStep 3478535 = 5217803) B5217803
theorem B2610215 : Blo 1374006 2610215 := bstep (se 1 (by rfl) ⟨1957661, by rfl⟩ : syracuseStep 2610215 = 3915323) B3915323
theorem B3478585 : Blo 1374006 3478585 := bstep (se 2 (by rfl) ⟨1304469, by rfl⟩ : syracuseStep 3478585 = 2608939) B2608939
theorem B11146319 : Blo 1374006 11146319 := bstep (se 1 (by rfl) ⟨8359739, by rfl⟩ : syracuseStep 11146319 = 16719479) B16719479
theorem B2610299 : Blo 1374006 2610299 := bstep (se 1 (by rfl) ⟨1957724, by rfl⟩ : syracuseStep 2610299 = 3915449) B3915449
theorem B20092105 : Blo 1374006 20092105 := bstep (se 2 (by rfl) ⟨7534539, by rfl⟩ : syracuseStep 20092105 = 15069079) B15069079
theorem B4642109 : Blo 1374006 4642109 := bstep (se 3 (by rfl) ⟨870395, by rfl⟩ : syracuseStep 4642109 = 1740791) B1740791
theorem B3478889 : Blo 1374006 3478889 := bstep (se 2 (by rfl) ⟨1304583, by rfl⟩ : syracuseStep 3478889 = 2609167) B2609167
theorem B3577193 : Blo 1374006 3577193 := bstep (se 2 (by rfl) ⟨1341447, by rfl⟩ : syracuseStep 3577193 = 2682895) B2682895
theorem B4953487 : Blo 1374006 4953487 := bstep (se 1 (by rfl) ⟨3715115, by rfl⟩ : syracuseStep 4953487 = 7430231) B7430231
theorem B29726099 : Blo 1374006 29726099 := bstep (se 1 (by rfl) ⟨22294574, by rfl⟩ : syracuseStep 29726099 = 44589149) B44589149
theorem B12547493 : Blo 1374006 12547493 := bstep (se 4 (by rfl) ⟨1176327, by rfl⟩ : syracuseStep 12547493 = 2352655) B2352655
theorem B2061743 : Blo 1374006 2061743 := bstep (se 1 (by rfl) ⟨1546307, by rfl⟩ : syracuseStep 2061743 = 3092615) B3092615
theorem B4953545 : Blo 1374006 4953545 := bstep (se 2 (by rfl) ⟨1857579, by rfl⟩ : syracuseStep 4953545 = 3715159) B3715159
theorem B2061833 : Blo 1374006 2061833 := bstep (se 2 (by rfl) ⟨773187, by rfl⟩ : syracuseStep 2061833 = 1546375) B1546375
theorem B2061863 : Blo 1374006 2061863 := bstep (se 1 (by rfl) ⟨1546397, by rfl⟩ : syracuseStep 2061863 = 3092795) B3092795
theorem B3094055 : Blo 1374006 3094055 := bstep (se 1 (by rfl) ⟨2320541, by rfl⟩ : syracuseStep 3094055 = 4641083) B4641083
theorem B2610785 : Blo 1374006 2610785 := bstep (se 2 (by rfl) ⟨979044, by rfl⟩ : syracuseStep 2610785 = 1958089) B1958089
theorem B2061947 : Blo 1374006 2061947 := bstep (se 1 (by rfl) ⟨1546460, by rfl⟩ : syracuseStep 2061947 = 3092921) B3092921
theorem B2062073 : Blo 1374006 2062073 := bstep (se 2 (by rfl) ⟨773277, by rfl⟩ : syracuseStep 2062073 = 1546555) B1546555
theorem B1374031 : Blo 1374006 1374031 := bstep (se 1 (by rfl) ⟨1030523, by rfl⟩ : syracuseStep 1374031 = 2061047) B2061047
theorem B1374047 : Blo 1374006 1374047 := bstep (se 1 (by rfl) ⟨1030535, by rfl⟩ : syracuseStep 1374047 = 2061071) B2061071
theorem B2062175 : Blo 1374006 2062175 := bstep (se 1 (by rfl) ⟨1546631, by rfl⟩ : syracuseStep 2062175 = 3093263) B3093263
theorem B2062187 : Blo 1374006 2062187 := bstep (se 1 (by rfl) ⟨1546640, by rfl⟩ : syracuseStep 2062187 = 3093281) B3093281
theorem B3094379 : Blo 1374006 3094379 := bstep (se 1 (by rfl) ⟨2320784, by rfl⟩ : syracuseStep 3094379 = 4641569) B4641569
theorem B1374075 : Blo 1374006 1374075 := bstep (se 1 (by rfl) ⟨1030556, by rfl⟩ : syracuseStep 1374075 = 2061113) B2061113
theorem B3094433 : Blo 1374006 3094433 := bstep (se 2 (by rfl) ⟨1160412, by rfl⟩ : syracuseStep 3094433 = 2320825) B2320825
theorem B1374127 : Blo 1374006 1374127 := bstep (se 1 (by rfl) ⟨1030595, by rfl⟩ : syracuseStep 1374127 = 2061191) B2061191
theorem B1546159 : Blo 1374006 1546159 := bstep (se 1 (by rfl) ⟨1159619, by rfl⟩ : syracuseStep 1546159 = 2319239) B2319239
theorem B10442681 : Blo 1374006 10442681 := bstep (se 2 (by rfl) ⟨3916005, by rfl⟩ : syracuseStep 10442681 = 7832011) B7832011
theorem B1374151 : Blo 1374006 1374151 := bstep (se 1 (by rfl) ⟨1030613, by rfl⟩ : syracuseStep 1374151 = 2061227) B2061227
theorem B1374171 : Blo 1374006 1374171 := bstep (se 1 (by rfl) ⟨1030628, by rfl⟩ : syracuseStep 1374171 = 2061257) B2061257
theorem B11745283 : Blo 1374006 11745283 := bstep (se 1 (by rfl) ⟨8808962, by rfl⟩ : syracuseStep 11745283 = 17617925) B17617925
theorem B1374247 : Blo 1374006 1374247 := bstep (se 1 (by rfl) ⟨1030685, by rfl⟩ : syracuseStep 1374247 = 2061371) B2061371
theorem B1374287 : Blo 1374006 1374287 := bstep (se 1 (by rfl) ⟨1030715, by rfl⟩ : syracuseStep 1374287 = 2061431) B2061431
theorem B2062415 : Blo 1374006 2062415 := bstep (se 1 (by rfl) ⟨1546811, by rfl⟩ : syracuseStep 2062415 = 3093623) B3093623
theorem B1374303 : Blo 1374006 1374303 := bstep (se 1 (by rfl) ⟨1030727, by rfl⟩ : syracuseStep 1374303 = 2061455) B2061455
theorem B1374331 : Blo 1374006 1374331 := bstep (se 1 (by rfl) ⟨1030748, by rfl⟩ : syracuseStep 1374331 = 2061497) B2061497
theorem B1374383 : Blo 1374006 1374383 := bstep (se 1 (by rfl) ⟨1030787, by rfl⟩ : syracuseStep 1374383 = 2061575) B2061575
theorem B1374407 : Blo 1374006 1374407 := bstep (se 1 (by rfl) ⟨1030805, by rfl⟩ : syracuseStep 1374407 = 2061611) B2061611
theorem B2062535 : Blo 1374006 2062535 := bstep (se 1 (by rfl) ⟨1546901, by rfl⟩ : syracuseStep 2062535 = 3093803) B3093803
theorem B1374427 : Blo 1374006 1374427 := bstep (se 1 (by rfl) ⟨1030820, by rfl⟩ : syracuseStep 1374427 = 2061641) B2061641
theorem B3094775 : Blo 1374006 3094775 := bstep (se 1 (by rfl) ⟨2321081, by rfl⟩ : syracuseStep 3094775 = 4642163) B4642163
theorem B1374503 : Blo 1374006 1374503 := bstep (se 1 (by rfl) ⟨1030877, by rfl⟩ : syracuseStep 1374503 = 2061755) B2061755
theorem B1374543 : Blo 1374006 1374543 := bstep (se 1 (by rfl) ⟨1030907, by rfl⟩ : syracuseStep 1374543 = 2061815) B2061815
theorem B5871959 : Blo 1374006 5871959 := bstep (se 1 (by rfl) ⟨4403969, by rfl⟩ : syracuseStep 5871959 = 8807939) B8807939
theorem B1374559 : Blo 1374006 1374559 := bstep (se 1 (by rfl) ⟨1030919, by rfl⟩ : syracuseStep 1374559 = 2061839) B2061839
theorem B1546591 : Blo 1374006 1546591 := bstep (se 1 (by rfl) ⟨1159943, by rfl⟩ : syracuseStep 1546591 = 2319887) B2319887
theorem B2062697 : Blo 1374006 2062697 := bstep (se 2 (by rfl) ⟨773511, by rfl⟩ : syracuseStep 2062697 = 1547023) B1547023
theorem B1374587 : Blo 1374006 1374587 := bstep (se 1 (by rfl) ⟨1030940, by rfl⟩ : syracuseStep 1374587 = 2061881) B2061881
theorem B1374639 : Blo 1374006 1374639 := bstep (se 1 (by rfl) ⟨1030979, by rfl⟩ : syracuseStep 1374639 = 2061959) B2061959
theorem B2062775 : Blo 1374006 2062775 := bstep (se 1 (by rfl) ⟨1547081, by rfl⟩ : syracuseStep 2062775 = 3094163) B3094163
theorem B1374663 : Blo 1374006 1374663 := bstep (se 1 (by rfl) ⟨1030997, by rfl⟩ : syracuseStep 1374663 = 2061995) B2061995
theorem B1374683 : Blo 1374006 1374683 := bstep (se 1 (by rfl) ⟨1031012, by rfl⟩ : syracuseStep 1374683 = 2062025) B2062025
theorem B2062811 : Blo 1374006 2062811 := bstep (se 1 (by rfl) ⟨1547108, by rfl⟩ : syracuseStep 2062811 = 3094217) B3094217
theorem B1374759 : Blo 1374006 1374759 := bstep (se 1 (by rfl) ⟨1031069, by rfl⟩ : syracuseStep 1374759 = 2062139) B2062139
theorem B1956431 : Blo 1374006 1956431 := bstep (se 1 (by rfl) ⟨1467323, by rfl⟩ : syracuseStep 1956431 = 2934647) B2934647
theorem B1374799 : Blo 1374006 1374799 := bstep (se 1 (by rfl) ⟨1031099, by rfl⟩ : syracuseStep 1374799 = 2062199) B2062199
theorem B1374815 : Blo 1374006 1374815 := bstep (se 1 (by rfl) ⟨1031111, by rfl⟩ : syracuseStep 1374815 = 2062223) B2062223
theorem B1374843 : Blo 1374006 1374843 := bstep (se 1 (by rfl) ⟨1031132, by rfl⟩ : syracuseStep 1374843 = 2062265) B2062265
theorem B1374895 : Blo 1374006 1374895 := bstep (se 1 (by rfl) ⟨1031171, by rfl⟩ : syracuseStep 1374895 = 2062343) B2062343
theorem B1374919 : Blo 1374006 1374919 := bstep (se 1 (by rfl) ⟨1031189, by rfl⟩ : syracuseStep 1374919 = 2062379) B2062379
theorem B1546951 : Blo 1374006 1546951 := bstep (se 1 (by rfl) ⟨1160213, by rfl⟩ : syracuseStep 1546951 = 2320427) B2320427
theorem B1374939 : Blo 1374006 1374939 := bstep (se 1 (by rfl) ⟨1031204, by rfl⟩ : syracuseStep 1374939 = 2062409) B2062409
theorem B6961949 : Blo 1374006 6961949 := bstep (se 3 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 6961949 = 2610731) B2610731
theorem B1375015 : Blo 1374006 1375015 := bstep (se 1 (by rfl) ⟨1031261, by rfl⟩ : syracuseStep 1375015 = 2062523) B2062523
theorem B1375055 : Blo 1374006 1375055 := bstep (se 1 (by rfl) ⟨1031291, by rfl⟩ : syracuseStep 1375055 = 2062583) B2062583
theorem B5217119 : Blo 1374006 5217119 := bstep (se 1 (by rfl) ⟨3912839, by rfl⟩ : syracuseStep 5217119 = 7825679) B7825679
theorem B1375071 : Blo 1374006 1375071 := bstep (se 1 (by rfl) ⟨1031303, by rfl⟩ : syracuseStep 1375071 = 2062607) B2062607
theorem B31742837 : Blo 1374006 31742837 := bstep (se 5 (by rfl) ⟨1487945, by rfl⟩ : syracuseStep 31742837 = 2975891) B2975891
theorem B1375099 : Blo 1374006 1375099 := bstep (se 1 (by rfl) ⟨1031324, by rfl⟩ : syracuseStep 1375099 = 2062649) B2062649
theorem B1375151 : Blo 1374006 1375151 := bstep (se 1 (by rfl) ⟨1031363, by rfl⟩ : syracuseStep 1375151 = 2062727) B2062727
theorem B1375175 : Blo 1374006 1375175 := bstep (se 1 (by rfl) ⟨1031381, by rfl⟩ : syracuseStep 1375175 = 2062763) B2062763
theorem B1375195 : Blo 1374006 1375195 := bstep (se 1 (by rfl) ⟨1031396, by rfl⟩ : syracuseStep 1375195 = 2062793) B2062793
theorem B1375271 : Blo 1374006 1375271 := bstep (se 1 (by rfl) ⟨1031453, by rfl⟩ : syracuseStep 1375271 = 2062907) B2062907
theorem B8805455 : Blo 1374006 8805455 := bstep (se 1 (by rfl) ⟨6604091, by rfl⟩ : syracuseStep 8805455 = 13208183) B13208183
theorem B1858639 : Blo 1374006 1858639 := bstep (se 1 (by rfl) ⟨1393979, by rfl⟩ : syracuseStep 1858639 = 2787959) B2787959
theorem B1375311 : Blo 1374006 1375311 := bstep (se 1 (by rfl) ⟨1031483, by rfl⟩ : syracuseStep 1375311 = 2062967) B2062967
theorem B1375327 : Blo 1374006 1375327 := bstep (se 1 (by rfl) ⟨1031495, by rfl⟩ : syracuseStep 1375327 = 2062991) B2062991
theorem B1375355 : Blo 1374006 1375355 := bstep (se 1 (by rfl) ⟨1031516, by rfl⟩ : syracuseStep 1375355 = 2063033) B2063033
theorem B1375407 : Blo 1374006 1375407 := bstep (se 1 (by rfl) ⟨1031555, by rfl⟩ : syracuseStep 1375407 = 2063111) B2063111
theorem B1375431 : Blo 1374006 1375431 := bstep (se 1 (by rfl) ⟨1031573, by rfl⟩ : syracuseStep 1375431 = 2063147) B2063147
theorem B1375451 : Blo 1374006 1375451 := bstep (se 1 (by rfl) ⟨1031588, by rfl⟩ : syracuseStep 1375451 = 2063177) B2063177
theorem B14499107 : Blo 1374006 14499107 := bstep (se 1 (by rfl) ⟨10874330, by rfl⟩ : syracuseStep 14499107 = 21748661) B21748661
theorem B10435877 : Blo 1374006 10435877 := bstep (se 4 (by rfl) ⟨978363, by rfl⟩ : syracuseStep 10435877 = 1956727) B1956727
theorem B5217817 : Blo 1374006 5217817 := bstep (se 2 (by rfl) ⟨1956681, by rfl⟩ : syracuseStep 5217817 = 3913363) B3913363
theorem B7831079 : Blo 1374006 7831079 := bstep (se 1 (by rfl) ⟨5873309, by rfl⟩ : syracuseStep 7831079 = 11746619) B11746619
theorem B3481127 : Blo 1374006 3481127 := bstep (se 1 (by rfl) ⟨2610845, by rfl⟩ : syracuseStep 3481127 = 5221691) B5221691
theorem B5218091 : Blo 1374006 5218091 := bstep (se 1 (by rfl) ⟨3913568, by rfl⟩ : syracuseStep 5218091 = 7827137) B7827137
theorem B5218121 : Blo 1374006 5218121 := bstep (se 2 (by rfl) ⟨1956795, by rfl⟩ : syracuseStep 5218121 = 3913591) B3913591
theorem B3481451 : Blo 1374006 3481451 := bstep (se 1 (by rfl) ⟨2611088, by rfl⟩ : syracuseStep 3481451 = 5222177) B5222177
theorem B6603227 : Blo 1374006 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B8806913 : Blo 1374006 8806913 := bstep (se 2 (by rfl) ⟨3302592, by rfl⟩ : syracuseStep 8806913 = 6605185) B6605185
theorem B2318969 : Blo 1374006 2318969 := bstep (se 2 (by rfl) ⟨869613, by rfl⟩ : syracuseStep 2318969 = 1739227) B1739227
theorem B16097939 : Blo 1374006 16097939 := bstep (se 1 (by rfl) ⟨12073454, by rfl⟩ : syracuseStep 16097939 = 24146909) B24146909
theorem B2319023 : Blo 1374006 2319023 := bstep (se 1 (by rfl) ⟨1739267, by rfl⟩ : syracuseStep 2319023 = 3478535) B3478535
theorem B10437335 : Blo 1374006 10437335 := bstep (se 1 (by rfl) ⟨7828001, by rfl⟩ : syracuseStep 10437335 = 15656003) B15656003
theorem B7430879 : Blo 1374006 7430879 := bstep (se 1 (by rfl) ⟨5573159, by rfl⟩ : syracuseStep 7430879 = 11146319) B11146319
theorem B21168965 : Blo 1374006 21168965 := bstep (se 4 (by rfl) ⟨1984590, by rfl⟩ : syracuseStep 21168965 = 3969181) B3969181
theorem B4637519 : Blo 1374006 4637519 := bstep (se 1 (by rfl) ⟨3478139, by rfl⟩ : syracuseStep 4637519 = 6956279) B6956279
theorem B2319259 : Blo 1374006 2319259 := bstep (se 1 (by rfl) ⟨1739444, by rfl⟩ : syracuseStep 2319259 = 3478889) B3478889
theorem B2384795 : Blo 1374006 2384795 := bstep (se 1 (by rfl) ⟨1788596, by rfl⟩ : syracuseStep 2384795 = 3577193) B3577193
theorem B19817399 : Blo 1374006 19817399 := bstep (se 1 (by rfl) ⟨14863049, by rfl⟩ : syracuseStep 19817399 = 29726099) B29726099
theorem B8364995 : Blo 1374006 8364995 := bstep (se 1 (by rfl) ⟨6273746, by rfl⟩ : syracuseStep 8364995 = 12547493) B12547493
theorem B3302363 : Blo 1374006 3302363 := bstep (se 1 (by rfl) ⟨2476772, by rfl⟩ : syracuseStep 3302363 = 4953545) B4953545
theorem B4637843 : Blo 1374006 4637843 := bstep (se 1 (by rfl) ⟨3478382, by rfl⟩ : syracuseStep 4637843 = 6956765) B6956765
theorem B2147615 : Blo 1374006 2147615 := bstep (se 1 (by rfl) ⟨1610711, by rfl⟩ : syracuseStep 2147615 = 3221423) B3221423
theorem B4638113 : Blo 1374006 4638113 := bstep (se 2 (by rfl) ⟨1739292, by rfl⟩ : syracuseStep 4638113 = 3478585) B3478585
theorem B26789473 : Blo 1374006 26789473 := bstep (se 2 (by rfl) ⟨10046052, by rfl⟩ : syracuseStep 26789473 = 20092105) B20092105
theorem B6604649 : Blo 1374006 6604649 := bstep (se 2 (by rfl) ⟨2476743, by rfl⟩ : syracuseStep 6604649 = 4953487) B4953487
theorem B14870405 : Blo 1374006 14870405 := bstep (se 4 (by rfl) ⟨1394100, by rfl⟩ : syracuseStep 14870405 = 2788201) B2788201
theorem B21161891 : Blo 1374006 21161891 := bstep (se 1 (by rfl) ⟨15871418, by rfl⟩ : syracuseStep 21161891 = 31742837) B31742837
theorem B6957089 : Blo 1374006 6957089 := bstep (se 2 (by rfl) ⟨2608908, by rfl⟩ : syracuseStep 6957089 = 5217817) B5217817
theorem B6957251 : Blo 1374006 6957251 := bstep (se 1 (by rfl) ⟨5217938, by rfl⟩ : syracuseStep 6957251 = 10435877) B10435877
theorem B5220719 : Blo 1374006 5220719 := bstep (se 1 (by rfl) ⟨3915539, by rfl⟩ : syracuseStep 5220719 = 7831079) B7831079
theorem B2320751 : Blo 1374006 2320751 := bstep (se 1 (by rfl) ⟨1740563, by rfl⟩ : syracuseStep 2320751 = 3481127) B3481127
theorem B23497127 : Blo 1374006 23497127 := bstep (se 1 (by rfl) ⟨17622845, by rfl⟩ : syracuseStep 23497127 = 35245691) B35245691
theorem B2320967 : Blo 1374006 2320967 := bstep (se 1 (by rfl) ⟨1740725, by rfl⟩ : syracuseStep 2320967 = 3481451) B3481451
theorem B57191093 : Blo 1374006 57191093 := bstep (se 5 (by rfl) ⟨2680832, by rfl⟩ : syracuseStep 57191093 = 5361665) B5361665
theorem B3304439 : Blo 1374006 3304439 := bstep (se 1 (by rfl) ⟨2478329, by rfl⟩ : syracuseStep 3304439 = 4956659) B4956659
theorem B7433255 : Blo 1374006 7433255 := bstep (se 1 (by rfl) ⟨5574941, by rfl⟩ : syracuseStep 7433255 = 11149883) B11149883
theorem B3091553 : Blo 1374006 3091553 := bstep (se 2 (by rfl) ⟨1159332, by rfl⟩ : syracuseStep 3091553 = 2318665) B2318665
theorem B101682377 : Blo 1374006 101682377 := bstep (se 2 (by rfl) ⟨38130891, by rfl⟩ : syracuseStep 101682377 = 76261783) B76261783
theorem B5024987 : Blo 1374006 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B3091751 : Blo 1374006 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B1740143 : Blo 1374006 1740143 := bstep (se 1 (by rfl) ⟨1305107, by rfl⟩ : syracuseStep 1740143 = 2610215) B2610215
theorem B1740199 : Blo 1374006 1740199 := bstep (se 1 (by rfl) ⟨1305149, by rfl⟩ : syracuseStep 1740199 = 2610299) B2610299
theorem B3304891 : Blo 1374006 3304891 := bstep (se 1 (by rfl) ⟨2478668, by rfl⟩ : syracuseStep 3304891 = 4957337) B4957337
theorem B3092129 : Blo 1374006 3092129 := bstep (se 2 (by rfl) ⟨1159548, by rfl⟩ : syracuseStep 3092129 = 2319097) B2319097
theorem B11742893 : Blo 1374006 11742893 := bstep (se 3 (by rfl) ⟨2201792, by rfl⟩ : syracuseStep 11742893 = 4403585) B4403585
theorem B1740523 : Blo 1374006 1740523 := bstep (se 1 (by rfl) ⟨1305392, by rfl⟩ : syracuseStep 1740523 = 2610785) B2610785
theorem B5222191 : Blo 1374006 5222191 := bstep (se 1 (by rfl) ⟨3916643, by rfl⟩ : syracuseStep 5222191 = 7833287) B7833287
theorem B29716409 : Blo 1374006 29716409 := bstep (se 2 (by rfl) ⟨11143653, by rfl⟩ : syracuseStep 29716409 = 22287307) B22287307
theorem B13209601 : Blo 1374006 13209601 := bstep (se 2 (by rfl) ⟨4953600, by rfl⟩ : syracuseStep 13209601 = 9907201) B9907201
theorem B3092489 : Blo 1374006 3092489 := bstep (se 2 (by rfl) ⟨1159683, by rfl⟩ : syracuseStep 3092489 = 2319367) B2319367
theorem B2478185 : Blo 1374006 2478185 := bstep (se 2 (by rfl) ⟨929319, by rfl⟩ : syracuseStep 2478185 = 1858639) B1858639
theorem B12546251 : Blo 1374006 12546251 := bstep (se 1 (by rfl) ⟨9409688, by rfl⟩ : syracuseStep 12546251 = 18819377) B18819377
theorem B15274241 : Blo 1374006 15274241 := bstep (se 2 (by rfl) ⟨5727840, by rfl⟩ : syracuseStep 15274241 = 11455681) B11455681
theorem B3092903 : Blo 1374006 3092903 := bstep (se 1 (by rfl) ⟨2319677, by rfl⟩ : syracuseStep 3092903 = 4639355) B4639355
theorem B3093011 : Blo 1374006 3093011 := bstep (se 1 (by rfl) ⟨2319758, by rfl⟩ : syracuseStep 3093011 = 4639517) B4639517
theorem B4641299 : Blo 1374006 4641299 := bstep (se 1 (by rfl) ⟨3480974, by rfl⟩ : syracuseStep 4641299 = 6961949) B6961949
theorem B15872561 : Blo 1374006 15872561 := bstep (se 2 (by rfl) ⟨5952210, by rfl⟩ : syracuseStep 15872561 = 11904421) B11904421
theorem B14864957 : Blo 1374006 14864957 := bstep (se 3 (by rfl) ⟨2787179, by rfl⟩ : syracuseStep 14864957 = 5574359) B5574359
theorem B13218365 : Blo 1374006 13218365 := bstep (se 3 (by rfl) ⟨2478443, by rfl⟩ : syracuseStep 13218365 = 4956887) B4956887
theorem B3478079 : Blo 1374006 3478079 := bstep (se 1 (by rfl) ⟨2608559, by rfl⟩ : syracuseStep 3478079 = 5217119) B5217119
theorem B3093065 : Blo 1374006 3093065 := bstep (se 2 (by rfl) ⟨1159899, by rfl⟩ : syracuseStep 3093065 = 2319799) B2319799
theorem B2061023 : Blo 1374006 2061023 := bstep (se 1 (by rfl) ⟨1545767, by rfl⟩ : syracuseStep 2061023 = 3091535) B3091535
theorem B5870303 : Blo 1374006 5870303 := bstep (se 1 (by rfl) ⟨4402727, by rfl⟩ : syracuseStep 5870303 = 8805455) B8805455
theorem B2061287 : Blo 1374006 2061287 := bstep (se 1 (by rfl) ⟨1545965, by rfl⟩ : syracuseStep 2061287 = 3091931) B3091931
theorem B3093479 : Blo 1374006 3093479 := bstep (se 1 (by rfl) ⟨2320109, by rfl⟩ : syracuseStep 3093479 = 4640219) B4640219
theorem B3716219 : Blo 1374006 3716219 := bstep (se 1 (by rfl) ⟨2787164, by rfl⟩ : syracuseStep 3716219 = 5574329) B5574329
theorem B3478727 : Blo 1374006 3478727 := bstep (se 1 (by rfl) ⟨2609045, by rfl⟩ : syracuseStep 3478727 = 5218091) B5218091
theorem B3478747 : Blo 1374006 3478747 := bstep (se 1 (by rfl) ⟨2609060, by rfl⟩ : syracuseStep 3478747 = 5218121) B5218121
theorem B2061545 : Blo 1374006 2061545 := bstep (se 2 (by rfl) ⟨773079, by rfl⟩ : syracuseStep 2061545 = 1546159) B1546159
theorem B2061599 : Blo 1374006 2061599 := bstep (se 1 (by rfl) ⟨1546199, by rfl⟩ : syracuseStep 2061599 = 3092399) B3092399
theorem B15660377 : Blo 1374006 15660377 := bstep (se 2 (by rfl) ⟨5872641, by rfl⟩ : syracuseStep 15660377 = 11745283) B11745283
theorem B3093857 : Blo 1374006 3093857 := bstep (se 2 (by rfl) ⟨1160196, by rfl⟩ : syracuseStep 3093857 = 2320393) B2320393
theorem B5870987 : Blo 1374006 5870987 := bstep (se 1 (by rfl) ⟨4403240, by rfl⟩ : syracuseStep 5870987 = 8806481) B8806481
theorem B13391243 : Blo 1374006 13391243 := bstep (se 1 (by rfl) ⟨10043432, by rfl⟩ : syracuseStep 13391243 = 20086865) B20086865
theorem B3093947 : Blo 1374006 3093947 := bstep (se 1 (by rfl) ⟨2320460, by rfl⟩ : syracuseStep 3093947 = 4640921) B4640921
theorem B2061767 : Blo 1374006 2061767 := bstep (se 1 (by rfl) ⟨1546325, by rfl⟩ : syracuseStep 2061767 = 3092651) B3092651
theorem B3094073 : Blo 1374006 3094073 := bstep (se 2 (by rfl) ⟨1160277, by rfl⟩ : syracuseStep 3094073 = 2320555) B2320555
theorem B1545799 : Blo 1374006 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B2062121 : Blo 1374006 2062121 := bstep (se 2 (by rfl) ⟨773295, by rfl⟩ : syracuseStep 2062121 = 1546591) B1546591
theorem B2062127 : Blo 1374006 2062127 := bstep (se 1 (by rfl) ⟨1546595, by rfl⟩ : syracuseStep 2062127 = 3093191) B3093191
theorem B6960977 : Blo 1374006 6960977 := bstep (se 2 (by rfl) ⟨2610366, by rfl⟩ : syracuseStep 6960977 = 5220733) B5220733
theorem B4405097 : Blo 1374006 4405097 := bstep (se 2 (by rfl) ⟨1651911, by rfl⟩ : syracuseStep 4405097 = 3303823) B3303823
theorem B1374107 : Blo 1374006 1374107 := bstep (se 1 (by rfl) ⟨1030580, by rfl⟩ : syracuseStep 1374107 = 2061161) B2061161
theorem B1374159 : Blo 1374006 1374159 := bstep (se 1 (by rfl) ⟨1030619, by rfl⟩ : syracuseStep 1374159 = 2061239) B2061239
theorem B1374183 : Blo 1374006 1374183 := bstep (se 1 (by rfl) ⟨1030637, by rfl⟩ : syracuseStep 1374183 = 2061275) B2061275
theorem B3094739 : Blo 1374006 3094739 := bstep (se 1 (by rfl) ⟨2321054, by rfl⟩ : syracuseStep 3094739 = 4642109) B4642109
theorem B2062601 : Blo 1374006 2062601 := bstep (se 2 (by rfl) ⟨773475, by rfl⟩ : syracuseStep 2062601 = 1546951) B1546951
theorem B3094793 : Blo 1374006 3094793 := bstep (se 2 (by rfl) ⟨1160547, by rfl⟩ : syracuseStep 3094793 = 2321095) B2321095
theorem B1374495 : Blo 1374006 1374495 := bstep (se 1 (by rfl) ⟨1030871, by rfl⟩ : syracuseStep 1374495 = 2061743) B2061743
theorem B3479881 : Blo 1374006 3479881 := bstep (se 2 (by rfl) ⟨1304955, by rfl⟩ : syracuseStep 3479881 = 2609911) B2609911
theorem B10434905 : Blo 1374006 10434905 := bstep (se 2 (by rfl) ⟨3913089, by rfl⟩ : syracuseStep 10434905 = 7826179) B7826179
theorem B1374555 : Blo 1374006 1374555 := bstep (se 1 (by rfl) ⟨1030916, by rfl⟩ : syracuseStep 1374555 = 2061833) B2061833
theorem B1374575 : Blo 1374006 1374575 := bstep (se 1 (by rfl) ⟨1030931, by rfl⟩ : syracuseStep 1374575 = 2061863) B2061863
theorem B2062703 : Blo 1374006 2062703 := bstep (se 1 (by rfl) ⟨1547027, by rfl⟩ : syracuseStep 2062703 = 3094055) B3094055
theorem B1374631 : Blo 1374006 1374631 := bstep (se 1 (by rfl) ⟨1030973, by rfl⟩ : syracuseStep 1374631 = 2061947) B2061947
theorem B1546663 : Blo 1374006 1546663 := bstep (se 1 (by rfl) ⟨1159997, by rfl⟩ : syracuseStep 1546663 = 2319995) B2319995
theorem B1374715 : Blo 1374006 1374715 := bstep (se 1 (by rfl) ⟨1031036, by rfl⟩ : syracuseStep 1374715 = 2062073) B2062073
theorem B1374783 : Blo 1374006 1374783 := bstep (se 1 (by rfl) ⟨1031087, by rfl⟩ : syracuseStep 1374783 = 2062175) B2062175
theorem B3349055 : Blo 1374006 3349055 := bstep (se 1 (by rfl) ⟨2511791, by rfl⟩ : syracuseStep 3349055 = 5023583) B5023583
theorem B1374791 : Blo 1374006 1374791 := bstep (se 1 (by rfl) ⟨1031093, by rfl⟩ : syracuseStep 1374791 = 2062187) B2062187
theorem B2062919 : Blo 1374006 2062919 := bstep (se 1 (by rfl) ⟨1547189, by rfl⟩ : syracuseStep 2062919 = 3094379) B3094379
theorem B2062955 : Blo 1374006 2062955 := bstep (se 1 (by rfl) ⟨1547216, by rfl⟩ : syracuseStep 2062955 = 3094433) B3094433
theorem B3480185 : Blo 1374006 3480185 := bstep (se 2 (by rfl) ⟨1305069, by rfl⟩ : syracuseStep 3480185 = 2610139) B2610139
theorem B6961787 : Blo 1374006 6961787 := bstep (se 1 (by rfl) ⟨5221340, by rfl⟩ : syracuseStep 6961787 = 10442681) B10442681
theorem B1374943 : Blo 1374006 1374943 := bstep (se 1 (by rfl) ⟨1031207, by rfl⟩ : syracuseStep 1374943 = 2062415) B2062415
theorem B1375023 : Blo 1374006 1375023 := bstep (se 1 (by rfl) ⟨1031267, by rfl⟩ : syracuseStep 1375023 = 2062535) B2062535
theorem B2063183 : Blo 1374006 2063183 := bstep (se 1 (by rfl) ⟨1547387, by rfl⟩ : syracuseStep 2063183 = 3094775) B3094775
theorem B5217149 : Blo 1374006 5217149 := bstep (se 3 (by rfl) ⟨978215, by rfl⟩ : syracuseStep 5217149 = 1956431) B1956431
theorem B3914639 : Blo 1374006 3914639 := bstep (se 1 (by rfl) ⟨2935979, by rfl⟩ : syracuseStep 3914639 = 5871959) B5871959
theorem B1375131 : Blo 1374006 1375131 := bstep (se 1 (by rfl) ⟨1031348, by rfl⟩ : syracuseStep 1375131 = 2062697) B2062697
theorem B1375183 : Blo 1374006 1375183 := bstep (se 1 (by rfl) ⟨1031387, by rfl⟩ : syracuseStep 1375183 = 2062775) B2062775
theorem B1375207 : Blo 1374006 1375207 := bstep (se 1 (by rfl) ⟨1031405, by rfl⟩ : syracuseStep 1375207 = 2062811) B2062811
theorem B1547239 : Blo 1374006 1547239 := bstep (se 1 (by rfl) ⟨1160429, by rfl⟩ : syracuseStep 1547239 = 2320859) B2320859
theorem B5872763 : Blo 1374006 5872763 := bstep (se 1 (by rfl) ⟨4404572, by rfl⟩ : syracuseStep 5872763 = 8809145) B8809145
theorem B7052507 : Blo 1374006 7052507 := bstep (se 1 (by rfl) ⟨5289380, by rfl⟩ : syracuseStep 7052507 = 10578761) B10578761
theorem B3136745 : Blo 1374006 3136745 := bstep (se 2 (by rfl) ⟨1176279, by rfl⟩ : syracuseStep 3136745 = 2352559) B2352559
theorem B9666071 : Blo 1374006 9666071 := bstep (se 1 (by rfl) ⟨7249553, by rfl⟩ : syracuseStep 9666071 = 14499107) B14499107
theorem B17612801 : Blo 1374006 17612801 := bstep (se 2 (by rfl) ⟨6604800, by rfl⟩ : syracuseStep 17612801 = 13209601) B13209601
theorem B8364167 : Blo 1374006 8364167 := bstep (se 1 (by rfl) ⟨6273125, by rfl⟩ : syracuseStep 8364167 = 12546251) B12546251
theorem B10182827 : Blo 1374006 10182827 := bstep (se 1 (by rfl) ⟨7637120, by rfl⟩ : syracuseStep 10182827 = 15274241) B15274241
theorem B2318719 : Blo 1374006 2318719 := bstep (se 1 (by rfl) ⟨1739039, by rfl⟩ : syracuseStep 2318719 = 3478079) B3478079
theorem B10731959 : Blo 1374006 10731959 := bstep (se 1 (by rfl) ⟨8048969, by rfl⟩ : syracuseStep 10731959 = 16097939) B16097939
theorem B142877189 : Blo 1374006 142877189 := bstep (se 4 (by rfl) ⟨13394736, by rfl⟩ : syracuseStep 142877189 = 26789473) B26789473
theorem B8364653 : Blo 1374006 8364653 := bstep (se 3 (by rfl) ⟨1568372, by rfl⟩ : syracuseStep 8364653 = 3136745) B3136745
theorem B2319151 : Blo 1374006 2319151 := bstep (se 1 (by rfl) ⟨1739363, by rfl⟩ : syracuseStep 2319151 = 3478727) B3478727
theorem B9913603 : Blo 1374006 9913603 := bstep (se 1 (by rfl) ⟨7435202, by rfl⟩ : syracuseStep 9913603 = 14870405) B14870405
theorem B14107927 : Blo 1374006 14107927 := bstep (se 1 (by rfl) ⟨10580945, by rfl⟩ : syracuseStep 14107927 = 21161891) B21161891
theorem B4638059 : Blo 1374006 4638059 := bstep (se 1 (by rfl) ⟨3478544, by rfl⟩ : syracuseStep 4638059 = 6957089) B6957089
theorem B4638167 : Blo 1374006 4638167 := bstep (se 1 (by rfl) ⟨3478625, by rfl⟩ : syracuseStep 4638167 = 6957251) B6957251
theorem B6956603 : Blo 1374006 6956603 := bstep (se 1 (by rfl) ⟨5217452, by rfl⟩ : syracuseStep 6956603 = 10434905) B10434905
theorem B15664751 : Blo 1374006 15664751 := bstep (se 1 (by rfl) ⟨11748563, by rfl⟩ : syracuseStep 15664751 = 23497127) B23497127
theorem B4638329 : Blo 1374006 4638329 := bstep (se 2 (by rfl) ⟨1739373, by rfl⟩ : syracuseStep 4638329 = 3478747) B3478747
theorem B2320123 : Blo 1374006 2320123 := bstep (se 1 (by rfl) ⟨1740092, by rfl⟩ : syracuseStep 2320123 = 3480185) B3480185
theorem B38127395 : Blo 1374006 38127395 := bstep (se 1 (by rfl) ⟨28595546, by rfl⟩ : syracuseStep 38127395 = 57191093) B57191093
theorem B2320265 : Blo 1374006 2320265 := bstep (se 2 (by rfl) ⟨870099, by rfl⟩ : syracuseStep 2320265 = 1740199) B1740199
theorem B2320697 : Blo 1374006 2320697 := bstep (se 2 (by rfl) ⟨870261, by rfl⟩ : syracuseStep 2320697 = 1740523) B1740523
theorem B6359453 : Blo 1374006 6359453 := bstep (se 3 (by rfl) ⟨1192397, by rfl⟩ : syracuseStep 6359453 = 2384795) B2384795
theorem B79243757 : Blo 1374006 79243757 := bstep (se 3 (by rfl) ⟨14858204, by rfl⟩ : syracuseStep 79243757 = 29716409) B29716409
theorem B4402151 : Blo 1374006 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B4639841 : Blo 1374006 4639841 := bstep (se 2 (by rfl) ⟨1739940, by rfl⟩ : syracuseStep 4639841 = 3479881) B3479881
theorem B6958223 : Blo 1374006 6958223 := bstep (se 1 (by rfl) ⟨5218667, by rfl⟩ : syracuseStep 6958223 = 10437335) B10437335
theorem B3091679 : Blo 1374006 3091679 := bstep (se 1 (by rfl) ⟨2318759, by rfl⟩ : syracuseStep 3091679 = 4637519) B4637519
theorem B2477479 : Blo 1374006 2477479 := bstep (se 1 (by rfl) ⟨1858109, by rfl⟩ : syracuseStep 2477479 = 3716219) B3716219
theorem B3091895 : Blo 1374006 3091895 := bstep (se 1 (by rfl) ⟨2318921, by rfl⟩ : syracuseStep 3091895 = 4637843) B4637843
theorem B10440251 : Blo 1374006 10440251 := bstep (se 1 (by rfl) ⟨7830188, by rfl⟩ : syracuseStep 10440251 = 15660377) B15660377
theorem B3092075 : Blo 1374006 3092075 := bstep (se 1 (by rfl) ⟨2319056, by rfl⟩ : syracuseStep 3092075 = 4638113) B4638113
theorem B4640381 : Blo 1374006 4640381 := bstep (se 3 (by rfl) ⟨870071, by rfl⟩ : syracuseStep 4640381 = 1740143) B1740143
theorem B3092345 : Blo 1374006 3092345 := bstep (se 2 (by rfl) ⟨1159629, by rfl⟩ : syracuseStep 3092345 = 2319259) B2319259
theorem B4640651 : Blo 1374006 4640651 := bstep (se 1 (by rfl) ⟨3480488, by rfl⟩ : syracuseStep 4640651 = 6960977) B6960977
theorem B4403099 : Blo 1374006 4403099 := bstep (se 1 (by rfl) ⟨3302324, by rfl⟩ : syracuseStep 4403099 = 6604649) B6604649
theorem B2936731 : Blo 1374006 2936731 := bstep (se 1 (by rfl) ⟨2202548, by rfl⟩ : syracuseStep 2936731 = 4405097) B4405097
theorem B2232703 : Blo 1374006 2232703 := bstep (se 1 (by rfl) ⟨1674527, by rfl⟩ : syracuseStep 2232703 = 3349055) B3349055
theorem B4641191 : Blo 1374006 4641191 := bstep (se 1 (by rfl) ⟨3480893, by rfl⟩ : syracuseStep 4641191 = 6961787) B6961787
theorem B3478099 : Blo 1374006 3478099 := bstep (se 1 (by rfl) ⟨2608574, by rfl⟩ : syracuseStep 3478099 = 5217149) B5217149
theorem B2609759 : Blo 1374006 2609759 := bstep (se 1 (by rfl) ⟨1957319, by rfl⟩ : syracuseStep 2609759 = 3914639) B3914639
theorem B2061035 : Blo 1374006 2061035 := bstep (se 1 (by rfl) ⟨1545776, by rfl⟩ : syracuseStep 2061035 = 3091553) B3091553
theorem B2061065 : Blo 1374006 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B2061167 : Blo 1374006 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B6444047 : Blo 1374006 6444047 := bstep (se 1 (by rfl) ⟨4833035, by rfl⟩ : syracuseStep 6444047 = 9666071) B9666071
theorem B2061419 : Blo 1374006 2061419 := bstep (se 1 (by rfl) ⟨1546064, by rfl⟩ : syracuseStep 2061419 = 3092129) B3092129
theorem B7828595 : Blo 1374006 7828595 := bstep (se 1 (by rfl) ⟨5871446, by rfl⟩ : syracuseStep 7828595 = 11742893) B11742893
theorem B2061659 : Blo 1374006 2061659 := bstep (se 1 (by rfl) ⟨1546244, by rfl⟩ : syracuseStep 2061659 = 3092489) B3092489
theorem B1652123 : Blo 1374006 1652123 := bstep (se 1 (by rfl) ⟨1239092, by rfl⟩ : syracuseStep 1652123 = 2478185) B2478185
theorem B2061935 : Blo 1374006 2061935 := bstep (se 1 (by rfl) ⟨1546451, by rfl⟩ : syracuseStep 2061935 = 3092903) B3092903
theorem B5871275 : Blo 1374006 5871275 := bstep (se 1 (by rfl) ⟨4403456, by rfl⟩ : syracuseStep 5871275 = 8806913) B8806913
theorem B2062007 : Blo 1374006 2062007 := bstep (se 1 (by rfl) ⟨1546505, by rfl⟩ : syracuseStep 2062007 = 3093011) B3093011
theorem B3094199 : Blo 1374006 3094199 := bstep (se 1 (by rfl) ⟨2320649, by rfl⟩ : syracuseStep 3094199 = 4641299) B4641299
theorem B10581707 : Blo 1374006 10581707 := bstep (se 1 (by rfl) ⟨7936280, by rfl⟩ : syracuseStep 10581707 = 15872561) B15872561
theorem B9909971 : Blo 1374006 9909971 := bstep (se 1 (by rfl) ⟨7432478, by rfl⟩ : syracuseStep 9909971 = 14864957) B14864957
theorem B8812243 : Blo 1374006 8812243 := bstep (se 1 (by rfl) ⟨6609182, by rfl⟩ : syracuseStep 8812243 = 13218365) B13218365
theorem B2062043 : Blo 1374006 2062043 := bstep (se 1 (by rfl) ⟨1546532, by rfl⟩ : syracuseStep 2062043 = 3093065) B3093065
theorem B1545979 : Blo 1374006 1545979 := bstep (se 1 (by rfl) ⟨1159484, by rfl⟩ : syracuseStep 1545979 = 2318969) B2318969
theorem B1546015 : Blo 1374006 1546015 := bstep (se 1 (by rfl) ⟨1159511, by rfl⟩ : syracuseStep 1546015 = 2319023) B2319023
theorem B1374015 : Blo 1374006 1374015 := bstep (se 1 (by rfl) ⟨1030511, by rfl⟩ : syracuseStep 1374015 = 2061023) B2061023
theorem B3913535 : Blo 1374006 3913535 := bstep (se 1 (by rfl) ⟨2935151, by rfl⟩ : syracuseStep 3913535 = 5870303) B5870303
theorem B14112643 : Blo 1374006 14112643 := bstep (se 1 (by rfl) ⟨10584482, by rfl⟩ : syracuseStep 14112643 = 21168965) B21168965
theorem B2062217 : Blo 1374006 2062217 := bstep (se 2 (by rfl) ⟨773331, by rfl⟩ : syracuseStep 2062217 = 1546663) B1546663
theorem B13211599 : Blo 1374006 13211599 := bstep (se 1 (by rfl) ⟨9908699, by rfl⟩ : syracuseStep 13211599 = 19817399) B19817399
theorem B5576663 : Blo 1374006 5576663 := bstep (se 1 (by rfl) ⟨4182497, by rfl⟩ : syracuseStep 5576663 = 8364995) B8364995
theorem B2201575 : Blo 1374006 2201575 := bstep (se 1 (by rfl) ⟨1651181, by rfl⟩ : syracuseStep 2201575 = 3302363) B3302363
theorem B1374191 : Blo 1374006 1374191 := bstep (se 1 (by rfl) ⟨1030643, by rfl⟩ : syracuseStep 1374191 = 2061287) B2061287
theorem B2062319 : Blo 1374006 2062319 := bstep (se 1 (by rfl) ⟨1546739, by rfl⟩ : syracuseStep 2062319 = 3093479) B3093479
theorem B1374363 : Blo 1374006 1374363 := bstep (se 1 (by rfl) ⟨1030772, by rfl⟩ : syracuseStep 1374363 = 2061545) B2061545
theorem B1374399 : Blo 1374006 1374399 := bstep (se 1 (by rfl) ⟨1030799, by rfl⟩ : syracuseStep 1374399 = 2061599) B2061599
theorem B1431743 : Blo 1374006 1431743 := bstep (se 1 (by rfl) ⟨1073807, by rfl⟩ : syracuseStep 1431743 = 2147615) B2147615
theorem B2062571 : Blo 1374006 2062571 := bstep (se 1 (by rfl) ⟨1546928, by rfl⟩ : syracuseStep 2062571 = 3093857) B3093857
theorem B3913991 : Blo 1374006 3913991 := bstep (se 1 (by rfl) ⟨2935493, by rfl⟩ : syracuseStep 3913991 = 5870987) B5870987
theorem B8927495 : Blo 1374006 8927495 := bstep (se 1 (by rfl) ⟨6695621, by rfl⟩ : syracuseStep 8927495 = 13391243) B13391243
theorem B2062631 : Blo 1374006 2062631 := bstep (se 1 (by rfl) ⟨1546973, by rfl⟩ : syracuseStep 2062631 = 3093947) B3093947
theorem B1374511 : Blo 1374006 1374511 := bstep (se 1 (by rfl) ⟨1030883, by rfl⟩ : syracuseStep 1374511 = 2061767) B2061767
theorem B2062715 : Blo 1374006 2062715 := bstep (se 1 (by rfl) ⟨1547036, by rfl⟩ : syracuseStep 2062715 = 3094073) B3094073
theorem B1374747 : Blo 1374006 1374747 := bstep (se 1 (by rfl) ⟨1031060, by rfl⟩ : syracuseStep 1374747 = 2062121) B2062121
theorem B1374751 : Blo 1374006 1374751 := bstep (se 1 (by rfl) ⟨1031063, by rfl⟩ : syracuseStep 1374751 = 2062127) B2062127
theorem B2062985 : Blo 1374006 2062985 := bstep (se 2 (by rfl) ⟨773619, by rfl⟩ : syracuseStep 2062985 = 1547239) B1547239
theorem B2063159 : Blo 1374006 2063159 := bstep (se 1 (by rfl) ⟨1547369, by rfl⟩ : syracuseStep 2063159 = 3094739) B3094739
theorem B1375067 : Blo 1374006 1375067 := bstep (se 1 (by rfl) ⟨1031300, by rfl⟩ : syracuseStep 1375067 = 2062601) B2062601
theorem B2063195 : Blo 1374006 2063195 := bstep (se 1 (by rfl) ⟨1547396, by rfl⟩ : syracuseStep 2063195 = 3094793) B3094793
theorem B3480479 : Blo 1374006 3480479 := bstep (se 1 (by rfl) ⟨2610359, by rfl⟩ : syracuseStep 3480479 = 5220719) B5220719
theorem B1375135 : Blo 1374006 1375135 := bstep (se 1 (by rfl) ⟨1031351, by rfl⟩ : syracuseStep 1375135 = 2062703) B2062703
theorem B1547167 : Blo 1374006 1547167 := bstep (se 1 (by rfl) ⟨1160375, by rfl⟩ : syracuseStep 1547167 = 2320751) B2320751
theorem B1375279 : Blo 1374006 1375279 := bstep (se 1 (by rfl) ⟨1031459, by rfl⟩ : syracuseStep 1375279 = 2062919) B2062919
theorem B1547311 : Blo 1374006 1547311 := bstep (se 1 (by rfl) ⟨1160483, by rfl⟩ : syracuseStep 1547311 = 2320967) B2320967
theorem B1375303 : Blo 1374006 1375303 := bstep (se 1 (by rfl) ⟨1031477, by rfl⟩ : syracuseStep 1375303 = 2062955) B2062955
theorem B1375455 : Blo 1374006 1375455 := bstep (se 1 (by rfl) ⟨1031591, by rfl⟩ : syracuseStep 1375455 = 2063183) B2063183
theorem B4406521 : Blo 1374006 4406521 := bstep (se 2 (by rfl) ⟨1652445, by rfl⟩ : syracuseStep 4406521 = 3304891) B3304891
theorem B19815677 : Blo 1374006 19815677 := bstep (se 3 (by rfl) ⟨3715439, by rfl⟩ : syracuseStep 19815677 = 7430879) B7430879
theorem B2202959 : Blo 1374006 2202959 := bstep (se 1 (by rfl) ⟨1652219, by rfl⟩ : syracuseStep 2202959 = 3304439) B3304439
theorem B4955503 : Blo 1374006 4955503 := bstep (se 1 (by rfl) ⟨3716627, by rfl⟩ : syracuseStep 4955503 = 7433255) B7433255
theorem B3915175 : Blo 1374006 3915175 := bstep (se 1 (by rfl) ⟨2936381, by rfl⟩ : syracuseStep 3915175 = 5872763) B5872763
theorem B67788251 : Blo 1374006 67788251 := bstep (se 1 (by rfl) ⟨50841188, by rfl⟩ : syracuseStep 67788251 = 101682377) B101682377
theorem B4701671 : Blo 1374006 4701671 := bstep (se 1 (by rfl) ⟨3526253, by rfl⟩ : syracuseStep 4701671 = 7052507) B7052507
theorem B3349991 : Blo 1374006 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B6962921 : Blo 1374006 6962921 := bstep (se 2 (by rfl) ⟨2611095, by rfl⟩ : syracuseStep 6962921 = 5222191) B5222191
theorem B3817981 : Blo 1374006 3817981 := bstep (se 3 (by rfl) ⟨715871, by rfl⟩ : syracuseStep 3817981 = 1431743) B1431743
theorem B5219063 : Blo 1374006 5219063 := bstep (se 1 (by rfl) ⟨3914297, by rfl⟩ : syracuseStep 5219063 = 7828595) B7828595
theorem B4637465 : Blo 1374006 4637465 := bstep (se 2 (by rfl) ⟨1739049, by rfl⟩ : syracuseStep 4637465 = 3478099) B3478099
theorem B4637735 : Blo 1374006 4637735 := bstep (se 1 (by rfl) ⟨3478301, by rfl⟩ : syracuseStep 4637735 = 6956603) B6956603
theorem B7054471 : Blo 1374006 7054471 := bstep (se 1 (by rfl) ⟨5290853, by rfl⟩ : syracuseStep 7054471 = 10581707) B10581707
theorem B5875361 : Blo 1374006 5875361 := bstep (se 2 (by rfl) ⟨2203260, by rfl⟩ : syracuseStep 5875361 = 4406521) B4406521
theorem B18810569 : Blo 1374006 18810569 := bstep (se 2 (by rfl) ⟨7053963, by rfl⟩ : syracuseStep 18810569 = 14107927) B14107927
theorem B3303305 : Blo 1374006 3303305 := bstep (se 2 (by rfl) ⟨1238739, by rfl⟩ : syracuseStep 3303305 = 2477479) B2477479
theorem B5220233 : Blo 1374006 5220233 := bstep (se 2 (by rfl) ⟨1957587, by rfl⟩ : syracuseStep 5220233 = 3915175) B3915175
theorem B2320319 : Blo 1374006 2320319 := bstep (se 1 (by rfl) ⟨1740239, by rfl⟩ : syracuseStep 2320319 = 3480479) B3480479
theorem B2934767 : Blo 1374006 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B101673053 : Blo 1374006 101673053 := bstep (se 3 (by rfl) ⟨19063697, by rfl⟩ : syracuseStep 101673053 = 38127395) B38127395
theorem B4638815 : Blo 1374006 4638815 := bstep (se 1 (by rfl) ⟨3479111, by rfl⟩ : syracuseStep 4638815 = 6958223) B6958223
theorem B1468639 : Blo 1374006 1468639 := bstep (se 1 (by rfl) ⟨1101479, by rfl⟩ : syracuseStep 1468639 = 2202959) B2202959
theorem B11749657 : Blo 1374006 11749657 := bstep (se 2 (by rfl) ⟨4406121, by rfl⟩ : syracuseStep 11749657 = 8812243) B8812243
theorem B2935399 : Blo 1374006 2935399 := bstep (se 1 (by rfl) ⟨2201549, by rfl⟩ : syracuseStep 2935399 = 4403099) B4403099
theorem B17615465 : Blo 1374006 17615465 := bstep (se 2 (by rfl) ⟨6605799, by rfl⟩ : syracuseStep 17615465 = 13211599) B13211599
theorem B2935433 : Blo 1374006 2935433 := bstep (se 2 (by rfl) ⟨1100787, by rfl⟩ : syracuseStep 2935433 = 2201575) B2201575
theorem B11741867 : Blo 1374006 11741867 := bstep (se 1 (by rfl) ⟨8806400, by rfl⟩ : syracuseStep 11741867 = 17612801) B17612801
theorem B7154639 : Blo 1374006 7154639 := bstep (se 1 (by rfl) ⟨5365979, by rfl⟩ : syracuseStep 7154639 = 10731959) B10731959
theorem B95251459 : Blo 1374006 95251459 := bstep (se 1 (by rfl) ⟨71438594, by rfl⟩ : syracuseStep 95251459 = 142877189) B142877189
theorem B3091625 : Blo 1374006 3091625 := bstep (se 2 (by rfl) ⟨1159359, by rfl⟩ : syracuseStep 3091625 = 2318719) B2318719
theorem B3092039 : Blo 1374006 3092039 := bstep (se 1 (by rfl) ⟨2319029, by rfl⟩ : syracuseStep 3092039 = 4638059) B4638059
theorem B3092111 : Blo 1374006 3092111 := bstep (se 1 (by rfl) ⟨2319083, by rfl⟩ : syracuseStep 3092111 = 4638167) B4638167
theorem B3092201 : Blo 1374006 3092201 := bstep (se 2 (by rfl) ⟨1159575, by rfl⟩ : syracuseStep 3092201 = 2319151) B2319151
theorem B3092219 : Blo 1374006 3092219 := bstep (se 1 (by rfl) ⟨2319164, by rfl⟩ : syracuseStep 3092219 = 4638329) B4638329
theorem B6606647 : Blo 1374006 6606647 := bstep (se 1 (by rfl) ⟨4954985, by rfl⟩ : syracuseStep 6606647 = 9909971) B9909971
theorem B2609023 : Blo 1374006 2609023 := bstep (se 1 (by rfl) ⟨1956767, by rfl⟩ : syracuseStep 2609023 = 3913535) B3913535
theorem B2609327 : Blo 1374006 2609327 := bstep (se 1 (by rfl) ⟨1956995, by rfl⟩ : syracuseStep 2609327 = 3913991) B3913991
theorem B5951663 : Blo 1374006 5951663 := bstep (se 1 (by rfl) ⟨4463747, by rfl⟩ : syracuseStep 5951663 = 8927495) B8927495
theorem B6959357 : Blo 1374006 6959357 := bstep (se 3 (by rfl) ⟨1304879, by rfl⟩ : syracuseStep 6959357 = 2609759) B2609759
theorem B4239635 : Blo 1374006 4239635 := bstep (se 1 (by rfl) ⟨3179726, by rfl⟩ : syracuseStep 4239635 = 6359453) B6359453
theorem B13218137 : Blo 1374006 13218137 := bstep (se 2 (by rfl) ⟨4956801, by rfl⟩ : syracuseStep 13218137 = 9913603) B9913603
theorem B6607337 : Blo 1374006 6607337 := bstep (se 2 (by rfl) ⟨2477751, by rfl⟩ : syracuseStep 6607337 = 4955503) B4955503
theorem B11907749 : Blo 1374006 11907749 := bstep (se 4 (by rfl) ⟨1116351, by rfl⟩ : syracuseStep 11907749 = 2232703) B2232703
theorem B3093227 : Blo 1374006 3093227 := bstep (se 1 (by rfl) ⟨2319920, by rfl⟩ : syracuseStep 3093227 = 4639841) B4639841
theorem B2061119 : Blo 1374006 2061119 := bstep (se 1 (by rfl) ⟨1545839, by rfl⟩ : syracuseStep 2061119 = 3091679) B3091679
theorem B13210451 : Blo 1374006 13210451 := bstep (se 1 (by rfl) ⟨9907838, by rfl⟩ : syracuseStep 13210451 = 19815677) B19815677
theorem B2061263 : Blo 1374006 2061263 := bstep (se 1 (by rfl) ⟨1545947, by rfl⟩ : syracuseStep 2061263 = 3091895) B3091895
theorem B45192167 : Blo 1374006 45192167 := bstep (se 1 (by rfl) ⟨33894125, by rfl⟩ : syracuseStep 45192167 = 67788251) B67788251
theorem B3134447 : Blo 1374006 3134447 := bstep (se 1 (by rfl) ⟨2350835, by rfl⟩ : syracuseStep 3134447 = 4701671) B4701671
theorem B2233327 : Blo 1374006 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B2061305 : Blo 1374006 2061305 := bstep (se 2 (by rfl) ⟨772989, by rfl⟩ : syracuseStep 2061305 = 1545979) B1545979
theorem B3093497 : Blo 1374006 3093497 := bstep (se 2 (by rfl) ⟨1160061, by rfl⟩ : syracuseStep 3093497 = 2320123) B2320123
theorem B6960167 : Blo 1374006 6960167 := bstep (se 1 (by rfl) ⟨5220125, by rfl⟩ : syracuseStep 6960167 = 10440251) B10440251
theorem B2061353 : Blo 1374006 2061353 := bstep (se 2 (by rfl) ⟨773007, by rfl⟩ : syracuseStep 2061353 = 1546015) B1546015
theorem B2061383 : Blo 1374006 2061383 := bstep (se 1 (by rfl) ⟨1546037, by rfl⟩ : syracuseStep 2061383 = 3092075) B3092075
theorem B3093587 : Blo 1374006 3093587 := bstep (se 1 (by rfl) ⟨2320190, by rfl⟩ : syracuseStep 3093587 = 4640381) B4640381
theorem B4641947 : Blo 1374006 4641947 := bstep (se 1 (by rfl) ⟨3481460, by rfl⟩ : syracuseStep 4641947 = 6962921) B6962921
theorem B2061563 : Blo 1374006 2061563 := bstep (se 1 (by rfl) ⟨1546172, by rfl⟩ : syracuseStep 2061563 = 3092345) B3092345
theorem B3093767 : Blo 1374006 3093767 := bstep (se 1 (by rfl) ⟨2320325, by rfl⟩ : syracuseStep 3093767 = 4640651) B4640651
theorem B17184125 : Blo 1374006 17184125 := bstep (se 3 (by rfl) ⟨3222023, by rfl⟩ : syracuseStep 17184125 = 6444047) B6444047
theorem B5576111 : Blo 1374006 5576111 := bstep (se 1 (by rfl) ⟨4182083, by rfl⟩ : syracuseStep 5576111 = 8364167) B8364167
theorem B6788551 : Blo 1374006 6788551 := bstep (se 1 (by rfl) ⟨5091413, by rfl⟩ : syracuseStep 6788551 = 10182827) B10182827
theorem B3094127 : Blo 1374006 3094127 := bstep (se 1 (by rfl) ⟨2320595, by rfl⟩ : syracuseStep 3094127 = 4641191) B4641191
theorem B5576435 : Blo 1374006 5576435 := bstep (se 1 (by rfl) ⟨4182326, by rfl⟩ : syracuseStep 5576435 = 8364653) B8364653
theorem B1374023 : Blo 1374006 1374023 := bstep (se 1 (by rfl) ⟨1030517, by rfl⟩ : syracuseStep 1374023 = 2061035) B2061035
theorem B1374043 : Blo 1374006 1374043 := bstep (se 1 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 1374043 = 2061065) B2061065
theorem B1374111 : Blo 1374006 1374111 := bstep (se 1 (by rfl) ⟨1030583, by rfl⟩ : syracuseStep 1374111 = 2061167) B2061167
theorem B1374279 : Blo 1374006 1374279 := bstep (se 1 (by rfl) ⟨1030709, by rfl⟩ : syracuseStep 1374279 = 2061419) B2061419
theorem B1374439 : Blo 1374006 1374439 := bstep (se 1 (by rfl) ⟨1030829, by rfl⟩ : syracuseStep 1374439 = 2061659) B2061659
theorem B4405661 : Blo 1374006 4405661 := bstep (se 3 (by rfl) ⟨826061, by rfl⟩ : syracuseStep 4405661 = 1652123) B1652123
theorem B1374623 : Blo 1374006 1374623 := bstep (se 1 (by rfl) ⟨1030967, by rfl⟩ : syracuseStep 1374623 = 2061935) B2061935
theorem B10443167 : Blo 1374006 10443167 := bstep (se 1 (by rfl) ⟨7832375, by rfl⟩ : syracuseStep 10443167 = 15664751) B15664751
theorem B3914183 : Blo 1374006 3914183 := bstep (se 1 (by rfl) ⟨2935637, by rfl⟩ : syracuseStep 3914183 = 5871275) B5871275
theorem B1374671 : Blo 1374006 1374671 := bstep (se 1 (by rfl) ⟨1031003, by rfl⟩ : syracuseStep 1374671 = 2062007) B2062007
theorem B2062799 : Blo 1374006 2062799 := bstep (se 1 (by rfl) ⟨1547099, by rfl⟩ : syracuseStep 2062799 = 3094199) B3094199
theorem B1374695 : Blo 1374006 1374695 := bstep (se 1 (by rfl) ⟨1031021, by rfl⟩ : syracuseStep 1374695 = 2062043) B2062043
theorem B2062889 : Blo 1374006 2062889 := bstep (se 2 (by rfl) ⟨773583, by rfl⟩ : syracuseStep 2062889 = 1547167) B1547167
theorem B1374811 : Blo 1374006 1374811 := bstep (se 1 (by rfl) ⟨1031108, by rfl⟩ : syracuseStep 1374811 = 2062217) B2062217
theorem B1546843 : Blo 1374006 1546843 := bstep (se 1 (by rfl) ⟨1160132, by rfl⟩ : syracuseStep 1546843 = 2320265) B2320265
theorem B3717775 : Blo 1374006 3717775 := bstep (se 1 (by rfl) ⟨2788331, by rfl⟩ : syracuseStep 3717775 = 5576663) B5576663
theorem B1374879 : Blo 1374006 1374879 := bstep (se 1 (by rfl) ⟨1031159, by rfl⟩ : syracuseStep 1374879 = 2062319) B2062319
theorem B2063081 : Blo 1374006 2063081 := bstep (se 2 (by rfl) ⟨773655, by rfl⟩ : syracuseStep 2063081 = 1547311) B1547311
theorem B1375047 : Blo 1374006 1375047 := bstep (se 1 (by rfl) ⟨1031285, by rfl⟩ : syracuseStep 1375047 = 2062571) B2062571
theorem B1375087 : Blo 1374006 1375087 := bstep (se 1 (by rfl) ⟨1031315, by rfl⟩ : syracuseStep 1375087 = 2062631) B2062631
theorem B1547131 : Blo 1374006 1547131 := bstep (se 1 (by rfl) ⟨1160348, by rfl⟩ : syracuseStep 1547131 = 2320697) B2320697
theorem B1375143 : Blo 1374006 1375143 := bstep (se 1 (by rfl) ⟨1031357, by rfl⟩ : syracuseStep 1375143 = 2062715) B2062715
theorem B52829171 : Blo 1374006 52829171 := bstep (se 1 (by rfl) ⟨39621878, by rfl⟩ : syracuseStep 52829171 = 79243757) B79243757
theorem B1375323 : Blo 1374006 1375323 := bstep (se 1 (by rfl) ⟨1031492, by rfl⟩ : syracuseStep 1375323 = 2062985) B2062985
theorem B1375439 : Blo 1374006 1375439 := bstep (se 1 (by rfl) ⟨1031579, by rfl⟩ : syracuseStep 1375439 = 2063159) B2063159
theorem B1375463 : Blo 1374006 1375463 := bstep (se 1 (by rfl) ⟨1031597, by rfl⟩ : syracuseStep 1375463 = 2063195) B2063195
theorem B18816857 : Blo 1374006 18816857 := bstep (se 2 (by rfl) ⟨7056321, by rfl⟩ : syracuseStep 18816857 = 14112643) B14112643
theorem B3915641 : Blo 1374006 3915641 := bstep (se 2 (by rfl) ⟨1468365, by rfl⟩ : syracuseStep 3915641 = 2936731) B2936731
theorem B1958185 : Blo 1374006 1958185 := bstep (se 2 (by rfl) ⟨734319, by rfl⟩ : syracuseStep 1958185 = 1468639) B1468639
theorem B7938499 : Blo 1374006 7938499 := bstep (se 1 (by rfl) ⟨5953874, by rfl⟩ : syracuseStep 7938499 = 11907749) B11907749
theorem B8806967 : Blo 1374006 8806967 := bstep (se 1 (by rfl) ⟨6605225, by rfl⟩ : syracuseStep 8806967 = 13210451) B13210451
theorem B2089631 : Blo 1374006 2089631 := bstep (se 1 (by rfl) ⟨1567223, by rfl⟩ : syracuseStep 2089631 = 3134447) B3134447
theorem B11305693 : Blo 1374006 11305693 := bstep (se 3 (by rfl) ⟨2119817, by rfl⟩ : syracuseStep 11305693 = 4239635) B4239635
theorem B4957033 : Blo 1374006 4957033 := bstep (se 2 (by rfl) ⟨1858887, by rfl⟩ : syracuseStep 4957033 = 3717775) B3717775
theorem B3916907 : Blo 1374006 3916907 := bstep (se 1 (by rfl) ⟨2937680, by rfl⟩ : syracuseStep 3916907 = 5875361) B5875361
theorem B10437821 : Blo 1374006 10437821 := bstep (se 3 (by rfl) ⟨1957091, by rfl⟩ : syracuseStep 10437821 = 3914183) B3914183
theorem B127001945 : Blo 1374006 127001945 := bstep (se 2 (by rfl) ⟨47625729, by rfl⟩ : syracuseStep 127001945 = 95251459) B95251459
theorem B67782035 : Blo 1374006 67782035 := bstep (se 1 (by rfl) ⟨50836526, by rfl⟩ : syracuseStep 67782035 = 101673053) B101673053
theorem B4769759 : Blo 1374006 4769759 := bstep (se 1 (by rfl) ⟨3577319, by rfl⟩ : syracuseStep 4769759 = 7154639) B7154639
theorem B35219447 : Blo 1374006 35219447 := bstep (se 1 (by rfl) ⟨26414585, by rfl⟩ : syracuseStep 35219447 = 52829171) B52829171
theorem B12544571 : Blo 1374006 12544571 := bstep (se 1 (by rfl) ⟨9408428, by rfl⟩ : syracuseStep 12544571 = 18816857) B18816857
theorem B1739551 : Blo 1374006 1739551 := bstep (se 1 (by rfl) ⟨1304663, by rfl⟩ : syracuseStep 1739551 = 2609327) B2609327
theorem B3967775 : Blo 1374006 3967775 := bstep (se 1 (by rfl) ⟨2975831, by rfl⟩ : syracuseStep 3967775 = 5951663) B5951663
theorem B4639571 : Blo 1374006 4639571 := bstep (se 1 (by rfl) ⟨3479678, by rfl⟩ : syracuseStep 4639571 = 6959357) B6959357
theorem B15666209 : Blo 1374006 15666209 := bstep (se 2 (by rfl) ⟨5874828, by rfl⟩ : syracuseStep 15666209 = 11749657) B11749657
theorem B3091643 : Blo 1374006 3091643 := bstep (se 1 (by rfl) ⟨2318732, by rfl⟩ : syracuseStep 3091643 = 4637465) B4637465
theorem B3091823 : Blo 1374006 3091823 := bstep (se 1 (by rfl) ⟨2318867, by rfl⟩ : syracuseStep 3091823 = 4637735) B4637735
theorem B4640111 : Blo 1374006 4640111 := bstep (se 1 (by rfl) ⟨3480083, by rfl⟩ : syracuseStep 4640111 = 6960167) B6960167
theorem B11456083 : Blo 1374006 11456083 := bstep (se 1 (by rfl) ⟨8592062, by rfl⟩ : syracuseStep 11456083 = 17184125) B17184125
theorem B2977769 : Blo 1374006 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B3092543 : Blo 1374006 3092543 := bstep (se 1 (by rfl) ⟨2319407, by rfl⟩ : syracuseStep 3092543 = 4638815) B4638815
theorem B2937107 : Blo 1374006 2937107 := bstep (se 1 (by rfl) ⟨2202830, by rfl⟩ : syracuseStep 2937107 = 4405661) B4405661
theorem B11743643 : Blo 1374006 11743643 := bstep (se 1 (by rfl) ⟨8807732, by rfl⟩ : syracuseStep 11743643 = 17615465) B17615465
theorem B7827911 : Blo 1374006 7827911 := bstep (se 1 (by rfl) ⟨5870933, by rfl⟩ : syracuseStep 7827911 = 11741867) B11741867
theorem B2061083 : Blo 1374006 2061083 := bstep (se 1 (by rfl) ⟨1545812, by rfl⟩ : syracuseStep 2061083 = 3091625) B3091625
theorem B10441709 : Blo 1374006 10441709 := bstep (se 3 (by rfl) ⟨1957820, by rfl⟩ : syracuseStep 10441709 = 3915641) B3915641
theorem B2061359 : Blo 1374006 2061359 := bstep (se 1 (by rfl) ⟨1546019, by rfl⟩ : syracuseStep 2061359 = 3092039) B3092039
theorem B2061407 : Blo 1374006 2061407 := bstep (se 1 (by rfl) ⟨1546055, by rfl⟩ : syracuseStep 2061407 = 3092111) B3092111
theorem B2061467 : Blo 1374006 2061467 := bstep (se 1 (by rfl) ⟨1546100, by rfl⟩ : syracuseStep 2061467 = 3092201) B3092201
theorem B2061479 : Blo 1374006 2061479 := bstep (se 1 (by rfl) ⟨1546109, by rfl⟩ : syracuseStep 2061479 = 3092219) B3092219
theorem B3478697 : Blo 1374006 3478697 := bstep (se 2 (by rfl) ⟨1304511, by rfl⟩ : syracuseStep 3478697 = 2609023) B2609023
theorem B4404431 : Blo 1374006 4404431 := bstep (se 1 (by rfl) ⟨3303323, by rfl⟩ : syracuseStep 4404431 = 6606647) B6606647
theorem B20362565 : Blo 1374006 20362565 := bstep (se 4 (by rfl) ⟨1908990, by rfl⟩ : syracuseStep 20362565 = 3817981) B3817981
theorem B8812091 : Blo 1374006 8812091 := bstep (se 1 (by rfl) ⟨6609068, by rfl⟩ : syracuseStep 8812091 = 13218137) B13218137
theorem B2062151 : Blo 1374006 2062151 := bstep (se 1 (by rfl) ⟨1546613, by rfl⟩ : syracuseStep 2062151 = 3093227) B3093227
theorem B3479375 : Blo 1374006 3479375 := bstep (se 1 (by rfl) ⟨2609531, by rfl⟩ : syracuseStep 3479375 = 5219063) B5219063
theorem B1374079 : Blo 1374006 1374079 := bstep (se 1 (by rfl) ⟨1030559, by rfl⟩ : syracuseStep 1374079 = 2061119) B2061119
theorem B1374175 : Blo 1374006 1374175 := bstep (se 1 (by rfl) ⟨1030631, by rfl⟩ : syracuseStep 1374175 = 2061263) B2061263
theorem B30128111 : Blo 1374006 30128111 := bstep (se 1 (by rfl) ⟨22596083, by rfl⟩ : syracuseStep 30128111 = 45192167) B45192167
theorem B1374203 : Blo 1374006 1374203 := bstep (se 1 (by rfl) ⟨1030652, by rfl⟩ : syracuseStep 1374203 = 2061305) B2061305
theorem B2062331 : Blo 1374006 2062331 := bstep (se 1 (by rfl) ⟨1546748, by rfl⟩ : syracuseStep 2062331 = 3093497) B3093497
theorem B1374235 : Blo 1374006 1374235 := bstep (se 1 (by rfl) ⟨1030676, by rfl⟩ : syracuseStep 1374235 = 2061353) B2061353
theorem B37623845 : Blo 1374006 37623845 := bstep (se 4 (by rfl) ⟨3527235, by rfl⟩ : syracuseStep 37623845 = 7054471) B7054471
theorem B1374255 : Blo 1374006 1374255 := bstep (se 1 (by rfl) ⟨1030691, by rfl⟩ : syracuseStep 1374255 = 2061383) B2061383
theorem B2062391 : Blo 1374006 2062391 := bstep (se 1 (by rfl) ⟨1546793, by rfl⟩ : syracuseStep 2062391 = 3093587) B3093587
theorem B3094631 : Blo 1374006 3094631 := bstep (se 1 (by rfl) ⟨2320973, by rfl⟩ : syracuseStep 3094631 = 4641947) B4641947
theorem B2062457 : Blo 1374006 2062457 := bstep (se 2 (by rfl) ⟨773421, by rfl⟩ : syracuseStep 2062457 = 1546843) B1546843
theorem B3913865 : Blo 1374006 3913865 := bstep (se 2 (by rfl) ⟨1467699, by rfl⟩ : syracuseStep 3913865 = 2935399) B2935399
theorem B1374375 : Blo 1374006 1374375 := bstep (se 1 (by rfl) ⟨1030781, by rfl⟩ : syracuseStep 1374375 = 2061563) B2061563
theorem B2062511 : Blo 1374006 2062511 := bstep (se 1 (by rfl) ⟨1546883, by rfl⟩ : syracuseStep 2062511 = 3093767) B3093767
theorem B3717407 : Blo 1374006 3717407 := bstep (se 1 (by rfl) ⟨2788055, by rfl⟩ : syracuseStep 3717407 = 5576111) B5576111
theorem B2062751 : Blo 1374006 2062751 := bstep (se 1 (by rfl) ⟨1547063, by rfl⟩ : syracuseStep 2062751 = 3094127) B3094127
theorem B12540379 : Blo 1374006 12540379 := bstep (se 1 (by rfl) ⟨9405284, by rfl⟩ : syracuseStep 12540379 = 18810569) B18810569
theorem B3717623 : Blo 1374006 3717623 := bstep (se 1 (by rfl) ⟨2788217, by rfl⟩ : syracuseStep 3717623 = 5576435) B5576435
theorem B2062841 : Blo 1374006 2062841 := bstep (se 2 (by rfl) ⟨773565, by rfl⟩ : syracuseStep 2062841 = 1547131) B1547131
theorem B2202203 : Blo 1374006 2202203 := bstep (se 1 (by rfl) ⟨1651652, by rfl⟩ : syracuseStep 2202203 = 3303305) B3303305
theorem B3480155 : Blo 1374006 3480155 := bstep (se 1 (by rfl) ⟨2610116, by rfl⟩ : syracuseStep 3480155 = 5220233) B5220233
theorem B17619565 : Blo 1374006 17619565 := bstep (se 3 (by rfl) ⟨3303668, by rfl⟩ : syracuseStep 17619565 = 6607337) B6607337
theorem B1546879 : Blo 1374006 1546879 := bstep (se 1 (by rfl) ⟨1160159, by rfl⟩ : syracuseStep 1546879 = 2320319) B2320319
theorem B1956511 : Blo 1374006 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B6962111 : Blo 1374006 6962111 := bstep (se 1 (by rfl) ⟨5221583, by rfl⟩ : syracuseStep 6962111 = 10443167) B10443167
theorem B1375199 : Blo 1374006 1375199 := bstep (se 1 (by rfl) ⟨1031399, by rfl⟩ : syracuseStep 1375199 = 2062799) B2062799
theorem B1375259 : Blo 1374006 1375259 := bstep (se 1 (by rfl) ⟨1031444, by rfl⟩ : syracuseStep 1375259 = 2062889) B2062889
theorem B1956955 : Blo 1374006 1956955 := bstep (se 1 (by rfl) ⟨1467716, by rfl⟩ : syracuseStep 1956955 = 2935433) B2935433
theorem B1375387 : Blo 1374006 1375387 := bstep (se 1 (by rfl) ⟨1031540, by rfl⟩ : syracuseStep 1375387 = 2063081) B2063081
theorem B9051401 : Blo 1374006 9051401 := bstep (se 2 (by rfl) ⟨3394275, by rfl⟩ : syracuseStep 9051401 = 6788551) B6788551
theorem B5218607 : Blo 1374006 5218607 := bstep (se 1 (by rfl) ⟨3913955, by rfl⟩ : syracuseStep 5218607 = 7827911) B7827911
theorem B1393087 : Blo 1374006 1393087 := bstep (se 1 (by rfl) ⟨1044815, by rfl⟩ : syracuseStep 1393087 = 2089631) B2089631
theorem B10584665 : Blo 1374006 10584665 := bstep (se 2 (by rfl) ⟨3969249, by rfl⟩ : syracuseStep 10584665 = 7938499) B7938499
theorem B16720505 : Blo 1374006 16720505 := bstep (se 2 (by rfl) ⟨6270189, by rfl⟩ : syracuseStep 16720505 = 12540379) B12540379
theorem B7832285 : Blo 1374006 7832285 := bstep (se 3 (by rfl) ⟨1468553, by rfl⟩ : syracuseStep 7832285 = 2937107) B2937107
theorem B2319131 : Blo 1374006 2319131 := bstep (se 1 (by rfl) ⟨1739348, by rfl⟩ : syracuseStep 2319131 = 3478697) B3478697
theorem B13575043 : Blo 1374006 13575043 := bstep (se 1 (by rfl) ⟨10181282, by rfl⟩ : syracuseStep 13575043 = 20362565) B20362565
theorem B45188023 : Blo 1374006 45188023 := bstep (se 1 (by rfl) ⟨33891017, by rfl⟩ : syracuseStep 45188023 = 67782035) B67782035
theorem B15074257 : Blo 1374006 15074257 := bstep (se 2 (by rfl) ⟨5652846, by rfl⟩ : syracuseStep 15074257 = 11305693) B11305693
theorem B5874727 : Blo 1374006 5874727 := bstep (se 1 (by rfl) ⟨4406045, by rfl⟩ : syracuseStep 5874727 = 8812091) B8812091
theorem B2319401 : Blo 1374006 2319401 := bstep (se 2 (by rfl) ⟨869775, by rfl⟩ : syracuseStep 2319401 = 1739551) B1739551
theorem B2319583 : Blo 1374006 2319583 := bstep (se 1 (by rfl) ⟨1739687, by rfl⟩ : syracuseStep 2319583 = 3479375) B3479375
theorem B9913661 : Blo 1374006 9913661 := bstep (se 3 (by rfl) ⟨1858811, by rfl⟩ : syracuseStep 9913661 = 3717623) B3717623
theorem B3179839 : Blo 1374006 3179839 := bstep (se 1 (by rfl) ⟨2384879, by rfl⟩ : syracuseStep 3179839 = 4769759) B4769759
theorem B23479631 : Blo 1374006 23479631 := bstep (se 1 (by rfl) ⟨17609723, by rfl⟩ : syracuseStep 23479631 = 35219447) B35219447
theorem B1468135 : Blo 1374006 1468135 := bstep (se 1 (by rfl) ⟨1101101, by rfl⟩ : syracuseStep 1468135 = 2202203) B2202203
theorem B2320103 : Blo 1374006 2320103 := bstep (se 1 (by rfl) ⟨1740077, by rfl⟩ : syracuseStep 2320103 = 3480155) B3480155
theorem B7940717 : Blo 1374006 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B61099109 : Blo 1374006 61099109 := bstep (se 4 (by rfl) ⟨5728041, by rfl⟩ : syracuseStep 61099109 = 11456083) B11456083
theorem B6958547 : Blo 1374006 6958547 := bstep (se 1 (by rfl) ⟨5218910, by rfl⟩ : syracuseStep 6958547 = 10437821) B10437821
theorem B2936287 : Blo 1374006 2936287 := bstep (se 1 (by rfl) ⟨2202215, by rfl⟩ : syracuseStep 2936287 = 4404431) B4404431
theorem B2608681 : Blo 1374006 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B84667963 : Blo 1374006 84667963 := bstep (se 1 (by rfl) ⟨63500972, by rfl⟩ : syracuseStep 84667963 = 127001945) B127001945
theorem B2609243 : Blo 1374006 2609243 := bstep (se 1 (by rfl) ⟨1956932, by rfl⟩ : syracuseStep 2609243 = 3913865) B3913865
theorem B2609273 : Blo 1374006 2609273 := bstep (se 2 (by rfl) ⟨978477, by rfl⟩ : syracuseStep 2609273 = 1956955) B1956955
theorem B2478271 : Blo 1374006 2478271 := bstep (se 1 (by rfl) ⟨1858703, by rfl⟩ : syracuseStep 2478271 = 3717407) B3717407
theorem B3093047 : Blo 1374006 3093047 := bstep (se 1 (by rfl) ⟨2319785, by rfl⟩ : syracuseStep 3093047 = 4639571) B4639571
theorem B4641407 : Blo 1374006 4641407 := bstep (se 1 (by rfl) ⟨3481055, by rfl⟩ : syracuseStep 4641407 = 6962111) B6962111
theorem B2061095 : Blo 1374006 2061095 := bstep (se 1 (by rfl) ⟨1545821, by rfl⟩ : syracuseStep 2061095 = 3091643) B3091643
theorem B6034267 : Blo 1374006 6034267 := bstep (se 1 (by rfl) ⟨4525700, by rfl⟩ : syracuseStep 6034267 = 9051401) B9051401
theorem B2061215 : Blo 1374006 2061215 := bstep (se 1 (by rfl) ⟨1545911, by rfl⟩ : syracuseStep 2061215 = 3091823) B3091823
theorem B3093407 : Blo 1374006 3093407 := bstep (se 1 (by rfl) ⟨2320055, by rfl⟩ : syracuseStep 3093407 = 4640111) B4640111
theorem B2061695 : Blo 1374006 2061695 := bstep (se 1 (by rfl) ⟨1546271, by rfl⟩ : syracuseStep 2061695 = 3092543) B3092543
theorem B7829095 : Blo 1374006 7829095 := bstep (se 1 (by rfl) ⟨5871821, by rfl⟩ : syracuseStep 7829095 = 11743643) B11743643
theorem B5871311 : Blo 1374006 5871311 := bstep (se 1 (by rfl) ⟨4403483, by rfl⟩ : syracuseStep 5871311 = 8806967) B8806967
theorem B1374055 : Blo 1374006 1374055 := bstep (se 1 (by rfl) ⟨1030541, by rfl⟩ : syracuseStep 1374055 = 2061083) B2061083
theorem B6961139 : Blo 1374006 6961139 := bstep (se 1 (by rfl) ⟨5220854, by rfl⟩ : syracuseStep 6961139 = 10441709) B10441709
theorem B1374239 : Blo 1374006 1374239 := bstep (se 1 (by rfl) ⟨1030679, by rfl⟩ : syracuseStep 1374239 = 2061359) B2061359
theorem B1374271 : Blo 1374006 1374271 := bstep (se 1 (by rfl) ⟨1030703, by rfl⟩ : syracuseStep 1374271 = 2061407) B2061407
theorem B2611271 : Blo 1374006 2611271 := bstep (se 1 (by rfl) ⟨1958453, by rfl⟩ : syracuseStep 2611271 = 3916907) B3916907
theorem B1374311 : Blo 1374006 1374311 := bstep (se 1 (by rfl) ⟨1030733, by rfl⟩ : syracuseStep 1374311 = 2061467) B2061467
theorem B1374319 : Blo 1374006 1374319 := bstep (se 1 (by rfl) ⟨1030739, by rfl⟩ : syracuseStep 1374319 = 2061479) B2061479
theorem B23492753 : Blo 1374006 23492753 := bstep (se 2 (by rfl) ⟨8809782, by rfl⟩ : syracuseStep 23492753 = 17619565) B17619565
theorem B2062505 : Blo 1374006 2062505 := bstep (se 2 (by rfl) ⟨773439, by rfl⟩ : syracuseStep 2062505 = 1546879) B1546879
theorem B6609377 : Blo 1374006 6609377 := bstep (se 2 (by rfl) ⟨2478516, by rfl⟩ : syracuseStep 6609377 = 4957033) B4957033
theorem B1374767 : Blo 1374006 1374767 := bstep (se 1 (by rfl) ⟨1031075, by rfl⟩ : syracuseStep 1374767 = 2062151) B2062151
theorem B20085407 : Blo 1374006 20085407 := bstep (se 1 (by rfl) ⟨15064055, by rfl⟩ : syracuseStep 20085407 = 30128111) B30128111
theorem B1374887 : Blo 1374006 1374887 := bstep (se 1 (by rfl) ⟨1031165, by rfl⟩ : syracuseStep 1374887 = 2062331) B2062331
theorem B25082563 : Blo 1374006 25082563 := bstep (se 1 (by rfl) ⟨18811922, by rfl⟩ : syracuseStep 25082563 = 37623845) B37623845
theorem B1374927 : Blo 1374006 1374927 := bstep (se 1 (by rfl) ⟨1031195, by rfl⟩ : syracuseStep 1374927 = 2062391) B2062391
theorem B2063087 : Blo 1374006 2063087 := bstep (se 1 (by rfl) ⟨1547315, by rfl⟩ : syracuseStep 2063087 = 3094631) B3094631
theorem B1374971 : Blo 1374006 1374971 := bstep (se 1 (by rfl) ⟨1031228, by rfl⟩ : syracuseStep 1374971 = 2062457) B2062457
theorem B1375007 : Blo 1374006 1375007 := bstep (se 1 (by rfl) ⟨1031255, by rfl⟩ : syracuseStep 1375007 = 2062511) B2062511
theorem B10443653 : Blo 1374006 10443653 := bstep (se 4 (by rfl) ⟨979092, by rfl⟩ : syracuseStep 10443653 = 1958185) B1958185
theorem B1375167 : Blo 1374006 1375167 := bstep (se 1 (by rfl) ⟨1031375, by rfl⟩ : syracuseStep 1375167 = 2062751) B2062751
theorem B1375227 : Blo 1374006 1375227 := bstep (se 1 (by rfl) ⟨1031420, by rfl⟩ : syracuseStep 1375227 = 2062841) B2062841
theorem B8363047 : Blo 1374006 8363047 := bstep (se 1 (by rfl) ⟨6272285, by rfl⟩ : syracuseStep 8363047 = 12544571) B12544571
theorem B2645183 : Blo 1374006 2645183 := bstep (se 1 (by rfl) ⟨1983887, by rfl⟩ : syracuseStep 2645183 = 3967775) B3967775
theorem B10444139 : Blo 1374006 10444139 := bstep (se 1 (by rfl) ⟨7833104, by rfl⟩ : syracuseStep 10444139 = 15666209) B15666209
theorem B8045689 : Blo 1374006 8045689 := bstep (se 2 (by rfl) ⟨3017133, by rfl⟩ : syracuseStep 8045689 = 6034267) B6034267
theorem B11150729 : Blo 1374006 11150729 := bstep (se 2 (by rfl) ⟨4181523, by rfl⟩ : syracuseStep 11150729 = 8363047) B8363047
theorem B7832969 : Blo 1374006 7832969 := bstep (se 2 (by rfl) ⟨2937363, by rfl⟩ : syracuseStep 7832969 = 5874727) B5874727
theorem B5293811 : Blo 1374006 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B40732739 : Blo 1374006 40732739 := bstep (se 1 (by rfl) ⟨30549554, by rfl⟩ : syracuseStep 40732739 = 61099109) B61099109
theorem B1763455 : Blo 1374006 1763455 := bstep (se 1 (by rfl) ⟨1322591, by rfl⟩ : syracuseStep 1763455 = 2645183) B2645183
theorem B10438793 : Blo 1374006 10438793 := bstep (se 2 (by rfl) ⟨3914547, by rfl⟩ : syracuseStep 10438793 = 7829095) B7829095
theorem B4639031 : Blo 1374006 4639031 := bstep (se 1 (by rfl) ⟨3479273, by rfl⟩ : syracuseStep 4639031 = 6958547) B6958547
theorem B1739495 : Blo 1374006 1739495 := bstep (se 1 (by rfl) ⟨1304621, by rfl⟩ : syracuseStep 1739495 = 2609243) B2609243
theorem B3304361 : Blo 1374006 3304361 := bstep (se 2 (by rfl) ⟨1239135, by rfl⟩ : syracuseStep 3304361 = 2478271) B2478271
theorem B6958061 : Blo 1374006 6958061 := bstep (se 3 (by rfl) ⟨1304636, by rfl⟩ : syracuseStep 6958061 = 2609273) B2609273
theorem B7056443 : Blo 1374006 7056443 := bstep (se 1 (by rfl) ⟨5292332, by rfl⟩ : syracuseStep 7056443 = 10584665) B10584665
theorem B5221523 : Blo 1374006 5221523 := bstep (se 1 (by rfl) ⟨3916142, by rfl⟩ : syracuseStep 5221523 = 7832285) B7832285
theorem B33443417 : Blo 1374006 33443417 := bstep (se 2 (by rfl) ⟨12541281, by rfl⟩ : syracuseStep 33443417 = 25082563) B25082563
theorem B18100057 : Blo 1374006 18100057 := bstep (se 2 (by rfl) ⟨6787521, by rfl⟩ : syracuseStep 18100057 = 13575043) B13575043
theorem B20099009 : Blo 1374006 20099009 := bstep (se 2 (by rfl) ⟨7537128, by rfl⟩ : syracuseStep 20099009 = 15074257) B15074257
theorem B4640759 : Blo 1374006 4640759 := bstep (se 1 (by rfl) ⟨3480569, by rfl⟩ : syracuseStep 4640759 = 6961139) B6961139
theorem B1740847 : Blo 1374006 1740847 := bstep (se 1 (by rfl) ⟨1305635, by rfl⟩ : syracuseStep 1740847 = 2611271) B2611271
theorem B3092777 : Blo 1374006 3092777 := bstep (se 2 (by rfl) ⟨1159791, by rfl⟩ : syracuseStep 3092777 = 2319583) B2319583
theorem B4239785 : Blo 1374006 4239785 := bstep (se 2 (by rfl) ⟨1589919, by rfl⟩ : syracuseStep 4239785 = 3179839) B3179839
theorem B13390271 : Blo 1374006 13390271 := bstep (se 1 (by rfl) ⟨10042703, by rfl⟩ : syracuseStep 13390271 = 20085407) B20085407
theorem B3478241 : Blo 1374006 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B112890617 : Blo 1374006 112890617 := bstep (se 2 (by rfl) ⟨42333981, by rfl⟩ : syracuseStep 112890617 = 84667963) B84667963
theorem B3479071 : Blo 1374006 3479071 := bstep (se 1 (by rfl) ⟨2609303, by rfl⟩ : syracuseStep 3479071 = 5218607) B5218607
theorem B2062031 : Blo 1374006 2062031 := bstep (se 1 (by rfl) ⟨1546523, by rfl⟩ : syracuseStep 2062031 = 3093047) B3093047
theorem B11147003 : Blo 1374006 11147003 := bstep (se 1 (by rfl) ⟨8360252, by rfl⟩ : syracuseStep 11147003 = 16720505) B16720505
theorem B3094271 : Blo 1374006 3094271 := bstep (se 1 (by rfl) ⟨2320703, by rfl⟩ : syracuseStep 3094271 = 4641407) B4641407
theorem B1546087 : Blo 1374006 1546087 := bstep (se 1 (by rfl) ⟨1159565, by rfl⟩ : syracuseStep 1546087 = 2319131) B2319131
theorem B1374063 : Blo 1374006 1374063 := bstep (se 1 (by rfl) ⟨1030547, by rfl⟩ : syracuseStep 1374063 = 2061095) B2061095
theorem B1857449 : Blo 1374006 1857449 := bstep (se 2 (by rfl) ⟨696543, by rfl⟩ : syracuseStep 1857449 = 1393087) B1393087
theorem B1374143 : Blo 1374006 1374143 := bstep (se 1 (by rfl) ⟨1030607, by rfl⟩ : syracuseStep 1374143 = 2061215) B2061215
theorem B2062271 : Blo 1374006 2062271 := bstep (se 1 (by rfl) ⟨1546703, by rfl⟩ : syracuseStep 2062271 = 3093407) B3093407
theorem B1546267 : Blo 1374006 1546267 := bstep (se 1 (by rfl) ⟨1159700, by rfl⟩ : syracuseStep 1546267 = 2319401) B2319401
theorem B6609107 : Blo 1374006 6609107 := bstep (se 1 (by rfl) ⟨4956830, by rfl⟩ : syracuseStep 6609107 = 9913661) B9913661
theorem B15653087 : Blo 1374006 15653087 := bstep (se 1 (by rfl) ⟨11739815, by rfl⟩ : syracuseStep 15653087 = 23479631) B23479631
theorem B1374463 : Blo 1374006 1374463 := bstep (se 1 (by rfl) ⟨1030847, by rfl⟩ : syracuseStep 1374463 = 2061695) B2061695
theorem B3914207 : Blo 1374006 3914207 := bstep (se 1 (by rfl) ⟨2935655, by rfl⟩ : syracuseStep 3914207 = 5871311) B5871311
theorem B1546735 : Blo 1374006 1546735 := bstep (se 1 (by rfl) ⟨1160051, by rfl⟩ : syracuseStep 1546735 = 2320103) B2320103
theorem B7830053 : Blo 1374006 7830053 := bstep (se 4 (by rfl) ⟨734067, by rfl⟩ : syracuseStep 7830053 = 1468135) B1468135
theorem B60250697 : Blo 1374006 60250697 := bstep (se 2 (by rfl) ⟨22594011, by rfl⟩ : syracuseStep 60250697 = 45188023) B45188023
theorem B15661835 : Blo 1374006 15661835 := bstep (se 1 (by rfl) ⟨11746376, by rfl⟩ : syracuseStep 15661835 = 23492753) B23492753
theorem B1375003 : Blo 1374006 1375003 := bstep (se 1 (by rfl) ⟨1031252, by rfl⟩ : syracuseStep 1375003 = 2062505) B2062505
theorem B4406251 : Blo 1374006 4406251 := bstep (se 1 (by rfl) ⟨3304688, by rfl⟩ : syracuseStep 4406251 = 6609377) B6609377
theorem B1375391 : Blo 1374006 1375391 := bstep (se 1 (by rfl) ⟨1031543, by rfl⟩ : syracuseStep 1375391 = 2063087) B2063087
theorem B6962435 : Blo 1374006 6962435 := bstep (se 1 (by rfl) ⟨5221826, by rfl⟩ : syracuseStep 6962435 = 10443653) B10443653
theorem B3915049 : Blo 1374006 3915049 := bstep (se 2 (by rfl) ⟨1468143, by rfl⟩ : syracuseStep 3915049 = 2936287) B2936287
theorem B6962759 : Blo 1374006 6962759 := bstep (se 1 (by rfl) ⟨5222069, by rfl⟩ : syracuseStep 6962759 = 10444139) B10444139
theorem B18817181 : Blo 1374006 18817181 := bstep (se 3 (by rfl) ⟨3528221, by rfl⟩ : syracuseStep 18817181 = 7056443) B7056443
theorem B2351273 : Blo 1374006 2351273 := bstep (se 2 (by rfl) ⟨881727, by rfl⟩ : syracuseStep 2351273 = 1763455) B1763455
theorem B2826523 : Blo 1374006 2826523 := bstep (se 1 (by rfl) ⟨2119892, by rfl⟩ : syracuseStep 2826523 = 4239785) B4239785
theorem B2318827 : Blo 1374006 2318827 := bstep (se 1 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 2318827 = 3478241) B3478241
theorem B75260411 : Blo 1374006 75260411 := bstep (se 1 (by rfl) ⟨56445308, by rfl⟩ : syracuseStep 75260411 = 112890617) B112890617
theorem B7431335 : Blo 1374006 7431335 := bstep (se 1 (by rfl) ⟨5573501, by rfl⟩ : syracuseStep 7431335 = 11147003) B11147003
theorem B5875001 : Blo 1374006 5875001 := bstep (se 2 (by rfl) ⟨2203125, by rfl⟩ : syracuseStep 5875001 = 4406251) B4406251
theorem B5220035 : Blo 1374006 5220035 := bstep (se 1 (by rfl) ⟨3915026, by rfl⟩ : syracuseStep 5220035 = 7830053) B7830053
theorem B40167131 : Blo 1374006 40167131 := bstep (se 1 (by rfl) ⟨30125348, by rfl⟩ : syracuseStep 40167131 = 60250697) B60250697
theorem B5220065 : Blo 1374006 5220065 := bstep (se 2 (by rfl) ⟨1957524, by rfl⟩ : syracuseStep 5220065 = 3915049) B3915049
theorem B4638653 : Blo 1374006 4638653 := bstep (se 3 (by rfl) ⟨869747, by rfl⟩ : syracuseStep 4638653 = 1739495) B1739495
theorem B4638707 : Blo 1374006 4638707 := bstep (se 1 (by rfl) ⟨3479030, by rfl⟩ : syracuseStep 4638707 = 6958061) B6958061
theorem B4638761 : Blo 1374006 4638761 := bstep (se 2 (by rfl) ⟨1739535, by rfl⟩ : syracuseStep 4638761 = 3479071) B3479071
theorem B2321129 : Blo 1374006 2321129 := bstep (se 2 (by rfl) ⟨870423, by rfl⟩ : syracuseStep 2321129 = 1740847) B1740847
theorem B7433819 : Blo 1374006 7433819 := bstep (se 1 (by rfl) ⟨5575364, by rfl⟩ : syracuseStep 7433819 = 11150729) B11150729
theorem B5221979 : Blo 1374006 5221979 := bstep (se 1 (by rfl) ⟨3916484, by rfl⟩ : syracuseStep 5221979 = 7832969) B7832969
theorem B6959195 : Blo 1374006 6959195 := bstep (se 1 (by rfl) ⟨5219396, by rfl⟩ : syracuseStep 6959195 = 10438793) B10438793
theorem B10727585 : Blo 1374006 10727585 := bstep (se 2 (by rfl) ⟨4022844, by rfl⟩ : syracuseStep 10727585 = 8045689) B8045689
theorem B3092687 : Blo 1374006 3092687 := bstep (se 1 (by rfl) ⟨2319515, by rfl⟩ : syracuseStep 3092687 = 4639031) B4639031
theorem B2609471 : Blo 1374006 2609471 := bstep (se 1 (by rfl) ⟨1957103, by rfl⟩ : syracuseStep 2609471 = 3914207) B3914207
theorem B10441223 : Blo 1374006 10441223 := bstep (se 1 (by rfl) ⟨7830917, by rfl⟩ : syracuseStep 10441223 = 15661835) B15661835
theorem B4641623 : Blo 1374006 4641623 := bstep (se 1 (by rfl) ⟨3481217, by rfl⟩ : syracuseStep 4641623 = 6962435) B6962435
theorem B4641839 : Blo 1374006 4641839 := bstep (se 1 (by rfl) ⟨3481379, by rfl⟩ : syracuseStep 4641839 = 6962759) B6962759
theorem B22295611 : Blo 1374006 22295611 := bstep (se 1 (by rfl) ⟨16721708, by rfl⟩ : syracuseStep 22295611 = 33443417) B33443417
theorem B4953197 : Blo 1374006 4953197 := bstep (se 3 (by rfl) ⟨928724, by rfl⟩ : syracuseStep 4953197 = 1857449) B1857449
theorem B8811629 : Blo 1374006 8811629 := bstep (se 3 (by rfl) ⟨1652180, by rfl⟩ : syracuseStep 8811629 = 3304361) B3304361
theorem B2061449 : Blo 1374006 2061449 := bstep (se 2 (by rfl) ⟨773043, by rfl⟩ : syracuseStep 2061449 = 1546087) B1546087
theorem B13399339 : Blo 1374006 13399339 := bstep (se 1 (by rfl) ⟨10049504, by rfl⟩ : syracuseStep 13399339 = 20099009) B20099009
theorem B3093839 : Blo 1374006 3093839 := bstep (se 1 (by rfl) ⟨2320379, by rfl⟩ : syracuseStep 3093839 = 4640759) B4640759
theorem B2061689 : Blo 1374006 2061689 := bstep (se 2 (by rfl) ⟨773133, by rfl⟩ : syracuseStep 2061689 = 1546267) B1546267
theorem B2061851 : Blo 1374006 2061851 := bstep (se 1 (by rfl) ⟨1546388, by rfl⟩ : syracuseStep 2061851 = 3092777) B3092777
theorem B8926847 : Blo 1374006 8926847 := bstep (se 1 (by rfl) ⟨6695135, by rfl⟩ : syracuseStep 8926847 = 13390271) B13390271
theorem B2062313 : Blo 1374006 2062313 := bstep (se 2 (by rfl) ⟨773367, by rfl⟩ : syracuseStep 2062313 = 1546735) B1546735
theorem B1374687 : Blo 1374006 1374687 := bstep (se 1 (by rfl) ⟨1031015, by rfl⟩ : syracuseStep 1374687 = 2062031) B2062031
theorem B3529207 : Blo 1374006 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B2062847 : Blo 1374006 2062847 := bstep (se 1 (by rfl) ⟨1547135, by rfl⟩ : syracuseStep 2062847 = 3094271) B3094271
theorem B1374847 : Blo 1374006 1374847 := bstep (se 1 (by rfl) ⟨1031135, by rfl⟩ : syracuseStep 1374847 = 2062271) B2062271
theorem B27155159 : Blo 1374006 27155159 := bstep (se 1 (by rfl) ⟨20366369, by rfl⟩ : syracuseStep 27155159 = 40732739) B40732739
theorem B4406071 : Blo 1374006 4406071 := bstep (se 1 (by rfl) ⟨3304553, by rfl⟩ : syracuseStep 4406071 = 6609107) B6609107
theorem B10435391 : Blo 1374006 10435391 := bstep (se 1 (by rfl) ⟨7826543, by rfl⟩ : syracuseStep 10435391 = 15653087) B15653087
theorem B3481015 : Blo 1374006 3481015 := bstep (se 1 (by rfl) ⟨2610761, by rfl⟩ : syracuseStep 3481015 = 5221523) B5221523
theorem B24133409 : Blo 1374006 24133409 := bstep (se 2 (by rfl) ⟨9050028, by rfl⟩ : syracuseStep 24133409 = 18100057) B18100057
theorem B7151723 : Blo 1374006 7151723 := bstep (se 1 (by rfl) ⟨5363792, by rfl⟩ : syracuseStep 7151723 = 10727585) B10727585
theorem B3768697 : Blo 1374006 3768697 := bstep (se 2 (by rfl) ⟨1413261, by rfl⟩ : syracuseStep 3768697 = 2826523) B2826523
theorem B3302131 : Blo 1374006 3302131 := bstep (se 1 (by rfl) ⟨2476598, by rfl⟩ : syracuseStep 3302131 = 4953197) B4953197
theorem B5874419 : Blo 1374006 5874419 := bstep (se 1 (by rfl) ⟨4405814, by rfl⟩ : syracuseStep 5874419 = 8811629) B8811629
theorem B3916667 : Blo 1374006 3916667 := bstep (se 1 (by rfl) ⟨2937500, by rfl⟩ : syracuseStep 3916667 = 5875001) B5875001
theorem B5874761 : Blo 1374006 5874761 := bstep (se 2 (by rfl) ⟨2203035, by rfl⟩ : syracuseStep 5874761 = 4406071) B4406071
theorem B6956927 : Blo 1374006 6956927 := bstep (se 1 (by rfl) ⟨5217695, by rfl⟩ : syracuseStep 6956927 = 10435391) B10435391
theorem B107112349 : Blo 1374006 107112349 := bstep (se 3 (by rfl) ⟨20083565, by rfl⟩ : syracuseStep 107112349 = 40167131) B40167131
theorem B4639463 : Blo 1374006 4639463 := bstep (se 1 (by rfl) ⟨3479597, by rfl⟩ : syracuseStep 4639463 = 6959195) B6959195
theorem B12544787 : Blo 1374006 12544787 := bstep (se 1 (by rfl) ⟨9408590, by rfl⟩ : syracuseStep 12544787 = 18817181) B18817181
theorem B1739647 : Blo 1374006 1739647 := bstep (se 1 (by rfl) ⟨1304735, by rfl⟩ : syracuseStep 1739647 = 2609471) B2609471
theorem B6270061 : Blo 1374006 6270061 := bstep (se 3 (by rfl) ⟨1175636, by rfl⟩ : syracuseStep 6270061 = 2351273) B2351273
theorem B3091769 : Blo 1374006 3091769 := bstep (se 2 (by rfl) ⟨1159413, by rfl⟩ : syracuseStep 3091769 = 2318827) B2318827
theorem B4705609 : Blo 1374006 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B5951231 : Blo 1374006 5951231 := bstep (se 1 (by rfl) ⟨4463423, by rfl⟩ : syracuseStep 5951231 = 8926847) B8926847
theorem B3092435 : Blo 1374006 3092435 := bstep (se 1 (by rfl) ⟨2319326, by rfl⟩ : syracuseStep 3092435 = 4638653) B4638653
theorem B3092471 : Blo 1374006 3092471 := bstep (se 1 (by rfl) ⟨2319353, by rfl⟩ : syracuseStep 3092471 = 4638707) B4638707
theorem B3092507 : Blo 1374006 3092507 := bstep (se 1 (by rfl) ⟨2319380, by rfl⟩ : syracuseStep 3092507 = 4638761) B4638761
theorem B4641353 : Blo 1374006 4641353 := bstep (se 2 (by rfl) ⟨1740507, by rfl⟩ : syracuseStep 4641353 = 3481015) B3481015
theorem B2061791 : Blo 1374006 2061791 := bstep (se 1 (by rfl) ⟨1546343, by rfl⟩ : syracuseStep 2061791 = 3092687) B3092687
theorem B50173607 : Blo 1374006 50173607 := bstep (se 1 (by rfl) ⟨37630205, by rfl⟩ : syracuseStep 50173607 = 75260411) B75260411
theorem B6960815 : Blo 1374006 6960815 := bstep (se 1 (by rfl) ⟨5220611, by rfl⟩ : syracuseStep 6960815 = 10441223) B10441223
theorem B3094415 : Blo 1374006 3094415 := bstep (se 1 (by rfl) ⟨2320811, by rfl⟩ : syracuseStep 3094415 = 4641623) B4641623
theorem B3094559 : Blo 1374006 3094559 := bstep (se 1 (by rfl) ⟨2320919, by rfl⟩ : syracuseStep 3094559 = 4641839) B4641839
theorem B1374299 : Blo 1374006 1374299 := bstep (se 1 (by rfl) ⟨1030724, by rfl⟩ : syracuseStep 1374299 = 2061449) B2061449
theorem B4954223 : Blo 1374006 4954223 := bstep (se 1 (by rfl) ⟨3715667, by rfl⟩ : syracuseStep 4954223 = 7431335) B7431335
theorem B2062559 : Blo 1374006 2062559 := bstep (se 1 (by rfl) ⟨1546919, by rfl⟩ : syracuseStep 2062559 = 3093839) B3093839
theorem B1374459 : Blo 1374006 1374459 := bstep (se 1 (by rfl) ⟨1030844, by rfl⟩ : syracuseStep 1374459 = 2061689) B2061689
theorem B1374567 : Blo 1374006 1374567 := bstep (se 1 (by rfl) ⟨1030925, by rfl⟩ : syracuseStep 1374567 = 2061851) B2061851
theorem B3480023 : Blo 1374006 3480023 := bstep (se 1 (by rfl) ⟨2610017, by rfl⟩ : syracuseStep 3480023 = 5220035) B5220035
theorem B3480043 : Blo 1374006 3480043 := bstep (se 1 (by rfl) ⟨2610032, by rfl⟩ : syracuseStep 3480043 = 5220065) B5220065
theorem B1374875 : Blo 1374006 1374875 := bstep (se 1 (by rfl) ⟨1031156, by rfl⟩ : syracuseStep 1374875 = 2062313) B2062313
theorem B29727481 : Blo 1374006 29727481 := bstep (se 2 (by rfl) ⟨11147805, by rfl⟩ : syracuseStep 29727481 = 22295611) B22295611
theorem B1375231 : Blo 1374006 1375231 := bstep (se 1 (by rfl) ⟨1031423, by rfl⟩ : syracuseStep 1375231 = 2062847) B2062847
theorem B17865785 : Blo 1374006 17865785 := bstep (se 2 (by rfl) ⟨6699669, by rfl⟩ : syracuseStep 17865785 = 13399339) B13399339
theorem B18103439 : Blo 1374006 18103439 := bstep (se 1 (by rfl) ⟨13577579, by rfl⟩ : syracuseStep 18103439 = 27155159) B27155159
theorem B1547419 : Blo 1374006 1547419 := bstep (se 1 (by rfl) ⟨1160564, by rfl⟩ : syracuseStep 1547419 = 2321129) B2321129
theorem B4955879 : Blo 1374006 4955879 := bstep (se 1 (by rfl) ⟨3716909, by rfl⟩ : syracuseStep 4955879 = 7433819) B7433819
theorem B3481319 : Blo 1374006 3481319 := bstep (se 1 (by rfl) ⟨2610989, by rfl⟩ : syracuseStep 3481319 = 5221979) B5221979
theorem B16088939 : Blo 1374006 16088939 := bstep (se 1 (by rfl) ⟨12066704, by rfl⟩ : syracuseStep 16088939 = 24133409) B24133409
theorem B4767815 : Blo 1374006 4767815 := bstep (se 1 (by rfl) ⟨3575861, by rfl⟩ : syracuseStep 4767815 = 7151723) B7151723
theorem B48275837 : Blo 1374006 48275837 := bstep (se 3 (by rfl) ⟨9051719, by rfl⟩ : syracuseStep 48275837 = 18103439) B18103439
theorem B3916279 : Blo 1374006 3916279 := bstep (se 1 (by rfl) ⟨2937209, by rfl⟩ : syracuseStep 3916279 = 5874419) B5874419
theorem B3916507 : Blo 1374006 3916507 := bstep (se 1 (by rfl) ⟨2937380, by rfl⟩ : syracuseStep 3916507 = 5874761) B5874761
theorem B33449071 : Blo 1374006 33449071 := bstep (se 1 (by rfl) ⟨25086803, by rfl⟩ : syracuseStep 33449071 = 50173607) B50173607
theorem B2319529 : Blo 1374006 2319529 := bstep (se 2 (by rfl) ⟨869823, by rfl⟩ : syracuseStep 2319529 = 1739647) B1739647
theorem B4637951 : Blo 1374006 4637951 := bstep (se 1 (by rfl) ⟨3478463, by rfl⟩ : syracuseStep 4637951 = 6956927) B6956927
theorem B3302815 : Blo 1374006 3302815 := bstep (se 1 (by rfl) ⟨2477111, by rfl⟩ : syracuseStep 3302815 = 4954223) B4954223
theorem B2320015 : Blo 1374006 2320015 := bstep (se 1 (by rfl) ⟨1740011, by rfl⟩ : syracuseStep 2320015 = 3480023) B3480023
theorem B3303919 : Blo 1374006 3303919 := bstep (se 1 (by rfl) ⟨2477939, by rfl⟩ : syracuseStep 3303919 = 4955879) B4955879
theorem B2320879 : Blo 1374006 2320879 := bstep (se 1 (by rfl) ⟨1740659, by rfl⟩ : syracuseStep 2320879 = 3481319) B3481319
theorem B3967487 : Blo 1374006 3967487 := bstep (se 1 (by rfl) ⟨2975615, by rfl⟩ : syracuseStep 3967487 = 5951231) B5951231
theorem B10725959 : Blo 1374006 10725959 := bstep (se 1 (by rfl) ⟨8044469, by rfl⟩ : syracuseStep 10725959 = 16088939) B16088939
theorem B5024929 : Blo 1374006 5024929 := bstep (se 2 (by rfl) ⟨1884348, by rfl⟩ : syracuseStep 5024929 = 3768697) B3768697
theorem B4640057 : Blo 1374006 4640057 := bstep (se 2 (by rfl) ⟨1740021, by rfl⟩ : syracuseStep 4640057 = 3480043) B3480043
theorem B4402841 : Blo 1374006 4402841 := bstep (se 2 (by rfl) ⟨1651065, by rfl⟩ : syracuseStep 4402841 = 3302131) B3302131
theorem B39636641 : Blo 1374006 39636641 := bstep (se 2 (by rfl) ⟨14863740, by rfl⟩ : syracuseStep 39636641 = 29727481) B29727481
theorem B4640543 : Blo 1374006 4640543 := bstep (se 1 (by rfl) ⟨3480407, by rfl⟩ : syracuseStep 4640543 = 6960815) B6960815
theorem B8360081 : Blo 1374006 8360081 := bstep (se 2 (by rfl) ⟨3135030, by rfl⟩ : syracuseStep 8360081 = 6270061) B6270061
theorem B3092975 : Blo 1374006 3092975 := bstep (se 1 (by rfl) ⟨2319731, by rfl⟩ : syracuseStep 3092975 = 4639463) B4639463
theorem B2061179 : Blo 1374006 2061179 := bstep (se 1 (by rfl) ⟨1545884, by rfl⟩ : syracuseStep 2061179 = 3091769) B3091769
theorem B142816465 : Blo 1374006 142816465 := bstep (se 2 (by rfl) ⟨53556174, by rfl⟩ : syracuseStep 142816465 = 107112349) B107112349
theorem B2061623 : Blo 1374006 2061623 := bstep (se 1 (by rfl) ⟨1546217, by rfl⟩ : syracuseStep 2061623 = 3092435) B3092435
theorem B2061647 : Blo 1374006 2061647 := bstep (se 1 (by rfl) ⟨1546235, by rfl⟩ : syracuseStep 2061647 = 3092471) B3092471
theorem B2061671 : Blo 1374006 2061671 := bstep (se 1 (by rfl) ⟨1546253, by rfl⟩ : syracuseStep 2061671 = 3092507) B3092507
theorem B3094235 : Blo 1374006 3094235 := bstep (se 1 (by rfl) ⟨2320676, by rfl⟩ : syracuseStep 3094235 = 4641353) B4641353
theorem B2611111 : Blo 1374006 2611111 := bstep (se 1 (by rfl) ⟨1958333, by rfl⟩ : syracuseStep 2611111 = 3916667) B3916667
theorem B1374527 : Blo 1374006 1374527 := bstep (se 1 (by rfl) ⟨1030895, by rfl⟩ : syracuseStep 1374527 = 2061791) B2061791
theorem B2062943 : Blo 1374006 2062943 := bstep (se 1 (by rfl) ⟨1547207, by rfl⟩ : syracuseStep 2062943 = 3094415) B3094415
theorem B2063039 : Blo 1374006 2063039 := bstep (se 1 (by rfl) ⟨1547279, by rfl⟩ : syracuseStep 2063039 = 3094559) B3094559
theorem B1375039 : Blo 1374006 1375039 := bstep (se 1 (by rfl) ⟨1031279, by rfl⟩ : syracuseStep 1375039 = 2062559) B2062559
theorem B2063225 : Blo 1374006 2063225 := bstep (se 2 (by rfl) ⟨773709, by rfl⟩ : syracuseStep 2063225 = 1547419) B1547419
theorem B6274145 : Blo 1374006 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B8363191 : Blo 1374006 8363191 := bstep (se 1 (by rfl) ⟨6272393, by rfl⟩ : syracuseStep 8363191 = 12544787) B12544787
theorem B11910523 : Blo 1374006 11910523 := bstep (se 1 (by rfl) ⟨8932892, by rfl⟩ : syracuseStep 11910523 = 17865785) B17865785
theorem B3178543 : Blo 1374006 3178543 := bstep (se 1 (by rfl) ⟨2383907, by rfl⟩ : syracuseStep 3178543 = 4767815) B4767815
theorem B44598761 : Blo 1374006 44598761 := bstep (se 2 (by rfl) ⟨16724535, by rfl⟩ : syracuseStep 44598761 = 33449071) B33449071
theorem B11150921 : Blo 1374006 11150921 := bstep (se 2 (by rfl) ⟨4181595, by rfl⟩ : syracuseStep 11150921 = 8363191) B8363191
theorem B11740909 : Blo 1374006 11740909 := bstep (se 3 (by rfl) ⟨2201420, by rfl⟩ : syracuseStep 11740909 = 4402841) B4402841
theorem B5573387 : Blo 1374006 5573387 := bstep (se 1 (by rfl) ⟨4180040, by rfl⟩ : syracuseStep 5573387 = 8360081) B8360081
theorem B5221705 : Blo 1374006 5221705 := bstep (se 2 (by rfl) ⟨1958139, by rfl⟩ : syracuseStep 5221705 = 3916279) B3916279
theorem B3091967 : Blo 1374006 3091967 := bstep (se 1 (by rfl) ⟨2318975, by rfl⟩ : syracuseStep 3091967 = 4637951) B4637951
theorem B5222009 : Blo 1374006 5222009 := bstep (se 2 (by rfl) ⟨1958253, by rfl⟩ : syracuseStep 5222009 = 3916507) B3916507
theorem B761687813 : Blo 1374006 761687813 := bstep (se 4 (by rfl) ⟨71408232, by rfl⟩ : syracuseStep 761687813 = 142816465) B142816465
theorem B28602557 : Blo 1374006 28602557 := bstep (se 3 (by rfl) ⟨5362979, by rfl⟩ : syracuseStep 28602557 = 10725959) B10725959
theorem B3092705 : Blo 1374006 3092705 := bstep (se 2 (by rfl) ⟨1159764, by rfl⟩ : syracuseStep 3092705 = 2319529) B2319529
theorem B15880697 : Blo 1374006 15880697 := bstep (se 2 (by rfl) ⟨5955261, by rfl⟩ : syracuseStep 15880697 = 11910523) B11910523
theorem B4403753 : Blo 1374006 4403753 := bstep (se 2 (by rfl) ⟨1651407, by rfl⟩ : syracuseStep 4403753 = 3302815) B3302815
theorem B4182763 : Blo 1374006 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B3093353 : Blo 1374006 3093353 := bstep (se 2 (by rfl) ⟨1160007, by rfl⟩ : syracuseStep 3093353 = 2320015) B2320015
theorem B3093371 : Blo 1374006 3093371 := bstep (se 1 (by rfl) ⟨2320028, by rfl⟩ : syracuseStep 3093371 = 4640057) B4640057
theorem B26424427 : Blo 1374006 26424427 := bstep (se 1 (by rfl) ⟨19818320, by rfl⟩ : syracuseStep 26424427 = 39636641) B39636641
theorem B3093695 : Blo 1374006 3093695 := bstep (se 1 (by rfl) ⟨2320271, by rfl⟩ : syracuseStep 3093695 = 4640543) B4640543
theorem B32183891 : Blo 1374006 32183891 := bstep (se 1 (by rfl) ⟨24137918, by rfl⟩ : syracuseStep 32183891 = 48275837) B48275837
theorem B2061983 : Blo 1374006 2061983 := bstep (se 1 (by rfl) ⟨1546487, by rfl⟩ : syracuseStep 2061983 = 3092975) B3092975
theorem B1374119 : Blo 1374006 1374119 := bstep (se 1 (by rfl) ⟨1030589, by rfl⟩ : syracuseStep 1374119 = 2061179) B2061179
theorem B3094505 : Blo 1374006 3094505 := bstep (se 2 (by rfl) ⟨1160439, by rfl⟩ : syracuseStep 3094505 = 2320879) B2320879
theorem B1374415 : Blo 1374006 1374415 := bstep (se 1 (by rfl) ⟨1030811, by rfl⟩ : syracuseStep 1374415 = 2061623) B2061623
theorem B1374431 : Blo 1374006 1374431 := bstep (se 1 (by rfl) ⟨1030823, by rfl⟩ : syracuseStep 1374431 = 2061647) B2061647
theorem B1374447 : Blo 1374006 1374447 := bstep (se 1 (by rfl) ⟨1030835, by rfl⟩ : syracuseStep 1374447 = 2061671) B2061671
theorem B2062823 : Blo 1374006 2062823 := bstep (se 1 (by rfl) ⟨1547117, by rfl⟩ : syracuseStep 2062823 = 3094235) B3094235
theorem B6699905 : Blo 1374006 6699905 := bstep (se 2 (by rfl) ⟨2512464, by rfl⟩ : syracuseStep 6699905 = 5024929) B5024929
theorem B2644991 : Blo 1374006 2644991 := bstep (se 1 (by rfl) ⟨1983743, by rfl⟩ : syracuseStep 2644991 = 3967487) B3967487
theorem B1375295 : Blo 1374006 1375295 := bstep (se 1 (by rfl) ⟨1031471, by rfl⟩ : syracuseStep 1375295 = 2062943) B2062943
theorem B1375359 : Blo 1374006 1375359 := bstep (se 1 (by rfl) ⟨1031519, by rfl⟩ : syracuseStep 1375359 = 2063039) B2063039
theorem B1375483 : Blo 1374006 1375483 := bstep (se 1 (by rfl) ⟨1031612, by rfl⟩ : syracuseStep 1375483 = 2063225) B2063225
theorem B3481481 : Blo 1374006 3481481 := bstep (se 2 (by rfl) ⟨1305555, by rfl⟩ : syracuseStep 3481481 = 2611111) B2611111
theorem B17620901 : Blo 1374006 17620901 := bstep (se 4 (by rfl) ⟨1651959, by rfl⟩ : syracuseStep 17620901 = 3303919) B3303919
theorem B21455927 : Blo 1374006 21455927 := bstep (se 1 (by rfl) ⟨16091945, by rfl⟩ : syracuseStep 21455927 = 32183891) B32183891
theorem B4466603 : Blo 1374006 4466603 := bstep (se 1 (by rfl) ⟨3349952, by rfl⟩ : syracuseStep 4466603 = 6699905) B6699905
theorem B1763327 : Blo 1374006 1763327 := bstep (se 1 (by rfl) ⟨1322495, by rfl⟩ : syracuseStep 1763327 = 2644991) B2644991
theorem B507791875 : Blo 1374006 507791875 := bstep (se 1 (by rfl) ⟨380843906, by rfl⟩ : syracuseStep 507791875 = 761687813) B761687813
theorem B2320987 : Blo 1374006 2320987 := bstep (se 1 (by rfl) ⟨1740740, by rfl⟩ : syracuseStep 2320987 = 3481481) B3481481
theorem B4238057 : Blo 1374006 4238057 := bstep (se 2 (by rfl) ⟨1589271, by rfl⟩ : syracuseStep 4238057 = 3178543) B3178543
theorem B10587131 : Blo 1374006 10587131 := bstep (se 1 (by rfl) ⟨7940348, by rfl⟩ : syracuseStep 10587131 = 15880697) B15880697
theorem B2935835 : Blo 1374006 2935835 := bstep (se 1 (by rfl) ⟨2201876, by rfl⟩ : syracuseStep 2935835 = 4403753) B4403753
theorem B29732507 : Blo 1374006 29732507 := bstep (se 1 (by rfl) ⟨22299380, by rfl⟩ : syracuseStep 29732507 = 44598761) B44598761
theorem B7433947 : Blo 1374006 7433947 := bstep (se 1 (by rfl) ⟨5575460, by rfl⟩ : syracuseStep 7433947 = 11150921) B11150921
theorem B3715591 : Blo 1374006 3715591 := bstep (se 1 (by rfl) ⟨2786693, by rfl⟩ : syracuseStep 3715591 = 5573387) B5573387
theorem B2061311 : Blo 1374006 2061311 := bstep (se 1 (by rfl) ⟨1545983, by rfl⟩ : syracuseStep 2061311 = 3091967) B3091967
theorem B19068371 : Blo 1374006 19068371 := bstep (se 1 (by rfl) ⟨14301278, by rfl⟩ : syracuseStep 19068371 = 28602557) B28602557
theorem B2061803 : Blo 1374006 2061803 := bstep (se 1 (by rfl) ⟨1546352, by rfl⟩ : syracuseStep 2061803 = 3092705) B3092705
theorem B2062235 : Blo 1374006 2062235 := bstep (se 1 (by rfl) ⟨1546676, by rfl⟩ : syracuseStep 2062235 = 3093353) B3093353
theorem B2062247 : Blo 1374006 2062247 := bstep (se 1 (by rfl) ⟨1546685, by rfl⟩ : syracuseStep 2062247 = 3093371) B3093371
theorem B2062463 : Blo 1374006 2062463 := bstep (se 1 (by rfl) ⟨1546847, by rfl⟩ : syracuseStep 2062463 = 3093695) B3093695
theorem B5577017 : Blo 1374006 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B1374655 : Blo 1374006 1374655 := bstep (se 1 (by rfl) ⟨1030991, by rfl⟩ : syracuseStep 1374655 = 2061983) B2061983
theorem B2063003 : Blo 1374006 2063003 := bstep (se 1 (by rfl) ⟨1547252, by rfl⟩ : syracuseStep 2063003 = 3094505) B3094505
theorem B35232569 : Blo 1374006 35232569 := bstep (se 2 (by rfl) ⟨13212213, by rfl⟩ : syracuseStep 35232569 = 26424427) B26424427
theorem B1375215 : Blo 1374006 1375215 := bstep (se 1 (by rfl) ⟨1031411, by rfl⟩ : syracuseStep 1375215 = 2062823) B2062823
theorem B6962273 : Blo 1374006 6962273 := bstep (se 2 (by rfl) ⟨2610852, by rfl⟩ : syracuseStep 6962273 = 5221705) B5221705
theorem B15654545 : Blo 1374006 15654545 := bstep (se 2 (by rfl) ⟨5870454, by rfl⟩ : syracuseStep 15654545 = 11740909) B11740909
theorem B3481339 : Blo 1374006 3481339 := bstep (se 1 (by rfl) ⟨2611004, by rfl⟩ : syracuseStep 3481339 = 5222009) B5222009
theorem B11747267 : Blo 1374006 11747267 := bstep (se 1 (by rfl) ⟨8810450, by rfl⟩ : syracuseStep 11747267 = 17620901) B17620901
theorem B14303951 : Blo 1374006 14303951 := bstep (se 1 (by rfl) ⟨10727963, by rfl⟩ : syracuseStep 14303951 = 21455927) B21455927
theorem B23488379 : Blo 1374006 23488379 := bstep (se 1 (by rfl) ⟨17616284, by rfl⟩ : syracuseStep 23488379 = 35232569) B35232569
theorem B677055833 : Blo 1374006 677055833 := bstep (se 2 (by rfl) ⟨253895937, by rfl⟩ : syracuseStep 677055833 = 507791875) B507791875
theorem B14872045 : Blo 1374006 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B2977735 : Blo 1374006 2977735 := bstep (se 1 (by rfl) ⟨2233301, by rfl⟩ : syracuseStep 2977735 = 4466603) B4466603
theorem B7058087 : Blo 1374006 7058087 := bstep (se 1 (by rfl) ⟨5293565, by rfl⟩ : syracuseStep 7058087 = 10587131) B10587131
theorem B4641515 : Blo 1374006 4641515 := bstep (se 1 (by rfl) ⟨3481136, by rfl⟩ : syracuseStep 4641515 = 6962273) B6962273
theorem B4641785 : Blo 1374006 4641785 := bstep (se 2 (by rfl) ⟨1740669, by rfl⟩ : syracuseStep 4641785 = 3481339) B3481339
theorem B19821671 : Blo 1374006 19821671 := bstep (se 1 (by rfl) ⟨14866253, by rfl⟩ : syracuseStep 19821671 = 29732507) B29732507
theorem B1374207 : Blo 1374006 1374207 := bstep (se 1 (by rfl) ⟨1030655, by rfl⟩ : syracuseStep 1374207 = 2061311) B2061311
theorem B4954121 : Blo 1374006 4954121 := bstep (se 2 (by rfl) ⟨1857795, by rfl⟩ : syracuseStep 4954121 = 3715591) B3715591
theorem B3094649 : Blo 1374006 3094649 := bstep (se 2 (by rfl) ⟨1160493, by rfl⟩ : syracuseStep 3094649 = 2320987) B2320987
theorem B12712247 : Blo 1374006 12712247 := bstep (se 1 (by rfl) ⟨9534185, by rfl⟩ : syracuseStep 12712247 = 19068371) B19068371
theorem B1374535 : Blo 1374006 1374535 := bstep (se 1 (by rfl) ⟨1030901, by rfl⟩ : syracuseStep 1374535 = 2061803) B2061803
theorem B1374823 : Blo 1374006 1374823 := bstep (se 1 (by rfl) ⟨1031117, by rfl⟩ : syracuseStep 1374823 = 2062235) B2062235
theorem B1374831 : Blo 1374006 1374831 := bstep (se 1 (by rfl) ⟨1031123, by rfl⟩ : syracuseStep 1374831 = 2062247) B2062247
theorem B1374975 : Blo 1374006 1374975 := bstep (se 1 (by rfl) ⟨1031231, by rfl⟩ : syracuseStep 1374975 = 2062463) B2062463
theorem B1375335 : Blo 1374006 1375335 := bstep (se 1 (by rfl) ⟨1031501, by rfl⟩ : syracuseStep 1375335 = 2063003) B2063003
theorem B2825371 : Blo 1374006 2825371 := bstep (se 1 (by rfl) ⟨2119028, by rfl⟩ : syracuseStep 2825371 = 4238057) B4238057
theorem B1957223 : Blo 1374006 1957223 := bstep (se 1 (by rfl) ⟨1467917, by rfl⟩ : syracuseStep 1957223 = 2935835) B2935835
theorem B9911929 : Blo 1374006 9911929 := bstep (se 2 (by rfl) ⟨3716973, by rfl⟩ : syracuseStep 9911929 = 7433947) B7433947
theorem B10436363 : Blo 1374006 10436363 := bstep (se 1 (by rfl) ⟨7827272, by rfl⟩ : syracuseStep 10436363 = 15654545) B15654545
theorem B7831511 : Blo 1374006 7831511 := bstep (se 1 (by rfl) ⟨5873633, by rfl⟩ : syracuseStep 7831511 = 11747267) B11747267
theorem B4702205 : Blo 1374006 4702205 := bstep (se 3 (by rfl) ⟨881663, by rfl⟩ : syracuseStep 4702205 = 1763327) B1763327
theorem B9535967 : Blo 1374006 9535967 := bstep (se 1 (by rfl) ⟨7151975, by rfl⟩ : syracuseStep 9535967 = 14303951) B14303951
theorem B13214447 : Blo 1374006 13214447 := bstep (se 1 (by rfl) ⟨9910835, by rfl⟩ : syracuseStep 13214447 = 19821671) B19821671
theorem B5219261 : Blo 1374006 5219261 := bstep (se 3 (by rfl) ⟨978611, by rfl⟩ : syracuseStep 5219261 = 1957223) B1957223
theorem B3302747 : Blo 1374006 3302747 := bstep (se 1 (by rfl) ⟨2477060, by rfl⟩ : syracuseStep 3302747 = 4954121) B4954121
theorem B13215905 : Blo 1374006 13215905 := bstep (se 2 (by rfl) ⟨4955964, by rfl⟩ : syracuseStep 13215905 = 9911929) B9911929
theorem B6957575 : Blo 1374006 6957575 := bstep (se 1 (by rfl) ⟨5218181, by rfl⟩ : syracuseStep 6957575 = 10436363) B10436363
theorem B5221007 : Blo 1374006 5221007 := bstep (se 1 (by rfl) ⟨3915755, by rfl⟩ : syracuseStep 5221007 = 7831511) B7831511
theorem B4705391 : Blo 1374006 4705391 := bstep (se 1 (by rfl) ⟨3529043, by rfl⟩ : syracuseStep 4705391 = 7058087) B7058087
theorem B15068645 : Blo 1374006 15068645 := bstep (se 4 (by rfl) ⟨1412685, by rfl⟩ : syracuseStep 15068645 = 2825371) B2825371
theorem B15658919 : Blo 1374006 15658919 := bstep (se 1 (by rfl) ⟨11744189, by rfl⟩ : syracuseStep 15658919 = 23488379) B23488379
theorem B8474831 : Blo 1374006 8474831 := bstep (se 1 (by rfl) ⟨6356123, by rfl⟩ : syracuseStep 8474831 = 12712247) B12712247
theorem B19829393 : Blo 1374006 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B3970313 : Blo 1374006 3970313 := bstep (se 2 (by rfl) ⟨1488867, by rfl⟩ : syracuseStep 3970313 = 2977735) B2977735
theorem B3134803 : Blo 1374006 3134803 := bstep (se 1 (by rfl) ⟨2351102, by rfl⟩ : syracuseStep 3134803 = 4702205) B4702205
theorem B3094343 : Blo 1374006 3094343 := bstep (se 1 (by rfl) ⟨2320757, by rfl⟩ : syracuseStep 3094343 = 4641515) B4641515
theorem B3094523 : Blo 1374006 3094523 := bstep (se 1 (by rfl) ⟨2320892, by rfl⟩ : syracuseStep 3094523 = 4641785) B4641785
theorem B2063099 : Blo 1374006 2063099 := bstep (se 1 (by rfl) ⟨1547324, by rfl⟩ : syracuseStep 2063099 = 3094649) B3094649
theorem B451370555 : Blo 1374006 451370555 := bstep (se 1 (by rfl) ⟨338527916, by rfl⟩ : syracuseStep 451370555 = 677055833) B677055833
theorem B6357311 : Blo 1374006 6357311 := bstep (se 1 (by rfl) ⟨4767983, by rfl⟩ : syracuseStep 6357311 = 9535967) B9535967
theorem B2646875 : Blo 1374006 2646875 := bstep (se 1 (by rfl) ⟨1985156, by rfl⟩ : syracuseStep 2646875 = 3970313) B3970313
theorem B4638383 : Blo 1374006 4638383 := bstep (se 1 (by rfl) ⟨3478787, by rfl⟩ : syracuseStep 4638383 = 6957575) B6957575
theorem B4179737 : Blo 1374006 4179737 := bstep (se 2 (by rfl) ⟨1567401, by rfl⟩ : syracuseStep 4179737 = 3134803) B3134803
theorem B10045763 : Blo 1374006 10045763 := bstep (se 1 (by rfl) ⟨7534322, by rfl⟩ : syracuseStep 10045763 = 15068645) B15068645
theorem B10439279 : Blo 1374006 10439279 := bstep (se 1 (by rfl) ⟨7829459, by rfl⟩ : syracuseStep 10439279 = 15658919) B15658919
theorem B8809631 : Blo 1374006 8809631 := bstep (se 1 (by rfl) ⟨6607223, by rfl⟩ : syracuseStep 8809631 = 13214447) B13214447
theorem B8810603 : Blo 1374006 8810603 := bstep (se 1 (by rfl) ⟨6607952, by rfl⟩ : syracuseStep 8810603 = 13215905) B13215905
theorem B300913703 : Blo 1374006 300913703 := bstep (se 1 (by rfl) ⟨225685277, by rfl⟩ : syracuseStep 300913703 = 451370555) B451370555
theorem B5649887 : Blo 1374006 5649887 := bstep (se 1 (by rfl) ⟨4237415, by rfl⟩ : syracuseStep 5649887 = 8474831) B8474831
theorem B12547709 : Blo 1374006 12547709 := bstep (se 3 (by rfl) ⟨2352695, by rfl⟩ : syracuseStep 12547709 = 4705391) B4705391
theorem B13219595 : Blo 1374006 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B3479507 : Blo 1374006 3479507 := bstep (se 1 (by rfl) ⟨2609630, by rfl⟩ : syracuseStep 3479507 = 5219261) B5219261
theorem B2201831 : Blo 1374006 2201831 := bstep (se 1 (by rfl) ⟨1651373, by rfl⟩ : syracuseStep 2201831 = 3302747) B3302747
theorem B2062895 : Blo 1374006 2062895 := bstep (se 1 (by rfl) ⟨1547171, by rfl⟩ : syracuseStep 2062895 = 3094343) B3094343
theorem B2063015 : Blo 1374006 2063015 := bstep (se 1 (by rfl) ⟨1547261, by rfl⟩ : syracuseStep 2063015 = 3094523) B3094523
theorem B3480671 : Blo 1374006 3480671 := bstep (se 1 (by rfl) ⟨2610503, by rfl⟩ : syracuseStep 3480671 = 5221007) B5221007
theorem B1375399 : Blo 1374006 1375399 := bstep (se 1 (by rfl) ⟨1031549, by rfl⟩ : syracuseStep 1375399 = 2063099) B2063099
theorem B5873735 : Blo 1374006 5873735 := bstep (se 1 (by rfl) ⟨4405301, by rfl⟩ : syracuseStep 5873735 = 8810603) B8810603
theorem B8365139 : Blo 1374006 8365139 := bstep (se 1 (by rfl) ⟨6273854, by rfl⟩ : syracuseStep 8365139 = 12547709) B12547709
theorem B2786491 : Blo 1374006 2786491 := bstep (se 1 (by rfl) ⟨2089868, by rfl⟩ : syracuseStep 2786491 = 4179737) B4179737
theorem B2319671 : Blo 1374006 2319671 := bstep (se 1 (by rfl) ⟨1739753, by rfl⟩ : syracuseStep 2319671 = 3479507) B3479507
theorem B1467887 : Blo 1374006 1467887 := bstep (se 1 (by rfl) ⟨1100915, by rfl⟩ : syracuseStep 1467887 = 2201831) B2201831
theorem B2320447 : Blo 1374006 2320447 := bstep (se 1 (by rfl) ⟨1740335, by rfl⟩ : syracuseStep 2320447 = 3480671) B3480671
theorem B4238207 : Blo 1374006 4238207 := bstep (se 1 (by rfl) ⟨3178655, by rfl⟩ : syracuseStep 4238207 = 6357311) B6357311
theorem B200609135 : Blo 1374006 200609135 := bstep (se 1 (by rfl) ⟨150456851, by rfl⟩ : syracuseStep 200609135 = 300913703) B300913703
theorem B3092255 : Blo 1374006 3092255 := bstep (se 1 (by rfl) ⟨2319191, by rfl⟩ : syracuseStep 3092255 = 4638383) B4638383
theorem B6697175 : Blo 1374006 6697175 := bstep (se 1 (by rfl) ⟨5022881, by rfl⟩ : syracuseStep 6697175 = 10045763) B10045763
theorem B6959519 : Blo 1374006 6959519 := bstep (se 1 (by rfl) ⟨5219639, by rfl⟩ : syracuseStep 6959519 = 10439279) B10439279
theorem B7058333 : Blo 1374006 7058333 := bstep (se 3 (by rfl) ⟨1323437, by rfl⟩ : syracuseStep 7058333 = 2646875) B2646875
theorem B3766591 : Blo 1374006 3766591 := bstep (se 1 (by rfl) ⟨2824943, by rfl⟩ : syracuseStep 3766591 = 5649887) B5649887
theorem B8813063 : Blo 1374006 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B1375263 : Blo 1374006 1375263 := bstep (se 1 (by rfl) ⟨1031447, by rfl⟩ : syracuseStep 1375263 = 2062895) B2062895
theorem B1375343 : Blo 1374006 1375343 := bstep (se 1 (by rfl) ⟨1031507, by rfl⟩ : syracuseStep 1375343 = 2063015) B2063015
theorem B5873087 : Blo 1374006 5873087 := bstep (se 1 (by rfl) ⟨4404815, by rfl⟩ : syracuseStep 5873087 = 8809631) B8809631
theorem B15663293 : Blo 1374006 15663293 := bstep (se 3 (by rfl) ⟨2936867, by rfl⟩ : syracuseStep 15663293 = 5873735) B5873735
theorem B17859133 : Blo 1374006 17859133 := bstep (se 3 (by rfl) ⟨3348587, by rfl⟩ : syracuseStep 17859133 = 6697175) B6697175
theorem B20088485 : Blo 1374006 20088485 := bstep (se 4 (by rfl) ⟨1883295, by rfl⟩ : syracuseStep 20088485 = 3766591) B3766591
theorem B15657461 : Blo 1374006 15657461 := bstep (se 5 (by rfl) ⟨733943, by rfl⟩ : syracuseStep 15657461 = 1467887) B1467887
theorem B4639679 : Blo 1374006 4639679 := bstep (se 1 (by rfl) ⟨3479759, by rfl⟩ : syracuseStep 4639679 = 6959519) B6959519
theorem B4705555 : Blo 1374006 4705555 := bstep (se 1 (by rfl) ⟨3529166, by rfl⟩ : syracuseStep 4705555 = 7058333) B7058333
theorem B3715321 : Blo 1374006 3715321 := bstep (se 2 (by rfl) ⟨1393245, by rfl⟩ : syracuseStep 3715321 = 2786491) B2786491
theorem B133739423 : Blo 1374006 133739423 := bstep (se 1 (by rfl) ⟨100304567, by rfl⟩ : syracuseStep 133739423 = 200609135) B200609135
theorem B2061503 : Blo 1374006 2061503 := bstep (se 1 (by rfl) ⟨1546127, by rfl⟩ : syracuseStep 2061503 = 3092255) B3092255
theorem B3093929 : Blo 1374006 3093929 := bstep (se 2 (by rfl) ⟨1160223, by rfl⟩ : syracuseStep 3093929 = 2320447) B2320447
theorem B5576759 : Blo 1374006 5576759 := bstep (se 1 (by rfl) ⟨4182569, by rfl⟩ : syracuseStep 5576759 = 8365139) B8365139
theorem B1546447 : Blo 1374006 1546447 := bstep (se 1 (by rfl) ⟨1159835, by rfl⟩ : syracuseStep 1546447 = 2319671) B2319671
theorem B23501501 : Blo 1374006 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B2825471 : Blo 1374006 2825471 := bstep (se 1 (by rfl) ⟨2119103, by rfl⟩ : syracuseStep 2825471 = 4238207) B4238207
theorem B3915391 : Blo 1374006 3915391 := bstep (se 1 (by rfl) ⟨2936543, by rfl⟩ : syracuseStep 3915391 = 5873087) B5873087
theorem B10438307 : Blo 1374006 10438307 := bstep (se 1 (by rfl) ⟨7828730, by rfl⟩ : syracuseStep 10438307 = 15657461) B15657461
theorem B5220521 : Blo 1374006 5220521 := bstep (se 2 (by rfl) ⟨1957695, by rfl⟩ : syracuseStep 5220521 = 3915391) B3915391
theorem B15667667 : Blo 1374006 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B3093119 : Blo 1374006 3093119 := bstep (se 1 (by rfl) ⟨2319839, by rfl⟩ : syracuseStep 3093119 = 4639679) B4639679
theorem B10442195 : Blo 1374006 10442195 := bstep (se 1 (by rfl) ⟨7831646, by rfl⟩ : syracuseStep 10442195 = 15663293) B15663293
theorem B2061929 : Blo 1374006 2061929 := bstep (se 2 (by rfl) ⟨773223, by rfl⟩ : syracuseStep 2061929 = 1546447) B1546447
theorem B4953761 : Blo 1374006 4953761 := bstep (se 2 (by rfl) ⟨1857660, by rfl⟩ : syracuseStep 4953761 = 3715321) B3715321
theorem B89159615 : Blo 1374006 89159615 := bstep (se 1 (by rfl) ⟨66869711, by rfl⟩ : syracuseStep 89159615 = 133739423) B133739423
theorem B23812177 : Blo 1374006 23812177 := bstep (se 2 (by rfl) ⟨8929566, by rfl⟩ : syracuseStep 23812177 = 17859133) B17859133
theorem B1374335 : Blo 1374006 1374335 := bstep (se 1 (by rfl) ⟨1030751, by rfl⟩ : syracuseStep 1374335 = 2061503) B2061503
theorem B2062619 : Blo 1374006 2062619 := bstep (se 1 (by rfl) ⟨1546964, by rfl⟩ : syracuseStep 2062619 = 3093929) B3093929
theorem B13392323 : Blo 1374006 13392323 := bstep (se 1 (by rfl) ⟨10044242, by rfl⟩ : syracuseStep 13392323 = 20088485) B20088485
theorem B3717839 : Blo 1374006 3717839 := bstep (se 1 (by rfl) ⟨2788379, by rfl⟩ : syracuseStep 3717839 = 5576759) B5576759
theorem B6274073 : Blo 1374006 6274073 := bstep (se 2 (by rfl) ⟨2352777, by rfl⟩ : syracuseStep 6274073 = 4705555) B4705555
theorem B1883647 : Blo 1374006 1883647 := bstep (se 1 (by rfl) ⟨1412735, by rfl⟩ : syracuseStep 1883647 = 2825471) B2825471
theorem B10445111 : Blo 1374006 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B3302507 : Blo 1374006 3302507 := bstep (se 1 (by rfl) ⟨2476880, by rfl⟩ : syracuseStep 3302507 = 4953761) B4953761
theorem B9914237 : Blo 1374006 9914237 := bstep (se 3 (by rfl) ⟨1858919, by rfl⟩ : syracuseStep 9914237 = 3717839) B3717839
theorem B6958871 : Blo 1374006 6958871 := bstep (se 1 (by rfl) ⟨5219153, by rfl⟩ : syracuseStep 6958871 = 10438307) B10438307
theorem B2511529 : Blo 1374006 2511529 := bstep (se 2 (by rfl) ⟨941823, by rfl⟩ : syracuseStep 2511529 = 1883647) B1883647
theorem B4182715 : Blo 1374006 4182715 := bstep (se 1 (by rfl) ⟨3137036, by rfl⟩ : syracuseStep 4182715 = 6274073) B6274073
theorem B31749569 : Blo 1374006 31749569 := bstep (se 2 (by rfl) ⟨11906088, by rfl⟩ : syracuseStep 31749569 = 23812177) B23812177
theorem B2062079 : Blo 1374006 2062079 := bstep (se 1 (by rfl) ⟨1546559, by rfl⟩ : syracuseStep 2062079 = 3093119) B3093119
theorem B6961463 : Blo 1374006 6961463 := bstep (se 1 (by rfl) ⟨5221097, by rfl⟩ : syracuseStep 6961463 = 10442195) B10442195
theorem B1374619 : Blo 1374006 1374619 := bstep (se 1 (by rfl) ⟨1030964, by rfl⟩ : syracuseStep 1374619 = 2061929) B2061929
theorem B59439743 : Blo 1374006 59439743 := bstep (se 1 (by rfl) ⟨44579807, by rfl⟩ : syracuseStep 59439743 = 89159615) B89159615
theorem B3480347 : Blo 1374006 3480347 := bstep (se 1 (by rfl) ⟨2610260, by rfl⟩ : syracuseStep 3480347 = 5220521) B5220521
theorem B1375079 : Blo 1374006 1375079 := bstep (se 1 (by rfl) ⟨1031309, by rfl⟩ : syracuseStep 1375079 = 2062619) B2062619
theorem B8928215 : Blo 1374006 8928215 := bstep (se 1 (by rfl) ⟨6696161, by rfl⟩ : syracuseStep 8928215 = 13392323) B13392323
theorem B6963407 : Blo 1374006 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B13394821 : Blo 1374006 13394821 := bstep (se 4 (by rfl) ⟨1255764, by rfl⟩ : syracuseStep 13394821 = 2511529) B2511529
theorem B39626495 : Blo 1374006 39626495 := bstep (se 1 (by rfl) ⟨29719871, by rfl⟩ : syracuseStep 39626495 = 59439743) B59439743
theorem B2320231 : Blo 1374006 2320231 := bstep (se 1 (by rfl) ⟨1740173, by rfl⟩ : syracuseStep 2320231 = 3480347) B3480347
theorem B4639247 : Blo 1374006 4639247 := bstep (se 1 (by rfl) ⟨3479435, by rfl⟩ : syracuseStep 4639247 = 6958871) B6958871
theorem B4640975 : Blo 1374006 4640975 := bstep (se 1 (by rfl) ⟨3480731, by rfl⟩ : syracuseStep 4640975 = 6961463) B6961463
theorem B5952143 : Blo 1374006 5952143 := bstep (se 1 (by rfl) ⟨4464107, by rfl⟩ : syracuseStep 5952143 = 8928215) B8928215
theorem B2201671 : Blo 1374006 2201671 := bstep (se 1 (by rfl) ⟨1651253, by rfl⟩ : syracuseStep 2201671 = 3302507) B3302507
theorem B5576953 : Blo 1374006 5576953 := bstep (se 2 (by rfl) ⟨2091357, by rfl⟩ : syracuseStep 5576953 = 4182715) B4182715
theorem B21166379 : Blo 1374006 21166379 := bstep (se 1 (by rfl) ⟨15874784, by rfl⟩ : syracuseStep 21166379 = 31749569) B31749569
theorem B1374719 : Blo 1374006 1374719 := bstep (se 1 (by rfl) ⟨1031039, by rfl⟩ : syracuseStep 1374719 = 2062079) B2062079
theorem B6609491 : Blo 1374006 6609491 := bstep (se 1 (by rfl) ⟨4957118, by rfl⟩ : syracuseStep 6609491 = 9914237) B9914237
theorem B17859761 : Blo 1374006 17859761 := bstep (se 2 (by rfl) ⟨6697410, by rfl⟩ : syracuseStep 17859761 = 13394821) B13394821
theorem B11742245 : Blo 1374006 11742245 := bstep (se 4 (by rfl) ⟨1100835, by rfl⟩ : syracuseStep 11742245 = 2201671) B2201671
theorem B14110919 : Blo 1374006 14110919 := bstep (se 1 (by rfl) ⟨10583189, by rfl⟩ : syracuseStep 14110919 = 21166379) B21166379
theorem B3092831 : Blo 1374006 3092831 := bstep (se 1 (by rfl) ⟨2319623, by rfl⟩ : syracuseStep 3092831 = 4639247) B4639247
theorem B15872381 : Blo 1374006 15872381 := bstep (se 3 (by rfl) ⟨2976071, by rfl⟩ : syracuseStep 15872381 = 5952143) B5952143
theorem B3093641 : Blo 1374006 3093641 := bstep (se 2 (by rfl) ⟨1160115, by rfl⟩ : syracuseStep 3093641 = 2320231) B2320231
theorem B3093983 : Blo 1374006 3093983 := bstep (se 1 (by rfl) ⟨2320487, by rfl⟩ : syracuseStep 3093983 = 4640975) B4640975
theorem B4642271 : Blo 1374006 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B7435937 : Blo 1374006 7435937 := bstep (se 2 (by rfl) ⟨2788476, by rfl⟩ : syracuseStep 7435937 = 5576953) B5576953
theorem B26417663 : Blo 1374006 26417663 := bstep (se 1 (by rfl) ⟨19813247, by rfl⟩ : syracuseStep 26417663 = 39626495) B39626495
theorem B4406327 : Blo 1374006 4406327 := bstep (se 1 (by rfl) ⟨3304745, by rfl⟩ : syracuseStep 4406327 = 6609491) B6609491
theorem B4957291 : Blo 1374006 4957291 := bstep (se 1 (by rfl) ⟨3717968, by rfl⟩ : syracuseStep 4957291 = 7435937) B7435937
theorem B9407279 : Blo 1374006 9407279 := bstep (se 1 (by rfl) ⟨7055459, by rfl⟩ : syracuseStep 9407279 = 14110919) B14110919
theorem B11906507 : Blo 1374006 11906507 := bstep (se 1 (by rfl) ⟨8929880, by rfl⟩ : syracuseStep 11906507 = 17859761) B17859761
theorem B7828163 : Blo 1374006 7828163 := bstep (se 1 (by rfl) ⟨5871122, by rfl⟩ : syracuseStep 7828163 = 11742245) B11742245
theorem B2937551 : Blo 1374006 2937551 := bstep (se 1 (by rfl) ⟨2203163, by rfl⟩ : syracuseStep 2937551 = 4406327) B4406327
theorem B2061887 : Blo 1374006 2061887 := bstep (se 1 (by rfl) ⟨1546415, by rfl⟩ : syracuseStep 2061887 = 3092831) B3092831
theorem B10581587 : Blo 1374006 10581587 := bstep (se 1 (by rfl) ⟨7936190, by rfl⟩ : syracuseStep 10581587 = 15872381) B15872381
theorem B2062427 : Blo 1374006 2062427 := bstep (se 1 (by rfl) ⟨1546820, by rfl⟩ : syracuseStep 2062427 = 3093641) B3093641
theorem B2062655 : Blo 1374006 2062655 := bstep (se 1 (by rfl) ⟨1546991, by rfl⟩ : syracuseStep 2062655 = 3093983) B3093983
theorem B3094847 : Blo 1374006 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B17611775 : Blo 1374006 17611775 := bstep (se 1 (by rfl) ⟨13208831, by rfl⟩ : syracuseStep 17611775 = 26417663) B26417663
theorem B5218775 : Blo 1374006 5218775 := bstep (se 1 (by rfl) ⟨3914081, by rfl⟩ : syracuseStep 5218775 = 7828163) B7828163
theorem B7054391 : Blo 1374006 7054391 := bstep (se 1 (by rfl) ⟨5290793, by rfl⟩ : syracuseStep 7054391 = 10581587) B10581587
theorem B7833469 : Blo 1374006 7833469 := bstep (se 3 (by rfl) ⟨1468775, by rfl⟩ : syracuseStep 7833469 = 2937551) B2937551
theorem B11741183 : Blo 1374006 11741183 := bstep (se 1 (by rfl) ⟨8805887, by rfl⟩ : syracuseStep 11741183 = 17611775) B17611775
theorem B26438885 : Blo 1374006 26438885 := bstep (se 4 (by rfl) ⟨2478645, by rfl⟩ : syracuseStep 26438885 = 4957291) B4957291
theorem B6271519 : Blo 1374006 6271519 := bstep (se 1 (by rfl) ⟨4703639, by rfl⟩ : syracuseStep 6271519 = 9407279) B9407279
theorem B1374591 : Blo 1374006 1374591 := bstep (se 1 (by rfl) ⟨1030943, by rfl⟩ : syracuseStep 1374591 = 2061887) B2061887
theorem B1374951 : Blo 1374006 1374951 := bstep (se 1 (by rfl) ⟨1031213, by rfl⟩ : syracuseStep 1374951 = 2062427) B2062427
theorem B1375103 : Blo 1374006 1375103 := bstep (se 1 (by rfl) ⟨1031327, by rfl⟩ : syracuseStep 1375103 = 2062655) B2062655
theorem B2063231 : Blo 1374006 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B7937671 : Blo 1374006 7937671 := bstep (se 1 (by rfl) ⟨5953253, by rfl⟩ : syracuseStep 7937671 = 11906507) B11906507
theorem B18811709 : Blo 1374006 18811709 := bstep (se 3 (by rfl) ⟨3527195, by rfl⟩ : syracuseStep 18811709 = 7054391) B7054391
theorem B7827455 : Blo 1374006 7827455 := bstep (se 1 (by rfl) ⟨5870591, by rfl⟩ : syracuseStep 7827455 = 11741183) B11741183
theorem B17625923 : Blo 1374006 17625923 := bstep (se 1 (by rfl) ⟨13219442, by rfl⟩ : syracuseStep 17625923 = 26438885) B26438885
theorem B3479183 : Blo 1374006 3479183 := bstep (se 1 (by rfl) ⟨2609387, by rfl⟩ : syracuseStep 3479183 = 5218775) B5218775
theorem B8362025 : Blo 1374006 8362025 := bstep (se 2 (by rfl) ⟨3135759, by rfl⟩ : syracuseStep 8362025 = 6271519) B6271519
theorem B1375487 : Blo 1374006 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B10583561 : Blo 1374006 10583561 := bstep (se 2 (by rfl) ⟨3968835, by rfl⟩ : syracuseStep 10583561 = 7937671) B7937671
theorem B10444625 : Blo 1374006 10444625 := bstep (se 2 (by rfl) ⟨3916734, by rfl⟩ : syracuseStep 10444625 = 7833469) B7833469
theorem B2319455 : Blo 1374006 2319455 := bstep (se 1 (by rfl) ⟨1739591, by rfl⟩ : syracuseStep 2319455 = 3479183) B3479183
theorem B7055707 : Blo 1374006 7055707 := bstep (se 1 (by rfl) ⟨5291780, by rfl⟩ : syracuseStep 7055707 = 10583561) B10583561
theorem B11750615 : Blo 1374006 11750615 := bstep (se 1 (by rfl) ⟨8812961, by rfl⟩ : syracuseStep 11750615 = 17625923) B17625923
theorem B5574683 : Blo 1374006 5574683 := bstep (se 1 (by rfl) ⟨4181012, by rfl⟩ : syracuseStep 5574683 = 8362025) B8362025
theorem B12541139 : Blo 1374006 12541139 := bstep (se 1 (by rfl) ⟨9405854, by rfl⟩ : syracuseStep 12541139 = 18811709) B18811709
theorem B6963083 : Blo 1374006 6963083 := bstep (se 1 (by rfl) ⟨5222312, by rfl⟩ : syracuseStep 6963083 = 10444625) B10444625
theorem B5218303 : Blo 1374006 5218303 := bstep (se 1 (by rfl) ⟨3913727, by rfl⟩ : syracuseStep 5218303 = 7827455) B7827455
theorem B7833743 : Blo 1374006 7833743 := bstep (se 1 (by rfl) ⟨5875307, by rfl⟩ : syracuseStep 7833743 = 11750615) B11750615
theorem B6957737 : Blo 1374006 6957737 := bstep (se 2 (by rfl) ⟨2609151, by rfl⟩ : syracuseStep 6957737 = 5218303) B5218303
theorem B9407609 : Blo 1374006 9407609 := bstep (se 2 (by rfl) ⟨3527853, by rfl⟩ : syracuseStep 9407609 = 7055707) B7055707
theorem B8360759 : Blo 1374006 8360759 := bstep (se 1 (by rfl) ⟨6270569, by rfl⟩ : syracuseStep 8360759 = 12541139) B12541139
theorem B4642055 : Blo 1374006 4642055 := bstep (se 1 (by rfl) ⟨3481541, by rfl⟩ : syracuseStep 4642055 = 6963083) B6963083
theorem B3716455 : Blo 1374006 3716455 := bstep (se 1 (by rfl) ⟨2787341, by rfl⟩ : syracuseStep 3716455 = 5574683) B5574683
theorem B1546303 : Blo 1374006 1546303 := bstep (se 1 (by rfl) ⟨1159727, by rfl⟩ : syracuseStep 1546303 = 2319455) B2319455
theorem B4638491 : Blo 1374006 4638491 := bstep (se 1 (by rfl) ⟨3478868, by rfl⟩ : syracuseStep 4638491 = 6957737) B6957737
theorem B5222495 : Blo 1374006 5222495 := bstep (se 1 (by rfl) ⟨3916871, by rfl⟩ : syracuseStep 5222495 = 7833743) B7833743
theorem B6271739 : Blo 1374006 6271739 := bstep (se 1 (by rfl) ⟨4703804, by rfl⟩ : syracuseStep 6271739 = 9407609) B9407609
theorem B22295357 : Blo 1374006 22295357 := bstep (se 3 (by rfl) ⟨4180379, by rfl⟩ : syracuseStep 22295357 = 8360759) B8360759
theorem B2061737 : Blo 1374006 2061737 := bstep (se 2 (by rfl) ⟨773151, by rfl⟩ : syracuseStep 2061737 = 1546303) B1546303
theorem B3094703 : Blo 1374006 3094703 := bstep (se 1 (by rfl) ⟨2321027, by rfl⟩ : syracuseStep 3094703 = 4642055) B4642055
theorem B4955273 : Blo 1374006 4955273 := bstep (se 2 (by rfl) ⟨1858227, by rfl⟩ : syracuseStep 4955273 = 3716455) B3716455
theorem B3481663 : Blo 1374006 3481663 := bstep (se 1 (by rfl) ⟨2611247, by rfl⟩ : syracuseStep 3481663 = 5222495) B5222495
theorem B3303515 : Blo 1374006 3303515 := bstep (se 1 (by rfl) ⟨2477636, by rfl⟩ : syracuseStep 3303515 = 4955273) B4955273
theorem B4181159 : Blo 1374006 4181159 := bstep (se 1 (by rfl) ⟨3135869, by rfl⟩ : syracuseStep 4181159 = 6271739) B6271739
theorem B14863571 : Blo 1374006 14863571 := bstep (se 1 (by rfl) ⟨11147678, by rfl⟩ : syracuseStep 14863571 = 22295357) B22295357
theorem B3092327 : Blo 1374006 3092327 := bstep (se 1 (by rfl) ⟨2319245, by rfl⟩ : syracuseStep 3092327 = 4638491) B4638491
theorem B1374491 : Blo 1374006 1374491 := bstep (se 1 (by rfl) ⟨1030868, by rfl⟩ : syracuseStep 1374491 = 2061737) B2061737
theorem B2063135 : Blo 1374006 2063135 := bstep (se 1 (by rfl) ⟨1547351, by rfl⟩ : syracuseStep 2063135 = 3094703) B3094703
theorem B2787439 : Blo 1374006 2787439 := bstep (se 1 (by rfl) ⟨2090579, by rfl⟩ : syracuseStep 2787439 = 4181159) B4181159
theorem B8809373 : Blo 1374006 8809373 := bstep (se 3 (by rfl) ⟨1651757, by rfl⟩ : syracuseStep 8809373 = 3303515) B3303515
theorem B9909047 : Blo 1374006 9909047 := bstep (se 1 (by rfl) ⟨7431785, by rfl⟩ : syracuseStep 9909047 = 14863571) B14863571
theorem B2061551 : Blo 1374006 2061551 := bstep (se 1 (by rfl) ⟨1546163, by rfl⟩ : syracuseStep 2061551 = 3092327) B3092327
theorem B4642217 : Blo 1374006 4642217 := bstep (se 2 (by rfl) ⟨1740831, by rfl⟩ : syracuseStep 4642217 = 3481663) B3481663
theorem B1375423 : Blo 1374006 1375423 := bstep (se 1 (by rfl) ⟨1031567, by rfl⟩ : syracuseStep 1375423 = 2063135) B2063135
theorem B6606031 : Blo 1374006 6606031 := bstep (se 1 (by rfl) ⟨4954523, by rfl⟩ : syracuseStep 6606031 = 9909047) B9909047
theorem B3716585 : Blo 1374006 3716585 := bstep (se 2 (by rfl) ⟨1393719, by rfl⟩ : syracuseStep 3716585 = 2787439) B2787439
theorem B1374367 : Blo 1374006 1374367 := bstep (se 1 (by rfl) ⟨1030775, by rfl⟩ : syracuseStep 1374367 = 2061551) B2061551
theorem B3094811 : Blo 1374006 3094811 := bstep (se 1 (by rfl) ⟨2321108, by rfl⟩ : syracuseStep 3094811 = 4642217) B4642217
theorem B5872915 : Blo 1374006 5872915 := bstep (se 1 (by rfl) ⟨4404686, by rfl⟩ : syracuseStep 5872915 = 8809373) B8809373
theorem B8808041 : Blo 1374006 8808041 := bstep (se 2 (by rfl) ⟨3303015, by rfl⟩ : syracuseStep 8808041 = 6606031) B6606031
theorem B2477723 : Blo 1374006 2477723 := bstep (se 1 (by rfl) ⟨1858292, by rfl⟩ : syracuseStep 2477723 = 3716585) B3716585
theorem B2063207 : Blo 1374006 2063207 := bstep (se 1 (by rfl) ⟨1547405, by rfl⟩ : syracuseStep 2063207 = 3094811) B3094811
theorem B7830553 : Blo 1374006 7830553 := bstep (se 2 (by rfl) ⟨2936457, by rfl⟩ : syracuseStep 7830553 = 5872915) B5872915
theorem B10440737 : Blo 1374006 10440737 := bstep (se 2 (by rfl) ⟨3915276, by rfl⟩ : syracuseStep 10440737 = 7830553) B7830553
theorem B6607261 : Blo 1374006 6607261 := bstep (se 3 (by rfl) ⟨1238861, by rfl⟩ : syracuseStep 6607261 = 2477723) B2477723
theorem B5872027 : Blo 1374006 5872027 := bstep (se 1 (by rfl) ⟨4404020, by rfl⟩ : syracuseStep 5872027 = 8808041) B8808041
theorem B1375471 : Blo 1374006 1375471 := bstep (se 1 (by rfl) ⟨1031603, by rfl⟩ : syracuseStep 1375471 = 2063207) B2063207
theorem B8809681 : Blo 1374006 8809681 := bstep (se 2 (by rfl) ⟨3303630, by rfl⟩ : syracuseStep 8809681 = 6607261) B6607261
theorem B6960491 : Blo 1374006 6960491 := bstep (se 1 (by rfl) ⟨5220368, by rfl⟩ : syracuseStep 6960491 = 10440737) B10440737
theorem B7829369 : Blo 1374006 7829369 := bstep (se 2 (by rfl) ⟨2936013, by rfl⟩ : syracuseStep 7829369 = 5872027) B5872027
theorem B5219579 : Blo 1374006 5219579 := bstep (se 1 (by rfl) ⟨3914684, by rfl⟩ : syracuseStep 5219579 = 7829369) B7829369
theorem B4640327 : Blo 1374006 4640327 := bstep (se 1 (by rfl) ⟨3480245, by rfl⟩ : syracuseStep 4640327 = 6960491) B6960491
theorem B11746241 : Blo 1374006 11746241 := bstep (se 2 (by rfl) ⟨4404840, by rfl⟩ : syracuseStep 11746241 = 8809681) B8809681
theorem B3093551 : Blo 1374006 3093551 := bstep (se 1 (by rfl) ⟨2320163, by rfl⟩ : syracuseStep 3093551 = 4640327) B4640327
theorem B3479719 : Blo 1374006 3479719 := bstep (se 1 (by rfl) ⟨2609789, by rfl⟩ : syracuseStep 3479719 = 5219579) B5219579
theorem B7830827 : Blo 1374006 7830827 := bstep (se 1 (by rfl) ⟨5873120, by rfl⟩ : syracuseStep 7830827 = 11746241) B11746241
theorem B5220551 : Blo 1374006 5220551 := bstep (se 1 (by rfl) ⟨3915413, by rfl⟩ : syracuseStep 5220551 = 7830827) B7830827
theorem B4639625 : Blo 1374006 4639625 := bstep (se 2 (by rfl) ⟨1739859, by rfl⟩ : syracuseStep 4639625 = 3479719) B3479719
theorem B2062367 : Blo 1374006 2062367 := bstep (se 1 (by rfl) ⟨1546775, by rfl⟩ : syracuseStep 2062367 = 3093551) B3093551
theorem B3093083 : Blo 1374006 3093083 := bstep (se 1 (by rfl) ⟨2319812, by rfl⟩ : syracuseStep 3093083 = 4639625) B4639625
theorem B1374911 : Blo 1374006 1374911 := bstep (se 1 (by rfl) ⟨1031183, by rfl⟩ : syracuseStep 1374911 = 2062367) B2062367
theorem B3480367 : Blo 1374006 3480367 := bstep (se 1 (by rfl) ⟨2610275, by rfl⟩ : syracuseStep 3480367 = 5220551) B5220551
theorem B4640489 : Blo 1374006 4640489 := bstep (se 2 (by rfl) ⟨1740183, by rfl⟩ : syracuseStep 4640489 = 3480367) B3480367
theorem B2062055 : Blo 1374006 2062055 := bstep (se 1 (by rfl) ⟨1546541, by rfl⟩ : syracuseStep 2062055 = 3093083) B3093083
theorem B3093659 : Blo 1374006 3093659 := bstep (se 1 (by rfl) ⟨2320244, by rfl⟩ : syracuseStep 3093659 = 4640489) B4640489
theorem B1374703 : Blo 1374006 1374703 := bstep (se 1 (by rfl) ⟨1031027, by rfl⟩ : syracuseStep 1374703 = 2062055) B2062055
theorem B2062439 : Blo 1374006 2062439 := bstep (se 1 (by rfl) ⟨1546829, by rfl⟩ : syracuseStep 2062439 = 3093659) B3093659
theorem B1374959 : Blo 1374006 1374959 := bstep (se 1 (by rfl) ⟨1031219, by rfl⟩ : syracuseStep 1374959 = 2062439) B2062439

theorem C0 (j : ℕ) (h1 : 343501 ≤ j) (h2 : j ≤ 343875) : Blo 1374006 (4 * j + 3) := by
  interval_cases j
  · exact B1374007
  · exact B1374011
  · exact B1374015
  · exact B1374019
  · exact B1374023
  · exact B1374027
  · exact B1374031
  · exact B1374035
  · exact B1374039
  · exact B1374043
  · exact B1374047
  · exact B1374051
  · exact B1374055
  · exact B1374059
  · exact B1374063
  · exact B1374067
  · exact B1374071
  · exact B1374075
  · exact B1374079
  · exact B1374083
  · exact B1374087
  · exact B1374091
  · exact B1374095
  · exact B1374099
  · exact B1374103
  · exact B1374107
  · exact B1374111
  · exact B1374115
  · exact B1374119
  · exact B1374123
  · exact B1374127
  · exact B1374131
  · exact B1374135
  · exact B1374139
  · exact B1374143
  · exact B1374147
  · exact B1374151
  · exact B1374155
  · exact B1374159
  · exact B1374163
  · exact B1374167
  · exact B1374171
  · exact B1374175
  · exact B1374179
  · exact B1374183
  · exact B1374187
  · exact B1374191
  · exact B1374195
  · exact B1374199
  · exact B1374203
  · exact B1374207
  · exact B1374211
  · exact B1374215
  · exact B1374219
  · exact B1374223
  · exact B1374227
  · exact B1374231
  · exact B1374235
  · exact B1374239
  · exact B1374243
  · exact B1374247
  · exact B1374251
  · exact B1374255
  · exact B1374259
  · exact B1374263
  · exact B1374267
  · exact B1374271
  · exact B1374275
  · exact B1374279
  · exact B1374283
  · exact B1374287
  · exact B1374291
  · exact B1374295
  · exact B1374299
  · exact B1374303
  · exact B1374307
  · exact B1374311
  · exact B1374315
  · exact B1374319
  · exact B1374323
  · exact B1374327
  · exact B1374331
  · exact B1374335
  · exact B1374339
  · exact B1374343
  · exact B1374347
  · exact B1374351
  · exact B1374355
  · exact B1374359
  · exact B1374363
  · exact B1374367
  · exact B1374371
  · exact B1374375
  · exact B1374379
  · exact B1374383
  · exact B1374387
  · exact B1374391
  · exact B1374395
  · exact B1374399
  · exact B1374403
  · exact B1374407
  · exact B1374411
  · exact B1374415
  · exact B1374419
  · exact B1374423
  · exact B1374427
  · exact B1374431
  · exact B1374435
  · exact B1374439
  · exact B1374443
  · exact B1374447
  · exact B1374451
  · exact B1374455
  · exact B1374459
  · exact B1374463
  · exact B1374467
  · exact B1374471
  · exact B1374475
  · exact B1374479
  · exact B1374483
  · exact B1374487
  · exact B1374491
  · exact B1374495
  · exact B1374499
  · exact B1374503
  · exact B1374507
  · exact B1374511
  · exact B1374515
  · exact B1374519
  · exact B1374523
  · exact B1374527
  · exact B1374531
  · exact B1374535
  · exact B1374539
  · exact B1374543
  · exact B1374547
  · exact B1374551
  · exact B1374555
  · exact B1374559
  · exact B1374563
  · exact B1374567
  · exact B1374571
  · exact B1374575
  · exact B1374579
  · exact B1374583
  · exact B1374587
  · exact B1374591
  · exact B1374595
  · exact B1374599
  · exact B1374603
  · exact B1374607
  · exact B1374611
  · exact B1374615
  · exact B1374619
  · exact B1374623
  · exact B1374627
  · exact B1374631
  · exact B1374635
  · exact B1374639
  · exact B1374643
  · exact B1374647
  · exact B1374651
  · exact B1374655
  · exact B1374659
  · exact B1374663
  · exact B1374667
  · exact B1374671
  · exact B1374675
  · exact B1374679
  · exact B1374683
  · exact B1374687
  · exact B1374691
  · exact B1374695
  · exact B1374699
  · exact B1374703
  · exact B1374707
  · exact B1374711
  · exact B1374715
  · exact B1374719
  · exact B1374723
  · exact B1374727
  · exact B1374731
  · exact B1374735
  · exact B1374739
  · exact B1374743
  · exact B1374747
  · exact B1374751
  · exact B1374755
  · exact B1374759
  · exact B1374763
  · exact B1374767
  · exact B1374771
  · exact B1374775
  · exact B1374779
  · exact B1374783
  · exact B1374787
  · exact B1374791
  · exact B1374795
  · exact B1374799
  · exact B1374803
  · exact B1374807
  · exact B1374811
  · exact B1374815
  · exact B1374819
  · exact B1374823
  · exact B1374827
  · exact B1374831
  · exact B1374835
  · exact B1374839
  · exact B1374843
  · exact B1374847
  · exact B1374851
  · exact B1374855
  · exact B1374859
  · exact B1374863
  · exact B1374867
  · exact B1374871
  · exact B1374875
  · exact B1374879
  · exact B1374883
  · exact B1374887
  · exact B1374891
  · exact B1374895
  · exact B1374899
  · exact B1374903
  · exact B1374907
  · exact B1374911
  · exact B1374915
  · exact B1374919
  · exact B1374923
  · exact B1374927
  · exact B1374931
  · exact B1374935
  · exact B1374939
  · exact B1374943
  · exact B1374947
  · exact B1374951
  · exact B1374955
  · exact B1374959
  · exact B1374963
  · exact B1374967
  · exact B1374971
  · exact B1374975
  · exact B1374979
  · exact B1374983
  · exact B1374987
  · exact B1374991
  · exact B1374995
  · exact B1374999
  · exact B1375003
  · exact B1375007
  · exact B1375011
  · exact B1375015
  · exact B1375019
  · exact B1375023
  · exact B1375027
  · exact B1375031
  · exact B1375035
  · exact B1375039
  · exact B1375043
  · exact B1375047
  · exact B1375051
  · exact B1375055
  · exact B1375059
  · exact B1375063
  · exact B1375067
  · exact B1375071
  · exact B1375075
  · exact B1375079
  · exact B1375083
  · exact B1375087
  · exact B1375091
  · exact B1375095
  · exact B1375099
  · exact B1375103
  · exact B1375107
  · exact B1375111
  · exact B1375115
  · exact B1375119
  · exact B1375123
  · exact B1375127
  · exact B1375131
  · exact B1375135
  · exact B1375139
  · exact B1375143
  · exact B1375147
  · exact B1375151
  · exact B1375155
  · exact B1375159
  · exact B1375163
  · exact B1375167
  · exact B1375171
  · exact B1375175
  · exact B1375179
  · exact B1375183
  · exact B1375187
  · exact B1375191
  · exact B1375195
  · exact B1375199
  · exact B1375203
  · exact B1375207
  · exact B1375211
  · exact B1375215
  · exact B1375219
  · exact B1375223
  · exact B1375227
  · exact B1375231
  · exact B1375235
  · exact B1375239
  · exact B1375243
  · exact B1375247
  · exact B1375251
  · exact B1375255
  · exact B1375259
  · exact B1375263
  · exact B1375267
  · exact B1375271
  · exact B1375275
  · exact B1375279
  · exact B1375283
  · exact B1375287
  · exact B1375291
  · exact B1375295
  · exact B1375299
  · exact B1375303
  · exact B1375307
  · exact B1375311
  · exact B1375315
  · exact B1375319
  · exact B1375323
  · exact B1375327
  · exact B1375331
  · exact B1375335
  · exact B1375339
  · exact B1375343
  · exact B1375347
  · exact B1375351
  · exact B1375355
  · exact B1375359
  · exact B1375363
  · exact B1375367
  · exact B1375371
  · exact B1375375
  · exact B1375379
  · exact B1375383
  · exact B1375387
  · exact B1375391
  · exact B1375395
  · exact B1375399
  · exact B1375403
  · exact B1375407
  · exact B1375411
  · exact B1375415
  · exact B1375419
  · exact B1375423
  · exact B1375427
  · exact B1375431
  · exact B1375435
  · exact B1375439
  · exact B1375443
  · exact B1375447
  · exact B1375451
  · exact B1375455
  · exact B1375459
  · exact B1375463
  · exact B1375467
  · exact B1375471
  · exact B1375475
  · exact B1375479
  · exact B1375483
  · exact B1375487
  · exact B1375491
  · exact B1375495
  · exact B1375499
  · exact B1375503

theorem solution (m : ℕ) (hlo : 1374006 ≤ m) (hhi : m ≤ 1375506) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 343501 ≤ j := by omega
    have hj2 : j ≤ 343875 := by omega
    have hb : Blo 1374006 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
