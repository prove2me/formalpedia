-- Prove2me | solution 1 for syracuse_descends_range_1421530_1423530
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:41:34.909116+00:00
-- url     : https://prove2.me/submissions/9e4db06e-9a2e-4187-8690-c8dc56257e45

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


theorem B3416077 : Blo 1421530 3416077 := bbase (se 3 (by rfl) ⟨640514, by rfl⟩ : syracuseStep 3416077 = 1281029) (by norm_num)
theorem B2400293 : Blo 1421530 2400293 := bbase (se 4 (by rfl) ⟨225027, by rfl⟩ : syracuseStep 2400293 = 450055) (by norm_num)
theorem B16425109 : Blo 1421530 16425109 := bbase (se 6 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 16425109 = 769927) (by norm_num)
theorem B9117845 : Blo 1421530 9117845 := bbase (se 6 (by rfl) ⟨213699, by rfl⟩ : syracuseStep 9117845 = 427399) (by norm_num)
theorem B2277533 : Blo 1421530 2277533 := bbase (se 3 (by rfl) ⟨427037, by rfl⟩ : syracuseStep 2277533 = 854075) (by norm_num)
theorem B2400421 : Blo 1421530 2400421 := bbase (se 4 (by rfl) ⟨225039, by rfl⟩ : syracuseStep 2400421 = 450079) (by norm_num)
theorem B6832309 : Blo 1421530 6832309 := bbase (se 5 (by rfl) ⟨320264, by rfl⟩ : syracuseStep 6832309 = 640529) (by norm_num)
theorem B3416309 : Blo 1421530 3416309 := bbase (se 5 (by rfl) ⟨160139, by rfl⟩ : syracuseStep 3416309 = 320279) (by norm_num)
theorem B2400509 : Blo 1421530 2400509 := bbase (se 3 (by rfl) ⟨450095, by rfl⟩ : syracuseStep 2400509 = 900191) (by norm_num)
theorem B2564365 : Blo 1421530 2564365 := bbase (se 3 (by rfl) ⟨480818, by rfl⟩ : syracuseStep 2564365 = 961637) (by norm_num)
theorem B7201061 : Blo 1421530 7201061 := bbase (se 4 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 7201061 = 1350199) (by norm_num)
theorem B2466133 : Blo 1421530 2466133 := bbase (se 10 (by rfl) ⟨3612, by rfl⟩ : syracuseStep 2466133 = 7225) (by norm_num)
theorem B3039581 : Blo 1421530 3039581 := bbase (se 3 (by rfl) ⟨569921, by rfl⟩ : syracuseStep 3039581 = 1139843) (by norm_num)
theorem B4800869 : Blo 1421530 4800869 := bbase (se 4 (by rfl) ⟨450081, by rfl⟩ : syracuseStep 4800869 = 900163) (by norm_num)
theorem B9732469 : Blo 1421530 9732469 := bbase (se 5 (by rfl) ⟨456209, by rfl⟩ : syracuseStep 9732469 = 912419) (by norm_num)
theorem B2277757 : Blo 1421530 2277757 := bbase (se 3 (by rfl) ⟨427079, by rfl⟩ : syracuseStep 2277757 = 854159) (by norm_num)
theorem B2400637 : Blo 1421530 2400637 := bbase (se 3 (by rfl) ⟨450119, by rfl⟩ : syracuseStep 2400637 = 900239) (by norm_num)
theorem B10797461 : Blo 1421530 10797461 := bbase (se 6 (by rfl) ⟨253065, by rfl⟩ : syracuseStep 10797461 = 506131) (by norm_num)
theorem B2736533 : Blo 1421530 2736533 := bbase (se 6 (by rfl) ⟨64137, by rfl⟩ : syracuseStep 2736533 = 128275) (by norm_num)
theorem B3416501 : Blo 1421530 3416501 := bbase (se 5 (by rfl) ⟨160148, by rfl⟩ : syracuseStep 3416501 = 320297) (by norm_num)
theorem B2277821 : Blo 1421530 2277821 := bbase (se 3 (by rfl) ⟨427091, by rfl⟩ : syracuseStep 2277821 = 854183) (by norm_num)
theorem B2400725 : Blo 1421530 2400725 := bbase (se 7 (by rfl) ⟨28133, by rfl⟩ : syracuseStep 2400725 = 56267) (by norm_num)
theorem B12157397 : Blo 1421530 12157397 := bbase (se 7 (by rfl) ⟨142469, by rfl⟩ : syracuseStep 12157397 = 284939) (by norm_num)
theorem B3039725 : Blo 1421530 3039725 := bbase (se 3 (by rfl) ⟨569948, by rfl⟩ : syracuseStep 3039725 = 1139897) (by norm_num)
theorem B14606837 : Blo 1421530 14606837 := bbase (se 5 (by rfl) ⟨684695, by rfl⟩ : syracuseStep 14606837 = 1369391) (by norm_num)
theorem B2433557 : Blo 1421530 2433557 := bbase (se 6 (by rfl) ⟨57036, by rfl⟩ : syracuseStep 2433557 = 114073) (by norm_num)
theorem B2163245 : Blo 1421530 2163245 := bbase (se 3 (by rfl) ⟨405608, by rfl⟩ : syracuseStep 2163245 = 811217) (by norm_num)
theorem B2277949 : Blo 1421530 2277949 := bbase (se 3 (by rfl) ⟨427115, by rfl⟩ : syracuseStep 2277949 = 854231) (by norm_num)
theorem B2400853 : Blo 1421530 2400853 := bbase (se 8 (by rfl) ⟨14067, by rfl⟩ : syracuseStep 2400853 = 28135) (by norm_num)
theorem B21897877 : Blo 1421530 21897877 := bbase (se 6 (by rfl) ⟨513231, by rfl⟩ : syracuseStep 21897877 = 1026463) (by norm_num)
theorem B2400941 : Blo 1421530 2400941 := bbase (se 3 (by rfl) ⟨450176, by rfl⟩ : syracuseStep 2400941 = 900353) (by norm_num)
theorem B3416789 : Blo 1421530 3416789 := bbase (se 7 (by rfl) ⟨40040, by rfl⟩ : syracuseStep 3416789 = 80081) (by norm_num)
theorem B7217909 : Blo 1421530 7217909 := bbase (se 5 (by rfl) ⟨338339, by rfl⟩ : syracuseStep 7217909 = 676679) (by norm_num)
theorem B4801301 : Blo 1421530 4801301 := bbase (se 6 (by rfl) ⟨112530, by rfl⟩ : syracuseStep 4801301 = 225061) (by norm_num)
theorem B2564885 : Blo 1421530 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B2401069 : Blo 1421530 2401069 := bbase (se 3 (by rfl) ⟨450200, by rfl⟩ : syracuseStep 2401069 = 900401) (by norm_num)
theorem B4809557 : Blo 1421530 4809557 := bbase (se 9 (by rfl) ⟨14090, by rfl⟩ : syracuseStep 4809557 = 28181) (by norm_num)
theorem B3040085 : Blo 1421530 3040085 := bbase (se 9 (by rfl) ⟨8906, by rfl⟩ : syracuseStep 3040085 = 17813) (by norm_num)
theorem B2401157 : Blo 1421530 2401157 := bbase (se 4 (by rfl) ⟨225108, by rfl⟩ : syracuseStep 2401157 = 450217) (by norm_num)
theorem B2597789 : Blo 1421530 2597789 := bbase (se 3 (by rfl) ⟨487085, by rfl⟩ : syracuseStep 2597789 = 974171) (by norm_num)
theorem B2565029 : Blo 1421530 2565029 := bbase (se 4 (by rfl) ⟨240471, by rfl⟩ : syracuseStep 2565029 = 480943) (by norm_num)
theorem B2024365 : Blo 1421530 2024365 := bbase (se 3 (by rfl) ⟨379568, by rfl⟩ : syracuseStep 2024365 = 759137) (by norm_num)
theorem B1442809 : Blo 1421530 1442809 := bbase (se 2 (by rfl) ⟨541053, by rfl⟩ : syracuseStep 1442809 = 1082107) (by norm_num)
theorem B2401285 : Blo 1421530 2401285 := bbase (se 4 (by rfl) ⟨225120, by rfl⟩ : syracuseStep 2401285 = 450241) (by norm_num)
theorem B2311237 : Blo 1421530 2311237 := bbase (se 4 (by rfl) ⟨216678, by rfl⟩ : syracuseStep 2311237 = 433357) (by norm_num)
theorem B2401373 : Blo 1421530 2401373 := bbase (se 3 (by rfl) ⟨450257, by rfl⟩ : syracuseStep 2401373 = 900515) (by norm_num)
theorem B2565245 : Blo 1421530 2565245 := bbase (se 3 (by rfl) ⟨480983, by rfl⟩ : syracuseStep 2565245 = 961967) (by norm_num)
theorem B3245197 : Blo 1421530 3245197 := bbase (se 3 (by rfl) ⟨608474, by rfl⟩ : syracuseStep 3245197 = 1216949) (by norm_num)
theorem B5129365 : Blo 1421530 5129365 := bbase (se 6 (by rfl) ⟨120219, by rfl⟩ : syracuseStep 5129365 = 240439) (by norm_num)
theorem B2884781 : Blo 1421530 2884781 := bbase (se 3 (by rfl) ⟨540896, by rfl⟩ : syracuseStep 2884781 = 1081793) (by norm_num)
theorem B7300277 : Blo 1421530 7300277 := bbase (se 5 (by rfl) ⟨342200, by rfl⟩ : syracuseStep 7300277 = 684401) (by norm_num)
theorem B4048069 : Blo 1421530 4048069 := bbase (se 4 (by rfl) ⟨379506, by rfl⟩ : syracuseStep 4048069 = 759013) (by norm_num)
theorem B4801733 : Blo 1421530 4801733 := bbase (se 4 (by rfl) ⟨450162, by rfl⟩ : syracuseStep 4801733 = 900325) (by norm_num)
theorem B2401501 : Blo 1421530 2401501 := bbase (se 3 (by rfl) ⟨450281, by rfl⟩ : syracuseStep 2401501 = 900563) (by norm_num)
theorem B2401589 : Blo 1421530 2401589 := bbase (se 5 (by rfl) ⟨112574, by rfl⟩ : syracuseStep 2401589 = 225149) (by norm_num)
theorem B10257749 : Blo 1421530 10257749 := bbase (se 12 (by rfl) ⟨3756, by rfl⟩ : syracuseStep 10257749 = 7513) (by norm_num)
theorem B2401717 : Blo 1421530 2401717 := bbase (se 5 (by rfl) ⟨112580, by rfl⟩ : syracuseStep 2401717 = 225161) (by norm_num)
theorem B5400053 : Blo 1421530 5400053 := bbase (se 5 (by rfl) ⟨253127, by rfl⟩ : syracuseStep 5400053 = 506255) (by norm_num)
theorem B2024957 : Blo 1421530 2024957 := bbase (se 3 (by rfl) ⟨379679, by rfl⟩ : syracuseStep 2024957 = 759359) (by norm_num)
theorem B2401805 : Blo 1421530 2401805 := bbase (se 3 (by rfl) ⟨450338, by rfl⟩ : syracuseStep 2401805 = 900677) (by norm_num)
theorem B7202357 : Blo 1421530 7202357 := bbase (se 5 (by rfl) ⟨337610, by rfl⟩ : syracuseStep 7202357 = 675221) (by norm_num)
theorem B2025037 : Blo 1421530 2025037 := bbase (se 3 (by rfl) ⟨379694, by rfl⟩ : syracuseStep 2025037 = 759389) (by norm_num)
theorem B4802165 : Blo 1421530 4802165 := bbase (se 5 (by rfl) ⟨225101, by rfl⟩ : syracuseStep 4802165 = 450203) (by norm_num)
theorem B2401933 : Blo 1421530 2401933 := bbase (se 3 (by rfl) ⟨450362, by rfl⟩ : syracuseStep 2401933 = 900725) (by norm_num)
theorem B2025157 : Blo 1421530 2025157 := bbase (se 4 (by rfl) ⟨189858, by rfl⟩ : syracuseStep 2025157 = 379717) (by norm_num)
theorem B2402021 : Blo 1421530 2402021 := bbase (se 4 (by rfl) ⟨225189, by rfl⟩ : syracuseStep 2402021 = 450379) (by norm_num)
theorem B2279173 : Blo 1421530 2279173 := bbase (se 4 (by rfl) ⟨213672, by rfl⟩ : syracuseStep 2279173 = 427345) (by norm_num)
theorem B1599241 : Blo 1421530 1599241 := bbase (se 2 (by rfl) ⟨599715, by rfl⟩ : syracuseStep 1599241 = 1199431) (by norm_num)
theorem B5400341 : Blo 1421530 5400341 := bbase (se 6 (by rfl) ⟨126570, by rfl⟩ : syracuseStep 5400341 = 253141) (by norm_num)
theorem B2025253 : Blo 1421530 2025253 := bbase (se 4 (by rfl) ⟨189867, by rfl⟩ : syracuseStep 2025253 = 379735) (by norm_num)
theorem B1599277 : Blo 1421530 1599277 := bbase (se 3 (by rfl) ⟨299864, by rfl⟩ : syracuseStep 1599277 = 599729) (by norm_num)
theorem B1599313 : Blo 1421530 1599313 := bbase (se 2 (by rfl) ⟨599742, by rfl⟩ : syracuseStep 1599313 = 1199485) (by norm_num)
theorem B2402149 : Blo 1421530 2402149 := bbase (se 4 (by rfl) ⟨225201, by rfl⟩ : syracuseStep 2402149 = 450403) (by norm_num)
theorem B1599349 : Blo 1421530 1599349 := bbase (se 5 (by rfl) ⟨74969, by rfl⟩ : syracuseStep 1599349 = 149939) (by norm_num)
theorem B1599385 : Blo 1421530 1599385 := bbase (se 2 (by rfl) ⟨599769, by rfl⟩ : syracuseStep 1599385 = 1199539) (by norm_num)
theorem B3598253 : Blo 1421530 3598253 := bbase (se 3 (by rfl) ⟨674672, by rfl⟩ : syracuseStep 3598253 = 1349345) (by norm_num)
theorem B2467757 : Blo 1421530 2467757 := bbase (se 3 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 2467757 = 925409) (by norm_num)
theorem B1599421 : Blo 1421530 1599421 := bbase (se 3 (by rfl) ⟨299891, by rfl⟩ : syracuseStep 1599421 = 599783) (by norm_num)
theorem B1599457 : Blo 1421530 1599457 := bbase (se 2 (by rfl) ⟨599796, by rfl⟩ : syracuseStep 1599457 = 1199593) (by norm_num)
theorem B3164141 : Blo 1421530 3164141 := bbase (se 3 (by rfl) ⟨593276, by rfl⟩ : syracuseStep 3164141 = 1186553) (by norm_num)
theorem B1599493 : Blo 1421530 1599493 := bbase (se 4 (by rfl) ⟨149952, by rfl⟩ : syracuseStep 1599493 = 299905) (by norm_num)
theorem B4802597 : Blo 1421530 4802597 := bbase (se 4 (by rfl) ⟨450243, by rfl⟩ : syracuseStep 4802597 = 900487) (by norm_num)
theorem B1599529 : Blo 1421530 1599529 := bbase (se 2 (by rfl) ⟨599823, by rfl⟩ : syracuseStep 1599529 = 1199647) (by norm_num)
theorem B1599565 : Blo 1421530 1599565 := bbase (se 3 (by rfl) ⟨299918, by rfl⟩ : syracuseStep 1599565 = 599837) (by norm_num)
theorem B3598445 : Blo 1421530 3598445 := bbase (se 3 (by rfl) ⟨674708, by rfl⟩ : syracuseStep 3598445 = 1349417) (by norm_num)
theorem B1599601 : Blo 1421530 1599601 := bbase (se 2 (by rfl) ⟨599850, by rfl⟩ : syracuseStep 1599601 = 1199701) (by norm_num)
theorem B9242741 : Blo 1421530 9242741 := bbase (se 5 (by rfl) ⟨433253, by rfl⟩ : syracuseStep 9242741 = 866507) (by norm_num)
theorem B1599637 : Blo 1421530 1599637 := bbase (se 6 (by rfl) ⟨37491, by rfl⟩ : syracuseStep 1599637 = 74983) (by norm_num)
theorem B7301285 : Blo 1421530 7301285 := bbase (se 4 (by rfl) ⟨684495, by rfl⟩ : syracuseStep 7301285 = 1368991) (by norm_num)
theorem B1599673 : Blo 1421530 1599673 := bbase (se 2 (by rfl) ⟨599877, by rfl⟩ : syracuseStep 1599673 = 1199755) (by norm_num)
theorem B1599709 : Blo 1421530 1599709 := bbase (se 3 (by rfl) ⟨299945, by rfl⟩ : syracuseStep 1599709 = 599891) (by norm_num)
theorem B1599745 : Blo 1421530 1599745 := bbase (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) (by norm_num)
theorem B2025749 : Blo 1421530 2025749 := bbase (se 6 (by rfl) ⟨47478, by rfl⟩ : syracuseStep 2025749 = 94957) (by norm_num)
theorem B1599781 : Blo 1421530 1599781 := bbase (se 4 (by rfl) ⟨149979, by rfl⟩ : syracuseStep 1599781 = 299959) (by norm_num)
theorem B1599817 : Blo 1421530 1599817 := bbase (se 2 (by rfl) ⟨599931, by rfl⟩ : syracuseStep 1599817 = 1199863) (by norm_num)
theorem B2132309 : Blo 1421530 2132309 := bbase (se 10 (by rfl) ⟨3123, by rfl⟩ : syracuseStep 2132309 = 6247) (by norm_num)
theorem B2132333 : Blo 1421530 2132333 := bbase (se 3 (by rfl) ⟨399812, by rfl⟩ : syracuseStep 2132333 = 799625) (by norm_num)
theorem B1599853 : Blo 1421530 1599853 := bbase (se 3 (by rfl) ⟨299972, by rfl⟩ : syracuseStep 1599853 = 599945) (by norm_num)
theorem B2132357 : Blo 1421530 2132357 := bbase (se 4 (by rfl) ⟨199908, by rfl⟩ : syracuseStep 2132357 = 399817) (by norm_num)
theorem B1599889 : Blo 1421530 1599889 := bbase (se 2 (by rfl) ⟨599958, by rfl⟩ : syracuseStep 1599889 = 1199917) (by norm_num)
theorem B2132381 : Blo 1421530 2132381 := bbase (se 3 (by rfl) ⟨399821, by rfl⟩ : syracuseStep 2132381 = 799643) (by norm_num)
theorem B2279845 : Blo 1421530 2279845 := bbase (se 4 (by rfl) ⟨213735, by rfl⟩ : syracuseStep 2279845 = 427471) (by norm_num)
theorem B2132405 : Blo 1421530 2132405 := bbase (se 5 (by rfl) ⟨99956, by rfl⟩ : syracuseStep 2132405 = 199913) (by norm_num)
theorem B1599925 : Blo 1421530 1599925 := bbase (se 5 (by rfl) ⟨74996, by rfl⟩ : syracuseStep 1599925 = 149993) (by norm_num)
theorem B3598789 : Blo 1421530 3598789 := bbase (se 4 (by rfl) ⟨337386, by rfl⟩ : syracuseStep 3598789 = 674773) (by norm_num)
theorem B4327877 : Blo 1421530 4327877 := bbase (se 4 (by rfl) ⟨405738, by rfl⟩ : syracuseStep 4327877 = 811477) (by norm_num)
theorem B2132429 : Blo 1421530 2132429 := bbase (se 3 (by rfl) ⟨399830, by rfl⟩ : syracuseStep 2132429 = 799661) (by norm_num)
theorem B4803029 : Blo 1421530 4803029 := bbase (se 7 (by rfl) ⟨56285, by rfl⟩ : syracuseStep 4803029 = 112571) (by norm_num)
theorem B1599961 : Blo 1421530 1599961 := bbase (se 2 (by rfl) ⟨599985, by rfl⟩ : syracuseStep 1599961 = 1199971) (by norm_num)
theorem B2132453 : Blo 1421530 2132453 := bbase (se 4 (by rfl) ⟨199917, by rfl⟩ : syracuseStep 2132453 = 399835) (by norm_num)
theorem B2132477 : Blo 1421530 2132477 := bbase (se 3 (by rfl) ⟨399839, by rfl⟩ : syracuseStep 2132477 = 799679) (by norm_num)
theorem B1599997 : Blo 1421530 1599997 := bbase (se 3 (by rfl) ⟨299999, by rfl⟩ : syracuseStep 1599997 = 599999) (by norm_num)
theorem B2132501 : Blo 1421530 2132501 := bbase (se 6 (by rfl) ⟨49980, by rfl⟩ : syracuseStep 2132501 = 99961) (by norm_num)
theorem B1600033 : Blo 1421530 1600033 := bbase (se 2 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 1600033 = 1200025) (by norm_num)
theorem B3648037 : Blo 1421530 3648037 := bbase (se 4 (by rfl) ⟨342003, by rfl⟩ : syracuseStep 3648037 = 684007) (by norm_num)
theorem B2132525 : Blo 1421530 2132525 := bbase (se 3 (by rfl) ⟨399848, by rfl⟩ : syracuseStep 2132525 = 799697) (by norm_num)
theorem B3598901 : Blo 1421530 3598901 := bbase (se 5 (by rfl) ⟨168698, by rfl⟩ : syracuseStep 3598901 = 337397) (by norm_num)
theorem B2132549 : Blo 1421530 2132549 := bbase (se 4 (by rfl) ⟨199926, by rfl⟩ : syracuseStep 2132549 = 399853) (by norm_num)
theorem B1600069 : Blo 1421530 1600069 := bbase (se 4 (by rfl) ⟨150006, by rfl⟩ : syracuseStep 1600069 = 300013) (by norm_num)
theorem B2132573 : Blo 1421530 2132573 := bbase (se 3 (by rfl) ⟨399857, by rfl⟩ : syracuseStep 2132573 = 799715) (by norm_num)
theorem B1600105 : Blo 1421530 1600105 := bbase (se 2 (by rfl) ⟨600039, by rfl⟩ : syracuseStep 1600105 = 1200079) (by norm_num)
theorem B2132597 : Blo 1421530 2132597 := bbase (se 5 (by rfl) ⟨99965, by rfl⟩ : syracuseStep 2132597 = 199931) (by norm_num)
theorem B2132621 : Blo 1421530 2132621 := bbase (se 3 (by rfl) ⟨399866, by rfl⟩ : syracuseStep 2132621 = 799733) (by norm_num)
theorem B1600141 : Blo 1421530 1600141 := bbase (se 3 (by rfl) ⟨300026, by rfl⟩ : syracuseStep 1600141 = 600053) (by norm_num)
theorem B2132645 : Blo 1421530 2132645 := bbase (se 4 (by rfl) ⟨199935, by rfl⟩ : syracuseStep 2132645 = 399871) (by norm_num)
theorem B1600177 : Blo 1421530 1600177 := bbase (se 2 (by rfl) ⟨600066, by rfl⟩ : syracuseStep 1600177 = 1200133) (by norm_num)
theorem B2132669 : Blo 1421530 2132669 := bbase (se 3 (by rfl) ⟨399875, by rfl⟩ : syracuseStep 2132669 = 799751) (by norm_num)
theorem B2132693 : Blo 1421530 2132693 := bbase (se 7 (by rfl) ⟨24992, by rfl⟩ : syracuseStep 2132693 = 49985) (by norm_num)
theorem B1600213 : Blo 1421530 1600213 := bbase (se 7 (by rfl) ⟨18752, by rfl⟩ : syracuseStep 1600213 = 37505) (by norm_num)
theorem B2132717 : Blo 1421530 2132717 := bbase (se 3 (by rfl) ⟨399884, by rfl⟩ : syracuseStep 2132717 = 799769) (by norm_num)
theorem B3599093 : Blo 1421530 3599093 := bbase (se 5 (by rfl) ⟨168707, by rfl⟩ : syracuseStep 3599093 = 337415) (by norm_num)
theorem B1600249 : Blo 1421530 1600249 := bbase (se 2 (by rfl) ⟨600093, by rfl⟩ : syracuseStep 1600249 = 1200187) (by norm_num)
theorem B2132741 : Blo 1421530 2132741 := bbase (se 4 (by rfl) ⟨199944, by rfl⟩ : syracuseStep 2132741 = 399889) (by norm_num)
theorem B2132765 : Blo 1421530 2132765 := bbase (se 3 (by rfl) ⟨399893, by rfl⟩ : syracuseStep 2132765 = 799787) (by norm_num)
theorem B1600285 : Blo 1421530 1600285 := bbase (se 3 (by rfl) ⟨300053, by rfl⟩ : syracuseStep 1600285 = 600107) (by norm_num)
theorem B2132789 : Blo 1421530 2132789 := bbase (se 5 (by rfl) ⟨99974, by rfl⟩ : syracuseStep 2132789 = 199949) (by norm_num)
theorem B2026301 : Blo 1421530 2026301 := bbase (se 3 (by rfl) ⟨379931, by rfl⟩ : syracuseStep 2026301 = 759863) (by norm_num)
theorem B1600321 : Blo 1421530 1600321 := bbase (se 2 (by rfl) ⟨600120, by rfl⟩ : syracuseStep 1600321 = 1200241) (by norm_num)
theorem B7203653 : Blo 1421530 7203653 := bbase (se 4 (by rfl) ⟨675342, by rfl⟩ : syracuseStep 7203653 = 1350685) (by norm_num)
theorem B2132813 : Blo 1421530 2132813 := bbase (se 3 (by rfl) ⟨399902, by rfl⟩ : syracuseStep 2132813 = 799805) (by norm_num)
theorem B2132837 : Blo 1421530 2132837 := bbase (se 4 (by rfl) ⟨199953, by rfl⟩ : syracuseStep 2132837 = 399907) (by norm_num)
theorem B1600357 : Blo 1421530 1600357 := bbase (se 4 (by rfl) ⟨150033, by rfl⟩ : syracuseStep 1600357 = 300067) (by norm_num)
theorem B2132861 : Blo 1421530 2132861 := bbase (se 3 (by rfl) ⟨399911, by rfl⟩ : syracuseStep 2132861 = 799823) (by norm_num)
theorem B4803461 : Blo 1421530 4803461 := bbase (se 4 (by rfl) ⟨450324, by rfl⟩ : syracuseStep 4803461 = 900649) (by norm_num)
theorem B1600393 : Blo 1421530 1600393 := bbase (se 2 (by rfl) ⟨600147, by rfl⟩ : syracuseStep 1600393 = 1200295) (by norm_num)
theorem B2132885 : Blo 1421530 2132885 := bbase (se 6 (by rfl) ⟨49989, by rfl⟩ : syracuseStep 2132885 = 99979) (by norm_num)
theorem B13863829 : Blo 1421530 13863829 := bbase (se 6 (by rfl) ⟨324933, by rfl⟩ : syracuseStep 13863829 = 649867) (by norm_num)
theorem B2132909 : Blo 1421530 2132909 := bbase (se 3 (by rfl) ⟨399920, by rfl⟩ : syracuseStep 2132909 = 799841) (by norm_num)
theorem B1600429 : Blo 1421530 1600429 := bbase (se 3 (by rfl) ⟨300080, by rfl⟩ : syracuseStep 1600429 = 600161) (by norm_num)
theorem B5401525 : Blo 1421530 5401525 := bbase (se 5 (by rfl) ⟨253196, by rfl⟩ : syracuseStep 5401525 = 506393) (by norm_num)
theorem B2132933 : Blo 1421530 2132933 := bbase (se 4 (by rfl) ⟨199962, by rfl⟩ : syracuseStep 2132933 = 399925) (by norm_num)
theorem B1600465 : Blo 1421530 1600465 := bbase (se 2 (by rfl) ⟨600174, by rfl⟩ : syracuseStep 1600465 = 1200349) (by norm_num)
theorem B2132957 : Blo 1421530 2132957 := bbase (se 3 (by rfl) ⟨399929, by rfl⟩ : syracuseStep 2132957 = 799859) (by norm_num)
theorem B2132981 : Blo 1421530 2132981 := bbase (se 5 (by rfl) ⟨99983, by rfl⟩ : syracuseStep 2132981 = 199967) (by norm_num)
theorem B1600501 : Blo 1421530 1600501 := bbase (se 5 (by rfl) ⟨75023, by rfl⟩ : syracuseStep 1600501 = 150047) (by norm_num)
theorem B2133005 : Blo 1421530 2133005 := bbase (se 3 (by rfl) ⟨399938, by rfl⟩ : syracuseStep 2133005 = 799877) (by norm_num)
theorem B4557845 : Blo 1421530 4557845 := bbase (se 6 (by rfl) ⟨106824, by rfl⟩ : syracuseStep 4557845 = 213649) (by norm_num)
theorem B1600537 : Blo 1421530 1600537 := bbase (se 2 (by rfl) ⟨600201, by rfl⟩ : syracuseStep 1600537 = 1200403) (by norm_num)
theorem B2133029 : Blo 1421530 2133029 := bbase (se 4 (by rfl) ⟨199971, by rfl⟩ : syracuseStep 2133029 = 399943) (by norm_num)
theorem B2133053 : Blo 1421530 2133053 := bbase (se 3 (by rfl) ⟨399947, by rfl⟩ : syracuseStep 2133053 = 799895) (by norm_num)
theorem B1600573 : Blo 1421530 1600573 := bbase (se 3 (by rfl) ⟨300107, by rfl⟩ : syracuseStep 1600573 = 600215) (by norm_num)
theorem B3599437 : Blo 1421530 3599437 := bbase (se 3 (by rfl) ⟨674894, by rfl⟩ : syracuseStep 3599437 = 1349789) (by norm_num)
theorem B2133077 : Blo 1421530 2133077 := bbase (se 8 (by rfl) ⟨12498, by rfl⟩ : syracuseStep 2133077 = 24997) (by norm_num)
theorem B1600609 : Blo 1421530 1600609 := bbase (se 2 (by rfl) ⟨600228, by rfl⟩ : syracuseStep 1600609 = 1200457) (by norm_num)
theorem B1518697 : Blo 1421530 1518697 := bbase (se 2 (by rfl) ⟨569511, by rfl⟩ : syracuseStep 1518697 = 1139023) (by norm_num)
theorem B2133101 : Blo 1421530 2133101 := bbase (se 3 (by rfl) ⟨399956, by rfl⟩ : syracuseStep 2133101 = 799913) (by norm_num)
theorem B2133125 : Blo 1421530 2133125 := bbase (se 4 (by rfl) ⟨199980, by rfl⟩ : syracuseStep 2133125 = 399961) (by norm_num)
theorem B1600645 : Blo 1421530 1600645 := bbase (se 4 (by rfl) ⟨150060, by rfl⟩ : syracuseStep 1600645 = 300121) (by norm_num)
theorem B2133149 : Blo 1421530 2133149 := bbase (se 3 (by rfl) ⟨399965, by rfl⟩ : syracuseStep 2133149 = 799931) (by norm_num)
theorem B1600681 : Blo 1421530 1600681 := bbase (se 2 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 1600681 = 1200511) (by norm_num)
theorem B1518769 : Blo 1421530 1518769 := bbase (se 2 (by rfl) ⟨569538, by rfl⟩ : syracuseStep 1518769 = 1139077) (by norm_num)
theorem B2133173 : Blo 1421530 2133173 := bbase (se 5 (by rfl) ⟨99992, by rfl⟩ : syracuseStep 2133173 = 199985) (by norm_num)
theorem B3599549 : Blo 1421530 3599549 := bbase (se 3 (by rfl) ⟨674915, by rfl⟩ : syracuseStep 3599549 = 1349831) (by norm_num)
theorem B2133197 : Blo 1421530 2133197 := bbase (se 3 (by rfl) ⟨399974, by rfl⟩ : syracuseStep 2133197 = 799949) (by norm_num)
theorem B1600717 : Blo 1421530 1600717 := bbase (se 3 (by rfl) ⟨300134, by rfl⟩ : syracuseStep 1600717 = 600269) (by norm_num)
theorem B2133221 : Blo 1421530 2133221 := bbase (se 4 (by rfl) ⟨199989, by rfl⟩ : syracuseStep 2133221 = 399979) (by norm_num)
theorem B5401829 : Blo 1421530 5401829 := bbase (se 4 (by rfl) ⟨506421, by rfl⟩ : syracuseStep 5401829 = 1012843) (by norm_num)
theorem B1600753 : Blo 1421530 1600753 := bbase (se 2 (by rfl) ⟨600282, by rfl⟩ : syracuseStep 1600753 = 1200565) (by norm_num)
theorem B2133245 : Blo 1421530 2133245 := bbase (se 3 (by rfl) ⟨399983, by rfl⟩ : syracuseStep 2133245 = 799967) (by norm_num)
theorem B2133269 : Blo 1421530 2133269 := bbase (se 6 (by rfl) ⟨49998, by rfl⟩ : syracuseStep 2133269 = 99997) (by norm_num)
theorem B1600789 : Blo 1421530 1600789 := bbase (se 6 (by rfl) ⟨37518, by rfl⟩ : syracuseStep 1600789 = 75037) (by norm_num)
theorem B2133293 : Blo 1421530 2133293 := bbase (se 3 (by rfl) ⟨399992, by rfl⟩ : syracuseStep 2133293 = 799985) (by norm_num)
theorem B4803893 : Blo 1421530 4803893 := bbase (se 5 (by rfl) ⟨225182, by rfl⟩ : syracuseStep 4803893 = 450365) (by norm_num)
theorem B1600825 : Blo 1421530 1600825 := bbase (se 2 (by rfl) ⟨600309, by rfl⟩ : syracuseStep 1600825 = 1200619) (by norm_num)
theorem B2133317 : Blo 1421530 2133317 := bbase (se 4 (by rfl) ⟨199998, by rfl⟩ : syracuseStep 2133317 = 399997) (by norm_num)
theorem B2133341 : Blo 1421530 2133341 := bbase (se 3 (by rfl) ⟨400001, by rfl⟩ : syracuseStep 2133341 = 800003) (by norm_num)
theorem B1600861 : Blo 1421530 1600861 := bbase (se 3 (by rfl) ⟨300161, by rfl⟩ : syracuseStep 1600861 = 600323) (by norm_num)
theorem B1518949 : Blo 1421530 1518949 := bbase (se 4 (by rfl) ⟨142401, by rfl⟩ : syracuseStep 1518949 = 284803) (by norm_num)
theorem B2133365 : Blo 1421530 2133365 := bbase (se 5 (by rfl) ⟨100001, by rfl⟩ : syracuseStep 2133365 = 200003) (by norm_num)
theorem B3599741 : Blo 1421530 3599741 := bbase (se 3 (by rfl) ⟨674951, by rfl⟩ : syracuseStep 3599741 = 1349903) (by norm_num)
theorem B1600897 : Blo 1421530 1600897 := bbase (se 2 (by rfl) ⟨600336, by rfl⟩ : syracuseStep 1600897 = 1200673) (by norm_num)
theorem B2133389 : Blo 1421530 2133389 := bbase (se 3 (by rfl) ⟨400010, by rfl⟩ : syracuseStep 2133389 = 800021) (by norm_num)
theorem B2133413 : Blo 1421530 2133413 := bbase (se 4 (by rfl) ⟨200007, by rfl⟩ : syracuseStep 2133413 = 400015) (by norm_num)
theorem B1600933 : Blo 1421530 1600933 := bbase (se 4 (by rfl) ⟨150087, by rfl⟩ : syracuseStep 1600933 = 300175) (by norm_num)
theorem B2133437 : Blo 1421530 2133437 := bbase (se 3 (by rfl) ⟨400019, by rfl⟩ : syracuseStep 2133437 = 800039) (by norm_num)
theorem B1600969 : Blo 1421530 1600969 := bbase (se 2 (by rfl) ⟨600363, by rfl⟩ : syracuseStep 1600969 = 1200727) (by norm_num)
theorem B2133461 : Blo 1421530 2133461 := bbase (se 7 (by rfl) ⟨25001, by rfl⟩ : syracuseStep 2133461 = 50003) (by norm_num)
theorem B2133485 : Blo 1421530 2133485 := bbase (se 3 (by rfl) ⟨400028, by rfl⟩ : syracuseStep 2133485 = 800057) (by norm_num)
theorem B1601005 : Blo 1421530 1601005 := bbase (se 3 (by rfl) ⟨300188, by rfl⟩ : syracuseStep 1601005 = 600377) (by norm_num)
theorem B2133509 : Blo 1421530 2133509 := bbase (se 4 (by rfl) ⟨200016, by rfl⟩ : syracuseStep 2133509 = 400033) (by norm_num)
theorem B1601041 : Blo 1421530 1601041 := bbase (se 2 (by rfl) ⟨600390, by rfl⟩ : syracuseStep 1601041 = 1200781) (by norm_num)
theorem B2133533 : Blo 1421530 2133533 := bbase (se 3 (by rfl) ⟨400037, by rfl⟩ : syracuseStep 2133533 = 800075) (by norm_num)
theorem B3198509 : Blo 1421530 3198509 := bbase (se 3 (by rfl) ⟨599720, by rfl⟩ : syracuseStep 3198509 = 1199441) (by norm_num)
theorem B2133557 : Blo 1421530 2133557 := bbase (se 5 (by rfl) ⟨100010, by rfl⟩ : syracuseStep 2133557 = 200021) (by norm_num)
theorem B1601077 : Blo 1421530 1601077 := bbase (se 5 (by rfl) ⟨75050, by rfl⟩ : syracuseStep 1601077 = 150101) (by norm_num)
theorem B2133581 : Blo 1421530 2133581 := bbase (se 3 (by rfl) ⟨400046, by rfl⟩ : syracuseStep 2133581 = 800093) (by norm_num)
theorem B1601113 : Blo 1421530 1601113 := bbase (se 2 (by rfl) ⟨600417, by rfl⟩ : syracuseStep 1601113 = 1200835) (by norm_num)
theorem B2133605 : Blo 1421530 2133605 := bbase (se 4 (by rfl) ⟨200025, by rfl⟩ : syracuseStep 2133605 = 400051) (by norm_num)
theorem B3198581 : Blo 1421530 3198581 := bbase (se 5 (by rfl) ⟨149933, by rfl⟩ : syracuseStep 3198581 = 299867) (by norm_num)
theorem B2133629 : Blo 1421530 2133629 := bbase (se 3 (by rfl) ⟨400055, by rfl⟩ : syracuseStep 2133629 = 800111) (by norm_num)
theorem B1601149 : Blo 1421530 1601149 := bbase (se 3 (by rfl) ⟨300215, by rfl⟩ : syracuseStep 1601149 = 600431) (by norm_num)
theorem B2133653 : Blo 1421530 2133653 := bbase (se 6 (by rfl) ⟨50007, by rfl⟩ : syracuseStep 2133653 = 100015) (by norm_num)
theorem B1601185 : Blo 1421530 1601185 := bbase (se 2 (by rfl) ⟨600444, by rfl⟩ : syracuseStep 1601185 = 1200889) (by norm_num)
theorem B2133677 : Blo 1421530 2133677 := bbase (se 3 (by rfl) ⟨400064, by rfl⟩ : syracuseStep 2133677 = 800129) (by norm_num)
theorem B2698933 : Blo 1421530 2698933 := bbase (se 5 (by rfl) ⟨126512, by rfl⟩ : syracuseStep 2698933 = 253025) (by norm_num)
theorem B3198653 : Blo 1421530 3198653 := bbase (se 3 (by rfl) ⟨599747, by rfl⟩ : syracuseStep 3198653 = 1199495) (by norm_num)
theorem B2133701 : Blo 1421530 2133701 := bbase (se 4 (by rfl) ⟨200034, by rfl⟩ : syracuseStep 2133701 = 400069) (by norm_num)
theorem B1601221 : Blo 1421530 1601221 := bbase (se 4 (by rfl) ⟨150114, by rfl⟩ : syracuseStep 1601221 = 300229) (by norm_num)
theorem B3600085 : Blo 1421530 3600085 := bbase (se 7 (by rfl) ⟨42188, by rfl⟩ : syracuseStep 3600085 = 84377) (by norm_num)
theorem B46157525 : Blo 1421530 46157525 := bbase (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) (by norm_num)
theorem B2133725 : Blo 1421530 2133725 := bbase (se 3 (by rfl) ⟨400073, by rfl⟩ : syracuseStep 2133725 = 800147) (by norm_num)
theorem B4804325 : Blo 1421530 4804325 := bbase (se 4 (by rfl) ⟨450405, by rfl⟩ : syracuseStep 4804325 = 900811) (by norm_num)
theorem B1601257 : Blo 1421530 1601257 := bbase (se 2 (by rfl) ⟨600471, by rfl⟩ : syracuseStep 1601257 = 1200943) (by norm_num)
theorem B2133749 : Blo 1421530 2133749 := bbase (se 5 (by rfl) ⟨100019, by rfl⟩ : syracuseStep 2133749 = 200039) (by norm_num)
theorem B3198725 : Blo 1421530 3198725 := bbase (se 4 (by rfl) ⟨299880, by rfl⟩ : syracuseStep 3198725 = 599761) (by norm_num)
theorem B2133773 : Blo 1421530 2133773 := bbase (se 3 (by rfl) ⟨400082, by rfl⟩ : syracuseStep 2133773 = 800165) (by norm_num)
theorem B1601293 : Blo 1421530 1601293 := bbase (se 3 (by rfl) ⟨300242, by rfl⟩ : syracuseStep 1601293 = 600485) (by norm_num)
theorem B1519393 : Blo 1421530 1519393 := bbase (se 2 (by rfl) ⟨569772, by rfl⟩ : syracuseStep 1519393 = 1139545) (by norm_num)
theorem B2133797 : Blo 1421530 2133797 := bbase (se 4 (by rfl) ⟨200043, by rfl⟩ : syracuseStep 2133797 = 400087) (by norm_num)
theorem B1601329 : Blo 1421530 1601329 := bbase (se 2 (by rfl) ⟨600498, by rfl⟩ : syracuseStep 1601329 = 1200997) (by norm_num)
theorem B2133821 : Blo 1421530 2133821 := bbase (se 3 (by rfl) ⟨400091, by rfl⟩ : syracuseStep 2133821 = 800183) (by norm_num)
theorem B2699077 : Blo 1421530 2699077 := bbase (se 4 (by rfl) ⟨253038, by rfl⟩ : syracuseStep 2699077 = 506077) (by norm_num)
theorem B3600197 : Blo 1421530 3600197 := bbase (se 4 (by rfl) ⟨337518, by rfl⟩ : syracuseStep 3600197 = 675037) (by norm_num)
theorem B3198797 : Blo 1421530 3198797 := bbase (se 3 (by rfl) ⟨599774, by rfl⟩ : syracuseStep 3198797 = 1199549) (by norm_num)
theorem B2133845 : Blo 1421530 2133845 := bbase (se 9 (by rfl) ⟨6251, by rfl⟩ : syracuseStep 2133845 = 12503) (by norm_num)
theorem B1601365 : Blo 1421530 1601365 := bbase (se 9 (by rfl) ⟨4691, by rfl⟩ : syracuseStep 1601365 = 9383) (by norm_num)
theorem B2133869 : Blo 1421530 2133869 := bbase (se 3 (by rfl) ⟨400100, by rfl⟩ : syracuseStep 2133869 = 800201) (by norm_num)
theorem B1601401 : Blo 1421530 1601401 := bbase (se 2 (by rfl) ⟨600525, by rfl⟩ : syracuseStep 1601401 = 1201051) (by norm_num)
theorem B2133893 : Blo 1421530 2133893 := bbase (se 4 (by rfl) ⟨200052, by rfl⟩ : syracuseStep 2133893 = 400105) (by norm_num)
theorem B3198869 : Blo 1421530 3198869 := bbase (se 6 (by rfl) ⟨74973, by rfl⟩ : syracuseStep 3198869 = 149947) (by norm_num)
theorem B2133917 : Blo 1421530 2133917 := bbase (se 3 (by rfl) ⟨400109, by rfl⟩ : syracuseStep 2133917 = 800219) (by norm_num)
theorem B1519517 : Blo 1421530 1519517 := bbase (se 3 (by rfl) ⟨284909, by rfl⟩ : syracuseStep 1519517 = 569819) (by norm_num)
theorem B1601437 : Blo 1421530 1601437 := bbase (se 3 (by rfl) ⟨300269, by rfl⟩ : syracuseStep 1601437 = 600539) (by norm_num)
theorem B2133941 : Blo 1421530 2133941 := bbase (se 5 (by rfl) ⟨100028, by rfl⟩ : syracuseStep 2133941 = 200057) (by norm_num)
theorem B2133965 : Blo 1421530 2133965 := bbase (se 3 (by rfl) ⟨400118, by rfl⟩ : syracuseStep 2133965 = 800237) (by norm_num)
theorem B17313749 : Blo 1421530 17313749 := bbase (se 7 (by rfl) ⟨202895, by rfl⟩ : syracuseStep 17313749 = 405791) (by norm_num)
theorem B3198941 : Blo 1421530 3198941 := bbase (se 3 (by rfl) ⟨599801, by rfl⟩ : syracuseStep 3198941 = 1199603) (by norm_num)
theorem B2699237 : Blo 1421530 2699237 := bbase (se 4 (by rfl) ⟨253053, by rfl⟩ : syracuseStep 2699237 = 506107) (by norm_num)
theorem B4050917 : Blo 1421530 4050917 := bbase (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) (by norm_num)
theorem B2133989 : Blo 1421530 2133989 := bbase (se 4 (by rfl) ⟨200061, by rfl⟩ : syracuseStep 2133989 = 400123) (by norm_num)
theorem B2134013 : Blo 1421530 2134013 := bbase (se 3 (by rfl) ⟨400127, by rfl⟩ : syracuseStep 2134013 = 800255) (by norm_num)
theorem B3600389 : Blo 1421530 3600389 := bbase (se 4 (by rfl) ⟨337536, by rfl⟩ : syracuseStep 3600389 = 675073) (by norm_num)
theorem B2134037 : Blo 1421530 2134037 := bbase (se 6 (by rfl) ⟨50016, by rfl⟩ : syracuseStep 2134037 = 100033) (by norm_num)
theorem B3199013 : Blo 1421530 3199013 := bbase (se 4 (by rfl) ⟨299907, by rfl⟩ : syracuseStep 3199013 = 599815) (by norm_num)
theorem B2134061 : Blo 1421530 2134061 := bbase (se 3 (by rfl) ⟨400136, by rfl⟩ : syracuseStep 2134061 = 800273) (by norm_num)
theorem B2134085 : Blo 1421530 2134085 := bbase (se 4 (by rfl) ⟨200070, by rfl⟩ : syracuseStep 2134085 = 400141) (by norm_num)
theorem B3420229 : Blo 1421530 3420229 := bbase (se 4 (by rfl) ⟨320646, by rfl⟩ : syracuseStep 3420229 = 641293) (by norm_num)
theorem B7204949 : Blo 1421530 7204949 := bbase (se 8 (by rfl) ⟨42216, by rfl⟩ : syracuseStep 7204949 = 84433) (by norm_num)
theorem B2134109 : Blo 1421530 2134109 := bbase (se 3 (by rfl) ⟨400145, by rfl⟩ : syracuseStep 2134109 = 800291) (by norm_num)
theorem B3199085 : Blo 1421530 3199085 := bbase (se 3 (by rfl) ⟨599828, by rfl⟩ : syracuseStep 3199085 = 1199657) (by norm_num)
theorem B2699381 : Blo 1421530 2699381 := bbase (se 5 (by rfl) ⟨126533, by rfl⟩ : syracuseStep 2699381 = 253067) (by norm_num)
theorem B2134133 : Blo 1421530 2134133 := bbase (se 5 (by rfl) ⟨100037, by rfl⟩ : syracuseStep 2134133 = 200075) (by norm_num)
theorem B6574213 : Blo 1421530 6574213 := bbase (se 4 (by rfl) ⟨616332, by rfl⟩ : syracuseStep 6574213 = 1232665) (by norm_num)
theorem B2134157 : Blo 1421530 2134157 := bbase (se 3 (by rfl) ⟨400154, by rfl⟩ : syracuseStep 2134157 = 800309) (by norm_num)
theorem B1519769 : Blo 1421530 1519769 := bbase (se 2 (by rfl) ⟨569913, by rfl⟩ : syracuseStep 1519769 = 1139827) (by norm_num)
theorem B2134181 : Blo 1421530 2134181 := bbase (se 4 (by rfl) ⟨200079, by rfl⟩ : syracuseStep 2134181 = 400159) (by norm_num)
theorem B3199157 : Blo 1421530 3199157 := bbase (se 5 (by rfl) ⟨149960, by rfl⟩ : syracuseStep 3199157 = 299921) (by norm_num)
theorem B2134205 : Blo 1421530 2134205 := bbase (se 3 (by rfl) ⟨400163, by rfl⟩ : syracuseStep 2134205 = 800327) (by norm_num)
theorem B7794901 : Blo 1421530 7794901 := bbase (se 7 (by rfl) ⟨91346, by rfl⟩ : syracuseStep 7794901 = 182693) (by norm_num)
theorem B2134229 : Blo 1421530 2134229 := bbase (se 7 (by rfl) ⟨25010, by rfl⟩ : syracuseStep 2134229 = 50021) (by norm_num)
theorem B25972949 : Blo 1421530 25972949 := bbase (se 7 (by rfl) ⟨304370, by rfl⟩ : syracuseStep 25972949 = 608741) (by norm_num)
theorem B2134253 : Blo 1421530 2134253 := bbase (se 3 (by rfl) ⟨400172, by rfl⟩ : syracuseStep 2134253 = 800345) (by norm_num)
theorem B3199229 : Blo 1421530 3199229 := bbase (se 3 (by rfl) ⟨599855, by rfl⟩ : syracuseStep 3199229 = 1199711) (by norm_num)
theorem B2134277 : Blo 1421530 2134277 := bbase (se 4 (by rfl) ⟨200088, by rfl⟩ : syracuseStep 2134277 = 400177) (by norm_num)
theorem B2887949 : Blo 1421530 2887949 := bbase (se 3 (by rfl) ⟨541490, by rfl⟩ : syracuseStep 2887949 = 1082981) (by norm_num)
theorem B6836501 : Blo 1421530 6836501 := bbase (se 6 (by rfl) ⟨160230, by rfl⟩ : syracuseStep 6836501 = 320461) (by norm_num)
theorem B2134301 : Blo 1421530 2134301 := bbase (se 3 (by rfl) ⟨400181, by rfl⟩ : syracuseStep 2134301 = 800363) (by norm_num)
theorem B2134325 : Blo 1421530 2134325 := bbase (se 5 (by rfl) ⟨100046, by rfl⟩ : syracuseStep 2134325 = 200093) (by norm_num)
theorem B3199301 : Blo 1421530 3199301 := bbase (se 4 (by rfl) ⟨299934, by rfl⟩ : syracuseStep 3199301 = 599869) (by norm_num)
theorem B2134349 : Blo 1421530 2134349 := bbase (se 3 (by rfl) ⟨400190, by rfl⟩ : syracuseStep 2134349 = 800381) (by norm_num)
theorem B3600733 : Blo 1421530 3600733 := bbase (se 3 (by rfl) ⟨675137, by rfl⟩ : syracuseStep 3600733 = 1350275) (by norm_num)
theorem B2134373 : Blo 1421530 2134373 := bbase (se 4 (by rfl) ⟨200097, by rfl⟩ : syracuseStep 2134373 = 400195) (by norm_num)
theorem B2134397 : Blo 1421530 2134397 := bbase (se 3 (by rfl) ⟨400199, by rfl⟩ : syracuseStep 2134397 = 800399) (by norm_num)
theorem B3199373 : Blo 1421530 3199373 := bbase (se 3 (by rfl) ⟨599882, by rfl⟩ : syracuseStep 3199373 = 1199765) (by norm_num)
theorem B2699669 : Blo 1421530 2699669 := bbase (se 6 (by rfl) ⟨63273, by rfl⟩ : syracuseStep 2699669 = 126547) (by norm_num)
theorem B2134421 : Blo 1421530 2134421 := bbase (se 6 (by rfl) ⟨50025, by rfl⟩ : syracuseStep 2134421 = 100051) (by norm_num)
theorem B8106389 : Blo 1421530 8106389 := bbase (se 6 (by rfl) ⟨189993, by rfl⟩ : syracuseStep 8106389 = 379987) (by norm_num)
theorem B1708457 : Blo 1421530 1708457 := bbase (se 2 (by rfl) ⟨640671, by rfl⟩ : syracuseStep 1708457 = 1281343) (by norm_num)
theorem B2134445 : Blo 1421530 2134445 := bbase (se 3 (by rfl) ⟨400208, by rfl⟩ : syracuseStep 2134445 = 800417) (by norm_num)
theorem B2134469 : Blo 1421530 2134469 := bbase (se 4 (by rfl) ⟨200106, by rfl⟩ : syracuseStep 2134469 = 400213) (by norm_num)
theorem B3600845 : Blo 1421530 3600845 := bbase (se 3 (by rfl) ⟨675158, by rfl⟩ : syracuseStep 3600845 = 1350317) (by norm_num)
theorem B3199445 : Blo 1421530 3199445 := bbase (se 7 (by rfl) ⟨37493, by rfl⟩ : syracuseStep 3199445 = 74987) (by norm_num)
theorem B3650005 : Blo 1421530 3650005 := bbase (se 7 (by rfl) ⟨42773, by rfl⟩ : syracuseStep 3650005 = 85547) (by norm_num)
theorem B2134493 : Blo 1421530 2134493 := bbase (se 3 (by rfl) ⟨400217, by rfl⟩ : syracuseStep 2134493 = 800435) (by norm_num)
theorem B7197173 : Blo 1421530 7197173 := bbase (se 5 (by rfl) ⟨337367, by rfl⟩ : syracuseStep 7197173 = 674735) (by norm_num)
theorem B2134517 : Blo 1421530 2134517 := bbase (se 5 (by rfl) ⟨100055, by rfl⟩ : syracuseStep 2134517 = 200111) (by norm_num)
theorem B2134541 : Blo 1421530 2134541 := bbase (se 3 (by rfl) ⟨400226, by rfl⟩ : syracuseStep 2134541 = 800453) (by norm_num)
theorem B8098325 : Blo 1421530 8098325 := bbase (se 6 (by rfl) ⟨189804, by rfl⟩ : syracuseStep 8098325 = 379609) (by norm_num)
theorem B3199517 : Blo 1421530 3199517 := bbase (se 3 (by rfl) ⟨599909, by rfl⟩ : syracuseStep 3199517 = 1199819) (by norm_num)
theorem B2134565 : Blo 1421530 2134565 := bbase (se 4 (by rfl) ⟨200115, by rfl⟩ : syracuseStep 2134565 = 400231) (by norm_num)
theorem B2699821 : Blo 1421530 2699821 := bbase (se 3 (by rfl) ⟨506216, by rfl⟩ : syracuseStep 2699821 = 1012433) (by norm_num)
theorem B2134589 : Blo 1421530 2134589 := bbase (se 3 (by rfl) ⟨400235, by rfl⟩ : syracuseStep 2134589 = 800471) (by norm_num)
theorem B2134613 : Blo 1421530 2134613 := bbase (se 8 (by rfl) ⟨12507, by rfl⟩ : syracuseStep 2134613 = 25015) (by norm_num)
theorem B3199589 : Blo 1421530 3199589 := bbase (se 4 (by rfl) ⟨299961, by rfl⟩ : syracuseStep 3199589 = 599923) (by norm_num)
theorem B2134637 : Blo 1421530 2134637 := bbase (se 3 (by rfl) ⟨400244, by rfl⟩ : syracuseStep 2134637 = 800489) (by norm_num)
theorem B2134661 : Blo 1421530 2134661 := bbase (se 4 (by rfl) ⟨200124, by rfl⟩ : syracuseStep 2134661 = 400249) (by norm_num)
theorem B3601037 : Blo 1421530 3601037 := bbase (se 3 (by rfl) ⟨675194, by rfl⟩ : syracuseStep 3601037 = 1350389) (by norm_num)
theorem B12145301 : Blo 1421530 12145301 := bbase (se 6 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 12145301 = 569311) (by norm_num)
theorem B2134685 : Blo 1421530 2134685 := bbase (se 3 (by rfl) ⟨400253, by rfl⟩ : syracuseStep 2134685 = 800507) (by norm_num)
theorem B3199661 : Blo 1421530 3199661 := bbase (se 3 (by rfl) ⟨599936, by rfl⟩ : syracuseStep 3199661 = 1199873) (by norm_num)
theorem B2134709 : Blo 1421530 2134709 := bbase (se 5 (by rfl) ⟨100064, by rfl⟩ : syracuseStep 2134709 = 200129) (by norm_num)
theorem B2134733 : Blo 1421530 2134733 := bbase (se 3 (by rfl) ⟨400262, by rfl⟩ : syracuseStep 2134733 = 800525) (by norm_num)
theorem B2134757 : Blo 1421530 2134757 := bbase (se 4 (by rfl) ⟨200133, by rfl⟩ : syracuseStep 2134757 = 400267) (by norm_num)
theorem B3199733 : Blo 1421530 3199733 := bbase (se 5 (by rfl) ⟨149987, by rfl⟩ : syracuseStep 3199733 = 299975) (by norm_num)
theorem B1708789 : Blo 1421530 1708789 := bbase (se 5 (by rfl) ⟨80099, by rfl⟩ : syracuseStep 1708789 = 160199) (by norm_num)
theorem B2134781 : Blo 1421530 2134781 := bbase (se 3 (by rfl) ⟨400271, by rfl⟩ : syracuseStep 2134781 = 800543) (by norm_num)
theorem B2134805 : Blo 1421530 2134805 := bbase (se 6 (by rfl) ⟨50034, by rfl⟩ : syracuseStep 2134805 = 100069) (by norm_num)
theorem B2134829 : Blo 1421530 2134829 := bbase (se 3 (by rfl) ⟨400280, by rfl⟩ : syracuseStep 2134829 = 800561) (by norm_num)
theorem B3199805 : Blo 1421530 3199805 := bbase (se 3 (by rfl) ⟨599963, by rfl⟩ : syracuseStep 3199805 = 1199927) (by norm_num)
theorem B2134853 : Blo 1421530 2134853 := bbase (se 4 (by rfl) ⟨200142, by rfl⟩ : syracuseStep 2134853 = 400285) (by norm_num)
theorem B2700125 : Blo 1421530 2700125 := bbase (se 3 (by rfl) ⟨506273, by rfl⟩ : syracuseStep 2700125 = 1012547) (by norm_num)
theorem B2134877 : Blo 1421530 2134877 := bbase (se 3 (by rfl) ⟨400289, by rfl⟩ : syracuseStep 2134877 = 800579) (by norm_num)
theorem B9237365 : Blo 1421530 9237365 := bbase (se 5 (by rfl) ⟨433001, by rfl⟩ : syracuseStep 9237365 = 866003) (by norm_num)
theorem B2134901 : Blo 1421530 2134901 := bbase (se 5 (by rfl) ⟨100073, by rfl⟩ : syracuseStep 2134901 = 200147) (by norm_num)
theorem B3199877 : Blo 1421530 3199877 := bbase (se 4 (by rfl) ⟨299988, by rfl⟩ : syracuseStep 3199877 = 599977) (by norm_num)
theorem B1708933 : Blo 1421530 1708933 := bbase (se 4 (by rfl) ⟨160212, by rfl⟩ : syracuseStep 1708933 = 320425) (by norm_num)
theorem B2134925 : Blo 1421530 2134925 := bbase (se 3 (by rfl) ⟨400298, by rfl⟩ : syracuseStep 2134925 = 800597) (by norm_num)
theorem B2134949 : Blo 1421530 2134949 := bbase (se 4 (by rfl) ⟨200151, by rfl⟩ : syracuseStep 2134949 = 400303) (by norm_num)
theorem B2134973 : Blo 1421530 2134973 := bbase (se 3 (by rfl) ⟨400307, by rfl⟩ : syracuseStep 2134973 = 800615) (by norm_num)
theorem B3199949 : Blo 1421530 3199949 := bbase (se 3 (by rfl) ⟨599990, by rfl⟩ : syracuseStep 3199949 = 1199981) (by norm_num)
theorem B2134997 : Blo 1421530 2134997 := bbase (se 7 (by rfl) ⟨25019, by rfl⟩ : syracuseStep 2134997 = 50039) (by norm_num)
theorem B3601381 : Blo 1421530 3601381 := bbase (se 4 (by rfl) ⟨337629, by rfl⟩ : syracuseStep 3601381 = 675259) (by norm_num)
theorem B2135021 : Blo 1421530 2135021 := bbase (se 3 (by rfl) ⟨400316, by rfl⟩ : syracuseStep 2135021 = 800633) (by norm_num)
theorem B2135045 : Blo 1421530 2135045 := bbase (se 4 (by rfl) ⟨200160, by rfl⟩ : syracuseStep 2135045 = 400321) (by norm_num)
theorem B3200021 : Blo 1421530 3200021 := bbase (se 6 (by rfl) ⟨75000, by rfl⟩ : syracuseStep 3200021 = 150001) (by norm_num)
theorem B2135069 : Blo 1421530 2135069 := bbase (se 3 (by rfl) ⟨400325, by rfl⟩ : syracuseStep 2135069 = 800651) (by norm_num)
theorem B2135093 : Blo 1421530 2135093 := bbase (se 5 (by rfl) ⟨100082, by rfl⟩ : syracuseStep 2135093 = 200165) (by norm_num)
theorem B2135117 : Blo 1421530 2135117 := bbase (se 3 (by rfl) ⟨400334, by rfl⟩ : syracuseStep 2135117 = 800669) (by norm_num)
theorem B3601493 : Blo 1421530 3601493 := bbase (se 8 (by rfl) ⟨21102, by rfl⟩ : syracuseStep 3601493 = 42205) (by norm_num)
theorem B3200093 : Blo 1421530 3200093 := bbase (se 3 (by rfl) ⟨600017, by rfl⟩ : syracuseStep 3200093 = 1200035) (by norm_num)
theorem B1922149 : Blo 1421530 1922149 := bbase (se 4 (by rfl) ⟨180201, by rfl⟩ : syracuseStep 1922149 = 360403) (by norm_num)
theorem B2135141 : Blo 1421530 2135141 := bbase (se 4 (by rfl) ⟨200169, by rfl⟩ : syracuseStep 2135141 = 400339) (by norm_num)
theorem B1799273 : Blo 1421530 1799273 := bbase (se 2 (by rfl) ⟨674727, by rfl⟩ : syracuseStep 1799273 = 1349455) (by norm_num)
theorem B2135165 : Blo 1421530 2135165 := bbase (se 3 (by rfl) ⟨400343, by rfl⟩ : syracuseStep 2135165 = 800687) (by norm_num)
theorem B4052101 : Blo 1421530 4052101 := bbase (se 4 (by rfl) ⟨379884, by rfl⟩ : syracuseStep 4052101 = 759769) (by norm_num)
theorem B2135189 : Blo 1421530 2135189 := bbase (se 6 (by rfl) ⟨50043, by rfl⟩ : syracuseStep 2135189 = 100087) (by norm_num)
theorem B1799329 : Blo 1421530 1799329 := bbase (se 2 (by rfl) ⟨674748, by rfl⟩ : syracuseStep 1799329 = 1349497) (by norm_num)
theorem B3200165 : Blo 1421530 3200165 := bbase (se 4 (by rfl) ⟨300015, by rfl⟩ : syracuseStep 3200165 = 600031) (by norm_num)
theorem B2135213 : Blo 1421530 2135213 := bbase (se 3 (by rfl) ⟨400352, by rfl⟩ : syracuseStep 2135213 = 800705) (by norm_num)
theorem B2135237 : Blo 1421530 2135237 := bbase (se 4 (by rfl) ⟨200178, by rfl⟩ : syracuseStep 2135237 = 400357) (by norm_num)
theorem B2135261 : Blo 1421530 2135261 := bbase (se 3 (by rfl) ⟨400361, by rfl⟩ : syracuseStep 2135261 = 800723) (by norm_num)
theorem B4560101 : Blo 1421530 4560101 := bbase (se 4 (by rfl) ⟨427509, by rfl⟩ : syracuseStep 4560101 = 855019) (by norm_num)
theorem B3200237 : Blo 1421530 3200237 := bbase (se 3 (by rfl) ⟨600044, by rfl⟩ : syracuseStep 3200237 = 1200089) (by norm_num)
theorem B9114869 : Blo 1421530 9114869 := bbase (se 5 (by rfl) ⟨427259, by rfl⟩ : syracuseStep 9114869 = 854519) (by norm_num)
theorem B2135285 : Blo 1421530 2135285 := bbase (se 5 (by rfl) ⟨100091, by rfl⟩ : syracuseStep 2135285 = 200183) (by norm_num)
theorem B1799425 : Blo 1421530 1799425 := bbase (se 2 (by rfl) ⟨674784, by rfl⟩ : syracuseStep 1799425 = 1349569) (by norm_num)
theorem B3036437 : Blo 1421530 3036437 := bbase (se 6 (by rfl) ⟨71166, by rfl⟩ : syracuseStep 3036437 = 142333) (by norm_num)
theorem B3601685 : Blo 1421530 3601685 := bbase (se 6 (by rfl) ⟨84414, by rfl⟩ : syracuseStep 3601685 = 168829) (by norm_num)
theorem B4052261 : Blo 1421530 4052261 := bbase (se 4 (by rfl) ⟨379899, by rfl⟩ : syracuseStep 4052261 = 759799) (by norm_num)
theorem B5403941 : Blo 1421530 5403941 := bbase (se 4 (by rfl) ⟨506619, by rfl⟩ : syracuseStep 5403941 = 1013239) (by norm_num)
theorem B3200309 : Blo 1421530 3200309 := bbase (se 5 (by rfl) ⟨150014, by rfl⟩ : syracuseStep 3200309 = 300029) (by norm_num)
theorem B7206245 : Blo 1421530 7206245 := bbase (se 4 (by rfl) ⟨675585, by rfl⟩ : syracuseStep 7206245 = 1351171) (by norm_num)
theorem B4560229 : Blo 1421530 4560229 := bbase (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) (by norm_num)
theorem B1848685 : Blo 1421530 1848685 := bbase (se 3 (by rfl) ⟨346628, by rfl⟩ : syracuseStep 1848685 = 693257) (by norm_num)
theorem B3200381 : Blo 1421530 3200381 := bbase (se 3 (by rfl) ⟨600071, by rfl⟩ : syracuseStep 3200381 = 1200143) (by norm_num)
theorem B4797845 : Blo 1421530 4797845 := bbase (se 6 (by rfl) ⟨112449, by rfl⟩ : syracuseStep 4797845 = 224899) (by norm_num)
theorem B1799597 : Blo 1421530 1799597 := bbase (se 3 (by rfl) ⟨337424, by rfl⟩ : syracuseStep 1799597 = 674849) (by norm_num)
theorem B3200453 : Blo 1421530 3200453 := bbase (se 4 (by rfl) ⟨300042, by rfl⟩ : syracuseStep 3200453 = 600085) (by norm_num)
theorem B2340317 : Blo 1421530 2340317 := bbase (se 3 (by rfl) ⟨438809, by rfl⟩ : syracuseStep 2340317 = 877619) (by norm_num)
theorem B1799653 : Blo 1421530 1799653 := bbase (se 4 (by rfl) ⟨168717, by rfl⟩ : syracuseStep 1799653 = 337435) (by norm_num)
theorem B3200525 : Blo 1421530 3200525 := bbase (se 3 (by rfl) ⟨600098, by rfl⟩ : syracuseStep 3200525 = 1200197) (by norm_num)
theorem B4052501 : Blo 1421530 4052501 := bbase (se 6 (by rfl) ⟨94980, by rfl⟩ : syracuseStep 4052501 = 189961) (by norm_num)
theorem B1799749 : Blo 1421530 1799749 := bbase (se 4 (by rfl) ⟨168726, by rfl⟩ : syracuseStep 1799749 = 337453) (by norm_num)
theorem B5404229 : Blo 1421530 5404229 := bbase (se 4 (by rfl) ⟨506646, by rfl⟩ : syracuseStep 5404229 = 1013293) (by norm_num)
theorem B2700877 : Blo 1421530 2700877 := bbase (se 3 (by rfl) ⟨506414, by rfl⟩ : syracuseStep 2700877 = 1012829) (by norm_num)
theorem B3200597 : Blo 1421530 3200597 := bbase (se 8 (by rfl) ⟨18753, by rfl⟩ : syracuseStep 3200597 = 37507) (by norm_num)
theorem B3602029 : Blo 1421530 3602029 := bbase (se 3 (by rfl) ⟨675380, by rfl⟩ : syracuseStep 3602029 = 1350761) (by norm_num)
theorem B8648309 : Blo 1421530 8648309 := bbase (se 5 (by rfl) ⟨405389, by rfl⟩ : syracuseStep 8648309 = 810779) (by norm_num)
theorem B3200669 : Blo 1421530 3200669 := bbase (se 3 (by rfl) ⟨600125, by rfl⟩ : syracuseStep 3200669 = 1200251) (by norm_num)
theorem B4052693 : Blo 1421530 4052693 := bbase (se 7 (by rfl) ⟨47492, by rfl⟩ : syracuseStep 4052693 = 94985) (by norm_num)
theorem B2701021 : Blo 1421530 2701021 := bbase (se 3 (by rfl) ⟨506441, by rfl⟩ : syracuseStep 2701021 = 1012883) (by norm_num)
theorem B3602141 : Blo 1421530 3602141 := bbase (se 3 (by rfl) ⟨675401, by rfl⟩ : syracuseStep 3602141 = 1350803) (by norm_num)
theorem B3200741 : Blo 1421530 3200741 := bbase (se 4 (by rfl) ⟨300069, by rfl⟩ : syracuseStep 3200741 = 600139) (by norm_num)
theorem B1799921 : Blo 1421530 1799921 := bbase (se 2 (by rfl) ⟨674970, by rfl⟩ : syracuseStep 1799921 = 1349941) (by norm_num)
theorem B7198469 : Blo 1421530 7198469 := bbase (se 4 (by rfl) ⟨674856, by rfl⟩ : syracuseStep 7198469 = 1349713) (by norm_num)
theorem B1799977 : Blo 1421530 1799977 := bbase (se 2 (by rfl) ⟨674991, by rfl⟩ : syracuseStep 1799977 = 1349983) (by norm_num)
theorem B3200813 : Blo 1421530 3200813 := bbase (se 3 (by rfl) ⟨600152, by rfl⟩ : syracuseStep 3200813 = 1200305) (by norm_num)
theorem B4798277 : Blo 1421530 4798277 := bbase (se 4 (by rfl) ⟨449838, by rfl⟩ : syracuseStep 4798277 = 899677) (by norm_num)
theorem B3200885 : Blo 1421530 3200885 := bbase (se 5 (by rfl) ⟨150041, by rfl⟩ : syracuseStep 3200885 = 300083) (by norm_num)
theorem B2701181 : Blo 1421530 2701181 := bbase (se 3 (by rfl) ⟨506471, by rfl⟩ : syracuseStep 2701181 = 1012943) (by norm_num)
theorem B1709957 : Blo 1421530 1709957 := bbase (se 4 (by rfl) ⟨160308, by rfl⟩ : syracuseStep 1709957 = 320617) (by norm_num)
theorem B1800073 : Blo 1421530 1800073 := bbase (se 2 (by rfl) ⟨675027, by rfl⟩ : syracuseStep 1800073 = 1350055) (by norm_num)
theorem B3463069 : Blo 1421530 3463069 := bbase (se 3 (by rfl) ⟨649325, by rfl⟩ : syracuseStep 3463069 = 1298651) (by norm_num)
theorem B3602333 : Blo 1421530 3602333 := bbase (se 3 (by rfl) ⟨675437, by rfl⟩ : syracuseStep 3602333 = 1350875) (by norm_num)
theorem B3200957 : Blo 1421530 3200957 := bbase (se 3 (by rfl) ⟨600179, by rfl⟩ : syracuseStep 3200957 = 1200359) (by norm_num)
theorem B3037189 : Blo 1421530 3037189 := bbase (se 4 (by rfl) ⟨284736, by rfl⟩ : syracuseStep 3037189 = 569473) (by norm_num)
theorem B3201029 : Blo 1421530 3201029 := bbase (se 4 (by rfl) ⟨300096, by rfl⟩ : syracuseStep 3201029 = 600193) (by norm_num)
theorem B2701325 : Blo 1421530 2701325 := bbase (se 3 (by rfl) ⟨506498, by rfl⟩ : syracuseStep 2701325 = 1012997) (by norm_num)
theorem B1800245 : Blo 1421530 1800245 := bbase (se 5 (by rfl) ⟨84386, by rfl⟩ : syracuseStep 1800245 = 168773) (by norm_num)
theorem B6486085 : Blo 1421530 6486085 := bbase (se 4 (by rfl) ⟨608070, by rfl⟩ : syracuseStep 6486085 = 1216141) (by norm_num)
theorem B3201101 : Blo 1421530 3201101 := bbase (se 3 (by rfl) ⟨600206, by rfl⟩ : syracuseStep 3201101 = 1200413) (by norm_num)
theorem B49305685 : Blo 1421530 49305685 := bbase (se 8 (by rfl) ⟨288900, by rfl⟩ : syracuseStep 49305685 = 577801) (by norm_num)
theorem B1800301 : Blo 1421530 1800301 := bbase (se 3 (by rfl) ⟨337556, by rfl⟩ : syracuseStep 1800301 = 675113) (by norm_num)
theorem B2562173 : Blo 1421530 2562173 := bbase (se 3 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 2562173 = 960815) (by norm_num)
theorem B3037333 : Blo 1421530 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B6076565 : Blo 1421530 6076565 := bbase (se 6 (by rfl) ⟨142419, by rfl⟩ : syracuseStep 6076565 = 284839) (by norm_num)
theorem B3201173 : Blo 1421530 3201173 := bbase (se 6 (by rfl) ⟨75027, by rfl⟩ : syracuseStep 3201173 = 150055) (by norm_num)
theorem B1800397 : Blo 1421530 1800397 := bbase (se 3 (by rfl) ⟨337574, by rfl⟩ : syracuseStep 1800397 = 675149) (by norm_num)
theorem B3201245 : Blo 1421530 3201245 := bbase (se 3 (by rfl) ⟨600233, by rfl⟩ : syracuseStep 3201245 = 1200467) (by norm_num)
theorem B4798709 : Blo 1421530 4798709 := bbase (se 5 (by rfl) ⟨224939, by rfl⟩ : syracuseStep 4798709 = 449879) (by norm_num)
theorem B3602677 : Blo 1421530 3602677 := bbase (se 5 (by rfl) ⟨168875, by rfl⟩ : syracuseStep 3602677 = 337751) (by norm_num)
theorem B3201317 : Blo 1421530 3201317 := bbase (se 4 (by rfl) ⟨300123, by rfl⟩ : syracuseStep 3201317 = 600247) (by norm_num)
theorem B2701613 : Blo 1421530 2701613 := bbase (se 3 (by rfl) ⟨506552, by rfl⟩ : syracuseStep 2701613 = 1013105) (by norm_num)
theorem B3602789 : Blo 1421530 3602789 := bbase (se 4 (by rfl) ⟨337761, by rfl⟩ : syracuseStep 3602789 = 675523) (by norm_num)
theorem B3201389 : Blo 1421530 3201389 := bbase (se 3 (by rfl) ⟨600260, by rfl⟩ : syracuseStep 3201389 = 1200521) (by norm_num)
theorem B1800569 : Blo 1421530 1800569 := bbase (se 2 (by rfl) ⟨675213, by rfl⟩ : syracuseStep 1800569 = 1350427) (by norm_num)
theorem B1800625 : Blo 1421530 1800625 := bbase (se 2 (by rfl) ⟨675234, by rfl⟩ : syracuseStep 1800625 = 1350469) (by norm_num)
theorem B6076853 : Blo 1421530 6076853 := bbase (se 5 (by rfl) ⟨284852, by rfl⟩ : syracuseStep 6076853 = 569705) (by norm_num)
theorem B3201461 : Blo 1421530 3201461 := bbase (se 5 (by rfl) ⟨150068, by rfl⟩ : syracuseStep 3201461 = 300137) (by norm_num)
theorem B5126597 : Blo 1421530 5126597 := bbase (se 4 (by rfl) ⟨480618, by rfl⟩ : syracuseStep 5126597 = 961237) (by norm_num)
theorem B2701765 : Blo 1421530 2701765 := bbase (se 4 (by rfl) ⟨253290, by rfl⟩ : syracuseStep 2701765 = 506581) (by norm_num)
theorem B16194005 : Blo 1421530 16194005 := bbase (se 7 (by rfl) ⟨189773, by rfl⟩ : syracuseStep 16194005 = 379547) (by norm_num)
theorem B3201533 : Blo 1421530 3201533 := bbase (se 3 (by rfl) ⟨600287, by rfl⟩ : syracuseStep 3201533 = 1200575) (by norm_num)
theorem B3037709 : Blo 1421530 3037709 := bbase (se 3 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 3037709 = 1139141) (by norm_num)
theorem B1800721 : Blo 1421530 1800721 := bbase (se 2 (by rfl) ⟨675270, by rfl⟩ : syracuseStep 1800721 = 1350541) (by norm_num)
theorem B3242533 : Blo 1421530 3242533 := bbase (se 4 (by rfl) ⟨303987, by rfl⟩ : syracuseStep 3242533 = 607975) (by norm_num)
theorem B5765669 : Blo 1421530 5765669 := bbase (se 4 (by rfl) ⟨540531, by rfl⟩ : syracuseStep 5765669 = 1081063) (by norm_num)
theorem B3602981 : Blo 1421530 3602981 := bbase (se 4 (by rfl) ⟨337779, by rfl⟩ : syracuseStep 3602981 = 675559) (by norm_num)
theorem B3201605 : Blo 1421530 3201605 := bbase (se 4 (by rfl) ⟨300150, by rfl⟩ : syracuseStep 3201605 = 600301) (by norm_num)
theorem B3201677 : Blo 1421530 3201677 := bbase (se 3 (by rfl) ⟨600314, by rfl⟩ : syracuseStep 3201677 = 1200629) (by norm_num)
theorem B4799141 : Blo 1421530 4799141 := bbase (se 4 (by rfl) ⟨449919, by rfl⟩ : syracuseStep 4799141 = 899839) (by norm_num)
theorem B4053685 : Blo 1421530 4053685 := bbase (se 5 (by rfl) ⟨190016, by rfl⟩ : syracuseStep 4053685 = 380033) (by norm_num)
theorem B2398909 : Blo 1421530 2398909 := bbase (se 3 (by rfl) ⟨449795, by rfl⟩ : syracuseStep 2398909 = 899591) (by norm_num)
theorem B1800893 : Blo 1421530 1800893 := bbase (se 3 (by rfl) ⟨337667, by rfl⟩ : syracuseStep 1800893 = 675335) (by norm_num)
theorem B3201749 : Blo 1421530 3201749 := bbase (se 7 (by rfl) ⟨37520, by rfl⟩ : syracuseStep 3201749 = 75041) (by norm_num)
theorem B5126885 : Blo 1421530 5126885 := bbase (se 4 (by rfl) ⟨480645, by rfl⟩ : syracuseStep 5126885 = 961291) (by norm_num)
theorem B1800949 : Blo 1421530 1800949 := bbase (se 5 (by rfl) ⟨84419, by rfl⟩ : syracuseStep 1800949 = 168839) (by norm_num)
theorem B2702069 : Blo 1421530 2702069 := bbase (se 5 (by rfl) ⟨126659, by rfl⟩ : syracuseStep 2702069 = 253319) (by norm_num)
theorem B2161421 : Blo 1421530 2161421 := bbase (se 3 (by rfl) ⟨405266, by rfl⟩ : syracuseStep 2161421 = 810533) (by norm_num)
theorem B2398997 : Blo 1421530 2398997 := bbase (se 6 (by rfl) ⟨56226, by rfl⟩ : syracuseStep 2398997 = 112453) (by norm_num)
theorem B3201821 : Blo 1421530 3201821 := bbase (se 3 (by rfl) ⟨600341, by rfl⟩ : syracuseStep 3201821 = 1200683) (by norm_num)
theorem B7297877 : Blo 1421530 7297877 := bbase (se 9 (by rfl) ⟨21380, by rfl⟩ : syracuseStep 7297877 = 42761) (by norm_num)
theorem B1801045 : Blo 1421530 1801045 := bbase (se 9 (by rfl) ⟨5276, by rfl⟩ : syracuseStep 1801045 = 10553) (by norm_num)
theorem B3201893 : Blo 1421530 3201893 := bbase (se 4 (by rfl) ⟨300177, by rfl⟩ : syracuseStep 3201893 = 600355) (by norm_num)
theorem B2882413 : Blo 1421530 2882413 := bbase (se 3 (by rfl) ⟨540452, by rfl⟩ : syracuseStep 2882413 = 1080905) (by norm_num)
theorem B3038077 : Blo 1421530 3038077 := bbase (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) (by norm_num)
theorem B2399125 : Blo 1421530 2399125 := bbase (se 6 (by rfl) ⟨56229, by rfl⟩ : syracuseStep 2399125 = 112459) (by norm_num)
theorem B3201965 : Blo 1421530 3201965 := bbase (se 3 (by rfl) ⟨600368, by rfl⟩ : syracuseStep 3201965 = 1200737) (by norm_num)
theorem B2399213 : Blo 1421530 2399213 := bbase (se 3 (by rfl) ⟨449852, by rfl⟩ : syracuseStep 2399213 = 899705) (by norm_num)
theorem B3202037 : Blo 1421530 3202037 := bbase (se 5 (by rfl) ⟨150095, by rfl⟩ : syracuseStep 3202037 = 300191) (by norm_num)
theorem B1801217 : Blo 1421530 1801217 := bbase (se 2 (by rfl) ⟨675456, by rfl⟩ : syracuseStep 1801217 = 1350913) (by norm_num)
theorem B7199765 : Blo 1421530 7199765 := bbase (se 6 (by rfl) ⟨168744, by rfl⟩ : syracuseStep 7199765 = 337489) (by norm_num)
theorem B1801273 : Blo 1421530 1801273 := bbase (se 2 (by rfl) ⟨675477, by rfl⟩ : syracuseStep 1801273 = 1350955) (by norm_num)
theorem B3202109 : Blo 1421530 3202109 := bbase (se 3 (by rfl) ⟨600395, by rfl⟩ : syracuseStep 3202109 = 1200791) (by norm_num)
theorem B4799573 : Blo 1421530 4799573 := bbase (se 8 (by rfl) ⟨28122, by rfl⟩ : syracuseStep 4799573 = 56245) (by norm_num)
theorem B2399341 : Blo 1421530 2399341 := bbase (se 3 (by rfl) ⟨449876, by rfl⟩ : syracuseStep 2399341 = 899753) (by norm_num)
theorem B5397637 : Blo 1421530 5397637 := bbase (se 4 (by rfl) ⟨506028, by rfl⟩ : syracuseStep 5397637 = 1012057) (by norm_num)
theorem B3202181 : Blo 1421530 3202181 := bbase (se 4 (by rfl) ⟨300204, by rfl⟩ : syracuseStep 3202181 = 600409) (by norm_num)
theorem B1801369 : Blo 1421530 1801369 := bbase (se 2 (by rfl) ⟨675513, by rfl⟩ : syracuseStep 1801369 = 1351027) (by norm_num)
theorem B6077605 : Blo 1421530 6077605 := bbase (se 4 (by rfl) ⟨569775, by rfl⟩ : syracuseStep 6077605 = 1139551) (by norm_num)
theorem B2399429 : Blo 1421530 2399429 := bbase (se 4 (by rfl) ⟨224946, by rfl⟩ : syracuseStep 2399429 = 449893) (by norm_num)
theorem B3202253 : Blo 1421530 3202253 := bbase (se 3 (by rfl) ⟨600422, by rfl⟩ : syracuseStep 3202253 = 1200845) (by norm_num)
theorem B1441037 : Blo 1421530 1441037 := bbase (se 3 (by rfl) ⟨270194, by rfl⟩ : syracuseStep 1441037 = 540389) (by norm_num)
theorem B3202325 : Blo 1421530 3202325 := bbase (se 6 (by rfl) ⟨75054, by rfl⟩ : syracuseStep 3202325 = 150109) (by norm_num)
theorem B4554053 : Blo 1421530 4554053 := bbase (se 4 (by rfl) ⟨426942, by rfl⟩ : syracuseStep 4554053 = 853885) (by norm_num)
theorem B2399557 : Blo 1421530 2399557 := bbase (se 4 (by rfl) ⟨224958, by rfl⟩ : syracuseStep 2399557 = 449917) (by norm_num)
theorem B1801541 : Blo 1421530 1801541 := bbase (se 4 (by rfl) ⟨168894, by rfl⟩ : syracuseStep 1801541 = 337789) (by norm_num)
theorem B3202397 : Blo 1421530 3202397 := bbase (se 3 (by rfl) ⟨600449, by rfl⟩ : syracuseStep 3202397 = 1200899) (by norm_num)
theorem B10255733 : Blo 1421530 10255733 := bbase (se 5 (by rfl) ⟨480737, by rfl⟩ : syracuseStep 10255733 = 961475) (by norm_num)
theorem B1801597 : Blo 1421530 1801597 := bbase (se 3 (by rfl) ⟨337799, by rfl⟩ : syracuseStep 1801597 = 675599) (by norm_num)
theorem B2399645 : Blo 1421530 2399645 := bbase (se 3 (by rfl) ⟨449933, by rfl⟩ : syracuseStep 2399645 = 899867) (by norm_num)
theorem B3202469 : Blo 1421530 3202469 := bbase (se 4 (by rfl) ⟨300231, by rfl⟩ : syracuseStep 3202469 = 600463) (by norm_num)
theorem B2563501 : Blo 1421530 2563501 := bbase (se 3 (by rfl) ⟨480656, by rfl⟩ : syracuseStep 2563501 = 961313) (by norm_num)
theorem B5397941 : Blo 1421530 5397941 := bbase (se 5 (by rfl) ⟨253028, by rfl⟩ : syracuseStep 5397941 = 506057) (by norm_num)
theorem B3202541 : Blo 1421530 3202541 := bbase (se 3 (by rfl) ⟨600476, by rfl⟩ : syracuseStep 3202541 = 1200953) (by norm_num)
theorem B4554245 : Blo 1421530 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B4800005 : Blo 1421530 4800005 := bbase (se 4 (by rfl) ⟨450000, by rfl⟩ : syracuseStep 4800005 = 900001) (by norm_num)
theorem B2399773 : Blo 1421530 2399773 := bbase (se 3 (by rfl) ⟨449957, by rfl⟩ : syracuseStep 2399773 = 899915) (by norm_num)
theorem B1539629 : Blo 1421530 1539629 := bbase (se 3 (by rfl) ⟨288680, by rfl⟩ : syracuseStep 1539629 = 577361) (by norm_num)
theorem B3202613 : Blo 1421530 3202613 := bbase (se 5 (by rfl) ⟨150122, by rfl⟩ : syracuseStep 3202613 = 300245) (by norm_num)
theorem B2563645 : Blo 1421530 2563645 := bbase (se 3 (by rfl) ⟨480683, by rfl⟩ : syracuseStep 2563645 = 961367) (by norm_num)
theorem B2924093 : Blo 1421530 2924093 := bbase (se 3 (by rfl) ⟨548267, by rfl⟩ : syracuseStep 2924093 = 1096535) (by norm_num)
theorem B20012629 : Blo 1421530 20012629 := bbase (se 8 (by rfl) ⟨117261, by rfl⟩ : syracuseStep 20012629 = 234523) (by norm_num)
theorem B2399861 : Blo 1421530 2399861 := bbase (se 5 (by rfl) ⟨112493, by rfl⟩ : syracuseStep 2399861 = 224987) (by norm_num)
theorem B3202685 : Blo 1421530 3202685 := bbase (se 3 (by rfl) ⟨600503, by rfl⟩ : syracuseStep 3202685 = 1201007) (by norm_num)
theorem B3415733 : Blo 1421530 3415733 := bbase (se 5 (by rfl) ⟨160112, by rfl⟩ : syracuseStep 3415733 = 320225) (by norm_num)
theorem B3202757 : Blo 1421530 3202757 := bbase (se 4 (by rfl) ⟨300258, by rfl⟩ : syracuseStep 3202757 = 600517) (by norm_num)
theorem B2277077 : Blo 1421530 2277077 := bbase (se 7 (by rfl) ⟨26684, by rfl⟩ : syracuseStep 2277077 = 53369) (by norm_num)
theorem B2399989 : Blo 1421530 2399989 := bbase (se 5 (by rfl) ⟨112499, by rfl⟩ : syracuseStep 2399989 = 224999) (by norm_num)
theorem B3243773 : Blo 1421530 3243773 := bbase (se 3 (by rfl) ⟨608207, by rfl⟩ : syracuseStep 3243773 = 1216415) (by norm_num)
theorem B3202829 : Blo 1421530 3202829 := bbase (se 3 (by rfl) ⟨600530, by rfl⟩ : syracuseStep 3202829 = 1201061) (by norm_num)
theorem B2400077 : Blo 1421530 2400077 := bbase (se 3 (by rfl) ⟨450014, by rfl⟩ : syracuseStep 2400077 = 900029) (by norm_num)
theorem B3202901 : Blo 1421530 3202901 := bbase (se 9 (by rfl) ⟨9383, by rfl⟩ : syracuseStep 3202901 = 18767) (by norm_num)
theorem B5128037 : Blo 1421530 5128037 := bbase (se 4 (by rfl) ⟨480753, by rfl⟩ : syracuseStep 5128037 = 961507) (by norm_num)
theorem B6078341 : Blo 1421530 6078341 := bbase (se 4 (by rfl) ⟨569844, by rfl⟩ : syracuseStep 6078341 = 1139689) (by norm_num)
theorem B4800437 : Blo 1421530 4800437 := bbase (se 5 (by rfl) ⟨225020, by rfl⟩ : syracuseStep 4800437 = 450041) (by norm_num)
theorem B2400205 : Blo 1421530 2400205 := bbase (se 3 (by rfl) ⟨450038, by rfl⟩ : syracuseStep 2400205 = 900077) (by norm_num)
theorem B2883541 : Blo 1421530 2883541 := bbase (se 7 (by rfl) ⟨33791, by rfl⟩ : syracuseStep 2883541 = 67583) (by norm_num)
theorem B2564077 : Blo 1421530 2564077 := bbase (se 3 (by rfl) ⟨480764, by rfl⟩ : syracuseStep 2564077 = 961529) (by norm_num)
theorem B10805237 : Blo 1421530 10805237 := bbase (se 5 (by rfl) ⟨506495, by rfl⟩ : syracuseStep 10805237 = 1012991) (by norm_num)
theorem B2400259 : Blo 1421530 2400259 := bstep (se 1 (by rfl) ⟨1800194, by rfl⟩ : syracuseStep 2400259 = 3600389) B3600389
theorem B18219077 : Blo 1421530 18219077 := bstep (se 4 (by rfl) ⟨1708038, by rfl⟩ : syracuseStep 18219077 = 3416077) B3416077
theorem B6078563 : Blo 1421530 6078563 := bstep (se 1 (by rfl) ⟨4558922, by rfl⟩ : syracuseStep 6078563 = 9117845) B9117845
theorem B65740913 : Blo 1421530 65740913 := bstep (se 2 (by rfl) ⟨24652842, by rfl⟩ : syracuseStep 65740913 = 49305685) B49305685
theorem B4800653 : Blo 1421530 4800653 := bstep (se 3 (by rfl) ⟨900122, by rfl⟩ : syracuseStep 4800653 = 1800245) B1800245
theorem B2400401 : Blo 1421530 2400401 := bstep (se 2 (by rfl) ⟨900150, by rfl⟩ : syracuseStep 2400401 = 1800301) B1800301
theorem B2277539 : Blo 1421530 2277539 := bstep (se 1 (by rfl) ⟨1708154, by rfl⟩ : syracuseStep 2277539 = 3416309) B3416309
theorem B8765617 : Blo 1421530 8765617 := bstep (se 2 (by rfl) ⟨3287106, by rfl⟩ : syracuseStep 8765617 = 6574213) B6574213
theorem B1925299 : Blo 1421530 1925299 := bstep (se 1 (by rfl) ⟨1443974, by rfl⟩ : syracuseStep 1925299 = 2887949) B2887949
theorem B4800707 : Blo 1421530 4800707 := bstep (se 1 (by rfl) ⟨3600530, by rfl⟩ : syracuseStep 4800707 = 7201061) B7201061
theorem B9109745 : Blo 1421530 9109745 := bstep (se 2 (by rfl) ⟨3416154, by rfl⟩ : syracuseStep 9109745 = 6832309) B6832309
theorem B2400529 : Blo 1421530 2400529 := bstep (se 2 (by rfl) ⟨900198, by rfl⟩ : syracuseStep 2400529 = 1800397) B1800397
theorem B2277667 : Blo 1421530 2277667 := bstep (se 1 (by rfl) ⟨1708250, by rfl⟩ : syracuseStep 2277667 = 3416501) B3416501
theorem B2400563 : Blo 1421530 2400563 := bstep (se 1 (by rfl) ⟨1800422, by rfl⟩ : syracuseStep 2400563 = 3600845) B3600845
theorem B5398883 : Blo 1421530 5398883 := bstep (se 1 (by rfl) ⟨4049162, by rfl⟩ : syracuseStep 5398883 = 8098325) B8098325
theorem B1622371 : Blo 1421530 1622371 := bstep (se 1 (by rfl) ⟨1216778, by rfl⟩ : syracuseStep 1622371 = 2433557) B2433557
theorem B2400691 : Blo 1421530 2400691 := bstep (se 1 (by rfl) ⟨1800518, by rfl⟩ : syracuseStep 2400691 = 3601037) B3601037
theorem B4800977 : Blo 1421530 4800977 := bstep (se 2 (by rfl) ⟨1800366, by rfl⟩ : syracuseStep 4800977 = 3600733) B3600733
theorem B12976625 : Blo 1421530 12976625 := bstep (se 2 (by rfl) ⟨4866234, by rfl⟩ : syracuseStep 12976625 = 9732469) B9732469
theorem B2400833 : Blo 1421530 2400833 := bstep (se 2 (by rfl) ⟨900312, by rfl⟩ : syracuseStep 2400833 = 1800625) B1800625
theorem B24306317 : Blo 1421530 24306317 := bstep (se 3 (by rfl) ⟨4557434, by rfl⟩ : syracuseStep 24306317 = 9114869) B9114869
theorem B2400961 : Blo 1421530 2400961 := bstep (se 2 (by rfl) ⟨900360, by rfl⟩ : syracuseStep 2400961 = 1800721) B1800721
theorem B3842765 : Blo 1421530 3842765 := bstep (se 3 (by rfl) ⟨720518, by rfl⟩ : syracuseStep 3842765 = 1441037) B1441037
theorem B2400995 : Blo 1421530 2400995 := bstep (se 1 (by rfl) ⟨1800746, by rfl⟩ : syracuseStep 2400995 = 3601493) B3601493
theorem B4866851 : Blo 1421530 4866851 := bstep (se 1 (by rfl) ⟨3650138, by rfl⟩ : syracuseStep 4866851 = 7300277) B7300277
theorem B3040067 : Blo 1421530 3040067 := bstep (se 1 (by rfl) ⟨2280050, by rfl⟩ : syracuseStep 3040067 = 4560101) B4560101
theorem B2024291 : Blo 1421530 2024291 := bstep (se 1 (by rfl) ⟨1518218, by rfl⟩ : syracuseStep 2024291 = 3036437) B3036437
theorem B2401123 : Blo 1421530 2401123 := bstep (se 1 (by rfl) ⟨1800842, by rfl⟩ : syracuseStep 2401123 = 3601685) B3601685
theorem B29197169 : Blo 1421530 29197169 := bstep (se 2 (by rfl) ⟨10948938, by rfl⟩ : syracuseStep 29197169 = 21897877) B21897877
theorem B4801517 : Blo 1421530 4801517 := bstep (se 3 (by rfl) ⟨900284, by rfl⟩ : syracuseStep 4801517 = 1800569) B1800569
theorem B2278385 : Blo 1421530 2278385 := bstep (se 2 (by rfl) ⟨854394, by rfl⟩ : syracuseStep 2278385 = 1708789) B1708789
theorem B2401265 : Blo 1421530 2401265 := bstep (se 2 (by rfl) ⟨900474, by rfl⟩ : syracuseStep 2401265 = 1800949) B1800949
theorem B4801571 : Blo 1421530 4801571 := bstep (se 1 (by rfl) ⟨3601178, by rfl⟩ : syracuseStep 4801571 = 7202357) B7202357
theorem B2401393 : Blo 1421530 2401393 := bstep (se 2 (by rfl) ⟨900522, by rfl⟩ : syracuseStep 2401393 = 1801045) B1801045
theorem B3843217 : Blo 1421530 3843217 := bstep (se 2 (by rfl) ⟨1441206, by rfl⟩ : syracuseStep 3843217 = 2882413) B2882413
theorem B2401427 : Blo 1421530 2401427 := bstep (se 1 (by rfl) ⟨1801070, by rfl⟩ : syracuseStep 2401427 = 3602141) B3602141
theorem B2278577 : Blo 1421530 2278577 := bstep (se 2 (by rfl) ⟨854466, by rfl⟩ : syracuseStep 2278577 = 1708933) B1708933
theorem B7202033 : Blo 1421530 7202033 := bstep (se 2 (by rfl) ⟨2700762, by rfl⟩ : syracuseStep 7202033 = 5401525) B5401525
theorem B2401555 : Blo 1421530 2401555 := bstep (se 1 (by rfl) ⟨1801166, by rfl⟩ : syracuseStep 2401555 = 3602333) B3602333
theorem B4801841 : Blo 1421530 4801841 := bstep (se 2 (by rfl) ⟨1800690, by rfl⟩ : syracuseStep 4801841 = 3601381) B3601381
theorem B27329845 : Blo 1421530 27329845 := bstep (se 5 (by rfl) ⟨1281086, by rfl⟩ : syracuseStep 27329845 = 2562173) B2562173
theorem B5399885 : Blo 1421530 5399885 := bstep (se 3 (by rfl) ⟨1012478, by rfl⟩ : syracuseStep 5399885 = 2024957) B2024957
theorem B2401697 : Blo 1421530 2401697 := bstep (se 2 (by rfl) ⟨900636, by rfl⟩ : syracuseStep 2401697 = 1801273) B1801273
theorem B6161827 : Blo 1421530 6161827 := bstep (se 1 (by rfl) ⟨4621370, by rfl⟩ : syracuseStep 6161827 = 9242741) B9242741
theorem B3081649 : Blo 1421530 3081649 := bstep (se 2 (by rfl) ⟨1155618, by rfl⟩ : syracuseStep 3081649 = 2311237) B2311237
theorem B4867523 : Blo 1421530 4867523 := bstep (se 1 (by rfl) ⟨3650642, by rfl⟩ : syracuseStep 4867523 = 7301285) B7301285
theorem B5768653 : Blo 1421530 5768653 := bstep (se 3 (by rfl) ⟨1081622, by rfl⟩ : syracuseStep 5768653 = 2163245) B2163245
theorem B2024929 : Blo 1421530 2024929 := bstep (se 2 (by rfl) ⟨759348, by rfl⟩ : syracuseStep 2024929 = 1518697) B1518697
theorem B4326929 : Blo 1421530 4326929 := bstep (se 2 (by rfl) ⟨1622598, by rfl⟩ : syracuseStep 4326929 = 3245197) B3245197
theorem B2401825 : Blo 1421530 2401825 := bstep (se 2 (by rfl) ⟨900684, by rfl⟩ : syracuseStep 2401825 = 1801369) B1801369
theorem B8103473 : Blo 1421530 8103473 := bstep (se 2 (by rfl) ⟨3038802, by rfl⟩ : syracuseStep 8103473 = 6077605) B6077605
theorem B2401859 : Blo 1421530 2401859 := bstep (se 1 (by rfl) ⟨1801394, by rfl⟩ : syracuseStep 2401859 = 3602789) B3602789
theorem B3417731 : Blo 1421530 3417731 := bstep (se 1 (by rfl) ⟨2563298, by rfl⟩ : syracuseStep 3417731 = 5126597) B5126597
theorem B23062157 : Blo 1421530 23062157 := bstep (se 3 (by rfl) ⟨4324154, by rfl⟩ : syracuseStep 23062157 = 8648309) B8648309
theorem B3843779 : Blo 1421530 3843779 := bstep (se 1 (by rfl) ⟨2882834, by rfl⟩ : syracuseStep 3843779 = 5765669) B5765669
theorem B2401987 : Blo 1421530 2401987 := bstep (se 1 (by rfl) ⟨1801490, by rfl⟩ : syracuseStep 2401987 = 3602981) B3602981
theorem B2025265 : Blo 1421530 2025265 := bstep (se 2 (by rfl) ⟨759474, by rfl⟩ : syracuseStep 2025265 = 1518949) B1518949
theorem B6080305 : Blo 1421530 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B3417923 : Blo 1421530 3417923 := bstep (se 1 (by rfl) ⟨2563442, by rfl⟩ : syracuseStep 3417923 = 5126885) B5126885
theorem B4802381 : Blo 1421530 4802381 := bstep (se 3 (by rfl) ⟨900446, by rfl⟩ : syracuseStep 4802381 = 1800893) B1800893
theorem B2402129 : Blo 1421530 2402129 := bstep (se 2 (by rfl) ⟨900798, by rfl⟩ : syracuseStep 2402129 = 1801597) B1801597
theorem B1599331 : Blo 1421530 1599331 := bstep (se 1 (by rfl) ⟨1199498, by rfl⟩ : syracuseStep 1599331 = 2398997) B2398997
theorem B4802435 : Blo 1421530 4802435 := bstep (se 1 (by rfl) ⟨3601826, by rfl⟩ : syracuseStep 4802435 = 7203653) B7203653
theorem B9111437 : Blo 1421530 9111437 := bstep (se 3 (by rfl) ⟨1708394, by rfl⟩ : syracuseStep 9111437 = 3416789) B3416789
theorem B10807181 : Blo 1421530 10807181 := bstep (se 3 (by rfl) ⟨2026346, by rfl⟩ : syracuseStep 10807181 = 4052693) B4052693
theorem B3418001 : Blo 1421530 3418001 := bstep (se 2 (by rfl) ⟨1281750, by rfl⟩ : syracuseStep 3418001 = 2563501) B2563501
theorem B1599475 : Blo 1421530 1599475 := bstep (se 1 (by rfl) ⟨1199606, by rfl⟩ : syracuseStep 1599475 = 2399213) B2399213
theorem B3418193 : Blo 1421530 3418193 := bstep (se 2 (by rfl) ⟨1281822, by rfl⟩ : syracuseStep 3418193 = 2563645) B2563645
theorem B26683505 : Blo 1421530 26683505 := bstep (se 2 (by rfl) ⟨10006314, by rfl⟩ : syracuseStep 26683505 = 20012629) B20012629
theorem B1599619 : Blo 1421530 1599619 := bstep (se 1 (by rfl) ⟨1199714, by rfl⟩ : syracuseStep 1599619 = 2399429) B2399429
theorem B4802705 : Blo 1421530 4802705 := bstep (se 2 (by rfl) ⟨1801014, by rfl⟩ : syracuseStep 4802705 = 3602029) B3602029
theorem B12159173 : Blo 1421530 12159173 := bstep (se 4 (by rfl) ⟨1139922, by rfl⟩ : syracuseStep 12159173 = 2279845) B2279845
theorem B3598577 : Blo 1421530 3598577 := bstep (se 2 (by rfl) ⟨1349466, by rfl⟩ : syracuseStep 3598577 = 2698933) B2698933
theorem B1599763 : Blo 1421530 1599763 := bstep (se 1 (by rfl) ⟨1199822, by rfl⟩ : syracuseStep 1599763 = 2399645) B2399645
theorem B3598627 : Blo 1421530 3598627 := bstep (se 1 (by rfl) ⟨2698970, by rfl⟩ : syracuseStep 3598627 = 5397941) B5397941
theorem B2132321 : Blo 1421530 2132321 := bstep (se 2 (by rfl) ⟨799620, by rfl⟩ : syracuseStep 2132321 = 1599241) B1599241
theorem B2132339 : Blo 1421530 2132339 := bstep (se 1 (by rfl) ⟨1599254, by rfl⟩ : syracuseStep 2132339 = 3198509) B3198509
theorem B2025857 : Blo 1421530 2025857 := bstep (se 2 (by rfl) ⟨759696, by rfl⟩ : syracuseStep 2025857 = 1519393) B1519393
theorem B2132369 : Blo 1421530 2132369 := bstep (se 2 (by rfl) ⟨799638, by rfl⟩ : syracuseStep 2132369 = 1599277) B1599277
theorem B2132387 : Blo 1421530 2132387 := bstep (se 1 (by rfl) ⟨1599290, by rfl⟩ : syracuseStep 2132387 = 3198581) B3198581
theorem B1599907 : Blo 1421530 1599907 := bstep (se 1 (by rfl) ⟨1199930, by rfl⟩ : syracuseStep 1599907 = 2399861) B2399861
theorem B3598769 : Blo 1421530 3598769 := bstep (se 2 (by rfl) ⟨1349538, by rfl⟩ : syracuseStep 3598769 = 2699077) B2699077
theorem B2132417 : Blo 1421530 2132417 := bstep (se 2 (by rfl) ⟨799656, by rfl⟩ : syracuseStep 2132417 = 1599313) B1599313
theorem B19466693 : Blo 1421530 19466693 := bstep (se 4 (by rfl) ⟨1825002, by rfl⟩ : syracuseStep 19466693 = 3650005) B3650005
theorem B2132435 : Blo 1421530 2132435 := bstep (se 1 (by rfl) ⟨1599326, by rfl⟩ : syracuseStep 2132435 = 3198653) B3198653
theorem B30771683 : Blo 1421530 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B2132465 : Blo 1421530 2132465 := bstep (se 2 (by rfl) ⟨799674, by rfl⟩ : syracuseStep 2132465 = 1599349) B1599349
theorem B2132483 : Blo 1421530 2132483 := bstep (se 1 (by rfl) ⟨1599362, by rfl⟩ : syracuseStep 2132483 = 3198725) B3198725
theorem B2132513 : Blo 1421530 2132513 := bstep (se 2 (by rfl) ⟨799692, by rfl⟩ : syracuseStep 2132513 = 1599385) B1599385
theorem B2132531 : Blo 1421530 2132531 := bstep (se 1 (by rfl) ⟨1599398, by rfl⟩ : syracuseStep 2132531 = 3198797) B3198797
theorem B1600051 : Blo 1421530 1600051 := bstep (se 1 (by rfl) ⟨1200038, by rfl⟩ : syracuseStep 1600051 = 2400077) B2400077
theorem B3418691 : Blo 1421530 3418691 := bstep (se 1 (by rfl) ⟨2564018, by rfl⟩ : syracuseStep 3418691 = 5128037) B5128037
theorem B2132561 : Blo 1421530 2132561 := bstep (se 2 (by rfl) ⟨799710, by rfl⟩ : syracuseStep 2132561 = 1599421) B1599421
theorem B2132579 : Blo 1421530 2132579 := bstep (se 1 (by rfl) ⟨1599434, by rfl⟩ : syracuseStep 2132579 = 3198869) B3198869
theorem B3844721 : Blo 1421530 3844721 := bstep (se 2 (by rfl) ⟨1441770, by rfl⟩ : syracuseStep 3844721 = 2883541) B2883541
theorem B2132609 : Blo 1421530 2132609 := bstep (se 2 (by rfl) ⟨799728, by rfl⟩ : syracuseStep 2132609 = 1599457) B1599457
theorem B3418769 : Blo 1421530 3418769 := bstep (se 2 (by rfl) ⟨1282038, by rfl⟩ : syracuseStep 3418769 = 2564077) B2564077
theorem B2132627 : Blo 1421530 2132627 := bstep (se 1 (by rfl) ⟨1599470, by rfl⟩ : syracuseStep 2132627 = 3198941) B3198941
theorem B7203491 : Blo 1421530 7203491 := bstep (se 1 (by rfl) ⟨5402618, by rfl⟩ : syracuseStep 7203491 = 10805237) B10805237
theorem B4803245 : Blo 1421530 4803245 := bstep (se 3 (by rfl) ⟨900608, by rfl⟩ : syracuseStep 4803245 = 1801217) B1801217
theorem B2132657 : Blo 1421530 2132657 := bstep (se 2 (by rfl) ⟨799746, by rfl⟩ : syracuseStep 2132657 = 1599493) B1599493
theorem B4049585 : Blo 1421530 4049585 := bstep (se 2 (by rfl) ⟨1518594, by rfl⟩ : syracuseStep 4049585 = 3037189) B3037189
theorem B2132675 : Blo 1421530 2132675 := bstep (se 1 (by rfl) ⟨1599506, by rfl⟩ : syracuseStep 2132675 = 3199013) B3199013
theorem B1600195 : Blo 1421530 1600195 := bstep (se 1 (by rfl) ⟨1200146, by rfl⟩ : syracuseStep 1600195 = 2400293) B2400293
theorem B2132705 : Blo 1421530 2132705 := bstep (se 2 (by rfl) ⟨799764, by rfl⟩ : syracuseStep 2132705 = 1599529) B1599529
theorem B4803299 : Blo 1421530 4803299 := bstep (se 1 (by rfl) ⟨3602474, by rfl⟩ : syracuseStep 4803299 = 7204949) B7204949
theorem B2132723 : Blo 1421530 2132723 := bstep (se 1 (by rfl) ⟨1599542, by rfl⟩ : syracuseStep 2132723 = 3199085) B3199085
theorem B2132753 : Blo 1421530 2132753 := bstep (se 2 (by rfl) ⟨799782, by rfl⟩ : syracuseStep 2132753 = 1599565) B1599565
theorem B1518355 : Blo 1421530 1518355 := bstep (se 1 (by rfl) ⟨1138766, by rfl⟩ : syracuseStep 1518355 = 2277533) B2277533
theorem B2132771 : Blo 1421530 2132771 := bstep (se 1 (by rfl) ⟨1599578, by rfl⟩ : syracuseStep 2132771 = 3199157) B3199157
theorem B2132801 : Blo 1421530 2132801 := bstep (se 2 (by rfl) ⟨799800, by rfl⟩ : syracuseStep 2132801 = 1599601) B1599601
theorem B2132819 : Blo 1421530 2132819 := bstep (se 1 (by rfl) ⟨1599614, by rfl⟩ : syracuseStep 2132819 = 3199229) B3199229
theorem B1600339 : Blo 1421530 1600339 := bstep (se 1 (by rfl) ⟨1200254, by rfl⟩ : syracuseStep 1600339 = 2400509) B2400509
theorem B4557667 : Blo 1421530 4557667 := bstep (se 1 (by rfl) ⟨3418250, by rfl⟩ : syracuseStep 4557667 = 6836501) B6836501
theorem B2132849 : Blo 1421530 2132849 := bstep (se 2 (by rfl) ⟨799818, by rfl⟩ : syracuseStep 2132849 = 1599637) B1599637
theorem B4049777 : Blo 1421530 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B21900145 : Blo 1421530 21900145 := bstep (se 2 (by rfl) ⟨8212554, by rfl⟩ : syracuseStep 21900145 = 16425109) B16425109
theorem B2132867 : Blo 1421530 2132867 := bstep (se 1 (by rfl) ⟨1599650, by rfl⟩ : syracuseStep 2132867 = 3199301) B3199301
theorem B2026387 : Blo 1421530 2026387 := bstep (se 1 (by rfl) ⟨1519790, by rfl⟩ : syracuseStep 2026387 = 3039581) B3039581
theorem B2132897 : Blo 1421530 2132897 := bstep (se 2 (by rfl) ⟨799836, by rfl⟩ : syracuseStep 2132897 = 1599673) B1599673
theorem B2132915 : Blo 1421530 2132915 := bstep (se 1 (by rfl) ⟨1599686, by rfl⟩ : syracuseStep 2132915 = 3199373) B3199373
theorem B2132945 : Blo 1421530 2132945 := bstep (se 2 (by rfl) ⟨799854, by rfl⟩ : syracuseStep 2132945 = 1599709) B1599709
theorem B2132963 : Blo 1421530 2132963 := bstep (se 1 (by rfl) ⟨1599722, by rfl⟩ : syracuseStep 2132963 = 3199445) B3199445
theorem B1600483 : Blo 1421530 1600483 := bstep (se 1 (by rfl) ⟨1200362, by rfl⟩ : syracuseStep 1600483 = 2400725) B2400725
theorem B8104931 : Blo 1421530 8104931 := bstep (se 1 (by rfl) ⟨6078698, by rfl⟩ : syracuseStep 8104931 = 12157397) B12157397
theorem B4803569 : Blo 1421530 4803569 := bstep (se 2 (by rfl) ⟨1801338, by rfl⟩ : syracuseStep 4803569 = 3602677) B3602677
theorem B2132993 : Blo 1421530 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B3419153 : Blo 1421530 3419153 := bstep (se 2 (by rfl) ⟨1282182, by rfl⟩ : syracuseStep 3419153 = 2564365) B2564365
theorem B2133011 : Blo 1421530 2133011 := bstep (se 1 (by rfl) ⟨1599758, by rfl⟩ : syracuseStep 2133011 = 3199517) B3199517
theorem B2133041 : Blo 1421530 2133041 := bstep (se 2 (by rfl) ⟨799890, by rfl⟩ : syracuseStep 2133041 = 1599781) B1599781
theorem B2133059 : Blo 1421530 2133059 := bstep (se 1 (by rfl) ⟨1599794, by rfl⟩ : syracuseStep 2133059 = 3199589) B3199589
theorem B2133089 : Blo 1421530 2133089 := bstep (se 2 (by rfl) ⟨799908, by rfl⟩ : syracuseStep 2133089 = 1599817) B1599817
theorem B8096867 : Blo 1421530 8096867 := bstep (se 1 (by rfl) ⟨6072650, by rfl⟩ : syracuseStep 8096867 = 12145301) B12145301
theorem B2133107 : Blo 1421530 2133107 := bstep (se 1 (by rfl) ⟨1599830, by rfl⟩ : syracuseStep 2133107 = 3199661) B3199661
theorem B1600627 : Blo 1421530 1600627 := bstep (se 1 (by rfl) ⟨1200470, by rfl⟩ : syracuseStep 1600627 = 2400941) B2400941
theorem B2133137 : Blo 1421530 2133137 := bstep (se 2 (by rfl) ⟨799926, by rfl⟩ : syracuseStep 2133137 = 1599853) B1599853
theorem B2133155 : Blo 1421530 2133155 := bstep (se 1 (by rfl) ⟨1599866, by rfl⟩ : syracuseStep 2133155 = 3199733) B3199733
theorem B4811939 : Blo 1421530 4811939 := bstep (se 1 (by rfl) ⟨3608954, by rfl⟩ : syracuseStep 4811939 = 7217909) B7217909
theorem B2133185 : Blo 1421530 2133185 := bstep (se 2 (by rfl) ⟨799944, by rfl⟩ : syracuseStep 2133185 = 1599889) B1599889
theorem B10251461 : Blo 1421530 10251461 := bstep (se 4 (by rfl) ⟨961074, by rfl⟩ : syracuseStep 10251461 = 1922149) B1922149
theorem B2133203 : Blo 1421530 2133203 := bstep (se 1 (by rfl) ⟨1599902, by rfl⟩ : syracuseStep 2133203 = 3199805) B3199805
theorem B2026723 : Blo 1421530 2026723 := bstep (se 1 (by rfl) ⟨1520042, by rfl⟩ : syracuseStep 2026723 = 3040085) B3040085
theorem B2133233 : Blo 1421530 2133233 := bstep (se 2 (by rfl) ⟨799962, by rfl⟩ : syracuseStep 2133233 = 1599925) B1599925
theorem B2133251 : Blo 1421530 2133251 := bstep (se 1 (by rfl) ⟨1599938, by rfl⟩ : syracuseStep 2133251 = 3199877) B3199877
theorem B1600771 : Blo 1421530 1600771 := bstep (se 1 (by rfl) ⟨1200578, by rfl⟩ : syracuseStep 1600771 = 2401157) B2401157
theorem B2133281 : Blo 1421530 2133281 := bstep (se 2 (by rfl) ⟨799980, by rfl⟩ : syracuseStep 2133281 = 1599961) B1599961
theorem B2133299 : Blo 1421530 2133299 := bstep (se 1 (by rfl) ⟨1599974, by rfl⟩ : syracuseStep 2133299 = 3199949) B3199949
theorem B2133329 : Blo 1421530 2133329 := bstep (se 2 (by rfl) ⟨799998, by rfl⟩ : syracuseStep 2133329 = 1599997) B1599997
theorem B2133347 : Blo 1421530 2133347 := bstep (se 1 (by rfl) ⟨1600010, by rfl⟩ : syracuseStep 2133347 = 3200021) B3200021
theorem B2133377 : Blo 1421530 2133377 := bstep (se 2 (by rfl) ⟨800016, by rfl⟩ : syracuseStep 2133377 = 1600033) B1600033
theorem B5401997 : Blo 1421530 5401997 := bstep (se 3 (by rfl) ⟨1012874, by rfl⟩ : syracuseStep 5401997 = 2025749) B2025749
theorem B3599761 : Blo 1421530 3599761 := bstep (se 2 (by rfl) ⟨1349910, by rfl⟩ : syracuseStep 3599761 = 2699821) B2699821
theorem B2133395 : Blo 1421530 2133395 := bstep (se 1 (by rfl) ⟨1600046, by rfl⟩ : syracuseStep 2133395 = 3200093) B3200093
theorem B1600915 : Blo 1421530 1600915 := bstep (se 1 (by rfl) ⟨1200686, by rfl⟩ : syracuseStep 1600915 = 2401373) B2401373
theorem B2133425 : Blo 1421530 2133425 := bstep (se 2 (by rfl) ⟨800034, by rfl⟩ : syracuseStep 2133425 = 1600069) B1600069
theorem B2133443 : Blo 1421530 2133443 := bstep (se 1 (by rfl) ⟨1600082, by rfl⟩ : syracuseStep 2133443 = 3200165) B3200165
theorem B7204301 : Blo 1421530 7204301 := bstep (se 3 (by rfl) ⟨1350806, by rfl⟩ : syracuseStep 7204301 = 2701613) B2701613
theorem B2133473 : Blo 1421530 2133473 := bstep (se 2 (by rfl) ⟨800052, by rfl⟩ : syracuseStep 2133473 = 1600105) B1600105
theorem B2133491 : Blo 1421530 2133491 := bstep (se 1 (by rfl) ⟨1600118, by rfl⟩ : syracuseStep 2133491 = 3200237) B3200237
theorem B4804109 : Blo 1421530 4804109 := bstep (se 3 (by rfl) ⟨900770, by rfl⟩ : syracuseStep 4804109 = 1801541) B1801541
theorem B2133521 : Blo 1421530 2133521 := bstep (se 2 (by rfl) ⟨800070, by rfl⟩ : syracuseStep 2133521 = 1600141) B1600141
theorem B2133539 : Blo 1421530 2133539 := bstep (se 1 (by rfl) ⟨1600154, by rfl⟩ : syracuseStep 2133539 = 3200309) B3200309
theorem B1601059 : Blo 1421530 1601059 := bstep (se 1 (by rfl) ⟨1200794, by rfl⟩ : syracuseStep 1601059 = 2401589) B2401589
theorem B2133569 : Blo 1421530 2133569 := bstep (se 2 (by rfl) ⟨800088, by rfl⟩ : syracuseStep 2133569 = 1600177) B1600177
theorem B4804163 : Blo 1421530 4804163 := bstep (se 1 (by rfl) ⟨3603122, by rfl⟩ : syracuseStep 4804163 = 7206245) B7206245
theorem B3198545 : Blo 1421530 3198545 := bstep (se 2 (by rfl) ⟨1199454, by rfl⟩ : syracuseStep 3198545 = 2398909) B2398909
theorem B2133587 : Blo 1421530 2133587 := bstep (se 1 (by rfl) ⟨1600190, by rfl⟩ : syracuseStep 2133587 = 3200381) B3200381
theorem B3198563 : Blo 1421530 3198563 := bstep (se 1 (by rfl) ⟨2398922, by rfl⟩ : syracuseStep 3198563 = 4797845) B4797845
theorem B2133617 : Blo 1421530 2133617 := bstep (se 2 (by rfl) ⟨800106, by rfl⟩ : syracuseStep 2133617 = 1600213) B1600213
theorem B2133635 : Blo 1421530 2133635 := bstep (se 1 (by rfl) ⟨1600226, by rfl⟩ : syracuseStep 2133635 = 3200453) B3200453
theorem B1560211 : Blo 1421530 1560211 := bstep (se 1 (by rfl) ⟨1170158, by rfl⟩ : syracuseStep 1560211 = 2340317) B2340317
theorem B2133665 : Blo 1421530 2133665 := bstep (se 2 (by rfl) ⟨800124, by rfl⟩ : syracuseStep 2133665 = 1600249) B1600249
theorem B3600035 : Blo 1421530 3600035 := bstep (se 1 (by rfl) ⟨2700026, by rfl⟩ : syracuseStep 3600035 = 5400053) B5400053
theorem B2133683 : Blo 1421530 2133683 := bstep (se 1 (by rfl) ⟨1600262, by rfl⟩ : syracuseStep 2133683 = 3200525) B3200525
theorem B1601203 : Blo 1421530 1601203 := bstep (se 1 (by rfl) ⟨1200902, by rfl⟩ : syracuseStep 1601203 = 2401805) B2401805
theorem B2133713 : Blo 1421530 2133713 := bstep (se 2 (by rfl) ⟨800142, by rfl⟩ : syracuseStep 2133713 = 1600285) B1600285
theorem B2133731 : Blo 1421530 2133731 := bstep (se 1 (by rfl) ⟨1600298, by rfl⟩ : syracuseStep 2133731 = 3200597) B3200597
theorem B2133761 : Blo 1421530 2133761 := bstep (se 2 (by rfl) ⟨800160, by rfl⟩ : syracuseStep 2133761 = 1600321) B1600321
theorem B2133779 : Blo 1421530 2133779 := bstep (se 1 (by rfl) ⟨1600334, by rfl⟩ : syracuseStep 2133779 = 3200669) B3200669
theorem B2133809 : Blo 1421530 2133809 := bstep (se 2 (by rfl) ⟨800178, by rfl⟩ : syracuseStep 2133809 = 1600357) B1600357
theorem B2133827 : Blo 1421530 2133827 := bstep (se 1 (by rfl) ⟨1600370, by rfl⟩ : syracuseStep 2133827 = 3200741) B3200741
theorem B1601347 : Blo 1421530 1601347 := bstep (se 1 (by rfl) ⟨1201010, by rfl⟩ : syracuseStep 1601347 = 2402021) B2402021
theorem B6074189 : Blo 1421530 6074189 := bstep (se 3 (by rfl) ⟨1138910, by rfl⟩ : syracuseStep 6074189 = 2277821) B2277821
theorem B4050769 : Blo 1421530 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B2133857 : Blo 1421530 2133857 := bstep (se 2 (by rfl) ⟨800196, by rfl⟩ : syracuseStep 2133857 = 1600393) B1600393
theorem B3600227 : Blo 1421530 3600227 := bstep (se 1 (by rfl) ⟨2700170, by rfl⟩ : syracuseStep 3600227 = 5400341) B5400341
theorem B3198833 : Blo 1421530 3198833 := bstep (se 2 (by rfl) ⟨1199562, by rfl⟩ : syracuseStep 3198833 = 2399125) B2399125
theorem B18485105 : Blo 1421530 18485105 := bstep (se 2 (by rfl) ⟨6931914, by rfl⟩ : syracuseStep 18485105 = 13863829) B13863829
theorem B2133875 : Blo 1421530 2133875 := bstep (se 1 (by rfl) ⟨1600406, by rfl⟩ : syracuseStep 2133875 = 3200813) B3200813
theorem B3198851 : Blo 1421530 3198851 := bstep (se 1 (by rfl) ⟨2399138, by rfl⟩ : syracuseStep 3198851 = 4798277) B4798277
theorem B2699153 : Blo 1421530 2699153 := bstep (se 2 (by rfl) ⟨1012182, by rfl⟩ : syracuseStep 2699153 = 2024365) B2024365
theorem B2133905 : Blo 1421530 2133905 := bstep (se 2 (by rfl) ⟨800214, by rfl⟩ : syracuseStep 2133905 = 1600429) B1600429
theorem B2133923 : Blo 1421530 2133923 := bstep (se 1 (by rfl) ⟨1600442, by rfl⟩ : syracuseStep 2133923 = 3200885) B3200885
theorem B2133953 : Blo 1421530 2133953 := bstep (se 2 (by rfl) ⟨800232, by rfl⟩ : syracuseStep 2133953 = 1600465) B1600465
theorem B8105933 : Blo 1421530 8105933 := bstep (se 3 (by rfl) ⟨1519862, by rfl⟩ : syracuseStep 8105933 = 3039725) B3039725
theorem B2133971 : Blo 1421530 2133971 := bstep (se 1 (by rfl) ⟨1600478, by rfl⟩ : syracuseStep 2133971 = 3200957) B3200957
theorem B2134001 : Blo 1421530 2134001 := bstep (se 2 (by rfl) ⟨800250, by rfl⟩ : syracuseStep 2134001 = 1600501) B1600501
theorem B2134019 : Blo 1421530 2134019 := bstep (se 1 (by rfl) ⟨1600514, by rfl⟩ : syracuseStep 2134019 = 3201029) B3201029
theorem B12144653 : Blo 1421530 12144653 := bstep (se 3 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 12144653 = 4554245) B4554245
theorem B2134049 : Blo 1421530 2134049 := bstep (se 2 (by rfl) ⟨800268, by rfl⟩ : syracuseStep 2134049 = 1600537) B1600537
theorem B2134067 : Blo 1421530 2134067 := bstep (se 1 (by rfl) ⟨1600550, by rfl⟩ : syracuseStep 2134067 = 3201101) B3201101
theorem B2134097 : Blo 1421530 2134097 := bstep (se 2 (by rfl) ⟨800286, by rfl⟩ : syracuseStep 2134097 = 1600573) B1600573
theorem B4051043 : Blo 1421530 4051043 := bstep (se 1 (by rfl) ⟨3038282, by rfl⟩ : syracuseStep 4051043 = 6076565) B6076565
theorem B2134115 : Blo 1421530 2134115 := bstep (se 1 (by rfl) ⟨1600586, by rfl⟩ : syracuseStep 2134115 = 3201173) B3201173
theorem B2134145 : Blo 1421530 2134145 := bstep (se 2 (by rfl) ⟨800304, by rfl⟩ : syracuseStep 2134145 = 1600609) B1600609
theorem B3199121 : Blo 1421530 3199121 := bstep (se 2 (by rfl) ⟨1199670, by rfl⟩ : syracuseStep 3199121 = 2399341) B2399341
theorem B2134163 : Blo 1421530 2134163 := bstep (se 1 (by rfl) ⟨1600622, by rfl⟩ : syracuseStep 2134163 = 3201245) B3201245
theorem B3199139 : Blo 1421530 3199139 := bstep (se 1 (by rfl) ⟨2399354, by rfl⟩ : syracuseStep 3199139 = 4798709) B4798709
theorem B7196849 : Blo 1421530 7196849 := bstep (se 2 (by rfl) ⟨2698818, by rfl⟩ : syracuseStep 7196849 = 5397637) B5397637
theorem B2134193 : Blo 1421530 2134193 := bstep (se 2 (by rfl) ⟨800322, by rfl⟩ : syracuseStep 2134193 = 1600645) B1600645
theorem B5402801 : Blo 1421530 5402801 := bstep (se 2 (by rfl) ⟨2026050, by rfl⟩ : syracuseStep 5402801 = 4052101) B4052101
theorem B2134211 : Blo 1421530 2134211 := bstep (se 1 (by rfl) ⟨1600658, by rfl⟩ : syracuseStep 2134211 = 3201317) B3201317
theorem B10801349 : Blo 1421530 10801349 := bstep (se 4 (by rfl) ⟨1012626, by rfl⟩ : syracuseStep 10801349 = 2025253) B2025253
theorem B2134241 : Blo 1421530 2134241 := bstep (se 2 (by rfl) ⟨800340, by rfl⟩ : syracuseStep 2134241 = 1600681) B1600681
theorem B1421539 : Blo 1421530 1421539 := bstep (se 1 (by rfl) ⟨1066154, by rfl⟩ : syracuseStep 1421539 = 2132309) B2132309
theorem B1421555 : Blo 1421530 1421555 := bstep (se 1 (by rfl) ⟨1066166, by rfl⟩ : syracuseStep 1421555 = 2132333) B2132333
theorem B2134259 : Blo 1421530 2134259 := bstep (se 1 (by rfl) ⟨1600694, by rfl⟩ : syracuseStep 2134259 = 3201389) B3201389
theorem B1421571 : Blo 1421530 1421571 := bstep (se 1 (by rfl) ⟨1066178, by rfl⟩ : syracuseStep 1421571 = 2132357) B2132357
theorem B2134289 : Blo 1421530 2134289 := bstep (se 2 (by rfl) ⟨800358, by rfl⟩ : syracuseStep 2134289 = 1600717) B1600717
theorem B1421587 : Blo 1421530 1421587 := bstep (se 1 (by rfl) ⟨1066190, by rfl⟩ : syracuseStep 1421587 = 2132381) B2132381
theorem B1421603 : Blo 1421530 1421603 := bstep (se 1 (by rfl) ⟨1066202, by rfl⟩ : syracuseStep 1421603 = 2132405) B2132405
theorem B4051235 : Blo 1421530 4051235 := bstep (se 1 (by rfl) ⟨3038426, by rfl⟩ : syracuseStep 4051235 = 6076853) B6076853
theorem B2134307 : Blo 1421530 2134307 := bstep (se 1 (by rfl) ⟨1600730, by rfl⟩ : syracuseStep 2134307 = 3201461) B3201461
theorem B1421619 : Blo 1421530 1421619 := bstep (se 1 (by rfl) ⟨1066214, by rfl⟩ : syracuseStep 1421619 = 2132429) B2132429
theorem B2134337 : Blo 1421530 2134337 := bstep (se 2 (by rfl) ⟨800376, by rfl⟩ : syracuseStep 2134337 = 1600753) B1600753
theorem B1421635 : Blo 1421530 1421635 := bstep (se 1 (by rfl) ⟨1066226, by rfl⟩ : syracuseStep 1421635 = 2132453) B2132453
theorem B1421651 : Blo 1421530 1421651 := bstep (se 1 (by rfl) ⟨1066238, by rfl⟩ : syracuseStep 1421651 = 2132477) B2132477
theorem B2134355 : Blo 1421530 2134355 := bstep (se 1 (by rfl) ⟨1600766, by rfl⟩ : syracuseStep 2134355 = 3201533) B3201533
theorem B1421667 : Blo 1421530 1421667 := bstep (se 1 (by rfl) ⟨1066250, by rfl⟩ : syracuseStep 1421667 = 2132501) B2132501
theorem B2134385 : Blo 1421530 2134385 := bstep (se 2 (by rfl) ⟨800394, by rfl⟩ : syracuseStep 2134385 = 1600789) B1600789
theorem B1421683 : Blo 1421530 1421683 := bstep (se 1 (by rfl) ⟨1066262, by rfl⟩ : syracuseStep 1421683 = 2132525) B2132525
theorem B1421699 : Blo 1421530 1421699 := bstep (se 1 (by rfl) ⟨1066274, by rfl⟩ : syracuseStep 1421699 = 2132549) B2132549
theorem B2134403 : Blo 1421530 2134403 := bstep (se 1 (by rfl) ⟨1600802, by rfl⟩ : syracuseStep 2134403 = 3201605) B3201605
theorem B1421715 : Blo 1421530 1421715 := bstep (se 1 (by rfl) ⟨1066286, by rfl⟩ : syracuseStep 1421715 = 2132573) B2132573
theorem B2134433 : Blo 1421530 2134433 := bstep (se 2 (by rfl) ⟨800412, by rfl⟩ : syracuseStep 2134433 = 1600825) B1600825
theorem B1421731 : Blo 1421530 1421731 := bstep (se 1 (by rfl) ⟨1066298, by rfl⟩ : syracuseStep 1421731 = 2132597) B2132597
theorem B3199409 : Blo 1421530 3199409 := bstep (se 2 (by rfl) ⟨1199778, by rfl⟩ : syracuseStep 3199409 = 2399557) B2399557
theorem B1421747 : Blo 1421530 1421747 := bstep (se 1 (by rfl) ⟨1066310, by rfl⟩ : syracuseStep 1421747 = 2132621) B2132621
theorem B2134451 : Blo 1421530 2134451 := bstep (se 1 (by rfl) ⟨1600838, by rfl⟩ : syracuseStep 2134451 = 3201677) B3201677
theorem B18223541 : Blo 1421530 18223541 := bstep (se 5 (by rfl) ⟨854228, by rfl⟩ : syracuseStep 18223541 = 1708457) B1708457
theorem B1421763 : Blo 1421530 1421763 := bstep (se 1 (by rfl) ⟨1066322, by rfl⟩ : syracuseStep 1421763 = 2132645) B2132645
theorem B3199427 : Blo 1421530 3199427 := bstep (se 1 (by rfl) ⟨2399570, by rfl⟩ : syracuseStep 3199427 = 4799141) B4799141
theorem B13152709 : Blo 1421530 13152709 := bstep (se 4 (by rfl) ⟨1233066, by rfl⟩ : syracuseStep 13152709 = 2466133) B2466133
theorem B2134481 : Blo 1421530 2134481 := bstep (se 2 (by rfl) ⟨800430, by rfl⟩ : syracuseStep 2134481 = 1600861) B1600861
theorem B1421779 : Blo 1421530 1421779 := bstep (se 1 (by rfl) ⟨1066334, by rfl⟩ : syracuseStep 1421779 = 2132669) B2132669
theorem B1421795 : Blo 1421530 1421795 := bstep (se 1 (by rfl) ⟨1066346, by rfl⟩ : syracuseStep 1421795 = 2132693) B2132693
theorem B2134499 : Blo 1421530 2134499 := bstep (se 1 (by rfl) ⟨1600874, by rfl⟩ : syracuseStep 2134499 = 3201749) B3201749
theorem B1421811 : Blo 1421530 1421811 := bstep (se 1 (by rfl) ⟨1066358, by rfl⟩ : syracuseStep 1421811 = 2132717) B2132717
theorem B2134529 : Blo 1421530 2134529 := bstep (se 2 (by rfl) ⟨800448, by rfl⟩ : syracuseStep 2134529 = 1600897) B1600897
theorem B1421827 : Blo 1421530 1421827 := bstep (se 1 (by rfl) ⟨1066370, by rfl⟩ : syracuseStep 1421827 = 2132741) B2132741
theorem B1421843 : Blo 1421530 1421843 := bstep (se 1 (by rfl) ⟨1066382, by rfl⟩ : syracuseStep 1421843 = 2132765) B2132765
theorem B2134547 : Blo 1421530 2134547 := bstep (se 1 (by rfl) ⟨1600910, by rfl⟩ : syracuseStep 2134547 = 3201821) B3201821
theorem B1421859 : Blo 1421530 1421859 := bstep (se 1 (by rfl) ⟨1066394, by rfl⟩ : syracuseStep 1421859 = 2132789) B2132789
theorem B2134577 : Blo 1421530 2134577 := bstep (se 2 (by rfl) ⟨800466, by rfl⟩ : syracuseStep 2134577 = 1600933) B1600933
theorem B1421875 : Blo 1421530 1421875 := bstep (se 1 (by rfl) ⟨1066406, by rfl⟩ : syracuseStep 1421875 = 2132813) B2132813
theorem B1421891 : Blo 1421530 1421891 := bstep (se 1 (by rfl) ⟨1066418, by rfl⟩ : syracuseStep 1421891 = 2132837) B2132837
theorem B2134595 : Blo 1421530 2134595 := bstep (se 1 (by rfl) ⟨1600946, by rfl⟩ : syracuseStep 2134595 = 3201893) B3201893
theorem B1421907 : Blo 1421530 1421907 := bstep (se 1 (by rfl) ⟨1066430, by rfl⟩ : syracuseStep 1421907 = 2132861) B2132861
theorem B2134625 : Blo 1421530 2134625 := bstep (se 2 (by rfl) ⟨800484, by rfl⟩ : syracuseStep 2134625 = 1600969) B1600969
theorem B1421923 : Blo 1421530 1421923 := bstep (se 1 (by rfl) ⟨1066442, by rfl⟩ : syracuseStep 1421923 = 2132885) B2132885
theorem B1421939 : Blo 1421530 1421939 := bstep (se 1 (by rfl) ⟨1066454, by rfl⟩ : syracuseStep 1421939 = 2132909) B2132909
theorem B2134643 : Blo 1421530 2134643 := bstep (se 1 (by rfl) ⟨1600982, by rfl⟩ : syracuseStep 2134643 = 3201965) B3201965
theorem B1421955 : Blo 1421530 1421955 := bstep (se 1 (by rfl) ⟨1066466, by rfl⟩ : syracuseStep 1421955 = 2132933) B2132933
theorem B2134673 : Blo 1421530 2134673 := bstep (se 2 (by rfl) ⟨800502, by rfl⟩ : syracuseStep 2134673 = 1601005) B1601005
theorem B1421971 : Blo 1421530 1421971 := bstep (se 1 (by rfl) ⟨1066478, by rfl⟩ : syracuseStep 1421971 = 2132957) B2132957
theorem B1421987 : Blo 1421530 1421987 := bstep (se 1 (by rfl) ⟨1066490, by rfl⟩ : syracuseStep 1421987 = 2132981) B2132981
theorem B2134691 : Blo 1421530 2134691 := bstep (se 1 (by rfl) ⟨1601018, by rfl⟩ : syracuseStep 2134691 = 3202037) B3202037
theorem B1422003 : Blo 1421530 1422003 := bstep (se 1 (by rfl) ⟨1066502, by rfl⟩ : syracuseStep 1422003 = 2133005) B2133005
theorem B2134721 : Blo 1421530 2134721 := bstep (se 2 (by rfl) ⟨800520, by rfl⟩ : syracuseStep 2134721 = 1601041) B1601041
theorem B1422019 : Blo 1421530 1422019 := bstep (se 1 (by rfl) ⟨1066514, by rfl⟩ : syracuseStep 1422019 = 2133029) B2133029
theorem B3199697 : Blo 1421530 3199697 := bstep (se 2 (by rfl) ⟨1199886, by rfl⟩ : syracuseStep 3199697 = 2399773) B2399773
theorem B1422035 : Blo 1421530 1422035 := bstep (se 1 (by rfl) ⟨1066526, by rfl⟩ : syracuseStep 1422035 = 2133053) B2133053
theorem B2134739 : Blo 1421530 2134739 := bstep (se 1 (by rfl) ⟨1601054, by rfl⟩ : syracuseStep 2134739 = 3202109) B3202109
theorem B1422051 : Blo 1421530 1422051 := bstep (se 1 (by rfl) ⟨1066538, by rfl⟩ : syracuseStep 1422051 = 2133077) B2133077
theorem B3199715 : Blo 1421530 3199715 := bstep (se 1 (by rfl) ⟨2399786, by rfl⟩ : syracuseStep 3199715 = 4799573) B4799573
theorem B2134769 : Blo 1421530 2134769 := bstep (se 2 (by rfl) ⟨800538, by rfl⟩ : syracuseStep 2134769 = 1601077) B1601077
theorem B1422067 : Blo 1421530 1422067 := bstep (se 1 (by rfl) ⟨1066550, by rfl⟩ : syracuseStep 1422067 = 2133101) B2133101
theorem B1422083 : Blo 1421530 1422083 := bstep (se 1 (by rfl) ⟨1066562, by rfl⟩ : syracuseStep 1422083 = 2133125) B2133125
theorem B2134787 : Blo 1421530 2134787 := bstep (se 1 (by rfl) ⟨1601090, by rfl⟩ : syracuseStep 2134787 = 3202181) B3202181
theorem B2700049 : Blo 1421530 2700049 := bstep (se 2 (by rfl) ⟨1012518, by rfl⟩ : syracuseStep 2700049 = 2025037) B2025037
theorem B3601169 : Blo 1421530 3601169 := bstep (se 2 (by rfl) ⟨1350438, by rfl⟩ : syracuseStep 3601169 = 2700877) B2700877
theorem B1422099 : Blo 1421530 1422099 := bstep (se 1 (by rfl) ⟨1066574, by rfl⟩ : syracuseStep 1422099 = 2133149) B2133149
theorem B2134817 : Blo 1421530 2134817 := bstep (se 2 (by rfl) ⟨800556, by rfl⟩ : syracuseStep 2134817 = 1601113) B1601113
theorem B1422115 : Blo 1421530 1422115 := bstep (se 1 (by rfl) ⟨1066586, by rfl⟩ : syracuseStep 1422115 = 2133173) B2133173
theorem B1422131 : Blo 1421530 1422131 := bstep (se 1 (by rfl) ⟨1066598, by rfl⟩ : syracuseStep 1422131 = 2133197) B2133197
theorem B2134835 : Blo 1421530 2134835 := bstep (se 1 (by rfl) ⟨1601126, by rfl⟩ : syracuseStep 2134835 = 3202253) B3202253
theorem B1422147 : Blo 1421530 1422147 := bstep (se 1 (by rfl) ⟨1066610, by rfl⟩ : syracuseStep 1422147 = 2133221) B2133221
theorem B3601219 : Blo 1421530 3601219 := bstep (se 1 (by rfl) ⟨2700914, by rfl⟩ : syracuseStep 3601219 = 5401829) B5401829
theorem B5403469 : Blo 1421530 5403469 := bstep (se 3 (by rfl) ⟨1013150, by rfl⟩ : syracuseStep 5403469 = 2026301) B2026301
theorem B1422163 : Blo 1421530 1422163 := bstep (se 1 (by rfl) ⟨1066622, by rfl⟩ : syracuseStep 1422163 = 2133245) B2133245
theorem B2134865 : Blo 1421530 2134865 := bstep (se 2 (by rfl) ⟨800574, by rfl⟩ : syracuseStep 2134865 = 1601149) B1601149
theorem B1422179 : Blo 1421530 1422179 := bstep (se 1 (by rfl) ⟨1066634, by rfl⟩ : syracuseStep 1422179 = 2133269) B2133269
theorem B2134883 : Blo 1421530 2134883 := bstep (se 1 (by rfl) ⟨1601162, by rfl⟩ : syracuseStep 2134883 = 3202325) B3202325
theorem B1422195 : Blo 1421530 1422195 := bstep (se 1 (by rfl) ⟨1066646, by rfl⟩ : syracuseStep 1422195 = 2133293) B2133293
theorem B2134913 : Blo 1421530 2134913 := bstep (se 2 (by rfl) ⟨800592, by rfl⟩ : syracuseStep 2134913 = 1601185) B1601185
theorem B3036035 : Blo 1421530 3036035 := bstep (se 1 (by rfl) ⟨2277026, by rfl⟩ : syracuseStep 3036035 = 4554053) B4554053
theorem B1422211 : Blo 1421530 1422211 := bstep (se 1 (by rfl) ⟨1066658, by rfl⟩ : syracuseStep 1422211 = 2133317) B2133317
theorem B12825485 : Blo 1421530 12825485 := bstep (se 3 (by rfl) ⟨2404778, by rfl⟩ : syracuseStep 12825485 = 4809557) B4809557
theorem B19461005 : Blo 1421530 19461005 := bstep (se 3 (by rfl) ⟨3648938, by rfl⟩ : syracuseStep 19461005 = 7297877) B7297877
theorem B1422227 : Blo 1421530 1422227 := bstep (se 1 (by rfl) ⟨1066670, by rfl⟩ : syracuseStep 1422227 = 2133341) B2133341
theorem B2134931 : Blo 1421530 2134931 := bstep (se 1 (by rfl) ⟨1601198, by rfl⟩ : syracuseStep 2134931 = 3202397) B3202397
theorem B1422243 : Blo 1421530 1422243 := bstep (se 1 (by rfl) ⟨1066682, by rfl⟩ : syracuseStep 1422243 = 2133365) B2133365
theorem B6837155 : Blo 1421530 6837155 := bstep (se 1 (by rfl) ⟨5127866, by rfl⟩ : syracuseStep 6837155 = 10255733) B10255733
theorem B2700209 : Blo 1421530 2700209 := bstep (se 2 (by rfl) ⟨1012578, by rfl⟩ : syracuseStep 2700209 = 2025157) B2025157
theorem B2134961 : Blo 1421530 2134961 := bstep (se 2 (by rfl) ⟨800610, by rfl⟩ : syracuseStep 2134961 = 1601221) B1601221
theorem B1422259 : Blo 1421530 1422259 := bstep (se 1 (by rfl) ⟨1066694, by rfl⟩ : syracuseStep 1422259 = 2133389) B2133389
theorem B1422275 : Blo 1421530 1422275 := bstep (se 1 (by rfl) ⟨1066706, by rfl⟩ : syracuseStep 1422275 = 2133413) B2133413
theorem B2134979 : Blo 1421530 2134979 := bstep (se 1 (by rfl) ⟨1601234, by rfl⟩ : syracuseStep 2134979 = 3202469) B3202469
theorem B3601361 : Blo 1421530 3601361 := bstep (se 2 (by rfl) ⟨1350510, by rfl⟩ : syracuseStep 3601361 = 2701021) B2701021
theorem B1422291 : Blo 1421530 1422291 := bstep (se 1 (by rfl) ⟨1066718, by rfl⟩ : syracuseStep 1422291 = 2133437) B2133437
theorem B2135009 : Blo 1421530 2135009 := bstep (se 2 (by rfl) ⟨800628, by rfl⟩ : syracuseStep 2135009 = 1601257) B1601257
theorem B1422307 : Blo 1421530 1422307 := bstep (se 1 (by rfl) ⟨1066730, by rfl⟩ : syracuseStep 1422307 = 2133461) B2133461
theorem B3199985 : Blo 1421530 3199985 := bstep (se 2 (by rfl) ⟨1199994, by rfl⟩ : syracuseStep 3199985 = 2399989) B2399989
theorem B1422323 : Blo 1421530 1422323 := bstep (se 1 (by rfl) ⟨1066742, by rfl⟩ : syracuseStep 1422323 = 2133485) B2133485
theorem B2135027 : Blo 1421530 2135027 := bstep (se 1 (by rfl) ⟨1601270, by rfl⟩ : syracuseStep 2135027 = 3202541) B3202541
theorem B3200003 : Blo 1421530 3200003 := bstep (se 1 (by rfl) ⟨2400002, by rfl⟩ : syracuseStep 3200003 = 4800005) B4800005
theorem B1422339 : Blo 1421530 1422339 := bstep (se 1 (by rfl) ⟨1066754, by rfl⟩ : syracuseStep 1422339 = 2133509) B2133509
theorem B4559885 : Blo 1421530 4559885 := bstep (se 3 (by rfl) ⟨854978, by rfl⟩ : syracuseStep 4559885 = 1709957) B1709957
theorem B2135057 : Blo 1421530 2135057 := bstep (se 2 (by rfl) ⟨800646, by rfl⟩ : syracuseStep 2135057 = 1601293) B1601293
theorem B1422355 : Blo 1421530 1422355 := bstep (se 1 (by rfl) ⟨1066766, by rfl⟩ : syracuseStep 1422355 = 2133533) B2133533
theorem B1422371 : Blo 1421530 1422371 := bstep (se 1 (by rfl) ⟨1066778, by rfl⟩ : syracuseStep 1422371 = 2133557) B2133557
theorem B2135075 : Blo 1421530 2135075 := bstep (se 1 (by rfl) ⟨1601306, by rfl⟩ : syracuseStep 2135075 = 3202613) B3202613
theorem B1422387 : Blo 1421530 1422387 := bstep (se 1 (by rfl) ⟨1066790, by rfl⟩ : syracuseStep 1422387 = 2133581) B2133581
theorem B2135105 : Blo 1421530 2135105 := bstep (se 2 (by rfl) ⟨800664, by rfl⟩ : syracuseStep 2135105 = 1601329) B1601329
theorem B1422403 : Blo 1421530 1422403 := bstep (se 1 (by rfl) ⟨1066802, by rfl⟩ : syracuseStep 1422403 = 2133605) B2133605
theorem B6927437 : Blo 1421530 6927437 := bstep (se 3 (by rfl) ⟨1298894, by rfl⟩ : syracuseStep 6927437 = 2597789) B2597789
theorem B4052045 : Blo 1421530 4052045 := bstep (se 3 (by rfl) ⟨759758, by rfl⟩ : syracuseStep 4052045 = 1519517) B1519517
theorem B1422419 : Blo 1421530 1422419 := bstep (se 1 (by rfl) ⟨1066814, by rfl⟩ : syracuseStep 1422419 = 2133629) B2133629
theorem B2135123 : Blo 1421530 2135123 := bstep (se 1 (by rfl) ⟨1601342, by rfl⟩ : syracuseStep 2135123 = 3202685) B3202685
theorem B1422435 : Blo 1421530 1422435 := bstep (se 1 (by rfl) ⟨1066826, by rfl⟩ : syracuseStep 1422435 = 2133653) B2133653
theorem B2135153 : Blo 1421530 2135153 := bstep (se 2 (by rfl) ⟨800682, by rfl⟩ : syracuseStep 2135153 = 1601365) B1601365
theorem B1422451 : Blo 1421530 1422451 := bstep (se 1 (by rfl) ⟨1066838, by rfl⟩ : syracuseStep 1422451 = 2133677) B2133677
theorem B1422467 : Blo 1421530 1422467 := bstep (se 1 (by rfl) ⟨1066850, by rfl⟩ : syracuseStep 1422467 = 2133701) B2133701
theorem B2135171 : Blo 1421530 2135171 := bstep (se 1 (by rfl) ⟨1601378, by rfl⟩ : syracuseStep 2135171 = 3202757) B3202757
theorem B1422483 : Blo 1421530 1422483 := bstep (se 1 (by rfl) ⟨1066862, by rfl⟩ : syracuseStep 1422483 = 2133725) B2133725
theorem B2135201 : Blo 1421530 2135201 := bstep (se 2 (by rfl) ⟨800700, by rfl⟩ : syracuseStep 2135201 = 1601401) B1601401
theorem B1422499 : Blo 1421530 1422499 := bstep (se 1 (by rfl) ⟨1066874, by rfl⟩ : syracuseStep 1422499 = 2133749) B2133749
theorem B1422515 : Blo 1421530 1422515 := bstep (se 1 (by rfl) ⟨1066886, by rfl⟩ : syracuseStep 1422515 = 2133773) B2133773
theorem B2135219 : Blo 1421530 2135219 := bstep (se 1 (by rfl) ⟨1601414, by rfl⟩ : syracuseStep 2135219 = 3202829) B3202829
theorem B1422531 : Blo 1421530 1422531 := bstep (se 1 (by rfl) ⟨1066898, by rfl⟩ : syracuseStep 1422531 = 2133797) B2133797
theorem B4617425 : Blo 1421530 4617425 := bstep (se 2 (by rfl) ⟨1731534, by rfl⟩ : syracuseStep 4617425 = 3463069) B3463069
theorem B2135249 : Blo 1421530 2135249 := bstep (se 2 (by rfl) ⟨800718, by rfl⟩ : syracuseStep 2135249 = 1601437) B1601437
theorem B1422547 : Blo 1421530 1422547 := bstep (se 1 (by rfl) ⟨1066910, by rfl⟩ : syracuseStep 1422547 = 2133821) B2133821
theorem B1422563 : Blo 1421530 1422563 := bstep (se 1 (by rfl) ⟨1066922, by rfl⟩ : syracuseStep 1422563 = 2133845) B2133845
theorem B2135267 : Blo 1421530 2135267 := bstep (se 1 (by rfl) ⟨1601450, by rfl⟩ : syracuseStep 2135267 = 3202901) B3202901
theorem B1422579 : Blo 1421530 1422579 := bstep (se 1 (by rfl) ⟨1066934, by rfl⟩ : syracuseStep 1422579 = 2133869) B2133869
theorem B1422595 : Blo 1421530 1422595 := bstep (se 1 (by rfl) ⟨1066946, by rfl⟩ : syracuseStep 1422595 = 2133893) B2133893
theorem B4052227 : Blo 1421530 4052227 := bstep (se 1 (by rfl) ⟨3039170, by rfl⟩ : syracuseStep 4052227 = 6078341) B6078341
theorem B3200273 : Blo 1421530 3200273 := bstep (se 2 (by rfl) ⟨1200102, by rfl⟩ : syracuseStep 3200273 = 2400205) B2400205
theorem B1422611 : Blo 1421530 1422611 := bstep (se 1 (by rfl) ⟨1066958, by rfl⟩ : syracuseStep 1422611 = 2133917) B2133917
theorem B3200291 : Blo 1421530 3200291 := bstep (se 1 (by rfl) ⟨2400218, by rfl⟩ : syracuseStep 3200291 = 4800437) B4800437
theorem B1422627 : Blo 1421530 1422627 := bstep (se 1 (by rfl) ⟨1066970, by rfl⟩ : syracuseStep 1422627 = 2133941) B2133941
theorem B1422643 : Blo 1421530 1422643 := bstep (se 1 (by rfl) ⟨1066982, by rfl⟩ : syracuseStep 1422643 = 2133965) B2133965
theorem B1799491 : Blo 1421530 1799491 := bstep (se 1 (by rfl) ⟨1349618, by rfl⟩ : syracuseStep 1799491 = 2699237) B2699237
theorem B2700611 : Blo 1421530 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B1422659 : Blo 1421530 1422659 := bstep (se 1 (by rfl) ⟨1066994, by rfl⟩ : syracuseStep 1422659 = 2133989) B2133989
theorem B1422675 : Blo 1421530 1422675 := bstep (se 1 (by rfl) ⟨1067006, by rfl⟩ : syracuseStep 1422675 = 2134013) B2134013
theorem B1422691 : Blo 1421530 1422691 := bstep (se 1 (by rfl) ⟨1067018, by rfl⟩ : syracuseStep 1422691 = 2134037) B2134037
theorem B1422707 : Blo 1421530 1422707 := bstep (se 1 (by rfl) ⟨1067030, by rfl⟩ : syracuseStep 1422707 = 2134061) B2134061
theorem B1422723 : Blo 1421530 1422723 := bstep (se 1 (by rfl) ⟨1067042, by rfl⟩ : syracuseStep 1422723 = 2134085) B2134085
theorem B1422739 : Blo 1421530 1422739 := bstep (se 1 (by rfl) ⟨1067054, by rfl⟩ : syracuseStep 1422739 = 2134109) B2134109
theorem B1799587 : Blo 1421530 1799587 := bstep (se 1 (by rfl) ⟨1349690, by rfl⟩ : syracuseStep 1799587 = 2699381) B2699381
theorem B1422755 : Blo 1421530 1422755 := bstep (se 1 (by rfl) ⟨1067066, by rfl⟩ : syracuseStep 1422755 = 2134133) B2134133
theorem B4560305 : Blo 1421530 4560305 := bstep (se 2 (by rfl) ⟨1710114, by rfl⟩ : syracuseStep 4560305 = 3420229) B3420229
theorem B1422771 : Blo 1421530 1422771 := bstep (se 1 (by rfl) ⟨1067078, by rfl⟩ : syracuseStep 1422771 = 2134157) B2134157
theorem B1422787 : Blo 1421530 1422787 := bstep (se 1 (by rfl) ⟨1067090, by rfl⟩ : syracuseStep 1422787 = 2134181) B2134181
theorem B1422803 : Blo 1421530 1422803 := bstep (se 1 (by rfl) ⟨1067102, by rfl⟩ : syracuseStep 1422803 = 2134205) B2134205
theorem B1422819 : Blo 1421530 1422819 := bstep (se 1 (by rfl) ⟨1067114, by rfl⟩ : syracuseStep 1422819 = 2134229) B2134229
theorem B17315299 : Blo 1421530 17315299 := bstep (se 1 (by rfl) ⟨12986474, by rfl⟩ : syracuseStep 17315299 = 25972949) B25972949
theorem B1422835 : Blo 1421530 1422835 := bstep (se 1 (by rfl) ⟨1067126, by rfl⟩ : syracuseStep 1422835 = 2134253) B2134253
theorem B1422851 : Blo 1421530 1422851 := bstep (se 1 (by rfl) ⟨1067138, by rfl⟩ : syracuseStep 1422851 = 2134277) B2134277
theorem B1422867 : Blo 1421530 1422867 := bstep (se 1 (by rfl) ⟨1067150, by rfl⟩ : syracuseStep 1422867 = 2134301) B2134301
theorem B1422883 : Blo 1421530 1422883 := bstep (se 1 (by rfl) ⟨1067162, by rfl⟩ : syracuseStep 1422883 = 2134325) B2134325
theorem B3200561 : Blo 1421530 3200561 := bstep (se 2 (by rfl) ⟨1200210, by rfl⟩ : syracuseStep 3200561 = 2400421) B2400421
theorem B1422899 : Blo 1421530 1422899 := bstep (se 1 (by rfl) ⟨1067174, by rfl⟩ : syracuseStep 1422899 = 2134349) B2134349
theorem B3200579 : Blo 1421530 3200579 := bstep (se 1 (by rfl) ⟨2400434, by rfl⟩ : syracuseStep 3200579 = 4800869) B4800869
theorem B1422915 : Blo 1421530 1422915 := bstep (se 1 (by rfl) ⟨1067186, by rfl⟩ : syracuseStep 1422915 = 2134373) B2134373
theorem B1422931 : Blo 1421530 1422931 := bstep (se 1 (by rfl) ⟨1067198, by rfl⟩ : syracuseStep 1422931 = 2134397) B2134397
theorem B7198307 : Blo 1421530 7198307 := bstep (se 1 (by rfl) ⟨5398730, by rfl⟩ : syracuseStep 7198307 = 10797461) B10797461
theorem B1422947 : Blo 1421530 1422947 := bstep (se 1 (by rfl) ⟨1067210, by rfl⟩ : syracuseStep 1422947 = 2134421) B2134421
theorem B5404259 : Blo 1421530 5404259 := bstep (se 1 (by rfl) ⟨4053194, by rfl⟩ : syracuseStep 5404259 = 8106389) B8106389
theorem B4798061 : Blo 1421530 4798061 := bstep (se 3 (by rfl) ⟨899636, by rfl⟩ : syracuseStep 4798061 = 1799273) B1799273
theorem B10393201 : Blo 1421530 10393201 := bstep (se 2 (by rfl) ⟨3897450, by rfl⟩ : syracuseStep 10393201 = 7794901) B7794901
theorem B1422963 : Blo 1421530 1422963 := bstep (se 1 (by rfl) ⟨1067222, by rfl⟩ : syracuseStep 1422963 = 2134445) B2134445
theorem B1422979 : Blo 1421530 1422979 := bstep (se 1 (by rfl) ⟨1067234, by rfl⟩ : syracuseStep 1422979 = 2134469) B2134469
theorem B1422995 : Blo 1421530 1422995 := bstep (se 1 (by rfl) ⟨1067246, by rfl⟩ : syracuseStep 1422995 = 2134493) B2134493
theorem B4798115 : Blo 1421530 4798115 := bstep (se 1 (by rfl) ⟨3598586, by rfl⟩ : syracuseStep 4798115 = 7197173) B7197173
theorem B1423011 : Blo 1421530 1423011 := bstep (se 1 (by rfl) ⟨1067258, by rfl⟩ : syracuseStep 1423011 = 2134517) B2134517
theorem B9737891 : Blo 1421530 9737891 := bstep (se 1 (by rfl) ⟨7303418, by rfl⟩ : syracuseStep 9737891 = 14606837) B14606837
theorem B1423027 : Blo 1421530 1423027 := bstep (se 1 (by rfl) ⟨1067270, by rfl⟩ : syracuseStep 1423027 = 2134541) B2134541
theorem B1423043 : Blo 1421530 1423043 := bstep (se 1 (by rfl) ⟨1067282, by rfl⟩ : syracuseStep 1423043 = 2134565) B2134565
theorem B34592453 : Blo 1421530 34592453 := bstep (se 4 (by rfl) ⟨3243042, by rfl⟩ : syracuseStep 34592453 = 6486085) B6486085
theorem B1423059 : Blo 1421530 1423059 := bstep (se 1 (by rfl) ⟨1067294, by rfl⟩ : syracuseStep 1423059 = 2134589) B2134589
theorem B1423075 : Blo 1421530 1423075 := bstep (se 1 (by rfl) ⟨1067306, by rfl⟩ : syracuseStep 1423075 = 2134613) B2134613
theorem B4052717 : Blo 1421530 4052717 := bstep (se 3 (by rfl) ⟨759884, by rfl⟩ : syracuseStep 4052717 = 1519769) B1519769
theorem B1423091 : Blo 1421530 1423091 := bstep (se 1 (by rfl) ⟨1067318, by rfl⟩ : syracuseStep 1423091 = 2134637) B2134637
theorem B1423107 : Blo 1421530 1423107 := bstep (se 1 (by rfl) ⟨1067330, by rfl⟩ : syracuseStep 1423107 = 2134661) B2134661
theorem B1423123 : Blo 1421530 1423123 := bstep (se 1 (by rfl) ⟨1067342, by rfl⟩ : syracuseStep 1423123 = 2134685) B2134685
theorem B1423139 : Blo 1421530 1423139 := bstep (se 1 (by rfl) ⟨1067354, by rfl⟩ : syracuseStep 1423139 = 2134709) B2134709
theorem B1423155 : Blo 1421530 1423155 := bstep (se 1 (by rfl) ⟨1067366, by rfl⟩ : syracuseStep 1423155 = 2134733) B2134733
theorem B1423171 : Blo 1421530 1423171 := bstep (se 1 (by rfl) ⟨1067378, by rfl⟩ : syracuseStep 1423171 = 2134757) B2134757
theorem B3037009 : Blo 1421530 3037009 := bstep (se 2 (by rfl) ⟨1138878, by rfl⟩ : syracuseStep 3037009 = 2277757) B2277757
theorem B3200849 : Blo 1421530 3200849 := bstep (se 2 (by rfl) ⟨1200318, by rfl⟩ : syracuseStep 3200849 = 2400637) B2400637
theorem B1423187 : Blo 1421530 1423187 := bstep (se 1 (by rfl) ⟨1067390, by rfl⟩ : syracuseStep 1423187 = 2134781) B2134781
theorem B3200867 : Blo 1421530 3200867 := bstep (se 1 (by rfl) ⟨2400650, by rfl⟩ : syracuseStep 3200867 = 4801301) B4801301
theorem B1423203 : Blo 1421530 1423203 := bstep (se 1 (by rfl) ⟨1067402, by rfl⟩ : syracuseStep 1423203 = 2134805) B2134805
theorem B1709923 : Blo 1421530 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B1423219 : Blo 1421530 1423219 := bstep (se 1 (by rfl) ⟨1067414, by rfl⟩ : syracuseStep 1423219 = 2134829) B2134829
theorem B1423235 : Blo 1421530 1423235 := bstep (se 1 (by rfl) ⟨1067426, by rfl⟩ : syracuseStep 1423235 = 2134853) B2134853
theorem B1800083 : Blo 1421530 1800083 := bstep (se 1 (by rfl) ⟨1350062, by rfl⟩ : syracuseStep 1800083 = 2700125) B2700125
theorem B1423251 : Blo 1421530 1423251 := bstep (se 1 (by rfl) ⟨1067438, by rfl⟩ : syracuseStep 1423251 = 2134877) B2134877
theorem B6158243 : Blo 1421530 6158243 := bstep (se 1 (by rfl) ⟨4618682, by rfl⟩ : syracuseStep 6158243 = 9237365) B9237365
theorem B1423267 : Blo 1421530 1423267 := bstep (se 1 (by rfl) ⟨1067450, by rfl⟩ : syracuseStep 1423267 = 2134901) B2134901
theorem B4798385 : Blo 1421530 4798385 := bstep (se 2 (by rfl) ⟨1799394, by rfl⟩ : syracuseStep 4798385 = 3598789) B3598789
theorem B3602353 : Blo 1421530 3602353 := bstep (se 2 (by rfl) ⟨1350882, by rfl⟩ : syracuseStep 3602353 = 2701765) B2701765
theorem B1423283 : Blo 1421530 1423283 := bstep (se 1 (by rfl) ⟨1067462, by rfl⟩ : syracuseStep 1423283 = 2134925) B2134925
theorem B1423299 : Blo 1421530 1423299 := bstep (se 1 (by rfl) ⟨1067474, by rfl⟩ : syracuseStep 1423299 = 2134949) B2134949
theorem B1710019 : Blo 1421530 1710019 := bstep (se 1 (by rfl) ⟨1282514, by rfl⟩ : syracuseStep 1710019 = 2565029) B2565029
theorem B1423315 : Blo 1421530 1423315 := bstep (se 1 (by rfl) ⟨1067486, by rfl⟩ : syracuseStep 1423315 = 2134973) B2134973
theorem B1423331 : Blo 1421530 1423331 := bstep (se 1 (by rfl) ⟨1067498, by rfl⟩ : syracuseStep 1423331 = 2134997) B2134997
theorem B1423347 : Blo 1421530 1423347 := bstep (se 1 (by rfl) ⟨1067510, by rfl⟩ : syracuseStep 1423347 = 2135021) B2135021
theorem B1423363 : Blo 1421530 1423363 := bstep (se 1 (by rfl) ⟨1067522, by rfl⟩ : syracuseStep 1423363 = 2135045) B2135045
theorem B1423379 : Blo 1421530 1423379 := bstep (se 1 (by rfl) ⟨1067534, by rfl⟩ : syracuseStep 1423379 = 2135069) B2135069
theorem B1423395 : Blo 1421530 1423395 := bstep (se 1 (by rfl) ⟨1067546, by rfl⟩ : syracuseStep 1423395 = 2135093) B2135093
theorem B4323377 : Blo 1421530 4323377 := bstep (se 2 (by rfl) ⟨1621266, by rfl⟩ : syracuseStep 4323377 = 3242533) B3242533
theorem B4864049 : Blo 1421530 4864049 := bstep (se 2 (by rfl) ⟨1824018, by rfl⟩ : syracuseStep 4864049 = 3648037) B3648037
theorem B1423411 : Blo 1421530 1423411 := bstep (se 1 (by rfl) ⟨1067558, by rfl⟩ : syracuseStep 1423411 = 2135117) B2135117
theorem B1423427 : Blo 1421530 1423427 := bstep (se 1 (by rfl) ⟨1067570, by rfl⟩ : syracuseStep 1423427 = 2135141) B2135141
theorem B3037265 : Blo 1421530 3037265 := bstep (se 2 (by rfl) ⟨1138974, by rfl⟩ : syracuseStep 3037265 = 2277949) B2277949
theorem B1423443 : Blo 1421530 1423443 := bstep (se 1 (by rfl) ⟨1067582, by rfl⟩ : syracuseStep 1423443 = 2135165) B2135165
theorem B1710163 : Blo 1421530 1710163 := bstep (se 1 (by rfl) ⟨1282622, by rfl⟩ : syracuseStep 1710163 = 2565245) B2565245
theorem B1423459 : Blo 1421530 1423459 := bstep (se 1 (by rfl) ⟨1067594, by rfl⟩ : syracuseStep 1423459 = 2135189) B2135189
theorem B3201137 : Blo 1421530 3201137 := bstep (se 2 (by rfl) ⟨1200426, by rfl⟩ : syracuseStep 3201137 = 2400853) B2400853
theorem B1923187 : Blo 1421530 1923187 := bstep (se 1 (by rfl) ⟨1442390, by rfl⟩ : syracuseStep 1923187 = 2884781) B2884781
theorem B1423475 : Blo 1421530 1423475 := bstep (se 1 (by rfl) ⟨1067606, by rfl⟩ : syracuseStep 1423475 = 2135213) B2135213
theorem B3201155 : Blo 1421530 3201155 := bstep (se 1 (by rfl) ⟨2400866, by rfl⟩ : syracuseStep 3201155 = 4801733) B4801733
theorem B1423491 : Blo 1421530 1423491 := bstep (se 1 (by rfl) ⟨1067618, by rfl⟩ : syracuseStep 1423491 = 2135237) B2135237
theorem B1423507 : Blo 1421530 1423507 := bstep (se 1 (by rfl) ⟨1067630, by rfl⟩ : syracuseStep 1423507 = 2135261) B2135261
theorem B1423523 : Blo 1421530 1423523 := bstep (se 1 (by rfl) ⟨1067642, by rfl⟩ : syracuseStep 1423523 = 2135285) B2135285
theorem B2701507 : Blo 1421530 2701507 := bstep (se 1 (by rfl) ⟨2026130, by rfl⟩ : syracuseStep 2701507 = 4052261) B4052261
theorem B3602627 : Blo 1421530 3602627 := bstep (se 1 (by rfl) ⟨2701970, by rfl⟩ : syracuseStep 3602627 = 5403941) B5403941
theorem B6838499 : Blo 1421530 6838499 := bstep (se 1 (by rfl) ⟨5128874, by rfl⟩ : syracuseStep 6838499 = 10257749) B10257749
theorem B5404913 : Blo 1421530 5404913 := bstep (se 2 (by rfl) ⟨2026842, by rfl⟩ : syracuseStep 5404913 = 4053685) B4053685
theorem B8100101 : Blo 1421530 8100101 := bstep (se 4 (by rfl) ⟨759384, by rfl⟩ : syracuseStep 8100101 = 1518769) B1518769
theorem B2701667 : Blo 1421530 2701667 := bstep (se 1 (by rfl) ⟨2026250, by rfl⟩ : syracuseStep 2701667 = 4052501) B4052501
theorem B3602819 : Blo 1421530 3602819 := bstep (se 1 (by rfl) ⟨2702114, by rfl⟩ : syracuseStep 3602819 = 5404229) B5404229
theorem B7199117 : Blo 1421530 7199117 := bstep (se 3 (by rfl) ⟨1349834, by rfl⟩ : syracuseStep 7199117 = 2699669) B2699669
theorem B7297421 : Blo 1421530 7297421 := bstep (se 3 (by rfl) ⟨1368266, by rfl⟩ : syracuseStep 7297421 = 2736533) B2736533
theorem B3201425 : Blo 1421530 3201425 := bstep (se 2 (by rfl) ⟨1200534, by rfl⟩ : syracuseStep 3201425 = 2401069) B2401069
theorem B3201443 : Blo 1421530 3201443 := bstep (se 1 (by rfl) ⟨2401082, by rfl⟩ : syracuseStep 3201443 = 4802165) B4802165
theorem B4798925 : Blo 1421530 4798925 := bstep (se 3 (by rfl) ⟨899798, by rfl⟩ : syracuseStep 4798925 = 1799597) B1799597
theorem B4798979 : Blo 1421530 4798979 := bstep (se 1 (by rfl) ⟨3599234, by rfl⟩ : syracuseStep 4798979 = 7198469) B7198469
theorem B11541005 : Blo 1421530 11541005 := bstep (se 3 (by rfl) ⟨2163938, by rfl⟩ : syracuseStep 11541005 = 4327877) B4327877
theorem B1800787 : Blo 1421530 1800787 := bstep (se 1 (by rfl) ⟨1350590, by rfl⟩ : syracuseStep 1800787 = 2701181) B2701181
theorem B2398835 : Blo 1421530 2398835 := bstep (se 1 (by rfl) ⟨1799126, by rfl⟩ : syracuseStep 2398835 = 3598253) B3598253
theorem B1645171 : Blo 1421530 1645171 := bstep (se 1 (by rfl) ⟨1233878, by rfl⟩ : syracuseStep 1645171 = 2467757) B2467757
theorem B1923745 : Blo 1421530 1923745 := bstep (se 2 (by rfl) ⟨721404, by rfl⟩ : syracuseStep 1923745 = 1442809) B1442809
theorem B3201713 : Blo 1421530 3201713 := bstep (se 2 (by rfl) ⟨1200642, by rfl⟩ : syracuseStep 3201713 = 2401285) B2401285
theorem B1800883 : Blo 1421530 1800883 := bstep (se 1 (by rfl) ⟨1350662, by rfl⟩ : syracuseStep 1800883 = 2701325) B2701325
theorem B3201731 : Blo 1421530 3201731 := bstep (se 1 (by rfl) ⟨2401298, by rfl⟩ : syracuseStep 3201731 = 4802597) B4802597
theorem B8100557 : Blo 1421530 8100557 := bstep (se 3 (by rfl) ⟨1518854, by rfl⟩ : syracuseStep 8100557 = 3037709) B3037709
theorem B2398963 : Blo 1421530 2398963 := bstep (se 1 (by rfl) ⟨1799222, by rfl⟩ : syracuseStep 2398963 = 3598445) B3598445
theorem B4799249 : Blo 1421530 4799249 := bstep (se 2 (by rfl) ⟨1799718, by rfl⟩ : syracuseStep 4799249 = 3599437) B3599437
theorem B6839153 : Blo 1421530 6839153 := bstep (se 2 (by rfl) ⟨2564682, by rfl⟩ : syracuseStep 6839153 = 5129365) B5129365
theorem B2399105 : Blo 1421530 2399105 := bstep (se 2 (by rfl) ⟨899664, by rfl⟩ : syracuseStep 2399105 = 1799329) B1799329
theorem B5397425 : Blo 1421530 5397425 := bstep (se 2 (by rfl) ⟨2024034, by rfl⟩ : syracuseStep 5397425 = 4048069) B4048069
theorem B3202001 : Blo 1421530 3202001 := bstep (se 2 (by rfl) ⟨1200750, by rfl⟩ : syracuseStep 3202001 = 2401501) B2401501
theorem B10796003 : Blo 1421530 10796003 := bstep (se 1 (by rfl) ⟨8097002, by rfl⟩ : syracuseStep 10796003 = 16194005) B16194005
theorem B3202019 : Blo 1421530 3202019 := bstep (se 1 (by rfl) ⟨2401514, by rfl⟩ : syracuseStep 3202019 = 4803029) B4803029
theorem B2399233 : Blo 1421530 2399233 := bstep (se 2 (by rfl) ⟨899712, by rfl⟩ : syracuseStep 2399233 = 1799425) B1799425
theorem B2399267 : Blo 1421530 2399267 := bstep (se 1 (by rfl) ⟨1799450, by rfl⟩ : syracuseStep 2399267 = 3598901) B3598901
theorem B2464913 : Blo 1421530 2464913 := bstep (se 2 (by rfl) ⟨924342, by rfl⟩ : syracuseStep 2464913 = 1848685) B1848685
theorem B2399395 : Blo 1421530 2399395 := bstep (se 1 (by rfl) ⟨1799546, by rfl⟩ : syracuseStep 2399395 = 3599093) B3599093
theorem B1801379 : Blo 1421530 1801379 := bstep (se 1 (by rfl) ⟨1351034, by rfl⟩ : syracuseStep 1801379 = 2702069) B2702069
theorem B1440947 : Blo 1421530 1440947 := bstep (se 1 (by rfl) ⟨1080710, by rfl⟩ : syracuseStep 1440947 = 2161421) B2161421
theorem B65690837 : Blo 1421530 65690837 := bstep (se 7 (by rfl) ⟨769814, by rfl⟩ : syracuseStep 65690837 = 1539629) B1539629
theorem B3202289 : Blo 1421530 3202289 := bstep (se 2 (by rfl) ⟨1200858, by rfl⟩ : syracuseStep 3202289 = 2401717) B2401717
theorem B3202307 : Blo 1421530 3202307 := bstep (se 1 (by rfl) ⟨2401730, by rfl⟩ : syracuseStep 3202307 = 4803461) B4803461
theorem B4799789 : Blo 1421530 4799789 := bstep (se 3 (by rfl) ⟨899960, by rfl⟩ : syracuseStep 4799789 = 1799921) B1799921
theorem B2399537 : Blo 1421530 2399537 := bstep (se 2 (by rfl) ⟨899826, by rfl⟩ : syracuseStep 2399537 = 1799653) B1799653
theorem B8650061 : Blo 1421530 8650061 := bstep (se 3 (by rfl) ⟨1621886, by rfl⟩ : syracuseStep 8650061 = 3243773) B3243773
theorem B4799843 : Blo 1421530 4799843 := bstep (se 1 (by rfl) ⟨3599882, by rfl⟩ : syracuseStep 4799843 = 7199765) B7199765
theorem B3038563 : Blo 1421530 3038563 := bstep (se 1 (by rfl) ⟨2278922, by rfl⟩ : syracuseStep 3038563 = 4557845) B4557845
theorem B2399665 : Blo 1421530 2399665 := bstep (se 2 (by rfl) ⟨899874, by rfl⟩ : syracuseStep 2399665 = 1799749) B1799749
theorem B2399699 : Blo 1421530 2399699 := bstep (se 1 (by rfl) ⟨1799774, by rfl⟩ : syracuseStep 2399699 = 3599549) B3599549
theorem B3202577 : Blo 1421530 3202577 := bstep (se 2 (by rfl) ⟨1200966, by rfl⟩ : syracuseStep 3202577 = 2401933) B2401933
theorem B3202595 : Blo 1421530 3202595 := bstep (se 1 (by rfl) ⟨2401946, by rfl⟩ : syracuseStep 3202595 = 4803893) B4803893
theorem B24288821 : Blo 1421530 24288821 := bstep (se 5 (by rfl) ⟨1138538, by rfl⟩ : syracuseStep 24288821 = 2277077) B2277077
theorem B2399827 : Blo 1421530 2399827 := bstep (se 1 (by rfl) ⟨1799870, by rfl⟩ : syracuseStep 2399827 = 3599741) B3599741
theorem B4800113 : Blo 1421530 4800113 := bstep (se 2 (by rfl) ⟨1800042, by rfl⟩ : syracuseStep 4800113 = 3600085) B3600085
theorem B3038897 : Blo 1421530 3038897 := bstep (se 2 (by rfl) ⟨1139586, by rfl⟩ : syracuseStep 3038897 = 2279173) B2279173
theorem B1949395 : Blo 1421530 1949395 := bstep (se 1 (by rfl) ⟨1462046, by rfl⟩ : syracuseStep 1949395 = 2924093) B2924093
theorem B2399969 : Blo 1421530 2399969 := bstep (se 2 (by rfl) ⟨899988, by rfl⟩ : syracuseStep 2399969 = 1799977) B1799977
theorem B2277155 : Blo 1421530 2277155 := bstep (se 1 (by rfl) ⟨1707866, by rfl⟩ : syracuseStep 2277155 = 3415733) B3415733
theorem B3202865 : Blo 1421530 3202865 := bstep (se 2 (by rfl) ⟨1201074, by rfl⟩ : syracuseStep 3202865 = 2402149) B2402149
theorem B3202883 : Blo 1421530 3202883 := bstep (se 1 (by rfl) ⟨2402162, by rfl⟩ : syracuseStep 3202883 = 4804325) B4804325
theorem B2400097 : Blo 1421530 2400097 := bstep (se 2 (by rfl) ⟨900036, by rfl⟩ : syracuseStep 2400097 = 1800073) B1800073
theorem B2400131 : Blo 1421530 2400131 := bstep (se 1 (by rfl) ⟨1800098, by rfl⟩ : syracuseStep 2400131 = 3600197) B3600197
theorem B8437709 : Blo 1421530 8437709 := bstep (se 3 (by rfl) ⟨1582070, by rfl⟩ : syracuseStep 8437709 = 3164141) B3164141
theorem B11542499 : Blo 1421530 11542499 := bstep (se 1 (by rfl) ⟨8656874, by rfl⟩ : syracuseStep 11542499 = 17313749) B17313749
theorem B43827275 : Blo 1421530 43827275 := bstep (se 1 (by rfl) ⟨32870456, by rfl⟩ : syracuseStep 43827275 = 65740913) B65740913
theorem B7200899 : Blo 1421530 7200899 := bstep (se 1 (by rfl) ⟨5400674, by rfl⟩ : syracuseStep 7200899 = 10801349) B10801349
theorem B2564249 : Blo 1421530 2564249 := bstep (se 2 (by rfl) ⟨961593, by rfl⟩ : syracuseStep 2564249 = 1923187) B1923187
theorem B12149027 : Blo 1421530 12149027 := bstep (se 1 (by rfl) ⟨9111770, by rfl⟩ : syracuseStep 12149027 = 18223541) B18223541
theorem B16204211 : Blo 1421530 16204211 := bstep (se 1 (by rfl) ⟨12153158, by rfl⟩ : syracuseStep 16204211 = 24306317) B24306317
theorem B2163161 : Blo 1421530 2163161 := bstep (se 2 (by rfl) ⟨811185, by rfl⟩ : syracuseStep 2163161 = 1622371) B1622371
theorem B3842525 : Blo 1421530 3842525 := bstep (se 3 (by rfl) ⟨720473, by rfl⟩ : syracuseStep 3842525 = 1440947) B1440947
theorem B2400779 : Blo 1421530 2400779 := bstep (se 1 (by rfl) ⟨1800584, by rfl⟩ : syracuseStep 2400779 = 3601169) B3601169
theorem B19464779 : Blo 1421530 19464779 := bstep (se 1 (by rfl) ⟨14598584, by rfl⟩ : syracuseStep 19464779 = 29197169) B29197169
theorem B2024023 : Blo 1421530 2024023 := bstep (se 1 (by rfl) ⟨1518017, by rfl⟩ : syracuseStep 2024023 = 3036035) B3036035
theorem B8774245 : Blo 1421530 8774245 := bstep (se 4 (by rfl) ⟨822585, by rfl⟩ : syracuseStep 8774245 = 1645171) B1645171
theorem B2400907 : Blo 1421530 2400907 := bstep (se 1 (by rfl) ⟨1800680, by rfl⟩ : syracuseStep 2400907 = 3601361) B3601361
theorem B3039923 : Blo 1421530 3039923 := bstep (se 1 (by rfl) ⟨2279942, by rfl⟩ : syracuseStep 3039923 = 4559885) B4559885
theorem B20497157 : Blo 1421530 20497157 := bstep (se 4 (by rfl) ⟨1921608, by rfl⟩ : syracuseStep 20497157 = 3843217) B3843217
theorem B2401049 : Blo 1421530 2401049 := bstep (se 2 (by rfl) ⟨900393, by rfl⟩ : syracuseStep 2401049 = 1800787) B1800787
theorem B4801355 : Blo 1421530 4801355 := bstep (se 1 (by rfl) ⟨3601016, by rfl⟩ : syracuseStep 4801355 = 7202033) B7202033
theorem B2564993 : Blo 1421530 2564993 := bstep (se 2 (by rfl) ⟨961872, by rfl⟩ : syracuseStep 2564993 = 1923745) B1923745
theorem B2401177 : Blo 1421530 2401177 := bstep (se 2 (by rfl) ⟨900441, by rfl⟩ : syracuseStep 2401177 = 1800883) B1800883
theorem B3245015 : Blo 1421530 3245015 := bstep (se 1 (by rfl) ⟨2433761, by rfl⟩ : syracuseStep 3245015 = 4867523) B4867523
theorem B2884619 : Blo 1421530 2884619 := bstep (se 1 (by rfl) ⟨2163464, by rfl⟩ : syracuseStep 2884619 = 4326929) B4326929
theorem B2278487 : Blo 1421530 2278487 := bstep (se 1 (by rfl) ⟨1708865, by rfl⟩ : syracuseStep 2278487 = 3417731) B3417731
theorem B4801625 : Blo 1421530 4801625 := bstep (se 2 (by rfl) ⟨1800609, by rfl⟩ : syracuseStep 4801625 = 3601219) B3601219
theorem B23061635 : Blo 1421530 23061635 := bstep (se 1 (by rfl) ⟨17296226, by rfl⟩ : syracuseStep 23061635 = 34592453) B34592453
theorem B2278615 : Blo 1421530 2278615 := bstep (se 1 (by rfl) ⟨1708961, by rfl⟩ : syracuseStep 2278615 = 3417923) B3417923
theorem B2278667 : Blo 1421530 2278667 := bstep (se 1 (by rfl) ⟨1709000, by rfl⟩ : syracuseStep 2278667 = 3418001) B3418001
theorem B4105495 : Blo 1421530 4105495 := bstep (se 1 (by rfl) ⟨3079121, by rfl⟩ : syracuseStep 4105495 = 6158243) B6158243
theorem B34604333 : Blo 1421530 34604333 := bstep (se 3 (by rfl) ⟨6488312, by rfl⟩ : syracuseStep 34604333 = 12976625) B12976625
theorem B2024843 : Blo 1421530 2024843 := bstep (se 1 (by rfl) ⟨1518632, by rfl⟩ : syracuseStep 2024843 = 3037265) B3037265
theorem B2278795 : Blo 1421530 2278795 := bstep (se 1 (by rfl) ⟨1709096, by rfl⟩ : syracuseStep 2278795 = 3418193) B3418193
theorem B2401751 : Blo 1421530 2401751 := bstep (se 1 (by rfl) ⟨1801313, by rfl⟩ : syracuseStep 2401751 = 3602627) B3602627
theorem B5400067 : Blo 1421530 5400067 := bstep (se 1 (by rfl) ⟨4050050, by rfl⟩ : syracuseStep 5400067 = 8100101) B8100101
theorem B2401879 : Blo 1421530 2401879 := bstep (se 1 (by rfl) ⟨1801409, by rfl⟩ : syracuseStep 2401879 = 3602819) B3602819
theorem B12977795 : Blo 1421530 12977795 := bstep (se 1 (by rfl) ⟨9733346, by rfl⟩ : syracuseStep 12977795 = 19466693) B19466693
theorem B20514455 : Blo 1421530 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B7694003 : Blo 1421530 7694003 := bstep (se 1 (by rfl) ⟨5770502, by rfl⟩ : syracuseStep 7694003 = 11541005) B11541005
theorem B36439793 : Blo 1421530 36439793 := bstep (se 2 (by rfl) ⟨13664922, by rfl⟩ : syracuseStep 36439793 = 27329845) B27329845
theorem B1599223 : Blo 1421530 1599223 := bstep (se 1 (by rfl) ⟨1199417, by rfl⟩ : syracuseStep 1599223 = 2398835) B2398835
theorem B2279179 : Blo 1421530 2279179 := bstep (se 1 (by rfl) ⟨1709384, by rfl⟩ : syracuseStep 2279179 = 3418769) B3418769
theorem B4802327 : Blo 1421530 4802327 := bstep (se 1 (by rfl) ⟨3601745, by rfl⟩ : syracuseStep 4802327 = 7203491) B7203491
theorem B8103725 : Blo 1421530 8103725 := bstep (se 3 (by rfl) ⟨1519448, by rfl⟩ : syracuseStep 8103725 = 3038897) B3038897
theorem B5400371 : Blo 1421530 5400371 := bstep (se 1 (by rfl) ⟨4050278, by rfl⟩ : syracuseStep 5400371 = 8100557) B8100557
theorem B10250077 : Blo 1421530 10250077 := bstep (se 3 (by rfl) ⟨1921889, by rfl⟩ : syracuseStep 10250077 = 3843779) B3843779
theorem B16205669 : Blo 1421530 16205669 := bstep (se 4 (by rfl) ⟨1519281, by rfl⟩ : syracuseStep 16205669 = 3038563) B3038563
theorem B1599403 : Blo 1421530 1599403 := bstep (se 1 (by rfl) ⟨1199552, by rfl⟩ : syracuseStep 1599403 = 2399105) B2399105
theorem B3598283 : Blo 1421530 3598283 := bstep (se 1 (by rfl) ⟨2698712, by rfl⟩ : syracuseStep 3598283 = 5397425) B5397425
theorem B2279435 : Blo 1421530 2279435 := bstep (se 1 (by rfl) ⟨1709576, by rfl⟩ : syracuseStep 2279435 = 3419153) B3419153
theorem B1599511 : Blo 1421530 1599511 := bstep (se 1 (by rfl) ⟨1199633, by rfl⟩ : syracuseStep 1599511 = 2399267) B2399267
theorem B12978269 : Blo 1421530 12978269 := bstep (se 3 (by rfl) ⟨2433425, by rfl⟩ : syracuseStep 12978269 = 4866851) B4866851
theorem B6834307 : Blo 1421530 6834307 := bstep (se 1 (by rfl) ⟨5125730, by rfl⟩ : syracuseStep 6834307 = 10251461) B10251461
theorem B1599691 : Blo 1421530 1599691 := bstep (se 1 (by rfl) ⟨1199768, by rfl⟩ : syracuseStep 1599691 = 2399537) B2399537
theorem B2599193 : Blo 1421530 2599193 := bstep (se 2 (by rfl) ⟨974697, by rfl⟩ : syracuseStep 2599193 = 1949395) B1949395
theorem B10799405 : Blo 1421530 10799405 := bstep (se 3 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 10799405 = 4049777) B4049777
theorem B49293613 : Blo 1421530 49293613 := bstep (se 3 (by rfl) ⟨9242552, by rfl⟩ : syracuseStep 49293613 = 18485105) B18485105
theorem B4802867 : Blo 1421530 4802867 := bstep (se 1 (by rfl) ⟨3602150, by rfl⟩ : syracuseStep 4802867 = 7204301) B7204301
theorem B1599799 : Blo 1421530 1599799 := bstep (se 1 (by rfl) ⟨1199849, by rfl⟩ : syracuseStep 1599799 = 2399699) B2399699
theorem B2132363 : Blo 1421530 2132363 := bstep (se 1 (by rfl) ⟨1599272, by rfl⟩ : syracuseStep 2132363 = 3198545) B3198545
theorem B2132375 : Blo 1421530 2132375 := bstep (se 1 (by rfl) ⟨1599281, by rfl⟩ : syracuseStep 2132375 = 3198563) B3198563
theorem B4049345 : Blo 1421530 4049345 := bstep (se 2 (by rfl) ⟨1518504, by rfl⟩ : syracuseStep 4049345 = 3037009) B3037009
theorem B5401025 : Blo 1421530 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B2132441 : Blo 1421530 2132441 := bstep (se 2 (by rfl) ⟨799665, by rfl⟩ : syracuseStep 2132441 = 1599331) B1599331
theorem B2279897 : Blo 1421530 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B1599979 : Blo 1421530 1599979 := bstep (se 1 (by rfl) ⟨1199984, by rfl⟩ : syracuseStep 1599979 = 2399969) B2399969
theorem B1518103 : Blo 1421530 1518103 := bstep (se 1 (by rfl) ⟨1138577, by rfl⟩ : syracuseStep 1518103 = 2277155) B2277155
theorem B4049459 : Blo 1421530 4049459 := bstep (se 1 (by rfl) ⟨3037094, by rfl⟩ : syracuseStep 4049459 = 6074189) B6074189
theorem B4803137 : Blo 1421530 4803137 := bstep (se 2 (by rfl) ⟨1801176, by rfl⟩ : syracuseStep 4803137 = 3602353) B3602353
theorem B2132555 : Blo 1421530 2132555 := bstep (se 1 (by rfl) ⟨1599416, by rfl⟩ : syracuseStep 2132555 = 3198833) B3198833
theorem B2132567 : Blo 1421530 2132567 := bstep (se 1 (by rfl) ⟨1599425, by rfl⟩ : syracuseStep 2132567 = 3198851) B3198851
theorem B1600087 : Blo 1421530 1600087 := bstep (se 1 (by rfl) ⟨1200065, by rfl⟩ : syracuseStep 1600087 = 2400131) B2400131
theorem B2280025 : Blo 1421530 2280025 := bstep (se 2 (by rfl) ⟨855009, by rfl⟩ : syracuseStep 2280025 = 1710019) B1710019
theorem B7694999 : Blo 1421530 7694999 := bstep (se 1 (by rfl) ⟨5771249, by rfl⟩ : syracuseStep 7694999 = 11542499) B11542499
theorem B2132633 : Blo 1421530 2132633 := bstep (se 2 (by rfl) ⟨799737, by rfl⟩ : syracuseStep 2132633 = 1599475) B1599475
theorem B8096435 : Blo 1421530 8096435 := bstep (se 1 (by rfl) ⟨6072326, by rfl⟩ : syracuseStep 8096435 = 12144653) B12144653
theorem B2132747 : Blo 1421530 2132747 := bstep (se 1 (by rfl) ⟨1599560, by rfl⟩ : syracuseStep 2132747 = 3199121) B3199121
theorem B1600267 : Blo 1421530 1600267 := bstep (se 1 (by rfl) ⟨1200200, by rfl⟩ : syracuseStep 1600267 = 2400401) B2400401
theorem B2132759 : Blo 1421530 2132759 := bstep (se 1 (by rfl) ⟨1599569, by rfl⟩ : syracuseStep 2132759 = 3199139) B3199139
theorem B1518359 : Blo 1421530 1518359 := bstep (se 1 (by rfl) ⟨1138769, by rfl⟩ : syracuseStep 1518359 = 2277539) B2277539
theorem B6073163 : Blo 1421530 6073163 := bstep (se 1 (by rfl) ⟨4554872, by rfl⟩ : syracuseStep 6073163 = 9109745) B9109745
theorem B2132825 : Blo 1421530 2132825 := bstep (se 2 (by rfl) ⟨799809, by rfl⟩ : syracuseStep 2132825 = 1599619) B1599619
theorem B1600375 : Blo 1421530 1600375 := bstep (se 1 (by rfl) ⟨1200281, by rfl⟩ : syracuseStep 1600375 = 2400563) B2400563
theorem B3599255 : Blo 1421530 3599255 := bstep (se 1 (by rfl) ⟨2699441, by rfl⟩ : syracuseStep 3599255 = 5398883) B5398883
theorem B2567065 : Blo 1421530 2567065 := bstep (se 2 (by rfl) ⟨962649, by rfl⟩ : syracuseStep 2567065 = 1925299) B1925299
theorem B2132939 : Blo 1421530 2132939 := bstep (se 1 (by rfl) ⟨1599704, by rfl⟩ : syracuseStep 2132939 = 3199409) B3199409
theorem B2132951 : Blo 1421530 2132951 := bstep (se 1 (by rfl) ⟨1599713, by rfl⟩ : syracuseStep 2132951 = 3199427) B3199427
theorem B2133017 : Blo 1421530 2133017 := bstep (se 2 (by rfl) ⟨799881, by rfl⟩ : syracuseStep 2133017 = 1599763) B1599763
theorem B1600555 : Blo 1421530 1600555 := bstep (se 1 (by rfl) ⟨1200416, by rfl⟩ : syracuseStep 1600555 = 2400833) B2400833
theorem B4803677 : Blo 1421530 4803677 := bstep (se 3 (by rfl) ⟨900689, by rfl⟩ : syracuseStep 4803677 = 1801379) B1801379
theorem B9120869 : Blo 1421530 9120869 := bstep (se 4 (by rfl) ⟨855081, by rfl⟩ : syracuseStep 9120869 = 1710163) B1710163
theorem B2133131 : Blo 1421530 2133131 := bstep (se 1 (by rfl) ⟨1599848, by rfl⟩ : syracuseStep 2133131 = 3199697) B3199697
theorem B2133143 : Blo 1421530 2133143 := bstep (se 1 (by rfl) ⟨1599857, by rfl⟩ : syracuseStep 2133143 = 3199715) B3199715
theorem B1600663 : Blo 1421530 1600663 := bstep (se 1 (by rfl) ⟨1200497, by rfl⟩ : syracuseStep 1600663 = 2400995) B2400995
theorem B2026711 : Blo 1421530 2026711 := bstep (se 1 (by rfl) ⟨1520033, by rfl⟩ : syracuseStep 2026711 = 3040067) B3040067
theorem B2133209 : Blo 1421530 2133209 := bstep (se 2 (by rfl) ⟨799953, by rfl⟩ : syracuseStep 2133209 = 1599907) B1599907
theorem B55430405 : Blo 1421530 55430405 := bstep (se 4 (by rfl) ⟨5196600, by rfl⟩ : syracuseStep 55430405 = 10393201) B10393201
theorem B4558103 : Blo 1421530 4558103 := bstep (se 1 (by rfl) ⟨3418577, by rfl⟩ : syracuseStep 4558103 = 6837155) B6837155
theorem B2133323 : Blo 1421530 2133323 := bstep (se 1 (by rfl) ⟨1599992, by rfl⟩ : syracuseStep 2133323 = 3199985) B3199985
theorem B1518923 : Blo 1421530 1518923 := bstep (se 1 (by rfl) ⟨1139192, by rfl⟩ : syracuseStep 1518923 = 2278385) B2278385
theorem B1600843 : Blo 1421530 1600843 := bstep (se 1 (by rfl) ⟨1200632, by rfl⟩ : syracuseStep 1600843 = 2401265) B2401265
theorem B2133335 : Blo 1421530 2133335 := bstep (se 1 (by rfl) ⟨1600001, by rfl⟩ : syracuseStep 2133335 = 3200003) B3200003
theorem B36466037 : Blo 1421530 36466037 := bstep (se 5 (by rfl) ⟨1709345, by rfl⟩ : syracuseStep 36466037 = 3418691) B3418691
theorem B2133401 : Blo 1421530 2133401 := bstep (se 2 (by rfl) ⟨800025, by rfl⟩ : syracuseStep 2133401 = 1600051) B1600051
theorem B1600951 : Blo 1421530 1600951 := bstep (se 1 (by rfl) ⟨1200713, by rfl⟩ : syracuseStep 1600951 = 2401427) B2401427
theorem B2133515 : Blo 1421530 2133515 := bstep (se 1 (by rfl) ⟨1600136, by rfl⟩ : syracuseStep 2133515 = 3200273) B3200273
theorem B2133527 : Blo 1421530 2133527 := bstep (se 1 (by rfl) ⟨1600145, by rfl⟩ : syracuseStep 2133527 = 3200291) B3200291
theorem B3599923 : Blo 1421530 3599923 := bstep (se 1 (by rfl) ⟨2699942, by rfl⟩ : syracuseStep 3599923 = 5399885) B5399885
theorem B2133593 : Blo 1421530 2133593 := bstep (se 2 (by rfl) ⟨800097, by rfl⟩ : syracuseStep 2133593 = 1600195) B1600195
theorem B1601131 : Blo 1421530 1601131 := bstep (se 1 (by rfl) ⟨1200848, by rfl⟩ : syracuseStep 1601131 = 2401697) B2401697
theorem B3198617 : Blo 1421530 3198617 := bstep (se 2 (by rfl) ⟨1199481, by rfl⟩ : syracuseStep 3198617 = 2398963) B2398963
theorem B5402285 : Blo 1421530 5402285 := bstep (se 3 (by rfl) ⟨1012928, by rfl⟩ : syracuseStep 5402285 = 2025857) B2025857
theorem B3600065 : Blo 1421530 3600065 := bstep (se 2 (by rfl) ⟨1350024, by rfl⟩ : syracuseStep 3600065 = 2700049) B2700049
theorem B2133707 : Blo 1421530 2133707 := bstep (se 1 (by rfl) ⟨1600280, by rfl⟩ : syracuseStep 2133707 = 3200561) B3200561
theorem B5402315 : Blo 1421530 5402315 := bstep (se 1 (by rfl) ⟨4051736, by rfl⟩ : syracuseStep 5402315 = 8103473) B8103473
theorem B2133719 : Blo 1421530 2133719 := bstep (se 1 (by rfl) ⟨1600289, by rfl⟩ : syracuseStep 2133719 = 3200579) B3200579
theorem B1601239 : Blo 1421530 1601239 := bstep (se 1 (by rfl) ⟨1200929, by rfl⟩ : syracuseStep 1601239 = 2401859) B2401859
theorem B3198707 : Blo 1421530 3198707 := bstep (se 1 (by rfl) ⟨2399030, by rfl⟩ : syracuseStep 3198707 = 4798061) B4798061
theorem B7204625 : Blo 1421530 7204625 := bstep (se 2 (by rfl) ⟨2701734, by rfl⟩ : syracuseStep 7204625 = 5403469) B5403469
theorem B3198743 : Blo 1421530 3198743 := bstep (se 1 (by rfl) ⟨2399057, by rfl⟩ : syracuseStep 3198743 = 4798115) B4798115
theorem B6491927 : Blo 1421530 6491927 := bstep (se 1 (by rfl) ⟨4868945, by rfl⟩ : syracuseStep 6491927 = 9737891) B9737891
theorem B2133785 : Blo 1421530 2133785 := bstep (se 2 (by rfl) ⟨800169, by rfl⟩ : syracuseStep 2133785 = 1600339) B1600339
theorem B12160813 : Blo 1421530 12160813 := bstep (se 3 (by rfl) ⟨2280152, by rfl⟩ : syracuseStep 12160813 = 4560305) B4560305
theorem B29200193 : Blo 1421530 29200193 := bstep (se 2 (by rfl) ⟨10950072, by rfl⟩ : syracuseStep 29200193 = 21900145) B21900145
theorem B2133899 : Blo 1421530 2133899 := bstep (se 1 (by rfl) ⟨1600424, by rfl⟩ : syracuseStep 2133899 = 3200849) B3200849
theorem B1601419 : Blo 1421530 1601419 := bstep (se 1 (by rfl) ⟨1201064, by rfl⟩ : syracuseStep 1601419 = 2402129) B2402129
theorem B2133911 : Blo 1421530 2133911 := bstep (se 1 (by rfl) ⟨1600433, by rfl⟩ : syracuseStep 2133911 = 3200867) B3200867
theorem B6074291 : Blo 1421530 6074291 := bstep (se 1 (by rfl) ⟨4555718, by rfl⟩ : syracuseStep 6074291 = 9111437) B9111437
theorem B7204787 : Blo 1421530 7204787 := bstep (se 1 (by rfl) ⟨5403590, by rfl⟩ : syracuseStep 7204787 = 10807181) B10807181
theorem B3198923 : Blo 1421530 3198923 := bstep (se 1 (by rfl) ⟨2399192, by rfl⟩ : syracuseStep 3198923 = 4798385) B4798385
theorem B2133977 : Blo 1421530 2133977 := bstep (se 2 (by rfl) ⟨800241, by rfl⟩ : syracuseStep 2133977 = 1600483) B1600483
theorem B3198977 : Blo 1421530 3198977 := bstep (se 2 (by rfl) ⟨1199616, by rfl⟩ : syracuseStep 3198977 = 2399233) B2399233
theorem B2134091 : Blo 1421530 2134091 := bstep (se 1 (by rfl) ⟨1600568, by rfl⟩ : syracuseStep 2134091 = 3201137) B3201137
theorem B17789003 : Blo 1421530 17789003 := bstep (se 1 (by rfl) ⟨13341752, by rfl⟩ : syracuseStep 17789003 = 26683505) B26683505
theorem B2134103 : Blo 1421530 2134103 := bstep (se 1 (by rfl) ⟨1600577, by rfl⟩ : syracuseStep 2134103 = 3201155) B3201155
theorem B8097893 : Blo 1421530 8097893 := bstep (se 4 (by rfl) ⟨759177, by rfl⟩ : syracuseStep 8097893 = 1518355) B1518355
theorem B8106115 : Blo 1421530 8106115 := bstep (se 1 (by rfl) ⟨6079586, by rfl⟩ : syracuseStep 8106115 = 12159173) B12159173
theorem B4558999 : Blo 1421530 4558999 := bstep (se 1 (by rfl) ⟨3419249, by rfl⟩ : syracuseStep 4558999 = 6838499) B6838499
theorem B2134169 : Blo 1421530 2134169 := bstep (se 2 (by rfl) ⟨800313, by rfl⟩ : syracuseStep 2134169 = 1600627) B1600627
theorem B3199193 : Blo 1421530 3199193 := bstep (se 2 (by rfl) ⟨1199697, by rfl⟩ : syracuseStep 3199193 = 2399395) B2399395
theorem B1421547 : Blo 1421530 1421547 := bstep (se 1 (by rfl) ⟨1066160, by rfl⟩ : syracuseStep 1421547 = 2132321) B2132321
theorem B1421559 : Blo 1421530 1421559 := bstep (se 1 (by rfl) ⟨1066169, by rfl⟩ : syracuseStep 1421559 = 2132339) B2132339
theorem B1421579 : Blo 1421530 1421579 := bstep (se 1 (by rfl) ⟨1066184, by rfl⟩ : syracuseStep 1421579 = 2132369) B2132369
theorem B2134283 : Blo 1421530 2134283 := bstep (se 1 (by rfl) ⟨1600712, by rfl⟩ : syracuseStep 2134283 = 3201425) B3201425
theorem B1421591 : Blo 1421530 1421591 := bstep (se 1 (by rfl) ⟨1066193, by rfl⟩ : syracuseStep 1421591 = 2132387) B2132387
theorem B2134295 : Blo 1421530 2134295 := bstep (se 1 (by rfl) ⟨1600721, by rfl⟩ : syracuseStep 2134295 = 3201443) B3201443
theorem B1421611 : Blo 1421530 1421611 := bstep (se 1 (by rfl) ⟨1066208, by rfl⟩ : syracuseStep 1421611 = 2132417) B2132417
theorem B3199283 : Blo 1421530 3199283 := bstep (se 1 (by rfl) ⟨2399462, by rfl⟩ : syracuseStep 3199283 = 4798925) B4798925
theorem B1421623 : Blo 1421530 1421623 := bstep (se 1 (by rfl) ⟨1066217, by rfl⟩ : syracuseStep 1421623 = 2132435) B2132435
theorem B1421643 : Blo 1421530 1421643 := bstep (se 1 (by rfl) ⟨1066232, by rfl⟩ : syracuseStep 1421643 = 2132465) B2132465
theorem B1421655 : Blo 1421530 1421655 := bstep (se 1 (by rfl) ⟨1066241, by rfl⟩ : syracuseStep 1421655 = 2132483) B2132483
theorem B3199319 : Blo 1421530 3199319 := bstep (se 1 (by rfl) ⟨2399489, by rfl⟩ : syracuseStep 3199319 = 4798979) B4798979
theorem B2134361 : Blo 1421530 2134361 := bstep (se 2 (by rfl) ⟨800385, by rfl⟩ : syracuseStep 2134361 = 1600771) B1600771
theorem B5402969 : Blo 1421530 5402969 := bstep (se 2 (by rfl) ⟨2026113, by rfl⟩ : syracuseStep 5402969 = 4052227) B4052227
theorem B1421675 : Blo 1421530 1421675 := bstep (se 1 (by rfl) ⟨1066256, by rfl⟩ : syracuseStep 1421675 = 2132513) B2132513
theorem B1421687 : Blo 1421530 1421687 := bstep (se 1 (by rfl) ⟨1066265, by rfl⟩ : syracuseStep 1421687 = 2132531) B2132531
theorem B1421707 : Blo 1421530 1421707 := bstep (se 1 (by rfl) ⟨1066280, by rfl⟩ : syracuseStep 1421707 = 2132561) B2132561
theorem B1421719 : Blo 1421530 1421719 := bstep (se 1 (by rfl) ⟨1066289, by rfl⟩ : syracuseStep 1421719 = 2132579) B2132579
theorem B1421739 : Blo 1421530 1421739 := bstep (se 1 (by rfl) ⟨1066304, by rfl⟩ : syracuseStep 1421739 = 2132609) B2132609
theorem B1421751 : Blo 1421530 1421751 := bstep (se 1 (by rfl) ⟨1066313, by rfl⟩ : syracuseStep 1421751 = 2132627) B2132627
theorem B1421771 : Blo 1421530 1421771 := bstep (se 1 (by rfl) ⟨1066328, by rfl⟩ : syracuseStep 1421771 = 2132657) B2132657
theorem B2699723 : Blo 1421530 2699723 := bstep (se 1 (by rfl) ⟨2024792, by rfl⟩ : syracuseStep 2699723 = 4049585) B4049585
theorem B2134475 : Blo 1421530 2134475 := bstep (se 1 (by rfl) ⟨1600856, by rfl⟩ : syracuseStep 2134475 = 3201713) B3201713
theorem B1421783 : Blo 1421530 1421783 := bstep (se 1 (by rfl) ⟨1066337, by rfl⟩ : syracuseStep 1421783 = 2132675) B2132675
theorem B2134487 : Blo 1421530 2134487 := bstep (se 1 (by rfl) ⟨1600865, by rfl⟩ : syracuseStep 2134487 = 3201731) B3201731
theorem B1421803 : Blo 1421530 1421803 := bstep (se 1 (by rfl) ⟨1066352, by rfl⟩ : syracuseStep 1421803 = 2132705) B2132705
theorem B1421815 : Blo 1421530 1421815 := bstep (se 1 (by rfl) ⟨1066361, by rfl⟩ : syracuseStep 1421815 = 2132723) B2132723
theorem B1421835 : Blo 1421530 1421835 := bstep (se 1 (by rfl) ⟨1066376, by rfl⟩ : syracuseStep 1421835 = 2132753) B2132753
theorem B3199499 : Blo 1421530 3199499 := bstep (se 1 (by rfl) ⟨2399624, by rfl⟩ : syracuseStep 3199499 = 4799249) B4799249
theorem B1421847 : Blo 1421530 1421847 := bstep (se 1 (by rfl) ⟨1066385, by rfl⟩ : syracuseStep 1421847 = 2132771) B2132771
theorem B2134553 : Blo 1421530 2134553 := bstep (se 2 (by rfl) ⟨800457, by rfl⟩ : syracuseStep 2134553 = 1600915) B1600915
theorem B1421867 : Blo 1421530 1421867 := bstep (se 1 (by rfl) ⟨1066400, by rfl⟩ : syracuseStep 1421867 = 2132801) B2132801
theorem B1421879 : Blo 1421530 1421879 := bstep (se 1 (by rfl) ⟨1066409, by rfl⟩ : syracuseStep 1421879 = 2132819) B2132819
theorem B3199553 : Blo 1421530 3199553 := bstep (se 2 (by rfl) ⟨1199832, by rfl⟩ : syracuseStep 3199553 = 2399665) B2399665
theorem B4108865 : Blo 1421530 4108865 := bstep (se 2 (by rfl) ⟨1540824, by rfl⟩ : syracuseStep 4108865 = 3081649) B3081649
theorem B1421899 : Blo 1421530 1421899 := bstep (se 1 (by rfl) ⟨1066424, by rfl⟩ : syracuseStep 1421899 = 2132849) B2132849
theorem B4559435 : Blo 1421530 4559435 := bstep (se 1 (by rfl) ⟨3419576, by rfl⟩ : syracuseStep 4559435 = 6839153) B6839153
theorem B1421911 : Blo 1421530 1421911 := bstep (se 1 (by rfl) ⟨1066433, by rfl⟩ : syracuseStep 1421911 = 2132867) B2132867
theorem B1421931 : Blo 1421530 1421931 := bstep (se 1 (by rfl) ⟨1066448, by rfl⟩ : syracuseStep 1421931 = 2132897) B2132897
theorem B1421943 : Blo 1421530 1421943 := bstep (se 1 (by rfl) ⟨1066457, by rfl⟩ : syracuseStep 1421943 = 2132915) B2132915
theorem B2699905 : Blo 1421530 2699905 := bstep (se 2 (by rfl) ⟨1012464, by rfl⟩ : syracuseStep 2699905 = 2024929) B2024929
theorem B1421963 : Blo 1421530 1421963 := bstep (se 1 (by rfl) ⟨1066472, by rfl⟩ : syracuseStep 1421963 = 2132945) B2132945
theorem B2134667 : Blo 1421530 2134667 := bstep (se 1 (by rfl) ⟨1601000, by rfl⟩ : syracuseStep 2134667 = 3202001) B3202001
theorem B7197335 : Blo 1421530 7197335 := bstep (se 1 (by rfl) ⟨5398001, by rfl⟩ : syracuseStep 7197335 = 10796003) B10796003
theorem B1421975 : Blo 1421530 1421975 := bstep (se 1 (by rfl) ⟨1066481, by rfl⟩ : syracuseStep 1421975 = 2132963) B2132963
theorem B5403287 : Blo 1421530 5403287 := bstep (se 1 (by rfl) ⟨4052465, by rfl⟩ : syracuseStep 5403287 = 8104931) B8104931
theorem B2134679 : Blo 1421530 2134679 := bstep (se 1 (by rfl) ⟨1601009, by rfl⟩ : syracuseStep 2134679 = 3202019) B3202019
theorem B1421995 : Blo 1421530 1421995 := bstep (se 1 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 1421995 = 2132993) B2132993
theorem B1422007 : Blo 1421530 1422007 := bstep (se 1 (by rfl) ⟨1066505, by rfl⟩ : syracuseStep 1422007 = 2133011) B2133011
theorem B1422027 : Blo 1421530 1422027 := bstep (se 1 (by rfl) ⟨1066520, by rfl⟩ : syracuseStep 1422027 = 2133041) B2133041
theorem B1422039 : Blo 1421530 1422039 := bstep (se 1 (by rfl) ⟨1066529, by rfl⟩ : syracuseStep 1422039 = 2133059) B2133059
theorem B2134745 : Blo 1421530 2134745 := bstep (se 2 (by rfl) ⟨800529, by rfl⟩ : syracuseStep 2134745 = 1601059) B1601059
theorem B1422059 : Blo 1421530 1422059 := bstep (se 1 (by rfl) ⟨1066544, by rfl⟩ : syracuseStep 1422059 = 2133089) B2133089
theorem B1422071 : Blo 1421530 1422071 := bstep (se 1 (by rfl) ⟨1066553, by rfl⟩ : syracuseStep 1422071 = 2133107) B2133107
theorem B1643275 : Blo 1421530 1643275 := bstep (se 1 (by rfl) ⟨1232456, by rfl⟩ : syracuseStep 1643275 = 2464913) B2464913
theorem B1422091 : Blo 1421530 1422091 := bstep (se 1 (by rfl) ⟨1066568, by rfl⟩ : syracuseStep 1422091 = 2133137) B2133137
theorem B1422103 : Blo 1421530 1422103 := bstep (se 1 (by rfl) ⟨1066577, by rfl⟩ : syracuseStep 1422103 = 2133155) B2133155
theorem B3199769 : Blo 1421530 3199769 := bstep (se 2 (by rfl) ⟨1199913, by rfl⟩ : syracuseStep 3199769 = 2399827) B2399827
theorem B3207959 : Blo 1421530 3207959 := bstep (se 1 (by rfl) ⟨2405969, by rfl⟩ : syracuseStep 3207959 = 4811939) B4811939
theorem B1422123 : Blo 1421530 1422123 := bstep (se 1 (by rfl) ⟨1066592, by rfl⟩ : syracuseStep 1422123 = 2133185) B2133185
theorem B1422135 : Blo 1421530 1422135 := bstep (se 1 (by rfl) ⟨1066601, by rfl⟩ : syracuseStep 1422135 = 2133203) B2133203
theorem B1422155 : Blo 1421530 1422155 := bstep (se 1 (by rfl) ⟨1066616, by rfl⟩ : syracuseStep 1422155 = 2133233) B2133233
theorem B2134859 : Blo 1421530 2134859 := bstep (se 1 (by rfl) ⟨1601144, by rfl⟩ : syracuseStep 2134859 = 3202289) B3202289
theorem B1422167 : Blo 1421530 1422167 := bstep (se 1 (by rfl) ⟨1066625, by rfl⟩ : syracuseStep 1422167 = 2133251) B2133251
theorem B2134871 : Blo 1421530 2134871 := bstep (se 1 (by rfl) ⟨1601153, by rfl⟩ : syracuseStep 2134871 = 3202307) B3202307
theorem B1422187 : Blo 1421530 1422187 := bstep (se 1 (by rfl) ⟨1066640, by rfl⟩ : syracuseStep 1422187 = 2133281) B2133281
theorem B3199859 : Blo 1421530 3199859 := bstep (se 1 (by rfl) ⟨2399894, by rfl⟩ : syracuseStep 3199859 = 4799789) B4799789
theorem B1422199 : Blo 1421530 1422199 := bstep (se 1 (by rfl) ⟨1066649, by rfl⟩ : syracuseStep 1422199 = 2133299) B2133299
theorem B1422219 : Blo 1421530 1422219 := bstep (se 1 (by rfl) ⟨1066664, by rfl⟩ : syracuseStep 1422219 = 2133329) B2133329
theorem B3199895 : Blo 1421530 3199895 := bstep (se 1 (by rfl) ⟨2399921, by rfl⟩ : syracuseStep 3199895 = 4799843) B4799843
theorem B1422231 : Blo 1421530 1422231 := bstep (se 1 (by rfl) ⟨1066673, by rfl⟩ : syracuseStep 1422231 = 2133347) B2133347
theorem B2134937 : Blo 1421530 2134937 := bstep (se 2 (by rfl) ⟨800601, by rfl⟩ : syracuseStep 2134937 = 1601203) B1601203
theorem B1422251 : Blo 1421530 1422251 := bstep (se 1 (by rfl) ⟨1066688, by rfl⟩ : syracuseStep 1422251 = 2133377) B2133377
theorem B3601331 : Blo 1421530 3601331 := bstep (se 1 (by rfl) ⟨2700998, by rfl⟩ : syracuseStep 3601331 = 5401997) B5401997
theorem B1422263 : Blo 1421530 1422263 := bstep (se 1 (by rfl) ⟨1066697, by rfl⟩ : syracuseStep 1422263 = 2133395) B2133395
theorem B1422283 : Blo 1421530 1422283 := bstep (se 1 (by rfl) ⟨1066712, by rfl⟩ : syracuseStep 1422283 = 2133425) B2133425
theorem B1422295 : Blo 1421530 1422295 := bstep (se 1 (by rfl) ⟨1066721, by rfl⟩ : syracuseStep 1422295 = 2133443) B2133443
theorem B1422315 : Blo 1421530 1422315 := bstep (se 1 (by rfl) ⟨1066736, by rfl⟩ : syracuseStep 1422315 = 2133473) B2133473
theorem B1422327 : Blo 1421530 1422327 := bstep (se 1 (by rfl) ⟨1066745, by rfl⟩ : syracuseStep 1422327 = 2133491) B2133491
theorem B1422347 : Blo 1421530 1422347 := bstep (se 1 (by rfl) ⟨1066760, by rfl⟩ : syracuseStep 1422347 = 2133521) B2133521
theorem B2135051 : Blo 1421530 2135051 := bstep (se 1 (by rfl) ⟨1601288, by rfl⟩ : syracuseStep 2135051 = 3202577) B3202577
theorem B1422359 : Blo 1421530 1422359 := bstep (se 1 (by rfl) ⟨1066769, by rfl⟩ : syracuseStep 1422359 = 2133539) B2133539
theorem B2135063 : Blo 1421530 2135063 := bstep (se 1 (by rfl) ⟨1601297, by rfl⟩ : syracuseStep 2135063 = 3202595) B3202595
theorem B16192547 : Blo 1421530 16192547 := bstep (se 1 (by rfl) ⟨12144410, by rfl⟩ : syracuseStep 16192547 = 24288821) B24288821
theorem B1422379 : Blo 1421530 1422379 := bstep (se 1 (by rfl) ⟨1066784, by rfl⟩ : syracuseStep 1422379 = 2133569) B2133569
theorem B1422391 : Blo 1421530 1422391 := bstep (se 1 (by rfl) ⟨1066793, by rfl⟩ : syracuseStep 1422391 = 2133587) B2133587
theorem B2700353 : Blo 1421530 2700353 := bstep (se 2 (by rfl) ⟨1012632, by rfl⟩ : syracuseStep 2700353 = 2025265) B2025265
theorem B8107073 : Blo 1421530 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B3200075 : Blo 1421530 3200075 := bstep (se 1 (by rfl) ⟨2400056, by rfl⟩ : syracuseStep 3200075 = 4800113) B4800113
theorem B1422411 : Blo 1421530 1422411 := bstep (se 1 (by rfl) ⟨1066808, by rfl⟩ : syracuseStep 1422411 = 2133617) B2133617
theorem B1422423 : Blo 1421530 1422423 := bstep (se 1 (by rfl) ⟨1066817, by rfl⟩ : syracuseStep 1422423 = 2133635) B2133635
theorem B2135129 : Blo 1421530 2135129 := bstep (se 2 (by rfl) ⟨800673, by rfl⟩ : syracuseStep 2135129 = 1601347) B1601347
theorem B1422443 : Blo 1421530 1422443 := bstep (se 1 (by rfl) ⟨1066832, by rfl⟩ : syracuseStep 1422443 = 2133665) B2133665
theorem B1422455 : Blo 1421530 1422455 := bstep (se 1 (by rfl) ⟨1066841, by rfl⟩ : syracuseStep 1422455 = 2133683) B2133683
theorem B3200129 : Blo 1421530 3200129 := bstep (se 2 (by rfl) ⟨1200048, by rfl⟩ : syracuseStep 3200129 = 2400097) B2400097
theorem B1422475 : Blo 1421530 1422475 := bstep (se 1 (by rfl) ⟨1066856, by rfl⟩ : syracuseStep 1422475 = 2133713) B2133713
theorem B1422487 : Blo 1421530 1422487 := bstep (se 1 (by rfl) ⟨1066865, by rfl⟩ : syracuseStep 1422487 = 2133731) B2133731
theorem B1422507 : Blo 1421530 1422507 := bstep (se 1 (by rfl) ⟨1066880, by rfl⟩ : syracuseStep 1422507 = 2133761) B2133761
theorem B1422519 : Blo 1421530 1422519 := bstep (se 1 (by rfl) ⟨1066889, by rfl⟩ : syracuseStep 1422519 = 2133779) B2133779
theorem B1422539 : Blo 1421530 1422539 := bstep (se 1 (by rfl) ⟨1066904, by rfl⟩ : syracuseStep 1422539 = 2133809) B2133809
theorem B2135243 : Blo 1421530 2135243 := bstep (se 1 (by rfl) ⟨1601432, by rfl⟩ : syracuseStep 2135243 = 3202865) B3202865
theorem B1422551 : Blo 1421530 1422551 := bstep (se 1 (by rfl) ⟨1066913, by rfl⟩ : syracuseStep 1422551 = 2133827) B2133827
theorem B2135255 : Blo 1421530 2135255 := bstep (se 1 (by rfl) ⟨1601441, by rfl⟩ : syracuseStep 2135255 = 3202883) B3202883
theorem B1422571 : Blo 1421530 1422571 := bstep (se 1 (by rfl) ⟨1066928, by rfl⟩ : syracuseStep 1422571 = 2133857) B2133857
theorem B1422583 : Blo 1421530 1422583 := bstep (se 1 (by rfl) ⟨1066937, by rfl⟩ : syracuseStep 1422583 = 2133875) B2133875
theorem B1799435 : Blo 1421530 1799435 := bstep (se 1 (by rfl) ⟨1349576, by rfl⟩ : syracuseStep 1799435 = 2699153) B2699153
theorem B1422603 : Blo 1421530 1422603 := bstep (se 1 (by rfl) ⟨1066952, by rfl⟩ : syracuseStep 1422603 = 2133905) B2133905
theorem B1422615 : Blo 1421530 1422615 := bstep (se 1 (by rfl) ⟨1066961, by rfl⟩ : syracuseStep 1422615 = 2133923) B2133923
theorem B1422635 : Blo 1421530 1422635 := bstep (se 1 (by rfl) ⟨1066976, by rfl⟩ : syracuseStep 1422635 = 2133953) B2133953
theorem B5625139 : Blo 1421530 5625139 := bstep (se 1 (by rfl) ⟨4218854, by rfl⟩ : syracuseStep 5625139 = 8437709) B8437709
theorem B5403955 : Blo 1421530 5403955 := bstep (se 1 (by rfl) ⟨4052966, by rfl⟩ : syracuseStep 5403955 = 8105933) B8105933
theorem B1422647 : Blo 1421530 1422647 := bstep (se 1 (by rfl) ⟨1066985, by rfl⟩ : syracuseStep 1422647 = 2133971) B2133971
theorem B1422667 : Blo 1421530 1422667 := bstep (se 1 (by rfl) ⟨1067000, by rfl⟩ : syracuseStep 1422667 = 2134001) B2134001
theorem B1422679 : Blo 1421530 1422679 := bstep (se 1 (by rfl) ⟨1067009, by rfl⟩ : syracuseStep 1422679 = 2134019) B2134019
theorem B3200345 : Blo 1421530 3200345 := bstep (se 2 (by rfl) ⟨1200129, by rfl⟩ : syracuseStep 3200345 = 2400259) B2400259
theorem B1422699 : Blo 1421530 1422699 := bstep (se 1 (by rfl) ⟨1067024, by rfl⟩ : syracuseStep 1422699 = 2134049) B2134049
theorem B1422711 : Blo 1421530 1422711 := bstep (se 1 (by rfl) ⟨1067033, by rfl⟩ : syracuseStep 1422711 = 2134067) B2134067
theorem B12146051 : Blo 1421530 12146051 := bstep (se 1 (by rfl) ⟨9109538, by rfl⟩ : syracuseStep 12146051 = 18219077) B18219077
theorem B1422731 : Blo 1421530 1422731 := bstep (se 1 (by rfl) ⟨1067048, by rfl⟩ : syracuseStep 1422731 = 2134097) B2134097
theorem B2700695 : Blo 1421530 2700695 := bstep (se 1 (by rfl) ⟨2025521, by rfl⟩ : syracuseStep 2700695 = 4051043) B4051043
theorem B1422743 : Blo 1421530 1422743 := bstep (se 1 (by rfl) ⟨1067057, by rfl⟩ : syracuseStep 1422743 = 2134115) B2134115
theorem B1422763 : Blo 1421530 1422763 := bstep (se 1 (by rfl) ⟨1067072, by rfl⟩ : syracuseStep 1422763 = 2134145) B2134145
theorem B3200435 : Blo 1421530 3200435 := bstep (se 1 (by rfl) ⟨2400326, by rfl⟩ : syracuseStep 3200435 = 4800653) B4800653
theorem B1422775 : Blo 1421530 1422775 := bstep (se 1 (by rfl) ⟨1067081, by rfl⟩ : syracuseStep 1422775 = 2134163) B2134163
theorem B4797899 : Blo 1421530 4797899 := bstep (se 1 (by rfl) ⟨3598424, by rfl⟩ : syracuseStep 4797899 = 7196849) B7196849
theorem B1422795 : Blo 1421530 1422795 := bstep (se 1 (by rfl) ⟨1067096, by rfl⟩ : syracuseStep 1422795 = 2134193) B2134193
theorem B3601867 : Blo 1421530 3601867 := bstep (se 1 (by rfl) ⟨2701400, by rfl⟩ : syracuseStep 3601867 = 5402801) B5402801
theorem B3200471 : Blo 1421530 3200471 := bstep (se 1 (by rfl) ⟨2400353, by rfl⟩ : syracuseStep 3200471 = 4800707) B4800707
theorem B1422807 : Blo 1421530 1422807 := bstep (se 1 (by rfl) ⟨1067105, by rfl⟩ : syracuseStep 1422807 = 2134211) B2134211
theorem B1422827 : Blo 1421530 1422827 := bstep (se 1 (by rfl) ⟨1067120, by rfl⟩ : syracuseStep 1422827 = 2134241) B2134241
theorem B1422839 : Blo 1421530 1422839 := bstep (se 1 (by rfl) ⟨1067129, by rfl⟩ : syracuseStep 1422839 = 2134259) B2134259
theorem B1422859 : Blo 1421530 1422859 := bstep (se 1 (by rfl) ⟨1067144, by rfl⟩ : syracuseStep 1422859 = 2134289) B2134289
theorem B1422871 : Blo 1421530 1422871 := bstep (se 1 (by rfl) ⟨1067153, by rfl⟩ : syracuseStep 1422871 = 2134307) B2134307
theorem B1422891 : Blo 1421530 1422891 := bstep (se 1 (by rfl) ⟨1067168, by rfl⟩ : syracuseStep 1422891 = 2134337) B2134337
theorem B1422903 : Blo 1421530 1422903 := bstep (se 1 (by rfl) ⟨1067177, by rfl⟩ : syracuseStep 1422903 = 2134355) B2134355
theorem B11687489 : Blo 1421530 11687489 := bstep (se 2 (by rfl) ⟨4382808, by rfl⟩ : syracuseStep 11687489 = 8765617) B8765617
theorem B1422923 : Blo 1421530 1422923 := bstep (se 1 (by rfl) ⟨1067192, by rfl⟩ : syracuseStep 1422923 = 2134385) B2134385
theorem B1422935 : Blo 1421530 1422935 := bstep (se 1 (by rfl) ⟨1067201, by rfl⟩ : syracuseStep 1422935 = 2134403) B2134403
theorem B3602009 : Blo 1421530 3602009 := bstep (se 2 (by rfl) ⟨1350753, by rfl⟩ : syracuseStep 3602009 = 2701507) B2701507
theorem B1422955 : Blo 1421530 1422955 := bstep (se 1 (by rfl) ⟨1067216, by rfl⟩ : syracuseStep 1422955 = 2134433) B2134433
theorem B1422967 : Blo 1421530 1422967 := bstep (se 1 (by rfl) ⟨1067225, by rfl⟩ : syracuseStep 1422967 = 2134451) B2134451
theorem B3200651 : Blo 1421530 3200651 := bstep (se 1 (by rfl) ⟨2400488, by rfl⟩ : syracuseStep 3200651 = 4800977) B4800977
theorem B1422987 : Blo 1421530 1422987 := bstep (se 1 (by rfl) ⟨1067240, by rfl⟩ : syracuseStep 1422987 = 2134481) B2134481
theorem B1422999 : Blo 1421530 1422999 := bstep (se 1 (by rfl) ⟨1067249, by rfl⟩ : syracuseStep 1422999 = 2134499) B2134499
theorem B1423019 : Blo 1421530 1423019 := bstep (se 1 (by rfl) ⟨1067264, by rfl⟩ : syracuseStep 1423019 = 2134529) B2134529
theorem B1423031 : Blo 1421530 1423031 := bstep (se 1 (by rfl) ⟨1067273, by rfl⟩ : syracuseStep 1423031 = 2134547) B2134547
theorem B3200705 : Blo 1421530 3200705 := bstep (se 2 (by rfl) ⟨1200264, by rfl⟩ : syracuseStep 3200705 = 2400529) B2400529
theorem B1423051 : Blo 1421530 1423051 := bstep (se 1 (by rfl) ⟨1067288, by rfl⟩ : syracuseStep 1423051 = 2134577) B2134577
theorem B1423063 : Blo 1421530 1423063 := bstep (se 1 (by rfl) ⟨1067297, by rfl⟩ : syracuseStep 1423063 = 2134595) B2134595
theorem B4798169 : Blo 1421530 4798169 := bstep (se 2 (by rfl) ⟨1799313, by rfl⟩ : syracuseStep 4798169 = 3598627) B3598627
theorem B3036889 : Blo 1421530 3036889 := bstep (se 2 (by rfl) ⟨1138833, by rfl⟩ : syracuseStep 3036889 = 2277667) B2277667
theorem B1423083 : Blo 1421530 1423083 := bstep (se 1 (by rfl) ⟨1067312, by rfl⟩ : syracuseStep 1423083 = 2134625) B2134625
theorem B1423095 : Blo 1421530 1423095 := bstep (se 1 (by rfl) ⟨1067321, by rfl⟩ : syracuseStep 1423095 = 2134643) B2134643
theorem B1423115 : Blo 1421530 1423115 := bstep (se 1 (by rfl) ⟨1067336, by rfl⟩ : syracuseStep 1423115 = 2134673) B2134673
theorem B1423127 : Blo 1421530 1423127 := bstep (se 1 (by rfl) ⟨1067345, by rfl⟩ : syracuseStep 1423127 = 2134691) B2134691
theorem B1423147 : Blo 1421530 1423147 := bstep (se 1 (by rfl) ⟨1067360, by rfl⟩ : syracuseStep 1423147 = 2134721) B2134721
theorem B6076205 : Blo 1421530 6076205 := bstep (se 3 (by rfl) ⟨1139288, by rfl⟩ : syracuseStep 6076205 = 2278577) B2278577
theorem B2561843 : Blo 1421530 2561843 := bstep (se 1 (by rfl) ⟨1921382, by rfl⟩ : syracuseStep 2561843 = 3842765) B3842765
theorem B1423159 : Blo 1421530 1423159 := bstep (se 1 (by rfl) ⟨1067369, by rfl⟩ : syracuseStep 1423159 = 2134739) B2134739
theorem B1423179 : Blo 1421530 1423179 := bstep (se 1 (by rfl) ⟨1067384, by rfl⟩ : syracuseStep 1423179 = 2134769) B2134769
theorem B1423191 : Blo 1421530 1423191 := bstep (se 1 (by rfl) ⟨1067393, by rfl⟩ : syracuseStep 1423191 = 2134787) B2134787
theorem B1423211 : Blo 1421530 1423211 := bstep (se 1 (by rfl) ⟨1067408, by rfl⟩ : syracuseStep 1423211 = 2134817) B2134817
theorem B1423223 : Blo 1421530 1423223 := bstep (se 1 (by rfl) ⟨1067417, by rfl⟩ : syracuseStep 1423223 = 2134835) B2134835
theorem B1423243 : Blo 1421530 1423243 := bstep (se 1 (by rfl) ⟨1067432, by rfl⟩ : syracuseStep 1423243 = 2134865) B2134865
theorem B1423255 : Blo 1421530 1423255 := bstep (se 1 (by rfl) ⟨1067441, by rfl⟩ : syracuseStep 1423255 = 2134883) B2134883
theorem B3200921 : Blo 1421530 3200921 := bstep (se 2 (by rfl) ⟨1200345, by rfl⟩ : syracuseStep 3200921 = 2400691) B2400691
theorem B1423275 : Blo 1421530 1423275 := bstep (se 1 (by rfl) ⟨1067456, by rfl⟩ : syracuseStep 1423275 = 2134913) B2134913
theorem B17536945 : Blo 1421530 17536945 := bstep (se 2 (by rfl) ⟨6576354, by rfl⟩ : syracuseStep 17536945 = 13152709) B13152709
theorem B8550323 : Blo 1421530 8550323 := bstep (se 1 (by rfl) ⟨6412742, by rfl⟩ : syracuseStep 8550323 = 12825485) B12825485
theorem B12974003 : Blo 1421530 12974003 := bstep (se 1 (by rfl) ⟨9730502, by rfl⟩ : syracuseStep 12974003 = 19461005) B19461005
theorem B1423287 : Blo 1421530 1423287 := bstep (se 1 (by rfl) ⟨1067465, by rfl⟩ : syracuseStep 1423287 = 2134931) B2134931
theorem B1800139 : Blo 1421530 1800139 := bstep (se 1 (by rfl) ⟨1350104, by rfl⟩ : syracuseStep 1800139 = 2700209) B2700209
theorem B1423307 : Blo 1421530 1423307 := bstep (se 1 (by rfl) ⟨1067480, by rfl⟩ : syracuseStep 1423307 = 2134961) B2134961
theorem B1423319 : Blo 1421530 1423319 := bstep (se 1 (by rfl) ⟨1067489, by rfl⟩ : syracuseStep 1423319 = 2134979) B2134979
theorem B1423339 : Blo 1421530 1423339 := bstep (se 1 (by rfl) ⟨1067504, by rfl⟩ : syracuseStep 1423339 = 2135009) B2135009
theorem B3201011 : Blo 1421530 3201011 := bstep (se 1 (by rfl) ⟨2400758, by rfl⟩ : syracuseStep 3201011 = 4801517) B4801517
theorem B1423351 : Blo 1421530 1423351 := bstep (se 1 (by rfl) ⟨1067513, by rfl⟩ : syracuseStep 1423351 = 2135027) B2135027
theorem B1423371 : Blo 1421530 1423371 := bstep (se 1 (by rfl) ⟨1067528, by rfl⟩ : syracuseStep 1423371 = 2135057) B2135057
theorem B3201047 : Blo 1421530 3201047 := bstep (se 1 (by rfl) ⟨2400785, by rfl⟩ : syracuseStep 3201047 = 4801571) B4801571
theorem B1423383 : Blo 1421530 1423383 := bstep (se 1 (by rfl) ⟨1067537, by rfl⟩ : syracuseStep 1423383 = 2135075) B2135075
theorem B1423403 : Blo 1421530 1423403 := bstep (se 1 (by rfl) ⟨1067552, by rfl⟩ : syracuseStep 1423403 = 2135105) B2135105
theorem B4618291 : Blo 1421530 4618291 := bstep (se 1 (by rfl) ⟨3463718, by rfl⟩ : syracuseStep 4618291 = 6927437) B6927437
theorem B2701363 : Blo 1421530 2701363 := bstep (se 1 (by rfl) ⟨2026022, by rfl⟩ : syracuseStep 2701363 = 4052045) B4052045
theorem B1423415 : Blo 1421530 1423415 := bstep (se 1 (by rfl) ⟨1067561, by rfl⟩ : syracuseStep 1423415 = 2135123) B2135123
theorem B1423435 : Blo 1421530 1423435 := bstep (se 1 (by rfl) ⟨1067576, by rfl⟩ : syracuseStep 1423435 = 2135153) B2135153
theorem B1423447 : Blo 1421530 1423447 := bstep (se 1 (by rfl) ⟨1067585, by rfl⟩ : syracuseStep 1423447 = 2135171) B2135171
theorem B10803293 : Blo 1421530 10803293 := bstep (se 3 (by rfl) ⟨2025617, by rfl⟩ : syracuseStep 10803293 = 4051235) B4051235
theorem B8321125 : Blo 1421530 8321125 := bstep (se 4 (by rfl) ⟨780105, by rfl⟩ : syracuseStep 8321125 = 1560211) B1560211
theorem B1423467 : Blo 1421530 1423467 := bstep (se 1 (by rfl) ⟨1067600, by rfl⟩ : syracuseStep 1423467 = 2135201) B2135201
theorem B1423479 : Blo 1421530 1423479 := bstep (se 1 (by rfl) ⟨1067609, by rfl⟩ : syracuseStep 1423479 = 2135219) B2135219
theorem B3078283 : Blo 1421530 3078283 := bstep (se 1 (by rfl) ⟨2308712, by rfl⟩ : syracuseStep 3078283 = 4617425) B4617425
theorem B1423499 : Blo 1421530 1423499 := bstep (se 1 (by rfl) ⟨1067624, by rfl⟩ : syracuseStep 1423499 = 2135249) B2135249
theorem B1423511 : Blo 1421530 1423511 := bstep (se 1 (by rfl) ⟨1067633, by rfl⟩ : syracuseStep 1423511 = 2135267) B2135267
theorem B3201227 : Blo 1421530 3201227 := bstep (se 1 (by rfl) ⟨2400920, by rfl⟩ : syracuseStep 3201227 = 4801841) B4801841
theorem B1800407 : Blo 1421530 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B3201281 : Blo 1421530 3201281 := bstep (se 2 (by rfl) ⟨1200480, by rfl⟩ : syracuseStep 3201281 = 2400961) B2400961
theorem B4798871 : Blo 1421530 4798871 := bstep (se 1 (by rfl) ⟨3599153, by rfl⟩ : syracuseStep 4798871 = 7198307) B7198307
theorem B3602839 : Blo 1421530 3602839 := bstep (se 1 (by rfl) ⟨2702129, by rfl⟩ : syracuseStep 3602839 = 5404259) B5404259
theorem B15374771 : Blo 1421530 15374771 := bstep (se 1 (by rfl) ⟨11531078, by rfl⟩ : syracuseStep 15374771 = 23062157) B23062157
theorem B6076889 : Blo 1421530 6076889 := bstep (se 2 (by rfl) ⟨2278833, by rfl⟩ : syracuseStep 6076889 = 4557667) B4557667
theorem B3201497 : Blo 1421530 3201497 := bstep (se 2 (by rfl) ⟨1200561, by rfl⟩ : syracuseStep 3201497 = 2401123) B2401123
theorem B2701811 : Blo 1421530 2701811 := bstep (se 1 (by rfl) ⟨2026358, by rfl⟩ : syracuseStep 2701811 = 4052717) B4052717
theorem B2701849 : Blo 1421530 2701849 := bstep (se 2 (by rfl) ⟨1013193, by rfl⟩ : syracuseStep 2701849 = 2026387) B2026387
theorem B3201587 : Blo 1421530 3201587 := bstep (se 1 (by rfl) ⟨2401190, by rfl⟩ : syracuseStep 3201587 = 4802381) B4802381
theorem B3201623 : Blo 1421530 3201623 := bstep (se 1 (by rfl) ⟨2401217, by rfl⟩ : syracuseStep 3201623 = 4802435) B4802435
theorem B4052375 : Blo 1421530 4052375 := bstep (se 1 (by rfl) ⟨3039281, by rfl⟩ : syracuseStep 4052375 = 6078563) B6078563
theorem B2882251 : Blo 1421530 2882251 := bstep (se 1 (by rfl) ⟨2161688, by rfl⟩ : syracuseStep 2882251 = 4323377) B4323377
theorem B3242699 : Blo 1421530 3242699 := bstep (se 1 (by rfl) ⟨2432024, by rfl⟩ : syracuseStep 3242699 = 4864049) B4864049
theorem B3201803 : Blo 1421530 3201803 := bstep (se 1 (by rfl) ⟨2401352, by rfl⟩ : syracuseStep 3201803 = 4802705) B4802705
theorem B77839157 : Blo 1421530 77839157 := bstep (se 5 (by rfl) ⟨3648710, by rfl⟩ : syracuseStep 77839157 = 7297421) B7297421
theorem B3201857 : Blo 1421530 3201857 := bstep (se 2 (by rfl) ⟨1200696, by rfl⟩ : syracuseStep 3201857 = 2401393) B2401393
theorem B2399051 : Blo 1421530 2399051 := bstep (se 1 (by rfl) ⟨1799288, by rfl⟩ : syracuseStep 2399051 = 3598577) B3598577
theorem B3603275 : Blo 1421530 3603275 := bstep (se 1 (by rfl) ⟨2702456, by rfl⟩ : syracuseStep 3603275 = 5404913) B5404913
theorem B1801111 : Blo 1421530 1801111 := bstep (se 1 (by rfl) ⟨1350833, by rfl⟩ : syracuseStep 1801111 = 2701667) B2701667
theorem B4799411 : Blo 1421530 4799411 := bstep (se 1 (by rfl) ⟨3599558, by rfl⟩ : syracuseStep 4799411 = 7199117) B7199117
theorem B2399179 : Blo 1421530 2399179 := bstep (se 1 (by rfl) ⟨1799384, by rfl⟩ : syracuseStep 2399179 = 3598769) B3598769
theorem B2702297 : Blo 1421530 2702297 := bstep (se 2 (by rfl) ⟨1013361, by rfl⟩ : syracuseStep 2702297 = 2026723) B2026723
theorem B3202073 : Blo 1421530 3202073 := bstep (se 2 (by rfl) ⟨1200777, by rfl⟩ : syracuseStep 3202073 = 2401555) B2401555
theorem B2563147 : Blo 1421530 2563147 := bstep (se 1 (by rfl) ⟨1922360, by rfl⟩ : syracuseStep 2563147 = 3844721) B3844721
theorem B2399321 : Blo 1421530 2399321 := bstep (se 2 (by rfl) ⟨899745, by rfl⟩ : syracuseStep 2399321 = 1799491) B1799491
theorem B3202163 : Blo 1421530 3202163 := bstep (se 1 (by rfl) ⟨2401622, by rfl⟩ : syracuseStep 3202163 = 4803245) B4803245
theorem B3202199 : Blo 1421530 3202199 := bstep (se 1 (by rfl) ⟨2401649, by rfl⟩ : syracuseStep 3202199 = 4803299) B4803299
theorem B4799681 : Blo 1421530 4799681 := bstep (se 2 (by rfl) ⟨1799880, by rfl⟩ : syracuseStep 4799681 = 3599761) B3599761
theorem B2399449 : Blo 1421530 2399449 := bstep (se 2 (by rfl) ⟨899793, by rfl⟩ : syracuseStep 2399449 = 1799587) B1799587
theorem B8215769 : Blo 1421530 8215769 := bstep (se 2 (by rfl) ⟨3080913, by rfl⟩ : syracuseStep 8215769 = 6161827) B6161827
theorem B7691537 : Blo 1421530 7691537 := bstep (se 2 (by rfl) ⟨2884326, by rfl⟩ : syracuseStep 7691537 = 5768653) B5768653
theorem B3202379 : Blo 1421530 3202379 := bstep (se 1 (by rfl) ⟨2401784, by rfl⟩ : syracuseStep 3202379 = 4803569) B4803569
theorem B3202433 : Blo 1421530 3202433 := bstep (se 2 (by rfl) ⟨1200912, by rfl⟩ : syracuseStep 3202433 = 2401825) B2401825
theorem B5397911 : Blo 1421530 5397911 := bstep (se 1 (by rfl) ⟨4048433, by rfl⟩ : syracuseStep 5397911 = 8096867) B8096867
theorem B43793891 : Blo 1421530 43793891 := bstep (se 1 (by rfl) ⟨32845418, by rfl⟩ : syracuseStep 43793891 = 65690837) B65690837
theorem B5766707 : Blo 1421530 5766707 := bstep (se 1 (by rfl) ⟨4325030, by rfl⟩ : syracuseStep 5766707 = 8650061) B8650061
theorem B3202649 : Blo 1421530 3202649 := bstep (se 2 (by rfl) ⟨1200993, by rfl⟩ : syracuseStep 3202649 = 2401987) B2401987
theorem B5398109 : Blo 1421530 5398109 := bstep (se 3 (by rfl) ⟨1012145, by rfl⟩ : syracuseStep 5398109 = 2024291) B2024291
theorem B3202739 : Blo 1421530 3202739 := bstep (se 1 (by rfl) ⟨2402054, by rfl⟩ : syracuseStep 3202739 = 4804109) B4804109
theorem B3202775 : Blo 1421530 3202775 := bstep (se 1 (by rfl) ⟨2402081, by rfl⟩ : syracuseStep 3202775 = 4804163) B4804163
theorem B4800221 : Blo 1421530 4800221 := bstep (se 3 (by rfl) ⟨900041, by rfl⟩ : syracuseStep 4800221 = 1800083) B1800083
theorem B2400023 : Blo 1421530 2400023 := bstep (se 1 (by rfl) ⟨1800017, by rfl⟩ : syracuseStep 2400023 = 3600035) B3600035
theorem B92348261 : Blo 1421530 92348261 := bstep (se 4 (by rfl) ⟨8657649, by rfl⟩ : syracuseStep 92348261 = 17315299) B17315299
theorem B2400151 : Blo 1421530 2400151 := bstep (se 1 (by rfl) ⟨1800113, by rfl⟩ : syracuseStep 2400151 = 3600227) B3600227
theorem B7692317 : Blo 1421530 7692317 := bstep (se 3 (by rfl) ⟨1442309, by rfl⟩ : syracuseStep 7692317 = 2884619) B2884619
theorem B6078493 : Blo 1421530 6078493 := bstep (se 3 (by rfl) ⟨1139717, by rfl⟩ : syracuseStep 6078493 = 2279435) B2279435
theorem B5398595 : Blo 1421530 5398595 := bstep (se 1 (by rfl) ⟨4048946, by rfl⟩ : syracuseStep 5398595 = 8097893) B8097893
theorem B4800599 : Blo 1421530 4800599 := bstep (se 1 (by rfl) ⟨3600449, by rfl⟩ : syracuseStep 4800599 = 7200899) B7200899
theorem B4104377 : Blo 1421530 4104377 := bstep (se 2 (by rfl) ⟨1539141, by rfl⟩ : syracuseStep 4104377 = 3078283) B3078283
theorem B6078665 : Blo 1421530 6078665 := bstep (se 2 (by rfl) ⟨2279499, by rfl⟩ : syracuseStep 6078665 = 4558999) B4558999
theorem B1442107 : Blo 1421530 1442107 := bstep (se 1 (by rfl) ⟨1081580, by rfl⟩ : syracuseStep 1442107 = 2163161) B2163161
theorem B12976519 : Blo 1421530 12976519 := bstep (se 1 (by rfl) ⟨9732389, by rfl⟩ : syracuseStep 12976519 = 19464779) B19464779
theorem B3039623 : Blo 1421530 3039623 := bstep (se 1 (by rfl) ⟨2279717, by rfl⟩ : syracuseStep 3039623 = 4559435) B4559435
theorem B65724817 : Blo 1421530 65724817 := bstep (se 2 (by rfl) ⟨24646806, by rfl⟩ : syracuseStep 65724817 = 49293613) B49293613
theorem B13664771 : Blo 1421530 13664771 := bstep (se 1 (by rfl) ⟨10248578, by rfl⟩ : syracuseStep 13664771 = 20497157) B20497157
theorem B4801085 : Blo 1421530 4801085 := bstep (se 3 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 4801085 = 1800407) B1800407
theorem B2400887 : Blo 1421530 2400887 := bstep (se 1 (by rfl) ⟨1800665, by rfl⟩ : syracuseStep 2400887 = 3601331) B3601331
theorem B2163343 : Blo 1421530 2163343 := bstep (se 1 (by rfl) ⟨1622507, by rfl⟩ : syracuseStep 2163343 = 3245015) B3245015
theorem B2024137 : Blo 1421530 2024137 := bstep (se 2 (by rfl) ⟨759051, by rfl⟩ : syracuseStep 2024137 = 1518103) B1518103
theorem B3040033 : Blo 1421530 3040033 := bstep (se 2 (by rfl) ⟨1140012, by rfl⟩ : syracuseStep 3040033 = 2280025) B2280025
theorem B11698993 : Blo 1421530 11698993 := bstep (se 2 (by rfl) ⟨4387122, by rfl⟩ : syracuseStep 11698993 = 8774245) B8774245
theorem B23069555 : Blo 1421530 23069555 := bstep (se 1 (by rfl) ⟨17302166, by rfl⟩ : syracuseStep 23069555 = 34604333) B34604333
theorem B3843001 : Blo 1421530 3843001 := bstep (se 2 (by rfl) ⟨1441125, by rfl⟩ : syracuseStep 3843001 = 2882251) B2882251
theorem B136872917 : Blo 1421530 136872917 := bstep (se 7 (by rfl) ⟨1603979, by rfl⟩ : syracuseStep 136872917 = 3207959) B3207959
theorem B5399581 : Blo 1421530 5399581 := bstep (se 3 (by rfl) ⟨1012421, by rfl⟩ : syracuseStep 5399581 = 2024843) B2024843
theorem B7791659 : Blo 1421530 7791659 := bstep (se 1 (by rfl) ⟨5843744, by rfl⟩ : syracuseStep 7791659 = 11687489) B11687489
theorem B2401339 : Blo 1421530 2401339 := bstep (se 1 (by rfl) ⟨1801004, by rfl⟩ : syracuseStep 2401339 = 3602009) B3602009
theorem B8651863 : Blo 1421530 8651863 := bstep (se 1 (by rfl) ⟨6488897, by rfl⟩ : syracuseStep 8651863 = 12977795) B12977795
theorem B5129335 : Blo 1421530 5129335 := bstep (se 1 (by rfl) ⟨3847001, by rfl⟩ : syracuseStep 5129335 = 7694003) B7694003
theorem B2401481 : Blo 1421530 2401481 := bstep (se 2 (by rfl) ⟨900555, by rfl⟩ : syracuseStep 2401481 = 1801111) B1801111
theorem B8652179 : Blo 1421530 8652179 := bstep (se 1 (by rfl) ⟨6489134, by rfl⟩ : syracuseStep 8652179 = 12978269) B12978269
theorem B7202195 : Blo 1421530 7202195 := bstep (se 1 (by rfl) ⟨5401646, by rfl⟩ : syracuseStep 7202195 = 10803293) B10803293
theorem B10249847 : Blo 1421530 10249847 := bstep (se 1 (by rfl) ⟨7687385, by rfl⟩ : syracuseStep 10249847 = 15374771) B15374771
theorem B5473993 : Blo 1421530 5473993 := bstep (se 2 (by rfl) ⟨2052747, by rfl⟩ : syracuseStep 5473993 = 4105495) B4105495
theorem B5129999 : Blo 1421530 5129999 := bstep (se 1 (by rfl) ⟨3847499, by rfl⟩ : syracuseStep 5129999 = 7694999) B7694999
theorem B1599367 : Blo 1421530 1599367 := bstep (se 1 (by rfl) ⟨1199525, by rfl⟩ : syracuseStep 1599367 = 2399051) B2399051
theorem B4048775 : Blo 1421530 4048775 := bstep (se 1 (by rfl) ⟨3036581, by rfl⟩ : syracuseStep 4048775 = 6073163) B6073163
theorem B2402183 : Blo 1421530 2402183 := bstep (se 1 (by rfl) ⟨1801637, by rfl⟩ : syracuseStep 2402183 = 3603275) B3603275
theorem B4802489 : Blo 1421530 4802489 := bstep (se 2 (by rfl) ⟨1800933, by rfl⟩ : syracuseStep 4802489 = 3601867) B3601867
theorem B1599547 : Blo 1421530 1599547 := bstep (se 1 (by rfl) ⟨1199660, by rfl⟩ : syracuseStep 1599547 = 2399321) B2399321
theorem B4048957 : Blo 1421530 4048957 := bstep (se 3 (by rfl) ⟨759179, by rfl⟩ : syracuseStep 4048957 = 1518359) B1518359
theorem B6080579 : Blo 1421530 6080579 := bstep (se 1 (by rfl) ⟨4560434, by rfl⟩ : syracuseStep 6080579 = 9120869) B9120869
theorem B3598607 : Blo 1421530 3598607 := bstep (se 1 (by rfl) ⟨2698955, by rfl⟩ : syracuseStep 3598607 = 5397911) B5397911
theorem B4049185 : Blo 1421530 4049185 := bstep (se 2 (by rfl) ⟨1518444, by rfl⟩ : syracuseStep 4049185 = 3036889) B3036889
theorem B2132297 : Blo 1421530 2132297 := bstep (se 2 (by rfl) ⟨799611, by rfl⟩ : syracuseStep 2132297 = 1599223) B1599223
theorem B3844471 : Blo 1421530 3844471 := bstep (se 1 (by rfl) ⟨2883353, by rfl⟩ : syracuseStep 3844471 = 5766707) B5766707
theorem B3598739 : Blo 1421530 3598739 := bstep (se 1 (by rfl) ⟨2699054, by rfl⟩ : syracuseStep 3598739 = 5398109) B5398109
theorem B16214417 : Blo 1421530 16214417 := bstep (se 2 (by rfl) ⟨6080406, by rfl⟩ : syracuseStep 16214417 = 12160813) B12160813
theorem B2132411 : Blo 1421530 2132411 := bstep (se 1 (by rfl) ⟨1599308, by rfl⟩ : syracuseStep 2132411 = 3198617) B3198617
theorem B13666769 : Blo 1421530 13666769 := bstep (se 2 (by rfl) ⟨5125038, by rfl⟩ : syracuseStep 13666769 = 10250077) B10250077
theorem B2132471 : Blo 1421530 2132471 := bstep (se 1 (by rfl) ⟨1599353, by rfl⟩ : syracuseStep 2132471 = 3198707) B3198707
theorem B4803083 : Blo 1421530 4803083 := bstep (se 1 (by rfl) ⟨3602312, by rfl⟩ : syracuseStep 4803083 = 7204625) B7204625
theorem B2132495 : Blo 1421530 2132495 := bstep (se 1 (by rfl) ⟨1599371, by rfl⟩ : syracuseStep 2132495 = 3198743) B3198743
theorem B1600015 : Blo 1421530 1600015 := bstep (se 1 (by rfl) ⟨1200011, by rfl⟩ : syracuseStep 1600015 = 2400023) B2400023
theorem B4327951 : Blo 1421530 4327951 := bstep (se 1 (by rfl) ⟨3245963, by rfl⟩ : syracuseStep 4327951 = 6491927) B6491927
theorem B19466795 : Blo 1421530 19466795 := bstep (se 1 (by rfl) ⟨14600096, by rfl⟩ : syracuseStep 19466795 = 29200193) B29200193
theorem B2132537 : Blo 1421530 2132537 := bstep (se 2 (by rfl) ⟨799701, by rfl⟩ : syracuseStep 2132537 = 1599403) B1599403
theorem B23382593 : Blo 1421530 23382593 := bstep (se 2 (by rfl) ⟨8768472, by rfl⟩ : syracuseStep 23382593 = 17536945) B17536945
theorem B61565507 : Blo 1421530 61565507 := bstep (se 1 (by rfl) ⟨46174130, by rfl⟩ : syracuseStep 61565507 = 92348261) B92348261
theorem B4049527 : Blo 1421530 4049527 := bstep (se 1 (by rfl) ⟨3037145, by rfl⟩ : syracuseStep 4049527 = 6074291) B6074291
theorem B4803191 : Blo 1421530 4803191 := bstep (se 1 (by rfl) ⟨3602393, by rfl⟩ : syracuseStep 4803191 = 7204787) B7204787
theorem B2132615 : Blo 1421530 2132615 := bstep (se 1 (by rfl) ⟨1599461, by rfl⟩ : syracuseStep 2132615 = 3198923) B3198923
theorem B2132651 : Blo 1421530 2132651 := bstep (se 1 (by rfl) ⟨1599488, by rfl⟩ : syracuseStep 2132651 = 3198977) B3198977
theorem B2132681 : Blo 1421530 2132681 := bstep (se 2 (by rfl) ⟨799755, by rfl⟩ : syracuseStep 2132681 = 1599511) B1599511
theorem B11094833 : Blo 1421530 11094833 := bstep (se 2 (by rfl) ⟨4160562, by rfl⟩ : syracuseStep 11094833 = 8321125) B8321125
theorem B2132795 : Blo 1421530 2132795 := bstep (se 1 (by rfl) ⟨1599596, by rfl⟩ : syracuseStep 2132795 = 3199193) B3199193
theorem B9112409 : Blo 1421530 9112409 := bstep (se 2 (by rfl) ⟨3417153, by rfl⟩ : syracuseStep 9112409 = 6834307) B6834307
theorem B10808153 : Blo 1421530 10808153 := bstep (se 2 (by rfl) ⟨4053057, by rfl⟩ : syracuseStep 10808153 = 8106115) B8106115
theorem B2132855 : Blo 1421530 2132855 := bstep (se 1 (by rfl) ⟨1599641, by rfl⟩ : syracuseStep 2132855 = 3199283) B3199283
theorem B2132879 : Blo 1421530 2132879 := bstep (se 1 (by rfl) ⟨1599659, by rfl⟩ : syracuseStep 2132879 = 3199319) B3199319
theorem B2132921 : Blo 1421530 2132921 := bstep (se 2 (by rfl) ⟨799845, by rfl⟩ : syracuseStep 2132921 = 1599691) B1599691
theorem B2132999 : Blo 1421530 2132999 := bstep (se 1 (by rfl) ⟨1599749, by rfl⟩ : syracuseStep 2132999 = 3199499) B3199499
theorem B1600519 : Blo 1421530 1600519 := bstep (se 1 (by rfl) ⟨1200389, by rfl⟩ : syracuseStep 1600519 = 2400779) B2400779
theorem B2133035 : Blo 1421530 2133035 := bstep (se 1 (by rfl) ⟨1599776, by rfl⟩ : syracuseStep 2133035 = 3199553) B3199553
theorem B2133065 : Blo 1421530 2133065 := bstep (se 2 (by rfl) ⟨799899, by rfl⟩ : syracuseStep 2133065 = 1599799) B1599799
theorem B2026615 : Blo 1421530 2026615 := bstep (se 1 (by rfl) ⟨1519961, by rfl⟩ : syracuseStep 2026615 = 3039923) B3039923
theorem B2133179 : Blo 1421530 2133179 := bstep (se 1 (by rfl) ⟨1599884, by rfl⟩ : syracuseStep 2133179 = 3199769) B3199769
theorem B1600699 : Blo 1421530 1600699 := bstep (se 1 (by rfl) ⟨1200524, by rfl⟩ : syracuseStep 1600699 = 2401049) B2401049
theorem B4803785 : Blo 1421530 4803785 := bstep (se 2 (by rfl) ⟨1801419, by rfl⟩ : syracuseStep 4803785 = 3602839) B3602839
theorem B2133239 : Blo 1421530 2133239 := bstep (se 1 (by rfl) ⟨1599929, by rfl⟩ : syracuseStep 2133239 = 3199859) B3199859
theorem B2133263 : Blo 1421530 2133263 := bstep (se 1 (by rfl) ⟨1599947, by rfl⟩ : syracuseStep 2133263 = 3199895) B3199895
theorem B2133305 : Blo 1421530 2133305 := bstep (se 2 (by rfl) ⟨799989, by rfl⟩ : syracuseStep 2133305 = 1599979) B1599979
theorem B2133383 : Blo 1421530 2133383 := bstep (se 1 (by rfl) ⟨1600037, by rfl⟩ : syracuseStep 2133383 = 3200075) B3200075
theorem B2133419 : Blo 1421530 2133419 := bstep (se 1 (by rfl) ⟨1600064, by rfl⟩ : syracuseStep 2133419 = 3200129) B3200129
theorem B2698697 : Blo 1421530 2698697 := bstep (se 2 (by rfl) ⟨1012011, by rfl⟩ : syracuseStep 2698697 = 2024023) B2024023
theorem B2133449 : Blo 1421530 2133449 := bstep (se 2 (by rfl) ⟨800043, by rfl⟩ : syracuseStep 2133449 = 1600087) B1600087
theorem B3599873 : Blo 1421530 3599873 := bstep (se 2 (by rfl) ⟨1349952, by rfl⟩ : syracuseStep 3599873 = 2699905) B2699905
theorem B1519111 : Blo 1421530 1519111 := bstep (se 1 (by rfl) ⟨1139333, by rfl⟩ : syracuseStep 1519111 = 2278667) B2278667
theorem B4050461 : Blo 1421530 4050461 := bstep (se 3 (by rfl) ⟨759461, by rfl⟩ : syracuseStep 4050461 = 1518923) B1518923
theorem B2133563 : Blo 1421530 2133563 := bstep (se 1 (by rfl) ⟨1600172, by rfl⟩ : syracuseStep 2133563 = 3200345) B3200345
theorem B8097367 : Blo 1421530 8097367 := bstep (se 1 (by rfl) ⟨6073025, by rfl⟩ : syracuseStep 8097367 = 12146051) B12146051
theorem B2133623 : Blo 1421530 2133623 := bstep (se 1 (by rfl) ⟨1600217, by rfl⟩ : syracuseStep 2133623 = 3200435) B3200435
theorem B3198599 : Blo 1421530 3198599 := bstep (se 1 (by rfl) ⟨2398949, by rfl⟩ : syracuseStep 3198599 = 4797899) B4797899
theorem B2133647 : Blo 1421530 2133647 := bstep (se 1 (by rfl) ⟨1600235, by rfl⟩ : syracuseStep 2133647 = 3200471) B3200471
theorem B1601167 : Blo 1421530 1601167 := bstep (se 1 (by rfl) ⟨1200875, by rfl⟩ : syracuseStep 1601167 = 2401751) B2401751
theorem B2191033 : Blo 1421530 2191033 := bstep (se 2 (by rfl) ⟨821637, by rfl⟩ : syracuseStep 2191033 = 1643275) B1643275
theorem B2133689 : Blo 1421530 2133689 := bstep (se 2 (by rfl) ⟨800133, by rfl⟩ : syracuseStep 2133689 = 1600267) B1600267
theorem B2133767 : Blo 1421530 2133767 := bstep (se 1 (by rfl) ⟨1600325, by rfl⟩ : syracuseStep 2133767 = 3200651) B3200651
theorem B13676303 : Blo 1421530 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B10809125 : Blo 1421530 10809125 := bstep (se 4 (by rfl) ⟨1013355, by rfl⟩ : syracuseStep 10809125 = 2026711) B2026711
theorem B2133803 : Blo 1421530 2133803 := bstep (se 1 (by rfl) ⟨1600352, by rfl⟩ : syracuseStep 2133803 = 3200705) B3200705
theorem B3198779 : Blo 1421530 3198779 := bstep (se 1 (by rfl) ⟨2399084, by rfl⟩ : syracuseStep 3198779 = 4798169) B4798169
theorem B2133833 : Blo 1421530 2133833 := bstep (se 2 (by rfl) ⟨800187, by rfl⟩ : syracuseStep 2133833 = 1600375) B1600375
theorem B24293195 : Blo 1421530 24293195 := bstep (se 1 (by rfl) ⟨18219896, by rfl⟩ : syracuseStep 24293195 = 36439793) B36439793
theorem B4050803 : Blo 1421530 4050803 := bstep (se 1 (by rfl) ⟨3038102, by rfl⟩ : syracuseStep 4050803 = 6076205) B6076205
theorem B5402483 : Blo 1421530 5402483 := bstep (se 1 (by rfl) ⟨4051862, by rfl⟩ : syracuseStep 5402483 = 8103725) B8103725
theorem B1707895 : Blo 1421530 1707895 := bstep (se 1 (by rfl) ⟨1280921, by rfl⟩ : syracuseStep 1707895 = 2561843) B2561843
theorem B3600247 : Blo 1421530 3600247 := bstep (se 1 (by rfl) ⟨2700185, by rfl⟩ : syracuseStep 3600247 = 5400371) B5400371
theorem B3198905 : Blo 1421530 3198905 := bstep (se 2 (by rfl) ⟨1199589, by rfl⟩ : syracuseStep 3198905 = 2399179) B2399179
theorem B2133947 : Blo 1421530 2133947 := bstep (se 1 (by rfl) ⟨1600460, by rfl⟩ : syracuseStep 2133947 = 3200921) B3200921
theorem B2134007 : Blo 1421530 2134007 := bstep (se 1 (by rfl) ⟨1600505, by rfl⟩ : syracuseStep 2134007 = 3201011) B3201011
theorem B2134031 : Blo 1421530 2134031 := bstep (se 1 (by rfl) ⟨1600523, by rfl⟩ : syracuseStep 2134031 = 3201047) B3201047
theorem B2134073 : Blo 1421530 2134073 := bstep (se 2 (by rfl) ⟨800277, by rfl⟩ : syracuseStep 2134073 = 1600555) B1600555
theorem B2134151 : Blo 1421530 2134151 := bstep (se 1 (by rfl) ⟨1600613, by rfl⟩ : syracuseStep 2134151 = 3201227) B3201227
theorem B2134187 : Blo 1421530 2134187 := bstep (se 1 (by rfl) ⟨1600640, by rfl⟩ : syracuseStep 2134187 = 3201281) B3201281
theorem B10956973 : Blo 1421530 10956973 := bstep (se 3 (by rfl) ⟨2054432, by rfl⟩ : syracuseStep 10956973 = 4108865) B4108865
theorem B1732795 : Blo 1421530 1732795 := bstep (se 1 (by rfl) ⟨1299596, by rfl⟩ : syracuseStep 1732795 = 2599193) B2599193
theorem B2134217 : Blo 1421530 2134217 := bstep (se 2 (by rfl) ⟨800331, by rfl⟩ : syracuseStep 2134217 = 1600663) B1600663
theorem B1421575 : Blo 1421530 1421575 := bstep (se 1 (by rfl) ⟨1066181, by rfl⟩ : syracuseStep 1421575 = 2132363) B2132363
theorem B1421583 : Blo 1421530 1421583 := bstep (se 1 (by rfl) ⟨1066187, by rfl⟩ : syracuseStep 1421583 = 2132375) B2132375
theorem B3199247 : Blo 1421530 3199247 := bstep (se 1 (by rfl) ⟨2399435, by rfl⟩ : syracuseStep 3199247 = 4798871) B4798871
theorem B3199265 : Blo 1421530 3199265 := bstep (se 2 (by rfl) ⟨1199724, by rfl⟩ : syracuseStep 3199265 = 2399449) B2399449
theorem B2699563 : Blo 1421530 2699563 := bstep (se 1 (by rfl) ⟨2024672, by rfl⟩ : syracuseStep 2699563 = 4049345) B4049345
theorem B3600683 : Blo 1421530 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B1421627 : Blo 1421530 1421627 := bstep (se 1 (by rfl) ⟨1066220, by rfl⟩ : syracuseStep 1421627 = 2132441) B2132441
theorem B4051259 : Blo 1421530 4051259 := bstep (se 1 (by rfl) ⟨3038444, by rfl⟩ : syracuseStep 4051259 = 6076889) B6076889
theorem B2134331 : Blo 1421530 2134331 := bstep (se 1 (by rfl) ⟨1600748, by rfl⟩ : syracuseStep 2134331 = 3201497) B3201497
theorem B1519931 : Blo 1421530 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B2699639 : Blo 1421530 2699639 := bstep (se 1 (by rfl) ⟨2024729, by rfl⟩ : syracuseStep 2699639 = 4049459) B4049459
theorem B2134391 : Blo 1421530 2134391 := bstep (se 1 (by rfl) ⟨1600793, by rfl⟩ : syracuseStep 2134391 = 3201587) B3201587
theorem B1421703 : Blo 1421530 1421703 := bstep (se 1 (by rfl) ⟨1066277, by rfl⟩ : syracuseStep 1421703 = 2132555) B2132555
theorem B1421711 : Blo 1421530 1421711 := bstep (se 1 (by rfl) ⟨1066283, by rfl⟩ : syracuseStep 1421711 = 2132567) B2132567
theorem B2134415 : Blo 1421530 2134415 := bstep (se 1 (by rfl) ⟨1600811, by rfl⟩ : syracuseStep 2134415 = 3201623) B3201623
theorem B7500185 : Blo 1421530 7500185 := bstep (se 2 (by rfl) ⟨2812569, by rfl⟩ : syracuseStep 7500185 = 5625139) B5625139
theorem B7205273 : Blo 1421530 7205273 := bstep (se 2 (by rfl) ⟨2701977, by rfl⟩ : syracuseStep 7205273 = 5403955) B5403955
theorem B2134457 : Blo 1421530 2134457 := bstep (se 2 (by rfl) ⟨800421, by rfl⟩ : syracuseStep 2134457 = 1600843) B1600843
theorem B1421755 : Blo 1421530 1421755 := bstep (se 1 (by rfl) ⟨1066316, by rfl⟩ : syracuseStep 1421755 = 2132633) B2132633
theorem B1421831 : Blo 1421530 1421831 := bstep (se 1 (by rfl) ⟨1066373, by rfl⟩ : syracuseStep 1421831 = 2132747) B2132747
theorem B2134535 : Blo 1421530 2134535 := bstep (se 1 (by rfl) ⟨1600901, by rfl⟩ : syracuseStep 2134535 = 3201803) B3201803
theorem B1421839 : Blo 1421530 1421839 := bstep (se 1 (by rfl) ⟨1066379, by rfl⟩ : syracuseStep 1421839 = 2132759) B2132759
theorem B51892771 : Blo 1421530 51892771 := bstep (se 1 (by rfl) ⟨38919578, by rfl⟩ : syracuseStep 51892771 = 77839157) B77839157
theorem B2134571 : Blo 1421530 2134571 := bstep (se 1 (by rfl) ⟨1600928, by rfl⟩ : syracuseStep 2134571 = 3201857) B3201857
theorem B1421883 : Blo 1421530 1421883 := bstep (se 1 (by rfl) ⟨1066412, by rfl⟩ : syracuseStep 1421883 = 2132825) B2132825
theorem B2134601 : Blo 1421530 2134601 := bstep (se 2 (by rfl) ⟨800475, by rfl⟩ : syracuseStep 2134601 = 1600951) B1600951
theorem B3199607 : Blo 1421530 3199607 := bstep (se 1 (by rfl) ⟨2399705, by rfl⟩ : syracuseStep 3199607 = 4799411) B4799411
theorem B1421959 : Blo 1421530 1421959 := bstep (se 1 (by rfl) ⟨1066469, by rfl⟩ : syracuseStep 1421959 = 2132939) B2132939
theorem B1421967 : Blo 1421530 1421967 := bstep (se 1 (by rfl) ⟨1066475, by rfl⟩ : syracuseStep 1421967 = 2132951) B2132951
theorem B1422011 : Blo 1421530 1422011 := bstep (se 1 (by rfl) ⟨1066508, by rfl⟩ : syracuseStep 1422011 = 2133017) B2133017
theorem B2134715 : Blo 1421530 2134715 := bstep (se 1 (by rfl) ⟨1601036, by rfl⟩ : syracuseStep 2134715 = 3202073) B3202073
theorem B2134775 : Blo 1421530 2134775 := bstep (se 1 (by rfl) ⟨1601081, by rfl⟩ : syracuseStep 2134775 = 3202163) B3202163
theorem B1422087 : Blo 1421530 1422087 := bstep (se 1 (by rfl) ⟨1066565, by rfl⟩ : syracuseStep 1422087 = 2133131) B2133131
theorem B1422095 : Blo 1421530 1422095 := bstep (se 1 (by rfl) ⟨1066571, by rfl⟩ : syracuseStep 1422095 = 2133143) B2133143
theorem B2134799 : Blo 1421530 2134799 := bstep (se 1 (by rfl) ⟨1601099, by rfl⟩ : syracuseStep 2134799 = 3202199) B3202199
theorem B3199787 : Blo 1421530 3199787 := bstep (se 1 (by rfl) ⟨2399840, by rfl⟩ : syracuseStep 3199787 = 4799681) B4799681
theorem B2134841 : Blo 1421530 2134841 := bstep (se 2 (by rfl) ⟨800565, by rfl⟩ : syracuseStep 2134841 = 1601131) B1601131
theorem B1422139 : Blo 1421530 1422139 := bstep (se 1 (by rfl) ⟨1066604, by rfl⟩ : syracuseStep 1422139 = 2133209) B2133209
theorem B5477179 : Blo 1421530 5477179 := bstep (se 1 (by rfl) ⟨4107884, by rfl⟩ : syracuseStep 5477179 = 8215769) B8215769
theorem B1422215 : Blo 1421530 1422215 := bstep (se 1 (by rfl) ⟨1066661, by rfl⟩ : syracuseStep 1422215 = 2133323) B2133323
theorem B2134919 : Blo 1421530 2134919 := bstep (se 1 (by rfl) ⟨1601189, by rfl⟩ : syracuseStep 2134919 = 3202379) B3202379
theorem B1422223 : Blo 1421530 1422223 := bstep (se 1 (by rfl) ⟨1066667, by rfl⟩ : syracuseStep 1422223 = 2133335) B2133335
theorem B24310691 : Blo 1421530 24310691 := bstep (se 1 (by rfl) ⟨18233018, by rfl⟩ : syracuseStep 24310691 = 36466037) B36466037
theorem B2134955 : Blo 1421530 2134955 := bstep (se 1 (by rfl) ⟨1601216, by rfl⟩ : syracuseStep 2134955 = 3202433) B3202433
theorem B1422267 : Blo 1421530 1422267 := bstep (se 1 (by rfl) ⟨1066700, by rfl⟩ : syracuseStep 1422267 = 2133401) B2133401
theorem B2134985 : Blo 1421530 2134985 := bstep (se 2 (by rfl) ⟨800619, by rfl⟩ : syracuseStep 2134985 = 1601239) B1601239
theorem B1422343 : Blo 1421530 1422343 := bstep (se 1 (by rfl) ⟨1066757, by rfl⟩ : syracuseStep 1422343 = 2133515) B2133515
theorem B1422351 : Blo 1421530 1422351 := bstep (se 1 (by rfl) ⟨1066763, by rfl⟩ : syracuseStep 1422351 = 2133527) B2133527
theorem B1422395 : Blo 1421530 1422395 := bstep (se 1 (by rfl) ⟨1066796, by rfl⟩ : syracuseStep 1422395 = 2133593) B2133593
theorem B2135099 : Blo 1421530 2135099 := bstep (se 1 (by rfl) ⟨1601324, by rfl⟩ : syracuseStep 2135099 = 3202649) B3202649
theorem B3601523 : Blo 1421530 3601523 := bstep (se 1 (by rfl) ⟨2701142, by rfl⟩ : syracuseStep 3601523 = 5402285) B5402285
theorem B2135159 : Blo 1421530 2135159 := bstep (se 1 (by rfl) ⟨1601369, by rfl⟩ : syracuseStep 2135159 = 3202739) B3202739
theorem B1422471 : Blo 1421530 1422471 := bstep (se 1 (by rfl) ⟨1066853, by rfl⟩ : syracuseStep 1422471 = 2133707) B2133707
theorem B3601543 : Blo 1421530 3601543 := bstep (se 1 (by rfl) ⟨2701157, by rfl⟩ : syracuseStep 3601543 = 5402315) B5402315
theorem B1422479 : Blo 1421530 1422479 := bstep (se 1 (by rfl) ⟨1066859, by rfl⟩ : syracuseStep 1422479 = 2133719) B2133719
theorem B2135183 : Blo 1421530 2135183 := bstep (se 1 (by rfl) ⟨1601387, by rfl⟩ : syracuseStep 2135183 = 3202775) B3202775
theorem B3200147 : Blo 1421530 3200147 := bstep (se 1 (by rfl) ⟨2400110, by rfl⟩ : syracuseStep 3200147 = 4800221) B4800221
theorem B2135225 : Blo 1421530 2135225 := bstep (se 2 (by rfl) ⟨800709, by rfl⟩ : syracuseStep 2135225 = 1601419) B1601419
theorem B1422523 : Blo 1421530 1422523 := bstep (se 1 (by rfl) ⟨1066892, by rfl⟩ : syracuseStep 1422523 = 2133785) B2133785
theorem B3200201 : Blo 1421530 3200201 := bstep (se 2 (by rfl) ⟨1200075, by rfl⟩ : syracuseStep 3200201 = 2400151) B2400151
theorem B1422599 : Blo 1421530 1422599 := bstep (se 1 (by rfl) ⟨1066949, by rfl⟩ : syracuseStep 1422599 = 2133899) B2133899
theorem B1422607 : Blo 1421530 1422607 := bstep (se 1 (by rfl) ⟨1066955, by rfl⟩ : syracuseStep 1422607 = 2133911) B2133911
theorem B1422651 : Blo 1421530 1422651 := bstep (se 1 (by rfl) ⟨1066988, by rfl⟩ : syracuseStep 1422651 = 2133977) B2133977
theorem B1422727 : Blo 1421530 1422727 := bstep (se 1 (by rfl) ⟨1067045, by rfl⟩ : syracuseStep 1422727 = 2134091) B2134091
theorem B11859335 : Blo 1421530 11859335 := bstep (se 1 (by rfl) ⟨8894501, by rfl⟩ : syracuseStep 11859335 = 17789003) B17789003
theorem B1422735 : Blo 1421530 1422735 := bstep (se 1 (by rfl) ⟨1067051, by rfl⟩ : syracuseStep 1422735 = 2134103) B2134103
theorem B6157721 : Blo 1421530 6157721 := bstep (se 2 (by rfl) ⟨2309145, by rfl⟩ : syracuseStep 6157721 = 4618291) B4618291
theorem B3601817 : Blo 1421530 3601817 := bstep (se 2 (by rfl) ⟨1350681, by rfl⟩ : syracuseStep 3601817 = 2701363) B2701363
theorem B1422779 : Blo 1421530 1422779 := bstep (se 1 (by rfl) ⟨1067084, by rfl⟩ : syracuseStep 1422779 = 2134169) B2134169
theorem B1422855 : Blo 1421530 1422855 := bstep (se 1 (by rfl) ⟨1067141, by rfl⟩ : syracuseStep 1422855 = 2134283) B2134283
theorem B1422863 : Blo 1421530 1422863 := bstep (se 1 (by rfl) ⟨1067147, by rfl⟩ : syracuseStep 1422863 = 2134295) B2134295
theorem B8099351 : Blo 1421530 8099351 := bstep (se 1 (by rfl) ⟨6074513, by rfl⟩ : syracuseStep 8099351 = 12149027) B12149027
theorem B116872733 : Blo 1421530 116872733 := bstep (se 3 (by rfl) ⟨21913637, by rfl⟩ : syracuseStep 116872733 = 43827275) B43827275
theorem B1422907 : Blo 1421530 1422907 := bstep (se 1 (by rfl) ⟨1067180, by rfl⟩ : syracuseStep 1422907 = 2134361) B2134361
theorem B3601979 : Blo 1421530 3601979 := bstep (se 1 (by rfl) ⟨2701484, by rfl⟩ : syracuseStep 3601979 = 5402969) B5402969
theorem B6075965 : Blo 1421530 6075965 := bstep (se 3 (by rfl) ⟨1139243, by rfl⟩ : syracuseStep 6075965 = 2278487) B2278487
theorem B10802807 : Blo 1421530 10802807 := bstep (se 1 (by rfl) ⟨8102105, by rfl⟩ : syracuseStep 10802807 = 16204211) B16204211
theorem B1799815 : Blo 1421530 1799815 := bstep (se 1 (by rfl) ⟨1349861, by rfl⟩ : syracuseStep 1799815 = 2699723) B2699723
theorem B1422983 : Blo 1421530 1422983 := bstep (se 1 (by rfl) ⟨1067237, by rfl⟩ : syracuseStep 1422983 = 2134475) B2134475
theorem B1422991 : Blo 1421530 1422991 := bstep (se 1 (by rfl) ⟨1067243, by rfl⟩ : syracuseStep 1422991 = 2134487) B2134487
theorem B1423035 : Blo 1421530 1423035 := bstep (se 1 (by rfl) ⟨1067276, by rfl⟩ : syracuseStep 1423035 = 2134553) B2134553
theorem B13670117 : Blo 1421530 13670117 := bstep (se 4 (by rfl) ⟨1281573, by rfl⟩ : syracuseStep 13670117 = 2563147) B2563147
theorem B1423111 : Blo 1421530 1423111 := bstep (se 1 (by rfl) ⟨1067333, by rfl⟩ : syracuseStep 1423111 = 2134667) B2134667
theorem B4798223 : Blo 1421530 4798223 := bstep (se 1 (by rfl) ⟨3598667, by rfl⟩ : syracuseStep 4798223 = 7197335) B7197335
theorem B3602191 : Blo 1421530 3602191 := bstep (se 1 (by rfl) ⟨2701643, by rfl⟩ : syracuseStep 3602191 = 5403287) B5403287
theorem B1423119 : Blo 1421530 1423119 := bstep (se 1 (by rfl) ⟨1067339, by rfl⟩ : syracuseStep 1423119 = 2134679) B2134679
theorem B1423163 : Blo 1421530 1423163 := bstep (se 1 (by rfl) ⟨1067372, by rfl⟩ : syracuseStep 1423163 = 2134745) B2134745
theorem B3200903 : Blo 1421530 3200903 := bstep (se 1 (by rfl) ⟨2400677, by rfl⟩ : syracuseStep 3200903 = 4801355) B4801355
theorem B1423239 : Blo 1421530 1423239 := bstep (se 1 (by rfl) ⟨1067429, by rfl⟩ : syracuseStep 1423239 = 2134859) B2134859
theorem B1423247 : Blo 1421530 1423247 := bstep (se 1 (by rfl) ⟨1067435, by rfl⟩ : syracuseStep 1423247 = 2134871) B2134871
theorem B1709995 : Blo 1421530 1709995 := bstep (se 1 (by rfl) ⟨1282496, by rfl⟩ : syracuseStep 1709995 = 2564993) B2564993
theorem B1423291 : Blo 1421530 1423291 := bstep (se 1 (by rfl) ⟨1067468, by rfl⟩ : syracuseStep 1423291 = 2134937) B2134937
theorem B1423367 : Blo 1421530 1423367 := bstep (se 1 (by rfl) ⟨1067525, by rfl⟩ : syracuseStep 1423367 = 2135051) B2135051
theorem B1423375 : Blo 1421530 1423375 := bstep (se 1 (by rfl) ⟨1067531, by rfl⟩ : syracuseStep 1423375 = 2135063) B2135063
theorem B10795031 : Blo 1421530 10795031 := bstep (se 1 (by rfl) ⟨8096273, by rfl⟩ : syracuseStep 10795031 = 16192547) B16192547
theorem B4798493 : Blo 1421530 4798493 := bstep (se 3 (by rfl) ⟨899717, by rfl⟩ : syracuseStep 4798493 = 1799435) B1799435
theorem B3602465 : Blo 1421530 3602465 := bstep (se 2 (by rfl) ⟨1350924, by rfl⟩ : syracuseStep 3602465 = 2701849) B2701849
theorem B1800235 : Blo 1421530 1800235 := bstep (se 1 (by rfl) ⟨1350176, by rfl⟩ : syracuseStep 1800235 = 2700353) B2700353
theorem B20510765 : Blo 1421530 20510765 := bstep (se 3 (by rfl) ⟨3845768, by rfl⟩ : syracuseStep 20510765 = 7691537) B7691537
theorem B5404715 : Blo 1421530 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B3201083 : Blo 1421530 3201083 := bstep (se 1 (by rfl) ⟨2400812, by rfl⟩ : syracuseStep 3201083 = 4801625) B4801625
theorem B1423419 : Blo 1421530 1423419 := bstep (se 1 (by rfl) ⟨1067564, by rfl⟩ : syracuseStep 1423419 = 2135129) B2135129
theorem B15374423 : Blo 1421530 15374423 := bstep (se 1 (by rfl) ⟨11530817, by rfl⟩ : syracuseStep 15374423 = 23061635) B23061635
theorem B1423495 : Blo 1421530 1423495 := bstep (se 1 (by rfl) ⟨1067621, by rfl⟩ : syracuseStep 1423495 = 2135243) B2135243
theorem B1423503 : Blo 1421530 1423503 := bstep (se 1 (by rfl) ⟨1067627, by rfl⟩ : syracuseStep 1423503 = 2135255) B2135255
theorem B3201209 : Blo 1421530 3201209 := bstep (se 2 (by rfl) ⟨1200453, by rfl⟩ : syracuseStep 3201209 = 2400907) B2400907
theorem B1800463 : Blo 1421530 1800463 := bstep (se 1 (by rfl) ⟨1350347, by rfl⟩ : syracuseStep 1800463 = 2700695) B2700695
theorem B2701583 : Blo 1421530 2701583 := bstep (se 1 (by rfl) ⟨2026187, by rfl⟩ : syracuseStep 2701583 = 4052375) B4052375
theorem B3201551 : Blo 1421530 3201551 := bstep (se 1 (by rfl) ⟨2401163, by rfl⟩ : syracuseStep 3201551 = 4802327) B4802327
theorem B3422753 : Blo 1421530 3422753 := bstep (se 2 (by rfl) ⟨1283532, by rfl⟩ : syracuseStep 3422753 = 2567065) B2567065
theorem B3201569 : Blo 1421530 3201569 := bstep (se 2 (by rfl) ⟨1200588, by rfl⟩ : syracuseStep 3201569 = 2401177) B2401177
theorem B10803779 : Blo 1421530 10803779 := bstep (se 1 (by rfl) ⟨8102834, by rfl⟩ : syracuseStep 10803779 = 16205669) B16205669
theorem B10246733 : Blo 1421530 10246733 := bstep (se 3 (by rfl) ⟨1921262, by rfl⟩ : syracuseStep 10246733 = 3842525) B3842525
theorem B5700215 : Blo 1421530 5700215 := bstep (se 1 (by rfl) ⟨4275161, by rfl⟩ : syracuseStep 5700215 = 8550323) B8550323
theorem B8649335 : Blo 1421530 8649335 := bstep (se 1 (by rfl) ⟨6487001, by rfl⟩ : syracuseStep 8649335 = 12974003) B12974003
theorem B2398855 : Blo 1421530 2398855 := bstep (se 1 (by rfl) ⟨1799141, by rfl⟩ : syracuseStep 2398855 = 3598283) B3598283
theorem B7199603 : Blo 1421530 7199603 := bstep (se 1 (by rfl) ⟨5399702, by rfl⟩ : syracuseStep 7199603 = 10799405) B10799405
theorem B3201911 : Blo 1421530 3201911 := bstep (se 1 (by rfl) ⟨2401433, by rfl⟩ : syracuseStep 3201911 = 4802867) B4802867
theorem B27351989 : Blo 1421530 27351989 := bstep (se 5 (by rfl) ⟨1282124, by rfl⟩ : syracuseStep 27351989 = 2564249) B2564249
theorem B3038153 : Blo 1421530 3038153 := bstep (se 2 (by rfl) ⟨1139307, by rfl⟩ : syracuseStep 3038153 = 2278615) B2278615
theorem B1801207 : Blo 1421530 1801207 := bstep (se 1 (by rfl) ⟨1350905, by rfl⟩ : syracuseStep 1801207 = 2701811) B2701811
theorem B3202091 : Blo 1421530 3202091 := bstep (se 1 (by rfl) ⟨2401568, by rfl⟩ : syracuseStep 3202091 = 4803137) B4803137
theorem B5397623 : Blo 1421530 5397623 := bstep (se 1 (by rfl) ⟨4048217, by rfl⟩ : syracuseStep 5397623 = 8096435) B8096435
theorem B2161799 : Blo 1421530 2161799 := bstep (se 1 (by rfl) ⟨1621349, by rfl⟩ : syracuseStep 2161799 = 3242699) B3242699
theorem B3038393 : Blo 1421530 3038393 := bstep (se 2 (by rfl) ⟨1139397, by rfl⟩ : syracuseStep 3038393 = 2278795) B2278795
theorem B2399503 : Blo 1421530 2399503 := bstep (se 1 (by rfl) ⟨1799627, by rfl⟩ : syracuseStep 2399503 = 3599255) B3599255
theorem B1801531 : Blo 1421530 1801531 := bstep (se 1 (by rfl) ⟨1351148, by rfl⟩ : syracuseStep 1801531 = 2702297) B2702297
theorem B7200089 : Blo 1421530 7200089 := bstep (se 2 (by rfl) ⟨2700033, by rfl⟩ : syracuseStep 7200089 = 5400067) B5400067
theorem B3202451 : Blo 1421530 3202451 := bstep (se 1 (by rfl) ⟨2401838, by rfl⟩ : syracuseStep 3202451 = 4803677) B4803677
theorem B4799897 : Blo 1421530 4799897 := bstep (se 2 (by rfl) ⟨1799961, by rfl⟩ : syracuseStep 4799897 = 3599923) B3599923
theorem B3202505 : Blo 1421530 3202505 := bstep (se 2 (by rfl) ⟨1200939, by rfl⟩ : syracuseStep 3202505 = 2401879) B2401879
theorem B36953603 : Blo 1421530 36953603 := bstep (se 1 (by rfl) ⟨27715202, by rfl⟩ : syracuseStep 36953603 = 55430405) B55430405
theorem B3038735 : Blo 1421530 3038735 := bstep (se 1 (by rfl) ⟨2279051, by rfl⟩ : syracuseStep 3038735 = 4558103) B4558103
theorem B29195927 : Blo 1421530 29195927 := bstep (se 1 (by rfl) ⟨21896945, by rfl⟩ : syracuseStep 29195927 = 43793891) B43793891
theorem B3038905 : Blo 1421530 3038905 := bstep (se 2 (by rfl) ⟨1139589, by rfl⟩ : syracuseStep 3038905 = 2279179) B2279179
theorem B2400043 : Blo 1421530 2400043 := bstep (se 1 (by rfl) ⟨1800032, by rfl⟩ : syracuseStep 2400043 = 3600065) B3600065
theorem B2400185 : Blo 1421530 2400185 := bstep (se 2 (by rfl) ⟨900069, by rfl⟩ : syracuseStep 2400185 = 1800139) B1800139
theorem B5128211 : Blo 1421530 5128211 := bstep (se 1 (by rfl) ⟨3846158, by rfl⟩ : syracuseStep 5128211 = 7692317) B7692317
theorem B2400313 : Blo 1421530 2400313 := bstep (se 2 (by rfl) ⟨900117, by rfl⟩ : syracuseStep 2400313 = 1800235) B1800235
theorem B5398609 : Blo 1421530 5398609 := bstep (se 2 (by rfl) ⟨2024478, by rfl⟩ : syracuseStep 5398609 = 4048957) B4048957
theorem B2736251 : Blo 1421530 2736251 := bstep (se 1 (by rfl) ⟨2052188, by rfl⟩ : syracuseStep 2736251 = 4104377) B4104377
theorem B2400455 : Blo 1421530 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B9109847 : Blo 1421530 9109847 := bstep (se 1 (by rfl) ⟨6832385, by rfl⟩ : syracuseStep 9109847 = 13664771) B13664771
theorem B2400617 : Blo 1421530 2400617 := bstep (se 2 (by rfl) ⟨900231, by rfl⟩ : syracuseStep 2400617 = 1800463) B1800463
theorem B5398913 : Blo 1421530 5398913 := bstep (se 2 (by rfl) ⟨2024592, by rfl⟩ : syracuseStep 5398913 = 4049185) B4049185
theorem B17302025 : Blo 1421530 17302025 := bstep (se 2 (by rfl) ⟨6488259, by rfl⟩ : syracuseStep 17302025 = 12976519) B12976519
theorem B5194439 : Blo 1421530 5194439 := bstep (se 1 (by rfl) ⟨3895829, by rfl⟩ : syracuseStep 5194439 = 7791659) B7791659
theorem B69190361 : Blo 1421530 69190361 := bstep (se 2 (by rfl) ⟨25946385, by rfl⟩ : syracuseStep 69190361 = 51892771) B51892771
theorem B2401015 : Blo 1421530 2401015 := bstep (se 1 (by rfl) ⟨1800761, by rfl⟩ : syracuseStep 2401015 = 3601523) B3601523
theorem B5399369 : Blo 1421530 5399369 := bstep (se 2 (by rfl) ⟨2024763, by rfl⟩ : syracuseStep 5399369 = 4049527) B4049527
theorem B2884457 : Blo 1421530 2884457 := bstep (se 2 (by rfl) ⟨1081671, by rfl⟩ : syracuseStep 2884457 = 2163343) B2163343
theorem B7906223 : Blo 1421530 7906223 := bstep (se 1 (by rfl) ⟨5929667, by rfl⟩ : syracuseStep 7906223 = 11859335) B11859335
theorem B5768119 : Blo 1421530 5768119 := bstep (se 1 (by rfl) ⟨4326089, by rfl⟩ : syracuseStep 5768119 = 8652179) B8652179
theorem B4801463 : Blo 1421530 4801463 := bstep (se 1 (by rfl) ⟨3601097, by rfl⟩ : syracuseStep 4801463 = 7202195) B7202195
theorem B2401211 : Blo 1421530 2401211 := bstep (se 1 (by rfl) ⟨1800908, by rfl⟩ : syracuseStep 2401211 = 3601817) B3601817
theorem B5399567 : Blo 1421530 5399567 := bstep (se 1 (by rfl) ⟨4049675, by rfl⟩ : syracuseStep 5399567 = 8099351) B8099351
theorem B77915155 : Blo 1421530 77915155 := bstep (se 1 (by rfl) ⟨58436366, by rfl⟩ : syracuseStep 77915155 = 116872733) B116872733
theorem B2401319 : Blo 1421530 2401319 := bstep (se 1 (by rfl) ⟨1800989, by rfl⟩ : syracuseStep 2401319 = 3601979) B3601979
theorem B15598657 : Blo 1421530 15598657 := bstep (se 2 (by rfl) ⟨5849496, by rfl⟩ : syracuseStep 15598657 = 11698993) B11698993
theorem B6833231 : Blo 1421530 6833231 := bstep (se 1 (by rfl) ⟨5124923, by rfl⟩ : syracuseStep 6833231 = 10249847) B10249847
theorem B7201871 : Blo 1421530 7201871 := bstep (se 1 (by rfl) ⟨5401403, by rfl⟩ : syracuseStep 7201871 = 10802807) B10802807
theorem B2401609 : Blo 1421530 2401609 := bstep (se 2 (by rfl) ⟨900603, by rfl⟩ : syracuseStep 2401609 = 1801207) B1801207
theorem B2401643 : Blo 1421530 2401643 := bstep (se 1 (by rfl) ⟨1801232, by rfl⟩ : syracuseStep 2401643 = 3602465) B3602465
theorem B13673843 : Blo 1421530 13673843 := bstep (se 1 (by rfl) ⟨10255382, by rfl⟩ : syracuseStep 13673843 = 20510765) B20510765
theorem B10249615 : Blo 1421530 10249615 := bstep (se 1 (by rfl) ⟨7687211, by rfl⟩ : syracuseStep 10249615 = 15374423) B15374423
theorem B11535817 : Blo 1421530 11535817 := bstep (se 2 (by rfl) ⟨4325931, by rfl⟩ : syracuseStep 11535817 = 8651863) B8651863
theorem B4802057 : Blo 1421530 4802057 := bstep (se 2 (by rfl) ⟨1800771, by rfl⟩ : syracuseStep 4802057 = 3601543) B3601543
theorem B9111179 : Blo 1421530 9111179 := bstep (se 1 (by rfl) ⟨6833384, by rfl⟩ : syracuseStep 9111179 = 13666769) B13666769
theorem B12977863 : Blo 1421530 12977863 := bstep (se 1 (by rfl) ⟨9733397, by rfl⟩ : syracuseStep 12977863 = 19466795) B19466795
theorem B7202519 : Blo 1421530 7202519 := bstep (se 1 (by rfl) ⟨5401889, by rfl⟩ : syracuseStep 7202519 = 10803779) B10803779
theorem B41043671 : Blo 1421530 41043671 := bstep (se 1 (by rfl) ⟨30782753, by rfl⟩ : syracuseStep 41043671 = 61565507) B61565507
theorem B2402041 : Blo 1421530 2402041 := bstep (se 2 (by rfl) ⟨900765, by rfl⟩ : syracuseStep 2402041 = 1801531) B1801531
theorem B2025481 : Blo 1421530 2025481 := bstep (se 2 (by rfl) ⟨759555, by rfl⟩ : syracuseStep 2025481 = 1519111) B1519111
theorem B3598415 : Blo 1421530 3598415 := bstep (se 1 (by rfl) ⟨2698811, by rfl⟩ : syracuseStep 3598415 = 5397623) B5397623
theorem B2025595 : Blo 1421530 2025595 := bstep (se 1 (by rfl) ⟨1519196, by rfl⟩ : syracuseStep 2025595 = 3038393) B3038393
theorem B24635735 : Blo 1421530 24635735 := bstep (se 1 (by rfl) ⟨18476801, by rfl⟩ : syracuseStep 24635735 = 36953603) B36953603
theorem B2025823 : Blo 1421530 2025823 := bstep (se 1 (by rfl) ⟨1519367, by rfl⟩ : syracuseStep 2025823 = 3038735) B3038735
theorem B4802921 : Blo 1421530 4802921 := bstep (se 2 (by rfl) ⟨1801095, by rfl⟩ : syracuseStep 4802921 = 3602191) B3602191
theorem B2132399 : Blo 1421530 2132399 := bstep (se 1 (by rfl) ⟨1599299, by rfl⟩ : syracuseStep 2132399 = 3198599) B3198599
theorem B2132489 : Blo 1421530 2132489 := bstep (se 2 (by rfl) ⟨799683, by rfl⟩ : syracuseStep 2132489 = 1599367) B1599367
theorem B2132519 : Blo 1421530 2132519 := bstep (se 1 (by rfl) ⟨1599389, by rfl⟩ : syracuseStep 2132519 = 3198779) B3198779
theorem B2279993 : Blo 1421530 2279993 := bstep (se 2 (by rfl) ⟨854997, by rfl⟩ : syracuseStep 2279993 = 1709995) B1709995
theorem B2132603 : Blo 1421530 2132603 := bstep (se 1 (by rfl) ⟨1599452, by rfl⟩ : syracuseStep 2132603 = 3198905) B3198905
theorem B1600123 : Blo 1421530 1600123 := bstep (se 1 (by rfl) ⟨1200092, by rfl⟩ : syracuseStep 1600123 = 2400185) B2400185
theorem B8104657 : Blo 1421530 8104657 := bstep (se 2 (by rfl) ⟨3039246, by rfl⟩ : syracuseStep 8104657 = 6078493) B6078493
theorem B3599063 : Blo 1421530 3599063 := bstep (se 1 (by rfl) ⟨2699297, by rfl⟩ : syracuseStep 3599063 = 5398595) B5398595
theorem B2132729 : Blo 1421530 2132729 := bstep (se 2 (by rfl) ⟨799773, by rfl⟩ : syracuseStep 2132729 = 1599547) B1599547
theorem B2132831 : Blo 1421530 2132831 := bstep (se 1 (by rfl) ⟨1599623, by rfl⟩ : syracuseStep 2132831 = 3199247) B3199247
theorem B2132843 : Blo 1421530 2132843 := bstep (se 1 (by rfl) ⟨1599632, by rfl⟩ : syracuseStep 2132843 = 3199265) B3199265
theorem B14609297 : Blo 1421530 14609297 := bstep (se 2 (by rfl) ⟨5478486, by rfl⟩ : syracuseStep 14609297 = 10956973) B10956973
theorem B2026415 : Blo 1421530 2026415 := bstep (se 1 (by rfl) ⟨1519811, by rfl⟩ : syracuseStep 2026415 = 3039623) B3039623
theorem B5000123 : Blo 1421530 5000123 := bstep (se 1 (by rfl) ⟨3750092, by rfl⟩ : syracuseStep 5000123 = 7500185) B7500185
theorem B4803515 : Blo 1421530 4803515 := bstep (se 1 (by rfl) ⟨3602636, by rfl⟩ : syracuseStep 4803515 = 7205273) B7205273
theorem B3599417 : Blo 1421530 3599417 := bstep (se 2 (by rfl) ⟨1349781, by rfl⟩ : syracuseStep 3599417 = 2699563) B2699563
theorem B2133071 : Blo 1421530 2133071 := bstep (se 1 (by rfl) ⟨1599803, by rfl⟩ : syracuseStep 2133071 = 3199607) B3199607
theorem B1600591 : Blo 1421530 1600591 := bstep (se 1 (by rfl) ⟨1200443, by rfl⟩ : syracuseStep 1600591 = 2400887) B2400887
theorem B87633089 : Blo 1421530 87633089 := bstep (se 2 (by rfl) ⟨32862408, by rfl⟩ : syracuseStep 87633089 = 65724817) B65724817
theorem B2133191 : Blo 1421530 2133191 := bstep (se 1 (by rfl) ⟨1599893, by rfl⟩ : syracuseStep 2133191 = 3199787) B3199787
theorem B15379703 : Blo 1421530 15379703 := bstep (se 1 (by rfl) ⟨11534777, by rfl⟩ : syracuseStep 15379703 = 23069555) B23069555
theorem B16207127 : Blo 1421530 16207127 := bstep (se 1 (by rfl) ⟨12155345, by rfl⟩ : syracuseStep 16207127 = 24310691) B24310691
theorem B27356453 : Blo 1421530 27356453 := bstep (se 4 (by rfl) ⟨2564667, by rfl⟩ : syracuseStep 27356453 = 5129335) B5129335
theorem B2133353 : Blo 1421530 2133353 := bstep (se 2 (by rfl) ⟨800007, by rfl⟩ : syracuseStep 2133353 = 1600015) B1600015
theorem B5770601 : Blo 1421530 5770601 := bstep (se 2 (by rfl) ⟨2163975, by rfl⟩ : syracuseStep 5770601 = 4327951) B4327951
theorem B2133431 : Blo 1421530 2133431 := bstep (se 1 (by rfl) ⟨1600073, by rfl⟩ : syracuseStep 2133431 = 3200147) B3200147
theorem B2133467 : Blo 1421530 2133467 := bstep (se 1 (by rfl) ⟨1600100, by rfl⟩ : syracuseStep 2133467 = 3200201) B3200201
theorem B1600987 : Blo 1421530 1600987 := bstep (se 1 (by rfl) ⟨1200740, by rfl⟩ : syracuseStep 1600987 = 2401481) B2401481
theorem B3198473 : Blo 1421530 3198473 := bstep (se 2 (by rfl) ⟨1199427, by rfl⟩ : syracuseStep 3198473 = 2398855) B2398855
theorem B2698849 : Blo 1421530 2698849 := bstep (se 2 (by rfl) ⟨1012068, by rfl⟩ : syracuseStep 2698849 = 2024137) B2024137
theorem B11685509 : Blo 1421530 11685509 := bstep (se 4 (by rfl) ⟨1095516, by rfl⟩ : syracuseStep 11685509 = 2191033) B2191033
theorem B4050643 : Blo 1421530 4050643 := bstep (se 1 (by rfl) ⟨3037982, by rfl⟩ : syracuseStep 4050643 = 6075965) B6075965
theorem B16420589 : Blo 1421530 16420589 := bstep (se 3 (by rfl) ⟨3078860, by rfl⟩ : syracuseStep 16420589 = 6157721) B6157721
theorem B7302905 : Blo 1421530 7302905 := bstep (se 2 (by rfl) ⟨2738589, by rfl⟩ : syracuseStep 7302905 = 5477179) B5477179
theorem B9113411 : Blo 1421530 9113411 := bstep (se 1 (by rfl) ⟨6835058, by rfl⟩ : syracuseStep 9113411 = 13670117) B13670117
theorem B3198815 : Blo 1421530 3198815 := bstep (se 1 (by rfl) ⟨2399111, by rfl⟩ : syracuseStep 3198815 = 4798223) B4798223
theorem B3419999 : Blo 1421530 3419999 := bstep (se 1 (by rfl) ⟨2564999, by rfl⟩ : syracuseStep 3419999 = 5129999) B5129999
theorem B7196525 : Blo 1421530 7196525 := bstep (se 3 (by rfl) ⟨1349348, by rfl⟩ : syracuseStep 7196525 = 2698697) B2698697
theorem B36966293 : Blo 1421530 36966293 := bstep (se 6 (by rfl) ⟨866397, by rfl⟩ : syracuseStep 36966293 = 1732795) B1732795
theorem B5124001 : Blo 1421530 5124001 := bstep (se 2 (by rfl) ⟨1921500, by rfl⟩ : syracuseStep 5124001 = 3843001) B3843001
theorem B2699183 : Blo 1421530 2699183 := bstep (se 1 (by rfl) ⟨2024387, by rfl⟩ : syracuseStep 2699183 = 4048775) B4048775
theorem B2133935 : Blo 1421530 2133935 := bstep (se 1 (by rfl) ⟨1600451, by rfl⟩ : syracuseStep 2133935 = 3200903) B3200903
theorem B1601455 : Blo 1421530 1601455 := bstep (se 1 (by rfl) ⟨1201091, by rfl⟩ : syracuseStep 1601455 = 2402183) B2402183
theorem B2134025 : Blo 1421530 2134025 := bstep (se 2 (by rfl) ⟨800259, by rfl⟩ : syracuseStep 2134025 = 1600519) B1600519
theorem B7196687 : Blo 1421530 7196687 := bstep (se 1 (by rfl) ⟨5397515, by rfl⟩ : syracuseStep 7196687 = 10795031) B10795031
theorem B3198995 : Blo 1421530 3198995 := bstep (se 1 (by rfl) ⟨2399246, by rfl⟩ : syracuseStep 3198995 = 4798493) B4798493
theorem B2134055 : Blo 1421530 2134055 := bstep (se 1 (by rfl) ⟨1600541, by rfl⟩ : syracuseStep 2134055 = 3201083) B3201083
theorem B2134139 : Blo 1421530 2134139 := bstep (se 1 (by rfl) ⟨1600604, by rfl⟩ : syracuseStep 2134139 = 3201209) B3201209
theorem B1421531 : Blo 1421530 1421531 := bstep (se 1 (by rfl) ⟨1066148, by rfl⟩ : syracuseStep 1421531 = 2132297) B2132297
theorem B2134265 : Blo 1421530 2134265 := bstep (se 2 (by rfl) ⟨800349, by rfl⟩ : syracuseStep 2134265 = 1600699) B1600699
theorem B10809611 : Blo 1421530 10809611 := bstep (se 1 (by rfl) ⟨8107208, by rfl⟩ : syracuseStep 10809611 = 16214417) B16214417
theorem B1421607 : Blo 1421530 1421607 := bstep (se 1 (by rfl) ⟨1066205, by rfl⟩ : syracuseStep 1421607 = 2132411) B2132411
theorem B1421647 : Blo 1421530 1421647 := bstep (se 1 (by rfl) ⟨1066235, by rfl⟩ : syracuseStep 1421647 = 2132471) B2132471
theorem B1421663 : Blo 1421530 1421663 := bstep (se 1 (by rfl) ⟨1066247, by rfl⟩ : syracuseStep 1421663 = 2132495) B2132495
theorem B2134367 : Blo 1421530 2134367 := bstep (se 1 (by rfl) ⟨1600775, by rfl⟩ : syracuseStep 2134367 = 3201551) B3201551
theorem B3199337 : Blo 1421530 3199337 := bstep (se 2 (by rfl) ⟨1199751, by rfl⟩ : syracuseStep 3199337 = 2399503) B2399503
theorem B2281835 : Blo 1421530 2281835 := bstep (se 1 (by rfl) ⟨1711376, by rfl⟩ : syracuseStep 2281835 = 3422753) B3422753
theorem B2134379 : Blo 1421530 2134379 := bstep (se 1 (by rfl) ⟨1600784, by rfl⟩ : syracuseStep 2134379 = 3201569) B3201569
theorem B1421691 : Blo 1421530 1421691 := bstep (se 1 (by rfl) ⟨1066268, by rfl⟩ : syracuseStep 1421691 = 2132537) B2132537
theorem B1421743 : Blo 1421530 1421743 := bstep (se 1 (by rfl) ⟨1066307, by rfl⟩ : syracuseStep 1421743 = 2132615) B2132615
theorem B1421767 : Blo 1421530 1421767 := bstep (se 1 (by rfl) ⟨1066325, by rfl⟩ : syracuseStep 1421767 = 2132651) B2132651
theorem B1421787 : Blo 1421530 1421787 := bstep (se 1 (by rfl) ⟨1066340, by rfl⟩ : syracuseStep 1421787 = 2132681) B2132681
theorem B1421863 : Blo 1421530 1421863 := bstep (se 1 (by rfl) ⟨1066397, by rfl⟩ : syracuseStep 1421863 = 2132795) B2132795
theorem B6074939 : Blo 1421530 6074939 := bstep (se 1 (by rfl) ⟨4556204, by rfl⟩ : syracuseStep 6074939 = 9112409) B9112409
theorem B7205435 : Blo 1421530 7205435 := bstep (se 1 (by rfl) ⟨5404076, by rfl⟩ : syracuseStep 7205435 = 10808153) B10808153
theorem B1421903 : Blo 1421530 1421903 := bstep (se 1 (by rfl) ⟨1066427, by rfl⟩ : syracuseStep 1421903 = 2132855) B2132855
theorem B2134607 : Blo 1421530 2134607 := bstep (se 1 (by rfl) ⟨1600955, by rfl⟩ : syracuseStep 2134607 = 3201911) B3201911
theorem B1421919 : Blo 1421530 1421919 := bstep (se 1 (by rfl) ⟨1066439, by rfl⟩ : syracuseStep 1421919 = 2132879) B2132879
theorem B1421947 : Blo 1421530 1421947 := bstep (se 1 (by rfl) ⟨1066460, by rfl⟩ : syracuseStep 1421947 = 2132921) B2132921
theorem B1421999 : Blo 1421530 1421999 := bstep (se 1 (by rfl) ⟨1066499, by rfl⟩ : syracuseStep 1421999 = 2132999) B2132999
theorem B1422023 : Blo 1421530 1422023 := bstep (se 1 (by rfl) ⟨1066517, by rfl⟩ : syracuseStep 1422023 = 2133035) B2133035
theorem B2134727 : Blo 1421530 2134727 := bstep (se 1 (by rfl) ⟨1601045, by rfl⟩ : syracuseStep 2134727 = 3202091) B3202091
theorem B1422043 : Blo 1421530 1422043 := bstep (se 1 (by rfl) ⟨1066532, by rfl⟩ : syracuseStep 1422043 = 2133065) B2133065
theorem B1422119 : Blo 1421530 1422119 := bstep (se 1 (by rfl) ⟨1066589, by rfl⟩ : syracuseStep 1422119 = 2133179) B2133179
theorem B1422159 : Blo 1421530 1422159 := bstep (se 1 (by rfl) ⟨1066619, by rfl⟩ : syracuseStep 1422159 = 2133239) B2133239
theorem B1422175 : Blo 1421530 1422175 := bstep (se 1 (by rfl) ⟨1066631, by rfl⟩ : syracuseStep 1422175 = 2133263) B2133263
theorem B2134889 : Blo 1421530 2134889 := bstep (se 2 (by rfl) ⟨800583, by rfl⟩ : syracuseStep 2134889 = 1601167) B1601167
theorem B1422203 : Blo 1421530 1422203 := bstep (se 1 (by rfl) ⟨1066652, by rfl⟩ : syracuseStep 1422203 = 2133305) B2133305
theorem B4051873 : Blo 1421530 4051873 := bstep (se 2 (by rfl) ⟨1519452, by rfl⟩ : syracuseStep 4051873 = 3038905) B3038905
theorem B1422255 : Blo 1421530 1422255 := bstep (se 1 (by rfl) ⟨1066691, by rfl⟩ : syracuseStep 1422255 = 2133383) B2133383
theorem B2134967 : Blo 1421530 2134967 := bstep (se 1 (by rfl) ⟨1601225, by rfl⟩ : syracuseStep 2134967 = 3202451) B3202451
theorem B3199931 : Blo 1421530 3199931 := bstep (se 1 (by rfl) ⟨2399948, by rfl⟩ : syracuseStep 3199931 = 4799897) B4799897
theorem B1422279 : Blo 1421530 1422279 := bstep (se 1 (by rfl) ⟨1066709, by rfl⟩ : syracuseStep 1422279 = 2133419) B2133419
theorem B1422299 : Blo 1421530 1422299 := bstep (se 1 (by rfl) ⟨1066724, by rfl⟩ : syracuseStep 1422299 = 2133449) B2133449
theorem B2135003 : Blo 1421530 2135003 := bstep (se 1 (by rfl) ⟨1601252, by rfl⟩ : syracuseStep 2135003 = 3202505) B3202505
theorem B2700307 : Blo 1421530 2700307 := bstep (se 1 (by rfl) ⟨2025230, by rfl⟩ : syracuseStep 2700307 = 4050461) B4050461
theorem B1422375 : Blo 1421530 1422375 := bstep (se 1 (by rfl) ⟨1066781, by rfl⟩ : syracuseStep 1422375 = 2133563) B2133563
theorem B3200057 : Blo 1421530 3200057 := bstep (se 2 (by rfl) ⟨1200021, by rfl⟩ : syracuseStep 3200057 = 2400043) B2400043
theorem B1422415 : Blo 1421530 1422415 := bstep (se 1 (by rfl) ⟨1066811, by rfl⟩ : syracuseStep 1422415 = 2133623) B2133623
theorem B1422431 : Blo 1421530 1422431 := bstep (se 1 (by rfl) ⟨1066823, by rfl⟩ : syracuseStep 1422431 = 2133647) B2133647
theorem B1422459 : Blo 1421530 1422459 := bstep (se 1 (by rfl) ⟨1066844, by rfl⟩ : syracuseStep 1422459 = 2133689) B2133689
theorem B1422511 : Blo 1421530 1422511 := bstep (se 1 (by rfl) ⟨1066883, by rfl⟩ : syracuseStep 1422511 = 2133767) B2133767
theorem B7206083 : Blo 1421530 7206083 := bstep (se 1 (by rfl) ⟨5404562, by rfl⟩ : syracuseStep 7206083 = 10809125) B10809125
theorem B1422535 : Blo 1421530 1422535 := bstep (se 1 (by rfl) ⟨1066901, by rfl⟩ : syracuseStep 1422535 = 2133803) B2133803
theorem B1422555 : Blo 1421530 1422555 := bstep (se 1 (by rfl) ⟨1066916, by rfl⟩ : syracuseStep 1422555 = 2133833) B2133833
theorem B2700535 : Blo 1421530 2700535 := bstep (se 1 (by rfl) ⟨2025401, by rfl⟩ : syracuseStep 2700535 = 4050803) B4050803
theorem B3601655 : Blo 1421530 3601655 := bstep (se 1 (by rfl) ⟨2701241, by rfl⟩ : syracuseStep 3601655 = 5402483) B5402483
theorem B1422631 : Blo 1421530 1422631 := bstep (se 1 (by rfl) ⟨1066973, by rfl⟩ : syracuseStep 1422631 = 2133947) B2133947
theorem B1422671 : Blo 1421530 1422671 := bstep (se 1 (by rfl) ⟨1067003, by rfl⟩ : syracuseStep 1422671 = 2134007) B2134007
theorem B1422687 : Blo 1421530 1422687 := bstep (se 1 (by rfl) ⟨1067015, by rfl⟩ : syracuseStep 1422687 = 2134031) B2134031
theorem B1422715 : Blo 1421530 1422715 := bstep (se 1 (by rfl) ⟨1067036, by rfl⟩ : syracuseStep 1422715 = 2134073) B2134073
theorem B3200399 : Blo 1421530 3200399 := bstep (se 1 (by rfl) ⟨2400299, by rfl⟩ : syracuseStep 3200399 = 4800599) B4800599
theorem B1422767 : Blo 1421530 1422767 := bstep (se 1 (by rfl) ⟨1067075, by rfl⟩ : syracuseStep 1422767 = 2134151) B2134151
theorem B1422791 : Blo 1421530 1422791 := bstep (se 1 (by rfl) ⟨1067093, by rfl⟩ : syracuseStep 1422791 = 2134187) B2134187
theorem B1422811 : Blo 1421530 1422811 := bstep (se 1 (by rfl) ⟨1067108, by rfl⟩ : syracuseStep 1422811 = 2134217) B2134217
theorem B4052443 : Blo 1421530 4052443 := bstep (se 1 (by rfl) ⟨3039332, by rfl⟩ : syracuseStep 4052443 = 6078665) B6078665
theorem B2700839 : Blo 1421530 2700839 := bstep (se 1 (by rfl) ⟨2025629, by rfl⟩ : syracuseStep 2700839 = 4051259) B4051259
theorem B1422887 : Blo 1421530 1422887 := bstep (se 1 (by rfl) ⟨1067165, by rfl⟩ : syracuseStep 1422887 = 2134331) B2134331
theorem B1799759 : Blo 1421530 1799759 := bstep (se 1 (by rfl) ⟨1349819, by rfl⟩ : syracuseStep 1799759 = 2699639) B2699639
theorem B1422927 : Blo 1421530 1422927 := bstep (se 1 (by rfl) ⟨1067195, by rfl⟩ : syracuseStep 1422927 = 2134391) B2134391
theorem B1422943 : Blo 1421530 1422943 := bstep (se 1 (by rfl) ⟨1067207, by rfl⟩ : syracuseStep 1422943 = 2134415) B2134415
theorem B1422971 : Blo 1421530 1422971 := bstep (se 1 (by rfl) ⟨1067228, by rfl⟩ : syracuseStep 1422971 = 2134457) B2134457
theorem B1423023 : Blo 1421530 1423023 := bstep (se 1 (by rfl) ⟨1067267, by rfl⟩ : syracuseStep 1423023 = 2134535) B2134535
theorem B1423047 : Blo 1421530 1423047 := bstep (se 1 (by rfl) ⟨1067285, by rfl⟩ : syracuseStep 1423047 = 2134571) B2134571
theorem B3200723 : Blo 1421530 3200723 := bstep (se 1 (by rfl) ⟨2400542, by rfl⟩ : syracuseStep 3200723 = 4801085) B4801085
theorem B1423067 : Blo 1421530 1423067 := bstep (se 1 (by rfl) ⟨1067300, by rfl⟩ : syracuseStep 1423067 = 2134601) B2134601
theorem B1922809 : Blo 1421530 1922809 := bstep (se 2 (by rfl) ⟨721053, by rfl⟩ : syracuseStep 1922809 = 1442107) B1442107
theorem B1423143 : Blo 1421530 1423143 := bstep (se 1 (by rfl) ⟨1067357, by rfl⟩ : syracuseStep 1423143 = 2134715) B2134715
theorem B5125961 : Blo 1421530 5125961 := bstep (se 2 (by rfl) ⟨1922235, by rfl⟩ : syracuseStep 5125961 = 3844471) B3844471
theorem B1423183 : Blo 1421530 1423183 := bstep (se 1 (by rfl) ⟨1067387, by rfl⟩ : syracuseStep 1423183 = 2134775) B2134775
theorem B1423199 : Blo 1421530 1423199 := bstep (se 1 (by rfl) ⟨1067399, by rfl⟩ : syracuseStep 1423199 = 2134799) B2134799
theorem B1423227 : Blo 1421530 1423227 := bstep (se 1 (by rfl) ⟨1067420, by rfl⟩ : syracuseStep 1423227 = 2134841) B2134841
theorem B1423279 : Blo 1421530 1423279 := bstep (se 1 (by rfl) ⟨1067459, by rfl⟩ : syracuseStep 1423279 = 2134919) B2134919
theorem B1423303 : Blo 1421530 1423303 := bstep (se 1 (by rfl) ⟨1067477, by rfl⟩ : syracuseStep 1423303 = 2134955) B2134955
theorem B1423323 : Blo 1421530 1423323 := bstep (se 1 (by rfl) ⟨1067492, by rfl⟩ : syracuseStep 1423323 = 2134985) B2134985
theorem B91248611 : Blo 1421530 91248611 := bstep (se 1 (by rfl) ⟨68436458, by rfl⟩ : syracuseStep 91248611 = 136872917) B136872917
theorem B1423399 : Blo 1421530 1423399 := bstep (se 1 (by rfl) ⟨1067549, by rfl⟩ : syracuseStep 1423399 = 2135099) B2135099
theorem B1423439 : Blo 1421530 1423439 := bstep (se 1 (by rfl) ⟨1067579, by rfl⟩ : syracuseStep 1423439 = 2135159) B2135159
theorem B1423455 : Blo 1421530 1423455 := bstep (se 1 (by rfl) ⟨1067591, by rfl⟩ : syracuseStep 1423455 = 2135183) B2135183
theorem B1423483 : Blo 1421530 1423483 := bstep (se 1 (by rfl) ⟨1067612, by rfl⟩ : syracuseStep 1423483 = 2135225) B2135225
theorem B4053149 : Blo 1421530 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B4053377 : Blo 1421530 4053377 := bstep (se 2 (by rfl) ⟨1520016, by rfl⟩ : syracuseStep 4053377 = 3040033) B3040033
theorem B3201659 : Blo 1421530 3201659 := bstep (se 1 (by rfl) ⟨2401244, by rfl⟩ : syracuseStep 3201659 = 4802489) B4802489
theorem B3603143 : Blo 1421530 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B7199441 : Blo 1421530 7199441 := bstep (se 2 (by rfl) ⟨2699790, by rfl⟩ : syracuseStep 7199441 = 5399581) B5399581
theorem B4053719 : Blo 1421530 4053719 := bstep (se 1 (by rfl) ⟨3040289, by rfl⟩ : syracuseStep 4053719 = 6080579) B6080579
theorem B3201785 : Blo 1421530 3201785 := bstep (se 2 (by rfl) ⟨1200669, by rfl⟩ : syracuseStep 3201785 = 2401339) B2401339
theorem B2702153 : Blo 1421530 2702153 := bstep (se 2 (by rfl) ⟨1013307, by rfl⟩ : syracuseStep 2702153 = 2026615) B2026615
theorem B2399071 : Blo 1421530 2399071 := bstep (se 1 (by rfl) ⟨1799303, by rfl⟩ : syracuseStep 2399071 = 3598607) B3598607
theorem B1801055 : Blo 1421530 1801055 := bstep (se 1 (by rfl) ⟨1350791, by rfl⟩ : syracuseStep 1801055 = 2701583) B2701583
theorem B2399159 : Blo 1421530 2399159 := bstep (se 1 (by rfl) ⟨1799369, by rfl⟩ : syracuseStep 2399159 = 3598739) B3598739
theorem B3202055 : Blo 1421530 3202055 := bstep (se 1 (by rfl) ⟨2401541, by rfl⟩ : syracuseStep 3202055 = 4803083) B4803083
theorem B15588395 : Blo 1421530 15588395 := bstep (se 1 (by rfl) ⟨11691296, by rfl⟩ : syracuseStep 15588395 = 23382593) B23382593
theorem B6831155 : Blo 1421530 6831155 := bstep (se 1 (by rfl) ⟨5123366, by rfl⟩ : syracuseStep 6831155 = 10246733) B10246733
theorem B3800143 : Blo 1421530 3800143 := bstep (se 1 (by rfl) ⟨2850107, by rfl⟩ : syracuseStep 3800143 = 5700215) B5700215
theorem B5766223 : Blo 1421530 5766223 := bstep (se 1 (by rfl) ⟨4324667, by rfl⟩ : syracuseStep 5766223 = 8649335) B8649335
theorem B3202127 : Blo 1421530 3202127 := bstep (se 1 (by rfl) ⟨2401595, by rfl⟩ : syracuseStep 3202127 = 4803191) B4803191
theorem B7396555 : Blo 1421530 7396555 := bstep (se 1 (by rfl) ⟨5547416, by rfl⟩ : syracuseStep 7396555 = 11094833) B11094833
theorem B4799735 : Blo 1421530 4799735 := bstep (se 1 (by rfl) ⟨3599801, by rfl⟩ : syracuseStep 4799735 = 7199603) B7199603
theorem B18234659 : Blo 1421530 18234659 := bstep (se 1 (by rfl) ⟨13675994, by rfl⟩ : syracuseStep 18234659 = 27351989) B27351989
theorem B9108773 : Blo 1421530 9108773 := bstep (se 4 (by rfl) ⟨853947, by rfl⟩ : syracuseStep 9108773 = 1707895) B1707895
theorem B1441199 : Blo 1421530 1441199 := bstep (se 1 (by rfl) ⟨1080899, by rfl⟩ : syracuseStep 1441199 = 2161799) B2161799
theorem B10796489 : Blo 1421530 10796489 := bstep (se 2 (by rfl) ⟨4048683, by rfl⟩ : syracuseStep 10796489 = 8097367) B8097367
theorem B3202523 : Blo 1421530 3202523 := bstep (se 1 (by rfl) ⟨2401892, by rfl⟩ : syracuseStep 3202523 = 4803785) B4803785
theorem B2399753 : Blo 1421530 2399753 := bstep (se 2 (by rfl) ⟨899907, by rfl⟩ : syracuseStep 2399753 = 1799815) B1799815
theorem B4800059 : Blo 1421530 4800059 := bstep (se 1 (by rfl) ⟨3600044, by rfl⟩ : syracuseStep 4800059 = 7200089) B7200089
theorem B7298657 : Blo 1421530 7298657 := bstep (se 2 (by rfl) ⟨2736996, by rfl⟩ : syracuseStep 7298657 = 5473993) B5473993
theorem B2399915 : Blo 1421530 2399915 := bstep (se 1 (by rfl) ⟨1799936, by rfl⟩ : syracuseStep 2399915 = 3599873) B3599873
theorem B19463951 : Blo 1421530 19463951 := bstep (se 1 (by rfl) ⟨14597963, by rfl⟩ : syracuseStep 19463951 = 29195927) B29195927
theorem B4800329 : Blo 1421530 4800329 := bstep (se 2 (by rfl) ⟨1800123, by rfl⟩ : syracuseStep 4800329 = 3600247) B3600247
theorem B9117535 : Blo 1421530 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B8101741 : Blo 1421530 8101741 := bstep (se 3 (by rfl) ⟨1519076, by rfl⟩ : syracuseStep 8101741 = 3038153) B3038153
theorem B16195463 : Blo 1421530 16195463 := bstep (se 1 (by rfl) ⟨12146597, by rfl⟩ : syracuseStep 16195463 = 24293195) B24293195
theorem B11534683 : Blo 1421530 11534683 := bstep (se 1 (by rfl) ⟨8651012, by rfl⟩ : syracuseStep 11534683 = 17302025) B17302025
theorem B4555487 : Blo 1421530 4555487 := bstep (se 1 (by rfl) ⟨3416615, by rfl⟩ : syracuseStep 4555487 = 6833231) B6833231
theorem B4801247 : Blo 1421530 4801247 := bstep (se 1 (by rfl) ⟨3600935, by rfl⟩ : syracuseStep 4801247 = 7201871) B7201871
theorem B2401103 : Blo 1421530 2401103 := bstep (se 1 (by rfl) ⟨1800827, by rfl⟩ : syracuseStep 2401103 = 3601655) B3601655
theorem B10806209 : Blo 1421530 10806209 := bstep (se 2 (by rfl) ⟨4052328, by rfl⟩ : syracuseStep 10806209 = 8104657) B8104657
theorem B69215269 : Blo 1421530 69215269 := bstep (se 4 (by rfl) ⟨6488931, by rfl⟩ : syracuseStep 69215269 = 12977863) B12977863
theorem B3843197 : Blo 1421530 3843197 := bstep (se 3 (by rfl) ⟨720599, by rfl⟩ : syracuseStep 3843197 = 1441199) B1441199
theorem B4801679 : Blo 1421530 4801679 := bstep (se 1 (by rfl) ⟨3601259, by rfl⟩ : syracuseStep 4801679 = 7202519) B7202519
theorem B27362447 : Blo 1421530 27362447 := bstep (se 1 (by rfl) ⟨20521835, by rfl⟩ : syracuseStep 27362447 = 41043671) B41043671
theorem B6079981 : Blo 1421530 6079981 := bstep (se 3 (by rfl) ⟨1139996, by rfl⟩ : syracuseStep 6079981 = 2279993) B2279993
theorem B2402095 : Blo 1421530 2402095 := bstep (se 1 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 2402095 = 3603143) B3603143
theorem B13666153 : Blo 1421530 13666153 := bstep (se 2 (by rfl) ⟨5124807, by rfl⟩ : syracuseStep 13666153 = 10249615) B10249615
theorem B1599439 : Blo 1421530 1599439 := bstep (se 1 (by rfl) ⟨1199579, by rfl⟩ : syracuseStep 1599439 = 2399159) B2399159
theorem B3598465 : Blo 1421530 3598465 := bstep (se 2 (by rfl) ⟨1349424, by rfl⟩ : syracuseStep 3598465 = 2698849) B2698849
theorem B6072515 : Blo 1421530 6072515 := bstep (se 1 (by rfl) ⟨4554386, by rfl⟩ : syracuseStep 6072515 = 9108773) B9108773
theorem B18237635 : Blo 1421530 18237635 := bstep (se 1 (by rfl) ⟨13678226, by rfl⟩ : syracuseStep 18237635 = 27356453) B27356453
theorem B4802813 : Blo 1421530 4802813 := bstep (se 3 (by rfl) ⟨900527, by rfl⟩ : syracuseStep 4802813 = 1801055) B1801055
theorem B5400857 : Blo 1421530 5400857 := bstep (se 2 (by rfl) ⟨2025321, by rfl⟩ : syracuseStep 5400857 = 4050643) B4050643
theorem B2132315 : Blo 1421530 2132315 := bstep (se 1 (by rfl) ⟨1599236, by rfl⟩ : syracuseStep 2132315 = 3198473) B3198473
theorem B1599835 : Blo 1421530 1599835 := bstep (se 1 (by rfl) ⟨1199876, by rfl⟩ : syracuseStep 1599835 = 2399753) B2399753
theorem B1599943 : Blo 1421530 1599943 := bstep (se 1 (by rfl) ⟨1199957, by rfl⟩ : syracuseStep 1599943 = 2399915) B2399915
theorem B10947059 : Blo 1421530 10947059 := bstep (se 1 (by rfl) ⟨8210294, by rfl⟩ : syracuseStep 10947059 = 16420589) B16420589
theorem B4868603 : Blo 1421530 4868603 := bstep (se 1 (by rfl) ⟨3651452, by rfl⟩ : syracuseStep 4868603 = 7302905) B7302905
theorem B2132543 : Blo 1421530 2132543 := bstep (se 1 (by rfl) ⟨1599407, by rfl⟩ : syracuseStep 2132543 = 3198815) B3198815
theorem B2279999 : Blo 1421530 2279999 := bstep (se 1 (by rfl) ⟨1709999, by rfl⟩ : syracuseStep 2279999 = 3419999) B3419999
theorem B243329629 : Blo 1421530 243329629 := bstep (se 3 (by rfl) ⟨45624305, by rfl⟩ : syracuseStep 243329629 = 91248611) B91248611
theorem B24644195 : Blo 1421530 24644195 := bstep (se 1 (by rfl) ⟨18483146, by rfl⟩ : syracuseStep 24644195 = 36966293) B36966293
theorem B2132663 : Blo 1421530 2132663 := bstep (se 1 (by rfl) ⟨1599497, by rfl⟩ : syracuseStep 2132663 = 3198995) B3198995
theorem B13675229 : Blo 1421530 13675229 := bstep (se 3 (by rfl) ⟨2564105, by rfl⟩ : syracuseStep 13675229 = 5128211) B5128211
theorem B1600303 : Blo 1421530 1600303 := bstep (se 1 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 1600303 = 2400455) B2400455
theorem B6073231 : Blo 1421530 6073231 := bstep (se 1 (by rfl) ⟨4554923, by rfl⟩ : syracuseStep 6073231 = 9109847) B9109847
theorem B2132891 : Blo 1421530 2132891 := bstep (se 1 (by rfl) ⟨1599668, by rfl⟩ : syracuseStep 2132891 = 3199337) B3199337
theorem B1600411 : Blo 1421530 1600411 := bstep (se 1 (by rfl) ⟨1200308, by rfl⟩ : syracuseStep 1600411 = 2400617) B2400617
theorem B3599275 : Blo 1421530 3599275 := bstep (se 1 (by rfl) ⟨2699456, by rfl⟩ : syracuseStep 3599275 = 5398913) B5398913
theorem B4803623 : Blo 1421530 4803623 := bstep (se 1 (by rfl) ⟨3602717, by rfl⟩ : syracuseStep 4803623 = 7205435) B7205435
theorem B3599579 : Blo 1421530 3599579 := bstep (se 1 (by rfl) ⟨2699684, by rfl⟩ : syracuseStep 3599579 = 5399369) B5399369
theorem B2133287 : Blo 1421530 2133287 := bstep (se 1 (by rfl) ⟨1599965, by rfl⟩ : syracuseStep 2133287 = 3199931) B3199931
theorem B1600807 : Blo 1421530 1600807 := bstep (se 1 (by rfl) ⟨1200605, by rfl⟩ : syracuseStep 1600807 = 2401211) B2401211
theorem B3599711 : Blo 1421530 3599711 := bstep (se 1 (by rfl) ⟨2699783, by rfl⟩ : syracuseStep 3599711 = 5399567) B5399567
theorem B1600879 : Blo 1421530 1600879 := bstep (se 1 (by rfl) ⟨1200659, by rfl⟩ : syracuseStep 1600879 = 2401319) B2401319
theorem B2133371 : Blo 1421530 2133371 := bstep (se 1 (by rfl) ⟨1600028, by rfl⟩ : syracuseStep 2133371 = 3200057) B3200057
theorem B4804055 : Blo 1421530 4804055 := bstep (se 1 (by rfl) ⟨3603041, by rfl⟩ : syracuseStep 4804055 = 7206083) B7206083
theorem B2133497 : Blo 1421530 2133497 := bstep (se 2 (by rfl) ⟨800061, by rfl⟩ : syracuseStep 2133497 = 1600123) B1600123
theorem B1601095 : Blo 1421530 1601095 := bstep (se 1 (by rfl) ⟨1200821, by rfl⟩ : syracuseStep 1601095 = 2401643) B2401643
theorem B2133599 : Blo 1421530 2133599 := bstep (se 1 (by rfl) ⟨1600199, by rfl⟩ : syracuseStep 2133599 = 3200399) B3200399
theorem B6074119 : Blo 1421530 6074119 := bstep (se 1 (by rfl) ⟨4555589, by rfl⟩ : syracuseStep 6074119 = 9111179) B9111179
theorem B3198761 : Blo 1421530 3198761 := bstep (se 2 (by rfl) ⟨1199535, by rfl⟩ : syracuseStep 3198761 = 2399071) B2399071
theorem B2133815 : Blo 1421530 2133815 := bstep (se 1 (by rfl) ⟨1600361, by rfl⟩ : syracuseStep 2133815 = 3200723) B3200723
theorem B5402497 : Blo 1421530 5402497 := bstep (se 2 (by rfl) ⟨2025936, by rfl⟩ : syracuseStep 5402497 = 4051873) B4051873
theorem B3600409 : Blo 1421530 3600409 := bstep (se 2 (by rfl) ⟨1350153, by rfl⟩ : syracuseStep 3600409 = 2700307) B2700307
theorem B103886873 : Blo 1421530 103886873 := bstep (se 2 (by rfl) ⟨38957577, by rfl⟩ : syracuseStep 103886873 = 77915155) B77915155
theorem B5066857 : Blo 1421530 5066857 := bstep (se 2 (by rfl) ⟨1900071, by rfl⟩ : syracuseStep 5066857 = 3800143) B3800143
theorem B7688297 : Blo 1421530 7688297 := bstep (se 2 (by rfl) ⟨2883111, by rfl⟩ : syracuseStep 7688297 = 5766223) B5766223
theorem B2134121 : Blo 1421530 2134121 := bstep (se 2 (by rfl) ⟨800295, by rfl⟩ : syracuseStep 2134121 = 1600591) B1600591
theorem B16199837 : Blo 1421530 16199837 := bstep (se 3 (by rfl) ⟨3037469, by rfl⟩ : syracuseStep 16199837 = 6074939) B6074939
theorem B1421599 : Blo 1421530 1421599 := bstep (se 1 (by rfl) ⟨1066199, by rfl⟩ : syracuseStep 1421599 = 2132399) B2132399
theorem B3600713 : Blo 1421530 3600713 := bstep (se 2 (by rfl) ⟨1350267, by rfl⟩ : syracuseStep 3600713 = 2700535) B2700535
theorem B1421659 : Blo 1421530 1421659 := bstep (se 1 (by rfl) ⟨1066244, by rfl⟩ : syracuseStep 1421659 = 2132489) B2132489
theorem B1421679 : Blo 1421530 1421679 := bstep (se 1 (by rfl) ⟨1066259, by rfl⟩ : syracuseStep 1421679 = 2132519) B2132519
theorem B1421735 : Blo 1421530 1421735 := bstep (se 1 (by rfl) ⟨1066301, by rfl⟩ : syracuseStep 1421735 = 2132603) B2132603
theorem B2134439 : Blo 1421530 2134439 := bstep (se 1 (by rfl) ⟨1600829, by rfl⟩ : syracuseStep 2134439 = 3201659) B3201659
theorem B1421819 : Blo 1421530 1421819 := bstep (se 1 (by rfl) ⟨1066364, by rfl⟩ : syracuseStep 1421819 = 2132729) B2132729
theorem B2134523 : Blo 1421530 2134523 := bstep (se 1 (by rfl) ⟨1600892, by rfl⟩ : syracuseStep 2134523 = 3201785) B3201785
theorem B1421887 : Blo 1421530 1421887 := bstep (se 1 (by rfl) ⟨1066415, by rfl⟩ : syracuseStep 1421887 = 2132831) B2132831
theorem B1421895 : Blo 1421530 1421895 := bstep (se 1 (by rfl) ⟨1066421, by rfl⟩ : syracuseStep 1421895 = 2132843) B2132843
theorem B15381089 : Blo 1421530 15381089 := bstep (se 2 (by rfl) ⟨5767908, by rfl⟩ : syracuseStep 15381089 = 11535817) B11535817
theorem B5403257 : Blo 1421530 5403257 := bstep (se 2 (by rfl) ⟨2026221, by rfl⟩ : syracuseStep 5403257 = 4052443) B4052443
theorem B2134649 : Blo 1421530 2134649 := bstep (se 2 (by rfl) ⟨800493, by rfl⟩ : syracuseStep 2134649 = 1600987) B1600987
theorem B2134703 : Blo 1421530 2134703 := bstep (se 1 (by rfl) ⟨1601027, by rfl⟩ : syracuseStep 2134703 = 3202055) B3202055
theorem B10392263 : Blo 1421530 10392263 := bstep (se 1 (by rfl) ⟨7794197, by rfl⟩ : syracuseStep 10392263 = 15588395) B15588395
theorem B1422047 : Blo 1421530 1422047 := bstep (se 1 (by rfl) ⟨1066535, by rfl⟩ : syracuseStep 1422047 = 2133071) B2133071
theorem B2134751 : Blo 1421530 2134751 := bstep (se 1 (by rfl) ⟨1601063, by rfl⟩ : syracuseStep 2134751 = 3202127) B3202127
theorem B58422059 : Blo 1421530 58422059 := bstep (se 1 (by rfl) ⟨43816544, by rfl⟩ : syracuseStep 58422059 = 87633089) B87633089
theorem B1422127 : Blo 1421530 1422127 := bstep (se 1 (by rfl) ⟨1066595, by rfl⟩ : syracuseStep 1422127 = 2133191) B2133191
theorem B3199823 : Blo 1421530 3199823 := bstep (se 1 (by rfl) ⟨2399867, by rfl⟩ : syracuseStep 3199823 = 4799735) B4799735
theorem B10253135 : Blo 1421530 10253135 := bstep (se 1 (by rfl) ⟨7689851, by rfl⟩ : syracuseStep 10253135 = 15379703) B15379703
theorem B13669229 : Blo 1421530 13669229 := bstep (se 3 (by rfl) ⟨2562980, by rfl⟩ : syracuseStep 13669229 = 5125961) B5125961
theorem B1422235 : Blo 1421530 1422235 := bstep (se 1 (by rfl) ⟨1066676, by rfl⟩ : syracuseStep 1422235 = 2133353) B2133353
theorem B3847067 : Blo 1421530 3847067 := bstep (se 1 (by rfl) ⟨2885300, by rfl⟩ : syracuseStep 3847067 = 5770601) B5770601
theorem B1422287 : Blo 1421530 1422287 := bstep (se 1 (by rfl) ⟨1066715, by rfl⟩ : syracuseStep 1422287 = 2133431) B2133431
theorem B7197659 : Blo 1421530 7197659 := bstep (se 1 (by rfl) ⟨5398244, by rfl⟩ : syracuseStep 7197659 = 10796489) B10796489
theorem B1422311 : Blo 1421530 1422311 := bstep (se 1 (by rfl) ⟨1066733, by rfl⟩ : syracuseStep 1422311 = 2133467) B2133467
theorem B2135015 : Blo 1421530 2135015 := bstep (se 1 (by rfl) ⟨1601261, by rfl⟩ : syracuseStep 2135015 = 3202523) B3202523
theorem B3200039 : Blo 1421530 3200039 := bstep (se 1 (by rfl) ⟨2400029, by rfl⟩ : syracuseStep 3200039 = 4800059) B4800059
theorem B7197821 : Blo 1421530 7197821 := bstep (se 3 (by rfl) ⟨1349591, by rfl⟩ : syracuseStep 7197821 = 2699183) B2699183
theorem B5403773 : Blo 1421530 5403773 := bstep (se 3 (by rfl) ⟨1013207, by rfl⟩ : syracuseStep 5403773 = 2026415) B2026415
theorem B21083261 : Blo 1421530 21083261 := bstep (se 3 (by rfl) ⟨3953111, by rfl⟩ : syracuseStep 21083261 = 7906223) B7906223
theorem B10802321 : Blo 1421530 10802321 := bstep (se 2 (by rfl) ⟨4050870, by rfl⟩ : syracuseStep 10802321 = 8101741) B8101741
theorem B6075607 : Blo 1421530 6075607 := bstep (se 1 (by rfl) ⟨4556705, by rfl⟩ : syracuseStep 6075607 = 9113411) B9113411
theorem B3200219 : Blo 1421530 3200219 := bstep (se 1 (by rfl) ⟨2400164, by rfl⟩ : syracuseStep 3200219 = 4800329) B4800329
theorem B2135273 : Blo 1421530 2135273 := bstep (se 2 (by rfl) ⟨800727, by rfl⟩ : syracuseStep 2135273 = 1601455) B1601455
theorem B4797683 : Blo 1421530 4797683 := bstep (se 1 (by rfl) ⟨3598262, by rfl⟩ : syracuseStep 4797683 = 7196525) B7196525
theorem B1422623 : Blo 1421530 1422623 := bstep (se 1 (by rfl) ⟨1066967, by rfl⟩ : syracuseStep 1422623 = 2133935) B2133935
theorem B1422683 : Blo 1421530 1422683 := bstep (se 1 (by rfl) ⟨1067012, by rfl⟩ : syracuseStep 1422683 = 2134025) B2134025
theorem B4797791 : Blo 1421530 4797791 := bstep (se 1 (by rfl) ⟨3598343, by rfl⟩ : syracuseStep 4797791 = 7196687) B7196687
theorem B2700641 : Blo 1421530 2700641 := bstep (se 2 (by rfl) ⟨1012740, by rfl⟩ : syracuseStep 2700641 = 2025481) B2025481
theorem B1422703 : Blo 1421530 1422703 := bstep (se 1 (by rfl) ⟨1067027, by rfl⟩ : syracuseStep 1422703 = 2134055) B2134055
theorem B3200417 : Blo 1421530 3200417 := bstep (se 2 (by rfl) ⟨1200156, by rfl⟩ : syracuseStep 3200417 = 2400313) B2400313
theorem B1824167 : Blo 1421530 1824167 := bstep (se 1 (by rfl) ⟨1368125, by rfl⟩ : syracuseStep 1824167 = 2736251) B2736251
theorem B1422759 : Blo 1421530 1422759 := bstep (se 1 (by rfl) ⟨1067069, by rfl⟩ : syracuseStep 1422759 = 2134139) B2134139
theorem B7198145 : Blo 1421530 7198145 := bstep (se 2 (by rfl) ⟨2699304, by rfl⟩ : syracuseStep 7198145 = 5398609) B5398609
theorem B18216413 : Blo 1421530 18216413 := bstep (se 3 (by rfl) ⟨3415577, by rfl⟩ : syracuseStep 18216413 = 6831155) B6831155
theorem B2700793 : Blo 1421530 2700793 := bstep (se 2 (by rfl) ⟨1012797, by rfl⟩ : syracuseStep 2700793 = 2025595) B2025595
theorem B1422843 : Blo 1421530 1422843 := bstep (se 1 (by rfl) ⟨1067132, by rfl⟩ : syracuseStep 1422843 = 2134265) B2134265
theorem B7206407 : Blo 1421530 7206407 := bstep (se 1 (by rfl) ⟨5404805, by rfl⟩ : syracuseStep 7206407 = 10809611) B10809611
theorem B1422911 : Blo 1421530 1422911 := bstep (se 1 (by rfl) ⟨1067183, by rfl⟩ : syracuseStep 1422911 = 2134367) B2134367
theorem B1521223 : Blo 1421530 1521223 := bstep (se 1 (by rfl) ⟨1140917, by rfl⟩ : syracuseStep 1521223 = 2281835) B2281835
theorem B1422919 : Blo 1421530 1422919 := bstep (se 1 (by rfl) ⟨1067189, by rfl⟩ : syracuseStep 1422919 = 2134379) B2134379
theorem B1423071 : Blo 1421530 1423071 := bstep (se 1 (by rfl) ⟨1067303, by rfl⟩ : syracuseStep 1423071 = 2134607) B2134607
theorem B2701097 : Blo 1421530 2701097 := bstep (se 2 (by rfl) ⟨1012911, by rfl⟩ : syracuseStep 2701097 = 2025823) B2025823
theorem B3462959 : Blo 1421530 3462959 := bstep (se 1 (by rfl) ⟨2597219, by rfl⟩ : syracuseStep 3462959 = 5194439) B5194439
theorem B1423151 : Blo 1421530 1423151 := bstep (se 1 (by rfl) ⟨1067363, by rfl⟩ : syracuseStep 1423151 = 2134727) B2134727
theorem B46126907 : Blo 1421530 46126907 := bstep (se 1 (by rfl) ⟨34595180, by rfl⟩ : syracuseStep 46126907 = 69190361) B69190361
theorem B1423259 : Blo 1421530 1423259 := bstep (se 1 (by rfl) ⟨1067444, by rfl⟩ : syracuseStep 1423259 = 2134889) B2134889
theorem B3200975 : Blo 1421530 3200975 := bstep (se 1 (by rfl) ⟨2400731, by rfl⟩ : syracuseStep 3200975 = 4801463) B4801463
theorem B1423311 : Blo 1421530 1423311 := bstep (se 1 (by rfl) ⟨1067483, by rfl⟩ : syracuseStep 1423311 = 2134967) B2134967
theorem B1423335 : Blo 1421530 1423335 := bstep (se 1 (by rfl) ⟨1067501, by rfl⟩ : syracuseStep 1423335 = 2135003) B2135003
theorem B9115895 : Blo 1421530 9115895 := bstep (se 1 (by rfl) ⟨6836921, by rfl⟩ : syracuseStep 9115895 = 13673843) B13673843
theorem B3201353 : Blo 1421530 3201353 := bstep (se 2 (by rfl) ⟨1200507, by rfl⟩ : syracuseStep 3201353 = 2401015) B2401015
theorem B3201371 : Blo 1421530 3201371 := bstep (se 1 (by rfl) ⟨2401028, by rfl⟩ : syracuseStep 3201371 = 4802057) B4802057
theorem B1800559 : Blo 1421530 1800559 := bstep (se 1 (by rfl) ⟨1350419, by rfl⟩ : syracuseStep 1800559 = 2700839) B2700839
theorem B7690825 : Blo 1421530 7690825 := bstep (se 2 (by rfl) ⟨2884059, by rfl⟩ : syracuseStep 7690825 = 5768119) B5768119
theorem B2398943 : Blo 1421530 2398943 := bstep (se 1 (by rfl) ⟨1799207, by rfl⟩ : syracuseStep 2398943 = 3598415) B3598415
theorem B20798209 : Blo 1421530 20798209 := bstep (se 2 (by rfl) ⟨7799328, by rfl⟩ : syracuseStep 20798209 = 15598657) B15598657
theorem B2702099 : Blo 1421530 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B4799357 : Blo 1421530 4799357 := bstep (se 3 (by rfl) ⟨899879, by rfl⟩ : syracuseStep 4799357 = 1799759) B1799759
theorem B16423823 : Blo 1421530 16423823 := bstep (se 1 (by rfl) ⟨12317867, by rfl⟩ : syracuseStep 16423823 = 24635735) B24635735
theorem B3201947 : Blo 1421530 3201947 := bstep (se 1 (by rfl) ⟨2401460, by rfl⟩ : syracuseStep 3201947 = 4802921) B4802921
theorem B2702251 : Blo 1421530 2702251 := bstep (se 1 (by rfl) ⟨2026688, by rfl⟩ : syracuseStep 2702251 = 4053377) B4053377
theorem B9862073 : Blo 1421530 9862073 := bstep (se 2 (by rfl) ⟨3698277, by rfl⟩ : syracuseStep 9862073 = 7396555) B7396555
theorem B3202145 : Blo 1421530 3202145 := bstep (se 2 (by rfl) ⟨1200804, by rfl⟩ : syracuseStep 3202145 = 2401609) B2401609
theorem B4799627 : Blo 1421530 4799627 := bstep (se 1 (by rfl) ⟨3599720, by rfl⟩ : syracuseStep 4799627 = 7199441) B7199441
theorem B2399375 : Blo 1421530 2399375 := bstep (se 1 (by rfl) ⟨1799531, by rfl⟩ : syracuseStep 2399375 = 3599063) B3599063
theorem B2702479 : Blo 1421530 2702479 := bstep (se 1 (by rfl) ⟨2026859, by rfl⟩ : syracuseStep 2702479 = 4053719) B4053719
theorem B1801435 : Blo 1421530 1801435 := bstep (se 1 (by rfl) ⟨1351076, by rfl⟩ : syracuseStep 1801435 = 2702153) B2702153
theorem B9739531 : Blo 1421530 9739531 := bstep (se 1 (by rfl) ⟨7304648, by rfl⟩ : syracuseStep 9739531 = 14609297) B14609297
theorem B3333415 : Blo 1421530 3333415 := bstep (se 1 (by rfl) ⟨2500061, by rfl⟩ : syracuseStep 3333415 = 5000123) B5000123
theorem B3202343 : Blo 1421530 3202343 := bstep (se 1 (by rfl) ⟨2401757, by rfl⟩ : syracuseStep 3202343 = 4803515) B4803515
theorem B2399611 : Blo 1421530 2399611 := bstep (se 1 (by rfl) ⟨1799708, by rfl⟩ : syracuseStep 2399611 = 3599417) B3599417
theorem B10804751 : Blo 1421530 10804751 := bstep (se 1 (by rfl) ⟨8103563, by rfl⟩ : syracuseStep 10804751 = 16207127) B16207127
theorem B12156439 : Blo 1421530 12156439 := bstep (se 1 (by rfl) ⟨9117329, by rfl⟩ : syracuseStep 12156439 = 18234659) B18234659
theorem B7691885 : Blo 1421530 7691885 := bstep (se 3 (by rfl) ⟨1442228, by rfl⟩ : syracuseStep 7691885 = 2884457) B2884457
theorem B2563745 : Blo 1421530 2563745 := bstep (se 2 (by rfl) ⟨961404, by rfl⟩ : syracuseStep 2563745 = 1922809) B1922809
theorem B3202721 : Blo 1421530 3202721 := bstep (se 2 (by rfl) ⟨1201020, by rfl⟩ : syracuseStep 3202721 = 2402041) B2402041
theorem B4865771 : Blo 1421530 4865771 := bstep (se 1 (by rfl) ⟨3649328, by rfl⟩ : syracuseStep 4865771 = 7298657) B7298657
theorem B7790339 : Blo 1421530 7790339 := bstep (se 1 (by rfl) ⟨5842754, by rfl⟩ : syracuseStep 7790339 = 11685509) B11685509
theorem B12156713 : Blo 1421530 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B12975967 : Blo 1421530 12975967 := bstep (se 1 (by rfl) ⟨9731975, by rfl⟩ : syracuseStep 12975967 = 19463951) B19463951
theorem B6832001 : Blo 1421530 6832001 := bstep (se 2 (by rfl) ⟨2562000, by rfl⟩ : syracuseStep 6832001 = 5124001) B5124001
theorem B10796975 : Blo 1421530 10796975 := bstep (se 1 (by rfl) ⟨8097731, by rfl⟩ : syracuseStep 10796975 = 16195463) B16195463
theorem B4800545 : Blo 1421530 4800545 := bstep (se 2 (by rfl) ⟨1800204, by rfl⟩ : syracuseStep 4800545 = 3600409) B3600409
theorem B2400475 : Blo 1421530 2400475 := bstep (se 1 (by rfl) ⟨1800356, by rfl⟩ : syracuseStep 2400475 = 3600713) B3600713
theorem B56222029 : Blo 1421530 56222029 := bstep (se 3 (by rfl) ⟨10541630, by rfl⟩ : syracuseStep 56222029 = 21083261) B21083261
theorem B2400745 : Blo 1421530 2400745 := bstep (se 2 (by rfl) ⟨900279, by rfl⟩ : syracuseStep 2400745 = 1800559) B1800559
theorem B2564711 : Blo 1421530 2564711 := bstep (se 1 (by rfl) ⟨1923533, by rfl⟩ : syracuseStep 2564711 = 3847067) B3847067
theorem B7201547 : Blo 1421530 7201547 := bstep (se 1 (by rfl) ⟨5401160, by rfl⟩ : syracuseStep 7201547 = 10802321) B10802321
theorem B7201709 : Blo 1421530 7201709 := bstep (se 3 (by rfl) ⟨1350320, by rfl⟩ : syracuseStep 7201709 = 2700641) B2700641
theorem B27730945 : Blo 1421530 27730945 := bstep (se 2 (by rfl) ⟨10399104, by rfl⟩ : syracuseStep 27730945 = 20798209) B20798209
theorem B4048343 : Blo 1421530 4048343 := bstep (se 1 (by rfl) ⟨3036257, by rfl⟩ : syracuseStep 4048343 = 6072515) B6072515
theorem B12158423 : Blo 1421530 12158423 := bstep (se 1 (by rfl) ⟨9118817, by rfl⟩ : syracuseStep 12158423 = 18237635) B18237635
theorem B6079997 : Blo 1421530 6079997 := bstep (se 3 (by rfl) ⟨1139999, by rfl⟩ : syracuseStep 6079997 = 2279999) B2279999
theorem B2401913 : Blo 1421530 2401913 := bstep (se 2 (by rfl) ⟨900717, by rfl⟩ : syracuseStep 2401913 = 1801435) B1801435
theorem B3245735 : Blo 1421530 3245735 := bstep (se 1 (by rfl) ⟨2434301, by rfl⟩ : syracuseStep 3245735 = 4868603) B4868603
theorem B12986041 : Blo 1421530 12986041 := bstep (se 2 (by rfl) ⟨4869765, by rfl⟩ : syracuseStep 12986041 = 9739531) B9739531
theorem B1599295 : Blo 1421530 1599295 := bstep (se 1 (by rfl) ⟨1199471, by rfl⟩ : syracuseStep 1599295 = 2398943) B2398943
theorem B1599583 : Blo 1421530 1599583 := bstep (se 1 (by rfl) ⟨1199687, by rfl⟩ : syracuseStep 1599583 = 2399375) B2399375
theorem B9234557 : Blo 1421530 9234557 := bstep (se 3 (by rfl) ⟨1731479, by rfl⟩ : syracuseStep 9234557 = 3462959) B3462959
theorem B7203167 : Blo 1421530 7203167 := bstep (se 1 (by rfl) ⟨5402375, by rfl⟩ : syracuseStep 7203167 = 10804751) B10804751
theorem B18221537 : Blo 1421530 18221537 := bstep (se 2 (by rfl) ⟨6833076, by rfl⟩ : syracuseStep 18221537 = 13666153) B13666153
theorem B7203329 : Blo 1421530 7203329 := bstep (se 2 (by rfl) ⟨2701248, by rfl⟩ : syracuseStep 7203329 = 5402497) B5402497
theorem B2132507 : Blo 1421530 2132507 := bstep (se 1 (by rfl) ⟨1599380, by rfl⟩ : syracuseStep 2132507 = 3198761) B3198761
theorem B8104475 : Blo 1421530 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B2132585 : Blo 1421530 2132585 := bstep (se 2 (by rfl) ⟨799719, by rfl⟩ : syracuseStep 2132585 = 1599439) B1599439
theorem B69257915 : Blo 1421530 69257915 := bstep (se 1 (by rfl) ⟨51943436, by rfl⟩ : syracuseStep 69257915 = 103886873) B103886873
theorem B10799891 : Blo 1421530 10799891 := bstep (se 1 (by rfl) ⟨8099918, by rfl⟩ : syracuseStep 10799891 = 16199837) B16199837
theorem B2133113 : Blo 1421530 2133113 := bstep (se 2 (by rfl) ⟨799917, by rfl⟩ : syracuseStep 2133113 = 1599835) B1599835
theorem B15379577 : Blo 1421530 15379577 := bstep (se 2 (by rfl) ⟨5767341, by rfl⟩ : syracuseStep 15379577 = 11534683) B11534683
theorem B38948039 : Blo 1421530 38948039 := bstep (se 1 (by rfl) ⟨29211029, by rfl⟩ : syracuseStep 38948039 = 58422059) B58422059
theorem B2133215 : Blo 1421530 2133215 := bstep (se 1 (by rfl) ⟨1599911, by rfl⟩ : syracuseStep 2133215 = 3199823) B3199823
theorem B6835423 : Blo 1421530 6835423 := bstep (se 1 (by rfl) ⟨5126567, by rfl⟩ : syracuseStep 6835423 = 10253135) B10253135
theorem B1600735 : Blo 1421530 1600735 := bstep (se 1 (by rfl) ⟨1200551, by rfl⟩ : syracuseStep 1600735 = 2401103) B2401103
theorem B9112819 : Blo 1421530 9112819 := bstep (se 1 (by rfl) ⟨6834614, by rfl⟩ : syracuseStep 9112819 = 13669229) B13669229
theorem B2133257 : Blo 1421530 2133257 := bstep (se 2 (by rfl) ⟨799971, by rfl⟩ : syracuseStep 2133257 = 1599943) B1599943
theorem B7204139 : Blo 1421530 7204139 := bstep (se 1 (by rfl) ⟨5403104, by rfl⟩ : syracuseStep 7204139 = 10806209) B10806209
theorem B2133359 : Blo 1421530 2133359 := bstep (se 1 (by rfl) ⟨1600019, by rfl⟩ : syracuseStep 2133359 = 3200039) B3200039
theorem B324439505 : Blo 1421530 324439505 := bstep (se 2 (by rfl) ⟨121664814, by rfl⟩ : syracuseStep 324439505 = 243329629) B243329629
theorem B2133479 : Blo 1421530 2133479 := bstep (se 1 (by rfl) ⟨1600109, by rfl⟩ : syracuseStep 2133479 = 3200219) B3200219
theorem B3198455 : Blo 1421530 3198455 := bstep (se 1 (by rfl) ⟨2398841, by rfl⟩ : syracuseStep 3198455 = 4797683) B4797683
theorem B3198527 : Blo 1421530 3198527 := bstep (se 1 (by rfl) ⟨2398895, by rfl⟩ : syracuseStep 3198527 = 4797791) B4797791
theorem B2133611 : Blo 1421530 2133611 := bstep (se 1 (by rfl) ⟨1600208, by rfl⟩ : syracuseStep 2133611 = 3200417) B3200417
theorem B12144275 : Blo 1421530 12144275 := bstep (se 1 (by rfl) ⟨9108206, by rfl⟩ : syracuseStep 12144275 = 18216413) B18216413
theorem B4804271 : Blo 1421530 4804271 := bstep (se 1 (by rfl) ⟨3603203, by rfl⟩ : syracuseStep 4804271 = 7206407) B7206407
theorem B2133737 : Blo 1421530 2133737 := bstep (se 2 (by rfl) ⟨800151, by rfl⟩ : syracuseStep 2133737 = 1600303) B1600303
theorem B8097641 : Blo 1421530 8097641 := bstep (se 2 (by rfl) ⟨3036615, by rfl⟩ : syracuseStep 8097641 = 6073231) B6073231
theorem B2133881 : Blo 1421530 2133881 := bstep (se 2 (by rfl) ⟨800205, by rfl⟩ : syracuseStep 2133881 = 1600411) B1600411
theorem B2133983 : Blo 1421530 2133983 := bstep (se 1 (by rfl) ⟨1600487, by rfl⟩ : syracuseStep 2133983 = 3200975) B3200975
theorem B92287025 : Blo 1421530 92287025 := bstep (se 2 (by rfl) ⟨34607634, by rfl⟩ : syracuseStep 92287025 = 69215269) B69215269
theorem B32452757 : Blo 1421530 32452757 := bstep (se 6 (by rfl) ⟨760611, by rfl⟩ : syracuseStep 32452757 = 1521223) B1521223
theorem B3600571 : Blo 1421530 3600571 := bstep (se 1 (by rfl) ⟨2700428, by rfl⟩ : syracuseStep 3600571 = 5400857) B5400857
theorem B2134235 : Blo 1421530 2134235 := bstep (se 1 (by rfl) ⟨1600676, by rfl⟩ : syracuseStep 2134235 = 3201353) B3201353
theorem B1421543 : Blo 1421530 1421543 := bstep (se 1 (by rfl) ⟨1066157, by rfl⟩ : syracuseStep 1421543 = 2132315) B2132315
theorem B2134247 : Blo 1421530 2134247 := bstep (se 1 (by rfl) ⟨1600685, by rfl⟩ : syracuseStep 2134247 = 3201371) B3201371
theorem B1421695 : Blo 1421530 1421695 := bstep (se 1 (by rfl) ⟨1066271, by rfl⟩ : syracuseStep 1421695 = 2132543) B2132543
theorem B4444553 : Blo 1421530 4444553 := bstep (se 2 (by rfl) ⟨1666707, by rfl⟩ : syracuseStep 4444553 = 3333415) B3333415
theorem B2134409 : Blo 1421530 2134409 := bstep (se 2 (by rfl) ⟨800403, by rfl⟩ : syracuseStep 2134409 = 1600807) B1600807
theorem B16429463 : Blo 1421530 16429463 := bstep (se 1 (by rfl) ⟨12322097, by rfl⟩ : syracuseStep 16429463 = 24644195) B24644195
theorem B6836653 : Blo 1421530 6836653 := bstep (se 3 (by rfl) ⟨1281872, by rfl⟩ : syracuseStep 6836653 = 2563745) B2563745
theorem B1421775 : Blo 1421530 1421775 := bstep (se 1 (by rfl) ⟨1066331, by rfl⟩ : syracuseStep 1421775 = 2132663) B2132663
theorem B2134505 : Blo 1421530 2134505 := bstep (se 2 (by rfl) ⟨800439, by rfl⟩ : syracuseStep 2134505 = 1600879) B1600879
theorem B3199481 : Blo 1421530 3199481 := bstep (se 2 (by rfl) ⟨1199805, by rfl⟩ : syracuseStep 3199481 = 2399611) B2399611
theorem B3199571 : Blo 1421530 3199571 := bstep (se 1 (by rfl) ⟨2399678, by rfl⟩ : syracuseStep 3199571 = 4799357) B4799357
theorem B10949215 : Blo 1421530 10949215 := bstep (se 1 (by rfl) ⟨8211911, by rfl⟩ : syracuseStep 10949215 = 16423823) B16423823
theorem B1421927 : Blo 1421530 1421927 := bstep (se 1 (by rfl) ⟨1066445, by rfl⟩ : syracuseStep 1421927 = 2132891) B2132891
theorem B2134631 : Blo 1421530 2134631 := bstep (se 1 (by rfl) ⟨1600973, by rfl⟩ : syracuseStep 2134631 = 3201947) B3201947
theorem B6574715 : Blo 1421530 6574715 := bstep (se 1 (by rfl) ⟨4931036, by rfl⟩ : syracuseStep 6574715 = 9862073) B9862073
theorem B8106641 : Blo 1421530 8106641 := bstep (se 2 (by rfl) ⟨3039990, by rfl⟩ : syracuseStep 8106641 = 6079981) B6079981
theorem B3601057 : Blo 1421530 3601057 := bstep (se 2 (by rfl) ⟨1350396, by rfl⟩ : syracuseStep 3601057 = 2700793) B2700793
theorem B16208585 : Blo 1421530 16208585 := bstep (se 2 (by rfl) ⟨6078219, by rfl⟩ : syracuseStep 16208585 = 12156439) B12156439
theorem B7205597 : Blo 1421530 7205597 := bstep (se 3 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 7205597 = 2702099) B2702099
theorem B2134763 : Blo 1421530 2134763 := bstep (se 1 (by rfl) ⟨1601072, by rfl⟩ : syracuseStep 2134763 = 3202145) B3202145
theorem B3199751 : Blo 1421530 3199751 := bstep (se 1 (by rfl) ⟨2399813, by rfl⟩ : syracuseStep 3199751 = 4799627) B4799627
theorem B2134793 : Blo 1421530 2134793 := bstep (se 2 (by rfl) ⟨800547, by rfl⟩ : syracuseStep 2134793 = 1601095) B1601095
theorem B1422191 : Blo 1421530 1422191 := bstep (se 1 (by rfl) ⟨1066643, by rfl⟩ : syracuseStep 1422191 = 2133287) B2133287
theorem B2134895 : Blo 1421530 2134895 := bstep (se 1 (by rfl) ⟨1601171, by rfl⟩ : syracuseStep 2134895 = 3202343) B3202343
theorem B1422247 : Blo 1421530 1422247 := bstep (se 1 (by rfl) ⟨1066685, by rfl⟩ : syracuseStep 1422247 = 2133371) B2133371
theorem B1422331 : Blo 1421530 1422331 := bstep (se 1 (by rfl) ⟨1066748, by rfl⟩ : syracuseStep 1422331 = 2133497) B2133497
theorem B8098825 : Blo 1421530 8098825 := bstep (se 2 (by rfl) ⟨3037059, by rfl⟩ : syracuseStep 8098825 = 6074119) B6074119
theorem B1422399 : Blo 1421530 1422399 := bstep (se 1 (by rfl) ⟨1066799, by rfl⟩ : syracuseStep 1422399 = 2133599) B2133599
theorem B2135147 : Blo 1421530 2135147 := bstep (se 1 (by rfl) ⟨1601360, by rfl⟩ : syracuseStep 2135147 = 3202721) B3202721
theorem B1422543 : Blo 1421530 1422543 := bstep (se 1 (by rfl) ⟨1066907, by rfl⟩ : syracuseStep 1422543 = 2133815) B2133815
theorem B7197983 : Blo 1421530 7197983 := bstep (se 1 (by rfl) ⟨5398487, by rfl⟩ : syracuseStep 7197983 = 10796975) B10796975
theorem B5125531 : Blo 1421530 5125531 := bstep (se 1 (by rfl) ⟨3844148, by rfl⟩ : syracuseStep 5125531 = 7688297) B7688297
theorem B1422747 : Blo 1421530 1422747 := bstep (se 1 (by rfl) ⟨1067060, by rfl⟩ : syracuseStep 1422747 = 2134121) B2134121
theorem B6755809 : Blo 1421530 6755809 := bstep (se 2 (by rfl) ⟨2533428, by rfl⟩ : syracuseStep 6755809 = 5066857) B5066857
theorem B4797953 : Blo 1421530 4797953 := bstep (se 2 (by rfl) ⟨1799232, by rfl⟩ : syracuseStep 4797953 = 3598465) B3598465
theorem B1422959 : Blo 1421530 1422959 := bstep (se 1 (by rfl) ⟨1067219, by rfl⟩ : syracuseStep 1422959 = 2134439) B2134439
theorem B1423015 : Blo 1421530 1423015 := bstep (se 1 (by rfl) ⟨1067261, by rfl⟩ : syracuseStep 1423015 = 2134523) B2134523
theorem B10254059 : Blo 1421530 10254059 := bstep (se 1 (by rfl) ⟨7690544, by rfl⟩ : syracuseStep 10254059 = 15381089) B15381089
theorem B3602171 : Blo 1421530 3602171 := bstep (se 1 (by rfl) ⟨2701628, by rfl⟩ : syracuseStep 3602171 = 5403257) B5403257
theorem B1423099 : Blo 1421530 1423099 := bstep (se 1 (by rfl) ⟨1067324, by rfl⟩ : syracuseStep 1423099 = 2134649) B2134649
theorem B1423135 : Blo 1421530 1423135 := bstep (se 1 (by rfl) ⟨1067351, by rfl⟩ : syracuseStep 1423135 = 2134703) B2134703
theorem B6928175 : Blo 1421530 6928175 := bstep (se 1 (by rfl) ⟨5196131, by rfl⟩ : syracuseStep 6928175 = 10392263) B10392263
theorem B3200831 : Blo 1421530 3200831 := bstep (se 1 (by rfl) ⟨2400623, by rfl⟩ : syracuseStep 3200831 = 4801247) B4801247
theorem B1423167 : Blo 1421530 1423167 := bstep (se 1 (by rfl) ⟨1067375, by rfl⟩ : syracuseStep 1423167 = 2134751) B2134751
theorem B4798439 : Blo 1421530 4798439 := bstep (se 1 (by rfl) ⟨3598829, by rfl⟩ : syracuseStep 4798439 = 7197659) B7197659
theorem B1423343 : Blo 1421530 1423343 := bstep (se 1 (by rfl) ⟨1067507, by rfl⟩ : syracuseStep 1423343 = 2135015) B2135015
theorem B4798547 : Blo 1421530 4798547 := bstep (se 1 (by rfl) ⟨3598910, by rfl⟩ : syracuseStep 4798547 = 7197821) B7197821
theorem B2562131 : Blo 1421530 2562131 := bstep (se 1 (by rfl) ⟨1921598, by rfl⟩ : syracuseStep 2562131 = 3843197) B3843197
theorem B3602515 : Blo 1421530 3602515 := bstep (se 1 (by rfl) ⟨2701886, by rfl⟩ : syracuseStep 3602515 = 5403773) B5403773
theorem B3201119 : Blo 1421530 3201119 := bstep (se 1 (by rfl) ⟨2400839, by rfl⟩ : syracuseStep 3201119 = 4801679) B4801679
theorem B10254433 : Blo 1421530 10254433 := bstep (se 2 (by rfl) ⟨3845412, by rfl⟩ : syracuseStep 10254433 = 7690825) B7690825
theorem B18241631 : Blo 1421530 18241631 := bstep (se 1 (by rfl) ⟨13681223, by rfl⟩ : syracuseStep 18241631 = 27362447) B27362447
theorem B1423515 : Blo 1421530 1423515 := bstep (se 1 (by rfl) ⟨1067636, by rfl⟩ : syracuseStep 1423515 = 2135273) B2135273
theorem B4798763 : Blo 1421530 4798763 := bstep (se 1 (by rfl) ⟨3599072, by rfl⟩ : syracuseStep 4798763 = 7198145) B7198145
theorem B4864445 : Blo 1421530 4864445 := bstep (se 3 (by rfl) ⟨912083, by rfl⟩ : syracuseStep 4864445 = 1824167) B1824167
theorem B1800731 : Blo 1421530 1800731 := bstep (se 1 (by rfl) ⟨1350548, by rfl⟩ : syracuseStep 1800731 = 2701097) B2701097
theorem B30751271 : Blo 1421530 30751271 := bstep (se 1 (by rfl) ⟨23063453, by rfl⟩ : syracuseStep 30751271 = 46126907) B46126907
theorem B4799033 : Blo 1421530 4799033 := bstep (se 2 (by rfl) ⟨1799637, by rfl⟩ : syracuseStep 4799033 = 3599275) B3599275
theorem B3603001 : Blo 1421530 3603001 := bstep (se 2 (by rfl) ⟨1351125, by rfl⟩ : syracuseStep 3603001 = 2702251) B2702251
theorem B6077263 : Blo 1421530 6077263 := bstep (se 1 (by rfl) ⟨4557947, by rfl⟩ : syracuseStep 6077263 = 9115895) B9115895
theorem B3201875 : Blo 1421530 3201875 := bstep (se 1 (by rfl) ⟨2401406, by rfl⟩ : syracuseStep 3201875 = 4802813) B4802813
theorem B3603305 : Blo 1421530 3603305 := bstep (se 2 (by rfl) ⟨1351239, by rfl⟩ : syracuseStep 3603305 = 2702479) B2702479
theorem B8100809 : Blo 1421530 8100809 := bstep (se 2 (by rfl) ⟨3037803, by rfl⟩ : syracuseStep 8100809 = 6075607) B6075607
theorem B7298039 : Blo 1421530 7298039 := bstep (se 1 (by rfl) ⟨5473529, by rfl⟩ : syracuseStep 7298039 = 10947059) B10947059
theorem B9116819 : Blo 1421530 9116819 := bstep (se 1 (by rfl) ⟨6837614, by rfl⟩ : syracuseStep 9116819 = 13675229) B13675229
theorem B12147965 : Blo 1421530 12147965 := bstep (se 3 (by rfl) ⟨2277743, by rfl⟩ : syracuseStep 12147965 = 4555487) B4555487
theorem B12975389 : Blo 1421530 12975389 := bstep (se 3 (by rfl) ⟨2432885, by rfl⟩ : syracuseStep 12975389 = 4865771) B4865771
theorem B3202415 : Blo 1421530 3202415 := bstep (se 1 (by rfl) ⟨2401811, by rfl⟩ : syracuseStep 3202415 = 4803623) B4803623
theorem B2399719 : Blo 1421530 2399719 := bstep (se 1 (by rfl) ⟨1799789, by rfl⟩ : syracuseStep 2399719 = 3599579) B3599579
theorem B2399807 : Blo 1421530 2399807 := bstep (se 1 (by rfl) ⟨1799855, by rfl⟩ : syracuseStep 2399807 = 3599711) B3599711
theorem B3202703 : Blo 1421530 3202703 := bstep (se 1 (by rfl) ⟨2402027, by rfl⟩ : syracuseStep 3202703 = 4804055) B4804055
theorem B3202793 : Blo 1421530 3202793 := bstep (se 2 (by rfl) ⟨1201047, by rfl⟩ : syracuseStep 3202793 = 2402095) B2402095
theorem B5127923 : Blo 1421530 5127923 := bstep (se 1 (by rfl) ⟨3845942, by rfl⟩ : syracuseStep 5127923 = 7691885) B7691885
theorem B17301289 : Blo 1421530 17301289 := bstep (se 2 (by rfl) ⟨6487983, by rfl⟩ : syracuseStep 17301289 = 12975967) B12975967
theorem B5193559 : Blo 1421530 5193559 := bstep (se 1 (by rfl) ⟨3895169, by rfl⟩ : syracuseStep 5193559 = 7790339) B7790339
theorem B4554667 : Blo 1421530 4554667 := bstep (se 1 (by rfl) ⟨3416000, by rfl⟩ : syracuseStep 4554667 = 6832001) B6832001
theorem B21635171 : Blo 1421530 21635171 := bstep (se 1 (by rfl) ⟨16226378, by rfl⟩ : syracuseStep 21635171 = 32452757) B32452757
theorem B13672577 : Blo 1421530 13672577 := bstep (se 2 (by rfl) ⟨5127216, by rfl⟩ : syracuseStep 13672577 = 10254433) B10254433
theorem B6832349 : Blo 1421530 6832349 := bstep (se 3 (by rfl) ⟨1281065, by rfl⟩ : syracuseStep 6832349 = 2562131) B2562131
theorem B4800761 : Blo 1421530 4800761 := bstep (se 2 (by rfl) ⟨1800285, by rfl⟩ : syracuseStep 4800761 = 3600571) B3600571
theorem B10952975 : Blo 1421530 10952975 := bstep (se 1 (by rfl) ⟨8214731, by rfl⟩ : syracuseStep 10952975 = 16429463) B16429463
theorem B4383143 : Blo 1421530 4383143 := bstep (se 1 (by rfl) ⟨3287357, by rfl⟩ : syracuseStep 4383143 = 6574715) B6574715
theorem B10805723 : Blo 1421530 10805723 := bstep (se 1 (by rfl) ⟨8104292, by rfl⟩ : syracuseStep 10805723 = 16208585) B16208585
theorem B4801031 : Blo 1421530 4801031 := bstep (se 1 (by rfl) ⟨3600773, by rfl⟩ : syracuseStep 4801031 = 7201547) B7201547
theorem B4801139 : Blo 1421530 4801139 := bstep (se 1 (by rfl) ⟨3600854, by rfl⟩ : syracuseStep 4801139 = 7201709) B7201709
theorem B14598953 : Blo 1421530 14598953 := bstep (se 2 (by rfl) ⟨5474607, by rfl⟩ : syracuseStep 14598953 = 10949215) B10949215
theorem B4801409 : Blo 1421530 4801409 := bstep (se 2 (by rfl) ⟨1800528, by rfl⟩ : syracuseStep 4801409 = 3601057) B3601057
theorem B8103017 : Blo 1421530 8103017 := bstep (se 2 (by rfl) ⟨3038631, by rfl⟩ : syracuseStep 8103017 = 6077263) B6077263
theorem B2163823 : Blo 1421530 2163823 := bstep (se 1 (by rfl) ⟨1622867, by rfl⟩ : syracuseStep 2163823 = 3245735) B3245735
theorem B2401447 : Blo 1421530 2401447 := bstep (se 1 (by rfl) ⟨1801085, by rfl⟩ : syracuseStep 2401447 = 3602171) B3602171
theorem B10798433 : Blo 1421530 10798433 := bstep (se 2 (by rfl) ⟨4049412, by rfl⟩ : syracuseStep 10798433 = 8098825) B8098825
theorem B4801949 : Blo 1421530 4801949 := bstep (se 3 (by rfl) ⟨900365, by rfl⟩ : syracuseStep 4801949 = 1800731) B1800731
theorem B4802111 : Blo 1421530 4802111 := bstep (se 1 (by rfl) ⟨3601583, by rfl⟩ : syracuseStep 4802111 = 7203167) B7203167
theorem B12150425 : Blo 1421530 12150425 := bstep (se 2 (by rfl) ⟨4556409, by rfl⟩ : syracuseStep 12150425 = 9112819) B9112819
theorem B4802219 : Blo 1421530 4802219 := bstep (se 1 (by rfl) ⟨3601664, by rfl⟩ : syracuseStep 4802219 = 7203329) B7203329
theorem B46171943 : Blo 1421530 46171943 := bstep (se 1 (by rfl) ⟨34628957, by rfl⟩ : syracuseStep 46171943 = 69257915) B69257915
theorem B6834041 : Blo 1421530 6834041 := bstep (se 2 (by rfl) ⟨2562765, by rfl⟩ : syracuseStep 6834041 = 5125531) B5125531
theorem B2402203 : Blo 1421530 2402203 := bstep (se 1 (by rfl) ⟨1801652, by rfl⟩ : syracuseStep 2402203 = 3603305) B3603305
theorem B5400539 : Blo 1421530 5400539 := bstep (se 1 (by rfl) ⟨4050404, by rfl⟩ : syracuseStep 5400539 = 8100809) B8100809
theorem B4802759 : Blo 1421530 4802759 := bstep (se 1 (by rfl) ⟨3602069, by rfl⟩ : syracuseStep 4802759 = 7204139) B7204139
theorem B2132303 : Blo 1421530 2132303 := bstep (se 1 (by rfl) ⟨1599227, by rfl⟩ : syracuseStep 2132303 = 3198455) B3198455
theorem B2132351 : Blo 1421530 2132351 := bstep (se 1 (by rfl) ⟨1599263, by rfl⟩ : syracuseStep 2132351 = 3198527) B3198527
theorem B1599871 : Blo 1421530 1599871 := bstep (se 1 (by rfl) ⟨1199903, by rfl⟩ : syracuseStep 1599871 = 2399807) B2399807
theorem B2132393 : Blo 1421530 2132393 := bstep (se 2 (by rfl) ⟨799647, by rfl⟩ : syracuseStep 2132393 = 1599295) B1599295
theorem B8096183 : Blo 1421530 8096183 := bstep (se 1 (by rfl) ⟨6072137, by rfl⟩ : syracuseStep 8096183 = 12144275) B12144275
theorem B6924745 : Blo 1421530 6924745 := bstep (se 2 (by rfl) ⟨2596779, by rfl⟩ : syracuseStep 6924745 = 5193559) B5193559
theorem B3418615 : Blo 1421530 3418615 := bstep (se 1 (by rfl) ⟨2563961, by rfl⟩ : syracuseStep 3418615 = 5127923) B5127923
theorem B6072889 : Blo 1421530 6072889 := bstep (se 2 (by rfl) ⟨2277333, by rfl⟩ : syracuseStep 6072889 = 4554667) B4554667
theorem B61524683 : Blo 1421530 61524683 := bstep (se 1 (by rfl) ⟨46143512, by rfl⟩ : syracuseStep 61524683 = 92287025) B92287025
theorem B4803353 : Blo 1421530 4803353 := bstep (se 2 (by rfl) ⟨1801257, by rfl⟩ : syracuseStep 4803353 = 3602515) B3602515
theorem B2132777 : Blo 1421530 2132777 := bstep (se 2 (by rfl) ⟨799791, by rfl⟩ : syracuseStep 2132777 = 1599583) B1599583
theorem B2132987 : Blo 1421530 2132987 := bstep (se 1 (by rfl) ⟨1599740, by rfl⟩ : syracuseStep 2132987 = 3199481) B3199481
theorem B2133047 : Blo 1421530 2133047 := bstep (se 1 (by rfl) ⟨1599785, by rfl⟩ : syracuseStep 2133047 = 3199571) B3199571
theorem B4803731 : Blo 1421530 4803731 := bstep (se 1 (by rfl) ⟨3602798, by rfl⟩ : syracuseStep 4803731 = 7205597) B7205597
theorem B2133167 : Blo 1421530 2133167 := bstep (se 1 (by rfl) ⟨1599875, by rfl⟩ : syracuseStep 2133167 = 3199751) B3199751
theorem B4804001 : Blo 1421530 4804001 := bstep (se 2 (by rfl) ⟨1801500, by rfl⟩ : syracuseStep 4804001 = 3603001) B3603001
theorem B2698895 : Blo 1421530 2698895 := bstep (se 1 (by rfl) ⟨2024171, by rfl⟩ : syracuseStep 2698895 = 4048343) B4048343
theorem B8105615 : Blo 1421530 8105615 := bstep (se 1 (by rfl) ⟨6079211, by rfl⟩ : syracuseStep 8105615 = 12158423) B12158423
theorem B3198635 : Blo 1421530 3198635 := bstep (se 1 (by rfl) ⟨2398976, by rfl⟩ : syracuseStep 3198635 = 4797953) B4797953
theorem B1601275 : Blo 1421530 1601275 := bstep (se 1 (by rfl) ⟨1200956, by rfl⟩ : syracuseStep 1601275 = 2401913) B2401913
theorem B6836039 : Blo 1421530 6836039 := bstep (se 1 (by rfl) ⟨5127029, by rfl⟩ : syracuseStep 6836039 = 10254059) B10254059
theorem B2133887 : Blo 1421530 2133887 := bstep (se 1 (by rfl) ⟨1600415, by rfl⟩ : syracuseStep 2133887 = 3200831) B3200831
theorem B3198959 : Blo 1421530 3198959 := bstep (se 1 (by rfl) ⟨2399219, by rfl⟩ : syracuseStep 3198959 = 4798439) B4798439
theorem B36974593 : Blo 1421530 36974593 := bstep (se 2 (by rfl) ⟨13865472, by rfl⟩ : syracuseStep 36974593 = 27730945) B27730945
theorem B3199031 : Blo 1421530 3199031 := bstep (se 1 (by rfl) ⟨2399273, by rfl⟩ : syracuseStep 3199031 = 4798547) B4798547
theorem B2134079 : Blo 1421530 2134079 := bstep (se 1 (by rfl) ⟨1600559, by rfl⟩ : syracuseStep 2134079 = 3201119) B3201119
theorem B12161087 : Blo 1421530 12161087 := bstep (se 1 (by rfl) ⟨9120815, by rfl⟩ : syracuseStep 12161087 = 18241631) B18241631
theorem B6156371 : Blo 1421530 6156371 := bstep (se 1 (by rfl) ⟨4617278, by rfl⟩ : syracuseStep 6156371 = 9234557) B9234557
theorem B3199175 : Blo 1421530 3199175 := bstep (se 1 (by rfl) ⟨2399381, by rfl⟩ : syracuseStep 3199175 = 4798763) B4798763
theorem B9113897 : Blo 1421530 9113897 := bstep (se 2 (by rfl) ⟨3417711, by rfl⟩ : syracuseStep 9113897 = 6835423) B6835423
theorem B2134313 : Blo 1421530 2134313 := bstep (se 2 (by rfl) ⟨800367, by rfl⟩ : syracuseStep 2134313 = 1600735) B1600735
theorem B1421671 : Blo 1421530 1421671 := bstep (se 1 (by rfl) ⟨1066253, by rfl⟩ : syracuseStep 1421671 = 2132507) B2132507
theorem B5402983 : Blo 1421530 5402983 := bstep (se 1 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 5402983 = 8104475) B8104475
theorem B20500847 : Blo 1421530 20500847 := bstep (se 1 (by rfl) ⟨15375635, by rfl⟩ : syracuseStep 20500847 = 30751271) B30751271
theorem B3199355 : Blo 1421530 3199355 := bstep (se 1 (by rfl) ⟨2399516, by rfl⟩ : syracuseStep 3199355 = 4799033) B4799033
theorem B1421723 : Blo 1421530 1421723 := bstep (se 1 (by rfl) ⟨1066292, by rfl⟩ : syracuseStep 1421723 = 2132585) B2132585
theorem B2134583 : Blo 1421530 2134583 := bstep (se 1 (by rfl) ⟨1600937, by rfl⟩ : syracuseStep 2134583 = 3201875) B3201875
theorem B9007745 : Blo 1421530 9007745 := bstep (se 2 (by rfl) ⟨3377904, by rfl⟩ : syracuseStep 9007745 = 6755809) B6755809
theorem B3199625 : Blo 1421530 3199625 := bstep (se 2 (by rfl) ⟨1199859, by rfl⟩ : syracuseStep 3199625 = 2399719) B2399719
theorem B1422075 : Blo 1421530 1422075 := bstep (se 1 (by rfl) ⟨1066556, by rfl⟩ : syracuseStep 1422075 = 2133113) B2133113
theorem B10253051 : Blo 1421530 10253051 := bstep (se 1 (by rfl) ⟨7689788, by rfl⟩ : syracuseStep 10253051 = 15379577) B15379577
theorem B25965359 : Blo 1421530 25965359 := bstep (se 1 (by rfl) ⟨19474019, by rfl⟩ : syracuseStep 25965359 = 38948039) B38948039
theorem B1422143 : Blo 1421530 1422143 := bstep (se 1 (by rfl) ⟨1066607, by rfl⟩ : syracuseStep 1422143 = 2133215) B2133215
theorem B8098643 : Blo 1421530 8098643 := bstep (se 1 (by rfl) ⟨6073982, by rfl⟩ : syracuseStep 8098643 = 12147965) B12147965
theorem B1422171 : Blo 1421530 1422171 := bstep (se 1 (by rfl) ⟨1066628, by rfl⟩ : syracuseStep 1422171 = 2133257) B2133257
theorem B1422239 : Blo 1421530 1422239 := bstep (se 1 (by rfl) ⟨1066679, by rfl⟩ : syracuseStep 1422239 = 2133359) B2133359
theorem B2134943 : Blo 1421530 2134943 := bstep (se 1 (by rfl) ⟨1601207, by rfl⟩ : syracuseStep 2134943 = 3202415) B3202415
theorem B17314721 : Blo 1421530 17314721 := bstep (se 2 (by rfl) ⟨6493020, by rfl⟩ : syracuseStep 17314721 = 12986041) B12986041
theorem B1422319 : Blo 1421530 1422319 := bstep (se 1 (by rfl) ⟨1066739, by rfl⟩ : syracuseStep 1422319 = 2133479) B2133479
theorem B1422407 : Blo 1421530 1422407 := bstep (se 1 (by rfl) ⟨1066805, by rfl⟩ : syracuseStep 1422407 = 2133611) B2133611
theorem B2135135 : Blo 1421530 2135135 := bstep (se 1 (by rfl) ⟨1601351, by rfl⟩ : syracuseStep 2135135 = 3202703) B3202703
theorem B1422491 : Blo 1421530 1422491 := bstep (se 1 (by rfl) ⟨1066868, by rfl⟩ : syracuseStep 1422491 = 2133737) B2133737
theorem B2135195 : Blo 1421530 2135195 := bstep (se 1 (by rfl) ⟨1601396, by rfl⟩ : syracuseStep 2135195 = 3202793) B3202793
theorem B1422587 : Blo 1421530 1422587 := bstep (se 1 (by rfl) ⟨1066940, by rfl⟩ : syracuseStep 1422587 = 2133881) B2133881
theorem B1422655 : Blo 1421530 1422655 := bstep (se 1 (by rfl) ⟨1066991, by rfl⟩ : syracuseStep 1422655 = 2133983) B2133983
theorem B3200363 : Blo 1421530 3200363 := bstep (se 1 (by rfl) ⟨2400272, by rfl⟩ : syracuseStep 3200363 = 4800545) B4800545
theorem B1422823 : Blo 1421530 1422823 := bstep (se 1 (by rfl) ⟨1067117, by rfl⟩ : syracuseStep 1422823 = 2134235) B2134235
theorem B1422831 : Blo 1421530 1422831 := bstep (se 1 (by rfl) ⟨1067123, by rfl⟩ : syracuseStep 1422831 = 2134247) B2134247
theorem B2963035 : Blo 1421530 2963035 := bstep (se 1 (by rfl) ⟨2222276, by rfl⟩ : syracuseStep 2963035 = 4444553) B4444553
theorem B1422939 : Blo 1421530 1422939 := bstep (se 1 (by rfl) ⟨1067204, by rfl⟩ : syracuseStep 1422939 = 2134409) B2134409
theorem B3200633 : Blo 1421530 3200633 := bstep (se 2 (by rfl) ⟨1200237, by rfl⟩ : syracuseStep 3200633 = 2400475) B2400475
theorem B1423003 : Blo 1421530 1423003 := bstep (se 1 (by rfl) ⟨1067252, by rfl⟩ : syracuseStep 1423003 = 2134505) B2134505
theorem B1423087 : Blo 1421530 1423087 := bstep (se 1 (by rfl) ⟨1067315, by rfl⟩ : syracuseStep 1423087 = 2134631) B2134631
theorem B1709807 : Blo 1421530 1709807 := bstep (se 1 (by rfl) ⟨1282355, by rfl⟩ : syracuseStep 1709807 = 2564711) B2564711
theorem B5404427 : Blo 1421530 5404427 := bstep (se 1 (by rfl) ⟨4053320, by rfl⟩ : syracuseStep 5404427 = 8106641) B8106641
theorem B1423175 : Blo 1421530 1423175 := bstep (se 1 (by rfl) ⟨1067381, by rfl⟩ : syracuseStep 1423175 = 2134763) B2134763
theorem B1423195 : Blo 1421530 1423195 := bstep (se 1 (by rfl) ⟨1067396, by rfl⟩ : syracuseStep 1423195 = 2134793) B2134793
theorem B9115537 : Blo 1421530 9115537 := bstep (se 2 (by rfl) ⟨3418326, by rfl⟩ : syracuseStep 9115537 = 6836653) B6836653
theorem B1423263 : Blo 1421530 1423263 := bstep (se 1 (by rfl) ⟨1067447, by rfl⟩ : syracuseStep 1423263 = 2134895) B2134895
theorem B3200993 : Blo 1421530 3200993 := bstep (se 2 (by rfl) ⟨1200372, by rfl⟩ : syracuseStep 3200993 = 2400745) B2400745
theorem B1423431 : Blo 1421530 1423431 := bstep (se 1 (by rfl) ⟨1067573, by rfl⟩ : syracuseStep 1423431 = 2135147) B2135147
theorem B4798655 : Blo 1421530 4798655 := bstep (se 1 (by rfl) ⟨3598991, by rfl⟩ : syracuseStep 4798655 = 7197983) B7197983
theorem B4053331 : Blo 1421530 4053331 := bstep (se 1 (by rfl) ⟨3039998, by rfl⟩ : syracuseStep 4053331 = 6079997) B6079997
theorem B4618783 : Blo 1421530 4618783 := bstep (se 1 (by rfl) ⟨3464087, by rfl⟩ : syracuseStep 4618783 = 6928175) B6928175
theorem B3242963 : Blo 1421530 3242963 := bstep (se 1 (by rfl) ⟨2432222, by rfl⟩ : syracuseStep 3242963 = 4864445) B4864445
theorem B12147691 : Blo 1421530 12147691 := bstep (se 1 (by rfl) ⟨9110768, by rfl⟩ : syracuseStep 12147691 = 18221537) B18221537
theorem B299850821 : Blo 1421530 299850821 := bstep (se 4 (by rfl) ⟨28111014, by rfl⟩ : syracuseStep 299850821 = 56222029) B56222029
theorem B7199927 : Blo 1421530 7199927 := bstep (se 1 (by rfl) ⟨5399945, by rfl⟩ : syracuseStep 7199927 = 10799891) B10799891
theorem B4865359 : Blo 1421530 4865359 := bstep (se 1 (by rfl) ⟨3649019, by rfl⟩ : syracuseStep 4865359 = 7298039) B7298039
theorem B6077879 : Blo 1421530 6077879 := bstep (se 1 (by rfl) ⟨4558409, by rfl⟩ : syracuseStep 6077879 = 9116819) B9116819
theorem B8650259 : Blo 1421530 8650259 := bstep (se 1 (by rfl) ⟨6487694, by rfl⟩ : syracuseStep 8650259 = 12975389) B12975389
theorem B216293003 : Blo 1421530 216293003 := bstep (se 1 (by rfl) ⟨162219752, by rfl⟩ : syracuseStep 216293003 = 324439505) B324439505
theorem B23068385 : Blo 1421530 23068385 := bstep (se 2 (by rfl) ⟨8650644, by rfl⟩ : syracuseStep 23068385 = 17301289) B17301289
theorem B3202847 : Blo 1421530 3202847 := bstep (se 1 (by rfl) ⟨2402135, by rfl⟩ : syracuseStep 3202847 = 4804271) B4804271
theorem B5398427 : Blo 1421530 5398427 := bstep (se 1 (by rfl) ⟨4048820, by rfl⟩ : syracuseStep 5398427 = 8097641) B8097641
theorem B49299457 : Blo 1421530 49299457 := bstep (se 2 (by rfl) ⟨18487296, by rfl⟩ : syracuseStep 49299457 = 36974593) B36974593
theorem B4554899 : Blo 1421530 4554899 := bstep (se 1 (by rfl) ⟨3416174, by rfl⟩ : syracuseStep 4554899 = 6832349) B6832349
theorem B16416989 : Blo 1421530 16416989 := bstep (se 3 (by rfl) ⟨3078185, by rfl⟩ : syracuseStep 16416989 = 6156371) B6156371
theorem B9732635 : Blo 1421530 9732635 := bstep (se 1 (by rfl) ⟨7299476, by rfl⟩ : syracuseStep 9732635 = 14598953) B14598953
theorem B17310239 : Blo 1421530 17310239 := bstep (se 1 (by rfl) ⟨12982679, by rfl⟩ : syracuseStep 17310239 = 25965359) B25965359
theorem B5399095 : Blo 1421530 5399095 := bstep (se 1 (by rfl) ⟨4049321, by rfl⟩ : syracuseStep 5399095 = 8098643) B8098643
theorem B9232993 : Blo 1421530 9232993 := bstep (se 2 (by rfl) ⟨3462372, by rfl⟩ : syracuseStep 9232993 = 6924745) B6924745
theorem B11543147 : Blo 1421530 11543147 := bstep (se 1 (by rfl) ⟨8657360, by rfl⟩ : syracuseStep 11543147 = 17314721) B17314721
theorem B4556027 : Blo 1421530 4556027 := bstep (se 1 (by rfl) ⟨3417020, by rfl⟩ : syracuseStep 4556027 = 6834041) B6834041
theorem B16196921 : Blo 1421530 16196921 := bstep (se 2 (by rfl) ⟨6073845, by rfl⟩ : syracuseStep 16196921 = 12147691) B12147691
theorem B24020653 : Blo 1421530 24020653 := bstep (se 3 (by rfl) ⟨4503872, by rfl⟩ : syracuseStep 24020653 = 9007745) B9007745
theorem B3950713 : Blo 1421530 3950713 := bstep (se 2 (by rfl) ⟨1481517, by rfl⟩ : syracuseStep 3950713 = 2963035) B2963035
theorem B2132423 : Blo 1421530 2132423 := bstep (se 1 (by rfl) ⟨1599317, by rfl⟩ : syracuseStep 2132423 = 3198635) B3198635
theorem B15378923 : Blo 1421530 15378923 := bstep (se 1 (by rfl) ⟨11534192, by rfl⟩ : syracuseStep 15378923 = 23068385) B23068385
theorem B4557359 : Blo 1421530 4557359 := bstep (se 1 (by rfl) ⟨3418019, by rfl⟩ : syracuseStep 4557359 = 6836039) B6836039
theorem B3598951 : Blo 1421530 3598951 := bstep (se 1 (by rfl) ⟨2699213, by rfl⟩ : syracuseStep 3598951 = 5398427) B5398427
theorem B2132639 : Blo 1421530 2132639 := bstep (se 1 (by rfl) ⟨1599479, by rfl⟩ : syracuseStep 2132639 = 3198959) B3198959
theorem B2132687 : Blo 1421530 2132687 := bstep (se 1 (by rfl) ⟨1599515, by rfl⟩ : syracuseStep 2132687 = 3199031) B3199031
theorem B2132783 : Blo 1421530 2132783 := bstep (se 1 (by rfl) ⟨1599587, by rfl⟩ : syracuseStep 2132783 = 3199175) B3199175
theorem B7301983 : Blo 1421530 7301983 := bstep (se 1 (by rfl) ⟨5476487, by rfl⟩ : syracuseStep 7301983 = 10952975) B10952975
theorem B13667231 : Blo 1421530 13667231 := bstep (se 1 (by rfl) ⟨10250423, by rfl⟩ : syracuseStep 13667231 = 20500847) B20500847
theorem B2132903 : Blo 1421530 2132903 := bstep (se 1 (by rfl) ⟨1599677, by rfl⟩ : syracuseStep 2132903 = 3199355) B3199355
theorem B7203815 : Blo 1421530 7203815 := bstep (se 1 (by rfl) ⟨5402861, by rfl⟩ : syracuseStep 7203815 = 10805723) B10805723
theorem B2133083 : Blo 1421530 2133083 := bstep (se 1 (by rfl) ⟨1599812, by rfl⟩ : syracuseStep 2133083 = 3199625) B3199625
theorem B7203977 : Blo 1421530 7203977 := bstep (se 2 (by rfl) ⟨2701491, by rfl⟩ : syracuseStep 7203977 = 5402983) B5402983
theorem B6835367 : Blo 1421530 6835367 := bstep (se 1 (by rfl) ⟨5126525, by rfl⟩ : syracuseStep 6835367 = 10253051) B10253051
theorem B2133161 : Blo 1421530 2133161 := bstep (se 2 (by rfl) ⟨799935, by rfl⟩ : syracuseStep 2133161 = 1599871) B1599871
theorem B4558153 : Blo 1421530 4558153 := bstep (se 2 (by rfl) ⟨1709307, by rfl⟩ : syracuseStep 4558153 = 3418615) B3418615
theorem B5402011 : Blo 1421530 5402011 := bstep (se 1 (by rfl) ⟨4051508, by rfl⟩ : syracuseStep 5402011 = 8103017) B8103017
theorem B8097185 : Blo 1421530 8097185 := bstep (se 2 (by rfl) ⟨3036444, by rfl⟩ : syracuseStep 8097185 = 6072889) B6072889
theorem B2133575 : Blo 1421530 2133575 := bstep (se 1 (by rfl) ⟨1600181, by rfl⟩ : syracuseStep 2133575 = 3200363) B3200363
theorem B2133755 : Blo 1421530 2133755 := bstep (se 1 (by rfl) ⟨1600316, by rfl⟩ : syracuseStep 2133755 = 3200633) B3200633
theorem B30781295 : Blo 1421530 30781295 := bstep (se 1 (by rfl) ⟨23085971, by rfl⟩ : syracuseStep 30781295 = 46171943) B46171943
theorem B3600359 : Blo 1421530 3600359 := bstep (se 1 (by rfl) ⟨2700269, by rfl⟩ : syracuseStep 3600359 = 5400539) B5400539
theorem B2133995 : Blo 1421530 2133995 := bstep (se 1 (by rfl) ⟨1600496, by rfl⟩ : syracuseStep 2133995 = 3200993) B3200993
theorem B3199103 : Blo 1421530 3199103 := bstep (se 1 (by rfl) ⟨2399327, by rfl⟩ : syracuseStep 3199103 = 4798655) B4798655
theorem B1421535 : Blo 1421530 1421535 := bstep (se 1 (by rfl) ⟨1066151, by rfl⟩ : syracuseStep 1421535 = 2132303) B2132303
theorem B1421567 : Blo 1421530 1421567 := bstep (se 1 (by rfl) ⟨1066175, by rfl⟩ : syracuseStep 1421567 = 2132351) B2132351
theorem B1421595 : Blo 1421530 1421595 := bstep (se 1 (by rfl) ⟨1066196, by rfl⟩ : syracuseStep 1421595 = 2132393) B2132393
theorem B1421851 : Blo 1421530 1421851 := bstep (se 1 (by rfl) ⟨1066388, by rfl⟩ : syracuseStep 1421851 = 2132777) B2132777
theorem B4559485 : Blo 1421530 4559485 := bstep (se 3 (by rfl) ⟨854903, by rfl⟩ : syracuseStep 4559485 = 1709807) B1709807
theorem B1421991 : Blo 1421530 1421991 := bstep (se 1 (by rfl) ⟨1066493, by rfl⟩ : syracuseStep 1421991 = 2132987) B2132987
theorem B1422031 : Blo 1421530 1422031 := bstep (se 1 (by rfl) ⟨1066523, by rfl⟩ : syracuseStep 1422031 = 2133047) B2133047
theorem B1422111 : Blo 1421530 1422111 := bstep (se 1 (by rfl) ⟨1066583, by rfl⟩ : syracuseStep 1422111 = 2133167) B2133167
theorem B4051919 : Blo 1421530 4051919 := bstep (se 1 (by rfl) ⟨3038939, by rfl⟩ : syracuseStep 4051919 = 6077879) B6077879
theorem B2135033 : Blo 1421530 2135033 := bstep (se 2 (by rfl) ⟨800637, by rfl⟩ : syracuseStep 2135033 = 1601275) B1601275
theorem B1799263 : Blo 1421530 1799263 := bstep (se 1 (by rfl) ⟨1349447, by rfl⟩ : syracuseStep 1799263 = 2698895) B2698895
theorem B5403743 : Blo 1421530 5403743 := bstep (se 1 (by rfl) ⟨4052807, by rfl⟩ : syracuseStep 5403743 = 8105615) B8105615
theorem B2135231 : Blo 1421530 2135231 := bstep (se 1 (by rfl) ⟨1601423, by rfl⟩ : syracuseStep 2135231 = 3202847) B3202847
theorem B12154049 : Blo 1421530 12154049 := bstep (se 2 (by rfl) ⟨4557768, by rfl⟩ : syracuseStep 12154049 = 9115537) B9115537
theorem B1422591 : Blo 1421530 1422591 := bstep (se 1 (by rfl) ⟨1066943, by rfl⟩ : syracuseStep 1422591 = 2133887) B2133887
theorem B1422719 : Blo 1421530 1422719 := bstep (se 1 (by rfl) ⟨1067039, by rfl⟩ : syracuseStep 1422719 = 2134079) B2134079
theorem B8107391 : Blo 1421530 8107391 := bstep (se 1 (by rfl) ⟨6080543, by rfl⟩ : syracuseStep 8107391 = 12161087) B12161087
theorem B14423447 : Blo 1421530 14423447 := bstep (se 1 (by rfl) ⟨10817585, by rfl⟩ : syracuseStep 14423447 = 21635171) B21635171
theorem B9115051 : Blo 1421530 9115051 := bstep (se 1 (by rfl) ⟨6836288, by rfl⟩ : syracuseStep 9115051 = 13672577) B13672577
theorem B3200507 : Blo 1421530 3200507 := bstep (se 1 (by rfl) ⟨2400380, by rfl⟩ : syracuseStep 3200507 = 4800761) B4800761
theorem B6075931 : Blo 1421530 6075931 := bstep (se 1 (by rfl) ⟨4556948, by rfl⟩ : syracuseStep 6075931 = 9113897) B9113897
theorem B1422875 : Blo 1421530 1422875 := bstep (se 1 (by rfl) ⟨1067156, by rfl⟩ : syracuseStep 1422875 = 2134313) B2134313
theorem B2922095 : Blo 1421530 2922095 := bstep (se 1 (by rfl) ⟨2191571, by rfl⟩ : syracuseStep 2922095 = 4383143) B4383143
theorem B3200687 : Blo 1421530 3200687 := bstep (se 1 (by rfl) ⟨2400515, by rfl⟩ : syracuseStep 3200687 = 4801031) B4801031
theorem B1423055 : Blo 1421530 1423055 := bstep (se 1 (by rfl) ⟨1067291, by rfl⟩ : syracuseStep 1423055 = 2134583) B2134583
theorem B3200759 : Blo 1421530 3200759 := bstep (se 1 (by rfl) ⟨2400569, by rfl⟩ : syracuseStep 3200759 = 4801139) B4801139
theorem B5404441 : Blo 1421530 5404441 := bstep (se 2 (by rfl) ⟨2026665, by rfl⟩ : syracuseStep 5404441 = 4053331) B4053331
theorem B11540389 : Blo 1421530 11540389 := bstep (se 4 (by rfl) ⟨1081911, by rfl⟩ : syracuseStep 11540389 = 2163823) B2163823
theorem B3200939 : Blo 1421530 3200939 := bstep (se 1 (by rfl) ⟨2400704, by rfl⟩ : syracuseStep 3200939 = 4801409) B4801409
theorem B1423295 : Blo 1421530 1423295 := bstep (se 1 (by rfl) ⟨1067471, by rfl⟩ : syracuseStep 1423295 = 2134943) B2134943
theorem B6158377 : Blo 1421530 6158377 := bstep (se 2 (by rfl) ⟨2309391, by rfl⟩ : syracuseStep 6158377 = 4618783) B4618783
theorem B1423423 : Blo 1421530 1423423 := bstep (se 1 (by rfl) ⟨1067567, by rfl⟩ : syracuseStep 1423423 = 2135135) B2135135
theorem B1423463 : Blo 1421530 1423463 := bstep (se 1 (by rfl) ⟨1067597, by rfl⟩ : syracuseStep 1423463 = 2135195) B2135195
theorem B7198955 : Blo 1421530 7198955 := bstep (se 1 (by rfl) ⟨5399216, by rfl⟩ : syracuseStep 7198955 = 10798433) B10798433
theorem B3201299 : Blo 1421530 3201299 := bstep (se 1 (by rfl) ⟨2400974, by rfl⟩ : syracuseStep 3201299 = 4801949) B4801949
theorem B3201407 : Blo 1421530 3201407 := bstep (se 1 (by rfl) ⟨2401055, by rfl⟩ : syracuseStep 3201407 = 4802111) B4802111
theorem B8100283 : Blo 1421530 8100283 := bstep (se 1 (by rfl) ⟨6075212, by rfl⟩ : syracuseStep 8100283 = 12150425) B12150425
theorem B3201479 : Blo 1421530 3201479 := bstep (se 1 (by rfl) ⟨2401109, by rfl⟩ : syracuseStep 3201479 = 4802219) B4802219
theorem B3602951 : Blo 1421530 3602951 := bstep (se 1 (by rfl) ⟨2702213, by rfl⟩ : syracuseStep 3602951 = 5404427) B5404427
theorem B3201839 : Blo 1421530 3201839 := bstep (se 1 (by rfl) ⟨2401379, by rfl⟩ : syracuseStep 3201839 = 4802759) B4802759
theorem B3201929 : Blo 1421530 3201929 := bstep (se 2 (by rfl) ⟨1200723, by rfl⟩ : syracuseStep 3201929 = 2401447) B2401447
theorem B5397455 : Blo 1421530 5397455 := bstep (se 1 (by rfl) ⟨4048091, by rfl⟩ : syracuseStep 5397455 = 8096183) B8096183
theorem B6487145 : Blo 1421530 6487145 := bstep (se 2 (by rfl) ⟨2432679, by rfl⟩ : syracuseStep 6487145 = 4865359) B4865359
theorem B41016455 : Blo 1421530 41016455 := bstep (se 1 (by rfl) ⟨30762341, by rfl⟩ : syracuseStep 41016455 = 61524683) B61524683
theorem B3202235 : Blo 1421530 3202235 := bstep (se 1 (by rfl) ⟨2401676, by rfl⟩ : syracuseStep 3202235 = 4803353) B4803353
theorem B2161975 : Blo 1421530 2161975 := bstep (se 1 (by rfl) ⟨1621481, by rfl⟩ : syracuseStep 2161975 = 3242963) B3242963
theorem B199900547 : Blo 1421530 199900547 := bstep (se 1 (by rfl) ⟨149925410, by rfl⟩ : syracuseStep 199900547 = 299850821) B299850821
theorem B3202487 : Blo 1421530 3202487 := bstep (se 1 (by rfl) ⟨2401865, by rfl⟩ : syracuseStep 3202487 = 4803731) B4803731
theorem B4799951 : Blo 1421530 4799951 := bstep (se 1 (by rfl) ⟨3599963, by rfl⟩ : syracuseStep 4799951 = 7199927) B7199927
theorem B3202667 : Blo 1421530 3202667 := bstep (se 1 (by rfl) ⟨2402000, by rfl⟩ : syracuseStep 3202667 = 4804001) B4804001
theorem B5766839 : Blo 1421530 5766839 := bstep (se 1 (by rfl) ⟨4325129, by rfl⟩ : syracuseStep 5766839 = 8650259) B8650259
theorem B144195335 : Blo 1421530 144195335 := bstep (se 1 (by rfl) ⟨108146501, by rfl⟩ : syracuseStep 144195335 = 216293003) B216293003
theorem B3202937 : Blo 1421530 3202937 := bstep (se 2 (by rfl) ⟨1201101, by rfl⟩ : syracuseStep 3202937 = 2402203) B2402203
theorem B65732609 : Blo 1421530 65732609 := bstep (se 2 (by rfl) ⟨24649728, by rfl⟩ : syracuseStep 65732609 = 49299457) B49299457
theorem B10944659 : Blo 1421530 10944659 := bstep (se 1 (by rfl) ⟨8208494, by rfl⟩ : syracuseStep 10944659 = 16416989) B16416989
theorem B6488423 : Blo 1421530 6488423 := bstep (se 1 (by rfl) ⟨4866317, by rfl⟩ : syracuseStep 6488423 = 9732635) B9732635
theorem B49242629 : Blo 1421530 49242629 := bstep (se 4 (by rfl) ⟨4616496, by rfl⟩ : syracuseStep 49242629 = 9232993) B9232993
theorem B21070469 : Blo 1421530 21070469 := bstep (se 4 (by rfl) ⟨1975356, by rfl⟩ : syracuseStep 21070469 = 3950713) B3950713
theorem B8102699 : Blo 1421530 8102699 := bstep (se 1 (by rfl) ⟨6077024, by rfl⟩ : syracuseStep 8102699 = 12154049) B12154049
theorem B6079313 : Blo 1421530 6079313 := bstep (se 2 (by rfl) ⟨2279742, by rfl⟩ : syracuseStep 6079313 = 4559485) B4559485
theorem B10797947 : Blo 1421530 10797947 := bstep (se 1 (by rfl) ⟨8098460, by rfl⟩ : syracuseStep 10797947 = 16196921) B16196921
theorem B2401967 : Blo 1421530 2401967 := bstep (se 1 (by rfl) ⟨1801475, by rfl⟩ : syracuseStep 2401967 = 3602951) B3602951
theorem B7202681 : Blo 1421530 7202681 := bstep (se 2 (by rfl) ⟨2701005, by rfl⟩ : syracuseStep 7202681 = 5402011) B5402011
theorem B9111487 : Blo 1421530 9111487 := bstep (se 1 (by rfl) ⟨6833615, by rfl⟩ : syracuseStep 9111487 = 13667231) B13667231
theorem B3598303 : Blo 1421530 3598303 := bstep (se 1 (by rfl) ⟨2698727, by rfl⟩ : syracuseStep 3598303 = 5397455) B5397455
theorem B4802543 : Blo 1421530 4802543 := bstep (se 1 (by rfl) ⟨3601907, by rfl⟩ : syracuseStep 4802543 = 7203815) B7203815
theorem B4802651 : Blo 1421530 4802651 := bstep (se 1 (by rfl) ⟨3601988, by rfl⟩ : syracuseStep 4802651 = 7203977) B7203977
theorem B4556911 : Blo 1421530 4556911 := bstep (se 1 (by rfl) ⟨3417683, by rfl⟩ : syracuseStep 4556911 = 6835367) B6835367
theorem B3844559 : Blo 1421530 3844559 := bstep (se 1 (by rfl) ⟨2883419, by rfl⟩ : syracuseStep 3844559 = 5766839) B5766839
theorem B15387185 : Blo 1421530 15387185 := bstep (se 2 (by rfl) ⟨5770194, by rfl⟩ : syracuseStep 15387185 = 11540389) B11540389
theorem B8211169 : Blo 1421530 8211169 := bstep (se 2 (by rfl) ⟨3079188, by rfl⟩ : syracuseStep 8211169 = 6158377) B6158377
theorem B2132735 : Blo 1421530 2132735 := bstep (se 1 (by rfl) ⟨1599551, by rfl⟩ : syracuseStep 2132735 = 3199103) B3199103
theorem B7695431 : Blo 1421530 7695431 := bstep (se 1 (by rfl) ⟨5771573, by rfl⟩ : syracuseStep 7695431 = 11543147) B11543147
theorem B10800377 : Blo 1421530 10800377 := bstep (se 2 (by rfl) ⟨4050141, by rfl⟩ : syracuseStep 10800377 = 8100283) B8100283
theorem B2133671 : Blo 1421530 2133671 := bstep (se 1 (by rfl) ⟨1600253, by rfl⟩ : syracuseStep 2133671 = 3200507) B3200507
theorem B2133791 : Blo 1421530 2133791 := bstep (se 1 (by rfl) ⟨1600343, by rfl⟩ : syracuseStep 2133791 = 3200687) B3200687
theorem B9735977 : Blo 1421530 9735977 := bstep (se 2 (by rfl) ⟨3650991, by rfl⟩ : syracuseStep 9735977 = 7301983) B7301983
theorem B2133839 : Blo 1421530 2133839 := bstep (se 1 (by rfl) ⟨1600379, by rfl⟩ : syracuseStep 2133839 = 3200759) B3200759
theorem B2133959 : Blo 1421530 2133959 := bstep (se 1 (by rfl) ⟨1600469, by rfl⟩ : syracuseStep 2133959 = 3200939) B3200939
theorem B2134199 : Blo 1421530 2134199 := bstep (se 1 (by rfl) ⟨1600649, by rfl⟩ : syracuseStep 2134199 = 3201299) B3201299
theorem B2134271 : Blo 1421530 2134271 := bstep (se 1 (by rfl) ⟨1600703, by rfl⟩ : syracuseStep 2134271 = 3201407) B3201407
theorem B1421615 : Blo 1421530 1421615 := bstep (se 1 (by rfl) ⟨1066211, by rfl⟩ : syracuseStep 1421615 = 2132423) B2132423
theorem B2134319 : Blo 1421530 2134319 := bstep (se 1 (by rfl) ⟨1600739, by rfl⟩ : syracuseStep 2134319 = 3201479) B3201479
theorem B10252615 : Blo 1421530 10252615 := bstep (se 1 (by rfl) ⟨7689461, by rfl⟩ : syracuseStep 10252615 = 15378923) B15378923
theorem B1421759 : Blo 1421530 1421759 := bstep (se 1 (by rfl) ⟨1066319, by rfl⟩ : syracuseStep 1421759 = 2132639) B2132639
theorem B1421791 : Blo 1421530 1421791 := bstep (se 1 (by rfl) ⟨1066343, by rfl⟩ : syracuseStep 1421791 = 2132687) B2132687
theorem B1421855 : Blo 1421530 1421855 := bstep (se 1 (by rfl) ⟨1066391, by rfl⟩ : syracuseStep 1421855 = 2132783) B2132783
theorem B2134559 : Blo 1421530 2134559 := bstep (se 1 (by rfl) ⟨1600919, by rfl⟩ : syracuseStep 2134559 = 3201839) B3201839
theorem B12153401 : Blo 1421530 12153401 := bstep (se 2 (by rfl) ⟨4557525, by rfl⟩ : syracuseStep 12153401 = 9115051) B9115051
theorem B2134619 : Blo 1421530 2134619 := bstep (se 1 (by rfl) ⟨1600964, by rfl⟩ : syracuseStep 2134619 = 3201929) B3201929
theorem B1421935 : Blo 1421530 1421935 := bstep (se 1 (by rfl) ⟨1066451, by rfl⟩ : syracuseStep 1421935 = 2132903) B2132903
theorem B1422055 : Blo 1421530 1422055 := bstep (se 1 (by rfl) ⟨1066541, by rfl⟩ : syracuseStep 1422055 = 2133083) B2133083
theorem B1422107 : Blo 1421530 1422107 := bstep (se 1 (by rfl) ⟨1066580, by rfl⟩ : syracuseStep 1422107 = 2133161) B2133161
theorem B2134823 : Blo 1421530 2134823 := bstep (se 1 (by rfl) ⟨1601117, by rfl⟩ : syracuseStep 2134823 = 3202235) B3202235
theorem B32027537 : Blo 1421530 32027537 := bstep (se 2 (by rfl) ⟨12010326, by rfl⟩ : syracuseStep 32027537 = 24020653) B24020653
theorem B2134991 : Blo 1421530 2134991 := bstep (se 1 (by rfl) ⟨1601243, by rfl⟩ : syracuseStep 2134991 = 3202487) B3202487
theorem B3199967 : Blo 1421530 3199967 := bstep (se 1 (by rfl) ⟨2399975, by rfl⟩ : syracuseStep 3199967 = 4799951) B4799951
theorem B7205921 : Blo 1421530 7205921 := bstep (se 2 (by rfl) ⟨2702220, by rfl⟩ : syracuseStep 7205921 = 5404441) B5404441
theorem B1422383 : Blo 1421530 1422383 := bstep (se 1 (by rfl) ⟨1066787, by rfl⟩ : syracuseStep 1422383 = 2133575) B2133575
theorem B2135111 : Blo 1421530 2135111 := bstep (se 1 (by rfl) ⟨1601333, by rfl⟩ : syracuseStep 2135111 = 3202667) B3202667
theorem B1422503 : Blo 1421530 1422503 := bstep (se 1 (by rfl) ⟨1066877, by rfl⟩ : syracuseStep 1422503 = 2133755) B2133755
theorem B96130223 : Blo 1421530 96130223 := bstep (se 1 (by rfl) ⟨72097667, by rfl⟩ : syracuseStep 96130223 = 144195335) B144195335
theorem B2135291 : Blo 1421530 2135291 := bstep (se 1 (by rfl) ⟨1601468, by rfl⟩ : syracuseStep 2135291 = 3202937) B3202937
theorem B1422663 : Blo 1421530 1422663 := bstep (se 1 (by rfl) ⟨1066997, by rfl⟩ : syracuseStep 1422663 = 2133995) B2133995
theorem B3036599 : Blo 1421530 3036599 := bstep (se 1 (by rfl) ⟨2277449, by rfl⟩ : syracuseStep 3036599 = 4554899) B4554899
theorem B11540159 : Blo 1421530 11540159 := bstep (se 1 (by rfl) ⟨8655119, by rfl⟩ : syracuseStep 11540159 = 17310239) B17310239
theorem B2701279 : Blo 1421530 2701279 := bstep (se 1 (by rfl) ⟨2025959, by rfl⟩ : syracuseStep 2701279 = 4051919) B4051919
theorem B1423355 : Blo 1421530 1423355 := bstep (se 1 (by rfl) ⟨1067516, by rfl⟩ : syracuseStep 1423355 = 2135033) B2135033
theorem B3602495 : Blo 1421530 3602495 := bstep (se 1 (by rfl) ⟨2701871, by rfl⟩ : syracuseStep 3602495 = 5403743) B5403743
theorem B7198793 : Blo 1421530 7198793 := bstep (se 2 (by rfl) ⟨2699547, by rfl⟩ : syracuseStep 7198793 = 5399095) B5399095
theorem B1423487 : Blo 1421530 1423487 := bstep (se 1 (by rfl) ⟨1067615, by rfl⟩ : syracuseStep 1423487 = 2135231) B2135231
theorem B4798601 : Blo 1421530 4798601 := bstep (se 2 (by rfl) ⟨1799475, by rfl⟩ : syracuseStep 4798601 = 3598951) B3598951
theorem B3037351 : Blo 1421530 3037351 := bstep (se 1 (by rfl) ⟨2278013, by rfl⟩ : syracuseStep 3037351 = 4556027) B4556027
theorem B5404927 : Blo 1421530 5404927 := bstep (se 1 (by rfl) ⟨4053695, by rfl⟩ : syracuseStep 5404927 = 8107391) B8107391
theorem B9615631 : Blo 1421530 9615631 := bstep (se 1 (by rfl) ⟨7211723, by rfl⟩ : syracuseStep 9615631 = 14423447) B14423447
theorem B1948063 : Blo 1421530 1948063 := bstep (se 1 (by rfl) ⟨1461047, by rfl⟩ : syracuseStep 1948063 = 2922095) B2922095
theorem B2399017 : Blo 1421530 2399017 := bstep (se 2 (by rfl) ⟨899631, by rfl⟩ : syracuseStep 2399017 = 1799263) B1799263
theorem B4799303 : Blo 1421530 4799303 := bstep (se 1 (by rfl) ⟨3599477, by rfl⟩ : syracuseStep 4799303 = 7198955) B7198955
theorem B3038239 : Blo 1421530 3038239 := bstep (se 1 (by rfl) ⟨2278679, by rfl⟩ : syracuseStep 3038239 = 4557359) B4557359
theorem B2882633 : Blo 1421530 2882633 := bstep (se 2 (by rfl) ⟨1080987, by rfl⟩ : syracuseStep 2882633 = 2161975) B2161975
theorem B6077537 : Blo 1421530 6077537 := bstep (se 2 (by rfl) ⟨2279076, by rfl⟩ : syracuseStep 6077537 = 4558153) B4558153
theorem B8101241 : Blo 1421530 8101241 := bstep (se 2 (by rfl) ⟨3037965, by rfl⟩ : syracuseStep 8101241 = 6075931) B6075931
theorem B4324763 : Blo 1421530 4324763 := bstep (se 1 (by rfl) ⟨3243572, by rfl⟩ : syracuseStep 4324763 = 6487145) B6487145
theorem B27344303 : Blo 1421530 27344303 := bstep (se 1 (by rfl) ⟨20508227, by rfl⟩ : syracuseStep 27344303 = 41016455) B41016455
theorem B133267031 : Blo 1421530 133267031 := bstep (se 1 (by rfl) ⟨99950273, by rfl⟩ : syracuseStep 133267031 = 199900547) B199900547
theorem B5398123 : Blo 1421530 5398123 := bstep (se 1 (by rfl) ⟨4048592, by rfl⟩ : syracuseStep 5398123 = 8097185) B8097185
theorem B20520863 : Blo 1421530 20520863 := bstep (se 1 (by rfl) ⟨15390647, by rfl⟩ : syracuseStep 20520863 = 30781295) B30781295
theorem B2400239 : Blo 1421530 2400239 := bstep (se 1 (by rfl) ⟨1800179, by rfl⟩ : syracuseStep 2400239 = 3600359) B3600359
theorem B4325615 : Blo 1421530 4325615 := bstep (se 1 (by rfl) ⟨3244211, by rfl⟩ : syracuseStep 4325615 = 6488423) B6488423
theorem B12820841 : Blo 1421530 12820841 := bstep (se 2 (by rfl) ⟨4807815, by rfl⟩ : syracuseStep 12820841 = 9615631) B9615631
theorem B8102267 : Blo 1421530 8102267 := bstep (se 1 (by rfl) ⟨6076700, by rfl⟩ : syracuseStep 8102267 = 12153401) B12153401
theorem B2597417 : Blo 1421530 2597417 := bstep (se 2 (by rfl) ⟨974031, by rfl⟩ : syracuseStep 2597417 = 1948063) B1948063
theorem B64086815 : Blo 1421530 64086815 := bstep (se 1 (by rfl) ⟨48065111, by rfl⟩ : syracuseStep 64086815 = 96130223) B96130223
theorem B2024399 : Blo 1421530 2024399 := bstep (se 1 (by rfl) ⟨1518299, by rfl⟩ : syracuseStep 2024399 = 3036599) B3036599
theorem B7693439 : Blo 1421530 7693439 := bstep (se 1 (by rfl) ⟨5770079, by rfl⟩ : syracuseStep 7693439 = 11540159) B11540159
theorem B4801787 : Blo 1421530 4801787 := bstep (se 1 (by rfl) ⟨3601340, by rfl⟩ : syracuseStep 4801787 = 7202681) B7202681
theorem B2401663 : Blo 1421530 2401663 := bstep (se 1 (by rfl) ⟨1801247, by rfl⟩ : syracuseStep 2401663 = 3602495) B3602495
theorem B5130287 : Blo 1421530 5130287 := bstep (se 1 (by rfl) ⟨3847715, by rfl⟩ : syracuseStep 5130287 = 7695431) B7695431
theorem B5400827 : Blo 1421530 5400827 := bstep (se 1 (by rfl) ⟨4050620, by rfl⟩ : syracuseStep 5400827 = 8101241) B8101241
theorem B18229535 : Blo 1421530 18229535 := bstep (se 1 (by rfl) ⟨13672151, by rfl⟩ : syracuseStep 18229535 = 27344303) B27344303
theorem B88844687 : Blo 1421530 88844687 := bstep (se 1 (by rfl) ⟨66633515, by rfl⟩ : syracuseStep 88844687 = 133267031) B133267031
theorem B6490651 : Blo 1421530 6490651 := bstep (se 1 (by rfl) ⟨4867988, by rfl⟩ : syracuseStep 6490651 = 9735977) B9735977
theorem B1600159 : Blo 1421530 1600159 := bstep (se 1 (by rfl) ⟨1200119, by rfl⟩ : syracuseStep 1600159 = 2400239) B2400239
theorem B43821739 : Blo 1421530 43821739 := bstep (se 1 (by rfl) ⟨32866304, by rfl⟩ : syracuseStep 43821739 = 65732609) B65732609
theorem B7687021 : Blo 1421530 7687021 := bstep (se 3 (by rfl) ⟨1441316, by rfl⟩ : syracuseStep 7687021 = 2882633) B2882633
theorem B4049801 : Blo 1421530 4049801 := bstep (se 2 (by rfl) ⟨1518675, by rfl⟩ : syracuseStep 4049801 = 3037351) B3037351
theorem B32828419 : Blo 1421530 32828419 := bstep (se 1 (by rfl) ⟨24621314, by rfl⟩ : syracuseStep 32828419 = 49242629) B49242629
theorem B5401799 : Blo 1421530 5401799 := bstep (se 1 (by rfl) ⟨4051349, by rfl⟩ : syracuseStep 5401799 = 8102699) B8102699
theorem B21351691 : Blo 1421530 21351691 := bstep (se 1 (by rfl) ⟨16013768, by rfl⟩ : syracuseStep 21351691 = 32027537) B32027537
theorem B2133311 : Blo 1421530 2133311 := bstep (se 1 (by rfl) ⟨1599983, by rfl⟩ : syracuseStep 2133311 = 3199967) B3199967
theorem B4803947 : Blo 1421530 4803947 := bstep (se 1 (by rfl) ⟨3602960, by rfl⟩ : syracuseStep 4803947 = 7205921) B7205921
theorem B10948225 : Blo 1421530 10948225 := bstep (se 2 (by rfl) ⟨4105584, by rfl⟩ : syracuseStep 10948225 = 8211169) B8211169
theorem B3198689 : Blo 1421530 3198689 := bstep (se 2 (by rfl) ⟨1199508, by rfl⟩ : syracuseStep 3198689 = 2399017) B2399017
theorem B1601311 : Blo 1421530 1601311 := bstep (se 1 (by rfl) ⟨1200983, by rfl⟩ : syracuseStep 1601311 = 2401967) B2401967
theorem B4050985 : Blo 1421530 4050985 := bstep (se 2 (by rfl) ⟨1519119, by rfl⟩ : syracuseStep 4050985 = 3038239) B3038239
theorem B3199067 : Blo 1421530 3199067 := bstep (se 1 (by rfl) ⟨2399300, by rfl⟩ : syracuseStep 3199067 = 4798601) B4798601
theorem B1421823 : Blo 1421530 1421823 := bstep (se 1 (by rfl) ⟨1066367, by rfl⟩ : syracuseStep 1421823 = 2132735) B2132735
theorem B3199535 : Blo 1421530 3199535 := bstep (se 1 (by rfl) ⟨2399651, by rfl⟩ : syracuseStep 3199535 = 4799303) B4799303
theorem B4051691 : Blo 1421530 4051691 := bstep (se 1 (by rfl) ⟨3038768, by rfl⟩ : syracuseStep 4051691 = 6077537) B6077537
theorem B7197497 : Blo 1421530 7197497 := bstep (se 2 (by rfl) ⟨2699061, by rfl⟩ : syracuseStep 7197497 = 5398123) B5398123
theorem B1422447 : Blo 1421530 1422447 := bstep (se 1 (by rfl) ⟨1066835, by rfl⟩ : syracuseStep 1422447 = 2133671) B2133671
theorem B1422527 : Blo 1421530 1422527 := bstep (se 1 (by rfl) ⟨1066895, by rfl⟩ : syracuseStep 1422527 = 2133791) B2133791
theorem B1422559 : Blo 1421530 1422559 := bstep (se 1 (by rfl) ⟨1066919, by rfl⟩ : syracuseStep 1422559 = 2133839) B2133839
theorem B4797737 : Blo 1421530 4797737 := bstep (se 2 (by rfl) ⟨1799151, by rfl⟩ : syracuseStep 4797737 = 3598303) B3598303
theorem B3601705 : Blo 1421530 3601705 := bstep (se 2 (by rfl) ⟨1350639, by rfl⟩ : syracuseStep 3601705 = 2701279) B2701279
theorem B1422639 : Blo 1421530 1422639 := bstep (se 1 (by rfl) ⟨1066979, by rfl⟩ : syracuseStep 1422639 = 2133959) B2133959
theorem B1422799 : Blo 1421530 1422799 := bstep (se 1 (by rfl) ⟨1067099, by rfl⟩ : syracuseStep 1422799 = 2134199) B2134199
theorem B6075881 : Blo 1421530 6075881 := bstep (se 2 (by rfl) ⟨2278455, by rfl⟩ : syracuseStep 6075881 = 4556911) B4556911
theorem B1422847 : Blo 1421530 1422847 := bstep (se 1 (by rfl) ⟨1067135, by rfl⟩ : syracuseStep 1422847 = 2134271) B2134271
theorem B1422879 : Blo 1421530 1422879 := bstep (se 1 (by rfl) ⟨1067159, by rfl⟩ : syracuseStep 1422879 = 2134319) B2134319
theorem B7206569 : Blo 1421530 7206569 := bstep (se 2 (by rfl) ⟨2702463, by rfl⟩ : syracuseStep 7206569 = 5404927) B5404927
theorem B1423039 : Blo 1421530 1423039 := bstep (se 1 (by rfl) ⟨1067279, by rfl⟩ : syracuseStep 1423039 = 2134559) B2134559
theorem B29185757 : Blo 1421530 29185757 := bstep (se 3 (by rfl) ⟨5472329, by rfl⟩ : syracuseStep 29185757 = 10944659) B10944659
theorem B1423079 : Blo 1421530 1423079 := bstep (se 1 (by rfl) ⟨1067309, by rfl⟩ : syracuseStep 1423079 = 2134619) B2134619
theorem B14046979 : Blo 1421530 14046979 := bstep (se 1 (by rfl) ⟨10535234, by rfl⟩ : syracuseStep 14046979 = 21070469) B21070469
theorem B13670153 : Blo 1421530 13670153 := bstep (se 2 (by rfl) ⟨5126307, by rfl⟩ : syracuseStep 13670153 = 10252615) B10252615
theorem B1423215 : Blo 1421530 1423215 := bstep (se 1 (by rfl) ⟨1067411, by rfl⟩ : syracuseStep 1423215 = 2134823) B2134823
theorem B7198631 : Blo 1421530 7198631 := bstep (se 1 (by rfl) ⟨5398973, by rfl⟩ : syracuseStep 7198631 = 10797947) B10797947
theorem B1423327 : Blo 1421530 1423327 := bstep (se 1 (by rfl) ⟨1067495, by rfl⟩ : syracuseStep 1423327 = 2134991) B2134991
theorem B1423407 : Blo 1421530 1423407 := bstep (se 1 (by rfl) ⟨1067555, by rfl⟩ : syracuseStep 1423407 = 2135111) B2135111
theorem B1423527 : Blo 1421530 1423527 := bstep (se 1 (by rfl) ⟨1067645, by rfl⟩ : syracuseStep 1423527 = 2135291) B2135291
theorem B11532701 : Blo 1421530 11532701 := bstep (se 3 (by rfl) ⟨2162381, by rfl⟩ : syracuseStep 11532701 = 4324763) B4324763
theorem B3201695 : Blo 1421530 3201695 := bstep (se 1 (by rfl) ⟨2401271, by rfl⟩ : syracuseStep 3201695 = 4802543) B4802543
theorem B4799195 : Blo 1421530 4799195 := bstep (se 1 (by rfl) ⟨3599396, by rfl⟩ : syracuseStep 4799195 = 7198793) B7198793
theorem B3201767 : Blo 1421530 3201767 := bstep (se 1 (by rfl) ⟨2401325, by rfl⟩ : syracuseStep 3201767 = 4802651) B4802651
theorem B41032493 : Blo 1421530 41032493 := bstep (se 3 (by rfl) ⟨7693592, by rfl⟩ : syracuseStep 41032493 = 15387185) B15387185
theorem B2563039 : Blo 1421530 2563039 := bstep (se 1 (by rfl) ⟨1922279, by rfl⟩ : syracuseStep 2563039 = 3844559) B3844559
theorem B7200251 : Blo 1421530 7200251 := bstep (se 1 (by rfl) ⟨5400188, by rfl⟩ : syracuseStep 7200251 = 10800377) B10800377
theorem B16211501 : Blo 1421530 16211501 := bstep (se 3 (by rfl) ⟨3039656, by rfl⟩ : syracuseStep 16211501 = 6079313) B6079313
theorem B12148649 : Blo 1421530 12148649 := bstep (se 2 (by rfl) ⟨4555743, by rfl⟩ : syracuseStep 12148649 = 9111487) B9111487
theorem B13680575 : Blo 1421530 13680575 := bstep (se 1 (by rfl) ⟨10260431, by rfl⟩ : syracuseStep 13680575 = 20520863) B20520863
theorem B2883743 : Blo 1421530 2883743 := bstep (se 1 (by rfl) ⟨2162807, by rfl⟩ : syracuseStep 2883743 = 4325615) B4325615
theorem B10249361 : Blo 1421530 10249361 := bstep (se 2 (by rfl) ⟨3843510, by rfl⟩ : syracuseStep 10249361 = 7687021) B7687021
theorem B19457171 : Blo 1421530 19457171 := bstep (se 1 (by rfl) ⟨14592878, by rfl⟩ : syracuseStep 19457171 = 29185757) B29185757
theorem B3417385 : Blo 1421530 3417385 := bstep (se 2 (by rfl) ⟨1281519, by rfl⟩ : syracuseStep 3417385 = 2563039) B2563039
theorem B59229791 : Blo 1421530 59229791 := bstep (se 1 (by rfl) ⟨44422343, by rfl⟩ : syracuseStep 59229791 = 88844687) B88844687
theorem B28468921 : Blo 1421530 28468921 := bstep (se 2 (by rfl) ⟨10675845, by rfl⟩ : syracuseStep 28468921 = 21351691) B21351691
theorem B4802273 : Blo 1421530 4802273 := bstep (se 2 (by rfl) ⟨1800852, by rfl⟩ : syracuseStep 4802273 = 3601705) B3601705
theorem B27354995 : Blo 1421530 27354995 := bstep (se 1 (by rfl) ⟨20516246, by rfl⟩ : syracuseStep 27354995 = 41032493) B41032493
theorem B18729305 : Blo 1421530 18729305 := bstep (se 2 (by rfl) ⟨7023489, by rfl⟩ : syracuseStep 18729305 = 14046979) B14046979
theorem B10807667 : Blo 1421530 10807667 := bstep (se 1 (by rfl) ⟨8105750, by rfl⟩ : syracuseStep 10807667 = 16211501) B16211501
theorem B2132459 : Blo 1421530 2132459 := bstep (se 1 (by rfl) ⟨1599344, by rfl⟩ : syracuseStep 2132459 = 3198689) B3198689
theorem B9120383 : Blo 1421530 9120383 := bstep (se 1 (by rfl) ⟨6840287, by rfl⟩ : syracuseStep 9120383 = 13680575) B13680575
theorem B5401313 : Blo 1421530 5401313 := bstep (se 2 (by rfl) ⟨2025492, by rfl⟩ : syracuseStep 5401313 = 4050985) B4050985
theorem B2132711 : Blo 1421530 2132711 := bstep (se 1 (by rfl) ⟨1599533, by rfl⟩ : syracuseStep 2132711 = 3199067) B3199067
theorem B8547227 : Blo 1421530 8547227 := bstep (se 1 (by rfl) ⟨6410420, by rfl⟩ : syracuseStep 8547227 = 12820841) B12820841
theorem B5401511 : Blo 1421530 5401511 := bstep (se 1 (by rfl) ⟨4051133, by rfl⟩ : syracuseStep 5401511 = 8102267) B8102267
theorem B20515837 : Blo 1421530 20515837 := bstep (se 3 (by rfl) ⟨3846719, by rfl⟩ : syracuseStep 20515837 = 7693439) B7693439
theorem B1731611 : Blo 1421530 1731611 := bstep (se 1 (by rfl) ⟨1298708, by rfl⟩ : syracuseStep 1731611 = 2597417) B2597417
theorem B2133023 : Blo 1421530 2133023 := bstep (se 1 (by rfl) ⟨1599767, by rfl⟩ : syracuseStep 2133023 = 3199535) B3199535
theorem B8654201 : Blo 1421530 8654201 := bstep (se 2 (by rfl) ⟨3245325, by rfl⟩ : syracuseStep 8654201 = 6490651) B6490651
theorem B3198491 : Blo 1421530 3198491 := bstep (se 1 (by rfl) ⟨2398868, by rfl⟩ : syracuseStep 3198491 = 4797737) B4797737
theorem B2133545 : Blo 1421530 2133545 := bstep (se 2 (by rfl) ⟨800079, by rfl⟩ : syracuseStep 2133545 = 1600159) B1600159
theorem B58428985 : Blo 1421530 58428985 := bstep (se 2 (by rfl) ⟨21910869, by rfl⟩ : syracuseStep 58428985 = 43821739) B43821739
theorem B4050587 : Blo 1421530 4050587 := bstep (se 1 (by rfl) ⟨3037940, by rfl⟩ : syracuseStep 4050587 = 6075881) B6075881
theorem B4804379 : Blo 1421530 4804379 := bstep (se 1 (by rfl) ⟨3603284, by rfl⟩ : syracuseStep 4804379 = 7206569) B7206569
theorem B9113435 : Blo 1421530 9113435 := bstep (se 1 (by rfl) ⟨6835076, by rfl⟩ : syracuseStep 9113435 = 13670153) B13670153
theorem B3420191 : Blo 1421530 3420191 := bstep (se 1 (by rfl) ⟨2565143, by rfl⟩ : syracuseStep 3420191 = 5130287) B5130287
theorem B3600551 : Blo 1421530 3600551 := bstep (se 1 (by rfl) ⟨2700413, by rfl⟩ : syracuseStep 3600551 = 5400827) B5400827
theorem B12153023 : Blo 1421530 12153023 := bstep (se 1 (by rfl) ⟨9114767, by rfl⟩ : syracuseStep 12153023 = 18229535) B18229535
theorem B7688467 : Blo 1421530 7688467 := bstep (se 1 (by rfl) ⟨5766350, by rfl⟩ : syracuseStep 7688467 = 11532701) B11532701
theorem B2134463 : Blo 1421530 2134463 := bstep (se 1 (by rfl) ⟨1600847, by rfl⟩ : syracuseStep 2134463 = 3201695) B3201695
theorem B3199463 : Blo 1421530 3199463 := bstep (se 1 (by rfl) ⟨2399597, by rfl⟩ : syracuseStep 3199463 = 4799195) B4799195
theorem B2134511 : Blo 1421530 2134511 := bstep (se 1 (by rfl) ⟨1600883, by rfl⟩ : syracuseStep 2134511 = 3201767) B3201767
theorem B2699867 : Blo 1421530 2699867 := bstep (se 1 (by rfl) ⟨2024900, by rfl⟩ : syracuseStep 2699867 = 4049801) B4049801
theorem B170898173 : Blo 1421530 170898173 := bstep (se 3 (by rfl) ⟨32043407, by rfl⟩ : syracuseStep 170898173 = 64086815) B64086815
theorem B3601199 : Blo 1421530 3601199 := bstep (se 1 (by rfl) ⟨2700899, by rfl⟩ : syracuseStep 3601199 = 5401799) B5401799
theorem B1422207 : Blo 1421530 1422207 := bstep (se 1 (by rfl) ⟨1066655, by rfl⟩ : syracuseStep 1422207 = 2133311) B2133311
theorem B2135081 : Blo 1421530 2135081 := bstep (se 2 (by rfl) ⟨800655, by rfl⟩ : syracuseStep 2135081 = 1601311) B1601311
theorem B8099099 : Blo 1421530 8099099 := bstep (se 1 (by rfl) ⟨6074324, by rfl⟩ : syracuseStep 8099099 = 12148649) B12148649
theorem B175084901 : Blo 1421530 175084901 := bstep (se 4 (by rfl) ⟨16414209, by rfl⟩ : syracuseStep 175084901 = 32828419) B32828419
theorem B2701127 : Blo 1421530 2701127 := bstep (se 1 (by rfl) ⟨2025845, by rfl⟩ : syracuseStep 2701127 = 4051691) B4051691
theorem B4798331 : Blo 1421530 4798331 := bstep (se 1 (by rfl) ⟨3598748, by rfl⟩ : syracuseStep 4798331 = 7197497) B7197497
theorem B3201191 : Blo 1421530 3201191 := bstep (se 1 (by rfl) ⟨2400893, by rfl⟩ : syracuseStep 3201191 = 4801787) B4801787
theorem B4799087 : Blo 1421530 4799087 := bstep (se 1 (by rfl) ⟨3599315, by rfl⟩ : syracuseStep 4799087 = 7198631) B7198631
theorem B3202217 : Blo 1421530 3202217 := bstep (se 2 (by rfl) ⟨1200831, by rfl⟩ : syracuseStep 3202217 = 2401663) B2401663
theorem B14597633 : Blo 1421530 14597633 := bstep (se 2 (by rfl) ⟨5474112, by rfl⟩ : syracuseStep 14597633 = 10948225) B10948225
theorem B3202631 : Blo 1421530 3202631 := bstep (se 1 (by rfl) ⟨2401973, by rfl⟩ : syracuseStep 3202631 = 4803947) B4803947
theorem B4800167 : Blo 1421530 4800167 := bstep (se 1 (by rfl) ⟨3600125, by rfl⟩ : syracuseStep 4800167 = 7200251) B7200251
theorem B5398397 : Blo 1421530 5398397 := bstep (se 3 (by rfl) ⟨1012199, by rfl⟩ : syracuseStep 5398397 = 2024399) B2024399
theorem B2400367 : Blo 1421530 2400367 := bstep (se 1 (by rfl) ⟨1800275, by rfl⟩ : syracuseStep 2400367 = 3600551) B3600551
theorem B8102015 : Blo 1421530 8102015 := bstep (se 1 (by rfl) ⟨6076511, by rfl⟩ : syracuseStep 8102015 = 12153023) B12153023
theorem B2400799 : Blo 1421530 2400799 := bstep (se 1 (by rfl) ⟨1800599, by rfl⟩ : syracuseStep 2400799 = 3601199) B3601199
theorem B6832907 : Blo 1421530 6832907 := bstep (se 1 (by rfl) ⟨5124680, by rfl⟩ : syracuseStep 6832907 = 10249361) B10249361
theorem B5399399 : Blo 1421530 5399399 := bstep (se 1 (by rfl) ⟨4049549, by rfl⟩ : syracuseStep 5399399 = 8099099) B8099099
theorem B39486527 : Blo 1421530 39486527 := bstep (se 1 (by rfl) ⟨29614895, by rfl⟩ : syracuseStep 39486527 = 59229791) B59229791
theorem B18236663 : Blo 1421530 18236663 := bstep (se 1 (by rfl) ⟨13677497, by rfl⟩ : syracuseStep 18236663 = 27354995) B27354995
theorem B27354449 : Blo 1421530 27354449 := bstep (se 2 (by rfl) ⟨10257918, by rfl⟩ : syracuseStep 27354449 = 20515837) B20515837
theorem B12486203 : Blo 1421530 12486203 := bstep (se 1 (by rfl) ⟨9364652, by rfl⟩ : syracuseStep 12486203 = 18729305) B18729305
theorem B4556513 : Blo 1421530 4556513 := bstep (se 2 (by rfl) ⟨1708692, by rfl⟩ : syracuseStep 4556513 = 3417385) B3417385
theorem B6080255 : Blo 1421530 6080255 := bstep (se 1 (by rfl) ⟨4560191, by rfl⟩ : syracuseStep 6080255 = 9120383) B9120383
theorem B7203005 : Blo 1421530 7203005 := bstep (se 3 (by rfl) ⟨1350563, by rfl⟩ : syracuseStep 7203005 = 2701127) B2701127
theorem B5769467 : Blo 1421530 5769467 := bstep (se 1 (by rfl) ⟨4327100, by rfl⟩ : syracuseStep 5769467 = 8654201) B8654201
theorem B2132327 : Blo 1421530 2132327 := bstep (se 1 (by rfl) ⟨1599245, by rfl⟩ : syracuseStep 2132327 = 3198491) B3198491
theorem B3598931 : Blo 1421530 3598931 := bstep (se 1 (by rfl) ⟨2699198, by rfl⟩ : syracuseStep 3598931 = 5398397) B5398397
theorem B9120509 : Blo 1421530 9120509 := bstep (se 3 (by rfl) ⟨1710095, by rfl⟩ : syracuseStep 9120509 = 3420191) B3420191
theorem B2132975 : Blo 1421530 2132975 := bstep (se 1 (by rfl) ⟨1599731, by rfl⟩ : syracuseStep 2132975 = 3199463) B3199463
theorem B10251289 : Blo 1421530 10251289 := bstep (se 2 (by rfl) ⟨3844233, by rfl⟩ : syracuseStep 10251289 = 7688467) B7688467
theorem B12971447 : Blo 1421530 12971447 := bstep (se 1 (by rfl) ⟨9728585, by rfl⟩ : syracuseStep 12971447 = 19457171) B19457171
theorem B116723267 : Blo 1421530 116723267 := bstep (se 1 (by rfl) ⟨87542450, by rfl⟩ : syracuseStep 116723267 = 175084901) B175084901
theorem B3198887 : Blo 1421530 3198887 := bstep (se 1 (by rfl) ⟨2399165, by rfl⟩ : syracuseStep 3198887 = 4798331) B4798331
theorem B2134127 : Blo 1421530 2134127 := bstep (se 1 (by rfl) ⟨1600595, by rfl⟩ : syracuseStep 2134127 = 3201191) B3201191
theorem B7205111 : Blo 1421530 7205111 := bstep (se 1 (by rfl) ⟨5403833, by rfl⟩ : syracuseStep 7205111 = 10807667) B10807667
theorem B1421639 : Blo 1421530 1421639 := bstep (se 1 (by rfl) ⟨1066229, by rfl⟩ : syracuseStep 1421639 = 2132459) B2132459
theorem B3199391 : Blo 1421530 3199391 := bstep (se 1 (by rfl) ⟨2399543, by rfl⟩ : syracuseStep 3199391 = 4799087) B4799087
theorem B3600875 : Blo 1421530 3600875 := bstep (se 1 (by rfl) ⟨2700656, by rfl⟩ : syracuseStep 3600875 = 5401313) B5401313
theorem B1421807 : Blo 1421530 1421807 := bstep (se 1 (by rfl) ⟨1066355, by rfl⟩ : syracuseStep 1421807 = 2132711) B2132711
theorem B5698151 : Blo 1421530 5698151 := bstep (se 1 (by rfl) ⟨4273613, by rfl⟩ : syracuseStep 5698151 = 8547227) B8547227
theorem B3601007 : Blo 1421530 3601007 := bstep (se 1 (by rfl) ⟨2700755, by rfl⟩ : syracuseStep 3601007 = 5401511) B5401511
theorem B1422015 : Blo 1421530 1422015 := bstep (se 1 (by rfl) ⟨1066511, by rfl⟩ : syracuseStep 1422015 = 2133023) B2133023
theorem B2134811 : Blo 1421530 2134811 := bstep (se 1 (by rfl) ⟨1601108, by rfl⟩ : syracuseStep 2134811 = 3202217) B3202217
theorem B37958561 : Blo 1421530 37958561 := bstep (se 2 (by rfl) ⟨14234460, by rfl⟩ : syracuseStep 37958561 = 28468921) B28468921
theorem B1422363 : Blo 1421530 1422363 := bstep (se 1 (by rfl) ⟨1066772, by rfl⟩ : syracuseStep 1422363 = 2133545) B2133545
theorem B2135087 : Blo 1421530 2135087 := bstep (se 1 (by rfl) ⟨1601315, by rfl⟩ : syracuseStep 2135087 = 3202631) B3202631
theorem B2700391 : Blo 1421530 2700391 := bstep (se 1 (by rfl) ⟨2025293, by rfl⟩ : syracuseStep 2700391 = 4050587) B4050587
theorem B3200111 : Blo 1421530 3200111 := bstep (se 1 (by rfl) ⟨2400083, by rfl⟩ : syracuseStep 3200111 = 4800167) B4800167
theorem B6075623 : Blo 1421530 6075623 := bstep (se 1 (by rfl) ⟨4556717, by rfl⟩ : syracuseStep 6075623 = 9113435) B9113435
theorem B4617629 : Blo 1421530 4617629 := bstep (se 3 (by rfl) ⟨865805, by rfl⟩ : syracuseStep 4617629 = 1731611) B1731611
theorem B1922495 : Blo 1421530 1922495 := bstep (se 1 (by rfl) ⟨1441871, by rfl⟩ : syracuseStep 1922495 = 2883743) B2883743
theorem B1422975 : Blo 1421530 1422975 := bstep (se 1 (by rfl) ⟨1067231, by rfl⟩ : syracuseStep 1422975 = 2134463) B2134463
theorem B1423007 : Blo 1421530 1423007 := bstep (se 1 (by rfl) ⟨1067255, by rfl⟩ : syracuseStep 1423007 = 2134511) B2134511
theorem B1799911 : Blo 1421530 1799911 := bstep (se 1 (by rfl) ⟨1349933, by rfl⟩ : syracuseStep 1799911 = 2699867) B2699867
theorem B113932115 : Blo 1421530 113932115 := bstep (se 1 (by rfl) ⟨85449086, by rfl⟩ : syracuseStep 113932115 = 170898173) B170898173
theorem B1423387 : Blo 1421530 1423387 := bstep (se 1 (by rfl) ⟨1067540, by rfl⟩ : syracuseStep 1423387 = 2135081) B2135081
theorem B3201515 : Blo 1421530 3201515 := bstep (se 1 (by rfl) ⟨2401136, by rfl⟩ : syracuseStep 3201515 = 4802273) B4802273
theorem B77905313 : Blo 1421530 77905313 := bstep (se 2 (by rfl) ⟨29214492, by rfl⟩ : syracuseStep 77905313 = 58428985) B58428985
theorem B9731755 : Blo 1421530 9731755 := bstep (se 1 (by rfl) ⟨7298816, by rfl⟩ : syracuseStep 9731755 = 14597633) B14597633
theorem B3202919 : Blo 1421530 3202919 := bstep (se 1 (by rfl) ⟨2402189, by rfl⟩ : syracuseStep 3202919 = 4804379) B4804379
theorem B2400583 : Blo 1421530 2400583 := bstep (se 1 (by rfl) ⟨1800437, by rfl⟩ : syracuseStep 2400583 = 3600875) B3600875
theorem B2400671 : Blo 1421530 2400671 := bstep (se 1 (by rfl) ⟨1800503, by rfl⟩ : syracuseStep 2400671 = 3601007) B3601007
theorem B4555271 : Blo 1421530 4555271 := bstep (se 1 (by rfl) ⟨3416453, by rfl⟩ : syracuseStep 4555271 = 6832907) B6832907
theorem B25305707 : Blo 1421530 25305707 := bstep (se 1 (by rfl) ⟨18979280, by rfl⟩ : syracuseStep 25305707 = 37958561) B37958561
theorem B12157775 : Blo 1421530 12157775 := bstep (se 1 (by rfl) ⟨9118331, by rfl⟩ : syracuseStep 12157775 = 18236663) B18236663
theorem B18236299 : Blo 1421530 18236299 := bstep (se 1 (by rfl) ⟨13677224, by rfl⟩ : syracuseStep 18236299 = 27354449) B27354449
theorem B8324135 : Blo 1421530 8324135 := bstep (se 1 (by rfl) ⟨6243101, by rfl⟩ : syracuseStep 8324135 = 12486203) B12486203
theorem B4802003 : Blo 1421530 4802003 := bstep (se 1 (by rfl) ⟨3601502, by rfl⟩ : syracuseStep 4802003 = 7203005) B7203005
theorem B6080339 : Blo 1421530 6080339 := bstep (se 1 (by rfl) ⟨4560254, by rfl⟩ : syracuseStep 6080339 = 9120509) B9120509
theorem B2132591 : Blo 1421530 2132591 := bstep (se 1 (by rfl) ⟨1599443, by rfl⟩ : syracuseStep 2132591 = 3198887) B3198887
theorem B5401343 : Blo 1421530 5401343 := bstep (se 1 (by rfl) ⟨4051007, by rfl⟩ : syracuseStep 5401343 = 8102015) B8102015
theorem B4803407 : Blo 1421530 4803407 := bstep (se 1 (by rfl) ⟨3602555, by rfl⟩ : syracuseStep 4803407 = 7205111) B7205111
theorem B2132927 : Blo 1421530 2132927 := bstep (se 1 (by rfl) ⟨1599695, by rfl⟩ : syracuseStep 2132927 = 3199391) B3199391
theorem B3599599 : Blo 1421530 3599599 := bstep (se 1 (by rfl) ⟨2699699, by rfl⟩ : syracuseStep 3599599 = 5399399) B5399399
theorem B26324351 : Blo 1421530 26324351 := bstep (se 1 (by rfl) ⟨19743263, by rfl⟩ : syracuseStep 26324351 = 39486527) B39486527
theorem B2133407 : Blo 1421530 2133407 := bstep (se 1 (by rfl) ⟨1600055, by rfl⟩ : syracuseStep 2133407 = 3200111) B3200111
theorem B4050415 : Blo 1421530 4050415 := bstep (se 1 (by rfl) ⟨3037811, by rfl⟩ : syracuseStep 4050415 = 6075623) B6075623
theorem B13668385 : Blo 1421530 13668385 := bstep (se 2 (by rfl) ⟨5125644, by rfl⟩ : syracuseStep 13668385 = 10251289) B10251289
theorem B3600521 : Blo 1421530 3600521 := bstep (se 2 (by rfl) ⟨1350195, by rfl⟩ : syracuseStep 3600521 = 2700391) B2700391
theorem B3846311 : Blo 1421530 3846311 := bstep (se 1 (by rfl) ⟨2884733, by rfl⟩ : syracuseStep 3846311 = 5769467) B5769467
theorem B1421551 : Blo 1421530 1421551 := bstep (se 1 (by rfl) ⟨1066163, by rfl⟩ : syracuseStep 1421551 = 2132327) B2132327
theorem B2134343 : Blo 1421530 2134343 := bstep (se 1 (by rfl) ⟨1600757, by rfl⟩ : syracuseStep 2134343 = 3201515) B3201515
theorem B1421983 : Blo 1421530 1421983 := bstep (se 1 (by rfl) ⟨1066487, by rfl⟩ : syracuseStep 1421983 = 2132975) B2132975
theorem B8647631 : Blo 1421530 8647631 := bstep (se 1 (by rfl) ⟨6485723, by rfl⟩ : syracuseStep 8647631 = 12971447) B12971447
theorem B2135279 : Blo 1421530 2135279 := bstep (se 1 (by rfl) ⟨1601459, by rfl⟩ : syracuseStep 2135279 = 3202919) B3202919
theorem B1422751 : Blo 1421530 1422751 := bstep (se 1 (by rfl) ⟨1067063, by rfl⟩ : syracuseStep 1422751 = 2134127) B2134127
theorem B3200489 : Blo 1421530 3200489 := bstep (se 2 (by rfl) ⟨1200183, by rfl⟩ : syracuseStep 3200489 = 2400367) B2400367
theorem B3798767 : Blo 1421530 3798767 := bstep (se 1 (by rfl) ⟨2849075, by rfl⟩ : syracuseStep 3798767 = 5698151) B5698151
theorem B1423207 : Blo 1421530 1423207 := bstep (se 1 (by rfl) ⟨1067405, by rfl⟩ : syracuseStep 1423207 = 2134811) B2134811
theorem B1423391 : Blo 1421530 1423391 := bstep (se 1 (by rfl) ⟨1067543, by rfl⟩ : syracuseStep 1423391 = 2135087) B2135087
theorem B3201065 : Blo 1421530 3201065 := bstep (se 2 (by rfl) ⟨1200399, by rfl⟩ : syracuseStep 3201065 = 2400799) B2400799
theorem B3078419 : Blo 1421530 3078419 := bstep (se 1 (by rfl) ⟨2308814, by rfl⟩ : syracuseStep 3078419 = 4617629) B4617629
theorem B3037675 : Blo 1421530 3037675 := bstep (se 1 (by rfl) ⟨2278256, by rfl⟩ : syracuseStep 3037675 = 4556513) B4556513
theorem B5126653 : Blo 1421530 5126653 := bstep (se 3 (by rfl) ⟨961247, by rfl⟩ : syracuseStep 5126653 = 1922495) B1922495
theorem B4053503 : Blo 1421530 4053503 := bstep (se 1 (by rfl) ⟨3040127, by rfl⟩ : syracuseStep 4053503 = 6080255) B6080255
theorem B75954743 : Blo 1421530 75954743 := bstep (se 1 (by rfl) ⟨56966057, by rfl⟩ : syracuseStep 75954743 = 113932115) B113932115
theorem B2399287 : Blo 1421530 2399287 := bstep (se 1 (by rfl) ⟨1799465, by rfl⟩ : syracuseStep 2399287 = 3598931) B3598931
theorem B12975673 : Blo 1421530 12975673 := bstep (se 2 (by rfl) ⟨4865877, by rfl⟩ : syracuseStep 12975673 = 9731755) B9731755
theorem B51936875 : Blo 1421530 51936875 := bstep (se 1 (by rfl) ⟨38952656, by rfl⟩ : syracuseStep 51936875 = 77905313) B77905313
theorem B2399881 : Blo 1421530 2399881 := bstep (se 2 (by rfl) ⟨899955, by rfl⟩ : syracuseStep 2399881 = 1799911) B1799911
theorem B77815511 : Blo 1421530 77815511 := bstep (se 1 (by rfl) ⟨58361633, by rfl⟩ : syracuseStep 77815511 = 116723267) B116723267
theorem B2400347 : Blo 1421530 2400347 := bstep (se 1 (by rfl) ⟨1800260, by rfl⟩ : syracuseStep 2400347 = 3600521) B3600521
theorem B2564207 : Blo 1421530 2564207 := bstep (se 1 (by rfl) ⟨1923155, by rfl⟩ : syracuseStep 2564207 = 3846311) B3846311
theorem B8209117 : Blo 1421530 8209117 := bstep (se 3 (by rfl) ⟨1539209, by rfl⟩ : syracuseStep 8209117 = 3078419) B3078419
theorem B2532511 : Blo 1421530 2532511 := bstep (se 1 (by rfl) ⟨1899383, by rfl⟩ : syracuseStep 2532511 = 3798767) B3798767
theorem B24315065 : Blo 1421530 24315065 := bstep (se 2 (by rfl) ⟨9118149, by rfl⟩ : syracuseStep 24315065 = 18236299) B18236299
theorem B50636495 : Blo 1421530 50636495 := bstep (se 1 (by rfl) ⟨37977371, by rfl⟩ : syracuseStep 50636495 = 75954743) B75954743
theorem B5400553 : Blo 1421530 5400553 := bstep (se 2 (by rfl) ⟨2025207, by rfl⟩ : syracuseStep 5400553 = 4050415) B4050415
theorem B17549567 : Blo 1421530 17549567 := bstep (se 1 (by rfl) ⟨13162175, by rfl⟩ : syracuseStep 17549567 = 26324351) B26324351
theorem B1600447 : Blo 1421530 1600447 := bstep (se 1 (by rfl) ⟨1200335, by rfl⟩ : syracuseStep 1600447 = 2400671) B2400671
theorem B8105183 : Blo 1421530 8105183 := bstep (se 1 (by rfl) ⟨6078887, by rfl⟩ : syracuseStep 8105183 = 12157775) B12157775
theorem B4050233 : Blo 1421530 4050233 := bstep (se 2 (by rfl) ⟨1518837, by rfl⟩ : syracuseStep 4050233 = 3037675) B3037675
theorem B6835537 : Blo 1421530 6835537 := bstep (se 2 (by rfl) ⟨2563326, by rfl⟩ : syracuseStep 6835537 = 5126653) B5126653
theorem B5549423 : Blo 1421530 5549423 := bstep (se 1 (by rfl) ⟨4162067, by rfl⟩ : syracuseStep 5549423 = 8324135) B8324135
theorem B2133659 : Blo 1421530 2133659 := bstep (se 1 (by rfl) ⟨1600244, by rfl⟩ : syracuseStep 2133659 = 3200489) B3200489
theorem B2134043 : Blo 1421530 2134043 := bstep (se 1 (by rfl) ⟨1600532, by rfl⟩ : syracuseStep 2134043 = 3201065) B3201065
theorem B3199049 : Blo 1421530 3199049 := bstep (se 2 (by rfl) ⟨1199643, by rfl⟩ : syracuseStep 3199049 = 2399287) B2399287
theorem B67481885 : Blo 1421530 67481885 := bstep (se 3 (by rfl) ⟨12652853, by rfl⟩ : syracuseStep 67481885 = 25305707) B25305707
theorem B1421727 : Blo 1421530 1421727 := bstep (se 1 (by rfl) ⟨1066295, by rfl⟩ : syracuseStep 1421727 = 2132591) B2132591
theorem B3600895 : Blo 1421530 3600895 := bstep (se 1 (by rfl) ⟨2700671, by rfl⟩ : syracuseStep 3600895 = 5401343) B5401343
theorem B1421951 : Blo 1421530 1421951 := bstep (se 1 (by rfl) ⟨1066463, by rfl⟩ : syracuseStep 1421951 = 2132927) B2132927
theorem B3199841 : Blo 1421530 3199841 := bstep (se 2 (by rfl) ⟨1199940, by rfl⟩ : syracuseStep 3199841 = 2399881) B2399881
theorem B1422271 : Blo 1421530 1422271 := bstep (se 1 (by rfl) ⟨1066703, by rfl⟩ : syracuseStep 1422271 = 2133407) B2133407
theorem B34624583 : Blo 1421530 34624583 := bstep (se 1 (by rfl) ⟨25968437, by rfl⟩ : syracuseStep 34624583 = 51936875) B51936875
theorem B51877007 : Blo 1421530 51877007 := bstep (se 1 (by rfl) ⟨38907755, by rfl⟩ : syracuseStep 51877007 = 77815511) B77815511
theorem B18224513 : Blo 1421530 18224513 := bstep (se 2 (by rfl) ⟨6834192, by rfl⟩ : syracuseStep 18224513 = 13668385) B13668385
theorem B1422895 : Blo 1421530 1422895 := bstep (se 1 (by rfl) ⟨1067171, by rfl⟩ : syracuseStep 1422895 = 2134343) B2134343
theorem B3036847 : Blo 1421530 3036847 := bstep (se 1 (by rfl) ⟨2277635, by rfl⟩ : syracuseStep 3036847 = 4555271) B4555271
theorem B3200777 : Blo 1421530 3200777 := bstep (se 2 (by rfl) ⟨1200291, by rfl⟩ : syracuseStep 3200777 = 2400583) B2400583
theorem B5765087 : Blo 1421530 5765087 := bstep (se 1 (by rfl) ⟨4323815, by rfl⟩ : syracuseStep 5765087 = 8647631) B8647631
theorem B1423519 : Blo 1421530 1423519 := bstep (se 1 (by rfl) ⟨1067639, by rfl⟩ : syracuseStep 1423519 = 2135279) B2135279
theorem B3201335 : Blo 1421530 3201335 := bstep (se 1 (by rfl) ⟨2401001, by rfl⟩ : syracuseStep 3201335 = 4802003) B4802003
theorem B4053559 : Blo 1421530 4053559 := bstep (se 1 (by rfl) ⟨3040169, by rfl⟩ : syracuseStep 4053559 = 6080339) B6080339
theorem B4799465 : Blo 1421530 4799465 := bstep (se 2 (by rfl) ⟨1799799, by rfl⟩ : syracuseStep 4799465 = 3599599) B3599599
theorem B2702335 : Blo 1421530 2702335 := bstep (se 1 (by rfl) ⟨2026751, by rfl⟩ : syracuseStep 2702335 = 4053503) B4053503
theorem B3202271 : Blo 1421530 3202271 := bstep (se 1 (by rfl) ⟨2401703, by rfl⟩ : syracuseStep 3202271 = 4803407) B4803407
theorem B17300897 : Blo 1421530 17300897 := bstep (se 2 (by rfl) ⟨6487836, by rfl⟩ : syracuseStep 17300897 = 12975673) B12975673
theorem B4801193 : Blo 1421530 4801193 := bstep (se 2 (by rfl) ⟨1800447, by rfl⟩ : syracuseStep 4801193 = 3600895) B3600895
theorem B12149675 : Blo 1421530 12149675 := bstep (se 1 (by rfl) ⟨9112256, by rfl⟩ : syracuseStep 12149675 = 18224513) B18224513
theorem B10945489 : Blo 1421530 10945489 := bstep (se 2 (by rfl) ⟨4104558, by rfl⟩ : syracuseStep 10945489 = 8209117) B8209117
theorem B3843391 : Blo 1421530 3843391 := bstep (se 1 (by rfl) ⟨2882543, by rfl⟩ : syracuseStep 3843391 = 5765087) B5765087
theorem B11699711 : Blo 1421530 11699711 := bstep (se 1 (by rfl) ⟨8774783, by rfl⟩ : syracuseStep 11699711 = 17549567) B17549567
theorem B4049129 : Blo 1421530 4049129 := bstep (se 2 (by rfl) ⟨1518423, by rfl⟩ : syracuseStep 4049129 = 3036847) B3036847
theorem B2132699 : Blo 1421530 2132699 := bstep (se 1 (by rfl) ⟨1599524, by rfl⟩ : syracuseStep 2132699 = 3199049) B3199049
theorem B1600231 : Blo 1421530 1600231 := bstep (se 1 (by rfl) ⟨1200173, by rfl⟩ : syracuseStep 1600231 = 2400347) B2400347
theorem B2133227 : Blo 1421530 2133227 := bstep (se 1 (by rfl) ⟨1599920, by rfl⟩ : syracuseStep 2133227 = 3199841) B3199841
theorem B14798461 : Blo 1421530 14798461 := bstep (se 3 (by rfl) ⟨2774711, by rfl⟩ : syracuseStep 14798461 = 5549423) B5549423
theorem B2133851 : Blo 1421530 2133851 := bstep (se 1 (by rfl) ⟨1600388, by rfl⟩ : syracuseStep 2133851 = 3200777) B3200777
theorem B2133929 : Blo 1421530 2133929 := bstep (se 2 (by rfl) ⟨800223, by rfl⟩ : syracuseStep 2133929 = 1600447) B1600447
theorem B2134223 : Blo 1421530 2134223 := bstep (se 1 (by rfl) ⟨1600667, by rfl⟩ : syracuseStep 2134223 = 3201335) B3201335
theorem B9114049 : Blo 1421530 9114049 := bstep (se 2 (by rfl) ⟨3417768, by rfl⟩ : syracuseStep 9114049 = 6835537) B6835537
theorem B3199643 : Blo 1421530 3199643 := bstep (se 1 (by rfl) ⟨2399732, by rfl⟩ : syracuseStep 3199643 = 4799465) B4799465
theorem B5403455 : Blo 1421530 5403455 := bstep (se 1 (by rfl) ⟨4052591, by rfl⟩ : syracuseStep 5403455 = 8105183) B8105183
theorem B2134847 : Blo 1421530 2134847 := bstep (se 1 (by rfl) ⟨1601135, by rfl⟩ : syracuseStep 2134847 = 3202271) B3202271
theorem B2700155 : Blo 1421530 2700155 := bstep (se 1 (by rfl) ⟨2025116, by rfl⟩ : syracuseStep 2700155 = 4050233) B4050233
theorem B1422439 : Blo 1421530 1422439 := bstep (se 1 (by rfl) ⟨1066829, by rfl⟩ : syracuseStep 1422439 = 2133659) B2133659
theorem B1422695 : Blo 1421530 1422695 := bstep (se 1 (by rfl) ⟨1067021, by rfl⟩ : syracuseStep 1422695 = 2134043) B2134043
theorem B1709471 : Blo 1421530 1709471 := bstep (se 1 (by rfl) ⟨1282103, by rfl⟩ : syracuseStep 1709471 = 2564207) B2564207
theorem B44987923 : Blo 1421530 44987923 := bstep (se 1 (by rfl) ⟨33740942, by rfl⟩ : syracuseStep 44987923 = 67481885) B67481885
theorem B23083055 : Blo 1421530 23083055 := bstep (se 1 (by rfl) ⟨17312291, by rfl⟩ : syracuseStep 23083055 = 34624583) B34624583
theorem B5404745 : Blo 1421530 5404745 := bstep (se 2 (by rfl) ⟨2026779, by rfl⟩ : syracuseStep 5404745 = 4053559) B4053559
theorem B34584671 : Blo 1421530 34584671 := bstep (se 1 (by rfl) ⟨25938503, by rfl⟩ : syracuseStep 34584671 = 51877007) B51877007
theorem B16210043 : Blo 1421530 16210043 := bstep (se 1 (by rfl) ⟨12157532, by rfl⟩ : syracuseStep 16210043 = 24315065) B24315065
theorem B13506725 : Blo 1421530 13506725 := bstep (se 4 (by rfl) ⟨1266255, by rfl⟩ : syracuseStep 13506725 = 2532511) B2532511
theorem B33757663 : Blo 1421530 33757663 := bstep (se 1 (by rfl) ⟨25318247, by rfl⟩ : syracuseStep 33757663 = 50636495) B50636495
theorem B3603113 : Blo 1421530 3603113 := bstep (se 2 (by rfl) ⟨1351167, by rfl⟩ : syracuseStep 3603113 = 2702335) B2702335
theorem B11533931 : Blo 1421530 11533931 := bstep (se 1 (by rfl) ⟨8650448, by rfl⟩ : syracuseStep 11533931 = 17300897) B17300897
theorem B7200737 : Blo 1421530 7200737 := bstep (se 2 (by rfl) ⟨2700276, by rfl⟩ : syracuseStep 7200737 = 5400553) B5400553
theorem B7799807 : Blo 1421530 7799807 := bstep (se 1 (by rfl) ⟨5849855, by rfl⟩ : syracuseStep 7799807 = 11699711) B11699711
theorem B10806695 : Blo 1421530 10806695 := bstep (se 1 (by rfl) ⟨8105021, by rfl⟩ : syracuseStep 10806695 = 16210043) B16210043
theorem B9004483 : Blo 1421530 9004483 := bstep (se 1 (by rfl) ⟨6753362, by rfl⟩ : syracuseStep 9004483 = 13506725) B13506725
theorem B2402075 : Blo 1421530 2402075 := bstep (se 1 (by rfl) ⟨1801556, by rfl⟩ : syracuseStep 2402075 = 3603113) B3603113
theorem B59983897 : Blo 1421530 59983897 := bstep (se 2 (by rfl) ⟨22493961, by rfl⟩ : syracuseStep 59983897 = 44987923) B44987923
theorem B2133095 : Blo 1421530 2133095 := bstep (se 1 (by rfl) ⟨1599821, by rfl⟩ : syracuseStep 2133095 = 3199643) B3199643
theorem B12152065 : Blo 1421530 12152065 := bstep (se 2 (by rfl) ⟨4557024, by rfl⟩ : syracuseStep 12152065 = 9114049) B9114049
theorem B45010217 : Blo 1421530 45010217 := bstep (se 2 (by rfl) ⟨16878831, by rfl⟩ : syracuseStep 45010217 = 33757663) B33757663
theorem B2133641 : Blo 1421530 2133641 := bstep (se 2 (by rfl) ⟨800115, by rfl⟩ : syracuseStep 2133641 = 1600231) B1600231
theorem B4558589 : Blo 1421530 4558589 := bstep (se 3 (by rfl) ⟨854735, by rfl⟩ : syracuseStep 4558589 = 1709471) B1709471
theorem B14593985 : Blo 1421530 14593985 := bstep (se 2 (by rfl) ⟨5472744, by rfl⟩ : syracuseStep 14593985 = 10945489) B10945489
theorem B15388703 : Blo 1421530 15388703 := bstep (se 1 (by rfl) ⟨11541527, by rfl⟩ : syracuseStep 15388703 = 23083055) B23083055
theorem B23056447 : Blo 1421530 23056447 := bstep (se 1 (by rfl) ⟨17292335, by rfl⟩ : syracuseStep 23056447 = 34584671) B34584671
theorem B2699419 : Blo 1421530 2699419 := bstep (se 1 (by rfl) ⟨2024564, by rfl⟩ : syracuseStep 2699419 = 4049129) B4049129
theorem B5124521 : Blo 1421530 5124521 := bstep (se 2 (by rfl) ⟨1921695, by rfl⟩ : syracuseStep 5124521 = 3843391) B3843391
theorem B1421799 : Blo 1421530 1421799 := bstep (se 1 (by rfl) ⟨1066349, by rfl⟩ : syracuseStep 1421799 = 2132699) B2132699
theorem B1422151 : Blo 1421530 1422151 := bstep (se 1 (by rfl) ⟨1066613, by rfl⟩ : syracuseStep 1422151 = 2133227) B2133227
theorem B19731281 : Blo 1421530 19731281 := bstep (se 2 (by rfl) ⟨7399230, by rfl⟩ : syracuseStep 19731281 = 14798461) B14798461
theorem B7689287 : Blo 1421530 7689287 := bstep (se 1 (by rfl) ⟨5766965, by rfl⟩ : syracuseStep 7689287 = 11533931) B11533931
theorem B1422567 : Blo 1421530 1422567 := bstep (se 1 (by rfl) ⟨1066925, by rfl⟩ : syracuseStep 1422567 = 2133851) B2133851
theorem B1422619 : Blo 1421530 1422619 := bstep (se 1 (by rfl) ⟨1066964, by rfl⟩ : syracuseStep 1422619 = 2133929) B2133929
theorem B1422815 : Blo 1421530 1422815 := bstep (se 1 (by rfl) ⟨1067111, by rfl⟩ : syracuseStep 1422815 = 2134223) B2134223
theorem B3200795 : Blo 1421530 3200795 := bstep (se 1 (by rfl) ⟨2400596, by rfl⟩ : syracuseStep 3200795 = 4801193) B4801193
theorem B3602303 : Blo 1421530 3602303 := bstep (se 1 (by rfl) ⟨2701727, by rfl⟩ : syracuseStep 3602303 = 5403455) B5403455
theorem B1423231 : Blo 1421530 1423231 := bstep (se 1 (by rfl) ⟨1067423, by rfl⟩ : syracuseStep 1423231 = 2134847) B2134847
theorem B8099783 : Blo 1421530 8099783 := bstep (se 1 (by rfl) ⟨6074837, by rfl⟩ : syracuseStep 8099783 = 12149675) B12149675
theorem B3603163 : Blo 1421530 3603163 := bstep (se 1 (by rfl) ⟨2702372, by rfl⟩ : syracuseStep 3603163 = 5404745) B5404745
theorem B7200413 : Blo 1421530 7200413 := bstep (se 3 (by rfl) ⟨1350077, by rfl⟩ : syracuseStep 7200413 = 2700155) B2700155
theorem B4800491 : Blo 1421530 4800491 := bstep (se 1 (by rfl) ⟨3600368, by rfl⟩ : syracuseStep 4800491 = 7200737) B7200737
theorem B79978529 : Blo 1421530 79978529 := bstep (se 2 (by rfl) ⟨29991948, by rfl⟩ : syracuseStep 79978529 = 59983897) B59983897
theorem B20504765 : Blo 1421530 20504765 := bstep (se 3 (by rfl) ⟨3844643, by rfl⟩ : syracuseStep 20504765 = 7689287) B7689287
theorem B3416347 : Blo 1421530 3416347 := bstep (se 1 (by rfl) ⟨2562260, by rfl⟩ : syracuseStep 3416347 = 5124521) B5124521
theorem B2401535 : Blo 1421530 2401535 := bstep (se 1 (by rfl) ⟨1801151, by rfl⟩ : syracuseStep 2401535 = 3602303) B3602303
theorem B5399855 : Blo 1421530 5399855 := bstep (se 1 (by rfl) ⟨4049891, by rfl⟩ : syracuseStep 5399855 = 8099783) B8099783
theorem B10259135 : Blo 1421530 10259135 := bstep (se 1 (by rfl) ⟨7694351, by rfl⟩ : syracuseStep 10259135 = 15388703) B15388703
theorem B3599225 : Blo 1421530 3599225 := bstep (se 2 (by rfl) ⟨1349709, by rfl⟩ : syracuseStep 3599225 = 2699419) B2699419
theorem B7204463 : Blo 1421530 7204463 := bstep (se 1 (by rfl) ⟨5403347, by rfl⟩ : syracuseStep 7204463 = 10806695) B10806695
theorem B4804217 : Blo 1421530 4804217 := bstep (se 2 (by rfl) ⟨1801581, by rfl⟩ : syracuseStep 4804217 = 3603163) B3603163
theorem B2133863 : Blo 1421530 2133863 := bstep (se 1 (by rfl) ⟨1600397, by rfl⟩ : syracuseStep 2133863 = 3200795) B3200795
theorem B1601383 : Blo 1421530 1601383 := bstep (se 1 (by rfl) ⟨1201037, by rfl⟩ : syracuseStep 1601383 = 2402075) B2402075
theorem B12005977 : Blo 1421530 12005977 := bstep (se 2 (by rfl) ⟨4502241, by rfl⟩ : syracuseStep 12005977 = 9004483) B9004483
theorem B1422063 : Blo 1421530 1422063 := bstep (se 1 (by rfl) ⟨1066547, by rfl⟩ : syracuseStep 1422063 = 2133095) B2133095
theorem B1422427 : Blo 1421530 1422427 := bstep (se 1 (by rfl) ⟨1066820, by rfl⟩ : syracuseStep 1422427 = 2133641) B2133641
theorem B9729323 : Blo 1421530 9729323 := bstep (se 1 (by rfl) ⟨7296992, by rfl⟩ : syracuseStep 9729323 = 14593985) B14593985
theorem B3200327 : Blo 1421530 3200327 := bstep (se 1 (by rfl) ⟨2400245, by rfl⟩ : syracuseStep 3200327 = 4800491) B4800491
theorem B30741929 : Blo 1421530 30741929 := bstep (se 2 (by rfl) ⟨11528223, by rfl⟩ : syracuseStep 30741929 = 23056447) B23056447
theorem B5199871 : Blo 1421530 5199871 := bstep (se 1 (by rfl) ⟨3899903, by rfl⟩ : syracuseStep 5199871 = 7799807) B7799807
theorem B16202753 : Blo 1421530 16202753 := bstep (se 2 (by rfl) ⟨6076032, by rfl⟩ : syracuseStep 16202753 = 12152065) B12152065
theorem B30006811 : Blo 1421530 30006811 := bstep (se 1 (by rfl) ⟨22505108, by rfl⟩ : syracuseStep 30006811 = 45010217) B45010217
theorem B52616749 : Blo 1421530 52616749 := bstep (se 3 (by rfl) ⟨9865640, by rfl⟩ : syracuseStep 52616749 = 19731281) B19731281
theorem B4800275 : Blo 1421530 4800275 := bstep (se 1 (by rfl) ⟨3600206, by rfl⟩ : syracuseStep 4800275 = 7200413) B7200413
theorem B3039059 : Blo 1421530 3039059 := bstep (se 1 (by rfl) ⟨2279294, by rfl⟩ : syracuseStep 3039059 = 4558589) B4558589
theorem B4555129 : Blo 1421530 4555129 := bstep (se 2 (by rfl) ⟨1708173, by rfl⟩ : syracuseStep 4555129 = 3416347) B3416347
theorem B16007969 : Blo 1421530 16007969 := bstep (se 2 (by rfl) ⟨6002988, by rfl⟩ : syracuseStep 16007969 = 12005977) B12005977
theorem B8104157 : Blo 1421530 8104157 := bstep (se 3 (by rfl) ⟨1519529, by rfl⟩ : syracuseStep 8104157 = 3039059) B3039059
theorem B4802975 : Blo 1421530 4802975 := bstep (se 1 (by rfl) ⟨3602231, by rfl⟩ : syracuseStep 4802975 = 7204463) B7204463
theorem B6933161 : Blo 1421530 6933161 := bstep (se 2 (by rfl) ⟨2599935, by rfl⟩ : syracuseStep 6933161 = 5199871) B5199871
theorem B1601023 : Blo 1421530 1601023 := bstep (se 1 (by rfl) ⟨1200767, by rfl⟩ : syracuseStep 1601023 = 2401535) B2401535
theorem B3599903 : Blo 1421530 3599903 := bstep (se 1 (by rfl) ⟨2699927, by rfl⟩ : syracuseStep 3599903 = 5399855) B5399855
theorem B2133551 : Blo 1421530 2133551 := bstep (se 1 (by rfl) ⟨1600163, by rfl⟩ : syracuseStep 2133551 = 3200327) B3200327
theorem B10801835 : Blo 1421530 10801835 := bstep (se 1 (by rfl) ⟨8101376, by rfl⟩ : syracuseStep 10801835 = 16202753) B16202753
theorem B2135177 : Blo 1421530 2135177 := bstep (se 2 (by rfl) ⟨800691, by rfl⟩ : syracuseStep 2135177 = 1601383) B1601383
theorem B3200183 : Blo 1421530 3200183 := bstep (se 1 (by rfl) ⟨2400137, by rfl⟩ : syracuseStep 3200183 = 4800275) B4800275
theorem B1422575 : Blo 1421530 1422575 := bstep (se 1 (by rfl) ⟨1066931, by rfl⟩ : syracuseStep 1422575 = 2133863) B2133863
theorem B53319019 : Blo 1421530 53319019 := bstep (se 1 (by rfl) ⟨39989264, by rfl⟩ : syracuseStep 53319019 = 79978529) B79978529
theorem B54679373 : Blo 1421530 54679373 := bstep (se 3 (by rfl) ⟨10252382, by rfl⟩ : syracuseStep 54679373 = 20504765) B20504765
theorem B6486215 : Blo 1421530 6486215 := bstep (se 1 (by rfl) ⟨4864661, by rfl⟩ : syracuseStep 6486215 = 9729323) B9729323
theorem B20494619 : Blo 1421530 20494619 := bstep (se 1 (by rfl) ⟨15370964, by rfl⟩ : syracuseStep 20494619 = 30741929) B30741929
theorem B6839423 : Blo 1421530 6839423 := bstep (se 1 (by rfl) ⟨5129567, by rfl⟩ : syracuseStep 6839423 = 10259135) B10259135
theorem B2399483 : Blo 1421530 2399483 := bstep (se 1 (by rfl) ⟨1799612, by rfl⟩ : syracuseStep 2399483 = 3599225) B3599225
theorem B40009081 : Blo 1421530 40009081 := bstep (se 2 (by rfl) ⟨15003405, by rfl⟩ : syracuseStep 40009081 = 30006811) B30006811
theorem B70155665 : Blo 1421530 70155665 := bstep (se 2 (by rfl) ⟨26308374, by rfl⟩ : syracuseStep 70155665 = 52616749) B52616749
theorem B3202811 : Blo 1421530 3202811 := bstep (se 1 (by rfl) ⟨2402108, by rfl⟩ : syracuseStep 3202811 = 4804217) B4804217
theorem B7201223 : Blo 1421530 7201223 := bstep (se 1 (by rfl) ⟨5400917, by rfl⟩ : syracuseStep 7201223 = 10801835) B10801835
theorem B71092025 : Blo 1421530 71092025 := bstep (se 2 (by rfl) ⟨26659509, by rfl⟩ : syracuseStep 71092025 = 53319019) B53319019
theorem B1599655 : Blo 1421530 1599655 := bstep (se 1 (by rfl) ⟨1199741, by rfl⟩ : syracuseStep 1599655 = 2399483) B2399483
theorem B46770443 : Blo 1421530 46770443 := bstep (se 1 (by rfl) ⟨35077832, by rfl⟩ : syracuseStep 46770443 = 70155665) B70155665
theorem B6073505 : Blo 1421530 6073505 := bstep (se 2 (by rfl) ⟨2277564, by rfl⟩ : syracuseStep 6073505 = 4555129) B4555129
theorem B17296573 : Blo 1421530 17296573 := bstep (se 3 (by rfl) ⟨3243107, by rfl⟩ : syracuseStep 17296573 = 6486215) B6486215
theorem B2133455 : Blo 1421530 2133455 := bstep (se 1 (by rfl) ⟨1600091, by rfl⟩ : syracuseStep 2133455 = 3200183) B3200183
theorem B5402771 : Blo 1421530 5402771 := bstep (se 1 (by rfl) ⟨4052078, by rfl⟩ : syracuseStep 5402771 = 8104157) B8104157
theorem B2134697 : Blo 1421530 2134697 := bstep (se 2 (by rfl) ⟨800511, by rfl⟩ : syracuseStep 2134697 = 1601023) B1601023
theorem B4559615 : Blo 1421530 4559615 := bstep (se 1 (by rfl) ⟨3419711, by rfl⟩ : syracuseStep 4559615 = 6839423) B6839423
theorem B1422367 : Blo 1421530 1422367 := bstep (se 1 (by rfl) ⟨1066775, by rfl⟩ : syracuseStep 1422367 = 2133551) B2133551
theorem B2135207 : Blo 1421530 2135207 := bstep (se 1 (by rfl) ⟨1601405, by rfl⟩ : syracuseStep 2135207 = 3202811) B3202811
theorem B1423451 : Blo 1421530 1423451 := bstep (se 1 (by rfl) ⟨1067588, by rfl⟩ : syracuseStep 1423451 = 2135177) B2135177
theorem B36452915 : Blo 1421530 36452915 := bstep (se 1 (by rfl) ⟨27339686, by rfl⟩ : syracuseStep 36452915 = 54679373) B54679373
theorem B13663079 : Blo 1421530 13663079 := bstep (se 1 (by rfl) ⟨10247309, by rfl⟩ : syracuseStep 13663079 = 20494619) B20494619
theorem B3201983 : Blo 1421530 3201983 := bstep (se 1 (by rfl) ⟨2401487, by rfl⟩ : syracuseStep 3201983 = 4802975) B4802975
theorem B18488429 : Blo 1421530 18488429 := bstep (se 3 (by rfl) ⟨3466580, by rfl⟩ : syracuseStep 18488429 = 6933161) B6933161
theorem B53345441 : Blo 1421530 53345441 := bstep (se 2 (by rfl) ⟨20004540, by rfl⟩ : syracuseStep 53345441 = 40009081) B40009081
theorem B42687917 : Blo 1421530 42687917 := bstep (se 3 (by rfl) ⟨8003984, by rfl⟩ : syracuseStep 42687917 = 16007969) B16007969
theorem B2399935 : Blo 1421530 2399935 := bstep (se 1 (by rfl) ⟨1799951, by rfl⟩ : syracuseStep 2399935 = 3599903) B3599903
theorem B4800815 : Blo 1421530 4800815 := bstep (se 1 (by rfl) ⟨3600611, by rfl⟩ : syracuseStep 4800815 = 7201223) B7201223
theorem B3039743 : Blo 1421530 3039743 := bstep (se 1 (by rfl) ⟨2279807, by rfl⟩ : syracuseStep 3039743 = 4559615) B4559615
theorem B31180295 : Blo 1421530 31180295 := bstep (se 1 (by rfl) ⟨23385221, by rfl⟩ : syracuseStep 31180295 = 46770443) B46770443
theorem B23062097 : Blo 1421530 23062097 := bstep (se 2 (by rfl) ⟨8648286, by rfl⟩ : syracuseStep 23062097 = 17296573) B17296573
theorem B4049003 : Blo 1421530 4049003 := bstep (se 1 (by rfl) ⟨3036752, by rfl⟩ : syracuseStep 4049003 = 6073505) B6073505
theorem B35563627 : Blo 1421530 35563627 := bstep (se 1 (by rfl) ⟨26672720, by rfl⟩ : syracuseStep 35563627 = 53345441) B53345441
theorem B2132873 : Blo 1421530 2132873 := bstep (se 2 (by rfl) ⟨799827, by rfl⟩ : syracuseStep 2132873 = 1599655) B1599655
theorem B47394683 : Blo 1421530 47394683 := bstep (se 1 (by rfl) ⟨35546012, by rfl⟩ : syracuseStep 47394683 = 71092025) B71092025
theorem B24301943 : Blo 1421530 24301943 := bstep (se 1 (by rfl) ⟨18226457, by rfl⟩ : syracuseStep 24301943 = 36452915) B36452915
theorem B2134655 : Blo 1421530 2134655 := bstep (se 1 (by rfl) ⟨1600991, by rfl⟩ : syracuseStep 2134655 = 3201983) B3201983
theorem B12325619 : Blo 1421530 12325619 := bstep (se 1 (by rfl) ⟨9244214, by rfl⟩ : syracuseStep 12325619 = 18488429) B18488429
theorem B3199913 : Blo 1421530 3199913 := bstep (se 2 (by rfl) ⟨1199967, by rfl⟩ : syracuseStep 3199913 = 2399935) B2399935
theorem B1422303 : Blo 1421530 1422303 := bstep (se 1 (by rfl) ⟨1066727, by rfl⟩ : syracuseStep 1422303 = 2133455) B2133455
theorem B3601847 : Blo 1421530 3601847 := bstep (se 1 (by rfl) ⟨2701385, by rfl⟩ : syracuseStep 3601847 = 5402771) B5402771
theorem B1423131 : Blo 1421530 1423131 := bstep (se 1 (by rfl) ⟨1067348, by rfl⟩ : syracuseStep 1423131 = 2134697) B2134697
theorem B1423471 : Blo 1421530 1423471 := bstep (se 1 (by rfl) ⟨1067603, by rfl⟩ : syracuseStep 1423471 = 2135207) B2135207
theorem B9108719 : Blo 1421530 9108719 := bstep (se 1 (by rfl) ⟨6831539, by rfl⟩ : syracuseStep 9108719 = 13663079) B13663079
theorem B28458611 : Blo 1421530 28458611 := bstep (se 1 (by rfl) ⟨21343958, by rfl⟩ : syracuseStep 28458611 = 42687917) B42687917
theorem B2401231 : Blo 1421530 2401231 := bstep (se 1 (by rfl) ⟨1800923, by rfl⟩ : syracuseStep 2401231 = 3601847) B3601847
theorem B32868317 : Blo 1421530 32868317 := bstep (se 3 (by rfl) ⟨6162809, by rfl⟩ : syracuseStep 32868317 = 12325619) B12325619
theorem B6072479 : Blo 1421530 6072479 := bstep (se 1 (by rfl) ⟨4554359, by rfl⟩ : syracuseStep 6072479 = 9108719) B9108719
theorem B47418169 : Blo 1421530 47418169 := bstep (se 2 (by rfl) ⟨17781813, by rfl⟩ : syracuseStep 47418169 = 35563627) B35563627
theorem B2026495 : Blo 1421530 2026495 := bstep (se 1 (by rfl) ⟨1519871, by rfl⟩ : syracuseStep 2026495 = 3039743) B3039743
theorem B2133275 : Blo 1421530 2133275 := bstep (se 1 (by rfl) ⟨1599956, by rfl⟩ : syracuseStep 2133275 = 3199913) B3199913
theorem B20786863 : Blo 1421530 20786863 := bstep (se 1 (by rfl) ⟨15590147, by rfl⟩ : syracuseStep 20786863 = 31180295) B31180295
theorem B2699335 : Blo 1421530 2699335 := bstep (se 1 (by rfl) ⟨2024501, by rfl⟩ : syracuseStep 2699335 = 4049003) B4049003
theorem B1421915 : Blo 1421530 1421915 := bstep (se 1 (by rfl) ⟨1066436, by rfl⟩ : syracuseStep 1421915 = 2132873) B2132873
theorem B3200543 : Blo 1421530 3200543 := bstep (se 1 (by rfl) ⟨2400407, by rfl⟩ : syracuseStep 3200543 = 4800815) B4800815
theorem B16201295 : Blo 1421530 16201295 := bstep (se 1 (by rfl) ⟨12150971, by rfl⟩ : syracuseStep 16201295 = 24301943) B24301943
theorem B1423103 : Blo 1421530 1423103 := bstep (se 1 (by rfl) ⟨1067327, by rfl⟩ : syracuseStep 1423103 = 2134655) B2134655
theorem B15374731 : Blo 1421530 15374731 := bstep (se 1 (by rfl) ⟨11531048, by rfl⟩ : syracuseStep 15374731 = 23062097) B23062097
theorem B18972407 : Blo 1421530 18972407 := bstep (se 1 (by rfl) ⟨14229305, by rfl⟩ : syracuseStep 18972407 = 28458611) B28458611
theorem B31596455 : Blo 1421530 31596455 := bstep (se 1 (by rfl) ⟨23697341, by rfl⟩ : syracuseStep 31596455 = 47394683) B47394683
theorem B4048319 : Blo 1421530 4048319 := bstep (se 1 (by rfl) ⟨3036239, by rfl⟩ : syracuseStep 4048319 = 6072479) B6072479
theorem B27715817 : Blo 1421530 27715817 := bstep (se 2 (by rfl) ⟨10393431, by rfl⟩ : syracuseStep 27715817 = 20786863) B20786863
theorem B21064303 : Blo 1421530 21064303 := bstep (se 1 (by rfl) ⟨15798227, by rfl⟩ : syracuseStep 21064303 = 31596455) B31596455
theorem B3599113 : Blo 1421530 3599113 := bstep (se 2 (by rfl) ⟨1349667, by rfl⟩ : syracuseStep 3599113 = 2699335) B2699335
theorem B20499641 : Blo 1421530 20499641 := bstep (se 2 (by rfl) ⟨7687365, by rfl⟩ : syracuseStep 20499641 = 15374731) B15374731
theorem B2133695 : Blo 1421530 2133695 := bstep (se 1 (by rfl) ⟨1600271, by rfl⟩ : syracuseStep 2133695 = 3200543) B3200543
theorem B10800863 : Blo 1421530 10800863 := bstep (se 1 (by rfl) ⟨8100647, by rfl⟩ : syracuseStep 10800863 = 16201295) B16201295
theorem B1422183 : Blo 1421530 1422183 := bstep (se 1 (by rfl) ⟨1066637, by rfl⟩ : syracuseStep 1422183 = 2133275) B2133275
theorem B63224225 : Blo 1421530 63224225 := bstep (se 2 (by rfl) ⟨23709084, by rfl⟩ : syracuseStep 63224225 = 47418169) B47418169
theorem B3201641 : Blo 1421530 3201641 := bstep (se 2 (by rfl) ⟨1200615, by rfl⟩ : syracuseStep 3201641 = 2401231) B2401231
theorem B21912211 : Blo 1421530 21912211 := bstep (se 1 (by rfl) ⟨16434158, by rfl⟩ : syracuseStep 21912211 = 32868317) B32868317
theorem B2701993 : Blo 1421530 2701993 := bstep (se 2 (by rfl) ⟨1013247, by rfl⟩ : syracuseStep 2701993 = 2026495) B2026495
theorem B12648271 : Blo 1421530 12648271 := bstep (se 1 (by rfl) ⟨9486203, by rfl⟩ : syracuseStep 12648271 = 18972407) B18972407
theorem B73908845 : Blo 1421530 73908845 := bstep (se 3 (by rfl) ⟨13857908, by rfl⟩ : syracuseStep 73908845 = 27715817) B27715817
theorem B42149483 : Blo 1421530 42149483 := bstep (se 1 (by rfl) ⟨31612112, by rfl⟩ : syracuseStep 42149483 = 63224225) B63224225
theorem B13666427 : Blo 1421530 13666427 := bstep (se 1 (by rfl) ⟨10249820, by rfl⟩ : syracuseStep 13666427 = 20499641) B20499641
theorem B28085737 : Blo 1421530 28085737 := bstep (se 2 (by rfl) ⟨10532151, by rfl⟩ : syracuseStep 28085737 = 21064303) B21064303
theorem B2134427 : Blo 1421530 2134427 := bstep (se 1 (by rfl) ⟨1600820, by rfl⟩ : syracuseStep 2134427 = 3201641) B3201641
theorem B16864361 : Blo 1421530 16864361 := bstep (se 2 (by rfl) ⟨6324135, by rfl⟩ : syracuseStep 16864361 = 12648271) B12648271
theorem B1422463 : Blo 1421530 1422463 := bstep (se 1 (by rfl) ⟨1066847, by rfl⟩ : syracuseStep 1422463 = 2133695) B2133695
theorem B116865125 : Blo 1421530 116865125 := bstep (se 4 (by rfl) ⟨10956105, by rfl⟩ : syracuseStep 116865125 = 21912211) B21912211
theorem B3602657 : Blo 1421530 3602657 := bstep (se 2 (by rfl) ⟨1350996, by rfl⟩ : syracuseStep 3602657 = 2701993) B2701993
theorem B4798817 : Blo 1421530 4798817 := bstep (se 2 (by rfl) ⟨1799556, by rfl⟩ : syracuseStep 4798817 = 3599113) B3599113
theorem B10795517 : Blo 1421530 10795517 := bstep (se 3 (by rfl) ⟨2024159, by rfl⟩ : syracuseStep 10795517 = 4048319) B4048319
theorem B7200575 : Blo 1421530 7200575 := bstep (se 1 (by rfl) ⟨5400431, by rfl⟩ : syracuseStep 7200575 = 10800863) B10800863
theorem B28099655 : Blo 1421530 28099655 := bstep (se 1 (by rfl) ⟨21074741, by rfl⟩ : syracuseStep 28099655 = 42149483) B42149483
theorem B9110951 : Blo 1421530 9110951 := bstep (se 1 (by rfl) ⟨6833213, by rfl⟩ : syracuseStep 9110951 = 13666427) B13666427
theorem B2401771 : Blo 1421530 2401771 := bstep (se 1 (by rfl) ⟨1801328, by rfl⟩ : syracuseStep 2401771 = 3602657) B3602657
theorem B37447649 : Blo 1421530 37447649 := bstep (se 2 (by rfl) ⟨14042868, by rfl⟩ : syracuseStep 37447649 = 28085737) B28085737
theorem B11242907 : Blo 1421530 11242907 := bstep (se 1 (by rfl) ⟨8432180, by rfl⟩ : syracuseStep 11242907 = 16864361) B16864361
theorem B77910083 : Blo 1421530 77910083 := bstep (se 1 (by rfl) ⟨58432562, by rfl⟩ : syracuseStep 77910083 = 116865125) B116865125
theorem B3199211 : Blo 1421530 3199211 := bstep (se 1 (by rfl) ⟨2399408, by rfl⟩ : syracuseStep 3199211 = 4798817) B4798817
theorem B7197011 : Blo 1421530 7197011 := bstep (se 1 (by rfl) ⟨5397758, by rfl⟩ : syracuseStep 7197011 = 10795517) B10795517
theorem B1422951 : Blo 1421530 1422951 := bstep (se 1 (by rfl) ⟨1067213, by rfl⟩ : syracuseStep 1422951 = 2134427) B2134427
theorem B49272563 : Blo 1421530 49272563 := bstep (se 1 (by rfl) ⟨36954422, by rfl⟩ : syracuseStep 49272563 = 73908845) B73908845
theorem B4800383 : Blo 1421530 4800383 := bstep (se 1 (by rfl) ⟨3600287, by rfl⟩ : syracuseStep 4800383 = 7200575) B7200575
theorem B51940055 : Blo 1421530 51940055 := bstep (se 1 (by rfl) ⟨38955041, by rfl⟩ : syracuseStep 51940055 = 77910083) B77910083
theorem B2132807 : Blo 1421530 2132807 := bstep (se 1 (by rfl) ⟨1599605, by rfl⟩ : syracuseStep 2132807 = 3199211) B3199211
theorem B6073967 : Blo 1421530 6073967 := bstep (se 1 (by rfl) ⟨4555475, by rfl⟩ : syracuseStep 6073967 = 9110951) B9110951
theorem B24965099 : Blo 1421530 24965099 := bstep (se 1 (by rfl) ⟨18723824, by rfl⟩ : syracuseStep 24965099 = 37447649) B37447649
theorem B3200255 : Blo 1421530 3200255 := bstep (se 1 (by rfl) ⟨2400191, by rfl⟩ : syracuseStep 3200255 = 4800383) B4800383
theorem B4798007 : Blo 1421530 4798007 := bstep (se 1 (by rfl) ⟨3598505, by rfl⟩ : syracuseStep 4798007 = 7197011) B7197011
theorem B18733103 : Blo 1421530 18733103 := bstep (se 1 (by rfl) ⟨14049827, by rfl⟩ : syracuseStep 18733103 = 28099655) B28099655
theorem B32848375 : Blo 1421530 32848375 := bstep (se 1 (by rfl) ⟨24636281, by rfl⟩ : syracuseStep 32848375 = 49272563) B49272563
theorem B3202361 : Blo 1421530 3202361 := bstep (se 2 (by rfl) ⟨1200885, by rfl⟩ : syracuseStep 3202361 = 2401771) B2401771
theorem B7495271 : Blo 1421530 7495271 := bstep (se 1 (by rfl) ⟨5621453, by rfl⟩ : syracuseStep 7495271 = 11242907) B11242907
theorem B4049311 : Blo 1421530 4049311 := bstep (se 1 (by rfl) ⟨3036983, by rfl⟩ : syracuseStep 4049311 = 6073967) B6073967
theorem B43797833 : Blo 1421530 43797833 := bstep (se 2 (by rfl) ⟨16424187, by rfl⟩ : syracuseStep 43797833 = 32848375) B32848375
theorem B2133503 : Blo 1421530 2133503 := bstep (se 1 (by rfl) ⟨1600127, by rfl⟩ : syracuseStep 2133503 = 3200255) B3200255
theorem B3198671 : Blo 1421530 3198671 := bstep (se 1 (by rfl) ⟨2399003, by rfl⟩ : syracuseStep 3198671 = 4798007) B4798007
theorem B12488735 : Blo 1421530 12488735 := bstep (se 1 (by rfl) ⟨9366551, by rfl⟩ : syracuseStep 12488735 = 18733103) B18733103
theorem B1421871 : Blo 1421530 1421871 := bstep (se 1 (by rfl) ⟨1066403, by rfl⟩ : syracuseStep 1421871 = 2132807) B2132807
theorem B2134907 : Blo 1421530 2134907 := bstep (se 1 (by rfl) ⟨1601180, by rfl⟩ : syracuseStep 2134907 = 3202361) B3202361
theorem B16643399 : Blo 1421530 16643399 := bstep (se 1 (by rfl) ⟨12482549, by rfl⟩ : syracuseStep 16643399 = 24965099) B24965099
theorem B34626703 : Blo 1421530 34626703 := bstep (se 1 (by rfl) ⟨25970027, by rfl⟩ : syracuseStep 34626703 = 51940055) B51940055
theorem B4996847 : Blo 1421530 4996847 := bstep (se 1 (by rfl) ⟨3747635, by rfl⟩ : syracuseStep 4996847 = 7495271) B7495271
theorem B5399081 : Blo 1421530 5399081 := bstep (se 2 (by rfl) ⟨2024655, by rfl⟩ : syracuseStep 5399081 = 4049311) B4049311
theorem B177529589 : Blo 1421530 177529589 := bstep (se 5 (by rfl) ⟨8321699, by rfl⟩ : syracuseStep 177529589 = 16643399) B16643399
theorem B29198555 : Blo 1421530 29198555 := bstep (se 1 (by rfl) ⟨21898916, by rfl⟩ : syracuseStep 29198555 = 43797833) B43797833
theorem B2132447 : Blo 1421530 2132447 := bstep (se 1 (by rfl) ⟨1599335, by rfl⟩ : syracuseStep 2132447 = 3198671) B3198671
theorem B8325823 : Blo 1421530 8325823 := bstep (se 1 (by rfl) ⟨6244367, by rfl⟩ : syracuseStep 8325823 = 12488735) B12488735
theorem B13324925 : Blo 1421530 13324925 := bstep (se 3 (by rfl) ⟨2498423, by rfl⟩ : syracuseStep 13324925 = 4996847) B4996847
theorem B1422335 : Blo 1421530 1422335 := bstep (se 1 (by rfl) ⟨1066751, by rfl⟩ : syracuseStep 1422335 = 2133503) B2133503
theorem B1423271 : Blo 1421530 1423271 := bstep (se 1 (by rfl) ⟨1067453, by rfl⟩ : syracuseStep 1423271 = 2134907) B2134907
theorem B46168937 : Blo 1421530 46168937 := bstep (se 2 (by rfl) ⟨17313351, by rfl⟩ : syracuseStep 46168937 = 34626703) B34626703
theorem B11101097 : Blo 1421530 11101097 := bstep (se 2 (by rfl) ⟨4162911, by rfl⟩ : syracuseStep 11101097 = 8325823) B8325823
theorem B19465703 : Blo 1421530 19465703 := bstep (se 1 (by rfl) ⟨14599277, by rfl⟩ : syracuseStep 19465703 = 29198555) B29198555
theorem B30779291 : Blo 1421530 30779291 := bstep (se 1 (by rfl) ⟨23084468, by rfl⟩ : syracuseStep 30779291 = 46168937) B46168937
theorem B3599387 : Blo 1421530 3599387 := bstep (se 1 (by rfl) ⟨2699540, by rfl⟩ : syracuseStep 3599387 = 5399081) B5399081
theorem B8883283 : Blo 1421530 8883283 := bstep (se 1 (by rfl) ⟨6662462, by rfl⟩ : syracuseStep 8883283 = 13324925) B13324925
theorem B118353059 : Blo 1421530 118353059 := bstep (se 1 (by rfl) ⟨88764794, by rfl⟩ : syracuseStep 118353059 = 177529589) B177529589
theorem B1421631 : Blo 1421530 1421631 := bstep (se 1 (by rfl) ⟨1066223, by rfl⟩ : syracuseStep 1421631 = 2132447) B2132447
theorem B12977135 : Blo 1421530 12977135 := bstep (se 1 (by rfl) ⟨9732851, by rfl⟩ : syracuseStep 12977135 = 19465703) B19465703
theorem B82078109 : Blo 1421530 82078109 := bstep (se 3 (by rfl) ⟨15389645, by rfl⟩ : syracuseStep 82078109 = 30779291) B30779291
theorem B78902039 : Blo 1421530 78902039 := bstep (se 1 (by rfl) ⟨59176529, by rfl⟩ : syracuseStep 78902039 = 118353059) B118353059
theorem B29602925 : Blo 1421530 29602925 := bstep (se 3 (by rfl) ⟨5550548, by rfl⟩ : syracuseStep 29602925 = 11101097) B11101097
theorem B11844377 : Blo 1421530 11844377 := bstep (se 2 (by rfl) ⟨4441641, by rfl⟩ : syracuseStep 11844377 = 8883283) B8883283
theorem B2399591 : Blo 1421530 2399591 := bstep (se 1 (by rfl) ⟨1799693, by rfl⟩ : syracuseStep 2399591 = 3599387) B3599387
theorem B52601359 : Blo 1421530 52601359 := bstep (se 1 (by rfl) ⟨39451019, by rfl⟩ : syracuseStep 52601359 = 78902039) B78902039
theorem B8651423 : Blo 1421530 8651423 := bstep (se 1 (by rfl) ⟨6488567, by rfl⟩ : syracuseStep 8651423 = 12977135) B12977135
theorem B19735283 : Blo 1421530 19735283 := bstep (se 1 (by rfl) ⟨14801462, by rfl⟩ : syracuseStep 19735283 = 29602925) B29602925
theorem B1599727 : Blo 1421530 1599727 := bstep (se 1 (by rfl) ⟨1199795, by rfl⟩ : syracuseStep 1599727 = 2399591) B2399591
theorem B54718739 : Blo 1421530 54718739 := bstep (se 1 (by rfl) ⟨41039054, by rfl⟩ : syracuseStep 54718739 = 82078109) B82078109
theorem B7896251 : Blo 1421530 7896251 := bstep (se 1 (by rfl) ⟨5922188, by rfl⟩ : syracuseStep 7896251 = 11844377) B11844377
theorem B36479159 : Blo 1421530 36479159 := bstep (se 1 (by rfl) ⟨27359369, by rfl⟩ : syracuseStep 36479159 = 54718739) B54718739
theorem B5767615 : Blo 1421530 5767615 := bstep (se 1 (by rfl) ⟨4325711, by rfl⟩ : syracuseStep 5767615 = 8651423) B8651423
theorem B52627421 : Blo 1421530 52627421 := bstep (se 3 (by rfl) ⟨9867641, by rfl⟩ : syracuseStep 52627421 = 19735283) B19735283
theorem B2132969 : Blo 1421530 2132969 := bstep (se 2 (by rfl) ⟨799863, by rfl⟩ : syracuseStep 2132969 = 1599727) B1599727
theorem B21056669 : Blo 1421530 21056669 := bstep (se 3 (by rfl) ⟨3948125, by rfl⟩ : syracuseStep 21056669 = 7896251) B7896251
theorem B70135145 : Blo 1421530 70135145 := bstep (se 2 (by rfl) ⟨26300679, by rfl⟩ : syracuseStep 70135145 = 52601359) B52601359
theorem B1421979 : Blo 1421530 1421979 := bstep (se 1 (by rfl) ⟨1066484, by rfl⟩ : syracuseStep 1421979 = 2132969) B2132969
theorem B14037779 : Blo 1421530 14037779 := bstep (se 1 (by rfl) ⟨10528334, by rfl⟩ : syracuseStep 14037779 = 21056669) B21056669
theorem B46756763 : Blo 1421530 46756763 := bstep (se 1 (by rfl) ⟨35067572, by rfl⟩ : syracuseStep 46756763 = 70135145) B70135145
theorem B24319439 : Blo 1421530 24319439 := bstep (se 1 (by rfl) ⟨18239579, by rfl⟩ : syracuseStep 24319439 = 36479159) B36479159
theorem B7690153 : Blo 1421530 7690153 := bstep (se 2 (by rfl) ⟨2883807, by rfl⟩ : syracuseStep 7690153 = 5767615) B5767615
theorem B35084947 : Blo 1421530 35084947 := bstep (se 1 (by rfl) ⟨26313710, by rfl⟩ : syracuseStep 35084947 = 52627421) B52627421
theorem B31171175 : Blo 1421530 31171175 := bstep (se 1 (by rfl) ⟨23378381, by rfl⟩ : syracuseStep 31171175 = 46756763) B46756763
theorem B16212959 : Blo 1421530 16212959 := bstep (se 1 (by rfl) ⟨12159719, by rfl⟩ : syracuseStep 16212959 = 24319439) B24319439
theorem B9358519 : Blo 1421530 9358519 := bstep (se 1 (by rfl) ⟨7018889, by rfl⟩ : syracuseStep 9358519 = 14037779) B14037779
theorem B46779929 : Blo 1421530 46779929 := bstep (se 2 (by rfl) ⟨17542473, by rfl⟩ : syracuseStep 46779929 = 35084947) B35084947
theorem B10253537 : Blo 1421530 10253537 := bstep (se 2 (by rfl) ⟨3845076, by rfl⟩ : syracuseStep 10253537 = 7690153) B7690153
theorem B12478025 : Blo 1421530 12478025 := bstep (se 2 (by rfl) ⟨4679259, by rfl⟩ : syracuseStep 12478025 = 9358519) B9358519
theorem B10808639 : Blo 1421530 10808639 := bstep (se 1 (by rfl) ⟨8106479, by rfl⟩ : syracuseStep 10808639 = 16212959) B16212959
theorem B6835691 : Blo 1421530 6835691 := bstep (se 1 (by rfl) ⟨5126768, by rfl⟩ : syracuseStep 6835691 = 10253537) B10253537
theorem B20780783 : Blo 1421530 20780783 := bstep (se 1 (by rfl) ⟨15585587, by rfl⟩ : syracuseStep 20780783 = 31171175) B31171175
theorem B31186619 : Blo 1421530 31186619 := bstep (se 1 (by rfl) ⟨23389964, by rfl⟩ : syracuseStep 31186619 = 46779929) B46779929
theorem B13853855 : Blo 1421530 13853855 := bstep (se 1 (by rfl) ⟨10390391, by rfl⟩ : syracuseStep 13853855 = 20780783) B20780783
theorem B18228509 : Blo 1421530 18228509 := bstep (se 3 (by rfl) ⟨3417845, by rfl⟩ : syracuseStep 18228509 = 6835691) B6835691
theorem B8318683 : Blo 1421530 8318683 := bstep (se 1 (by rfl) ⟨6239012, by rfl⟩ : syracuseStep 8318683 = 12478025) B12478025
theorem B7205759 : Blo 1421530 7205759 := bstep (se 1 (by rfl) ⟨5404319, by rfl⟩ : syracuseStep 7205759 = 10808639) B10808639
theorem B20791079 : Blo 1421530 20791079 := bstep (se 1 (by rfl) ⟨15593309, by rfl⟩ : syracuseStep 20791079 = 31186619) B31186619
theorem B4803839 : Blo 1421530 4803839 := bstep (se 1 (by rfl) ⟨3602879, by rfl⟩ : syracuseStep 4803839 = 7205759) B7205759
theorem B9235903 : Blo 1421530 9235903 := bstep (se 1 (by rfl) ⟨6926927, by rfl⟩ : syracuseStep 9235903 = 13853855) B13853855
theorem B12152339 : Blo 1421530 12152339 := bstep (se 1 (by rfl) ⟨9114254, by rfl⟩ : syracuseStep 12152339 = 18228509) B18228509
theorem B11091577 : Blo 1421530 11091577 := bstep (se 2 (by rfl) ⟨4159341, by rfl⟩ : syracuseStep 11091577 = 8318683) B8318683
theorem B13860719 : Blo 1421530 13860719 := bstep (se 1 (by rfl) ⟨10395539, by rfl⟩ : syracuseStep 13860719 = 20791079) B20791079
theorem B12314537 : Blo 1421530 12314537 := bstep (se 2 (by rfl) ⟨4617951, by rfl⟩ : syracuseStep 12314537 = 9235903) B9235903
theorem B14788769 : Blo 1421530 14788769 := bstep (se 2 (by rfl) ⟨5545788, by rfl⟩ : syracuseStep 14788769 = 11091577) B11091577
theorem B3202559 : Blo 1421530 3202559 := bstep (se 1 (by rfl) ⟨2401919, by rfl⟩ : syracuseStep 3202559 = 4803839) B4803839
theorem B8101559 : Blo 1421530 8101559 := bstep (se 1 (by rfl) ⟨6076169, by rfl⟩ : syracuseStep 8101559 = 12152339) B12152339
theorem B9240479 : Blo 1421530 9240479 := bstep (se 1 (by rfl) ⟨6930359, by rfl⟩ : syracuseStep 9240479 = 13860719) B13860719
theorem B39436717 : Blo 1421530 39436717 := bstep (se 3 (by rfl) ⟨7394384, by rfl⟩ : syracuseStep 39436717 = 14788769) B14788769
theorem B8209691 : Blo 1421530 8209691 := bstep (se 1 (by rfl) ⟨6157268, by rfl⟩ : syracuseStep 8209691 = 12314537) B12314537
theorem B5401039 : Blo 1421530 5401039 := bstep (se 1 (by rfl) ⟨4050779, by rfl⟩ : syracuseStep 5401039 = 8101559) B8101559
theorem B2135039 : Blo 1421530 2135039 := bstep (se 1 (by rfl) ⟨1601279, by rfl⟩ : syracuseStep 2135039 = 3202559) B3202559
theorem B6160319 : Blo 1421530 6160319 := bstep (se 1 (by rfl) ⟨4620239, by rfl⟩ : syracuseStep 6160319 = 9240479) B9240479
theorem B7201385 : Blo 1421530 7201385 := bstep (se 2 (by rfl) ⟨2700519, by rfl⟩ : syracuseStep 7201385 = 5401039) B5401039
theorem B5473127 : Blo 1421530 5473127 := bstep (se 1 (by rfl) ⟨4104845, by rfl⟩ : syracuseStep 5473127 = 8209691) B8209691
theorem B4106879 : Blo 1421530 4106879 := bstep (se 1 (by rfl) ⟨3080159, by rfl⟩ : syracuseStep 4106879 = 6160319) B6160319
theorem B52582289 : Blo 1421530 52582289 := bstep (se 2 (by rfl) ⟨19718358, by rfl⟩ : syracuseStep 52582289 = 39436717) B39436717
theorem B1423359 : Blo 1421530 1423359 := bstep (se 1 (by rfl) ⟨1067519, by rfl⟩ : syracuseStep 1423359 = 2135039) B2135039
theorem B4800923 : Blo 1421530 4800923 := bstep (se 1 (by rfl) ⟨3600692, by rfl⟩ : syracuseStep 4800923 = 7201385) B7201385
theorem B2737919 : Blo 1421530 2737919 := bstep (se 1 (by rfl) ⟨2053439, by rfl⟩ : syracuseStep 2737919 = 4106879) B4106879
theorem B14595005 : Blo 1421530 14595005 := bstep (se 3 (by rfl) ⟨2736563, by rfl⟩ : syracuseStep 14595005 = 5473127) B5473127
theorem B140219437 : Blo 1421530 140219437 := bstep (se 3 (by rfl) ⟨26291144, by rfl⟩ : syracuseStep 140219437 = 52582289) B52582289
theorem B186959249 : Blo 1421530 186959249 := bstep (se 2 (by rfl) ⟨70109718, by rfl⟩ : syracuseStep 186959249 = 140219437) B140219437
theorem B7301117 : Blo 1421530 7301117 := bstep (se 3 (by rfl) ⟨1368959, by rfl⟩ : syracuseStep 7301117 = 2737919) B2737919
theorem B3200615 : Blo 1421530 3200615 := bstep (se 1 (by rfl) ⟨2400461, by rfl⟩ : syracuseStep 3200615 = 4800923) B4800923
theorem B38920013 : Blo 1421530 38920013 := bstep (se 3 (by rfl) ⟨7297502, by rfl⟩ : syracuseStep 38920013 = 14595005) B14595005
theorem B4867411 : Blo 1421530 4867411 := bstep (se 1 (by rfl) ⟨3650558, by rfl⟩ : syracuseStep 4867411 = 7301117) B7301117
theorem B25946675 : Blo 1421530 25946675 := bstep (se 1 (by rfl) ⟨19460006, by rfl⟩ : syracuseStep 25946675 = 38920013) B38920013
theorem B2133743 : Blo 1421530 2133743 := bstep (se 1 (by rfl) ⟨1600307, by rfl⟩ : syracuseStep 2133743 = 3200615) B3200615
theorem B124639499 : Blo 1421530 124639499 := bstep (se 1 (by rfl) ⟨93479624, by rfl⟩ : syracuseStep 124639499 = 186959249) B186959249
theorem B83092999 : Blo 1421530 83092999 := bstep (se 1 (by rfl) ⟨62319749, by rfl⟩ : syracuseStep 83092999 = 124639499) B124639499
theorem B6489881 : Blo 1421530 6489881 := bstep (se 2 (by rfl) ⟨2433705, by rfl⟩ : syracuseStep 6489881 = 4867411) B4867411
theorem B17297783 : Blo 1421530 17297783 := bstep (se 1 (by rfl) ⟨12973337, by rfl⟩ : syracuseStep 17297783 = 25946675) B25946675
theorem B1422495 : Blo 1421530 1422495 := bstep (se 1 (by rfl) ⟨1066871, by rfl⟩ : syracuseStep 1422495 = 2133743) B2133743
theorem B4326587 : Blo 1421530 4326587 := bstep (se 1 (by rfl) ⟨3244940, by rfl⟩ : syracuseStep 4326587 = 6489881) B6489881
theorem B110790665 : Blo 1421530 110790665 := bstep (se 2 (by rfl) ⟨41546499, by rfl⟩ : syracuseStep 110790665 = 83092999) B83092999
theorem B11531855 : Blo 1421530 11531855 := bstep (se 1 (by rfl) ⟨8648891, by rfl⟩ : syracuseStep 11531855 = 17297783) B17297783
theorem B2884391 : Blo 1421530 2884391 := bstep (se 1 (by rfl) ⟨2163293, by rfl⟩ : syracuseStep 2884391 = 4326587) B4326587
theorem B73860443 : Blo 1421530 73860443 := bstep (se 1 (by rfl) ⟨55395332, by rfl⟩ : syracuseStep 73860443 = 110790665) B110790665
theorem B30751613 : Blo 1421530 30751613 := bstep (se 3 (by rfl) ⟨5765927, by rfl⟩ : syracuseStep 30751613 = 11531855) B11531855
theorem B20501075 : Blo 1421530 20501075 := bstep (se 1 (by rfl) ⟨15375806, by rfl⟩ : syracuseStep 20501075 = 30751613) B30751613
theorem B30766837 : Blo 1421530 30766837 := bstep (se 5 (by rfl) ⟨1442195, by rfl⟩ : syracuseStep 30766837 = 2884391) B2884391
theorem B49240295 : Blo 1421530 49240295 := bstep (se 1 (by rfl) ⟨36930221, by rfl⟩ : syracuseStep 49240295 = 73860443) B73860443
theorem B32826863 : Blo 1421530 32826863 := bstep (se 1 (by rfl) ⟨24620147, by rfl⟩ : syracuseStep 32826863 = 49240295) B49240295
theorem B13667383 : Blo 1421530 13667383 := bstep (se 1 (by rfl) ⟨10250537, by rfl⟩ : syracuseStep 13667383 = 20501075) B20501075
theorem B41022449 : Blo 1421530 41022449 := bstep (se 2 (by rfl) ⟨15383418, by rfl⟩ : syracuseStep 41022449 = 30766837) B30766837
theorem B27348299 : Blo 1421530 27348299 := bstep (se 1 (by rfl) ⟨20511224, by rfl⟩ : syracuseStep 27348299 = 41022449) B41022449
theorem B21884575 : Blo 1421530 21884575 := bstep (se 1 (by rfl) ⟨16413431, by rfl⟩ : syracuseStep 21884575 = 32826863) B32826863
theorem B18223177 : Blo 1421530 18223177 := bstep (se 2 (by rfl) ⟨6833691, by rfl⟩ : syracuseStep 18223177 = 13667383) B13667383
theorem B24297569 : Blo 1421530 24297569 := bstep (se 2 (by rfl) ⟨9111588, by rfl⟩ : syracuseStep 24297569 = 18223177) B18223177
theorem B18232199 : Blo 1421530 18232199 := bstep (se 1 (by rfl) ⟨13674149, by rfl⟩ : syracuseStep 18232199 = 27348299) B27348299
theorem B29179433 : Blo 1421530 29179433 := bstep (se 2 (by rfl) ⟨10942287, by rfl⟩ : syracuseStep 29179433 = 21884575) B21884575
theorem B16198379 : Blo 1421530 16198379 := bstep (se 1 (by rfl) ⟨12148784, by rfl⟩ : syracuseStep 16198379 = 24297569) B24297569
theorem B19452955 : Blo 1421530 19452955 := bstep (se 1 (by rfl) ⟨14589716, by rfl⟩ : syracuseStep 19452955 = 29179433) B29179433
theorem B12154799 : Blo 1421530 12154799 := bstep (se 1 (by rfl) ⟨9116099, by rfl⟩ : syracuseStep 12154799 = 18232199) B18232199
theorem B8103199 : Blo 1421530 8103199 := bstep (se 1 (by rfl) ⟨6077399, by rfl⟩ : syracuseStep 8103199 = 12154799) B12154799
theorem B25937273 : Blo 1421530 25937273 := bstep (se 2 (by rfl) ⟨9726477, by rfl⟩ : syracuseStep 25937273 = 19452955) B19452955
theorem B10798919 : Blo 1421530 10798919 := bstep (se 1 (by rfl) ⟨8099189, by rfl⟩ : syracuseStep 10798919 = 16198379) B16198379
theorem B69166061 : Blo 1421530 69166061 := bstep (se 3 (by rfl) ⟨12968636, by rfl⟩ : syracuseStep 69166061 = 25937273) B25937273
theorem B7199279 : Blo 1421530 7199279 := bstep (se 1 (by rfl) ⟨5399459, by rfl⟩ : syracuseStep 7199279 = 10798919) B10798919
theorem B10804265 : Blo 1421530 10804265 := bstep (se 2 (by rfl) ⟨4051599, by rfl⟩ : syracuseStep 10804265 = 8103199) B8103199
theorem B7202843 : Blo 1421530 7202843 := bstep (se 1 (by rfl) ⟨5402132, by rfl⟩ : syracuseStep 7202843 = 10804265) B10804265
theorem B46110707 : Blo 1421530 46110707 := bstep (se 1 (by rfl) ⟨34583030, by rfl⟩ : syracuseStep 46110707 = 69166061) B69166061
theorem B4799519 : Blo 1421530 4799519 := bstep (se 1 (by rfl) ⟨3599639, by rfl⟩ : syracuseStep 4799519 = 7199279) B7199279
theorem B4801895 : Blo 1421530 4801895 := bstep (se 1 (by rfl) ⟨3601421, by rfl⟩ : syracuseStep 4801895 = 7202843) B7202843
theorem B30740471 : Blo 1421530 30740471 := bstep (se 1 (by rfl) ⟨23055353, by rfl⟩ : syracuseStep 30740471 = 46110707) B46110707
theorem B3199679 : Blo 1421530 3199679 := bstep (se 1 (by rfl) ⟨2399759, by rfl⟩ : syracuseStep 3199679 = 4799519) B4799519
theorem B2133119 : Blo 1421530 2133119 := bstep (se 1 (by rfl) ⟨1599839, by rfl⟩ : syracuseStep 2133119 = 3199679) B3199679
theorem B20493647 : Blo 1421530 20493647 := bstep (se 1 (by rfl) ⟨15370235, by rfl⟩ : syracuseStep 20493647 = 30740471) B30740471
theorem B3201263 : Blo 1421530 3201263 := bstep (se 1 (by rfl) ⟨2400947, by rfl⟩ : syracuseStep 3201263 = 4801895) B4801895
theorem B2134175 : Blo 1421530 2134175 := bstep (se 1 (by rfl) ⟨1600631, by rfl⟩ : syracuseStep 2134175 = 3201263) B3201263
theorem B1422079 : Blo 1421530 1422079 := bstep (se 1 (by rfl) ⟨1066559, by rfl⟩ : syracuseStep 1422079 = 2133119) B2133119
theorem B13662431 : Blo 1421530 13662431 := bstep (se 1 (by rfl) ⟨10246823, by rfl⟩ : syracuseStep 13662431 = 20493647) B20493647
theorem B1422783 : Blo 1421530 1422783 := bstep (se 1 (by rfl) ⟨1067087, by rfl⟩ : syracuseStep 1422783 = 2134175) B2134175
theorem B9108287 : Blo 1421530 9108287 := bstep (se 1 (by rfl) ⟨6831215, by rfl⟩ : syracuseStep 9108287 = 13662431) B13662431
theorem B6072191 : Blo 1421530 6072191 := bstep (se 1 (by rfl) ⟨4554143, by rfl⟩ : syracuseStep 6072191 = 9108287) B9108287
theorem B4048127 : Blo 1421530 4048127 := bstep (se 1 (by rfl) ⟨3036095, by rfl⟩ : syracuseStep 4048127 = 6072191) B6072191
theorem B2698751 : Blo 1421530 2698751 := bstep (se 1 (by rfl) ⟨2024063, by rfl⟩ : syracuseStep 2698751 = 4048127) B4048127
theorem B1799167 : Blo 1421530 1799167 := bstep (se 1 (by rfl) ⟨1349375, by rfl⟩ : syracuseStep 1799167 = 2698751) B2698751
theorem B2398889 : Blo 1421530 2398889 := bstep (se 2 (by rfl) ⟨899583, by rfl⟩ : syracuseStep 2398889 = 1799167) B1799167
theorem B1599259 : Blo 1421530 1599259 := bstep (se 1 (by rfl) ⟨1199444, by rfl⟩ : syracuseStep 1599259 = 2398889) B2398889
theorem B2132345 : Blo 1421530 2132345 := bstep (se 2 (by rfl) ⟨799629, by rfl⟩ : syracuseStep 2132345 = 1599259) B1599259
theorem B1421563 : Blo 1421530 1421563 := bstep (se 1 (by rfl) ⟨1066172, by rfl⟩ : syracuseStep 1421563 = 2132345) B2132345

theorem C0 (j : ℕ) (h1 : 355382 ≤ j) (h2 : j ≤ 355881) : Blo 1421530 (4 * j + 3) := by
  interval_cases j
  · exact B1421531
  · exact B1421535
  · exact B1421539
  · exact B1421543
  · exact B1421547
  · exact B1421551
  · exact B1421555
  · exact B1421559
  · exact B1421563
  · exact B1421567
  · exact B1421571
  · exact B1421575
  · exact B1421579
  · exact B1421583
  · exact B1421587
  · exact B1421591
  · exact B1421595
  · exact B1421599
  · exact B1421603
  · exact B1421607
  · exact B1421611
  · exact B1421615
  · exact B1421619
  · exact B1421623
  · exact B1421627
  · exact B1421631
  · exact B1421635
  · exact B1421639
  · exact B1421643
  · exact B1421647
  · exact B1421651
  · exact B1421655
  · exact B1421659
  · exact B1421663
  · exact B1421667
  · exact B1421671
  · exact B1421675
  · exact B1421679
  · exact B1421683
  · exact B1421687
  · exact B1421691
  · exact B1421695
  · exact B1421699
  · exact B1421703
  · exact B1421707
  · exact B1421711
  · exact B1421715
  · exact B1421719
  · exact B1421723
  · exact B1421727
  · exact B1421731
  · exact B1421735
  · exact B1421739
  · exact B1421743
  · exact B1421747
  · exact B1421751
  · exact B1421755
  · exact B1421759
  · exact B1421763
  · exact B1421767
  · exact B1421771
  · exact B1421775
  · exact B1421779
  · exact B1421783
  · exact B1421787
  · exact B1421791
  · exact B1421795
  · exact B1421799
  · exact B1421803
  · exact B1421807
  · exact B1421811
  · exact B1421815
  · exact B1421819
  · exact B1421823
  · exact B1421827
  · exact B1421831
  · exact B1421835
  · exact B1421839
  · exact B1421843
  · exact B1421847
  · exact B1421851
  · exact B1421855
  · exact B1421859
  · exact B1421863
  · exact B1421867
  · exact B1421871
  · exact B1421875
  · exact B1421879
  · exact B1421883
  · exact B1421887
  · exact B1421891
  · exact B1421895
  · exact B1421899
  · exact B1421903
  · exact B1421907
  · exact B1421911
  · exact B1421915
  · exact B1421919
  · exact B1421923
  · exact B1421927
  · exact B1421931
  · exact B1421935
  · exact B1421939
  · exact B1421943
  · exact B1421947
  · exact B1421951
  · exact B1421955
  · exact B1421959
  · exact B1421963
  · exact B1421967
  · exact B1421971
  · exact B1421975
  · exact B1421979
  · exact B1421983
  · exact B1421987
  · exact B1421991
  · exact B1421995
  · exact B1421999
  · exact B1422003
  · exact B1422007
  · exact B1422011
  · exact B1422015
  · exact B1422019
  · exact B1422023
  · exact B1422027
  · exact B1422031
  · exact B1422035
  · exact B1422039
  · exact B1422043
  · exact B1422047
  · exact B1422051
  · exact B1422055
  · exact B1422059
  · exact B1422063
  · exact B1422067
  · exact B1422071
  · exact B1422075
  · exact B1422079
  · exact B1422083
  · exact B1422087
  · exact B1422091
  · exact B1422095
  · exact B1422099
  · exact B1422103
  · exact B1422107
  · exact B1422111
  · exact B1422115
  · exact B1422119
  · exact B1422123
  · exact B1422127
  · exact B1422131
  · exact B1422135
  · exact B1422139
  · exact B1422143
  · exact B1422147
  · exact B1422151
  · exact B1422155
  · exact B1422159
  · exact B1422163
  · exact B1422167
  · exact B1422171
  · exact B1422175
  · exact B1422179
  · exact B1422183
  · exact B1422187
  · exact B1422191
  · exact B1422195
  · exact B1422199
  · exact B1422203
  · exact B1422207
  · exact B1422211
  · exact B1422215
  · exact B1422219
  · exact B1422223
  · exact B1422227
  · exact B1422231
  · exact B1422235
  · exact B1422239
  · exact B1422243
  · exact B1422247
  · exact B1422251
  · exact B1422255
  · exact B1422259
  · exact B1422263
  · exact B1422267
  · exact B1422271
  · exact B1422275
  · exact B1422279
  · exact B1422283
  · exact B1422287
  · exact B1422291
  · exact B1422295
  · exact B1422299
  · exact B1422303
  · exact B1422307
  · exact B1422311
  · exact B1422315
  · exact B1422319
  · exact B1422323
  · exact B1422327
  · exact B1422331
  · exact B1422335
  · exact B1422339
  · exact B1422343
  · exact B1422347
  · exact B1422351
  · exact B1422355
  · exact B1422359
  · exact B1422363
  · exact B1422367
  · exact B1422371
  · exact B1422375
  · exact B1422379
  · exact B1422383
  · exact B1422387
  · exact B1422391
  · exact B1422395
  · exact B1422399
  · exact B1422403
  · exact B1422407
  · exact B1422411
  · exact B1422415
  · exact B1422419
  · exact B1422423
  · exact B1422427
  · exact B1422431
  · exact B1422435
  · exact B1422439
  · exact B1422443
  · exact B1422447
  · exact B1422451
  · exact B1422455
  · exact B1422459
  · exact B1422463
  · exact B1422467
  · exact B1422471
  · exact B1422475
  · exact B1422479
  · exact B1422483
  · exact B1422487
  · exact B1422491
  · exact B1422495
  · exact B1422499
  · exact B1422503
  · exact B1422507
  · exact B1422511
  · exact B1422515
  · exact B1422519
  · exact B1422523
  · exact B1422527
  · exact B1422531
  · exact B1422535
  · exact B1422539
  · exact B1422543
  · exact B1422547
  · exact B1422551
  · exact B1422555
  · exact B1422559
  · exact B1422563
  · exact B1422567
  · exact B1422571
  · exact B1422575
  · exact B1422579
  · exact B1422583
  · exact B1422587
  · exact B1422591
  · exact B1422595
  · exact B1422599
  · exact B1422603
  · exact B1422607
  · exact B1422611
  · exact B1422615
  · exact B1422619
  · exact B1422623
  · exact B1422627
  · exact B1422631
  · exact B1422635
  · exact B1422639
  · exact B1422643
  · exact B1422647
  · exact B1422651
  · exact B1422655
  · exact B1422659
  · exact B1422663
  · exact B1422667
  · exact B1422671
  · exact B1422675
  · exact B1422679
  · exact B1422683
  · exact B1422687
  · exact B1422691
  · exact B1422695
  · exact B1422699
  · exact B1422703
  · exact B1422707
  · exact B1422711
  · exact B1422715
  · exact B1422719
  · exact B1422723
  · exact B1422727
  · exact B1422731
  · exact B1422735
  · exact B1422739
  · exact B1422743
  · exact B1422747
  · exact B1422751
  · exact B1422755
  · exact B1422759
  · exact B1422763
  · exact B1422767
  · exact B1422771
  · exact B1422775
  · exact B1422779
  · exact B1422783
  · exact B1422787
  · exact B1422791
  · exact B1422795
  · exact B1422799
  · exact B1422803
  · exact B1422807
  · exact B1422811
  · exact B1422815
  · exact B1422819
  · exact B1422823
  · exact B1422827
  · exact B1422831
  · exact B1422835
  · exact B1422839
  · exact B1422843
  · exact B1422847
  · exact B1422851
  · exact B1422855
  · exact B1422859
  · exact B1422863
  · exact B1422867
  · exact B1422871
  · exact B1422875
  · exact B1422879
  · exact B1422883
  · exact B1422887
  · exact B1422891
  · exact B1422895
  · exact B1422899
  · exact B1422903
  · exact B1422907
  · exact B1422911
  · exact B1422915
  · exact B1422919
  · exact B1422923
  · exact B1422927
  · exact B1422931
  · exact B1422935
  · exact B1422939
  · exact B1422943
  · exact B1422947
  · exact B1422951
  · exact B1422955
  · exact B1422959
  · exact B1422963
  · exact B1422967
  · exact B1422971
  · exact B1422975
  · exact B1422979
  · exact B1422983
  · exact B1422987
  · exact B1422991
  · exact B1422995
  · exact B1422999
  · exact B1423003
  · exact B1423007
  · exact B1423011
  · exact B1423015
  · exact B1423019
  · exact B1423023
  · exact B1423027
  · exact B1423031
  · exact B1423035
  · exact B1423039
  · exact B1423043
  · exact B1423047
  · exact B1423051
  · exact B1423055
  · exact B1423059
  · exact B1423063
  · exact B1423067
  · exact B1423071
  · exact B1423075
  · exact B1423079
  · exact B1423083
  · exact B1423087
  · exact B1423091
  · exact B1423095
  · exact B1423099
  · exact B1423103
  · exact B1423107
  · exact B1423111
  · exact B1423115
  · exact B1423119
  · exact B1423123
  · exact B1423127
  · exact B1423131
  · exact B1423135
  · exact B1423139
  · exact B1423143
  · exact B1423147
  · exact B1423151
  · exact B1423155
  · exact B1423159
  · exact B1423163
  · exact B1423167
  · exact B1423171
  · exact B1423175
  · exact B1423179
  · exact B1423183
  · exact B1423187
  · exact B1423191
  · exact B1423195
  · exact B1423199
  · exact B1423203
  · exact B1423207
  · exact B1423211
  · exact B1423215
  · exact B1423219
  · exact B1423223
  · exact B1423227
  · exact B1423231
  · exact B1423235
  · exact B1423239
  · exact B1423243
  · exact B1423247
  · exact B1423251
  · exact B1423255
  · exact B1423259
  · exact B1423263
  · exact B1423267
  · exact B1423271
  · exact B1423275
  · exact B1423279
  · exact B1423283
  · exact B1423287
  · exact B1423291
  · exact B1423295
  · exact B1423299
  · exact B1423303
  · exact B1423307
  · exact B1423311
  · exact B1423315
  · exact B1423319
  · exact B1423323
  · exact B1423327
  · exact B1423331
  · exact B1423335
  · exact B1423339
  · exact B1423343
  · exact B1423347
  · exact B1423351
  · exact B1423355
  · exact B1423359
  · exact B1423363
  · exact B1423367
  · exact B1423371
  · exact B1423375
  · exact B1423379
  · exact B1423383
  · exact B1423387
  · exact B1423391
  · exact B1423395
  · exact B1423399
  · exact B1423403
  · exact B1423407
  · exact B1423411
  · exact B1423415
  · exact B1423419
  · exact B1423423
  · exact B1423427
  · exact B1423431
  · exact B1423435
  · exact B1423439
  · exact B1423443
  · exact B1423447
  · exact B1423451
  · exact B1423455
  · exact B1423459
  · exact B1423463
  · exact B1423467
  · exact B1423471
  · exact B1423475
  · exact B1423479
  · exact B1423483
  · exact B1423487
  · exact B1423491
  · exact B1423495
  · exact B1423499
  · exact B1423503
  · exact B1423507
  · exact B1423511
  · exact B1423515
  · exact B1423519
  · exact B1423523
  · exact B1423527

theorem solution (m : ℕ) (hlo : 1421530 ≤ m) (hhi : m ≤ 1423530) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 355382 ≤ j := by omega
    have hj2 : j ≤ 355881 := by omega
    have hb : Blo 1421530 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
