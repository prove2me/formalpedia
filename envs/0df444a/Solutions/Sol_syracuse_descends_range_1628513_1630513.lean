-- Prove2me | solution 1 for syracuse_descends_range_1628513_1630513
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:14:16.03999+00:00
-- url     : https://prove2.me/submissions/3bc6001d-c8fc-40db-a91d-0c25ffa2e72f

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


theorem B4407301 : Blo 1628513 4407301 := bbase (se 4 (by rfl) ⟨413184, by rfl⟩ : syracuseStep 4407301 = 826369) (by norm_num)
theorem B1957969 : Blo 1628513 1957969 := bbase (se 2 (by rfl) ⟨734238, by rfl⟩ : syracuseStep 1957969 = 1468477) (by norm_num)
theorem B8249525 : Blo 1628513 8249525 := bbase (se 5 (by rfl) ⟨386696, by rfl⟩ : syracuseStep 8249525 = 773393) (by norm_num)
theorem B11149493 : Blo 1628513 11149493 := bbase (se 5 (by rfl) ⟨522632, by rfl⟩ : syracuseStep 11149493 = 1045265) (by norm_num)
theorem B5218661 : Blo 1628513 5218661 := bbase (se 4 (by rfl) ⟨489249, by rfl⟩ : syracuseStep 5218661 = 978499) (by norm_num)
theorem B1958305 : Blo 1628513 1958305 := bbase (se 2 (by rfl) ⟨734364, by rfl⟩ : syracuseStep 1958305 = 1468729) (by norm_num)
theorem B5497253 : Blo 1628513 5497253 := bbase (se 4 (by rfl) ⟨515367, by rfl⟩ : syracuseStep 5497253 = 1030735) (by norm_num)
theorem B6185429 : Blo 1628513 6185429 := bbase (se 7 (by rfl) ⟨72485, by rfl⟩ : syracuseStep 6185429 = 144971) (by norm_num)
theorem B3482149 : Blo 1628513 3482149 := bbase (se 4 (by rfl) ⟨326451, by rfl⟩ : syracuseStep 3482149 = 652903) (by norm_num)
theorem B1696465 : Blo 1628513 1696465 := bbase (se 2 (by rfl) ⟨636174, by rfl⟩ : syracuseStep 1696465 = 1272349) (by norm_num)
theorem B3916525 : Blo 1628513 3916525 := bbase (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) (by norm_num)
theorem B6185717 : Blo 1628513 6185717 := bbase (se 5 (by rfl) ⟨289955, by rfl⟩ : syracuseStep 6185717 = 579911) (by norm_num)
theorem B2089781 : Blo 1628513 2089781 := bbase (se 5 (by rfl) ⟨97958, by rfl⟩ : syracuseStep 2089781 = 195917) (by norm_num)
theorem B15876917 : Blo 1628513 15876917 := bbase (se 5 (by rfl) ⟨744230, by rfl⟩ : syracuseStep 15876917 = 1488461) (by norm_num)
theorem B4293461 : Blo 1628513 4293461 := bbase (se 9 (by rfl) ⟨12578, by rfl⟩ : syracuseStep 4293461 = 25157) (by norm_num)
theorem B5497685 : Blo 1628513 5497685 := bbase (se 9 (by rfl) ⟨16106, by rfl⟩ : syracuseStep 5497685 = 32213) (by norm_num)
theorem B2319445 : Blo 1628513 2319445 := bbase (se 8 (by rfl) ⟨13590, by rfl⟩ : syracuseStep 2319445 = 27181) (by norm_num)
theorem B2090233 : Blo 1628513 2090233 := bbase (se 2 (by rfl) ⟨783837, by rfl⟩ : syracuseStep 2090233 = 1567675) (by norm_num)
theorem B5498117 : Blo 1628513 5498117 := bbase (se 4 (by rfl) ⟨515448, by rfl⟩ : syracuseStep 5498117 = 1030897) (by norm_num)
theorem B4637989 : Blo 1628513 4637989 := bbase (se 4 (by rfl) ⟨434811, by rfl⟩ : syracuseStep 4637989 = 869623) (by norm_num)
theorem B2090377 : Blo 1628513 2090377 := bbase (se 2 (by rfl) ⟨783891, by rfl⟩ : syracuseStep 2090377 = 1567783) (by norm_num)
theorem B6956437 : Blo 1628513 6956437 := bbase (se 6 (by rfl) ⟨163041, by rfl⟩ : syracuseStep 6956437 = 326083) (by norm_num)
theorem B2319781 : Blo 1628513 2319781 := bbase (se 4 (by rfl) ⟨217479, by rfl⟩ : syracuseStep 2319781 = 434959) (by norm_num)
theorem B8250821 : Blo 1628513 8250821 := bbase (se 4 (by rfl) ⟨773514, by rfl⟩ : syracuseStep 8250821 = 1547029) (by norm_num)
theorem B8365525 : Blo 1628513 8365525 := bbase (se 7 (by rfl) ⟨98033, by rfl⟩ : syracuseStep 8365525 = 196067) (by norm_num)
theorem B2442773 : Blo 1628513 2442773 := bbase (se 6 (by rfl) ⟨57252, by rfl⟩ : syracuseStep 2442773 = 114505) (by norm_num)
theorem B2442797 : Blo 1628513 2442797 := bbase (se 3 (by rfl) ⟨458024, by rfl⟩ : syracuseStep 2442797 = 916049) (by norm_num)
theorem B2442821 : Blo 1628513 2442821 := bbase (se 4 (by rfl) ⟨229014, by rfl⟩ : syracuseStep 2442821 = 458029) (by norm_num)
theorem B2442845 : Blo 1628513 2442845 := bbase (se 3 (by rfl) ⟨458033, by rfl⟩ : syracuseStep 2442845 = 916067) (by norm_num)
theorem B2442869 : Blo 1628513 2442869 := bbase (se 5 (by rfl) ⟨114509, by rfl⟩ : syracuseStep 2442869 = 229019) (by norm_num)
theorem B2319997 : Blo 1628513 2319997 := bbase (se 3 (by rfl) ⟨434999, by rfl⟩ : syracuseStep 2319997 = 869999) (by norm_num)
theorem B2442893 : Blo 1628513 2442893 := bbase (se 3 (by rfl) ⟨458042, by rfl⟩ : syracuseStep 2442893 = 916085) (by norm_num)
theorem B15656597 : Blo 1628513 15656597 := bbase (se 6 (by rfl) ⟨366951, by rfl⟩ : syracuseStep 15656597 = 733903) (by norm_num)
theorem B6882965 : Blo 1628513 6882965 := bbase (se 6 (by rfl) ⟨161319, by rfl⟩ : syracuseStep 6882965 = 322639) (by norm_num)
theorem B2442917 : Blo 1628513 2442917 := bbase (se 4 (by rfl) ⟨229023, by rfl⟩ : syracuseStep 2442917 = 458047) (by norm_num)
theorem B5498549 : Blo 1628513 5498549 := bbase (se 5 (by rfl) ⟨257744, by rfl⟩ : syracuseStep 5498549 = 515489) (by norm_num)
theorem B2442941 : Blo 1628513 2442941 := bbase (se 3 (by rfl) ⟨458051, by rfl⟩ : syracuseStep 2442941 = 916103) (by norm_num)
theorem B2442965 : Blo 1628513 2442965 := bbase (se 7 (by rfl) ⟨28628, by rfl⟩ : syracuseStep 2442965 = 57257) (by norm_num)
theorem B2442989 : Blo 1628513 2442989 := bbase (se 3 (by rfl) ⟨458060, by rfl⟩ : syracuseStep 2442989 = 916121) (by norm_num)
theorem B5220085 : Blo 1628513 5220085 := bbase (se 5 (by rfl) ⟨244691, by rfl⟩ : syracuseStep 5220085 = 489383) (by norm_num)
theorem B4122373 : Blo 1628513 4122373 := bbase (se 4 (by rfl) ⟨386472, by rfl⟩ : syracuseStep 4122373 = 772945) (by norm_num)
theorem B2443013 : Blo 1628513 2443013 := bbase (se 4 (by rfl) ⟨229032, by rfl⟩ : syracuseStep 2443013 = 458065) (by norm_num)
theorem B2443037 : Blo 1628513 2443037 := bbase (se 3 (by rfl) ⟨458069, by rfl⟩ : syracuseStep 2443037 = 916139) (by norm_num)
theorem B2443061 : Blo 1628513 2443061 := bbase (se 5 (by rfl) ⟨114518, by rfl⟩ : syracuseStep 2443061 = 229037) (by norm_num)
theorem B2443085 : Blo 1628513 2443085 := bbase (se 3 (by rfl) ⟨458078, by rfl⟩ : syracuseStep 2443085 = 916157) (by norm_num)
theorem B2443109 : Blo 1628513 2443109 := bbase (se 4 (by rfl) ⟨229041, by rfl⟩ : syracuseStep 2443109 = 458083) (by norm_num)
theorem B4122485 : Blo 1628513 4122485 := bbase (se 5 (by rfl) ⟨193241, by rfl⟩ : syracuseStep 4122485 = 386483) (by norm_num)
theorem B2443133 : Blo 1628513 2443133 := bbase (se 3 (by rfl) ⟨458087, by rfl⟩ : syracuseStep 2443133 = 916175) (by norm_num)
theorem B2443157 : Blo 1628513 2443157 := bbase (se 6 (by rfl) ⟨57261, by rfl⟩ : syracuseStep 2443157 = 114523) (by norm_num)
theorem B20875157 : Blo 1628513 20875157 := bbase (se 6 (by rfl) ⟨489261, by rfl⟩ : syracuseStep 20875157 = 978523) (by norm_num)
theorem B6186901 : Blo 1628513 6186901 := bbase (se 6 (by rfl) ⟨145005, by rfl⟩ : syracuseStep 6186901 = 290011) (by norm_num)
theorem B2443181 : Blo 1628513 2443181 := bbase (se 3 (by rfl) ⟨458096, by rfl⟩ : syracuseStep 2443181 = 916193) (by norm_num)
theorem B2443205 : Blo 1628513 2443205 := bbase (se 4 (by rfl) ⟨229050, by rfl⟩ : syracuseStep 2443205 = 458101) (by norm_num)
theorem B2443229 : Blo 1628513 2443229 := bbase (se 3 (by rfl) ⟨458105, by rfl⟩ : syracuseStep 2443229 = 916211) (by norm_num)
theorem B2443253 : Blo 1628513 2443253 := bbase (se 5 (by rfl) ⟨114527, by rfl⟩ : syracuseStep 2443253 = 229055) (by norm_num)
theorem B2320373 : Blo 1628513 2320373 := bbase (se 5 (by rfl) ⟨108767, by rfl⟩ : syracuseStep 2320373 = 217535) (by norm_num)
theorem B2443277 : Blo 1628513 2443277 := bbase (se 3 (by rfl) ⟨458114, by rfl⟩ : syracuseStep 2443277 = 916229) (by norm_num)
theorem B19810325 : Blo 1628513 19810325 := bbase (se 6 (by rfl) ⟨464304, by rfl⟩ : syracuseStep 19810325 = 928609) (by norm_num)
theorem B2443301 : Blo 1628513 2443301 := bbase (se 4 (by rfl) ⟨229059, by rfl⟩ : syracuseStep 2443301 = 458119) (by norm_num)
theorem B4122677 : Blo 1628513 4122677 := bbase (se 5 (by rfl) ⟨193250, by rfl⟩ : syracuseStep 4122677 = 386501) (by norm_num)
theorem B7153717 : Blo 1628513 7153717 := bbase (se 5 (by rfl) ⟨335330, by rfl⟩ : syracuseStep 7153717 = 670661) (by norm_num)
theorem B2443325 : Blo 1628513 2443325 := bbase (se 3 (by rfl) ⟨458123, by rfl⟩ : syracuseStep 2443325 = 916247) (by norm_num)
theorem B2476109 : Blo 1628513 2476109 := bbase (se 3 (by rfl) ⟨464270, by rfl⟩ : syracuseStep 2476109 = 928541) (by norm_num)
theorem B2443349 : Blo 1628513 2443349 := bbase (se 8 (by rfl) ⟨14316, by rfl⟩ : syracuseStep 2443349 = 28633) (by norm_num)
theorem B5498981 : Blo 1628513 5498981 := bbase (se 4 (by rfl) ⟨515529, by rfl⟩ : syracuseStep 5498981 = 1031059) (by norm_num)
theorem B2443373 : Blo 1628513 2443373 := bbase (se 3 (by rfl) ⟨458132, by rfl⟩ : syracuseStep 2443373 = 916265) (by norm_num)
theorem B2443397 : Blo 1628513 2443397 := bbase (se 4 (by rfl) ⟨229068, by rfl⟩ : syracuseStep 2443397 = 458137) (by norm_num)
theorem B2443421 : Blo 1628513 2443421 := bbase (se 3 (by rfl) ⟨458141, by rfl⟩ : syracuseStep 2443421 = 916283) (by norm_num)
theorem B2443445 : Blo 1628513 2443445 := bbase (se 5 (by rfl) ⟨114536, by rfl⟩ : syracuseStep 2443445 = 229073) (by norm_num)
theorem B6187205 : Blo 1628513 6187205 := bbase (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) (by norm_num)
theorem B1673417 : Blo 1628513 1673417 := bbase (se 2 (by rfl) ⟨627531, by rfl⟩ : syracuseStep 1673417 = 1255063) (by norm_num)
theorem B2443469 : Blo 1628513 2443469 := bbase (se 3 (by rfl) ⟨458150, by rfl⟩ : syracuseStep 2443469 = 916301) (by norm_num)
theorem B2443493 : Blo 1628513 2443493 := bbase (se 4 (by rfl) ⟨229077, by rfl⟩ : syracuseStep 2443493 = 458155) (by norm_num)
theorem B3303661 : Blo 1628513 3303661 := bbase (se 3 (by rfl) ⟨619436, by rfl⟩ : syracuseStep 3303661 = 1238873) (by norm_num)
theorem B2443517 : Blo 1628513 2443517 := bbase (se 3 (by rfl) ⟨458159, by rfl⟩ : syracuseStep 2443517 = 916319) (by norm_num)
theorem B2443541 : Blo 1628513 2443541 := bbase (se 6 (by rfl) ⟨57270, by rfl⟩ : syracuseStep 2443541 = 114541) (by norm_num)
theorem B2443565 : Blo 1628513 2443565 := bbase (se 3 (by rfl) ⟨458168, by rfl⟩ : syracuseStep 2443565 = 916337) (by norm_num)
theorem B2935109 : Blo 1628513 2935109 := bbase (se 4 (by rfl) ⟨275166, by rfl⟩ : syracuseStep 2935109 = 550333) (by norm_num)
theorem B2443589 : Blo 1628513 2443589 := bbase (se 4 (by rfl) ⟨229086, by rfl⟩ : syracuseStep 2443589 = 458173) (by norm_num)
theorem B3664205 : Blo 1628513 3664205 := bbase (se 3 (by rfl) ⟨687038, by rfl⟩ : syracuseStep 3664205 = 1374077) (by norm_num)
theorem B11741525 : Blo 1628513 11741525 := bbase (se 10 (by rfl) ⟨17199, by rfl⟩ : syracuseStep 11741525 = 34399) (by norm_num)
theorem B23816533 : Blo 1628513 23816533 := bbase (se 10 (by rfl) ⟨34887, by rfl⟩ : syracuseStep 23816533 = 69775) (by norm_num)
theorem B44607829 : Blo 1628513 44607829 := bbase (se 10 (by rfl) ⟨65343, by rfl⟩ : syracuseStep 44607829 = 130687) (by norm_num)
theorem B2443613 : Blo 1628513 2443613 := bbase (se 3 (by rfl) ⟨458177, by rfl⟩ : syracuseStep 2443613 = 916355) (by norm_num)
theorem B2443637 : Blo 1628513 2443637 := bbase (se 5 (by rfl) ⟨114545, by rfl⟩ : syracuseStep 2443637 = 229091) (by norm_num)
theorem B7833989 : Blo 1628513 7833989 := bbase (se 4 (by rfl) ⟨734436, by rfl⟩ : syracuseStep 7833989 = 1468873) (by norm_num)
theorem B4123021 : Blo 1628513 4123021 := bbase (se 3 (by rfl) ⟨773066, by rfl⟩ : syracuseStep 4123021 = 1546133) (by norm_num)
theorem B2443661 : Blo 1628513 2443661 := bbase (se 3 (by rfl) ⟨458186, by rfl⟩ : syracuseStep 2443661 = 916373) (by norm_num)
theorem B3664277 : Blo 1628513 3664277 := bbase (se 6 (by rfl) ⟨85881, by rfl⟩ : syracuseStep 3664277 = 171763) (by norm_num)
theorem B1739161 : Blo 1628513 1739161 := bbase (se 2 (by rfl) ⟨652185, by rfl⟩ : syracuseStep 1739161 = 1304371) (by norm_num)
theorem B2443685 : Blo 1628513 2443685 := bbase (se 4 (by rfl) ⟨229095, by rfl⟩ : syracuseStep 2443685 = 458191) (by norm_num)
theorem B4180405 : Blo 1628513 4180405 := bbase (se 5 (by rfl) ⟨195956, by rfl⟩ : syracuseStep 4180405 = 391913) (by norm_num)
theorem B2443709 : Blo 1628513 2443709 := bbase (se 3 (by rfl) ⟨458195, by rfl⟩ : syracuseStep 2443709 = 916391) (by norm_num)
theorem B2443733 : Blo 1628513 2443733 := bbase (se 7 (by rfl) ⟨28637, by rfl⟩ : syracuseStep 2443733 = 57275) (by norm_num)
theorem B3664349 : Blo 1628513 3664349 := bbase (se 3 (by rfl) ⟨687065, by rfl⟩ : syracuseStep 3664349 = 1374131) (by norm_num)
theorem B2443757 : Blo 1628513 2443757 := bbase (se 3 (by rfl) ⟨458204, by rfl⟩ : syracuseStep 2443757 = 916409) (by norm_num)
theorem B4123133 : Blo 1628513 4123133 := bbase (se 3 (by rfl) ⟨773087, by rfl⟩ : syracuseStep 4123133 = 1546175) (by norm_num)
theorem B2443781 : Blo 1628513 2443781 := bbase (se 4 (by rfl) ⟨229104, by rfl⟩ : syracuseStep 2443781 = 458209) (by norm_num)
theorem B5499413 : Blo 1628513 5499413 := bbase (se 6 (by rfl) ⟨128892, by rfl⟩ : syracuseStep 5499413 = 257785) (by norm_num)
theorem B2443805 : Blo 1628513 2443805 := bbase (se 3 (by rfl) ⟨458213, by rfl⟩ : syracuseStep 2443805 = 916427) (by norm_num)
theorem B3664421 : Blo 1628513 3664421 := bbase (se 4 (by rfl) ⟨343539, by rfl⟩ : syracuseStep 3664421 = 687079) (by norm_num)
theorem B9275957 : Blo 1628513 9275957 := bbase (se 5 (by rfl) ⟨434810, by rfl⟩ : syracuseStep 9275957 = 869621) (by norm_num)
theorem B2443829 : Blo 1628513 2443829 := bbase (se 5 (by rfl) ⟨114554, by rfl⟩ : syracuseStep 2443829 = 229109) (by norm_num)
theorem B2787901 : Blo 1628513 2787901 := bbase (se 3 (by rfl) ⟨522731, by rfl⟩ : syracuseStep 2787901 = 1045463) (by norm_num)
theorem B2443853 : Blo 1628513 2443853 := bbase (se 3 (by rfl) ⟨458222, by rfl⟩ : syracuseStep 2443853 = 916445) (by norm_num)
theorem B2443877 : Blo 1628513 2443877 := bbase (se 4 (by rfl) ⟨229113, by rfl⟩ : syracuseStep 2443877 = 458227) (by norm_num)
theorem B3664493 : Blo 1628513 3664493 := bbase (se 3 (by rfl) ⟨687092, by rfl⟩ : syracuseStep 3664493 = 1374185) (by norm_num)
theorem B2443901 : Blo 1628513 2443901 := bbase (se 3 (by rfl) ⟨458231, by rfl⟩ : syracuseStep 2443901 = 916463) (by norm_num)
theorem B7531157 : Blo 1628513 7531157 := bbase (se 6 (by rfl) ⟨176511, by rfl⟩ : syracuseStep 7531157 = 353023) (by norm_num)
theorem B2443925 : Blo 1628513 2443925 := bbase (se 6 (by rfl) ⟨57279, by rfl⟩ : syracuseStep 2443925 = 114559) (by norm_num)
theorem B2443949 : Blo 1628513 2443949 := bbase (se 3 (by rfl) ⟨458240, by rfl⟩ : syracuseStep 2443949 = 916481) (by norm_num)
theorem B3664565 : Blo 1628513 3664565 := bbase (se 5 (by rfl) ⟨171776, by rfl⟩ : syracuseStep 3664565 = 343553) (by norm_num)
theorem B4123325 : Blo 1628513 4123325 := bbase (se 3 (by rfl) ⟨773123, by rfl⟩ : syracuseStep 4123325 = 1546247) (by norm_num)
theorem B2443973 : Blo 1628513 2443973 := bbase (se 4 (by rfl) ⟨229122, by rfl⟩ : syracuseStep 2443973 = 458245) (by norm_num)
theorem B8252117 : Blo 1628513 8252117 := bbase (se 7 (by rfl) ⟨96704, by rfl⟩ : syracuseStep 8252117 = 193409) (by norm_num)
theorem B2443997 : Blo 1628513 2443997 := bbase (se 3 (by rfl) ⟨458249, by rfl⟩ : syracuseStep 2443997 = 916499) (by norm_num)
theorem B2444021 : Blo 1628513 2444021 := bbase (se 5 (by rfl) ⟨114563, by rfl⟩ : syracuseStep 2444021 = 229127) (by norm_num)
theorem B3664637 : Blo 1628513 3664637 := bbase (se 3 (by rfl) ⟨687119, by rfl⟩ : syracuseStep 3664637 = 1374239) (by norm_num)
theorem B4639493 : Blo 1628513 4639493 := bbase (se 4 (by rfl) ⟨434952, by rfl⟩ : syracuseStep 4639493 = 869905) (by norm_num)
theorem B2444045 : Blo 1628513 2444045 := bbase (se 3 (by rfl) ⟨458258, by rfl⟩ : syracuseStep 2444045 = 916517) (by norm_num)
theorem B2444069 : Blo 1628513 2444069 := bbase (se 4 (by rfl) ⟨229131, by rfl⟩ : syracuseStep 2444069 = 458263) (by norm_num)
theorem B2444093 : Blo 1628513 2444093 := bbase (se 3 (by rfl) ⟨458267, by rfl⟩ : syracuseStep 2444093 = 916535) (by norm_num)
theorem B3664709 : Blo 1628513 3664709 := bbase (se 4 (by rfl) ⟨343566, by rfl⟩ : syracuseStep 3664709 = 687133) (by norm_num)
theorem B1739605 : Blo 1628513 1739605 := bbase (se 9 (by rfl) ⟨5096, by rfl⟩ : syracuseStep 1739605 = 10193) (by norm_num)
theorem B2444117 : Blo 1628513 2444117 := bbase (se 9 (by rfl) ⟨7160, by rfl⟩ : syracuseStep 2444117 = 14321) (by norm_num)
theorem B2444141 : Blo 1628513 2444141 := bbase (se 3 (by rfl) ⟨458276, by rfl⟩ : syracuseStep 2444141 = 916553) (by norm_num)
theorem B2444165 : Blo 1628513 2444165 := bbase (se 4 (by rfl) ⟨229140, by rfl⟩ : syracuseStep 2444165 = 458281) (by norm_num)
theorem B3664781 : Blo 1628513 3664781 := bbase (se 3 (by rfl) ⟨687146, by rfl⟩ : syracuseStep 3664781 = 1374293) (by norm_num)
theorem B1739665 : Blo 1628513 1739665 := bbase (se 2 (by rfl) ⟨652374, by rfl⟩ : syracuseStep 1739665 = 1304749) (by norm_num)
theorem B21752725 : Blo 1628513 21752725 := bbase (se 6 (by rfl) ⟨509829, by rfl⟩ : syracuseStep 21752725 = 1019659) (by norm_num)
theorem B2444189 : Blo 1628513 2444189 := bbase (se 3 (by rfl) ⟨458285, by rfl⟩ : syracuseStep 2444189 = 916571) (by norm_num)
theorem B2444213 : Blo 1628513 2444213 := bbase (se 5 (by rfl) ⟨114572, by rfl⟩ : syracuseStep 2444213 = 229145) (by norm_num)
theorem B5499845 : Blo 1628513 5499845 := bbase (se 4 (by rfl) ⟨515610, by rfl⟩ : syracuseStep 5499845 = 1031221) (by norm_num)
theorem B2444237 : Blo 1628513 2444237 := bbase (se 3 (by rfl) ⟨458294, by rfl⟩ : syracuseStep 2444237 = 916589) (by norm_num)
theorem B3664853 : Blo 1628513 3664853 := bbase (se 7 (by rfl) ⟨42947, by rfl⟩ : syracuseStep 3664853 = 85895) (by norm_num)
theorem B2444261 : Blo 1628513 2444261 := bbase (se 4 (by rfl) ⟨229149, by rfl⟩ : syracuseStep 2444261 = 458299) (by norm_num)
theorem B2444285 : Blo 1628513 2444285 := bbase (se 3 (by rfl) ⟨458303, by rfl⟩ : syracuseStep 2444285 = 916607) (by norm_num)
theorem B4123669 : Blo 1628513 4123669 := bbase (se 6 (by rfl) ⟨96648, by rfl⟩ : syracuseStep 4123669 = 193297) (by norm_num)
theorem B2444309 : Blo 1628513 2444309 := bbase (se 6 (by rfl) ⟨57288, by rfl⟩ : syracuseStep 2444309 = 114577) (by norm_num)
theorem B3664925 : Blo 1628513 3664925 := bbase (se 3 (by rfl) ⟨687173, by rfl⟩ : syracuseStep 3664925 = 1374347) (by norm_num)
theorem B2444333 : Blo 1628513 2444333 := bbase (se 3 (by rfl) ⟨458312, by rfl⟩ : syracuseStep 2444333 = 916625) (by norm_num)
theorem B2444357 : Blo 1628513 2444357 := bbase (se 4 (by rfl) ⟨229158, by rfl⟩ : syracuseStep 2444357 = 458317) (by norm_num)
theorem B2935901 : Blo 1628513 2935901 := bbase (se 3 (by rfl) ⟨550481, by rfl⟩ : syracuseStep 2935901 = 1100963) (by norm_num)
theorem B2444381 : Blo 1628513 2444381 := bbase (se 3 (by rfl) ⟨458321, by rfl⟩ : syracuseStep 2444381 = 916643) (by norm_num)
theorem B3664997 : Blo 1628513 3664997 := bbase (se 4 (by rfl) ⟨343593, by rfl⟩ : syracuseStep 3664997 = 687187) (by norm_num)
theorem B2444405 : Blo 1628513 2444405 := bbase (se 5 (by rfl) ⟨114581, by rfl⟩ : syracuseStep 2444405 = 229163) (by norm_num)
theorem B2976893 : Blo 1628513 2976893 := bbase (se 3 (by rfl) ⟨558167, by rfl⟩ : syracuseStep 2976893 = 1116335) (by norm_num)
theorem B4123781 : Blo 1628513 4123781 := bbase (se 4 (by rfl) ⟨386604, by rfl⟩ : syracuseStep 4123781 = 773209) (by norm_num)
theorem B2444429 : Blo 1628513 2444429 := bbase (se 3 (by rfl) ⟨458330, by rfl⟩ : syracuseStep 2444429 = 916661) (by norm_num)
theorem B2444453 : Blo 1628513 2444453 := bbase (se 4 (by rfl) ⟨229167, by rfl⟩ : syracuseStep 2444453 = 458335) (by norm_num)
theorem B3665069 : Blo 1628513 3665069 := bbase (se 3 (by rfl) ⟨687200, by rfl⟩ : syracuseStep 3665069 = 1374401) (by norm_num)
theorem B2444477 : Blo 1628513 2444477 := bbase (se 3 (by rfl) ⟨458339, by rfl⟩ : syracuseStep 2444477 = 916679) (by norm_num)
theorem B1674437 : Blo 1628513 1674437 := bbase (se 4 (by rfl) ⟨156978, by rfl⟩ : syracuseStep 1674437 = 313957) (by norm_num)
theorem B1739981 : Blo 1628513 1739981 := bbase (se 3 (by rfl) ⟨326246, by rfl⟩ : syracuseStep 1739981 = 652493) (by norm_num)
theorem B11144405 : Blo 1628513 11144405 := bbase (se 7 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 11144405 = 261197) (by norm_num)
theorem B2444501 : Blo 1628513 2444501 := bbase (se 7 (by rfl) ⟨28646, by rfl⟩ : syracuseStep 2444501 = 57293) (by norm_num)
theorem B2936045 : Blo 1628513 2936045 := bbase (se 3 (by rfl) ⟨550508, by rfl⟩ : syracuseStep 2936045 = 1101017) (by norm_num)
theorem B2444525 : Blo 1628513 2444525 := bbase (se 3 (by rfl) ⟨458348, by rfl⟩ : syracuseStep 2444525 = 916697) (by norm_num)
theorem B3665141 : Blo 1628513 3665141 := bbase (se 5 (by rfl) ⟨171803, by rfl⟩ : syracuseStep 3665141 = 343607) (by norm_num)
theorem B2444549 : Blo 1628513 2444549 := bbase (se 4 (by rfl) ⟨229176, by rfl⟩ : syracuseStep 2444549 = 458353) (by norm_num)
theorem B21155093 : Blo 1628513 21155093 := bbase (se 6 (by rfl) ⟨495822, by rfl⟩ : syracuseStep 21155093 = 991645) (by norm_num)
theorem B2444573 : Blo 1628513 2444573 := bbase (se 3 (by rfl) ⟨458357, by rfl⟩ : syracuseStep 2444573 = 916715) (by norm_num)
theorem B4181285 : Blo 1628513 4181285 := bbase (se 4 (by rfl) ⟨391995, by rfl⟩ : syracuseStep 4181285 = 783991) (by norm_num)
theorem B3091765 : Blo 1628513 3091765 := bbase (se 5 (by rfl) ⟨144926, by rfl⟩ : syracuseStep 3091765 = 289853) (by norm_num)
theorem B2444597 : Blo 1628513 2444597 := bbase (se 5 (by rfl) ⟨114590, by rfl⟩ : syracuseStep 2444597 = 229181) (by norm_num)
theorem B5221685 : Blo 1628513 5221685 := bbase (se 5 (by rfl) ⟨244766, by rfl⟩ : syracuseStep 5221685 = 489533) (by norm_num)
theorem B3665213 : Blo 1628513 3665213 := bbase (se 3 (by rfl) ⟨687227, by rfl⟩ : syracuseStep 3665213 = 1374455) (by norm_num)
theorem B2936125 : Blo 1628513 2936125 := bbase (se 3 (by rfl) ⟨550523, by rfl⟩ : syracuseStep 2936125 = 1101047) (by norm_num)
theorem B4123973 : Blo 1628513 4123973 := bbase (se 4 (by rfl) ⟨386622, by rfl⟩ : syracuseStep 4123973 = 773245) (by norm_num)
theorem B2444621 : Blo 1628513 2444621 := bbase (se 3 (by rfl) ⟨458366, by rfl⟩ : syracuseStep 2444621 = 916733) (by norm_num)
theorem B2444645 : Blo 1628513 2444645 := bbase (se 4 (by rfl) ⟨229185, by rfl⟩ : syracuseStep 2444645 = 458371) (by norm_num)
theorem B5500277 : Blo 1628513 5500277 := bbase (se 5 (by rfl) ⟨257825, by rfl⟩ : syracuseStep 5500277 = 515651) (by norm_num)
theorem B2936189 : Blo 1628513 2936189 := bbase (se 3 (by rfl) ⟨550535, by rfl⟩ : syracuseStep 2936189 = 1101071) (by norm_num)
theorem B2444669 : Blo 1628513 2444669 := bbase (se 3 (by rfl) ⟨458375, by rfl⟩ : syracuseStep 2444669 = 916751) (by norm_num)
theorem B3665285 : Blo 1628513 3665285 := bbase (se 4 (by rfl) ⟨343620, by rfl⟩ : syracuseStep 3665285 = 687241) (by norm_num)
theorem B2444693 : Blo 1628513 2444693 := bbase (se 6 (by rfl) ⟨57297, by rfl⟩ : syracuseStep 2444693 = 114595) (by norm_num)
theorem B2444717 : Blo 1628513 2444717 := bbase (se 3 (by rfl) ⟨458384, by rfl⟩ : syracuseStep 2444717 = 916769) (by norm_num)
theorem B2444741 : Blo 1628513 2444741 := bbase (se 4 (by rfl) ⟨229194, by rfl⟩ : syracuseStep 2444741 = 458389) (by norm_num)
theorem B3665357 : Blo 1628513 3665357 := bbase (se 3 (by rfl) ⟨687254, by rfl⟩ : syracuseStep 3665357 = 1374509) (by norm_num)
theorem B3091925 : Blo 1628513 3091925 := bbase (se 7 (by rfl) ⟨36233, by rfl⟩ : syracuseStep 3091925 = 72467) (by norm_num)
theorem B2444765 : Blo 1628513 2444765 := bbase (se 3 (by rfl) ⟨458393, by rfl⟩ : syracuseStep 2444765 = 916787) (by norm_num)
theorem B2608613 : Blo 1628513 2608613 := bbase (se 4 (by rfl) ⟨244557, by rfl⟩ : syracuseStep 2608613 = 489115) (by norm_num)
theorem B2444789 : Blo 1628513 2444789 := bbase (se 5 (by rfl) ⟨114599, by rfl⟩ : syracuseStep 2444789 = 229199) (by norm_num)
theorem B3304957 : Blo 1628513 3304957 := bbase (se 3 (by rfl) ⟨619679, by rfl⟩ : syracuseStep 3304957 = 1239359) (by norm_num)
theorem B1764865 : Blo 1628513 1764865 := bbase (se 2 (by rfl) ⟨661824, by rfl⟩ : syracuseStep 1764865 = 1323649) (by norm_num)
theorem B2444813 : Blo 1628513 2444813 := bbase (se 3 (by rfl) ⟨458402, by rfl⟩ : syracuseStep 2444813 = 916805) (by norm_num)
theorem B3665429 : Blo 1628513 3665429 := bbase (se 6 (by rfl) ⟨85908, by rfl⟩ : syracuseStep 3665429 = 171817) (by norm_num)
theorem B2444837 : Blo 1628513 2444837 := bbase (se 4 (by rfl) ⟨229203, by rfl⟩ : syracuseStep 2444837 = 458407) (by norm_num)
theorem B2444861 : Blo 1628513 2444861 := bbase (se 3 (by rfl) ⟨458411, by rfl⟩ : syracuseStep 2444861 = 916823) (by norm_num)
theorem B29724245 : Blo 1628513 29724245 := bbase (se 8 (by rfl) ⟨174165, by rfl⟩ : syracuseStep 29724245 = 348331) (by norm_num)
theorem B2444885 : Blo 1628513 2444885 := bbase (se 8 (by rfl) ⟨14325, by rfl⟩ : syracuseStep 2444885 = 28651) (by norm_num)
theorem B3665501 : Blo 1628513 3665501 := bbase (se 3 (by rfl) ⟨687281, by rfl⟩ : syracuseStep 3665501 = 1374563) (by norm_num)
theorem B3092069 : Blo 1628513 3092069 := bbase (se 4 (by rfl) ⟨289881, by rfl⟩ : syracuseStep 3092069 = 579763) (by norm_num)
theorem B2444909 : Blo 1628513 2444909 := bbase (se 3 (by rfl) ⟨458420, by rfl⟩ : syracuseStep 2444909 = 916841) (by norm_num)
theorem B2444933 : Blo 1628513 2444933 := bbase (se 4 (by rfl) ⟨229212, by rfl⟩ : syracuseStep 2444933 = 458425) (by norm_num)
theorem B1740425 : Blo 1628513 1740425 := bbase (se 2 (by rfl) ⟨652659, by rfl⟩ : syracuseStep 1740425 = 1305319) (by norm_num)
theorem B4124317 : Blo 1628513 4124317 := bbase (se 3 (by rfl) ⟨773309, by rfl⟩ : syracuseStep 4124317 = 1546619) (by norm_num)
theorem B2444957 : Blo 1628513 2444957 := bbase (se 3 (by rfl) ⟨458429, by rfl⟩ : syracuseStep 2444957 = 916859) (by norm_num)
theorem B3665573 : Blo 1628513 3665573 := bbase (se 4 (by rfl) ⟨343647, by rfl⟩ : syracuseStep 3665573 = 687295) (by norm_num)
theorem B10440373 : Blo 1628513 10440373 := bbase (se 5 (by rfl) ⟨489392, by rfl⟩ : syracuseStep 10440373 = 978785) (by norm_num)
theorem B2444981 : Blo 1628513 2444981 := bbase (se 5 (by rfl) ⟨114608, by rfl⟩ : syracuseStep 2444981 = 229217) (by norm_num)
theorem B1740485 : Blo 1628513 1740485 := bbase (se 4 (by rfl) ⟨163170, by rfl⟩ : syracuseStep 1740485 = 326341) (by norm_num)
theorem B2445005 : Blo 1628513 2445005 := bbase (se 3 (by rfl) ⟨458438, by rfl⟩ : syracuseStep 2445005 = 916877) (by norm_num)
theorem B2445029 : Blo 1628513 2445029 := bbase (se 4 (by rfl) ⟨229221, by rfl⟩ : syracuseStep 2445029 = 458443) (by norm_num)
theorem B3665645 : Blo 1628513 3665645 := bbase (se 3 (by rfl) ⟨687308, by rfl⟩ : syracuseStep 3665645 = 1374617) (by norm_num)
theorem B2445053 : Blo 1628513 2445053 := bbase (se 3 (by rfl) ⟨458447, by rfl⟩ : syracuseStep 2445053 = 916895) (by norm_num)
theorem B7827205 : Blo 1628513 7827205 := bbase (se 4 (by rfl) ⟨733800, by rfl⟩ : syracuseStep 7827205 = 1467601) (by norm_num)
theorem B4124429 : Blo 1628513 4124429 := bbase (se 3 (by rfl) ⟨773330, by rfl⟩ : syracuseStep 4124429 = 1546661) (by norm_num)
theorem B2748181 : Blo 1628513 2748181 := bbase (se 6 (by rfl) ⟨64410, by rfl⟩ : syracuseStep 2748181 = 128821) (by norm_num)
theorem B2445077 : Blo 1628513 2445077 := bbase (se 6 (by rfl) ⟨57306, by rfl⟩ : syracuseStep 2445077 = 114613) (by norm_num)
theorem B5500709 : Blo 1628513 5500709 := bbase (se 4 (by rfl) ⟨515691, by rfl⟩ : syracuseStep 5500709 = 1031383) (by norm_num)
theorem B2445101 : Blo 1628513 2445101 := bbase (se 3 (by rfl) ⟨458456, by rfl⟩ : syracuseStep 2445101 = 916913) (by norm_num)
theorem B3665717 : Blo 1628513 3665717 := bbase (se 5 (by rfl) ⟨171830, by rfl⟩ : syracuseStep 3665717 = 343661) (by norm_num)
theorem B1740613 : Blo 1628513 1740613 := bbase (se 4 (by rfl) ⟨163182, by rfl⟩ : syracuseStep 1740613 = 326365) (by norm_num)
theorem B2445125 : Blo 1628513 2445125 := bbase (se 4 (by rfl) ⟨229230, by rfl⟩ : syracuseStep 2445125 = 458461) (by norm_num)
theorem B2445149 : Blo 1628513 2445149 := bbase (se 3 (by rfl) ⟨458465, by rfl⟩ : syracuseStep 2445149 = 916931) (by norm_num)
theorem B4181861 : Blo 1628513 4181861 := bbase (se 4 (by rfl) ⟨392049, by rfl⟩ : syracuseStep 4181861 = 784099) (by norm_num)
theorem B2748269 : Blo 1628513 2748269 := bbase (se 3 (by rfl) ⟨515300, by rfl⟩ : syracuseStep 2748269 = 1030601) (by norm_num)
theorem B2445173 : Blo 1628513 2445173 := bbase (se 5 (by rfl) ⟨114617, by rfl⟩ : syracuseStep 2445173 = 229235) (by norm_num)
theorem B3665789 : Blo 1628513 3665789 := bbase (se 3 (by rfl) ⟨687335, by rfl⟩ : syracuseStep 3665789 = 1374671) (by norm_num)
theorem B3092357 : Blo 1628513 3092357 := bbase (se 4 (by rfl) ⟨289908, by rfl⟩ : syracuseStep 3092357 = 579817) (by norm_num)
theorem B6270853 : Blo 1628513 6270853 := bbase (se 4 (by rfl) ⟨587892, by rfl⟩ : syracuseStep 6270853 = 1175785) (by norm_num)
theorem B2445197 : Blo 1628513 2445197 := bbase (se 3 (by rfl) ⟨458474, by rfl⟩ : syracuseStep 2445197 = 916949) (by norm_num)
theorem B2445221 : Blo 1628513 2445221 := bbase (se 4 (by rfl) ⟨229239, by rfl⟩ : syracuseStep 2445221 = 458479) (by norm_num)
theorem B2445245 : Blo 1628513 2445245 := bbase (se 3 (by rfl) ⟨458483, by rfl⟩ : syracuseStep 2445245 = 916967) (by norm_num)
theorem B3665861 : Blo 1628513 3665861 := bbase (se 4 (by rfl) ⟨343674, by rfl⟩ : syracuseStep 3665861 = 687349) (by norm_num)
theorem B4124621 : Blo 1628513 4124621 := bbase (se 3 (by rfl) ⟨773366, by rfl⟩ : syracuseStep 4124621 = 1546733) (by norm_num)
theorem B2445269 : Blo 1628513 2445269 := bbase (se 7 (by rfl) ⟨28655, by rfl⟩ : syracuseStep 2445269 = 57311) (by norm_num)
theorem B8253413 : Blo 1628513 8253413 := bbase (se 4 (by rfl) ⟨773757, by rfl⟩ : syracuseStep 8253413 = 1547515) (by norm_num)
theorem B2748397 : Blo 1628513 2748397 := bbase (se 3 (by rfl) ⟨515324, by rfl⟩ : syracuseStep 2748397 = 1030649) (by norm_num)
theorem B2445293 : Blo 1628513 2445293 := bbase (se 3 (by rfl) ⟨458492, by rfl⟩ : syracuseStep 2445293 = 916985) (by norm_num)
theorem B2445317 : Blo 1628513 2445317 := bbase (se 4 (by rfl) ⟨229248, by rfl⟩ : syracuseStep 2445317 = 458497) (by norm_num)
theorem B3665933 : Blo 1628513 3665933 := bbase (se 3 (by rfl) ⟨687362, by rfl⟩ : syracuseStep 3665933 = 1374725) (by norm_num)
theorem B3092509 : Blo 1628513 3092509 := bbase (se 3 (by rfl) ⟨579845, by rfl⟩ : syracuseStep 3092509 = 1159691) (by norm_num)
theorem B2445341 : Blo 1628513 2445341 := bbase (se 3 (by rfl) ⟨458501, by rfl⟩ : syracuseStep 2445341 = 917003) (by norm_num)
theorem B2445365 : Blo 1628513 2445365 := bbase (se 5 (by rfl) ⟨114626, by rfl⟩ : syracuseStep 2445365 = 229253) (by norm_num)
theorem B2748485 : Blo 1628513 2748485 := bbase (se 4 (by rfl) ⟨257670, by rfl⟩ : syracuseStep 2748485 = 515341) (by norm_num)
theorem B2445389 : Blo 1628513 2445389 := bbase (se 3 (by rfl) ⟨458510, by rfl⟩ : syracuseStep 2445389 = 917021) (by norm_num)
theorem B3715157 : Blo 1628513 3715157 := bbase (se 8 (by rfl) ⟨21768, by rfl⟩ : syracuseStep 3715157 = 43537) (by norm_num)
theorem B3666005 : Blo 1628513 3666005 := bbase (se 8 (by rfl) ⟨21480, by rfl⟩ : syracuseStep 3666005 = 42961) (by norm_num)
theorem B4182101 : Blo 1628513 4182101 := bbase (se 8 (by rfl) ⟨24504, by rfl⟩ : syracuseStep 4182101 = 49009) (by norm_num)
theorem B2445413 : Blo 1628513 2445413 := bbase (se 4 (by rfl) ⟨229257, by rfl⟩ : syracuseStep 2445413 = 458515) (by norm_num)
theorem B2445437 : Blo 1628513 2445437 := bbase (se 3 (by rfl) ⟨458519, by rfl⟩ : syracuseStep 2445437 = 917039) (by norm_num)
theorem B2445461 : Blo 1628513 2445461 := bbase (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) (by norm_num)
theorem B3666077 : Blo 1628513 3666077 := bbase (se 3 (by rfl) ⟨687389, by rfl⟩ : syracuseStep 3666077 = 1374779) (by norm_num)
theorem B3969181 : Blo 1628513 3969181 := bbase (se 3 (by rfl) ⟨744221, by rfl⟩ : syracuseStep 3969181 = 1488443) (by norm_num)
theorem B2445485 : Blo 1628513 2445485 := bbase (se 3 (by rfl) ⟨458528, by rfl⟩ : syracuseStep 2445485 = 917057) (by norm_num)
theorem B2748613 : Blo 1628513 2748613 := bbase (se 4 (by rfl) ⟨257682, by rfl⟩ : syracuseStep 2748613 = 515365) (by norm_num)
theorem B2445509 : Blo 1628513 2445509 := bbase (se 4 (by rfl) ⟨229266, by rfl⟩ : syracuseStep 2445509 = 458533) (by norm_num)
theorem B5501141 : Blo 1628513 5501141 := bbase (se 7 (by rfl) ⟨64466, by rfl⟩ : syracuseStep 5501141 = 128933) (by norm_num)
theorem B2445533 : Blo 1628513 2445533 := bbase (se 3 (by rfl) ⟨458537, by rfl⟩ : syracuseStep 2445533 = 917075) (by norm_num)
theorem B3666149 : Blo 1628513 3666149 := bbase (se 4 (by rfl) ⟨343701, by rfl⟩ : syracuseStep 3666149 = 687403) (by norm_num)
theorem B2445557 : Blo 1628513 2445557 := bbase (se 5 (by rfl) ⟨114635, by rfl⟩ : syracuseStep 2445557 = 229271) (by norm_num)
theorem B1741057 : Blo 1628513 1741057 := bbase (se 2 (by rfl) ⟨652896, by rfl⟩ : syracuseStep 1741057 = 1305793) (by norm_num)
theorem B6189317 : Blo 1628513 6189317 := bbase (se 4 (by rfl) ⟨580248, by rfl⟩ : syracuseStep 6189317 = 1160497) (by norm_num)
theorem B2445581 : Blo 1628513 2445581 := bbase (se 3 (by rfl) ⟨458546, by rfl⟩ : syracuseStep 2445581 = 917093) (by norm_num)
theorem B2748701 : Blo 1628513 2748701 := bbase (se 3 (by rfl) ⟨515381, by rfl⟩ : syracuseStep 2748701 = 1030763) (by norm_num)
theorem B4124965 : Blo 1628513 4124965 := bbase (se 4 (by rfl) ⟨386715, by rfl⟩ : syracuseStep 4124965 = 773431) (by norm_num)
theorem B2445605 : Blo 1628513 2445605 := bbase (se 4 (by rfl) ⟨229275, by rfl⟩ : syracuseStep 2445605 = 458551) (by norm_num)
theorem B3666221 : Blo 1628513 3666221 := bbase (se 3 (by rfl) ⟨687416, by rfl⟩ : syracuseStep 3666221 = 1374833) (by norm_num)
theorem B4641077 : Blo 1628513 4641077 := bbase (se 5 (by rfl) ⟨217550, by rfl⟩ : syracuseStep 4641077 = 435101) (by norm_num)
theorem B2445629 : Blo 1628513 2445629 := bbase (se 3 (by rfl) ⟨458555, by rfl⟩ : syracuseStep 2445629 = 917111) (by norm_num)
theorem B6959429 : Blo 1628513 6959429 := bbase (se 4 (by rfl) ⟨652446, by rfl⟩ : syracuseStep 6959429 = 1304893) (by norm_num)
theorem B3092813 : Blo 1628513 3092813 := bbase (se 3 (by rfl) ⟨579902, by rfl⟩ : syracuseStep 3092813 = 1159805) (by norm_num)
theorem B23482709 : Blo 1628513 23482709 := bbase (se 10 (by rfl) ⟨34398, by rfl⟩ : syracuseStep 23482709 = 68797) (by norm_num)
theorem B2445653 : Blo 1628513 2445653 := bbase (se 10 (by rfl) ⟨3582, by rfl⟩ : syracuseStep 2445653 = 7165) (by norm_num)
theorem B2445677 : Blo 1628513 2445677 := bbase (se 3 (by rfl) ⟨458564, by rfl⟩ : syracuseStep 2445677 = 917129) (by norm_num)
theorem B3666293 : Blo 1628513 3666293 := bbase (se 5 (by rfl) ⟨171857, by rfl⟩ : syracuseStep 3666293 = 343715) (by norm_num)
theorem B1741177 : Blo 1628513 1741177 := bbase (se 2 (by rfl) ⟨652941, by rfl⟩ : syracuseStep 1741177 = 1305883) (by norm_num)
theorem B8245637 : Blo 1628513 8245637 := bbase (se 4 (by rfl) ⟨773028, by rfl⟩ : syracuseStep 8245637 = 1546057) (by norm_num)
theorem B5222789 : Blo 1628513 5222789 := bbase (se 4 (by rfl) ⟨489636, by rfl⟩ : syracuseStep 5222789 = 979273) (by norm_num)
theorem B2445701 : Blo 1628513 2445701 := bbase (se 4 (by rfl) ⟨229284, by rfl⟩ : syracuseStep 2445701 = 458569) (by norm_num)
theorem B4125077 : Blo 1628513 4125077 := bbase (se 6 (by rfl) ⟨96681, by rfl⟩ : syracuseStep 4125077 = 193363) (by norm_num)
theorem B2748829 : Blo 1628513 2748829 := bbase (se 3 (by rfl) ⟨515405, by rfl⟩ : syracuseStep 2748829 = 1030811) (by norm_num)
theorem B2445725 : Blo 1628513 2445725 := bbase (se 3 (by rfl) ⟨458573, by rfl⟩ : syracuseStep 2445725 = 917147) (by norm_num)
theorem B2445749 : Blo 1628513 2445749 := bbase (se 5 (by rfl) ⟨114644, by rfl⟩ : syracuseStep 2445749 = 229289) (by norm_num)
theorem B3666365 : Blo 1628513 3666365 := bbase (se 3 (by rfl) ⟨687443, by rfl⟩ : syracuseStep 3666365 = 1374887) (by norm_num)
theorem B2748917 : Blo 1628513 2748917 := bbase (se 5 (by rfl) ⟨128855, by rfl⟩ : syracuseStep 2748917 = 257711) (by norm_num)
theorem B3666437 : Blo 1628513 3666437 := bbase (se 4 (by rfl) ⟨343728, by rfl⟩ : syracuseStep 3666437 = 687457) (by norm_num)
theorem B21172757 : Blo 1628513 21172757 := bbase (se 6 (by rfl) ⟨496236, by rfl⟩ : syracuseStep 21172757 = 992473) (by norm_num)
theorem B6189605 : Blo 1628513 6189605 := bbase (se 4 (by rfl) ⟨580275, by rfl⟩ : syracuseStep 6189605 = 1160551) (by norm_num)
theorem B2609741 : Blo 1628513 2609741 := bbase (se 3 (by rfl) ⟨489326, by rfl⟩ : syracuseStep 2609741 = 978653) (by norm_num)
theorem B3666509 : Blo 1628513 3666509 := bbase (se 3 (by rfl) ⟨687470, by rfl⟩ : syracuseStep 3666509 = 1374941) (by norm_num)
theorem B4125269 : Blo 1628513 4125269 := bbase (se 8 (by rfl) ⟨24171, by rfl⟩ : syracuseStep 4125269 = 48343) (by norm_num)
theorem B2749045 : Blo 1628513 2749045 := bbase (se 5 (by rfl) ⟨128861, by rfl⟩ : syracuseStep 2749045 = 257723) (by norm_num)
theorem B5501573 : Blo 1628513 5501573 := bbase (se 4 (by rfl) ⟨515772, by rfl⟩ : syracuseStep 5501573 = 1031545) (by norm_num)
theorem B3666581 : Blo 1628513 3666581 := bbase (se 6 (by rfl) ⟨85935, by rfl⟩ : syracuseStep 3666581 = 171871) (by norm_num)
theorem B5870245 : Blo 1628513 5870245 := bbase (se 4 (by rfl) ⟨550335, by rfl⟩ : syracuseStep 5870245 = 1100671) (by norm_num)
theorem B2749133 : Blo 1628513 2749133 := bbase (se 3 (by rfl) ⟨515462, by rfl⟩ : syracuseStep 2749133 = 1030925) (by norm_num)
theorem B9278165 : Blo 1628513 9278165 := bbase (se 7 (by rfl) ⟨108728, by rfl⟩ : syracuseStep 9278165 = 217457) (by norm_num)
theorem B3666653 : Blo 1628513 3666653 := bbase (se 3 (by rfl) ⟨687497, by rfl⟩ : syracuseStep 3666653 = 1374995) (by norm_num)
theorem B2478845 : Blo 1628513 2478845 := bbase (se 3 (by rfl) ⟨464783, by rfl⟩ : syracuseStep 2478845 = 929567) (by norm_num)
theorem B3666725 : Blo 1628513 3666725 := bbase (se 4 (by rfl) ⟨343755, by rfl⟩ : syracuseStep 3666725 = 687511) (by norm_num)
theorem B2061121 : Blo 1628513 2061121 := bbase (se 2 (by rfl) ⟨772920, by rfl⟩ : syracuseStep 2061121 = 1545841) (by norm_num)
theorem B2749261 : Blo 1628513 2749261 := bbase (se 3 (by rfl) ⟨515486, by rfl⟩ : syracuseStep 2749261 = 1030973) (by norm_num)
theorem B8934229 : Blo 1628513 8934229 := bbase (se 9 (by rfl) ⟨26174, by rfl⟩ : syracuseStep 8934229 = 52349) (by norm_num)
theorem B3478373 : Blo 1628513 3478373 := bbase (se 4 (by rfl) ⟨326097, by rfl⟩ : syracuseStep 3478373 = 652195) (by norm_num)
theorem B3666797 : Blo 1628513 3666797 := bbase (se 3 (by rfl) ⟨687524, by rfl⟩ : syracuseStep 3666797 = 1375049) (by norm_num)
theorem B2061217 : Blo 1628513 2061217 := bbase (se 2 (by rfl) ⟨772956, by rfl⟩ : syracuseStep 2061217 = 1545913) (by norm_num)
theorem B2749349 : Blo 1628513 2749349 := bbase (se 4 (by rfl) ⟨257751, by rfl⟩ : syracuseStep 2749349 = 515503) (by norm_num)
theorem B4125613 : Blo 1628513 4125613 := bbase (se 3 (by rfl) ⟨773552, by rfl⟩ : syracuseStep 4125613 = 1547105) (by norm_num)
theorem B13915061 : Blo 1628513 13915061 := bbase (se 5 (by rfl) ⟨652268, by rfl⟩ : syracuseStep 13915061 = 1304537) (by norm_num)
theorem B3666869 : Blo 1628513 3666869 := bbase (se 5 (by rfl) ⟨171884, by rfl⟩ : syracuseStep 3666869 = 343769) (by norm_num)
theorem B4641749 : Blo 1628513 4641749 := bbase (se 7 (by rfl) ⟨54395, by rfl⟩ : syracuseStep 4641749 = 108791) (by norm_num)
theorem B4404197 : Blo 1628513 4404197 := bbase (se 4 (by rfl) ⟨412893, by rfl⟩ : syracuseStep 4404197 = 825787) (by norm_num)
theorem B3666941 : Blo 1628513 3666941 := bbase (se 3 (by rfl) ⟨687551, by rfl⟩ : syracuseStep 3666941 = 1375103) (by norm_num)
theorem B4125725 : Blo 1628513 4125725 := bbase (se 3 (by rfl) ⟨773573, by rfl⟩ : syracuseStep 4125725 = 1547147) (by norm_num)
theorem B2749477 : Blo 1628513 2749477 := bbase (se 4 (by rfl) ⟨257763, by rfl⟩ : syracuseStep 2749477 = 515527) (by norm_num)
theorem B5502005 : Blo 1628513 5502005 := bbase (se 5 (by rfl) ⟨257906, by rfl⟩ : syracuseStep 5502005 = 515813) (by norm_num)
theorem B4183093 : Blo 1628513 4183093 := bbase (se 5 (by rfl) ⟨196082, by rfl⟩ : syracuseStep 4183093 = 392165) (by norm_num)
theorem B3093565 : Blo 1628513 3093565 := bbase (se 3 (by rfl) ⟨580043, by rfl⟩ : syracuseStep 3093565 = 1160087) (by norm_num)
theorem B3667013 : Blo 1628513 3667013 := bbase (se 4 (by rfl) ⟨343782, by rfl⟩ : syracuseStep 3667013 = 687565) (by norm_num)
theorem B2061389 : Blo 1628513 2061389 := bbase (se 3 (by rfl) ⟨386510, by rfl⟩ : syracuseStep 2061389 = 773021) (by norm_num)
theorem B2610253 : Blo 1628513 2610253 := bbase (se 3 (by rfl) ⟨489422, by rfl⟩ : syracuseStep 2610253 = 978845) (by norm_num)
theorem B27858005 : Blo 1628513 27858005 := bbase (se 8 (by rfl) ⟨163230, by rfl⟩ : syracuseStep 27858005 = 326461) (by norm_num)
theorem B3478621 : Blo 1628513 3478621 := bbase (se 3 (by rfl) ⟨652241, by rfl⟩ : syracuseStep 3478621 = 1304483) (by norm_num)
theorem B2749565 : Blo 1628513 2749565 := bbase (se 3 (by rfl) ⟨515543, by rfl⟩ : syracuseStep 2749565 = 1031087) (by norm_num)
theorem B2061445 : Blo 1628513 2061445 := bbase (se 4 (by rfl) ⟨193260, by rfl⟩ : syracuseStep 2061445 = 386521) (by norm_num)
theorem B3667085 : Blo 1628513 3667085 := bbase (se 3 (by rfl) ⟨687578, by rfl⟩ : syracuseStep 3667085 = 1375157) (by norm_num)
theorem B1832089 : Blo 1628513 1832089 := bbase (se 2 (by rfl) ⟨687033, by rfl⟩ : syracuseStep 1832089 = 1374067) (by norm_num)
theorem B1832125 : Blo 1628513 1832125 := bbase (se 3 (by rfl) ⟨343523, by rfl⟩ : syracuseStep 1832125 = 687047) (by norm_num)
theorem B3093709 : Blo 1628513 3093709 := bbase (se 3 (by rfl) ⟨580070, by rfl⟩ : syracuseStep 3093709 = 1160141) (by norm_num)
theorem B3667157 : Blo 1628513 3667157 := bbase (se 7 (by rfl) ⟨42974, by rfl⟩ : syracuseStep 3667157 = 85949) (by norm_num)
theorem B4125917 : Blo 1628513 4125917 := bbase (se 3 (by rfl) ⟨773609, by rfl⟩ : syracuseStep 4125917 = 1547219) (by norm_num)
theorem B1832161 : Blo 1628513 1832161 := bbase (se 2 (by rfl) ⟨687060, by rfl⟩ : syracuseStep 1832161 = 1374121) (by norm_num)
theorem B2061541 : Blo 1628513 2061541 := bbase (se 4 (by rfl) ⟨193269, by rfl⟩ : syracuseStep 2061541 = 386539) (by norm_num)
theorem B2749693 : Blo 1628513 2749693 := bbase (se 3 (by rfl) ⟨515567, by rfl⟩ : syracuseStep 2749693 = 1031135) (by norm_num)
theorem B1832197 : Blo 1628513 1832197 := bbase (se 4 (by rfl) ⟨171768, by rfl⟩ : syracuseStep 1832197 = 343537) (by norm_num)
theorem B3667229 : Blo 1628513 3667229 := bbase (se 3 (by rfl) ⟨687605, by rfl⟩ : syracuseStep 3667229 = 1375211) (by norm_num)
theorem B1832233 : Blo 1628513 1832233 := bbase (se 2 (by rfl) ⟨687087, by rfl⟩ : syracuseStep 1832233 = 1374175) (by norm_num)
theorem B6960437 : Blo 1628513 6960437 := bbase (se 5 (by rfl) ⟨326270, by rfl⟩ : syracuseStep 6960437 = 652541) (by norm_num)
theorem B1832269 : Blo 1628513 1832269 := bbase (se 3 (by rfl) ⟨343550, by rfl⟩ : syracuseStep 1832269 = 687101) (by norm_num)
theorem B2749781 : Blo 1628513 2749781 := bbase (se 13 (by rfl) ⟨503, by rfl⟩ : syracuseStep 2749781 = 1007) (by norm_num)
theorem B3667301 : Blo 1628513 3667301 := bbase (se 4 (by rfl) ⟨343809, by rfl⟩ : syracuseStep 3667301 = 687619) (by norm_num)
theorem B3093869 : Blo 1628513 3093869 := bbase (se 3 (by rfl) ⟨580100, by rfl⟩ : syracuseStep 3093869 = 1160201) (by norm_num)
theorem B1832305 : Blo 1628513 1832305 := bbase (se 2 (by rfl) ⟨687114, by rfl⟩ : syracuseStep 1832305 = 1374229) (by norm_num)
theorem B4642181 : Blo 1628513 4642181 := bbase (se 4 (by rfl) ⟨435204, by rfl⟩ : syracuseStep 4642181 = 870409) (by norm_num)
theorem B2061713 : Blo 1628513 2061713 := bbase (se 2 (by rfl) ⟨773142, by rfl⟩ : syracuseStep 2061713 = 1546285) (by norm_num)
theorem B1832341 : Blo 1628513 1832341 := bbase (se 6 (by rfl) ⟨42945, by rfl⟩ : syracuseStep 1832341 = 85891) (by norm_num)
theorem B3667373 : Blo 1628513 3667373 := bbase (se 3 (by rfl) ⟨687632, by rfl⟩ : syracuseStep 3667373 = 1375265) (by norm_num)
theorem B1832377 : Blo 1628513 1832377 := bbase (se 2 (by rfl) ⟨687141, by rfl⟩ : syracuseStep 1832377 = 1374283) (by norm_num)
theorem B2061769 : Blo 1628513 2061769 := bbase (se 2 (by rfl) ⟨773163, by rfl⟩ : syracuseStep 2061769 = 1546327) (by norm_num)
theorem B2749909 : Blo 1628513 2749909 := bbase (se 7 (by rfl) ⟨32225, by rfl⟩ : syracuseStep 2749909 = 64451) (by norm_num)
theorem B1832413 : Blo 1628513 1832413 := bbase (se 3 (by rfl) ⟨343577, by rfl⟩ : syracuseStep 1832413 = 687155) (by norm_num)
theorem B5502437 : Blo 1628513 5502437 := bbase (se 4 (by rfl) ⟨515853, by rfl⟩ : syracuseStep 5502437 = 1031707) (by norm_num)
theorem B3667445 : Blo 1628513 3667445 := bbase (se 5 (by rfl) ⟨171911, by rfl⟩ : syracuseStep 3667445 = 343823) (by norm_num)
theorem B3094013 : Blo 1628513 3094013 := bbase (se 3 (by rfl) ⟨580127, by rfl⟩ : syracuseStep 3094013 = 1160255) (by norm_num)
theorem B1832449 : Blo 1628513 1832449 := bbase (se 2 (by rfl) ⟨687168, by rfl⟩ : syracuseStep 1832449 = 1374337) (by norm_num)
theorem B1832485 : Blo 1628513 1832485 := bbase (se 4 (by rfl) ⟨171795, by rfl⟩ : syracuseStep 1832485 = 343591) (by norm_num)
theorem B2061865 : Blo 1628513 2061865 := bbase (se 2 (by rfl) ⟨773199, by rfl⟩ : syracuseStep 2061865 = 1546399) (by norm_num)
theorem B2749997 : Blo 1628513 2749997 := bbase (se 3 (by rfl) ⟨515624, by rfl⟩ : syracuseStep 2749997 = 1031249) (by norm_num)
theorem B4126261 : Blo 1628513 4126261 := bbase (se 5 (by rfl) ⟨193418, by rfl⟩ : syracuseStep 4126261 = 386837) (by norm_num)
theorem B3667517 : Blo 1628513 3667517 := bbase (se 3 (by rfl) ⟨687659, by rfl⟩ : syracuseStep 3667517 = 1375319) (by norm_num)
theorem B1832521 : Blo 1628513 1832521 := bbase (se 2 (by rfl) ⟨687195, by rfl⟩ : syracuseStep 1832521 = 1374391) (by norm_num)
theorem B3479125 : Blo 1628513 3479125 := bbase (se 8 (by rfl) ⟨20385, by rfl⟩ : syracuseStep 3479125 = 40771) (by norm_num)
theorem B1832557 : Blo 1628513 1832557 := bbase (se 3 (by rfl) ⟨343604, by rfl⟩ : syracuseStep 1832557 = 687209) (by norm_num)
theorem B3667589 : Blo 1628513 3667589 := bbase (se 4 (by rfl) ⟨343836, by rfl⟩ : syracuseStep 3667589 = 687673) (by norm_num)
theorem B1832593 : Blo 1628513 1832593 := bbase (se 2 (by rfl) ⟨687222, by rfl⟩ : syracuseStep 1832593 = 1374445) (by norm_num)
theorem B8246933 : Blo 1628513 8246933 := bbase (se 6 (by rfl) ⟨193287, by rfl⟩ : syracuseStep 8246933 = 386575) (by norm_num)
theorem B4126373 : Blo 1628513 4126373 := bbase (se 4 (by rfl) ⟨386847, by rfl⟩ : syracuseStep 4126373 = 773695) (by norm_num)
theorem B2750125 : Blo 1628513 2750125 := bbase (se 3 (by rfl) ⟨515648, by rfl⟩ : syracuseStep 2750125 = 1031297) (by norm_num)
theorem B1832629 : Blo 1628513 1832629 := bbase (se 5 (by rfl) ⟨85904, by rfl⟩ : syracuseStep 1832629 = 171809) (by norm_num)
theorem B6190789 : Blo 1628513 6190789 := bbase (se 4 (by rfl) ⟨580386, by rfl⟩ : syracuseStep 6190789 = 1160773) (by norm_num)
theorem B3667661 : Blo 1628513 3667661 := bbase (se 3 (by rfl) ⟨687686, by rfl⟩ : syracuseStep 3667661 = 1375373) (by norm_num)
theorem B2062037 : Blo 1628513 2062037 := bbase (se 7 (by rfl) ⟨24164, by rfl⟩ : syracuseStep 2062037 = 48329) (by norm_num)
theorem B1832665 : Blo 1628513 1832665 := bbase (se 2 (by rfl) ⟨687249, by rfl⟩ : syracuseStep 1832665 = 1374499) (by norm_num)
theorem B1832701 : Blo 1628513 1832701 := bbase (se 3 (by rfl) ⟨343631, by rfl⟩ : syracuseStep 1832701 = 687263) (by norm_num)
theorem B2750213 : Blo 1628513 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B2062093 : Blo 1628513 2062093 := bbase (se 3 (by rfl) ⟨386642, by rfl⟩ : syracuseStep 2062093 = 773285) (by norm_num)
theorem B3667733 : Blo 1628513 3667733 := bbase (se 6 (by rfl) ⟨85962, by rfl⟩ : syracuseStep 3667733 = 171925) (by norm_num)
theorem B25098005 : Blo 1628513 25098005 := bbase (se 6 (by rfl) ⟨588234, by rfl⟩ : syracuseStep 25098005 = 1176469) (by norm_num)
theorem B3094301 : Blo 1628513 3094301 := bbase (se 3 (by rfl) ⟨580181, by rfl⟩ : syracuseStep 3094301 = 1160363) (by norm_num)
theorem B1832737 : Blo 1628513 1832737 := bbase (se 2 (by rfl) ⟨687276, by rfl⟩ : syracuseStep 1832737 = 1374553) (by norm_num)
theorem B1832773 : Blo 1628513 1832773 := bbase (se 4 (by rfl) ⟨171822, by rfl⟩ : syracuseStep 1832773 = 343645) (by norm_num)
theorem B3667805 : Blo 1628513 3667805 := bbase (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) (by norm_num)
theorem B4126565 : Blo 1628513 4126565 := bbase (se 4 (by rfl) ⟨386865, by rfl⟩ : syracuseStep 4126565 = 773731) (by norm_num)
theorem B1832809 : Blo 1628513 1832809 := bbase (se 2 (by rfl) ⟨687303, by rfl⟩ : syracuseStep 1832809 = 1374607) (by norm_num)
theorem B2062189 : Blo 1628513 2062189 := bbase (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) (by norm_num)
theorem B1652609 : Blo 1628513 1652609 := bbase (se 2 (by rfl) ⟨619728, by rfl⟩ : syracuseStep 1652609 = 1239457) (by norm_num)
theorem B2750341 : Blo 1628513 2750341 := bbase (se 4 (by rfl) ⟨257844, by rfl⟩ : syracuseStep 2750341 = 515689) (by norm_num)
theorem B1832845 : Blo 1628513 1832845 := bbase (se 3 (by rfl) ⟨343658, by rfl⟩ : syracuseStep 1832845 = 687317) (by norm_num)
theorem B5502869 : Blo 1628513 5502869 := bbase (se 6 (by rfl) ⟨128973, by rfl⟩ : syracuseStep 5502869 = 257947) (by norm_num)
theorem B3667877 : Blo 1628513 3667877 := bbase (se 4 (by rfl) ⟨343863, by rfl⟩ : syracuseStep 3667877 = 687727) (by norm_num)
theorem B1832881 : Blo 1628513 1832881 := bbase (se 2 (by rfl) ⟨687330, by rfl⟩ : syracuseStep 1832881 = 1374661) (by norm_num)
theorem B12375989 : Blo 1628513 12375989 := bbase (se 5 (by rfl) ⟨580124, by rfl⟩ : syracuseStep 12375989 = 1160249) (by norm_num)
theorem B3094453 : Blo 1628513 3094453 := bbase (se 5 (by rfl) ⟨145052, by rfl⟩ : syracuseStep 3094453 = 290105) (by norm_num)
theorem B1832917 : Blo 1628513 1832917 := bbase (se 7 (by rfl) ⟨21479, by rfl⟩ : syracuseStep 1832917 = 42959) (by norm_num)
theorem B7436245 : Blo 1628513 7436245 := bbase (se 7 (by rfl) ⟨87143, by rfl⟩ : syracuseStep 7436245 = 174287) (by norm_num)
theorem B2750429 : Blo 1628513 2750429 := bbase (se 3 (by rfl) ⟨515705, by rfl⟩ : syracuseStep 2750429 = 1031411) (by norm_num)
theorem B3667949 : Blo 1628513 3667949 := bbase (se 3 (by rfl) ⟨687740, by rfl⟩ : syracuseStep 3667949 = 1375481) (by norm_num)
theorem B1832953 : Blo 1628513 1832953 := bbase (se 2 (by rfl) ⟨687357, by rfl⟩ : syracuseStep 1832953 = 1374715) (by norm_num)
theorem B2062361 : Blo 1628513 2062361 := bbase (se 2 (by rfl) ⟨773385, by rfl⟩ : syracuseStep 2062361 = 1546771) (by norm_num)
theorem B1832989 : Blo 1628513 1832989 := bbase (se 3 (by rfl) ⟨343685, by rfl⟩ : syracuseStep 1832989 = 687371) (by norm_num)
theorem B2611253 : Blo 1628513 2611253 := bbase (se 5 (by rfl) ⟨122402, by rfl⟩ : syracuseStep 2611253 = 244805) (by norm_num)
theorem B3668021 : Blo 1628513 3668021 := bbase (se 5 (by rfl) ⟨171938, by rfl⟩ : syracuseStep 3668021 = 343877) (by norm_num)
theorem B1833025 : Blo 1628513 1833025 := bbase (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) (by norm_num)
theorem B2062417 : Blo 1628513 2062417 := bbase (se 2 (by rfl) ⟨773406, by rfl⟩ : syracuseStep 2062417 = 1546813) (by norm_num)
theorem B2750557 : Blo 1628513 2750557 := bbase (se 3 (by rfl) ⟨515729, by rfl⟩ : syracuseStep 2750557 = 1031459) (by norm_num)
theorem B1833061 : Blo 1628513 1833061 := bbase (se 4 (by rfl) ⟨171849, by rfl⟩ : syracuseStep 1833061 = 343699) (by norm_num)
theorem B4642933 : Blo 1628513 4642933 := bbase (se 5 (by rfl) ⟨217637, by rfl⟩ : syracuseStep 4642933 = 435275) (by norm_num)
theorem B3668093 : Blo 1628513 3668093 := bbase (se 3 (by rfl) ⟨687767, by rfl⟩ : syracuseStep 3668093 = 1375535) (by norm_num)
theorem B1833097 : Blo 1628513 1833097 := bbase (se 2 (by rfl) ⟨687411, by rfl⟩ : syracuseStep 1833097 = 1374823) (by norm_num)
theorem B1833133 : Blo 1628513 1833133 := bbase (se 3 (by rfl) ⟨343712, by rfl⟩ : syracuseStep 1833133 = 687425) (by norm_num)
theorem B2062513 : Blo 1628513 2062513 := bbase (se 2 (by rfl) ⟨773442, by rfl⟩ : syracuseStep 2062513 = 1546885) (by norm_num)
theorem B2750645 : Blo 1628513 2750645 := bbase (se 5 (by rfl) ⟨128936, by rfl⟩ : syracuseStep 2750645 = 257873) (by norm_num)
theorem B2611381 : Blo 1628513 2611381 := bbase (se 5 (by rfl) ⟨122408, by rfl⟩ : syracuseStep 2611381 = 244817) (by norm_num)
theorem B4126909 : Blo 1628513 4126909 := bbase (se 3 (by rfl) ⟨773795, by rfl⟩ : syracuseStep 4126909 = 1547591) (by norm_num)
theorem B3668165 : Blo 1628513 3668165 := bbase (se 4 (by rfl) ⟨343890, by rfl⟩ : syracuseStep 3668165 = 687781) (by norm_num)
theorem B1833169 : Blo 1628513 1833169 := bbase (se 2 (by rfl) ⟨687438, by rfl⟩ : syracuseStep 1833169 = 1374877) (by norm_num)
theorem B3094757 : Blo 1628513 3094757 := bbase (se 4 (by rfl) ⟨290133, by rfl⟩ : syracuseStep 3094757 = 580267) (by norm_num)
theorem B1833205 : Blo 1628513 1833205 := bbase (se 5 (by rfl) ⟨85931, by rfl⟩ : syracuseStep 1833205 = 171863) (by norm_num)
theorem B2611445 : Blo 1628513 2611445 := bbase (se 5 (by rfl) ⟨122411, by rfl⟩ : syracuseStep 2611445 = 244823) (by norm_num)
theorem B2201861 : Blo 1628513 2201861 := bbase (se 4 (by rfl) ⟨206424, by rfl⟩ : syracuseStep 2201861 = 412849) (by norm_num)
theorem B3668237 : Blo 1628513 3668237 := bbase (se 3 (by rfl) ⟨687794, by rfl⟩ : syracuseStep 3668237 = 1375589) (by norm_num)
theorem B1833241 : Blo 1628513 1833241 := bbase (se 2 (by rfl) ⟨687465, by rfl⟩ : syracuseStep 1833241 = 1374931) (by norm_num)
theorem B4127021 : Blo 1628513 4127021 := bbase (se 3 (by rfl) ⟨773816, by rfl⟩ : syracuseStep 4127021 = 1547633) (by norm_num)
theorem B2750773 : Blo 1628513 2750773 := bbase (se 5 (by rfl) ⟨128942, by rfl⟩ : syracuseStep 2750773 = 257885) (by norm_num)
theorem B11155765 : Blo 1628513 11155765 := bbase (se 5 (by rfl) ⟨522926, by rfl⟩ : syracuseStep 11155765 = 1045853) (by norm_num)
theorem B1833277 : Blo 1628513 1833277 := bbase (se 3 (by rfl) ⟨343739, by rfl⟩ : syracuseStep 1833277 = 687479) (by norm_num)
theorem B12368213 : Blo 1628513 12368213 := bbase (se 10 (by rfl) ⟨18117, by rfl⟩ : syracuseStep 12368213 = 36235) (by norm_num)
theorem B3668309 : Blo 1628513 3668309 := bbase (se 10 (by rfl) ⟨5373, by rfl⟩ : syracuseStep 3668309 = 10747) (by norm_num)
theorem B2062685 : Blo 1628513 2062685 := bbase (se 3 (by rfl) ⟨386753, by rfl⟩ : syracuseStep 2062685 = 773507) (by norm_num)
theorem B1833313 : Blo 1628513 1833313 := bbase (se 2 (by rfl) ⟨687492, by rfl⟩ : syracuseStep 1833313 = 1374985) (by norm_num)
theorem B1833349 : Blo 1628513 1833349 := bbase (se 4 (by rfl) ⟨171876, by rfl⟩ : syracuseStep 1833349 = 343753) (by norm_num)
theorem B2750861 : Blo 1628513 2750861 := bbase (se 3 (by rfl) ⟨515786, by rfl⟩ : syracuseStep 2750861 = 1031573) (by norm_num)
theorem B6183317 : Blo 1628513 6183317 := bbase (se 6 (by rfl) ⟨144921, by rfl⟩ : syracuseStep 6183317 = 289843) (by norm_num)
theorem B2062741 : Blo 1628513 2062741 := bbase (se 6 (by rfl) ⟨48345, by rfl⟩ : syracuseStep 2062741 = 96691) (by norm_num)
theorem B3668381 : Blo 1628513 3668381 := bbase (se 3 (by rfl) ⟨687821, by rfl⟩ : syracuseStep 3668381 = 1375643) (by norm_num)
theorem B1833385 : Blo 1628513 1833385 := bbase (se 2 (by rfl) ⟨687519, by rfl⟩ : syracuseStep 1833385 = 1375039) (by norm_num)
theorem B3480013 : Blo 1628513 3480013 := bbase (se 3 (by rfl) ⟨652502, by rfl⟩ : syracuseStep 3480013 = 1305005) (by norm_num)
theorem B1833421 : Blo 1628513 1833421 := bbase (se 3 (by rfl) ⟨343766, by rfl⟩ : syracuseStep 1833421 = 687533) (by norm_num)
theorem B3668453 : Blo 1628513 3668453 := bbase (se 4 (by rfl) ⟨343917, by rfl⟩ : syracuseStep 3668453 = 687835) (by norm_num)
theorem B4127213 : Blo 1628513 4127213 := bbase (se 3 (by rfl) ⟨773852, by rfl⟩ : syracuseStep 4127213 = 1547705) (by norm_num)
theorem B1833457 : Blo 1628513 1833457 := bbase (se 2 (by rfl) ⟨687546, by rfl⟩ : syracuseStep 1833457 = 1375093) (by norm_num)
theorem B2062837 : Blo 1628513 2062837 := bbase (se 5 (by rfl) ⟨96695, by rfl⟩ : syracuseStep 2062837 = 193391) (by norm_num)
theorem B2750989 : Blo 1628513 2750989 := bbase (se 3 (by rfl) ⟨515810, by rfl⟩ : syracuseStep 2750989 = 1031621) (by norm_num)
theorem B1833493 : Blo 1628513 1833493 := bbase (se 6 (by rfl) ⟨42972, by rfl⟩ : syracuseStep 1833493 = 85945) (by norm_num)
theorem B3668525 : Blo 1628513 3668525 := bbase (se 3 (by rfl) ⟨687848, by rfl⟩ : syracuseStep 3668525 = 1375697) (by norm_num)
theorem B1833529 : Blo 1628513 1833529 := bbase (se 2 (by rfl) ⟨687573, by rfl⟩ : syracuseStep 1833529 = 1375147) (by norm_num)
theorem B1833565 : Blo 1628513 1833565 := bbase (se 3 (by rfl) ⟨343793, by rfl⟩ : syracuseStep 1833565 = 687587) (by norm_num)
theorem B2751077 : Blo 1628513 2751077 := bbase (se 4 (by rfl) ⟨257913, by rfl⟩ : syracuseStep 2751077 = 515827) (by norm_num)
theorem B3668597 : Blo 1628513 3668597 := bbase (se 5 (by rfl) ⟨171965, by rfl⟩ : syracuseStep 3668597 = 343931) (by norm_num)
theorem B1833601 : Blo 1628513 1833601 := bbase (se 2 (by rfl) ⟨687600, by rfl⟩ : syracuseStep 1833601 = 1375201) (by norm_num)
theorem B3914381 : Blo 1628513 3914381 := bbase (se 3 (by rfl) ⟨733946, by rfl⟩ : syracuseStep 3914381 = 1467893) (by norm_num)
theorem B2063009 : Blo 1628513 2063009 := bbase (se 2 (by rfl) ⟨773628, by rfl⟩ : syracuseStep 2063009 = 1547257) (by norm_num)
theorem B1833637 : Blo 1628513 1833637 := bbase (se 4 (by rfl) ⟨171903, by rfl⟩ : syracuseStep 1833637 = 343807) (by norm_num)
theorem B7051973 : Blo 1628513 7051973 := bbase (se 4 (by rfl) ⟨661122, by rfl⟩ : syracuseStep 7051973 = 1322245) (by norm_num)
theorem B1833673 : Blo 1628513 1833673 := bbase (se 2 (by rfl) ⟨687627, by rfl⟩ : syracuseStep 1833673 = 1375255) (by norm_num)
theorem B2063065 : Blo 1628513 2063065 := bbase (se 2 (by rfl) ⟨773649, by rfl⟩ : syracuseStep 2063065 = 1547299) (by norm_num)
theorem B2751205 : Blo 1628513 2751205 := bbase (se 4 (by rfl) ⟨257925, by rfl⟩ : syracuseStep 2751205 = 515851) (by norm_num)
theorem B1833709 : Blo 1628513 1833709 := bbase (se 3 (by rfl) ⟨343820, by rfl⟩ : syracuseStep 1833709 = 687641) (by norm_num)
theorem B1858313 : Blo 1628513 1858313 := bbase (se 2 (by rfl) ⟨696867, by rfl⟩ : syracuseStep 1858313 = 1393735) (by norm_num)
theorem B1833745 : Blo 1628513 1833745 := bbase (se 2 (by rfl) ⟨687654, by rfl⟩ : syracuseStep 1833745 = 1375309) (by norm_num)
theorem B3914525 : Blo 1628513 3914525 := bbase (se 3 (by rfl) ⟨733973, by rfl⟩ : syracuseStep 3914525 = 1467947) (by norm_num)
theorem B1833781 : Blo 1628513 1833781 := bbase (se 5 (by rfl) ⟨85958, by rfl⟩ : syracuseStep 1833781 = 171917) (by norm_num)
theorem B2063161 : Blo 1628513 2063161 := bbase (se 2 (by rfl) ⟨773685, by rfl⟩ : syracuseStep 2063161 = 1547371) (by norm_num)
theorem B2751293 : Blo 1628513 2751293 := bbase (se 3 (by rfl) ⟨515867, by rfl⟩ : syracuseStep 2751293 = 1031735) (by norm_num)
theorem B1833817 : Blo 1628513 1833817 := bbase (se 2 (by rfl) ⟨687681, by rfl⟩ : syracuseStep 1833817 = 1375363) (by norm_num)
theorem B1858405 : Blo 1628513 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B1833853 : Blo 1628513 1833853 := bbase (se 3 (by rfl) ⟨343847, by rfl⟩ : syracuseStep 1833853 = 687695) (by norm_num)
theorem B5651333 : Blo 1628513 5651333 := bbase (se 4 (by rfl) ⟨529812, by rfl⟩ : syracuseStep 5651333 = 1059625) (by norm_num)
theorem B1833889 : Blo 1628513 1833889 := bbase (se 2 (by rfl) ⟨687708, by rfl⟩ : syracuseStep 1833889 = 1375417) (by norm_num)
theorem B8248229 : Blo 1628513 8248229 := bbase (se 4 (by rfl) ⟨773271, by rfl⟩ : syracuseStep 8248229 = 1546543) (by norm_num)
theorem B3480509 : Blo 1628513 3480509 := bbase (se 3 (by rfl) ⟨652595, by rfl⟩ : syracuseStep 3480509 = 1305191) (by norm_num)
theorem B2751421 : Blo 1628513 2751421 := bbase (se 3 (by rfl) ⟨515891, by rfl⟩ : syracuseStep 2751421 = 1031783) (by norm_num)
theorem B1833925 : Blo 1628513 1833925 := bbase (se 4 (by rfl) ⟨171930, by rfl⟩ : syracuseStep 1833925 = 343861) (by norm_num)
theorem B2063333 : Blo 1628513 2063333 := bbase (se 4 (by rfl) ⟨193437, by rfl⟩ : syracuseStep 2063333 = 386875) (by norm_num)
theorem B1833961 : Blo 1628513 1833961 := bbase (se 2 (by rfl) ⟨687735, by rfl⟩ : syracuseStep 1833961 = 1375471) (by norm_num)
theorem B1833997 : Blo 1628513 1833997 := bbase (se 3 (by rfl) ⟨343874, by rfl⟩ : syracuseStep 1833997 = 687749) (by norm_num)
theorem B2063389 : Blo 1628513 2063389 := bbase (se 3 (by rfl) ⟨386885, by rfl⟩ : syracuseStep 2063389 = 773771) (by norm_num)
theorem B5217317 : Blo 1628513 5217317 := bbase (se 4 (by rfl) ⟨489123, by rfl⟩ : syracuseStep 5217317 = 978247) (by norm_num)
theorem B6962213 : Blo 1628513 6962213 := bbase (se 4 (by rfl) ⟨652707, by rfl⟩ : syracuseStep 6962213 = 1305415) (by norm_num)
theorem B1834033 : Blo 1628513 1834033 := bbase (se 2 (by rfl) ⟨687762, by rfl⟩ : syracuseStep 1834033 = 1375525) (by norm_num)
theorem B1956917 : Blo 1628513 1956917 := bbase (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) (by norm_num)
theorem B1834069 : Blo 1628513 1834069 := bbase (se 8 (by rfl) ⟨10746, by rfl⟩ : syracuseStep 1834069 = 21493) (by norm_num)
theorem B1834105 : Blo 1628513 1834105 := bbase (se 2 (by rfl) ⟨687789, by rfl⟩ : syracuseStep 1834105 = 1375579) (by norm_num)
theorem B2063485 : Blo 1628513 2063485 := bbase (se 3 (by rfl) ⟨386903, by rfl⟩ : syracuseStep 2063485 = 773807) (by norm_num)
theorem B1834141 : Blo 1628513 1834141 := bbase (se 3 (by rfl) ⟨343901, by rfl⟩ : syracuseStep 1834141 = 687803) (by norm_num)
theorem B1834177 : Blo 1628513 1834177 := bbase (se 2 (by rfl) ⟨687816, by rfl⟩ : syracuseStep 1834177 = 1375633) (by norm_num)
theorem B1834213 : Blo 1628513 1834213 := bbase (se 4 (by rfl) ⟨171957, by rfl⟩ : syracuseStep 1834213 = 343915) (by norm_num)
theorem B1834249 : Blo 1628513 1834249 := bbase (se 2 (by rfl) ⟨687843, by rfl⟩ : syracuseStep 1834249 = 1375687) (by norm_num)
theorem B3136781 : Blo 1628513 3136781 := bbase (se 3 (by rfl) ⟨588146, by rfl⟩ : syracuseStep 3136781 = 1176293) (by norm_num)
theorem B1834285 : Blo 1628513 1834285 := bbase (se 3 (by rfl) ⟨343928, by rfl⟩ : syracuseStep 1834285 = 687857) (by norm_num)
theorem B2415925 : Blo 1628513 2415925 := bbase (se 5 (by rfl) ⟨113246, by rfl⟩ : syracuseStep 2415925 = 226493) (by norm_num)
theorem B1858897 : Blo 1628513 1858897 := bbase (se 2 (by rfl) ⟨697086, by rfl⟩ : syracuseStep 1858897 = 1394173) (by norm_num)
theorem B17612117 : Blo 1628513 17612117 := bbase (se 11 (by rfl) ⟨12899, by rfl⟩ : syracuseStep 17612117 = 25799) (by norm_num)
theorem B1834321 : Blo 1628513 1834321 := bbase (se 2 (by rfl) ⟨687870, by rfl⟩ : syracuseStep 1834321 = 1375741) (by norm_num)
theorem B1957225 : Blo 1628513 1957225 := bbase (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) (by norm_num)
theorem B1858933 : Blo 1628513 1858933 := bbase (se 5 (by rfl) ⟨87137, by rfl⟩ : syracuseStep 1858933 = 174275) (by norm_num)
theorem B5291477 : Blo 1628513 5291477 := bbase (se 7 (by rfl) ⟨62009, by rfl⟩ : syracuseStep 5291477 = 124019) (by norm_num)
theorem B3137069 : Blo 1628513 3137069 := bbase (se 3 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 3137069 = 1176401) (by norm_num)
theorem B5496389 : Blo 1628513 5496389 := bbase (se 4 (by rfl) ⟨515286, by rfl⟩ : syracuseStep 5496389 = 1030573) (by norm_num)
theorem B1957613 : Blo 1628513 1957613 := bbase (se 3 (by rfl) ⟨367052, by rfl⟩ : syracuseStep 1957613 = 734105) (by norm_num)
theorem B6610709 : Blo 1628513 6610709 := bbase (se 6 (by rfl) ⟨154938, by rfl⟩ : syracuseStep 6610709 = 309877) (by norm_num)
theorem B3481397 : Blo 1628513 3481397 := bbase (se 5 (by rfl) ⟨163190, by rfl⟩ : syracuseStep 3481397 = 326381) (by norm_num)
theorem B3137381 : Blo 1628513 3137381 := bbase (se 4 (by rfl) ⟨294129, by rfl⟩ : syracuseStep 3137381 = 588259) (by norm_num)
theorem B10436501 : Blo 1628513 10436501 := bbase (se 6 (by rfl) ⟨244605, by rfl⟩ : syracuseStep 10436501 = 489211) (by norm_num)
theorem B2383781 : Blo 1628513 2383781 := bbase (se 4 (by rfl) ⟨223479, by rfl⟩ : syracuseStep 2383781 = 446959) (by norm_num)
theorem B3481517 : Blo 1628513 3481517 := bbase (se 3 (by rfl) ⟨652784, by rfl⟩ : syracuseStep 3481517 = 1305569) (by norm_num)
theorem B5496821 : Blo 1628513 5496821 := bbase (se 5 (by rfl) ⟨257663, by rfl⟩ : syracuseStep 5496821 = 515327) (by norm_num)
theorem B1630211 : Blo 1628513 1630211 := bstep (se 1 (by rfl) ⟨1222658, by rfl⟩ : syracuseStep 1630211 = 2445317) B2445317
theorem B1630227 : Blo 1628513 1630227 := bstep (se 1 (by rfl) ⟨1222670, by rfl⟩ : syracuseStep 1630227 = 2445341) B2445341
theorem B1630243 : Blo 1628513 1630243 := bstep (se 1 (by rfl) ⟨1222682, by rfl⟩ : syracuseStep 1630243 = 2445365) B2445365
theorem B1630259 : Blo 1628513 1630259 := bstep (se 1 (by rfl) ⟨1222694, by rfl⟩ : syracuseStep 1630259 = 2445389) B2445389
theorem B1630275 : Blo 1628513 1630275 := bstep (se 1 (by rfl) ⟨1222706, by rfl⟩ : syracuseStep 1630275 = 2445413) B2445413
theorem B1630291 : Blo 1628513 1630291 := bstep (se 1 (by rfl) ⟨1222718, by rfl⟩ : syracuseStep 1630291 = 2445437) B2445437
theorem B1630307 : Blo 1628513 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B1630323 : Blo 1628513 1630323 := bstep (se 1 (by rfl) ⟨1222742, by rfl⟩ : syracuseStep 1630323 = 2445485) B2445485
theorem B1630339 : Blo 1628513 1630339 := bstep (se 1 (by rfl) ⟨1222754, by rfl⟩ : syracuseStep 1630339 = 2445509) B2445509
theorem B5218445 : Blo 1628513 5218445 := bstep (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) B1956917
theorem B1630355 : Blo 1628513 1630355 := bstep (se 1 (by rfl) ⟨1222766, by rfl⟩ : syracuseStep 1630355 = 2445533) B2445533
theorem B1630371 : Blo 1628513 1630371 := bstep (se 1 (by rfl) ⟨1222778, by rfl⟩ : syracuseStep 1630371 = 2445557) B2445557
theorem B1630387 : Blo 1628513 1630387 := bstep (se 1 (by rfl) ⟨1222790, by rfl⟩ : syracuseStep 1630387 = 2445581) B2445581
theorem B1630403 : Blo 1628513 1630403 := bstep (se 1 (by rfl) ⟨1222802, by rfl⟩ : syracuseStep 1630403 = 2445605) B2445605
theorem B6602957 : Blo 1628513 6602957 := bstep (se 3 (by rfl) ⟨1238054, by rfl⟩ : syracuseStep 6602957 = 2476109) B2476109
theorem B5497037 : Blo 1628513 5497037 := bstep (se 3 (by rfl) ⟨1030694, by rfl⟩ : syracuseStep 5497037 = 2061389) B2061389
theorem B1630419 : Blo 1628513 1630419 := bstep (se 1 (by rfl) ⟨1222814, by rfl⟩ : syracuseStep 1630419 = 2445629) B2445629
theorem B15655139 : Blo 1628513 15655139 := bstep (se 1 (by rfl) ⟨11741354, by rfl⟩ : syracuseStep 15655139 = 23482709) B23482709
theorem B1630435 : Blo 1628513 1630435 := bstep (se 1 (by rfl) ⟨1222826, by rfl⟩ : syracuseStep 1630435 = 2445653) B2445653
theorem B3481841 : Blo 1628513 3481841 := bstep (se 2 (by rfl) ⟨1305690, by rfl⟩ : syracuseStep 3481841 = 2611381) B2611381
theorem B1630451 : Blo 1628513 1630451 := bstep (se 1 (by rfl) ⟨1222838, by rfl⟩ : syracuseStep 1630451 = 2445677) B2445677
theorem B5497091 : Blo 1628513 5497091 := bstep (se 1 (by rfl) ⟨4122818, by rfl⟩ : syracuseStep 5497091 = 8245637) B8245637
theorem B3481859 : Blo 1628513 3481859 := bstep (se 1 (by rfl) ⟨2611394, by rfl⟩ : syracuseStep 3481859 = 5222789) B5222789
theorem B1630467 : Blo 1628513 1630467 := bstep (se 1 (by rfl) ⟨1222850, by rfl⟩ : syracuseStep 1630467 = 2445701) B2445701
theorem B1630483 : Blo 1628513 1630483 := bstep (se 1 (by rfl) ⟨1222862, by rfl⟩ : syracuseStep 1630483 = 2445725) B2445725
theorem B1630499 : Blo 1628513 1630499 := bstep (se 1 (by rfl) ⟨1222874, by rfl⟩ : syracuseStep 1630499 = 2445749) B2445749
theorem B14868805 : Blo 1628513 14868805 := bstep (se 4 (by rfl) ⟨1393950, by rfl⟩ : syracuseStep 14868805 = 2787901) B2787901
theorem B6185443 : Blo 1628513 6185443 := bstep (se 1 (by rfl) ⟨4639082, by rfl⟩ : syracuseStep 6185443 = 9278165) B9278165
theorem B5497361 : Blo 1628513 5497361 := bstep (se 2 (by rfl) ⟨2061510, by rfl⟩ : syracuseStep 5497361 = 4123021) B4123021
theorem B2318881 : Blo 1628513 2318881 := bstep (se 2 (by rfl) ⟨869580, by rfl⟩ : syracuseStep 2318881 = 1739161) B1739161
theorem B10584611 : Blo 1628513 10584611 := bstep (se 1 (by rfl) ⟨7938458, by rfl⟩ : syracuseStep 10584611 = 15876917) B15876917
theorem B2318915 : Blo 1628513 2318915 := bstep (se 1 (by rfl) ⟨1739186, by rfl⟩ : syracuseStep 2318915 = 3478373) B3478373
theorem B6963853 : Blo 1628513 6963853 := bstep (se 3 (by rfl) ⟨1305722, by rfl⟩ : syracuseStep 6963853 = 2611445) B2611445
theorem B18572003 : Blo 1628513 18572003 := bstep (se 1 (by rfl) ⟨13929002, by rfl⟩ : syracuseStep 18572003 = 27858005) B27858005
theorem B11150093 : Blo 1628513 11150093 := bstep (se 3 (by rfl) ⟨2090642, by rfl⟩ : syracuseStep 11150093 = 4181285) B4181285
theorem B21168965 : Blo 1628513 21168965 := bstep (se 4 (by rfl) ⟨1984590, by rfl⟩ : syracuseStep 21168965 = 3969181) B3969181
theorem B2261953 : Blo 1628513 2261953 := bstep (se 2 (by rfl) ⟨848232, by rfl⟩ : syracuseStep 2261953 = 1696465) B1696465
theorem B5497901 : Blo 1628513 5497901 := bstep (se 3 (by rfl) ⟨1030856, by rfl⟩ : syracuseStep 5497901 = 2061713) B2061713
theorem B5497955 : Blo 1628513 5497955 := bstep (se 1 (by rfl) ⟨4123466, by rfl⟩ : syracuseStep 5497955 = 8246933) B8246933
theorem B10437731 : Blo 1628513 10437731 := bstep (se 1 (by rfl) ⟨7828298, by rfl⟩ : syracuseStep 10437731 = 15656597) B15656597
theorem B4588643 : Blo 1628513 4588643 := bstep (se 1 (by rfl) ⟨3441482, by rfl⟩ : syracuseStep 4588643 = 6882965) B6882965
theorem B2319473 : Blo 1628513 2319473 := bstep (se 2 (by rfl) ⟨869802, by rfl⟩ : syracuseStep 2319473 = 1739605) B1739605
theorem B11912305 : Blo 1628513 11912305 := bstep (se 2 (by rfl) ⟨4467114, by rfl⟩ : syracuseStep 11912305 = 8934229) B8934229
theorem B2319553 : Blo 1628513 2319553 := bstep (se 2 (by rfl) ⟨869832, by rfl⟩ : syracuseStep 2319553 = 1739665) B1739665
theorem B8250659 : Blo 1628513 8250659 := bstep (se 1 (by rfl) ⟨6187994, by rfl⟩ : syracuseStep 8250659 = 12375989) B12375989
theorem B13206883 : Blo 1628513 13206883 := bstep (se 1 (by rfl) ⟨9905162, by rfl⟩ : syracuseStep 13206883 = 19810325) B19810325
theorem B5498225 : Blo 1628513 5498225 := bstep (se 2 (by rfl) ⟨2061834, by rfl⟩ : syracuseStep 5498225 = 4123669) B4123669
theorem B56460685 : Blo 1628513 56460685 := bstep (se 3 (by rfl) ⟨10586378, by rfl⟩ : syracuseStep 56460685 = 21172757) B21172757
theorem B8365517 : Blo 1628513 8365517 := bstep (se 3 (by rfl) ⟨1568534, by rfl⟩ : syracuseStep 8365517 = 3137069) B3137069
theorem B4638161 : Blo 1628513 4638161 := bstep (se 2 (by rfl) ⟨1739310, by rfl⟩ : syracuseStep 4638161 = 3478621) B3478621
theorem B2442785 : Blo 1628513 2442785 := bstep (se 2 (by rfl) ⟨916044, by rfl⟩ : syracuseStep 2442785 = 1832089) B1832089
theorem B2442803 : Blo 1628513 2442803 := bstep (se 1 (by rfl) ⟨1832102, by rfl⟩ : syracuseStep 2442803 = 3664205) B3664205
theorem B2442833 : Blo 1628513 2442833 := bstep (se 2 (by rfl) ⟨916062, by rfl⟩ : syracuseStep 2442833 = 1832125) B1832125
theorem B4122211 : Blo 1628513 4122211 := bstep (se 1 (by rfl) ⟨3091658, by rfl⟩ : syracuseStep 4122211 = 6183317) B6183317
theorem B2442851 : Blo 1628513 2442851 := bstep (se 1 (by rfl) ⟨1832138, by rfl⟩ : syracuseStep 2442851 = 3664277) B3664277
theorem B2442881 : Blo 1628513 2442881 := bstep (se 2 (by rfl) ⟨916080, by rfl⟩ : syracuseStep 2442881 = 1832161) B1832161
theorem B2442899 : Blo 1628513 2442899 := bstep (se 1 (by rfl) ⟨1832174, by rfl⟩ : syracuseStep 2442899 = 3664349) B3664349
theorem B2786977 : Blo 1628513 2786977 := bstep (se 2 (by rfl) ⟨1045116, by rfl⟩ : syracuseStep 2786977 = 2090233) B2090233
theorem B2442929 : Blo 1628513 2442929 := bstep (se 2 (by rfl) ⟨916098, by rfl⟩ : syracuseStep 2442929 = 1832197) B1832197
theorem B2442947 : Blo 1628513 2442947 := bstep (se 1 (by rfl) ⟨1832210, by rfl⟩ : syracuseStep 2442947 = 3664421) B3664421
theorem B2442977 : Blo 1628513 2442977 := bstep (se 2 (by rfl) ⟨916116, by rfl⟩ : syracuseStep 2442977 = 1832233) B1832233
theorem B4122353 : Blo 1628513 4122353 := bstep (se 2 (by rfl) ⟨1545882, by rfl⟩ : syracuseStep 4122353 = 3091765) B3091765
theorem B2442995 : Blo 1628513 2442995 := bstep (se 1 (by rfl) ⟨1832246, by rfl⟩ : syracuseStep 2442995 = 3664493) B3664493
theorem B2443025 : Blo 1628513 2443025 := bstep (se 2 (by rfl) ⟨916134, by rfl⟩ : syracuseStep 2443025 = 1832269) B1832269
theorem B2443043 : Blo 1628513 2443043 := bstep (se 1 (by rfl) ⟨1832282, by rfl⟩ : syracuseStep 2443043 = 3664565) B3664565
theorem B2443073 : Blo 1628513 2443073 := bstep (se 2 (by rfl) ⟨916152, by rfl⟩ : syracuseStep 2443073 = 1832305) B1832305
theorem B2443091 : Blo 1628513 2443091 := bstep (se 1 (by rfl) ⟨1832318, by rfl⟩ : syracuseStep 2443091 = 3664637) B3664637
theorem B2787169 : Blo 1628513 2787169 := bstep (se 2 (by rfl) ⟨1045188, by rfl⟩ : syracuseStep 2787169 = 2090377) B2090377
theorem B9275249 : Blo 1628513 9275249 := bstep (se 2 (by rfl) ⟨3478218, by rfl⟩ : syracuseStep 9275249 = 6956437) B6956437
theorem B2443121 : Blo 1628513 2443121 := bstep (se 2 (by rfl) ⟨916170, by rfl⟩ : syracuseStep 2443121 = 1832341) B1832341
theorem B2443139 : Blo 1628513 2443139 := bstep (se 1 (by rfl) ⟨1832354, by rfl⟩ : syracuseStep 2443139 = 3664709) B3664709
theorem B5498765 : Blo 1628513 5498765 := bstep (se 3 (by rfl) ⟨1031018, by rfl⟩ : syracuseStep 5498765 = 2062037) B2062037
theorem B2443169 : Blo 1628513 2443169 := bstep (se 2 (by rfl) ⟨916188, by rfl⟩ : syracuseStep 2443169 = 1832377) B1832377
theorem B2443187 : Blo 1628513 2443187 := bstep (se 1 (by rfl) ⟨1832390, by rfl⟩ : syracuseStep 2443187 = 3664781) B3664781
theorem B5498819 : Blo 1628513 5498819 := bstep (se 1 (by rfl) ⟨4124114, by rfl⟩ : syracuseStep 5498819 = 8248229) B8248229
theorem B9914309 : Blo 1628513 9914309 := bstep (se 4 (by rfl) ⟨929466, by rfl⟩ : syracuseStep 9914309 = 1858933) B1858933
theorem B5220301 : Blo 1628513 5220301 := bstep (se 3 (by rfl) ⟨978806, by rfl⟩ : syracuseStep 5220301 = 1957613) B1957613
theorem B2443217 : Blo 1628513 2443217 := bstep (se 2 (by rfl) ⟨916206, by rfl⟩ : syracuseStep 2443217 = 1832413) B1832413
theorem B2320339 : Blo 1628513 2320339 := bstep (se 1 (by rfl) ⟨1740254, by rfl⟩ : syracuseStep 2320339 = 3480509) B3480509
theorem B2443235 : Blo 1628513 2443235 := bstep (se 1 (by rfl) ⟨1832426, by rfl⟩ : syracuseStep 2443235 = 3664853) B3664853
theorem B2443265 : Blo 1628513 2443265 := bstep (se 2 (by rfl) ⟨916224, by rfl⟩ : syracuseStep 2443265 = 1832449) B1832449
theorem B2353153 : Blo 1628513 2353153 := bstep (se 2 (by rfl) ⟨882432, by rfl⟩ : syracuseStep 2353153 = 1764865) B1764865
theorem B2443283 : Blo 1628513 2443283 := bstep (se 1 (by rfl) ⟨1832462, by rfl⟩ : syracuseStep 2443283 = 3664925) B3664925
theorem B2443313 : Blo 1628513 2443313 := bstep (se 2 (by rfl) ⟨916242, by rfl⟩ : syracuseStep 2443313 = 1832485) B1832485
theorem B75221045 : Blo 1628513 75221045 := bstep (se 5 (by rfl) ⟨3525986, by rfl⟩ : syracuseStep 75221045 = 7051973) B7051973
theorem B17860661 : Blo 1628513 17860661 := bstep (se 5 (by rfl) ⟨837218, by rfl⟩ : syracuseStep 17860661 = 1674437) B1674437
theorem B2443331 : Blo 1628513 2443331 := bstep (se 1 (by rfl) ⟨1832498, by rfl⟩ : syracuseStep 2443331 = 3664997) B3664997
theorem B10438733 : Blo 1628513 10438733 := bstep (se 3 (by rfl) ⟨1957262, by rfl⟩ : syracuseStep 10438733 = 3914525) B3914525
theorem B8251469 : Blo 1628513 8251469 := bstep (se 3 (by rfl) ⟨1547150, by rfl⟩ : syracuseStep 8251469 = 3094301) B3094301
theorem B1984595 : Blo 1628513 1984595 := bstep (se 1 (by rfl) ⟨1488446, by rfl⟩ : syracuseStep 1984595 = 2976893) B2976893
theorem B2443361 : Blo 1628513 2443361 := bstep (se 2 (by rfl) ⟨916260, by rfl⟩ : syracuseStep 2443361 = 1832521) B1832521
theorem B4638833 : Blo 1628513 4638833 := bstep (se 2 (by rfl) ⟨1739562, by rfl⟩ : syracuseStep 4638833 = 3479125) B3479125
theorem B2443379 : Blo 1628513 2443379 := bstep (se 1 (by rfl) ⟨1832534, by rfl⟩ : syracuseStep 2443379 = 3665069) B3665069
theorem B2443409 : Blo 1628513 2443409 := bstep (se 2 (by rfl) ⟨916278, by rfl⟩ : syracuseStep 2443409 = 1832557) B1832557
theorem B2443427 : Blo 1628513 2443427 := bstep (se 1 (by rfl) ⟨1832570, by rfl⟩ : syracuseStep 2443427 = 3665141) B3665141
theorem B2091187 : Blo 1628513 2091187 := bstep (se 1 (by rfl) ⟨1568390, by rfl⟩ : syracuseStep 2091187 = 3136781) B3136781
theorem B2443457 : Blo 1628513 2443457 := bstep (se 2 (by rfl) ⟨916296, by rfl⟩ : syracuseStep 2443457 = 1832593) B1832593
theorem B5499089 : Blo 1628513 5499089 := bstep (se 2 (by rfl) ⟨2062158, by rfl⟩ : syracuseStep 5499089 = 4124317) B4124317
theorem B2443475 : Blo 1628513 2443475 := bstep (se 1 (by rfl) ⟨1832606, by rfl⟩ : syracuseStep 2443475 = 3665213) B3665213
theorem B89163989 : Blo 1628513 89163989 := bstep (se 7 (by rfl) ⟨1044890, by rfl⟩ : syracuseStep 89163989 = 2089781) B2089781
theorem B11741411 : Blo 1628513 11741411 := bstep (se 1 (by rfl) ⟨8806058, by rfl⟩ : syracuseStep 11741411 = 17612117) B17612117
theorem B2443505 : Blo 1628513 2443505 := bstep (se 2 (by rfl) ⟨916314, by rfl⟩ : syracuseStep 2443505 = 1832629) B1832629
theorem B13920497 : Blo 1628513 13920497 := bstep (se 2 (by rfl) ⟨5220186, by rfl⟩ : syracuseStep 13920497 = 10440373) B10440373
theorem B2443523 : Blo 1628513 2443523 := bstep (se 1 (by rfl) ⟨1832642, by rfl⟩ : syracuseStep 2443523 = 3665285) B3665285
theorem B2443553 : Blo 1628513 2443553 := bstep (se 2 (by rfl) ⟨916332, by rfl⟩ : syracuseStep 2443553 = 1832665) B1832665
theorem B2443571 : Blo 1628513 2443571 := bstep (se 1 (by rfl) ⟨1832678, by rfl⟩ : syracuseStep 2443571 = 3665357) B3665357
theorem B1739075 : Blo 1628513 1739075 := bstep (se 1 (by rfl) ⟨1304306, by rfl⟩ : syracuseStep 1739075 = 2608613) B2608613
theorem B2443601 : Blo 1628513 2443601 := bstep (se 2 (by rfl) ⟨916350, by rfl⟩ : syracuseStep 2443601 = 1832701) B1832701
theorem B2443619 : Blo 1628513 2443619 := bstep (se 1 (by rfl) ⟨1832714, by rfl⟩ : syracuseStep 2443619 = 3665429) B3665429
theorem B3664241 : Blo 1628513 3664241 := bstep (se 2 (by rfl) ⟨1374090, by rfl⟩ : syracuseStep 3664241 = 2748181) B2748181
theorem B2443649 : Blo 1628513 2443649 := bstep (se 2 (by rfl) ⟨916368, by rfl⟩ : syracuseStep 2443649 = 1832737) B1832737
theorem B3664259 : Blo 1628513 3664259 := bstep (se 1 (by rfl) ⟨2748194, by rfl⟩ : syracuseStep 3664259 = 5496389) B5496389
theorem B2443667 : Blo 1628513 2443667 := bstep (se 1 (by rfl) ⟨1832750, by rfl⟩ : syracuseStep 2443667 = 3665501) B3665501
theorem B2443697 : Blo 1628513 2443697 := bstep (se 2 (by rfl) ⟨916386, by rfl⟩ : syracuseStep 2443697 = 1832773) B1832773
theorem B2320817 : Blo 1628513 2320817 := bstep (se 2 (by rfl) ⟨870306, by rfl⟩ : syracuseStep 2320817 = 1740613) B1740613
theorem B2443715 : Blo 1628513 2443715 := bstep (se 1 (by rfl) ⟨1832786, by rfl⟩ : syracuseStep 2443715 = 3665573) B3665573
theorem B44616133 : Blo 1628513 44616133 := bstep (se 4 (by rfl) ⟨4182762, by rfl⟩ : syracuseStep 44616133 = 8365525) B8365525
theorem B2443745 : Blo 1628513 2443745 := bstep (se 2 (by rfl) ⟨916404, by rfl⟩ : syracuseStep 2443745 = 1832809) B1832809
theorem B2443763 : Blo 1628513 2443763 := bstep (se 1 (by rfl) ⟨1832822, by rfl⟩ : syracuseStep 2443763 = 3665645) B3665645
theorem B2443793 : Blo 1628513 2443793 := bstep (se 2 (by rfl) ⟨916422, by rfl⟩ : syracuseStep 2443793 = 1832845) B1832845
theorem B2443811 : Blo 1628513 2443811 := bstep (se 1 (by rfl) ⟨1832858, by rfl⟩ : syracuseStep 2443811 = 3665717) B3665717
theorem B2320931 : Blo 1628513 2320931 := bstep (se 1 (by rfl) ⟨1740698, by rfl⟩ : syracuseStep 2320931 = 3481397) B3481397
theorem B2443841 : Blo 1628513 2443841 := bstep (se 2 (by rfl) ⟨916440, by rfl⟩ : syracuseStep 2443841 = 1832881) B1832881
theorem B2787907 : Blo 1628513 2787907 := bstep (se 1 (by rfl) ⟨2090930, by rfl⟩ : syracuseStep 2787907 = 4181861) B4181861
theorem B2091587 : Blo 1628513 2091587 := bstep (se 1 (by rfl) ⟨1568690, by rfl⟩ : syracuseStep 2091587 = 3137381) B3137381
theorem B2443859 : Blo 1628513 2443859 := bstep (se 1 (by rfl) ⟨1832894, by rfl⟩ : syracuseStep 2443859 = 3665789) B3665789
theorem B6957667 : Blo 1628513 6957667 := bstep (se 1 (by rfl) ⟨5218250, by rfl⟩ : syracuseStep 6957667 = 10436501) B10436501
theorem B2443889 : Blo 1628513 2443889 := bstep (se 2 (by rfl) ⟨916458, by rfl⟩ : syracuseStep 2443889 = 1832917) B1832917
theorem B9914993 : Blo 1628513 9914993 := bstep (se 2 (by rfl) ⟨3718122, by rfl⟩ : syracuseStep 9914993 = 7436245) B7436245
theorem B2321011 : Blo 1628513 2321011 := bstep (se 1 (by rfl) ⟨1740758, by rfl⟩ : syracuseStep 2321011 = 3481517) B3481517
theorem B2443907 : Blo 1628513 2443907 := bstep (se 1 (by rfl) ⟨1832930, by rfl⟩ : syracuseStep 2443907 = 3665861) B3665861
theorem B6187661 : Blo 1628513 6187661 := bstep (se 3 (by rfl) ⟨1160186, by rfl⟩ : syracuseStep 6187661 = 2320373) B2320373
theorem B3664529 : Blo 1628513 3664529 := bstep (se 2 (by rfl) ⟨1374198, by rfl⟩ : syracuseStep 3664529 = 2748397) B2748397
theorem B2443937 : Blo 1628513 2443937 := bstep (se 2 (by rfl) ⟨916476, by rfl⟩ : syracuseStep 2443937 = 1832953) B1832953
theorem B3664547 : Blo 1628513 3664547 := bstep (se 1 (by rfl) ⟨2748410, by rfl⟩ : syracuseStep 3664547 = 5496821) B5496821
theorem B5876401 : Blo 1628513 5876401 := bstep (se 2 (by rfl) ⟨2203650, by rfl⟩ : syracuseStep 5876401 = 4407301) B4407301
theorem B2443955 : Blo 1628513 2443955 := bstep (se 1 (by rfl) ⟨1832966, by rfl⟩ : syracuseStep 2443955 = 3665933) B3665933
theorem B4123345 : Blo 1628513 4123345 := bstep (se 2 (by rfl) ⟨1546254, by rfl⟩ : syracuseStep 4123345 = 3092509) B3092509
theorem B2443985 : Blo 1628513 2443985 := bstep (se 2 (by rfl) ⟨916494, by rfl⟩ : syracuseStep 2443985 = 1832989) B1832989
theorem B2444003 : Blo 1628513 2444003 := bstep (se 1 (by rfl) ⟨1833002, by rfl⟩ : syracuseStep 2444003 = 3666005) B3666005
theorem B2788067 : Blo 1628513 2788067 := bstep (se 1 (by rfl) ⟨2091050, by rfl⟩ : syracuseStep 2788067 = 4182101) B4182101
theorem B5499629 : Blo 1628513 5499629 := bstep (se 3 (by rfl) ⟨1031180, by rfl⟩ : syracuseStep 5499629 = 2062361) B2062361
theorem B9538289 : Blo 1628513 9538289 := bstep (se 2 (by rfl) ⟨3576858, by rfl⟩ : syracuseStep 9538289 = 7153717) B7153717
theorem B2444033 : Blo 1628513 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B2444051 : Blo 1628513 2444051 := bstep (se 1 (by rfl) ⟨1833038, by rfl⟩ : syracuseStep 2444051 = 3666077) B3666077
theorem B5499683 : Blo 1628513 5499683 := bstep (se 1 (by rfl) ⟨4124762, by rfl⟩ : syracuseStep 5499683 = 8249525) B8249525
theorem B2444081 : Blo 1628513 2444081 := bstep (se 2 (by rfl) ⟨916530, by rfl⟩ : syracuseStep 2444081 = 1833061) B1833061
theorem B2444099 : Blo 1628513 2444099 := bstep (se 1 (by rfl) ⟨1833074, by rfl⟩ : syracuseStep 2444099 = 3666149) B3666149
theorem B2444129 : Blo 1628513 2444129 := bstep (se 2 (by rfl) ⟨916548, by rfl⟩ : syracuseStep 2444129 = 1833097) B1833097
theorem B2444147 : Blo 1628513 2444147 := bstep (se 1 (by rfl) ⟨1833110, by rfl⟩ : syracuseStep 2444147 = 3666221) B3666221
theorem B4639619 : Blo 1628513 4639619 := bstep (se 1 (by rfl) ⟨3479714, by rfl⟩ : syracuseStep 4639619 = 6959429) B6959429
theorem B9907085 : Blo 1628513 9907085 := bstep (se 3 (by rfl) ⟨1857578, by rfl⟩ : syracuseStep 9907085 = 3715157) B3715157
theorem B2444177 : Blo 1628513 2444177 := bstep (se 2 (by rfl) ⟨916566, by rfl⟩ : syracuseStep 2444177 = 1833133) B1833133
theorem B2444195 : Blo 1628513 2444195 := bstep (se 1 (by rfl) ⟨1833146, by rfl⟩ : syracuseStep 2444195 = 3666293) B3666293
theorem B3664817 : Blo 1628513 3664817 := bstep (se 2 (by rfl) ⟨1374306, by rfl⟩ : syracuseStep 3664817 = 2748613) B2748613
theorem B2444225 : Blo 1628513 2444225 := bstep (se 2 (by rfl) ⟨916584, by rfl⟩ : syracuseStep 2444225 = 1833169) B1833169
theorem B3664835 : Blo 1628513 3664835 := bstep (se 1 (by rfl) ⟨2748626, by rfl⟩ : syracuseStep 3664835 = 5497253) B5497253
theorem B22309829 : Blo 1628513 22309829 := bstep (se 4 (by rfl) ⟨2091546, by rfl⟩ : syracuseStep 22309829 = 4183093) B4183093
theorem B2444243 : Blo 1628513 2444243 := bstep (se 1 (by rfl) ⟨1833182, by rfl⟩ : syracuseStep 2444243 = 3666365) B3666365
theorem B4123619 : Blo 1628513 4123619 := bstep (se 1 (by rfl) ⟨3092714, by rfl⟩ : syracuseStep 4123619 = 6185429) B6185429
theorem B2444273 : Blo 1628513 2444273 := bstep (se 2 (by rfl) ⟨916602, by rfl⟩ : syracuseStep 2444273 = 1833205) B1833205
theorem B2444291 : Blo 1628513 2444291 := bstep (se 1 (by rfl) ⟨1833218, by rfl⟩ : syracuseStep 2444291 = 3666437) B3666437
theorem B2444321 : Blo 1628513 2444321 := bstep (se 2 (by rfl) ⟨916620, by rfl⟩ : syracuseStep 2444321 = 1833241) B1833241
theorem B5499953 : Blo 1628513 5499953 := bstep (se 2 (by rfl) ⟨2062482, by rfl⟩ : syracuseStep 5499953 = 4124965) B4124965
theorem B1739827 : Blo 1628513 1739827 := bstep (se 1 (by rfl) ⟨1304870, by rfl⟩ : syracuseStep 1739827 = 2609741) B2609741
theorem B2444339 : Blo 1628513 2444339 := bstep (se 1 (by rfl) ⟨1833254, by rfl⟩ : syracuseStep 2444339 = 3666509) B3666509
theorem B2444369 : Blo 1628513 2444369 := bstep (se 2 (by rfl) ⟨916638, by rfl⟩ : syracuseStep 2444369 = 1833277) B1833277
theorem B2444387 : Blo 1628513 2444387 := bstep (se 1 (by rfl) ⟨1833290, by rfl⟩ : syracuseStep 2444387 = 3666581) B3666581
theorem B31755377 : Blo 1628513 31755377 := bstep (se 2 (by rfl) ⟨11908266, by rfl⟩ : syracuseStep 31755377 = 23816533) B23816533
theorem B59477105 : Blo 1628513 59477105 := bstep (se 2 (by rfl) ⟨22303914, by rfl⟩ : syracuseStep 59477105 = 44607829) B44607829
theorem B2444417 : Blo 1628513 2444417 := bstep (se 2 (by rfl) ⟨916656, by rfl⟩ : syracuseStep 2444417 = 1833313) B1833313
theorem B29731981 : Blo 1628513 29731981 := bstep (se 3 (by rfl) ⟨5574746, by rfl⟩ : syracuseStep 29731981 = 11149493) B11149493
theorem B2444435 : Blo 1628513 2444435 := bstep (se 1 (by rfl) ⟨1833326, by rfl⟩ : syracuseStep 2444435 = 3666653) B3666653
theorem B2321569 : Blo 1628513 2321569 := bstep (se 2 (by rfl) ⟨870588, by rfl⟩ : syracuseStep 2321569 = 1741177) B1741177
theorem B4123811 : Blo 1628513 4123811 := bstep (se 1 (by rfl) ⟨3092858, by rfl⟩ : syracuseStep 4123811 = 6185717) B6185717
theorem B2444465 : Blo 1628513 2444465 := bstep (se 2 (by rfl) ⟨916674, by rfl⟩ : syracuseStep 2444465 = 1833349) B1833349
theorem B2444483 : Blo 1628513 2444483 := bstep (se 1 (by rfl) ⟨1833362, by rfl⟩ : syracuseStep 2444483 = 3666725) B3666725
theorem B4639949 : Blo 1628513 4639949 := bstep (se 3 (by rfl) ⟨869990, by rfl⟩ : syracuseStep 4639949 = 1739981) B1739981
theorem B3665105 : Blo 1628513 3665105 := bstep (se 2 (by rfl) ⟨1374414, by rfl⟩ : syracuseStep 3665105 = 2748829) B2748829
theorem B2444513 : Blo 1628513 2444513 := bstep (se 2 (by rfl) ⟨916692, by rfl⟩ : syracuseStep 2444513 = 1833385) B1833385
theorem B2862307 : Blo 1628513 2862307 := bstep (se 1 (by rfl) ⟨2146730, by rfl⟩ : syracuseStep 2862307 = 4293461) B4293461
theorem B3665123 : Blo 1628513 3665123 := bstep (se 1 (by rfl) ⟨2748842, by rfl⟩ : syracuseStep 3665123 = 5497685) B5497685
theorem B5573873 : Blo 1628513 5573873 := bstep (se 2 (by rfl) ⟨2090202, by rfl⟩ : syracuseStep 5573873 = 4180405) B4180405
theorem B2444531 : Blo 1628513 2444531 := bstep (se 1 (by rfl) ⟨1833398, by rfl⟩ : syracuseStep 2444531 = 3666797) B3666797
theorem B4640017 : Blo 1628513 4640017 := bstep (se 2 (by rfl) ⟨1740006, by rfl⟩ : syracuseStep 4640017 = 3480013) B3480013
theorem B2444561 : Blo 1628513 2444561 := bstep (se 2 (by rfl) ⟨916710, by rfl⟩ : syracuseStep 2444561 = 1833421) B1833421
theorem B9276707 : Blo 1628513 9276707 := bstep (se 1 (by rfl) ⟨6957530, by rfl⟩ : syracuseStep 9276707 = 13915061) B13915061
theorem B2444579 : Blo 1628513 2444579 := bstep (se 1 (by rfl) ⟨1833434, by rfl⟩ : syracuseStep 2444579 = 3666869) B3666869
theorem B2444609 : Blo 1628513 2444609 := bstep (se 2 (by rfl) ⟨916728, by rfl⟩ : syracuseStep 2444609 = 1833457) B1833457
theorem B2936131 : Blo 1628513 2936131 := bstep (se 1 (by rfl) ⟨2202098, by rfl⟩ : syracuseStep 2936131 = 4404197) B4404197
theorem B2444627 : Blo 1628513 2444627 := bstep (se 1 (by rfl) ⟨1833470, by rfl⟩ : syracuseStep 2444627 = 3666941) B3666941
theorem B2444657 : Blo 1628513 2444657 := bstep (se 2 (by rfl) ⟨916746, by rfl⟩ : syracuseStep 2444657 = 1833493) B1833493
theorem B2444675 : Blo 1628513 2444675 := bstep (se 1 (by rfl) ⟨1833506, by rfl⟩ : syracuseStep 2444675 = 3667013) B3667013
theorem B2444705 : Blo 1628513 2444705 := bstep (se 2 (by rfl) ⟨916764, by rfl⟩ : syracuseStep 2444705 = 1833529) B1833529
theorem B2444723 : Blo 1628513 2444723 := bstep (se 1 (by rfl) ⟨1833542, by rfl⟩ : syracuseStep 2444723 = 3667085) B3667085
theorem B2444753 : Blo 1628513 2444753 := bstep (se 2 (by rfl) ⟨916782, by rfl⟩ : syracuseStep 2444753 = 1833565) B1833565
theorem B2444771 : Blo 1628513 2444771 := bstep (se 1 (by rfl) ⟨1833578, by rfl⟩ : syracuseStep 2444771 = 3667157) B3667157
theorem B3665393 : Blo 1628513 3665393 := bstep (se 2 (by rfl) ⟨1374522, by rfl⟩ : syracuseStep 3665393 = 2749045) B2749045
theorem B2444801 : Blo 1628513 2444801 := bstep (se 2 (by rfl) ⟨916800, by rfl⟩ : syracuseStep 2444801 = 1833601) B1833601
theorem B3665411 : Blo 1628513 3665411 := bstep (se 1 (by rfl) ⟨2749058, by rfl⟩ : syracuseStep 3665411 = 5498117) B5498117
theorem B2444819 : Blo 1628513 2444819 := bstep (se 1 (by rfl) ⟨1833614, by rfl⟩ : syracuseStep 2444819 = 3667229) B3667229
theorem B4640291 : Blo 1628513 4640291 := bstep (se 1 (by rfl) ⟨3480218, by rfl⟩ : syracuseStep 4640291 = 6960437) B6960437
theorem B7826993 : Blo 1628513 7826993 := bstep (se 2 (by rfl) ⟨2935122, by rfl⟩ : syracuseStep 7826993 = 5870245) B5870245
theorem B2444849 : Blo 1628513 2444849 := bstep (se 2 (by rfl) ⟨916818, by rfl⟩ : syracuseStep 2444849 = 1833637) B1833637
theorem B2444867 : Blo 1628513 2444867 := bstep (se 1 (by rfl) ⟨1833650, by rfl⟩ : syracuseStep 2444867 = 3667301) B3667301
theorem B5500493 : Blo 1628513 5500493 := bstep (se 3 (by rfl) ⟨1031342, by rfl⟩ : syracuseStep 5500493 = 2062685) B2062685
theorem B2444897 : Blo 1628513 2444897 := bstep (se 2 (by rfl) ⟨916836, by rfl⟩ : syracuseStep 2444897 = 1833673) B1833673
theorem B2444915 : Blo 1628513 2444915 := bstep (se 1 (by rfl) ⟨1833686, by rfl⟩ : syracuseStep 2444915 = 3667373) B3667373
theorem B5500547 : Blo 1628513 5500547 := bstep (se 1 (by rfl) ⟨4125410, by rfl⟩ : syracuseStep 5500547 = 8250821) B8250821
theorem B2444945 : Blo 1628513 2444945 := bstep (se 2 (by rfl) ⟨916854, by rfl⟩ : syracuseStep 2444945 = 1833709) B1833709
theorem B5222033 : Blo 1628513 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B2444963 : Blo 1628513 2444963 := bstep (se 1 (by rfl) ⟨1833722, by rfl⟩ : syracuseStep 2444963 = 3667445) B3667445
theorem B2444993 : Blo 1628513 2444993 := bstep (se 2 (by rfl) ⟨916872, by rfl⟩ : syracuseStep 2444993 = 1833745) B1833745
theorem B2445011 : Blo 1628513 2445011 := bstep (se 1 (by rfl) ⟨1833758, by rfl⟩ : syracuseStep 2445011 = 3667517) B3667517
theorem B2445041 : Blo 1628513 2445041 := bstep (se 2 (by rfl) ⟨916890, by rfl⟩ : syracuseStep 2445041 = 1833781) B1833781
theorem B2748161 : Blo 1628513 2748161 := bstep (se 2 (by rfl) ⟨1030560, by rfl⟩ : syracuseStep 2748161 = 2061121) B2061121
theorem B2445059 : Blo 1628513 2445059 := bstep (se 1 (by rfl) ⟨1833794, by rfl⟩ : syracuseStep 2445059 = 3667589) B3667589
theorem B3665681 : Blo 1628513 3665681 := bstep (se 2 (by rfl) ⟨1374630, by rfl⟩ : syracuseStep 3665681 = 2749261) B2749261
theorem B2445089 : Blo 1628513 2445089 := bstep (se 2 (by rfl) ⟨916908, by rfl⟩ : syracuseStep 2445089 = 1833817) B1833817
theorem B3665699 : Blo 1628513 3665699 := bstep (se 1 (by rfl) ⟨2749274, by rfl⟩ : syracuseStep 3665699 = 5498549) B5498549
theorem B2477873 : Blo 1628513 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B2445107 : Blo 1628513 2445107 := bstep (se 1 (by rfl) ⟨1833830, by rfl⟩ : syracuseStep 2445107 = 3667661) B3667661
theorem B2445137 : Blo 1628513 2445137 := bstep (se 2 (by rfl) ⟨916926, by rfl⟩ : syracuseStep 2445137 = 1833853) B1833853
theorem B2445155 : Blo 1628513 2445155 := bstep (se 1 (by rfl) ⟨1833866, by rfl⟩ : syracuseStep 2445155 = 3667733) B3667733
theorem B16732003 : Blo 1628513 16732003 := bstep (se 1 (by rfl) ⟨12549002, by rfl⟩ : syracuseStep 16732003 = 25098005) B25098005
theorem B29003633 : Blo 1628513 29003633 := bstep (se 2 (by rfl) ⟨10876362, by rfl⟩ : syracuseStep 29003633 = 21752725) B21752725
theorem B2748289 : Blo 1628513 2748289 := bstep (se 2 (by rfl) ⟨1030608, by rfl⟩ : syracuseStep 2748289 = 2061217) B2061217
theorem B2445185 : Blo 1628513 2445185 := bstep (se 2 (by rfl) ⟨916944, by rfl⟩ : syracuseStep 2445185 = 1833889) B1833889
theorem B5500817 : Blo 1628513 5500817 := bstep (se 2 (by rfl) ⟨2062806, by rfl⟩ : syracuseStep 5500817 = 4125613) B4125613
theorem B2445203 : Blo 1628513 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B2748323 : Blo 1628513 2748323 := bstep (se 1 (by rfl) ⟨2061242, by rfl⟩ : syracuseStep 2748323 = 4122485) B4122485
theorem B2445233 : Blo 1628513 2445233 := bstep (se 2 (by rfl) ⟨916962, by rfl⟩ : syracuseStep 2445233 = 1833925) B1833925
theorem B2445251 : Blo 1628513 2445251 := bstep (se 1 (by rfl) ⟨1833938, by rfl⟩ : syracuseStep 2445251 = 3667877) B3667877
theorem B2445281 : Blo 1628513 2445281 := bstep (se 2 (by rfl) ⟨916980, by rfl⟩ : syracuseStep 2445281 = 1833961) B1833961
theorem B2445299 : Blo 1628513 2445299 := bstep (se 1 (by rfl) ⟨1833974, by rfl⟩ : syracuseStep 2445299 = 3667949) B3667949
theorem B9285637 : Blo 1628513 9285637 := bstep (se 4 (by rfl) ⟨870528, by rfl⟩ : syracuseStep 9285637 = 1741057) B1741057
theorem B2445329 : Blo 1628513 2445329 := bstep (se 2 (by rfl) ⟨916998, by rfl⟩ : syracuseStep 2445329 = 1833997) B1833997
theorem B2748451 : Blo 1628513 2748451 := bstep (se 1 (by rfl) ⟨2061338, by rfl⟩ : syracuseStep 2748451 = 4122677) B4122677
theorem B1740835 : Blo 1628513 1740835 := bstep (se 1 (by rfl) ⟨1305626, by rfl⟩ : syracuseStep 1740835 = 2611253) B2611253
theorem B2445347 : Blo 1628513 2445347 := bstep (se 1 (by rfl) ⟨1834010, by rfl⟩ : syracuseStep 2445347 = 3668021) B3668021
theorem B3665969 : Blo 1628513 3665969 := bstep (se 2 (by rfl) ⟨1374738, by rfl⟩ : syracuseStep 3665969 = 2749477) B2749477
theorem B2445377 : Blo 1628513 2445377 := bstep (se 2 (by rfl) ⟨917016, by rfl⟩ : syracuseStep 2445377 = 1834033) B1834033
theorem B3665987 : Blo 1628513 3665987 := bstep (se 1 (by rfl) ⟨2749490, by rfl⟩ : syracuseStep 3665987 = 5498981) B5498981
theorem B4124753 : Blo 1628513 4124753 := bstep (se 2 (by rfl) ⟨1546782, by rfl⟩ : syracuseStep 4124753 = 3093565) B3093565
theorem B2445395 : Blo 1628513 2445395 := bstep (se 1 (by rfl) ⟨1834046, by rfl⟩ : syracuseStep 2445395 = 3668093) B3668093
theorem B3092593 : Blo 1628513 3092593 := bstep (se 2 (by rfl) ⟨1159722, by rfl⟩ : syracuseStep 3092593 = 2319445) B2319445
theorem B2445425 : Blo 1628513 2445425 := bstep (se 2 (by rfl) ⟨917034, by rfl⟩ : syracuseStep 2445425 = 1834069) B1834069
theorem B4124803 : Blo 1628513 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B2445443 : Blo 1628513 2445443 := bstep (se 1 (by rfl) ⟨1834082, by rfl⟩ : syracuseStep 2445443 = 3668165) B3668165
theorem B2445473 : Blo 1628513 2445473 := bstep (se 2 (by rfl) ⟨917052, by rfl⟩ : syracuseStep 2445473 = 1834105) B1834105
theorem B2748593 : Blo 1628513 2748593 := bstep (se 2 (by rfl) ⟨1030722, by rfl⟩ : syracuseStep 2748593 = 2061445) B2061445
theorem B2445491 : Blo 1628513 2445491 := bstep (se 1 (by rfl) ⟨1834118, by rfl⟩ : syracuseStep 2445491 = 3668237) B3668237
theorem B2445521 : Blo 1628513 2445521 := bstep (se 2 (by rfl) ⟨917070, by rfl⟩ : syracuseStep 2445521 = 1834141) B1834141
theorem B8245475 : Blo 1628513 8245475 := bstep (se 1 (by rfl) ⟨6184106, by rfl⟩ : syracuseStep 8245475 = 12368213) B12368213
theorem B7827683 : Blo 1628513 7827683 := bstep (se 1 (by rfl) ⟨5870762, by rfl⟩ : syracuseStep 7827683 = 11741525) B11741525
theorem B2445539 : Blo 1628513 2445539 := bstep (se 1 (by rfl) ⟨1834154, by rfl⟩ : syracuseStep 2445539 = 3668309) B3668309
theorem B2445569 : Blo 1628513 2445569 := bstep (se 2 (by rfl) ⟨917088, by rfl⟩ : syracuseStep 2445569 = 1834177) B1834177
theorem B5222659 : Blo 1628513 5222659 := bstep (se 1 (by rfl) ⟨3916994, by rfl⟩ : syracuseStep 5222659 = 7833989) B7833989
theorem B4124945 : Blo 1628513 4124945 := bstep (se 2 (by rfl) ⟨1546854, by rfl⟩ : syracuseStep 4124945 = 3093709) B3093709
theorem B2445587 : Blo 1628513 2445587 := bstep (se 1 (by rfl) ⟨1834190, by rfl⟩ : syracuseStep 2445587 = 3668381) B3668381
theorem B2748721 : Blo 1628513 2748721 := bstep (se 2 (by rfl) ⟨1030770, by rfl⟩ : syracuseStep 2748721 = 2061541) B2061541
theorem B2445617 : Blo 1628513 2445617 := bstep (se 2 (by rfl) ⟨917106, by rfl⟩ : syracuseStep 2445617 = 1834213) B1834213
theorem B2445635 : Blo 1628513 2445635 := bstep (se 1 (by rfl) ⟨1834226, by rfl⟩ : syracuseStep 2445635 = 3668453) B3668453
theorem B3666257 : Blo 1628513 3666257 := bstep (se 2 (by rfl) ⟨1374846, by rfl⟩ : syracuseStep 3666257 = 2749693) B2749693
theorem B2748755 : Blo 1628513 2748755 := bstep (se 1 (by rfl) ⟨2061566, by rfl⟩ : syracuseStep 2748755 = 4123133) B4123133
theorem B2445665 : Blo 1628513 2445665 := bstep (se 2 (by rfl) ⟨917124, by rfl⟩ : syracuseStep 2445665 = 1834249) B1834249
theorem B3666275 : Blo 1628513 3666275 := bstep (se 1 (by rfl) ⟨2749706, by rfl⟩ : syracuseStep 3666275 = 5499413) B5499413
theorem B4641133 : Blo 1628513 4641133 := bstep (se 3 (by rfl) ⟨870212, by rfl⟩ : syracuseStep 4641133 = 1740425) B1740425
theorem B2445683 : Blo 1628513 2445683 := bstep (se 1 (by rfl) ⟨1834262, by rfl⟩ : syracuseStep 2445683 = 3668525) B3668525
theorem B20083085 : Blo 1628513 20083085 := bstep (se 3 (by rfl) ⟨3765578, by rfl⟩ : syracuseStep 20083085 = 7531157) B7531157
theorem B2445713 : Blo 1628513 2445713 := bstep (se 2 (by rfl) ⟨917142, by rfl⟩ : syracuseStep 2445713 = 1834285) B1834285
theorem B2445731 : Blo 1628513 2445731 := bstep (se 1 (by rfl) ⟨1834298, by rfl⟩ : syracuseStep 2445731 = 3668597) B3668597
theorem B5501357 : Blo 1628513 5501357 := bstep (se 3 (by rfl) ⟨1031504, by rfl⟩ : syracuseStep 5501357 = 2063009) B2063009
theorem B2609587 : Blo 1628513 2609587 := bstep (se 1 (by rfl) ⟨1957190, by rfl⟩ : syracuseStep 2609587 = 3914381) B3914381
theorem B2478529 : Blo 1628513 2478529 := bstep (se 2 (by rfl) ⟨929448, by rfl⟩ : syracuseStep 2478529 = 1858897) B1858897
theorem B2445761 : Blo 1628513 2445761 := bstep (se 2 (by rfl) ⟨917160, by rfl⟩ : syracuseStep 2445761 = 1834321) B1834321
theorem B2748883 : Blo 1628513 2748883 := bstep (se 1 (by rfl) ⟨2061662, by rfl⟩ : syracuseStep 2748883 = 4123325) B4123325
theorem B2609633 : Blo 1628513 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B5501411 : Blo 1628513 5501411 := bstep (se 1 (by rfl) ⟨4126058, by rfl⟩ : syracuseStep 5501411 = 8252117) B8252117
theorem B3092995 : Blo 1628513 3092995 := bstep (se 1 (by rfl) ⟨2319746, by rfl⟩ : syracuseStep 3092995 = 4639493) B4639493
theorem B4641293 : Blo 1628513 4641293 := bstep (se 3 (by rfl) ⟨870242, by rfl⟩ : syracuseStep 4641293 = 1740485) B1740485
theorem B3093041 : Blo 1628513 3093041 := bstep (se 2 (by rfl) ⟨1159890, by rfl⟩ : syracuseStep 3093041 = 2319781) B2319781
theorem B2749025 : Blo 1628513 2749025 := bstep (se 2 (by rfl) ⟨1030884, by rfl⟩ : syracuseStep 2749025 = 2061769) B2061769
theorem B3666545 : Blo 1628513 3666545 := bstep (se 2 (by rfl) ⟨1374954, by rfl⟩ : syracuseStep 3666545 = 2749909) B2749909
theorem B3666563 : Blo 1628513 3666563 := bstep (se 1 (by rfl) ⟨2749922, by rfl⟩ : syracuseStep 3666563 = 5499845) B5499845
theorem B3478211 : Blo 1628513 3478211 := bstep (se 1 (by rfl) ⟨2608658, by rfl⟩ : syracuseStep 3478211 = 5217317) B5217317
theorem B4641475 : Blo 1628513 4641475 := bstep (se 1 (by rfl) ⟨3481106, by rfl⟩ : syracuseStep 4641475 = 6962213) B6962213
theorem B2749153 : Blo 1628513 2749153 := bstep (se 2 (by rfl) ⟨1030932, by rfl⟩ : syracuseStep 2749153 = 2061865) B2061865
theorem B5501681 : Blo 1628513 5501681 := bstep (se 2 (by rfl) ⟨2063130, by rfl⟩ : syracuseStep 5501681 = 4126261) B4126261
theorem B2749187 : Blo 1628513 2749187 := bstep (se 1 (by rfl) ⟨2061890, by rfl⟩ : syracuseStep 2749187 = 4123781) B4123781
theorem B3093329 : Blo 1628513 3093329 := bstep (se 2 (by rfl) ⟨1159998, by rfl⟩ : syracuseStep 3093329 = 2319997) B2319997
theorem B14103395 : Blo 1628513 14103395 := bstep (se 1 (by rfl) ⟨10577546, by rfl⟩ : syracuseStep 14103395 = 21155093) B21155093
theorem B2749315 : Blo 1628513 2749315 := bstep (se 1 (by rfl) ⟨2061986, by rfl⟩ : syracuseStep 2749315 = 4123973) B4123973
theorem B3666833 : Blo 1628513 3666833 := bstep (se 2 (by rfl) ⟨1375062, by rfl⟩ : syracuseStep 3666833 = 2750125) B2750125
theorem B3666851 : Blo 1628513 3666851 := bstep (se 1 (by rfl) ⟨2750138, by rfl⟩ : syracuseStep 3666851 = 5500277) B5500277
theorem B8254385 : Blo 1628513 8254385 := bstep (se 2 (by rfl) ⟨3095394, by rfl⟩ : syracuseStep 8254385 = 6190789) B6190789
theorem B2061283 : Blo 1628513 2061283 := bstep (se 1 (by rfl) ⟨1545962, by rfl⟩ : syracuseStep 2061283 = 3091925) B3091925
theorem B3527651 : Blo 1628513 3527651 := bstep (se 1 (by rfl) ⟨2645738, by rfl⟩ : syracuseStep 3527651 = 5291477) B5291477
theorem B6960113 : Blo 1628513 6960113 := bstep (se 2 (by rfl) ⟨2610042, by rfl⟩ : syracuseStep 6960113 = 5220085) B5220085
theorem B8246285 : Blo 1628513 8246285 := bstep (se 3 (by rfl) ⟨1546178, by rfl⟩ : syracuseStep 8246285 = 3092357) B3092357
theorem B2749457 : Blo 1628513 2749457 := bstep (se 2 (by rfl) ⟨1031046, by rfl⟩ : syracuseStep 2749457 = 2062093) B2062093
theorem B2061379 : Blo 1628513 2061379 := bstep (se 1 (by rfl) ⟨1546034, by rfl⟩ : syracuseStep 2061379 = 3092069) B3092069
theorem B2749585 : Blo 1628513 2749585 := bstep (se 2 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 2749585 = 2062189) B2062189
theorem B8361137 : Blo 1628513 8361137 := bstep (se 2 (by rfl) ⟨3135426, by rfl⟩ : syracuseStep 8361137 = 6270853) B6270853
theorem B3667121 : Blo 1628513 3667121 := bstep (se 2 (by rfl) ⟨1375170, by rfl⟩ : syracuseStep 3667121 = 2750341) B2750341
theorem B2749619 : Blo 1628513 2749619 := bstep (se 1 (by rfl) ⟨2062214, by rfl⟩ : syracuseStep 2749619 = 4124429) B4124429
theorem B3667139 : Blo 1628513 3667139 := bstep (se 1 (by rfl) ⟨2750354, by rfl⟩ : syracuseStep 3667139 = 5500709) B5500709
theorem B4125937 : Blo 1628513 4125937 := bstep (se 2 (by rfl) ⟨1547226, by rfl⟩ : syracuseStep 4125937 = 3094453) B3094453
theorem B1832179 : Blo 1628513 1832179 := bstep (se 1 (by rfl) ⟨1374134, by rfl⟩ : syracuseStep 1832179 = 2748269) B2748269
theorem B5502221 : Blo 1628513 5502221 := bstep (se 3 (by rfl) ⟨1031666, by rfl⟩ : syracuseStep 5502221 = 2063333) B2063333
theorem B2749747 : Blo 1628513 2749747 := bstep (se 1 (by rfl) ⟨2062310, by rfl⟩ : syracuseStep 2749747 = 4124621) B4124621
theorem B5502275 : Blo 1628513 5502275 := bstep (se 1 (by rfl) ⟨4126706, by rfl⟩ : syracuseStep 5502275 = 8253413) B8253413
theorem B1832323 : Blo 1628513 1832323 := bstep (se 1 (by rfl) ⟨1374242, by rfl⟩ : syracuseStep 1832323 = 2748485) B2748485
theorem B2749889 : Blo 1628513 2749889 := bstep (se 2 (by rfl) ⟨1031208, by rfl⟩ : syracuseStep 2749889 = 2062417) B2062417
theorem B2610625 : Blo 1628513 2610625 := bstep (se 2 (by rfl) ⟨978984, by rfl⟩ : syracuseStep 2610625 = 1957969) B1957969
theorem B3667409 : Blo 1628513 3667409 := bstep (se 2 (by rfl) ⟨1375278, by rfl⟩ : syracuseStep 3667409 = 2750557) B2750557
theorem B3667427 : Blo 1628513 3667427 := bstep (se 1 (by rfl) ⟨2750570, by rfl⟩ : syracuseStep 3667427 = 5501141) B5501141
theorem B6190577 : Blo 1628513 6190577 := bstep (se 2 (by rfl) ⟨2321466, by rfl⟩ : syracuseStep 6190577 = 4642933) B4642933
theorem B4126211 : Blo 1628513 4126211 := bstep (se 1 (by rfl) ⟨3094658, by rfl⟩ : syracuseStep 4126211 = 6189317) B6189317
theorem B1832467 : Blo 1628513 1832467 := bstep (se 1 (by rfl) ⟨1374350, by rfl⟩ : syracuseStep 1832467 = 2748701) B2748701
theorem B3094051 : Blo 1628513 3094051 := bstep (se 1 (by rfl) ⟨2320538, by rfl⟩ : syracuseStep 3094051 = 4641077) B4641077
theorem B2061875 : Blo 1628513 2061875 := bstep (se 1 (by rfl) ⟨1546406, by rfl⟩ : syracuseStep 2061875 = 3092813) B3092813
theorem B2750017 : Blo 1628513 2750017 := bstep (se 2 (by rfl) ⟨1031256, by rfl⟩ : syracuseStep 2750017 = 2062513) B2062513
theorem B3479107 : Blo 1628513 3479107 := bstep (se 1 (by rfl) ⟨2609330, by rfl⟩ : syracuseStep 3479107 = 5218661) B5218661
theorem B5502545 : Blo 1628513 5502545 := bstep (se 2 (by rfl) ⟨2063454, by rfl⟩ : syracuseStep 5502545 = 4126909) B4126909
theorem B2750051 : Blo 1628513 2750051 := bstep (se 1 (by rfl) ⟨2062538, by rfl⟩ : syracuseStep 2750051 = 4125077) B4125077
theorem B4404881 : Blo 1628513 4404881 := bstep (se 2 (by rfl) ⟨1651830, by rfl⟩ : syracuseStep 4404881 = 3303661) B3303661
theorem B1832611 : Blo 1628513 1832611 := bstep (se 1 (by rfl) ⟨1374458, by rfl⟩ : syracuseStep 1832611 = 2748917) B2748917
theorem B4126403 : Blo 1628513 4126403 := bstep (se 1 (by rfl) ⟨3094802, by rfl⟩ : syracuseStep 4126403 = 6189605) B6189605
theorem B2750179 : Blo 1628513 2750179 := bstep (se 1 (by rfl) ⟨2062634, by rfl⟩ : syracuseStep 2750179 = 4125269) B4125269
theorem B3667697 : Blo 1628513 3667697 := bstep (se 2 (by rfl) ⟨1375386, by rfl⟩ : syracuseStep 3667697 = 2750773) B2750773
theorem B14874353 : Blo 1628513 14874353 := bstep (se 2 (by rfl) ⟨5577882, by rfl⟩ : syracuseStep 14874353 = 11155765) B11155765
theorem B3667715 : Blo 1628513 3667715 := bstep (se 1 (by rfl) ⟨2750786, by rfl⟩ : syracuseStep 3667715 = 5501573) B5501573
theorem B1832755 : Blo 1628513 1832755 := bstep (se 1 (by rfl) ⟨1374566, by rfl⟩ : syracuseStep 1832755 = 2749133) B2749133
theorem B4462445 : Blo 1628513 4462445 := bstep (se 3 (by rfl) ⟨836708, by rfl⟩ : syracuseStep 4462445 = 1673417) B1673417
theorem B2750321 : Blo 1628513 2750321 := bstep (se 2 (by rfl) ⟨1031370, by rfl⟩ : syracuseStep 2750321 = 2062741) B2062741
theorem B2611073 : Blo 1628513 2611073 := bstep (se 2 (by rfl) ⟨979152, by rfl⟩ : syracuseStep 2611073 = 1958305) B1958305
theorem B1832899 : Blo 1628513 1832899 := bstep (se 1 (by rfl) ⟨1374674, by rfl⟩ : syracuseStep 1832899 = 2749349) B2749349
theorem B7829453 : Blo 1628513 7829453 := bstep (se 3 (by rfl) ⟨1468022, by rfl⟩ : syracuseStep 7829453 = 2936045) B2936045
theorem B3094499 : Blo 1628513 3094499 := bstep (se 1 (by rfl) ⟨2320874, by rfl⟩ : syracuseStep 3094499 = 4641749) B4641749
theorem B2750449 : Blo 1628513 2750449 := bstep (se 2 (by rfl) ⟨1031418, by rfl⟩ : syracuseStep 2750449 = 2062837) B2062837
theorem B5871629 : Blo 1628513 5871629 := bstep (se 3 (by rfl) ⟨1100930, by rfl⟩ : syracuseStep 5871629 = 2201861) B2201861
theorem B3667985 : Blo 1628513 3667985 := bstep (se 2 (by rfl) ⟨1375494, by rfl⟩ : syracuseStep 3667985 = 2750989) B2750989
theorem B2750483 : Blo 1628513 2750483 := bstep (se 1 (by rfl) ⟨2062862, by rfl⟩ : syracuseStep 2750483 = 4125725) B4125725
theorem B3668003 : Blo 1628513 3668003 := bstep (se 1 (by rfl) ⟨2751002, by rfl⟩ : syracuseStep 3668003 = 5502005) B5502005
theorem B4642865 : Blo 1628513 4642865 := bstep (se 2 (by rfl) ⟨1741074, by rfl⟩ : syracuseStep 4642865 = 3482149) B3482149
theorem B1833043 : Blo 1628513 1833043 := bstep (se 1 (by rfl) ⟨1374782, by rfl⟩ : syracuseStep 1833043 = 2749565) B2749565
theorem B13924493 : Blo 1628513 13924493 := bstep (se 3 (by rfl) ⟨2610842, by rfl⟩ : syracuseStep 13924493 = 5221685) B5221685
theorem B2750611 : Blo 1628513 2750611 := bstep (se 1 (by rfl) ⟨2062958, by rfl⟩ : syracuseStep 2750611 = 4125917) B4125917
theorem B1833187 : Blo 1628513 1833187 := bstep (se 1 (by rfl) ⟨1374890, by rfl⟩ : syracuseStep 1833187 = 2749781) B2749781
theorem B2062579 : Blo 1628513 2062579 := bstep (se 1 (by rfl) ⟨1546934, by rfl⟩ : syracuseStep 2062579 = 3093869) B3093869
theorem B3094787 : Blo 1628513 3094787 := bstep (se 1 (by rfl) ⟨2321090, by rfl⟩ : syracuseStep 3094787 = 4642181) B4642181
theorem B2750753 : Blo 1628513 2750753 := bstep (se 2 (by rfl) ⟨1031532, by rfl⟩ : syracuseStep 2750753 = 2063065) B2063065
theorem B3668273 : Blo 1628513 3668273 := bstep (se 2 (by rfl) ⟨1375602, by rfl⟩ : syracuseStep 3668273 = 2751205) B2751205
theorem B3668291 : Blo 1628513 3668291 := bstep (se 1 (by rfl) ⟨2751218, by rfl⟩ : syracuseStep 3668291 = 5502437) B5502437
theorem B7829837 : Blo 1628513 7829837 := bstep (se 3 (by rfl) ⟨1468094, by rfl⟩ : syracuseStep 7829837 = 2936189) B2936189
theorem B2062675 : Blo 1628513 2062675 := bstep (se 1 (by rfl) ⟨1547006, by rfl⟩ : syracuseStep 2062675 = 3094013) B3094013
theorem B1628515 : Blo 1628513 1628515 := bstep (se 1 (by rfl) ⟨1221386, by rfl⟩ : syracuseStep 1628515 = 2442773) B2442773
theorem B1628531 : Blo 1628513 1628531 := bstep (se 1 (by rfl) ⟨1221398, by rfl⟩ : syracuseStep 1628531 = 2442797) B2442797
theorem B1833331 : Blo 1628513 1833331 := bstep (se 1 (by rfl) ⟨1374998, by rfl⟩ : syracuseStep 1833331 = 2749997) B2749997
theorem B1628547 : Blo 1628513 1628547 := bstep (se 1 (by rfl) ⟨1221410, by rfl⟩ : syracuseStep 1628547 = 2442821) B2442821
theorem B1628563 : Blo 1628513 1628563 := bstep (se 1 (by rfl) ⟨1221422, by rfl⟩ : syracuseStep 1628563 = 2442845) B2442845
theorem B2750881 : Blo 1628513 2750881 := bstep (se 2 (by rfl) ⟨1031580, by rfl⟩ : syracuseStep 2750881 = 2063161) B2063161
theorem B1628579 : Blo 1628513 1628579 := bstep (se 1 (by rfl) ⟨1221434, by rfl⟩ : syracuseStep 1628579 = 2442869) B2442869
theorem B1628595 : Blo 1628513 1628595 := bstep (se 1 (by rfl) ⟨1221446, by rfl⟩ : syracuseStep 1628595 = 2442893) B2442893
theorem B1628611 : Blo 1628513 1628611 := bstep (se 1 (by rfl) ⟨1221458, by rfl⟩ : syracuseStep 1628611 = 2442917) B2442917
theorem B2750915 : Blo 1628513 2750915 := bstep (se 1 (by rfl) ⟨2063186, by rfl⟩ : syracuseStep 2750915 = 4126373) B4126373
theorem B1628627 : Blo 1628513 1628627 := bstep (se 1 (by rfl) ⟨1221470, by rfl⟩ : syracuseStep 1628627 = 2442941) B2442941
theorem B1628643 : Blo 1628513 1628643 := bstep (se 1 (by rfl) ⟨1221482, by rfl⟩ : syracuseStep 1628643 = 2442965) B2442965
theorem B1628659 : Blo 1628513 1628659 := bstep (se 1 (by rfl) ⟨1221494, by rfl⟩ : syracuseStep 1628659 = 2442989) B2442989
theorem B1628675 : Blo 1628513 1628675 := bstep (se 1 (by rfl) ⟨1221506, by rfl⟩ : syracuseStep 1628675 = 2443013) B2443013
theorem B1833475 : Blo 1628513 1833475 := bstep (se 1 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 1833475 = 2750213) B2750213
theorem B1628691 : Blo 1628513 1628691 := bstep (se 1 (by rfl) ⟨1221518, by rfl⟩ : syracuseStep 1628691 = 2443037) B2443037
theorem B1628707 : Blo 1628513 1628707 := bstep (se 1 (by rfl) ⟨1221530, by rfl⟩ : syracuseStep 1628707 = 2443061) B2443061
theorem B1628723 : Blo 1628513 1628723 := bstep (se 1 (by rfl) ⟨1221542, by rfl⟩ : syracuseStep 1628723 = 2443085) B2443085
theorem B1628739 : Blo 1628513 1628739 := bstep (se 1 (by rfl) ⟨1221554, by rfl⟩ : syracuseStep 1628739 = 2443109) B2443109
theorem B2751043 : Blo 1628513 2751043 := bstep (se 1 (by rfl) ⟨2063282, by rfl⟩ : syracuseStep 2751043 = 4126565) B4126565
theorem B1628755 : Blo 1628513 1628755 := bstep (se 1 (by rfl) ⟨1221566, by rfl⟩ : syracuseStep 1628755 = 2443133) B2443133
theorem B3668561 : Blo 1628513 3668561 := bstep (se 2 (by rfl) ⟨1375710, by rfl⟩ : syracuseStep 3668561 = 2751421) B2751421
theorem B1628771 : Blo 1628513 1628771 := bstep (se 1 (by rfl) ⟨1221578, by rfl⟩ : syracuseStep 1628771 = 2443157) B2443157
theorem B13916771 : Blo 1628513 13916771 := bstep (se 1 (by rfl) ⟨10437578, by rfl⟩ : syracuseStep 13916771 = 20875157) B20875157
theorem B3668579 : Blo 1628513 3668579 := bstep (se 1 (by rfl) ⟨2751434, by rfl⟩ : syracuseStep 3668579 = 5502869) B5502869
theorem B1628787 : Blo 1628513 1628787 := bstep (se 1 (by rfl) ⟨1221590, by rfl⟩ : syracuseStep 1628787 = 2443181) B2443181
theorem B1628803 : Blo 1628513 1628803 := bstep (se 1 (by rfl) ⟨1221602, by rfl⟩ : syracuseStep 1628803 = 2443205) B2443205
theorem B1628819 : Blo 1628513 1628819 := bstep (se 1 (by rfl) ⟨1221614, by rfl⟩ : syracuseStep 1628819 = 2443229) B2443229
theorem B1833619 : Blo 1628513 1833619 := bstep (se 1 (by rfl) ⟨1375214, by rfl⟩ : syracuseStep 1833619 = 2750429) B2750429
theorem B1628835 : Blo 1628513 1628835 := bstep (se 1 (by rfl) ⟨1221626, by rfl⟩ : syracuseStep 1628835 = 2443253) B2443253
theorem B1628851 : Blo 1628513 1628851 := bstep (se 1 (by rfl) ⟨1221638, by rfl⟩ : syracuseStep 1628851 = 2443277) B2443277
theorem B1628867 : Blo 1628513 1628867 := bstep (se 1 (by rfl) ⟨1221650, by rfl⟩ : syracuseStep 1628867 = 2443301) B2443301
theorem B2751185 : Blo 1628513 2751185 := bstep (se 2 (by rfl) ⟨1031694, by rfl⟩ : syracuseStep 2751185 = 2063389) B2063389
theorem B1628883 : Blo 1628513 1628883 := bstep (se 1 (by rfl) ⟨1221662, by rfl⟩ : syracuseStep 1628883 = 2443325) B2443325
theorem B1628899 : Blo 1628513 1628899 := bstep (se 1 (by rfl) ⟨1221674, by rfl⟩ : syracuseStep 1628899 = 2443349) B2443349
theorem B1628915 : Blo 1628513 1628915 := bstep (se 1 (by rfl) ⟨1221686, by rfl⟩ : syracuseStep 1628915 = 2443373) B2443373
theorem B1628931 : Blo 1628513 1628931 := bstep (se 1 (by rfl) ⟨1221698, by rfl⟩ : syracuseStep 1628931 = 2443397) B2443397
theorem B3480337 : Blo 1628513 3480337 := bstep (se 2 (by rfl) ⟨1305126, by rfl⟩ : syracuseStep 3480337 = 2610253) B2610253
theorem B1628947 : Blo 1628513 1628947 := bstep (se 1 (by rfl) ⟨1221710, by rfl⟩ : syracuseStep 1628947 = 2443421) B2443421
theorem B1628963 : Blo 1628513 1628963 := bstep (se 1 (by rfl) ⟨1221722, by rfl⟩ : syracuseStep 1628963 = 2443445) B2443445
theorem B1833763 : Blo 1628513 1833763 := bstep (se 1 (by rfl) ⟨1375322, by rfl⟩ : syracuseStep 1833763 = 2750645) B2750645
theorem B1628979 : Blo 1628513 1628979 := bstep (se 1 (by rfl) ⟨1221734, by rfl⟩ : syracuseStep 1628979 = 2443469) B2443469
theorem B1628995 : Blo 1628513 1628995 := bstep (se 1 (by rfl) ⟨1221746, by rfl⟩ : syracuseStep 1628995 = 2443493) B2443493
theorem B2063171 : Blo 1628513 2063171 := bstep (se 1 (by rfl) ⟨1547378, by rfl⟩ : syracuseStep 2063171 = 3094757) B3094757
theorem B2751313 : Blo 1628513 2751313 := bstep (se 2 (by rfl) ⟨1031742, by rfl⟩ : syracuseStep 2751313 = 2063485) B2063485
theorem B1629011 : Blo 1628513 1629011 := bstep (se 1 (by rfl) ⟨1221758, by rfl⟩ : syracuseStep 1629011 = 2443517) B2443517
theorem B1629027 : Blo 1628513 1629027 := bstep (se 1 (by rfl) ⟨1221770, by rfl⟩ : syracuseStep 1629027 = 2443541) B2443541
theorem B1629043 : Blo 1628513 1629043 := bstep (se 1 (by rfl) ⟨1221782, by rfl⟩ : syracuseStep 1629043 = 2443565) B2443565
theorem B2751347 : Blo 1628513 2751347 := bstep (se 1 (by rfl) ⟨2063510, by rfl⟩ : syracuseStep 2751347 = 4127021) B4127021
theorem B1956739 : Blo 1628513 1956739 := bstep (se 1 (by rfl) ⟨1467554, by rfl⟩ : syracuseStep 1956739 = 2935109) B2935109
theorem B1629059 : Blo 1628513 1629059 := bstep (se 1 (by rfl) ⟨1221794, by rfl⟩ : syracuseStep 1629059 = 2443589) B2443589
theorem B1629075 : Blo 1628513 1629075 := bstep (se 1 (by rfl) ⟨1221806, by rfl⟩ : syracuseStep 1629075 = 2443613) B2443613
theorem B1629091 : Blo 1628513 1629091 := bstep (se 1 (by rfl) ⟨1221818, by rfl⟩ : syracuseStep 1629091 = 2443637) B2443637
theorem B1629107 : Blo 1628513 1629107 := bstep (se 1 (by rfl) ⟨1221830, by rfl⟩ : syracuseStep 1629107 = 2443661) B2443661
theorem B1833907 : Blo 1628513 1833907 := bstep (se 1 (by rfl) ⟨1375430, by rfl⟩ : syracuseStep 1833907 = 2750861) B2750861
theorem B1629123 : Blo 1628513 1629123 := bstep (se 1 (by rfl) ⟨1221842, by rfl⟩ : syracuseStep 1629123 = 2443685) B2443685
theorem B12884933 : Blo 1628513 12884933 := bstep (se 4 (by rfl) ⟨1207962, by rfl⟩ : syracuseStep 12884933 = 2415925) B2415925
theorem B1629139 : Blo 1628513 1629139 := bstep (se 1 (by rfl) ⟨1221854, by rfl⟩ : syracuseStep 1629139 = 2443709) B2443709
theorem B1629155 : Blo 1628513 1629155 := bstep (se 1 (by rfl) ⟨1221866, by rfl⟩ : syracuseStep 1629155 = 2443733) B2443733
theorem B1629171 : Blo 1628513 1629171 := bstep (se 1 (by rfl) ⟨1221878, by rfl⟩ : syracuseStep 1629171 = 2443757) B2443757
theorem B2751475 : Blo 1628513 2751475 := bstep (se 1 (by rfl) ⟨2063606, by rfl⟩ : syracuseStep 2751475 = 4127213) B4127213
theorem B1629187 : Blo 1628513 1629187 := bstep (se 1 (by rfl) ⟨1221890, by rfl⟩ : syracuseStep 1629187 = 2443781) B2443781
theorem B1629203 : Blo 1628513 1629203 := bstep (se 1 (by rfl) ⟨1221902, by rfl⟩ : syracuseStep 1629203 = 2443805) B2443805
theorem B6183971 : Blo 1628513 6183971 := bstep (se 1 (by rfl) ⟨4637978, by rfl⟩ : syracuseStep 6183971 = 9275957) B9275957
theorem B1629219 : Blo 1628513 1629219 := bstep (se 1 (by rfl) ⟨1221914, by rfl⟩ : syracuseStep 1629219 = 2443829) B2443829
theorem B6183985 : Blo 1628513 6183985 := bstep (se 2 (by rfl) ⟨2318994, by rfl⟩ : syracuseStep 6183985 = 4637989) B4637989
theorem B1629235 : Blo 1628513 1629235 := bstep (se 1 (by rfl) ⟨1221926, by rfl⟩ : syracuseStep 1629235 = 2443853) B2443853
theorem B25426997 : Blo 1628513 25426997 := bstep (se 5 (by rfl) ⟨1191890, by rfl⟩ : syracuseStep 25426997 = 2383781) B2383781
theorem B1629251 : Blo 1628513 1629251 := bstep (se 1 (by rfl) ⟨1221938, by rfl⟩ : syracuseStep 1629251 = 2443877) B2443877
theorem B1834051 : Blo 1628513 1834051 := bstep (se 1 (by rfl) ⟨1375538, by rfl⟩ : syracuseStep 1834051 = 2751077) B2751077
theorem B3914833 : Blo 1628513 3914833 := bstep (se 2 (by rfl) ⟨1468062, by rfl⟩ : syracuseStep 3914833 = 2936125) B2936125
theorem B1629267 : Blo 1628513 1629267 := bstep (se 1 (by rfl) ⟨1221950, by rfl⟩ : syracuseStep 1629267 = 2443901) B2443901
theorem B1629283 : Blo 1628513 1629283 := bstep (se 1 (by rfl) ⟨1221962, by rfl⟩ : syracuseStep 1629283 = 2443925) B2443925
theorem B1629299 : Blo 1628513 1629299 := bstep (se 1 (by rfl) ⟨1221974, by rfl⟩ : syracuseStep 1629299 = 2443949) B2443949
theorem B1629315 : Blo 1628513 1629315 := bstep (se 1 (by rfl) ⟨1221986, by rfl⟩ : syracuseStep 1629315 = 2443973) B2443973
theorem B1629331 : Blo 1628513 1629331 := bstep (se 1 (by rfl) ⟨1221998, by rfl⟩ : syracuseStep 1629331 = 2443997) B2443997
theorem B1629347 : Blo 1628513 1629347 := bstep (se 1 (by rfl) ⟨1222010, by rfl⟩ : syracuseStep 1629347 = 2444021) B2444021
theorem B1629363 : Blo 1628513 1629363 := bstep (se 1 (by rfl) ⟨1222022, by rfl⟩ : syracuseStep 1629363 = 2444045) B2444045
theorem B1629379 : Blo 1628513 1629379 := bstep (se 1 (by rfl) ⟨1222034, by rfl⟩ : syracuseStep 1629379 = 2444069) B2444069
theorem B1629395 : Blo 1628513 1629395 := bstep (se 1 (by rfl) ⟨1222046, by rfl⟩ : syracuseStep 1629395 = 2444093) B2444093
theorem B1834195 : Blo 1628513 1834195 := bstep (se 1 (by rfl) ⟨1375646, by rfl⟩ : syracuseStep 1834195 = 2751293) B2751293
theorem B1629411 : Blo 1628513 1629411 := bstep (se 1 (by rfl) ⟨1222058, by rfl⟩ : syracuseStep 1629411 = 2444117) B2444117
theorem B1629427 : Blo 1628513 1629427 := bstep (se 1 (by rfl) ⟨1222070, by rfl⟩ : syracuseStep 1629427 = 2444141) B2444141
theorem B1629443 : Blo 1628513 1629443 := bstep (se 1 (by rfl) ⟨1222082, by rfl⟩ : syracuseStep 1629443 = 2444165) B2444165
theorem B3767555 : Blo 1628513 3767555 := bstep (se 1 (by rfl) ⟨2825666, by rfl⟩ : syracuseStep 3767555 = 5651333) B5651333
theorem B1629459 : Blo 1628513 1629459 := bstep (se 1 (by rfl) ⟨1222094, by rfl⟩ : syracuseStep 1629459 = 2444189) B2444189
theorem B1629475 : Blo 1628513 1629475 := bstep (se 1 (by rfl) ⟨1222106, by rfl⟩ : syracuseStep 1629475 = 2444213) B2444213
theorem B1629491 : Blo 1628513 1629491 := bstep (se 1 (by rfl) ⟨1222118, by rfl⟩ : syracuseStep 1629491 = 2444237) B2444237
theorem B1629507 : Blo 1628513 1629507 := bstep (se 1 (by rfl) ⟨1222130, by rfl⟩ : syracuseStep 1629507 = 2444261) B2444261
theorem B6610253 : Blo 1628513 6610253 := bstep (se 3 (by rfl) ⟨1239422, by rfl⟩ : syracuseStep 6610253 = 2478845) B2478845
theorem B1629523 : Blo 1628513 1629523 := bstep (se 1 (by rfl) ⟨1222142, by rfl⟩ : syracuseStep 1629523 = 2444285) B2444285
theorem B4406609 : Blo 1628513 4406609 := bstep (se 2 (by rfl) ⟨1652478, by rfl⟩ : syracuseStep 4406609 = 3304957) B3304957
theorem B1629539 : Blo 1628513 1629539 := bstep (se 1 (by rfl) ⟨1222154, by rfl⟩ : syracuseStep 1629539 = 2444309) B2444309
theorem B4955501 : Blo 1628513 4955501 := bstep (se 3 (by rfl) ⟨929156, by rfl⟩ : syracuseStep 4955501 = 1858313) B1858313
theorem B1629555 : Blo 1628513 1629555 := bstep (se 1 (by rfl) ⟨1222166, by rfl⟩ : syracuseStep 1629555 = 2444333) B2444333
theorem B1629571 : Blo 1628513 1629571 := bstep (se 1 (by rfl) ⟨1222178, by rfl⟩ : syracuseStep 1629571 = 2444357) B2444357
theorem B1957267 : Blo 1628513 1957267 := bstep (se 1 (by rfl) ⟨1467950, by rfl⟩ : syracuseStep 1957267 = 2935901) B2935901
theorem B1629587 : Blo 1628513 1629587 := bstep (se 1 (by rfl) ⟨1222190, by rfl⟩ : syracuseStep 1629587 = 2444381) B2444381
theorem B1629603 : Blo 1628513 1629603 := bstep (se 1 (by rfl) ⟨1222202, by rfl⟩ : syracuseStep 1629603 = 2444405) B2444405
theorem B1629619 : Blo 1628513 1629619 := bstep (se 1 (by rfl) ⟨1222214, by rfl⟩ : syracuseStep 1629619 = 2444429) B2444429
theorem B1629635 : Blo 1628513 1629635 := bstep (se 1 (by rfl) ⟨1222226, by rfl⟩ : syracuseStep 1629635 = 2444453) B2444453
theorem B1629651 : Blo 1628513 1629651 := bstep (se 1 (by rfl) ⟨1222238, by rfl⟩ : syracuseStep 1629651 = 2444477) B2444477
theorem B7429603 : Blo 1628513 7429603 := bstep (se 1 (by rfl) ⟨5572202, by rfl⟩ : syracuseStep 7429603 = 11144405) B11144405
theorem B1629667 : Blo 1628513 1629667 := bstep (se 1 (by rfl) ⟨1222250, by rfl⟩ : syracuseStep 1629667 = 2444501) B2444501
theorem B1629683 : Blo 1628513 1629683 := bstep (se 1 (by rfl) ⟨1222262, by rfl⟩ : syracuseStep 1629683 = 2444525) B2444525
theorem B1629699 : Blo 1628513 1629699 := bstep (se 1 (by rfl) ⟨1222274, by rfl⟩ : syracuseStep 1629699 = 2444549) B2444549
theorem B1629715 : Blo 1628513 1629715 := bstep (se 1 (by rfl) ⟨1222286, by rfl⟩ : syracuseStep 1629715 = 2444573) B2444573
theorem B1629731 : Blo 1628513 1629731 := bstep (se 1 (by rfl) ⟨1222298, by rfl⟩ : syracuseStep 1629731 = 2444597) B2444597
theorem B1629747 : Blo 1628513 1629747 := bstep (se 1 (by rfl) ⟨1222310, by rfl⟩ : syracuseStep 1629747 = 2444621) B2444621
theorem B1629763 : Blo 1628513 1629763 := bstep (se 1 (by rfl) ⟨1222322, by rfl⟩ : syracuseStep 1629763 = 2444645) B2444645
theorem B1629779 : Blo 1628513 1629779 := bstep (se 1 (by rfl) ⟨1222334, by rfl⟩ : syracuseStep 1629779 = 2444669) B2444669
theorem B1629795 : Blo 1628513 1629795 := bstep (se 1 (by rfl) ⟨1222346, by rfl⟩ : syracuseStep 1629795 = 2444693) B2444693
theorem B1629811 : Blo 1628513 1629811 := bstep (se 1 (by rfl) ⟨1222358, by rfl⟩ : syracuseStep 1629811 = 2444717) B2444717
theorem B1629827 : Blo 1628513 1629827 := bstep (se 1 (by rfl) ⟨1222370, by rfl⟩ : syracuseStep 1629827 = 2444741) B2444741
theorem B1629843 : Blo 1628513 1629843 := bstep (se 1 (by rfl) ⟨1222382, by rfl⟩ : syracuseStep 1629843 = 2444765) B2444765
theorem B1629859 : Blo 1628513 1629859 := bstep (se 1 (by rfl) ⟨1222394, by rfl⟩ : syracuseStep 1629859 = 2444789) B2444789
theorem B4406957 : Blo 1628513 4406957 := bstep (se 3 (by rfl) ⟨826304, by rfl⟩ : syracuseStep 4406957 = 1652609) B1652609
theorem B5496497 : Blo 1628513 5496497 := bstep (se 2 (by rfl) ⟨2061186, by rfl⟩ : syracuseStep 5496497 = 4122373) B4122373
theorem B10436273 : Blo 1628513 10436273 := bstep (se 2 (by rfl) ⟨3913602, by rfl⟩ : syracuseStep 10436273 = 7827205) B7827205
theorem B1629875 : Blo 1628513 1629875 := bstep (se 1 (by rfl) ⟨1222406, by rfl⟩ : syracuseStep 1629875 = 2444813) B2444813
theorem B1629891 : Blo 1628513 1629891 := bstep (se 1 (by rfl) ⟨1222418, by rfl⟩ : syracuseStep 1629891 = 2444837) B2444837
theorem B1629907 : Blo 1628513 1629907 := bstep (se 1 (by rfl) ⟨1222430, by rfl⟩ : syracuseStep 1629907 = 2444861) B2444861
theorem B19816163 : Blo 1628513 19816163 := bstep (se 1 (by rfl) ⟨14862122, by rfl⟩ : syracuseStep 19816163 = 29724245) B29724245
theorem B1629923 : Blo 1628513 1629923 := bstep (se 1 (by rfl) ⟨1222442, by rfl⟩ : syracuseStep 1629923 = 2444885) B2444885
theorem B1629939 : Blo 1628513 1629939 := bstep (se 1 (by rfl) ⟨1222454, by rfl⟩ : syracuseStep 1629939 = 2444909) B2444909
theorem B1629955 : Blo 1628513 1629955 := bstep (se 1 (by rfl) ⟨1222466, by rfl⟩ : syracuseStep 1629955 = 2444933) B2444933
theorem B1629971 : Blo 1628513 1629971 := bstep (se 1 (by rfl) ⟨1222478, by rfl⟩ : syracuseStep 1629971 = 2444957) B2444957
theorem B1629987 : Blo 1628513 1629987 := bstep (se 1 (by rfl) ⟨1222490, by rfl⟩ : syracuseStep 1629987 = 2444981) B2444981
theorem B1630003 : Blo 1628513 1630003 := bstep (se 1 (by rfl) ⟨1222502, by rfl⟩ : syracuseStep 1630003 = 2445005) B2445005
theorem B1630019 : Blo 1628513 1630019 := bstep (se 1 (by rfl) ⟨1222514, by rfl⟩ : syracuseStep 1630019 = 2445029) B2445029
theorem B1630035 : Blo 1628513 1630035 := bstep (se 1 (by rfl) ⟨1222526, by rfl⟩ : syracuseStep 1630035 = 2445053) B2445053
theorem B1630051 : Blo 1628513 1630051 := bstep (se 1 (by rfl) ⟨1222538, by rfl⟩ : syracuseStep 1630051 = 2445077) B2445077
theorem B4407139 : Blo 1628513 4407139 := bstep (se 1 (by rfl) ⟨3305354, by rfl⟩ : syracuseStep 4407139 = 6610709) B6610709
theorem B8249201 : Blo 1628513 8249201 := bstep (se 2 (by rfl) ⟨3093450, by rfl⟩ : syracuseStep 8249201 = 6186901) B6186901
theorem B1630067 : Blo 1628513 1630067 := bstep (se 1 (by rfl) ⟨1222550, by rfl⟩ : syracuseStep 1630067 = 2445101) B2445101
theorem B1630083 : Blo 1628513 1630083 := bstep (se 1 (by rfl) ⟨1222562, by rfl⟩ : syracuseStep 1630083 = 2445125) B2445125
theorem B1630099 : Blo 1628513 1630099 := bstep (se 1 (by rfl) ⟨1222574, by rfl⟩ : syracuseStep 1630099 = 2445149) B2445149
theorem B1630115 : Blo 1628513 1630115 := bstep (se 1 (by rfl) ⟨1222586, by rfl⟩ : syracuseStep 1630115 = 2445173) B2445173
theorem B1630131 : Blo 1628513 1630131 := bstep (se 1 (by rfl) ⟨1222598, by rfl⟩ : syracuseStep 1630131 = 2445197) B2445197
theorem B1630147 : Blo 1628513 1630147 := bstep (se 1 (by rfl) ⟨1222610, by rfl⟩ : syracuseStep 1630147 = 2445221) B2445221
theorem B1630163 : Blo 1628513 1630163 := bstep (se 1 (by rfl) ⟨1222622, by rfl⟩ : syracuseStep 1630163 = 2445245) B2445245
theorem B1630179 : Blo 1628513 1630179 := bstep (se 1 (by rfl) ⟨1222634, by rfl⟩ : syracuseStep 1630179 = 2445269) B2445269
theorem B1630195 : Blo 1628513 1630195 := bstep (se 1 (by rfl) ⟨1222646, by rfl⟩ : syracuseStep 1630195 = 2445293) B2445293
theorem B3137537 : Blo 1628513 3137537 := bstep (se 2 (by rfl) ⟨1176576, by rfl⟩ : syracuseStep 3137537 = 2353153) B2353153
theorem B1630219 : Blo 1628513 1630219 := bstep (se 1 (by rfl) ⟨1222664, by rfl⟩ : syracuseStep 1630219 = 2445329) B2445329
theorem B1630231 : Blo 1628513 1630231 := bstep (se 1 (by rfl) ⟨1222673, by rfl⟩ : syracuseStep 1630231 = 2445347) B2445347
theorem B1630251 : Blo 1628513 1630251 := bstep (se 1 (by rfl) ⟨1222688, by rfl⟩ : syracuseStep 1630251 = 2445377) B2445377
theorem B1630263 : Blo 1628513 1630263 := bstep (se 1 (by rfl) ⟨1222697, by rfl⟩ : syracuseStep 1630263 = 2445395) B2445395
theorem B1630283 : Blo 1628513 1630283 := bstep (se 1 (by rfl) ⟨1222712, by rfl⟩ : syracuseStep 1630283 = 2445425) B2445425
theorem B1630295 : Blo 1628513 1630295 := bstep (se 1 (by rfl) ⟨1222721, by rfl⟩ : syracuseStep 1630295 = 2445443) B2445443
theorem B1630315 : Blo 1628513 1630315 := bstep (se 1 (by rfl) ⟨1222736, by rfl⟩ : syracuseStep 1630315 = 2445473) B2445473
theorem B1630327 : Blo 1628513 1630327 := bstep (se 1 (by rfl) ⟨1222745, by rfl⟩ : syracuseStep 1630327 = 2445491) B2445491
theorem B1630347 : Blo 1628513 1630347 := bstep (se 1 (by rfl) ⟨1222760, by rfl⟩ : syracuseStep 1630347 = 2445521) B2445521
theorem B5496983 : Blo 1628513 5496983 := bstep (se 1 (by rfl) ⟨4122737, by rfl⟩ : syracuseStep 5496983 = 8245475) B8245475
theorem B10436759 : Blo 1628513 10436759 := bstep (se 1 (by rfl) ⟨7827569, by rfl⟩ : syracuseStep 10436759 = 15655139) B15655139
theorem B1630359 : Blo 1628513 1630359 := bstep (se 1 (by rfl) ⟨1222769, by rfl⟩ : syracuseStep 1630359 = 2445539) B2445539
theorem B1630379 : Blo 1628513 1630379 := bstep (se 1 (by rfl) ⟨1222784, by rfl⟩ : syracuseStep 1630379 = 2445569) B2445569
theorem B1630391 : Blo 1628513 1630391 := bstep (se 1 (by rfl) ⟨1222793, by rfl⟩ : syracuseStep 1630391 = 2445587) B2445587
theorem B1630411 : Blo 1628513 1630411 := bstep (se 1 (by rfl) ⟨1222808, by rfl⟩ : syracuseStep 1630411 = 2445617) B2445617
theorem B1630423 : Blo 1628513 1630423 := bstep (se 1 (by rfl) ⟨1222817, by rfl⟩ : syracuseStep 1630423 = 2445635) B2445635
theorem B5292253 : Blo 1628513 5292253 := bstep (se 3 (by rfl) ⟨992297, by rfl⟩ : syracuseStep 5292253 = 1984595) B1984595
theorem B1630443 : Blo 1628513 1630443 := bstep (se 1 (by rfl) ⟨1222832, by rfl⟩ : syracuseStep 1630443 = 2445665) B2445665
theorem B1630455 : Blo 1628513 1630455 := bstep (se 1 (by rfl) ⟨1222841, by rfl⟩ : syracuseStep 1630455 = 2445683) B2445683
theorem B1630475 : Blo 1628513 1630475 := bstep (se 1 (by rfl) ⟨1222856, by rfl⟩ : syracuseStep 1630475 = 2445713) B2445713
theorem B1630487 : Blo 1628513 1630487 := bstep (se 1 (by rfl) ⟨1222865, by rfl⟩ : syracuseStep 1630487 = 2445731) B2445731
theorem B1630507 : Blo 1628513 1630507 := bstep (se 1 (by rfl) ⟨1222880, by rfl⟩ : syracuseStep 1630507 = 2445761) B2445761
theorem B6185261 : Blo 1628513 6185261 := bstep (se 3 (by rfl) ⟨1159736, by rfl⟩ : syracuseStep 6185261 = 2319473) B2319473
theorem B6963545 : Blo 1628513 6963545 := bstep (se 2 (by rfl) ⟨2611329, by rfl⟩ : syracuseStep 6963545 = 5222659) B5222659
theorem B19825073 : Blo 1628513 19825073 := bstep (se 2 (by rfl) ⟨7434402, by rfl⟩ : syracuseStep 19825073 = 14868805) B14868805
theorem B2318807 : Blo 1628513 2318807 := bstep (se 1 (by rfl) ⟨1739105, by rfl⟩ : syracuseStep 2318807 = 3478211) B3478211
theorem B20873821 : Blo 1628513 20873821 := bstep (se 3 (by rfl) ⟨3913841, by rfl⟩ : syracuseStep 20873821 = 7827683) B7827683
theorem B2351767 : Blo 1628513 2351767 := bstep (se 1 (by rfl) ⟨1763825, by rfl⟩ : syracuseStep 2351767 = 3527651) B3527651
theorem B5497523 : Blo 1628513 5497523 := bstep (se 1 (by rfl) ⟨4123142, by rfl⟩ : syracuseStep 5497523 = 8246285) B8246285
theorem B5497793 : Blo 1628513 5497793 := bstep (se 2 (by rfl) ⟨2061672, by rfl⟩ : syracuseStep 5497793 = 4123345) B4123345
theorem B2974963 : Blo 1628513 2974963 := bstep (se 1 (by rfl) ⟨2231222, by rfl⟩ : syracuseStep 2974963 = 4462445) B4462445
theorem B3015937 : Blo 1628513 3015937 := bstep (se 2 (by rfl) ⟨1130976, by rfl⟩ : syracuseStep 3015937 = 2261953) B2261953
theorem B5219635 : Blo 1628513 5219635 := bstep (se 1 (by rfl) ⟨3914726, by rfl⟩ : syracuseStep 5219635 = 7829453) B7829453
theorem B2319769 : Blo 1628513 2319769 := bstep (se 2 (by rfl) ⟨869913, by rfl⟩ : syracuseStep 2319769 = 1739827) B1739827
theorem B9282995 : Blo 1628513 9282995 := bstep (se 1 (by rfl) ⟨6962246, by rfl⟩ : syracuseStep 9282995 = 13924493) B13924493
theorem B5219777 : Blo 1628513 5219777 := bstep (se 2 (by rfl) ⟨1957416, by rfl⟩ : syracuseStep 5219777 = 3914833) B3914833
theorem B5498333 : Blo 1628513 5498333 := bstep (se 3 (by rfl) ⟨1030937, by rfl⟩ : syracuseStep 5498333 = 2061875) B2061875
theorem B59442659 : Blo 1628513 59442659 := bstep (se 1 (by rfl) ⟨44581994, by rfl⟩ : syracuseStep 59442659 = 89163989) B89163989
theorem B39642641 : Blo 1628513 39642641 := bstep (se 2 (by rfl) ⟨14865990, by rfl⟩ : syracuseStep 39642641 = 29731981) B29731981
theorem B5219891 : Blo 1628513 5219891 := bstep (se 1 (by rfl) ⟨3914918, by rfl⟩ : syracuseStep 5219891 = 7829837) B7829837
theorem B2442827 : Blo 1628513 2442827 := bstep (se 1 (by rfl) ⟨1832120, by rfl⟩ : syracuseStep 2442827 = 3664241) B3664241
theorem B2442839 : Blo 1628513 2442839 := bstep (se 1 (by rfl) ⟨1832129, by rfl⟩ : syracuseStep 2442839 = 3664259) B3664259
theorem B2442905 : Blo 1628513 2442905 := bstep (se 2 (by rfl) ⟨916089, by rfl⟩ : syracuseStep 2442905 = 1832179) B1832179
theorem B6186689 : Blo 1628513 6186689 := bstep (se 2 (by rfl) ⟨2320008, by rfl⟩ : syracuseStep 6186689 = 4640017) B4640017
theorem B2443019 : Blo 1628513 2443019 := bstep (se 1 (by rfl) ⟨1832264, by rfl⟩ : syracuseStep 2443019 = 3664529) B3664529
theorem B2443031 : Blo 1628513 2443031 := bstep (se 1 (by rfl) ⟨1832273, by rfl⟩ : syracuseStep 2443031 = 3664547) B3664547
theorem B6358859 : Blo 1628513 6358859 := bstep (se 1 (by rfl) ⟨4769144, by rfl⟩ : syracuseStep 6358859 = 9538289) B9538289
theorem B2443097 : Blo 1628513 2443097 := bstep (se 2 (by rfl) ⟨916161, by rfl⟩ : syracuseStep 2443097 = 1832323) B1832323
theorem B6604723 : Blo 1628513 6604723 := bstep (se 1 (by rfl) ⟨4953542, by rfl⟩ : syracuseStep 6604723 = 9907085) B9907085
theorem B2443211 : Blo 1628513 2443211 := bstep (se 1 (by rfl) ⟨1832408, by rfl⟩ : syracuseStep 2443211 = 3664817) B3664817
theorem B2443223 : Blo 1628513 2443223 := bstep (se 1 (by rfl) ⟨1832417, by rfl⟩ : syracuseStep 2443223 = 3664835) B3664835
theorem B9906137 : Blo 1628513 9906137 := bstep (se 2 (by rfl) ⟨3714801, by rfl⟩ : syracuseStep 9906137 = 7429603) B7429603
theorem B4122647 : Blo 1628513 4122647 := bstep (se 1 (by rfl) ⟨3091985, by rfl⟩ : syracuseStep 4122647 = 6183971) B6183971
theorem B2443289 : Blo 1628513 2443289 := bstep (se 2 (by rfl) ⟨916233, by rfl⟩ : syracuseStep 2443289 = 1832467) B1832467
theorem B16951331 : Blo 1628513 16951331 := bstep (se 1 (by rfl) ⟨12713498, by rfl⟩ : syracuseStep 16951331 = 25426997) B25426997
theorem B21170251 : Blo 1628513 21170251 := bstep (se 1 (by rfl) ⟨15877688, by rfl⟩ : syracuseStep 21170251 = 31755377) B31755377
theorem B39651403 : Blo 1628513 39651403 := bstep (se 1 (by rfl) ⟨29738552, by rfl⟩ : syracuseStep 39651403 = 59477105) B59477105
theorem B4638809 : Blo 1628513 4638809 := bstep (se 2 (by rfl) ⟨1739553, by rfl⟩ : syracuseStep 4638809 = 3479107) B3479107
theorem B10438757 : Blo 1628513 10438757 := bstep (se 4 (by rfl) ⟨978633, by rfl⟩ : syracuseStep 10438757 = 1957267) B1957267
theorem B2443403 : Blo 1628513 2443403 := bstep (se 1 (by rfl) ⟨1832552, by rfl⟩ : syracuseStep 2443403 = 3665105) B3665105
theorem B2443415 : Blo 1628513 2443415 := bstep (se 1 (by rfl) ⟨1832561, by rfl⟩ : syracuseStep 2443415 = 3665123) B3665123
theorem B2443481 : Blo 1628513 2443481 := bstep (se 2 (by rfl) ⟨916305, by rfl⟩ : syracuseStep 2443481 = 1832611) B1832611
theorem B3303667 : Blo 1628513 3303667 := bstep (se 1 (by rfl) ⟨2477750, by rfl⟩ : syracuseStep 3303667 = 4955501) B4955501
theorem B2443595 : Blo 1628513 2443595 := bstep (se 1 (by rfl) ⟨1832696, by rfl⟩ : syracuseStep 2443595 = 3665393) B3665393
theorem B2443607 : Blo 1628513 2443607 := bstep (se 1 (by rfl) ⟨1832705, by rfl⟩ : syracuseStep 2443607 = 3665411) B3665411
theorem B2443673 : Blo 1628513 2443673 := bstep (se 2 (by rfl) ⟨916377, by rfl⟩ : syracuseStep 2443673 = 1832755) B1832755
theorem B3664331 : Blo 1628513 3664331 := bstep (se 1 (by rfl) ⟨2748248, by rfl⟩ : syracuseStep 3664331 = 5496497) B5496497
theorem B6957515 : Blo 1628513 6957515 := bstep (se 1 (by rfl) ⟨5218136, by rfl⟩ : syracuseStep 6957515 = 10436273) B10436273
theorem B22309337 : Blo 1628513 22309337 := bstep (se 2 (by rfl) ⟨8366001, by rfl⟩ : syracuseStep 22309337 = 16732003) B16732003
theorem B5876185 : Blo 1628513 5876185 := bstep (se 2 (by rfl) ⟨2203569, by rfl⟩ : syracuseStep 5876185 = 4407139) B4407139
theorem B3664385 : Blo 1628513 3664385 := bstep (se 2 (by rfl) ⟨1374144, by rfl⟩ : syracuseStep 3664385 = 2748289) B2748289
theorem B2443787 : Blo 1628513 2443787 := bstep (se 1 (by rfl) ⟨1832840, by rfl⟩ : syracuseStep 2443787 = 3665681) B3665681
theorem B34359821 : Blo 1628513 34359821 := bstep (se 3 (by rfl) ⟨6442466, by rfl⟩ : syracuseStep 34359821 = 12884933) B12884933
theorem B2443799 : Blo 1628513 2443799 := bstep (se 1 (by rfl) ⟨1832849, by rfl⟩ : syracuseStep 2443799 = 3665699) B3665699
theorem B5499467 : Blo 1628513 5499467 := bstep (se 1 (by rfl) ⟨4124600, by rfl⟩ : syracuseStep 5499467 = 8249201) B8249201
theorem B19335755 : Blo 1628513 19335755 := bstep (se 1 (by rfl) ⟨14501816, by rfl⟩ : syracuseStep 19335755 = 29003633) B29003633
theorem B2443865 : Blo 1628513 2443865 := bstep (se 2 (by rfl) ⟨916449, by rfl⟩ : syracuseStep 2443865 = 1832899) B1832899
theorem B12380849 : Blo 1628513 12380849 := bstep (se 2 (by rfl) ⟨4642818, by rfl⟩ : syracuseStep 12380849 = 9285637) B9285637
theorem B2443979 : Blo 1628513 2443979 := bstep (se 1 (by rfl) ⟨1832984, by rfl⟩ : syracuseStep 2443979 = 3665969) B3665969
theorem B2443991 : Blo 1628513 2443991 := bstep (se 1 (by rfl) ⟨1832993, by rfl⟩ : syracuseStep 2443991 = 3665987) B3665987
theorem B3664601 : Blo 1628513 3664601 := bstep (se 2 (by rfl) ⟨1374225, by rfl⟩ : syracuseStep 3664601 = 2748451) B2748451
theorem B2444057 : Blo 1628513 2444057 := bstep (se 2 (by rfl) ⟨916521, by rfl⟩ : syracuseStep 2444057 = 1833043) B1833043
theorem B4401971 : Blo 1628513 4401971 := bstep (se 1 (by rfl) ⟨3301478, by rfl⟩ : syracuseStep 4401971 = 6602957) B6602957
theorem B3664691 : Blo 1628513 3664691 := bstep (se 1 (by rfl) ⟨2748518, by rfl⟩ : syracuseStep 3664691 = 5497037) B5497037
theorem B4123457 : Blo 1628513 4123457 := bstep (se 2 (by rfl) ⟨1546296, by rfl⟩ : syracuseStep 4123457 = 3092593) B3092593
theorem B2321227 : Blo 1628513 2321227 := bstep (se 1 (by rfl) ⟨1740920, by rfl⟩ : syracuseStep 2321227 = 3481841) B3481841
theorem B3664727 : Blo 1628513 3664727 := bstep (se 1 (by rfl) ⟨2748545, by rfl⟩ : syracuseStep 3664727 = 5497091) B5497091
theorem B2321239 : Blo 1628513 2321239 := bstep (se 1 (by rfl) ⟨1740929, by rfl⟩ : syracuseStep 2321239 = 3481859) B3481859
theorem B5499737 : Blo 1628513 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B9284453 : Blo 1628513 9284453 := bstep (se 4 (by rfl) ⟨870417, by rfl⟩ : syracuseStep 9284453 = 1740835) B1740835
theorem B2444171 : Blo 1628513 2444171 := bstep (se 1 (by rfl) ⟨1833128, by rfl⟩ : syracuseStep 2444171 = 3666257) B3666257
theorem B2444183 : Blo 1628513 2444183 := bstep (se 1 (by rfl) ⟨1833137, by rfl⟩ : syracuseStep 2444183 = 3666275) B3666275
theorem B13388723 : Blo 1628513 13388723 := bstep (se 1 (by rfl) ⟨10041542, by rfl⟩ : syracuseStep 13388723 = 20083085) B20083085
theorem B2444249 : Blo 1628513 2444249 := bstep (se 2 (by rfl) ⟨916593, by rfl⟩ : syracuseStep 2444249 = 1833187) B1833187
theorem B1739755 : Blo 1628513 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B3664907 : Blo 1628513 3664907 := bstep (se 1 (by rfl) ⟨2748680, by rfl⟩ : syracuseStep 3664907 = 5497361) B5497361
theorem B7056407 : Blo 1628513 7056407 := bstep (se 1 (by rfl) ⟨5292305, by rfl⟩ : syracuseStep 7056407 = 10584611) B10584611
theorem B3664961 : Blo 1628513 3664961 := bstep (se 2 (by rfl) ⟨1374360, by rfl⟩ : syracuseStep 3664961 = 2748721) B2748721
theorem B2444363 : Blo 1628513 2444363 := bstep (se 1 (by rfl) ⟨1833272, by rfl⟩ : syracuseStep 2444363 = 3666545) B3666545
theorem B2444375 : Blo 1628513 2444375 := bstep (se 1 (by rfl) ⟨1833281, by rfl⟩ : syracuseStep 2444375 = 3666563) B3666563
theorem B6188177 : Blo 1628513 6188177 := bstep (se 2 (by rfl) ⟨2320566, by rfl⟩ : syracuseStep 6188177 = 4641133) B4641133
theorem B12381335 : Blo 1628513 12381335 := bstep (se 1 (by rfl) ⟨9286001, by rfl⟩ : syracuseStep 12381335 = 18572003) B18572003
theorem B2444441 : Blo 1628513 2444441 := bstep (se 2 (by rfl) ⟨916665, by rfl⟩ : syracuseStep 2444441 = 1833331) B1833331
theorem B2444555 : Blo 1628513 2444555 := bstep (se 1 (by rfl) ⟨1833416, by rfl⟩ : syracuseStep 2444555 = 3666833) B3666833
theorem B2444567 : Blo 1628513 2444567 := bstep (se 1 (by rfl) ⟨1833425, by rfl⟩ : syracuseStep 2444567 = 3666851) B3666851
theorem B3665177 : Blo 1628513 3665177 := bstep (se 2 (by rfl) ⟨1374441, by rfl⟩ : syracuseStep 3665177 = 2748883) B2748883
theorem B4640075 : Blo 1628513 4640075 := bstep (se 1 (by rfl) ⟨3480056, by rfl⟩ : syracuseStep 4640075 = 6960113) B6960113
theorem B4123993 : Blo 1628513 4123993 := bstep (se 2 (by rfl) ⟨1546497, by rfl⟩ : syracuseStep 4123993 = 3092995) B3092995
theorem B2444633 : Blo 1628513 2444633 := bstep (se 2 (by rfl) ⟨916737, by rfl⟩ : syracuseStep 2444633 = 1833475) B1833475
theorem B8252765 : Blo 1628513 8252765 := bstep (se 3 (by rfl) ⟨1547393, by rfl⟩ : syracuseStep 8252765 = 3094787) B3094787
theorem B3665267 : Blo 1628513 3665267 := bstep (se 1 (by rfl) ⟨2748950, by rfl⟩ : syracuseStep 3665267 = 5497901) B5497901
theorem B18550133 : Blo 1628513 18550133 := bstep (se 5 (by rfl) ⟨869537, by rfl⟩ : syracuseStep 18550133 = 1739075) B1739075
theorem B22310261 : Blo 1628513 22310261 := bstep (se 5 (by rfl) ⟨1045793, by rfl⟩ : syracuseStep 22310261 = 2091587) B2091587
theorem B3091841 : Blo 1628513 3091841 := bstep (se 2 (by rfl) ⟨1159440, by rfl⟩ : syracuseStep 3091841 = 2318881) B2318881
theorem B3665303 : Blo 1628513 3665303 := bstep (se 1 (by rfl) ⟨2748977, by rfl⟩ : syracuseStep 3665303 = 5497955) B5497955
theorem B6958487 : Blo 1628513 6958487 := bstep (se 1 (by rfl) ⟨5218865, by rfl⟩ : syracuseStep 6958487 = 10437731) B10437731
theorem B3059095 : Blo 1628513 3059095 := bstep (se 1 (by rfl) ⟨2294321, by rfl⟩ : syracuseStep 3059095 = 4588643) B4588643
theorem B5574091 : Blo 1628513 5574091 := bstep (se 1 (by rfl) ⟨4180568, by rfl⟩ : syracuseStep 5574091 = 8361137) B8361137
theorem B2444747 : Blo 1628513 2444747 := bstep (se 1 (by rfl) ⟨1833560, by rfl⟩ : syracuseStep 2444747 = 3667121) B3667121
theorem B2444759 : Blo 1628513 2444759 := bstep (se 1 (by rfl) ⟨1833569, by rfl⟩ : syracuseStep 2444759 = 3667139) B3667139
theorem B9276889 : Blo 1628513 9276889 := bstep (se 2 (by rfl) ⟨3478833, by rfl⟩ : syracuseStep 9276889 = 6957667) B6957667
theorem B9285137 : Blo 1628513 9285137 := bstep (se 2 (by rfl) ⟨3481926, by rfl⟩ : syracuseStep 9285137 = 6963853) B6963853
theorem B5500439 : Blo 1628513 5500439 := bstep (se 1 (by rfl) ⟨4125329, by rfl⟩ : syracuseStep 5500439 = 8250659) B8250659
theorem B2444825 : Blo 1628513 2444825 := bstep (se 2 (by rfl) ⟨916809, by rfl⟩ : syracuseStep 2444825 = 1833619) B1833619
theorem B11750957 : Blo 1628513 11750957 := bstep (se 3 (by rfl) ⟨2203304, by rfl⟩ : syracuseStep 11750957 = 4406609) B4406609
theorem B7835201 : Blo 1628513 7835201 := bstep (se 2 (by rfl) ⟨2938200, by rfl⟩ : syracuseStep 7835201 = 5876401) B5876401
theorem B3665483 : Blo 1628513 3665483 := bstep (se 1 (by rfl) ⟨2749112, by rfl⟩ : syracuseStep 3665483 = 5498225) B5498225
theorem B6188633 : Blo 1628513 6188633 := bstep (se 2 (by rfl) ⟨2320737, by rfl⟩ : syracuseStep 6188633 = 4641475) B4641475
theorem B11152997 : Blo 1628513 11152997 := bstep (se 4 (by rfl) ⟨1045593, by rfl⟩ : syracuseStep 11152997 = 2091187) B2091187
theorem B3665537 : Blo 1628513 3665537 := bstep (se 2 (by rfl) ⟨1374576, by rfl⟩ : syracuseStep 3665537 = 2749153) B2749153
theorem B3092107 : Blo 1628513 3092107 := bstep (se 1 (by rfl) ⟨2319080, by rfl⟩ : syracuseStep 3092107 = 4638161) B4638161
theorem B2444939 : Blo 1628513 2444939 := bstep (se 1 (by rfl) ⟨1833704, by rfl⟩ : syracuseStep 2444939 = 3667409) B3667409
theorem B2444951 : Blo 1628513 2444951 := bstep (se 1 (by rfl) ⟨1833713, by rfl⟩ : syracuseStep 2444951 = 3667427) B3667427
theorem B2445017 : Blo 1628513 2445017 := bstep (se 2 (by rfl) ⟨916881, by rfl⟩ : syracuseStep 2445017 = 1833763) B1833763
theorem B2936587 : Blo 1628513 2936587 := bstep (se 1 (by rfl) ⟨2202440, by rfl⟩ : syracuseStep 2936587 = 4404881) B4404881
theorem B6188845 : Blo 1628513 6188845 := bstep (se 3 (by rfl) ⟨1160408, by rfl⟩ : syracuseStep 6188845 = 2320817) B2320817
theorem B2748235 : Blo 1628513 2748235 := bstep (se 1 (by rfl) ⟨2061176, by rfl⟩ : syracuseStep 2748235 = 4122353) B4122353
theorem B2445131 : Blo 1628513 2445131 := bstep (se 1 (by rfl) ⟨1833848, by rfl⟩ : syracuseStep 2445131 = 3667697) B3667697
theorem B9916235 : Blo 1628513 9916235 := bstep (se 1 (by rfl) ⟨7437176, by rfl⟩ : syracuseStep 9916235 = 14874353) B14874353
theorem B2445143 : Blo 1628513 2445143 := bstep (se 1 (by rfl) ⟨1833857, by rfl⟩ : syracuseStep 2445143 = 3667715) B3667715
theorem B2608985 : Blo 1628513 2608985 := bstep (se 2 (by rfl) ⟨978369, by rfl⟩ : syracuseStep 2608985 = 1956739) B1956739
theorem B3665753 : Blo 1628513 3665753 := bstep (se 2 (by rfl) ⟨1374657, by rfl⟩ : syracuseStep 3665753 = 2749315) B2749315
theorem B2445209 : Blo 1628513 2445209 := bstep (se 2 (by rfl) ⟨916953, by rfl⟩ : syracuseStep 2445209 = 1833907) B1833907
theorem B3665843 : Blo 1628513 3665843 := bstep (se 1 (by rfl) ⟨2749382, by rfl⟩ : syracuseStep 3665843 = 5498765) B5498765
theorem B3665879 : Blo 1628513 3665879 := bstep (se 1 (by rfl) ⟨2749409, by rfl⟩ : syracuseStep 3665879 = 5498819) B5498819
theorem B2748377 : Blo 1628513 2748377 := bstep (se 2 (by rfl) ⟨1030641, by rfl⟩ : syracuseStep 2748377 = 2061283) B2061283
theorem B2445323 : Blo 1628513 2445323 := bstep (se 1 (by rfl) ⟨1833992, by rfl⟩ : syracuseStep 2445323 = 3667985) B3667985
theorem B2445335 : Blo 1628513 2445335 := bstep (se 1 (by rfl) ⟨1834001, by rfl⟩ : syracuseStep 2445335 = 3668003) B3668003
theorem B50147363 : Blo 1628513 50147363 := bstep (se 1 (by rfl) ⟨37610522, by rfl⟩ : syracuseStep 50147363 = 75221045) B75221045
theorem B11907107 : Blo 1628513 11907107 := bstep (se 1 (by rfl) ⟨8930330, by rfl⟩ : syracuseStep 11907107 = 17860661) B17860661
theorem B6959155 : Blo 1628513 6959155 := bstep (se 1 (by rfl) ⟨5219366, by rfl⟩ : syracuseStep 6959155 = 10438733) B10438733
theorem B5500979 : Blo 1628513 5500979 := bstep (se 1 (by rfl) ⟨4125734, by rfl⟩ : syracuseStep 5500979 = 8251469) B8251469
theorem B8245313 : Blo 1628513 8245313 := bstep (se 2 (by rfl) ⟨3091992, by rfl⟩ : syracuseStep 8245313 = 6183985) B6183985
theorem B3092555 : Blo 1628513 3092555 := bstep (se 1 (by rfl) ⟨2319416, by rfl⟩ : syracuseStep 3092555 = 4638833) B4638833
theorem B2748505 : Blo 1628513 2748505 := bstep (se 2 (by rfl) ⟨1030689, by rfl⟩ : syracuseStep 2748505 = 2061379) B2061379
theorem B2445401 : Blo 1628513 2445401 := bstep (se 2 (by rfl) ⟨917025, by rfl⟩ : syracuseStep 2445401 = 1834051) B1834051
theorem B6189149 : Blo 1628513 6189149 := bstep (se 3 (by rfl) ⟨1160465, by rfl⟩ : syracuseStep 6189149 = 2320931) B2320931
theorem B3666059 : Blo 1628513 3666059 := bstep (se 1 (by rfl) ⟨2749544, by rfl⟩ : syracuseStep 3666059 = 5499089) B5499089
theorem B7827607 : Blo 1628513 7827607 := bstep (se 1 (by rfl) ⟨5870705, by rfl⟩ : syracuseStep 7827607 = 11741411) B11741411
theorem B3666113 : Blo 1628513 3666113 := bstep (se 2 (by rfl) ⟨1374792, by rfl⟩ : syracuseStep 3666113 = 2749585) B2749585
theorem B2445515 : Blo 1628513 2445515 := bstep (se 1 (by rfl) ⟨1834136, by rfl⟩ : syracuseStep 2445515 = 3668273) B3668273
theorem B2445527 : Blo 1628513 2445527 := bstep (se 1 (by rfl) ⟨1834145, by rfl⟩ : syracuseStep 2445527 = 3668291) B3668291
theorem B3092737 : Blo 1628513 3092737 := bstep (se 2 (by rfl) ⟨1159776, by rfl⟩ : syracuseStep 3092737 = 2319553) B2319553
theorem B2445593 : Blo 1628513 2445593 := bstep (se 2 (by rfl) ⟨917097, by rfl⟩ : syracuseStep 2445593 = 1834195) B1834195
theorem B5501249 : Blo 1628513 5501249 := bstep (se 2 (by rfl) ⟨2062968, by rfl⟩ : syracuseStep 5501249 = 4125937) B4125937
theorem B15659365 : Blo 1628513 15659365 := bstep (se 4 (by rfl) ⟨1468065, by rfl⟩ : syracuseStep 15659365 = 2936131) B2936131
theorem B2445707 : Blo 1628513 2445707 := bstep (se 1 (by rfl) ⟨1834280, by rfl⟩ : syracuseStep 2445707 = 3668561) B3668561
theorem B9277847 : Blo 1628513 9277847 := bstep (se 1 (by rfl) ⟨6958385, by rfl⟩ : syracuseStep 9277847 = 13916771) B13916771
theorem B2445719 : Blo 1628513 2445719 := bstep (se 1 (by rfl) ⟨1834289, by rfl⟩ : syracuseStep 2445719 = 3668579) B3668579
theorem B3666329 : Blo 1628513 3666329 := bstep (se 2 (by rfl) ⟨1374873, by rfl⟩ : syracuseStep 3666329 = 2749747) B2749747
theorem B4125107 : Blo 1628513 4125107 := bstep (se 1 (by rfl) ⟨3093830, by rfl⟩ : syracuseStep 4125107 = 6187661) B6187661
theorem B17609177 : Blo 1628513 17609177 := bstep (se 2 (by rfl) ⟨6603441, by rfl⟩ : syracuseStep 17609177 = 13206883) B13206883
theorem B3666419 : Blo 1628513 3666419 := bstep (se 1 (by rfl) ⟨2749814, by rfl⟩ : syracuseStep 3666419 = 5499629) B5499629
theorem B75280913 : Blo 1628513 75280913 := bstep (se 2 (by rfl) ⟨28230342, by rfl⟩ : syracuseStep 75280913 = 56460685) B56460685
theorem B3666455 : Blo 1628513 3666455 := bstep (se 1 (by rfl) ⟨2749841, by rfl⟩ : syracuseStep 3666455 = 5499683) B5499683
theorem B3093079 : Blo 1628513 3093079 := bstep (se 1 (by rfl) ⟨2319809, by rfl⟩ : syracuseStep 3093079 = 4639619) B4639619
theorem B14873219 : Blo 1628513 14873219 := bstep (se 1 (by rfl) ⟨11154914, by rfl⟩ : syracuseStep 14873219 = 22309829) B22309829
theorem B2749079 : Blo 1628513 2749079 := bstep (se 1 (by rfl) ⟨2061809, by rfl⟩ : syracuseStep 2749079 = 4123619) B4123619
theorem B3666635 : Blo 1628513 3666635 := bstep (se 1 (by rfl) ⟨2749976, by rfl⟩ : syracuseStep 3666635 = 5499953) B5499953
theorem B29733581 : Blo 1628513 29733581 := bstep (se 3 (by rfl) ⟨5575046, by rfl⟩ : syracuseStep 29733581 = 11150093) B11150093
theorem B4125401 : Blo 1628513 4125401 := bstep (se 2 (by rfl) ⟨1547025, by rfl⟩ : syracuseStep 4125401 = 3094051) B3094051
theorem B3666689 : Blo 1628513 3666689 := bstep (se 2 (by rfl) ⟨1375008, by rfl⟩ : syracuseStep 3666689 = 2750017) B2750017
theorem B2749207 : Blo 1628513 2749207 := bstep (se 1 (by rfl) ⟨2061905, by rfl⟩ : syracuseStep 2749207 = 4123811) B4123811
theorem B3093299 : Blo 1628513 3093299 := bstep (se 1 (by rfl) ⟨2319974, by rfl⟩ : syracuseStep 3093299 = 4639949) B4639949
theorem B3715915 : Blo 1628513 3715915 := bstep (se 1 (by rfl) ⟨2786936, by rfl⟩ : syracuseStep 3715915 = 5573873) B5573873
theorem B2511703 : Blo 1628513 2511703 := bstep (se 1 (by rfl) ⟨1883777, by rfl⟩ : syracuseStep 2511703 = 3767555) B3767555
theorem B5501789 : Blo 1628513 5501789 := bstep (se 3 (by rfl) ⟨1031585, by rfl⟩ : syracuseStep 5501789 = 2063171) B2063171
theorem B3715969 : Blo 1628513 3715969 := bstep (se 2 (by rfl) ⟨1393488, by rfl⟩ : syracuseStep 3715969 = 2786977) B2786977
theorem B3666905 : Blo 1628513 3666905 := bstep (se 2 (by rfl) ⟨1375089, by rfl⟩ : syracuseStep 3666905 = 2750179) B2750179
theorem B13218821 : Blo 1628513 13218821 := bstep (se 4 (by rfl) ⟨1239264, by rfl⟩ : syracuseStep 13218821 = 2478529) B2478529
theorem B3093527 : Blo 1628513 3093527 := bstep (se 1 (by rfl) ⟨2320145, by rfl⟩ : syracuseStep 3093527 = 4640291) B4640291
theorem B3666995 : Blo 1628513 3666995 := bstep (se 1 (by rfl) ⟨2750246, by rfl⟩ : syracuseStep 3666995 = 5500493) B5500493
theorem B3667031 : Blo 1628513 3667031 := bstep (se 1 (by rfl) ⟨2750273, by rfl⟩ : syracuseStep 3667031 = 5500547) B5500547
theorem B2937971 : Blo 1628513 2937971 := bstep (se 1 (by rfl) ⟨2203478, by rfl⟩ : syracuseStep 2937971 = 4406957) B4406957
theorem B3716225 : Blo 1628513 3716225 := bstep (se 2 (by rfl) ⟨1393584, by rfl⟩ : syracuseStep 3716225 = 2787169) B2787169
theorem B13210775 : Blo 1628513 13210775 := bstep (se 1 (by rfl) ⟨9908081, by rfl⟩ : syracuseStep 13210775 = 19816163) B19816163
theorem B1832107 : Blo 1628513 1832107 := bstep (se 1 (by rfl) ⟨1374080, by rfl⟩ : syracuseStep 1832107 = 2748161) B2748161
theorem B1651915 : Blo 1628513 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B3667211 : Blo 1628513 3667211 := bstep (se 1 (by rfl) ⟨2750408, by rfl⟩ : syracuseStep 3667211 = 5500817) B5500817
theorem B6960401 : Blo 1628513 6960401 := bstep (se 2 (by rfl) ⟨2610150, by rfl⟩ : syracuseStep 6960401 = 5220301) B5220301
theorem B1832215 : Blo 1628513 1832215 := bstep (se 1 (by rfl) ⟨1374161, by rfl⟩ : syracuseStep 1832215 = 2748323) B2748323
theorem B3093785 : Blo 1628513 3093785 := bstep (se 2 (by rfl) ⟨1160169, by rfl⟩ : syracuseStep 3093785 = 2320339) B2320339
theorem B3667265 : Blo 1628513 3667265 := bstep (se 2 (by rfl) ⟨1375224, by rfl⟩ : syracuseStep 3667265 = 2750449) B2750449
theorem B2749835 : Blo 1628513 2749835 := bstep (se 1 (by rfl) ⟨2062376, by rfl⟩ : syracuseStep 2749835 = 4124753) B4124753
theorem B3478963 : Blo 1628513 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B1832395 : Blo 1628513 1832395 := bstep (se 1 (by rfl) ⟨1374296, by rfl⟩ : syracuseStep 1832395 = 2748593) B2748593
theorem B2749963 : Blo 1628513 2749963 := bstep (se 1 (by rfl) ⟨2062472, by rfl⟩ : syracuseStep 2749963 = 4124945) B4124945
theorem B3667481 : Blo 1628513 3667481 := bstep (se 2 (by rfl) ⟨1375305, by rfl⟩ : syracuseStep 3667481 = 2750611) B2750611
theorem B1832503 : Blo 1628513 1832503 := bstep (se 1 (by rfl) ⟨1374377, by rfl⟩ : syracuseStep 1832503 = 2748755) B2748755
theorem B3667571 : Blo 1628513 3667571 := bstep (se 1 (by rfl) ⟨2750678, by rfl⟩ : syracuseStep 3667571 = 5501357) B5501357
theorem B3667607 : Blo 1628513 3667607 := bstep (se 1 (by rfl) ⟨2750705, by rfl⟩ : syracuseStep 3667607 = 5501411) B5501411
theorem B2750105 : Blo 1628513 2750105 := bstep (se 2 (by rfl) ⟨1031289, by rfl⟩ : syracuseStep 2750105 = 2062579) B2062579
theorem B3094195 : Blo 1628513 3094195 := bstep (se 1 (by rfl) ⟨2320646, by rfl⟩ : syracuseStep 3094195 = 4641293) B4641293
theorem B2062027 : Blo 1628513 2062027 := bstep (se 1 (by rfl) ⟨1546520, by rfl⟩ : syracuseStep 2062027 = 3093041) B3093041
theorem B1832683 : Blo 1628513 1832683 := bstep (se 1 (by rfl) ⟨1374512, by rfl⟩ : syracuseStep 1832683 = 2749025) B2749025
theorem B2750233 : Blo 1628513 2750233 := bstep (se 2 (by rfl) ⟨1031337, by rfl⟩ : syracuseStep 2750233 = 2062675) B2062675
theorem B3667787 : Blo 1628513 3667787 := bstep (se 1 (by rfl) ⟨2750840, by rfl⟩ : syracuseStep 3667787 = 5501681) B5501681
theorem B1832791 : Blo 1628513 1832791 := bstep (se 1 (by rfl) ⟨1374593, by rfl⟩ : syracuseStep 1832791 = 2749187) B2749187
theorem B3667841 : Blo 1628513 3667841 := bstep (se 2 (by rfl) ⟨1375440, by rfl⟩ : syracuseStep 3667841 = 2750881) B2750881
theorem B14112643 : Blo 1628513 14112643 := bstep (se 1 (by rfl) ⟨10584482, by rfl⟩ : syracuseStep 14112643 = 21168965) B21168965
theorem B9402263 : Blo 1628513 9402263 := bstep (se 1 (by rfl) ⟨7051697, by rfl⟩ : syracuseStep 9402263 = 14103395) B14103395
theorem B3479449 : Blo 1628513 3479449 := bstep (se 2 (by rfl) ⟨1304793, by rfl⟩ : syracuseStep 3479449 = 2609587) B2609587
theorem B59488177 : Blo 1628513 59488177 := bstep (se 2 (by rfl) ⟨22308066, by rfl⟩ : syracuseStep 59488177 = 44616133) B44616133
theorem B5502923 : Blo 1628513 5502923 := bstep (se 1 (by rfl) ⟨4127192, by rfl⟩ : syracuseStep 5502923 = 8254385) B8254385
theorem B8247257 : Blo 1628513 8247257 := bstep (se 2 (by rfl) ⟨3092721, by rfl⟩ : syracuseStep 8247257 = 6185443) B6185443
theorem B1832971 : Blo 1628513 1832971 := bstep (se 1 (by rfl) ⟨1374728, by rfl⟩ : syracuseStep 1832971 = 2749457) B2749457
theorem B3717209 : Blo 1628513 3717209 := bstep (se 2 (by rfl) ⟨1393953, by rfl⟩ : syracuseStep 3717209 = 2787907) B2787907
theorem B3668057 : Blo 1628513 3668057 := bstep (se 2 (by rfl) ⟨1375521, by rfl⟩ : syracuseStep 3668057 = 2751043) B2751043
theorem B1833079 : Blo 1628513 1833079 := bstep (se 1 (by rfl) ⟨1374809, by rfl⟩ : syracuseStep 1833079 = 2749619) B2749619
theorem B3094681 : Blo 1628513 3094681 := bstep (se 2 (by rfl) ⟨1160505, by rfl⟩ : syracuseStep 3094681 = 2321011) B2321011
theorem B3668147 : Blo 1628513 3668147 := bstep (se 1 (by rfl) ⟨2751110, by rfl⟩ : syracuseStep 3668147 = 5502221) B5502221
theorem B17627341 : Blo 1628513 17627341 := bstep (se 3 (by rfl) ⟨3305126, by rfl⟩ : syracuseStep 17627341 = 6610253) B6610253
theorem B3668183 : Blo 1628513 3668183 := bstep (se 1 (by rfl) ⟨2751137, by rfl⟩ : syracuseStep 3668183 = 5502275) B5502275
theorem B1833259 : Blo 1628513 1833259 := bstep (se 1 (by rfl) ⟨1374944, by rfl⟩ : syracuseStep 1833259 = 2749889) B2749889
theorem B5577011 : Blo 1628513 5577011 := bstep (se 1 (by rfl) ⟨4182758, by rfl⟩ : syracuseStep 5577011 = 8365517) B8365517
theorem B4127051 : Blo 1628513 4127051 := bstep (se 1 (by rfl) ⟨3095288, by rfl⟩ : syracuseStep 4127051 = 6190577) B6190577
theorem B2750807 : Blo 1628513 2750807 := bstep (se 1 (by rfl) ⟨2063105, by rfl⟩ : syracuseStep 2750807 = 4126211) B4126211
theorem B1628523 : Blo 1628513 1628523 := bstep (se 1 (by rfl) ⟨1221392, by rfl⟩ : syracuseStep 1628523 = 2442785) B2442785
theorem B1628535 : Blo 1628513 1628535 := bstep (se 1 (by rfl) ⟨1221401, by rfl⟩ : syracuseStep 1628535 = 2442803) B2442803
theorem B1628555 : Blo 1628513 1628555 := bstep (se 1 (by rfl) ⟨1221416, by rfl⟩ : syracuseStep 1628555 = 2442833) B2442833
theorem B3668363 : Blo 1628513 3668363 := bstep (se 1 (by rfl) ⟨2751272, by rfl⟩ : syracuseStep 3668363 = 5502545) B5502545
theorem B1628567 : Blo 1628513 1628567 := bstep (se 1 (by rfl) ⟨1221425, by rfl⟩ : syracuseStep 1628567 = 2442851) B2442851
theorem B1833367 : Blo 1628513 1833367 := bstep (se 1 (by rfl) ⟨1375025, by rfl⟩ : syracuseStep 1833367 = 2750051) B2750051
theorem B1628587 : Blo 1628513 1628587 := bstep (se 1 (by rfl) ⟨1221440, by rfl⟩ : syracuseStep 1628587 = 2442881) B2442881
theorem B1628599 : Blo 1628513 1628599 := bstep (se 1 (by rfl) ⟨1221449, by rfl⟩ : syracuseStep 1628599 = 2442899) B2442899
theorem B3668417 : Blo 1628513 3668417 := bstep (se 2 (by rfl) ⟨1375656, by rfl⟩ : syracuseStep 3668417 = 2751313) B2751313
theorem B1628619 : Blo 1628513 1628619 := bstep (se 1 (by rfl) ⟨1221464, by rfl⟩ : syracuseStep 1628619 = 2442929) B2442929
theorem B1628631 : Blo 1628513 1628631 := bstep (se 1 (by rfl) ⟨1221473, by rfl⟩ : syracuseStep 1628631 = 2442947) B2442947
theorem B2750935 : Blo 1628513 2750935 := bstep (se 1 (by rfl) ⟨2063201, by rfl⟩ : syracuseStep 2750935 = 4126403) B4126403
theorem B1628651 : Blo 1628513 1628651 := bstep (se 1 (by rfl) ⟨1221488, by rfl⟩ : syracuseStep 1628651 = 2442977) B2442977
theorem B1628663 : Blo 1628513 1628663 := bstep (se 1 (by rfl) ⟨1221497, by rfl⟩ : syracuseStep 1628663 = 2442995) B2442995
theorem B1628683 : Blo 1628513 1628683 := bstep (se 1 (by rfl) ⟨1221512, by rfl⟩ : syracuseStep 1628683 = 2443025) B2443025
theorem B1628695 : Blo 1628513 1628695 := bstep (se 1 (by rfl) ⟨1221521, by rfl⟩ : syracuseStep 1628695 = 2443043) B2443043
theorem B1628715 : Blo 1628513 1628715 := bstep (se 1 (by rfl) ⟨1221536, by rfl⟩ : syracuseStep 1628715 = 2443073) B2443073
theorem B1628727 : Blo 1628513 1628727 := bstep (se 1 (by rfl) ⟨1221545, by rfl⟩ : syracuseStep 1628727 = 2443091) B2443091
theorem B6183499 : Blo 1628513 6183499 := bstep (se 1 (by rfl) ⟨4637624, by rfl⟩ : syracuseStep 6183499 = 9275249) B9275249
theorem B1628747 : Blo 1628513 1628747 := bstep (se 1 (by rfl) ⟨1221560, by rfl⟩ : syracuseStep 1628747 = 2443121) B2443121
theorem B1833547 : Blo 1628513 1833547 := bstep (se 1 (by rfl) ⟨1375160, by rfl⟩ : syracuseStep 1833547 = 2750321) B2750321
theorem B1628759 : Blo 1628513 1628759 := bstep (se 1 (by rfl) ⟨1221569, by rfl⟩ : syracuseStep 1628759 = 2443139) B2443139
theorem B1628779 : Blo 1628513 1628779 := bstep (se 1 (by rfl) ⟨1221584, by rfl⟩ : syracuseStep 1628779 = 2443169) B2443169
theorem B1628791 : Blo 1628513 1628791 := bstep (se 1 (by rfl) ⟨1221593, by rfl⟩ : syracuseStep 1628791 = 2443187) B2443187
theorem B6609539 : Blo 1628513 6609539 := bstep (se 1 (by rfl) ⟨4957154, by rfl⟩ : syracuseStep 6609539 = 9914309) B9914309
theorem B1628811 : Blo 1628513 1628811 := bstep (se 1 (by rfl) ⟨1221608, by rfl⟩ : syracuseStep 1628811 = 2443217) B2443217
theorem B1628823 : Blo 1628513 1628823 := bstep (se 1 (by rfl) ⟨1221617, by rfl⟩ : syracuseStep 1628823 = 2443235) B2443235
theorem B2062999 : Blo 1628513 2062999 := bstep (se 1 (by rfl) ⟨1547249, by rfl⟩ : syracuseStep 2062999 = 3094499) B3094499
theorem B3668633 : Blo 1628513 3668633 := bstep (se 2 (by rfl) ⟨1375737, by rfl⟩ : syracuseStep 3668633 = 2751475) B2751475
theorem B1628843 : Blo 1628513 1628843 := bstep (se 1 (by rfl) ⟨1221632, by rfl⟩ : syracuseStep 1628843 = 2443265) B2443265
theorem B3914419 : Blo 1628513 3914419 := bstep (se 1 (by rfl) ⟨2935814, by rfl⟩ : syracuseStep 3914419 = 5871629) B5871629
theorem B1628855 : Blo 1628513 1628855 := bstep (se 1 (by rfl) ⟨1221641, by rfl⟩ : syracuseStep 1628855 = 2443283) B2443283
theorem B1833655 : Blo 1628513 1833655 := bstep (se 1 (by rfl) ⟨1375241, by rfl⟩ : syracuseStep 1833655 = 2750483) B2750483
theorem B1628875 : Blo 1628513 1628875 := bstep (se 1 (by rfl) ⟨1221656, by rfl⟩ : syracuseStep 1628875 = 2443313) B2443313
theorem B3095243 : Blo 1628513 3095243 := bstep (se 1 (by rfl) ⟨2321432, by rfl⟩ : syracuseStep 3095243 = 4642865) B4642865
theorem B1628887 : Blo 1628513 1628887 := bstep (se 1 (by rfl) ⟨1221665, by rfl⟩ : syracuseStep 1628887 = 2443331) B2443331
theorem B1628907 : Blo 1628513 1628907 := bstep (se 1 (by rfl) ⟨1221680, by rfl⟩ : syracuseStep 1628907 = 2443361) B2443361
theorem B1628919 : Blo 1628513 1628919 := bstep (se 1 (by rfl) ⟨1221689, by rfl⟩ : syracuseStep 1628919 = 2443379) B2443379
theorem B18561797 : Blo 1628513 18561797 := bstep (se 4 (by rfl) ⟨1740168, by rfl⟩ : syracuseStep 18561797 = 3480337) B3480337
theorem B1628939 : Blo 1628513 1628939 := bstep (se 1 (by rfl) ⟨1221704, by rfl⟩ : syracuseStep 1628939 = 2443409) B2443409
theorem B1628951 : Blo 1628513 1628951 := bstep (se 1 (by rfl) ⟨1221713, by rfl⟩ : syracuseStep 1628951 = 2443427) B2443427
theorem B1628971 : Blo 1628513 1628971 := bstep (se 1 (by rfl) ⟨1221728, by rfl⟩ : syracuseStep 1628971 = 2443457) B2443457
theorem B1628983 : Blo 1628513 1628983 := bstep (se 1 (by rfl) ⟨1221737, by rfl⟩ : syracuseStep 1628983 = 2443475) B2443475
theorem B15883073 : Blo 1628513 15883073 := bstep (se 2 (by rfl) ⟨5956152, by rfl⟩ : syracuseStep 15883073 = 11912305) B11912305
theorem B1629003 : Blo 1628513 1629003 := bstep (se 1 (by rfl) ⟨1221752, by rfl⟩ : syracuseStep 1629003 = 2443505) B2443505
theorem B9280331 : Blo 1628513 9280331 := bstep (se 1 (by rfl) ⟨6960248, by rfl⟩ : syracuseStep 9280331 = 13920497) B13920497
theorem B1629015 : Blo 1628513 1629015 := bstep (se 1 (by rfl) ⟨1221761, by rfl⟩ : syracuseStep 1629015 = 2443523) B2443523
theorem B6183773 : Blo 1628513 6183773 := bstep (se 3 (by rfl) ⟨1159457, by rfl⟩ : syracuseStep 6183773 = 2318915) B2318915
theorem B1629035 : Blo 1628513 1629035 := bstep (se 1 (by rfl) ⟨1221776, by rfl⟩ : syracuseStep 1629035 = 2443553) B2443553
theorem B1833835 : Blo 1628513 1833835 := bstep (se 1 (by rfl) ⟨1375376, by rfl⟩ : syracuseStep 1833835 = 2750753) B2750753
theorem B1629047 : Blo 1628513 1629047 := bstep (se 1 (by rfl) ⟨1221785, by rfl⟩ : syracuseStep 1629047 = 2443571) B2443571
theorem B3095425 : Blo 1628513 3095425 := bstep (se 2 (by rfl) ⟨1160784, by rfl⟩ : syracuseStep 3095425 = 2321569) B2321569
theorem B1629067 : Blo 1628513 1629067 := bstep (se 1 (by rfl) ⟨1221800, by rfl⟩ : syracuseStep 1629067 = 2443601) B2443601
theorem B1629079 : Blo 1628513 1629079 := bstep (se 1 (by rfl) ⟨1221809, by rfl⟩ : syracuseStep 1629079 = 2443619) B2443619
theorem B1629099 : Blo 1628513 1629099 := bstep (se 1 (by rfl) ⟨1221824, by rfl⟩ : syracuseStep 1629099 = 2443649) B2443649
theorem B1629111 : Blo 1628513 1629111 := bstep (se 1 (by rfl) ⟨1221833, by rfl⟩ : syracuseStep 1629111 = 2443667) B2443667
theorem B1629131 : Blo 1628513 1629131 := bstep (se 1 (by rfl) ⟨1221848, by rfl⟩ : syracuseStep 1629131 = 2443697) B2443697
theorem B1629143 : Blo 1628513 1629143 := bstep (se 1 (by rfl) ⟨1221857, by rfl⟩ : syracuseStep 1629143 = 2443715) B2443715
theorem B1833943 : Blo 1628513 1833943 := bstep (se 1 (by rfl) ⟨1375457, by rfl⟩ : syracuseStep 1833943 = 2750915) B2750915
theorem B3816409 : Blo 1628513 3816409 := bstep (se 2 (by rfl) ⟨1431153, by rfl⟩ : syracuseStep 3816409 = 2862307) B2862307
theorem B1629163 : Blo 1628513 1629163 := bstep (se 1 (by rfl) ⟨1221872, by rfl⟩ : syracuseStep 1629163 = 2443745) B2443745
theorem B1629175 : Blo 1628513 1629175 := bstep (se 1 (by rfl) ⟨1221881, by rfl⟩ : syracuseStep 1629175 = 2443763) B2443763
theorem B1629195 : Blo 1628513 1629195 := bstep (se 1 (by rfl) ⟨1221896, by rfl⟩ : syracuseStep 1629195 = 2443793) B2443793
theorem B1629207 : Blo 1628513 1629207 := bstep (se 1 (by rfl) ⟨1221905, by rfl⟩ : syracuseStep 1629207 = 2443811) B2443811
theorem B1629227 : Blo 1628513 1629227 := bstep (se 1 (by rfl) ⟨1221920, by rfl⟩ : syracuseStep 1629227 = 2443841) B2443841
theorem B1629239 : Blo 1628513 1629239 := bstep (se 1 (by rfl) ⟨1221929, by rfl⟩ : syracuseStep 1629239 = 2443859) B2443859
theorem B1629259 : Blo 1628513 1629259 := bstep (se 1 (by rfl) ⟨1221944, by rfl⟩ : syracuseStep 1629259 = 2443889) B2443889
theorem B6609995 : Blo 1628513 6609995 := bstep (se 1 (by rfl) ⟨4957496, by rfl⟩ : syracuseStep 6609995 = 9914993) B9914993
theorem B1629271 : Blo 1628513 1629271 := bstep (se 1 (by rfl) ⟨1221953, by rfl⟩ : syracuseStep 1629271 = 2443907) B2443907
theorem B1629291 : Blo 1628513 1629291 := bstep (se 1 (by rfl) ⟨1221968, by rfl⟩ : syracuseStep 1629291 = 2443937) B2443937
theorem B1629303 : Blo 1628513 1629303 := bstep (se 1 (by rfl) ⟨1221977, by rfl⟩ : syracuseStep 1629303 = 2443955) B2443955
theorem B1629323 : Blo 1628513 1629323 := bstep (se 1 (by rfl) ⟨1221992, by rfl⟩ : syracuseStep 1629323 = 2443985) B2443985
theorem B1834123 : Blo 1628513 1834123 := bstep (se 1 (by rfl) ⟨1375592, by rfl⟩ : syracuseStep 1834123 = 2751185) B2751185
theorem B1629335 : Blo 1628513 1629335 := bstep (se 1 (by rfl) ⟨1222001, by rfl⟩ : syracuseStep 1629335 = 2444003) B2444003
theorem B1858711 : Blo 1628513 1858711 := bstep (se 1 (by rfl) ⟨1394033, by rfl⟩ : syracuseStep 1858711 = 2788067) B2788067
theorem B1629355 : Blo 1628513 1629355 := bstep (se 1 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 1629355 = 2444033) B2444033
theorem B1629367 : Blo 1628513 1629367 := bstep (se 1 (by rfl) ⟨1222025, by rfl⟩ : syracuseStep 1629367 = 2444051) B2444051
theorem B1629387 : Blo 1628513 1629387 := bstep (se 1 (by rfl) ⟨1222040, by rfl⟩ : syracuseStep 1629387 = 2444081) B2444081
theorem B1629399 : Blo 1628513 1629399 := bstep (se 1 (by rfl) ⟨1222049, by rfl⟩ : syracuseStep 1629399 = 2444099) B2444099
theorem B1629419 : Blo 1628513 1629419 := bstep (se 1 (by rfl) ⟨1222064, by rfl⟩ : syracuseStep 1629419 = 2444129) B2444129
theorem B1629431 : Blo 1628513 1629431 := bstep (se 1 (by rfl) ⟨1222073, by rfl⟩ : syracuseStep 1629431 = 2444147) B2444147
theorem B1834231 : Blo 1628513 1834231 := bstep (se 1 (by rfl) ⟨1375673, by rfl⟩ : syracuseStep 1834231 = 2751347) B2751347
theorem B3480833 : Blo 1628513 3480833 := bstep (se 2 (by rfl) ⟨1305312, by rfl⟩ : syracuseStep 3480833 = 2610625) B2610625
theorem B1629451 : Blo 1628513 1629451 := bstep (se 1 (by rfl) ⟨1222088, by rfl⟩ : syracuseStep 1629451 = 2444177) B2444177
theorem B1629463 : Blo 1628513 1629463 := bstep (se 1 (by rfl) ⟨1222097, by rfl⟩ : syracuseStep 1629463 = 2444195) B2444195
theorem B1629483 : Blo 1628513 1629483 := bstep (se 1 (by rfl) ⟨1222112, by rfl⟩ : syracuseStep 1629483 = 2444225) B2444225
theorem B1629495 : Blo 1628513 1629495 := bstep (se 1 (by rfl) ⟨1222121, by rfl⟩ : syracuseStep 1629495 = 2444243) B2444243
theorem B1629515 : Blo 1628513 1629515 := bstep (se 1 (by rfl) ⟨1222136, by rfl⟩ : syracuseStep 1629515 = 2444273) B2444273
theorem B1629527 : Blo 1628513 1629527 := bstep (se 1 (by rfl) ⟨1222145, by rfl⟩ : syracuseStep 1629527 = 2444291) B2444291
theorem B1629547 : Blo 1628513 1629547 := bstep (se 1 (by rfl) ⟨1222160, by rfl⟩ : syracuseStep 1629547 = 2444321) B2444321
theorem B1629559 : Blo 1628513 1629559 := bstep (se 1 (by rfl) ⟨1222169, by rfl⟩ : syracuseStep 1629559 = 2444339) B2444339
theorem B1629579 : Blo 1628513 1629579 := bstep (se 1 (by rfl) ⟨1222184, by rfl⟩ : syracuseStep 1629579 = 2444369) B2444369
theorem B1629591 : Blo 1628513 1629591 := bstep (se 1 (by rfl) ⟨1222193, by rfl⟩ : syracuseStep 1629591 = 2444387) B2444387
theorem B1629611 : Blo 1628513 1629611 := bstep (se 1 (by rfl) ⟨1222208, by rfl⟩ : syracuseStep 1629611 = 2444417) B2444417
theorem B1629623 : Blo 1628513 1629623 := bstep (se 1 (by rfl) ⟨1222217, by rfl⟩ : syracuseStep 1629623 = 2444435) B2444435
theorem B1629643 : Blo 1628513 1629643 := bstep (se 1 (by rfl) ⟨1222232, by rfl⟩ : syracuseStep 1629643 = 2444465) B2444465
theorem B1629655 : Blo 1628513 1629655 := bstep (se 1 (by rfl) ⟨1222241, by rfl⟩ : syracuseStep 1629655 = 2444483) B2444483
theorem B5496281 : Blo 1628513 5496281 := bstep (se 2 (by rfl) ⟨2061105, by rfl⟩ : syracuseStep 5496281 = 4122211) B4122211
theorem B1629675 : Blo 1628513 1629675 := bstep (se 1 (by rfl) ⟨1222256, by rfl⟩ : syracuseStep 1629675 = 2444513) B2444513
theorem B1629687 : Blo 1628513 1629687 := bstep (se 1 (by rfl) ⟨1222265, by rfl⟩ : syracuseStep 1629687 = 2444531) B2444531
theorem B1629707 : Blo 1628513 1629707 := bstep (se 1 (by rfl) ⟨1222280, by rfl⟩ : syracuseStep 1629707 = 2444561) B2444561
theorem B6184471 : Blo 1628513 6184471 := bstep (se 1 (by rfl) ⟨4638353, by rfl⟩ : syracuseStep 6184471 = 9276707) B9276707
theorem B1629719 : Blo 1628513 1629719 := bstep (se 1 (by rfl) ⟨1222289, by rfl⟩ : syracuseStep 1629719 = 2444579) B2444579
theorem B1629739 : Blo 1628513 1629739 := bstep (se 1 (by rfl) ⟨1222304, by rfl⟩ : syracuseStep 1629739 = 2444609) B2444609
theorem B8248877 : Blo 1628513 8248877 := bstep (se 3 (by rfl) ⟨1546664, by rfl⟩ : syracuseStep 8248877 = 3093329) B3093329
theorem B1629751 : Blo 1628513 1629751 := bstep (se 1 (by rfl) ⟨1222313, by rfl⟩ : syracuseStep 1629751 = 2444627) B2444627
theorem B1629771 : Blo 1628513 1629771 := bstep (se 1 (by rfl) ⟨1222328, by rfl⟩ : syracuseStep 1629771 = 2444657) B2444657
theorem B1629783 : Blo 1628513 1629783 := bstep (se 1 (by rfl) ⟨1222337, by rfl⟩ : syracuseStep 1629783 = 2444675) B2444675
theorem B1629803 : Blo 1628513 1629803 := bstep (se 1 (by rfl) ⟨1222352, by rfl⟩ : syracuseStep 1629803 = 2444705) B2444705
theorem B1629815 : Blo 1628513 1629815 := bstep (se 1 (by rfl) ⟨1222361, by rfl⟩ : syracuseStep 1629815 = 2444723) B2444723
theorem B1629835 : Blo 1628513 1629835 := bstep (se 1 (by rfl) ⟨1222376, by rfl⟩ : syracuseStep 1629835 = 2444753) B2444753
theorem B1629847 : Blo 1628513 1629847 := bstep (se 1 (by rfl) ⟨1222385, by rfl⟩ : syracuseStep 1629847 = 2444771) B2444771
theorem B1629867 : Blo 1628513 1629867 := bstep (se 1 (by rfl) ⟨1222400, by rfl⟩ : syracuseStep 1629867 = 2444801) B2444801
theorem B6962861 : Blo 1628513 6962861 := bstep (se 3 (by rfl) ⟨1305536, by rfl⟩ : syracuseStep 6962861 = 2611073) B2611073
theorem B1629879 : Blo 1628513 1629879 := bstep (se 1 (by rfl) ⟨1222409, by rfl⟩ : syracuseStep 1629879 = 2444819) B2444819
theorem B5217995 : Blo 1628513 5217995 := bstep (se 1 (by rfl) ⟨3913496, by rfl⟩ : syracuseStep 5217995 = 7826993) B7826993
theorem B1629899 : Blo 1628513 1629899 := bstep (se 1 (by rfl) ⟨1222424, by rfl⟩ : syracuseStep 1629899 = 2444849) B2444849
theorem B1629911 : Blo 1628513 1629911 := bstep (se 1 (by rfl) ⟨1222433, by rfl⟩ : syracuseStep 1629911 = 2444867) B2444867
theorem B1629931 : Blo 1628513 1629931 := bstep (se 1 (by rfl) ⟨1222448, by rfl⟩ : syracuseStep 1629931 = 2444897) B2444897
theorem B1629943 : Blo 1628513 1629943 := bstep (se 1 (by rfl) ⟨1222457, by rfl⟩ : syracuseStep 1629943 = 2444915) B2444915
theorem B1629963 : Blo 1628513 1629963 := bstep (se 1 (by rfl) ⟨1222472, by rfl⟩ : syracuseStep 1629963 = 2444945) B2444945
theorem B3481355 : Blo 1628513 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B1629975 : Blo 1628513 1629975 := bstep (se 1 (by rfl) ⟨1222481, by rfl⟩ : syracuseStep 1629975 = 2444963) B2444963
theorem B1629995 : Blo 1628513 1629995 := bstep (se 1 (by rfl) ⟨1222496, by rfl⟩ : syracuseStep 1629995 = 2444993) B2444993
theorem B1630007 : Blo 1628513 1630007 := bstep (se 1 (by rfl) ⟨1222505, by rfl⟩ : syracuseStep 1630007 = 2445011) B2445011
theorem B1630027 : Blo 1628513 1630027 := bstep (se 1 (by rfl) ⟨1222520, by rfl⟩ : syracuseStep 1630027 = 2445041) B2445041
theorem B1630039 : Blo 1628513 1630039 := bstep (se 1 (by rfl) ⟨1222529, by rfl⟩ : syracuseStep 1630039 = 2445059) B2445059
theorem B1630059 : Blo 1628513 1630059 := bstep (se 1 (by rfl) ⟨1222544, by rfl⟩ : syracuseStep 1630059 = 2445089) B2445089
theorem B1630071 : Blo 1628513 1630071 := bstep (se 1 (by rfl) ⟨1222553, by rfl⟩ : syracuseStep 1630071 = 2445107) B2445107
theorem B1630091 : Blo 1628513 1630091 := bstep (se 1 (by rfl) ⟨1222568, by rfl⟩ : syracuseStep 1630091 = 2445137) B2445137
theorem B1630103 : Blo 1628513 1630103 := bstep (se 1 (by rfl) ⟨1222577, by rfl⟩ : syracuseStep 1630103 = 2445155) B2445155
theorem B1630123 : Blo 1628513 1630123 := bstep (se 1 (by rfl) ⟨1222592, by rfl⟩ : syracuseStep 1630123 = 2445185) B2445185
theorem B1630135 : Blo 1628513 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B1630155 : Blo 1628513 1630155 := bstep (se 1 (by rfl) ⟨1222616, by rfl⟩ : syracuseStep 1630155 = 2445233) B2445233
theorem B1630167 : Blo 1628513 1630167 := bstep (se 1 (by rfl) ⟨1222625, by rfl⟩ : syracuseStep 1630167 = 2445251) B2445251
theorem B1630187 : Blo 1628513 1630187 := bstep (se 1 (by rfl) ⟨1222640, by rfl⟩ : syracuseStep 1630187 = 2445281) B2445281
theorem B1630199 : Blo 1628513 1630199 := bstep (se 1 (by rfl) ⟨1222649, by rfl⟩ : syracuseStep 1630199 = 2445299) B2445299
theorem B1630215 : Blo 1628513 1630215 := bstep (se 1 (by rfl) ⟨1222661, by rfl⟩ : syracuseStep 1630215 = 2445323) B2445323
theorem B1630223 : Blo 1628513 1630223 := bstep (se 1 (by rfl) ⟨1222667, by rfl⟩ : syracuseStep 1630223 = 2445335) B2445335
theorem B33431575 : Blo 1628513 33431575 := bstep (se 1 (by rfl) ⟨25073681, by rfl⟩ : syracuseStep 33431575 = 50147363) B50147363
theorem B7938071 : Blo 1628513 7938071 := bstep (se 1 (by rfl) ⟨5953553, by rfl⟩ : syracuseStep 7938071 = 11907107) B11907107
theorem B5496875 : Blo 1628513 5496875 := bstep (se 1 (by rfl) ⟨4122656, by rfl⟩ : syracuseStep 5496875 = 8245313) B8245313
theorem B1630267 : Blo 1628513 1630267 := bstep (se 1 (by rfl) ⟨1222700, by rfl⟩ : syracuseStep 1630267 = 2445401) B2445401
theorem B18817085 : Blo 1628513 18817085 := bstep (se 3 (by rfl) ⟨3528203, by rfl⟩ : syracuseStep 18817085 = 7056407) B7056407
theorem B1630343 : Blo 1628513 1630343 := bstep (se 1 (by rfl) ⟨1222757, by rfl⟩ : syracuseStep 1630343 = 2445515) B2445515
theorem B1630351 : Blo 1628513 1630351 := bstep (se 1 (by rfl) ⟨1222763, by rfl⟩ : syracuseStep 1630351 = 2445527) B2445527
theorem B1630395 : Blo 1628513 1630395 := bstep (se 1 (by rfl) ⟨1222796, by rfl⟩ : syracuseStep 1630395 = 2445593) B2445593
theorem B10436809 : Blo 1628513 10436809 := bstep (se 2 (by rfl) ⟨3913803, by rfl⟩ : syracuseStep 10436809 = 7827607) B7827607
theorem B12370157 : Blo 1628513 12370157 := bstep (se 3 (by rfl) ⟨2319404, by rfl⟩ : syracuseStep 12370157 = 4638809) B4638809
theorem B9912557 : Blo 1628513 9912557 := bstep (se 3 (by rfl) ⟨1858604, by rfl⟩ : syracuseStep 9912557 = 3717209) B3717209
theorem B1630471 : Blo 1628513 1630471 := bstep (se 1 (by rfl) ⟨1222853, by rfl⟩ : syracuseStep 1630471 = 2445707) B2445707
theorem B6185231 : Blo 1628513 6185231 := bstep (se 1 (by rfl) ⟨4638923, by rfl⟩ : syracuseStep 6185231 = 9277847) B9277847
theorem B1630479 : Blo 1628513 1630479 := bstep (se 1 (by rfl) ⟨1222859, by rfl⟩ : syracuseStep 1630479 = 2445719) B2445719
theorem B23503121 : Blo 1628513 23503121 := bstep (se 2 (by rfl) ⟨8813670, by rfl⟩ : syracuseStep 23503121 = 17627341) B17627341
theorem B11739451 : Blo 1628513 11739451 := bstep (se 1 (by rfl) ⟨8804588, by rfl⟩ : syracuseStep 11739451 = 17609177) B17609177
theorem B9282221 : Blo 1628513 9282221 := bstep (se 3 (by rfl) ⟨1740416, by rfl⟩ : syracuseStep 9282221 = 3480833) B3480833
theorem B1958647 : Blo 1628513 1958647 := bstep (se 1 (by rfl) ⟨1468985, by rfl⟩ : syracuseStep 1958647 = 2937971) B2937971
theorem B8807183 : Blo 1628513 8807183 := bstep (se 1 (by rfl) ⟨6605387, by rfl⟩ : syracuseStep 8807183 = 13210775) B13210775
theorem B5219225 : Blo 1628513 5219225 := bstep (se 2 (by rfl) ⟨1957209, by rfl⟩ : syracuseStep 5219225 = 3914419) B3914419
theorem B26428427 : Blo 1628513 26428427 := bstep (se 1 (by rfl) ⟨19821320, by rfl⟩ : syracuseStep 26428427 = 39642641) B39642641
theorem B18555965 : Blo 1628513 18555965 := bstep (se 3 (by rfl) ⟨3479243, by rfl⟩ : syracuseStep 18555965 = 6958487) B6958487
theorem B6268175 : Blo 1628513 6268175 := bstep (se 1 (by rfl) ⟨4701131, by rfl⟩ : syracuseStep 6268175 = 9402263) B9402263
theorem B5088545 : Blo 1628513 5088545 := bstep (se 2 (by rfl) ⟨1908204, by rfl⟩ : syracuseStep 5088545 = 3816409) B3816409
theorem B2319673 : Blo 1628513 2319673 := bstep (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) B1739755
theorem B6604091 : Blo 1628513 6604091 := bstep (se 1 (by rfl) ⟨4953068, by rfl⟩ : syracuseStep 6604091 = 9906137) B9906137
theorem B5498171 : Blo 1628513 5498171 := bstep (se 1 (by rfl) ⟨4123628, by rfl⟩ : syracuseStep 5498171 = 8247257) B8247257
theorem B2442809 : Blo 1628513 2442809 := bstep (se 2 (by rfl) ⟨916053, by rfl⟩ : syracuseStep 2442809 = 1832107) B1832107
theorem B2442887 : Blo 1628513 2442887 := bstep (se 1 (by rfl) ⟨1832165, by rfl⟩ : syracuseStep 2442887 = 3664331) B3664331
theorem B4638343 : Blo 1628513 4638343 := bstep (se 1 (by rfl) ⟨3478757, by rfl⟩ : syracuseStep 4638343 = 6957515) B6957515
theorem B3966617 : Blo 1628513 3966617 := bstep (se 2 (by rfl) ⟨1487481, by rfl⟩ : syracuseStep 3966617 = 2974963) B2974963
theorem B2442923 : Blo 1628513 2442923 := bstep (se 1 (by rfl) ⟨1832192, by rfl⟩ : syracuseStep 2442923 = 3664385) B3664385
theorem B22906547 : Blo 1628513 22906547 := bstep (se 1 (by rfl) ⟨17179910, by rfl⟩ : syracuseStep 22906547 = 34359821) B34359821
theorem B2442953 : Blo 1628513 2442953 := bstep (se 2 (by rfl) ⟨916107, by rfl⟩ : syracuseStep 2442953 = 1832215) B1832215
theorem B12379877 : Blo 1628513 12379877 := bstep (se 4 (by rfl) ⟨1160613, by rfl⟩ : syracuseStep 12379877 = 2321227) B2321227
theorem B5498657 : Blo 1628513 5498657 := bstep (se 2 (by rfl) ⟨2061996, by rfl⟩ : syracuseStep 5498657 = 4123993) B4123993
theorem B2443067 : Blo 1628513 2443067 := bstep (se 1 (by rfl) ⟨1832300, by rfl⟩ : syracuseStep 2443067 = 3664601) B3664601
theorem B2934647 : Blo 1628513 2934647 := bstep (se 1 (by rfl) ⟨2200985, by rfl⟩ : syracuseStep 2934647 = 4401971) B4401971
theorem B2443127 : Blo 1628513 2443127 := bstep (se 1 (by rfl) ⟨1832345, by rfl⟩ : syracuseStep 2443127 = 3664691) B3664691
theorem B6186887 : Blo 1628513 6186887 := bstep (se 1 (by rfl) ⟨4640165, by rfl⟩ : syracuseStep 6186887 = 9280331) B9280331
theorem B2443151 : Blo 1628513 2443151 := bstep (se 1 (by rfl) ⟨1832363, by rfl⟩ : syracuseStep 2443151 = 3664727) B3664727
theorem B4122515 : Blo 1628513 4122515 := bstep (se 1 (by rfl) ⟨3091886, by rfl⟩ : syracuseStep 4122515 = 6183773) B6183773
theorem B4638617 : Blo 1628513 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B2443193 : Blo 1628513 2443193 := bstep (se 2 (by rfl) ⟨916197, by rfl⟩ : syracuseStep 2443193 = 1832395) B1832395
theorem B7432121 : Blo 1628513 7432121 := bstep (se 2 (by rfl) ⟨2787045, by rfl⟩ : syracuseStep 7432121 = 5574091) B5574091
theorem B2443271 : Blo 1628513 2443271 := bstep (se 1 (by rfl) ⟨1832453, by rfl⟩ : syracuseStep 2443271 = 3664907) B3664907
theorem B2443307 : Blo 1628513 2443307 := bstep (se 1 (by rfl) ⟨1832480, by rfl⟩ : syracuseStep 2443307 = 3664961) B3664961
theorem B2443337 : Blo 1628513 2443337 := bstep (se 2 (by rfl) ⟨916251, by rfl⟩ : syracuseStep 2443337 = 1832503) B1832503
theorem B12372101 : Blo 1628513 12372101 := bstep (se 4 (by rfl) ⟨1159884, by rfl⟩ : syracuseStep 12372101 = 2319769) B2319769
theorem B4122809 : Blo 1628513 4122809 := bstep (se 2 (by rfl) ⟨1546053, by rfl⟩ : syracuseStep 4122809 = 3092107) B3092107
theorem B2443451 : Blo 1628513 2443451 := bstep (se 1 (by rfl) ⟨1832588, by rfl⟩ : syracuseStep 2443451 = 3665177) B3665177
theorem B2443511 : Blo 1628513 2443511 := bstep (se 1 (by rfl) ⟨1832633, by rfl⟩ : syracuseStep 2443511 = 3665267) B3665267
theorem B2443535 : Blo 1628513 2443535 := bstep (se 1 (by rfl) ⟨1832651, by rfl⟩ : syracuseStep 2443535 = 3665303) B3665303
theorem B2443577 : Blo 1628513 2443577 := bstep (se 2 (by rfl) ⟨916341, by rfl⟩ : syracuseStep 2443577 = 1832683) B1832683
theorem B3664187 : Blo 1628513 3664187 := bstep (se 1 (by rfl) ⟨2748140, by rfl⟩ : syracuseStep 3664187 = 5496281) B5496281
theorem B5499251 : Blo 1628513 5499251 := bstep (se 1 (by rfl) ⟨4124438, by rfl⟩ : syracuseStep 5499251 = 8248877) B8248877
theorem B7833971 : Blo 1628513 7833971 := bstep (se 1 (by rfl) ⟨5875478, by rfl⟩ : syracuseStep 7833971 = 11750957) B11750957
theorem B2443655 : Blo 1628513 2443655 := bstep (se 1 (by rfl) ⟨1832741, by rfl⟩ : syracuseStep 2443655 = 3665483) B3665483
theorem B8251793 : Blo 1628513 8251793 := bstep (se 2 (by rfl) ⟨3094422, by rfl⟩ : syracuseStep 8251793 = 6188845) B6188845
theorem B2443691 : Blo 1628513 2443691 := bstep (se 1 (by rfl) ⟨1832768, by rfl⟩ : syracuseStep 2443691 = 3665537) B3665537
theorem B3664313 : Blo 1628513 3664313 := bstep (se 2 (by rfl) ⟨1374117, by rfl⟩ : syracuseStep 3664313 = 2748235) B2748235
theorem B2443721 : Blo 1628513 2443721 := bstep (se 2 (by rfl) ⟨916395, by rfl⟩ : syracuseStep 2443721 = 1832791) B1832791
theorem B2320903 : Blo 1628513 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B4639265 : Blo 1628513 4639265 := bstep (se 2 (by rfl) ⟨1739724, by rfl⟩ : syracuseStep 4639265 = 3479449) B3479449
theorem B1739323 : Blo 1628513 1739323 := bstep (se 1 (by rfl) ⟨1304492, by rfl⟩ : syracuseStep 1739323 = 2608985) B2608985
theorem B2443835 : Blo 1628513 2443835 := bstep (se 1 (by rfl) ⟨1832876, by rfl⟩ : syracuseStep 2443835 = 3665753) B3665753
theorem B79317569 : Blo 1628513 79317569 := bstep (se 2 (by rfl) ⟨29744088, by rfl⟩ : syracuseStep 79317569 = 59488177) B59488177
theorem B2443895 : Blo 1628513 2443895 := bstep (se 1 (by rfl) ⟨1832921, by rfl⟩ : syracuseStep 2443895 = 3665843) B3665843
theorem B2443919 : Blo 1628513 2443919 := bstep (se 1 (by rfl) ⟨1832939, by rfl⟩ : syracuseStep 2443919 = 3665879) B3665879
theorem B2091691 : Blo 1628513 2091691 := bstep (se 1 (by rfl) ⟨1568768, by rfl⟩ : syracuseStep 2091691 = 3137537) B3137537
theorem B2443961 : Blo 1628513 2443961 := bstep (se 2 (by rfl) ⟨916485, by rfl⟩ : syracuseStep 2443961 = 1832971) B1832971
theorem B2444039 : Blo 1628513 2444039 := bstep (se 1 (by rfl) ⟨1833029, by rfl⟩ : syracuseStep 2444039 = 3666059) B3666059
theorem B3664655 : Blo 1628513 3664655 := bstep (se 1 (by rfl) ⟨2748491, by rfl⟩ : syracuseStep 3664655 = 5496983) B5496983
theorem B6957839 : Blo 1628513 6957839 := bstep (se 1 (by rfl) ⟨5218379, by rfl⟩ : syracuseStep 6957839 = 10436759) B10436759
theorem B3664673 : Blo 1628513 3664673 := bstep (se 2 (by rfl) ⟨1374252, by rfl⟩ : syracuseStep 3664673 = 2748505) B2748505
theorem B2444075 : Blo 1628513 2444075 := bstep (se 1 (by rfl) ⟨1833056, by rfl⟩ : syracuseStep 2444075 = 3666113) B3666113
theorem B2444105 : Blo 1628513 2444105 := bstep (se 2 (by rfl) ⟨916539, by rfl⟩ : syracuseStep 2444105 = 1833079) B1833079
theorem B4123507 : Blo 1628513 4123507 := bstep (se 1 (by rfl) ⟨3092630, by rfl⟩ : syracuseStep 4123507 = 6185261) B6185261
theorem B2444219 : Blo 1628513 2444219 := bstep (se 1 (by rfl) ⟨1833164, by rfl⟩ : syracuseStep 2444219 = 3666329) B3666329
theorem B13216715 : Blo 1628513 13216715 := bstep (se 1 (by rfl) ⟨9912536, by rfl⟩ : syracuseStep 13216715 = 19825073) B19825073
theorem B7056337 : Blo 1628513 7056337 := bstep (se 2 (by rfl) ⟨2646126, by rfl⟩ : syracuseStep 7056337 = 5292253) B5292253
theorem B2444279 : Blo 1628513 2444279 := bstep (se 1 (by rfl) ⟨1833209, by rfl⟩ : syracuseStep 2444279 = 3666419) B3666419
theorem B4123649 : Blo 1628513 4123649 := bstep (se 2 (by rfl) ⟨1546368, by rfl⟩ : syracuseStep 4123649 = 3092737) B3092737
theorem B50187275 : Blo 1628513 50187275 := bstep (se 1 (by rfl) ⟨37640456, by rfl⟩ : syracuseStep 50187275 = 75280913) B75280913
theorem B2444303 : Blo 1628513 2444303 := bstep (se 1 (by rfl) ⟨1833227, by rfl⟩ : syracuseStep 2444303 = 3666455) B3666455
theorem B2444345 : Blo 1628513 2444345 := bstep (se 2 (by rfl) ⟨916629, by rfl⟩ : syracuseStep 2444345 = 1833259) B1833259
theorem B9915479 : Blo 1628513 9915479 := bstep (se 1 (by rfl) ⟨7436609, by rfl⟩ : syracuseStep 9915479 = 14873219) B14873219
theorem B3665015 : Blo 1628513 3665015 := bstep (se 1 (by rfl) ⟨2748761, by rfl⟩ : syracuseStep 3665015 = 5497523) B5497523
theorem B2444423 : Blo 1628513 2444423 := bstep (se 1 (by rfl) ⟨1833317, by rfl⟩ : syracuseStep 2444423 = 3666635) B3666635
theorem B2444459 : Blo 1628513 2444459 := bstep (se 1 (by rfl) ⟨1833344, by rfl⟩ : syracuseStep 2444459 = 3666689) B3666689
theorem B2444489 : Blo 1628513 2444489 := bstep (se 2 (by rfl) ⟨916683, by rfl⟩ : syracuseStep 2444489 = 1833367) B1833367
theorem B7834913 : Blo 1628513 7834913 := bstep (se 2 (by rfl) ⟨2938092, by rfl⟩ : syracuseStep 7834913 = 5876185) B5876185
theorem B3665195 : Blo 1628513 3665195 := bstep (se 1 (by rfl) ⟨2748896, by rfl⟩ : syracuseStep 3665195 = 5497793) B5497793
theorem B2444603 : Blo 1628513 2444603 := bstep (se 1 (by rfl) ⟨1833452, by rfl⟩ : syracuseStep 2444603 = 3666905) B3666905
theorem B2444663 : Blo 1628513 2444663 := bstep (se 1 (by rfl) ⟨1833497, by rfl⟩ : syracuseStep 2444663 = 3666995) B3666995
theorem B2444687 : Blo 1628513 2444687 := bstep (se 1 (by rfl) ⟨1833515, by rfl⟩ : syracuseStep 2444687 = 3667031) B3667031
theorem B2477483 : Blo 1628513 2477483 := bstep (se 1 (by rfl) ⟨1858112, by rfl⟩ : syracuseStep 2477483 = 3716225) B3716225
theorem B8244665 : Blo 1628513 8244665 := bstep (se 2 (by rfl) ⟨3091749, by rfl⟩ : syracuseStep 8244665 = 6183499) B6183499
theorem B2444729 : Blo 1628513 2444729 := bstep (se 2 (by rfl) ⟨916773, by rfl⟩ : syracuseStep 2444729 = 1833547) B1833547
theorem B4124105 : Blo 1628513 4124105 := bstep (se 2 (by rfl) ⟨1546539, by rfl⟩ : syracuseStep 4124105 = 3093079) B3093079
theorem B27831761 : Blo 1628513 27831761 := bstep (se 2 (by rfl) ⟨10436910, by rfl⟩ : syracuseStep 27831761 = 20873821) B20873821
theorem B2444807 : Blo 1628513 2444807 := bstep (se 1 (by rfl) ⟨1833605, by rfl⟩ : syracuseStep 2444807 = 3667211) B3667211
theorem B4640267 : Blo 1628513 4640267 := bstep (se 1 (by rfl) ⟨3480200, by rfl⟩ : syracuseStep 4640267 = 6960401) B6960401
theorem B2444843 : Blo 1628513 2444843 := bstep (se 1 (by rfl) ⟨1833632, by rfl⟩ : syracuseStep 2444843 = 3667265) B3667265
theorem B2444873 : Blo 1628513 2444873 := bstep (se 2 (by rfl) ⟨916827, by rfl⟩ : syracuseStep 2444873 = 1833655) B1833655
theorem B6188663 : Blo 1628513 6188663 := bstep (se 1 (by rfl) ⟨4641497, by rfl⟩ : syracuseStep 6188663 = 9282995) B9282995
theorem B3665555 : Blo 1628513 3665555 := bstep (se 1 (by rfl) ⟨2749166, by rfl⟩ : syracuseStep 3665555 = 5498333) B5498333
theorem B39628439 : Blo 1628513 39628439 := bstep (se 1 (by rfl) ⟨29721329, by rfl⟩ : syracuseStep 39628439 = 59442659) B59442659
theorem B2444987 : Blo 1628513 2444987 := bstep (se 1 (by rfl) ⟨1833740, by rfl⟩ : syracuseStep 2444987 = 3667481) B3667481
theorem B3665609 : Blo 1628513 3665609 := bstep (se 2 (by rfl) ⟨1374603, by rfl⟩ : syracuseStep 3665609 = 2749207) B2749207
theorem B2445047 : Blo 1628513 2445047 := bstep (se 1 (by rfl) ⟨1833785, by rfl⟩ : syracuseStep 2445047 = 3667571) B3667571
theorem B2445071 : Blo 1628513 2445071 := bstep (se 1 (by rfl) ⟨1833803, by rfl⟩ : syracuseStep 2445071 = 3667607) B3667607
theorem B4124459 : Blo 1628513 4124459 := bstep (se 1 (by rfl) ⟨3093344, by rfl⟩ : syracuseStep 4124459 = 6186689) B6186689
theorem B2445113 : Blo 1628513 2445113 := bstep (se 2 (by rfl) ⟨916917, by rfl⟩ : syracuseStep 2445113 = 1833835) B1833835
theorem B4239239 : Blo 1628513 4239239 := bstep (se 1 (by rfl) ⟨3179429, by rfl⟩ : syracuseStep 4239239 = 6358859) B6358859
theorem B2445191 : Blo 1628513 2445191 := bstep (se 1 (by rfl) ⟨1833893, by rfl⟩ : syracuseStep 2445191 = 3667787) B3667787
theorem B2445227 : Blo 1628513 2445227 := bstep (se 1 (by rfl) ⟨1833920, by rfl⟩ : syracuseStep 2445227 = 3667841) B3667841
theorem B2445257 : Blo 1628513 2445257 := bstep (se 2 (by rfl) ⟨916971, by rfl⟩ : syracuseStep 2445257 = 1833943) B1833943
theorem B2748431 : Blo 1628513 2748431 := bstep (se 1 (by rfl) ⟨2061323, by rfl⟩ : syracuseStep 2748431 = 4122647) B4122647
theorem B11300887 : Blo 1628513 11300887 := bstep (se 1 (by rfl) ⟨8475665, by rfl⟩ : syracuseStep 11300887 = 16951331) B16951331
theorem B2445371 : Blo 1628513 2445371 := bstep (se 1 (by rfl) ⟨1834028, by rfl⟩ : syracuseStep 2445371 = 3668057) B3668057
theorem B6959171 : Blo 1628513 6959171 := bstep (se 1 (by rfl) ⟨5219378, by rfl⟩ : syracuseStep 6959171 = 10438757) B10438757
theorem B2445431 : Blo 1628513 2445431 := bstep (se 1 (by rfl) ⟨1834073, by rfl⟩ : syracuseStep 2445431 = 3668147) B3668147
theorem B2445455 : Blo 1628513 2445455 := bstep (se 1 (by rfl) ⟨1834091, by rfl⟩ : syracuseStep 2445455 = 3668183) B3668183
theorem B2445497 : Blo 1628513 2445497 := bstep (se 2 (by rfl) ⟨917061, by rfl⟩ : syracuseStep 2445497 = 1834123) B1834123
theorem B2478281 : Blo 1628513 2478281 := bstep (se 2 (by rfl) ⟨929355, by rfl⟩ : syracuseStep 2478281 = 1858711) B1858711
theorem B2445575 : Blo 1628513 2445575 := bstep (se 1 (by rfl) ⟨1834181, by rfl⟩ : syracuseStep 2445575 = 3668363) B3668363
theorem B2445611 : Blo 1628513 2445611 := bstep (se 1 (by rfl) ⟨1834208, by rfl⟩ : syracuseStep 2445611 = 3668417) B3668417
theorem B14872891 : Blo 1628513 14872891 := bstep (se 1 (by rfl) ⟨11154668, by rfl⟩ : syracuseStep 14872891 = 22309337) B22309337
theorem B2445641 : Blo 1628513 2445641 := bstep (se 2 (by rfl) ⟨917115, by rfl⟩ : syracuseStep 2445641 = 1834231) B1834231
theorem B17625437 : Blo 1628513 17625437 := bstep (se 3 (by rfl) ⟨3304769, by rfl⟩ : syracuseStep 17625437 = 6609539) B6609539
theorem B3666311 : Blo 1628513 3666311 := bstep (se 1 (by rfl) ⟨2749733, by rfl⟩ : syracuseStep 3666311 = 5499467) B5499467
theorem B12890503 : Blo 1628513 12890503 := bstep (se 1 (by rfl) ⟨9667877, by rfl⟩ : syracuseStep 12890503 = 19335755) B19335755
theorem B6959513 : Blo 1628513 6959513 := bstep (se 2 (by rfl) ⟨2609817, by rfl⟩ : syracuseStep 6959513 = 5219635) B5219635
theorem B2445755 : Blo 1628513 2445755 := bstep (se 1 (by rfl) ⟨1834316, by rfl⟩ : syracuseStep 2445755 = 3668633) B3668633
theorem B8253899 : Blo 1628513 8253899 := bstep (se 1 (by rfl) ⟨6190424, by rfl⟩ : syracuseStep 8253899 = 12380849) B12380849
theorem B18567629 : Blo 1628513 18567629 := bstep (se 3 (by rfl) ⟨3481430, by rfl⟩ : syracuseStep 18567629 = 6962861) B6962861
theorem B12374531 : Blo 1628513 12374531 := bstep (se 1 (by rfl) ⟨9280898, by rfl⟩ : syracuseStep 12374531 = 18561797) B18561797
theorem B2748971 : Blo 1628513 2748971 := bstep (se 1 (by rfl) ⟨2061728, by rfl⟩ : syracuseStep 2748971 = 4123457) B4123457
theorem B10588715 : Blo 1628513 10588715 := bstep (se 1 (by rfl) ⟨7941536, by rfl⟩ : syracuseStep 10588715 = 15883073) B15883073
theorem B3666491 : Blo 1628513 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B6189635 : Blo 1628513 6189635 := bstep (se 1 (by rfl) ⟨4642226, by rfl⟩ : syracuseStep 6189635 = 9284453) B9284453
theorem B8925815 : Blo 1628513 8925815 := bstep (se 1 (by rfl) ⟨6694361, by rfl⟩ : syracuseStep 8925815 = 13388723) B13388723
theorem B3666617 : Blo 1628513 3666617 := bstep (se 2 (by rfl) ⟨1374981, by rfl⟩ : syracuseStep 3666617 = 2749963) B2749963
theorem B8245961 : Blo 1628513 8245961 := bstep (se 2 (by rfl) ⟨3092235, by rfl⟩ : syracuseStep 8245961 = 6184471) B6184471
theorem B4125451 : Blo 1628513 4125451 := bstep (se 1 (by rfl) ⟨3094088, by rfl⟩ : syracuseStep 4125451 = 6188177) B6188177
theorem B8254223 : Blo 1628513 8254223 := bstep (se 1 (by rfl) ⟨6190667, by rfl⟩ : syracuseStep 8254223 = 12381335) B12381335
theorem B3093383 : Blo 1628513 3093383 := bstep (se 1 (by rfl) ⟨2320037, by rfl⟩ : syracuseStep 3093383 = 4640075) B4640075
theorem B5501843 : Blo 1628513 5501843 := bstep (se 1 (by rfl) ⟨4126382, by rfl⟩ : syracuseStep 5501843 = 8252765) B8252765
theorem B4125593 : Blo 1628513 4125593 := bstep (se 2 (by rfl) ⟨1547097, by rfl⟩ : syracuseStep 4125593 = 3094195) B3094195
theorem B12366755 : Blo 1628513 12366755 := bstep (se 1 (by rfl) ⟨9275066, by rfl⟩ : syracuseStep 12366755 = 18550133) B18550133
theorem B14873507 : Blo 1628513 14873507 := bstep (se 1 (by rfl) ⟨11155130, by rfl⟩ : syracuseStep 14873507 = 22310261) B22310261
theorem B2061227 : Blo 1628513 2061227 := bstep (se 1 (by rfl) ⟨1545920, by rfl⟩ : syracuseStep 2061227 = 3091841) B3091841
theorem B2749369 : Blo 1628513 2749369 := bstep (se 2 (by rfl) ⟨1031013, by rfl⟩ : syracuseStep 2749369 = 2062027) B2062027
theorem B6190091 : Blo 1628513 6190091 := bstep (se 1 (by rfl) ⟨4642568, by rfl⟩ : syracuseStep 6190091 = 9285137) B9285137
theorem B3666959 : Blo 1628513 3666959 := bstep (se 1 (by rfl) ⟨2750219, by rfl⟩ : syracuseStep 3666959 = 5500439) B5500439
theorem B3666977 : Blo 1628513 3666977 := bstep (se 2 (by rfl) ⟨1375116, by rfl⟩ : syracuseStep 3666977 = 2750233) B2750233
theorem B5223467 : Blo 1628513 5223467 := bstep (se 1 (by rfl) ⟨3917600, by rfl⟩ : syracuseStep 5223467 = 7835201) B7835201
theorem B4125755 : Blo 1628513 4125755 := bstep (se 1 (by rfl) ⟨3094316, by rfl⟩ : syracuseStep 4125755 = 6188633) B6188633
theorem B7435331 : Blo 1628513 7435331 := bstep (se 1 (by rfl) ⟨5576498, by rfl⟩ : syracuseStep 7435331 = 11152997) B11152997
theorem B3478663 : Blo 1628513 3478663 := bstep (se 1 (by rfl) ⟨2608997, by rfl⟩ : syracuseStep 3478663 = 5217995) B5217995
theorem B1832251 : Blo 1628513 1832251 := bstep (se 1 (by rfl) ⟨1374188, by rfl⟩ : syracuseStep 1832251 = 2748377) B2748377
theorem B3667319 : Blo 1628513 3667319 := bstep (se 1 (by rfl) ⟨2750489, by rfl⟩ : syracuseStep 3667319 = 5500979) B5500979
theorem B2061703 : Blo 1628513 2061703 := bstep (se 1 (by rfl) ⟨1546277, by rfl⟩ : syracuseStep 2061703 = 3092555) B3092555
theorem B4126099 : Blo 1628513 4126099 := bstep (se 1 (by rfl) ⟨3094574, by rfl⟩ : syracuseStep 4126099 = 6189149) B6189149
theorem B9278873 : Blo 1628513 9278873 := bstep (se 2 (by rfl) ⟨3479577, by rfl⟩ : syracuseStep 9278873 = 6959155) B6959155
theorem B28227001 : Blo 1628513 28227001 := bstep (se 2 (by rfl) ⟨10585125, by rfl⟩ : syracuseStep 28227001 = 21170251) B21170251
theorem B52868537 : Blo 1628513 52868537 := bstep (se 2 (by rfl) ⟨19825701, by rfl⟩ : syracuseStep 52868537 = 39651403) B39651403
theorem B4126241 : Blo 1628513 4126241 := bstep (se 2 (by rfl) ⟨1547340, by rfl⟩ : syracuseStep 4126241 = 3094681) B3094681
theorem B3667499 : Blo 1628513 3667499 := bstep (se 1 (by rfl) ⟨2750624, by rfl⟩ : syracuseStep 3667499 = 5501249) B5501249
theorem B4642363 : Blo 1628513 4642363 := bstep (se 1 (by rfl) ⟨3481772, by rfl⟩ : syracuseStep 4642363 = 6963545) B6963545
theorem B2750071 : Blo 1628513 2750071 := bstep (se 1 (by rfl) ⟨2062553, by rfl⟩ : syracuseStep 2750071 = 4125107) B4125107
theorem B4404889 : Blo 1628513 4404889 := bstep (se 2 (by rfl) ⟨1651833, by rfl⟩ : syracuseStep 4404889 = 3303667) B3303667
theorem B1832719 : Blo 1628513 1832719 := bstep (se 1 (by rfl) ⟨1374539, by rfl⟩ : syracuseStep 1832719 = 2749079) B2749079
theorem B20879153 : Blo 1628513 20879153 := bstep (se 2 (by rfl) ⟨7829682, by rfl⟩ : syracuseStep 20879153 = 15659365) B15659365
theorem B2750267 : Blo 1628513 2750267 := bstep (se 1 (by rfl) ⟨2062700, by rfl⟩ : syracuseStep 2750267 = 4125401) B4125401
theorem B2062199 : Blo 1628513 2062199 := bstep (se 1 (by rfl) ⟨1546649, by rfl⟩ : syracuseStep 2062199 = 3093299) B3093299
theorem B3667859 : Blo 1628513 3667859 := bstep (se 1 (by rfl) ⟨2750894, by rfl⟩ : syracuseStep 3667859 = 5501789) B5501789
theorem B3667913 : Blo 1628513 3667913 := bstep (se 2 (by rfl) ⟨1375467, by rfl⟩ : syracuseStep 3667913 = 2750935) B2750935
theorem B8812547 : Blo 1628513 8812547 := bstep (se 1 (by rfl) ⟨6609410, by rfl⟩ : syracuseStep 8812547 = 13218821) B13218821
theorem B2062351 : Blo 1628513 2062351 := bstep (se 1 (by rfl) ⟨1546763, by rfl⟩ : syracuseStep 2062351 = 3093527) B3093527
theorem B2062523 : Blo 1628513 2062523 := bstep (se 1 (by rfl) ⟨1546892, by rfl⟩ : syracuseStep 2062523 = 3093785) B3093785
theorem B3135689 : Blo 1628513 3135689 := bstep (se 2 (by rfl) ⟨1175883, by rfl⟩ : syracuseStep 3135689 = 2351767) B2351767
theorem B2750665 : Blo 1628513 2750665 := bstep (se 2 (by rfl) ⟨1031499, by rfl⟩ : syracuseStep 2750665 = 2062999) B2062999
theorem B1833223 : Blo 1628513 1833223 := bstep (se 1 (by rfl) ⟨1374917, by rfl⟩ : syracuseStep 1833223 = 2749835) B2749835
theorem B3479851 : Blo 1628513 3479851 := bstep (se 1 (by rfl) ⟨2609888, by rfl⟩ : syracuseStep 3479851 = 5219777) B5219777
theorem B3479927 : Blo 1628513 3479927 := bstep (se 1 (by rfl) ⟨2609945, by rfl⟩ : syracuseStep 3479927 = 5219891) B5219891
theorem B1628551 : Blo 1628513 1628551 := bstep (se 1 (by rfl) ⟨1221413, by rfl⟩ : syracuseStep 1628551 = 2442827) B2442827
theorem B1628559 : Blo 1628513 1628559 := bstep (se 1 (by rfl) ⟨1221419, by rfl⟩ : syracuseStep 1628559 = 2442839) B2442839
theorem B4954553 : Blo 1628513 4954553 := bstep (se 2 (by rfl) ⟨1857957, by rfl⟩ : syracuseStep 4954553 = 3715915) B3715915
theorem B1628603 : Blo 1628513 1628603 := bstep (se 1 (by rfl) ⟨1221452, by rfl⟩ : syracuseStep 1628603 = 2442905) B2442905
theorem B1833403 : Blo 1628513 1833403 := bstep (se 1 (by rfl) ⟨1375052, by rfl⟩ : syracuseStep 1833403 = 2750105) B2750105
theorem B3348937 : Blo 1628513 3348937 := bstep (se 2 (by rfl) ⟨1255851, by rfl⟩ : syracuseStep 3348937 = 2511703) B2511703
theorem B3094985 : Blo 1628513 3094985 := bstep (se 2 (by rfl) ⟨1160619, by rfl⟩ : syracuseStep 3094985 = 2321239) B2321239
theorem B4954625 : Blo 1628513 4954625 := bstep (se 2 (by rfl) ⟨1857984, by rfl⟩ : syracuseStep 4954625 = 3715969) B3715969
theorem B4127233 : Blo 1628513 4127233 := bstep (se 2 (by rfl) ⟨1547712, by rfl⟩ : syracuseStep 4127233 = 3095425) B3095425
theorem B1628679 : Blo 1628513 1628679 := bstep (se 1 (by rfl) ⟨1221509, by rfl⟩ : syracuseStep 1628679 = 2443019) B2443019
theorem B1628687 : Blo 1628513 1628687 := bstep (se 1 (by rfl) ⟨1221515, by rfl⟩ : syracuseStep 1628687 = 2443031) B2443031
theorem B1628731 : Blo 1628513 1628731 := bstep (se 1 (by rfl) ⟨1221548, by rfl⟩ : syracuseStep 1628731 = 2443097) B2443097
theorem B6183485 : Blo 1628513 6183485 := bstep (se 3 (by rfl) ⟨1159403, by rfl⟩ : syracuseStep 6183485 = 2318807) B2318807
theorem B1628807 : Blo 1628513 1628807 := bstep (se 1 (by rfl) ⟨1221605, by rfl⟩ : syracuseStep 1628807 = 2443211) B2443211
theorem B3668615 : Blo 1628513 3668615 := bstep (se 1 (by rfl) ⟨2751461, by rfl⟩ : syracuseStep 3668615 = 5502923) B5502923
theorem B1628815 : Blo 1628513 1628815 := bstep (se 1 (by rfl) ⟨1221611, by rfl⟩ : syracuseStep 1628815 = 2443223) B2443223
theorem B1628859 : Blo 1628513 1628859 := bstep (se 1 (by rfl) ⟨1221644, by rfl⟩ : syracuseStep 1628859 = 2443289) B2443289
theorem B1628935 : Blo 1628513 1628935 := bstep (se 1 (by rfl) ⟨1221701, by rfl⟩ : syracuseStep 1628935 = 2443403) B2443403
theorem B1628943 : Blo 1628513 1628943 := bstep (se 1 (by rfl) ⟨1221707, by rfl⟩ : syracuseStep 1628943 = 2443415) B2443415
theorem B1628987 : Blo 1628513 1628987 := bstep (se 1 (by rfl) ⟨1221740, by rfl⟩ : syracuseStep 1628987 = 2443481) B2443481
theorem B3718007 : Blo 1628513 3718007 := bstep (se 1 (by rfl) ⟨2788505, by rfl⟩ : syracuseStep 3718007 = 5577011) B5577011
theorem B1629063 : Blo 1628513 1629063 := bstep (se 1 (by rfl) ⟨1221797, by rfl⟩ : syracuseStep 1629063 = 2443595) B2443595
theorem B2751367 : Blo 1628513 2751367 := bstep (se 1 (by rfl) ⟨2063525, by rfl⟩ : syracuseStep 2751367 = 4127051) B4127051
theorem B1629071 : Blo 1628513 1629071 := bstep (se 1 (by rfl) ⟨1221803, by rfl⟩ : syracuseStep 1629071 = 2443607) B2443607
theorem B1833871 : Blo 1628513 1833871 := bstep (se 1 (by rfl) ⟨1375403, by rfl⟩ : syracuseStep 1833871 = 2750807) B2750807
theorem B2202553 : Blo 1628513 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B1629115 : Blo 1628513 1629115 := bstep (se 1 (by rfl) ⟨1221836, by rfl⟩ : syracuseStep 1629115 = 2443673) B2443673
theorem B4021249 : Blo 1628513 4021249 := bstep (se 2 (by rfl) ⟨1507968, by rfl⟩ : syracuseStep 4021249 = 3015937) B3015937
theorem B1629191 : Blo 1628513 1629191 := bstep (se 1 (by rfl) ⟨1221893, by rfl⟩ : syracuseStep 1629191 = 2443787) B2443787
theorem B1629199 : Blo 1628513 1629199 := bstep (se 1 (by rfl) ⟨1221899, by rfl⟩ : syracuseStep 1629199 = 2443799) B2443799
theorem B1629243 : Blo 1628513 1629243 := bstep (se 1 (by rfl) ⟨1221932, by rfl⟩ : syracuseStep 1629243 = 2443865) B2443865
theorem B1629319 : Blo 1628513 1629319 := bstep (se 1 (by rfl) ⟨1221989, by rfl⟩ : syracuseStep 1629319 = 2443979) B2443979
theorem B2063495 : Blo 1628513 2063495 := bstep (se 1 (by rfl) ⟨1547621, by rfl⟩ : syracuseStep 2063495 = 3095243) B3095243
theorem B1629327 : Blo 1628513 1629327 := bstep (se 1 (by rfl) ⟨1221995, by rfl⟩ : syracuseStep 1629327 = 2443991) B2443991
theorem B1629371 : Blo 1628513 1629371 := bstep (se 1 (by rfl) ⟨1222028, by rfl⟩ : syracuseStep 1629371 = 2444057) B2444057
theorem B4078793 : Blo 1628513 4078793 := bstep (se 2 (by rfl) ⟨1529547, by rfl⟩ : syracuseStep 4078793 = 3059095) B3059095
theorem B79289549 : Blo 1628513 79289549 := bstep (se 3 (by rfl) ⟨14866790, by rfl⟩ : syracuseStep 79289549 = 29733581) B29733581
theorem B1629447 : Blo 1628513 1629447 := bstep (se 1 (by rfl) ⟨1222085, by rfl⟩ : syracuseStep 1629447 = 2444171) B2444171
theorem B1629455 : Blo 1628513 1629455 := bstep (se 1 (by rfl) ⟨1222091, by rfl⟩ : syracuseStep 1629455 = 2444183) B2444183
theorem B12369185 : Blo 1628513 12369185 := bstep (se 2 (by rfl) ⟨4638444, by rfl⟩ : syracuseStep 12369185 = 9276889) B9276889
theorem B1629499 : Blo 1628513 1629499 := bstep (se 1 (by rfl) ⟨1222124, by rfl⟩ : syracuseStep 1629499 = 2444249) B2444249
theorem B1629575 : Blo 1628513 1629575 := bstep (se 1 (by rfl) ⟨1222181, by rfl⟩ : syracuseStep 1629575 = 2444363) B2444363
theorem B4406663 : Blo 1628513 4406663 := bstep (se 1 (by rfl) ⟨3304997, by rfl⟩ : syracuseStep 4406663 = 6609995) B6609995
theorem B1629583 : Blo 1628513 1629583 := bstep (se 1 (by rfl) ⟨1222187, by rfl⟩ : syracuseStep 1629583 = 2444375) B2444375
theorem B1629627 : Blo 1628513 1629627 := bstep (se 1 (by rfl) ⟨1222220, by rfl⟩ : syracuseStep 1629627 = 2444441) B2444441
theorem B1629703 : Blo 1628513 1629703 := bstep (se 1 (by rfl) ⟨1222277, by rfl⟩ : syracuseStep 1629703 = 2444555) B2444555
theorem B1629711 : Blo 1628513 1629711 := bstep (se 1 (by rfl) ⟨1222283, by rfl⟩ : syracuseStep 1629711 = 2444567) B2444567
theorem B1629755 : Blo 1628513 1629755 := bstep (se 1 (by rfl) ⟨1222316, by rfl⟩ : syracuseStep 1629755 = 2444633) B2444633
theorem B35225189 : Blo 1628513 35225189 := bstep (se 4 (by rfl) ⟨3302361, by rfl⟩ : syracuseStep 35225189 = 6604723) B6604723
theorem B1629831 : Blo 1628513 1629831 := bstep (se 1 (by rfl) ⟨1222373, by rfl⟩ : syracuseStep 1629831 = 2444747) B2444747
theorem B1629839 : Blo 1628513 1629839 := bstep (se 1 (by rfl) ⟨1222379, by rfl⟩ : syracuseStep 1629839 = 2444759) B2444759
theorem B3915449 : Blo 1628513 3915449 := bstep (se 2 (by rfl) ⟨1468293, by rfl⟩ : syracuseStep 3915449 = 2936587) B2936587
theorem B1629883 : Blo 1628513 1629883 := bstep (se 1 (by rfl) ⟨1222412, by rfl⟩ : syracuseStep 1629883 = 2444825) B2444825
theorem B1629959 : Blo 1628513 1629959 := bstep (se 1 (by rfl) ⟨1222469, by rfl⟩ : syracuseStep 1629959 = 2444939) B2444939
theorem B1629967 : Blo 1628513 1629967 := bstep (se 1 (by rfl) ⟨1222475, by rfl⟩ : syracuseStep 1629967 = 2444951) B2444951
theorem B1630011 : Blo 1628513 1630011 := bstep (se 1 (by rfl) ⟨1222508, by rfl⟩ : syracuseStep 1630011 = 2445017) B2445017
theorem B18816857 : Blo 1628513 18816857 := bstep (se 2 (by rfl) ⟨7056321, by rfl⟩ : syracuseStep 18816857 = 14112643) B14112643
theorem B1630087 : Blo 1628513 1630087 := bstep (se 1 (by rfl) ⟨1222565, by rfl⟩ : syracuseStep 1630087 = 2445131) B2445131
theorem B6610823 : Blo 1628513 6610823 := bstep (se 1 (by rfl) ⟨4958117, by rfl⟩ : syracuseStep 6610823 = 9916235) B9916235
theorem B1630095 : Blo 1628513 1630095 := bstep (se 1 (by rfl) ⟨1222571, by rfl⟩ : syracuseStep 1630095 = 2445143) B2445143
theorem B1630139 : Blo 1628513 1630139 := bstep (se 1 (by rfl) ⟨1222604, by rfl⟩ : syracuseStep 1630139 = 2445209) B2445209
theorem B5292047 : Blo 1628513 5292047 := bstep (se 1 (by rfl) ⟨3969035, by rfl⟩ : syracuseStep 5292047 = 7938071) B7938071
theorem B1630247 : Blo 1628513 1630247 := bstep (se 1 (by rfl) ⟨1222685, by rfl⟩ : syracuseStep 1630247 = 2445371) B2445371
theorem B1630287 : Blo 1628513 1630287 := bstep (se 1 (by rfl) ⟨1222715, by rfl⟩ : syracuseStep 1630287 = 2445431) B2445431
theorem B1630303 : Blo 1628513 1630303 := bstep (se 1 (by rfl) ⟨1222727, by rfl⟩ : syracuseStep 1630303 = 2445455) B2445455
theorem B1630331 : Blo 1628513 1630331 := bstep (se 1 (by rfl) ⟨1222748, by rfl⟩ : syracuseStep 1630331 = 2445497) B2445497
theorem B1630383 : Blo 1628513 1630383 := bstep (se 1 (by rfl) ⟨1222787, by rfl⟩ : syracuseStep 1630383 = 2445575) B2445575
theorem B1630407 : Blo 1628513 1630407 := bstep (se 1 (by rfl) ⟨1222805, by rfl⟩ : syracuseStep 1630407 = 2445611) B2445611
theorem B1630427 : Blo 1628513 1630427 := bstep (se 1 (by rfl) ⟨1222820, by rfl⟩ : syracuseStep 1630427 = 2445641) B2445641
theorem B1630503 : Blo 1628513 1630503 := bstep (se 1 (by rfl) ⟨1222877, by rfl⟩ : syracuseStep 1630503 = 2445755) B2445755
theorem B12378419 : Blo 1628513 12378419 := bstep (se 1 (by rfl) ⟨9283814, by rfl⟩ : syracuseStep 12378419 = 18567629) B18567629
theorem B8249687 : Blo 1628513 8249687 := bstep (se 1 (by rfl) ⟨6187265, by rfl⟩ : syracuseStep 8249687 = 12374531) B12374531
theorem B5497307 : Blo 1628513 5497307 := bstep (se 1 (by rfl) ⟨4122980, by rfl⟩ : syracuseStep 5497307 = 8245961) B8245961
theorem B17187337 : Blo 1628513 17187337 := bstep (se 2 (by rfl) ⟨6445251, by rfl⟩ : syracuseStep 17187337 = 12890503) B12890503
theorem B4465249 : Blo 1628513 4465249 := bstep (se 2 (by rfl) ⟨1674468, by rfl⟩ : syracuseStep 4465249 = 3348937) B3348937
theorem B12370643 : Blo 1628513 12370643 := bstep (se 1 (by rfl) ⟨9277982, by rfl⟩ : syracuseStep 12370643 = 18555965) B18555965
theorem B4956887 : Blo 1628513 4956887 := bstep (se 1 (by rfl) ⟨3717665, by rfl⟩ : syracuseStep 4956887 = 7435331) B7435331
theorem B4178783 : Blo 1628513 4178783 := bstep (se 1 (by rfl) ⟨3134087, by rfl⟩ : syracuseStep 4178783 = 6268175) B6268175
theorem B3392363 : Blo 1628513 3392363 := bstep (se 1 (by rfl) ⟨2544272, by rfl⟩ : syracuseStep 3392363 = 5088545) B5088545
theorem B6185915 : Blo 1628513 6185915 := bstep (se 1 (by rfl) ⟨4639436, by rfl⟩ : syracuseStep 6185915 = 9278873) B9278873
theorem B15271031 : Blo 1628513 15271031 := bstep (se 1 (by rfl) ⟨11453273, by rfl⟩ : syracuseStep 15271031 = 22906547) B22906547
theorem B5498009 : Blo 1628513 5498009 := bstep (se 2 (by rfl) ⟨2061753, by rfl⟩ : syracuseStep 5498009 = 4123507) B4123507
theorem B13919435 : Blo 1628513 13919435 := bstep (se 1 (by rfl) ⟨10439576, by rfl⟩ : syracuseStep 13919435 = 20879153) B20879153
theorem B5875031 : Blo 1628513 5875031 := bstep (se 1 (by rfl) ⟨4406273, by rfl⟩ : syracuseStep 5875031 = 8812547) B8812547
theorem B2090459 : Blo 1628513 2090459 := bstep (se 1 (by rfl) ⟨1567844, by rfl⟩ : syracuseStep 2090459 = 3135689) B3135689
theorem B4638217 : Blo 1628513 4638217 := bstep (se 2 (by rfl) ⟨1739331, by rfl⟩ : syracuseStep 4638217 = 3478663) B3478663
theorem B2442791 : Blo 1628513 2442791 := bstep (se 1 (by rfl) ⟨1832093, by rfl⟩ : syracuseStep 2442791 = 3664187) B3664187
theorem B2442875 : Blo 1628513 2442875 := bstep (se 1 (by rfl) ⟨1832156, by rfl⟩ : syracuseStep 2442875 = 3664313) B3664313
theorem B3303035 : Blo 1628513 3303035 := bstep (se 1 (by rfl) ⟨2477276, by rfl⟩ : syracuseStep 3303035 = 4954553) B4954553
theorem B3303083 : Blo 1628513 3303083 := bstep (se 1 (by rfl) ⟨2477312, by rfl⟩ : syracuseStep 3303083 = 4954625) B4954625
theorem B4122323 : Blo 1628513 4122323 := bstep (se 1 (by rfl) ⟨3091742, by rfl⟩ : syracuseStep 4122323 = 6183485) B6183485
theorem B2443001 : Blo 1628513 2443001 := bstep (se 2 (by rfl) ⟨916125, by rfl⟩ : syracuseStep 2443001 = 1832251) B1832251
theorem B2443103 : Blo 1628513 2443103 := bstep (se 1 (by rfl) ⟨1832327, by rfl⟩ : syracuseStep 2443103 = 3664655) B3664655
theorem B4638559 : Blo 1628513 4638559 := bstep (se 1 (by rfl) ⟨3478919, by rfl⟩ : syracuseStep 4638559 = 6957839) B6957839
theorem B2443115 : Blo 1628513 2443115 := bstep (se 1 (by rfl) ⟨1832336, by rfl⟩ : syracuseStep 2443115 = 3664673) B3664673
theorem B37636001 : Blo 1628513 37636001 := bstep (se 2 (by rfl) ⟨14113500, by rfl⟩ : syracuseStep 37636001 = 28227001) B28227001
theorem B33458183 : Blo 1628513 33458183 := bstep (se 1 (by rfl) ⟨25093637, by rfl⟩ : syracuseStep 33458183 = 50187275) B50187275
theorem B2443343 : Blo 1628513 2443343 := bstep (se 1 (by rfl) ⟨1832507, by rfl⟩ : syracuseStep 2443343 = 3665015) B3665015
theorem B2443463 : Blo 1628513 2443463 := bstep (se 1 (by rfl) ⟨1832597, by rfl⟩ : syracuseStep 2443463 = 3665195) B3665195
theorem B5499197 : Blo 1628513 5499197 := bstep (se 3 (by rfl) ⟨1031099, by rfl⟩ : syracuseStep 5499197 = 2062199) B2062199
theorem B2443625 : Blo 1628513 2443625 := bstep (se 2 (by rfl) ⟨916359, by rfl⟩ : syracuseStep 2443625 = 1832719) B1832719
theorem B2443703 : Blo 1628513 2443703 := bstep (se 1 (by rfl) ⟨1832777, by rfl⟩ : syracuseStep 2443703 = 3665555) B3665555
theorem B2443739 : Blo 1628513 2443739 := bstep (se 1 (by rfl) ⟨1832804, by rfl⟩ : syracuseStep 2443739 = 3665609) B3665609
theorem B19818989 : Blo 1628513 19818989 := bstep (se 3 (by rfl) ⟨3716060, by rfl⟩ : syracuseStep 19818989 = 7432121) B7432121
theorem B12544571 : Blo 1628513 12544571 := bstep (se 1 (by rfl) ⟨9408428, by rfl⟩ : syracuseStep 12544571 = 18816857) B18816857
theorem B3664583 : Blo 1628513 3664583 := bstep (se 1 (by rfl) ⟨2748437, by rfl⟩ : syracuseStep 3664583 = 5496875) B5496875
theorem B44575433 : Blo 1628513 44575433 := bstep (se 2 (by rfl) ⟨16715787, by rfl⟩ : syracuseStep 44575433 = 33431575) B33431575
theorem B12544723 : Blo 1628513 12544723 := bstep (se 1 (by rfl) ⟨9408542, by rfl⟩ : syracuseStep 12544723 = 18817085) B18817085
theorem B4639447 : Blo 1628513 4639447 := bstep (se 1 (by rfl) ⟨3479585, by rfl⟩ : syracuseStep 4639447 = 6959171) B6959171
theorem B13929245 : Blo 1628513 13929245 := bstep (se 3 (by rfl) ⟨2611733, by rfl⟩ : syracuseStep 13929245 = 5223467) B5223467
theorem B60271397 : Blo 1628513 60271397 := bstep (se 4 (by rfl) ⟨5650443, by rfl⟩ : syracuseStep 60271397 = 11300887) B11300887
theorem B4123487 : Blo 1628513 4123487 := bstep (se 1 (by rfl) ⟨3092615, by rfl⟩ : syracuseStep 4123487 = 6185231) B6185231
theorem B11750291 : Blo 1628513 11750291 := bstep (se 1 (by rfl) ⟨8812718, by rfl⟩ : syracuseStep 11750291 = 17625437) B17625437
theorem B2444207 : Blo 1628513 2444207 := bstep (se 1 (by rfl) ⟨1833155, by rfl⟩ : syracuseStep 2444207 = 3666311) B3666311
theorem B4639675 : Blo 1628513 4639675 := bstep (se 1 (by rfl) ⟨3479756, by rfl⟩ : syracuseStep 4639675 = 6959513) B6959513
theorem B9276389 : Blo 1628513 9276389 := bstep (se 4 (by rfl) ⟨869661, by rfl⟩ : syracuseStep 9276389 = 1739323) B1739323
theorem B2444297 : Blo 1628513 2444297 := bstep (se 2 (by rfl) ⟨916611, by rfl⟩ : syracuseStep 2444297 = 1833223) B1833223
theorem B2444327 : Blo 1628513 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B4639801 : Blo 1628513 4639801 := bstep (se 2 (by rfl) ⟨1739925, by rfl⟩ : syracuseStep 4639801 = 3479851) B3479851
theorem B5950543 : Blo 1628513 5950543 := bstep (se 1 (by rfl) ⟨4462907, by rfl⟩ : syracuseStep 5950543 = 8925815) B8925815
theorem B6188147 : Blo 1628513 6188147 := bstep (se 1 (by rfl) ⟨4641110, by rfl⟩ : syracuseStep 6188147 = 9282221) B9282221
theorem B2444411 : Blo 1628513 2444411 := bstep (se 1 (by rfl) ⟨1833308, by rfl⟩ : syracuseStep 2444411 = 3666617) B3666617
theorem B5500061 : Blo 1628513 5500061 := bstep (se 3 (by rfl) ⟨1031261, by rfl⟩ : syracuseStep 5500061 = 2062523) B2062523
theorem B2444537 : Blo 1628513 2444537 := bstep (se 2 (by rfl) ⟨916701, by rfl⟩ : syracuseStep 2444537 = 1833403) B1833403
theorem B8244503 : Blo 1628513 8244503 := bstep (se 1 (by rfl) ⟨6183377, by rfl⟩ : syracuseStep 8244503 = 12366755) B12366755
theorem B9915671 : Blo 1628513 9915671 := bstep (se 1 (by rfl) ⟨7436753, by rfl⟩ : syracuseStep 9915671 = 14873507) B14873507
theorem B2444639 : Blo 1628513 2444639 := bstep (se 1 (by rfl) ⟨1833479, by rfl⟩ : syracuseStep 2444639 = 3666959) B3666959
theorem B2444651 : Blo 1628513 2444651 := bstep (se 1 (by rfl) ⟨1833488, by rfl⟩ : syracuseStep 2444651 = 3666977) B3666977
theorem B4402727 : Blo 1628513 4402727 := bstep (se 1 (by rfl) ⟨3302045, by rfl⟩ : syracuseStep 4402727 = 6604091) B6604091
theorem B3665447 : Blo 1628513 3665447 := bstep (se 1 (by rfl) ⟨2749085, by rfl⟩ : syracuseStep 3665447 = 5498171) B5498171
theorem B2788921 : Blo 1628513 2788921 := bstep (se 2 (by rfl) ⟨1045845, by rfl⟩ : syracuseStep 2788921 = 2091691) B2091691
theorem B2444879 : Blo 1628513 2444879 := bstep (se 1 (by rfl) ⟨1833659, by rfl⟩ : syracuseStep 2444879 = 3667319) B3667319
theorem B35245691 : Blo 1628513 35245691 := bstep (se 1 (by rfl) ⟨26434268, by rfl⟩ : syracuseStep 35245691 = 52868537) B52868537
theorem B5500601 : Blo 1628513 5500601 := bstep (se 2 (by rfl) ⟨2062725, by rfl⟩ : syracuseStep 5500601 = 4125451) B4125451
theorem B11751101 : Blo 1628513 11751101 := bstep (se 3 (by rfl) ⟨2203331, by rfl⟩ : syracuseStep 11751101 = 4406663) B4406663
theorem B2444999 : Blo 1628513 2444999 := bstep (se 1 (by rfl) ⟨1833749, by rfl⟩ : syracuseStep 2444999 = 3667499) B3667499
theorem B8253251 : Blo 1628513 8253251 := bstep (se 1 (by rfl) ⟨6189938, by rfl⟩ : syracuseStep 8253251 = 12379877) B12379877
theorem B2445161 : Blo 1628513 2445161 := bstep (se 2 (by rfl) ⟨916935, by rfl⟩ : syracuseStep 2445161 = 1833871) B1833871
theorem B3665771 : Blo 1628513 3665771 := bstep (se 1 (by rfl) ⟨2749328, by rfl⟩ : syracuseStep 3665771 = 5498657) B5498657
theorem B3665825 : Blo 1628513 3665825 := bstep (se 2 (by rfl) ⟨1374684, by rfl⟩ : syracuseStep 3665825 = 2749369) B2749369
theorem B2936737 : Blo 1628513 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B4124591 : Blo 1628513 4124591 := bstep (se 1 (by rfl) ⟨3093443, by rfl⟩ : syracuseStep 4124591 = 6186887) B6186887
theorem B2748343 : Blo 1628513 2748343 := bstep (se 1 (by rfl) ⟨2061257, by rfl⟩ : syracuseStep 2748343 = 4122515) B4122515
theorem B2445239 : Blo 1628513 2445239 := bstep (se 1 (by rfl) ⟨1833929, by rfl⟩ : syracuseStep 2445239 = 3667859) B3667859
theorem B3092411 : Blo 1628513 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B9408449 : Blo 1628513 9408449 := bstep (se 2 (by rfl) ⟨3528168, by rfl⟩ : syracuseStep 9408449 = 7056337) B7056337
theorem B2445275 : Blo 1628513 2445275 := bstep (se 1 (by rfl) ⟨1833956, by rfl⟩ : syracuseStep 2445275 = 3667913) B3667913
theorem B5361665 : Blo 1628513 5361665 := bstep (se 2 (by rfl) ⟨2010624, by rfl⟩ : syracuseStep 5361665 = 4021249) B4021249
theorem B12374045 : Blo 1628513 12374045 := bstep (se 3 (by rfl) ⟨2320133, by rfl⟩ : syracuseStep 12374045 = 4640267) B4640267
theorem B2748539 : Blo 1628513 2748539 := bstep (se 1 (by rfl) ⟨2061404, by rfl⟩ : syracuseStep 2748539 = 4122809) B4122809
theorem B211513517 : Blo 1628513 211513517 := bstep (se 3 (by rfl) ⟨39658784, by rfl⟩ : syracuseStep 211513517 = 79317569) B79317569
theorem B3666167 : Blo 1628513 3666167 := bstep (se 1 (by rfl) ⟨2749625, by rfl⟩ : syracuseStep 3666167 = 5499251) B5499251
theorem B5222647 : Blo 1628513 5222647 := bstep (se 1 (by rfl) ⟨3916985, by rfl⟩ : syracuseStep 5222647 = 7833971) B7833971
theorem B5501195 : Blo 1628513 5501195 := bstep (se 1 (by rfl) ⟨4125896, by rfl⟩ : syracuseStep 5501195 = 8251793) B8251793
theorem B3092843 : Blo 1628513 3092843 := bstep (se 1 (by rfl) ⟨2319632, by rfl⟩ : syracuseStep 3092843 = 4639265) B4639265
theorem B3092897 : Blo 1628513 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B2445743 : Blo 1628513 2445743 := bstep (se 1 (by rfl) ⟨1834307, by rfl⟩ : syracuseStep 2445743 = 3668615) B3668615
theorem B2748937 : Blo 1628513 2748937 := bstep (se 2 (by rfl) ⟨1030851, by rfl⟩ : syracuseStep 2748937 = 2061703) B2061703
theorem B5501465 : Blo 1628513 5501465 := bstep (se 2 (by rfl) ⟨2063049, by rfl⟩ : syracuseStep 5501465 = 4126099) B4126099
theorem B2478671 : Blo 1628513 2478671 := bstep (se 1 (by rfl) ⟨1859003, by rfl⟩ : syracuseStep 2478671 = 3718007) B3718007
theorem B8811143 : Blo 1628513 8811143 := bstep (se 1 (by rfl) ⟨6608357, by rfl⟩ : syracuseStep 8811143 = 13216715) B13216715
theorem B2749099 : Blo 1628513 2749099 := bstep (se 1 (by rfl) ⟨2061824, by rfl⟩ : syracuseStep 2749099 = 4123649) B4123649
theorem B6189817 : Blo 1628513 6189817 := bstep (se 2 (by rfl) ⟨2321181, by rfl⟩ : syracuseStep 6189817 = 4642363) B4642363
theorem B52859699 : Blo 1628513 52859699 := bstep (se 1 (by rfl) ⟨39644774, by rfl⟩ : syracuseStep 52859699 = 79289549) B79289549
theorem B3666761 : Blo 1628513 3666761 := bstep (se 2 (by rfl) ⟨1375035, by rfl⟩ : syracuseStep 3666761 = 2750071) B2750071
theorem B8246123 : Blo 1628513 8246123 := bstep (se 1 (by rfl) ⟨6184592, by rfl⟩ : syracuseStep 8246123 = 12369185) B12369185
theorem B5223275 : Blo 1628513 5223275 := bstep (se 1 (by rfl) ⟨3917456, by rfl⟩ : syracuseStep 5223275 = 7834913) B7834913
theorem B1651655 : Blo 1628513 1651655 := bstep (se 1 (by rfl) ⟨1238741, by rfl⟩ : syracuseStep 1651655 = 2477483) B2477483
theorem B2749403 : Blo 1628513 2749403 := bstep (se 1 (by rfl) ⟨2062052, by rfl⟩ : syracuseStep 2749403 = 4124105) B4124105
theorem B23483459 : Blo 1628513 23483459 := bstep (se 1 (by rfl) ⟨17612594, by rfl⟩ : syracuseStep 23483459 = 35225189) B35225189
theorem B4125775 : Blo 1628513 4125775 := bstep (se 1 (by rfl) ⟨3094331, by rfl⟩ : syracuseStep 4125775 = 6188663) B6188663
theorem B2610299 : Blo 1628513 2610299 := bstep (se 1 (by rfl) ⟨1957724, by rfl⟩ : syracuseStep 2610299 = 3915449) B3915449
theorem B2749639 : Blo 1628513 2749639 := bstep (se 1 (by rfl) ⟨2062229, by rfl⟩ : syracuseStep 2749639 = 4124459) B4124459
theorem B1832287 : Blo 1628513 1832287 := bstep (se 1 (by rfl) ⟨1374215, by rfl⟩ : syracuseStep 1832287 = 2748431) B2748431
theorem B2749801 : Blo 1628513 2749801 := bstep (se 2 (by rfl) ⟨1031175, by rfl⟩ : syracuseStep 2749801 = 2062351) B2062351
theorem B8246771 : Blo 1628513 8246771 := bstep (se 1 (by rfl) ⟨6185078, by rfl⟩ : syracuseStep 8246771 = 12370157) B12370157
theorem B15668747 : Blo 1628513 15668747 := bstep (se 1 (by rfl) ⟨11751560, by rfl⟩ : syracuseStep 15668747 = 23503121) B23503121
theorem B13915745 : Blo 1628513 13915745 := bstep (se 2 (by rfl) ⟨5218404, by rfl⟩ : syracuseStep 13915745 = 10436809) B10436809
theorem B3667553 : Blo 1628513 3667553 := bstep (se 2 (by rfl) ⟨1375332, by rfl⟩ : syracuseStep 3667553 = 2750665) B2750665
theorem B5502599 : Blo 1628513 5502599 := bstep (se 1 (by rfl) ⟨4126949, by rfl⟩ : syracuseStep 5502599 = 8253899) B8253899
theorem B5502653 : Blo 1628513 5502653 := bstep (se 3 (by rfl) ⟨1031747, by rfl⟩ : syracuseStep 5502653 = 2063495) B2063495
theorem B1832647 : Blo 1628513 1832647 := bstep (se 1 (by rfl) ⟨1374485, by rfl⟩ : syracuseStep 1832647 = 2748971) B2748971
theorem B7059143 : Blo 1628513 7059143 := bstep (se 1 (by rfl) ⟨5294357, by rfl⟩ : syracuseStep 7059143 = 10588715) B10588715
theorem B4126423 : Blo 1628513 4126423 := bstep (se 1 (by rfl) ⟨3094817, by rfl⟩ : syracuseStep 4126423 = 6189635) B6189635
theorem B15652601 : Blo 1628513 15652601 := bstep (se 2 (by rfl) ⟨5869725, by rfl⟩ : syracuseStep 15652601 = 11739451) B11739451
theorem B19830521 : Blo 1628513 19830521 := bstep (se 2 (by rfl) ⟨7436445, by rfl⟩ : syracuseStep 19830521 = 14872891) B14872891
theorem B5871455 : Blo 1628513 5871455 := bstep (se 1 (by rfl) ⟨4403591, by rfl⟩ : syracuseStep 5871455 = 8807183) B8807183
theorem B5502815 : Blo 1628513 5502815 := bstep (se 1 (by rfl) ⟨4127111, by rfl⟩ : syracuseStep 5502815 = 8254223) B8254223
theorem B6608749 : Blo 1628513 6608749 := bstep (se 3 (by rfl) ⟨1239140, by rfl⟩ : syracuseStep 6608749 = 2478281) B2478281
theorem B10876781 : Blo 1628513 10876781 := bstep (se 3 (by rfl) ⟨2039396, by rfl⟩ : syracuseStep 10876781 = 4078793) B4078793
theorem B2062255 : Blo 1628513 2062255 := bstep (se 1 (by rfl) ⟨1546691, by rfl⟩ : syracuseStep 2062255 = 3093383) B3093383
theorem B3667895 : Blo 1628513 3667895 := bstep (se 1 (by rfl) ⟨2750921, by rfl⟩ : syracuseStep 3667895 = 5501843) B5501843
theorem B3479483 : Blo 1628513 3479483 := bstep (se 1 (by rfl) ⟨2609612, by rfl⟩ : syracuseStep 3479483 = 5219225) B5219225
theorem B2750395 : Blo 1628513 2750395 := bstep (se 1 (by rfl) ⟨2062796, by rfl⟩ : syracuseStep 2750395 = 4125593) B4125593
theorem B26433485 : Blo 1628513 26433485 := bstep (se 3 (by rfl) ⟨4956278, by rfl⟩ : syracuseStep 26433485 = 9912557) B9912557
theorem B5502977 : Blo 1628513 5502977 := bstep (se 2 (by rfl) ⟨2063616, by rfl⟩ : syracuseStep 5502977 = 4127233) B4127233
theorem B17618951 : Blo 1628513 17618951 := bstep (se 1 (by rfl) ⟨13214213, by rfl⟩ : syracuseStep 17618951 = 26428427) B26428427
theorem B4126727 : Blo 1628513 4126727 := bstep (se 1 (by rfl) ⟨3095045, by rfl⟩ : syracuseStep 4126727 = 6190091) B6190091
theorem B3094537 : Blo 1628513 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B2750503 : Blo 1628513 2750503 := bstep (se 1 (by rfl) ⟨2062877, by rfl⟩ : syracuseStep 2750503 = 4125755) B4125755
theorem B9279805 : Blo 1628513 9279805 := bstep (se 3 (by rfl) ⟨1739963, by rfl⟩ : syracuseStep 9279805 = 3479927) B3479927
theorem B2611529 : Blo 1628513 2611529 := bstep (se 2 (by rfl) ⟨979323, by rfl⟩ : syracuseStep 2611529 = 1958647) B1958647
theorem B2750827 : Blo 1628513 2750827 := bstep (se 1 (by rfl) ⟨2063120, by rfl⟩ : syracuseStep 2750827 = 4126241) B4126241
theorem B1628539 : Blo 1628513 1628539 := bstep (se 1 (by rfl) ⟨1221404, by rfl⟩ : syracuseStep 1628539 = 2442809) B2442809
theorem B1628591 : Blo 1628513 1628591 := bstep (se 1 (by rfl) ⟨1221443, by rfl⟩ : syracuseStep 1628591 = 2442887) B2442887
theorem B2644411 : Blo 1628513 2644411 := bstep (se 1 (by rfl) ⟨1983308, by rfl⟩ : syracuseStep 2644411 = 3966617) B3966617
theorem B1628615 : Blo 1628513 1628615 := bstep (se 1 (by rfl) ⟨1221461, by rfl⟩ : syracuseStep 1628615 = 2442923) B2442923
theorem B1628635 : Blo 1628513 1628635 := bstep (se 1 (by rfl) ⟨1221476, by rfl⟩ : syracuseStep 1628635 = 2442953) B2442953
theorem B3668489 : Blo 1628513 3668489 := bstep (se 2 (by rfl) ⟨1375683, by rfl⟩ : syracuseStep 3668489 = 2751367) B2751367
theorem B1628711 : Blo 1628513 1628711 := bstep (se 1 (by rfl) ⟨1221533, by rfl⟩ : syracuseStep 1628711 = 2443067) B2443067
theorem B1833511 : Blo 1628513 1833511 := bstep (se 1 (by rfl) ⟨1375133, by rfl⟩ : syracuseStep 1833511 = 2750267) B2750267
theorem B1956431 : Blo 1628513 1956431 := bstep (se 1 (by rfl) ⟨1467323, by rfl⟩ : syracuseStep 1956431 = 2934647) B2934647
theorem B1628751 : Blo 1628513 1628751 := bstep (se 1 (by rfl) ⟨1221563, by rfl⟩ : syracuseStep 1628751 = 2443127) B2443127
theorem B1628767 : Blo 1628513 1628767 := bstep (se 1 (by rfl) ⟨1221575, by rfl⟩ : syracuseStep 1628767 = 2443151) B2443151
theorem B1628795 : Blo 1628513 1628795 := bstep (se 1 (by rfl) ⟨1221596, by rfl⟩ : syracuseStep 1628795 = 2443193) B2443193
theorem B1628847 : Blo 1628513 1628847 := bstep (se 1 (by rfl) ⟨1221635, by rfl⟩ : syracuseStep 1628847 = 2443271) B2443271
theorem B1628871 : Blo 1628513 1628871 := bstep (se 1 (by rfl) ⟨1221653, by rfl⟩ : syracuseStep 1628871 = 2443307) B2443307
theorem B1628891 : Blo 1628513 1628891 := bstep (se 1 (by rfl) ⟨1221668, by rfl⟩ : syracuseStep 1628891 = 2443337) B2443337
theorem B45218549 : Blo 1628513 45218549 := bstep (se 5 (by rfl) ⟨2119619, by rfl⟩ : syracuseStep 45218549 = 4239239) B4239239
theorem B8248067 : Blo 1628513 8248067 := bstep (se 1 (by rfl) ⟨6186050, by rfl⟩ : syracuseStep 8248067 = 12372101) B12372101
theorem B1628967 : Blo 1628513 1628967 := bstep (se 1 (by rfl) ⟨1221725, by rfl⟩ : syracuseStep 1628967 = 2443451) B2443451
theorem B1629007 : Blo 1628513 1629007 := bstep (se 1 (by rfl) ⟨1221755, by rfl⟩ : syracuseStep 1629007 = 2443511) B2443511
theorem B1629023 : Blo 1628513 1629023 := bstep (se 1 (by rfl) ⟨1221767, by rfl⟩ : syracuseStep 1629023 = 2443535) B2443535
theorem B1629051 : Blo 1628513 1629051 := bstep (se 1 (by rfl) ⟨1221788, by rfl⟩ : syracuseStep 1629051 = 2443577) B2443577
theorem B1629103 : Blo 1628513 1629103 := bstep (se 1 (by rfl) ⟨1221827, by rfl⟩ : syracuseStep 1629103 = 2443655) B2443655
theorem B1629127 : Blo 1628513 1629127 := bstep (se 1 (by rfl) ⟨1221845, by rfl⟩ : syracuseStep 1629127 = 2443691) B2443691
theorem B1629147 : Blo 1628513 1629147 := bstep (se 1 (by rfl) ⟨1221860, by rfl⟩ : syracuseStep 1629147 = 2443721) B2443721
theorem B2063323 : Blo 1628513 2063323 := bstep (se 1 (by rfl) ⟨1547492, by rfl⟩ : syracuseStep 2063323 = 3094985) B3094985
theorem B1629223 : Blo 1628513 1629223 := bstep (se 1 (by rfl) ⟨1221917, by rfl⟩ : syracuseStep 1629223 = 2443835) B2443835
theorem B1629263 : Blo 1628513 1629263 := bstep (se 1 (by rfl) ⟨1221947, by rfl⟩ : syracuseStep 1629263 = 2443895) B2443895
theorem B1629279 : Blo 1628513 1629279 := bstep (se 1 (by rfl) ⟨1221959, by rfl⟩ : syracuseStep 1629279 = 2443919) B2443919
theorem B1629307 : Blo 1628513 1629307 := bstep (se 1 (by rfl) ⟨1221980, by rfl⟩ : syracuseStep 1629307 = 2443961) B2443961
theorem B1629359 : Blo 1628513 1629359 := bstep (se 1 (by rfl) ⟨1222019, by rfl⟩ : syracuseStep 1629359 = 2444039) B2444039
theorem B1629383 : Blo 1628513 1629383 := bstep (se 1 (by rfl) ⟨1222037, by rfl⟩ : syracuseStep 1629383 = 2444075) B2444075
theorem B1629403 : Blo 1628513 1629403 := bstep (se 1 (by rfl) ⟨1222052, by rfl⟩ : syracuseStep 1629403 = 2444105) B2444105
theorem B1629479 : Blo 1628513 1629479 := bstep (se 1 (by rfl) ⟨1222109, by rfl⟩ : syracuseStep 1629479 = 2444219) B2444219
theorem B1629519 : Blo 1628513 1629519 := bstep (se 1 (by rfl) ⟨1222139, by rfl⟩ : syracuseStep 1629519 = 2444279) B2444279
theorem B1629535 : Blo 1628513 1629535 := bstep (se 1 (by rfl) ⟨1222151, by rfl⟩ : syracuseStep 1629535 = 2444303) B2444303
theorem B1629563 : Blo 1628513 1629563 := bstep (se 1 (by rfl) ⟨1222172, by rfl⟩ : syracuseStep 1629563 = 2444345) B2444345
theorem B6610319 : Blo 1628513 6610319 := bstep (se 1 (by rfl) ⟨4957739, by rfl⟩ : syracuseStep 6610319 = 9915479) B9915479
theorem B1629615 : Blo 1628513 1629615 := bstep (se 1 (by rfl) ⟨1222211, by rfl⟩ : syracuseStep 1629615 = 2444423) B2444423
theorem B1629639 : Blo 1628513 1629639 := bstep (se 1 (by rfl) ⟨1222229, by rfl⟩ : syracuseStep 1629639 = 2444459) B2444459
theorem B1629659 : Blo 1628513 1629659 := bstep (se 1 (by rfl) ⟨1222244, by rfl⟩ : syracuseStep 1629659 = 2444489) B2444489
theorem B6184457 : Blo 1628513 6184457 := bstep (se 2 (by rfl) ⟨2319171, by rfl⟩ : syracuseStep 6184457 = 4638343) B4638343
theorem B5873185 : Blo 1628513 5873185 := bstep (se 2 (by rfl) ⟨2202444, by rfl⟩ : syracuseStep 5873185 = 4404889) B4404889
theorem B1629735 : Blo 1628513 1629735 := bstep (se 1 (by rfl) ⟨1222301, by rfl⟩ : syracuseStep 1629735 = 2444603) B2444603
theorem B1629775 : Blo 1628513 1629775 := bstep (se 1 (by rfl) ⟨1222331, by rfl⟩ : syracuseStep 1629775 = 2444663) B2444663
theorem B1629791 : Blo 1628513 1629791 := bstep (se 1 (by rfl) ⟨1222343, by rfl⟩ : syracuseStep 1629791 = 2444687) B2444687
theorem B5496443 : Blo 1628513 5496443 := bstep (se 1 (by rfl) ⟨4122332, by rfl⟩ : syracuseStep 5496443 = 8244665) B8244665
theorem B1629819 : Blo 1628513 1629819 := bstep (se 1 (by rfl) ⟨1222364, by rfl⟩ : syracuseStep 1629819 = 2444729) B2444729
theorem B18554507 : Blo 1628513 18554507 := bstep (se 1 (by rfl) ⟨13915880, by rfl⟩ : syracuseStep 18554507 = 27831761) B27831761
theorem B1629871 : Blo 1628513 1629871 := bstep (se 1 (by rfl) ⟨1222403, by rfl⟩ : syracuseStep 1629871 = 2444807) B2444807
theorem B1629895 : Blo 1628513 1629895 := bstep (se 1 (by rfl) ⟨1222421, by rfl⟩ : syracuseStep 1629895 = 2444843) B2444843
theorem B1629915 : Blo 1628513 1629915 := bstep (se 1 (by rfl) ⟨1222436, by rfl⟩ : syracuseStep 1629915 = 2444873) B2444873
theorem B26418959 : Blo 1628513 26418959 := bstep (se 1 (by rfl) ⟨19814219, by rfl⟩ : syracuseStep 26418959 = 39628439) B39628439
theorem B5496605 : Blo 1628513 5496605 := bstep (se 3 (by rfl) ⟨1030613, by rfl⟩ : syracuseStep 5496605 = 2061227) B2061227
theorem B1629991 : Blo 1628513 1629991 := bstep (se 1 (by rfl) ⟨1222493, by rfl⟩ : syracuseStep 1629991 = 2444987) B2444987
theorem B1630031 : Blo 1628513 1630031 := bstep (se 1 (by rfl) ⟨1222523, by rfl⟩ : syracuseStep 1630031 = 2445047) B2445047
theorem B1630047 : Blo 1628513 1630047 := bstep (se 1 (by rfl) ⟨1222535, by rfl⟩ : syracuseStep 1630047 = 2445071) B2445071
theorem B1630075 : Blo 1628513 1630075 := bstep (se 1 (by rfl) ⟨1222556, by rfl⟩ : syracuseStep 1630075 = 2445113) B2445113
theorem B1630127 : Blo 1628513 1630127 := bstep (se 1 (by rfl) ⟨1222595, by rfl⟩ : syracuseStep 1630127 = 2445191) B2445191
theorem B4407215 : Blo 1628513 4407215 := bstep (se 1 (by rfl) ⟨3305411, by rfl⟩ : syracuseStep 4407215 = 6610823) B6610823
theorem B1630151 : Blo 1628513 1630151 := bstep (se 1 (by rfl) ⟨1222613, by rfl⟩ : syracuseStep 1630151 = 2445227) B2445227
theorem B1630171 : Blo 1628513 1630171 := bstep (se 1 (by rfl) ⟨1222628, by rfl⟩ : syracuseStep 1630171 = 2445257) B2445257
theorem B8249363 : Blo 1628513 8249363 := bstep (se 1 (by rfl) ⟨6187022, by rfl⟩ : syracuseStep 8249363 = 12374045) B12374045
theorem B141009011 : Blo 1628513 141009011 := bstep (se 1 (by rfl) ⟨105756758, by rfl⟩ : syracuseStep 141009011 = 211513517) B211513517
theorem B1630495 : Blo 1628513 1630495 := bstep (se 1 (by rfl) ⟨1222871, by rfl⟩ : syracuseStep 1630495 = 2445743) B2445743
theorem B6963529 : Blo 1628513 6963529 := bstep (se 2 (by rfl) ⟨2611323, by rfl⟩ : syracuseStep 6963529 = 5222647) B5222647
theorem B5874095 : Blo 1628513 5874095 := bstep (se 1 (by rfl) ⟨4405571, by rfl⟩ : syracuseStep 5874095 = 8811143) B8811143
theorem B23814661 : Blo 1628513 23814661 := bstep (se 4 (by rfl) ⟨2232624, by rfl⟩ : syracuseStep 23814661 = 4465249) B4465249
theorem B2785855 : Blo 1628513 2785855 := bstep (se 1 (by rfl) ⟨2089391, by rfl⟩ : syracuseStep 2785855 = 4178783) B4178783
theorem B2261575 : Blo 1628513 2261575 := bstep (se 1 (by rfl) ⟨1696181, by rfl⟩ : syracuseStep 2261575 = 3392363) B3392363
theorem B5497415 : Blo 1628513 5497415 := bstep (se 1 (by rfl) ⟨4123061, by rfl⟩ : syracuseStep 5497415 = 8246123) B8246123
theorem B3482183 : Blo 1628513 3482183 := bstep (se 1 (by rfl) ⟨2611637, by rfl⟩ : syracuseStep 3482183 = 5223275) B5223275
theorem B15655639 : Blo 1628513 15655639 := bstep (se 1 (by rfl) ⟨11741729, by rfl⟩ : syracuseStep 15655639 = 23483459) B23483459
theorem B3916687 : Blo 1628513 3916687 := bstep (se 1 (by rfl) ⟨2937515, by rfl⟩ : syracuseStep 3916687 = 5875031) B5875031
theorem B6185929 : Blo 1628513 6185929 := bstep (se 2 (by rfl) ⟨2319723, by rfl⟩ : syracuseStep 6185929 = 4639447) B4639447
theorem B5497847 : Blo 1628513 5497847 := bstep (se 1 (by rfl) ⟨4123385, by rfl⟩ : syracuseStep 5497847 = 8246771) B8246771
theorem B10445831 : Blo 1628513 10445831 := bstep (se 1 (by rfl) ⟨7834373, by rfl⟩ : syracuseStep 10445831 = 15668747) B15668747
theorem B6186233 : Blo 1628513 6186233 := bstep (se 2 (by rfl) ⟨2319837, by rfl⟩ : syracuseStep 6186233 = 4639675) B4639675
theorem B17622323 : Blo 1628513 17622323 := bstep (se 1 (by rfl) ⟨13216742, by rfl⟩ : syracuseStep 17622323 = 26433485) B26433485
theorem B6186401 : Blo 1628513 6186401 := bstep (se 2 (by rfl) ⟨2319900, by rfl⟩ : syracuseStep 6186401 = 4639801) B4639801
theorem B2443049 : Blo 1628513 2443049 := bstep (se 2 (by rfl) ⟨916143, by rfl⟩ : syracuseStep 2443049 = 1832287) B1832287
theorem B2443055 : Blo 1628513 2443055 := bstep (se 1 (by rfl) ⟨1832291, by rfl⟩ : syracuseStep 2443055 = 3664583) B3664583
theorem B5498711 : Blo 1628513 5498711 := bstep (se 1 (by rfl) ⟨4124033, by rfl⟩ : syracuseStep 5498711 = 8248067) B8248067
theorem B7833527 : Blo 1628513 7833527 := bstep (se 1 (by rfl) ⟨5875145, by rfl⟩ : syracuseStep 7833527 = 11750291) B11750291
theorem B2443529 : Blo 1628513 2443529 := bstep (se 2 (by rfl) ⟨916323, by rfl⟩ : syracuseStep 2443529 = 1832647) B1832647
theorem B4122971 : Blo 1628513 4122971 := bstep (se 1 (by rfl) ⟨3092228, by rfl⟩ : syracuseStep 4122971 = 6184457) B6184457
theorem B2935151 : Blo 1628513 2935151 := bstep (se 1 (by rfl) ⟨2201363, by rfl⟩ : syracuseStep 2935151 = 4402727) B4402727
theorem B2443631 : Blo 1628513 2443631 := bstep (se 1 (by rfl) ⟨1832723, by rfl⟩ : syracuseStep 2443631 = 3665447) B3665447
theorem B3664295 : Blo 1628513 3664295 := bstep (se 1 (by rfl) ⟨2748221, by rfl⟩ : syracuseStep 3664295 = 5496443) B5496443
theorem B23497127 : Blo 1628513 23497127 := bstep (se 1 (by rfl) ⟨17622845, by rfl⟩ : syracuseStep 23497127 = 35245691) B35245691
theorem B7834067 : Blo 1628513 7834067 := bstep (se 1 (by rfl) ⟨5875550, by rfl⟩ : syracuseStep 7834067 = 11751101) B11751101
theorem B3664403 : Blo 1628513 3664403 := bstep (se 1 (by rfl) ⟨2748302, by rfl⟩ : syracuseStep 3664403 = 5496605) B5496605
theorem B2443847 : Blo 1628513 2443847 := bstep (se 1 (by rfl) ⟨1832885, by rfl⟩ : syracuseStep 2443847 = 3665771) B3665771
theorem B3664457 : Blo 1628513 3664457 := bstep (se 2 (by rfl) ⟨1374171, by rfl⟩ : syracuseStep 3664457 = 2748343) B2748343
theorem B2443883 : Blo 1628513 2443883 := bstep (se 1 (by rfl) ⟨1832912, by rfl⟩ : syracuseStep 2443883 = 3665825) B3665825
theorem B57191093 : Blo 1628513 57191093 := bstep (se 5 (by rfl) ⟨2680832, by rfl⟩ : syracuseStep 57191093 = 5361665) B5361665
theorem B2444111 : Blo 1628513 2444111 := bstep (se 1 (by rfl) ⟨1833083, by rfl⟩ : syracuseStep 2444111 = 3666167) B3666167
theorem B8252279 : Blo 1628513 8252279 := bstep (se 1 (by rfl) ⟨6189209, by rfl⟩ : syracuseStep 8252279 = 12378419) B12378419
theorem B5499791 : Blo 1628513 5499791 := bstep (se 1 (by rfl) ⟨4124843, by rfl⟩ : syracuseStep 5499791 = 8249687) B8249687
theorem B3664871 : Blo 1628513 3664871 := bstep (se 1 (by rfl) ⟨2748653, by rfl⟩ : syracuseStep 3664871 = 5497307) B5497307
theorem B12373073 : Blo 1628513 12373073 := bstep (se 2 (by rfl) ⟨4639902, by rfl⟩ : syracuseStep 12373073 = 9279805) B9279805
theorem B2444507 : Blo 1628513 2444507 := bstep (se 1 (by rfl) ⟨1833380, by rfl⟩ : syracuseStep 2444507 = 3666761) B3666761
theorem B3525881 : Blo 1628513 3525881 := bstep (se 2 (by rfl) ⟨1322205, by rfl⟩ : syracuseStep 3525881 = 2644411) B2644411
theorem B4123943 : Blo 1628513 4123943 := bstep (se 1 (by rfl) ⟨3092957, by rfl⟩ : syracuseStep 4123943 = 6185915) B6185915
theorem B3665249 : Blo 1628513 3665249 := bstep (se 2 (by rfl) ⟨1374468, by rfl⟩ : syracuseStep 3665249 = 2748937) B2748937
theorem B22916449 : Blo 1628513 22916449 := bstep (se 2 (by rfl) ⟨8593668, by rfl⟩ : syracuseStep 22916449 = 17187337) B17187337
theorem B2444681 : Blo 1628513 2444681 := bstep (se 2 (by rfl) ⟨916755, by rfl⟩ : syracuseStep 2444681 = 1833511) B1833511
theorem B1740199 : Blo 1628513 1740199 := bstep (se 1 (by rfl) ⟨1305149, by rfl⟩ : syracuseStep 1740199 = 2610299) B2610299
theorem B3665339 : Blo 1628513 3665339 := bstep (se 1 (by rfl) ⟨2749004, by rfl⟩ : syracuseStep 3665339 = 5498009) B5498009
theorem B3665465 : Blo 1628513 3665465 := bstep (se 2 (by rfl) ⟨1374549, by rfl⟩ : syracuseStep 3665465 = 2749099) B2749099
theorem B8253089 : Blo 1628513 8253089 := bstep (se 2 (by rfl) ⟨3094908, by rfl⟩ : syracuseStep 8253089 = 6189817) B6189817
theorem B9277163 : Blo 1628513 9277163 := bstep (se 1 (by rfl) ⟨6957872, by rfl⟩ : syracuseStep 9277163 = 13915745) B13915745
theorem B2445035 : Blo 1628513 2445035 := bstep (se 1 (by rfl) ⟨1833776, by rfl⟩ : syracuseStep 2445035 = 3667553) B3667553
theorem B4706095 : Blo 1628513 4706095 := bstep (se 1 (by rfl) ⟨3529571, by rfl⟩ : syracuseStep 4706095 = 7059143) B7059143
theorem B2748215 : Blo 1628513 2748215 := bstep (se 1 (by rfl) ⟨2061161, by rfl⟩ : syracuseStep 2748215 = 4122323) B4122323
theorem B5574557 : Blo 1628513 5574557 := bstep (se 3 (by rfl) ⟨1045229, by rfl⟩ : syracuseStep 5574557 = 2090459) B2090459
theorem B2445263 : Blo 1628513 2445263 := bstep (se 1 (by rfl) ⟨1833947, by rfl⟩ : syracuseStep 2445263 = 3667895) B3667895
theorem B7934057 : Blo 1628513 7934057 := bstep (se 2 (by rfl) ⟨2975271, by rfl⟩ : syracuseStep 7934057 = 5950543) B5950543
theorem B5501033 : Blo 1628513 5501033 := bstep (se 2 (by rfl) ⟨2062887, by rfl⟩ : syracuseStep 5501033 = 4125775) B4125775
theorem B3666131 : Blo 1628513 3666131 := bstep (se 1 (by rfl) ⟨2749598, by rfl⟩ : syracuseStep 3666131 = 5499197) B5499197
theorem B1741019 : Blo 1628513 1741019 := bstep (se 1 (by rfl) ⟨1305764, by rfl⟩ : syracuseStep 1741019 = 2611529) B2611529
theorem B3666185 : Blo 1628513 3666185 := bstep (se 2 (by rfl) ⟨1374819, by rfl⟩ : syracuseStep 3666185 = 2749639) B2749639
theorem B2445659 : Blo 1628513 2445659 := bstep (se 1 (by rfl) ⟨1834244, by rfl⟩ : syracuseStep 2445659 = 3668489) B3668489
theorem B29716955 : Blo 1628513 29716955 := bstep (se 1 (by rfl) ⟨22287716, by rfl⟩ : syracuseStep 29716955 = 44575433) B44575433
theorem B3666401 : Blo 1628513 3666401 := bstep (se 2 (by rfl) ⟨1374900, by rfl⟩ : syracuseStep 3666401 = 2749801) B2749801
theorem B9286163 : Blo 1628513 9286163 := bstep (se 1 (by rfl) ⟨6964622, by rfl⟩ : syracuseStep 9286163 = 13929245) B13929245
theorem B13218365 : Blo 1628513 13218365 := bstep (se 3 (by rfl) ⟨2478443, by rfl⟩ : syracuseStep 13218365 = 4956887) B4956887
theorem B2748991 : Blo 1628513 2748991 := bstep (se 1 (by rfl) ⟨2061743, by rfl⟩ : syracuseStep 2748991 = 4123487) B4123487
theorem B4125431 : Blo 1628513 4125431 := bstep (se 1 (by rfl) ⟨3094073, by rfl⟩ : syracuseStep 4125431 = 6188147) B6188147
theorem B3666707 : Blo 1628513 3666707 := bstep (se 1 (by rfl) ⟨2750030, by rfl⟩ : syracuseStep 3666707 = 5500061) B5500061
theorem B5501897 : Blo 1628513 5501897 := bstep (se 2 (by rfl) ⟨2063211, by rfl⟩ : syracuseStep 5501897 = 4126423) B4126423
theorem B29004749 : Blo 1628513 29004749 := bstep (se 3 (by rfl) ⟨5438390, by rfl⟩ : syracuseStep 29004749 = 10876781) B10876781
theorem B3667067 : Blo 1628513 3667067 := bstep (se 1 (by rfl) ⟨2750300, by rfl⟩ : syracuseStep 3667067 = 5500601) B5500601
theorem B11752573 : Blo 1628513 11752573 := bstep (se 3 (by rfl) ⟨2203607, by rfl⟩ : syracuseStep 11752573 = 4407215) B4407215
theorem B8811665 : Blo 1628513 8811665 := bstep (se 2 (by rfl) ⟨3304374, by rfl⟩ : syracuseStep 8811665 = 6608749) B6608749
theorem B9278621 : Blo 1628513 9278621 := bstep (se 3 (by rfl) ⟨1739741, by rfl⟩ : syracuseStep 9278621 = 3479483) B3479483
theorem B4404413 : Blo 1628513 4404413 := bstep (se 3 (by rfl) ⟨825827, by rfl⟩ : syracuseStep 4404413 = 1651655) B1651655
theorem B5502167 : Blo 1628513 5502167 := bstep (se 1 (by rfl) ⟨4126625, by rfl⟩ : syracuseStep 5502167 = 8253251) B8253251
theorem B2749673 : Blo 1628513 2749673 := bstep (se 2 (by rfl) ⟨1031127, by rfl⟩ : syracuseStep 2749673 = 2062255) B2062255
theorem B3667193 : Blo 1628513 3667193 := bstep (se 2 (by rfl) ⟨1375197, by rfl⟩ : syracuseStep 3667193 = 2750395) B2750395
theorem B2749727 : Blo 1628513 2749727 := bstep (se 1 (by rfl) ⟨2062295, by rfl⟩ : syracuseStep 2749727 = 4124591) B4124591
theorem B2061607 : Blo 1628513 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B6272299 : Blo 1628513 6272299 := bstep (se 1 (by rfl) ⟨4704224, by rfl⟩ : syracuseStep 6272299 = 9408449) B9408449
theorem B3528031 : Blo 1628513 3528031 := bstep (se 1 (by rfl) ⟨2646023, by rfl⟩ : syracuseStep 3528031 = 5292047) B5292047
theorem B4126049 : Blo 1628513 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B3667337 : Blo 1628513 3667337 := bstep (se 2 (by rfl) ⟨1375251, by rfl⟩ : syracuseStep 3667337 = 2750503) B2750503
theorem B1832359 : Blo 1628513 1832359 := bstep (se 1 (by rfl) ⟨1374269, by rfl⟩ : syracuseStep 1832359 = 2748539) B2748539
theorem B3667463 : Blo 1628513 3667463 := bstep (se 1 (by rfl) ⟨2750597, by rfl⟩ : syracuseStep 3667463 = 5501195) B5501195
theorem B2061931 : Blo 1628513 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B3667643 : Blo 1628513 3667643 := bstep (se 1 (by rfl) ⟨2750732, by rfl⟩ : syracuseStep 3667643 = 5501465) B5501465
theorem B1652447 : Blo 1628513 1652447 := bstep (se 1 (by rfl) ⟨1239335, by rfl⟩ : syracuseStep 1652447 = 2478671) B2478671
theorem B8247095 : Blo 1628513 8247095 := bstep (se 1 (by rfl) ⟨6185321, by rfl⟩ : syracuseStep 8247095 = 12370643) B12370643
theorem B3667769 : Blo 1628513 3667769 := bstep (se 2 (by rfl) ⟨1375413, by rfl⟩ : syracuseStep 3667769 = 2750827) B2750827
theorem B35239799 : Blo 1628513 35239799 := bstep (se 1 (by rfl) ⟨26429849, by rfl⟩ : syracuseStep 35239799 = 52859699) B52859699
theorem B1832935 : Blo 1628513 1832935 := bstep (se 1 (by rfl) ⟨1374701, by rfl⟩ : syracuseStep 1832935 = 2749403) B2749403
theorem B10180687 : Blo 1628513 10180687 := bstep (se 1 (by rfl) ⟨7635515, by rfl⟩ : syracuseStep 10180687 = 15271031) B15271031
theorem B9279623 : Blo 1628513 9279623 := bstep (se 1 (by rfl) ⟨6959717, by rfl⟩ : syracuseStep 9279623 = 13919435) B13919435
theorem B16726297 : Blo 1628513 16726297 := bstep (se 2 (by rfl) ⟨6272361, by rfl⟩ : syracuseStep 16726297 = 12544723) B12544723
theorem B8247581 : Blo 1628513 8247581 := bstep (se 3 (by rfl) ⟨1546421, by rfl⟩ : syracuseStep 8247581 = 3092843) B3092843
theorem B1628527 : Blo 1628513 1628527 := bstep (se 1 (by rfl) ⟨1221395, by rfl⟩ : syracuseStep 1628527 = 2442791) B2442791
theorem B1628583 : Blo 1628513 1628583 := bstep (se 1 (by rfl) ⟨1221437, by rfl⟩ : syracuseStep 1628583 = 2442875) B2442875
theorem B2202023 : Blo 1628513 2202023 := bstep (se 1 (by rfl) ⟨1651517, by rfl⟩ : syracuseStep 2202023 = 3303035) B3303035
theorem B3668399 : Blo 1628513 3668399 := bstep (se 1 (by rfl) ⟨2751299, by rfl⟩ : syracuseStep 3668399 = 5502599) B5502599
theorem B2202055 : Blo 1628513 2202055 := bstep (se 1 (by rfl) ⟨1651541, by rfl⟩ : syracuseStep 2202055 = 3303083) B3303083
theorem B3668435 : Blo 1628513 3668435 := bstep (se 1 (by rfl) ⟨2751326, by rfl⟩ : syracuseStep 3668435 = 5502653) B5502653
theorem B1628667 : Blo 1628513 1628667 := bstep (se 1 (by rfl) ⟨1221500, by rfl⟩ : syracuseStep 1628667 = 2443001) B2443001
theorem B10435067 : Blo 1628513 10435067 := bstep (se 1 (by rfl) ⟨7826300, by rfl⟩ : syracuseStep 10435067 = 15652601) B15652601
theorem B13220347 : Blo 1628513 13220347 := bstep (se 1 (by rfl) ⟨9915260, by rfl⟩ : syracuseStep 13220347 = 19830521) B19830521
theorem B1628735 : Blo 1628513 1628735 := bstep (se 1 (by rfl) ⟨1221551, by rfl⟩ : syracuseStep 1628735 = 2443103) B2443103
theorem B3914303 : Blo 1628513 3914303 := bstep (se 1 (by rfl) ⟨2935727, by rfl⟩ : syracuseStep 3914303 = 5871455) B5871455
theorem B3668543 : Blo 1628513 3668543 := bstep (se 1 (by rfl) ⟨2751407, by rfl⟩ : syracuseStep 3668543 = 5502815) B5502815
theorem B1628743 : Blo 1628513 1628743 := bstep (se 1 (by rfl) ⟨1221557, by rfl⟩ : syracuseStep 1628743 = 2443115) B2443115
theorem B25090667 : Blo 1628513 25090667 := bstep (se 1 (by rfl) ⟨18818000, by rfl⟩ : syracuseStep 25090667 = 37636001) B37636001
theorem B2751097 : Blo 1628513 2751097 := bstep (se 2 (by rfl) ⟨1031661, by rfl⟩ : syracuseStep 2751097 = 2063323) B2063323
theorem B3668651 : Blo 1628513 3668651 := bstep (se 1 (by rfl) ⟨2751488, by rfl⟩ : syracuseStep 3668651 = 5502977) B5502977
theorem B11745967 : Blo 1628513 11745967 := bstep (se 1 (by rfl) ⟨8809475, by rfl⟩ : syracuseStep 11745967 = 17618951) B17618951
theorem B22305455 : Blo 1628513 22305455 := bstep (se 1 (by rfl) ⟨16729091, by rfl⟩ : syracuseStep 22305455 = 33458183) B33458183
theorem B2751151 : Blo 1628513 2751151 := bstep (se 1 (by rfl) ⟨2063363, by rfl⟩ : syracuseStep 2751151 = 4126727) B4126727
theorem B1628895 : Blo 1628513 1628895 := bstep (se 1 (by rfl) ⟨1221671, by rfl⟩ : syracuseStep 1628895 = 2443343) B2443343
theorem B1628975 : Blo 1628513 1628975 := bstep (se 1 (by rfl) ⟨1221731, by rfl⟩ : syracuseStep 1628975 = 2443463) B2443463
theorem B5217149 : Blo 1628513 5217149 := bstep (se 3 (by rfl) ⟨978215, by rfl⟩ : syracuseStep 5217149 = 1956431) B1956431
theorem B1629083 : Blo 1628513 1629083 := bstep (se 1 (by rfl) ⟨1221812, by rfl⟩ : syracuseStep 1629083 = 2443625) B2443625
theorem B1629135 : Blo 1628513 1629135 := bstep (se 1 (by rfl) ⟨1221851, by rfl⟩ : syracuseStep 1629135 = 2443703) B2443703
theorem B1629159 : Blo 1628513 1629159 := bstep (se 1 (by rfl) ⟨1221869, by rfl⟩ : syracuseStep 1629159 = 2443739) B2443739
theorem B13212659 : Blo 1628513 13212659 := bstep (se 1 (by rfl) ⟨9909494, by rfl⟩ : syracuseStep 13212659 = 19818989) B19818989
theorem B8363047 : Blo 1628513 8363047 := bstep (se 1 (by rfl) ⟨6272285, by rfl⟩ : syracuseStep 8363047 = 12544571) B12544571
theorem B30145699 : Blo 1628513 30145699 := bstep (se 1 (by rfl) ⟨22609274, by rfl⟩ : syracuseStep 30145699 = 45218549) B45218549
theorem B40180931 : Blo 1628513 40180931 := bstep (se 1 (by rfl) ⟨30135698, by rfl⟩ : syracuseStep 40180931 = 60271397) B60271397
theorem B1629471 : Blo 1628513 1629471 := bstep (se 1 (by rfl) ⟨1222103, by rfl⟩ : syracuseStep 1629471 = 2444207) B2444207
theorem B6184259 : Blo 1628513 6184259 := bstep (se 1 (by rfl) ⟨4638194, by rfl⟩ : syracuseStep 6184259 = 9276389) B9276389
theorem B1629531 : Blo 1628513 1629531 := bstep (se 1 (by rfl) ⟨1222148, by rfl⟩ : syracuseStep 1629531 = 2444297) B2444297
theorem B6184289 : Blo 1628513 6184289 := bstep (se 2 (by rfl) ⟨2319108, by rfl⟩ : syracuseStep 6184289 = 4638217) B4638217
theorem B1629551 : Blo 1628513 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B7830913 : Blo 1628513 7830913 := bstep (se 2 (by rfl) ⟨2936592, by rfl⟩ : syracuseStep 7830913 = 5873185) B5873185
theorem B3718561 : Blo 1628513 3718561 := bstep (se 2 (by rfl) ⟨1394460, by rfl⟩ : syracuseStep 3718561 = 2788921) B2788921
theorem B1629607 : Blo 1628513 1629607 := bstep (se 1 (by rfl) ⟨1222205, by rfl⟩ : syracuseStep 1629607 = 2444411) B2444411
theorem B1629691 : Blo 1628513 1629691 := bstep (se 1 (by rfl) ⟨1222268, by rfl⟩ : syracuseStep 1629691 = 2444537) B2444537
theorem B5496335 : Blo 1628513 5496335 := bstep (se 1 (by rfl) ⟨4122251, by rfl⟩ : syracuseStep 5496335 = 8244503) B8244503
theorem B6610447 : Blo 1628513 6610447 := bstep (se 1 (by rfl) ⟨4957835, by rfl⟩ : syracuseStep 6610447 = 9915671) B9915671
theorem B1629759 : Blo 1628513 1629759 := bstep (se 1 (by rfl) ⟨1222319, by rfl⟩ : syracuseStep 1629759 = 2444639) B2444639
theorem B1629767 : Blo 1628513 1629767 := bstep (se 1 (by rfl) ⟨1222325, by rfl⟩ : syracuseStep 1629767 = 2444651) B2444651
theorem B4406879 : Blo 1628513 4406879 := bstep (se 1 (by rfl) ⟨3305159, by rfl⟩ : syracuseStep 4406879 = 6610319) B6610319
theorem B1629919 : Blo 1628513 1629919 := bstep (se 1 (by rfl) ⟨1222439, by rfl⟩ : syracuseStep 1629919 = 2444879) B2444879
theorem B12369671 : Blo 1628513 12369671 := bstep (se 1 (by rfl) ⟨9277253, by rfl⟩ : syracuseStep 12369671 = 18554507) B18554507
theorem B6184745 : Blo 1628513 6184745 := bstep (se 2 (by rfl) ⟨2319279, by rfl⟩ : syracuseStep 6184745 = 4638559) B4638559
theorem B1629999 : Blo 1628513 1629999 := bstep (se 1 (by rfl) ⟨1222499, by rfl⟩ : syracuseStep 1629999 = 2444999) B2444999
theorem B17612639 : Blo 1628513 17612639 := bstep (se 1 (by rfl) ⟨13209479, by rfl⟩ : syracuseStep 17612639 = 26418959) B26418959
theorem B3915649 : Blo 1628513 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B1630107 : Blo 1628513 1630107 := bstep (se 1 (by rfl) ⟨1222580, by rfl⟩ : syracuseStep 1630107 = 2445161) B2445161
theorem B1630159 : Blo 1628513 1630159 := bstep (se 1 (by rfl) ⟨1222619, by rfl⟩ : syracuseStep 1630159 = 2445239) B2445239
theorem B1630183 : Blo 1628513 1630183 := bstep (se 1 (by rfl) ⟨1222637, by rfl⟩ : syracuseStep 1630183 = 2445275) B2445275
theorem B13574249 : Blo 1628513 13574249 := bstep (se 2 (by rfl) ⟨5090343, by rfl⟩ : syracuseStep 13574249 = 10180687) B10180687
theorem B1630439 : Blo 1628513 1630439 := bstep (se 1 (by rfl) ⟨1222829, by rfl⟩ : syracuseStep 1630439 = 2445659) B2445659
theorem B3916063 : Blo 1628513 3916063 := bstep (se 1 (by rfl) ⟨2937047, by rfl⟩ : syracuseStep 3916063 = 5874095) B5874095
theorem B6963887 : Blo 1628513 6963887 := bstep (se 1 (by rfl) ⟨5222915, by rfl⟩ : syracuseStep 6963887 = 10445831) B10445831
theorem B31752881 : Blo 1628513 31752881 := bstep (se 2 (by rfl) ⟨11907330, by rfl⟩ : syracuseStep 31752881 = 23814661) B23814661
theorem B3015433 : Blo 1628513 3015433 := bstep (se 2 (by rfl) ⟨1130787, by rfl⟩ : syracuseStep 3015433 = 2261575) B2261575
theorem B5874443 : Blo 1628513 5874443 := bstep (se 1 (by rfl) ⟨4405832, by rfl⟩ : syracuseStep 5874443 = 8811665) B8811665
theorem B6185747 : Blo 1628513 6185747 := bstep (se 1 (by rfl) ⟨4639310, by rfl⟩ : syracuseStep 6185747 = 9278621) B9278621
theorem B11748215 : Blo 1628513 11748215 := bstep (se 1 (by rfl) ⟨8811161, by rfl⟩ : syracuseStep 11748215 = 17622323) B17622323
theorem B20874185 : Blo 1628513 20874185 := bstep (se 2 (by rfl) ⟨7827819, by rfl⟩ : syracuseStep 20874185 = 15655639) B15655639
theorem B5498063 : Blo 1628513 5498063 := bstep (se 1 (by rfl) ⟨4123547, by rfl⟩ : syracuseStep 5498063 = 8247095) B8247095
theorem B11150729 : Blo 1628513 11150729 := bstep (se 2 (by rfl) ⟨4181523, by rfl⟩ : syracuseStep 11150729 = 8363047) B8363047
theorem B6186415 : Blo 1628513 6186415 := bstep (se 1 (by rfl) ⟨4639811, by rfl⟩ : syracuseStep 6186415 = 9279623) B9279623
theorem B10438141 : Blo 1628513 10438141 := bstep (se 3 (by rfl) ⟨1957151, by rfl⟩ : syracuseStep 10438141 = 3914303) B3914303
theorem B5498387 : Blo 1628513 5498387 := bstep (se 1 (by rfl) ⟨4123790, by rfl⟩ : syracuseStep 5498387 = 8247581) B8247581
theorem B2442863 : Blo 1628513 2442863 := bstep (se 1 (by rfl) ⟨1832147, by rfl⟩ : syracuseStep 2442863 = 3664295) B3664295
theorem B15664751 : Blo 1628513 15664751 := bstep (se 1 (by rfl) ⟨11748563, by rfl⟩ : syracuseStep 15664751 = 23497127) B23497127
theorem B6956711 : Blo 1628513 6956711 := bstep (se 1 (by rfl) ⟨5217533, by rfl⟩ : syracuseStep 6956711 = 10435067) B10435067
theorem B2442935 : Blo 1628513 2442935 := bstep (se 1 (by rfl) ⟨1832201, by rfl⟩ : syracuseStep 2442935 = 3664403) B3664403
theorem B2442971 : Blo 1628513 2442971 := bstep (se 1 (by rfl) ⟨1832228, by rfl⟩ : syracuseStep 2442971 = 3664457) B3664457
theorem B14870303 : Blo 1628513 14870303 := bstep (se 1 (by rfl) ⟨11152727, by rfl⟩ : syracuseStep 14870303 = 22305455) B22305455
theorem B38127395 : Blo 1628513 38127395 := bstep (se 1 (by rfl) ⟨28595546, by rfl⟩ : syracuseStep 38127395 = 57191093) B57191093
theorem B4704041 : Blo 1628513 4704041 := bstep (se 2 (by rfl) ⟨1764015, by rfl⟩ : syracuseStep 4704041 = 3528031) B3528031
theorem B4958081 : Blo 1628513 4958081 := bstep (se 2 (by rfl) ⟨1859280, by rfl⟩ : syracuseStep 4958081 = 3718561) B3718561
theorem B2443145 : Blo 1628513 2443145 := bstep (se 2 (by rfl) ⟨916179, by rfl⟩ : syracuseStep 2443145 = 1832359) B1832359
theorem B2320265 : Blo 1628513 2320265 := bstep (se 2 (by rfl) ⟨870099, by rfl⟩ : syracuseStep 2320265 = 1740199) B1740199
theorem B2443247 : Blo 1628513 2443247 := bstep (se 1 (by rfl) ⟨1832435, by rfl⟩ : syracuseStep 2443247 = 3664871) B3664871
theorem B8808439 : Blo 1628513 8808439 := bstep (se 1 (by rfl) ⟨6606329, by rfl⟩ : syracuseStep 8808439 = 13212659) B13212659
theorem B4122839 : Blo 1628513 4122839 := bstep (se 1 (by rfl) ⟨3092129, by rfl⟩ : syracuseStep 4122839 = 6184259) B6184259
theorem B4122859 : Blo 1628513 4122859 := bstep (se 1 (by rfl) ⟨3092144, by rfl⟩ : syracuseStep 4122859 = 6184289) B6184289
theorem B2443499 : Blo 1628513 2443499 := bstep (se 1 (by rfl) ⟨1832624, by rfl⟩ : syracuseStep 2443499 = 3665249) B3665249
theorem B2443559 : Blo 1628513 2443559 := bstep (se 1 (by rfl) ⟨1832669, by rfl⟩ : syracuseStep 2443559 = 3665339) B3665339
theorem B13912397 : Blo 1628513 13912397 := bstep (se 3 (by rfl) ⟨2608574, by rfl⟩ : syracuseStep 13912397 = 5217149) B5217149
theorem B3664223 : Blo 1628513 3664223 := bstep (se 1 (by rfl) ⟨2748167, by rfl⟩ : syracuseStep 3664223 = 5496335) B5496335
theorem B2443643 : Blo 1628513 2443643 := bstep (se 1 (by rfl) ⟨1832732, by rfl⟩ : syracuseStep 2443643 = 3665465) B3665465
theorem B5220865 : Blo 1628513 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B4123163 : Blo 1628513 4123163 := bstep (se 1 (by rfl) ⟨3092372, by rfl⟩ : syracuseStep 4123163 = 6184745) B6184745
theorem B11741759 : Blo 1628513 11741759 := bstep (se 1 (by rfl) ⟨8806319, by rfl⟩ : syracuseStep 11741759 = 17612639) B17612639
theorem B2443913 : Blo 1628513 2443913 := bstep (se 2 (by rfl) ⟨916467, by rfl⟩ : syracuseStep 2443913 = 1832935) B1832935
theorem B5499575 : Blo 1628513 5499575 := bstep (se 1 (by rfl) ⟨4124681, by rfl⟩ : syracuseStep 5499575 = 8249363) B8249363
theorem B94006007 : Blo 1628513 94006007 := bstep (se 1 (by rfl) ⟨70504505, by rfl⟩ : syracuseStep 94006007 = 141009011) B141009011
theorem B2444087 : Blo 1628513 2444087 := bstep (se 1 (by rfl) ⟨1833065, by rfl⟩ : syracuseStep 2444087 = 3666131) B3666131
theorem B2444123 : Blo 1628513 2444123 := bstep (se 1 (by rfl) ⟨1833092, by rfl⟩ : syracuseStep 2444123 = 3666185) B3666185
theorem B19811303 : Blo 1628513 19811303 := bstep (se 1 (by rfl) ⟨14858477, by rfl⟩ : syracuseStep 19811303 = 29716955) B29716955
theorem B2444267 : Blo 1628513 2444267 := bstep (se 1 (by rfl) ⟨1833200, by rfl⟩ : syracuseStep 2444267 = 3666401) B3666401
theorem B22301729 : Blo 1628513 22301729 := bstep (se 2 (by rfl) ⟨8363148, by rfl⟩ : syracuseStep 22301729 = 16726297) B16726297
theorem B3664943 : Blo 1628513 3664943 := bstep (se 1 (by rfl) ⟨2748707, by rfl⟩ : syracuseStep 3664943 = 5497415) B5497415
theorem B2321455 : Blo 1628513 2321455 := bstep (se 1 (by rfl) ⟨1741091, by rfl⟩ : syracuseStep 2321455 = 3482183) B3482183
theorem B9284705 : Blo 1628513 9284705 := bstep (se 2 (by rfl) ⟨3481764, by rfl⟩ : syracuseStep 9284705 = 6963529) B6963529
theorem B2444471 : Blo 1628513 2444471 := bstep (se 1 (by rfl) ⟨1833353, by rfl⟩ : syracuseStep 2444471 = 3666707) B3666707
theorem B19336499 : Blo 1628513 19336499 := bstep (se 1 (by rfl) ⟨14502374, by rfl⟩ : syracuseStep 19336499 = 29004749) B29004749
theorem B3665231 : Blo 1628513 3665231 := bstep (se 1 (by rfl) ⟨2748923, by rfl⟩ : syracuseStep 3665231 = 5497847) B5497847
theorem B3714473 : Blo 1628513 3714473 := bstep (se 2 (by rfl) ⟨1392927, by rfl⟩ : syracuseStep 3714473 = 2785855) B2785855
theorem B3665321 : Blo 1628513 3665321 := bstep (se 2 (by rfl) ⟨1374495, by rfl⟩ : syracuseStep 3665321 = 2748991) B2748991
theorem B2444711 : Blo 1628513 2444711 := bstep (se 1 (by rfl) ⟨1833533, by rfl⟩ : syracuseStep 2444711 = 3667067) B3667067
theorem B4124155 : Blo 1628513 4124155 := bstep (se 1 (by rfl) ⟨3093116, by rfl⟩ : syracuseStep 4124155 = 6186233) B6186233
theorem B2444795 : Blo 1628513 2444795 := bstep (se 1 (by rfl) ⟨1833596, by rfl⟩ : syracuseStep 2444795 = 3667193) B3667193
theorem B2444891 : Blo 1628513 2444891 := bstep (se 1 (by rfl) ⟨1833668, by rfl⟩ : syracuseStep 2444891 = 3667337) B3667337
theorem B4124267 : Blo 1628513 4124267 := bstep (se 1 (by rfl) ⟨3093200, by rfl⟩ : syracuseStep 4124267 = 6186401) B6186401
theorem B2444975 : Blo 1628513 2444975 := bstep (se 1 (by rfl) ⟨1833731, by rfl⟩ : syracuseStep 2444975 = 3667463) B3667463
theorem B2445095 : Blo 1628513 2445095 := bstep (se 1 (by rfl) ⟨1833821, by rfl⟩ : syracuseStep 2445095 = 3667643) B3667643
theorem B5222249 : Blo 1628513 5222249 := bstep (se 2 (by rfl) ⟨1958343, by rfl⟩ : syracuseStep 5222249 = 3916687) B3916687
theorem B2445179 : Blo 1628513 2445179 := bstep (se 1 (by rfl) ⟨1833884, by rfl⟩ : syracuseStep 2445179 = 3667769) B3667769
theorem B3665807 : Blo 1628513 3665807 := bstep (se 1 (by rfl) ⟨2749355, by rfl⟩ : syracuseStep 3665807 = 5498711) B5498711
theorem B5222351 : Blo 1628513 5222351 := bstep (se 1 (by rfl) ⟨3916763, by rfl⟩ : syracuseStep 5222351 = 7833527) B7833527
theorem B40194265 : Blo 1628513 40194265 := bstep (se 2 (by rfl) ⟨15072849, by rfl⟩ : syracuseStep 40194265 = 30145699) B30145699
theorem B33452261 : Blo 1628513 33452261 := bstep (se 4 (by rfl) ⟨3136149, by rfl⟩ : syracuseStep 33452261 = 6272299) B6272299
theorem B2748647 : Blo 1628513 2748647 := bstep (se 1 (by rfl) ⟨2061485, by rfl⟩ : syracuseStep 2748647 = 4122971) B4122971
theorem B2445599 : Blo 1628513 2445599 := bstep (se 1 (by rfl) ⟨1834199, by rfl⟩ : syracuseStep 2445599 = 3668399) B3668399
theorem B5222711 : Blo 1628513 5222711 := bstep (se 1 (by rfl) ⟨3917033, by rfl⟩ : syracuseStep 5222711 = 7834067) B7834067
theorem B2445623 : Blo 1628513 2445623 := bstep (se 1 (by rfl) ⟨1834217, by rfl⟩ : syracuseStep 2445623 = 3668435) B3668435
theorem B2445695 : Blo 1628513 2445695 := bstep (se 1 (by rfl) ⟨1834271, by rfl⟩ : syracuseStep 2445695 = 3668543) B3668543
theorem B2748809 : Blo 1628513 2748809 := bstep (se 2 (by rfl) ⟨1030803, by rfl⟩ : syracuseStep 2748809 = 2061607) B2061607
theorem B2445767 : Blo 1628513 2445767 := bstep (se 1 (by rfl) ⟨1834325, by rfl⟩ : syracuseStep 2445767 = 3668651) B3668651
theorem B10441217 : Blo 1628513 10441217 := bstep (se 2 (by rfl) ⟨3915456, by rfl⟩ : syracuseStep 10441217 = 7830913) B7830913
theorem B5501519 : Blo 1628513 5501519 := bstep (se 1 (by rfl) ⟨4126139, by rfl⟩ : syracuseStep 5501519 = 8252279) B8252279
theorem B3666527 : Blo 1628513 3666527 := bstep (se 1 (by rfl) ⟨2749895, by rfl⟩ : syracuseStep 3666527 = 5499791) B5499791
theorem B2749241 : Blo 1628513 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B2749295 : Blo 1628513 2749295 := bstep (se 1 (by rfl) ⟨2061971, by rfl⟩ : syracuseStep 2749295 = 4123943) B4123943
theorem B11744293 : Blo 1628513 11744293 := bstep (se 4 (by rfl) ⟨1101027, by rfl⟩ : syracuseStep 11744293 = 2202055) B2202055
theorem B2937919 : Blo 1628513 2937919 := bstep (se 1 (by rfl) ⟨2203439, by rfl⟩ : syracuseStep 2937919 = 4406879) B4406879
theorem B5502059 : Blo 1628513 5502059 := bstep (se 1 (by rfl) ⟨4126544, by rfl⟩ : syracuseStep 5502059 = 8253089) B8253089
theorem B8246447 : Blo 1628513 8246447 := bstep (se 1 (by rfl) ⟨6184835, by rfl⟩ : syracuseStep 8246447 = 12369671) B12369671
theorem B1832143 : Blo 1628513 1832143 := bstep (se 1 (by rfl) ⟨1374107, by rfl⟩ : syracuseStep 1832143 = 2748215) B2748215
theorem B3716371 : Blo 1628513 3716371 := bstep (se 1 (by rfl) ⟨2787278, by rfl⟩ : syracuseStep 3716371 = 5574557) B5574557
theorem B5289371 : Blo 1628513 5289371 := bstep (se 1 (by rfl) ⟨3967028, by rfl⟩ : syracuseStep 5289371 = 7934057) B7934057
theorem B3667355 : Blo 1628513 3667355 := bstep (se 1 (by rfl) ⟨2750516, by rfl⟩ : syracuseStep 3667355 = 5501033) B5501033
theorem B6190775 : Blo 1628513 6190775 := bstep (se 1 (by rfl) ⟨4643081, by rfl⟩ : syracuseStep 6190775 = 9286163) B9286163
theorem B8812243 : Blo 1628513 8812243 := bstep (se 1 (by rfl) ⟨6609182, by rfl⟩ : syracuseStep 8812243 = 13218365) B13218365
theorem B11745101 : Blo 1628513 11745101 := bstep (se 3 (by rfl) ⟨2202206, by rfl⟩ : syracuseStep 11745101 = 4404413) B4404413
theorem B2750287 : Blo 1628513 2750287 := bstep (se 1 (by rfl) ⟨2062715, by rfl⟩ : syracuseStep 2750287 = 4125431) B4125431
theorem B4642717 : Blo 1628513 4642717 := bstep (se 3 (by rfl) ⟨870509, by rfl⟩ : syracuseStep 4642717 = 1741019) B1741019
theorem B3667931 : Blo 1628513 3667931 := bstep (se 1 (by rfl) ⟨2750948, by rfl⟩ : syracuseStep 3667931 = 5501897) B5501897
theorem B9402349 : Blo 1628513 9402349 := bstep (se 3 (by rfl) ⟨1762940, by rfl⟩ : syracuseStep 9402349 = 3525881) B3525881
theorem B17627129 : Blo 1628513 17627129 := bstep (se 2 (by rfl) ⟨6610173, by rfl⟩ : syracuseStep 17627129 = 13220347) B13220347
theorem B3668111 : Blo 1628513 3668111 := bstep (se 1 (by rfl) ⟨2751083, by rfl⟩ : syracuseStep 3668111 = 5502167) B5502167
theorem B1833115 : Blo 1628513 1833115 := bstep (se 1 (by rfl) ⟨1374836, by rfl⟩ : syracuseStep 1833115 = 2749673) B2749673
theorem B3668129 : Blo 1628513 3668129 := bstep (se 2 (by rfl) ⟨1375548, by rfl⟩ : syracuseStep 3668129 = 2751097) B2751097
theorem B1833151 : Blo 1628513 1833151 := bstep (se 1 (by rfl) ⟨1374863, by rfl⟩ : syracuseStep 1833151 = 2749727) B2749727
theorem B15661289 : Blo 1628513 15661289 := bstep (se 2 (by rfl) ⟨5872983, by rfl⟩ : syracuseStep 15661289 = 11745967) B11745967
theorem B3668201 : Blo 1628513 3668201 := bstep (se 2 (by rfl) ⟨1375575, by rfl⟩ : syracuseStep 3668201 = 2751151) B2751151
theorem B2750699 : Blo 1628513 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B5872061 : Blo 1628513 5872061 := bstep (se 3 (by rfl) ⟨1101011, by rfl⟩ : syracuseStep 5872061 = 2202023) B2202023
theorem B1628699 : Blo 1628513 1628699 := bstep (se 1 (by rfl) ⟨1221524, by rfl⟩ : syracuseStep 1628699 = 2443049) B2443049
theorem B1628703 : Blo 1628513 1628703 := bstep (se 1 (by rfl) ⟨1221527, by rfl⟩ : syracuseStep 1628703 = 2443055) B2443055
theorem B23493199 : Blo 1628513 23493199 := bstep (se 1 (by rfl) ⟨17619899, by rfl⟩ : syracuseStep 23493199 = 35239799) B35239799
theorem B8247905 : Blo 1628513 8247905 := bstep (se 2 (by rfl) ⟨3092964, by rfl⟩ : syracuseStep 8247905 = 6185929) B6185929
theorem B15670097 : Blo 1628513 15670097 := bstep (se 2 (by rfl) ⟨5876286, by rfl⟩ : syracuseStep 15670097 = 11752573) B11752573
theorem B1629019 : Blo 1628513 1629019 := bstep (se 1 (by rfl) ⟨1221764, by rfl⟩ : syracuseStep 1629019 = 2443529) B2443529
theorem B1956767 : Blo 1628513 1956767 := bstep (se 1 (by rfl) ⟨1467575, by rfl⟩ : syracuseStep 1956767 = 2935151) B2935151
theorem B1629087 : Blo 1628513 1629087 := bstep (se 1 (by rfl) ⟨1221815, by rfl⟩ : syracuseStep 1629087 = 2443631) B2443631
theorem B1629231 : Blo 1628513 1629231 := bstep (se 1 (by rfl) ⟨1221923, by rfl⟩ : syracuseStep 1629231 = 2443847) B2443847
theorem B1629255 : Blo 1628513 1629255 := bstep (se 1 (by rfl) ⟨1221941, by rfl⟩ : syracuseStep 1629255 = 2443883) B2443883
theorem B16727111 : Blo 1628513 16727111 := bstep (se 1 (by rfl) ⟨12545333, by rfl⟩ : syracuseStep 16727111 = 25090667) B25090667
theorem B30555265 : Blo 1628513 30555265 := bstep (se 2 (by rfl) ⟨11458224, by rfl⟩ : syracuseStep 30555265 = 22916449) B22916449
theorem B1629407 : Blo 1628513 1629407 := bstep (se 1 (by rfl) ⟨1222055, by rfl⟩ : syracuseStep 1629407 = 2444111) B2444111
theorem B4406525 : Blo 1628513 4406525 := bstep (se 3 (by rfl) ⟨826223, by rfl⟩ : syracuseStep 4406525 = 1652447) B1652447
theorem B8813929 : Blo 1628513 8813929 := bstep (se 2 (by rfl) ⟨3305223, by rfl⟩ : syracuseStep 8813929 = 6610447) B6610447
theorem B8248715 : Blo 1628513 8248715 := bstep (se 1 (by rfl) ⟨6186536, by rfl⟩ : syracuseStep 8248715 = 12373073) B12373073
theorem B26787287 : Blo 1628513 26787287 := bstep (se 1 (by rfl) ⟨20090465, by rfl⟩ : syracuseStep 26787287 = 40180931) B40180931
theorem B1629671 : Blo 1628513 1629671 := bstep (se 1 (by rfl) ⟨1222253, by rfl⟩ : syracuseStep 1629671 = 2444507) B2444507
theorem B1629787 : Blo 1628513 1629787 := bstep (se 1 (by rfl) ⟨1222340, by rfl⟩ : syracuseStep 1629787 = 2444681) B2444681
theorem B6274793 : Blo 1628513 6274793 := bstep (se 2 (by rfl) ⟨2353047, by rfl⟩ : syracuseStep 6274793 = 4706095) B4706095
theorem B6184775 : Blo 1628513 6184775 := bstep (se 1 (by rfl) ⟨4638581, by rfl⟩ : syracuseStep 6184775 = 9277163) B9277163
theorem B1630023 : Blo 1628513 1630023 := bstep (se 1 (by rfl) ⟨1222517, by rfl⟩ : syracuseStep 1630023 = 2445035) B2445035
theorem B1630175 : Blo 1628513 1630175 := bstep (se 1 (by rfl) ⟨1222631, by rfl⟩ : syracuseStep 1630175 = 2445263) B2445263
theorem B1630399 : Blo 1628513 1630399 := bstep (se 1 (by rfl) ⟨1222799, by rfl⟩ : syracuseStep 1630399 = 2445599) B2445599
theorem B3481807 : Blo 1628513 3481807 := bstep (se 1 (by rfl) ⟨2611355, by rfl⟩ : syracuseStep 3481807 = 5222711) B5222711
theorem B1630415 : Blo 1628513 1630415 := bstep (se 1 (by rfl) ⟨1222811, by rfl⟩ : syracuseStep 1630415 = 2445623) B2445623
theorem B1630463 : Blo 1628513 1630463 := bstep (se 1 (by rfl) ⟨1222847, by rfl⟩ : syracuseStep 1630463 = 2445695) B2445695
theorem B53592353 : Blo 1628513 53592353 := bstep (se 2 (by rfl) ⟨20097132, by rfl⟩ : syracuseStep 53592353 = 40194265) B40194265
theorem B1630511 : Blo 1628513 1630511 := bstep (se 1 (by rfl) ⟨1222883, by rfl⟩ : syracuseStep 1630511 = 2445767) B2445767
theorem B5497145 : Blo 1628513 5497145 := bstep (se 2 (by rfl) ⟨2061429, by rfl⟩ : syracuseStep 5497145 = 4122859) B4122859
theorem B21168587 : Blo 1628513 21168587 := bstep (se 1 (by rfl) ⟨15876440, by rfl⟩ : syracuseStep 21168587 = 31752881) B31752881
theorem B3916295 : Blo 1628513 3916295 := bstep (se 1 (by rfl) ⟨2937221, by rfl⟩ : syracuseStep 3916295 = 5874443) B5874443
theorem B7832143 : Blo 1628513 7832143 := bstep (se 1 (by rfl) ⟨5874107, by rfl⟩ : syracuseStep 7832143 = 11748215) B11748215
theorem B5497631 : Blo 1628513 5497631 := bstep (se 1 (by rfl) ⟨4123223, by rfl⟩ : syracuseStep 5497631 = 8246447) B8246447
theorem B46998629 : Blo 1628513 46998629 := bstep (se 4 (by rfl) ⟨4406121, by rfl⟩ : syracuseStep 46998629 = 8812243) B8812243
theorem B4637807 : Blo 1628513 4637807 := bstep (se 1 (by rfl) ⟨3478355, by rfl⟩ : syracuseStep 4637807 = 6956711) B6956711
theorem B9913535 : Blo 1628513 9913535 := bstep (se 1 (by rfl) ⟨7435151, by rfl⟩ : syracuseStep 9913535 = 14870303) B14870303
theorem B3917225 : Blo 1628513 3917225 := bstep (se 2 (by rfl) ⟨1468959, by rfl⟩ : syracuseStep 3917225 = 2937919) B2937919
theorem B40740353 : Blo 1628513 40740353 := bstep (se 2 (by rfl) ⟨15277632, by rfl⟩ : syracuseStep 40740353 = 30555265) B30555265
theorem B9274931 : Blo 1628513 9274931 := bstep (se 1 (by rfl) ⟨6956198, by rfl⟩ : syracuseStep 9274931 = 13912397) B13912397
theorem B2442815 : Blo 1628513 2442815 := bstep (se 1 (by rfl) ⟨1832111, by rfl⟩ : syracuseStep 2442815 = 3664223) B3664223
theorem B2442857 : Blo 1628513 2442857 := bstep (se 2 (by rfl) ⟨916071, by rfl⟩ : syracuseStep 2442857 = 1832143) B1832143
theorem B5498603 : Blo 1628513 5498603 := bstep (se 1 (by rfl) ⟨4123952, by rfl⟩ : syracuseStep 5498603 = 8247905) B8247905
theorem B62670671 : Blo 1628513 62670671 := bstep (se 1 (by rfl) ⟨47003003, by rfl⟩ : syracuseStep 62670671 = 94006007) B94006007
theorem B10446731 : Blo 1628513 10446731 := bstep (se 1 (by rfl) ⟨7835048, by rfl⟩ : syracuseStep 10446731 = 15670097) B15670097
theorem B13207535 : Blo 1628513 13207535 := bstep (se 1 (by rfl) ⟨9905651, by rfl⟩ : syracuseStep 13207535 = 19811303) B19811303
theorem B5498873 : Blo 1628513 5498873 := bstep (se 2 (by rfl) ⟨2062077, by rfl⟩ : syracuseStep 5498873 = 4124155) B4124155
theorem B2443295 : Blo 1628513 2443295 := bstep (se 1 (by rfl) ⟨1832471, by rfl⟩ : syracuseStep 2443295 = 3664943) B3664943
theorem B11151407 : Blo 1628513 11151407 := bstep (se 1 (by rfl) ⟨8363555, by rfl⟩ : syracuseStep 11151407 = 16727111) B16727111
theorem B101673053 : Blo 1628513 101673053 := bstep (se 3 (by rfl) ⟨19063697, by rfl⟩ : syracuseStep 101673053 = 38127395) B38127395
theorem B12544109 : Blo 1628513 12544109 := bstep (se 3 (by rfl) ⟨2352020, by rfl⟩ : syracuseStep 12544109 = 4704041) B4704041
theorem B31320269 : Blo 1628513 31320269 := bstep (se 3 (by rfl) ⟨5872550, by rfl⟩ : syracuseStep 31320269 = 11745101) B11745101
theorem B2443487 : Blo 1628513 2443487 := bstep (se 1 (by rfl) ⟨1832615, by rfl⟩ : syracuseStep 2443487 = 3665231) B3665231
theorem B5499143 : Blo 1628513 5499143 := bstep (se 1 (by rfl) ⟨4124357, by rfl⟩ : syracuseStep 5499143 = 8248715) B8248715
theorem B2476315 : Blo 1628513 2476315 := bstep (se 1 (by rfl) ⟨1857236, by rfl⟩ : syracuseStep 2476315 = 3714473) B3714473
theorem B2443547 : Blo 1628513 2443547 := bstep (se 1 (by rfl) ⟨1832660, by rfl⟩ : syracuseStep 2443547 = 3665321) B3665321
theorem B6187373 : Blo 1628513 6187373 := bstep (se 3 (by rfl) ⟨1160132, by rfl⟩ : syracuseStep 6187373 = 2320265) B2320265
theorem B4123183 : Blo 1628513 4123183 := bstep (se 1 (by rfl) ⟨3092387, by rfl⟩ : syracuseStep 4123183 = 6184775) B6184775
theorem B2443871 : Blo 1628513 2443871 := bstep (se 1 (by rfl) ⟨1832903, by rfl⟩ : syracuseStep 2443871 = 3665807) B3665807
theorem B12536465 : Blo 1628513 12536465 := bstep (se 2 (by rfl) ⟨4701174, by rfl⟩ : syracuseStep 12536465 = 9402349) B9402349
theorem B22301507 : Blo 1628513 22301507 := bstep (se 1 (by rfl) ⟨16726130, by rfl⟩ : syracuseStep 22301507 = 33452261) B33452261
theorem B2444153 : Blo 1628513 2444153 := bstep (se 2 (by rfl) ⟨916557, by rfl⟩ : syracuseStep 2444153 = 1833115) B1833115
theorem B2444201 : Blo 1628513 2444201 := bstep (se 2 (by rfl) ⟨916575, by rfl⟩ : syracuseStep 2444201 = 1833151) B1833151
theorem B5221417 : Blo 1628513 5221417 := bstep (se 2 (by rfl) ⟨1958031, by rfl⟩ : syracuseStep 5221417 = 3916063) B3916063
theorem B2444351 : Blo 1628513 2444351 := bstep (se 1 (by rfl) ⟨1833263, by rfl⟩ : syracuseStep 2444351 = 3666527) B3666527
theorem B4123831 : Blo 1628513 4123831 := bstep (se 1 (by rfl) ⟨3092873, by rfl⟩ : syracuseStep 4123831 = 6185747) B6185747
theorem B3665375 : Blo 1628513 3665375 := bstep (se 1 (by rfl) ⟨2749031, by rfl⟩ : syracuseStep 3665375 = 5498063) B5498063
theorem B7433819 : Blo 1628513 7433819 := bstep (se 1 (by rfl) ⟨5575364, by rfl⟩ : syracuseStep 7433819 = 11150729) B11150729
theorem B3526247 : Blo 1628513 3526247 := bstep (se 1 (by rfl) ⟨2644685, by rfl⟩ : syracuseStep 3526247 = 5289371) B5289371
theorem B2444903 : Blo 1628513 2444903 := bstep (se 1 (by rfl) ⟨1833677, by rfl⟩ : syracuseStep 2444903 = 3667355) B3667355
theorem B3665591 : Blo 1628513 3665591 := bstep (se 1 (by rfl) ⟨2749193, by rfl⟩ : syracuseStep 3665591 = 5498387) B5498387
theorem B15658829 : Blo 1628513 15658829 := bstep (se 3 (by rfl) ⟨2936030, by rfl⟩ : syracuseStep 15658829 = 5872061) B5872061
theorem B3305387 : Blo 1628513 3305387 := bstep (se 1 (by rfl) ⟨2479040, by rfl⟩ : syracuseStep 3305387 = 4958081) B4958081
theorem B2445287 : Blo 1628513 2445287 := bstep (se 1 (by rfl) ⟨1833965, by rfl⟩ : syracuseStep 2445287 = 3667931) B3667931
theorem B11751419 : Blo 1628513 11751419 := bstep (se 1 (by rfl) ⟨8813564, by rfl⟩ : syracuseStep 11751419 = 17627129) B17627129
theorem B15659057 : Blo 1628513 15659057 := bstep (se 2 (by rfl) ⟨5872146, by rfl⟩ : syracuseStep 15659057 = 11744293) B11744293
theorem B2445407 : Blo 1628513 2445407 := bstep (se 1 (by rfl) ⟨1834055, by rfl⟩ : syracuseStep 2445407 = 3668111) B3668111
theorem B19820645 : Blo 1628513 19820645 := bstep (se 4 (by rfl) ⟨1858185, by rfl⟩ : syracuseStep 19820645 = 3716371) B3716371
theorem B2445419 : Blo 1628513 2445419 := bstep (se 1 (by rfl) ⟨1834064, by rfl⟩ : syracuseStep 2445419 = 3668129) B3668129
theorem B2748559 : Blo 1628513 2748559 := bstep (se 1 (by rfl) ⟨2061419, by rfl⟩ : syracuseStep 2748559 = 4122839) B4122839
theorem B10440859 : Blo 1628513 10440859 := bstep (se 1 (by rfl) ⟨7830644, by rfl⟩ : syracuseStep 10440859 = 15661289) B15661289
theorem B2445467 : Blo 1628513 2445467 := bstep (se 1 (by rfl) ⟨1834100, by rfl⟩ : syracuseStep 2445467 = 3668201) B3668201
theorem B2748775 : Blo 1628513 2748775 := bstep (se 1 (by rfl) ⟨2061581, by rfl⟩ : syracuseStep 2748775 = 4123163) B4123163
theorem B7827839 : Blo 1628513 7827839 := bstep (se 1 (by rfl) ⟨5870879, by rfl⟩ : syracuseStep 7827839 = 11741759) B11741759
theorem B3666383 : Blo 1628513 3666383 := bstep (se 1 (by rfl) ⟨2749787, by rfl⟩ : syracuseStep 3666383 = 5499575) B5499575
theorem B11751905 : Blo 1628513 11751905 := bstep (se 2 (by rfl) ⟨4406964, by rfl⟩ : syracuseStep 11751905 = 8813929) B8813929
theorem B16732781 : Blo 1628513 16732781 := bstep (se 3 (by rfl) ⟨3137396, by rfl⟩ : syracuseStep 16732781 = 6274793) B6274793
theorem B6189803 : Blo 1628513 6189803 := bstep (se 1 (by rfl) ⟨4642352, by rfl⟩ : syracuseStep 6189803 = 9284705) B9284705
theorem B2937683 : Blo 1628513 2937683 := bstep (se 1 (by rfl) ⟨2203262, by rfl⟩ : syracuseStep 2937683 = 4406525) B4406525
theorem B12890999 : Blo 1628513 12890999 := bstep (se 1 (by rfl) ⟨9668249, by rfl⟩ : syracuseStep 12890999 = 19336499) B19336499
theorem B2749511 : Blo 1628513 2749511 := bstep (se 1 (by rfl) ⟨2062133, by rfl⟩ : syracuseStep 2749511 = 4124267) B4124267
theorem B3667049 : Blo 1628513 3667049 := bstep (se 2 (by rfl) ⟨1375143, by rfl⟩ : syracuseStep 3667049 = 2750287) B2750287
theorem B6190289 : Blo 1628513 6190289 := bstep (se 2 (by rfl) ⟨2321358, by rfl⟩ : syracuseStep 6190289 = 4642717) B4642717
theorem B11744585 : Blo 1628513 11744585 := bstep (se 2 (by rfl) ⟨4404219, by rfl⟩ : syracuseStep 11744585 = 8808439) B8808439
theorem B9049499 : Blo 1628513 9049499 := bstep (se 1 (by rfl) ⟨6787124, by rfl⟩ : syracuseStep 9049499 = 13574249) B13574249
theorem B1832431 : Blo 1628513 1832431 := bstep (se 1 (by rfl) ⟨1374323, by rfl⟩ : syracuseStep 1832431 = 2748647) B2748647
theorem B1832539 : Blo 1628513 1832539 := bstep (se 1 (by rfl) ⟨1374404, by rfl⟩ : syracuseStep 1832539 = 2748809) B2748809
theorem B6960811 : Blo 1628513 6960811 := bstep (se 1 (by rfl) ⟨5220608, by rfl⟩ : syracuseStep 6960811 = 10441217) B10441217
theorem B3667679 : Blo 1628513 3667679 := bstep (se 1 (by rfl) ⟨2750759, by rfl⟩ : syracuseStep 3667679 = 5501519) B5501519
theorem B4642591 : Blo 1628513 4642591 := bstep (se 1 (by rfl) ⟨3481943, by rfl⟩ : syracuseStep 4642591 = 6963887) B6963887
theorem B1832827 : Blo 1628513 1832827 := bstep (se 1 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 1832827 = 2749241) B2749241
theorem B1832863 : Blo 1628513 1832863 := bstep (se 1 (by rfl) ⟨1374647, by rfl⟩ : syracuseStep 1832863 = 2749295) B2749295
theorem B13916123 : Blo 1628513 13916123 := bstep (se 1 (by rfl) ⟨10437092, by rfl⟩ : syracuseStep 13916123 = 20874185) B20874185
theorem B6961153 : Blo 1628513 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B3668039 : Blo 1628513 3668039 := bstep (se 1 (by rfl) ⟨2751029, by rfl⟩ : syracuseStep 3668039 = 5502059) B5502059
theorem B31324265 : Blo 1628513 31324265 := bstep (se 2 (by rfl) ⟨11746599, by rfl⟩ : syracuseStep 31324265 = 23493199) B23493199
theorem B4020577 : Blo 1628513 4020577 := bstep (se 2 (by rfl) ⟨1507716, by rfl⟩ : syracuseStep 4020577 = 3015433) B3015433
theorem B1628575 : Blo 1628513 1628575 := bstep (se 1 (by rfl) ⟨1221431, by rfl⟩ : syracuseStep 1628575 = 2442863) B2442863
theorem B10443167 : Blo 1628513 10443167 := bstep (se 1 (by rfl) ⟨7832375, by rfl⟩ : syracuseStep 10443167 = 15664751) B15664751
theorem B1628623 : Blo 1628513 1628623 := bstep (se 1 (by rfl) ⟨1221467, by rfl⟩ : syracuseStep 1628623 = 2442935) B2442935
theorem B4127183 : Blo 1628513 4127183 := bstep (se 1 (by rfl) ⟨3095387, by rfl⟩ : syracuseStep 4127183 = 6190775) B6190775
theorem B1628647 : Blo 1628513 1628647 := bstep (se 1 (by rfl) ⟨1221485, by rfl⟩ : syracuseStep 1628647 = 2442971) B2442971
theorem B1628763 : Blo 1628513 1628763 := bstep (se 1 (by rfl) ⟨1221572, by rfl⟩ : syracuseStep 1628763 = 2443145) B2443145
theorem B1628831 : Blo 1628513 1628831 := bstep (se 1 (by rfl) ⟨1221623, by rfl⟩ : syracuseStep 1628831 = 2443247) B2443247
theorem B3095273 : Blo 1628513 3095273 := bstep (se 2 (by rfl) ⟨1160727, by rfl⟩ : syracuseStep 3095273 = 2321455) B2321455
theorem B1628999 : Blo 1628513 1628999 := bstep (se 1 (by rfl) ⟨1221749, by rfl⟩ : syracuseStep 1628999 = 2443499) B2443499
theorem B1833799 : Blo 1628513 1833799 := bstep (se 1 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 1833799 = 2750699) B2750699
theorem B1629039 : Blo 1628513 1629039 := bstep (se 1 (by rfl) ⟨1221779, by rfl⟩ : syracuseStep 1629039 = 2443559) B2443559
theorem B1629095 : Blo 1628513 1629095 := bstep (se 1 (by rfl) ⟨1221821, by rfl⟩ : syracuseStep 1629095 = 2443643) B2443643
theorem B20872181 : Blo 1628513 20872181 := bstep (se 5 (by rfl) ⟨978383, by rfl⟩ : syracuseStep 20872181 = 1956767) B1956767
theorem B1629275 : Blo 1628513 1629275 := bstep (se 1 (by rfl) ⟨1221956, by rfl⟩ : syracuseStep 1629275 = 2443913) B2443913
theorem B1629391 : Blo 1628513 1629391 := bstep (se 1 (by rfl) ⟨1222043, by rfl⟩ : syracuseStep 1629391 = 2444087) B2444087
theorem B1629415 : Blo 1628513 1629415 := bstep (se 1 (by rfl) ⟨1222061, by rfl⟩ : syracuseStep 1629415 = 2444123) B2444123
theorem B8248553 : Blo 1628513 8248553 := bstep (se 2 (by rfl) ⟨3093207, by rfl⟩ : syracuseStep 8248553 = 6186415) B6186415
theorem B1629511 : Blo 1628513 1629511 := bstep (se 1 (by rfl) ⟨1222133, by rfl⟩ : syracuseStep 1629511 = 2444267) B2444267
theorem B13917521 : Blo 1628513 13917521 := bstep (se 2 (by rfl) ⟨5219070, by rfl⟩ : syracuseStep 13917521 = 10438141) B10438141
theorem B14867819 : Blo 1628513 14867819 := bstep (se 1 (by rfl) ⟨11150864, by rfl⟩ : syracuseStep 14867819 = 22301729) B22301729
theorem B1629647 : Blo 1628513 1629647 := bstep (se 1 (by rfl) ⟨1222235, by rfl⟩ : syracuseStep 1629647 = 2444471) B2444471
theorem B1629807 : Blo 1628513 1629807 := bstep (se 1 (by rfl) ⟨1222355, by rfl⟩ : syracuseStep 1629807 = 2444711) B2444711
theorem B17858191 : Blo 1628513 17858191 := bstep (se 1 (by rfl) ⟨13393643, by rfl⟩ : syracuseStep 17858191 = 26787287) B26787287
theorem B1629863 : Blo 1628513 1629863 := bstep (se 1 (by rfl) ⟨1222397, by rfl⟩ : syracuseStep 1629863 = 2444795) B2444795
theorem B1629927 : Blo 1628513 1629927 := bstep (se 1 (by rfl) ⟨1222445, by rfl⟩ : syracuseStep 1629927 = 2444891) B2444891
theorem B1629983 : Blo 1628513 1629983 := bstep (se 1 (by rfl) ⟨1222487, by rfl⟩ : syracuseStep 1629983 = 2444975) B2444975
theorem B1630063 : Blo 1628513 1630063 := bstep (se 1 (by rfl) ⟨1222547, by rfl⟩ : syracuseStep 1630063 = 2445095) B2445095
theorem B13926269 : Blo 1628513 13926269 := bstep (se 3 (by rfl) ⟨2611175, by rfl⟩ : syracuseStep 13926269 = 5222351) B5222351
theorem B3481499 : Blo 1628513 3481499 := bstep (se 1 (by rfl) ⟨2611124, by rfl⟩ : syracuseStep 3481499 = 5222249) B5222249
theorem B1630119 : Blo 1628513 1630119 := bstep (se 1 (by rfl) ⟨1222589, by rfl⟩ : syracuseStep 1630119 = 2445179) B2445179
theorem B9281537 : Blo 1628513 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B1630271 : Blo 1628513 1630271 := bstep (se 1 (by rfl) ⟨1222703, by rfl⟩ : syracuseStep 1630271 = 2445407) B2445407
theorem B13213763 : Blo 1628513 13213763 := bstep (se 1 (by rfl) ⟨9910322, by rfl⟩ : syracuseStep 13213763 = 19820645) B19820645
theorem B1630279 : Blo 1628513 1630279 := bstep (se 1 (by rfl) ⟨1222709, by rfl⟩ : syracuseStep 1630279 = 2445419) B2445419
theorem B1630311 : Blo 1628513 1630311 := bstep (se 1 (by rfl) ⟨1222733, by rfl⟩ : syracuseStep 1630311 = 2445467) B2445467
theorem B5218559 : Blo 1628513 5218559 := bstep (se 1 (by rfl) ⟨3913919, by rfl⟩ : syracuseStep 5218559 = 7827839) B7827839
theorem B1958455 : Blo 1628513 1958455 := bstep (se 1 (by rfl) ⟨1468841, by rfl⟩ : syracuseStep 1958455 = 2937683) B2937683
theorem B5497577 : Blo 1628513 5497577 := bstep (se 2 (by rfl) ⟨2061591, by rfl⟩ : syracuseStep 5497577 = 4123183) B4123183
theorem B41780447 : Blo 1628513 41780447 := bstep (se 1 (by rfl) ⟨31335335, by rfl⟩ : syracuseStep 41780447 = 62670671) B62670671
theorem B6964487 : Blo 1628513 6964487 := bstep (se 1 (by rfl) ⟨5223365, by rfl⟩ : syracuseStep 6964487 = 10446731) B10446731
theorem B67782035 : Blo 1628513 67782035 := bstep (se 1 (by rfl) ⟨50836526, by rfl⟩ : syracuseStep 67782035 = 101673053) B101673053
theorem B20882843 : Blo 1628513 20882843 := bstep (se 1 (by rfl) ⟨15662132, by rfl⟩ : syracuseStep 20882843 = 31324265) B31324265
theorem B13207013 : Blo 1628513 13207013 := bstep (se 4 (by rfl) ⟨1238157, by rfl⟩ : syracuseStep 13207013 = 2476315) B2476315
theorem B5498441 : Blo 1628513 5498441 := bstep (se 2 (by rfl) ⟨2061915, by rfl⟩ : syracuseStep 5498441 = 4123831) B4123831
theorem B2443241 : Blo 1628513 2443241 := bstep (se 2 (by rfl) ⟨916215, by rfl⟩ : syracuseStep 2443241 = 1832431) B1832431
theorem B2443385 : Blo 1628513 2443385 := bstep (se 2 (by rfl) ⟨916269, by rfl⟩ : syracuseStep 2443385 = 1832539) B1832539
theorem B5499035 : Blo 1628513 5499035 := bstep (se 1 (by rfl) ⟨4124276, by rfl⟩ : syracuseStep 5499035 = 8248553) B8248553
theorem B34375997 : Blo 1628513 34375997 := bstep (se 3 (by rfl) ⟨6445499, by rfl⟩ : syracuseStep 34375997 = 12890999) B12890999
theorem B2443583 : Blo 1628513 2443583 := bstep (se 1 (by rfl) ⟨1832687, by rfl⟩ : syracuseStep 2443583 = 3665375) B3665375
theorem B9283997 : Blo 1628513 9283997 := bstep (se 3 (by rfl) ⟨1740749, by rfl⟩ : syracuseStep 9283997 = 3481499) B3481499
theorem B2443727 : Blo 1628513 2443727 := bstep (se 1 (by rfl) ⟨1832795, by rfl⟩ : syracuseStep 2443727 = 3665591) B3665591
theorem B2443769 : Blo 1628513 2443769 := bstep (se 2 (by rfl) ⟨916413, by rfl⟩ : syracuseStep 2443769 = 1832827) B1832827
theorem B2443817 : Blo 1628513 2443817 := bstep (se 2 (by rfl) ⟨916431, by rfl⟩ : syracuseStep 2443817 = 1832863) B1832863
theorem B10439219 : Blo 1628513 10439219 := bstep (se 1 (by rfl) ⟨7829414, by rfl⟩ : syracuseStep 10439219 = 15658829) B15658829
theorem B9284179 : Blo 1628513 9284179 := bstep (se 1 (by rfl) ⟨6963134, by rfl⟩ : syracuseStep 9284179 = 13926269) B13926269
theorem B7834279 : Blo 1628513 7834279 := bstep (se 1 (by rfl) ⟨5875709, by rfl⟩ : syracuseStep 7834279 = 11751419) B11751419
theorem B10439371 : Blo 1628513 10439371 := bstep (se 1 (by rfl) ⟨7829528, by rfl⟩ : syracuseStep 10439371 = 15659057) B15659057
theorem B3664745 : Blo 1628513 3664745 := bstep (se 2 (by rfl) ⟨1374279, by rfl⟩ : syracuseStep 3664745 = 2748559) B2748559
theorem B35728235 : Blo 1628513 35728235 := bstep (se 1 (by rfl) ⟨26796176, by rfl⟩ : syracuseStep 35728235 = 53592353) B53592353
theorem B13921145 : Blo 1628513 13921145 := bstep (se 2 (by rfl) ⟨5220429, by rfl⟩ : syracuseStep 13921145 = 10440859) B10440859
theorem B3664763 : Blo 1628513 3664763 := bstep (se 1 (by rfl) ⟨2748572, by rfl⟩ : syracuseStep 3664763 = 5497145) B5497145
theorem B2444255 : Blo 1628513 2444255 := bstep (se 1 (by rfl) ⟨1833191, by rfl⟩ : syracuseStep 2444255 = 3666383) B3666383
theorem B3665033 : Blo 1628513 3665033 := bstep (se 2 (by rfl) ⟨1374387, by rfl⟩ : syracuseStep 3665033 = 2748775) B2748775
theorem B3665087 : Blo 1628513 3665087 := bstep (se 1 (by rfl) ⟨2748815, by rfl⟩ : syracuseStep 3665087 = 5497631) B5497631
theorem B2444699 : Blo 1628513 2444699 := bstep (se 1 (by rfl) ⟨1833524, by rfl⟩ : syracuseStep 2444699 = 3667049) B3667049
theorem B3091871 : Blo 1628513 3091871 := bstep (se 1 (by rfl) ⟨2318903, by rfl⟩ : syracuseStep 3091871 = 4637807) B4637807
theorem B6032999 : Blo 1628513 6032999 := bstep (se 1 (by rfl) ⟨4524749, by rfl⟩ : syracuseStep 6032999 = 9049499) B9049499
theorem B27160235 : Blo 1628513 27160235 := bstep (se 1 (by rfl) ⟨20370176, by rfl⟩ : syracuseStep 27160235 = 40740353) B40740353
theorem B2445065 : Blo 1628513 2445065 := bstep (se 2 (by rfl) ⟨916899, by rfl⟩ : syracuseStep 2445065 = 1833799) B1833799
theorem B2445119 : Blo 1628513 2445119 := bstep (se 1 (by rfl) ⟨1833839, by rfl⟩ : syracuseStep 2445119 = 3667679) B3667679
theorem B3665735 : Blo 1628513 3665735 := bstep (se 1 (by rfl) ⟨2749301, by rfl⟩ : syracuseStep 3665735 = 5498603) B5498603
theorem B31338413 : Blo 1628513 31338413 := bstep (se 3 (by rfl) ⟨5875952, by rfl⟩ : syracuseStep 31338413 = 11751905) B11751905
theorem B9277415 : Blo 1628513 9277415 := bstep (se 1 (by rfl) ⟨6958061, by rfl⟩ : syracuseStep 9277415 = 13916123) B13916123
theorem B3665915 : Blo 1628513 3665915 := bstep (se 1 (by rfl) ⟨2749436, by rfl⟩ : syracuseStep 3665915 = 5498873) B5498873
theorem B7434271 : Blo 1628513 7434271 := bstep (se 1 (by rfl) ⟨5575703, by rfl⟩ : syracuseStep 7434271 = 11151407) B11151407
theorem B2445359 : Blo 1628513 2445359 := bstep (se 1 (by rfl) ⟨1834019, by rfl⟩ : syracuseStep 2445359 = 3668039) B3668039
theorem B3666095 : Blo 1628513 3666095 := bstep (se 1 (by rfl) ⟨2749571, by rfl⟩ : syracuseStep 3666095 = 5499143) B5499143
theorem B4124915 : Blo 1628513 4124915 := bstep (se 1 (by rfl) ⟨3093686, by rfl⟩ : syracuseStep 4124915 = 6187373) B6187373
theorem B21443077 : Blo 1628513 21443077 := bstep (se 4 (by rfl) ⟨2010288, by rfl⟩ : syracuseStep 21443077 = 4020577) B4020577
theorem B8254061 : Blo 1628513 8254061 := bstep (se 3 (by rfl) ⟨1547636, by rfl⟩ : syracuseStep 8254061 = 3095273) B3095273
theorem B13914787 : Blo 1628513 13914787 := bstep (se 1 (by rfl) ⟨10436090, by rfl⟩ : syracuseStep 13914787 = 20872181) B20872181
theorem B23810921 : Blo 1628513 23810921 := bstep (se 2 (by rfl) ⟨8929095, by rfl⟩ : syracuseStep 23810921 = 17858191) B17858191
theorem B9278347 : Blo 1628513 9278347 := bstep (se 1 (by rfl) ⟨6958760, by rfl⟩ : syracuseStep 9278347 = 13917521) B13917521
theorem B6190121 : Blo 1628513 6190121 := bstep (se 2 (by rfl) ⟨2321295, by rfl⟩ : syracuseStep 6190121 = 4642591) B4642591
theorem B4642409 : Blo 1628513 4642409 := bstep (se 2 (by rfl) ⟨1740903, by rfl⟩ : syracuseStep 4642409 = 3481807) B3481807
theorem B14112391 : Blo 1628513 14112391 := bstep (se 1 (by rfl) ⟨10584293, by rfl⟩ : syracuseStep 14112391 = 21168587) B21168587
theorem B2610863 : Blo 1628513 2610863 := bstep (se 1 (by rfl) ⟨1958147, by rfl⟩ : syracuseStep 2610863 = 3916295) B3916295
theorem B11155187 : Blo 1628513 11155187 := bstep (se 1 (by rfl) ⟨8366390, by rfl⟩ : syracuseStep 11155187 = 16732781) B16732781
theorem B4126535 : Blo 1628513 4126535 := bstep (se 1 (by rfl) ⟨3094901, by rfl⟩ : syracuseStep 4126535 = 6189803) B6189803
theorem B1833007 : Blo 1628513 1833007 := bstep (se 1 (by rfl) ⟨1374755, by rfl⟩ : syracuseStep 1833007 = 2749511) B2749511
theorem B31332419 : Blo 1628513 31332419 := bstep (se 1 (by rfl) ⟨23499314, by rfl⟩ : syracuseStep 31332419 = 46998629) B46998629
theorem B10442857 : Blo 1628513 10442857 := bstep (se 2 (by rfl) ⟨3916071, by rfl⟩ : syracuseStep 10442857 = 7832143) B7832143
theorem B6609023 : Blo 1628513 6609023 := bstep (se 1 (by rfl) ⟨4956767, by rfl⟩ : syracuseStep 6609023 = 9913535) B9913535
theorem B4126859 : Blo 1628513 4126859 := bstep (se 1 (by rfl) ⟨3095144, by rfl⟩ : syracuseStep 4126859 = 6190289) B6190289
theorem B7829723 : Blo 1628513 7829723 := bstep (se 1 (by rfl) ⟨5872292, by rfl⟩ : syracuseStep 7829723 = 11744585) B11744585
theorem B2611483 : Blo 1628513 2611483 := bstep (se 1 (by rfl) ⟨1958612, by rfl⟩ : syracuseStep 2611483 = 3917225) B3917225
theorem B6183287 : Blo 1628513 6183287 := bstep (se 1 (by rfl) ⟨4637465, by rfl⟩ : syracuseStep 6183287 = 9274931) B9274931
theorem B1628543 : Blo 1628513 1628543 := bstep (se 1 (by rfl) ⟨1221407, by rfl⟩ : syracuseStep 1628543 = 2442815) B2442815
theorem B1628571 : Blo 1628513 1628571 := bstep (se 1 (by rfl) ⟨1221428, by rfl⟩ : syracuseStep 1628571 = 2442857) B2442857
theorem B8805023 : Blo 1628513 8805023 := bstep (se 1 (by rfl) ⟨6603767, by rfl⟩ : syracuseStep 8805023 = 13207535) B13207535
theorem B1628863 : Blo 1628513 1628863 := bstep (se 1 (by rfl) ⟨1221647, by rfl⟩ : syracuseStep 1628863 = 2443295) B2443295
theorem B6961889 : Blo 1628513 6961889 := bstep (se 2 (by rfl) ⟨2610708, by rfl⟩ : syracuseStep 6961889 = 5221417) B5221417
theorem B8362739 : Blo 1628513 8362739 := bstep (se 1 (by rfl) ⟨6272054, by rfl⟩ : syracuseStep 8362739 = 12544109) B12544109
theorem B20880179 : Blo 1628513 20880179 := bstep (se 1 (by rfl) ⟨15660134, by rfl⟩ : syracuseStep 20880179 = 31320269) B31320269
theorem B1628991 : Blo 1628513 1628991 := bstep (se 1 (by rfl) ⟨1221743, by rfl⟩ : syracuseStep 1628991 = 2443487) B2443487
theorem B1629031 : Blo 1628513 1629031 := bstep (se 1 (by rfl) ⟨1221773, by rfl⟩ : syracuseStep 1629031 = 2443547) B2443547
theorem B6962111 : Blo 1628513 6962111 := bstep (se 1 (by rfl) ⟨5221583, by rfl⟩ : syracuseStep 6962111 = 10443167) B10443167
theorem B2751455 : Blo 1628513 2751455 := bstep (se 1 (by rfl) ⟨2063591, by rfl⟩ : syracuseStep 2751455 = 4127183) B4127183
theorem B33430573 : Blo 1628513 33430573 := bstep (se 3 (by rfl) ⟨6268232, by rfl⟩ : syracuseStep 33430573 = 12536465) B12536465
theorem B1629247 : Blo 1628513 1629247 := bstep (se 1 (by rfl) ⟨1221935, by rfl⟩ : syracuseStep 1629247 = 2443871) B2443871
theorem B14867671 : Blo 1628513 14867671 := bstep (se 1 (by rfl) ⟨11150753, by rfl⟩ : syracuseStep 14867671 = 22301507) B22301507
theorem B1629435 : Blo 1628513 1629435 := bstep (se 1 (by rfl) ⟨1222076, by rfl⟩ : syracuseStep 1629435 = 2444153) B2444153
theorem B1629467 : Blo 1628513 1629467 := bstep (se 1 (by rfl) ⟨1222100, by rfl⟩ : syracuseStep 1629467 = 2444201) B2444201
theorem B1629567 : Blo 1628513 1629567 := bstep (se 1 (by rfl) ⟨1222175, by rfl⟩ : syracuseStep 1629567 = 2444351) B2444351
theorem B9281081 : Blo 1628513 9281081 := bstep (se 2 (by rfl) ⟨3480405, by rfl⟩ : syracuseStep 9281081 = 6960811) B6960811
theorem B9911879 : Blo 1628513 9911879 := bstep (se 1 (by rfl) ⟨7433909, by rfl⟩ : syracuseStep 9911879 = 14867819) B14867819
theorem B4955879 : Blo 1628513 4955879 := bstep (se 1 (by rfl) ⟨3716909, by rfl⟩ : syracuseStep 4955879 = 7433819) B7433819
theorem B2350831 : Blo 1628513 2350831 := bstep (se 1 (by rfl) ⟨1763123, by rfl⟩ : syracuseStep 2350831 = 3526247) B3526247
theorem B1629935 : Blo 1628513 1629935 := bstep (se 1 (by rfl) ⟨1222451, by rfl⟩ : syracuseStep 1629935 = 2444903) B2444903
theorem B2203591 : Blo 1628513 2203591 := bstep (se 1 (by rfl) ⟨1652693, by rfl⟩ : syracuseStep 2203591 = 3305387) B3305387
theorem B1630191 : Blo 1628513 1630191 := bstep (se 1 (by rfl) ⟨1222643, by rfl⟩ : syracuseStep 1630191 = 2445287) B2445287
theorem B1630239 : Blo 1628513 1630239 := bstep (se 1 (by rfl) ⟨1222679, by rfl⟩ : syracuseStep 1630239 = 2445359) B2445359
theorem B39649445 : Blo 1628513 39649445 := bstep (se 4 (by rfl) ⟨3717135, by rfl⟩ : syracuseStep 39649445 = 7434271) B7434271
theorem B28590769 : Blo 1628513 28590769 := bstep (se 2 (by rfl) ⟨10721538, by rfl⟩ : syracuseStep 28590769 = 21443077) B21443077
theorem B12378905 : Blo 1628513 12378905 := bstep (se 2 (by rfl) ⟨4642089, by rfl⟩ : syracuseStep 12378905 = 9284179) B9284179
theorem B27853631 : Blo 1628513 27853631 := bstep (se 1 (by rfl) ⟨20890223, by rfl⟩ : syracuseStep 27853631 = 41780447) B41780447
theorem B10445705 : Blo 1628513 10445705 := bstep (se 2 (by rfl) ⟨3917139, by rfl⟩ : syracuseStep 10445705 = 7834279) B7834279
theorem B45188023 : Blo 1628513 45188023 := bstep (se 1 (by rfl) ⟨33891017, by rfl⟩ : syracuseStep 45188023 = 67782035) B67782035
theorem B13919161 : Blo 1628513 13919161 := bstep (se 2 (by rfl) ⟨5219685, by rfl⟩ : syracuseStep 13919161 = 10439371) B10439371
theorem B12371129 : Blo 1628513 12371129 := bstep (se 2 (by rfl) ⟨4639173, by rfl⟩ : syracuseStep 12371129 = 9278347) B9278347
theorem B44574097 : Blo 1628513 44574097 := bstep (se 2 (by rfl) ⟨16715286, by rfl⟩ : syracuseStep 44574097 = 33430573) B33430573
theorem B13927909 : Blo 1628513 13927909 := bstep (se 4 (by rfl) ⟨1305741, by rfl⟩ : syracuseStep 13927909 = 2611483) B2611483
theorem B5219815 : Blo 1628513 5219815 := bstep (se 1 (by rfl) ⟨3914861, by rfl⟩ : syracuseStep 5219815 = 7829723) B7829723
theorem B4122191 : Blo 1628513 4122191 := bstep (se 1 (by rfl) ⟨3091643, by rfl⟩ : syracuseStep 4122191 = 6183287) B6183287
theorem B13920119 : Blo 1628513 13920119 := bstep (se 1 (by rfl) ⟨10440089, by rfl⟩ : syracuseStep 13920119 = 20880179) B20880179
theorem B2443163 : Blo 1628513 2443163 := bstep (se 1 (by rfl) ⟨1832372, by rfl⟩ : syracuseStep 2443163 = 3664745) B3664745
theorem B2443175 : Blo 1628513 2443175 := bstep (se 1 (by rfl) ⟨1832381, by rfl⟩ : syracuseStep 2443175 = 3664763) B3664763
theorem B2443355 : Blo 1628513 2443355 := bstep (se 1 (by rfl) ⟨1832516, by rfl⟩ : syracuseStep 2443355 = 3665033) B3665033
theorem B2443391 : Blo 1628513 2443391 := bstep (se 1 (by rfl) ⟨1832543, by rfl⟩ : syracuseStep 2443391 = 3665087) B3665087
theorem B6187387 : Blo 1628513 6187387 := bstep (se 1 (by rfl) ⟨4640540, by rfl⟩ : syracuseStep 6187387 = 9281081) B9281081
theorem B18106823 : Blo 1628513 18106823 := bstep (se 1 (by rfl) ⟨13580117, by rfl⟩ : syracuseStep 18106823 = 27160235) B27160235
theorem B3303919 : Blo 1628513 3303919 := bstep (se 1 (by rfl) ⟨2477939, by rfl⟩ : syracuseStep 3303919 = 4955879) B4955879
theorem B2443823 : Blo 1628513 2443823 := bstep (se 1 (by rfl) ⟨1832867, by rfl⟩ : syracuseStep 2443823 = 3665735) B3665735
theorem B20892275 : Blo 1628513 20892275 := bstep (se 1 (by rfl) ⟨15669206, by rfl⟩ : syracuseStep 20892275 = 31338413) B31338413
theorem B2443943 : Blo 1628513 2443943 := bstep (se 1 (by rfl) ⟨1832957, by rfl⟩ : syracuseStep 2443943 = 3665915) B3665915
theorem B6187691 : Blo 1628513 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B8809175 : Blo 1628513 8809175 := bstep (se 1 (by rfl) ⟨6606881, by rfl⟩ : syracuseStep 8809175 = 13213763) B13213763
theorem B2444009 : Blo 1628513 2444009 := bstep (se 2 (by rfl) ⟨916503, by rfl⟩ : syracuseStep 2444009 = 1833007) B1833007
theorem B2444063 : Blo 1628513 2444063 := bstep (se 1 (by rfl) ⟨1833047, by rfl⟩ : syracuseStep 2444063 = 3666095) B3666095
theorem B3665051 : Blo 1628513 3665051 := bstep (se 1 (by rfl) ⟨2748788, by rfl⟩ : syracuseStep 3665051 = 5497577) B5497577
theorem B13921895 : Blo 1628513 13921895 := bstep (se 1 (by rfl) ⟨10441421, by rfl⟩ : syracuseStep 13921895 = 20882843) B20882843
theorem B3665627 : Blo 1628513 3665627 := bstep (se 1 (by rfl) ⟨2749220, by rfl⟩ : syracuseStep 3665627 = 5498441) B5498441
theorem B8244989 : Blo 1628513 8244989 := bstep (se 3 (by rfl) ⟨1545935, by rfl⟩ : syracuseStep 8244989 = 3091871) B3091871
theorem B1740575 : Blo 1628513 1740575 := bstep (se 1 (by rfl) ⟨1305431, by rfl⟩ : syracuseStep 1740575 = 2610863) B2610863
theorem B3666023 : Blo 1628513 3666023 := bstep (se 1 (by rfl) ⟨2749517, by rfl⟩ : syracuseStep 3666023 = 5499035) B5499035
theorem B22917331 : Blo 1628513 22917331 := bstep (se 1 (by rfl) ⟨17187998, by rfl⟩ : syracuseStep 22917331 = 34375997) B34375997
theorem B6189331 : Blo 1628513 6189331 := bstep (se 1 (by rfl) ⟨4641998, by rfl⟩ : syracuseStep 6189331 = 9283997) B9283997
theorem B6959479 : Blo 1628513 6959479 := bstep (se 1 (by rfl) ⟨5219609, by rfl⟩ : syracuseStep 6959479 = 10439219) B10439219
theorem B5870015 : Blo 1628513 5870015 := bstep (se 1 (by rfl) ⟨4402511, by rfl⟩ : syracuseStep 5870015 = 8805023) B8805023
theorem B4641259 : Blo 1628513 4641259 := bstep (se 1 (by rfl) ⟨3480944, by rfl⟩ : syracuseStep 4641259 = 6961889) B6961889
theorem B5575159 : Blo 1628513 5575159 := bstep (se 1 (by rfl) ⟨4181369, by rfl⟩ : syracuseStep 5575159 = 8362739) B8362739
theorem B23818823 : Blo 1628513 23818823 := bstep (se 1 (by rfl) ⟨17864117, by rfl⟩ : syracuseStep 23818823 = 35728235) B35728235
theorem B4641407 : Blo 1628513 4641407 := bstep (se 1 (by rfl) ⟨3481055, by rfl⟩ : syracuseStep 4641407 = 6962111) B6962111
theorem B3134441 : Blo 1628513 3134441 := bstep (se 2 (by rfl) ⟨1175415, by rfl⟩ : syracuseStep 3134441 = 2350831) B2350831
theorem B6607919 : Blo 1628513 6607919 := bstep (se 1 (by rfl) ⟨4955939, by rfl⟩ : syracuseStep 6607919 = 9911879) B9911879
theorem B2938121 : Blo 1628513 2938121 := bstep (se 2 (by rfl) ⟨1101795, by rfl⟩ : syracuseStep 2938121 = 2203591) B2203591
theorem B13923809 : Blo 1628513 13923809 := bstep (se 2 (by rfl) ⟨5221428, by rfl⟩ : syracuseStep 13923809 = 10442857) B10442857
theorem B2749943 : Blo 1628513 2749943 := bstep (se 1 (by rfl) ⟨2062457, by rfl⟩ : syracuseStep 2749943 = 4124915) B4124915
theorem B3479039 : Blo 1628513 3479039 := bstep (se 1 (by rfl) ⟨2609279, by rfl⟩ : syracuseStep 3479039 = 5218559) B5218559
theorem B5502707 : Blo 1628513 5502707 := bstep (se 1 (by rfl) ⟨4127030, by rfl⟩ : syracuseStep 5502707 = 8254061) B8254061
theorem B15873947 : Blo 1628513 15873947 := bstep (se 1 (by rfl) ⟨11905460, by rfl⟩ : syracuseStep 15873947 = 23810921) B23810921
theorem B4126747 : Blo 1628513 4126747 := bstep (se 1 (by rfl) ⟨3095060, by rfl⟩ : syracuseStep 4126747 = 6190121) B6190121
theorem B2611273 : Blo 1628513 2611273 := bstep (se 2 (by rfl) ⟨979227, by rfl⟩ : syracuseStep 2611273 = 1958455) B1958455
theorem B4642991 : Blo 1628513 4642991 := bstep (se 1 (by rfl) ⟨3482243, by rfl⟩ : syracuseStep 4642991 = 6964487) B6964487
theorem B18553049 : Blo 1628513 18553049 := bstep (se 2 (by rfl) ⟨6957393, by rfl⟩ : syracuseStep 18553049 = 13914787) B13914787
theorem B8804675 : Blo 1628513 8804675 := bstep (se 1 (by rfl) ⟨6603506, by rfl⟩ : syracuseStep 8804675 = 13207013) B13207013
theorem B3094939 : Blo 1628513 3094939 := bstep (se 1 (by rfl) ⟨2321204, by rfl⟩ : syracuseStep 3094939 = 4642409) B4642409
theorem B7436791 : Blo 1628513 7436791 := bstep (se 1 (by rfl) ⟨5577593, by rfl⟩ : syracuseStep 7436791 = 11155187) B11155187
theorem B2751023 : Blo 1628513 2751023 := bstep (se 1 (by rfl) ⟨2063267, by rfl⟩ : syracuseStep 2751023 = 4126535) B4126535
theorem B1628827 : Blo 1628513 1628827 := bstep (se 1 (by rfl) ⟨1221620, by rfl⟩ : syracuseStep 1628827 = 2443241) B2443241
theorem B20888279 : Blo 1628513 20888279 := bstep (se 1 (by rfl) ⟨15666209, by rfl⟩ : syracuseStep 20888279 = 31332419) B31332419
theorem B1628923 : Blo 1628513 1628923 := bstep (se 1 (by rfl) ⟨1221692, by rfl⟩ : syracuseStep 1628923 = 2443385) B2443385
theorem B4406015 : Blo 1628513 4406015 := bstep (se 1 (by rfl) ⟨3304511, by rfl⟩ : syracuseStep 4406015 = 6609023) B6609023
theorem B2751239 : Blo 1628513 2751239 := bstep (se 1 (by rfl) ⟨2063429, by rfl⟩ : syracuseStep 2751239 = 4126859) B4126859
theorem B1629055 : Blo 1628513 1629055 := bstep (se 1 (by rfl) ⟨1221791, by rfl⟩ : syracuseStep 1629055 = 2443583) B2443583
theorem B16087997 : Blo 1628513 16087997 := bstep (se 3 (by rfl) ⟨3016499, by rfl⟩ : syracuseStep 16087997 = 6032999) B6032999
theorem B19823561 : Blo 1628513 19823561 := bstep (se 2 (by rfl) ⟨7433835, by rfl⟩ : syracuseStep 19823561 = 14867671) B14867671
theorem B1629151 : Blo 1628513 1629151 := bstep (se 1 (by rfl) ⟨1221863, by rfl⟩ : syracuseStep 1629151 = 2443727) B2443727
theorem B1629179 : Blo 1628513 1629179 := bstep (se 1 (by rfl) ⟨1221884, by rfl⟩ : syracuseStep 1629179 = 2443769) B2443769
theorem B1629211 : Blo 1628513 1629211 := bstep (se 1 (by rfl) ⟨1221908, by rfl⟩ : syracuseStep 1629211 = 2443817) B2443817
theorem B9280763 : Blo 1628513 9280763 := bstep (se 1 (by rfl) ⟨6960572, by rfl⟩ : syracuseStep 9280763 = 13921145) B13921145
theorem B1629503 : Blo 1628513 1629503 := bstep (se 1 (by rfl) ⟨1222127, by rfl⟩ : syracuseStep 1629503 = 2444255) B2444255
theorem B1834303 : Blo 1628513 1834303 := bstep (se 1 (by rfl) ⟨1375727, by rfl⟩ : syracuseStep 1834303 = 2751455) B2751455
theorem B18816521 : Blo 1628513 18816521 := bstep (se 2 (by rfl) ⟨7056195, by rfl⟩ : syracuseStep 18816521 = 14112391) B14112391
theorem B1629799 : Blo 1628513 1629799 := bstep (se 1 (by rfl) ⟨1222349, by rfl⟩ : syracuseStep 1629799 = 2444699) B2444699
theorem B1630043 : Blo 1628513 1630043 := bstep (se 1 (by rfl) ⟨1222532, by rfl⟩ : syracuseStep 1630043 = 2445065) B2445065
theorem B1630079 : Blo 1628513 1630079 := bstep (se 1 (by rfl) ⟨1222559, by rfl⟩ : syracuseStep 1630079 = 2445119) B2445119
theorem B6184943 : Blo 1628513 6184943 := bstep (se 1 (by rfl) ⟨4638707, by rfl⟩ : syracuseStep 6184943 = 9277415) B9277415
theorem B3481697 : Blo 1628513 3481697 := bstep (se 2 (by rfl) ⟨1305636, by rfl⟩ : syracuseStep 3481697 = 2611273) B2611273
theorem B8249849 : Blo 1628513 8249849 := bstep (se 2 (by rfl) ⟨3093693, by rfl⟩ : syracuseStep 8249849 = 6187387) B6187387
theorem B6963803 : Blo 1628513 6963803 := bstep (se 1 (by rfl) ⟨5222852, by rfl⟩ : syracuseStep 6963803 = 10445705) B10445705
theorem B1958747 : Blo 1628513 1958747 := bstep (se 1 (by rfl) ⟨1469060, by rfl⟩ : syracuseStep 1958747 = 2938121) B2938121
theorem B9282539 : Blo 1628513 9282539 := bstep (se 1 (by rfl) ⟨6961904, by rfl⟩ : syracuseStep 9282539 = 13923809) B13923809
theorem B2319359 : Blo 1628513 2319359 := bstep (se 1 (by rfl) ⟨1739519, by rfl⟩ : syracuseStep 2319359 = 3479039) B3479039
theorem B122225765 : Blo 1628513 122225765 := bstep (se 4 (by rfl) ⟨11458665, by rfl⟩ : syracuseStep 122225765 = 22917331) B22917331
theorem B50177389 : Blo 1628513 50177389 := bstep (se 3 (by rfl) ⟨9408260, by rfl⟩ : syracuseStep 50177389 = 18816521) B18816521
theorem B13928183 : Blo 1628513 13928183 := bstep (se 1 (by rfl) ⟨10446137, by rfl⟩ : syracuseStep 13928183 = 20892275) B20892275
theorem B10725331 : Blo 1628513 10725331 := bstep (se 1 (by rfl) ⟨8043998, by rfl⟩ : syracuseStep 10725331 = 16087997) B16087997
theorem B13215707 : Blo 1628513 13215707 := bstep (se 1 (by rfl) ⟨9911780, by rfl⟩ : syracuseStep 13215707 = 19823561) B19823561
theorem B2443367 : Blo 1628513 2443367 := bstep (se 1 (by rfl) ⟨1832525, by rfl⟩ : syracuseStep 2443367 = 3665051) B3665051
theorem B6187175 : Blo 1628513 6187175 := bstep (se 1 (by rfl) ⟨4640381, by rfl⟩ : syracuseStep 6187175 = 9280763) B9280763
theorem B2443751 : Blo 1628513 2443751 := bstep (se 1 (by rfl) ⟨1832813, by rfl⟩ : syracuseStep 2443751 = 3665627) B3665627
theorem B8358509 : Blo 1628513 8358509 := bstep (se 3 (by rfl) ⟨1567220, by rfl⟩ : syracuseStep 8358509 = 3134441) B3134441
theorem B4123295 : Blo 1628513 4123295 := bstep (se 1 (by rfl) ⟨3092471, by rfl⟩ : syracuseStep 4123295 = 6184943) B6184943
theorem B2444015 : Blo 1628513 2444015 := bstep (se 1 (by rfl) ⟨1833011, by rfl⟩ : syracuseStep 2444015 = 3666023) B3666023
theorem B8252441 : Blo 1628513 8252441 := bstep (se 2 (by rfl) ⟨3094665, by rfl⟩ : syracuseStep 8252441 = 6189331) B6189331
theorem B15879215 : Blo 1628513 15879215 := bstep (se 1 (by rfl) ⟨11909411, by rfl⟩ : syracuseStep 15879215 = 23818823) B23818823
theorem B8252603 : Blo 1628513 8252603 := bstep (se 1 (by rfl) ⟨6189452, by rfl⟩ : syracuseStep 8252603 = 12378905) B12378905
theorem B6188345 : Blo 1628513 6188345 := bstep (se 2 (by rfl) ⟨2320629, by rfl⟩ : syracuseStep 6188345 = 4641259) B4641259
theorem B7433545 : Blo 1628513 7433545 := bstep (se 2 (by rfl) ⟨2787579, by rfl⟩ : syracuseStep 7433545 = 5575159) B5575159
theorem B38121025 : Blo 1628513 38121025 := bstep (se 2 (by rfl) ⟨14295384, by rfl⟩ : syracuseStep 38121025 = 28590769) B28590769
theorem B2748127 : Blo 1628513 2748127 := bstep (se 1 (by rfl) ⟨2061095, by rfl⟩ : syracuseStep 2748127 = 4122191) B4122191
theorem B18558881 : Blo 1628513 18558881 := bstep (se 2 (by rfl) ⟨6959580, by rfl⟩ : syracuseStep 18558881 = 13919161) B13919161
theorem B5869783 : Blo 1628513 5869783 := bstep (se 1 (by rfl) ⟨4402337, by rfl⟩ : syracuseStep 5869783 = 8804675) B8804675
theorem B12071215 : Blo 1628513 12071215 := bstep (se 1 (by rfl) ⟨9053411, by rfl⟩ : syracuseStep 12071215 = 18106823) B18106823
theorem B2445737 : Blo 1628513 2445737 := bstep (se 2 (by rfl) ⟨917151, by rfl⟩ : syracuseStep 2445737 = 1834303) B1834303
theorem B4125127 : Blo 1628513 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B2937343 : Blo 1628513 2937343 := bstep (se 1 (by rfl) ⟨2203007, by rfl⟩ : syracuseStep 2937343 = 4406015) B4406015
theorem B6959753 : Blo 1628513 6959753 := bstep (se 2 (by rfl) ⟨2609907, by rfl⟩ : syracuseStep 6959753 = 5219815) B5219815
theorem B4641533 : Blo 1628513 4641533 := bstep (se 3 (by rfl) ⟨870287, by rfl⟩ : syracuseStep 4641533 = 1740575) B1740575
theorem B39662885 : Blo 1628513 39662885 := bstep (se 4 (by rfl) ⟨3718395, by rfl⟩ : syracuseStep 39662885 = 7436791) B7436791
theorem B5502329 : Blo 1628513 5502329 := bstep (se 2 (by rfl) ⟨2063373, by rfl⟩ : syracuseStep 5502329 = 4126747) B4126747
theorem B26432963 : Blo 1628513 26432963 := bstep (se 1 (by rfl) ⟨19824722, by rfl⟩ : syracuseStep 26432963 = 39649445) B39649445
theorem B3913343 : Blo 1628513 3913343 := bstep (se 1 (by rfl) ⟨2935007, by rfl⟩ : syracuseStep 3913343 = 5870015) B5870015
theorem B3094271 : Blo 1628513 3094271 := bstep (se 1 (by rfl) ⟨2320703, by rfl⟩ : syracuseStep 3094271 = 4641407) B4641407
theorem B9279305 : Blo 1628513 9279305 := bstep (se 2 (by rfl) ⟨3479739, by rfl⟩ : syracuseStep 9279305 = 6959479) B6959479
theorem B4126585 : Blo 1628513 4126585 := bstep (se 2 (by rfl) ⟨1547469, by rfl⟩ : syracuseStep 4126585 = 3094939) B3094939
theorem B18569087 : Blo 1628513 18569087 := bstep (se 1 (by rfl) ⟨13926815, by rfl⟩ : syracuseStep 18569087 = 27853631) B27853631
theorem B4405279 : Blo 1628513 4405279 := bstep (se 1 (by rfl) ⟨3303959, by rfl⟩ : syracuseStep 4405279 = 6607919) B6607919
theorem B8247419 : Blo 1628513 8247419 := bstep (se 1 (by rfl) ⟨6185564, by rfl⟩ : syracuseStep 8247419 = 12371129) B12371129
theorem B1833295 : Blo 1628513 1833295 := bstep (se 1 (by rfl) ⟨1374971, by rfl⟩ : syracuseStep 1833295 = 2749943) B2749943
theorem B3668471 : Blo 1628513 3668471 := bstep (se 1 (by rfl) ⟨2751353, by rfl⟩ : syracuseStep 3668471 = 5502707) B5502707
theorem B60250697 : Blo 1628513 60250697 := bstep (se 2 (by rfl) ⟨22594011, by rfl⟩ : syracuseStep 60250697 = 45188023) B45188023
theorem B9280079 : Blo 1628513 9280079 := bstep (se 1 (by rfl) ⟨6960059, by rfl⟩ : syracuseStep 9280079 = 13920119) B13920119
theorem B1628775 : Blo 1628513 1628775 := bstep (se 1 (by rfl) ⟨1221581, by rfl⟩ : syracuseStep 1628775 = 2443163) B2443163
theorem B10582631 : Blo 1628513 10582631 := bstep (se 1 (by rfl) ⟨7936973, by rfl⟩ : syracuseStep 10582631 = 15873947) B15873947
theorem B1628783 : Blo 1628513 1628783 := bstep (se 1 (by rfl) ⟨1221587, by rfl⟩ : syracuseStep 1628783 = 2443175) B2443175
theorem B1628903 : Blo 1628513 1628903 := bstep (se 1 (by rfl) ⟨1221677, by rfl⟩ : syracuseStep 1628903 = 2443355) B2443355
theorem B1628927 : Blo 1628513 1628927 := bstep (se 1 (by rfl) ⟨1221695, by rfl⟩ : syracuseStep 1628927 = 2443391) B2443391
theorem B3095327 : Blo 1628513 3095327 := bstep (se 1 (by rfl) ⟨2321495, by rfl⟩ : syracuseStep 3095327 = 4642991) B4642991
theorem B12368699 : Blo 1628513 12368699 := bstep (se 1 (by rfl) ⟨9276524, by rfl⟩ : syracuseStep 12368699 = 18553049) B18553049
theorem B1629215 : Blo 1628513 1629215 := bstep (se 1 (by rfl) ⟨1221911, by rfl⟩ : syracuseStep 1629215 = 2443823) B2443823
theorem B1834015 : Blo 1628513 1834015 := bstep (se 1 (by rfl) ⟨1375511, by rfl⟩ : syracuseStep 1834015 = 2751023) B2751023
theorem B1629295 : Blo 1628513 1629295 := bstep (se 1 (by rfl) ⟨1221971, by rfl⟩ : syracuseStep 1629295 = 2443943) B2443943
theorem B5872783 : Blo 1628513 5872783 := bstep (se 1 (by rfl) ⟨4404587, by rfl⟩ : syracuseStep 5872783 = 8809175) B8809175
theorem B13925519 : Blo 1628513 13925519 := bstep (se 1 (by rfl) ⟨10444139, by rfl⟩ : syracuseStep 13925519 = 20888279) B20888279
theorem B1629339 : Blo 1628513 1629339 := bstep (se 1 (by rfl) ⟨1222004, by rfl⟩ : syracuseStep 1629339 = 2444009) B2444009
theorem B1834159 : Blo 1628513 1834159 := bstep (se 1 (by rfl) ⟨1375619, by rfl⟩ : syracuseStep 1834159 = 2751239) B2751239
theorem B1629375 : Blo 1628513 1629375 := bstep (se 1 (by rfl) ⟨1222031, by rfl⟩ : syracuseStep 1629375 = 2444063) B2444063
theorem B59432129 : Blo 1628513 59432129 := bstep (se 2 (by rfl) ⟨22287048, by rfl⟩ : syracuseStep 59432129 = 44574097) B44574097
theorem B18570545 : Blo 1628513 18570545 := bstep (se 2 (by rfl) ⟨6963954, by rfl⟩ : syracuseStep 18570545 = 13927909) B13927909
theorem B9281263 : Blo 1628513 9281263 := bstep (se 1 (by rfl) ⟨6960947, by rfl⟩ : syracuseStep 9281263 = 13921895) B13921895
theorem B5496659 : Blo 1628513 5496659 := bstep (se 1 (by rfl) ⟨4122494, by rfl⟩ : syracuseStep 5496659 = 8244989) B8244989
theorem B17620901 : Blo 1628513 17620901 := bstep (se 4 (by rfl) ⟨1651959, by rfl⟩ : syracuseStep 17620901 = 3303919) B3303919
theorem B5873705 : Blo 1628513 5873705 := bstep (se 2 (by rfl) ⟨2202639, by rfl⟩ : syracuseStep 5873705 = 4405279) B4405279
theorem B325935373 : Blo 1628513 325935373 := bstep (se 3 (by rfl) ⟨61112882, by rfl⟩ : syracuseStep 325935373 = 122225765) B122225765
theorem B1630491 : Blo 1628513 1630491 := bstep (se 1 (by rfl) ⟨1222868, by rfl⟩ : syracuseStep 1630491 = 2445737) B2445737
theorem B3916457 : Blo 1628513 3916457 := bstep (se 2 (by rfl) ⟨1468671, by rfl⟩ : syracuseStep 3916457 = 2937343) B2937343
theorem B17621975 : Blo 1628513 17621975 := bstep (se 1 (by rfl) ⟨13216481, by rfl⟩ : syracuseStep 17621975 = 26432963) B26432963
theorem B6186203 : Blo 1628513 6186203 := bstep (se 1 (by rfl) ⟨4639652, by rfl⟩ : syracuseStep 6186203 = 9279305) B9279305
theorem B12379391 : Blo 1628513 12379391 := bstep (se 1 (by rfl) ⟨9284543, by rfl⟩ : syracuseStep 12379391 = 18569087) B18569087
theorem B5498279 : Blo 1628513 5498279 := bstep (se 1 (by rfl) ⟨4123709, by rfl⟩ : syracuseStep 5498279 = 8247419) B8247419
theorem B40167131 : Blo 1628513 40167131 := bstep (se 1 (by rfl) ⟨30125348, by rfl⟩ : syracuseStep 40167131 = 60250697) B60250697
theorem B6186719 : Blo 1628513 6186719 := bstep (se 1 (by rfl) ⟨4640039, by rfl⟩ : syracuseStep 6186719 = 9280079) B9280079
theorem B7055087 : Blo 1628513 7055087 := bstep (se 1 (by rfl) ⟨5291315, by rfl⟩ : syracuseStep 7055087 = 10582631) B10582631
theorem B10586143 : Blo 1628513 10586143 := bstep (se 1 (by rfl) ⟨7939607, by rfl⟩ : syracuseStep 10586143 = 15879215) B15879215
theorem B9283679 : Blo 1628513 9283679 := bstep (se 1 (by rfl) ⟨6962759, by rfl⟩ : syracuseStep 9283679 = 13925519) B13925519
theorem B12380363 : Blo 1628513 12380363 := bstep (se 1 (by rfl) ⟨9285272, by rfl⟩ : syracuseStep 12380363 = 18570545) B18570545
theorem B3664169 : Blo 1628513 3664169 := bstep (se 2 (by rfl) ⟨1374063, by rfl⟩ : syracuseStep 3664169 = 2748127) B2748127
theorem B3664439 : Blo 1628513 3664439 := bstep (se 1 (by rfl) ⟨2748329, by rfl⟩ : syracuseStep 3664439 = 5496659) B5496659
theorem B12372587 : Blo 1628513 12372587 := bstep (se 1 (by rfl) ⟨9279440, by rfl⟩ : syracuseStep 12372587 = 18558881) B18558881
theorem B2321131 : Blo 1628513 2321131 := bstep (se 1 (by rfl) ⟨1740848, by rfl⟩ : syracuseStep 2321131 = 3481697) B3481697
theorem B7826377 : Blo 1628513 7826377 := bstep (se 2 (by rfl) ⟨2934891, by rfl⟩ : syracuseStep 7826377 = 5869783) B5869783
theorem B5499899 : Blo 1628513 5499899 := bstep (se 1 (by rfl) ⟨4124924, by rfl⟩ : syracuseStep 5499899 = 8249849) B8249849
theorem B4639835 : Blo 1628513 4639835 := bstep (se 1 (by rfl) ⟨3479876, by rfl⟩ : syracuseStep 4639835 = 6959753) B6959753
theorem B2444393 : Blo 1628513 2444393 := bstep (se 2 (by rfl) ⟨916647, by rfl⟩ : syracuseStep 2444393 = 1833295) B1833295
theorem B5500169 : Blo 1628513 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B6188359 : Blo 1628513 6188359 := bstep (se 1 (by rfl) ⟨4641269, by rfl⟩ : syracuseStep 6188359 = 9282539) B9282539
theorem B20893301 : Blo 1628513 20893301 := bstep (se 5 (by rfl) ⟨979373, by rfl⟩ : syracuseStep 20893301 = 1958747) B1958747
theorem B2608895 : Blo 1628513 2608895 := bstep (se 1 (by rfl) ⟨1956671, by rfl⟩ : syracuseStep 2608895 = 3913343) B3913343
theorem B9285455 : Blo 1628513 9285455 := bstep (se 1 (by rfl) ⟨6964091, by rfl⟩ : syracuseStep 9285455 = 13928183) B13928183
theorem B8810471 : Blo 1628513 8810471 := bstep (se 1 (by rfl) ⟨6607853, by rfl⟩ : syracuseStep 8810471 = 13215707) B13215707
theorem B2445353 : Blo 1628513 2445353 := bstep (se 2 (by rfl) ⟨917007, by rfl⟩ : syracuseStep 2445353 = 1834015) B1834015
theorem B4124783 : Blo 1628513 4124783 := bstep (se 1 (by rfl) ⟨3093587, by rfl⟩ : syracuseStep 4124783 = 6187175) B6187175
theorem B2445545 : Blo 1628513 2445545 := bstep (se 2 (by rfl) ⟨917079, by rfl⟩ : syracuseStep 2445545 = 1834159) B1834159
theorem B2445647 : Blo 1628513 2445647 := bstep (se 1 (by rfl) ⟨1834235, by rfl⟩ : syracuseStep 2445647 = 3668471) B3668471
theorem B2748863 : Blo 1628513 2748863 := bstep (se 1 (by rfl) ⟨2061647, by rfl⟩ : syracuseStep 2748863 = 4123295) B4123295
theorem B8245799 : Blo 1628513 8245799 := bstep (se 1 (by rfl) ⟨6184349, by rfl⟩ : syracuseStep 8245799 = 12368699) B12368699
theorem B5501627 : Blo 1628513 5501627 := bstep (se 1 (by rfl) ⟨4126220, by rfl⟩ : syracuseStep 5501627 = 8252441) B8252441
theorem B50828033 : Blo 1628513 50828033 := bstep (se 2 (by rfl) ⟨19060512, by rfl⟩ : syracuseStep 50828033 = 38121025) B38121025
theorem B5501735 : Blo 1628513 5501735 := bstep (se 1 (by rfl) ⟨4126301, by rfl⟩ : syracuseStep 5501735 = 8252603) B8252603
theorem B39621419 : Blo 1628513 39621419 := bstep (se 1 (by rfl) ⟨29716064, by rfl⟩ : syracuseStep 39621419 = 59432129) B59432129
theorem B4125563 : Blo 1628513 4125563 := bstep (se 1 (by rfl) ⟨3094172, by rfl⟩ : syracuseStep 4125563 = 6188345) B6188345
theorem B12375017 : Blo 1628513 12375017 := bstep (se 2 (by rfl) ⟨4640631, by rfl⟩ : syracuseStep 12375017 = 9281263) B9281263
theorem B5502113 : Blo 1628513 5502113 := bstep (se 2 (by rfl) ⟨2063292, by rfl⟩ : syracuseStep 5502113 = 4126585) B4126585
theorem B14300441 : Blo 1628513 14300441 := bstep (se 2 (by rfl) ⟨5362665, by rfl⟩ : syracuseStep 14300441 = 10725331) B10725331
theorem B4642535 : Blo 1628513 4642535 := bstep (se 1 (by rfl) ⟨3481901, by rfl⟩ : syracuseStep 4642535 = 6963803) B6963803
theorem B16094953 : Blo 1628513 16094953 := bstep (se 2 (by rfl) ⟨6035607, by rfl⟩ : syracuseStep 16094953 = 12071215) B12071215
theorem B3094355 : Blo 1628513 3094355 := bstep (se 1 (by rfl) ⟨2320766, by rfl⟩ : syracuseStep 3094355 = 4641533) B4641533
theorem B26441923 : Blo 1628513 26441923 := bstep (se 1 (by rfl) ⟨19831442, by rfl⟩ : syracuseStep 26441923 = 39662885) B39662885
theorem B3668219 : Blo 1628513 3668219 := bstep (se 1 (by rfl) ⟨2751164, by rfl⟩ : syracuseStep 3668219 = 5502329) B5502329
theorem B2062847 : Blo 1628513 2062847 := bstep (se 1 (by rfl) ⟨1547135, by rfl⟩ : syracuseStep 2062847 = 3094271) B3094271
theorem B1628911 : Blo 1628513 1628911 := bstep (se 1 (by rfl) ⟨1221683, by rfl⟩ : syracuseStep 1628911 = 2443367) B2443367
theorem B7830377 : Blo 1628513 7830377 := bstep (se 2 (by rfl) ⟨2936391, by rfl⟩ : syracuseStep 7830377 = 5872783) B5872783
theorem B22289357 : Blo 1628513 22289357 := bstep (se 3 (by rfl) ⟨4179254, by rfl⟩ : syracuseStep 22289357 = 8358509) B8358509
theorem B1629167 : Blo 1628513 1629167 := bstep (se 1 (by rfl) ⟨1221875, by rfl⟩ : syracuseStep 1629167 = 2443751) B2443751
theorem B9911393 : Blo 1628513 9911393 := bstep (se 2 (by rfl) ⟨3716772, by rfl⟩ : syracuseStep 9911393 = 7433545) B7433545
theorem B66903185 : Blo 1628513 66903185 := bstep (se 2 (by rfl) ⟨25088694, by rfl⟩ : syracuseStep 66903185 = 50177389) B50177389
theorem B1629343 : Blo 1628513 1629343 := bstep (se 1 (by rfl) ⟨1222007, by rfl⟩ : syracuseStep 1629343 = 2444015) B2444015
theorem B2063551 : Blo 1628513 2063551 := bstep (se 1 (by rfl) ⟨1547663, by rfl⟩ : syracuseStep 2063551 = 3095327) B3095327
theorem B11747267 : Blo 1628513 11747267 := bstep (se 1 (by rfl) ⟨8810450, by rfl⟩ : syracuseStep 11747267 = 17620901) B17620901
theorem B6184957 : Blo 1628513 6184957 := bstep (se 3 (by rfl) ⟨1159679, by rfl⟩ : syracuseStep 6184957 = 2319359) B2319359
theorem B3915803 : Blo 1628513 3915803 := bstep (se 1 (by rfl) ⟨2936852, by rfl⟩ : syracuseStep 3915803 = 5873705) B5873705
theorem B1630235 : Blo 1628513 1630235 := bstep (se 1 (by rfl) ⟨1222676, by rfl⟩ : syracuseStep 1630235 = 2445353) B2445353
theorem B14114857 : Blo 1628513 14114857 := bstep (se 2 (by rfl) ⟨5293071, by rfl⟩ : syracuseStep 14114857 = 10586143) B10586143
theorem B1630363 : Blo 1628513 1630363 := bstep (se 1 (by rfl) ⟨1222772, by rfl⟩ : syracuseStep 1630363 = 2445545) B2445545
theorem B1630431 : Blo 1628513 1630431 := bstep (se 1 (by rfl) ⟨1222823, by rfl⟩ : syracuseStep 1630431 = 2445647) B2445647
theorem B5497199 : Blo 1628513 5497199 := bstep (se 1 (by rfl) ⟨4122899, by rfl⟩ : syracuseStep 5497199 = 8245799) B8245799
theorem B8250011 : Blo 1628513 8250011 := bstep (se 1 (by rfl) ⟨6187508, by rfl⟩ : syracuseStep 8250011 = 12375017) B12375017
theorem B2442779 : Blo 1628513 2442779 := bstep (se 1 (by rfl) ⟨1832084, by rfl⟩ : syracuseStep 2442779 = 3664169) B3664169
theorem B2442959 : Blo 1628513 2442959 := bstep (se 1 (by rfl) ⟨1832219, by rfl⟩ : syracuseStep 2442959 = 3664439) B3664439
theorem B8251145 : Blo 1628513 8251145 := bstep (se 2 (by rfl) ⟨3094179, by rfl⟩ : syracuseStep 8251145 = 6188359) B6188359
theorem B5220251 : Blo 1628513 5220251 := bstep (se 1 (by rfl) ⟨3915188, by rfl⟩ : syracuseStep 5220251 = 7830377) B7830377
theorem B107112349 : Blo 1628513 107112349 := bstep (se 3 (by rfl) ⟨20083565, by rfl⟩ : syracuseStep 107112349 = 40167131) B40167131
theorem B6957053 : Blo 1628513 6957053 := bstep (se 3 (by rfl) ⟨1304447, by rfl⟩ : syracuseStep 6957053 = 2608895) B2608895
theorem B13928867 : Blo 1628513 13928867 := bstep (se 1 (by rfl) ⟨10446650, by rfl⟩ : syracuseStep 13928867 = 20893301) B20893301
theorem B46991933 : Blo 1628513 46991933 := bstep (se 3 (by rfl) ⟨8810987, by rfl⟩ : syracuseStep 46991933 = 17621975) B17621975
theorem B434580497 : Blo 1628513 434580497 := bstep (se 2 (by rfl) ⟨162967686, by rfl⟩ : syracuseStep 434580497 = 325935373) B325935373
theorem B26414279 : Blo 1628513 26414279 := bstep (se 1 (by rfl) ⟨19810709, by rfl⟩ : syracuseStep 26414279 = 39621419) B39621419
theorem B4124135 : Blo 1628513 4124135 := bstep (se 1 (by rfl) ⟨3093101, by rfl⟩ : syracuseStep 4124135 = 6186203) B6186203
theorem B8252927 : Blo 1628513 8252927 := bstep (se 1 (by rfl) ⟨6189695, by rfl⟩ : syracuseStep 8252927 = 12379391) B12379391
theorem B3665519 : Blo 1628513 3665519 := bstep (se 1 (by rfl) ⟨2749139, by rfl⟩ : syracuseStep 3665519 = 5498279) B5498279
theorem B4124479 : Blo 1628513 4124479 := bstep (se 1 (by rfl) ⟨3093359, by rfl⟩ : syracuseStep 4124479 = 6186719) B6186719
theorem B5500925 : Blo 1628513 5500925 := bstep (se 3 (by rfl) ⟨1031423, by rfl⟩ : syracuseStep 5500925 = 2062847) B2062847
theorem B6189119 : Blo 1628513 6189119 := bstep (se 1 (by rfl) ⟨4641839, by rfl⟩ : syracuseStep 6189119 = 9283679) B9283679
theorem B8253575 : Blo 1628513 8253575 := bstep (se 1 (by rfl) ⟨6190181, by rfl⟩ : syracuseStep 8253575 = 12380363) B12380363
theorem B2445479 : Blo 1628513 2445479 := bstep (se 1 (by rfl) ⟨1834109, by rfl⟩ : syracuseStep 2445479 = 3668219) B3668219
theorem B18813565 : Blo 1628513 18813565 := bstep (se 3 (by rfl) ⟨3527543, by rfl⟩ : syracuseStep 18813565 = 7055087) B7055087
theorem B3666599 : Blo 1628513 3666599 := bstep (se 1 (by rfl) ⟨2749949, by rfl⟩ : syracuseStep 3666599 = 5499899) B5499899
theorem B135541421 : Blo 1628513 135541421 := bstep (se 3 (by rfl) ⟨25414016, by rfl⟩ : syracuseStep 135541421 = 50828033) B50828033
theorem B3093223 : Blo 1628513 3093223 := bstep (se 1 (by rfl) ⟨2319917, by rfl⟩ : syracuseStep 3093223 = 4639835) B4639835
theorem B6607595 : Blo 1628513 6607595 := bstep (se 1 (by rfl) ⟨4955696, by rfl⟩ : syracuseStep 6607595 = 9911393) B9911393
theorem B44602123 : Blo 1628513 44602123 := bstep (se 1 (by rfl) ⟨33451592, by rfl⟩ : syracuseStep 44602123 = 66903185) B66903185
theorem B3666779 : Blo 1628513 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B21459937 : Blo 1628513 21459937 := bstep (se 2 (by rfl) ⟨8047476, by rfl⟩ : syracuseStep 21459937 = 16094953) B16094953
theorem B59438285 : Blo 1628513 59438285 := bstep (se 3 (by rfl) ⟨11144678, by rfl⟩ : syracuseStep 59438285 = 22289357) B22289357
theorem B6190303 : Blo 1628513 6190303 := bstep (se 1 (by rfl) ⟨4642727, by rfl⟩ : syracuseStep 6190303 = 9285455) B9285455
theorem B8246609 : Blo 1628513 8246609 := bstep (se 2 (by rfl) ⟨3092478, by rfl⟩ : syracuseStep 8246609 = 6184957) B6184957
theorem B2749855 : Blo 1628513 2749855 := bstep (se 1 (by rfl) ⟨2062391, by rfl⟩ : syracuseStep 2749855 = 4124783) B4124783
theorem B35255897 : Blo 1628513 35255897 := bstep (se 2 (by rfl) ⟨13220961, by rfl⟩ : syracuseStep 35255897 = 26441923) B26441923
theorem B1832575 : Blo 1628513 1832575 := bstep (se 1 (by rfl) ⟨1374431, by rfl⟩ : syracuseStep 1832575 = 2748863) B2748863
theorem B2610971 : Blo 1628513 2610971 := bstep (se 1 (by rfl) ⟨1958228, by rfl⟩ : syracuseStep 2610971 = 3916457) B3916457
theorem B3667751 : Blo 1628513 3667751 := bstep (se 1 (by rfl) ⟨2750813, by rfl⟩ : syracuseStep 3667751 = 5501627) B5501627
theorem B3667823 : Blo 1628513 3667823 := bstep (se 1 (by rfl) ⟨2750867, by rfl⟩ : syracuseStep 3667823 = 5501735) B5501735
theorem B2750375 : Blo 1628513 2750375 := bstep (se 1 (by rfl) ⟨2062781, by rfl⟩ : syracuseStep 2750375 = 4125563) B4125563
theorem B3668075 : Blo 1628513 3668075 := bstep (se 1 (by rfl) ⟨2751056, by rfl⟩ : syracuseStep 3668075 = 5502113) B5502113
theorem B9533627 : Blo 1628513 9533627 := bstep (se 1 (by rfl) ⟨7150220, by rfl⟩ : syracuseStep 9533627 = 14300441) B14300441
theorem B3094841 : Blo 1628513 3094841 := bstep (se 2 (by rfl) ⟨1160565, by rfl⟩ : syracuseStep 3094841 = 2321131) B2321131
theorem B3095023 : Blo 1628513 3095023 := bstep (se 1 (by rfl) ⟨2321267, by rfl⟩ : syracuseStep 3095023 = 4642535) B4642535
theorem B2062903 : Blo 1628513 2062903 := bstep (se 1 (by rfl) ⟨1547177, by rfl⟩ : syracuseStep 2062903 = 3094355) B3094355
theorem B10435169 : Blo 1628513 10435169 := bstep (se 2 (by rfl) ⟨3913188, by rfl⟩ : syracuseStep 10435169 = 7826377) B7826377
theorem B2751401 : Blo 1628513 2751401 := bstep (se 2 (by rfl) ⟨1031775, by rfl⟩ : syracuseStep 2751401 = 2063551) B2063551
theorem B8248391 : Blo 1628513 8248391 := bstep (se 1 (by rfl) ⟨6186293, by rfl⟩ : syracuseStep 8248391 = 12372587) B12372587
theorem B1629595 : Blo 1628513 1629595 := bstep (se 1 (by rfl) ⟨1222196, by rfl⟩ : syracuseStep 1629595 = 2444393) B2444393
theorem B7831511 : Blo 1628513 7831511 := bstep (se 1 (by rfl) ⟨5873633, by rfl⟩ : syracuseStep 7831511 = 11747267) B11747267
theorem B5873647 : Blo 1628513 5873647 := bstep (se 1 (by rfl) ⟨4405235, by rfl⟩ : syracuseStep 5873647 = 8810471) B8810471
theorem B1630319 : Blo 1628513 1630319 := bstep (se 1 (by rfl) ⟨1222739, by rfl⟩ : syracuseStep 1630319 = 2445479) B2445479
theorem B39625523 : Blo 1628513 39625523 := bstep (se 1 (by rfl) ⟨29719142, by rfl⟩ : syracuseStep 39625523 = 59438285) B59438285
theorem B5497739 : Blo 1628513 5497739 := bstep (se 1 (by rfl) ⟨4123304, by rfl⟩ : syracuseStep 5497739 = 8246609) B8246609
theorem B23503931 : Blo 1628513 23503931 := bstep (se 1 (by rfl) ⟨17627948, by rfl⟩ : syracuseStep 23503931 = 35255897) B35255897
theorem B4638035 : Blo 1628513 4638035 := bstep (se 1 (by rfl) ⟨3478526, by rfl⟩ : syracuseStep 4638035 = 6957053) B6957053
theorem B31327955 : Blo 1628513 31327955 := bstep (se 1 (by rfl) ⟨23495966, by rfl⟩ : syracuseStep 31327955 = 46991933) B46991933
theorem B6956779 : Blo 1628513 6956779 := bstep (se 1 (by rfl) ⟨5217584, by rfl⟩ : syracuseStep 6956779 = 10435169) B10435169
theorem B289720331 : Blo 1628513 289720331 := bstep (se 1 (by rfl) ⟨217290248, by rfl⟩ : syracuseStep 289720331 = 434580497) B434580497
theorem B5498927 : Blo 1628513 5498927 := bstep (se 1 (by rfl) ⟨4124195, by rfl⟩ : syracuseStep 5498927 = 8248391) B8248391
theorem B2443433 : Blo 1628513 2443433 := bstep (se 2 (by rfl) ⟨916287, by rfl⟩ : syracuseStep 2443433 = 1832575) B1832575
theorem B2443679 : Blo 1628513 2443679 := bstep (se 1 (by rfl) ⟨1832759, by rfl⟩ : syracuseStep 2443679 = 3665519) B3665519
theorem B5499305 : Blo 1628513 5499305 := bstep (se 2 (by rfl) ⟨2062239, by rfl⟩ : syracuseStep 5499305 = 4124479) B4124479
theorem B5221007 : Blo 1628513 5221007 := bstep (se 1 (by rfl) ⟨3915755, by rfl⟩ : syracuseStep 5221007 = 7831511) B7831511
theorem B18819809 : Blo 1628513 18819809 := bstep (se 2 (by rfl) ⟨7057428, by rfl⟩ : syracuseStep 18819809 = 14114857) B14114857
theorem B3664799 : Blo 1628513 3664799 := bstep (se 1 (by rfl) ⟨2748599, by rfl⟩ : syracuseStep 3664799 = 5497199) B5497199
theorem B5500007 : Blo 1628513 5500007 := bstep (se 1 (by rfl) ⟨4125005, by rfl⟩ : syracuseStep 5500007 = 8250011) B8250011
theorem B2444399 : Blo 1628513 2444399 := bstep (se 1 (by rfl) ⟨1833299, by rfl⟩ : syracuseStep 2444399 = 3666599) B3666599
theorem B90360947 : Blo 1628513 90360947 := bstep (se 1 (by rfl) ⟨67770710, by rfl⟩ : syracuseStep 90360947 = 135541421) B135541421
theorem B2444519 : Blo 1628513 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B100339013 : Blo 1628513 100339013 := bstep (se 4 (by rfl) ⟨9406782, by rfl⟩ : syracuseStep 100339013 = 18813565) B18813565
theorem B4124297 : Blo 1628513 4124297 := bstep (se 2 (by rfl) ⟨1546611, by rfl⟩ : syracuseStep 4124297 = 3093223) B3093223
theorem B59469497 : Blo 1628513 59469497 := bstep (se 2 (by rfl) ⟨22301061, by rfl⟩ : syracuseStep 59469497 = 44602123) B44602123
theorem B5500763 : Blo 1628513 5500763 := bstep (se 1 (by rfl) ⟨4125572, by rfl⟩ : syracuseStep 5500763 = 8251145) B8251145
theorem B1740647 : Blo 1628513 1740647 := bstep (se 1 (by rfl) ⟨1305485, by rfl⟩ : syracuseStep 1740647 = 2610971) B2610971
theorem B2445167 : Blo 1628513 2445167 := bstep (se 1 (by rfl) ⟨1833875, by rfl⟩ : syracuseStep 2445167 = 3667751) B3667751
theorem B2445215 : Blo 1628513 2445215 := bstep (se 1 (by rfl) ⟨1833911, by rfl⟩ : syracuseStep 2445215 = 3667823) B3667823
theorem B2445383 : Blo 1628513 2445383 := bstep (se 1 (by rfl) ⟨1834037, by rfl⟩ : syracuseStep 2445383 = 3668075) B3668075
theorem B9285911 : Blo 1628513 9285911 := bstep (se 1 (by rfl) ⟨6964433, by rfl⟩ : syracuseStep 9285911 = 13928867) B13928867
theorem B8253737 : Blo 1628513 8253737 := bstep (se 2 (by rfl) ⟨3095151, by rfl⟩ : syracuseStep 8253737 = 6190303) B6190303
theorem B3666473 : Blo 1628513 3666473 := bstep (se 2 (by rfl) ⟨1374927, by rfl⟩ : syracuseStep 3666473 = 2749855) B2749855
theorem B17609519 : Blo 1628513 17609519 := bstep (se 1 (by rfl) ⟨13207139, by rfl⟩ : syracuseStep 17609519 = 26414279) B26414279
theorem B2749423 : Blo 1628513 2749423 := bstep (se 1 (by rfl) ⟨2062067, by rfl⟩ : syracuseStep 2749423 = 4124135) B4124135
theorem B5501951 : Blo 1628513 5501951 := bstep (se 1 (by rfl) ⟨4126463, by rfl⟩ : syracuseStep 5501951 = 8252927) B8252927
theorem B142816465 : Blo 1628513 142816465 := bstep (se 2 (by rfl) ⟨53556174, by rfl⟩ : syracuseStep 142816465 = 107112349) B107112349
theorem B3667283 : Blo 1628513 3667283 := bstep (se 1 (by rfl) ⟨2750462, by rfl⟩ : syracuseStep 3667283 = 5500925) B5500925
theorem B4126079 : Blo 1628513 4126079 := bstep (se 1 (by rfl) ⟨3094559, by rfl⟩ : syracuseStep 4126079 = 6189119) B6189119
theorem B10442141 : Blo 1628513 10442141 := bstep (se 3 (by rfl) ⟨1957901, by rfl⟩ : syracuseStep 10442141 = 3915803) B3915803
theorem B5502383 : Blo 1628513 5502383 := bstep (se 1 (by rfl) ⟨4126787, by rfl⟩ : syracuseStep 5502383 = 8253575) B8253575
theorem B4405063 : Blo 1628513 4405063 := bstep (se 1 (by rfl) ⟨3303797, by rfl⟩ : syracuseStep 4405063 = 6607595) B6607595
theorem B4126697 : Blo 1628513 4126697 := bstep (se 2 (by rfl) ⟨1547511, by rfl⟩ : syracuseStep 4126697 = 3095023) B3095023
theorem B2750537 : Blo 1628513 2750537 := bstep (se 2 (by rfl) ⟨1031451, by rfl⟩ : syracuseStep 2750537 = 2062903) B2062903
theorem B1628519 : Blo 1628513 1628519 := bstep (se 1 (by rfl) ⟨1221389, by rfl⟩ : syracuseStep 1628519 = 2442779) B2442779
theorem B1628639 : Blo 1628513 1628639 := bstep (se 1 (by rfl) ⟨1221479, by rfl⟩ : syracuseStep 1628639 = 2442959) B2442959
theorem B3480167 : Blo 1628513 3480167 := bstep (se 1 (by rfl) ⟨2610125, by rfl⟩ : syracuseStep 3480167 = 5220251) B5220251
theorem B1833583 : Blo 1628513 1833583 := bstep (se 1 (by rfl) ⟨1375187, by rfl⟩ : syracuseStep 1833583 = 2750375) B2750375
theorem B28613249 : Blo 1628513 28613249 := bstep (se 2 (by rfl) ⟨10729968, by rfl⟩ : syracuseStep 28613249 = 21459937) B21459937
theorem B6355751 : Blo 1628513 6355751 := bstep (se 1 (by rfl) ⟨4766813, by rfl⟩ : syracuseStep 6355751 = 9533627) B9533627
theorem B2063227 : Blo 1628513 2063227 := bstep (se 1 (by rfl) ⟨1547420, by rfl⟩ : syracuseStep 2063227 = 3094841) B3094841
theorem B1834267 : Blo 1628513 1834267 := bstep (se 1 (by rfl) ⟨1375700, by rfl⟩ : syracuseStep 1834267 = 2751401) B2751401
theorem B7831529 : Blo 1628513 7831529 := bstep (se 2 (by rfl) ⟨2936823, by rfl⟩ : syracuseStep 7831529 = 5873647) B5873647
theorem B1630255 : Blo 1628513 1630255 := bstep (se 1 (by rfl) ⟨1222691, by rfl⟩ : syracuseStep 1630255 = 2445383) B2445383
theorem B2320111 : Blo 1628513 2320111 := bstep (se 1 (by rfl) ⟨1740083, by rfl⟩ : syracuseStep 2320111 = 3480167) B3480167
theorem B2443199 : Blo 1628513 2443199 := bstep (se 1 (by rfl) ⟨1832399, by rfl⟩ : syracuseStep 2443199 = 3664799) B3664799
theorem B46958717 : Blo 1628513 46958717 := bstep (se 3 (by rfl) ⟨8804759, by rfl⟩ : syracuseStep 46958717 = 17609519) B17609519
theorem B9275705 : Blo 1628513 9275705 := bstep (se 2 (by rfl) ⟨3478389, by rfl⟩ : syracuseStep 9275705 = 6956779) B6956779
theorem B5221019 : Blo 1628513 5221019 := bstep (se 1 (by rfl) ⟨3915764, by rfl⟩ : syracuseStep 5221019 = 7831529) B7831529
theorem B2444315 : Blo 1628513 2444315 := bstep (se 1 (by rfl) ⟨1833236, by rfl⟩ : syracuseStep 2444315 = 3666473) B3666473
theorem B3665159 : Blo 1628513 3665159 := bstep (se 1 (by rfl) ⟨2748869, by rfl⟩ : syracuseStep 3665159 = 5497739) B5497739
theorem B2444777 : Blo 1628513 2444777 := bstep (se 2 (by rfl) ⟨916791, by rfl⟩ : syracuseStep 2444777 = 1833583) B1833583
theorem B267570701 : Blo 1628513 267570701 := bstep (se 3 (by rfl) ⟨50169506, by rfl⟩ : syracuseStep 267570701 = 100339013) B100339013
theorem B3092023 : Blo 1628513 3092023 := bstep (se 1 (by rfl) ⟨2319017, by rfl⟩ : syracuseStep 3092023 = 4638035) B4638035
theorem B2444855 : Blo 1628513 2444855 := bstep (se 1 (by rfl) ⟨1833641, by rfl⟩ : syracuseStep 2444855 = 3667283) B3667283
theorem B761687813 : Blo 1628513 761687813 := bstep (se 4 (by rfl) ⟨71408232, by rfl⟩ : syracuseStep 761687813 = 142816465) B142816465
theorem B20885303 : Blo 1628513 20885303 := bstep (se 1 (by rfl) ⟨15663977, by rfl⟩ : syracuseStep 20885303 = 31327955) B31327955
theorem B3665897 : Blo 1628513 3665897 := bstep (se 2 (by rfl) ⟨1374711, by rfl⟩ : syracuseStep 3665897 = 2749423) B2749423
theorem B193146887 : Blo 1628513 193146887 := bstep (se 1 (by rfl) ⟨144860165, by rfl⟩ : syracuseStep 193146887 = 289720331) B289720331
theorem B3665951 : Blo 1628513 3665951 := bstep (se 1 (by rfl) ⟨2749463, by rfl⟩ : syracuseStep 3665951 = 5498927) B5498927
theorem B3666203 : Blo 1628513 3666203 := bstep (se 1 (by rfl) ⟨2749652, by rfl⟩ : syracuseStep 3666203 = 5499305) B5499305
theorem B2445689 : Blo 1628513 2445689 := bstep (se 2 (by rfl) ⟨917133, by rfl⟩ : syracuseStep 2445689 = 1834267) B1834267
theorem B19075499 : Blo 1628513 19075499 := bstep (se 1 (by rfl) ⟨14306624, by rfl⟩ : syracuseStep 19075499 = 28613249) B28613249
theorem B12546539 : Blo 1628513 12546539 := bstep (se 1 (by rfl) ⟨9409904, by rfl⟩ : syracuseStep 12546539 = 18819809) B18819809
theorem B3666671 : Blo 1628513 3666671 := bstep (se 1 (by rfl) ⟨2750003, by rfl⟩ : syracuseStep 3666671 = 5500007) B5500007
theorem B60240631 : Blo 1628513 60240631 := bstep (se 1 (by rfl) ⟨45180473, by rfl⟩ : syracuseStep 60240631 = 90360947) B90360947
theorem B4641725 : Blo 1628513 4641725 := bstep (se 3 (by rfl) ⟨870323, by rfl⟩ : syracuseStep 4641725 = 1740647) B1740647
theorem B2749531 : Blo 1628513 2749531 := bstep (se 1 (by rfl) ⟨2062148, by rfl⟩ : syracuseStep 2749531 = 4124297) B4124297
theorem B39646331 : Blo 1628513 39646331 := bstep (se 1 (by rfl) ⟨29734748, by rfl⟩ : syracuseStep 39646331 = 59469497) B59469497
theorem B3667175 : Blo 1628513 3667175 := bstep (se 1 (by rfl) ⟨2750381, by rfl⟩ : syracuseStep 3667175 = 5500763) B5500763
theorem B6190607 : Blo 1628513 6190607 := bstep (se 1 (by rfl) ⟨4642955, by rfl⟩ : syracuseStep 6190607 = 9285911) B9285911
theorem B5502491 : Blo 1628513 5502491 := bstep (se 1 (by rfl) ⟨4126868, by rfl⟩ : syracuseStep 5502491 = 8253737) B8253737
theorem B67794677 : Blo 1628513 67794677 := bstep (se 5 (by rfl) ⟨3177875, by rfl⟩ : syracuseStep 67794677 = 6355751) B6355751
theorem B26417015 : Blo 1628513 26417015 := bstep (se 1 (by rfl) ⟨19812761, by rfl⟩ : syracuseStep 26417015 = 39625523) B39625523
theorem B3667967 : Blo 1628513 3667967 := bstep (se 1 (by rfl) ⟨2750975, by rfl⟩ : syracuseStep 3667967 = 5501951) B5501951
theorem B15669287 : Blo 1628513 15669287 := bstep (se 1 (by rfl) ⟨11751965, by rfl⟩ : syracuseStep 15669287 = 23503931) B23503931
theorem B2750719 : Blo 1628513 2750719 := bstep (se 1 (by rfl) ⟨2063039, by rfl⟩ : syracuseStep 2750719 = 4126079) B4126079
theorem B6961427 : Blo 1628513 6961427 := bstep (se 1 (by rfl) ⟨5221070, by rfl⟩ : syracuseStep 6961427 = 10442141) B10442141
theorem B3668255 : Blo 1628513 3668255 := bstep (se 1 (by rfl) ⟨2751191, by rfl⟩ : syracuseStep 3668255 = 5502383) B5502383
theorem B2750969 : Blo 1628513 2750969 := bstep (se 2 (by rfl) ⟨1031613, by rfl⟩ : syracuseStep 2750969 = 2063227) B2063227
theorem B2751131 : Blo 1628513 2751131 := bstep (se 1 (by rfl) ⟨2063348, by rfl⟩ : syracuseStep 2751131 = 4126697) B4126697
theorem B1833691 : Blo 1628513 1833691 := bstep (se 1 (by rfl) ⟨1375268, by rfl⟩ : syracuseStep 1833691 = 2750537) B2750537
theorem B1628955 : Blo 1628513 1628955 := bstep (se 1 (by rfl) ⟨1221716, by rfl⟩ : syracuseStep 1628955 = 2443433) B2443433
theorem B1629119 : Blo 1628513 1629119 := bstep (se 1 (by rfl) ⟨1221839, by rfl⟩ : syracuseStep 1629119 = 2443679) B2443679
theorem B3480671 : Blo 1628513 3480671 := bstep (se 1 (by rfl) ⟨2610503, by rfl⟩ : syracuseStep 3480671 = 5221007) B5221007
theorem B1629599 : Blo 1628513 1629599 := bstep (se 1 (by rfl) ⟨1222199, by rfl⟩ : syracuseStep 1629599 = 2444399) B2444399
theorem B1629679 : Blo 1628513 1629679 := bstep (se 1 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 1629679 = 2444519) B2444519
theorem B5873417 : Blo 1628513 5873417 := bstep (se 2 (by rfl) ⟨2202531, by rfl⟩ : syracuseStep 5873417 = 4405063) B4405063
theorem B1630111 : Blo 1628513 1630111 := bstep (se 1 (by rfl) ⟨1222583, by rfl⟩ : syracuseStep 1630111 = 2445167) B2445167
theorem B1630143 : Blo 1628513 1630143 := bstep (se 1 (by rfl) ⟨1222607, by rfl⟩ : syracuseStep 1630143 = 2445215) B2445215
theorem B1630459 : Blo 1628513 1630459 := bstep (se 1 (by rfl) ⟨1222844, by rfl⟩ : syracuseStep 1630459 = 2445689) B2445689
theorem B9281789 : Blo 1628513 9281789 := bstep (se 3 (by rfl) ⟨1740335, by rfl⟩ : syracuseStep 9281789 = 3480671) B3480671
theorem B8364359 : Blo 1628513 8364359 := bstep (se 1 (by rfl) ⟨6273269, by rfl⟩ : syracuseStep 8364359 = 12546539) B12546539
theorem B45196451 : Blo 1628513 45196451 := bstep (se 1 (by rfl) ⟨33897338, by rfl⟩ : syracuseStep 45196451 = 67794677) B67794677
theorem B10446191 : Blo 1628513 10446191 := bstep (se 1 (by rfl) ⟨7834643, by rfl⟩ : syracuseStep 10446191 = 15669287) B15669287
theorem B4122697 : Blo 1628513 4122697 := bstep (se 2 (by rfl) ⟨1546011, by rfl⟩ : syracuseStep 4122697 = 3092023) B3092023
theorem B2443439 : Blo 1628513 2443439 := bstep (se 1 (by rfl) ⟨1832579, by rfl⟩ : syracuseStep 2443439 = 3665159) B3665159
theorem B507791875 : Blo 1628513 507791875 := bstep (se 1 (by rfl) ⟨380843906, by rfl⟩ : syracuseStep 507791875 = 761687813) B761687813
theorem B2443931 : Blo 1628513 2443931 := bstep (se 1 (by rfl) ⟨1832948, by rfl⟩ : syracuseStep 2443931 = 3665897) B3665897
theorem B515058365 : Blo 1628513 515058365 := bstep (se 3 (by rfl) ⟨96573443, by rfl⟩ : syracuseStep 515058365 = 193146887) B193146887
theorem B2443967 : Blo 1628513 2443967 := bstep (se 1 (by rfl) ⟨1832975, by rfl⟩ : syracuseStep 2443967 = 3665951) B3665951
theorem B2444135 : Blo 1628513 2444135 := bstep (se 1 (by rfl) ⟨1833101, by rfl⟩ : syracuseStep 2444135 = 3666203) B3666203
theorem B12716999 : Blo 1628513 12716999 := bstep (se 1 (by rfl) ⟨9537749, by rfl⟩ : syracuseStep 12716999 = 19075499) B19075499
theorem B2444447 : Blo 1628513 2444447 := bstep (se 1 (by rfl) ⟨1833335, by rfl⟩ : syracuseStep 2444447 = 3666671) B3666671
theorem B26430887 : Blo 1628513 26430887 := bstep (se 1 (by rfl) ⟨19823165, by rfl⟩ : syracuseStep 26430887 = 39646331) B39646331
theorem B2444783 : Blo 1628513 2444783 := bstep (se 1 (by rfl) ⟨1833587, by rfl⟩ : syracuseStep 2444783 = 3667175) B3667175
theorem B2444921 : Blo 1628513 2444921 := bstep (se 2 (by rfl) ⟨916845, by rfl⟩ : syracuseStep 2444921 = 1833691) B1833691
theorem B2445311 : Blo 1628513 2445311 := bstep (se 1 (by rfl) ⟨1833983, by rfl⟩ : syracuseStep 2445311 = 3667967) B3667967
theorem B31305811 : Blo 1628513 31305811 := bstep (se 1 (by rfl) ⟨23479358, by rfl⟩ : syracuseStep 31305811 = 46958717) B46958717
theorem B3666041 : Blo 1628513 3666041 := bstep (se 2 (by rfl) ⟨1374765, by rfl⟩ : syracuseStep 3666041 = 2749531) B2749531
theorem B4640951 : Blo 1628513 4640951 := bstep (se 1 (by rfl) ⟨3480713, by rfl⟩ : syracuseStep 4640951 = 6961427) B6961427
theorem B2445503 : Blo 1628513 2445503 := bstep (se 1 (by rfl) ⟨1834127, by rfl⟩ : syracuseStep 2445503 = 3668255) B3668255
theorem B3093481 : Blo 1628513 3093481 := bstep (se 2 (by rfl) ⟨1160055, by rfl⟩ : syracuseStep 3093481 = 2320111) B2320111
theorem B13923535 : Blo 1628513 13923535 := bstep (se 1 (by rfl) ⟨10442651, by rfl⟩ : syracuseStep 13923535 = 20885303) B20885303
theorem B3667625 : Blo 1628513 3667625 := bstep (se 2 (by rfl) ⟨1375359, by rfl⟩ : syracuseStep 3667625 = 2750719) B2750719
theorem B80320841 : Blo 1628513 80320841 := bstep (se 2 (by rfl) ⟨30120315, by rfl⟩ : syracuseStep 80320841 = 60240631) B60240631
theorem B4127071 : Blo 1628513 4127071 := bstep (se 1 (by rfl) ⟨3095303, by rfl⟩ : syracuseStep 4127071 = 6190607) B6190607
theorem B3668327 : Blo 1628513 3668327 := bstep (se 1 (by rfl) ⟨2751245, by rfl⟩ : syracuseStep 3668327 = 5502491) B5502491
theorem B17611343 : Blo 1628513 17611343 := bstep (se 1 (by rfl) ⟨13208507, by rfl⟩ : syracuseStep 17611343 = 26417015) B26417015
theorem B1628799 : Blo 1628513 1628799 := bstep (se 1 (by rfl) ⟨1221599, by rfl⟩ : syracuseStep 1628799 = 2443199) B2443199
theorem B6183803 : Blo 1628513 6183803 := bstep (se 1 (by rfl) ⟨4637852, by rfl⟩ : syracuseStep 6183803 = 9275705) B9275705
theorem B1833979 : Blo 1628513 1833979 := bstep (se 1 (by rfl) ⟨1375484, by rfl⟩ : syracuseStep 1833979 = 2750969) B2750969
theorem B3480679 : Blo 1628513 3480679 := bstep (se 1 (by rfl) ⟨2610509, by rfl⟩ : syracuseStep 3480679 = 5221019) B5221019
theorem B1834087 : Blo 1628513 1834087 := bstep (se 1 (by rfl) ⟨1375565, by rfl⟩ : syracuseStep 1834087 = 2751131) B2751131
theorem B1629543 : Blo 1628513 1629543 := bstep (se 1 (by rfl) ⟨1222157, by rfl⟩ : syracuseStep 1629543 = 2444315) B2444315
theorem B1629851 : Blo 1628513 1629851 := bstep (se 1 (by rfl) ⟨1222388, by rfl⟩ : syracuseStep 1629851 = 2444777) B2444777
theorem B178380467 : Blo 1628513 178380467 := bstep (se 1 (by rfl) ⟨133785350, by rfl⟩ : syracuseStep 178380467 = 267570701) B267570701
theorem B1629903 : Blo 1628513 1629903 := bstep (se 1 (by rfl) ⟨1222427, by rfl⟩ : syracuseStep 1629903 = 2444855) B2444855
theorem B12377933 : Blo 1628513 12377933 := bstep (se 3 (by rfl) ⟨2320862, by rfl⟩ : syracuseStep 12377933 = 4641725) B4641725
theorem B3915611 : Blo 1628513 3915611 := bstep (se 1 (by rfl) ⟨2936708, by rfl⟩ : syracuseStep 3915611 = 5873417) B5873417
theorem B5496929 : Blo 1628513 5496929 := bstep (se 2 (by rfl) ⟨2061348, by rfl⟩ : syracuseStep 5496929 = 4122697) B4122697
theorem B1630335 : Blo 1628513 1630335 := bstep (se 1 (by rfl) ⟨1222751, by rfl⟩ : syracuseStep 1630335 = 2445503) B2445503
theorem B30130967 : Blo 1628513 30130967 := bstep (se 1 (by rfl) ⟨22598225, by rfl⟩ : syracuseStep 30130967 = 45196451) B45196451
theorem B6964127 : Blo 1628513 6964127 := bstep (se 1 (by rfl) ⟨5223095, by rfl⟩ : syracuseStep 6964127 = 10446191) B10446191
theorem B18564713 : Blo 1628513 18564713 := bstep (se 2 (by rfl) ⟨6961767, by rfl⟩ : syracuseStep 18564713 = 13923535) B13923535
theorem B11740895 : Blo 1628513 11740895 := bstep (se 1 (by rfl) ⟨8805671, by rfl⟩ : syracuseStep 11740895 = 17611343) B17611343
theorem B1630207 : Blo 1628513 1630207 := bstep (se 1 (by rfl) ⟨1222655, by rfl⟩ : syracuseStep 1630207 = 2445311) B2445311
theorem B4122535 : Blo 1628513 4122535 := bstep (se 1 (by rfl) ⟨3091901, by rfl⟩ : syracuseStep 4122535 = 6183803) B6183803
theorem B8251955 : Blo 1628513 8251955 := bstep (se 1 (by rfl) ⟨6188966, by rfl⟩ : syracuseStep 8251955 = 12377933) B12377933
theorem B2444027 : Blo 1628513 2444027 := bstep (se 1 (by rfl) ⟨1833020, by rfl⟩ : syracuseStep 2444027 = 3666041) B3666041
theorem B41741081 : Blo 1628513 41741081 := bstep (se 2 (by rfl) ⟨15652905, by rfl⟩ : syracuseStep 41741081 = 31305811) B31305811
theorem B6187859 : Blo 1628513 6187859 := bstep (se 1 (by rfl) ⟨4640894, by rfl⟩ : syracuseStep 6187859 = 9281789) B9281789
theorem B677055833 : Blo 1628513 677055833 := bstep (se 2 (by rfl) ⟨253895937, by rfl⟩ : syracuseStep 677055833 = 507791875) B507791875
theorem B2445083 : Blo 1628513 2445083 := bstep (se 1 (by rfl) ⟨1833812, by rfl⟩ : syracuseStep 2445083 = 3667625) B3667625
theorem B4124641 : Blo 1628513 4124641 := bstep (se 2 (by rfl) ⟨1546740, by rfl⟩ : syracuseStep 4124641 = 3093481) B3093481
theorem B2445305 : Blo 1628513 2445305 := bstep (se 2 (by rfl) ⟨916989, by rfl⟩ : syracuseStep 2445305 = 1833979) B1833979
theorem B4640905 : Blo 1628513 4640905 := bstep (se 2 (by rfl) ⟨1740339, by rfl⟩ : syracuseStep 4640905 = 3480679) B3480679
theorem B2445449 : Blo 1628513 2445449 := bstep (se 2 (by rfl) ⟨917043, by rfl⟩ : syracuseStep 2445449 = 1834087) B1834087
theorem B53547227 : Blo 1628513 53547227 := bstep (se 1 (by rfl) ⟨40160420, by rfl⟩ : syracuseStep 53547227 = 80320841) B80320841
theorem B2445551 : Blo 1628513 2445551 := bstep (se 1 (by rfl) ⟨1834163, by rfl⟩ : syracuseStep 2445551 = 3668327) B3668327
theorem B343372243 : Blo 1628513 343372243 := bstep (se 1 (by rfl) ⟨257529182, by rfl⟩ : syracuseStep 343372243 = 515058365) B515058365
theorem B118920311 : Blo 1628513 118920311 := bstep (se 1 (by rfl) ⟨89190233, by rfl⟩ : syracuseStep 118920311 = 178380467) B178380467
theorem B2610407 : Blo 1628513 2610407 := bstep (se 1 (by rfl) ⟨1957805, by rfl⟩ : syracuseStep 2610407 = 3915611) B3915611
theorem B3093967 : Blo 1628513 3093967 := bstep (se 1 (by rfl) ⟨2320475, by rfl⟩ : syracuseStep 3093967 = 4640951) B4640951
theorem B5576239 : Blo 1628513 5576239 := bstep (se 1 (by rfl) ⟨4182179, by rfl⟩ : syracuseStep 5576239 = 8364359) B8364359
theorem B5502761 : Blo 1628513 5502761 := bstep (se 2 (by rfl) ⟨2063535, by rfl⟩ : syracuseStep 5502761 = 4127071) B4127071
theorem B1628959 : Blo 1628513 1628959 := bstep (se 1 (by rfl) ⟨1221719, by rfl⟩ : syracuseStep 1628959 = 2443439) B2443439
theorem B1629287 : Blo 1628513 1629287 := bstep (se 1 (by rfl) ⟨1221965, by rfl⟩ : syracuseStep 1629287 = 2443931) B2443931
theorem B1629311 : Blo 1628513 1629311 := bstep (se 1 (by rfl) ⟨1221983, by rfl⟩ : syracuseStep 1629311 = 2443967) B2443967
theorem B1629423 : Blo 1628513 1629423 := bstep (se 1 (by rfl) ⟨1222067, by rfl⟩ : syracuseStep 1629423 = 2444135) B2444135
theorem B8477999 : Blo 1628513 8477999 := bstep (se 1 (by rfl) ⟨6358499, by rfl⟩ : syracuseStep 8477999 = 12716999) B12716999
theorem B1629631 : Blo 1628513 1629631 := bstep (se 1 (by rfl) ⟨1222223, by rfl⟩ : syracuseStep 1629631 = 2444447) B2444447
theorem B17620591 : Blo 1628513 17620591 := bstep (se 1 (by rfl) ⟨13215443, by rfl⟩ : syracuseStep 17620591 = 26430887) B26430887
theorem B1629855 : Blo 1628513 1629855 := bstep (se 1 (by rfl) ⟨1222391, by rfl⟩ : syracuseStep 1629855 = 2444783) B2444783
theorem B1629947 : Blo 1628513 1629947 := bstep (se 1 (by rfl) ⟨1222460, by rfl⟩ : syracuseStep 1629947 = 2444921) B2444921
theorem B1630299 : Blo 1628513 1630299 := bstep (se 1 (by rfl) ⟨1222724, by rfl⟩ : syracuseStep 1630299 = 2445449) B2445449
theorem B1630367 : Blo 1628513 1630367 := bstep (se 1 (by rfl) ⟨1222775, by rfl⟩ : syracuseStep 1630367 = 2445551) B2445551
theorem B20087311 : Blo 1628513 20087311 := bstep (se 1 (by rfl) ⟨15065483, by rfl⟩ : syracuseStep 20087311 = 30130967) B30130967
theorem B5499521 : Blo 1628513 5499521 := bstep (se 2 (by rfl) ⟨2062320, by rfl⟩ : syracuseStep 5499521 = 4124641) B4124641
theorem B3664619 : Blo 1628513 3664619 := bstep (se 1 (by rfl) ⟨2748464, by rfl⟩ : syracuseStep 3664619 = 5496929) B5496929
theorem B6187873 : Blo 1628513 6187873 := bstep (se 2 (by rfl) ⟨2320452, by rfl⟩ : syracuseStep 6187873 = 4640905) B4640905
theorem B457829657 : Blo 1628513 457829657 := bstep (se 2 (by rfl) ⟨171686121, by rfl⟩ : syracuseStep 457829657 = 343372243) B343372243
theorem B7827263 : Blo 1628513 7827263 := bstep (se 1 (by rfl) ⟨5870447, by rfl⟩ : syracuseStep 7827263 = 11740895) B11740895
theorem B5501303 : Blo 1628513 5501303 := bstep (se 1 (by rfl) ⟨4125977, by rfl⟩ : syracuseStep 5501303 = 8251955) B8251955
theorem B4125239 : Blo 1628513 4125239 := bstep (se 1 (by rfl) ⟨3093929, by rfl⟩ : syracuseStep 4125239 = 6187859) B6187859
theorem B4125289 : Blo 1628513 4125289 := bstep (se 2 (by rfl) ⟨1546983, by rfl⟩ : syracuseStep 4125289 = 3093967) B3093967
theorem B7434985 : Blo 1628513 7434985 := bstep (se 2 (by rfl) ⟨2788119, by rfl⟩ : syracuseStep 7434985 = 5576239) B5576239
theorem B35698151 : Blo 1628513 35698151 := bstep (se 1 (by rfl) ⟨26773613, by rfl⟩ : syracuseStep 35698151 = 53547227) B53547227
theorem B6961085 : Blo 1628513 6961085 := bstep (se 3 (by rfl) ⟨1305203, by rfl⟩ : syracuseStep 6961085 = 2610407) B2610407
theorem B4642751 : Blo 1628513 4642751 := bstep (se 1 (by rfl) ⟨3482063, by rfl⟩ : syracuseStep 4642751 = 6964127) B6964127
theorem B79280207 : Blo 1628513 79280207 := bstep (se 1 (by rfl) ⟨59460155, by rfl⟩ : syracuseStep 79280207 = 118920311) B118920311
theorem B12376475 : Blo 1628513 12376475 := bstep (se 1 (by rfl) ⟨9282356, by rfl⟩ : syracuseStep 12376475 = 18564713) B18564713
theorem B3668507 : Blo 1628513 3668507 := bstep (se 1 (by rfl) ⟨2751380, by rfl⟩ : syracuseStep 3668507 = 5502761) B5502761
theorem B1629351 : Blo 1628513 1629351 := bstep (se 1 (by rfl) ⟨1222013, by rfl⟩ : syracuseStep 1629351 = 2444027) B2444027
theorem B27827387 : Blo 1628513 27827387 := bstep (se 1 (by rfl) ⟨20870540, by rfl⟩ : syracuseStep 27827387 = 41741081) B41741081
theorem B23494121 : Blo 1628513 23494121 := bstep (se 2 (by rfl) ⟨8810295, by rfl⟩ : syracuseStep 23494121 = 17620591) B17620591
theorem B5651999 : Blo 1628513 5651999 := bstep (se 1 (by rfl) ⟨4238999, by rfl⟩ : syracuseStep 5651999 = 8477999) B8477999
theorem B451370555 : Blo 1628513 451370555 := bstep (se 1 (by rfl) ⟨338527916, by rfl⟩ : syracuseStep 451370555 = 677055833) B677055833
theorem B1630055 : Blo 1628513 1630055 := bstep (se 1 (by rfl) ⟨1222541, by rfl⟩ : syracuseStep 1630055 = 2445083) B2445083
theorem B5496713 : Blo 1628513 5496713 := bstep (se 2 (by rfl) ⟨2061267, by rfl⟩ : syracuseStep 5496713 = 4122535) B4122535
theorem B1630203 : Blo 1628513 1630203 := bstep (se 1 (by rfl) ⟨1222652, by rfl⟩ : syracuseStep 1630203 = 2445305) B2445305
theorem B9913313 : Blo 1628513 9913313 := bstep (se 2 (by rfl) ⟨3717492, by rfl⟩ : syracuseStep 9913313 = 7434985) B7434985
theorem B23798767 : Blo 1628513 23798767 := bstep (se 1 (by rfl) ⟨17849075, by rfl⟩ : syracuseStep 23798767 = 35698151) B35698151
theorem B8250497 : Blo 1628513 8250497 := bstep (se 2 (by rfl) ⟨3093936, by rfl⟩ : syracuseStep 8250497 = 6187873) B6187873
theorem B8250983 : Blo 1628513 8250983 := bstep (se 1 (by rfl) ⟨6188237, by rfl⟩ : syracuseStep 8250983 = 12376475) B12376475
theorem B2443079 : Blo 1628513 2443079 := bstep (se 1 (by rfl) ⟨1832309, by rfl⟩ : syracuseStep 2443079 = 3664619) B3664619
theorem B305219771 : Blo 1628513 305219771 := bstep (se 1 (by rfl) ⟨228914828, by rfl⟩ : syracuseStep 305219771 = 457829657) B457829657
theorem B3664475 : Blo 1628513 3664475 := bstep (se 1 (by rfl) ⟨2748356, by rfl⟩ : syracuseStep 3664475 = 5496713) B5496713
theorem B26783081 : Blo 1628513 26783081 := bstep (se 2 (by rfl) ⟨10043655, by rfl⟩ : syracuseStep 26783081 = 20087311) B20087311
theorem B5500385 : Blo 1628513 5500385 := bstep (se 2 (by rfl) ⟨2062644, by rfl⟩ : syracuseStep 5500385 = 4125289) B4125289
theorem B4640723 : Blo 1628513 4640723 := bstep (se 1 (by rfl) ⟨3480542, by rfl⟩ : syracuseStep 4640723 = 6961085) B6961085
theorem B2445671 : Blo 1628513 2445671 := bstep (se 1 (by rfl) ⟨1834253, by rfl⟩ : syracuseStep 2445671 = 3668507) B3668507
theorem B3666347 : Blo 1628513 3666347 := bstep (se 1 (by rfl) ⟨2749760, by rfl⟩ : syracuseStep 3666347 = 5499521) B5499521
theorem B18551591 : Blo 1628513 18551591 := bstep (se 1 (by rfl) ⟨13913693, by rfl⟩ : syracuseStep 18551591 = 27827387) B27827387
theorem B300913703 : Blo 1628513 300913703 := bstep (se 1 (by rfl) ⟨225685277, by rfl⟩ : syracuseStep 300913703 = 451370555) B451370555
theorem B3667535 : Blo 1628513 3667535 := bstep (se 1 (by rfl) ⟨2750651, by rfl⟩ : syracuseStep 3667535 = 5501303) B5501303
theorem B2750159 : Blo 1628513 2750159 := bstep (se 1 (by rfl) ⟨2062619, by rfl⟩ : syracuseStep 2750159 = 4125239) B4125239
theorem B3095167 : Blo 1628513 3095167 := bstep (se 1 (by rfl) ⟨2321375, by rfl⟩ : syracuseStep 3095167 = 4642751) B4642751
theorem B52853471 : Blo 1628513 52853471 := bstep (se 1 (by rfl) ⟨39640103, by rfl⟩ : syracuseStep 52853471 = 79280207) B79280207
theorem B15662747 : Blo 1628513 15662747 := bstep (se 1 (by rfl) ⟨11747060, by rfl⟩ : syracuseStep 15662747 = 23494121) B23494121
theorem B3767999 : Blo 1628513 3767999 := bstep (se 1 (by rfl) ⟨2825999, by rfl⟩ : syracuseStep 3767999 = 5651999) B5651999
theorem B5218175 : Blo 1628513 5218175 := bstep (se 1 (by rfl) ⟨3913631, by rfl⟩ : syracuseStep 5218175 = 7827263) B7827263
theorem B1630447 : Blo 1628513 1630447 := bstep (se 1 (by rfl) ⟨1222835, by rfl⟩ : syracuseStep 1630447 = 2445671) B2445671
theorem B2442983 : Blo 1628513 2442983 := bstep (se 1 (by rfl) ⟨1832237, by rfl⟩ : syracuseStep 2442983 = 3664475) B3664475
theorem B35235647 : Blo 1628513 35235647 := bstep (se 1 (by rfl) ⟨26426735, by rfl⟩ : syracuseStep 35235647 = 52853471) B52853471
theorem B2444231 : Blo 1628513 2444231 := bstep (se 1 (by rfl) ⟨1833173, by rfl⟩ : syracuseStep 2444231 = 3666347) B3666347
theorem B200609135 : Blo 1628513 200609135 := bstep (se 1 (by rfl) ⟨150456851, by rfl⟩ : syracuseStep 200609135 = 300913703) B300913703
theorem B5500331 : Blo 1628513 5500331 := bstep (se 1 (by rfl) ⟨4125248, by rfl⟩ : syracuseStep 5500331 = 8250497) B8250497
theorem B2445023 : Blo 1628513 2445023 := bstep (se 1 (by rfl) ⟨1833767, by rfl⟩ : syracuseStep 2445023 = 3667535) B3667535
theorem B5500655 : Blo 1628513 5500655 := bstep (se 1 (by rfl) ⟨4125491, by rfl⟩ : syracuseStep 5500655 = 8250983) B8250983
theorem B31731689 : Blo 1628513 31731689 := bstep (se 2 (by rfl) ⟨11899383, by rfl⟩ : syracuseStep 31731689 = 23798767) B23798767
theorem B41767325 : Blo 1628513 41767325 := bstep (se 3 (by rfl) ⟨7831373, by rfl⟩ : syracuseStep 41767325 = 15662747) B15662747
theorem B10047997 : Blo 1628513 10047997 := bstep (se 3 (by rfl) ⟨1883999, by rfl⟩ : syracuseStep 10047997 = 3767999) B3767999
theorem B17855387 : Blo 1628513 17855387 := bstep (se 1 (by rfl) ⟨13391540, by rfl⟩ : syracuseStep 17855387 = 26783081) B26783081
theorem B3666923 : Blo 1628513 3666923 := bstep (se 1 (by rfl) ⟨2750192, by rfl⟩ : syracuseStep 3666923 = 5500385) B5500385
theorem B3478783 : Blo 1628513 3478783 := bstep (se 1 (by rfl) ⟨2609087, by rfl⟩ : syracuseStep 3478783 = 5218175) B5218175
theorem B3093815 : Blo 1628513 3093815 := bstep (se 1 (by rfl) ⟨2320361, by rfl⟩ : syracuseStep 3093815 = 4640723) B4640723
theorem B12367727 : Blo 1628513 12367727 := bstep (se 1 (by rfl) ⟨9275795, by rfl⟩ : syracuseStep 12367727 = 18551591) B18551591
theorem B6608875 : Blo 1628513 6608875 := bstep (se 1 (by rfl) ⟨4956656, by rfl⟩ : syracuseStep 6608875 = 9913313) B9913313
theorem B4126889 : Blo 1628513 4126889 := bstep (se 2 (by rfl) ⟨1547583, by rfl⟩ : syracuseStep 4126889 = 3095167) B3095167
theorem B1833439 : Blo 1628513 1833439 := bstep (se 1 (by rfl) ⟨1375079, by rfl⟩ : syracuseStep 1833439 = 2750159) B2750159
theorem B1628719 : Blo 1628513 1628719 := bstep (se 1 (by rfl) ⟨1221539, by rfl⟩ : syracuseStep 1628719 = 2443079) B2443079
theorem B203479847 : Blo 1628513 203479847 := bstep (se 1 (by rfl) ⟨152609885, by rfl⟩ : syracuseStep 203479847 = 305219771) B305219771
theorem B27844883 : Blo 1628513 27844883 := bstep (se 1 (by rfl) ⟨20883662, by rfl⟩ : syracuseStep 27844883 = 41767325) B41767325
theorem B11903591 : Blo 1628513 11903591 := bstep (se 1 (by rfl) ⟨8927693, by rfl⟩ : syracuseStep 11903591 = 17855387) B17855387
theorem B8250173 : Blo 1628513 8250173 := bstep (se 3 (by rfl) ⟨1546907, by rfl⟩ : syracuseStep 8250173 = 3093815) B3093815
theorem B4638377 : Blo 1628513 4638377 := bstep (se 2 (by rfl) ⟨1739391, by rfl⟩ : syracuseStep 4638377 = 3478783) B3478783
theorem B135653231 : Blo 1628513 135653231 := bstep (se 1 (by rfl) ⟨101739923, by rfl⟩ : syracuseStep 135653231 = 203479847) B203479847
theorem B21154459 : Blo 1628513 21154459 := bstep (se 1 (by rfl) ⟨15865844, by rfl⟩ : syracuseStep 21154459 = 31731689) B31731689
theorem B2444585 : Blo 1628513 2444585 := bstep (se 2 (by rfl) ⟨916719, by rfl⟩ : syracuseStep 2444585 = 1833439) B1833439
theorem B2444615 : Blo 1628513 2444615 := bstep (se 1 (by rfl) ⟨1833461, by rfl⟩ : syracuseStep 2444615 = 3666923) B3666923
theorem B13397329 : Blo 1628513 13397329 := bstep (se 2 (by rfl) ⟨5023998, by rfl⟩ : syracuseStep 13397329 = 10047997) B10047997
theorem B23490431 : Blo 1628513 23490431 := bstep (se 1 (by rfl) ⟨17617823, by rfl⟩ : syracuseStep 23490431 = 35235647) B35235647
theorem B8245151 : Blo 1628513 8245151 := bstep (se 1 (by rfl) ⟨6183863, by rfl⟩ : syracuseStep 8245151 = 12367727) B12367727
theorem B133739423 : Blo 1628513 133739423 := bstep (se 1 (by rfl) ⟨100304567, by rfl⟩ : syracuseStep 133739423 = 200609135) B200609135
theorem B3666887 : Blo 1628513 3666887 := bstep (se 1 (by rfl) ⟨2750165, by rfl⟩ : syracuseStep 3666887 = 5500331) B5500331
theorem B3667103 : Blo 1628513 3667103 := bstep (se 1 (by rfl) ⟨2750327, by rfl⟩ : syracuseStep 3667103 = 5500655) B5500655
theorem B8811833 : Blo 1628513 8811833 := bstep (se 2 (by rfl) ⟨3304437, by rfl⟩ : syracuseStep 8811833 = 6608875) B6608875
theorem B1628655 : Blo 1628513 1628655 := bstep (se 1 (by rfl) ⟨1221491, by rfl⟩ : syracuseStep 1628655 = 2442983) B2442983
theorem B2751259 : Blo 1628513 2751259 := bstep (se 1 (by rfl) ⟨2063444, by rfl⟩ : syracuseStep 2751259 = 4126889) B4126889
theorem B1629487 : Blo 1628513 1629487 := bstep (se 1 (by rfl) ⟨1222115, by rfl⟩ : syracuseStep 1629487 = 2444231) B2444231
theorem B1630015 : Blo 1628513 1630015 := bstep (se 1 (by rfl) ⟨1222511, by rfl⟩ : syracuseStep 1630015 = 2445023) B2445023
theorem B18563255 : Blo 1628513 18563255 := bstep (se 1 (by rfl) ⟨13922441, by rfl⟩ : syracuseStep 18563255 = 27844883) B27844883
theorem B28205945 : Blo 1628513 28205945 := bstep (se 2 (by rfl) ⟨10577229, by rfl⟩ : syracuseStep 28205945 = 21154459) B21154459
theorem B5500115 : Blo 1628513 5500115 := bstep (se 1 (by rfl) ⟨4125086, by rfl⟩ : syracuseStep 5500115 = 8250173) B8250173
theorem B2444591 : Blo 1628513 2444591 := bstep (se 1 (by rfl) ⟨1833443, by rfl⟩ : syracuseStep 2444591 = 3666887) B3666887
theorem B2444735 : Blo 1628513 2444735 := bstep (se 1 (by rfl) ⟨1833551, by rfl⟩ : syracuseStep 2444735 = 3667103) B3667103
theorem B23498221 : Blo 1628513 23498221 := bstep (se 3 (by rfl) ⟨4405916, by rfl⟩ : syracuseStep 23498221 = 8811833) B8811833
theorem B3092251 : Blo 1628513 3092251 := bstep (se 1 (by rfl) ⟨2319188, by rfl⟩ : syracuseStep 3092251 = 4638377) B4638377
theorem B90435487 : Blo 1628513 90435487 := bstep (se 1 (by rfl) ⟨67826615, by rfl⟩ : syracuseStep 90435487 = 135653231) B135653231
theorem B17863105 : Blo 1628513 17863105 := bstep (se 2 (by rfl) ⟨6698664, by rfl⟩ : syracuseStep 17863105 = 13397329) B13397329
theorem B15660287 : Blo 1628513 15660287 := bstep (se 1 (by rfl) ⟨11745215, by rfl⟩ : syracuseStep 15660287 = 23490431) B23490431
theorem B7935727 : Blo 1628513 7935727 := bstep (se 1 (by rfl) ⟨5951795, by rfl⟩ : syracuseStep 7935727 = 11903591) B11903591
theorem B89159615 : Blo 1628513 89159615 := bstep (se 1 (by rfl) ⟨66869711, by rfl⟩ : syracuseStep 89159615 = 133739423) B133739423
theorem B3668345 : Blo 1628513 3668345 := bstep (se 2 (by rfl) ⟨1375629, by rfl⟩ : syracuseStep 3668345 = 2751259) B2751259
theorem B1629723 : Blo 1628513 1629723 := bstep (se 1 (by rfl) ⟨1222292, by rfl⟩ : syracuseStep 1629723 = 2444585) B2444585
theorem B1629743 : Blo 1628513 1629743 := bstep (se 1 (by rfl) ⟨1222307, by rfl⟩ : syracuseStep 1629743 = 2444615) B2444615
theorem B5496767 : Blo 1628513 5496767 := bstep (se 1 (by rfl) ⟨4122575, by rfl⟩ : syracuseStep 5496767 = 8245151) B8245151
theorem B4123001 : Blo 1628513 4123001 := bstep (se 2 (by rfl) ⟨1546125, by rfl⟩ : syracuseStep 4123001 = 3092251) B3092251
theorem B120580649 : Blo 1628513 120580649 := bstep (se 2 (by rfl) ⟨45217743, by rfl⟩ : syracuseStep 120580649 = 90435487) B90435487
theorem B3664511 : Blo 1628513 3664511 := bstep (se 1 (by rfl) ⟨2748383, by rfl⟩ : syracuseStep 3664511 = 5496767) B5496767
theorem B18803963 : Blo 1628513 18803963 := bstep (se 1 (by rfl) ⟨14102972, by rfl⟩ : syracuseStep 18803963 = 28205945) B28205945
theorem B23817473 : Blo 1628513 23817473 := bstep (se 2 (by rfl) ⟨8931552, by rfl⟩ : syracuseStep 23817473 = 17863105) B17863105
theorem B10440191 : Blo 1628513 10440191 := bstep (se 1 (by rfl) ⟨7830143, by rfl⟩ : syracuseStep 10440191 = 15660287) B15660287
theorem B2445563 : Blo 1628513 2445563 := bstep (se 1 (by rfl) ⟨1834172, by rfl⟩ : syracuseStep 2445563 = 3668345) B3668345
theorem B31330961 : Blo 1628513 31330961 := bstep (se 2 (by rfl) ⟨11749110, by rfl⟩ : syracuseStep 31330961 = 23498221) B23498221
theorem B3666743 : Blo 1628513 3666743 := bstep (se 1 (by rfl) ⟨2750057, by rfl⟩ : syracuseStep 3666743 = 5500115) B5500115
theorem B10580969 : Blo 1628513 10580969 := bstep (se 2 (by rfl) ⟨3967863, by rfl⟩ : syracuseStep 10580969 = 7935727) B7935727
theorem B12375503 : Blo 1628513 12375503 := bstep (se 1 (by rfl) ⟨9281627, by rfl⟩ : syracuseStep 12375503 = 18563255) B18563255
theorem B59439743 : Blo 1628513 59439743 := bstep (se 1 (by rfl) ⟨44579807, by rfl⟩ : syracuseStep 59439743 = 89159615) B89159615
theorem B1629727 : Blo 1628513 1629727 := bstep (se 1 (by rfl) ⟨1222295, by rfl⟩ : syracuseStep 1629727 = 2444591) B2444591
theorem B1629823 : Blo 1628513 1629823 := bstep (se 1 (by rfl) ⟨1222367, by rfl⟩ : syracuseStep 1629823 = 2444735) B2444735
theorem B1630375 : Blo 1628513 1630375 := bstep (se 1 (by rfl) ⟨1222781, by rfl⟩ : syracuseStep 1630375 = 2445563) B2445563
theorem B7053979 : Blo 1628513 7053979 := bstep (se 1 (by rfl) ⟨5290484, by rfl⟩ : syracuseStep 7053979 = 10580969) B10580969
theorem B8250335 : Blo 1628513 8250335 := bstep (se 1 (by rfl) ⟨6187751, by rfl⟩ : syracuseStep 8250335 = 12375503) B12375503
theorem B2443007 : Blo 1628513 2443007 := bstep (se 1 (by rfl) ⟨1832255, by rfl⟩ : syracuseStep 2443007 = 3664511) B3664511
theorem B39626495 : Blo 1628513 39626495 := bstep (se 1 (by rfl) ⟨29719871, by rfl⟩ : syracuseStep 39626495 = 59439743) B59439743
theorem B12535975 : Blo 1628513 12535975 := bstep (se 1 (by rfl) ⟨9401981, by rfl⟩ : syracuseStep 12535975 = 18803963) B18803963
theorem B15878315 : Blo 1628513 15878315 := bstep (se 1 (by rfl) ⟨11908736, by rfl⟩ : syracuseStep 15878315 = 23817473) B23817473
theorem B2444495 : Blo 1628513 2444495 := bstep (se 1 (by rfl) ⟨1833371, by rfl⟩ : syracuseStep 2444495 = 3666743) B3666743
theorem B27840509 : Blo 1628513 27840509 := bstep (se 3 (by rfl) ⟨5220095, by rfl⟩ : syracuseStep 27840509 = 10440191) B10440191
theorem B2748667 : Blo 1628513 2748667 := bstep (se 1 (by rfl) ⟨2061500, by rfl⟩ : syracuseStep 2748667 = 4123001) B4123001
theorem B20887307 : Blo 1628513 20887307 := bstep (se 1 (by rfl) ⟨15665480, by rfl⟩ : syracuseStep 20887307 = 31330961) B31330961
theorem B80387099 : Blo 1628513 80387099 := bstep (se 1 (by rfl) ⟨60290324, by rfl⟩ : syracuseStep 80387099 = 120580649) B120580649
theorem B9405305 : Blo 1628513 9405305 := bstep (se 2 (by rfl) ⟨3526989, by rfl⟩ : syracuseStep 9405305 = 7053979) B7053979
theorem B16714633 : Blo 1628513 16714633 := bstep (se 2 (by rfl) ⟨6267987, by rfl⟩ : syracuseStep 16714633 = 12535975) B12535975
theorem B3664889 : Blo 1628513 3664889 := bstep (se 2 (by rfl) ⟨1374333, by rfl⟩ : syracuseStep 3664889 = 2748667) B2748667
theorem B5500223 : Blo 1628513 5500223 := bstep (se 1 (by rfl) ⟨4125167, by rfl⟩ : syracuseStep 5500223 = 8250335) B8250335
theorem B18560339 : Blo 1628513 18560339 := bstep (se 1 (by rfl) ⟨13920254, by rfl⟩ : syracuseStep 18560339 = 27840509) B27840509
theorem B42342173 : Blo 1628513 42342173 := bstep (se 3 (by rfl) ⟨7939157, by rfl⟩ : syracuseStep 42342173 = 15878315) B15878315
theorem B1628671 : Blo 1628513 1628671 := bstep (se 1 (by rfl) ⟨1221503, by rfl⟩ : syracuseStep 1628671 = 2443007) B2443007
theorem B26417663 : Blo 1628513 26417663 := bstep (se 1 (by rfl) ⟨19813247, by rfl⟩ : syracuseStep 26417663 = 39626495) B39626495
theorem B13924871 : Blo 1628513 13924871 := bstep (se 1 (by rfl) ⟨10443653, by rfl⟩ : syracuseStep 13924871 = 20887307) B20887307
theorem B53591399 : Blo 1628513 53591399 := bstep (se 1 (by rfl) ⟨40193549, by rfl⟩ : syracuseStep 53591399 = 80387099) B80387099
theorem B1629663 : Blo 1628513 1629663 := bstep (se 1 (by rfl) ⟨1222247, by rfl⟩ : syracuseStep 1629663 = 2444495) B2444495
theorem B9283247 : Blo 1628513 9283247 := bstep (se 1 (by rfl) ⟨6962435, by rfl⟩ : syracuseStep 9283247 = 13924871) B13924871
theorem B2443259 : Blo 1628513 2443259 := bstep (se 1 (by rfl) ⟨1832444, by rfl⟩ : syracuseStep 2443259 = 3664889) B3664889
theorem B35727599 : Blo 1628513 35727599 := bstep (se 1 (by rfl) ⟨26795699, by rfl⟩ : syracuseStep 35727599 = 53591399) B53591399
theorem B6270203 : Blo 1628513 6270203 := bstep (se 1 (by rfl) ⟨4702652, by rfl⟩ : syracuseStep 6270203 = 9405305) B9405305
theorem B12373559 : Blo 1628513 12373559 := bstep (se 1 (by rfl) ⟨9280169, by rfl⟩ : syracuseStep 12373559 = 18560339) B18560339
theorem B22286177 : Blo 1628513 22286177 := bstep (se 2 (by rfl) ⟨8357316, by rfl⟩ : syracuseStep 22286177 = 16714633) B16714633
theorem B3666815 : Blo 1628513 3666815 := bstep (se 1 (by rfl) ⟨2750111, by rfl⟩ : syracuseStep 3666815 = 5500223) B5500223
theorem B28228115 : Blo 1628513 28228115 := bstep (se 1 (by rfl) ⟨21171086, by rfl⟩ : syracuseStep 28228115 = 42342173) B42342173
theorem B17611775 : Blo 1628513 17611775 := bstep (se 1 (by rfl) ⟨13208831, by rfl⟩ : syracuseStep 17611775 = 26417663) B26417663
theorem B95273597 : Blo 1628513 95273597 := bstep (se 3 (by rfl) ⟨17863799, by rfl⟩ : syracuseStep 95273597 = 35727599) B35727599
theorem B16720541 : Blo 1628513 16720541 := bstep (se 3 (by rfl) ⟨3135101, by rfl⟩ : syracuseStep 16720541 = 6270203) B6270203
theorem B18818743 : Blo 1628513 18818743 := bstep (se 1 (by rfl) ⟨14114057, by rfl⟩ : syracuseStep 18818743 = 28228115) B28228115
theorem B11741183 : Blo 1628513 11741183 := bstep (se 1 (by rfl) ⟨8805887, by rfl⟩ : syracuseStep 11741183 = 17611775) B17611775
theorem B2444543 : Blo 1628513 2444543 := bstep (se 1 (by rfl) ⟨1833407, by rfl⟩ : syracuseStep 2444543 = 3666815) B3666815
theorem B6188831 : Blo 1628513 6188831 := bstep (se 1 (by rfl) ⟨4641623, by rfl⟩ : syracuseStep 6188831 = 9283247) B9283247
theorem B14857451 : Blo 1628513 14857451 := bstep (se 1 (by rfl) ⟨11143088, by rfl⟩ : syracuseStep 14857451 = 22286177) B22286177
theorem B1628839 : Blo 1628513 1628839 := bstep (se 1 (by rfl) ⟨1221629, by rfl⟩ : syracuseStep 1628839 = 2443259) B2443259
theorem B8249039 : Blo 1628513 8249039 := bstep (se 1 (by rfl) ⟨6186779, by rfl⟩ : syracuseStep 8249039 = 12373559) B12373559
theorem B9904967 : Blo 1628513 9904967 := bstep (se 1 (by rfl) ⟨7428725, by rfl⟩ : syracuseStep 9904967 = 14857451) B14857451
theorem B5499359 : Blo 1628513 5499359 := bstep (se 1 (by rfl) ⟨4124519, by rfl⟩ : syracuseStep 5499359 = 8249039) B8249039
theorem B7827455 : Blo 1628513 7827455 := bstep (se 1 (by rfl) ⟨5870591, by rfl⟩ : syracuseStep 7827455 = 11741183) B11741183
theorem B254062925 : Blo 1628513 254062925 := bstep (se 3 (by rfl) ⟨47636798, by rfl⟩ : syracuseStep 254062925 = 95273597) B95273597
theorem B4125887 : Blo 1628513 4125887 := bstep (se 1 (by rfl) ⟨3094415, by rfl⟩ : syracuseStep 4125887 = 6188831) B6188831
theorem B11147027 : Blo 1628513 11147027 := bstep (se 1 (by rfl) ⟨8360270, by rfl⟩ : syracuseStep 11147027 = 16720541) B16720541
theorem B1629695 : Blo 1628513 1629695 := bstep (se 1 (by rfl) ⟨1222271, by rfl⟩ : syracuseStep 1629695 = 2444543) B2444543
theorem B25091657 : Blo 1628513 25091657 := bstep (se 2 (by rfl) ⟨9409371, by rfl⟩ : syracuseStep 25091657 = 18818743) B18818743
theorem B6603311 : Blo 1628513 6603311 := bstep (se 1 (by rfl) ⟨4952483, by rfl⟩ : syracuseStep 6603311 = 9904967) B9904967
theorem B118901621 : Blo 1628513 118901621 := bstep (se 5 (by rfl) ⟨5573513, by rfl⟩ : syracuseStep 118901621 = 11147027) B11147027
theorem B3666239 : Blo 1628513 3666239 := bstep (se 1 (by rfl) ⟨2749679, by rfl⟩ : syracuseStep 3666239 = 5499359) B5499359
theorem B169375283 : Blo 1628513 169375283 := bstep (se 1 (by rfl) ⟨127031462, by rfl⟩ : syracuseStep 169375283 = 254062925) B254062925
theorem B2750591 : Blo 1628513 2750591 := bstep (se 1 (by rfl) ⟨2062943, by rfl⟩ : syracuseStep 2750591 = 4125887) B4125887
theorem B16727771 : Blo 1628513 16727771 := bstep (se 1 (by rfl) ⟨12545828, by rfl⟩ : syracuseStep 16727771 = 25091657) B25091657
theorem B5218303 : Blo 1628513 5218303 := bstep (se 1 (by rfl) ⟨3913727, by rfl⟩ : syracuseStep 5218303 = 7827455) B7827455
theorem B79267747 : Blo 1628513 79267747 := bstep (se 1 (by rfl) ⟨59450810, by rfl⟩ : syracuseStep 79267747 = 118901621) B118901621
theorem B11151847 : Blo 1628513 11151847 := bstep (se 1 (by rfl) ⟨8363885, by rfl⟩ : syracuseStep 11151847 = 16727771) B16727771
theorem B6957737 : Blo 1628513 6957737 := bstep (se 2 (by rfl) ⟨2609151, by rfl⟩ : syracuseStep 6957737 = 5218303) B5218303
theorem B2444159 : Blo 1628513 2444159 := bstep (se 1 (by rfl) ⟨1833119, by rfl⟩ : syracuseStep 2444159 = 3666239) B3666239
theorem B4402207 : Blo 1628513 4402207 := bstep (se 1 (by rfl) ⟨3301655, by rfl⟩ : syracuseStep 4402207 = 6603311) B6603311
theorem B112916855 : Blo 1628513 112916855 := bstep (se 1 (by rfl) ⟨84687641, by rfl⟩ : syracuseStep 112916855 = 169375283) B169375283
theorem B1833727 : Blo 1628513 1833727 := bstep (se 1 (by rfl) ⟨1375295, by rfl⟩ : syracuseStep 1833727 = 2750591) B2750591
theorem B23478437 : Blo 1628513 23478437 := bstep (se 4 (by rfl) ⟨2201103, by rfl⟩ : syracuseStep 23478437 = 4402207) B4402207
theorem B14869129 : Blo 1628513 14869129 := bstep (se 2 (by rfl) ⟨5575923, by rfl⟩ : syracuseStep 14869129 = 11151847) B11151847
theorem B4638491 : Blo 1628513 4638491 := bstep (se 1 (by rfl) ⟨3478868, by rfl⟩ : syracuseStep 4638491 = 6957737) B6957737
theorem B2444969 : Blo 1628513 2444969 := bstep (se 2 (by rfl) ⟨916863, by rfl⟩ : syracuseStep 2444969 = 1833727) B1833727
theorem B105690329 : Blo 1628513 105690329 := bstep (se 2 (by rfl) ⟨39633873, by rfl⟩ : syracuseStep 105690329 = 79267747) B79267747
theorem B301111613 : Blo 1628513 301111613 := bstep (se 3 (by rfl) ⟨56458427, by rfl⟩ : syracuseStep 301111613 = 112916855) B112916855
theorem B1629439 : Blo 1628513 1629439 := bstep (se 1 (by rfl) ⟨1222079, by rfl⟩ : syracuseStep 1629439 = 2444159) B2444159
theorem B70460219 : Blo 1628513 70460219 := bstep (se 1 (by rfl) ⟨52845164, by rfl⟩ : syracuseStep 70460219 = 105690329) B105690329
theorem B19825505 : Blo 1628513 19825505 := bstep (se 2 (by rfl) ⟨7434564, by rfl⟩ : syracuseStep 19825505 = 14869129) B14869129
theorem B3092327 : Blo 1628513 3092327 := bstep (se 1 (by rfl) ⟨2319245, by rfl⟩ : syracuseStep 3092327 = 4638491) B4638491
theorem B200741075 : Blo 1628513 200741075 := bstep (se 1 (by rfl) ⟨150555806, by rfl⟩ : syracuseStep 200741075 = 301111613) B301111613
theorem B15652291 : Blo 1628513 15652291 := bstep (se 1 (by rfl) ⟨11739218, by rfl⟩ : syracuseStep 15652291 = 23478437) B23478437
theorem B1629979 : Blo 1628513 1629979 := bstep (se 1 (by rfl) ⟨1222484, by rfl⟩ : syracuseStep 1629979 = 2444969) B2444969
theorem B46973479 : Blo 1628513 46973479 := bstep (se 1 (by rfl) ⟨35230109, by rfl⟩ : syracuseStep 46973479 = 70460219) B70460219
theorem B133827383 : Blo 1628513 133827383 := bstep (se 1 (by rfl) ⟨100370537, by rfl⟩ : syracuseStep 133827383 = 200741075) B200741075
theorem B13217003 : Blo 1628513 13217003 := bstep (se 1 (by rfl) ⟨9912752, by rfl⟩ : syracuseStep 13217003 = 19825505) B19825505
theorem B20869721 : Blo 1628513 20869721 := bstep (se 2 (by rfl) ⟨7826145, by rfl⟩ : syracuseStep 20869721 = 15652291) B15652291
theorem B2061551 : Blo 1628513 2061551 := bstep (se 1 (by rfl) ⟨1546163, by rfl⟩ : syracuseStep 2061551 = 3092327) B3092327
theorem B5497469 : Blo 1628513 5497469 := bstep (se 3 (by rfl) ⟨1030775, by rfl⟩ : syracuseStep 5497469 = 2061551) B2061551
theorem B13913147 : Blo 1628513 13913147 := bstep (se 1 (by rfl) ⟨10434860, by rfl⟩ : syracuseStep 13913147 = 20869721) B20869721
theorem B62631305 : Blo 1628513 62631305 := bstep (se 2 (by rfl) ⟨23486739, by rfl⟩ : syracuseStep 62631305 = 46973479) B46973479
theorem B8811335 : Blo 1628513 8811335 := bstep (se 1 (by rfl) ⟨6608501, by rfl⟩ : syracuseStep 8811335 = 13217003) B13217003
theorem B89218255 : Blo 1628513 89218255 := bstep (se 1 (by rfl) ⟨66913691, by rfl⟩ : syracuseStep 89218255 = 133827383) B133827383
theorem B5874223 : Blo 1628513 5874223 := bstep (se 1 (by rfl) ⟨4405667, by rfl⟩ : syracuseStep 5874223 = 8811335) B8811335
theorem B118957673 : Blo 1628513 118957673 := bstep (se 2 (by rfl) ⟨44609127, by rfl⟩ : syracuseStep 118957673 = 89218255) B89218255
theorem B9275431 : Blo 1628513 9275431 := bstep (se 1 (by rfl) ⟨6956573, by rfl⟩ : syracuseStep 9275431 = 13913147) B13913147
theorem B3664979 : Blo 1628513 3664979 := bstep (se 1 (by rfl) ⟨2748734, by rfl⟩ : syracuseStep 3664979 = 5497469) B5497469
theorem B41754203 : Blo 1628513 41754203 := bstep (se 1 (by rfl) ⟨31315652, by rfl⟩ : syracuseStep 41754203 = 62631305) B62631305
theorem B7832297 : Blo 1628513 7832297 := bstep (se 2 (by rfl) ⟨2937111, by rfl⟩ : syracuseStep 7832297 = 5874223) B5874223
theorem B2443319 : Blo 1628513 2443319 := bstep (se 1 (by rfl) ⟨1832489, by rfl⟩ : syracuseStep 2443319 = 3664979) B3664979
theorem B12367241 : Blo 1628513 12367241 := bstep (se 2 (by rfl) ⟨4637715, by rfl⟩ : syracuseStep 12367241 = 9275431) B9275431
theorem B79305115 : Blo 1628513 79305115 := bstep (se 1 (by rfl) ⟨59478836, by rfl⟩ : syracuseStep 79305115 = 118957673) B118957673
theorem B27836135 : Blo 1628513 27836135 := bstep (se 1 (by rfl) ⟨20877101, by rfl⟩ : syracuseStep 27836135 = 41754203) B41754203
theorem B18557423 : Blo 1628513 18557423 := bstep (se 1 (by rfl) ⟨13918067, by rfl⟩ : syracuseStep 18557423 = 27836135) B27836135
theorem B5221531 : Blo 1628513 5221531 := bstep (se 1 (by rfl) ⟨3916148, by rfl⟩ : syracuseStep 5221531 = 7832297) B7832297
theorem B8244827 : Blo 1628513 8244827 := bstep (se 1 (by rfl) ⟨6183620, by rfl⟩ : syracuseStep 8244827 = 12367241) B12367241
theorem B105740153 : Blo 1628513 105740153 := bstep (se 2 (by rfl) ⟨39652557, by rfl⟩ : syracuseStep 105740153 = 79305115) B79305115
theorem B1628879 : Blo 1628513 1628879 := bstep (se 1 (by rfl) ⟨1221659, by rfl⟩ : syracuseStep 1628879 = 2443319) B2443319
theorem B70493435 : Blo 1628513 70493435 := bstep (se 1 (by rfl) ⟨52870076, by rfl⟩ : syracuseStep 70493435 = 105740153) B105740153
theorem B12371615 : Blo 1628513 12371615 := bstep (se 1 (by rfl) ⟨9278711, by rfl⟩ : syracuseStep 12371615 = 18557423) B18557423
theorem B6962041 : Blo 1628513 6962041 := bstep (se 2 (by rfl) ⟨2610765, by rfl⟩ : syracuseStep 6962041 = 5221531) B5221531
theorem B5496551 : Blo 1628513 5496551 := bstep (se 1 (by rfl) ⟨4122413, by rfl⟩ : syracuseStep 5496551 = 8244827) B8244827
theorem B9282721 : Blo 1628513 9282721 := bstep (se 2 (by rfl) ⟨3481020, by rfl⟩ : syracuseStep 9282721 = 6962041) B6962041
theorem B3664367 : Blo 1628513 3664367 := bstep (se 1 (by rfl) ⟨2748275, by rfl⟩ : syracuseStep 3664367 = 5496551) B5496551
theorem B46995623 : Blo 1628513 46995623 := bstep (se 1 (by rfl) ⟨35246717, by rfl⟩ : syracuseStep 46995623 = 70493435) B70493435
theorem B8247743 : Blo 1628513 8247743 := bstep (se 1 (by rfl) ⟨6185807, by rfl⟩ : syracuseStep 8247743 = 12371615) B12371615
theorem B5498495 : Blo 1628513 5498495 := bstep (se 1 (by rfl) ⟨4123871, by rfl⟩ : syracuseStep 5498495 = 8247743) B8247743
theorem B2442911 : Blo 1628513 2442911 := bstep (se 1 (by rfl) ⟨1832183, by rfl⟩ : syracuseStep 2442911 = 3664367) B3664367
theorem B31330415 : Blo 1628513 31330415 := bstep (se 1 (by rfl) ⟨23497811, by rfl⟩ : syracuseStep 31330415 = 46995623) B46995623
theorem B12376961 : Blo 1628513 12376961 := bstep (se 2 (by rfl) ⟨4641360, by rfl⟩ : syracuseStep 12376961 = 9282721) B9282721
theorem B8251307 : Blo 1628513 8251307 := bstep (se 1 (by rfl) ⟨6188480, by rfl⟩ : syracuseStep 8251307 = 12376961) B12376961
theorem B3665663 : Blo 1628513 3665663 := bstep (se 1 (by rfl) ⟨2749247, by rfl⟩ : syracuseStep 3665663 = 5498495) B5498495
theorem B20886943 : Blo 1628513 20886943 := bstep (se 1 (by rfl) ⟨15665207, by rfl⟩ : syracuseStep 20886943 = 31330415) B31330415
theorem B1628607 : Blo 1628513 1628607 := bstep (se 1 (by rfl) ⟨1221455, by rfl⟩ : syracuseStep 1628607 = 2442911) B2442911
theorem B2443775 : Blo 1628513 2443775 := bstep (se 1 (by rfl) ⟨1832831, by rfl⟩ : syracuseStep 2443775 = 3665663) B3665663
theorem B5500871 : Blo 1628513 5500871 := bstep (se 1 (by rfl) ⟨4125653, by rfl⟩ : syracuseStep 5500871 = 8251307) B8251307
theorem B27849257 : Blo 1628513 27849257 := bstep (se 2 (by rfl) ⟨10443471, by rfl⟩ : syracuseStep 27849257 = 20886943) B20886943
theorem B18566171 : Blo 1628513 18566171 := bstep (se 1 (by rfl) ⟨13924628, by rfl⟩ : syracuseStep 18566171 = 27849257) B27849257
theorem B3667247 : Blo 1628513 3667247 := bstep (se 1 (by rfl) ⟨2750435, by rfl⟩ : syracuseStep 3667247 = 5500871) B5500871
theorem B1629183 : Blo 1628513 1629183 := bstep (se 1 (by rfl) ⟨1221887, by rfl⟩ : syracuseStep 1629183 = 2443775) B2443775
theorem B2444831 : Blo 1628513 2444831 := bstep (se 1 (by rfl) ⟨1833623, by rfl⟩ : syracuseStep 2444831 = 3667247) B3667247
theorem B12377447 : Blo 1628513 12377447 := bstep (se 1 (by rfl) ⟨9283085, by rfl⟩ : syracuseStep 12377447 = 18566171) B18566171
theorem B8251631 : Blo 1628513 8251631 := bstep (se 1 (by rfl) ⟨6188723, by rfl⟩ : syracuseStep 8251631 = 12377447) B12377447
theorem B1629887 : Blo 1628513 1629887 := bstep (se 1 (by rfl) ⟨1222415, by rfl⟩ : syracuseStep 1629887 = 2444831) B2444831
theorem B5501087 : Blo 1628513 5501087 := bstep (se 1 (by rfl) ⟨4125815, by rfl⟩ : syracuseStep 5501087 = 8251631) B8251631
theorem B3667391 : Blo 1628513 3667391 := bstep (se 1 (by rfl) ⟨2750543, by rfl⟩ : syracuseStep 3667391 = 5501087) B5501087
theorem B2444927 : Blo 1628513 2444927 := bstep (se 1 (by rfl) ⟨1833695, by rfl⟩ : syracuseStep 2444927 = 3667391) B3667391
theorem B1629951 : Blo 1628513 1629951 := bstep (se 1 (by rfl) ⟨1222463, by rfl⟩ : syracuseStep 1629951 = 2444927) B2444927

theorem C0 (j : ℕ) (h1 : 407128 ≤ j) (h2 : j ≤ 407627) : Blo 1628513 (4 * j + 3) := by
  interval_cases j
  · exact B1628515
  · exact B1628519
  · exact B1628523
  · exact B1628527
  · exact B1628531
  · exact B1628535
  · exact B1628539
  · exact B1628543
  · exact B1628547
  · exact B1628551
  · exact B1628555
  · exact B1628559
  · exact B1628563
  · exact B1628567
  · exact B1628571
  · exact B1628575
  · exact B1628579
  · exact B1628583
  · exact B1628587
  · exact B1628591
  · exact B1628595
  · exact B1628599
  · exact B1628603
  · exact B1628607
  · exact B1628611
  · exact B1628615
  · exact B1628619
  · exact B1628623
  · exact B1628627
  · exact B1628631
  · exact B1628635
  · exact B1628639
  · exact B1628643
  · exact B1628647
  · exact B1628651
  · exact B1628655
  · exact B1628659
  · exact B1628663
  · exact B1628667
  · exact B1628671
  · exact B1628675
  · exact B1628679
  · exact B1628683
  · exact B1628687
  · exact B1628691
  · exact B1628695
  · exact B1628699
  · exact B1628703
  · exact B1628707
  · exact B1628711
  · exact B1628715
  · exact B1628719
  · exact B1628723
  · exact B1628727
  · exact B1628731
  · exact B1628735
  · exact B1628739
  · exact B1628743
  · exact B1628747
  · exact B1628751
  · exact B1628755
  · exact B1628759
  · exact B1628763
  · exact B1628767
  · exact B1628771
  · exact B1628775
  · exact B1628779
  · exact B1628783
  · exact B1628787
  · exact B1628791
  · exact B1628795
  · exact B1628799
  · exact B1628803
  · exact B1628807
  · exact B1628811
  · exact B1628815
  · exact B1628819
  · exact B1628823
  · exact B1628827
  · exact B1628831
  · exact B1628835
  · exact B1628839
  · exact B1628843
  · exact B1628847
  · exact B1628851
  · exact B1628855
  · exact B1628859
  · exact B1628863
  · exact B1628867
  · exact B1628871
  · exact B1628875
  · exact B1628879
  · exact B1628883
  · exact B1628887
  · exact B1628891
  · exact B1628895
  · exact B1628899
  · exact B1628903
  · exact B1628907
  · exact B1628911
  · exact B1628915
  · exact B1628919
  · exact B1628923
  · exact B1628927
  · exact B1628931
  · exact B1628935
  · exact B1628939
  · exact B1628943
  · exact B1628947
  · exact B1628951
  · exact B1628955
  · exact B1628959
  · exact B1628963
  · exact B1628967
  · exact B1628971
  · exact B1628975
  · exact B1628979
  · exact B1628983
  · exact B1628987
  · exact B1628991
  · exact B1628995
  · exact B1628999
  · exact B1629003
  · exact B1629007
  · exact B1629011
  · exact B1629015
  · exact B1629019
  · exact B1629023
  · exact B1629027
  · exact B1629031
  · exact B1629035
  · exact B1629039
  · exact B1629043
  · exact B1629047
  · exact B1629051
  · exact B1629055
  · exact B1629059
  · exact B1629063
  · exact B1629067
  · exact B1629071
  · exact B1629075
  · exact B1629079
  · exact B1629083
  · exact B1629087
  · exact B1629091
  · exact B1629095
  · exact B1629099
  · exact B1629103
  · exact B1629107
  · exact B1629111
  · exact B1629115
  · exact B1629119
  · exact B1629123
  · exact B1629127
  · exact B1629131
  · exact B1629135
  · exact B1629139
  · exact B1629143
  · exact B1629147
  · exact B1629151
  · exact B1629155
  · exact B1629159
  · exact B1629163
  · exact B1629167
  · exact B1629171
  · exact B1629175
  · exact B1629179
  · exact B1629183
  · exact B1629187
  · exact B1629191
  · exact B1629195
  · exact B1629199
  · exact B1629203
  · exact B1629207
  · exact B1629211
  · exact B1629215
  · exact B1629219
  · exact B1629223
  · exact B1629227
  · exact B1629231
  · exact B1629235
  · exact B1629239
  · exact B1629243
  · exact B1629247
  · exact B1629251
  · exact B1629255
  · exact B1629259
  · exact B1629263
  · exact B1629267
  · exact B1629271
  · exact B1629275
  · exact B1629279
  · exact B1629283
  · exact B1629287
  · exact B1629291
  · exact B1629295
  · exact B1629299
  · exact B1629303
  · exact B1629307
  · exact B1629311
  · exact B1629315
  · exact B1629319
  · exact B1629323
  · exact B1629327
  · exact B1629331
  · exact B1629335
  · exact B1629339
  · exact B1629343
  · exact B1629347
  · exact B1629351
  · exact B1629355
  · exact B1629359
  · exact B1629363
  · exact B1629367
  · exact B1629371
  · exact B1629375
  · exact B1629379
  · exact B1629383
  · exact B1629387
  · exact B1629391
  · exact B1629395
  · exact B1629399
  · exact B1629403
  · exact B1629407
  · exact B1629411
  · exact B1629415
  · exact B1629419
  · exact B1629423
  · exact B1629427
  · exact B1629431
  · exact B1629435
  · exact B1629439
  · exact B1629443
  · exact B1629447
  · exact B1629451
  · exact B1629455
  · exact B1629459
  · exact B1629463
  · exact B1629467
  · exact B1629471
  · exact B1629475
  · exact B1629479
  · exact B1629483
  · exact B1629487
  · exact B1629491
  · exact B1629495
  · exact B1629499
  · exact B1629503
  · exact B1629507
  · exact B1629511
  · exact B1629515
  · exact B1629519
  · exact B1629523
  · exact B1629527
  · exact B1629531
  · exact B1629535
  · exact B1629539
  · exact B1629543
  · exact B1629547
  · exact B1629551
  · exact B1629555
  · exact B1629559
  · exact B1629563
  · exact B1629567
  · exact B1629571
  · exact B1629575
  · exact B1629579
  · exact B1629583
  · exact B1629587
  · exact B1629591
  · exact B1629595
  · exact B1629599
  · exact B1629603
  · exact B1629607
  · exact B1629611
  · exact B1629615
  · exact B1629619
  · exact B1629623
  · exact B1629627
  · exact B1629631
  · exact B1629635
  · exact B1629639
  · exact B1629643
  · exact B1629647
  · exact B1629651
  · exact B1629655
  · exact B1629659
  · exact B1629663
  · exact B1629667
  · exact B1629671
  · exact B1629675
  · exact B1629679
  · exact B1629683
  · exact B1629687
  · exact B1629691
  · exact B1629695
  · exact B1629699
  · exact B1629703
  · exact B1629707
  · exact B1629711
  · exact B1629715
  · exact B1629719
  · exact B1629723
  · exact B1629727
  · exact B1629731
  · exact B1629735
  · exact B1629739
  · exact B1629743
  · exact B1629747
  · exact B1629751
  · exact B1629755
  · exact B1629759
  · exact B1629763
  · exact B1629767
  · exact B1629771
  · exact B1629775
  · exact B1629779
  · exact B1629783
  · exact B1629787
  · exact B1629791
  · exact B1629795
  · exact B1629799
  · exact B1629803
  · exact B1629807
  · exact B1629811
  · exact B1629815
  · exact B1629819
  · exact B1629823
  · exact B1629827
  · exact B1629831
  · exact B1629835
  · exact B1629839
  · exact B1629843
  · exact B1629847
  · exact B1629851
  · exact B1629855
  · exact B1629859
  · exact B1629863
  · exact B1629867
  · exact B1629871
  · exact B1629875
  · exact B1629879
  · exact B1629883
  · exact B1629887
  · exact B1629891
  · exact B1629895
  · exact B1629899
  · exact B1629903
  · exact B1629907
  · exact B1629911
  · exact B1629915
  · exact B1629919
  · exact B1629923
  · exact B1629927
  · exact B1629931
  · exact B1629935
  · exact B1629939
  · exact B1629943
  · exact B1629947
  · exact B1629951
  · exact B1629955
  · exact B1629959
  · exact B1629963
  · exact B1629967
  · exact B1629971
  · exact B1629975
  · exact B1629979
  · exact B1629983
  · exact B1629987
  · exact B1629991
  · exact B1629995
  · exact B1629999
  · exact B1630003
  · exact B1630007
  · exact B1630011
  · exact B1630015
  · exact B1630019
  · exact B1630023
  · exact B1630027
  · exact B1630031
  · exact B1630035
  · exact B1630039
  · exact B1630043
  · exact B1630047
  · exact B1630051
  · exact B1630055
  · exact B1630059
  · exact B1630063
  · exact B1630067
  · exact B1630071
  · exact B1630075
  · exact B1630079
  · exact B1630083
  · exact B1630087
  · exact B1630091
  · exact B1630095
  · exact B1630099
  · exact B1630103
  · exact B1630107
  · exact B1630111
  · exact B1630115
  · exact B1630119
  · exact B1630123
  · exact B1630127
  · exact B1630131
  · exact B1630135
  · exact B1630139
  · exact B1630143
  · exact B1630147
  · exact B1630151
  · exact B1630155
  · exact B1630159
  · exact B1630163
  · exact B1630167
  · exact B1630171
  · exact B1630175
  · exact B1630179
  · exact B1630183
  · exact B1630187
  · exact B1630191
  · exact B1630195
  · exact B1630199
  · exact B1630203
  · exact B1630207
  · exact B1630211
  · exact B1630215
  · exact B1630219
  · exact B1630223
  · exact B1630227
  · exact B1630231
  · exact B1630235
  · exact B1630239
  · exact B1630243
  · exact B1630247
  · exact B1630251
  · exact B1630255
  · exact B1630259
  · exact B1630263
  · exact B1630267
  · exact B1630271
  · exact B1630275
  · exact B1630279
  · exact B1630283
  · exact B1630287
  · exact B1630291
  · exact B1630295
  · exact B1630299
  · exact B1630303
  · exact B1630307
  · exact B1630311
  · exact B1630315
  · exact B1630319
  · exact B1630323
  · exact B1630327
  · exact B1630331
  · exact B1630335
  · exact B1630339
  · exact B1630343
  · exact B1630347
  · exact B1630351
  · exact B1630355
  · exact B1630359
  · exact B1630363
  · exact B1630367
  · exact B1630371
  · exact B1630375
  · exact B1630379
  · exact B1630383
  · exact B1630387
  · exact B1630391
  · exact B1630395
  · exact B1630399
  · exact B1630403
  · exact B1630407
  · exact B1630411
  · exact B1630415
  · exact B1630419
  · exact B1630423
  · exact B1630427
  · exact B1630431
  · exact B1630435
  · exact B1630439
  · exact B1630443
  · exact B1630447
  · exact B1630451
  · exact B1630455
  · exact B1630459
  · exact B1630463
  · exact B1630467
  · exact B1630471
  · exact B1630475
  · exact B1630479
  · exact B1630483
  · exact B1630487
  · exact B1630491
  · exact B1630495
  · exact B1630499
  · exact B1630503
  · exact B1630507
  · exact B1630511

theorem solution (m : ℕ) (hlo : 1628513 ≤ m) (hhi : m ≤ 1630513) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 407128 ≤ j := by omega
    have hj2 : j ≤ 407627 := by omega
    have hb : Blo 1628513 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
