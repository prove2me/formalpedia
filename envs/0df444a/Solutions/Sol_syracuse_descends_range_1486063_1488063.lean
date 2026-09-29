-- Prove2me | solution 1 for syracuse_descends_range_1486063_1488063
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:46:21.577656+00:00
-- url     : https://prove2.me/submissions/23ba4395-928e-4099-b58d-db37cc8b6daf

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


theorem B8036405 : Blo 1486063 8036405 := bbase (se 5 (by rfl) ⟨376706, by rfl⟩ : syracuseStep 8036405 = 753413) (by norm_num)
theorem B2678845 : Blo 1486063 2678845 := bbase (se 3 (by rfl) ⟨502283, by rfl⟩ : syracuseStep 2678845 = 1004567) (by norm_num)
theorem B1933637 : Blo 1486063 1933637 := bbase (se 4 (by rfl) ⟨181278, by rfl⟩ : syracuseStep 1933637 = 362557) (by norm_num)
theorem B3621205 : Blo 1486063 3621205 := bbase (se 10 (by rfl) ⟨5304, by rfl⟩ : syracuseStep 3621205 = 10609) (by norm_num)
theorem B5022053 : Blo 1486063 5022053 := bbase (se 4 (by rfl) ⟨470817, by rfl⟩ : syracuseStep 5022053 = 941635) (by norm_num)
theorem B7528949 : Blo 1486063 7528949 := bbase (se 5 (by rfl) ⟨352919, by rfl⟩ : syracuseStep 7528949 = 705839) (by norm_num)
theorem B3867173 : Blo 1486063 3867173 := bbase (se 4 (by rfl) ⟨362547, by rfl⟩ : syracuseStep 3867173 = 725095) (by norm_num)
theorem B1810993 : Blo 1486063 1810993 := bbase (se 2 (by rfl) ⟨679122, by rfl⟩ : syracuseStep 1810993 = 1358245) (by norm_num)
theorem B2900549 : Blo 1486063 2900549 := bbase (se 4 (by rfl) ⟨271926, by rfl⟩ : syracuseStep 2900549 = 543853) (by norm_num)
theorem B1884749 : Blo 1486063 1884749 := bbase (se 3 (by rfl) ⟨353390, by rfl⟩ : syracuseStep 1884749 = 706781) (by norm_num)
theorem B1671853 : Blo 1486063 1671853 := bbase (se 3 (by rfl) ⟨313472, by rfl⟩ : syracuseStep 1671853 = 626945) (by norm_num)
theorem B5644997 : Blo 1486063 5644997 := bbase (se 4 (by rfl) ⟨529218, by rfl⟩ : syracuseStep 5644997 = 1058437) (by norm_num)
theorem B1671889 : Blo 1486063 1671889 := bbase (se 2 (by rfl) ⟨626958, by rfl⟩ : syracuseStep 1671889 = 1253917) (by norm_num)
theorem B1671925 : Blo 1486063 1671925 := bbase (se 5 (by rfl) ⟨78371, by rfl⟩ : syracuseStep 1671925 = 156743) (by norm_num)
theorem B1671961 : Blo 1486063 1671961 := bbase (se 2 (by rfl) ⟨626985, by rfl⟩ : syracuseStep 1671961 = 1253971) (by norm_num)
theorem B3572533 : Blo 1486063 3572533 := bbase (se 5 (by rfl) ⟨167462, by rfl⟩ : syracuseStep 3572533 = 334925) (by norm_num)
theorem B1671997 : Blo 1486063 1671997 := bbase (se 3 (by rfl) ⟨313499, by rfl⟩ : syracuseStep 1671997 = 626999) (by norm_num)
theorem B1672033 : Blo 1486063 1672033 := bbase (se 2 (by rfl) ⟨627012, by rfl⟩ : syracuseStep 1672033 = 1254025) (by norm_num)
theorem B3572581 : Blo 1486063 3572581 := bbase (se 4 (by rfl) ⟨334929, by rfl⟩ : syracuseStep 3572581 = 669859) (by norm_num)
theorem B2229101 : Blo 1486063 2229101 := bbase (se 3 (by rfl) ⟨417956, by rfl⟩ : syracuseStep 2229101 = 835913) (by norm_num)
theorem B1696621 : Blo 1486063 1696621 := bbase (se 3 (by rfl) ⟨318116, by rfl⟩ : syracuseStep 1696621 = 636233) (by norm_num)
theorem B2229125 : Blo 1486063 2229125 := bbase (se 4 (by rfl) ⟨208980, by rfl⟩ : syracuseStep 2229125 = 417961) (by norm_num)
theorem B1672069 : Blo 1486063 1672069 := bbase (se 4 (by rfl) ⟨156756, by rfl⟩ : syracuseStep 1672069 = 313513) (by norm_num)
theorem B2229149 : Blo 1486063 2229149 := bbase (se 3 (by rfl) ⟨417965, by rfl⟩ : syracuseStep 2229149 = 835931) (by norm_num)
theorem B1672105 : Blo 1486063 1672105 := bbase (se 2 (by rfl) ⟨627039, by rfl⟩ : syracuseStep 1672105 = 1254079) (by norm_num)
theorem B2679725 : Blo 1486063 2679725 := bbase (se 3 (by rfl) ⟨502448, by rfl⟩ : syracuseStep 2679725 = 1004897) (by norm_num)
theorem B2229173 : Blo 1486063 2229173 := bbase (se 5 (by rfl) ⟨104492, by rfl⟩ : syracuseStep 2229173 = 208985) (by norm_num)
theorem B2229197 : Blo 1486063 2229197 := bbase (se 3 (by rfl) ⟨417974, by rfl⟩ : syracuseStep 2229197 = 835949) (by norm_num)
theorem B1672141 : Blo 1486063 1672141 := bbase (se 3 (by rfl) ⟨313526, by rfl⟩ : syracuseStep 1672141 = 627053) (by norm_num)
theorem B1811417 : Blo 1486063 1811417 := bbase (se 2 (by rfl) ⟨679281, by rfl⟩ : syracuseStep 1811417 = 1358563) (by norm_num)
theorem B2229221 : Blo 1486063 2229221 := bbase (se 4 (by rfl) ⟨208989, by rfl⟩ : syracuseStep 2229221 = 417979) (by norm_num)
theorem B5645285 : Blo 1486063 5645285 := bbase (se 4 (by rfl) ⟨529245, by rfl⟩ : syracuseStep 5645285 = 1058491) (by norm_num)
theorem B1672177 : Blo 1486063 1672177 := bbase (se 2 (by rfl) ⟨627066, by rfl⟩ : syracuseStep 1672177 = 1254133) (by norm_num)
theorem B2507773 : Blo 1486063 2507773 := bbase (se 3 (by rfl) ⟨470207, by rfl⟩ : syracuseStep 2507773 = 940415) (by norm_num)
theorem B2229245 : Blo 1486063 2229245 := bbase (se 3 (by rfl) ⟨417983, by rfl⟩ : syracuseStep 2229245 = 835967) (by norm_num)
theorem B2229269 : Blo 1486063 2229269 := bbase (se 6 (by rfl) ⟨52248, by rfl⟩ : syracuseStep 2229269 = 104497) (by norm_num)
theorem B1672213 : Blo 1486063 1672213 := bbase (se 6 (by rfl) ⟨39192, by rfl⟩ : syracuseStep 1672213 = 78385) (by norm_num)
theorem B7144469 : Blo 1486063 7144469 := bbase (se 6 (by rfl) ⟨167448, by rfl⟩ : syracuseStep 7144469 = 334897) (by norm_num)
theorem B8471573 : Blo 1486063 8471573 := bbase (se 6 (by rfl) ⟨198552, by rfl⟩ : syracuseStep 8471573 = 397105) (by norm_num)
theorem B2229293 : Blo 1486063 2229293 := bbase (se 3 (by rfl) ⟨417992, by rfl⟩ : syracuseStep 2229293 = 835985) (by norm_num)
theorem B1672249 : Blo 1486063 1672249 := bbase (se 2 (by rfl) ⟨627093, by rfl⟩ : syracuseStep 1672249 = 1254187) (by norm_num)
theorem B2229317 : Blo 1486063 2229317 := bbase (se 4 (by rfl) ⟨208998, by rfl⟩ : syracuseStep 2229317 = 417997) (by norm_num)
theorem B2507861 : Blo 1486063 2507861 := bbase (se 8 (by rfl) ⟨14694, by rfl⟩ : syracuseStep 2507861 = 29389) (by norm_num)
theorem B2229341 : Blo 1486063 2229341 := bbase (se 3 (by rfl) ⟨418001, by rfl⟩ : syracuseStep 2229341 = 836003) (by norm_num)
theorem B1672285 : Blo 1486063 1672285 := bbase (se 3 (by rfl) ⟨313553, by rfl⟩ : syracuseStep 1672285 = 627107) (by norm_num)
theorem B2229365 : Blo 1486063 2229365 := bbase (se 5 (by rfl) ⟨104501, by rfl⟩ : syracuseStep 2229365 = 209003) (by norm_num)
theorem B1672321 : Blo 1486063 1672321 := bbase (se 2 (by rfl) ⟨627120, by rfl⟩ : syracuseStep 1672321 = 1254241) (by norm_num)
theorem B2679941 : Blo 1486063 2679941 := bbase (se 4 (by rfl) ⟨251244, by rfl⟩ : syracuseStep 2679941 = 502489) (by norm_num)
theorem B2229389 : Blo 1486063 2229389 := bbase (se 3 (by rfl) ⟨418010, by rfl⟩ : syracuseStep 2229389 = 836021) (by norm_num)
theorem B2229413 : Blo 1486063 2229413 := bbase (se 4 (by rfl) ⟨209007, by rfl⟩ : syracuseStep 2229413 = 418015) (by norm_num)
theorem B1672357 : Blo 1486063 1672357 := bbase (se 4 (by rfl) ⟨156783, by rfl⟩ : syracuseStep 1672357 = 313567) (by norm_num)
theorem B2229437 : Blo 1486063 2229437 := bbase (se 3 (by rfl) ⟨418019, by rfl⟩ : syracuseStep 2229437 = 836039) (by norm_num)
theorem B1672393 : Blo 1486063 1672393 := bbase (se 2 (by rfl) ⟨627147, by rfl⟩ : syracuseStep 1672393 = 1254295) (by norm_num)
theorem B2507989 : Blo 1486063 2507989 := bbase (se 7 (by rfl) ⟨29390, by rfl⟩ : syracuseStep 2507989 = 58781) (by norm_num)
theorem B2229461 : Blo 1486063 2229461 := bbase (se 7 (by rfl) ⟨26126, by rfl⟩ : syracuseStep 2229461 = 52253) (by norm_num)
theorem B32146645 : Blo 1486063 32146645 := bbase (se 7 (by rfl) ⟨376718, by rfl⟩ : syracuseStep 32146645 = 753437) (by norm_num)
theorem B2229485 : Blo 1486063 2229485 := bbase (se 3 (by rfl) ⟨418028, by rfl⟩ : syracuseStep 2229485 = 836057) (by norm_num)
theorem B1672429 : Blo 1486063 1672429 := bbase (se 3 (by rfl) ⟨313580, by rfl⟩ : syracuseStep 1672429 = 627161) (by norm_num)
theorem B2229509 : Blo 1486063 2229509 := bbase (se 4 (by rfl) ⟨209016, by rfl⟩ : syracuseStep 2229509 = 418033) (by norm_num)
theorem B1672465 : Blo 1486063 1672465 := bbase (se 2 (by rfl) ⟨627174, by rfl⟩ : syracuseStep 1672465 = 1254349) (by norm_num)
theorem B2229533 : Blo 1486063 2229533 := bbase (se 3 (by rfl) ⟨418037, by rfl⟩ : syracuseStep 2229533 = 836075) (by norm_num)
theorem B3343661 : Blo 1486063 3343661 := bbase (se 3 (by rfl) ⟨626936, by rfl⟩ : syracuseStep 3343661 = 1253873) (by norm_num)
theorem B2508077 : Blo 1486063 2508077 := bbase (se 3 (by rfl) ⟨470264, by rfl⟩ : syracuseStep 2508077 = 940529) (by norm_num)
theorem B2229557 : Blo 1486063 2229557 := bbase (se 5 (by rfl) ⟨104510, by rfl⟩ : syracuseStep 2229557 = 209021) (by norm_num)
theorem B1672501 : Blo 1486063 1672501 := bbase (se 5 (by rfl) ⟨78398, by rfl⟩ : syracuseStep 1672501 = 156797) (by norm_num)
theorem B1787189 : Blo 1486063 1787189 := bbase (se 5 (by rfl) ⟨83774, by rfl⟩ : syracuseStep 1787189 = 167549) (by norm_num)
theorem B2229581 : Blo 1486063 2229581 := bbase (se 3 (by rfl) ⟨418046, by rfl⟩ : syracuseStep 2229581 = 836093) (by norm_num)
theorem B1672537 : Blo 1486063 1672537 := bbase (se 2 (by rfl) ⟨627201, by rfl⟩ : syracuseStep 1672537 = 1254403) (by norm_num)
theorem B2229605 : Blo 1486063 2229605 := bbase (se 4 (by rfl) ⟨209025, by rfl⟩ : syracuseStep 2229605 = 418051) (by norm_num)
theorem B3343733 : Blo 1486063 3343733 := bbase (se 5 (by rfl) ⟨156737, by rfl⟩ : syracuseStep 3343733 = 313475) (by norm_num)
theorem B2229629 : Blo 1486063 2229629 := bbase (se 3 (by rfl) ⟨418055, by rfl⟩ : syracuseStep 2229629 = 836111) (by norm_num)
theorem B1672573 : Blo 1486063 1672573 := bbase (se 3 (by rfl) ⟨313607, by rfl⟩ : syracuseStep 1672573 = 627215) (by norm_num)
theorem B1860989 : Blo 1486063 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B4760981 : Blo 1486063 4760981 := bbase (se 6 (by rfl) ⟨111585, by rfl⟩ : syracuseStep 4760981 = 223171) (by norm_num)
theorem B2229653 : Blo 1486063 2229653 := bbase (se 6 (by rfl) ⟨52257, by rfl⟩ : syracuseStep 2229653 = 104515) (by norm_num)
theorem B1672609 : Blo 1486063 1672609 := bbase (se 2 (by rfl) ⟨627228, by rfl⟩ : syracuseStep 1672609 = 1254457) (by norm_num)
theorem B2680229 : Blo 1486063 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B2508205 : Blo 1486063 2508205 := bbase (se 3 (by rfl) ⟨470288, by rfl⟩ : syracuseStep 2508205 = 940577) (by norm_num)
theorem B2229677 : Blo 1486063 2229677 := bbase (se 3 (by rfl) ⟨418064, by rfl⟩ : syracuseStep 2229677 = 836129) (by norm_num)
theorem B3343805 : Blo 1486063 3343805 := bbase (se 3 (by rfl) ⟨626963, by rfl⟩ : syracuseStep 3343805 = 1253927) (by norm_num)
theorem B2229701 : Blo 1486063 2229701 := bbase (se 4 (by rfl) ⟨209034, by rfl⟩ : syracuseStep 2229701 = 418069) (by norm_num)
theorem B1672645 : Blo 1486063 1672645 := bbase (se 4 (by rfl) ⟨156810, by rfl⟩ : syracuseStep 1672645 = 313621) (by norm_num)
theorem B3573197 : Blo 1486063 3573197 := bbase (se 3 (by rfl) ⟨669974, by rfl⟩ : syracuseStep 3573197 = 1339949) (by norm_num)
theorem B2229725 : Blo 1486063 2229725 := bbase (se 3 (by rfl) ⟨418073, by rfl⟩ : syracuseStep 2229725 = 836147) (by norm_num)
theorem B1672681 : Blo 1486063 1672681 := bbase (se 2 (by rfl) ⟨627255, by rfl⟩ : syracuseStep 1672681 = 1254511) (by norm_num)
theorem B2229749 : Blo 1486063 2229749 := bbase (se 5 (by rfl) ⟨104519, by rfl⟩ : syracuseStep 2229749 = 209039) (by norm_num)
theorem B3343877 : Blo 1486063 3343877 := bbase (se 4 (by rfl) ⟨313488, by rfl⟩ : syracuseStep 3343877 = 626977) (by norm_num)
theorem B2508293 : Blo 1486063 2508293 := bbase (se 4 (by rfl) ⟨235152, by rfl⟩ : syracuseStep 2508293 = 470305) (by norm_num)
theorem B2229773 : Blo 1486063 2229773 := bbase (se 3 (by rfl) ⟨418082, by rfl⟩ : syracuseStep 2229773 = 836165) (by norm_num)
theorem B1672717 : Blo 1486063 1672717 := bbase (se 3 (by rfl) ⟨313634, by rfl⟩ : syracuseStep 1672717 = 627269) (by norm_num)
theorem B2229797 : Blo 1486063 2229797 := bbase (se 4 (by rfl) ⟨209043, by rfl⟩ : syracuseStep 2229797 = 418087) (by norm_num)
theorem B1672753 : Blo 1486063 1672753 := bbase (se 2 (by rfl) ⟨627282, by rfl⟩ : syracuseStep 1672753 = 1254565) (by norm_num)
theorem B2229821 : Blo 1486063 2229821 := bbase (se 3 (by rfl) ⟨418091, by rfl⟩ : syracuseStep 2229821 = 836183) (by norm_num)
theorem B3761741 : Blo 1486063 3761741 := bbase (se 3 (by rfl) ⟨705326, by rfl⟩ : syracuseStep 3761741 = 1410653) (by norm_num)
theorem B3343949 : Blo 1486063 3343949 := bbase (se 3 (by rfl) ⟨626990, by rfl⟩ : syracuseStep 3343949 = 1253981) (by norm_num)
theorem B2229845 : Blo 1486063 2229845 := bbase (se 8 (by rfl) ⟨13065, by rfl⟩ : syracuseStep 2229845 = 26131) (by norm_num)
theorem B1672789 : Blo 1486063 1672789 := bbase (se 8 (by rfl) ⟨9801, by rfl⟩ : syracuseStep 1672789 = 19603) (by norm_num)
theorem B2229869 : Blo 1486063 2229869 := bbase (se 3 (by rfl) ⟨418100, by rfl⟩ : syracuseStep 2229869 = 836201) (by norm_num)
theorem B1672825 : Blo 1486063 1672825 := bbase (se 2 (by rfl) ⟨627309, by rfl⟩ : syracuseStep 1672825 = 1254619) (by norm_num)
theorem B1787521 : Blo 1486063 1787521 := bbase (se 2 (by rfl) ⟨670320, by rfl⟩ : syracuseStep 1787521 = 1340641) (by norm_num)
theorem B2508421 : Blo 1486063 2508421 := bbase (se 4 (by rfl) ⟨235164, by rfl⟩ : syracuseStep 2508421 = 470329) (by norm_num)
theorem B2229893 : Blo 1486063 2229893 := bbase (se 4 (by rfl) ⟨209052, by rfl⟩ : syracuseStep 2229893 = 418105) (by norm_num)
theorem B3344021 : Blo 1486063 3344021 := bbase (se 6 (by rfl) ⟨78375, by rfl⟩ : syracuseStep 3344021 = 156751) (by norm_num)
theorem B2008733 : Blo 1486063 2008733 := bbase (se 3 (by rfl) ⟨376637, by rfl⟩ : syracuseStep 2008733 = 753275) (by norm_num)
theorem B2229917 : Blo 1486063 2229917 := bbase (se 3 (by rfl) ⟨418109, by rfl⟩ : syracuseStep 2229917 = 836219) (by norm_num)
theorem B1672861 : Blo 1486063 1672861 := bbase (se 3 (by rfl) ⟨313661, by rfl⟩ : syracuseStep 1672861 = 627323) (by norm_num)
theorem B6350501 : Blo 1486063 6350501 := bbase (se 4 (by rfl) ⟨595359, by rfl⟩ : syracuseStep 6350501 = 1190719) (by norm_num)
theorem B6874789 : Blo 1486063 6874789 := bbase (se 4 (by rfl) ⟨644511, by rfl⟩ : syracuseStep 6874789 = 1289023) (by norm_num)
theorem B2229941 : Blo 1486063 2229941 := bbase (se 5 (by rfl) ⟨104528, by rfl⟩ : syracuseStep 2229941 = 209057) (by norm_num)
theorem B1672897 : Blo 1486063 1672897 := bbase (se 2 (by rfl) ⟨627336, by rfl⟩ : syracuseStep 1672897 = 1254673) (by norm_num)
theorem B2229965 : Blo 1486063 2229965 := bbase (se 3 (by rfl) ⟨418118, by rfl⟩ : syracuseStep 2229965 = 836237) (by norm_num)
theorem B3344093 : Blo 1486063 3344093 := bbase (se 3 (by rfl) ⟨627017, by rfl⟩ : syracuseStep 3344093 = 1254035) (by norm_num)
theorem B2508509 : Blo 1486063 2508509 := bbase (se 3 (by rfl) ⟨470345, by rfl⟩ : syracuseStep 2508509 = 940691) (by norm_num)
theorem B2229989 : Blo 1486063 2229989 := bbase (se 4 (by rfl) ⟨209061, by rfl⟩ : syracuseStep 2229989 = 418123) (by norm_num)
theorem B1672933 : Blo 1486063 1672933 := bbase (se 4 (by rfl) ⟨156837, by rfl⟩ : syracuseStep 1672933 = 313675) (by norm_num)
theorem B2230013 : Blo 1486063 2230013 := bbase (se 3 (by rfl) ⟨418127, by rfl⟩ : syracuseStep 2230013 = 836255) (by norm_num)
theorem B7530245 : Blo 1486063 7530245 := bbase (se 4 (by rfl) ⟨705960, by rfl⟩ : syracuseStep 7530245 = 1411921) (by norm_num)
theorem B1672969 : Blo 1486063 1672969 := bbase (se 2 (by rfl) ⟨627363, by rfl⟩ : syracuseStep 1672969 = 1254727) (by norm_num)
theorem B1787665 : Blo 1486063 1787665 := bbase (se 2 (by rfl) ⟨670374, by rfl⟩ : syracuseStep 1787665 = 1340749) (by norm_num)
theorem B2230037 : Blo 1486063 2230037 := bbase (se 6 (by rfl) ⟨52266, by rfl⟩ : syracuseStep 2230037 = 104533) (by norm_num)
theorem B3344165 : Blo 1486063 3344165 := bbase (se 4 (by rfl) ⟨313515, by rfl⟩ : syracuseStep 3344165 = 627031) (by norm_num)
theorem B3573541 : Blo 1486063 3573541 := bbase (se 4 (by rfl) ⟨335019, by rfl⟩ : syracuseStep 3573541 = 670039) (by norm_num)
theorem B2230061 : Blo 1486063 2230061 := bbase (se 3 (by rfl) ⟨418136, by rfl⟩ : syracuseStep 2230061 = 836273) (by norm_num)
theorem B1673005 : Blo 1486063 1673005 := bbase (se 3 (by rfl) ⟨313688, by rfl⟩ : syracuseStep 1673005 = 627377) (by norm_num)
theorem B2008885 : Blo 1486063 2008885 := bbase (se 5 (by rfl) ⟨94166, by rfl⟩ : syracuseStep 2008885 = 188333) (by norm_num)
theorem B2230085 : Blo 1486063 2230085 := bbase (se 4 (by rfl) ⟨209070, by rfl⟩ : syracuseStep 2230085 = 418141) (by norm_num)
theorem B1673041 : Blo 1486063 1673041 := bbase (se 2 (by rfl) ⟨627390, by rfl⟩ : syracuseStep 1673041 = 1254781) (by norm_num)
theorem B2508637 : Blo 1486063 2508637 := bbase (se 3 (by rfl) ⟨470369, by rfl⟩ : syracuseStep 2508637 = 940739) (by norm_num)
theorem B2230109 : Blo 1486063 2230109 := bbase (se 3 (by rfl) ⟨418145, by rfl⟩ : syracuseStep 2230109 = 836291) (by norm_num)
theorem B3344237 : Blo 1486063 3344237 := bbase (se 3 (by rfl) ⟨627044, by rfl⟩ : syracuseStep 3344237 = 1254089) (by norm_num)
theorem B2230133 : Blo 1486063 2230133 := bbase (se 5 (by rfl) ⟨104537, by rfl⟩ : syracuseStep 2230133 = 209075) (by norm_num)
theorem B1673077 : Blo 1486063 1673077 := bbase (se 5 (by rfl) ⟨78425, by rfl⟩ : syracuseStep 1673077 = 156851) (by norm_num)
theorem B2230157 : Blo 1486063 2230157 := bbase (se 3 (by rfl) ⟨418154, by rfl⟩ : syracuseStep 2230157 = 836309) (by norm_num)
theorem B1673113 : Blo 1486063 1673113 := bbase (se 2 (by rfl) ⟨627417, by rfl⟩ : syracuseStep 1673113 = 1254835) (by norm_num)
theorem B3762085 : Blo 1486063 3762085 := bbase (se 4 (by rfl) ⟨352695, by rfl⟩ : syracuseStep 3762085 = 705391) (by norm_num)
theorem B2230181 : Blo 1486063 2230181 := bbase (se 4 (by rfl) ⟨209079, by rfl⟩ : syracuseStep 2230181 = 418159) (by norm_num)
theorem B3344309 : Blo 1486063 3344309 := bbase (se 5 (by rfl) ⟨156764, by rfl⟩ : syracuseStep 3344309 = 313529) (by norm_num)
theorem B2508725 : Blo 1486063 2508725 := bbase (se 5 (by rfl) ⟨117596, by rfl⟩ : syracuseStep 2508725 = 235193) (by norm_num)
theorem B2230205 : Blo 1486063 2230205 := bbase (se 3 (by rfl) ⟨418163, by rfl⟩ : syracuseStep 2230205 = 836327) (by norm_num)
theorem B1673149 : Blo 1486063 1673149 := bbase (se 3 (by rfl) ⟨313715, by rfl⟩ : syracuseStep 1673149 = 627431) (by norm_num)
theorem B2230229 : Blo 1486063 2230229 := bbase (se 7 (by rfl) ⟨26135, by rfl⟩ : syracuseStep 2230229 = 52271) (by norm_num)
theorem B1673185 : Blo 1486063 1673185 := bbase (se 2 (by rfl) ⟨627444, by rfl⟩ : syracuseStep 1673185 = 1254889) (by norm_num)
theorem B2230253 : Blo 1486063 2230253 := bbase (se 3 (by rfl) ⟨418172, by rfl⟩ : syracuseStep 2230253 = 836345) (by norm_num)
theorem B3344381 : Blo 1486063 3344381 := bbase (se 3 (by rfl) ⟨627071, by rfl⟩ : syracuseStep 3344381 = 1254143) (by norm_num)
theorem B2230277 : Blo 1486063 2230277 := bbase (se 4 (by rfl) ⟨209088, by rfl⟩ : syracuseStep 2230277 = 418177) (by norm_num)
theorem B1673221 : Blo 1486063 1673221 := bbase (se 4 (by rfl) ⟨156864, by rfl⟩ : syracuseStep 1673221 = 313729) (by norm_num)
theorem B3573773 : Blo 1486063 3573773 := bbase (se 3 (by rfl) ⟨670082, by rfl⟩ : syracuseStep 3573773 = 1340165) (by norm_num)
theorem B5015573 : Blo 1486063 5015573 := bbase (se 6 (by rfl) ⟨117552, by rfl⟩ : syracuseStep 5015573 = 235105) (by norm_num)
theorem B3762197 : Blo 1486063 3762197 := bbase (se 6 (by rfl) ⟨88176, by rfl⟩ : syracuseStep 3762197 = 176353) (by norm_num)
theorem B2230301 : Blo 1486063 2230301 := bbase (se 3 (by rfl) ⟨418181, by rfl⟩ : syracuseStep 2230301 = 836363) (by norm_num)
theorem B1673257 : Blo 1486063 1673257 := bbase (se 2 (by rfl) ⟨627471, by rfl⟩ : syracuseStep 1673257 = 1254943) (by norm_num)
theorem B2508853 : Blo 1486063 2508853 := bbase (se 5 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 2508853 = 235205) (by norm_num)
theorem B2230325 : Blo 1486063 2230325 := bbase (se 5 (by rfl) ⟨104546, by rfl⟩ : syracuseStep 2230325 = 209093) (by norm_num)
theorem B3344453 : Blo 1486063 3344453 := bbase (se 4 (by rfl) ⟨313542, by rfl⟩ : syracuseStep 3344453 = 627085) (by norm_num)
theorem B2230349 : Blo 1486063 2230349 := bbase (se 3 (by rfl) ⟨418190, by rfl⟩ : syracuseStep 2230349 = 836381) (by norm_num)
theorem B1673293 : Blo 1486063 1673293 := bbase (se 3 (by rfl) ⟨313742, by rfl⟩ : syracuseStep 1673293 = 627485) (by norm_num)
theorem B2230373 : Blo 1486063 2230373 := bbase (se 4 (by rfl) ⟨209097, by rfl⟩ : syracuseStep 2230373 = 418195) (by norm_num)
theorem B1673329 : Blo 1486063 1673329 := bbase (se 2 (by rfl) ⟨627498, by rfl⟩ : syracuseStep 1673329 = 1254997) (by norm_num)
theorem B2230397 : Blo 1486063 2230397 := bbase (se 3 (by rfl) ⟨418199, by rfl⟩ : syracuseStep 2230397 = 836399) (by norm_num)
theorem B5646469 : Blo 1486063 5646469 := bbase (se 4 (by rfl) ⟨529356, by rfl⟩ : syracuseStep 5646469 = 1058713) (by norm_num)
theorem B3344525 : Blo 1486063 3344525 := bbase (se 3 (by rfl) ⟨627098, by rfl⟩ : syracuseStep 3344525 = 1254197) (by norm_num)
theorem B2508941 : Blo 1486063 2508941 := bbase (se 3 (by rfl) ⟨470426, by rfl⟩ : syracuseStep 2508941 = 940853) (by norm_num)
theorem B4761749 : Blo 1486063 4761749 := bbase (se 6 (by rfl) ⟨111603, by rfl⟩ : syracuseStep 4761749 = 223207) (by norm_num)
theorem B2230421 : Blo 1486063 2230421 := bbase (se 6 (by rfl) ⟨52275, by rfl⟩ : syracuseStep 2230421 = 104551) (by norm_num)
theorem B1673365 : Blo 1486063 1673365 := bbase (se 6 (by rfl) ⟨39219, by rfl⟩ : syracuseStep 1673365 = 78439) (by norm_num)
theorem B2230445 : Blo 1486063 2230445 := bbase (se 3 (by rfl) ⟨418208, by rfl⟩ : syracuseStep 2230445 = 836417) (by norm_num)
theorem B1673401 : Blo 1486063 1673401 := bbase (se 2 (by rfl) ⟨627525, by rfl⟩ : syracuseStep 1673401 = 1255051) (by norm_num)
theorem B2230469 : Blo 1486063 2230469 := bbase (se 4 (by rfl) ⟨209106, by rfl⟩ : syracuseStep 2230469 = 418213) (by norm_num)
theorem B3573965 : Blo 1486063 3573965 := bbase (se 3 (by rfl) ⟨670118, by rfl⟩ : syracuseStep 3573965 = 1340237) (by norm_num)
theorem B3762389 : Blo 1486063 3762389 := bbase (se 7 (by rfl) ⟨44090, by rfl⟩ : syracuseStep 3762389 = 88181) (by norm_num)
theorem B3344597 : Blo 1486063 3344597 := bbase (se 7 (by rfl) ⟨39194, by rfl⟩ : syracuseStep 3344597 = 78389) (by norm_num)
theorem B2230493 : Blo 1486063 2230493 := bbase (se 3 (by rfl) ⟨418217, by rfl⟩ : syracuseStep 2230493 = 836435) (by norm_num)
theorem B1673437 : Blo 1486063 1673437 := bbase (se 3 (by rfl) ⟨313769, by rfl⟩ : syracuseStep 1673437 = 627539) (by norm_num)
theorem B2230517 : Blo 1486063 2230517 := bbase (se 5 (by rfl) ⟨104555, by rfl⟩ : syracuseStep 2230517 = 209111) (by norm_num)
theorem B1673473 : Blo 1486063 1673473 := bbase (se 2 (by rfl) ⟨627552, by rfl⟩ : syracuseStep 1673473 = 1255105) (by norm_num)
theorem B2509069 : Blo 1486063 2509069 := bbase (se 3 (by rfl) ⟨470450, by rfl⟩ : syracuseStep 2509069 = 940901) (by norm_num)
theorem B2230541 : Blo 1486063 2230541 := bbase (se 3 (by rfl) ⟨418226, by rfl⟩ : syracuseStep 2230541 = 836453) (by norm_num)
theorem B3344669 : Blo 1486063 3344669 := bbase (se 3 (by rfl) ⟨627125, by rfl⟩ : syracuseStep 3344669 = 1254251) (by norm_num)
theorem B2230565 : Blo 1486063 2230565 := bbase (se 4 (by rfl) ⟨209115, by rfl⟩ : syracuseStep 2230565 = 418231) (by norm_num)
theorem B1673509 : Blo 1486063 1673509 := bbase (se 4 (by rfl) ⟨156891, by rfl⟩ : syracuseStep 1673509 = 313783) (by norm_num)
theorem B2230589 : Blo 1486063 2230589 := bbase (se 3 (by rfl) ⟨418235, by rfl⟩ : syracuseStep 2230589 = 836471) (by norm_num)
theorem B1673545 : Blo 1486063 1673545 := bbase (se 2 (by rfl) ⟨627579, by rfl⟩ : syracuseStep 1673545 = 1255159) (by norm_num)
theorem B2230613 : Blo 1486063 2230613 := bbase (se 10 (by rfl) ⟨3267, by rfl⟩ : syracuseStep 2230613 = 6535) (by norm_num)
theorem B3344741 : Blo 1486063 3344741 := bbase (se 4 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 3344741 = 627139) (by norm_num)
theorem B2509157 : Blo 1486063 2509157 := bbase (se 4 (by rfl) ⟨235233, by rfl⟩ : syracuseStep 2509157 = 470467) (by norm_num)
theorem B2230637 : Blo 1486063 2230637 := bbase (se 3 (by rfl) ⟨418244, by rfl⟩ : syracuseStep 2230637 = 836489) (by norm_num)
theorem B1673581 : Blo 1486063 1673581 := bbase (se 3 (by rfl) ⟨313796, by rfl⟩ : syracuseStep 1673581 = 627593) (by norm_num)
theorem B2230661 : Blo 1486063 2230661 := bbase (se 4 (by rfl) ⟨209124, by rfl⟩ : syracuseStep 2230661 = 418249) (by norm_num)
theorem B1673617 : Blo 1486063 1673617 := bbase (se 2 (by rfl) ⟨627606, by rfl⟩ : syracuseStep 1673617 = 1255213) (by norm_num)
theorem B2230685 : Blo 1486063 2230685 := bbase (se 3 (by rfl) ⟨418253, by rfl⟩ : syracuseStep 2230685 = 836507) (by norm_num)
theorem B2681245 : Blo 1486063 2681245 := bbase (se 3 (by rfl) ⟨502733, by rfl⟩ : syracuseStep 2681245 = 1005467) (by norm_num)
theorem B3344813 : Blo 1486063 3344813 := bbase (se 3 (by rfl) ⟨627152, by rfl⟩ : syracuseStep 3344813 = 1254305) (by norm_num)
theorem B2230709 : Blo 1486063 2230709 := bbase (se 5 (by rfl) ⟨104564, by rfl⟩ : syracuseStep 2230709 = 209129) (by norm_num)
theorem B5646773 : Blo 1486063 5646773 := bbase (se 5 (by rfl) ⟨264692, by rfl⟩ : syracuseStep 5646773 = 529385) (by norm_num)
theorem B1673653 : Blo 1486063 1673653 := bbase (se 5 (by rfl) ⟨78452, by rfl⟩ : syracuseStep 1673653 = 156905) (by norm_num)
theorem B5016005 : Blo 1486063 5016005 := bbase (se 4 (by rfl) ⟨470250, by rfl⟩ : syracuseStep 5016005 = 940501) (by norm_num)
theorem B2230733 : Blo 1486063 2230733 := bbase (se 3 (by rfl) ⟨418262, by rfl⟩ : syracuseStep 2230733 = 836525) (by norm_num)
theorem B11446741 : Blo 1486063 11446741 := bbase (se 7 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 11446741 = 268283) (by norm_num)
theorem B1673689 : Blo 1486063 1673689 := bbase (se 2 (by rfl) ⟨627633, by rfl⟩ : syracuseStep 1673689 = 1255267) (by norm_num)
theorem B2509285 : Blo 1486063 2509285 := bbase (se 4 (by rfl) ⟨235245, by rfl⟩ : syracuseStep 2509285 = 470491) (by norm_num)
theorem B2230757 : Blo 1486063 2230757 := bbase (se 4 (by rfl) ⟨209133, by rfl⟩ : syracuseStep 2230757 = 418267) (by norm_num)
theorem B3574253 : Blo 1486063 3574253 := bbase (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) (by norm_num)
theorem B3344885 : Blo 1486063 3344885 := bbase (se 5 (by rfl) ⟨156791, by rfl⟩ : syracuseStep 3344885 = 313583) (by norm_num)
theorem B2230781 : Blo 1486063 2230781 := bbase (se 3 (by rfl) ⟨418271, by rfl⟩ : syracuseStep 2230781 = 836543) (by norm_num)
theorem B1673725 : Blo 1486063 1673725 := bbase (se 3 (by rfl) ⟨313823, by rfl⟩ : syracuseStep 1673725 = 627647) (by norm_num)
theorem B2542085 : Blo 1486063 2542085 := bbase (se 4 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 2542085 = 476641) (by norm_num)
theorem B2230805 : Blo 1486063 2230805 := bbase (se 6 (by rfl) ⟨52284, by rfl⟩ : syracuseStep 2230805 = 104569) (by norm_num)
theorem B1673761 : Blo 1486063 1673761 := bbase (se 2 (by rfl) ⟨627660, by rfl⟩ : syracuseStep 1673761 = 1255321) (by norm_num)
theorem B3762733 : Blo 1486063 3762733 := bbase (se 3 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 3762733 = 1411025) (by norm_num)
theorem B2230829 : Blo 1486063 2230829 := bbase (se 3 (by rfl) ⟨418280, by rfl⟩ : syracuseStep 2230829 = 836561) (by norm_num)
theorem B3344957 : Blo 1486063 3344957 := bbase (se 3 (by rfl) ⟨627179, by rfl⟩ : syracuseStep 3344957 = 1254359) (by norm_num)
theorem B2509373 : Blo 1486063 2509373 := bbase (se 3 (by rfl) ⟨470507, by rfl⟩ : syracuseStep 2509373 = 941015) (by norm_num)
theorem B2230853 : Blo 1486063 2230853 := bbase (se 4 (by rfl) ⟨209142, by rfl⟩ : syracuseStep 2230853 = 418285) (by norm_num)
theorem B5360197 : Blo 1486063 5360197 := bbase (se 4 (by rfl) ⟨502518, by rfl⟩ : syracuseStep 5360197 = 1005037) (by norm_num)
theorem B1673797 : Blo 1486063 1673797 := bbase (se 4 (by rfl) ⟨156918, by rfl⟩ : syracuseStep 1673797 = 313837) (by norm_num)
theorem B2230877 : Blo 1486063 2230877 := bbase (se 3 (by rfl) ⟨418289, by rfl⟩ : syracuseStep 2230877 = 836579) (by norm_num)
theorem B1673833 : Blo 1486063 1673833 := bbase (se 2 (by rfl) ⟨627687, by rfl⟩ : syracuseStep 1673833 = 1255375) (by norm_num)
theorem B2230901 : Blo 1486063 2230901 := bbase (se 5 (by rfl) ⟨104573, by rfl⟩ : syracuseStep 2230901 = 209147) (by norm_num)
theorem B3345029 : Blo 1486063 3345029 := bbase (se 4 (by rfl) ⟨313596, by rfl⟩ : syracuseStep 3345029 = 627193) (by norm_num)
theorem B6351493 : Blo 1486063 6351493 := bbase (se 4 (by rfl) ⟨595452, by rfl⟩ : syracuseStep 6351493 = 1190905) (by norm_num)
theorem B2230925 : Blo 1486063 2230925 := bbase (se 3 (by rfl) ⟨418298, by rfl⟩ : syracuseStep 2230925 = 836597) (by norm_num)
theorem B1673869 : Blo 1486063 1673869 := bbase (se 3 (by rfl) ⟨313850, by rfl⟩ : syracuseStep 1673869 = 627701) (by norm_num)
theorem B4762261 : Blo 1486063 4762261 := bbase (se 6 (by rfl) ⟨111615, by rfl⟩ : syracuseStep 4762261 = 223231) (by norm_num)
theorem B2116253 : Blo 1486063 2116253 := bbase (se 3 (by rfl) ⟨396797, by rfl⟩ : syracuseStep 2116253 = 793595) (by norm_num)
theorem B3762845 : Blo 1486063 3762845 := bbase (se 3 (by rfl) ⟨705533, by rfl⟩ : syracuseStep 3762845 = 1411067) (by norm_num)
theorem B2230949 : Blo 1486063 2230949 := bbase (se 4 (by rfl) ⟨209151, by rfl⟩ : syracuseStep 2230949 = 418303) (by norm_num)
theorem B1673905 : Blo 1486063 1673905 := bbase (se 2 (by rfl) ⟨627714, by rfl⟩ : syracuseStep 1673905 = 1255429) (by norm_num)
theorem B2509501 : Blo 1486063 2509501 := bbase (se 3 (by rfl) ⟨470531, by rfl⟩ : syracuseStep 2509501 = 941063) (by norm_num)
theorem B2230973 : Blo 1486063 2230973 := bbase (se 3 (by rfl) ⟨418307, by rfl⟩ : syracuseStep 2230973 = 836615) (by norm_num)
theorem B3345101 : Blo 1486063 3345101 := bbase (se 3 (by rfl) ⟨627206, by rfl⟩ : syracuseStep 3345101 = 1254413) (by norm_num)
theorem B2230997 : Blo 1486063 2230997 := bbase (se 7 (by rfl) ⟨26144, by rfl⟩ : syracuseStep 2230997 = 52289) (by norm_num)
theorem B1673941 : Blo 1486063 1673941 := bbase (se 7 (by rfl) ⟨19616, by rfl⟩ : syracuseStep 1673941 = 39233) (by norm_num)
theorem B2231021 : Blo 1486063 2231021 := bbase (se 3 (by rfl) ⟨418316, by rfl⟩ : syracuseStep 2231021 = 836633) (by norm_num)
theorem B1673977 : Blo 1486063 1673977 := bbase (se 2 (by rfl) ⟨627741, by rfl⟩ : syracuseStep 1673977 = 1255483) (by norm_num)
theorem B2231045 : Blo 1486063 2231045 := bbase (se 4 (by rfl) ⟨209160, by rfl⟩ : syracuseStep 2231045 = 418321) (by norm_num)
theorem B3345173 : Blo 1486063 3345173 := bbase (se 6 (by rfl) ⟨78402, by rfl⟩ : syracuseStep 3345173 = 156805) (by norm_num)
theorem B2509589 : Blo 1486063 2509589 := bbase (se 6 (by rfl) ⟨58818, by rfl⟩ : syracuseStep 2509589 = 117637) (by norm_num)
theorem B2231069 : Blo 1486063 2231069 := bbase (se 3 (by rfl) ⟨418325, by rfl⟩ : syracuseStep 2231069 = 836651) (by norm_num)
theorem B1674013 : Blo 1486063 1674013 := bbase (se 3 (by rfl) ⟨313877, by rfl⟩ : syracuseStep 1674013 = 627755) (by norm_num)
theorem B2231093 : Blo 1486063 2231093 := bbase (se 5 (by rfl) ⟨104582, by rfl⟩ : syracuseStep 2231093 = 209165) (by norm_num)
theorem B1674049 : Blo 1486063 1674049 := bbase (se 2 (by rfl) ⟨627768, by rfl⟩ : syracuseStep 1674049 = 1255537) (by norm_num)
theorem B2231117 : Blo 1486063 2231117 := bbase (se 3 (by rfl) ⟨418334, by rfl⟩ : syracuseStep 2231117 = 836669) (by norm_num)
theorem B3763037 : Blo 1486063 3763037 := bbase (se 3 (by rfl) ⟨705569, by rfl⟩ : syracuseStep 3763037 = 1411139) (by norm_num)
theorem B3345245 : Blo 1486063 3345245 := bbase (se 3 (by rfl) ⟨627233, by rfl⟩ : syracuseStep 3345245 = 1254467) (by norm_num)
theorem B2231141 : Blo 1486063 2231141 := bbase (se 4 (by rfl) ⟨209169, by rfl⟩ : syracuseStep 2231141 = 418339) (by norm_num)
theorem B5016437 : Blo 1486063 5016437 := bbase (se 5 (by rfl) ⟨235145, by rfl⟩ : syracuseStep 5016437 = 470291) (by norm_num)
theorem B2231165 : Blo 1486063 2231165 := bbase (se 3 (by rfl) ⟨418343, by rfl⟩ : syracuseStep 2231165 = 836687) (by norm_num)
theorem B2509717 : Blo 1486063 2509717 := bbase (se 6 (by rfl) ⟨58821, by rfl⟩ : syracuseStep 2509717 = 117643) (by norm_num)
theorem B2231189 : Blo 1486063 2231189 := bbase (se 6 (by rfl) ⟨52293, by rfl⟩ : syracuseStep 2231189 = 104587) (by norm_num)
theorem B3345317 : Blo 1486063 3345317 := bbase (se 4 (by rfl) ⟨313623, by rfl⟩ : syracuseStep 3345317 = 627247) (by norm_num)
theorem B2231213 : Blo 1486063 2231213 := bbase (se 3 (by rfl) ⟨418352, by rfl⟩ : syracuseStep 2231213 = 836705) (by norm_num)
theorem B2231237 : Blo 1486063 2231237 := bbase (se 4 (by rfl) ⟨209178, by rfl⟩ : syracuseStep 2231237 = 418357) (by norm_num)
theorem B4303829 : Blo 1486063 4303829 := bbase (se 7 (by rfl) ⟨50435, by rfl⟩ : syracuseStep 4303829 = 100871) (by norm_num)
theorem B2231261 : Blo 1486063 2231261 := bbase (se 3 (by rfl) ⟨418361, by rfl⟩ : syracuseStep 2231261 = 836723) (by norm_num)
theorem B3345389 : Blo 1486063 3345389 := bbase (se 3 (by rfl) ⟨627260, by rfl⟩ : syracuseStep 3345389 = 1254521) (by norm_num)
theorem B2509805 : Blo 1486063 2509805 := bbase (se 3 (by rfl) ⟨470588, by rfl⟩ : syracuseStep 2509805 = 941177) (by norm_num)
theorem B2231285 : Blo 1486063 2231285 := bbase (se 5 (by rfl) ⟨104591, by rfl⟩ : syracuseStep 2231285 = 209183) (by norm_num)
theorem B2231309 : Blo 1486063 2231309 := bbase (se 3 (by rfl) ⟨418370, by rfl⟩ : syracuseStep 2231309 = 836741) (by norm_num)
theorem B7531541 : Blo 1486063 7531541 := bbase (se 6 (by rfl) ⟨176520, by rfl⟩ : syracuseStep 7531541 = 353041) (by norm_num)
theorem B2231333 : Blo 1486063 2231333 := bbase (se 4 (by rfl) ⟨209187, by rfl⟩ : syracuseStep 2231333 = 418375) (by norm_num)
theorem B3345461 : Blo 1486063 3345461 := bbase (se 5 (by rfl) ⟨156818, by rfl⟩ : syracuseStep 3345461 = 313637) (by norm_num)
theorem B2231357 : Blo 1486063 2231357 := bbase (se 3 (by rfl) ⟨418379, by rfl⟩ : syracuseStep 2231357 = 836759) (by norm_num)
theorem B2231381 : Blo 1486063 2231381 := bbase (se 8 (by rfl) ⟨13074, by rfl⟩ : syracuseStep 2231381 = 26149) (by norm_num)
theorem B2509933 : Blo 1486063 2509933 := bbase (se 3 (by rfl) ⟨470612, by rfl⟩ : syracuseStep 2509933 = 941225) (by norm_num)
theorem B2231405 : Blo 1486063 2231405 := bbase (se 3 (by rfl) ⟨418388, by rfl⟩ : syracuseStep 2231405 = 836777) (by norm_num)
theorem B3345533 : Blo 1486063 3345533 := bbase (se 3 (by rfl) ⟨627287, by rfl⟩ : syracuseStep 3345533 = 1254575) (by norm_num)
theorem B2231429 : Blo 1486063 2231429 := bbase (se 4 (by rfl) ⟨209196, by rfl⟩ : syracuseStep 2231429 = 418393) (by norm_num)
theorem B2010269 : Blo 1486063 2010269 := bbase (se 3 (by rfl) ⟨376925, by rfl⟩ : syracuseStep 2010269 = 753851) (by norm_num)
theorem B2231453 : Blo 1486063 2231453 := bbase (se 3 (by rfl) ⟨418397, by rfl⟩ : syracuseStep 2231453 = 836795) (by norm_num)
theorem B3763381 : Blo 1486063 3763381 := bbase (se 5 (by rfl) ⟨176408, by rfl⟩ : syracuseStep 3763381 = 352817) (by norm_num)
theorem B2231477 : Blo 1486063 2231477 := bbase (se 5 (by rfl) ⟨104600, by rfl⟩ : syracuseStep 2231477 = 209201) (by norm_num)
theorem B3345605 : Blo 1486063 3345605 := bbase (se 4 (by rfl) ⟨313650, by rfl⟩ : syracuseStep 3345605 = 627301) (by norm_num)
theorem B2510021 : Blo 1486063 2510021 := bbase (se 4 (by rfl) ⟨235314, by rfl⟩ : syracuseStep 2510021 = 470629) (by norm_num)
theorem B2231501 : Blo 1486063 2231501 := bbase (se 3 (by rfl) ⟨418406, by rfl⟩ : syracuseStep 2231501 = 836813) (by norm_num)
theorem B2231525 : Blo 1486063 2231525 := bbase (se 4 (by rfl) ⟨209205, by rfl⟩ : syracuseStep 2231525 = 418411) (by norm_num)
theorem B2231549 : Blo 1486063 2231549 := bbase (se 3 (by rfl) ⟨418415, by rfl⟩ : syracuseStep 2231549 = 836831) (by norm_num)
theorem B3345677 : Blo 1486063 3345677 := bbase (se 3 (by rfl) ⟨627314, by rfl⟩ : syracuseStep 3345677 = 1254629) (by norm_num)
theorem B12061973 : Blo 1486063 12061973 := bbase (se 6 (by rfl) ⟨282702, by rfl⟩ : syracuseStep 12061973 = 565405) (by norm_num)
theorem B2231573 : Blo 1486063 2231573 := bbase (se 6 (by rfl) ⟨52302, by rfl⟩ : syracuseStep 2231573 = 104605) (by norm_num)
theorem B2821405 : Blo 1486063 2821405 := bbase (se 3 (by rfl) ⟨529013, by rfl⟩ : syracuseStep 2821405 = 1058027) (by norm_num)
theorem B3763493 : Blo 1486063 3763493 := bbase (se 4 (by rfl) ⟨352827, by rfl⟩ : syracuseStep 3763493 = 705655) (by norm_num)
theorem B5016869 : Blo 1486063 5016869 := bbase (se 4 (by rfl) ⟨470331, by rfl⟩ : syracuseStep 5016869 = 940663) (by norm_num)
theorem B2231597 : Blo 1486063 2231597 := bbase (se 3 (by rfl) ⟨418424, by rfl⟩ : syracuseStep 2231597 = 836849) (by norm_num)
theorem B2714941 : Blo 1486063 2714941 := bbase (se 3 (by rfl) ⟨509051, by rfl⟩ : syracuseStep 2714941 = 1018103) (by norm_num)
theorem B2510149 : Blo 1486063 2510149 := bbase (se 4 (by rfl) ⟨235326, by rfl⟩ : syracuseStep 2510149 = 470653) (by norm_num)
theorem B2231621 : Blo 1486063 2231621 := bbase (se 4 (by rfl) ⟨209214, by rfl⟩ : syracuseStep 2231621 = 418429) (by norm_num)
theorem B3345749 : Blo 1486063 3345749 := bbase (se 11 (by rfl) ⟨2450, by rfl⟩ : syracuseStep 3345749 = 4901) (by norm_num)
theorem B2231645 : Blo 1486063 2231645 := bbase (se 3 (by rfl) ⟨418433, by rfl⟩ : syracuseStep 2231645 = 836867) (by norm_num)
theorem B2231669 : Blo 1486063 2231669 := bbase (se 5 (by rfl) ⟨104609, by rfl⟩ : syracuseStep 2231669 = 209219) (by norm_num)
theorem B2231693 : Blo 1486063 2231693 := bbase (se 3 (by rfl) ⟨418442, by rfl⟩ : syracuseStep 2231693 = 836885) (by norm_num)
theorem B21441941 : Blo 1486063 21441941 := bbase (se 6 (by rfl) ⟨502545, by rfl⟩ : syracuseStep 21441941 = 1005091) (by norm_num)
theorem B3345821 : Blo 1486063 3345821 := bbase (se 3 (by rfl) ⟨627341, by rfl⟩ : syracuseStep 3345821 = 1254683) (by norm_num)
theorem B2510237 : Blo 1486063 2510237 := bbase (se 3 (by rfl) ⟨470669, by rfl⟩ : syracuseStep 2510237 = 941339) (by norm_num)
theorem B2231717 : Blo 1486063 2231717 := bbase (se 4 (by rfl) ⟨209223, by rfl⟩ : syracuseStep 2231717 = 418447) (by norm_num)
theorem B2821549 : Blo 1486063 2821549 := bbase (se 3 (by rfl) ⟨529040, by rfl⟩ : syracuseStep 2821549 = 1058081) (by norm_num)
theorem B7523765 : Blo 1486063 7523765 := bbase (se 5 (by rfl) ⟨352676, by rfl⟩ : syracuseStep 7523765 = 705353) (by norm_num)
theorem B10177973 : Blo 1486063 10177973 := bbase (se 5 (by rfl) ⟨477092, by rfl⟩ : syracuseStep 10177973 = 954185) (by norm_num)
theorem B2231741 : Blo 1486063 2231741 := bbase (se 3 (by rfl) ⟨418451, by rfl⟩ : syracuseStep 2231741 = 836903) (by norm_num)
theorem B2231765 : Blo 1486063 2231765 := bbase (se 7 (by rfl) ⟨26153, by rfl⟩ : syracuseStep 2231765 = 52307) (by norm_num)
theorem B3763685 : Blo 1486063 3763685 := bbase (se 4 (by rfl) ⟨352845, by rfl⟩ : syracuseStep 3763685 = 705691) (by norm_num)
theorem B3345893 : Blo 1486063 3345893 := bbase (se 4 (by rfl) ⟨313677, by rfl⟩ : syracuseStep 3345893 = 627355) (by norm_num)
theorem B2231789 : Blo 1486063 2231789 := bbase (se 3 (by rfl) ⟨418460, by rfl⟩ : syracuseStep 2231789 = 836921) (by norm_num)
theorem B9522677 : Blo 1486063 9522677 := bbase (se 5 (by rfl) ⟨446375, by rfl⟩ : syracuseStep 9522677 = 892751) (by norm_num)
theorem B2231813 : Blo 1486063 2231813 := bbase (se 4 (by rfl) ⟨209232, by rfl⟩ : syracuseStep 2231813 = 418465) (by norm_num)
theorem B2510365 : Blo 1486063 2510365 := bbase (se 3 (by rfl) ⟨470693, by rfl⟩ : syracuseStep 2510365 = 941387) (by norm_num)
theorem B2231837 : Blo 1486063 2231837 := bbase (se 3 (by rfl) ⟨418469, by rfl⟩ : syracuseStep 2231837 = 836939) (by norm_num)
theorem B3345965 : Blo 1486063 3345965 := bbase (se 3 (by rfl) ⟨627368, by rfl⟩ : syracuseStep 3345965 = 1254737) (by norm_num)
theorem B2231861 : Blo 1486063 2231861 := bbase (se 5 (by rfl) ⟨104618, by rfl⟩ : syracuseStep 2231861 = 209237) (by norm_num)
theorem B2821709 : Blo 1486063 2821709 := bbase (se 3 (by rfl) ⟨529070, by rfl⟩ : syracuseStep 2821709 = 1058141) (by norm_num)
theorem B2231885 : Blo 1486063 2231885 := bbase (se 3 (by rfl) ⟨418478, by rfl⟩ : syracuseStep 2231885 = 836957) (by norm_num)
theorem B2231909 : Blo 1486063 2231909 := bbase (se 4 (by rfl) ⟨209241, by rfl⟩ : syracuseStep 2231909 = 418483) (by norm_num)
theorem B3346037 : Blo 1486063 3346037 := bbase (se 5 (by rfl) ⟨156845, by rfl⟩ : syracuseStep 3346037 = 313691) (by norm_num)
theorem B2510453 : Blo 1486063 2510453 := bbase (se 5 (by rfl) ⟨117677, by rfl⟩ : syracuseStep 2510453 = 235355) (by norm_num)
theorem B2231933 : Blo 1486063 2231933 := bbase (se 3 (by rfl) ⟨418487, by rfl⟩ : syracuseStep 2231933 = 836975) (by norm_num)
theorem B2231957 : Blo 1486063 2231957 := bbase (se 6 (by rfl) ⟨52311, by rfl⟩ : syracuseStep 2231957 = 104623) (by norm_num)
theorem B2231981 : Blo 1486063 2231981 := bbase (se 3 (by rfl) ⟨418496, by rfl⟩ : syracuseStep 2231981 = 836993) (by norm_num)
theorem B3346109 : Blo 1486063 3346109 := bbase (se 3 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 3346109 = 1254791) (by norm_num)
theorem B2232005 : Blo 1486063 2232005 := bbase (se 4 (by rfl) ⟨209250, by rfl⟩ : syracuseStep 2232005 = 418501) (by norm_num)
theorem B5017301 : Blo 1486063 5017301 := bbase (se 7 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 5017301 = 117593) (by norm_num)
theorem B6786773 : Blo 1486063 6786773 := bbase (se 7 (by rfl) ⟨79532, by rfl⟩ : syracuseStep 6786773 = 159065) (by norm_num)
theorem B2821853 : Blo 1486063 2821853 := bbase (se 3 (by rfl) ⟨529097, by rfl⟩ : syracuseStep 2821853 = 1058195) (by norm_num)
theorem B2232029 : Blo 1486063 2232029 := bbase (se 3 (by rfl) ⟨418505, by rfl⟩ : syracuseStep 2232029 = 837011) (by norm_num)
theorem B7147237 : Blo 1486063 7147237 := bbase (se 4 (by rfl) ⟨670053, by rfl⟩ : syracuseStep 7147237 = 1340107) (by norm_num)
theorem B2010853 : Blo 1486063 2010853 := bbase (se 4 (by rfl) ⟨188517, by rfl⟩ : syracuseStep 2010853 = 377035) (by norm_num)
theorem B2510581 : Blo 1486063 2510581 := bbase (se 5 (by rfl) ⟨117683, by rfl⟩ : syracuseStep 2510581 = 235367) (by norm_num)
theorem B2232053 : Blo 1486063 2232053 := bbase (se 5 (by rfl) ⟨104627, by rfl⟩ : syracuseStep 2232053 = 209255) (by norm_num)
theorem B3346181 : Blo 1486063 3346181 := bbase (se 4 (by rfl) ⟨313704, by rfl⟩ : syracuseStep 3346181 = 627409) (by norm_num)
theorem B3174157 : Blo 1486063 3174157 := bbase (se 3 (by rfl) ⟨595154, by rfl⟩ : syracuseStep 3174157 = 1190309) (by norm_num)
theorem B2232077 : Blo 1486063 2232077 := bbase (se 3 (by rfl) ⟨418514, by rfl⟩ : syracuseStep 2232077 = 837029) (by norm_num)
theorem B3764029 : Blo 1486063 3764029 := bbase (se 3 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 3764029 = 1411511) (by norm_num)
theorem B3346253 : Blo 1486063 3346253 := bbase (se 3 (by rfl) ⟨627422, by rfl⟩ : syracuseStep 3346253 = 1254845) (by norm_num)
theorem B2510669 : Blo 1486063 2510669 := bbase (se 3 (by rfl) ⟨470750, by rfl⟩ : syracuseStep 2510669 = 941501) (by norm_num)
theorem B10719125 : Blo 1486063 10719125 := bbase (se 6 (by rfl) ⟨251229, by rfl⟩ : syracuseStep 10719125 = 502459) (by norm_num)
theorem B3346325 : Blo 1486063 3346325 := bbase (se 6 (by rfl) ⟨78429, by rfl⟩ : syracuseStep 3346325 = 156859) (by norm_num)
theorem B3764141 : Blo 1486063 3764141 := bbase (se 3 (by rfl) ⟨705776, by rfl⟩ : syracuseStep 3764141 = 1411553) (by norm_num)
theorem B2510797 : Blo 1486063 2510797 := bbase (se 3 (by rfl) ⟨470774, by rfl⟩ : syracuseStep 2510797 = 941549) (by norm_num)
theorem B3346397 : Blo 1486063 3346397 := bbase (se 3 (by rfl) ⟨627449, by rfl⟩ : syracuseStep 3346397 = 1254899) (by norm_num)
theorem B2822141 : Blo 1486063 2822141 := bbase (se 3 (by rfl) ⟨529151, by rfl⟩ : syracuseStep 2822141 = 1058303) (by norm_num)
theorem B7630853 : Blo 1486063 7630853 := bbase (se 4 (by rfl) ⟨715392, by rfl⟩ : syracuseStep 7630853 = 1430785) (by norm_num)
theorem B3346469 : Blo 1486063 3346469 := bbase (se 4 (by rfl) ⟨313731, by rfl⟩ : syracuseStep 3346469 = 627463) (by norm_num)
theorem B2510885 : Blo 1486063 2510885 := bbase (se 4 (by rfl) ⟨235395, by rfl⟩ : syracuseStep 2510885 = 470791) (by norm_num)
theorem B2117677 : Blo 1486063 2117677 := bbase (se 3 (by rfl) ⟨397064, by rfl⟩ : syracuseStep 2117677 = 794129) (by norm_num)
theorem B3764333 : Blo 1486063 3764333 := bbase (se 3 (by rfl) ⟨705812, by rfl⟩ : syracuseStep 3764333 = 1411625) (by norm_num)
theorem B3346541 : Blo 1486063 3346541 := bbase (se 3 (by rfl) ⟨627476, by rfl⟩ : syracuseStep 3346541 = 1254953) (by norm_num)
theorem B5017733 : Blo 1486063 5017733 := bbase (se 4 (by rfl) ⟨470412, by rfl⟩ : syracuseStep 5017733 = 940825) (by norm_num)
theorem B2822293 : Blo 1486063 2822293 := bbase (se 6 (by rfl) ⟨66147, by rfl⟩ : syracuseStep 2822293 = 132295) (by norm_num)
theorem B2511013 : Blo 1486063 2511013 := bbase (se 4 (by rfl) ⟨235407, by rfl⟩ : syracuseStep 2511013 = 470815) (by norm_num)
theorem B3346613 : Blo 1486063 3346613 := bbase (se 5 (by rfl) ⟨156872, by rfl⟩ : syracuseStep 3346613 = 313745) (by norm_num)
theorem B3174653 : Blo 1486063 3174653 := bbase (se 3 (by rfl) ⟨595247, by rfl⟩ : syracuseStep 3174653 = 1190495) (by norm_num)
theorem B3346685 : Blo 1486063 3346685 := bbase (se 3 (by rfl) ⟨627503, by rfl⟩ : syracuseStep 3346685 = 1255007) (by norm_num)
theorem B2511101 : Blo 1486063 2511101 := bbase (se 3 (by rfl) ⟨470831, by rfl⟩ : syracuseStep 2511101 = 941663) (by norm_num)
theorem B7532837 : Blo 1486063 7532837 := bbase (se 4 (by rfl) ⟨706203, by rfl⟩ : syracuseStep 7532837 = 1412407) (by norm_num)
theorem B3346757 : Blo 1486063 3346757 := bbase (se 4 (by rfl) ⟨313758, by rfl⟩ : syracuseStep 3346757 = 627517) (by norm_num)
theorem B4764005 : Blo 1486063 4764005 := bbase (se 4 (by rfl) ⟨446625, by rfl⟩ : syracuseStep 4764005 = 893251) (by norm_num)
theorem B3346829 : Blo 1486063 3346829 := bbase (se 3 (by rfl) ⟨627530, by rfl⟩ : syracuseStep 3346829 = 1255061) (by norm_num)
theorem B2863541 : Blo 1486063 2863541 := bbase (se 5 (by rfl) ⟨134228, by rfl⟩ : syracuseStep 2863541 = 268457) (by norm_num)
theorem B2822597 : Blo 1486063 2822597 := bbase (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) (by norm_num)
theorem B3764677 : Blo 1486063 3764677 := bbase (se 4 (by rfl) ⟨352938, by rfl⟩ : syracuseStep 3764677 = 705877) (by norm_num)
theorem B3346901 : Blo 1486063 3346901 := bbase (se 7 (by rfl) ⟨39221, by rfl⟩ : syracuseStep 3346901 = 78443) (by norm_num)
theorem B5648885 : Blo 1486063 5648885 := bbase (se 5 (by rfl) ⟨264791, by rfl⟩ : syracuseStep 5648885 = 529583) (by norm_num)
theorem B2413061 : Blo 1486063 2413061 := bbase (se 4 (by rfl) ⟨226224, by rfl⟩ : syracuseStep 2413061 = 452449) (by norm_num)
theorem B14291477 : Blo 1486063 14291477 := bbase (se 6 (by rfl) ⟨334956, by rfl⟩ : syracuseStep 14291477 = 669913) (by norm_num)
theorem B3346973 : Blo 1486063 3346973 := bbase (se 3 (by rfl) ⟨627557, by rfl⟩ : syracuseStep 3346973 = 1255115) (by norm_num)
theorem B4764197 : Blo 1486063 4764197 := bbase (se 4 (by rfl) ⟨446643, by rfl⟩ : syracuseStep 4764197 = 893287) (by norm_num)
theorem B5018165 : Blo 1486063 5018165 := bbase (se 5 (by rfl) ⟨235226, by rfl⟩ : syracuseStep 5018165 = 470453) (by norm_num)
theorem B3764789 : Blo 1486063 3764789 := bbase (se 5 (by rfl) ⟨176474, by rfl⟩ : syracuseStep 3764789 = 352949) (by norm_num)
theorem B3347045 : Blo 1486063 3347045 := bbase (se 4 (by rfl) ⟨313785, by rfl⟩ : syracuseStep 3347045 = 627571) (by norm_num)
theorem B2118269 : Blo 1486063 2118269 := bbase (se 3 (by rfl) ⟨397175, by rfl⟩ : syracuseStep 2118269 = 794351) (by norm_num)
theorem B5722757 : Blo 1486063 5722757 := bbase (se 4 (by rfl) ⟨536508, by rfl⟩ : syracuseStep 5722757 = 1073017) (by norm_num)
theorem B3347117 : Blo 1486063 3347117 := bbase (se 3 (by rfl) ⟨627584, by rfl⟩ : syracuseStep 3347117 = 1255169) (by norm_num)
theorem B7525061 : Blo 1486063 7525061 := bbase (se 4 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 7525061 = 1410949) (by norm_num)
theorem B2118349 : Blo 1486063 2118349 := bbase (se 3 (by rfl) ⟨397190, by rfl⟩ : syracuseStep 2118349 = 794381) (by norm_num)
theorem B1528561 : Blo 1486063 1528561 := bbase (se 2 (by rfl) ⟨573210, by rfl⟩ : syracuseStep 1528561 = 1146421) (by norm_num)
theorem B14480117 : Blo 1486063 14480117 := bbase (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) (by norm_num)
theorem B3764981 : Blo 1486063 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B3347189 : Blo 1486063 3347189 := bbase (se 5 (by rfl) ⟨156899, by rfl⟩ : syracuseStep 3347189 = 313799) (by norm_num)
theorem B5649173 : Blo 1486063 5649173 := bbase (se 6 (by rfl) ⟨132402, by rfl⟩ : syracuseStep 5649173 = 264805) (by norm_num)
theorem B3347261 : Blo 1486063 3347261 := bbase (se 3 (by rfl) ⟨627611, by rfl⟩ : syracuseStep 3347261 = 1255223) (by norm_num)
theorem B2118469 : Blo 1486063 2118469 := bbase (se 4 (by rfl) ⟨198606, by rfl⟩ : syracuseStep 2118469 = 397213) (by norm_num)
theorem B1880921 : Blo 1486063 1880921 := bbase (se 2 (by rfl) ⟨705345, by rfl⟩ : syracuseStep 1880921 = 1410691) (by norm_num)
theorem B3347333 : Blo 1486063 3347333 := bbase (se 4 (by rfl) ⟨313812, by rfl⟩ : syracuseStep 3347333 = 627625) (by norm_num)
theorem B1880977 : Blo 1486063 1880977 := bbase (se 2 (by rfl) ⟨705366, by rfl⟩ : syracuseStep 1880977 = 1410733) (by norm_num)
theorem B2118565 : Blo 1486063 2118565 := bbase (se 4 (by rfl) ⟨198615, by rfl⟩ : syracuseStep 2118565 = 397231) (by norm_num)
theorem B3347405 : Blo 1486063 3347405 := bbase (se 3 (by rfl) ⟨627638, by rfl⟩ : syracuseStep 3347405 = 1255277) (by norm_num)
theorem B5018597 : Blo 1486063 5018597 := bbase (se 4 (by rfl) ⟨470493, by rfl⟩ : syracuseStep 5018597 = 940987) (by norm_num)
theorem B1881073 : Blo 1486063 1881073 := bbase (se 2 (by rfl) ⟨705402, by rfl⟩ : syracuseStep 1881073 = 1410805) (by norm_num)
theorem B3347477 : Blo 1486063 3347477 := bbase (se 6 (by rfl) ⟨78456, by rfl⟩ : syracuseStep 3347477 = 156913) (by norm_num)
theorem B3765325 : Blo 1486063 3765325 := bbase (se 3 (by rfl) ⟨705998, by rfl⟩ : syracuseStep 3765325 = 1411997) (by norm_num)
theorem B1528913 : Blo 1486063 1528913 := bbase (se 2 (by rfl) ⟨573342, by rfl⟩ : syracuseStep 1528913 = 1146685) (by norm_num)
theorem B3175517 : Blo 1486063 3175517 := bbase (se 3 (by rfl) ⟨595409, by rfl⟩ : syracuseStep 3175517 = 1190819) (by norm_num)
theorem B3347549 : Blo 1486063 3347549 := bbase (se 3 (by rfl) ⟨627665, by rfl⟩ : syracuseStep 3347549 = 1255331) (by norm_num)
theorem B1881245 : Blo 1486063 1881245 := bbase (se 3 (by rfl) ⟨352733, by rfl⟩ : syracuseStep 1881245 = 705467) (by norm_num)
theorem B3347621 : Blo 1486063 3347621 := bbase (se 4 (by rfl) ⟨313839, by rfl⟩ : syracuseStep 3347621 = 627679) (by norm_num)
theorem B2823349 : Blo 1486063 2823349 := bbase (se 5 (by rfl) ⟨132344, by rfl⟩ : syracuseStep 2823349 = 264689) (by norm_num)
theorem B3765437 : Blo 1486063 3765437 := bbase (se 3 (by rfl) ⟨706019, by rfl⟩ : syracuseStep 3765437 = 1412039) (by norm_num)
theorem B6436037 : Blo 1486063 6436037 := bbase (se 4 (by rfl) ⟨603378, by rfl⟩ : syracuseStep 6436037 = 1206757) (by norm_num)
theorem B1881301 : Blo 1486063 1881301 := bbase (se 7 (by rfl) ⟨22046, by rfl⟩ : syracuseStep 1881301 = 44093) (by norm_num)
theorem B3175661 : Blo 1486063 3175661 := bbase (se 3 (by rfl) ⟨595436, by rfl⟩ : syracuseStep 3175661 = 1190873) (by norm_num)
theorem B3347693 : Blo 1486063 3347693 := bbase (se 3 (by rfl) ⟨627692, by rfl⟩ : syracuseStep 3347693 = 1255385) (by norm_num)
theorem B2381093 : Blo 1486063 2381093 := bbase (se 4 (by rfl) ⟨223227, by rfl⟩ : syracuseStep 2381093 = 446455) (by norm_num)
theorem B1881397 : Blo 1486063 1881397 := bbase (se 5 (by rfl) ⟨88190, by rfl⟩ : syracuseStep 1881397 = 176381) (by norm_num)
theorem B3814709 : Blo 1486063 3814709 := bbase (se 5 (by rfl) ⟨178814, by rfl⟩ : syracuseStep 3814709 = 357629) (by norm_num)
theorem B3347765 : Blo 1486063 3347765 := bbase (se 5 (by rfl) ⟨156926, by rfl⟩ : syracuseStep 3347765 = 313853) (by norm_num)
theorem B2823493 : Blo 1486063 2823493 := bbase (se 4 (by rfl) ⟨264702, by rfl⟩ : syracuseStep 2823493 = 529405) (by norm_num)
theorem B3765629 : Blo 1486063 3765629 := bbase (se 3 (by rfl) ⟨706055, by rfl⟩ : syracuseStep 3765629 = 1412111) (by norm_num)
theorem B3347837 : Blo 1486063 3347837 := bbase (se 3 (by rfl) ⟨627719, by rfl⟩ : syracuseStep 3347837 = 1255439) (by norm_num)
theorem B5019029 : Blo 1486063 5019029 := bbase (se 6 (by rfl) ⟨117633, by rfl⟩ : syracuseStep 5019029 = 235267) (by norm_num)
theorem B3347909 : Blo 1486063 3347909 := bbase (se 4 (by rfl) ⟨313866, by rfl⟩ : syracuseStep 3347909 = 627733) (by norm_num)
theorem B12703189 : Blo 1486063 12703189 := bbase (se 7 (by rfl) ⟨148865, by rfl⟩ : syracuseStep 12703189 = 297731) (by norm_num)
theorem B1881569 : Blo 1486063 1881569 := bbase (se 2 (by rfl) ⟨705588, by rfl⟩ : syracuseStep 1881569 = 1411177) (by norm_num)
theorem B2381285 : Blo 1486063 2381285 := bbase (se 4 (by rfl) ⟨223245, by rfl⟩ : syracuseStep 2381285 = 446491) (by norm_num)
theorem B2823653 : Blo 1486063 2823653 := bbase (se 4 (by rfl) ⟨264717, by rfl⟩ : syracuseStep 2823653 = 529435) (by norm_num)
theorem B3347981 : Blo 1486063 3347981 := bbase (se 3 (by rfl) ⟨627746, by rfl⟩ : syracuseStep 3347981 = 1255493) (by norm_num)
theorem B1881625 : Blo 1486063 1881625 := bbase (se 2 (by rfl) ⟨705609, by rfl⟩ : syracuseStep 1881625 = 1411219) (by norm_num)
theorem B3348053 : Blo 1486063 3348053 := bbase (se 8 (by rfl) ⟨19617, by rfl⟩ : syracuseStep 3348053 = 39235) (by norm_num)
theorem B2381413 : Blo 1486063 2381413 := bbase (se 4 (by rfl) ⟨223257, by rfl⟩ : syracuseStep 2381413 = 446515) (by norm_num)
theorem B2823797 : Blo 1486063 2823797 := bbase (se 5 (by rfl) ⟨132365, by rfl⟩ : syracuseStep 2823797 = 264731) (by norm_num)
theorem B1881721 : Blo 1486063 1881721 := bbase (se 2 (by rfl) ⟨705645, by rfl⟩ : syracuseStep 1881721 = 1411291) (by norm_num)
theorem B4232837 : Blo 1486063 4232837 := bbase (se 4 (by rfl) ⟨396828, by rfl⟩ : syracuseStep 4232837 = 793657) (by norm_num)
theorem B3348125 : Blo 1486063 3348125 := bbase (se 3 (by rfl) ⟨627773, by rfl⟩ : syracuseStep 3348125 = 1255547) (by norm_num)
theorem B3765973 : Blo 1486063 3765973 := bbase (se 7 (by rfl) ⟨44132, by rfl⟩ : syracuseStep 3765973 = 88265) (by norm_num)
theorem B1881893 : Blo 1486063 1881893 := bbase (se 4 (by rfl) ⟨176427, by rfl⟩ : syracuseStep 1881893 = 352855) (by norm_num)
theorem B5019461 : Blo 1486063 5019461 := bbase (se 4 (by rfl) ⟨470574, by rfl⟩ : syracuseStep 5019461 = 941149) (by norm_num)
theorem B3766085 : Blo 1486063 3766085 := bbase (se 4 (by rfl) ⟨353070, by rfl⟩ : syracuseStep 3766085 = 706141) (by norm_num)
theorem B1881949 : Blo 1486063 1881949 := bbase (se 3 (by rfl) ⟨352865, by rfl⟩ : syracuseStep 1881949 = 705731) (by norm_num)
theorem B2824085 : Blo 1486063 2824085 := bbase (se 6 (by rfl) ⟨66189, by rfl⟩ : syracuseStep 2824085 = 132379) (by norm_num)
theorem B1587109 : Blo 1486063 1587109 := bbase (se 4 (by rfl) ⟨148791, by rfl⟩ : syracuseStep 1587109 = 297583) (by norm_num)
theorem B1882045 : Blo 1486063 1882045 := bbase (se 3 (by rfl) ⟨352883, by rfl⟩ : syracuseStep 1882045 = 705767) (by norm_num)
theorem B7526357 : Blo 1486063 7526357 := bbase (se 7 (by rfl) ⟨88199, by rfl⟩ : syracuseStep 7526357 = 176399) (by norm_num)
theorem B3176405 : Blo 1486063 3176405 := bbase (se 7 (by rfl) ⟨37223, by rfl⟩ : syracuseStep 3176405 = 74447) (by norm_num)
theorem B3766277 : Blo 1486063 3766277 := bbase (se 4 (by rfl) ⟨353088, by rfl⟩ : syracuseStep 3766277 = 706177) (by norm_num)
theorem B2824237 : Blo 1486063 2824237 := bbase (se 3 (by rfl) ⟨529544, by rfl⟩ : syracuseStep 2824237 = 1059089) (by norm_num)
theorem B1718345 : Blo 1486063 1718345 := bbase (se 2 (by rfl) ⟨644379, by rfl⟩ : syracuseStep 1718345 = 1288759) (by norm_num)
theorem B1882217 : Blo 1486063 1882217 := bbase (se 2 (by rfl) ⟨705831, by rfl⟩ : syracuseStep 1882217 = 1411663) (by norm_num)
theorem B1882273 : Blo 1486063 1882273 := bbase (se 2 (by rfl) ⟨705852, by rfl⟩ : syracuseStep 1882273 = 1411705) (by norm_num)
theorem B3438797 : Blo 1486063 3438797 := bbase (se 3 (by rfl) ⟨644774, by rfl⟩ : syracuseStep 3438797 = 1289549) (by norm_num)
theorem B2382053 : Blo 1486063 2382053 := bbase (se 4 (by rfl) ⟨223317, by rfl⟩ : syracuseStep 2382053 = 446635) (by norm_num)
theorem B5019893 : Blo 1486063 5019893 := bbase (se 5 (by rfl) ⟨235307, by rfl⟩ : syracuseStep 5019893 = 470615) (by norm_num)
theorem B1882369 : Blo 1486063 1882369 := bbase (se 2 (by rfl) ⟨705888, by rfl⟩ : syracuseStep 1882369 = 1411777) (by norm_num)
theorem B1587485 : Blo 1486063 1587485 := bbase (se 3 (by rfl) ⟨297653, by rfl⟩ : syracuseStep 1587485 = 595307) (by norm_num)
theorem B4233509 : Blo 1486063 4233509 := bbase (se 4 (by rfl) ⟨396891, by rfl⟩ : syracuseStep 4233509 = 793783) (by norm_num)
theorem B5642581 : Blo 1486063 5642581 := bbase (se 10 (by rfl) ⟨8265, by rfl⟩ : syracuseStep 5642581 = 16531) (by norm_num)
theorem B2824541 : Blo 1486063 2824541 := bbase (se 3 (by rfl) ⟨529601, by rfl⟩ : syracuseStep 2824541 = 1059203) (by norm_num)
theorem B3766621 : Blo 1486063 3766621 := bbase (se 3 (by rfl) ⟨706241, by rfl⟩ : syracuseStep 3766621 = 1412483) (by norm_num)
theorem B1587557 : Blo 1486063 1587557 := bbase (se 4 (by rfl) ⟨148833, by rfl⟩ : syracuseStep 1587557 = 297667) (by norm_num)
theorem B11295125 : Blo 1486063 11295125 := bbase (se 6 (by rfl) ⟨264729, by rfl⟩ : syracuseStep 11295125 = 529459) (by norm_num)
theorem B1882541 : Blo 1486063 1882541 := bbase (se 3 (by rfl) ⟨352976, by rfl⟩ : syracuseStep 1882541 = 705953) (by norm_num)
theorem B1882597 : Blo 1486063 1882597 := bbase (se 4 (by rfl) ⟨176493, by rfl⟩ : syracuseStep 1882597 = 352987) (by norm_num)
theorem B1587745 : Blo 1486063 1587745 := bbase (se 2 (by rfl) ⟨595404, by rfl⟩ : syracuseStep 1587745 = 1190809) (by norm_num)
theorem B1882693 : Blo 1486063 1882693 := bbase (se 4 (by rfl) ⟨176502, by rfl⟩ : syracuseStep 1882693 = 353005) (by norm_num)
theorem B2259533 : Blo 1486063 2259533 := bbase (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) (by norm_num)
theorem B5642885 : Blo 1486063 5642885 := bbase (se 4 (by rfl) ⟨529020, by rfl⟩ : syracuseStep 5642885 = 1058041) (by norm_num)
theorem B5020325 : Blo 1486063 5020325 := bbase (se 4 (by rfl) ⟨470655, by rfl⟩ : syracuseStep 5020325 = 941311) (by norm_num)
theorem B2382509 : Blo 1486063 2382509 := bbase (se 3 (by rfl) ⟨446720, by rfl⟩ : syracuseStep 2382509 = 893441) (by norm_num)
theorem B3177157 : Blo 1486063 3177157 := bbase (se 4 (by rfl) ⟨297858, by rfl⟩ : syracuseStep 3177157 = 595717) (by norm_num)
theorem B4233941 : Blo 1486063 4233941 := bbase (se 7 (by rfl) ⟨49616, by rfl⟩ : syracuseStep 4233941 = 99233) (by norm_num)
theorem B1587929 : Blo 1486063 1587929 := bbase (se 2 (by rfl) ⟨595473, by rfl⟩ : syracuseStep 1587929 = 1190947) (by norm_num)
theorem B1882865 : Blo 1486063 1882865 := bbase (se 2 (by rfl) ⟨706074, by rfl⟩ : syracuseStep 1882865 = 1412149) (by norm_num)
theorem B3054341 : Blo 1486063 3054341 := bbase (se 4 (by rfl) ⟨286344, by rfl⟩ : syracuseStep 3054341 = 572689) (by norm_num)
theorem B1882921 : Blo 1486063 1882921 := bbase (se 2 (by rfl) ⟨706095, by rfl⟩ : syracuseStep 1882921 = 1412191) (by norm_num)
theorem B11287349 : Blo 1486063 11287349 := bbase (se 5 (by rfl) ⟨529094, by rfl⟩ : syracuseStep 11287349 = 1058189) (by norm_num)
theorem B2448181 : Blo 1486063 2448181 := bbase (se 5 (by rfl) ⟨114758, by rfl⟩ : syracuseStep 2448181 = 229517) (by norm_num)
theorem B32168789 : Blo 1486063 32168789 := bbase (se 9 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 32168789 = 188489) (by norm_num)
theorem B3177301 : Blo 1486063 3177301 := bbase (se 9 (by rfl) ⟨9308, by rfl⟩ : syracuseStep 3177301 = 18617) (by norm_num)
theorem B24132437 : Blo 1486063 24132437 := bbase (se 9 (by rfl) ⟨70700, by rfl⟩ : syracuseStep 24132437 = 141401) (by norm_num)
theorem B1883017 : Blo 1486063 1883017 := bbase (se 2 (by rfl) ⟨706131, by rfl⟩ : syracuseStep 1883017 = 1412263) (by norm_num)
theorem B2382733 : Blo 1486063 2382733 := bbase (se 3 (by rfl) ⟨446762, by rfl⟩ : syracuseStep 2382733 = 893525) (by norm_num)
theorem B3218357 : Blo 1486063 3218357 := bbase (se 5 (by rfl) ⟨150860, by rfl⟩ : syracuseStep 3218357 = 301721) (by norm_num)
theorem B2382797 : Blo 1486063 2382797 := bbase (se 3 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 2382797 = 893549) (by norm_num)
theorem B1883189 : Blo 1486063 1883189 := bbase (se 5 (by rfl) ⟨88274, by rfl⟩ : syracuseStep 1883189 = 176549) (by norm_num)
theorem B2382925 : Blo 1486063 2382925 := bbase (se 3 (by rfl) ⟨446798, by rfl⟩ : syracuseStep 2382925 = 893597) (by norm_num)
theorem B5020757 : Blo 1486063 5020757 := bbase (se 8 (by rfl) ⟨29418, by rfl⟩ : syracuseStep 5020757 = 58837) (by norm_num)
theorem B1883245 : Blo 1486063 1883245 := bbase (se 3 (by rfl) ⟨353108, by rfl⟩ : syracuseStep 1883245 = 706217) (by norm_num)
theorem B4586645 : Blo 1486063 4586645 := bbase (se 6 (by rfl) ⟨107499, by rfl⟩ : syracuseStep 4586645 = 214999) (by norm_num)
theorem B4021445 : Blo 1486063 4021445 := bbase (se 4 (by rfl) ⟨377010, by rfl⟩ : syracuseStep 4021445 = 754021) (by norm_num)
theorem B3177677 : Blo 1486063 3177677 := bbase (se 3 (by rfl) ⟨595814, by rfl⟩ : syracuseStep 3177677 = 1191629) (by norm_num)
theorem B7527653 : Blo 1486063 7527653 := bbase (se 4 (by rfl) ⟨705717, by rfl⟩ : syracuseStep 7527653 = 1411435) (by norm_num)
theorem B41278805 : Blo 1486063 41278805 := bbase (se 11 (by rfl) ⟨30233, by rfl⟩ : syracuseStep 41278805 = 60467) (by norm_num)
theorem B12705173 : Blo 1486063 12705173 := bbase (se 6 (by rfl) ⟨297777, by rfl⟩ : syracuseStep 12705173 = 595555) (by norm_num)
theorem B1834393 : Blo 1486063 1834393 := bbase (se 2 (by rfl) ⟨687897, by rfl⟩ : syracuseStep 1834393 = 1375795) (by norm_num)
theorem B7634341 : Blo 1486063 7634341 := bbase (se 4 (by rfl) ⟨715719, by rfl⟩ : syracuseStep 7634341 = 1431439) (by norm_num)
theorem B4234693 : Blo 1486063 4234693 := bbase (se 4 (by rfl) ⟨397002, by rfl⟩ : syracuseStep 4234693 = 794005) (by norm_num)
theorem B1588681 : Blo 1486063 1588681 := bbase (se 2 (by rfl) ⟨595755, by rfl⟩ : syracuseStep 1588681 = 1191511) (by norm_num)
theorem B16940501 : Blo 1486063 16940501 := bbase (se 7 (by rfl) ⟨198521, by rfl⟩ : syracuseStep 16940501 = 397043) (by norm_num)
theorem B2260453 : Blo 1486063 2260453 := bbase (se 4 (by rfl) ⟨211917, by rfl⟩ : syracuseStep 2260453 = 423835) (by norm_num)
theorem B5021189 : Blo 1486063 5021189 := bbase (se 4 (by rfl) ⟨470736, by rfl⟩ : syracuseStep 5021189 = 941473) (by norm_num)
theorem B2014733 : Blo 1486063 2014733 := bbase (se 3 (by rfl) ⟨377762, by rfl⟩ : syracuseStep 2014733 = 755525) (by norm_num)
theorem B1588753 : Blo 1486063 1588753 := bbase (se 2 (by rfl) ⟨595782, by rfl⟩ : syracuseStep 1588753 = 1191565) (by norm_num)
theorem B1785397 : Blo 1486063 1785397 := bbase (se 5 (by rfl) ⟨83690, by rfl⟩ : syracuseStep 1785397 = 167381) (by norm_num)
theorem B3178045 : Blo 1486063 3178045 := bbase (se 3 (by rfl) ⟨595883, by rfl⟩ : syracuseStep 3178045 = 1191767) (by norm_num)
theorem B2678341 : Blo 1486063 2678341 := bbase (se 4 (by rfl) ⟨251094, by rfl⟩ : syracuseStep 2678341 = 502189) (by norm_num)
theorem B1719973 : Blo 1486063 1719973 := bbase (se 4 (by rfl) ⟨161247, by rfl⟩ : syracuseStep 1719973 = 322495) (by norm_num)
theorem B1588933 : Blo 1486063 1588933 := bbase (se 4 (by rfl) ⟨148962, by rfl⟩ : syracuseStep 1588933 = 297925) (by norm_num)
theorem B1507069 : Blo 1486063 1507069 := bbase (se 3 (by rfl) ⟨282575, by rfl⟩ : syracuseStep 1507069 = 565151) (by norm_num)
theorem B1859365 : Blo 1486063 1859365 := bbase (se 4 (by rfl) ⟨174315, by rfl⟩ : syracuseStep 1859365 = 348631) (by norm_num)
theorem B7143221 : Blo 1486063 7143221 := bbase (se 5 (by rfl) ⟨334838, by rfl⟩ : syracuseStep 7143221 = 669677) (by norm_num)
theorem B2678629 : Blo 1486063 2678629 := bbase (se 4 (by rfl) ⟨251121, by rfl⟩ : syracuseStep 2678629 = 502243) (by norm_num)
theorem B5357429 : Blo 1486063 5357429 := bbase (se 5 (by rfl) ⟨251129, by rfl⟩ : syracuseStep 5357429 = 502259) (by norm_num)
theorem B6348725 : Blo 1486063 6348725 := bbase (se 5 (by rfl) ⟨297596, by rfl⟩ : syracuseStep 6348725 = 595193) (by norm_num)
theorem B5021621 : Blo 1486063 5021621 := bbase (se 5 (by rfl) ⟨235388, by rfl⟩ : syracuseStep 5021621 = 470777) (by norm_num)
theorem B5431253 : Blo 1486063 5431253 := bbase (se 7 (by rfl) ⟨63647, by rfl⟩ : syracuseStep 5431253 = 127295) (by norm_num)
theorem B20348941 : Blo 1486063 20348941 := bstep (se 3 (by rfl) ⟨3815426, by rfl⟩ : syracuseStep 20348941 = 7630853) B7630853
theorem B5357603 : Blo 1486063 5357603 := bstep (se 1 (by rfl) ⟨4018202, by rfl⟩ : syracuseStep 5357603 = 8036405) B8036405
theorem B3571793 : Blo 1486063 3571793 := bstep (se 2 (by rfl) ⟨1339422, by rfl⟩ : syracuseStep 3571793 = 2678845) B2678845
theorem B5021837 : Blo 1486063 5021837 := bstep (se 3 (by rfl) ⟨941594, by rfl⟩ : syracuseStep 5021837 = 1883189) B1883189
theorem B7528625 : Blo 1486063 7528625 := bstep (se 2 (by rfl) ⟨2823234, by rfl⟩ : syracuseStep 7528625 = 5646469) B5646469
theorem B5021891 : Blo 1486063 5021891 := bstep (se 1 (by rfl) ⟨3766418, by rfl⟩ : syracuseStep 5021891 = 7532837) B7532837
theorem B1909027 : Blo 1486063 1909027 := bstep (se 1 (by rfl) ⟨1431770, by rfl⟩ : syracuseStep 1909027 = 2863541) B2863541
theorem B9527651 : Blo 1486063 9527651 := bstep (se 1 (by rfl) ⟨7145738, by rfl⟩ : syracuseStep 9527651 = 14291477) B14291477
theorem B1933699 : Blo 1486063 1933699 := bstep (se 1 (by rfl) ⟨1450274, by rfl⟩ : syracuseStep 1933699 = 2900549) B2900549
theorem B5022161 : Blo 1486063 5022161 := bstep (se 2 (by rfl) ⟨1883310, by rfl⟩ : syracuseStep 5022161 = 3766621) B3766621
theorem B10723853 : Blo 1486063 10723853 := bstep (se 3 (by rfl) ⟨2010722, by rfl⟩ : syracuseStep 10723853 = 4021445) B4021445
theorem B19063349 : Blo 1486063 19063349 := bstep (se 5 (by rfl) ⟨893594, by rfl⟩ : syracuseStep 19063349 = 1787189) B1787189
theorem B1786483 : Blo 1486063 1786483 := bstep (se 1 (by rfl) ⟨1339862, by rfl⟩ : syracuseStep 1786483 = 2679725) B2679725
theorem B1671907 : Blo 1486063 1671907 := bstep (se 1 (by rfl) ⟨1253930, by rfl⟩ : syracuseStep 1671907 = 2507861) B2507861
theorem B1786627 : Blo 1486063 1786627 := bstep (se 1 (by rfl) ⟨1339970, by rfl⟩ : syracuseStep 1786627 = 2679941) B2679941
theorem B6349681 : Blo 1486063 6349681 := bstep (se 2 (by rfl) ⟨2381130, by rfl⟩ : syracuseStep 6349681 = 4762261) B4762261
theorem B2229107 : Blo 1486063 2229107 := bstep (se 1 (by rfl) ⟨1671830, by rfl⟩ : syracuseStep 2229107 = 3343661) B3343661
theorem B1672051 : Blo 1486063 1672051 := bstep (se 1 (by rfl) ⟨1254038, by rfl⟩ : syracuseStep 1672051 = 2508077) B2508077
theorem B2229137 : Blo 1486063 2229137 := bstep (se 2 (by rfl) ⟨835926, by rfl⟩ : syracuseStep 2229137 = 1671853) B1671853
theorem B2229155 : Blo 1486063 2229155 := bstep (se 1 (by rfl) ⟨1671866, by rfl⟩ : syracuseStep 2229155 = 3343733) B3343733
theorem B4236209 : Blo 1486063 4236209 := bstep (se 2 (by rfl) ⟨1588578, by rfl⟩ : syracuseStep 4236209 = 3177157) B3177157
theorem B2229185 : Blo 1486063 2229185 := bstep (se 2 (by rfl) ⟨835944, by rfl⟩ : syracuseStep 2229185 = 1671889) B1671889
theorem B2229203 : Blo 1486063 2229203 := bstep (se 1 (by rfl) ⟨1671902, by rfl⟩ : syracuseStep 2229203 = 3343805) B3343805
theorem B2229233 : Blo 1486063 2229233 := bstep (se 2 (by rfl) ⟨835962, by rfl⟩ : syracuseStep 2229233 = 1671925) B1671925
theorem B2229251 : Blo 1486063 2229251 := bstep (se 1 (by rfl) ⟨1671938, by rfl⟩ : syracuseStep 2229251 = 3343877) B3343877
theorem B1672195 : Blo 1486063 1672195 := bstep (se 1 (by rfl) ⟨1254146, by rfl⟩ : syracuseStep 1672195 = 2508293) B2508293
theorem B2229281 : Blo 1486063 2229281 := bstep (se 2 (by rfl) ⟨835980, by rfl⟩ : syracuseStep 2229281 = 1671961) B1671961
theorem B2507827 : Blo 1486063 2507827 := bstep (se 1 (by rfl) ⟨1880870, by rfl⟩ : syracuseStep 2507827 = 3761741) B3761741
theorem B2229299 : Blo 1486063 2229299 := bstep (se 1 (by rfl) ⟨1671974, by rfl⟩ : syracuseStep 2229299 = 3343949) B3343949
theorem B2229329 : Blo 1486063 2229329 := bstep (se 2 (by rfl) ⟨835998, by rfl⟩ : syracuseStep 2229329 = 1671997) B1671997
theorem B2229347 : Blo 1486063 2229347 := bstep (se 1 (by rfl) ⟨1672010, by rfl⟩ : syracuseStep 2229347 = 3344021) B3344021
theorem B4236401 : Blo 1486063 4236401 := bstep (se 2 (by rfl) ⟨1588650, by rfl⟩ : syracuseStep 4236401 = 3177301) B3177301
theorem B2229377 : Blo 1486063 2229377 := bstep (se 2 (by rfl) ⟨836016, by rfl⟩ : syracuseStep 2229377 = 1672033) B1672033
theorem B2262161 : Blo 1486063 2262161 := bstep (se 2 (by rfl) ⟨848310, by rfl⟩ : syracuseStep 2262161 = 1696621) B1696621
theorem B2229395 : Blo 1486063 2229395 := bstep (se 1 (by rfl) ⟨1672046, by rfl⟩ : syracuseStep 2229395 = 3344093) B3344093
theorem B1672339 : Blo 1486063 1672339 := bstep (se 1 (by rfl) ⟨1254254, by rfl⟩ : syracuseStep 1672339 = 2508509) B2508509
theorem B2229425 : Blo 1486063 2229425 := bstep (se 2 (by rfl) ⟨836034, by rfl⟩ : syracuseStep 2229425 = 1672069) B1672069
theorem B2507969 : Blo 1486063 2507969 := bstep (se 2 (by rfl) ⟨940488, by rfl⟩ : syracuseStep 2507969 = 1880977) B1880977
theorem B2229443 : Blo 1486063 2229443 := bstep (se 1 (by rfl) ⟨1672082, by rfl⟩ : syracuseStep 2229443 = 3344165) B3344165
theorem B2229473 : Blo 1486063 2229473 := bstep (se 2 (by rfl) ⟨836052, by rfl⟩ : syracuseStep 2229473 = 1672105) B1672105
theorem B2229491 : Blo 1486063 2229491 := bstep (se 1 (by rfl) ⟨1672118, by rfl⟩ : syracuseStep 2229491 = 3344237) B3344237
theorem B8152325 : Blo 1486063 8152325 := bstep (se 4 (by rfl) ⟨764280, by rfl⟩ : syracuseStep 8152325 = 1528561) B1528561
theorem B2229521 : Blo 1486063 2229521 := bstep (se 2 (by rfl) ⟨836070, by rfl⟩ : syracuseStep 2229521 = 1672141) B1672141
theorem B2229539 : Blo 1486063 2229539 := bstep (se 1 (by rfl) ⟨1672154, by rfl⟩ : syracuseStep 2229539 = 3344309) B3344309
theorem B1672483 : Blo 1486063 1672483 := bstep (se 1 (by rfl) ⟨1254362, by rfl⟩ : syracuseStep 1672483 = 2508725) B2508725
theorem B2508097 : Blo 1486063 2508097 := bstep (se 2 (by rfl) ⟨940536, by rfl⟩ : syracuseStep 2508097 = 1881073) B1881073
theorem B2229569 : Blo 1486063 2229569 := bstep (se 2 (by rfl) ⟨836088, by rfl⟩ : syracuseStep 2229569 = 1672177) B1672177
theorem B8037701 : Blo 1486063 8037701 := bstep (se 4 (by rfl) ⟨753534, by rfl⟩ : syracuseStep 8037701 = 1507069) B1507069
theorem B3343697 : Blo 1486063 3343697 := bstep (se 2 (by rfl) ⟨1253886, by rfl⟩ : syracuseStep 3343697 = 2507773) B2507773
theorem B2229587 : Blo 1486063 2229587 := bstep (se 1 (by rfl) ⟨1672190, by rfl⟩ : syracuseStep 2229587 = 3344381) B3344381
theorem B3343715 : Blo 1486063 3343715 := bstep (se 1 (by rfl) ⟨2507786, by rfl⟩ : syracuseStep 3343715 = 5015573) B5015573
theorem B2508131 : Blo 1486063 2508131 := bstep (se 1 (by rfl) ⟨1881098, by rfl⟩ : syracuseStep 2508131 = 3762197) B3762197
theorem B2229617 : Blo 1486063 2229617 := bstep (se 2 (by rfl) ⟨836106, by rfl⟩ : syracuseStep 2229617 = 1672213) B1672213
theorem B2229635 : Blo 1486063 2229635 := bstep (se 1 (by rfl) ⟨1672226, by rfl⟩ : syracuseStep 2229635 = 3344453) B3344453
theorem B2229665 : Blo 1486063 2229665 := bstep (se 2 (by rfl) ⟨836124, by rfl⟩ : syracuseStep 2229665 = 1672249) B1672249
theorem B2229683 : Blo 1486063 2229683 := bstep (se 1 (by rfl) ⟨1672262, by rfl⟩ : syracuseStep 2229683 = 3344525) B3344525
theorem B1672627 : Blo 1486063 1672627 := bstep (se 1 (by rfl) ⟨1254470, by rfl⟩ : syracuseStep 1672627 = 2508941) B2508941
theorem B2229713 : Blo 1486063 2229713 := bstep (se 2 (by rfl) ⟨836142, by rfl⟩ : syracuseStep 2229713 = 1672285) B1672285
theorem B2508259 : Blo 1486063 2508259 := bstep (se 1 (by rfl) ⟨1881194, by rfl⟩ : syracuseStep 2508259 = 3762389) B3762389
theorem B2229731 : Blo 1486063 2229731 := bstep (se 1 (by rfl) ⟨1672298, by rfl⟩ : syracuseStep 2229731 = 3344597) B3344597
theorem B2229761 : Blo 1486063 2229761 := bstep (se 2 (by rfl) ⟨836160, by rfl⟩ : syracuseStep 2229761 = 1672321) B1672321
theorem B2229779 : Blo 1486063 2229779 := bstep (se 1 (by rfl) ⟨1672334, by rfl⟩ : syracuseStep 2229779 = 3344669) B3344669
theorem B2229809 : Blo 1486063 2229809 := bstep (se 2 (by rfl) ⟨836178, by rfl⟩ : syracuseStep 2229809 = 1672357) B1672357
theorem B2229827 : Blo 1486063 2229827 := bstep (se 1 (by rfl) ⟨1672370, by rfl⟩ : syracuseStep 2229827 = 3344741) B3344741
theorem B1672771 : Blo 1486063 1672771 := bstep (se 1 (by rfl) ⟨1254578, by rfl⟩ : syracuseStep 1672771 = 2509157) B2509157
theorem B2229857 : Blo 1486063 2229857 := bstep (se 2 (by rfl) ⟨836196, by rfl⟩ : syracuseStep 2229857 = 1672393) B1672393
theorem B7530083 : Blo 1486063 7530083 := bstep (se 1 (by rfl) ⟨5647562, by rfl⟩ : syracuseStep 7530083 = 11295125) B11295125
theorem B3343985 : Blo 1486063 3343985 := bstep (se 2 (by rfl) ⟨1253994, by rfl⟩ : syracuseStep 3343985 = 2507989) B2507989
theorem B2508401 : Blo 1486063 2508401 := bstep (se 2 (by rfl) ⟨940650, by rfl⟩ : syracuseStep 2508401 = 1881301) B1881301
theorem B2229875 : Blo 1486063 2229875 := bstep (se 1 (by rfl) ⟨1672406, by rfl⟩ : syracuseStep 2229875 = 3344813) B3344813
theorem B42862193 : Blo 1486063 42862193 := bstep (se 2 (by rfl) ⟨16073322, by rfl⟩ : syracuseStep 42862193 = 32146645) B32146645
theorem B3344003 : Blo 1486063 3344003 := bstep (se 1 (by rfl) ⟨2508002, by rfl⟩ : syracuseStep 3344003 = 5016005) B5016005
theorem B2229905 : Blo 1486063 2229905 := bstep (se 2 (by rfl) ⟨836214, by rfl⟩ : syracuseStep 2229905 = 1672429) B1672429
theorem B2229923 : Blo 1486063 2229923 := bstep (se 1 (by rfl) ⟨1672442, by rfl⟩ : syracuseStep 2229923 = 3344885) B3344885
theorem B2229953 : Blo 1486063 2229953 := bstep (se 2 (by rfl) ⟨836232, by rfl⟩ : syracuseStep 2229953 = 1672465) B1672465
theorem B3761873 : Blo 1486063 3761873 := bstep (se 2 (by rfl) ⟨1410702, by rfl⟩ : syracuseStep 3761873 = 2821405) B2821405
theorem B2229971 : Blo 1486063 2229971 := bstep (se 1 (by rfl) ⟨1672478, by rfl⟩ : syracuseStep 2229971 = 3344957) B3344957
theorem B1672915 : Blo 1486063 1672915 := bstep (se 1 (by rfl) ⟨1254686, by rfl⟩ : syracuseStep 1672915 = 2509373) B2509373
theorem B2508529 : Blo 1486063 2508529 := bstep (se 2 (by rfl) ⟨940698, by rfl⟩ : syracuseStep 2508529 = 1881397) B1881397
theorem B2230001 : Blo 1486063 2230001 := bstep (se 2 (by rfl) ⟨836250, by rfl⟩ : syracuseStep 2230001 = 1672501) B1672501
theorem B3761923 : Blo 1486063 3761923 := bstep (se 1 (by rfl) ⟨2821442, by rfl⟩ : syracuseStep 3761923 = 5642885) B5642885
theorem B2230019 : Blo 1486063 2230019 := bstep (se 1 (by rfl) ⟨1672514, by rfl⟩ : syracuseStep 2230019 = 3345029) B3345029
theorem B16934669 : Blo 1486063 16934669 := bstep (se 3 (by rfl) ⟨3175250, by rfl⟩ : syracuseStep 16934669 = 6350501) B6350501
theorem B2508563 : Blo 1486063 2508563 := bstep (se 1 (by rfl) ⟨1881422, by rfl⟩ : syracuseStep 2508563 = 3762845) B3762845
theorem B2230049 : Blo 1486063 2230049 := bstep (se 2 (by rfl) ⟨836268, by rfl⟩ : syracuseStep 2230049 = 1672537) B1672537
theorem B2230067 : Blo 1486063 2230067 := bstep (se 1 (by rfl) ⟨1672550, by rfl⟩ : syracuseStep 2230067 = 3345101) B3345101
theorem B2230097 : Blo 1486063 2230097 := bstep (se 2 (by rfl) ⟨836286, by rfl⟩ : syracuseStep 2230097 = 1672573) B1672573
theorem B2230115 : Blo 1486063 2230115 := bstep (se 1 (by rfl) ⟨1672586, by rfl⟩ : syracuseStep 2230115 = 3345173) B3345173
theorem B1673059 : Blo 1486063 1673059 := bstep (se 1 (by rfl) ⟨1254794, by rfl⟩ : syracuseStep 1673059 = 2509589) B2509589
theorem B2230145 : Blo 1486063 2230145 := bstep (se 2 (by rfl) ⟨836304, by rfl⟩ : syracuseStep 2230145 = 1672609) B1672609
theorem B3762065 : Blo 1486063 3762065 := bstep (se 2 (by rfl) ⟨1410774, by rfl⟩ : syracuseStep 3762065 = 2821549) B2821549
theorem B3344273 : Blo 1486063 3344273 := bstep (se 2 (by rfl) ⟨1254102, by rfl⟩ : syracuseStep 3344273 = 2508205) B2508205
theorem B2508691 : Blo 1486063 2508691 := bstep (se 1 (by rfl) ⟨1881518, by rfl⟩ : syracuseStep 2508691 = 3763037) B3763037
theorem B2230163 : Blo 1486063 2230163 := bstep (se 1 (by rfl) ⟨1672622, by rfl⟩ : syracuseStep 2230163 = 3345245) B3345245
theorem B3344291 : Blo 1486063 3344291 := bstep (se 1 (by rfl) ⟨2508218, by rfl⟩ : syracuseStep 3344291 = 5016437) B5016437
theorem B2230193 : Blo 1486063 2230193 := bstep (se 2 (by rfl) ⟨836322, by rfl⟩ : syracuseStep 2230193 = 1672645) B1672645
theorem B5646257 : Blo 1486063 5646257 := bstep (se 2 (by rfl) ⟨2117346, by rfl⟩ : syracuseStep 5646257 = 4234693) B4234693
theorem B2230211 : Blo 1486063 2230211 := bstep (se 1 (by rfl) ⟨1672658, by rfl⟩ : syracuseStep 2230211 = 3345317) B3345317
theorem B2230241 : Blo 1486063 2230241 := bstep (se 2 (by rfl) ⟨836340, by rfl⟩ : syracuseStep 2230241 = 1672681) B1672681
theorem B2869219 : Blo 1486063 2869219 := bstep (se 1 (by rfl) ⟨2151914, by rfl⟩ : syracuseStep 2869219 = 4303829) B4303829
theorem B2230259 : Blo 1486063 2230259 := bstep (se 1 (by rfl) ⟨1672694, by rfl⟩ : syracuseStep 2230259 = 3345389) B3345389
theorem B1673203 : Blo 1486063 1673203 := bstep (se 1 (by rfl) ⟨1254902, by rfl⟩ : syracuseStep 1673203 = 2509805) B2509805
theorem B2230289 : Blo 1486063 2230289 := bstep (se 2 (by rfl) ⟨836358, by rfl⟩ : syracuseStep 2230289 = 1672717) B1672717
theorem B2508833 : Blo 1486063 2508833 := bstep (se 2 (by rfl) ⟨940812, by rfl⟩ : syracuseStep 2508833 = 1881625) B1881625
theorem B2230307 : Blo 1486063 2230307 := bstep (se 1 (by rfl) ⟨1672730, by rfl⟩ : syracuseStep 2230307 = 3345461) B3345461
theorem B2230337 : Blo 1486063 2230337 := bstep (se 2 (by rfl) ⟨836376, by rfl⟩ : syracuseStep 2230337 = 1672753) B1672753
theorem B4237393 : Blo 1486063 4237393 := bstep (se 2 (by rfl) ⟨1589022, by rfl⟩ : syracuseStep 4237393 = 3178045) B3178045
theorem B2230355 : Blo 1486063 2230355 := bstep (se 1 (by rfl) ⟨1672766, by rfl⟩ : syracuseStep 2230355 = 3345533) B3345533
theorem B3057763 : Blo 1486063 3057763 := bstep (se 1 (by rfl) ⟨2293322, by rfl⟩ : syracuseStep 3057763 = 4586645) B4586645
theorem B2230385 : Blo 1486063 2230385 := bstep (se 2 (by rfl) ⟨836394, by rfl⟩ : syracuseStep 2230385 = 1672789) B1672789
theorem B2230403 : Blo 1486063 2230403 := bstep (se 1 (by rfl) ⟨1672802, by rfl⟩ : syracuseStep 2230403 = 3345605) B3345605
theorem B1673347 : Blo 1486063 1673347 := bstep (se 1 (by rfl) ⟨1255010, by rfl⟩ : syracuseStep 1673347 = 2510021) B2510021
theorem B2508961 : Blo 1486063 2508961 := bstep (se 2 (by rfl) ⟨940860, by rfl⟩ : syracuseStep 2508961 = 1881721) B1881721
theorem B2230433 : Blo 1486063 2230433 := bstep (se 2 (by rfl) ⟨836412, by rfl⟩ : syracuseStep 2230433 = 1672825) B1672825
theorem B3344561 : Blo 1486063 3344561 := bstep (se 2 (by rfl) ⟨1254210, by rfl⟩ : syracuseStep 3344561 = 2508421) B2508421
theorem B2230451 : Blo 1486063 2230451 := bstep (se 1 (by rfl) ⟨1672838, by rfl⟩ : syracuseStep 2230451 = 3345677) B3345677
theorem B3344579 : Blo 1486063 3344579 := bstep (se 1 (by rfl) ⟨2508434, by rfl⟩ : syracuseStep 3344579 = 5016869) B5016869
theorem B2508995 : Blo 1486063 2508995 := bstep (se 1 (by rfl) ⟨1881746, by rfl⟩ : syracuseStep 2508995 = 3763493) B3763493
theorem B11299013 : Blo 1486063 11299013 := bstep (se 4 (by rfl) ⟨1059282, by rfl⟩ : syracuseStep 11299013 = 2118565) B2118565
theorem B2230481 : Blo 1486063 2230481 := bstep (se 2 (by rfl) ⟨836430, by rfl⟩ : syracuseStep 2230481 = 1672861) B1672861
theorem B2230499 : Blo 1486063 2230499 := bstep (se 1 (by rfl) ⟨1672874, by rfl⟩ : syracuseStep 2230499 = 3345749) B3345749
theorem B27519203 : Blo 1486063 27519203 := bstep (se 1 (by rfl) ⟨20639402, by rfl⟩ : syracuseStep 27519203 = 41278805) B41278805
theorem B5015789 : Blo 1486063 5015789 := bstep (se 3 (by rfl) ⟨940460, by rfl⟩ : syracuseStep 5015789 = 1880921) B1880921
theorem B2230529 : Blo 1486063 2230529 := bstep (se 2 (by rfl) ⟨836448, by rfl⟩ : syracuseStep 2230529 = 1672897) B1672897
theorem B2230547 : Blo 1486063 2230547 := bstep (se 1 (by rfl) ⟨1672910, by rfl⟩ : syracuseStep 2230547 = 3345821) B3345821
theorem B1673491 : Blo 1486063 1673491 := bstep (se 1 (by rfl) ⟨1255118, by rfl⟩ : syracuseStep 1673491 = 2510237) B2510237
theorem B5015843 : Blo 1486063 5015843 := bstep (se 1 (by rfl) ⟨3761882, by rfl⟩ : syracuseStep 5015843 = 7523765) B7523765
theorem B6785315 : Blo 1486063 6785315 := bstep (se 1 (by rfl) ⟨5088986, by rfl⟩ : syracuseStep 6785315 = 10177973) B10177973
theorem B2230577 : Blo 1486063 2230577 := bstep (se 2 (by rfl) ⟨836466, by rfl⟩ : syracuseStep 2230577 = 1672933) B1672933
theorem B9529649 : Blo 1486063 9529649 := bstep (se 2 (by rfl) ⟨3573618, by rfl⟩ : syracuseStep 9529649 = 7147237) B7147237
theorem B2681137 : Blo 1486063 2681137 := bstep (se 2 (by rfl) ⟨1005426, by rfl⟩ : syracuseStep 2681137 = 2010853) B2010853
theorem B2509123 : Blo 1486063 2509123 := bstep (se 1 (by rfl) ⟨1881842, by rfl⟩ : syracuseStep 2509123 = 3763685) B3763685
theorem B2230595 : Blo 1486063 2230595 := bstep (se 1 (by rfl) ⟨1672946, by rfl⟩ : syracuseStep 2230595 = 3345893) B3345893
theorem B2230625 : Blo 1486063 2230625 := bstep (se 2 (by rfl) ⟨836484, by rfl⟩ : syracuseStep 2230625 = 1672969) B1672969
theorem B2230643 : Blo 1486063 2230643 := bstep (se 1 (by rfl) ⟨1672982, by rfl⟩ : syracuseStep 2230643 = 3345965) B3345965
theorem B7530893 : Blo 1486063 7530893 := bstep (se 3 (by rfl) ⟨1412042, by rfl⟩ : syracuseStep 7530893 = 2824085) B2824085
theorem B2230673 : Blo 1486063 2230673 := bstep (se 2 (by rfl) ⟨836502, by rfl⟩ : syracuseStep 2230673 = 1673005) B1673005
theorem B2230691 : Blo 1486063 2230691 := bstep (se 1 (by rfl) ⟨1673018, by rfl⟩ : syracuseStep 2230691 = 3346037) B3346037
theorem B1673635 : Blo 1486063 1673635 := bstep (se 1 (by rfl) ⟨1255226, by rfl⟩ : syracuseStep 1673635 = 2510453) B2510453
theorem B2230721 : Blo 1486063 2230721 := bstep (se 2 (by rfl) ⟨836520, by rfl⟩ : syracuseStep 2230721 = 1673041) B1673041
theorem B61049285 : Blo 1486063 61049285 := bstep (se 4 (by rfl) ⟨5723370, by rfl⟩ : syracuseStep 61049285 = 11446741) B11446741
theorem B3344849 : Blo 1486063 3344849 := bstep (se 2 (by rfl) ⟨1254318, by rfl⟩ : syracuseStep 3344849 = 2508637) B2508637
theorem B2509265 : Blo 1486063 2509265 := bstep (se 2 (by rfl) ⟨940974, by rfl⟩ : syracuseStep 2509265 = 1881949) B1881949
theorem B2230739 : Blo 1486063 2230739 := bstep (se 1 (by rfl) ⟨1673054, by rfl⟩ : syracuseStep 2230739 = 3346109) B3346109
theorem B3344867 : Blo 1486063 3344867 := bstep (se 1 (by rfl) ⟨2508650, by rfl⟩ : syracuseStep 3344867 = 5017301) B5017301
theorem B4524515 : Blo 1486063 4524515 := bstep (se 1 (by rfl) ⟨3393386, by rfl⟩ : syracuseStep 4524515 = 6786773) B6786773
theorem B2230769 : Blo 1486063 2230769 := bstep (se 2 (by rfl) ⟨836538, by rfl⟩ : syracuseStep 2230769 = 1673077) B1673077
theorem B2230787 : Blo 1486063 2230787 := bstep (se 1 (by rfl) ⟨1673090, by rfl⟩ : syracuseStep 2230787 = 3346181) B3346181
theorem B2230817 : Blo 1486063 2230817 := bstep (se 2 (by rfl) ⟨836556, by rfl⟩ : syracuseStep 2230817 = 1673113) B1673113
theorem B4762147 : Blo 1486063 4762147 := bstep (se 1 (by rfl) ⟨3571610, by rfl⟩ : syracuseStep 4762147 = 7143221) B7143221
theorem B2116145 : Blo 1486063 2116145 := bstep (se 2 (by rfl) ⟨793554, by rfl⟩ : syracuseStep 2116145 = 1587109) B1587109
theorem B5016113 : Blo 1486063 5016113 := bstep (se 2 (by rfl) ⟨1881042, by rfl⟩ : syracuseStep 5016113 = 3762085) B3762085
theorem B2230835 : Blo 1486063 2230835 := bstep (se 1 (by rfl) ⟨1673126, by rfl⟩ : syracuseStep 2230835 = 3346253) B3346253
theorem B1673779 : Blo 1486063 1673779 := bstep (se 1 (by rfl) ⟨1255334, by rfl⟩ : syracuseStep 1673779 = 2510669) B2510669
theorem B2509393 : Blo 1486063 2509393 := bstep (se 2 (by rfl) ⟨941022, by rfl⟩ : syracuseStep 2509393 = 1882045) B1882045
theorem B2230865 : Blo 1486063 2230865 := bstep (se 2 (by rfl) ⟨836574, by rfl⟩ : syracuseStep 2230865 = 1673149) B1673149
theorem B7146083 : Blo 1486063 7146083 := bstep (se 1 (by rfl) ⟨5359562, by rfl⟩ : syracuseStep 7146083 = 10719125) B10719125
theorem B2230883 : Blo 1486063 2230883 := bstep (se 1 (by rfl) ⟨1673162, by rfl⟩ : syracuseStep 2230883 = 3346325) B3346325
theorem B2509427 : Blo 1486063 2509427 := bstep (se 1 (by rfl) ⟨1882070, by rfl⟩ : syracuseStep 2509427 = 3764141) B3764141
theorem B2230913 : Blo 1486063 2230913 := bstep (se 2 (by rfl) ⟨836592, by rfl⟩ : syracuseStep 2230913 = 1673185) B1673185
theorem B2230931 : Blo 1486063 2230931 := bstep (se 1 (by rfl) ⟨1673198, by rfl⟩ : syracuseStep 2230931 = 3346397) B3346397
theorem B2230961 : Blo 1486063 2230961 := bstep (se 2 (by rfl) ⟨836610, by rfl⟩ : syracuseStep 2230961 = 1673221) B1673221
theorem B2230979 : Blo 1486063 2230979 := bstep (se 1 (by rfl) ⟨1673234, by rfl⟩ : syracuseStep 2230979 = 3346469) B3346469
theorem B1673923 : Blo 1486063 1673923 := bstep (se 1 (by rfl) ⟨1255442, by rfl⟩ : syracuseStep 1673923 = 2510885) B2510885
theorem B2231009 : Blo 1486063 2231009 := bstep (se 2 (by rfl) ⟨836628, by rfl⟩ : syracuseStep 2231009 = 1673257) B1673257
theorem B3345137 : Blo 1486063 3345137 := bstep (se 2 (by rfl) ⟨1254426, by rfl⟩ : syracuseStep 3345137 = 2508853) B2508853
theorem B2509555 : Blo 1486063 2509555 := bstep (se 1 (by rfl) ⟨1882166, by rfl⟩ : syracuseStep 2509555 = 3764333) B3764333
theorem B2231027 : Blo 1486063 2231027 := bstep (se 1 (by rfl) ⟨1673270, by rfl⟩ : syracuseStep 2231027 = 3346541) B3346541
theorem B3345155 : Blo 1486063 3345155 := bstep (se 1 (by rfl) ⟨2508866, by rfl⟩ : syracuseStep 3345155 = 5017733) B5017733
theorem B8473349 : Blo 1486063 8473349 := bstep (se 4 (by rfl) ⟨794376, by rfl⟩ : syracuseStep 8473349 = 1588753) B1588753
theorem B2231057 : Blo 1486063 2231057 := bstep (se 2 (by rfl) ⟨836646, by rfl⟩ : syracuseStep 2231057 = 1673293) B1673293
theorem B2231075 : Blo 1486063 2231075 := bstep (se 1 (by rfl) ⟨1673306, by rfl⟩ : syracuseStep 2231075 = 3346613) B3346613
theorem B2231105 : Blo 1486063 2231105 := bstep (se 2 (by rfl) ⟨836664, by rfl⟩ : syracuseStep 2231105 = 1673329) B1673329
theorem B2231123 : Blo 1486063 2231123 := bstep (se 1 (by rfl) ⟨1673342, by rfl⟩ : syracuseStep 2231123 = 3346685) B3346685
theorem B1674067 : Blo 1486063 1674067 := bstep (se 1 (by rfl) ⟨1255550, by rfl⟩ : syracuseStep 1674067 = 2511101) B2511101
theorem B4582253 : Blo 1486063 4582253 := bstep (se 3 (by rfl) ⟨859172, by rfl⟩ : syracuseStep 4582253 = 1718345) B1718345
theorem B3763057 : Blo 1486063 3763057 := bstep (se 2 (by rfl) ⟨1411146, by rfl⟩ : syracuseStep 3763057 = 2822293) B2822293
theorem B2231153 : Blo 1486063 2231153 := bstep (se 2 (by rfl) ⟨836682, by rfl⟩ : syracuseStep 2231153 = 1673365) B1673365
theorem B2509697 : Blo 1486063 2509697 := bstep (se 2 (by rfl) ⟨941136, by rfl⟩ : syracuseStep 2509697 = 1882273) B1882273
theorem B2231171 : Blo 1486063 2231171 := bstep (se 1 (by rfl) ⟨1673378, by rfl⟩ : syracuseStep 2231171 = 3346757) B3346757
theorem B2231201 : Blo 1486063 2231201 := bstep (se 2 (by rfl) ⟨836700, by rfl⟩ : syracuseStep 2231201 = 1673401) B1673401
theorem B2231219 : Blo 1486063 2231219 := bstep (se 1 (by rfl) ⟨1673414, by rfl⟩ : syracuseStep 2231219 = 3346829) B3346829
theorem B2231249 : Blo 1486063 2231249 := bstep (se 2 (by rfl) ⟨836718, by rfl⟩ : syracuseStep 2231249 = 1673437) B1673437
theorem B2231267 : Blo 1486063 2231267 := bstep (se 1 (by rfl) ⟨1673450, by rfl⟩ : syracuseStep 2231267 = 3346901) B3346901
theorem B2509825 : Blo 1486063 2509825 := bstep (se 2 (by rfl) ⟨941184, by rfl⟩ : syracuseStep 2509825 = 1882369) B1882369
theorem B1608707 : Blo 1486063 1608707 := bstep (se 1 (by rfl) ⟨1206530, by rfl⟩ : syracuseStep 1608707 = 2413061) B2413061
theorem B2231297 : Blo 1486063 2231297 := bstep (se 2 (by rfl) ⟨836736, by rfl⟩ : syracuseStep 2231297 = 1673473) B1673473
theorem B3345425 : Blo 1486063 3345425 := bstep (se 2 (by rfl) ⟨1254534, by rfl⟩ : syracuseStep 3345425 = 2509069) B2509069
theorem B2231315 : Blo 1486063 2231315 := bstep (se 1 (by rfl) ⟨1673486, by rfl⟩ : syracuseStep 2231315 = 3346973) B3346973
theorem B3345443 : Blo 1486063 3345443 := bstep (se 1 (by rfl) ⟨2509082, by rfl⟩ : syracuseStep 3345443 = 5018165) B5018165
theorem B2509859 : Blo 1486063 2509859 := bstep (se 1 (by rfl) ⟨1882394, by rfl⟩ : syracuseStep 2509859 = 3764789) B3764789
theorem B2231345 : Blo 1486063 2231345 := bstep (se 2 (by rfl) ⟨836754, by rfl⟩ : syracuseStep 2231345 = 1673509) B1673509
theorem B2231363 : Blo 1486063 2231363 := bstep (se 1 (by rfl) ⟨1673522, by rfl⟩ : syracuseStep 2231363 = 3347045) B3347045
theorem B5016653 : Blo 1486063 5016653 := bstep (se 3 (by rfl) ⟨940622, by rfl⟩ : syracuseStep 5016653 = 1881245) B1881245
theorem B5360717 : Blo 1486063 5360717 := bstep (se 3 (by rfl) ⟨1005134, by rfl⟩ : syracuseStep 5360717 = 2010269) B2010269
theorem B2231393 : Blo 1486063 2231393 := bstep (se 2 (by rfl) ⟨836772, by rfl⟩ : syracuseStep 2231393 = 1673545) B1673545
theorem B7523441 : Blo 1486063 7523441 := bstep (se 2 (by rfl) ⟨2821290, by rfl⟩ : syracuseStep 7523441 = 5642581) B5642581
theorem B2231411 : Blo 1486063 2231411 := bstep (se 1 (by rfl) ⟨1673558, by rfl⟩ : syracuseStep 2231411 = 3347117) B3347117
theorem B5016707 : Blo 1486063 5016707 := bstep (se 1 (by rfl) ⟨3762530, by rfl⟩ : syracuseStep 5016707 = 7525061) B7525061
theorem B3763331 : Blo 1486063 3763331 := bstep (se 1 (by rfl) ⟨2822498, by rfl⟩ : syracuseStep 3763331 = 5644997) B5644997
theorem B2231441 : Blo 1486063 2231441 := bstep (se 2 (by rfl) ⟨836790, by rfl⟩ : syracuseStep 2231441 = 1673581) B1673581
theorem B9653411 : Blo 1486063 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B2509987 : Blo 1486063 2509987 := bstep (se 1 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 2509987 = 3764981) B3764981
theorem B2231459 : Blo 1486063 2231459 := bstep (se 1 (by rfl) ⟨1673594, by rfl⟩ : syracuseStep 2231459 = 3347189) B3347189
theorem B2231489 : Blo 1486063 2231489 := bstep (se 2 (by rfl) ⟨836808, by rfl⟩ : syracuseStep 2231489 = 1673617) B1673617
theorem B8473805 : Blo 1486063 8473805 := bstep (se 3 (by rfl) ⟨1588838, by rfl⟩ : syracuseStep 8473805 = 3177677) B3177677
theorem B2231507 : Blo 1486063 2231507 := bstep (se 1 (by rfl) ⟨1673630, by rfl⟩ : syracuseStep 2231507 = 3347261) B3347261
theorem B2231537 : Blo 1486063 2231537 := bstep (se 2 (by rfl) ⟨836826, by rfl⟩ : syracuseStep 2231537 = 1673653) B1673653
theorem B1486067 : Blo 1486063 1486067 := bstep (se 1 (by rfl) ⟨1114550, by rfl⟩ : syracuseStep 1486067 = 2229101) B2229101
theorem B1486083 : Blo 1486063 1486083 := bstep (se 1 (by rfl) ⟨1114562, by rfl⟩ : syracuseStep 1486083 = 2229125) B2229125
theorem B2231555 : Blo 1486063 2231555 := bstep (se 1 (by rfl) ⟨1673666, by rfl⟩ : syracuseStep 2231555 = 3347333) B3347333
theorem B1486099 : Blo 1486063 1486099 := bstep (se 1 (by rfl) ⟨1114574, by rfl⟩ : syracuseStep 1486099 = 2229149) B2229149
theorem B2231585 : Blo 1486063 2231585 := bstep (se 2 (by rfl) ⟨836844, by rfl⟩ : syracuseStep 2231585 = 1673689) B1673689
theorem B1486115 : Blo 1486063 1486115 := bstep (se 1 (by rfl) ⟨1114586, by rfl⟩ : syracuseStep 1486115 = 2229173) B2229173
theorem B3345713 : Blo 1486063 3345713 := bstep (se 2 (by rfl) ⟨1254642, by rfl⟩ : syracuseStep 3345713 = 2509285) B2509285
theorem B2510129 : Blo 1486063 2510129 := bstep (se 2 (by rfl) ⟨941298, by rfl⟩ : syracuseStep 2510129 = 1882597) B1882597
theorem B1486131 : Blo 1486063 1486131 := bstep (se 1 (by rfl) ⟨1114598, by rfl⟩ : syracuseStep 1486131 = 2229197) B2229197
theorem B2231603 : Blo 1486063 2231603 := bstep (se 1 (by rfl) ⟨1673702, by rfl⟩ : syracuseStep 2231603 = 3347405) B3347405
theorem B1486147 : Blo 1486063 1486147 := bstep (se 1 (by rfl) ⟨1114610, by rfl⟩ : syracuseStep 1486147 = 2229221) B2229221
theorem B3763523 : Blo 1486063 3763523 := bstep (se 1 (by rfl) ⟨2822642, by rfl⟩ : syracuseStep 3763523 = 5645285) B5645285
theorem B3345731 : Blo 1486063 3345731 := bstep (se 1 (by rfl) ⟨2509298, by rfl⟩ : syracuseStep 3345731 = 5018597) B5018597
theorem B8465741 : Blo 1486063 8465741 := bstep (se 3 (by rfl) ⟨1587326, by rfl⟩ : syracuseStep 8465741 = 3174653) B3174653
theorem B2231633 : Blo 1486063 2231633 := bstep (se 2 (by rfl) ⟨836862, by rfl⟩ : syracuseStep 2231633 = 1673725) B1673725
theorem B1486163 : Blo 1486063 1486163 := bstep (se 1 (by rfl) ⟨1114622, by rfl⟩ : syracuseStep 1486163 = 2229245) B2229245
theorem B1486179 : Blo 1486063 1486179 := bstep (se 1 (by rfl) ⟨1114634, by rfl⟩ : syracuseStep 1486179 = 2229269) B2229269
theorem B4762979 : Blo 1486063 4762979 := bstep (se 1 (by rfl) ⟨3572234, by rfl⟩ : syracuseStep 4762979 = 7144469) B7144469
theorem B5647715 : Blo 1486063 5647715 := bstep (se 1 (by rfl) ⟨4235786, by rfl⟩ : syracuseStep 5647715 = 8471573) B8471573
theorem B2231651 : Blo 1486063 2231651 := bstep (se 1 (by rfl) ⟨1673738, by rfl⟩ : syracuseStep 2231651 = 3347477) B3347477
theorem B1486195 : Blo 1486063 1486195 := bstep (se 1 (by rfl) ⟨1114646, by rfl⟩ : syracuseStep 1486195 = 2229293) B2229293
theorem B2231681 : Blo 1486063 2231681 := bstep (se 2 (by rfl) ⟨836880, by rfl⟩ : syracuseStep 2231681 = 1673761) B1673761
theorem B1486211 : Blo 1486063 1486211 := bstep (se 1 (by rfl) ⟨1114658, by rfl⟩ : syracuseStep 1486211 = 2229317) B2229317
theorem B5016977 : Blo 1486063 5016977 := bstep (se 2 (by rfl) ⟨1881366, by rfl⟩ : syracuseStep 5016977 = 3762733) B3762733
theorem B1486227 : Blo 1486063 1486227 := bstep (se 1 (by rfl) ⟨1114670, by rfl⟩ : syracuseStep 1486227 = 2229341) B2229341
theorem B2117011 : Blo 1486063 2117011 := bstep (se 1 (by rfl) ⟨1587758, by rfl⟩ : syracuseStep 2117011 = 3175517) B3175517
theorem B2231699 : Blo 1486063 2231699 := bstep (se 1 (by rfl) ⟨1673774, by rfl⟩ : syracuseStep 2231699 = 3347549) B3347549
theorem B1486243 : Blo 1486063 1486243 := bstep (se 1 (by rfl) ⟨1114682, by rfl⟩ : syracuseStep 1486243 = 2229365) B2229365
theorem B7146929 : Blo 1486063 7146929 := bstep (se 2 (by rfl) ⟨2680098, by rfl⟩ : syracuseStep 7146929 = 5360197) B5360197
theorem B2510257 : Blo 1486063 2510257 := bstep (se 2 (by rfl) ⟨941346, by rfl⟩ : syracuseStep 2510257 = 1882693) B1882693
theorem B1486259 : Blo 1486063 1486259 := bstep (se 1 (by rfl) ⟨1114694, by rfl⟩ : syracuseStep 1486259 = 2229389) B2229389
theorem B2231729 : Blo 1486063 2231729 := bstep (se 2 (by rfl) ⟨836898, by rfl⟩ : syracuseStep 2231729 = 1673797) B1673797
theorem B1486275 : Blo 1486063 1486275 := bstep (se 1 (by rfl) ⟨1114706, by rfl⟩ : syracuseStep 1486275 = 2229413) B2229413
theorem B2231747 : Blo 1486063 2231747 := bstep (se 1 (by rfl) ⟨1673810, by rfl⟩ : syracuseStep 2231747 = 3347621) B3347621
theorem B1486291 : Blo 1486063 1486291 := bstep (se 1 (by rfl) ⟨1114718, by rfl⟩ : syracuseStep 1486291 = 2229437) B2229437
theorem B2510291 : Blo 1486063 2510291 := bstep (se 1 (by rfl) ⟨1882718, by rfl⟩ : syracuseStep 2510291 = 3765437) B3765437
theorem B2231777 : Blo 1486063 2231777 := bstep (se 2 (by rfl) ⟨836916, by rfl⟩ : syracuseStep 2231777 = 1673833) B1673833
theorem B1486307 : Blo 1486063 1486307 := bstep (se 1 (by rfl) ⟨1114730, by rfl⟩ : syracuseStep 1486307 = 2229461) B2229461
theorem B1486323 : Blo 1486063 1486323 := bstep (se 1 (by rfl) ⟨1114742, by rfl⟩ : syracuseStep 1486323 = 2229485) B2229485
theorem B2117107 : Blo 1486063 2117107 := bstep (se 1 (by rfl) ⟨1587830, by rfl⟩ : syracuseStep 2117107 = 3175661) B3175661
theorem B2231795 : Blo 1486063 2231795 := bstep (se 1 (by rfl) ⟨1673846, by rfl⟩ : syracuseStep 2231795 = 3347693) B3347693
theorem B1486339 : Blo 1486063 1486339 := bstep (se 1 (by rfl) ⟨1114754, by rfl⟩ : syracuseStep 1486339 = 2229509) B2229509
theorem B2231825 : Blo 1486063 2231825 := bstep (se 2 (by rfl) ⟨836934, by rfl⟩ : syracuseStep 2231825 = 1673869) B1673869
theorem B1486355 : Blo 1486063 1486355 := bstep (se 1 (by rfl) ⟨1114766, by rfl⟩ : syracuseStep 1486355 = 2229533) B2229533
theorem B1486371 : Blo 1486063 1486371 := bstep (se 1 (by rfl) ⟨1114778, by rfl⟩ : syracuseStep 1486371 = 2229557) B2229557
theorem B2231843 : Blo 1486063 2231843 := bstep (se 1 (by rfl) ⟨1673882, by rfl⟩ : syracuseStep 2231843 = 3347765) B3347765
theorem B1486387 : Blo 1486063 1486387 := bstep (se 1 (by rfl) ⟨1114790, by rfl⟩ : syracuseStep 1486387 = 2229581) B2229581
theorem B2231873 : Blo 1486063 2231873 := bstep (se 2 (by rfl) ⟨836952, by rfl⟩ : syracuseStep 2231873 = 1673905) B1673905
theorem B1486403 : Blo 1486063 1486403 := bstep (se 1 (by rfl) ⟨1114802, by rfl⟩ : syracuseStep 1486403 = 2229605) B2229605
theorem B3346001 : Blo 1486063 3346001 := bstep (se 2 (by rfl) ⟨1254750, by rfl⟩ : syracuseStep 3346001 = 2509501) B2509501
theorem B1486419 : Blo 1486063 1486419 := bstep (se 1 (by rfl) ⟨1114814, by rfl⟩ : syracuseStep 1486419 = 2229629) B2229629
theorem B2510419 : Blo 1486063 2510419 := bstep (se 1 (by rfl) ⟨1882814, by rfl⟩ : syracuseStep 2510419 = 3765629) B3765629
theorem B2231891 : Blo 1486063 2231891 := bstep (se 1 (by rfl) ⟨1673918, by rfl⟩ : syracuseStep 2231891 = 3347837) B3347837
theorem B3173987 : Blo 1486063 3173987 := bstep (se 1 (by rfl) ⟨2380490, by rfl⟩ : syracuseStep 3173987 = 4760981) B4760981
theorem B1486435 : Blo 1486063 1486435 := bstep (se 1 (by rfl) ⟨1114826, by rfl⟩ : syracuseStep 1486435 = 2229653) B2229653
theorem B3346019 : Blo 1486063 3346019 := bstep (se 1 (by rfl) ⟨2509514, by rfl⟩ : syracuseStep 3346019 = 5019029) B5019029
theorem B2231921 : Blo 1486063 2231921 := bstep (se 2 (by rfl) ⟨836970, by rfl⟩ : syracuseStep 2231921 = 1673941) B1673941
theorem B1486451 : Blo 1486063 1486451 := bstep (se 1 (by rfl) ⟨1114838, by rfl⟩ : syracuseStep 1486451 = 2229677) B2229677
theorem B1486467 : Blo 1486063 1486467 := bstep (se 1 (by rfl) ⟨1114850, by rfl⟩ : syracuseStep 1486467 = 2229701) B2229701
theorem B2231939 : Blo 1486063 2231939 := bstep (se 1 (by rfl) ⟨1673954, by rfl⟩ : syracuseStep 2231939 = 3347909) B3347909
theorem B1486483 : Blo 1486063 1486483 := bstep (se 1 (by rfl) ⟨1114862, by rfl⟩ : syracuseStep 1486483 = 2229725) B2229725
theorem B2231969 : Blo 1486063 2231969 := bstep (se 2 (by rfl) ⟨836988, by rfl⟩ : syracuseStep 2231969 = 1673977) B1673977
theorem B1486499 : Blo 1486063 1486499 := bstep (se 1 (by rfl) ⟨1114874, by rfl⟩ : syracuseStep 1486499 = 2229749) B2229749
theorem B1486515 : Blo 1486063 1486515 := bstep (se 1 (by rfl) ⟨1114886, by rfl⟩ : syracuseStep 1486515 = 2229773) B2229773
theorem B2231987 : Blo 1486063 2231987 := bstep (se 1 (by rfl) ⟨1673990, by rfl⟩ : syracuseStep 2231987 = 3347981) B3347981
theorem B1486531 : Blo 1486063 1486531 := bstep (se 1 (by rfl) ⟨1114898, by rfl⟩ : syracuseStep 1486531 = 2229797) B2229797
theorem B2232017 : Blo 1486063 2232017 := bstep (se 2 (by rfl) ⟨837006, by rfl⟩ : syracuseStep 2232017 = 1674013) B1674013
theorem B1486547 : Blo 1486063 1486547 := bstep (se 1 (by rfl) ⟨1114910, by rfl⟩ : syracuseStep 1486547 = 2229821) B2229821
theorem B1486563 : Blo 1486063 1486563 := bstep (se 1 (by rfl) ⟨1114922, by rfl⟩ : syracuseStep 1486563 = 2229845) B2229845
theorem B2510561 : Blo 1486063 2510561 := bstep (se 2 (by rfl) ⟨941460, by rfl⟩ : syracuseStep 2510561 = 1882921) B1882921
theorem B2232035 : Blo 1486063 2232035 := bstep (se 1 (by rfl) ⟨1674026, by rfl⟩ : syracuseStep 2232035 = 3348053) B3348053
theorem B4763377 : Blo 1486063 4763377 := bstep (se 2 (by rfl) ⟨1786266, by rfl⟩ : syracuseStep 4763377 = 3572533) B3572533
theorem B3264241 : Blo 1486063 3264241 := bstep (se 2 (by rfl) ⟨1224090, by rfl⟩ : syracuseStep 3264241 = 2448181) B2448181
theorem B1486579 : Blo 1486063 1486579 := bstep (se 1 (by rfl) ⟨1114934, by rfl⟩ : syracuseStep 1486579 = 2229869) B2229869
theorem B2232065 : Blo 1486063 2232065 := bstep (se 2 (by rfl) ⟨837024, by rfl⟩ : syracuseStep 2232065 = 1674049) B1674049
theorem B2821891 : Blo 1486063 2821891 := bstep (se 1 (by rfl) ⟨2116418, by rfl⟩ : syracuseStep 2821891 = 4232837) B4232837
theorem B1486595 : Blo 1486063 1486595 := bstep (se 1 (by rfl) ⟨1114946, by rfl⟩ : syracuseStep 1486595 = 2229893) B2229893
theorem B7147277 : Blo 1486063 7147277 := bstep (se 3 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 7147277 = 2680229) B2680229
theorem B1486611 : Blo 1486063 1486611 := bstep (se 1 (by rfl) ⟨1114958, by rfl⟩ : syracuseStep 1486611 = 2229917) B2229917
theorem B2232083 : Blo 1486063 2232083 := bstep (se 1 (by rfl) ⟨1674062, by rfl⟩ : syracuseStep 2232083 = 3348125) B3348125
theorem B1486627 : Blo 1486063 1486627 := bstep (se 1 (by rfl) ⟨1114970, by rfl⟩ : syracuseStep 1486627 = 2229941) B2229941
theorem B4763441 : Blo 1486063 4763441 := bstep (se 2 (by rfl) ⟨1786290, by rfl⟩ : syracuseStep 4763441 = 3572581) B3572581
theorem B1486643 : Blo 1486063 1486643 := bstep (se 1 (by rfl) ⟨1114982, by rfl⟩ : syracuseStep 1486643 = 2229965) B2229965
theorem B1486659 : Blo 1486063 1486659 := bstep (se 1 (by rfl) ⟨1114994, by rfl⟩ : syracuseStep 1486659 = 2229989) B2229989
theorem B1486675 : Blo 1486063 1486675 := bstep (se 1 (by rfl) ⟨1115006, by rfl⟩ : syracuseStep 1486675 = 2230013) B2230013
theorem B2510689 : Blo 1486063 2510689 := bstep (se 2 (by rfl) ⟨941508, by rfl⟩ : syracuseStep 2510689 = 1883017) B1883017
theorem B1486691 : Blo 1486063 1486691 := bstep (se 1 (by rfl) ⟨1115018, by rfl⟩ : syracuseStep 1486691 = 2230037) B2230037
theorem B3346289 : Blo 1486063 3346289 := bstep (se 2 (by rfl) ⟨1254858, by rfl⟩ : syracuseStep 3346289 = 2509717) B2509717
theorem B1486707 : Blo 1486063 1486707 := bstep (se 1 (by rfl) ⟨1115030, by rfl⟩ : syracuseStep 1486707 = 2230061) B2230061
theorem B1486723 : Blo 1486063 1486723 := bstep (se 1 (by rfl) ⟨1115042, by rfl⟩ : syracuseStep 1486723 = 2230085) B2230085
theorem B3346307 : Blo 1486063 3346307 := bstep (se 1 (by rfl) ⟨2509730, by rfl⟩ : syracuseStep 3346307 = 5019461) B5019461
theorem B2510723 : Blo 1486063 2510723 := bstep (se 1 (by rfl) ⟨1883042, by rfl⟩ : syracuseStep 2510723 = 3766085) B3766085
theorem B1486739 : Blo 1486063 1486739 := bstep (se 1 (by rfl) ⟨1115054, by rfl⟩ : syracuseStep 1486739 = 2230109) B2230109
theorem B1486755 : Blo 1486063 1486755 := bstep (se 1 (by rfl) ⟨1115066, by rfl⟩ : syracuseStep 1486755 = 2230133) B2230133
theorem B5017517 : Blo 1486063 5017517 := bstep (se 3 (by rfl) ⟨940784, by rfl⟩ : syracuseStep 5017517 = 1881569) B1881569
theorem B1486771 : Blo 1486063 1486771 := bstep (se 1 (by rfl) ⟨1115078, by rfl⟩ : syracuseStep 1486771 = 2230157) B2230157
theorem B1486787 : Blo 1486063 1486787 := bstep (se 1 (by rfl) ⟨1115090, by rfl⟩ : syracuseStep 1486787 = 2230181) B2230181
theorem B9531341 : Blo 1486063 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B1486803 : Blo 1486063 1486803 := bstep (se 1 (by rfl) ⟨1115102, by rfl⟩ : syracuseStep 1486803 = 2230205) B2230205
theorem B5017571 : Blo 1486063 5017571 := bstep (se 1 (by rfl) ⟨3763178, by rfl⟩ : syracuseStep 5017571 = 7526357) B7526357
theorem B1486819 : Blo 1486063 1486819 := bstep (se 1 (by rfl) ⟨1115114, by rfl⟩ : syracuseStep 1486819 = 2230229) B2230229
theorem B2117603 : Blo 1486063 2117603 := bstep (se 1 (by rfl) ⟨1588202, by rfl⟩ : syracuseStep 2117603 = 3176405) B3176405
theorem B1486835 : Blo 1486063 1486835 := bstep (se 1 (by rfl) ⟨1115126, by rfl⟩ : syracuseStep 1486835 = 2230253) B2230253
theorem B1486851 : Blo 1486063 1486851 := bstep (se 1 (by rfl) ⟨1115138, by rfl⟩ : syracuseStep 1486851 = 2230277) B2230277
theorem B2510851 : Blo 1486063 2510851 := bstep (se 1 (by rfl) ⟨1883138, by rfl⟩ : syracuseStep 2510851 = 3766277) B3766277
theorem B1486867 : Blo 1486063 1486867 := bstep (se 1 (by rfl) ⟨1115150, by rfl⟩ : syracuseStep 1486867 = 2230301) B2230301
theorem B1486883 : Blo 1486063 1486883 := bstep (se 1 (by rfl) ⟨1115162, by rfl⟩ : syracuseStep 1486883 = 2230325) B2230325
theorem B1486899 : Blo 1486063 1486899 := bstep (se 1 (by rfl) ⟨1115174, by rfl⟩ : syracuseStep 1486899 = 2230349) B2230349
theorem B1486915 : Blo 1486063 1486915 := bstep (se 1 (by rfl) ⟨1115186, by rfl⟩ : syracuseStep 1486915 = 2230373) B2230373
theorem B16928837 : Blo 1486063 16928837 := bstep (se 4 (by rfl) ⟨1587078, by rfl⟩ : syracuseStep 16928837 = 3174157) B3174157
theorem B1486931 : Blo 1486063 1486931 := bstep (se 1 (by rfl) ⟨1115198, by rfl⟩ : syracuseStep 1486931 = 2230397) B2230397
theorem B3174499 : Blo 1486063 3174499 := bstep (se 1 (by rfl) ⟨2380874, by rfl⟩ : syracuseStep 3174499 = 4761749) B4761749
theorem B1486947 : Blo 1486063 1486947 := bstep (se 1 (by rfl) ⟨1115210, by rfl⟩ : syracuseStep 1486947 = 2230421) B2230421
theorem B1486963 : Blo 1486063 1486963 := bstep (se 1 (by rfl) ⟨1115222, by rfl⟩ : syracuseStep 1486963 = 2230445) B2230445
theorem B1486979 : Blo 1486063 1486979 := bstep (se 1 (by rfl) ⟨1115234, by rfl⟩ : syracuseStep 1486979 = 2230469) B2230469
theorem B3346577 : Blo 1486063 3346577 := bstep (se 2 (by rfl) ⟨1254966, by rfl⟩ : syracuseStep 3346577 = 2509933) B2509933
theorem B2510993 : Blo 1486063 2510993 := bstep (se 2 (by rfl) ⟨941622, by rfl⟩ : syracuseStep 2510993 = 1883245) B1883245
theorem B1486995 : Blo 1486063 1486995 := bstep (se 1 (by rfl) ⟨1115246, by rfl⟩ : syracuseStep 1486995 = 2230493) B2230493
theorem B1487011 : Blo 1486063 1487011 := bstep (se 1 (by rfl) ⟨1115258, by rfl⟩ : syracuseStep 1487011 = 2230517) B2230517
theorem B3346595 : Blo 1486063 3346595 := bstep (se 1 (by rfl) ⟨2509946, by rfl⟩ : syracuseStep 3346595 = 5019893) B5019893
theorem B1487027 : Blo 1486063 1487027 := bstep (se 1 (by rfl) ⟨1115270, by rfl⟩ : syracuseStep 1487027 = 2230541) B2230541
theorem B2822339 : Blo 1486063 2822339 := bstep (se 1 (by rfl) ⟨2116754, by rfl⟩ : syracuseStep 2822339 = 4233509) B4233509
theorem B1487043 : Blo 1486063 1487043 := bstep (se 1 (by rfl) ⟨1115282, by rfl⟩ : syracuseStep 1487043 = 2230565) B2230565
theorem B19058885 : Blo 1486063 19058885 := bstep (se 4 (by rfl) ⟨1786770, by rfl⟩ : syracuseStep 19058885 = 3573541) B3573541
theorem B5025997 : Blo 1486063 5025997 := bstep (se 3 (by rfl) ⟨942374, by rfl⟩ : syracuseStep 5025997 = 1884749) B1884749
theorem B6025421 : Blo 1486063 6025421 := bstep (se 3 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 6025421 = 2259533) B2259533
theorem B1487059 : Blo 1486063 1487059 := bstep (se 1 (by rfl) ⟨1115294, by rfl⟩ : syracuseStep 1487059 = 2230589) B2230589
theorem B1487075 : Blo 1486063 1487075 := bstep (se 1 (by rfl) ⟨1115306, by rfl⟩ : syracuseStep 1487075 = 2230613) B2230613
theorem B5017841 : Blo 1486063 5017841 := bstep (se 2 (by rfl) ⟨1881690, by rfl⟩ : syracuseStep 5017841 = 3763381) B3763381
theorem B3764465 : Blo 1486063 3764465 := bstep (se 2 (by rfl) ⟨1411674, by rfl⟩ : syracuseStep 3764465 = 2823349) B2823349
theorem B1487091 : Blo 1486063 1487091 := bstep (se 1 (by rfl) ⟨1115318, by rfl⟩ : syracuseStep 1487091 = 2230637) B2230637
theorem B1487107 : Blo 1486063 1487107 := bstep (se 1 (by rfl) ⟨1115330, by rfl⟩ : syracuseStep 1487107 = 2230661) B2230661
theorem B1487123 : Blo 1486063 1487123 := bstep (se 1 (by rfl) ⟨1115342, by rfl⟩ : syracuseStep 1487123 = 2230685) B2230685
theorem B1487139 : Blo 1486063 1487139 := bstep (se 1 (by rfl) ⟨1115354, by rfl⟩ : syracuseStep 1487139 = 2230709) B2230709
theorem B3764515 : Blo 1486063 3764515 := bstep (se 1 (by rfl) ⟨2823386, by rfl⟩ : syracuseStep 3764515 = 5646773) B5646773
theorem B1487155 : Blo 1486063 1487155 := bstep (se 1 (by rfl) ⟨1115366, by rfl⟩ : syracuseStep 1487155 = 2230733) B2230733
theorem B1487171 : Blo 1486063 1487171 := bstep (se 1 (by rfl) ⟨1115378, by rfl⟩ : syracuseStep 1487171 = 2230757) B2230757
theorem B5648717 : Blo 1486063 5648717 := bstep (se 3 (by rfl) ⟨1059134, by rfl⟩ : syracuseStep 5648717 = 2118269) B2118269
theorem B1487187 : Blo 1486063 1487187 := bstep (se 1 (by rfl) ⟨1115390, by rfl⟩ : syracuseStep 1487187 = 2230781) B2230781
theorem B1487203 : Blo 1486063 1487203 := bstep (se 1 (by rfl) ⟨1115402, by rfl⟩ : syracuseStep 1487203 = 2230805) B2230805
theorem B1487219 : Blo 1486063 1487219 := bstep (se 1 (by rfl) ⟨1115414, by rfl⟩ : syracuseStep 1487219 = 2230829) B2230829
theorem B1487235 : Blo 1486063 1487235 := bstep (se 1 (by rfl) ⟨1115426, by rfl⟩ : syracuseStep 1487235 = 2230853) B2230853
theorem B1487251 : Blo 1486063 1487251 := bstep (se 1 (by rfl) ⟨1115438, by rfl⟩ : syracuseStep 1487251 = 2230877) B2230877
theorem B1487267 : Blo 1486063 1487267 := bstep (se 1 (by rfl) ⟨1115450, by rfl⟩ : syracuseStep 1487267 = 2230901) B2230901
theorem B3764657 : Blo 1486063 3764657 := bstep (se 2 (by rfl) ⟨1411746, by rfl⟩ : syracuseStep 3764657 = 2823493) B2823493
theorem B3346865 : Blo 1486063 3346865 := bstep (se 2 (by rfl) ⟨1255074, by rfl⟩ : syracuseStep 3346865 = 2510149) B2510149
theorem B1487283 : Blo 1486063 1487283 := bstep (se 1 (by rfl) ⟨1115462, by rfl⟩ : syracuseStep 1487283 = 2230925) B2230925
theorem B1487299 : Blo 1486063 1487299 := bstep (se 1 (by rfl) ⟨1115474, by rfl⟩ : syracuseStep 1487299 = 2230949) B2230949
theorem B3346883 : Blo 1486063 3346883 := bstep (se 1 (by rfl) ⟨2510162, by rfl⟩ : syracuseStep 3346883 = 5020325) B5020325
theorem B19313093 : Blo 1486063 19313093 := bstep (se 4 (by rfl) ⟨1810602, by rfl⟩ : syracuseStep 19313093 = 3621205) B3621205
theorem B1487315 : Blo 1486063 1487315 := bstep (se 1 (by rfl) ⟨1115486, by rfl⟩ : syracuseStep 1487315 = 2230973) B2230973
theorem B2822627 : Blo 1486063 2822627 := bstep (se 1 (by rfl) ⟨2116970, by rfl⟩ : syracuseStep 2822627 = 4233941) B4233941
theorem B1487331 : Blo 1486063 1487331 := bstep (se 1 (by rfl) ⟨1115498, by rfl⟩ : syracuseStep 1487331 = 2230997) B2230997
theorem B1487347 : Blo 1486063 1487347 := bstep (se 1 (by rfl) ⟨1115510, by rfl⟩ : syracuseStep 1487347 = 2231021) B2231021
theorem B2036227 : Blo 1486063 2036227 := bstep (se 1 (by rfl) ⟨1527170, by rfl⟩ : syracuseStep 2036227 = 3054341) B3054341
theorem B1487363 : Blo 1486063 1487363 := bstep (se 1 (by rfl) ⟨1115522, by rfl⟩ : syracuseStep 1487363 = 2231045) B2231045
theorem B1487379 : Blo 1486063 1487379 := bstep (se 1 (by rfl) ⟨1115534, by rfl⟩ : syracuseStep 1487379 = 2231069) B2231069
theorem B2445857 : Blo 1486063 2445857 := bstep (se 2 (by rfl) ⟨917196, by rfl⟩ : syracuseStep 2445857 = 1834393) B1834393
theorem B7524899 : Blo 1486063 7524899 := bstep (se 1 (by rfl) ⟨5643674, by rfl⟩ : syracuseStep 7524899 = 11287349) B11287349
theorem B1487395 : Blo 1486063 1487395 := bstep (se 1 (by rfl) ⟨1115546, by rfl⟩ : syracuseStep 1487395 = 2231093) B2231093
theorem B10179121 : Blo 1486063 10179121 := bstep (se 2 (by rfl) ⟨3817170, by rfl⟩ : syracuseStep 10179121 = 7634341) B7634341
theorem B1487411 : Blo 1486063 1487411 := bstep (se 1 (by rfl) ⟨1115558, by rfl⟩ : syracuseStep 1487411 = 2231117) B2231117
theorem B1487427 : Blo 1486063 1487427 := bstep (se 1 (by rfl) ⟨1115570, by rfl⟩ : syracuseStep 1487427 = 2231141) B2231141
theorem B1487443 : Blo 1486063 1487443 := bstep (se 1 (by rfl) ⟨1115582, by rfl⟩ : syracuseStep 1487443 = 2231165) B2231165
theorem B2118241 : Blo 1486063 2118241 := bstep (se 2 (by rfl) ⟨794340, by rfl⟩ : syracuseStep 2118241 = 1588681) B1588681
theorem B1487459 : Blo 1486063 1487459 := bstep (se 1 (by rfl) ⟨1115594, by rfl⟩ : syracuseStep 1487459 = 2231189) B2231189
theorem B16937585 : Blo 1486063 16937585 := bstep (se 2 (by rfl) ⟨6351594, by rfl⟩ : syracuseStep 16937585 = 12703189) B12703189
theorem B1487475 : Blo 1486063 1487475 := bstep (se 1 (by rfl) ⟨1115606, by rfl⟩ : syracuseStep 1487475 = 2231213) B2231213
theorem B1487491 : Blo 1486063 1487491 := bstep (se 1 (by rfl) ⟨1115618, by rfl⟩ : syracuseStep 1487491 = 2231237) B2231237
theorem B1487507 : Blo 1486063 1487507 := bstep (se 1 (by rfl) ⟨1115630, by rfl⟩ : syracuseStep 1487507 = 2231261) B2231261
theorem B1487523 : Blo 1486063 1487523 := bstep (se 1 (by rfl) ⟨1115642, by rfl⟩ : syracuseStep 1487523 = 2231285) B2231285
theorem B1487539 : Blo 1486063 1487539 := bstep (se 1 (by rfl) ⟨1115654, by rfl⟩ : syracuseStep 1487539 = 2231309) B2231309
theorem B1487555 : Blo 1486063 1487555 := bstep (se 1 (by rfl) ⟨1115666, by rfl⟩ : syracuseStep 1487555 = 2231333) B2231333
theorem B3347153 : Blo 1486063 3347153 := bstep (se 2 (by rfl) ⟨1255182, by rfl⟩ : syracuseStep 3347153 = 2510365) B2510365
theorem B1487571 : Blo 1486063 1487571 := bstep (se 1 (by rfl) ⟨1115678, by rfl⟩ : syracuseStep 1487571 = 2231357) B2231357
theorem B1487587 : Blo 1486063 1487587 := bstep (se 1 (by rfl) ⟨1115690, by rfl⟩ : syracuseStep 1487587 = 2231381) B2231381
theorem B3347171 : Blo 1486063 3347171 := bstep (se 1 (by rfl) ⟨2510378, by rfl⟩ : syracuseStep 3347171 = 5020757) B5020757
theorem B2380529 : Blo 1486063 2380529 := bstep (se 2 (by rfl) ⟨892698, by rfl⟩ : syracuseStep 2380529 = 1785397) B1785397
theorem B1487603 : Blo 1486063 1487603 := bstep (se 1 (by rfl) ⟨1115702, by rfl⟩ : syracuseStep 1487603 = 2231405) B2231405
theorem B1487619 : Blo 1486063 1487619 := bstep (se 1 (by rfl) ⟨1115714, by rfl⟩ : syracuseStep 1487619 = 2231429) B2231429
theorem B5018381 : Blo 1486063 5018381 := bstep (se 3 (by rfl) ⟨940946, by rfl⟩ : syracuseStep 5018381 = 1881893) B1881893
theorem B1487635 : Blo 1486063 1487635 := bstep (se 1 (by rfl) ⟨1115726, by rfl⟩ : syracuseStep 1487635 = 2231453) B2231453
theorem B1487651 : Blo 1486063 1487651 := bstep (se 1 (by rfl) ⟨1115738, by rfl⟩ : syracuseStep 1487651 = 2231477) B2231477
theorem B3175217 : Blo 1486063 3175217 := bstep (se 2 (by rfl) ⟨1190706, by rfl⟩ : syracuseStep 3175217 = 2381413) B2381413
theorem B1487667 : Blo 1486063 1487667 := bstep (se 1 (by rfl) ⟨1115750, by rfl⟩ : syracuseStep 1487667 = 2231501) B2231501
theorem B36680501 : Blo 1486063 36680501 := bstep (se 5 (by rfl) ⟨1719398, by rfl⟩ : syracuseStep 36680501 = 3438797) B3438797
theorem B5018435 : Blo 1486063 5018435 := bstep (se 1 (by rfl) ⟨3763826, by rfl⟩ : syracuseStep 5018435 = 7527653) B7527653
theorem B1487683 : Blo 1486063 1487683 := bstep (se 1 (by rfl) ⟨1115762, by rfl⟩ : syracuseStep 1487683 = 2231525) B2231525
theorem B14299973 : Blo 1486063 14299973 := bstep (se 4 (by rfl) ⟨1340622, by rfl⟩ : syracuseStep 14299973 = 2681245) B2681245
theorem B1487699 : Blo 1486063 1487699 := bstep (se 1 (by rfl) ⟨1115774, by rfl⟩ : syracuseStep 1487699 = 2231549) B2231549
theorem B8041315 : Blo 1486063 8041315 := bstep (se 1 (by rfl) ⟨6030986, by rfl⟩ : syracuseStep 8041315 = 12061973) B12061973
theorem B1487715 : Blo 1486063 1487715 := bstep (se 1 (by rfl) ⟨1115786, by rfl⟩ : syracuseStep 1487715 = 2231573) B2231573
theorem B1487731 : Blo 1486063 1487731 := bstep (se 1 (by rfl) ⟨1115798, by rfl⟩ : syracuseStep 1487731 = 2231597) B2231597
theorem B1487747 : Blo 1486063 1487747 := bstep (se 1 (by rfl) ⟨1115810, by rfl⟩ : syracuseStep 1487747 = 2231621) B2231621
theorem B1487763 : Blo 1486063 1487763 := bstep (se 1 (by rfl) ⟨1115822, by rfl⟩ : syracuseStep 1487763 = 2231645) B2231645
theorem B1487779 : Blo 1486063 1487779 := bstep (se 1 (by rfl) ⟨1115834, by rfl⟩ : syracuseStep 1487779 = 2231669) B2231669
theorem B2118577 : Blo 1486063 2118577 := bstep (se 2 (by rfl) ⟨794466, by rfl⟩ : syracuseStep 2118577 = 1588933) B1588933
theorem B1487795 : Blo 1486063 1487795 := bstep (se 1 (by rfl) ⟨1115846, by rfl⟩ : syracuseStep 1487795 = 2231693) B2231693
theorem B1487811 : Blo 1486063 1487811 := bstep (se 1 (by rfl) ⟨1115858, by rfl⟩ : syracuseStep 1487811 = 2231717) B2231717
theorem B1487827 : Blo 1486063 1487827 := bstep (se 1 (by rfl) ⟨1115870, by rfl⟩ : syracuseStep 1487827 = 2231741) B2231741
theorem B11293667 : Blo 1486063 11293667 := bstep (se 1 (by rfl) ⟨8470250, by rfl⟩ : syracuseStep 11293667 = 16940501) B16940501
theorem B1487843 : Blo 1486063 1487843 := bstep (se 1 (by rfl) ⟨1115882, by rfl⟩ : syracuseStep 1487843 = 2231765) B2231765
theorem B3347441 : Blo 1486063 3347441 := bstep (se 2 (by rfl) ⟨1255290, by rfl⟩ : syracuseStep 3347441 = 2510581) B2510581
theorem B1487859 : Blo 1486063 1487859 := bstep (se 1 (by rfl) ⟨1115894, by rfl⟩ : syracuseStep 1487859 = 2231789) B2231789
theorem B3347459 : Blo 1486063 3347459 := bstep (se 1 (by rfl) ⟨2510594, by rfl⟩ : syracuseStep 3347459 = 5021189) B5021189
theorem B1487875 : Blo 1486063 1487875 := bstep (se 1 (by rfl) ⟨1115906, by rfl⟩ : syracuseStep 1487875 = 2231813) B2231813
theorem B1487891 : Blo 1486063 1487891 := bstep (se 1 (by rfl) ⟨1115918, by rfl⟩ : syracuseStep 1487891 = 2231837) B2231837
theorem B1487907 : Blo 1486063 1487907 := bstep (se 1 (by rfl) ⟨1115930, by rfl⟩ : syracuseStep 1487907 = 2231861) B2231861
theorem B2479153 : Blo 1486063 2479153 := bstep (se 2 (by rfl) ⟨929682, by rfl⟩ : syracuseStep 2479153 = 1859365) B1859365
theorem B1881139 : Blo 1486063 1881139 := bstep (se 1 (by rfl) ⟨1410854, by rfl⟩ : syracuseStep 1881139 = 2821709) B2821709
theorem B1487923 : Blo 1486063 1487923 := bstep (se 1 (by rfl) ⟨1115942, by rfl⟩ : syracuseStep 1487923 = 2231885) B2231885
theorem B25408565 : Blo 1486063 25408565 := bstep (se 5 (by rfl) ⟨1191026, by rfl⟩ : syracuseStep 25408565 = 2382053) B2382053
theorem B1487939 : Blo 1486063 1487939 := bstep (se 1 (by rfl) ⟨1115954, by rfl⟩ : syracuseStep 1487939 = 2231909) B2231909
theorem B5018705 : Blo 1486063 5018705 := bstep (se 2 (by rfl) ⟨1882014, by rfl⟩ : syracuseStep 5018705 = 3764029) B3764029
theorem B1487955 : Blo 1486063 1487955 := bstep (se 1 (by rfl) ⟨1115966, by rfl⟩ : syracuseStep 1487955 = 2231933) B2231933
theorem B1487971 : Blo 1486063 1487971 := bstep (se 1 (by rfl) ⟨1115978, by rfl⟩ : syracuseStep 1487971 = 2231957) B2231957
theorem B1487987 : Blo 1486063 1487987 := bstep (se 1 (by rfl) ⟨1115990, by rfl⟩ : syracuseStep 1487987 = 2231981) B2231981
theorem B1488003 : Blo 1486063 1488003 := bstep (se 1 (by rfl) ⟨1116002, by rfl⟩ : syracuseStep 1488003 = 2232005) B2232005
theorem B1881235 : Blo 1486063 1881235 := bstep (se 1 (by rfl) ⟨1410926, by rfl⟩ : syracuseStep 1881235 = 2821853) B2821853
theorem B1488019 : Blo 1486063 1488019 := bstep (se 1 (by rfl) ⟨1116014, by rfl⟩ : syracuseStep 1488019 = 2232029) B2232029
theorem B1488035 : Blo 1486063 1488035 := bstep (se 1 (by rfl) ⟨1116026, by rfl⟩ : syracuseStep 1488035 = 2232053) B2232053
theorem B1488051 : Blo 1486063 1488051 := bstep (se 1 (by rfl) ⟨1116038, by rfl⟩ : syracuseStep 1488051 = 2232077) B2232077
theorem B6354125 : Blo 1486063 6354125 := bstep (se 3 (by rfl) ⟨1191398, by rfl⟩ : syracuseStep 6354125 = 2382797) B2382797
theorem B4830445 : Blo 1486063 4830445 := bstep (se 3 (by rfl) ⟨905708, by rfl⟩ : syracuseStep 4830445 = 1811417) B1811417
theorem B3347729 : Blo 1486063 3347729 := bstep (se 2 (by rfl) ⟨1255398, by rfl⟩ : syracuseStep 3347729 = 2510797) B2510797
theorem B4232483 : Blo 1486063 4232483 := bstep (se 1 (by rfl) ⟨3174362, by rfl⟩ : syracuseStep 4232483 = 6348725) B6348725
theorem B3347747 : Blo 1486063 3347747 := bstep (se 1 (by rfl) ⟨2510810, by rfl⟩ : syracuseStep 3347747 = 5021621) B5021621
theorem B7525709 : Blo 1486063 7525709 := bstep (se 3 (by rfl) ⟨1411070, by rfl⟩ : syracuseStep 7525709 = 2822141) B2822141
theorem B2823569 : Blo 1486063 2823569 := bstep (se 2 (by rfl) ⟨1058838, by rfl⟩ : syracuseStep 2823569 = 2117677) B2117677
theorem B3765649 : Blo 1486063 3765649 := bstep (se 2 (by rfl) ⟨1412118, by rfl⟩ : syracuseStep 3765649 = 2824237) B2824237
theorem B8467973 : Blo 1486063 8467973 := bstep (se 4 (by rfl) ⟨793872, by rfl⟩ : syracuseStep 8467973 = 1587745) B1587745
theorem B4077101 : Blo 1486063 4077101 := bstep (se 3 (by rfl) ⟨764456, by rfl⟩ : syracuseStep 4077101 = 1528913) B1528913
theorem B3348017 : Blo 1486063 3348017 := bstep (se 2 (by rfl) ⟨1255506, by rfl⟩ : syracuseStep 3348017 = 2511013) B2511013
theorem B3176003 : Blo 1486063 3176003 := bstep (se 1 (by rfl) ⟨2382002, by rfl⟩ : syracuseStep 3176003 = 4764005) B4764005
theorem B3348035 : Blo 1486063 3348035 := bstep (se 1 (by rfl) ⟨2511026, by rfl⟩ : syracuseStep 3348035 = 5022053) B5022053
theorem B5019245 : Blo 1486063 5019245 := bstep (se 3 (by rfl) ⟨941108, by rfl⟩ : syracuseStep 5019245 = 1882217) B1882217
theorem B1881731 : Blo 1486063 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B5019299 : Blo 1486063 5019299 := bstep (se 1 (by rfl) ⟨3764474, by rfl⟩ : syracuseStep 5019299 = 7528949) B7528949
theorem B3765923 : Blo 1486063 3765923 := bstep (se 1 (by rfl) ⟨2824442, by rfl⟩ : syracuseStep 3765923 = 5648885) B5648885
theorem B2578115 : Blo 1486063 2578115 := bstep (se 1 (by rfl) ⟨1933586, by rfl⟩ : syracuseStep 2578115 = 3867173) B3867173
theorem B3815171 : Blo 1486063 3815171 := bstep (se 1 (by rfl) ⟨2861378, by rfl⟩ : syracuseStep 3815171 = 5722757) B5722757
theorem B3766115 : Blo 1486063 3766115 := bstep (se 1 (by rfl) ⟨2824586, by rfl⟩ : syracuseStep 3766115 = 5649173) B5649173
theorem B5019569 : Blo 1486063 5019569 := bstep (se 2 (by rfl) ⟨1882338, by rfl⟩ : syracuseStep 5019569 = 3764677) B3764677
theorem B20625461 : Blo 1486063 20625461 := bstep (se 5 (by rfl) ⟨966818, by rfl⟩ : syracuseStep 20625461 = 1933637) B1933637
theorem B2414657 : Blo 1486063 2414657 := bstep (se 2 (by rfl) ⟨905496, by rfl⟩ : syracuseStep 2414657 = 1810993) B1810993
theorem B4233293 : Blo 1486063 4233293 := bstep (se 3 (by rfl) ⟨793742, by rfl⟩ : syracuseStep 4233293 = 1587485) B1587485
theorem B4290691 : Blo 1486063 4290691 := bstep (se 1 (by rfl) ⟨3218018, by rfl⟩ : syracuseStep 4290691 = 6436037) B6436037
theorem B10172557 : Blo 1486063 10172557 := bstep (se 3 (by rfl) ⟨1907354, by rfl⟩ : syracuseStep 10172557 = 3814709) B3814709
theorem B8468657 : Blo 1486063 8468657 := bstep (se 2 (by rfl) ⟨3175746, by rfl⟩ : syracuseStep 8468657 = 6351493) B6351493
theorem B1587395 : Blo 1486063 1587395 := bstep (se 1 (by rfl) ⟨1190546, by rfl⟩ : syracuseStep 1587395 = 2381093) B2381093
theorem B9173189 : Blo 1486063 9173189 := bstep (se 4 (by rfl) ⟨859986, by rfl⟩ : syracuseStep 9173189 = 1719973) B1719973
theorem B4233485 : Blo 1486063 4233485 := bstep (se 3 (by rfl) ⟨793778, by rfl⟩ : syracuseStep 4233485 = 1587557) B1587557
theorem B2824465 : Blo 1486063 2824465 := bstep (se 2 (by rfl) ⟨1059174, by rfl⟩ : syracuseStep 2824465 = 2118349) B2118349
theorem B2382131 : Blo 1486063 2382131 := bstep (se 1 (by rfl) ⟨1786598, by rfl⟩ : syracuseStep 2382131 = 3573197) B3573197
theorem B1587523 : Blo 1486063 1587523 := bstep (se 1 (by rfl) ⟨1190642, by rfl⟩ : syracuseStep 1587523 = 2381285) B2381285
theorem B1882435 : Blo 1486063 1882435 := bstep (se 1 (by rfl) ⟨1411826, by rfl⟩ : syracuseStep 1882435 = 2823653) B2823653
theorem B4962637 : Blo 1486063 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B1882531 : Blo 1486063 1882531 := bstep (se 1 (by rfl) ⟨1411898, by rfl⟩ : syracuseStep 1882531 = 2823797) B2823797
theorem B2824625 : Blo 1486063 2824625 := bstep (se 2 (by rfl) ⟨1059234, by rfl⟩ : syracuseStep 2824625 = 2118469) B2118469
theorem B5020109 : Blo 1486063 5020109 := bstep (se 3 (by rfl) ⟨941270, by rfl⟩ : syracuseStep 5020109 = 1882541) B1882541
theorem B5020163 : Blo 1486063 5020163 := bstep (se 1 (by rfl) ⟨3765122, by rfl⟩ : syracuseStep 5020163 = 7530245) B7530245
theorem B3176977 : Blo 1486063 3176977 := bstep (se 2 (by rfl) ⟨1191366, by rfl⟩ : syracuseStep 3176977 = 2382733) B2382733
theorem B2382515 : Blo 1486063 2382515 := bstep (se 1 (by rfl) ⟨1786886, by rfl⟩ : syracuseStep 2382515 = 3573773) B3573773
theorem B5372621 : Blo 1486063 5372621 := bstep (se 3 (by rfl) ⟨1007366, by rfl⟩ : syracuseStep 5372621 = 2014733) B2014733
theorem B12704525 : Blo 1486063 12704525 := bstep (se 3 (by rfl) ⟨2382098, by rfl⟩ : syracuseStep 12704525 = 4764197) B4764197
theorem B5020433 : Blo 1486063 5020433 := bstep (se 2 (by rfl) ⟨1882662, by rfl⟩ : syracuseStep 5020433 = 3765325) B3765325
theorem B3177233 : Blo 1486063 3177233 := bstep (se 2 (by rfl) ⟨1191462, by rfl⟩ : syracuseStep 3177233 = 2382925) B2382925
theorem B2382643 : Blo 1486063 2382643 := bstep (se 1 (by rfl) ⟨1786982, by rfl⟩ : syracuseStep 2382643 = 3573965) B3573965
theorem B1883027 : Blo 1486063 1883027 := bstep (se 1 (by rfl) ⟨1412270, by rfl⟩ : syracuseStep 1883027 = 2824541) B2824541
theorem B1694723 : Blo 1486063 1694723 := bstep (se 1 (by rfl) ⟨1271042, by rfl⟩ : syracuseStep 1694723 = 2542085) B2542085
theorem B5356621 : Blo 1486063 5356621 := bstep (se 3 (by rfl) ⟨1004366, by rfl⟩ : syracuseStep 5356621 = 2008733) B2008733
theorem B5643341 : Blo 1486063 5643341 := bstep (se 3 (by rfl) ⟨1058126, by rfl⟩ : syracuseStep 5643341 = 2116253) B2116253
theorem B3619921 : Blo 1486063 3619921 := bstep (se 2 (by rfl) ⟨1357470, by rfl⟩ : syracuseStep 3619921 = 2714941) B2714941
theorem B1588339 : Blo 1486063 1588339 := bstep (se 1 (by rfl) ⟨1191254, by rfl⟩ : syracuseStep 1588339 = 2382509) B2382509
theorem B21445859 : Blo 1486063 21445859 := bstep (se 1 (by rfl) ⟨16084394, by rfl⟩ : syracuseStep 21445859 = 32168789) B32168789
theorem B16088291 : Blo 1486063 16088291 := bstep (se 1 (by rfl) ⟨12066218, by rfl⟩ : syracuseStep 16088291 = 24132437) B24132437
theorem B4234477 : Blo 1486063 4234477 := bstep (se 3 (by rfl) ⟨793964, by rfl⟩ : syracuseStep 4234477 = 1587929) B1587929
theorem B2145571 : Blo 1486063 2145571 := bstep (se 1 (by rfl) ⟨1609178, by rfl⟩ : syracuseStep 2145571 = 3218357) B3218357
theorem B5020973 : Blo 1486063 5020973 := bstep (se 3 (by rfl) ⟨941432, by rfl⟩ : syracuseStep 5020973 = 1882865) B1882865
theorem B3013937 : Blo 1486063 3013937 := bstep (se 2 (by rfl) ⟨1130226, by rfl⟩ : syracuseStep 3013937 = 2260453) B2260453
theorem B5021027 : Blo 1486063 5021027 := bstep (se 1 (by rfl) ⟨3765770, by rfl⟩ : syracuseStep 5021027 = 7531541) B7531541
theorem B3571121 : Blo 1486063 3571121 := bstep (se 2 (by rfl) ⟨1339170, by rfl⟩ : syracuseStep 3571121 = 2678341) B2678341
theorem B2383361 : Blo 1486063 2383361 := bstep (se 2 (by rfl) ⟨893760, by rfl⟩ : syracuseStep 2383361 = 1787521) B1787521
theorem B9166385 : Blo 1486063 9166385 := bstep (se 2 (by rfl) ⟨3437394, by rfl⟩ : syracuseStep 9166385 = 6874789) B6874789
theorem B8470115 : Blo 1486063 8470115 := bstep (se 1 (by rfl) ⟨6352586, by rfl⟩ : syracuseStep 8470115 = 12705173) B12705173
theorem B14294627 : Blo 1486063 14294627 := bstep (se 1 (by rfl) ⟨10720970, by rfl⟩ : syracuseStep 14294627 = 21441941) B21441941
theorem B5021297 : Blo 1486063 5021297 := bstep (se 2 (by rfl) ⟨1882986, by rfl⟩ : syracuseStep 5021297 = 3765973) B3765973
theorem B6348451 : Blo 1486063 6348451 := bstep (se 1 (by rfl) ⟨4761338, by rfl⟩ : syracuseStep 6348451 = 9522677) B9522677
theorem B2383553 : Blo 1486063 2383553 := bstep (se 2 (by rfl) ⟨893832, by rfl⟩ : syracuseStep 2383553 = 1787665) B1787665
theorem B2678513 : Blo 1486063 2678513 := bstep (se 2 (by rfl) ⟨1004442, by rfl⟩ : syracuseStep 2678513 = 2008885) B2008885
theorem B3571505 : Blo 1486063 3571505 := bstep (se 2 (by rfl) ⟨1339314, by rfl⟩ : syracuseStep 3571505 = 2678629) B2678629
theorem B14483341 : Blo 1486063 14483341 := bstep (se 3 (by rfl) ⟨2715626, by rfl⟩ : syracuseStep 14483341 = 5431253) B5431253
theorem B3571619 : Blo 1486063 3571619 := bstep (se 1 (by rfl) ⟨2678714, by rfl⟩ : syracuseStep 3571619 = 5357429) B5357429
theorem B27131921 : Blo 1486063 27131921 := bstep (se 2 (by rfl) ⟨10174470, by rfl⟩ : syracuseStep 27131921 = 20348941) B20348941
theorem B14286941 : Blo 1486063 14286941 := bstep (se 3 (by rfl) ⟨2678801, by rfl⟩ : syracuseStep 14286941 = 5357603) B5357603
theorem B12705923 : Blo 1486063 12705923 := bstep (se 1 (by rfl) ⟨9529442, by rfl⟩ : syracuseStep 12705923 = 19058885) B19058885
theorem B6439085 : Blo 1486063 6439085 := bstep (se 3 (by rfl) ⟨1207328, by rfl⟩ : syracuseStep 6439085 = 2414657) B2414657
theorem B6701329 : Blo 1486063 6701329 := bstep (se 2 (by rfl) ⟨2512998, by rfl⟩ : syracuseStep 6701329 = 5025997) B5025997
theorem B11297069 : Blo 1486063 11297069 := bstep (se 3 (by rfl) ⟨2118200, by rfl⟩ : syracuseStep 11297069 = 4236401) B4236401
theorem B1630571 : Blo 1486063 1630571 := bstep (se 1 (by rfl) ⟨1222928, by rfl⟩ : syracuseStep 1630571 = 2445857) B2445857
theorem B24461837 : Blo 1486063 24461837 := bstep (se 3 (by rfl) ⟨4586594, by rfl⟩ : syracuseStep 24461837 = 9173189) B9173189
theorem B24453667 : Blo 1486063 24453667 := bstep (se 1 (by rfl) ⟨18340250, by rfl⟩ : syracuseStep 24453667 = 36680501) B36680501
theorem B8471141 : Blo 1486063 8471141 := bstep (se 4 (by rfl) ⟨794169, by rfl⟩ : syracuseStep 8471141 = 1588339) B1588339
theorem B7529111 : Blo 1486063 7529111 := bstep (se 1 (by rfl) ⟨5646833, by rfl⟩ : syracuseStep 7529111 = 11293667) B11293667
theorem B4235969 : Blo 1486063 4235969 := bstep (se 2 (by rfl) ⟨1588488, by rfl⟩ : syracuseStep 4235969 = 3176977) B3176977
theorem B11289293 : Blo 1486063 11289293 := bstep (se 3 (by rfl) ⟨2116742, by rfl⟩ : syracuseStep 11289293 = 4233485) B4233485
theorem B6349529 : Blo 1486063 6349529 := bstep (se 2 (by rfl) ⟨2381073, by rfl⟩ : syracuseStep 6349529 = 4762147) B4762147
theorem B1508107 : Blo 1486063 1508107 := bstep (se 1 (by rfl) ⟨1131080, by rfl⟩ : syracuseStep 1508107 = 2262161) B2262161
theorem B1671979 : Blo 1486063 1671979 := bstep (se 1 (by rfl) ⟨1253984, by rfl⟩ : syracuseStep 1671979 = 2507969) B2507969
theorem B4236083 : Blo 1486063 4236083 := bstep (se 1 (by rfl) ⟨3177062, by rfl⟩ : syracuseStep 4236083 = 6354125) B6354125
theorem B5358467 : Blo 1486063 5358467 := bstep (se 1 (by rfl) ⟨4018850, by rfl⟩ : syracuseStep 5358467 = 8037701) B8037701
theorem B2229131 : Blo 1486063 2229131 := bstep (se 1 (by rfl) ⟨1671848, by rfl⟩ : syracuseStep 2229131 = 3343697) B3343697
theorem B2229143 : Blo 1486063 2229143 := bstep (se 1 (by rfl) ⟨1671857, by rfl⟩ : syracuseStep 2229143 = 3343715) B3343715
theorem B1672087 : Blo 1486063 1672087 := bstep (se 1 (by rfl) ⟨1254065, by rfl⟩ : syracuseStep 1672087 = 2508131) B2508131
theorem B2229209 : Blo 1486063 2229209 := bstep (se 2 (by rfl) ⟨835953, by rfl⟩ : syracuseStep 2229209 = 1671907) B1671907
theorem B5645315 : Blo 1486063 5645315 := bstep (se 1 (by rfl) ⟨4233986, by rfl⟩ : syracuseStep 5645315 = 8467973) B8467973
theorem B2229323 : Blo 1486063 2229323 := bstep (se 1 (by rfl) ⟨1671992, by rfl⟩ : syracuseStep 2229323 = 3343985) B3343985
theorem B1672267 : Blo 1486063 1672267 := bstep (se 1 (by rfl) ⟨1254200, by rfl⟩ : syracuseStep 1672267 = 2508401) B2508401
theorem B28574795 : Blo 1486063 28574795 := bstep (se 1 (by rfl) ⟨21431096, by rfl⟩ : syracuseStep 28574795 = 42862193) B42862193
theorem B2229335 : Blo 1486063 2229335 := bstep (se 1 (by rfl) ⟨1672001, by rfl⟩ : syracuseStep 2229335 = 3344003) B3344003
theorem B2507915 : Blo 1486063 2507915 := bstep (se 1 (by rfl) ⟨1880936, by rfl⟩ : syracuseStep 2507915 = 3761873) B3761873
theorem B2229401 : Blo 1486063 2229401 := bstep (se 2 (by rfl) ⟨836025, by rfl⟩ : syracuseStep 2229401 = 1672051) B1672051
theorem B11289779 : Blo 1486063 11289779 := bstep (se 1 (by rfl) ⟨8467334, by rfl⟩ : syracuseStep 11289779 = 16934669) B16934669
theorem B1672375 : Blo 1486063 1672375 := bstep (se 1 (by rfl) ⟨1254281, by rfl⟩ : syracuseStep 1672375 = 2508563) B2508563
theorem B2508043 : Blo 1486063 2508043 := bstep (se 1 (by rfl) ⟨1881032, by rfl⟩ : syracuseStep 2508043 = 3762065) B3762065
theorem B2229515 : Blo 1486063 2229515 := bstep (se 1 (by rfl) ⟨1672136, by rfl⟩ : syracuseStep 2229515 = 3344273) B3344273
theorem B2229527 : Blo 1486063 2229527 := bstep (se 1 (by rfl) ⟨1672145, by rfl⟩ : syracuseStep 2229527 = 3344291) B3344291
theorem B2229593 : Blo 1486063 2229593 := bstep (se 2 (by rfl) ⟨836097, by rfl⟩ : syracuseStep 2229593 = 1672195) B1672195
theorem B9528677 : Blo 1486063 9528677 := bstep (se 4 (by rfl) ⟨893313, by rfl⟩ : syracuseStep 9528677 = 1786627) B1786627
theorem B1672555 : Blo 1486063 1672555 := bstep (se 1 (by rfl) ⟨1254416, by rfl⟩ : syracuseStep 1672555 = 2508833) B2508833
theorem B3343769 : Blo 1486063 3343769 := bstep (se 2 (by rfl) ⟨1253913, by rfl⟩ : syracuseStep 3343769 = 2507827) B2507827
theorem B2508185 : Blo 1486063 2508185 := bstep (se 2 (by rfl) ⟨940569, by rfl⟩ : syracuseStep 2508185 = 1881139) B1881139
theorem B4826561 : Blo 1486063 4826561 := bstep (se 2 (by rfl) ⟨1809960, by rfl⟩ : syracuseStep 4826561 = 3619921) B3619921
theorem B2229707 : Blo 1486063 2229707 := bstep (se 1 (by rfl) ⟨1672280, by rfl⟩ : syracuseStep 2229707 = 3344561) B3344561
theorem B5645771 : Blo 1486063 5645771 := bstep (se 1 (by rfl) ⟨4234328, by rfl⟩ : syracuseStep 5645771 = 8468657) B8468657
theorem B10872269 : Blo 1486063 10872269 := bstep (se 3 (by rfl) ⟨2038550, by rfl⟩ : syracuseStep 10872269 = 4077101) B4077101
theorem B2229719 : Blo 1486063 2229719 := bstep (se 1 (by rfl) ⟨1672289, by rfl⟩ : syracuseStep 2229719 = 3344579) B3344579
theorem B1672663 : Blo 1486063 1672663 := bstep (se 1 (by rfl) ⟨1254497, by rfl⟩ : syracuseStep 1672663 = 2508995) B2508995
theorem B3343859 : Blo 1486063 3343859 := bstep (se 1 (by rfl) ⟨2507894, by rfl⟩ : syracuseStep 3343859 = 5015789) B5015789
theorem B3343895 : Blo 1486063 3343895 := bstep (se 1 (by rfl) ⟨2507921, by rfl⟩ : syracuseStep 3343895 = 5015843) B5015843
theorem B2508313 : Blo 1486063 2508313 := bstep (se 2 (by rfl) ⟨940617, by rfl⟩ : syracuseStep 2508313 = 1881235) B1881235
theorem B2229785 : Blo 1486063 2229785 := bstep (se 2 (by rfl) ⟨836169, by rfl⟩ : syracuseStep 2229785 = 1672339) B1672339
theorem B4523543 : Blo 1486063 4523543 := bstep (se 1 (by rfl) ⟨3392657, by rfl⟩ : syracuseStep 4523543 = 6785315) B6785315
theorem B19056221 : Blo 1486063 19056221 := bstep (se 3 (by rfl) ⟨3573041, by rfl⟩ : syracuseStep 19056221 = 7146083) B7146083
theorem B40699523 : Blo 1486063 40699523 := bstep (se 1 (by rfl) ⟨30524642, by rfl⟩ : syracuseStep 40699523 = 61049285) B61049285
theorem B2229899 : Blo 1486063 2229899 := bstep (se 1 (by rfl) ⟨1672424, by rfl⟩ : syracuseStep 2229899 = 3344849) B3344849
theorem B1672843 : Blo 1486063 1672843 := bstep (se 1 (by rfl) ⟨1254632, by rfl⟩ : syracuseStep 1672843 = 2509265) B2509265
theorem B5645969 : Blo 1486063 5645969 := bstep (se 2 (by rfl) ⟨2117238, by rfl⟩ : syracuseStep 5645969 = 4234477) B4234477
theorem B2229911 : Blo 1486063 2229911 := bstep (se 1 (by rfl) ⟨1672433, by rfl⟩ : syracuseStep 2229911 = 3344867) B3344867
theorem B3016343 : Blo 1486063 3016343 := bstep (se 1 (by rfl) ⟨2262257, by rfl⟩ : syracuseStep 3016343 = 4524515) B4524515
theorem B3344075 : Blo 1486063 3344075 := bstep (se 1 (by rfl) ⟨2508056, by rfl⟩ : syracuseStep 3344075 = 5016113) B5016113
theorem B2229977 : Blo 1486063 2229977 := bstep (se 2 (by rfl) ⟨836241, by rfl⟩ : syracuseStep 2229977 = 1672483) B1672483
theorem B1672951 : Blo 1486063 1672951 := bstep (se 1 (by rfl) ⟨1254713, by rfl⟩ : syracuseStep 1672951 = 2509427) B2509427
theorem B3344129 : Blo 1486063 3344129 := bstep (se 2 (by rfl) ⟨1254048, by rfl⟩ : syracuseStep 3344129 = 2508097) B2508097
theorem B3581747 : Blo 1486063 3581747 := bstep (se 1 (by rfl) ⟨2686310, by rfl⟩ : syracuseStep 3581747 = 5372621) B5372621
theorem B2230091 : Blo 1486063 2230091 := bstep (se 1 (by rfl) ⟨1672568, by rfl⟩ : syracuseStep 2230091 = 3345137) B3345137
theorem B2230103 : Blo 1486063 2230103 := bstep (se 1 (by rfl) ⟨1672577, by rfl⟩ : syracuseStep 2230103 = 3345155) B3345155
theorem B2230169 : Blo 1486063 2230169 := bstep (se 2 (by rfl) ⟨836313, by rfl⟩ : syracuseStep 2230169 = 1672627) B1672627
theorem B1673131 : Blo 1486063 1673131 := bstep (se 1 (by rfl) ⟨1254848, by rfl⟩ : syracuseStep 1673131 = 2509697) B2509697
theorem B3344345 : Blo 1486063 3344345 := bstep (se 2 (by rfl) ⟨1254129, by rfl⟩ : syracuseStep 3344345 = 2508259) B2508259
theorem B2230283 : Blo 1486063 2230283 := bstep (se 1 (by rfl) ⟨1672712, by rfl⟩ : syracuseStep 2230283 = 3345425) B3345425
theorem B2230295 : Blo 1486063 2230295 := bstep (se 1 (by rfl) ⟨1672721, by rfl⟩ : syracuseStep 2230295 = 3345443) B3345443
theorem B1673239 : Blo 1486063 1673239 := bstep (se 1 (by rfl) ⟨1254929, by rfl⟩ : syracuseStep 1673239 = 2509859) B2509859
theorem B3762227 : Blo 1486063 3762227 := bstep (se 1 (by rfl) ⟨2821670, by rfl⟩ : syracuseStep 3762227 = 5643341) B5643341
theorem B3344435 : Blo 1486063 3344435 := bstep (se 1 (by rfl) ⟨2508326, by rfl⟩ : syracuseStep 3344435 = 5016653) B5016653
theorem B3573811 : Blo 1486063 3573811 := bstep (se 1 (by rfl) ⟨2680358, by rfl⟩ : syracuseStep 3573811 = 5360717) B5360717
theorem B5015627 : Blo 1486063 5015627 := bstep (se 1 (by rfl) ⟨3761720, by rfl⟩ : syracuseStep 5015627 = 7523441) B7523441
theorem B3344471 : Blo 1486063 3344471 := bstep (se 1 (by rfl) ⟨2508353, by rfl⟩ : syracuseStep 3344471 = 5016707) B5016707
theorem B2508887 : Blo 1486063 2508887 := bstep (se 1 (by rfl) ⟨1881665, by rfl⟩ : syracuseStep 2508887 = 3763331) B3763331
theorem B2230361 : Blo 1486063 2230361 := bstep (se 2 (by rfl) ⟨836385, by rfl⟩ : syracuseStep 2230361 = 1672771) B1672771
theorem B14297239 : Blo 1486063 14297239 := bstep (se 1 (by rfl) ⟨10722929, by rfl⟩ : syracuseStep 14297239 = 21445859) B21445859
theorem B10725527 : Blo 1486063 10725527 := bstep (se 1 (by rfl) ⟨8044145, by rfl⟩ : syracuseStep 10725527 = 16088291) B16088291
theorem B2009291 : Blo 1486063 2009291 := bstep (se 1 (by rfl) ⟨1506968, by rfl⟩ : syracuseStep 2009291 = 3013937) B3013937
theorem B2230475 : Blo 1486063 2230475 := bstep (se 1 (by rfl) ⟨1672856, by rfl⟩ : syracuseStep 2230475 = 3345713) B3345713
theorem B1673419 : Blo 1486063 1673419 := bstep (se 1 (by rfl) ⟨1255064, by rfl⟩ : syracuseStep 1673419 = 2510129) B2510129
theorem B2509015 : Blo 1486063 2509015 := bstep (se 1 (by rfl) ⟨1881761, by rfl⟩ : syracuseStep 2509015 = 3763523) B3763523
theorem B2230487 : Blo 1486063 2230487 := bstep (se 1 (by rfl) ⟨1672865, by rfl⟩ : syracuseStep 2230487 = 3345731) B3345731
theorem B8464601 : Blo 1486063 8464601 := bstep (se 2 (by rfl) ⟨3174225, by rfl⟩ : syracuseStep 8464601 = 6348451) B6348451
theorem B3344651 : Blo 1486063 3344651 := bstep (se 1 (by rfl) ⟨2508488, by rfl⟩ : syracuseStep 3344651 = 5016977) B5016977
theorem B2230553 : Blo 1486063 2230553 := bstep (se 2 (by rfl) ⟨836457, by rfl⟩ : syracuseStep 2230553 = 1672915) B1672915
theorem B1673527 : Blo 1486063 1673527 := bstep (se 1 (by rfl) ⟨1255145, by rfl⟩ : syracuseStep 1673527 = 2510291) B2510291
theorem B3344705 : Blo 1486063 3344705 := bstep (se 2 (by rfl) ⟨1254264, by rfl⟩ : syracuseStep 3344705 = 2508529) B2508529
theorem B6351169 : Blo 1486063 6351169 := bstep (se 2 (by rfl) ⟨2381688, by rfl⟩ : syracuseStep 6351169 = 4763377) B4763377
theorem B4352321 : Blo 1486063 4352321 := bstep (se 2 (by rfl) ⟨1632120, by rfl⟩ : syracuseStep 4352321 = 3264241) B3264241
theorem B5015897 : Blo 1486063 5015897 := bstep (se 2 (by rfl) ⟨1880961, by rfl⟩ : syracuseStep 5015897 = 3761923) B3761923
theorem B3762521 : Blo 1486063 3762521 := bstep (se 2 (by rfl) ⟨1410945, by rfl⟩ : syracuseStep 3762521 = 2821891) B2821891
theorem B2230667 : Blo 1486063 2230667 := bstep (se 1 (by rfl) ⟨1673000, by rfl⟩ : syracuseStep 2230667 = 3346001) B3346001
theorem B2115991 : Blo 1486063 2115991 := bstep (se 1 (by rfl) ⟨1586993, by rfl⟩ : syracuseStep 2115991 = 3173987) B3173987
theorem B2230679 : Blo 1486063 2230679 := bstep (se 1 (by rfl) ⟨1673009, by rfl⟩ : syracuseStep 2230679 = 3346019) B3346019
theorem B5646743 : Blo 1486063 5646743 := bstep (se 1 (by rfl) ⟨4235057, by rfl⟩ : syracuseStep 5646743 = 8470115) B8470115
theorem B9529751 : Blo 1486063 9529751 := bstep (se 1 (by rfl) ⟨7147313, by rfl⟩ : syracuseStep 9529751 = 14294627) B14294627
theorem B2230745 : Blo 1486063 2230745 := bstep (se 2 (by rfl) ⟨836529, by rfl⟩ : syracuseStep 2230745 = 1673059) B1673059
theorem B1673707 : Blo 1486063 1673707 := bstep (se 1 (by rfl) ⟨1255280, by rfl⟩ : syracuseStep 1673707 = 2510561) B2510561
theorem B19311121 : Blo 1486063 19311121 := bstep (se 2 (by rfl) ⟨7241670, by rfl⟩ : syracuseStep 19311121 = 14483341) B14483341
theorem B3344921 : Blo 1486063 3344921 := bstep (se 2 (by rfl) ⟨1254345, by rfl⟩ : syracuseStep 3344921 = 2508691) B2508691
theorem B2230859 : Blo 1486063 2230859 := bstep (se 1 (by rfl) ⟨1673144, by rfl⟩ : syracuseStep 2230859 = 3346289) B3346289
theorem B2230871 : Blo 1486063 2230871 := bstep (se 1 (by rfl) ⟨1673153, by rfl⟩ : syracuseStep 2230871 = 3346307) B3346307
theorem B1673815 : Blo 1486063 1673815 := bstep (se 1 (by rfl) ⟨1255361, by rfl⟩ : syracuseStep 1673815 = 2510723) B2510723
theorem B5646941 : Blo 1486063 5646941 := bstep (se 3 (by rfl) ⟨1058801, by rfl⟩ : syracuseStep 5646941 = 2117603) B2117603
theorem B11291237 : Blo 1486063 11291237 := bstep (se 4 (by rfl) ⟨1058553, by rfl⟩ : syracuseStep 11291237 = 2117107) B2117107
theorem B3345011 : Blo 1486063 3345011 := bstep (se 1 (by rfl) ⟨2508758, by rfl⟩ : syracuseStep 3345011 = 5017517) B5017517
theorem B3345047 : Blo 1486063 3345047 := bstep (se 1 (by rfl) ⟨2508785, by rfl⟩ : syracuseStep 3345047 = 5017571) B5017571
theorem B2230937 : Blo 1486063 2230937 := bstep (se 2 (by rfl) ⟨836601, by rfl⟩ : syracuseStep 2230937 = 1673203) B1673203
theorem B2231051 : Blo 1486063 2231051 := bstep (se 1 (by rfl) ⟨1673288, by rfl⟩ : syracuseStep 2231051 = 3346577) B3346577
theorem B1673995 : Blo 1486063 1673995 := bstep (se 1 (by rfl) ⟨1255496, by rfl⟩ : syracuseStep 1673995 = 2510993) B2510993
theorem B2231063 : Blo 1486063 2231063 := bstep (se 1 (by rfl) ⟨1673297, by rfl⟩ : syracuseStep 2231063 = 3346595) B3346595
theorem B4016947 : Blo 1486063 4016947 := bstep (se 1 (by rfl) ⟨3012710, by rfl⟩ : syracuseStep 4016947 = 6025421) B6025421
theorem B3345227 : Blo 1486063 3345227 := bstep (se 1 (by rfl) ⟨2508920, by rfl⟩ : syracuseStep 3345227 = 5017841) B5017841
theorem B2509643 : Blo 1486063 2509643 := bstep (se 1 (by rfl) ⟨1882232, by rfl⟩ : syracuseStep 2509643 = 3764465) B3764465
theorem B5720921 : Blo 1486063 5720921 := bstep (se 2 (by rfl) ⟨2145345, by rfl⟩ : syracuseStep 5720921 = 4290691) B4290691
theorem B2231129 : Blo 1486063 2231129 := bstep (se 2 (by rfl) ⟨836673, by rfl⟩ : syracuseStep 2231129 = 1673347) B1673347
theorem B3345281 : Blo 1486063 3345281 := bstep (se 2 (by rfl) ⟨1254480, by rfl⟩ : syracuseStep 3345281 = 2508961) B2508961
theorem B6351767 : Blo 1486063 6351767 := bstep (se 1 (by rfl) ⟨4763825, by rfl⟩ : syracuseStep 6351767 = 9527651) B9527651
theorem B2509771 : Blo 1486063 2509771 := bstep (se 1 (by rfl) ⟨1882328, by rfl⟩ : syracuseStep 2509771 = 3764657) B3764657
theorem B2231243 : Blo 1486063 2231243 := bstep (se 1 (by rfl) ⟨1673432, by rfl⟩ : syracuseStep 2231243 = 3346865) B3346865
theorem B2231255 : Blo 1486063 2231255 := bstep (se 1 (by rfl) ⟨1673441, by rfl⟩ : syracuseStep 2231255 = 3346883) B3346883
theorem B5016599 : Blo 1486063 5016599 := bstep (se 1 (by rfl) ⟨3762449, by rfl⟩ : syracuseStep 5016599 = 7524899) B7524899
theorem B2231321 : Blo 1486063 2231321 := bstep (se 2 (by rfl) ⟨836745, by rfl⟩ : syracuseStep 2231321 = 1673491) B1673491
theorem B12708899 : Blo 1486063 12708899 := bstep (se 1 (by rfl) ⟨9531674, by rfl⟩ : syracuseStep 12708899 = 19063349) B19063349
theorem B3574849 : Blo 1486063 3574849 := bstep (se 2 (by rfl) ⟨1340568, by rfl⟩ : syracuseStep 3574849 = 2681137) B2681137
theorem B28568645 : Blo 1486063 28568645 := bstep (se 4 (by rfl) ⟨2678310, by rfl⟩ : syracuseStep 28568645 = 5356621) B5356621
theorem B11291723 : Blo 1486063 11291723 := bstep (se 1 (by rfl) ⟨8468792, by rfl⟩ : syracuseStep 11291723 = 16937585) B16937585
theorem B2116697 : Blo 1486063 2116697 := bstep (se 2 (by rfl) ⟨793761, by rfl⟩ : syracuseStep 2116697 = 1587523) B1587523
theorem B3345497 : Blo 1486063 3345497 := bstep (se 2 (by rfl) ⟨1254561, by rfl⟩ : syracuseStep 3345497 = 2509123) B2509123
theorem B2509913 : Blo 1486063 2509913 := bstep (se 2 (by rfl) ⟨941217, by rfl⟩ : syracuseStep 2509913 = 1882435) B1882435
theorem B2231435 : Blo 1486063 2231435 := bstep (se 1 (by rfl) ⟨1673576, by rfl⟩ : syracuseStep 2231435 = 3347153) B3347153
theorem B2231447 : Blo 1486063 2231447 := bstep (se 1 (by rfl) ⟨1673585, by rfl⟩ : syracuseStep 2231447 = 3347171) B3347171
theorem B3345587 : Blo 1486063 3345587 := bstep (se 1 (by rfl) ⟨2509190, by rfl⟩ : syracuseStep 3345587 = 5018381) B5018381
theorem B2116811 : Blo 1486063 2116811 := bstep (se 1 (by rfl) ⟨1587608, by rfl⟩ : syracuseStep 2116811 = 3175217) B3175217
theorem B3345623 : Blo 1486063 3345623 := bstep (se 1 (by rfl) ⟨2509217, by rfl⟩ : syracuseStep 3345623 = 5018435) B5018435
theorem B2510041 : Blo 1486063 2510041 := bstep (se 2 (by rfl) ⟨941265, by rfl⟩ : syracuseStep 2510041 = 1882531) B1882531
theorem B2231513 : Blo 1486063 2231513 := bstep (se 2 (by rfl) ⟨836817, by rfl⟩ : syracuseStep 2231513 = 1673635) B1673635
theorem B1486071 : Blo 1486063 1486071 := bstep (se 1 (by rfl) ⟨1114553, by rfl⟩ : syracuseStep 1486071 = 2229107) B2229107
theorem B1486091 : Blo 1486063 1486091 := bstep (se 1 (by rfl) ⟨1114568, by rfl⟩ : syracuseStep 1486091 = 2229137) B2229137
theorem B1486103 : Blo 1486063 1486103 := bstep (se 1 (by rfl) ⟨1114577, by rfl⟩ : syracuseStep 1486103 = 2229155) B2229155
theorem B1486123 : Blo 1486063 1486123 := bstep (se 1 (by rfl) ⟨1114592, by rfl⟩ : syracuseStep 1486123 = 2229185) B2229185
theorem B1486135 : Blo 1486063 1486135 := bstep (se 1 (by rfl) ⟨1114601, by rfl⟩ : syracuseStep 1486135 = 2229203) B2229203
theorem B1486155 : Blo 1486063 1486155 := bstep (se 1 (by rfl) ⟨1114616, by rfl⟩ : syracuseStep 1486155 = 2229233) B2229233
theorem B2231627 : Blo 1486063 2231627 := bstep (se 1 (by rfl) ⟨1673720, by rfl⟩ : syracuseStep 2231627 = 3347441) B3347441
theorem B1486167 : Blo 1486063 1486167 := bstep (se 1 (by rfl) ⟨1114625, by rfl⟩ : syracuseStep 1486167 = 2229251) B2229251
theorem B2714969 : Blo 1486063 2714969 := bstep (se 2 (by rfl) ⟨1018113, by rfl⟩ : syracuseStep 2714969 = 2036227) B2036227
theorem B2231639 : Blo 1486063 2231639 := bstep (se 1 (by rfl) ⟨1673729, by rfl⟩ : syracuseStep 2231639 = 3347459) B3347459
theorem B1486187 : Blo 1486063 1486187 := bstep (se 1 (by rfl) ⟨1114640, by rfl⟩ : syracuseStep 1486187 = 2229281) B2229281
theorem B1486199 : Blo 1486063 1486199 := bstep (se 1 (by rfl) ⟨1114649, by rfl⟩ : syracuseStep 1486199 = 2229299) B2229299
theorem B1486219 : Blo 1486063 1486219 := bstep (se 1 (by rfl) ⟨1114664, by rfl⟩ : syracuseStep 1486219 = 2229329) B2229329
theorem B3345803 : Blo 1486063 3345803 := bstep (se 1 (by rfl) ⟨2509352, by rfl⟩ : syracuseStep 3345803 = 5018705) B5018705
theorem B1486231 : Blo 1486063 1486231 := bstep (se 1 (by rfl) ⟨1114673, by rfl⟩ : syracuseStep 1486231 = 2229347) B2229347
theorem B2231705 : Blo 1486063 2231705 := bstep (se 2 (by rfl) ⟨836889, by rfl⟩ : syracuseStep 2231705 = 1673779) B1673779
theorem B1486251 : Blo 1486063 1486251 := bstep (se 1 (by rfl) ⟨1114688, by rfl⟩ : syracuseStep 1486251 = 2229377) B2229377
theorem B1486263 : Blo 1486063 1486263 := bstep (se 1 (by rfl) ⟨1114697, by rfl⟩ : syracuseStep 1486263 = 2229395) B2229395
theorem B3345857 : Blo 1486063 3345857 := bstep (se 2 (by rfl) ⟨1254696, by rfl⟩ : syracuseStep 3345857 = 2509393) B2509393
theorem B1486283 : Blo 1486063 1486283 := bstep (se 1 (by rfl) ⟨1114712, by rfl⟩ : syracuseStep 1486283 = 2229425) B2229425
theorem B1486295 : Blo 1486063 1486295 := bstep (se 1 (by rfl) ⟨1114721, by rfl⟩ : syracuseStep 1486295 = 2229443) B2229443
theorem B1486315 : Blo 1486063 1486315 := bstep (se 1 (by rfl) ⟨1114736, by rfl⟩ : syracuseStep 1486315 = 2229473) B2229473
theorem B1486327 : Blo 1486063 1486327 := bstep (se 1 (by rfl) ⟨1114745, by rfl⟩ : syracuseStep 1486327 = 2229491) B2229491
theorem B5434883 : Blo 1486063 5434883 := bstep (se 1 (by rfl) ⟨4076162, by rfl⟩ : syracuseStep 5434883 = 8152325) B8152325
theorem B1486347 : Blo 1486063 1486347 := bstep (se 1 (by rfl) ⟨1114760, by rfl⟩ : syracuseStep 1486347 = 2229521) B2229521
theorem B2231819 : Blo 1486063 2231819 := bstep (se 1 (by rfl) ⟨1673864, by rfl⟩ : syracuseStep 2231819 = 3347729) B3347729
theorem B2821655 : Blo 1486063 2821655 := bstep (se 1 (by rfl) ⟨2116241, by rfl⟩ : syracuseStep 2821655 = 4232483) B4232483
theorem B1486359 : Blo 1486063 1486359 := bstep (se 1 (by rfl) ⟨1114769, by rfl⟩ : syracuseStep 1486359 = 2229539) B2229539
theorem B2231831 : Blo 1486063 2231831 := bstep (se 1 (by rfl) ⟨1673873, by rfl⟩ : syracuseStep 2231831 = 3347747) B3347747
theorem B1486379 : Blo 1486063 1486379 := bstep (se 1 (by rfl) ⟨1114784, by rfl⟩ : syracuseStep 1486379 = 2229569) B2229569
theorem B5017139 : Blo 1486063 5017139 := bstep (se 1 (by rfl) ⟨3762854, by rfl⟩ : syracuseStep 5017139 = 7525709) B7525709
theorem B1486391 : Blo 1486063 1486391 := bstep (se 1 (by rfl) ⟨1114793, by rfl⟩ : syracuseStep 1486391 = 2229587) B2229587
theorem B1486411 : Blo 1486063 1486411 := bstep (se 1 (by rfl) ⟨1114808, by rfl⟩ : syracuseStep 1486411 = 2229617) B2229617
theorem B1486423 : Blo 1486063 1486423 := bstep (se 1 (by rfl) ⟨1114817, by rfl⟩ : syracuseStep 1486423 = 2229635) B2229635
theorem B2231897 : Blo 1486063 2231897 := bstep (se 2 (by rfl) ⟨836961, by rfl⟩ : syracuseStep 2231897 = 1673923) B1673923
theorem B1486443 : Blo 1486063 1486443 := bstep (se 1 (by rfl) ⟨1114832, by rfl⟩ : syracuseStep 1486443 = 2229665) B2229665
theorem B1486455 : Blo 1486063 1486455 := bstep (se 1 (by rfl) ⟨1114841, by rfl⟩ : syracuseStep 1486455 = 2229683) B2229683
theorem B1486475 : Blo 1486063 1486475 := bstep (se 1 (by rfl) ⟨1114856, by rfl⟩ : syracuseStep 1486475 = 2229713) B2229713
theorem B1486487 : Blo 1486063 1486487 := bstep (se 1 (by rfl) ⟨1114865, by rfl⟩ : syracuseStep 1486487 = 2229731) B2229731
theorem B3346073 : Blo 1486063 3346073 := bstep (se 2 (by rfl) ⟨1254777, by rfl⟩ : syracuseStep 3346073 = 2509555) B2509555
theorem B1486507 : Blo 1486063 1486507 := bstep (se 1 (by rfl) ⟨1114880, by rfl⟩ : syracuseStep 1486507 = 2229761) B2229761
theorem B1486519 : Blo 1486063 1486519 := bstep (se 1 (by rfl) ⟨1114889, by rfl⟩ : syracuseStep 1486519 = 2229779) B2229779
theorem B1486539 : Blo 1486063 1486539 := bstep (se 1 (by rfl) ⟨1114904, by rfl⟩ : syracuseStep 1486539 = 2229809) B2229809
theorem B2232011 : Blo 1486063 2232011 := bstep (se 1 (by rfl) ⟨1674008, by rfl⟩ : syracuseStep 2232011 = 3348017) B3348017
theorem B1486551 : Blo 1486063 1486551 := bstep (se 1 (by rfl) ⟨1114913, by rfl⟩ : syracuseStep 1486551 = 2229827) B2229827
theorem B2117335 : Blo 1486063 2117335 := bstep (se 1 (by rfl) ⟨1588001, by rfl⟩ : syracuseStep 2117335 = 3176003) B3176003
theorem B2232023 : Blo 1486063 2232023 := bstep (se 1 (by rfl) ⟨1674017, by rfl⟩ : syracuseStep 2232023 = 3348035) B3348035
theorem B1486571 : Blo 1486063 1486571 := bstep (se 1 (by rfl) ⟨1114928, by rfl⟩ : syracuseStep 1486571 = 2229857) B2229857
theorem B3346163 : Blo 1486063 3346163 := bstep (se 1 (by rfl) ⟨2509622, by rfl⟩ : syracuseStep 3346163 = 5019245) B5019245
theorem B1486583 : Blo 1486063 1486583 := bstep (se 1 (by rfl) ⟨1114937, by rfl⟩ : syracuseStep 1486583 = 2229875) B2229875
theorem B1486603 : Blo 1486063 1486603 := bstep (se 1 (by rfl) ⟨1114952, by rfl⟩ : syracuseStep 1486603 = 2229905) B2229905
theorem B1486615 : Blo 1486063 1486615 := bstep (se 1 (by rfl) ⟨1114961, by rfl⟩ : syracuseStep 1486615 = 2229923) B2229923
theorem B3346199 : Blo 1486063 3346199 := bstep (se 1 (by rfl) ⟨2509649, by rfl⟩ : syracuseStep 3346199 = 5019299) B5019299
theorem B2510615 : Blo 1486063 2510615 := bstep (se 1 (by rfl) ⟨1882961, by rfl⟩ : syracuseStep 2510615 = 3765923) B3765923
theorem B2232089 : Blo 1486063 2232089 := bstep (se 2 (by rfl) ⟨837033, by rfl⟩ : syracuseStep 2232089 = 1674067) B1674067
theorem B1486635 : Blo 1486063 1486635 := bstep (se 1 (by rfl) ⟨1114976, by rfl⟩ : syracuseStep 1486635 = 2229953) B2229953
theorem B1486647 : Blo 1486063 1486647 := bstep (se 1 (by rfl) ⟨1114985, by rfl⟩ : syracuseStep 1486647 = 2229971) B2229971
theorem B8466241 : Blo 1486063 8466241 := bstep (se 2 (by rfl) ⟨3174840, by rfl⟩ : syracuseStep 8466241 = 6349681) B6349681
theorem B5017409 : Blo 1486063 5017409 := bstep (se 2 (by rfl) ⟨1881528, by rfl⟩ : syracuseStep 5017409 = 3763057) B3763057
theorem B1486667 : Blo 1486063 1486667 := bstep (se 1 (by rfl) ⟨1115000, by rfl⟩ : syracuseStep 1486667 = 2230001) B2230001
theorem B1486679 : Blo 1486063 1486679 := bstep (se 1 (by rfl) ⟨1115009, by rfl⟩ : syracuseStep 1486679 = 2230019) B2230019
theorem B2543447 : Blo 1486063 2543447 := bstep (se 1 (by rfl) ⟨1907585, by rfl⟩ : syracuseStep 2543447 = 3815171) B3815171
theorem B1486699 : Blo 1486063 1486699 := bstep (se 1 (by rfl) ⟨1115024, by rfl⟩ : syracuseStep 1486699 = 2230049) B2230049
theorem B1486711 : Blo 1486063 1486711 := bstep (se 1 (by rfl) ⟨1115033, by rfl⟩ : syracuseStep 1486711 = 2230067) B2230067
theorem B1486731 : Blo 1486063 1486731 := bstep (se 1 (by rfl) ⟨1115048, by rfl⟩ : syracuseStep 1486731 = 2230097) B2230097
theorem B1486743 : Blo 1486063 1486743 := bstep (se 1 (by rfl) ⟨1115057, by rfl⟩ : syracuseStep 1486743 = 2230115) B2230115
theorem B2510743 : Blo 1486063 2510743 := bstep (se 1 (by rfl) ⟨1883057, by rfl⟩ : syracuseStep 2510743 = 3766115) B3766115
theorem B1486763 : Blo 1486063 1486763 := bstep (se 1 (by rfl) ⟨1115072, by rfl⟩ : syracuseStep 1486763 = 2230145) B2230145
theorem B1486775 : Blo 1486063 1486775 := bstep (se 1 (by rfl) ⟨1115081, by rfl⟩ : syracuseStep 1486775 = 2230163) B2230163
theorem B1486795 : Blo 1486063 1486795 := bstep (se 1 (by rfl) ⟨1115096, by rfl⟩ : syracuseStep 1486795 = 2230193) B2230193
theorem B3764171 : Blo 1486063 3764171 := bstep (se 1 (by rfl) ⟨2823128, by rfl⟩ : syracuseStep 3764171 = 5646257) B5646257
theorem B3346379 : Blo 1486063 3346379 := bstep (se 1 (by rfl) ⟨2509784, by rfl⟩ : syracuseStep 3346379 = 5019569) B5019569
theorem B1486807 : Blo 1486063 1486807 := bstep (se 1 (by rfl) ⟨1115105, by rfl⟩ : syracuseStep 1486807 = 2230211) B2230211
theorem B1486827 : Blo 1486063 1486827 := bstep (se 1 (by rfl) ⟨1115120, by rfl⟩ : syracuseStep 1486827 = 2230241) B2230241
theorem B1486839 : Blo 1486063 1486839 := bstep (se 1 (by rfl) ⟨1115129, by rfl⟩ : syracuseStep 1486839 = 2230259) B2230259
theorem B3346433 : Blo 1486063 3346433 := bstep (se 2 (by rfl) ⟨1254912, by rfl⟩ : syracuseStep 3346433 = 2509825) B2509825
theorem B1486859 : Blo 1486063 1486859 := bstep (se 1 (by rfl) ⟨1115144, by rfl⟩ : syracuseStep 1486859 = 2230289) B2230289
theorem B1486871 : Blo 1486063 1486871 := bstep (se 1 (by rfl) ⟨1115153, by rfl⟩ : syracuseStep 1486871 = 2230307) B2230307
theorem B13750307 : Blo 1486063 13750307 := bstep (se 1 (by rfl) ⟨10312730, by rfl⟩ : syracuseStep 13750307 = 20625461) B20625461
theorem B1486891 : Blo 1486063 1486891 := bstep (se 1 (by rfl) ⟨1115168, by rfl⟩ : syracuseStep 1486891 = 2230337) B2230337
theorem B2822195 : Blo 1486063 2822195 := bstep (se 1 (by rfl) ⟨2116646, by rfl⟩ : syracuseStep 2822195 = 4233293) B4233293
theorem B1486903 : Blo 1486063 1486903 := bstep (se 1 (by rfl) ⟨1115177, by rfl⟩ : syracuseStep 1486903 = 2230355) B2230355
theorem B3305537 : Blo 1486063 3305537 := bstep (se 2 (by rfl) ⟨1239576, by rfl⟩ : syracuseStep 3305537 = 2479153) B2479153
theorem B1486923 : Blo 1486063 1486923 := bstep (se 1 (by rfl) ⟨1115192, by rfl⟩ : syracuseStep 1486923 = 2230385) B2230385
theorem B1486935 : Blo 1486063 1486935 := bstep (se 1 (by rfl) ⟨1115201, by rfl⟩ : syracuseStep 1486935 = 2230403) B2230403
theorem B1486955 : Blo 1486063 1486955 := bstep (se 1 (by rfl) ⟨1115216, by rfl⟩ : syracuseStep 1486955 = 2230433) B2230433
theorem B1486967 : Blo 1486063 1486967 := bstep (se 1 (by rfl) ⟨1115225, by rfl⟩ : syracuseStep 1486967 = 2230451) B2230451
theorem B7532675 : Blo 1486063 7532675 := bstep (se 1 (by rfl) ⟨5649506, by rfl⟩ : syracuseStep 7532675 = 11299013) B11299013
theorem B1486987 : Blo 1486063 1486987 := bstep (se 1 (by rfl) ⟨1115240, by rfl⟩ : syracuseStep 1486987 = 2230481) B2230481
theorem B1486999 : Blo 1486063 1486999 := bstep (se 1 (by rfl) ⟨1115249, by rfl⟩ : syracuseStep 1486999 = 2230499) B2230499
theorem B18346135 : Blo 1486063 18346135 := bstep (se 1 (by rfl) ⟨13759601, by rfl⟩ : syracuseStep 18346135 = 27519203) B27519203
theorem B1487019 : Blo 1486063 1487019 := bstep (se 1 (by rfl) ⟨1115264, by rfl⟩ : syracuseStep 1487019 = 2230529) B2230529
theorem B1487031 : Blo 1486063 1487031 := bstep (se 1 (by rfl) ⟨1115273, by rfl⟩ : syracuseStep 1487031 = 2230547) B2230547
theorem B1487051 : Blo 1486063 1487051 := bstep (se 1 (by rfl) ⟨1115288, by rfl⟩ : syracuseStep 1487051 = 2230577) B2230577
theorem B6353099 : Blo 1486063 6353099 := bstep (se 1 (by rfl) ⟨4764824, by rfl⟩ : syracuseStep 6353099 = 9529649) B9529649
theorem B1487063 : Blo 1486063 1487063 := bstep (se 1 (by rfl) ⟨1115297, by rfl⟩ : syracuseStep 1487063 = 2230595) B2230595
theorem B3346649 : Blo 1486063 3346649 := bstep (se 2 (by rfl) ⟨1254993, by rfl⟩ : syracuseStep 3346649 = 2509987) B2509987
theorem B1487083 : Blo 1486063 1487083 := bstep (se 1 (by rfl) ⟨1115312, by rfl⟩ : syracuseStep 1487083 = 2230625) B2230625
theorem B1487095 : Blo 1486063 1487095 := bstep (se 1 (by rfl) ⟨1115321, by rfl⟩ : syracuseStep 1487095 = 2230643) B2230643
theorem B1487115 : Blo 1486063 1487115 := bstep (se 1 (by rfl) ⟨1115336, by rfl⟩ : syracuseStep 1487115 = 2230673) B2230673
theorem B1487127 : Blo 1486063 1487127 := bstep (se 1 (by rfl) ⟨1115345, by rfl⟩ : syracuseStep 1487127 = 2230691) B2230691
theorem B1487147 : Blo 1486063 1487147 := bstep (se 1 (by rfl) ⟨1115360, by rfl⟩ : syracuseStep 1487147 = 2230721) B2230721
theorem B3346739 : Blo 1486063 3346739 := bstep (se 1 (by rfl) ⟨2510054, by rfl⟩ : syracuseStep 3346739 = 5020109) B5020109
theorem B1487159 : Blo 1486063 1487159 := bstep (se 1 (by rfl) ⟨1115369, by rfl⟩ : syracuseStep 1487159 = 2230739) B2230739
theorem B1487179 : Blo 1486063 1487179 := bstep (se 1 (by rfl) ⟨1115384, by rfl⟩ : syracuseStep 1487179 = 2230769) B2230769
theorem B1487191 : Blo 1486063 1487191 := bstep (se 1 (by rfl) ⟨1115393, by rfl⟩ : syracuseStep 1487191 = 2230787) B2230787
theorem B3346775 : Blo 1486063 3346775 := bstep (se 1 (by rfl) ⟨2510081, by rfl⟩ : syracuseStep 3346775 = 5020163) B5020163
theorem B5017949 : Blo 1486063 5017949 := bstep (se 3 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 5017949 = 1881731) B1881731
theorem B1487211 : Blo 1486063 1487211 := bstep (se 1 (by rfl) ⟨1115408, by rfl⟩ : syracuseStep 1487211 = 2230817) B2230817
theorem B1487223 : Blo 1486063 1487223 := bstep (se 1 (by rfl) ⟨1115417, by rfl⟩ : syracuseStep 1487223 = 2230835) B2230835
theorem B1487243 : Blo 1486063 1487243 := bstep (se 1 (by rfl) ⟨1115432, by rfl⟩ : syracuseStep 1487243 = 2230865) B2230865
theorem B1487255 : Blo 1486063 1487255 := bstep (se 1 (by rfl) ⟨1115441, by rfl⟩ : syracuseStep 1487255 = 2230883) B2230883
theorem B1487275 : Blo 1486063 1487275 := bstep (se 1 (by rfl) ⟨1115456, by rfl⟩ : syracuseStep 1487275 = 2230913) B2230913
theorem B1487287 : Blo 1486063 1487287 := bstep (se 1 (by rfl) ⟨1115465, by rfl⟩ : syracuseStep 1487287 = 2230931) B2230931
theorem B1487307 : Blo 1486063 1487307 := bstep (se 1 (by rfl) ⟨1115480, by rfl⟩ : syracuseStep 1487307 = 2230961) B2230961
theorem B1487319 : Blo 1486063 1487319 := bstep (se 1 (by rfl) ⟨1115489, by rfl⟩ : syracuseStep 1487319 = 2230979) B2230979
theorem B1487339 : Blo 1486063 1487339 := bstep (se 1 (by rfl) ⟨1115504, by rfl⟩ : syracuseStep 1487339 = 2231009) B2231009
theorem B1487351 : Blo 1486063 1487351 := bstep (se 1 (by rfl) ⟨1115513, by rfl⟩ : syracuseStep 1487351 = 2231027) B2231027
theorem B5648899 : Blo 1486063 5648899 := bstep (se 1 (by rfl) ⟨4236674, by rfl⟩ : syracuseStep 5648899 = 8473349) B8473349
theorem B1487371 : Blo 1486063 1487371 := bstep (se 1 (by rfl) ⟨1115528, by rfl⟩ : syracuseStep 1487371 = 2231057) B2231057
theorem B3346955 : Blo 1486063 3346955 := bstep (se 1 (by rfl) ⟨2510216, by rfl⟩ : syracuseStep 3346955 = 5020433) B5020433
theorem B2118155 : Blo 1486063 2118155 := bstep (se 1 (by rfl) ⟨1588616, by rfl⟩ : syracuseStep 2118155 = 3177233) B3177233
theorem B1487383 : Blo 1486063 1487383 := bstep (se 1 (by rfl) ⟨1115537, by rfl⟩ : syracuseStep 1487383 = 2231075) B2231075
theorem B2822681 : Blo 1486063 2822681 := bstep (se 2 (by rfl) ⟨1058505, by rfl⟩ : syracuseStep 2822681 = 2117011) B2117011
theorem B1487403 : Blo 1486063 1487403 := bstep (se 1 (by rfl) ⟨1115552, by rfl⟩ : syracuseStep 1487403 = 2231105) B2231105
theorem B1487415 : Blo 1486063 1487415 := bstep (se 1 (by rfl) ⟨1115561, by rfl⟩ : syracuseStep 1487415 = 2231123) B2231123
theorem B3347009 : Blo 1486063 3347009 := bstep (se 2 (by rfl) ⟨1255128, by rfl⟩ : syracuseStep 3347009 = 2510257) B2510257
theorem B1487435 : Blo 1486063 1487435 := bstep (se 1 (by rfl) ⟨1115576, by rfl⟩ : syracuseStep 1487435 = 2231153) B2231153
theorem B1487447 : Blo 1486063 1487447 := bstep (se 1 (by rfl) ⟨1115585, by rfl⟩ : syracuseStep 1487447 = 2231171) B2231171
theorem B1487467 : Blo 1486063 1487467 := bstep (se 1 (by rfl) ⟨1115600, by rfl⟩ : syracuseStep 1487467 = 2231201) B2231201
theorem B1487479 : Blo 1486063 1487479 := bstep (se 1 (by rfl) ⟨1115609, by rfl⟩ : syracuseStep 1487479 = 2231219) B2231219
theorem B1487499 : Blo 1486063 1487499 := bstep (se 1 (by rfl) ⟨1115624, by rfl⟩ : syracuseStep 1487499 = 2231249) B2231249
theorem B1487511 : Blo 1486063 1487511 := bstep (se 1 (by rfl) ⟨1115633, by rfl⟩ : syracuseStep 1487511 = 2231267) B2231267
theorem B1487531 : Blo 1486063 1487531 := bstep (se 1 (by rfl) ⟨1115648, by rfl⟩ : syracuseStep 1487531 = 2231297) B2231297
theorem B1487543 : Blo 1486063 1487543 := bstep (se 1 (by rfl) ⟨1115657, by rfl⟩ : syracuseStep 1487543 = 2231315) B2231315
theorem B1487563 : Blo 1486063 1487563 := bstep (se 1 (by rfl) ⟨1115672, by rfl⟩ : syracuseStep 1487563 = 2231345) B2231345
theorem B1487575 : Blo 1486063 1487575 := bstep (se 1 (by rfl) ⟨1115681, by rfl⟩ : syracuseStep 1487575 = 2231363) B2231363
theorem B1487595 : Blo 1486063 1487595 := bstep (se 1 (by rfl) ⟨1115696, by rfl⟩ : syracuseStep 1487595 = 2231393) B2231393
theorem B1487607 : Blo 1486063 1487607 := bstep (se 1 (by rfl) ⟨1115705, by rfl⟩ : syracuseStep 1487607 = 2231411) B2231411
theorem B1487627 : Blo 1486063 1487627 := bstep (se 1 (by rfl) ⟨1115720, by rfl⟩ : syracuseStep 1487627 = 2231441) B2231441
theorem B6435607 : Blo 1486063 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B1487639 : Blo 1486063 1487639 := bstep (se 1 (by rfl) ⟨1115729, by rfl⟩ : syracuseStep 1487639 = 2231459) B2231459
theorem B3347225 : Blo 1486063 3347225 := bstep (se 2 (by rfl) ⟨1255209, by rfl⟩ : syracuseStep 3347225 = 2510419) B2510419
theorem B1487659 : Blo 1486063 1487659 := bstep (se 1 (by rfl) ⟨1115744, by rfl⟩ : syracuseStep 1487659 = 2231489) B2231489
theorem B5649203 : Blo 1486063 5649203 := bstep (se 1 (by rfl) ⟨4236902, by rfl⟩ : syracuseStep 5649203 = 8473805) B8473805
theorem B1487671 : Blo 1486063 1487671 := bstep (se 1 (by rfl) ⟨1115753, by rfl⟩ : syracuseStep 1487671 = 2231507) B2231507
theorem B1487691 : Blo 1486063 1487691 := bstep (se 1 (by rfl) ⟨1115768, by rfl⟩ : syracuseStep 1487691 = 2231537) B2231537
theorem B1487703 : Blo 1486063 1487703 := bstep (se 1 (by rfl) ⟨1115777, by rfl⟩ : syracuseStep 1487703 = 2231555) B2231555
theorem B1487723 : Blo 1486063 1487723 := bstep (se 1 (by rfl) ⟨1115792, by rfl⟩ : syracuseStep 1487723 = 2231585) B2231585
theorem B3347315 : Blo 1486063 3347315 := bstep (se 1 (by rfl) ⟨2510486, by rfl⟩ : syracuseStep 3347315 = 5020973) B5020973
theorem B1487735 : Blo 1486063 1487735 := bstep (se 1 (by rfl) ⟨1115801, by rfl⟩ : syracuseStep 1487735 = 2231603) B2231603
theorem B1487755 : Blo 1486063 1487755 := bstep (se 1 (by rfl) ⟨1115816, by rfl⟩ : syracuseStep 1487755 = 2231633) B2231633
theorem B3175319 : Blo 1486063 3175319 := bstep (se 1 (by rfl) ⟨2381489, by rfl⟩ : syracuseStep 3175319 = 4762979) B4762979
theorem B3765143 : Blo 1486063 3765143 := bstep (se 1 (by rfl) ⟨2823857, by rfl⟩ : syracuseStep 3765143 = 5647715) B5647715
theorem B3347351 : Blo 1486063 3347351 := bstep (se 1 (by rfl) ⟨2510513, by rfl⟩ : syracuseStep 3347351 = 5021027) B5021027
theorem B1487767 : Blo 1486063 1487767 := bstep (se 1 (by rfl) ⟨1115825, by rfl⟩ : syracuseStep 1487767 = 2231651) B2231651
theorem B1487787 : Blo 1486063 1487787 := bstep (se 1 (by rfl) ⟨1115840, by rfl⟩ : syracuseStep 1487787 = 2231681) B2231681
theorem B1487799 : Blo 1486063 1487799 := bstep (se 1 (by rfl) ⟨1115849, by rfl⟩ : syracuseStep 1487799 = 2231699) B2231699
theorem B2380747 : Blo 1486063 2380747 := bstep (se 1 (by rfl) ⟨1785560, by rfl⟩ : syracuseStep 2380747 = 3571121) B3571121
theorem B4764619 : Blo 1486063 4764619 := bstep (se 1 (by rfl) ⟨3573464, by rfl⟩ : syracuseStep 4764619 = 7146929) B7146929
theorem B1487819 : Blo 1486063 1487819 := bstep (se 1 (by rfl) ⟨1115864, by rfl⟩ : syracuseStep 1487819 = 2231729) B2231729
theorem B1487831 : Blo 1486063 1487831 := bstep (se 1 (by rfl) ⟨1115873, by rfl⟩ : syracuseStep 1487831 = 2231747) B2231747
theorem B1487851 : Blo 1486063 1487851 := bstep (se 1 (by rfl) ⟨1115888, by rfl⟩ : syracuseStep 1487851 = 2231777) B2231777
theorem B1487863 : Blo 1486063 1487863 := bstep (se 1 (by rfl) ⟨1115897, by rfl⟩ : syracuseStep 1487863 = 2231795) B2231795
theorem B1487883 : Blo 1486063 1487883 := bstep (se 1 (by rfl) ⟨1115912, by rfl⟩ : syracuseStep 1487883 = 2231825) B2231825
theorem B1487895 : Blo 1486063 1487895 := bstep (se 1 (by rfl) ⟨1115921, by rfl⟩ : syracuseStep 1487895 = 2231843) B2231843
theorem B1487915 : Blo 1486063 1487915 := bstep (se 1 (by rfl) ⟨1115936, by rfl⟩ : syracuseStep 1487915 = 2231873) B2231873
theorem B1487927 : Blo 1486063 1487927 := bstep (se 1 (by rfl) ⟨1115945, by rfl⟩ : syracuseStep 1487927 = 2231891) B2231891
theorem B3347531 : Blo 1486063 3347531 := bstep (se 1 (by rfl) ⟨2510648, by rfl⟩ : syracuseStep 3347531 = 5021297) B5021297
theorem B1487947 : Blo 1486063 1487947 := bstep (se 1 (by rfl) ⟨1115960, by rfl⟩ : syracuseStep 1487947 = 2231921) B2231921
theorem B1487959 : Blo 1486063 1487959 := bstep (se 1 (by rfl) ⟨1115969, by rfl⟩ : syracuseStep 1487959 = 2231939) B2231939
theorem B9524317 : Blo 1486063 9524317 := bstep (se 3 (by rfl) ⟨1785809, by rfl⟩ : syracuseStep 9524317 = 3571619) B3571619
theorem B1487979 : Blo 1486063 1487979 := bstep (se 1 (by rfl) ⟨1115984, by rfl⟩ : syracuseStep 1487979 = 2231969) B2231969
theorem B1487991 : Blo 1486063 1487991 := bstep (se 1 (by rfl) ⟨1115993, by rfl⟩ : syracuseStep 1487991 = 2231987) B2231987
theorem B3347585 : Blo 1486063 3347585 := bstep (se 2 (by rfl) ⟨1255344, by rfl⟩ : syracuseStep 3347585 = 2510689) B2510689
theorem B1488011 : Blo 1486063 1488011 := bstep (se 1 (by rfl) ⟨1116008, by rfl⟩ : syracuseStep 1488011 = 2232017) B2232017
theorem B1488023 : Blo 1486063 1488023 := bstep (se 1 (by rfl) ⟨1116017, by rfl⟩ : syracuseStep 1488023 = 2232035) B2232035
theorem B1488043 : Blo 1486063 1488043 := bstep (se 1 (by rfl) ⟨1116032, by rfl⟩ : syracuseStep 1488043 = 2232065) B2232065
theorem B4764851 : Blo 1486063 4764851 := bstep (se 1 (by rfl) ⟨3573638, by rfl⟩ : syracuseStep 4764851 = 7147277) B7147277
theorem B1488055 : Blo 1486063 1488055 := bstep (se 1 (by rfl) ⟨1116041, by rfl⟩ : syracuseStep 1488055 = 2232083) B2232083
theorem B2381003 : Blo 1486063 2381003 := bstep (se 1 (by rfl) ⟨1785752, by rfl⟩ : syracuseStep 2381003 = 3571505) B3571505
theorem B3175627 : Blo 1486063 3175627 := bstep (se 1 (by rfl) ⟨2381720, by rfl⟩ : syracuseStep 3175627 = 4763441) B4763441
theorem B6354227 : Blo 1486063 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B3347801 : Blo 1486063 3347801 := bstep (se 2 (by rfl) ⟨1255425, by rfl⟩ : syracuseStep 3347801 = 2510851) B2510851
theorem B4519261 : Blo 1486063 4519261 := bstep (se 3 (by rfl) ⟨847361, by rfl⟩ : syracuseStep 4519261 = 1694723) B1694723
theorem B4289885 : Blo 1486063 4289885 := bstep (se 3 (by rfl) ⟨804353, by rfl⟩ : syracuseStep 4289885 = 1608707) B1608707
theorem B11285891 : Blo 1486063 11285891 := bstep (se 1 (by rfl) ⟨8464418, by rfl⟩ : syracuseStep 11285891 = 16928837) B16928837
theorem B2381195 : Blo 1486063 2381195 := bstep (se 1 (by rfl) ⟨1785896, by rfl⟩ : syracuseStep 2381195 = 3571793) B3571793
theorem B3347891 : Blo 1486063 3347891 := bstep (se 1 (by rfl) ⟨2510918, by rfl⟩ : syracuseStep 3347891 = 5021837) B5021837
theorem B5649857 : Blo 1486063 5649857 := bstep (se 2 (by rfl) ⟨2118696, by rfl⟩ : syracuseStep 5649857 = 4237393) B4237393
theorem B5019083 : Blo 1486063 5019083 := bstep (se 1 (by rfl) ⟨3764312, by rfl⟩ : syracuseStep 5019083 = 7528625) B7528625
theorem B1881559 : Blo 1486063 1881559 := bstep (se 1 (by rfl) ⟨1411169, by rfl⟩ : syracuseStep 1881559 = 2822339) B2822339
theorem B4232665 : Blo 1486063 4232665 := bstep (se 2 (by rfl) ⟨1587249, by rfl⟩ : syracuseStep 4232665 = 3174499) B3174499
theorem B3347927 : Blo 1486063 3347927 := bstep (se 1 (by rfl) ⟨2510945, by rfl⟩ : syracuseStep 3347927 = 5021891) B5021891
theorem B4077017 : Blo 1486063 4077017 := bstep (se 2 (by rfl) ⟨1528881, by rfl⟩ : syracuseStep 4077017 = 3057763) B3057763
theorem B13563409 : Blo 1486063 13563409 := bstep (se 2 (by rfl) ⟨5086278, by rfl⟩ : syracuseStep 13563409 = 10172557) B10172557
theorem B3765811 : Blo 1486063 3765811 := bstep (se 1 (by rfl) ⟨2824358, by rfl⟩ : syracuseStep 3765811 = 5648717) B5648717
theorem B3348107 : Blo 1486063 3348107 := bstep (se 1 (by rfl) ⟨2511080, by rfl⟩ : syracuseStep 3348107 = 5022161) B5022161
theorem B7149235 : Blo 1486063 7149235 := bstep (se 1 (by rfl) ⟨5361926, by rfl⟩ : syracuseStep 7149235 = 10723853) B10723853
theorem B3765953 : Blo 1486063 3765953 := bstep (se 2 (by rfl) ⟨1412232, by rfl⟩ : syracuseStep 3765953 = 2824465) B2824465
theorem B5019353 : Blo 1486063 5019353 := bstep (se 2 (by rfl) ⟨1882257, by rfl⟩ : syracuseStep 5019353 = 3764515) B3764515
theorem B6616849 : Blo 1486063 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B2578265 : Blo 1486063 2578265 := bstep (se 2 (by rfl) ⟨966849, by rfl⟩ : syracuseStep 2578265 = 1933699) B1933699
theorem B4233053 : Blo 1486063 4233053 := bstep (se 3 (by rfl) ⟨793697, by rfl⟩ : syracuseStep 4233053 = 1587395) B1587395
theorem B9533315 : Blo 1486063 9533315 := bstep (se 1 (by rfl) ⟨7149986, by rfl⟩ : syracuseStep 9533315 = 14299973) B14299973
theorem B2824139 : Blo 1486063 2824139 := bstep (se 1 (by rfl) ⟨2118104, by rfl⟩ : syracuseStep 2824139 = 4236209) B4236209
theorem B16939043 : Blo 1486063 16939043 := bstep (se 1 (by rfl) ⟨12704282, by rfl⟩ : syracuseStep 16939043 = 25408565) B25408565
theorem B13572161 : Blo 1486063 13572161 := bstep (se 2 (by rfl) ⟨5089560, by rfl⟩ : syracuseStep 13572161 = 10179121) B10179121
theorem B2824321 : Blo 1486063 2824321 := bstep (se 2 (by rfl) ⟨1059120, by rfl⟩ : syracuseStep 2824321 = 2118241) B2118241
theorem B2381977 : Blo 1486063 2381977 := bstep (se 2 (by rfl) ⟨893241, by rfl⟩ : syracuseStep 2381977 = 1786483) B1786483
theorem B1882379 : Blo 1486063 1882379 := bstep (se 1 (by rfl) ⟨1411784, by rfl⟩ : syracuseStep 1882379 = 2823569) B2823569
theorem B5020055 : Blo 1486063 5020055 := bstep (se 1 (by rfl) ⟨3765041, by rfl⟩ : syracuseStep 5020055 = 7530083) B7530083
theorem B3176857 : Blo 1486063 3176857 := bstep (se 2 (by rfl) ⟨1191321, by rfl⟩ : syracuseStep 3176857 = 2382643) B2382643
theorem B1718743 : Blo 1486063 1718743 := bstep (se 1 (by rfl) ⟨1289057, by rfl⟩ : syracuseStep 1718743 = 2578115) B2578115
theorem B10721753 : Blo 1486063 10721753 := bstep (se 2 (by rfl) ⟨4020657, by rfl⟩ : syracuseStep 10721753 = 8041315) B8041315
theorem B51501581 : Blo 1486063 51501581 := bstep (se 3 (by rfl) ⟨9656546, by rfl⟩ : syracuseStep 51501581 = 19313093) B19313093
theorem B2824769 : Blo 1486063 2824769 := bstep (se 2 (by rfl) ⟨1059288, by rfl⟩ : syracuseStep 2824769 = 2118577) B2118577
theorem B25762373 : Blo 1486063 25762373 := bstep (se 4 (by rfl) ⟨2415222, by rfl⟩ : syracuseStep 25762373 = 4830445) B4830445
theorem B7527005 : Blo 1486063 7527005 := bstep (se 3 (by rfl) ⟨1411313, by rfl⟩ : syracuseStep 7527005 = 2822627) B2822627
theorem B5643053 : Blo 1486063 5643053 := bstep (se 3 (by rfl) ⟨1058072, by rfl⟩ : syracuseStep 5643053 = 2116145) B2116145
theorem B11443045 : Blo 1486063 11443045 := bstep (se 4 (by rfl) ⟨1072785, by rfl⟩ : syracuseStep 11443045 = 2145571) B2145571
theorem B10181477 : Blo 1486063 10181477 := bstep (se 4 (by rfl) ⟨954513, by rfl⟩ : syracuseStep 10181477 = 1909027) B1909027
theorem B1588087 : Blo 1486063 1588087 := bstep (se 1 (by rfl) ⟨1191065, by rfl⟩ : syracuseStep 1588087 = 2382131) B2382131
theorem B5020595 : Blo 1486063 5020595 := bstep (se 1 (by rfl) ⟨3765446, by rfl⟩ : syracuseStep 5020595 = 7530893) B7530893
theorem B1883083 : Blo 1486063 1883083 := bstep (se 1 (by rfl) ⟨1412312, by rfl⟩ : syracuseStep 1883083 = 2824625) B2824625
theorem B1588343 : Blo 1486063 1588343 := bstep (se 1 (by rfl) ⟨1191257, by rfl⟩ : syracuseStep 1588343 = 2382515) B2382515
theorem B6356141 : Blo 1486063 6356141 := bstep (se 3 (by rfl) ⟨1191776, by rfl⟩ : syracuseStep 6356141 = 2383553) B2383553
theorem B8469683 : Blo 1486063 8469683 := bstep (se 1 (by rfl) ⟨6352262, by rfl⟩ : syracuseStep 8469683 = 12704525) B12704525
theorem B5020865 : Blo 1486063 5020865 := bstep (se 2 (by rfl) ⟨1882824, by rfl⟩ : syracuseStep 5020865 = 3765649) B3765649
theorem B3054835 : Blo 1486063 3054835 := bstep (se 1 (by rfl) ⟨2291126, by rfl⟩ : syracuseStep 3054835 = 4582253) B4582253
theorem B6348077 : Blo 1486063 6348077 := bstep (se 3 (by rfl) ⟨1190264, by rfl⟩ : syracuseStep 6348077 = 2380529) B2380529
theorem B7142701 : Blo 1486063 7142701 := bstep (se 3 (by rfl) ⟨1339256, by rfl⟩ : syracuseStep 7142701 = 2678513) B2678513
theorem B5643827 : Blo 1486063 5643827 := bstep (se 1 (by rfl) ⟨4232870, by rfl⟩ : syracuseStep 5643827 = 8465741) B8465741
theorem B1588907 : Blo 1486063 1588907 := bstep (se 1 (by rfl) ⟨1191680, by rfl⟩ : syracuseStep 1588907 = 2383361) B2383361
theorem B6110923 : Blo 1486063 6110923 := bstep (se 1 (by rfl) ⟨4583192, by rfl⟩ : syracuseStep 6110923 = 9166385) B9166385
theorem B5021405 : Blo 1486063 5021405 := bstep (se 3 (by rfl) ⟨941513, by rfl⟩ : syracuseStep 5021405 = 1883027) B1883027
theorem B3825625 : Blo 1486063 3825625 := bstep (se 2 (by rfl) ⟨1434609, by rfl⟩ : syracuseStep 3825625 = 2869219) B2869219
theorem B18087947 : Blo 1486063 18087947 := bstep (se 1 (by rfl) ⟨13565960, by rfl⟩ : syracuseStep 18087947 = 27131921) B27131921
theorem B9166871 : Blo 1486063 9166871 := bstep (se 1 (by rfl) ⟨6875153, by rfl⟩ : syracuseStep 9166871 = 13750307) B13750307
theorem B2203691 : Blo 1486063 2203691 := bstep (se 1 (by rfl) ⟨1652768, by rfl⟩ : syracuseStep 2203691 = 3305537) B3305537
theorem B8470615 : Blo 1486063 8470615 := bstep (se 1 (by rfl) ⟨6352961, by rfl⟩ : syracuseStep 8470615 = 12705923) B12705923
theorem B5021783 : Blo 1486063 5021783 := bstep (se 1 (by rfl) ⟨3766337, by rfl⟩ : syracuseStep 5021783 = 7532675) B7532675
theorem B4292723 : Blo 1486063 4292723 := bstep (se 1 (by rfl) ⟨3219542, by rfl⟩ : syracuseStep 4292723 = 6439085) B6439085
theorem B4235399 : Blo 1486063 4235399 := bstep (se 1 (by rfl) ⟨3176549, by rfl⟩ : syracuseStep 4235399 = 6353099) B6353099
theorem B19062985 : Blo 1486063 19062985 := bstep (se 2 (by rfl) ⟨7148619, by rfl⟩ : syracuseStep 19062985 = 14297239) B14297239
theorem B24461513 : Blo 1486063 24461513 := bstep (se 2 (by rfl) ⟨9173067, by rfl⟩ : syracuseStep 24461513 = 18346135) B18346135
theorem B5644525 : Blo 1486063 5644525 := bstep (se 3 (by rfl) ⟨1058348, by rfl⟩ : syracuseStep 5644525 = 2116697) B2116697
theorem B4235581 : Blo 1486063 4235581 := bstep (se 3 (by rfl) ⟨794171, by rfl⟩ : syracuseStep 4235581 = 1588343) B1588343
theorem B5358109 : Blo 1486063 5358109 := bstep (se 3 (by rfl) ⟨1004645, by rfl⟩ : syracuseStep 5358109 = 2009291) B2009291
theorem B5644829 : Blo 1486063 5644829 := bstep (se 3 (by rfl) ⟨1058405, by rfl⟩ : syracuseStep 5644829 = 2116811) B2116811
theorem B4235809 : Blo 1486063 4235809 := bstep (se 2 (by rfl) ⟨1588428, by rfl⟩ : syracuseStep 4235809 = 3176857) B3176857
theorem B3572311 : Blo 1486063 3572311 := bstep (se 1 (by rfl) ⟨2679233, by rfl⟩ : syracuseStep 3572311 = 5358467) B5358467
theorem B25748161 : Blo 1486063 25748161 := bstep (se 2 (by rfl) ⟨9655560, by rfl⟩ : syracuseStep 25748161 = 19311121) B19311121
theorem B32604889 : Blo 1486063 32604889 := bstep (se 2 (by rfl) ⟨12226833, by rfl⟩ : syracuseStep 32604889 = 24453667) B24453667
theorem B1671943 : Blo 1486063 1671943 := bstep (se 1 (by rfl) ⟨1253957, by rfl⟩ : syracuseStep 1671943 = 2507915) B2507915
theorem B4236151 : Blo 1486063 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B2859923 : Blo 1486063 2859923 := bstep (se 1 (by rfl) ⟨2144942, by rfl⟩ : syracuseStep 2859923 = 4289885) B4289885
theorem B2229179 : Blo 1486063 2229179 := bstep (se 1 (by rfl) ⟨1671884, by rfl⟩ : syracuseStep 2229179 = 3343769) B3343769
theorem B1672123 : Blo 1486063 1672123 := bstep (se 1 (by rfl) ⟨1254092, by rfl⟩ : syracuseStep 1672123 = 2508185) B2508185
theorem B2229239 : Blo 1486063 2229239 := bstep (se 1 (by rfl) ⟨1671929, by rfl⟩ : syracuseStep 2229239 = 3343859) B3343859
theorem B2229263 : Blo 1486063 2229263 := bstep (se 1 (by rfl) ⟨1671947, by rfl⟩ : syracuseStep 2229263 = 3343895) B3343895
theorem B3015695 : Blo 1486063 3015695 := bstep (se 1 (by rfl) ⟨2261771, by rfl⟩ : syracuseStep 3015695 = 4523543) B4523543
theorem B6349853 : Blo 1486063 6349853 := bstep (se 3 (by rfl) ⟨1190597, by rfl⟩ : syracuseStep 6349853 = 2381195) B2381195
theorem B2229305 : Blo 1486063 2229305 := bstep (se 2 (by rfl) ⟨835989, by rfl⟩ : syracuseStep 2229305 = 1671979) B1671979
theorem B2229383 : Blo 1486063 2229383 := bstep (se 1 (by rfl) ⟨1672037, by rfl⟩ : syracuseStep 2229383 = 3344075) B3344075
theorem B2229419 : Blo 1486063 2229419 := bstep (se 1 (by rfl) ⟨1672064, by rfl⟩ : syracuseStep 2229419 = 3344129) B3344129
theorem B12870829 : Blo 1486063 12870829 := bstep (se 3 (by rfl) ⟨2413280, by rfl⟩ : syracuseStep 12870829 = 4826561) B4826561
theorem B2229449 : Blo 1486063 2229449 := bstep (se 2 (by rfl) ⟨836043, by rfl⟩ : syracuseStep 2229449 = 1672087) B1672087
theorem B2229563 : Blo 1486063 2229563 := bstep (se 1 (by rfl) ⟨1672172, by rfl⟩ : syracuseStep 2229563 = 3344345) B3344345
theorem B2508151 : Blo 1486063 2508151 := bstep (se 1 (by rfl) ⟨1881113, by rfl⟩ : syracuseStep 2508151 = 3762227) B3762227
theorem B2229623 : Blo 1486063 2229623 := bstep (se 1 (by rfl) ⟨1672217, by rfl⟩ : syracuseStep 2229623 = 3344435) B3344435
theorem B3343751 : Blo 1486063 3343751 := bstep (se 1 (by rfl) ⟨2507813, by rfl⟩ : syracuseStep 3343751 = 5015627) B5015627
theorem B2229647 : Blo 1486063 2229647 := bstep (se 1 (by rfl) ⟨1672235, by rfl⟩ : syracuseStep 2229647 = 3344471) B3344471
theorem B1672591 : Blo 1486063 1672591 := bstep (se 1 (by rfl) ⟨1254443, by rfl⟩ : syracuseStep 1672591 = 2508887) B2508887
theorem B2229689 : Blo 1486063 2229689 := bstep (se 2 (by rfl) ⟨836133, by rfl⟩ : syracuseStep 2229689 = 1672267) B1672267
theorem B12699089 : Blo 1486063 12699089 := bstep (se 2 (by rfl) ⟨4762158, by rfl⟩ : syracuseStep 12699089 = 9524317) B9524317
theorem B2229767 : Blo 1486063 2229767 := bstep (se 1 (by rfl) ⟨1672325, by rfl⟩ : syracuseStep 2229767 = 3344651) B3344651
theorem B2229803 : Blo 1486063 2229803 := bstep (se 1 (by rfl) ⟨1672352, by rfl⟩ : syracuseStep 2229803 = 3344705) B3344705
theorem B2901547 : Blo 1486063 2901547 := bstep (se 1 (by rfl) ⟨2176160, by rfl⟩ : syracuseStep 2901547 = 4352321) B4352321
theorem B3343931 : Blo 1486063 3343931 := bstep (se 1 (by rfl) ⟨2507948, by rfl⟩ : syracuseStep 3343931 = 5015897) B5015897
theorem B2508347 : Blo 1486063 2508347 := bstep (se 1 (by rfl) ⟨1881260, by rfl⟩ : syracuseStep 2508347 = 3762521) B3762521
theorem B2229833 : Blo 1486063 2229833 := bstep (se 2 (by rfl) ⟨836187, by rfl⟩ : syracuseStep 2229833 = 1672375) B1672375
theorem B4073113 : Blo 1486063 4073113 := bstep (se 2 (by rfl) ⟨1527417, by rfl⟩ : syracuseStep 4073113 = 3054835) B3054835
theorem B34334387 : Blo 1486063 34334387 := bstep (se 1 (by rfl) ⟨25750790, by rfl⟩ : syracuseStep 34334387 = 51501581) B51501581
theorem B3344057 : Blo 1486063 3344057 := bstep (se 2 (by rfl) ⟨1254021, by rfl⟩ : syracuseStep 3344057 = 2508043) B2508043
theorem B2229947 : Blo 1486063 2229947 := bstep (se 1 (by rfl) ⟨1672460, by rfl⟩ : syracuseStep 2229947 = 3344921) B3344921
theorem B2230007 : Blo 1486063 2230007 := bstep (se 1 (by rfl) ⟨1672505, by rfl⟩ : syracuseStep 2230007 = 3345011) B3345011
theorem B2230031 : Blo 1486063 2230031 := bstep (se 1 (by rfl) ⟨1672523, by rfl⟩ : syracuseStep 2230031 = 3345047) B3345047
theorem B4237085 : Blo 1486063 4237085 := bstep (se 3 (by rfl) ⟨794453, by rfl⟩ : syracuseStep 4237085 = 1588907) B1588907
theorem B2230073 : Blo 1486063 2230073 := bstep (se 2 (by rfl) ⟨836277, by rfl⟩ : syracuseStep 2230073 = 1672555) B1672555
theorem B3762035 : Blo 1486063 3762035 := bstep (se 1 (by rfl) ⟨2821526, by rfl⟩ : syracuseStep 3762035 = 5643053) B5643053
theorem B2230151 : Blo 1486063 2230151 := bstep (se 1 (by rfl) ⟨1672613, by rfl⟩ : syracuseStep 2230151 = 3345227) B3345227
theorem B1673095 : Blo 1486063 1673095 := bstep (se 1 (by rfl) ⟨1254821, by rfl⟩ : syracuseStep 1673095 = 2509643) B2509643
theorem B2230187 : Blo 1486063 2230187 := bstep (se 1 (by rfl) ⟨1672640, by rfl⟩ : syracuseStep 2230187 = 3345281) B3345281
theorem B2508745 : Blo 1486063 2508745 := bstep (se 2 (by rfl) ⟨940779, by rfl⟩ : syracuseStep 2508745 = 1881559) B1881559
theorem B2230217 : Blo 1486063 2230217 := bstep (se 2 (by rfl) ⟨836331, by rfl⟩ : syracuseStep 2230217 = 1672663) B1672663
theorem B3344399 : Blo 1486063 3344399 := bstep (se 1 (by rfl) ⟨2508299, by rfl⟩ : syracuseStep 3344399 = 5016599) B5016599
theorem B8472599 : Blo 1486063 8472599 := bstep (se 1 (by rfl) ⟨6354449, by rfl⟩ : syracuseStep 8472599 = 12708899) B12708899
theorem B3344417 : Blo 1486063 3344417 := bstep (se 2 (by rfl) ⟨1254156, by rfl⟩ : syracuseStep 3344417 = 2508313) B2508313
theorem B2230331 : Blo 1486063 2230331 := bstep (se 1 (by rfl) ⟨1672748, by rfl⟩ : syracuseStep 2230331 = 3345497) B3345497
theorem B1673275 : Blo 1486063 1673275 := bstep (se 1 (by rfl) ⟨1254956, by rfl⟩ : syracuseStep 1673275 = 2509913) B2509913
theorem B4237427 : Blo 1486063 4237427 := bstep (se 1 (by rfl) ⟨3178070, by rfl⟩ : syracuseStep 4237427 = 6356141) B6356141
theorem B2230391 : Blo 1486063 2230391 := bstep (se 1 (by rfl) ⟨1672793, by rfl⟩ : syracuseStep 2230391 = 3345587) B3345587
theorem B5646455 : Blo 1486063 5646455 := bstep (se 1 (by rfl) ⟨4234841, by rfl⟩ : syracuseStep 5646455 = 8469683) B8469683
theorem B2230415 : Blo 1486063 2230415 := bstep (se 1 (by rfl) ⟨1672811, by rfl⟩ : syracuseStep 2230415 = 3345623) B3345623
theorem B2230457 : Blo 1486063 2230457 := bstep (se 2 (by rfl) ⟨836421, by rfl⟩ : syracuseStep 2230457 = 1672843) B1672843
theorem B2230535 : Blo 1486063 2230535 := bstep (se 1 (by rfl) ⟨1672901, by rfl⟩ : syracuseStep 2230535 = 3345803) B3345803
theorem B2230571 : Blo 1486063 2230571 := bstep (se 1 (by rfl) ⟨1672928, by rfl⟩ : syracuseStep 2230571 = 3345857) B3345857
theorem B2230601 : Blo 1486063 2230601 := bstep (se 2 (by rfl) ⟨836475, by rfl⟩ : syracuseStep 2230601 = 1672951) B1672951
theorem B3623255 : Blo 1486063 3623255 := bstep (se 1 (by rfl) ⟨2717441, by rfl⟩ : syracuseStep 3623255 = 5434883) B5434883
theorem B3762551 : Blo 1486063 3762551 := bstep (se 1 (by rfl) ⟨2821913, by rfl⟩ : syracuseStep 3762551 = 5643827) B5643827
theorem B3344759 : Blo 1486063 3344759 := bstep (se 1 (by rfl) ⟨2508569, by rfl⟩ : syracuseStep 3344759 = 5017139) B5017139
theorem B2230715 : Blo 1486063 2230715 := bstep (se 1 (by rfl) ⟨1673036, by rfl⟩ : syracuseStep 2230715 = 3346073) B3346073
theorem B2230775 : Blo 1486063 2230775 := bstep (se 1 (by rfl) ⟨1673081, by rfl⟩ : syracuseStep 2230775 = 3346163) B3346163
theorem B2230799 : Blo 1486063 2230799 := bstep (se 1 (by rfl) ⟨1673099, by rfl⟩ : syracuseStep 2230799 = 3346199) B3346199
theorem B1673743 : Blo 1486063 1673743 := bstep (se 1 (by rfl) ⟨1255307, by rfl⟩ : syracuseStep 1673743 = 2510615) B2510615
theorem B3344939 : Blo 1486063 3344939 := bstep (se 1 (by rfl) ⟨2508704, by rfl⟩ : syracuseStep 3344939 = 5017409) B5017409
theorem B2230841 : Blo 1486063 2230841 := bstep (se 2 (by rfl) ⟨836565, by rfl⟩ : syracuseStep 2230841 = 1673131) B1673131
theorem B2509447 : Blo 1486063 2509447 := bstep (se 1 (by rfl) ⟨1882085, by rfl⟩ : syracuseStep 2509447 = 3764171) B3764171
theorem B2230919 : Blo 1486063 2230919 := bstep (se 1 (by rfl) ⟨1673189, by rfl⟩ : syracuseStep 2230919 = 3346379) B3346379
theorem B2230955 : Blo 1486063 2230955 := bstep (se 1 (by rfl) ⟨1673216, by rfl⟩ : syracuseStep 2230955 = 3346433) B3346433
theorem B2230985 : Blo 1486063 2230985 := bstep (se 2 (by rfl) ⟨836619, by rfl⟩ : syracuseStep 2230985 = 1673239) B1673239
theorem B2231099 : Blo 1486063 2231099 := bstep (se 1 (by rfl) ⟨1673324, by rfl⟩ : syracuseStep 2231099 = 3346649) B3346649
theorem B7531379 : Blo 1486063 7531379 := bstep (se 1 (by rfl) ⟨5648534, by rfl⟩ : syracuseStep 7531379 = 11297069) B11297069
theorem B2231159 : Blo 1486063 2231159 := bstep (se 1 (by rfl) ⟨1673369, by rfl⟩ : syracuseStep 2231159 = 3346739) B3346739
theorem B2231183 : Blo 1486063 2231183 := bstep (se 1 (by rfl) ⟨1673387, by rfl⟩ : syracuseStep 2231183 = 3346775) B3346775
theorem B3345299 : Blo 1486063 3345299 := bstep (se 1 (by rfl) ⟨2508974, by rfl⟩ : syracuseStep 3345299 = 5017949) B5017949
theorem B2231225 : Blo 1486063 2231225 := bstep (se 2 (by rfl) ⟨836709, by rfl⟩ : syracuseStep 2231225 = 1673419) B1673419
theorem B3345353 : Blo 1486063 3345353 := bstep (se 2 (by rfl) ⟨1254507, by rfl⟩ : syracuseStep 3345353 = 2509015) B2509015
theorem B2231303 : Blo 1486063 2231303 := bstep (se 1 (by rfl) ⟨1673477, by rfl⟩ : syracuseStep 2231303 = 3346955) B3346955
theorem B2231339 : Blo 1486063 2231339 := bstep (se 1 (by rfl) ⟨1673504, by rfl⟩ : syracuseStep 2231339 = 3347009) B3347009
theorem B5647427 : Blo 1486063 5647427 := bstep (se 1 (by rfl) ⟨4235570, by rfl⟩ : syracuseStep 5647427 = 8471141) B8471141
theorem B2231369 : Blo 1486063 2231369 := bstep (se 2 (by rfl) ⟨836763, by rfl⟩ : syracuseStep 2231369 = 1673527) B1673527
theorem B2231483 : Blo 1486063 2231483 := bstep (se 1 (by rfl) ⟨1673612, by rfl⟩ : syracuseStep 2231483 = 3347225) B3347225
theorem B2821321 : Blo 1486063 2821321 := bstep (se 2 (by rfl) ⟨1057995, by rfl⟩ : syracuseStep 2821321 = 2115991) B2115991
theorem B2231543 : Blo 1486063 2231543 := bstep (se 1 (by rfl) ⟨1673657, by rfl⟩ : syracuseStep 2231543 = 3347315) B3347315
theorem B1486087 : Blo 1486063 1486087 := bstep (se 1 (by rfl) ⟨1114565, by rfl⟩ : syracuseStep 1486087 = 2229131) B2229131
theorem B1486095 : Blo 1486063 1486095 := bstep (se 1 (by rfl) ⟨1114571, by rfl⟩ : syracuseStep 1486095 = 2229143) B2229143
theorem B2510095 : Blo 1486063 2510095 := bstep (se 1 (by rfl) ⟨1882571, by rfl⟩ : syracuseStep 2510095 = 3765143) B3765143
theorem B2231567 : Blo 1486063 2231567 := bstep (se 1 (by rfl) ⟨1673675, by rfl⟩ : syracuseStep 2231567 = 3347351) B3347351
theorem B2231609 : Blo 1486063 2231609 := bstep (se 2 (by rfl) ⟨836853, by rfl⟩ : syracuseStep 2231609 = 1673707) B1673707
theorem B1486139 : Blo 1486063 1486139 := bstep (se 1 (by rfl) ⟨1114604, by rfl⟩ : syracuseStep 1486139 = 2229209) B2229209
theorem B3763543 : Blo 1486063 3763543 := bstep (se 1 (by rfl) ⟨2822657, by rfl⟩ : syracuseStep 3763543 = 5645315) B5645315
theorem B7531865 : Blo 1486063 7531865 := bstep (se 2 (by rfl) ⟨2824449, by rfl⟩ : syracuseStep 7531865 = 5648899) B5648899
theorem B1486215 : Blo 1486063 1486215 := bstep (se 1 (by rfl) ⟨1114661, by rfl⟩ : syracuseStep 1486215 = 2229323) B2229323
theorem B19049863 : Blo 1486063 19049863 := bstep (se 1 (by rfl) ⟨14287397, by rfl⟩ : syracuseStep 19049863 = 28574795) B28574795
theorem B2231687 : Blo 1486063 2231687 := bstep (se 1 (by rfl) ⟨1673765, by rfl⟩ : syracuseStep 2231687 = 3347531) B3347531
theorem B1486223 : Blo 1486063 1486223 := bstep (se 1 (by rfl) ⟨1114667, by rfl⟩ : syracuseStep 1486223 = 2229335) B2229335
theorem B2231723 : Blo 1486063 2231723 := bstep (se 1 (by rfl) ⟨1673792, by rfl⟩ : syracuseStep 2231723 = 3347585) B3347585
theorem B1486267 : Blo 1486063 1486267 := bstep (se 1 (by rfl) ⟨1114700, by rfl⟩ : syracuseStep 1486267 = 2229401) B2229401
theorem B2231753 : Blo 1486063 2231753 := bstep (se 2 (by rfl) ⟨836907, by rfl⟩ : syracuseStep 2231753 = 1673815) B1673815
theorem B1486343 : Blo 1486063 1486343 := bstep (se 1 (by rfl) ⟨1114757, by rfl⟩ : syracuseStep 1486343 = 2229515) B2229515
theorem B1486351 : Blo 1486063 1486351 := bstep (se 1 (by rfl) ⟨1114763, by rfl⟩ : syracuseStep 1486351 = 2229527) B2229527
theorem B1486395 : Blo 1486063 1486395 := bstep (se 1 (by rfl) ⟨1114796, by rfl⟩ : syracuseStep 1486395 = 2229593) B2229593
theorem B2231867 : Blo 1486063 2231867 := bstep (se 1 (by rfl) ⟨1673900, by rfl⟩ : syracuseStep 2231867 = 3347801) B3347801
theorem B6352451 : Blo 1486063 6352451 := bstep (se 1 (by rfl) ⟨4764338, by rfl⟩ : syracuseStep 6352451 = 9528677) B9528677
theorem B7523927 : Blo 1486063 7523927 := bstep (se 1 (by rfl) ⟨5642945, by rfl⟩ : syracuseStep 7523927 = 11285891) B11285891
theorem B2231927 : Blo 1486063 2231927 := bstep (se 1 (by rfl) ⟨1673945, by rfl⟩ : syracuseStep 2231927 = 3347891) B3347891
theorem B1486471 : Blo 1486063 1486471 := bstep (se 1 (by rfl) ⟨1114853, by rfl⟩ : syracuseStep 1486471 = 2229707) B2229707
theorem B3763847 : Blo 1486063 3763847 := bstep (se 1 (by rfl) ⟨2822885, by rfl⟩ : syracuseStep 3763847 = 5645771) B5645771
theorem B3346055 : Blo 1486063 3346055 := bstep (se 1 (by rfl) ⟨2509541, by rfl⟩ : syracuseStep 3346055 = 5019083) B5019083
theorem B1486479 : Blo 1486063 1486479 := bstep (se 1 (by rfl) ⟨1114859, by rfl⟩ : syracuseStep 1486479 = 2229719) B2229719
theorem B2231951 : Blo 1486063 2231951 := bstep (se 1 (by rfl) ⟨1673963, by rfl⟩ : syracuseStep 2231951 = 3347927) B3347927
theorem B2010809 : Blo 1486063 2010809 := bstep (se 2 (by rfl) ⟨754053, by rfl⟩ : syracuseStep 2010809 = 1508107) B1508107
theorem B2231993 : Blo 1486063 2231993 := bstep (se 2 (by rfl) ⟨836997, by rfl⟩ : syracuseStep 2231993 = 1673995) B1673995
theorem B1486523 : Blo 1486063 1486523 := bstep (se 1 (by rfl) ⟨1114892, by rfl⟩ : syracuseStep 1486523 = 2229785) B2229785
theorem B8580809 : Blo 1486063 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B1486599 : Blo 1486063 1486599 := bstep (se 1 (by rfl) ⟨1114949, by rfl⟩ : syracuseStep 1486599 = 2229899) B2229899
theorem B2232071 : Blo 1486063 2232071 := bstep (se 1 (by rfl) ⟨1674053, by rfl⟩ : syracuseStep 2232071 = 3348107) B3348107
theorem B1486607 : Blo 1486063 1486607 := bstep (se 1 (by rfl) ⟨1114955, by rfl⟩ : syracuseStep 1486607 = 2229911) B2229911
theorem B3763979 : Blo 1486063 3763979 := bstep (se 1 (by rfl) ⟨2822984, by rfl⟩ : syracuseStep 3763979 = 5645969) B5645969
theorem B2510635 : Blo 1486063 2510635 := bstep (se 1 (by rfl) ⟨1882976, by rfl⟩ : syracuseStep 2510635 = 3765953) B3765953
theorem B15257393 : Blo 1486063 15257393 := bstep (se 2 (by rfl) ⟨5721522, by rfl⟩ : syracuseStep 15257393 = 11443045) B11443045
theorem B1486651 : Blo 1486063 1486651 := bstep (se 1 (by rfl) ⟨1114988, by rfl⟩ : syracuseStep 1486651 = 2229977) B2229977
theorem B3346235 : Blo 1486063 3346235 := bstep (se 1 (by rfl) ⟨2509676, by rfl⟩ : syracuseStep 3346235 = 5019353) B5019353
theorem B2117449 : Blo 1486063 2117449 := bstep (se 2 (by rfl) ⟨794043, by rfl⟩ : syracuseStep 2117449 = 1588087) B1588087
theorem B2387831 : Blo 1486063 2387831 := bstep (se 1 (by rfl) ⟨1790873, by rfl⟩ : syracuseStep 2387831 = 3581747) B3581747
theorem B1486727 : Blo 1486063 1486727 := bstep (se 1 (by rfl) ⟨1115045, by rfl⟩ : syracuseStep 1486727 = 2230091) B2230091
theorem B1486735 : Blo 1486063 1486735 := bstep (se 1 (by rfl) ⟨1115051, by rfl⟩ : syracuseStep 1486735 = 2230103) B2230103
theorem B2822035 : Blo 1486063 2822035 := bstep (se 1 (by rfl) ⟨2116526, by rfl⟩ : syracuseStep 2822035 = 4233053) B4233053
theorem B3174329 : Blo 1486063 3174329 := bstep (se 2 (by rfl) ⟨1190373, by rfl⟩ : syracuseStep 3174329 = 2380747) B2380747
theorem B6352825 : Blo 1486063 6352825 := bstep (se 2 (by rfl) ⟨2382309, by rfl⟩ : syracuseStep 6352825 = 4764619) B4764619
theorem B1486779 : Blo 1486063 1486779 := bstep (se 1 (by rfl) ⟨1115084, by rfl⟩ : syracuseStep 1486779 = 2230169) B2230169
theorem B3346361 : Blo 1486063 3346361 := bstep (se 2 (by rfl) ⟨1254885, by rfl⟩ : syracuseStep 3346361 = 2509771) B2509771
theorem B2510777 : Blo 1486063 2510777 := bstep (se 2 (by rfl) ⟨941541, by rfl⟩ : syracuseStep 2510777 = 1883083) B1883083
theorem B1486855 : Blo 1486063 1486855 := bstep (se 1 (by rfl) ⟨1115141, by rfl⟩ : syracuseStep 1486855 = 2230283) B2230283
theorem B1486863 : Blo 1486063 1486863 := bstep (se 1 (by rfl) ⟨1115147, by rfl⟩ : syracuseStep 1486863 = 2230295) B2230295
theorem B11292695 : Blo 1486063 11292695 := bstep (se 1 (by rfl) ⟨8469521, by rfl⟩ : syracuseStep 11292695 = 16939043) B16939043
theorem B5648413 : Blo 1486063 5648413 := bstep (se 3 (by rfl) ⟨1059077, by rfl⟩ : syracuseStep 5648413 = 2118155) B2118155
theorem B9048107 : Blo 1486063 9048107 := bstep (se 1 (by rfl) ⟨6786080, by rfl⟩ : syracuseStep 9048107 = 13572161) B13572161
theorem B1486907 : Blo 1486063 1486907 := bstep (se 1 (by rfl) ⟨1115180, by rfl⟩ : syracuseStep 1486907 = 2230361) B2230361
theorem B7524413 : Blo 1486063 7524413 := bstep (se 3 (by rfl) ⟨1410827, by rfl⟩ : syracuseStep 7524413 = 2821655) B2821655
theorem B1486983 : Blo 1486063 1486983 := bstep (se 1 (by rfl) ⟨1115237, by rfl⟩ : syracuseStep 1486983 = 2230475) B2230475
theorem B1486991 : Blo 1486063 1486991 := bstep (se 1 (by rfl) ⟨1115243, by rfl⟩ : syracuseStep 1486991 = 2230487) B2230487
theorem B1487035 : Blo 1486063 1487035 := bstep (se 1 (by rfl) ⟨1115276, by rfl⟩ : syracuseStep 1487035 = 2230553) B2230553
theorem B1487111 : Blo 1486063 1487111 := bstep (se 1 (by rfl) ⟨1115333, by rfl⟩ : syracuseStep 1487111 = 2230667) B2230667
theorem B1487119 : Blo 1486063 1487119 := bstep (se 1 (by rfl) ⟨1115339, by rfl⟩ : syracuseStep 1487119 = 2230679) B2230679
theorem B3764495 : Blo 1486063 3764495 := bstep (se 1 (by rfl) ⟨2823371, by rfl⟩ : syracuseStep 3764495 = 5646743) B5646743
theorem B6353167 : Blo 1486063 6353167 := bstep (se 1 (by rfl) ⟨4764875, by rfl⟩ : syracuseStep 6353167 = 9529751) B9529751
theorem B3346703 : Blo 1486063 3346703 := bstep (se 1 (by rfl) ⟨2510027, by rfl⟩ : syracuseStep 3346703 = 5020055) B5020055
theorem B3346721 : Blo 1486063 3346721 := bstep (se 2 (by rfl) ⟨1255020, by rfl⟩ : syracuseStep 3346721 = 2510041) B2510041
theorem B1487163 : Blo 1486063 1487163 := bstep (se 1 (by rfl) ⟨1115372, by rfl⟩ : syracuseStep 1487163 = 2230745) B2230745
theorem B7147835 : Blo 1486063 7147835 := bstep (se 1 (by rfl) ⟨5360876, by rfl⟩ : syracuseStep 7147835 = 10721753) B10721753
theorem B108532061 : Blo 1486063 108532061 := bstep (se 3 (by rfl) ⟨20349761, by rfl⟩ : syracuseStep 108532061 = 40699523) B40699523
theorem B17174915 : Blo 1486063 17174915 := bstep (se 1 (by rfl) ⟨12881186, by rfl⟩ : syracuseStep 17174915 = 25762373) B25762373
theorem B1487239 : Blo 1486063 1487239 := bstep (se 1 (by rfl) ⟨1115429, by rfl⟩ : syracuseStep 1487239 = 2230859) B2230859
theorem B1487247 : Blo 1486063 1487247 := bstep (se 1 (by rfl) ⟨1115435, by rfl⟩ : syracuseStep 1487247 = 2230871) B2230871
theorem B9523601 : Blo 1486063 9523601 := bstep (se 2 (by rfl) ⟨3571350, by rfl⟩ : syracuseStep 9523601 = 7142701) B7142701
theorem B5018003 : Blo 1486063 5018003 := bstep (se 1 (by rfl) ⟨3763502, by rfl⟩ : syracuseStep 5018003 = 7527005) B7527005
theorem B3764627 : Blo 1486063 3764627 := bstep (se 1 (by rfl) ⟨2823470, by rfl⟩ : syracuseStep 3764627 = 5646941) B5646941
theorem B1487291 : Blo 1486063 1487291 := bstep (se 1 (by rfl) ⟨1115468, by rfl⟩ : syracuseStep 1487291 = 2230937) B2230937
theorem B6025681 : Blo 1486063 6025681 := bstep (se 2 (by rfl) ⟨2259630, by rfl⟩ : syracuseStep 6025681 = 4519261) B4519261
theorem B1487367 : Blo 1486063 1487367 := bstep (se 1 (by rfl) ⟨1115525, by rfl⟩ : syracuseStep 1487367 = 2231051) B2231051
theorem B1487375 : Blo 1486063 1487375 := bstep (se 1 (by rfl) ⟨1115531, by rfl⟩ : syracuseStep 1487375 = 2231063) B2231063
theorem B3813947 : Blo 1486063 3813947 := bstep (se 1 (by rfl) ⟨2860460, by rfl⟩ : syracuseStep 3813947 = 5720921) B5720921
theorem B1487419 : Blo 1486063 1487419 := bstep (se 1 (by rfl) ⟨1115564, by rfl⟩ : syracuseStep 1487419 = 2231129) B2231129
theorem B6787651 : Blo 1486063 6787651 := bstep (se 1 (by rfl) ⟨5090738, by rfl⟩ : syracuseStep 6787651 = 10181477) B10181477
theorem B3347063 : Blo 1486063 3347063 := bstep (se 1 (by rfl) ⟨2510297, by rfl⟩ : syracuseStep 3347063 = 5020595) B5020595
theorem B1487495 : Blo 1486063 1487495 := bstep (se 1 (by rfl) ⟨1115621, by rfl⟩ : syracuseStep 1487495 = 2231243) B2231243
theorem B1487503 : Blo 1486063 1487503 := bstep (se 1 (by rfl) ⟨1115627, by rfl⟩ : syracuseStep 1487503 = 2231255) B2231255
theorem B1487547 : Blo 1486063 1487547 := bstep (se 1 (by rfl) ⟨1115660, by rfl⟩ : syracuseStep 1487547 = 2231321) B2231321
theorem B18084545 : Blo 1486063 18084545 := bstep (se 2 (by rfl) ⟨6781704, by rfl⟩ : syracuseStep 18084545 = 13563409) B13563409
theorem B1487623 : Blo 1486063 1487623 := bstep (se 1 (by rfl) ⟨1115717, by rfl⟩ : syracuseStep 1487623 = 2231435) B2231435
theorem B1487631 : Blo 1486063 1487631 := bstep (se 1 (by rfl) ⟨1115723, by rfl⟩ : syracuseStep 1487631 = 2231447) B2231447
theorem B3347243 : Blo 1486063 3347243 := bstep (se 1 (by rfl) ⟨2510432, by rfl⟩ : syracuseStep 3347243 = 5020865) B5020865
theorem B1487675 : Blo 1486063 1487675 := bstep (se 1 (by rfl) ⟨1115756, by rfl⟩ : syracuseStep 1487675 = 2231513) B2231513
theorem B4232051 : Blo 1486063 4232051 := bstep (se 1 (by rfl) ⟨3174038, by rfl⟩ : syracuseStep 4232051 = 6348077) B6348077
theorem B1487751 : Blo 1486063 1487751 := bstep (se 1 (by rfl) ⟨1115813, by rfl⟩ : syracuseStep 1487751 = 2231627) B2231627
theorem B1487759 : Blo 1486063 1487759 := bstep (se 1 (by rfl) ⟨1115819, by rfl⟩ : syracuseStep 1487759 = 2231639) B2231639
theorem B9532313 : Blo 1486063 9532313 := bstep (se 2 (by rfl) ⟨3574617, by rfl⟩ : syracuseStep 9532313 = 7149235) B7149235
theorem B8147897 : Blo 1486063 8147897 := bstep (se 2 (by rfl) ⟨3055461, by rfl⟩ : syracuseStep 8147897 = 6110923) B6110923
theorem B1487803 : Blo 1486063 1487803 := bstep (se 1 (by rfl) ⟨1115852, by rfl⟩ : syracuseStep 1487803 = 2231705) B2231705
theorem B2823113 : Blo 1486063 2823113 := bstep (se 2 (by rfl) ⟨1058667, by rfl⟩ : syracuseStep 2823113 = 2117335) B2117335
theorem B1487879 : Blo 1486063 1487879 := bstep (se 1 (by rfl) ⟨1115909, by rfl⟩ : syracuseStep 1487879 = 2231819) B2231819
theorem B1487887 : Blo 1486063 1487887 := bstep (se 1 (by rfl) ⟨1115915, by rfl⟩ : syracuseStep 1487887 = 2231831) B2231831
theorem B1487931 : Blo 1486063 1487931 := bstep (se 1 (by rfl) ⟨1115948, by rfl⟩ : syracuseStep 1487931 = 2231897) B2231897
theorem B8467517 : Blo 1486063 8467517 := bstep (se 3 (by rfl) ⟨1587659, by rfl⟩ : syracuseStep 8467517 = 3175319) B3175319
theorem B1488007 : Blo 1486063 1488007 := bstep (se 1 (by rfl) ⟨1116005, by rfl⟩ : syracuseStep 1488007 = 2232011) B2232011
theorem B1488015 : Blo 1486063 1488015 := bstep (se 1 (by rfl) ⟨1116011, by rfl⟩ : syracuseStep 1488015 = 2232023) B2232023
theorem B3347603 : Blo 1486063 3347603 := bstep (se 1 (by rfl) ⟨2510702, by rfl⟩ : syracuseStep 3347603 = 5021405) B5021405
theorem B1488059 : Blo 1486063 1488059 := bstep (se 1 (by rfl) ⟨1116044, by rfl⟩ : syracuseStep 1488059 = 2232089) B2232089
theorem B3347657 : Blo 1486063 3347657 := bstep (se 2 (by rfl) ⟨1255371, by rfl⟩ : syracuseStep 3347657 = 2510743) B2510743
theorem B5100833 : Blo 1486063 5100833 := bstep (se 2 (by rfl) ⟨1912812, by rfl⟩ : syracuseStep 5100833 = 3825625) B3825625
theorem B1881463 : Blo 1486063 1881463 := bstep (se 1 (by rfl) ⟨1411097, by rfl⟩ : syracuseStep 1881463 = 2822195) B2822195
theorem B9524627 : Blo 1486063 9524627 := bstep (se 1 (by rfl) ⟨7143470, by rfl⟩ : syracuseStep 9524627 = 14286941) B14286941
theorem B4765081 : Blo 1486063 4765081 := bstep (se 2 (by rfl) ⟨1786905, by rfl⟩ : syracuseStep 4765081 = 3573811) B3573811
theorem B3765761 : Blo 1486063 3765761 := bstep (se 2 (by rfl) ⟨1412160, by rfl⟩ : syracuseStep 3765761 = 2824321) B2824321
theorem B3175969 : Blo 1486063 3175969 := bstep (se 2 (by rfl) ⟨1190988, by rfl⟩ : syracuseStep 3175969 = 2381977) B2381977
theorem B16307891 : Blo 1486063 16307891 := bstep (se 1 (by rfl) ⟨12230918, by rfl⟩ : syracuseStep 16307891 = 24461837) B24461837
theorem B1881787 : Blo 1486063 1881787 := bstep (se 1 (by rfl) ⟨1411340, by rfl⟩ : syracuseStep 1881787 = 2822681) B2822681
theorem B8935105 : Blo 1486063 8935105 := bstep (se 2 (by rfl) ⟨3350664, by rfl⟩ : syracuseStep 8935105 = 6701329) B6701329
theorem B8468225 : Blo 1486063 8468225 := bstep (se 2 (by rfl) ⟨3175584, by rfl⟩ : syracuseStep 8468225 = 6351169) B6351169
theorem B5019407 : Blo 1486063 5019407 := bstep (se 1 (by rfl) ⟨3764555, by rfl⟩ : syracuseStep 5019407 = 7529111) B7529111
theorem B2823979 : Blo 1486063 2823979 := bstep (se 1 (by rfl) ⟨2117984, by rfl⟩ : syracuseStep 2823979 = 4235969) B4235969
theorem B7526195 : Blo 1486063 7526195 := bstep (se 1 (by rfl) ⟨5644646, by rfl⟩ : syracuseStep 7526195 = 11289293) B11289293
theorem B4233019 : Blo 1486063 4233019 := bstep (se 1 (by rfl) ⟨3174764, by rfl⟩ : syracuseStep 4233019 = 6349529) B6349529
theorem B2824055 : Blo 1486063 2824055 := bstep (se 1 (by rfl) ⟨2118041, by rfl⟩ : syracuseStep 2824055 = 4236083) B4236083
theorem B3766135 : Blo 1486063 3766135 := bstep (se 1 (by rfl) ⟨2824601, by rfl⟩ : syracuseStep 3766135 = 5649203) B5649203
theorem B2291657 : Blo 1486063 2291657 := bstep (se 2 (by rfl) ⟨859371, by rfl⟩ : syracuseStep 2291657 = 1718743) B1718743
theorem B5019677 : Blo 1486063 5019677 := bstep (se 3 (by rfl) ⟨941189, by rfl⟩ : syracuseStep 5019677 = 1882379) B1882379
theorem B7526519 : Blo 1486063 7526519 := bstep (se 1 (by rfl) ⟨5644889, by rfl⟩ : syracuseStep 7526519 = 11289779) B11289779
theorem B3176567 : Blo 1486063 3176567 := bstep (se 1 (by rfl) ⟨2382425, by rfl⟩ : syracuseStep 3176567 = 4764851) B4764851
theorem B1587335 : Blo 1486063 1587335 := bstep (se 1 (by rfl) ⟨1190501, by rfl⟩ : syracuseStep 1587335 = 2381003) B2381003
theorem B7239917 : Blo 1486063 7239917 := bstep (se 3 (by rfl) ⟨1357484, by rfl⟩ : syracuseStep 7239917 = 2714969) B2714969
theorem B4348189 : Blo 1486063 4348189 := bstep (se 3 (by rfl) ⟨815285, by rfl⟩ : syracuseStep 4348189 = 1630571) B1630571
theorem B3766571 : Blo 1486063 3766571 := bstep (se 1 (by rfl) ⟨2824928, by rfl⟩ : syracuseStep 3766571 = 5649857) B5649857
theorem B7248179 : Blo 1486063 7248179 := bstep (se 1 (by rfl) ⟨5436134, by rfl⟩ : syracuseStep 7248179 = 10872269) B10872269
theorem B2718011 : Blo 1486063 2718011 := bstep (se 1 (by rfl) ⟨2038508, by rfl⟩ : syracuseStep 2718011 = 4077017) B4077017
theorem B12704147 : Blo 1486063 12704147 := bstep (se 1 (by rfl) ⟨9528110, by rfl⟩ : syracuseStep 12704147 = 19056221) B19056221
theorem B5355929 : Blo 1486063 5355929 := bstep (se 2 (by rfl) ⟨2008473, by rfl⟩ : syracuseStep 5355929 = 4016947) B4016947
theorem B1718843 : Blo 1486063 1718843 := bstep (se 1 (by rfl) ⟨1289132, by rfl⟩ : syracuseStep 1718843 = 2578265) B2578265
theorem B6355543 : Blo 1486063 6355543 := bstep (se 1 (by rfl) ⟨4766657, by rfl⟩ : syracuseStep 6355543 = 9533315) B9533315
theorem B1882759 : Blo 1486063 1882759 := bstep (se 1 (by rfl) ⟨1412069, by rfl⟩ : syracuseStep 1882759 = 2824139) B2824139
theorem B4766465 : Blo 1486063 4766465 := bstep (se 2 (by rfl) ⟨1787424, by rfl⟩ : syracuseStep 4766465 = 3574849) B3574849
theorem B7150351 : Blo 1486063 7150351 := bstep (se 1 (by rfl) ⟨5362763, by rfl⟩ : syracuseStep 7150351 = 10725527) B10725527
theorem B5643067 : Blo 1486063 5643067 := bstep (se 1 (by rfl) ⟨4232300, by rfl⟩ : syracuseStep 5643067 = 8464601) B8464601
theorem B4234169 : Blo 1486063 4234169 := bstep (se 2 (by rfl) ⟨1587813, by rfl⟩ : syracuseStep 4234169 = 3175627) B3175627
theorem B1883179 : Blo 1486063 1883179 := bstep (se 1 (by rfl) ⟨1412384, by rfl⟩ : syracuseStep 1883179 = 2824769) B2824769
theorem B8043581 : Blo 1486063 8043581 := bstep (se 3 (by rfl) ⟨1508171, by rfl⟩ : syracuseStep 8043581 = 3016343) B3016343
theorem B7527491 : Blo 1486063 7527491 := bstep (se 1 (by rfl) ⟨5645618, by rfl⟩ : syracuseStep 7527491 = 11291237) B11291237
theorem B4234511 : Blo 1486063 4234511 := bstep (se 1 (by rfl) ⟨3175883, by rfl⟩ : syracuseStep 4234511 = 6351767) B6351767
theorem B5643553 : Blo 1486063 5643553 := bstep (se 2 (by rfl) ⟨2116332, by rfl⟩ : syracuseStep 5643553 = 4232665) B4232665
theorem B19045763 : Blo 1486063 19045763 := bstep (se 1 (by rfl) ⟨14284322, by rfl⟩ : syracuseStep 19045763 = 28568645) B28568645
theorem B7527815 : Blo 1486063 7527815 := bstep (se 1 (by rfl) ⟨5645861, by rfl⟩ : syracuseStep 7527815 = 11291723) B11291723
theorem B5021081 : Blo 1486063 5021081 := bstep (se 2 (by rfl) ⟨1882905, by rfl⟩ : syracuseStep 5021081 = 3765811) B3765811
theorem B6782525 : Blo 1486063 6782525 := bstep (se 3 (by rfl) ⟨1271723, by rfl⟩ : syracuseStep 6782525 = 2543447) B2543447
theorem B8822465 : Blo 1486063 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B11288321 : Blo 1486063 11288321 := bstep (se 2 (by rfl) ⟨4233120, by rfl⟩ : syracuseStep 11288321 = 8466241) B8466241
theorem B12058631 : Blo 1486063 12058631 := bstep (se 1 (by rfl) ⟨9043973, by rfl⟩ : syracuseStep 12058631 = 18087947) B18087947
theorem B7528463 : Blo 1486063 7528463 := bstep (se 1 (by rfl) ⟨5646347, by rfl⟩ : syracuseStep 7528463 = 11292695) B11292695
theorem B24444989 : Blo 1486063 24444989 := bstep (se 3 (by rfl) ⟨4583435, by rfl⟩ : syracuseStep 24444989 = 9166871) B9166871
theorem B6349067 : Blo 1486063 6349067 := bstep (se 1 (by rfl) ⟨4761800, by rfl⟩ : syracuseStep 6349067 = 9523601) B9523601
theorem B8470889 : Blo 1486063 8470889 := bstep (se 2 (by rfl) ⟨3176583, by rfl⟩ : syracuseStep 8470889 = 6353167) B6353167
theorem B5431931 : Blo 1486063 5431931 := bstep (se 1 (by rfl) ⟨4073948, by rfl⟩ : syracuseStep 5431931 = 8147897) B8147897
theorem B7144145 : Blo 1486063 7144145 := bstep (se 2 (by rfl) ⟨2679054, by rfl⟩ : syracuseStep 7144145 = 5358109) B5358109
theorem B5645011 : Blo 1486063 5645011 := bstep (se 1 (by rfl) ⟨4233758, by rfl⟩ : syracuseStep 5645011 = 8467517) B8467517
theorem B3400555 : Blo 1486063 3400555 := bstep (se 1 (by rfl) ⟨2550416, by rfl⟩ : syracuseStep 3400555 = 5100833) B5100833
theorem B2229167 : Blo 1486063 2229167 := bstep (se 1 (by rfl) ⟨1671875, by rfl⟩ : syracuseStep 2229167 = 3343751) B3343751
theorem B6349751 : Blo 1486063 6349751 := bstep (se 1 (by rfl) ⟨4762313, by rfl⟩ : syracuseStep 6349751 = 9524627) B9524627
theorem B137323525 : Blo 1486063 137323525 := bstep (se 4 (by rfl) ⟨12874080, by rfl⟩ : syracuseStep 137323525 = 25748161) B25748161
theorem B2229257 : Blo 1486063 2229257 := bstep (se 2 (by rfl) ⟨835971, by rfl⟩ : syracuseStep 2229257 = 1671943) B1671943
theorem B2229287 : Blo 1486063 2229287 := bstep (se 1 (by rfl) ⟨1671965, by rfl⟩ : syracuseStep 2229287 = 3343931) B3343931
theorem B1672231 : Blo 1486063 1672231 := bstep (se 1 (by rfl) ⟨1254173, by rfl⟩ : syracuseStep 1672231 = 2508347) B2508347
theorem B22889591 : Blo 1486063 22889591 := bstep (se 1 (by rfl) ⟨17167193, by rfl⟩ : syracuseStep 22889591 = 34334387) B34334387
theorem B10871927 : Blo 1486063 10871927 := bstep (se 1 (by rfl) ⟨8153945, by rfl⟩ : syracuseStep 10871927 = 16307891) B16307891
theorem B2229371 : Blo 1486063 2229371 := bstep (se 1 (by rfl) ⟨1672028, by rfl⟩ : syracuseStep 2229371 = 3344057) B3344057
theorem B5645483 : Blo 1486063 5645483 := bstep (se 1 (by rfl) ⟨4234112, by rfl⟩ : syracuseStep 5645483 = 8468225) B8468225
theorem B25470197 : Blo 1486063 25470197 := bstep (se 5 (by rfl) ⟨1193915, by rfl⟩ : syracuseStep 25470197 = 2387831) B2387831
theorem B2508023 : Blo 1486063 2508023 := bstep (se 1 (by rfl) ⟨1881017, by rfl⟩ : syracuseStep 2508023 = 3762035) B3762035
theorem B2229497 : Blo 1486063 2229497 := bstep (se 2 (by rfl) ⟨836061, by rfl⟩ : syracuseStep 2229497 = 1672123) B1672123
theorem B2229599 : Blo 1486063 2229599 := bstep (se 1 (by rfl) ⟨1672199, by rfl⟩ : syracuseStep 2229599 = 3344399) B3344399
theorem B2229611 : Blo 1486063 2229611 := bstep (se 1 (by rfl) ⟨1672208, by rfl⟩ : syracuseStep 2229611 = 3344417) B3344417
theorem B4826611 : Blo 1486063 4826611 := bstep (se 1 (by rfl) ⟨3619958, by rfl⟩ : syracuseStep 4826611 = 7239917) B7239917
theorem B1812007 : Blo 1486063 1812007 := bstep (se 1 (by rfl) ⟨1359005, by rfl⟩ : syracuseStep 1812007 = 2718011) B2718011
theorem B2508367 : Blo 1486063 2508367 := bstep (se 1 (by rfl) ⟨1881275, by rfl⟩ : syracuseStep 2508367 = 3762551) B3762551
theorem B2229839 : Blo 1486063 2229839 := bstep (se 1 (by rfl) ⟨1672379, by rfl⟩ : syracuseStep 2229839 = 3344759) B3344759
theorem B3761761 : Blo 1486063 3761761 := bstep (se 2 (by rfl) ⟨1410660, by rfl⟩ : syracuseStep 3761761 = 2821321) B2821321
theorem B2229959 : Blo 1486063 2229959 := bstep (se 1 (by rfl) ⟨1672469, by rfl⟩ : syracuseStep 2229959 = 3344939) B3344939
theorem B3344201 : Blo 1486063 3344201 := bstep (se 2 (by rfl) ⟨1254075, by rfl⟩ : syracuseStep 3344201 = 2508151) B2508151
theorem B2508617 : Blo 1486063 2508617 := bstep (se 2 (by rfl) ⟨940731, by rfl⟩ : syracuseStep 2508617 = 1881463) B1881463
theorem B2230121 : Blo 1486063 2230121 := bstep (se 2 (by rfl) ⟨836295, by rfl⟩ : syracuseStep 2230121 = 1672591) B1672591
theorem B2230199 : Blo 1486063 2230199 := bstep (se 1 (by rfl) ⟨1672649, by rfl⟩ : syracuseStep 2230199 = 3345299) B3345299
theorem B2230235 : Blo 1486063 2230235 := bstep (se 1 (by rfl) ⟨1672676, by rfl⟩ : syracuseStep 2230235 = 3345353) B3345353
theorem B3868729 : Blo 1486063 3868729 := bstep (se 2 (by rfl) ⟨1450773, by rfl⟩ : syracuseStep 3868729 = 2901547) B2901547
theorem B2509049 : Blo 1486063 2509049 := bstep (se 2 (by rfl) ⟨940893, by rfl⟩ : syracuseStep 2509049 = 1881787) B1881787
theorem B11913473 : Blo 1486063 11913473 := bstep (se 2 (by rfl) ⟨4467552, by rfl⟩ : syracuseStep 11913473 = 8935105) B8935105
theorem B5015951 : Blo 1486063 5015951 := bstep (se 1 (by rfl) ⟨3761963, by rfl⟩ : syracuseStep 5015951 = 7523927) B7523927
theorem B2509231 : Blo 1486063 2509231 := bstep (se 1 (by rfl) ⟨1881923, by rfl⟩ : syracuseStep 2509231 = 3763847) B3763847
theorem B2230703 : Blo 1486063 2230703 := bstep (se 1 (by rfl) ⟨1673027, by rfl⟩ : syracuseStep 2230703 = 3346055) B3346055
theorem B5720539 : Blo 1486063 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B2509319 : Blo 1486063 2509319 := bstep (se 1 (by rfl) ⟨1881989, by rfl⟩ : syracuseStep 2509319 = 3763979) B3763979
theorem B2230793 : Blo 1486063 2230793 := bstep (se 2 (by rfl) ⟨836547, by rfl⟩ : syracuseStep 2230793 = 1673095) B1673095
theorem B3762713 : Blo 1486063 3762713 := bstep (se 2 (by rfl) ⟨1411017, by rfl⟩ : syracuseStep 3762713 = 2822035) B2822035
theorem B2230823 : Blo 1486063 2230823 := bstep (se 1 (by rfl) ⟨1673117, by rfl⟩ : syracuseStep 2230823 = 3346235) B3346235
theorem B3344993 : Blo 1486063 3344993 := bstep (se 2 (by rfl) ⟨1254372, by rfl⟩ : syracuseStep 3344993 = 2508745) B2508745
theorem B2116219 : Blo 1486063 2116219 := bstep (se 1 (by rfl) ⟨1587164, by rfl⟩ : syracuseStep 2116219 = 3174329) B3174329
theorem B2230907 : Blo 1486063 2230907 := bstep (se 1 (by rfl) ⟨1673180, by rfl⟩ : syracuseStep 2230907 = 3346361) B3346361
theorem B1673851 : Blo 1486063 1673851 := bstep (se 1 (by rfl) ⟨1255388, by rfl⟩ : syracuseStep 1673851 = 2510777) B2510777
theorem B6032071 : Blo 1486063 6032071 := bstep (se 1 (by rfl) ⟨4524053, by rfl⟩ : syracuseStep 6032071 = 9048107) B9048107
theorem B7531217 : Blo 1486063 7531217 := bstep (se 2 (by rfl) ⟨2824206, by rfl⟩ : syracuseStep 7531217 = 5648413) B5648413
theorem B5016275 : Blo 1486063 5016275 := bstep (se 1 (by rfl) ⟨3762206, by rfl⟩ : syracuseStep 5016275 = 7524413) B7524413
theorem B2231033 : Blo 1486063 2231033 := bstep (se 2 (by rfl) ⟨836637, by rfl⟩ : syracuseStep 2231033 = 1673275) B1673275
theorem B21449549 : Blo 1486063 21449549 := bstep (se 3 (by rfl) ⟨4021790, by rfl⟩ : syracuseStep 21449549 = 8043581) B8043581
theorem B2509663 : Blo 1486063 2509663 := bstep (se 1 (by rfl) ⟨1882247, by rfl⟩ : syracuseStep 2509663 = 3764495) B3764495
theorem B2231135 : Blo 1486063 2231135 := bstep (se 1 (by rfl) ⟨1673351, by rfl⟩ : syracuseStep 2231135 = 3346703) B3346703
theorem B2231147 : Blo 1486063 2231147 := bstep (se 1 (by rfl) ⟨1673360, by rfl⟩ : syracuseStep 2231147 = 3346721) B3346721
theorem B72354707 : Blo 1486063 72354707 := bstep (se 1 (by rfl) ⟨54266030, by rfl⟩ : syracuseStep 72354707 = 108532061) B108532061
theorem B3345335 : Blo 1486063 3345335 := bstep (se 1 (by rfl) ⟨2509001, by rfl⟩ : syracuseStep 3345335 = 5018003) B5018003
theorem B2509751 : Blo 1486063 2509751 := bstep (se 1 (by rfl) ⟨1882313, by rfl⟩ : syracuseStep 2509751 = 3764627) B3764627
theorem B11447261 : Blo 1486063 11447261 := bstep (se 3 (by rfl) ⟨2146361, by rfl⟩ : syracuseStep 11447261 = 4292723) B4292723
theorem B3763219 : Blo 1486063 3763219 := bstep (se 1 (by rfl) ⟨2822414, by rfl⟩ : syracuseStep 3763219 = 5644829) B5644829
theorem B2542631 : Blo 1486063 2542631 := bstep (se 1 (by rfl) ⟨1906973, by rfl⟩ : syracuseStep 2542631 = 3813947) B3813947
theorem B2231375 : Blo 1486063 2231375 := bstep (se 1 (by rfl) ⟨1673531, by rfl⟩ : syracuseStep 2231375 = 3347063) B3347063
theorem B5647441 : Blo 1486063 5647441 := bstep (se 2 (by rfl) ⟨2117790, by rfl⟩ : syracuseStep 5647441 = 4235581) B4235581
theorem B23506037 : Blo 1486063 23506037 := bstep (se 5 (by rfl) ⟨1101845, by rfl⟩ : syracuseStep 23506037 = 2203691) B2203691
theorem B2231495 : Blo 1486063 2231495 := bstep (se 1 (by rfl) ⟨1673621, by rfl⟩ : syracuseStep 2231495 = 3347243) B3347243
theorem B2821367 : Blo 1486063 2821367 := bstep (se 1 (by rfl) ⟨2116025, by rfl⟩ : syracuseStep 2821367 = 4232051) B4232051
theorem B1486119 : Blo 1486063 1486119 := bstep (se 1 (by rfl) ⟨1114589, by rfl⟩ : syracuseStep 1486119 = 2229179) B2229179
theorem B1486159 : Blo 1486063 1486159 := bstep (se 1 (by rfl) ⟨1114619, by rfl⟩ : syracuseStep 1486159 = 2229239) B2229239
theorem B1486175 : Blo 1486063 1486175 := bstep (se 1 (by rfl) ⟨1114631, by rfl⟩ : syracuseStep 1486175 = 2229263) B2229263
theorem B2010463 : Blo 1486063 2010463 := bstep (se 1 (by rfl) ⟨1507847, by rfl⟩ : syracuseStep 2010463 = 3015695) B3015695
theorem B2231657 : Blo 1486063 2231657 := bstep (se 2 (by rfl) ⟨836871, by rfl⟩ : syracuseStep 2231657 = 1673743) B1673743
theorem B1486203 : Blo 1486063 1486203 := bstep (se 1 (by rfl) ⟨1114652, by rfl⟩ : syracuseStep 1486203 = 2229305) B2229305
theorem B5647745 : Blo 1486063 5647745 := bstep (se 2 (by rfl) ⟨2117904, by rfl⟩ : syracuseStep 5647745 = 4235809) B4235809
theorem B1486255 : Blo 1486063 1486255 := bstep (se 1 (by rfl) ⟨1114691, by rfl⟩ : syracuseStep 1486255 = 2229383) B2229383
theorem B2231735 : Blo 1486063 2231735 := bstep (se 1 (by rfl) ⟨1673801, by rfl⟩ : syracuseStep 2231735 = 3347603) B3347603
theorem B1486279 : Blo 1486063 1486279 := bstep (se 1 (by rfl) ⟨1114709, by rfl⟩ : syracuseStep 1486279 = 2229419) B2229419
theorem B4763081 : Blo 1486063 4763081 := bstep (se 2 (by rfl) ⟨1786155, by rfl⟩ : syracuseStep 4763081 = 3572311) B3572311
theorem B8474057 : Blo 1486063 8474057 := bstep (se 2 (by rfl) ⟨3177771, by rfl⟩ : syracuseStep 8474057 = 6355543) B6355543
theorem B1486299 : Blo 1486063 1486299 := bstep (se 1 (by rfl) ⟨1114724, by rfl⟩ : syracuseStep 1486299 = 2229449) B2229449
theorem B2231771 : Blo 1486063 2231771 := bstep (se 1 (by rfl) ⟨1673828, by rfl⟩ : syracuseStep 2231771 = 3347657) B3347657
theorem B3345929 : Blo 1486063 3345929 := bstep (se 2 (by rfl) ⟨1254723, by rfl⟩ : syracuseStep 3345929 = 2509447) B2509447
theorem B2510345 : Blo 1486063 2510345 := bstep (se 2 (by rfl) ⟨941379, by rfl⟩ : syracuseStep 2510345 = 1882759) B1882759
theorem B1486375 : Blo 1486063 1486375 := bstep (se 1 (by rfl) ⟨1114781, by rfl⟩ : syracuseStep 1486375 = 2229563) B2229563
theorem B1486415 : Blo 1486063 1486415 := bstep (se 1 (by rfl) ⟨1114811, by rfl⟩ : syracuseStep 1486415 = 2229623) B2229623
theorem B1486431 : Blo 1486063 1486431 := bstep (se 1 (by rfl) ⟨1114823, by rfl⟩ : syracuseStep 1486431 = 2229647) B2229647
theorem B1486459 : Blo 1486063 1486459 := bstep (se 1 (by rfl) ⟨1114844, by rfl⟩ : syracuseStep 1486459 = 2229689) B2229689
theorem B8466059 : Blo 1486063 8466059 := bstep (se 1 (by rfl) ⟨6349544, by rfl⟩ : syracuseStep 8466059 = 12699089) B12699089
theorem B2510507 : Blo 1486063 2510507 := bstep (se 1 (by rfl) ⟨1882880, by rfl⟩ : syracuseStep 2510507 = 3765761) B3765761
theorem B1486511 : Blo 1486063 1486511 := bstep (se 1 (by rfl) ⟨1114883, by rfl⟩ : syracuseStep 1486511 = 2229767) B2229767
theorem B1486535 : Blo 1486063 1486535 := bstep (se 1 (by rfl) ⟨1114901, by rfl⟩ : syracuseStep 1486535 = 2229803) B2229803
theorem B1486555 : Blo 1486063 1486555 := bstep (se 1 (by rfl) ⟨1114916, by rfl⟩ : syracuseStep 1486555 = 2229833) B2229833
theorem B14282477 : Blo 1486063 14282477 := bstep (se 3 (by rfl) ⟨2677964, by rfl⟩ : syracuseStep 14282477 = 5355929) B5355929
theorem B7524089 : Blo 1486063 7524089 := bstep (se 2 (by rfl) ⟨2821533, by rfl⟩ : syracuseStep 7524089 = 5643067) B5643067
theorem B1486631 : Blo 1486063 1486631 := bstep (se 1 (by rfl) ⟨1114973, by rfl⟩ : syracuseStep 1486631 = 2229947) B2229947
theorem B5648201 : Blo 1486063 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B1486671 : Blo 1486063 1486671 := bstep (se 1 (by rfl) ⟨1115003, by rfl⟩ : syracuseStep 1486671 = 2230007) B2230007
theorem B1486687 : Blo 1486063 1486687 := bstep (se 1 (by rfl) ⟨1115015, by rfl⟩ : syracuseStep 1486687 = 2230031) B2230031
theorem B3346271 : Blo 1486063 3346271 := bstep (se 1 (by rfl) ⟨2509703, by rfl⟩ : syracuseStep 3346271 = 5019407) B5019407
theorem B5017463 : Blo 1486063 5017463 := bstep (se 1 (by rfl) ⟨3763097, by rfl⟩ : syracuseStep 5017463 = 7526195) B7526195
theorem B1486715 : Blo 1486063 1486715 := bstep (se 1 (by rfl) ⟨1115036, by rfl⟩ : syracuseStep 1486715 = 2230073) B2230073
theorem B1486767 : Blo 1486063 1486767 := bstep (se 1 (by rfl) ⟨1115075, by rfl⟩ : syracuseStep 1486767 = 2230151) B2230151
theorem B1486791 : Blo 1486063 1486791 := bstep (se 1 (by rfl) ⟨1115093, by rfl⟩ : syracuseStep 1486791 = 2230187) B2230187
theorem B1486811 : Blo 1486063 1486811 := bstep (se 1 (by rfl) ⟨1115108, by rfl⟩ : syracuseStep 1486811 = 2230217) B2230217
theorem B5648399 : Blo 1486063 5648399 := bstep (se 1 (by rfl) ⟨4236299, by rfl⟩ : syracuseStep 5648399 = 8472599) B8472599
theorem B3346451 : Blo 1486063 3346451 := bstep (se 1 (by rfl) ⟨2509838, by rfl⟩ : syracuseStep 3346451 = 5019677) B5019677
theorem B1486887 : Blo 1486063 1486887 := bstep (se 1 (by rfl) ⟨1115165, by rfl⟩ : syracuseStep 1486887 = 2230331) B2230331
theorem B2510905 : Blo 1486063 2510905 := bstep (se 2 (by rfl) ⟨941589, by rfl⟩ : syracuseStep 2510905 = 1883179) B1883179
theorem B5017679 : Blo 1486063 5017679 := bstep (se 1 (by rfl) ⟨3763259, by rfl⟩ : syracuseStep 5017679 = 7526519) B7526519
theorem B1486927 : Blo 1486063 1486927 := bstep (se 1 (by rfl) ⟨1115195, by rfl⟩ : syracuseStep 1486927 = 2230391) B2230391
theorem B3764303 : Blo 1486063 3764303 := bstep (se 1 (by rfl) ⟨2823227, by rfl⟩ : syracuseStep 3764303 = 5646455) B5646455
theorem B2117711 : Blo 1486063 2117711 := bstep (se 1 (by rfl) ⟨1588283, by rfl⟩ : syracuseStep 2117711 = 3176567) B3176567
theorem B1486943 : Blo 1486063 1486943 := bstep (se 1 (by rfl) ⟨1115207, by rfl⟩ : syracuseStep 1486943 = 2230415) B2230415
theorem B1486971 : Blo 1486063 1486971 := bstep (se 1 (by rfl) ⟨1115228, by rfl⟩ : syracuseStep 1486971 = 2230457) B2230457
theorem B4583581 : Blo 1486063 4583581 := bstep (se 3 (by rfl) ⟨859421, by rfl⟩ : syracuseStep 4583581 = 1718843) B1718843
theorem B1487023 : Blo 1486063 1487023 := bstep (se 1 (by rfl) ⟨1115267, by rfl⟩ : syracuseStep 1487023 = 2230535) B2230535
theorem B1487047 : Blo 1486063 1487047 := bstep (se 1 (by rfl) ⟨1115285, by rfl⟩ : syracuseStep 1487047 = 2230571) B2230571
theorem B2511047 : Blo 1486063 2511047 := bstep (se 1 (by rfl) ⟨1883285, by rfl⟩ : syracuseStep 2511047 = 3766571) B3766571
theorem B1487067 : Blo 1486063 1487067 := bstep (se 1 (by rfl) ⟨1115300, by rfl⟩ : syracuseStep 1487067 = 2230601) B2230601
theorem B1487143 : Blo 1486063 1487143 := bstep (se 1 (by rfl) ⟨1115357, by rfl⟩ : syracuseStep 1487143 = 2230715) B2230715
theorem B1487183 : Blo 1486063 1487183 := bstep (se 1 (by rfl) ⟨1115387, by rfl⟩ : syracuseStep 1487183 = 2230775) B2230775
theorem B1487199 : Blo 1486063 1487199 := bstep (se 1 (by rfl) ⟨1115399, by rfl⟩ : syracuseStep 1487199 = 2230799) B2230799
theorem B3346793 : Blo 1486063 3346793 := bstep (se 2 (by rfl) ⟨1255047, by rfl⟩ : syracuseStep 3346793 = 2510095) B2510095
theorem B1487227 : Blo 1486063 1487227 := bstep (se 1 (by rfl) ⟨1115420, by rfl⟩ : syracuseStep 1487227 = 2230841) B2230841
theorem B7524737 : Blo 1486063 7524737 := bstep (se 2 (by rfl) ⟨2821776, by rfl⟩ : syracuseStep 7524737 = 5643553) B5643553
theorem B1487279 : Blo 1486063 1487279 := bstep (se 1 (by rfl) ⟨1115459, by rfl⟩ : syracuseStep 1487279 = 2230919) B2230919
theorem B1487303 : Blo 1486063 1487303 := bstep (se 1 (by rfl) ⟨1115477, by rfl⟩ : syracuseStep 1487303 = 2230955) B2230955
theorem B5018057 : Blo 1486063 5018057 := bstep (se 2 (by rfl) ⟨1881771, by rfl⟩ : syracuseStep 5018057 = 3763543) B3763543
theorem B1487323 : Blo 1486063 1487323 := bstep (se 1 (by rfl) ⟨1115492, by rfl⟩ : syracuseStep 1487323 = 2230985) B2230985
theorem B5362157 : Blo 1486063 5362157 := bstep (se 3 (by rfl) ⟨1005404, by rfl⟩ : syracuseStep 5362157 = 2010809) B2010809
theorem B25399817 : Blo 1486063 25399817 := bstep (se 2 (by rfl) ⟨9524931, by rfl⟩ : syracuseStep 25399817 = 19049863) B19049863
theorem B6353441 : Blo 1486063 6353441 := bstep (se 2 (by rfl) ⟨2382540, by rfl⟩ : syracuseStep 6353441 = 4765081) B4765081
theorem B1487399 : Blo 1486063 1487399 := bstep (se 1 (by rfl) ⟨1115549, by rfl⟩ : syracuseStep 1487399 = 2231099) B2231099
theorem B1487439 : Blo 1486063 1487439 := bstep (se 1 (by rfl) ⟨1115579, by rfl⟩ : syracuseStep 1487439 = 2231159) B2231159
theorem B1487455 : Blo 1486063 1487455 := bstep (se 1 (by rfl) ⟨1115591, by rfl⟩ : syracuseStep 1487455 = 2231183) B2231183
theorem B2822779 : Blo 1486063 2822779 := bstep (se 1 (by rfl) ⟨2117084, by rfl⟩ : syracuseStep 2822779 = 4234169) B4234169
theorem B1487483 : Blo 1486063 1487483 := bstep (se 1 (by rfl) ⟨1115612, by rfl⟩ : syracuseStep 1487483 = 2231225) B2231225
theorem B1487535 : Blo 1486063 1487535 := bstep (se 1 (by rfl) ⟨1115651, by rfl⟩ : syracuseStep 1487535 = 2231303) B2231303
theorem B1487559 : Blo 1486063 1487559 := bstep (se 1 (by rfl) ⟨1115669, by rfl⟩ : syracuseStep 1487559 = 2231339) B2231339
theorem B5018327 : Blo 1486063 5018327 := bstep (se 1 (by rfl) ⟨3763745, by rfl⟩ : syracuseStep 5018327 = 7527491) B7527491
theorem B3764951 : Blo 1486063 3764951 := bstep (se 1 (by rfl) ⟨2823713, by rfl⟩ : syracuseStep 3764951 = 5647427) B5647427
theorem B1487579 : Blo 1486063 1487579 := bstep (se 1 (by rfl) ⟨1115684, by rfl⟩ : syracuseStep 1487579 = 2231369) B2231369
theorem B1487655 : Blo 1486063 1487655 := bstep (se 1 (by rfl) ⟨1115741, by rfl⟩ : syracuseStep 1487655 = 2231483) B2231483
theorem B1487695 : Blo 1486063 1487695 := bstep (se 1 (by rfl) ⟨1115771, by rfl⟩ : syracuseStep 1487695 = 2231543) B2231543
theorem B2823007 : Blo 1486063 2823007 := bstep (se 1 (by rfl) ⟨2117255, by rfl⟩ : syracuseStep 2823007 = 4234511) B4234511
theorem B1487711 : Blo 1486063 1487711 := bstep (se 1 (by rfl) ⟨1115783, by rfl⟩ : syracuseStep 1487711 = 2231567) B2231567
theorem B1487739 : Blo 1486063 1487739 := bstep (se 1 (by rfl) ⟨1115804, by rfl⟩ : syracuseStep 1487739 = 2231609) B2231609
theorem B5018543 : Blo 1486063 5018543 := bstep (se 1 (by rfl) ⟨3763907, by rfl⟩ : syracuseStep 5018543 = 7527815) B7527815
theorem B1487791 : Blo 1486063 1487791 := bstep (se 1 (by rfl) ⟨1115843, by rfl⟩ : syracuseStep 1487791 = 2231687) B2231687
theorem B3347387 : Blo 1486063 3347387 := bstep (se 1 (by rfl) ⟨2510540, by rfl⟩ : syracuseStep 3347387 = 5021081) B5021081
theorem B1487815 : Blo 1486063 1487815 := bstep (se 1 (by rfl) ⟨1115861, by rfl⟩ : syracuseStep 1487815 = 2231723) B2231723
theorem B1487835 : Blo 1486063 1487835 := bstep (se 1 (by rfl) ⟨1115876, by rfl⟩ : syracuseStep 1487835 = 2231753) B2231753
theorem B1487911 : Blo 1486063 1487911 := bstep (se 1 (by rfl) ⟨1115933, by rfl⟩ : syracuseStep 1487911 = 2231867) B2231867
theorem B3765305 : Blo 1486063 3765305 := bstep (se 2 (by rfl) ⟨1411989, by rfl⟩ : syracuseStep 3765305 = 2823979) B2823979
theorem B3347513 : Blo 1486063 3347513 := bstep (se 2 (by rfl) ⟨1255317, by rfl⟩ : syracuseStep 3347513 = 2510635) B2510635
theorem B1487951 : Blo 1486063 1487951 := bstep (se 1 (by rfl) ⟨1115963, by rfl⟩ : syracuseStep 1487951 = 2231927) B2231927
theorem B2823265 : Blo 1486063 2823265 := bstep (se 2 (by rfl) ⟨1058724, by rfl⟩ : syracuseStep 2823265 = 2117449) B2117449
theorem B1487967 : Blo 1486063 1487967 := bstep (se 1 (by rfl) ⟨1115975, by rfl⟩ : syracuseStep 1487967 = 2231951) B2231951
theorem B1487995 : Blo 1486063 1487995 := bstep (se 1 (by rfl) ⟨1115996, by rfl⟩ : syracuseStep 1487995 = 2231993) B2231993
theorem B7525547 : Blo 1486063 7525547 := bstep (se 1 (by rfl) ⟨5644160, by rfl⟩ : syracuseStep 7525547 = 11288321) B11288321
theorem B1488047 : Blo 1486063 1488047 := bstep (se 1 (by rfl) ⟨1116035, by rfl⟩ : syracuseStep 1488047 = 2232071) B2232071
theorem B10171595 : Blo 1486063 10171595 := bstep (se 1 (by rfl) ⟨7628696, by rfl⟩ : syracuseStep 10171595 = 15257393) B15257393
theorem B3347855 : Blo 1486063 3347855 := bstep (se 1 (by rfl) ⟨2510891, by rfl⟩ : syracuseStep 3347855 = 5021783) B5021783
theorem B2823599 : Blo 1486063 2823599 := bstep (se 1 (by rfl) ⟨2117699, by rfl⟩ : syracuseStep 2823599 = 4235399) B4235399
theorem B11294153 : Blo 1486063 11294153 := bstep (se 2 (by rfl) ⟨4235307, by rfl⟩ : syracuseStep 11294153 = 8470615) B8470615
theorem B16307675 : Blo 1486063 16307675 := bstep (se 1 (by rfl) ⟨12230756, by rfl⟩ : syracuseStep 16307675 = 24461513) B24461513
theorem B4765223 : Blo 1486063 4765223 := bstep (se 1 (by rfl) ⟨3573917, by rfl⟩ : syracuseStep 4765223 = 7147835) B7147835
theorem B11449943 : Blo 1486063 11449943 := bstep (se 1 (by rfl) ⟨8587457, by rfl⟩ : syracuseStep 11449943 = 17174915) B17174915
theorem B25417313 : Blo 1486063 25417313 := bstep (se 2 (by rfl) ⟨9531492, by rfl⟩ : syracuseStep 25417313 = 19062985) B19062985
theorem B7526033 : Blo 1486063 7526033 := bstep (se 2 (by rfl) ⟨2822262, by rfl⟩ : syracuseStep 7526033 = 5644525) B5644525
theorem B4232893 : Blo 1486063 4232893 := bstep (se 3 (by rfl) ⟨793667, by rfl⟩ : syracuseStep 4232893 = 1587335) B1587335
theorem B12056363 : Blo 1486063 12056363 := bstep (se 1 (by rfl) ⟨9042272, by rfl⟩ : syracuseStep 12056363 = 18084545) B18084545
theorem B1906615 : Blo 1486063 1906615 := bstep (se 1 (by rfl) ⟨1429961, by rfl⟩ : syracuseStep 1906615 = 2859923) B2859923
theorem B6354875 : Blo 1486063 6354875 := bstep (se 1 (by rfl) ⟨4766156, by rfl⟩ : syracuseStep 6354875 = 9532313) B9532313
theorem B8034241 : Blo 1486063 8034241 := bstep (se 2 (by rfl) ⟨3012840, by rfl⟩ : syracuseStep 8034241 = 6025681) B6025681
theorem B4233235 : Blo 1486063 4233235 := bstep (se 1 (by rfl) ⟨3174926, by rfl⟩ : syracuseStep 4233235 = 6349853) B6349853
theorem B9050201 : Blo 1486063 9050201 := bstep (se 2 (by rfl) ⟨3393825, by rfl⟩ : syracuseStep 9050201 = 6787651) B6787651
theorem B43473185 : Blo 1486063 43473185 := bstep (se 2 (by rfl) ⟨16302444, by rfl⟩ : syracuseStep 43473185 = 32604889) B32604889
theorem B9533801 : Blo 1486063 9533801 := bstep (se 2 (by rfl) ⟨3575175, by rfl⟩ : syracuseStep 9533801 = 7150351) B7150351
theorem B2824723 : Blo 1486063 2824723 := bstep (se 1 (by rfl) ⟨2118542, by rfl⟩ : syracuseStep 2824723 = 4237085) B4237085
theorem B1882703 : Blo 1486063 1882703 := bstep (se 1 (by rfl) ⟨1412027, by rfl⟩ : syracuseStep 1882703 = 2824055) B2824055
theorem B2824951 : Blo 1486063 2824951 := bstep (se 1 (by rfl) ⟨2118713, by rfl⟩ : syracuseStep 2824951 = 4237427) B4237427
theorem B23190341 : Blo 1486063 23190341 := bstep (se 4 (by rfl) ⟨2174094, by rfl⟩ : syracuseStep 23190341 = 4348189) B4348189
theorem B4832119 : Blo 1486063 4832119 := bstep (se 1 (by rfl) ⟨3624089, by rfl⟩ : syracuseStep 4832119 = 7248179) B7248179
theorem B2415503 : Blo 1486063 2415503 := bstep (se 1 (by rfl) ⟨1811627, by rfl⟩ : syracuseStep 2415503 = 3623255) B3623255
theorem B17161105 : Blo 1486063 17161105 := bstep (se 2 (by rfl) ⟨6435414, by rfl⟩ : syracuseStep 17161105 = 12870829) B12870829
theorem B8469431 : Blo 1486063 8469431 := bstep (se 1 (by rfl) ⟨6352073, by rfl⟩ : syracuseStep 8469431 = 12704147) B12704147
theorem B3177643 : Blo 1486063 3177643 := bstep (se 1 (by rfl) ⟨2383232, by rfl⟩ : syracuseStep 3177643 = 4766465) B4766465
theorem B5020919 : Blo 1486063 5020919 := bstep (se 1 (by rfl) ⟨3765689, by rfl⟩ : syracuseStep 5020919 = 7531379) B7531379
theorem B4234625 : Blo 1486063 4234625 := bstep (se 2 (by rfl) ⟨1587984, by rfl⟩ : syracuseStep 4234625 = 3175969) B3175969
theorem B24444341 : Blo 1486063 24444341 := bstep (se 5 (by rfl) ⟨1145828, by rfl⟩ : syracuseStep 24444341 = 2291657) B2291657
theorem B5430817 : Blo 1486063 5430817 := bstep (se 2 (by rfl) ⟨2036556, by rfl⟩ : syracuseStep 5430817 = 4073113) B4073113
theorem B5021243 : Blo 1486063 5021243 := bstep (se 1 (by rfl) ⟨3765932, by rfl⟩ : syracuseStep 5021243 = 7531865) B7531865
theorem B12697175 : Blo 1486063 12697175 := bstep (se 1 (by rfl) ⟨9522881, by rfl⟩ : syracuseStep 12697175 = 19045763) B19045763
theorem B4521683 : Blo 1486063 4521683 := bstep (se 1 (by rfl) ⟨3391262, by rfl⟩ : syracuseStep 4521683 = 6782525) B6782525
theorem B4234967 : Blo 1486063 4234967 := bstep (se 1 (by rfl) ⟨3176225, by rfl⟩ : syracuseStep 4234967 = 6352451) B6352451
theorem B5644025 : Blo 1486063 5644025 := bstep (se 2 (by rfl) ⟨2116509, by rfl⟩ : syracuseStep 5644025 = 4233019) B4233019
theorem B5881643 : Blo 1486063 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B5021513 : Blo 1486063 5021513 := bstep (se 2 (by rfl) ⟨1883067, by rfl⟩ : syracuseStep 5021513 = 3766135) B3766135
theorem B7528301 : Blo 1486063 7528301 := bstep (se 3 (by rfl) ⟨1411556, by rfl⟩ : syracuseStep 7528301 = 2823113) B2823113
theorem B8470433 : Blo 1486063 8470433 := bstep (se 2 (by rfl) ⟨3176412, by rfl⟩ : syracuseStep 8470433 = 6352825) B6352825
theorem B5644313 : Blo 1486063 5644313 := bstep (se 2 (by rfl) ⟨2116617, by rfl⟩ : syracuseStep 5644313 = 4233235) B4233235
theorem B16933211 : Blo 1486063 16933211 := bstep (se 1 (by rfl) ⟨12699908, by rfl⟩ : syracuseStep 16933211 = 25399817) B25399817
theorem B4235627 : Blo 1486063 4235627 := bstep (se 1 (by rfl) ⟨3176720, by rfl⟩ : syracuseStep 4235627 = 6353441) B6353441
theorem B3621287 : Blo 1486063 3621287 := bstep (se 1 (by rfl) ⟨2715965, by rfl⟩ : syracuseStep 3621287 = 5431931) B5431931
theorem B27124253 : Blo 1486063 27124253 := bstep (se 3 (by rfl) ⟨5085797, by rfl⟩ : syracuseStep 27124253 = 10171595) B10171595
theorem B7627385 : Blo 1486063 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B24445765 : Blo 1486063 24445765 := bstep (se 4 (by rfl) ⟨2291790, by rfl⟩ : syracuseStep 24445765 = 4583581) B4583581
theorem B1672015 : Blo 1486063 1672015 := bstep (se 1 (by rfl) ⟨1254011, by rfl⟩ : syracuseStep 1672015 = 2508023) B2508023
theorem B7529435 : Blo 1486063 7529435 := bstep (se 1 (by rfl) ⟨5647076, by rfl⟩ : syracuseStep 7529435 = 11294153) B11294153
theorem B10871783 : Blo 1486063 10871783 := bstep (se 1 (by rfl) ⟨8153837, by rfl⟩ : syracuseStep 10871783 = 16307675) B16307675
theorem B7529597 : Blo 1486063 7529597 := bstep (se 3 (by rfl) ⟨1411799, by rfl⟩ : syracuseStep 7529597 = 2823599) B2823599
theorem B22881473 : Blo 1486063 22881473 := bstep (se 2 (by rfl) ⟨8580552, by rfl⟩ : syracuseStep 22881473 = 17161105) B17161105
theorem B8037575 : Blo 1486063 8037575 := bstep (se 1 (by rfl) ⟨6028181, by rfl⟩ : syracuseStep 8037575 = 12056363) B12056363
theorem B2229467 : Blo 1486063 2229467 := bstep (se 1 (by rfl) ⟨1672100, by rfl⟩ : syracuseStep 2229467 = 3344201) B3344201
theorem B1672411 : Blo 1486063 1672411 := bstep (se 1 (by rfl) ⟨1254308, by rfl⟩ : syracuseStep 1672411 = 2508617) B2508617
theorem B2229641 : Blo 1486063 2229641 := bstep (se 2 (by rfl) ⟨836115, by rfl⟩ : syracuseStep 2229641 = 1672231) B1672231
theorem B7529921 : Blo 1486063 7529921 := bstep (se 2 (by rfl) ⟨2823720, by rfl⟩ : syracuseStep 7529921 = 5647441) B5647441
theorem B1672699 : Blo 1486063 1672699 := bstep (se 1 (by rfl) ⟨1254524, by rfl⟩ : syracuseStep 1672699 = 2509049) B2509049
theorem B4236857 : Blo 1486063 4236857 := bstep (se 2 (by rfl) ⟨1588821, by rfl⟩ : syracuseStep 4236857 = 3177643) B3177643
theorem B3343967 : Blo 1486063 3343967 := bstep (se 1 (by rfl) ⟨2507975, by rfl⟩ : syracuseStep 3343967 = 5015951) B5015951
theorem B1672879 : Blo 1486063 1672879 := bstep (se 1 (by rfl) ⟨1254659, by rfl⟩ : syracuseStep 1672879 = 2509319) B2509319
theorem B2508475 : Blo 1486063 2508475 := bstep (se 1 (by rfl) ⟨1881356, by rfl⟩ : syracuseStep 2508475 = 3762713) B3762713
theorem B2229995 : Blo 1486063 2229995 := bstep (se 1 (by rfl) ⟨1672496, by rfl⟩ : syracuseStep 2229995 = 3344993) B3344993
theorem B3344183 : Blo 1486063 3344183 := bstep (se 1 (by rfl) ⟨2508137, by rfl⟩ : syracuseStep 3344183 = 5016275) B5016275
theorem B48236471 : Blo 1486063 48236471 := bstep (se 1 (by rfl) ⟨36177353, by rfl⟩ : syracuseStep 48236471 = 72354707) B72354707
theorem B2230223 : Blo 1486063 2230223 := bstep (se 1 (by rfl) ⟨1672667, by rfl⟩ : syracuseStep 2230223 = 3345335) B3345335
theorem B5646287 : Blo 1486063 5646287 := bstep (se 1 (by rfl) ⟨4234715, by rfl⟩ : syracuseStep 5646287 = 8469431) B8469431
theorem B1673167 : Blo 1486063 1673167 := bstep (se 1 (by rfl) ⟨1254875, by rfl⟩ : syracuseStep 1673167 = 2509751) B2509751
theorem B3344489 : Blo 1486063 3344489 := bstep (se 2 (by rfl) ⟨1254183, by rfl⟩ : syracuseStep 3344489 = 2508367) B2508367
theorem B5015681 : Blo 1486063 5015681 := bstep (se 2 (by rfl) ⟨1880880, by rfl⟩ : syracuseStep 5015681 = 3761761) B3761761
theorem B57198797 : Blo 1486063 57198797 := bstep (se 3 (by rfl) ⟨10724774, by rfl⟩ : syracuseStep 57198797 = 21449549) B21449549
theorem B16296227 : Blo 1486063 16296227 := bstep (se 1 (by rfl) ⟨12222170, by rfl⟩ : syracuseStep 16296227 = 24444341) B24444341
theorem B2230619 : Blo 1486063 2230619 := bstep (se 1 (by rfl) ⟨1672964, by rfl⟩ : syracuseStep 2230619 = 3345929) B3345929
theorem B1673563 : Blo 1486063 1673563 := bstep (se 1 (by rfl) ⟨1255172, by rfl⟩ : syracuseStep 1673563 = 2510345) B2510345
theorem B8464783 : Blo 1486063 8464783 := bstep (se 1 (by rfl) ⟨6348587, by rfl⟩ : syracuseStep 8464783 = 12697175) B12697175
theorem B1673671 : Blo 1486063 1673671 := bstep (se 1 (by rfl) ⟨1255253, by rfl⟩ : syracuseStep 1673671 = 2510507) B2510507
theorem B9521651 : Blo 1486063 9521651 := bstep (se 1 (by rfl) ⟨7141238, by rfl⟩ : syracuseStep 9521651 = 14282477) B14282477
theorem B5016059 : Blo 1486063 5016059 := bstep (se 1 (by rfl) ⟨3762044, by rfl⟩ : syracuseStep 5016059 = 7524089) B7524089
theorem B3762683 : Blo 1486063 3762683 := bstep (se 1 (by rfl) ⟨2822012, by rfl⟩ : syracuseStep 3762683 = 5644025) B5644025
theorem B2230847 : Blo 1486063 2230847 := bstep (se 1 (by rfl) ⟨1673135, by rfl⟩ : syracuseStep 2230847 = 3346271) B3346271
theorem B2542153 : Blo 1486063 2542153 := bstep (se 2 (by rfl) ⟨953307, by rfl⟩ : syracuseStep 2542153 = 1906615) B1906615
theorem B3344975 : Blo 1486063 3344975 := bstep (se 1 (by rfl) ⟨2508731, by rfl⟩ : syracuseStep 3344975 = 5017463) B5017463
theorem B25741925 : Blo 1486063 25741925 := bstep (se 4 (by rfl) ⟨2413305, by rfl⟩ : syracuseStep 25741925 = 4826611) B4826611
theorem B5646955 : Blo 1486063 5646955 := bstep (se 1 (by rfl) ⟨4235216, by rfl⟩ : syracuseStep 5646955 = 8470433) B8470433
theorem B8039087 : Blo 1486063 8039087 := bstep (se 1 (by rfl) ⟨6029315, by rfl⟩ : syracuseStep 8039087 = 12058631) B12058631
theorem B2230967 : Blo 1486063 2230967 := bstep (se 1 (by rfl) ⟨1673225, by rfl⟩ : syracuseStep 2230967 = 3346451) B3346451
theorem B16296659 : Blo 1486063 16296659 := bstep (se 1 (by rfl) ⟨12222494, by rfl⟩ : syracuseStep 16296659 = 24444989) B24444989
theorem B3345119 : Blo 1486063 3345119 := bstep (se 1 (by rfl) ⟨2508839, by rfl⟩ : syracuseStep 3345119 = 5017679) B5017679
theorem B2509535 : Blo 1486063 2509535 := bstep (se 1 (by rfl) ⟨1882151, by rfl⟩ : syracuseStep 2509535 = 3764303) B3764303
theorem B1674031 : Blo 1486063 1674031 := bstep (se 1 (by rfl) ⟨1255523, by rfl⟩ : syracuseStep 1674031 = 2511047) B2511047
theorem B5647229 : Blo 1486063 5647229 := bstep (se 3 (by rfl) ⟨1058855, by rfl⟩ : syracuseStep 5647229 = 2117711) B2117711
theorem B5647259 : Blo 1486063 5647259 := bstep (se 1 (by rfl) ⟨4235444, by rfl⟩ : syracuseStep 5647259 = 8470889) B8470889
theorem B2231195 : Blo 1486063 2231195 := bstep (se 1 (by rfl) ⟨1673396, by rfl⟩ : syracuseStep 2231195 = 3346793) B3346793
theorem B5016491 : Blo 1486063 5016491 := bstep (se 1 (by rfl) ⟨3762368, by rfl⟩ : syracuseStep 5016491 = 7524737) B7524737
theorem B3345371 : Blo 1486063 3345371 := bstep (se 1 (by rfl) ⟨2509028, by rfl⟩ : syracuseStep 3345371 = 5018057) B5018057
theorem B4762763 : Blo 1486063 4762763 := bstep (se 1 (by rfl) ⟨3572072, by rfl⟩ : syracuseStep 4762763 = 7144145) B7144145
theorem B3345551 : Blo 1486063 3345551 := bstep (se 1 (by rfl) ⟨2509163, by rfl⟩ : syracuseStep 3345551 = 5018327) B5018327
theorem B2509967 : Blo 1486063 2509967 := bstep (se 1 (by rfl) ⟨1882475, by rfl⟩ : syracuseStep 2509967 = 3764951) B3764951
theorem B3345641 : Blo 1486063 3345641 := bstep (se 2 (by rfl) ⟨1254615, by rfl⟩ : syracuseStep 3345641 = 2509231) B2509231
theorem B1486111 : Blo 1486063 1486111 := bstep (se 1 (by rfl) ⟨1114583, by rfl⟩ : syracuseStep 1486111 = 2229167) B2229167
theorem B3345695 : Blo 1486063 3345695 := bstep (se 1 (by rfl) ⟨2509271, by rfl⟩ : syracuseStep 3345695 = 5018543) B5018543
theorem B2231591 : Blo 1486063 2231591 := bstep (se 1 (by rfl) ⟨1673693, by rfl⟩ : syracuseStep 2231591 = 3347387) B3347387
theorem B1486171 : Blo 1486063 1486171 := bstep (se 1 (by rfl) ⟨1114628, by rfl⟩ : syracuseStep 1486171 = 2229257) B2229257
theorem B1486191 : Blo 1486063 1486191 := bstep (se 1 (by rfl) ⟨1114643, by rfl⟩ : syracuseStep 1486191 = 2229287) B2229287
theorem B2510203 : Blo 1486063 2510203 := bstep (se 1 (by rfl) ⟨1882652, by rfl⟩ : syracuseStep 2510203 = 3765305) B3765305
theorem B2231675 : Blo 1486063 2231675 := bstep (se 1 (by rfl) ⟨1673756, by rfl⟩ : syracuseStep 2231675 = 3347513) B3347513
theorem B1486247 : Blo 1486063 1486247 := bstep (se 1 (by rfl) ⟨1114685, by rfl⟩ : syracuseStep 1486247 = 2229371) B2229371
theorem B5017031 : Blo 1486063 5017031 := bstep (se 1 (by rfl) ⟨3762773, by rfl⟩ : syracuseStep 5017031 = 7525547) B7525547
theorem B3763655 : Blo 1486063 3763655 := bstep (se 1 (by rfl) ⟨2822741, by rfl⟩ : syracuseStep 3763655 = 5645483) B5645483
theorem B2821625 : Blo 1486063 2821625 := bstep (se 2 (by rfl) ⟨1058109, by rfl⟩ : syracuseStep 2821625 = 2116219) B2116219
theorem B3763705 : Blo 1486063 3763705 := bstep (se 2 (by rfl) ⟨1411389, by rfl⟩ : syracuseStep 3763705 = 2822779) B2822779
theorem B1486331 : Blo 1486063 1486331 := bstep (se 1 (by rfl) ⟨1114748, by rfl⟩ : syracuseStep 1486331 = 2229497) B2229497
theorem B2231801 : Blo 1486063 2231801 := bstep (se 2 (by rfl) ⟨836925, by rfl⟩ : syracuseStep 2231801 = 1673851) B1673851
theorem B1486399 : Blo 1486063 1486399 := bstep (se 1 (by rfl) ⟨1114799, by rfl⟩ : syracuseStep 1486399 = 2229599) B2229599
theorem B1486407 : Blo 1486063 1486407 := bstep (se 1 (by rfl) ⟨1114805, by rfl⟩ : syracuseStep 1486407 = 2229611) B2229611
theorem B2231903 : Blo 1486063 2231903 := bstep (se 1 (by rfl) ⟨1673927, by rfl⟩ : syracuseStep 2231903 = 3347855) B3347855
theorem B1486559 : Blo 1486063 1486559 := bstep (se 1 (by rfl) ⟨1114919, by rfl⟩ : syracuseStep 1486559 = 2229839) B2229839
theorem B16944875 : Blo 1486063 16944875 := bstep (se 1 (by rfl) ⟨12708656, by rfl⟩ : syracuseStep 16944875 = 25417313) B25417313
theorem B5017355 : Blo 1486063 5017355 := bstep (se 1 (by rfl) ⟨3763016, by rfl⟩ : syracuseStep 5017355 = 7526033) B7526033
theorem B3764009 : Blo 1486063 3764009 := bstep (se 2 (by rfl) ⟨1411503, by rfl⟩ : syracuseStep 3764009 = 2823007) B2823007
theorem B3346217 : Blo 1486063 3346217 := bstep (se 2 (by rfl) ⟨1254831, by rfl⟩ : syracuseStep 3346217 = 2509663) B2509663
theorem B1486639 : Blo 1486063 1486639 := bstep (se 1 (by rfl) ⟨1114979, by rfl⟩ : syracuseStep 1486639 = 2229959) B2229959
theorem B4534073 : Blo 1486063 4534073 := bstep (se 2 (by rfl) ⟨1700277, by rfl⟩ : syracuseStep 4534073 = 3400555) B3400555
theorem B12701549 : Blo 1486063 12701549 := bstep (se 3 (by rfl) ⟨2381540, by rfl⟩ : syracuseStep 12701549 = 4763081) B4763081
theorem B1486747 : Blo 1486063 1486747 := bstep (se 1 (by rfl) ⟨1115060, by rfl⟩ : syracuseStep 1486747 = 2230121) B2230121
theorem B1486799 : Blo 1486063 1486799 := bstep (se 1 (by rfl) ⟨1115099, by rfl⟩ : syracuseStep 1486799 = 2230199) B2230199
theorem B14299085 : Blo 1486063 14299085 := bstep (se 3 (by rfl) ⟨2681078, by rfl⟩ : syracuseStep 14299085 = 5362157) B5362157
theorem B1486823 : Blo 1486063 1486823 := bstep (se 1 (by rfl) ⟨1115117, by rfl⟩ : syracuseStep 1486823 = 2230235) B2230235
theorem B5017625 : Blo 1486063 5017625 := bstep (se 2 (by rfl) ⟨1881609, by rfl⟩ : syracuseStep 5017625 = 3763219) B3763219
theorem B6033467 : Blo 1486063 6033467 := bstep (se 1 (by rfl) ⟨4525100, by rfl⟩ : syracuseStep 6033467 = 9050201) B9050201
theorem B3764353 : Blo 1486063 3764353 := bstep (se 2 (by rfl) ⟨1411632, by rfl⟩ : syracuseStep 3764353 = 2823265) B2823265
theorem B7942315 : Blo 1486063 7942315 := bstep (se 1 (by rfl) ⟨5956736, by rfl⟩ : syracuseStep 7942315 = 11913473) B11913473
theorem B1487135 : Blo 1486063 1487135 := bstep (se 1 (by rfl) ⟨1115351, by rfl⟩ : syracuseStep 1487135 = 2230703) B2230703
theorem B1487195 : Blo 1486063 1487195 := bstep (se 1 (by rfl) ⟨1115396, by rfl⟩ : syracuseStep 1487195 = 2230793) B2230793
theorem B1487215 : Blo 1486063 1487215 := bstep (se 1 (by rfl) ⟨1115411, by rfl⟩ : syracuseStep 1487215 = 2230823) B2230823
theorem B1487271 : Blo 1486063 1487271 := bstep (se 1 (by rfl) ⟨1115453, by rfl⟩ : syracuseStep 1487271 = 2230907) B2230907
theorem B1487355 : Blo 1486063 1487355 := bstep (se 1 (by rfl) ⟨1115516, by rfl⟩ : syracuseStep 1487355 = 2231033) B2231033
theorem B1487423 : Blo 1486063 1487423 := bstep (se 1 (by rfl) ⟨1115567, by rfl⟩ : syracuseStep 1487423 = 2231135) B2231135
theorem B1487431 : Blo 1486063 1487431 := bstep (se 1 (by rfl) ⟨1115573, by rfl⟩ : syracuseStep 1487431 = 2231147) B2231147
theorem B1610335 : Blo 1486063 1610335 := bstep (se 1 (by rfl) ⟨1207751, by rfl⟩ : syracuseStep 1610335 = 2415503) B2415503
theorem B7631507 : Blo 1486063 7631507 := bstep (se 1 (by rfl) ⟨5723630, by rfl⟩ : syracuseStep 7631507 = 11447261) B11447261
theorem B1487583 : Blo 1486063 1487583 := bstep (se 1 (by rfl) ⟨1115687, by rfl⟩ : syracuseStep 1487583 = 2231375) B2231375
theorem B1487663 : Blo 1486063 1487663 := bstep (se 1 (by rfl) ⟨1115747, by rfl⟩ : syracuseStep 1487663 = 2231495) B2231495
theorem B1880911 : Blo 1486063 1880911 := bstep (se 1 (by rfl) ⟨1410683, by rfl⟩ : syracuseStep 1880911 = 2821367) B2821367
theorem B3347279 : Blo 1486063 3347279 := bstep (se 1 (by rfl) ⟨2510459, by rfl⟩ : syracuseStep 3347279 = 5020919) B5020919
theorem B1487771 : Blo 1486063 1487771 := bstep (se 1 (by rfl) ⟨1115828, by rfl⟩ : syracuseStep 1487771 = 2231657) B2231657
theorem B2823083 : Blo 1486063 2823083 := bstep (se 1 (by rfl) ⟨2117312, by rfl⟩ : syracuseStep 2823083 = 4234625) B4234625
theorem B3765163 : Blo 1486063 3765163 := bstep (se 1 (by rfl) ⟨2823872, by rfl⟩ : syracuseStep 3765163 = 5647745) B5647745
theorem B1487823 : Blo 1486063 1487823 := bstep (se 1 (by rfl) ⟨1115867, by rfl⟩ : syracuseStep 1487823 = 2231735) B2231735
theorem B5649371 : Blo 1486063 5649371 := bstep (se 1 (by rfl) ⟨4237028, by rfl⟩ : syracuseStep 5649371 = 8474057) B8474057
theorem B1487847 : Blo 1486063 1487847 := bstep (se 1 (by rfl) ⟨1115885, by rfl⟩ : syracuseStep 1487847 = 2231771) B2231771
theorem B3347495 : Blo 1486063 3347495 := bstep (se 1 (by rfl) ⟨2510621, by rfl⟩ : syracuseStep 3347495 = 5021243) B5021243
theorem B2823311 : Blo 1486063 2823311 := bstep (se 1 (by rfl) ⟨2117483, by rfl⟩ : syracuseStep 2823311 = 4234967) B4234967
theorem B16946333 : Blo 1486063 16946333 := bstep (se 3 (by rfl) ⟨3177437, by rfl⟩ : syracuseStep 16946333 = 6354875) B6354875
theorem B3921095 : Blo 1486063 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B3765467 : Blo 1486063 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B3347675 : Blo 1486063 3347675 := bstep (se 1 (by rfl) ⟨2510756, by rfl⟩ : syracuseStep 3347675 = 5021513) B5021513
theorem B5018867 : Blo 1486063 5018867 := bstep (se 1 (by rfl) ⟨3764150, by rfl⟩ : syracuseStep 5018867 = 7528301) B7528301
theorem B10712321 : Blo 1486063 10712321 := bstep (se 2 (by rfl) ⟨4017120, by rfl⟩ : syracuseStep 10712321 = 8034241) B8034241
theorem B5018975 : Blo 1486063 5018975 := bstep (se 1 (by rfl) ⟨3764231, by rfl⟩ : syracuseStep 5018975 = 7528463) B7528463
theorem B3765599 : Blo 1486063 3765599 := bstep (se 1 (by rfl) ⟨2824199, by rfl⟩ : syracuseStep 3765599 = 5648399) B5648399
theorem B3347873 : Blo 1486063 3347873 := bstep (se 2 (by rfl) ⟨1255452, by rfl⟩ : syracuseStep 3347873 = 2510905) B2510905
theorem B4232711 : Blo 1486063 4232711 := bstep (se 1 (by rfl) ⟨3174533, by rfl⟩ : syracuseStep 4232711 = 6349067) B6349067
theorem B20633221 : Blo 1486063 20633221 := bstep (se 4 (by rfl) ⟨1934364, by rfl⟩ : syracuseStep 20633221 = 3868729) B3868729
theorem B27121397 : Blo 1486063 27121397 := bstep (se 5 (by rfl) ⟨1271315, by rfl⟩ : syracuseStep 27121397 = 2542631) B2542631
theorem B4233167 : Blo 1486063 4233167 := bstep (se 1 (by rfl) ⟨3174875, by rfl⟩ : syracuseStep 4233167 = 6349751) B6349751
theorem B3766297 : Blo 1486063 3766297 := bstep (se 2 (by rfl) ⟨1412361, by rfl⟩ : syracuseStep 3766297 = 2824723) B2824723
theorem B15259727 : Blo 1486063 15259727 := bstep (se 1 (by rfl) ⟨11444795, by rfl⟩ : syracuseStep 15259727 = 22889591) B22889591
theorem B7247951 : Blo 1486063 7247951 := bstep (se 1 (by rfl) ⟨5435963, by rfl⟩ : syracuseStep 7247951 = 10871927) B10871927
theorem B16980131 : Blo 1486063 16980131 := bstep (se 1 (by rfl) ⟨12735098, by rfl⟩ : syracuseStep 16980131 = 25470197) B25470197
theorem B8042761 : Blo 1486063 8042761 := bstep (se 2 (by rfl) ⟨3016035, by rfl⟩ : syracuseStep 8042761 = 6032071) B6032071
theorem B7526681 : Blo 1486063 7526681 := bstep (se 2 (by rfl) ⟨2822505, by rfl⟩ : syracuseStep 7526681 = 5645011) B5645011
theorem B3766601 : Blo 1486063 3766601 := bstep (se 2 (by rfl) ⟨1412475, by rfl⟩ : syracuseStep 3766601 = 2824951) B2824951
theorem B3176815 : Blo 1486063 3176815 := bstep (se 1 (by rfl) ⟨2382611, by rfl⟩ : syracuseStep 3176815 = 4765223) B4765223
theorem B7633295 : Blo 1486063 7633295 := bstep (se 1 (by rfl) ⟨5724971, by rfl⟩ : syracuseStep 7633295 = 11449943) B11449943
theorem B183098033 : Blo 1486063 183098033 := bstep (se 2 (by rfl) ⟨68661762, by rfl⟩ : syracuseStep 183098033 = 137323525) B137323525
theorem B28982123 : Blo 1486063 28982123 := bstep (se 1 (by rfl) ⟨21736592, by rfl⟩ : syracuseStep 28982123 = 43473185) B43473185
theorem B5020541 : Blo 1486063 5020541 := bstep (se 3 (by rfl) ⟨941351, by rfl⟩ : syracuseStep 5020541 = 1882703) B1882703
theorem B6355867 : Blo 1486063 6355867 := bstep (se 1 (by rfl) ⟨4766900, by rfl⟩ : syracuseStep 6355867 = 9533801) B9533801
theorem B5020811 : Blo 1486063 5020811 := bstep (se 1 (by rfl) ⟨3765608, by rfl⟩ : syracuseStep 5020811 = 7531217) B7531217
theorem B10722469 : Blo 1486063 10722469 := bstep (se 4 (by rfl) ⟨1005231, by rfl⟩ : syracuseStep 10722469 = 2010463) B2010463
theorem B12057821 : Blo 1486063 12057821 := bstep (se 3 (by rfl) ⟨2260841, by rfl⟩ : syracuseStep 12057821 = 4521683) B4521683
theorem B25771301 : Blo 1486063 25771301 := bstep (se 4 (by rfl) ⟨2416059, by rfl⟩ : syracuseStep 25771301 = 4832119) B4832119
theorem B7241089 : Blo 1486063 7241089 := bstep (se 2 (by rfl) ⟨2715408, by rfl⟩ : syracuseStep 7241089 = 5430817) B5430817
theorem B2416009 : Blo 1486063 2416009 := bstep (se 2 (by rfl) ⟨906003, by rfl⟩ : syracuseStep 2416009 = 1812007) B1812007
theorem B15670691 : Blo 1486063 15670691 := bstep (se 1 (by rfl) ⟨11753018, by rfl⟩ : syracuseStep 15670691 = 23506037) B23506037
theorem B61840909 : Blo 1486063 61840909 := bstep (se 3 (by rfl) ⟨11595170, by rfl⟩ : syracuseStep 61840909 = 23190341) B23190341
theorem B5643857 : Blo 1486063 5643857 := bstep (se 2 (by rfl) ⟨2116446, by rfl⟩ : syracuseStep 5643857 = 4232893) B4232893
theorem B5644039 : Blo 1486063 5644039 := bstep (se 1 (by rfl) ⟨4233029, by rfl⟩ : syracuseStep 5644039 = 8466059) B8466059
theorem B5021729 : Blo 1486063 5021729 := bstep (se 2 (by rfl) ⟨1883148, by rfl⟩ : syracuseStep 5021729 = 3766297) B3766297
theorem B4022311 : Blo 1486063 4022311 := bstep (se 1 (by rfl) ⟨3016733, by rfl⟩ : syracuseStep 4022311 = 6033467) B6033467
theorem B11288807 : Blo 1486063 11288807 := bstep (se 1 (by rfl) ⟨8466605, by rfl⟩ : syracuseStep 11288807 = 16933211) B16933211
theorem B10723681 : Blo 1486063 10723681 := bstep (se 2 (by rfl) ⟨4021380, by rfl⟩ : syracuseStep 10723681 = 8042761) B8042761
theorem B4235753 : Blo 1486063 4235753 := bstep (se 2 (by rfl) ⟨1588407, by rfl⟩ : syracuseStep 4235753 = 3176815) B3176815
theorem B11297555 : Blo 1486063 11297555 := bstep (se 1 (by rfl) ⟨8473166, by rfl⟩ : syracuseStep 11297555 = 16946333) B16946333
theorem B2147113 : Blo 1486063 2147113 := bstep (se 2 (by rfl) ⟨805167, by rfl⟩ : syracuseStep 2147113 = 1610335) B1610335
theorem B15254315 : Blo 1486063 15254315 := bstep (se 1 (by rfl) ⟨11440736, by rfl⟩ : syracuseStep 15254315 = 22881473) B22881473
theorem B5358383 : Blo 1486063 5358383 := bstep (se 1 (by rfl) ⟨4018787, by rfl⟩ : syracuseStep 5358383 = 8037575) B8037575
theorem B7529273 : Blo 1486063 7529273 := bstep (se 2 (by rfl) ⟨2823477, by rfl⟩ : syracuseStep 7529273 = 5646955) B5646955
theorem B2229311 : Blo 1486063 2229311 := bstep (se 1 (by rfl) ⟨1671983, by rfl⟩ : syracuseStep 2229311 = 3343967) B3343967
theorem B2507881 : Blo 1486063 2507881 := bstep (se 2 (by rfl) ⟨940455, by rfl⟩ : syracuseStep 2507881 = 1880911) B1880911
theorem B2229353 : Blo 1486063 2229353 := bstep (se 2 (by rfl) ⟨836007, by rfl⟩ : syracuseStep 2229353 = 1672015) B1672015
theorem B2229455 : Blo 1486063 2229455 := bstep (se 1 (by rfl) ⟨1672091, by rfl⟩ : syracuseStep 2229455 = 3344183) B3344183
theorem B2229659 : Blo 1486063 2229659 := bstep (se 1 (by rfl) ⟨1672244, by rfl⟩ : syracuseStep 2229659 = 3344489) B3344489
theorem B3343787 : Blo 1486063 3343787 := bstep (se 1 (by rfl) ⟨2507840, by rfl⟩ : syracuseStep 3343787 = 5015681) B5015681
theorem B10864151 : Blo 1486063 10864151 := bstep (se 1 (by rfl) ⟨8148113, by rfl⟩ : syracuseStep 10864151 = 16296227) B16296227
theorem B14296625 : Blo 1486063 14296625 := bstep (se 2 (by rfl) ⟨5361234, by rfl⟩ : syracuseStep 14296625 = 10722469) B10722469
theorem B5088863 : Blo 1486063 5088863 := bstep (se 1 (by rfl) ⟨3816647, by rfl⟩ : syracuseStep 5088863 = 7633295) B7633295
theorem B2229881 : Blo 1486063 2229881 := bstep (se 2 (by rfl) ⟨836205, by rfl⟩ : syracuseStep 2229881 = 1672411) B1672411
theorem B3344039 : Blo 1486063 3344039 := bstep (se 1 (by rfl) ⟨2508029, by rfl⟩ : syracuseStep 3344039 = 5016059) B5016059
theorem B2508455 : Blo 1486063 2508455 := bstep (se 1 (by rfl) ⟨1881341, by rfl⟩ : syracuseStep 2508455 = 3762683) B3762683
theorem B130377413 : Blo 1486063 130377413 := bstep (se 4 (by rfl) ⟨12222882, by rfl⟩ : syracuseStep 130377413 = 24445765) B24445765
theorem B2229983 : Blo 1486063 2229983 := bstep (se 1 (by rfl) ⟨1672487, by rfl⟩ : syracuseStep 2229983 = 3344975) B3344975
theorem B20350685 : Blo 1486063 20350685 := bstep (se 3 (by rfl) ⟨3815753, by rfl⟩ : syracuseStep 20350685 = 7631507) B7631507
theorem B5359391 : Blo 1486063 5359391 := bstep (se 1 (by rfl) ⟨4019543, by rfl⟩ : syracuseStep 5359391 = 8039087) B8039087
theorem B10864439 : Blo 1486063 10864439 := bstep (se 1 (by rfl) ⟨8148329, by rfl⟩ : syracuseStep 10864439 = 16296659) B16296659
theorem B2230079 : Blo 1486063 2230079 := bstep (se 1 (by rfl) ⟨1672559, by rfl⟩ : syracuseStep 2230079 = 3345119) B3345119
theorem B1673023 : Blo 1486063 1673023 := bstep (se 1 (by rfl) ⟨1254767, by rfl⟩ : syracuseStep 1673023 = 2509535) B2509535
theorem B3221345 : Blo 1486063 3221345 := bstep (se 2 (by rfl) ⟨1208004, by rfl⟩ : syracuseStep 3221345 = 2416009) B2416009
theorem B3344327 : Blo 1486063 3344327 := bstep (se 1 (by rfl) ⟨2508245, by rfl⟩ : syracuseStep 3344327 = 5016491) B5016491
theorem B2230247 : Blo 1486063 2230247 := bstep (se 1 (by rfl) ⟨1672685, by rfl⟩ : syracuseStep 2230247 = 3345371) B3345371
theorem B2230265 : Blo 1486063 2230265 := bstep (se 2 (by rfl) ⟨836349, by rfl⟩ : syracuseStep 2230265 = 1672699) B1672699
theorem B82454545 : Blo 1486063 82454545 := bstep (se 2 (by rfl) ⟨30920454, by rfl⟩ : syracuseStep 82454545 = 61840909) B61840909
theorem B2230367 : Blo 1486063 2230367 := bstep (se 1 (by rfl) ⟨1672775, by rfl⟩ : syracuseStep 2230367 = 3345551) B3345551
theorem B1673311 : Blo 1486063 1673311 := bstep (se 1 (by rfl) ⟨1254983, by rfl⟩ : syracuseStep 1673311 = 2509967) B2509967
theorem B8038547 : Blo 1486063 8038547 := bstep (se 1 (by rfl) ⟨6028910, by rfl⟩ : syracuseStep 8038547 = 12057821) B12057821
theorem B2230427 : Blo 1486063 2230427 := bstep (se 1 (by rfl) ⟨1672820, by rfl⟩ : syracuseStep 2230427 = 3345641) B3345641
theorem B27510961 : Blo 1486063 27510961 := bstep (se 2 (by rfl) ⟨10316610, by rfl⟩ : syracuseStep 27510961 = 20633221) B20633221
theorem B2230463 : Blo 1486063 2230463 := bstep (se 1 (by rfl) ⟨1672847, by rfl⟩ : syracuseStep 2230463 = 3345695) B3345695
theorem B17180867 : Blo 1486063 17180867 := bstep (se 1 (by rfl) ⟨12885650, by rfl⟩ : syracuseStep 17180867 = 25771301) B25771301
theorem B2230505 : Blo 1486063 2230505 := bstep (se 2 (by rfl) ⟨836439, by rfl⟩ : syracuseStep 2230505 = 1672879) B1672879
theorem B3344633 : Blo 1486063 3344633 := bstep (se 2 (by rfl) ⟨1254237, by rfl⟩ : syracuseStep 3344633 = 2508475) B2508475
theorem B10447127 : Blo 1486063 10447127 := bstep (se 1 (by rfl) ⟨7835345, by rfl⟩ : syracuseStep 10447127 = 15670691) B15670691
theorem B3344687 : Blo 1486063 3344687 := bstep (se 1 (by rfl) ⟨2508515, by rfl⟩ : syracuseStep 3344687 = 5017031) B5017031
theorem B2509103 : Blo 1486063 2509103 := bstep (se 1 (by rfl) ⟨1881827, by rfl⟩ : syracuseStep 2509103 = 3763655) B3763655
theorem B3762571 : Blo 1486063 3762571 := bstep (se 1 (by rfl) ⟨2821928, by rfl⟩ : syracuseStep 3762571 = 5643857) B5643857
theorem B3344903 : Blo 1486063 3344903 := bstep (se 1 (by rfl) ⟨2508677, by rfl⟩ : syracuseStep 3344903 = 5017355) B5017355
theorem B2509339 : Blo 1486063 2509339 := bstep (se 1 (by rfl) ⟨1882004, by rfl⟩ : syracuseStep 2509339 = 3764009) B3764009
theorem B2230811 : Blo 1486063 2230811 := bstep (se 1 (by rfl) ⟨1673108, by rfl⟩ : syracuseStep 2230811 = 3346217) B3346217
theorem B2230889 : Blo 1486063 2230889 := bstep (se 2 (by rfl) ⟨836583, by rfl⟩ : syracuseStep 2230889 = 1673167) B1673167
theorem B3762875 : Blo 1486063 3762875 := bstep (se 1 (by rfl) ⟨2822156, by rfl⟩ : syracuseStep 3762875 = 5644313) B5644313
theorem B3345083 : Blo 1486063 3345083 := bstep (se 1 (by rfl) ⟨2508812, by rfl⟩ : syracuseStep 3345083 = 5017625) B5017625
theorem B18082835 : Blo 1486063 18082835 := bstep (se 1 (by rfl) ⟨13562126, by rfl⟩ : syracuseStep 18082835 = 27124253) B27124253
theorem B2231417 : Blo 1486063 2231417 := bstep (se 2 (by rfl) ⟨836781, by rfl⟩ : syracuseStep 2231417 = 1673563) B1673563
theorem B10456253 : Blo 1486063 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B2231519 : Blo 1486063 2231519 := bstep (se 1 (by rfl) ⟨1673639, by rfl⟩ : syracuseStep 2231519 = 3347279) B3347279
theorem B2231561 : Blo 1486063 2231561 := bstep (se 2 (by rfl) ⟨836835, by rfl⟩ : syracuseStep 2231561 = 1673671) B1673671
theorem B2231663 : Blo 1486063 2231663 := bstep (se 1 (by rfl) ⟨1673747, by rfl⟩ : syracuseStep 2231663 = 3347495) B3347495
theorem B1486311 : Blo 1486063 1486311 := bstep (se 1 (by rfl) ⟨1114733, by rfl⟩ : syracuseStep 1486311 = 2229467) B2229467
theorem B2510311 : Blo 1486063 2510311 := bstep (se 1 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 2510311 = 3765467) B3765467
theorem B2231783 : Blo 1486063 2231783 := bstep (se 1 (by rfl) ⟨1673837, by rfl⟩ : syracuseStep 2231783 = 3347675) B3347675
theorem B3345911 : Blo 1486063 3345911 := bstep (se 1 (by rfl) ⟨2509433, by rfl⟩ : syracuseStep 3345911 = 5018867) B5018867
theorem B3345983 : Blo 1486063 3345983 := bstep (se 1 (by rfl) ⟨2509487, by rfl⟩ : syracuseStep 3345983 = 5018975) B5018975
theorem B2510399 : Blo 1486063 2510399 := bstep (se 1 (by rfl) ⟨1882799, by rfl⟩ : syracuseStep 2510399 = 3765599) B3765599
theorem B1486427 : Blo 1486063 1486427 := bstep (se 1 (by rfl) ⟨1114820, by rfl⟩ : syracuseStep 1486427 = 2229641) B2229641
theorem B2231915 : Blo 1486063 2231915 := bstep (se 1 (by rfl) ⟨1673936, by rfl⟩ : syracuseStep 2231915 = 3347873) B3347873
theorem B2821807 : Blo 1486063 2821807 := bstep (se 1 (by rfl) ⟨2116355, by rfl⟩ : syracuseStep 2821807 = 4232711) B4232711
theorem B2232041 : Blo 1486063 2232041 := bstep (se 2 (by rfl) ⟨837015, by rfl⟩ : syracuseStep 2232041 = 1674031) B1674031
theorem B1486663 : Blo 1486063 1486663 := bstep (se 1 (by rfl) ⟨1114997, by rfl⟩ : syracuseStep 1486663 = 2229995) B2229995
theorem B8474489 : Blo 1486063 8474489 := bstep (se 2 (by rfl) ⟨3177933, by rfl⟩ : syracuseStep 8474489 = 6355867) B6355867
theorem B32157647 : Blo 1486063 32157647 := bstep (se 1 (by rfl) ⟨24118235, by rfl⟩ : syracuseStep 32157647 = 48236471) B48236471
theorem B25391069 : Blo 1486063 25391069 := bstep (se 3 (by rfl) ⟨4760825, by rfl⟩ : syracuseStep 25391069 = 9521651) B9521651
theorem B2822111 : Blo 1486063 2822111 := bstep (se 1 (by rfl) ⟨2116583, by rfl⟩ : syracuseStep 2822111 = 4233167) B4233167
theorem B1486815 : Blo 1486063 1486815 := bstep (se 1 (by rfl) ⟨1115111, by rfl⟩ : syracuseStep 1486815 = 2230223) B2230223
theorem B3764191 : Blo 1486063 3764191 := bstep (se 1 (by rfl) ⟨2823143, by rfl⟩ : syracuseStep 3764191 = 5646287) B5646287
theorem B5017787 : Blo 1486063 5017787 := bstep (se 1 (by rfl) ⟨3763340, by rfl⟩ : syracuseStep 5017787 = 7526681) B7526681
theorem B2511067 : Blo 1486063 2511067 := bstep (se 1 (by rfl) ⟨1883300, by rfl⟩ : syracuseStep 2511067 = 3766601) B3766601
theorem B1487079 : Blo 1486063 1487079 := bstep (se 1 (by rfl) ⟨1115309, by rfl⟩ : syracuseStep 1487079 = 2230619) B2230619
theorem B1487231 : Blo 1486063 1487231 := bstep (se 1 (by rfl) ⟨1115423, by rfl⟩ : syracuseStep 1487231 = 2230847) B2230847
theorem B122065355 : Blo 1486063 122065355 := bstep (se 1 (by rfl) ⟨91549016, by rfl⟩ : syracuseStep 122065355 = 183098033) B183098033
theorem B1487311 : Blo 1486063 1487311 := bstep (se 1 (by rfl) ⟨1115483, by rfl⟩ : syracuseStep 1487311 = 2230967) B2230967
theorem B3346937 : Blo 1486063 3346937 := bstep (se 2 (by rfl) ⟨1255101, by rfl⟩ : syracuseStep 3346937 = 2510203) B2510203
theorem B9654785 : Blo 1486063 9654785 := bstep (se 2 (by rfl) ⟨3620544, by rfl⟩ : syracuseStep 9654785 = 7241089) B7241089
theorem B19321415 : Blo 1486063 19321415 := bstep (se 1 (by rfl) ⟨14491061, by rfl⟩ : syracuseStep 19321415 = 28982123) B28982123
theorem B3764819 : Blo 1486063 3764819 := bstep (se 1 (by rfl) ⟨2823614, by rfl⟩ : syracuseStep 3764819 = 5647229) B5647229
theorem B3347027 : Blo 1486063 3347027 := bstep (se 1 (by rfl) ⟨2510270, by rfl⟩ : syracuseStep 3347027 = 5020541) B5020541
theorem B3764839 : Blo 1486063 3764839 := bstep (se 1 (by rfl) ⟨2823629, by rfl⟩ : syracuseStep 3764839 = 5647259) B5647259
theorem B1487463 : Blo 1486063 1487463 := bstep (se 1 (by rfl) ⟨1115597, by rfl⟩ : syracuseStep 1487463 = 2231195) B2231195
theorem B72323725 : Blo 1486063 72323725 := bstep (se 3 (by rfl) ⟨13560698, by rfl⟩ : syracuseStep 72323725 = 27121397) B27121397
theorem B5018273 : Blo 1486063 5018273 := bstep (se 2 (by rfl) ⟨1881852, by rfl⟩ : syracuseStep 5018273 = 3763705) B3763705
theorem B3175175 : Blo 1486063 3175175 := bstep (se 1 (by rfl) ⟨2381381, by rfl⟩ : syracuseStep 3175175 = 4762763) B4762763
theorem B3347207 : Blo 1486063 3347207 := bstep (se 1 (by rfl) ⟨2510405, by rfl⟩ : syracuseStep 3347207 = 5020811) B5020811
theorem B1487727 : Blo 1486063 1487727 := bstep (se 1 (by rfl) ⟨1115795, by rfl⟩ : syracuseStep 1487727 = 2231591) B2231591
theorem B1487783 : Blo 1486063 1487783 := bstep (se 1 (by rfl) ⟨1115837, by rfl⟩ : syracuseStep 1487783 = 2231675) B2231675
theorem B1881083 : Blo 1486063 1881083 := bstep (se 1 (by rfl) ⟨1410812, by rfl⟩ : syracuseStep 1881083 = 2821625) B2821625
theorem B1487867 : Blo 1486063 1487867 := bstep (se 1 (by rfl) ⟨1115900, by rfl⟩ : syracuseStep 1487867 = 2231801) B2231801
theorem B7525385 : Blo 1486063 7525385 := bstep (se 2 (by rfl) ⟨2822019, by rfl⟩ : syracuseStep 7525385 = 5644039) B5644039
theorem B1487935 : Blo 1486063 1487935 := bstep (se 1 (by rfl) ⟨1115951, by rfl⟩ : syracuseStep 1487935 = 2231903) B2231903
theorem B8467699 : Blo 1486063 8467699 := bstep (se 1 (by rfl) ⟨6350774, by rfl⟩ : syracuseStep 8467699 = 12701549) B12701549
theorem B9532723 : Blo 1486063 9532723 := bstep (se 1 (by rfl) ⟨7149542, by rfl⟩ : syracuseStep 9532723 = 14299085) B14299085
theorem B5019137 : Blo 1486063 5019137 := bstep (se 2 (by rfl) ⟨1882176, by rfl⟩ : syracuseStep 5019137 = 3764353) B3764353
theorem B10589753 : Blo 1486063 10589753 := bstep (se 2 (by rfl) ⟨3971157, by rfl⟩ : syracuseStep 10589753 = 7942315) B7942315
theorem B2823751 : Blo 1486063 2823751 := bstep (se 1 (by rfl) ⟨2117813, by rfl⟩ : syracuseStep 2823751 = 4235627) B4235627
theorem B2414191 : Blo 1486063 2414191 := bstep (se 1 (by rfl) ⟨1810643, by rfl⟩ : syracuseStep 2414191 = 3621287) B3621287
theorem B11286377 : Blo 1486063 11286377 := bstep (se 2 (by rfl) ⟨4232391, by rfl⟩ : syracuseStep 11286377 = 8464783) B8464783
theorem B1882055 : Blo 1486063 1882055 := bstep (se 1 (by rfl) ⟨1411541, by rfl⟩ : syracuseStep 1882055 = 2823083) B2823083
theorem B5019623 : Blo 1486063 5019623 := bstep (se 1 (by rfl) ⟨3764717, by rfl⟩ : syracuseStep 5019623 = 7529435) B7529435
theorem B3766247 : Blo 1486063 3766247 := bstep (se 1 (by rfl) ⟨2824685, by rfl⟩ : syracuseStep 3766247 = 5649371) B5649371
theorem B7247855 : Blo 1486063 7247855 := bstep (se 1 (by rfl) ⟨5435891, by rfl⟩ : syracuseStep 7247855 = 10871783) B10871783
theorem B5019731 : Blo 1486063 5019731 := bstep (se 1 (by rfl) ⟨3764798, by rfl⟩ : syracuseStep 5019731 = 7529597) B7529597
theorem B1882207 : Blo 1486063 1882207 := bstep (se 1 (by rfl) ⟨1411655, by rfl⟩ : syracuseStep 1882207 = 2823311) B2823311
theorem B3389537 : Blo 1486063 3389537 := bstep (se 2 (by rfl) ⟨1271076, by rfl⟩ : syracuseStep 3389537 = 2542153) B2542153
theorem B7141547 : Blo 1486063 7141547 := bstep (se 1 (by rfl) ⟨5356160, by rfl⟩ : syracuseStep 7141547 = 10712321) B10712321
theorem B5019947 : Blo 1486063 5019947 := bstep (se 1 (by rfl) ⟨3764960, by rfl⟩ : syracuseStep 5019947 = 7529921) B7529921
theorem B2824571 : Blo 1486063 2824571 := bstep (se 1 (by rfl) ⟨2118428, by rfl⟩ : syracuseStep 2824571 = 4236857) B4236857
theorem B5020217 : Blo 1486063 5020217 := bstep (se 2 (by rfl) ⟨1882581, by rfl⟩ : syracuseStep 5020217 = 3765163) B3765163
theorem B10173151 : Blo 1486063 10173151 := bstep (se 1 (by rfl) ⟨7629863, by rfl⟩ : syracuseStep 10173151 = 15259727) B15259727
theorem B4831967 : Blo 1486063 4831967 := bstep (se 1 (by rfl) ⟨3623975, by rfl⟩ : syracuseStep 4831967 = 7247951) B7247951
theorem B11320087 : Blo 1486063 11320087 := bstep (se 1 (by rfl) ⟨8490065, by rfl⟩ : syracuseStep 11320087 = 16980131) B16980131
theorem B38132531 : Blo 1486063 38132531 := bstep (se 1 (by rfl) ⟨28599398, by rfl⟩ : syracuseStep 38132531 = 57198797) B57198797
theorem B20339693 : Blo 1486063 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B17161283 : Blo 1486063 17161283 := bstep (se 1 (by rfl) ⟨12870962, by rfl⟩ : syracuseStep 17161283 = 25741925) B25741925
theorem B11296583 : Blo 1486063 11296583 := bstep (se 1 (by rfl) ⟨8472437, by rfl⟩ : syracuseStep 11296583 = 16944875) B16944875
theorem B3022715 : Blo 1486063 3022715 := bstep (se 1 (by rfl) ⟨2267036, by rfl⟩ : syracuseStep 3022715 = 4534073) B4534073
theorem B3572255 : Blo 1486063 3572255 := bstep (se 1 (by rfl) ⟨2679191, by rfl⟩ : syracuseStep 3572255 = 5358383) B5358383
theorem B2229191 : Blo 1486063 2229191 := bstep (se 1 (by rfl) ⟨1671893, by rfl⟩ : syracuseStep 2229191 = 3343787) B3343787
theorem B7242767 : Blo 1486063 7242767 := bstep (se 1 (by rfl) ⟨5432075, by rfl⟩ : syracuseStep 7242767 = 10864151) B10864151
theorem B2229359 : Blo 1486063 2229359 := bstep (se 1 (by rfl) ⟨1672019, by rfl⟩ : syracuseStep 2229359 = 3344039) B3344039
theorem B1672303 : Blo 1486063 1672303 := bstep (se 1 (by rfl) ⟨1254227, by rfl⟩ : syracuseStep 1672303 = 2508455) B2508455
theorem B86918275 : Blo 1486063 86918275 := bstep (se 1 (by rfl) ⟨65188706, by rfl⟩ : syracuseStep 86918275 = 130377413) B130377413
theorem B13567123 : Blo 1486063 13567123 := bstep (se 1 (by rfl) ⟨10175342, by rfl⟩ : syracuseStep 13567123 = 20350685) B20350685
theorem B54256805 : Blo 1486063 54256805 := bstep (se 4 (by rfl) ⟨5086575, by rfl⟩ : syracuseStep 54256805 = 10173151) B10173151
theorem B3572927 : Blo 1486063 3572927 := bstep (se 1 (by rfl) ⟨2679695, by rfl⟩ : syracuseStep 3572927 = 5359391) B5359391
theorem B7242959 : Blo 1486063 7242959 := bstep (se 1 (by rfl) ⟨5432219, by rfl⟩ : syracuseStep 7242959 = 10864439) B10864439
theorem B2147563 : Blo 1486063 2147563 := bstep (se 1 (by rfl) ⟨1610672, by rfl⟩ : syracuseStep 2147563 = 3221345) B3221345
theorem B2229551 : Blo 1486063 2229551 := bstep (se 1 (by rfl) ⟨1672163, by rfl⟩ : syracuseStep 2229551 = 3344327) B3344327
theorem B5359031 : Blo 1486063 5359031 := bstep (se 1 (by rfl) ⟨4019273, by rfl⟩ : syracuseStep 5359031 = 8038547) B8038547
theorem B4761031 : Blo 1486063 4761031 := bstep (se 1 (by rfl) ⟨3570773, by rfl⟩ : syracuseStep 4761031 = 7141547) B7141547
theorem B3343841 : Blo 1486063 3343841 := bstep (se 2 (by rfl) ⟨1253940, by rfl⟩ : syracuseStep 3343841 = 2507881) B2507881
theorem B2229755 : Blo 1486063 2229755 := bstep (se 1 (by rfl) ⟨1672316, by rfl⟩ : syracuseStep 2229755 = 3344633) B3344633
theorem B6964751 : Blo 1486063 6964751 := bstep (se 1 (by rfl) ⟨5223563, by rfl⟩ : syracuseStep 6964751 = 10447127) B10447127
theorem B2229791 : Blo 1486063 2229791 := bstep (se 1 (by rfl) ⟨1672343, by rfl⟩ : syracuseStep 2229791 = 3344687) B3344687
theorem B1672735 : Blo 1486063 1672735 := bstep (se 1 (by rfl) ⟨1254551, by rfl⟩ : syracuseStep 1672735 = 2509103) B2509103
theorem B11290265 : Blo 1486063 11290265 := bstep (se 2 (by rfl) ⟨4233849, by rfl⟩ : syracuseStep 11290265 = 8467699) B8467699
theorem B2229935 : Blo 1486063 2229935 := bstep (se 1 (by rfl) ⟨1672451, by rfl⟩ : syracuseStep 2229935 = 3344903) B3344903
theorem B2508583 : Blo 1486063 2508583 := bstep (se 1 (by rfl) ⟨1881437, by rfl⟩ : syracuseStep 2508583 = 3762875) B3762875
theorem B2230055 : Blo 1486063 2230055 := bstep (se 1 (by rfl) ⟨1672541, by rfl⟩ : syracuseStep 2230055 = 3345083) B3345083
theorem B3221311 : Blo 1486063 3221311 := bstep (se 1 (by rfl) ⟨2415983, by rfl⟩ : syracuseStep 3221311 = 4831967) B4831967
theorem B25421687 : Blo 1486063 25421687 := bstep (se 1 (by rfl) ⟨19066265, by rfl⟩ : syracuseStep 25421687 = 38132531) B38132531
theorem B13559795 : Blo 1486063 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B3762409 : Blo 1486063 3762409 := bstep (se 2 (by rfl) ⟨1410903, by rfl⟩ : syracuseStep 3762409 = 2821807) B2821807
theorem B2230607 : Blo 1486063 2230607 := bstep (se 1 (by rfl) ⟨1672955, by rfl⟩ : syracuseStep 2230607 = 3345911) B3345911
theorem B2230655 : Blo 1486063 2230655 := bstep (se 1 (by rfl) ⟨1672991, by rfl⟩ : syracuseStep 2230655 = 3345983) B3345983
theorem B1673599 : Blo 1486063 1673599 := bstep (se 1 (by rfl) ⟨1255199, by rfl⟩ : syracuseStep 1673599 = 2510399) B2510399
theorem B2230697 : Blo 1486063 2230697 := bstep (se 2 (by rfl) ⟨836511, by rfl⟩ : syracuseStep 2230697 = 1673023) B1673023
theorem B7531055 : Blo 1486063 7531055 := bstep (se 1 (by rfl) ⟨5648291, by rfl⟩ : syracuseStep 7531055 = 11296583) B11296583
theorem B16927379 : Blo 1486063 16927379 := bstep (se 1 (by rfl) ⟨12695534, by rfl⟩ : syracuseStep 16927379 = 25391069) B25391069
theorem B5016221 : Blo 1486063 5016221 := bstep (se 3 (by rfl) ⟨940541, by rfl⟩ : syracuseStep 5016221 = 1881083) B1881083
theorem B109939393 : Blo 1486063 109939393 := bstep (se 2 (by rfl) ⟨41227272, by rfl⟩ : syracuseStep 109939393 = 82454545) B82454545
theorem B3345191 : Blo 1486063 3345191 := bstep (se 1 (by rfl) ⟨2508893, by rfl⟩ : syracuseStep 3345191 = 5017787) B5017787
theorem B2509609 : Blo 1486063 2509609 := bstep (se 2 (by rfl) ⟨941103, by rfl⟩ : syracuseStep 2509609 = 1882207) B1882207
theorem B2231081 : Blo 1486063 2231081 := bstep (se 2 (by rfl) ⟨836655, by rfl⟩ : syracuseStep 2231081 = 1673311) B1673311
theorem B9038765 : Blo 1486063 9038765 := bstep (se 3 (by rfl) ⟨1694768, by rfl⟩ : syracuseStep 9038765 = 3389537) B3389537
theorem B2231291 : Blo 1486063 2231291 := bstep (se 1 (by rfl) ⟨1673468, by rfl⟩ : syracuseStep 2231291 = 3346937) B3346937
theorem B12880943 : Blo 1486063 12880943 := bstep (se 1 (by rfl) ⟨9660707, by rfl⟩ : syracuseStep 12880943 = 19321415) B19321415
theorem B2509879 : Blo 1486063 2509879 := bstep (se 1 (by rfl) ⟨1882409, by rfl⟩ : syracuseStep 2509879 = 3764819) B3764819
theorem B2231351 : Blo 1486063 2231351 := bstep (se 1 (by rfl) ⟨1673513, by rfl⟩ : syracuseStep 2231351 = 3347027) B3347027
theorem B3345515 : Blo 1486063 3345515 := bstep (se 1 (by rfl) ⟨2509136, by rfl⟩ : syracuseStep 3345515 = 5018273) B5018273
theorem B14298241 : Blo 1486063 14298241 := bstep (se 2 (by rfl) ⟨5361840, by rfl⟩ : syracuseStep 14298241 = 10723681) B10723681
theorem B2116783 : Blo 1486063 2116783 := bstep (se 1 (by rfl) ⟨1587587, by rfl⟩ : syracuseStep 2116783 = 3175175) B3175175
theorem B2231471 : Blo 1486063 2231471 := bstep (se 1 (by rfl) ⟨1673603, by rfl⟩ : syracuseStep 2231471 = 3347207) B3347207
theorem B7531703 : Blo 1486063 7531703 := bstep (se 1 (by rfl) ⟨5648777, by rfl⟩ : syracuseStep 7531703 = 11297555) B11297555
theorem B5016761 : Blo 1486063 5016761 := bstep (se 2 (by rfl) ⟨1881285, by rfl⟩ : syracuseStep 5016761 = 3762571) B3762571
theorem B10169543 : Blo 1486063 10169543 := bstep (se 1 (by rfl) ⟨7627157, by rfl⟩ : syracuseStep 10169543 = 15254315) B15254315
theorem B5016923 : Blo 1486063 5016923 := bstep (se 1 (by rfl) ⟨3762692, by rfl⟩ : syracuseStep 5016923 = 7525385) B7525385
theorem B3345785 : Blo 1486063 3345785 := bstep (se 2 (by rfl) ⟨1254669, by rfl⟩ : syracuseStep 3345785 = 2509339) B2509339
theorem B1486207 : Blo 1486063 1486207 := bstep (se 1 (by rfl) ⟨1114655, by rfl⟩ : syracuseStep 1486207 = 2229311) B2229311
theorem B1486235 : Blo 1486063 1486235 := bstep (se 1 (by rfl) ⟨1114676, by rfl⟩ : syracuseStep 1486235 = 2229353) B2229353
theorem B1486303 : Blo 1486063 1486303 := bstep (se 1 (by rfl) ⟨1114727, by rfl⟩ : syracuseStep 1486303 = 2229455) B2229455
theorem B96431633 : Blo 1486063 96431633 := bstep (se 2 (by rfl) ⟨36161862, by rfl⟩ : syracuseStep 96431633 = 72323725) B72323725
theorem B1486439 : Blo 1486063 1486439 := bstep (se 1 (by rfl) ⟨1114829, by rfl⟩ : syracuseStep 1486439 = 2229659) B2229659
theorem B7532189 : Blo 1486063 7532189 := bstep (se 3 (by rfl) ⟨1412285, by rfl⟩ : syracuseStep 7532189 = 2824571) B2824571
theorem B3346091 : Blo 1486063 3346091 := bstep (se 1 (by rfl) ⟨2509568, by rfl⟩ : syracuseStep 3346091 = 5019137) B5019137
theorem B15093449 : Blo 1486063 15093449 := bstep (se 2 (by rfl) ⟨5660043, by rfl⟩ : syracuseStep 15093449 = 11320087) B11320087
theorem B9531083 : Blo 1486063 9531083 := bstep (se 1 (by rfl) ⟨7148312, by rfl⟩ : syracuseStep 9531083 = 14296625) B14296625
theorem B1486587 : Blo 1486063 1486587 := bstep (se 1 (by rfl) ⟨1114940, by rfl⟩ : syracuseStep 1486587 = 2229881) B2229881
theorem B1486655 : Blo 1486063 1486655 := bstep (se 1 (by rfl) ⟨1114991, by rfl⟩ : syracuseStep 1486655 = 2229983) B2229983
theorem B1486719 : Blo 1486063 1486719 := bstep (se 1 (by rfl) ⟨1115039, by rfl⟩ : syracuseStep 1486719 = 2230079) B2230079
theorem B7524251 : Blo 1486063 7524251 := bstep (se 1 (by rfl) ⟨5643188, by rfl⟩ : syracuseStep 7524251 = 11286377) B11286377
theorem B1486831 : Blo 1486063 1486831 := bstep (se 1 (by rfl) ⟨1115123, by rfl⟩ : syracuseStep 1486831 = 2230247) B2230247
theorem B3346415 : Blo 1486063 3346415 := bstep (se 1 (by rfl) ⟨2509811, by rfl⟩ : syracuseStep 3346415 = 5019623) B5019623
theorem B2510831 : Blo 1486063 2510831 := bstep (se 1 (by rfl) ⟨1883123, by rfl⟩ : syracuseStep 2510831 = 3766247) B3766247
theorem B1486843 : Blo 1486063 1486843 := bstep (se 1 (by rfl) ⟨1115132, by rfl⟩ : syracuseStep 1486843 = 2230265) B2230265
theorem B3346487 : Blo 1486063 3346487 := bstep (se 1 (by rfl) ⟨2509865, by rfl⟩ : syracuseStep 3346487 = 5019731) B5019731
theorem B1486911 : Blo 1486063 1486911 := bstep (se 1 (by rfl) ⟨1115183, by rfl⟩ : syracuseStep 1486911 = 2230367) B2230367
theorem B1486951 : Blo 1486063 1486951 := bstep (se 1 (by rfl) ⟨1115213, by rfl⟩ : syracuseStep 1486951 = 2230427) B2230427
theorem B1486975 : Blo 1486063 1486975 := bstep (se 1 (by rfl) ⟨1115231, by rfl⟩ : syracuseStep 1486975 = 2230463) B2230463
theorem B1487003 : Blo 1486063 1487003 := bstep (se 1 (by rfl) ⟨1115252, by rfl⟩ : syracuseStep 1487003 = 2230505) B2230505
theorem B3346631 : Blo 1486063 3346631 := bstep (se 1 (by rfl) ⟨2509973, by rfl⟩ : syracuseStep 3346631 = 5019947) B5019947
theorem B13570301 : Blo 1486063 13570301 := bstep (se 3 (by rfl) ⟨2544431, by rfl⟩ : syracuseStep 13570301 = 5088863) B5088863
theorem B1487207 : Blo 1486063 1487207 := bstep (se 1 (by rfl) ⟨1115405, by rfl⟩ : syracuseStep 1487207 = 2230811) B2230811
theorem B3346811 : Blo 1486063 3346811 := bstep (se 1 (by rfl) ⟨2510108, by rfl⟩ : syracuseStep 3346811 = 5020217) B5020217
theorem B12710297 : Blo 1486063 12710297 := bstep (se 2 (by rfl) ⟨4766361, by rfl⟩ : syracuseStep 12710297 = 9532723) B9532723
theorem B1487259 : Blo 1486063 1487259 := bstep (se 1 (by rfl) ⟨1115444, by rfl⟩ : syracuseStep 1487259 = 2230889) B2230889
theorem B3347081 : Blo 1486063 3347081 := bstep (se 2 (by rfl) ⟨1255155, by rfl⟩ : syracuseStep 3347081 = 2510311) B2510311
theorem B12055223 : Blo 1486063 12055223 := bstep (se 1 (by rfl) ⟨9041417, by rfl⟩ : syracuseStep 12055223 = 18082835) B18082835
theorem B11440855 : Blo 1486063 11440855 := bstep (se 1 (by rfl) ⟨8580641, by rfl⟩ : syracuseStep 11440855 = 17161283) B17161283
theorem B1487611 : Blo 1486063 1487611 := bstep (se 1 (by rfl) ⟨1115708, by rfl⟩ : syracuseStep 1487611 = 2231417) B2231417
theorem B3765001 : Blo 1486063 3765001 := bstep (se 2 (by rfl) ⟨1411875, by rfl⟩ : syracuseStep 3765001 = 2823751) B2823751
theorem B1487679 : Blo 1486063 1487679 := bstep (se 1 (by rfl) ⟨1115759, by rfl⟩ : syracuseStep 1487679 = 2231519) B2231519
theorem B1487707 : Blo 1486063 1487707 := bstep (se 1 (by rfl) ⟨1115780, by rfl⟩ : syracuseStep 1487707 = 2231561) B2231561
theorem B1487775 : Blo 1486063 1487775 := bstep (se 1 (by rfl) ⟨1115831, by rfl⟩ : syracuseStep 1487775 = 2231663) B2231663
theorem B1487855 : Blo 1486063 1487855 := bstep (se 1 (by rfl) ⟨1115891, by rfl⟩ : syracuseStep 1487855 = 2231783) B2231783
theorem B1487943 : Blo 1486063 1487943 := bstep (se 1 (by rfl) ⟨1115957, by rfl⟩ : syracuseStep 1487943 = 2231915) B2231915
theorem B1488027 : Blo 1486063 1488027 := bstep (se 1 (by rfl) ⟨1116020, by rfl⟩ : syracuseStep 1488027 = 2232041) B2232041
theorem B5018813 : Blo 1486063 5018813 := bstep (se 3 (by rfl) ⟨941027, by rfl⟩ : syracuseStep 5018813 = 1882055) B1882055
theorem B5649659 : Blo 1486063 5649659 := bstep (se 1 (by rfl) ⟨4237244, by rfl⟩ : syracuseStep 5649659 = 8474489) B8474489
theorem B5018921 : Blo 1486063 5018921 := bstep (se 2 (by rfl) ⟨1882095, by rfl⟩ : syracuseStep 5018921 = 3764191) B3764191
theorem B1881407 : Blo 1486063 1881407 := bstep (se 1 (by rfl) ⟨1411055, by rfl⟩ : syracuseStep 1881407 = 2822111) B2822111
theorem B3347819 : Blo 1486063 3347819 := bstep (se 1 (by rfl) ⟨2510864, by rfl⟩ : syracuseStep 3347819 = 5021729) B5021729
theorem B5363081 : Blo 1486063 5363081 := bstep (se 2 (by rfl) ⟨2011155, by rfl⟩ : syracuseStep 5363081 = 4022311) B4022311
theorem B7525871 : Blo 1486063 7525871 := bstep (se 1 (by rfl) ⟨5644403, by rfl⟩ : syracuseStep 7525871 = 11288807) B11288807
theorem B36681281 : Blo 1486063 36681281 := bstep (se 2 (by rfl) ⟨13755480, by rfl⟩ : syracuseStep 36681281 = 27510961) B27510961
theorem B3348089 : Blo 1486063 3348089 := bstep (se 2 (by rfl) ⟨1255533, by rfl⟩ : syracuseStep 3348089 = 2511067) B2511067
theorem B81376903 : Blo 1486063 81376903 := bstep (se 1 (by rfl) ⟨61032677, by rfl⟩ : syracuseStep 81376903 = 122065355) B122065355
theorem B2823835 : Blo 1486063 2823835 := bstep (se 1 (by rfl) ⟨2117876, by rfl⟩ : syracuseStep 2823835 = 4235753) B4235753
theorem B6436523 : Blo 1486063 6436523 := bstep (se 1 (by rfl) ⟨4827392, by rfl⟩ : syracuseStep 6436523 = 9654785) B9654785
theorem B45815645 : Blo 1486063 45815645 := bstep (se 3 (by rfl) ⟨8590433, by rfl⟩ : syracuseStep 45815645 = 17180867) B17180867
theorem B5019515 : Blo 1486063 5019515 := bstep (se 1 (by rfl) ⟨3764636, by rfl⟩ : syracuseStep 5019515 = 7529273) B7529273
theorem B5019785 : Blo 1486063 5019785 := bstep (se 2 (by rfl) ⟨1882419, by rfl⟩ : syracuseStep 5019785 = 3764839) B3764839
theorem B7059835 : Blo 1486063 7059835 := bstep (se 1 (by rfl) ⟨5294876, by rfl⟩ : syracuseStep 7059835 = 10589753) B10589753
theorem B4831903 : Blo 1486063 4831903 := bstep (se 1 (by rfl) ⟨3623927, by rfl⟩ : syracuseStep 4831903 = 7247855) B7247855
theorem B11451269 : Blo 1486063 11451269 := bstep (se 4 (by rfl) ⟨1073556, by rfl⟩ : syracuseStep 11451269 = 2147113) B2147113
theorem B6970835 : Blo 1486063 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B3218921 : Blo 1486063 3218921 := bstep (se 2 (by rfl) ⟨1207095, by rfl⟩ : syracuseStep 3218921 = 2414191) B2414191
theorem B2015143 : Blo 1486063 2015143 := bstep (se 1 (by rfl) ⟨1511357, by rfl⟩ : syracuseStep 2015143 = 3022715) B3022715
theorem B21438431 : Blo 1486063 21438431 := bstep (se 1 (by rfl) ⟨16078823, by rfl⟩ : syracuseStep 21438431 = 32157647) B32157647
theorem B8036815 : Blo 1486063 8036815 := bstep (se 1 (by rfl) ⟨6027611, by rfl⟩ : syracuseStep 8036815 = 12055223) B12055223
theorem B3572687 : Blo 1486063 3572687 := bstep (se 1 (by rfl) ⟨2679515, by rfl⟩ : syracuseStep 3572687 = 5359031) B5359031
theorem B2229227 : Blo 1486063 2229227 := bstep (se 1 (by rfl) ⟨1671920, by rfl⟩ : syracuseStep 2229227 = 3343841) B3343841
theorem B24454187 : Blo 1486063 24454187 := bstep (se 1 (by rfl) ⟨18340640, by rfl⟩ : syracuseStep 24454187 = 36681281) B36681281
theorem B11453669 : Blo 1486063 11453669 := bstep (se 4 (by rfl) ⟨1073781, by rfl⟩ : syracuseStep 11453669 = 2147563) B2147563
theorem B2229737 : Blo 1486063 2229737 := bstep (se 2 (by rfl) ⟨836151, by rfl⟩ : syracuseStep 2229737 = 1672303) B1672303
theorem B19064321 : Blo 1486063 19064321 := bstep (se 2 (by rfl) ⟨7149120, by rfl⟩ : syracuseStep 19064321 = 14298241) B14298241
theorem B18089497 : Blo 1486063 18089497 := bstep (se 2 (by rfl) ⟨6783561, by rfl⟩ : syracuseStep 18089497 = 13567123) B13567123
theorem B3344147 : Blo 1486063 3344147 := bstep (se 1 (by rfl) ⟨2508110, by rfl⟩ : syracuseStep 3344147 = 5016221) B5016221
theorem B17164061 : Blo 1486063 17164061 := bstep (se 3 (by rfl) ⟨3218261, by rfl⟩ : syracuseStep 17164061 = 6436523) B6436523
theorem B2230127 : Blo 1486063 2230127 := bstep (se 1 (by rfl) ⟨1672595, by rfl⟩ : syracuseStep 2230127 = 3345191) B3345191
theorem B37652453 : Blo 1486063 37652453 := bstep (se 4 (by rfl) ⟨3529917, by rfl⟩ : syracuseStep 37652453 = 7059835) B7059835
theorem B8587295 : Blo 1486063 8587295 := bstep (se 1 (by rfl) ⟨6440471, by rfl⟩ : syracuseStep 8587295 = 12880943) B12880943
theorem B2230313 : Blo 1486063 2230313 := bstep (se 2 (by rfl) ⟨836367, by rfl⟩ : syracuseStep 2230313 = 1672735) B1672735
theorem B2230343 : Blo 1486063 2230343 := bstep (se 1 (by rfl) ⟨1672757, by rfl⟩ : syracuseStep 2230343 = 3345515) B3345515
theorem B3344507 : Blo 1486063 3344507 := bstep (se 1 (by rfl) ⟨2508380, by rfl⟩ : syracuseStep 3344507 = 5016761) B5016761
theorem B3344615 : Blo 1486063 3344615 := bstep (se 1 (by rfl) ⟨2508461, by rfl⟩ : syracuseStep 3344615 = 5016923) B5016923
theorem B2230523 : Blo 1486063 2230523 := bstep (se 1 (by rfl) ⟨1672892, by rfl⟩ : syracuseStep 2230523 = 3345785) B3345785
theorem B4647223 : Blo 1486063 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B3344777 : Blo 1486063 3344777 := bstep (se 2 (by rfl) ⟨1254291, by rfl⟩ : syracuseStep 3344777 = 2508583) B2508583
theorem B4295081 : Blo 1486063 4295081 := bstep (se 2 (by rfl) ⟨1610655, by rfl⟩ : syracuseStep 4295081 = 3221311) B3221311
theorem B2230727 : Blo 1486063 2230727 := bstep (se 1 (by rfl) ⟨1673045, by rfl⟩ : syracuseStep 2230727 = 3346091) B3346091
theorem B10062299 : Blo 1486063 10062299 := bstep (se 1 (by rfl) ⟨7546724, by rfl⟩ : syracuseStep 10062299 = 15093449) B15093449
theorem B5016167 : Blo 1486063 5016167 := bstep (se 1 (by rfl) ⟨3762125, by rfl⟩ : syracuseStep 5016167 = 7524251) B7524251
theorem B2230943 : Blo 1486063 2230943 := bstep (se 1 (by rfl) ⟨1673207, by rfl⟩ : syracuseStep 2230943 = 3346415) B3346415
theorem B1673887 : Blo 1486063 1673887 := bstep (se 1 (by rfl) ⟨1255415, by rfl⟩ : syracuseStep 1673887 = 2510831) B2510831
theorem B2230991 : Blo 1486063 2230991 := bstep (se 1 (by rfl) ⟨1673243, by rfl⟩ : syracuseStep 2230991 = 3346487) B3346487
theorem B2231087 : Blo 1486063 2231087 := bstep (se 1 (by rfl) ⟨1673315, by rfl⟩ : syracuseStep 2231087 = 3346631) B3346631
theorem B2231207 : Blo 1486063 2231207 := bstep (se 1 (by rfl) ⟨1673405, by rfl⟩ : syracuseStep 2231207 = 3346811) B3346811
theorem B8473531 : Blo 1486063 8473531 := bstep (se 1 (by rfl) ⟨6355148, by rfl⟩ : syracuseStep 8473531 = 12710297) B12710297
theorem B5016545 : Blo 1486063 5016545 := bstep (se 2 (by rfl) ⟨1881204, by rfl⟩ : syracuseStep 5016545 = 3762409) B3762409
theorem B2231387 : Blo 1486063 2231387 := bstep (se 1 (by rfl) ⟨1673540, by rfl⟩ : syracuseStep 2231387 = 3347081) B3347081
theorem B2231465 : Blo 1486063 2231465 := bstep (se 2 (by rfl) ⟨836799, by rfl⟩ : syracuseStep 2231465 = 1673599) B1673599
theorem B1486127 : Blo 1486063 1486127 := bstep (se 1 (by rfl) ⟨1114595, by rfl⟩ : syracuseStep 1486127 = 2229191) B2229191
theorem B36187469 : Blo 1486063 36187469 := bstep (se 3 (by rfl) ⟨6785150, by rfl⟩ : syracuseStep 36187469 = 13570301) B13570301
theorem B4828511 : Blo 1486063 4828511 := bstep (se 1 (by rfl) ⟨3621383, by rfl⟩ : syracuseStep 4828511 = 7242767) B7242767
theorem B1486239 : Blo 1486063 1486239 := bstep (se 1 (by rfl) ⟨1114679, by rfl⟩ : syracuseStep 1486239 = 2229359) B2229359
theorem B36171203 : Blo 1486063 36171203 := bstep (se 1 (by rfl) ⟨27128402, by rfl⟩ : syracuseStep 36171203 = 54256805) B54256805
theorem B3345875 : Blo 1486063 3345875 := bstep (se 1 (by rfl) ⟨2509406, by rfl⟩ : syracuseStep 3345875 = 5018813) B5018813
theorem B4828639 : Blo 1486063 4828639 := bstep (se 1 (by rfl) ⟨3621479, by rfl⟩ : syracuseStep 4828639 = 7242959) B7242959
theorem B5017085 : Blo 1486063 5017085 := bstep (se 3 (by rfl) ⟨940703, by rfl⟩ : syracuseStep 5017085 = 1881407) B1881407
theorem B3345947 : Blo 1486063 3345947 := bstep (se 1 (by rfl) ⟨2509460, by rfl⟩ : syracuseStep 3345947 = 5018921) B5018921
theorem B1486367 : Blo 1486063 1486367 := bstep (se 1 (by rfl) ⟨1114775, by rfl⟩ : syracuseStep 1486367 = 2229551) B2229551
theorem B6442537 : Blo 1486063 6442537 := bstep (se 2 (by rfl) ⟨2415951, by rfl⟩ : syracuseStep 6442537 = 4831903) B4831903
theorem B2231879 : Blo 1486063 2231879 := bstep (se 1 (by rfl) ⟨1673909, by rfl⟩ : syracuseStep 2231879 = 3347819) B3347819
theorem B3575387 : Blo 1486063 3575387 := bstep (se 1 (by rfl) ⟨2681540, by rfl⟩ : syracuseStep 3575387 = 5363081) B5363081
theorem B5017247 : Blo 1486063 5017247 := bstep (se 1 (by rfl) ⟨3762935, by rfl⟩ : syracuseStep 5017247 = 7525871) B7525871
theorem B1486503 : Blo 1486063 1486503 := bstep (se 1 (by rfl) ⟨1114877, by rfl⟩ : syracuseStep 1486503 = 2229755) B2229755
theorem B1486527 : Blo 1486063 1486527 := bstep (se 1 (by rfl) ⟨1114895, by rfl⟩ : syracuseStep 1486527 = 2229791) B2229791
theorem B3346145 : Blo 1486063 3346145 := bstep (se 2 (by rfl) ⟨1254804, by rfl⟩ : syracuseStep 3346145 = 2509609) B2509609
theorem B2232059 : Blo 1486063 2232059 := bstep (se 1 (by rfl) ⟨1674044, by rfl⟩ : syracuseStep 2232059 = 3348089) B3348089
theorem B1486623 : Blo 1486063 1486623 := bstep (se 1 (by rfl) ⟨1114967, by rfl⟩ : syracuseStep 1486623 = 2229935) B2229935
theorem B61017893 : Blo 1486063 61017893 := bstep (se 4 (by rfl) ⟨5720427, by rfl⟩ : syracuseStep 61017893 = 11440855) B11440855
theorem B1486703 : Blo 1486063 1486703 := bstep (se 1 (by rfl) ⟨1115027, by rfl⟩ : syracuseStep 1486703 = 2230055) B2230055
theorem B30543763 : Blo 1486063 30543763 := bstep (se 1 (by rfl) ⟨22907822, by rfl⟩ : syracuseStep 30543763 = 45815645) B45815645
theorem B3346343 : Blo 1486063 3346343 := bstep (se 1 (by rfl) ⟨2509757, by rfl⟩ : syracuseStep 3346343 = 5019515) B5019515
theorem B9039863 : Blo 1486063 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B3346505 : Blo 1486063 3346505 := bstep (se 2 (by rfl) ⟨1254939, by rfl⟩ : syracuseStep 3346505 = 2509879) B2509879
theorem B3346523 : Blo 1486063 3346523 := bstep (se 1 (by rfl) ⟨2509892, by rfl⟩ : syracuseStep 3346523 = 5019785) B5019785
theorem B1487071 : Blo 1486063 1487071 := bstep (se 1 (by rfl) ⟨1115303, by rfl⟩ : syracuseStep 1487071 = 2230607) B2230607
theorem B2822377 : Blo 1486063 2822377 := bstep (se 2 (by rfl) ⟨1058391, by rfl⟩ : syracuseStep 2822377 = 2116783) B2116783
theorem B1487103 : Blo 1486063 1487103 := bstep (se 1 (by rfl) ⟨1115327, by rfl⟩ : syracuseStep 1487103 = 2230655) B2230655
theorem B1487131 : Blo 1486063 1487131 := bstep (se 1 (by rfl) ⟨1115348, by rfl⟩ : syracuseStep 1487131 = 2230697) B2230697
theorem B11284919 : Blo 1486063 11284919 := bstep (se 1 (by rfl) ⟨8463689, by rfl⟩ : syracuseStep 11284919 = 16927379) B16927379
theorem B1487387 : Blo 1486063 1487387 := bstep (se 1 (by rfl) ⟨1115540, by rfl⟩ : syracuseStep 1487387 = 2231081) B2231081
theorem B6025843 : Blo 1486063 6025843 := bstep (se 1 (by rfl) ⟨4519382, by rfl⟩ : syracuseStep 6025843 = 9038765) B9038765
theorem B1487527 : Blo 1486063 1487527 := bstep (se 1 (by rfl) ⟨1115645, by rfl⟩ : syracuseStep 1487527 = 2231291) B2231291
theorem B1487567 : Blo 1486063 1487567 := bstep (se 1 (by rfl) ⟨1115675, by rfl⟩ : syracuseStep 1487567 = 2231351) B2231351
theorem B1487647 : Blo 1486063 1487647 := bstep (se 1 (by rfl) ⟨1115735, by rfl⟩ : syracuseStep 1487647 = 2231471) B2231471
theorem B6779695 : Blo 1486063 6779695 := bstep (se 1 (by rfl) ⟨5084771, by rfl⟩ : syracuseStep 6779695 = 10169543) B10169543
theorem B3765113 : Blo 1486063 3765113 := bstep (se 2 (by rfl) ⟨1411917, by rfl⟩ : syracuseStep 3765113 = 2823835) B2823835
theorem B64287755 : Blo 1486063 64287755 := bstep (se 1 (by rfl) ⟨48215816, by rfl⟩ : syracuseStep 64287755 = 96431633) B96431633
theorem B6354055 : Blo 1486063 6354055 := bstep (se 1 (by rfl) ⟨4765541, by rfl⟩ : syracuseStep 6354055 = 9531083) B9531083
theorem B14292287 : Blo 1486063 14292287 := bstep (se 1 (by rfl) ⟨10719215, by rfl⟩ : syracuseStep 14292287 = 21438431) B21438431
theorem B2381503 : Blo 1486063 2381503 := bstep (se 1 (by rfl) ⟨1786127, by rfl⟩ : syracuseStep 2381503 = 3572255) B3572255
theorem B2381951 : Blo 1486063 2381951 := bstep (se 1 (by rfl) ⟨1786463, by rfl⟩ : syracuseStep 2381951 = 3572927) B3572927
theorem B3766439 : Blo 1486063 3766439 := bstep (se 1 (by rfl) ⟨2824829, by rfl⟩ : syracuseStep 3766439 = 5649659) B5649659
theorem B146585857 : Blo 1486063 146585857 := bstep (se 2 (by rfl) ⟨54969696, by rfl⟩ : syracuseStep 146585857 = 109939393) B109939393
theorem B4643167 : Blo 1486063 4643167 := bstep (se 1 (by rfl) ⟨3482375, by rfl⟩ : syracuseStep 4643167 = 6964751) B6964751
theorem B5020001 : Blo 1486063 5020001 := bstep (se 2 (by rfl) ⟨1882500, by rfl⟩ : syracuseStep 5020001 = 3765001) B3765001
theorem B7526843 : Blo 1486063 7526843 := bstep (se 1 (by rfl) ⟨5645132, by rfl⟩ : syracuseStep 7526843 = 11290265) B11290265
theorem B16947791 : Blo 1486063 16947791 := bstep (se 1 (by rfl) ⟨12710843, by rfl⟩ : syracuseStep 16947791 = 25421687) B25421687
theorem B115891033 : Blo 1486063 115891033 := bstep (se 2 (by rfl) ⟨43459137, by rfl⟩ : syracuseStep 115891033 = 86918275) B86918275
theorem B5020703 : Blo 1486063 5020703 := bstep (se 1 (by rfl) ⟨3765527, by rfl⟩ : syracuseStep 5020703 = 7531055) B7531055
theorem B7634179 : Blo 1486063 7634179 := bstep (se 1 (by rfl) ⟨5725634, by rfl⟩ : syracuseStep 7634179 = 11451269) B11451269
theorem B6348041 : Blo 1486063 6348041 := bstep (se 2 (by rfl) ⟨2380515, by rfl⟩ : syracuseStep 6348041 = 4761031) B4761031
theorem B5021135 : Blo 1486063 5021135 := bstep (se 1 (by rfl) ⟨3765851, by rfl⟩ : syracuseStep 5021135 = 7531703) B7531703
theorem B108502537 : Blo 1486063 108502537 := bstep (se 2 (by rfl) ⟨40688451, by rfl⟩ : syracuseStep 108502537 = 81376903) B81376903
theorem B10747429 : Blo 1486063 10747429 := bstep (se 4 (by rfl) ⟨1007571, by rfl⟩ : syracuseStep 10747429 = 2015143) B2015143
theorem B2145947 : Blo 1486063 2145947 := bstep (se 1 (by rfl) ⟨1609460, by rfl⟩ : syracuseStep 2145947 = 3218921) B3218921
theorem B5021459 : Blo 1486063 5021459 := bstep (se 1 (by rfl) ⟨3766094, by rfl⟩ : syracuseStep 5021459 = 7532189) B7532189
theorem B32137829 : Blo 1486063 32137829 := bstep (se 4 (by rfl) ⟨3012921, by rfl⟩ : syracuseStep 32137829 = 6025843) B6025843
theorem B10715753 : Blo 1486063 10715753 := bstep (se 2 (by rfl) ⟨4018407, by rfl⟩ : syracuseStep 10715753 = 8036815) B8036815
theorem B16302791 : Blo 1486063 16302791 := bstep (se 1 (by rfl) ⟨12227093, by rfl⟩ : syracuseStep 16302791 = 24454187) B24454187
theorem B229278485 : Blo 1486063 229278485 := bstep (se 6 (by rfl) ⟨5373714, by rfl⟩ : syracuseStep 229278485 = 10747429) B10747429
theorem B7635779 : Blo 1486063 7635779 := bstep (se 1 (by rfl) ⟨5726834, by rfl⟩ : syracuseStep 7635779 = 11453669) B11453669
theorem B9528191 : Blo 1486063 9528191 := bstep (se 1 (by rfl) ⟨7146143, by rfl⟩ : syracuseStep 9528191 = 14292287) B14292287
theorem B2229431 : Blo 1486063 2229431 := bstep (se 1 (by rfl) ⟨1672073, by rfl⟩ : syracuseStep 2229431 = 3344147) B3344147
theorem B11298041 : Blo 1486063 11298041 := bstep (se 2 (by rfl) ⟨4236765, by rfl⟩ : syracuseStep 11298041 = 8473531) B8473531
theorem B25101635 : Blo 1486063 25101635 := bstep (se 1 (by rfl) ⟨18826226, by rfl⟩ : syracuseStep 25101635 = 37652453) B37652453
theorem B40715621 : Blo 1486063 40715621 := bstep (se 4 (by rfl) ⟨3817089, by rfl⟩ : syracuseStep 40715621 = 7634179) B7634179
theorem B2229671 : Blo 1486063 2229671 := bstep (se 1 (by rfl) ⟨1672253, by rfl⟩ : syracuseStep 2229671 = 3344507) B3344507
theorem B2229743 : Blo 1486063 2229743 := bstep (se 1 (by rfl) ⟨1672307, by rfl⟩ : syracuseStep 2229743 = 3344615) B3344615
theorem B8472073 : Blo 1486063 8472073 := bstep (se 2 (by rfl) ⟨3177027, by rfl⟩ : syracuseStep 8472073 = 6354055) B6354055
theorem B2229851 : Blo 1486063 2229851 := bstep (se 1 (by rfl) ⟨1672388, by rfl⟩ : syracuseStep 2229851 = 3344777) B3344777
theorem B11298527 : Blo 1486063 11298527 := bstep (se 1 (by rfl) ⟨8473895, by rfl⟩ : syracuseStep 11298527 = 16947791) B16947791
theorem B3344111 : Blo 1486063 3344111 := bstep (se 1 (by rfl) ⟨2508083, by rfl⟩ : syracuseStep 3344111 = 5016167) B5016167
theorem B3344363 : Blo 1486063 3344363 := bstep (se 1 (by rfl) ⟨2508272, by rfl⟩ : syracuseStep 3344363 = 5016545) B5016545
theorem B24119329 : Blo 1486063 24119329 := bstep (se 2 (by rfl) ⟨9044748, by rfl⟩ : syracuseStep 24119329 = 18089497) B18089497
theorem B2230583 : Blo 1486063 2230583 := bstep (se 1 (by rfl) ⟨1672937, by rfl⟩ : syracuseStep 2230583 = 3345875) B3345875
theorem B3344723 : Blo 1486063 3344723 := bstep (se 1 (by rfl) ⟨2508542, by rfl⟩ : syracuseStep 3344723 = 5017085) B5017085
theorem B2230631 : Blo 1486063 2230631 := bstep (se 1 (by rfl) ⟨1672973, by rfl⟩ : syracuseStep 2230631 = 3345947) B3345947
theorem B3344831 : Blo 1486063 3344831 := bstep (se 1 (by rfl) ⟨2508623, by rfl⟩ : syracuseStep 3344831 = 5017247) B5017247
theorem B2230763 : Blo 1486063 2230763 := bstep (se 1 (by rfl) ⟨1673072, by rfl⟩ : syracuseStep 2230763 = 3346145) B3346145
theorem B40725017 : Blo 1486063 40725017 := bstep (se 2 (by rfl) ⟨15271881, by rfl⟩ : syracuseStep 40725017 = 30543763) B30543763
theorem B2230895 : Blo 1486063 2230895 := bstep (se 1 (by rfl) ⟨1673171, by rfl⟩ : syracuseStep 2230895 = 3346343) B3346343
theorem B2231003 : Blo 1486063 2231003 := bstep (se 1 (by rfl) ⟨1673252, by rfl⟩ : syracuseStep 2231003 = 3346505) B3346505
theorem B2231015 : Blo 1486063 2231015 := bstep (se 1 (by rfl) ⟨1673261, by rfl⟩ : syracuseStep 2231015 = 3346523) B3346523
theorem B7523279 : Blo 1486063 7523279 := bstep (se 1 (by rfl) ⟨5642459, by rfl⟩ : syracuseStep 7523279 = 11284919) B11284919
theorem B3763169 : Blo 1486063 3763169 := bstep (se 2 (by rfl) ⟨1411188, by rfl⟩ : syracuseStep 3763169 = 2822377) B2822377
theorem B195447809 : Blo 1486063 195447809 := bstep (se 2 (by rfl) ⟨73292928, by rfl⟩ : syracuseStep 195447809 = 146585857) B146585857
theorem B2510075 : Blo 1486063 2510075 := bstep (se 1 (by rfl) ⟨1882556, by rfl⟩ : syracuseStep 2510075 = 3765113) B3765113
theorem B1486151 : Blo 1486063 1486151 := bstep (se 1 (by rfl) ⟨1114613, by rfl⟩ : syracuseStep 1486151 = 2229227) B2229227
theorem B2231849 : Blo 1486063 2231849 := bstep (se 2 (by rfl) ⟨836943, by rfl⟩ : syracuseStep 2231849 = 1673887) B1673887
theorem B1486491 : Blo 1486063 1486491 := bstep (se 1 (by rfl) ⟨1114868, by rfl⟩ : syracuseStep 1486491 = 2229737) B2229737
theorem B12709547 : Blo 1486063 12709547 := bstep (se 1 (by rfl) ⟨9532160, by rfl⟩ : syracuseStep 12709547 = 19064321) B19064321
theorem B9039593 : Blo 1486063 9039593 := bstep (se 2 (by rfl) ⟨3389847, by rfl⟩ : syracuseStep 9039593 = 6779695) B6779695
theorem B154521377 : Blo 1486063 154521377 := bstep (se 2 (by rfl) ⟨57945516, by rfl⟩ : syracuseStep 154521377 = 115891033) B115891033
theorem B96456541 : Blo 1486063 96456541 := bstep (se 3 (by rfl) ⟨18085601, by rfl⟩ : syracuseStep 96456541 = 36171203) B36171203
theorem B1486751 : Blo 1486063 1486751 := bstep (se 1 (by rfl) ⟨1115063, by rfl⟩ : syracuseStep 1486751 = 2230127) B2230127
theorem B1486875 : Blo 1486063 1486875 := bstep (se 1 (by rfl) ⟨1115156, by rfl⟩ : syracuseStep 1486875 = 2230313) B2230313
theorem B1486895 : Blo 1486063 1486895 := bstep (se 1 (by rfl) ⟨1115171, by rfl⟩ : syracuseStep 1486895 = 2230343) B2230343
theorem B2510959 : Blo 1486063 2510959 := bstep (se 1 (by rfl) ⟨1883219, by rfl⟩ : syracuseStep 2510959 = 3766439) B3766439
theorem B1487015 : Blo 1486063 1487015 := bstep (se 1 (by rfl) ⟨1115261, by rfl⟩ : syracuseStep 1487015 = 2230523) B2230523
theorem B3346667 : Blo 1486063 3346667 := bstep (se 1 (by rfl) ⟨2510000, by rfl⟩ : syracuseStep 3346667 = 5020001) B5020001
theorem B2863387 : Blo 1486063 2863387 := bstep (se 1 (by rfl) ⟨2147540, by rfl⟩ : syracuseStep 2863387 = 4295081) B4295081
theorem B24785189 : Blo 1486063 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B5017895 : Blo 1486063 5017895 := bstep (se 1 (by rfl) ⟨3763421, by rfl⟩ : syracuseStep 5017895 = 7526843) B7526843
theorem B1487151 : Blo 1486063 1487151 := bstep (se 1 (by rfl) ⟨1115363, by rfl⟩ : syracuseStep 1487151 = 2230727) B2230727
theorem B5722525 : Blo 1486063 5722525 := bstep (se 3 (by rfl) ⟨1072973, by rfl⟩ : syracuseStep 5722525 = 2145947) B2145947
theorem B1487295 : Blo 1486063 1487295 := bstep (se 1 (by rfl) ⟨1115471, by rfl⟩ : syracuseStep 1487295 = 2230943) B2230943
theorem B1487327 : Blo 1486063 1487327 := bstep (se 1 (by rfl) ⟨1115495, by rfl⟩ : syracuseStep 1487327 = 2230991) B2230991
theorem B1487391 : Blo 1486063 1487391 := bstep (se 1 (by rfl) ⟨1115543, by rfl⟩ : syracuseStep 1487391 = 2231087) B2231087
theorem B1487471 : Blo 1486063 1487471 := bstep (se 1 (by rfl) ⟨1115603, by rfl⟩ : syracuseStep 1487471 = 2231207) B2231207
theorem B3347135 : Blo 1486063 3347135 := bstep (se 1 (by rfl) ⟨2510351, by rfl⟩ : syracuseStep 3347135 = 5020703) B5020703
theorem B8590049 : Blo 1486063 8590049 := bstep (se 2 (by rfl) ⟨3221268, by rfl⟩ : syracuseStep 8590049 = 6442537) B6442537
theorem B1487591 : Blo 1486063 1487591 := bstep (se 1 (by rfl) ⟨1115693, by rfl⟩ : syracuseStep 1487591 = 2231387) B2231387
theorem B1487643 : Blo 1486063 1487643 := bstep (se 1 (by rfl) ⟨1115732, by rfl⟩ : syracuseStep 1487643 = 2231465) B2231465
theorem B4232027 : Blo 1486063 4232027 := bstep (se 1 (by rfl) ⟨3174020, by rfl⟩ : syracuseStep 4232027 = 6348041) B6348041
theorem B3175337 : Blo 1486063 3175337 := bstep (se 2 (by rfl) ⟨1190751, by rfl⟩ : syracuseStep 3175337 = 2381503) B2381503
theorem B3347423 : Blo 1486063 3347423 := bstep (se 1 (by rfl) ⟨2510567, by rfl⟩ : syracuseStep 3347423 = 5021135) B5021135
theorem B1487919 : Blo 1486063 1487919 := bstep (se 1 (by rfl) ⟨1115939, by rfl⟩ : syracuseStep 1487919 = 2231879) B2231879
theorem B1488039 : Blo 1486063 1488039 := bstep (se 1 (by rfl) ⟨1116029, by rfl⟩ : syracuseStep 1488039 = 2232059) B2232059
theorem B3347639 : Blo 1486063 3347639 := bstep (se 1 (by rfl) ⟨2510729, by rfl⟩ : syracuseStep 3347639 = 5021459) B5021459
theorem B40678595 : Blo 1486063 40678595 := bstep (se 1 (by rfl) ⟨30508946, by rfl⟩ : syracuseStep 40678595 = 61017893) B61017893
theorem B6026575 : Blo 1486063 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B6190889 : Blo 1486063 6190889 := bstep (se 2 (by rfl) ⟨2321583, by rfl⟩ : syracuseStep 6190889 = 4643167) B4643167
theorem B42858503 : Blo 1486063 42858503 := bstep (se 1 (by rfl) ⟨32143877, by rfl⟩ : syracuseStep 42858503 = 64287755) B64287755
theorem B12876029 : Blo 1486063 12876029 := bstep (se 3 (by rfl) ⟨2414255, by rfl⟩ : syracuseStep 12876029 = 4828511) B4828511
theorem B11442707 : Blo 1486063 11442707 := bstep (se 1 (by rfl) ⟨8582030, by rfl⟩ : syracuseStep 11442707 = 17164061) B17164061
theorem B5724863 : Blo 1486063 5724863 := bstep (se 1 (by rfl) ⟨4293647, by rfl⟩ : syracuseStep 5724863 = 8587295) B8587295
theorem B1587967 : Blo 1486063 1587967 := bstep (se 1 (by rfl) ⟨1190975, by rfl⟩ : syracuseStep 1587967 = 2381951) B2381951
theorem B6708199 : Blo 1486063 6708199 := bstep (se 1 (by rfl) ⟨5031149, by rfl⟩ : syracuseStep 6708199 = 10062299) B10062299
theorem B6438185 : Blo 1486063 6438185 := bstep (se 2 (by rfl) ⟨2414319, by rfl⟩ : syracuseStep 6438185 = 4828639) B4828639
theorem B144670049 : Blo 1486063 144670049 := bstep (se 2 (by rfl) ⟨54251268, by rfl⟩ : syracuseStep 144670049 = 108502537) B108502537
theorem B24124979 : Blo 1486063 24124979 := bstep (se 1 (by rfl) ⟨18093734, by rfl⟩ : syracuseStep 24124979 = 36187469) B36187469
theorem B2383591 : Blo 1486063 2383591 := bstep (se 1 (by rfl) ⟨1787693, by rfl⟩ : syracuseStep 2383591 = 3575387) B3575387
theorem B9527165 : Blo 1486063 9527165 := bstep (se 3 (by rfl) ⟨1786343, by rfl⟩ : syracuseStep 9527165 = 3572687) B3572687
theorem B16523459 : Blo 1486063 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B3817849 : Blo 1486063 3817849 := bstep (se 2 (by rfl) ⟨1431693, by rfl⟩ : syracuseStep 3817849 = 2863387) B2863387
theorem B5726699 : Blo 1486063 5726699 := bstep (se 1 (by rfl) ⟨4295024, by rfl⟩ : syracuseStep 5726699 = 8590049) B8590049
theorem B66937693 : Blo 1486063 66937693 := bstep (se 3 (by rfl) ⟨12550817, by rfl⟩ : syracuseStep 66937693 = 25101635) B25101635
theorem B2229407 : Blo 1486063 2229407 := bstep (se 1 (by rfl) ⟨1672055, by rfl⟩ : syracuseStep 2229407 = 3344111) B3344111
theorem B2229575 : Blo 1486063 2229575 := bstep (se 1 (by rfl) ⟨1672181, by rfl⟩ : syracuseStep 2229575 = 3344363) B3344363
theorem B2229815 : Blo 1486063 2229815 := bstep (se 1 (by rfl) ⟨1672361, by rfl⟩ : syracuseStep 2229815 = 3344723) B3344723
theorem B28575341 : Blo 1486063 28575341 := bstep (se 3 (by rfl) ⟨5357876, by rfl⟩ : syracuseStep 28575341 = 10715753) B10715753
theorem B2229887 : Blo 1486063 2229887 := bstep (se 1 (by rfl) ⟨1672415, by rfl⟩ : syracuseStep 2229887 = 3344831) B3344831
theorem B7628471 : Blo 1486063 7628471 := bstep (se 1 (by rfl) ⟨5721353, by rfl⟩ : syracuseStep 7628471 = 11442707) B11442707
theorem B27150011 : Blo 1486063 27150011 := bstep (se 1 (by rfl) ⟨20362508, by rfl⟩ : syracuseStep 27150011 = 40725017) B40725017
theorem B5015519 : Blo 1486063 5015519 := bstep (se 1 (by rfl) ⟨3761639, by rfl⟩ : syracuseStep 5015519 = 7523279) B7523279
theorem B2508779 : Blo 1486063 2508779 := bstep (se 1 (by rfl) ⟨1881584, by rfl⟩ : syracuseStep 2508779 = 3763169) B3763169
theorem B16509037 : Blo 1486063 16509037 := bstep (se 3 (by rfl) ⟨3095444, by rfl⟩ : syracuseStep 16509037 = 6190889) B6190889
theorem B1673383 : Blo 1486063 1673383 := bstep (se 1 (by rfl) ⟨1255037, by rfl⟩ : syracuseStep 1673383 = 2510075) B2510075
theorem B96446699 : Blo 1486063 96446699 := bstep (se 1 (by rfl) ⟨72335024, by rfl⟩ : syracuseStep 96446699 = 144670049) B144670049
theorem B16083319 : Blo 1486063 16083319 := bstep (se 1 (by rfl) ⟨12062489, by rfl⟩ : syracuseStep 16083319 = 24124979) B24124979
theorem B8473031 : Blo 1486063 8473031 := bstep (se 1 (by rfl) ⟨6354773, by rfl⟩ : syracuseStep 8473031 = 12709547) B12709547
theorem B128608721 : Blo 1486063 128608721 := bstep (se 2 (by rfl) ⟨48228270, by rfl⟩ : syracuseStep 128608721 = 96456541) B96456541
theorem B6351443 : Blo 1486063 6351443 := bstep (se 1 (by rfl) ⟨4763582, by rfl⟩ : syracuseStep 6351443 = 9527165) B9527165
theorem B2231111 : Blo 1486063 2231111 := bstep (se 1 (by rfl) ⟨1673333, by rfl⟩ : syracuseStep 2231111 = 3346667) B3346667
theorem B3345263 : Blo 1486063 3345263 := bstep (se 1 (by rfl) ⟨2508947, by rfl⟩ : syracuseStep 3345263 = 5017895) B5017895
theorem B21425219 : Blo 1486063 21425219 := bstep (se 1 (by rfl) ⟨16068914, by rfl⟩ : syracuseStep 21425219 = 32137829) B32137829
theorem B2231423 : Blo 1486063 2231423 := bstep (se 1 (by rfl) ⟨1673567, by rfl⟩ : syracuseStep 2231423 = 3347135) B3347135
theorem B7630033 : Blo 1486063 7630033 := bstep (se 2 (by rfl) ⟨2861262, by rfl⟩ : syracuseStep 7630033 = 5722525) B5722525
theorem B5090519 : Blo 1486063 5090519 := bstep (se 1 (by rfl) ⟨3817889, by rfl⟩ : syracuseStep 5090519 = 7635779) B7635779
theorem B6352127 : Blo 1486063 6352127 := bstep (se 1 (by rfl) ⟨4764095, by rfl⟩ : syracuseStep 6352127 = 9528191) B9528191
theorem B2116891 : Blo 1486063 2116891 := bstep (se 1 (by rfl) ⟨1587668, by rfl⟩ : syracuseStep 2116891 = 3175337) B3175337
theorem B2231615 : Blo 1486063 2231615 := bstep (se 1 (by rfl) ⟨1673711, by rfl⟩ : syracuseStep 2231615 = 3347423) B3347423
theorem B1486287 : Blo 1486063 1486287 := bstep (se 1 (by rfl) ⟨1114715, by rfl⟩ : syracuseStep 1486287 = 2229431) B2229431
theorem B2231759 : Blo 1486063 2231759 := bstep (se 1 (by rfl) ⟨1673819, by rfl⟩ : syracuseStep 2231759 = 3347639) B3347639
theorem B27119063 : Blo 1486063 27119063 := bstep (se 1 (by rfl) ⟨20339297, by rfl⟩ : syracuseStep 27119063 = 40678595) B40678595
theorem B7532027 : Blo 1486063 7532027 := bstep (se 1 (by rfl) ⟨5649020, by rfl⟩ : syracuseStep 7532027 = 11298041) B11298041
theorem B27143747 : Blo 1486063 27143747 := bstep (se 1 (by rfl) ⟨20357810, by rfl⟩ : syracuseStep 27143747 = 40715621) B40715621
theorem B1486447 : Blo 1486063 1486447 := bstep (se 1 (by rfl) ⟨1114835, by rfl⟩ : syracuseStep 1486447 = 2229671) B2229671
theorem B1486495 : Blo 1486063 1486495 := bstep (se 1 (by rfl) ⟨1114871, by rfl⟩ : syracuseStep 1486495 = 2229743) B2229743
theorem B1486567 : Blo 1486063 1486567 := bstep (se 1 (by rfl) ⟨1114925, by rfl⟩ : syracuseStep 1486567 = 2229851) B2229851
theorem B7532351 : Blo 1486063 7532351 := bstep (se 1 (by rfl) ⟨5649263, by rfl⟩ : syracuseStep 7532351 = 11298527) B11298527
theorem B1487055 : Blo 1486063 1487055 := bstep (se 1 (by rfl) ⟨1115291, by rfl⟩ : syracuseStep 1487055 = 2230583) B2230583
theorem B1487087 : Blo 1486063 1487087 := bstep (se 1 (by rfl) ⟨1115315, by rfl⟩ : syracuseStep 1487087 = 2230631) B2230631
theorem B1487175 : Blo 1486063 1487175 := bstep (se 1 (by rfl) ⟨1115381, by rfl⟩ : syracuseStep 1487175 = 2230763) B2230763
theorem B1487263 : Blo 1486063 1487263 := bstep (se 1 (by rfl) ⟨1115447, by rfl⟩ : syracuseStep 1487263 = 2230895) B2230895
theorem B1487335 : Blo 1486063 1487335 := bstep (se 1 (by rfl) ⟨1115501, by rfl⟩ : syracuseStep 1487335 = 2231003) B2231003
theorem B1487343 : Blo 1486063 1487343 := bstep (se 1 (by rfl) ⟨1115507, by rfl⟩ : syracuseStep 1487343 = 2231015) B2231015
theorem B130298539 : Blo 1486063 130298539 := bstep (se 1 (by rfl) ⟨97723904, by rfl⟩ : syracuseStep 130298539 = 195447809) B195447809
theorem B11285405 : Blo 1486063 11285405 := bstep (se 3 (by rfl) ⟨2116013, by rfl⟩ : syracuseStep 11285405 = 4232027) B4232027
theorem B1487899 : Blo 1486063 1487899 := bstep (se 1 (by rfl) ⟨1115924, by rfl⟩ : syracuseStep 1487899 = 2231849) B2231849
theorem B6026395 : Blo 1486063 6026395 := bstep (se 1 (by rfl) ⟨4519796, by rfl⟩ : syracuseStep 6026395 = 9039593) B9039593
theorem B32159105 : Blo 1486063 32159105 := bstep (se 2 (by rfl) ⟨12059664, by rfl⟩ : syracuseStep 32159105 = 24119329) B24119329
theorem B3347945 : Blo 1486063 3347945 := bstep (se 2 (by rfl) ⟨1255479, by rfl⟩ : syracuseStep 3347945 = 2510959) B2510959
theorem B10868527 : Blo 1486063 10868527 := bstep (se 1 (by rfl) ⟨8151395, by rfl⟩ : syracuseStep 10868527 = 16302791) B16302791
theorem B8944265 : Blo 1486063 8944265 := bstep (se 2 (by rfl) ⟨3354099, by rfl⟩ : syracuseStep 8944265 = 6708199) B6708199
theorem B8469157 : Blo 1486063 8469157 := bstep (se 4 (by rfl) ⟨793983, by rfl⟩ : syracuseStep 8469157 = 1587967) B1587967
theorem B28572335 : Blo 1486063 28572335 := bstep (se 1 (by rfl) ⟨21429251, by rfl⟩ : syracuseStep 28572335 = 42858503) B42858503
theorem B8584019 : Blo 1486063 8584019 := bstep (se 1 (by rfl) ⟨6438014, by rfl⟩ : syracuseStep 8584019 = 12876029) B12876029
theorem B8035433 : Blo 1486063 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B3816575 : Blo 1486063 3816575 := bstep (se 1 (by rfl) ⟨2862431, by rfl⟩ : syracuseStep 3816575 = 5724863) B5724863
theorem B11296097 : Blo 1486063 11296097 := bstep (se 2 (by rfl) ⟨4236036, by rfl⟩ : syracuseStep 11296097 = 8472073) B8472073
theorem B611409293 : Blo 1486063 611409293 := bstep (se 3 (by rfl) ⟨114639242, by rfl⟩ : syracuseStep 611409293 = 229278485) B229278485
theorem B4292123 : Blo 1486063 4292123 := bstep (se 1 (by rfl) ⟨3219092, by rfl⟩ : syracuseStep 4292123 = 6438185) B6438185
theorem B3178121 : Blo 1486063 3178121 := bstep (se 2 (by rfl) ⟨1191795, by rfl⟩ : syracuseStep 3178121 = 2383591) B2383591
theorem B103014251 : Blo 1486063 103014251 := bstep (se 1 (by rfl) ⟨77260688, by rfl⟩ : syracuseStep 103014251 = 154521377) B154521377
theorem B3817799 : Blo 1486063 3817799 := bstep (se 1 (by rfl) ⟨2863349, by rfl⟩ : syracuseStep 3817799 = 5726699) B5726699
theorem B21439403 : Blo 1486063 21439403 := bstep (se 1 (by rfl) ⟨16079552, by rfl⟩ : syracuseStep 21439403 = 32159105) B32159105
theorem B3343679 : Blo 1486063 3343679 := bstep (se 1 (by rfl) ⟨2507759, by rfl⟩ : syracuseStep 3343679 = 5015519) B5015519
theorem B1672519 : Blo 1486063 1672519 := bstep (se 1 (by rfl) ⟨1254389, by rfl⟩ : syracuseStep 1672519 = 2508779) B2508779
theorem B11445661 : Blo 1486063 11445661 := bstep (se 3 (by rfl) ⟨2146061, by rfl⟩ : syracuseStep 11445661 = 4292123) B4292123
theorem B85739147 : Blo 1486063 85739147 := bstep (se 1 (by rfl) ⟨64304360, by rfl⟩ : syracuseStep 85739147 = 128608721) B128608721
theorem B19048223 : Blo 1486063 19048223 := bstep (se 1 (by rfl) ⟨14286167, by rfl⟩ : syracuseStep 19048223 = 28572335) B28572335
theorem B2230175 : Blo 1486063 2230175 := bstep (se 1 (by rfl) ⟨1672631, by rfl⟩ : syracuseStep 2230175 = 3345263) B3345263
theorem B3393679 : Blo 1486063 3393679 := bstep (se 1 (by rfl) ⟨2545259, by rfl⟩ : syracuseStep 3393679 = 5090519) B5090519
theorem B7530731 : Blo 1486063 7530731 := bstep (se 1 (by rfl) ⟨5648048, by rfl⟩ : syracuseStep 7530731 = 11296097) B11296097
theorem B352192789 : Blo 1486063 352192789 := bstep (se 6 (by rfl) ⟨8254518, by rfl⟩ : syracuseStep 352192789 = 16509037) B16509037
theorem B68676167 : Blo 1486063 68676167 := bstep (se 1 (by rfl) ⟨51507125, by rfl⟩ : syracuseStep 68676167 = 103014251) B103014251
theorem B2231177 : Blo 1486063 2231177 := bstep (se 2 (by rfl) ⟨836691, by rfl⟩ : syracuseStep 2231177 = 1673383) B1673383
theorem B5090465 : Blo 1486063 5090465 := bstep (se 2 (by rfl) ⟨1908924, by rfl⟩ : syracuseStep 5090465 = 3817849) B3817849
theorem B7523603 : Blo 1486063 7523603 := bstep (se 1 (by rfl) ⟨5642702, by rfl⟩ : syracuseStep 7523603 = 11285405) B11285405
theorem B1486271 : Blo 1486063 1486271 := bstep (se 1 (by rfl) ⟨1114703, by rfl⟩ : syracuseStep 1486271 = 2229407) B2229407
theorem B1486383 : Blo 1486063 1486383 := bstep (se 1 (by rfl) ⟨1114787, by rfl⟩ : syracuseStep 1486383 = 2229575) B2229575
theorem B11292209 : Blo 1486063 11292209 := bstep (se 2 (by rfl) ⟨4234578, by rfl⟩ : syracuseStep 11292209 = 8469157) B8469157
theorem B173731385 : Blo 1486063 173731385 := bstep (se 2 (by rfl) ⟨65149269, by rfl⟩ : syracuseStep 173731385 = 130298539) B130298539
theorem B2231963 : Blo 1486063 2231963 := bstep (se 1 (by rfl) ⟨1673972, by rfl⟩ : syracuseStep 2231963 = 3347945) B3347945
theorem B1486543 : Blo 1486063 1486543 := bstep (se 1 (by rfl) ⟨1114907, by rfl⟩ : syracuseStep 1486543 = 2229815) B2229815
theorem B19050227 : Blo 1486063 19050227 := bstep (se 1 (by rfl) ⟨14287670, by rfl⟩ : syracuseStep 19050227 = 28575341) B28575341
theorem B1486591 : Blo 1486063 1486591 := bstep (se 1 (by rfl) ⟨1114943, by rfl⟩ : syracuseStep 1486591 = 2229887) B2229887
theorem B18100007 : Blo 1486063 18100007 := bstep (se 1 (by rfl) ⟨13575005, by rfl⟩ : syracuseStep 18100007 = 27150011) B27150011
theorem B5648687 : Blo 1486063 5648687 := bstep (se 1 (by rfl) ⟨4236515, by rfl⟩ : syracuseStep 5648687 = 8473031) B8473031
theorem B8474989 : Blo 1486063 8474989 := bstep (se 3 (by rfl) ⟨1589060, by rfl⟩ : syracuseStep 8474989 = 3178121) B3178121
theorem B2822521 : Blo 1486063 2822521 := bstep (se 2 (by rfl) ⟨1058445, by rfl⟩ : syracuseStep 2822521 = 2116891) B2116891
theorem B1487407 : Blo 1486063 1487407 := bstep (se 1 (by rfl) ⟨1115555, by rfl⟩ : syracuseStep 1487407 = 2231111) B2231111
theorem B5722679 : Blo 1486063 5722679 := bstep (se 1 (by rfl) ⟨4292009, by rfl⟩ : syracuseStep 5722679 = 8584019) B8584019
theorem B14283479 : Blo 1486063 14283479 := bstep (se 1 (by rfl) ⟨10712609, by rfl⟩ : syracuseStep 14283479 = 21425219) B21425219
theorem B2544383 : Blo 1486063 2544383 := bstep (se 1 (by rfl) ⟨1908287, by rfl⟩ : syracuseStep 2544383 = 3816575) B3816575
theorem B1487615 : Blo 1486063 1487615 := bstep (se 1 (by rfl) ⟨1115711, by rfl⟩ : syracuseStep 1487615 = 2231423) B2231423
theorem B1487743 : Blo 1486063 1487743 := bstep (se 1 (by rfl) ⟨1115807, by rfl⟩ : syracuseStep 1487743 = 2231615) B2231615
theorem B407606195 : Blo 1486063 407606195 := bstep (se 1 (by rfl) ⟨305704646, by rfl⟩ : syracuseStep 407606195 = 611409293) B611409293
theorem B1487839 : Blo 1486063 1487839 := bstep (se 1 (by rfl) ⟨1115879, by rfl⟩ : syracuseStep 1487839 = 2231759) B2231759
theorem B11015639 : Blo 1486063 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B21444425 : Blo 1486063 21444425 := bstep (se 2 (by rfl) ⟨8041659, by rfl⟩ : syracuseStep 21444425 = 16083319) B16083319
theorem B5085647 : Blo 1486063 5085647 := bstep (se 1 (by rfl) ⟨3814235, by rfl⟩ : syracuseStep 5085647 = 7628471) B7628471
theorem B89250257 : Blo 1486063 89250257 := bstep (se 2 (by rfl) ⟨33468846, by rfl⟩ : syracuseStep 89250257 = 66937693) B66937693
theorem B64297799 : Blo 1486063 64297799 := bstep (se 1 (by rfl) ⟨48223349, by rfl⟩ : syracuseStep 64297799 = 96446699) B96446699
theorem B8035193 : Blo 1486063 8035193 := bstep (se 2 (by rfl) ⟨3013197, by rfl⟩ : syracuseStep 8035193 = 6026395) B6026395
theorem B10173377 : Blo 1486063 10173377 := bstep (se 2 (by rfl) ⟨3815016, by rfl⟩ : syracuseStep 10173377 = 7630033) B7630033
theorem B4234295 : Blo 1486063 4234295 := bstep (se 1 (by rfl) ⟨3175721, by rfl⟩ : syracuseStep 4234295 = 6351443) B6351443
theorem B5962843 : Blo 1486063 5962843 := bstep (se 1 (by rfl) ⟨4472132, by rfl⟩ : syracuseStep 5962843 = 8944265) B8944265
theorem B5356955 : Blo 1486063 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B4234751 : Blo 1486063 4234751 := bstep (se 1 (by rfl) ⟨3176063, by rfl⟩ : syracuseStep 4234751 = 6352127) B6352127
theorem B18079375 : Blo 1486063 18079375 := bstep (se 1 (by rfl) ⟨13559531, by rfl⟩ : syracuseStep 18079375 = 27119063) B27119063
theorem B5021351 : Blo 1486063 5021351 := bstep (se 1 (by rfl) ⟨3766013, by rfl⟩ : syracuseStep 5021351 = 7532027) B7532027
theorem B18095831 : Blo 1486063 18095831 := bstep (se 1 (by rfl) ⟨13571873, by rfl⟩ : syracuseStep 18095831 = 27143747) B27143747
theorem B14491369 : Blo 1486063 14491369 := bstep (se 2 (by rfl) ⟨5434263, by rfl⟩ : syracuseStep 14491369 = 10868527) B10868527
theorem B5021567 : Blo 1486063 5021567 := bstep (se 1 (by rfl) ⟨3766175, by rfl⟩ : syracuseStep 5021567 = 7532351) B7532351
theorem B469590385 : Blo 1486063 469590385 := bstep (se 2 (by rfl) ⟨176096394, by rfl⟩ : syracuseStep 469590385 = 352192789) B352192789
theorem B13574573 : Blo 1486063 13574573 := bstep (se 3 (by rfl) ⟨2545232, by rfl⟩ : syracuseStep 13574573 = 5090465) B5090465
theorem B2229119 : Blo 1486063 2229119 := bstep (se 1 (by rfl) ⟨1671839, by rfl⟩ : syracuseStep 2229119 = 3343679) B3343679
theorem B12698815 : Blo 1486063 12698815 := bstep (se 1 (by rfl) ⟨9524111, by rfl⟩ : syracuseStep 12698815 = 19048223) B19048223
theorem B14296283 : Blo 1486063 14296283 := bstep (se 1 (by rfl) ⟨10722212, by rfl⟩ : syracuseStep 14296283 = 21444425) B21444425
theorem B59500171 : Blo 1486063 59500171 := bstep (se 1 (by rfl) ⟨44625128, by rfl⟩ : syracuseStep 59500171 = 89250257) B89250257
theorem B2230025 : Blo 1486063 2230025 := bstep (se 2 (by rfl) ⟨836259, by rfl⟩ : syracuseStep 2230025 = 1672519) B1672519
theorem B6785021 : Blo 1486063 6785021 := bstep (se 3 (by rfl) ⟨1272191, by rfl⟩ : syracuseStep 6785021 = 2544383) B2544383
theorem B5015735 : Blo 1486063 5015735 := bstep (se 1 (by rfl) ⟨3761801, by rfl⟩ : syracuseStep 5015735 = 7523603) B7523603
theorem B115820923 : Blo 1486063 115820923 := bstep (se 1 (by rfl) ⟨86865692, by rfl⟩ : syracuseStep 115820923 = 173731385) B173731385
theorem B1086949853 : Blo 1486063 1086949853 := bstep (se 3 (by rfl) ⟨203803097, by rfl⟩ : syracuseStep 1086949853 = 407606195) B407606195
theorem B12700151 : Blo 1486063 12700151 := bstep (se 1 (by rfl) ⟨9525113, by rfl⟩ : syracuseStep 12700151 = 19050227) B19050227
theorem B4524905 : Blo 1486063 4524905 := bstep (se 2 (by rfl) ⟨1696839, by rfl⟩ : syracuseStep 4524905 = 3393679) B3393679
theorem B9522319 : Blo 1486063 9522319 := bstep (se 1 (by rfl) ⟨7141739, by rfl⟩ : syracuseStep 9522319 = 14283479) B14283479
theorem B11299985 : Blo 1486063 11299985 := bstep (se 2 (by rfl) ⟨4237494, by rfl⟩ : syracuseStep 11299985 = 8474989) B8474989
theorem B3763361 : Blo 1486063 3763361 := bstep (se 2 (by rfl) ⟨1411260, by rfl⟩ : syracuseStep 3763361 = 2822521) B2822521
theorem B7343759 : Blo 1486063 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B57159431 : Blo 1486063 57159431 := bstep (se 1 (by rfl) ⟨42869573, by rfl⟩ : syracuseStep 57159431 = 85739147) B85739147
theorem B1486783 : Blo 1486063 1486783 := bstep (se 1 (by rfl) ⟨1115087, by rfl⟩ : syracuseStep 1486783 = 2230175) B2230175
theorem B7950457 : Blo 1486063 7950457 := bstep (se 2 (by rfl) ⟨2981421, by rfl⟩ : syracuseStep 7950457 = 5962843) B5962843
theorem B42865199 : Blo 1486063 42865199 := bstep (se 1 (by rfl) ⟨32148899, by rfl⟩ : syracuseStep 42865199 = 64297799) B64297799
theorem B1487451 : Blo 1486063 1487451 := bstep (se 1 (by rfl) ⟨1115588, by rfl⟩ : syracuseStep 1487451 = 2231177) B2231177
theorem B2822863 : Blo 1486063 2822863 := bstep (se 1 (by rfl) ⟨2117147, by rfl⟩ : syracuseStep 2822863 = 4234295) B4234295
theorem B24105833 : Blo 1486063 24105833 := bstep (se 2 (by rfl) ⟨9039687, by rfl⟩ : syracuseStep 24105833 = 18079375) B18079375
theorem B19321825 : Blo 1486063 19321825 := bstep (se 2 (by rfl) ⟨7245684, by rfl⟩ : syracuseStep 19321825 = 14491369) B14491369
theorem B2823167 : Blo 1486063 2823167 := bstep (se 1 (by rfl) ⟨2117375, by rfl⟩ : syracuseStep 2823167 = 4234751) B4234751
theorem B1487975 : Blo 1486063 1487975 := bstep (se 1 (by rfl) ⟨1115981, by rfl⟩ : syracuseStep 1487975 = 2231963) B2231963
theorem B3347567 : Blo 1486063 3347567 := bstep (se 1 (by rfl) ⟨2510675, by rfl⟩ : syracuseStep 3347567 = 5021351) B5021351
theorem B12063887 : Blo 1486063 12063887 := bstep (se 1 (by rfl) ⟨9047915, by rfl⟩ : syracuseStep 12063887 = 18095831) B18095831
theorem B3347711 : Blo 1486063 3347711 := bstep (se 1 (by rfl) ⟨2510783, by rfl⟩ : syracuseStep 3347711 = 5021567) B5021567
theorem B3765791 : Blo 1486063 3765791 := bstep (se 1 (by rfl) ⟨2824343, by rfl⟩ : syracuseStep 3765791 = 5648687) B5648687
theorem B2545199 : Blo 1486063 2545199 := bstep (se 1 (by rfl) ⟨1908899, by rfl⟩ : syracuseStep 2545199 = 3817799) B3817799
theorem B3815119 : Blo 1486063 3815119 := bstep (se 1 (by rfl) ⟨2861339, by rfl⟩ : syracuseStep 3815119 = 5722679) B5722679
theorem B14292935 : Blo 1486063 14292935 := bstep (se 1 (by rfl) ⟨10719701, by rfl⟩ : syracuseStep 14292935 = 21439403) B21439403
theorem B5020487 : Blo 1486063 5020487 := bstep (se 1 (by rfl) ⟨3765365, by rfl⟩ : syracuseStep 5020487 = 7530731) B7530731
theorem B3390431 : Blo 1486063 3390431 := bstep (se 1 (by rfl) ⟨2542823, by rfl⟩ : syracuseStep 3390431 = 5085647) B5085647
theorem B45784111 : Blo 1486063 45784111 := bstep (se 1 (by rfl) ⟨34338083, by rfl⟩ : syracuseStep 45784111 = 68676167) B68676167
theorem B15260881 : Blo 1486063 15260881 := bstep (se 2 (by rfl) ⟨5722830, by rfl⟩ : syracuseStep 15260881 = 11445661) B11445661
theorem B5356795 : Blo 1486063 5356795 := bstep (se 1 (by rfl) ⟨4017596, by rfl⟩ : syracuseStep 5356795 = 8035193) B8035193
theorem B6782251 : Blo 1486063 6782251 := bstep (se 1 (by rfl) ⟨5086688, by rfl⟩ : syracuseStep 6782251 = 10173377) B10173377
theorem B3571303 : Blo 1486063 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B7528139 : Blo 1486063 7528139 := bstep (se 1 (by rfl) ⟨5646104, by rfl⟩ : syracuseStep 7528139 = 11292209) B11292209
theorem B12066671 : Blo 1486063 12066671 := bstep (se 1 (by rfl) ⟨9050003, by rfl⟩ : syracuseStep 12066671 = 18100007) B18100007
theorem B154427897 : Blo 1486063 154427897 := bstep (se 2 (by rfl) ⟨57910461, by rfl⟩ : syracuseStep 154427897 = 115820923) B115820923
theorem B42402437 : Blo 1486063 42402437 := bstep (se 4 (by rfl) ⟨3975228, by rfl⟩ : syracuseStep 42402437 = 7950457) B7950457
theorem B1696799 : Blo 1486063 1696799 := bstep (se 1 (by rfl) ⟨1272599, by rfl⟩ : syracuseStep 1696799 = 2545199) B2545199
theorem B9528623 : Blo 1486063 9528623 := bstep (se 1 (by rfl) ⟨7146467, by rfl⟩ : syracuseStep 9528623 = 14292935) B14292935
theorem B4523347 : Blo 1486063 4523347 := bstep (se 1 (by rfl) ⟨3392510, by rfl⟩ : syracuseStep 4523347 = 6785021) B6785021
theorem B3343823 : Blo 1486063 3343823 := bstep (se 1 (by rfl) ⟨2507867, by rfl⟩ : syracuseStep 3343823 = 5015735) B5015735
theorem B724633235 : Blo 1486063 724633235 := bstep (se 1 (by rfl) ⟨543474926, by rfl⟩ : syracuseStep 724633235 = 1086949853) B1086949853
theorem B3016603 : Blo 1486063 3016603 := bstep (se 1 (by rfl) ⟨2262452, by rfl⟩ : syracuseStep 3016603 = 4524905) B4524905
theorem B2508907 : Blo 1486063 2508907 := bstep (se 1 (by rfl) ⟨1881680, by rfl⟩ : syracuseStep 2508907 = 3763361) B3763361
theorem B4761737 : Blo 1486063 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B79333561 : Blo 1486063 79333561 := bstep (se 2 (by rfl) ⟨29750085, by rfl⟩ : syracuseStep 79333561 = 59500171) B59500171
theorem B28576799 : Blo 1486063 28576799 := bstep (se 1 (by rfl) ⟨21432599, by rfl⟩ : syracuseStep 28576799 = 42865199) B42865199
theorem B1486079 : Blo 1486063 1486079 := bstep (se 1 (by rfl) ⟨1114559, by rfl⟩ : syracuseStep 1486079 = 2229119) B2229119
theorem B2231711 : Blo 1486063 2231711 := bstep (se 1 (by rfl) ⟨1673783, by rfl⟩ : syracuseStep 2231711 = 3347567) B3347567
theorem B9530855 : Blo 1486063 9530855 := bstep (se 1 (by rfl) ⟨7148141, by rfl⟩ : syracuseStep 9530855 = 14296283) B14296283
theorem B2231807 : Blo 1486063 2231807 := bstep (se 1 (by rfl) ⟨1673855, by rfl⟩ : syracuseStep 2231807 = 3347711) B3347711
theorem B3763817 : Blo 1486063 3763817 := bstep (se 2 (by rfl) ⟨1411431, by rfl⟩ : syracuseStep 3763817 = 2822863) B2822863
theorem B2510527 : Blo 1486063 2510527 := bstep (se 1 (by rfl) ⟨1882895, by rfl⟩ : syracuseStep 2510527 = 3765791) B3765791
theorem B1486683 : Blo 1486063 1486683 := bstep (se 1 (by rfl) ⟨1115012, by rfl⟩ : syracuseStep 1486683 = 2230025) B2230025
theorem B8466767 : Blo 1486063 8466767 := bstep (se 1 (by rfl) ⟨6350075, by rfl⟩ : syracuseStep 8466767 = 12700151) B12700151
theorem B3346991 : Blo 1486063 3346991 := bstep (se 1 (by rfl) ⟨2510243, by rfl⟩ : syracuseStep 3346991 = 5020487) B5020487
theorem B7533323 : Blo 1486063 7533323 := bstep (se 1 (by rfl) ⟨5649992, by rfl⟩ : syracuseStep 7533323 = 11299985) B11299985
theorem B4895839 : Blo 1486063 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B5018759 : Blo 1486063 5018759 := bstep (se 1 (by rfl) ⟨3764069, by rfl⟩ : syracuseStep 5018759 = 7528139) B7528139
theorem B38106287 : Blo 1486063 38106287 := bstep (se 1 (by rfl) ⟨28579715, by rfl⟩ : syracuseStep 38106287 = 57159431) B57159431
theorem B9041149 : Blo 1486063 9041149 := bstep (se 3 (by rfl) ⟨1695215, by rfl⟩ : syracuseStep 9041149 = 3390431) B3390431
theorem B9049715 : Blo 1486063 9049715 := bstep (se 1 (by rfl) ⟨6787286, by rfl⟩ : syracuseStep 9049715 = 13574573) B13574573
theorem B626120513 : Blo 1486063 626120513 := bstep (se 2 (by rfl) ⟨234795192, by rfl⟩ : syracuseStep 626120513 = 469590385) B469590385
theorem B16070555 : Blo 1486063 16070555 := bstep (se 1 (by rfl) ⟨12052916, by rfl⟩ : syracuseStep 16070555 = 24105833) B24105833
theorem B1882111 : Blo 1486063 1882111 := bstep (se 1 (by rfl) ⟨1411583, by rfl⟩ : syracuseStep 1882111 = 2823167) B2823167
theorem B8042591 : Blo 1486063 8042591 := bstep (se 1 (by rfl) ⟨6031943, by rfl⟩ : syracuseStep 8042591 = 12063887) B12063887
theorem B20347301 : Blo 1486063 20347301 := bstep (se 4 (by rfl) ⟨1907559, by rfl⟩ : syracuseStep 20347301 = 3815119) B3815119
theorem B25762433 : Blo 1486063 25762433 := bstep (se 2 (by rfl) ⟨9660912, by rfl⟩ : syracuseStep 25762433 = 19321825) B19321825
theorem B61045481 : Blo 1486063 61045481 := bstep (se 2 (by rfl) ⟨22892055, by rfl⟩ : syracuseStep 61045481 = 45784111) B45784111
theorem B12696425 : Blo 1486063 12696425 := bstep (se 2 (by rfl) ⟨4761159, by rfl⟩ : syracuseStep 12696425 = 9522319) B9522319
theorem B16931753 : Blo 1486063 16931753 := bstep (se 2 (by rfl) ⟨6349407, by rfl⟩ : syracuseStep 16931753 = 12698815) B12698815
theorem B20347841 : Blo 1486063 20347841 := bstep (se 2 (by rfl) ⟨7630440, by rfl⟩ : syracuseStep 20347841 = 15260881) B15260881
theorem B7142393 : Blo 1486063 7142393 := bstep (se 2 (by rfl) ⟨2678397, by rfl⟩ : syracuseStep 7142393 = 5356795) B5356795
theorem B9043001 : Blo 1486063 9043001 := bstep (se 2 (by rfl) ⟨3391125, by rfl⟩ : syracuseStep 9043001 = 6782251) B6782251
theorem B8044447 : Blo 1486063 8044447 := bstep (se 1 (by rfl) ⟨6033335, by rfl⟩ : syracuseStep 8044447 = 12066671) B12066671
theorem B5644511 : Blo 1486063 5644511 := bstep (se 1 (by rfl) ⟨4233383, by rfl⟩ : syracuseStep 5644511 = 8466767) B8466767
theorem B5022215 : Blo 1486063 5022215 := bstep (se 1 (by rfl) ⟨3766661, by rfl⟩ : syracuseStep 5022215 = 7533323) B7533323
theorem B25404191 : Blo 1486063 25404191 := bstep (se 1 (by rfl) ⟨19053143, by rfl⟩ : syracuseStep 25404191 = 38106287) B38106287
theorem B2229215 : Blo 1486063 2229215 := bstep (se 1 (by rfl) ⟨1671911, by rfl⟩ : syracuseStep 2229215 = 3343823) B3343823
theorem B68699821 : Blo 1486063 68699821 := bstep (se 3 (by rfl) ⟨12881216, by rfl⟩ : syracuseStep 68699821 = 25762433) B25762433
theorem B8464283 : Blo 1486063 8464283 := bstep (se 1 (by rfl) ⟨6348212, by rfl⟩ : syracuseStep 8464283 = 12696425) B12696425
theorem B4761595 : Blo 1486063 4761595 := bstep (se 1 (by rfl) ⟨3571196, by rfl⟩ : syracuseStep 4761595 = 7142393) B7142393
theorem B2509211 : Blo 1486063 2509211 := bstep (se 1 (by rfl) ⟨1881908, by rfl⟩ : syracuseStep 2509211 = 3763817) B3763817
theorem B10725929 : Blo 1486063 10725929 := bstep (se 2 (by rfl) ⟨4022223, by rfl⟩ : syracuseStep 10725929 = 8044447) B8044447
theorem B2509481 : Blo 1486063 2509481 := bstep (se 2 (by rfl) ⟨941055, by rfl⟩ : syracuseStep 2509481 = 1882111) B1882111
theorem B4524797 : Blo 1486063 4524797 := bstep (se 3 (by rfl) ⟨848399, by rfl⟩ : syracuseStep 4524797 = 1696799) B1696799
theorem B3345209 : Blo 1486063 3345209 := bstep (se 2 (by rfl) ⟨1254453, by rfl⟩ : syracuseStep 3345209 = 2508907) B2508907
theorem B105778081 : Blo 1486063 105778081 := bstep (se 2 (by rfl) ⟨39666780, by rfl⟩ : syracuseStep 105778081 = 79333561) B79333561
theorem B2231327 : Blo 1486063 2231327 := bstep (se 1 (by rfl) ⟨1673495, by rfl⟩ : syracuseStep 2231327 = 3346991) B3346991
theorem B3345839 : Blo 1486063 3345839 := bstep (se 1 (by rfl) ⟨2509379, by rfl⟩ : syracuseStep 3345839 = 5018759) B5018759
theorem B6352415 : Blo 1486063 6352415 := bstep (se 1 (by rfl) ⟨4764311, by rfl⟩ : syracuseStep 6352415 = 9528623) B9528623
theorem B6033143 : Blo 1486063 6033143 := bstep (se 1 (by rfl) ⟨4524857, by rfl⟩ : syracuseStep 6033143 = 9049715) B9049715
theorem B54259469 : Blo 1486063 54259469 := bstep (se 3 (by rfl) ⟨10173650, by rfl⟩ : syracuseStep 54259469 = 20347301) B20347301
theorem B411807725 : Blo 1486063 411807725 := bstep (se 3 (by rfl) ⟨77213948, by rfl⟩ : syracuseStep 411807725 = 154427897) B154427897
theorem B5361727 : Blo 1486063 5361727 := bstep (se 1 (by rfl) ⟨4021295, by rfl⟩ : syracuseStep 5361727 = 8042591) B8042591
theorem B3174491 : Blo 1486063 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B12054865 : Blo 1486063 12054865 := bstep (se 2 (by rfl) ⟨4520574, by rfl⟩ : syracuseStep 12054865 = 9041149) B9041149
theorem B19051199 : Blo 1486063 19051199 := bstep (se 1 (by rfl) ⟨14288399, by rfl⟩ : syracuseStep 19051199 = 28576799) B28576799
theorem B3347369 : Blo 1486063 3347369 := bstep (se 2 (by rfl) ⟨1255263, by rfl⟩ : syracuseStep 3347369 = 2510527) B2510527
theorem B1487807 : Blo 1486063 1487807 := bstep (se 1 (by rfl) ⟨1115855, by rfl⟩ : syracuseStep 1487807 = 2231711) B2231711
theorem B6353903 : Blo 1486063 6353903 := bstep (se 1 (by rfl) ⟨4765427, by rfl⟩ : syracuseStep 6353903 = 9530855) B9530855
theorem B1487871 : Blo 1486063 1487871 := bstep (se 1 (by rfl) ⟨1115903, by rfl⟩ : syracuseStep 1487871 = 2231807) B2231807
theorem B28268291 : Blo 1486063 28268291 := bstep (se 1 (by rfl) ⟨21201218, by rfl⟩ : syracuseStep 28268291 = 42402437) B42402437
theorem B483088823 : Blo 1486063 483088823 := bstep (se 1 (by rfl) ⟨362316617, by rfl⟩ : syracuseStep 483088823 = 724633235) B724633235
theorem B417413675 : Blo 1486063 417413675 := bstep (se 1 (by rfl) ⟨313060256, by rfl⟩ : syracuseStep 417413675 = 626120513) B626120513
theorem B10713703 : Blo 1486063 10713703 := bstep (se 1 (by rfl) ⟨8035277, by rfl⟩ : syracuseStep 10713703 = 16070555) B16070555
theorem B6527785 : Blo 1486063 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B24124517 : Blo 1486063 24124517 := bstep (se 4 (by rfl) ⟨2261673, by rfl⟩ : syracuseStep 24124517 = 4523347) B4523347
theorem B40696987 : Blo 1486063 40696987 := bstep (se 1 (by rfl) ⟨30522740, by rfl⟩ : syracuseStep 40696987 = 61045481) B61045481
theorem B11287835 : Blo 1486063 11287835 := bstep (se 1 (by rfl) ⟨8465876, by rfl⟩ : syracuseStep 11287835 = 16931753) B16931753
theorem B13565227 : Blo 1486063 13565227 := bstep (se 1 (by rfl) ⟨10173920, by rfl⟩ : syracuseStep 13565227 = 20347841) B20347841
theorem B6028667 : Blo 1486063 6028667 := bstep (se 1 (by rfl) ⟨4521500, by rfl⟩ : syracuseStep 6028667 = 9043001) B9043001
theorem B4022137 : Blo 1486063 4022137 := bstep (se 2 (by rfl) ⟨1508301, by rfl⟩ : syracuseStep 4022137 = 3016603) B3016603
theorem B16073153 : Blo 1486063 16073153 := bstep (se 2 (by rfl) ⟨6027432, by rfl⟩ : syracuseStep 16073153 = 12054865) B12054865
theorem B4235935 : Blo 1486063 4235935 := bstep (se 1 (by rfl) ⟨3176951, by rfl⟩ : syracuseStep 4235935 = 6353903) B6353903
theorem B1672807 : Blo 1486063 1672807 := bstep (se 1 (by rfl) ⟨1254605, by rfl⟩ : syracuseStep 1672807 = 2509211) B2509211
theorem B278275783 : Blo 1486063 278275783 := bstep (se 1 (by rfl) ⟨208706837, by rfl⟩ : syracuseStep 278275783 = 417413675) B417413675
theorem B6348793 : Blo 1486063 6348793 := bstep (se 2 (by rfl) ⟨2380797, by rfl⟩ : syracuseStep 6348793 = 4761595) B4761595
theorem B1672987 : Blo 1486063 1672987 := bstep (se 1 (by rfl) ⟨1254740, by rfl⟩ : syracuseStep 1672987 = 2509481) B2509481
theorem B3016531 : Blo 1486063 3016531 := bstep (se 1 (by rfl) ⟨2262398, by rfl⟩ : syracuseStep 3016531 = 4524797) B4524797
theorem B2230139 : Blo 1486063 2230139 := bstep (se 1 (by rfl) ⟨1672604, by rfl⟩ : syracuseStep 2230139 = 3345209) B3345209
theorem B16083011 : Blo 1486063 16083011 := bstep (se 1 (by rfl) ⟨12062258, by rfl⟩ : syracuseStep 16083011 = 24124517) B24124517
theorem B2230559 : Blo 1486063 2230559 := bstep (se 1 (by rfl) ⟨1672919, by rfl⟩ : syracuseStep 2230559 = 3345839) B3345839
theorem B3763007 : Blo 1486063 3763007 := bstep (se 1 (by rfl) ⟨2822255, by rfl⟩ : syracuseStep 3763007 = 5644511) B5644511
theorem B8465309 : Blo 1486063 8465309 := bstep (se 3 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 8465309 = 3174491) B3174491
theorem B12700799 : Blo 1486063 12700799 := bstep (se 1 (by rfl) ⟨9525599, by rfl⟩ : syracuseStep 12700799 = 19051199) B19051199
theorem B16936127 : Blo 1486063 16936127 := bstep (se 1 (by rfl) ⟨12702095, by rfl⟩ : syracuseStep 16936127 = 25404191) B25404191
theorem B2231579 : Blo 1486063 2231579 := bstep (se 1 (by rfl) ⟨1673684, by rfl⟩ : syracuseStep 2231579 = 3347369) B3347369
theorem B1486143 : Blo 1486063 1486143 := bstep (se 1 (by rfl) ⟨1114607, by rfl⟩ : syracuseStep 1486143 = 2229215) B2229215
theorem B8703713 : Blo 1486063 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B1487551 : Blo 1486063 1487551 := bstep (se 1 (by rfl) ⟨1115663, by rfl⟩ : syracuseStep 1487551 = 2231327) B2231327
theorem B7525223 : Blo 1486063 7525223 := bstep (se 1 (by rfl) ⟨5643917, by rfl⟩ : syracuseStep 7525223 = 11287835) B11287835
theorem B91599761 : Blo 1486063 91599761 := bstep (se 2 (by rfl) ⟨34349910, by rfl⟩ : syracuseStep 91599761 = 68699821) B68699821
theorem B4019111 : Blo 1486063 4019111 := bstep (se 1 (by rfl) ⟨3014333, by rfl⟩ : syracuseStep 4019111 = 6028667) B6028667
theorem B5362849 : Blo 1486063 5362849 := bstep (se 2 (by rfl) ⟨2011068, by rfl⟩ : syracuseStep 5362849 = 4022137) B4022137
theorem B36172979 : Blo 1486063 36172979 := bstep (se 1 (by rfl) ⟨27129734, by rfl⟩ : syracuseStep 36172979 = 54259469) B54259469
theorem B7148969 : Blo 1486063 7148969 := bstep (se 2 (by rfl) ⟨2680863, by rfl⟩ : syracuseStep 7148969 = 5361727) B5361727
theorem B3348143 : Blo 1486063 3348143 := bstep (se 1 (by rfl) ⟨2511107, by rfl⟩ : syracuseStep 3348143 = 5022215) B5022215
theorem B14284937 : Blo 1486063 14284937 := bstep (se 2 (by rfl) ⟨5356851, by rfl⟩ : syracuseStep 14284937 = 10713703) B10713703
theorem B5642855 : Blo 1486063 5642855 := bstep (se 1 (by rfl) ⟨4232141, by rfl⟩ : syracuseStep 5642855 = 8464283) B8464283
theorem B54262649 : Blo 1486063 54262649 := bstep (se 2 (by rfl) ⟨20348493, by rfl⟩ : syracuseStep 54262649 = 40696987) B40696987
theorem B322059215 : Blo 1486063 322059215 := bstep (se 1 (by rfl) ⟨241544411, by rfl⟩ : syracuseStep 322059215 = 483088823) B483088823
theorem B7150619 : Blo 1486063 7150619 := bstep (se 1 (by rfl) ⟨5362964, by rfl⟩ : syracuseStep 7150619 = 10725929) B10725929
theorem B18086969 : Blo 1486063 18086969 := bstep (se 2 (by rfl) ⟨6782613, by rfl⟩ : syracuseStep 18086969 = 13565227) B13565227
theorem B75382109 : Blo 1486063 75382109 := bstep (se 3 (by rfl) ⟨14134145, by rfl⟩ : syracuseStep 75382109 = 28268291) B28268291
theorem B564149765 : Blo 1486063 564149765 := bstep (se 4 (by rfl) ⟨52889040, by rfl⟩ : syracuseStep 564149765 = 105778081) B105778081
theorem B4234943 : Blo 1486063 4234943 := bstep (se 1 (by rfl) ⟨3176207, by rfl⟩ : syracuseStep 4234943 = 6352415) B6352415
theorem B4022095 : Blo 1486063 4022095 := bstep (se 1 (by rfl) ⟨3016571, by rfl⟩ : syracuseStep 4022095 = 6033143) B6033143
theorem B274538483 : Blo 1486063 274538483 := bstep (se 1 (by rfl) ⟨205903862, by rfl⟩ : syracuseStep 274538483 = 411807725) B411807725
theorem B10715435 : Blo 1486063 10715435 := bstep (se 1 (by rfl) ⟨8036576, by rfl⟩ : syracuseStep 10715435 = 16073153) B16073153
theorem B38093165 : Blo 1486063 38093165 := bstep (se 3 (by rfl) ⟨7142468, by rfl⟩ : syracuseStep 38093165 = 14284937) B14284937
theorem B2679407 : Blo 1486063 2679407 := bstep (se 1 (by rfl) ⟨2009555, by rfl⟩ : syracuseStep 2679407 = 4019111) B4019111
theorem B3761903 : Blo 1486063 3761903 := bstep (se 1 (by rfl) ⟨2821427, by rfl⟩ : syracuseStep 3761903 = 5642855) B5642855
theorem B2508671 : Blo 1486063 2508671 := bstep (se 1 (by rfl) ⟨1881503, by rfl⟩ : syracuseStep 2508671 = 3763007) B3763007
theorem B23209901 : Blo 1486063 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B214706143 : Blo 1486063 214706143 := bstep (se 1 (by rfl) ⟨161029607, by rfl⟩ : syracuseStep 214706143 = 322059215) B322059215
theorem B11290751 : Blo 1486063 11290751 := bstep (se 1 (by rfl) ⟨8468063, by rfl⟩ : syracuseStep 11290751 = 16936127) B16936127
theorem B2230409 : Blo 1486063 2230409 := bstep (se 2 (by rfl) ⟨836403, by rfl⟩ : syracuseStep 2230409 = 1672807) B1672807
theorem B371034377 : Blo 1486063 371034377 := bstep (se 2 (by rfl) ⟨139137891, by rfl⟩ : syracuseStep 371034377 = 278275783) B278275783
theorem B2230649 : Blo 1486063 2230649 := bstep (se 2 (by rfl) ⟨836493, by rfl⟩ : syracuseStep 2230649 = 1672987) B1672987
theorem B8465057 : Blo 1486063 8465057 := bstep (se 2 (by rfl) ⟨3174396, by rfl⟩ : syracuseStep 8465057 = 6348793) B6348793
theorem B5016815 : Blo 1486063 5016815 := bstep (se 1 (by rfl) ⟨3762611, by rfl⟩ : syracuseStep 5016815 = 7525223) B7525223
theorem B61066507 : Blo 1486063 61066507 := bstep (se 1 (by rfl) ⟨45799880, by rfl⟩ : syracuseStep 61066507 = 91599761) B91599761
theorem B5647913 : Blo 1486063 5647913 := bstep (se 2 (by rfl) ⟨2117967, by rfl⟩ : syracuseStep 5647913 = 4235935) B4235935
theorem B2232095 : Blo 1486063 2232095 := bstep (se 1 (by rfl) ⟨1674071, by rfl⟩ : syracuseStep 2232095 = 3348143) B3348143
theorem B1486759 : Blo 1486063 1486759 := bstep (se 1 (by rfl) ⟨1115069, by rfl⟩ : syracuseStep 1486759 = 2230139) B2230139
theorem B1487039 : Blo 1486063 1487039 := bstep (se 1 (by rfl) ⟨1115279, by rfl⟩ : syracuseStep 1487039 = 2230559) B2230559
theorem B11293181 : Blo 1486063 11293181 := bstep (se 3 (by rfl) ⟨2117471, by rfl⟩ : syracuseStep 11293181 = 4234943) B4234943
theorem B8467199 : Blo 1486063 8467199 := bstep (se 1 (by rfl) ⟨6350399, by rfl⟩ : syracuseStep 8467199 = 12700799) B12700799
theorem B1487719 : Blo 1486063 1487719 := bstep (se 1 (by rfl) ⟨1115789, by rfl⟩ : syracuseStep 1487719 = 2231579) B2231579
theorem B50254739 : Blo 1486063 50254739 := bstep (se 1 (by rfl) ⟨37691054, by rfl⟩ : syracuseStep 50254739 = 75382109) B75382109
theorem B376099843 : Blo 1486063 376099843 := bstep (se 1 (by rfl) ⟨282074882, by rfl⟩ : syracuseStep 376099843 = 564149765) B564149765
theorem B5362793 : Blo 1486063 5362793 := bstep (se 2 (by rfl) ⟨2011047, by rfl⟩ : syracuseStep 5362793 = 4022095) B4022095
theorem B19068317 : Blo 1486063 19068317 := bstep (se 3 (by rfl) ⟨3575309, by rfl⟩ : syracuseStep 19068317 = 7150619) B7150619
theorem B24115319 : Blo 1486063 24115319 := bstep (se 1 (by rfl) ⟨18086489, by rfl⟩ : syracuseStep 24115319 = 36172979) B36172979
theorem B4765979 : Blo 1486063 4765979 := bstep (se 1 (by rfl) ⟨3574484, by rfl⟩ : syracuseStep 4765979 = 7148969) B7148969
theorem B10722007 : Blo 1486063 10722007 := bstep (se 1 (by rfl) ⟨8041505, by rfl⟩ : syracuseStep 10722007 = 16083011) B16083011
theorem B7150465 : Blo 1486063 7150465 := bstep (se 2 (by rfl) ⟨2681424, by rfl⟩ : syracuseStep 7150465 = 5362849) B5362849
theorem B16088165 : Blo 1486063 16088165 := bstep (se 4 (by rfl) ⟨1508265, by rfl⟩ : syracuseStep 16088165 = 3016531) B3016531
theorem B36175099 : Blo 1486063 36175099 := bstep (se 1 (by rfl) ⟨27131324, by rfl⟩ : syracuseStep 36175099 = 54262649) B54262649
theorem B5643539 : Blo 1486063 5643539 := bstep (se 1 (by rfl) ⟨4232654, by rfl⟩ : syracuseStep 5643539 = 8465309) B8465309
theorem B12057979 : Blo 1486063 12057979 := bstep (se 1 (by rfl) ⟨9043484, by rfl⟩ : syracuseStep 12057979 = 18086969) B18086969
theorem B183025655 : Blo 1486063 183025655 := bstep (se 1 (by rfl) ⟨137269241, by rfl⟩ : syracuseStep 183025655 = 274538483) B274538483
theorem B7143623 : Blo 1486063 7143623 := bstep (se 1 (by rfl) ⟨5357717, by rfl⟩ : syracuseStep 7143623 = 10715435) B10715435
theorem B25395443 : Blo 1486063 25395443 := bstep (se 1 (by rfl) ⟨19046582, by rfl⟩ : syracuseStep 25395443 = 38093165) B38093165
theorem B7528787 : Blo 1486063 7528787 := bstep (se 1 (by rfl) ⟨5646590, by rfl⟩ : syracuseStep 7528787 = 11293181) B11293181
theorem B1786271 : Blo 1486063 1786271 := bstep (se 1 (by rfl) ⟨1339703, by rfl⟩ : syracuseStep 1786271 = 2679407) B2679407
theorem B5644799 : Blo 1486063 5644799 := bstep (se 1 (by rfl) ⟨4233599, by rfl⟩ : syracuseStep 5644799 = 8467199) B8467199
theorem B14296009 : Blo 1486063 14296009 := bstep (se 2 (by rfl) ⟨5361003, by rfl⟩ : syracuseStep 14296009 = 10722007) B10722007
theorem B2507935 : Blo 1486063 2507935 := bstep (se 1 (by rfl) ⟨1880951, by rfl⟩ : syracuseStep 2507935 = 3761903) B3761903
theorem B1672447 : Blo 1486063 1672447 := bstep (se 1 (by rfl) ⟨1254335, by rfl⟩ : syracuseStep 1672447 = 2508671) B2508671
theorem B501466457 : Blo 1486063 501466457 := bstep (se 2 (by rfl) ⟨188049921, by rfl⟩ : syracuseStep 501466457 = 376099843) B376099843
theorem B81422009 : Blo 1486063 81422009 := bstep (se 2 (by rfl) ⟨30533253, by rfl⟩ : syracuseStep 81422009 = 61066507) B61066507
theorem B10725443 : Blo 1486063 10725443 := bstep (se 1 (by rfl) ⟨8044082, by rfl⟩ : syracuseStep 10725443 = 16088165) B16088165
theorem B3344543 : Blo 1486063 3344543 := bstep (se 1 (by rfl) ⟨2508407, by rfl⟩ : syracuseStep 3344543 = 5016815) B5016815
theorem B3762359 : Blo 1486063 3762359 := bstep (se 1 (by rfl) ⟨2821769, by rfl⟩ : syracuseStep 3762359 = 5643539) B5643539
theorem B3575195 : Blo 1486063 3575195 := bstep (se 1 (by rfl) ⟨2681396, by rfl⟩ : syracuseStep 3575195 = 5362793) B5362793
theorem B16076879 : Blo 1486063 16076879 := bstep (se 1 (by rfl) ⟨12057659, by rfl⟩ : syracuseStep 16076879 = 24115319) B24115319
theorem B1486939 : Blo 1486063 1486939 := bstep (se 1 (by rfl) ⟨1115204, by rfl⟩ : syracuseStep 1486939 = 2230409) B2230409
theorem B1487099 : Blo 1486063 1487099 := bstep (se 1 (by rfl) ⟨1115324, by rfl⟩ : syracuseStep 1487099 = 2230649) B2230649
theorem B16077305 : Blo 1486063 16077305 := bstep (se 2 (by rfl) ⟨6028989, by rfl⟩ : syracuseStep 16077305 = 12057979) B12057979
theorem B3765275 : Blo 1486063 3765275 := bstep (se 1 (by rfl) ⟨2823956, by rfl⟩ : syracuseStep 3765275 = 5647913) B5647913
theorem B1488063 : Blo 1486063 1488063 := bstep (se 1 (by rfl) ⟨1116047, by rfl⟩ : syracuseStep 1488063 = 2232095) B2232095
theorem B286274857 : Blo 1486063 286274857 := bstep (se 2 (by rfl) ⟨107353071, by rfl⟩ : syracuseStep 286274857 = 214706143) B214706143
theorem B122017103 : Blo 1486063 122017103 := bstep (se 1 (by rfl) ⟨91512827, by rfl⟩ : syracuseStep 122017103 = 183025655) B183025655
theorem B33503159 : Blo 1486063 33503159 := bstep (se 1 (by rfl) ⟨25127369, by rfl⟩ : syracuseStep 33503159 = 50254739) B50254739
theorem B12712211 : Blo 1486063 12712211 := bstep (se 1 (by rfl) ⟨9534158, by rfl⟩ : syracuseStep 12712211 = 19068317) B19068317
theorem B9533953 : Blo 1486063 9533953 := bstep (se 2 (by rfl) ⟨3575232, by rfl⟩ : syracuseStep 9533953 = 7150465) B7150465
theorem B15473267 : Blo 1486063 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B7527167 : Blo 1486063 7527167 := bstep (se 1 (by rfl) ⟨5645375, by rfl⟩ : syracuseStep 7527167 = 11290751) B11290751
theorem B247356251 : Blo 1486063 247356251 := bstep (se 1 (by rfl) ⟨185517188, by rfl⟩ : syracuseStep 247356251 = 371034377) B371034377
theorem B3177319 : Blo 1486063 3177319 := bstep (se 1 (by rfl) ⟨2382989, by rfl⟩ : syracuseStep 3177319 = 4765979) B4765979
theorem B48233465 : Blo 1486063 48233465 := bstep (se 2 (by rfl) ⟨18087549, by rfl⟩ : syracuseStep 48233465 = 36175099) B36175099
theorem B5643371 : Blo 1486063 5643371 := bstep (se 1 (by rfl) ⟨4232528, by rfl⟩ : syracuseStep 5643371 = 8465057) B8465057
theorem B54281339 : Blo 1486063 54281339 := bstep (se 1 (by rfl) ⟨40711004, by rfl⟩ : syracuseStep 54281339 = 81422009) B81422009
theorem B4236425 : Blo 1486063 4236425 := bstep (se 2 (by rfl) ⟨1588659, by rfl⟩ : syracuseStep 4236425 = 3177319) B3177319
theorem B2229695 : Blo 1486063 2229695 := bstep (se 1 (by rfl) ⟨1672271, by rfl⟩ : syracuseStep 2229695 = 3344543) B3344543
theorem B2508239 : Blo 1486063 2508239 := bstep (se 1 (by rfl) ⟨1881179, by rfl⟩ : syracuseStep 2508239 = 3762359) B3762359
theorem B3343913 : Blo 1486063 3343913 := bstep (se 2 (by rfl) ⟨1253967, by rfl⟩ : syracuseStep 3343913 = 2507935) B2507935
theorem B2229929 : Blo 1486063 2229929 := bstep (se 2 (by rfl) ⟨836223, by rfl⟩ : syracuseStep 2229929 = 1672447) B1672447
theorem B381699809 : Blo 1486063 381699809 := bstep (se 2 (by rfl) ⟨143137428, by rfl⟩ : syracuseStep 381699809 = 286274857) B286274857
theorem B10315511 : Blo 1486063 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B32155643 : Blo 1486063 32155643 := bstep (se 1 (by rfl) ⟨24116732, by rfl⟩ : syracuseStep 32155643 = 48233465) B48233465
theorem B3762247 : Blo 1486063 3762247 := bstep (se 1 (by rfl) ⟨2821685, by rfl⟩ : syracuseStep 3762247 = 5643371) B5643371
theorem B10717919 : Blo 1486063 10717919 := bstep (se 1 (by rfl) ⟨8038439, by rfl⟩ : syracuseStep 10717919 = 16076879) B16076879
theorem B4762415 : Blo 1486063 4762415 := bstep (se 1 (by rfl) ⟨3571811, by rfl⟩ : syracuseStep 4762415 = 7143623) B7143623
theorem B10718203 : Blo 1486063 10718203 := bstep (se 1 (by rfl) ⟨8038652, by rfl⟩ : syracuseStep 10718203 = 16077305) B16077305
theorem B3763199 : Blo 1486063 3763199 := bstep (se 1 (by rfl) ⟨2822399, by rfl⟩ : syracuseStep 3763199 = 5644799) B5644799
theorem B2510183 : Blo 1486063 2510183 := bstep (se 1 (by rfl) ⟨1882637, by rfl⟩ : syracuseStep 2510183 = 3765275) B3765275
theorem B334310971 : Blo 1486063 334310971 := bstep (se 1 (by rfl) ⟨250733228, by rfl⟩ : syracuseStep 334310971 = 501466457) B501466457
theorem B4763389 : Blo 1486063 4763389 := bstep (se 3 (by rfl) ⟨893135, by rfl⟩ : syracuseStep 4763389 = 1786271) B1786271
theorem B22335439 : Blo 1486063 22335439 := bstep (se 1 (by rfl) ⟨16751579, by rfl⟩ : syracuseStep 22335439 = 33503159) B33503159
theorem B8474807 : Blo 1486063 8474807 := bstep (se 1 (by rfl) ⟨6356105, by rfl⟩ : syracuseStep 8474807 = 12712211) B12712211
theorem B5018111 : Blo 1486063 5018111 := bstep (se 1 (by rfl) ⟨3763583, by rfl⟩ : syracuseStep 5018111 = 7527167) B7527167
theorem B16930295 : Blo 1486063 16930295 := bstep (se 1 (by rfl) ⟨12697721, by rfl⟩ : syracuseStep 16930295 = 25395443) B25395443
theorem B5019191 : Blo 1486063 5019191 := bstep (se 1 (by rfl) ⟨3764393, by rfl⟩ : syracuseStep 5019191 = 7528787) B7528787
theorem B12711937 : Blo 1486063 12711937 := bstep (se 2 (by rfl) ⟨4766976, by rfl⟩ : syracuseStep 12711937 = 9533953) B9533953
theorem B81344735 : Blo 1486063 81344735 := bstep (se 1 (by rfl) ⟨61008551, by rfl⟩ : syracuseStep 81344735 = 122017103) B122017103
theorem B19061345 : Blo 1486063 19061345 := bstep (se 2 (by rfl) ⟨7148004, by rfl⟩ : syracuseStep 19061345 = 14296009) B14296009
theorem B7150295 : Blo 1486063 7150295 := bstep (se 1 (by rfl) ⟨5362721, by rfl⟩ : syracuseStep 7150295 = 10725443) B10725443
theorem B164904167 : Blo 1486063 164904167 := bstep (se 1 (by rfl) ⟨123678125, by rfl⟩ : syracuseStep 164904167 = 247356251) B247356251
theorem B2383463 : Blo 1486063 2383463 := bstep (se 1 (by rfl) ⟨1787597, by rfl⟩ : syracuseStep 2383463 = 3575195) B3575195
theorem B16949249 : Blo 1486063 16949249 := bstep (se 2 (by rfl) ⟨6355968, by rfl⟩ : syracuseStep 16949249 = 12711937) B12711937
theorem B1672159 : Blo 1486063 1672159 := bstep (se 1 (by rfl) ⟨1254119, by rfl⟩ : syracuseStep 1672159 = 2508239) B2508239
theorem B2229275 : Blo 1486063 2229275 := bstep (se 1 (by rfl) ⟨1671956, by rfl⟩ : syracuseStep 2229275 = 3343913) B3343913
theorem B12707563 : Blo 1486063 12707563 := bstep (se 1 (by rfl) ⟨9530672, by rfl⟩ : syracuseStep 12707563 = 19061345) B19061345
theorem B7145279 : Blo 1486063 7145279 := bstep (se 1 (by rfl) ⟨5358959, by rfl⟩ : syracuseStep 7145279 = 10717919) B10717919
theorem B2508799 : Blo 1486063 2508799 := bstep (se 1 (by rfl) ⟨1881599, by rfl⟩ : syracuseStep 2508799 = 3763199) B3763199
theorem B12699773 : Blo 1486063 12699773 := bstep (se 3 (by rfl) ⟨2381207, by rfl⟩ : syracuseStep 12699773 = 4762415) B4762415
theorem B1673455 : Blo 1486063 1673455 := bstep (se 1 (by rfl) ⟨1255091, by rfl⟩ : syracuseStep 1673455 = 2510183) B2510183
theorem B6351185 : Blo 1486063 6351185 := bstep (se 2 (by rfl) ⟨2381694, by rfl⟩ : syracuseStep 6351185 = 4763389) B4763389
theorem B29780585 : Blo 1486063 29780585 := bstep (se 2 (by rfl) ⟨11167719, by rfl⟩ : syracuseStep 29780585 = 22335439) B22335439
theorem B5016329 : Blo 1486063 5016329 := bstep (se 2 (by rfl) ⟨1881123, by rfl⟩ : syracuseStep 5016329 = 3762247) B3762247
theorem B3345407 : Blo 1486063 3345407 := bstep (se 1 (by rfl) ⟨2509055, by rfl⟩ : syracuseStep 3345407 = 5018111) B5018111
theorem B36187559 : Blo 1486063 36187559 := bstep (se 1 (by rfl) ⟨27140669, by rfl⟩ : syracuseStep 36187559 = 54281339) B54281339
theorem B1486463 : Blo 1486063 1486463 := bstep (se 1 (by rfl) ⟨1114847, by rfl⟩ : syracuseStep 1486463 = 2229695) B2229695
theorem B3346127 : Blo 1486063 3346127 := bstep (se 1 (by rfl) ⟨2509595, by rfl⟩ : syracuseStep 3346127 = 5019191) B5019191
theorem B1486619 : Blo 1486063 1486619 := bstep (se 1 (by rfl) ⟨1114964, by rfl⟩ : syracuseStep 1486619 = 2229929) B2229929
theorem B6877007 : Blo 1486063 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B14290937 : Blo 1486063 14290937 := bstep (se 2 (by rfl) ⟨5359101, by rfl⟩ : syracuseStep 14290937 = 10718203) B10718203
theorem B445747961 : Blo 1486063 445747961 := bstep (se 2 (by rfl) ⟨167155485, by rfl⟩ : syracuseStep 445747961 = 334310971) B334310971
theorem B5649871 : Blo 1486063 5649871 := bstep (se 1 (by rfl) ⟨4237403, by rfl⟩ : syracuseStep 5649871 = 8474807) B8474807
theorem B2824283 : Blo 1486063 2824283 := bstep (se 1 (by rfl) ⟨2118212, by rfl⟩ : syracuseStep 2824283 = 4236425) B4236425
theorem B11286863 : Blo 1486063 11286863 := bstep (se 1 (by rfl) ⟨8465147, by rfl⟩ : syracuseStep 11286863 = 16930295) B16930295
theorem B254466539 : Blo 1486063 254466539 := bstep (se 1 (by rfl) ⟨190849904, by rfl⟩ : syracuseStep 254466539 = 381699809) B381699809
theorem B21437095 : Blo 1486063 21437095 := bstep (se 1 (by rfl) ⟨16077821, by rfl⟩ : syracuseStep 21437095 = 32155643) B32155643
theorem B54229823 : Blo 1486063 54229823 := bstep (se 1 (by rfl) ⟨40672367, by rfl⟩ : syracuseStep 54229823 = 81344735) B81344735
theorem B6355901 : Blo 1486063 6355901 := bstep (se 3 (by rfl) ⟨1191731, by rfl⟩ : syracuseStep 6355901 = 2383463) B2383463
theorem B4766863 : Blo 1486063 4766863 := bstep (se 1 (by rfl) ⟨3575147, by rfl⟩ : syracuseStep 4766863 = 7150295) B7150295
theorem B109936111 : Blo 1486063 109936111 := bstep (se 1 (by rfl) ⟨82452083, by rfl⟩ : syracuseStep 109936111 = 164904167) B164904167
theorem B297165307 : Blo 1486063 297165307 := bstep (se 1 (by rfl) ⟨222873980, by rfl⟩ : syracuseStep 297165307 = 445747961) B445747961
theorem B28582793 : Blo 1486063 28582793 := bstep (se 2 (by rfl) ⟨10718547, by rfl⟩ : syracuseStep 28582793 = 21437095) B21437095
theorem B2229545 : Blo 1486063 2229545 := bstep (se 2 (by rfl) ⟨836079, by rfl⟩ : syracuseStep 2229545 = 1672159) B1672159
theorem B3344219 : Blo 1486063 3344219 := bstep (se 1 (by rfl) ⟨2508164, by rfl⟩ : syracuseStep 3344219 = 5016329) B5016329
theorem B36153215 : Blo 1486063 36153215 := bstep (se 1 (by rfl) ⟨27114911, by rfl⟩ : syracuseStep 36153215 = 54229823) B54229823
theorem B4237267 : Blo 1486063 4237267 := bstep (se 1 (by rfl) ⟨3177950, by rfl⟩ : syracuseStep 4237267 = 6355901) B6355901
theorem B146581481 : Blo 1486063 146581481 := bstep (se 2 (by rfl) ⟨54968055, by rfl⟩ : syracuseStep 146581481 = 109936111) B109936111
theorem B2230271 : Blo 1486063 2230271 := bstep (se 1 (by rfl) ⟨1672703, by rfl⟩ : syracuseStep 2230271 = 3345407) B3345407
theorem B16943417 : Blo 1486063 16943417 := bstep (se 2 (by rfl) ⟨6353781, by rfl⟩ : syracuseStep 16943417 = 12707563) B12707563
theorem B2230751 : Blo 1486063 2230751 := bstep (se 1 (by rfl) ⟨1673063, by rfl⟩ : syracuseStep 2230751 = 3346127) B3346127
theorem B3345065 : Blo 1486063 3345065 := bstep (se 2 (by rfl) ⟨1254399, by rfl⟩ : syracuseStep 3345065 = 2508799) B2508799
theorem B11299499 : Blo 1486063 11299499 := bstep (se 1 (by rfl) ⟨8474624, by rfl⟩ : syracuseStep 11299499 = 16949249) B16949249
theorem B9527291 : Blo 1486063 9527291 := bstep (se 1 (by rfl) ⟨7145468, by rfl⟩ : syracuseStep 9527291 = 14290937) B14290937
theorem B2231273 : Blo 1486063 2231273 := bstep (se 2 (by rfl) ⟨836727, by rfl⟩ : syracuseStep 2231273 = 1673455) B1673455
theorem B1486183 : Blo 1486063 1486183 := bstep (se 1 (by rfl) ⟨1114637, by rfl⟩ : syracuseStep 1486183 = 2229275) B2229275
theorem B4763519 : Blo 1486063 4763519 := bstep (se 1 (by rfl) ⟨3572639, by rfl⟩ : syracuseStep 4763519 = 7145279) B7145279
theorem B8466515 : Blo 1486063 8466515 := bstep (se 1 (by rfl) ⟨6349886, by rfl⟩ : syracuseStep 8466515 = 12699773) B12699773
theorem B7524575 : Blo 1486063 7524575 := bstep (se 1 (by rfl) ⟨5643431, by rfl⟩ : syracuseStep 7524575 = 11286863) B11286863
theorem B169644359 : Blo 1486063 169644359 := bstep (se 1 (by rfl) ⟨127233269, by rfl⟩ : syracuseStep 169644359 = 254466539) B254466539
theorem B19853723 : Blo 1486063 19853723 := bstep (se 1 (by rfl) ⟨14890292, by rfl⟩ : syracuseStep 19853723 = 29780585) B29780585
theorem B7533161 : Blo 1486063 7533161 := bstep (se 2 (by rfl) ⟨2824935, by rfl⟩ : syracuseStep 7533161 = 5649871) B5649871
theorem B4584671 : Blo 1486063 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B1882855 : Blo 1486063 1882855 := bstep (se 1 (by rfl) ⟨1412141, by rfl⟩ : syracuseStep 1882855 = 2824283) B2824283
theorem B6355817 : Blo 1486063 6355817 := bstep (se 2 (by rfl) ⟨2383431, by rfl⟩ : syracuseStep 6355817 = 4766863) B4766863
theorem B4234123 : Blo 1486063 4234123 := bstep (se 1 (by rfl) ⟨3175592, by rfl⟩ : syracuseStep 4234123 = 6351185) B6351185
theorem B24125039 : Blo 1486063 24125039 := bstep (se 1 (by rfl) ⟨18093779, by rfl⟩ : syracuseStep 24125039 = 36187559) B36187559
theorem B5644343 : Blo 1486063 5644343 := bstep (se 1 (by rfl) ⟨4233257, by rfl⟩ : syracuseStep 5644343 = 8466515) B8466515
theorem B5022107 : Blo 1486063 5022107 := bstep (se 1 (by rfl) ⟨3766580, by rfl⟩ : syracuseStep 5022107 = 7533161) B7533161
theorem B19055195 : Blo 1486063 19055195 := bstep (se 1 (by rfl) ⟨14291396, by rfl⟩ : syracuseStep 19055195 = 28582793) B28582793
theorem B3056447 : Blo 1486063 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B5645497 : Blo 1486063 5645497 := bstep (se 2 (by rfl) ⟨2117061, by rfl⟩ : syracuseStep 5645497 = 4234123) B4234123
theorem B2229479 : Blo 1486063 2229479 := bstep (se 1 (by rfl) ⟨1672109, by rfl⟩ : syracuseStep 2229479 = 3344219) B3344219
theorem B24102143 : Blo 1486063 24102143 := bstep (se 1 (by rfl) ⟨18076607, by rfl⟩ : syracuseStep 24102143 = 36153215) B36153215
theorem B2230043 : Blo 1486063 2230043 := bstep (se 1 (by rfl) ⟨1672532, by rfl⟩ : syracuseStep 2230043 = 3345065) B3345065
theorem B4237211 : Blo 1486063 4237211 := bstep (se 1 (by rfl) ⟨3177908, by rfl⟩ : syracuseStep 4237211 = 6355817) B6355817
theorem B16083359 : Blo 1486063 16083359 := bstep (se 1 (by rfl) ⟨12062519, by rfl⟩ : syracuseStep 16083359 = 24125039) B24125039
theorem B6351527 : Blo 1486063 6351527 := bstep (se 1 (by rfl) ⟨4763645, by rfl⟩ : syracuseStep 6351527 = 9527291) B9527291
theorem B5016383 : Blo 1486063 5016383 := bstep (se 1 (by rfl) ⟨3762287, by rfl⟩ : syracuseStep 5016383 = 7524575) B7524575
theorem B1486363 : Blo 1486063 1486363 := bstep (se 1 (by rfl) ⟨1114772, by rfl⟩ : syracuseStep 1486363 = 2229545) B2229545
theorem B2510473 : Blo 1486063 2510473 := bstep (se 2 (by rfl) ⟨941427, by rfl⟩ : syracuseStep 2510473 = 1882855) B1882855
theorem B1486847 : Blo 1486063 1486847 := bstep (se 1 (by rfl) ⟨1115135, by rfl⟩ : syracuseStep 1486847 = 2230271) B2230271
theorem B1487167 : Blo 1486063 1487167 := bstep (se 1 (by rfl) ⟨1115375, by rfl⟩ : syracuseStep 1487167 = 2230751) B2230751
theorem B7532999 : Blo 1486063 7532999 := bstep (se 1 (by rfl) ⟨5649749, by rfl⟩ : syracuseStep 7532999 = 11299499) B11299499
theorem B1487515 : Blo 1486063 1487515 := bstep (se 1 (by rfl) ⟨1115636, by rfl⟩ : syracuseStep 1487515 = 2231273) B2231273
theorem B3175679 : Blo 1486063 3175679 := bstep (se 1 (by rfl) ⟨2381759, by rfl⟩ : syracuseStep 3175679 = 4763519) B4763519
theorem B5649689 : Blo 1486063 5649689 := bstep (se 2 (by rfl) ⟨2118633, by rfl⟩ : syracuseStep 5649689 = 4237267) B4237267
theorem B13235815 : Blo 1486063 13235815 := bstep (se 1 (by rfl) ⟨9926861, by rfl⟩ : syracuseStep 13235815 = 19853723) B19853723
theorem B396220409 : Blo 1486063 396220409 := bstep (se 2 (by rfl) ⟨148582653, by rfl⟩ : syracuseStep 396220409 = 297165307) B297165307
theorem B452384957 : Blo 1486063 452384957 := bstep (se 3 (by rfl) ⟨84822179, by rfl⟩ : syracuseStep 452384957 = 169644359) B169644359
theorem B97720987 : Blo 1486063 97720987 := bstep (se 1 (by rfl) ⟨73290740, by rfl⟩ : syracuseStep 97720987 = 146581481) B146581481
theorem B11295611 : Blo 1486063 11295611 := bstep (se 1 (by rfl) ⟨8471708, by rfl⟩ : syracuseStep 11295611 = 16943417) B16943417
theorem B5021999 : Blo 1486063 5021999 := bstep (se 1 (by rfl) ⟨3766499, by rfl⟩ : syracuseStep 5021999 = 7532999) B7532999
theorem B130294649 : Blo 1486063 130294649 := bstep (se 2 (by rfl) ⟨48860493, by rfl⟩ : syracuseStep 130294649 = 97720987) B97720987
theorem B3344255 : Blo 1486063 3344255 := bstep (se 1 (by rfl) ⟨2508191, by rfl⟩ : syracuseStep 3344255 = 5016383) B5016383
theorem B7530407 : Blo 1486063 7530407 := bstep (se 1 (by rfl) ⟨5647805, by rfl⟩ : syracuseStep 7530407 = 11295611) B11295611
theorem B17647753 : Blo 1486063 17647753 := bstep (se 2 (by rfl) ⟨6617907, by rfl⟩ : syracuseStep 17647753 = 13235815) B13235815
theorem B3762895 : Blo 1486063 3762895 := bstep (se 1 (by rfl) ⟨2822171, by rfl⟩ : syracuseStep 3762895 = 5644343) B5644343
theorem B1486319 : Blo 1486063 1486319 := bstep (se 1 (by rfl) ⟨1114739, by rfl⟩ : syracuseStep 1486319 = 2229479) B2229479
theorem B16068095 : Blo 1486063 16068095 := bstep (se 1 (by rfl) ⟨12051071, by rfl⟩ : syracuseStep 16068095 = 24102143) B24102143
theorem B2117119 : Blo 1486063 2117119 := bstep (se 1 (by rfl) ⟨1587839, by rfl⟩ : syracuseStep 2117119 = 3175679) B3175679
theorem B1486695 : Blo 1486063 1486695 := bstep (se 1 (by rfl) ⟨1115021, by rfl⟩ : syracuseStep 1486695 = 2230043) B2230043
theorem B264146939 : Blo 1486063 264146939 := bstep (se 1 (by rfl) ⟨198110204, by rfl⟩ : syracuseStep 264146939 = 396220409) B396220409
theorem B3347297 : Blo 1486063 3347297 := bstep (se 2 (by rfl) ⟨1255236, by rfl⟩ : syracuseStep 3347297 = 2510473) B2510473
theorem B3348071 : Blo 1486063 3348071 := bstep (se 1 (by rfl) ⟨2511053, by rfl⟩ : syracuseStep 3348071 = 5022107) B5022107
theorem B12703463 : Blo 1486063 12703463 := bstep (se 1 (by rfl) ⟨9527597, by rfl⟩ : syracuseStep 12703463 = 19055195) B19055195
theorem B1206359885 : Blo 1486063 1206359885 := bstep (se 3 (by rfl) ⟨226192478, by rfl⟩ : syracuseStep 1206359885 = 452384957) B452384957
theorem B2037631 : Blo 1486063 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B3766459 : Blo 1486063 3766459 := bstep (se 1 (by rfl) ⟨2824844, by rfl⟩ : syracuseStep 3766459 = 5649689) B5649689
theorem B2824807 : Blo 1486063 2824807 := bstep (se 1 (by rfl) ⟨2118605, by rfl⟩ : syracuseStep 2824807 = 4237211) B4237211
theorem B7527329 : Blo 1486063 7527329 := bstep (se 2 (by rfl) ⟨2822748, by rfl⟩ : syracuseStep 7527329 = 5645497) B5645497
theorem B10722239 : Blo 1486063 10722239 := bstep (se 1 (by rfl) ⟨8041679, by rfl⟩ : syracuseStep 10722239 = 16083359) B16083359
theorem B4234351 : Blo 1486063 4234351 := bstep (se 1 (by rfl) ⟨3175763, by rfl⟩ : syracuseStep 4234351 = 6351527) B6351527
theorem B5021945 : Blo 1486063 5021945 := bstep (se 2 (by rfl) ⟨1883229, by rfl⟩ : syracuseStep 5021945 = 3766459) B3766459
theorem B2229503 : Blo 1486063 2229503 := bstep (se 1 (by rfl) ⟨1672127, by rfl⟩ : syracuseStep 2229503 = 3344255) B3344255
theorem B5645801 : Blo 1486063 5645801 := bstep (se 2 (by rfl) ⟨2117175, by rfl⟩ : syracuseStep 5645801 = 4234351) B4234351
theorem B176097959 : Blo 1486063 176097959 := bstep (se 1 (by rfl) ⟨132073469, by rfl⟩ : syracuseStep 176097959 = 264146939) B264146939
theorem B23530337 : Blo 1486063 23530337 := bstep (se 2 (by rfl) ⟨8823876, by rfl⟩ : syracuseStep 23530337 = 17647753) B17647753
theorem B2231531 : Blo 1486063 2231531 := bstep (se 1 (by rfl) ⟨1673648, by rfl⟩ : syracuseStep 2231531 = 3347297) B3347297
theorem B86863099 : Blo 1486063 86863099 := bstep (se 1 (by rfl) ⟨65147324, by rfl⟩ : syracuseStep 86863099 = 130294649) B130294649
theorem B5017193 : Blo 1486063 5017193 := bstep (se 2 (by rfl) ⟨1881447, by rfl⟩ : syracuseStep 5017193 = 3762895) B3762895
theorem B2232047 : Blo 1486063 2232047 := bstep (se 1 (by rfl) ⟨1674035, by rfl⟩ : syracuseStep 2232047 = 3348071) B3348071
theorem B5018219 : Blo 1486063 5018219 := bstep (se 1 (by rfl) ⟨3763664, by rfl⟩ : syracuseStep 5018219 = 7527329) B7527329
theorem B7148159 : Blo 1486063 7148159 := bstep (se 1 (by rfl) ⟨5361119, by rfl⟩ : syracuseStep 7148159 = 10722239) B10722239
theorem B2822825 : Blo 1486063 2822825 := bstep (se 2 (by rfl) ⟨1058559, by rfl⟩ : syracuseStep 2822825 = 2117119) B2117119
theorem B10712063 : Blo 1486063 10712063 := bstep (se 1 (by rfl) ⟨8034047, by rfl⟩ : syracuseStep 10712063 = 16068095) B16068095
theorem B2716841 : Blo 1486063 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B3347999 : Blo 1486063 3347999 := bstep (se 1 (by rfl) ⟨2510999, by rfl⟩ : syracuseStep 3347999 = 5021999) B5021999
theorem B3766409 : Blo 1486063 3766409 := bstep (se 2 (by rfl) ⟨1412403, by rfl⟩ : syracuseStep 3766409 = 2824807) B2824807
theorem B8468975 : Blo 1486063 8468975 := bstep (se 1 (by rfl) ⟨6351731, by rfl⟩ : syracuseStep 8468975 = 12703463) B12703463
theorem B804239923 : Blo 1486063 804239923 := bstep (se 1 (by rfl) ⟨603179942, by rfl⟩ : syracuseStep 804239923 = 1206359885) B1206359885
theorem B5020271 : Blo 1486063 5020271 := bstep (se 1 (by rfl) ⟨3765203, by rfl⟩ : syracuseStep 5020271 = 7530407) B7530407
theorem B5645983 : Blo 1486063 5645983 := bstep (se 1 (by rfl) ⟨4234487, by rfl⟩ : syracuseStep 5645983 = 8468975) B8468975
theorem B3344795 : Blo 1486063 3344795 := bstep (se 1 (by rfl) ⟨2508596, by rfl⟩ : syracuseStep 3344795 = 5017193) B5017193
theorem B3345479 : Blo 1486063 3345479 := bstep (se 1 (by rfl) ⟨2509109, by rfl⟩ : syracuseStep 3345479 = 5018219) B5018219
theorem B7244909 : Blo 1486063 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B1072319897 : Blo 1486063 1072319897 := bstep (se 2 (by rfl) ⟨402119961, by rfl⟩ : syracuseStep 1072319897 = 804239923) B804239923
theorem B1486335 : Blo 1486063 1486335 := bstep (se 1 (by rfl) ⟨1114751, by rfl⟩ : syracuseStep 1486335 = 2229503) B2229503
theorem B3763867 : Blo 1486063 3763867 := bstep (se 1 (by rfl) ⟨2822900, by rfl⟩ : syracuseStep 3763867 = 5645801) B5645801
theorem B2231999 : Blo 1486063 2231999 := bstep (se 1 (by rfl) ⟨1673999, by rfl⟩ : syracuseStep 2231999 = 3347999) B3347999
theorem B2510939 : Blo 1486063 2510939 := bstep (se 1 (by rfl) ⟨1883204, by rfl⟩ : syracuseStep 2510939 = 3766409) B3766409
theorem B3346847 : Blo 1486063 3346847 := bstep (se 1 (by rfl) ⟨2510135, by rfl⟩ : syracuseStep 3346847 = 5020271) B5020271
theorem B1487687 : Blo 1486063 1487687 := bstep (se 1 (by rfl) ⟨1115765, by rfl⟩ : syracuseStep 1487687 = 2231531) B2231531
theorem B1488031 : Blo 1486063 1488031 := bstep (se 1 (by rfl) ⟨1116023, by rfl⟩ : syracuseStep 1488031 = 2232047) B2232047
theorem B3347963 : Blo 1486063 3347963 := bstep (se 1 (by rfl) ⟨2510972, by rfl⟩ : syracuseStep 3347963 = 5021945) B5021945
theorem B4765439 : Blo 1486063 4765439 := bstep (se 1 (by rfl) ⟨3574079, by rfl⟩ : syracuseStep 4765439 = 7148159) B7148159
theorem B1881883 : Blo 1486063 1881883 := bstep (se 1 (by rfl) ⟨1411412, by rfl⟩ : syracuseStep 1881883 = 2822825) B2822825
theorem B7141375 : Blo 1486063 7141375 := bstep (se 1 (by rfl) ⟨5356031, by rfl⟩ : syracuseStep 7141375 = 10712063) B10712063
theorem B115817465 : Blo 1486063 115817465 := bstep (se 2 (by rfl) ⟨43431549, by rfl⟩ : syracuseStep 115817465 = 86863099) B86863099
theorem B117398639 : Blo 1486063 117398639 := bstep (se 1 (by rfl) ⟨88048979, by rfl⟩ : syracuseStep 117398639 = 176097959) B176097959
theorem B15686891 : Blo 1486063 15686891 := bstep (se 1 (by rfl) ⟨11765168, by rfl⟩ : syracuseStep 15686891 = 23530337) B23530337
theorem B2229863 : Blo 1486063 2229863 := bstep (se 1 (by rfl) ⟨1672397, by rfl⟩ : syracuseStep 2229863 = 3344795) B3344795
theorem B77211643 : Blo 1486063 77211643 := bstep (se 1 (by rfl) ⟨57908732, by rfl⟩ : syracuseStep 77211643 = 115817465) B115817465
theorem B12707837 : Blo 1486063 12707837 := bstep (se 3 (by rfl) ⟨2382719, by rfl⟩ : syracuseStep 12707837 = 4765439) B4765439
theorem B2230319 : Blo 1486063 2230319 := bstep (se 1 (by rfl) ⟨1672739, by rfl⟩ : syracuseStep 2230319 = 3345479) B3345479
theorem B2509177 : Blo 1486063 2509177 := bstep (se 2 (by rfl) ⟨940941, by rfl⟩ : syracuseStep 2509177 = 1881883) B1881883
theorem B9521833 : Blo 1486063 9521833 := bstep (se 2 (by rfl) ⟨3570687, by rfl⟩ : syracuseStep 9521833 = 7141375) B7141375
theorem B1673959 : Blo 1486063 1673959 := bstep (se 1 (by rfl) ⟨1255469, by rfl⟩ : syracuseStep 1673959 = 2510939) B2510939
theorem B2231231 : Blo 1486063 2231231 := bstep (se 1 (by rfl) ⟨1673423, by rfl⟩ : syracuseStep 2231231 = 3346847) B3346847
theorem B2231975 : Blo 1486063 2231975 := bstep (se 1 (by rfl) ⟨1673981, by rfl⟩ : syracuseStep 2231975 = 3347963) B3347963
theorem B4829939 : Blo 1486063 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B10457927 : Blo 1486063 10457927 := bstep (se 1 (by rfl) ⟨7843445, by rfl⟩ : syracuseStep 10457927 = 15686891) B15686891
theorem B5018489 : Blo 1486063 5018489 := bstep (se 2 (by rfl) ⟨1881933, by rfl⟩ : syracuseStep 5018489 = 3763867) B3763867
theorem B714879931 : Blo 1486063 714879931 := bstep (se 1 (by rfl) ⟨536159948, by rfl⟩ : syracuseStep 714879931 = 1072319897) B1072319897
theorem B1487999 : Blo 1486063 1487999 := bstep (se 1 (by rfl) ⟨1115999, by rfl⟩ : syracuseStep 1487999 = 2231999) B2231999
theorem B78265759 : Blo 1486063 78265759 := bstep (se 1 (by rfl) ⟨58699319, by rfl⟩ : syracuseStep 78265759 = 117398639) B117398639
theorem B7527977 : Blo 1486063 7527977 := bstep (se 2 (by rfl) ⟨2822991, by rfl⟩ : syracuseStep 7527977 = 5645983) B5645983
theorem B3219959 : Blo 1486063 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B6971951 : Blo 1486063 6971951 := bstep (se 1 (by rfl) ⟨5228963, by rfl⟩ : syracuseStep 6971951 = 10457927) B10457927
theorem B953173241 : Blo 1486063 953173241 := bstep (se 2 (by rfl) ⟨357439965, by rfl⟩ : syracuseStep 953173241 = 714879931) B714879931
theorem B8471891 : Blo 1486063 8471891 := bstep (se 1 (by rfl) ⟨6353918, by rfl⟩ : syracuseStep 8471891 = 12707837) B12707837
theorem B3345569 : Blo 1486063 3345569 := bstep (se 2 (by rfl) ⟨1254588, by rfl⟩ : syracuseStep 3345569 = 2509177) B2509177
theorem B3345659 : Blo 1486063 3345659 := bstep (se 1 (by rfl) ⟨2509244, by rfl⟩ : syracuseStep 3345659 = 5018489) B5018489
theorem B2231945 : Blo 1486063 2231945 := bstep (se 2 (by rfl) ⟨836979, by rfl⟩ : syracuseStep 2231945 = 1673959) B1673959
theorem B1486575 : Blo 1486063 1486575 := bstep (se 1 (by rfl) ⟨1114931, by rfl⟩ : syracuseStep 1486575 = 2229863) B2229863
theorem B1486879 : Blo 1486063 1486879 := bstep (se 1 (by rfl) ⟨1115159, by rfl⟩ : syracuseStep 1486879 = 2230319) B2230319
theorem B104354345 : Blo 1486063 104354345 := bstep (se 2 (by rfl) ⟨39132879, by rfl⟩ : syracuseStep 104354345 = 78265759) B78265759
theorem B1487487 : Blo 1486063 1487487 := bstep (se 1 (by rfl) ⟨1115615, by rfl⟩ : syracuseStep 1487487 = 2231231) B2231231
theorem B5018651 : Blo 1486063 5018651 := bstep (se 1 (by rfl) ⟨3763988, by rfl⟩ : syracuseStep 5018651 = 7527977) B7527977
theorem B1487983 : Blo 1486063 1487983 := bstep (se 1 (by rfl) ⟨1115987, by rfl⟩ : syracuseStep 1487983 = 2231975) B2231975
theorem B12695777 : Blo 1486063 12695777 := bstep (se 2 (by rfl) ⟨4760916, by rfl⟩ : syracuseStep 12695777 = 9521833) B9521833
theorem B102948857 : Blo 1486063 102948857 := bstep (se 2 (by rfl) ⟨38605821, by rfl⟩ : syracuseStep 102948857 = 77211643) B77211643
theorem B8586557 : Blo 1486063 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B8463851 : Blo 1486063 8463851 := bstep (se 1 (by rfl) ⟨6347888, by rfl⟩ : syracuseStep 8463851 = 12695777) B12695777
theorem B635448827 : Blo 1486063 635448827 := bstep (se 1 (by rfl) ⟨476586620, by rfl⟩ : syracuseStep 635448827 = 953173241) B953173241
theorem B2230379 : Blo 1486063 2230379 := bstep (se 1 (by rfl) ⟨1672784, by rfl⟩ : syracuseStep 2230379 = 3345569) B3345569
theorem B2230439 : Blo 1486063 2230439 := bstep (se 1 (by rfl) ⟨1672829, by rfl⟩ : syracuseStep 2230439 = 3345659) B3345659
theorem B69569563 : Blo 1486063 69569563 := bstep (se 1 (by rfl) ⟨52177172, by rfl⟩ : syracuseStep 69569563 = 104354345) B104354345
theorem B3345767 : Blo 1486063 3345767 := bstep (se 1 (by rfl) ⟨2509325, by rfl⟩ : syracuseStep 3345767 = 5018651) B5018651
theorem B5647927 : Blo 1486063 5647927 := bstep (se 1 (by rfl) ⟨4235945, by rfl⟩ : syracuseStep 5647927 = 8471891) B8471891
theorem B18591869 : Blo 1486063 18591869 := bstep (se 3 (by rfl) ⟨3485975, by rfl⟩ : syracuseStep 18591869 = 6971951) B6971951
theorem B1487963 : Blo 1486063 1487963 := bstep (se 1 (by rfl) ⟨1115972, by rfl⟩ : syracuseStep 1487963 = 2231945) B2231945
theorem B68632571 : Blo 1486063 68632571 := bstep (se 1 (by rfl) ⟨51474428, by rfl⟩ : syracuseStep 68632571 = 102948857) B102948857
theorem B12394579 : Blo 1486063 12394579 := bstep (se 1 (by rfl) ⟨9295934, by rfl⟩ : syracuseStep 12394579 = 18591869) B18591869
theorem B92759417 : Blo 1486063 92759417 := bstep (se 2 (by rfl) ⟨34784781, by rfl⟩ : syracuseStep 92759417 = 69569563) B69569563
theorem B7530569 : Blo 1486063 7530569 := bstep (se 2 (by rfl) ⟨2823963, by rfl⟩ : syracuseStep 7530569 = 5647927) B5647927
theorem B2230511 : Blo 1486063 2230511 := bstep (se 1 (by rfl) ⟨1672883, by rfl⟩ : syracuseStep 2230511 = 3345767) B3345767
theorem B45755047 : Blo 1486063 45755047 := bstep (se 1 (by rfl) ⟨34316285, by rfl⟩ : syracuseStep 45755047 = 68632571) B68632571
theorem B1486919 : Blo 1486063 1486919 := bstep (se 1 (by rfl) ⟨1115189, by rfl⟩ : syracuseStep 1486919 = 2230379) B2230379
theorem B1486959 : Blo 1486063 1486959 := bstep (se 1 (by rfl) ⟨1115219, by rfl⟩ : syracuseStep 1486959 = 2230439) B2230439
theorem B5724371 : Blo 1486063 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B5642567 : Blo 1486063 5642567 := bstep (se 1 (by rfl) ⟨4231925, by rfl⟩ : syracuseStep 5642567 = 8463851) B8463851
theorem B423632551 : Blo 1486063 423632551 := bstep (se 1 (by rfl) ⟨317724413, by rfl⟩ : syracuseStep 423632551 = 635448827) B635448827
theorem B3761711 : Blo 1486063 3761711 := bstep (se 1 (by rfl) ⟨2821283, by rfl⟩ : syracuseStep 3761711 = 5642567) B5642567
theorem B16526105 : Blo 1486063 16526105 := bstep (se 2 (by rfl) ⟨6197289, by rfl⟩ : syracuseStep 16526105 = 12394579) B12394579
theorem B244026917 : Blo 1486063 244026917 := bstep (se 4 (by rfl) ⟨22877523, by rfl⟩ : syracuseStep 244026917 = 45755047) B45755047
theorem B1487007 : Blo 1486063 1487007 := bstep (se 1 (by rfl) ⟨1115255, by rfl⟩ : syracuseStep 1487007 = 2230511) B2230511
theorem B564843401 : Blo 1486063 564843401 := bstep (se 2 (by rfl) ⟨211816275, by rfl⟩ : syracuseStep 564843401 = 423632551) B423632551
theorem B61839611 : Blo 1486063 61839611 := bstep (se 1 (by rfl) ⟨46379708, by rfl⟩ : syracuseStep 61839611 = 92759417) B92759417
theorem B5020379 : Blo 1486063 5020379 := bstep (se 1 (by rfl) ⟨3765284, by rfl⟩ : syracuseStep 5020379 = 7530569) B7530569
theorem B3816247 : Blo 1486063 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B376562267 : Blo 1486063 376562267 := bstep (se 1 (by rfl) ⟨282421700, by rfl⟩ : syracuseStep 376562267 = 564843401) B564843401
theorem B2507807 : Blo 1486063 2507807 := bstep (se 1 (by rfl) ⟨1880855, by rfl⟩ : syracuseStep 2507807 = 3761711) B3761711
theorem B5088329 : Blo 1486063 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B41226407 : Blo 1486063 41226407 := bstep (se 1 (by rfl) ⟨30919805, by rfl⟩ : syracuseStep 41226407 = 61839611) B61839611
theorem B3346919 : Blo 1486063 3346919 := bstep (se 1 (by rfl) ⟨2510189, by rfl⟩ : syracuseStep 3346919 = 5020379) B5020379
theorem B11017403 : Blo 1486063 11017403 := bstep (se 1 (by rfl) ⟨8263052, by rfl⟩ : syracuseStep 11017403 = 16526105) B16526105
theorem B162684611 : Blo 1486063 162684611 := bstep (se 1 (by rfl) ⟨122013458, by rfl⟩ : syracuseStep 162684611 = 244026917) B244026917
theorem B27484271 : Blo 1486063 27484271 := bstep (se 1 (by rfl) ⟨20613203, by rfl⟩ : syracuseStep 27484271 = 41226407) B41226407
theorem B1671871 : Blo 1486063 1671871 := bstep (se 1 (by rfl) ⟨1253903, by rfl⟩ : syracuseStep 1671871 = 2507807) B2507807
theorem B3392219 : Blo 1486063 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B108456407 : Blo 1486063 108456407 := bstep (se 1 (by rfl) ⟨81342305, by rfl⟩ : syracuseStep 108456407 = 162684611) B162684611
theorem B2231279 : Blo 1486063 2231279 := bstep (se 1 (by rfl) ⟨1673459, by rfl⟩ : syracuseStep 2231279 = 3346919) B3346919
theorem B7344935 : Blo 1486063 7344935 := bstep (se 1 (by rfl) ⟨5508701, by rfl⟩ : syracuseStep 7344935 = 11017403) B11017403
theorem B251041511 : Blo 1486063 251041511 := bstep (se 1 (by rfl) ⟨188281133, by rfl⟩ : syracuseStep 251041511 = 376562267) B376562267
theorem B2229161 : Blo 1486063 2229161 := bstep (se 2 (by rfl) ⟨835935, by rfl⟩ : syracuseStep 2229161 = 1671871) B1671871
theorem B72304271 : Blo 1486063 72304271 := bstep (se 1 (by rfl) ⟨54228203, by rfl⟩ : syracuseStep 72304271 = 108456407) B108456407
theorem B9045917 : Blo 1486063 9045917 := bstep (se 3 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 9045917 = 3392219) B3392219
theorem B1487519 : Blo 1486063 1487519 := bstep (se 1 (by rfl) ⟨1115639, by rfl⟩ : syracuseStep 1487519 = 2231279) B2231279
theorem B18322847 : Blo 1486063 18322847 := bstep (se 1 (by rfl) ⟨13742135, by rfl⟩ : syracuseStep 18322847 = 27484271) B27484271
theorem B4896623 : Blo 1486063 4896623 := bstep (se 1 (by rfl) ⟨3672467, by rfl⟩ : syracuseStep 4896623 = 7344935) B7344935
theorem B167361007 : Blo 1486063 167361007 := bstep (se 1 (by rfl) ⟨125520755, by rfl⟩ : syracuseStep 167361007 = 251041511) B251041511
theorem B12215231 : Blo 1486063 12215231 := bstep (se 1 (by rfl) ⟨9161423, by rfl⟩ : syracuseStep 12215231 = 18322847) B18322847
theorem B48202847 : Blo 1486063 48202847 := bstep (se 1 (by rfl) ⟨36152135, by rfl⟩ : syracuseStep 48202847 = 72304271) B72304271
theorem B6030611 : Blo 1486063 6030611 := bstep (se 1 (by rfl) ⟨4522958, by rfl⟩ : syracuseStep 6030611 = 9045917) B9045917
theorem B1486107 : Blo 1486063 1486107 := bstep (se 1 (by rfl) ⟨1114580, by rfl⟩ : syracuseStep 1486107 = 2229161) B2229161
theorem B223148009 : Blo 1486063 223148009 := bstep (se 2 (by rfl) ⟨83680503, by rfl⟩ : syracuseStep 223148009 = 167361007) B167361007
theorem B13057661 : Blo 1486063 13057661 := bstep (se 3 (by rfl) ⟨2448311, by rfl⟩ : syracuseStep 13057661 = 4896623) B4896623
theorem B8143487 : Blo 1486063 8143487 := bstep (se 1 (by rfl) ⟨6107615, by rfl⟩ : syracuseStep 8143487 = 12215231) B12215231
theorem B8705107 : Blo 1486063 8705107 := bstep (se 1 (by rfl) ⟨6528830, by rfl⟩ : syracuseStep 8705107 = 13057661) B13057661
theorem B32135231 : Blo 1486063 32135231 := bstep (se 1 (by rfl) ⟨24101423, by rfl⟩ : syracuseStep 32135231 = 48202847) B48202847
theorem B4020407 : Blo 1486063 4020407 := bstep (se 1 (by rfl) ⟨3015305, by rfl⟩ : syracuseStep 4020407 = 6030611) B6030611
theorem B148765339 : Blo 1486063 148765339 := bstep (se 1 (by rfl) ⟨111574004, by rfl⟩ : syracuseStep 148765339 = 223148009) B223148009
theorem B198353785 : Blo 1486063 198353785 := bstep (se 2 (by rfl) ⟨74382669, by rfl⟩ : syracuseStep 198353785 = 148765339) B148765339
theorem B21423487 : Blo 1486063 21423487 := bstep (se 1 (by rfl) ⟨16067615, by rfl⟩ : syracuseStep 21423487 = 32135231) B32135231
theorem B2680271 : Blo 1486063 2680271 := bstep (se 1 (by rfl) ⟨2010203, by rfl⟩ : syracuseStep 2680271 = 4020407) B4020407
theorem B5428991 : Blo 1486063 5428991 := bstep (se 1 (by rfl) ⟨4071743, by rfl⟩ : syracuseStep 5428991 = 8143487) B8143487
theorem B11606809 : Blo 1486063 11606809 := bstep (se 2 (by rfl) ⟨4352553, by rfl⟩ : syracuseStep 11606809 = 8705107) B8705107
theorem B15475745 : Blo 1486063 15475745 := bstep (se 2 (by rfl) ⟨5803404, by rfl⟩ : syracuseStep 15475745 = 11606809) B11606809
theorem B264471713 : Blo 1486063 264471713 := bstep (se 2 (by rfl) ⟨99176892, by rfl⟩ : syracuseStep 264471713 = 198353785) B198353785
theorem B14477309 : Blo 1486063 14477309 := bstep (se 3 (by rfl) ⟨2714495, by rfl⟩ : syracuseStep 14477309 = 5428991) B5428991
theorem B28564649 : Blo 1486063 28564649 := bstep (se 2 (by rfl) ⟨10711743, by rfl⟩ : syracuseStep 28564649 = 21423487) B21423487
theorem B28589557 : Blo 1486063 28589557 := bstep (se 5 (by rfl) ⟨1340135, by rfl⟩ : syracuseStep 28589557 = 2680271) B2680271
theorem B9651539 : Blo 1486063 9651539 := bstep (se 1 (by rfl) ⟨7238654, by rfl⟩ : syracuseStep 9651539 = 14477309) B14477309
theorem B38119409 : Blo 1486063 38119409 := bstep (se 2 (by rfl) ⟨14294778, by rfl⟩ : syracuseStep 38119409 = 28589557) B28589557
theorem B19043099 : Blo 1486063 19043099 := bstep (se 1 (by rfl) ⟨14282324, by rfl⟩ : syracuseStep 19043099 = 28564649) B28564649
theorem B41268653 : Blo 1486063 41268653 := bstep (se 3 (by rfl) ⟨7737872, by rfl⟩ : syracuseStep 41268653 = 15475745) B15475745
theorem B176314475 : Blo 1486063 176314475 := bstep (se 1 (by rfl) ⟨132235856, by rfl⟩ : syracuseStep 176314475 = 264471713) B264471713
theorem B25412939 : Blo 1486063 25412939 := bstep (se 1 (by rfl) ⟨19059704, by rfl⟩ : syracuseStep 25412939 = 38119409) B38119409
theorem B440198965 : Blo 1486063 440198965 := bstep (se 5 (by rfl) ⟨20634326, by rfl⟩ : syracuseStep 440198965 = 41268653) B41268653
theorem B6434359 : Blo 1486063 6434359 := bstep (se 1 (by rfl) ⟨4825769, by rfl⟩ : syracuseStep 6434359 = 9651539) B9651539
theorem B117542983 : Blo 1486063 117542983 := bstep (se 1 (by rfl) ⟨88157237, by rfl⟩ : syracuseStep 117542983 = 176314475) B176314475
theorem B12695399 : Blo 1486063 12695399 := bstep (se 1 (by rfl) ⟨9521549, by rfl⟩ : syracuseStep 12695399 = 19043099) B19043099
theorem B16941959 : Blo 1486063 16941959 := bstep (se 1 (by rfl) ⟨12706469, by rfl⟩ : syracuseStep 16941959 = 25412939) B25412939
theorem B137266325 : Blo 1486063 137266325 := bstep (se 6 (by rfl) ⟨3217179, by rfl⟩ : syracuseStep 137266325 = 6434359) B6434359
theorem B8463599 : Blo 1486063 8463599 := bstep (se 1 (by rfl) ⟨6347699, by rfl⟩ : syracuseStep 8463599 = 12695399) B12695399
theorem B156723977 : Blo 1486063 156723977 := bstep (se 2 (by rfl) ⟨58771491, by rfl⟩ : syracuseStep 156723977 = 117542983) B117542983
theorem B586931953 : Blo 1486063 586931953 := bstep (se 2 (by rfl) ⟨220099482, by rfl⟩ : syracuseStep 586931953 = 440198965) B440198965
theorem B104482651 : Blo 1486063 104482651 := bstep (se 1 (by rfl) ⟨78361988, by rfl⟩ : syracuseStep 104482651 = 156723977) B156723977
theorem B782575937 : Blo 1486063 782575937 := bstep (se 2 (by rfl) ⟨293465976, by rfl⟩ : syracuseStep 782575937 = 586931953) B586931953
theorem B11294639 : Blo 1486063 11294639 := bstep (se 1 (by rfl) ⟨8470979, by rfl⟩ : syracuseStep 11294639 = 16941959) B16941959
theorem B91510883 : Blo 1486063 91510883 := bstep (se 1 (by rfl) ⟨68633162, by rfl⟩ : syracuseStep 91510883 = 137266325) B137266325
theorem B5642399 : Blo 1486063 5642399 := bstep (se 1 (by rfl) ⟨4231799, by rfl⟩ : syracuseStep 5642399 = 8463599) B8463599
theorem B7529759 : Blo 1486063 7529759 := bstep (se 1 (by rfl) ⟨5647319, by rfl⟩ : syracuseStep 7529759 = 11294639) B11294639
theorem B61007255 : Blo 1486063 61007255 := bstep (se 1 (by rfl) ⟨45755441, by rfl⟩ : syracuseStep 61007255 = 91510883) B91510883
theorem B3761599 : Blo 1486063 3761599 := bstep (se 1 (by rfl) ⟨2821199, by rfl⟩ : syracuseStep 3761599 = 5642399) B5642399
theorem B521717291 : Blo 1486063 521717291 := bstep (se 1 (by rfl) ⟨391287968, by rfl⟩ : syracuseStep 521717291 = 782575937) B782575937
theorem B139310201 : Blo 1486063 139310201 := bstep (se 2 (by rfl) ⟨52241325, by rfl⟩ : syracuseStep 139310201 = 104482651) B104482651
theorem B92873467 : Blo 1486063 92873467 := bstep (se 1 (by rfl) ⟨69655100, by rfl⟩ : syracuseStep 92873467 = 139310201) B139310201
theorem B5015465 : Blo 1486063 5015465 := bstep (se 2 (by rfl) ⟨1880799, by rfl⟩ : syracuseStep 5015465 = 3761599) B3761599
theorem B347811527 : Blo 1486063 347811527 := bstep (se 1 (by rfl) ⟨260858645, by rfl⟩ : syracuseStep 347811527 = 521717291) B521717291
theorem B5019839 : Blo 1486063 5019839 := bstep (se 1 (by rfl) ⟨3764879, by rfl⟩ : syracuseStep 5019839 = 7529759) B7529759
theorem B40671503 : Blo 1486063 40671503 := bstep (se 1 (by rfl) ⟨30503627, by rfl⟩ : syracuseStep 40671503 = 61007255) B61007255
theorem B123831289 : Blo 1486063 123831289 := bstep (se 2 (by rfl) ⟨46436733, by rfl⟩ : syracuseStep 123831289 = 92873467) B92873467
theorem B3343643 : Blo 1486063 3343643 := bstep (se 1 (by rfl) ⟨2507732, by rfl⟩ : syracuseStep 3343643 = 5015465) B5015465
theorem B3346559 : Blo 1486063 3346559 := bstep (se 1 (by rfl) ⟨2509919, by rfl⟩ : syracuseStep 3346559 = 5019839) B5019839
theorem B27114335 : Blo 1486063 27114335 := bstep (se 1 (by rfl) ⟨20335751, by rfl⟩ : syracuseStep 27114335 = 40671503) B40671503
theorem B927497405 : Blo 1486063 927497405 := bstep (se 3 (by rfl) ⟨173905763, by rfl⟩ : syracuseStep 927497405 = 347811527) B347811527
theorem B2229095 : Blo 1486063 2229095 := bstep (se 1 (by rfl) ⟨1671821, by rfl⟩ : syracuseStep 2229095 = 3343643) B3343643
theorem B2231039 : Blo 1486063 2231039 := bstep (se 1 (by rfl) ⟨1673279, by rfl⟩ : syracuseStep 2231039 = 3346559) B3346559
theorem B18076223 : Blo 1486063 18076223 := bstep (se 1 (by rfl) ⟨13557167, by rfl⟩ : syracuseStep 18076223 = 27114335) B27114335
theorem B165108385 : Blo 1486063 165108385 := bstep (se 2 (by rfl) ⟨61915644, by rfl⟩ : syracuseStep 165108385 = 123831289) B123831289
theorem B618331603 : Blo 1486063 618331603 := bstep (se 1 (by rfl) ⟨463748702, by rfl⟩ : syracuseStep 618331603 = 927497405) B927497405
theorem B12050815 : Blo 1486063 12050815 := bstep (se 1 (by rfl) ⟨9038111, by rfl⟩ : syracuseStep 12050815 = 18076223) B18076223
theorem B220144513 : Blo 1486063 220144513 := bstep (se 2 (by rfl) ⟨82554192, by rfl⟩ : syracuseStep 220144513 = 165108385) B165108385
theorem B1486063 : Blo 1486063 1486063 := bstep (se 1 (by rfl) ⟨1114547, by rfl⟩ : syracuseStep 1486063 = 2229095) B2229095
theorem B1487359 : Blo 1486063 1487359 := bstep (se 1 (by rfl) ⟨1115519, by rfl⟩ : syracuseStep 1487359 = 2231039) B2231039
theorem B824442137 : Blo 1486063 824442137 := bstep (se 2 (by rfl) ⟨309165801, by rfl⟩ : syracuseStep 824442137 = 618331603) B618331603
theorem B549628091 : Blo 1486063 549628091 := bstep (se 1 (by rfl) ⟨412221068, by rfl⟩ : syracuseStep 549628091 = 824442137) B824442137
theorem B16067753 : Blo 1486063 16067753 := bstep (se 2 (by rfl) ⟨6025407, by rfl⟩ : syracuseStep 16067753 = 12050815) B12050815
theorem B293526017 : Blo 1486063 293526017 := bstep (se 2 (by rfl) ⟨110072256, by rfl⟩ : syracuseStep 293526017 = 220144513) B220144513
theorem B195684011 : Blo 1486063 195684011 := bstep (se 1 (by rfl) ⟨146763008, by rfl⟩ : syracuseStep 195684011 = 293526017) B293526017
theorem B10711835 : Blo 1486063 10711835 := bstep (se 1 (by rfl) ⟨8033876, by rfl⟩ : syracuseStep 10711835 = 16067753) B16067753
theorem B366418727 : Blo 1486063 366418727 := bstep (se 1 (by rfl) ⟨274814045, by rfl⟩ : syracuseStep 366418727 = 549628091) B549628091
theorem B244279151 : Blo 1486063 244279151 := bstep (se 1 (by rfl) ⟨183209363, by rfl⟩ : syracuseStep 244279151 = 366418727) B366418727
theorem B7141223 : Blo 1486063 7141223 := bstep (se 1 (by rfl) ⟨5355917, by rfl⟩ : syracuseStep 7141223 = 10711835) B10711835
theorem B130456007 : Blo 1486063 130456007 := bstep (se 1 (by rfl) ⟨97842005, by rfl⟩ : syracuseStep 130456007 = 195684011) B195684011
theorem B4760815 : Blo 1486063 4760815 := bstep (se 1 (by rfl) ⟨3570611, by rfl⟩ : syracuseStep 4760815 = 7141223) B7141223
theorem B162852767 : Blo 1486063 162852767 := bstep (se 1 (by rfl) ⟨122139575, by rfl⟩ : syracuseStep 162852767 = 244279151) B244279151
theorem B86970671 : Blo 1486063 86970671 := bstep (se 1 (by rfl) ⟨65228003, by rfl⟩ : syracuseStep 86970671 = 130456007) B130456007
theorem B57980447 : Blo 1486063 57980447 := bstep (se 1 (by rfl) ⟨43485335, by rfl⟩ : syracuseStep 57980447 = 86970671) B86970671
theorem B6347753 : Blo 1486063 6347753 := bstep (se 2 (by rfl) ⟨2380407, by rfl⟩ : syracuseStep 6347753 = 4760815) B4760815
theorem B108568511 : Blo 1486063 108568511 := bstep (se 1 (by rfl) ⟨81426383, by rfl⟩ : syracuseStep 108568511 = 162852767) B162852767
theorem B72379007 : Blo 1486063 72379007 := bstep (se 1 (by rfl) ⟨54284255, by rfl⟩ : syracuseStep 72379007 = 108568511) B108568511
theorem B38653631 : Blo 1486063 38653631 := bstep (se 1 (by rfl) ⟨28990223, by rfl⟩ : syracuseStep 38653631 = 57980447) B57980447
theorem B4231835 : Blo 1486063 4231835 := bstep (se 1 (by rfl) ⟨3173876, by rfl⟩ : syracuseStep 4231835 = 6347753) B6347753
theorem B48252671 : Blo 1486063 48252671 := bstep (se 1 (by rfl) ⟨36189503, by rfl⟩ : syracuseStep 48252671 = 72379007) B72379007
theorem B2821223 : Blo 1486063 2821223 := bstep (se 1 (by rfl) ⟨2115917, by rfl⟩ : syracuseStep 2821223 = 4231835) B4231835
theorem B25769087 : Blo 1486063 25769087 := bstep (se 1 (by rfl) ⟨19326815, by rfl⟩ : syracuseStep 25769087 = 38653631) B38653631
theorem B17179391 : Blo 1486063 17179391 := bstep (se 1 (by rfl) ⟨12884543, by rfl⟩ : syracuseStep 17179391 = 25769087) B25769087
theorem B1880815 : Blo 1486063 1880815 := bstep (se 1 (by rfl) ⟨1410611, by rfl⟩ : syracuseStep 1880815 = 2821223) B2821223
theorem B32168447 : Blo 1486063 32168447 := bstep (se 1 (by rfl) ⟨24126335, by rfl⟩ : syracuseStep 32168447 = 48252671) B48252671
theorem B11452927 : Blo 1486063 11452927 := bstep (se 1 (by rfl) ⟨8589695, by rfl⟩ : syracuseStep 11452927 = 17179391) B17179391
theorem B2507753 : Blo 1486063 2507753 := bstep (se 2 (by rfl) ⟨940407, by rfl⟩ : syracuseStep 2507753 = 1880815) B1880815
theorem B21445631 : Blo 1486063 21445631 := bstep (se 1 (by rfl) ⟨16084223, by rfl⟩ : syracuseStep 21445631 = 32168447) B32168447
theorem B1671835 : Blo 1486063 1671835 := bstep (se 1 (by rfl) ⟨1253876, by rfl⟩ : syracuseStep 1671835 = 2507753) B2507753
theorem B15270569 : Blo 1486063 15270569 := bstep (se 2 (by rfl) ⟨5726463, by rfl⟩ : syracuseStep 15270569 = 11452927) B11452927
theorem B14297087 : Blo 1486063 14297087 := bstep (se 1 (by rfl) ⟨10722815, by rfl⟩ : syracuseStep 14297087 = 21445631) B21445631
theorem B2229113 : Blo 1486063 2229113 := bstep (se 2 (by rfl) ⟨835917, by rfl⟩ : syracuseStep 2229113 = 1671835) B1671835
theorem B9531391 : Blo 1486063 9531391 := bstep (se 1 (by rfl) ⟨7148543, by rfl⟩ : syracuseStep 9531391 = 14297087) B14297087
theorem B10180379 : Blo 1486063 10180379 := bstep (se 1 (by rfl) ⟨7635284, by rfl⟩ : syracuseStep 10180379 = 15270569) B15270569
theorem B12708521 : Blo 1486063 12708521 := bstep (se 2 (by rfl) ⟨4765695, by rfl⟩ : syracuseStep 12708521 = 9531391) B9531391
theorem B1486075 : Blo 1486063 1486075 := bstep (se 1 (by rfl) ⟨1114556, by rfl⟩ : syracuseStep 1486075 = 2229113) B2229113
theorem B6786919 : Blo 1486063 6786919 := bstep (se 1 (by rfl) ⟨5090189, by rfl⟩ : syracuseStep 6786919 = 10180379) B10180379
theorem B8472347 : Blo 1486063 8472347 := bstep (se 1 (by rfl) ⟨6354260, by rfl⟩ : syracuseStep 8472347 = 12708521) B12708521
theorem B36196901 : Blo 1486063 36196901 := bstep (se 4 (by rfl) ⟨3393459, by rfl⟩ : syracuseStep 36196901 = 6786919) B6786919
theorem B5648231 : Blo 1486063 5648231 := bstep (se 1 (by rfl) ⟨4236173, by rfl⟩ : syracuseStep 5648231 = 8472347) B8472347
theorem B24131267 : Blo 1486063 24131267 := bstep (se 1 (by rfl) ⟨18098450, by rfl⟩ : syracuseStep 24131267 = 36196901) B36196901
theorem B3765487 : Blo 1486063 3765487 := bstep (se 1 (by rfl) ⟨2824115, by rfl⟩ : syracuseStep 3765487 = 5648231) B5648231
theorem B16087511 : Blo 1486063 16087511 := bstep (se 1 (by rfl) ⟨12065633, by rfl⟩ : syracuseStep 16087511 = 24131267) B24131267
theorem B10725007 : Blo 1486063 10725007 := bstep (se 1 (by rfl) ⟨8043755, by rfl⟩ : syracuseStep 10725007 = 16087511) B16087511
theorem B5020649 : Blo 1486063 5020649 := bstep (se 2 (by rfl) ⟨1882743, by rfl⟩ : syracuseStep 5020649 = 3765487) B3765487
theorem B3347099 : Blo 1486063 3347099 := bstep (se 1 (by rfl) ⟨2510324, by rfl⟩ : syracuseStep 3347099 = 5020649) B5020649
theorem B14300009 : Blo 1486063 14300009 := bstep (se 2 (by rfl) ⟨5362503, by rfl⟩ : syracuseStep 14300009 = 10725007) B10725007
theorem B2231399 : Blo 1486063 2231399 := bstep (se 1 (by rfl) ⟨1673549, by rfl⟩ : syracuseStep 2231399 = 3347099) B3347099
theorem B9533339 : Blo 1486063 9533339 := bstep (se 1 (by rfl) ⟨7150004, by rfl⟩ : syracuseStep 9533339 = 14300009) B14300009
theorem B1487599 : Blo 1486063 1487599 := bstep (se 1 (by rfl) ⟨1115699, by rfl⟩ : syracuseStep 1487599 = 2231399) B2231399
theorem B6355559 : Blo 1486063 6355559 := bstep (se 1 (by rfl) ⟨4766669, by rfl⟩ : syracuseStep 6355559 = 9533339) B9533339
theorem B4237039 : Blo 1486063 4237039 := bstep (se 1 (by rfl) ⟨3177779, by rfl⟩ : syracuseStep 4237039 = 6355559) B6355559
theorem B5649385 : Blo 1486063 5649385 := bstep (se 2 (by rfl) ⟨2118519, by rfl⟩ : syracuseStep 5649385 = 4237039) B4237039
theorem B7532513 : Blo 1486063 7532513 := bstep (se 2 (by rfl) ⟨2824692, by rfl⟩ : syracuseStep 7532513 = 5649385) B5649385
theorem B5021675 : Blo 1486063 5021675 := bstep (se 1 (by rfl) ⟨3766256, by rfl⟩ : syracuseStep 5021675 = 7532513) B7532513
theorem B3347783 : Blo 1486063 3347783 := bstep (se 1 (by rfl) ⟨2510837, by rfl⟩ : syracuseStep 3347783 = 5021675) B5021675
theorem B2231855 : Blo 1486063 2231855 := bstep (se 1 (by rfl) ⟨1673891, by rfl⟩ : syracuseStep 2231855 = 3347783) B3347783
theorem B1487903 : Blo 1486063 1487903 := bstep (se 1 (by rfl) ⟨1115927, by rfl⟩ : syracuseStep 1487903 = 2231855) B2231855

theorem C0 (j : ℕ) (h1 : 371515 ≤ j) (h2 : j ≤ 372015) : Blo 1486063 (4 * j + 3) := by
  interval_cases j
  · exact B1486063
  · exact B1486067
  · exact B1486071
  · exact B1486075
  · exact B1486079
  · exact B1486083
  · exact B1486087
  · exact B1486091
  · exact B1486095
  · exact B1486099
  · exact B1486103
  · exact B1486107
  · exact B1486111
  · exact B1486115
  · exact B1486119
  · exact B1486123
  · exact B1486127
  · exact B1486131
  · exact B1486135
  · exact B1486139
  · exact B1486143
  · exact B1486147
  · exact B1486151
  · exact B1486155
  · exact B1486159
  · exact B1486163
  · exact B1486167
  · exact B1486171
  · exact B1486175
  · exact B1486179
  · exact B1486183
  · exact B1486187
  · exact B1486191
  · exact B1486195
  · exact B1486199
  · exact B1486203
  · exact B1486207
  · exact B1486211
  · exact B1486215
  · exact B1486219
  · exact B1486223
  · exact B1486227
  · exact B1486231
  · exact B1486235
  · exact B1486239
  · exact B1486243
  · exact B1486247
  · exact B1486251
  · exact B1486255
  · exact B1486259
  · exact B1486263
  · exact B1486267
  · exact B1486271
  · exact B1486275
  · exact B1486279
  · exact B1486283
  · exact B1486287
  · exact B1486291
  · exact B1486295
  · exact B1486299
  · exact B1486303
  · exact B1486307
  · exact B1486311
  · exact B1486315
  · exact B1486319
  · exact B1486323
  · exact B1486327
  · exact B1486331
  · exact B1486335
  · exact B1486339
  · exact B1486343
  · exact B1486347
  · exact B1486351
  · exact B1486355
  · exact B1486359
  · exact B1486363
  · exact B1486367
  · exact B1486371
  · exact B1486375
  · exact B1486379
  · exact B1486383
  · exact B1486387
  · exact B1486391
  · exact B1486395
  · exact B1486399
  · exact B1486403
  · exact B1486407
  · exact B1486411
  · exact B1486415
  · exact B1486419
  · exact B1486423
  · exact B1486427
  · exact B1486431
  · exact B1486435
  · exact B1486439
  · exact B1486443
  · exact B1486447
  · exact B1486451
  · exact B1486455
  · exact B1486459
  · exact B1486463
  · exact B1486467
  · exact B1486471
  · exact B1486475
  · exact B1486479
  · exact B1486483
  · exact B1486487
  · exact B1486491
  · exact B1486495
  · exact B1486499
  · exact B1486503
  · exact B1486507
  · exact B1486511
  · exact B1486515
  · exact B1486519
  · exact B1486523
  · exact B1486527
  · exact B1486531
  · exact B1486535
  · exact B1486539
  · exact B1486543
  · exact B1486547
  · exact B1486551
  · exact B1486555
  · exact B1486559
  · exact B1486563
  · exact B1486567
  · exact B1486571
  · exact B1486575
  · exact B1486579
  · exact B1486583
  · exact B1486587
  · exact B1486591
  · exact B1486595
  · exact B1486599
  · exact B1486603
  · exact B1486607
  · exact B1486611
  · exact B1486615
  · exact B1486619
  · exact B1486623
  · exact B1486627
  · exact B1486631
  · exact B1486635
  · exact B1486639
  · exact B1486643
  · exact B1486647
  · exact B1486651
  · exact B1486655
  · exact B1486659
  · exact B1486663
  · exact B1486667
  · exact B1486671
  · exact B1486675
  · exact B1486679
  · exact B1486683
  · exact B1486687
  · exact B1486691
  · exact B1486695
  · exact B1486699
  · exact B1486703
  · exact B1486707
  · exact B1486711
  · exact B1486715
  · exact B1486719
  · exact B1486723
  · exact B1486727
  · exact B1486731
  · exact B1486735
  · exact B1486739
  · exact B1486743
  · exact B1486747
  · exact B1486751
  · exact B1486755
  · exact B1486759
  · exact B1486763
  · exact B1486767
  · exact B1486771
  · exact B1486775
  · exact B1486779
  · exact B1486783
  · exact B1486787
  · exact B1486791
  · exact B1486795
  · exact B1486799
  · exact B1486803
  · exact B1486807
  · exact B1486811
  · exact B1486815
  · exact B1486819
  · exact B1486823
  · exact B1486827
  · exact B1486831
  · exact B1486835
  · exact B1486839
  · exact B1486843
  · exact B1486847
  · exact B1486851
  · exact B1486855
  · exact B1486859
  · exact B1486863
  · exact B1486867
  · exact B1486871
  · exact B1486875
  · exact B1486879
  · exact B1486883
  · exact B1486887
  · exact B1486891
  · exact B1486895
  · exact B1486899
  · exact B1486903
  · exact B1486907
  · exact B1486911
  · exact B1486915
  · exact B1486919
  · exact B1486923
  · exact B1486927
  · exact B1486931
  · exact B1486935
  · exact B1486939
  · exact B1486943
  · exact B1486947
  · exact B1486951
  · exact B1486955
  · exact B1486959
  · exact B1486963
  · exact B1486967
  · exact B1486971
  · exact B1486975
  · exact B1486979
  · exact B1486983
  · exact B1486987
  · exact B1486991
  · exact B1486995
  · exact B1486999
  · exact B1487003
  · exact B1487007
  · exact B1487011
  · exact B1487015
  · exact B1487019
  · exact B1487023
  · exact B1487027
  · exact B1487031
  · exact B1487035
  · exact B1487039
  · exact B1487043
  · exact B1487047
  · exact B1487051
  · exact B1487055
  · exact B1487059
  · exact B1487063
  · exact B1487067
  · exact B1487071
  · exact B1487075
  · exact B1487079
  · exact B1487083
  · exact B1487087
  · exact B1487091
  · exact B1487095
  · exact B1487099
  · exact B1487103
  · exact B1487107
  · exact B1487111
  · exact B1487115
  · exact B1487119
  · exact B1487123
  · exact B1487127
  · exact B1487131
  · exact B1487135
  · exact B1487139
  · exact B1487143
  · exact B1487147
  · exact B1487151
  · exact B1487155
  · exact B1487159
  · exact B1487163
  · exact B1487167
  · exact B1487171
  · exact B1487175
  · exact B1487179
  · exact B1487183
  · exact B1487187
  · exact B1487191
  · exact B1487195
  · exact B1487199
  · exact B1487203
  · exact B1487207
  · exact B1487211
  · exact B1487215
  · exact B1487219
  · exact B1487223
  · exact B1487227
  · exact B1487231
  · exact B1487235
  · exact B1487239
  · exact B1487243
  · exact B1487247
  · exact B1487251
  · exact B1487255
  · exact B1487259
  · exact B1487263
  · exact B1487267
  · exact B1487271
  · exact B1487275
  · exact B1487279
  · exact B1487283
  · exact B1487287
  · exact B1487291
  · exact B1487295
  · exact B1487299
  · exact B1487303
  · exact B1487307
  · exact B1487311
  · exact B1487315
  · exact B1487319
  · exact B1487323
  · exact B1487327
  · exact B1487331
  · exact B1487335
  · exact B1487339
  · exact B1487343
  · exact B1487347
  · exact B1487351
  · exact B1487355
  · exact B1487359
  · exact B1487363
  · exact B1487367
  · exact B1487371
  · exact B1487375
  · exact B1487379
  · exact B1487383
  · exact B1487387
  · exact B1487391
  · exact B1487395
  · exact B1487399
  · exact B1487403
  · exact B1487407
  · exact B1487411
  · exact B1487415
  · exact B1487419
  · exact B1487423
  · exact B1487427
  · exact B1487431
  · exact B1487435
  · exact B1487439
  · exact B1487443
  · exact B1487447
  · exact B1487451
  · exact B1487455
  · exact B1487459
  · exact B1487463
  · exact B1487467
  · exact B1487471
  · exact B1487475
  · exact B1487479
  · exact B1487483
  · exact B1487487
  · exact B1487491
  · exact B1487495
  · exact B1487499
  · exact B1487503
  · exact B1487507
  · exact B1487511
  · exact B1487515
  · exact B1487519
  · exact B1487523
  · exact B1487527
  · exact B1487531
  · exact B1487535
  · exact B1487539
  · exact B1487543
  · exact B1487547
  · exact B1487551
  · exact B1487555
  · exact B1487559
  · exact B1487563
  · exact B1487567
  · exact B1487571
  · exact B1487575
  · exact B1487579
  · exact B1487583
  · exact B1487587
  · exact B1487591
  · exact B1487595
  · exact B1487599
  · exact B1487603
  · exact B1487607
  · exact B1487611
  · exact B1487615
  · exact B1487619
  · exact B1487623
  · exact B1487627
  · exact B1487631
  · exact B1487635
  · exact B1487639
  · exact B1487643
  · exact B1487647
  · exact B1487651
  · exact B1487655
  · exact B1487659
  · exact B1487663
  · exact B1487667
  · exact B1487671
  · exact B1487675
  · exact B1487679
  · exact B1487683
  · exact B1487687
  · exact B1487691
  · exact B1487695
  · exact B1487699
  · exact B1487703
  · exact B1487707
  · exact B1487711
  · exact B1487715
  · exact B1487719
  · exact B1487723
  · exact B1487727
  · exact B1487731
  · exact B1487735
  · exact B1487739
  · exact B1487743
  · exact B1487747
  · exact B1487751
  · exact B1487755
  · exact B1487759
  · exact B1487763
  · exact B1487767
  · exact B1487771
  · exact B1487775
  · exact B1487779
  · exact B1487783
  · exact B1487787
  · exact B1487791
  · exact B1487795
  · exact B1487799
  · exact B1487803
  · exact B1487807
  · exact B1487811
  · exact B1487815
  · exact B1487819
  · exact B1487823
  · exact B1487827
  · exact B1487831
  · exact B1487835
  · exact B1487839
  · exact B1487843
  · exact B1487847
  · exact B1487851
  · exact B1487855
  · exact B1487859
  · exact B1487863
  · exact B1487867
  · exact B1487871
  · exact B1487875
  · exact B1487879
  · exact B1487883
  · exact B1487887
  · exact B1487891
  · exact B1487895
  · exact B1487899
  · exact B1487903
  · exact B1487907
  · exact B1487911
  · exact B1487915
  · exact B1487919
  · exact B1487923
  · exact B1487927
  · exact B1487931
  · exact B1487935
  · exact B1487939
  · exact B1487943
  · exact B1487947
  · exact B1487951
  · exact B1487955
  · exact B1487959
  · exact B1487963
  · exact B1487967
  · exact B1487971
  · exact B1487975
  · exact B1487979
  · exact B1487983
  · exact B1487987
  · exact B1487991
  · exact B1487995
  · exact B1487999
  · exact B1488003
  · exact B1488007
  · exact B1488011
  · exact B1488015
  · exact B1488019
  · exact B1488023
  · exact B1488027
  · exact B1488031
  · exact B1488035
  · exact B1488039
  · exact B1488043
  · exact B1488047
  · exact B1488051
  · exact B1488055
  · exact B1488059
  · exact B1488063

theorem solution (m : ℕ) (hlo : 1486063 ≤ m) (hhi : m ≤ 1488063) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 371515 ≤ j := by omega
    have hj2 : j ≤ 372015 := by omega
    have hb : Blo 1486063 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
