-- Prove2me | solution 1 for syracuse_descends_range_674311_678311
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:53.355885+00:00
-- url     : https://prove2.me/submissions/f7336f70-1620-4a08-8e3a-22d463a0cadb

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


theorem B1015829 : Blo 674311 1015829 := bbase (se 6 (by rfl) ⟨23808, by rfl⟩ : syracuseStep 1015829 = 47617) (by norm_num)
theorem B1015853 : Blo 674311 1015853 := bbase (se 3 (by rfl) ⟨190472, by rfl⟩ : syracuseStep 1015853 = 380945) (by norm_num)
theorem B1015877 : Blo 674311 1015877 := bbase (se 4 (by rfl) ⟨95238, by rfl⟩ : syracuseStep 1015877 = 190477) (by norm_num)
theorem B1015901 : Blo 674311 1015901 := bbase (se 3 (by rfl) ⟨190481, by rfl⟩ : syracuseStep 1015901 = 380963) (by norm_num)
theorem B1015925 : Blo 674311 1015925 := bbase (se 5 (by rfl) ⟨47621, by rfl⟩ : syracuseStep 1015925 = 95243) (by norm_num)
theorem B1015949 : Blo 674311 1015949 := bbase (se 3 (by rfl) ⟨190490, by rfl⟩ : syracuseStep 1015949 = 380981) (by norm_num)
theorem B721057 : Blo 674311 721057 := bbase (se 2 (by rfl) ⟨270396, by rfl⟩ : syracuseStep 721057 = 540793) (by norm_num)
theorem B1015973 : Blo 674311 1015973 := bbase (se 4 (by rfl) ⟨95247, by rfl⟩ : syracuseStep 1015973 = 190495) (by norm_num)
theorem B1015997 : Blo 674311 1015997 := bbase (se 3 (by rfl) ⟨190499, by rfl⟩ : syracuseStep 1015997 = 380999) (by norm_num)
theorem B1016021 : Blo 674311 1016021 := bbase (se 7 (by rfl) ⟨11906, by rfl⟩ : syracuseStep 1016021 = 23813) (by norm_num)
theorem B1016045 : Blo 674311 1016045 := bbase (se 3 (by rfl) ⟨190508, by rfl⟩ : syracuseStep 1016045 = 381017) (by norm_num)
theorem B1736957 : Blo 674311 1736957 := bbase (se 3 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 1736957 = 651359) (by norm_num)
theorem B1442053 : Blo 674311 1442053 := bbase (se 4 (by rfl) ⟨135192, by rfl⟩ : syracuseStep 1442053 = 270385) (by norm_num)
theorem B1016069 : Blo 674311 1016069 := bbase (se 4 (by rfl) ⟨95256, by rfl⟩ : syracuseStep 1016069 = 190513) (by norm_num)
theorem B1016093 : Blo 674311 1016093 := bbase (se 3 (by rfl) ⟨190517, by rfl⟩ : syracuseStep 1016093 = 381035) (by norm_num)
theorem B1016117 : Blo 674311 1016117 := bbase (se 5 (by rfl) ⟨47630, by rfl⟩ : syracuseStep 1016117 = 95261) (by norm_num)
theorem B1081669 : Blo 674311 1081669 := bbase (se 4 (by rfl) ⟨101406, by rfl⟩ : syracuseStep 1081669 = 202813) (by norm_num)
theorem B1016141 : Blo 674311 1016141 := bbase (se 3 (by rfl) ⟨190526, by rfl⟩ : syracuseStep 1016141 = 381053) (by norm_num)
theorem B35225941 : Blo 674311 35225941 := bbase (se 10 (by rfl) ⟨51600, by rfl⟩ : syracuseStep 35225941 = 103201) (by norm_num)
theorem B1016165 : Blo 674311 1016165 := bbase (se 4 (by rfl) ⟨95265, by rfl⟩ : syracuseStep 1016165 = 190531) (by norm_num)
theorem B1016189 : Blo 674311 1016189 := bbase (se 3 (by rfl) ⟨190535, by rfl⟩ : syracuseStep 1016189 = 381071) (by norm_num)
theorem B1016213 : Blo 674311 1016213 := bbase (se 6 (by rfl) ⟨23817, by rfl⟩ : syracuseStep 1016213 = 47635) (by norm_num)
theorem B1016237 : Blo 674311 1016237 := bbase (se 3 (by rfl) ⟨190544, by rfl⟩ : syracuseStep 1016237 = 381089) (by norm_num)
theorem B1016261 : Blo 674311 1016261 := bbase (se 4 (by rfl) ⟨95274, by rfl⟩ : syracuseStep 1016261 = 190549) (by norm_num)
theorem B1016285 : Blo 674311 1016285 := bbase (se 3 (by rfl) ⟨190553, by rfl⟩ : syracuseStep 1016285 = 381107) (by norm_num)
theorem B1016309 : Blo 674311 1016309 := bbase (se 5 (by rfl) ⟨47639, by rfl⟩ : syracuseStep 1016309 = 95279) (by norm_num)
theorem B1016333 : Blo 674311 1016333 := bbase (se 3 (by rfl) ⟨190562, by rfl⟩ : syracuseStep 1016333 = 381125) (by norm_num)
theorem B721433 : Blo 674311 721433 := bbase (se 2 (by rfl) ⟨270537, by rfl⟩ : syracuseStep 721433 = 541075) (by norm_num)
theorem B1016357 : Blo 674311 1016357 := bbase (se 4 (by rfl) ⟨95283, by rfl⟩ : syracuseStep 1016357 = 190567) (by norm_num)
theorem B1016381 : Blo 674311 1016381 := bbase (se 3 (by rfl) ⟨190571, by rfl⟩ : syracuseStep 1016381 = 381143) (by norm_num)
theorem B1081925 : Blo 674311 1081925 := bbase (se 4 (by rfl) ⟨101430, by rfl⟩ : syracuseStep 1081925 = 202861) (by norm_num)
theorem B21955157 : Blo 674311 21955157 := bbase (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) (by norm_num)
theorem B1016405 : Blo 674311 1016405 := bbase (se 8 (by rfl) ⟨5955, by rfl⟩ : syracuseStep 1016405 = 11911) (by norm_num)
theorem B721505 : Blo 674311 721505 := bbase (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) (by norm_num)
theorem B1016429 : Blo 674311 1016429 := bbase (se 3 (by rfl) ⟨190580, by rfl⟩ : syracuseStep 1016429 = 381161) (by norm_num)
theorem B1016453 : Blo 674311 1016453 := bbase (se 4 (by rfl) ⟨95292, by rfl⟩ : syracuseStep 1016453 = 190585) (by norm_num)
theorem B1016477 : Blo 674311 1016477 := bbase (se 3 (by rfl) ⟨190589, by rfl⟩ : syracuseStep 1016477 = 381179) (by norm_num)
theorem B1016501 : Blo 674311 1016501 := bbase (se 5 (by rfl) ⟨47648, by rfl⟩ : syracuseStep 1016501 = 95297) (by norm_num)
theorem B1016525 : Blo 674311 1016525 := bbase (se 3 (by rfl) ⟨190598, by rfl⟩ : syracuseStep 1016525 = 381197) (by norm_num)
theorem B1016549 : Blo 674311 1016549 := bbase (se 4 (by rfl) ⟨95301, by rfl⟩ : syracuseStep 1016549 = 190603) (by norm_num)
theorem B1442549 : Blo 674311 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B1016573 : Blo 674311 1016573 := bbase (se 3 (by rfl) ⟨190607, by rfl⟩ : syracuseStep 1016573 = 381215) (by norm_num)
theorem B1082117 : Blo 674311 1082117 := bbase (se 4 (by rfl) ⟨101448, by rfl⟩ : syracuseStep 1082117 = 202897) (by norm_num)
theorem B1016597 : Blo 674311 1016597 := bbase (se 6 (by rfl) ⟨23826, by rfl⟩ : syracuseStep 1016597 = 47653) (by norm_num)
theorem B721693 : Blo 674311 721693 := bbase (se 3 (by rfl) ⟨135317, by rfl⟩ : syracuseStep 721693 = 270635) (by norm_num)
theorem B1016621 : Blo 674311 1016621 := bbase (se 3 (by rfl) ⟨190616, by rfl⟩ : syracuseStep 1016621 = 381233) (by norm_num)
theorem B1016645 : Blo 674311 1016645 := bbase (se 4 (by rfl) ⟨95310, by rfl⟩ : syracuseStep 1016645 = 190621) (by norm_num)
theorem B1016669 : Blo 674311 1016669 := bbase (se 3 (by rfl) ⟨190625, by rfl⟩ : syracuseStep 1016669 = 381251) (by norm_num)
theorem B1016693 : Blo 674311 1016693 := bbase (se 5 (by rfl) ⟨47657, by rfl⟩ : syracuseStep 1016693 = 95315) (by norm_num)
theorem B1016717 : Blo 674311 1016717 := bbase (se 3 (by rfl) ⟨190634, by rfl⟩ : syracuseStep 1016717 = 381269) (by norm_num)
theorem B2884517 : Blo 674311 2884517 := bbase (se 4 (by rfl) ⟨270423, by rfl⟩ : syracuseStep 2884517 = 540847) (by norm_num)
theorem B1016741 : Blo 674311 1016741 := bbase (se 4 (by rfl) ⟨95319, by rfl⟩ : syracuseStep 1016741 = 190639) (by norm_num)
theorem B1016765 : Blo 674311 1016765 := bbase (se 3 (by rfl) ⟨190643, by rfl⟩ : syracuseStep 1016765 = 381287) (by norm_num)
theorem B721877 : Blo 674311 721877 := bbase (se 7 (by rfl) ⟨8459, by rfl⟩ : syracuseStep 721877 = 16919) (by norm_num)
theorem B1016789 : Blo 674311 1016789 := bbase (se 7 (by rfl) ⟨11915, by rfl⟩ : syracuseStep 1016789 = 23831) (by norm_num)
theorem B1016813 : Blo 674311 1016813 := bbase (se 3 (by rfl) ⟨190652, by rfl⟩ : syracuseStep 1016813 = 381305) (by norm_num)
theorem B1016837 : Blo 674311 1016837 := bbase (se 4 (by rfl) ⟨95328, by rfl⟩ : syracuseStep 1016837 = 190657) (by norm_num)
theorem B1016861 : Blo 674311 1016861 := bbase (se 3 (by rfl) ⟨190661, by rfl⟩ : syracuseStep 1016861 = 381323) (by norm_num)
theorem B1016885 : Blo 674311 1016885 := bbase (se 5 (by rfl) ⟨47666, by rfl⟩ : syracuseStep 1016885 = 95333) (by norm_num)
theorem B1016909 : Blo 674311 1016909 := bbase (se 3 (by rfl) ⟨190670, by rfl⟩ : syracuseStep 1016909 = 381341) (by norm_num)
theorem B1016933 : Blo 674311 1016933 := bbase (se 4 (by rfl) ⟨95337, by rfl⟩ : syracuseStep 1016933 = 190675) (by norm_num)
theorem B1016957 : Blo 674311 1016957 := bbase (se 3 (by rfl) ⟨190679, by rfl⟩ : syracuseStep 1016957 = 381359) (by norm_num)
theorem B1016981 : Blo 674311 1016981 := bbase (se 6 (by rfl) ⟨23835, by rfl⟩ : syracuseStep 1016981 = 47671) (by norm_num)
theorem B1017005 : Blo 674311 1017005 := bbase (se 3 (by rfl) ⟨190688, by rfl⟩ : syracuseStep 1017005 = 381377) (by norm_num)
theorem B1017029 : Blo 674311 1017029 := bbase (se 4 (by rfl) ⟨95346, by rfl⟩ : syracuseStep 1017029 = 190693) (by norm_num)
theorem B1017053 : Blo 674311 1017053 := bbase (se 3 (by rfl) ⟨190697, by rfl⟩ : syracuseStep 1017053 = 381395) (by norm_num)
theorem B1017077 : Blo 674311 1017077 := bbase (se 5 (by rfl) ⟨47675, by rfl⟩ : syracuseStep 1017077 = 95351) (by norm_num)
theorem B1017101 : Blo 674311 1017101 := bbase (se 3 (by rfl) ⟨190706, by rfl⟩ : syracuseStep 1017101 = 381413) (by norm_num)
theorem B1017125 : Blo 674311 1017125 := bbase (se 4 (by rfl) ⟨95355, by rfl⟩ : syracuseStep 1017125 = 190711) (by norm_num)
theorem B1017149 : Blo 674311 1017149 := bbase (se 3 (by rfl) ⟨190715, by rfl⟩ : syracuseStep 1017149 = 381431) (by norm_num)
theorem B1017173 : Blo 674311 1017173 := bbase (se 12 (by rfl) ⟨372, by rfl⟩ : syracuseStep 1017173 = 745) (by norm_num)
theorem B1017197 : Blo 674311 1017197 := bbase (se 3 (by rfl) ⟨190724, by rfl⟩ : syracuseStep 1017197 = 381449) (by norm_num)
theorem B1017221 : Blo 674311 1017221 := bbase (se 4 (by rfl) ⟨95364, by rfl⟩ : syracuseStep 1017221 = 190729) (by norm_num)
theorem B1017245 : Blo 674311 1017245 := bbase (se 3 (by rfl) ⟨190733, by rfl⟩ : syracuseStep 1017245 = 381467) (by norm_num)
theorem B1017269 : Blo 674311 1017269 := bbase (se 5 (by rfl) ⟨47684, by rfl⟩ : syracuseStep 1017269 = 95369) (by norm_num)
theorem B1017293 : Blo 674311 1017293 := bbase (se 3 (by rfl) ⟨190742, by rfl⟩ : syracuseStep 1017293 = 381485) (by norm_num)
theorem B1017317 : Blo 674311 1017317 := bbase (se 4 (by rfl) ⟨95373, by rfl⟩ : syracuseStep 1017317 = 190747) (by norm_num)
theorem B1017341 : Blo 674311 1017341 := bbase (se 3 (by rfl) ⟨190751, by rfl⟩ : syracuseStep 1017341 = 381503) (by norm_num)
theorem B853517 : Blo 674311 853517 := bbase (se 3 (by rfl) ⟨160034, by rfl⟩ : syracuseStep 853517 = 320069) (by norm_num)
theorem B1017365 : Blo 674311 1017365 := bbase (se 6 (by rfl) ⟨23844, by rfl⟩ : syracuseStep 1017365 = 47689) (by norm_num)
theorem B1017389 : Blo 674311 1017389 := bbase (se 3 (by rfl) ⟨190760, by rfl⟩ : syracuseStep 1017389 = 381521) (by norm_num)
theorem B853573 : Blo 674311 853573 := bbase (se 4 (by rfl) ⟨80022, by rfl⟩ : syracuseStep 853573 = 160045) (by norm_num)
theorem B1017413 : Blo 674311 1017413 := bbase (se 4 (by rfl) ⟨95382, by rfl⟩ : syracuseStep 1017413 = 190765) (by norm_num)
theorem B1443413 : Blo 674311 1443413 := bbase (se 8 (by rfl) ⟨8457, by rfl⟩ : syracuseStep 1443413 = 16915) (by norm_num)
theorem B1017437 : Blo 674311 1017437 := bbase (se 3 (by rfl) ⟨190769, by rfl⟩ : syracuseStep 1017437 = 381539) (by norm_num)
theorem B1017461 : Blo 674311 1017461 := bbase (se 5 (by rfl) ⟨47693, by rfl⟩ : syracuseStep 1017461 = 95387) (by norm_num)
theorem B853669 : Blo 674311 853669 := bbase (se 4 (by rfl) ⟨80031, by rfl⟩ : syracuseStep 853669 = 160063) (by norm_num)
theorem B1083053 : Blo 674311 1083053 := bbase (se 3 (by rfl) ⟨203072, by rfl⟩ : syracuseStep 1083053 = 406145) (by norm_num)
theorem B722629 : Blo 674311 722629 := bbase (se 4 (by rfl) ⟨67746, by rfl⟩ : syracuseStep 722629 = 135493) (by norm_num)
theorem B1443557 : Blo 674311 1443557 := bbase (se 4 (by rfl) ⟨135333, by rfl⟩ : syracuseStep 1443557 = 270667) (by norm_num)
theorem B722701 : Blo 674311 722701 := bbase (se 3 (by rfl) ⟨135506, by rfl⟩ : syracuseStep 722701 = 271013) (by norm_num)
theorem B853841 : Blo 674311 853841 := bbase (se 2 (by rfl) ⟨320190, by rfl⟩ : syracuseStep 853841 = 640381) (by norm_num)
theorem B853897 : Blo 674311 853897 := bbase (se 2 (by rfl) ⟨320211, by rfl⟩ : syracuseStep 853897 = 640423) (by norm_num)
theorem B1542037 : Blo 674311 1542037 := bbase (se 6 (by rfl) ⟨36141, by rfl⟩ : syracuseStep 1542037 = 72283) (by norm_num)
theorem B3475349 : Blo 674311 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B722881 : Blo 674311 722881 := bbase (se 2 (by rfl) ⟨271080, by rfl⟩ : syracuseStep 722881 = 542161) (by norm_num)
theorem B853993 : Blo 674311 853993 := bbase (se 2 (by rfl) ⟨320247, by rfl⟩ : syracuseStep 853993 = 640495) (by norm_num)
theorem B1083437 : Blo 674311 1083437 := bbase (se 3 (by rfl) ⟨203144, by rfl⟩ : syracuseStep 1083437 = 406289) (by norm_num)
theorem B7702613 : Blo 674311 7702613 := bbase (se 8 (by rfl) ⟨45132, by rfl⟩ : syracuseStep 7702613 = 90265) (by norm_num)
theorem B854165 : Blo 674311 854165 := bbase (se 6 (by rfl) ⟨20019, by rfl⟩ : syracuseStep 854165 = 40039) (by norm_num)
theorem B1083565 : Blo 674311 1083565 := bbase (se 3 (by rfl) ⟨203168, by rfl⟩ : syracuseStep 1083565 = 406337) (by norm_num)
theorem B854221 : Blo 674311 854221 := bbase (se 3 (by rfl) ⟨160166, by rfl⟩ : syracuseStep 854221 = 320333) (by norm_num)
theorem B1280261 : Blo 674311 1280261 := bbase (se 4 (by rfl) ⟨120024, by rfl⟩ : syracuseStep 1280261 = 240049) (by norm_num)
theorem B854317 : Blo 674311 854317 := bbase (se 3 (by rfl) ⟨160184, by rfl⟩ : syracuseStep 854317 = 320369) (by norm_num)
theorem B3246389 : Blo 674311 3246389 := bbase (se 5 (by rfl) ⟨152174, by rfl⟩ : syracuseStep 3246389 = 304349) (by norm_num)
theorem B723325 : Blo 674311 723325 := bbase (se 3 (by rfl) ⟨135623, by rfl⟩ : syracuseStep 723325 = 271247) (by norm_num)
theorem B1444301 : Blo 674311 1444301 := bbase (se 3 (by rfl) ⟨270806, by rfl⟩ : syracuseStep 1444301 = 541613) (by norm_num)
theorem B854489 : Blo 674311 854489 := bbase (se 2 (by rfl) ⟨320433, by rfl⟩ : syracuseStep 854489 = 640867) (by norm_num)
theorem B2165221 : Blo 674311 2165221 := bbase (se 4 (by rfl) ⟨202989, by rfl⟩ : syracuseStep 2165221 = 405979) (by norm_num)
theorem B723449 : Blo 674311 723449 := bbase (se 2 (by rfl) ⟨271293, by rfl⟩ : syracuseStep 723449 = 542587) (by norm_num)
theorem B854545 : Blo 674311 854545 := bbase (se 2 (by rfl) ⟨320454, by rfl⟩ : syracuseStep 854545 = 640909) (by norm_num)
theorem B1280549 : Blo 674311 1280549 := bbase (se 4 (by rfl) ⟨120051, by rfl⟩ : syracuseStep 1280549 = 240103) (by norm_num)
theorem B2165285 : Blo 674311 2165285 := bbase (se 4 (by rfl) ⟨202995, by rfl⟩ : syracuseStep 2165285 = 405991) (by norm_num)
theorem B854641 : Blo 674311 854641 := bbase (se 2 (by rfl) ⟨320490, by rfl⟩ : syracuseStep 854641 = 640981) (by norm_num)
theorem B2886293 : Blo 674311 2886293 := bbase (se 6 (by rfl) ⟨67647, by rfl⟩ : syracuseStep 2886293 = 135295) (by norm_num)
theorem B1280701 : Blo 674311 1280701 := bbase (se 3 (by rfl) ⟨240131, by rfl⟩ : syracuseStep 1280701 = 480263) (by norm_num)
theorem B723701 : Blo 674311 723701 := bbase (se 5 (by rfl) ⟨33923, by rfl⟩ : syracuseStep 723701 = 67847) (by norm_num)
theorem B854813 : Blo 674311 854813 := bbase (se 3 (by rfl) ⟨160277, by rfl⟩ : syracuseStep 854813 = 320555) (by norm_num)
theorem B1542941 : Blo 674311 1542941 := bbase (se 3 (by rfl) ⟨289301, by rfl⟩ : syracuseStep 1542941 = 578603) (by norm_num)
theorem B854869 : Blo 674311 854869 := bbase (se 9 (by rfl) ⟨2504, by rfl⟩ : syracuseStep 854869 = 5009) (by norm_num)
theorem B1706933 : Blo 674311 1706933 := bbase (se 5 (by rfl) ⟨80012, by rfl⟩ : syracuseStep 1706933 = 160025) (by norm_num)
theorem B854965 : Blo 674311 854965 := bbase (se 5 (by rfl) ⟨40076, by rfl⟩ : syracuseStep 854965 = 80153) (by norm_num)
theorem B1281005 : Blo 674311 1281005 := bbase (se 3 (by rfl) ⟨240188, by rfl⟩ : syracuseStep 1281005 = 480377) (by norm_num)
theorem B1543205 : Blo 674311 1543205 := bbase (se 4 (by rfl) ⟨144675, by rfl⟩ : syracuseStep 1543205 = 289351) (by norm_num)
theorem B855137 : Blo 674311 855137 := bbase (se 2 (by rfl) ⟨320676, by rfl⟩ : syracuseStep 855137 = 641353) (by norm_num)
theorem B1084565 : Blo 674311 1084565 := bbase (se 6 (by rfl) ⟨25419, by rfl⟩ : syracuseStep 1084565 = 50839) (by norm_num)
theorem B855193 : Blo 674311 855193 := bbase (se 2 (by rfl) ⟨320697, by rfl⟩ : syracuseStep 855193 = 641395) (by norm_num)
theorem B724145 : Blo 674311 724145 := bbase (se 2 (by rfl) ⟨271554, by rfl⟩ : syracuseStep 724145 = 543109) (by norm_num)
theorem B1445053 : Blo 674311 1445053 := bbase (se 3 (by rfl) ⟨270947, by rfl⟩ : syracuseStep 1445053 = 541895) (by norm_num)
theorem B855289 : Blo 674311 855289 := bbase (se 2 (by rfl) ⟨320733, by rfl⟩ : syracuseStep 855289 = 641467) (by norm_num)
theorem B1707277 : Blo 674311 1707277 := bbase (se 3 (by rfl) ⟨320114, by rfl⟩ : syracuseStep 1707277 = 640229) (by norm_num)
theorem B1084693 : Blo 674311 1084693 := bbase (se 6 (by rfl) ⟨25422, by rfl⟩ : syracuseStep 1084693 = 50845) (by norm_num)
theorem B1445197 : Blo 674311 1445197 := bbase (se 3 (by rfl) ⟨270974, by rfl⟩ : syracuseStep 1445197 = 541949) (by norm_num)
theorem B1707389 : Blo 674311 1707389 := bbase (se 3 (by rfl) ⟨320135, by rfl⟩ : syracuseStep 1707389 = 640271) (by norm_num)
theorem B855461 : Blo 674311 855461 := bbase (se 4 (by rfl) ⟨80199, by rfl⟩ : syracuseStep 855461 = 160399) (by norm_num)
theorem B855517 : Blo 674311 855517 := bbase (se 3 (by rfl) ⟨160409, by rfl⟩ : syracuseStep 855517 = 320819) (by norm_num)
theorem B822817 : Blo 674311 822817 := bbase (se 2 (by rfl) ⟨308556, by rfl⟩ : syracuseStep 822817 = 617113) (by norm_num)
theorem B1707581 : Blo 674311 1707581 := bbase (se 3 (by rfl) ⟨320171, by rfl⟩ : syracuseStep 1707581 = 640343) (by norm_num)
theorem B855613 : Blo 674311 855613 := bbase (se 3 (by rfl) ⟨160427, by rfl⟩ : syracuseStep 855613 = 320855) (by norm_num)
theorem B2887285 : Blo 674311 2887285 := bbase (se 5 (by rfl) ⟨135341, by rfl⟩ : syracuseStep 2887285 = 270683) (by norm_num)
theorem B1085077 : Blo 674311 1085077 := bbase (se 6 (by rfl) ⟨25431, by rfl⟩ : syracuseStep 1085077 = 50863) (by norm_num)
theorem B2920133 : Blo 674311 2920133 := bbase (se 4 (by rfl) ⟨273762, by rfl⟩ : syracuseStep 2920133 = 547525) (by norm_num)
theorem B1445573 : Blo 674311 1445573 := bbase (se 4 (by rfl) ⟨135522, by rfl⟩ : syracuseStep 1445573 = 271045) (by norm_num)
theorem B1281757 : Blo 674311 1281757 := bbase (se 3 (by rfl) ⟨240329, by rfl⟩ : syracuseStep 1281757 = 480659) (by norm_num)
theorem B855785 : Blo 674311 855785 := bbase (se 2 (by rfl) ⟨320919, by rfl⟩ : syracuseStep 855785 = 641839) (by norm_num)
theorem B855841 : Blo 674311 855841 := bbase (se 2 (by rfl) ⟨320940, by rfl⟩ : syracuseStep 855841 = 641881) (by norm_num)
theorem B986941 : Blo 674311 986941 := bbase (se 3 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 986941 = 370103) (by norm_num)
theorem B1281901 : Blo 674311 1281901 := bbase (se 3 (by rfl) ⟨240356, by rfl⟩ : syracuseStep 1281901 = 480713) (by norm_num)
theorem B855937 : Blo 674311 855937 := bbase (se 2 (by rfl) ⟨320976, by rfl⟩ : syracuseStep 855937 = 641953) (by norm_num)
theorem B1707925 : Blo 674311 1707925 := bbase (se 6 (by rfl) ⟨40029, by rfl⟩ : syracuseStep 1707925 = 80059) (by norm_num)
theorem B1085333 : Blo 674311 1085333 := bbase (se 6 (by rfl) ⟨25437, by rfl⟩ : syracuseStep 1085333 = 50875) (by norm_num)
theorem B1708037 : Blo 674311 1708037 := bbase (se 4 (by rfl) ⟨160128, by rfl⟩ : syracuseStep 1708037 = 320257) (by norm_num)
theorem B1282061 : Blo 674311 1282061 := bbase (se 3 (by rfl) ⟨240386, by rfl⟩ : syracuseStep 1282061 = 480773) (by norm_num)
theorem B856109 : Blo 674311 856109 := bbase (se 3 (by rfl) ⟨160520, by rfl⟩ : syracuseStep 856109 = 321041) (by norm_num)
theorem B1445941 : Blo 674311 1445941 := bbase (se 5 (by rfl) ⟨67778, by rfl⟩ : syracuseStep 1445941 = 135557) (by norm_num)
theorem B856165 : Blo 674311 856165 := bbase (se 4 (by rfl) ⟨80265, by rfl⟩ : syracuseStep 856165 = 160531) (by norm_num)
theorem B1282205 : Blo 674311 1282205 := bbase (se 3 (by rfl) ⟨240413, by rfl⟩ : syracuseStep 1282205 = 480827) (by norm_num)
theorem B1708229 : Blo 674311 1708229 := bbase (se 4 (by rfl) ⟨160146, by rfl⟩ : syracuseStep 1708229 = 320293) (by norm_num)
theorem B856261 : Blo 674311 856261 := bbase (se 4 (by rfl) ⟨80274, by rfl⟩ : syracuseStep 856261 = 160549) (by norm_num)
theorem B856433 : Blo 674311 856433 := bbase (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) (by norm_num)
theorem B856489 : Blo 674311 856489 := bbase (se 2 (by rfl) ⟨321183, by rfl⟩ : syracuseStep 856489 = 642367) (by norm_num)
theorem B6951349 : Blo 674311 6951349 := bbase (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) (by norm_num)
theorem B1282493 : Blo 674311 1282493 := bbase (se 3 (by rfl) ⟨240467, by rfl⟩ : syracuseStep 1282493 = 480935) (by norm_num)
theorem B856585 : Blo 674311 856585 := bbase (se 2 (by rfl) ⟨321219, by rfl⟩ : syracuseStep 856585 = 642439) (by norm_num)
theorem B1708573 : Blo 674311 1708573 := bbase (se 3 (by rfl) ⟨320357, by rfl⟩ : syracuseStep 1708573 = 640715) (by norm_num)
theorem B1282645 : Blo 674311 1282645 := bbase (se 8 (by rfl) ⟨7515, by rfl⟩ : syracuseStep 1282645 = 15031) (by norm_num)
theorem B1708685 : Blo 674311 1708685 := bbase (se 3 (by rfl) ⟨320378, by rfl⟩ : syracuseStep 1708685 = 640757) (by norm_num)
theorem B856757 : Blo 674311 856757 := bbase (se 5 (by rfl) ⟨40160, by rfl⟩ : syracuseStep 856757 = 80321) (by norm_num)
theorem B856813 : Blo 674311 856813 := bbase (se 3 (by rfl) ⟨160652, by rfl⟩ : syracuseStep 856813 = 321305) (by norm_num)
theorem B1544957 : Blo 674311 1544957 := bbase (se 3 (by rfl) ⟨289679, by rfl⟩ : syracuseStep 1544957 = 579359) (by norm_num)
theorem B1086205 : Blo 674311 1086205 := bbase (se 3 (by rfl) ⟨203663, by rfl⟩ : syracuseStep 1086205 = 407327) (by norm_num)
theorem B856909 : Blo 674311 856909 := bbase (se 3 (by rfl) ⟨160670, by rfl⟩ : syracuseStep 856909 = 321341) (by norm_num)
theorem B758605 : Blo 674311 758605 := bbase (se 3 (by rfl) ⟨142238, by rfl⟩ : syracuseStep 758605 = 284477) (by norm_num)
theorem B1708877 : Blo 674311 1708877 := bbase (se 3 (by rfl) ⟨320414, by rfl⟩ : syracuseStep 1708877 = 640829) (by norm_num)
theorem B1086301 : Blo 674311 1086301 := bbase (se 3 (by rfl) ⟨203681, by rfl⟩ : syracuseStep 1086301 = 407363) (by norm_num)
theorem B758641 : Blo 674311 758641 := bbase (se 2 (by rfl) ⟨284490, by rfl⟩ : syracuseStep 758641 = 568981) (by norm_num)
theorem B1282949 : Blo 674311 1282949 := bbase (se 4 (by rfl) ⟨120276, by rfl⟩ : syracuseStep 1282949 = 240553) (by norm_num)
theorem B758677 : Blo 674311 758677 := bbase (se 6 (by rfl) ⟨17781, by rfl⟩ : syracuseStep 758677 = 35563) (by norm_num)
theorem B758713 : Blo 674311 758713 := bbase (se 2 (by rfl) ⟨284517, by rfl⟩ : syracuseStep 758713 = 569035) (by norm_num)
theorem B758749 : Blo 674311 758749 := bbase (se 3 (by rfl) ⟨142265, by rfl⟩ : syracuseStep 758749 = 284531) (by norm_num)
theorem B857081 : Blo 674311 857081 := bbase (se 2 (by rfl) ⟨321405, by rfl⟩ : syracuseStep 857081 = 642811) (by norm_num)
theorem B1086461 : Blo 674311 1086461 := bbase (se 3 (by rfl) ⟨203711, by rfl⟩ : syracuseStep 1086461 = 407423) (by norm_num)
theorem B758785 : Blo 674311 758785 := bbase (se 2 (by rfl) ⟨284544, by rfl⟩ : syracuseStep 758785 = 569089) (by norm_num)
theorem B758821 : Blo 674311 758821 := bbase (se 4 (by rfl) ⟨71139, by rfl⟩ : syracuseStep 758821 = 142279) (by norm_num)
theorem B857137 : Blo 674311 857137 := bbase (se 2 (by rfl) ⟨321426, by rfl⟩ : syracuseStep 857137 = 642853) (by norm_num)
theorem B758857 : Blo 674311 758857 := bbase (se 2 (by rfl) ⟨284571, by rfl⟩ : syracuseStep 758857 = 569143) (by norm_num)
theorem B758893 : Blo 674311 758893 := bbase (se 3 (by rfl) ⟨142292, by rfl⟩ : syracuseStep 758893 = 284585) (by norm_num)
theorem B758929 : Blo 674311 758929 := bbase (se 2 (by rfl) ⟨284598, by rfl⟩ : syracuseStep 758929 = 569197) (by norm_num)
theorem B857233 : Blo 674311 857233 := bbase (se 2 (by rfl) ⟨321462, by rfl⟩ : syracuseStep 857233 = 642925) (by norm_num)
theorem B1709221 : Blo 674311 1709221 := bbase (se 4 (by rfl) ⟨160239, by rfl⟩ : syracuseStep 1709221 = 320479) (by norm_num)
theorem B758965 : Blo 674311 758965 := bbase (se 5 (by rfl) ⟨35576, by rfl⟩ : syracuseStep 758965 = 71153) (by norm_num)
theorem B1545421 : Blo 674311 1545421 := bbase (se 3 (by rfl) ⟨289766, by rfl⟩ : syracuseStep 1545421 = 579533) (by norm_num)
theorem B759001 : Blo 674311 759001 := bbase (se 2 (by rfl) ⟨284625, by rfl⟩ : syracuseStep 759001 = 569251) (by norm_num)
theorem B759037 : Blo 674311 759037 := bbase (se 3 (by rfl) ⟨142319, by rfl⟩ : syracuseStep 759037 = 284639) (by norm_num)
theorem B1709333 : Blo 674311 1709333 := bbase (se 6 (by rfl) ⟨40062, by rfl⟩ : syracuseStep 1709333 = 80125) (by norm_num)
theorem B759073 : Blo 674311 759073 := bbase (se 2 (by rfl) ⟨284652, by rfl⟩ : syracuseStep 759073 = 569305) (by norm_num)
theorem B857405 : Blo 674311 857405 := bbase (se 3 (by rfl) ⟨160763, by rfl⟩ : syracuseStep 857405 = 321527) (by norm_num)
theorem B759109 : Blo 674311 759109 := bbase (se 4 (by rfl) ⟨71166, by rfl⟩ : syracuseStep 759109 = 142333) (by norm_num)
theorem B759145 : Blo 674311 759145 := bbase (se 2 (by rfl) ⟨284679, by rfl⟩ : syracuseStep 759145 = 569359) (by norm_num)
theorem B857461 : Blo 674311 857461 := bbase (se 5 (by rfl) ⟨40193, by rfl⟩ : syracuseStep 857461 = 80387) (by norm_num)
theorem B759181 : Blo 674311 759181 := bbase (se 3 (by rfl) ⟨142346, by rfl⟩ : syracuseStep 759181 = 284693) (by norm_num)
theorem B759217 : Blo 674311 759217 := bbase (se 2 (by rfl) ⟨284706, by rfl⟩ : syracuseStep 759217 = 569413) (by norm_num)
theorem B759253 : Blo 674311 759253 := bbase (se 7 (by rfl) ⟨8897, by rfl⟩ : syracuseStep 759253 = 17795) (by norm_num)
theorem B1709525 : Blo 674311 1709525 := bbase (se 7 (by rfl) ⟨20033, by rfl⟩ : syracuseStep 1709525 = 40067) (by norm_num)
theorem B857557 : Blo 674311 857557 := bbase (se 7 (by rfl) ⟨10049, by rfl⟩ : syracuseStep 857557 = 20099) (by norm_num)
theorem B2168309 : Blo 674311 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B759289 : Blo 674311 759289 := bbase (se 2 (by rfl) ⟨284733, by rfl⟩ : syracuseStep 759289 = 569467) (by norm_num)
theorem B1218053 : Blo 674311 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B1447445 : Blo 674311 1447445 := bbase (se 6 (by rfl) ⟨33924, by rfl⟩ : syracuseStep 1447445 = 67849) (by norm_num)
theorem B759325 : Blo 674311 759325 := bbase (se 3 (by rfl) ⟨142373, by rfl⟩ : syracuseStep 759325 = 284747) (by norm_num)
theorem B759361 : Blo 674311 759361 := bbase (se 2 (by rfl) ⟨284760, by rfl⟩ : syracuseStep 759361 = 569521) (by norm_num)
theorem B759397 : Blo 674311 759397 := bbase (se 4 (by rfl) ⟨71193, by rfl⟩ : syracuseStep 759397 = 142387) (by norm_num)
theorem B1283701 : Blo 674311 1283701 := bbase (se 5 (by rfl) ⟨60173, by rfl⟩ : syracuseStep 1283701 = 120347) (by norm_num)
theorem B857729 : Blo 674311 857729 := bbase (se 2 (by rfl) ⟨321648, by rfl⟩ : syracuseStep 857729 = 643297) (by norm_num)
theorem B759433 : Blo 674311 759433 := bbase (se 2 (by rfl) ⟨284787, by rfl⟩ : syracuseStep 759433 = 569575) (by norm_num)
theorem B1447589 : Blo 674311 1447589 := bbase (se 4 (by rfl) ⟨135711, by rfl⟩ : syracuseStep 1447589 = 271423) (by norm_num)
theorem B759469 : Blo 674311 759469 := bbase (se 3 (by rfl) ⟨142400, by rfl⟩ : syracuseStep 759469 = 284801) (by norm_num)
theorem B857785 : Blo 674311 857785 := bbase (se 2 (by rfl) ⟨321669, by rfl⟩ : syracuseStep 857785 = 643339) (by norm_num)
theorem B759505 : Blo 674311 759505 := bbase (se 2 (by rfl) ⟨284814, by rfl⟩ : syracuseStep 759505 = 569629) (by norm_num)
theorem B759541 : Blo 674311 759541 := bbase (se 5 (by rfl) ⟨35603, by rfl⟩ : syracuseStep 759541 = 71207) (by norm_num)
theorem B1283845 : Blo 674311 1283845 := bbase (se 4 (by rfl) ⟨120360, by rfl⟩ : syracuseStep 1283845 = 240721) (by norm_num)
theorem B2561813 : Blo 674311 2561813 := bbase (se 6 (by rfl) ⟨60042, by rfl⟩ : syracuseStep 2561813 = 120085) (by norm_num)
theorem B759577 : Blo 674311 759577 := bbase (se 2 (by rfl) ⟨284841, by rfl⟩ : syracuseStep 759577 = 569683) (by norm_num)
theorem B857881 : Blo 674311 857881 := bbase (se 2 (by rfl) ⟨321705, by rfl⟩ : syracuseStep 857881 = 643411) (by norm_num)
theorem B1709869 : Blo 674311 1709869 := bbase (se 3 (by rfl) ⟨320600, by rfl⟩ : syracuseStep 1709869 = 641201) (by norm_num)
theorem B759613 : Blo 674311 759613 := bbase (se 3 (by rfl) ⟨142427, by rfl⟩ : syracuseStep 759613 = 284855) (by norm_num)
theorem B759649 : Blo 674311 759649 := bbase (se 2 (by rfl) ⟨284868, by rfl⟩ : syracuseStep 759649 = 569737) (by norm_num)
theorem B759685 : Blo 674311 759685 := bbase (se 4 (by rfl) ⟨71220, by rfl⟩ : syracuseStep 759685 = 142441) (by norm_num)
theorem B1709981 : Blo 674311 1709981 := bbase (se 3 (by rfl) ⟨320621, by rfl⟩ : syracuseStep 1709981 = 641243) (by norm_num)
theorem B1284005 : Blo 674311 1284005 := bbase (se 4 (by rfl) ⟨120375, by rfl⟩ : syracuseStep 1284005 = 240751) (by norm_num)
theorem B759721 : Blo 674311 759721 := bbase (se 2 (by rfl) ⟨284895, by rfl⟩ : syracuseStep 759721 = 569791) (by norm_num)
theorem B858053 : Blo 674311 858053 := bbase (se 4 (by rfl) ⟨80442, by rfl⟩ : syracuseStep 858053 = 160885) (by norm_num)
theorem B759757 : Blo 674311 759757 := bbase (se 3 (by rfl) ⟨142454, by rfl⟩ : syracuseStep 759757 = 284909) (by norm_num)
theorem B759793 : Blo 674311 759793 := bbase (se 2 (by rfl) ⟨284922, by rfl⟩ : syracuseStep 759793 = 569845) (by norm_num)
theorem B694261 : Blo 674311 694261 := bbase (se 5 (by rfl) ⟨32543, by rfl⟩ : syracuseStep 694261 = 65087) (by norm_num)
theorem B858109 : Blo 674311 858109 := bbase (se 3 (by rfl) ⟨160895, by rfl⟩ : syracuseStep 858109 = 321791) (by norm_num)
theorem B1447949 : Blo 674311 1447949 := bbase (se 3 (by rfl) ⟨271490, by rfl⟩ : syracuseStep 1447949 = 542981) (by norm_num)
theorem B759829 : Blo 674311 759829 := bbase (se 6 (by rfl) ⟨17808, by rfl⟩ : syracuseStep 759829 = 35617) (by norm_num)
theorem B2562101 : Blo 674311 2562101 := bbase (se 5 (by rfl) ⟨120098, by rfl⟩ : syracuseStep 2562101 = 240197) (by norm_num)
theorem B1284149 : Blo 674311 1284149 := bbase (se 5 (by rfl) ⟨60194, by rfl⟩ : syracuseStep 1284149 = 120389) (by norm_num)
theorem B759865 : Blo 674311 759865 := bbase (se 2 (by rfl) ⟨284949, by rfl⟩ : syracuseStep 759865 = 569899) (by norm_num)
theorem B759901 : Blo 674311 759901 := bbase (se 3 (by rfl) ⟨142481, by rfl⟩ : syracuseStep 759901 = 284963) (by norm_num)
theorem B1710173 : Blo 674311 1710173 := bbase (se 3 (by rfl) ⟨320657, by rfl⟩ : syracuseStep 1710173 = 641315) (by norm_num)
theorem B858205 : Blo 674311 858205 := bbase (se 3 (by rfl) ⟨160913, by rfl⟩ : syracuseStep 858205 = 321827) (by norm_num)
theorem B759937 : Blo 674311 759937 := bbase (se 2 (by rfl) ⟨284976, by rfl⟩ : syracuseStep 759937 = 569953) (by norm_num)
theorem B3414149 : Blo 674311 3414149 := bbase (se 4 (by rfl) ⟨320076, by rfl⟩ : syracuseStep 3414149 = 640153) (by norm_num)
theorem B759973 : Blo 674311 759973 := bbase (se 4 (by rfl) ⟨71247, by rfl⟩ : syracuseStep 759973 = 142495) (by norm_num)
theorem B760009 : Blo 674311 760009 := bbase (se 2 (by rfl) ⟨285003, by rfl⟩ : syracuseStep 760009 = 570007) (by norm_num)
theorem B760045 : Blo 674311 760045 := bbase (se 3 (by rfl) ⟨142508, by rfl⟩ : syracuseStep 760045 = 285017) (by norm_num)
theorem B858377 : Blo 674311 858377 := bbase (se 2 (by rfl) ⟨321891, by rfl⟩ : syracuseStep 858377 = 643783) (by norm_num)
theorem B760081 : Blo 674311 760081 := bbase (se 2 (by rfl) ⟨285030, by rfl⟩ : syracuseStep 760081 = 570061) (by norm_num)
theorem B5478677 : Blo 674311 5478677 := bbase (se 6 (by rfl) ⟨128406, by rfl⟩ : syracuseStep 5478677 = 256813) (by norm_num)
theorem B760117 : Blo 674311 760117 := bbase (se 5 (by rfl) ⟨35630, by rfl⟩ : syracuseStep 760117 = 71261) (by norm_num)
theorem B858433 : Blo 674311 858433 := bbase (se 2 (by rfl) ⟨321912, by rfl⟩ : syracuseStep 858433 = 643825) (by norm_num)
theorem B1284437 : Blo 674311 1284437 := bbase (se 10 (by rfl) ⟨1881, by rfl⟩ : syracuseStep 1284437 = 3763) (by norm_num)
theorem B760153 : Blo 674311 760153 := bbase (se 2 (by rfl) ⟨285057, by rfl⟩ : syracuseStep 760153 = 570115) (by norm_num)
theorem B760189 : Blo 674311 760189 := bbase (se 3 (by rfl) ⟨142535, by rfl⟩ : syracuseStep 760189 = 285071) (by norm_num)
theorem B760225 : Blo 674311 760225 := bbase (se 2 (by rfl) ⟨285084, by rfl⟩ : syracuseStep 760225 = 570169) (by norm_num)
theorem B1710517 : Blo 674311 1710517 := bbase (se 5 (by rfl) ⟨80180, by rfl⟩ : syracuseStep 1710517 = 160361) (by norm_num)
theorem B760261 : Blo 674311 760261 := bbase (se 4 (by rfl) ⟨71274, by rfl⟩ : syracuseStep 760261 = 142549) (by norm_num)
theorem B760297 : Blo 674311 760297 := bbase (se 2 (by rfl) ⟨285111, by rfl⟩ : syracuseStep 760297 = 570223) (by norm_num)
theorem B1284589 : Blo 674311 1284589 := bbase (se 3 (by rfl) ⟨240860, by rfl⟩ : syracuseStep 1284589 = 481721) (by norm_num)
theorem B760333 : Blo 674311 760333 := bbase (se 3 (by rfl) ⟨142562, by rfl⟩ : syracuseStep 760333 = 285125) (by norm_num)
theorem B3840533 : Blo 674311 3840533 := bbase (se 6 (by rfl) ⟨90012, by rfl⟩ : syracuseStep 3840533 = 180025) (by norm_num)
theorem B1710629 : Blo 674311 1710629 := bbase (se 4 (by rfl) ⟨160371, by rfl⟩ : syracuseStep 1710629 = 320743) (by norm_num)
theorem B1546789 : Blo 674311 1546789 := bbase (se 4 (by rfl) ⟨145011, by rfl⟩ : syracuseStep 1546789 = 290023) (by norm_num)
theorem B760369 : Blo 674311 760369 := bbase (se 2 (by rfl) ⟨285138, by rfl⟩ : syracuseStep 760369 = 570277) (by norm_num)
theorem B760405 : Blo 674311 760405 := bbase (se 8 (by rfl) ⟨4455, by rfl⟩ : syracuseStep 760405 = 8911) (by norm_num)
theorem B760441 : Blo 674311 760441 := bbase (se 2 (by rfl) ⟨285165, by rfl⟩ : syracuseStep 760441 = 570331) (by norm_num)
theorem B5872277 : Blo 674311 5872277 := bbase (se 6 (by rfl) ⟨137631, by rfl⟩ : syracuseStep 5872277 = 275263) (by norm_num)
theorem B760477 : Blo 674311 760477 := bbase (se 3 (by rfl) ⟨142589, by rfl⟩ : syracuseStep 760477 = 285179) (by norm_num)
theorem B1317541 : Blo 674311 1317541 := bbase (se 4 (by rfl) ⟨123519, by rfl⟩ : syracuseStep 1317541 = 247039) (by norm_num)
theorem B760513 : Blo 674311 760513 := bbase (se 2 (by rfl) ⟨285192, by rfl⟩ : syracuseStep 760513 = 570385) (by norm_num)
theorem B1710821 : Blo 674311 1710821 := bbase (se 4 (by rfl) ⟨160389, by rfl⟩ : syracuseStep 1710821 = 320779) (by norm_num)
theorem B760549 : Blo 674311 760549 := bbase (se 4 (by rfl) ⟨71301, by rfl⟩ : syracuseStep 760549 = 142603) (by norm_num)
theorem B760585 : Blo 674311 760585 := bbase (se 2 (by rfl) ⟨285219, by rfl⟩ : syracuseStep 760585 = 570439) (by norm_num)
theorem B1284893 : Blo 674311 1284893 := bbase (se 3 (by rfl) ⟨240917, by rfl⟩ : syracuseStep 1284893 = 481835) (by norm_num)
theorem B760621 : Blo 674311 760621 := bbase (se 3 (by rfl) ⟨142616, by rfl⟩ : syracuseStep 760621 = 285233) (by norm_num)
theorem B760657 : Blo 674311 760657 := bbase (se 2 (by rfl) ⟨285246, by rfl⟩ : syracuseStep 760657 = 570493) (by norm_num)
theorem B760693 : Blo 674311 760693 := bbase (se 5 (by rfl) ⟨35657, by rfl⟩ : syracuseStep 760693 = 71315) (by norm_num)
theorem B760729 : Blo 674311 760729 := bbase (se 2 (by rfl) ⟨285273, by rfl⟩ : syracuseStep 760729 = 570547) (by norm_num)
theorem B760765 : Blo 674311 760765 := bbase (se 3 (by rfl) ⟨142643, by rfl⟩ : syracuseStep 760765 = 285287) (by norm_num)
theorem B760801 : Blo 674311 760801 := bbase (se 2 (by rfl) ⟨285300, by rfl⟩ : syracuseStep 760801 = 570601) (by norm_num)
theorem B760837 : Blo 674311 760837 := bbase (se 4 (by rfl) ⟨71328, by rfl⟩ : syracuseStep 760837 = 142657) (by norm_num)
theorem B760873 : Blo 674311 760873 := bbase (se 2 (by rfl) ⟨285327, by rfl⟩ : syracuseStep 760873 = 570655) (by norm_num)
theorem B1711165 : Blo 674311 1711165 := bbase (se 3 (by rfl) ⟨320843, by rfl⟩ : syracuseStep 1711165 = 641687) (by norm_num)
theorem B760909 : Blo 674311 760909 := bbase (se 3 (by rfl) ⟨142670, by rfl⟩ : syracuseStep 760909 = 285341) (by norm_num)
theorem B760945 : Blo 674311 760945 := bbase (se 2 (by rfl) ⟨285354, by rfl⟩ : syracuseStep 760945 = 570709) (by norm_num)
theorem B760981 : Blo 674311 760981 := bbase (se 6 (by rfl) ⟨17835, by rfl⟩ : syracuseStep 760981 = 35671) (by norm_num)
theorem B1711277 : Blo 674311 1711277 := bbase (se 3 (by rfl) ⟨320864, by rfl⟩ : syracuseStep 1711277 = 641729) (by norm_num)
theorem B761017 : Blo 674311 761017 := bbase (se 2 (by rfl) ⟨285381, by rfl⟩ : syracuseStep 761017 = 570763) (by norm_num)
theorem B2432197 : Blo 674311 2432197 := bbase (se 4 (by rfl) ⟨228018, by rfl⟩ : syracuseStep 2432197 = 456037) (by norm_num)
theorem B1219789 : Blo 674311 1219789 := bbase (se 3 (by rfl) ⟨228710, by rfl⟩ : syracuseStep 1219789 = 457421) (by norm_num)
theorem B2563285 : Blo 674311 2563285 := bbase (se 7 (by rfl) ⟨30038, by rfl⟩ : syracuseStep 2563285 = 60077) (by norm_num)
theorem B2923733 : Blo 674311 2923733 := bbase (se 7 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 2923733 = 68525) (by norm_num)
theorem B761053 : Blo 674311 761053 := bbase (se 3 (by rfl) ⟨142697, by rfl⟩ : syracuseStep 761053 = 285395) (by norm_num)
theorem B761089 : Blo 674311 761089 := bbase (se 2 (by rfl) ⟨285408, by rfl⟩ : syracuseStep 761089 = 570817) (by norm_num)
theorem B761125 : Blo 674311 761125 := bbase (se 4 (by rfl) ⟨71355, by rfl⟩ : syracuseStep 761125 = 142711) (by norm_num)
theorem B761161 : Blo 674311 761161 := bbase (se 2 (by rfl) ⟨285435, by rfl⟩ : syracuseStep 761161 = 570871) (by norm_num)
theorem B1711469 : Blo 674311 1711469 := bbase (se 3 (by rfl) ⟨320900, by rfl⟩ : syracuseStep 1711469 = 641801) (by norm_num)
theorem B761197 : Blo 674311 761197 := bbase (se 3 (by rfl) ⟨142724, by rfl⟩ : syracuseStep 761197 = 285449) (by norm_num)
theorem B761233 : Blo 674311 761233 := bbase (se 2 (by rfl) ⟨285462, by rfl⟩ : syracuseStep 761233 = 570925) (by norm_num)
theorem B3415445 : Blo 674311 3415445 := bbase (se 6 (by rfl) ⟨80049, by rfl⟩ : syracuseStep 3415445 = 160099) (by norm_num)
theorem B5774773 : Blo 674311 5774773 := bbase (se 5 (by rfl) ⟨270692, by rfl⟩ : syracuseStep 5774773 = 541385) (by norm_num)
theorem B761269 : Blo 674311 761269 := bbase (se 5 (by rfl) ⟨35684, by rfl⟩ : syracuseStep 761269 = 71369) (by norm_num)
theorem B761305 : Blo 674311 761305 := bbase (se 2 (by rfl) ⟨285489, by rfl⟩ : syracuseStep 761305 = 570979) (by norm_num)
theorem B1154557 : Blo 674311 1154557 := bbase (se 3 (by rfl) ⟨216479, by rfl⟩ : syracuseStep 1154557 = 432959) (by norm_num)
theorem B761341 : Blo 674311 761341 := bbase (se 3 (by rfl) ⟨142751, by rfl⟩ : syracuseStep 761341 = 285503) (by norm_num)
theorem B2563589 : Blo 674311 2563589 := bbase (se 4 (by rfl) ⟨240336, by rfl⟩ : syracuseStep 2563589 = 480673) (by norm_num)
theorem B1285645 : Blo 674311 1285645 := bbase (se 3 (by rfl) ⟨241058, by rfl⟩ : syracuseStep 1285645 = 482117) (by norm_num)
theorem B761377 : Blo 674311 761377 := bbase (se 2 (by rfl) ⟨285516, by rfl⟩ : syracuseStep 761377 = 571033) (by norm_num)
theorem B761413 : Blo 674311 761413 := bbase (se 4 (by rfl) ⟨71382, by rfl⟩ : syracuseStep 761413 = 142765) (by norm_num)
theorem B761449 : Blo 674311 761449 := bbase (se 2 (by rfl) ⟨285543, by rfl⟩ : syracuseStep 761449 = 571087) (by norm_num)
theorem B761485 : Blo 674311 761485 := bbase (se 3 (by rfl) ⟨142778, by rfl⟩ : syracuseStep 761485 = 285557) (by norm_num)
theorem B1285789 : Blo 674311 1285789 := bbase (se 3 (by rfl) ⟨241085, by rfl⟩ : syracuseStep 1285789 = 482171) (by norm_num)
theorem B761521 : Blo 674311 761521 := bbase (se 2 (by rfl) ⟨285570, by rfl⟩ : syracuseStep 761521 = 571141) (by norm_num)
theorem B1711813 : Blo 674311 1711813 := bbase (se 4 (by rfl) ⟨160482, by rfl⟩ : syracuseStep 1711813 = 320965) (by norm_num)
theorem B761557 : Blo 674311 761557 := bbase (se 7 (by rfl) ⟨8924, by rfl⟩ : syracuseStep 761557 = 17849) (by norm_num)
theorem B761593 : Blo 674311 761593 := bbase (se 2 (by rfl) ⟨285597, by rfl⟩ : syracuseStep 761593 = 571195) (by norm_num)
theorem B1154837 : Blo 674311 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B761629 : Blo 674311 761629 := bbase (se 3 (by rfl) ⟨142805, by rfl⟩ : syracuseStep 761629 = 285611) (by norm_num)
theorem B1711925 : Blo 674311 1711925 := bbase (se 5 (by rfl) ⟨80246, by rfl⟩ : syracuseStep 1711925 = 160493) (by norm_num)
theorem B1285949 : Blo 674311 1285949 := bbase (se 3 (by rfl) ⟨241115, by rfl⟩ : syracuseStep 1285949 = 482231) (by norm_num)
theorem B761665 : Blo 674311 761665 := bbase (se 2 (by rfl) ⟨285624, by rfl⟩ : syracuseStep 761665 = 571249) (by norm_num)
theorem B761701 : Blo 674311 761701 := bbase (se 4 (by rfl) ⟨71409, by rfl⟩ : syracuseStep 761701 = 142819) (by norm_num)
theorem B761737 : Blo 674311 761737 := bbase (se 2 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 761737 = 571303) (by norm_num)
theorem B761773 : Blo 674311 761773 := bbase (se 3 (by rfl) ⟨142832, by rfl⟩ : syracuseStep 761773 = 285665) (by norm_num)
theorem B1286093 : Blo 674311 1286093 := bbase (se 3 (by rfl) ⟨241142, by rfl⟩ : syracuseStep 1286093 = 482285) (by norm_num)
theorem B761809 : Blo 674311 761809 := bbase (se 2 (by rfl) ⟨285678, by rfl⟩ : syracuseStep 761809 = 571357) (by norm_num)
theorem B1712117 : Blo 674311 1712117 := bbase (se 5 (by rfl) ⟨80255, by rfl⟩ : syracuseStep 1712117 = 160511) (by norm_num)
theorem B761845 : Blo 674311 761845 := bbase (se 5 (by rfl) ⟨35711, by rfl⟩ : syracuseStep 761845 = 71423) (by norm_num)
theorem B1220597 : Blo 674311 1220597 := bbase (se 5 (by rfl) ⟨57215, by rfl⟩ : syracuseStep 1220597 = 114431) (by norm_num)
theorem B761881 : Blo 674311 761881 := bbase (se 2 (by rfl) ⟨285705, by rfl⟩ : syracuseStep 761881 = 571411) (by norm_num)
theorem B761917 : Blo 674311 761917 := bbase (se 3 (by rfl) ⟨142859, by rfl⟩ : syracuseStep 761917 = 285719) (by norm_num)
theorem B761953 : Blo 674311 761953 := bbase (se 2 (by rfl) ⟨285732, by rfl⟩ : syracuseStep 761953 = 571465) (by norm_num)
theorem B761989 : Blo 674311 761989 := bbase (se 4 (by rfl) ⟨71436, by rfl⟩ : syracuseStep 761989 = 142873) (by norm_num)
theorem B762025 : Blo 674311 762025 := bbase (se 2 (by rfl) ⟨285759, by rfl⟩ : syracuseStep 762025 = 571519) (by norm_num)
theorem B762061 : Blo 674311 762061 := bbase (se 3 (by rfl) ⟨142886, by rfl⟩ : syracuseStep 762061 = 285773) (by norm_num)
theorem B6496469 : Blo 674311 6496469 := bbase (se 7 (by rfl) ⟨76130, by rfl⟩ : syracuseStep 6496469 = 152261) (by norm_num)
theorem B2597093 : Blo 674311 2597093 := bbase (se 4 (by rfl) ⟨243477, by rfl⟩ : syracuseStep 2597093 = 486955) (by norm_num)
theorem B1286381 : Blo 674311 1286381 := bbase (se 3 (by rfl) ⟨241196, by rfl⟩ : syracuseStep 1286381 = 482393) (by norm_num)
theorem B762097 : Blo 674311 762097 := bbase (se 2 (by rfl) ⟨285786, by rfl⟩ : syracuseStep 762097 = 571573) (by norm_num)
theorem B762133 : Blo 674311 762133 := bbase (se 6 (by rfl) ⟨17862, by rfl⟩ : syracuseStep 762133 = 35725) (by norm_num)
theorem B762169 : Blo 674311 762169 := bbase (se 2 (by rfl) ⟨285813, by rfl⟩ : syracuseStep 762169 = 571627) (by norm_num)
theorem B1712461 : Blo 674311 1712461 := bbase (se 3 (by rfl) ⟨321086, by rfl⟩ : syracuseStep 1712461 = 642173) (by norm_num)
theorem B762205 : Blo 674311 762205 := bbase (se 3 (by rfl) ⟨142913, by rfl⟩ : syracuseStep 762205 = 285827) (by norm_num)
theorem B762241 : Blo 674311 762241 := bbase (se 2 (by rfl) ⟨285840, by rfl⟩ : syracuseStep 762241 = 571681) (by norm_num)
theorem B1286533 : Blo 674311 1286533 := bbase (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) (by norm_num)
theorem B762277 : Blo 674311 762277 := bbase (se 4 (by rfl) ⟨71463, by rfl⟩ : syracuseStep 762277 = 142927) (by norm_num)
theorem B1712573 : Blo 674311 1712573 := bbase (se 3 (by rfl) ⟨321107, by rfl⟩ : syracuseStep 1712573 = 642215) (by norm_num)
theorem B762313 : Blo 674311 762313 := bbase (se 2 (by rfl) ⟨285867, by rfl⟩ : syracuseStep 762313 = 571735) (by norm_num)
theorem B762349 : Blo 674311 762349 := bbase (se 3 (by rfl) ⟨142940, by rfl⟩ : syracuseStep 762349 = 285881) (by norm_num)
theorem B2892293 : Blo 674311 2892293 := bbase (se 4 (by rfl) ⟨271152, by rfl⟩ : syracuseStep 2892293 = 542305) (by norm_num)
theorem B762385 : Blo 674311 762385 := bbase (se 2 (by rfl) ⟨285894, by rfl⟩ : syracuseStep 762385 = 571789) (by norm_num)
theorem B762421 : Blo 674311 762421 := bbase (se 5 (by rfl) ⟨35738, by rfl⟩ : syracuseStep 762421 = 71477) (by norm_num)
theorem B1581637 : Blo 674311 1581637 := bbase (se 4 (by rfl) ⟨148278, by rfl⟩ : syracuseStep 1581637 = 296557) (by norm_num)
theorem B762457 : Blo 674311 762457 := bbase (se 2 (by rfl) ⟨285921, by rfl⟩ : syracuseStep 762457 = 571843) (by norm_num)
theorem B1712765 : Blo 674311 1712765 := bbase (se 3 (by rfl) ⟨321143, by rfl⟩ : syracuseStep 1712765 = 642287) (by norm_num)
theorem B762493 : Blo 674311 762493 := bbase (se 3 (by rfl) ⟨142967, by rfl⟩ : syracuseStep 762493 = 285935) (by norm_num)
theorem B762529 : Blo 674311 762529 := bbase (se 2 (by rfl) ⟨285948, by rfl⟩ : syracuseStep 762529 = 571897) (by norm_num)
theorem B3416741 : Blo 674311 3416741 := bbase (se 4 (by rfl) ⟨320319, by rfl⟩ : syracuseStep 3416741 = 640639) (by norm_num)
theorem B3842741 : Blo 674311 3842741 := bbase (se 5 (by rfl) ⟨180128, by rfl⟩ : syracuseStep 3842741 = 360257) (by norm_num)
theorem B1286837 : Blo 674311 1286837 := bbase (se 5 (by rfl) ⟨60320, by rfl⟩ : syracuseStep 1286837 = 120641) (by norm_num)
theorem B762565 : Blo 674311 762565 := bbase (se 4 (by rfl) ⟨71490, by rfl⟩ : syracuseStep 762565 = 142981) (by norm_num)
theorem B762601 : Blo 674311 762601 := bbase (se 2 (by rfl) ⟨285975, by rfl⟩ : syracuseStep 762601 = 571951) (by norm_num)
theorem B762637 : Blo 674311 762637 := bbase (se 3 (by rfl) ⟨142994, by rfl⟩ : syracuseStep 762637 = 285989) (by norm_num)
theorem B2892581 : Blo 674311 2892581 := bbase (se 4 (by rfl) ⟨271179, by rfl⟩ : syracuseStep 2892581 = 542359) (by norm_num)
theorem B762673 : Blo 674311 762673 := bbase (se 2 (by rfl) ⟨286002, by rfl⟩ : syracuseStep 762673 = 572005) (by norm_num)
theorem B3253061 : Blo 674311 3253061 := bbase (se 4 (by rfl) ⟨304974, by rfl⟩ : syracuseStep 3253061 = 609949) (by norm_num)
theorem B762709 : Blo 674311 762709 := bbase (se 9 (by rfl) ⟨2234, by rfl⟩ : syracuseStep 762709 = 4469) (by norm_num)
theorem B762745 : Blo 674311 762745 := bbase (se 2 (by rfl) ⟨286029, by rfl⟩ : syracuseStep 762745 = 572059) (by norm_num)
theorem B762781 : Blo 674311 762781 := bbase (se 3 (by rfl) ⟨143021, by rfl⟩ : syracuseStep 762781 = 286043) (by norm_num)
theorem B762817 : Blo 674311 762817 := bbase (se 2 (by rfl) ⟨286056, by rfl⟩ : syracuseStep 762817 = 572113) (by norm_num)
theorem B5120981 : Blo 674311 5120981 := bbase (se 7 (by rfl) ⟨60011, by rfl⟩ : syracuseStep 5120981 = 120023) (by norm_num)
theorem B1713109 : Blo 674311 1713109 := bbase (se 7 (by rfl) ⟨20075, by rfl⟩ : syracuseStep 1713109 = 40151) (by norm_num)
theorem B762853 : Blo 674311 762853 := bbase (se 4 (by rfl) ⟨71517, by rfl⟩ : syracuseStep 762853 = 143035) (by norm_num)
theorem B762889 : Blo 674311 762889 := bbase (se 2 (by rfl) ⟨286083, by rfl⟩ : syracuseStep 762889 = 572167) (by norm_num)
theorem B762925 : Blo 674311 762925 := bbase (se 3 (by rfl) ⟨143048, by rfl⟩ : syracuseStep 762925 = 286097) (by norm_num)
theorem B1713221 : Blo 674311 1713221 := bbase (se 4 (by rfl) ⟨160614, by rfl⟩ : syracuseStep 1713221 = 321229) (by norm_num)
theorem B762961 : Blo 674311 762961 := bbase (se 2 (by rfl) ⟨286110, by rfl⟩ : syracuseStep 762961 = 572221) (by norm_num)
theorem B762997 : Blo 674311 762997 := bbase (se 5 (by rfl) ⟨35765, by rfl⟩ : syracuseStep 762997 = 71531) (by norm_num)
theorem B763033 : Blo 674311 763033 := bbase (se 2 (by rfl) ⟨286137, by rfl⟩ : syracuseStep 763033 = 572275) (by norm_num)
theorem B763069 : Blo 674311 763069 := bbase (se 3 (by rfl) ⟨143075, by rfl⟩ : syracuseStep 763069 = 286151) (by norm_num)
theorem B2172101 : Blo 674311 2172101 := bbase (se 4 (by rfl) ⟨203634, by rfl⟩ : syracuseStep 2172101 = 407269) (by norm_num)
theorem B1713413 : Blo 674311 1713413 := bbase (se 4 (by rfl) ⟨160632, by rfl⟩ : syracuseStep 1713413 = 321265) (by norm_num)
theorem B5776757 : Blo 674311 5776757 := bbase (se 5 (by rfl) ⟨270785, by rfl⟩ : syracuseStep 5776757 = 541571) (by norm_num)
theorem B1287589 : Blo 674311 1287589 := bbase (se 4 (by rfl) ⟨120711, by rfl⟩ : syracuseStep 1287589 = 241423) (by norm_num)
theorem B4335029 : Blo 674311 4335029 := bbase (se 5 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 4335029 = 406409) (by norm_num)
theorem B3253733 : Blo 674311 3253733 := bbase (se 4 (by rfl) ⟨305037, by rfl⟩ : syracuseStep 3253733 = 610075) (by norm_num)
theorem B1156589 : Blo 674311 1156589 := bbase (se 3 (by rfl) ⟨216860, by rfl⟩ : syracuseStep 1156589 = 433721) (by norm_num)
theorem B2893333 : Blo 674311 2893333 := bbase (se 6 (by rfl) ⟨67812, by rfl⟩ : syracuseStep 2893333 = 135625) (by norm_num)
theorem B1287733 : Blo 674311 1287733 := bbase (se 5 (by rfl) ⟨60362, by rfl⟩ : syracuseStep 1287733 = 120725) (by norm_num)
theorem B2565701 : Blo 674311 2565701 := bbase (se 4 (by rfl) ⟨240534, by rfl⟩ : syracuseStep 2565701 = 481069) (by norm_num)
theorem B1713757 : Blo 674311 1713757 := bbase (se 3 (by rfl) ⟨321329, by rfl⟩ : syracuseStep 1713757 = 642659) (by norm_num)
theorem B1517237 : Blo 674311 1517237 := bbase (se 5 (by rfl) ⟨71120, by rfl⟩ : syracuseStep 1517237 = 142241) (by norm_num)
theorem B1713869 : Blo 674311 1713869 := bbase (se 3 (by rfl) ⟨321350, by rfl⟩ : syracuseStep 1713869 = 642701) (by norm_num)
theorem B1517309 : Blo 674311 1517309 := bbase (se 3 (by rfl) ⟨284495, by rfl⟩ : syracuseStep 1517309 = 568991) (by norm_num)
theorem B1517381 : Blo 674311 1517381 := bbase (se 4 (by rfl) ⟨142254, by rfl⟩ : syracuseStep 1517381 = 284509) (by norm_num)
theorem B2565989 : Blo 674311 2565989 := bbase (se 4 (by rfl) ⟨240561, by rfl⟩ : syracuseStep 2565989 = 481123) (by norm_num)
theorem B1517453 : Blo 674311 1517453 := bbase (se 3 (by rfl) ⟨284522, by rfl⟩ : syracuseStep 1517453 = 569045) (by norm_num)
theorem B1714061 : Blo 674311 1714061 := bbase (se 3 (by rfl) ⟨321386, by rfl⟩ : syracuseStep 1714061 = 642773) (by norm_num)
theorem B3418037 : Blo 674311 3418037 := bbase (se 5 (by rfl) ⟨160220, by rfl⟩ : syracuseStep 3418037 = 320441) (by norm_num)
theorem B1517525 : Blo 674311 1517525 := bbase (se 7 (by rfl) ⟨17783, by rfl⟩ : syracuseStep 1517525 = 35567) (by norm_num)
theorem B1517597 : Blo 674311 1517597 := bbase (se 3 (by rfl) ⟨284549, by rfl⟩ : syracuseStep 1517597 = 569099) (by norm_num)
theorem B960589 : Blo 674311 960589 := bbase (se 3 (by rfl) ⟨180110, by rfl⟩ : syracuseStep 960589 = 360221) (by norm_num)
theorem B2173013 : Blo 674311 2173013 := bbase (se 8 (by rfl) ⟨12732, by rfl⟩ : syracuseStep 2173013 = 25465) (by norm_num)
theorem B1517669 : Blo 674311 1517669 := bbase (se 4 (by rfl) ⟨142281, by rfl⟩ : syracuseStep 1517669 = 284563) (by norm_num)
theorem B1517741 : Blo 674311 1517741 := bbase (se 3 (by rfl) ⟨284576, by rfl⟩ : syracuseStep 1517741 = 569153) (by norm_num)
theorem B1714405 : Blo 674311 1714405 := bbase (se 4 (by rfl) ⟨160725, by rfl⟩ : syracuseStep 1714405 = 321451) (by norm_num)
theorem B1517813 : Blo 674311 1517813 := bbase (se 5 (by rfl) ⟨71147, by rfl⟩ : syracuseStep 1517813 = 142295) (by norm_num)
theorem B2894069 : Blo 674311 2894069 := bbase (se 5 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 2894069 = 271319) (by norm_num)
theorem B1517885 : Blo 674311 1517885 := bbase (se 3 (by rfl) ⟨284603, by rfl⟩ : syracuseStep 1517885 = 569207) (by norm_num)
theorem B1714517 : Blo 674311 1714517 := bbase (se 10 (by rfl) ⟨2511, by rfl⟩ : syracuseStep 1714517 = 5023) (by norm_num)
theorem B731489 : Blo 674311 731489 := bbase (se 2 (by rfl) ⟨274308, by rfl⟩ : syracuseStep 731489 = 548617) (by norm_num)
theorem B1517957 : Blo 674311 1517957 := bbase (se 4 (by rfl) ⟨142308, by rfl⟩ : syracuseStep 1517957 = 284617) (by norm_num)
theorem B960925 : Blo 674311 960925 := bbase (se 3 (by rfl) ⟨180173, by rfl⟩ : syracuseStep 960925 = 360347) (by norm_num)
theorem B1518029 : Blo 674311 1518029 := bbase (se 3 (by rfl) ⟨284630, by rfl⟩ : syracuseStep 1518029 = 569261) (by norm_num)
theorem B1518101 : Blo 674311 1518101 := bbase (se 6 (by rfl) ⟨35580, by rfl⟩ : syracuseStep 1518101 = 71161) (by norm_num)
theorem B1714709 : Blo 674311 1714709 := bbase (se 6 (by rfl) ⟨40188, by rfl⟩ : syracuseStep 1714709 = 80377) (by norm_num)
theorem B1518173 : Blo 674311 1518173 := bbase (se 3 (by rfl) ⟨284657, by rfl⟩ : syracuseStep 1518173 = 569315) (by norm_num)
theorem B961141 : Blo 674311 961141 := bbase (se 5 (by rfl) ⟨45053, by rfl⟩ : syracuseStep 961141 = 90107) (by norm_num)
theorem B1518245 : Blo 674311 1518245 := bbase (se 4 (by rfl) ⟨142335, by rfl⟩ : syracuseStep 1518245 = 284671) (by norm_num)
theorem B1518317 : Blo 674311 1518317 := bbase (se 3 (by rfl) ⟨284684, by rfl⟩ : syracuseStep 1518317 = 569369) (by norm_num)
theorem B1518389 : Blo 674311 1518389 := bbase (se 5 (by rfl) ⟨71174, by rfl⟩ : syracuseStep 1518389 = 142349) (by norm_num)
theorem B1715053 : Blo 674311 1715053 := bbase (se 3 (by rfl) ⟨321572, by rfl⟩ : syracuseStep 1715053 = 643145) (by norm_num)
theorem B1518461 : Blo 674311 1518461 := bbase (se 3 (by rfl) ⟨284711, by rfl⟩ : syracuseStep 1518461 = 569423) (by norm_num)
theorem B1518533 : Blo 674311 1518533 := bbase (se 4 (by rfl) ⟨142362, by rfl⟩ : syracuseStep 1518533 = 284725) (by norm_num)
theorem B1715165 : Blo 674311 1715165 := bbase (se 3 (by rfl) ⟨321593, by rfl⟩ : syracuseStep 1715165 = 643187) (by norm_num)
theorem B961517 : Blo 674311 961517 := bbase (se 3 (by rfl) ⟨180284, by rfl⟩ : syracuseStep 961517 = 360569) (by norm_num)
theorem B2567173 : Blo 674311 2567173 := bbase (se 4 (by rfl) ⟨240672, by rfl⟩ : syracuseStep 2567173 = 481345) (by norm_num)
theorem B1518605 : Blo 674311 1518605 := bbase (se 3 (by rfl) ⟨284738, by rfl⟩ : syracuseStep 1518605 = 569477) (by norm_num)
theorem B1518677 : Blo 674311 1518677 := bbase (se 8 (by rfl) ⟨8898, by rfl⟩ : syracuseStep 1518677 = 17797) (by norm_num)
theorem B1518749 : Blo 674311 1518749 := bbase (se 3 (by rfl) ⟨284765, by rfl⟩ : syracuseStep 1518749 = 569531) (by norm_num)
theorem B1715357 : Blo 674311 1715357 := bbase (se 3 (by rfl) ⟨321629, by rfl⟩ : syracuseStep 1715357 = 643259) (by norm_num)
theorem B3419333 : Blo 674311 3419333 := bbase (se 4 (by rfl) ⟨320562, by rfl⟩ : syracuseStep 3419333 = 641125) (by norm_num)
theorem B1518821 : Blo 674311 1518821 := bbase (se 4 (by rfl) ⟨142389, by rfl⟩ : syracuseStep 1518821 = 284779) (by norm_num)
theorem B1518893 : Blo 674311 1518893 := bbase (se 3 (by rfl) ⟨284792, by rfl⟩ : syracuseStep 1518893 = 569585) (by norm_num)
theorem B2567477 : Blo 674311 2567477 := bbase (se 5 (by rfl) ⟨120350, by rfl⟩ : syracuseStep 2567477 = 240701) (by norm_num)
theorem B1518965 : Blo 674311 1518965 := bbase (se 5 (by rfl) ⟨71201, by rfl⟩ : syracuseStep 1518965 = 142403) (by norm_num)
theorem B1486237 : Blo 674311 1486237 := bbase (se 3 (by rfl) ⟨278669, by rfl⟩ : syracuseStep 1486237 = 557339) (by norm_num)
theorem B1519037 : Blo 674311 1519037 := bbase (se 3 (by rfl) ⟨284819, by rfl⟩ : syracuseStep 1519037 = 569639) (by norm_num)
theorem B2436581 : Blo 674311 2436581 := bbase (se 4 (by rfl) ⟨228429, by rfl⟩ : syracuseStep 2436581 = 456859) (by norm_num)
theorem B1715701 : Blo 674311 1715701 := bbase (se 5 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 1715701 = 160847) (by norm_num)
theorem B1519109 : Blo 674311 1519109 := bbase (se 4 (by rfl) ⟨142416, by rfl⟩ : syracuseStep 1519109 = 284833) (by norm_num)
theorem B1519181 : Blo 674311 1519181 := bbase (se 3 (by rfl) ⟨284846, by rfl⟩ : syracuseStep 1519181 = 569693) (by norm_num)
theorem B1715813 : Blo 674311 1715813 := bbase (se 4 (by rfl) ⟨160857, by rfl⟩ : syracuseStep 1715813 = 321715) (by norm_num)
theorem B1519253 : Blo 674311 1519253 := bbase (se 6 (by rfl) ⟨35607, by rfl⟩ : syracuseStep 1519253 = 71215) (by norm_num)
theorem B1519325 : Blo 674311 1519325 := bbase (se 3 (by rfl) ⟨284873, by rfl⟩ : syracuseStep 1519325 = 569747) (by norm_num)
theorem B1519397 : Blo 674311 1519397 := bbase (se 4 (by rfl) ⟨142443, by rfl⟩ : syracuseStep 1519397 = 284887) (by norm_num)
theorem B1716005 : Blo 674311 1716005 := bbase (se 4 (by rfl) ⟨160875, by rfl⟩ : syracuseStep 1716005 = 321751) (by norm_num)
theorem B1027885 : Blo 674311 1027885 := bbase (se 3 (by rfl) ⟨192728, by rfl⟩ : syracuseStep 1027885 = 385457) (by norm_num)
theorem B1519469 : Blo 674311 1519469 := bbase (se 3 (by rfl) ⟨284900, by rfl⟩ : syracuseStep 1519469 = 569801) (by norm_num)
theorem B1027957 : Blo 674311 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B1027981 : Blo 674311 1027981 := bbase (se 3 (by rfl) ⟨192746, by rfl⟩ : syracuseStep 1027981 = 385493) (by norm_num)
theorem B1519541 : Blo 674311 1519541 := bbase (se 5 (by rfl) ⟨71228, by rfl⟩ : syracuseStep 1519541 = 142457) (by norm_num)
theorem B1519613 : Blo 674311 1519613 := bbase (se 3 (by rfl) ⟨284927, by rfl⟩ : syracuseStep 1519613 = 569855) (by norm_num)
theorem B1519685 : Blo 674311 1519685 := bbase (se 4 (by rfl) ⟨142470, by rfl⟩ : syracuseStep 1519685 = 284941) (by norm_num)
theorem B1716349 : Blo 674311 1716349 := bbase (se 3 (by rfl) ⟨321815, by rfl⟩ : syracuseStep 1716349 = 643631) (by norm_num)
theorem B1519757 : Blo 674311 1519757 := bbase (se 3 (by rfl) ⟨284954, by rfl⟩ : syracuseStep 1519757 = 569909) (by norm_num)
theorem B1519829 : Blo 674311 1519829 := bbase (se 7 (by rfl) ⟨17810, by rfl⟩ : syracuseStep 1519829 = 35621) (by norm_num)
theorem B1716461 : Blo 674311 1716461 := bbase (se 3 (by rfl) ⟨321836, by rfl⟩ : syracuseStep 1716461 = 643673) (by norm_num)
theorem B1519901 : Blo 674311 1519901 := bbase (se 3 (by rfl) ⟨284981, by rfl⟩ : syracuseStep 1519901 = 569963) (by norm_num)
theorem B1519973 : Blo 674311 1519973 := bbase (se 4 (by rfl) ⟨142497, by rfl⟩ : syracuseStep 1519973 = 284995) (by norm_num)
theorem B962941 : Blo 674311 962941 := bbase (se 3 (by rfl) ⟨180551, by rfl⟩ : syracuseStep 962941 = 361103) (by norm_num)
theorem B1520045 : Blo 674311 1520045 := bbase (se 3 (by rfl) ⟨285008, by rfl⟩ : syracuseStep 1520045 = 570017) (by norm_num)
theorem B1716653 : Blo 674311 1716653 := bbase (se 3 (by rfl) ⟨321872, by rfl⟩ : syracuseStep 1716653 = 643745) (by norm_num)
theorem B3420629 : Blo 674311 3420629 := bbase (se 7 (by rfl) ⟨40085, by rfl⟩ : syracuseStep 3420629 = 80171) (by norm_num)
theorem B1520117 : Blo 674311 1520117 := bbase (se 5 (by rfl) ⟨71255, by rfl⟩ : syracuseStep 1520117 = 142511) (by norm_num)
theorem B3650069 : Blo 674311 3650069 := bbase (se 6 (by rfl) ⟨85548, by rfl⟩ : syracuseStep 3650069 = 171097) (by norm_num)
theorem B1520189 : Blo 674311 1520189 := bbase (se 3 (by rfl) ⟨285035, by rfl⟩ : syracuseStep 1520189 = 570071) (by norm_num)
theorem B1520261 : Blo 674311 1520261 := bbase (se 4 (by rfl) ⟨142524, by rfl⟩ : syracuseStep 1520261 = 285049) (by norm_num)
theorem B4108981 : Blo 674311 4108981 := bbase (se 5 (by rfl) ⟨192608, by rfl⟩ : syracuseStep 4108981 = 385217) (by norm_num)
theorem B1520333 : Blo 674311 1520333 := bbase (se 3 (by rfl) ⟨285062, by rfl⟩ : syracuseStep 1520333 = 570125) (by norm_num)
theorem B1159901 : Blo 674311 1159901 := bbase (se 3 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 1159901 = 434963) (by norm_num)
theorem B1520405 : Blo 674311 1520405 := bbase (se 6 (by rfl) ⟨35634, by rfl⟩ : syracuseStep 1520405 = 71269) (by norm_num)
theorem B1520477 : Blo 674311 1520477 := bbase (se 3 (by rfl) ⟨285089, by rfl⟩ : syracuseStep 1520477 = 570179) (by norm_num)
theorem B1520549 : Blo 674311 1520549 := bbase (se 4 (by rfl) ⟨142551, by rfl⟩ : syracuseStep 1520549 = 285103) (by norm_num)
theorem B963533 : Blo 674311 963533 := bbase (se 3 (by rfl) ⟨180662, by rfl⟩ : syracuseStep 963533 = 361325) (by norm_num)
theorem B1520621 : Blo 674311 1520621 := bbase (se 3 (by rfl) ⟨285116, by rfl⟩ : syracuseStep 1520621 = 570233) (by norm_num)
theorem B3716117 : Blo 674311 3716117 := bbase (se 6 (by rfl) ⟨87096, by rfl⟩ : syracuseStep 3716117 = 174193) (by norm_num)
theorem B963613 : Blo 674311 963613 := bbase (se 3 (by rfl) ⟨180677, by rfl⟩ : syracuseStep 963613 = 361355) (by norm_num)
theorem B1520693 : Blo 674311 1520693 := bbase (se 5 (by rfl) ⟨71282, by rfl⟩ : syracuseStep 1520693 = 142565) (by norm_num)
theorem B1520765 : Blo 674311 1520765 := bbase (se 3 (by rfl) ⟨285143, by rfl⟩ : syracuseStep 1520765 = 570287) (by norm_num)
theorem B963733 : Blo 674311 963733 := bbase (se 6 (by rfl) ⟨22587, by rfl⟩ : syracuseStep 963733 = 45175) (by norm_num)
theorem B2438309 : Blo 674311 2438309 := bbase (se 4 (by rfl) ⟨228591, by rfl⟩ : syracuseStep 2438309 = 457183) (by norm_num)
theorem B1520837 : Blo 674311 1520837 := bbase (se 4 (by rfl) ⟨142578, by rfl⟩ : syracuseStep 1520837 = 285157) (by norm_num)
theorem B963829 : Blo 674311 963829 := bbase (se 5 (by rfl) ⟨45179, by rfl⟩ : syracuseStep 963829 = 90359) (by norm_num)
theorem B1520909 : Blo 674311 1520909 := bbase (se 3 (by rfl) ⟨285170, by rfl⟩ : syracuseStep 1520909 = 570341) (by norm_num)
theorem B1520981 : Blo 674311 1520981 := bbase (se 13 (by rfl) ⟨278, by rfl⟩ : syracuseStep 1520981 = 557) (by norm_num)
theorem B2569589 : Blo 674311 2569589 := bbase (se 5 (by rfl) ⟨120449, by rfl⟩ : syracuseStep 2569589 = 240899) (by norm_num)
theorem B1521053 : Blo 674311 1521053 := bbase (se 3 (by rfl) ⟨285197, by rfl⟩ : syracuseStep 1521053 = 570395) (by norm_num)
theorem B3716533 : Blo 674311 3716533 := bbase (se 5 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 3716533 = 348425) (by norm_num)
theorem B2897365 : Blo 674311 2897365 := bbase (se 7 (by rfl) ⟨33953, by rfl⟩ : syracuseStep 2897365 = 67907) (by norm_num)
theorem B865753 : Blo 674311 865753 := bbase (se 2 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 865753 = 649315) (by norm_num)
theorem B1521125 : Blo 674311 1521125 := bbase (se 4 (by rfl) ⟨142605, by rfl⟩ : syracuseStep 1521125 = 285211) (by norm_num)
theorem B1521197 : Blo 674311 1521197 := bbase (se 3 (by rfl) ⟨285224, by rfl⟩ : syracuseStep 1521197 = 570449) (by norm_num)
theorem B1390189 : Blo 674311 1390189 := bbase (se 3 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 1390189 = 521321) (by norm_num)
theorem B1521269 : Blo 674311 1521269 := bbase (se 5 (by rfl) ⟨71309, by rfl⟩ : syracuseStep 1521269 = 142619) (by norm_num)
theorem B2569877 : Blo 674311 2569877 := bbase (se 6 (by rfl) ⟨60231, by rfl⟩ : syracuseStep 2569877 = 120463) (by norm_num)
theorem B1521341 : Blo 674311 1521341 := bbase (se 3 (by rfl) ⟨285251, by rfl⟩ : syracuseStep 1521341 = 570503) (by norm_num)
theorem B4863701 : Blo 674311 4863701 := bbase (se 7 (by rfl) ⟨56996, by rfl⟩ : syracuseStep 4863701 = 113993) (by norm_num)
theorem B3421925 : Blo 674311 3421925 := bbase (se 4 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 3421925 = 641611) (by norm_num)
theorem B964325 : Blo 674311 964325 := bbase (se 4 (by rfl) ⟨90405, by rfl⟩ : syracuseStep 964325 = 180811) (by norm_num)
theorem B1521413 : Blo 674311 1521413 := bbase (se 4 (by rfl) ⟨142632, by rfl⟩ : syracuseStep 1521413 = 285265) (by norm_num)
theorem B1521485 : Blo 674311 1521485 := bbase (se 3 (by rfl) ⟨285278, by rfl⟩ : syracuseStep 1521485 = 570557) (by norm_num)
theorem B1947493 : Blo 674311 1947493 := bbase (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) (by norm_num)
theorem B1521557 : Blo 674311 1521557 := bbase (se 6 (by rfl) ⟨35661, by rfl⟩ : syracuseStep 1521557 = 71323) (by norm_num)
theorem B1521629 : Blo 674311 1521629 := bbase (se 3 (by rfl) ⟨285305, by rfl⟩ : syracuseStep 1521629 = 570611) (by norm_num)
theorem B1521701 : Blo 674311 1521701 := bbase (se 4 (by rfl) ⟨142659, by rfl⟩ : syracuseStep 1521701 = 285319) (by norm_num)
theorem B1521773 : Blo 674311 1521773 := bbase (se 3 (by rfl) ⟨285332, by rfl⟩ : syracuseStep 1521773 = 570665) (by norm_num)
theorem B1521845 : Blo 674311 1521845 := bbase (se 5 (by rfl) ⟨71336, by rfl⟩ : syracuseStep 1521845 = 142673) (by norm_num)
theorem B1521917 : Blo 674311 1521917 := bbase (se 3 (by rfl) ⟨285359, by rfl⟩ : syracuseStep 1521917 = 570719) (by norm_num)
theorem B964877 : Blo 674311 964877 := bbase (se 3 (by rfl) ⟨180914, by rfl⟩ : syracuseStep 964877 = 361829) (by norm_num)
theorem B1521989 : Blo 674311 1521989 := bbase (se 4 (by rfl) ⟨142686, by rfl⟩ : syracuseStep 1521989 = 285373) (by norm_num)
theorem B1980805 : Blo 674311 1980805 := bbase (se 4 (by rfl) ⟨185700, by rfl⟩ : syracuseStep 1980805 = 371401) (by norm_num)
theorem B1522061 : Blo 674311 1522061 := bbase (se 3 (by rfl) ⟨285386, by rfl⟩ : syracuseStep 1522061 = 570773) (by norm_num)
theorem B1030573 : Blo 674311 1030573 := bbase (se 3 (by rfl) ⟨193232, by rfl⟩ : syracuseStep 1030573 = 386465) (by norm_num)
theorem B1522133 : Blo 674311 1522133 := bbase (se 7 (by rfl) ⟨17837, by rfl⟩ : syracuseStep 1522133 = 35675) (by norm_num)
theorem B2275829 : Blo 674311 2275829 := bbase (se 5 (by rfl) ⟨106679, by rfl⟩ : syracuseStep 2275829 = 213359) (by norm_num)
theorem B1522205 : Blo 674311 1522205 := bbase (se 3 (by rfl) ⟨285413, by rfl⟩ : syracuseStep 1522205 = 570827) (by norm_num)
theorem B1620533 : Blo 674311 1620533 := bbase (se 5 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 1620533 = 151925) (by norm_num)
theorem B2964053 : Blo 674311 2964053 := bbase (se 8 (by rfl) ⟨17367, by rfl⟩ : syracuseStep 2964053 = 34735) (by norm_num)
theorem B1522277 : Blo 674311 1522277 := bbase (se 4 (by rfl) ⟨142713, by rfl⟩ : syracuseStep 1522277 = 285427) (by norm_num)
theorem B1522349 : Blo 674311 1522349 := bbase (se 3 (by rfl) ⟨285440, by rfl⟩ : syracuseStep 1522349 = 570881) (by norm_num)
theorem B1784533 : Blo 674311 1784533 := bbase (se 7 (by rfl) ⟨20912, by rfl⟩ : syracuseStep 1784533 = 41825) (by norm_num)
theorem B1030877 : Blo 674311 1030877 := bbase (se 3 (by rfl) ⟨193289, by rfl⟩ : syracuseStep 1030877 = 386579) (by norm_num)
theorem B1522421 : Blo 674311 1522421 := bbase (se 5 (by rfl) ⟨71363, by rfl⟩ : syracuseStep 1522421 = 142727) (by norm_num)
theorem B867125 : Blo 674311 867125 := bbase (se 5 (by rfl) ⟨40646, by rfl⟩ : syracuseStep 867125 = 81293) (by norm_num)
theorem B1391413 : Blo 674311 1391413 := bbase (se 5 (by rfl) ⟨65222, by rfl⟩ : syracuseStep 1391413 = 130445) (by norm_num)
theorem B2571061 : Blo 674311 2571061 := bbase (se 5 (by rfl) ⟨120518, by rfl⟩ : syracuseStep 2571061 = 241037) (by norm_num)
theorem B1522493 : Blo 674311 1522493 := bbase (se 3 (by rfl) ⟨285467, by rfl⟩ : syracuseStep 1522493 = 570935) (by norm_num)
theorem B1522565 : Blo 674311 1522565 := bbase (se 4 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 1522565 = 285481) (by norm_num)
theorem B2276261 : Blo 674311 2276261 := bbase (se 4 (by rfl) ⟨213399, by rfl⟩ : syracuseStep 2276261 = 426799) (by norm_num)
theorem B1522637 : Blo 674311 1522637 := bbase (se 3 (by rfl) ⟨285494, by rfl⟩ : syracuseStep 1522637 = 570989) (by norm_num)
theorem B3423221 : Blo 674311 3423221 := bbase (se 5 (by rfl) ⟨160463, by rfl⟩ : syracuseStep 3423221 = 320927) (by norm_num)
theorem B965629 : Blo 674311 965629 := bbase (se 3 (by rfl) ⟨181055, by rfl⟩ : syracuseStep 965629 = 362111) (by norm_num)
theorem B1522709 : Blo 674311 1522709 := bbase (se 6 (by rfl) ⟨35688, by rfl⟩ : syracuseStep 1522709 = 71377) (by norm_num)
theorem B1522781 : Blo 674311 1522781 := bbase (se 3 (by rfl) ⟨285521, by rfl⟩ : syracuseStep 1522781 = 571043) (by norm_num)
theorem B2571365 : Blo 674311 2571365 := bbase (se 4 (by rfl) ⟨241065, by rfl⟩ : syracuseStep 2571365 = 482131) (by norm_num)
theorem B1850485 : Blo 674311 1850485 := bbase (se 5 (by rfl) ⟨86741, by rfl⟩ : syracuseStep 1850485 = 173483) (by norm_num)
theorem B8666261 : Blo 674311 8666261 := bbase (se 6 (by rfl) ⟨203115, by rfl⟩ : syracuseStep 8666261 = 406231) (by norm_num)
theorem B1522853 : Blo 674311 1522853 := bbase (se 4 (by rfl) ⟨142767, by rfl⟩ : syracuseStep 1522853 = 285535) (by norm_num)
theorem B1522925 : Blo 674311 1522925 := bbase (se 3 (by rfl) ⟨285548, by rfl⟩ : syracuseStep 1522925 = 571097) (by norm_num)
theorem B1522997 : Blo 674311 1522997 := bbase (se 5 (by rfl) ⟨71390, by rfl⟩ : syracuseStep 1522997 = 142781) (by norm_num)
theorem B2276693 : Blo 674311 2276693 := bbase (se 11 (by rfl) ⟨1667, by rfl⟩ : syracuseStep 2276693 = 3335) (by norm_num)
theorem B2735477 : Blo 674311 2735477 := bbase (se 5 (by rfl) ⟨128225, by rfl⟩ : syracuseStep 2735477 = 256451) (by norm_num)
theorem B1523069 : Blo 674311 1523069 := bbase (se 3 (by rfl) ⟨285575, by rfl⟩ : syracuseStep 1523069 = 571151) (by norm_num)
theorem B1523141 : Blo 674311 1523141 := bbase (se 4 (by rfl) ⟨142794, by rfl⟩ : syracuseStep 1523141 = 285589) (by norm_num)
theorem B1523213 : Blo 674311 1523213 := bbase (se 3 (by rfl) ⟨285602, by rfl⟩ : syracuseStep 1523213 = 571205) (by norm_num)
theorem B1523285 : Blo 674311 1523285 := bbase (se 8 (by rfl) ⟨8925, by rfl⟩ : syracuseStep 1523285 = 17851) (by norm_num)
theorem B769645 : Blo 674311 769645 := bbase (se 3 (by rfl) ⟨144308, by rfl⟩ : syracuseStep 769645 = 288617) (by norm_num)
theorem B1523357 : Blo 674311 1523357 := bbase (se 3 (by rfl) ⟨285629, by rfl⟩ : syracuseStep 1523357 = 571259) (by norm_num)
theorem B769765 : Blo 674311 769765 := bbase (se 4 (by rfl) ⟨72165, by rfl⟩ : syracuseStep 769765 = 144331) (by norm_num)
theorem B1523429 : Blo 674311 1523429 := bbase (se 4 (by rfl) ⟨142821, by rfl⟩ : syracuseStep 1523429 = 285643) (by norm_num)
theorem B6602485 : Blo 674311 6602485 := bbase (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) (by norm_num)
theorem B2277125 : Blo 674311 2277125 := bbase (se 4 (by rfl) ⟨213480, by rfl⟩ : syracuseStep 2277125 = 426961) (by norm_num)
theorem B1523501 : Blo 674311 1523501 := bbase (se 3 (by rfl) ⟨285656, by rfl⟩ : syracuseStep 1523501 = 571313) (by norm_num)
theorem B1523573 : Blo 674311 1523573 := bbase (se 5 (by rfl) ⟨71417, by rfl⟩ : syracuseStep 1523573 = 142835) (by norm_num)
theorem B1097597 : Blo 674311 1097597 := bbase (se 3 (by rfl) ⟨205799, by rfl⟩ : syracuseStep 1097597 = 411599) (by norm_num)
theorem B1523645 : Blo 674311 1523645 := bbase (se 3 (by rfl) ⟨285683, by rfl⟩ : syracuseStep 1523645 = 571367) (by norm_num)
theorem B1523717 : Blo 674311 1523717 := bbase (se 4 (by rfl) ⟨142848, by rfl⟩ : syracuseStep 1523717 = 285697) (by norm_num)
theorem B3293237 : Blo 674311 3293237 := bbase (se 5 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 3293237 = 308741) (by norm_num)
theorem B1523789 : Blo 674311 1523789 := bbase (se 3 (by rfl) ⟨285710, by rfl⟩ : syracuseStep 1523789 = 571421) (by norm_num)
theorem B1523861 : Blo 674311 1523861 := bbase (se 6 (by rfl) ⟨35715, by rfl⟩ : syracuseStep 1523861 = 71431) (by norm_num)
theorem B2277557 : Blo 674311 2277557 := bbase (se 5 (by rfl) ⟨106760, by rfl⟩ : syracuseStep 2277557 = 213521) (by norm_num)
theorem B1523933 : Blo 674311 1523933 := bbase (se 3 (by rfl) ⟨285737, by rfl⟩ : syracuseStep 1523933 = 571475) (by norm_num)
theorem B3424517 : Blo 674311 3424517 := bbase (se 4 (by rfl) ⟨321048, by rfl⟩ : syracuseStep 3424517 = 642097) (by norm_num)
theorem B770329 : Blo 674311 770329 := bbase (se 2 (by rfl) ⟨288873, by rfl⟩ : syracuseStep 770329 = 577747) (by norm_num)
theorem B1524005 : Blo 674311 1524005 := bbase (se 4 (by rfl) ⟨142875, by rfl⟩ : syracuseStep 1524005 = 285751) (by norm_num)
theorem B868709 : Blo 674311 868709 := bbase (se 4 (by rfl) ⟨81441, by rfl⟩ : syracuseStep 868709 = 162883) (by norm_num)
theorem B1524077 : Blo 674311 1524077 := bbase (se 3 (by rfl) ⟨285764, by rfl⟩ : syracuseStep 1524077 = 571529) (by norm_num)
theorem B1524149 : Blo 674311 1524149 := bbase (se 5 (by rfl) ⟨71444, by rfl⟩ : syracuseStep 1524149 = 142889) (by norm_num)
theorem B1524221 : Blo 674311 1524221 := bbase (se 3 (by rfl) ⟨285791, by rfl⟩ : syracuseStep 1524221 = 571583) (by norm_num)
theorem B6242837 : Blo 674311 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B5128757 : Blo 674311 5128757 := bbase (se 5 (by rfl) ⟨240410, by rfl⟩ : syracuseStep 5128757 = 480821) (by norm_num)
theorem B1524293 : Blo 674311 1524293 := bbase (se 4 (by rfl) ⟨142902, by rfl⟩ : syracuseStep 1524293 = 285805) (by norm_num)
theorem B2277989 : Blo 674311 2277989 := bbase (se 4 (by rfl) ⟨213561, by rfl⟩ : syracuseStep 2277989 = 427123) (by norm_num)
theorem B1524365 : Blo 674311 1524365 := bbase (se 3 (by rfl) ⟨285818, by rfl⟩ : syracuseStep 1524365 = 571637) (by norm_num)
theorem B1524437 : Blo 674311 1524437 := bbase (se 7 (by rfl) ⟨17864, by rfl⟩ : syracuseStep 1524437 = 35729) (by norm_num)
theorem B1524509 : Blo 674311 1524509 := bbase (se 3 (by rfl) ⟨285845, by rfl⟩ : syracuseStep 1524509 = 571691) (by norm_num)
theorem B1098557 : Blo 674311 1098557 := bbase (se 3 (by rfl) ⟨205979, by rfl⟩ : syracuseStep 1098557 = 411959) (by norm_num)
theorem B1524581 : Blo 674311 1524581 := bbase (se 4 (by rfl) ⟨142929, by rfl⟩ : syracuseStep 1524581 = 285859) (by norm_num)
theorem B1524653 : Blo 674311 1524653 := bbase (se 3 (by rfl) ⟨285872, by rfl⟩ : syracuseStep 1524653 = 571745) (by norm_num)
theorem B1524725 : Blo 674311 1524725 := bbase (se 5 (by rfl) ⟨71471, by rfl⟩ : syracuseStep 1524725 = 142943) (by norm_num)
theorem B2278421 : Blo 674311 2278421 := bbase (se 6 (by rfl) ⟨53400, by rfl⟩ : syracuseStep 2278421 = 106801) (by norm_num)
theorem B1524797 : Blo 674311 1524797 := bbase (se 3 (by rfl) ⟨285899, by rfl⟩ : syracuseStep 1524797 = 571799) (by norm_num)
theorem B1524869 : Blo 674311 1524869 := bbase (se 4 (by rfl) ⟨142956, by rfl⟩ : syracuseStep 1524869 = 285913) (by norm_num)
theorem B2573477 : Blo 674311 2573477 := bbase (se 4 (by rfl) ⟨241263, by rfl⟩ : syracuseStep 2573477 = 482527) (by norm_num)
theorem B1524941 : Blo 674311 1524941 := bbase (se 3 (by rfl) ⟨285926, by rfl⟩ : syracuseStep 1524941 = 571853) (by norm_num)
theorem B1525013 : Blo 674311 1525013 := bbase (se 6 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 1525013 = 71485) (by norm_num)
theorem B1099045 : Blo 674311 1099045 := bbase (se 4 (by rfl) ⟨103035, by rfl⟩ : syracuseStep 1099045 = 206071) (by norm_num)
theorem B1525085 : Blo 674311 1525085 := bbase (se 3 (by rfl) ⟨285953, by rfl⟩ : syracuseStep 1525085 = 571907) (by norm_num)
theorem B1525157 : Blo 674311 1525157 := bbase (se 4 (by rfl) ⟨142983, by rfl⟩ : syracuseStep 1525157 = 285967) (by norm_num)
theorem B2278853 : Blo 674311 2278853 := bbase (se 4 (by rfl) ⟨213642, by rfl⟩ : syracuseStep 2278853 = 427285) (by norm_num)
theorem B2573765 : Blo 674311 2573765 := bbase (se 4 (by rfl) ⟨241290, by rfl⟩ : syracuseStep 2573765 = 482581) (by norm_num)
theorem B1525229 : Blo 674311 1525229 := bbase (se 3 (by rfl) ⟨285980, by rfl⟩ : syracuseStep 1525229 = 571961) (by norm_num)
theorem B3425813 : Blo 674311 3425813 := bbase (se 6 (by rfl) ⟨80292, by rfl⟩ : syracuseStep 3425813 = 160585) (by norm_num)
theorem B1525301 : Blo 674311 1525301 := bbase (se 5 (by rfl) ⟨71498, by rfl⟩ : syracuseStep 1525301 = 142997) (by norm_num)
theorem B1525373 : Blo 674311 1525373 := bbase (se 3 (by rfl) ⟨286007, by rfl⟩ : syracuseStep 1525373 = 572015) (by norm_num)
theorem B1525445 : Blo 674311 1525445 := bbase (se 4 (by rfl) ⟨143010, by rfl⟩ : syracuseStep 1525445 = 286021) (by norm_num)
theorem B1525517 : Blo 674311 1525517 := bbase (se 3 (by rfl) ⟨286034, by rfl⟩ : syracuseStep 1525517 = 572069) (by norm_num)
theorem B1525589 : Blo 674311 1525589 := bbase (se 9 (by rfl) ⟨4469, by rfl⟩ : syracuseStep 1525589 = 8939) (by norm_num)
theorem B2279285 : Blo 674311 2279285 := bbase (se 5 (by rfl) ⟨106841, by rfl⟩ : syracuseStep 2279285 = 213683) (by norm_num)
theorem B1623925 : Blo 674311 1623925 := bbase (se 5 (by rfl) ⟨76121, by rfl⟩ : syracuseStep 1623925 = 152243) (by norm_num)
theorem B1525661 : Blo 674311 1525661 := bbase (se 3 (by rfl) ⟨286061, by rfl⟩ : syracuseStep 1525661 = 572123) (by norm_num)
theorem B7325653 : Blo 674311 7325653 := bbase (se 7 (by rfl) ⟨85847, by rfl⟩ : syracuseStep 7325653 = 171695) (by norm_num)
theorem B1525733 : Blo 674311 1525733 := bbase (se 4 (by rfl) ⟨143037, by rfl⟩ : syracuseStep 1525733 = 286075) (by norm_num)
theorem B1525805 : Blo 674311 1525805 := bbase (se 3 (by rfl) ⟨286088, by rfl⟩ : syracuseStep 1525805 = 572177) (by norm_num)
theorem B1525877 : Blo 674311 1525877 := bbase (se 5 (by rfl) ⟨71525, by rfl⟩ : syracuseStep 1525877 = 143051) (by norm_num)
theorem B1099909 : Blo 674311 1099909 := bbase (se 4 (by rfl) ⟨103116, by rfl⟩ : syracuseStep 1099909 = 206233) (by norm_num)
theorem B1460405 : Blo 674311 1460405 := bbase (se 5 (by rfl) ⟨68456, by rfl⟩ : syracuseStep 1460405 = 136913) (by norm_num)
theorem B1525949 : Blo 674311 1525949 := bbase (se 3 (by rfl) ⟨286115, by rfl⟩ : syracuseStep 1525949 = 572231) (by norm_num)
theorem B1526021 : Blo 674311 1526021 := bbase (se 4 (by rfl) ⟨143064, by rfl⟩ : syracuseStep 1526021 = 286129) (by norm_num)
theorem B1624349 : Blo 674311 1624349 := bbase (se 3 (by rfl) ⟨304565, by rfl⟩ : syracuseStep 1624349 = 609131) (by norm_num)
theorem B2279717 : Blo 674311 2279717 := bbase (se 4 (by rfl) ⟨213723, by rfl⟩ : syracuseStep 2279717 = 427447) (by norm_num)
theorem B1526093 : Blo 674311 1526093 := bbase (se 3 (by rfl) ⟨286142, by rfl⟩ : syracuseStep 1526093 = 572285) (by norm_num)
theorem B3852629 : Blo 674311 3852629 := bbase (se 10 (by rfl) ⟨5643, by rfl⟩ : syracuseStep 3852629 = 11287) (by norm_num)
theorem B5196149 : Blo 674311 5196149 := bbase (se 5 (by rfl) ⟨243569, by rfl⟩ : syracuseStep 5196149 = 487139) (by norm_num)
theorem B1526165 : Blo 674311 1526165 := bbase (se 6 (by rfl) ⟨35769, by rfl⟩ : syracuseStep 1526165 = 71539) (by norm_num)
theorem B6244789 : Blo 674311 6244789 := bbase (se 5 (by rfl) ⟨292724, by rfl⟩ : syracuseStep 6244789 = 585449) (by norm_num)
theorem B1100245 : Blo 674311 1100245 := bbase (se 7 (by rfl) ⟨12893, by rfl⟩ : syracuseStep 1100245 = 25787) (by norm_num)
theorem B1624637 : Blo 674311 1624637 := bbase (se 3 (by rfl) ⟨304619, by rfl⟩ : syracuseStep 1624637 = 609239) (by norm_num)
theorem B2574949 : Blo 674311 2574949 := bbase (se 4 (by rfl) ⟨241401, by rfl⟩ : syracuseStep 2574949 = 482803) (by norm_num)
theorem B2280149 : Blo 674311 2280149 := bbase (se 7 (by rfl) ⟨26720, by rfl⟩ : syracuseStep 2280149 = 53441) (by norm_num)
theorem B3427109 : Blo 674311 3427109 := bbase (se 4 (by rfl) ⟨321291, by rfl⟩ : syracuseStep 3427109 = 642583) (by norm_num)
theorem B4868981 : Blo 674311 4868981 := bbase (se 5 (by rfl) ⟨228233, by rfl⟩ : syracuseStep 4868981 = 456467) (by norm_num)
theorem B2575253 : Blo 674311 2575253 := bbase (se 6 (by rfl) ⟨60357, by rfl⟩ : syracuseStep 2575253 = 120715) (by norm_num)
theorem B773029 : Blo 674311 773029 := bbase (se 4 (by rfl) ⟨72471, by rfl⟩ : syracuseStep 773029 = 144943) (by norm_num)
theorem B2739205 : Blo 674311 2739205 := bbase (se 4 (by rfl) ⟨256800, by rfl⟩ : syracuseStep 2739205 = 513601) (by norm_num)
theorem B3132533 : Blo 674311 3132533 := bbase (se 5 (by rfl) ⟨146837, by rfl⟩ : syracuseStep 3132533 = 293675) (by norm_num)
theorem B2280581 : Blo 674311 2280581 := bbase (se 4 (by rfl) ⟨213804, by rfl⟩ : syracuseStep 2280581 = 427609) (by norm_num)
theorem B773321 : Blo 674311 773321 := bbase (se 2 (by rfl) ⟨289995, by rfl⟩ : syracuseStep 773321 = 579991) (by norm_num)
theorem B1920277 : Blo 674311 1920277 := bbase (se 6 (by rfl) ⟨45006, by rfl⟩ : syracuseStep 1920277 = 90013) (by norm_num)
theorem B1461557 : Blo 674311 1461557 := bbase (se 5 (by rfl) ⟨68510, by rfl⟩ : syracuseStep 1461557 = 137021) (by norm_num)
theorem B1560053 : Blo 674311 1560053 := bbase (se 5 (by rfl) ⟨73127, by rfl⟩ : syracuseStep 1560053 = 146255) (by norm_num)
theorem B2281013 : Blo 674311 2281013 := bbase (se 5 (by rfl) ⟨106922, by rfl⟩ : syracuseStep 2281013 = 213845) (by norm_num)
theorem B1298053 : Blo 674311 1298053 := bbase (se 4 (by rfl) ⟨121692, by rfl⟩ : syracuseStep 1298053 = 243385) (by norm_num)
theorem B1756829 : Blo 674311 1756829 := bbase (se 3 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 1756829 = 658811) (by norm_num)
theorem B1953589 : Blo 674311 1953589 := bbase (se 5 (by rfl) ⟨91574, by rfl⟩ : syracuseStep 1953589 = 183149) (by norm_num)
theorem B1560421 : Blo 674311 1560421 := bbase (se 4 (by rfl) ⟨146289, by rfl⟩ : syracuseStep 1560421 = 292579) (by norm_num)
theorem B2281445 : Blo 674311 2281445 := bbase (se 4 (by rfl) ⟨213885, by rfl⟩ : syracuseStep 2281445 = 427771) (by norm_num)
theorem B8802325 : Blo 674311 8802325 := bbase (se 6 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 8802325 = 412609) (by norm_num)
theorem B3428405 : Blo 674311 3428405 := bbase (se 5 (by rfl) ⟨160706, by rfl⟩ : syracuseStep 3428405 = 321413) (by norm_num)
theorem B1822981 : Blo 674311 1822981 := bbase (se 4 (by rfl) ⟨170904, by rfl⟩ : syracuseStep 1822981 = 341809) (by norm_num)
theorem B2281877 : Blo 674311 2281877 := bbase (se 6 (by rfl) ⟨53481, by rfl⟩ : syracuseStep 2281877 = 106963) (by norm_num)
theorem B2314709 : Blo 674311 2314709 := bbase (se 7 (by rfl) ⟨27125, by rfl⟩ : syracuseStep 2314709 = 54251) (by norm_num)
theorem B1692269 : Blo 674311 1692269 := bbase (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) (by norm_num)
theorem B1921781 : Blo 674311 1921781 := bbase (se 5 (by rfl) ⟨90083, by rfl⟩ : syracuseStep 1921781 = 180167) (by norm_num)
theorem B2282309 : Blo 674311 2282309 := bbase (se 4 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 2282309 = 427933) (by norm_num)
theorem B5788853 : Blo 674311 5788853 := bbase (se 5 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 5788853 = 542705) (by norm_num)
theorem B2282741 : Blo 674311 2282741 := bbase (se 5 (by rfl) ⟨107003, by rfl⟩ : syracuseStep 2282741 = 214007) (by norm_num)
theorem B3429701 : Blo 674311 3429701 := bbase (se 4 (by rfl) ⟨321534, by rfl⟩ : syracuseStep 3429701 = 643069) (by norm_num)
theorem B1627789 : Blo 674311 1627789 := bbase (se 3 (by rfl) ⟨305210, by rfl⟩ : syracuseStep 1627789 = 610421) (by norm_num)
theorem B2283173 : Blo 674311 2283173 := bbase (se 4 (by rfl) ⟨214047, by rfl⟩ : syracuseStep 2283173 = 428095) (by norm_num)
theorem B1824581 : Blo 674311 1824581 := bbase (se 4 (by rfl) ⟨171054, by rfl⟩ : syracuseStep 1824581 = 342109) (by norm_num)
theorem B2283605 : Blo 674311 2283605 := bbase (se 8 (by rfl) ⟨13380, by rfl⟩ : syracuseStep 2283605 = 26761) (by norm_num)
theorem B2742437 : Blo 674311 2742437 := bbase (se 4 (by rfl) ⟨257103, by rfl⟩ : syracuseStep 2742437 = 514207) (by norm_num)
theorem B1923365 : Blo 674311 1923365 := bbase (se 4 (by rfl) ⟨180315, by rfl⟩ : syracuseStep 1923365 = 360631) (by norm_num)
theorem B1628461 : Blo 674311 1628461 := bbase (se 3 (by rfl) ⟨305336, by rfl⟩ : syracuseStep 1628461 = 610673) (by norm_num)
theorem B2284037 : Blo 674311 2284037 := bbase (se 4 (by rfl) ⟨214128, by rfl⟩ : syracuseStep 2284037 = 428257) (by norm_num)
theorem B1628693 : Blo 674311 1628693 := bbase (se 6 (by rfl) ⟨38172, by rfl⟩ : syracuseStep 1628693 = 76345) (by norm_num)
theorem B4872757 : Blo 674311 4872757 := bbase (se 5 (by rfl) ⟨228410, by rfl⟩ : syracuseStep 4872757 = 456821) (by norm_num)
theorem B3430997 : Blo 674311 3430997 := bbase (se 8 (by rfl) ⟨20103, by rfl⟩ : syracuseStep 3430997 = 40207) (by norm_num)
theorem B2775653 : Blo 674311 2775653 := bbase (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) (by norm_num)
theorem B1825445 : Blo 674311 1825445 := bbase (se 4 (by rfl) ⟨171135, by rfl⟩ : syracuseStep 1825445 = 342271) (by norm_num)
theorem B1628837 : Blo 674311 1628837 := bbase (se 4 (by rfl) ⟨152703, by rfl⟩ : syracuseStep 1628837 = 305407) (by norm_num)
theorem B1628885 : Blo 674311 1628885 := bbase (se 7 (by rfl) ⟨19088, by rfl⟩ : syracuseStep 1628885 = 38177) (by norm_num)
theorem B2284469 : Blo 674311 2284469 := bbase (se 5 (by rfl) ⟨107084, by rfl⟩ : syracuseStep 2284469 = 214169) (by norm_num)
theorem B1924037 : Blo 674311 1924037 := bbase (se 4 (by rfl) ⟨180378, by rfl⟩ : syracuseStep 1924037 = 360757) (by norm_num)
theorem B1629173 : Blo 674311 1629173 := bbase (se 5 (by rfl) ⟨76367, by rfl⟩ : syracuseStep 1629173 = 152735) (by norm_num)
theorem B1956917 : Blo 674311 1956917 := bbase (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) (by norm_num)
theorem B1137901 : Blo 674311 1137901 := bbase (se 3 (by rfl) ⟨213356, by rfl⟩ : syracuseStep 1137901 = 426713) (by norm_num)
theorem B810281 : Blo 674311 810281 := bbase (se 2 (by rfl) ⟨303855, by rfl⟩ : syracuseStep 810281 = 607711) (by norm_num)
theorem B1137989 : Blo 674311 1137989 := bbase (se 4 (by rfl) ⟨106686, by rfl⟩ : syracuseStep 1137989 = 213373) (by norm_num)
theorem B3661141 : Blo 674311 3661141 := bbase (se 11 (by rfl) ⟨2681, by rfl⟩ : syracuseStep 3661141 = 5363) (by norm_num)
theorem B810329 : Blo 674311 810329 := bbase (se 2 (by rfl) ⟨303873, by rfl⟩ : syracuseStep 810329 = 607747) (by norm_num)
theorem B2284901 : Blo 674311 2284901 := bbase (se 4 (by rfl) ⟨214209, by rfl⟩ : syracuseStep 2284901 = 428419) (by norm_num)
theorem B1924469 : Blo 674311 1924469 := bbase (se 5 (by rfl) ⟨90209, by rfl⟩ : syracuseStep 1924469 = 180419) (by norm_num)
theorem B1564085 : Blo 674311 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B810425 : Blo 674311 810425 := bbase (se 2 (by rfl) ⟨303909, by rfl⟩ : syracuseStep 810425 = 607819) (by norm_num)
theorem B1138117 : Blo 674311 1138117 := bbase (se 4 (by rfl) ⟨106698, by rfl⟩ : syracuseStep 1138117 = 213397) (by norm_num)
theorem B1138205 : Blo 674311 1138205 := bbase (se 3 (by rfl) ⟨213413, by rfl⟩ : syracuseStep 1138205 = 426827) (by norm_num)
theorem B2743877 : Blo 674311 2743877 := bbase (se 4 (by rfl) ⟨257238, by rfl⟩ : syracuseStep 2743877 = 514477) (by norm_num)
theorem B810589 : Blo 674311 810589 := bbase (se 3 (by rfl) ⟨151985, by rfl⟩ : syracuseStep 810589 = 303971) (by norm_num)
theorem B2252405 : Blo 674311 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B1138333 : Blo 674311 1138333 := bbase (se 3 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 1138333 = 426875) (by norm_num)
theorem B1138421 : Blo 674311 1138421 := bbase (se 5 (by rfl) ⟨53363, by rfl⟩ : syracuseStep 1138421 = 106727) (by norm_num)
theorem B2285333 : Blo 674311 2285333 := bbase (se 6 (by rfl) ⟨53562, by rfl⟩ : syracuseStep 2285333 = 107125) (by norm_num)
theorem B810805 : Blo 674311 810805 := bbase (se 5 (by rfl) ⟨38006, by rfl⟩ : syracuseStep 810805 = 76013) (by norm_num)
theorem B3432293 : Blo 674311 3432293 := bbase (se 4 (by rfl) ⟨321777, by rfl⟩ : syracuseStep 3432293 = 643555) (by norm_num)
theorem B1138549 : Blo 674311 1138549 := bbase (se 5 (by rfl) ⟨53369, by rfl⟩ : syracuseStep 1138549 = 106739) (by norm_num)
theorem B1138637 : Blo 674311 1138637 := bbase (se 3 (by rfl) ⟨213494, by rfl⟩ : syracuseStep 1138637 = 426989) (by norm_num)
theorem B810973 : Blo 674311 810973 := bbase (se 3 (by rfl) ⟨152057, by rfl⟩ : syracuseStep 810973 = 304115) (by norm_num)
theorem B1138765 : Blo 674311 1138765 := bbase (se 3 (by rfl) ⟨213518, by rfl⟩ : syracuseStep 1138765 = 427037) (by norm_num)
theorem B1925221 : Blo 674311 1925221 := bbase (se 4 (by rfl) ⟨180489, by rfl⟩ : syracuseStep 1925221 = 360979) (by norm_num)
theorem B5136533 : Blo 674311 5136533 := bbase (se 6 (by rfl) ⟨120387, by rfl⟩ : syracuseStep 5136533 = 240775) (by norm_num)
theorem B1138853 : Blo 674311 1138853 := bbase (se 4 (by rfl) ⟨106767, by rfl⟩ : syracuseStep 1138853 = 213535) (by norm_num)
theorem B2285765 : Blo 674311 2285765 := bbase (se 4 (by rfl) ⟨214290, by rfl⟩ : syracuseStep 2285765 = 428581) (by norm_num)
theorem B2318597 : Blo 674311 2318597 := bbase (se 4 (by rfl) ⟨217368, by rfl⟩ : syracuseStep 2318597 = 434737) (by norm_num)
theorem B1138981 : Blo 674311 1138981 := bbase (se 4 (by rfl) ⟨106779, by rfl⟩ : syracuseStep 1138981 = 213559) (by norm_num)
theorem B1139069 : Blo 674311 1139069 := bbase (se 3 (by rfl) ⟨213575, by rfl⟩ : syracuseStep 1139069 = 427151) (by norm_num)
theorem B811501 : Blo 674311 811501 := bbase (se 3 (by rfl) ⟨152156, by rfl⟩ : syracuseStep 811501 = 304313) (by norm_num)
theorem B1139197 : Blo 674311 1139197 := bbase (se 3 (by rfl) ⟨213599, by rfl⟩ : syracuseStep 1139197 = 427199) (by norm_num)
theorem B1139285 : Blo 674311 1139285 := bbase (se 8 (by rfl) ⟨6675, by rfl⟩ : syracuseStep 1139285 = 13351) (by norm_num)
theorem B2286197 : Blo 674311 2286197 := bbase (se 5 (by rfl) ⟨107165, by rfl⟩ : syracuseStep 2286197 = 214331) (by norm_num)
theorem B1139413 : Blo 674311 1139413 := bbase (se 7 (by rfl) ⟨13352, by rfl⟩ : syracuseStep 1139413 = 26705) (by norm_num)
theorem B1139501 : Blo 674311 1139501 := bbase (se 3 (by rfl) ⟨213656, by rfl⟩ : syracuseStep 1139501 = 427313) (by norm_num)
theorem B1139629 : Blo 674311 1139629 := bbase (se 3 (by rfl) ⟨213680, by rfl⟩ : syracuseStep 1139629 = 427361) (by norm_num)
theorem B1139717 : Blo 674311 1139717 := bbase (se 4 (by rfl) ⟨106848, by rfl⟩ : syracuseStep 1139717 = 213697) (by norm_num)
theorem B2286629 : Blo 674311 2286629 := bbase (se 4 (by rfl) ⟨214371, by rfl⟩ : syracuseStep 2286629 = 428743) (by norm_num)
theorem B2319445 : Blo 674311 2319445 := bbase (se 8 (by rfl) ⟨13590, by rfl⟩ : syracuseStep 2319445 = 27181) (by norm_num)
theorem B3433589 : Blo 674311 3433589 := bbase (se 5 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 3433589 = 321899) (by norm_num)
theorem B1139845 : Blo 674311 1139845 := bbase (se 4 (by rfl) ⟨106860, by rfl⟩ : syracuseStep 1139845 = 213721) (by norm_num)
theorem B1139933 : Blo 674311 1139933 := bbase (se 3 (by rfl) ⟨213737, by rfl⟩ : syracuseStep 1139933 = 427475) (by norm_num)
theorem B1172701 : Blo 674311 1172701 := bbase (se 3 (by rfl) ⟨219881, by rfl⟩ : syracuseStep 1172701 = 439763) (by norm_num)
theorem B1140061 : Blo 674311 1140061 := bbase (se 3 (by rfl) ⟨213761, by rfl⟩ : syracuseStep 1140061 = 427523) (by norm_num)
theorem B1140149 : Blo 674311 1140149 := bbase (se 5 (by rfl) ⟨53444, by rfl⟩ : syracuseStep 1140149 = 106889) (by norm_num)
theorem B2287061 : Blo 674311 2287061 := bbase (se 7 (by rfl) ⟨26801, by rfl⟩ : syracuseStep 2287061 = 53603) (by norm_num)
theorem B8644117 : Blo 674311 8644117 := bbase (se 6 (by rfl) ⟨202596, by rfl⟩ : syracuseStep 8644117 = 405193) (by norm_num)
theorem B1140277 : Blo 674311 1140277 := bbase (se 5 (by rfl) ⟨53450, by rfl⟩ : syracuseStep 1140277 = 106901) (by norm_num)
theorem B812597 : Blo 674311 812597 := bbase (se 5 (by rfl) ⟨38090, by rfl⟩ : syracuseStep 812597 = 76181) (by norm_num)
theorem B1140365 : Blo 674311 1140365 := bbase (se 3 (by rfl) ⟨213818, by rfl⟩ : syracuseStep 1140365 = 427637) (by norm_num)
theorem B1140493 : Blo 674311 1140493 := bbase (se 3 (by rfl) ⟨213842, by rfl⟩ : syracuseStep 1140493 = 427685) (by norm_num)
theorem B1304365 : Blo 674311 1304365 := bbase (se 3 (by rfl) ⟨244568, by rfl⟩ : syracuseStep 1304365 = 489137) (by norm_num)
theorem B1140581 : Blo 674311 1140581 := bbase (se 4 (by rfl) ⟨106929, by rfl⟩ : syracuseStep 1140581 = 213859) (by norm_num)
theorem B2287493 : Blo 674311 2287493 := bbase (se 4 (by rfl) ⟨214452, by rfl⟩ : syracuseStep 2287493 = 428905) (by norm_num)
theorem B1140709 : Blo 674311 1140709 := bbase (se 4 (by rfl) ⟨106941, by rfl⟩ : syracuseStep 1140709 = 213883) (by norm_num)
theorem B1140797 : Blo 674311 1140797 := bbase (se 3 (by rfl) ⟨213899, by rfl⟩ : syracuseStep 1140797 = 427799) (by norm_num)
theorem B1730717 : Blo 674311 1730717 := bbase (se 3 (by rfl) ⟨324509, by rfl⟩ : syracuseStep 1730717 = 649019) (by norm_num)
theorem B1140925 : Blo 674311 1140925 := bbase (se 3 (by rfl) ⟨213923, by rfl⟩ : syracuseStep 1140925 = 427847) (by norm_num)
theorem B3860693 : Blo 674311 3860693 := bbase (se 7 (by rfl) ⟨45242, by rfl⟩ : syracuseStep 3860693 = 90485) (by norm_num)
theorem B813289 : Blo 674311 813289 := bbase (se 2 (by rfl) ⟨304983, by rfl⟩ : syracuseStep 813289 = 609967) (by norm_num)
theorem B1141013 : Blo 674311 1141013 := bbase (se 6 (by rfl) ⟨26742, by rfl⟩ : syracuseStep 1141013 = 53485) (by norm_num)
theorem B2287925 : Blo 674311 2287925 := bbase (se 5 (by rfl) ⟨107246, by rfl⟩ : syracuseStep 2287925 = 214493) (by norm_num)
theorem B813385 : Blo 674311 813385 := bbase (se 2 (by rfl) ⟨305019, by rfl⟩ : syracuseStep 813385 = 610039) (by norm_num)
theorem B4811093 : Blo 674311 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B1730965 : Blo 674311 1730965 := bbase (se 6 (by rfl) ⟨40569, by rfl⟩ : syracuseStep 1730965 = 81139) (by norm_num)
theorem B1141141 : Blo 674311 1141141 := bbase (se 6 (by rfl) ⟨26745, by rfl⟩ : syracuseStep 1141141 = 53491) (by norm_num)
theorem B911837 : Blo 674311 911837 := bbase (se 3 (by rfl) ⟨170969, by rfl⟩ : syracuseStep 911837 = 341939) (by norm_num)
theorem B1141229 : Blo 674311 1141229 := bbase (se 3 (by rfl) ⟨213980, by rfl⟩ : syracuseStep 1141229 = 427961) (by norm_num)
theorem B6941173 : Blo 674311 6941173 := bbase (se 5 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 6941173 = 650735) (by norm_num)
theorem B1141357 : Blo 674311 1141357 := bbase (se 3 (by rfl) ⟨214004, by rfl⟩ : syracuseStep 1141357 = 428009) (by norm_num)
theorem B6941333 : Blo 674311 6941333 := bbase (se 6 (by rfl) ⟨162687, by rfl⟩ : syracuseStep 6941333 = 325375) (by norm_num)
theorem B1141445 : Blo 674311 1141445 := bbase (se 4 (by rfl) ⟨107010, by rfl⟩ : syracuseStep 1141445 = 214021) (by norm_num)
theorem B813769 : Blo 674311 813769 := bbase (se 2 (by rfl) ⟨305163, by rfl⟩ : syracuseStep 813769 = 610327) (by norm_num)
theorem B2288357 : Blo 674311 2288357 := bbase (se 4 (by rfl) ⟨214533, by rfl⟩ : syracuseStep 2288357 = 429067) (by norm_num)
theorem B1567525 : Blo 674311 1567525 := bbase (se 4 (by rfl) ⟨146955, by rfl⟩ : syracuseStep 1567525 = 293911) (by norm_num)
theorem B1141573 : Blo 674311 1141573 := bbase (se 4 (by rfl) ⟨107022, by rfl⟩ : syracuseStep 1141573 = 214045) (by norm_num)
theorem B1928069 : Blo 674311 1928069 := bbase (se 4 (by rfl) ⟨180756, by rfl⟩ : syracuseStep 1928069 = 361513) (by norm_num)
theorem B1141661 : Blo 674311 1141661 := bbase (se 3 (by rfl) ⟨214061, by rfl⟩ : syracuseStep 1141661 = 428123) (by norm_num)
theorem B2747317 : Blo 674311 2747317 := bbase (se 5 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 2747317 = 257561) (by norm_num)
theorem B1141789 : Blo 674311 1141789 := bbase (se 3 (by rfl) ⟨214085, by rfl⟩ : syracuseStep 1141789 = 428171) (by norm_num)
theorem B1141877 : Blo 674311 1141877 := bbase (se 5 (by rfl) ⟨53525, by rfl⟩ : syracuseStep 1141877 = 107051) (by norm_num)
theorem B2288789 : Blo 674311 2288789 := bbase (se 6 (by rfl) ⟨53643, by rfl⟩ : syracuseStep 2288789 = 107287) (by norm_num)
theorem B1830053 : Blo 674311 1830053 := bbase (se 4 (by rfl) ⟨171567, by rfl⟩ : syracuseStep 1830053 = 343135) (by norm_num)
theorem B1142005 : Blo 674311 1142005 := bbase (se 5 (by rfl) ⟨53531, by rfl⟩ : syracuseStep 1142005 = 107063) (by norm_num)
theorem B1142093 : Blo 674311 1142093 := bbase (se 3 (by rfl) ⟨214142, by rfl⟩ : syracuseStep 1142093 = 428285) (by norm_num)
theorem B1371485 : Blo 674311 1371485 := bbase (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) (by norm_num)
theorem B3861877 : Blo 674311 3861877 := bbase (se 5 (by rfl) ⟨181025, by rfl⟩ : syracuseStep 3861877 = 362051) (by norm_num)
theorem B1142221 : Blo 674311 1142221 := bbase (se 3 (by rfl) ⟨214166, by rfl⟩ : syracuseStep 1142221 = 428333) (by norm_num)
theorem B1142309 : Blo 674311 1142309 := bbase (se 4 (by rfl) ⟨107091, by rfl⟩ : syracuseStep 1142309 = 214183) (by norm_num)
theorem B2289221 : Blo 674311 2289221 := bbase (se 4 (by rfl) ⟨214614, by rfl⟩ : syracuseStep 2289221 = 429229) (by norm_num)
theorem B1830485 : Blo 674311 1830485 := bbase (se 8 (by rfl) ⟨10725, by rfl⟩ : syracuseStep 1830485 = 21451) (by norm_num)
theorem B781949 : Blo 674311 781949 := bbase (se 3 (by rfl) ⟨146615, by rfl⟩ : syracuseStep 781949 = 293231) (by norm_num)
theorem B1142437 : Blo 674311 1142437 := bbase (se 4 (by rfl) ⟨107103, by rfl⟩ : syracuseStep 1142437 = 214207) (by norm_num)
theorem B814817 : Blo 674311 814817 := bbase (se 2 (by rfl) ⟨305556, by rfl⟩ : syracuseStep 814817 = 611113) (by norm_num)
theorem B1142525 : Blo 674311 1142525 := bbase (se 3 (by rfl) ⟨214223, by rfl⟩ : syracuseStep 1142525 = 428447) (by norm_num)
theorem B1011485 : Blo 674311 1011485 := bbase (se 3 (by rfl) ⟨189653, by rfl⟩ : syracuseStep 1011485 = 379307) (by norm_num)
theorem B1011509 : Blo 674311 1011509 := bbase (se 5 (by rfl) ⟨47414, by rfl⟩ : syracuseStep 1011509 = 94829) (by norm_num)
theorem B1011533 : Blo 674311 1011533 := bbase (se 3 (by rfl) ⟨189662, by rfl⟩ : syracuseStep 1011533 = 379325) (by norm_num)
theorem B1011557 : Blo 674311 1011557 := bbase (se 4 (by rfl) ⟨94833, by rfl⟩ : syracuseStep 1011557 = 189667) (by norm_num)
theorem B1011581 : Blo 674311 1011581 := bbase (se 3 (by rfl) ⟨189671, by rfl⟩ : syracuseStep 1011581 = 379343) (by norm_num)
theorem B1142653 : Blo 674311 1142653 := bbase (se 3 (by rfl) ⟨214247, by rfl⟩ : syracuseStep 1142653 = 428495) (by norm_num)
theorem B913285 : Blo 674311 913285 := bbase (se 4 (by rfl) ⟨85620, by rfl⟩ : syracuseStep 913285 = 171241) (by norm_num)
theorem B1011605 : Blo 674311 1011605 := bbase (se 6 (by rfl) ⟨23709, by rfl⟩ : syracuseStep 1011605 = 47419) (by norm_num)
theorem B1011629 : Blo 674311 1011629 := bbase (se 3 (by rfl) ⟨189680, by rfl⟩ : syracuseStep 1011629 = 379361) (by norm_num)
theorem B1011653 : Blo 674311 1011653 := bbase (se 4 (by rfl) ⟨94842, by rfl⟩ : syracuseStep 1011653 = 189685) (by norm_num)
theorem B1830853 : Blo 674311 1830853 := bbase (se 4 (by rfl) ⟨171642, by rfl⟩ : syracuseStep 1830853 = 343285) (by norm_num)
theorem B1142741 : Blo 674311 1142741 := bbase (se 7 (by rfl) ⟨13391, by rfl⟩ : syracuseStep 1142741 = 26783) (by norm_num)
theorem B1011677 : Blo 674311 1011677 := bbase (se 3 (by rfl) ⟨189689, by rfl⟩ : syracuseStep 1011677 = 379379) (by norm_num)
theorem B1011701 : Blo 674311 1011701 := bbase (se 5 (by rfl) ⟨47423, by rfl⟩ : syracuseStep 1011701 = 94847) (by norm_num)
theorem B1011725 : Blo 674311 1011725 := bbase (se 3 (by rfl) ⟨189698, by rfl⟩ : syracuseStep 1011725 = 379397) (by norm_num)
theorem B1011749 : Blo 674311 1011749 := bbase (se 4 (by rfl) ⟨94851, by rfl⟩ : syracuseStep 1011749 = 189703) (by norm_num)
theorem B1929253 : Blo 674311 1929253 := bbase (se 4 (by rfl) ⟨180867, by rfl⟩ : syracuseStep 1929253 = 361735) (by norm_num)
theorem B1011773 : Blo 674311 1011773 := bbase (se 3 (by rfl) ⟨189707, by rfl⟩ : syracuseStep 1011773 = 379415) (by norm_num)
theorem B1011797 : Blo 674311 1011797 := bbase (se 8 (by rfl) ⟨5928, by rfl⟩ : syracuseStep 1011797 = 11857) (by norm_num)
theorem B1142869 : Blo 674311 1142869 := bbase (se 8 (by rfl) ⟨6696, by rfl⟩ : syracuseStep 1142869 = 13393) (by norm_num)
theorem B684137 : Blo 674311 684137 := bbase (se 2 (by rfl) ⟨256551, by rfl⟩ : syracuseStep 684137 = 513103) (by norm_num)
theorem B1011821 : Blo 674311 1011821 := bbase (se 3 (by rfl) ⟨189716, by rfl⟩ : syracuseStep 1011821 = 379433) (by norm_num)
theorem B1011845 : Blo 674311 1011845 := bbase (se 4 (by rfl) ⟨94860, by rfl⟩ : syracuseStep 1011845 = 189721) (by norm_num)
theorem B1011869 : Blo 674311 1011869 := bbase (se 3 (by rfl) ⟨189725, by rfl⟩ : syracuseStep 1011869 = 379451) (by norm_num)
theorem B1142957 : Blo 674311 1142957 := bbase (se 3 (by rfl) ⟨214304, by rfl⟩ : syracuseStep 1142957 = 428609) (by norm_num)
theorem B1011893 : Blo 674311 1011893 := bbase (se 5 (by rfl) ⟨47432, by rfl⟩ : syracuseStep 1011893 = 94865) (by norm_num)
theorem B1929413 : Blo 674311 1929413 := bbase (se 4 (by rfl) ⟨180882, by rfl⟩ : syracuseStep 1929413 = 361765) (by norm_num)
theorem B1011917 : Blo 674311 1011917 := bbase (se 3 (by rfl) ⟨189734, by rfl⟩ : syracuseStep 1011917 = 379469) (by norm_num)
theorem B1011941 : Blo 674311 1011941 := bbase (se 4 (by rfl) ⟨94869, by rfl⟩ : syracuseStep 1011941 = 189739) (by norm_num)
theorem B1011965 : Blo 674311 1011965 := bbase (se 3 (by rfl) ⟨189743, by rfl⟩ : syracuseStep 1011965 = 379487) (by norm_num)
theorem B1011989 : Blo 674311 1011989 := bbase (se 6 (by rfl) ⟨23718, by rfl⟩ : syracuseStep 1011989 = 47437) (by norm_num)
theorem B1012013 : Blo 674311 1012013 := bbase (se 3 (by rfl) ⟨189752, by rfl⟩ : syracuseStep 1012013 = 379505) (by norm_num)
theorem B1143085 : Blo 674311 1143085 := bbase (se 3 (by rfl) ⟨214328, by rfl⟩ : syracuseStep 1143085 = 428657) (by norm_num)
theorem B1012037 : Blo 674311 1012037 := bbase (se 4 (by rfl) ⟨94878, by rfl⟩ : syracuseStep 1012037 = 189757) (by norm_num)
theorem B1012061 : Blo 674311 1012061 := bbase (se 3 (by rfl) ⟨189761, by rfl⟩ : syracuseStep 1012061 = 379523) (by norm_num)
theorem B1012085 : Blo 674311 1012085 := bbase (se 5 (by rfl) ⟨47441, by rfl⟩ : syracuseStep 1012085 = 94883) (by norm_num)
theorem B1143173 : Blo 674311 1143173 := bbase (se 4 (by rfl) ⟨107172, by rfl⟩ : syracuseStep 1143173 = 214345) (by norm_num)
theorem B1012109 : Blo 674311 1012109 := bbase (se 3 (by rfl) ⟨189770, by rfl⟩ : syracuseStep 1012109 = 379541) (by norm_num)
theorem B3076501 : Blo 674311 3076501 := bbase (se 6 (by rfl) ⟨72105, by rfl⟩ : syracuseStep 3076501 = 144211) (by norm_num)
theorem B684445 : Blo 674311 684445 := bbase (se 3 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 684445 = 256667) (by norm_num)
theorem B1012133 : Blo 674311 1012133 := bbase (se 4 (by rfl) ⟨94887, by rfl⟩ : syracuseStep 1012133 = 189775) (by norm_num)
theorem B1929653 : Blo 674311 1929653 := bbase (se 5 (by rfl) ⟨90452, by rfl⟩ : syracuseStep 1929653 = 180905) (by norm_num)
theorem B1012157 : Blo 674311 1012157 := bbase (se 3 (by rfl) ⟨189779, by rfl⟩ : syracuseStep 1012157 = 379559) (by norm_num)
theorem B1012181 : Blo 674311 1012181 := bbase (se 7 (by rfl) ⟨11861, by rfl⟩ : syracuseStep 1012181 = 23723) (by norm_num)
theorem B1012205 : Blo 674311 1012205 := bbase (se 3 (by rfl) ⟨189788, by rfl⟩ : syracuseStep 1012205 = 379577) (by norm_num)
theorem B1012229 : Blo 674311 1012229 := bbase (se 4 (by rfl) ⟨94896, by rfl⟩ : syracuseStep 1012229 = 189793) (by norm_num)
theorem B1143301 : Blo 674311 1143301 := bbase (se 4 (by rfl) ⟨107184, by rfl⟩ : syracuseStep 1143301 = 214369) (by norm_num)
theorem B1012253 : Blo 674311 1012253 := bbase (se 3 (by rfl) ⟨189797, by rfl⟩ : syracuseStep 1012253 = 379595) (by norm_num)
theorem B1372717 : Blo 674311 1372717 := bbase (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) (by norm_num)
theorem B1012277 : Blo 674311 1012277 := bbase (se 5 (by rfl) ⟨47450, by rfl⟩ : syracuseStep 1012277 = 94901) (by norm_num)
theorem B1012301 : Blo 674311 1012301 := bbase (se 3 (by rfl) ⟨189806, by rfl⟩ : syracuseStep 1012301 = 379613) (by norm_num)
theorem B1143389 : Blo 674311 1143389 := bbase (se 3 (by rfl) ⟨214385, by rfl⟩ : syracuseStep 1143389 = 428771) (by norm_num)
theorem B1012325 : Blo 674311 1012325 := bbase (se 4 (by rfl) ⟨94905, by rfl⟩ : syracuseStep 1012325 = 189811) (by norm_num)
theorem B1929845 : Blo 674311 1929845 := bbase (se 5 (by rfl) ⟨90461, by rfl⟩ : syracuseStep 1929845 = 180923) (by norm_num)
theorem B1012349 : Blo 674311 1012349 := bbase (se 3 (by rfl) ⟨189815, by rfl⟩ : syracuseStep 1012349 = 379631) (by norm_num)
theorem B1012373 : Blo 674311 1012373 := bbase (se 6 (by rfl) ⟨23727, by rfl⟩ : syracuseStep 1012373 = 47455) (by norm_num)
theorem B1012397 : Blo 674311 1012397 := bbase (se 3 (by rfl) ⟨189824, by rfl⟩ : syracuseStep 1012397 = 379649) (by norm_num)
theorem B1012421 : Blo 674311 1012421 := bbase (se 4 (by rfl) ⟨94914, by rfl⟩ : syracuseStep 1012421 = 189829) (by norm_num)
theorem B1012445 : Blo 674311 1012445 := bbase (se 3 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 1012445 = 379667) (by norm_num)
theorem B1143517 : Blo 674311 1143517 := bbase (se 3 (by rfl) ⟨214409, by rfl⟩ : syracuseStep 1143517 = 428819) (by norm_num)
theorem B1012469 : Blo 674311 1012469 := bbase (se 5 (by rfl) ⟨47459, by rfl⟩ : syracuseStep 1012469 = 94919) (by norm_num)
theorem B1012493 : Blo 674311 1012493 := bbase (se 3 (by rfl) ⟨189842, by rfl⟩ : syracuseStep 1012493 = 379685) (by norm_num)
theorem B1012517 : Blo 674311 1012517 := bbase (se 4 (by rfl) ⟨94923, by rfl⟩ : syracuseStep 1012517 = 189847) (by norm_num)
theorem B5206837 : Blo 674311 5206837 := bbase (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) (by norm_num)
theorem B1143605 : Blo 674311 1143605 := bbase (se 5 (by rfl) ⟨53606, by rfl⟩ : syracuseStep 1143605 = 107213) (by norm_num)
theorem B1012541 : Blo 674311 1012541 := bbase (se 3 (by rfl) ⟨189851, by rfl⟩ : syracuseStep 1012541 = 379703) (by norm_num)
theorem B1012565 : Blo 674311 1012565 := bbase (se 9 (by rfl) ⟨2966, by rfl⟩ : syracuseStep 1012565 = 5933) (by norm_num)
theorem B1012589 : Blo 674311 1012589 := bbase (se 3 (by rfl) ⟨189860, by rfl⟩ : syracuseStep 1012589 = 379721) (by norm_num)
theorem B1012613 : Blo 674311 1012613 := bbase (se 4 (by rfl) ⟨94932, by rfl⟩ : syracuseStep 1012613 = 189865) (by norm_num)
theorem B1012637 : Blo 674311 1012637 := bbase (se 3 (by rfl) ⟨189869, by rfl⟩ : syracuseStep 1012637 = 379739) (by norm_num)
theorem B684973 : Blo 674311 684973 := bbase (se 3 (by rfl) ⟨128432, by rfl⟩ : syracuseStep 684973 = 256865) (by norm_num)
theorem B1012661 : Blo 674311 1012661 := bbase (se 5 (by rfl) ⟨47468, by rfl⟩ : syracuseStep 1012661 = 94937) (by norm_num)
theorem B1143733 : Blo 674311 1143733 := bbase (se 5 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 1143733 = 107225) (by norm_num)
theorem B1012685 : Blo 674311 1012685 := bbase (se 3 (by rfl) ⟨189878, by rfl⟩ : syracuseStep 1012685 = 379757) (by norm_num)
theorem B2880485 : Blo 674311 2880485 := bbase (se 4 (by rfl) ⟨270045, by rfl⟩ : syracuseStep 2880485 = 540091) (by norm_num)
theorem B1012709 : Blo 674311 1012709 := bbase (se 4 (by rfl) ⟨94941, by rfl⟩ : syracuseStep 1012709 = 189883) (by norm_num)
theorem B1012733 : Blo 674311 1012733 := bbase (se 3 (by rfl) ⟨189887, by rfl⟩ : syracuseStep 1012733 = 379775) (by norm_num)
theorem B1143821 : Blo 674311 1143821 := bbase (se 3 (by rfl) ⟨214466, by rfl⟩ : syracuseStep 1143821 = 428933) (by norm_num)
theorem B1012757 : Blo 674311 1012757 := bbase (se 6 (by rfl) ⟨23736, by rfl⟩ : syracuseStep 1012757 = 47473) (by norm_num)
theorem B1012781 : Blo 674311 1012781 := bbase (se 3 (by rfl) ⟨189896, by rfl⟩ : syracuseStep 1012781 = 379793) (by norm_num)
theorem B1012805 : Blo 674311 1012805 := bbase (se 4 (by rfl) ⟨94950, by rfl⟩ : syracuseStep 1012805 = 189901) (by norm_num)
theorem B1012829 : Blo 674311 1012829 := bbase (se 3 (by rfl) ⟨189905, by rfl⟩ : syracuseStep 1012829 = 379811) (by norm_num)
theorem B1012853 : Blo 674311 1012853 := bbase (se 5 (by rfl) ⟨47477, by rfl⟩ : syracuseStep 1012853 = 94955) (by norm_num)
theorem B1012877 : Blo 674311 1012877 := bbase (se 3 (by rfl) ⟨189914, by rfl⟩ : syracuseStep 1012877 = 379829) (by norm_num)
theorem B1143949 : Blo 674311 1143949 := bbase (se 3 (by rfl) ⟨214490, by rfl⟩ : syracuseStep 1143949 = 428981) (by norm_num)
theorem B1012901 : Blo 674311 1012901 := bbase (se 4 (by rfl) ⟨94959, by rfl⟩ : syracuseStep 1012901 = 189919) (by norm_num)
theorem B1012925 : Blo 674311 1012925 := bbase (se 3 (by rfl) ⟨189923, by rfl⟩ : syracuseStep 1012925 = 379847) (by norm_num)
theorem B1012949 : Blo 674311 1012949 := bbase (se 7 (by rfl) ⟨11870, by rfl⟩ : syracuseStep 1012949 = 23741) (by norm_num)
theorem B1144037 : Blo 674311 1144037 := bbase (se 4 (by rfl) ⟨107253, by rfl⟩ : syracuseStep 1144037 = 214507) (by norm_num)
theorem B1012973 : Blo 674311 1012973 := bbase (se 3 (by rfl) ⟨189932, by rfl⟩ : syracuseStep 1012973 = 379865) (by norm_num)
theorem B1012997 : Blo 674311 1012997 := bbase (se 4 (by rfl) ⟨94968, by rfl⟩ : syracuseStep 1012997 = 189937) (by norm_num)
theorem B3241237 : Blo 674311 3241237 := bbase (se 6 (by rfl) ⟨75966, by rfl⟩ : syracuseStep 3241237 = 151933) (by norm_num)
theorem B1013021 : Blo 674311 1013021 := bbase (se 3 (by rfl) ⟨189941, by rfl⟩ : syracuseStep 1013021 = 379883) (by norm_num)
theorem B3470629 : Blo 674311 3470629 := bbase (se 4 (by rfl) ⟨325371, by rfl⟩ : syracuseStep 3470629 = 650743) (by norm_num)
theorem B1013045 : Blo 674311 1013045 := bbase (se 5 (by rfl) ⟨47486, by rfl⟩ : syracuseStep 1013045 = 94973) (by norm_num)
theorem B5862709 : Blo 674311 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B1013069 : Blo 674311 1013069 := bbase (se 3 (by rfl) ⟨189950, by rfl⟩ : syracuseStep 1013069 = 379901) (by norm_num)
theorem B1013093 : Blo 674311 1013093 := bbase (se 4 (by rfl) ⟨94977, by rfl⟩ : syracuseStep 1013093 = 189955) (by norm_num)
theorem B1144165 : Blo 674311 1144165 := bbase (se 4 (by rfl) ⟨107265, by rfl⟩ : syracuseStep 1144165 = 214531) (by norm_num)
theorem B1013117 : Blo 674311 1013117 := bbase (se 3 (by rfl) ⟨189959, by rfl⟩ : syracuseStep 1013117 = 379919) (by norm_num)
theorem B1013141 : Blo 674311 1013141 := bbase (se 6 (by rfl) ⟨23745, by rfl⟩ : syracuseStep 1013141 = 47491) (by norm_num)
theorem B1832357 : Blo 674311 1832357 := bbase (se 4 (by rfl) ⟨171783, by rfl⟩ : syracuseStep 1832357 = 343567) (by norm_num)
theorem B1013165 : Blo 674311 1013165 := bbase (se 3 (by rfl) ⟨189968, by rfl⟩ : syracuseStep 1013165 = 379937) (by norm_num)
theorem B1734061 : Blo 674311 1734061 := bbase (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) (by norm_num)
theorem B1144253 : Blo 674311 1144253 := bbase (se 3 (by rfl) ⟨214547, by rfl⟩ : syracuseStep 1144253 = 429095) (by norm_num)
theorem B1013189 : Blo 674311 1013189 := bbase (se 4 (by rfl) ⟨94986, by rfl⟩ : syracuseStep 1013189 = 189973) (by norm_num)
theorem B1013213 : Blo 674311 1013213 := bbase (se 3 (by rfl) ⟨189977, by rfl⟩ : syracuseStep 1013213 = 379955) (by norm_num)
theorem B1013237 : Blo 674311 1013237 := bbase (se 5 (by rfl) ⟨47495, by rfl⟩ : syracuseStep 1013237 = 94991) (by norm_num)
theorem B1832453 : Blo 674311 1832453 := bbase (se 4 (by rfl) ⟨171792, by rfl⟩ : syracuseStep 1832453 = 343585) (by norm_num)
theorem B1013261 : Blo 674311 1013261 := bbase (se 3 (by rfl) ⟨189986, by rfl⟩ : syracuseStep 1013261 = 379973) (by norm_num)
theorem B1013285 : Blo 674311 1013285 := bbase (se 4 (by rfl) ⟨94995, by rfl⟩ : syracuseStep 1013285 = 189991) (by norm_num)
theorem B1013309 : Blo 674311 1013309 := bbase (se 3 (by rfl) ⟨189995, by rfl⟩ : syracuseStep 1013309 = 379991) (by norm_num)
theorem B1144381 : Blo 674311 1144381 := bbase (se 3 (by rfl) ⟨214571, by rfl⟩ : syracuseStep 1144381 = 429143) (by norm_num)
theorem B1013333 : Blo 674311 1013333 := bbase (se 8 (by rfl) ⟨5937, by rfl⟩ : syracuseStep 1013333 = 11875) (by norm_num)
theorem B1930837 : Blo 674311 1930837 := bbase (se 8 (by rfl) ⟨11313, by rfl⟩ : syracuseStep 1930837 = 22627) (by norm_num)
theorem B1013357 : Blo 674311 1013357 := bbase (se 3 (by rfl) ⟨190004, by rfl⟩ : syracuseStep 1013357 = 380009) (by norm_num)
theorem B1013381 : Blo 674311 1013381 := bbase (se 4 (by rfl) ⟨95004, by rfl⟩ : syracuseStep 1013381 = 190009) (by norm_num)
theorem B1144469 : Blo 674311 1144469 := bbase (se 6 (by rfl) ⟨26823, by rfl⟩ : syracuseStep 1144469 = 53647) (by norm_num)
theorem B1013405 : Blo 674311 1013405 := bbase (se 3 (by rfl) ⟨190013, by rfl⟩ : syracuseStep 1013405 = 380027) (by norm_num)
theorem B1013429 : Blo 674311 1013429 := bbase (se 5 (by rfl) ⟨47504, by rfl⟩ : syracuseStep 1013429 = 95009) (by norm_num)
theorem B1013453 : Blo 674311 1013453 := bbase (se 3 (by rfl) ⟨190022, by rfl⟩ : syracuseStep 1013453 = 380045) (by norm_num)
theorem B1013477 : Blo 674311 1013477 := bbase (se 4 (by rfl) ⟨95013, by rfl⟩ : syracuseStep 1013477 = 190027) (by norm_num)
theorem B1013501 : Blo 674311 1013501 := bbase (se 3 (by rfl) ⟨190031, by rfl⟩ : syracuseStep 1013501 = 380063) (by norm_num)
theorem B1013525 : Blo 674311 1013525 := bbase (se 6 (by rfl) ⟨23754, by rfl⟩ : syracuseStep 1013525 = 47509) (by norm_num)
theorem B1144597 : Blo 674311 1144597 := bbase (se 6 (by rfl) ⟨26826, by rfl⟩ : syracuseStep 1144597 = 53653) (by norm_num)
theorem B1013549 : Blo 674311 1013549 := bbase (se 3 (by rfl) ⟨190040, by rfl⟩ : syracuseStep 1013549 = 380081) (by norm_num)
theorem B1013573 : Blo 674311 1013573 := bbase (se 4 (by rfl) ⟨95022, by rfl⟩ : syracuseStep 1013573 = 190045) (by norm_num)
theorem B685913 : Blo 674311 685913 := bbase (se 2 (by rfl) ⟨257217, by rfl⟩ : syracuseStep 685913 = 514435) (by norm_num)
theorem B1013597 : Blo 674311 1013597 := bbase (se 3 (by rfl) ⟨190049, by rfl⟩ : syracuseStep 1013597 = 380099) (by norm_num)
theorem B1013621 : Blo 674311 1013621 := bbase (se 5 (by rfl) ⟨47513, by rfl⟩ : syracuseStep 1013621 = 95027) (by norm_num)
theorem B685945 : Blo 674311 685945 := bbase (se 2 (by rfl) ⟨257229, by rfl⟩ : syracuseStep 685945 = 514459) (by norm_num)
theorem B1013645 : Blo 674311 1013645 := bbase (se 3 (by rfl) ⟨190058, by rfl⟩ : syracuseStep 1013645 = 380117) (by norm_num)
theorem B1013669 : Blo 674311 1013669 := bbase (se 4 (by rfl) ⟨95031, by rfl⟩ : syracuseStep 1013669 = 190063) (by norm_num)
theorem B1013693 : Blo 674311 1013693 := bbase (se 3 (by rfl) ⟨190067, by rfl⟩ : syracuseStep 1013693 = 380135) (by norm_num)
theorem B1013717 : Blo 674311 1013717 := bbase (se 7 (by rfl) ⟨11879, by rfl⟩ : syracuseStep 1013717 = 23759) (by norm_num)
theorem B1013741 : Blo 674311 1013741 := bbase (se 3 (by rfl) ⟨190076, by rfl⟩ : syracuseStep 1013741 = 380153) (by norm_num)
theorem B1013765 : Blo 674311 1013765 := bbase (se 4 (by rfl) ⟨95040, by rfl⟩ : syracuseStep 1013765 = 190081) (by norm_num)
theorem B1013789 : Blo 674311 1013789 := bbase (se 3 (by rfl) ⟨190085, by rfl⟩ : syracuseStep 1013789 = 380171) (by norm_num)
theorem B1013813 : Blo 674311 1013813 := bbase (se 5 (by rfl) ⟨47522, by rfl⟩ : syracuseStep 1013813 = 95045) (by norm_num)
theorem B1013837 : Blo 674311 1013837 := bbase (se 3 (by rfl) ⟨190094, by rfl⟩ : syracuseStep 1013837 = 380189) (by norm_num)
theorem B1013861 : Blo 674311 1013861 := bbase (se 4 (by rfl) ⟨95049, by rfl⟩ : syracuseStep 1013861 = 190099) (by norm_num)
theorem B1013885 : Blo 674311 1013885 := bbase (se 3 (by rfl) ⟨190103, by rfl⟩ : syracuseStep 1013885 = 380207) (by norm_num)
theorem B1013909 : Blo 674311 1013909 := bbase (se 6 (by rfl) ⟨23763, by rfl⟩ : syracuseStep 1013909 = 47527) (by norm_num)
theorem B1013933 : Blo 674311 1013933 := bbase (se 3 (by rfl) ⟨190112, by rfl⟩ : syracuseStep 1013933 = 380225) (by norm_num)
theorem B1013957 : Blo 674311 1013957 := bbase (se 4 (by rfl) ⟨95058, by rfl⟩ : syracuseStep 1013957 = 190117) (by norm_num)
theorem B1013981 : Blo 674311 1013981 := bbase (se 3 (by rfl) ⟨190121, by rfl⟩ : syracuseStep 1013981 = 380243) (by norm_num)
theorem B1014005 : Blo 674311 1014005 := bbase (se 5 (by rfl) ⟨47531, by rfl⟩ : syracuseStep 1014005 = 95063) (by norm_num)
theorem B1014029 : Blo 674311 1014029 := bbase (se 3 (by rfl) ⟨190130, by rfl⟩ : syracuseStep 1014029 = 380261) (by norm_num)
theorem B2193685 : Blo 674311 2193685 := bbase (se 6 (by rfl) ⟨51414, by rfl⟩ : syracuseStep 2193685 = 102829) (by norm_num)
theorem B1014053 : Blo 674311 1014053 := bbase (se 4 (by rfl) ⟨95067, by rfl⟩ : syracuseStep 1014053 = 190135) (by norm_num)
theorem B1014077 : Blo 674311 1014077 := bbase (se 3 (by rfl) ⟨190139, by rfl⟩ : syracuseStep 1014077 = 380279) (by norm_num)
theorem B1014101 : Blo 674311 1014101 := bbase (se 10 (by rfl) ⟨1485, by rfl⟩ : syracuseStep 1014101 = 2971) (by norm_num)
theorem B1014125 : Blo 674311 1014125 := bbase (se 3 (by rfl) ⟨190148, by rfl⟩ : syracuseStep 1014125 = 380297) (by norm_num)
theorem B1014149 : Blo 674311 1014149 := bbase (se 4 (by rfl) ⟨95076, by rfl⟩ : syracuseStep 1014149 = 190153) (by norm_num)
theorem B1538461 : Blo 674311 1538461 := bbase (se 3 (by rfl) ⟨288461, by rfl⟩ : syracuseStep 1538461 = 576923) (by norm_num)
theorem B1014173 : Blo 674311 1014173 := bbase (se 3 (by rfl) ⟨190157, by rfl⟩ : syracuseStep 1014173 = 380315) (by norm_num)
theorem B1014197 : Blo 674311 1014197 := bbase (se 5 (by rfl) ⟨47540, by rfl⟩ : syracuseStep 1014197 = 95081) (by norm_num)
theorem B1014221 : Blo 674311 1014221 := bbase (se 3 (by rfl) ⟨190166, by rfl⟩ : syracuseStep 1014221 = 380333) (by norm_num)
theorem B1014245 : Blo 674311 1014245 := bbase (se 4 (by rfl) ⟨95085, by rfl⟩ : syracuseStep 1014245 = 190171) (by norm_num)
theorem B1014269 : Blo 674311 1014269 := bbase (se 3 (by rfl) ⟨190175, by rfl⟩ : syracuseStep 1014269 = 380351) (by norm_num)
theorem B1014293 : Blo 674311 1014293 := bbase (se 6 (by rfl) ⟨23772, by rfl⟩ : syracuseStep 1014293 = 47545) (by norm_num)
theorem B1014317 : Blo 674311 1014317 := bbase (se 3 (by rfl) ⟨190184, by rfl⟩ : syracuseStep 1014317 = 380369) (by norm_num)
theorem B1014341 : Blo 674311 1014341 := bbase (se 4 (by rfl) ⟨95094, by rfl⟩ : syracuseStep 1014341 = 190189) (by norm_num)
theorem B1014365 : Blo 674311 1014365 := bbase (se 3 (by rfl) ⟨190193, by rfl⟩ : syracuseStep 1014365 = 380387) (by norm_num)
theorem B1014389 : Blo 674311 1014389 := bbase (se 5 (by rfl) ⟨47549, by rfl⟩ : syracuseStep 1014389 = 95099) (by norm_num)
theorem B1014413 : Blo 674311 1014413 := bbase (se 3 (by rfl) ⟨190202, by rfl⟩ : syracuseStep 1014413 = 380405) (by norm_num)
theorem B1014437 : Blo 674311 1014437 := bbase (se 4 (by rfl) ⟨95103, by rfl⟩ : syracuseStep 1014437 = 190207) (by norm_num)
theorem B1014461 : Blo 674311 1014461 := bbase (se 3 (by rfl) ⟨190211, by rfl⟩ : syracuseStep 1014461 = 380423) (by norm_num)
theorem B1014485 : Blo 674311 1014485 := bbase (se 7 (by rfl) ⟨11888, by rfl⟩ : syracuseStep 1014485 = 23777) (by norm_num)
theorem B1014509 : Blo 674311 1014509 := bbase (se 3 (by rfl) ⟨190220, by rfl⟩ : syracuseStep 1014509 = 380441) (by norm_num)
theorem B1014533 : Blo 674311 1014533 := bbase (se 4 (by rfl) ⟨95112, by rfl⟩ : syracuseStep 1014533 = 190225) (by norm_num)
theorem B1014557 : Blo 674311 1014557 := bbase (se 3 (by rfl) ⟨190229, by rfl⟩ : syracuseStep 1014557 = 380459) (by norm_num)
theorem B1014581 : Blo 674311 1014581 := bbase (se 5 (by rfl) ⟨47558, by rfl⟩ : syracuseStep 1014581 = 95117) (by norm_num)
theorem B1014605 : Blo 674311 1014605 := bbase (se 3 (by rfl) ⟨190238, by rfl⟩ : syracuseStep 1014605 = 380477) (by norm_num)
theorem B1014629 : Blo 674311 1014629 := bbase (se 4 (by rfl) ⟨95121, by rfl⟩ : syracuseStep 1014629 = 190243) (by norm_num)
theorem B1014653 : Blo 674311 1014653 := bbase (se 3 (by rfl) ⟨190247, by rfl⟩ : syracuseStep 1014653 = 380495) (by norm_num)
theorem B1014677 : Blo 674311 1014677 := bbase (se 6 (by rfl) ⟨23781, by rfl⟩ : syracuseStep 1014677 = 47563) (by norm_num)
theorem B1014701 : Blo 674311 1014701 := bbase (se 3 (by rfl) ⟨190256, by rfl⟩ : syracuseStep 1014701 = 380513) (by norm_num)
theorem B1080253 : Blo 674311 1080253 := bbase (se 3 (by rfl) ⟨202547, by rfl⟩ : syracuseStep 1080253 = 405095) (by norm_num)
theorem B1014725 : Blo 674311 1014725 := bbase (se 4 (by rfl) ⟨95130, by rfl⟩ : syracuseStep 1014725 = 190261) (by norm_num)
theorem B1014749 : Blo 674311 1014749 := bbase (se 3 (by rfl) ⟨190265, by rfl⟩ : syracuseStep 1014749 = 380531) (by norm_num)
theorem B1014773 : Blo 674311 1014773 := bbase (se 5 (by rfl) ⟨47567, by rfl⟩ : syracuseStep 1014773 = 95135) (by norm_num)
theorem B1014797 : Blo 674311 1014797 := bbase (se 3 (by rfl) ⟨190274, by rfl⟩ : syracuseStep 1014797 = 380549) (by norm_num)
theorem B1014821 : Blo 674311 1014821 := bbase (se 4 (by rfl) ⟨95139, by rfl⟩ : syracuseStep 1014821 = 190279) (by norm_num)
theorem B1014845 : Blo 674311 1014845 := bbase (se 3 (by rfl) ⟨190283, by rfl⟩ : syracuseStep 1014845 = 380567) (by norm_num)
theorem B1014869 : Blo 674311 1014869 := bbase (se 8 (by rfl) ⟨5946, by rfl⟩ : syracuseStep 1014869 = 11893) (by norm_num)
theorem B1014893 : Blo 674311 1014893 := bbase (se 3 (by rfl) ⟨190292, by rfl⟩ : syracuseStep 1014893 = 380585) (by norm_num)
theorem B1014917 : Blo 674311 1014917 := bbase (se 4 (by rfl) ⟨95148, by rfl⟩ : syracuseStep 1014917 = 190297) (by norm_num)
theorem B1014941 : Blo 674311 1014941 := bbase (se 3 (by rfl) ⟨190301, by rfl⟩ : syracuseStep 1014941 = 380603) (by norm_num)
theorem B1014965 : Blo 674311 1014965 := bbase (se 5 (by rfl) ⟨47576, by rfl⟩ : syracuseStep 1014965 = 95153) (by norm_num)
theorem B1014989 : Blo 674311 1014989 := bbase (se 3 (by rfl) ⟨190310, by rfl⟩ : syracuseStep 1014989 = 380621) (by norm_num)
theorem B1015013 : Blo 674311 1015013 := bbase (se 4 (by rfl) ⟨95157, by rfl⟩ : syracuseStep 1015013 = 190315) (by norm_num)
theorem B1015037 : Blo 674311 1015037 := bbase (se 3 (by rfl) ⟨190319, by rfl⟩ : syracuseStep 1015037 = 380639) (by norm_num)
theorem B1015061 : Blo 674311 1015061 := bbase (se 6 (by rfl) ⟨23790, by rfl⟩ : syracuseStep 1015061 = 47581) (by norm_num)
theorem B1015085 : Blo 674311 1015085 := bbase (se 3 (by rfl) ⟨190328, by rfl⟩ : syracuseStep 1015085 = 380657) (by norm_num)
theorem B720181 : Blo 674311 720181 := bbase (se 5 (by rfl) ⟨33758, by rfl⟩ : syracuseStep 720181 = 67517) (by norm_num)
theorem B1015109 : Blo 674311 1015109 := bbase (se 4 (by rfl) ⟨95166, by rfl⟩ : syracuseStep 1015109 = 190333) (by norm_num)
theorem B1015133 : Blo 674311 1015133 := bbase (se 3 (by rfl) ⟨190337, by rfl⟩ : syracuseStep 1015133 = 380675) (by norm_num)
theorem B1015157 : Blo 674311 1015157 := bbase (se 5 (by rfl) ⟨47585, by rfl⟩ : syracuseStep 1015157 = 95171) (by norm_num)
theorem B1441165 : Blo 674311 1441165 := bbase (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) (by norm_num)
theorem B1015181 : Blo 674311 1015181 := bbase (se 3 (by rfl) ⟨190346, by rfl⟩ : syracuseStep 1015181 = 380693) (by norm_num)
theorem B1015205 : Blo 674311 1015205 := bbase (se 4 (by rfl) ⟨95175, by rfl⟩ : syracuseStep 1015205 = 190351) (by norm_num)
theorem B1736117 : Blo 674311 1736117 := bbase (se 5 (by rfl) ⟨81380, by rfl⟩ : syracuseStep 1736117 = 162761) (by norm_num)
theorem B1015229 : Blo 674311 1015229 := bbase (se 3 (by rfl) ⟨190355, by rfl⟩ : syracuseStep 1015229 = 380711) (by norm_num)
theorem B1015253 : Blo 674311 1015253 := bbase (se 7 (by rfl) ⟨11897, by rfl⟩ : syracuseStep 1015253 = 23795) (by norm_num)
theorem B1015277 : Blo 674311 1015277 := bbase (se 3 (by rfl) ⟨190364, by rfl⟩ : syracuseStep 1015277 = 380729) (by norm_num)
theorem B1015301 : Blo 674311 1015301 := bbase (se 4 (by rfl) ⟨95184, by rfl⟩ : syracuseStep 1015301 = 190369) (by norm_num)
theorem B1015325 : Blo 674311 1015325 := bbase (se 3 (by rfl) ⟨190373, by rfl⟩ : syracuseStep 1015325 = 380747) (by norm_num)
theorem B1015349 : Blo 674311 1015349 := bbase (se 5 (by rfl) ⟨47594, by rfl⟩ : syracuseStep 1015349 = 95189) (by norm_num)
theorem B1015373 : Blo 674311 1015373 := bbase (se 3 (by rfl) ⟨190382, by rfl⟩ : syracuseStep 1015373 = 380765) (by norm_num)
theorem B1015397 : Blo 674311 1015397 := bbase (se 4 (by rfl) ⟨95193, by rfl⟩ : syracuseStep 1015397 = 190387) (by norm_num)
theorem B1015421 : Blo 674311 1015421 := bbase (se 3 (by rfl) ⟨190391, by rfl⟩ : syracuseStep 1015421 = 380783) (by norm_num)
theorem B1015445 : Blo 674311 1015445 := bbase (se 6 (by rfl) ⟨23799, by rfl⟩ : syracuseStep 1015445 = 47599) (by norm_num)
theorem B1015469 : Blo 674311 1015469 := bbase (se 3 (by rfl) ⟨190400, by rfl⟩ : syracuseStep 1015469 = 380801) (by norm_num)
theorem B1015493 : Blo 674311 1015493 := bbase (se 4 (by rfl) ⟨95202, by rfl⟩ : syracuseStep 1015493 = 190405) (by norm_num)
theorem B2162389 : Blo 674311 2162389 := bbase (se 7 (by rfl) ⟨25340, by rfl⟩ : syracuseStep 2162389 = 50681) (by norm_num)
theorem B1015517 : Blo 674311 1015517 := bbase (se 3 (by rfl) ⟨190409, by rfl⟩ : syracuseStep 1015517 = 380819) (by norm_num)
theorem B720613 : Blo 674311 720613 := bbase (se 4 (by rfl) ⟨67557, by rfl⟩ : syracuseStep 720613 = 135115) (by norm_num)
theorem B1015541 : Blo 674311 1015541 := bbase (se 5 (by rfl) ⟨47603, by rfl⟩ : syracuseStep 1015541 = 95207) (by norm_num)
theorem B5144309 : Blo 674311 5144309 := bbase (se 5 (by rfl) ⟨241139, by rfl⟩ : syracuseStep 5144309 = 482279) (by norm_num)
theorem B1015565 : Blo 674311 1015565 := bbase (se 3 (by rfl) ⟨190418, by rfl⟩ : syracuseStep 1015565 = 380837) (by norm_num)
theorem B1015589 : Blo 674311 1015589 := bbase (se 4 (by rfl) ⟨95211, by rfl⟩ : syracuseStep 1015589 = 190423) (by norm_num)
theorem B720685 : Blo 674311 720685 := bbase (se 3 (by rfl) ⟨135128, by rfl⟩ : syracuseStep 720685 = 270257) (by norm_num)
theorem B1015613 : Blo 674311 1015613 := bbase (se 3 (by rfl) ⟨190427, by rfl⟩ : syracuseStep 1015613 = 380855) (by norm_num)
theorem B3702613 : Blo 674311 3702613 := bbase (se 9 (by rfl) ⟨10847, by rfl⟩ : syracuseStep 3702613 = 21695) (by norm_num)
theorem B1015637 : Blo 674311 1015637 := bbase (se 9 (by rfl) ⟨2975, by rfl⟩ : syracuseStep 1015637 = 5951) (by norm_num)
theorem B1015661 : Blo 674311 1015661 := bbase (se 3 (by rfl) ⟨190436, by rfl⟩ : syracuseStep 1015661 = 380873) (by norm_num)
theorem B1015685 : Blo 674311 1015685 := bbase (se 4 (by rfl) ⟨95220, by rfl⟩ : syracuseStep 1015685 = 190441) (by norm_num)
theorem B1015709 : Blo 674311 1015709 := bbase (se 3 (by rfl) ⟨190445, by rfl⟩ : syracuseStep 1015709 = 380891) (by norm_num)
theorem B1015733 : Blo 674311 1015733 := bbase (se 5 (by rfl) ⟨47612, by rfl⟩ : syracuseStep 1015733 = 95225) (by norm_num)
theorem B1015757 : Blo 674311 1015757 := bbase (se 3 (by rfl) ⟨190454, by rfl⟩ : syracuseStep 1015757 = 380909) (by norm_num)
theorem B3243989 : Blo 674311 3243989 := bbase (se 7 (by rfl) ⟨38015, by rfl⟩ : syracuseStep 3243989 = 76031) (by norm_num)
theorem B1015781 : Blo 674311 1015781 := bbase (se 4 (by rfl) ⟨95229, by rfl⟩ : syracuseStep 1015781 = 190459) (by norm_num)
theorem B1015805 : Blo 674311 1015805 := bbase (se 3 (by rfl) ⟨190463, by rfl⟩ : syracuseStep 1015805 = 380927) (by norm_num)
theorem B1015811 : Blo 674311 1015811 := bstep (se 1 (by rfl) ⟨761858, by rfl⟩ : syracuseStep 1015811 = 1523717) B1523717
theorem B1015841 : Blo 674311 1015841 := bstep (se 2 (by rfl) ⟨380940, by rfl⟩ : syracuseStep 1015841 = 761881) B761881
theorem B1015859 : Blo 674311 1015859 := bstep (se 1 (by rfl) ⟨761894, by rfl⟩ : syracuseStep 1015859 = 1523789) B1523789
theorem B1015889 : Blo 674311 1015889 := bstep (se 2 (by rfl) ⟨380958, by rfl⟩ : syracuseStep 1015889 = 761917) B761917
theorem B1015907 : Blo 674311 1015907 := bstep (se 1 (by rfl) ⟨761930, by rfl⟩ : syracuseStep 1015907 = 1523861) B1523861
theorem B1015937 : Blo 674311 1015937 := bstep (se 2 (by rfl) ⟨380976, by rfl⟩ : syracuseStep 1015937 = 761953) B761953
theorem B8781965 : Blo 674311 8781965 := bstep (se 3 (by rfl) ⟨1646618, by rfl⟩ : syracuseStep 8781965 = 3293237) B3293237
theorem B1015955 : Blo 674311 1015955 := bstep (se 1 (by rfl) ⟨761966, by rfl⟩ : syracuseStep 1015955 = 1523933) B1523933
theorem B1015985 : Blo 674311 1015985 := bstep (se 2 (by rfl) ⟨380994, by rfl⟩ : syracuseStep 1015985 = 761989) B761989
theorem B1016003 : Blo 674311 1016003 := bstep (se 1 (by rfl) ⟨762002, by rfl⟩ : syracuseStep 1016003 = 1524005) B1524005
theorem B1016033 : Blo 674311 1016033 := bstep (se 2 (by rfl) ⟨381012, by rfl⟩ : syracuseStep 1016033 = 762025) B762025
theorem B1016051 : Blo 674311 1016051 := bstep (se 1 (by rfl) ⟨762038, by rfl⟩ : syracuseStep 1016051 = 1524077) B1524077
theorem B1016081 : Blo 674311 1016081 := bstep (se 2 (by rfl) ⟨381030, by rfl⟩ : syracuseStep 1016081 = 762061) B762061
theorem B1016099 : Blo 674311 1016099 := bstep (se 1 (by rfl) ⟨762074, by rfl⟩ : syracuseStep 1016099 = 1524149) B1524149
theorem B1016129 : Blo 674311 1016129 := bstep (se 2 (by rfl) ⟨381048, by rfl⟩ : syracuseStep 1016129 = 762097) B762097
theorem B1016147 : Blo 674311 1016147 := bstep (se 1 (by rfl) ⟨762110, by rfl⟩ : syracuseStep 1016147 = 1524221) B1524221
theorem B1016177 : Blo 674311 1016177 := bstep (se 2 (by rfl) ⟨381066, by rfl⟩ : syracuseStep 1016177 = 762133) B762133
theorem B721283 : Blo 674311 721283 := bstep (se 1 (by rfl) ⟨540962, by rfl⟩ : syracuseStep 721283 = 1081925) B1081925
theorem B1016195 : Blo 674311 1016195 := bstep (se 1 (by rfl) ⟨762146, by rfl⟩ : syracuseStep 1016195 = 1524293) B1524293
theorem B1016225 : Blo 674311 1016225 := bstep (se 2 (by rfl) ⟨381084, by rfl⟩ : syracuseStep 1016225 = 762169) B762169
theorem B1442225 : Blo 674311 1442225 := bstep (se 2 (by rfl) ⟨540834, by rfl⟩ : syracuseStep 1442225 = 1081669) B1081669
theorem B1016243 : Blo 674311 1016243 := bstep (se 1 (by rfl) ⟨762182, by rfl⟩ : syracuseStep 1016243 = 1524365) B1524365
theorem B1016273 : Blo 674311 1016273 := bstep (se 2 (by rfl) ⟨381102, by rfl⟩ : syracuseStep 1016273 = 762205) B762205
theorem B1016291 : Blo 674311 1016291 := bstep (se 1 (by rfl) ⟨762218, by rfl⟩ : syracuseStep 1016291 = 1524437) B1524437
theorem B1016321 : Blo 674311 1016321 := bstep (se 2 (by rfl) ⟨381120, by rfl⟩ : syracuseStep 1016321 = 762241) B762241
theorem B1016339 : Blo 674311 1016339 := bstep (se 1 (by rfl) ⟨762254, by rfl⟩ : syracuseStep 1016339 = 1524509) B1524509
theorem B1016369 : Blo 674311 1016369 := bstep (se 2 (by rfl) ⟨381138, by rfl⟩ : syracuseStep 1016369 = 762277) B762277
theorem B1016387 : Blo 674311 1016387 := bstep (se 1 (by rfl) ⟨762290, by rfl⟩ : syracuseStep 1016387 = 1524581) B1524581
theorem B1016417 : Blo 674311 1016417 := bstep (se 2 (by rfl) ⟨381156, by rfl⟩ : syracuseStep 1016417 = 762313) B762313
theorem B1016435 : Blo 674311 1016435 := bstep (se 1 (by rfl) ⟨762326, by rfl⟩ : syracuseStep 1016435 = 1524653) B1524653
theorem B1016465 : Blo 674311 1016465 := bstep (se 2 (by rfl) ⟨381174, by rfl⟩ : syracuseStep 1016465 = 762349) B762349
theorem B1016483 : Blo 674311 1016483 := bstep (se 1 (by rfl) ⟨762362, by rfl⟩ : syracuseStep 1016483 = 1524725) B1524725
theorem B1016513 : Blo 674311 1016513 := bstep (se 2 (by rfl) ⟨381192, by rfl⟩ : syracuseStep 1016513 = 762385) B762385
theorem B1016531 : Blo 674311 1016531 := bstep (se 1 (by rfl) ⟨762398, by rfl⟩ : syracuseStep 1016531 = 1524797) B1524797
theorem B1016561 : Blo 674311 1016561 := bstep (se 2 (by rfl) ⟨381210, by rfl⟩ : syracuseStep 1016561 = 762421) B762421
theorem B1016579 : Blo 674311 1016579 := bstep (se 1 (by rfl) ⟨762434, by rfl⟩ : syracuseStep 1016579 = 1524869) B1524869
theorem B1016609 : Blo 674311 1016609 := bstep (se 2 (by rfl) ⟨381228, by rfl⟩ : syracuseStep 1016609 = 762457) B762457
theorem B1016627 : Blo 674311 1016627 := bstep (se 1 (by rfl) ⟨762470, by rfl⟩ : syracuseStep 1016627 = 1524941) B1524941
theorem B1016657 : Blo 674311 1016657 := bstep (se 2 (by rfl) ⟨381246, by rfl⟩ : syracuseStep 1016657 = 762493) B762493
theorem B1016675 : Blo 674311 1016675 := bstep (se 1 (by rfl) ⟨762506, by rfl⟩ : syracuseStep 1016675 = 1525013) B1525013
theorem B1016705 : Blo 674311 1016705 := bstep (se 2 (by rfl) ⟨381264, by rfl⟩ : syracuseStep 1016705 = 762529) B762529
theorem B1016723 : Blo 674311 1016723 := bstep (se 1 (by rfl) ⟨762542, by rfl⟩ : syracuseStep 1016723 = 1525085) B1525085
theorem B1016753 : Blo 674311 1016753 := bstep (se 2 (by rfl) ⟨381282, by rfl⟩ : syracuseStep 1016753 = 762565) B762565
theorem B1016771 : Blo 674311 1016771 := bstep (se 1 (by rfl) ⟨762578, by rfl⟩ : syracuseStep 1016771 = 1525157) B1525157
theorem B1016801 : Blo 674311 1016801 := bstep (se 2 (by rfl) ⟨381300, by rfl⟩ : syracuseStep 1016801 = 762601) B762601
theorem B1016819 : Blo 674311 1016819 := bstep (se 1 (by rfl) ⟨762614, by rfl⟩ : syracuseStep 1016819 = 1525229) B1525229
theorem B1016849 : Blo 674311 1016849 := bstep (se 2 (by rfl) ⟨381318, by rfl⟩ : syracuseStep 1016849 = 762637) B762637
theorem B1016867 : Blo 674311 1016867 := bstep (se 1 (by rfl) ⟨762650, by rfl⟩ : syracuseStep 1016867 = 1525301) B1525301
theorem B1016897 : Blo 674311 1016897 := bstep (se 2 (by rfl) ⟨381336, by rfl⟩ : syracuseStep 1016897 = 762673) B762673
theorem B1016915 : Blo 674311 1016915 := bstep (se 1 (by rfl) ⟨762686, by rfl⟩ : syracuseStep 1016915 = 1525373) B1525373
theorem B1016945 : Blo 674311 1016945 := bstep (se 2 (by rfl) ⟨381354, by rfl⟩ : syracuseStep 1016945 = 762709) B762709
theorem B722035 : Blo 674311 722035 := bstep (se 1 (by rfl) ⟨541526, by rfl⟩ : syracuseStep 722035 = 1083053) B1083053
theorem B1016963 : Blo 674311 1016963 := bstep (se 1 (by rfl) ⟨762722, by rfl⟩ : syracuseStep 1016963 = 1525445) B1525445
theorem B1016993 : Blo 674311 1016993 := bstep (se 2 (by rfl) ⟨381372, by rfl⟩ : syracuseStep 1016993 = 762745) B762745
theorem B1017011 : Blo 674311 1017011 := bstep (se 1 (by rfl) ⟨762758, by rfl⟩ : syracuseStep 1017011 = 1525517) B1525517
theorem B1017041 : Blo 674311 1017041 := bstep (se 2 (by rfl) ⟨381390, by rfl⟩ : syracuseStep 1017041 = 762781) B762781
theorem B1017059 : Blo 674311 1017059 := bstep (se 1 (by rfl) ⟨762794, by rfl⟩ : syracuseStep 1017059 = 1525589) B1525589
theorem B1017089 : Blo 674311 1017089 := bstep (se 2 (by rfl) ⟨381408, by rfl⟩ : syracuseStep 1017089 = 762817) B762817
theorem B1017107 : Blo 674311 1017107 := bstep (se 1 (by rfl) ⟨762830, by rfl⟩ : syracuseStep 1017107 = 1525661) B1525661
theorem B1017137 : Blo 674311 1017137 := bstep (se 2 (by rfl) ⟨381426, by rfl⟩ : syracuseStep 1017137 = 762853) B762853
theorem B1017155 : Blo 674311 1017155 := bstep (se 1 (by rfl) ⟨762866, by rfl⟩ : syracuseStep 1017155 = 1525733) B1525733
theorem B1017185 : Blo 674311 1017185 := bstep (se 2 (by rfl) ⟨381444, by rfl⟩ : syracuseStep 1017185 = 762889) B762889
theorem B722291 : Blo 674311 722291 := bstep (se 1 (by rfl) ⟨541718, by rfl⟩ : syracuseStep 722291 = 1083437) B1083437
theorem B1017203 : Blo 674311 1017203 := bstep (se 1 (by rfl) ⟨762902, by rfl⟩ : syracuseStep 1017203 = 1525805) B1525805
theorem B16647565 : Blo 674311 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B9733517 : Blo 674311 9733517 := bstep (se 3 (by rfl) ⟨1825034, by rfl⟩ : syracuseStep 9733517 = 3650069) B3650069
theorem B1017233 : Blo 674311 1017233 := bstep (se 2 (by rfl) ⟨381462, by rfl⟩ : syracuseStep 1017233 = 762925) B762925
theorem B1017251 : Blo 674311 1017251 := bstep (se 1 (by rfl) ⟨762938, by rfl⟩ : syracuseStep 1017251 = 1525877) B1525877
theorem B1017281 : Blo 674311 1017281 := bstep (se 2 (by rfl) ⟨381480, by rfl⟩ : syracuseStep 1017281 = 762961) B762961
theorem B11699653 : Blo 674311 11699653 := bstep (se 4 (by rfl) ⟨1096842, by rfl⟩ : syracuseStep 11699653 = 2193685) B2193685
theorem B1017299 : Blo 674311 1017299 := bstep (se 1 (by rfl) ⟨762974, by rfl⟩ : syracuseStep 1017299 = 1525949) B1525949
theorem B1017329 : Blo 674311 1017329 := bstep (se 2 (by rfl) ⟨381498, by rfl⟩ : syracuseStep 1017329 = 762997) B762997
theorem B853507 : Blo 674311 853507 := bstep (se 1 (by rfl) ⟨640130, by rfl⟩ : syracuseStep 853507 = 1280261) B1280261
theorem B1017347 : Blo 674311 1017347 := bstep (se 1 (by rfl) ⟨763010, by rfl⟩ : syracuseStep 1017347 = 1526021) B1526021
theorem B1082899 : Blo 674311 1082899 := bstep (se 1 (by rfl) ⟨812174, by rfl⟩ : syracuseStep 1082899 = 1624349) B1624349
theorem B1017377 : Blo 674311 1017377 := bstep (se 2 (by rfl) ⟨381516, by rfl⟩ : syracuseStep 1017377 = 763033) B763033
theorem B2164259 : Blo 674311 2164259 := bstep (se 1 (by rfl) ⟨1623194, by rfl⟩ : syracuseStep 2164259 = 3246389) B3246389
theorem B1017395 : Blo 674311 1017395 := bstep (se 1 (by rfl) ⟨763046, by rfl⟩ : syracuseStep 1017395 = 1526093) B1526093
theorem B1017425 : Blo 674311 1017425 := bstep (se 2 (by rfl) ⟨381534, by rfl⟩ : syracuseStep 1017425 = 763069) B763069
theorem B1017443 : Blo 674311 1017443 := bstep (se 1 (by rfl) ⟨763082, by rfl⟩ : syracuseStep 1017443 = 1526165) B1526165
theorem B5146253 : Blo 674311 5146253 := bstep (se 3 (by rfl) ⟨964922, by rfl⟩ : syracuseStep 5146253 = 1929845) B1929845
theorem B1443523 : Blo 674311 1443523 := bstep (se 1 (by rfl) ⟨1082642, by rfl⟩ : syracuseStep 1443523 = 2165285) B2165285
theorem B3245987 : Blo 674311 3245987 := bstep (se 1 (by rfl) ⟨2434490, by rfl⟩ : syracuseStep 3245987 = 4868981) B4868981
theorem B854003 : Blo 674311 854003 := bstep (se 1 (by rfl) ⟨640502, by rfl⟩ : syracuseStep 854003 = 1281005) B1281005
theorem B2885645 : Blo 674311 2885645 := bstep (se 3 (by rfl) ⟨541058, by rfl⟩ : syracuseStep 2885645 = 1082117) B1082117
theorem B723043 : Blo 674311 723043 := bstep (se 1 (by rfl) ⟨542282, by rfl⟩ : syracuseStep 723043 = 1084565) B1084565
theorem B1739153 : Blo 674311 1739153 := bstep (se 2 (by rfl) ⟨652182, by rfl⟩ : syracuseStep 1739153 = 1304365) B1304365
theorem B2165233 : Blo 674311 2165233 := bstep (se 2 (by rfl) ⟨811962, by rfl⟩ : syracuseStep 2165233 = 1623925) B1623925
theorem B4328005 : Blo 674311 4328005 := bstep (se 4 (by rfl) ⟨405750, by rfl⟩ : syracuseStep 4328005 = 811501) B811501
theorem B9767537 : Blo 674311 9767537 := bstep (se 2 (by rfl) ⟨3662826, by rfl⟩ : syracuseStep 9767537 = 7325653) B7325653
theorem B854707 : Blo 674311 854707 := bstep (se 1 (by rfl) ⟨641030, by rfl⟩ : syracuseStep 854707 = 1282061) B1282061
theorem B1280785 : Blo 674311 1280785 := bstep (se 2 (by rfl) ⟨480294, by rfl⟩ : syracuseStep 1280785 = 960589) B960589
theorem B854803 : Blo 674311 854803 := bstep (se 1 (by rfl) ⟨641102, by rfl⟩ : syracuseStep 854803 = 1282205) B1282205
theorem B1444753 : Blo 674311 1444753 := bstep (se 2 (by rfl) ⟨541782, by rfl⟩ : syracuseStep 1444753 = 1083565) B1083565
theorem B1084385 : Blo 674311 1084385 := bstep (se 2 (by rfl) ⟨406644, by rfl⟩ : syracuseStep 1084385 = 813289) B813289
theorem B1543139 : Blo 674311 1543139 := bstep (se 1 (by rfl) ⟨1157354, by rfl⟩ : syracuseStep 1543139 = 2314709) B2314709
theorem B1084513 : Blo 674311 1084513 := bstep (se 2 (by rfl) ⟨406692, by rfl⟩ : syracuseStep 1084513 = 813385) B813385
theorem B1281187 : Blo 674311 1281187 := bstep (se 1 (by rfl) ⟨960890, by rfl⟩ : syracuseStep 1281187 = 1921781) B1921781
theorem B1281233 : Blo 674311 1281233 := bstep (se 2 (by rfl) ⟨480462, by rfl⟩ : syracuseStep 1281233 = 960925) B960925
theorem B8326385 : Blo 674311 8326385 := bstep (se 2 (by rfl) ⟨3122394, by rfl⟩ : syracuseStep 8326385 = 6244789) B6244789
theorem B855299 : Blo 674311 855299 := bstep (se 1 (by rfl) ⟨641474, by rfl⟩ : syracuseStep 855299 = 1282949) B1282949
theorem B2886961 : Blo 674311 2886961 := bstep (se 2 (by rfl) ⟨1082610, by rfl⟩ : syracuseStep 2886961 = 2165221) B2165221
theorem B724307 : Blo 674311 724307 := bstep (se 1 (by rfl) ⟨543230, by rfl⟩ : syracuseStep 724307 = 1086461) B1086461
theorem B1281521 : Blo 674311 1281521 := bstep (se 2 (by rfl) ⟨480570, by rfl⟩ : syracuseStep 1281521 = 961141) B961141
theorem B1707601 : Blo 674311 1707601 := bstep (se 2 (by rfl) ⟨640350, by rfl⟩ : syracuseStep 1707601 = 1280701) B1280701
theorem B1445539 : Blo 674311 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B1707875 : Blo 674311 1707875 := bstep (se 1 (by rfl) ⟨1280906, by rfl⟩ : syracuseStep 1707875 = 2561813) B2561813
theorem B1216387 : Blo 674311 1216387 := bstep (se 1 (by rfl) ⟨912290, by rfl⟩ : syracuseStep 1216387 = 1824581) B1824581
theorem B856003 : Blo 674311 856003 := bstep (se 1 (by rfl) ⟨642002, by rfl⟩ : syracuseStep 856003 = 1284005) B1284005
theorem B1708067 : Blo 674311 1708067 := bstep (se 1 (by rfl) ⟨1281050, by rfl⟩ : syracuseStep 1708067 = 2562101) B2562101
theorem B856099 : Blo 674311 856099 := bstep (se 1 (by rfl) ⟨642074, by rfl⟩ : syracuseStep 856099 = 1284149) B1284149
theorem B2166925 : Blo 674311 2166925 := bstep (se 3 (by rfl) ⟨406298, by rfl⟩ : syracuseStep 2166925 = 812597) B812597
theorem B1282243 : Blo 674311 1282243 := bstep (se 1 (by rfl) ⟨961682, by rfl⟩ : syracuseStep 1282243 = 1923365) B1923365
theorem B2560355 : Blo 674311 2560355 := bstep (se 1 (by rfl) ⟨1920266, by rfl⟩ : syracuseStep 2560355 = 3840533) B3840533
theorem B1085795 : Blo 674311 1085795 := bstep (se 1 (by rfl) ⟨814346, by rfl⟩ : syracuseStep 1085795 = 1628693) B1628693
theorem B2560369 : Blo 674311 2560369 := bstep (se 2 (by rfl) ⟨960138, by rfl⟩ : syracuseStep 2560369 = 1920277) B1920277
theorem B1446257 : Blo 674311 1446257 := bstep (se 2 (by rfl) ⟨542346, by rfl⟩ : syracuseStep 1446257 = 1084693) B1084693
theorem B1216963 : Blo 674311 1216963 := bstep (se 1 (by rfl) ⟨912722, by rfl⟩ : syracuseStep 1216963 = 1825445) B1825445
theorem B1085891 : Blo 674311 1085891 := bstep (se 1 (by rfl) ⟨814418, by rfl⟩ : syracuseStep 1085891 = 1628837) B1628837
theorem B1085923 : Blo 674311 1085923 := bstep (se 1 (by rfl) ⟨814442, by rfl⟩ : syracuseStep 1085923 = 1628885) B1628885
theorem B5149169 : Blo 674311 5149169 := bstep (se 2 (by rfl) ⟨1930938, by rfl⟩ : syracuseStep 5149169 = 3861877) B3861877
theorem B856595 : Blo 674311 856595 := bstep (se 1 (by rfl) ⟨642446, by rfl⟩ : syracuseStep 856595 = 1284893) B1284893
theorem B1282691 : Blo 674311 1282691 := bstep (se 1 (by rfl) ⟨962018, by rfl⟩ : syracuseStep 1282691 = 1924037) B1924037
theorem B1446769 : Blo 674311 1446769 := bstep (se 2 (by rfl) ⟨542538, by rfl⟩ : syracuseStep 1446769 = 1085077) B1085077
theorem B758659 : Blo 674311 758659 := bstep (se 1 (by rfl) ⟨568994, by rfl⟩ : syracuseStep 758659 = 1137989) B1137989
theorem B1282979 : Blo 674311 1282979 := bstep (se 1 (by rfl) ⟨962234, by rfl⟩ : syracuseStep 1282979 = 1924469) B1924469
theorem B1709009 : Blo 674311 1709009 := bstep (se 2 (by rfl) ⟨640878, by rfl⟩ : syracuseStep 1709009 = 1281757) B1281757
theorem B1709059 : Blo 674311 1709059 := bstep (se 1 (by rfl) ⟨1281794, by rfl⟩ : syracuseStep 1709059 = 2563589) B2563589
theorem B758803 : Blo 674311 758803 := bstep (se 1 (by rfl) ⟨569102, by rfl⟩ : syracuseStep 758803 = 1138205) B1138205
theorem B1315921 : Blo 674311 1315921 := bstep (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) B986941
theorem B1709201 : Blo 674311 1709201 := bstep (se 2 (by rfl) ⟨640950, by rfl⟩ : syracuseStep 1709201 = 1281901) B1281901
theorem B758947 : Blo 674311 758947 := bstep (se 1 (by rfl) ⟨569210, by rfl⟩ : syracuseStep 758947 = 1138421) B1138421
theorem B857299 : Blo 674311 857299 := bstep (se 1 (by rfl) ⟨642974, by rfl⟩ : syracuseStep 857299 = 1285949) B1285949
theorem B759091 : Blo 674311 759091 := bstep (se 1 (by rfl) ⟨569318, by rfl⟩ : syracuseStep 759091 = 1138637) B1138637
theorem B857395 : Blo 674311 857395 := bstep (se 1 (by rfl) ⟨643046, by rfl⟩ : syracuseStep 857395 = 1286093) B1286093
theorem B11736433 : Blo 674311 11736433 := bstep (se 2 (by rfl) ⟨4401162, by rfl⟩ : syracuseStep 11736433 = 8802325) B8802325
theorem B759235 : Blo 674311 759235 := bstep (se 1 (by rfl) ⟨569426, by rfl⟩ : syracuseStep 759235 = 1138853) B1138853
theorem B4330979 : Blo 674311 4330979 := bstep (se 1 (by rfl) ⟨3248234, by rfl⟩ : syracuseStep 4330979 = 6496469) B6496469
theorem B1545731 : Blo 674311 1545731 := bstep (se 1 (by rfl) ⟨1159298, by rfl⟩ : syracuseStep 1545731 = 2318597) B2318597
theorem B759379 : Blo 674311 759379 := bstep (se 1 (by rfl) ⟨569534, by rfl⟩ : syracuseStep 759379 = 1139069) B1139069
theorem B2430641 : Blo 674311 2430641 := bstep (se 2 (by rfl) ⟨911490, by rfl⟩ : syracuseStep 2430641 = 1822981) B1822981
theorem B759523 : Blo 674311 759523 := bstep (se 1 (by rfl) ⟨569642, by rfl⟩ : syracuseStep 759523 = 1139285) B1139285
theorem B2561827 : Blo 674311 2561827 := bstep (se 1 (by rfl) ⟨1921370, by rfl⟩ : syracuseStep 2561827 = 3842741) B3842741
theorem B857891 : Blo 674311 857891 := bstep (se 1 (by rfl) ⟨643418, by rfl⟩ : syracuseStep 857891 = 1286837) B1286837
theorem B1283921 : Blo 674311 1283921 := bstep (se 2 (by rfl) ⟨481470, by rfl⟩ : syracuseStep 1283921 = 962941) B962941
theorem B4102001 : Blo 674311 4102001 := bstep (se 2 (by rfl) ⟨1538250, by rfl⟩ : syracuseStep 4102001 = 3076501) B3076501
theorem B759667 : Blo 674311 759667 := bstep (se 1 (by rfl) ⟨569750, by rfl⟩ : syracuseStep 759667 = 1139501) B1139501
theorem B2168707 : Blo 674311 2168707 := bstep (se 1 (by rfl) ⟨1626530, by rfl⟩ : syracuseStep 2168707 = 3253061) B3253061
theorem B3413987 : Blo 674311 3413987 := bstep (se 1 (by rfl) ⟨2560490, by rfl⟩ : syracuseStep 3413987 = 5120981) B5120981
theorem B759811 : Blo 674311 759811 := bstep (se 1 (by rfl) ⟨569858, by rfl⟩ : syracuseStep 759811 = 1139717) B1139717
theorem B1710193 : Blo 674311 1710193 := bstep (se 2 (by rfl) ⟨641322, by rfl⟩ : syracuseStep 1710193 = 1282645) B1282645
theorem B759955 : Blo 674311 759955 := bstep (se 1 (by rfl) ⟨569966, by rfl⟩ : syracuseStep 759955 = 1139933) B1139933
theorem B5478641 : Blo 674311 5478641 := bstep (se 2 (by rfl) ⟨2054490, by rfl⟩ : syracuseStep 5478641 = 4108981) B4108981
theorem B760099 : Blo 674311 760099 := bstep (se 1 (by rfl) ⟨570074, by rfl⟩ : syracuseStep 760099 = 1140149) B1140149
theorem B2890019 : Blo 674311 2890019 := bstep (se 1 (by rfl) ⟨2167514, by rfl⟩ : syracuseStep 2890019 = 4335029) B4335029
theorem B2169155 : Blo 674311 2169155 := bstep (se 1 (by rfl) ⟨1626866, by rfl⟩ : syracuseStep 2169155 = 3253733) B3253733
theorem B1448273 : Blo 674311 1448273 := bstep (se 2 (by rfl) ⟨543102, by rfl⟩ : syracuseStep 1448273 = 1086205) B1086205
theorem B1710467 : Blo 674311 1710467 := bstep (se 1 (by rfl) ⟨1282850, by rfl⟩ : syracuseStep 1710467 = 2565701) B2565701
theorem B760243 : Blo 674311 760243 := bstep (se 1 (by rfl) ⟨570182, by rfl⟩ : syracuseStep 760243 = 1140365) B1140365
theorem B1710659 : Blo 674311 1710659 := bstep (se 1 (by rfl) ⟨1282994, by rfl⟩ : syracuseStep 1710659 = 2565989) B2565989
theorem B760387 : Blo 674311 760387 := bstep (se 1 (by rfl) ⟨570290, by rfl⟩ : syracuseStep 760387 = 1140581) B1140581
theorem B2431565 : Blo 674311 2431565 := bstep (se 3 (by rfl) ⟨455918, by rfl⟩ : syracuseStep 2431565 = 911837) B911837
theorem B1284817 : Blo 674311 1284817 := bstep (se 2 (by rfl) ⟨481806, by rfl⟩ : syracuseStep 1284817 = 963613) B963613
theorem B760531 : Blo 674311 760531 := bstep (se 1 (by rfl) ⟨570398, by rfl⟩ : syracuseStep 760531 = 1140797) B1140797
theorem B1448675 : Blo 674311 1448675 := bstep (se 1 (by rfl) ⟨1086506, by rfl⟩ : syracuseStep 1448675 = 2173013) B2173013
theorem B3414797 : Blo 674311 3414797 := bstep (se 3 (by rfl) ⟨640274, by rfl⟩ : syracuseStep 3414797 = 1280549) B1280549
theorem B1153811 : Blo 674311 1153811 := bstep (se 1 (by rfl) ⟨865358, by rfl⟩ : syracuseStep 1153811 = 1730717) B1730717
theorem B4332365 : Blo 674311 4332365 := bstep (se 3 (by rfl) ⟨812318, by rfl⟩ : syracuseStep 4332365 = 1624637) B1624637
theorem B760675 : Blo 674311 760675 := bstep (se 1 (by rfl) ⟨570506, by rfl⟩ : syracuseStep 760675 = 1141013) B1141013
theorem B1284977 : Blo 674311 1284977 := bstep (se 2 (by rfl) ⟨481866, by rfl⟩ : syracuseStep 1284977 = 963733) B963733
theorem B3840965 : Blo 674311 3840965 := bstep (se 4 (by rfl) ⟨360090, by rfl⟩ : syracuseStep 3840965 = 720181) B720181
theorem B31267781 : Blo 674311 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B760819 : Blo 674311 760819 := bstep (se 1 (by rfl) ⟨570614, by rfl⟩ : syracuseStep 760819 = 1141229) B1141229
theorem B4627505 : Blo 674311 4627505 := bstep (se 2 (by rfl) ⟨1735314, by rfl⟩ : syracuseStep 4627505 = 3470629) B3470629
theorem B760963 : Blo 674311 760963 := bstep (se 1 (by rfl) ⟨570722, by rfl⟩ : syracuseStep 760963 = 1141445) B1141445
theorem B4955377 : Blo 674311 4955377 := bstep (se 2 (by rfl) ⟨1858266, by rfl⟩ : syracuseStep 4955377 = 3716533) B3716533
theorem B1285379 : Blo 674311 1285379 := bstep (se 1 (by rfl) ⟨964034, by rfl⟩ : syracuseStep 1285379 = 1928069) B1928069
theorem B761107 : Blo 674311 761107 := bstep (se 1 (by rfl) ⟨570830, by rfl⟩ : syracuseStep 761107 = 1141661) B1141661
theorem B761251 : Blo 674311 761251 := bstep (se 1 (by rfl) ⟨570938, by rfl⟩ : syracuseStep 761251 = 1141877) B1141877
theorem B1220035 : Blo 674311 1220035 := bstep (se 1 (by rfl) ⟨915026, by rfl⟩ : syracuseStep 1220035 = 1830053) B1830053
theorem B1711601 : Blo 674311 1711601 := bstep (se 2 (by rfl) ⟨641850, by rfl⟩ : syracuseStep 1711601 = 1283701) B1283701
theorem B2170385 : Blo 674311 2170385 := bstep (se 2 (by rfl) ⟨813894, by rfl⟩ : syracuseStep 2170385 = 1627789) B1627789
theorem B1711651 : Blo 674311 1711651 := bstep (se 1 (by rfl) ⟨1283738, by rfl⟩ : syracuseStep 1711651 = 2567477) B2567477
theorem B761395 : Blo 674311 761395 := bstep (se 1 (by rfl) ⟨571046, by rfl⟩ : syracuseStep 761395 = 1142093) B1142093
theorem B1711793 : Blo 674311 1711793 := bstep (se 2 (by rfl) ⟨641922, by rfl⟩ : syracuseStep 1711793 = 1283845) B1283845
theorem B761539 : Blo 674311 761539 := bstep (se 1 (by rfl) ⟨571154, by rfl⟩ : syracuseStep 761539 = 1142309) B1142309
theorem B761683 : Blo 674311 761683 := bstep (se 1 (by rfl) ⟨571262, by rfl⟩ : syracuseStep 761683 = 1142525) B1142525
theorem B2564045 : Blo 674311 2564045 := bstep (se 3 (by rfl) ⟨480758, by rfl⟩ : syracuseStep 2564045 = 961517) B961517
theorem B761827 : Blo 674311 761827 := bstep (se 1 (by rfl) ⟨571370, by rfl⟩ : syracuseStep 761827 = 1142741) B1142741
theorem B761971 : Blo 674311 761971 := bstep (se 1 (by rfl) ⟨571478, by rfl⟩ : syracuseStep 761971 = 1142957) B1142957
theorem B1286275 : Blo 674311 1286275 := bstep (se 1 (by rfl) ⟨964706, by rfl⟩ : syracuseStep 1286275 = 1929413) B1929413
theorem B5218445 : Blo 674311 5218445 := bstep (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) B1956917
theorem B762115 : Blo 674311 762115 := bstep (se 1 (by rfl) ⟨571586, by rfl⟩ : syracuseStep 762115 = 1143173) B1143173
theorem B1286435 : Blo 674311 1286435 := bstep (se 1 (by rfl) ⟨964826, by rfl⟩ : syracuseStep 1286435 = 1929653) B1929653
theorem B2171281 : Blo 674311 2171281 := bstep (se 2 (by rfl) ⟨814230, by rfl⟩ : syracuseStep 2171281 = 1628461) B1628461
theorem B762259 : Blo 674311 762259 := bstep (se 1 (by rfl) ⟨571694, by rfl⟩ : syracuseStep 762259 = 1143389) B1143389
theorem B762403 : Blo 674311 762403 := bstep (se 1 (by rfl) ⟨571802, by rfl⟩ : syracuseStep 762403 = 1143605) B1143605
theorem B1712785 : Blo 674311 1712785 := bstep (se 2 (by rfl) ⟨642294, by rfl⟩ : syracuseStep 1712785 = 1284589) B1284589
theorem B762547 : Blo 674311 762547 := bstep (se 1 (by rfl) ⟨571910, by rfl⟩ : syracuseStep 762547 = 1143821) B1143821
theorem B6497009 : Blo 674311 6497009 := bstep (se 2 (by rfl) ⟨2436378, by rfl⟩ : syracuseStep 6497009 = 4872757) B4872757
theorem B762691 : Blo 674311 762691 := bstep (se 1 (by rfl) ⟨572018, by rfl⟩ : syracuseStep 762691 = 1144037) B1144037
theorem B1713059 : Blo 674311 1713059 := bstep (se 1 (by rfl) ⟨1284794, by rfl⟩ : syracuseStep 1713059 = 2569589) B2569589
theorem B7316405 : Blo 674311 7316405 := bstep (se 5 (by rfl) ⟨342956, by rfl⟩ : syracuseStep 7316405 = 685913) B685913
theorem B1221571 : Blo 674311 1221571 := bstep (se 1 (by rfl) ⟨916178, by rfl⟩ : syracuseStep 1221571 = 1832357) B1832357
theorem B762835 : Blo 674311 762835 := bstep (se 1 (by rfl) ⟨572126, by rfl⟩ : syracuseStep 762835 = 1144253) B1144253
theorem B1221635 : Blo 674311 1221635 := bstep (se 1 (by rfl) ⟨916226, by rfl⟩ : syracuseStep 1221635 = 1832453) B1832453
theorem B1713251 : Blo 674311 1713251 := bstep (se 1 (by rfl) ⟨1284938, by rfl⟩ : syracuseStep 1713251 = 2569877) B2569877
theorem B762979 : Blo 674311 762979 := bstep (se 1 (by rfl) ⟨572234, by rfl⟩ : syracuseStep 762979 = 1144469) B1144469
theorem B1287505 : Blo 674311 1287505 := bstep (se 2 (by rfl) ⟨482814, by rfl⟩ : syracuseStep 1287505 = 965629) B965629
theorem B2467313 : Blo 674311 2467313 := bstep (se 2 (by rfl) ⟨925242, by rfl⟩ : syracuseStep 2467313 = 1850485) B1850485
theorem B3417713 : Blo 674311 3417713 := bstep (se 2 (by rfl) ⟨1281642, by rfl⟩ : syracuseStep 3417713 = 2563285) B2563285
theorem B6006413 : Blo 674311 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B1517201 : Blo 674311 1517201 := bstep (se 2 (by rfl) ⟨568950, by rfl⟩ : syracuseStep 1517201 = 1137901) B1137901
theorem B1517219 : Blo 674311 1517219 := bstep (se 1 (by rfl) ⟨1137914, by rfl⟩ : syracuseStep 1517219 = 2275829) B2275829
theorem B1976035 : Blo 674311 1976035 := bstep (se 1 (by rfl) ⟨1482026, by rfl⟩ : syracuseStep 1976035 = 2964053) B2964053
theorem B2172845 : Blo 674311 2172845 := bstep (se 3 (by rfl) ⟨407408, by rfl⟩ : syracuseStep 2172845 = 814817) B814817
theorem B1517489 : Blo 674311 1517489 := bstep (se 2 (by rfl) ⟨569058, by rfl⟩ : syracuseStep 1517489 = 1138117) B1138117
theorem B1517507 : Blo 674311 1517507 := bstep (se 1 (by rfl) ⟨1138130, by rfl⟩ : syracuseStep 1517507 = 2276261) B2276261
theorem B1714193 : Blo 674311 1714193 := bstep (se 2 (by rfl) ⟨642822, by rfl⟩ : syracuseStep 1714193 = 1285645) B1285645
theorem B1714243 : Blo 674311 1714243 := bstep (se 1 (by rfl) ⟨1285682, by rfl⟩ : syracuseStep 1714243 = 2571365) B2571365
theorem B5482565 : Blo 674311 5482565 := bstep (se 4 (by rfl) ⟨513990, by rfl⟩ : syracuseStep 5482565 = 1027981) B1027981
theorem B5777507 : Blo 674311 5777507 := bstep (se 1 (by rfl) ⟨4333130, by rfl⟩ : syracuseStep 5777507 = 8666261) B8666261
theorem B1026193 : Blo 674311 1026193 := bstep (se 2 (by rfl) ⟨384822, by rfl⟩ : syracuseStep 1026193 = 769645) B769645
theorem B1517777 : Blo 674311 1517777 := bstep (se 2 (by rfl) ⟨569166, by rfl⟩ : syracuseStep 1517777 = 1138333) B1138333
theorem B1714385 : Blo 674311 1714385 := bstep (se 2 (by rfl) ⟨642894, by rfl⟩ : syracuseStep 1714385 = 1285789) B1285789
theorem B1517795 : Blo 674311 1517795 := bstep (se 1 (by rfl) ⟨1138346, by rfl⟩ : syracuseStep 1517795 = 2276693) B2276693
theorem B1157411 : Blo 674311 1157411 := bstep (se 1 (by rfl) ⟨868058, by rfl⟩ : syracuseStep 1157411 = 1736117) B1736117
theorem B960817 : Blo 674311 960817 := bstep (se 2 (by rfl) ⟨360306, by rfl⟩ : syracuseStep 960817 = 720613) B720613
theorem B1026353 : Blo 674311 1026353 := bstep (se 2 (by rfl) ⟨384882, by rfl⟩ : syracuseStep 1026353 = 769765) B769765
theorem B2926925 : Blo 674311 2926925 := bstep (se 3 (by rfl) ⟨548798, by rfl⟩ : syracuseStep 2926925 = 1097597) B1097597
theorem B2894221 : Blo 674311 2894221 := bstep (se 3 (by rfl) ⟨542666, by rfl⟩ : syracuseStep 2894221 = 1085333) B1085333
theorem B960913 : Blo 674311 960913 := bstep (se 2 (by rfl) ⟨360342, by rfl⟩ : syracuseStep 960913 = 720685) B720685
theorem B1518065 : Blo 674311 1518065 := bstep (se 2 (by rfl) ⟨569274, by rfl⟩ : syracuseStep 1518065 = 1138549) B1138549
theorem B1518083 : Blo 674311 1518083 := bstep (se 1 (by rfl) ⟨1138562, by rfl⟩ : syracuseStep 1518083 = 2277125) B2277125
theorem B1518353 : Blo 674311 1518353 := bstep (se 2 (by rfl) ⟨569382, by rfl⟩ : syracuseStep 1518353 = 1138765) B1138765
theorem B1518371 : Blo 674311 1518371 := bstep (se 1 (by rfl) ⟨1138778, by rfl⟩ : syracuseStep 1518371 = 2277557) B2277557
theorem B2566961 : Blo 674311 2566961 := bstep (se 2 (by rfl) ⟨962610, by rfl⟩ : syracuseStep 2566961 = 1925221) B1925221
theorem B1157971 : Blo 674311 1157971 := bstep (se 1 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 1157971 = 1736957) B1736957
theorem B961409 : Blo 674311 961409 := bstep (se 2 (by rfl) ⟨360528, by rfl⟩ : syracuseStep 961409 = 721057) B721057
theorem B3419171 : Blo 674311 3419171 := bstep (se 1 (by rfl) ⟨2564378, by rfl⟩ : syracuseStep 3419171 = 5128757) B5128757
theorem B1518641 : Blo 674311 1518641 := bstep (se 2 (by rfl) ⟨569490, by rfl⟩ : syracuseStep 1518641 = 1138981) B1138981
theorem B1518659 : Blo 674311 1518659 := bstep (se 1 (by rfl) ⟨1138994, by rfl⟩ : syracuseStep 1518659 = 2277989) B2277989
theorem B46967921 : Blo 674311 46967921 := bstep (se 2 (by rfl) ⟨17612970, by rfl⟩ : syracuseStep 46967921 = 35225941) B35225941
theorem B1715377 : Blo 674311 1715377 := bstep (se 2 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 1715377 = 1286533) B1286533
theorem B732371 : Blo 674311 732371 := bstep (se 1 (by rfl) ⟨549278, by rfl⟩ : syracuseStep 732371 = 1098557) B1098557
theorem B1518929 : Blo 674311 1518929 := bstep (se 2 (by rfl) ⟨569598, by rfl⟩ : syracuseStep 1518929 = 1139197) B1139197
theorem B1518947 : Blo 674311 1518947 := bstep (se 1 (by rfl) ⟨1139210, by rfl⟩ : syracuseStep 1518947 = 2278421) B2278421
theorem B2108849 : Blo 674311 2108849 := bstep (se 2 (by rfl) ⟨790818, by rfl⟩ : syracuseStep 2108849 = 1581637) B1581637
theorem B1715651 : Blo 674311 1715651 := bstep (se 1 (by rfl) ⟨1286738, by rfl⟩ : syracuseStep 1715651 = 2573477) B2573477
theorem B1519217 : Blo 674311 1519217 := bstep (se 2 (by rfl) ⟨569706, by rfl⟩ : syracuseStep 1519217 = 1139413) B1139413
theorem B1519235 : Blo 674311 1519235 := bstep (se 1 (by rfl) ⟨1139426, by rfl⟩ : syracuseStep 1519235 = 2278853) B2278853
theorem B1715843 : Blo 674311 1715843 := bstep (se 1 (by rfl) ⟨1286882, by rfl⟩ : syracuseStep 1715843 = 2573765) B2573765
theorem B962275 : Blo 674311 962275 := bstep (se 1 (by rfl) ⟨721706, by rfl⟩ : syracuseStep 962275 = 1443413) B1443413
theorem B962371 : Blo 674311 962371 := bstep (se 1 (by rfl) ⟨721778, by rfl⟩ : syracuseStep 962371 = 1443557) B1443557
theorem B3419981 : Blo 674311 3419981 := bstep (se 3 (by rfl) ⟨641246, by rfl⟩ : syracuseStep 3419981 = 1282493) B1282493
theorem B1519505 : Blo 674311 1519505 := bstep (se 2 (by rfl) ⟨569814, by rfl⟩ : syracuseStep 1519505 = 1139629) B1139629
theorem B1519523 : Blo 674311 1519523 := bstep (se 1 (by rfl) ⟨1139642, by rfl⟩ : syracuseStep 1519523 = 2279285) B2279285
theorem B3092593 : Blo 674311 3092593 := bstep (se 2 (by rfl) ⟨1159722, by rfl⟩ : syracuseStep 3092593 = 2319445) B2319445
theorem B4108421 : Blo 674311 4108421 := bstep (se 4 (by rfl) ⟨385164, by rfl⟩ : syracuseStep 4108421 = 770329) B770329
theorem B1519793 : Blo 674311 1519793 := bstep (se 2 (by rfl) ⟨569922, by rfl⟩ : syracuseStep 1519793 = 1139845) B1139845
theorem B1519811 : Blo 674311 1519811 := bstep (se 1 (by rfl) ⟨1139858, by rfl⟩ : syracuseStep 1519811 = 2279717) B2279717
theorem B2568419 : Blo 674311 2568419 := bstep (se 1 (by rfl) ⟨1926314, by rfl⟩ : syracuseStep 2568419 = 3852629) B3852629
theorem B962867 : Blo 674311 962867 := bstep (se 1 (by rfl) ⟨722150, by rfl⟩ : syracuseStep 962867 = 1444301) B1444301
theorem B1520081 : Blo 674311 1520081 := bstep (se 2 (by rfl) ⟨570030, by rfl⟩ : syracuseStep 1520081 = 1140061) B1140061
theorem B1520099 : Blo 674311 1520099 := bstep (se 1 (by rfl) ⟨1140074, by rfl⟩ : syracuseStep 1520099 = 2280149) B2280149
theorem B1028627 : Blo 674311 1028627 := bstep (se 1 (by rfl) ⟨771470, by rfl⟩ : syracuseStep 1028627 = 1542941) B1542941
theorem B1716785 : Blo 674311 1716785 := bstep (se 2 (by rfl) ⟨643794, by rfl⟩ : syracuseStep 1716785 = 1287589) B1287589
theorem B1716835 : Blo 674311 1716835 := bstep (se 1 (by rfl) ⟨1287626, by rfl⟩ : syracuseStep 1716835 = 2575253) B2575253
theorem B3846797 : Blo 674311 3846797 := bstep (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) B1442549
theorem B1028803 : Blo 674311 1028803 := bstep (se 1 (by rfl) ⟨771602, by rfl⟩ : syracuseStep 1028803 = 1543205) B1543205
theorem B1520369 : Blo 674311 1520369 := bstep (se 2 (by rfl) ⟨570138, by rfl⟩ : syracuseStep 1520369 = 1140277) B1140277
theorem B1716977 : Blo 674311 1716977 := bstep (se 2 (by rfl) ⟨643866, by rfl⟩ : syracuseStep 1716977 = 1287733) B1287733
theorem B1520387 : Blo 674311 1520387 := bstep (se 1 (by rfl) ⟨1140290, by rfl⟩ : syracuseStep 1520387 = 2280581) B2280581
theorem B963505 : Blo 674311 963505 := bstep (se 2 (by rfl) ⟨361314, by rfl⟩ : syracuseStep 963505 = 722629) B722629
theorem B1520657 : Blo 674311 1520657 := bstep (se 2 (by rfl) ⟨570246, by rfl⟩ : syracuseStep 1520657 = 1140493) B1140493
theorem B1520675 : Blo 674311 1520675 := bstep (se 1 (by rfl) ⟨1140506, by rfl⟩ : syracuseStep 1520675 = 2281013) B2281013
theorem B1946755 : Blo 674311 1946755 := bstep (se 1 (by rfl) ⟨1460066, by rfl⟩ : syracuseStep 1946755 = 2920133) B2920133
theorem B2569421 : Blo 674311 2569421 := bstep (se 3 (by rfl) ⟨481766, by rfl⟩ : syracuseStep 2569421 = 963533) B963533
theorem B963841 : Blo 674311 963841 := bstep (se 2 (by rfl) ⟨361440, by rfl⟩ : syracuseStep 963841 = 722881) B722881
theorem B1520945 : Blo 674311 1520945 := bstep (se 2 (by rfl) ⟨570354, by rfl⟩ : syracuseStep 1520945 = 1140709) B1140709
theorem B1520963 : Blo 674311 1520963 := bstep (se 1 (by rfl) ⟨1140722, by rfl⟩ : syracuseStep 1520963 = 2281445) B2281445
theorem B1521233 : Blo 674311 1521233 := bstep (se 2 (by rfl) ⟨570462, by rfl⟩ : syracuseStep 1521233 = 1140925) B1140925
theorem B1521251 : Blo 674311 1521251 := bstep (se 1 (by rfl) ⟨1140938, by rfl⟩ : syracuseStep 1521251 = 2281877) B2281877
theorem B1128179 : Blo 674311 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B6502157 : Blo 674311 6502157 := bstep (se 3 (by rfl) ⟨1219154, by rfl⟩ : syracuseStep 6502157 = 2438309) B2438309
theorem B964433 : Blo 674311 964433 := bstep (se 2 (by rfl) ⟨361662, by rfl⟩ : syracuseStep 964433 = 723325) B723325
theorem B1029971 : Blo 674311 1029971 := bstep (se 1 (by rfl) ⟨772478, by rfl⟩ : syracuseStep 1029971 = 1544957) B1544957
theorem B2307953 : Blo 674311 2307953 := bstep (se 2 (by rfl) ⟨865482, by rfl⟩ : syracuseStep 2307953 = 1730965) B1730965
theorem B1521521 : Blo 674311 1521521 := bstep (se 2 (by rfl) ⟨570570, by rfl⟩ : syracuseStep 1521521 = 1141141) B1141141
theorem B1521539 : Blo 674311 1521539 := bstep (se 1 (by rfl) ⟨1141154, by rfl⟩ : syracuseStep 1521539 = 2282309) B2282309
theorem B9254897 : Blo 674311 9254897 := bstep (se 2 (by rfl) ⟨3470586, by rfl⟩ : syracuseStep 9254897 = 6941173) B6941173
theorem B1521809 : Blo 674311 1521809 := bstep (se 2 (by rfl) ⟨570678, by rfl⟩ : syracuseStep 1521809 = 1141357) B1141357
theorem B1521827 : Blo 674311 1521827 := bstep (se 1 (by rfl) ⟨1141370, by rfl⟩ : syracuseStep 1521827 = 2282741) B2282741
theorem B964963 : Blo 674311 964963 := bstep (se 1 (by rfl) ⟨723722, by rfl⟩ : syracuseStep 964963 = 1447445) B1447445
theorem B1522097 : Blo 674311 1522097 := bstep (se 2 (by rfl) ⟨570786, by rfl⟩ : syracuseStep 1522097 = 1141573) B1141573
theorem B1522115 : Blo 674311 1522115 := bstep (se 1 (by rfl) ⟨1141586, by rfl⟩ : syracuseStep 1522115 = 2283173) B2283173
theorem B1030705 : Blo 674311 1030705 := bstep (se 2 (by rfl) ⟨386514, by rfl⟩ : syracuseStep 1030705 = 773029) B773029
theorem B3652273 : Blo 674311 3652273 := bstep (se 2 (by rfl) ⟨1369602, by rfl⟩ : syracuseStep 3652273 = 2739205) B2739205
theorem B3422897 : Blo 674311 3422897 := bstep (se 2 (by rfl) ⟨1283586, by rfl⟩ : syracuseStep 3422897 = 2567173) B2567173
theorem B965299 : Blo 674311 965299 := bstep (se 1 (by rfl) ⟨723974, by rfl⟩ : syracuseStep 965299 = 1447949) B1447949
theorem B2276045 : Blo 674311 2276045 := bstep (se 3 (by rfl) ⟨426758, by rfl⟩ : syracuseStep 2276045 = 853517) B853517
theorem B1522385 : Blo 674311 1522385 := bstep (se 2 (by rfl) ⟨570894, by rfl⟩ : syracuseStep 1522385 = 1141789) B1141789
theorem B1522403 : Blo 674311 1522403 := bstep (se 1 (by rfl) ⟨1141802, by rfl⟩ : syracuseStep 1522403 = 2283605) B2283605
theorem B2276099 : Blo 674311 2276099 := bstep (se 1 (by rfl) ⟨1707074, by rfl⟩ : syracuseStep 2276099 = 3414149) B3414149
theorem B3849029 : Blo 674311 3849029 := bstep (se 4 (by rfl) ⟨360846, by rfl⟩ : syracuseStep 3849029 = 721693) B721693
theorem B3652451 : Blo 674311 3652451 := bstep (se 1 (by rfl) ⟨2739338, by rfl⟩ : syracuseStep 3652451 = 5478677) B5478677
theorem B1522673 : Blo 674311 1522673 := bstep (se 2 (by rfl) ⟨571002, by rfl⟩ : syracuseStep 1522673 = 1142005) B1142005
theorem B1522691 : Blo 674311 1522691 := bstep (se 1 (by rfl) ⟨1142018, by rfl⟩ : syracuseStep 1522691 = 2284037) B2284037
theorem B2276369 : Blo 674311 2276369 := bstep (se 2 (by rfl) ⟨853638, by rfl⟩ : syracuseStep 2276369 = 1707277) B1707277
theorem B1850435 : Blo 674311 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B3914851 : Blo 674311 3914851 := bstep (se 1 (by rfl) ⟨2936138, by rfl⟩ : syracuseStep 3914851 = 5872277) B5872277
theorem B1981649 : Blo 674311 1981649 := bstep (se 2 (by rfl) ⟨743118, by rfl⟩ : syracuseStep 1981649 = 1486237) B1486237
theorem B2571533 : Blo 674311 2571533 := bstep (se 3 (by rfl) ⟨482162, by rfl⟩ : syracuseStep 2571533 = 964325) B964325
theorem B1522961 : Blo 674311 1522961 := bstep (se 2 (by rfl) ⟨571110, by rfl⟩ : syracuseStep 1522961 = 1142221) B1142221
theorem B1522979 : Blo 674311 1522979 := bstep (se 1 (by rfl) ⟨1142234, by rfl⟩ : syracuseStep 1522979 = 2284469) B2284469
theorem B3849713 : Blo 674311 3849713 := bstep (se 2 (by rfl) ⟨1443642, by rfl⟩ : syracuseStep 3849713 = 2887285) B2887285
theorem B2276909 : Blo 674311 2276909 := bstep (se 3 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 2276909 = 853841) B853841
theorem B1523249 : Blo 674311 1523249 := bstep (se 2 (by rfl) ⟨571218, by rfl⟩ : syracuseStep 1523249 = 1142437) B1142437
theorem B1523267 : Blo 674311 1523267 := bstep (se 1 (by rfl) ⟨1142450, by rfl⟩ : syracuseStep 1523267 = 2284901) B2284901
theorem B2276963 : Blo 674311 2276963 := bstep (se 1 (by rfl) ⟨1707722, by rfl⟩ : syracuseStep 2276963 = 3415445) B3415445
theorem B2080561 : Blo 674311 2080561 := bstep (se 2 (by rfl) ⟨780210, by rfl⟩ : syracuseStep 2080561 = 1560421) B1560421
theorem B1523537 : Blo 674311 1523537 := bstep (se 2 (by rfl) ⟨571326, by rfl⟩ : syracuseStep 1523537 = 1142653) B1142653
theorem B1523555 : Blo 674311 1523555 := bstep (se 1 (by rfl) ⟨1142666, by rfl⟩ : syracuseStep 1523555 = 2285333) B2285333
theorem B2277233 : Blo 674311 2277233 := bstep (se 2 (by rfl) ⟨853962, by rfl⟩ : syracuseStep 2277233 = 1707925) B1707925
theorem B2441137 : Blo 674311 2441137 := bstep (se 2 (by rfl) ⟨915426, by rfl⟩ : syracuseStep 2441137 = 1830853) B1830853
theorem B2572337 : Blo 674311 2572337 := bstep (se 2 (by rfl) ⟨964626, by rfl⟩ : syracuseStep 2572337 = 1929253) B1929253
theorem B3424355 : Blo 674311 3424355 := bstep (se 1 (by rfl) ⟨2568266, by rfl⟩ : syracuseStep 3424355 = 5136533) B5136533
theorem B1523825 : Blo 674311 1523825 := bstep (se 2 (by rfl) ⟨571434, by rfl⟩ : syracuseStep 1523825 = 1142869) B1142869
theorem B1523843 : Blo 674311 1523843 := bstep (se 1 (by rfl) ⟨1142882, by rfl⟩ : syracuseStep 1523843 = 2285765) B2285765
theorem B2277773 : Blo 674311 2277773 := bstep (se 3 (by rfl) ⟨427082, by rfl⟩ : syracuseStep 2277773 = 854165) B854165
theorem B1524113 : Blo 674311 1524113 := bstep (se 2 (by rfl) ⟨571542, by rfl⟩ : syracuseStep 1524113 = 1143085) B1143085
theorem B1524131 : Blo 674311 1524131 := bstep (se 1 (by rfl) ⟨1143098, by rfl⟩ : syracuseStep 1524131 = 2286197) B2286197
theorem B2277827 : Blo 674311 2277827 := bstep (se 1 (by rfl) ⟨1708370, by rfl⟩ : syracuseStep 2277827 = 3416741) B3416741
theorem B1524401 : Blo 674311 1524401 := bstep (se 2 (by rfl) ⟨571650, by rfl⟩ : syracuseStep 1524401 = 1143301) B1143301
theorem B1524419 : Blo 674311 1524419 := bstep (se 1 (by rfl) ⟨1143314, by rfl⟩ : syracuseStep 1524419 = 2286629) B2286629
theorem B2573005 : Blo 674311 2573005 := bstep (se 3 (by rfl) ⟨482438, by rfl⟩ : syracuseStep 2573005 = 964877) B964877
theorem B2278097 : Blo 674311 2278097 := bstep (se 2 (by rfl) ⟨854286, by rfl⟩ : syracuseStep 2278097 = 1708573) B1708573
theorem B3425165 : Blo 674311 3425165 := bstep (se 3 (by rfl) ⟨642218, by rfl⟩ : syracuseStep 3425165 = 1284437) B1284437
theorem B3851171 : Blo 674311 3851171 := bstep (se 1 (by rfl) ⟨2888378, by rfl⟩ : syracuseStep 3851171 = 5776757) B5776757
theorem B1950637 : Blo 674311 1950637 := bstep (se 3 (by rfl) ⟨365744, by rfl⟩ : syracuseStep 1950637 = 731489) B731489
theorem B1524689 : Blo 674311 1524689 := bstep (se 2 (by rfl) ⟨571758, by rfl⟩ : syracuseStep 1524689 = 1143517) B1143517
theorem B1524707 : Blo 674311 1524707 := bstep (se 1 (by rfl) ⟨1143530, by rfl⟩ : syracuseStep 1524707 = 2287061) B2287061
theorem B771059 : Blo 674311 771059 := bstep (se 1 (by rfl) ⟨578294, by rfl⟩ : syracuseStep 771059 = 1156589) B1156589
theorem B6505541 : Blo 674311 6505541 := bstep (se 4 (by rfl) ⟨609894, by rfl⟩ : syracuseStep 6505541 = 1219789) B1219789
theorem B2278637 : Blo 674311 2278637 := bstep (se 3 (by rfl) ⟨427244, by rfl⟩ : syracuseStep 2278637 = 854489) B854489
theorem B1524977 : Blo 674311 1524977 := bstep (se 2 (by rfl) ⟨571866, by rfl⟩ : syracuseStep 1524977 = 1143733) B1143733
theorem B1524995 : Blo 674311 1524995 := bstep (se 1 (by rfl) ⟨1143746, by rfl⟩ : syracuseStep 1524995 = 2287493) B2287493
theorem B2278691 : Blo 674311 2278691 := bstep (se 1 (by rfl) ⟨1709018, by rfl⟩ : syracuseStep 2278691 = 3418037) B3418037
theorem B2573795 : Blo 674311 2573795 := bstep (se 1 (by rfl) ⟨1930346, by rfl⟩ : syracuseStep 2573795 = 3860693) B3860693
theorem B1525265 : Blo 674311 1525265 := bstep (se 2 (by rfl) ⟨571974, by rfl⟩ : syracuseStep 1525265 = 1143949) B1143949
theorem B1525283 : Blo 674311 1525283 := bstep (se 1 (by rfl) ⟨1143962, by rfl⟩ : syracuseStep 1525283 = 2287925) B2287925
theorem B2278961 : Blo 674311 2278961 := bstep (se 2 (by rfl) ⟨854610, by rfl⟩ : syracuseStep 2278961 = 1709221) B1709221
theorem B1525553 : Blo 674311 1525553 := bstep (se 2 (by rfl) ⟨572082, by rfl⟩ : syracuseStep 1525553 = 1144165) B1144165
theorem B1525571 : Blo 674311 1525571 := bstep (se 1 (by rfl) ⟨1144178, by rfl⟩ : syracuseStep 1525571 = 2288357) B2288357
theorem B2312081 : Blo 674311 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B2279501 : Blo 674311 2279501 := bstep (se 3 (by rfl) ⟨427406, by rfl⟩ : syracuseStep 2279501 = 854813) B854813
theorem B1525841 : Blo 674311 1525841 := bstep (se 2 (by rfl) ⟨572190, by rfl⟩ : syracuseStep 1525841 = 1144381) B1144381
theorem B1525859 : Blo 674311 1525859 := bstep (se 1 (by rfl) ⟨1144394, by rfl⟩ : syracuseStep 1525859 = 2288789) B2288789
theorem B2574449 : Blo 674311 2574449 := bstep (se 2 (by rfl) ⟨965418, by rfl⟩ : syracuseStep 2574449 = 1930837) B1930837
theorem B2279555 : Blo 674311 2279555 := bstep (se 1 (by rfl) ⟨1709666, by rfl⟩ : syracuseStep 2279555 = 3419333) B3419333
theorem B2312333 : Blo 674311 2312333 := bstep (se 3 (by rfl) ⟨433562, by rfl⟩ : syracuseStep 2312333 = 867125) B867125
theorem B1853585 : Blo 674311 1853585 := bstep (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) B1390189
theorem B1624387 : Blo 674311 1624387 := bstep (se 1 (by rfl) ⟨1218290, by rfl⟩ : syracuseStep 1624387 = 2436581) B2436581
theorem B1526129 : Blo 674311 1526129 := bstep (se 2 (by rfl) ⟨572298, by rfl⟩ : syracuseStep 1526129 = 1144597) B1144597
theorem B1526147 : Blo 674311 1526147 := bstep (se 1 (by rfl) ⟨1144610, by rfl⟩ : syracuseStep 1526147 = 2289221) B2289221
theorem B2279825 : Blo 674311 2279825 := bstep (se 2 (by rfl) ⟨854934, by rfl⟩ : syracuseStep 2279825 = 1709869) B1709869
theorem B674323 : Blo 674311 674323 := bstep (se 1 (by rfl) ⟨505742, by rfl⟩ : syracuseStep 674323 = 1011485) B1011485
theorem B674339 : Blo 674311 674339 := bstep (se 1 (by rfl) ⟨505754, by rfl⟩ : syracuseStep 674339 = 1011509) B1011509
theorem B674355 : Blo 674311 674355 := bstep (se 1 (by rfl) ⟨505766, by rfl⟩ : syracuseStep 674355 = 1011533) B1011533
theorem B674371 : Blo 674311 674371 := bstep (se 1 (by rfl) ⟨505778, by rfl⟩ : syracuseStep 674371 = 1011557) B1011557
theorem B674387 : Blo 674311 674387 := bstep (se 1 (by rfl) ⟨505790, by rfl⟩ : syracuseStep 674387 = 1011581) B1011581
theorem B674403 : Blo 674311 674403 := bstep (se 1 (by rfl) ⟨505802, by rfl⟩ : syracuseStep 674403 = 1011605) B1011605
theorem B674419 : Blo 674311 674419 := bstep (se 1 (by rfl) ⟨505814, by rfl⟩ : syracuseStep 674419 = 1011629) B1011629
theorem B674435 : Blo 674311 674435 := bstep (se 1 (by rfl) ⟨505826, by rfl⟩ : syracuseStep 674435 = 1011653) B1011653
theorem B4344461 : Blo 674311 4344461 := bstep (se 3 (by rfl) ⟨814586, by rfl⟩ : syracuseStep 4344461 = 1629173) B1629173
theorem B674451 : Blo 674311 674451 := bstep (se 1 (by rfl) ⟨505838, by rfl⟩ : syracuseStep 674451 = 1011677) B1011677
theorem B674467 : Blo 674311 674467 := bstep (se 1 (by rfl) ⟨505850, by rfl⟩ : syracuseStep 674467 = 1011701) B1011701
theorem B674483 : Blo 674311 674483 := bstep (se 1 (by rfl) ⟨505862, by rfl⟩ : syracuseStep 674483 = 1011725) B1011725
theorem B674499 : Blo 674311 674499 := bstep (se 1 (by rfl) ⟨505874, by rfl⟩ : syracuseStep 674499 = 1011749) B1011749
theorem B674515 : Blo 674311 674515 := bstep (se 1 (by rfl) ⟨505886, by rfl⟩ : syracuseStep 674515 = 1011773) B1011773
theorem B674531 : Blo 674311 674531 := bstep (se 1 (by rfl) ⟨505898, by rfl⟩ : syracuseStep 674531 = 1011797) B1011797
theorem B674547 : Blo 674311 674547 := bstep (se 1 (by rfl) ⟨505910, by rfl⟩ : syracuseStep 674547 = 1011821) B1011821
theorem B674563 : Blo 674311 674563 := bstep (se 1 (by rfl) ⟨505922, by rfl⟩ : syracuseStep 674563 = 1011845) B1011845
theorem B674579 : Blo 674311 674579 := bstep (se 1 (by rfl) ⟨505934, by rfl⟩ : syracuseStep 674579 = 1011869) B1011869
theorem B42257173 : Blo 674311 42257173 := bstep (se 6 (by rfl) ⟨990402, by rfl⟩ : syracuseStep 42257173 = 1980805) B1980805
theorem B674595 : Blo 674311 674595 := bstep (se 1 (by rfl) ⟨505946, by rfl⟩ : syracuseStep 674595 = 1011893) B1011893
theorem B674611 : Blo 674311 674611 := bstep (se 1 (by rfl) ⟨505958, by rfl⟩ : syracuseStep 674611 = 1011917) B1011917
theorem B674627 : Blo 674311 674627 := bstep (se 1 (by rfl) ⟨505970, by rfl⟩ : syracuseStep 674627 = 1011941) B1011941
theorem B674643 : Blo 674311 674643 := bstep (se 1 (by rfl) ⟨505982, by rfl⟩ : syracuseStep 674643 = 1011965) B1011965
theorem B674659 : Blo 674311 674659 := bstep (se 1 (by rfl) ⟨505994, by rfl⟩ : syracuseStep 674659 = 1011989) B1011989
theorem B674675 : Blo 674311 674675 := bstep (se 1 (by rfl) ⟨506006, by rfl⟩ : syracuseStep 674675 = 1012013) B1012013
theorem B674691 : Blo 674311 674691 := bstep (se 1 (by rfl) ⟨506018, by rfl⟩ : syracuseStep 674691 = 1012037) B1012037
theorem B674707 : Blo 674311 674707 := bstep (se 1 (by rfl) ⟨506030, by rfl⟩ : syracuseStep 674707 = 1012061) B1012061
theorem B674723 : Blo 674311 674723 := bstep (se 1 (by rfl) ⟨506042, by rfl⟩ : syracuseStep 674723 = 1012085) B1012085
theorem B2280365 : Blo 674311 2280365 := bstep (se 3 (by rfl) ⟨427568, by rfl⟩ : syracuseStep 2280365 = 855137) B855137
theorem B674739 : Blo 674311 674739 := bstep (se 1 (by rfl) ⟨506054, by rfl⟩ : syracuseStep 674739 = 1012109) B1012109
theorem B674755 : Blo 674311 674755 := bstep (se 1 (by rfl) ⟨506066, by rfl⟩ : syracuseStep 674755 = 1012133) B1012133
theorem B674771 : Blo 674311 674771 := bstep (se 1 (by rfl) ⟨506078, by rfl⟩ : syracuseStep 674771 = 1012157) B1012157
theorem B674787 : Blo 674311 674787 := bstep (se 1 (by rfl) ⟨506090, by rfl⟩ : syracuseStep 674787 = 1012181) B1012181
theorem B2280419 : Blo 674311 2280419 := bstep (se 1 (by rfl) ⟨1710314, by rfl⟩ : syracuseStep 2280419 = 3420629) B3420629
theorem B674803 : Blo 674311 674803 := bstep (se 1 (by rfl) ⟨506102, by rfl⟩ : syracuseStep 674803 = 1012205) B1012205
theorem B674819 : Blo 674311 674819 := bstep (se 1 (by rfl) ⟨506114, by rfl⟩ : syracuseStep 674819 = 1012229) B1012229
theorem B674835 : Blo 674311 674835 := bstep (se 1 (by rfl) ⟨506126, by rfl⟩ : syracuseStep 674835 = 1012253) B1012253
theorem B674851 : Blo 674311 674851 := bstep (se 1 (by rfl) ⟨506138, by rfl⟩ : syracuseStep 674851 = 1012277) B1012277
theorem B674867 : Blo 674311 674867 := bstep (se 1 (by rfl) ⟨506150, by rfl⟩ : syracuseStep 674867 = 1012301) B1012301
theorem B674883 : Blo 674311 674883 := bstep (se 1 (by rfl) ⟨506162, by rfl⟩ : syracuseStep 674883 = 1012325) B1012325
theorem B674899 : Blo 674311 674899 := bstep (se 1 (by rfl) ⟨506174, by rfl⟩ : syracuseStep 674899 = 1012349) B1012349
theorem B674915 : Blo 674311 674915 := bstep (se 1 (by rfl) ⟨506186, by rfl⟩ : syracuseStep 674915 = 1012373) B1012373
theorem B674931 : Blo 674311 674931 := bstep (se 1 (by rfl) ⟨506198, by rfl⟩ : syracuseStep 674931 = 1012397) B1012397
theorem B674947 : Blo 674311 674947 := bstep (se 1 (by rfl) ⟨506210, by rfl⟩ : syracuseStep 674947 = 1012421) B1012421
theorem B674963 : Blo 674311 674963 := bstep (se 1 (by rfl) ⟨506222, by rfl⟩ : syracuseStep 674963 = 1012445) B1012445
theorem B773267 : Blo 674311 773267 := bstep (se 1 (by rfl) ⟨579950, by rfl⟩ : syracuseStep 773267 = 1159901) B1159901
theorem B674979 : Blo 674311 674979 := bstep (se 1 (by rfl) ⟨506234, by rfl⟩ : syracuseStep 674979 = 1012469) B1012469
theorem B674995 : Blo 674311 674995 := bstep (se 1 (by rfl) ⟨506246, by rfl⟩ : syracuseStep 674995 = 1012493) B1012493
theorem B675011 : Blo 674311 675011 := bstep (se 1 (by rfl) ⟨506258, by rfl⟩ : syracuseStep 675011 = 1012517) B1012517
theorem B2051281 : Blo 674311 2051281 := bstep (se 2 (by rfl) ⟨769230, by rfl⟩ : syracuseStep 2051281 = 1538461) B1538461
theorem B675027 : Blo 674311 675027 := bstep (se 1 (by rfl) ⟨506270, by rfl⟩ : syracuseStep 675027 = 1012541) B1012541
theorem B675043 : Blo 674311 675043 := bstep (se 1 (by rfl) ⟨506282, by rfl⟩ : syracuseStep 675043 = 1012565) B1012565
theorem B2280689 : Blo 674311 2280689 := bstep (se 2 (by rfl) ⟨855258, by rfl⟩ : syracuseStep 2280689 = 1710517) B1710517
theorem B675059 : Blo 674311 675059 := bstep (se 1 (by rfl) ⟨506294, by rfl⟩ : syracuseStep 675059 = 1012589) B1012589
theorem B675075 : Blo 674311 675075 := bstep (se 1 (by rfl) ⟨506306, by rfl⟩ : syracuseStep 675075 = 1012613) B1012613
theorem B675091 : Blo 674311 675091 := bstep (se 1 (by rfl) ⟨506318, by rfl⟩ : syracuseStep 675091 = 1012637) B1012637
theorem B675107 : Blo 674311 675107 := bstep (se 1 (by rfl) ⟨506330, by rfl⟩ : syracuseStep 675107 = 1012661) B1012661
theorem B675123 : Blo 674311 675123 := bstep (se 1 (by rfl) ⟨506342, by rfl⟩ : syracuseStep 675123 = 1012685) B1012685
theorem B1920323 : Blo 674311 1920323 := bstep (se 1 (by rfl) ⟨1440242, by rfl⟩ : syracuseStep 1920323 = 2880485) B2880485
theorem B675139 : Blo 674311 675139 := bstep (se 1 (by rfl) ⟨506354, by rfl⟩ : syracuseStep 675139 = 1012709) B1012709
theorem B675155 : Blo 674311 675155 := bstep (se 1 (by rfl) ⟨506366, by rfl⟩ : syracuseStep 675155 = 1012733) B1012733
theorem B675171 : Blo 674311 675171 := bstep (se 1 (by rfl) ⟨506378, by rfl⟩ : syracuseStep 675171 = 1012757) B1012757
theorem B2477411 : Blo 674311 2477411 := bstep (se 1 (by rfl) ⟨1858058, by rfl⟩ : syracuseStep 2477411 = 3716117) B3716117
theorem B675187 : Blo 674311 675187 := bstep (se 1 (by rfl) ⟨506390, by rfl⟩ : syracuseStep 675187 = 1012781) B1012781
theorem B675203 : Blo 674311 675203 := bstep (se 1 (by rfl) ⟨506402, by rfl⟩ : syracuseStep 675203 = 1012805) B1012805
theorem B675219 : Blo 674311 675219 := bstep (se 1 (by rfl) ⟨506414, by rfl⟩ : syracuseStep 675219 = 1012829) B1012829
theorem B675235 : Blo 674311 675235 := bstep (se 1 (by rfl) ⟨506426, by rfl⟩ : syracuseStep 675235 = 1012853) B1012853
theorem B675251 : Blo 674311 675251 := bstep (se 1 (by rfl) ⟨506438, by rfl⟩ : syracuseStep 675251 = 1012877) B1012877
theorem B675267 : Blo 674311 675267 := bstep (se 1 (by rfl) ⟨506450, by rfl⟩ : syracuseStep 675267 = 1012901) B1012901
theorem B675283 : Blo 674311 675283 := bstep (se 1 (by rfl) ⟨506462, by rfl⟩ : syracuseStep 675283 = 1012925) B1012925
theorem B675299 : Blo 674311 675299 := bstep (se 1 (by rfl) ⟨506474, by rfl⟩ : syracuseStep 675299 = 1012949) B1012949
theorem B675315 : Blo 674311 675315 := bstep (se 1 (by rfl) ⟨506486, by rfl⟩ : syracuseStep 675315 = 1012973) B1012973
theorem B675331 : Blo 674311 675331 := bstep (se 1 (by rfl) ⟨506498, by rfl⟩ : syracuseStep 675331 = 1012997) B1012997
theorem B675347 : Blo 674311 675347 := bstep (se 1 (by rfl) ⟨506510, by rfl⟩ : syracuseStep 675347 = 1013021) B1013021
theorem B675363 : Blo 674311 675363 := bstep (se 1 (by rfl) ⟨506522, by rfl⟩ : syracuseStep 675363 = 1013045) B1013045
theorem B1756721 : Blo 674311 1756721 := bstep (se 2 (by rfl) ⟨658770, by rfl⟩ : syracuseStep 1756721 = 1317541) B1317541
theorem B675379 : Blo 674311 675379 := bstep (se 1 (by rfl) ⟨506534, by rfl⟩ : syracuseStep 675379 = 1013069) B1013069
theorem B675395 : Blo 674311 675395 := bstep (se 1 (by rfl) ⟨506546, by rfl⟩ : syracuseStep 675395 = 1013093) B1013093
theorem B675411 : Blo 674311 675411 := bstep (se 1 (by rfl) ⟨506558, by rfl⟩ : syracuseStep 675411 = 1013117) B1013117
theorem B675427 : Blo 674311 675427 := bstep (se 1 (by rfl) ⟨506570, by rfl⟩ : syracuseStep 675427 = 1013141) B1013141
theorem B2379377 : Blo 674311 2379377 := bstep (se 2 (by rfl) ⟨892266, by rfl⟩ : syracuseStep 2379377 = 1784533) B1784533
theorem B675443 : Blo 674311 675443 := bstep (se 1 (by rfl) ⟨506582, by rfl⟩ : syracuseStep 675443 = 1013165) B1013165
theorem B675459 : Blo 674311 675459 := bstep (se 1 (by rfl) ⟨506594, by rfl⟩ : syracuseStep 675459 = 1013189) B1013189
theorem B675475 : Blo 674311 675475 := bstep (se 1 (by rfl) ⟨506606, by rfl⟩ : syracuseStep 675475 = 1013213) B1013213
theorem B675491 : Blo 674311 675491 := bstep (se 1 (by rfl) ⟨506618, by rfl⟩ : syracuseStep 675491 = 1013237) B1013237
theorem B675507 : Blo 674311 675507 := bstep (se 1 (by rfl) ⟨506630, by rfl⟩ : syracuseStep 675507 = 1013261) B1013261
theorem B675523 : Blo 674311 675523 := bstep (se 1 (by rfl) ⟨506642, by rfl⟩ : syracuseStep 675523 = 1013285) B1013285
theorem B675539 : Blo 674311 675539 := bstep (se 1 (by rfl) ⟨506654, by rfl⟩ : syracuseStep 675539 = 1013309) B1013309
theorem B675555 : Blo 674311 675555 := bstep (se 1 (by rfl) ⟨506666, by rfl⟩ : syracuseStep 675555 = 1013333) B1013333
theorem B1855217 : Blo 674311 1855217 := bstep (se 2 (by rfl) ⟨695706, by rfl⟩ : syracuseStep 1855217 = 1391413) B1391413
theorem B3428081 : Blo 674311 3428081 := bstep (se 2 (by rfl) ⟨1285530, by rfl⟩ : syracuseStep 3428081 = 2571061) B2571061
theorem B675571 : Blo 674311 675571 := bstep (se 1 (by rfl) ⟨506678, by rfl⟩ : syracuseStep 675571 = 1013357) B1013357
theorem B675587 : Blo 674311 675587 := bstep (se 1 (by rfl) ⟨506690, by rfl⟩ : syracuseStep 675587 = 1013381) B1013381
theorem B2281229 : Blo 674311 2281229 := bstep (se 3 (by rfl) ⟨427730, by rfl⟩ : syracuseStep 2281229 = 855461) B855461
theorem B675603 : Blo 674311 675603 := bstep (se 1 (by rfl) ⟨506702, by rfl⟩ : syracuseStep 675603 = 1013405) B1013405
theorem B675619 : Blo 674311 675619 := bstep (se 1 (by rfl) ⟨506714, by rfl⟩ : syracuseStep 675619 = 1013429) B1013429
theorem B675635 : Blo 674311 675635 := bstep (se 1 (by rfl) ⟨506726, by rfl⟩ : syracuseStep 675635 = 1013453) B1013453
theorem B675651 : Blo 674311 675651 := bstep (se 1 (by rfl) ⟨506738, by rfl⟩ : syracuseStep 675651 = 1013477) B1013477
theorem B2281283 : Blo 674311 2281283 := bstep (se 1 (by rfl) ⟨1710962, by rfl⟩ : syracuseStep 2281283 = 3421925) B3421925
theorem B675667 : Blo 674311 675667 := bstep (se 1 (by rfl) ⟨506750, by rfl⟩ : syracuseStep 675667 = 1013501) B1013501
theorem B675683 : Blo 674311 675683 := bstep (se 1 (by rfl) ⟨506762, by rfl⟩ : syracuseStep 675683 = 1013525) B1013525
theorem B675699 : Blo 674311 675699 := bstep (se 1 (by rfl) ⟨506774, by rfl⟩ : syracuseStep 675699 = 1013549) B1013549
theorem B675715 : Blo 674311 675715 := bstep (se 1 (by rfl) ⟨506786, by rfl⟩ : syracuseStep 675715 = 1013573) B1013573
theorem B675731 : Blo 674311 675731 := bstep (se 1 (by rfl) ⟨506798, by rfl⟩ : syracuseStep 675731 = 1013597) B1013597
theorem B675747 : Blo 674311 675747 := bstep (se 1 (by rfl) ⟨506810, by rfl⟩ : syracuseStep 675747 = 1013621) B1013621
theorem B675763 : Blo 674311 675763 := bstep (se 1 (by rfl) ⟨506822, by rfl⟩ : syracuseStep 675763 = 1013645) B1013645
theorem B675779 : Blo 674311 675779 := bstep (se 1 (by rfl) ⟨506834, by rfl⟩ : syracuseStep 675779 = 1013669) B1013669
theorem B675795 : Blo 674311 675795 := bstep (se 1 (by rfl) ⟨506846, by rfl⟩ : syracuseStep 675795 = 1013693) B1013693
theorem B675811 : Blo 674311 675811 := bstep (se 1 (by rfl) ⟨506858, by rfl⟩ : syracuseStep 675811 = 1013717) B1013717
theorem B675827 : Blo 674311 675827 := bstep (se 1 (by rfl) ⟨506870, by rfl⟩ : syracuseStep 675827 = 1013741) B1013741
theorem B675843 : Blo 674311 675843 := bstep (se 1 (by rfl) ⟨506882, by rfl⟩ : syracuseStep 675843 = 1013765) B1013765
theorem B675859 : Blo 674311 675859 := bstep (se 1 (by rfl) ⟨506894, by rfl⟩ : syracuseStep 675859 = 1013789) B1013789
theorem B675875 : Blo 674311 675875 := bstep (se 1 (by rfl) ⟨506906, by rfl⟩ : syracuseStep 675875 = 1013813) B1013813
theorem B675891 : Blo 674311 675891 := bstep (se 1 (by rfl) ⟨506918, by rfl⟩ : syracuseStep 675891 = 1013837) B1013837
theorem B675907 : Blo 674311 675907 := bstep (se 1 (by rfl) ⟨506930, by rfl⟩ : syracuseStep 675907 = 1013861) B1013861
theorem B3854405 : Blo 674311 3854405 := bstep (se 4 (by rfl) ⟨361350, by rfl⟩ : syracuseStep 3854405 = 722701) B722701
theorem B2281553 : Blo 674311 2281553 := bstep (se 2 (by rfl) ⟨855582, by rfl⟩ : syracuseStep 2281553 = 1711165) B1711165
theorem B675923 : Blo 674311 675923 := bstep (se 1 (by rfl) ⟨506942, by rfl⟩ : syracuseStep 675923 = 1013885) B1013885
theorem B675939 : Blo 674311 675939 := bstep (se 1 (by rfl) ⟨506954, by rfl⟩ : syracuseStep 675939 = 1013909) B1013909
theorem B675955 : Blo 674311 675955 := bstep (se 1 (by rfl) ⟨506966, by rfl⟩ : syracuseStep 675955 = 1013933) B1013933
theorem B675971 : Blo 674311 675971 := bstep (se 1 (by rfl) ⟨506978, by rfl⟩ : syracuseStep 675971 = 1013957) B1013957
theorem B675987 : Blo 674311 675987 := bstep (se 1 (by rfl) ⟨506990, by rfl⟩ : syracuseStep 675987 = 1013981) B1013981
theorem B676003 : Blo 674311 676003 := bstep (se 1 (by rfl) ⟨507002, by rfl⟩ : syracuseStep 676003 = 1014005) B1014005
theorem B676019 : Blo 674311 676019 := bstep (se 1 (by rfl) ⟨507014, by rfl⟩ : syracuseStep 676019 = 1014029) B1014029
theorem B676035 : Blo 674311 676035 := bstep (se 1 (by rfl) ⟨507026, by rfl⟩ : syracuseStep 676035 = 1014053) B1014053
theorem B676051 : Blo 674311 676051 := bstep (se 1 (by rfl) ⟨507038, by rfl⟩ : syracuseStep 676051 = 1014077) B1014077
theorem B676067 : Blo 674311 676067 := bstep (se 1 (by rfl) ⟨507050, by rfl⟩ : syracuseStep 676067 = 1014101) B1014101
theorem B676083 : Blo 674311 676083 := bstep (se 1 (by rfl) ⟨507062, by rfl⟩ : syracuseStep 676083 = 1014125) B1014125
theorem B676099 : Blo 674311 676099 := bstep (se 1 (by rfl) ⟨507074, by rfl⟩ : syracuseStep 676099 = 1014149) B1014149
theorem B676115 : Blo 674311 676115 := bstep (se 1 (by rfl) ⟨507086, by rfl⟩ : syracuseStep 676115 = 1014173) B1014173
theorem B676131 : Blo 674311 676131 := bstep (se 1 (by rfl) ⟨507098, by rfl⟩ : syracuseStep 676131 = 1014197) B1014197
theorem B676147 : Blo 674311 676147 := bstep (se 1 (by rfl) ⟨507110, by rfl⟩ : syracuseStep 676147 = 1014221) B1014221
theorem B676163 : Blo 674311 676163 := bstep (se 1 (by rfl) ⟨507122, by rfl⟩ : syracuseStep 676163 = 1014245) B1014245
theorem B2085197 : Blo 674311 2085197 := bstep (se 3 (by rfl) ⟨390974, by rfl⟩ : syracuseStep 2085197 = 781949) B781949
theorem B676179 : Blo 674311 676179 := bstep (se 1 (by rfl) ⟨507134, by rfl⟩ : syracuseStep 676179 = 1014269) B1014269
theorem B676195 : Blo 674311 676195 := bstep (se 1 (by rfl) ⟨507146, by rfl⟩ : syracuseStep 676195 = 1014293) B1014293
theorem B676211 : Blo 674311 676211 := bstep (se 1 (by rfl) ⟨507158, by rfl⟩ : syracuseStep 676211 = 1014317) B1014317
theorem B676227 : Blo 674311 676227 := bstep (se 1 (by rfl) ⟨507170, by rfl⟩ : syracuseStep 676227 = 1014341) B1014341
theorem B676243 : Blo 674311 676243 := bstep (se 1 (by rfl) ⟨507182, by rfl⟩ : syracuseStep 676243 = 1014365) B1014365
theorem B676259 : Blo 674311 676259 := bstep (se 1 (by rfl) ⟨507194, by rfl⟩ : syracuseStep 676259 = 1014389) B1014389
theorem B676275 : Blo 674311 676275 := bstep (se 1 (by rfl) ⟨507206, by rfl⟩ : syracuseStep 676275 = 1014413) B1014413
theorem B676291 : Blo 674311 676291 := bstep (se 1 (by rfl) ⟨507218, by rfl⟩ : syracuseStep 676291 = 1014437) B1014437
theorem B676307 : Blo 674311 676307 := bstep (se 1 (by rfl) ⟨507230, by rfl⟩ : syracuseStep 676307 = 1014461) B1014461
theorem B676323 : Blo 674311 676323 := bstep (se 1 (by rfl) ⟨507242, by rfl⟩ : syracuseStep 676323 = 1014485) B1014485
theorem B676339 : Blo 674311 676339 := bstep (se 1 (by rfl) ⟨507254, by rfl⟩ : syracuseStep 676339 = 1014509) B1014509
theorem B676355 : Blo 674311 676355 := bstep (se 1 (by rfl) ⟨507266, by rfl⟩ : syracuseStep 676355 = 1014533) B1014533
theorem B3854861 : Blo 674311 3854861 := bstep (se 3 (by rfl) ⟨722786, by rfl⟩ : syracuseStep 3854861 = 1445573) B1445573
theorem B1921553 : Blo 674311 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B676371 : Blo 674311 676371 := bstep (se 1 (by rfl) ⟨507278, by rfl⟩ : syracuseStep 676371 = 1014557) B1014557
theorem B18469397 : Blo 674311 18469397 := bstep (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) B865753
theorem B676387 : Blo 674311 676387 := bstep (se 1 (by rfl) ⟨507290, by rfl⟩ : syracuseStep 676387 = 1014581) B1014581
theorem B676403 : Blo 674311 676403 := bstep (se 1 (by rfl) ⟨507302, by rfl⟩ : syracuseStep 676403 = 1014605) B1014605
theorem B676419 : Blo 674311 676419 := bstep (se 1 (by rfl) ⟨507314, by rfl⟩ : syracuseStep 676419 = 1014629) B1014629
theorem B676435 : Blo 674311 676435 := bstep (se 1 (by rfl) ⟨507326, by rfl⟩ : syracuseStep 676435 = 1014653) B1014653
theorem B676451 : Blo 674311 676451 := bstep (se 1 (by rfl) ⟨507338, by rfl⟩ : syracuseStep 676451 = 1014677) B1014677
theorem B2282093 : Blo 674311 2282093 := bstep (se 3 (by rfl) ⟨427892, by rfl⟩ : syracuseStep 2282093 = 855785) B855785
theorem B676467 : Blo 674311 676467 := bstep (se 1 (by rfl) ⟨507350, by rfl⟩ : syracuseStep 676467 = 1014701) B1014701
theorem B676483 : Blo 674311 676483 := bstep (se 1 (by rfl) ⟨507362, by rfl⟩ : syracuseStep 676483 = 1014725) B1014725
theorem B3658373 : Blo 674311 3658373 := bstep (se 4 (by rfl) ⟨342972, by rfl⟩ : syracuseStep 3658373 = 685945) B685945
theorem B676499 : Blo 674311 676499 := bstep (se 1 (by rfl) ⟨507374, by rfl⟩ : syracuseStep 676499 = 1014749) B1014749
theorem B2282147 : Blo 674311 2282147 := bstep (se 1 (by rfl) ⟨1711610, by rfl⟩ : syracuseStep 2282147 = 3423221) B3423221
theorem B676515 : Blo 674311 676515 := bstep (se 1 (by rfl) ⟨507386, by rfl⟩ : syracuseStep 676515 = 1014773) B1014773
theorem B676531 : Blo 674311 676531 := bstep (se 1 (by rfl) ⟨507398, by rfl⟩ : syracuseStep 676531 = 1014797) B1014797
theorem B676547 : Blo 674311 676547 := bstep (se 1 (by rfl) ⟨507410, by rfl⟩ : syracuseStep 676547 = 1014821) B1014821
theorem B4870853 : Blo 674311 4870853 := bstep (se 4 (by rfl) ⟨456642, by rfl⟩ : syracuseStep 4870853 = 913285) B913285
theorem B676563 : Blo 674311 676563 := bstep (se 1 (by rfl) ⟨507422, by rfl⟩ : syracuseStep 676563 = 1014845) B1014845
theorem B676579 : Blo 674311 676579 := bstep (se 1 (by rfl) ⟨507434, by rfl⟩ : syracuseStep 676579 = 1014869) B1014869
theorem B676595 : Blo 674311 676595 := bstep (se 1 (by rfl) ⟨507446, by rfl⟩ : syracuseStep 676595 = 1014893) B1014893
theorem B676611 : Blo 674311 676611 := bstep (se 1 (by rfl) ⟨507458, by rfl⟩ : syracuseStep 676611 = 1014917) B1014917
theorem B676627 : Blo 674311 676627 := bstep (se 1 (by rfl) ⟨507470, by rfl⟩ : syracuseStep 676627 = 1014941) B1014941
theorem B676643 : Blo 674311 676643 := bstep (se 1 (by rfl) ⟨507482, by rfl⟩ : syracuseStep 676643 = 1014965) B1014965
theorem B676659 : Blo 674311 676659 := bstep (se 1 (by rfl) ⟨507494, by rfl⟩ : syracuseStep 676659 = 1014989) B1014989
theorem B676675 : Blo 674311 676675 := bstep (se 1 (by rfl) ⟨507506, by rfl⟩ : syracuseStep 676675 = 1015013) B1015013
theorem B676691 : Blo 674311 676691 := bstep (se 1 (by rfl) ⟨507518, by rfl⟩ : syracuseStep 676691 = 1015037) B1015037
theorem B676707 : Blo 674311 676707 := bstep (se 1 (by rfl) ⟨507530, by rfl⟩ : syracuseStep 676707 = 1015061) B1015061
theorem B676723 : Blo 674311 676723 := bstep (se 1 (by rfl) ⟨507542, by rfl⟩ : syracuseStep 676723 = 1015085) B1015085
theorem B676739 : Blo 674311 676739 := bstep (se 1 (by rfl) ⟨507554, by rfl⟩ : syracuseStep 676739 = 1015109) B1015109
theorem B676755 : Blo 674311 676755 := bstep (se 1 (by rfl) ⟨507566, by rfl⟩ : syracuseStep 676755 = 1015133) B1015133
theorem B1823651 : Blo 674311 1823651 := bstep (se 1 (by rfl) ⟨1367738, by rfl⟩ : syracuseStep 1823651 = 2735477) B2735477
theorem B676771 : Blo 674311 676771 := bstep (se 1 (by rfl) ⟨507578, by rfl⟩ : syracuseStep 676771 = 1015157) B1015157
theorem B2282417 : Blo 674311 2282417 := bstep (se 2 (by rfl) ⟨855906, by rfl⟩ : syracuseStep 2282417 = 1711813) B1711813
theorem B676787 : Blo 674311 676787 := bstep (se 1 (by rfl) ⟨507590, by rfl⟩ : syracuseStep 676787 = 1015181) B1015181
theorem B676803 : Blo 674311 676803 := bstep (se 1 (by rfl) ⟨507602, by rfl⟩ : syracuseStep 676803 = 1015205) B1015205
theorem B676819 : Blo 674311 676819 := bstep (se 1 (by rfl) ⟨507614, by rfl⟩ : syracuseStep 676819 = 1015229) B1015229
theorem B676835 : Blo 674311 676835 := bstep (se 1 (by rfl) ⟨507626, by rfl⟩ : syracuseStep 676835 = 1015253) B1015253
theorem B8803313 : Blo 674311 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B676851 : Blo 674311 676851 := bstep (se 1 (by rfl) ⟨507638, by rfl⟩ : syracuseStep 676851 = 1015277) B1015277
theorem B676867 : Blo 674311 676867 := bstep (se 1 (by rfl) ⟨507650, by rfl⟩ : syracuseStep 676867 = 1015301) B1015301
theorem B676883 : Blo 674311 676883 := bstep (se 1 (by rfl) ⟨507662, by rfl⟩ : syracuseStep 676883 = 1015325) B1015325
theorem B676899 : Blo 674311 676899 := bstep (se 1 (by rfl) ⟨507674, by rfl⟩ : syracuseStep 676899 = 1015349) B1015349
theorem B676915 : Blo 674311 676915 := bstep (se 1 (by rfl) ⟨507686, by rfl⟩ : syracuseStep 676915 = 1015373) B1015373
theorem B676931 : Blo 674311 676931 := bstep (se 1 (by rfl) ⟨507698, by rfl⟩ : syracuseStep 676931 = 1015397) B1015397
theorem B676947 : Blo 674311 676947 := bstep (se 1 (by rfl) ⟨507710, by rfl⟩ : syracuseStep 676947 = 1015421) B1015421
theorem B676963 : Blo 674311 676963 := bstep (se 1 (by rfl) ⟨507722, by rfl⟩ : syracuseStep 676963 = 1015445) B1015445
theorem B4936817 : Blo 674311 4936817 := bstep (se 2 (by rfl) ⟨1851306, by rfl⟩ : syracuseStep 4936817 = 3702613) B3702613
theorem B676979 : Blo 674311 676979 := bstep (se 1 (by rfl) ⟨507734, by rfl⟩ : syracuseStep 676979 = 1015469) B1015469
theorem B676995 : Blo 674311 676995 := bstep (se 1 (by rfl) ⟨507746, by rfl⟩ : syracuseStep 676995 = 1015493) B1015493
theorem B677011 : Blo 674311 677011 := bstep (se 1 (by rfl) ⟨507758, by rfl⟩ : syracuseStep 677011 = 1015517) B1015517
theorem B3429539 : Blo 674311 3429539 := bstep (se 1 (by rfl) ⟨2572154, by rfl⟩ : syracuseStep 3429539 = 5144309) B5144309
theorem B677027 : Blo 674311 677027 := bstep (se 1 (by rfl) ⟨507770, by rfl⟩ : syracuseStep 677027 = 1015541) B1015541
theorem B677043 : Blo 674311 677043 := bstep (se 1 (by rfl) ⟨507782, by rfl⟩ : syracuseStep 677043 = 1015565) B1015565
theorem B677059 : Blo 674311 677059 := bstep (se 1 (by rfl) ⟨507794, by rfl⟩ : syracuseStep 677059 = 1015589) B1015589
theorem B677075 : Blo 674311 677075 := bstep (se 1 (by rfl) ⟨507806, by rfl⟩ : syracuseStep 677075 = 1015613) B1015613
theorem B677091 : Blo 674311 677091 := bstep (se 1 (by rfl) ⟨507818, by rfl⟩ : syracuseStep 677091 = 1015637) B1015637
theorem B677107 : Blo 674311 677107 := bstep (se 1 (by rfl) ⟨507830, by rfl⟩ : syracuseStep 677107 = 1015661) B1015661
theorem B677123 : Blo 674311 677123 := bstep (se 1 (by rfl) ⟨507842, by rfl⟩ : syracuseStep 677123 = 1015685) B1015685
theorem B677139 : Blo 674311 677139 := bstep (se 1 (by rfl) ⟨507854, by rfl⟩ : syracuseStep 677139 = 1015709) B1015709
theorem B677155 : Blo 674311 677155 := bstep (se 1 (by rfl) ⟨507866, by rfl⟩ : syracuseStep 677155 = 1015733) B1015733
theorem B677171 : Blo 674311 677171 := bstep (se 1 (by rfl) ⟨507878, by rfl⟩ : syracuseStep 677171 = 1015757) B1015757
theorem B677187 : Blo 674311 677187 := bstep (se 1 (by rfl) ⟨507890, by rfl⟩ : syracuseStep 677187 = 1015781) B1015781
theorem B677203 : Blo 674311 677203 := bstep (se 1 (by rfl) ⟨507902, by rfl⟩ : syracuseStep 677203 = 1015805) B1015805
theorem B677219 : Blo 674311 677219 := bstep (se 1 (by rfl) ⟨507914, by rfl⟩ : syracuseStep 677219 = 1015829) B1015829
theorem B677235 : Blo 674311 677235 := bstep (se 1 (by rfl) ⟨507926, by rfl⟩ : syracuseStep 677235 = 1015853) B1015853
theorem B677251 : Blo 674311 677251 := bstep (se 1 (by rfl) ⟨507938, by rfl⟩ : syracuseStep 677251 = 1015877) B1015877
theorem B677267 : Blo 674311 677267 := bstep (se 1 (by rfl) ⟨507950, by rfl⟩ : syracuseStep 677267 = 1015901) B1015901
theorem B677283 : Blo 674311 677283 := bstep (se 1 (by rfl) ⟨507962, by rfl⟩ : syracuseStep 677283 = 1015925) B1015925
theorem B677299 : Blo 674311 677299 := bstep (se 1 (by rfl) ⟨507974, by rfl⟩ : syracuseStep 677299 = 1015949) B1015949
theorem B677315 : Blo 674311 677315 := bstep (se 1 (by rfl) ⟨507986, by rfl⟩ : syracuseStep 677315 = 1015973) B1015973
theorem B2282957 : Blo 674311 2282957 := bstep (se 3 (by rfl) ⟨428054, by rfl⟩ : syracuseStep 2282957 = 856109) B856109
theorem B677331 : Blo 674311 677331 := bstep (se 1 (by rfl) ⟨507998, by rfl⟩ : syracuseStep 677331 = 1015997) B1015997
theorem B677347 : Blo 674311 677347 := bstep (se 1 (by rfl) ⟨508010, by rfl⟩ : syracuseStep 677347 = 1016021) B1016021
theorem B677363 : Blo 674311 677363 := bstep (se 1 (by rfl) ⟨508022, by rfl⟩ : syracuseStep 677363 = 1016045) B1016045
theorem B2283011 : Blo 674311 2283011 := bstep (se 1 (by rfl) ⟨1712258, by rfl⟩ : syracuseStep 2283011 = 3424517) B3424517
theorem B677379 : Blo 674311 677379 := bstep (se 1 (by rfl) ⟨508034, by rfl⟩ : syracuseStep 677379 = 1016069) B1016069
theorem B677395 : Blo 674311 677395 := bstep (se 1 (by rfl) ⟨508046, by rfl⟩ : syracuseStep 677395 = 1016093) B1016093
theorem B677411 : Blo 674311 677411 := bstep (se 1 (by rfl) ⟨508058, by rfl⟩ : syracuseStep 677411 = 1016117) B1016117
theorem B677427 : Blo 674311 677427 := bstep (se 1 (by rfl) ⟨508070, by rfl⟩ : syracuseStep 677427 = 1016141) B1016141
theorem B677443 : Blo 674311 677443 := bstep (se 1 (by rfl) ⟨508082, by rfl⟩ : syracuseStep 677443 = 1016165) B1016165
theorem B677459 : Blo 674311 677459 := bstep (se 1 (by rfl) ⟨508094, by rfl⟩ : syracuseStep 677459 = 1016189) B1016189
theorem B677475 : Blo 674311 677475 := bstep (se 1 (by rfl) ⟨508106, by rfl⟩ : syracuseStep 677475 = 1016213) B1016213
theorem B1824365 : Blo 674311 1824365 := bstep (se 3 (by rfl) ⟨342068, by rfl⟩ : syracuseStep 1824365 = 684137) B684137
theorem B677491 : Blo 674311 677491 := bstep (se 1 (by rfl) ⟨508118, by rfl⟩ : syracuseStep 677491 = 1016237) B1016237
theorem B677507 : Blo 674311 677507 := bstep (se 1 (by rfl) ⟨508130, by rfl⟩ : syracuseStep 677507 = 1016261) B1016261
theorem B677523 : Blo 674311 677523 := bstep (se 1 (by rfl) ⟨508142, by rfl⟩ : syracuseStep 677523 = 1016285) B1016285
theorem B677539 : Blo 674311 677539 := bstep (se 1 (by rfl) ⟨508154, by rfl⟩ : syracuseStep 677539 = 1016309) B1016309
theorem B677555 : Blo 674311 677555 := bstep (se 1 (by rfl) ⟨508166, by rfl⟩ : syracuseStep 677555 = 1016333) B1016333
theorem B677571 : Blo 674311 677571 := bstep (se 1 (by rfl) ⟨508178, by rfl⟩ : syracuseStep 677571 = 1016357) B1016357
theorem B677587 : Blo 674311 677587 := bstep (se 1 (by rfl) ⟨508190, by rfl⟩ : syracuseStep 677587 = 1016381) B1016381
theorem B14636771 : Blo 674311 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B677603 : Blo 674311 677603 := bstep (se 1 (by rfl) ⟨508202, by rfl⟩ : syracuseStep 677603 = 1016405) B1016405
theorem B677619 : Blo 674311 677619 := bstep (se 1 (by rfl) ⟨508214, by rfl⟩ : syracuseStep 677619 = 1016429) B1016429
theorem B677635 : Blo 674311 677635 := bstep (se 1 (by rfl) ⟨508226, by rfl⟩ : syracuseStep 677635 = 1016453) B1016453
theorem B2283281 : Blo 674311 2283281 := bstep (se 2 (by rfl) ⟨856230, by rfl⟩ : syracuseStep 2283281 = 1712461) B1712461
theorem B677651 : Blo 674311 677651 := bstep (se 1 (by rfl) ⟨508238, by rfl⟩ : syracuseStep 677651 = 1016477) B1016477
theorem B677667 : Blo 674311 677667 := bstep (se 1 (by rfl) ⟨508250, by rfl⟩ : syracuseStep 677667 = 1016501) B1016501
theorem B677683 : Blo 674311 677683 := bstep (se 1 (by rfl) ⟨508262, by rfl⟩ : syracuseStep 677683 = 1016525) B1016525
theorem B677699 : Blo 674311 677699 := bstep (se 1 (by rfl) ⟨508274, by rfl⟩ : syracuseStep 677699 = 1016549) B1016549
theorem B677715 : Blo 674311 677715 := bstep (se 1 (by rfl) ⟨508286, by rfl⟩ : syracuseStep 677715 = 1016573) B1016573
theorem B677731 : Blo 674311 677731 := bstep (se 1 (by rfl) ⟨508298, by rfl⟩ : syracuseStep 677731 = 1016597) B1016597
theorem B677747 : Blo 674311 677747 := bstep (se 1 (by rfl) ⟨508310, by rfl⟩ : syracuseStep 677747 = 1016621) B1016621
theorem B677763 : Blo 674311 677763 := bstep (se 1 (by rfl) ⟨508322, by rfl⟩ : syracuseStep 677763 = 1016645) B1016645
theorem B677779 : Blo 674311 677779 := bstep (se 1 (by rfl) ⟨508334, by rfl⟩ : syracuseStep 677779 = 1016669) B1016669
theorem B677795 : Blo 674311 677795 := bstep (se 1 (by rfl) ⟨508346, by rfl⟩ : syracuseStep 677795 = 1016693) B1016693
theorem B677811 : Blo 674311 677811 := bstep (se 1 (by rfl) ⟨508358, by rfl⟩ : syracuseStep 677811 = 1016717) B1016717
theorem B1923011 : Blo 674311 1923011 := bstep (se 1 (by rfl) ⟨1442258, by rfl⟩ : syracuseStep 1923011 = 2884517) B2884517
theorem B677827 : Blo 674311 677827 := bstep (se 1 (by rfl) ⟨508370, by rfl⟩ : syracuseStep 677827 = 1016741) B1016741
theorem B3430349 : Blo 674311 3430349 := bstep (se 3 (by rfl) ⟨643190, by rfl⟩ : syracuseStep 3430349 = 1286381) B1286381
theorem B677843 : Blo 674311 677843 := bstep (se 1 (by rfl) ⟨508382, by rfl⟩ : syracuseStep 677843 = 1016765) B1016765
theorem B677859 : Blo 674311 677859 := bstep (se 1 (by rfl) ⟨508394, by rfl⟩ : syracuseStep 677859 = 1016789) B1016789
theorem B677875 : Blo 674311 677875 := bstep (se 1 (by rfl) ⟨508406, by rfl⟩ : syracuseStep 677875 = 1016813) B1016813
theorem B677891 : Blo 674311 677891 := bstep (se 1 (by rfl) ⟨508418, by rfl⟩ : syracuseStep 677891 = 1016837) B1016837
theorem B677907 : Blo 674311 677907 := bstep (se 1 (by rfl) ⟨508430, by rfl⟩ : syracuseStep 677907 = 1016861) B1016861
theorem B677923 : Blo 674311 677923 := bstep (se 1 (by rfl) ⟨508442, by rfl⟩ : syracuseStep 677923 = 1016885) B1016885
theorem B677939 : Blo 674311 677939 := bstep (se 1 (by rfl) ⟨508454, by rfl⟩ : syracuseStep 677939 = 1016909) B1016909
theorem B677955 : Blo 674311 677955 := bstep (se 1 (by rfl) ⟨508466, by rfl⟩ : syracuseStep 677955 = 1016933) B1016933
theorem B677971 : Blo 674311 677971 := bstep (se 1 (by rfl) ⟨508478, by rfl⟩ : syracuseStep 677971 = 1016957) B1016957
theorem B677987 : Blo 674311 677987 := bstep (se 1 (by rfl) ⟨508490, by rfl⟩ : syracuseStep 677987 = 1016981) B1016981
theorem B678003 : Blo 674311 678003 := bstep (se 1 (by rfl) ⟨508502, by rfl⟩ : syracuseStep 678003 = 1017005) B1017005
theorem B678019 : Blo 674311 678019 := bstep (se 1 (by rfl) ⟨508514, by rfl⟩ : syracuseStep 678019 = 1017029) B1017029
theorem B678035 : Blo 674311 678035 := bstep (se 1 (by rfl) ⟨508526, by rfl⟩ : syracuseStep 678035 = 1017053) B1017053
theorem B678051 : Blo 674311 678051 := bstep (se 1 (by rfl) ⟨508538, by rfl⟩ : syracuseStep 678051 = 1017077) B1017077
theorem B678067 : Blo 674311 678067 := bstep (se 1 (by rfl) ⟨508550, by rfl⟩ : syracuseStep 678067 = 1017101) B1017101
theorem B678083 : Blo 674311 678083 := bstep (se 1 (by rfl) ⟨508562, by rfl⟩ : syracuseStep 678083 = 1017125) B1017125
theorem B678099 : Blo 674311 678099 := bstep (se 1 (by rfl) ⟨508574, by rfl⟩ : syracuseStep 678099 = 1017149) B1017149
theorem B678115 : Blo 674311 678115 := bstep (se 1 (by rfl) ⟨508586, by rfl⟩ : syracuseStep 678115 = 1017173) B1017173
theorem B678131 : Blo 674311 678131 := bstep (se 1 (by rfl) ⟨508598, by rfl⟩ : syracuseStep 678131 = 1017197) B1017197
theorem B678147 : Blo 674311 678147 := bstep (se 1 (by rfl) ⟨508610, by rfl⟩ : syracuseStep 678147 = 1017221) B1017221
theorem B2316557 : Blo 674311 2316557 := bstep (se 3 (by rfl) ⟨434354, by rfl⟩ : syracuseStep 2316557 = 868709) B868709
theorem B678163 : Blo 674311 678163 := bstep (se 1 (by rfl) ⟨508622, by rfl⟩ : syracuseStep 678163 = 1017245) B1017245
theorem B678179 : Blo 674311 678179 := bstep (se 1 (by rfl) ⟨508634, by rfl⟩ : syracuseStep 678179 = 1017269) B1017269
theorem B2283821 : Blo 674311 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B678195 : Blo 674311 678195 := bstep (se 1 (by rfl) ⟨508646, by rfl⟩ : syracuseStep 678195 = 1017293) B1017293
theorem B678211 : Blo 674311 678211 := bstep (se 1 (by rfl) ⟨508658, by rfl⟩ : syracuseStep 678211 = 1017317) B1017317
theorem B678227 : Blo 674311 678227 := bstep (se 1 (by rfl) ⟨508670, by rfl⟩ : syracuseStep 678227 = 1017341) B1017341
theorem B2283875 : Blo 674311 2283875 := bstep (se 1 (by rfl) ⟨1712906, by rfl⟩ : syracuseStep 2283875 = 3425813) B3425813
theorem B678243 : Blo 674311 678243 := bstep (se 1 (by rfl) ⟨508682, by rfl⟩ : syracuseStep 678243 = 1017365) B1017365
theorem B678259 : Blo 674311 678259 := bstep (se 1 (by rfl) ⟨508694, by rfl⟩ : syracuseStep 678259 = 1017389) B1017389
theorem B678275 : Blo 674311 678275 := bstep (se 1 (by rfl) ⟨508706, by rfl⟩ : syracuseStep 678275 = 1017413) B1017413
theorem B678291 : Blo 674311 678291 := bstep (se 1 (by rfl) ⟨508718, by rfl⟩ : syracuseStep 678291 = 1017437) B1017437
theorem B678307 : Blo 674311 678307 := bstep (se 1 (by rfl) ⟨508730, by rfl⟩ : syracuseStep 678307 = 1017461) B1017461
theorem B2316899 : Blo 674311 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B2284145 : Blo 674311 2284145 := bstep (se 2 (by rfl) ⟨856554, by rfl⟩ : syracuseStep 2284145 = 1713109) B1713109
theorem B7690949 : Blo 674311 7690949 := bstep (se 4 (by rfl) ⟨721026, by rfl⟩ : syracuseStep 7690949 = 1442053) B1442053
theorem B5135075 : Blo 674311 5135075 := bstep (se 1 (by rfl) ⟨3851306, by rfl⟩ : syracuseStep 5135075 = 7702613) B7702613
theorem B1923821 : Blo 674311 1923821 := bstep (se 3 (by rfl) ⟨360716, by rfl⟩ : syracuseStep 1923821 = 721433) B721433
theorem B973603 : Blo 674311 973603 := bstep (se 1 (by rfl) ⟨730202, by rfl⟩ : syracuseStep 973603 = 1460405) B1460405
theorem B3464099 : Blo 674311 3464099 := bstep (se 1 (by rfl) ⟨2598074, by rfl⟩ : syracuseStep 3464099 = 5196149) B5196149
theorem B1924013 : Blo 674311 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B1465393 : Blo 674311 1465393 := bstep (se 2 (by rfl) ⟨549522, by rfl⟩ : syracuseStep 1465393 = 1099045) B1099045
theorem B2284685 : Blo 674311 2284685 := bstep (se 3 (by rfl) ⟨428378, by rfl⟩ : syracuseStep 2284685 = 856757) B856757
theorem B2284739 : Blo 674311 2284739 := bstep (se 1 (by rfl) ⟨1713554, by rfl⟩ : syracuseStep 2284739 = 3427109) B3427109
theorem B1137955 : Blo 674311 1137955 := bstep (se 1 (by rfl) ⟨853466, by rfl⟩ : syracuseStep 1137955 = 1706933) B1706933
theorem B11525489 : Blo 674311 11525489 := bstep (se 2 (by rfl) ⟨4322058, by rfl⟩ : syracuseStep 11525489 = 8644117) B8644117
theorem B3857777 : Blo 674311 3857777 := bstep (se 2 (by rfl) ⟨1446666, by rfl⟩ : syracuseStep 3857777 = 2893333) B2893333
theorem B2088355 : Blo 674311 2088355 := bstep (se 1 (by rfl) ⟨1566266, by rfl⟩ : syracuseStep 2088355 = 3132533) B3132533
theorem B1138097 : Blo 674311 1138097 := bstep (se 2 (by rfl) ⟨426786, by rfl⟩ : syracuseStep 1138097 = 853573) B853573
theorem B2285009 : Blo 674311 2285009 := bstep (se 2 (by rfl) ⟨856878, by rfl⟩ : syracuseStep 2285009 = 1713757) B1713757
theorem B1138225 : Blo 674311 1138225 := bstep (se 2 (by rfl) ⟨426834, by rfl⟩ : syracuseStep 1138225 = 853669) B853669
theorem B1138259 : Blo 674311 1138259 := bstep (se 1 (by rfl) ⟨853694, by rfl⟩ : syracuseStep 1138259 = 1707389) B1707389
theorem B1040035 : Blo 674311 1040035 := bstep (se 1 (by rfl) ⟨780026, by rfl⟩ : syracuseStep 1040035 = 1560053) B1560053
theorem B1138387 : Blo 674311 1138387 := bstep (se 1 (by rfl) ⟨853790, by rfl⟩ : syracuseStep 1138387 = 1707581) B1707581
theorem B1138529 : Blo 674311 1138529 := bstep (se 2 (by rfl) ⟨426948, by rfl⟩ : syracuseStep 1138529 = 853897) B853897
theorem B2056049 : Blo 674311 2056049 := bstep (se 2 (by rfl) ⟨771018, by rfl⟩ : syracuseStep 2056049 = 1542037) B1542037
theorem B1925005 : Blo 674311 1925005 := bstep (se 3 (by rfl) ⟨360938, by rfl⟩ : syracuseStep 1925005 = 721877) B721877
theorem B1138657 : Blo 674311 1138657 := bstep (se 2 (by rfl) ⟨426996, by rfl⟩ : syracuseStep 1138657 = 853993) B853993
theorem B2285549 : Blo 674311 2285549 := bstep (se 3 (by rfl) ⟨428540, by rfl⟩ : syracuseStep 2285549 = 857081) B857081
theorem B1138691 : Blo 674311 1138691 := bstep (se 1 (by rfl) ⟨854018, by rfl⟩ : syracuseStep 1138691 = 1708037) B1708037
theorem B2285603 : Blo 674311 2285603 := bstep (se 1 (by rfl) ⟨1714202, by rfl⟩ : syracuseStep 2285603 = 3428405) B3428405
theorem B1138819 : Blo 674311 1138819 := bstep (se 1 (by rfl) ⟨854114, by rfl⟩ : syracuseStep 1138819 = 1708229) B1708229
theorem B1466545 : Blo 674311 1466545 := bstep (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) B1099909
theorem B1138961 : Blo 674311 1138961 := bstep (se 2 (by rfl) ⟨427110, by rfl⟩ : syracuseStep 1138961 = 854221) B854221
theorem B2285873 : Blo 674311 2285873 := bstep (se 2 (by rfl) ⟨857202, by rfl⟩ : syracuseStep 2285873 = 1714405) B1714405
theorem B1139089 : Blo 674311 1139089 := bstep (se 2 (by rfl) ⟨427158, by rfl⟩ : syracuseStep 1139089 = 854317) B854317
theorem B1139123 : Blo 674311 1139123 := bstep (se 1 (by rfl) ⟨854342, by rfl⟩ : syracuseStep 1139123 = 1708685) B1708685
theorem B5792269 : Blo 674311 5792269 := bstep (se 3 (by rfl) ⟨1086050, by rfl⟩ : syracuseStep 5792269 = 2172101) B2172101
theorem B1139251 : Blo 674311 1139251 := bstep (se 1 (by rfl) ⟨854438, by rfl⟩ : syracuseStep 1139251 = 1708877) B1708877
theorem B1466993 : Blo 674311 1466993 := bstep (se 2 (by rfl) ⟨550122, by rfl⟩ : syracuseStep 1466993 = 1100245) B1100245
theorem B1139393 : Blo 674311 1139393 := bstep (se 2 (by rfl) ⟨427272, by rfl⟩ : syracuseStep 1139393 = 854545) B854545
theorem B3859235 : Blo 674311 3859235 := bstep (se 1 (by rfl) ⟨2894426, by rfl⟩ : syracuseStep 3859235 = 5788853) B5788853
theorem B3433265 : Blo 674311 3433265 := bstep (se 2 (by rfl) ⟨1287474, by rfl⟩ : syracuseStep 3433265 = 2574949) B2574949
theorem B1139521 : Blo 674311 1139521 := bstep (se 2 (by rfl) ⟨427320, by rfl⟩ : syracuseStep 1139521 = 854641) B854641
theorem B2286413 : Blo 674311 2286413 := bstep (se 3 (by rfl) ⟨428702, by rfl⟩ : syracuseStep 2286413 = 857405) B857405
theorem B1139555 : Blo 674311 1139555 := bstep (se 1 (by rfl) ⟨854666, by rfl⟩ : syracuseStep 1139555 = 1709333) B1709333
theorem B2286467 : Blo 674311 2286467 := bstep (se 1 (by rfl) ⟨1714850, by rfl⟩ : syracuseStep 2286467 = 3429701) B3429701
theorem B1139683 : Blo 674311 1139683 := bstep (se 1 (by rfl) ⟨854762, by rfl⟩ : syracuseStep 1139683 = 1709525) B1709525
theorem B812035 : Blo 674311 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B2090033 : Blo 674311 2090033 := bstep (se 2 (by rfl) ⟨783762, by rfl⟩ : syracuseStep 2090033 = 1567525) B1567525
theorem B1139825 : Blo 674311 1139825 := bstep (se 2 (by rfl) ⟨427434, by rfl⟩ : syracuseStep 1139825 = 854869) B854869
theorem B2286737 : Blo 674311 2286737 := bstep (se 2 (by rfl) ⟨857526, by rfl⟩ : syracuseStep 2286737 = 1715053) B1715053
theorem B1139953 : Blo 674311 1139953 := bstep (se 2 (by rfl) ⟨427482, by rfl⟩ : syracuseStep 1139953 = 854965) B854965
theorem B3663089 : Blo 674311 3663089 := bstep (se 2 (by rfl) ⟨1373658, by rfl⟩ : syracuseStep 3663089 = 2747317) B2747317
theorem B1139987 : Blo 674311 1139987 := bstep (se 1 (by rfl) ⟨854990, by rfl⟩ : syracuseStep 1139987 = 1709981) B1709981
theorem B1140115 : Blo 674311 1140115 := bstep (se 1 (by rfl) ⟨855086, by rfl⟩ : syracuseStep 1140115 = 1710173) B1710173
theorem B1828291 : Blo 674311 1828291 := bstep (se 1 (by rfl) ⟨1371218, by rfl⟩ : syracuseStep 1828291 = 2742437) B2742437
theorem B17360405 : Blo 674311 17360405 := bstep (se 6 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 17360405 = 813769) B813769
theorem B1140257 : Blo 674311 1140257 := bstep (se 2 (by rfl) ⟨427596, by rfl⟩ : syracuseStep 1140257 = 855193) B855193
theorem B1926737 : Blo 674311 1926737 := bstep (se 2 (by rfl) ⟨722526, by rfl⟩ : syracuseStep 1926737 = 1445053) B1445053
theorem B1140385 : Blo 674311 1140385 := bstep (se 2 (by rfl) ⟨427644, by rfl⟩ : syracuseStep 1140385 = 855289) B855289
theorem B2287277 : Blo 674311 2287277 := bstep (se 3 (by rfl) ⟨428864, by rfl⟩ : syracuseStep 2287277 = 857729) B857729
theorem B1140419 : Blo 674311 1140419 := bstep (se 1 (by rfl) ⟨855314, by rfl⟩ : syracuseStep 1140419 = 1710629) B1710629
theorem B2287331 : Blo 674311 2287331 := bstep (se 1 (by rfl) ⟨1715498, by rfl⟩ : syracuseStep 2287331 = 3430997) B3430997
theorem B3860237 : Blo 674311 3860237 := bstep (se 3 (by rfl) ⟨723794, by rfl⟩ : syracuseStep 3860237 = 1447589) B1447589
theorem B1926929 : Blo 674311 1926929 := bstep (se 2 (by rfl) ⟨722598, by rfl⟩ : syracuseStep 1926929 = 1445197) B1445197
theorem B1140547 : Blo 674311 1140547 := bstep (se 1 (by rfl) ⟨855410, by rfl⟩ : syracuseStep 1140547 = 1710821) B1710821
theorem B5793605 : Blo 674311 5793605 := bstep (se 4 (by rfl) ⟨543150, by rfl⟩ : syracuseStep 5793605 = 1086301) B1086301
theorem B1140689 : Blo 674311 1140689 := bstep (se 2 (by rfl) ⟨427758, by rfl⟩ : syracuseStep 1140689 = 855517) B855517
theorem B2287601 : Blo 674311 2287601 := bstep (se 2 (by rfl) ⟨857850, by rfl⟩ : syracuseStep 2287601 = 1715701) B1715701
theorem B1140817 : Blo 674311 1140817 := bstep (se 2 (by rfl) ⟨427806, by rfl⟩ : syracuseStep 1140817 = 855613) B855613
theorem B1140851 : Blo 674311 1140851 := bstep (se 1 (by rfl) ⟨855638, by rfl⟩ : syracuseStep 1140851 = 1711277) B1711277
theorem B1730737 : Blo 674311 1730737 := bstep (se 2 (by rfl) ⟨649026, by rfl⟩ : syracuseStep 1730737 = 1298053) B1298053
theorem B1140979 : Blo 674311 1140979 := bstep (se 1 (by rfl) ⟨855734, by rfl⟩ : syracuseStep 1140979 = 1711469) B1711469
theorem B1042723 : Blo 674311 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B1141121 : Blo 674311 1141121 := bstep (se 2 (by rfl) ⟨427920, by rfl⟩ : syracuseStep 1141121 = 855841) B855841
theorem B1829251 : Blo 674311 1829251 := bstep (se 1 (by rfl) ⟨1371938, by rfl⟩ : syracuseStep 1829251 = 2743877) B2743877
theorem B1370513 : Blo 674311 1370513 := bstep (se 2 (by rfl) ⟨513942, by rfl⟩ : syracuseStep 1370513 = 1027885) B1027885
theorem B1370609 : Blo 674311 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B1141249 : Blo 674311 1141249 := bstep (se 2 (by rfl) ⟨427968, by rfl⟩ : syracuseStep 1141249 = 855937) B855937
theorem B2288141 : Blo 674311 2288141 := bstep (se 3 (by rfl) ⟨429026, by rfl⟩ : syracuseStep 2288141 = 858053) B858053
theorem B1141283 : Blo 674311 1141283 := bstep (se 1 (by rfl) ⟨855962, by rfl⟩ : syracuseStep 1141283 = 1711925) B1711925
theorem B2288195 : Blo 674311 2288195 := bstep (se 1 (by rfl) ⟨1716146, by rfl⟩ : syracuseStep 2288195 = 3432293) B3432293
theorem B1141411 : Blo 674311 1141411 := bstep (se 1 (by rfl) ⟨856058, by rfl⟩ : syracuseStep 1141411 = 1712117) B1712117
theorem B813731 : Blo 674311 813731 := bstep (se 1 (by rfl) ⟨610298, by rfl⟩ : syracuseStep 813731 = 1220597) B1220597
theorem B1927921 : Blo 674311 1927921 := bstep (se 2 (by rfl) ⟨722970, by rfl⟩ : syracuseStep 1927921 = 1445941) B1445941
theorem B1141553 : Blo 674311 1141553 := bstep (se 2 (by rfl) ⟨428082, by rfl⟩ : syracuseStep 1141553 = 856165) B856165
theorem B1731395 : Blo 674311 1731395 := bstep (se 1 (by rfl) ⟨1298546, by rfl⟩ : syracuseStep 1731395 = 2597093) B2597093
theorem B2288465 : Blo 674311 2288465 := bstep (se 2 (by rfl) ⟨858174, by rfl⟩ : syracuseStep 2288465 = 1716349) B1716349
theorem B1141681 : Blo 674311 1141681 := bstep (se 2 (by rfl) ⟨428130, by rfl⟩ : syracuseStep 1141681 = 856261) B856261
theorem B1141715 : Blo 674311 1141715 := bstep (se 1 (by rfl) ⟨856286, by rfl⟩ : syracuseStep 1141715 = 1712573) B1712573
theorem B1928195 : Blo 674311 1928195 := bstep (se 1 (by rfl) ⟨1446146, by rfl⟩ : syracuseStep 1928195 = 2892293) B2892293
theorem B1141843 : Blo 674311 1141843 := bstep (se 1 (by rfl) ⟨856382, by rfl⟩ : syracuseStep 1141843 = 1712765) B1712765
theorem B1928387 : Blo 674311 1928387 := bstep (se 1 (by rfl) ⟨1446290, by rfl⟩ : syracuseStep 1928387 = 2892581) B2892581
theorem B912593 : Blo 674311 912593 := bstep (se 2 (by rfl) ⟨342222, by rfl⟩ : syracuseStep 912593 = 684445) B684445
theorem B1141985 : Blo 674311 1141985 := bstep (se 2 (by rfl) ⟨428244, by rfl⟩ : syracuseStep 1141985 = 856489) B856489
theorem B9268465 : Blo 674311 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B1142113 : Blo 674311 1142113 := bstep (se 2 (by rfl) ⟨428292, by rfl⟩ : syracuseStep 1142113 = 856585) B856585
theorem B2289005 : Blo 674311 2289005 := bstep (se 3 (by rfl) ⟨429188, by rfl⟩ : syracuseStep 2289005 = 858377) B858377
theorem B1142147 : Blo 674311 1142147 := bstep (se 1 (by rfl) ⟨856610, by rfl⟩ : syracuseStep 1142147 = 1713221) B1713221
theorem B1830289 : Blo 674311 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B2289059 : Blo 674311 2289059 := bstep (se 1 (by rfl) ⟨1716794, by rfl⟩ : syracuseStep 2289059 = 3433589) B3433589
theorem B1142275 : Blo 674311 1142275 := bstep (se 1 (by rfl) ⟨856706, by rfl⟩ : syracuseStep 1142275 = 1713413) B1713413
theorem B1142417 : Blo 674311 1142417 := bstep (se 2 (by rfl) ⟨428406, by rfl⟩ : syracuseStep 1142417 = 856813) B856813
theorem B6942449 : Blo 674311 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B1011473 : Blo 674311 1011473 := bstep (se 2 (by rfl) ⟨379302, by rfl⟩ : syracuseStep 1011473 = 758605) B758605
theorem B1142545 : Blo 674311 1142545 := bstep (se 2 (by rfl) ⟨428454, by rfl⟩ : syracuseStep 1142545 = 856909) B856909
theorem B41676565 : Blo 674311 41676565 := bstep (se 6 (by rfl) ⟨976794, by rfl⟩ : syracuseStep 41676565 = 1953589) B1953589
theorem B1011491 : Blo 674311 1011491 := bstep (se 1 (by rfl) ⟨758618, by rfl⟩ : syracuseStep 1011491 = 1517237) B1517237
theorem B1142579 : Blo 674311 1142579 := bstep (se 1 (by rfl) ⟨856934, by rfl⟩ : syracuseStep 1142579 = 1713869) B1713869
theorem B1011521 : Blo 674311 1011521 := bstep (se 2 (by rfl) ⟨379320, by rfl⟩ : syracuseStep 1011521 = 758641) B758641
theorem B6254405 : Blo 674311 6254405 := bstep (se 4 (by rfl) ⟨586350, by rfl⟩ : syracuseStep 6254405 = 1172701) B1172701
theorem B1011539 : Blo 674311 1011539 := bstep (se 1 (by rfl) ⟨758654, by rfl⟩ : syracuseStep 1011539 = 1517309) B1517309
theorem B1011569 : Blo 674311 1011569 := bstep (se 2 (by rfl) ⟨379338, by rfl⟩ : syracuseStep 1011569 = 758677) B758677
theorem B1011587 : Blo 674311 1011587 := bstep (se 1 (by rfl) ⟨758690, by rfl⟩ : syracuseStep 1011587 = 1517381) B1517381
theorem B913297 : Blo 674311 913297 := bstep (se 2 (by rfl) ⟨342486, by rfl⟩ : syracuseStep 913297 = 684973) B684973
theorem B1011617 : Blo 674311 1011617 := bstep (se 2 (by rfl) ⟨379356, by rfl⟩ : syracuseStep 1011617 = 758713) B758713
theorem B1011635 : Blo 674311 1011635 := bstep (se 1 (by rfl) ⟨758726, by rfl⟩ : syracuseStep 1011635 = 1517453) B1517453
theorem B1142707 : Blo 674311 1142707 := bstep (se 1 (by rfl) ⟨857030, by rfl⟩ : syracuseStep 1142707 = 1714061) B1714061
theorem B5140421 : Blo 674311 5140421 := bstep (se 4 (by rfl) ⟨481914, by rfl⟩ : syracuseStep 5140421 = 963829) B963829
theorem B1011665 : Blo 674311 1011665 := bstep (se 2 (by rfl) ⟨379374, by rfl⟩ : syracuseStep 1011665 = 758749) B758749
theorem B1011683 : Blo 674311 1011683 := bstep (se 1 (by rfl) ⟨758762, by rfl⟩ : syracuseStep 1011683 = 1517525) B1517525
theorem B1929197 : Blo 674311 1929197 := bstep (se 3 (by rfl) ⟨361724, by rfl⟩ : syracuseStep 1929197 = 723449) B723449
theorem B1011713 : Blo 674311 1011713 := bstep (se 2 (by rfl) ⟨379392, by rfl⟩ : syracuseStep 1011713 = 758785) B758785
theorem B1011731 : Blo 674311 1011731 := bstep (se 1 (by rfl) ⟨758798, by rfl⟩ : syracuseStep 1011731 = 1517597) B1517597
theorem B1011761 : Blo 674311 1011761 := bstep (se 2 (by rfl) ⟨379410, by rfl⟩ : syracuseStep 1011761 = 758821) B758821
theorem B1142849 : Blo 674311 1142849 := bstep (se 2 (by rfl) ⟨428568, by rfl⟩ : syracuseStep 1142849 = 857137) B857137
theorem B1011779 : Blo 674311 1011779 := bstep (se 1 (by rfl) ⟨758834, by rfl⟩ : syracuseStep 1011779 = 1517669) B1517669
theorem B1011809 : Blo 674311 1011809 := bstep (se 2 (by rfl) ⟨379428, by rfl⟩ : syracuseStep 1011809 = 758857) B758857
theorem B1011827 : Blo 674311 1011827 := bstep (se 1 (by rfl) ⟨758870, by rfl⟩ : syracuseStep 1011827 = 1517741) B1517741
theorem B4321421 : Blo 674311 4321421 := bstep (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) B1620533
theorem B1011857 : Blo 674311 1011857 := bstep (se 2 (by rfl) ⟨379446, by rfl⟩ : syracuseStep 1011857 = 758893) B758893
theorem B1011875 : Blo 674311 1011875 := bstep (se 1 (by rfl) ⟨758906, by rfl⟩ : syracuseStep 1011875 = 1517813) B1517813
theorem B1929379 : Blo 674311 1929379 := bstep (se 1 (by rfl) ⟨1447034, by rfl⟩ : syracuseStep 1929379 = 2894069) B2894069
theorem B1011905 : Blo 674311 1011905 := bstep (se 2 (by rfl) ⟨379464, by rfl⟩ : syracuseStep 1011905 = 758929) B758929
theorem B1142977 : Blo 674311 1142977 := bstep (se 2 (by rfl) ⟨428616, by rfl⟩ : syracuseStep 1142977 = 857233) B857233
theorem B1011923 : Blo 674311 1011923 := bstep (se 1 (by rfl) ⟨758942, by rfl⟩ : syracuseStep 1011923 = 1517885) B1517885
theorem B1143011 : Blo 674311 1143011 := bstep (se 1 (by rfl) ⟨857258, by rfl⟩ : syracuseStep 1143011 = 1714517) B1714517
theorem B3207395 : Blo 674311 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B1011953 : Blo 674311 1011953 := bstep (se 2 (by rfl) ⟨379482, by rfl⟩ : syracuseStep 1011953 = 758965) B758965
theorem B1011971 : Blo 674311 1011971 := bstep (se 1 (by rfl) ⟨758978, by rfl⟩ : syracuseStep 1011971 = 1517957) B1517957
theorem B2060561 : Blo 674311 2060561 := bstep (se 2 (by rfl) ⟨772710, by rfl⟩ : syracuseStep 2060561 = 1545421) B1545421
theorem B1012001 : Blo 674311 1012001 := bstep (se 2 (by rfl) ⟨379500, by rfl⟩ : syracuseStep 1012001 = 759001) B759001
theorem B1012019 : Blo 674311 1012019 := bstep (se 1 (by rfl) ⟨759014, by rfl⟩ : syracuseStep 1012019 = 1518029) B1518029
theorem B1012049 : Blo 674311 1012049 := bstep (se 2 (by rfl) ⟨379518, by rfl⟩ : syracuseStep 1012049 = 759037) B759037
theorem B1143139 : Blo 674311 1143139 := bstep (se 1 (by rfl) ⟨857354, by rfl⟩ : syracuseStep 1143139 = 1714709) B1714709
theorem B1012067 : Blo 674311 1012067 := bstep (se 1 (by rfl) ⟨759050, by rfl⟩ : syracuseStep 1012067 = 1518101) B1518101
theorem B4321649 : Blo 674311 4321649 := bstep (se 2 (by rfl) ⟨1620618, by rfl⟩ : syracuseStep 4321649 = 3241237) B3241237
theorem B1012097 : Blo 674311 1012097 := bstep (se 2 (by rfl) ⟨379536, by rfl⟩ : syracuseStep 1012097 = 759073) B759073
theorem B7696781 : Blo 674311 7696781 := bstep (se 3 (by rfl) ⟨1443146, by rfl⟩ : syracuseStep 7696781 = 2886293) B2886293
theorem B18510221 : Blo 674311 18510221 := bstep (se 3 (by rfl) ⟨3470666, by rfl⟩ : syracuseStep 18510221 = 6941333) B6941333
theorem B1012115 : Blo 674311 1012115 := bstep (se 1 (by rfl) ⟨759086, by rfl⟩ : syracuseStep 1012115 = 1518173) B1518173
theorem B1012145 : Blo 674311 1012145 := bstep (se 2 (by rfl) ⟨379554, by rfl⟩ : syracuseStep 1012145 = 759109) B759109
theorem B1012163 : Blo 674311 1012163 := bstep (se 1 (by rfl) ⟨759122, by rfl⟩ : syracuseStep 1012163 = 1518245) B1518245
theorem B1012193 : Blo 674311 1012193 := bstep (se 2 (by rfl) ⟨379572, by rfl⟩ : syracuseStep 1012193 = 759145) B759145
theorem B1143281 : Blo 674311 1143281 := bstep (se 2 (by rfl) ⟨428730, by rfl⟩ : syracuseStep 1143281 = 857461) B857461
theorem B1012211 : Blo 674311 1012211 := bstep (se 1 (by rfl) ⟨759158, by rfl⟩ : syracuseStep 1012211 = 1518317) B1518317
theorem B1012241 : Blo 674311 1012241 := bstep (se 2 (by rfl) ⟨379590, by rfl⟩ : syracuseStep 1012241 = 759181) B759181
theorem B1012259 : Blo 674311 1012259 := bstep (se 1 (by rfl) ⟨759194, by rfl⟩ : syracuseStep 1012259 = 1518389) B1518389
theorem B1012289 : Blo 674311 1012289 := bstep (se 2 (by rfl) ⟨379608, by rfl⟩ : syracuseStep 1012289 = 759217) B759217
theorem B1012307 : Blo 674311 1012307 := bstep (se 1 (by rfl) ⟨759230, by rfl⟩ : syracuseStep 1012307 = 1518461) B1518461
theorem B1012337 : Blo 674311 1012337 := bstep (se 2 (by rfl) ⟨379626, by rfl⟩ : syracuseStep 1012337 = 759253) B759253
theorem B1143409 : Blo 674311 1143409 := bstep (se 2 (by rfl) ⟨428778, by rfl⟩ : syracuseStep 1143409 = 857557) B857557
theorem B3863153 : Blo 674311 3863153 := bstep (se 2 (by rfl) ⟨1448682, by rfl⟩ : syracuseStep 3863153 = 2897365) B2897365
theorem B1012355 : Blo 674311 1012355 := bstep (se 1 (by rfl) ⟨759266, by rfl⟩ : syracuseStep 1012355 = 1518533) B1518533
theorem B1929869 : Blo 674311 1929869 := bstep (se 3 (by rfl) ⟨361850, by rfl⟩ : syracuseStep 1929869 = 723701) B723701
theorem B1143443 : Blo 674311 1143443 := bstep (se 1 (by rfl) ⟨857582, by rfl⟩ : syracuseStep 1143443 = 1715165) B1715165
theorem B1012385 : Blo 674311 1012385 := bstep (se 2 (by rfl) ⟨379644, by rfl⟩ : syracuseStep 1012385 = 759289) B759289
theorem B1012403 : Blo 674311 1012403 := bstep (se 1 (by rfl) ⟨759302, by rfl⟩ : syracuseStep 1012403 = 1518605) B1518605
theorem B1012433 : Blo 674311 1012433 := bstep (se 2 (by rfl) ⟨379662, by rfl⟩ : syracuseStep 1012433 = 759325) B759325
theorem B1012451 : Blo 674311 1012451 := bstep (se 1 (by rfl) ⟨759338, by rfl⟩ : syracuseStep 1012451 = 1518677) B1518677
theorem B1012481 : Blo 674311 1012481 := bstep (se 2 (by rfl) ⟨379680, by rfl⟩ : syracuseStep 1012481 = 759361) B759361
theorem B1012499 : Blo 674311 1012499 := bstep (se 1 (by rfl) ⟨759374, by rfl⟩ : syracuseStep 1012499 = 1518749) B1518749
theorem B1143571 : Blo 674311 1143571 := bstep (se 1 (by rfl) ⟨857678, by rfl⟩ : syracuseStep 1143571 = 1715357) B1715357
theorem B1012529 : Blo 674311 1012529 := bstep (se 2 (by rfl) ⟨379698, by rfl⟩ : syracuseStep 1012529 = 759397) B759397
theorem B1012547 : Blo 674311 1012547 := bstep (se 1 (by rfl) ⟨759410, by rfl⟩ : syracuseStep 1012547 = 1518821) B1518821
theorem B1012577 : Blo 674311 1012577 := bstep (se 2 (by rfl) ⟨379716, by rfl⟩ : syracuseStep 1012577 = 759433) B759433
theorem B1012595 : Blo 674311 1012595 := bstep (se 1 (by rfl) ⟨759446, by rfl⟩ : syracuseStep 1012595 = 1518893) B1518893
theorem B1012625 : Blo 674311 1012625 := bstep (se 2 (by rfl) ⟨379734, by rfl⟩ : syracuseStep 1012625 = 759469) B759469
theorem B914323 : Blo 674311 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B1143713 : Blo 674311 1143713 := bstep (se 2 (by rfl) ⟨428892, by rfl⟩ : syracuseStep 1143713 = 857785) B857785
theorem B1012643 : Blo 674311 1012643 := bstep (se 1 (by rfl) ⟨759482, by rfl⟩ : syracuseStep 1012643 = 1518965) B1518965
theorem B1012673 : Blo 674311 1012673 := bstep (se 2 (by rfl) ⟨379752, by rfl⟩ : syracuseStep 1012673 = 759505) B759505
theorem B1012691 : Blo 674311 1012691 := bstep (se 1 (by rfl) ⟨759518, by rfl⟩ : syracuseStep 1012691 = 1519037) B1519037
theorem B1012721 : Blo 674311 1012721 := bstep (se 2 (by rfl) ⟨379770, by rfl⟩ : syracuseStep 1012721 = 759541) B759541
theorem B1012739 : Blo 674311 1012739 := bstep (se 1 (by rfl) ⟨759554, by rfl⟩ : syracuseStep 1012739 = 1519109) B1519109
theorem B1012769 : Blo 674311 1012769 := bstep (se 2 (by rfl) ⟨379788, by rfl⟩ : syracuseStep 1012769 = 759577) B759577
theorem B1143841 : Blo 674311 1143841 := bstep (se 2 (by rfl) ⟨428940, by rfl⟩ : syracuseStep 1143841 = 857881) B857881
theorem B1012787 : Blo 674311 1012787 := bstep (se 1 (by rfl) ⟨759590, by rfl⟩ : syracuseStep 1012787 = 1519181) B1519181
theorem B1143875 : Blo 674311 1143875 := bstep (se 1 (by rfl) ⟨857906, by rfl⟩ : syracuseStep 1143875 = 1715813) B1715813
theorem B1012817 : Blo 674311 1012817 := bstep (se 2 (by rfl) ⟨379806, by rfl⟩ : syracuseStep 1012817 = 759613) B759613
theorem B1012835 : Blo 674311 1012835 := bstep (se 1 (by rfl) ⟨759626, by rfl⟩ : syracuseStep 1012835 = 1519253) B1519253
theorem B1012865 : Blo 674311 1012865 := bstep (se 2 (by rfl) ⟨379824, by rfl⟩ : syracuseStep 1012865 = 759649) B759649
theorem B1012883 : Blo 674311 1012883 := bstep (se 1 (by rfl) ⟨759662, by rfl⟩ : syracuseStep 1012883 = 1519325) B1519325
theorem B1012913 : Blo 674311 1012913 := bstep (se 2 (by rfl) ⟨379842, by rfl⟩ : syracuseStep 1012913 = 759685) B759685
theorem B1012931 : Blo 674311 1012931 := bstep (se 1 (by rfl) ⟨759698, by rfl⟩ : syracuseStep 1012931 = 1519397) B1519397
theorem B1144003 : Blo 674311 1144003 := bstep (se 1 (by rfl) ⟨858002, by rfl⟩ : syracuseStep 1144003 = 1716005) B1716005
theorem B1012961 : Blo 674311 1012961 := bstep (se 2 (by rfl) ⟨379860, by rfl⟩ : syracuseStep 1012961 = 759721) B759721
theorem B1012979 : Blo 674311 1012979 := bstep (se 1 (by rfl) ⟨759734, by rfl⟩ : syracuseStep 1012979 = 1519469) B1519469
theorem B1013009 : Blo 674311 1013009 := bstep (se 2 (by rfl) ⟨379878, by rfl⟩ : syracuseStep 1013009 = 759757) B759757
theorem B1013027 : Blo 674311 1013027 := bstep (se 1 (by rfl) ⟨759770, by rfl⟩ : syracuseStep 1013027 = 1519541) B1519541
theorem B1013057 : Blo 674311 1013057 := bstep (se 2 (by rfl) ⟨379896, by rfl⟩ : syracuseStep 1013057 = 759793) B759793
theorem B1144145 : Blo 674311 1144145 := bstep (se 2 (by rfl) ⟨429054, by rfl⟩ : syracuseStep 1144145 = 858109) B858109
theorem B1013075 : Blo 674311 1013075 := bstep (se 1 (by rfl) ⟨759806, by rfl⟩ : syracuseStep 1013075 = 1519613) B1519613
theorem B1013105 : Blo 674311 1013105 := bstep (se 2 (by rfl) ⟨379914, by rfl⟩ : syracuseStep 1013105 = 759829) B759829
theorem B1013123 : Blo 674311 1013123 := bstep (se 1 (by rfl) ⟨759842, by rfl⟩ : syracuseStep 1013123 = 1519685) B1519685
theorem B1013153 : Blo 674311 1013153 := bstep (se 2 (by rfl) ⟨379932, by rfl⟩ : syracuseStep 1013153 = 759865) B759865
theorem B1013171 : Blo 674311 1013171 := bstep (se 1 (by rfl) ⟨759878, by rfl⟩ : syracuseStep 1013171 = 1519757) B1519757
theorem B1013201 : Blo 674311 1013201 := bstep (se 2 (by rfl) ⟨379950, by rfl⟩ : syracuseStep 1013201 = 759901) B759901
theorem B1144273 : Blo 674311 1144273 := bstep (se 2 (by rfl) ⟨429102, by rfl⟩ : syracuseStep 1144273 = 858205) B858205
theorem B1013219 : Blo 674311 1013219 := bstep (se 1 (by rfl) ⟨759914, by rfl⟩ : syracuseStep 1013219 = 1519829) B1519829
theorem B1144307 : Blo 674311 1144307 := bstep (se 1 (by rfl) ⟨858230, by rfl⟩ : syracuseStep 1144307 = 1716461) B1716461
theorem B1013249 : Blo 674311 1013249 := bstep (se 2 (by rfl) ⟨379968, by rfl⟩ : syracuseStep 1013249 = 759937) B759937
theorem B4388357 : Blo 674311 4388357 := bstep (se 4 (by rfl) ⟨411408, by rfl⟩ : syracuseStep 4388357 = 822817) B822817
theorem B1013267 : Blo 674311 1013267 := bstep (se 1 (by rfl) ⟨759950, by rfl⟩ : syracuseStep 1013267 = 1519901) B1519901
theorem B1013297 : Blo 674311 1013297 := bstep (se 2 (by rfl) ⟨379986, by rfl⟩ : syracuseStep 1013297 = 759973) B759973
theorem B1013315 : Blo 674311 1013315 := bstep (se 1 (by rfl) ⟨759986, by rfl⟩ : syracuseStep 1013315 = 1519973) B1519973
theorem B1013345 : Blo 674311 1013345 := bstep (se 2 (by rfl) ⟨380004, by rfl⟩ : syracuseStep 1013345 = 760009) B760009
theorem B1013363 : Blo 674311 1013363 := bstep (se 1 (by rfl) ⟨760022, by rfl⟩ : syracuseStep 1013363 = 1520045) B1520045
theorem B1144435 : Blo 674311 1144435 := bstep (se 1 (by rfl) ⟨858326, by rfl⟩ : syracuseStep 1144435 = 1716653) B1716653
theorem B1013393 : Blo 674311 1013393 := bstep (se 2 (by rfl) ⟨380022, by rfl⟩ : syracuseStep 1013393 = 760045) B760045
theorem B1013411 : Blo 674311 1013411 := bstep (se 1 (by rfl) ⟨760058, by rfl⟩ : syracuseStep 1013411 = 1520117) B1520117
theorem B1013441 : Blo 674311 1013441 := bstep (se 2 (by rfl) ⟨380040, by rfl⟩ : syracuseStep 1013441 = 760081) B760081
theorem B1013459 : Blo 674311 1013459 := bstep (se 1 (by rfl) ⟨760094, by rfl⟩ : syracuseStep 1013459 = 1520189) B1520189
theorem B1013489 : Blo 674311 1013489 := bstep (se 2 (by rfl) ⟨380058, by rfl⟩ : syracuseStep 1013489 = 760117) B760117
theorem B1144577 : Blo 674311 1144577 := bstep (se 2 (by rfl) ⟨429216, by rfl⟩ : syracuseStep 1144577 = 858433) B858433
theorem B1013507 : Blo 674311 1013507 := bstep (se 1 (by rfl) ⟨760130, by rfl⟩ : syracuseStep 1013507 = 1520261) B1520261
theorem B1013537 : Blo 674311 1013537 := bstep (se 2 (by rfl) ⟨380076, by rfl⟩ : syracuseStep 1013537 = 760153) B760153
theorem B1931053 : Blo 674311 1931053 := bstep (se 3 (by rfl) ⟨362072, by rfl⟩ : syracuseStep 1931053 = 724145) B724145
theorem B1013555 : Blo 674311 1013555 := bstep (se 1 (by rfl) ⟨760166, by rfl⟩ : syracuseStep 1013555 = 1520333) B1520333
theorem B1013585 : Blo 674311 1013585 := bstep (se 2 (by rfl) ⟨380094, by rfl⟩ : syracuseStep 1013585 = 760189) B760189
theorem B1013603 : Blo 674311 1013603 := bstep (se 1 (by rfl) ⟨760202, by rfl⟩ : syracuseStep 1013603 = 1520405) B1520405
theorem B2062189 : Blo 674311 2062189 := bstep (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) B773321
theorem B1013633 : Blo 674311 1013633 := bstep (se 2 (by rfl) ⟨380112, by rfl⟩ : syracuseStep 1013633 = 760225) B760225
theorem B7796621 : Blo 674311 7796621 := bstep (se 3 (by rfl) ⟨1461866, by rfl⟩ : syracuseStep 7796621 = 2923733) B2923733
theorem B1374097 : Blo 674311 1374097 := bstep (se 2 (by rfl) ⟨515286, by rfl⟩ : syracuseStep 1374097 = 1030573) B1030573
theorem B1013651 : Blo 674311 1013651 := bstep (se 1 (by rfl) ⟨760238, by rfl⟩ : syracuseStep 1013651 = 1520477) B1520477
theorem B1013681 : Blo 674311 1013681 := bstep (se 2 (by rfl) ⟨380130, by rfl⟩ : syracuseStep 1013681 = 760261) B760261
theorem B1013699 : Blo 674311 1013699 := bstep (se 1 (by rfl) ⟨760274, by rfl⟩ : syracuseStep 1013699 = 1520549) B1520549
theorem B1013729 : Blo 674311 1013729 := bstep (se 2 (by rfl) ⟨380148, by rfl⟩ : syracuseStep 1013729 = 760297) B760297
theorem B1013747 : Blo 674311 1013747 := bstep (se 1 (by rfl) ⟨760310, by rfl⟩ : syracuseStep 1013747 = 1520621) B1520621
theorem B1013777 : Blo 674311 1013777 := bstep (se 2 (by rfl) ⟨380166, by rfl⟩ : syracuseStep 1013777 = 760333) B760333
theorem B1013795 : Blo 674311 1013795 := bstep (se 1 (by rfl) ⟨760346, by rfl⟩ : syracuseStep 1013795 = 1520693) B1520693
theorem B2062385 : Blo 674311 2062385 := bstep (se 2 (by rfl) ⟨773394, by rfl⟩ : syracuseStep 2062385 = 1546789) B1546789
theorem B1013825 : Blo 674311 1013825 := bstep (se 2 (by rfl) ⟨380184, by rfl⟩ : syracuseStep 1013825 = 760369) B760369
theorem B1013843 : Blo 674311 1013843 := bstep (se 1 (by rfl) ⟨760382, by rfl⟩ : syracuseStep 1013843 = 1520765) B1520765
theorem B2160749 : Blo 674311 2160749 := bstep (se 3 (by rfl) ⟨405140, by rfl⟩ : syracuseStep 2160749 = 810281) B810281
theorem B1013873 : Blo 674311 1013873 := bstep (se 2 (by rfl) ⟨380202, by rfl⟩ : syracuseStep 1013873 = 760405) B760405
theorem B1013891 : Blo 674311 1013891 := bstep (se 1 (by rfl) ⟨760418, by rfl⟩ : syracuseStep 1013891 = 1520837) B1520837
theorem B3897485 : Blo 674311 3897485 := bstep (se 3 (by rfl) ⟨730778, by rfl⟩ : syracuseStep 3897485 = 1461557) B1461557
theorem B1013921 : Blo 674311 1013921 := bstep (se 2 (by rfl) ⟨380220, by rfl⟩ : syracuseStep 1013921 = 760441) B760441
theorem B1013939 : Blo 674311 1013939 := bstep (se 1 (by rfl) ⟨760454, by rfl⟩ : syracuseStep 1013939 = 1520909) B1520909
theorem B1013969 : Blo 674311 1013969 := bstep (se 2 (by rfl) ⟨380238, by rfl⟩ : syracuseStep 1013969 = 760477) B760477
theorem B1013987 : Blo 674311 1013987 := bstep (se 1 (by rfl) ⟨760490, by rfl⟩ : syracuseStep 1013987 = 1520981) B1520981
theorem B2160877 : Blo 674311 2160877 := bstep (se 3 (by rfl) ⟨405164, by rfl⟩ : syracuseStep 2160877 = 810329) B810329
theorem B1014017 : Blo 674311 1014017 := bstep (se 2 (by rfl) ⟨380256, by rfl⟩ : syracuseStep 1014017 = 760513) B760513
theorem B1014035 : Blo 674311 1014035 := bstep (se 1 (by rfl) ⟨760526, by rfl⟩ : syracuseStep 1014035 = 1521053) B1521053
theorem B1014065 : Blo 674311 1014065 := bstep (se 2 (by rfl) ⟨380274, by rfl⟩ : syracuseStep 1014065 = 760549) B760549
theorem B1014083 : Blo 674311 1014083 := bstep (se 1 (by rfl) ⟨760562, by rfl⟩ : syracuseStep 1014083 = 1521125) B1521125
theorem B1014113 : Blo 674311 1014113 := bstep (se 2 (by rfl) ⟨380292, by rfl⟩ : syracuseStep 1014113 = 760585) B760585
theorem B1014131 : Blo 674311 1014131 := bstep (se 1 (by rfl) ⟨760598, by rfl⟩ : syracuseStep 1014131 = 1521197) B1521197
theorem B1014161 : Blo 674311 1014161 := bstep (se 2 (by rfl) ⟨380310, by rfl⟩ : syracuseStep 1014161 = 760621) B760621
theorem B1014179 : Blo 674311 1014179 := bstep (se 1 (by rfl) ⟨760634, by rfl⟩ : syracuseStep 1014179 = 1521269) B1521269
theorem B1014209 : Blo 674311 1014209 := bstep (se 2 (by rfl) ⟨380328, by rfl⟩ : syracuseStep 1014209 = 760657) B760657
theorem B1014227 : Blo 674311 1014227 := bstep (se 1 (by rfl) ⟨760670, by rfl⟩ : syracuseStep 1014227 = 1521341) B1521341
theorem B3242467 : Blo 674311 3242467 := bstep (se 1 (by rfl) ⟨2431850, by rfl⟩ : syracuseStep 3242467 = 4863701) B4863701
theorem B2161133 : Blo 674311 2161133 := bstep (se 3 (by rfl) ⟨405212, by rfl⟩ : syracuseStep 2161133 = 810425) B810425
theorem B1014257 : Blo 674311 1014257 := bstep (se 2 (by rfl) ⟨380346, by rfl⟩ : syracuseStep 1014257 = 760693) B760693
theorem B1014275 : Blo 674311 1014275 := bstep (se 1 (by rfl) ⟨760706, by rfl⟩ : syracuseStep 1014275 = 1521413) B1521413
theorem B1014305 : Blo 674311 1014305 := bstep (se 2 (by rfl) ⟨380364, by rfl⟩ : syracuseStep 1014305 = 760729) B760729
theorem B1014323 : Blo 674311 1014323 := bstep (se 1 (by rfl) ⟨760742, by rfl⟩ : syracuseStep 1014323 = 1521485) B1521485
theorem B1440337 : Blo 674311 1440337 := bstep (se 2 (by rfl) ⟨540126, by rfl⟩ : syracuseStep 1440337 = 1080253) B1080253
theorem B1014353 : Blo 674311 1014353 := bstep (se 2 (by rfl) ⟨380382, by rfl⟩ : syracuseStep 1014353 = 760765) B760765
theorem B1014371 : Blo 674311 1014371 := bstep (se 1 (by rfl) ⟨760778, by rfl⟩ : syracuseStep 1014371 = 1521557) B1521557
theorem B1014401 : Blo 674311 1014401 := bstep (se 2 (by rfl) ⟨380400, by rfl⟩ : syracuseStep 1014401 = 760801) B760801
theorem B1014419 : Blo 674311 1014419 := bstep (se 1 (by rfl) ⟨760814, by rfl⟩ : syracuseStep 1014419 = 1521629) B1521629
theorem B1014449 : Blo 674311 1014449 := bstep (se 2 (by rfl) ⟨380418, by rfl⟩ : syracuseStep 1014449 = 760837) B760837
theorem B1014467 : Blo 674311 1014467 := bstep (se 1 (by rfl) ⟨760850, by rfl⟩ : syracuseStep 1014467 = 1521701) B1521701
theorem B1014497 : Blo 674311 1014497 := bstep (se 2 (by rfl) ⟨380436, by rfl⟩ : syracuseStep 1014497 = 760873) B760873
theorem B1014515 : Blo 674311 1014515 := bstep (se 1 (by rfl) ⟨760886, by rfl⟩ : syracuseStep 1014515 = 1521773) B1521773
theorem B1014545 : Blo 674311 1014545 := bstep (se 2 (by rfl) ⟨380454, by rfl⟩ : syracuseStep 1014545 = 760909) B760909
theorem B1014563 : Blo 674311 1014563 := bstep (se 1 (by rfl) ⟨760922, by rfl⟩ : syracuseStep 1014563 = 1521845) B1521845
theorem B1014593 : Blo 674311 1014593 := bstep (se 2 (by rfl) ⟨380472, by rfl⟩ : syracuseStep 1014593 = 760945) B760945
theorem B1014611 : Blo 674311 1014611 := bstep (se 1 (by rfl) ⟨760958, by rfl⟩ : syracuseStep 1014611 = 1521917) B1521917
theorem B1014641 : Blo 674311 1014641 := bstep (se 2 (by rfl) ⟨380490, by rfl⟩ : syracuseStep 1014641 = 760981) B760981
theorem B1014659 : Blo 674311 1014659 := bstep (se 1 (by rfl) ⟨760994, by rfl⟩ : syracuseStep 1014659 = 1521989) B1521989
theorem B4881293 : Blo 674311 4881293 := bstep (se 3 (by rfl) ⟨915242, by rfl⟩ : syracuseStep 4881293 = 1830485) B1830485
theorem B1014689 : Blo 674311 1014689 := bstep (se 2 (by rfl) ⟨380508, by rfl⟩ : syracuseStep 1014689 = 761017) B761017
theorem B3242929 : Blo 674311 3242929 := bstep (se 2 (by rfl) ⟨1216098, by rfl⟩ : syracuseStep 3242929 = 2432197) B2432197
theorem B1014707 : Blo 674311 1014707 := bstep (se 1 (by rfl) ⟨761030, by rfl⟩ : syracuseStep 1014707 = 1522061) B1522061
theorem B1014737 : Blo 674311 1014737 := bstep (se 2 (by rfl) ⟨380526, by rfl⟩ : syracuseStep 1014737 = 761053) B761053
theorem B1014755 : Blo 674311 1014755 := bstep (se 1 (by rfl) ⟨761066, by rfl⟩ : syracuseStep 1014755 = 1522133) B1522133
theorem B1014785 : Blo 674311 1014785 := bstep (se 2 (by rfl) ⟨380544, by rfl⟩ : syracuseStep 1014785 = 761089) B761089
theorem B1014803 : Blo 674311 1014803 := bstep (se 1 (by rfl) ⟨761102, by rfl⟩ : syracuseStep 1014803 = 1522205) B1522205
theorem B1014833 : Blo 674311 1014833 := bstep (se 2 (by rfl) ⟨380562, by rfl⟩ : syracuseStep 1014833 = 761125) B761125
theorem B1014851 : Blo 674311 1014851 := bstep (se 1 (by rfl) ⟨761138, by rfl⟩ : syracuseStep 1014851 = 1522277) B1522277
theorem B4684877 : Blo 674311 4684877 := bstep (se 3 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 4684877 = 1756829) B1756829
theorem B1014881 : Blo 674311 1014881 := bstep (se 2 (by rfl) ⟨380580, by rfl⟩ : syracuseStep 1014881 = 761161) B761161
theorem B4881521 : Blo 674311 4881521 := bstep (se 2 (by rfl) ⟨1830570, by rfl⟩ : syracuseStep 4881521 = 3661141) B3661141
theorem B1014899 : Blo 674311 1014899 := bstep (se 1 (by rfl) ⟨761174, by rfl⟩ : syracuseStep 1014899 = 1522349) B1522349
theorem B1014929 : Blo 674311 1014929 := bstep (se 2 (by rfl) ⟨380598, by rfl⟩ : syracuseStep 1014929 = 761197) B761197
theorem B687251 : Blo 674311 687251 := bstep (se 1 (by rfl) ⟨515438, by rfl⟩ : syracuseStep 687251 = 1030877) B1030877
theorem B1014947 : Blo 674311 1014947 := bstep (se 1 (by rfl) ⟨761210, by rfl⟩ : syracuseStep 1014947 = 1522421) B1522421
theorem B1014977 : Blo 674311 1014977 := bstep (se 2 (by rfl) ⟨380616, by rfl⟩ : syracuseStep 1014977 = 761233) B761233
theorem B10386629 : Blo 674311 10386629 := bstep (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) B1947493
theorem B1014995 : Blo 674311 1014995 := bstep (se 1 (by rfl) ⟨761246, by rfl⟩ : syracuseStep 1014995 = 1522493) B1522493
theorem B7699697 : Blo 674311 7699697 := bstep (se 2 (by rfl) ⟨2887386, by rfl⟩ : syracuseStep 7699697 = 5774773) B5774773
theorem B1015025 : Blo 674311 1015025 := bstep (se 2 (by rfl) ⟨380634, by rfl⟩ : syracuseStep 1015025 = 761269) B761269
theorem B1015043 : Blo 674311 1015043 := bstep (se 1 (by rfl) ⟨761282, by rfl⟩ : syracuseStep 1015043 = 1522565) B1522565
theorem B1015073 : Blo 674311 1015073 := bstep (se 2 (by rfl) ⟨380652, by rfl⟩ : syracuseStep 1015073 = 761305) B761305
theorem B1015091 : Blo 674311 1015091 := bstep (se 1 (by rfl) ⟨761318, by rfl⟩ : syracuseStep 1015091 = 1522637) B1522637
theorem B1539409 : Blo 674311 1539409 := bstep (se 2 (by rfl) ⟨577278, by rfl⟩ : syracuseStep 1539409 = 1154557) B1154557
theorem B1015121 : Blo 674311 1015121 := bstep (se 2 (by rfl) ⟨380670, by rfl⟩ : syracuseStep 1015121 = 761341) B761341
theorem B1015139 : Blo 674311 1015139 := bstep (se 1 (by rfl) ⟨761354, by rfl⟩ : syracuseStep 1015139 = 1522709) B1522709
theorem B1015169 : Blo 674311 1015169 := bstep (se 2 (by rfl) ⟨380688, by rfl⟩ : syracuseStep 1015169 = 761377) B761377
theorem B3079565 : Blo 674311 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B1015187 : Blo 674311 1015187 := bstep (se 1 (by rfl) ⟨761390, by rfl⟩ : syracuseStep 1015187 = 1522781) B1522781
theorem B1015217 : Blo 674311 1015217 := bstep (se 2 (by rfl) ⟨380706, by rfl⟩ : syracuseStep 1015217 = 761413) B761413
theorem B1015235 : Blo 674311 1015235 := bstep (se 1 (by rfl) ⟨761426, by rfl⟩ : syracuseStep 1015235 = 1522853) B1522853
theorem B1080785 : Blo 674311 1080785 := bstep (se 2 (by rfl) ⟨405294, by rfl⟩ : syracuseStep 1080785 = 810589) B810589
theorem B1015265 : Blo 674311 1015265 := bstep (se 2 (by rfl) ⟨380724, by rfl⟩ : syracuseStep 1015265 = 761449) B761449
theorem B1015283 : Blo 674311 1015283 := bstep (se 1 (by rfl) ⟨761462, by rfl⟩ : syracuseStep 1015283 = 1522925) B1522925
theorem B1015313 : Blo 674311 1015313 := bstep (se 2 (by rfl) ⟨380742, by rfl⟩ : syracuseStep 1015313 = 761485) B761485
theorem B1015331 : Blo 674311 1015331 := bstep (se 1 (by rfl) ⟨761498, by rfl⟩ : syracuseStep 1015331 = 1522997) B1522997
theorem B1015361 : Blo 674311 1015361 := bstep (se 2 (by rfl) ⟨380760, by rfl⟩ : syracuseStep 1015361 = 761521) B761521
theorem B1015379 : Blo 674311 1015379 := bstep (se 1 (by rfl) ⟨761534, by rfl⟩ : syracuseStep 1015379 = 1523069) B1523069
theorem B2883185 : Blo 674311 2883185 := bstep (se 2 (by rfl) ⟨1081194, by rfl⟩ : syracuseStep 2883185 = 2162389) B2162389
theorem B1015409 : Blo 674311 1015409 := bstep (se 2 (by rfl) ⟨380778, by rfl⟩ : syracuseStep 1015409 = 761557) B761557
theorem B1015427 : Blo 674311 1015427 := bstep (se 1 (by rfl) ⟨761570, by rfl⟩ : syracuseStep 1015427 = 1523141) B1523141
theorem B1015457 : Blo 674311 1015457 := bstep (se 2 (by rfl) ⟨380796, by rfl⟩ : syracuseStep 1015457 = 761593) B761593
theorem B1015475 : Blo 674311 1015475 := bstep (se 1 (by rfl) ⟨761606, by rfl⟩ : syracuseStep 1015475 = 1523213) B1523213
theorem B1015505 : Blo 674311 1015505 := bstep (se 2 (by rfl) ⟨380814, by rfl⟩ : syracuseStep 1015505 = 761629) B761629
theorem B1015523 : Blo 674311 1015523 := bstep (se 1 (by rfl) ⟨761642, by rfl⟩ : syracuseStep 1015523 = 1523285) B1523285
theorem B1081073 : Blo 674311 1081073 := bstep (se 2 (by rfl) ⟨405402, by rfl⟩ : syracuseStep 1081073 = 810805) B810805
theorem B1015553 : Blo 674311 1015553 := bstep (se 2 (by rfl) ⟨380832, by rfl⟩ : syracuseStep 1015553 = 761665) B761665
theorem B1015571 : Blo 674311 1015571 := bstep (se 1 (by rfl) ⟨761678, by rfl⟩ : syracuseStep 1015571 = 1523357) B1523357
theorem B1015601 : Blo 674311 1015601 := bstep (se 2 (by rfl) ⟨380850, by rfl⟩ : syracuseStep 1015601 = 761701) B761701
theorem B1015619 : Blo 674311 1015619 := bstep (se 1 (by rfl) ⟨761714, by rfl⟩ : syracuseStep 1015619 = 1523429) B1523429
theorem B1015649 : Blo 674311 1015649 := bstep (se 2 (by rfl) ⟨380868, by rfl⟩ : syracuseStep 1015649 = 761737) B761737
theorem B1015667 : Blo 674311 1015667 := bstep (se 1 (by rfl) ⟨761750, by rfl⟩ : syracuseStep 1015667 = 1523501) B1523501
theorem B1015697 : Blo 674311 1015697 := bstep (se 2 (by rfl) ⟨380886, by rfl⟩ : syracuseStep 1015697 = 761773) B761773
theorem B1015715 : Blo 674311 1015715 := bstep (se 1 (by rfl) ⟨761786, by rfl⟩ : syracuseStep 1015715 = 1523573) B1523573
theorem B1015745 : Blo 674311 1015745 := bstep (se 2 (by rfl) ⟨380904, by rfl⟩ : syracuseStep 1015745 = 761809) B761809
theorem B3702725 : Blo 674311 3702725 := bstep (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) B694261
theorem B1081297 : Blo 674311 1081297 := bstep (se 2 (by rfl) ⟨405486, by rfl⟩ : syracuseStep 1081297 = 810973) B810973
theorem B1015763 : Blo 674311 1015763 := bstep (se 1 (by rfl) ⟨761822, by rfl⟩ : syracuseStep 1015763 = 1523645) B1523645
theorem B2162659 : Blo 674311 2162659 := bstep (se 1 (by rfl) ⟨1621994, by rfl⟩ : syracuseStep 2162659 = 3243989) B3243989
theorem B1015793 : Blo 674311 1015793 := bstep (se 2 (by rfl) ⟨380922, by rfl⟩ : syracuseStep 1015793 = 761845) B761845
theorem B1015883 : Blo 674311 1015883 := bstep (se 1 (by rfl) ⟨761912, by rfl⟩ : syracuseStep 1015883 = 1523825) B1523825
theorem B1015895 : Blo 674311 1015895 := bstep (se 1 (by rfl) ⟨761921, by rfl⟩ : syracuseStep 1015895 = 1523843) B1523843
theorem B1015961 : Blo 674311 1015961 := bstep (se 2 (by rfl) ⟨380985, by rfl⟩ : syracuseStep 1015961 = 761971) B761971
theorem B1016075 : Blo 674311 1016075 := bstep (se 1 (by rfl) ⟨762056, by rfl⟩ : syracuseStep 1016075 = 1524113) B1524113
theorem B1016087 : Blo 674311 1016087 := bstep (se 1 (by rfl) ⟨762065, by rfl⟩ : syracuseStep 1016087 = 1524131) B1524131
theorem B1016153 : Blo 674311 1016153 := bstep (se 2 (by rfl) ⟨381057, by rfl⟩ : syracuseStep 1016153 = 762115) B762115
theorem B1016267 : Blo 674311 1016267 := bstep (se 1 (by rfl) ⟨762200, by rfl⟩ : syracuseStep 1016267 = 1524401) B1524401
theorem B1016279 : Blo 674311 1016279 := bstep (se 1 (by rfl) ⟨762209, by rfl⟩ : syracuseStep 1016279 = 1524419) B1524419
theorem B1016345 : Blo 674311 1016345 := bstep (se 2 (by rfl) ⟨381129, by rfl⟩ : syracuseStep 1016345 = 762259) B762259
theorem B8553053 : Blo 674311 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B1016459 : Blo 674311 1016459 := bstep (se 1 (by rfl) ⟨762344, by rfl⟩ : syracuseStep 1016459 = 1524689) B1524689
theorem B1016471 : Blo 674311 1016471 := bstep (se 1 (by rfl) ⟨762353, by rfl⟩ : syracuseStep 1016471 = 1524707) B1524707
theorem B1016537 : Blo 674311 1016537 := bstep (se 2 (by rfl) ⟨381201, by rfl⟩ : syracuseStep 1016537 = 762403) B762403
theorem B1016651 : Blo 674311 1016651 := bstep (se 1 (by rfl) ⟨762488, by rfl⟩ : syracuseStep 1016651 = 1524977) B1524977
theorem B1016663 : Blo 674311 1016663 := bstep (se 1 (by rfl) ⟨762497, by rfl⟩ : syracuseStep 1016663 = 1524995) B1524995
theorem B1016729 : Blo 674311 1016729 := bstep (se 2 (by rfl) ⟨381273, by rfl⟩ : syracuseStep 1016729 = 762547) B762547
theorem B6489011 : Blo 674311 6489011 := bstep (se 1 (by rfl) ⟨4866758, by rfl⟩ : syracuseStep 6489011 = 9733517) B9733517
theorem B1016843 : Blo 674311 1016843 := bstep (se 1 (by rfl) ⟨762632, by rfl⟩ : syracuseStep 1016843 = 1525265) B1525265
theorem B1016855 : Blo 674311 1016855 := bstep (se 1 (by rfl) ⟨762641, by rfl⟩ : syracuseStep 1016855 = 1525283) B1525283
theorem B1016921 : Blo 674311 1016921 := bstep (se 2 (by rfl) ⟨381345, by rfl⟩ : syracuseStep 1016921 = 762691) B762691
theorem B1017035 : Blo 674311 1017035 := bstep (se 1 (by rfl) ⟨762776, by rfl⟩ : syracuseStep 1017035 = 1525553) B1525553
theorem B1017047 : Blo 674311 1017047 := bstep (se 1 (by rfl) ⟨762785, by rfl⟩ : syracuseStep 1017047 = 1525571) B1525571
theorem B1541387 : Blo 674311 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B2163991 : Blo 674311 2163991 := bstep (se 1 (by rfl) ⟨1622993, by rfl⟩ : syracuseStep 2163991 = 3245987) B3245987
theorem B1017113 : Blo 674311 1017113 := bstep (se 2 (by rfl) ⟨381417, by rfl⟩ : syracuseStep 1017113 = 762835) B762835
theorem B1017227 : Blo 674311 1017227 := bstep (se 1 (by rfl) ⟨762920, by rfl⟩ : syracuseStep 1017227 = 1525841) B1525841
theorem B1017239 : Blo 674311 1017239 := bstep (se 1 (by rfl) ⟨762929, by rfl⟩ : syracuseStep 1017239 = 1525859) B1525859
theorem B1541555 : Blo 674311 1541555 := bstep (se 1 (by rfl) ⟨1156166, by rfl⟩ : syracuseStep 1541555 = 2312333) B2312333
theorem B1017305 : Blo 674311 1017305 := bstep (se 2 (by rfl) ⟨381489, by rfl⟩ : syracuseStep 1017305 = 762979) B762979
theorem B1017419 : Blo 674311 1017419 := bstep (se 1 (by rfl) ⟨763064, by rfl⟩ : syracuseStep 1017419 = 1526129) B1526129
theorem B1017431 : Blo 674311 1017431 := bstep (se 1 (by rfl) ⟨763073, by rfl⟩ : syracuseStep 1017431 = 1526147) B1526147
theorem B15599537 : Blo 674311 15599537 := bstep (se 2 (by rfl) ⟨5849826, by rfl⟩ : syracuseStep 15599537 = 11699653) B11699653
theorem B1443865 : Blo 674311 1443865 := bstep (se 2 (by rfl) ⟨541449, by rfl⟩ : syracuseStep 1443865 = 1082899) B1082899
theorem B854155 : Blo 674311 854155 := bstep (se 1 (by rfl) ⟨640616, by rfl⟩ : syracuseStep 854155 = 1281233) B1281233
theorem B1280215 : Blo 674311 1280215 := bstep (se 1 (by rfl) ⟨960161, by rfl⟩ : syracuseStep 1280215 = 1920323) B1920323
theorem B6490469 : Blo 674311 6490469 := bstep (se 4 (by rfl) ⟨608481, by rfl⟩ : syracuseStep 6490469 = 1216963) B1216963
theorem B1706903 : Blo 674311 1706903 := bstep (se 1 (by rfl) ⟨1280177, by rfl⟩ : syracuseStep 1706903 = 2560355) B2560355
theorem B723863 : Blo 674311 723863 := bstep (se 1 (by rfl) ⟨542897, by rfl⟩ : syracuseStep 723863 = 1085795) B1085795
theorem B1281035 : Blo 674311 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B1281089 : Blo 674311 1281089 := bstep (se 2 (by rfl) ⟨480408, by rfl⟩ : syracuseStep 1281089 = 960817) B960817
theorem B855127 : Blo 674311 855127 := bstep (se 1 (by rfl) ⟨641345, by rfl⟩ : syracuseStep 855127 = 1282691) B1282691
theorem B2165849 : Blo 674311 2165849 := bstep (se 2 (by rfl) ⟨812193, by rfl⟩ : syracuseStep 2165849 = 1624387) B1624387
theorem B3247235 : Blo 674311 3247235 := bstep (se 1 (by rfl) ⟨2435426, by rfl⟩ : syracuseStep 3247235 = 4870853) B4870853
theorem B1215767 : Blo 674311 1215767 := bstep (se 1 (by rfl) ⟨911825, by rfl⟩ : syracuseStep 1215767 = 1823651) B1823651
theorem B2886977 : Blo 674311 2886977 := bstep (se 2 (by rfl) ⟨1082616, by rfl⟩ : syracuseStep 2886977 = 2165233) B2165233
theorem B5868875 : Blo 674311 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B5770673 : Blo 674311 5770673 := bstep (se 2 (by rfl) ⟨2164002, by rfl⟩ : syracuseStep 5770673 = 4328005) B4328005
theorem B2887319 : Blo 674311 2887319 := bstep (se 1 (by rfl) ⟨2165489, by rfl⟩ : syracuseStep 2887319 = 4330979) B4330979
theorem B1707713 : Blo 674311 1707713 := bstep (se 2 (by rfl) ⟨640392, by rfl⟩ : syracuseStep 1707713 = 1280785) B1280785
theorem B1216243 : Blo 674311 1216243 := bstep (se 1 (by rfl) ⟨912182, by rfl⟩ : syracuseStep 1216243 = 1824365) B1824365
theorem B1543961 : Blo 674311 1543961 := bstep (se 2 (by rfl) ⟨578985, by rfl⟩ : syracuseStep 1543961 = 1157971) B1157971
theorem B855947 : Blo 674311 855947 := bstep (se 1 (by rfl) ⟨641960, by rfl⟩ : syracuseStep 855947 = 1283921) B1283921
theorem B1282007 : Blo 674311 1282007 := bstep (se 1 (by rfl) ⟨961505, by rfl⟩ : syracuseStep 1282007 = 1923011) B1923011
theorem B5771357 : Blo 674311 5771357 := bstep (se 3 (by rfl) ⟨1082129, by rfl⟩ : syracuseStep 5771357 = 2164259) B2164259
theorem B1446017 : Blo 674311 1446017 := bstep (se 2 (by rfl) ⟨542256, by rfl⟩ : syracuseStep 1446017 = 1084513) B1084513
theorem B1446103 : Blo 674311 1446103 := bstep (se 1 (by rfl) ⟨1084577, by rfl⟩ : syracuseStep 1446103 = 2169155) B2169155
theorem B1708249 : Blo 674311 1708249 := bstep (se 2 (by rfl) ⟨640593, by rfl⟩ : syracuseStep 1708249 = 1281187) B1281187
theorem B12357953 : Blo 674311 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B1544599 : Blo 674311 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B1282547 : Blo 674311 1282547 := bstep (se 1 (by rfl) ⟨961910, by rfl⟩ : syracuseStep 1282547 = 1923821) B1923821
theorem B2888243 : Blo 674311 2888243 := bstep (se 1 (by rfl) ⟨2166182, by rfl⟩ : syracuseStep 2888243 = 4332365) B4332365
theorem B856651 : Blo 674311 856651 := bstep (se 1 (by rfl) ⟨642488, by rfl⟩ : syracuseStep 856651 = 1284977) B1284977
theorem B20845187 : Blo 674311 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B2560643 : Blo 674311 2560643 := bstep (se 1 (by rfl) ⟨1920482, by rfl⟩ : syracuseStep 2560643 = 3840965) B3840965
theorem B3085003 : Blo 674311 3085003 := bstep (se 1 (by rfl) ⟨2313752, by rfl⟩ : syracuseStep 3085003 = 4627505) B4627505
theorem B856919 : Blo 674311 856919 := bstep (se 1 (by rfl) ⟨642689, by rfl⟩ : syracuseStep 856919 = 1285379) B1285379
theorem B758731 : Blo 674311 758731 := bstep (se 1 (by rfl) ⟨569048, by rfl⟩ : syracuseStep 758731 = 1138097) B1138097
theorem B1283033 : Blo 674311 1283033 := bstep (se 2 (by rfl) ⟨481137, by rfl⟩ : syracuseStep 1283033 = 962275) B962275
theorem B1446923 : Blo 674311 1446923 := bstep (se 1 (by rfl) ⟨1085192, by rfl⟩ : syracuseStep 1446923 = 2170385) B2170385
theorem B758839 : Blo 674311 758839 := bstep (se 1 (by rfl) ⟨569129, by rfl⟩ : syracuseStep 758839 = 1138259) B1138259
theorem B1217729 : Blo 674311 1217729 := bstep (se 2 (by rfl) ⟨456648, by rfl⟩ : syracuseStep 1217729 = 913297) B913297
theorem B759019 : Blo 674311 759019 := bstep (se 1 (by rfl) ⟨569264, by rfl⟩ : syracuseStep 759019 = 1138529) B1138529
theorem B1709363 : Blo 674311 1709363 := bstep (se 1 (by rfl) ⟨1282022, by rfl⟩ : syracuseStep 1709363 = 2564045) B2564045
theorem B759127 : Blo 674311 759127 := bstep (se 1 (by rfl) ⟨569345, by rfl⟩ : syracuseStep 759127 = 1138691) B1138691
theorem B4330853 : Blo 674311 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B3478963 : Blo 674311 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B759307 : Blo 674311 759307 := bstep (se 1 (by rfl) ⟨569480, by rfl⟩ : syracuseStep 759307 = 1138961) B1138961
theorem B2889233 : Blo 674311 2889233 := bstep (se 2 (by rfl) ⟨1083462, by rfl⟩ : syracuseStep 2889233 = 2166925) B2166925
theorem B857623 : Blo 674311 857623 := bstep (se 1 (by rfl) ⟨643217, by rfl⟩ : syracuseStep 857623 = 1286435) B1286435
theorem B1709657 : Blo 674311 1709657 := bstep (se 2 (by rfl) ⟨641121, by rfl⟩ : syracuseStep 1709657 = 1282243) B1282243
theorem B759415 : Blo 674311 759415 := bstep (se 1 (by rfl) ⟨569561, by rfl⟩ : syracuseStep 759415 = 1139123) B1139123
theorem B759595 : Blo 674311 759595 := bstep (se 1 (by rfl) ⟨569696, by rfl⟩ : syracuseStep 759595 = 1139393) B1139393
theorem B3413825 : Blo 674311 3413825 := bstep (se 2 (by rfl) ⟨1280184, by rfl⟩ : syracuseStep 3413825 = 2560369) B2560369
theorem B4331339 : Blo 674311 4331339 := bstep (se 1 (by rfl) ⟨3248504, by rfl⟩ : syracuseStep 4331339 = 6497009) B6497009
theorem B759703 : Blo 674311 759703 := bstep (se 1 (by rfl) ⟨569777, by rfl⟩ : syracuseStep 759703 = 1139555) B1139555
theorem B1447897 : Blo 674311 1447897 := bstep (se 2 (by rfl) ⟨542961, by rfl⟩ : syracuseStep 1447897 = 1085923) B1085923
theorem B759883 : Blo 674311 759883 := bstep (se 1 (by rfl) ⟨569912, by rfl⟩ : syracuseStep 759883 = 1139825) B1139825
theorem B759991 : Blo 674311 759991 := bstep (se 1 (by rfl) ⟨569993, by rfl⟩ : syracuseStep 759991 = 1139987) B1139987
theorem B1644875 : Blo 674311 1644875 := bstep (se 1 (by rfl) ⟨1233656, by rfl⟩ : syracuseStep 1644875 = 2467313) B2467313
theorem B11573603 : Blo 674311 11573603 := bstep (se 1 (by rfl) ⟨8680202, by rfl⟩ : syracuseStep 11573603 = 17360405) B17360405
theorem B760171 : Blo 674311 760171 := bstep (se 1 (by rfl) ⟨570128, by rfl⟩ : syracuseStep 760171 = 1140257) B1140257
theorem B1284491 : Blo 674311 1284491 := bstep (se 1 (by rfl) ⟨963368, by rfl⟩ : syracuseStep 1284491 = 1926737) B1926737
theorem B4004275 : Blo 674311 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B760279 : Blo 674311 760279 := bstep (se 1 (by rfl) ⟨570209, by rfl⟩ : syracuseStep 760279 = 1140419) B1140419
theorem B1219097 : Blo 674311 1219097 := bstep (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) B914323
theorem B1284673 : Blo 674311 1284673 := bstep (se 2 (by rfl) ⟨481752, by rfl⟩ : syracuseStep 1284673 = 963505) B963505
theorem B760459 : Blo 674311 760459 := bstep (se 1 (by rfl) ⟨570344, by rfl⟩ : syracuseStep 760459 = 1140689) B1140689
theorem B760567 : Blo 674311 760567 := bstep (se 1 (by rfl) ⟨570425, by rfl⟩ : syracuseStep 760567 = 1140851) B1140851
theorem B2595673 : Blo 674311 2595673 := bstep (se 2 (by rfl) ⟨973377, by rfl⟩ : syracuseStep 2595673 = 1946755) B1946755
theorem B760747 : Blo 674311 760747 := bstep (se 1 (by rfl) ⟨570560, by rfl⟩ : syracuseStep 760747 = 1141121) B1141121
theorem B1285121 : Blo 674311 1285121 := bstep (se 2 (by rfl) ⟨481920, by rfl⟩ : syracuseStep 1285121 = 963841) B963841
theorem B760855 : Blo 674311 760855 := bstep (se 1 (by rfl) ⟨570641, by rfl⟩ : syracuseStep 760855 = 1141283) B1141283
theorem B2169949 : Blo 674311 2169949 := bstep (se 3 (by rfl) ⟨406865, by rfl⟩ : syracuseStep 2169949 = 813731) B813731
theorem B1711307 : Blo 674311 1711307 := bstep (se 1 (by rfl) ⟨1283480, by rfl⟩ : syracuseStep 1711307 = 2566961) B2566961
theorem B761035 : Blo 674311 761035 := bstep (se 1 (by rfl) ⟨570776, by rfl⟩ : syracuseStep 761035 = 1141553) B1141553
theorem B1154263 : Blo 674311 1154263 := bstep (se 1 (by rfl) ⟨865697, by rfl⟩ : syracuseStep 1154263 = 1731395) B1731395
theorem B62594309 : Blo 674311 62594309 := bstep (se 4 (by rfl) ⟨5868216, by rfl⟩ : syracuseStep 62594309 = 11736433) B11736433
theorem B761143 : Blo 674311 761143 := bstep (se 1 (by rfl) ⟨570857, by rfl⟩ : syracuseStep 761143 = 1141715) B1141715
theorem B1285463 : Blo 674311 1285463 := bstep (se 1 (by rfl) ⟨964097, by rfl⟩ : syracuseStep 1285463 = 1928195) B1928195
theorem B761323 : Blo 674311 761323 := bstep (se 1 (by rfl) ⟨570992, by rfl⟩ : syracuseStep 761323 = 1141985) B1141985
theorem B761431 : Blo 674311 761431 := bstep (se 1 (by rfl) ⟨571073, by rfl⟩ : syracuseStep 761431 = 1142147) B1142147
theorem B2563757 : Blo 674311 2563757 := bstep (se 3 (by rfl) ⟨480704, by rfl⟩ : syracuseStep 2563757 = 961409) B961409
theorem B3415769 : Blo 674311 3415769 := bstep (se 2 (by rfl) ⟨1280913, by rfl⟩ : syracuseStep 3415769 = 2561827) B2561827
theorem B761611 : Blo 674311 761611 := bstep (se 1 (by rfl) ⟨571208, by rfl⟩ : syracuseStep 761611 = 1142417) B1142417
theorem B2891609 : Blo 674311 2891609 := bstep (se 2 (by rfl) ⟨1084353, by rfl⟩ : syracuseStep 2891609 = 2168707) B2168707
theorem B761719 : Blo 674311 761719 := bstep (se 1 (by rfl) ⟨571289, by rfl⟩ : syracuseStep 761719 = 1142579) B1142579
theorem B4169603 : Blo 674311 4169603 := bstep (se 1 (by rfl) ⟨3127202, by rfl⟩ : syracuseStep 4169603 = 6254405) B6254405
theorem B2891693 : Blo 674311 2891693 := bstep (se 3 (by rfl) ⟨542192, by rfl⟩ : syracuseStep 2891693 = 1084385) B1084385
theorem B1286131 : Blo 674311 1286131 := bstep (se 1 (by rfl) ⟨964598, by rfl⟩ : syracuseStep 1286131 = 1929197) B1929197
theorem B761899 : Blo 674311 761899 := bstep (se 1 (by rfl) ⟨571424, by rfl⟩ : syracuseStep 761899 = 1142849) B1142849
theorem B1712279 : Blo 674311 1712279 := bstep (se 1 (by rfl) ⟨1284209, by rfl⟩ : syracuseStep 1712279 = 2568419) B2568419
theorem B762007 : Blo 674311 762007 := bstep (se 1 (by rfl) ⟨571505, by rfl⟩ : syracuseStep 762007 = 1143011) B1143011
theorem B762187 : Blo 674311 762187 := bstep (se 1 (by rfl) ⟨571640, by rfl⟩ : syracuseStep 762187 = 1143281) B1143281
theorem B2564531 : Blo 674311 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B1286579 : Blo 674311 1286579 := bstep (se 1 (by rfl) ⟨964934, by rfl⟩ : syracuseStep 1286579 = 1929869) B1929869
theorem B762295 : Blo 674311 762295 := bstep (se 1 (by rfl) ⟨571721, by rfl⟩ : syracuseStep 762295 = 1143443) B1143443
theorem B1286617 : Blo 674311 1286617 := bstep (se 2 (by rfl) ⟨482481, by rfl⟩ : syracuseStep 1286617 = 964963) B964963
theorem B2433581 : Blo 674311 2433581 := bstep (se 3 (by rfl) ⟨456296, by rfl⟩ : syracuseStep 2433581 = 912593) B912593
theorem B762475 : Blo 674311 762475 := bstep (se 1 (by rfl) ⟨571856, by rfl⟩ : syracuseStep 762475 = 1143713) B1143713
theorem B762583 : Blo 674311 762583 := bstep (se 1 (by rfl) ⟨571937, by rfl⟩ : syracuseStep 762583 = 1143875) B1143875
theorem B1712947 : Blo 674311 1712947 := bstep (se 1 (by rfl) ⟨1284710, by rfl⟩ : syracuseStep 1712947 = 2569421) B2569421
theorem B762763 : Blo 674311 762763 := bstep (se 1 (by rfl) ⟨572072, by rfl⟩ : syracuseStep 762763 = 1144145) B1144145
theorem B1287065 : Blo 674311 1287065 := bstep (se 2 (by rfl) ⟨482649, by rfl⟩ : syracuseStep 1287065 = 965299) B965299
theorem B1713089 : Blo 674311 1713089 := bstep (se 2 (by rfl) ⟨642408, by rfl⟩ : syracuseStep 1713089 = 1284817) B1284817
theorem B762871 : Blo 674311 762871 := bstep (se 1 (by rfl) ⟨572153, by rfl⟩ : syracuseStep 762871 = 1144307) B1144307
theorem B2925571 : Blo 674311 2925571 := bstep (se 1 (by rfl) ⟨2194178, by rfl⟩ : syracuseStep 2925571 = 4388357) B4388357
theorem B763051 : Blo 674311 763051 := bstep (se 1 (by rfl) ⟨572288, by rfl⟩ : syracuseStep 763051 = 1144577) B1144577
theorem B4334771 : Blo 674311 4334771 := bstep (se 1 (by rfl) ⟨3251078, by rfl⟩ : syracuseStep 4334771 = 6502157) B6502157
theorem B3417389 : Blo 674311 3417389 := bstep (se 3 (by rfl) ⟨640760, by rfl⟩ : syracuseStep 3417389 = 1281521) B1281521
theorem B6169931 : Blo 674311 6169931 := bstep (se 1 (by rfl) ⟨4627448, by rfl⟩ : syracuseStep 6169931 = 9254897) B9254897
theorem B2598323 : Blo 674311 2598323 := bstep (se 1 (by rfl) ⟨1948742, by rfl⟩ : syracuseStep 2598323 = 3897485) B3897485
theorem B5219801 : Blo 674311 5219801 := bstep (se 2 (by rfl) ⟨1957425, by rfl⟩ : syracuseStep 5219801 = 3914851) B3914851
theorem B1517273 : Blo 674311 1517273 := bstep (se 2 (by rfl) ⟨568977, by rfl⟩ : syracuseStep 1517273 = 1137955) B1137955
theorem B1517363 : Blo 674311 1517363 := bstep (se 1 (by rfl) ⟨1138022, by rfl⟩ : syracuseStep 1517363 = 2276045) B2276045
theorem B1517399 : Blo 674311 1517399 := bstep (se 1 (by rfl) ⟨1138049, by rfl⟩ : syracuseStep 1517399 = 2276099) B2276099
theorem B2566019 : Blo 674311 2566019 := bstep (se 1 (by rfl) ⟨1924514, by rfl⟩ : syracuseStep 2566019 = 3849029) B3849029
theorem B2434967 : Blo 674311 2434967 := bstep (se 1 (by rfl) ⟨1826225, by rfl⟩ : syracuseStep 2434967 = 3652451) B3652451
theorem B3254195 : Blo 674311 3254195 := bstep (se 1 (by rfl) ⟨2440646, by rfl⟩ : syracuseStep 3254195 = 4881293) B4881293
theorem B1517579 : Blo 674311 1517579 := bstep (se 1 (by rfl) ⟨1138184, by rfl⟩ : syracuseStep 1517579 = 2276369) B2276369
theorem B3123251 : Blo 674311 3123251 := bstep (se 1 (by rfl) ⟨2342438, by rfl⟩ : syracuseStep 3123251 = 4684877) B4684877
theorem B1517633 : Blo 674311 1517633 := bstep (se 2 (by rfl) ⟨569112, by rfl⟩ : syracuseStep 1517633 = 1138225) B1138225
theorem B3254347 : Blo 674311 3254347 := bstep (se 1 (by rfl) ⟨2440760, by rfl⟩ : syracuseStep 3254347 = 4881521) B4881521
theorem B6924419 : Blo 674311 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B1321099 : Blo 674311 1321099 := bstep (se 1 (by rfl) ⟨990824, by rfl⟩ : syracuseStep 1321099 = 1981649) B1981649
theorem B1714355 : Blo 674311 1714355 := bstep (se 1 (by rfl) ⟨1285766, by rfl⟩ : syracuseStep 1714355 = 2571533) B2571533
theorem B1386713 : Blo 674311 1386713 := bstep (se 2 (by rfl) ⟨520017, by rfl⟩ : syracuseStep 1386713 = 1040035) B1040035
theorem B1517849 : Blo 674311 1517849 := bstep (se 2 (by rfl) ⟨569193, by rfl⟩ : syracuseStep 1517849 = 1138387) B1138387
theorem B2566475 : Blo 674311 2566475 := bstep (se 1 (by rfl) ⟨1924856, by rfl⟩ : syracuseStep 2566475 = 3849713) B3849713
theorem B1517939 : Blo 674311 1517939 := bstep (se 1 (by rfl) ⟨1138454, by rfl⟩ : syracuseStep 1517939 = 2276909) B2276909
theorem B1517975 : Blo 674311 1517975 := bstep (se 1 (by rfl) ⟨1138481, by rfl⟩ : syracuseStep 1517975 = 2276963) B2276963
theorem B2566673 : Blo 674311 2566673 := bstep (se 2 (by rfl) ⟨962502, by rfl⟩ : syracuseStep 2566673 = 1925005) B1925005
theorem B3254849 : Blo 674311 3254849 := bstep (se 2 (by rfl) ⟨1220568, by rfl⟩ : syracuseStep 3254849 = 2441137) B2441137
theorem B1518155 : Blo 674311 1518155 := bstep (se 1 (by rfl) ⟨1138616, by rfl⟩ : syracuseStep 1518155 = 2277233) B2277233
theorem B1518209 : Blo 674311 1518209 := bstep (se 2 (by rfl) ⟨569328, by rfl⟩ : syracuseStep 1518209 = 1138657) B1138657
theorem B2468483 : Blo 674311 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B1714891 : Blo 674311 1714891 := bstep (se 1 (by rfl) ⟨1286168, by rfl⟩ : syracuseStep 1714891 = 2572337) B2572337
theorem B1518425 : Blo 674311 1518425 := bstep (se 2 (by rfl) ⟨569409, by rfl⟩ : syracuseStep 1518425 = 1138819) B1138819
theorem B1715033 : Blo 674311 1715033 := bstep (se 2 (by rfl) ⟨643137, by rfl⟩ : syracuseStep 1715033 = 1286275) B1286275
theorem B1518515 : Blo 674311 1518515 := bstep (se 1 (by rfl) ⟨1138886, by rfl⟩ : syracuseStep 1518515 = 2277773) B2277773
theorem B961483 : Blo 674311 961483 := bstep (se 1 (by rfl) ⟨721112, by rfl⟩ : syracuseStep 961483 = 1442225) B1442225
theorem B1518551 : Blo 674311 1518551 := bstep (se 1 (by rfl) ⟨1138913, by rfl⟩ : syracuseStep 1518551 = 2277827) B2277827
theorem B1518731 : Blo 674311 1518731 := bstep (se 1 (by rfl) ⟨1139048, by rfl⟩ : syracuseStep 1518731 = 2278097) B2278097
theorem B1518785 : Blo 674311 1518785 := bstep (se 2 (by rfl) ⟨569544, by rfl⟩ : syracuseStep 1518785 = 1139089) B1139089
theorem B2895041 : Blo 674311 2895041 := bstep (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) B2171281
theorem B2567447 : Blo 674311 2567447 := bstep (se 1 (by rfl) ⟨1925585, by rfl⟩ : syracuseStep 2567447 = 3851171) B3851171
theorem B4337027 : Blo 674311 4337027 := bstep (se 1 (by rfl) ⟨3252770, by rfl⟩ : syracuseStep 4337027 = 6505541) B6505541
theorem B1519001 : Blo 674311 1519001 := bstep (se 2 (by rfl) ⟨569625, by rfl⟩ : syracuseStep 1519001 = 1139251) B1139251
theorem B2567645 : Blo 674311 2567645 := bstep (se 3 (by rfl) ⟨481433, by rfl⟩ : syracuseStep 2567645 = 962867) B962867
theorem B1519091 : Blo 674311 1519091 := bstep (se 1 (by rfl) ⟨1139318, by rfl⟩ : syracuseStep 1519091 = 2278637) B2278637
theorem B1519127 : Blo 674311 1519127 := bstep (se 1 (by rfl) ⟨1139345, by rfl⟩ : syracuseStep 1519127 = 2278691) B2278691
theorem B1715863 : Blo 674311 1715863 := bstep (se 1 (by rfl) ⟨1286897, by rfl⟩ : syracuseStep 1715863 = 2573795) B2573795
theorem B1519307 : Blo 674311 1519307 := bstep (se 1 (by rfl) ⟨1139480, by rfl⟩ : syracuseStep 1519307 = 2278961) B2278961
theorem B49360589 : Blo 674311 49360589 := bstep (se 3 (by rfl) ⟨9255110, by rfl⟩ : syracuseStep 49360589 = 18510221) B18510221
theorem B1519361 : Blo 674311 1519361 := bstep (se 2 (by rfl) ⟨569760, by rfl⟩ : syracuseStep 1519361 = 1139521) B1139521
theorem B2895709 : Blo 674311 2895709 := bstep (se 3 (by rfl) ⟨542945, by rfl⟩ : syracuseStep 2895709 = 1085891) B1085891
theorem B2600849 : Blo 674311 2600849 := bstep (se 2 (by rfl) ⟨975318, by rfl⟩ : syracuseStep 2600849 = 1950637) B1950637
theorem B1519577 : Blo 674311 1519577 := bstep (se 2 (by rfl) ⟨569841, by rfl⟩ : syracuseStep 1519577 = 1139683) B1139683
theorem B1519667 : Blo 674311 1519667 := bstep (se 1 (by rfl) ⟨1139750, by rfl⟩ : syracuseStep 1519667 = 2279501) B2279501
theorem B1716299 : Blo 674311 1716299 := bstep (se 1 (by rfl) ⟨1287224, by rfl⟩ : syracuseStep 1716299 = 2574449) B2574449
theorem B1519703 : Blo 674311 1519703 := bstep (se 1 (by rfl) ⟨1139777, by rfl⟩ : syracuseStep 1519703 = 2279555) B2279555
theorem B962713 : Blo 674311 962713 := bstep (se 2 (by rfl) ⟨361017, by rfl⟩ : syracuseStep 962713 = 722035) B722035
theorem B1519883 : Blo 674311 1519883 := bstep (se 1 (by rfl) ⟨1139912, by rfl⟩ : syracuseStep 1519883 = 2279825) B2279825
theorem B1159435 : Blo 674311 1159435 := bstep (se 1 (by rfl) ⟨869576, by rfl⟩ : syracuseStep 1159435 = 1739153) B1739153
theorem B3911981 : Blo 674311 3911981 := bstep (se 3 (by rfl) ⟨733496, by rfl⟩ : syracuseStep 3911981 = 1466993) B1466993
theorem B1519937 : Blo 674311 1519937 := bstep (se 2 (by rfl) ⟨569976, by rfl⟩ : syracuseStep 1519937 = 1139953) B1139953
theorem B2896307 : Blo 674311 2896307 := bstep (se 1 (by rfl) ⟨2172230, by rfl⟩ : syracuseStep 2896307 = 4344461) B4344461
theorem B1716673 : Blo 674311 1716673 := bstep (se 2 (by rfl) ⟨643752, by rfl⟩ : syracuseStep 1716673 = 1287505) B1287505
theorem B22196753 : Blo 674311 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B1520153 : Blo 674311 1520153 := bstep (se 2 (by rfl) ⟨570057, by rfl⟩ : syracuseStep 1520153 = 1140115) B1140115
theorem B2437721 : Blo 674311 2437721 := bstep (se 2 (by rfl) ⟨914145, by rfl⟩ : syracuseStep 2437721 = 1828291) B1828291
theorem B1520243 : Blo 674311 1520243 := bstep (se 1 (by rfl) ⟨1140182, by rfl⟩ : syracuseStep 1520243 = 2280365) B2280365
theorem B1520279 : Blo 674311 1520279 := bstep (se 1 (by rfl) ⟨1140209, by rfl⟩ : syracuseStep 1520279 = 2280419) B2280419
theorem B1028759 : Blo 674311 1028759 := bstep (se 1 (by rfl) ⟨771569, by rfl⟩ : syracuseStep 1028759 = 1543139) B1543139
theorem B5124869 : Blo 674311 5124869 := bstep (se 4 (by rfl) ⟨480456, by rfl⟩ : syracuseStep 5124869 = 960913) B960913
theorem B5550923 : Blo 674311 5550923 := bstep (se 1 (by rfl) ⟨4163192, by rfl⟩ : syracuseStep 5550923 = 8326385) B8326385
theorem B1520459 : Blo 674311 1520459 := bstep (se 1 (by rfl) ⟨1140344, by rfl⟩ : syracuseStep 1520459 = 2280689) B2280689
theorem B7811957 : Blo 674311 7811957 := bstep (se 5 (by rfl) ⟨366185, by rfl⟩ : syracuseStep 7811957 = 732371) B732371
theorem B1520513 : Blo 674311 1520513 := bstep (se 2 (by rfl) ⟨570192, by rfl⟩ : syracuseStep 1520513 = 1140385) B1140385
theorem B1651607 : Blo 674311 1651607 := bstep (se 1 (by rfl) ⟨1238705, by rfl⟩ : syracuseStep 1651607 = 2477411) B2477411
theorem B2634713 : Blo 674311 2634713 := bstep (se 2 (by rfl) ⟨988017, by rfl⟩ : syracuseStep 2634713 = 1976035) B1976035
theorem B1586251 : Blo 674311 1586251 := bstep (se 1 (by rfl) ⟨1189688, by rfl⟩ : syracuseStep 1586251 = 2379377) B2379377
theorem B1520729 : Blo 674311 1520729 := bstep (se 2 (by rfl) ⟨570273, by rfl⟩ : syracuseStep 1520729 = 1140547) B1140547
theorem B3421277 : Blo 674311 3421277 := bstep (se 3 (by rfl) ⟨641489, by rfl⟩ : syracuseStep 3421277 = 1282979) B1282979
theorem B1520819 : Blo 674311 1520819 := bstep (se 1 (by rfl) ⟨1140614, by rfl⟩ : syracuseStep 1520819 = 2281229) B2281229
theorem B1520855 : Blo 674311 1520855 := bstep (se 1 (by rfl) ⟨1140641, by rfl⟩ : syracuseStep 1520855 = 2281283) B2281283
theorem B2569603 : Blo 674311 2569603 := bstep (se 1 (by rfl) ⟨1927202, by rfl⟩ : syracuseStep 2569603 = 3854405) B3854405
theorem B1521035 : Blo 674311 1521035 := bstep (se 1 (by rfl) ⟨1140776, by rfl⟩ : syracuseStep 1521035 = 2281553) B2281553
theorem B1521089 : Blo 674311 1521089 := bstep (se 2 (by rfl) ⟨570408, by rfl⟩ : syracuseStep 1521089 = 1140817) B1140817
theorem B964057 : Blo 674311 964057 := bstep (se 2 (by rfl) ⟨361521, by rfl⟩ : syracuseStep 964057 = 723043) B723043
theorem B964171 : Blo 674311 964171 := bstep (se 1 (by rfl) ⟨723128, by rfl⟩ : syracuseStep 964171 = 1446257) B1446257
theorem B1521305 : Blo 674311 1521305 := bstep (se 2 (by rfl) ⟨570489, by rfl⟩ : syracuseStep 1521305 = 1140979) B1140979
theorem B2569907 : Blo 674311 2569907 := bstep (se 1 (by rfl) ⟨1927430, by rfl⟩ : syracuseStep 2569907 = 3854861) B3854861
theorem B1521395 : Blo 674311 1521395 := bstep (se 1 (by rfl) ⟨1141046, by rfl⟩ : syracuseStep 1521395 = 2282093) B2282093
theorem B2438915 : Blo 674311 2438915 := bstep (se 1 (by rfl) ⟨1829186, by rfl⟩ : syracuseStep 2438915 = 3658373) B3658373
theorem B1521431 : Blo 674311 1521431 := bstep (se 1 (by rfl) ⟨1141073, by rfl⟩ : syracuseStep 1521431 = 2282147) B2282147
theorem B2439001 : Blo 674311 2439001 := bstep (se 2 (by rfl) ⟨914625, by rfl⟩ : syracuseStep 2439001 = 1829251) B1829251
theorem B1521611 : Blo 674311 1521611 := bstep (se 1 (by rfl) ⟨1141208, by rfl⟩ : syracuseStep 1521611 = 2282417) B2282417
theorem B1521665 : Blo 674311 1521665 := bstep (se 2 (by rfl) ⟨570624, by rfl⟩ : syracuseStep 1521665 = 1141249) B1141249
theorem B3291211 : Blo 674311 3291211 := bstep (se 1 (by rfl) ⟨2468408, by rfl⟩ : syracuseStep 3291211 = 4936817) B4936817
theorem B1521881 : Blo 674311 1521881 := bstep (se 2 (by rfl) ⟨570705, by rfl⟩ : syracuseStep 1521881 = 1141411) B1141411
theorem B19478789 : Blo 674311 19478789 := bstep (se 4 (by rfl) ⟨1826136, by rfl⟩ : syracuseStep 19478789 = 3652273) B3652273
theorem B1521971 : Blo 674311 1521971 := bstep (se 1 (by rfl) ⟨1141478, by rfl⟩ : syracuseStep 1521971 = 2282957) B2282957
theorem B2570561 : Blo 674311 2570561 := bstep (se 2 (by rfl) ⟨963960, by rfl⟩ : syracuseStep 2570561 = 1927921) B1927921
theorem B1522007 : Blo 674311 1522007 := bstep (se 1 (by rfl) ⟨1141505, by rfl⟩ : syracuseStep 1522007 = 2283011) B2283011
theorem B1030487 : Blo 674311 1030487 := bstep (se 1 (by rfl) ⟨772865, by rfl⟩ : syracuseStep 1030487 = 1545731) B1545731
theorem B56342897 : Blo 674311 56342897 := bstep (se 2 (by rfl) ⟨21128586, by rfl⟩ : syracuseStep 56342897 = 42257173) B42257173
theorem B1620427 : Blo 674311 1620427 := bstep (se 1 (by rfl) ⟨1215320, by rfl⟩ : syracuseStep 1620427 = 2430641) B2430641
theorem B1522187 : Blo 674311 1522187 := bstep (se 1 (by rfl) ⟨1141640, by rfl⟩ : syracuseStep 1522187 = 2283281) B2283281
theorem B1522241 : Blo 674311 1522241 := bstep (se 2 (by rfl) ⟨570840, by rfl⟩ : syracuseStep 1522241 = 1141681) B1141681
theorem B2734667 : Blo 674311 2734667 := bstep (se 1 (by rfl) ⟨2051000, by rfl⟩ : syracuseStep 2734667 = 4102001) B4102001
theorem B2275991 : Blo 674311 2275991 := bstep (se 1 (by rfl) ⟨1706993, by rfl⟩ : syracuseStep 2275991 = 3413987) B3413987
theorem B1522457 : Blo 674311 1522457 := bstep (se 2 (by rfl) ⟨570921, by rfl⟩ : syracuseStep 1522457 = 1141843) B1141843
theorem B3652427 : Blo 674311 3652427 := bstep (se 1 (by rfl) ⟨2739320, by rfl⟩ : syracuseStep 3652427 = 5478641) B5478641
theorem B5192549 : Blo 674311 5192549 := bstep (se 4 (by rfl) ⟨486801, by rfl⟩ : syracuseStep 5192549 = 973603) B973603
theorem B1522547 : Blo 674311 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B965515 : Blo 674311 965515 := bstep (se 1 (by rfl) ⟨724136, by rfl⟩ : syracuseStep 965515 = 1448273) B1448273
theorem B1522583 : Blo 674311 1522583 := bstep (se 1 (by rfl) ⟨1141937, by rfl⟩ : syracuseStep 1522583 = 2283875) B2283875
theorem B2735041 : Blo 674311 2735041 := bstep (se 2 (by rfl) ⟨1025640, by rfl⟩ : syracuseStep 2735041 = 2051281) B2051281
theorem B1621043 : Blo 674311 1621043 := bstep (se 1 (by rfl) ⟨1215782, by rfl⟩ : syracuseStep 1621043 = 2431565) B2431565
theorem B3849281 : Blo 674311 3849281 := bstep (se 2 (by rfl) ⟨1443480, by rfl⟩ : syracuseStep 3849281 = 2886961) B2886961
theorem B1522763 : Blo 674311 1522763 := bstep (se 1 (by rfl) ⟨1142072, by rfl⟩ : syracuseStep 1522763 = 2284145) B2284145
theorem B1522817 : Blo 674311 1522817 := bstep (se 2 (by rfl) ⟨571056, by rfl⟩ : syracuseStep 1522817 = 1142113) B1142113
theorem B5127299 : Blo 674311 5127299 := bstep (se 1 (by rfl) ⟨3845474, by rfl⟩ : syracuseStep 5127299 = 7690949) B7690949
theorem B3423383 : Blo 674311 3423383 := bstep (se 1 (by rfl) ⟨2567537, by rfl⟩ : syracuseStep 3423383 = 5135075) B5135075
theorem B965783 : Blo 674311 965783 := bstep (se 1 (by rfl) ⟨724337, by rfl⟩ : syracuseStep 965783 = 1448675) B1448675
theorem B2276531 : Blo 674311 2276531 := bstep (se 1 (by rfl) ⟨1707398, by rfl⟩ : syracuseStep 2276531 = 3414797) B3414797
theorem B2440385 : Blo 674311 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B2309399 : Blo 674311 2309399 := bstep (se 1 (by rfl) ⟨1732049, by rfl⟩ : syracuseStep 2309399 = 3464099) B3464099
theorem B1523033 : Blo 674311 1523033 := bstep (se 2 (by rfl) ⟨571137, by rfl⟩ : syracuseStep 1523033 = 1142275) B1142275
theorem B1523123 : Blo 674311 1523123 := bstep (se 1 (by rfl) ⟨1142342, by rfl⟩ : syracuseStep 1523123 = 2284685) B2284685
theorem B2276801 : Blo 674311 2276801 := bstep (se 2 (by rfl) ⟨853800, by rfl⟩ : syracuseStep 2276801 = 1707601) B1707601
theorem B1523159 : Blo 674311 1523159 := bstep (se 1 (by rfl) ⟨1142369, by rfl⟩ : syracuseStep 1523159 = 2284739) B2284739
theorem B2571821 : Blo 674311 2571821 := bstep (se 3 (by rfl) ⟨482216, by rfl⟩ : syracuseStep 2571821 = 964433) B964433
theorem B7683659 : Blo 674311 7683659 := bstep (se 1 (by rfl) ⟨5762744, by rfl⟩ : syracuseStep 7683659 = 11525489) B11525489
theorem B2571851 : Blo 674311 2571851 := bstep (se 1 (by rfl) ⟨1928888, by rfl⟩ : syracuseStep 2571851 = 3857777) B3857777
theorem B1523339 : Blo 674311 1523339 := bstep (se 1 (by rfl) ⟨1142504, by rfl⟩ : syracuseStep 1523339 = 2285009) B2285009
theorem B1523393 : Blo 674311 1523393 := bstep (se 2 (by rfl) ⟨571272, by rfl⟩ : syracuseStep 1523393 = 1142545) B1142545
theorem B20790989 : Blo 674311 20790989 := bstep (se 3 (by rfl) ⟨3898310, by rfl⟩ : syracuseStep 20790989 = 7796621) B7796621
theorem B1621849 : Blo 674311 1621849 := bstep (se 2 (by rfl) ⟨608193, by rfl⟩ : syracuseStep 1621849 = 1216387) B1216387
theorem B1523609 : Blo 674311 1523609 := bstep (se 2 (by rfl) ⟨571353, by rfl⟩ : syracuseStep 1523609 = 1142707) B1142707
theorem B2277341 : Blo 674311 2277341 := bstep (se 3 (by rfl) ⟨427001, by rfl⟩ : syracuseStep 2277341 = 854003) B854003
theorem B1523699 : Blo 674311 1523699 := bstep (se 1 (by rfl) ⟨1142774, by rfl⟩ : syracuseStep 1523699 = 2285549) B2285549
theorem B1523735 : Blo 674311 1523735 := bstep (se 1 (by rfl) ⟨1142801, by rfl⟩ : syracuseStep 1523735 = 2285603) B2285603
theorem B1523915 : Blo 674311 1523915 := bstep (se 1 (by rfl) ⟨1142936, by rfl⟩ : syracuseStep 1523915 = 2285873) B2285873
theorem B2572505 : Blo 674311 2572505 := bstep (se 2 (by rfl) ⟨964689, by rfl⟩ : syracuseStep 2572505 = 1929379) B1929379
theorem B1523969 : Blo 674311 1523969 := bstep (se 2 (by rfl) ⟨571488, by rfl⟩ : syracuseStep 1523969 = 1142977) B1142977
theorem B1524185 : Blo 674311 1524185 := bstep (se 2 (by rfl) ⟨571569, by rfl⟩ : syracuseStep 1524185 = 1143139) B1143139
theorem B2572823 : Blo 674311 2572823 := bstep (se 1 (by rfl) ⟨1929617, by rfl⟩ : syracuseStep 2572823 = 3859235) B3859235
theorem B1524275 : Blo 674311 1524275 := bstep (se 1 (by rfl) ⟨1143206, by rfl⟩ : syracuseStep 1524275 = 2286413) B2286413
theorem B1524311 : Blo 674311 1524311 := bstep (se 1 (by rfl) ⟨1143233, by rfl⟩ : syracuseStep 1524311 = 2286467) B2286467
theorem B1393355 : Blo 674311 1393355 := bstep (se 1 (by rfl) ⟨1045016, by rfl⟩ : syracuseStep 1393355 = 2090033) B2090033
theorem B6177485 : Blo 674311 6177485 := bstep (se 3 (by rfl) ⟨1158278, by rfl⟩ : syracuseStep 6177485 = 2316557) B2316557
theorem B79086293 : Blo 674311 79086293 := bstep (se 7 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 79086293 = 1853585) B1853585
theorem B1524491 : Blo 674311 1524491 := bstep (se 1 (by rfl) ⟨1143368, by rfl⟩ : syracuseStep 1524491 = 2286737) B2286737
theorem B1524545 : Blo 674311 1524545 := bstep (se 2 (by rfl) ⟨571704, by rfl⟩ : syracuseStep 1524545 = 1143409) B1143409
theorem B2442059 : Blo 674311 2442059 := bstep (se 1 (by rfl) ⟨1831544, by rfl⟩ : syracuseStep 2442059 = 3663089) B3663089
theorem B1524761 : Blo 674311 1524761 := bstep (se 2 (by rfl) ⟨571785, by rfl⟩ : syracuseStep 1524761 = 1143571) B1143571
theorem B2278475 : Blo 674311 2278475 := bstep (se 1 (by rfl) ⟨1708856, by rfl⟩ : syracuseStep 2278475 = 3417713) B3417713
theorem B1524851 : Blo 674311 1524851 := bstep (se 1 (by rfl) ⟨1143638, by rfl⟩ : syracuseStep 1524851 = 2287277) B2287277
theorem B1524887 : Blo 674311 1524887 := bstep (se 1 (by rfl) ⟨1143665, by rfl⟩ : syracuseStep 1524887 = 2287331) B2287331
theorem B2573491 : Blo 674311 2573491 := bstep (se 1 (by rfl) ⟨1930118, by rfl⟩ : syracuseStep 2573491 = 3860237) B3860237
theorem B1525067 : Blo 674311 1525067 := bstep (se 1 (by rfl) ⟨1143800, by rfl⟩ : syracuseStep 1525067 = 2287601) B2287601
theorem B2278745 : Blo 674311 2278745 := bstep (se 2 (by rfl) ⟨854529, by rfl⟩ : syracuseStep 2278745 = 1709059) B1709059
theorem B1525121 : Blo 674311 1525121 := bstep (se 2 (by rfl) ⟨571920, by rfl⟩ : syracuseStep 1525121 = 1143841) B1143841
theorem B3655043 : Blo 674311 3655043 := bstep (se 1 (by rfl) ⟨2741282, by rfl⟩ : syracuseStep 3655043 = 5482565) B5482565
theorem B3851671 : Blo 674311 3851671 := bstep (se 1 (by rfl) ⟨2888753, by rfl⟩ : syracuseStep 3851671 = 5777507) B5777507
theorem B1754561 : Blo 674311 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B771607 : Blo 674311 771607 := bstep (se 1 (by rfl) ⟨578705, by rfl⟩ : syracuseStep 771607 = 1157411) B1157411
theorem B1951283 : Blo 674311 1951283 := bstep (se 1 (by rfl) ⟨1463462, by rfl⟩ : syracuseStep 1951283 = 2926925) B2926925
theorem B1525337 : Blo 674311 1525337 := bstep (se 2 (by rfl) ⟨572001, by rfl⟩ : syracuseStep 1525337 = 1144003) B1144003
theorem B1525427 : Blo 674311 1525427 := bstep (se 1 (by rfl) ⟨1144070, by rfl⟩ : syracuseStep 1525427 = 2288141) B2288141
theorem B1525463 : Blo 674311 1525463 := bstep (se 1 (by rfl) ⟨1144097, by rfl⟩ : syracuseStep 1525463 = 2288195) B2288195
theorem B1525643 : Blo 674311 1525643 := bstep (se 1 (by rfl) ⟨1144232, by rfl⟩ : syracuseStep 1525643 = 2288465) B2288465
theorem B1525697 : Blo 674311 1525697 := bstep (se 2 (by rfl) ⟨572136, by rfl⟩ : syracuseStep 1525697 = 1144273) B1144273
theorem B2279447 : Blo 674311 2279447 := bstep (se 1 (by rfl) ⟨1709585, by rfl⟩ : syracuseStep 2279447 = 3419171) B3419171
theorem B31311947 : Blo 674311 31311947 := bstep (se 1 (by rfl) ⟨23483960, by rfl⟩ : syracuseStep 31311947 = 46967921) B46967921
theorem B1525913 : Blo 674311 1525913 := bstep (se 2 (by rfl) ⟨572217, by rfl⟩ : syracuseStep 1525913 = 1144435) B1144435
theorem B1526003 : Blo 674311 1526003 := bstep (se 1 (by rfl) ⟨1144502, by rfl⟩ : syracuseStep 1526003 = 2289005) B2289005
theorem B1526039 : Blo 674311 1526039 := bstep (se 1 (by rfl) ⟨1144529, by rfl⟩ : syracuseStep 1526039 = 2289059) B2289059
theorem B2574737 : Blo 674311 2574737 := bstep (se 2 (by rfl) ⟨965526, by rfl⟩ : syracuseStep 2574737 = 1931053) B1931053
theorem B5130701 : Blo 674311 5130701 := bstep (se 3 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 5130701 = 1924013) B1924013
theorem B674315 : Blo 674311 674315 := bstep (se 1 (by rfl) ⟨505736, by rfl⟩ : syracuseStep 674315 = 1011473) B1011473
theorem B674327 : Blo 674311 674327 := bstep (se 1 (by rfl) ⟨505745, by rfl⟩ : syracuseStep 674327 = 1011491) B1011491
theorem B674347 : Blo 674311 674347 := bstep (se 1 (by rfl) ⟨505760, by rfl⟩ : syracuseStep 674347 = 1011521) B1011521
theorem B2279987 : Blo 674311 2279987 := bstep (se 1 (by rfl) ⟨1709990, by rfl⟩ : syracuseStep 2279987 = 3419981) B3419981
theorem B674359 : Blo 674311 674359 := bstep (se 1 (by rfl) ⟨505769, by rfl⟩ : syracuseStep 674359 = 1011539) B1011539
theorem B674379 : Blo 674311 674379 := bstep (se 1 (by rfl) ⟨505784, by rfl⟩ : syracuseStep 674379 = 1011569) B1011569
theorem B674391 : Blo 674311 674391 := bstep (se 1 (by rfl) ⟨505793, by rfl⟩ : syracuseStep 674391 = 1011587) B1011587
theorem B674411 : Blo 674311 674411 := bstep (se 1 (by rfl) ⟨505808, by rfl⟩ : syracuseStep 674411 = 1011617) B1011617
theorem B674423 : Blo 674311 674423 := bstep (se 1 (by rfl) ⟨505817, by rfl⟩ : syracuseStep 674423 = 1011635) B1011635
theorem B3426947 : Blo 674311 3426947 := bstep (se 1 (by rfl) ⟨2570210, by rfl⟩ : syracuseStep 3426947 = 5140421) B5140421
theorem B674443 : Blo 674311 674443 := bstep (se 1 (by rfl) ⟨505832, by rfl⟩ : syracuseStep 674443 = 1011665) B1011665
theorem B674455 : Blo 674311 674455 := bstep (se 1 (by rfl) ⟨505841, by rfl⟩ : syracuseStep 674455 = 1011683) B1011683
theorem B674475 : Blo 674311 674475 := bstep (se 1 (by rfl) ⟨505856, by rfl⟩ : syracuseStep 674475 = 1011713) B1011713
theorem B674487 : Blo 674311 674487 := bstep (se 1 (by rfl) ⟨505865, by rfl⟩ : syracuseStep 674487 = 1011731) B1011731
theorem B674507 : Blo 674311 674507 := bstep (se 1 (by rfl) ⟨505880, by rfl⟩ : syracuseStep 674507 = 1011761) B1011761
theorem B674519 : Blo 674311 674519 := bstep (se 1 (by rfl) ⟨505889, by rfl⟩ : syracuseStep 674519 = 1011779) B1011779
theorem B674539 : Blo 674311 674539 := bstep (se 1 (by rfl) ⟨505904, by rfl⟩ : syracuseStep 674539 = 1011809) B1011809
theorem B674551 : Blo 674311 674551 := bstep (se 1 (by rfl) ⟨505913, by rfl⟩ : syracuseStep 674551 = 1011827) B1011827
theorem B2738947 : Blo 674311 2738947 := bstep (se 1 (by rfl) ⟨2054210, by rfl⟩ : syracuseStep 2738947 = 4108421) B4108421
theorem B674571 : Blo 674311 674571 := bstep (se 1 (by rfl) ⟨505928, by rfl⟩ : syracuseStep 674571 = 1011857) B1011857
theorem B674583 : Blo 674311 674583 := bstep (se 1 (by rfl) ⟨505937, by rfl⟩ : syracuseStep 674583 = 1011875) B1011875
theorem B674603 : Blo 674311 674603 := bstep (se 1 (by rfl) ⟨505952, by rfl⟩ : syracuseStep 674603 = 1011905) B1011905
theorem B674615 : Blo 674311 674615 := bstep (se 1 (by rfl) ⟨505961, by rfl⟩ : syracuseStep 674615 = 1011923) B1011923
theorem B2280257 : Blo 674311 2280257 := bstep (se 2 (by rfl) ⟨855096, by rfl⟩ : syracuseStep 2280257 = 1710193) B1710193
theorem B674635 : Blo 674311 674635 := bstep (se 1 (by rfl) ⟨505976, by rfl⟩ : syracuseStep 674635 = 1011953) B1011953
theorem B674647 : Blo 674311 674647 := bstep (se 1 (by rfl) ⟨505985, by rfl⟩ : syracuseStep 674647 = 1011971) B1011971
theorem B674667 : Blo 674311 674667 := bstep (se 1 (by rfl) ⟨506000, by rfl⟩ : syracuseStep 674667 = 1012001) B1012001
theorem B674679 : Blo 674311 674679 := bstep (se 1 (by rfl) ⟨506009, by rfl⟩ : syracuseStep 674679 = 1012019) B1012019
theorem B674699 : Blo 674311 674699 := bstep (se 1 (by rfl) ⟨506024, by rfl⟩ : syracuseStep 674699 = 1012049) B1012049
theorem B674711 : Blo 674311 674711 := bstep (se 1 (by rfl) ⟨506033, by rfl⟩ : syracuseStep 674711 = 1012067) B1012067
theorem B674731 : Blo 674311 674731 := bstep (se 1 (by rfl) ⟨506048, by rfl⟩ : syracuseStep 674731 = 1012097) B1012097
theorem B5131187 : Blo 674311 5131187 := bstep (se 1 (by rfl) ⟨3848390, by rfl⟩ : syracuseStep 5131187 = 7696781) B7696781
theorem B674743 : Blo 674311 674743 := bstep (se 1 (by rfl) ⟨506057, by rfl⟩ : syracuseStep 674743 = 1012115) B1012115
theorem B674763 : Blo 674311 674763 := bstep (se 1 (by rfl) ⟨506072, by rfl⟩ : syracuseStep 674763 = 1012145) B1012145
theorem B674775 : Blo 674311 674775 := bstep (se 1 (by rfl) ⟨506081, by rfl⟩ : syracuseStep 674775 = 1012163) B1012163
theorem B674795 : Blo 674311 674795 := bstep (se 1 (by rfl) ⟨506096, by rfl⟩ : syracuseStep 674795 = 1012193) B1012193
theorem B674807 : Blo 674311 674807 := bstep (se 1 (by rfl) ⟨506105, by rfl⟩ : syracuseStep 674807 = 1012211) B1012211
theorem B674827 : Blo 674311 674827 := bstep (se 1 (by rfl) ⟨506120, by rfl⟩ : syracuseStep 674827 = 1012241) B1012241
theorem B674839 : Blo 674311 674839 := bstep (se 1 (by rfl) ⟨506129, by rfl⟩ : syracuseStep 674839 = 1012259) B1012259
theorem B674859 : Blo 674311 674859 := bstep (se 1 (by rfl) ⟨506144, by rfl⟩ : syracuseStep 674859 = 1012289) B1012289
theorem B674871 : Blo 674311 674871 := bstep (se 1 (by rfl) ⟨506153, by rfl⟩ : syracuseStep 674871 = 1012307) B1012307
theorem B674891 : Blo 674311 674891 := bstep (se 1 (by rfl) ⟨506168, by rfl⟩ : syracuseStep 674891 = 1012337) B1012337
theorem B2575435 : Blo 674311 2575435 := bstep (se 1 (by rfl) ⟨1931576, by rfl⟩ : syracuseStep 2575435 = 3863153) B3863153
theorem B674903 : Blo 674311 674903 := bstep (se 1 (by rfl) ⟨506177, by rfl⟩ : syracuseStep 674903 = 1012355) B1012355
theorem B674923 : Blo 674311 674923 := bstep (se 1 (by rfl) ⟨506192, by rfl⟩ : syracuseStep 674923 = 1012385) B1012385
theorem B674935 : Blo 674311 674935 := bstep (se 1 (by rfl) ⟨506201, by rfl⟩ : syracuseStep 674935 = 1012403) B1012403
theorem B674955 : Blo 674311 674955 := bstep (se 1 (by rfl) ⟨506216, by rfl⟩ : syracuseStep 674955 = 1012433) B1012433
theorem B674967 : Blo 674311 674967 := bstep (se 1 (by rfl) ⟨506225, by rfl⟩ : syracuseStep 674967 = 1012451) B1012451
theorem B674987 : Blo 674311 674987 := bstep (se 1 (by rfl) ⟨506240, by rfl⟩ : syracuseStep 674987 = 1012481) B1012481
theorem B674999 : Blo 674311 674999 := bstep (se 1 (by rfl) ⟨506249, by rfl⟩ : syracuseStep 674999 = 1012499) B1012499
theorem B675019 : Blo 674311 675019 := bstep (se 1 (by rfl) ⟨506264, by rfl⟩ : syracuseStep 675019 = 1012529) B1012529
theorem B675031 : Blo 674311 675031 := bstep (se 1 (by rfl) ⟨506273, by rfl⟩ : syracuseStep 675031 = 1012547) B1012547
theorem B675051 : Blo 674311 675051 := bstep (se 1 (by rfl) ⟨506288, by rfl⟩ : syracuseStep 675051 = 1012577) B1012577
theorem B675063 : Blo 674311 675063 := bstep (se 1 (by rfl) ⟨506297, by rfl⟩ : syracuseStep 675063 = 1012595) B1012595
theorem B675083 : Blo 674311 675083 := bstep (se 1 (by rfl) ⟨506312, by rfl⟩ : syracuseStep 675083 = 1012625) B1012625
theorem B675095 : Blo 674311 675095 := bstep (se 1 (by rfl) ⟨506321, by rfl⟩ : syracuseStep 675095 = 1012643) B1012643
theorem B675115 : Blo 674311 675115 := bstep (se 1 (by rfl) ⟨506336, by rfl⟩ : syracuseStep 675115 = 1012673) B1012673
theorem B675127 : Blo 674311 675127 := bstep (se 1 (by rfl) ⟨506345, by rfl⟩ : syracuseStep 675127 = 1012691) B1012691
theorem B675147 : Blo 674311 675147 := bstep (se 1 (by rfl) ⟨506360, by rfl⟩ : syracuseStep 675147 = 1012721) B1012721
theorem B675159 : Blo 674311 675159 := bstep (se 1 (by rfl) ⟨506369, by rfl⟩ : syracuseStep 675159 = 1012739) B1012739
theorem B2280797 : Blo 674311 2280797 := bstep (se 3 (by rfl) ⟨427649, by rfl⟩ : syracuseStep 2280797 = 855299) B855299
theorem B675179 : Blo 674311 675179 := bstep (se 1 (by rfl) ⟨506384, by rfl⟩ : syracuseStep 675179 = 1012769) B1012769
theorem B675191 : Blo 674311 675191 := bstep (se 1 (by rfl) ⟨506393, by rfl⟩ : syracuseStep 675191 = 1012787) B1012787
theorem B675211 : Blo 674311 675211 := bstep (se 1 (by rfl) ⟨506408, by rfl⟩ : syracuseStep 675211 = 1012817) B1012817
theorem B675223 : Blo 674311 675223 := bstep (se 1 (by rfl) ⟨506417, by rfl⟩ : syracuseStep 675223 = 1012835) B1012835
theorem B675243 : Blo 674311 675243 := bstep (se 1 (by rfl) ⟨506432, by rfl⟩ : syracuseStep 675243 = 1012865) B1012865
theorem B675255 : Blo 674311 675255 := bstep (se 1 (by rfl) ⟨506441, by rfl⟩ : syracuseStep 675255 = 1012883) B1012883
theorem B1920449 : Blo 674311 1920449 := bstep (se 2 (by rfl) ⟨720168, by rfl⟩ : syracuseStep 1920449 = 1440337) B1440337
theorem B675275 : Blo 674311 675275 := bstep (se 1 (by rfl) ⟨506456, by rfl⟩ : syracuseStep 675275 = 1012913) B1012913
theorem B675287 : Blo 674311 675287 := bstep (se 1 (by rfl) ⟨506465, by rfl⟩ : syracuseStep 675287 = 1012931) B1012931
theorem B675307 : Blo 674311 675307 := bstep (se 1 (by rfl) ⟨506480, by rfl⟩ : syracuseStep 675307 = 1012961) B1012961
theorem B675319 : Blo 674311 675319 := bstep (se 1 (by rfl) ⟨506489, by rfl⟩ : syracuseStep 675319 = 1012979) B1012979
theorem B675339 : Blo 674311 675339 := bstep (se 1 (by rfl) ⟨506504, by rfl⟩ : syracuseStep 675339 = 1013009) B1013009
theorem B675351 : Blo 674311 675351 := bstep (se 1 (by rfl) ⟨506513, by rfl⟩ : syracuseStep 675351 = 1013027) B1013027
theorem B675371 : Blo 674311 675371 := bstep (se 1 (by rfl) ⟨506528, by rfl⟩ : syracuseStep 675371 = 1013057) B1013057
theorem B675383 : Blo 674311 675383 := bstep (se 1 (by rfl) ⟨506537, by rfl⟩ : syracuseStep 675383 = 1013075) B1013075
theorem B675403 : Blo 674311 675403 := bstep (se 1 (by rfl) ⟨506552, by rfl⟩ : syracuseStep 675403 = 1013105) B1013105
theorem B675415 : Blo 674311 675415 := bstep (se 1 (by rfl) ⟨506561, by rfl⟩ : syracuseStep 675415 = 1013123) B1013123
theorem B675435 : Blo 674311 675435 := bstep (se 1 (by rfl) ⟨506576, by rfl⟩ : syracuseStep 675435 = 1013153) B1013153
theorem B675447 : Blo 674311 675447 := bstep (se 1 (by rfl) ⟨506585, by rfl⟩ : syracuseStep 675447 = 1013171) B1013171
theorem B675467 : Blo 674311 675467 := bstep (se 1 (by rfl) ⟨506600, by rfl⟩ : syracuseStep 675467 = 1013201) B1013201
theorem B675479 : Blo 674311 675479 := bstep (se 1 (by rfl) ⟨506609, by rfl⟩ : syracuseStep 675479 = 1013219) B1013219
theorem B675499 : Blo 674311 675499 := bstep (se 1 (by rfl) ⟨506624, by rfl⟩ : syracuseStep 675499 = 1013249) B1013249
theorem B675511 : Blo 674311 675511 := bstep (se 1 (by rfl) ⟨506633, by rfl⟩ : syracuseStep 675511 = 1013267) B1013267
theorem B675531 : Blo 674311 675531 := bstep (se 1 (by rfl) ⟨506648, by rfl⟩ : syracuseStep 675531 = 1013297) B1013297
theorem B675543 : Blo 674311 675543 := bstep (se 1 (by rfl) ⟨506657, by rfl⟩ : syracuseStep 675543 = 1013315) B1013315
theorem B675563 : Blo 674311 675563 := bstep (se 1 (by rfl) ⟨506672, by rfl⟩ : syracuseStep 675563 = 1013345) B1013345
theorem B675575 : Blo 674311 675575 := bstep (se 1 (by rfl) ⟨506681, by rfl⟩ : syracuseStep 675575 = 1013363) B1013363
theorem B675595 : Blo 674311 675595 := bstep (se 1 (by rfl) ⟨506696, by rfl⟩ : syracuseStep 675595 = 1013393) B1013393
theorem B675607 : Blo 674311 675607 := bstep (se 1 (by rfl) ⟨506705, by rfl⟩ : syracuseStep 675607 = 1013411) B1013411
theorem B675627 : Blo 674311 675627 := bstep (se 1 (by rfl) ⟨506720, by rfl⟩ : syracuseStep 675627 = 1013441) B1013441
theorem B5623597 : Blo 674311 5623597 := bstep (se 3 (by rfl) ⟨1054424, by rfl⟩ : syracuseStep 5623597 = 2108849) B2108849
theorem B675639 : Blo 674311 675639 := bstep (se 1 (by rfl) ⟨506729, by rfl⟩ : syracuseStep 675639 = 1013459) B1013459
theorem B675659 : Blo 674311 675659 := bstep (se 1 (by rfl) ⟨506744, by rfl⟩ : syracuseStep 675659 = 1013489) B1013489
theorem B675671 : Blo 674311 675671 := bstep (se 1 (by rfl) ⟨506753, by rfl⟩ : syracuseStep 675671 = 1013507) B1013507
theorem B675691 : Blo 674311 675691 := bstep (se 1 (by rfl) ⟨506768, by rfl⟩ : syracuseStep 675691 = 1013537) B1013537
theorem B675703 : Blo 674311 675703 := bstep (se 1 (by rfl) ⟨506777, by rfl⟩ : syracuseStep 675703 = 1013555) B1013555
theorem B675723 : Blo 674311 675723 := bstep (se 1 (by rfl) ⟨506792, by rfl⟩ : syracuseStep 675723 = 1013585) B1013585
theorem B675735 : Blo 674311 675735 := bstep (se 1 (by rfl) ⟨506801, by rfl⟩ : syracuseStep 675735 = 1013603) B1013603
theorem B675755 : Blo 674311 675755 := bstep (se 1 (by rfl) ⟨506816, by rfl⟩ : syracuseStep 675755 = 1013633) B1013633
theorem B675767 : Blo 674311 675767 := bstep (se 1 (by rfl) ⟨506825, by rfl⟩ : syracuseStep 675767 = 1013651) B1013651
theorem B675787 : Blo 674311 675787 := bstep (se 1 (by rfl) ⟨506840, by rfl⟩ : syracuseStep 675787 = 1013681) B1013681
theorem B675799 : Blo 674311 675799 := bstep (se 1 (by rfl) ⟨506849, by rfl⟩ : syracuseStep 675799 = 1013699) B1013699
theorem B675819 : Blo 674311 675819 := bstep (se 1 (by rfl) ⟨506864, by rfl⟩ : syracuseStep 675819 = 1013729) B1013729
theorem B675831 : Blo 674311 675831 := bstep (se 1 (by rfl) ⟨506873, by rfl⟩ : syracuseStep 675831 = 1013747) B1013747
theorem B675851 : Blo 674311 675851 := bstep (se 1 (by rfl) ⟨506888, by rfl⟩ : syracuseStep 675851 = 1013777) B1013777
theorem B675863 : Blo 674311 675863 := bstep (se 1 (by rfl) ⟨506897, by rfl⟩ : syracuseStep 675863 = 1013795) B1013795
theorem B675883 : Blo 674311 675883 := bstep (se 1 (by rfl) ⟨506912, by rfl⟩ : syracuseStep 675883 = 1013825) B1013825
theorem B675895 : Blo 674311 675895 := bstep (se 1 (by rfl) ⟨506921, by rfl⟩ : syracuseStep 675895 = 1013843) B1013843
theorem B1953857 : Blo 674311 1953857 := bstep (se 2 (by rfl) ⟨732696, by rfl⟩ : syracuseStep 1953857 = 1465393) B1465393
theorem B675915 : Blo 674311 675915 := bstep (se 1 (by rfl) ⟨506936, by rfl⟩ : syracuseStep 675915 = 1013873) B1013873
theorem B675927 : Blo 674311 675927 := bstep (se 1 (by rfl) ⟨506945, by rfl⟩ : syracuseStep 675927 = 1013891) B1013891
theorem B675947 : Blo 674311 675947 := bstep (se 1 (by rfl) ⟨506960, by rfl⟩ : syracuseStep 675947 = 1013921) B1013921
theorem B675959 : Blo 674311 675959 := bstep (se 1 (by rfl) ⟨506969, by rfl⟩ : syracuseStep 675959 = 1013939) B1013939
theorem B675979 : Blo 674311 675979 := bstep (se 1 (by rfl) ⟨506984, by rfl⟩ : syracuseStep 675979 = 1013969) B1013969
theorem B675991 : Blo 674311 675991 := bstep (se 1 (by rfl) ⟨506993, by rfl⟩ : syracuseStep 675991 = 1013987) B1013987
theorem B676011 : Blo 674311 676011 := bstep (se 1 (by rfl) ⟨507008, by rfl⟩ : syracuseStep 676011 = 1014017) B1014017
theorem B676023 : Blo 674311 676023 := bstep (se 1 (by rfl) ⟨507017, by rfl⟩ : syracuseStep 676023 = 1014035) B1014035
theorem B676043 : Blo 674311 676043 := bstep (se 1 (by rfl) ⟨507032, by rfl⟩ : syracuseStep 676043 = 1014065) B1014065
theorem B676055 : Blo 674311 676055 := bstep (se 1 (by rfl) ⟨507041, by rfl⟩ : syracuseStep 676055 = 1014083) B1014083
theorem B676075 : Blo 674311 676075 := bstep (se 1 (by rfl) ⟨507056, by rfl⟩ : syracuseStep 676075 = 1014113) B1014113
theorem B676087 : Blo 674311 676087 := bstep (se 1 (by rfl) ⟨507065, by rfl⟩ : syracuseStep 676087 = 1014131) B1014131
theorem B676107 : Blo 674311 676107 := bstep (se 1 (by rfl) ⟨507080, by rfl⟩ : syracuseStep 676107 = 1014161) B1014161
theorem B676119 : Blo 674311 676119 := bstep (se 1 (by rfl) ⟨507089, by rfl⟩ : syracuseStep 676119 = 1014179) B1014179
theorem B676139 : Blo 674311 676139 := bstep (se 1 (by rfl) ⟨507104, by rfl⟩ : syracuseStep 676139 = 1014209) B1014209
theorem B676151 : Blo 674311 676151 := bstep (se 1 (by rfl) ⟨507113, by rfl⟩ : syracuseStep 676151 = 1014227) B1014227
theorem B6607169 : Blo 674311 6607169 := bstep (se 2 (by rfl) ⟨2477688, by rfl⟩ : syracuseStep 6607169 = 4955377) B4955377
theorem B676171 : Blo 674311 676171 := bstep (se 1 (by rfl) ⟨507128, by rfl⟩ : syracuseStep 676171 = 1014257) B1014257
theorem B676183 : Blo 674311 676183 := bstep (se 1 (by rfl) ⟨507137, by rfl⟩ : syracuseStep 676183 = 1014275) B1014275
theorem B5132645 : Blo 674311 5132645 := bstep (se 4 (by rfl) ⟨481185, by rfl⟩ : syracuseStep 5132645 = 962371) B962371
theorem B676203 : Blo 674311 676203 := bstep (se 1 (by rfl) ⟨507152, by rfl⟩ : syracuseStep 676203 = 1014305) B1014305
theorem B676215 : Blo 674311 676215 := bstep (se 1 (by rfl) ⟨507161, by rfl⟩ : syracuseStep 676215 = 1014323) B1014323
theorem B676235 : Blo 674311 676235 := bstep (se 1 (by rfl) ⟨507176, by rfl⟩ : syracuseStep 676235 = 1014353) B1014353
theorem B676247 : Blo 674311 676247 := bstep (se 1 (by rfl) ⟨507185, by rfl⟩ : syracuseStep 676247 = 1014371) B1014371
theorem B676267 : Blo 674311 676267 := bstep (se 1 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 676267 = 1014401) B1014401
theorem B676279 : Blo 674311 676279 := bstep (se 1 (by rfl) ⟨507209, by rfl⟩ : syracuseStep 676279 = 1014419) B1014419
theorem B2052545 : Blo 674311 2052545 := bstep (se 2 (by rfl) ⟨769704, by rfl⟩ : syracuseStep 2052545 = 1539409) B1539409
theorem B2281931 : Blo 674311 2281931 := bstep (se 1 (by rfl) ⟨1711448, by rfl⟩ : syracuseStep 2281931 = 3422897) B3422897
theorem B676299 : Blo 674311 676299 := bstep (se 1 (by rfl) ⟨507224, by rfl⟩ : syracuseStep 676299 = 1014449) B1014449
theorem B676311 : Blo 674311 676311 := bstep (se 1 (by rfl) ⟨507233, by rfl⟩ : syracuseStep 676311 = 1014467) B1014467
theorem B676331 : Blo 674311 676331 := bstep (se 1 (by rfl) ⟨507248, by rfl⟩ : syracuseStep 676331 = 1014497) B1014497
theorem B676343 : Blo 674311 676343 := bstep (se 1 (by rfl) ⟨507257, by rfl⟩ : syracuseStep 676343 = 1014515) B1014515
theorem B676363 : Blo 674311 676363 := bstep (se 1 (by rfl) ⟨507272, by rfl⟩ : syracuseStep 676363 = 1014545) B1014545
theorem B676375 : Blo 674311 676375 := bstep (se 1 (by rfl) ⟨507281, by rfl⟩ : syracuseStep 676375 = 1014563) B1014563
theorem B676395 : Blo 674311 676395 := bstep (se 1 (by rfl) ⟨507296, by rfl⟩ : syracuseStep 676395 = 1014593) B1014593
theorem B676407 : Blo 674311 676407 := bstep (se 1 (by rfl) ⟨507305, by rfl⟩ : syracuseStep 676407 = 1014611) B1014611
theorem B10998341 : Blo 674311 10998341 := bstep (se 4 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 10998341 = 2062189) B2062189
theorem B676427 : Blo 674311 676427 := bstep (se 1 (by rfl) ⟨507320, by rfl⟩ : syracuseStep 676427 = 1014641) B1014641
theorem B676439 : Blo 674311 676439 := bstep (se 1 (by rfl) ⟨507329, by rfl⟩ : syracuseStep 676439 = 1014659) B1014659
theorem B1626713 : Blo 674311 1626713 := bstep (se 2 (by rfl) ⟨610017, by rfl⟩ : syracuseStep 1626713 = 1220035) B1220035
theorem B676459 : Blo 674311 676459 := bstep (se 1 (by rfl) ⟨507344, by rfl⟩ : syracuseStep 676459 = 1014689) B1014689
theorem B676471 : Blo 674311 676471 := bstep (se 1 (by rfl) ⟨507353, by rfl⟩ : syracuseStep 676471 = 1014707) B1014707
theorem B676491 : Blo 674311 676491 := bstep (se 1 (by rfl) ⟨507368, by rfl⟩ : syracuseStep 676491 = 1014737) B1014737
theorem B676503 : Blo 674311 676503 := bstep (se 1 (by rfl) ⟨507377, by rfl⟩ : syracuseStep 676503 = 1014755) B1014755
theorem B676523 : Blo 674311 676523 := bstep (se 1 (by rfl) ⟨507392, by rfl⟩ : syracuseStep 676523 = 1014785) B1014785
theorem B676535 : Blo 674311 676535 := bstep (se 1 (by rfl) ⟨507401, by rfl⟩ : syracuseStep 676535 = 1014803) B1014803
theorem B676555 : Blo 674311 676555 := bstep (se 1 (by rfl) ⟨507416, by rfl⟩ : syracuseStep 676555 = 1014833) B1014833
theorem B1233623 : Blo 674311 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B676567 : Blo 674311 676567 := bstep (se 1 (by rfl) ⟨507425, by rfl⟩ : syracuseStep 676567 = 1014851) B1014851
theorem B2282201 : Blo 674311 2282201 := bstep (se 2 (by rfl) ⟨855825, by rfl⟩ : syracuseStep 2282201 = 1711651) B1711651
theorem B676587 : Blo 674311 676587 := bstep (se 1 (by rfl) ⟨507440, by rfl⟩ : syracuseStep 676587 = 1014881) B1014881
theorem B676599 : Blo 674311 676599 := bstep (se 1 (by rfl) ⟨507449, by rfl⟩ : syracuseStep 676599 = 1014899) B1014899
theorem B676619 : Blo 674311 676619 := bstep (se 1 (by rfl) ⟨507464, by rfl⟩ : syracuseStep 676619 = 1014929) B1014929
theorem B676631 : Blo 674311 676631 := bstep (se 1 (by rfl) ⟨507473, by rfl⟩ : syracuseStep 676631 = 1014947) B1014947
theorem B676651 : Blo 674311 676651 := bstep (se 1 (by rfl) ⟨507488, by rfl⟩ : syracuseStep 676651 = 1014977) B1014977
theorem B676663 : Blo 674311 676663 := bstep (se 1 (by rfl) ⟨507497, by rfl⟩ : syracuseStep 676663 = 1014995) B1014995
theorem B5133131 : Blo 674311 5133131 := bstep (se 1 (by rfl) ⟨3849848, by rfl⟩ : syracuseStep 5133131 = 7699697) B7699697
theorem B676683 : Blo 674311 676683 := bstep (se 1 (by rfl) ⟨507512, by rfl⟩ : syracuseStep 676683 = 1015025) B1015025
theorem B676695 : Blo 674311 676695 := bstep (se 1 (by rfl) ⟨507521, by rfl⟩ : syracuseStep 676695 = 1015043) B1015043
theorem B676715 : Blo 674311 676715 := bstep (se 1 (by rfl) ⟨507536, by rfl⟩ : syracuseStep 676715 = 1015073) B1015073
theorem B676727 : Blo 674311 676727 := bstep (se 1 (by rfl) ⟨507545, by rfl⟩ : syracuseStep 676727 = 1015091) B1015091
theorem B676747 : Blo 674311 676747 := bstep (se 1 (by rfl) ⟨507560, by rfl⟩ : syracuseStep 676747 = 1015121) B1015121
theorem B676759 : Blo 674311 676759 := bstep (se 1 (by rfl) ⟨507569, by rfl⟩ : syracuseStep 676759 = 1015139) B1015139
theorem B676779 : Blo 674311 676779 := bstep (se 1 (by rfl) ⟨507584, by rfl⟩ : syracuseStep 676779 = 1015169) B1015169
theorem B2053043 : Blo 674311 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B676791 : Blo 674311 676791 := bstep (se 1 (by rfl) ⟨507593, by rfl⟩ : syracuseStep 676791 = 1015187) B1015187
theorem B676811 : Blo 674311 676811 := bstep (se 1 (by rfl) ⟨507608, by rfl⟩ : syracuseStep 676811 = 1015217) B1015217
theorem B676823 : Blo 674311 676823 := bstep (se 1 (by rfl) ⟨507617, by rfl⟩ : syracuseStep 676823 = 1015235) B1015235
theorem B676843 : Blo 674311 676843 := bstep (se 1 (by rfl) ⟨507632, by rfl⟩ : syracuseStep 676843 = 1015265) B1015265
theorem B676855 : Blo 674311 676855 := bstep (se 1 (by rfl) ⟨507641, by rfl⟩ : syracuseStep 676855 = 1015283) B1015283
theorem B676875 : Blo 674311 676875 := bstep (se 1 (by rfl) ⟨507656, by rfl⟩ : syracuseStep 676875 = 1015313) B1015313
theorem B676887 : Blo 674311 676887 := bstep (se 1 (by rfl) ⟨507665, by rfl⟩ : syracuseStep 676887 = 1015331) B1015331
theorem B676907 : Blo 674311 676907 := bstep (se 1 (by rfl) ⟨507680, by rfl⟩ : syracuseStep 676907 = 1015361) B1015361
theorem B676919 : Blo 674311 676919 := bstep (se 1 (by rfl) ⟨507689, by rfl⟩ : syracuseStep 676919 = 1015379) B1015379
theorem B2774081 : Blo 674311 2774081 := bstep (se 2 (by rfl) ⟨1040280, by rfl⟩ : syracuseStep 2774081 = 2080561) B2080561
theorem B1922123 : Blo 674311 1922123 := bstep (se 1 (by rfl) ⟨1441592, by rfl⟩ : syracuseStep 1922123 = 2883185) B2883185
theorem B676939 : Blo 674311 676939 := bstep (se 1 (by rfl) ⟨507704, by rfl⟩ : syracuseStep 676939 = 1015409) B1015409
theorem B676951 : Blo 674311 676951 := bstep (se 1 (by rfl) ⟨507713, by rfl⟩ : syracuseStep 676951 = 1015427) B1015427
theorem B676971 : Blo 674311 676971 := bstep (se 1 (by rfl) ⟨507728, by rfl⟩ : syracuseStep 676971 = 1015457) B1015457
theorem B676983 : Blo 674311 676983 := bstep (se 1 (by rfl) ⟨507737, by rfl⟩ : syracuseStep 676983 = 1015475) B1015475
theorem B677003 : Blo 674311 677003 := bstep (se 1 (by rfl) ⟨507752, by rfl⟩ : syracuseStep 677003 = 1015505) B1015505
theorem B677015 : Blo 674311 677015 := bstep (se 1 (by rfl) ⟨507761, by rfl⟩ : syracuseStep 677015 = 1015523) B1015523
theorem B677035 : Blo 674311 677035 := bstep (se 1 (by rfl) ⟨507776, by rfl⟩ : syracuseStep 677035 = 1015553) B1015553
theorem B677047 : Blo 674311 677047 := bstep (se 1 (by rfl) ⟨507785, by rfl⟩ : syracuseStep 677047 = 1015571) B1015571
theorem B677067 : Blo 674311 677067 := bstep (se 1 (by rfl) ⟨507800, by rfl⟩ : syracuseStep 677067 = 1015601) B1015601
theorem B677079 : Blo 674311 677079 := bstep (se 1 (by rfl) ⟨507809, by rfl⟩ : syracuseStep 677079 = 1015619) B1015619
theorem B677099 : Blo 674311 677099 := bstep (se 1 (by rfl) ⟨507824, by rfl⟩ : syracuseStep 677099 = 1015649) B1015649
theorem B677111 : Blo 674311 677111 := bstep (se 1 (by rfl) ⟨507833, by rfl⟩ : syracuseStep 677111 = 1015667) B1015667
theorem B677131 : Blo 674311 677131 := bstep (se 1 (by rfl) ⟨507848, by rfl⟩ : syracuseStep 677131 = 1015697) B1015697
theorem B677143 : Blo 674311 677143 := bstep (se 1 (by rfl) ⟨507857, by rfl⟩ : syracuseStep 677143 = 1015715) B1015715
theorem B677163 : Blo 674311 677163 := bstep (se 1 (by rfl) ⟨507872, by rfl⟩ : syracuseStep 677163 = 1015745) B1015745
theorem B677175 : Blo 674311 677175 := bstep (se 1 (by rfl) ⟨507881, by rfl⟩ : syracuseStep 677175 = 1015763) B1015763
theorem B677195 : Blo 674311 677195 := bstep (se 1 (by rfl) ⟨507896, by rfl⟩ : syracuseStep 677195 = 1015793) B1015793
theorem B677207 : Blo 674311 677207 := bstep (se 1 (by rfl) ⟨507905, by rfl⟩ : syracuseStep 677207 = 1015811) B1015811
theorem B677227 : Blo 674311 677227 := bstep (se 1 (by rfl) ⟨507920, by rfl⟩ : syracuseStep 677227 = 1015841) B1015841
theorem B677239 : Blo 674311 677239 := bstep (se 1 (by rfl) ⟨507929, by rfl⟩ : syracuseStep 677239 = 1015859) B1015859
theorem B677259 : Blo 674311 677259 := bstep (se 1 (by rfl) ⟨507944, by rfl⟩ : syracuseStep 677259 = 1015889) B1015889
theorem B2282903 : Blo 674311 2282903 := bstep (se 1 (by rfl) ⟨1712177, by rfl⟩ : syracuseStep 2282903 = 3424355) B3424355
theorem B677271 : Blo 674311 677271 := bstep (se 1 (by rfl) ⟨507953, by rfl⟩ : syracuseStep 677271 = 1015907) B1015907
theorem B677291 : Blo 674311 677291 := bstep (se 1 (by rfl) ⟨507968, by rfl⟩ : syracuseStep 677291 = 1015937) B1015937
theorem B5854643 : Blo 674311 5854643 := bstep (se 1 (by rfl) ⟨4390982, by rfl⟩ : syracuseStep 5854643 = 8781965) B8781965
theorem B677303 : Blo 674311 677303 := bstep (se 1 (by rfl) ⟨507977, by rfl⟩ : syracuseStep 677303 = 1015955) B1015955
theorem B677323 : Blo 674311 677323 := bstep (se 1 (by rfl) ⟨507992, by rfl⟩ : syracuseStep 677323 = 1015985) B1015985
theorem B677335 : Blo 674311 677335 := bstep (se 1 (by rfl) ⟨508001, by rfl⟩ : syracuseStep 677335 = 1016003) B1016003
theorem B677355 : Blo 674311 677355 := bstep (se 1 (by rfl) ⟨508016, by rfl⟩ : syracuseStep 677355 = 1016033) B1016033
theorem B677367 : Blo 674311 677367 := bstep (se 1 (by rfl) ⟨508025, by rfl⟩ : syracuseStep 677367 = 1016051) B1016051
theorem B677387 : Blo 674311 677387 := bstep (se 1 (by rfl) ⟨508040, by rfl⟩ : syracuseStep 677387 = 1016081) B1016081
theorem B677399 : Blo 674311 677399 := bstep (se 1 (by rfl) ⟨508049, by rfl⟩ : syracuseStep 677399 = 1016099) B1016099
theorem B677419 : Blo 674311 677419 := bstep (se 1 (by rfl) ⟨508064, by rfl⟩ : syracuseStep 677419 = 1016129) B1016129
theorem B677431 : Blo 674311 677431 := bstep (se 1 (by rfl) ⟨508073, by rfl⟩ : syracuseStep 677431 = 1016147) B1016147
theorem B1955393 : Blo 674311 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B677451 : Blo 674311 677451 := bstep (se 1 (by rfl) ⟨508088, by rfl⟩ : syracuseStep 677451 = 1016177) B1016177
theorem B677463 : Blo 674311 677463 := bstep (se 1 (by rfl) ⟨508097, by rfl⟩ : syracuseStep 677463 = 1016195) B1016195
theorem B677483 : Blo 674311 677483 := bstep (se 1 (by rfl) ⟨508112, by rfl⟩ : syracuseStep 677483 = 1016225) B1016225
theorem B677495 : Blo 674311 677495 := bstep (se 1 (by rfl) ⟨508121, by rfl⟩ : syracuseStep 677495 = 1016243) B1016243
theorem B677515 : Blo 674311 677515 := bstep (se 1 (by rfl) ⟨508136, by rfl⟩ : syracuseStep 677515 = 1016273) B1016273
theorem B677527 : Blo 674311 677527 := bstep (se 1 (by rfl) ⟨508145, by rfl⟩ : syracuseStep 677527 = 1016291) B1016291
theorem B677547 : Blo 674311 677547 := bstep (se 1 (by rfl) ⟨508160, by rfl⟩ : syracuseStep 677547 = 1016321) B1016321
theorem B677559 : Blo 674311 677559 := bstep (se 1 (by rfl) ⟨508169, by rfl⟩ : syracuseStep 677559 = 1016339) B1016339
theorem B677579 : Blo 674311 677579 := bstep (se 1 (by rfl) ⟨508184, by rfl⟩ : syracuseStep 677579 = 1016369) B1016369
theorem B677591 : Blo 674311 677591 := bstep (se 1 (by rfl) ⟨508193, by rfl⟩ : syracuseStep 677591 = 1016387) B1016387
theorem B677611 : Blo 674311 677611 := bstep (se 1 (by rfl) ⟨508208, by rfl⟩ : syracuseStep 677611 = 1016417) B1016417
theorem B677623 : Blo 674311 677623 := bstep (se 1 (by rfl) ⟨508217, by rfl⟩ : syracuseStep 677623 = 1016435) B1016435
theorem B677643 : Blo 674311 677643 := bstep (se 1 (by rfl) ⟨508232, by rfl⟩ : syracuseStep 677643 = 1016465) B1016465
theorem B677655 : Blo 674311 677655 := bstep (se 1 (by rfl) ⟨508241, by rfl⟩ : syracuseStep 677655 = 1016483) B1016483
theorem B677675 : Blo 674311 677675 := bstep (se 1 (by rfl) ⟨508256, by rfl⟩ : syracuseStep 677675 = 1016513) B1016513
theorem B677687 : Blo 674311 677687 := bstep (se 1 (by rfl) ⟨508265, by rfl⟩ : syracuseStep 677687 = 1016531) B1016531
theorem B677707 : Blo 674311 677707 := bstep (se 1 (by rfl) ⟨508280, by rfl⟩ : syracuseStep 677707 = 1016561) B1016561
theorem B677719 : Blo 674311 677719 := bstep (se 1 (by rfl) ⟨508289, by rfl⟩ : syracuseStep 677719 = 1016579) B1016579
theorem B677739 : Blo 674311 677739 := bstep (se 1 (by rfl) ⟨508304, by rfl⟩ : syracuseStep 677739 = 1016609) B1016609
theorem B677751 : Blo 674311 677751 := bstep (se 1 (by rfl) ⟨508313, by rfl⟩ : syracuseStep 677751 = 1016627) B1016627
theorem B677771 : Blo 674311 677771 := bstep (se 1 (by rfl) ⟨508328, by rfl⟩ : syracuseStep 677771 = 1016657) B1016657
theorem B677783 : Blo 674311 677783 := bstep (se 1 (by rfl) ⟨508337, by rfl⟩ : syracuseStep 677783 = 1016675) B1016675
theorem B677803 : Blo 674311 677803 := bstep (se 1 (by rfl) ⟨508352, by rfl⟩ : syracuseStep 677803 = 1016705) B1016705
theorem B2283443 : Blo 674311 2283443 := bstep (se 1 (by rfl) ⟨1712582, by rfl⟩ : syracuseStep 2283443 = 3425165) B3425165
theorem B677815 : Blo 674311 677815 := bstep (se 1 (by rfl) ⟨508361, by rfl⟩ : syracuseStep 677815 = 1016723) B1016723
theorem B677835 : Blo 674311 677835 := bstep (se 1 (by rfl) ⟨508376, by rfl⟩ : syracuseStep 677835 = 1016753) B1016753
theorem B677847 : Blo 674311 677847 := bstep (se 1 (by rfl) ⟨508385, by rfl⟩ : syracuseStep 677847 = 1016771) B1016771
theorem B677867 : Blo 674311 677867 := bstep (se 1 (by rfl) ⟨508400, by rfl⟩ : syracuseStep 677867 = 1016801) B1016801
theorem B677879 : Blo 674311 677879 := bstep (se 1 (by rfl) ⟨508409, by rfl⟩ : syracuseStep 677879 = 1016819) B1016819
theorem B677899 : Blo 674311 677899 := bstep (se 1 (by rfl) ⟨508424, by rfl⟩ : syracuseStep 677899 = 1016849) B1016849
theorem B7723025 : Blo 674311 7723025 := bstep (se 2 (by rfl) ⟨2896134, by rfl⟩ : syracuseStep 7723025 = 5792269) B5792269
theorem B677911 : Blo 674311 677911 := bstep (se 1 (by rfl) ⟨508433, by rfl⟩ : syracuseStep 677911 = 1016867) B1016867
theorem B677931 : Blo 674311 677931 := bstep (se 1 (by rfl) ⟨508448, by rfl⟩ : syracuseStep 677931 = 1016897) B1016897
theorem B677943 : Blo 674311 677943 := bstep (se 1 (by rfl) ⟨508457, by rfl⟩ : syracuseStep 677943 = 1016915) B1016915
theorem B677963 : Blo 674311 677963 := bstep (se 1 (by rfl) ⟨508472, by rfl⟩ : syracuseStep 677963 = 1016945) B1016945
theorem B677975 : Blo 674311 677975 := bstep (se 1 (by rfl) ⟨508481, by rfl⟩ : syracuseStep 677975 = 1016963) B1016963
theorem B677995 : Blo 674311 677995 := bstep (se 1 (by rfl) ⟨508496, by rfl⟩ : syracuseStep 677995 = 1016993) B1016993
theorem B678007 : Blo 674311 678007 := bstep (se 1 (by rfl) ⟨508505, by rfl⟩ : syracuseStep 678007 = 1017011) B1017011
theorem B678027 : Blo 674311 678027 := bstep (se 1 (by rfl) ⟨508520, by rfl⟩ : syracuseStep 678027 = 1017041) B1017041
theorem B678039 : Blo 674311 678039 := bstep (se 1 (by rfl) ⟨508529, by rfl⟩ : syracuseStep 678039 = 1017059) B1017059
theorem B678059 : Blo 674311 678059 := bstep (se 1 (by rfl) ⟨508544, by rfl⟩ : syracuseStep 678059 = 1017089) B1017089
theorem B678071 : Blo 674311 678071 := bstep (se 1 (by rfl) ⟨508553, by rfl⟩ : syracuseStep 678071 = 1017107) B1017107
theorem B2283713 : Blo 674311 2283713 := bstep (se 2 (by rfl) ⟨856392, by rfl⟩ : syracuseStep 2283713 = 1712785) B1712785
theorem B678091 : Blo 674311 678091 := bstep (se 1 (by rfl) ⟨508568, by rfl⟩ : syracuseStep 678091 = 1017137) B1017137
theorem B5560525 : Blo 674311 5560525 := bstep (se 3 (by rfl) ⟨1042598, by rfl⟩ : syracuseStep 5560525 = 2085197) B2085197
theorem B678103 : Blo 674311 678103 := bstep (se 1 (by rfl) ⟨508577, by rfl⟩ : syracuseStep 678103 = 1017155) B1017155
theorem B678123 : Blo 674311 678123 := bstep (se 1 (by rfl) ⟨508592, by rfl⟩ : syracuseStep 678123 = 1017185) B1017185
theorem B678135 : Blo 674311 678135 := bstep (se 1 (by rfl) ⟨508601, by rfl⟩ : syracuseStep 678135 = 1017203) B1017203
theorem B9230597 : Blo 674311 9230597 := bstep (se 4 (by rfl) ⟨865368, by rfl⟩ : syracuseStep 9230597 = 1730737) B1730737
theorem B678155 : Blo 674311 678155 := bstep (se 1 (by rfl) ⟨508616, by rfl⟩ : syracuseStep 678155 = 1017233) B1017233
theorem B3430673 : Blo 674311 3430673 := bstep (se 2 (by rfl) ⟨1286502, by rfl⟩ : syracuseStep 3430673 = 2573005) B2573005
theorem B678167 : Blo 674311 678167 := bstep (se 1 (by rfl) ⟨508625, by rfl⟩ : syracuseStep 678167 = 1017251) B1017251
theorem B678187 : Blo 674311 678187 := bstep (se 1 (by rfl) ⟨508640, by rfl⟩ : syracuseStep 678187 = 1017281) B1017281
theorem B678199 : Blo 674311 678199 := bstep (se 1 (by rfl) ⟨508649, by rfl⟩ : syracuseStep 678199 = 1017299) B1017299
theorem B678219 : Blo 674311 678219 := bstep (se 1 (by rfl) ⟨508664, by rfl⟩ : syracuseStep 678219 = 1017329) B1017329
theorem B678231 : Blo 674311 678231 := bstep (se 1 (by rfl) ⟨508673, by rfl⟩ : syracuseStep 678231 = 1017347) B1017347
theorem B1923421 : Blo 674311 1923421 := bstep (se 3 (by rfl) ⟨360641, by rfl⟩ : syracuseStep 1923421 = 721283) B721283
theorem B678251 : Blo 674311 678251 := bstep (se 1 (by rfl) ⟨508688, by rfl⟩ : syracuseStep 678251 = 1017377) B1017377
theorem B678263 : Blo 674311 678263 := bstep (se 1 (by rfl) ⟨508697, by rfl⟩ : syracuseStep 678263 = 1017395) B1017395
theorem B678283 : Blo 674311 678283 := bstep (se 1 (by rfl) ⟨508712, by rfl⟩ : syracuseStep 678283 = 1017425) B1017425
theorem B678295 : Blo 674311 678295 := bstep (se 1 (by rfl) ⟨508721, by rfl⟩ : syracuseStep 678295 = 1017443) B1017443
theorem B3430835 : Blo 674311 3430835 := bstep (se 1 (by rfl) ⟨2573126, by rfl⟩ : syracuseStep 3430835 = 5146253) B5146253
theorem B1628761 : Blo 674311 1628761 := bstep (se 2 (by rfl) ⟨610785, by rfl⟩ : syracuseStep 1628761 = 1221571) B1221571
theorem B1923763 : Blo 674311 1923763 := bstep (se 1 (by rfl) ⟨1442822, by rfl⟩ : syracuseStep 1923763 = 2885645) B2885645
theorem B2284253 : Blo 674311 2284253 := bstep (se 3 (by rfl) ⟨428297, by rfl⟩ : syracuseStep 2284253 = 856595) B856595
theorem B5561189 : Blo 674311 5561189 := bstep (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) B1042723
theorem B6511691 : Blo 674311 6511691 := bstep (se 1 (by rfl) ⟨4883768, by rfl⟩ : syracuseStep 6511691 = 9767537) B9767537
theorem B1138009 : Blo 674311 1138009 := bstep (se 2 (by rfl) ⟨426753, by rfl⟩ : syracuseStep 1138009 = 853507) B853507
theorem B1924697 : Blo 674311 1924697 := bstep (se 2 (by rfl) ⟨721761, by rfl⟩ : syracuseStep 1924697 = 1443523) B1443523
theorem B1171147 : Blo 674311 1171147 := bstep (se 1 (by rfl) ⟨878360, by rfl⟩ : syracuseStep 1171147 = 1756721) B1756721
theorem B2285387 : Blo 674311 2285387 := bstep (se 1 (by rfl) ⟨1714040, by rfl⟩ : syracuseStep 2285387 = 3428081) B3428081
theorem B1138583 : Blo 674311 1138583 := bstep (se 1 (by rfl) ⟨853937, by rfl⟩ : syracuseStep 1138583 = 1707875) B1707875
theorem B2056157 : Blo 674311 2056157 := bstep (se 3 (by rfl) ⟨385529, by rfl⟩ : syracuseStep 2056157 = 771059) B771059
theorem B1138711 : Blo 674311 1138711 := bstep (se 1 (by rfl) ⟨854033, by rfl⟩ : syracuseStep 1138711 = 1708067) B1708067
theorem B2285657 : Blo 674311 2285657 := bstep (se 2 (by rfl) ⟨857121, by rfl⟩ : syracuseStep 2285657 = 1714243) B1714243
theorem B1368257 : Blo 674311 1368257 := bstep (se 2 (by rfl) ⟨513096, by rfl⟩ : syracuseStep 1368257 = 1026193) B1026193
theorem B5497093 : Blo 674311 5497093 := bstep (se 4 (by rfl) ⟨515352, by rfl⟩ : syracuseStep 5497093 = 1030705) B1030705
theorem B3432779 : Blo 674311 3432779 := bstep (se 1 (by rfl) ⟨2574584, by rfl⟩ : syracuseStep 3432779 = 5149169) B5149169
theorem B12312931 : Blo 674311 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B3858961 : Blo 674311 3858961 := bstep (se 2 (by rfl) ⟨1447110, by rfl⟩ : syracuseStep 3858961 = 2894221) B2894221
theorem B1139339 : Blo 674311 1139339 := bstep (se 1 (by rfl) ⟨854504, by rfl⟩ : syracuseStep 1139339 = 1709009) B1709009
theorem B1139467 : Blo 674311 1139467 := bstep (se 1 (by rfl) ⟨854600, by rfl⟩ : syracuseStep 1139467 = 1709201) B1709201
theorem B2286359 : Blo 674311 2286359 := bstep (se 1 (by rfl) ⟨1714769, by rfl⟩ : syracuseStep 2286359 = 3429539) B3429539
theorem B7725941 : Blo 674311 7725941 := bstep (se 5 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 7725941 = 724307) B724307
theorem B1139609 : Blo 674311 1139609 := bstep (se 2 (by rfl) ⟨427353, by rfl⟩ : syracuseStep 1139609 = 854707) B854707
theorem B1926109 : Blo 674311 1926109 := bstep (se 3 (by rfl) ⟨361145, by rfl⟩ : syracuseStep 1926109 = 722291) B722291
theorem B1139737 : Blo 674311 1139737 := bstep (se 2 (by rfl) ⟨427401, by rfl⟩ : syracuseStep 1139737 = 854803) B854803
theorem B9757847 : Blo 674311 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B1926337 : Blo 674311 1926337 := bstep (se 2 (by rfl) ⟨722376, by rfl⟩ : syracuseStep 1926337 = 1444753) B1444753
theorem B2286899 : Blo 674311 2286899 := bstep (se 1 (by rfl) ⟨1715174, by rfl⟩ : syracuseStep 2286899 = 3430349) B3430349
theorem B1926679 : Blo 674311 1926679 := bstep (se 1 (by rfl) ⟨1445009, by rfl⟩ : syracuseStep 1926679 = 2890019) B2890019
theorem B2287169 : Blo 674311 2287169 := bstep (se 2 (by rfl) ⟨857688, by rfl⟩ : syracuseStep 2287169 = 1715377) B1715377
theorem B1140311 : Blo 674311 1140311 := bstep (se 1 (by rfl) ⟨855233, by rfl⟩ : syracuseStep 1140311 = 1710467) B1710467
theorem B1140439 : Blo 674311 1140439 := bstep (se 1 (by rfl) ⟨855329, by rfl⟩ : syracuseStep 1140439 = 1710659) B1710659
theorem B3008477 : Blo 674311 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B5138477 : Blo 674311 5138477 := bstep (se 3 (by rfl) ⟨963464, by rfl⟩ : syracuseStep 5138477 = 1926929) B1926929
theorem B2287709 : Blo 674311 2287709 := bstep (se 3 (by rfl) ⟨428945, by rfl⟩ : syracuseStep 2287709 = 857891) B857891
theorem B1927385 : Blo 674311 1927385 := bstep (se 2 (by rfl) ⟨722769, by rfl⟩ : syracuseStep 1927385 = 1445539) B1445539
theorem B1141067 : Blo 674311 1141067 := bstep (se 1 (by rfl) ⟨855800, by rfl⟩ : syracuseStep 1141067 = 1711601) B1711601
theorem B55568753 : Blo 674311 55568753 := bstep (se 2 (by rfl) ⟨20838282, by rfl⟩ : syracuseStep 55568753 = 41676565) B41676565
theorem B1141195 : Blo 674311 1141195 := bstep (se 1 (by rfl) ⟨855896, by rfl⟩ : syracuseStep 1141195 = 1711793) B1711793
theorem B5794253 : Blo 674311 5794253 := bstep (se 3 (by rfl) ⟨1086422, by rfl⟩ : syracuseStep 5794253 = 2172845) B2172845
theorem B1370699 : Blo 674311 1370699 := bstep (se 1 (by rfl) ⟨1028024, by rfl⟩ : syracuseStep 1370699 = 2056049) B2056049
theorem B1141337 : Blo 674311 1141337 := bstep (se 2 (by rfl) ⟨428001, by rfl⟩ : syracuseStep 1141337 = 856003) B856003
theorem B1141465 : Blo 674311 1141465 := bstep (se 2 (by rfl) ⟨428049, by rfl⟩ : syracuseStep 1141465 = 856099) B856099
theorem B4123457 : Blo 674311 4123457 := bstep (se 2 (by rfl) ⟨1546296, by rfl⟩ : syracuseStep 4123457 = 3092593) B3092593
theorem B2288843 : Blo 674311 2288843 := bstep (se 1 (by rfl) ⟨1716632, by rfl⟩ : syracuseStep 2288843 = 3433265) B3433265
theorem B1142039 : Blo 674311 1142039 := bstep (se 1 (by rfl) ⟨856529, by rfl⟩ : syracuseStep 1142039 = 1713059) B1713059
theorem B4877603 : Blo 674311 4877603 := bstep (se 1 (by rfl) ⟨3658202, by rfl⟩ : syracuseStep 4877603 = 7316405) B7316405
theorem B814423 : Blo 674311 814423 := bstep (se 1 (by rfl) ⟨610817, by rfl⟩ : syracuseStep 814423 = 1221635) B1221635
theorem B1142167 : Blo 674311 1142167 := bstep (se 1 (by rfl) ⟨856625, by rfl⟩ : syracuseStep 1142167 = 1713251) B1713251
theorem B2289113 : Blo 674311 2289113 := bstep (se 2 (by rfl) ⟨858417, by rfl⟩ : syracuseStep 2289113 = 1716835) B1716835
theorem B1371737 : Blo 674311 1371737 := bstep (se 2 (by rfl) ⟨514401, by rfl⟩ : syracuseStep 1371737 = 1028803) B1028803
theorem B1011467 : Blo 674311 1011467 := bstep (se 1 (by rfl) ⟨758600, by rfl⟩ : syracuseStep 1011467 = 1517201) B1517201
theorem B1011479 : Blo 674311 1011479 := bstep (se 1 (by rfl) ⟨758609, by rfl⟩ : syracuseStep 1011479 = 1517219) B1517219
theorem B1929025 : Blo 674311 1929025 := bstep (se 2 (by rfl) ⟨723384, by rfl⟩ : syracuseStep 1929025 = 1446769) B1446769
theorem B1011545 : Blo 674311 1011545 := bstep (se 2 (by rfl) ⟨379329, by rfl⟩ : syracuseStep 1011545 = 758659) B758659
theorem B3862403 : Blo 674311 3862403 := bstep (se 1 (by rfl) ⟨2896802, by rfl⟩ : syracuseStep 3862403 = 5793605) B5793605
theorem B1011659 : Blo 674311 1011659 := bstep (se 1 (by rfl) ⟨758744, by rfl⟩ : syracuseStep 1011659 = 1517489) B1517489
theorem B1011671 : Blo 674311 1011671 := bstep (se 1 (by rfl) ⟨758753, by rfl⟩ : syracuseStep 1011671 = 1517507) B1517507
theorem B1142795 : Blo 674311 1142795 := bstep (se 1 (by rfl) ⟨857096, by rfl⟩ : syracuseStep 1142795 = 1714193) B1714193
theorem B1011737 : Blo 674311 1011737 := bstep (se 2 (by rfl) ⟨379401, by rfl⟩ : syracuseStep 1011737 = 758803) B758803
theorem B1011851 : Blo 674311 1011851 := bstep (se 1 (by rfl) ⟨758888, by rfl⟩ : syracuseStep 1011851 = 1517777) B1517777
theorem B1142923 : Blo 674311 1142923 := bstep (se 1 (by rfl) ⟨857192, by rfl⟩ : syracuseStep 1142923 = 1714385) B1714385
theorem B1011863 : Blo 674311 1011863 := bstep (se 1 (by rfl) ⟨758897, by rfl⟩ : syracuseStep 1011863 = 1517795) B1517795
theorem B684235 : Blo 674311 684235 := bstep (se 1 (by rfl) ⟨513176, by rfl⟩ : syracuseStep 684235 = 1026353) B1026353
theorem B1011929 : Blo 674311 1011929 := bstep (se 2 (by rfl) ⟨379473, by rfl⟩ : syracuseStep 1011929 = 758947) B758947
theorem B913675 : Blo 674311 913675 := bstep (se 1 (by rfl) ⟨685256, by rfl⟩ : syracuseStep 913675 = 1370513) B1370513
theorem B1143065 : Blo 674311 1143065 := bstep (se 2 (by rfl) ⟨428649, by rfl⟩ : syracuseStep 1143065 = 857299) B857299
theorem B1012043 : Blo 674311 1012043 := bstep (se 1 (by rfl) ⟨759032, by rfl⟩ : syracuseStep 1012043 = 1518065) B1518065
theorem B913739 : Blo 674311 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B1012055 : Blo 674311 1012055 := bstep (se 1 (by rfl) ⟨759041, by rfl⟩ : syracuseStep 1012055 = 1518083) B1518083
theorem B1012121 : Blo 674311 1012121 := bstep (se 2 (by rfl) ⟨379545, by rfl⟩ : syracuseStep 1012121 = 759091) B759091
theorem B1143193 : Blo 674311 1143193 := bstep (se 2 (by rfl) ⟨428697, by rfl⟩ : syracuseStep 1143193 = 857395) B857395
theorem B1012235 : Blo 674311 1012235 := bstep (se 1 (by rfl) ⟨759176, by rfl⟩ : syracuseStep 1012235 = 1518353) B1518353
theorem B1012247 : Blo 674311 1012247 := bstep (se 1 (by rfl) ⟨759185, by rfl⟩ : syracuseStep 1012247 = 1518371) B1518371
theorem B1012313 : Blo 674311 1012313 := bstep (se 2 (by rfl) ⟨379617, by rfl⟩ : syracuseStep 1012313 = 759235) B759235
theorem B1012427 : Blo 674311 1012427 := bstep (se 1 (by rfl) ⟨759320, by rfl⟩ : syracuseStep 1012427 = 1518641) B1518641
theorem B1012439 : Blo 674311 1012439 := bstep (se 1 (by rfl) ⟨759329, by rfl⟩ : syracuseStep 1012439 = 1518659) B1518659
theorem B3076829 : Blo 674311 3076829 := bstep (se 3 (by rfl) ⟨576905, by rfl⟩ : syracuseStep 3076829 = 1153811) B1153811
theorem B1012505 : Blo 674311 1012505 := bstep (se 2 (by rfl) ⟨379689, by rfl⟩ : syracuseStep 1012505 = 759379) B759379
theorem B1012619 : Blo 674311 1012619 := bstep (se 1 (by rfl) ⟨759464, by rfl⟩ : syracuseStep 1012619 = 1518929) B1518929
theorem B1012631 : Blo 674311 1012631 := bstep (se 1 (by rfl) ⟨759473, by rfl⟩ : syracuseStep 1012631 = 1518947) B1518947
theorem B1143767 : Blo 674311 1143767 := bstep (se 1 (by rfl) ⟨857825, by rfl⟩ : syracuseStep 1143767 = 1715651) B1715651
theorem B1012697 : Blo 674311 1012697 := bstep (se 2 (by rfl) ⟨379761, by rfl⟩ : syracuseStep 1012697 = 759523) B759523
theorem B1012811 : Blo 674311 1012811 := bstep (se 1 (by rfl) ⟨759608, by rfl⟩ : syracuseStep 1012811 = 1519217) B1519217
theorem B1012823 : Blo 674311 1012823 := bstep (se 1 (by rfl) ⟨759617, by rfl⟩ : syracuseStep 1012823 = 1519235) B1519235
theorem B1143895 : Blo 674311 1143895 := bstep (se 1 (by rfl) ⟨857921, by rfl⟩ : syracuseStep 1143895 = 1715843) B1715843
theorem B1012889 : Blo 674311 1012889 := bstep (se 2 (by rfl) ⟨379833, by rfl⟩ : syracuseStep 1012889 = 759667) B759667
theorem B1832129 : Blo 674311 1832129 := bstep (se 2 (by rfl) ⟨687048, by rfl⟩ : syracuseStep 1832129 = 1374097) B1374097
theorem B1013003 : Blo 674311 1013003 := bstep (se 1 (by rfl) ⟨759752, by rfl⟩ : syracuseStep 1013003 = 1519505) B1519505
theorem B1013015 : Blo 674311 1013015 := bstep (se 1 (by rfl) ⟨759761, by rfl⟩ : syracuseStep 1013015 = 1519523) B1519523
theorem B1013081 : Blo 674311 1013081 := bstep (se 2 (by rfl) ⟨379905, by rfl⟩ : syracuseStep 1013081 = 759811) B759811
theorem B2880947 : Blo 674311 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B1013195 : Blo 674311 1013195 := bstep (se 1 (by rfl) ⟨759896, by rfl⟩ : syracuseStep 1013195 = 1519793) B1519793
theorem B1013207 : Blo 674311 1013207 := bstep (se 1 (by rfl) ⟨759905, by rfl⟩ : syracuseStep 1013207 = 1519811) B1519811
theorem B1373707 : Blo 674311 1373707 := bstep (se 1 (by rfl) ⟨1030280, by rfl⟩ : syracuseStep 1373707 = 2060561) B2060561
theorem B1013273 : Blo 674311 1013273 := bstep (se 2 (by rfl) ⟨379977, by rfl⟩ : syracuseStep 1013273 = 759955) B759955
theorem B2881099 : Blo 674311 2881099 := bstep (se 1 (by rfl) ⟨2160824, by rfl⟩ : syracuseStep 2881099 = 4321649) B4321649
theorem B1013387 : Blo 674311 1013387 := bstep (se 1 (by rfl) ⟨760040, by rfl⟩ : syracuseStep 1013387 = 1520081) B1520081
theorem B2881169 : Blo 674311 2881169 := bstep (se 2 (by rfl) ⟨1080438, by rfl⟩ : syracuseStep 2881169 = 2160877) B2160877
theorem B1013399 : Blo 674311 1013399 := bstep (se 1 (by rfl) ⟨760049, by rfl⟩ : syracuseStep 1013399 = 1520099) B1520099
theorem B685751 : Blo 674311 685751 := bstep (se 1 (by rfl) ⟨514313, by rfl⟩ : syracuseStep 685751 = 1028627) B1028627
theorem B1144523 : Blo 674311 1144523 := bstep (se 1 (by rfl) ⟨858392, by rfl⟩ : syracuseStep 1144523 = 1716785) B1716785
theorem B1013465 : Blo 674311 1013465 := bstep (se 2 (by rfl) ⟨380049, by rfl⟩ : syracuseStep 1013465 = 760099) B760099
theorem B1832669 : Blo 674311 1832669 := bstep (se 3 (by rfl) ⟨343625, by rfl⟩ : syracuseStep 1832669 = 687251) B687251
theorem B2062045 : Blo 674311 2062045 := bstep (se 3 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 2062045 = 773267) B773267
theorem B1013579 : Blo 674311 1013579 := bstep (se 1 (by rfl) ⟨760184, by rfl⟩ : syracuseStep 1013579 = 1520369) B1520369
theorem B1144651 : Blo 674311 1144651 := bstep (se 1 (by rfl) ⟨858488, by rfl⟩ : syracuseStep 1144651 = 1716977) B1716977
theorem B1013591 : Blo 674311 1013591 := bstep (se 1 (by rfl) ⟨760193, by rfl⟩ : syracuseStep 1013591 = 1520387) B1520387
theorem B5142365 : Blo 674311 5142365 := bstep (se 3 (by rfl) ⟨964193, by rfl⟩ : syracuseStep 5142365 = 1928387) B1928387
theorem B1013657 : Blo 674311 1013657 := bstep (se 2 (by rfl) ⟨380121, by rfl⟩ : syracuseStep 1013657 = 760243) B760243
theorem B4323289 : Blo 674311 4323289 := bstep (se 2 (by rfl) ⟨1621233, by rfl⟩ : syracuseStep 4323289 = 3242467) B3242467
theorem B1013771 : Blo 674311 1013771 := bstep (se 1 (by rfl) ⟨760328, by rfl⟩ : syracuseStep 1013771 = 1520657) B1520657
theorem B1013783 : Blo 674311 1013783 := bstep (se 1 (by rfl) ⟨760337, by rfl⟩ : syracuseStep 1013783 = 1520675) B1520675
theorem B1013849 : Blo 674311 1013849 := bstep (se 2 (by rfl) ⟨380193, by rfl⟩ : syracuseStep 1013849 = 760387) B760387
theorem B1013963 : Blo 674311 1013963 := bstep (se 1 (by rfl) ⟨760472, by rfl⟩ : syracuseStep 1013963 = 1520945) B1520945
theorem B1013975 : Blo 674311 1013975 := bstep (se 1 (by rfl) ⟨760481, by rfl⟩ : syracuseStep 1013975 = 1520963) B1520963
theorem B1014041 : Blo 674311 1014041 := bstep (se 2 (by rfl) ⟨380265, by rfl⟩ : syracuseStep 1014041 = 760531) B760531
theorem B1014155 : Blo 674311 1014155 := bstep (se 1 (by rfl) ⟨760616, by rfl⟩ : syracuseStep 1014155 = 1521233) B1521233
theorem B1014167 : Blo 674311 1014167 := bstep (se 1 (by rfl) ⟨760625, by rfl⟩ : syracuseStep 1014167 = 1521251) B1521251
theorem B1014233 : Blo 674311 1014233 := bstep (se 2 (by rfl) ⟨380337, by rfl⟩ : syracuseStep 1014233 = 760675) B760675
theorem B686647 : Blo 674311 686647 := bstep (se 1 (by rfl) ⟨514985, by rfl⟩ : syracuseStep 686647 = 1029971) B1029971
theorem B4323905 : Blo 674311 4323905 := bstep (se 2 (by rfl) ⟨1621464, by rfl⟩ : syracuseStep 4323905 = 3242929) B3242929
theorem B1538635 : Blo 674311 1538635 := bstep (se 1 (by rfl) ⟨1153976, by rfl⟩ : syracuseStep 1538635 = 2307953) B2307953
theorem B1014347 : Blo 674311 1014347 := bstep (se 1 (by rfl) ⟨760760, by rfl⟩ : syracuseStep 1014347 = 1521521) B1521521
theorem B1014359 : Blo 674311 1014359 := bstep (se 1 (by rfl) ⟨760769, by rfl⟩ : syracuseStep 1014359 = 1521539) B1521539
theorem B1014425 : Blo 674311 1014425 := bstep (se 2 (by rfl) ⟨380409, by rfl⟩ : syracuseStep 1014425 = 760819) B760819
theorem B1374923 : Blo 674311 1374923 := bstep (se 1 (by rfl) ⟨1031192, by rfl⟩ : syracuseStep 1374923 = 2062385) B2062385
theorem B1440499 : Blo 674311 1440499 := bstep (se 1 (by rfl) ⟨1080374, by rfl⟩ : syracuseStep 1440499 = 2160749) B2160749
theorem B1014539 : Blo 674311 1014539 := bstep (se 1 (by rfl) ⟨760904, by rfl⟩ : syracuseStep 1014539 = 1521809) B1521809
theorem B1014551 : Blo 674311 1014551 := bstep (se 1 (by rfl) ⟨760913, by rfl⟩ : syracuseStep 1014551 = 1521827) B1521827
theorem B1014617 : Blo 674311 1014617 := bstep (se 2 (by rfl) ⟨380481, by rfl⟩ : syracuseStep 1014617 = 760963) B760963
theorem B1014731 : Blo 674311 1014731 := bstep (se 1 (by rfl) ⟨761048, by rfl⟩ : syracuseStep 1014731 = 1522097) B1522097
theorem B1014743 : Blo 674311 1014743 := bstep (se 1 (by rfl) ⟨761057, by rfl⟩ : syracuseStep 1014743 = 1522115) B1522115
theorem B1440755 : Blo 674311 1440755 := bstep (se 1 (by rfl) ⟨1080566, by rfl⟩ : syracuseStep 1440755 = 2161133) B2161133
theorem B1014809 : Blo 674311 1014809 := bstep (se 2 (by rfl) ⟨380553, by rfl⟩ : syracuseStep 1014809 = 761107) B761107
theorem B1014923 : Blo 674311 1014923 := bstep (se 1 (by rfl) ⟨761192, by rfl⟩ : syracuseStep 1014923 = 1522385) B1522385
theorem B1014935 : Blo 674311 1014935 := bstep (se 1 (by rfl) ⟨761201, by rfl⟩ : syracuseStep 1014935 = 1522403) B1522403
theorem B1015001 : Blo 674311 1015001 := bstep (se 2 (by rfl) ⟨380625, by rfl⟩ : syracuseStep 1015001 = 761251) B761251
theorem B2784473 : Blo 674311 2784473 := bstep (se 2 (by rfl) ⟨1044177, by rfl⟩ : syracuseStep 2784473 = 2088355) B2088355
theorem B2882861 : Blo 674311 2882861 := bstep (se 3 (by rfl) ⟨540536, by rfl⟩ : syracuseStep 2882861 = 1081073) B1081073
theorem B18513197 : Blo 674311 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B4947245 : Blo 674311 4947245 := bstep (se 3 (by rfl) ⟨927608, by rfl⟩ : syracuseStep 4947245 = 1855217) B1855217
theorem B1015115 : Blo 674311 1015115 := bstep (se 1 (by rfl) ⟨761336, by rfl⟩ : syracuseStep 1015115 = 1522673) B1522673
theorem B1015127 : Blo 674311 1015127 := bstep (se 1 (by rfl) ⟨761345, by rfl⟩ : syracuseStep 1015127 = 1522691) B1522691
theorem B1015193 : Blo 674311 1015193 := bstep (se 2 (by rfl) ⟨380697, by rfl⟩ : syracuseStep 1015193 = 761395) B761395
theorem B1015307 : Blo 674311 1015307 := bstep (se 1 (by rfl) ⟨761480, by rfl⟩ : syracuseStep 1015307 = 1522961) B1522961
theorem B1015319 : Blo 674311 1015319 := bstep (se 1 (by rfl) ⟨761489, by rfl⟩ : syracuseStep 1015319 = 1522979) B1522979
theorem B1015385 : Blo 674311 1015385 := bstep (se 2 (by rfl) ⟨380769, by rfl⟩ : syracuseStep 1015385 = 761539) B761539
theorem B720523 : Blo 674311 720523 := bstep (se 1 (by rfl) ⟨540392, by rfl⟩ : syracuseStep 720523 = 1080785) B1080785
theorem B1015499 : Blo 674311 1015499 := bstep (se 1 (by rfl) ⟨761624, by rfl⟩ : syracuseStep 1015499 = 1523249) B1523249
theorem B1015511 : Blo 674311 1015511 := bstep (se 1 (by rfl) ⟨761633, by rfl⟩ : syracuseStep 1015511 = 1523267) B1523267
theorem B1015577 : Blo 674311 1015577 := bstep (se 2 (by rfl) ⟨380841, by rfl⟩ : syracuseStep 1015577 = 761683) B761683
theorem B1015691 : Blo 674311 1015691 := bstep (se 1 (by rfl) ⟨761768, by rfl⟩ : syracuseStep 1015691 = 1523537) B1523537
theorem B1015703 : Blo 674311 1015703 := bstep (se 1 (by rfl) ⟨761777, by rfl⟩ : syracuseStep 1015703 = 1523555) B1523555
theorem B1441729 : Blo 674311 1441729 := bstep (se 2 (by rfl) ⟨540648, by rfl⟩ : syracuseStep 1441729 = 1081297) B1081297
theorem B2883545 : Blo 674311 2883545 := bstep (se 2 (by rfl) ⟨1081329, by rfl⟩ : syracuseStep 2883545 = 2162659) B2162659
theorem B1015769 : Blo 674311 1015769 := bstep (se 2 (by rfl) ⟨380913, by rfl⟩ : syracuseStep 1015769 = 761827) B761827
theorem B1015823 : Blo 674311 1015823 := bstep (se 1 (by rfl) ⟨761867, by rfl⟩ : syracuseStep 1015823 = 1523735) B1523735
theorem B1015865 : Blo 674311 1015865 := bstep (se 2 (by rfl) ⟨380949, by rfl⟩ : syracuseStep 1015865 = 761899) B761899
theorem B1015943 : Blo 674311 1015943 := bstep (se 1 (by rfl) ⟨761957, by rfl⟩ : syracuseStep 1015943 = 1523915) B1523915
theorem B1015979 : Blo 674311 1015979 := bstep (se 1 (by rfl) ⟨761984, by rfl⟩ : syracuseStep 1015979 = 1523969) B1523969
theorem B1016009 : Blo 674311 1016009 := bstep (se 2 (by rfl) ⟨381003, by rfl⟩ : syracuseStep 1016009 = 762007) B762007
theorem B1016123 : Blo 674311 1016123 := bstep (se 1 (by rfl) ⟨762092, by rfl⟩ : syracuseStep 1016123 = 1524185) B1524185
theorem B1016183 : Blo 674311 1016183 := bstep (se 1 (by rfl) ⟨762137, by rfl⟩ : syracuseStep 1016183 = 1524275) B1524275
theorem B1016207 : Blo 674311 1016207 := bstep (se 1 (by rfl) ⟨762155, by rfl⟩ : syracuseStep 1016207 = 1524311) B1524311
theorem B1016249 : Blo 674311 1016249 := bstep (se 2 (by rfl) ⟨381093, by rfl⟩ : syracuseStep 1016249 = 762187) B762187
theorem B16417241 : Blo 674311 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B52724195 : Blo 674311 52724195 := bstep (se 1 (by rfl) ⟨39543146, by rfl⟩ : syracuseStep 52724195 = 79086293) B79086293
theorem B1016327 : Blo 674311 1016327 := bstep (se 1 (by rfl) ⟨762245, by rfl⟩ : syracuseStep 1016327 = 1524491) B1524491
theorem B1016363 : Blo 674311 1016363 := bstep (se 1 (by rfl) ⟨762272, by rfl⟩ : syracuseStep 1016363 = 1524545) B1524545
theorem B1016393 : Blo 674311 1016393 := bstep (se 2 (by rfl) ⟨381147, by rfl⟩ : syracuseStep 1016393 = 762295) B762295
theorem B4326007 : Blo 674311 4326007 := bstep (se 1 (by rfl) ⟨3244505, by rfl⟩ : syracuseStep 4326007 = 6489011) B6489011
theorem B1016507 : Blo 674311 1016507 := bstep (se 1 (by rfl) ⟨762380, by rfl⟩ : syracuseStep 1016507 = 1524761) B1524761
theorem B5145281 : Blo 674311 5145281 := bstep (se 2 (by rfl) ⟨1929480, by rfl⟩ : syracuseStep 5145281 = 3858961) B3858961
theorem B7045861 : Blo 674311 7045861 := bstep (se 4 (by rfl) ⟨660549, by rfl⟩ : syracuseStep 7045861 = 1321099) B1321099
theorem B1016567 : Blo 674311 1016567 := bstep (se 1 (by rfl) ⟨762425, by rfl⟩ : syracuseStep 1016567 = 1524851) B1524851
theorem B1016591 : Blo 674311 1016591 := bstep (se 1 (by rfl) ⟨762443, by rfl⟩ : syracuseStep 1016591 = 1524887) B1524887
theorem B1016633 : Blo 674311 1016633 := bstep (se 2 (by rfl) ⟨381237, by rfl⟩ : syracuseStep 1016633 = 762475) B762475
theorem B1016711 : Blo 674311 1016711 := bstep (se 1 (by rfl) ⟨762533, by rfl⟩ : syracuseStep 1016711 = 1525067) B1525067
theorem B1016747 : Blo 674311 1016747 := bstep (se 1 (by rfl) ⟨762560, by rfl⟩ : syracuseStep 1016747 = 1525121) B1525121
theorem B1016777 : Blo 674311 1016777 := bstep (se 2 (by rfl) ⟨381291, by rfl⟩ : syracuseStep 1016777 = 762583) B762583
theorem B1016891 : Blo 674311 1016891 := bstep (se 1 (by rfl) ⟨762668, by rfl⟩ : syracuseStep 1016891 = 1525337) B1525337
theorem B1016951 : Blo 674311 1016951 := bstep (se 1 (by rfl) ⟨762713, by rfl⟩ : syracuseStep 1016951 = 1525427) B1525427
theorem B1016975 : Blo 674311 1016975 := bstep (se 1 (by rfl) ⟨762731, by rfl⟩ : syracuseStep 1016975 = 1525463) B1525463
theorem B5473453 : Blo 674311 5473453 := bstep (se 3 (by rfl) ⟨1026272, by rfl⟩ : syracuseStep 5473453 = 2052545) B2052545
theorem B1017017 : Blo 674311 1017017 := bstep (se 2 (by rfl) ⟨381381, by rfl⟩ : syracuseStep 1017017 = 762763) B762763
theorem B1017095 : Blo 674311 1017095 := bstep (se 1 (by rfl) ⟨762821, by rfl⟩ : syracuseStep 1017095 = 1525643) B1525643
theorem B1017131 : Blo 674311 1017131 := bstep (se 1 (by rfl) ⟨762848, by rfl⟩ : syracuseStep 1017131 = 1525697) B1525697
theorem B1017161 : Blo 674311 1017161 := bstep (se 2 (by rfl) ⟨381435, by rfl⟩ : syracuseStep 1017161 = 762871) B762871
theorem B3900761 : Blo 674311 3900761 := bstep (se 2 (by rfl) ⟨1462785, by rfl⟩ : syracuseStep 3900761 = 2925571) B2925571
theorem B20874631 : Blo 674311 20874631 := bstep (se 1 (by rfl) ⟨15655973, by rfl⟩ : syracuseStep 20874631 = 31311947) B31311947
theorem B1017275 : Blo 674311 1017275 := bstep (se 1 (by rfl) ⟨762956, by rfl⟩ : syracuseStep 1017275 = 1525913) B1525913
theorem B1017335 : Blo 674311 1017335 := bstep (se 1 (by rfl) ⟨763001, by rfl⟩ : syracuseStep 1017335 = 1526003) B1526003
theorem B1017359 : Blo 674311 1017359 := bstep (se 1 (by rfl) ⟨763019, by rfl⟩ : syracuseStep 1017359 = 1526039) B1526039
theorem B1017401 : Blo 674311 1017401 := bstep (se 2 (by rfl) ⟨381525, by rfl⟩ : syracuseStep 1017401 = 763051) B763051
theorem B22808141 : Blo 674311 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B2885321 : Blo 674311 2885321 := bstep (se 2 (by rfl) ⟨1081995, by rfl⟩ : syracuseStep 2885321 = 2163991) B2163991
theorem B854059 : Blo 674311 854059 := bstep (se 1 (by rfl) ⟨640544, by rfl⟩ : syracuseStep 854059 = 1281089) B1281089
theorem B1443899 : Blo 674311 1443899 := bstep (se 1 (by rfl) ⟨1082924, by rfl⟩ : syracuseStep 1443899 = 2165849) B2165849
theorem B2164823 : Blo 674311 2164823 := bstep (se 1 (by rfl) ⟨1623617, by rfl⟩ : syracuseStep 2164823 = 3247235) B3247235
theorem B1280299 : Blo 674311 1280299 := bstep (se 1 (by rfl) ⟨960224, by rfl⟩ : syracuseStep 1280299 = 1920449) B1920449
theorem B1706953 : Blo 674311 1706953 := bstep (se 2 (by rfl) ⟨640107, by rfl⟩ : syracuseStep 1706953 = 1280215) B1280215
theorem B855031 : Blo 674311 855031 := bstep (se 1 (by rfl) ⟨641273, by rfl⟩ : syracuseStep 855031 = 1282547) B1282547
theorem B1084475 : Blo 674311 1084475 := bstep (se 1 (by rfl) ⟨813356, by rfl⟩ : syracuseStep 1084475 = 1626713) B1626713
theorem B26020925 : Blo 674311 26020925 := bstep (se 3 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 26020925 = 9757847) B9757847
theorem B1707095 : Blo 674311 1707095 := bstep (se 1 (by rfl) ⟨1280321, by rfl⟩ : syracuseStep 1707095 = 2560643) B2560643
theorem B13896791 : Blo 674311 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B822415 : Blo 674311 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B855355 : Blo 674311 855355 := bstep (se 1 (by rfl) ⟨641516, by rfl⟩ : syracuseStep 855355 = 1283033) B1283033
theorem B1281415 : Blo 674311 1281415 := bstep (se 1 (by rfl) ⟨961061, by rfl⟩ : syracuseStep 1281415 = 1922123) B1922123
theorem B2887235 : Blo 674311 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B3903095 : Blo 674311 3903095 := bstep (se 1 (by rfl) ⟨2927321, by rfl⟩ : syracuseStep 3903095 = 5854643) B5854643
theorem B2887559 : Blo 674311 2887559 := bstep (se 1 (by rfl) ⟨2165669, by rfl⟩ : syracuseStep 2887559 = 4331339) B4331339
theorem B1281977 : Blo 674311 1281977 := bstep (se 2 (by rfl) ⟨480741, by rfl⟩ : syracuseStep 1281977 = 961483) B961483
theorem B5148683 : Blo 674311 5148683 := bstep (se 1 (by rfl) ⟨3861512, by rfl⟩ : syracuseStep 5148683 = 7723025) B7723025
theorem B856327 : Blo 674311 856327 := bstep (se 1 (by rfl) ⟨642245, by rfl⟩ : syracuseStep 856327 = 1284491) B1284491
theorem B1085897 : Blo 674311 1085897 := bstep (se 2 (by rfl) ⟨407211, by rfl⟩ : syracuseStep 1085897 = 814423) B814423
theorem B3707459 : Blo 674311 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B856747 : Blo 674311 856747 := bstep (se 1 (by rfl) ⟨642560, by rfl⟩ : syracuseStep 856747 = 1285121) B1285121
theorem B856975 : Blo 674311 856975 := bstep (se 1 (by rfl) ⟨642731, by rfl⟩ : syracuseStep 856975 = 1285463) B1285463
theorem B1283131 : Blo 674311 1283131 := bstep (se 1 (by rfl) ⟨962348, by rfl⟩ : syracuseStep 1283131 = 1924697) B1924697
theorem B1709171 : Blo 674311 1709171 := bstep (se 1 (by rfl) ⟨1281878, by rfl⟩ : syracuseStep 1709171 = 2563757) B2563757
theorem B759055 : Blo 674311 759055 := bstep (se 1 (by rfl) ⟨569291, by rfl⟩ : syracuseStep 759055 = 1138583) B1138583
theorem B1283617 : Blo 674311 1283617 := bstep (se 2 (by rfl) ⟨481356, by rfl⟩ : syracuseStep 1283617 = 962713) B962713
theorem B1709687 : Blo 674311 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B857719 : Blo 674311 857719 := bstep (se 1 (by rfl) ⟨643289, by rfl⟩ : syracuseStep 857719 = 1286579) B1286579
theorem B1218233 : Blo 674311 1218233 := bstep (se 2 (by rfl) ⟨456837, by rfl⟩ : syracuseStep 1218233 = 913675) B913675
theorem B1545913 : Blo 674311 1545913 := bstep (se 2 (by rfl) ⟨579717, by rfl⟩ : syracuseStep 1545913 = 1159435) B1159435
theorem B759559 : Blo 674311 759559 := bstep (se 1 (by rfl) ⟨569669, by rfl⟩ : syracuseStep 759559 = 1139339) B1139339
theorem B5150627 : Blo 674311 5150627 := bstep (se 1 (by rfl) ⟨3862970, by rfl⟩ : syracuseStep 5150627 = 7725941) B7725941
theorem B759739 : Blo 674311 759739 := bstep (se 1 (by rfl) ⟨569804, by rfl⟩ : syracuseStep 759739 = 1139609) B1139609
theorem B858043 : Blo 674311 858043 := bstep (se 1 (by rfl) ⟨643532, by rfl⟩ : syracuseStep 858043 = 1287065) B1287065
theorem B2889847 : Blo 674311 2889847 := bstep (se 1 (by rfl) ⟨2167385, by rfl⟩ : syracuseStep 2889847 = 4334771) B4334771
theorem B17307917 : Blo 674311 17307917 := bstep (se 3 (by rfl) ⟨3245234, by rfl⟩ : syracuseStep 17307917 = 6490469) B6490469
theorem B3479867 : Blo 674311 3479867 := bstep (se 1 (by rfl) ⟨2609900, by rfl⟩ : syracuseStep 3479867 = 5219801) B5219801
theorem B760207 : Blo 674311 760207 := bstep (se 1 (by rfl) ⟨570155, by rfl⟩ : syracuseStep 760207 = 1140311) B1140311
theorem B1710679 : Blo 674311 1710679 := bstep (se 1 (by rfl) ⟨1283009, by rfl⟩ : syracuseStep 1710679 = 2566019) B2566019
theorem B2169463 : Blo 674311 2169463 := bstep (se 1 (by rfl) ⟨1627097, by rfl⟩ : syracuseStep 2169463 = 3254195) B3254195
theorem B2005651 : Blo 674311 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B3250925 : Blo 674311 3250925 := bstep (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) B1219097
theorem B924475 : Blo 674311 924475 := bstep (se 1 (by rfl) ⟨693356, by rfl⟩ : syracuseStep 924475 = 1386713) B1386713
theorem B1284923 : Blo 674311 1284923 := bstep (se 1 (by rfl) ⟨963692, by rfl⟩ : syracuseStep 1284923 = 1927385) B1927385
theorem B1710983 : Blo 674311 1710983 := bstep (se 1 (by rfl) ⟨1283237, by rfl⟩ : syracuseStep 1710983 = 2566475) B2566475
theorem B760711 : Blo 674311 760711 := bstep (se 1 (by rfl) ⟨570533, by rfl⟩ : syracuseStep 760711 = 1141067) B1141067
theorem B1711115 : Blo 674311 1711115 := bstep (se 1 (by rfl) ⟨1283336, by rfl⟩ : syracuseStep 1711115 = 2566673) B2566673
theorem B2169899 : Blo 674311 2169899 := bstep (se 1 (by rfl) ⟨1627424, by rfl⟩ : syracuseStep 2169899 = 3254849) B3254849
theorem B760891 : Blo 674311 760891 := bstep (se 1 (by rfl) ⟨570668, by rfl⟩ : syracuseStep 760891 = 1141337) B1141337
theorem B1645655 : Blo 674311 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B1285409 : Blo 674311 1285409 := bstep (se 2 (by rfl) ⟨482028, by rfl⟩ : syracuseStep 1285409 = 964057) B964057
theorem B3841465 : Blo 674311 3841465 := bstep (se 2 (by rfl) ⟨1440549, by rfl⟩ : syracuseStep 3841465 = 2881099) B2881099
theorem B1285561 : Blo 674311 1285561 := bstep (se 2 (by rfl) ⟨482085, by rfl⟩ : syracuseStep 1285561 = 964171) B964171
theorem B1711631 : Blo 674311 1711631 := bstep (se 1 (by rfl) ⟨1283723, by rfl⟩ : syracuseStep 1711631 = 2567447) B2567447
theorem B761359 : Blo 674311 761359 := bstep (se 1 (by rfl) ⟨571019, by rfl⟩ : syracuseStep 761359 = 1142039) B1142039
theorem B3251735 : Blo 674311 3251735 := bstep (se 1 (by rfl) ⟨2438801, by rfl⟩ : syracuseStep 3251735 = 4877603) B4877603
theorem B2891351 : Blo 674311 2891351 := bstep (se 1 (by rfl) ⟨2168513, by rfl⟩ : syracuseStep 2891351 = 4337027) B4337027
theorem B1711763 : Blo 674311 1711763 := bstep (se 1 (by rfl) ⟨1283822, by rfl⟩ : syracuseStep 1711763 = 2567645) B2567645
theorem B3252001 : Blo 674311 3252001 := bstep (se 2 (by rfl) ⟨1219500, by rfl⟩ : syracuseStep 3252001 = 2439001) B2439001
theorem B32907059 : Blo 674311 32907059 := bstep (se 1 (by rfl) ⟨24680294, by rfl⟩ : syracuseStep 32907059 = 49360589) B49360589
theorem B761863 : Blo 674311 761863 := bstep (se 1 (by rfl) ⟨571397, by rfl⟩ : syracuseStep 761863 = 1142795) B1142795
theorem B3416093 : Blo 674311 3416093 := bstep (se 3 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 3416093 = 1281035) B1281035
theorem B762043 : Blo 674311 762043 := bstep (se 1 (by rfl) ⟨571532, by rfl⟩ : syracuseStep 762043 = 1143065) B1143065
theorem B7414033 : Blo 674311 7414033 := bstep (se 2 (by rfl) ⟨2780262, by rfl⟩ : syracuseStep 7414033 = 5560525) B5560525
theorem B2564561 : Blo 674311 2564561 := bstep (se 2 (by rfl) ⟨961710, by rfl⟩ : syracuseStep 2564561 = 1923421) B1923421
theorem B3416579 : Blo 674311 3416579 := bstep (se 1 (by rfl) ⟨2562434, by rfl⟩ : syracuseStep 3416579 = 5124869) B5124869
theorem B762511 : Blo 674311 762511 := bstep (se 1 (by rfl) ⟨571883, by rfl⟩ : syracuseStep 762511 = 1143767) B1143767
theorem B1712897 : Blo 674311 1712897 := bstep (se 2 (by rfl) ⟨642336, by rfl⟩ : syracuseStep 1712897 = 1284673) B1284673
theorem B2171681 : Blo 674311 2171681 := bstep (se 2 (by rfl) ⟨814380, by rfl⟩ : syracuseStep 2171681 = 1628761) B1628761
theorem B1221419 : Blo 674311 1221419 := bstep (se 1 (by rfl) ⟨916064, by rfl⟩ : syracuseStep 1221419 = 1832129) B1832129
theorem B2565017 : Blo 674311 2565017 := bstep (se 2 (by rfl) ⟨961881, by rfl⟩ : syracuseStep 2565017 = 1923763) B1923763
theorem B1713271 : Blo 674311 1713271 := bstep (se 1 (by rfl) ⟨1284953, by rfl⟩ : syracuseStep 1713271 = 2569907) B2569907
theorem B763015 : Blo 674311 763015 := bstep (se 1 (by rfl) ⟨572261, by rfl⟩ : syracuseStep 763015 = 1144523) B1144523
theorem B1221779 : Blo 674311 1221779 := bstep (se 1 (by rfl) ⟨916334, by rfl⟩ : syracuseStep 1221779 = 1832669) B1832669
theorem B1287353 : Blo 674311 1287353 := bstep (se 2 (by rfl) ⟨482757, by rfl⟩ : syracuseStep 1287353 = 965515) B965515
theorem B3646721 : Blo 674311 3646721 := bstep (se 2 (by rfl) ⟨1367520, by rfl⟩ : syracuseStep 3646721 = 2735041) B2735041
theorem B2893265 : Blo 674311 2893265 := bstep (se 2 (by rfl) ⟨1084974, by rfl⟩ : syracuseStep 2893265 = 2169949) B2169949
theorem B12985859 : Blo 674311 12985859 := bstep (se 1 (by rfl) ⟨9739394, by rfl⟩ : syracuseStep 12985859 = 19478789) B19478789
theorem B1713707 : Blo 674311 1713707 := bstep (se 1 (by rfl) ⟨1285280, by rfl⟩ : syracuseStep 1713707 = 2570561) B2570561
theorem B29992517 : Blo 674311 29992517 := bstep (se 4 (by rfl) ⟨2811798, by rfl⟩ : syracuseStep 29992517 = 5623597) B5623597
theorem B37561931 : Blo 674311 37561931 := bstep (se 1 (by rfl) ⟨28171448, by rfl⟩ : syracuseStep 37561931 = 56342897) B56342897
theorem B1517327 : Blo 674311 1517327 := bstep (se 1 (by rfl) ⟨1137995, by rfl⟩ : syracuseStep 1517327 = 2275991) B2275991
theorem B1517345 : Blo 674311 1517345 := bstep (se 2 (by rfl) ⟨569004, by rfl⟩ : syracuseStep 1517345 = 1138009) B1138009
theorem B2434951 : Blo 674311 2434951 := bstep (se 1 (by rfl) ⟨1826213, by rfl⟩ : syracuseStep 2434951 = 3652427) B3652427
theorem B960503 : Blo 674311 960503 := bstep (se 1 (by rfl) ⟨720377, by rfl⟩ : syracuseStep 960503 = 1440755) B1440755
theorem B2566187 : Blo 674311 2566187 := bstep (se 1 (by rfl) ⟨1924640, by rfl⟩ : syracuseStep 2566187 = 3849281) B3849281
theorem B3418199 : Blo 674311 3418199 := bstep (se 1 (by rfl) ⟨2563649, by rfl⟩ : syracuseStep 3418199 = 5127299) B5127299
theorem B1517687 : Blo 674311 1517687 := bstep (se 1 (by rfl) ⟨1138265, by rfl⟩ : syracuseStep 1517687 = 2276531) B2276531
theorem B960697 : Blo 674311 960697 := bstep (se 2 (by rfl) ⟨360261, by rfl⟩ : syracuseStep 960697 = 720523) B720523
theorem B1517867 : Blo 674311 1517867 := bstep (se 1 (by rfl) ⟨1138400, by rfl⟩ : syracuseStep 1517867 = 2276801) B2276801
theorem B11118941 : Blo 674311 11118941 := bstep (se 3 (by rfl) ⟨2084801, by rfl⟩ : syracuseStep 11118941 = 4169603) B4169603
theorem B1714547 : Blo 674311 1714547 := bstep (se 1 (by rfl) ⟨1285910, by rfl⟩ : syracuseStep 1714547 = 2571821) B2571821
theorem B5122439 : Blo 674311 5122439 := bstep (se 1 (by rfl) ⟨3841829, by rfl⟩ : syracuseStep 5122439 = 7683659) B7683659
theorem B1714567 : Blo 674311 1714567 := bstep (se 1 (by rfl) ⟨1285925, by rfl⟩ : syracuseStep 1714567 = 2571851) B2571851
theorem B3418685 : Blo 674311 3418685 := bstep (se 3 (by rfl) ⟨641003, by rfl⟩ : syracuseStep 3418685 = 1282007) B1282007
theorem B1518227 : Blo 674311 1518227 := bstep (se 1 (by rfl) ⟨1138670, by rfl⟩ : syracuseStep 1518227 = 2277341) B2277341
theorem B1714841 : Blo 674311 1714841 := bstep (se 2 (by rfl) ⟨643065, by rfl⟩ : syracuseStep 1714841 = 1286131) B1286131
theorem B1518281 : Blo 674311 1518281 := bstep (se 2 (by rfl) ⟨569355, by rfl⟩ : syracuseStep 1518281 = 1138711) B1138711
theorem B1715003 : Blo 674311 1715003 := bstep (se 1 (by rfl) ⟨1286252, by rfl⟩ : syracuseStep 1715003 = 2572505) B2572505
theorem B1715215 : Blo 674311 1715215 := bstep (se 1 (by rfl) ⟨1286411, by rfl⟩ : syracuseStep 1715215 = 2572823) B2572823
theorem B928903 : Blo 674311 928903 := bstep (se 1 (by rfl) ⟨696677, by rfl⟩ : syracuseStep 928903 = 1393355) B1393355
theorem B1715489 : Blo 674311 1715489 := bstep (se 2 (by rfl) ⟨643308, by rfl⟩ : syracuseStep 1715489 = 1286617) B1286617
theorem B1518983 : Blo 674311 1518983 := bstep (se 1 (by rfl) ⟨1139237, by rfl⟩ : syracuseStep 1518983 = 2278475) B2278475
theorem B10431949 : Blo 674311 10431949 := bstep (se 3 (by rfl) ⟨1955990, by rfl⟩ : syracuseStep 10431949 = 3911981) B3911981
theorem B1027591 : Blo 674311 1027591 := bstep (se 1 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 1027591 = 1541387) B1541387
theorem B2436637 : Blo 674311 2436637 := bstep (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) B913739
theorem B1519163 : Blo 674311 1519163 := bstep (se 1 (by rfl) ⟨1139372, by rfl⟩ : syracuseStep 1519163 = 2278745) B2278745
theorem B2436695 : Blo 674311 2436695 := bstep (se 1 (by rfl) ⟨1827521, by rfl⟩ : syracuseStep 2436695 = 3655043) B3655043
theorem B1027703 : Blo 674311 1027703 := bstep (se 1 (by rfl) ⟨770777, by rfl⟩ : syracuseStep 1027703 = 1541555) B1541555
theorem B1519289 : Blo 674311 1519289 := bstep (se 2 (by rfl) ⟨569733, by rfl⟩ : syracuseStep 1519289 = 1139467) B1139467
theorem B10399691 : Blo 674311 10399691 := bstep (se 1 (by rfl) ⟨7799768, by rfl⟩ : syracuseStep 10399691 = 15599537) B15599537
theorem B2568145 : Blo 674311 2568145 := bstep (se 2 (by rfl) ⟨963054, by rfl⟩ : syracuseStep 2568145 = 1926109) B1926109
theorem B1519631 : Blo 674311 1519631 := bstep (se 1 (by rfl) ⟨1139723, by rfl⟩ : syracuseStep 1519631 = 2279447) B2279447
theorem B1519649 : Blo 674311 1519649 := bstep (se 2 (by rfl) ⟨569868, by rfl⟩ : syracuseStep 1519649 = 1139737) B1139737
theorem B2568449 : Blo 674311 2568449 := bstep (se 2 (by rfl) ⟨963168, by rfl⟩ : syracuseStep 2568449 = 1926337) B1926337
theorem B1716491 : Blo 674311 1716491 := bstep (se 1 (by rfl) ⟨1287368, by rfl⟩ : syracuseStep 1716491 = 2574737) B2574737
theorem B3420467 : Blo 674311 3420467 := bstep (se 1 (by rfl) ⟨2565350, by rfl⟩ : syracuseStep 3420467 = 5130701) B5130701
theorem B1519991 : Blo 674311 1519991 := bstep (se 1 (by rfl) ⟨1139993, by rfl⟩ : syracuseStep 1519991 = 2279987) B2279987
theorem B1520171 : Blo 674311 1520171 := bstep (se 1 (by rfl) ⟨1140128, by rfl⟩ : syracuseStep 1520171 = 2280257) B2280257
theorem B3420791 : Blo 674311 3420791 := bstep (se 1 (by rfl) ⟨2565593, by rfl⟩ : syracuseStep 3420791 = 5131187) B5131187
theorem B14594741 : Blo 674311 14594741 := bstep (se 5 (by rfl) ⟨684128, by rfl⟩ : syracuseStep 14594741 = 1368257) B1368257
theorem B2568905 : Blo 674311 2568905 := bstep (se 2 (by rfl) ⟨963339, by rfl⟩ : syracuseStep 2568905 = 1926679) B1926679
theorem B1028809 : Blo 674311 1028809 := bstep (se 2 (by rfl) ⟨385803, by rfl⟩ : syracuseStep 1028809 = 771607) B771607
theorem B8237861 : Blo 674311 8237861 := bstep (se 4 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 8237861 = 1544599) B1544599
theorem B1520531 : Blo 674311 1520531 := bstep (se 1 (by rfl) ⟨1140398, by rfl⟩ : syracuseStep 1520531 = 2280797) B2280797
theorem B1520585 : Blo 674311 1520585 := bstep (se 2 (by rfl) ⟨570219, by rfl⟩ : syracuseStep 1520585 = 1140439) B1140439
theorem B3847115 : Blo 674311 3847115 := bstep (se 1 (by rfl) ⟨2885336, by rfl⟩ : syracuseStep 3847115 = 5770673) B5770673
theorem B3847571 : Blo 674311 3847571 := bstep (se 1 (by rfl) ⟨2885678, by rfl⟩ : syracuseStep 3847571 = 5771357) B5771357
theorem B4339129 : Blo 674311 4339129 := bstep (se 2 (by rfl) ⟨1627173, by rfl⟩ : syracuseStep 4339129 = 3254347) B3254347
theorem B8238635 : Blo 674311 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B4404779 : Blo 674311 4404779 := bstep (se 1 (by rfl) ⟨3303584, by rfl⟩ : syracuseStep 4404779 = 6607169) B6607169
theorem B3421763 : Blo 674311 3421763 := bstep (se 1 (by rfl) ⟨2566322, by rfl⟩ : syracuseStep 3421763 = 5132645) B5132645
theorem B1521287 : Blo 674311 1521287 := bstep (se 1 (by rfl) ⟨1140965, by rfl⟩ : syracuseStep 1521287 = 2281931) B2281931
theorem B1521467 : Blo 674311 1521467 := bstep (se 1 (by rfl) ⟨1141100, by rfl⟩ : syracuseStep 1521467 = 2282201) B2282201
theorem B3422087 : Blo 674311 3422087 := bstep (se 1 (by rfl) ⟨2566565, by rfl⟩ : syracuseStep 3422087 = 5133131) B5133131
theorem B1521593 : Blo 674311 1521593 := bstep (se 2 (by rfl) ⟨570597, by rfl⟩ : syracuseStep 1521593 = 1141195) B1141195
theorem B1849387 : Blo 674311 1849387 := bstep (se 1 (by rfl) ⟨1387040, by rfl⟩ : syracuseStep 1849387 = 2774081) B2774081
theorem B10991861 : Blo 674311 10991861 := bstep (se 5 (by rfl) ⟨515243, by rfl⟩ : syracuseStep 10991861 = 1030487) B1030487
theorem B1521935 : Blo 674311 1521935 := bstep (se 1 (by rfl) ⟨1141451, by rfl⟩ : syracuseStep 1521935 = 2282903) B2282903
theorem B1521953 : Blo 674311 1521953 := bstep (se 2 (by rfl) ⟨570732, by rfl⟩ : syracuseStep 1521953 = 1141465) B1141465
theorem B3651929 : Blo 674311 3651929 := bstep (se 2 (by rfl) ⟨1369473, by rfl⟩ : syracuseStep 3651929 = 2738947) B2738947
theorem B6928861 : Blo 674311 6928861 := bstep (se 3 (by rfl) ⟨1299161, by rfl⟩ : syracuseStep 6928861 = 2598323) B2598323
theorem B2275883 : Blo 674311 2275883 := bstep (se 1 (by rfl) ⟨1706912, by rfl⟩ : syracuseStep 2275883 = 3413825) B3413825
theorem B1522295 : Blo 674311 1522295 := bstep (se 1 (by rfl) ⟨1141721, by rfl⟩ : syracuseStep 1522295 = 2283443) B2283443
theorem B1522475 : Blo 674311 1522475 := bstep (se 1 (by rfl) ⟨1141856, by rfl⟩ : syracuseStep 1522475 = 2283713) B2283713
theorem B1096583 : Blo 674311 1096583 := bstep (se 1 (by rfl) ⟨822437, by rfl⟩ : syracuseStep 1096583 = 1644875) B1644875
theorem B7715735 : Blo 674311 7715735 := bstep (se 1 (by rfl) ⟨5786801, by rfl⟩ : syracuseStep 7715735 = 11573603) B11573603
theorem B1522835 : Blo 674311 1522835 := bstep (se 1 (by rfl) ⟨1142126, by rfl⟩ : syracuseStep 1522835 = 2284253) B2284253
theorem B1522889 : Blo 674311 1522889 := bstep (se 2 (by rfl) ⟨571083, by rfl⟩ : syracuseStep 1522889 = 1142167) B1142167
theorem B6503773 : Blo 674311 6503773 := bstep (se 3 (by rfl) ⟨1219457, by rfl⟩ : syracuseStep 6503773 = 2438915) B2438915
theorem B4341127 : Blo 674311 4341127 := bstep (se 1 (by rfl) ⟨3255845, by rfl⟩ : syracuseStep 4341127 = 6511691) B6511691
theorem B41729539 : Blo 674311 41729539 := bstep (se 1 (by rfl) ⟨31297154, by rfl⟩ : syracuseStep 41729539 = 62594309) B62594309
theorem B1621657 : Blo 674311 1621657 := bstep (se 2 (by rfl) ⟨608121, by rfl⟩ : syracuseStep 1621657 = 1216243) B1216243
theorem B2572033 : Blo 674311 2572033 := bstep (se 2 (by rfl) ⟨964512, by rfl⟩ : syracuseStep 2572033 = 1929025) B1929025
theorem B2277179 : Blo 674311 2277179 := bstep (se 1 (by rfl) ⟨1707884, by rfl⟩ : syracuseStep 2277179 = 3415769) B3415769
theorem B1523591 : Blo 674311 1523591 := bstep (se 1 (by rfl) ⟨1142693, by rfl⟩ : syracuseStep 1523591 = 2285387) B2285387
theorem B1523771 : Blo 674311 1523771 := bstep (se 1 (by rfl) ⟨1142828, by rfl⟩ : syracuseStep 1523771 = 2285657) B2285657
theorem B1523897 : Blo 674311 1523897 := bstep (se 2 (by rfl) ⟨571461, by rfl⟩ : syracuseStep 1523897 = 1142923) B1142923
theorem B2277665 : Blo 674311 2277665 := bstep (se 2 (by rfl) ⟨854124, by rfl⟩ : syracuseStep 2277665 = 1708249) B1708249
theorem B1622387 : Blo 674311 1622387 := bstep (se 1 (by rfl) ⟨1216790, by rfl⟩ : syracuseStep 1622387 = 2433581) B2433581
theorem B1524239 : Blo 674311 1524239 := bstep (se 1 (by rfl) ⟨1143179, by rfl⟩ : syracuseStep 1524239 = 2286359) B2286359
theorem B1524257 : Blo 674311 1524257 := bstep (se 2 (by rfl) ⟨571596, by rfl⟩ : syracuseStep 1524257 = 1143193) B1143193
theorem B2278259 : Blo 674311 2278259 := bstep (se 1 (by rfl) ⟨1708694, by rfl⟩ : syracuseStep 2278259 = 3417389) B3417389
theorem B1524599 : Blo 674311 1524599 := bstep (se 1 (by rfl) ⟨1143449, by rfl⟩ : syracuseStep 1524599 = 2286899) B2286899
theorem B4113287 : Blo 674311 4113287 := bstep (se 1 (by rfl) ⟨3084965, by rfl⟩ : syracuseStep 4113287 = 6169931) B6169931
theorem B4113337 : Blo 674311 4113337 := bstep (se 2 (by rfl) ⟨1542501, by rfl⟩ : syracuseStep 4113337 = 3085003) B3085003
theorem B1524779 : Blo 674311 1524779 := bstep (se 1 (by rfl) ⟨1143584, by rfl⟩ : syracuseStep 1524779 = 2287169) B2287169
theorem B1623311 : Blo 674311 1623311 := bstep (se 1 (by rfl) ⟨1217483, by rfl⟩ : syracuseStep 1623311 = 2434967) B2434967
theorem B3425651 : Blo 674311 3425651 := bstep (se 1 (by rfl) ⟨2569238, by rfl⟩ : syracuseStep 3425651 = 5138477) B5138477
theorem B2082167 : Blo 674311 2082167 := bstep (se 1 (by rfl) ⟨1561625, by rfl⟩ : syracuseStep 2082167 = 3123251) B3123251
theorem B1525139 : Blo 674311 1525139 := bstep (se 1 (by rfl) ⟨1143854, by rfl⟩ : syracuseStep 1525139 = 2287709) B2287709
theorem B2115001 : Blo 674311 2115001 := bstep (se 2 (by rfl) ⟨793125, by rfl⟩ : syracuseStep 2115001 = 1586251) B1586251
theorem B1525193 : Blo 674311 1525193 := bstep (se 2 (by rfl) ⟨571947, by rfl⟩ : syracuseStep 1525193 = 1143895) B1143895
theorem B37045835 : Blo 674311 37045835 := bstep (se 1 (by rfl) ⟨27784376, by rfl⟩ : syracuseStep 37045835 = 55568753) B55568753
theorem B3426137 : Blo 674311 3426137 := bstep (se 2 (by rfl) ⟨1284801, by rfl⟩ : syracuseStep 3426137 = 2569603) B2569603
theorem B4638617 : Blo 674311 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B1525895 : Blo 674311 1525895 := bstep (se 1 (by rfl) ⟨1144421, by rfl⟩ : syracuseStep 1525895 = 2288843) B2288843
theorem B1526075 : Blo 674311 1526075 := bstep (se 1 (by rfl) ⟨1144556, by rfl⟩ : syracuseStep 1526075 = 2289113) B2289113
theorem B1526201 : Blo 674311 1526201 := bstep (se 2 (by rfl) ⟨572325, by rfl⟩ : syracuseStep 1526201 = 1144651) B1144651
theorem B674311 : Blo 674311 674311 := bstep (se 1 (by rfl) ⟨505733, by rfl⟩ : syracuseStep 674311 = 1011467) B1011467
theorem B674319 : Blo 674311 674319 := bstep (se 1 (by rfl) ⟨505739, by rfl⟩ : syracuseStep 674319 = 1011479) B1011479
theorem B674363 : Blo 674311 674363 := bstep (se 1 (by rfl) ⟨505772, by rfl⟩ : syracuseStep 674363 = 1011545) B1011545
theorem B2574935 : Blo 674311 2574935 := bstep (se 1 (by rfl) ⟨1931201, by rfl⟩ : syracuseStep 2574935 = 3862403) B3862403
theorem B674439 : Blo 674311 674439 := bstep (se 1 (by rfl) ⟨505829, by rfl⟩ : syracuseStep 674439 = 1011659) B1011659
theorem B674447 : Blo 674311 674447 := bstep (se 1 (by rfl) ⟨505835, by rfl⟩ : syracuseStep 674447 = 1011671) B1011671
theorem B674491 : Blo 674311 674491 := bstep (se 1 (by rfl) ⟨505868, by rfl⟩ : syracuseStep 674491 = 1011737) B1011737
theorem B674567 : Blo 674311 674567 := bstep (se 1 (by rfl) ⟨505925, by rfl⟩ : syracuseStep 674567 = 1011851) B1011851
theorem B674575 : Blo 674311 674575 := bstep (se 1 (by rfl) ⟨505931, by rfl⟩ : syracuseStep 674575 = 1011863) B1011863
theorem B674619 : Blo 674311 674619 := bstep (se 1 (by rfl) ⟨505964, by rfl⟩ : syracuseStep 674619 = 1011929) B1011929
theorem B674695 : Blo 674311 674695 := bstep (se 1 (by rfl) ⟨506021, by rfl⟩ : syracuseStep 674695 = 1012043) B1012043
theorem B674703 : Blo 674311 674703 := bstep (se 1 (by rfl) ⟨506027, by rfl⟩ : syracuseStep 674703 = 1012055) B1012055
theorem B674747 : Blo 674311 674747 := bstep (se 1 (by rfl) ⟨506060, by rfl⟩ : syracuseStep 674747 = 1012121) B1012121
theorem B674823 : Blo 674311 674823 := bstep (se 1 (by rfl) ⟨506117, by rfl⟩ : syracuseStep 674823 = 1012235) B1012235
theorem B14797835 : Blo 674311 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B674831 : Blo 674311 674831 := bstep (se 1 (by rfl) ⟨506123, by rfl⟩ : syracuseStep 674831 = 1012247) B1012247
theorem B674875 : Blo 674311 674875 := bstep (se 1 (by rfl) ⟨506156, by rfl⟩ : syracuseStep 674875 = 1012313) B1012313
theorem B1625147 : Blo 674311 1625147 := bstep (se 1 (by rfl) ⟨1218860, by rfl⟩ : syracuseStep 1625147 = 2437721) B2437721
theorem B2575421 : Blo 674311 2575421 := bstep (se 3 (by rfl) ⟨482891, by rfl⟩ : syracuseStep 2575421 = 965783) B965783
theorem B674951 : Blo 674311 674951 := bstep (se 1 (by rfl) ⟨506213, by rfl⟩ : syracuseStep 674951 = 1012427) B1012427
theorem B674959 : Blo 674311 674959 := bstep (se 1 (by rfl) ⟨506219, by rfl⟩ : syracuseStep 674959 = 1012439) B1012439
theorem B2051219 : Blo 674311 2051219 := bstep (se 1 (by rfl) ⟨1538414, by rfl⟩ : syracuseStep 2051219 = 3076829) B3076829
theorem B7720109 : Blo 674311 7720109 := bstep (se 3 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 7720109 = 2895041) B2895041
theorem B675003 : Blo 674311 675003 := bstep (se 1 (by rfl) ⟨506252, by rfl⟩ : syracuseStep 675003 = 1012505) B1012505
theorem B675079 : Blo 674311 675079 := bstep (se 1 (by rfl) ⟨506309, by rfl⟩ : syracuseStep 675079 = 1012619) B1012619
theorem B675087 : Blo 674311 675087 := bstep (se 1 (by rfl) ⟨506315, by rfl⟩ : syracuseStep 675087 = 1012631) B1012631
theorem B1101071 : Blo 674311 1101071 := bstep (se 1 (by rfl) ⟨825803, by rfl⟩ : syracuseStep 1101071 = 1651607) B1651607
theorem B675131 : Blo 674311 675131 := bstep (se 1 (by rfl) ⟨506348, by rfl⟩ : syracuseStep 675131 = 1012697) B1012697
theorem B1756475 : Blo 674311 1756475 := bstep (se 1 (by rfl) ⟨1317356, by rfl⟩ : syracuseStep 1756475 = 2634713) B2634713
theorem B675207 : Blo 674311 675207 := bstep (se 1 (by rfl) ⟨506405, by rfl⟩ : syracuseStep 675207 = 1012811) B1012811
theorem B675215 : Blo 674311 675215 := bstep (se 1 (by rfl) ⟨506411, by rfl⟩ : syracuseStep 675215 = 1012823) B1012823
theorem B2280851 : Blo 674311 2280851 := bstep (se 1 (by rfl) ⟨1710638, by rfl⟩ : syracuseStep 2280851 = 3421277) B3421277
theorem B2051513 : Blo 674311 2051513 := bstep (se 2 (by rfl) ⟨769317, by rfl⟩ : syracuseStep 2051513 = 1538635) B1538635
theorem B675259 : Blo 674311 675259 := bstep (se 1 (by rfl) ⟨506444, by rfl⟩ : syracuseStep 675259 = 1012889) B1012889
theorem B675335 : Blo 674311 675335 := bstep (se 1 (by rfl) ⟨506501, by rfl⟩ : syracuseStep 675335 = 1013003) B1013003
theorem B675343 : Blo 674311 675343 := bstep (se 1 (by rfl) ⟨506507, by rfl⟩ : syracuseStep 675343 = 1013015) B1013015
theorem B15650333 : Blo 674311 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B675387 : Blo 674311 675387 := bstep (se 1 (by rfl) ⟨506540, by rfl⟩ : syracuseStep 675387 = 1013081) B1013081
theorem B1920631 : Blo 674311 1920631 := bstep (se 1 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 1920631 = 2880947) B2880947
theorem B675463 : Blo 674311 675463 := bstep (se 1 (by rfl) ⟨506597, by rfl⟩ : syracuseStep 675463 = 1013195) B1013195
theorem B675471 : Blo 674311 675471 := bstep (se 1 (by rfl) ⟨506603, by rfl⟩ : syracuseStep 675471 = 1013207) B1013207
theorem B1920665 : Blo 674311 1920665 := bstep (se 2 (by rfl) ⟨720249, by rfl⟩ : syracuseStep 1920665 = 1440499) B1440499
theorem B675515 : Blo 674311 675515 := bstep (se 1 (by rfl) ⟨506636, by rfl⟩ : syracuseStep 675515 = 1013273) B1013273
theorem B675591 : Blo 674311 675591 := bstep (se 1 (by rfl) ⟨506693, by rfl⟩ : syracuseStep 675591 = 1013387) B1013387
theorem B1920779 : Blo 674311 1920779 := bstep (se 1 (by rfl) ⟨1440584, by rfl⟩ : syracuseStep 1920779 = 2881169) B2881169
theorem B675599 : Blo 674311 675599 := bstep (se 1 (by rfl) ⟨506699, by rfl⟩ : syracuseStep 675599 = 1013399) B1013399
theorem B3460897 : Blo 674311 3460897 := bstep (se 2 (by rfl) ⟨1297836, by rfl⟩ : syracuseStep 3460897 = 2595673) B2595673
theorem B675643 : Blo 674311 675643 := bstep (se 1 (by rfl) ⟨506732, by rfl⟩ : syracuseStep 675643 = 1013465) B1013465
theorem B675719 : Blo 674311 675719 := bstep (se 1 (by rfl) ⟨506789, by rfl⟩ : syracuseStep 675719 = 1013579) B1013579
theorem B675727 : Blo 674311 675727 := bstep (se 1 (by rfl) ⟨506795, by rfl⟩ : syracuseStep 675727 = 1013591) B1013591
theorem B3428243 : Blo 674311 3428243 := bstep (se 1 (by rfl) ⟨2571182, by rfl⟩ : syracuseStep 3428243 = 5142365) B5142365
theorem B675771 : Blo 674311 675771 := bstep (se 1 (by rfl) ⟨506828, by rfl⟩ : syracuseStep 675771 = 1013657) B1013657
theorem B675847 : Blo 674311 675847 := bstep (se 1 (by rfl) ⟨506885, by rfl⟩ : syracuseStep 675847 = 1013771) B1013771
theorem B675855 : Blo 674311 675855 := bstep (se 1 (by rfl) ⟨506891, by rfl⟩ : syracuseStep 675855 = 1013783) B1013783
theorem B675899 : Blo 674311 675899 := bstep (se 1 (by rfl) ⟨506924, by rfl⟩ : syracuseStep 675899 = 1013849) B1013849
theorem B675975 : Blo 674311 675975 := bstep (se 1 (by rfl) ⟨506981, by rfl⟩ : syracuseStep 675975 = 1013963) B1013963
theorem B675983 : Blo 674311 675983 := bstep (se 1 (by rfl) ⟨506987, by rfl⟩ : syracuseStep 675983 = 1013975) B1013975
theorem B676027 : Blo 674311 676027 := bstep (se 1 (by rfl) ⟨507020, by rfl⟩ : syracuseStep 676027 = 1014041) B1014041
theorem B676103 : Blo 674311 676103 := bstep (se 1 (by rfl) ⟨507077, by rfl⟩ : syracuseStep 676103 = 1014155) B1014155
theorem B676111 : Blo 674311 676111 := bstep (se 1 (by rfl) ⟨507083, by rfl⟩ : syracuseStep 676111 = 1014167) B1014167
theorem B676155 : Blo 674311 676155 := bstep (se 1 (by rfl) ⟨507116, by rfl⟩ : syracuseStep 676155 = 1014233) B1014233
theorem B1823111 : Blo 674311 1823111 := bstep (se 1 (by rfl) ⟨1367333, by rfl⟩ : syracuseStep 1823111 = 2734667) B2734667
theorem B676231 : Blo 674311 676231 := bstep (se 1 (by rfl) ⟨507173, by rfl⟩ : syracuseStep 676231 = 1014347) B1014347
theorem B676239 : Blo 674311 676239 := bstep (se 1 (by rfl) ⟨507179, by rfl⟩ : syracuseStep 676239 = 1014359) B1014359
theorem B676283 : Blo 674311 676283 := bstep (se 1 (by rfl) ⟨507212, by rfl⟩ : syracuseStep 676283 = 1014425) B1014425
theorem B676359 : Blo 674311 676359 := bstep (se 1 (by rfl) ⟨507269, by rfl⟩ : syracuseStep 676359 = 1014539) B1014539
theorem B676367 : Blo 674311 676367 := bstep (se 1 (by rfl) ⟨507275, by rfl⟩ : syracuseStep 676367 = 1014551) B1014551
theorem B676411 : Blo 674311 676411 := bstep (se 1 (by rfl) ⟨507308, by rfl⟩ : syracuseStep 676411 = 1014617) B1014617
theorem B3461699 : Blo 674311 3461699 := bstep (se 1 (by rfl) ⟨2596274, by rfl⟩ : syracuseStep 3461699 = 5192549) B5192549
theorem B676487 : Blo 674311 676487 := bstep (se 1 (by rfl) ⟨507365, by rfl⟩ : syracuseStep 676487 = 1014731) B1014731
theorem B676495 : Blo 674311 676495 := bstep (se 1 (by rfl) ⟨507371, by rfl⟩ : syracuseStep 676495 = 1014743) B1014743
theorem B676539 : Blo 674311 676539 := bstep (se 1 (by rfl) ⟨507404, by rfl⟩ : syracuseStep 676539 = 1014809) B1014809
theorem B4117229 : Blo 674311 4117229 := bstep (se 3 (by rfl) ⟨771980, by rfl⟩ : syracuseStep 4117229 = 1543961) B1543961
theorem B676615 : Blo 674311 676615 := bstep (se 1 (by rfl) ⟨507461, by rfl⟩ : syracuseStep 676615 = 1014923) B1014923
theorem B2282255 : Blo 674311 2282255 := bstep (se 1 (by rfl) ⟨1711691, by rfl⟩ : syracuseStep 2282255 = 3423383) B3423383
theorem B676623 : Blo 674311 676623 := bstep (se 1 (by rfl) ⟨507467, by rfl⟩ : syracuseStep 676623 = 1014935) B1014935
theorem B1626923 : Blo 674311 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B676667 : Blo 674311 676667 := bstep (se 1 (by rfl) ⟨507500, by rfl⟩ : syracuseStep 676667 = 1015001) B1015001
theorem B1856315 : Blo 674311 1856315 := bstep (se 1 (by rfl) ⟨1392236, by rfl⟩ : syracuseStep 1856315 = 2784473) B2784473
theorem B1921907 : Blo 674311 1921907 := bstep (se 1 (by rfl) ⟨1441430, by rfl⟩ : syracuseStep 1921907 = 2882861) B2882861
theorem B12342131 : Blo 674311 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B3298163 : Blo 674311 3298163 := bstep (se 1 (by rfl) ⟨2473622, by rfl⟩ : syracuseStep 3298163 = 4947245) B4947245
theorem B676743 : Blo 674311 676743 := bstep (se 1 (by rfl) ⟨507557, by rfl⟩ : syracuseStep 676743 = 1015115) B1015115
theorem B676751 : Blo 674311 676751 := bstep (se 1 (by rfl) ⟨507563, by rfl⟩ : syracuseStep 676751 = 1015127) B1015127
theorem B1561529 : Blo 674311 1561529 := bstep (se 2 (by rfl) ⟨585573, by rfl⟩ : syracuseStep 1561529 = 1171147) B1171147
theorem B676795 : Blo 674311 676795 := bstep (se 1 (by rfl) ⟨507596, by rfl⟩ : syracuseStep 676795 = 1015193) B1015193
theorem B676871 : Blo 674311 676871 := bstep (se 1 (by rfl) ⟨507653, by rfl⟩ : syracuseStep 676871 = 1015307) B1015307
theorem B676879 : Blo 674311 676879 := bstep (se 1 (by rfl) ⟨507659, by rfl⟩ : syracuseStep 676879 = 1015319) B1015319
theorem B2282525 : Blo 674311 2282525 := bstep (se 3 (by rfl) ⟨427973, by rfl⟩ : syracuseStep 2282525 = 855947) B855947
theorem B676923 : Blo 674311 676923 := bstep (se 1 (by rfl) ⟨507692, by rfl⟩ : syracuseStep 676923 = 1015385) B1015385
theorem B676999 : Blo 674311 676999 := bstep (se 1 (by rfl) ⟨507749, by rfl⟩ : syracuseStep 676999 = 1015499) B1015499
theorem B677007 : Blo 674311 677007 := bstep (se 1 (by rfl) ⟨507755, by rfl⟩ : syracuseStep 677007 = 1015511) B1015511
theorem B677051 : Blo 674311 677051 := bstep (se 1 (by rfl) ⟨507788, by rfl⟩ : syracuseStep 677051 = 1015577) B1015577
theorem B1922305 : Blo 674311 1922305 := bstep (se 2 (by rfl) ⟨720864, by rfl⟩ : syracuseStep 1922305 = 1441729) B1441729
theorem B677127 : Blo 674311 677127 := bstep (se 1 (by rfl) ⟨507845, by rfl⟩ : syracuseStep 677127 = 1015691) B1015691
theorem B677135 : Blo 674311 677135 := bstep (se 1 (by rfl) ⟨507851, by rfl⟩ : syracuseStep 677135 = 1015703) B1015703
theorem B1922363 : Blo 674311 1922363 := bstep (se 1 (by rfl) ⟨1441772, by rfl⟩ : syracuseStep 1922363 = 2883545) B2883545
theorem B677179 : Blo 674311 677179 := bstep (se 1 (by rfl) ⟨507884, by rfl⟩ : syracuseStep 677179 = 1015769) B1015769
theorem B677255 : Blo 674311 677255 := bstep (se 1 (by rfl) ⟨507941, by rfl⟩ : syracuseStep 677255 = 1015883) B1015883
theorem B677263 : Blo 674311 677263 := bstep (se 1 (by rfl) ⟨507947, by rfl⟩ : syracuseStep 677263 = 1015895) B1015895
theorem B677307 : Blo 674311 677307 := bstep (se 1 (by rfl) ⟨507980, by rfl⟩ : syracuseStep 677307 = 1015961) B1015961
theorem B677383 : Blo 674311 677383 := bstep (se 1 (by rfl) ⟨508037, by rfl⟩ : syracuseStep 677383 = 1016075) B1016075
theorem B677391 : Blo 674311 677391 := bstep (se 1 (by rfl) ⟨508043, by rfl⟩ : syracuseStep 677391 = 1016087) B1016087
theorem B677435 : Blo 674311 677435 := bstep (se 1 (by rfl) ⟨508076, by rfl⟩ : syracuseStep 677435 = 1016153) B1016153
theorem B677511 : Blo 674311 677511 := bstep (se 1 (by rfl) ⟨508133, by rfl⟩ : syracuseStep 677511 = 1016267) B1016267
theorem B677519 : Blo 674311 677519 := bstep (se 1 (by rfl) ⟨508139, by rfl⟩ : syracuseStep 677519 = 1016279) B1016279
theorem B3856045 : Blo 674311 3856045 := bstep (se 3 (by rfl) ⟨723008, by rfl⟩ : syracuseStep 3856045 = 1446017) B1446017
theorem B7329457 : Blo 674311 7329457 := bstep (se 2 (by rfl) ⟨2748546, by rfl⟩ : syracuseStep 7329457 = 5497093) B5497093
theorem B677563 : Blo 674311 677563 := bstep (se 1 (by rfl) ⟨508172, by rfl⟩ : syracuseStep 677563 = 1016345) B1016345
theorem B17553125 : Blo 674311 17553125 := bstep (se 4 (by rfl) ⟨1645605, by rfl⟩ : syracuseStep 17553125 = 3291211) B3291211
theorem B677639 : Blo 674311 677639 := bstep (se 1 (by rfl) ⟨508229, by rfl⟩ : syracuseStep 677639 = 1016459) B1016459
theorem B677647 : Blo 674311 677647 := bstep (se 1 (by rfl) ⟨508235, by rfl⟩ : syracuseStep 677647 = 1016471) B1016471
theorem B4118323 : Blo 674311 4118323 := bstep (se 1 (by rfl) ⟨3088742, by rfl⟩ : syracuseStep 4118323 = 6177485) B6177485
theorem B677691 : Blo 674311 677691 := bstep (se 1 (by rfl) ⟨508268, by rfl⟩ : syracuseStep 677691 = 1016537) B1016537
theorem B1628039 : Blo 674311 1628039 := bstep (se 1 (by rfl) ⟨1221029, by rfl⟩ : syracuseStep 1628039 = 2442059) B2442059
theorem B677767 : Blo 674311 677767 := bstep (se 1 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 677767 = 1016651) B1016651
theorem B677775 : Blo 674311 677775 := bstep (se 1 (by rfl) ⟨508331, by rfl⟩ : syracuseStep 677775 = 1016663) B1016663
theorem B677819 : Blo 674311 677819 := bstep (se 1 (by rfl) ⟨508364, by rfl⟩ : syracuseStep 677819 = 1016729) B1016729
theorem B677895 : Blo 674311 677895 := bstep (se 1 (by rfl) ⟨508421, by rfl⟩ : syracuseStep 677895 = 1016843) B1016843
theorem B677903 : Blo 674311 677903 := bstep (se 1 (by rfl) ⟨508427, by rfl⟩ : syracuseStep 677903 = 1016855) B1016855
theorem B677947 : Blo 674311 677947 := bstep (se 1 (by rfl) ⟨508460, by rfl⟩ : syracuseStep 677947 = 1016921) B1016921
theorem B678023 : Blo 674311 678023 := bstep (se 1 (by rfl) ⟨508517, by rfl⟩ : syracuseStep 678023 = 1017035) B1017035
theorem B678031 : Blo 674311 678031 := bstep (se 1 (by rfl) ⟨508523, by rfl⟩ : syracuseStep 678031 = 1017047) B1017047
theorem B678075 : Blo 674311 678075 := bstep (se 1 (by rfl) ⟨508556, by rfl⟩ : syracuseStep 678075 = 1017113) B1017113
theorem B678151 : Blo 674311 678151 := bstep (se 1 (by rfl) ⟨508613, by rfl⟩ : syracuseStep 678151 = 1017227) B1017227
theorem B678159 : Blo 674311 678159 := bstep (se 1 (by rfl) ⟨508619, by rfl⟩ : syracuseStep 678159 = 1017239) B1017239
theorem B678203 : Blo 674311 678203 := bstep (se 1 (by rfl) ⟨508652, by rfl⟩ : syracuseStep 678203 = 1017305) B1017305
theorem B1300855 : Blo 674311 1300855 := bstep (se 1 (by rfl) ⟨975641, by rfl⟩ : syracuseStep 1300855 = 1951283) B1951283
theorem B678279 : Blo 674311 678279 := bstep (se 1 (by rfl) ⟨508709, by rfl⟩ : syracuseStep 678279 = 1017419) B1017419
theorem B678287 : Blo 674311 678287 := bstep (se 1 (by rfl) ⟨508715, by rfl⟩ : syracuseStep 678287 = 1017431) B1017431
theorem B2283929 : Blo 674311 2283929 := bstep (se 2 (by rfl) ⟨856473, by rfl⟩ : syracuseStep 2283929 = 1712947) B1712947
theorem B3431321 : Blo 674311 3431321 := bstep (se 2 (by rfl) ⟨1286745, by rfl⟩ : syracuseStep 3431321 = 2573491) B2573491
theorem B2743357 : Blo 674311 2743357 := bstep (se 3 (by rfl) ⟨514379, by rfl⟩ : syracuseStep 2743357 = 1028759) B1028759
theorem B2284631 : Blo 674311 2284631 := bstep (se 1 (by rfl) ⟨1713473, by rfl⟩ : syracuseStep 2284631 = 3426947) B3426947
theorem B5135561 : Blo 674311 5135561 := bstep (se 2 (by rfl) ⟨1925835, by rfl⟩ : syracuseStep 5135561 = 3851671) B3851671
theorem B1137935 : Blo 674311 1137935 := bstep (se 1 (by rfl) ⟨853451, by rfl⟩ : syracuseStep 1137935 = 1706903) B1706903
theorem B1924651 : Blo 674311 1924651 := bstep (se 1 (by rfl) ⟨1443488, by rfl⟩ : syracuseStep 1924651 = 2886977) B2886977
theorem B2285117 : Blo 674311 2285117 := bstep (se 3 (by rfl) ⟨428459, by rfl⟩ : syracuseStep 2285117 = 856919) B856919
theorem B1924879 : Blo 674311 1924879 := bstep (se 1 (by rfl) ⟨1443659, by rfl⟩ : syracuseStep 1924879 = 2887319) B2887319
theorem B1138475 : Blo 674311 1138475 := bstep (se 1 (by rfl) ⟨853856, by rfl⟩ : syracuseStep 1138475 = 1707713) B1707713
theorem B3858461 : Blo 674311 3858461 := bstep (se 3 (by rfl) ⟨723461, by rfl⟩ : syracuseStep 3858461 = 1446923) B1446923
theorem B1925153 : Blo 674311 1925153 := bstep (se 2 (by rfl) ⟨721932, by rfl⟩ : syracuseStep 1925153 = 1443865) B1443865
theorem B1302571 : Blo 674311 1302571 := bstep (se 1 (by rfl) ⟨976928, by rfl⟩ : syracuseStep 1302571 = 1953857) B1953857
theorem B1138873 : Blo 674311 1138873 := bstep (se 2 (by rfl) ⟨427077, by rfl⟩ : syracuseStep 1138873 = 854155) B854155
theorem B3662117 : Blo 674311 3662117 := bstep (se 4 (by rfl) ⟨343323, by rfl⟩ : syracuseStep 3662117 = 686647) B686647
theorem B1925495 : Blo 674311 1925495 := bstep (se 1 (by rfl) ⟨1444121, by rfl⟩ : syracuseStep 1925495 = 2888243) B2888243
theorem B7332227 : Blo 674311 7332227 := bstep (se 1 (by rfl) ⟨5499170, by rfl⟩ : syracuseStep 7332227 = 10998341) B10998341
theorem B1368695 : Blo 674311 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B811819 : Blo 674311 811819 := bstep (se 1 (by rfl) ⟨608864, by rfl⟩ : syracuseStep 811819 = 1217729) B1217729
theorem B1139575 : Blo 674311 1139575 := bstep (se 1 (by rfl) ⟨854681, by rfl⟩ : syracuseStep 1139575 = 1709363) B1709363
theorem B2286521 : Blo 674311 2286521 := bstep (se 2 (by rfl) ⟨857445, by rfl⟩ : syracuseStep 2286521 = 1714891) B1714891
theorem B1926155 : Blo 674311 1926155 := bstep (se 1 (by rfl) ⟨1444616, by rfl⟩ : syracuseStep 1926155 = 2889233) B2889233
theorem B1303595 : Blo 674311 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B1139771 : Blo 674311 1139771 := bstep (se 1 (by rfl) ⟨854828, by rfl⟩ : syracuseStep 1139771 = 1709657) B1709657
theorem B4678829 : Blo 674311 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B3433913 : Blo 674311 3433913 := bstep (se 2 (by rfl) ⟨1287717, by rfl⟩ : syracuseStep 3433913 = 2575435) B2575435
theorem B1140169 : Blo 674311 1140169 := bstep (se 2 (by rfl) ⟨427563, by rfl⟩ : syracuseStep 1140169 = 855127) B855127
theorem B6153731 : Blo 674311 6153731 := bstep (se 1 (by rfl) ⟨4615298, by rfl⟩ : syracuseStep 6153731 = 9230597) B9230597
theorem B2287115 : Blo 674311 2287115 := bstep (se 1 (by rfl) ⟨1715336, by rfl⟩ : syracuseStep 2287115 = 3430673) B3430673
theorem B2287223 : Blo 674311 2287223 := bstep (se 1 (by rfl) ⟨1715417, by rfl⟩ : syracuseStep 2287223 = 3430835) B3430835
theorem B1828669 : Blo 674311 1828669 := bstep (se 3 (by rfl) ⟨342875, by rfl⟩ : syracuseStep 1828669 = 685751) B685751
theorem B1140871 : Blo 674311 1140871 := bstep (se 1 (by rfl) ⟨855653, by rfl⟩ : syracuseStep 1140871 = 1711307) B1711307
theorem B2287817 : Blo 674311 2287817 := bstep (se 2 (by rfl) ⟨857931, by rfl⟩ : syracuseStep 2287817 = 1715863) B1715863
theorem B3860945 : Blo 674311 3860945 := bstep (se 2 (by rfl) ⟨1447854, by rfl⟩ : syracuseStep 3860945 = 2895709) B2895709
theorem B1927739 : Blo 674311 1927739 := bstep (se 1 (by rfl) ⟨1445804, by rfl⟩ : syracuseStep 1927739 = 2891609) B2891609
theorem B1927795 : Blo 674311 1927795 := bstep (se 1 (by rfl) ⟨1445846, by rfl⟩ : syracuseStep 1927795 = 2891693) B2891693
theorem B1370771 : Blo 674311 1370771 := bstep (se 1 (by rfl) ⟨1028078, by rfl⟩ : syracuseStep 1370771 = 2056157) B2056157
theorem B1141519 : Blo 674311 1141519 := bstep (se 1 (by rfl) ⟨856139, by rfl⟩ : syracuseStep 1141519 = 1712279) B1712279
theorem B2288519 : Blo 674311 2288519 := bstep (se 1 (by rfl) ⟨1716389, by rfl⟩ : syracuseStep 2288519 = 3432779) B3432779
theorem B912313 : Blo 674311 912313 := bstep (se 2 (by rfl) ⟨342117, by rfl⟩ : syracuseStep 912313 = 684235) B684235
theorem B1928137 : Blo 674311 1928137 := bstep (se 2 (by rfl) ⟨723051, by rfl⟩ : syracuseStep 1928137 = 1446103) B1446103
theorem B2288897 : Blo 674311 2288897 := bstep (se 2 (by rfl) ⟨858336, by rfl⟩ : syracuseStep 2288897 = 1716673) B1716673
theorem B1142059 : Blo 674311 1142059 := bstep (se 1 (by rfl) ⟨856544, by rfl⟩ : syracuseStep 1142059 = 1713089) B1713089
theorem B1142201 : Blo 674311 1142201 := bstep (se 2 (by rfl) ⟨428325, by rfl⟩ : syracuseStep 1142201 = 856651) B856651
theorem B1011515 : Blo 674311 1011515 := bstep (se 1 (by rfl) ⟨758636, by rfl⟩ : syracuseStep 1011515 = 1517273) B1517273
theorem B1011575 : Blo 674311 1011575 := bstep (se 1 (by rfl) ⟨758681, by rfl⟩ : syracuseStep 1011575 = 1517363) B1517363
theorem B1011599 : Blo 674311 1011599 := bstep (se 1 (by rfl) ⟨758699, by rfl⟩ : syracuseStep 1011599 = 1517399) B1517399
theorem B1011641 : Blo 674311 1011641 := bstep (se 2 (by rfl) ⟨379365, by rfl⟩ : syracuseStep 1011641 = 758731) B758731
theorem B1011719 : Blo 674311 1011719 := bstep (se 1 (by rfl) ⟨758789, by rfl⟩ : syracuseStep 1011719 = 1517579) B1517579
theorem B1011755 : Blo 674311 1011755 := bstep (se 1 (by rfl) ⟨758816, by rfl⟩ : syracuseStep 1011755 = 1517633) B1517633
theorem B1011785 : Blo 674311 1011785 := bstep (se 2 (by rfl) ⟨379419, by rfl⟩ : syracuseStep 1011785 = 758839) B758839
theorem B4616279 : Blo 674311 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B1142903 : Blo 674311 1142903 := bstep (se 1 (by rfl) ⟨857177, by rfl⟩ : syracuseStep 1142903 = 1714355) B1714355
theorem B1011899 : Blo 674311 1011899 := bstep (se 1 (by rfl) ⟨758924, by rfl⟩ : syracuseStep 1011899 = 1517849) B1517849
theorem B1011959 : Blo 674311 1011959 := bstep (se 1 (by rfl) ⟨758969, by rfl⟩ : syracuseStep 1011959 = 1517939) B1517939
theorem B1011983 : Blo 674311 1011983 := bstep (se 1 (by rfl) ⟨758987, by rfl⟩ : syracuseStep 1011983 = 1517975) B1517975
theorem B3862835 : Blo 674311 3862835 := bstep (se 1 (by rfl) ⟨2897126, by rfl⟩ : syracuseStep 3862835 = 5794253) B5794253
theorem B1012025 : Blo 674311 1012025 := bstep (se 2 (by rfl) ⟨379509, by rfl⟩ : syracuseStep 1012025 = 759019) B759019
theorem B1012103 : Blo 674311 1012103 := bstep (se 1 (by rfl) ⟨759077, by rfl⟩ : syracuseStep 1012103 = 1518155) B1518155
theorem B913799 : Blo 674311 913799 := bstep (se 1 (by rfl) ⟨685349, by rfl⟩ : syracuseStep 913799 = 1370699) B1370699
theorem B1012139 : Blo 674311 1012139 := bstep (se 1 (by rfl) ⟨759104, by rfl⟩ : syracuseStep 1012139 = 1518209) B1518209
theorem B1012169 : Blo 674311 1012169 := bstep (se 2 (by rfl) ⟨379563, by rfl⟩ : syracuseStep 1012169 = 759127) B759127
theorem B2748971 : Blo 674311 2748971 := bstep (se 1 (by rfl) ⟨2061728, by rfl⟩ : syracuseStep 2748971 = 4123457) B4123457
theorem B1012283 : Blo 674311 1012283 := bstep (se 1 (by rfl) ⟨759212, by rfl⟩ : syracuseStep 1012283 = 1518425) B1518425
theorem B1143355 : Blo 674311 1143355 := bstep (se 1 (by rfl) ⟨857516, by rfl⟩ : syracuseStep 1143355 = 1715033) B1715033
theorem B1012343 : Blo 674311 1012343 := bstep (se 1 (by rfl) ⟨759257, by rfl⟩ : syracuseStep 1012343 = 1518515) B1518515
theorem B1012367 : Blo 674311 1012367 := bstep (se 1 (by rfl) ⟨759275, by rfl⟩ : syracuseStep 1012367 = 1518551) B1518551
theorem B1012409 : Blo 674311 1012409 := bstep (se 2 (by rfl) ⟨379653, by rfl⟩ : syracuseStep 1012409 = 759307) B759307
theorem B1831609 : Blo 674311 1831609 := bstep (se 2 (by rfl) ⟨686853, by rfl⟩ : syracuseStep 1831609 = 1373707) B1373707
theorem B1143497 : Blo 674311 1143497 := bstep (se 2 (by rfl) ⟨428811, by rfl⟩ : syracuseStep 1143497 = 857623) B857623
theorem B1012487 : Blo 674311 1012487 := bstep (se 1 (by rfl) ⟨759365, by rfl⟩ : syracuseStep 1012487 = 1518731) B1518731
theorem B1012523 : Blo 674311 1012523 := bstep (se 1 (by rfl) ⟨759392, by rfl⟩ : syracuseStep 1012523 = 1518785) B1518785
theorem B1012553 : Blo 674311 1012553 := bstep (se 2 (by rfl) ⟨379707, by rfl⟩ : syracuseStep 1012553 = 759415) B759415
theorem B1012667 : Blo 674311 1012667 := bstep (se 1 (by rfl) ⟨759500, by rfl⟩ : syracuseStep 1012667 = 1519001) B1519001
theorem B2749393 : Blo 674311 2749393 := bstep (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) B2062045
theorem B1012727 : Blo 674311 1012727 := bstep (se 1 (by rfl) ⟨759545, by rfl⟩ : syracuseStep 1012727 = 1519091) B1519091
theorem B1012751 : Blo 674311 1012751 := bstep (se 1 (by rfl) ⟨759563, by rfl⟩ : syracuseStep 1012751 = 1519127) B1519127
theorem B1012793 : Blo 674311 1012793 := bstep (se 2 (by rfl) ⟨379797, by rfl⟩ : syracuseStep 1012793 = 759595) B759595
theorem B914491 : Blo 674311 914491 := bstep (se 1 (by rfl) ⟨685868, by rfl⟩ : syracuseStep 914491 = 1371737) B1371737
theorem B1930301 : Blo 674311 1930301 := bstep (se 3 (by rfl) ⟨361931, by rfl⟩ : syracuseStep 1930301 = 723863) B723863
theorem B1012871 : Blo 674311 1012871 := bstep (se 1 (by rfl) ⟨759653, by rfl⟩ : syracuseStep 1012871 = 1519307) B1519307
theorem B1012907 : Blo 674311 1012907 := bstep (se 1 (by rfl) ⟨759680, by rfl⟩ : syracuseStep 1012907 = 1519361) B1519361
theorem B1012937 : Blo 674311 1012937 := bstep (se 2 (by rfl) ⟨379851, by rfl⟩ : syracuseStep 1012937 = 759703) B759703
theorem B1733899 : Blo 674311 1733899 := bstep (se 1 (by rfl) ⟨1300424, by rfl⟩ : syracuseStep 1733899 = 2600849) B2600849
theorem B5764385 : Blo 674311 5764385 := bstep (se 2 (by rfl) ⟨2161644, by rfl⟩ : syracuseStep 5764385 = 4323289) B4323289
theorem B1930529 : Blo 674311 1930529 := bstep (se 2 (by rfl) ⟨723948, by rfl⟩ : syracuseStep 1930529 = 1447897) B1447897
theorem B1013051 : Blo 674311 1013051 := bstep (se 1 (by rfl) ⟨759788, by rfl⟩ : syracuseStep 1013051 = 1519577) B1519577
theorem B1013111 : Blo 674311 1013111 := bstep (se 1 (by rfl) ⟨759833, by rfl⟩ : syracuseStep 1013111 = 1519667) B1519667
theorem B1144199 : Blo 674311 1144199 := bstep (se 1 (by rfl) ⟨858149, by rfl⟩ : syracuseStep 1144199 = 1716299) B1716299
theorem B1013135 : Blo 674311 1013135 := bstep (se 1 (by rfl) ⟨759851, by rfl⟩ : syracuseStep 1013135 = 1519703) B1519703
theorem B1013177 : Blo 674311 1013177 := bstep (se 2 (by rfl) ⟨379941, by rfl⟩ : syracuseStep 1013177 = 759883) B759883
theorem B1013255 : Blo 674311 1013255 := bstep (se 1 (by rfl) ⟨759941, by rfl⟩ : syracuseStep 1013255 = 1519883) B1519883
theorem B1013291 : Blo 674311 1013291 := bstep (se 1 (by rfl) ⟨759968, by rfl⟩ : syracuseStep 1013291 = 1519937) B1519937
theorem B1013321 : Blo 674311 1013321 := bstep (se 2 (by rfl) ⟨379995, by rfl⟩ : syracuseStep 1013321 = 759991) B759991
theorem B1930871 : Blo 674311 1930871 := bstep (se 1 (by rfl) ⟨1448153, by rfl⟩ : syracuseStep 1930871 = 2896307) B2896307
theorem B1013435 : Blo 674311 1013435 := bstep (se 1 (by rfl) ⟨760076, by rfl⟩ : syracuseStep 1013435 = 1520153) B1520153
theorem B1013495 : Blo 674311 1013495 := bstep (se 1 (by rfl) ⟨760121, by rfl⟩ : syracuseStep 1013495 = 1520243) B1520243
theorem B1013519 : Blo 674311 1013519 := bstep (se 1 (by rfl) ⟨760139, by rfl⟩ : syracuseStep 1013519 = 1520279) B1520279
theorem B1013561 : Blo 674311 1013561 := bstep (se 2 (by rfl) ⟨380085, by rfl⟩ : syracuseStep 1013561 = 760171) B760171
theorem B3700615 : Blo 674311 3700615 := bstep (se 1 (by rfl) ⟨2775461, by rfl⟩ : syracuseStep 3700615 = 5550923) B5550923
theorem B1013639 : Blo 674311 1013639 := bstep (se 1 (by rfl) ⟨760229, by rfl⟩ : syracuseStep 1013639 = 1520459) B1520459
theorem B5339033 : Blo 674311 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B5207971 : Blo 674311 5207971 := bstep (se 1 (by rfl) ⟨3905978, by rfl⟩ : syracuseStep 5207971 = 7811957) B7811957
theorem B1013675 : Blo 674311 1013675 := bstep (se 1 (by rfl) ⟨760256, by rfl⟩ : syracuseStep 1013675 = 1520513) B1520513
theorem B2160569 : Blo 674311 2160569 := bstep (se 2 (by rfl) ⟨810213, by rfl⟩ : syracuseStep 2160569 = 1620427) B1620427
theorem B1013705 : Blo 674311 1013705 := bstep (se 2 (by rfl) ⟨380139, by rfl⟩ : syracuseStep 1013705 = 760279) B760279
theorem B1013819 : Blo 674311 1013819 := bstep (se 1 (by rfl) ⟨760364, by rfl⟩ : syracuseStep 1013819 = 1520729) B1520729
theorem B3242045 : Blo 674311 3242045 := bstep (se 3 (by rfl) ⟨607883, by rfl⟩ : syracuseStep 3242045 = 1215767) B1215767
theorem B1013879 : Blo 674311 1013879 := bstep (se 1 (by rfl) ⟨760409, by rfl⟩ : syracuseStep 1013879 = 1520819) B1520819
theorem B1013903 : Blo 674311 1013903 := bstep (se 1 (by rfl) ⟨760427, by rfl⟩ : syracuseStep 1013903 = 1520855) B1520855
theorem B1013945 : Blo 674311 1013945 := bstep (se 2 (by rfl) ⟨380229, by rfl⟩ : syracuseStep 1013945 = 760459) B760459
theorem B1014023 : Blo 674311 1014023 := bstep (se 1 (by rfl) ⟨760517, by rfl⟩ : syracuseStep 1014023 = 1521035) B1521035
theorem B1014059 : Blo 674311 1014059 := bstep (se 1 (by rfl) ⟨760544, by rfl⟩ : syracuseStep 1014059 = 1521089) B1521089
theorem B1014089 : Blo 674311 1014089 := bstep (se 2 (by rfl) ⟨380283, by rfl⟩ : syracuseStep 1014089 = 760567) B760567
theorem B1014203 : Blo 674311 1014203 := bstep (se 1 (by rfl) ⟨760652, by rfl⟩ : syracuseStep 1014203 = 1521305) B1521305
theorem B1014263 : Blo 674311 1014263 := bstep (se 1 (by rfl) ⟨760697, by rfl⟩ : syracuseStep 1014263 = 1521395) B1521395
theorem B1014287 : Blo 674311 1014287 := bstep (se 1 (by rfl) ⟨760715, by rfl⟩ : syracuseStep 1014287 = 1521431) B1521431
theorem B1014329 : Blo 674311 1014329 := bstep (se 2 (by rfl) ⟨380373, by rfl⟩ : syracuseStep 1014329 = 760747) B760747
theorem B1014407 : Blo 674311 1014407 := bstep (se 1 (by rfl) ⟨760805, by rfl⟩ : syracuseStep 1014407 = 1521611) B1521611
theorem B1014443 : Blo 674311 1014443 := bstep (se 1 (by rfl) ⟨760832, by rfl⟩ : syracuseStep 1014443 = 1521665) B1521665
theorem B1014473 : Blo 674311 1014473 := bstep (se 2 (by rfl) ⟨380427, by rfl⟩ : syracuseStep 1014473 = 760855) B760855
theorem B1014587 : Blo 674311 1014587 := bstep (se 1 (by rfl) ⟨760940, by rfl⟩ : syracuseStep 1014587 = 1521881) B1521881
theorem B1014647 : Blo 674311 1014647 := bstep (se 1 (by rfl) ⟨760985, by rfl⟩ : syracuseStep 1014647 = 1521971) B1521971
theorem B1014671 : Blo 674311 1014671 := bstep (se 1 (by rfl) ⟨761003, by rfl⟩ : syracuseStep 1014671 = 1522007) B1522007
theorem B1014713 : Blo 674311 1014713 := bstep (se 2 (by rfl) ⟨380517, by rfl⟩ : syracuseStep 1014713 = 761035) B761035
theorem B1539017 : Blo 674311 1539017 := bstep (se 2 (by rfl) ⟨577131, by rfl⟩ : syracuseStep 1539017 = 1154263) B1154263
theorem B1014791 : Blo 674311 1014791 := bstep (se 1 (by rfl) ⟨761093, by rfl⟩ : syracuseStep 1014791 = 1522187) B1522187
theorem B2882603 : Blo 674311 2882603 := bstep (se 1 (by rfl) ⟨2161952, by rfl⟩ : syracuseStep 2882603 = 4323905) B4323905
theorem B1014827 : Blo 674311 1014827 := bstep (se 1 (by rfl) ⟨761120, by rfl⟩ : syracuseStep 1014827 = 1522241) B1522241
theorem B1014857 : Blo 674311 1014857 := bstep (se 2 (by rfl) ⟨380571, by rfl⟩ : syracuseStep 1014857 = 761143) B761143
theorem B916615 : Blo 674311 916615 := bstep (se 1 (by rfl) ⟨687461, by rfl⟩ : syracuseStep 916615 = 1374923) B1374923
theorem B1014971 : Blo 674311 1014971 := bstep (se 1 (by rfl) ⟨761228, by rfl⟩ : syracuseStep 1014971 = 1522457) B1522457
theorem B1015031 : Blo 674311 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B1015055 : Blo 674311 1015055 := bstep (se 1 (by rfl) ⟨761291, by rfl⟩ : syracuseStep 1015055 = 1522583) B1522583
theorem B1015097 : Blo 674311 1015097 := bstep (se 2 (by rfl) ⟨380661, by rfl⟩ : syracuseStep 1015097 = 761323) B761323
theorem B1080695 : Blo 674311 1080695 := bstep (se 1 (by rfl) ⟨810521, by rfl⟩ : syracuseStep 1080695 = 1621043) B1621043
theorem B1015175 : Blo 674311 1015175 := bstep (se 1 (by rfl) ⟨761381, by rfl⟩ : syracuseStep 1015175 = 1522763) B1522763
theorem B1015211 : Blo 674311 1015211 := bstep (se 1 (by rfl) ⟨761408, by rfl⟩ : syracuseStep 1015211 = 1522817) B1522817
theorem B1015241 : Blo 674311 1015241 := bstep (se 2 (by rfl) ⟨380715, by rfl⟩ : syracuseStep 1015241 = 761431) B761431
theorem B1539599 : Blo 674311 1539599 := bstep (se 1 (by rfl) ⟨1154699, by rfl⟩ : syracuseStep 1539599 = 2309399) B2309399
theorem B1015355 : Blo 674311 1015355 := bstep (se 1 (by rfl) ⟨761516, by rfl⟩ : syracuseStep 1015355 = 1523033) B1523033
theorem B1015415 : Blo 674311 1015415 := bstep (se 1 (by rfl) ⟨761561, by rfl⟩ : syracuseStep 1015415 = 1523123) B1523123
theorem B1015439 : Blo 674311 1015439 := bstep (se 1 (by rfl) ⟨761579, by rfl⟩ : syracuseStep 1015439 = 1523159) B1523159
theorem B1015481 : Blo 674311 1015481 := bstep (se 2 (by rfl) ⟨380805, by rfl⟩ : syracuseStep 1015481 = 761611) B761611
theorem B1015559 : Blo 674311 1015559 := bstep (se 1 (by rfl) ⟨761669, by rfl⟩ : syracuseStep 1015559 = 1523339) B1523339
theorem B2162465 : Blo 674311 2162465 := bstep (se 2 (by rfl) ⟨810924, by rfl⟩ : syracuseStep 2162465 = 1621849) B1621849
theorem B1015595 : Blo 674311 1015595 := bstep (se 1 (by rfl) ⟨761696, by rfl⟩ : syracuseStep 1015595 = 1523393) B1523393
theorem B13860659 : Blo 674311 13860659 := bstep (se 1 (by rfl) ⟨10395494, by rfl⟩ : syracuseStep 13860659 = 20790989) B20790989
theorem B1015625 : Blo 674311 1015625 := bstep (se 2 (by rfl) ⟨380859, by rfl⟩ : syracuseStep 1015625 = 761719) B761719
theorem B1015739 : Blo 674311 1015739 := bstep (se 1 (by rfl) ⟨761804, by rfl⟩ : syracuseStep 1015739 = 1523609) B1523609
theorem B1015799 : Blo 674311 1015799 := bstep (se 1 (by rfl) ⟨761849, by rfl⟩ : syracuseStep 1015799 = 1523699) B1523699
theorem B1015817 : Blo 674311 1015817 := bstep (se 2 (by rfl) ⟨380931, by rfl⟩ : syracuseStep 1015817 = 761863) B761863
theorem B1015847 : Blo 674311 1015847 := bstep (se 1 (by rfl) ⟨761885, by rfl⟩ : syracuseStep 1015847 = 1523771) B1523771
theorem B1015931 : Blo 674311 1015931 := bstep (se 1 (by rfl) ⟨761948, by rfl⟩ : syracuseStep 1015931 = 1523897) B1523897
theorem B21921941 : Blo 674311 21921941 := bstep (se 6 (by rfl) ⟨513795, by rfl⟩ : syracuseStep 21921941 = 1027591) B1027591
theorem B6947045 : Blo 674311 6947045 := bstep (se 4 (by rfl) ⟨651285, by rfl⟩ : syracuseStep 6947045 = 1302571) B1302571
theorem B1016057 : Blo 674311 1016057 := bstep (se 2 (by rfl) ⟨381021, by rfl⟩ : syracuseStep 1016057 = 762043) B762043
theorem B10944827 : Blo 674311 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B1016159 : Blo 674311 1016159 := bstep (se 1 (by rfl) ⟨762119, by rfl⟩ : syracuseStep 1016159 = 1524239) B1524239
theorem B1016171 : Blo 674311 1016171 := bstep (se 1 (by rfl) ⟨762128, by rfl⟩ : syracuseStep 1016171 = 1524257) B1524257
theorem B1016399 : Blo 674311 1016399 := bstep (se 1 (by rfl) ⟨762299, by rfl⟩ : syracuseStep 1016399 = 1524599) B1524599
theorem B1016519 : Blo 674311 1016519 := bstep (se 1 (by rfl) ⟨762389, by rfl⟩ : syracuseStep 1016519 = 1524779) B1524779
theorem B5768009 : Blo 674311 5768009 := bstep (se 2 (by rfl) ⟨2163003, by rfl⟩ : syracuseStep 5768009 = 4326007) B4326007
theorem B1082207 : Blo 674311 1082207 := bstep (se 1 (by rfl) ⟨811655, by rfl⟩ : syracuseStep 1082207 = 1623311) B1623311
theorem B1016681 : Blo 674311 1016681 := bstep (se 2 (by rfl) ⟨381255, by rfl⟩ : syracuseStep 1016681 = 762511) B762511
theorem B1016759 : Blo 674311 1016759 := bstep (se 1 (by rfl) ⟨762569, by rfl⟩ : syracuseStep 1016759 = 1525139) B1525139
theorem B1016795 : Blo 674311 1016795 := bstep (se 1 (by rfl) ⟨762596, by rfl⟩ : syracuseStep 1016795 = 1525193) B1525193
theorem B4326365 : Blo 674311 4326365 := bstep (se 3 (by rfl) ⟨811193, by rfl⟩ : syracuseStep 4326365 = 1622387) B1622387
theorem B15205427 : Blo 674311 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B1082425 : Blo 674311 1082425 := bstep (se 2 (by rfl) ⟨405909, by rfl⟩ : syracuseStep 1082425 = 811819) B811819
theorem B1443215 : Blo 674311 1443215 := bstep (se 1 (by rfl) ⟨1082411, by rfl⟩ : syracuseStep 1443215 = 2164823) B2164823
theorem B1017263 : Blo 674311 1017263 := bstep (se 1 (by rfl) ⟨762947, by rfl⟩ : syracuseStep 1017263 = 1525895) B1525895
theorem B1017353 : Blo 674311 1017353 := bstep (se 2 (by rfl) ⟨381507, by rfl⟩ : syracuseStep 1017353 = 763015) B763015
theorem B1017383 : Blo 674311 1017383 := bstep (se 1 (by rfl) ⟨763037, by rfl⟩ : syracuseStep 1017383 = 1526075) B1526075
theorem B1017467 : Blo 674311 1017467 := bstep (se 1 (by rfl) ⟨763100, by rfl⟩ : syracuseStep 1017467 = 1526201) B1526201
theorem B9865223 : Blo 674311 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B1083431 : Blo 674311 1083431 := bstep (se 1 (by rfl) ⟨812573, by rfl⟩ : syracuseStep 1083431 = 1625147) B1625147
theorem B5146739 : Blo 674311 5146739 := bstep (se 1 (by rfl) ⟨3860054, by rfl⟩ : syracuseStep 5146739 = 7720109) B7720109
theorem B4950173 : Blo 674311 4950173 := bstep (se 3 (by rfl) ⟨928157, by rfl⟩ : syracuseStep 4950173 = 1856315) B1856315
theorem B1280443 : Blo 674311 1280443 := bstep (se 1 (by rfl) ⟨960332, by rfl⟩ : syracuseStep 1280443 = 1920665) B1920665
theorem B4164077 : Blo 674311 4164077 := bstep (se 3 (by rfl) ⟨780764, by rfl⟩ : syracuseStep 4164077 = 1561529) B1561529
theorem B1280519 : Blo 674311 1280519 := bstep (se 1 (by rfl) ⟨960389, by rfl⟩ : syracuseStep 1280519 = 1920779) B1920779
theorem B854651 : Blo 674311 854651 := bstep (se 1 (by rfl) ⟨640988, by rfl⟩ : syracuseStep 854651 = 1281977) B1281977
theorem B1280929 : Blo 674311 1280929 := bstep (se 2 (by rfl) ⟨480348, by rfl⟩ : syracuseStep 1280929 = 960697) B960697
theorem B1215407 : Blo 674311 1215407 := bstep (se 1 (by rfl) ⟨911555, by rfl⟩ : syracuseStep 1215407 = 1823111) B1823111
theorem B1707065 : Blo 674311 1707065 := bstep (se 2 (by rfl) ⟨640149, by rfl⟩ : syracuseStep 1707065 = 1280299) B1280299
theorem B1281271 : Blo 674311 1281271 := bstep (se 1 (by rfl) ⟨960953, by rfl⟩ : syracuseStep 1281271 = 1921907) B1921907
theorem B8228087 : Blo 674311 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B1281575 : Blo 674311 1281575 := bstep (se 1 (by rfl) ⟨961181, by rfl⟩ : syracuseStep 1281575 = 1922363) B1922363
theorem B11702083 : Blo 674311 11702083 := bstep (se 1 (by rfl) ⟨8776562, by rfl⟩ : syracuseStep 11702083 = 17553125) B17553125
theorem B1216417 : Blo 674311 1216417 := bstep (se 2 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 1216417 = 912313) B912313
theorem B11538611 : Blo 674311 11538611 := bstep (se 1 (by rfl) ⟨8653958, by rfl⟩ : syracuseStep 11538611 = 17307917) B17307917
theorem B2167283 : Blo 674311 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B1708553 : Blo 674311 1708553 := bstep (se 2 (by rfl) ⟨640707, by rfl⟩ : syracuseStep 1708553 = 1281415) B1281415
theorem B1446599 : Blo 674311 1446599 := bstep (se 1 (by rfl) ⟨1084949, by rfl⟩ : syracuseStep 1446599 = 2169899) B2169899
theorem B3248849 : Blo 674311 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B2560841 : Blo 674311 2560841 := bstep (se 2 (by rfl) ⟨960315, by rfl⟩ : syracuseStep 2560841 = 1920631) B1920631
theorem B758623 : Blo 674311 758623 := bstep (se 1 (by rfl) ⟨568967, by rfl⟩ : syracuseStep 758623 = 1137935) B1137935
theorem B2167823 : Blo 674311 2167823 := bstep (se 1 (by rfl) ⟨1625867, by rfl⟩ : syracuseStep 2167823 = 3251735) B3251735
theorem B758983 : Blo 674311 758983 := bstep (se 1 (by rfl) ⟨569237, by rfl⟩ : syracuseStep 758983 = 1138475) B1138475
theorem B2561341 : Blo 674311 2561341 := bstep (se 3 (by rfl) ⟨480251, by rfl⟩ : syracuseStep 2561341 = 960503) B960503
theorem B1283435 : Blo 674311 1283435 := bstep (se 1 (by rfl) ⟨962576, by rfl⟩ : syracuseStep 1283435 = 1925153) B1925153
theorem B16422389 : Blo 674311 16422389 := bstep (se 5 (by rfl) ⟨769799, by rfl⟩ : syracuseStep 16422389 = 1539599) B1539599
theorem B1283663 : Blo 674311 1283663 := bstep (se 1 (by rfl) ⟨962747, by rfl⟩ : syracuseStep 1283663 = 1925495) B1925495
theorem B4888151 : Blo 674311 4888151 := bstep (se 1 (by rfl) ⟨3666113, by rfl⟩ : syracuseStep 4888151 = 7332227) B7332227
theorem B1709707 : Blo 674311 1709707 := bstep (se 1 (by rfl) ⟨1282280, by rfl⟩ : syracuseStep 1709707 = 2564561) B2564561
theorem B1447787 : Blo 674311 1447787 := bstep (se 1 (by rfl) ⟨1085840, by rfl⟩ : syracuseStep 1447787 = 2171681) B2171681
theorem B1710011 : Blo 674311 1710011 := bstep (se 1 (by rfl) ⟨1282508, by rfl⟩ : syracuseStep 1710011 = 2565017) B2565017
theorem B1284103 : Blo 674311 1284103 := bstep (se 1 (by rfl) ⟨963077, by rfl⟩ : syracuseStep 1284103 = 1926155) B1926155
theorem B4888613 : Blo 674311 4888613 := bstep (se 4 (by rfl) ⟨458307, by rfl⟩ : syracuseStep 4888613 = 916615) B916615
theorem B759847 : Blo 674311 759847 := bstep (se 1 (by rfl) ⟨569885, by rfl⟩ : syracuseStep 759847 = 1139771) B1139771
theorem B3119219 : Blo 674311 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B2431147 : Blo 674311 2431147 := bstep (se 1 (by rfl) ⟨1823360, by rfl⟩ : syracuseStep 2431147 = 3646721) B3646721
theorem B4102487 : Blo 674311 4102487 := bstep (se 1 (by rfl) ⟨3076865, by rfl⟩ : syracuseStep 4102487 = 6153731) B6153731
theorem B8657239 : Blo 674311 8657239 := bstep (se 1 (by rfl) ⟨6492929, by rfl⟩ : syracuseStep 8657239 = 12985859) B12985859
theorem B19995011 : Blo 674311 19995011 := bstep (se 1 (by rfl) ⟨14996258, by rfl⟩ : syracuseStep 19995011 = 29992517) B29992517
theorem B25041287 : Blo 674311 25041287 := bstep (se 1 (by rfl) ⟨18780965, by rfl⟩ : syracuseStep 25041287 = 37561931) B37561931
theorem B1710791 : Blo 674311 1710791 := bstep (se 1 (by rfl) ⟨1283093, by rfl⟩ : syracuseStep 1710791 = 2566187) B2566187
theorem B1710841 : Blo 674311 1710841 := bstep (se 2 (by rfl) ⟨641565, by rfl⟩ : syracuseStep 1710841 = 1283131) B1283131
theorem B1219321 : Blo 674311 1219321 := bstep (se 2 (by rfl) ⟨457245, by rfl⟩ : syracuseStep 1219321 = 914491) B914491
theorem B7412627 : Blo 674311 7412627 := bstep (se 1 (by rfl) ⟨5559470, by rfl⟩ : syracuseStep 7412627 = 11118941) B11118941
theorem B3414959 : Blo 674311 3414959 := bstep (se 1 (by rfl) ⟨2561219, by rfl⟩ : syracuseStep 3414959 = 5122439) B5122439
theorem B2563073 : Blo 674311 2563073 := bstep (se 2 (by rfl) ⟨961152, by rfl⟩ : syracuseStep 2563073 = 1922305) B1922305
theorem B1285159 : Blo 674311 1285159 := bstep (se 1 (by rfl) ⟨963869, by rfl⟩ : syracuseStep 1285159 = 1927739) B1927739
theorem B1711489 : Blo 674311 1711489 := bstep (se 2 (by rfl) ⟨641808, by rfl⟩ : syracuseStep 1711489 = 1283617) B1283617
theorem B761467 : Blo 674311 761467 := bstep (se 1 (by rfl) ⟨571100, by rfl⟩ : syracuseStep 761467 = 1142201) B1142201
theorem B11280005 : Blo 674311 11280005 := bstep (se 4 (by rfl) ⟨1057500, by rfl⟩ : syracuseStep 11280005 = 2115001) B2115001
theorem B2924221 : Blo 674311 2924221 := bstep (se 3 (by rfl) ⟨548291, by rfl⟩ : syracuseStep 2924221 = 1096583) B1096583
theorem B2465849 : Blo 674311 2465849 := bstep (se 2 (by rfl) ⟨924693, by rfl⟩ : syracuseStep 2465849 = 1849387) B1849387
theorem B761935 : Blo 674311 761935 := bstep (se 1 (by rfl) ⟨571451, by rfl⟩ : syracuseStep 761935 = 1142903) B1142903
theorem B2891933 : Blo 674311 2891933 := bstep (se 3 (by rfl) ⟨542237, by rfl⟩ : syracuseStep 2891933 = 1084475) B1084475
theorem B1712299 : Blo 674311 1712299 := bstep (se 1 (by rfl) ⟨1284224, by rfl⟩ : syracuseStep 1712299 = 2568449) B2568449
theorem B1712603 : Blo 674311 1712603 := bstep (se 1 (by rfl) ⟨1284452, by rfl⟩ : syracuseStep 1712603 = 2568905) B2568905
theorem B762331 : Blo 674311 762331 := bstep (se 1 (by rfl) ⟨571748, by rfl⟩ : syracuseStep 762331 = 1143497) B1143497
theorem B2564743 : Blo 674311 2564743 := bstep (se 1 (by rfl) ⟨1923557, by rfl⟩ : syracuseStep 2564743 = 3847115) B3847115
theorem B1286867 : Blo 674311 1286867 := bstep (se 1 (by rfl) ⟨965150, by rfl⟩ : syracuseStep 1286867 = 1930301) B1930301
theorem B2892617 : Blo 674311 2892617 := bstep (se 2 (by rfl) ⟨1084731, by rfl⟩ : syracuseStep 2892617 = 2169463) B2169463
theorem B3842923 : Blo 674311 3842923 := bstep (se 1 (by rfl) ⟨2882192, by rfl⟩ : syracuseStep 3842923 = 5764385) B5764385
theorem B1287019 : Blo 674311 1287019 := bstep (se 1 (by rfl) ⟨965264, by rfl⟩ : syracuseStep 1287019 = 1930529) B1930529
theorem B762799 : Blo 674311 762799 := bstep (se 1 (by rfl) ⟨572099, by rfl⟩ : syracuseStep 762799 = 1144199) B1144199
theorem B2565047 : Blo 674311 2565047 := bstep (se 1 (by rfl) ⟨1923785, by rfl⟩ : syracuseStep 2565047 = 3847571) B3847571
theorem B1287247 : Blo 674311 1287247 := bstep (se 1 (by rfl) ⟨965435, by rfl⟩ : syracuseStep 1287247 = 1930871) B1930871
theorem B2434619 : Blo 674311 2434619 := bstep (se 1 (by rfl) ⟨1825964, by rfl⟩ : syracuseStep 2434619 = 3651929) B3651929
theorem B1517255 : Blo 674311 1517255 := bstep (se 1 (by rfl) ⟨1137941, by rfl⟩ : syracuseStep 1517255 = 2275883) B2275883
theorem B5121953 : Blo 674311 5121953 := bstep (se 2 (by rfl) ⟨1920732, by rfl⟩ : syracuseStep 5121953 = 3841465) B3841465
theorem B1714081 : Blo 674311 1714081 := bstep (se 2 (by rfl) ⟨642780, by rfl⟩ : syracuseStep 1714081 = 1285561) B1285561
theorem B1026011 : Blo 674311 1026011 := bstep (se 1 (by rfl) ⟨769508, by rfl⟩ : syracuseStep 1026011 = 1539017) B1539017
theorem B12986405 : Blo 674311 12986405 := bstep (se 4 (by rfl) ⟨1217475, by rfl⟩ : syracuseStep 12986405 = 2434951) B2434951
theorem B2566201 : Blo 674311 2566201 := bstep (se 2 (by rfl) ⟨962325, by rfl⟩ : syracuseStep 2566201 = 1924651) B1924651
theorem B2566505 : Blo 674311 2566505 := bstep (se 2 (by rfl) ⟨962439, by rfl⟩ : syracuseStep 2566505 = 1924879) B1924879
theorem B4336001 : Blo 674311 4336001 := bstep (se 2 (by rfl) ⟨1626000, by rfl⟩ : syracuseStep 4336001 = 3252001) B3252001
theorem B1518119 : Blo 674311 1518119 := bstep (se 1 (by rfl) ⟨1138589, by rfl⟩ : syracuseStep 1518119 = 2277179) B2277179
theorem B1518443 : Blo 674311 1518443 := bstep (se 1 (by rfl) ⟨1138832, by rfl⟩ : syracuseStep 1518443 = 2277665) B2277665
theorem B1518497 : Blo 674311 1518497 := bstep (se 2 (by rfl) ⟨569436, by rfl⟩ : syracuseStep 1518497 = 1138873) B1138873
theorem B1518839 : Blo 674311 1518839 := bstep (se 1 (by rfl) ⟨1139129, by rfl⟩ : syracuseStep 1518839 = 2278259) B2278259
theorem B2600507 : Blo 674311 2600507 := bstep (se 1 (by rfl) ⟨1950380, by rfl⟩ : syracuseStep 2600507 = 3900761) B3900761
theorem B1388111 : Blo 674311 1388111 := bstep (se 1 (by rfl) ⟨1041083, by rfl⟩ : syracuseStep 1388111 = 2082167) B2082167
theorem B2436797 : Blo 674311 2436797 := bstep (se 3 (by rfl) ⟨456899, by rfl⟩ : syracuseStep 2436797 = 913799) B913799
theorem B1519433 : Blo 674311 1519433 := bstep (se 2 (by rfl) ⟨569787, by rfl⟩ : syracuseStep 1519433 = 1139575) B1139575
theorem B2895725 : Blo 674311 2895725 := bstep (se 3 (by rfl) ⟨542948, by rfl⟩ : syracuseStep 2895725 = 1085897) B1085897
theorem B5484449 : Blo 674311 5484449 := bstep (se 2 (by rfl) ⟨2056668, by rfl⟩ : syracuseStep 5484449 = 4113337) B4113337
theorem B3092411 : Blo 674311 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B962599 : Blo 674311 962599 := bstep (se 1 (by rfl) ⟨721949, by rfl⟩ : syracuseStep 962599 = 1443899) B1443899
theorem B3649853 : Blo 674311 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B1716623 : Blo 674311 1716623 := bstep (se 1 (by rfl) ⟨1287467, by rfl⟩ : syracuseStep 1716623 = 2574935) B2574935
theorem B27832841 : Blo 674311 27832841 := bstep (se 2 (by rfl) ⟨10437315, by rfl⟩ : syracuseStep 27832841 = 20874631) B20874631
theorem B1520225 : Blo 674311 1520225 := bstep (se 2 (by rfl) ⟨570084, by rfl⟩ : syracuseStep 1520225 = 1140169) B1140169
theorem B17347283 : Blo 674311 17347283 := bstep (se 1 (by rfl) ⟨13010462, by rfl⟩ : syracuseStep 17347283 = 26020925) B26020925
theorem B1716947 : Blo 674311 1716947 := bstep (se 1 (by rfl) ⟨1287710, by rfl⟩ : syracuseStep 1716947 = 2575421) B2575421
theorem B4338461 : Blo 674311 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B3257117 : Blo 674311 3257117 := bstep (se 3 (by rfl) ⟨610709, by rfl⟩ : syracuseStep 3257117 = 1221419) B1221419
theorem B1520567 : Blo 674311 1520567 := bstep (se 1 (by rfl) ⟨1140425, by rfl⟩ : syracuseStep 1520567 = 2280851) B2280851
theorem B8795101 : Blo 674311 8795101 := bstep (se 3 (by rfl) ⟨1649081, by rfl⟩ : syracuseStep 8795101 = 3298163) B3298163
theorem B10433555 : Blo 674311 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B2602063 : Blo 674311 2602063 := bstep (se 1 (by rfl) ⟨1951547, by rfl⟩ : syracuseStep 2602063 = 3903095) B3903095
theorem B2438225 : Blo 674311 2438225 := bstep (se 2 (by rfl) ⟨914334, by rfl⟩ : syracuseStep 2438225 = 1828669) B1828669
theorem B1521161 : Blo 674311 1521161 := bstep (se 2 (by rfl) ⟨570435, by rfl⟩ : syracuseStep 1521161 = 1140871) B1140871
theorem B2307799 : Blo 674311 2307799 := bstep (se 1 (by rfl) ⟨1730849, by rfl⟩ : syracuseStep 2307799 = 3461699) B3461699
theorem B2471639 : Blo 674311 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B1521503 : Blo 674311 1521503 := bstep (se 1 (by rfl) ⟨1141127, by rfl⟩ : syracuseStep 1521503 = 2282255) B2282255
theorem B1521683 : Blo 674311 1521683 := bstep (se 1 (by rfl) ⟨1141262, by rfl⟩ : syracuseStep 1521683 = 2282525) B2282525
theorem B2570393 : Blo 674311 2570393 := bstep (se 2 (by rfl) ⟨963897, by rfl⟩ : syracuseStep 2570393 = 1927795) B1927795
theorem B1522025 : Blo 674311 1522025 := bstep (se 2 (by rfl) ⟨570759, by rfl⟩ : syracuseStep 1522025 = 1141519) B1141519
theorem B2275937 : Blo 674311 2275937 := bstep (se 2 (by rfl) ⟨853476, by rfl⟩ : syracuseStep 2275937 = 1706953) B1706953
theorem B2570849 : Blo 674311 2570849 := bstep (se 2 (by rfl) ⟨964068, by rfl⟩ : syracuseStep 2570849 = 1928137) B1928137
theorem B1096553 : Blo 674311 1096553 := bstep (se 2 (by rfl) ⟨411207, by rfl⟩ : syracuseStep 1096553 = 822415) B822415
theorem B1522619 : Blo 674311 1522619 := bstep (se 1 (by rfl) ⟨1141964, by rfl⟩ : syracuseStep 1522619 = 2283929) B2283929
theorem B1522745 : Blo 674311 1522745 := bstep (se 2 (by rfl) ⟨571029, by rfl⟩ : syracuseStep 1522745 = 1142059) B1142059
theorem B13909265 : Blo 674311 13909265 := bstep (se 2 (by rfl) ⟨5215974, by rfl⟩ : syracuseStep 13909265 = 10431949) B10431949
theorem B1523087 : Blo 674311 1523087 := bstep (se 1 (by rfl) ⟨1142315, by rfl⟩ : syracuseStep 1523087 = 2284631) B2284631
theorem B3423707 : Blo 674311 3423707 := bstep (se 1 (by rfl) ⟨2567780, by rfl⟩ : syracuseStep 3423707 = 5135561) B5135561
theorem B4341437 : Blo 674311 4341437 := bstep (se 3 (by rfl) ⟨814019, by rfl⟩ : syracuseStep 4341437 = 1628039) B1628039
theorem B1523411 : Blo 674311 1523411 := bstep (se 1 (by rfl) ⟨1142558, by rfl⟩ : syracuseStep 1523411 = 2285117) B2285117
theorem B21938039 : Blo 674311 21938039 := bstep (se 1 (by rfl) ⟨16453529, by rfl⟩ : syracuseStep 21938039 = 32907059) B32907059
theorem B3424193 : Blo 674311 3424193 := bstep (se 2 (by rfl) ⟨1284072, by rfl⟩ : syracuseStep 3424193 = 2568145) B2568145
theorem B2277395 : Blo 674311 2277395 := bstep (se 1 (by rfl) ⟨1708046, by rfl⟩ : syracuseStep 2277395 = 3416093) B3416093
theorem B2572307 : Blo 674311 2572307 := bstep (se 1 (by rfl) ⟨1929230, by rfl⟩ : syracuseStep 2572307 = 3858461) B3858461
theorem B2441411 : Blo 674311 2441411 := bstep (se 1 (by rfl) ⟨1831058, by rfl⟩ : syracuseStep 2441411 = 3662117) B3662117
theorem B2277719 : Blo 674311 2277719 := bstep (se 1 (by rfl) ⟨1708289, by rfl⟩ : syracuseStep 2277719 = 3416579) B3416579
theorem B1524347 : Blo 674311 1524347 := bstep (se 1 (by rfl) ⟨1143260, by rfl⟩ : syracuseStep 1524347 = 2286521) B2286521
theorem B869063 : Blo 674311 869063 := bstep (se 1 (by rfl) ⟨651797, by rfl⟩ : syracuseStep 869063 = 1303595) B1303595
theorem B1524473 : Blo 674311 1524473 := bstep (se 2 (by rfl) ⟨571677, by rfl⟩ : syracuseStep 1524473 = 1143355) B1143355
theorem B2442145 : Blo 674311 2442145 := bstep (se 2 (by rfl) ⟨915804, by rfl⟩ : syracuseStep 2442145 = 1831609) B1831609
theorem B1524743 : Blo 674311 1524743 := bstep (se 1 (by rfl) ⟨1143557, by rfl⟩ : syracuseStep 1524743 = 2287115) B2287115
theorem B1524815 : Blo 674311 1524815 := bstep (se 1 (by rfl) ⟨1143611, by rfl⟩ : syracuseStep 1524815 = 2287223) B2287223
theorem B2278799 : Blo 674311 2278799 := bstep (se 1 (by rfl) ⟨1709099, by rfl⟩ : syracuseStep 2278799 = 3418199) B3418199
theorem B1525211 : Blo 674311 1525211 := bstep (se 1 (by rfl) ⟨1143908, by rfl⟩ : syracuseStep 1525211 = 2287817) B2287817
theorem B2573963 : Blo 674311 2573963 := bstep (se 1 (by rfl) ⟨1930472, by rfl⟩ : syracuseStep 2573963 = 3860945) B3860945
theorem B2311865 : Blo 674311 2311865 := bstep (se 2 (by rfl) ⟨866949, by rfl⟩ : syracuseStep 2311865 = 1733899) B1733899
theorem B2279123 : Blo 674311 2279123 := bstep (se 1 (by rfl) ⟨1709342, by rfl⟩ : syracuseStep 2279123 = 3418685) B3418685
theorem B5785505 : Blo 674311 5785505 := bstep (se 2 (by rfl) ⟨2169564, by rfl⟩ : syracuseStep 5785505 = 4339129) B4339129
theorem B1525679 : Blo 674311 1525679 := bstep (se 1 (by rfl) ⟨1144259, by rfl⟩ : syracuseStep 1525679 = 2288519) B2288519
theorem B3426461 : Blo 674311 3426461 := bstep (se 3 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 3426461 = 1284923) B1284923
theorem B1525931 : Blo 674311 1525931 := bstep (se 1 (by rfl) ⟨1144448, by rfl⟩ : syracuseStep 1525931 = 2288897) B2288897
theorem B1624463 : Blo 674311 1624463 := bstep (se 1 (by rfl) ⟨1218347, by rfl⟩ : syracuseStep 1624463 = 2436695) B2436695
theorem B5491097 : Blo 674311 5491097 := bstep (se 2 (by rfl) ⟨2059161, by rfl⟩ : syracuseStep 5491097 = 4118323) B4118323
theorem B4934153 : Blo 674311 4934153 := bstep (se 2 (by rfl) ⟨1850307, by rfl⟩ : syracuseStep 4934153 = 3700615) B3700615
theorem B674343 : Blo 674311 674343 := bstep (se 1 (by rfl) ⟨505757, by rfl⟩ : syracuseStep 674343 = 1011515) B1011515
theorem B674383 : Blo 674311 674383 := bstep (se 1 (by rfl) ⟨505787, by rfl⟩ : syracuseStep 674383 = 1011575) B1011575
theorem B674399 : Blo 674311 674399 := bstep (se 1 (by rfl) ⟨505799, by rfl⟩ : syracuseStep 674399 = 1011599) B1011599
theorem B674427 : Blo 674311 674427 := bstep (se 1 (by rfl) ⟨505820, by rfl⟩ : syracuseStep 674427 = 1011641) B1011641
theorem B6933127 : Blo 674311 6933127 := bstep (se 1 (by rfl) ⟨5199845, by rfl⟩ : syracuseStep 6933127 = 10399691) B10399691
theorem B674479 : Blo 674311 674479 := bstep (se 1 (by rfl) ⟨505859, by rfl⟩ : syracuseStep 674479 = 1011719) B1011719
theorem B674503 : Blo 674311 674503 := bstep (se 1 (by rfl) ⟨505877, by rfl⟩ : syracuseStep 674503 = 1011755) B1011755
theorem B674523 : Blo 674311 674523 := bstep (se 1 (by rfl) ⟨505892, by rfl⟩ : syracuseStep 674523 = 1011785) B1011785
theorem B674599 : Blo 674311 674599 := bstep (se 1 (by rfl) ⟨505949, by rfl⟩ : syracuseStep 674599 = 1011899) B1011899
theorem B3853129 : Blo 674311 3853129 := bstep (se 2 (by rfl) ⟨1444923, by rfl⟩ : syracuseStep 3853129 = 2889847) B2889847
theorem B674639 : Blo 674311 674639 := bstep (se 1 (by rfl) ⟨505979, by rfl⟩ : syracuseStep 674639 = 1011959) B1011959
theorem B674655 : Blo 674311 674655 := bstep (se 1 (by rfl) ⟨505991, by rfl⟩ : syracuseStep 674655 = 1011983) B1011983
theorem B2280311 : Blo 674311 2280311 := bstep (se 1 (by rfl) ⟨1710233, by rfl⟩ : syracuseStep 2280311 = 3420467) B3420467
theorem B2575223 : Blo 674311 2575223 := bstep (se 1 (by rfl) ⟨1931417, by rfl⟩ : syracuseStep 2575223 = 3862835) B3862835
theorem B674683 : Blo 674311 674683 := bstep (se 1 (by rfl) ⟨506012, by rfl⟩ : syracuseStep 674683 = 1012025) B1012025
theorem B674735 : Blo 674311 674735 := bstep (se 1 (by rfl) ⟨506051, by rfl⟩ : syracuseStep 674735 = 1012103) B1012103
theorem B674759 : Blo 674311 674759 := bstep (se 1 (by rfl) ⟨506069, by rfl⟩ : syracuseStep 674759 = 1012139) B1012139
theorem B674779 : Blo 674311 674779 := bstep (se 1 (by rfl) ⟨506084, by rfl⟩ : syracuseStep 674779 = 1012169) B1012169
theorem B674855 : Blo 674311 674855 := bstep (se 1 (by rfl) ⟨506141, by rfl⟩ : syracuseStep 674855 = 1012283) B1012283
theorem B674895 : Blo 674311 674895 := bstep (se 1 (by rfl) ⟨506171, by rfl⟩ : syracuseStep 674895 = 1012343) B1012343
theorem B2280527 : Blo 674311 2280527 := bstep (se 1 (by rfl) ⟨1710395, by rfl⟩ : syracuseStep 2280527 = 3420791) B3420791
theorem B674911 : Blo 674311 674911 := bstep (se 1 (by rfl) ⟨506183, by rfl⟩ : syracuseStep 674911 = 1012367) B1012367
theorem B674939 : Blo 674311 674939 := bstep (se 1 (by rfl) ⟨506204, by rfl⟩ : syracuseStep 674939 = 1012409) B1012409
theorem B674991 : Blo 674311 674991 := bstep (se 1 (by rfl) ⟨506243, by rfl⟩ : syracuseStep 674991 = 1012487) B1012487
theorem B5491907 : Blo 674311 5491907 := bstep (se 1 (by rfl) ⟨4118930, by rfl⟩ : syracuseStep 5491907 = 8237861) B8237861
theorem B675015 : Blo 674311 675015 := bstep (se 1 (by rfl) ⟨506261, by rfl⟩ : syracuseStep 675015 = 1012523) B1012523
theorem B675035 : Blo 674311 675035 := bstep (se 1 (by rfl) ⟨506276, by rfl⟩ : syracuseStep 675035 = 1012553) B1012553
theorem B675111 : Blo 674311 675111 := bstep (se 1 (by rfl) ⟨506333, by rfl⟩ : syracuseStep 675111 = 1012667) B1012667
theorem B675151 : Blo 674311 675151 := bstep (se 1 (by rfl) ⟨506363, by rfl⟩ : syracuseStep 675151 = 1012727) B1012727
theorem B675167 : Blo 674311 675167 := bstep (se 1 (by rfl) ⟨506375, by rfl⟩ : syracuseStep 675167 = 1012751) B1012751
theorem B675195 : Blo 674311 675195 := bstep (se 1 (by rfl) ⟨506396, by rfl⟩ : syracuseStep 675195 = 1012793) B1012793
theorem B2936189 : Blo 674311 2936189 := bstep (se 3 (by rfl) ⟨550535, by rfl⟩ : syracuseStep 2936189 = 1101071) B1101071
theorem B3427757 : Blo 674311 3427757 := bstep (se 3 (by rfl) ⟨642704, by rfl⟩ : syracuseStep 3427757 = 1285409) B1285409
theorem B675247 : Blo 674311 675247 := bstep (se 1 (by rfl) ⟨506435, by rfl⟩ : syracuseStep 675247 = 1012871) B1012871
theorem B675271 : Blo 674311 675271 := bstep (se 1 (by rfl) ⟨506453, by rfl⟩ : syracuseStep 675271 = 1012907) B1012907
theorem B2280905 : Blo 674311 2280905 := bstep (se 2 (by rfl) ⟨855339, by rfl⟩ : syracuseStep 2280905 = 1710679) B1710679
theorem B675291 : Blo 674311 675291 := bstep (se 1 (by rfl) ⟨506468, by rfl⟩ : syracuseStep 675291 = 1012937) B1012937
theorem B2674201 : Blo 674311 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B675367 : Blo 674311 675367 := bstep (se 1 (by rfl) ⟨506525, by rfl⟩ : syracuseStep 675367 = 1013051) B1013051
theorem B675407 : Blo 674311 675407 := bstep (se 1 (by rfl) ⟨506555, by rfl⟩ : syracuseStep 675407 = 1013111) B1013111
theorem B675423 : Blo 674311 675423 := bstep (se 1 (by rfl) ⟨506567, by rfl⟩ : syracuseStep 675423 = 1013135) B1013135
theorem B675451 : Blo 674311 675451 := bstep (se 1 (by rfl) ⟨506588, by rfl⟩ : syracuseStep 675451 = 1013177) B1013177
theorem B675503 : Blo 674311 675503 := bstep (se 1 (by rfl) ⟨506627, by rfl⟩ : syracuseStep 675503 = 1013255) B1013255
theorem B675527 : Blo 674311 675527 := bstep (se 1 (by rfl) ⟨506645, by rfl⟩ : syracuseStep 675527 = 1013291) B1013291
theorem B5492423 : Blo 674311 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B2936519 : Blo 674311 2936519 := bstep (se 1 (by rfl) ⟨2202389, by rfl⟩ : syracuseStep 2936519 = 4404779) B4404779
theorem B2281175 : Blo 674311 2281175 := bstep (se 1 (by rfl) ⟨1710881, by rfl⟩ : syracuseStep 2281175 = 3421763) B3421763
theorem B675547 : Blo 674311 675547 := bstep (se 1 (by rfl) ⟨506660, by rfl⟩ : syracuseStep 675547 = 1013321) B1013321
theorem B1232633 : Blo 674311 1232633 := bstep (se 2 (by rfl) ⟨462237, by rfl⟩ : syracuseStep 1232633 = 924475) B924475
theorem B675623 : Blo 674311 675623 := bstep (se 1 (by rfl) ⟨506717, by rfl⟩ : syracuseStep 675623 = 1013435) B1013435
theorem B675663 : Blo 674311 675663 := bstep (se 1 (by rfl) ⟨506747, by rfl⟩ : syracuseStep 675663 = 1013495) B1013495
theorem B675679 : Blo 674311 675679 := bstep (se 1 (by rfl) ⟨506759, by rfl⟩ : syracuseStep 675679 = 1013519) B1013519
theorem B675707 : Blo 674311 675707 := bstep (se 1 (by rfl) ⟨506780, by rfl⟩ : syracuseStep 675707 = 1013561) B1013561
theorem B675759 : Blo 674311 675759 := bstep (se 1 (by rfl) ⟨506819, by rfl⟩ : syracuseStep 675759 = 1013639) B1013639
theorem B2281391 : Blo 674311 2281391 := bstep (se 1 (by rfl) ⟨1711043, by rfl⟩ : syracuseStep 2281391 = 3422087) B3422087
theorem B3559355 : Blo 674311 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B675783 : Blo 674311 675783 := bstep (se 1 (by rfl) ⟨506837, by rfl⟩ : syracuseStep 675783 = 1013675) B1013675
theorem B675803 : Blo 674311 675803 := bstep (se 1 (by rfl) ⟨506852, by rfl⟩ : syracuseStep 675803 = 1013705) B1013705
theorem B675879 : Blo 674311 675879 := bstep (se 1 (by rfl) ⟨506909, by rfl⟩ : syracuseStep 675879 = 1013819) B1013819
theorem B675919 : Blo 674311 675919 := bstep (se 1 (by rfl) ⟨506939, by rfl⟩ : syracuseStep 675919 = 1013879) B1013879
theorem B3657809 : Blo 674311 3657809 := bstep (se 2 (by rfl) ⟨1371678, by rfl⟩ : syracuseStep 3657809 = 2743357) B2743357
theorem B675935 : Blo 674311 675935 := bstep (se 1 (by rfl) ⟨506951, by rfl⟩ : syracuseStep 675935 = 1013903) B1013903
theorem B675963 : Blo 674311 675963 := bstep (se 1 (by rfl) ⟨506972, by rfl⟩ : syracuseStep 675963 = 1013945) B1013945
theorem B7327907 : Blo 674311 7327907 := bstep (se 1 (by rfl) ⟨5495930, by rfl⟩ : syracuseStep 7327907 = 10991861) B10991861
theorem B676015 : Blo 674311 676015 := bstep (se 1 (by rfl) ⟨507011, by rfl⟩ : syracuseStep 676015 = 1014023) B1014023
theorem B676039 : Blo 674311 676039 := bstep (se 1 (by rfl) ⟨507029, by rfl⟩ : syracuseStep 676039 = 1014059) B1014059
theorem B676059 : Blo 674311 676059 := bstep (se 1 (by rfl) ⟨507044, by rfl⟩ : syracuseStep 676059 = 1014089) B1014089
theorem B676135 : Blo 674311 676135 := bstep (se 1 (by rfl) ⟨507101, by rfl⟩ : syracuseStep 676135 = 1014203) B1014203
theorem B676175 : Blo 674311 676175 := bstep (se 1 (by rfl) ⟨507131, by rfl⟩ : syracuseStep 676175 = 1014263) B1014263
theorem B676191 : Blo 674311 676191 := bstep (se 1 (by rfl) ⟨507143, by rfl⟩ : syracuseStep 676191 = 1014287) B1014287
theorem B676219 : Blo 674311 676219 := bstep (se 1 (by rfl) ⟨507164, by rfl⟩ : syracuseStep 676219 = 1014329) B1014329
theorem B676271 : Blo 674311 676271 := bstep (se 1 (by rfl) ⟨507203, by rfl⟩ : syracuseStep 676271 = 1014407) B1014407
theorem B676295 : Blo 674311 676295 := bstep (se 1 (by rfl) ⟨507221, by rfl⟩ : syracuseStep 676295 = 1014443) B1014443
theorem B8671697 : Blo 674311 8671697 := bstep (se 2 (by rfl) ⟨3251886, by rfl⟩ : syracuseStep 8671697 = 6503773) B6503773
theorem B676315 : Blo 674311 676315 := bstep (se 1 (by rfl) ⟨507236, by rfl⟩ : syracuseStep 676315 = 1014473) B1014473
theorem B5788169 : Blo 674311 5788169 := bstep (se 2 (by rfl) ⟨2170563, by rfl⟩ : syracuseStep 5788169 = 4341127) B4341127
theorem B676391 : Blo 674311 676391 := bstep (se 1 (by rfl) ⟨507293, by rfl⟩ : syracuseStep 676391 = 1014587) B1014587
theorem B676431 : Blo 674311 676431 := bstep (se 1 (by rfl) ⟨507323, by rfl⟩ : syracuseStep 676431 = 1014647) B1014647
theorem B676447 : Blo 674311 676447 := bstep (se 1 (by rfl) ⟨507335, by rfl⟩ : syracuseStep 676447 = 1014671) B1014671
theorem B676475 : Blo 674311 676475 := bstep (se 1 (by rfl) ⟨507356, by rfl⟩ : syracuseStep 676475 = 1014713) B1014713
theorem B676527 : Blo 674311 676527 := bstep (se 1 (by rfl) ⟨507395, by rfl⟩ : syracuseStep 676527 = 1014791) B1014791
theorem B1921735 : Blo 674311 1921735 := bstep (se 1 (by rfl) ⟨1441301, by rfl⟩ : syracuseStep 1921735 = 2882603) B2882603
theorem B676551 : Blo 674311 676551 := bstep (se 1 (by rfl) ⟨507413, by rfl⟩ : syracuseStep 676551 = 1014827) B1014827
theorem B676571 : Blo 674311 676571 := bstep (se 1 (by rfl) ⟨507428, by rfl⟩ : syracuseStep 676571 = 1014857) B1014857
theorem B676647 : Blo 674311 676647 := bstep (se 1 (by rfl) ⟨507485, by rfl⟩ : syracuseStep 676647 = 1014971) B1014971
theorem B676687 : Blo 674311 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B676703 : Blo 674311 676703 := bstep (se 1 (by rfl) ⟨507527, by rfl⟩ : syracuseStep 676703 = 1015055) B1015055
theorem B676731 : Blo 674311 676731 := bstep (se 1 (by rfl) ⟨507548, by rfl⟩ : syracuseStep 676731 = 1015097) B1015097
theorem B676783 : Blo 674311 676783 := bstep (se 1 (by rfl) ⟨507587, by rfl⟩ : syracuseStep 676783 = 1015175) B1015175
theorem B676807 : Blo 674311 676807 := bstep (se 1 (by rfl) ⟨507605, by rfl⟩ : syracuseStep 676807 = 1015211) B1015211
theorem B676827 : Blo 674311 676827 := bstep (se 1 (by rfl) ⟨507620, by rfl⟩ : syracuseStep 676827 = 1015241) B1015241
theorem B3429377 : Blo 674311 3429377 := bstep (se 2 (by rfl) ⟨1286016, by rfl⟩ : syracuseStep 3429377 = 2572033) B2572033
theorem B676903 : Blo 674311 676903 := bstep (se 1 (by rfl) ⟨507677, by rfl⟩ : syracuseStep 676903 = 1015355) B1015355
theorem B676943 : Blo 674311 676943 := bstep (se 1 (by rfl) ⟨507707, by rfl⟩ : syracuseStep 676943 = 1015415) B1015415
theorem B676959 : Blo 674311 676959 := bstep (se 1 (by rfl) ⟨507719, by rfl⟩ : syracuseStep 676959 = 1015439) B1015439
theorem B676987 : Blo 674311 676987 := bstep (se 1 (by rfl) ⟨507740, by rfl⟩ : syracuseStep 676987 = 1015481) B1015481
theorem B677039 : Blo 674311 677039 := bstep (se 1 (by rfl) ⟨507779, by rfl⟩ : syracuseStep 677039 = 1015559) B1015559
theorem B677063 : Blo 674311 677063 := bstep (se 1 (by rfl) ⟨507797, by rfl⟩ : syracuseStep 677063 = 1015595) B1015595
theorem B677083 : Blo 674311 677083 := bstep (se 1 (by rfl) ⟨507812, by rfl⟩ : syracuseStep 677083 = 1015625) B1015625
theorem B677159 : Blo 674311 677159 := bstep (se 1 (by rfl) ⟨507869, by rfl⟩ : syracuseStep 677159 = 1015739) B1015739
theorem B677199 : Blo 674311 677199 := bstep (se 1 (by rfl) ⟨507899, by rfl⟩ : syracuseStep 677199 = 1015799) B1015799
theorem B677215 : Blo 674311 677215 := bstep (se 1 (by rfl) ⟨507911, by rfl⟩ : syracuseStep 677215 = 1015823) B1015823
theorem B677243 : Blo 674311 677243 := bstep (se 1 (by rfl) ⟨507932, by rfl⟩ : syracuseStep 677243 = 1015865) B1015865
theorem B677295 : Blo 674311 677295 := bstep (se 1 (by rfl) ⟨507971, by rfl⟩ : syracuseStep 677295 = 1015943) B1015943
theorem B677319 : Blo 674311 677319 := bstep (se 1 (by rfl) ⟨507989, by rfl⟩ : syracuseStep 677319 = 1015979) B1015979
theorem B677339 : Blo 674311 677339 := bstep (se 1 (by rfl) ⟨508004, by rfl⟩ : syracuseStep 677339 = 1016009) B1016009
theorem B677415 : Blo 674311 677415 := bstep (se 1 (by rfl) ⟨508061, by rfl⟩ : syracuseStep 677415 = 1016123) B1016123
theorem B677455 : Blo 674311 677455 := bstep (se 1 (by rfl) ⟨508091, by rfl⟩ : syracuseStep 677455 = 1016183) B1016183
theorem B677471 : Blo 674311 677471 := bstep (se 1 (by rfl) ⟨508103, by rfl⟩ : syracuseStep 677471 = 1016207) B1016207
theorem B677499 : Blo 674311 677499 := bstep (se 1 (by rfl) ⟨508124, by rfl⟩ : syracuseStep 677499 = 1016249) B1016249
theorem B35149463 : Blo 674311 35149463 := bstep (se 1 (by rfl) ⟨26362097, by rfl⟩ : syracuseStep 35149463 = 52724195) B52724195
theorem B677551 : Blo 674311 677551 := bstep (se 1 (by rfl) ⟨508163, by rfl⟩ : syracuseStep 677551 = 1016327) B1016327
theorem B9885377 : Blo 674311 9885377 := bstep (se 2 (by rfl) ⟨3707016, by rfl⟩ : syracuseStep 9885377 = 7414033) B7414033
theorem B677575 : Blo 674311 677575 := bstep (se 1 (by rfl) ⟨508181, by rfl⟩ : syracuseStep 677575 = 1016363) B1016363
theorem B677595 : Blo 674311 677595 := bstep (se 1 (by rfl) ⟨508196, by rfl⟩ : syracuseStep 677595 = 1016393) B1016393
theorem B677671 : Blo 674311 677671 := bstep (se 1 (by rfl) ⟨508253, by rfl⟩ : syracuseStep 677671 = 1016507) B1016507
theorem B3430187 : Blo 674311 3430187 := bstep (se 1 (by rfl) ⟨2572640, by rfl⟩ : syracuseStep 3430187 = 5145281) B5145281
theorem B677711 : Blo 674311 677711 := bstep (se 1 (by rfl) ⟨508283, by rfl⟩ : syracuseStep 677711 = 1016567) B1016567
theorem B677727 : Blo 674311 677727 := bstep (se 1 (by rfl) ⟨508295, by rfl⟩ : syracuseStep 677727 = 1016591) B1016591
theorem B677755 : Blo 674311 677755 := bstep (se 1 (by rfl) ⟨508316, by rfl⟩ : syracuseStep 677755 = 1016633) B1016633
theorem B2742191 : Blo 674311 2742191 := bstep (se 1 (by rfl) ⟨2056643, by rfl⟩ : syracuseStep 2742191 = 4113287) B4113287
theorem B677807 : Blo 674311 677807 := bstep (se 1 (by rfl) ⟨508355, by rfl⟩ : syracuseStep 677807 = 1016711) B1016711
theorem B677831 : Blo 674311 677831 := bstep (se 1 (by rfl) ⟨508373, by rfl⟩ : syracuseStep 677831 = 1016747) B1016747
theorem B677851 : Blo 674311 677851 := bstep (se 1 (by rfl) ⟨508388, by rfl⟩ : syracuseStep 677851 = 1016777) B1016777
theorem B677927 : Blo 674311 677927 := bstep (se 1 (by rfl) ⟨508445, by rfl⟩ : syracuseStep 677927 = 1016891) B1016891
theorem B677967 : Blo 674311 677967 := bstep (se 1 (by rfl) ⟨508475, by rfl⟩ : syracuseStep 677967 = 1016951) B1016951
theorem B677983 : Blo 674311 677983 := bstep (se 1 (by rfl) ⟨508487, by rfl⟩ : syracuseStep 677983 = 1016975) B1016975
theorem B678011 : Blo 674311 678011 := bstep (se 1 (by rfl) ⟨508508, by rfl⟩ : syracuseStep 678011 = 1017017) B1017017
theorem B678063 : Blo 674311 678063 := bstep (se 1 (by rfl) ⟨508547, by rfl⟩ : syracuseStep 678063 = 1017095) B1017095
theorem B678087 : Blo 674311 678087 := bstep (se 1 (by rfl) ⟨508565, by rfl⟩ : syracuseStep 678087 = 1017131) B1017131
theorem B678107 : Blo 674311 678107 := bstep (se 1 (by rfl) ⟨508580, by rfl⟩ : syracuseStep 678107 = 1017161) B1017161
theorem B2283767 : Blo 674311 2283767 := bstep (se 1 (by rfl) ⟨1712825, by rfl⟩ : syracuseStep 2283767 = 3425651) B3425651
theorem B678183 : Blo 674311 678183 := bstep (se 1 (by rfl) ⟨508637, by rfl⟩ : syracuseStep 678183 = 1017275) B1017275
theorem B9394481 : Blo 674311 9394481 := bstep (se 2 (by rfl) ⟨3522930, by rfl⟩ : syracuseStep 9394481 = 7045861) B7045861
theorem B678223 : Blo 674311 678223 := bstep (se 1 (by rfl) ⟨508667, by rfl⟩ : syracuseStep 678223 = 1017335) B1017335
theorem B678239 : Blo 674311 678239 := bstep (se 1 (by rfl) ⟨508679, by rfl⟩ : syracuseStep 678239 = 1017359) B1017359
theorem B678267 : Blo 674311 678267 := bstep (se 1 (by rfl) ⟨508700, by rfl⟩ : syracuseStep 678267 = 1017401) B1017401
theorem B24697223 : Blo 674311 24697223 := bstep (se 1 (by rfl) ⟨18522917, by rfl⟩ : syracuseStep 24697223 = 37045835) B37045835
theorem B1923547 : Blo 674311 1923547 := bstep (se 1 (by rfl) ⟨1442660, by rfl⟩ : syracuseStep 1923547 = 2885321) B2885321
theorem B2284091 : Blo 674311 2284091 := bstep (se 1 (by rfl) ⟨1713068, by rfl⟩ : syracuseStep 2284091 = 3426137) B3426137
theorem B2284361 : Blo 674311 2284361 := bstep (se 2 (by rfl) ⟨856635, by rfl⟩ : syracuseStep 2284361 = 1713271) B1713271
theorem B7297937 : Blo 674311 7297937 := bstep (se 2 (by rfl) ⟨2736726, by rfl⟩ : syracuseStep 7297937 = 5473453) B5473453
theorem B1138063 : Blo 674311 1138063 := bstep (se 1 (by rfl) ⟨853547, by rfl⟩ : syracuseStep 1138063 = 1707095) B1707095
theorem B9264527 : Blo 674311 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B1367479 : Blo 674311 1367479 := bstep (se 1 (by rfl) ⟨1025609, by rfl⟩ : syracuseStep 1367479 = 2051219) B2051219
theorem B1170983 : Blo 674311 1170983 := bstep (se 1 (by rfl) ⟨878237, by rfl⟩ : syracuseStep 1170983 = 1756475) B1756475
theorem B1367675 : Blo 674311 1367675 := bstep (se 1 (by rfl) ⟨1025756, by rfl⟩ : syracuseStep 1367675 = 2051513) B2051513
theorem B1924823 : Blo 674311 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B1925039 : Blo 674311 1925039 := bstep (se 1 (by rfl) ⟨1443779, by rfl⟩ : syracuseStep 1925039 = 2887559) B2887559
theorem B2285495 : Blo 674311 2285495 := bstep (se 1 (by rfl) ⟨1714121, by rfl⟩ : syracuseStep 2285495 = 3428243) B3428243
theorem B3432455 : Blo 674311 3432455 := bstep (se 1 (by rfl) ⟨2574341, by rfl⟩ : syracuseStep 3432455 = 5148683) B5148683
theorem B1138745 : Blo 674311 1138745 := bstep (se 2 (by rfl) ⟨427029, by rfl⟩ : syracuseStep 1138745 = 854059) B854059
theorem B3432941 : Blo 674311 3432941 := bstep (se 3 (by rfl) ⟨643676, by rfl⟩ : syracuseStep 3432941 = 1287353) B1287353
theorem B2744819 : Blo 674311 2744819 := bstep (se 1 (by rfl) ⟨2058614, by rfl⟩ : syracuseStep 2744819 = 4117229) B4117229
theorem B2286089 : Blo 674311 2286089 := bstep (se 2 (by rfl) ⟨857283, by rfl⟩ : syracuseStep 2286089 = 1714567) B1714567
theorem B1139447 : Blo 674311 1139447 := bstep (se 1 (by rfl) ⟨854585, by rfl⟩ : syracuseStep 1139447 = 1709171) B1709171
theorem B1139791 : Blo 674311 1139791 := bstep (se 1 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 1139791 = 1709687) B1709687
theorem B812155 : Blo 674311 812155 := bstep (se 1 (by rfl) ⟨609116, by rfl⟩ : syracuseStep 812155 = 1218233) B1218233
theorem B3433751 : Blo 674311 3433751 := bstep (se 1 (by rfl) ⟨2575313, by rfl⟩ : syracuseStep 3433751 = 5150627) B5150627
theorem B1140041 : Blo 674311 1140041 := bstep (se 2 (by rfl) ⟨427515, by rfl⟩ : syracuseStep 1140041 = 855031) B855031
theorem B2286953 : Blo 674311 2286953 := bstep (se 2 (by rfl) ⟨857607, by rfl⟩ : syracuseStep 2286953 = 1715215) B1715215
theorem B1238537 : Blo 674311 1238537 := bstep (se 2 (by rfl) ⟨464451, by rfl⟩ : syracuseStep 1238537 = 928903) B928903
theorem B2319911 : Blo 674311 2319911 := bstep (se 1 (by rfl) ⟨1739933, by rfl⟩ : syracuseStep 2319911 = 3479867) B3479867
theorem B1140473 : Blo 674311 1140473 := bstep (se 2 (by rfl) ⟨427677, by rfl⟩ : syracuseStep 1140473 = 855355) B855355
theorem B1140655 : Blo 674311 1140655 := bstep (se 1 (by rfl) ⟨855491, by rfl⟩ : syracuseStep 1140655 = 1710983) B1710983
theorem B2287547 : Blo 674311 2287547 := bstep (se 1 (by rfl) ⟨1715660, by rfl⟩ : syracuseStep 2287547 = 3431321) B3431321
theorem B1140743 : Blo 674311 1140743 := bstep (se 1 (by rfl) ⟨855557, by rfl⟩ : syracuseStep 1140743 = 1711115) B1711115
theorem B1141087 : Blo 674311 1141087 := bstep (se 1 (by rfl) ⟨855815, by rfl⟩ : syracuseStep 1141087 = 1711631) B1711631
theorem B4614529 : Blo 674311 4614529 := bstep (se 2 (by rfl) ⟨1730448, by rfl⟩ : syracuseStep 4614529 = 3460897) B3460897
theorem B1927567 : Blo 674311 1927567 := bstep (se 1 (by rfl) ⟨1445675, by rfl⟩ : syracuseStep 1927567 = 2891351) B2891351
theorem B1141175 : Blo 674311 1141175 := bstep (se 1 (by rfl) ⟨855881, by rfl⟩ : syracuseStep 1141175 = 1711763) B1711763
theorem B8645453 : Blo 674311 8645453 := bstep (se 3 (by rfl) ⟨1621022, by rfl⟩ : syracuseStep 8645453 = 3242045) B3242045
theorem B1141769 : Blo 674311 1141769 := bstep (se 2 (by rfl) ⟨428163, by rfl⟩ : syracuseStep 1141769 = 856327) B856327
theorem B1141931 : Blo 674311 1141931 := bstep (se 1 (by rfl) ⟨856448, by rfl⟩ : syracuseStep 1141931 = 1712897) B1712897
theorem B814519 : Blo 674311 814519 := bstep (se 1 (by rfl) ⟨610889, by rfl⟩ : syracuseStep 814519 = 1221779) B1221779
theorem B1142329 : Blo 674311 1142329 := bstep (se 2 (by rfl) ⟨428373, by rfl⟩ : syracuseStep 1142329 = 856747) B856747
theorem B1371745 : Blo 674311 1371745 := bstep (se 2 (by rfl) ⟨514404, by rfl⟩ : syracuseStep 1371745 = 1028809) B1028809
theorem B2289275 : Blo 674311 2289275 := bstep (se 1 (by rfl) ⟨1716956, by rfl⟩ : syracuseStep 2289275 = 3433913) B3433913
theorem B1928843 : Blo 674311 1928843 := bstep (se 1 (by rfl) ⟨1446632, by rfl⟩ : syracuseStep 1928843 = 2893265) B2893265
theorem B1142471 : Blo 674311 1142471 := bstep (se 1 (by rfl) ⟨856853, by rfl⟩ : syracuseStep 1142471 = 1713707) B1713707
theorem B1011551 : Blo 674311 1011551 := bstep (se 1 (by rfl) ⟨758663, by rfl⟩ : syracuseStep 1011551 = 1517327) B1517327
theorem B1142633 : Blo 674311 1142633 := bstep (se 2 (by rfl) ⟨428487, by rfl⟩ : syracuseStep 1142633 = 856975) B856975
theorem B1011563 : Blo 674311 1011563 := bstep (se 1 (by rfl) ⟨758672, by rfl⟩ : syracuseStep 1011563 = 1517345) B1517345
theorem B3665857 : Blo 674311 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B1011791 : Blo 674311 1011791 := bstep (se 1 (by rfl) ⟨758843, by rfl⟩ : syracuseStep 1011791 = 1517687) B1517687
theorem B1011911 : Blo 674311 1011911 := bstep (se 1 (by rfl) ⟨758933, by rfl⟩ : syracuseStep 1011911 = 1517867) B1517867
theorem B1143031 : Blo 674311 1143031 := bstep (se 1 (by rfl) ⟨857273, by rfl⟩ : syracuseStep 1143031 = 1714547) B1714547
theorem B1012073 : Blo 674311 1012073 := bstep (se 2 (by rfl) ⟨379527, by rfl⟩ : syracuseStep 1012073 = 759055) B759055
theorem B1012151 : Blo 674311 1012151 := bstep (se 1 (by rfl) ⟨759113, by rfl⟩ : syracuseStep 1012151 = 1518227) B1518227
theorem B913847 : Blo 674311 913847 := bstep (se 1 (by rfl) ⟨685385, by rfl⟩ : syracuseStep 913847 = 1370771) B1370771
theorem B1143227 : Blo 674311 1143227 := bstep (se 1 (by rfl) ⟨857420, by rfl⟩ : syracuseStep 1143227 = 1714841) B1714841
theorem B1012187 : Blo 674311 1012187 := bstep (se 1 (by rfl) ⟨759140, by rfl⟩ : syracuseStep 1012187 = 1518281) B1518281
theorem B1143335 : Blo 674311 1143335 := bstep (se 1 (by rfl) ⟨857501, by rfl⟩ : syracuseStep 1143335 = 1715003) B1715003
theorem B1143625 : Blo 674311 1143625 := bstep (se 2 (by rfl) ⟨428859, by rfl⟩ : syracuseStep 1143625 = 857719) B857719
theorem B1143659 : Blo 674311 1143659 := bstep (se 1 (by rfl) ⟨857744, by rfl⟩ : syracuseStep 1143659 = 1715489) B1715489
theorem B5141393 : Blo 674311 5141393 := bstep (se 2 (by rfl) ⟨1928022, by rfl⟩ : syracuseStep 5141393 = 3856045) B3856045
theorem B2061217 : Blo 674311 2061217 := bstep (se 2 (by rfl) ⟨772956, by rfl⟩ : syracuseStep 2061217 = 1545913) B1545913
theorem B1012655 : Blo 674311 1012655 := bstep (se 1 (by rfl) ⟨759491, by rfl⟩ : syracuseStep 1012655 = 1518983) B1518983
theorem B1012745 : Blo 674311 1012745 := bstep (se 2 (by rfl) ⟨379779, by rfl⟩ : syracuseStep 1012745 = 759559) B759559
theorem B1012775 : Blo 674311 1012775 := bstep (se 1 (by rfl) ⟨759581, by rfl⟩ : syracuseStep 1012775 = 1519163) B1519163
theorem B685135 : Blo 674311 685135 := bstep (se 1 (by rfl) ⟨513851, by rfl⟩ : syracuseStep 685135 = 1027703) B1027703
theorem B1012859 : Blo 674311 1012859 := bstep (se 1 (by rfl) ⟨759644, by rfl⟩ : syracuseStep 1012859 = 1519289) B1519289
theorem B6943961 : Blo 674311 6943961 := bstep (se 2 (by rfl) ⟨2603985, by rfl⟩ : syracuseStep 6943961 = 5207971) B5207971
theorem B1012985 : Blo 674311 1012985 := bstep (se 2 (by rfl) ⟨379869, by rfl⟩ : syracuseStep 1012985 = 759739) B759739
theorem B1144057 : Blo 674311 1144057 := bstep (se 2 (by rfl) ⟨429021, by rfl⟩ : syracuseStep 1144057 = 858043) B858043
theorem B1013087 : Blo 674311 1013087 := bstep (se 1 (by rfl) ⟨759815, by rfl⟩ : syracuseStep 1013087 = 1519631) B1519631
theorem B1013099 : Blo 674311 1013099 := bstep (se 1 (by rfl) ⟨759824, by rfl⟩ : syracuseStep 1013099 = 1519649) B1519649
theorem B3077519 : Blo 674311 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B1144327 : Blo 674311 1144327 := bstep (se 1 (by rfl) ⟨858245, by rfl⟩ : syracuseStep 1144327 = 1716491) B1716491
theorem B4388413 : Blo 674311 4388413 := bstep (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) B1645655
theorem B1013327 : Blo 674311 1013327 := bstep (se 1 (by rfl) ⟨759995, by rfl⟩ : syracuseStep 1013327 = 1519991) B1519991
theorem B1013447 : Blo 674311 1013447 := bstep (se 1 (by rfl) ⟨760085, by rfl⟩ : syracuseStep 1013447 = 1520171) B1520171
theorem B1832647 : Blo 674311 1832647 := bstep (se 1 (by rfl) ⟨1374485, by rfl⟩ : syracuseStep 1832647 = 2748971) B2748971
theorem B9729827 : Blo 674311 9729827 := bstep (se 1 (by rfl) ⟨7297370, by rfl⟩ : syracuseStep 9729827 = 14594741) B14594741
theorem B1734473 : Blo 674311 1734473 := bstep (se 2 (by rfl) ⟨650427, by rfl⟩ : syracuseStep 1734473 = 1300855) B1300855
theorem B1013609 : Blo 674311 1013609 := bstep (se 2 (by rfl) ⟨380103, by rfl⟩ : syracuseStep 1013609 = 760207) B760207
theorem B1013687 : Blo 674311 1013687 := bstep (se 1 (by rfl) ⟨760265, by rfl⟩ : syracuseStep 1013687 = 1520531) B1520531
theorem B9238481 : Blo 674311 9238481 := bstep (se 2 (by rfl) ⟨3464430, by rfl⟩ : syracuseStep 9238481 = 6928861) B6928861
theorem B1013723 : Blo 674311 1013723 := bstep (se 1 (by rfl) ⟨760292, by rfl⟩ : syracuseStep 1013723 = 1520585) B1520585
theorem B39090437 : Blo 674311 39090437 := bstep (se 4 (by rfl) ⟨3664728, by rfl⟩ : syracuseStep 39090437 = 7329457) B7329457
theorem B1014191 : Blo 674311 1014191 := bstep (se 1 (by rfl) ⟨760643, by rfl⟩ : syracuseStep 1014191 = 1521287) B1521287
theorem B1014281 : Blo 674311 1014281 := bstep (se 2 (by rfl) ⟨380355, by rfl⟩ : syracuseStep 1014281 = 760711) B760711
theorem B1014311 : Blo 674311 1014311 := bstep (se 1 (by rfl) ⟨760733, by rfl⟩ : syracuseStep 1014311 = 1521467) B1521467
theorem B1440379 : Blo 674311 1440379 := bstep (se 1 (by rfl) ⟨1080284, by rfl⟩ : syracuseStep 1440379 = 2160569) B2160569
theorem B1014395 : Blo 674311 1014395 := bstep (se 1 (by rfl) ⟨760796, by rfl⟩ : syracuseStep 1014395 = 1521593) B1521593
theorem B1014521 : Blo 674311 1014521 := bstep (se 2 (by rfl) ⟨380445, by rfl⟩ : syracuseStep 1014521 = 760891) B760891
theorem B1014623 : Blo 674311 1014623 := bstep (se 1 (by rfl) ⟨760967, by rfl⟩ : syracuseStep 1014623 = 1521935) B1521935
theorem B1014635 : Blo 674311 1014635 := bstep (se 1 (by rfl) ⟨760976, by rfl⟩ : syracuseStep 1014635 = 1521953) B1521953
theorem B1014863 : Blo 674311 1014863 := bstep (se 1 (by rfl) ⟨761147, by rfl⟩ : syracuseStep 1014863 = 1522295) B1522295
theorem B1014983 : Blo 674311 1014983 := bstep (se 1 (by rfl) ⟨761237, by rfl⟩ : syracuseStep 1014983 = 1522475) B1522475
theorem B5143823 : Blo 674311 5143823 := bstep (se 1 (by rfl) ⟨3857867, by rfl⟩ : syracuseStep 5143823 = 7715735) B7715735
theorem B55639385 : Blo 674311 55639385 := bstep (se 2 (by rfl) ⟨20864769, by rfl⟩ : syracuseStep 55639385 = 41729539) B41729539
theorem B1015145 : Blo 674311 1015145 := bstep (se 2 (by rfl) ⟨380679, by rfl⟩ : syracuseStep 1015145 = 761359) B761359
theorem B1015223 : Blo 674311 1015223 := bstep (se 1 (by rfl) ⟨761417, by rfl⟩ : syracuseStep 1015223 = 1522835) B1522835
theorem B1015259 : Blo 674311 1015259 := bstep (se 1 (by rfl) ⟨761444, by rfl⟩ : syracuseStep 1015259 = 1522889) B1522889
theorem B36961757 : Blo 674311 36961757 := bstep (se 3 (by rfl) ⟨6930329, by rfl⟩ : syracuseStep 36961757 = 13860659) B13860659
theorem B2162209 : Blo 674311 2162209 := bstep (se 2 (by rfl) ⟨810828, by rfl⟩ : syracuseStep 2162209 = 1621657) B1621657
theorem B720463 : Blo 674311 720463 := bstep (se 1 (by rfl) ⟨540347, by rfl⟩ : syracuseStep 720463 = 1080695) B1080695
theorem B1441643 : Blo 674311 1441643 := bstep (se 1 (by rfl) ⟨1081232, by rfl⟩ : syracuseStep 1441643 = 2162465) B2162465
theorem B1015727 : Blo 674311 1015727 := bstep (se 1 (by rfl) ⟨761795, by rfl⟩ : syracuseStep 1015727 = 1523591) B1523591
theorem B1015913 : Blo 674311 1015913 := bstep (se 2 (by rfl) ⟨380967, by rfl⟩ : syracuseStep 1015913 = 761935) B761935
theorem B58458509 : Blo 674311 58458509 := bstep (se 3 (by rfl) ⟨10960970, by rfl⟩ : syracuseStep 58458509 = 21921941) B21921941
theorem B1016231 : Blo 674311 1016231 := bstep (se 1 (by rfl) ⟨762173, by rfl⟩ : syracuseStep 1016231 = 1524347) B1524347
theorem B1016315 : Blo 674311 1016315 := bstep (se 1 (by rfl) ⟨762236, by rfl⟩ : syracuseStep 1016315 = 1524473) B1524473
theorem B721471 : Blo 674311 721471 := bstep (se 1 (by rfl) ⟨541103, by rfl⟩ : syracuseStep 721471 = 1082207) B1082207
theorem B1016441 : Blo 674311 1016441 := bstep (se 2 (by rfl) ⟨381165, by rfl⟩ : syracuseStep 1016441 = 762331) B762331
theorem B2884243 : Blo 674311 2884243 := bstep (se 1 (by rfl) ⟨2163182, by rfl⟩ : syracuseStep 2884243 = 4326365) B4326365
theorem B1016495 : Blo 674311 1016495 := bstep (se 1 (by rfl) ⟨762371, by rfl⟩ : syracuseStep 1016495 = 1524743) B1524743
theorem B1016543 : Blo 674311 1016543 := bstep (se 1 (by rfl) ⟨762407, by rfl⟩ : syracuseStep 1016543 = 1524815) B1524815
theorem B1016807 : Blo 674311 1016807 := bstep (se 1 (by rfl) ⟨762605, by rfl⟩ : syracuseStep 1016807 = 1525211) B1525211
theorem B1541243 : Blo 674311 1541243 := bstep (se 1 (by rfl) ⟨1155932, by rfl⟩ : syracuseStep 1541243 = 2311865) B2311865
theorem B1017065 : Blo 674311 1017065 := bstep (se 2 (by rfl) ⟨381399, by rfl⟩ : syracuseStep 1017065 = 762799) B762799
theorem B1017119 : Blo 674311 1017119 := bstep (se 1 (by rfl) ⟨762839, by rfl⟩ : syracuseStep 1017119 = 1525679) B1525679
theorem B722287 : Blo 674311 722287 := bstep (se 1 (by rfl) ⟨541715, by rfl⟩ : syracuseStep 722287 = 1083431) B1083431
theorem B1443233 : Blo 674311 1443233 := bstep (se 2 (by rfl) ⟨541212, by rfl⟩ : syracuseStep 1443233 = 1082425) B1082425
theorem B1017287 : Blo 674311 1017287 := bstep (se 1 (by rfl) ⟨762965, by rfl⟩ : syracuseStep 1017287 = 1525931) B1525931
theorem B1082873 : Blo 674311 1082873 := bstep (se 2 (by rfl) ⟨406077, by rfl⟩ : syracuseStep 1082873 = 812155) B812155
theorem B1082975 : Blo 674311 1082975 := bstep (se 1 (by rfl) ⟨812231, by rfl⟩ : syracuseStep 1082975 = 1624463) B1624463
theorem B853679 : Blo 674311 853679 := bstep (se 1 (by rfl) ⟨640259, by rfl⟩ : syracuseStep 853679 = 1280519) B1280519
theorem B11569229 : Blo 674311 11569229 := bstep (se 3 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 11569229 = 4338461) B4338461
theorem B854383 : Blo 674311 854383 := bstep (se 1 (by rfl) ⟨640787, by rfl⟩ : syracuseStep 854383 = 1281575) B1281575
theorem B821755 : Blo 674311 821755 := bstep (se 1 (by rfl) ⟨616316, by rfl⟩ : syracuseStep 821755 = 1232633) B1232633
theorem B4885271 : Blo 674311 4885271 := bstep (se 1 (by rfl) ⟨3663953, by rfl⟩ : syracuseStep 4885271 = 7327907) B7327907
theorem B1707227 : Blo 674311 1707227 := bstep (se 1 (by rfl) ⟨1280420, by rfl⟩ : syracuseStep 1707227 = 2560841) B2560841
theorem B1707257 : Blo 674311 1707257 := bstep (se 2 (by rfl) ⟨640221, by rfl⟩ : syracuseStep 1707257 = 1280443) B1280443
theorem B1445215 : Blo 674311 1445215 := bstep (se 1 (by rfl) ⟨1083911, by rfl⟩ : syracuseStep 1445215 = 2167823) B2167823
theorem B9244169 : Blo 674311 9244169 := bstep (se 2 (by rfl) ⟨3466563, by rfl⟩ : syracuseStep 9244169 = 6933127) B6933127
theorem B855623 : Blo 674311 855623 := bstep (se 1 (by rfl) ⟨641717, by rfl⟩ : syracuseStep 855623 = 1283435) B1283435
theorem B10948259 : Blo 674311 10948259 := bstep (se 1 (by rfl) ⟨8211194, by rfl⟩ : syracuseStep 10948259 = 16422389) B16422389
theorem B855775 : Blo 674311 855775 := bstep (se 1 (by rfl) ⟨641831, by rfl⟩ : syracuseStep 855775 = 1283663) B1283663
theorem B23432975 : Blo 674311 23432975 := bstep (se 1 (by rfl) ⟨17574731, by rfl⟩ : syracuseStep 23432975 = 35149463) B35149463
theorem B6590251 : Blo 674311 6590251 := bstep (se 1 (by rfl) ⟨4942688, by rfl⟩ : syracuseStep 6590251 = 9885377) B9885377
theorem B1707905 : Blo 674311 1707905 := bstep (se 2 (by rfl) ⟨640464, by rfl⟩ : syracuseStep 1707905 = 1280929) B1280929
theorem B1708361 : Blo 674311 1708361 := bstep (se 2 (by rfl) ⟨640635, by rfl⟩ : syracuseStep 1708361 = 1281271) B1281271
theorem B1708715 : Blo 674311 1708715 := bstep (se 1 (by rfl) ⟨1281536, by rfl⟩ : syracuseStep 1708715 = 2563073) B2563073
theorem B15602777 : Blo 674311 15602777 := bstep (se 2 (by rfl) ⟨5851041, by rfl⟩ : syracuseStep 15602777 = 11702083) B11702083
theorem B1283215 : Blo 674311 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B4887809 : Blo 674311 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B1283359 : Blo 674311 1283359 := bstep (se 1 (by rfl) ⟨962519, by rfl⟩ : syracuseStep 1283359 = 1925039) B1925039
theorem B759163 : Blo 674311 759163 := bstep (se 1 (by rfl) ⟨569372, by rfl⟩ : syracuseStep 759163 = 1138745) B1138745
theorem B1643899 : Blo 674311 1643899 := bstep (se 1 (by rfl) ⟨1232924, by rfl⟩ : syracuseStep 1643899 = 2465849) B2465849
theorem B1283465 : Blo 674311 1283465 := bstep (se 2 (by rfl) ⟨481299, by rfl⟩ : syracuseStep 1283465 = 962599) B962599
theorem B759631 : Blo 674311 759631 := bstep (se 1 (by rfl) ⟨569723, by rfl⟩ : syracuseStep 759631 = 1139447) B1139447
theorem B1710031 : Blo 674311 1710031 := bstep (se 1 (by rfl) ⟨1282523, by rfl⟩ : syracuseStep 1710031 = 2565047) B2565047
theorem B760027 : Blo 674311 760027 := bstep (se 1 (by rfl) ⟨570020, by rfl⟩ : syracuseStep 760027 = 1140041) B1140041
theorem B2562313 : Blo 674311 2562313 := bstep (se 2 (by rfl) ⟨960867, by rfl⟩ : syracuseStep 2562313 = 1921735) B1921735
theorem B1546607 : Blo 674311 1546607 := bstep (se 1 (by rfl) ⟨1159955, by rfl⟩ : syracuseStep 1546607 = 2319911) B2319911
theorem B760315 : Blo 674311 760315 := bstep (se 1 (by rfl) ⟨570236, by rfl⟩ : syracuseStep 760315 = 1140473) B1140473
theorem B3414635 : Blo 674311 3414635 := bstep (se 1 (by rfl) ⟨2560976, by rfl⟩ : syracuseStep 3414635 = 5121953) B5121953
theorem B760495 : Blo 674311 760495 := bstep (se 1 (by rfl) ⟨570371, by rfl⟩ : syracuseStep 760495 = 1140743) B1140743
theorem B8657603 : Blo 674311 8657603 := bstep (se 1 (by rfl) ⟨6493202, by rfl⟩ : syracuseStep 8657603 = 12986405) B12986405
theorem B1711003 : Blo 674311 1711003 := bstep (se 1 (by rfl) ⟨1283252, by rfl⟩ : syracuseStep 1711003 = 2566505) B2566505
theorem B2890667 : Blo 674311 2890667 := bstep (se 1 (by rfl) ⟨2168000, by rfl⟩ : syracuseStep 2890667 = 4336001) B4336001
theorem B760783 : Blo 674311 760783 := bstep (se 1 (by rfl) ⟨570587, by rfl⟩ : syracuseStep 760783 = 1141175) B1141175
theorem B3415121 : Blo 674311 3415121 := bstep (se 2 (by rfl) ⟨1280670, by rfl⟩ : syracuseStep 3415121 = 2561341) B2561341
theorem B761179 : Blo 674311 761179 := bstep (se 1 (by rfl) ⟨570884, by rfl⟩ : syracuseStep 761179 = 1141769) B1141769
theorem B761287 : Blo 674311 761287 := bstep (se 1 (by rfl) ⟨570965, by rfl⟩ : syracuseStep 761287 = 1141931) B1141931
theorem B1285895 : Blo 674311 1285895 := bstep (se 1 (by rfl) ⟨964421, by rfl⟩ : syracuseStep 1285895 = 1928843) B1928843
theorem B761647 : Blo 674311 761647 := bstep (se 1 (by rfl) ⟨571235, by rfl⟩ : syracuseStep 761647 = 1142471) B1142471
theorem B761755 : Blo 674311 761755 := bstep (se 1 (by rfl) ⟨571316, by rfl⟩ : syracuseStep 761755 = 1142633) B1142633
theorem B1712137 : Blo 674311 1712137 := bstep (se 2 (by rfl) ⟨642051, by rfl⟩ : syracuseStep 1712137 = 1284103) B1284103
theorem B2433235 : Blo 674311 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B762151 : Blo 674311 762151 := bstep (se 1 (by rfl) ⟨571613, by rfl⟩ : syracuseStep 762151 = 1143227) B1143227
theorem B18555227 : Blo 674311 18555227 := bstep (se 1 (by rfl) ⟨13916420, by rfl⟩ : syracuseStep 18555227 = 27832841) B27832841
theorem B762223 : Blo 674311 762223 := bstep (se 1 (by rfl) ⟨571667, by rfl⟩ : syracuseStep 762223 = 1143335) B1143335
theorem B11542985 : Blo 674311 11542985 := bstep (se 2 (by rfl) ⟨4328619, by rfl⟩ : syracuseStep 11542985 = 8657239) B8657239
theorem B2171411 : Blo 674311 2171411 := bstep (se 1 (by rfl) ⟨1628558, by rfl⟩ : syracuseStep 2171411 = 3257117) B3257117
theorem B762439 : Blo 674311 762439 := bstep (se 1 (by rfl) ⟨571829, by rfl⟩ : syracuseStep 762439 = 1143659) B1143659
theorem B2564729 : Blo 674311 2564729 := bstep (se 2 (by rfl) ⟨961773, by rfl⟩ : syracuseStep 2564729 = 1923547) B1923547
theorem B6955703 : Blo 674311 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B4629307 : Blo 674311 4629307 := bstep (se 1 (by rfl) ⟨3471980, by rfl⟩ : syracuseStep 4629307 = 6943961) B6943961
theorem B1156315 : Blo 674311 1156315 := bstep (se 1 (by rfl) ⟨867236, by rfl⟩ : syracuseStep 1156315 = 1734473) B1734473
theorem B1713545 : Blo 674311 1713545 := bstep (se 2 (by rfl) ⟨642579, by rfl⟩ : syracuseStep 1713545 = 1285159) B1285159
theorem B1713595 : Blo 674311 1713595 := bstep (se 1 (by rfl) ⟨1285196, by rfl⟩ : syracuseStep 1713595 = 2570393) B2570393
theorem B3122621 : Blo 674311 3122621 := bstep (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) B1170983
theorem B26060291 : Blo 674311 26060291 := bstep (se 1 (by rfl) ⟨19545218, by rfl⟩ : syracuseStep 26060291 = 39090437) B39090437
theorem B1517291 : Blo 674311 1517291 := bstep (se 1 (by rfl) ⟨1137968, by rfl⟩ : syracuseStep 1517291 = 2275937) B2275937
theorem B1713899 : Blo 674311 1713899 := bstep (se 1 (by rfl) ⟨1285424, by rfl⟩ : syracuseStep 1713899 = 2570849) B2570849
theorem B1517417 : Blo 674311 1517417 := bstep (se 2 (by rfl) ⟨569031, by rfl⟩ : syracuseStep 1517417 = 1138063) B1138063
theorem B731035 : Blo 674311 731035 := bstep (se 1 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 731035 = 1096553) B1096553
theorem B960617 : Blo 674311 960617 := bstep (se 2 (by rfl) ⟨360231, by rfl⟩ : syracuseStep 960617 = 720463) B720463
theorem B3844381 : Blo 674311 3844381 := bstep (se 3 (by rfl) ⟨720821, by rfl⟩ : syracuseStep 3844381 = 1441643) B1441643
theorem B2894291 : Blo 674311 2894291 := bstep (se 1 (by rfl) ⟨2170718, by rfl⟩ : syracuseStep 2894291 = 4341437) B4341437
theorem B14625359 : Blo 674311 14625359 := bstep (se 1 (by rfl) ⟨10969019, by rfl⟩ : syracuseStep 14625359 = 21938039) B21938039
theorem B1518263 : Blo 674311 1518263 := bstep (se 1 (by rfl) ⟨1138697, by rfl⟩ : syracuseStep 1518263 = 2277395) B2277395
theorem B1714871 : Blo 674311 1714871 := bstep (se 1 (by rfl) ⟨1286153, by rfl⟩ : syracuseStep 1714871 = 2572307) B2572307
theorem B4631363 : Blo 674311 4631363 := bstep (se 1 (by rfl) ⟨3473522, by rfl⟩ : syracuseStep 4631363 = 6947045) B6947045
theorem B1518479 : Blo 674311 1518479 := bstep (se 1 (by rfl) ⟨1138859, by rfl⟩ : syracuseStep 1518479 = 2277719) B2277719
theorem B3845339 : Blo 674311 3845339 := bstep (se 1 (by rfl) ⟨2884004, by rfl⟩ : syracuseStep 3845339 = 5768009) B5768009
theorem B10136951 : Blo 674311 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B3419657 : Blo 674311 3419657 := bstep (se 2 (by rfl) ⟨1282371, by rfl⟩ : syracuseStep 3419657 = 2564743) B2564743
theorem B1519199 : Blo 674311 1519199 := bstep (se 1 (by rfl) ⟨1139399, by rfl⟩ : syracuseStep 1519199 = 2278799) B2278799
theorem B1715975 : Blo 674311 1715975 := bstep (se 1 (by rfl) ⟨1286981, by rfl⟩ : syracuseStep 1715975 = 2573963) B2573963
theorem B1519415 : Blo 674311 1519415 := bstep (se 1 (by rfl) ⟨1139561, by rfl⟩ : syracuseStep 1519415 = 2279123) B2279123
theorem B5123897 : Blo 674311 5123897 := bstep (se 2 (by rfl) ⟨1921461, by rfl⟩ : syracuseStep 5123897 = 3842923) B3842923
theorem B1716025 : Blo 674311 1716025 := bstep (se 2 (by rfl) ⟨643509, by rfl⟩ : syracuseStep 1716025 = 1287019) B1287019
theorem B3256193 : Blo 674311 3256193 := bstep (se 2 (by rfl) ⟨1221072, by rfl⟩ : syracuseStep 3256193 = 2442145) B2442145
theorem B5779421 : Blo 674311 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B1519721 : Blo 674311 1519721 := bstep (se 2 (by rfl) ⟨569895, by rfl⟩ : syracuseStep 1519721 = 1139791) B1139791
theorem B1716329 : Blo 674311 1716329 := bstep (se 2 (by rfl) ⟨643623, by rfl⟩ : syracuseStep 1716329 = 1287247) B1287247
theorem B8663597 : Blo 674311 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B1520207 : Blo 674311 1520207 := bstep (se 1 (by rfl) ⟨1140155, by rfl⟩ : syracuseStep 1520207 = 2280311) B2280311
theorem B1716815 : Blo 674311 1716815 := bstep (se 1 (by rfl) ⟨1287611, by rfl⟩ : syracuseStep 1716815 = 2575223) B2575223
theorem B1520351 : Blo 674311 1520351 := bstep (se 1 (by rfl) ⟨1140263, by rfl⟩ : syracuseStep 1520351 = 2280527) B2280527
theorem B5485391 : Blo 674311 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B1520603 : Blo 674311 1520603 := bstep (se 1 (by rfl) ⟨1140452, by rfl⟩ : syracuseStep 1520603 = 2280905) B2280905
theorem B1520783 : Blo 674311 1520783 := bstep (se 1 (by rfl) ⟨1140587, by rfl⟩ : syracuseStep 1520783 = 2281175) B2281175
theorem B1520873 : Blo 674311 1520873 := bstep (se 2 (by rfl) ⟨570327, by rfl⟩ : syracuseStep 1520873 = 1140655) B1140655
theorem B1520927 : Blo 674311 1520927 := bstep (se 1 (by rfl) ⟨1140695, by rfl⟩ : syracuseStep 1520927 = 2281391) B2281391
theorem B2372903 : Blo 674311 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B3421601 : Blo 674311 3421601 := bstep (se 2 (by rfl) ⟨1283100, by rfl⟩ : syracuseStep 3421601 = 2566201) B2566201
theorem B5781131 : Blo 674311 5781131 := bstep (se 1 (by rfl) ⟨4335848, by rfl⟩ : syracuseStep 5781131 = 8671697) B8671697
theorem B1521449 : Blo 674311 1521449 := bstep (se 2 (by rfl) ⟨570543, by rfl⟩ : syracuseStep 1521449 = 1141087) B1141087
theorem B964399 : Blo 674311 964399 := bstep (se 1 (by rfl) ⟨723299, by rfl⟩ : syracuseStep 964399 = 1446599) B1446599
theorem B2570089 : Blo 674311 2570089 := bstep (se 2 (by rfl) ⟨963783, by rfl⟩ : syracuseStep 2570089 = 1927567) B1927567
theorem B3848573 : Blo 674311 3848573 := bstep (se 3 (by rfl) ⟨721607, by rfl⟩ : syracuseStep 3848573 = 1443215) B1443215
theorem B3258767 : Blo 674311 3258767 := bstep (se 1 (by rfl) ⟨2444075, by rfl⟩ : syracuseStep 3258767 = 4888151) B4888151
theorem B965191 : Blo 674311 965191 := bstep (se 1 (by rfl) ⟨723893, by rfl⟩ : syracuseStep 965191 = 1447787) B1447787
theorem B3259075 : Blo 674311 3259075 := bstep (se 1 (by rfl) ⟨2444306, by rfl⟩ : syracuseStep 3259075 = 4888613) B4888613
theorem B2079479 : Blo 674311 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B1522511 : Blo 674311 1522511 := bstep (se 1 (by rfl) ⟨1141883, by rfl⟩ : syracuseStep 1522511 = 2283767) B2283767
theorem B2734991 : Blo 674311 2734991 := bstep (se 1 (by rfl) ⟨2051243, by rfl⟩ : syracuseStep 2734991 = 4102487) B4102487
theorem B16464815 : Blo 674311 16464815 := bstep (se 1 (by rfl) ⟨12348611, by rfl⟩ : syracuseStep 16464815 = 24697223) B24697223
theorem B16694191 : Blo 674311 16694191 := bstep (se 1 (by rfl) ⟨12520643, by rfl⟩ : syracuseStep 16694191 = 25041287) B25041287
theorem B1522727 : Blo 674311 1522727 := bstep (se 1 (by rfl) ⟨1142045, by rfl⟩ : syracuseStep 1522727 = 2284091) B2284091
theorem B1522907 : Blo 674311 1522907 := bstep (se 1 (by rfl) ⟨1142180, by rfl⟩ : syracuseStep 1522907 = 2284361) B2284361
theorem B9747701 : Blo 674311 9747701 := bstep (se 5 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 9747701 = 913847) B913847
theorem B4865291 : Blo 674311 4865291 := bstep (se 1 (by rfl) ⟨3648968, by rfl⟩ : syracuseStep 4865291 = 7297937) B7297937
theorem B2276639 : Blo 674311 2276639 := bstep (se 1 (by rfl) ⟨1707479, by rfl⟩ : syracuseStep 2276639 = 3414959) B3414959
theorem B1523105 : Blo 674311 1523105 := bstep (se 2 (by rfl) ⟨571164, by rfl⟩ : syracuseStep 1523105 = 1142329) B1142329
theorem B6176351 : Blo 674311 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B7520003 : Blo 674311 7520003 := bstep (se 1 (by rfl) ⟨5640002, by rfl⟩ : syracuseStep 7520003 = 11280005) B11280005
theorem B1621889 : Blo 674311 1621889 := bstep (se 2 (by rfl) ⟨608208, by rfl⟩ : syracuseStep 1621889 = 1216417) B1216417
theorem B1523663 : Blo 674311 1523663 := bstep (se 1 (by rfl) ⟨1142747, by rfl⟩ : syracuseStep 1523663 = 2285495) B2285495
theorem B1524041 : Blo 674311 1524041 := bstep (se 2 (by rfl) ⟨571515, by rfl⟩ : syracuseStep 1524041 = 1143031) B1143031
theorem B1524059 : Blo 674311 1524059 := bstep (se 1 (by rfl) ⟨1143044, by rfl⟩ : syracuseStep 1524059 = 2286089) B2286089
theorem B13877669 : Blo 674311 13877669 := bstep (se 4 (by rfl) ⟨1301031, by rfl⟩ : syracuseStep 13877669 = 2602063) B2602063
theorem B25051949 : Blo 674311 25051949 := bstep (se 3 (by rfl) ⟨4697240, by rfl⟩ : syracuseStep 25051949 = 9394481) B9394481
theorem B1524635 : Blo 674311 1524635 := bstep (se 1 (by rfl) ⟨1143476, by rfl⟩ : syracuseStep 1524635 = 2286953) B2286953
theorem B1623079 : Blo 674311 1623079 := bstep (se 1 (by rfl) ⟨1217309, by rfl⟩ : syracuseStep 1623079 = 2434619) B2434619
theorem B1524833 : Blo 674311 1524833 := bstep (se 2 (by rfl) ⟨571812, by rfl⟩ : syracuseStep 1524833 = 1143625) B1143625
theorem B1525031 : Blo 674311 1525031 := bstep (se 1 (by rfl) ⟨1143773, by rfl⟩ : syracuseStep 1525031 = 2287547) B2287547
theorem B13157741 : Blo 674311 13157741 := bstep (se 3 (by rfl) ⟨2467076, by rfl⟩ : syracuseStep 13157741 = 4934153) B4934153
theorem B2279069 : Blo 674311 2279069 := bstep (se 3 (by rfl) ⟨427325, by rfl⟩ : syracuseStep 2279069 = 854651) B854651
theorem B1525409 : Blo 674311 1525409 := bstep (se 2 (by rfl) ⟨572028, by rfl⟩ : syracuseStep 1525409 = 1144057) B1144057
theorem B1525769 : Blo 674311 1525769 := bstep (se 2 (by rfl) ⟨572163, by rfl⟩ : syracuseStep 1525769 = 1144327) B1144327
theorem B5851217 : Blo 674311 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B2279609 : Blo 674311 2279609 := bstep (se 2 (by rfl) ⟨854853, by rfl⟩ : syracuseStep 2279609 = 1709707) B1709707
theorem B26364149 : Blo 674311 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B2443529 : Blo 674311 2443529 := bstep (se 2 (by rfl) ⟨916323, by rfl⟩ : syracuseStep 2443529 = 1832647) B1832647
theorem B4344101 : Blo 674311 4344101 := bstep (se 4 (by rfl) ⟨407259, by rfl⟩ : syracuseStep 4344101 = 814519) B814519
theorem B1526183 : Blo 674311 1526183 := bstep (se 1 (by rfl) ⟨1144637, by rfl⟩ : syracuseStep 1526183 = 2289275) B2289275
theorem B1624531 : Blo 674311 1624531 := bstep (se 1 (by rfl) ⟨1218398, by rfl⟩ : syracuseStep 1624531 = 2436797) B2436797
theorem B674367 : Blo 674311 674367 := bstep (se 1 (by rfl) ⟨505775, by rfl⟩ : syracuseStep 674367 = 1011551) B1011551
theorem B674375 : Blo 674311 674375 := bstep (se 1 (by rfl) ⟨505781, by rfl⟩ : syracuseStep 674375 = 1011563) B1011563
theorem B3656299 : Blo 674311 3656299 := bstep (se 1 (by rfl) ⟨2742224, by rfl⟩ : syracuseStep 3656299 = 5484449) B5484449
theorem B674527 : Blo 674311 674527 := bstep (se 1 (by rfl) ⟨505895, by rfl⟩ : syracuseStep 674527 = 1011791) B1011791
theorem B674607 : Blo 674311 674607 := bstep (se 1 (by rfl) ⟨505955, by rfl⟩ : syracuseStep 674607 = 1011911) B1011911
theorem B674715 : Blo 674311 674715 := bstep (se 1 (by rfl) ⟨506036, by rfl⟩ : syracuseStep 674715 = 1012073) B1012073
theorem B674767 : Blo 674311 674767 := bstep (se 1 (by rfl) ⟨506075, by rfl⟩ : syracuseStep 674767 = 1012151) B1012151
theorem B674791 : Blo 674311 674791 := bstep (se 1 (by rfl) ⟨506093, by rfl⟩ : syracuseStep 674791 = 1012187) B1012187
theorem B3427595 : Blo 674311 3427595 := bstep (se 1 (by rfl) ⟨2570696, by rfl⟩ : syracuseStep 3427595 = 5141393) B5141393
theorem B675103 : Blo 674311 675103 := bstep (se 1 (by rfl) ⟨506327, by rfl⟩ : syracuseStep 675103 = 1012655) B1012655
theorem B675163 : Blo 674311 675163 := bstep (se 1 (by rfl) ⟨506372, by rfl⟩ : syracuseStep 675163 = 1012745) B1012745
theorem B675183 : Blo 674311 675183 := bstep (se 1 (by rfl) ⟨506387, by rfl⟩ : syracuseStep 675183 = 1012775) B1012775
theorem B1625483 : Blo 674311 1625483 := bstep (se 1 (by rfl) ⟨1219112, by rfl⟩ : syracuseStep 1625483 = 2438225) B2438225
theorem B675239 : Blo 674311 675239 := bstep (se 1 (by rfl) ⟨506429, by rfl⟩ : syracuseStep 675239 = 1012859) B1012859
theorem B1920505 : Blo 674311 1920505 := bstep (se 2 (by rfl) ⟨720189, by rfl⟩ : syracuseStep 1920505 = 1440379) B1440379
theorem B675323 : Blo 674311 675323 := bstep (se 1 (by rfl) ⟨506492, by rfl⟩ : syracuseStep 675323 = 1012985) B1012985
theorem B675391 : Blo 674311 675391 := bstep (se 1 (by rfl) ⟨506543, by rfl⟩ : syracuseStep 675391 = 1013087) B1013087
theorem B675399 : Blo 674311 675399 := bstep (se 1 (by rfl) ⟨506549, by rfl⟩ : syracuseStep 675399 = 1013099) B1013099
theorem B2281121 : Blo 674311 2281121 := bstep (se 2 (by rfl) ⟨855420, by rfl⟩ : syracuseStep 2281121 = 1710841) B1710841
theorem B1625761 : Blo 674311 1625761 := bstep (se 2 (by rfl) ⟨609660, by rfl⟩ : syracuseStep 1625761 = 1219321) B1219321
theorem B675551 : Blo 674311 675551 := bstep (se 1 (by rfl) ⟨506663, by rfl⟩ : syracuseStep 675551 = 1013327) B1013327
theorem B675631 : Blo 674311 675631 := bstep (se 1 (by rfl) ⟨506723, by rfl⟩ : syracuseStep 675631 = 1013447) B1013447
theorem B675739 : Blo 674311 675739 := bstep (se 1 (by rfl) ⟨506804, by rfl⟩ : syracuseStep 675739 = 1013609) B1013609
theorem B675791 : Blo 674311 675791 := bstep (se 1 (by rfl) ⟨506843, by rfl⟩ : syracuseStep 675791 = 1013687) B1013687
theorem B675815 : Blo 674311 675815 := bstep (se 1 (by rfl) ⟨506861, by rfl⟩ : syracuseStep 675815 = 1013723) B1013723
theorem B676127 : Blo 674311 676127 := bstep (se 1 (by rfl) ⟨507095, by rfl⟩ : syracuseStep 676127 = 1014191) B1014191
theorem B676187 : Blo 674311 676187 := bstep (se 1 (by rfl) ⟨507140, by rfl⟩ : syracuseStep 676187 = 1014281) B1014281
theorem B676207 : Blo 674311 676207 := bstep (se 1 (by rfl) ⟨507155, by rfl⟩ : syracuseStep 676207 = 1014311) B1014311
theorem B676263 : Blo 674311 676263 := bstep (se 1 (by rfl) ⟨507197, by rfl⟩ : syracuseStep 676263 = 1014395) B1014395
theorem B676347 : Blo 674311 676347 := bstep (se 1 (by rfl) ⟨507260, by rfl⟩ : syracuseStep 676347 = 1014521) B1014521
theorem B2281985 : Blo 674311 2281985 := bstep (se 2 (by rfl) ⟨855744, by rfl⟩ : syracuseStep 2281985 = 1711489) B1711489
theorem B676415 : Blo 674311 676415 := bstep (se 1 (by rfl) ⟨507311, by rfl⟩ : syracuseStep 676415 = 1014623) B1014623
theorem B676423 : Blo 674311 676423 := bstep (se 1 (by rfl) ⟨507317, by rfl⟩ : syracuseStep 676423 = 1014635) B1014635
theorem B1823305 : Blo 674311 1823305 := bstep (se 2 (by rfl) ⟨683739, by rfl⟩ : syracuseStep 1823305 = 1367479) B1367479
theorem B676575 : Blo 674311 676575 := bstep (se 1 (by rfl) ⟨507431, by rfl⟩ : syracuseStep 676575 = 1014863) B1014863
theorem B676655 : Blo 674311 676655 := bstep (se 1 (by rfl) ⟨507491, by rfl⟩ : syracuseStep 676655 = 1014983) B1014983
theorem B3429215 : Blo 674311 3429215 := bstep (se 1 (by rfl) ⟨2571911, by rfl⟩ : syracuseStep 3429215 = 5143823) B5143823
theorem B676763 : Blo 674311 676763 := bstep (se 1 (by rfl) ⟨507572, by rfl⟩ : syracuseStep 676763 = 1015145) B1015145
theorem B676815 : Blo 674311 676815 := bstep (se 1 (by rfl) ⟨507611, by rfl⟩ : syracuseStep 676815 = 1015223) B1015223
theorem B2282471 : Blo 674311 2282471 := bstep (se 1 (by rfl) ⟨1711853, by rfl⟩ : syracuseStep 2282471 = 3423707) B3423707
theorem B676839 : Blo 674311 676839 := bstep (se 1 (by rfl) ⟨507629, by rfl⟩ : syracuseStep 676839 = 1015259) B1015259
theorem B677151 : Blo 674311 677151 := bstep (se 1 (by rfl) ⟨507863, by rfl⟩ : syracuseStep 677151 = 1015727) B1015727
theorem B2282795 : Blo 674311 2282795 := bstep (se 1 (by rfl) ⟨1712096, by rfl⟩ : syracuseStep 2282795 = 3424193) B3424193
theorem B677211 : Blo 674311 677211 := bstep (se 1 (by rfl) ⟨507908, by rfl⟩ : syracuseStep 677211 = 1015817) B1015817
theorem B677231 : Blo 674311 677231 := bstep (se 1 (by rfl) ⟨507923, by rfl⟩ : syracuseStep 677231 = 1015847) B1015847
theorem B677287 : Blo 674311 677287 := bstep (se 1 (by rfl) ⟨507965, by rfl⟩ : syracuseStep 677287 = 1015931) B1015931
theorem B1627607 : Blo 674311 1627607 := bstep (se 1 (by rfl) ⟨1220705, by rfl⟩ : syracuseStep 1627607 = 2441411) B2441411
theorem B677371 : Blo 674311 677371 := bstep (se 1 (by rfl) ⟨508028, by rfl⟩ : syracuseStep 677371 = 1016057) B1016057
theorem B7296551 : Blo 674311 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B9754157 : Blo 674311 9754157 := bstep (se 3 (by rfl) ⟨1828904, by rfl⟩ : syracuseStep 9754157 = 3657809) B3657809
theorem B2283065 : Blo 674311 2283065 := bstep (se 2 (by rfl) ⟨856149, by rfl⟩ : syracuseStep 2283065 = 1712299) B1712299
theorem B677439 : Blo 674311 677439 := bstep (se 1 (by rfl) ⟨508079, by rfl⟩ : syracuseStep 677439 = 1016159) B1016159
theorem B677447 : Blo 674311 677447 := bstep (se 1 (by rfl) ⟨508085, by rfl⟩ : syracuseStep 677447 = 1016171) B1016171
theorem B677599 : Blo 674311 677599 := bstep (se 1 (by rfl) ⟨508199, by rfl⟩ : syracuseStep 677599 = 1016399) B1016399
theorem B677679 : Blo 674311 677679 := bstep (se 1 (by rfl) ⟨508259, by rfl⟩ : syracuseStep 677679 = 1016519) B1016519
theorem B677787 : Blo 674311 677787 := bstep (se 1 (by rfl) ⟨508340, by rfl⟩ : syracuseStep 677787 = 1016681) B1016681
theorem B677839 : Blo 674311 677839 := bstep (se 1 (by rfl) ⟨508379, by rfl⟩ : syracuseStep 677839 = 1016759) B1016759
theorem B677863 : Blo 674311 677863 := bstep (se 1 (by rfl) ⟨508397, by rfl⟩ : syracuseStep 677863 = 1016795) B1016795
theorem B678175 : Blo 674311 678175 := bstep (se 1 (by rfl) ⟨508631, by rfl⟩ : syracuseStep 678175 = 1017263) B1017263
theorem B678235 : Blo 674311 678235 := bstep (se 1 (by rfl) ⟨508676, by rfl⟩ : syracuseStep 678235 = 1017353) B1017353
theorem B678255 : Blo 674311 678255 := bstep (se 1 (by rfl) ⟨508691, by rfl⟩ : syracuseStep 678255 = 1017383) B1017383
theorem B678311 : Blo 674311 678311 := bstep (se 1 (by rfl) ⟨508733, by rfl⟩ : syracuseStep 678311 = 1017467) B1017467
theorem B3857003 : Blo 674311 3857003 := bstep (se 1 (by rfl) ⟨2892752, by rfl⟩ : syracuseStep 3857003 = 5785505) B5785505
theorem B6576815 : Blo 674311 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B3431159 : Blo 674311 3431159 := bstep (se 1 (by rfl) ⟨2573369, by rfl⟩ : syracuseStep 3431159 = 5146739) B5146739
theorem B2284307 : Blo 674311 2284307 := bstep (se 1 (by rfl) ⟨1713230, by rfl⟩ : syracuseStep 2284307 = 3426461) B3426461
theorem B3300115 : Blo 674311 3300115 := bstep (se 1 (by rfl) ⟨2475086, by rfl⟩ : syracuseStep 3300115 = 4950173) B4950173
theorem B3660731 : Blo 674311 3660731 := bstep (se 1 (by rfl) ⟨2745548, by rfl⟩ : syracuseStep 3660731 = 5491097) B5491097
theorem B2776051 : Blo 674311 2776051 := bstep (se 1 (by rfl) ⟨2082038, by rfl⟩ : syracuseStep 2776051 = 4164077) B4164077
theorem B2317501 : Blo 674311 2317501 := bstep (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) B869063
theorem B3431645 : Blo 674311 3431645 := bstep (se 3 (by rfl) ⟨643433, by rfl⟩ : syracuseStep 3431645 = 1286867) B1286867
theorem B810271 : Blo 674311 810271 := bstep (se 1 (by rfl) ⟨607703, by rfl⟩ : syracuseStep 810271 = 1215407) B1215407
theorem B1138043 : Blo 674311 1138043 := bstep (se 1 (by rfl) ⟨853532, by rfl⟩ : syracuseStep 1138043 = 1707065) B1707065
theorem B3661271 : Blo 674311 3661271 := bstep (se 1 (by rfl) ⟨2745953, by rfl⟩ : syracuseStep 3661271 = 5491907) B5491907
theorem B2285171 : Blo 674311 2285171 := bstep (se 1 (by rfl) ⟨1713878, by rfl⟩ : syracuseStep 2285171 = 3427757) B3427757
theorem B3661615 : Blo 674311 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B1957679 : Blo 674311 1957679 := bstep (se 1 (by rfl) ⟨1468259, by rfl⟩ : syracuseStep 1957679 = 2936519) B2936519
theorem B2285441 : Blo 674311 2285441 := bstep (se 2 (by rfl) ⟨857040, by rfl⟩ : syracuseStep 2285441 = 1714081) B1714081
theorem B7692407 : Blo 674311 7692407 := bstep (se 1 (by rfl) ⟨5769305, by rfl⟩ : syracuseStep 7692407 = 11538611) B11538611
theorem B1139035 : Blo 674311 1139035 := bstep (se 1 (by rfl) ⟨854276, by rfl⟩ : syracuseStep 1139035 = 1708553) B1708553
theorem B3858779 : Blo 674311 3858779 := bstep (se 1 (by rfl) ⟨2894084, by rfl⟩ : syracuseStep 3858779 = 5788169) B5788169
theorem B6152705 : Blo 674311 6152705 := bstep (se 2 (by rfl) ⟨2307264, by rfl⟩ : syracuseStep 6152705 = 4614529) B4614529
theorem B2286251 : Blo 674311 2286251 := bstep (se 1 (by rfl) ⟨1714688, by rfl⟩ : syracuseStep 2286251 = 3429377) B3429377
theorem B5137505 : Blo 674311 5137505 := bstep (se 2 (by rfl) ⟨1926564, by rfl⟩ : syracuseStep 5137505 = 3853129) B3853129
theorem B2286791 : Blo 674311 2286791 := bstep (se 1 (by rfl) ⟨1715093, by rfl⟩ : syracuseStep 2286791 = 3430187) B3430187
theorem B1828127 : Blo 674311 1828127 := bstep (se 1 (by rfl) ⟨1371095, by rfl⟩ : syracuseStep 1828127 = 2742191) B2742191
theorem B1140007 : Blo 674311 1140007 := bstep (se 1 (by rfl) ⟨855005, by rfl⟩ : syracuseStep 1140007 = 1710011) B1710011
theorem B3302765 : Blo 674311 3302765 := bstep (se 3 (by rfl) ⟨619268, by rfl⟩ : syracuseStep 3302765 = 1238537) B1238537
theorem B32826869 : Blo 674311 32826869 := bstep (se 5 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 32826869 = 3077519) B3077519
theorem B13330007 : Blo 674311 13330007 := bstep (se 1 (by rfl) ⟨9997505, by rfl⟩ : syracuseStep 13330007 = 19995011) B19995011
theorem B1140527 : Blo 674311 1140527 := bstep (se 1 (by rfl) ⟨855395, by rfl⟩ : syracuseStep 1140527 = 1710791) B1710791
theorem B4941751 : Blo 674311 4941751 := bstep (se 1 (by rfl) ⟨3706313, by rfl⟩ : syracuseStep 4941751 = 7412627) B7412627
theorem B3565601 : Blo 674311 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B1828993 : Blo 674311 1828993 := bstep (se 2 (by rfl) ⟨685872, by rfl⟩ : syracuseStep 1828993 = 1371745) B1371745
theorem B911783 : Blo 674311 911783 := bstep (se 1 (by rfl) ⟨683837, by rfl⟩ : syracuseStep 911783 = 1367675) B1367675
theorem B2288303 : Blo 674311 2288303 := bstep (se 1 (by rfl) ⟨1716227, by rfl⟩ : syracuseStep 2288303 = 3432455) B3432455
theorem B1927955 : Blo 674311 1927955 := bstep (se 1 (by rfl) ⟨1445966, by rfl⟩ : syracuseStep 1927955 = 2891933) B2891933
theorem B1141735 : Blo 674311 1141735 := bstep (se 1 (by rfl) ⟨856301, by rfl⟩ : syracuseStep 1141735 = 1712603) B1712603
theorem B2288627 : Blo 674311 2288627 := bstep (se 1 (by rfl) ⟨1716470, by rfl⟩ : syracuseStep 2288627 = 3432941) B3432941
theorem B1829879 : Blo 674311 1829879 := bstep (se 1 (by rfl) ⟨1372409, by rfl⟩ : syracuseStep 1829879 = 2744819) B2744819
theorem B1928411 : Blo 674311 1928411 := bstep (se 1 (by rfl) ⟨1446308, by rfl⟩ : syracuseStep 1928411 = 2892617) B2892617
theorem B2289167 : Blo 674311 2289167 := bstep (se 1 (by rfl) ⟨1716875, by rfl⟩ : syracuseStep 2289167 = 3433751) B3433751
theorem B1011497 : Blo 674311 1011497 := bstep (se 2 (by rfl) ⟨379311, by rfl⟩ : syracuseStep 1011497 = 758623) B758623
theorem B1011503 : Blo 674311 1011503 := bstep (se 1 (by rfl) ⟨758627, by rfl⟩ : syracuseStep 1011503 = 1517255) B1517255
theorem B2748289 : Blo 674311 2748289 := bstep (se 2 (by rfl) ⟨1030608, by rfl⟩ : syracuseStep 2748289 = 2061217) B2061217
theorem B11726801 : Blo 674311 11726801 := bstep (se 2 (by rfl) ⟨4397550, by rfl⟩ : syracuseStep 11726801 = 8795101) B8795101
theorem B684007 : Blo 674311 684007 := bstep (se 1 (by rfl) ⟨513005, by rfl⟩ : syracuseStep 684007 = 1026011) B1026011
theorem B913513 : Blo 674311 913513 := bstep (se 2 (by rfl) ⟨342567, by rfl⟩ : syracuseStep 913513 = 685135) B685135
theorem B1011977 : Blo 674311 1011977 := bstep (se 2 (by rfl) ⟨379491, by rfl⟩ : syracuseStep 1011977 = 758983) B758983
theorem B1012079 : Blo 674311 1012079 := bstep (se 1 (by rfl) ⟨759059, by rfl⟩ : syracuseStep 1012079 = 1518119) B1518119
theorem B5763635 : Blo 674311 5763635 := bstep (se 1 (by rfl) ⟨4322726, by rfl⟩ : syracuseStep 5763635 = 8645453) B8645453
theorem B1012295 : Blo 674311 1012295 := bstep (se 1 (by rfl) ⟨759221, by rfl⟩ : syracuseStep 1012295 = 1518443) B1518443
theorem B1012331 : Blo 674311 1012331 := bstep (se 1 (by rfl) ⟨759248, by rfl⟩ : syracuseStep 1012331 = 1518497) B1518497
theorem B1012559 : Blo 674311 1012559 := bstep (se 1 (by rfl) ⟨759419, by rfl⟩ : syracuseStep 1012559 = 1518839) B1518839
theorem B3077065 : Blo 674311 3077065 := bstep (se 2 (by rfl) ⟨1153899, by rfl⟩ : syracuseStep 3077065 = 2307799) B2307799
theorem B1733671 : Blo 674311 1733671 := bstep (se 1 (by rfl) ⟨1300253, by rfl⟩ : syracuseStep 1733671 = 2600507) B2600507
theorem B1012955 : Blo 674311 1012955 := bstep (se 1 (by rfl) ⟨759716, by rfl⟩ : syracuseStep 1012955 = 1519433) B1519433
theorem B1930483 : Blo 674311 1930483 := bstep (se 1 (by rfl) ⟨1447862, by rfl⟩ : syracuseStep 1930483 = 2895725) B2895725
theorem B2061607 : Blo 674311 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B1013129 : Blo 674311 1013129 := bstep (se 2 (by rfl) ⟨379923, by rfl⟩ : syracuseStep 1013129 = 759847) B759847
theorem B3241529 : Blo 674311 3241529 := bstep (se 2 (by rfl) ⟨1215573, by rfl⟩ : syracuseStep 3241529 = 2431147) B2431147
theorem B1144415 : Blo 674311 1144415 := bstep (se 1 (by rfl) ⟨858311, by rfl⟩ : syracuseStep 1144415 = 1716623) B1716623
theorem B1013483 : Blo 674311 1013483 := bstep (se 1 (by rfl) ⟨760112, by rfl⟩ : syracuseStep 1013483 = 1520225) B1520225
theorem B11564855 : Blo 674311 11564855 := bstep (se 1 (by rfl) ⟨8673641, by rfl⟩ : syracuseStep 11564855 = 17347283) B17347283
theorem B1144631 : Blo 674311 1144631 := bstep (se 1 (by rfl) ⟨858473, by rfl⟩ : syracuseStep 1144631 = 1716947) B1716947
theorem B1013711 : Blo 674311 1013711 := bstep (se 1 (by rfl) ⟨760283, by rfl⟩ : syracuseStep 1013711 = 1520567) B1520567
theorem B7829837 : Blo 674311 7829837 := bstep (se 3 (by rfl) ⟨1468094, by rfl⟩ : syracuseStep 7829837 = 2936189) B2936189
theorem B1014107 : Blo 674311 1014107 := bstep (se 1 (by rfl) ⟨760580, by rfl⟩ : syracuseStep 1014107 = 1521161) B1521161
theorem B6486551 : Blo 674311 6486551 := bstep (se 1 (by rfl) ⟨4864913, by rfl⟩ : syracuseStep 6486551 = 9729827) B9729827
theorem B1014335 : Blo 674311 1014335 := bstep (se 1 (by rfl) ⟨760751, by rfl⟩ : syracuseStep 1014335 = 1521503) B1521503
theorem B6158987 : Blo 674311 6158987 := bstep (se 1 (by rfl) ⟨4619240, by rfl⟩ : syracuseStep 6158987 = 9238481) B9238481
theorem B1014455 : Blo 674311 1014455 := bstep (se 1 (by rfl) ⟨760841, by rfl⟩ : syracuseStep 1014455 = 1521683) B1521683
theorem B3701629 : Blo 674311 3701629 := bstep (se 3 (by rfl) ⟨694055, by rfl⟩ : syracuseStep 3701629 = 1388111) B1388111
theorem B1014683 : Blo 674311 1014683 := bstep (se 1 (by rfl) ⟨761012, by rfl⟩ : syracuseStep 1014683 = 1522025) B1522025
theorem B1015079 : Blo 674311 1015079 := bstep (se 1 (by rfl) ⟨761309, by rfl⟩ : syracuseStep 1015079 = 1522619) B1522619
theorem B1015163 : Blo 674311 1015163 := bstep (se 1 (by rfl) ⟨761372, by rfl⟩ : syracuseStep 1015163 = 1522745) B1522745
theorem B2882945 : Blo 674311 2882945 := bstep (se 2 (by rfl) ⟨1081104, by rfl⟩ : syracuseStep 2882945 = 2162209) B2162209
theorem B1015289 : Blo 674311 1015289 := bstep (se 2 (by rfl) ⟨380733, by rfl⟩ : syracuseStep 1015289 = 761467) B761467
theorem B9272843 : Blo 674311 9272843 := bstep (se 1 (by rfl) ⟨6954632, by rfl⟩ : syracuseStep 9272843 = 13909265) B13909265
theorem B37092923 : Blo 674311 37092923 := bstep (se 1 (by rfl) ⟨27819692, by rfl⟩ : syracuseStep 37092923 = 55639385) B55639385
theorem B3898961 : Blo 674311 3898961 := bstep (se 2 (by rfl) ⟨1462110, by rfl⟩ : syracuseStep 3898961 = 2924221) B2924221
theorem B1015391 : Blo 674311 1015391 := bstep (se 1 (by rfl) ⟨761543, by rfl⟩ : syracuseStep 1015391 = 1523087) B1523087
theorem B24641171 : Blo 674311 24641171 := bstep (se 1 (by rfl) ⟨18480878, by rfl⟩ : syracuseStep 24641171 = 36961757) B36961757
theorem B1015607 : Blo 674311 1015607 := bstep (se 1 (by rfl) ⟨761705, by rfl⟩ : syracuseStep 1015607 = 1523411) B1523411
theorem B1016027 : Blo 674311 1016027 := bstep (se 1 (by rfl) ⟨762020, by rfl⟩ : syracuseStep 1016027 = 1524041) B1524041
theorem B1016039 : Blo 674311 1016039 := bstep (se 1 (by rfl) ⟨762029, by rfl⟩ : syracuseStep 1016039 = 1524059) B1524059
theorem B3244313 : Blo 674311 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B1016201 : Blo 674311 1016201 := bstep (se 2 (by rfl) ⟨381075, by rfl⟩ : syracuseStep 1016201 = 762151) B762151
theorem B1016297 : Blo 674311 1016297 := bstep (se 2 (by rfl) ⟨381111, by rfl⟩ : syracuseStep 1016297 = 762223) B762223
theorem B1016423 : Blo 674311 1016423 := bstep (se 1 (by rfl) ⟨762317, by rfl⟩ : syracuseStep 1016423 = 1524635) B1524635
theorem B1016555 : Blo 674311 1016555 := bstep (se 1 (by rfl) ⟨762416, by rfl⟩ : syracuseStep 1016555 = 1524833) B1524833
theorem B1016585 : Blo 674311 1016585 := bstep (se 2 (by rfl) ⟨381219, by rfl⟩ : syracuseStep 1016585 = 762439) B762439
theorem B1016687 : Blo 674311 1016687 := bstep (se 1 (by rfl) ⟨762515, by rfl⟩ : syracuseStep 1016687 = 1525031) B1525031
theorem B721915 : Blo 674311 721915 := bstep (se 1 (by rfl) ⟨541436, by rfl⟩ : syracuseStep 721915 = 1082873) B1082873
theorem B1016939 : Blo 674311 1016939 := bstep (se 1 (by rfl) ⟨762704, by rfl⟩ : syracuseStep 1016939 = 1525409) B1525409
theorem B1017179 : Blo 674311 1017179 := bstep (se 1 (by rfl) ⟨762884, by rfl⟩ : syracuseStep 1017179 = 1525769) B1525769
theorem B2164105 : Blo 674311 2164105 := bstep (se 2 (by rfl) ⟨811539, by rfl⟩ : syracuseStep 2164105 = 1623079) B1623079
theorem B3900811 : Blo 674311 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B1017455 : Blo 674311 1017455 := bstep (se 1 (by rfl) ⟨763091, by rfl⟩ : syracuseStep 1017455 = 1526183) B1526183
theorem B1541753 : Blo 674311 1541753 := bstep (se 2 (by rfl) ⟨578157, by rfl⟩ : syracuseStep 1541753 = 1156315) B1156315
theorem B1083655 : Blo 674311 1083655 := bstep (se 1 (by rfl) ⟨812741, by rfl⟩ : syracuseStep 1083655 = 1625483) B1625483
theorem B6162779 : Blo 674311 6162779 := bstep (se 1 (by rfl) ⟨4622084, by rfl⟩ : syracuseStep 6162779 = 9244169) B9244169
theorem B6589001 : Blo 674311 6589001 := bstep (se 2 (by rfl) ⟨2470875, by rfl⟩ : syracuseStep 6589001 = 4941751) B4941751
theorem B2166041 : Blo 674311 2166041 := bstep (se 2 (by rfl) ⟨812265, by rfl⟩ : syracuseStep 2166041 = 1624531) B1624531
theorem B1085071 : Blo 674311 1085071 := bstep (se 1 (by rfl) ⟨813803, by rfl⟩ : syracuseStep 1085071 = 1627607) B1627607
theorem B5771735 : Blo 674311 5771735 := bstep (se 1 (by rfl) ⟨4328801, by rfl⟩ : syracuseStep 5771735 = 8657603) B8657603
theorem B2560673 : Blo 674311 2560673 := bstep (se 2 (by rfl) ⟨960252, by rfl⟩ : syracuseStep 2560673 = 1920505) B1920505
theorem B758695 : Blo 674311 758695 := bstep (se 1 (by rfl) ⟨569021, by rfl⟩ : syracuseStep 758695 = 1138043) B1138043
theorem B8787001 : Blo 674311 8787001 := bstep (se 2 (by rfl) ⟨3295125, by rfl⟩ : syracuseStep 8787001 = 6590251) B6590251
theorem B1218017 : Blo 674311 1218017 := bstep (se 2 (by rfl) ⟨456756, by rfl⟩ : syracuseStep 1218017 = 913513) B913513
theorem B2561645 : Blo 674311 2561645 := bstep (se 3 (by rfl) ⟨480308, by rfl⟩ : syracuseStep 2561645 = 960617) B960617
theorem B4101803 : Blo 674311 4101803 := bstep (se 1 (by rfl) ⟨3076352, by rfl⟩ : syracuseStep 4101803 = 6152705) B6152705
theorem B1447607 : Blo 674311 1447607 := bstep (se 1 (by rfl) ⟨1085705, by rfl⟩ : syracuseStep 1447607 = 2171411) B2171411
theorem B1709819 : Blo 674311 1709819 := bstep (se 1 (by rfl) ⟨1282364, by rfl⟩ : syracuseStep 1709819 = 2564729) B2564729
theorem B2431073 : Blo 674311 2431073 := bstep (se 2 (by rfl) ⟨911652, by rfl⟩ : syracuseStep 2431073 = 1823305) B1823305
theorem B2201843 : Blo 674311 2201843 := bstep (se 1 (by rfl) ⟨1651382, by rfl⟩ : syracuseStep 2201843 = 3302765) B3302765
theorem B17373527 : Blo 674311 17373527 := bstep (se 1 (by rfl) ⟨13030145, by rfl⟩ : syracuseStep 17373527 = 26060291) B26060291
theorem B8886671 : Blo 674311 8886671 := bstep (se 1 (by rfl) ⟨6665003, by rfl⟩ : syracuseStep 8886671 = 13330007) B13330007
theorem B2431421 : Blo 674311 2431421 := bstep (se 3 (by rfl) ⟨455891, by rfl⟩ : syracuseStep 2431421 = 911783) B911783
theorem B760351 : Blo 674311 760351 := bstep (se 1 (by rfl) ⟨570263, by rfl⟩ : syracuseStep 760351 = 1140527) B1140527
theorem B4102753 : Blo 674311 4102753 := bstep (se 2 (by rfl) ⟨1538532, by rfl⟩ : syracuseStep 4102753 = 3077065) B3077065
theorem B1710953 : Blo 674311 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B1711145 : Blo 674311 1711145 := bstep (se 2 (by rfl) ⟨641679, by rfl⟩ : syracuseStep 1711145 = 1283359) B1283359
theorem B1285303 : Blo 674311 1285303 := bstep (se 1 (by rfl) ⟨963977, by rfl⟩ : syracuseStep 1285303 = 1927955) B1927955
theorem B3087575 : Blo 674311 3087575 := bstep (se 1 (by rfl) ⟨2315681, by rfl⟩ : syracuseStep 3087575 = 4631363) B4631363
theorem B1219919 : Blo 674311 1219919 := bstep (se 1 (by rfl) ⟨914939, by rfl⟩ : syracuseStep 1219919 = 1829879) B1829879
theorem B2563559 : Blo 674311 2563559 := bstep (se 1 (by rfl) ⟨1922669, by rfl⟩ : syracuseStep 2563559 = 3845339) B3845339
theorem B1285607 : Blo 674311 1285607 := bstep (se 1 (by rfl) ⟨964205, by rfl⟩ : syracuseStep 1285607 = 1928411) B1928411
theorem B6757967 : Blo 674311 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B1285865 : Blo 674311 1285865 := bstep (se 2 (by rfl) ⟨482199, by rfl⟩ : syracuseStep 1285865 = 964399) B964399
theorem B7708445 : Blo 674311 7708445 := bstep (se 3 (by rfl) ⟨1445333, by rfl⟩ : syracuseStep 7708445 = 2890667) B2890667
theorem B3415931 : Blo 674311 3415931 := bstep (se 1 (by rfl) ⟨2561948, by rfl⟩ : syracuseStep 3415931 = 5123897) B5123897
theorem B2170795 : Blo 674311 2170795 := bstep (se 1 (by rfl) ⟨1628096, by rfl⟩ : syracuseStep 2170795 = 3256193) B3256193
theorem B3416417 : Blo 674311 3416417 := bstep (se 2 (by rfl) ⟨1281156, by rfl⟩ : syracuseStep 3416417 = 2562313) B2562313
theorem B5775731 : Blo 674311 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B3842423 : Blo 674311 3842423 := bstep (se 1 (by rfl) ⟨2881817, by rfl⟩ : syracuseStep 3842423 = 5763635) B5763635
theorem B1286921 : Blo 674311 1286921 := bstep (se 2 (by rfl) ⟨482595, by rfl⟩ : syracuseStep 1286921 = 965191) B965191
theorem B1581935 : Blo 674311 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B4400153 : Blo 674311 4400153 := bstep (se 2 (by rfl) ⟨1650057, by rfl⟩ : syracuseStep 4400153 = 3300115) B3300115
theorem B762943 : Blo 674311 762943 := bstep (se 1 (by rfl) ⟨572207, by rfl⟩ : syracuseStep 762943 = 1144415) B1144415
theorem B7709903 : Blo 674311 7709903 := bstep (se 1 (by rfl) ⟨5782427, by rfl⟩ : syracuseStep 7709903 = 11564855) B11564855
theorem B763087 : Blo 674311 763087 := bstep (se 1 (by rfl) ⟨572315, by rfl⟩ : syracuseStep 763087 = 1144631) B1144631
theorem B22258921 : Blo 674311 22258921 := bstep (se 2 (by rfl) ⟨8347095, by rfl⟩ : syracuseStep 22258921 = 16694191) B16694191
theorem B5219891 : Blo 674311 5219891 := bstep (se 1 (by rfl) ⟨3914918, by rfl⟩ : syracuseStep 5219891 = 7829837) B7829837
theorem B3090001 : Blo 674311 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B2565715 : Blo 674311 2565715 := bstep (se 1 (by rfl) ⟨1924286, by rfl⟩ : syracuseStep 2565715 = 3848573) B3848573
theorem B2172511 : Blo 674311 2172511 := bstep (se 1 (by rfl) ⟨1629383, by rfl⟩ : syracuseStep 2172511 = 3258767) B3258767
theorem B4105991 : Blo 674311 4105991 := bstep (se 1 (by rfl) ⟨3079493, by rfl⟩ : syracuseStep 4105991 = 6158987) B6158987
theorem B1386319 : Blo 674311 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B6498467 : Blo 674311 6498467 := bstep (se 1 (by rfl) ⟨4873850, by rfl⟩ : syracuseStep 6498467 = 9747701) B9747701
theorem B1517759 : Blo 674311 1517759 := bstep (se 1 (by rfl) ⟨1138319, by rfl⟩ : syracuseStep 1517759 = 2276639) B2276639
theorem B2599307 : Blo 674311 2599307 := bstep (se 1 (by rfl) ⟨1949480, by rfl⟩ : syracuseStep 2599307 = 3898961) B3898961
theorem B16427447 : Blo 674311 16427447 := bstep (se 1 (by rfl) ⟨12320585, by rfl⟩ : syracuseStep 16427447 = 24641171) B24641171
theorem B3648037 : Blo 674311 3648037 := bstep (se 4 (by rfl) ⟨342003, by rfl⟩ : syracuseStep 3648037 = 684007) B684007
theorem B38972339 : Blo 674311 38972339 := bstep (se 1 (by rfl) ⟨29229254, by rfl⟩ : syracuseStep 38972339 = 58458509) B58458509
theorem B1518713 : Blo 674311 1518713 := bstep (se 2 (by rfl) ⟨569517, by rfl⟩ : syracuseStep 1518713 = 1139035) B1139035
theorem B1027495 : Blo 674311 1027495 := bstep (se 1 (by rfl) ⟨770621, by rfl⟩ : syracuseStep 1027495 = 1541243) B1541243
theorem B961961 : Blo 674311 961961 := bstep (se 2 (by rfl) ⟨360735, by rfl⟩ : syracuseStep 961961 = 721471) B721471
theorem B3845657 : Blo 674311 3845657 := bstep (se 2 (by rfl) ⟨1442121, by rfl⟩ : syracuseStep 3845657 = 2884243) B2884243
theorem B962155 : Blo 674311 962155 := bstep (se 1 (by rfl) ⟨721616, by rfl⟩ : syracuseStep 962155 = 1443233) B1443233
theorem B6172409 : Blo 674311 6172409 := bstep (se 2 (by rfl) ⟨2314653, by rfl⟩ : syracuseStep 6172409 = 4629307) B4629307
theorem B37007117 : Blo 674311 37007117 := bstep (se 3 (by rfl) ⟨6938834, by rfl⟩ : syracuseStep 37007117 = 13877669) B13877669
theorem B1519379 : Blo 674311 1519379 := bstep (se 1 (by rfl) ⟨1139534, by rfl⟩ : syracuseStep 1519379 = 2279069) B2279069
theorem B7712819 : Blo 674311 7712819 := bstep (se 1 (by rfl) ⟨5784614, by rfl⟩ : syracuseStep 7712819 = 11569229) B11569229
theorem B1519739 : Blo 674311 1519739 := bstep (se 1 (by rfl) ⟨1139804, by rfl⟩ : syracuseStep 1519739 = 2279609) B2279609
theorem B17576099 : Blo 674311 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B2896067 : Blo 674311 2896067 := bstep (se 1 (by rfl) ⟨2172050, by rfl⟩ : syracuseStep 2896067 = 4344101) B4344101
theorem B1520009 : Blo 674311 1520009 := bstep (se 2 (by rfl) ⟨570003, by rfl⟩ : syracuseStep 1520009 = 1140007) B1140007
theorem B3256847 : Blo 674311 3256847 := bstep (se 1 (by rfl) ⟨2442635, by rfl⟩ : syracuseStep 3256847 = 4885271) B4885271
theorem B1520747 : Blo 674311 1520747 := bstep (se 1 (by rfl) ⟨1140560, by rfl⟩ : syracuseStep 1520747 = 2281121) B2281121
theorem B2438657 : Blo 674311 2438657 := bstep (se 2 (by rfl) ⟨914496, by rfl⟩ : syracuseStep 2438657 = 1828993) B1828993
theorem B1521323 : Blo 674311 1521323 := bstep (se 1 (by rfl) ⟨1140992, by rfl⟩ : syracuseStep 1521323 = 2281985) B2281985
theorem B5125841 : Blo 674311 5125841 := bstep (se 2 (by rfl) ⟨1922190, by rfl⟩ : syracuseStep 5125841 = 3844381) B3844381
theorem B1521647 : Blo 674311 1521647 := bstep (se 1 (by rfl) ⟨1141235, by rfl⟩ : syracuseStep 1521647 = 2282471) B2282471
theorem B10401851 : Blo 674311 10401851 := bstep (se 1 (by rfl) ⟨7801388, by rfl⟩ : syracuseStep 10401851 = 15602777) B15602777
theorem B3258539 : Blo 674311 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B1521863 : Blo 674311 1521863 := bstep (se 1 (by rfl) ⟨1141397, by rfl⟩ : syracuseStep 1521863 = 2282795) B2282795
theorem B3422573 : Blo 674311 3422573 := bstep (se 3 (by rfl) ⟨641732, by rfl⟩ : syracuseStep 3422573 = 1283465) B1283465
theorem B4864367 : Blo 674311 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B6502771 : Blo 674311 6502771 := bstep (se 1 (by rfl) ⟨4877078, by rfl⟩ : syracuseStep 6502771 = 9754157) B9754157
theorem B1522043 : Blo 674311 1522043 := bstep (se 1 (by rfl) ⟨1141532, by rfl⟩ : syracuseStep 1522043 = 2283065) B2283065
theorem B1522313 : Blo 674311 1522313 := bstep (se 2 (by rfl) ⟨570867, by rfl⟩ : syracuseStep 1522313 = 1141735) B1141735
theorem B1031071 : Blo 674311 1031071 := bstep (se 1 (by rfl) ⟨773303, by rfl⟩ : syracuseStep 1031071 = 1546607) B1546607
theorem B2276423 : Blo 674311 2276423 := bstep (se 1 (by rfl) ⟨1707317, by rfl⟩ : syracuseStep 2276423 = 3414635) B3414635
theorem B2571335 : Blo 674311 2571335 := bstep (se 1 (by rfl) ⟨1928501, by rfl⟩ : syracuseStep 2571335 = 3857003) B3857003
theorem B2276477 : Blo 674311 2276477 := bstep (se 3 (by rfl) ⟨426839, by rfl⟩ : syracuseStep 2276477 = 853679) B853679
theorem B1522871 : Blo 674311 1522871 := bstep (se 1 (by rfl) ⟨1142153, by rfl⟩ : syracuseStep 1522871 = 2284307) B2284307
theorem B2440487 : Blo 674311 2440487 := bstep (se 1 (by rfl) ⟨1830365, by rfl⟩ : syracuseStep 2440487 = 3660731) B3660731
theorem B2276747 : Blo 674311 2276747 := bstep (se 1 (by rfl) ⟨1707560, by rfl⟩ : syracuseStep 2276747 = 3415121) B3415121
theorem B2440847 : Blo 674311 2440847 := bstep (se 1 (by rfl) ⟨1830635, by rfl⟩ : syracuseStep 2440847 = 3661271) B3661271
theorem B1523447 : Blo 674311 1523447 := bstep (se 1 (by rfl) ⟨1142585, by rfl⟩ : syracuseStep 1523447 = 2285171) B2285171
theorem B1523627 : Blo 674311 1523627 := bstep (se 1 (by rfl) ⟨1142720, by rfl⟩ : syracuseStep 1523627 = 2285441) B2285441
theorem B5128271 : Blo 674311 5128271 := bstep (se 1 (by rfl) ⟨3846203, by rfl⟩ : syracuseStep 5128271 = 7692407) B7692407
theorem B2572519 : Blo 674311 2572519 := bstep (se 1 (by rfl) ⟨1929389, by rfl⟩ : syracuseStep 2572519 = 3858779) B3858779
theorem B12370151 : Blo 674311 12370151 := bstep (se 1 (by rfl) ⟨9277613, by rfl⟩ : syracuseStep 12370151 = 18555227) B18555227
theorem B1524167 : Blo 674311 1524167 := bstep (se 1 (by rfl) ⟨1143125, by rfl⟩ : syracuseStep 1524167 = 2286251) B2286251
theorem B4637135 : Blo 674311 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B3425003 : Blo 674311 3425003 := bstep (se 1 (by rfl) ⟨2568752, by rfl⟩ : syracuseStep 3425003 = 5137505) B5137505
theorem B1524527 : Blo 674311 1524527 := bstep (se 1 (by rfl) ⟨1143395, by rfl⟩ : syracuseStep 1524527 = 2286791) B2286791
theorem B2081747 : Blo 674311 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B11551733 : Blo 674311 11551733 := bstep (se 5 (by rfl) ⟨541487, by rfl⟩ : syracuseStep 11551733 = 1082975) B1082975
theorem B2377067 : Blo 674311 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B2311561 : Blo 674311 2311561 := bstep (se 2 (by rfl) ⟨866835, by rfl⟩ : syracuseStep 2311561 = 1733671) B1733671
theorem B2573977 : Blo 674311 2573977 := bstep (se 2 (by rfl) ⟨965241, by rfl⟩ : syracuseStep 2573977 = 1930483) B1930483
theorem B9750239 : Blo 674311 9750239 := bstep (se 1 (by rfl) ⟨7312679, by rfl⟩ : syracuseStep 9750239 = 14625359) B14625359
theorem B1525535 : Blo 674311 1525535 := bstep (se 1 (by rfl) ⟨1144151, by rfl⟩ : syracuseStep 1525535 = 2288303) B2288303
theorem B3852197 : Blo 674311 3852197 := bstep (se 4 (by rfl) ⟨361143, by rfl⟩ : syracuseStep 3852197 = 722287) B722287
theorem B1525751 : Blo 674311 1525751 := bstep (se 1 (by rfl) ⟨1144313, by rfl⟩ : syracuseStep 1525751 = 2288627) B2288627
theorem B2279771 : Blo 674311 2279771 := bstep (se 1 (by rfl) ⟨1709828, by rfl⟩ : syracuseStep 2279771 = 3419657) B3419657
theorem B1526111 : Blo 674311 1526111 := bstep (se 1 (by rfl) ⟨1144583, by rfl⟩ : syracuseStep 1526111 = 2289167) B2289167
theorem B3426785 : Blo 674311 3426785 := bstep (se 2 (by rfl) ⟨1285044, by rfl⟩ : syracuseStep 3426785 = 2570089) B2570089
theorem B674331 : Blo 674311 674331 := bstep (se 1 (by rfl) ⟨505748, by rfl⟩ : syracuseStep 674331 = 1011497) B1011497
theorem B674335 : Blo 674311 674335 := bstep (se 1 (by rfl) ⟨505751, by rfl⟩ : syracuseStep 674335 = 1011503) B1011503
theorem B2280041 : Blo 674311 2280041 := bstep (se 2 (by rfl) ⟨855015, by rfl⟩ : syracuseStep 2280041 = 1710031) B1710031
theorem B7817867 : Blo 674311 7817867 := bstep (se 1 (by rfl) ⟨5863400, by rfl⟩ : syracuseStep 7817867 = 11726801) B11726801
theorem B3852947 : Blo 674311 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B674651 : Blo 674311 674651 := bstep (se 1 (by rfl) ⟨505988, by rfl⟩ : syracuseStep 674651 = 1011977) B1011977
theorem B674719 : Blo 674311 674719 := bstep (se 1 (by rfl) ⟨506039, by rfl⟩ : syracuseStep 674719 = 1012079) B1012079
theorem B674863 : Blo 674311 674863 := bstep (se 1 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 674863 = 1012295) B1012295
theorem B674887 : Blo 674311 674887 := bstep (se 1 (by rfl) ⟨506165, by rfl⟩ : syracuseStep 674887 = 1012331) B1012331
theorem B675039 : Blo 674311 675039 := bstep (se 1 (by rfl) ⟨506279, by rfl⟩ : syracuseStep 675039 = 1012559) B1012559
theorem B3656927 : Blo 674311 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B675303 : Blo 674311 675303 := bstep (se 1 (by rfl) ⟨506477, by rfl⟩ : syracuseStep 675303 = 1012955) B1012955
theorem B8670725 : Blo 674311 8670725 := bstep (se 4 (by rfl) ⟨812880, by rfl⟩ : syracuseStep 8670725 = 1625761) B1625761
theorem B4345433 : Blo 674311 4345433 := bstep (se 2 (by rfl) ⟨1629537, by rfl⟩ : syracuseStep 4345433 = 3259075) B3259075
theorem B675419 : Blo 674311 675419 := bstep (se 1 (by rfl) ⟨506564, by rfl⟩ : syracuseStep 675419 = 1013129) B1013129
theorem B2281067 : Blo 674311 2281067 := bstep (se 1 (by rfl) ⟨1710800, by rfl⟩ : syracuseStep 2281067 = 3421601) B3421601
theorem B3854087 : Blo 674311 3854087 := bstep (se 1 (by rfl) ⟨2890565, by rfl⟩ : syracuseStep 3854087 = 5781131) B5781131
theorem B675655 : Blo 674311 675655 := bstep (se 1 (by rfl) ⟨506741, by rfl⟩ : syracuseStep 675655 = 1013483) B1013483
theorem B4935505 : Blo 674311 4935505 := bstep (se 2 (by rfl) ⟨1850814, by rfl⟩ : syracuseStep 4935505 = 3701629) B3701629
theorem B2281337 : Blo 674311 2281337 := bstep (se 2 (by rfl) ⟨855501, by rfl⟩ : syracuseStep 2281337 = 1711003) B1711003
theorem B675807 : Blo 674311 675807 := bstep (se 1 (by rfl) ⟨506855, by rfl⟩ : syracuseStep 675807 = 1013711) B1013711
theorem B2281661 : Blo 674311 2281661 := bstep (se 3 (by rfl) ⟨427811, by rfl⟩ : syracuseStep 2281661 = 855623) B855623
theorem B676071 : Blo 674311 676071 := bstep (se 1 (by rfl) ⟨507053, by rfl⟩ : syracuseStep 676071 = 1014107) B1014107
theorem B676223 : Blo 674311 676223 := bstep (se 1 (by rfl) ⟨507167, by rfl⟩ : syracuseStep 676223 = 1014335) B1014335
theorem B676303 : Blo 674311 676303 := bstep (se 1 (by rfl) ⟨507227, by rfl⟩ : syracuseStep 676303 = 1014455) B1014455
theorem B1823327 : Blo 674311 1823327 := bstep (se 1 (by rfl) ⟨1367495, by rfl⟩ : syracuseStep 1823327 = 2734991) B2734991
theorem B676455 : Blo 674311 676455 := bstep (se 1 (by rfl) ⟨507341, by rfl⟩ : syracuseStep 676455 = 1014683) B1014683
theorem B3429053 : Blo 674311 3429053 := bstep (se 3 (by rfl) ⟨642947, by rfl⟩ : syracuseStep 3429053 = 1285895) B1285895
theorem B676719 : Blo 674311 676719 := bstep (se 1 (by rfl) ⟨507539, by rfl⟩ : syracuseStep 676719 = 1015079) B1015079
theorem B676775 : Blo 674311 676775 := bstep (se 1 (by rfl) ⟨507581, by rfl⟩ : syracuseStep 676775 = 1015163) B1015163
theorem B1921963 : Blo 674311 1921963 := bstep (se 1 (by rfl) ⟨1441472, by rfl⟩ : syracuseStep 1921963 = 2882945) B2882945
theorem B676859 : Blo 674311 676859 := bstep (se 1 (by rfl) ⟨507644, by rfl⟩ : syracuseStep 676859 = 1015289) B1015289
theorem B6181895 : Blo 674311 6181895 := bstep (se 1 (by rfl) ⟨4636421, by rfl⟩ : syracuseStep 6181895 = 9272843) B9272843
theorem B24728615 : Blo 674311 24728615 := bstep (se 1 (by rfl) ⟨18546461, by rfl⟩ : syracuseStep 24728615 = 37092923) B37092923
theorem B676927 : Blo 674311 676927 := bstep (se 1 (by rfl) ⟨507695, by rfl⟩ : syracuseStep 676927 = 1015391) B1015391
theorem B4117567 : Blo 674311 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B677071 : Blo 674311 677071 := bstep (se 1 (by rfl) ⟨507803, by rfl⟩ : syracuseStep 677071 = 1015607) B1015607
theorem B2282849 : Blo 674311 2282849 := bstep (se 2 (by rfl) ⟨856068, by rfl⟩ : syracuseStep 2282849 = 1712137) B1712137
theorem B677275 : Blo 674311 677275 := bstep (se 1 (by rfl) ⟨507956, by rfl⟩ : syracuseStep 677275 = 1015913) B1015913
theorem B677487 : Blo 674311 677487 := bstep (se 1 (by rfl) ⟨508115, by rfl⟩ : syracuseStep 677487 = 1016231) B1016231
theorem B677543 : Blo 674311 677543 := bstep (se 1 (by rfl) ⟨508157, by rfl⟩ : syracuseStep 677543 = 1016315) B1016315
theorem B677627 : Blo 674311 677627 := bstep (se 1 (by rfl) ⟨508220, by rfl⟩ : syracuseStep 677627 = 1016441) B1016441
theorem B677663 : Blo 674311 677663 := bstep (se 1 (by rfl) ⟨508247, by rfl⟩ : syracuseStep 677663 = 1016495) B1016495
theorem B677695 : Blo 674311 677695 := bstep (se 1 (by rfl) ⟨508271, by rfl⟩ : syracuseStep 677695 = 1016543) B1016543
theorem B16701299 : Blo 674311 16701299 := bstep (se 1 (by rfl) ⟨12525974, by rfl⟩ : syracuseStep 16701299 = 25051949) B25051949
theorem B677871 : Blo 674311 677871 := bstep (se 1 (by rfl) ⟨508403, by rfl⟩ : syracuseStep 677871 = 1016807) B1016807
theorem B678043 : Blo 674311 678043 := bstep (se 1 (by rfl) ⟨508532, by rfl⟩ : syracuseStep 678043 = 1017065) B1017065
theorem B678079 : Blo 674311 678079 := bstep (se 1 (by rfl) ⟨508559, by rfl⟩ : syracuseStep 678079 = 1017119) B1017119
theorem B8771827 : Blo 674311 8771827 := bstep (se 1 (by rfl) ⟨6578870, by rfl⟩ : syracuseStep 8771827 = 13157741) B13157741
theorem B678191 : Blo 674311 678191 := bstep (se 1 (by rfl) ⟨508643, by rfl⟩ : syracuseStep 678191 = 1017287) B1017287
theorem B1629019 : Blo 674311 1629019 := bstep (se 1 (by rfl) ⟨1221764, by rfl⟩ : syracuseStep 1629019 = 2443529) B2443529
theorem B2284793 : Blo 674311 2284793 := bstep (se 2 (by rfl) ⟨856797, by rfl⟩ : syracuseStep 2284793 = 1713595) B1713595
theorem B1138151 : Blo 674311 1138151 := bstep (se 1 (by rfl) ⟨853613, by rfl⟩ : syracuseStep 1138151 = 1707227) B1707227
theorem B1138171 : Blo 674311 1138171 := bstep (se 1 (by rfl) ⟨853628, by rfl⟩ : syracuseStep 1138171 = 1707257) B1707257
theorem B2285063 : Blo 674311 2285063 := bstep (se 1 (by rfl) ⟨1713797, by rfl⟩ : syracuseStep 2285063 = 3427595) B3427595
theorem B7298839 : Blo 674311 7298839 := bstep (se 1 (by rfl) ⟨5474129, by rfl⟩ : syracuseStep 7298839 = 10948259) B10948259
theorem B15621983 : Blo 674311 15621983 := bstep (se 1 (by rfl) ⟨11716487, by rfl⟩ : syracuseStep 15621983 = 23432975) B23432975
theorem B1138603 : Blo 674311 1138603 := bstep (se 1 (by rfl) ⟨853952, by rfl⟩ : syracuseStep 1138603 = 1707905) B1707905
theorem B4382693 : Blo 674311 4382693 := bstep (se 4 (by rfl) ⟨410877, by rfl⟩ : syracuseStep 4382693 = 821755) B821755
theorem B1138907 : Blo 674311 1138907 := bstep (se 1 (by rfl) ⟨854180, by rfl⟩ : syracuseStep 1138907 = 1708361) B1708361
theorem B1139143 : Blo 674311 1139143 := bstep (se 1 (by rfl) ⟨854357, by rfl⟩ : syracuseStep 1139143 = 1708715) B1708715
theorem B1139177 : Blo 674311 1139177 := bstep (se 2 (by rfl) ⟨427191, by rfl⟩ : syracuseStep 1139177 = 854383) B854383
theorem B2286143 : Blo 674311 2286143 := bstep (se 1 (by rfl) ⟨1714607, by rfl⟩ : syracuseStep 2286143 = 3429215) B3429215
theorem B4875005 : Blo 674311 4875005 := bstep (se 3 (by rfl) ⟨914063, by rfl⟩ : syracuseStep 4875005 = 1828127) B1828127
theorem B4875065 : Blo 674311 4875065 := bstep (se 2 (by rfl) ⟨1828149, by rfl⟩ : syracuseStep 4875065 = 3656299) B3656299
theorem B4384543 : Blo 674311 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B1926953 : Blo 674311 1926953 := bstep (se 2 (by rfl) ⟨722607, by rfl⟩ : syracuseStep 1926953 = 1445215) B1445215
theorem B2287439 : Blo 674311 2287439 := bstep (se 1 (by rfl) ⟨1715579, by rfl⟩ : syracuseStep 2287439 = 3431159) B3431159
theorem B2287763 : Blo 674311 2287763 := bstep (se 1 (by rfl) ⟨1715822, by rfl⟩ : syracuseStep 2287763 = 3431645) B3431645
theorem B1141033 : Blo 674311 1141033 := bstep (se 2 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 1141033 = 855775) B855775
theorem B2288033 : Blo 674311 2288033 := bstep (se 2 (by rfl) ⟨858012, by rfl⟩ : syracuseStep 2288033 = 1716025) B1716025
theorem B3664385 : Blo 674311 3664385 := bstep (se 2 (by rfl) ⟨1374144, by rfl⟩ : syracuseStep 3664385 = 2748289) B2748289
theorem B1305119 : Blo 674311 1305119 := bstep (se 1 (by rfl) ⟨978839, by rfl⟩ : syracuseStep 1305119 = 1957679) B1957679
theorem B14805605 : Blo 674311 14805605 := bstep (se 4 (by rfl) ⟨1388025, by rfl⟩ : syracuseStep 14805605 = 2776051) B2776051
theorem B7695323 : Blo 674311 7695323 := bstep (se 1 (by rfl) ⟨5771492, by rfl⟩ : syracuseStep 7695323 = 11542985) B11542985
theorem B1142363 : Blo 674311 1142363 := bstep (se 1 (by rfl) ⟨856772, by rfl⟩ : syracuseStep 1142363 = 1713545) B1713545
theorem B21884579 : Blo 674311 21884579 := bstep (se 1 (by rfl) ⟨16413434, by rfl⟩ : syracuseStep 21884579 = 32826869) B32826869
theorem B1011527 : Blo 674311 1011527 := bstep (se 1 (by rfl) ⟨758645, by rfl⟩ : syracuseStep 1011527 = 1517291) B1517291
theorem B1142599 : Blo 674311 1142599 := bstep (se 1 (by rfl) ⟨856949, by rfl⟩ : syracuseStep 1142599 = 1713899) B1713899
theorem B1011611 : Blo 674311 1011611 := bstep (se 1 (by rfl) ⟨758708, by rfl⟩ : syracuseStep 1011611 = 1517417) B1517417
theorem B1929527 : Blo 674311 1929527 := bstep (se 1 (by rfl) ⟨1447145, by rfl⟩ : syracuseStep 1929527 = 2894291) B2894291
theorem B2748809 : Blo 674311 2748809 := bstep (se 2 (by rfl) ⟨1030803, by rfl⟩ : syracuseStep 2748809 = 2061607) B2061607
theorem B1012175 : Blo 674311 1012175 := bstep (se 1 (by rfl) ⟨759131, by rfl⟩ : syracuseStep 1012175 = 1518263) B1518263
theorem B1143247 : Blo 674311 1143247 := bstep (se 1 (by rfl) ⟨857435, by rfl⟩ : syracuseStep 1143247 = 1714871) B1714871
theorem B1012217 : Blo 674311 1012217 := bstep (se 2 (by rfl) ⟨379581, by rfl⟩ : syracuseStep 1012217 = 759163) B759163
theorem B2191865 : Blo 674311 2191865 := bstep (se 2 (by rfl) ⟨821949, by rfl⟩ : syracuseStep 2191865 = 1643899) B1643899
theorem B1012319 : Blo 674311 1012319 := bstep (se 1 (by rfl) ⟨759239, by rfl⟩ : syracuseStep 1012319 = 1518479) B1518479
theorem B1012799 : Blo 674311 1012799 := bstep (se 1 (by rfl) ⟨759599, by rfl⟩ : syracuseStep 1012799 = 1519199) B1519199
theorem B1012841 : Blo 674311 1012841 := bstep (se 2 (by rfl) ⟨379815, by rfl⟩ : syracuseStep 1012841 = 759631) B759631
theorem B1143983 : Blo 674311 1143983 := bstep (se 1 (by rfl) ⟨857987, by rfl⟩ : syracuseStep 1143983 = 1715975) B1715975
theorem B1012943 : Blo 674311 1012943 := bstep (se 1 (by rfl) ⟨759707, by rfl⟩ : syracuseStep 1012943 = 1519415) B1519415
theorem B1013147 : Blo 674311 1013147 := bstep (se 1 (by rfl) ⟨759860, by rfl⟩ : syracuseStep 1013147 = 1519721) B1519721
theorem B1144219 : Blo 674311 1144219 := bstep (se 1 (by rfl) ⟨858164, by rfl⟩ : syracuseStep 1144219 = 1716329) B1716329
theorem B1013369 : Blo 674311 1013369 := bstep (se 2 (by rfl) ⟨380013, by rfl⟩ : syracuseStep 1013369 = 760027) B760027
theorem B1013471 : Blo 674311 1013471 := bstep (se 1 (by rfl) ⟨760103, by rfl⟩ : syracuseStep 1013471 = 1520207) B1520207
theorem B1144543 : Blo 674311 1144543 := bstep (se 1 (by rfl) ⟨858407, by rfl⟩ : syracuseStep 1144543 = 1716815) B1716815
theorem B1013567 : Blo 674311 1013567 := bstep (se 1 (by rfl) ⟨760175, by rfl⟩ : syracuseStep 1013567 = 1520351) B1520351
theorem B1013735 : Blo 674311 1013735 := bstep (se 1 (by rfl) ⟨760301, by rfl⟩ : syracuseStep 1013735 = 1520603) B1520603
theorem B1013753 : Blo 674311 1013753 := bstep (se 2 (by rfl) ⟨380157, by rfl⟩ : syracuseStep 1013753 = 760315) B760315
theorem B1013855 : Blo 674311 1013855 := bstep (se 1 (by rfl) ⟨760391, by rfl⟩ : syracuseStep 1013855 = 1520783) B1520783
theorem B1013915 : Blo 674311 1013915 := bstep (se 1 (by rfl) ⟨760436, by rfl⟩ : syracuseStep 1013915 = 1520873) B1520873
theorem B1013951 : Blo 674311 1013951 := bstep (se 1 (by rfl) ⟨760463, by rfl⟩ : syracuseStep 1013951 = 1520927) B1520927
theorem B1013993 : Blo 674311 1013993 := bstep (se 2 (by rfl) ⟨380247, by rfl⟩ : syracuseStep 1013993 = 760495) B760495
theorem B2161019 : Blo 674311 2161019 := bstep (se 1 (by rfl) ⟨1620764, by rfl⟩ : syracuseStep 2161019 = 3241529) B3241529
theorem B1014299 : Blo 674311 1014299 := bstep (se 1 (by rfl) ⟨760724, by rfl⟩ : syracuseStep 1014299 = 1521449) B1521449
theorem B1014377 : Blo 674311 1014377 := bstep (se 2 (by rfl) ⟨380391, by rfl⟩ : syracuseStep 1014377 = 760783) B760783
theorem B19528613 : Blo 674311 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B4324367 : Blo 674311 4324367 := bstep (se 1 (by rfl) ⟨3243275, by rfl⟩ : syracuseStep 4324367 = 6486551) B6486551
theorem B1080361 : Blo 674311 1080361 := bstep (se 2 (by rfl) ⟨405135, by rfl⟩ : syracuseStep 1080361 = 810271) B810271
theorem B1014905 : Blo 674311 1014905 := bstep (se 2 (by rfl) ⟨380589, by rfl⟩ : syracuseStep 1014905 = 761179) B761179
theorem B1015007 : Blo 674311 1015007 := bstep (se 1 (by rfl) ⟨761255, by rfl⟩ : syracuseStep 1015007 = 1522511) B1522511
theorem B1015049 : Blo 674311 1015049 := bstep (se 2 (by rfl) ⟨380643, by rfl⟩ : syracuseStep 1015049 = 761287) B761287
theorem B10976543 : Blo 674311 10976543 := bstep (se 1 (by rfl) ⟨8232407, by rfl⟩ : syracuseStep 10976543 = 16464815) B16464815
theorem B1015151 : Blo 674311 1015151 := bstep (se 1 (by rfl) ⟨761363, by rfl⟩ : syracuseStep 1015151 = 1522727) B1522727
theorem B3898853 : Blo 674311 3898853 := bstep (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) B731035
theorem B1015271 : Blo 674311 1015271 := bstep (se 1 (by rfl) ⟨761453, by rfl⟩ : syracuseStep 1015271 = 1522907) B1522907
theorem B3243527 : Blo 674311 3243527 := bstep (se 1 (by rfl) ⟨2432645, by rfl⟩ : syracuseStep 3243527 = 4865291) B4865291
theorem B1015403 : Blo 674311 1015403 := bstep (se 1 (by rfl) ⟨761552, by rfl⟩ : syracuseStep 1015403 = 1523105) B1523105
theorem B1015529 : Blo 674311 1015529 := bstep (se 2 (by rfl) ⟨380823, by rfl⟩ : syracuseStep 1015529 = 761647) B761647
theorem B5013335 : Blo 674311 5013335 := bstep (se 1 (by rfl) ⟨3760001, by rfl⟩ : syracuseStep 5013335 = 7520003) B7520003
theorem B1015673 : Blo 674311 1015673 := bstep (se 2 (by rfl) ⟨380877, by rfl⟩ : syracuseStep 1015673 = 761755) B761755
theorem B1081259 : Blo 674311 1081259 := bstep (se 1 (by rfl) ⟨810944, by rfl⟩ : syracuseStep 1081259 = 1621889) B1621889
theorem B1015775 : Blo 674311 1015775 := bstep (se 1 (by rfl) ⟨761831, by rfl⟩ : syracuseStep 1015775 = 1523663) B1523663
theorem B2162875 : Blo 674311 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B1016111 : Blo 674311 1016111 := bstep (se 1 (by rfl) ⟨762083, by rfl⟩ : syracuseStep 1016111 = 1524167) B1524167
theorem B1016351 : Blo 674311 1016351 := bstep (se 1 (by rfl) ⟨762263, by rfl⟩ : syracuseStep 1016351 = 1524527) B1524527
theorem B7701155 : Blo 674311 7701155 := bstep (se 1 (by rfl) ⟨5775866, by rfl⟩ : syracuseStep 7701155 = 11551733) B11551733
theorem B1017023 : Blo 674311 1017023 := bstep (se 1 (by rfl) ⟨762767, by rfl⟩ : syracuseStep 1017023 = 1525535) B1525535
theorem B1017167 : Blo 674311 1017167 := bstep (se 1 (by rfl) ⟨762875, by rfl⟩ : syracuseStep 1017167 = 1525751) B1525751
theorem B1017257 : Blo 674311 1017257 := bstep (se 2 (by rfl) ⟨381471, by rfl⟩ : syracuseStep 1017257 = 762943) B762943
theorem B1017407 : Blo 674311 1017407 := bstep (se 1 (by rfl) ⟨763055, by rfl⟩ : syracuseStep 1017407 = 1526111) B1526111
theorem B1017449 : Blo 674311 1017449 := bstep (se 2 (by rfl) ⟨381543, by rfl⟩ : syracuseStep 1017449 = 763087) B763087
theorem B4392667 : Blo 674311 4392667 := bstep (se 1 (by rfl) ⟨3294500, by rfl⟩ : syracuseStep 4392667 = 6589001) B6589001
theorem B5211911 : Blo 674311 5211911 := bstep (se 1 (by rfl) ⟨3908933, by rfl⟩ : syracuseStep 5211911 = 7817867) B7817867
theorem B2885473 : Blo 674311 2885473 := bstep (se 2 (by rfl) ⟨1082052, by rfl⟩ : syracuseStep 2885473 = 2164105) B2164105
theorem B1444873 : Blo 674311 1444873 := bstep (se 2 (by rfl) ⟨541827, by rfl⟩ : syracuseStep 1444873 = 1083655) B1083655
theorem B1215551 : Blo 674311 1215551 := bstep (se 1 (by rfl) ⟨911663, by rfl⟩ : syracuseStep 1215551 = 1823327) B1823327
theorem B1707115 : Blo 674311 1707115 := bstep (se 1 (by rfl) ⟨1280336, by rfl⟩ : syracuseStep 1707115 = 2560673) B2560673
theorem B16485743 : Blo 674311 16485743 := bstep (se 1 (by rfl) ⟨12364307, by rfl⟩ : syracuseStep 16485743 = 24728615) B24728615
theorem B1707763 : Blo 674311 1707763 := bstep (se 1 (by rfl) ⟨1280822, by rfl⟩ : syracuseStep 1707763 = 2561645) B2561645
theorem B3248045 : Blo 674311 3248045 := bstep (se 3 (by rfl) ⟨609008, by rfl⟩ : syracuseStep 3248045 = 1218017) B1218017
theorem B1282873 : Blo 674311 1282873 := bstep (se 2 (by rfl) ⟨481077, by rfl⟩ : syracuseStep 1282873 = 962155) B962155
theorem B1446761 : Blo 674311 1446761 := bstep (se 2 (by rfl) ⟨542535, by rfl⟩ : syracuseStep 1446761 = 1085071) B1085071
theorem B758767 : Blo 674311 758767 := bstep (se 1 (by rfl) ⟨569075, by rfl⟩ : syracuseStep 758767 = 1138151) B1138151
theorem B1709039 : Blo 674311 1709039 := bstep (se 1 (by rfl) ⟨1281779, by rfl⟩ : syracuseStep 1709039 = 2563559) B2563559
theorem B857071 : Blo 674311 857071 := bstep (se 1 (by rfl) ⟨642803, by rfl⟩ : syracuseStep 857071 = 1285607) B1285607
theorem B857243 : Blo 674311 857243 := bstep (se 1 (by rfl) ⟨642932, by rfl⟩ : syracuseStep 857243 = 1285865) B1285865
theorem B2921795 : Blo 674311 2921795 := bstep (se 1 (by rfl) ⟨2191346, by rfl⟩ : syracuseStep 2921795 = 4382693) B4382693
theorem B759271 : Blo 674311 759271 := bstep (se 1 (by rfl) ⟨569453, by rfl⟩ : syracuseStep 759271 = 1138907) B1138907
theorem B2561615 : Blo 674311 2561615 := bstep (se 1 (by rfl) ⟨1921211, by rfl⟩ : syracuseStep 2561615 = 3842423) B3842423
theorem B759451 : Blo 674311 759451 := bstep (se 1 (by rfl) ⟨569588, by rfl⟩ : syracuseStep 759451 = 1139177) B1139177
theorem B3250003 : Blo 674311 3250003 := bstep (se 1 (by rfl) ⟨2437502, by rfl⟩ : syracuseStep 3250003 = 4875005) B4875005
theorem B857947 : Blo 674311 857947 := bstep (se 1 (by rfl) ⟨643460, by rfl⟩ : syracuseStep 857947 = 1286921) B1286921
theorem B3250043 : Blo 674311 3250043 := bstep (se 1 (by rfl) ⟨2437532, by rfl⟩ : syracuseStep 3250043 = 4875065) B4875065
theorem B3479927 : Blo 674311 3479927 := bstep (se 1 (by rfl) ⟨2609945, by rfl⟩ : syracuseStep 3479927 = 5219891) B5219891
theorem B1284635 : Blo 674311 1284635 := bstep (se 1 (by rfl) ⟨963476, by rfl⟩ : syracuseStep 1284635 = 1926953) B1926953
theorem B2562617 : Blo 674311 2562617 := bstep (se 2 (by rfl) ⟨960981, by rfl⟩ : syracuseStep 2562617 = 1921963) B1921963
theorem B3480317 : Blo 674311 3480317 := bstep (se 3 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 3480317 = 1305119) B1305119
theorem B4332311 : Blo 674311 4332311 := bstep (se 1 (by rfl) ⟨3249233, by rfl⟩ : syracuseStep 4332311 = 6498467) B6498467
theorem B10951631 : Blo 674311 10951631 := bstep (se 1 (by rfl) ⟨8213723, by rfl⟩ : syracuseStep 10951631 = 16427447) B16427447
theorem B9870403 : Blo 674311 9870403 := bstep (se 1 (by rfl) ⟨7402802, by rfl⟩ : syracuseStep 9870403 = 14805605) B14805605
theorem B12328325 : Blo 674311 12328325 := bstep (se 4 (by rfl) ⟨1155780, by rfl⟩ : syracuseStep 12328325 = 2311561) B2311561
theorem B2563771 : Blo 674311 2563771 := bstep (se 1 (by rfl) ⟨1922828, by rfl⟩ : syracuseStep 2563771 = 3845657) B3845657
theorem B761575 : Blo 674311 761575 := bstep (se 1 (by rfl) ⟨571181, by rfl⟩ : syracuseStep 761575 = 1142363) B1142363
theorem B14589719 : Blo 674311 14589719 := bstep (se 1 (by rfl) ⟨10942289, by rfl⟩ : syracuseStep 14589719 = 21884579) B21884579
theorem B1286351 : Blo 674311 1286351 := bstep (se 1 (by rfl) ⟨964763, by rfl⟩ : syracuseStep 1286351 = 1929527) B1929527
theorem B2171231 : Blo 674311 2171231 := bstep (se 1 (by rfl) ⟨1628423, by rfl⟩ : syracuseStep 2171231 = 3256847) B3256847
theorem B5776109 : Blo 674311 5776109 := bstep (se 3 (by rfl) ⟨1083020, by rfl⟩ : syracuseStep 5776109 = 2166041) B2166041
theorem B762655 : Blo 674311 762655 := bstep (se 1 (by rfl) ⟨571991, by rfl⟩ : syracuseStep 762655 = 1143983) B1143983
theorem B3253117 : Blo 674311 3253117 := bstep (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) B1219919
theorem B2565229 : Blo 674311 2565229 := bstep (se 3 (by rfl) ⟨480980, by rfl⟩ : syracuseStep 2565229 = 961961) B961961
theorem B2172025 : Blo 674311 2172025 := bstep (se 2 (by rfl) ⟨814509, by rfl⟩ : syracuseStep 2172025 = 1629019) B1629019
theorem B3417227 : Blo 674311 3417227 := bstep (se 1 (by rfl) ⟨2562920, by rfl⟩ : syracuseStep 3417227 = 5125841) B5125841
theorem B2172359 : Blo 674311 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B1713737 : Blo 674311 1713737 := bstep (se 2 (by rfl) ⟨642651, by rfl⟩ : syracuseStep 1713737 = 1285303) B1285303
theorem B13019075 : Blo 674311 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B16459757 : Blo 674311 16459757 := bstep (se 3 (by rfl) ⟨3086204, by rfl⟩ : syracuseStep 16459757 = 6172409) B6172409
theorem B1517561 : Blo 674311 1517561 := bstep (se 2 (by rfl) ⟨569085, by rfl⟩ : syracuseStep 1517561 = 1138171) B1138171
theorem B1517615 : Blo 674311 1517615 := bstep (se 1 (by rfl) ⟨1138211, by rfl⟩ : syracuseStep 1517615 = 2276423) B2276423
theorem B1714223 : Blo 674311 1714223 := bstep (se 1 (by rfl) ⟨1285667, by rfl⟩ : syracuseStep 1714223 = 2571335) B2571335
theorem B1517651 : Blo 674311 1517651 := bstep (se 1 (by rfl) ⟨1138238, by rfl⟩ : syracuseStep 1517651 = 2276477) B2276477
theorem B7317695 : Blo 674311 7317695 := bstep (se 1 (by rfl) ⟨5488271, by rfl⟩ : syracuseStep 7317695 = 10976543) B10976543
theorem B1517831 : Blo 674311 1517831 := bstep (se 1 (by rfl) ⟨1138373, by rfl⟩ : syracuseStep 1517831 = 2276747) B2276747
theorem B2599235 : Blo 674311 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B1518137 : Blo 674311 1518137 := bstep (se 2 (by rfl) ⟨569301, by rfl⟩ : syracuseStep 1518137 = 1138603) B1138603
theorem B2894393 : Blo 674311 2894393 := bstep (se 2 (by rfl) ⟨1085397, by rfl⟩ : syracuseStep 2894393 = 2170795) B2170795
theorem B3418847 : Blo 674311 3418847 := bstep (se 1 (by rfl) ⟨2564135, by rfl⟩ : syracuseStep 3418847 = 5128271) B5128271
theorem B1518857 : Blo 674311 1518857 := bstep (se 2 (by rfl) ⟨569571, by rfl⟩ : syracuseStep 1518857 = 1139143) B1139143
theorem B1027835 : Blo 674311 1027835 := bstep (se 1 (by rfl) ⟨770876, by rfl⟩ : syracuseStep 1027835 = 1541753) B1541753
theorem B6500159 : Blo 674311 6500159 := bstep (se 1 (by rfl) ⟨4875119, by rfl⟩ : syracuseStep 6500159 = 9750239) B9750239
theorem B12365693 : Blo 674311 12365693 := bstep (se 3 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 12365693 = 4637135) B4637135
theorem B2568131 : Blo 674311 2568131 := bstep (se 1 (by rfl) ⟨1926098, by rfl⟩ : syracuseStep 2568131 = 3852197) B3852197
theorem B5844973 : Blo 674311 5844973 := bstep (se 3 (by rfl) ⟨1095932, by rfl⟩ : syracuseStep 5844973 = 2191865) B2191865
theorem B1519847 : Blo 674311 1519847 := bstep (se 1 (by rfl) ⟨1139885, by rfl⟩ : syracuseStep 1519847 = 2279771) B2279771
theorem B4108519 : Blo 674311 4108519 := bstep (se 1 (by rfl) ⟨3081389, by rfl⟩ : syracuseStep 4108519 = 6162779) B6162779
theorem B1520027 : Blo 674311 1520027 := bstep (se 1 (by rfl) ⟨1140020, by rfl⟩ : syracuseStep 1520027 = 2280041) B2280041
theorem B2568631 : Blo 674311 2568631 := bstep (se 1 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 2568631 = 3852947) B3852947
theorem B3420953 : Blo 674311 3420953 := bstep (se 2 (by rfl) ⟨1282857, by rfl⟩ : syracuseStep 3420953 = 2565715) B2565715
theorem B2437951 : Blo 674311 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B5780483 : Blo 674311 5780483 := bstep (se 1 (by rfl) ⟨4335362, by rfl⟩ : syracuseStep 5780483 = 8670725) B8670725
theorem B5846057 : Blo 674311 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B2896955 : Blo 674311 2896955 := bstep (se 1 (by rfl) ⟨2172716, by rfl⟩ : syracuseStep 2896955 = 4345433) B4345433
theorem B1520711 : Blo 674311 1520711 := bstep (se 1 (by rfl) ⟨1140533, by rfl⟩ : syracuseStep 1520711 = 2281067) B2281067
theorem B1848425 : Blo 674311 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B2569391 : Blo 674311 2569391 := bstep (se 1 (by rfl) ⟨1927043, by rfl⟩ : syracuseStep 2569391 = 3854087) B3854087
theorem B5551325 : Blo 674311 5551325 := bstep (se 3 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 5551325 = 2081747) B2081747
theorem B1520891 : Blo 674311 1520891 := bstep (se 1 (by rfl) ⟨1140668, by rfl⟩ : syracuseStep 1520891 = 2281337) B2281337
theorem B1521107 : Blo 674311 1521107 := bstep (se 1 (by rfl) ⟨1140830, by rfl⟩ : syracuseStep 1521107 = 2281661) B2281661
theorem B3847823 : Blo 674311 3847823 := bstep (se 1 (by rfl) ⟨2885867, by rfl⟩ : syracuseStep 3847823 = 5771735) B5771735
theorem B1521377 : Blo 674311 1521377 := bstep (se 2 (by rfl) ⟨570516, by rfl⟩ : syracuseStep 1521377 = 1141033) B1141033
theorem B4864049 : Blo 674311 4864049 := bstep (se 2 (by rfl) ⟨1824018, by rfl⟩ : syracuseStep 4864049 = 3648037) B3648037
theorem B1521899 : Blo 674311 1521899 := bstep (se 1 (by rfl) ⟨1141424, by rfl⟩ : syracuseStep 1521899 = 2282849) B2282849
theorem B6338845 : Blo 674311 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B2734535 : Blo 674311 2734535 := bstep (se 1 (by rfl) ⟨2050901, by rfl⟩ : syracuseStep 2734535 = 4101803) B4101803
theorem B965071 : Blo 674311 965071 := bstep (se 1 (by rfl) ⟨723803, by rfl⟩ : syracuseStep 965071 = 1447607) B1447607
theorem B11582351 : Blo 674311 11582351 := bstep (se 1 (by rfl) ⟨8686763, by rfl⟩ : syracuseStep 11582351 = 17373527) B17373527
theorem B1620947 : Blo 674311 1620947 := bstep (se 1 (by rfl) ⟨1215710, by rfl⟩ : syracuseStep 1620947 = 2431421) B2431421
theorem B1523195 : Blo 674311 1523195 := bstep (se 1 (by rfl) ⟨1142396, by rfl⟩ : syracuseStep 1523195 = 2284793) B2284793
theorem B1523375 : Blo 674311 1523375 := bstep (se 1 (by rfl) ⟨1142531, by rfl⟩ : syracuseStep 1523375 = 2285063) B2285063
theorem B4505311 : Blo 674311 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B1523465 : Blo 674311 1523465 := bstep (se 2 (by rfl) ⟨571299, by rfl⟩ : syracuseStep 1523465 = 1142599) B1142599
theorem B2277287 : Blo 674311 2277287 := bstep (se 1 (by rfl) ⟨1707965, by rfl⟩ : syracuseStep 2277287 = 3415931) B3415931
theorem B3850213 : Blo 674311 3850213 := bstep (se 4 (by rfl) ⟨360957, by rfl⟩ : syracuseStep 3850213 = 721915) B721915
theorem B2277611 : Blo 674311 2277611 := bstep (se 1 (by rfl) ⟨1708208, by rfl⟩ : syracuseStep 2277611 = 3416417) B3416417
theorem B3850487 : Blo 674311 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B1524095 : Blo 674311 1524095 := bstep (se 1 (by rfl) ⟨1143071, by rfl⟩ : syracuseStep 1524095 = 2286143) B2286143
theorem B1524329 : Blo 674311 1524329 := bstep (se 2 (by rfl) ⟨571623, by rfl⟩ : syracuseStep 1524329 = 1143247) B1143247
theorem B2933435 : Blo 674311 2933435 := bstep (se 1 (by rfl) ⟨2200076, by rfl⟩ : syracuseStep 2933435 = 4400153) B4400153
theorem B2737327 : Blo 674311 2737327 := bstep (se 1 (by rfl) ⟨2052995, by rfl⟩ : syracuseStep 2737327 = 4105991) B4105991
theorem B1524959 : Blo 674311 1524959 := bstep (se 1 (by rfl) ⟨1143719, by rfl⟩ : syracuseStep 1524959 = 2287439) B2287439
theorem B11716001 : Blo 674311 11716001 := bstep (se 2 (by rfl) ⟨4393500, by rfl⟩ : syracuseStep 11716001 = 8787001) B8787001
theorem B5490089 : Blo 674311 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B1525175 : Blo 674311 1525175 := bstep (se 1 (by rfl) ⟨1143881, by rfl⟩ : syracuseStep 1525175 = 2287763) B2287763
theorem B1525355 : Blo 674311 1525355 := bstep (se 1 (by rfl) ⟨1144016, by rfl⟩ : syracuseStep 1525355 = 2288033) B2288033
theorem B2442923 : Blo 674311 2442923 := bstep (se 1 (by rfl) ⟨1832192, by rfl⟩ : syracuseStep 2442923 = 3664385) B3664385
theorem B1525625 : Blo 674311 1525625 := bstep (se 2 (by rfl) ⟨572109, by rfl⟩ : syracuseStep 1525625 = 1144219) B1144219
theorem B5130215 : Blo 674311 5130215 := bstep (se 1 (by rfl) ⟨3847661, by rfl⟩ : syracuseStep 5130215 = 7695323) B7695323
theorem B1526057 : Blo 674311 1526057 := bstep (se 2 (by rfl) ⟨572271, by rfl⟩ : syracuseStep 1526057 = 1144543) B1144543
theorem B674351 : Blo 674311 674351 := bstep (se 1 (by rfl) ⟨505763, by rfl⟩ : syracuseStep 674351 = 1011527) B1011527
theorem B674407 : Blo 674311 674407 := bstep (se 1 (by rfl) ⟨505805, by rfl⟩ : syracuseStep 674407 = 1011611) B1011611
theorem B11717399 : Blo 674311 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B674783 : Blo 674311 674783 := bstep (se 1 (by rfl) ⟨506087, by rfl⟩ : syracuseStep 674783 = 1012175) B1012175
theorem B674811 : Blo 674311 674811 := bstep (se 1 (by rfl) ⟨506108, by rfl⟩ : syracuseStep 674811 = 1012217) B1012217
theorem B674879 : Blo 674311 674879 := bstep (se 1 (by rfl) ⟨506159, by rfl⟩ : syracuseStep 674879 = 1012319) B1012319
theorem B8670361 : Blo 674311 8670361 := bstep (se 2 (by rfl) ⟨3251385, by rfl⟩ : syracuseStep 8670361 = 6502771) B6502771
theorem B11586725 : Blo 674311 11586725 := bstep (se 4 (by rfl) ⟨1086255, by rfl⟩ : syracuseStep 11586725 = 2172511) B2172511
theorem B675199 : Blo 674311 675199 := bstep (se 1 (by rfl) ⟨506399, by rfl⟩ : syracuseStep 675199 = 1012799) B1012799
theorem B675227 : Blo 674311 675227 := bstep (se 1 (by rfl) ⟨506420, by rfl⟩ : syracuseStep 675227 = 1012841) B1012841
theorem B6507965 : Blo 674311 6507965 := bstep (se 3 (by rfl) ⟨1220243, by rfl⟩ : syracuseStep 6507965 = 2440487) B2440487
theorem B675295 : Blo 674311 675295 := bstep (se 1 (by rfl) ⟨506471, by rfl⟩ : syracuseStep 675295 = 1012943) B1012943
theorem B675431 : Blo 674311 675431 := bstep (se 1 (by rfl) ⟨506573, by rfl⟩ : syracuseStep 675431 = 1013147) B1013147
theorem B1625771 : Blo 674311 1625771 := bstep (se 1 (by rfl) ⟨1219328, by rfl⟩ : syracuseStep 1625771 = 2438657) B2438657
theorem B675579 : Blo 674311 675579 := bstep (se 1 (by rfl) ⟨506684, by rfl⟩ : syracuseStep 675579 = 1013369) B1013369
theorem B675647 : Blo 674311 675647 := bstep (se 1 (by rfl) ⟨506735, by rfl⟩ : syracuseStep 675647 = 1013471) B1013471
theorem B675711 : Blo 674311 675711 := bstep (se 1 (by rfl) ⟨506783, by rfl⟩ : syracuseStep 675711 = 1013567) B1013567
theorem B675823 : Blo 674311 675823 := bstep (se 1 (by rfl) ⟨506867, by rfl⟩ : syracuseStep 675823 = 1013735) B1013735
theorem B675835 : Blo 674311 675835 := bstep (se 1 (by rfl) ⟨506876, by rfl⟩ : syracuseStep 675835 = 1013753) B1013753
theorem B6934567 : Blo 674311 6934567 := bstep (se 1 (by rfl) ⟨5200925, by rfl⟩ : syracuseStep 6934567 = 10401851) B10401851
theorem B675903 : Blo 674311 675903 := bstep (se 1 (by rfl) ⟨506927, by rfl⟩ : syracuseStep 675903 = 1013855) B1013855
theorem B675943 : Blo 674311 675943 := bstep (se 1 (by rfl) ⟨506957, by rfl⟩ : syracuseStep 675943 = 1013915) B1013915
theorem B675967 : Blo 674311 675967 := bstep (se 1 (by rfl) ⟨506975, by rfl⟩ : syracuseStep 675967 = 1013951) B1013951
theorem B675995 : Blo 674311 675995 := bstep (se 1 (by rfl) ⟨506996, by rfl⟩ : syracuseStep 675995 = 1013993) B1013993
theorem B2281715 : Blo 674311 2281715 := bstep (se 1 (by rfl) ⟨1711286, by rfl⟩ : syracuseStep 2281715 = 3422573) B3422573
theorem B676199 : Blo 674311 676199 := bstep (se 1 (by rfl) ⟨507149, by rfl⟩ : syracuseStep 676199 = 1014299) B1014299
theorem B676251 : Blo 674311 676251 := bstep (se 1 (by rfl) ⟨507188, by rfl⟩ : syracuseStep 676251 = 1014377) B1014377
theorem B676603 : Blo 674311 676603 := bstep (se 1 (by rfl) ⟨507452, by rfl⟩ : syracuseStep 676603 = 1014905) B1014905
theorem B676671 : Blo 674311 676671 := bstep (se 1 (by rfl) ⟨507503, by rfl⟩ : syracuseStep 676671 = 1015007) B1015007
theorem B676699 : Blo 674311 676699 := bstep (se 1 (by rfl) ⟨507524, by rfl⟩ : syracuseStep 676699 = 1015049) B1015049
theorem B676767 : Blo 674311 676767 := bstep (se 1 (by rfl) ⟨507575, by rfl⟩ : syracuseStep 676767 = 1015151) B1015151
theorem B676847 : Blo 674311 676847 := bstep (se 1 (by rfl) ⟨507635, by rfl⟩ : syracuseStep 676847 = 1015271) B1015271
theorem B676935 : Blo 674311 676935 := bstep (se 1 (by rfl) ⟨507701, by rfl⟩ : syracuseStep 676935 = 1015403) B1015403
theorem B1627231 : Blo 674311 1627231 := bstep (se 1 (by rfl) ⟨1220423, by rfl⟩ : syracuseStep 1627231 = 2440847) B2440847
theorem B677019 : Blo 674311 677019 := bstep (se 1 (by rfl) ⟨507764, by rfl⟩ : syracuseStep 677019 = 1015529) B1015529
theorem B677115 : Blo 674311 677115 := bstep (se 1 (by rfl) ⟨507836, by rfl⟩ : syracuseStep 677115 = 1015673) B1015673
theorem B677183 : Blo 674311 677183 := bstep (se 1 (by rfl) ⟨507887, by rfl⟩ : syracuseStep 677183 = 1015775) B1015775
theorem B677351 : Blo 674311 677351 := bstep (se 1 (by rfl) ⟨508013, by rfl⟩ : syracuseStep 677351 = 1016027) B1016027
theorem B677359 : Blo 674311 677359 := bstep (se 1 (by rfl) ⟨508019, by rfl⟩ : syracuseStep 677359 = 1016039) B1016039
theorem B8246767 : Blo 674311 8246767 := bstep (se 1 (by rfl) ⟨6185075, by rfl⟩ : syracuseStep 8246767 = 12370151) B12370151
theorem B677467 : Blo 674311 677467 := bstep (se 1 (by rfl) ⟨508100, by rfl⟩ : syracuseStep 677467 = 1016201) B1016201
theorem B3430025 : Blo 674311 3430025 := bstep (se 2 (by rfl) ⟨1286259, by rfl⟩ : syracuseStep 3430025 = 2572519) B2572519
theorem B677531 : Blo 674311 677531 := bstep (se 1 (by rfl) ⟨508148, by rfl⟩ : syracuseStep 677531 = 1016297) B1016297
theorem B677615 : Blo 674311 677615 := bstep (se 1 (by rfl) ⟨508211, by rfl⟩ : syracuseStep 677615 = 1016423) B1016423
theorem B2283335 : Blo 674311 2283335 := bstep (se 1 (by rfl) ⟨1712501, by rfl⟩ : syracuseStep 2283335 = 3425003) B3425003
theorem B677703 : Blo 674311 677703 := bstep (se 1 (by rfl) ⟨508277, by rfl⟩ : syracuseStep 677703 = 1016555) B1016555
theorem B677723 : Blo 674311 677723 := bstep (se 1 (by rfl) ⟨508292, by rfl⟩ : syracuseStep 677723 = 1016585) B1016585
theorem B677791 : Blo 674311 677791 := bstep (se 1 (by rfl) ⟨508343, by rfl⟩ : syracuseStep 677791 = 1016687) B1016687
theorem B677959 : Blo 674311 677959 := bstep (se 1 (by rfl) ⟨508469, by rfl⟩ : syracuseStep 677959 = 1016939) B1016939
theorem B678119 : Blo 674311 678119 := bstep (se 1 (by rfl) ⟨508589, by rfl⟩ : syracuseStep 678119 = 1017179) B1017179
theorem B678303 : Blo 674311 678303 := bstep (se 1 (by rfl) ⟨508727, by rfl⟩ : syracuseStep 678303 = 1017455) B1017455
theorem B29678561 : Blo 674311 29678561 := bstep (se 2 (by rfl) ⟨11129460, by rfl⟩ : syracuseStep 29678561 = 22258921) B22258921
theorem B2284523 : Blo 674311 2284523 := bstep (se 1 (by rfl) ⟨1713392, by rfl⟩ : syracuseStep 2284523 = 3426785) B3426785
theorem B5201081 : Blo 674311 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B4120001 : Blo 674311 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B3431969 : Blo 674311 3431969 := bstep (se 2 (by rfl) ⟨1286988, by rfl⟩ : syracuseStep 3431969 = 2573977) B2573977
theorem B4218493 : Blo 674311 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B2286035 : Blo 674311 2286035 := bstep (se 1 (by rfl) ⟨1714526, by rfl⟩ : syracuseStep 2286035 = 3429053) B3429053
theorem B4121263 : Blo 674311 4121263 := bstep (se 1 (by rfl) ⟨3090947, by rfl⟩ : syracuseStep 4121263 = 6181895) B6181895
theorem B1139879 : Blo 674311 1139879 := bstep (se 1 (by rfl) ⟨854909, by rfl⟩ : syracuseStep 1139879 = 1709819) B1709819
theorem B11134199 : Blo 674311 11134199 := bstep (se 1 (by rfl) ⟨8350649, by rfl⟩ : syracuseStep 11134199 = 16701299) B16701299
theorem B1467895 : Blo 674311 1467895 := bstep (se 1 (by rfl) ⟨1100921, by rfl⟩ : syracuseStep 1467895 = 2201843) B2201843
theorem B5924447 : Blo 674311 5924447 := bstep (se 1 (by rfl) ⟨4443335, by rfl⟩ : syracuseStep 5924447 = 8886671) B8886671
theorem B1369993 : Blo 674311 1369993 := bstep (se 2 (by rfl) ⟨513747, by rfl⟩ : syracuseStep 1369993 = 1027495) B1027495
theorem B1140635 : Blo 674311 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B1140763 : Blo 674311 1140763 := bstep (se 1 (by rfl) ⟨855572, by rfl⟩ : syracuseStep 1140763 = 1711145) B1711145
theorem B2058383 : Blo 674311 2058383 := bstep (se 1 (by rfl) ⟨1543787, by rfl⟩ : syracuseStep 2058383 = 3087575) B3087575
theorem B6580673 : Blo 674311 6580673 := bstep (se 2 (by rfl) ⟨2467752, by rfl⟩ : syracuseStep 6580673 = 4935505) B4935505
theorem B5138963 : Blo 674311 5138963 := bstep (se 1 (by rfl) ⟨3854222, by rfl⟩ : syracuseStep 5138963 = 7708445) B7708445
theorem B10414655 : Blo 674311 10414655 := bstep (se 1 (by rfl) ⟨7810991, by rfl⟩ : syracuseStep 10414655 = 15621983) B15621983
theorem B5761925 : Blo 674311 5761925 := bstep (se 4 (by rfl) ⟨540180, by rfl⟩ : syracuseStep 5761925 = 1080361) B1080361
theorem B6482861 : Blo 674311 6482861 := bstep (se 3 (by rfl) ⟨1215536, by rfl⟩ : syracuseStep 6482861 = 2431073) B2431073
theorem B5139935 : Blo 674311 5139935 := bstep (se 1 (by rfl) ⟨3854951, by rfl⟩ : syracuseStep 5139935 = 7709903) B7709903
theorem B1011593 : Blo 674311 1011593 := bstep (se 2 (by rfl) ⟨379347, by rfl⟩ : syracuseStep 1011593 = 758695) B758695
theorem B1011839 : Blo 674311 1011839 := bstep (se 1 (by rfl) ⟨758879, by rfl⟩ : syracuseStep 1011839 = 1517759) B1517759
theorem B1732871 : Blo 674311 1732871 := bstep (se 1 (by rfl) ⟨1299653, by rfl⟩ : syracuseStep 1732871 = 2599307) B2599307
theorem B25981559 : Blo 674311 25981559 := bstep (se 1 (by rfl) ⟨19486169, by rfl⟩ : syracuseStep 25981559 = 38972339) B38972339
theorem B1012475 : Blo 674311 1012475 := bstep (se 1 (by rfl) ⟨759356, by rfl⟩ : syracuseStep 1012475 = 1518713) B1518713
theorem B24671411 : Blo 674311 24671411 := bstep (se 1 (by rfl) ⟨18503558, by rfl⟩ : syracuseStep 24671411 = 37007117) B37007117
theorem B1012919 : Blo 674311 1012919 := bstep (se 1 (by rfl) ⟨759689, by rfl⟩ : syracuseStep 1012919 = 1519379) B1519379
theorem B5141879 : Blo 674311 5141879 := bstep (se 1 (by rfl) ⟨3856409, by rfl⟩ : syracuseStep 5141879 = 7712819) B7712819
theorem B1013159 : Blo 674311 1013159 := bstep (se 1 (by rfl) ⟨759869, by rfl⟩ : syracuseStep 1013159 = 1519739) B1519739
theorem B1930711 : Blo 674311 1930711 := bstep (se 1 (by rfl) ⟨1448033, by rfl⟩ : syracuseStep 1930711 = 2896067) B2896067
theorem B1013339 : Blo 674311 1013339 := bstep (se 1 (by rfl) ⟨760004, by rfl⟩ : syracuseStep 1013339 = 1520009) B1520009
theorem B1832539 : Blo 674311 1832539 := bstep (se 1 (by rfl) ⟨1374404, by rfl⟩ : syracuseStep 1832539 = 2748809) B2748809
theorem B11695769 : Blo 674311 11695769 := bstep (se 2 (by rfl) ⟨4385913, by rfl⟩ : syracuseStep 11695769 = 8771827) B8771827
theorem B1013801 : Blo 674311 1013801 := bstep (se 2 (by rfl) ⟨380175, by rfl⟩ : syracuseStep 1013801 = 760351) B760351
theorem B1013831 : Blo 674311 1013831 := bstep (se 1 (by rfl) ⟨760373, by rfl⟩ : syracuseStep 1013831 = 1520747) B1520747
theorem B5470337 : Blo 674311 5470337 := bstep (se 2 (by rfl) ⟨2051376, by rfl⟩ : syracuseStep 5470337 = 4102753) B4102753
theorem B1014215 : Blo 674311 1014215 := bstep (se 1 (by rfl) ⟨760661, by rfl⟩ : syracuseStep 1014215 = 1521323) B1521323
theorem B1374761 : Blo 674311 1374761 := bstep (se 2 (by rfl) ⟨515535, by rfl⟩ : syracuseStep 1374761 = 1031071) B1031071
theorem B1014431 : Blo 674311 1014431 := bstep (se 1 (by rfl) ⟨760823, by rfl⟩ : syracuseStep 1014431 = 1521647) B1521647
theorem B1014575 : Blo 674311 1014575 := bstep (se 1 (by rfl) ⟨760931, by rfl⟩ : syracuseStep 1014575 = 1521863) B1521863
theorem B3242911 : Blo 674311 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B1440679 : Blo 674311 1440679 := bstep (se 1 (by rfl) ⟨1080509, by rfl⟩ : syracuseStep 1440679 = 2161019) B2161019
theorem B1014695 : Blo 674311 1014695 := bstep (se 1 (by rfl) ⟨761021, by rfl⟩ : syracuseStep 1014695 = 1522043) B1522043
theorem B1014875 : Blo 674311 1014875 := bstep (se 1 (by rfl) ⟨761156, by rfl⟩ : syracuseStep 1014875 = 1522313) B1522313
theorem B2882911 : Blo 674311 2882911 := bstep (se 1 (by rfl) ⟨2162183, by rfl⟩ : syracuseStep 2882911 = 4324367) B4324367
theorem B1015247 : Blo 674311 1015247 := bstep (se 1 (by rfl) ⟨761435, by rfl⟩ : syracuseStep 1015247 = 1522871) B1522871
theorem B2162351 : Blo 674311 2162351 := bstep (se 1 (by rfl) ⟨1621763, by rfl⟩ : syracuseStep 2162351 = 3243527) B3243527
theorem B9731785 : Blo 674311 9731785 := bstep (se 2 (by rfl) ⟨3649419, by rfl⟩ : syracuseStep 9731785 = 7298839) B7298839
theorem B1015631 : Blo 674311 1015631 := bstep (se 1 (by rfl) ⟨761723, by rfl⟩ : syracuseStep 1015631 = 1523447) B1523447
theorem B3342223 : Blo 674311 3342223 := bstep (se 1 (by rfl) ⟨2506667, by rfl⟩ : syracuseStep 3342223 = 5013335) B5013335
theorem B720839 : Blo 674311 720839 := bstep (se 1 (by rfl) ⟨540629, by rfl⟩ : syracuseStep 720839 = 1081259) B1081259
theorem B1015751 : Blo 674311 1015751 := bstep (se 1 (by rfl) ⟨761813, by rfl⟩ : syracuseStep 1015751 = 1523627) B1523627
theorem B2883833 : Blo 674311 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B1016063 : Blo 674311 1016063 := bstep (se 1 (by rfl) ⟨762047, by rfl⟩ : syracuseStep 1016063 = 1524095) B1524095
theorem B1016219 : Blo 674311 1016219 := bstep (se 1 (by rfl) ⟨762164, by rfl⟩ : syracuseStep 1016219 = 1524329) B1524329
theorem B4620989 : Blo 674311 4620989 := bstep (se 3 (by rfl) ⟨866435, by rfl⟩ : syracuseStep 4620989 = 1732871) B1732871
theorem B1016639 : Blo 674311 1016639 := bstep (se 1 (by rfl) ⟨762479, by rfl⟩ : syracuseStep 1016639 = 1524959) B1524959
theorem B1016783 : Blo 674311 1016783 := bstep (se 1 (by rfl) ⟨762587, by rfl⟩ : syracuseStep 1016783 = 1525175) B1525175
theorem B1016873 : Blo 674311 1016873 := bstep (se 2 (by rfl) ⟨381327, by rfl⟩ : syracuseStep 1016873 = 762655) B762655
theorem B1016903 : Blo 674311 1016903 := bstep (se 1 (by rfl) ⟨762677, by rfl⟩ : syracuseStep 1016903 = 1525355) B1525355
theorem B1017083 : Blo 674311 1017083 := bstep (se 1 (by rfl) ⟨762812, by rfl⟩ : syracuseStep 1017083 = 1525625) B1525625
theorem B1017371 : Blo 674311 1017371 := bstep (se 1 (by rfl) ⟨763028, by rfl⟩ : syracuseStep 1017371 = 1526057) B1526057
theorem B1083847 : Blo 674311 1083847 := bstep (se 1 (by rfl) ⟨812885, by rfl⟩ : syracuseStep 1083847 = 1625771) B1625771
theorem B2165363 : Blo 674311 2165363 := bstep (se 1 (by rfl) ⟨1624022, by rfl⟩ : syracuseStep 2165363 = 3248045) B3248045
theorem B1707743 : Blo 674311 1707743 := bstep (se 1 (by rfl) ⟨1280807, by rfl⟩ : syracuseStep 1707743 = 2561615) B2561615
theorem B2166695 : Blo 674311 2166695 := bstep (se 1 (by rfl) ⟨1625021, by rfl⟩ : syracuseStep 2166695 = 3250043) B3250043
theorem B856423 : Blo 674311 856423 := bstep (se 1 (by rfl) ⟨642317, by rfl⟩ : syracuseStep 856423 = 1284635) B1284635
theorem B1708411 : Blo 674311 1708411 := bstep (se 1 (by rfl) ⟨1281308, by rfl⟩ : syracuseStep 1708411 = 2562617) B2562617
theorem B2888207 : Blo 674311 2888207 := bstep (se 1 (by rfl) ⟨2166155, by rfl⟩ : syracuseStep 2888207 = 4332311) B4332311
theorem B13898429 : Blo 674311 13898429 := bstep (se 3 (by rfl) ⟨2605955, by rfl⟩ : syracuseStep 13898429 = 5211911) B5211911
theorem B9246089 : Blo 674311 9246089 := bstep (se 2 (by rfl) ⟨3467283, by rfl⟩ : syracuseStep 9246089 = 6934567) B6934567
theorem B857567 : Blo 674311 857567 := bstep (se 1 (by rfl) ⟨643175, by rfl⟩ : syracuseStep 857567 = 1286351) B1286351
theorem B1447487 : Blo 674311 1447487 := bstep (se 1 (by rfl) ⟨1085615, by rfl⟩ : syracuseStep 1447487 = 2171231) B2171231
theorem B5478025 : Blo 674311 5478025 := bstep (se 2 (by rfl) ⟨2054259, by rfl⟩ : syracuseStep 5478025 = 4108519) B4108519
theorem B759919 : Blo 674311 759919 := bstep (se 1 (by rfl) ⟨569939, by rfl⟩ : syracuseStep 759919 = 1139879) B1139879
theorem B1448239 : Blo 674311 1448239 := bstep (se 1 (by rfl) ⟨1086179, by rfl⟩ : syracuseStep 1448239 = 2172359) B2172359
theorem B1710497 : Blo 674311 1710497 := bstep (se 2 (by rfl) ⟨641436, by rfl⟩ : syracuseStep 1710497 = 1282873) B1282873
theorem B3250601 : Blo 674311 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B760423 : Blo 674311 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B2169641 : Blo 674311 2169641 := bstep (se 2 (by rfl) ⟨813615, by rfl⟩ : syracuseStep 2169641 = 1627231) B1627231
theorem B3841283 : Blo 674311 3841283 := bstep (se 1 (by rfl) ⟨2880962, by rfl⟩ : syracuseStep 3841283 = 5761925) B5761925
theorem B4333337 : Blo 674311 4333337 := bstep (se 2 (by rfl) ⟨1625001, by rfl⟩ : syracuseStep 4333337 = 3250003) B3250003
theorem B4333439 : Blo 674311 4333439 := bstep (se 1 (by rfl) ⟨3250079, by rfl⟩ : syracuseStep 4333439 = 6500159) B6500159
theorem B1712087 : Blo 674311 1712087 := bstep (se 1 (by rfl) ⟨1284065, by rfl⟩ : syracuseStep 1712087 = 2568131) B2568131
theorem B1286761 : Blo 674311 1286761 := bstep (se 2 (by rfl) ⟨482535, by rfl⟩ : syracuseStep 1286761 = 965071) B965071
theorem B1712927 : Blo 674311 1712927 := bstep (se 1 (by rfl) ⟨1284695, by rfl⟩ : syracuseStep 1712927 = 2569391) B2569391
theorem B2565215 : Blo 674311 2565215 := bstep (se 1 (by rfl) ⟨1923911, by rfl⟩ : syracuseStep 2565215 = 3847823) B3847823
theorem B3646891 : Blo 674311 3646891 := bstep (se 1 (by rfl) ⟨2735168, by rfl⟩ : syracuseStep 3646891 = 5470337) B5470337
theorem B3843881 : Blo 674311 3843881 := bstep (se 2 (by rfl) ⟨1441455, by rfl⟩ : syracuseStep 3843881 = 2882911) B2882911
theorem B3418361 : Blo 674311 3418361 := bstep (se 2 (by rfl) ⟨1281885, by rfl⟩ : syracuseStep 3418361 = 2563771) B2563771
theorem B6007081 : Blo 674311 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B1518191 : Blo 674311 1518191 := bstep (se 1 (by rfl) ⟨1138643, by rfl⟩ : syracuseStep 1518191 = 2277287) B2277287
theorem B1518407 : Blo 674311 1518407 := bstep (se 1 (by rfl) ⟨1138805, by rfl⟩ : syracuseStep 1518407 = 2277611) B2277611
theorem B2566991 : Blo 674311 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B7810667 : Blo 674311 7810667 := bstep (se 1 (by rfl) ⟨5858000, by rfl⟩ : syracuseStep 7810667 = 11716001) B11716001
theorem B4337489 : Blo 674311 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B3420143 : Blo 674311 3420143 := bstep (se 1 (by rfl) ⟨2565107, by rfl⟩ : syracuseStep 3420143 = 5130215) B5130215
theorem B3420305 : Blo 674311 3420305 := bstep (se 2 (by rfl) ⟨1282614, by rfl⟩ : syracuseStep 3420305 = 2565229) B2565229
theorem B2896033 : Blo 674311 2896033 := bstep (se 2 (by rfl) ⟨1086012, by rfl⟩ : syracuseStep 2896033 = 2172025) B2172025
theorem B3649769 : Blo 674311 3649769 := bstep (se 2 (by rfl) ⟨1368663, by rfl⟩ : syracuseStep 3649769 = 2737327) B2737327
theorem B7811599 : Blo 674311 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B10990495 : Blo 674311 10990495 := bstep (se 1 (by rfl) ⟨8242871, by rfl⟩ : syracuseStep 10990495 = 16485743) B16485743
theorem B4338643 : Blo 674311 4338643 := bstep (se 1 (by rfl) ⟨3253982, by rfl⟩ : syracuseStep 4338643 = 6507965) B6507965
theorem B3847297 : Blo 674311 3847297 := bstep (se 2 (by rfl) ⟨1442736, by rfl⟩ : syracuseStep 3847297 = 2885473) B2885473
theorem B1521017 : Blo 674311 1521017 := bstep (se 2 (by rfl) ⟨570381, by rfl⟩ : syracuseStep 1521017 = 1140763) B1140763
theorem B1521143 : Blo 674311 1521143 := bstep (se 1 (by rfl) ⟨1140857, by rfl⟩ : syracuseStep 1521143 = 2281715) B2281715
theorem B4929133 : Blo 674311 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B1947863 : Blo 674311 1947863 := bstep (se 1 (by rfl) ⟨1460897, by rfl⟩ : syracuseStep 1947863 = 2921795) B2921795
theorem B1522223 : Blo 674311 1522223 := bstep (se 1 (by rfl) ⟨1141667, by rfl⟩ : syracuseStep 1522223 = 2283335) B2283335
theorem B2276153 : Blo 674311 2276153 := bstep (se 2 (by rfl) ⟨853557, by rfl⟩ : syracuseStep 2276153 = 1707115) B1707115
theorem B1523015 : Blo 674311 1523015 := bstep (se 1 (by rfl) ⟨1142261, by rfl⟩ : syracuseStep 1523015 = 2284523) B2284523
theorem B2277017 : Blo 674311 2277017 := bstep (se 2 (by rfl) ⟨853881, by rfl⟩ : syracuseStep 2277017 = 1707763) B1707763
theorem B1524023 : Blo 674311 1524023 := bstep (se 1 (by rfl) ⟨1143017, by rfl⟩ : syracuseStep 1524023 = 2286035) B2286035
theorem B5489021 : Blo 674311 5489021 := bstep (se 3 (by rfl) ⟨1029191, by rfl⟩ : syracuseStep 5489021 = 2058383) B2058383
theorem B3850739 : Blo 674311 3850739 := bstep (se 1 (by rfl) ⟨2888054, by rfl⟩ : syracuseStep 3850739 = 5776109) B5776109
theorem B3424841 : Blo 674311 3424841 := bstep (se 2 (by rfl) ⟨1284315, by rfl⟩ : syracuseStep 3424841 = 2568631) B2568631
theorem B2278151 : Blo 674311 2278151 := bstep (se 1 (by rfl) ⟨1708613, by rfl⟩ : syracuseStep 2278151 = 3417227) B3417227
theorem B7422799 : Blo 674311 7422799 := bstep (se 1 (by rfl) ⟨5567099, by rfl⟩ : syracuseStep 7422799 = 11134199) B11134199
theorem B3949631 : Blo 674311 3949631 := bstep (se 1 (by rfl) ⟨2962223, by rfl⟩ : syracuseStep 3949631 = 5924447) B5924447
theorem B3425975 : Blo 674311 3425975 := bstep (se 1 (by rfl) ⟨2569481, by rfl⟩ : syracuseStep 3425975 = 5138963) B5138963
theorem B2279231 : Blo 674311 2279231 := bstep (se 1 (by rfl) ⟨1709423, by rfl⟩ : syracuseStep 2279231 = 3418847) B3418847
theorem B2574281 : Blo 674311 2574281 := bstep (se 2 (by rfl) ⟨965355, by rfl⟩ : syracuseStep 2574281 = 1930711) B1930711
theorem B10995689 : Blo 674311 10995689 := bstep (se 2 (by rfl) ⟨4123383, by rfl⟩ : syracuseStep 10995689 = 8246767) B8246767
theorem B2443385 : Blo 674311 2443385 := bstep (se 2 (by rfl) ⟨916269, by rfl⟩ : syracuseStep 2443385 = 1832539) B1832539
theorem B3426623 : Blo 674311 3426623 := bstep (se 1 (by rfl) ⟨2569967, by rfl⟩ : syracuseStep 3426623 = 5139935) B5139935
theorem B8243795 : Blo 674311 8243795 := bstep (se 1 (by rfl) ⟨6182846, by rfl⟩ : syracuseStep 8243795 = 12365693) B12365693
theorem B674395 : Blo 674311 674395 := bstep (se 1 (by rfl) ⟨505796, by rfl⟩ : syracuseStep 674395 = 1011593) B1011593
theorem B674559 : Blo 674311 674559 := bstep (se 1 (by rfl) ⟨505919, by rfl⟩ : syracuseStep 674559 = 1011839) B1011839
theorem B17321039 : Blo 674311 17321039 := bstep (se 1 (by rfl) ⟨12990779, by rfl⟩ : syracuseStep 17321039 = 25981559) B25981559
theorem B674983 : Blo 674311 674983 := bstep (se 1 (by rfl) ⟨506237, by rfl⟩ : syracuseStep 674983 = 1012475) B1012475
theorem B2280635 : Blo 674311 2280635 := bstep (se 1 (by rfl) ⟨1710476, by rfl⟩ : syracuseStep 2280635 = 3420953) B3420953
theorem B3853655 : Blo 674311 3853655 := bstep (se 1 (by rfl) ⟨2890241, by rfl⟩ : syracuseStep 3853655 = 5780483) B5780483
theorem B675279 : Blo 674311 675279 := bstep (se 1 (by rfl) ⟨506459, by rfl⟩ : syracuseStep 675279 = 1012919) B1012919
theorem B3427919 : Blo 674311 3427919 := bstep (se 1 (by rfl) ⟨2570939, by rfl⟩ : syracuseStep 3427919 = 5141879) B5141879
theorem B675439 : Blo 674311 675439 := bstep (se 1 (by rfl) ⟨506579, by rfl⟩ : syracuseStep 675439 = 1013159) B1013159
theorem B675559 : Blo 674311 675559 := bstep (se 1 (by rfl) ⟨506669, by rfl⟩ : syracuseStep 675559 = 1013339) B1013339
theorem B1920905 : Blo 674311 1920905 := bstep (se 2 (by rfl) ⟨720339, by rfl⟩ : syracuseStep 1920905 = 1440679) B1440679
theorem B675867 : Blo 674311 675867 := bstep (se 1 (by rfl) ⟨506900, by rfl⟩ : syracuseStep 675867 = 1013801) B1013801
theorem B675887 : Blo 674311 675887 := bstep (se 1 (by rfl) ⟨506915, by rfl⟩ : syracuseStep 675887 = 1013831) B1013831
theorem B13160537 : Blo 674311 13160537 := bstep (se 2 (by rfl) ⟨4935201, by rfl⟩ : syracuseStep 13160537 = 9870403) B9870403
theorem B1823023 : Blo 674311 1823023 := bstep (se 1 (by rfl) ⟨1367267, by rfl⟩ : syracuseStep 1823023 = 2734535) B2734535
theorem B676143 : Blo 674311 676143 := bstep (se 1 (by rfl) ⟨507107, by rfl⟩ : syracuseStep 676143 = 1014215) B1014215
theorem B676287 : Blo 674311 676287 := bstep (se 1 (by rfl) ⟨507215, by rfl⟩ : syracuseStep 676287 = 1014431) B1014431
theorem B676383 : Blo 674311 676383 := bstep (se 1 (by rfl) ⟨507287, by rfl⟩ : syracuseStep 676383 = 1014575) B1014575
theorem B7721567 : Blo 674311 7721567 := bstep (se 1 (by rfl) ⟨5791175, by rfl⟩ : syracuseStep 7721567 = 11582351) B11582351
theorem B676463 : Blo 674311 676463 := bstep (se 1 (by rfl) ⟨507347, by rfl⟩ : syracuseStep 676463 = 1014695) B1014695
theorem B676583 : Blo 674311 676583 := bstep (se 1 (by rfl) ⟨507437, by rfl⟩ : syracuseStep 676583 = 1014875) B1014875
theorem B5624657 : Blo 674311 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B676831 : Blo 674311 676831 := bstep (se 1 (by rfl) ⟨507623, by rfl⟩ : syracuseStep 676831 = 1015247) B1015247
theorem B1922237 : Blo 674311 1922237 := bstep (se 3 (by rfl) ⟨360419, by rfl⟩ : syracuseStep 1922237 = 720839) B720839
theorem B677087 : Blo 674311 677087 := bstep (se 1 (by rfl) ⟨507815, by rfl⟩ : syracuseStep 677087 = 1015631) B1015631
theorem B677167 : Blo 674311 677167 := bstep (se 1 (by rfl) ⟨507875, by rfl⟩ : syracuseStep 677167 = 1015751) B1015751
theorem B5133617 : Blo 674311 5133617 := bstep (se 2 (by rfl) ⟨1925106, by rfl⟩ : syracuseStep 5133617 = 3850213) B3850213
theorem B677407 : Blo 674311 677407 := bstep (se 1 (by rfl) ⟨508055, by rfl⟩ : syracuseStep 677407 = 1016111) B1016111
theorem B677567 : Blo 674311 677567 := bstep (se 1 (by rfl) ⟨508175, by rfl⟩ : syracuseStep 677567 = 1016351) B1016351
theorem B5134103 : Blo 674311 5134103 := bstep (se 1 (by rfl) ⟨3850577, by rfl⟩ : syracuseStep 5134103 = 7701155) B7701155
theorem B1955623 : Blo 674311 1955623 := bstep (se 1 (by rfl) ⟨1466717, by rfl⟩ : syracuseStep 1955623 = 2933435) B2933435
theorem B678015 : Blo 674311 678015 := bstep (se 1 (by rfl) ⟨508511, by rfl⟩ : syracuseStep 678015 = 1017023) B1017023
theorem B678111 : Blo 674311 678111 := bstep (se 1 (by rfl) ⟨508583, by rfl⟩ : syracuseStep 678111 = 1017167) B1017167
theorem B3660059 : Blo 674311 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B678171 : Blo 674311 678171 := bstep (se 1 (by rfl) ⟨508628, by rfl⟩ : syracuseStep 678171 = 1017257) B1017257
theorem B678271 : Blo 674311 678271 := bstep (se 1 (by rfl) ⟨508703, by rfl⟩ : syracuseStep 678271 = 1017407) B1017407
theorem B678299 : Blo 674311 678299 := bstep (se 1 (by rfl) ⟨508724, by rfl⟩ : syracuseStep 678299 = 1017449) B1017449
theorem B1628615 : Blo 674311 1628615 := bstep (se 1 (by rfl) ⟨1221461, by rfl⟩ : syracuseStep 1628615 = 2442923) B2442923
theorem B1957193 : Blo 674311 1957193 := bstep (se 2 (by rfl) ⟨733947, by rfl⟩ : syracuseStep 1957193 = 1467895) B1467895
theorem B810367 : Blo 674311 810367 := bstep (se 1 (by rfl) ⟨607775, by rfl⟩ : syracuseStep 810367 = 1215551) B1215551
theorem B7724483 : Blo 674311 7724483 := bstep (se 1 (by rfl) ⟨5793362, by rfl⟩ : syracuseStep 7724483 = 11586725) B11586725
theorem B3858029 : Blo 674311 3858029 := bstep (se 3 (by rfl) ⟨723380, by rfl⟩ : syracuseStep 3858029 = 1446761) B1446761
theorem B5856889 : Blo 674311 5856889 := bstep (se 2 (by rfl) ⟨2196333, by rfl⟩ : syracuseStep 5856889 = 4392667) B4392667
theorem B1826657 : Blo 674311 1826657 := bstep (se 2 (by rfl) ⟨684996, by rfl⟩ : syracuseStep 1826657 = 1369993) B1369993
theorem B2285981 : Blo 674311 2285981 := bstep (se 3 (by rfl) ⟨428621, by rfl⟩ : syracuseStep 2285981 = 857243) B857243
theorem B1139359 : Blo 674311 1139359 := bstep (se 1 (by rfl) ⟨854519, by rfl⟩ : syracuseStep 1139359 = 1709039) B1709039
theorem B21980069 : Blo 674311 21980069 := bstep (se 4 (by rfl) ⟨2060631, by rfl⟩ : syracuseStep 21980069 = 4121263) B4121263
theorem B2286683 : Blo 674311 2286683 := bstep (se 1 (by rfl) ⟨1715012, by rfl⟩ : syracuseStep 2286683 = 3430025) B3430025
theorem B37119221 : Blo 674311 37119221 := bstep (se 5 (by rfl) ⟨1739963, by rfl⟩ : syracuseStep 37119221 = 3479927) B3479927
theorem B1926497 : Blo 674311 1926497 := bstep (se 2 (by rfl) ⟨722436, by rfl⟩ : syracuseStep 1926497 = 1444873) B1444873
theorem B11560481 : Blo 674311 11560481 := bstep (se 2 (by rfl) ⟨4335180, by rfl⟩ : syracuseStep 11560481 = 8670361) B8670361
theorem B2320211 : Blo 674311 2320211 := bstep (se 1 (by rfl) ⟨1740158, by rfl⟩ : syracuseStep 2320211 = 3480317) B3480317
theorem B7301087 : Blo 674311 7301087 := bstep (se 1 (by rfl) ⟨5475815, by rfl⟩ : syracuseStep 7301087 = 10951631) B10951631
theorem B19785707 : Blo 674311 19785707 := bstep (se 1 (by rfl) ⟨14839280, by rfl⟩ : syracuseStep 19785707 = 29678561) B29678561
theorem B3467387 : Blo 674311 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B8218883 : Blo 674311 8218883 := bstep (se 1 (by rfl) ⟨6164162, by rfl⟩ : syracuseStep 8218883 = 12328325) B12328325
theorem B2746667 : Blo 674311 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B2287979 : Blo 674311 2287979 := bstep (se 1 (by rfl) ⟨1715984, by rfl⟩ : syracuseStep 2287979 = 3431969) B3431969
theorem B9726479 : Blo 674311 9726479 := bstep (se 1 (by rfl) ⟨7294859, by rfl⟩ : syracuseStep 9726479 = 14589719) B14589719
theorem B7793297 : Blo 674311 7793297 := bstep (se 2 (by rfl) ⟨2922486, by rfl⟩ : syracuseStep 7793297 = 5844973) B5844973
theorem B1142491 : Blo 674311 1142491 := bstep (se 1 (by rfl) ⟨856868, by rfl⟩ : syracuseStep 1142491 = 1713737) B1713737
theorem B8679383 : Blo 674311 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B1011689 : Blo 674311 1011689 := bstep (se 2 (by rfl) ⟨379383, by rfl⟩ : syracuseStep 1011689 = 758767) B758767
theorem B1142761 : Blo 674311 1142761 := bstep (se 2 (by rfl) ⟨428535, by rfl⟩ : syracuseStep 1142761 = 857071) B857071
theorem B10973171 : Blo 674311 10973171 := bstep (se 1 (by rfl) ⟨8229878, by rfl⟩ : syracuseStep 10973171 = 16459757) B16459757
theorem B1011707 : Blo 674311 1011707 := bstep (se 1 (by rfl) ⟨758780, by rfl⟩ : syracuseStep 1011707 = 1517561) B1517561
theorem B1011743 : Blo 674311 1011743 := bstep (se 1 (by rfl) ⟨758807, by rfl⟩ : syracuseStep 1011743 = 1517615) B1517615
theorem B1142815 : Blo 674311 1142815 := bstep (se 1 (by rfl) ⟨857111, by rfl⟩ : syracuseStep 1142815 = 1714223) B1714223
theorem B1011767 : Blo 674311 1011767 := bstep (se 1 (by rfl) ⟨758825, by rfl⟩ : syracuseStep 1011767 = 1517651) B1517651
theorem B4878463 : Blo 674311 4878463 := bstep (se 1 (by rfl) ⟨3658847, by rfl⟩ : syracuseStep 4878463 = 7317695) B7317695
theorem B1011887 : Blo 674311 1011887 := bstep (se 1 (by rfl) ⟨758915, by rfl⟩ : syracuseStep 1011887 = 1517831) B1517831
theorem B1732823 : Blo 674311 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B4387115 : Blo 674311 4387115 := bstep (se 1 (by rfl) ⟨3290336, by rfl⟩ : syracuseStep 4387115 = 6580673) B6580673
theorem B1012091 : Blo 674311 1012091 := bstep (se 1 (by rfl) ⟨759068, by rfl⟩ : syracuseStep 1012091 = 1518137) B1518137
theorem B1929595 : Blo 674311 1929595 := bstep (se 1 (by rfl) ⟨1447196, by rfl⟩ : syracuseStep 1929595 = 2894393) B2894393
theorem B6943103 : Blo 674311 6943103 := bstep (se 1 (by rfl) ⟨5207327, by rfl⟩ : syracuseStep 6943103 = 10414655) B10414655
theorem B4321907 : Blo 674311 4321907 := bstep (se 1 (by rfl) ⟨3241430, by rfl⟩ : syracuseStep 4321907 = 6482861) B6482861
theorem B1012361 : Blo 674311 1012361 := bstep (se 2 (by rfl) ⟨379635, by rfl⟩ : syracuseStep 1012361 = 759271) B759271
theorem B1012571 : Blo 674311 1012571 := bstep (se 1 (by rfl) ⟨759428, by rfl⟩ : syracuseStep 1012571 = 1518857) B1518857
theorem B1012601 : Blo 674311 1012601 := bstep (se 2 (by rfl) ⟨379725, by rfl⟩ : syracuseStep 1012601 = 759451) B759451
theorem B1143929 : Blo 674311 1143929 := bstep (se 2 (by rfl) ⟨428973, by rfl⟩ : syracuseStep 1143929 = 857947) B857947
theorem B685223 : Blo 674311 685223 := bstep (se 1 (by rfl) ⟨513917, by rfl⟩ : syracuseStep 685223 = 1027835) B1027835
theorem B1013231 : Blo 674311 1013231 := bstep (se 1 (by rfl) ⟨759923, by rfl⟩ : syracuseStep 1013231 = 1519847) B1519847
theorem B1013351 : Blo 674311 1013351 := bstep (se 1 (by rfl) ⟨760013, by rfl⟩ : syracuseStep 1013351 = 1520027) B1520027
theorem B8451793 : Blo 674311 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B3897371 : Blo 674311 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B1931303 : Blo 674311 1931303 := bstep (se 1 (by rfl) ⟨1448477, by rfl⟩ : syracuseStep 1931303 = 2896955) B2896955
theorem B1013807 : Blo 674311 1013807 := bstep (se 1 (by rfl) ⟨760355, by rfl⟩ : syracuseStep 1013807 = 1520711) B1520711
theorem B16447607 : Blo 674311 16447607 := bstep (se 1 (by rfl) ⟨12335705, by rfl⟩ : syracuseStep 16447607 = 24671411) B24671411
theorem B3700883 : Blo 674311 3700883 := bstep (se 1 (by rfl) ⟨2775662, by rfl⟩ : syracuseStep 3700883 = 5551325) B5551325
theorem B1013927 : Blo 674311 1013927 := bstep (se 1 (by rfl) ⟨760445, by rfl⟩ : syracuseStep 1013927 = 1520891) B1520891
theorem B1014071 : Blo 674311 1014071 := bstep (se 1 (by rfl) ⟨760553, by rfl⟩ : syracuseStep 1014071 = 1521107) B1521107
theorem B7797179 : Blo 674311 7797179 := bstep (se 1 (by rfl) ⟨5847884, by rfl⟩ : syracuseStep 7797179 = 11695769) B11695769
theorem B1014251 : Blo 674311 1014251 := bstep (se 1 (by rfl) ⟨760688, by rfl⟩ : syracuseStep 1014251 = 1521377) B1521377
theorem B4323881 : Blo 674311 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B3242699 : Blo 674311 3242699 := bstep (se 1 (by rfl) ⟨2432024, by rfl⟩ : syracuseStep 3242699 = 4864049) B4864049
theorem B1014599 : Blo 674311 1014599 := bstep (se 1 (by rfl) ⟨760949, by rfl⟩ : syracuseStep 1014599 = 1521899) B1521899
theorem B916507 : Blo 674311 916507 := bstep (se 1 (by rfl) ⟨687380, by rfl⟩ : syracuseStep 916507 = 1374761) B1374761
theorem B1080631 : Blo 674311 1080631 := bstep (se 1 (by rfl) ⟨810473, by rfl⟩ : syracuseStep 1080631 = 1620947) B1620947
theorem B12975713 : Blo 674311 12975713 := bstep (se 2 (by rfl) ⟨4865892, by rfl⟩ : syracuseStep 12975713 = 9731785) B9731785
theorem B1015433 : Blo 674311 1015433 := bstep (se 2 (by rfl) ⟨380787, by rfl⟩ : syracuseStep 1015433 = 761575) B761575
theorem B1015463 : Blo 674311 1015463 := bstep (se 1 (by rfl) ⟨761597, by rfl⟩ : syracuseStep 1015463 = 1523195) B1523195
theorem B1441567 : Blo 674311 1441567 := bstep (se 1 (by rfl) ⟨1081175, by rfl⟩ : syracuseStep 1441567 = 2162351) B2162351
theorem B1015583 : Blo 674311 1015583 := bstep (se 1 (by rfl) ⟨761687, by rfl⟩ : syracuseStep 1015583 = 1523375) B1523375
theorem B1015643 : Blo 674311 1015643 := bstep (se 1 (by rfl) ⟨761732, by rfl⟩ : syracuseStep 1015643 = 1523465) B1523465
theorem B4456297 : Blo 674311 4456297 := bstep (se 2 (by rfl) ⟨1671111, by rfl⟩ : syracuseStep 4456297 = 3342223) B3342223
theorem B1016015 : Blo 674311 1016015 := bstep (se 1 (by rfl) ⟨762011, by rfl⟩ : syracuseStep 1016015 = 1524023) B1524023
theorem B9897065 : Blo 674311 9897065 := bstep (se 2 (by rfl) ⟨3711399, by rfl⟩ : syracuseStep 9897065 = 7422799) B7422799
theorem B7309045 : Blo 674311 7309045 := bstep (se 5 (by rfl) ⟨342611, by rfl⟩ : syracuseStep 7309045 = 685223) B685223
theorem B1443575 : Blo 674311 1443575 := bstep (se 1 (by rfl) ⟨1082681, by rfl⟩ : syracuseStep 1443575 = 2165363) B2165363
theorem B12322637 : Blo 674311 12322637 := bstep (se 3 (by rfl) ⟨2310494, by rfl⟩ : syracuseStep 12322637 = 4620989) B4620989
theorem B1280603 : Blo 674311 1280603 := bstep (se 1 (by rfl) ⟨960452, by rfl⟩ : syracuseStep 1280603 = 1920905) B1920905
theorem B1444463 : Blo 674311 1444463 := bstep (se 1 (by rfl) ⟨1083347, by rfl⟩ : syracuseStep 1444463 = 2166695) B2166695
theorem B5147711 : Blo 674311 5147711 := bstep (se 1 (by rfl) ⟨3860783, by rfl⟩ : syracuseStep 5147711 = 7721567) B7721567
theorem B1445129 : Blo 674311 1445129 := bstep (se 2 (by rfl) ⟨541923, by rfl⟩ : syracuseStep 1445129 = 1083847) B1083847
theorem B1281491 : Blo 674311 1281491 := bstep (se 1 (by rfl) ⟨961118, by rfl⟩ : syracuseStep 1281491 = 1922237) B1922237
theorem B2167067 : Blo 674311 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B1085743 : Blo 674311 1085743 := bstep (se 1 (by rfl) ⟨814307, by rfl⟩ : syracuseStep 1085743 = 1628615) B1628615
theorem B1446427 : Blo 674311 1446427 := bstep (se 1 (by rfl) ⟨1084820, by rfl⟩ : syracuseStep 1446427 = 2169641) B2169641
theorem B2560855 : Blo 674311 2560855 := bstep (se 1 (by rfl) ⟨1920641, by rfl⟩ : syracuseStep 2560855 = 3841283) B3841283
theorem B5149655 : Blo 674311 5149655 := bstep (se 1 (by rfl) ⟨3862241, by rfl⟩ : syracuseStep 5149655 = 7724483) B7724483
theorem B2888891 : Blo 674311 2888891 := bstep (se 1 (by rfl) ⟨2166668, by rfl⟩ : syracuseStep 2888891 = 4333337) B4333337
theorem B1217771 : Blo 674311 1217771 := bstep (se 1 (by rfl) ⟨913328, by rfl⟩ : syracuseStep 1217771 = 1826657) B1826657
theorem B2888959 : Blo 674311 2888959 := bstep (se 1 (by rfl) ⟨2166719, by rfl⟩ : syracuseStep 2888959 = 4333439) B4333439
theorem B5150141 : Blo 674311 5150141 := bstep (se 3 (by rfl) ⟨965651, by rfl⟩ : syracuseStep 5150141 = 1931303) B1931303
theorem B2430697 : Blo 674311 2430697 := bstep (se 2 (by rfl) ⟨911511, by rfl⟩ : syracuseStep 2430697 = 1823023) B1823023
theorem B14653379 : Blo 674311 14653379 := bstep (se 1 (by rfl) ⟨10990034, by rfl⟩ : syracuseStep 14653379 = 21980069) B21980069
theorem B1710143 : Blo 674311 1710143 := bstep (se 1 (by rfl) ⟨1282607, by rfl⟩ : syracuseStep 1710143 = 2565215) B2565215
theorem B24746147 : Blo 674311 24746147 := bstep (se 1 (by rfl) ⟨18559610, by rfl⟩ : syracuseStep 24746147 = 37119221) B37119221
theorem B1284331 : Blo 674311 1284331 := bstep (se 1 (by rfl) ⟨963248, by rfl⟩ : syracuseStep 1284331 = 1926497) B1926497
theorem B7706987 : Blo 674311 7706987 := bstep (se 1 (by rfl) ⟨5780240, by rfl⟩ : syracuseStep 7706987 = 11560481) B11560481
theorem B2562587 : Blo 674311 2562587 := bstep (se 1 (by rfl) ⟨1921940, by rfl⟩ : syracuseStep 2562587 = 3843881) B3843881
theorem B14653993 : Blo 674311 14653993 := bstep (se 2 (by rfl) ⟨5495247, by rfl⟩ : syracuseStep 14653993 = 10990495) B10990495
theorem B5479255 : Blo 674311 5479255 := bstep (se 1 (by rfl) ⟨4109441, by rfl⟩ : syracuseStep 5479255 = 8218883) B8218883
theorem B1711327 : Blo 674311 1711327 := bstep (se 1 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 1711327 = 2566991) B2566991
theorem B2891659 : Blo 674311 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B7315447 : Blo 674311 7315447 := bstep (se 1 (by rfl) ⟨5486585, by rfl⟩ : syracuseStep 7315447 = 10973171) B10973171
theorem B1155215 : Blo 674311 1155215 := bstep (se 1 (by rfl) ⟨866411, by rfl⟩ : syracuseStep 1155215 = 1732823) B1732823
theorem B2433179 : Blo 674311 2433179 := bstep (se 1 (by rfl) ⟨1824884, by rfl⟩ : syracuseStep 2433179 = 3649769) B3649769
theorem B2924743 : Blo 674311 2924743 := bstep (se 1 (by rfl) ⟨2193557, by rfl⟩ : syracuseStep 2924743 = 4387115) B4387115
theorem B4628735 : Blo 674311 4628735 := bstep (se 1 (by rfl) ⟨3471551, by rfl⟩ : syracuseStep 4628735 = 6943103) B6943103
theorem B762619 : Blo 674311 762619 := bstep (se 1 (by rfl) ⟨571964, by rfl⟩ : syracuseStep 762619 = 1143929) B1143929
theorem B2598247 : Blo 674311 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B1222009 : Blo 674311 1222009 := bstep (se 2 (by rfl) ⟨458253, by rfl⟩ : syracuseStep 1222009 = 916507) B916507
theorem B2467255 : Blo 674311 2467255 := bstep (se 1 (by rfl) ⟨1850441, by rfl⟩ : syracuseStep 2467255 = 3700883) B3700883
theorem B1517435 : Blo 674311 1517435 := bstep (se 1 (by rfl) ⟨1138076, by rfl⟩ : syracuseStep 1517435 = 2276153) B2276153
theorem B7809185 : Blo 674311 7809185 := bstep (se 2 (by rfl) ⟨2928444, by rfl⟩ : syracuseStep 7809185 = 5856889) B5856889
theorem B1518011 : Blo 674311 1518011 := bstep (se 1 (by rfl) ⟨1138508, by rfl⟩ : syracuseStep 1518011 = 2277017) B2277017
theorem B5941729 : Blo 674311 5941729 := bstep (se 2 (by rfl) ⟨2228148, by rfl⟩ : syracuseStep 5941729 = 4456297) B4456297
theorem B2567159 : Blo 674311 2567159 := bstep (se 1 (by rfl) ⟨1925369, by rfl⟩ : syracuseStep 2567159 = 3850739) B3850739
theorem B1518767 : Blo 674311 1518767 := bstep (se 1 (by rfl) ⟨1139075, by rfl⟩ : syracuseStep 1518767 = 2278151) B2278151
theorem B2633087 : Blo 674311 2633087 := bstep (se 1 (by rfl) ⟨1974815, by rfl⟩ : syracuseStep 2633087 = 3949631) B3949631
theorem B1715681 : Blo 674311 1715681 := bstep (se 2 (by rfl) ⟨643380, by rfl⟩ : syracuseStep 1715681 = 1286761) B1286761
theorem B1519145 : Blo 674311 1519145 := bstep (se 2 (by rfl) ⟨569679, by rfl⟩ : syracuseStep 1519145 = 1139359) B1139359
theorem B1519487 : Blo 674311 1519487 := bstep (se 1 (by rfl) ⟨1139615, by rfl⟩ : syracuseStep 1519487 = 2279231) B2279231
theorem B1716187 : Blo 674311 1716187 := bstep (se 1 (by rfl) ⟨1287140, by rfl⟩ : syracuseStep 1716187 = 2574281) B2574281
theorem B4862521 : Blo 674311 4862521 := bstep (se 2 (by rfl) ⟨1823445, by rfl⟩ : syracuseStep 4862521 = 3646891) B3646891
theorem B11547359 : Blo 674311 11547359 := bstep (se 1 (by rfl) ⟨8660519, by rfl⟩ : syracuseStep 11547359 = 17321039) B17321039
theorem B1520423 : Blo 674311 1520423 := bstep (se 1 (by rfl) ⟨1140317, by rfl⟩ : syracuseStep 1520423 = 2280635) B2280635
theorem B2569103 : Blo 674311 2569103 := bstep (se 1 (by rfl) ⟨1926827, by rfl⟩ : syracuseStep 2569103 = 3853655) B3853655
theorem B8009441 : Blo 674311 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B3749771 : Blo 674311 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B3422411 : Blo 674311 3422411 := bstep (se 1 (by rfl) ⟨2566808, by rfl⟩ : syracuseStep 3422411 = 5133617) B5133617
theorem B24656237 : Blo 674311 24656237 := bstep (se 3 (by rfl) ⟨4623044, by rfl⟩ : syracuseStep 24656237 = 9246089) B9246089
theorem B964991 : Blo 674311 964991 := bstep (se 1 (by rfl) ⟨723743, by rfl⟩ : syracuseStep 964991 = 1447487) B1447487
theorem B3422735 : Blo 674311 3422735 := bstep (se 1 (by rfl) ⟨2567051, by rfl⟩ : syracuseStep 3422735 = 5134103) B5134103
theorem B2440039 : Blo 674311 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B1523321 : Blo 674311 1523321 := bstep (se 2 (by rfl) ⟨571245, by rfl⟩ : syracuseStep 1523321 = 1142491) B1142491
theorem B2572019 : Blo 674311 2572019 := bstep (se 1 (by rfl) ⟨1929014, by rfl⟩ : syracuseStep 2572019 = 3858029) B3858029
theorem B1523681 : Blo 674311 1523681 := bstep (se 2 (by rfl) ⟨571380, by rfl⟩ : syracuseStep 1523681 = 1142761) B1142761
theorem B1523753 : Blo 674311 1523753 := bstep (se 2 (by rfl) ⟨571407, by rfl⟩ : syracuseStep 1523753 = 1142815) B1142815
theorem B6504617 : Blo 674311 6504617 := bstep (se 2 (by rfl) ⟨2439231, by rfl⟩ : syracuseStep 6504617 = 4878463) B4878463
theorem B1523987 : Blo 674311 1523987 := bstep (se 1 (by rfl) ⟨1142990, by rfl⟩ : syracuseStep 1523987 = 2285981) B2285981
theorem B2277881 : Blo 674311 2277881 := bstep (se 2 (by rfl) ⟨854205, by rfl⟩ : syracuseStep 2277881 = 1708411) B1708411
theorem B2572793 : Blo 674311 2572793 := bstep (se 2 (by rfl) ⟨964797, by rfl⟩ : syracuseStep 2572793 = 1929595) B1929595
theorem B1524455 : Blo 674311 1524455 := bstep (se 1 (by rfl) ⟨1143341, by rfl⟩ : syracuseStep 1524455 = 2286683) B2286683
theorem B7324445 : Blo 674311 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B20792477 : Blo 674311 20792477 := bstep (se 3 (by rfl) ⟨3898589, by rfl⟩ : syracuseStep 20792477 = 7797179) B7797179
theorem B5784857 : Blo 674311 5784857 := bstep (se 2 (by rfl) ⟨2169321, by rfl⟩ : syracuseStep 5784857 = 4338643) B4338643
theorem B4867391 : Blo 674311 4867391 := bstep (se 1 (by rfl) ⟨3650543, by rfl⟩ : syracuseStep 4867391 = 7301087) B7301087
theorem B13190471 : Blo 674311 13190471 := bstep (se 1 (by rfl) ⟨9892853, by rfl⟩ : syracuseStep 13190471 = 19785707) B19785707
theorem B2311591 : Blo 674311 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B2278907 : Blo 674311 2278907 := bstep (se 1 (by rfl) ⟨1709180, by rfl⟩ : syracuseStep 2278907 = 3418361) B3418361
theorem B5129729 : Blo 674311 5129729 := bstep (se 2 (by rfl) ⟨1923648, by rfl⟩ : syracuseStep 5129729 = 3847297) B3847297
theorem B1525319 : Blo 674311 1525319 := bstep (se 1 (by rfl) ⟨1143989, by rfl⟩ : syracuseStep 1525319 = 2287979) B2287979
theorem B5195531 : Blo 674311 5195531 := bstep (se 1 (by rfl) ⟨3896648, by rfl⟩ : syracuseStep 5195531 = 7793297) B7793297
theorem B6572177 : Blo 674311 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B2607497 : Blo 674311 2607497 := bstep (se 2 (by rfl) ⟨977811, by rfl⟩ : syracuseStep 2607497 = 1955623) B1955623
theorem B5786255 : Blo 674311 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B674459 : Blo 674311 674459 := bstep (se 1 (by rfl) ⟨505844, by rfl⟩ : syracuseStep 674459 = 1011689) B1011689
theorem B2280095 : Blo 674311 2280095 := bstep (se 1 (by rfl) ⟨1710071, by rfl⟩ : syracuseStep 2280095 = 3420143) B3420143
theorem B674471 : Blo 674311 674471 := bstep (se 1 (by rfl) ⟨505853, by rfl⟩ : syracuseStep 674471 = 1011707) B1011707
theorem B674495 : Blo 674311 674495 := bstep (se 1 (by rfl) ⟨505871, by rfl⟩ : syracuseStep 674495 = 1011743) B1011743
theorem B674511 : Blo 674311 674511 := bstep (se 1 (by rfl) ⟨505883, by rfl⟩ : syracuseStep 674511 = 1011767) B1011767
theorem B2280203 : Blo 674311 2280203 := bstep (se 1 (by rfl) ⟨1710152, by rfl⟩ : syracuseStep 2280203 = 3420305) B3420305
theorem B674591 : Blo 674311 674591 := bstep (se 1 (by rfl) ⟨505943, by rfl⟩ : syracuseStep 674591 = 1011887) B1011887
theorem B674727 : Blo 674311 674727 := bstep (se 1 (by rfl) ⟨506045, by rfl⟩ : syracuseStep 674727 = 1012091) B1012091
theorem B674907 : Blo 674311 674907 := bstep (se 1 (by rfl) ⟨506180, by rfl⟩ : syracuseStep 674907 = 1012361) B1012361
theorem B675047 : Blo 674311 675047 := bstep (se 1 (by rfl) ⟨506285, by rfl⟩ : syracuseStep 675047 = 1012571) B1012571
theorem B675067 : Blo 674311 675067 := bstep (se 1 (by rfl) ⟨506300, by rfl⟩ : syracuseStep 675067 = 1012601) B1012601
theorem B675487 : Blo 674311 675487 := bstep (se 1 (by rfl) ⟨506615, by rfl⟩ : syracuseStep 675487 = 1013231) B1013231
theorem B675567 : Blo 674311 675567 := bstep (se 1 (by rfl) ⟨506675, by rfl⟩ : syracuseStep 675567 = 1013351) B1013351
theorem B675871 : Blo 674311 675871 := bstep (se 1 (by rfl) ⟨506903, by rfl⟩ : syracuseStep 675871 = 1013807) B1013807
theorem B10965071 : Blo 674311 10965071 := bstep (se 1 (by rfl) ⟨8223803, by rfl⟩ : syracuseStep 10965071 = 16447607) B16447607
theorem B675951 : Blo 674311 675951 := bstep (se 1 (by rfl) ⟨506963, by rfl⟩ : syracuseStep 675951 = 1013927) B1013927
theorem B1298575 : Blo 674311 1298575 := bstep (se 1 (by rfl) ⟨973931, by rfl⟩ : syracuseStep 1298575 = 1947863) B1947863
theorem B676047 : Blo 674311 676047 := bstep (se 1 (by rfl) ⟨507035, by rfl⟩ : syracuseStep 676047 = 1014071) B1014071
theorem B676167 : Blo 674311 676167 := bstep (se 1 (by rfl) ⟨507125, by rfl⟩ : syracuseStep 676167 = 1014251) B1014251
theorem B676399 : Blo 674311 676399 := bstep (se 1 (by rfl) ⟨507299, by rfl⟩ : syracuseStep 676399 = 1014599) B1014599
theorem B1922089 : Blo 674311 1922089 := bstep (se 2 (by rfl) ⟨720783, by rfl⟩ : syracuseStep 1922089 = 1441567) B1441567
theorem B676955 : Blo 674311 676955 := bstep (se 1 (by rfl) ⟨507716, by rfl⟩ : syracuseStep 676955 = 1015433) B1015433
theorem B676975 : Blo 674311 676975 := bstep (se 1 (by rfl) ⟨507731, by rfl⟩ : syracuseStep 676975 = 1015463) B1015463
theorem B677055 : Blo 674311 677055 := bstep (se 1 (by rfl) ⟨507791, by rfl⟩ : syracuseStep 677055 = 1015583) B1015583
theorem B677095 : Blo 674311 677095 := bstep (se 1 (by rfl) ⟨507821, by rfl⟩ : syracuseStep 677095 = 1015643) B1015643
theorem B1922555 : Blo 674311 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B677375 : Blo 674311 677375 := bstep (se 1 (by rfl) ⟨508031, by rfl⟩ : syracuseStep 677375 = 1016063) B1016063
theorem B3659347 : Blo 674311 3659347 := bstep (se 1 (by rfl) ⟨2744510, by rfl⟩ : syracuseStep 3659347 = 5489021) B5489021
theorem B677479 : Blo 674311 677479 := bstep (se 1 (by rfl) ⟨508109, by rfl⟩ : syracuseStep 677479 = 1016219) B1016219
theorem B2283227 : Blo 674311 2283227 := bstep (se 1 (by rfl) ⟨1712420, by rfl⟩ : syracuseStep 2283227 = 3424841) B3424841
theorem B677759 : Blo 674311 677759 := bstep (se 1 (by rfl) ⟨508319, by rfl⟩ : syracuseStep 677759 = 1016639) B1016639
theorem B677855 : Blo 674311 677855 := bstep (se 1 (by rfl) ⟨508391, by rfl⟩ : syracuseStep 677855 = 1016783) B1016783
theorem B677915 : Blo 674311 677915 := bstep (se 1 (by rfl) ⟨508436, by rfl⟩ : syracuseStep 677915 = 1016873) B1016873
theorem B677935 : Blo 674311 677935 := bstep (se 1 (by rfl) ⟨508451, by rfl⟩ : syracuseStep 677935 = 1016903) B1016903
theorem B678055 : Blo 674311 678055 := bstep (se 1 (by rfl) ⟨508541, by rfl⟩ : syracuseStep 678055 = 1017083) B1017083
theorem B678247 : Blo 674311 678247 := bstep (se 1 (by rfl) ⟨508685, by rfl⟩ : syracuseStep 678247 = 1017371) B1017371
theorem B2283983 : Blo 674311 2283983 := bstep (se 1 (by rfl) ⟨1712987, by rfl⟩ : syracuseStep 2283983 = 3425975) B3425975
theorem B7330459 : Blo 674311 7330459 := bstep (se 1 (by rfl) ⟨5497844, by rfl⟩ : syracuseStep 7330459 = 10995689) B10995689
theorem B1628923 : Blo 674311 1628923 := bstep (se 1 (by rfl) ⟨1221692, by rfl⟩ : syracuseStep 1628923 = 2443385) B2443385
theorem B2284415 : Blo 674311 2284415 := bstep (se 1 (by rfl) ⟨1713311, by rfl⟩ : syracuseStep 2284415 = 3426623) B3426623
theorem B5495863 : Blo 674311 5495863 := bstep (se 1 (by rfl) ⟨4121897, by rfl⟩ : syracuseStep 5495863 = 8243795) B8243795
theorem B2285279 : Blo 674311 2285279 := bstep (se 1 (by rfl) ⟨1713959, by rfl⟩ : syracuseStep 2285279 = 3427919) B3427919
theorem B1138495 : Blo 674311 1138495 := bstep (se 1 (by rfl) ⟨853871, by rfl⟩ : syracuseStep 1138495 = 1707743) B1707743
theorem B8773691 : Blo 674311 8773691 := bstep (se 1 (by rfl) ⟨6580268, by rfl⟩ : syracuseStep 8773691 = 13160537) B13160537
theorem B1925471 : Blo 674311 1925471 := bstep (se 1 (by rfl) ⟨1444103, by rfl⟩ : syracuseStep 1925471 = 2888207) B2888207
theorem B9265619 : Blo 674311 9265619 := bstep (se 1 (by rfl) ⟨6949214, by rfl⟩ : syracuseStep 9265619 = 13898429) B13898429
theorem B2286845 : Blo 674311 2286845 := bstep (se 3 (by rfl) ⟨428783, by rfl⟩ : syracuseStep 2286845 = 857567) B857567
theorem B1140331 : Blo 674311 1140331 := bstep (se 1 (by rfl) ⟨855248, by rfl⟩ : syracuseStep 1140331 = 1710497) B1710497
theorem B1304795 : Blo 674311 1304795 := bstep (se 1 (by rfl) ⟨978596, by rfl⟩ : syracuseStep 1304795 = 1957193) B1957193
theorem B6187229 : Blo 674311 6187229 := bstep (se 3 (by rfl) ⟨1160105, by rfl⟩ : syracuseStep 6187229 = 2320211) B2320211
theorem B1141391 : Blo 674311 1141391 := bstep (se 1 (by rfl) ⟨856043, by rfl⟩ : syracuseStep 1141391 = 1712087) B1712087
theorem B3861377 : Blo 674311 3861377 := bstep (se 2 (by rfl) ⟨1448016, by rfl⟩ : syracuseStep 3861377 = 2896033) B2896033
theorem B1141897 : Blo 674311 1141897 := bstep (se 2 (by rfl) ⟨428211, by rfl⟩ : syracuseStep 1141897 = 856423) B856423
theorem B1141951 : Blo 674311 1141951 := bstep (se 1 (by rfl) ⟨856463, by rfl⟩ : syracuseStep 1141951 = 1712927) B1712927
theorem B10415465 : Blo 674311 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B6484319 : Blo 674311 6484319 := bstep (se 1 (by rfl) ⟨4863239, by rfl⟩ : syracuseStep 6484319 = 9726479) B9726479
theorem B1012127 : Blo 674311 1012127 := bstep (se 1 (by rfl) ⟨759095, by rfl⟩ : syracuseStep 1012127 = 1518191) B1518191
theorem B1012271 : Blo 674311 1012271 := bstep (se 1 (by rfl) ⟨759203, by rfl⟩ : syracuseStep 1012271 = 1518407) B1518407
theorem B4321957 : Blo 674311 4321957 := bstep (se 4 (by rfl) ⟨405183, by rfl⟩ : syracuseStep 4321957 = 810367) B810367
theorem B7304033 : Blo 674311 7304033 := bstep (se 2 (by rfl) ⟨2739012, by rfl⟩ : syracuseStep 7304033 = 5478025) B5478025
theorem B11269057 : Blo 674311 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B5207111 : Blo 674311 5207111 := bstep (se 1 (by rfl) ⟨3905333, by rfl⟩ : syracuseStep 5207111 = 7810667) B7810667
theorem B1013225 : Blo 674311 1013225 := bstep (se 2 (by rfl) ⟨379959, by rfl⟩ : syracuseStep 1013225 = 759919) B759919
theorem B1930985 : Blo 674311 1930985 := bstep (se 2 (by rfl) ⟨724119, by rfl⟩ : syracuseStep 1930985 = 1448239) B1448239
theorem B2881271 : Blo 674311 2881271 := bstep (se 1 (by rfl) ⟨2160953, by rfl⟩ : syracuseStep 2881271 = 4321907) B4321907
theorem B1013897 : Blo 674311 1013897 := bstep (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) B760423
theorem B1014011 : Blo 674311 1014011 := bstep (se 1 (by rfl) ⟨760508, by rfl⟩ : syracuseStep 1014011 = 1521017) B1521017
theorem B1014095 : Blo 674311 1014095 := bstep (se 1 (by rfl) ⟨760571, by rfl⟩ : syracuseStep 1014095 = 1521143) B1521143
theorem B2882587 : Blo 674311 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B1014815 : Blo 674311 1014815 := bstep (se 1 (by rfl) ⟨761111, by rfl⟩ : syracuseStep 1014815 = 1522223) B1522223
theorem B1440841 : Blo 674311 1440841 := bstep (se 2 (by rfl) ⟨540315, by rfl⟩ : syracuseStep 1440841 = 1080631) B1080631
theorem B2161799 : Blo 674311 2161799 := bstep (se 1 (by rfl) ⟨1621349, by rfl⟩ : syracuseStep 2161799 = 3242699) B3242699
theorem B1015343 : Blo 674311 1015343 := bstep (se 1 (by rfl) ⟨761507, by rfl⟩ : syracuseStep 1015343 = 1523015) B1523015
theorem B8650475 : Blo 674311 8650475 := bstep (se 1 (by rfl) ⟨6487856, by rfl⟩ : syracuseStep 8650475 = 12975713) B12975713
theorem B1015835 : Blo 674311 1015835 := bstep (se 1 (by rfl) ⟨761876, by rfl⟩ : syracuseStep 1015835 = 1523753) B1523753
theorem B23396509 : Blo 674311 23396509 := bstep (se 3 (by rfl) ⟨4386845, by rfl⟩ : syracuseStep 23396509 = 8773691) B8773691
theorem B1015991 : Blo 674311 1015991 := bstep (se 1 (by rfl) ⟨761993, by rfl⟩ : syracuseStep 1015991 = 1523987) B1523987
theorem B3899657 : Blo 674311 3899657 := bstep (se 2 (by rfl) ⟨1462371, by rfl⟩ : syracuseStep 3899657 = 2924743) B2924743
theorem B1016303 : Blo 674311 1016303 := bstep (se 1 (by rfl) ⟨762227, by rfl⟩ : syracuseStep 1016303 = 1524455) B1524455
theorem B4882963 : Blo 674311 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B13861651 : Blo 674311 13861651 := bstep (se 1 (by rfl) ⟨10396238, by rfl⟩ : syracuseStep 13861651 = 20792477) B20792477
theorem B1016825 : Blo 674311 1016825 := bstep (se 2 (by rfl) ⟨381309, by rfl⟩ : syracuseStep 1016825 = 762619) B762619
theorem B1016879 : Blo 674311 1016879 := bstep (se 1 (by rfl) ⟨762659, by rfl⟩ : syracuseStep 1016879 = 1525319) B1525319
theorem B1738331 : Blo 674311 1738331 := bstep (se 1 (by rfl) ⟨1303748, by rfl⟩ : syracuseStep 1738331 = 2607497) B2607497
theorem B853735 : Blo 674311 853735 := bstep (se 1 (by rfl) ⟨640301, by rfl⟩ : syracuseStep 853735 = 1280603) B1280603
theorem B3082121 : Blo 674311 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B854327 : Blo 674311 854327 := bstep (se 1 (by rfl) ⟨640745, by rfl⟩ : syracuseStep 854327 = 1281491) B1281491
theorem B7310047 : Blo 674311 7310047 := bstep (se 1 (by rfl) ⟨5482535, by rfl⟩ : syracuseStep 7310047 = 10965071) B10965071
theorem B1444711 : Blo 674311 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B12979709 : Blo 674311 12979709 := bstep (se 3 (by rfl) ⟨2433695, by rfl⟩ : syracuseStep 12979709 = 4867391) B4867391
theorem B9768919 : Blo 674311 9768919 := bstep (se 1 (by rfl) ⟨7326689, by rfl⟩ : syracuseStep 9768919 = 14653379) B14653379
theorem B1708391 : Blo 674311 1708391 := bstep (se 1 (by rfl) ⟨1281293, by rfl⟩ : syracuseStep 1708391 = 2562587) B2562587
theorem B9999389 : Blo 674311 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B3085823 : Blo 674311 3085823 := bstep (se 1 (by rfl) ⟨2314367, by rfl⟩ : syracuseStep 3085823 = 4628735) B4628735
theorem B3414473 : Blo 674311 3414473 := bstep (se 2 (by rfl) ⟨1280427, by rfl⟩ : syracuseStep 3414473 = 2560855) B2560855
theorem B2562785 : Blo 674311 2562785 := bstep (se 2 (by rfl) ⟨961044, by rfl⟩ : syracuseStep 2562785 = 1922089) B1922089
theorem B760927 : Blo 674311 760927 := bstep (se 1 (by rfl) ⟨570695, by rfl⟩ : syracuseStep 760927 = 1141391) B1141391
theorem B1711439 : Blo 674311 1711439 := bstep (se 1 (by rfl) ⟨1283579, by rfl⟩ : syracuseStep 1711439 = 2567159) B2567159
theorem B1712441 : Blo 674311 1712441 := bstep (se 2 (by rfl) ⟨642165, by rfl⟩ : syracuseStep 1712441 = 1284331) B1284331
theorem B1712735 : Blo 674311 1712735 := bstep (se 1 (by rfl) ⟨1284551, by rfl⟩ : syracuseStep 1712735 = 2569103) B2569103
theorem B19538657 : Blo 674311 19538657 := bstep (se 2 (by rfl) ⟨7326996, by rfl⟩ : syracuseStep 19538657 = 14653993) B14653993
theorem B9773945 : Blo 674311 9773945 := bstep (se 2 (by rfl) ⟨3665229, by rfl⟩ : syracuseStep 9773945 = 7330459) B7330459
theorem B2171897 : Blo 674311 2171897 := bstep (se 2 (by rfl) ⟨814461, by rfl⟩ : syracuseStep 2171897 = 1628923) B1628923
theorem B3253385 : Blo 674311 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B1287323 : Blo 674311 1287323 := bstep (se 1 (by rfl) ⟨965492, by rfl⟩ : syracuseStep 1287323 = 1930985) B1930985
theorem B3843449 : Blo 674311 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B1517993 : Blo 674311 1517993 := bstep (se 2 (by rfl) ⟨569247, by rfl⟩ : syracuseStep 1517993 = 1138495) B1138495
theorem B1714679 : Blo 674311 1714679 := bstep (se 1 (by rfl) ⟨1286009, by rfl⟩ : syracuseStep 1714679 = 2572019) B2572019
theorem B4336411 : Blo 674311 4336411 := bstep (se 1 (by rfl) ⟨3252308, by rfl⟩ : syracuseStep 4336411 = 6504617) B6504617
theorem B1518587 : Blo 674311 1518587 := bstep (se 1 (by rfl) ⟨1138940, by rfl⟩ : syracuseStep 1518587 = 2277881) B2277881
theorem B1715195 : Blo 674311 1715195 := bstep (se 1 (by rfl) ⟨1286396, by rfl⟩ : syracuseStep 1715195 = 2572793) B2572793
theorem B6598043 : Blo 674311 6598043 := bstep (se 1 (by rfl) ⟨4948532, by rfl⟩ : syracuseStep 6598043 = 9897065) B9897065
theorem B6925733 : Blo 674311 6925733 := bstep (se 4 (by rfl) ⟨649287, by rfl⟩ : syracuseStep 6925733 = 1298575) B1298575
theorem B8793647 : Blo 674311 8793647 := bstep (se 1 (by rfl) ⟨6595235, by rfl⟩ : syracuseStep 8793647 = 13190471) B13190471
theorem B1519271 : Blo 674311 1519271 := bstep (se 1 (by rfl) ⟨1139453, by rfl⟩ : syracuseStep 1519271 = 2278907) B2278907
theorem B3419819 : Blo 674311 3419819 := bstep (se 1 (by rfl) ⟨2564864, by rfl⟩ : syracuseStep 3419819 = 5129729) B5129729
theorem B962383 : Blo 674311 962383 := bstep (se 1 (by rfl) ⟨721787, by rfl⟩ : syracuseStep 962383 = 1443575) B1443575
theorem B962975 : Blo 674311 962975 := bstep (se 1 (by rfl) ⟨722231, by rfl⟩ : syracuseStep 962975 = 1444463) B1444463
theorem B1520063 : Blo 674311 1520063 := bstep (se 1 (by rfl) ⟨1140047, by rfl⟩ : syracuseStep 1520063 = 2280095) B2280095
theorem B1520135 : Blo 674311 1520135 := bstep (se 1 (by rfl) ⟨1140101, by rfl⟩ : syracuseStep 1520135 = 2280203) B2280203
theorem B3289673 : Blo 674311 3289673 := bstep (se 2 (by rfl) ⟨1233627, by rfl⟩ : syracuseStep 3289673 = 2467255) B2467255
theorem B1520441 : Blo 674311 1520441 := bstep (se 2 (by rfl) ⟨570165, by rfl⟩ : syracuseStep 1520441 = 1140331) B1140331
theorem B963419 : Blo 674311 963419 := bstep (se 1 (by rfl) ⟨722564, by rfl⟩ : syracuseStep 963419 = 1445129) B1445129
theorem B9745393 : Blo 674311 9745393 := bstep (se 2 (by rfl) ⟨3654522, by rfl⟩ : syracuseStep 9745393 = 7309045) B7309045
theorem B7714277 : Blo 674311 7714277 := bstep (se 4 (by rfl) ⟨723213, by rfl⟩ : syracuseStep 7714277 = 1446427) B1446427
theorem B1522151 : Blo 674311 1522151 := bstep (se 1 (by rfl) ⟨1141613, by rfl⟩ : syracuseStep 1522151 = 2283227) B2283227
theorem B5126813 : Blo 674311 5126813 := bstep (se 3 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 5126813 = 1922555) B1922555
theorem B16497431 : Blo 674311 16497431 := bstep (se 1 (by rfl) ⟨12373073, by rfl⟩ : syracuseStep 16497431 = 24746147) B24746147
theorem B1522529 : Blo 674311 1522529 := bstep (se 2 (by rfl) ⟨570948, by rfl⟩ : syracuseStep 1522529 = 1141897) B1141897
theorem B1522601 : Blo 674311 1522601 := bstep (se 2 (by rfl) ⟨570975, by rfl⟩ : syracuseStep 1522601 = 1141951) B1141951
theorem B1522655 : Blo 674311 1522655 := bstep (se 1 (by rfl) ⟨1141991, by rfl⟩ : syracuseStep 1522655 = 2283983) B2283983
theorem B1522943 : Blo 674311 1522943 := bstep (se 1 (by rfl) ⟨1142207, by rfl⟩ : syracuseStep 1522943 = 2284415) B2284415
theorem B1523519 : Blo 674311 1523519 := bstep (se 1 (by rfl) ⟨1142639, by rfl⟩ : syracuseStep 1523519 = 2285279) B2285279
theorem B770143 : Blo 674311 770143 := bstep (se 1 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 770143 = 1155215) B1155215
theorem B1622119 : Blo 674311 1622119 := bstep (se 1 (by rfl) ⟨1216589, by rfl⟩ : syracuseStep 1622119 = 2433179) B2433179
theorem B6177079 : Blo 674311 6177079 := bstep (se 1 (by rfl) ⟨4632809, by rfl⟩ : syracuseStep 6177079 = 9265619) B9265619
theorem B1524563 : Blo 674311 1524563 := bstep (se 1 (by rfl) ⟨1143422, by rfl⟩ : syracuseStep 1524563 = 2286845) B2286845
theorem B2573309 : Blo 674311 2573309 := bstep (se 3 (by rfl) ⟨482495, by rfl⟩ : syracuseStep 2573309 = 964991) B964991
theorem B15025409 : Blo 674311 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B869863 : Blo 674311 869863 := bstep (se 1 (by rfl) ⟨652397, by rfl⟩ : syracuseStep 869863 = 1304795) B1304795
theorem B3851945 : Blo 674311 3851945 := bstep (se 2 (by rfl) ⟨1444479, by rfl⟩ : syracuseStep 3851945 = 2888959) B2888959
theorem B2574251 : Blo 674311 2574251 := bstep (se 1 (by rfl) ⟨1930688, by rfl⟩ : syracuseStep 2574251 = 3861377) B3861377
theorem B1755391 : Blo 674311 1755391 := bstep (se 1 (by rfl) ⟨1316543, by rfl⟩ : syracuseStep 1755391 = 2633087) B2633087
theorem B674751 : Blo 674311 674751 := bstep (se 1 (by rfl) ⟨506063, by rfl⟩ : syracuseStep 674751 = 1012127) B1012127
theorem B674847 : Blo 674311 674847 := bstep (se 1 (by rfl) ⟨506135, by rfl⟩ : syracuseStep 674847 = 1012271) B1012271
theorem B4869355 : Blo 674311 4869355 := bstep (se 1 (by rfl) ⟨3652016, by rfl⟩ : syracuseStep 4869355 = 7304033) B7304033
theorem B675483 : Blo 674311 675483 := bstep (se 1 (by rfl) ⟨506612, by rfl⟩ : syracuseStep 675483 = 1013225) B1013225
theorem B1920847 : Blo 674311 1920847 := bstep (se 1 (by rfl) ⟨1440635, by rfl⟩ : syracuseStep 1920847 = 2881271) B2881271
theorem B7327817 : Blo 674311 7327817 := bstep (se 2 (by rfl) ⟨2747931, by rfl⟩ : syracuseStep 7327817 = 5495863) B5495863
theorem B675931 : Blo 674311 675931 := bstep (se 1 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 675931 = 1013897) B1013897
theorem B1921121 : Blo 674311 1921121 := bstep (se 2 (by rfl) ⟨720420, by rfl⟩ : syracuseStep 1921121 = 1440841) B1440841
theorem B2281607 : Blo 674311 2281607 := bstep (se 1 (by rfl) ⟨1711205, by rfl⟩ : syracuseStep 2281607 = 3422411) B3422411
theorem B676007 : Blo 674311 676007 := bstep (se 1 (by rfl) ⟨507005, by rfl⟩ : syracuseStep 676007 = 1014011) B1014011
theorem B676063 : Blo 674311 676063 := bstep (se 1 (by rfl) ⟨507047, by rfl⟩ : syracuseStep 676063 = 1014095) B1014095
theorem B16437491 : Blo 674311 16437491 := bstep (se 1 (by rfl) ⟨12328118, by rfl⟩ : syracuseStep 16437491 = 24656237) B24656237
theorem B2281769 : Blo 674311 2281769 := bstep (se 2 (by rfl) ⟨855663, by rfl⟩ : syracuseStep 2281769 = 1711327) B1711327
theorem B2281823 : Blo 674311 2281823 := bstep (se 1 (by rfl) ⟨1711367, by rfl⟩ : syracuseStep 2281823 = 3422735) B3422735
theorem B676543 : Blo 674311 676543 := bstep (se 1 (by rfl) ⟨507407, by rfl⟩ : syracuseStep 676543 = 1014815) B1014815
theorem B676895 : Blo 674311 676895 := bstep (se 1 (by rfl) ⟨507671, by rfl⟩ : syracuseStep 676895 = 1015343) B1015343
theorem B3855545 : Blo 674311 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B9753929 : Blo 674311 9753929 := bstep (se 2 (by rfl) ⟨3657723, by rfl⟩ : syracuseStep 9753929 = 7315447) B7315447
theorem B677343 : Blo 674311 677343 := bstep (se 1 (by rfl) ⟨508007, by rfl⟩ : syracuseStep 677343 = 1016015) B1016015
theorem B3856571 : Blo 674311 3856571 := bstep (se 1 (by rfl) ⟨2892428, by rfl⟩ : syracuseStep 3856571 = 5784857) B5784857
theorem B5134589 : Blo 674311 5134589 := bstep (se 3 (by rfl) ⟨962735, by rfl⟩ : syracuseStep 5134589 = 1925471) B1925471
theorem B3463687 : Blo 674311 3463687 := bstep (se 1 (by rfl) ⟨2597765, by rfl⟩ : syracuseStep 3463687 = 5195531) B5195531
theorem B8215091 : Blo 674311 8215091 := bstep (se 1 (by rfl) ⟨6161318, by rfl⟩ : syracuseStep 8215091 = 12322637) B12322637
theorem B4381451 : Blo 674311 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B5790629 : Blo 674311 5790629 := bstep (se 4 (by rfl) ⟨542871, by rfl⟩ : syracuseStep 5790629 = 1085743) B1085743
theorem B3857503 : Blo 674311 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B3464329 : Blo 674311 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B3431807 : Blo 674311 3431807 := bstep (se 1 (by rfl) ⟨2573855, by rfl⟩ : syracuseStep 3431807 = 5147711) B5147711
theorem B7922305 : Blo 674311 7922305 := bstep (se 2 (by rfl) ⟨2970864, by rfl⟩ : syracuseStep 7922305 = 5941729) B5941729
theorem B3433103 : Blo 674311 3433103 := bstep (se 1 (by rfl) ⟨2574827, by rfl⟩ : syracuseStep 3433103 = 5149655) B5149655
theorem B1925927 : Blo 674311 1925927 := bstep (se 1 (by rfl) ⟨1444445, by rfl⟩ : syracuseStep 1925927 = 2888891) B2888891
theorem B811847 : Blo 674311 811847 := bstep (se 1 (by rfl) ⟨608885, by rfl⟩ : syracuseStep 811847 = 1217771) B1217771
theorem B3433427 : Blo 674311 3433427 := bstep (se 1 (by rfl) ⟨2575070, by rfl⟩ : syracuseStep 3433427 = 5150141) B5150141
theorem B1140095 : Blo 674311 1140095 := bstep (se 1 (by rfl) ⟨855071, by rfl⟩ : syracuseStep 1140095 = 1710143) B1710143
theorem B5137991 : Blo 674311 5137991 := bstep (se 1 (by rfl) ⟨3853493, by rfl⟩ : syracuseStep 5137991 = 7706987) B7706987
theorem B29222693 : Blo 674311 29222693 := bstep (se 4 (by rfl) ⟨2739627, by rfl⟩ : syracuseStep 29222693 = 5479255) B5479255
theorem B2288249 : Blo 674311 2288249 := bstep (se 2 (by rfl) ⟨858093, by rfl⟩ : syracuseStep 2288249 = 1716187) B1716187
theorem B6483361 : Blo 674311 6483361 := bstep (se 2 (by rfl) ⟨2431260, by rfl⟩ : syracuseStep 6483361 = 4862521) B4862521
theorem B5762609 : Blo 674311 5762609 := bstep (se 2 (by rfl) ⟨2160978, by rfl⟩ : syracuseStep 5762609 = 4321957) B4321957
theorem B1011623 : Blo 674311 1011623 := bstep (se 1 (by rfl) ⟨758717, by rfl⟩ : syracuseStep 1011623 = 1517435) B1517435
theorem B5206123 : Blo 674311 5206123 := bstep (se 1 (by rfl) ⟨3904592, by rfl⟩ : syracuseStep 5206123 = 7809185) B7809185
theorem B4124819 : Blo 674311 4124819 := bstep (se 1 (by rfl) ⟨3093614, by rfl⟩ : syracuseStep 4124819 = 6187229) B6187229
theorem B1012007 : Blo 674311 1012007 := bstep (se 1 (by rfl) ⟨759005, by rfl⟩ : syracuseStep 1012007 = 1518011) B1518011
theorem B6517381 : Blo 674311 6517381 := bstep (se 4 (by rfl) ⟨611004, by rfl⟩ : syracuseStep 6517381 = 1222009) B1222009
theorem B4879129 : Blo 674311 4879129 := bstep (se 2 (by rfl) ⟨1829673, by rfl⟩ : syracuseStep 4879129 = 3659347) B3659347
theorem B1012511 : Blo 674311 1012511 := bstep (se 1 (by rfl) ⟨759383, by rfl⟩ : syracuseStep 1012511 = 1518767) B1518767
theorem B6943643 : Blo 674311 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B3240929 : Blo 674311 3240929 := bstep (se 2 (by rfl) ⟨1215348, by rfl⟩ : syracuseStep 3240929 = 2430697) B2430697
theorem B1143787 : Blo 674311 1143787 := bstep (se 1 (by rfl) ⟨857840, by rfl⟩ : syracuseStep 1143787 = 1715681) B1715681
theorem B1012763 : Blo 674311 1012763 := bstep (se 1 (by rfl) ⟨759572, by rfl⟩ : syracuseStep 1012763 = 1519145) B1519145
theorem B1012991 : Blo 674311 1012991 := bstep (se 1 (by rfl) ⟨759743, by rfl⟩ : syracuseStep 1012991 = 1519487) B1519487
theorem B4322879 : Blo 674311 4322879 := bstep (se 1 (by rfl) ⟨3242159, by rfl⟩ : syracuseStep 4322879 = 6484319) B6484319
theorem B7698239 : Blo 674311 7698239 := bstep (se 1 (by rfl) ⟨5773679, by rfl⟩ : syracuseStep 7698239 = 11547359) B11547359
theorem B1013615 : Blo 674311 1013615 := bstep (se 1 (by rfl) ⟨760211, by rfl⟩ : syracuseStep 1013615 = 1520423) B1520423
theorem B3471407 : Blo 674311 3471407 := bstep (se 1 (by rfl) ⟨2603555, by rfl⟩ : syracuseStep 3471407 = 5207111) B5207111
theorem B5339627 : Blo 674311 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B1441199 : Blo 674311 1441199 := bstep (se 1 (by rfl) ⟨1080899, by rfl⟩ : syracuseStep 1441199 = 2161799) B2161799
theorem B1015547 : Blo 674311 1015547 := bstep (se 1 (by rfl) ⟨761660, by rfl⟩ : syracuseStep 1015547 = 1523321) B1523321
theorem B5766983 : Blo 674311 5766983 := bstep (se 1 (by rfl) ⟨4325237, by rfl⟩ : syracuseStep 5766983 = 8650475) B8650475
theorem B1015787 : Blo 674311 1015787 := bstep (se 1 (by rfl) ⟨761840, by rfl⟩ : syracuseStep 1015787 = 1523681) B1523681
theorem B2162825 : Blo 674311 2162825 := bstep (se 2 (by rfl) ⟨811059, by rfl⟩ : syracuseStep 2162825 = 1622119) B1622119
theorem B1016375 : Blo 674311 1016375 := bstep (se 1 (by rfl) ⟨762281, by rfl⟩ : syracuseStep 1016375 = 1524563) B1524563
theorem B124781381 : Blo 674311 124781381 := bstep (se 4 (by rfl) ⟨11698254, by rfl⟩ : syracuseStep 124781381 = 23396509) B23396509
theorem B18482201 : Blo 674311 18482201 := bstep (se 2 (by rfl) ⟨6930825, by rfl⟩ : syracuseStep 18482201 = 13861651) B13861651
theorem B2164925 : Blo 674311 2164925 := bstep (se 3 (by rfl) ⟨405923, by rfl⟩ : syracuseStep 2164925 = 811847) B811847
theorem B8653139 : Blo 674311 8653139 := bstep (se 1 (by rfl) ⟨6489854, by rfl⟩ : syracuseStep 8653139 = 12979709) B12979709
theorem B4885211 : Blo 674311 4885211 := bstep (se 1 (by rfl) ⟨3663908, by rfl⟩ : syracuseStep 4885211 = 7327817) B7327817
theorem B1280747 : Blo 674311 1280747 := bstep (se 1 (by rfl) ⟨960560, by rfl⟩ : syracuseStep 1280747 = 1921121) B1921121
theorem B8228861 : Blo 674311 8228861 := bstep (se 3 (by rfl) ⟨1542911, by rfl⟩ : syracuseStep 8228861 = 3085823) B3085823
theorem B6492473 : Blo 674311 6492473 := bstep (se 2 (by rfl) ⟨2434677, by rfl⟩ : syracuseStep 6492473 = 4869355) B4869355
theorem B5476727 : Blo 674311 5476727 := bstep (se 1 (by rfl) ⟨4107545, by rfl⟩ : syracuseStep 5476727 = 8215091) B8215091
theorem B1708523 : Blo 674311 1708523 := bstep (se 1 (by rfl) ⟨1281392, by rfl⟩ : syracuseStep 1708523 = 2562785) B2562785
theorem B2920967 : Blo 674311 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B2561129 : Blo 674311 2561129 := bstep (se 2 (by rfl) ⟨960423, by rfl⟩ : syracuseStep 2561129 = 1920847) B1920847
theorem B1283177 : Blo 674311 1283177 := bstep (se 2 (by rfl) ⟨481191, by rfl⟩ : syracuseStep 1283177 = 962383) B962383
theorem B1283951 : Blo 674311 1283951 := bstep (se 1 (by rfl) ⟨962963, by rfl⟩ : syracuseStep 1283951 = 1925927) B1925927
theorem B1447931 : Blo 674311 1447931 := bstep (se 1 (by rfl) ⟨1085948, by rfl⟩ : syracuseStep 1447931 = 2171897) B2171897
theorem B858215 : Blo 674311 858215 := bstep (se 1 (by rfl) ⟨643661, by rfl⟩ : syracuseStep 858215 = 1287323) B1287323
theorem B8689841 : Blo 674311 8689841 := bstep (se 2 (by rfl) ⟨3258690, by rfl⟩ : syracuseStep 8689841 = 6517381) B6517381
theorem B2562299 : Blo 674311 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B760063 : Blo 674311 760063 := bstep (se 1 (by rfl) ⟨570047, by rfl⟩ : syracuseStep 760063 = 1140095) B1140095
theorem B4398695 : Blo 674311 4398695 := bstep (se 1 (by rfl) ⟨3299021, by rfl⟩ : syracuseStep 4398695 = 6598043) B6598043
theorem B3841739 : Blo 674311 3841739 := bstep (se 1 (by rfl) ⟨2881304, by rfl⟩ : syracuseStep 3841739 = 5762609) B5762609
theorem B4629095 : Blo 674311 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B3843197 : Blo 674311 3843197 := bstep (se 3 (by rfl) ⟨720599, by rfl⟩ : syracuseStep 3843197 = 1441199) B1441199
theorem B3417875 : Blo 674311 3417875 := bstep (se 1 (by rfl) ⟨2563406, by rfl⟩ : syracuseStep 3417875 = 5126813) B5126813
theorem B3844655 : Blo 674311 3844655 := bstep (se 1 (by rfl) ⟨2883491, by rfl⟩ : syracuseStep 3844655 = 5766983) B5766983
theorem B1026857 : Blo 674311 1026857 := bstep (se 2 (by rfl) ⟨385071, by rfl⟩ : syracuseStep 1026857 = 770143) B770143
theorem B2599771 : Blo 674311 2599771 := bstep (se 1 (by rfl) ⟨1949828, by rfl⟩ : syracuseStep 2599771 = 3899657) B3899657
theorem B1715539 : Blo 674311 1715539 := bstep (se 1 (by rfl) ⟨1286654, by rfl⟩ : syracuseStep 1715539 = 2573309) B2573309
theorem B1158887 : Blo 674311 1158887 := bstep (se 1 (by rfl) ⟨869165, by rfl⟩ : syracuseStep 1158887 = 1738331) B1738331
theorem B2567933 : Blo 674311 2567933 := bstep (se 3 (by rfl) ⟨481487, by rfl⟩ : syracuseStep 2567933 = 962975) B962975
theorem B2567963 : Blo 674311 2567963 := bstep (se 1 (by rfl) ⟨1925972, by rfl⟩ : syracuseStep 2567963 = 3851945) B3851945
theorem B1716167 : Blo 674311 1716167 := bstep (se 1 (by rfl) ⟨1287125, by rfl⟩ : syracuseStep 1716167 = 2574251) B2574251
theorem B32944421 : Blo 674311 32944421 := bstep (se 4 (by rfl) ⟨3088539, by rfl⟩ : syracuseStep 32944421 = 6177079) B6177079
theorem B1159817 : Blo 674311 1159817 := bstep (se 2 (by rfl) ⟨434931, by rfl⟩ : syracuseStep 1159817 = 869863) B869863
theorem B2569117 : Blo 674311 2569117 := bstep (se 3 (by rfl) ⟨481709, by rfl⟩ : syracuseStep 2569117 = 963419) B963419
theorem B1521071 : Blo 674311 1521071 := bstep (se 1 (by rfl) ⟨1140803, by rfl⟩ : syracuseStep 1521071 = 2281607) B2281607
theorem B10958327 : Blo 674311 10958327 := bstep (se 1 (by rfl) ⟨8218745, by rfl⟩ : syracuseStep 10958327 = 16437491) B16437491
theorem B1521179 : Blo 674311 1521179 := bstep (se 1 (by rfl) ⟨1140884, by rfl⟩ : syracuseStep 1521179 = 2281769) B2281769
theorem B1521215 : Blo 674311 1521215 := bstep (se 1 (by rfl) ⟨1140911, by rfl⟩ : syracuseStep 1521215 = 2281823) B2281823
theorem B2340521 : Blo 674311 2340521 := bstep (se 2 (by rfl) ⟨877695, by rfl⟩ : syracuseStep 2340521 = 1755391) B1755391
theorem B42252293 : Blo 674311 42252293 := bstep (se 4 (by rfl) ⟨3961152, by rfl⟩ : syracuseStep 42252293 = 7922305) B7922305
theorem B6666259 : Blo 674311 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B2570363 : Blo 674311 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B6502619 : Blo 674311 6502619 := bstep (se 1 (by rfl) ⟨4876964, by rfl⟩ : syracuseStep 6502619 = 9753929) B9753929
theorem B9746729 : Blo 674311 9746729 := bstep (se 2 (by rfl) ⟨3655023, by rfl⟩ : syracuseStep 9746729 = 7310047) B7310047
theorem B5781881 : Blo 674311 5781881 := bstep (se 2 (by rfl) ⟨2168205, by rfl⟩ : syracuseStep 5781881 = 4336411) B4336411
theorem B2571047 : Blo 674311 2571047 := bstep (se 1 (by rfl) ⟨1928285, by rfl⟩ : syracuseStep 2571047 = 3856571) B3856571
theorem B3423059 : Blo 674311 3423059 := bstep (se 1 (by rfl) ⟨2567294, by rfl⟩ : syracuseStep 3423059 = 5134589) B5134589
theorem B2276315 : Blo 674311 2276315 := bstep (se 1 (by rfl) ⟨1707236, by rfl⟩ : syracuseStep 2276315 = 3414473) B3414473
theorem B13025225 : Blo 674311 13025225 := bstep (se 2 (by rfl) ⟨4884459, by rfl⟩ : syracuseStep 13025225 = 9768919) B9768919
theorem B13025771 : Blo 674311 13025771 := bstep (se 1 (by rfl) ⟨9769328, by rfl⟩ : syracuseStep 13025771 = 19538657) B19538657
theorem B2278205 : Blo 674311 2278205 := bstep (se 3 (by rfl) ⟨427163, by rfl⟩ : syracuseStep 2278205 = 854327) B854327
theorem B6505505 : Blo 674311 6505505 := bstep (se 2 (by rfl) ⟨2439564, by rfl⟩ : syracuseStep 6505505 = 4879129) B4879129
theorem B3425327 : Blo 674311 3425327 := bstep (se 1 (by rfl) ⟨2568995, by rfl⟩ : syracuseStep 3425327 = 5137991) B5137991
theorem B19481795 : Blo 674311 19481795 := bstep (se 1 (by rfl) ⟨14611346, by rfl⟩ : syracuseStep 19481795 = 29222693) B29222693
theorem B1525049 : Blo 674311 1525049 := bstep (se 2 (by rfl) ⟨571893, by rfl⟩ : syracuseStep 1525049 = 1143787) B1143787
theorem B12993857 : Blo 674311 12993857 := bstep (se 2 (by rfl) ⟨4872696, by rfl⟩ : syracuseStep 12993857 = 9745393) B9745393
theorem B1525499 : Blo 674311 1525499 := bstep (se 1 (by rfl) ⟨1144124, by rfl⟩ : syracuseStep 1525499 = 2288249) B2288249
theorem B2279879 : Blo 674311 2279879 := bstep (se 1 (by rfl) ⟨1709909, by rfl⟩ : syracuseStep 2279879 = 3419819) B3419819
theorem B674415 : Blo 674311 674415 := bstep (se 1 (by rfl) ⟨505811, by rfl⟩ : syracuseStep 674415 = 1011623) B1011623
theorem B674671 : Blo 674311 674671 := bstep (se 1 (by rfl) ⟨506003, by rfl⟩ : syracuseStep 674671 = 1012007) B1012007
theorem B675007 : Blo 674311 675007 := bstep (se 1 (by rfl) ⟨506255, by rfl⟩ : syracuseStep 675007 = 1012511) B1012511
theorem B675175 : Blo 674311 675175 := bstep (se 1 (by rfl) ⟨506381, by rfl⟩ : syracuseStep 675175 = 1012763) B1012763
theorem B675327 : Blo 674311 675327 := bstep (se 1 (by rfl) ⟨506495, by rfl⟩ : syracuseStep 675327 = 1012991) B1012991
theorem B5132159 : Blo 674311 5132159 := bstep (se 1 (by rfl) ⟨3849119, by rfl⟩ : syracuseStep 5132159 = 7698239) B7698239
theorem B675743 : Blo 674311 675743 := bstep (se 1 (by rfl) ⟨506807, by rfl⟩ : syracuseStep 675743 = 1013615) B1013615
theorem B2314271 : Blo 674311 2314271 := bstep (se 1 (by rfl) ⟨1735703, by rfl⟩ : syracuseStep 2314271 = 3471407) B3471407
theorem B3559751 : Blo 674311 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B10998287 : Blo 674311 10998287 := bstep (se 1 (by rfl) ⟨8248715, by rfl⟩ : syracuseStep 10998287 = 16497431) B16497431
theorem B677031 : Blo 674311 677031 := bstep (se 1 (by rfl) ⟨507773, by rfl⟩ : syracuseStep 677031 = 1015547) B1015547
theorem B677191 : Blo 674311 677191 := bstep (se 1 (by rfl) ⟨507893, by rfl⟩ : syracuseStep 677191 = 1015787) B1015787
theorem B677223 : Blo 674311 677223 := bstep (se 1 (by rfl) ⟨507917, by rfl⟩ : syracuseStep 677223 = 1015835) B1015835
theorem B677327 : Blo 674311 677327 := bstep (se 1 (by rfl) ⟨507995, by rfl⟩ : syracuseStep 677327 = 1015991) B1015991
theorem B677535 : Blo 674311 677535 := bstep (se 1 (by rfl) ⟨508151, by rfl⟩ : syracuseStep 677535 = 1016303) B1016303
theorem B677883 : Blo 674311 677883 := bstep (se 1 (by rfl) ⟨508412, by rfl⟩ : syracuseStep 677883 = 1016825) B1016825
theorem B6510617 : Blo 674311 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B677919 : Blo 674311 677919 := bstep (se 1 (by rfl) ⟨508439, by rfl⟩ : syracuseStep 677919 = 1016879) B1016879
theorem B10016939 : Blo 674311 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B2054747 : Blo 674311 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B1138313 : Blo 674311 1138313 := bstep (se 2 (by rfl) ⟨426867, by rfl⟩ : syracuseStep 1138313 = 853735) B853735
theorem B8642477 : Blo 674311 8642477 := bstep (se 3 (by rfl) ⟨1620464, by rfl⟩ : syracuseStep 8642477 = 3240929) B3240929
theorem B18472997 : Blo 674311 18472997 := bstep (se 4 (by rfl) ⟨1731843, by rfl⟩ : syracuseStep 18472997 = 3463687) B3463687
theorem B1138927 : Blo 674311 1138927 := bstep (se 1 (by rfl) ⟨854195, by rfl⟩ : syracuseStep 1138927 = 1708391) B1708391
theorem B8675693 : Blo 674311 8675693 := bstep (se 3 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 8675693 = 3253385) B3253385
theorem B1926281 : Blo 674311 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B8644481 : Blo 674311 8644481 := bstep (se 2 (by rfl) ⟨3241680, by rfl⟩ : syracuseStep 8644481 = 6483361) B6483361
theorem B3860419 : Blo 674311 3860419 := bstep (se 1 (by rfl) ⟨2895314, by rfl⟩ : syracuseStep 3860419 = 5790629) B5790629
theorem B1140959 : Blo 674311 1140959 := bstep (se 1 (by rfl) ⟨855719, by rfl⟩ : syracuseStep 1140959 = 1711439) B1711439
theorem B2287871 : Blo 674311 2287871 := bstep (se 1 (by rfl) ⟨1715903, by rfl⟩ : syracuseStep 2287871 = 3431807) B3431807
theorem B6941497 : Blo 674311 6941497 := bstep (se 2 (by rfl) ⟨2603061, by rfl⟩ : syracuseStep 6941497 = 5206123) B5206123
theorem B1141627 : Blo 674311 1141627 := bstep (se 1 (by rfl) ⟨856220, by rfl⟩ : syracuseStep 1141627 = 1712441) B1712441
theorem B1141823 : Blo 674311 1141823 := bstep (se 1 (by rfl) ⟨856367, by rfl⟩ : syracuseStep 1141823 = 1712735) B1712735
theorem B2288735 : Blo 674311 2288735 := bstep (se 1 (by rfl) ⟨1716551, by rfl⟩ : syracuseStep 2288735 = 3433103) B3433103
theorem B6515963 : Blo 674311 6515963 := bstep (se 1 (by rfl) ⟨4886972, by rfl⟩ : syracuseStep 6515963 = 9773945) B9773945
theorem B2288951 : Blo 674311 2288951 := bstep (se 1 (by rfl) ⟨1716713, by rfl⟩ : syracuseStep 2288951 = 3433427) B3433427
theorem B1011995 : Blo 674311 1011995 := bstep (se 1 (by rfl) ⟨758996, by rfl⟩ : syracuseStep 1011995 = 1517993) B1517993
theorem B1143119 : Blo 674311 1143119 := bstep (se 1 (by rfl) ⟨857339, by rfl⟩ : syracuseStep 1143119 = 1714679) B1714679
theorem B1143463 : Blo 674311 1143463 := bstep (se 1 (by rfl) ⟨857597, by rfl⟩ : syracuseStep 1143463 = 1715195) B1715195
theorem B1012391 : Blo 674311 1012391 := bstep (se 1 (by rfl) ⟨759293, by rfl⟩ : syracuseStep 1012391 = 1518587) B1518587
theorem B4617155 : Blo 674311 4617155 := bstep (se 1 (by rfl) ⟨3462866, by rfl⟩ : syracuseStep 4617155 = 6925733) B6925733
theorem B5862431 : Blo 674311 5862431 := bstep (se 1 (by rfl) ⟨4396823, by rfl⟩ : syracuseStep 5862431 = 8793647) B8793647
theorem B1012847 : Blo 674311 1012847 := bstep (se 1 (by rfl) ⟨759635, by rfl⟩ : syracuseStep 1012847 = 1519271) B1519271
theorem B2749879 : Blo 674311 2749879 := bstep (se 1 (by rfl) ⟨2062409, by rfl⟩ : syracuseStep 2749879 = 4124819) B4124819
theorem B1013375 : Blo 674311 1013375 := bstep (se 1 (by rfl) ⟨760031, by rfl⟩ : syracuseStep 1013375 = 1520063) B1520063
theorem B1013423 : Blo 674311 1013423 := bstep (se 1 (by rfl) ⟨760067, by rfl⟩ : syracuseStep 1013423 = 1520135) B1520135
theorem B2193115 : Blo 674311 2193115 := bstep (se 1 (by rfl) ⟨1644836, by rfl⟩ : syracuseStep 2193115 = 3289673) B3289673
theorem B1013627 : Blo 674311 1013627 := bstep (se 1 (by rfl) ⟨760220, by rfl⟩ : syracuseStep 1013627 = 1520441) B1520441
theorem B5142851 : Blo 674311 5142851 := bstep (se 1 (by rfl) ⟨3857138, by rfl⟩ : syracuseStep 5142851 = 7714277) B7714277
theorem B2881919 : Blo 674311 2881919 := bstep (se 1 (by rfl) ⟨2161439, by rfl⟩ : syracuseStep 2881919 = 4322879) B4322879
theorem B1014569 : Blo 674311 1014569 := bstep (se 2 (by rfl) ⟨380463, by rfl⟩ : syracuseStep 1014569 = 760927) B760927
theorem B5143337 : Blo 674311 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B4619105 : Blo 674311 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B1014767 : Blo 674311 1014767 := bstep (se 1 (by rfl) ⟨761075, by rfl⟩ : syracuseStep 1014767 = 1522151) B1522151
theorem B1015019 : Blo 674311 1015019 := bstep (se 1 (by rfl) ⟨761264, by rfl⟩ : syracuseStep 1015019 = 1522529) B1522529
theorem B1015067 : Blo 674311 1015067 := bstep (se 1 (by rfl) ⟨761300, by rfl⟩ : syracuseStep 1015067 = 1522601) B1522601
theorem B1015103 : Blo 674311 1015103 := bstep (se 1 (by rfl) ⟨761327, by rfl⟩ : syracuseStep 1015103 = 1522655) B1522655
theorem B1015295 : Blo 674311 1015295 := bstep (se 1 (by rfl) ⟨761471, by rfl⟩ : syracuseStep 1015295 = 1522943) B1522943
theorem B1015679 : Blo 674311 1015679 := bstep (se 1 (by rfl) ⟨761759, by rfl⟩ : syracuseStep 1015679 = 1523519) B1523519
theorem B1441883 : Blo 674311 1441883 := bstep (se 1 (by rfl) ⟨1081412, by rfl⟩ : syracuseStep 1441883 = 2162825) B2162825
theorem B8683847 : Blo 674311 8683847 := bstep (se 1 (by rfl) ⟨6512885, by rfl⟩ : syracuseStep 8683847 = 13025771) B13025771
theorem B12321467 : Blo 674311 12321467 := bstep (se 1 (by rfl) ⟨9241100, by rfl⟩ : syracuseStep 12321467 = 18482201) B18482201
theorem B1016699 : Blo 674311 1016699 := bstep (se 1 (by rfl) ⟨762524, by rfl⟩ : syracuseStep 1016699 = 1525049) B1525049
theorem B1016999 : Blo 674311 1016999 := bstep (se 1 (by rfl) ⟨762749, by rfl⟩ : syracuseStep 1016999 = 1525499) B1525499
theorem B5768759 : Blo 674311 5768759 := bstep (se 1 (by rfl) ⟨4326569, by rfl⟩ : syracuseStep 5768759 = 8653139) B8653139
theorem B853831 : Blo 674311 853831 := bstep (se 1 (by rfl) ⟨640373, by rfl⟩ : syracuseStep 853831 = 1280747) B1280747
theorem B5147225 : Blo 674311 5147225 := bstep (se 2 (by rfl) ⟨1930209, by rfl⟩ : syracuseStep 5147225 = 3860419) B3860419
theorem B4328315 : Blo 674311 4328315 := bstep (se 1 (by rfl) ⟨3246236, by rfl⟩ : syracuseStep 4328315 = 6492473) B6492473
theorem B1707419 : Blo 674311 1707419 := bstep (se 1 (by rfl) ⟨1280564, by rfl⟩ : syracuseStep 1707419 = 2561129) B2561129
theorem B855451 : Blo 674311 855451 := bstep (se 1 (by rfl) ⟨641588, by rfl⟩ : syracuseStep 855451 = 1283177) B1283177
theorem B1708199 : Blo 674311 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B758875 : Blo 674311 758875 := bstep (se 1 (by rfl) ⟨569156, by rfl⟩ : syracuseStep 758875 = 1138313) B1138313
theorem B2561159 : Blo 674311 2561159 := bstep (se 1 (by rfl) ⟨1920869, by rfl⟩ : syracuseStep 2561159 = 3841739) B3841739
theorem B3086063 : Blo 674311 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B5773133 : Blo 674311 5773133 := bstep (se 3 (by rfl) ⟨1082462, by rfl⟩ : syracuseStep 5773133 = 2164925) B2164925
theorem B2562131 : Blo 674311 2562131 := bstep (se 1 (by rfl) ⟨1921598, by rfl⟩ : syracuseStep 2562131 = 3843197) B3843197
theorem B1284187 : Blo 674311 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B760639 : Blo 674311 760639 := bstep (se 1 (by rfl) ⟨570479, by rfl⟩ : syracuseStep 760639 = 1140959) B1140959
theorem B5479325 : Blo 674311 5479325 := bstep (se 3 (by rfl) ⟨1027373, by rfl⟩ : syracuseStep 5479325 = 2054747) B2054747
theorem B2563103 : Blo 674311 2563103 := bstep (se 1 (by rfl) ⟨1922327, by rfl⟩ : syracuseStep 2563103 = 3844655) B3844655
theorem B761215 : Blo 674311 761215 := bstep (se 1 (by rfl) ⟨570911, by rfl⟩ : syracuseStep 761215 = 1141823) B1141823
theorem B2924153 : Blo 674311 2924153 := bstep (se 2 (by rfl) ⟨1096557, by rfl⟩ : syracuseStep 2924153 = 2193115) B2193115
theorem B1711955 : Blo 674311 1711955 := bstep (se 1 (by rfl) ⟨1283966, by rfl⟩ : syracuseStep 1711955 = 2567933) B2567933
theorem B1711975 : Blo 674311 1711975 := bstep (se 1 (by rfl) ⟨1283981, by rfl⟩ : syracuseStep 1711975 = 2567963) B2567963
theorem B8888345 : Blo 674311 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B21962947 : Blo 674311 21962947 := bstep (se 1 (by rfl) ⟨16472210, by rfl⟩ : syracuseStep 21962947 = 32944421) B32944421
theorem B762079 : Blo 674311 762079 := bstep (se 1 (by rfl) ⟨571559, by rfl⟩ : syracuseStep 762079 = 1143119) B1143119
theorem B3908287 : Blo 674311 3908287 := bstep (se 1 (by rfl) ⟨2931215, by rfl⟩ : syracuseStep 3908287 = 5862431) B5862431
theorem B1713575 : Blo 674311 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B4335079 : Blo 674311 4335079 := bstep (se 1 (by rfl) ⟨3251309, by rfl⟩ : syracuseStep 4335079 = 6502619) B6502619
theorem B6497819 : Blo 674311 6497819 := bstep (se 1 (by rfl) ⟨4873364, by rfl⟩ : syracuseStep 6497819 = 9746729) B9746729
theorem B1714031 : Blo 674311 1714031 := bstep (se 1 (by rfl) ⟨1285523, by rfl⟩ : syracuseStep 1714031 = 2571047) B2571047
theorem B3090365 : Blo 674311 3090365 := bstep (se 3 (by rfl) ⟨579443, by rfl⟩ : syracuseStep 3090365 = 1158887) B1158887
theorem B1517543 : Blo 674311 1517543 := bstep (se 1 (by rfl) ⟨1138157, by rfl⟩ : syracuseStep 1517543 = 2276315) B2276315
theorem B6171389 : Blo 674311 6171389 := bstep (se 3 (by rfl) ⟨1157135, by rfl⟩ : syracuseStep 6171389 = 2314271) B2314271
theorem B1518569 : Blo 674311 1518569 := bstep (se 2 (by rfl) ⟨569463, by rfl⟩ : syracuseStep 1518569 = 1138927) B1138927
theorem B1518803 : Blo 674311 1518803 := bstep (se 1 (by rfl) ⟨1139102, by rfl⟩ : syracuseStep 1518803 = 2278205) B2278205
theorem B4337003 : Blo 674311 4337003 := bstep (se 1 (by rfl) ⟨3252752, by rfl⟩ : syracuseStep 4337003 = 6505505) B6505505
theorem B12987863 : Blo 674311 12987863 := bstep (se 1 (by rfl) ⟨9740897, by rfl⟩ : syracuseStep 12987863 = 19481795) B19481795
theorem B8662571 : Blo 674311 8662571 := bstep (se 1 (by rfl) ⟨6496928, by rfl⟩ : syracuseStep 8662571 = 12993857) B12993857
theorem B1519919 : Blo 674311 1519919 := bstep (se 1 (by rfl) ⟨1139939, by rfl⟩ : syracuseStep 1519919 = 2279879) B2279879
theorem B3421439 : Blo 674311 3421439 := bstep (se 1 (by rfl) ⟨2566079, by rfl⟩ : syracuseStep 3421439 = 5132159) B5132159
theorem B5485907 : Blo 674311 5485907 := bstep (se 1 (by rfl) ⟨4114430, by rfl⟩ : syracuseStep 5485907 = 8228861) B8228861
theorem B2373167 : Blo 674311 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B3651151 : Blo 674311 3651151 := bstep (se 1 (by rfl) ⟨2738363, by rfl⟩ : syracuseStep 3651151 = 5476727) B5476727
theorem B1947311 : Blo 674311 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B9255329 : Blo 674311 9255329 := bstep (se 2 (by rfl) ⟨3470748, by rfl⟩ : syracuseStep 9255329 = 6941497) B6941497
theorem B1522169 : Blo 674311 1522169 := bstep (se 2 (by rfl) ⟨570813, by rfl⟩ : syracuseStep 1522169 = 1141627) B1141627
theorem B965287 : Blo 674311 965287 := bstep (se 1 (by rfl) ⟨723965, by rfl⟩ : syracuseStep 965287 = 1447931) B1447931
theorem B4340411 : Blo 674311 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B3423869 : Blo 674311 3423869 := bstep (se 3 (by rfl) ⟨641975, by rfl⟩ : syracuseStep 3423869 = 1283951) B1283951
theorem B2932463 : Blo 674311 2932463 := bstep (se 1 (by rfl) ⟨2199347, by rfl⟩ : syracuseStep 2932463 = 4398695) B4398695
theorem B5783795 : Blo 674311 5783795 := bstep (se 1 (by rfl) ⟨4337846, by rfl⟩ : syracuseStep 5783795 = 8675693) B8675693
theorem B1524617 : Blo 674311 1524617 := bstep (se 2 (by rfl) ⟨571731, by rfl⟩ : syracuseStep 1524617 = 1143463) B1143463
theorem B7685117 : Blo 674311 7685117 := bstep (se 3 (by rfl) ⟨1440959, by rfl⟩ : syracuseStep 7685117 = 2881919) B2881919
theorem B2278583 : Blo 674311 2278583 := bstep (se 1 (by rfl) ⟨1708937, by rfl⟩ : syracuseStep 2278583 = 3417875) B3417875
theorem B3425489 : Blo 674311 3425489 := bstep (se 2 (by rfl) ⟨1284558, by rfl⟩ : syracuseStep 3425489 = 2569117) B2569117
theorem B12371381 : Blo 674311 12371381 := bstep (se 5 (by rfl) ⟨579908, by rfl⟩ : syracuseStep 12371381 = 1159817) B1159817
theorem B1525247 : Blo 674311 1525247 := bstep (se 1 (by rfl) ⟨1143935, by rfl⟩ : syracuseStep 1525247 = 2287871) B2287871
theorem B13027229 : Blo 674311 13027229 := bstep (se 3 (by rfl) ⟨2442605, by rfl⟩ : syracuseStep 13027229 = 4885211) B4885211
theorem B1525823 : Blo 674311 1525823 := bstep (se 1 (by rfl) ⟨1144367, by rfl⟩ : syracuseStep 1525823 = 2288735) B2288735
theorem B2738285 : Blo 674311 2738285 := bstep (se 3 (by rfl) ⟨513428, by rfl⟩ : syracuseStep 2738285 = 1026857) B1026857
theorem B4343975 : Blo 674311 4343975 := bstep (se 1 (by rfl) ⟨3257981, by rfl⟩ : syracuseStep 4343975 = 6515963) B6515963
theorem B1525967 : Blo 674311 1525967 := bstep (se 1 (by rfl) ⟨1144475, by rfl⟩ : syracuseStep 1525967 = 2288951) B2288951
theorem B14666021 : Blo 674311 14666021 := bstep (se 4 (by rfl) ⟨1374939, by rfl⟩ : syracuseStep 14666021 = 2749879) B2749879
theorem B674663 : Blo 674311 674663 := bstep (se 1 (by rfl) ⟨505997, by rfl⟩ : syracuseStep 674663 = 1011995) B1011995
theorem B674927 : Blo 674311 674927 := bstep (se 1 (by rfl) ⟨506195, by rfl⟩ : syracuseStep 674927 = 1012391) B1012391
theorem B675231 : Blo 674311 675231 := bstep (se 1 (by rfl) ⟨506423, by rfl⟩ : syracuseStep 675231 = 1012847) B1012847
theorem B675583 : Blo 674311 675583 := bstep (se 1 (by rfl) ⟨506687, by rfl⟩ : syracuseStep 675583 = 1013375) B1013375
theorem B1560347 : Blo 674311 1560347 := bstep (se 1 (by rfl) ⟨1170260, by rfl⟩ : syracuseStep 1560347 = 2340521) B2340521
theorem B675615 : Blo 674311 675615 := bstep (se 1 (by rfl) ⟨506711, by rfl⟩ : syracuseStep 675615 = 1013423) B1013423
theorem B675751 : Blo 674311 675751 := bstep (se 1 (by rfl) ⟨506813, by rfl⟩ : syracuseStep 675751 = 1013627) B1013627
theorem B28168195 : Blo 674311 28168195 := bstep (se 1 (by rfl) ⟨21126146, by rfl⟩ : syracuseStep 28168195 = 42252293) B42252293
theorem B3428567 : Blo 674311 3428567 := bstep (se 1 (by rfl) ⟨2571425, by rfl⟩ : syracuseStep 3428567 = 5142851) B5142851
theorem B3854587 : Blo 674311 3854587 := bstep (se 1 (by rfl) ⟨2890940, by rfl⟩ : syracuseStep 3854587 = 5781881) B5781881
theorem B676379 : Blo 674311 676379 := bstep (se 1 (by rfl) ⟨507284, by rfl⟩ : syracuseStep 676379 = 1014569) B1014569
theorem B3428891 : Blo 674311 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B2282039 : Blo 674311 2282039 := bstep (se 1 (by rfl) ⟨1711529, by rfl⟩ : syracuseStep 2282039 = 3423059) B3423059
theorem B676511 : Blo 674311 676511 := bstep (se 1 (by rfl) ⟨507383, by rfl⟩ : syracuseStep 676511 = 1014767) B1014767
theorem B676679 : Blo 674311 676679 := bstep (se 1 (by rfl) ⟨507509, by rfl⟩ : syracuseStep 676679 = 1015019) B1015019
theorem B676711 : Blo 674311 676711 := bstep (se 1 (by rfl) ⟨507533, by rfl⟩ : syracuseStep 676711 = 1015067) B1015067
theorem B676735 : Blo 674311 676735 := bstep (se 1 (by rfl) ⟨507551, by rfl⟩ : syracuseStep 676735 = 1015103) B1015103
theorem B676863 : Blo 674311 676863 := bstep (se 1 (by rfl) ⟨507647, by rfl⟩ : syracuseStep 676863 = 1015295) B1015295
theorem B677119 : Blo 674311 677119 := bstep (se 1 (by rfl) ⟨507839, by rfl⟩ : syracuseStep 677119 = 1015679) B1015679
theorem B677583 : Blo 674311 677583 := bstep (se 1 (by rfl) ⟨508187, by rfl⟩ : syracuseStep 677583 = 1016375) B1016375
theorem B83187587 : Blo 674311 83187587 := bstep (se 1 (by rfl) ⟨62390690, by rfl⟩ : syracuseStep 83187587 = 124781381) B124781381
theorem B2283551 : Blo 674311 2283551 := bstep (se 1 (by rfl) ⟨1712663, by rfl⟩ : syracuseStep 2283551 = 3425327) B3425327
theorem B1139015 : Blo 674311 1139015 := bstep (se 1 (by rfl) ⟨854261, by rfl⟩ : syracuseStep 1139015 = 1708523) B1708523
theorem B7332191 : Blo 674311 7332191 := bstep (se 1 (by rfl) ⟨5499143, by rfl⟩ : syracuseStep 7332191 = 10998287) B10998287
theorem B3466361 : Blo 674311 3466361 := bstep (se 2 (by rfl) ⟨1299885, by rfl⟩ : syracuseStep 3466361 = 2599771) B2599771
theorem B6677959 : Blo 674311 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B5793227 : Blo 674311 5793227 := bstep (se 1 (by rfl) ⟨4344920, by rfl⟩ : syracuseStep 5793227 = 8689841) B8689841
theorem B2287385 : Blo 674311 2287385 := bstep (se 2 (by rfl) ⟨857769, by rfl⟩ : syracuseStep 2287385 = 1715539) B1715539
theorem B5761651 : Blo 674311 5761651 := bstep (se 1 (by rfl) ⟨4321238, by rfl⟩ : syracuseStep 5761651 = 8642477) B8642477
theorem B12315331 : Blo 674311 12315331 := bstep (se 1 (by rfl) ⟨9236498, by rfl⟩ : syracuseStep 12315331 = 18472997) B18472997
theorem B2288573 : Blo 674311 2288573 := bstep (se 3 (by rfl) ⟨429107, by rfl⟩ : syracuseStep 2288573 = 858215) B858215
theorem B5762987 : Blo 674311 5762987 := bstep (se 1 (by rfl) ⟨4322240, by rfl⟩ : syracuseStep 5762987 = 8644481) B8644481
theorem B1144111 : Blo 674311 1144111 := bstep (se 1 (by rfl) ⟨858083, by rfl⟩ : syracuseStep 1144111 = 1716167) B1716167
theorem B1013417 : Blo 674311 1013417 := bstep (se 2 (by rfl) ⟨380031, by rfl⟩ : syracuseStep 1013417 = 760063) B760063
theorem B3078103 : Blo 674311 3078103 := bstep (se 1 (by rfl) ⟨2308577, by rfl⟩ : syracuseStep 3078103 = 4617155) B4617155
theorem B1014047 : Blo 674311 1014047 := bstep (se 1 (by rfl) ⟨760535, by rfl⟩ : syracuseStep 1014047 = 1521071) B1521071
theorem B7305551 : Blo 674311 7305551 := bstep (se 1 (by rfl) ⟨5479163, by rfl⟩ : syracuseStep 7305551 = 10958327) B10958327
theorem B1014119 : Blo 674311 1014119 := bstep (se 1 (by rfl) ⟨760589, by rfl⟩ : syracuseStep 1014119 = 1521179) B1521179
theorem B1014143 : Blo 674311 1014143 := bstep (se 1 (by rfl) ⟨760607, by rfl⟩ : syracuseStep 1014143 = 1521215) B1521215
theorem B3079403 : Blo 674311 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B8683483 : Blo 674311 8683483 := bstep (se 1 (by rfl) ⟨6512612, by rfl⟩ : syracuseStep 8683483 = 13025225) B13025225
theorem B1016105 : Blo 674311 1016105 := bstep (se 2 (by rfl) ⟨381039, by rfl⟩ : syracuseStep 1016105 = 762079) B762079
theorem B1016411 : Blo 674311 1016411 := bstep (se 1 (by rfl) ⟨762308, by rfl⟩ : syracuseStep 1016411 = 1524617) B1524617
theorem B5211049 : Blo 674311 5211049 := bstep (se 2 (by rfl) ⟨1954143, by rfl⟩ : syracuseStep 5211049 = 3908287) B3908287
theorem B1016831 : Blo 674311 1016831 := bstep (se 1 (by rfl) ⟨762623, by rfl⟩ : syracuseStep 1016831 = 1525247) B1525247
theorem B8684819 : Blo 674311 8684819 := bstep (se 1 (by rfl) ⟨6513614, by rfl⟩ : syracuseStep 8684819 = 13027229) B13027229
theorem B1017215 : Blo 674311 1017215 := bstep (se 1 (by rfl) ⟨762911, by rfl⟩ : syracuseStep 1017215 = 1525823) B1525823
theorem B1017311 : Blo 674311 1017311 := bstep (se 1 (by rfl) ⟨762983, by rfl⟩ : syracuseStep 1017311 = 1525967) B1525967
theorem B2885543 : Blo 674311 2885543 := bstep (se 1 (by rfl) ⟨2164157, by rfl⟩ : syracuseStep 2885543 = 4328315) B4328315
theorem B9243629 : Blo 674311 9243629 := bstep (se 3 (by rfl) ⟨1733180, by rfl⟩ : syracuseStep 9243629 = 3466361) B3466361
theorem B1707439 : Blo 674311 1707439 := bstep (se 1 (by rfl) ⟨1280579, by rfl⟩ : syracuseStep 1707439 = 2561159) B2561159
theorem B5148197 : Blo 674311 5148197 := bstep (se 4 (by rfl) ⟨482643, by rfl⟩ : syracuseStep 5148197 = 965287) B965287
theorem B16420441 : Blo 674311 16420441 := bstep (se 2 (by rfl) ⟨6157665, by rfl⟩ : syracuseStep 16420441 = 12315331) B12315331
theorem B1708087 : Blo 674311 1708087 := bstep (se 1 (by rfl) ⟨1281065, by rfl⟩ : syracuseStep 1708087 = 2562131) B2562131
theorem B1708735 : Blo 674311 1708735 := bstep (se 1 (by rfl) ⟨1281551, by rfl⟩ : syracuseStep 1708735 = 2563103) B2563103
theorem B37557593 : Blo 674311 37557593 := bstep (se 2 (by rfl) ⟨14084097, by rfl⟩ : syracuseStep 37557593 = 28168195) B28168195
theorem B759343 : Blo 674311 759343 := bstep (se 1 (by rfl) ⟨569507, by rfl⟩ : syracuseStep 759343 = 1139015) B1139015
theorem B4888127 : Blo 674311 4888127 := bstep (se 1 (by rfl) ⟨3666095, by rfl⟩ : syracuseStep 4888127 = 7332191) B7332191
theorem B4331879 : Blo 674311 4331879 := bstep (se 1 (by rfl) ⟨3248909, by rfl⟩ : syracuseStep 4331879 = 6497819) B6497819
theorem B2891335 : Blo 674311 2891335 := bstep (se 1 (by rfl) ⟨2168501, by rfl⟩ : syracuseStep 2891335 = 4337003) B4337003
theorem B8658575 : Blo 674311 8658575 := bstep (se 1 (by rfl) ⟨6493931, by rfl⟩ : syracuseStep 8658575 = 12987863) B12987863
theorem B5775047 : Blo 674311 5775047 := bstep (se 1 (by rfl) ⟨4331285, by rfl⟩ : syracuseStep 5775047 = 8662571) B8662571
theorem B3841991 : Blo 674311 3841991 := bstep (se 1 (by rfl) ⟨2881493, by rfl⟩ : syracuseStep 3841991 = 5762987) B5762987
theorem B4104137 : Blo 674311 4104137 := bstep (se 2 (by rfl) ⟨1539051, by rfl⟩ : syracuseStep 4104137 = 3078103) B3078103
theorem B1712249 : Blo 674311 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B1582111 : Blo 674311 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B6170219 : Blo 674311 6170219 := bstep (se 1 (by rfl) ⟨4627664, by rfl⟩ : syracuseStep 6170219 = 9255329) B9255329
theorem B2893607 : Blo 674311 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B11577977 : Blo 674311 11577977 := bstep (se 2 (by rfl) ⟨4341741, by rfl⟩ : syracuseStep 11577977 = 8683483) B8683483
theorem B961255 : Blo 674311 961255 := bstep (se 1 (by rfl) ⟨720941, by rfl⟩ : syracuseStep 961255 = 1441883) B1441883
theorem B5123411 : Blo 674311 5123411 := bstep (se 1 (by rfl) ⟨3842558, by rfl⟩ : syracuseStep 5123411 = 7685117) B7685117
theorem B1519055 : Blo 674311 1519055 := bstep (se 1 (by rfl) ⟨1139291, by rfl⟩ : syracuseStep 1519055 = 2278583) B2278583
theorem B3845839 : Blo 674311 3845839 := bstep (se 1 (by rfl) ⟨2884379, by rfl⟩ : syracuseStep 3845839 = 5768759) B5768759
theorem B2895983 : Blo 674311 2895983 := bstep (se 1 (by rfl) ⟨2171987, by rfl⟩ : syracuseStep 2895983 = 4343975) B4343975
theorem B9777347 : Blo 674311 9777347 := bstep (se 1 (by rfl) ⟨7333010, by rfl⟩ : syracuseStep 9777347 = 14666021) B14666021
theorem B5780105 : Blo 674311 5780105 := bstep (se 2 (by rfl) ⟨2167539, by rfl⟩ : syracuseStep 5780105 = 4335079) B4335079
theorem B1521359 : Blo 674311 1521359 := bstep (se 1 (by rfl) ⟨1141019, by rfl⟩ : syracuseStep 1521359 = 2282039) B2282039
theorem B7682201 : Blo 674311 7682201 := bstep (se 2 (by rfl) ⟨2880825, by rfl⟩ : syracuseStep 7682201 = 5761651) B5761651
theorem B14629085 : Blo 674311 14629085 := bstep (se 3 (by rfl) ⟨2742953, by rfl⟩ : syracuseStep 14629085 = 5485907) B5485907
theorem B3848755 : Blo 674311 3848755 := bstep (se 1 (by rfl) ⟨2886566, by rfl⟩ : syracuseStep 3848755 = 5773133) B5773133
theorem B55458391 : Blo 674311 55458391 := bstep (se 1 (by rfl) ⟨41593793, by rfl⟩ : syracuseStep 55458391 = 83187587) B83187587
theorem B1522367 : Blo 674311 1522367 := bstep (se 1 (by rfl) ⟨1141775, by rfl⟩ : syracuseStep 1522367 = 2283551) B2283551
theorem B3652883 : Blo 674311 3652883 := bstep (se 1 (by rfl) ⟨2739662, by rfl⟩ : syracuseStep 3652883 = 5479325) B5479325
theorem B1949435 : Blo 674311 1949435 := bstep (se 1 (by rfl) ⟨1462076, by rfl⟩ : syracuseStep 1949435 = 2924153) B2924153
theorem B1524923 : Blo 674311 1524923 := bstep (se 1 (by rfl) ⟨1143692, by rfl⟩ : syracuseStep 1524923 = 2287385) B2287385
theorem B1525481 : Blo 674311 1525481 := bstep (se 2 (by rfl) ⟨572055, by rfl⟩ : syracuseStep 1525481 = 1144111) B1144111
theorem B4114259 : Blo 674311 4114259 := bstep (se 1 (by rfl) ⟨3085694, by rfl⟩ : syracuseStep 4114259 = 6171389) B6171389
theorem B1525715 : Blo 674311 1525715 := bstep (se 1 (by rfl) ⟨1144286, by rfl⟩ : syracuseStep 1525715 = 2288573) B2288573
theorem B4868201 : Blo 674311 4868201 := bstep (se 2 (by rfl) ⟨1825575, by rfl⟩ : syracuseStep 4868201 = 3651151) B3651151
theorem B2280959 : Blo 674311 2280959 := bstep (se 1 (by rfl) ⟨1710719, by rfl⟩ : syracuseStep 2280959 = 3421439) B3421439
theorem B675611 : Blo 674311 675611 := bstep (se 1 (by rfl) ⟨506708, by rfl⟩ : syracuseStep 675611 = 1013417) B1013417
theorem B1298207 : Blo 674311 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B676031 : Blo 674311 676031 := bstep (se 1 (by rfl) ⟨507023, by rfl⟩ : syracuseStep 676031 = 1014047) B1014047
theorem B4870367 : Blo 674311 4870367 := bstep (se 1 (by rfl) ⟨3652775, by rfl⟩ : syracuseStep 4870367 = 7305551) B7305551
theorem B676079 : Blo 674311 676079 := bstep (se 1 (by rfl) ⟨507059, by rfl⟩ : syracuseStep 676079 = 1014119) B1014119
theorem B676095 : Blo 674311 676095 := bstep (se 1 (by rfl) ⟨507071, by rfl⟩ : syracuseStep 676095 = 1014143) B1014143
theorem B7819901 : Blo 674311 7819901 := bstep (se 3 (by rfl) ⟨1466231, by rfl⟩ : syracuseStep 7819901 = 2932463) B2932463
theorem B2052935 : Blo 674311 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B2282579 : Blo 674311 2282579 := bstep (se 1 (by rfl) ⟨1711934, by rfl⟩ : syracuseStep 2282579 = 3423869) B3423869
theorem B2282633 : Blo 674311 2282633 := bstep (se 2 (by rfl) ⟨855987, by rfl⟩ : syracuseStep 2282633 = 1711975) B1711975
theorem B3855863 : Blo 674311 3855863 := bstep (se 1 (by rfl) ⟨2891897, by rfl⟩ : syracuseStep 3855863 = 5783795) B5783795
theorem B5789231 : Blo 674311 5789231 := bstep (se 1 (by rfl) ⟨4341923, by rfl⟩ : syracuseStep 5789231 = 8683847) B8683847
theorem B29283929 : Blo 674311 29283929 := bstep (se 2 (by rfl) ⟨10981473, by rfl⟩ : syracuseStep 29283929 = 21962947) B21962947
theorem B8214311 : Blo 674311 8214311 := bstep (se 1 (by rfl) ⟨6160733, by rfl⟩ : syracuseStep 8214311 = 12321467) B12321467
theorem B677799 : Blo 674311 677799 := bstep (se 1 (by rfl) ⟨508349, by rfl⟩ : syracuseStep 677799 = 1016699) B1016699
theorem B677999 : Blo 674311 677999 := bstep (se 1 (by rfl) ⟨508499, by rfl⟩ : syracuseStep 677999 = 1016999) B1016999
theorem B2283659 : Blo 674311 2283659 := bstep (se 1 (by rfl) ⟨1712744, by rfl⟩ : syracuseStep 2283659 = 3425489) B3425489
theorem B8247587 : Blo 674311 8247587 := bstep (se 1 (by rfl) ⟨6185690, by rfl⟩ : syracuseStep 8247587 = 12371381) B12371381
theorem B1825523 : Blo 674311 1825523 := bstep (se 1 (by rfl) ⟨1369142, by rfl⟩ : syracuseStep 1825523 = 2738285) B2738285
theorem B3431483 : Blo 674311 3431483 := bstep (se 1 (by rfl) ⟨2573612, by rfl⟩ : syracuseStep 3431483 = 5147225) B5147225
theorem B8903945 : Blo 674311 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B1138279 : Blo 674311 1138279 := bstep (se 1 (by rfl) ⟨853709, by rfl⟩ : syracuseStep 1138279 = 1707419) B1707419
theorem B1138441 : Blo 674311 1138441 := bstep (se 2 (by rfl) ⟨426915, by rfl⟩ : syracuseStep 1138441 = 853831) B853831
theorem B1040231 : Blo 674311 1040231 := bstep (se 1 (by rfl) ⟨780173, by rfl⟩ : syracuseStep 1040231 = 1560347) B1560347
theorem B1138799 : Blo 674311 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B2285711 : Blo 674311 2285711 := bstep (se 1 (by rfl) ⟨1714283, by rfl⟩ : syracuseStep 2285711 = 3428567) B3428567
theorem B2285927 : Blo 674311 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B2057375 : Blo 674311 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B1140601 : Blo 674311 1140601 := bstep (se 2 (by rfl) ⟨427725, by rfl⟩ : syracuseStep 1140601 = 855451) B855451
theorem B1141303 : Blo 674311 1141303 := bstep (se 1 (by rfl) ⟨855977, by rfl⟩ : syracuseStep 1141303 = 1711955) B1711955
theorem B5925563 : Blo 674311 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B5139449 : Blo 674311 5139449 := bstep (se 2 (by rfl) ⟨1927293, by rfl⟩ : syracuseStep 5139449 = 3854587) B3854587
theorem B1142383 : Blo 674311 1142383 := bstep (se 1 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 1142383 = 1713575) B1713575
theorem B3862151 : Blo 674311 3862151 := bstep (se 1 (by rfl) ⟨2896613, by rfl⟩ : syracuseStep 3862151 = 5793227) B5793227
theorem B1142687 : Blo 674311 1142687 := bstep (se 1 (by rfl) ⟨857015, by rfl⟩ : syracuseStep 1142687 = 1714031) B1714031
theorem B2060243 : Blo 674311 2060243 := bstep (se 1 (by rfl) ⟨1545182, by rfl⟩ : syracuseStep 2060243 = 3090365) B3090365
theorem B1011695 : Blo 674311 1011695 := bstep (se 1 (by rfl) ⟨758771, by rfl⟩ : syracuseStep 1011695 = 1517543) B1517543
theorem B1011833 : Blo 674311 1011833 := bstep (se 2 (by rfl) ⟨379437, by rfl⟩ : syracuseStep 1011833 = 758875) B758875
theorem B1012379 : Blo 674311 1012379 := bstep (se 1 (by rfl) ⟨759284, by rfl⟩ : syracuseStep 1012379 = 1518569) B1518569
theorem B1012535 : Blo 674311 1012535 := bstep (se 1 (by rfl) ⟨759401, by rfl⟩ : syracuseStep 1012535 = 1518803) B1518803
theorem B1013279 : Blo 674311 1013279 := bstep (se 1 (by rfl) ⟨759959, by rfl⟩ : syracuseStep 1013279 = 1519919) B1519919
theorem B1014185 : Blo 674311 1014185 := bstep (se 2 (by rfl) ⟨380319, by rfl⟩ : syracuseStep 1014185 = 760639) B760639
theorem B1014779 : Blo 674311 1014779 := bstep (se 1 (by rfl) ⟨761084, by rfl⟩ : syracuseStep 1014779 = 1522169) B1522169
theorem B1014953 : Blo 674311 1014953 := bstep (se 2 (by rfl) ⟨380607, by rfl⟩ : syracuseStep 1014953 = 761215) B761215
theorem B1016615 : Blo 674311 1016615 := bstep (se 1 (by rfl) ⟨762461, by rfl⟩ : syracuseStep 1016615 = 1524923) B1524923
theorem B1016987 : Blo 674311 1016987 := bstep (se 1 (by rfl) ⟨762740, by rfl⟩ : syracuseStep 1016987 = 1525481) B1525481
theorem B6948065 : Blo 674311 6948065 := bstep (se 2 (by rfl) ⟨2605524, by rfl⟩ : syracuseStep 6948065 = 5211049) B5211049
theorem B1017143 : Blo 674311 1017143 := bstep (se 1 (by rfl) ⟨762857, by rfl⟩ : syracuseStep 1017143 = 1525715) B1525715
theorem B3245467 : Blo 674311 3245467 := bstep (se 1 (by rfl) ⟨2434100, by rfl⟩ : syracuseStep 3245467 = 4868201) B4868201
theorem B6162419 : Blo 674311 6162419 := bstep (se 1 (by rfl) ⟨4621814, by rfl⟩ : syracuseStep 6162419 = 9243629) B9243629
theorem B3246911 : Blo 674311 3246911 := bstep (se 1 (by rfl) ⟨2435183, by rfl⟩ : syracuseStep 3246911 = 4870367) B4870367
theorem B5213267 : Blo 674311 5213267 := bstep (se 1 (by rfl) ⟨3909950, by rfl⟩ : syracuseStep 5213267 = 7819901) B7819901
theorem B25038395 : Blo 674311 25038395 := bstep (se 1 (by rfl) ⟨18778796, by rfl⟩ : syracuseStep 25038395 = 37557593) B37557593
theorem B1281673 : Blo 674311 1281673 := bstep (se 2 (by rfl) ⟨480627, by rfl⟩ : syracuseStep 1281673 = 961255) B961255
theorem B5476207 : Blo 674311 5476207 := bstep (se 1 (by rfl) ⟨4107155, by rfl⟩ : syracuseStep 5476207 = 8214311) B8214311
theorem B2887919 : Blo 674311 2887919 := bstep (se 1 (by rfl) ⟨2165939, by rfl⟩ : syracuseStep 2887919 = 4331879) B4331879
theorem B1217015 : Blo 674311 1217015 := bstep (se 1 (by rfl) ⟨912761, by rfl⟩ : syracuseStep 1217015 = 1825523) B1825523
theorem B21893921 : Blo 674311 21893921 := bstep (se 2 (by rfl) ⟨8210220, by rfl⟩ : syracuseStep 21893921 = 16420441) B16420441
theorem B5935963 : Blo 674311 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B5772383 : Blo 674311 5772383 := bstep (se 1 (by rfl) ⟨4329287, by rfl⟩ : syracuseStep 5772383 = 8658575) B8658575
theorem B693487 : Blo 674311 693487 := bstep (se 1 (by rfl) ⟨520115, by rfl⟩ : syracuseStep 693487 = 1040231) B1040231
theorem B2561327 : Blo 674311 2561327 := bstep (se 1 (by rfl) ⟨1920995, by rfl⟩ : syracuseStep 2561327 = 3841991) B3841991
theorem B759199 : Blo 674311 759199 := bstep (se 1 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 759199 = 1138799) B1138799
theorem B21993565 : Blo 674311 21993565 := bstep (se 3 (by rfl) ⟨4123793, by rfl⟩ : syracuseStep 21993565 = 8247587) B8247587
theorem B3415607 : Blo 674311 3415607 := bstep (se 1 (by rfl) ⟨2561705, by rfl⟩ : syracuseStep 3415607 = 5123411) B5123411
theorem B761791 : Blo 674311 761791 := bstep (se 1 (by rfl) ⟨571343, by rfl⟩ : syracuseStep 761791 = 1142687) B1142687
theorem B5121467 : Blo 674311 5121467 := bstep (se 1 (by rfl) ⟨3841100, by rfl⟩ : syracuseStep 5121467 = 7682201) B7682201
theorem B1517705 : Blo 674311 1517705 := bstep (se 2 (by rfl) ⟨569139, by rfl⟩ : syracuseStep 1517705 = 1138279) B1138279
theorem B2435255 : Blo 674311 2435255 := bstep (se 1 (by rfl) ⟨1826441, by rfl⟩ : syracuseStep 2435255 = 3652883) B3652883
theorem B1517921 : Blo 674311 1517921 := bstep (se 2 (by rfl) ⟨569220, by rfl⟩ : syracuseStep 1517921 = 1138441) B1138441
theorem B1520639 : Blo 674311 1520639 := bstep (se 1 (by rfl) ⟨1140479, by rfl⟩ : syracuseStep 1520639 = 2280959) B2280959
theorem B1520801 : Blo 674311 1520801 := bstep (se 2 (by rfl) ⟨570300, by rfl⟩ : syracuseStep 1520801 = 1140601) B1140601
theorem B1521719 : Blo 674311 1521719 := bstep (se 1 (by rfl) ⟨1141289, by rfl⟩ : syracuseStep 1521719 = 2282579) B2282579
theorem B1521737 : Blo 674311 1521737 := bstep (se 2 (by rfl) ⟨570651, by rfl⟩ : syracuseStep 1521737 = 1141303) B1141303
theorem B1521755 : Blo 674311 1521755 := bstep (se 1 (by rfl) ⟨1141316, by rfl⟩ : syracuseStep 1521755 = 2282633) B2282633
theorem B2570575 : Blo 674311 2570575 := bstep (se 1 (by rfl) ⟨1927931, by rfl⟩ : syracuseStep 2570575 = 3855863) B3855863
theorem B3258751 : Blo 674311 3258751 := bstep (se 1 (by rfl) ⟨2444063, by rfl⟩ : syracuseStep 3258751 = 4888127) B4888127
theorem B1522439 : Blo 674311 1522439 := bstep (se 1 (by rfl) ⟨1141829, by rfl⟩ : syracuseStep 1522439 = 2283659) B2283659
theorem B2276585 : Blo 674311 2276585 := bstep (se 2 (by rfl) ⟨853719, by rfl⟩ : syracuseStep 2276585 = 1707439) B1707439
theorem B1523177 : Blo 674311 1523177 := bstep (se 2 (by rfl) ⟨571191, by rfl⟩ : syracuseStep 1523177 = 1142383) B1142383
theorem B5127785 : Blo 674311 5127785 := bstep (se 2 (by rfl) ⟨1922919, by rfl⟩ : syracuseStep 5127785 = 3845839) B3845839
theorem B3850031 : Blo 674311 3850031 := bstep (se 1 (by rfl) ⟨2887523, by rfl⟩ : syracuseStep 3850031 = 5775047) B5775047
theorem B2736091 : Blo 674311 2736091 := bstep (se 1 (by rfl) ⟨2052068, by rfl⟩ : syracuseStep 2736091 = 4104137) B4104137
theorem B2277449 : Blo 674311 2277449 := bstep (se 2 (by rfl) ⟨854043, by rfl⟩ : syracuseStep 2277449 = 1708087) B1708087
theorem B1523807 : Blo 674311 1523807 := bstep (se 1 (by rfl) ⟨1142855, by rfl⟩ : syracuseStep 1523807 = 2285711) B2285711
theorem B8437925 : Blo 674311 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B1523951 : Blo 674311 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B2278313 : Blo 674311 2278313 := bstep (se 2 (by rfl) ⟨854367, by rfl⟩ : syracuseStep 2278313 = 1708735) B1708735
theorem B4113479 : Blo 674311 4113479 := bstep (se 1 (by rfl) ⟨3085109, by rfl⟩ : syracuseStep 4113479 = 6170219) B6170219
theorem B7718651 : Blo 674311 7718651 := bstep (se 1 (by rfl) ⟨5788988, by rfl⟩ : syracuseStep 7718651 = 11577977) B11577977
theorem B3950375 : Blo 674311 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B3426299 : Blo 674311 3426299 := bstep (se 1 (by rfl) ⟨2569724, by rfl⟩ : syracuseStep 3426299 = 5139449) B5139449
theorem B2574767 : Blo 674311 2574767 := bstep (se 1 (by rfl) ⟨1931075, by rfl⟩ : syracuseStep 2574767 = 3862151) B3862151
theorem B674463 : Blo 674311 674463 := bstep (se 1 (by rfl) ⟨505847, by rfl⟩ : syracuseStep 674463 = 1011695) B1011695
theorem B674555 : Blo 674311 674555 := bstep (se 1 (by rfl) ⟨505916, by rfl⟩ : syracuseStep 674555 = 1011833) B1011833
theorem B3853403 : Blo 674311 3853403 := bstep (se 1 (by rfl) ⟨2890052, by rfl⟩ : syracuseStep 3853403 = 5780105) B5780105
theorem B674919 : Blo 674311 674919 := bstep (se 1 (by rfl) ⟨506189, by rfl⟩ : syracuseStep 674919 = 1012379) B1012379
theorem B675023 : Blo 674311 675023 := bstep (se 1 (by rfl) ⟨506267, by rfl⟩ : syracuseStep 675023 = 1012535) B1012535
theorem B5131673 : Blo 674311 5131673 := bstep (se 2 (by rfl) ⟨1924377, by rfl⟩ : syracuseStep 5131673 = 3848755) B3848755
theorem B73944521 : Blo 674311 73944521 := bstep (se 2 (by rfl) ⟨27729195, by rfl⟩ : syracuseStep 73944521 = 55458391) B55458391
theorem B675519 : Blo 674311 675519 := bstep (se 1 (by rfl) ⟨506639, by rfl⟩ : syracuseStep 675519 = 1013279) B1013279
theorem B9752723 : Blo 674311 9752723 := bstep (se 1 (by rfl) ⟨7314542, by rfl⟩ : syracuseStep 9752723 = 14629085) B14629085
theorem B676123 : Blo 674311 676123 := bstep (se 1 (by rfl) ⟨507092, by rfl⟩ : syracuseStep 676123 = 1014185) B1014185
theorem B676519 : Blo 674311 676519 := bstep (se 1 (by rfl) ⟨507389, by rfl⟩ : syracuseStep 676519 = 1014779) B1014779
theorem B3461885 : Blo 674311 3461885 := bstep (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) B1298207
theorem B3855113 : Blo 674311 3855113 := bstep (se 2 (by rfl) ⟨1445667, by rfl⟩ : syracuseStep 3855113 = 2891335) B2891335
theorem B676635 : Blo 674311 676635 := bstep (se 1 (by rfl) ⟨507476, by rfl⟩ : syracuseStep 676635 = 1014953) B1014953
theorem B1299623 : Blo 674311 1299623 := bstep (se 1 (by rfl) ⟨974717, by rfl⟩ : syracuseStep 1299623 = 1949435) B1949435
theorem B677403 : Blo 674311 677403 := bstep (se 1 (by rfl) ⟨508052, by rfl⟩ : syracuseStep 677403 = 1016105) B1016105
theorem B677607 : Blo 674311 677607 := bstep (se 1 (by rfl) ⟨508205, by rfl⟩ : syracuseStep 677607 = 1016411) B1016411
theorem B677887 : Blo 674311 677887 := bstep (se 1 (by rfl) ⟨508415, by rfl⟩ : syracuseStep 677887 = 1016831) B1016831
theorem B5789879 : Blo 674311 5789879 := bstep (se 1 (by rfl) ⟨4342409, by rfl⟩ : syracuseStep 5789879 = 8684819) B8684819
theorem B678143 : Blo 674311 678143 := bstep (se 1 (by rfl) ⟨508607, by rfl⟩ : syracuseStep 678143 = 1017215) B1017215
theorem B678207 : Blo 674311 678207 := bstep (se 1 (by rfl) ⟨508655, by rfl⟩ : syracuseStep 678207 = 1017311) B1017311
theorem B2742839 : Blo 674311 2742839 := bstep (se 1 (by rfl) ⟨2057129, by rfl⟩ : syracuseStep 2742839 = 4114259) B4114259
theorem B1923695 : Blo 674311 1923695 := bstep (se 1 (by rfl) ⟨1442771, by rfl⟩ : syracuseStep 1923695 = 2885543) B2885543
theorem B3432131 : Blo 674311 3432131 := bstep (se 1 (by rfl) ⟨2574098, by rfl⟩ : syracuseStep 3432131 = 5148197) B5148197
theorem B1368623 : Blo 674311 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B3859487 : Blo 674311 3859487 := bstep (se 1 (by rfl) ⟨2894615, by rfl⟩ : syracuseStep 3859487 = 5789231) B5789231
theorem B19522619 : Blo 674311 19522619 := bstep (se 1 (by rfl) ⟨14641964, by rfl⟩ : syracuseStep 19522619 = 29283929) B29283929
theorem B2287655 : Blo 674311 2287655 := bstep (se 1 (by rfl) ⟨1715741, by rfl⟩ : syracuseStep 2287655 = 3431483) B3431483
theorem B1141499 : Blo 674311 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B1371583 : Blo 674311 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B1929071 : Blo 674311 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B1012457 : Blo 674311 1012457 := bstep (se 2 (by rfl) ⟨379671, by rfl⟩ : syracuseStep 1012457 = 759343) B759343
theorem B1012703 : Blo 674311 1012703 := bstep (se 1 (by rfl) ⟨759527, by rfl⟩ : syracuseStep 1012703 = 1519055) B1519055
theorem B1373495 : Blo 674311 1373495 := bstep (se 1 (by rfl) ⟨1030121, by rfl⟩ : syracuseStep 1373495 = 2060243) B2060243
theorem B1930655 : Blo 674311 1930655 := bstep (se 1 (by rfl) ⟨1447991, by rfl⟩ : syracuseStep 1930655 = 2895983) B2895983
theorem B6518231 : Blo 674311 6518231 := bstep (se 1 (by rfl) ⟨4888673, by rfl⟩ : syracuseStep 6518231 = 9777347) B9777347
theorem B1014239 : Blo 674311 1014239 := bstep (se 1 (by rfl) ⟨760679, by rfl⟩ : syracuseStep 1014239 = 1521359) B1521359
theorem B1014911 : Blo 674311 1014911 := bstep (se 1 (by rfl) ⟨761183, by rfl⟩ : syracuseStep 1014911 = 1522367) B1522367
theorem B1015871 : Blo 674311 1015871 := bstep (se 1 (by rfl) ⟨761903, by rfl⟩ : syracuseStep 1015871 = 1523807) B1523807
theorem B1015967 : Blo 674311 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B5145767 : Blo 674311 5145767 := bstep (se 1 (by rfl) ⟨3859325, by rfl⟩ : syracuseStep 5145767 = 7718651) B7718651
theorem B4327289 : Blo 674311 4327289 := bstep (se 2 (by rfl) ⟨1622733, by rfl⟩ : syracuseStep 4327289 = 3245467) B3245467
theorem B2164607 : Blo 674311 2164607 := bstep (se 1 (by rfl) ⟨1623455, by rfl⟩ : syracuseStep 2164607 = 3246911) B3246911
theorem B3475511 : Blo 674311 3475511 := bstep (se 1 (by rfl) ⟨2606633, by rfl⟩ : syracuseStep 3475511 = 5213267) B5213267
theorem B1707551 : Blo 674311 1707551 := bstep (se 1 (by rfl) ⟨1280663, by rfl⟩ : syracuseStep 1707551 = 2561327) B2561327
theorem B1282463 : Blo 674311 1282463 := bstep (se 1 (by rfl) ⟨961847, by rfl⟩ : syracuseStep 1282463 = 1923695) B1923695
theorem B1708897 : Blo 674311 1708897 := bstep (se 2 (by rfl) ⟨640836, by rfl⟩ : syracuseStep 1708897 = 1281673) B1281673
theorem B13015079 : Blo 674311 13015079 := bstep (se 1 (by rfl) ⟨9761309, by rfl⟩ : syracuseStep 13015079 = 19522619) B19522619
theorem B3414311 : Blo 674311 3414311 := bstep (se 1 (by rfl) ⟨2560733, by rfl⟩ : syracuseStep 3414311 = 5121467) B5121467
theorem B760999 : Blo 674311 760999 := bstep (se 1 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 760999 = 1141499) B1141499
theorem B1286047 : Blo 674311 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B1287103 : Blo 674311 1287103 := bstep (se 1 (by rfl) ⟨965327, by rfl⟩ : syracuseStep 1287103 = 1930655) B1930655
theorem B1517723 : Blo 674311 1517723 := bstep (se 1 (by rfl) ⟨1138292, by rfl⟩ : syracuseStep 1517723 = 2276585) B2276585
theorem B3418523 : Blo 674311 3418523 := bstep (se 1 (by rfl) ⟨2563892, by rfl⟩ : syracuseStep 3418523 = 5127785) B5127785
theorem B2566687 : Blo 674311 2566687 := bstep (se 1 (by rfl) ⟨1925015, by rfl⟩ : syracuseStep 2566687 = 3850031) B3850031
theorem B3648121 : Blo 674311 3648121 := bstep (se 2 (by rfl) ⟨1368045, by rfl⟩ : syracuseStep 3648121 = 2736091) B2736091
theorem B1518299 : Blo 674311 1518299 := bstep (se 1 (by rfl) ⟨1138724, by rfl⟩ : syracuseStep 1518299 = 2277449) B2277449
theorem B1518875 : Blo 674311 1518875 := bstep (se 1 (by rfl) ⟨1139156, by rfl⟩ : syracuseStep 1518875 = 2278313) B2278313
theorem B4108279 : Blo 674311 4108279 := bstep (se 1 (by rfl) ⟨3081209, by rfl⟩ : syracuseStep 4108279 = 6162419) B6162419
theorem B1716511 : Blo 674311 1716511 := bstep (se 1 (by rfl) ⟨1287383, by rfl⟩ : syracuseStep 1716511 = 2574767) B2574767
theorem B2568935 : Blo 674311 2568935 := bstep (se 1 (by rfl) ⟨1926701, by rfl⟩ : syracuseStep 2568935 = 3853403) B3853403
theorem B3421115 : Blo 674311 3421115 := bstep (se 1 (by rfl) ⟨2565836, by rfl⟩ : syracuseStep 3421115 = 5131673) B5131673
theorem B49296347 : Blo 674311 49296347 := bstep (se 1 (by rfl) ⟨36972260, by rfl⟩ : syracuseStep 49296347 = 73944521) B73944521
theorem B16692263 : Blo 674311 16692263 := bstep (se 1 (by rfl) ⟨12519197, by rfl⟩ : syracuseStep 16692263 = 25038395) B25038395
theorem B6501815 : Blo 674311 6501815 := bstep (se 1 (by rfl) ⟨4876361, by rfl⟩ : syracuseStep 6501815 = 9752723) B9752723
theorem B2307923 : Blo 674311 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B2570075 : Blo 674311 2570075 := bstep (se 1 (by rfl) ⟨1927556, by rfl⟩ : syracuseStep 2570075 = 3855113) B3855113
theorem B14595947 : Blo 674311 14595947 := bstep (se 1 (by rfl) ⟨10946960, by rfl⟩ : syracuseStep 14595947 = 21893921) B21893921
theorem B18528173 : Blo 674311 18528173 := bstep (se 3 (by rfl) ⟨3474032, by rfl⟩ : syracuseStep 18528173 = 6948065) B6948065
theorem B3848255 : Blo 674311 3848255 := bstep (se 1 (by rfl) ⟨2886191, by rfl⟩ : syracuseStep 3848255 = 5772383) B5772383
theorem B2277071 : Blo 674311 2277071 := bstep (se 1 (by rfl) ⟨1707803, by rfl⟩ : syracuseStep 2277071 = 3415607) B3415607
theorem B2572991 : Blo 674311 2572991 := bstep (se 1 (by rfl) ⟨1929743, by rfl⟩ : syracuseStep 2572991 = 3859487) B3859487
theorem B7914617 : Blo 674311 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B1525103 : Blo 674311 1525103 := bstep (se 1 (by rfl) ⟨1143827, by rfl⟩ : syracuseStep 1525103 = 2287655) B2287655
theorem B1623503 : Blo 674311 1623503 := bstep (se 1 (by rfl) ⟨1217627, by rfl⟩ : syracuseStep 1623503 = 2435255) B2435255
theorem B3427433 : Blo 674311 3427433 := bstep (se 2 (by rfl) ⟨1285287, by rfl⟩ : syracuseStep 3427433 = 2570575) B2570575
theorem B674971 : Blo 674311 674971 := bstep (se 1 (by rfl) ⟨506228, by rfl⟩ : syracuseStep 674971 = 1012457) B1012457
theorem B4345001 : Blo 674311 4345001 := bstep (se 2 (by rfl) ⟨1629375, by rfl⟩ : syracuseStep 4345001 = 3258751) B3258751
theorem B675135 : Blo 674311 675135 := bstep (se 1 (by rfl) ⟨506351, by rfl⟩ : syracuseStep 675135 = 1012703) B1012703
theorem B4345487 : Blo 674311 4345487 := bstep (se 1 (by rfl) ⟨3259115, by rfl⟩ : syracuseStep 4345487 = 6518231) B6518231
theorem B676159 : Blo 674311 676159 := bstep (se 1 (by rfl) ⟨507119, by rfl⟩ : syracuseStep 676159 = 1014239) B1014239
theorem B676607 : Blo 674311 676607 := bstep (se 1 (by rfl) ⟨507455, by rfl⟩ : syracuseStep 676607 = 1014911) B1014911
theorem B5625283 : Blo 674311 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B677743 : Blo 674311 677743 := bstep (se 1 (by rfl) ⟨508307, by rfl⟩ : syracuseStep 677743 = 1016615) B1016615
theorem B2742319 : Blo 674311 2742319 := bstep (se 1 (by rfl) ⟨2056739, by rfl⟩ : syracuseStep 2742319 = 4113479) B4113479
theorem B677991 : Blo 674311 677991 := bstep (se 1 (by rfl) ⟨508493, by rfl⟩ : syracuseStep 677991 = 1016987) B1016987
theorem B678095 : Blo 674311 678095 := bstep (se 1 (by rfl) ⟨508571, by rfl⟩ : syracuseStep 678095 = 1017143) B1017143
theorem B2284199 : Blo 674311 2284199 := bstep (se 1 (by rfl) ⟨1713149, by rfl⟩ : syracuseStep 2284199 = 3426299) B3426299
theorem B1925279 : Blo 674311 1925279 := bstep (se 1 (by rfl) ⟨1443959, by rfl⟩ : syracuseStep 1925279 = 2887919) B2887919
theorem B811343 : Blo 674311 811343 := bstep (se 1 (by rfl) ⟨608507, by rfl⟩ : syracuseStep 811343 = 1217015) B1217015
theorem B3465661 : Blo 674311 3465661 := bstep (se 3 (by rfl) ⟨649811, by rfl⟩ : syracuseStep 3465661 = 1299623) B1299623
theorem B3662653 : Blo 674311 3662653 := bstep (se 3 (by rfl) ⟨686747, by rfl⟩ : syracuseStep 3662653 = 1373495) B1373495
theorem B3859919 : Blo 674311 3859919 := bstep (se 1 (by rfl) ⟨2894939, by rfl⟩ : syracuseStep 3859919 = 5789879) B5789879
theorem B1828559 : Blo 674311 1828559 := bstep (se 1 (by rfl) ⟨1371419, by rfl⟩ : syracuseStep 1828559 = 2742839) B2742839
theorem B1828777 : Blo 674311 1828777 := bstep (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) B1371583
theorem B2288087 : Blo 674311 2288087 := bstep (se 1 (by rfl) ⟨1716065, by rfl⟩ : syracuseStep 2288087 = 3432131) B3432131
theorem B7301609 : Blo 674311 7301609 := bstep (se 2 (by rfl) ⟨2738103, by rfl⟩ : syracuseStep 7301609 = 5476207) B5476207
theorem B912415 : Blo 674311 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B3698597 : Blo 674311 3698597 := bstep (se 4 (by rfl) ⟨346743, by rfl⟩ : syracuseStep 3698597 = 693487) B693487
theorem B1011803 : Blo 674311 1011803 := bstep (se 1 (by rfl) ⟨758852, by rfl⟩ : syracuseStep 1011803 = 1517705) B1517705
theorem B1011947 : Blo 674311 1011947 := bstep (se 1 (by rfl) ⟨758960, by rfl⟩ : syracuseStep 1011947 = 1517921) B1517921
theorem B1012265 : Blo 674311 1012265 := bstep (se 2 (by rfl) ⟨379599, by rfl⟩ : syracuseStep 1012265 = 759199) B759199
theorem B29324753 : Blo 674311 29324753 := bstep (se 2 (by rfl) ⟨10996782, by rfl⟩ : syracuseStep 29324753 = 21993565) B21993565
theorem B42137333 : Blo 674311 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B1013759 : Blo 674311 1013759 := bstep (se 1 (by rfl) ⟨760319, by rfl⟩ : syracuseStep 1013759 = 1520639) B1520639
theorem B1013867 : Blo 674311 1013867 := bstep (se 1 (by rfl) ⟨760400, by rfl⟩ : syracuseStep 1013867 = 1520801) B1520801
theorem B1014479 : Blo 674311 1014479 := bstep (se 1 (by rfl) ⟨760859, by rfl⟩ : syracuseStep 1014479 = 1521719) B1521719
theorem B1014491 : Blo 674311 1014491 := bstep (se 1 (by rfl) ⟨760868, by rfl⟩ : syracuseStep 1014491 = 1521737) B1521737
theorem B1014503 : Blo 674311 1014503 := bstep (se 1 (by rfl) ⟨760877, by rfl⟩ : syracuseStep 1014503 = 1521755) B1521755
theorem B1014959 : Blo 674311 1014959 := bstep (se 1 (by rfl) ⟨761219, by rfl⟩ : syracuseStep 1014959 = 1522439) B1522439
theorem B1015451 : Blo 674311 1015451 := bstep (se 1 (by rfl) ⟨761588, by rfl⟩ : syracuseStep 1015451 = 1523177) B1523177
theorem B1015721 : Blo 674311 1015721 := bstep (se 2 (by rfl) ⟨380895, by rfl⟩ : syracuseStep 1015721 = 761791) B761791
theorem B4620881 : Blo 674311 4620881 := bstep (se 2 (by rfl) ⟨1732830, by rfl⟩ : syracuseStep 4620881 = 3465661) B3465661
theorem B5276411 : Blo 674311 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B2163581 : Blo 674311 2163581 := bstep (se 3 (by rfl) ⟨405671, by rfl⟩ : syracuseStep 2163581 = 811343) B811343
theorem B1016735 : Blo 674311 1016735 := bstep (se 1 (by rfl) ⟨762551, by rfl⟩ : syracuseStep 1016735 = 1525103) B1525103
theorem B1082335 : Blo 674311 1082335 := bstep (se 1 (by rfl) ⟨811751, by rfl⟩ : syracuseStep 1082335 = 1623503) B1623503
theorem B4883537 : Blo 674311 4883537 := bstep (se 2 (by rfl) ⟨1831326, by rfl⟩ : syracuseStep 4883537 = 3662653) B3662653
theorem B2884859 : Blo 674311 2884859 := bstep (se 1 (by rfl) ⟨2163644, by rfl⟩ : syracuseStep 2884859 = 4327289) B4327289
theorem B1443071 : Blo 674311 1443071 := bstep (se 1 (by rfl) ⟨1082303, by rfl⟩ : syracuseStep 1443071 = 2164607) B2164607
theorem B854975 : Blo 674311 854975 := bstep (se 1 (by rfl) ⟨641231, by rfl⟩ : syracuseStep 854975 = 1282463) B1282463
theorem B1216553 : Blo 674311 1216553 := bstep (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) B912415
theorem B5477705 : Blo 674311 5477705 := bstep (se 2 (by rfl) ⟨2054139, by rfl⟩ : syracuseStep 5477705 = 4108279) B4108279
theorem B1283519 : Blo 674311 1283519 := bstep (se 1 (by rfl) ⟨962639, by rfl⟩ : syracuseStep 1283519 = 1925279) B1925279
theorem B1219039 : Blo 674311 1219039 := bstep (se 1 (by rfl) ⟨914279, by rfl⟩ : syracuseStep 1219039 = 1828559) B1828559
theorem B2465731 : Blo 674311 2465731 := bstep (se 1 (by rfl) ⟨1849298, by rfl⟩ : syracuseStep 2465731 = 3698597) B3698597
theorem B1712623 : Blo 674311 1712623 := bstep (se 1 (by rfl) ⟨1284467, by rfl⟩ : syracuseStep 1712623 = 2568935) B2568935
theorem B4334543 : Blo 674311 4334543 := bstep (se 1 (by rfl) ⟨3250907, by rfl⟩ : syracuseStep 4334543 = 6501815) B6501815
theorem B28091555 : Blo 674311 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B1713383 : Blo 674311 1713383 := bstep (se 1 (by rfl) ⟨1285037, by rfl⟩ : syracuseStep 1713383 = 2570075) B2570075
theorem B2565503 : Blo 674311 2565503 := bstep (se 1 (by rfl) ⟨1924127, by rfl⟩ : syracuseStep 2565503 = 3848255) B3848255
theorem B1518047 : Blo 674311 1518047 := bstep (se 1 (by rfl) ⟨1138535, by rfl⟩ : syracuseStep 1518047 = 2277071) B2277071
theorem B1714729 : Blo 674311 1714729 := bstep (se 2 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 1714729 = 1286047) B1286047
theorem B1715327 : Blo 674311 1715327 := bstep (se 1 (by rfl) ⟨1286495, by rfl⟩ : syracuseStep 1715327 = 2572991) B2572991
theorem B1716137 : Blo 674311 1716137 := bstep (se 2 (by rfl) ⟨643551, by rfl⟩ : syracuseStep 1716137 = 1287103) B1287103
theorem B2896667 : Blo 674311 2896667 := bstep (se 1 (by rfl) ⟨2172500, by rfl⟩ : syracuseStep 2896667 = 4345001) B4345001
theorem B2896991 : Blo 674311 2896991 := bstep (se 1 (by rfl) ⟨2172743, by rfl⟩ : syracuseStep 2896991 = 4345487) B4345487
theorem B2438369 : Blo 674311 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B3422249 : Blo 674311 3422249 := bstep (se 2 (by rfl) ⟨1283343, by rfl⟩ : syracuseStep 3422249 = 2566687) B2566687
theorem B2276207 : Blo 674311 2276207 := bstep (se 1 (by rfl) ⟨1707155, by rfl⟩ : syracuseStep 2276207 = 3414311) B3414311
theorem B1522799 : Blo 674311 1522799 := bstep (se 1 (by rfl) ⟨1142099, by rfl⟩ : syracuseStep 1522799 = 2284199) B2284199
theorem B2573279 : Blo 674311 2573279 := bstep (se 1 (by rfl) ⟨1929959, by rfl⟩ : syracuseStep 2573279 = 3859919) B3859919
theorem B2278529 : Blo 674311 2278529 := bstep (se 2 (by rfl) ⟨854448, by rfl⟩ : syracuseStep 2278529 = 1708897) B1708897
theorem B2279015 : Blo 674311 2279015 := bstep (se 1 (by rfl) ⟨1709261, by rfl⟩ : syracuseStep 2279015 = 3418523) B3418523
theorem B1525391 : Blo 674311 1525391 := bstep (se 1 (by rfl) ⟨1144043, by rfl⟩ : syracuseStep 1525391 = 2288087) B2288087
theorem B4867739 : Blo 674311 4867739 := bstep (se 1 (by rfl) ⟨3650804, by rfl⟩ : syracuseStep 4867739 = 7301609) B7301609
theorem B674535 : Blo 674311 674535 := bstep (se 1 (by rfl) ⟨505901, by rfl⟩ : syracuseStep 674535 = 1011803) B1011803
theorem B3656425 : Blo 674311 3656425 := bstep (se 2 (by rfl) ⟨1371159, by rfl⟩ : syracuseStep 3656425 = 2742319) B2742319
theorem B674631 : Blo 674311 674631 := bstep (se 1 (by rfl) ⟨505973, by rfl⟩ : syracuseStep 674631 = 1011947) B1011947
theorem B674843 : Blo 674311 674843 := bstep (se 1 (by rfl) ⟨506132, by rfl⟩ : syracuseStep 674843 = 1012265) B1012265
theorem B2280743 : Blo 674311 2280743 := bstep (se 1 (by rfl) ⟨1710557, by rfl⟩ : syracuseStep 2280743 = 3421115) B3421115
theorem B11128175 : Blo 674311 11128175 := bstep (se 1 (by rfl) ⟨8346131, by rfl⟩ : syracuseStep 11128175 = 16692263) B16692263
theorem B19549835 : Blo 674311 19549835 := bstep (se 1 (by rfl) ⟨14662376, by rfl⟩ : syracuseStep 19549835 = 29324753) B29324753
theorem B675839 : Blo 674311 675839 := bstep (se 1 (by rfl) ⟨506879, by rfl⟩ : syracuseStep 675839 = 1013759) B1013759
theorem B675911 : Blo 674311 675911 := bstep (se 1 (by rfl) ⟨506933, by rfl⟩ : syracuseStep 675911 = 1013867) B1013867
theorem B676319 : Blo 674311 676319 := bstep (se 1 (by rfl) ⟨507239, by rfl⟩ : syracuseStep 676319 = 1014479) B1014479
theorem B676327 : Blo 674311 676327 := bstep (se 1 (by rfl) ⟨507245, by rfl⟩ : syracuseStep 676327 = 1014491) B1014491
theorem B676335 : Blo 674311 676335 := bstep (se 1 (by rfl) ⟨507251, by rfl⟩ : syracuseStep 676335 = 1014503) B1014503
theorem B676639 : Blo 674311 676639 := bstep (se 1 (by rfl) ⟨507479, by rfl⟩ : syracuseStep 676639 = 1014959) B1014959
theorem B676967 : Blo 674311 676967 := bstep (se 1 (by rfl) ⟨507725, by rfl⟩ : syracuseStep 676967 = 1015451) B1015451
theorem B677147 : Blo 674311 677147 := bstep (se 1 (by rfl) ⟨507860, by rfl⟩ : syracuseStep 677147 = 1015721) B1015721
theorem B677247 : Blo 674311 677247 := bstep (se 1 (by rfl) ⟨507935, by rfl⟩ : syracuseStep 677247 = 1015871) B1015871
theorem B677311 : Blo 674311 677311 := bstep (se 1 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 677311 = 1015967) B1015967
theorem B3430511 : Blo 674311 3430511 := bstep (se 1 (by rfl) ⟨2572883, by rfl⟩ : syracuseStep 3430511 = 5145767) B5145767
theorem B2317007 : Blo 674311 2317007 := bstep (se 1 (by rfl) ⟨1737755, by rfl⟩ : syracuseStep 2317007 = 3475511) B3475511
theorem B2284955 : Blo 674311 2284955 := bstep (se 1 (by rfl) ⟨1713716, by rfl⟩ : syracuseStep 2284955 = 3427433) B3427433
theorem B1138367 : Blo 674311 1138367 := bstep (se 1 (by rfl) ⟨853775, by rfl⟩ : syracuseStep 1138367 = 1707551) B1707551
theorem B19456645 : Blo 674311 19456645 := bstep (se 4 (by rfl) ⟨1824060, by rfl⟩ : syracuseStep 19456645 = 3648121) B3648121
theorem B8676719 : Blo 674311 8676719 := bstep (se 1 (by rfl) ⟨6507539, by rfl⟩ : syracuseStep 8676719 = 13015079) B13015079
theorem B2288681 : Blo 674311 2288681 := bstep (se 2 (by rfl) ⟨858255, by rfl⟩ : syracuseStep 2288681 = 1716511) B1716511
theorem B1011815 : Blo 674311 1011815 := bstep (se 1 (by rfl) ⟨758861, by rfl⟩ : syracuseStep 1011815 = 1517723) B1517723
theorem B1012199 : Blo 674311 1012199 := bstep (se 1 (by rfl) ⟨759149, by rfl⟩ : syracuseStep 1012199 = 1518299) B1518299
theorem B7500377 : Blo 674311 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B1012583 : Blo 674311 1012583 := bstep (se 1 (by rfl) ⟨759437, by rfl⟩ : syracuseStep 1012583 = 1518875) B1518875
theorem B32864231 : Blo 674311 32864231 := bstep (se 1 (by rfl) ⟨24648173, by rfl⟩ : syracuseStep 32864231 = 49296347) B49296347
theorem B1538615 : Blo 674311 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B9730631 : Blo 674311 9730631 := bstep (se 1 (by rfl) ⟨7297973, by rfl⟩ : syracuseStep 9730631 = 14595947) B14595947
theorem B12352115 : Blo 674311 12352115 := bstep (se 1 (by rfl) ⟨9264086, by rfl⟩ : syracuseStep 12352115 = 18528173) B18528173
theorem B1014665 : Blo 674311 1014665 := bstep (se 2 (by rfl) ⟨380499, by rfl⟩ : syracuseStep 1014665 = 760999) B760999
theorem B3244141 : Blo 674311 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B3080587 : Blo 674311 3080587 := bstep (se 1 (by rfl) ⟨2310440, by rfl⟩ : syracuseStep 3080587 = 4620881) B4620881
theorem B1442387 : Blo 674311 1442387 := bstep (se 1 (by rfl) ⟨1081790, by rfl⟩ : syracuseStep 1442387 = 2163581) B2163581
theorem B1016927 : Blo 674311 1016927 := bstep (se 1 (by rfl) ⟨762695, by rfl⟩ : syracuseStep 1016927 = 1525391) B1525391
theorem B3245159 : Blo 674311 3245159 := bstep (se 1 (by rfl) ⟨2433869, by rfl⟩ : syracuseStep 3245159 = 4867739) B4867739
theorem B1443113 : Blo 674311 1443113 := bstep (se 2 (by rfl) ⟨541167, by rfl⟩ : syracuseStep 1443113 = 1082335) B1082335
theorem B855679 : Blo 674311 855679 := bstep (se 1 (by rfl) ⟨641759, by rfl⟩ : syracuseStep 855679 = 1283519) B1283519
theorem B758911 : Blo 674311 758911 := bstep (se 1 (by rfl) ⟨569183, by rfl⟩ : syracuseStep 758911 = 1138367) B1138367
theorem B2889695 : Blo 674311 2889695 := bstep (se 1 (by rfl) ⟨2167271, by rfl⟩ : syracuseStep 2889695 = 4334543) B4334543
theorem B1710335 : Blo 674311 1710335 := bstep (se 1 (by rfl) ⟨1282751, by rfl⟩ : syracuseStep 1710335 = 2565503) B2565503
theorem B4102973 : Blo 674311 4102973 := bstep (se 3 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 4102973 = 1538615) B1538615
theorem B8234743 : Blo 674311 8234743 := bstep (se 1 (by rfl) ⟨6176057, by rfl⟩ : syracuseStep 8234743 = 12352115) B12352115
theorem B1517471 : Blo 674311 1517471 := bstep (se 1 (by rfl) ⟨1138103, by rfl⟩ : syracuseStep 1517471 = 2276207) B2276207
theorem B13150565 : Blo 674311 13150565 := bstep (se 4 (by rfl) ⟨1232865, by rfl⟩ : syracuseStep 13150565 = 2465731) B2465731
theorem B3517607 : Blo 674311 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B1715519 : Blo 674311 1715519 := bstep (se 1 (by rfl) ⟨1286639, by rfl⟩ : syracuseStep 1715519 = 2573279) B2573279
theorem B1519019 : Blo 674311 1519019 := bstep (se 1 (by rfl) ⟨1139264, by rfl⟩ : syracuseStep 1519019 = 2278529) B2278529
theorem B962047 : Blo 674311 962047 := bstep (se 1 (by rfl) ⟨721535, by rfl⟩ : syracuseStep 962047 = 1443071) B1443071
theorem B1519343 : Blo 674311 1519343 := bstep (se 1 (by rfl) ⟨1139507, by rfl⟩ : syracuseStep 1519343 = 2279015) B2279015
theorem B20001005 : Blo 674311 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B1520495 : Blo 674311 1520495 := bstep (se 1 (by rfl) ⟨1140371, by rfl⟩ : syracuseStep 1520495 = 2280743) B2280743
theorem B7418783 : Blo 674311 7418783 := bstep (se 1 (by rfl) ⟨5564087, by rfl⟩ : syracuseStep 7418783 = 11128175) B11128175
theorem B6501541 : Blo 674311 6501541 := bstep (se 4 (by rfl) ⟨609519, by rfl⟩ : syracuseStep 6501541 = 1219039) B1219039
theorem B13022765 : Blo 674311 13022765 := bstep (se 3 (by rfl) ⟨2441768, by rfl⟩ : syracuseStep 13022765 = 4883537) B4883537
theorem B3651803 : Blo 674311 3651803 := bstep (se 1 (by rfl) ⟨2738852, by rfl⟩ : syracuseStep 3651803 = 5477705) B5477705
theorem B1523303 : Blo 674311 1523303 := bstep (se 1 (by rfl) ⟨1142477, by rfl⟩ : syracuseStep 1523303 = 2284955) B2284955
theorem B18727703 : Blo 674311 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B5784479 : Blo 674311 5784479 := bstep (se 1 (by rfl) ⟨4338359, by rfl⟩ : syracuseStep 5784479 = 8676719) B8676719
theorem B6178685 : Blo 674311 6178685 := bstep (se 3 (by rfl) ⟨1158503, by rfl⟩ : syracuseStep 6178685 = 2317007) B2317007
theorem B1525787 : Blo 674311 1525787 := bstep (se 1 (by rfl) ⟨1144340, by rfl⟩ : syracuseStep 1525787 = 2288681) B2288681
theorem B2279933 : Blo 674311 2279933 := bstep (se 3 (by rfl) ⟨427487, by rfl⟩ : syracuseStep 2279933 = 854975) B854975
theorem B674543 : Blo 674311 674543 := bstep (se 1 (by rfl) ⟨505907, by rfl⟩ : syracuseStep 674543 = 1011815) B1011815
theorem B674799 : Blo 674311 674799 := bstep (se 1 (by rfl) ⟨506099, by rfl⟩ : syracuseStep 674799 = 1012199) B1012199
theorem B675055 : Blo 674311 675055 := bstep (se 1 (by rfl) ⟨506291, by rfl⟩ : syracuseStep 675055 = 1012583) B1012583
theorem B1625579 : Blo 674311 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B21909487 : Blo 674311 21909487 := bstep (se 1 (by rfl) ⟨16432115, by rfl⟩ : syracuseStep 21909487 = 32864231) B32864231
theorem B2281499 : Blo 674311 2281499 := bstep (se 1 (by rfl) ⟨1711124, by rfl⟩ : syracuseStep 2281499 = 3422249) B3422249
theorem B676443 : Blo 674311 676443 := bstep (se 1 (by rfl) ⟨507332, by rfl⟩ : syracuseStep 676443 = 1014665) B1014665
theorem B677823 : Blo 674311 677823 := bstep (se 1 (by rfl) ⟨508367, by rfl⟩ : syracuseStep 677823 = 1016735) B1016735
theorem B2283497 : Blo 674311 2283497 := bstep (se 2 (by rfl) ⟨856311, by rfl⟩ : syracuseStep 2283497 = 1712623) B1712623
theorem B1923239 : Blo 674311 1923239 := bstep (se 1 (by rfl) ⟨1442429, by rfl⟩ : syracuseStep 1923239 = 2884859) B2884859
theorem B25942193 : Blo 674311 25942193 := bstep (se 2 (by rfl) ⟨9728322, by rfl⟩ : syracuseStep 25942193 = 19456645) B19456645
theorem B13033223 : Blo 674311 13033223 := bstep (se 1 (by rfl) ⟨9774917, by rfl⟩ : syracuseStep 13033223 = 19549835) B19549835
theorem B2286305 : Blo 674311 2286305 := bstep (se 2 (by rfl) ⟨857364, by rfl⟩ : syracuseStep 2286305 = 1714729) B1714729
theorem B4875233 : Blo 674311 4875233 := bstep (se 2 (by rfl) ⟨1828212, by rfl⟩ : syracuseStep 4875233 = 3656425) B3656425
theorem B2287007 : Blo 674311 2287007 := bstep (se 1 (by rfl) ⟨1715255, by rfl⟩ : syracuseStep 2287007 = 3430511) B3430511
theorem B1142255 : Blo 674311 1142255 := bstep (se 1 (by rfl) ⟨856691, by rfl⟩ : syracuseStep 1142255 = 1713383) B1713383
theorem B1012031 : Blo 674311 1012031 := bstep (se 1 (by rfl) ⟨759023, by rfl⟩ : syracuseStep 1012031 = 1518047) B1518047
theorem B1143551 : Blo 674311 1143551 := bstep (se 1 (by rfl) ⟨857663, by rfl⟩ : syracuseStep 1143551 = 1715327) B1715327
theorem B1144091 : Blo 674311 1144091 := bstep (se 1 (by rfl) ⟨858068, by rfl⟩ : syracuseStep 1144091 = 1716137) B1716137
theorem B1931111 : Blo 674311 1931111 := bstep (se 1 (by rfl) ⟨1448333, by rfl⟩ : syracuseStep 1931111 = 2896667) B2896667
theorem B1931327 : Blo 674311 1931327 := bstep (se 1 (by rfl) ⟨1448495, by rfl⟩ : syracuseStep 1931327 = 2896991) B2896991
theorem B6487087 : Blo 674311 6487087 := bstep (se 1 (by rfl) ⟨4865315, by rfl⟩ : syracuseStep 6487087 = 9730631) B9730631
theorem B1015199 : Blo 674311 1015199 := bstep (se 1 (by rfl) ⟨761399, by rfl⟩ : syracuseStep 1015199 = 1522799) B1522799
theorem B4325521 : Blo 674311 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B12485135 : Blo 674311 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B2163439 : Blo 674311 2163439 := bstep (se 1 (by rfl) ⟨1622579, by rfl⟩ : syracuseStep 2163439 = 3245159) B3245159
theorem B1017191 : Blo 674311 1017191 := bstep (se 1 (by rfl) ⟨762893, by rfl⟩ : syracuseStep 1017191 = 1525787) B1525787
theorem B1083719 : Blo 674311 1083719 := bstep (se 1 (by rfl) ⟨812789, by rfl⟩ : syracuseStep 1083719 = 1625579) B1625579
theorem B10979657 : Blo 674311 10979657 := bstep (se 2 (by rfl) ⟨4117371, by rfl⟩ : syracuseStep 10979657 = 8234743) B8234743
theorem B1282159 : Blo 674311 1282159 := bstep (se 1 (by rfl) ⟨961619, by rfl⟩ : syracuseStep 1282159 = 1923239) B1923239
theorem B1282729 : Blo 674311 1282729 := bstep (se 2 (by rfl) ⟨481023, by rfl⟩ : syracuseStep 1282729 = 962047) B962047
theorem B8688815 : Blo 674311 8688815 := bstep (se 1 (by rfl) ⟨6516611, by rfl⟩ : syracuseStep 8688815 = 13033223) B13033223
theorem B761503 : Blo 674311 761503 := bstep (se 1 (by rfl) ⟨571127, by rfl⟩ : syracuseStep 761503 = 1142255) B1142255
theorem B762367 : Blo 674311 762367 := bstep (se 1 (by rfl) ⟨571775, by rfl⟩ : syracuseStep 762367 = 1143551) B1143551
theorem B762727 : Blo 674311 762727 := bstep (se 1 (by rfl) ⟨572045, by rfl⟩ : syracuseStep 762727 = 1144091) B1144091
theorem B1287407 : Blo 674311 1287407 := bstep (se 1 (by rfl) ⟨965555, by rfl⟩ : syracuseStep 1287407 = 1931111) B1931111
theorem B1287551 : Blo 674311 1287551 := bstep (se 1 (by rfl) ⟨965663, by rfl⟩ : syracuseStep 1287551 = 1931327) B1931327
theorem B2434535 : Blo 674311 2434535 := bstep (se 1 (by rfl) ⟨1825901, by rfl⟩ : syracuseStep 2434535 = 3651803) B3651803
theorem B4107449 : Blo 674311 4107449 := bstep (se 2 (by rfl) ⟨1540293, by rfl⟩ : syracuseStep 4107449 = 3080587) B3080587
theorem B962075 : Blo 674311 962075 := bstep (se 1 (by rfl) ⟨721556, by rfl⟩ : syracuseStep 962075 = 1443113) B1443113
theorem B3846365 : Blo 674311 3846365 := bstep (se 3 (by rfl) ⟨721193, by rfl⟩ : syracuseStep 3846365 = 1442387) B1442387
theorem B1519955 : Blo 674311 1519955 := bstep (se 1 (by rfl) ⟨1139966, by rfl⟩ : syracuseStep 1519955 = 2279933) B2279933
theorem B1520999 : Blo 674311 1520999 := bstep (se 1 (by rfl) ⟨1140749, by rfl⟩ : syracuseStep 1520999 = 2281499) B2281499
theorem B1522331 : Blo 674311 1522331 := bstep (se 1 (by rfl) ⟨1141748, by rfl⟩ : syracuseStep 1522331 = 2283497) B2283497
theorem B2735315 : Blo 674311 2735315 := bstep (se 1 (by rfl) ⟨2051486, by rfl⟩ : syracuseStep 2735315 = 4102973) B4102973
theorem B29212649 : Blo 674311 29212649 := bstep (se 2 (by rfl) ⟨10954743, by rfl⟩ : syracuseStep 29212649 = 21909487) B21909487
theorem B1524203 : Blo 674311 1524203 := bstep (se 1 (by rfl) ⟨1143152, by rfl⟩ : syracuseStep 1524203 = 2286305) B2286305
theorem B1524671 : Blo 674311 1524671 := bstep (se 1 (by rfl) ⟨1143503, by rfl⟩ : syracuseStep 1524671 = 2287007) B2287007
theorem B8668721 : Blo 674311 8668721 := bstep (se 2 (by rfl) ⟨3250770, by rfl⟩ : syracuseStep 8668721 = 6501541) B6501541
theorem B8767043 : Blo 674311 8767043 := bstep (se 1 (by rfl) ⟨6575282, by rfl⟩ : syracuseStep 8767043 = 13150565) B13150565
theorem B2345071 : Blo 674311 2345071 := bstep (se 1 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 2345071 = 3517607) B3517607
theorem B674687 : Blo 674311 674687 := bstep (se 1 (by rfl) ⟨506015, by rfl⟩ : syracuseStep 674687 = 1012031) B1012031
theorem B676799 : Blo 674311 676799 := bstep (se 1 (by rfl) ⟨507599, by rfl⟩ : syracuseStep 676799 = 1015199) B1015199
theorem B3856319 : Blo 674311 3856319 := bstep (se 1 (by rfl) ⟨2892239, by rfl⟩ : syracuseStep 3856319 = 5784479) B5784479
theorem B677951 : Blo 674311 677951 := bstep (se 1 (by rfl) ⟨508463, by rfl⟩ : syracuseStep 677951 = 1016927) B1016927
theorem B13000621 : Blo 674311 13000621 := bstep (se 3 (by rfl) ⟨2437616, by rfl⟩ : syracuseStep 13000621 = 4875233) B4875233
theorem B1926463 : Blo 674311 1926463 := bstep (se 1 (by rfl) ⟨1444847, by rfl⟩ : syracuseStep 1926463 = 2889695) B2889695
theorem B17294795 : Blo 674311 17294795 := bstep (se 1 (by rfl) ⟨12971096, by rfl⟩ : syracuseStep 17294795 = 25942193) B25942193
theorem B1140223 : Blo 674311 1140223 := bstep (se 1 (by rfl) ⟨855167, by rfl⟩ : syracuseStep 1140223 = 1710335) B1710335
theorem B1140905 : Blo 674311 1140905 := bstep (se 2 (by rfl) ⟨427839, by rfl⟩ : syracuseStep 1140905 = 855679) B855679
theorem B16476493 : Blo 674311 16476493 := bstep (se 3 (by rfl) ⟨3089342, by rfl⟩ : syracuseStep 16476493 = 6178685) B6178685
theorem B1011647 : Blo 674311 1011647 := bstep (se 1 (by rfl) ⟨758735, by rfl⟩ : syracuseStep 1011647 = 1517471) B1517471
theorem B1011881 : Blo 674311 1011881 := bstep (se 2 (by rfl) ⟨379455, by rfl⟩ : syracuseStep 1011881 = 758911) B758911
theorem B1143679 : Blo 674311 1143679 := bstep (se 1 (by rfl) ⟨857759, by rfl⟩ : syracuseStep 1143679 = 1715519) B1715519
theorem B1012679 : Blo 674311 1012679 := bstep (se 1 (by rfl) ⟨759509, by rfl⟩ : syracuseStep 1012679 = 1519019) B1519019
theorem B1012895 : Blo 674311 1012895 := bstep (se 1 (by rfl) ⟨759671, by rfl⟩ : syracuseStep 1012895 = 1519343) B1519343
theorem B13334003 : Blo 674311 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B1013663 : Blo 674311 1013663 := bstep (se 1 (by rfl) ⟨760247, by rfl⟩ : syracuseStep 1013663 = 1520495) B1520495
theorem B4945855 : Blo 674311 4945855 := bstep (se 1 (by rfl) ⟨3709391, by rfl⟩ : syracuseStep 4945855 = 7418783) B7418783
theorem B8681843 : Blo 674311 8681843 := bstep (se 1 (by rfl) ⟨6511382, by rfl⟩ : syracuseStep 8681843 = 13022765) B13022765
theorem B8649449 : Blo 674311 8649449 := bstep (se 2 (by rfl) ⟨3243543, by rfl⟩ : syracuseStep 8649449 = 6487087) B6487087
theorem B1015535 : Blo 674311 1015535 := bstep (se 1 (by rfl) ⟨761651, by rfl⟩ : syracuseStep 1015535 = 1523303) B1523303
theorem B5767361 : Blo 674311 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B1016135 : Blo 674311 1016135 := bstep (se 1 (by rfl) ⟨762101, by rfl⟩ : syracuseStep 1016135 = 1524203) B1524203
theorem B1016447 : Blo 674311 1016447 := bstep (se 1 (by rfl) ⟨762335, by rfl⟩ : syracuseStep 1016447 = 1524671) B1524671
theorem B1016489 : Blo 674311 1016489 := bstep (se 2 (by rfl) ⟨381183, by rfl⟩ : syracuseStep 1016489 = 762367) B762367
theorem B2884585 : Blo 674311 2884585 := bstep (se 2 (by rfl) ⟨1081719, by rfl⟩ : syracuseStep 2884585 = 2163439) B2163439
theorem B1016969 : Blo 674311 1016969 := bstep (se 2 (by rfl) ⟨381363, by rfl⟩ : syracuseStep 1016969 = 762727) B762727
theorem B33293693 : Blo 674311 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B1709545 : Blo 674311 1709545 := bstep (se 2 (by rfl) ⟨641079, by rfl⟩ : syracuseStep 1709545 = 1282159) B1282159
theorem B858271 : Blo 674311 858271 := bstep (se 1 (by rfl) ⟨643703, by rfl⟩ : syracuseStep 858271 = 1287407) B1287407
theorem B2889917 : Blo 674311 2889917 := bstep (se 3 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 2889917 = 1083719) B1083719
theorem B1710305 : Blo 674311 1710305 := bstep (se 2 (by rfl) ⟨641364, by rfl⟩ : syracuseStep 1710305 = 1282729) B1282729
theorem B858367 : Blo 674311 858367 := bstep (se 1 (by rfl) ⟨643775, by rfl⟩ : syracuseStep 858367 = 1287551) B1287551
theorem B760603 : Blo 674311 760603 := bstep (se 1 (by rfl) ⟨570452, by rfl⟩ : syracuseStep 760603 = 1140905) B1140905
theorem B6594473 : Blo 674311 6594473 := bstep (se 2 (by rfl) ⟨2472927, by rfl⟩ : syracuseStep 6594473 = 4945855) B4945855
theorem B2564243 : Blo 674311 2564243 := bstep (se 1 (by rfl) ⟨1923182, by rfl⟩ : syracuseStep 2564243 = 3846365) B3846365
theorem B8889335 : Blo 674311 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B2565533 : Blo 674311 2565533 := bstep (se 3 (by rfl) ⟨481037, by rfl⟩ : syracuseStep 2565533 = 962075) B962075
theorem B19475099 : Blo 674311 19475099 := bstep (se 1 (by rfl) ⟨14606324, by rfl⟩ : syracuseStep 19475099 = 29212649) B29212649
theorem B5779147 : Blo 674311 5779147 := bstep (se 1 (by rfl) ⟨4334360, by rfl⟩ : syracuseStep 5779147 = 8668721) B8668721
theorem B5844695 : Blo 674311 5844695 := bstep (se 1 (by rfl) ⟨4383521, by rfl⟩ : syracuseStep 5844695 = 8767043) B8767043
theorem B7319771 : Blo 674311 7319771 := bstep (se 1 (by rfl) ⟨5489828, by rfl⟩ : syracuseStep 7319771 = 10979657) B10979657
theorem B2568617 : Blo 674311 2568617 := bstep (se 2 (by rfl) ⟨963231, by rfl⟩ : syracuseStep 2568617 = 1926463) B1926463
theorem B1520297 : Blo 674311 1520297 := bstep (se 2 (by rfl) ⟨570111, by rfl⟩ : syracuseStep 1520297 = 1140223) B1140223
theorem B3126761 : Blo 674311 3126761 := bstep (se 2 (by rfl) ⟨1172535, by rfl⟩ : syracuseStep 3126761 = 2345071) B2345071
theorem B21968657 : Blo 674311 21968657 := bstep (se 2 (by rfl) ⟨8238246, by rfl⟩ : syracuseStep 21968657 = 16476493) B16476493
theorem B2570879 : Blo 674311 2570879 := bstep (se 1 (by rfl) ⟨1928159, by rfl⟩ : syracuseStep 2570879 = 3856319) B3856319
theorem B1623023 : Blo 674311 1623023 := bstep (se 1 (by rfl) ⟨1217267, by rfl⟩ : syracuseStep 1623023 = 2434535) B2434535
theorem B1524905 : Blo 674311 1524905 := bstep (se 2 (by rfl) ⟨571839, by rfl⟩ : syracuseStep 1524905 = 1143679) B1143679
theorem B2738299 : Blo 674311 2738299 := bstep (se 1 (by rfl) ⟨2053724, by rfl⟩ : syracuseStep 2738299 = 4107449) B4107449
theorem B674431 : Blo 674311 674431 := bstep (se 1 (by rfl) ⟨505823, by rfl⟩ : syracuseStep 674431 = 1011647) B1011647
theorem B674587 : Blo 674311 674587 := bstep (se 1 (by rfl) ⟨505940, by rfl⟩ : syracuseStep 674587 = 1011881) B1011881
theorem B675119 : Blo 674311 675119 := bstep (se 1 (by rfl) ⟨506339, by rfl⟩ : syracuseStep 675119 = 1012679) B1012679
theorem B675263 : Blo 674311 675263 := bstep (se 1 (by rfl) ⟨506447, by rfl⟩ : syracuseStep 675263 = 1012895) B1012895
theorem B675775 : Blo 674311 675775 := bstep (se 1 (by rfl) ⟨506831, by rfl⟩ : syracuseStep 675775 = 1013663) B1013663
theorem B5787895 : Blo 674311 5787895 := bstep (se 1 (by rfl) ⟨4340921, by rfl⟩ : syracuseStep 5787895 = 8681843) B8681843
theorem B1823543 : Blo 674311 1823543 := bstep (se 1 (by rfl) ⟨1367657, by rfl⟩ : syracuseStep 1823543 = 2735315) B2735315
theorem B677023 : Blo 674311 677023 := bstep (se 1 (by rfl) ⟨507767, by rfl⟩ : syracuseStep 677023 = 1015535) B1015535
theorem B678127 : Blo 674311 678127 := bstep (se 1 (by rfl) ⟨508595, by rfl⟩ : syracuseStep 678127 = 1017191) B1017191
theorem B5792543 : Blo 674311 5792543 := bstep (se 1 (by rfl) ⟨4344407, by rfl⟩ : syracuseStep 5792543 = 8688815) B8688815
theorem B11529863 : Blo 674311 11529863 := bstep (se 1 (by rfl) ⟨8647397, by rfl⟩ : syracuseStep 11529863 = 17294795) B17294795
theorem B1013303 : Blo 674311 1013303 := bstep (se 1 (by rfl) ⟨759977, by rfl⟩ : syracuseStep 1013303 = 1519955) B1519955
theorem B1013999 : Blo 674311 1013999 := bstep (se 1 (by rfl) ⟨760499, by rfl⟩ : syracuseStep 1013999 = 1520999) B1520999
theorem B1014887 : Blo 674311 1014887 := bstep (se 1 (by rfl) ⟨761165, by rfl⟩ : syracuseStep 1014887 = 1522331) B1522331
theorem B5766299 : Blo 674311 5766299 := bstep (se 1 (by rfl) ⟨4324724, by rfl⟩ : syracuseStep 5766299 = 8649449) B8649449
theorem B1015337 : Blo 674311 1015337 := bstep (se 2 (by rfl) ⟨380751, by rfl⟩ : syracuseStep 1015337 = 761503) B761503
theorem B17334161 : Blo 674311 17334161 := bstep (se 2 (by rfl) ⟨6500310, by rfl⟩ : syracuseStep 17334161 = 13000621) B13000621
theorem B1082015 : Blo 674311 1082015 := bstep (se 1 (by rfl) ⟨811511, by rfl⟩ : syracuseStep 1082015 = 1623023) B1623023
theorem B1016603 : Blo 674311 1016603 := bstep (se 1 (by rfl) ⟨762452, by rfl⟩ : syracuseStep 1016603 = 1524905) B1524905
theorem B1215695 : Blo 674311 1215695 := bstep (se 1 (by rfl) ⟨911771, by rfl⟩ : syracuseStep 1215695 = 1823543) B1823543
theorem B7705529 : Blo 674311 7705529 := bstep (se 2 (by rfl) ⟨2889573, by rfl⟩ : syracuseStep 7705529 = 5779147) B5779147
theorem B4396315 : Blo 674311 4396315 := bstep (se 1 (by rfl) ⟨3297236, by rfl⟩ : syracuseStep 4396315 = 6594473) B6594473
theorem B1709495 : Blo 674311 1709495 := bstep (se 1 (by rfl) ⟨1282121, by rfl⟩ : syracuseStep 1709495 = 2564243) B2564243
theorem B1710355 : Blo 674311 1710355 := bstep (se 1 (by rfl) ⟨1282766, by rfl⟩ : syracuseStep 1710355 = 2565533) B2565533
theorem B12983399 : Blo 674311 12983399 := bstep (se 1 (by rfl) ⟨9737549, by rfl⟩ : syracuseStep 12983399 = 19475099) B19475099
theorem B1712411 : Blo 674311 1712411 := bstep (se 1 (by rfl) ⟨1284308, by rfl⟩ : syracuseStep 1712411 = 2568617) B2568617
theorem B1713919 : Blo 674311 1713919 := bstep (se 1 (by rfl) ⟨1285439, by rfl⟩ : syracuseStep 1713919 = 2570879) B2570879
theorem B3844199 : Blo 674311 3844199 := bstep (se 1 (by rfl) ⟨2883149, by rfl⟩ : syracuseStep 3844199 = 5766299) B5766299
theorem B3844907 : Blo 674311 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B22195795 : Blo 674311 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B3846113 : Blo 674311 3846113 := bstep (se 2 (by rfl) ⟨1442292, by rfl⟩ : syracuseStep 3846113 = 2884585) B2884585
theorem B3651065 : Blo 674311 3651065 := bstep (se 2 (by rfl) ⟨1369149, by rfl⟩ : syracuseStep 3651065 = 2738299) B2738299
theorem B7717193 : Blo 674311 7717193 := bstep (se 2 (by rfl) ⟨2893947, by rfl⟩ : syracuseStep 7717193 = 5787895) B5787895
theorem B2279393 : Blo 674311 2279393 := bstep (se 2 (by rfl) ⟨854772, by rfl⟩ : syracuseStep 2279393 = 1709545) B1709545
theorem B7686575 : Blo 674311 7686575 := bstep (se 1 (by rfl) ⟨5764931, by rfl⟩ : syracuseStep 7686575 = 11529863) B11529863
theorem B2084507 : Blo 674311 2084507 := bstep (se 1 (by rfl) ⟨1563380, by rfl⟩ : syracuseStep 2084507 = 3126761) B3126761
theorem B675535 : Blo 674311 675535 := bstep (se 1 (by rfl) ⟨506651, by rfl⟩ : syracuseStep 675535 = 1013303) B1013303
theorem B675999 : Blo 674311 675999 := bstep (se 1 (by rfl) ⟨506999, by rfl⟩ : syracuseStep 675999 = 1013999) B1013999
theorem B15585853 : Blo 674311 15585853 := bstep (se 3 (by rfl) ⟨2922347, by rfl⟩ : syracuseStep 15585853 = 5844695) B5844695
theorem B676591 : Blo 674311 676591 := bstep (se 1 (by rfl) ⟨507443, by rfl⟩ : syracuseStep 676591 = 1014887) B1014887
theorem B676891 : Blo 674311 676891 := bstep (se 1 (by rfl) ⟨507668, by rfl⟩ : syracuseStep 676891 = 1015337) B1015337
theorem B11556107 : Blo 674311 11556107 := bstep (se 1 (by rfl) ⟨8667080, by rfl⟩ : syracuseStep 11556107 = 17334161) B17334161
theorem B677423 : Blo 674311 677423 := bstep (se 1 (by rfl) ⟨508067, by rfl⟩ : syracuseStep 677423 = 1016135) B1016135
theorem B677631 : Blo 674311 677631 := bstep (se 1 (by rfl) ⟨508223, by rfl⟩ : syracuseStep 677631 = 1016447) B1016447
theorem B677659 : Blo 674311 677659 := bstep (se 1 (by rfl) ⟨508244, by rfl⟩ : syracuseStep 677659 = 1016489) B1016489
theorem B677979 : Blo 674311 677979 := bstep (se 1 (by rfl) ⟨508484, by rfl⟩ : syracuseStep 677979 = 1016969) B1016969
theorem B1926611 : Blo 674311 1926611 := bstep (se 1 (by rfl) ⟨1444958, by rfl⟩ : syracuseStep 1926611 = 2889917) B2889917
theorem B1140203 : Blo 674311 1140203 := bstep (se 1 (by rfl) ⟨855152, by rfl⟩ : syracuseStep 1140203 = 1710305) B1710305
theorem B3861695 : Blo 674311 3861695 := bstep (se 1 (by rfl) ⟨2896271, by rfl⟩ : syracuseStep 3861695 = 5792543) B5792543
theorem B5926223 : Blo 674311 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B4879847 : Blo 674311 4879847 := bstep (se 1 (by rfl) ⟨3659885, by rfl⟩ : syracuseStep 4879847 = 7319771) B7319771
theorem B1144361 : Blo 674311 1144361 := bstep (se 2 (by rfl) ⟨429135, by rfl⟩ : syracuseStep 1144361 = 858271) B858271
theorem B1144489 : Blo 674311 1144489 := bstep (se 2 (by rfl) ⟨429183, by rfl⟩ : syracuseStep 1144489 = 858367) B858367
theorem B1013531 : Blo 674311 1013531 := bstep (se 1 (by rfl) ⟨760148, by rfl⟩ : syracuseStep 1013531 = 1520297) B1520297
theorem B1014137 : Blo 674311 1014137 := bstep (se 2 (by rfl) ⟨380301, by rfl⟩ : syracuseStep 1014137 = 760603) B760603
theorem B14645771 : Blo 674311 14645771 := bstep (se 1 (by rfl) ⟨10984328, by rfl⟩ : syracuseStep 14645771 = 21968657) B21968657
theorem B5144795 : Blo 674311 5144795 := bstep (se 1 (by rfl) ⟨3858596, by rfl⟩ : syracuseStep 5144795 = 7717193) B7717193
theorem B721343 : Blo 674311 721343 := bstep (se 1 (by rfl) ⟨541007, by rfl⟩ : syracuseStep 721343 = 1082015) B1082015
theorem B7704071 : Blo 674311 7704071 := bstep (se 1 (by rfl) ⟨5778053, by rfl⟩ : syracuseStep 7704071 = 11556107) B11556107
theorem B8655599 : Blo 674311 8655599 := bstep (se 1 (by rfl) ⟨6491699, by rfl⟩ : syracuseStep 8655599 = 12983399) B12983399
theorem B29594393 : Blo 674311 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B20781137 : Blo 674311 20781137 := bstep (se 2 (by rfl) ⟨7792926, by rfl⟩ : syracuseStep 20781137 = 15585853) B15585853
theorem B1284407 : Blo 674311 1284407 := bstep (se 1 (by rfl) ⟨963305, by rfl⟩ : syracuseStep 1284407 = 1926611) B1926611
theorem B760135 : Blo 674311 760135 := bstep (se 1 (by rfl) ⟨570101, by rfl⟩ : syracuseStep 760135 = 1140203) B1140203
theorem B2562799 : Blo 674311 2562799 := bstep (se 1 (by rfl) ⟨1922099, by rfl⟩ : syracuseStep 2562799 = 3844199) B3844199
theorem B2563271 : Blo 674311 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B2564075 : Blo 674311 2564075 := bstep (se 1 (by rfl) ⟨1923056, by rfl⟩ : syracuseStep 2564075 = 3846113) B3846113
theorem B3253231 : Blo 674311 3253231 := bstep (se 1 (by rfl) ⟨2439923, by rfl⟩ : syracuseStep 3253231 = 4879847) B4879847
theorem B2434043 : Blo 674311 2434043 := bstep (se 1 (by rfl) ⟨1825532, by rfl⟩ : syracuseStep 2434043 = 3651065) B3651065
theorem B762907 : Blo 674311 762907 := bstep (se 1 (by rfl) ⟨572180, by rfl⟩ : syracuseStep 762907 = 1144361) B1144361
theorem B1519595 : Blo 674311 1519595 := bstep (se 1 (by rfl) ⟨1139696, by rfl⟩ : syracuseStep 1519595 = 2279393) B2279393
theorem B5124383 : Blo 674311 5124383 := bstep (se 1 (by rfl) ⟨3843287, by rfl⟩ : syracuseStep 5124383 = 7686575) B7686575
theorem B1389671 : Blo 674311 1389671 := bstep (se 1 (by rfl) ⟨1042253, by rfl⟩ : syracuseStep 1389671 = 2084507) B2084507
theorem B2574463 : Blo 674311 2574463 := bstep (se 1 (by rfl) ⟨1930847, by rfl⟩ : syracuseStep 2574463 = 3861695) B3861695
theorem B3950815 : Blo 674311 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B1525985 : Blo 674311 1525985 := bstep (se 2 (by rfl) ⟨572244, by rfl⟩ : syracuseStep 1525985 = 1144489) B1144489
theorem B2280473 : Blo 674311 2280473 := bstep (se 2 (by rfl) ⟨855177, by rfl⟩ : syracuseStep 2280473 = 1710355) B1710355
theorem B675687 : Blo 674311 675687 := bstep (se 1 (by rfl) ⟨506765, by rfl⟩ : syracuseStep 675687 = 1013531) B1013531
theorem B676091 : Blo 674311 676091 := bstep (se 1 (by rfl) ⟨507068, by rfl⟩ : syracuseStep 676091 = 1014137) B1014137
theorem B677735 : Blo 674311 677735 := bstep (se 1 (by rfl) ⟨508301, by rfl⟩ : syracuseStep 677735 = 1016603) B1016603
theorem B2285225 : Blo 674311 2285225 := bstep (se 2 (by rfl) ⟨856959, by rfl⟩ : syracuseStep 2285225 = 1713919) B1713919
theorem B5137019 : Blo 674311 5137019 := bstep (se 1 (by rfl) ⟨3852764, by rfl⟩ : syracuseStep 5137019 = 7705529) B7705529
theorem B1139663 : Blo 674311 1139663 := bstep (se 1 (by rfl) ⟨854747, by rfl⟩ : syracuseStep 1139663 = 1709495) B1709495
theorem B1141607 : Blo 674311 1141607 := bstep (se 1 (by rfl) ⟨856205, by rfl⟩ : syracuseStep 1141607 = 1712411) B1712411
theorem B5861753 : Blo 674311 5861753 := bstep (se 2 (by rfl) ⟨2198157, by rfl⟩ : syracuseStep 5861753 = 4396315) B4396315
theorem B3241853 : Blo 674311 3241853 := bstep (se 3 (by rfl) ⟨607847, by rfl⟩ : syracuseStep 3241853 = 1215695) B1215695
theorem B9763847 : Blo 674311 9763847 := bstep (se 1 (by rfl) ⟨7322885, by rfl⟩ : syracuseStep 9763847 = 14645771) B14645771
theorem B1017209 : Blo 674311 1017209 := bstep (se 2 (by rfl) ⟨381453, by rfl⟩ : syracuseStep 1017209 = 762907) B762907
theorem B1017323 : Blo 674311 1017323 := bstep (se 1 (by rfl) ⟨762992, by rfl⟩ : syracuseStep 1017323 = 1525985) B1525985
theorem B5770399 : Blo 674311 5770399 := bstep (se 1 (by rfl) ⟨4327799, by rfl⟩ : syracuseStep 5770399 = 8655599) B8655599
theorem B19729595 : Blo 674311 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B856271 : Blo 674311 856271 := bstep (se 1 (by rfl) ⟨642203, by rfl⟩ : syracuseStep 856271 = 1284407) B1284407
theorem B1708847 : Blo 674311 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B1709383 : Blo 674311 1709383 := bstep (se 1 (by rfl) ⟨1282037, by rfl⟩ : syracuseStep 1709383 = 2564075) B2564075
theorem B759775 : Blo 674311 759775 := bstep (se 1 (by rfl) ⟨569831, by rfl⟩ : syracuseStep 759775 = 1139663) B1139663
theorem B761071 : Blo 674311 761071 := bstep (se 1 (by rfl) ⟨570803, by rfl⟩ : syracuseStep 761071 = 1141607) B1141607
theorem B3416255 : Blo 674311 3416255 := bstep (se 1 (by rfl) ⟨2562191, by rfl⟩ : syracuseStep 3416255 = 5124383) B5124383
theorem B3907835 : Blo 674311 3907835 := bstep (se 1 (by rfl) ⟨2930876, by rfl⟩ : syracuseStep 3907835 = 5861753) B5861753
theorem B926447 : Blo 674311 926447 := bstep (se 1 (by rfl) ⟨694835, by rfl⟩ : syracuseStep 926447 = 1389671) B1389671
theorem B3417065 : Blo 674311 3417065 := bstep (se 2 (by rfl) ⟨1281399, by rfl⟩ : syracuseStep 3417065 = 2562799) B2562799
theorem B4337641 : Blo 674311 4337641 := bstep (se 2 (by rfl) ⟨1626615, by rfl⟩ : syracuseStep 4337641 = 3253231) B3253231
theorem B1520315 : Blo 674311 1520315 := bstep (se 1 (by rfl) ⟨1140236, by rfl⟩ : syracuseStep 1520315 = 2280473) B2280473
theorem B1523483 : Blo 674311 1523483 := bstep (se 1 (by rfl) ⟨1142612, by rfl⟩ : syracuseStep 1523483 = 2285225) B2285225
theorem B3424679 : Blo 674311 3424679 := bstep (se 1 (by rfl) ⟨2568509, by rfl⟩ : syracuseStep 3424679 = 5137019) B5137019
theorem B1622695 : Blo 674311 1622695 := bstep (se 1 (by rfl) ⟨1217021, by rfl⟩ : syracuseStep 1622695 = 2434043) B2434043
theorem B6509231 : Blo 674311 6509231 := bstep (se 1 (by rfl) ⟨4881923, by rfl⟩ : syracuseStep 6509231 = 9763847) B9763847
theorem B3429863 : Blo 674311 3429863 := bstep (se 1 (by rfl) ⟨2572397, by rfl⟩ : syracuseStep 3429863 = 5144795) B5144795
theorem B1923581 : Blo 674311 1923581 := bstep (se 3 (by rfl) ⟨360671, by rfl⟩ : syracuseStep 1923581 = 721343) B721343
theorem B5136047 : Blo 674311 5136047 := bstep (se 1 (by rfl) ⟨3852035, by rfl⟩ : syracuseStep 5136047 = 7704071) B7704071
theorem B3432617 : Blo 674311 3432617 := bstep (se 2 (by rfl) ⟨1287231, by rfl⟩ : syracuseStep 3432617 = 2574463) B2574463
theorem B5267753 : Blo 674311 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B13854091 : Blo 674311 13854091 := bstep (se 1 (by rfl) ⟨10390568, by rfl⟩ : syracuseStep 13854091 = 20781137) B20781137
theorem B1013063 : Blo 674311 1013063 := bstep (se 1 (by rfl) ⟨759797, by rfl⟩ : syracuseStep 1013063 = 1519595) B1519595
theorem B1013513 : Blo 674311 1013513 := bstep (se 2 (by rfl) ⟨380067, by rfl⟩ : syracuseStep 1013513 = 760135) B760135
theorem B2161235 : Blo 674311 2161235 := bstep (se 1 (by rfl) ⟨1620926, by rfl⟩ : syracuseStep 2161235 = 3241853) B3241853
theorem B2163593 : Blo 674311 2163593 := bstep (se 2 (by rfl) ⟨811347, by rfl⟩ : syracuseStep 2163593 = 1622695) B1622695
theorem B1282387 : Blo 674311 1282387 := bstep (se 1 (by rfl) ⟨961790, by rfl⟩ : syracuseStep 1282387 = 1923581) B1923581
theorem B3511835 : Blo 674311 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B13153063 : Blo 674311 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B4339487 : Blo 674311 4339487 := bstep (se 1 (by rfl) ⟨3254615, by rfl⟩ : syracuseStep 4339487 = 6509231) B6509231
theorem B3424031 : Blo 674311 3424031 := bstep (se 1 (by rfl) ⟨2568023, by rfl⟩ : syracuseStep 3424031 = 5136047) B5136047
theorem B5783521 : Blo 674311 5783521 := bstep (se 2 (by rfl) ⟨2168820, by rfl⟩ : syracuseStep 5783521 = 4337641) B4337641
theorem B2277503 : Blo 674311 2277503 := bstep (se 1 (by rfl) ⟨1708127, by rfl⟩ : syracuseStep 2277503 = 3416255) B3416255
theorem B2605223 : Blo 674311 2605223 := bstep (se 1 (by rfl) ⟨1953917, by rfl⟩ : syracuseStep 2605223 = 3907835) B3907835
theorem B2278043 : Blo 674311 2278043 := bstep (se 1 (by rfl) ⟨1708532, by rfl⟩ : syracuseStep 2278043 = 3417065) B3417065
theorem B2279177 : Blo 674311 2279177 := bstep (se 2 (by rfl) ⟨854691, by rfl⟩ : syracuseStep 2279177 = 1709383) B1709383
theorem B9882101 : Blo 674311 9882101 := bstep (se 5 (by rfl) ⟨463223, by rfl⟩ : syracuseStep 9882101 = 926447) B926447
theorem B675375 : Blo 674311 675375 := bstep (se 1 (by rfl) ⟨506531, by rfl⟩ : syracuseStep 675375 = 1013063) B1013063
theorem B675675 : Blo 674311 675675 := bstep (se 1 (by rfl) ⟨506756, by rfl⟩ : syracuseStep 675675 = 1013513) B1013513
theorem B2283119 : Blo 674311 2283119 := bstep (se 1 (by rfl) ⟨1712339, by rfl⟩ : syracuseStep 2283119 = 3424679) B3424679
theorem B2283389 : Blo 674311 2283389 := bstep (se 3 (by rfl) ⟨428135, by rfl⟩ : syracuseStep 2283389 = 856271) B856271
theorem B678139 : Blo 674311 678139 := bstep (se 1 (by rfl) ⟨508604, by rfl⟩ : syracuseStep 678139 = 1017209) B1017209
theorem B678215 : Blo 674311 678215 := bstep (se 1 (by rfl) ⟨508661, by rfl⟩ : syracuseStep 678215 = 1017323) B1017323
theorem B18472121 : Blo 674311 18472121 := bstep (se 2 (by rfl) ⟨6927045, by rfl⟩ : syracuseStep 18472121 = 13854091) B13854091
theorem B1139231 : Blo 674311 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B2286575 : Blo 674311 2286575 := bstep (se 1 (by rfl) ⟨1714931, by rfl⟩ : syracuseStep 2286575 = 3429863) B3429863
theorem B7693865 : Blo 674311 7693865 := bstep (se 2 (by rfl) ⟨2885199, by rfl⟩ : syracuseStep 7693865 = 5770399) B5770399
theorem B2288411 : Blo 674311 2288411 := bstep (se 1 (by rfl) ⟨1716308, by rfl⟩ : syracuseStep 2288411 = 3432617) B3432617
theorem B1013033 : Blo 674311 1013033 := bstep (se 2 (by rfl) ⟨379887, by rfl⟩ : syracuseStep 1013033 = 759775) B759775
theorem B1013543 : Blo 674311 1013543 := bstep (se 1 (by rfl) ⟨760157, by rfl⟩ : syracuseStep 1013543 = 1520315) B1520315
theorem B1014761 : Blo 674311 1014761 := bstep (se 2 (by rfl) ⟨380535, by rfl⟩ : syracuseStep 1014761 = 761071) B761071
theorem B1440823 : Blo 674311 1440823 := bstep (se 1 (by rfl) ⟨1080617, by rfl⟩ : syracuseStep 1440823 = 2161235) B2161235
theorem B1015655 : Blo 674311 1015655 := bstep (se 1 (by rfl) ⟨761741, by rfl⟩ : syracuseStep 1015655 = 1523483) B1523483
theorem B1736815 : Blo 674311 1736815 := bstep (se 1 (by rfl) ⟨1302611, by rfl⟩ : syracuseStep 1736815 = 2605223) B2605223
theorem B1442395 : Blo 674311 1442395 := bstep (se 1 (by rfl) ⟨1081796, by rfl⟩ : syracuseStep 1442395 = 2163593) B2163593
theorem B6588067 : Blo 674311 6588067 := bstep (se 1 (by rfl) ⟨4941050, by rfl⟩ : syracuseStep 6588067 = 9882101) B9882101
theorem B759487 : Blo 674311 759487 := bstep (se 1 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 759487 = 1139231) B1139231
theorem B1709849 : Blo 674311 1709849 := bstep (se 2 (by rfl) ⟨641193, by rfl⟩ : syracuseStep 1709849 = 1282387) B1282387
theorem B17537417 : Blo 674311 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B2892991 : Blo 674311 2892991 := bstep (se 1 (by rfl) ⟨2169743, by rfl⟩ : syracuseStep 2892991 = 4339487) B4339487
theorem B7711361 : Blo 674311 7711361 := bstep (se 2 (by rfl) ⟨2891760, by rfl⟩ : syracuseStep 7711361 = 5783521) B5783521
theorem B1518335 : Blo 674311 1518335 := bstep (se 1 (by rfl) ⟨1138751, by rfl⟩ : syracuseStep 1518335 = 2277503) B2277503
theorem B1518695 : Blo 674311 1518695 := bstep (se 1 (by rfl) ⟨1139021, by rfl⟩ : syracuseStep 1518695 = 2278043) B2278043
theorem B1519451 : Blo 674311 1519451 := bstep (se 1 (by rfl) ⟨1139588, by rfl⟩ : syracuseStep 1519451 = 2279177) B2279177
theorem B2341223 : Blo 674311 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B1522079 : Blo 674311 1522079 := bstep (se 1 (by rfl) ⟨1141559, by rfl⟩ : syracuseStep 1522079 = 2283119) B2283119
theorem B1522259 : Blo 674311 1522259 := bstep (se 1 (by rfl) ⟨1141694, by rfl⟩ : syracuseStep 1522259 = 2283389) B2283389
theorem B1524383 : Blo 674311 1524383 := bstep (se 1 (by rfl) ⟨1143287, by rfl⟩ : syracuseStep 1524383 = 2286575) B2286575
theorem B5129243 : Blo 674311 5129243 := bstep (se 1 (by rfl) ⟨3846932, by rfl⟩ : syracuseStep 5129243 = 7693865) B7693865
theorem B1525607 : Blo 674311 1525607 := bstep (se 1 (by rfl) ⟨1144205, by rfl⟩ : syracuseStep 1525607 = 2288411) B2288411
theorem B675355 : Blo 674311 675355 := bstep (se 1 (by rfl) ⟨506516, by rfl⟩ : syracuseStep 675355 = 1013033) B1013033
theorem B675695 : Blo 674311 675695 := bstep (se 1 (by rfl) ⟨506771, by rfl⟩ : syracuseStep 675695 = 1013543) B1013543
theorem B1921097 : Blo 674311 1921097 := bstep (se 2 (by rfl) ⟨720411, by rfl⟩ : syracuseStep 1921097 = 1440823) B1440823
theorem B676507 : Blo 674311 676507 := bstep (se 1 (by rfl) ⟨507380, by rfl⟩ : syracuseStep 676507 = 1014761) B1014761
theorem B2282687 : Blo 674311 2282687 := bstep (se 1 (by rfl) ⟨1712015, by rfl⟩ : syracuseStep 2282687 = 3424031) B3424031
theorem B677103 : Blo 674311 677103 := bstep (se 1 (by rfl) ⟨507827, by rfl⟩ : syracuseStep 677103 = 1015655) B1015655
theorem B12314747 : Blo 674311 12314747 := bstep (se 1 (by rfl) ⟨9236060, by rfl⟩ : syracuseStep 12314747 = 18472121) B18472121
theorem B1016255 : Blo 674311 1016255 := bstep (se 1 (by rfl) ⟨762191, by rfl⟩ : syracuseStep 1016255 = 1524383) B1524383
theorem B1017071 : Blo 674311 1017071 := bstep (se 1 (by rfl) ⟨762803, by rfl⟩ : syracuseStep 1017071 = 1525607) B1525607
theorem B8784089 : Blo 674311 8784089 := bstep (se 2 (by rfl) ⟨3294033, by rfl⟩ : syracuseStep 8784089 = 6588067) B6588067
theorem B5122925 : Blo 674311 5122925 := bstep (se 3 (by rfl) ⟨960548, by rfl⟩ : syracuseStep 5122925 = 1921097) B1921097
theorem B3419495 : Blo 674311 3419495 := bstep (se 1 (by rfl) ⟨2564621, by rfl⟩ : syracuseStep 3419495 = 5129243) B5129243
theorem B1521791 : Blo 674311 1521791 := bstep (se 1 (by rfl) ⟨1141343, by rfl⟩ : syracuseStep 1521791 = 2282687) B2282687
theorem B8209831 : Blo 674311 8209831 := bstep (se 1 (by rfl) ⟨6157373, by rfl⟩ : syracuseStep 8209831 = 12314747) B12314747
theorem B1560815 : Blo 674311 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B2315753 : Blo 674311 2315753 := bstep (se 2 (by rfl) ⟨868407, by rfl⟩ : syracuseStep 2315753 = 1736815) B1736815
theorem B1923193 : Blo 674311 1923193 := bstep (se 2 (by rfl) ⟨721197, by rfl⟩ : syracuseStep 1923193 = 1442395) B1442395
theorem B3857321 : Blo 674311 3857321 := bstep (se 2 (by rfl) ⟨1446495, by rfl⟩ : syracuseStep 3857321 = 2892991) B2892991
theorem B1139899 : Blo 674311 1139899 := bstep (se 1 (by rfl) ⟨854924, by rfl⟩ : syracuseStep 1139899 = 1709849) B1709849
theorem B11691611 : Blo 674311 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B5140907 : Blo 674311 5140907 := bstep (se 1 (by rfl) ⟨3855680, by rfl⟩ : syracuseStep 5140907 = 7711361) B7711361
theorem B1012223 : Blo 674311 1012223 := bstep (se 1 (by rfl) ⟨759167, by rfl⟩ : syracuseStep 1012223 = 1518335) B1518335
theorem B1012463 : Blo 674311 1012463 := bstep (se 1 (by rfl) ⟨759347, by rfl⟩ : syracuseStep 1012463 = 1518695) B1518695
theorem B1012649 : Blo 674311 1012649 := bstep (se 2 (by rfl) ⟨379743, by rfl⟩ : syracuseStep 1012649 = 759487) B759487
theorem B1012967 : Blo 674311 1012967 := bstep (se 1 (by rfl) ⟨759725, by rfl⟩ : syracuseStep 1012967 = 1519451) B1519451
theorem B1014719 : Blo 674311 1014719 := bstep (se 1 (by rfl) ⟨761039, by rfl⟩ : syracuseStep 1014719 = 1522079) B1522079
theorem B1014839 : Blo 674311 1014839 := bstep (se 1 (by rfl) ⟨761129, by rfl⟩ : syracuseStep 1014839 = 1522259) B1522259
theorem B10946441 : Blo 674311 10946441 := bstep (se 2 (by rfl) ⟨4104915, by rfl⟩ : syracuseStep 10946441 = 8209831) B8209831
theorem B1543835 : Blo 674311 1543835 := bstep (se 1 (by rfl) ⟨1157876, by rfl⟩ : syracuseStep 1543835 = 2315753) B2315753
theorem B3415283 : Blo 674311 3415283 := bstep (se 1 (by rfl) ⟨2561462, by rfl⟩ : syracuseStep 3415283 = 5122925) B5122925
theorem B2564257 : Blo 674311 2564257 := bstep (se 2 (by rfl) ⟨961596, by rfl⟩ : syracuseStep 2564257 = 1923193) B1923193
theorem B1519865 : Blo 674311 1519865 := bstep (se 2 (by rfl) ⟨569949, by rfl⟩ : syracuseStep 1519865 = 1139899) B1139899
theorem B2571547 : Blo 674311 2571547 := bstep (se 1 (by rfl) ⟨1928660, by rfl⟩ : syracuseStep 2571547 = 3857321) B3857321
theorem B2279663 : Blo 674311 2279663 := bstep (se 1 (by rfl) ⟨1709747, by rfl⟩ : syracuseStep 2279663 = 3419495) B3419495
theorem B3427271 : Blo 674311 3427271 := bstep (se 1 (by rfl) ⟨2570453, by rfl⟩ : syracuseStep 3427271 = 5140907) B5140907
theorem B674815 : Blo 674311 674815 := bstep (se 1 (by rfl) ⟨506111, by rfl⟩ : syracuseStep 674815 = 1012223) B1012223
theorem B674975 : Blo 674311 674975 := bstep (se 1 (by rfl) ⟨506231, by rfl⟩ : syracuseStep 674975 = 1012463) B1012463
theorem B675099 : Blo 674311 675099 := bstep (se 1 (by rfl) ⟨506324, by rfl⟩ : syracuseStep 675099 = 1012649) B1012649
theorem B675311 : Blo 674311 675311 := bstep (se 1 (by rfl) ⟨506483, by rfl⟩ : syracuseStep 675311 = 1012967) B1012967
theorem B676479 : Blo 674311 676479 := bstep (se 1 (by rfl) ⟨507359, by rfl⟩ : syracuseStep 676479 = 1014719) B1014719
theorem B676559 : Blo 674311 676559 := bstep (se 1 (by rfl) ⟨507419, by rfl⟩ : syracuseStep 676559 = 1014839) B1014839
theorem B677503 : Blo 674311 677503 := bstep (se 1 (by rfl) ⟨508127, by rfl⟩ : syracuseStep 677503 = 1016255) B1016255
theorem B678047 : Blo 674311 678047 := bstep (se 1 (by rfl) ⟨508535, by rfl⟩ : syracuseStep 678047 = 1017071) B1017071
theorem B5856059 : Blo 674311 5856059 := bstep (se 1 (by rfl) ⟨4392044, by rfl⟩ : syracuseStep 5856059 = 8784089) B8784089
theorem B1040543 : Blo 674311 1040543 := bstep (se 1 (by rfl) ⟨780407, by rfl⟩ : syracuseStep 1040543 = 1560815) B1560815
theorem B7794407 : Blo 674311 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B1014527 : Blo 674311 1014527 := bstep (se 1 (by rfl) ⟨760895, by rfl⟩ : syracuseStep 1014527 = 1521791) B1521791
theorem B3904039 : Blo 674311 3904039 := bstep (se 1 (by rfl) ⟨2928029, by rfl⟩ : syracuseStep 3904039 = 5856059) B5856059
theorem B693695 : Blo 674311 693695 := bstep (se 1 (by rfl) ⟨520271, by rfl⟩ : syracuseStep 693695 = 1040543) B1040543
theorem B3419009 : Blo 674311 3419009 := bstep (se 2 (by rfl) ⟨1282128, by rfl⟩ : syracuseStep 3419009 = 2564257) B2564257
theorem B1519775 : Blo 674311 1519775 := bstep (se 1 (by rfl) ⟨1139831, by rfl⟩ : syracuseStep 1519775 = 2279663) B2279663
theorem B1029223 : Blo 674311 1029223 := bstep (se 1 (by rfl) ⟨771917, by rfl⟩ : syracuseStep 1029223 = 1543835) B1543835
theorem B2276855 : Blo 674311 2276855 := bstep (se 1 (by rfl) ⟨1707641, by rfl⟩ : syracuseStep 2276855 = 3415283) B3415283
theorem B5196271 : Blo 674311 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B3428729 : Blo 674311 3428729 := bstep (se 2 (by rfl) ⟨1285773, by rfl⟩ : syracuseStep 3428729 = 2571547) B2571547
theorem B676351 : Blo 674311 676351 := bstep (se 1 (by rfl) ⟨507263, by rfl⟩ : syracuseStep 676351 = 1014527) B1014527
theorem B7297627 : Blo 674311 7297627 := bstep (se 1 (by rfl) ⟨5473220, by rfl⟩ : syracuseStep 7297627 = 10946441) B10946441
theorem B2284847 : Blo 674311 2284847 := bstep (se 1 (by rfl) ⟨1713635, by rfl⟩ : syracuseStep 2284847 = 3427271) B3427271
theorem B1013243 : Blo 674311 1013243 := bstep (se 1 (by rfl) ⟨759932, by rfl⟩ : syracuseStep 1013243 = 1519865) B1519865
theorem B1517903 : Blo 674311 1517903 := bstep (se 1 (by rfl) ⟨1138427, by rfl⟩ : syracuseStep 1517903 = 2276855) B2276855
theorem B6928361 : Blo 674311 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B1849853 : Blo 674311 1849853 := bstep (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) B693695
theorem B1523231 : Blo 674311 1523231 := bstep (se 1 (by rfl) ⟨1142423, by rfl⟩ : syracuseStep 1523231 = 2284847) B2284847
theorem B2279339 : Blo 674311 2279339 := bstep (se 1 (by rfl) ⟨1709504, by rfl⟩ : syracuseStep 2279339 = 3419009) B3419009
theorem B675495 : Blo 674311 675495 := bstep (se 1 (by rfl) ⟨506621, by rfl⟩ : syracuseStep 675495 = 1013243) B1013243
theorem B2285819 : Blo 674311 2285819 := bstep (se 1 (by rfl) ⟨1714364, by rfl⟩ : syracuseStep 2285819 = 3428729) B3428729
theorem B5205385 : Blo 674311 5205385 := bstep (se 2 (by rfl) ⟨1952019, by rfl⟩ : syracuseStep 5205385 = 3904039) B3904039
theorem B1372297 : Blo 674311 1372297 := bstep (se 2 (by rfl) ⟨514611, by rfl⟩ : syracuseStep 1372297 = 1029223) B1029223
theorem B1013183 : Blo 674311 1013183 := bstep (se 1 (by rfl) ⟨759887, by rfl⟩ : syracuseStep 1013183 = 1519775) B1519775
theorem B9730169 : Blo 674311 9730169 := bstep (se 2 (by rfl) ⟨3648813, by rfl⟩ : syracuseStep 9730169 = 7297627) B7297627
theorem B1519559 : Blo 674311 1519559 := bstep (se 1 (by rfl) ⟨1139669, by rfl⟩ : syracuseStep 1519559 = 2279339) B2279339
theorem B1523879 : Blo 674311 1523879 := bstep (se 1 (by rfl) ⟨1142909, by rfl⟩ : syracuseStep 1523879 = 2285819) B2285819
theorem B675455 : Blo 674311 675455 := bstep (se 1 (by rfl) ⟨506591, by rfl⟩ : syracuseStep 675455 = 1013183) B1013183
theorem B1233235 : Blo 674311 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B6940513 : Blo 674311 6940513 := bstep (se 2 (by rfl) ⟨2602692, by rfl⟩ : syracuseStep 6940513 = 5205385) B5205385
theorem B1829729 : Blo 674311 1829729 := bstep (se 2 (by rfl) ⟨686148, by rfl⟩ : syracuseStep 1829729 = 1372297) B1372297
theorem B1011935 : Blo 674311 1011935 := bstep (se 1 (by rfl) ⟨758951, by rfl⟩ : syracuseStep 1011935 = 1517903) B1517903
theorem B4618907 : Blo 674311 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B6486779 : Blo 674311 6486779 := bstep (se 1 (by rfl) ⟨4865084, by rfl⟩ : syracuseStep 6486779 = 9730169) B9730169
theorem B1015487 : Blo 674311 1015487 := bstep (se 1 (by rfl) ⟨761615, by rfl⟩ : syracuseStep 1015487 = 1523231) B1523231
theorem B1015919 : Blo 674311 1015919 := bstep (se 1 (by rfl) ⟨761939, by rfl⟩ : syracuseStep 1015919 = 1523879) B1523879
theorem B1644313 : Blo 674311 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B1219819 : Blo 674311 1219819 := bstep (se 1 (by rfl) ⟨914864, by rfl⟩ : syracuseStep 1219819 = 1829729) B1829729
theorem B9254017 : Blo 674311 9254017 := bstep (se 2 (by rfl) ⟨3470256, by rfl⟩ : syracuseStep 9254017 = 6940513) B6940513
theorem B674623 : Blo 674311 674623 := bstep (se 1 (by rfl) ⟨505967, by rfl⟩ : syracuseStep 674623 = 1011935) B1011935
theorem B676991 : Blo 674311 676991 := bstep (se 1 (by rfl) ⟨507743, by rfl⟩ : syracuseStep 676991 = 1015487) B1015487
theorem B1013039 : Blo 674311 1013039 := bstep (se 1 (by rfl) ⟨759779, by rfl⟩ : syracuseStep 1013039 = 1519559) B1519559
theorem B3079271 : Blo 674311 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B4324519 : Blo 674311 4324519 := bstep (se 1 (by rfl) ⟨3243389, by rfl⟩ : syracuseStep 4324519 = 6486779) B6486779
theorem B12338689 : Blo 674311 12338689 := bstep (se 2 (by rfl) ⟨4627008, by rfl⟩ : syracuseStep 12338689 = 9254017) B9254017
theorem B675359 : Blo 674311 675359 := bstep (se 1 (by rfl) ⟨506519, by rfl⟩ : syracuseStep 675359 = 1013039) B1013039
theorem B1626425 : Blo 674311 1626425 := bstep (se 2 (by rfl) ⟨609909, by rfl⟩ : syracuseStep 1626425 = 1219819) B1219819
theorem B2052847 : Blo 674311 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B677279 : Blo 674311 677279 := bstep (se 1 (by rfl) ⟨507959, by rfl⟩ : syracuseStep 677279 = 1015919) B1015919
theorem B2192417 : Blo 674311 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B5766025 : Blo 674311 5766025 := bstep (se 2 (by rfl) ⟨2162259, by rfl⟩ : syracuseStep 5766025 = 4324519) B4324519
theorem B16451585 : Blo 674311 16451585 := bstep (se 2 (by rfl) ⟨6169344, by rfl⟩ : syracuseStep 16451585 = 12338689) B12338689
theorem B1084283 : Blo 674311 1084283 := bstep (se 1 (by rfl) ⟨813212, by rfl⟩ : syracuseStep 1084283 = 1626425) B1626425
theorem B10948517 : Blo 674311 10948517 := bstep (se 4 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 10948517 = 2052847) B2052847
theorem B1461611 : Blo 674311 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B7688033 : Blo 674311 7688033 := bstep (se 2 (by rfl) ⟨2883012, by rfl⟩ : syracuseStep 7688033 = 5766025) B5766025
theorem B722855 : Blo 674311 722855 := bstep (se 1 (by rfl) ⟨542141, by rfl⟩ : syracuseStep 722855 = 1084283) B1084283
theorem B5125355 : Blo 674311 5125355 := bstep (se 1 (by rfl) ⟨3844016, by rfl⟩ : syracuseStep 5125355 = 7688033) B7688033
theorem B10967723 : Blo 674311 10967723 := bstep (se 1 (by rfl) ⟨8225792, by rfl⟩ : syracuseStep 10967723 = 16451585) B16451585
theorem B7299011 : Blo 674311 7299011 := bstep (se 1 (by rfl) ⟨5474258, by rfl⟩ : syracuseStep 7299011 = 10948517) B10948517
theorem B3897629 : Blo 674311 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B7311815 : Blo 674311 7311815 := bstep (se 1 (by rfl) ⟨5483861, by rfl⟩ : syracuseStep 7311815 = 10967723) B10967723
theorem B3416903 : Blo 674311 3416903 := bstep (se 1 (by rfl) ⟨2562677, by rfl⟩ : syracuseStep 3416903 = 5125355) B5125355
theorem B2598419 : Blo 674311 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B4866007 : Blo 674311 4866007 := bstep (se 1 (by rfl) ⟨3649505, by rfl⟩ : syracuseStep 4866007 = 7299011) B7299011
theorem B1927613 : Blo 674311 1927613 := bstep (se 3 (by rfl) ⟨361427, by rfl⟩ : syracuseStep 1927613 = 722855) B722855
theorem B1285075 : Blo 674311 1285075 := bstep (se 1 (by rfl) ⟨963806, by rfl⟩ : syracuseStep 1285075 = 1927613) B1927613
theorem B2277935 : Blo 674311 2277935 := bstep (se 1 (by rfl) ⟨1708451, by rfl⟩ : syracuseStep 2277935 = 3416903) B3416903
theorem B4874543 : Blo 674311 4874543 := bstep (se 1 (by rfl) ⟨3655907, by rfl⟩ : syracuseStep 4874543 = 7311815) B7311815
theorem B1732279 : Blo 674311 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B6488009 : Blo 674311 6488009 := bstep (se 2 (by rfl) ⟨2433003, by rfl⟩ : syracuseStep 6488009 = 4866007) B4866007
theorem B3249695 : Blo 674311 3249695 := bstep (se 1 (by rfl) ⟨2437271, by rfl⟩ : syracuseStep 3249695 = 4874543) B4874543
theorem B1713433 : Blo 674311 1713433 := bstep (se 2 (by rfl) ⟨642537, by rfl⟩ : syracuseStep 1713433 = 1285075) B1285075
theorem B1518623 : Blo 674311 1518623 := bstep (se 1 (by rfl) ⟨1138967, by rfl⟩ : syracuseStep 1518623 = 2277935) B2277935
theorem B2309705 : Blo 674311 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B4325339 : Blo 674311 4325339 := bstep (se 1 (by rfl) ⟨3244004, by rfl⟩ : syracuseStep 4325339 = 6488009) B6488009
theorem B2166463 : Blo 674311 2166463 := bstep (se 1 (by rfl) ⟨1624847, by rfl⟩ : syracuseStep 2166463 = 3249695) B3249695
theorem B2284577 : Blo 674311 2284577 := bstep (se 2 (by rfl) ⟨856716, by rfl⟩ : syracuseStep 2284577 = 1713433) B1713433
theorem B1012415 : Blo 674311 1012415 := bstep (se 1 (by rfl) ⟨759311, by rfl⟩ : syracuseStep 1012415 = 1518623) B1518623
theorem B1539803 : Blo 674311 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B11534237 : Blo 674311 11534237 := bstep (se 3 (by rfl) ⟨2162669, by rfl⟩ : syracuseStep 11534237 = 4325339) B4325339
theorem B2888617 : Blo 674311 2888617 := bstep (se 2 (by rfl) ⟨1083231, by rfl⟩ : syracuseStep 2888617 = 2166463) B2166463
theorem B1026535 : Blo 674311 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B1523051 : Blo 674311 1523051 := bstep (se 1 (by rfl) ⟨1142288, by rfl⟩ : syracuseStep 1523051 = 2284577) B2284577
theorem B674943 : Blo 674311 674943 := bstep (se 1 (by rfl) ⟨506207, by rfl⟩ : syracuseStep 674943 = 1012415) B1012415
theorem B7689491 : Blo 674311 7689491 := bstep (se 1 (by rfl) ⟨5767118, by rfl⟩ : syracuseStep 7689491 = 11534237) B11534237
theorem B5126327 : Blo 674311 5126327 := bstep (se 1 (by rfl) ⟨3844745, by rfl⟩ : syracuseStep 5126327 = 7689491) B7689491
theorem B3851489 : Blo 674311 3851489 := bstep (se 2 (by rfl) ⟨1444308, by rfl⟩ : syracuseStep 3851489 = 2888617) B2888617
theorem B1368713 : Blo 674311 1368713 := bstep (se 2 (by rfl) ⟨513267, by rfl⟩ : syracuseStep 1368713 = 1026535) B1026535
theorem B1015367 : Blo 674311 1015367 := bstep (se 1 (by rfl) ⟨761525, by rfl⟩ : syracuseStep 1015367 = 1523051) B1523051
theorem B3417551 : Blo 674311 3417551 := bstep (se 1 (by rfl) ⟨2563163, by rfl⟩ : syracuseStep 3417551 = 5126327) B5126327
theorem B2567659 : Blo 674311 2567659 := bstep (se 1 (by rfl) ⟨1925744, by rfl⟩ : syracuseStep 2567659 = 3851489) B3851489
theorem B676911 : Blo 674311 676911 := bstep (se 1 (by rfl) ⟨507683, by rfl⟩ : syracuseStep 676911 = 1015367) B1015367
theorem B912475 : Blo 674311 912475 := bstep (se 1 (by rfl) ⟨684356, by rfl⟩ : syracuseStep 912475 = 1368713) B1368713
theorem B1216633 : Blo 674311 1216633 := bstep (se 2 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 1216633 = 912475) B912475
theorem B3423545 : Blo 674311 3423545 := bstep (se 2 (by rfl) ⟨1283829, by rfl⟩ : syracuseStep 3423545 = 2567659) B2567659
theorem B2278367 : Blo 674311 2278367 := bstep (se 1 (by rfl) ⟨1708775, by rfl⟩ : syracuseStep 2278367 = 3417551) B3417551
theorem B1518911 : Blo 674311 1518911 := bstep (se 1 (by rfl) ⟨1139183, by rfl⟩ : syracuseStep 1518911 = 2278367) B2278367
theorem B1622177 : Blo 674311 1622177 := bstep (se 2 (by rfl) ⟨608316, by rfl⟩ : syracuseStep 1622177 = 1216633) B1216633
theorem B2282363 : Blo 674311 2282363 := bstep (se 1 (by rfl) ⟨1711772, by rfl⟩ : syracuseStep 2282363 = 3423545) B3423545
theorem B1081451 : Blo 674311 1081451 := bstep (se 1 (by rfl) ⟨811088, by rfl⟩ : syracuseStep 1081451 = 1622177) B1622177
theorem B1521575 : Blo 674311 1521575 := bstep (se 1 (by rfl) ⟨1141181, by rfl⟩ : syracuseStep 1521575 = 2282363) B2282363
theorem B1012607 : Blo 674311 1012607 := bstep (se 1 (by rfl) ⟨759455, by rfl⟩ : syracuseStep 1012607 = 1518911) B1518911
theorem B2883869 : Blo 674311 2883869 := bstep (se 3 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 2883869 = 1081451) B1081451
theorem B675071 : Blo 674311 675071 := bstep (se 1 (by rfl) ⟨506303, by rfl⟩ : syracuseStep 675071 = 1012607) B1012607
theorem B1014383 : Blo 674311 1014383 := bstep (se 1 (by rfl) ⟨760787, by rfl⟩ : syracuseStep 1014383 = 1521575) B1521575
theorem B676255 : Blo 674311 676255 := bstep (se 1 (by rfl) ⟨507191, by rfl⟩ : syracuseStep 676255 = 1014383) B1014383
theorem B1922579 : Blo 674311 1922579 := bstep (se 1 (by rfl) ⟨1441934, by rfl⟩ : syracuseStep 1922579 = 2883869) B2883869
theorem B1281719 : Blo 674311 1281719 := bstep (se 1 (by rfl) ⟨961289, by rfl⟩ : syracuseStep 1281719 = 1922579) B1922579
theorem B854479 : Blo 674311 854479 := bstep (se 1 (by rfl) ⟨640859, by rfl⟩ : syracuseStep 854479 = 1281719) B1281719
theorem B1139305 : Blo 674311 1139305 := bstep (se 2 (by rfl) ⟨427239, by rfl⟩ : syracuseStep 1139305 = 854479) B854479
theorem B1519073 : Blo 674311 1519073 := bstep (se 2 (by rfl) ⟨569652, by rfl⟩ : syracuseStep 1519073 = 1139305) B1139305
theorem B1012715 : Blo 674311 1012715 := bstep (se 1 (by rfl) ⟨759536, by rfl⟩ : syracuseStep 1012715 = 1519073) B1519073
theorem B675143 : Blo 674311 675143 := bstep (se 1 (by rfl) ⟨506357, by rfl⟩ : syracuseStep 675143 = 1012715) B1012715

theorem C0 (j : ℕ) (h1 : 168577 ≤ j) (h2 : j ≤ 169276) : Blo 674311 (4 * j + 3) := by
  interval_cases j
  · exact B674311
  · exact B674315
  · exact B674319
  · exact B674323
  · exact B674327
  · exact B674331
  · exact B674335
  · exact B674339
  · exact B674343
  · exact B674347
  · exact B674351
  · exact B674355
  · exact B674359
  · exact B674363
  · exact B674367
  · exact B674371
  · exact B674375
  · exact B674379
  · exact B674383
  · exact B674387
  · exact B674391
  · exact B674395
  · exact B674399
  · exact B674403
  · exact B674407
  · exact B674411
  · exact B674415
  · exact B674419
  · exact B674423
  · exact B674427
  · exact B674431
  · exact B674435
  · exact B674439
  · exact B674443
  · exact B674447
  · exact B674451
  · exact B674455
  · exact B674459
  · exact B674463
  · exact B674467
  · exact B674471
  · exact B674475
  · exact B674479
  · exact B674483
  · exact B674487
  · exact B674491
  · exact B674495
  · exact B674499
  · exact B674503
  · exact B674507
  · exact B674511
  · exact B674515
  · exact B674519
  · exact B674523
  · exact B674527
  · exact B674531
  · exact B674535
  · exact B674539
  · exact B674543
  · exact B674547
  · exact B674551
  · exact B674555
  · exact B674559
  · exact B674563
  · exact B674567
  · exact B674571
  · exact B674575
  · exact B674579
  · exact B674583
  · exact B674587
  · exact B674591
  · exact B674595
  · exact B674599
  · exact B674603
  · exact B674607
  · exact B674611
  · exact B674615
  · exact B674619
  · exact B674623
  · exact B674627
  · exact B674631
  · exact B674635
  · exact B674639
  · exact B674643
  · exact B674647
  · exact B674651
  · exact B674655
  · exact B674659
  · exact B674663
  · exact B674667
  · exact B674671
  · exact B674675
  · exact B674679
  · exact B674683
  · exact B674687
  · exact B674691
  · exact B674695
  · exact B674699
  · exact B674703
  · exact B674707
  · exact B674711
  · exact B674715
  · exact B674719
  · exact B674723
  · exact B674727
  · exact B674731
  · exact B674735
  · exact B674739
  · exact B674743
  · exact B674747
  · exact B674751
  · exact B674755
  · exact B674759
  · exact B674763
  · exact B674767
  · exact B674771
  · exact B674775
  · exact B674779
  · exact B674783
  · exact B674787
  · exact B674791
  · exact B674795
  · exact B674799
  · exact B674803
  · exact B674807
  · exact B674811
  · exact B674815
  · exact B674819
  · exact B674823
  · exact B674827
  · exact B674831
  · exact B674835
  · exact B674839
  · exact B674843
  · exact B674847
  · exact B674851
  · exact B674855
  · exact B674859
  · exact B674863
  · exact B674867
  · exact B674871
  · exact B674875
  · exact B674879
  · exact B674883
  · exact B674887
  · exact B674891
  · exact B674895
  · exact B674899
  · exact B674903
  · exact B674907
  · exact B674911
  · exact B674915
  · exact B674919
  · exact B674923
  · exact B674927
  · exact B674931
  · exact B674935
  · exact B674939
  · exact B674943
  · exact B674947
  · exact B674951
  · exact B674955
  · exact B674959
  · exact B674963
  · exact B674967
  · exact B674971
  · exact B674975
  · exact B674979
  · exact B674983
  · exact B674987
  · exact B674991
  · exact B674995
  · exact B674999
  · exact B675003
  · exact B675007
  · exact B675011
  · exact B675015
  · exact B675019
  · exact B675023
  · exact B675027
  · exact B675031
  · exact B675035
  · exact B675039
  · exact B675043
  · exact B675047
  · exact B675051
  · exact B675055
  · exact B675059
  · exact B675063
  · exact B675067
  · exact B675071
  · exact B675075
  · exact B675079
  · exact B675083
  · exact B675087
  · exact B675091
  · exact B675095
  · exact B675099
  · exact B675103
  · exact B675107
  · exact B675111
  · exact B675115
  · exact B675119
  · exact B675123
  · exact B675127
  · exact B675131
  · exact B675135
  · exact B675139
  · exact B675143
  · exact B675147
  · exact B675151
  · exact B675155
  · exact B675159
  · exact B675163
  · exact B675167
  · exact B675171
  · exact B675175
  · exact B675179
  · exact B675183
  · exact B675187
  · exact B675191
  · exact B675195
  · exact B675199
  · exact B675203
  · exact B675207
  · exact B675211
  · exact B675215
  · exact B675219
  · exact B675223
  · exact B675227
  · exact B675231
  · exact B675235
  · exact B675239
  · exact B675243
  · exact B675247
  · exact B675251
  · exact B675255
  · exact B675259
  · exact B675263
  · exact B675267
  · exact B675271
  · exact B675275
  · exact B675279
  · exact B675283
  · exact B675287
  · exact B675291
  · exact B675295
  · exact B675299
  · exact B675303
  · exact B675307
  · exact B675311
  · exact B675315
  · exact B675319
  · exact B675323
  · exact B675327
  · exact B675331
  · exact B675335
  · exact B675339
  · exact B675343
  · exact B675347
  · exact B675351
  · exact B675355
  · exact B675359
  · exact B675363
  · exact B675367
  · exact B675371
  · exact B675375
  · exact B675379
  · exact B675383
  · exact B675387
  · exact B675391
  · exact B675395
  · exact B675399
  · exact B675403
  · exact B675407
  · exact B675411
  · exact B675415
  · exact B675419
  · exact B675423
  · exact B675427
  · exact B675431
  · exact B675435
  · exact B675439
  · exact B675443
  · exact B675447
  · exact B675451
  · exact B675455
  · exact B675459
  · exact B675463
  · exact B675467
  · exact B675471
  · exact B675475
  · exact B675479
  · exact B675483
  · exact B675487
  · exact B675491
  · exact B675495
  · exact B675499
  · exact B675503
  · exact B675507
  · exact B675511
  · exact B675515
  · exact B675519
  · exact B675523
  · exact B675527
  · exact B675531
  · exact B675535
  · exact B675539
  · exact B675543
  · exact B675547
  · exact B675551
  · exact B675555
  · exact B675559
  · exact B675563
  · exact B675567
  · exact B675571
  · exact B675575
  · exact B675579
  · exact B675583
  · exact B675587
  · exact B675591
  · exact B675595
  · exact B675599
  · exact B675603
  · exact B675607
  · exact B675611
  · exact B675615
  · exact B675619
  · exact B675623
  · exact B675627
  · exact B675631
  · exact B675635
  · exact B675639
  · exact B675643
  · exact B675647
  · exact B675651
  · exact B675655
  · exact B675659
  · exact B675663
  · exact B675667
  · exact B675671
  · exact B675675
  · exact B675679
  · exact B675683
  · exact B675687
  · exact B675691
  · exact B675695
  · exact B675699
  · exact B675703
  · exact B675707
  · exact B675711
  · exact B675715
  · exact B675719
  · exact B675723
  · exact B675727
  · exact B675731
  · exact B675735
  · exact B675739
  · exact B675743
  · exact B675747
  · exact B675751
  · exact B675755
  · exact B675759
  · exact B675763
  · exact B675767
  · exact B675771
  · exact B675775
  · exact B675779
  · exact B675783
  · exact B675787
  · exact B675791
  · exact B675795
  · exact B675799
  · exact B675803
  · exact B675807
  · exact B675811
  · exact B675815
  · exact B675819
  · exact B675823
  · exact B675827
  · exact B675831
  · exact B675835
  · exact B675839
  · exact B675843
  · exact B675847
  · exact B675851
  · exact B675855
  · exact B675859
  · exact B675863
  · exact B675867
  · exact B675871
  · exact B675875
  · exact B675879
  · exact B675883
  · exact B675887
  · exact B675891
  · exact B675895
  · exact B675899
  · exact B675903
  · exact B675907
  · exact B675911
  · exact B675915
  · exact B675919
  · exact B675923
  · exact B675927
  · exact B675931
  · exact B675935
  · exact B675939
  · exact B675943
  · exact B675947
  · exact B675951
  · exact B675955
  · exact B675959
  · exact B675963
  · exact B675967
  · exact B675971
  · exact B675975
  · exact B675979
  · exact B675983
  · exact B675987
  · exact B675991
  · exact B675995
  · exact B675999
  · exact B676003
  · exact B676007
  · exact B676011
  · exact B676015
  · exact B676019
  · exact B676023
  · exact B676027
  · exact B676031
  · exact B676035
  · exact B676039
  · exact B676043
  · exact B676047
  · exact B676051
  · exact B676055
  · exact B676059
  · exact B676063
  · exact B676067
  · exact B676071
  · exact B676075
  · exact B676079
  · exact B676083
  · exact B676087
  · exact B676091
  · exact B676095
  · exact B676099
  · exact B676103
  · exact B676107
  · exact B676111
  · exact B676115
  · exact B676119
  · exact B676123
  · exact B676127
  · exact B676131
  · exact B676135
  · exact B676139
  · exact B676143
  · exact B676147
  · exact B676151
  · exact B676155
  · exact B676159
  · exact B676163
  · exact B676167
  · exact B676171
  · exact B676175
  · exact B676179
  · exact B676183
  · exact B676187
  · exact B676191
  · exact B676195
  · exact B676199
  · exact B676203
  · exact B676207
  · exact B676211
  · exact B676215
  · exact B676219
  · exact B676223
  · exact B676227
  · exact B676231
  · exact B676235
  · exact B676239
  · exact B676243
  · exact B676247
  · exact B676251
  · exact B676255
  · exact B676259
  · exact B676263
  · exact B676267
  · exact B676271
  · exact B676275
  · exact B676279
  · exact B676283
  · exact B676287
  · exact B676291
  · exact B676295
  · exact B676299
  · exact B676303
  · exact B676307
  · exact B676311
  · exact B676315
  · exact B676319
  · exact B676323
  · exact B676327
  · exact B676331
  · exact B676335
  · exact B676339
  · exact B676343
  · exact B676347
  · exact B676351
  · exact B676355
  · exact B676359
  · exact B676363
  · exact B676367
  · exact B676371
  · exact B676375
  · exact B676379
  · exact B676383
  · exact B676387
  · exact B676391
  · exact B676395
  · exact B676399
  · exact B676403
  · exact B676407
  · exact B676411
  · exact B676415
  · exact B676419
  · exact B676423
  · exact B676427
  · exact B676431
  · exact B676435
  · exact B676439
  · exact B676443
  · exact B676447
  · exact B676451
  · exact B676455
  · exact B676459
  · exact B676463
  · exact B676467
  · exact B676471
  · exact B676475
  · exact B676479
  · exact B676483
  · exact B676487
  · exact B676491
  · exact B676495
  · exact B676499
  · exact B676503
  · exact B676507
  · exact B676511
  · exact B676515
  · exact B676519
  · exact B676523
  · exact B676527
  · exact B676531
  · exact B676535
  · exact B676539
  · exact B676543
  · exact B676547
  · exact B676551
  · exact B676555
  · exact B676559
  · exact B676563
  · exact B676567
  · exact B676571
  · exact B676575
  · exact B676579
  · exact B676583
  · exact B676587
  · exact B676591
  · exact B676595
  · exact B676599
  · exact B676603
  · exact B676607
  · exact B676611
  · exact B676615
  · exact B676619
  · exact B676623
  · exact B676627
  · exact B676631
  · exact B676635
  · exact B676639
  · exact B676643
  · exact B676647
  · exact B676651
  · exact B676655
  · exact B676659
  · exact B676663
  · exact B676667
  · exact B676671
  · exact B676675
  · exact B676679
  · exact B676683
  · exact B676687
  · exact B676691
  · exact B676695
  · exact B676699
  · exact B676703
  · exact B676707
  · exact B676711
  · exact B676715
  · exact B676719
  · exact B676723
  · exact B676727
  · exact B676731
  · exact B676735
  · exact B676739
  · exact B676743
  · exact B676747
  · exact B676751
  · exact B676755
  · exact B676759
  · exact B676763
  · exact B676767
  · exact B676771
  · exact B676775
  · exact B676779
  · exact B676783
  · exact B676787
  · exact B676791
  · exact B676795
  · exact B676799
  · exact B676803
  · exact B676807
  · exact B676811
  · exact B676815
  · exact B676819
  · exact B676823
  · exact B676827
  · exact B676831
  · exact B676835
  · exact B676839
  · exact B676843
  · exact B676847
  · exact B676851
  · exact B676855
  · exact B676859
  · exact B676863
  · exact B676867
  · exact B676871
  · exact B676875
  · exact B676879
  · exact B676883
  · exact B676887
  · exact B676891
  · exact B676895
  · exact B676899
  · exact B676903
  · exact B676907
  · exact B676911
  · exact B676915
  · exact B676919
  · exact B676923
  · exact B676927
  · exact B676931
  · exact B676935
  · exact B676939
  · exact B676943
  · exact B676947
  · exact B676951
  · exact B676955
  · exact B676959
  · exact B676963
  · exact B676967
  · exact B676971
  · exact B676975
  · exact B676979
  · exact B676983
  · exact B676987
  · exact B676991
  · exact B676995
  · exact B676999
  · exact B677003
  · exact B677007
  · exact B677011
  · exact B677015
  · exact B677019
  · exact B677023
  · exact B677027
  · exact B677031
  · exact B677035
  · exact B677039
  · exact B677043
  · exact B677047
  · exact B677051
  · exact B677055
  · exact B677059
  · exact B677063
  · exact B677067
  · exact B677071
  · exact B677075
  · exact B677079
  · exact B677083
  · exact B677087
  · exact B677091
  · exact B677095
  · exact B677099
  · exact B677103
  · exact B677107

theorem C1 (j : ℕ) (h1 : 169277 ≤ j) (h2 : j ≤ 169577) : Blo 674311 (4 * j + 3) := by
  interval_cases j
  · exact B677111
  · exact B677115
  · exact B677119
  · exact B677123
  · exact B677127
  · exact B677131
  · exact B677135
  · exact B677139
  · exact B677143
  · exact B677147
  · exact B677151
  · exact B677155
  · exact B677159
  · exact B677163
  · exact B677167
  · exact B677171
  · exact B677175
  · exact B677179
  · exact B677183
  · exact B677187
  · exact B677191
  · exact B677195
  · exact B677199
  · exact B677203
  · exact B677207
  · exact B677211
  · exact B677215
  · exact B677219
  · exact B677223
  · exact B677227
  · exact B677231
  · exact B677235
  · exact B677239
  · exact B677243
  · exact B677247
  · exact B677251
  · exact B677255
  · exact B677259
  · exact B677263
  · exact B677267
  · exact B677271
  · exact B677275
  · exact B677279
  · exact B677283
  · exact B677287
  · exact B677291
  · exact B677295
  · exact B677299
  · exact B677303
  · exact B677307
  · exact B677311
  · exact B677315
  · exact B677319
  · exact B677323
  · exact B677327
  · exact B677331
  · exact B677335
  · exact B677339
  · exact B677343
  · exact B677347
  · exact B677351
  · exact B677355
  · exact B677359
  · exact B677363
  · exact B677367
  · exact B677371
  · exact B677375
  · exact B677379
  · exact B677383
  · exact B677387
  · exact B677391
  · exact B677395
  · exact B677399
  · exact B677403
  · exact B677407
  · exact B677411
  · exact B677415
  · exact B677419
  · exact B677423
  · exact B677427
  · exact B677431
  · exact B677435
  · exact B677439
  · exact B677443
  · exact B677447
  · exact B677451
  · exact B677455
  · exact B677459
  · exact B677463
  · exact B677467
  · exact B677471
  · exact B677475
  · exact B677479
  · exact B677483
  · exact B677487
  · exact B677491
  · exact B677495
  · exact B677499
  · exact B677503
  · exact B677507
  · exact B677511
  · exact B677515
  · exact B677519
  · exact B677523
  · exact B677527
  · exact B677531
  · exact B677535
  · exact B677539
  · exact B677543
  · exact B677547
  · exact B677551
  · exact B677555
  · exact B677559
  · exact B677563
  · exact B677567
  · exact B677571
  · exact B677575
  · exact B677579
  · exact B677583
  · exact B677587
  · exact B677591
  · exact B677595
  · exact B677599
  · exact B677603
  · exact B677607
  · exact B677611
  · exact B677615
  · exact B677619
  · exact B677623
  · exact B677627
  · exact B677631
  · exact B677635
  · exact B677639
  · exact B677643
  · exact B677647
  · exact B677651
  · exact B677655
  · exact B677659
  · exact B677663
  · exact B677667
  · exact B677671
  · exact B677675
  · exact B677679
  · exact B677683
  · exact B677687
  · exact B677691
  · exact B677695
  · exact B677699
  · exact B677703
  · exact B677707
  · exact B677711
  · exact B677715
  · exact B677719
  · exact B677723
  · exact B677727
  · exact B677731
  · exact B677735
  · exact B677739
  · exact B677743
  · exact B677747
  · exact B677751
  · exact B677755
  · exact B677759
  · exact B677763
  · exact B677767
  · exact B677771
  · exact B677775
  · exact B677779
  · exact B677783
  · exact B677787
  · exact B677791
  · exact B677795
  · exact B677799
  · exact B677803
  · exact B677807
  · exact B677811
  · exact B677815
  · exact B677819
  · exact B677823
  · exact B677827
  · exact B677831
  · exact B677835
  · exact B677839
  · exact B677843
  · exact B677847
  · exact B677851
  · exact B677855
  · exact B677859
  · exact B677863
  · exact B677867
  · exact B677871
  · exact B677875
  · exact B677879
  · exact B677883
  · exact B677887
  · exact B677891
  · exact B677895
  · exact B677899
  · exact B677903
  · exact B677907
  · exact B677911
  · exact B677915
  · exact B677919
  · exact B677923
  · exact B677927
  · exact B677931
  · exact B677935
  · exact B677939
  · exact B677943
  · exact B677947
  · exact B677951
  · exact B677955
  · exact B677959
  · exact B677963
  · exact B677967
  · exact B677971
  · exact B677975
  · exact B677979
  · exact B677983
  · exact B677987
  · exact B677991
  · exact B677995
  · exact B677999
  · exact B678003
  · exact B678007
  · exact B678011
  · exact B678015
  · exact B678019
  · exact B678023
  · exact B678027
  · exact B678031
  · exact B678035
  · exact B678039
  · exact B678043
  · exact B678047
  · exact B678051
  · exact B678055
  · exact B678059
  · exact B678063
  · exact B678067
  · exact B678071
  · exact B678075
  · exact B678079
  · exact B678083
  · exact B678087
  · exact B678091
  · exact B678095
  · exact B678099
  · exact B678103
  · exact B678107
  · exact B678111
  · exact B678115
  · exact B678119
  · exact B678123
  · exact B678127
  · exact B678131
  · exact B678135
  · exact B678139
  · exact B678143
  · exact B678147
  · exact B678151
  · exact B678155
  · exact B678159
  · exact B678163
  · exact B678167
  · exact B678171
  · exact B678175
  · exact B678179
  · exact B678183
  · exact B678187
  · exact B678191
  · exact B678195
  · exact B678199
  · exact B678203
  · exact B678207
  · exact B678211
  · exact B678215
  · exact B678219
  · exact B678223
  · exact B678227
  · exact B678231
  · exact B678235
  · exact B678239
  · exact B678243
  · exact B678247
  · exact B678251
  · exact B678255
  · exact B678259
  · exact B678263
  · exact B678267
  · exact B678271
  · exact B678275
  · exact B678279
  · exact B678283
  · exact B678287
  · exact B678291
  · exact B678295
  · exact B678299
  · exact B678303
  · exact B678307
  · exact B678311

theorem solution (m : ℕ) (hlo : 674311 ≤ m) (hhi : m ≤ 678311) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 168577 ≤ j := by omega
    have hj2 : j ≤ 169577 := by omega
    have hb : Blo 674311 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 169277 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
