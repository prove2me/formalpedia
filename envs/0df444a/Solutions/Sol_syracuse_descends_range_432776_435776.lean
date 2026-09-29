-- Prove2me | solution 1 for syracuse_descends_range_432776_435776
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:55.051375+00:00
-- url     : https://prove2.me/submissions/a2fb3f8d-1e4d-4360-8eb2-466b49375a69

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


theorem B974861 : Blo 432776 974861 := bbase (se 3 (by rfl) ⟨182786, by rfl⟩ : syracuseStep 974861 = 365573) (by norm_num)
theorem B3301397 : Blo 432776 3301397 := bbase (se 6 (by rfl) ⟨77376, by rfl⟩ : syracuseStep 3301397 = 154753) (by norm_num)
theorem B2203685 : Blo 432776 2203685 := bbase (se 4 (by rfl) ⟨206595, by rfl⟩ : syracuseStep 2203685 = 413191) (by norm_num)
theorem B1237045 : Blo 432776 1237045 := bbase (se 5 (by rfl) ⟨57986, by rfl⟩ : syracuseStep 1237045 = 115973) (by norm_num)
theorem B1450037 : Blo 432776 1450037 := bbase (se 5 (by rfl) ⟨67970, by rfl⟩ : syracuseStep 1450037 = 135941) (by norm_num)
theorem B974933 : Blo 432776 974933 := bbase (se 8 (by rfl) ⟨5712, by rfl⟩ : syracuseStep 974933 = 11425) (by norm_num)
theorem B1097813 : Blo 432776 1097813 := bbase (se 8 (by rfl) ⟨6432, by rfl⟩ : syracuseStep 1097813 = 12865) (by norm_num)
theorem B1859669 : Blo 432776 1859669 := bbase (se 8 (by rfl) ⟨10896, by rfl⟩ : syracuseStep 1859669 = 21793) (by norm_num)
theorem B548957 : Blo 432776 548957 := bbase (se 3 (by rfl) ⟨102929, by rfl⟩ : syracuseStep 548957 = 205859) (by norm_num)
theorem B549013 : Blo 432776 549013 := bbase (se 6 (by rfl) ⟨12867, by rfl⟩ : syracuseStep 549013 = 25735) (by norm_num)
theorem B5578901 : Blo 432776 5578901 := bbase (se 6 (by rfl) ⟨130755, by rfl⟩ : syracuseStep 5578901 = 261511) (by norm_num)
theorem B975005 : Blo 432776 975005 := bbase (se 3 (by rfl) ⟨182813, by rfl⟩ : syracuseStep 975005 = 365627) (by norm_num)
theorem B1102349 : Blo 432776 1102349 := bbase (se 3 (by rfl) ⟨206690, by rfl⟩ : syracuseStep 1102349 = 413381) (by norm_num)
theorem B1851605 : Blo 432776 1851605 := bbase (se 7 (by rfl) ⟨21698, by rfl⟩ : syracuseStep 1851605 = 43397) (by norm_num)
theorem B975077 : Blo 432776 975077 := bbase (se 4 (by rfl) ⟨91413, by rfl⟩ : syracuseStep 975077 = 182827) (by norm_num)
theorem B1392869 : Blo 432776 1392869 := bbase (se 4 (by rfl) ⟨130581, by rfl⟩ : syracuseStep 1392869 = 261163) (by norm_num)
theorem B549109 : Blo 432776 549109 := bbase (se 5 (by rfl) ⟨25739, by rfl⟩ : syracuseStep 549109 = 51479) (by norm_num)
theorem B975149 : Blo 432776 975149 := bbase (se 3 (by rfl) ⟨182840, by rfl⟩ : syracuseStep 975149 = 365681) (by norm_num)
theorem B1040701 : Blo 432776 1040701 := bbase (se 3 (by rfl) ⟨195131, by rfl⟩ : syracuseStep 1040701 = 390263) (by norm_num)
theorem B1466693 : Blo 432776 1466693 := bbase (se 4 (by rfl) ⟨137502, by rfl⟩ : syracuseStep 1466693 = 275005) (by norm_num)
theorem B975221 : Blo 432776 975221 := bbase (se 5 (by rfl) ⟨45713, by rfl⟩ : syracuseStep 975221 = 91427) (by norm_num)
theorem B926093 : Blo 432776 926093 := bbase (se 3 (by rfl) ⟨173642, by rfl⟩ : syracuseStep 926093 = 347285) (by norm_num)
theorem B549281 : Blo 432776 549281 := bbase (se 2 (by rfl) ⟨205980, by rfl⟩ : syracuseStep 549281 = 411961) (by norm_num)
theorem B1098157 : Blo 432776 1098157 := bbase (se 3 (by rfl) ⟨205904, by rfl⟩ : syracuseStep 1098157 = 411809) (by norm_num)
theorem B3293621 : Blo 432776 3293621 := bbase (se 5 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 3293621 = 308777) (by norm_num)
theorem B975293 : Blo 432776 975293 := bbase (se 3 (by rfl) ⟨182867, by rfl⟩ : syracuseStep 975293 = 365735) (by norm_num)
theorem B2195909 : Blo 432776 2195909 := bbase (se 4 (by rfl) ⟨205866, by rfl⟩ : syracuseStep 2195909 = 411733) (by norm_num)
theorem B991685 : Blo 432776 991685 := bbase (se 4 (by rfl) ⟨92970, by rfl⟩ : syracuseStep 991685 = 185941) (by norm_num)
theorem B549337 : Blo 432776 549337 := bbase (se 2 (by rfl) ⟨206001, by rfl⟩ : syracuseStep 549337 = 412003) (by norm_num)
theorem B1671653 : Blo 432776 1671653 := bbase (se 4 (by rfl) ⟨156717, by rfl⟩ : syracuseStep 1671653 = 313435) (by norm_num)
theorem B975365 : Blo 432776 975365 := bbase (se 4 (by rfl) ⟨91440, by rfl⟩ : syracuseStep 975365 = 182881) (by norm_num)
theorem B696845 : Blo 432776 696845 := bbase (se 3 (by rfl) ⟨130658, by rfl⟩ : syracuseStep 696845 = 261317) (by norm_num)
theorem B1098269 : Blo 432776 1098269 := bbase (se 3 (by rfl) ⟨205925, by rfl⟩ : syracuseStep 1098269 = 411851) (by norm_num)
theorem B549433 : Blo 432776 549433 := bbase (se 2 (by rfl) ⟨206037, by rfl⟩ : syracuseStep 549433 = 412075) (by norm_num)
theorem B975437 : Blo 432776 975437 := bbase (se 3 (by rfl) ⟨182894, by rfl⟩ : syracuseStep 975437 = 365789) (by norm_num)
theorem B434765 : Blo 432776 434765 := bbase (se 3 (by rfl) ⟨81518, by rfl⟩ : syracuseStep 434765 = 163037) (by norm_num)
theorem B2466389 : Blo 432776 2466389 := bbase (se 8 (by rfl) ⟨14451, by rfl⟩ : syracuseStep 2466389 = 28903) (by norm_num)
theorem B975509 : Blo 432776 975509 := bbase (se 6 (by rfl) ⟨22863, by rfl⟩ : syracuseStep 975509 = 45727) (by norm_num)
theorem B7422677 : Blo 432776 7422677 := bbase (se 7 (by rfl) ⟨86984, by rfl⟩ : syracuseStep 7422677 = 173969) (by norm_num)
theorem B975581 : Blo 432776 975581 := bbase (se 3 (by rfl) ⟨182921, by rfl⟩ : syracuseStep 975581 = 365843) (by norm_num)
theorem B1098461 : Blo 432776 1098461 := bbase (se 3 (by rfl) ⟨205961, by rfl⟩ : syracuseStep 1098461 = 411923) (by norm_num)
theorem B549605 : Blo 432776 549605 := bbase (se 4 (by rfl) ⟨51525, by rfl⟩ : syracuseStep 549605 = 103051) (by norm_num)
theorem B1467125 : Blo 432776 1467125 := bbase (se 5 (by rfl) ⟨68771, by rfl⟩ : syracuseStep 1467125 = 137543) (by norm_num)
theorem B549661 : Blo 432776 549661 := bbase (se 3 (by rfl) ⟨103061, by rfl⟩ : syracuseStep 549661 = 206123) (by norm_num)
theorem B975653 : Blo 432776 975653 := bbase (se 4 (by rfl) ⟨91467, by rfl⟩ : syracuseStep 975653 = 182935) (by norm_num)
theorem B975725 : Blo 432776 975725 := bbase (se 3 (by rfl) ⟨182948, by rfl⟩ : syracuseStep 975725 = 365897) (by norm_num)
theorem B1409909 : Blo 432776 1409909 := bbase (se 5 (by rfl) ⟨66089, by rfl⟩ : syracuseStep 1409909 = 132179) (by norm_num)
theorem B549757 : Blo 432776 549757 := bbase (se 3 (by rfl) ⟨103079, by rfl⟩ : syracuseStep 549757 = 206159) (by norm_num)
theorem B975797 : Blo 432776 975797 := bbase (se 5 (by rfl) ⟨45740, by rfl⟩ : syracuseStep 975797 = 91481) (by norm_num)
theorem B975869 : Blo 432776 975869 := bbase (se 3 (by rfl) ⟨182975, by rfl⟩ : syracuseStep 975869 = 365951) (by norm_num)
theorem B697357 : Blo 432776 697357 := bbase (se 3 (by rfl) ⟨130754, by rfl⟩ : syracuseStep 697357 = 261509) (by norm_num)
theorem B549929 : Blo 432776 549929 := bbase (se 2 (by rfl) ⟨206223, by rfl⟩ : syracuseStep 549929 = 412447) (by norm_num)
theorem B1098805 : Blo 432776 1098805 := bbase (se 5 (by rfl) ⟨51506, by rfl⟩ : syracuseStep 1098805 = 103013) (by norm_num)
theorem B975941 : Blo 432776 975941 := bbase (se 4 (by rfl) ⟨91494, by rfl⟩ : syracuseStep 975941 = 182989) (by norm_num)
theorem B549985 : Blo 432776 549985 := bbase (se 2 (by rfl) ⟨206244, by rfl⟩ : syracuseStep 549985 = 412489) (by norm_num)
theorem B1000549 : Blo 432776 1000549 := bbase (se 4 (by rfl) ⟨93801, by rfl⟩ : syracuseStep 1000549 = 187603) (by norm_num)
theorem B976013 : Blo 432776 976013 := bbase (se 3 (by rfl) ⟨183002, by rfl⟩ : syracuseStep 976013 = 366005) (by norm_num)
theorem B1098917 : Blo 432776 1098917 := bbase (se 4 (by rfl) ⟨103023, by rfl⟩ : syracuseStep 1098917 = 206047) (by norm_num)
theorem B1467557 : Blo 432776 1467557 := bbase (se 4 (by rfl) ⟨137583, by rfl⟩ : syracuseStep 1467557 = 275167) (by norm_num)
theorem B550081 : Blo 432776 550081 := bbase (se 2 (by rfl) ⟨206280, by rfl⟩ : syracuseStep 550081 = 412561) (by norm_num)
theorem B976085 : Blo 432776 976085 := bbase (se 7 (by rfl) ⟨11438, by rfl⟩ : syracuseStep 976085 = 22877) (by norm_num)
theorem B1000669 : Blo 432776 1000669 := bbase (se 3 (by rfl) ⟨187625, by rfl⟩ : syracuseStep 1000669 = 375251) (by norm_num)
theorem B926981 : Blo 432776 926981 := bbase (se 4 (by rfl) ⟨86904, by rfl⟩ : syracuseStep 926981 = 173809) (by norm_num)
theorem B4179221 : Blo 432776 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B730397 : Blo 432776 730397 := bbase (se 3 (by rfl) ⟨136949, by rfl⟩ : syracuseStep 730397 = 273899) (by norm_num)
theorem B976157 : Blo 432776 976157 := bbase (se 3 (by rfl) ⟨183029, by rfl⟩ : syracuseStep 976157 = 366059) (by norm_num)
theorem B918821 : Blo 432776 918821 := bbase (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) (by norm_num)
theorem B2204981 : Blo 432776 2204981 := bbase (se 5 (by rfl) ⟨103358, by rfl⟩ : syracuseStep 2204981 = 206717) (by norm_num)
theorem B976229 : Blo 432776 976229 := bbase (se 4 (by rfl) ⟨91521, by rfl⟩ : syracuseStep 976229 = 183043) (by norm_num)
theorem B1099109 : Blo 432776 1099109 := bbase (se 4 (by rfl) ⟨103041, by rfl⟩ : syracuseStep 1099109 = 206083) (by norm_num)
theorem B1983845 : Blo 432776 1983845 := bbase (se 4 (by rfl) ⟨185985, by rfl⟩ : syracuseStep 1983845 = 371971) (by norm_num)
theorem B550253 : Blo 432776 550253 := bbase (se 3 (by rfl) ⟨103172, by rfl⟩ : syracuseStep 550253 = 206345) (by norm_num)
theorem B836981 : Blo 432776 836981 := bbase (se 5 (by rfl) ⟨39233, by rfl⟩ : syracuseStep 836981 = 78467) (by norm_num)
theorem B927101 : Blo 432776 927101 := bbase (se 3 (by rfl) ⟨173831, by rfl⟩ : syracuseStep 927101 = 347663) (by norm_num)
theorem B730525 : Blo 432776 730525 := bbase (se 3 (by rfl) ⟨136973, by rfl⟩ : syracuseStep 730525 = 273947) (by norm_num)
theorem B550309 : Blo 432776 550309 := bbase (se 4 (by rfl) ⟨51591, by rfl⟩ : syracuseStep 550309 = 103183) (by norm_num)
theorem B976301 : Blo 432776 976301 := bbase (se 3 (by rfl) ⟨183056, by rfl⟩ : syracuseStep 976301 = 366113) (by norm_num)
theorem B1041893 : Blo 432776 1041893 := bbase (se 4 (by rfl) ⟨97677, by rfl⟩ : syracuseStep 1041893 = 195355) (by norm_num)
theorem B730613 : Blo 432776 730613 := bbase (se 5 (by rfl) ⟨34247, by rfl⟩ : syracuseStep 730613 = 68495) (by norm_num)
theorem B976373 : Blo 432776 976373 := bbase (se 5 (by rfl) ⟨45767, by rfl⟩ : syracuseStep 976373 = 91535) (by norm_num)
theorem B1648133 : Blo 432776 1648133 := bbase (se 4 (by rfl) ⟨154512, by rfl⟩ : syracuseStep 1648133 = 309025) (by norm_num)
theorem B550405 : Blo 432776 550405 := bbase (se 4 (by rfl) ⟨51600, by rfl⟩ : syracuseStep 550405 = 103201) (by norm_num)
theorem B697901 : Blo 432776 697901 := bbase (se 3 (by rfl) ⟨130856, by rfl⟩ : syracuseStep 697901 = 261713) (by norm_num)
theorem B976445 : Blo 432776 976445 := bbase (se 3 (by rfl) ⟨183083, by rfl⟩ : syracuseStep 976445 = 366167) (by norm_num)
theorem B1467989 : Blo 432776 1467989 := bbase (se 8 (by rfl) ⟨8601, by rfl⟩ : syracuseStep 1467989 = 17203) (by norm_num)
theorem B1975909 : Blo 432776 1975909 := bbase (se 4 (by rfl) ⟨185241, by rfl⟩ : syracuseStep 1975909 = 370483) (by norm_num)
theorem B730741 : Blo 432776 730741 := bbase (se 5 (by rfl) ⟨34253, by rfl⟩ : syracuseStep 730741 = 68507) (by norm_num)
theorem B976517 : Blo 432776 976517 := bbase (se 4 (by rfl) ⟨91548, by rfl⟩ : syracuseStep 976517 = 183097) (by norm_num)
theorem B1320581 : Blo 432776 1320581 := bbase (se 4 (by rfl) ⟨123804, by rfl⟩ : syracuseStep 1320581 = 247609) (by norm_num)
theorem B1042085 : Blo 432776 1042085 := bbase (se 4 (by rfl) ⟨97695, by rfl⟩ : syracuseStep 1042085 = 195391) (by norm_num)
theorem B550577 : Blo 432776 550577 := bbase (se 2 (by rfl) ⟨206466, by rfl⟩ : syracuseStep 550577 = 412933) (by norm_num)
theorem B1099453 : Blo 432776 1099453 := bbase (se 3 (by rfl) ⟨206147, by rfl⟩ : syracuseStep 1099453 = 412295) (by norm_num)
theorem B730829 : Blo 432776 730829 := bbase (se 3 (by rfl) ⟨137030, by rfl⟩ : syracuseStep 730829 = 274061) (by norm_num)
theorem B976589 : Blo 432776 976589 := bbase (se 3 (by rfl) ⟨183110, by rfl⟩ : syracuseStep 976589 = 366221) (by norm_num)
theorem B2197205 : Blo 432776 2197205 := bbase (se 7 (by rfl) ⟨25748, by rfl⟩ : syracuseStep 2197205 = 51497) (by norm_num)
theorem B1058525 : Blo 432776 1058525 := bbase (se 3 (by rfl) ⟨198473, by rfl⟩ : syracuseStep 1058525 = 396947) (by norm_num)
theorem B550633 : Blo 432776 550633 := bbase (se 2 (by rfl) ⟨206487, by rfl⟩ : syracuseStep 550633 = 412975) (by norm_num)
theorem B976661 : Blo 432776 976661 := bbase (se 6 (by rfl) ⟨22890, by rfl⟩ : syracuseStep 976661 = 45781) (by norm_num)
theorem B1648421 : Blo 432776 1648421 := bbase (se 4 (by rfl) ⟨154539, by rfl⟩ : syracuseStep 1648421 = 309079) (by norm_num)
theorem B1099565 : Blo 432776 1099565 := bbase (se 3 (by rfl) ⟨206168, by rfl⟩ : syracuseStep 1099565 = 412337) (by norm_num)
theorem B550729 : Blo 432776 550729 := bbase (se 2 (by rfl) ⟨206523, by rfl⟩ : syracuseStep 550729 = 413047) (by norm_num)
theorem B730957 : Blo 432776 730957 := bbase (se 3 (by rfl) ⟨137054, by rfl⟩ : syracuseStep 730957 = 274109) (by norm_num)
theorem B976733 : Blo 432776 976733 := bbase (se 3 (by rfl) ⟨183137, by rfl⟩ : syracuseStep 976733 = 366275) (by norm_num)
theorem B714629 : Blo 432776 714629 := bbase (se 4 (by rfl) ⟨66996, by rfl⟩ : syracuseStep 714629 = 133993) (by norm_num)
theorem B4949909 : Blo 432776 4949909 := bbase (se 6 (by rfl) ⟨116013, by rfl⟩ : syracuseStep 4949909 = 232027) (by norm_num)
theorem B731045 : Blo 432776 731045 := bbase (se 4 (by rfl) ⟨68535, by rfl⟩ : syracuseStep 731045 = 137071) (by norm_num)
theorem B976805 : Blo 432776 976805 := bbase (se 4 (by rfl) ⟨91575, by rfl⟩ : syracuseStep 976805 = 183151) (by norm_num)
theorem B1853381 : Blo 432776 1853381 := bbase (se 4 (by rfl) ⟨173754, by rfl⟩ : syracuseStep 1853381 = 347509) (by norm_num)
theorem B649181 : Blo 432776 649181 := bbase (se 3 (by rfl) ⟨121721, by rfl⟩ : syracuseStep 649181 = 243443) (by norm_num)
theorem B976877 : Blo 432776 976877 := bbase (se 3 (by rfl) ⟨183164, by rfl⟩ : syracuseStep 976877 = 366329) (by norm_num)
theorem B1099757 : Blo 432776 1099757 := bbase (se 3 (by rfl) ⟨206204, by rfl⟩ : syracuseStep 1099757 = 412409) (by norm_num)
theorem B649205 : Blo 432776 649205 := bbase (se 5 (by rfl) ⟨30431, by rfl⟩ : syracuseStep 649205 = 60863) (by norm_num)
theorem B927733 : Blo 432776 927733 := bbase (se 5 (by rfl) ⟨43487, by rfl⟩ : syracuseStep 927733 = 86975) (by norm_num)
theorem B550901 : Blo 432776 550901 := bbase (se 5 (by rfl) ⟨25823, by rfl⟩ : syracuseStep 550901 = 51647) (by norm_num)
theorem B1468421 : Blo 432776 1468421 := bbase (se 4 (by rfl) ⟨137664, by rfl⟩ : syracuseStep 1468421 = 275329) (by norm_num)
theorem B649229 : Blo 432776 649229 := bbase (se 3 (by rfl) ⟨121730, by rfl⟩ : syracuseStep 649229 = 243461) (by norm_num)
theorem B649253 : Blo 432776 649253 := bbase (se 4 (by rfl) ⟨60867, by rfl⟩ : syracuseStep 649253 = 121735) (by norm_num)
theorem B731173 : Blo 432776 731173 := bbase (se 4 (by rfl) ⟨68547, by rfl⟩ : syracuseStep 731173 = 137095) (by norm_num)
theorem B550957 : Blo 432776 550957 := bbase (se 3 (by rfl) ⟨103304, by rfl⟩ : syracuseStep 550957 = 206609) (by norm_num)
theorem B616501 : Blo 432776 616501 := bbase (se 5 (by rfl) ⟨28898, by rfl⟩ : syracuseStep 616501 = 57797) (by norm_num)
theorem B976949 : Blo 432776 976949 := bbase (se 5 (by rfl) ⟨45794, by rfl⟩ : syracuseStep 976949 = 91589) (by norm_num)
theorem B649277 : Blo 432776 649277 := bbase (se 3 (by rfl) ⟨121739, by rfl⟩ : syracuseStep 649277 = 243479) (by norm_num)
theorem B649301 : Blo 432776 649301 := bbase (se 8 (by rfl) ⟨3804, by rfl⟩ : syracuseStep 649301 = 7609) (by norm_num)
theorem B649325 : Blo 432776 649325 := bbase (se 3 (by rfl) ⟨121748, by rfl⟩ : syracuseStep 649325 = 243497) (by norm_num)
theorem B878701 : Blo 432776 878701 := bbase (se 3 (by rfl) ⟨164756, by rfl⟩ : syracuseStep 878701 = 329513) (by norm_num)
theorem B624757 : Blo 432776 624757 := bbase (se 5 (by rfl) ⟨29285, by rfl⟩ : syracuseStep 624757 = 58571) (by norm_num)
theorem B731261 : Blo 432776 731261 := bbase (se 3 (by rfl) ⟨137111, by rfl⟩ : syracuseStep 731261 = 274223) (by norm_num)
theorem B977021 : Blo 432776 977021 := bbase (se 3 (by rfl) ⟨183191, by rfl⟩ : syracuseStep 977021 = 366383) (by norm_num)
theorem B649349 : Blo 432776 649349 := bbase (se 4 (by rfl) ⟨60876, by rfl⟩ : syracuseStep 649349 = 121753) (by norm_num)
theorem B551053 : Blo 432776 551053 := bbase (se 3 (by rfl) ⟨103322, by rfl⟩ : syracuseStep 551053 = 206645) (by norm_num)
theorem B649373 : Blo 432776 649373 := bbase (se 3 (by rfl) ⟨121757, by rfl⟩ : syracuseStep 649373 = 243515) (by norm_num)
theorem B649397 : Blo 432776 649397 := bbase (se 5 (by rfl) ⟨30440, by rfl⟩ : syracuseStep 649397 = 60881) (by norm_num)
theorem B1411253 : Blo 432776 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B977093 : Blo 432776 977093 := bbase (se 4 (by rfl) ⟨91602, by rfl⟩ : syracuseStep 977093 = 183205) (by norm_num)
theorem B649421 : Blo 432776 649421 := bbase (se 3 (by rfl) ⟨121766, by rfl⟩ : syracuseStep 649421 = 243533) (by norm_num)
theorem B649445 : Blo 432776 649445 := bbase (se 4 (by rfl) ⟨60885, by rfl⟩ : syracuseStep 649445 = 121771) (by norm_num)
theorem B2476277 : Blo 432776 2476277 := bbase (se 5 (by rfl) ⟨116075, by rfl⟩ : syracuseStep 2476277 = 232151) (by norm_num)
theorem B649469 : Blo 432776 649469 := bbase (se 3 (by rfl) ⟨121775, by rfl⟩ : syracuseStep 649469 = 243551) (by norm_num)
theorem B731389 : Blo 432776 731389 := bbase (se 3 (by rfl) ⟨137135, by rfl⟩ : syracuseStep 731389 = 274271) (by norm_num)
theorem B977165 : Blo 432776 977165 := bbase (se 3 (by rfl) ⟨183218, by rfl⟩ : syracuseStep 977165 = 366437) (by norm_num)
theorem B649493 : Blo 432776 649493 := bbase (se 6 (by rfl) ⟨15222, by rfl⟩ : syracuseStep 649493 = 30445) (by norm_num)
theorem B2787605 : Blo 432776 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B3352853 : Blo 432776 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B1173797 : Blo 432776 1173797 := bbase (se 4 (by rfl) ⟨110043, by rfl⟩ : syracuseStep 1173797 = 220087) (by norm_num)
theorem B649517 : Blo 432776 649517 := bbase (se 3 (by rfl) ⟨121784, by rfl⟩ : syracuseStep 649517 = 243569) (by norm_num)
theorem B551225 : Blo 432776 551225 := bbase (se 2 (by rfl) ⟨206709, by rfl⟩ : syracuseStep 551225 = 413419) (by norm_num)
theorem B1386821 : Blo 432776 1386821 := bbase (se 4 (by rfl) ⟨130014, by rfl⟩ : syracuseStep 1386821 = 260029) (by norm_num)
theorem B649541 : Blo 432776 649541 := bbase (se 4 (by rfl) ⟨60894, by rfl⟩ : syracuseStep 649541 = 121789) (by norm_num)
theorem B1100101 : Blo 432776 1100101 := bbase (se 4 (by rfl) ⟨103134, by rfl⟩ : syracuseStep 1100101 = 206269) (by norm_num)
theorem B1059149 : Blo 432776 1059149 := bbase (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) (by norm_num)
theorem B731477 : Blo 432776 731477 := bbase (se 10 (by rfl) ⟨1071, by rfl⟩ : syracuseStep 731477 = 2143) (by norm_num)
theorem B9382229 : Blo 432776 9382229 := bbase (se 10 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 9382229 = 27487) (by norm_num)
theorem B977237 : Blo 432776 977237 := bbase (se 10 (by rfl) ⟨1431, by rfl⟩ : syracuseStep 977237 = 2863) (by norm_num)
theorem B649565 : Blo 432776 649565 := bbase (se 3 (by rfl) ⟨121793, by rfl⟩ : syracuseStep 649565 = 243587) (by norm_num)
theorem B551281 : Blo 432776 551281 := bbase (se 2 (by rfl) ⟨206730, by rfl⟩ : syracuseStep 551281 = 413461) (by norm_num)
theorem B649589 : Blo 432776 649589 := bbase (se 5 (by rfl) ⟨30449, by rfl⟩ : syracuseStep 649589 = 60899) (by norm_num)
theorem B4163957 : Blo 432776 4163957 := bbase (se 5 (by rfl) ⟨195185, by rfl⟩ : syracuseStep 4163957 = 390371) (by norm_num)
theorem B616837 : Blo 432776 616837 := bbase (se 4 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 616837 = 115657) (by norm_num)
theorem B649613 : Blo 432776 649613 := bbase (se 3 (by rfl) ⟨121802, by rfl⟩ : syracuseStep 649613 = 243605) (by norm_num)
theorem B977309 : Blo 432776 977309 := bbase (se 3 (by rfl) ⟨183245, by rfl⟩ : syracuseStep 977309 = 366491) (by norm_num)
theorem B1460645 : Blo 432776 1460645 := bbase (se 4 (by rfl) ⟨136935, by rfl⟩ : syracuseStep 1460645 = 273871) (by norm_num)
theorem B649637 : Blo 432776 649637 := bbase (se 4 (by rfl) ⟨60903, by rfl⟩ : syracuseStep 649637 = 121807) (by norm_num)
theorem B1583525 : Blo 432776 1583525 := bbase (se 4 (by rfl) ⟨148455, by rfl⟩ : syracuseStep 1583525 = 296911) (by norm_num)
theorem B1321397 : Blo 432776 1321397 := bbase (se 5 (by rfl) ⟨61940, by rfl⟩ : syracuseStep 1321397 = 123881) (by norm_num)
theorem B1100213 : Blo 432776 1100213 := bbase (se 5 (by rfl) ⟨51572, by rfl⟩ : syracuseStep 1100213 = 103145) (by norm_num)
theorem B1468853 : Blo 432776 1468853 := bbase (se 5 (by rfl) ⟨68852, by rfl⟩ : syracuseStep 1468853 = 137705) (by norm_num)
theorem B649661 : Blo 432776 649661 := bbase (se 3 (by rfl) ⟨121811, by rfl⟩ : syracuseStep 649661 = 243623) (by norm_num)
theorem B649685 : Blo 432776 649685 := bbase (se 7 (by rfl) ⟨7613, by rfl⟩ : syracuseStep 649685 = 15227) (by norm_num)
theorem B731605 : Blo 432776 731605 := bbase (se 7 (by rfl) ⟨8573, by rfl⟩ : syracuseStep 731605 = 17147) (by norm_num)
theorem B551377 : Blo 432776 551377 := bbase (se 2 (by rfl) ⟨206766, by rfl⟩ : syracuseStep 551377 = 413533) (by norm_num)
theorem B977381 : Blo 432776 977381 := bbase (se 4 (by rfl) ⟨91629, by rfl⟩ : syracuseStep 977381 = 183259) (by norm_num)
theorem B649709 : Blo 432776 649709 := bbase (se 3 (by rfl) ⟨121820, by rfl⟩ : syracuseStep 649709 = 243641) (by norm_num)
theorem B821765 : Blo 432776 821765 := bbase (se 4 (by rfl) ⟨77040, by rfl⟩ : syracuseStep 821765 = 154081) (by norm_num)
theorem B649733 : Blo 432776 649733 := bbase (se 4 (by rfl) ⟨60912, by rfl⟩ : syracuseStep 649733 = 121825) (by norm_num)
theorem B649757 : Blo 432776 649757 := bbase (se 3 (by rfl) ⟨121829, by rfl⟩ : syracuseStep 649757 = 243659) (by norm_num)
theorem B731693 : Blo 432776 731693 := bbase (se 3 (by rfl) ⟨137192, by rfl⟩ : syracuseStep 731693 = 274385) (by norm_num)
theorem B977453 : Blo 432776 977453 := bbase (se 3 (by rfl) ⟨183272, by rfl⟩ : syracuseStep 977453 = 366545) (by norm_num)
theorem B649781 : Blo 432776 649781 := bbase (se 5 (by rfl) ⟨30458, by rfl⟩ : syracuseStep 649781 = 60917) (by norm_num)
theorem B649805 : Blo 432776 649805 := bbase (se 3 (by rfl) ⟨121838, by rfl⟩ : syracuseStep 649805 = 243677) (by norm_num)
theorem B617053 : Blo 432776 617053 := bbase (se 3 (by rfl) ⟨115697, by rfl⟩ : syracuseStep 617053 = 231395) (by norm_num)
theorem B649829 : Blo 432776 649829 := bbase (se 4 (by rfl) ⟨60921, by rfl⟩ : syracuseStep 649829 = 121843) (by norm_num)
theorem B977525 : Blo 432776 977525 := bbase (se 5 (by rfl) ⟨45821, by rfl⟩ : syracuseStep 977525 = 91643) (by norm_num)
theorem B1100405 : Blo 432776 1100405 := bbase (se 5 (by rfl) ⟨51581, by rfl⟩ : syracuseStep 1100405 = 103163) (by norm_num)
theorem B649853 : Blo 432776 649853 := bbase (se 3 (by rfl) ⟨121847, by rfl⟩ : syracuseStep 649853 = 243695) (by norm_num)
theorem B649877 : Blo 432776 649877 := bbase (se 6 (by rfl) ⟨15231, by rfl⟩ : syracuseStep 649877 = 30463) (by norm_num)
theorem B2083477 : Blo 432776 2083477 := bbase (se 6 (by rfl) ⟨48831, by rfl⟩ : syracuseStep 2083477 = 97663) (by norm_num)
theorem B821917 : Blo 432776 821917 := bbase (se 3 (by rfl) ⟨154109, by rfl⟩ : syracuseStep 821917 = 308219) (by norm_num)
theorem B649901 : Blo 432776 649901 := bbase (se 3 (by rfl) ⟨121856, by rfl⟩ : syracuseStep 649901 = 243713) (by norm_num)
theorem B731821 : Blo 432776 731821 := bbase (se 3 (by rfl) ⟨137216, by rfl⟩ : syracuseStep 731821 = 274433) (by norm_num)
theorem B469693 : Blo 432776 469693 := bbase (se 3 (by rfl) ⟨88067, by rfl⟩ : syracuseStep 469693 = 176135) (by norm_num)
theorem B977597 : Blo 432776 977597 := bbase (se 3 (by rfl) ⟨183299, by rfl⟩ : syracuseStep 977597 = 366599) (by norm_num)
theorem B649925 : Blo 432776 649925 := bbase (se 4 (by rfl) ⟨60930, by rfl⟩ : syracuseStep 649925 = 121861) (by norm_num)
theorem B649949 : Blo 432776 649949 := bbase (se 3 (by rfl) ⟨121865, by rfl⟩ : syracuseStep 649949 = 243731) (by norm_num)
theorem B3697397 : Blo 432776 3697397 := bbase (se 5 (by rfl) ⟨173315, by rfl⟩ : syracuseStep 3697397 = 346631) (by norm_num)
theorem B649973 : Blo 432776 649973 := bbase (se 5 (by rfl) ⟨30467, by rfl⟩ : syracuseStep 649973 = 60935) (by norm_num)
theorem B731909 : Blo 432776 731909 := bbase (se 4 (by rfl) ⟨68616, by rfl⟩ : syracuseStep 731909 = 137233) (by norm_num)
theorem B977669 : Blo 432776 977669 := bbase (se 4 (by rfl) ⟨91656, by rfl⟩ : syracuseStep 977669 = 183313) (by norm_num)
theorem B649997 : Blo 432776 649997 := bbase (se 3 (by rfl) ⟨121874, by rfl⟩ : syracuseStep 649997 = 243749) (by norm_num)
theorem B527129 : Blo 432776 527129 := bbase (se 2 (by rfl) ⟨197673, by rfl⟩ : syracuseStep 527129 = 395347) (by norm_num)
theorem B650021 : Blo 432776 650021 := bbase (se 4 (by rfl) ⟨60939, by rfl⟩ : syracuseStep 650021 = 121879) (by norm_num)
theorem B650045 : Blo 432776 650045 := bbase (se 3 (by rfl) ⟨121883, by rfl⟩ : syracuseStep 650045 = 243767) (by norm_num)
theorem B879421 : Blo 432776 879421 := bbase (se 3 (by rfl) ⟨164891, by rfl⟩ : syracuseStep 879421 = 329783) (by norm_num)
theorem B658253 : Blo 432776 658253 := bbase (se 3 (by rfl) ⟨123422, by rfl⟩ : syracuseStep 658253 = 246845) (by norm_num)
theorem B977741 : Blo 432776 977741 := bbase (se 3 (by rfl) ⟨183326, by rfl⟩ : syracuseStep 977741 = 366653) (by norm_num)
theorem B1461077 : Blo 432776 1461077 := bbase (se 9 (by rfl) ⟨4280, by rfl⟩ : syracuseStep 1461077 = 8561) (by norm_num)
theorem B1755989 : Blo 432776 1755989 := bbase (se 9 (by rfl) ⟨5144, by rfl⟩ : syracuseStep 1755989 = 10289) (by norm_num)
theorem B650069 : Blo 432776 650069 := bbase (se 9 (by rfl) ⟨1904, by rfl⟩ : syracuseStep 650069 = 3809) (by norm_num)
theorem B1239893 : Blo 432776 1239893 := bbase (se 9 (by rfl) ⟨3632, by rfl⟩ : syracuseStep 1239893 = 7265) (by norm_num)
theorem B1469285 : Blo 432776 1469285 := bbase (se 4 (by rfl) ⟨137745, by rfl⟩ : syracuseStep 1469285 = 275491) (by norm_num)
theorem B650093 : Blo 432776 650093 := bbase (se 3 (by rfl) ⟨121892, by rfl⟩ : syracuseStep 650093 = 243785) (by norm_num)
theorem B928621 : Blo 432776 928621 := bbase (se 3 (by rfl) ⟨174116, by rfl⟩ : syracuseStep 928621 = 348233) (by norm_num)
theorem B2116469 : Blo 432776 2116469 := bbase (se 5 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 2116469 = 198419) (by norm_num)
theorem B650117 : Blo 432776 650117 := bbase (se 4 (by rfl) ⟨60948, by rfl⟩ : syracuseStep 650117 = 121897) (by norm_num)
theorem B732037 : Blo 432776 732037 := bbase (se 4 (by rfl) ⟨68628, by rfl⟩ : syracuseStep 732037 = 137257) (by norm_num)
theorem B977813 : Blo 432776 977813 := bbase (se 6 (by rfl) ⟨22917, by rfl⟩ : syracuseStep 977813 = 45835) (by norm_num)
theorem B650141 : Blo 432776 650141 := bbase (se 3 (by rfl) ⟨121901, by rfl⟩ : syracuseStep 650141 = 243803) (by norm_num)
theorem B650165 : Blo 432776 650165 := bbase (se 5 (by rfl) ⟨30476, by rfl⟩ : syracuseStep 650165 = 60953) (by norm_num)
theorem B1567669 : Blo 432776 1567669 := bbase (se 5 (by rfl) ⟨73484, by rfl⟩ : syracuseStep 1567669 = 146969) (by norm_num)
theorem B1649605 : Blo 432776 1649605 := bbase (se 4 (by rfl) ⟨154650, by rfl⟩ : syracuseStep 1649605 = 309301) (by norm_num)
theorem B822221 : Blo 432776 822221 := bbase (se 3 (by rfl) ⟨154166, by rfl⟩ : syracuseStep 822221 = 308333) (by norm_num)
theorem B650189 : Blo 432776 650189 := bbase (se 3 (by rfl) ⟨121910, by rfl⟩ : syracuseStep 650189 = 243821) (by norm_num)
theorem B1100749 : Blo 432776 1100749 := bbase (se 3 (by rfl) ⟨206390, by rfl⟩ : syracuseStep 1100749 = 412781) (by norm_num)
theorem B617429 : Blo 432776 617429 := bbase (se 7 (by rfl) ⟨7235, by rfl⟩ : syracuseStep 617429 = 14471) (by norm_num)
theorem B732125 : Blo 432776 732125 := bbase (se 3 (by rfl) ⟨137273, by rfl⟩ : syracuseStep 732125 = 274547) (by norm_num)
theorem B977885 : Blo 432776 977885 := bbase (se 3 (by rfl) ⟨183353, by rfl⟩ : syracuseStep 977885 = 366707) (by norm_num)
theorem B650213 : Blo 432776 650213 := bbase (se 4 (by rfl) ⟨60957, by rfl⟩ : syracuseStep 650213 = 121915) (by norm_num)
theorem B2198501 : Blo 432776 2198501 := bbase (se 4 (by rfl) ⟨206109, by rfl⟩ : syracuseStep 2198501 = 412219) (by norm_num)
theorem B928741 : Blo 432776 928741 := bbase (se 4 (by rfl) ⟨87069, by rfl⟩ : syracuseStep 928741 = 174139) (by norm_num)
theorem B1395701 : Blo 432776 1395701 := bbase (se 5 (by rfl) ⟨65423, by rfl⟩ : syracuseStep 1395701 = 130847) (by norm_num)
theorem B650237 : Blo 432776 650237 := bbase (se 3 (by rfl) ⟨121919, by rfl⟩ : syracuseStep 650237 = 243839) (by norm_num)
theorem B650261 : Blo 432776 650261 := bbase (se 6 (by rfl) ⟨15240, by rfl⟩ : syracuseStep 650261 = 30481) (by norm_num)
theorem B977957 : Blo 432776 977957 := bbase (se 4 (by rfl) ⟨91683, by rfl⟩ : syracuseStep 977957 = 183367) (by norm_num)
theorem B650285 : Blo 432776 650285 := bbase (se 3 (by rfl) ⟨121928, by rfl⟩ : syracuseStep 650285 = 243857) (by norm_num)
theorem B1100861 : Blo 432776 1100861 := bbase (se 3 (by rfl) ⟨206411, by rfl⟩ : syracuseStep 1100861 = 412823) (by norm_num)
theorem B650309 : Blo 432776 650309 := bbase (se 4 (by rfl) ⟨60966, by rfl⟩ : syracuseStep 650309 = 121933) (by norm_num)
theorem B1567829 : Blo 432776 1567829 := bbase (se 8 (by rfl) ⟨9186, by rfl⟩ : syracuseStep 1567829 = 18373) (by norm_num)
theorem B650333 : Blo 432776 650333 := bbase (se 3 (by rfl) ⟨121937, by rfl⟩ : syracuseStep 650333 = 243875) (by norm_num)
theorem B732253 : Blo 432776 732253 := bbase (se 3 (by rfl) ⟨137297, by rfl⟩ : syracuseStep 732253 = 274595) (by norm_num)
theorem B978029 : Blo 432776 978029 := bbase (se 3 (by rfl) ⟨183380, by rfl⟩ : syracuseStep 978029 = 366761) (by norm_num)
theorem B650357 : Blo 432776 650357 := bbase (se 5 (by rfl) ⟨30485, by rfl⟩ : syracuseStep 650357 = 60971) (by norm_num)
theorem B650381 : Blo 432776 650381 := bbase (se 3 (by rfl) ⟨121946, by rfl⟩ : syracuseStep 650381 = 243893) (by norm_num)
theorem B650405 : Blo 432776 650405 := bbase (se 4 (by rfl) ⟨60975, by rfl⟩ : syracuseStep 650405 = 121951) (by norm_num)
theorem B732341 : Blo 432776 732341 := bbase (se 5 (by rfl) ⟨34328, by rfl⟩ : syracuseStep 732341 = 68657) (by norm_num)
theorem B978101 : Blo 432776 978101 := bbase (se 5 (by rfl) ⟨45848, by rfl⟩ : syracuseStep 978101 = 91697) (by norm_num)
theorem B650429 : Blo 432776 650429 := bbase (se 3 (by rfl) ⟨121955, by rfl⟩ : syracuseStep 650429 = 243911) (by norm_num)
theorem B650453 : Blo 432776 650453 := bbase (se 7 (by rfl) ⟨7622, by rfl⟩ : syracuseStep 650453 = 15245) (by norm_num)
theorem B928997 : Blo 432776 928997 := bbase (se 4 (by rfl) ⟨87093, by rfl⟩ : syracuseStep 928997 = 174187) (by norm_num)
theorem B650477 : Blo 432776 650477 := bbase (se 3 (by rfl) ⟨121964, by rfl⟩ : syracuseStep 650477 = 243929) (by norm_num)
theorem B1649909 : Blo 432776 1649909 := bbase (se 5 (by rfl) ⟨77339, by rfl⟩ : syracuseStep 1649909 = 154679) (by norm_num)
theorem B879869 : Blo 432776 879869 := bbase (se 3 (by rfl) ⟨164975, by rfl⟩ : syracuseStep 879869 = 329951) (by norm_num)
theorem B978173 : Blo 432776 978173 := bbase (se 3 (by rfl) ⟨183407, by rfl⟩ : syracuseStep 978173 = 366815) (by norm_num)
theorem B1101053 : Blo 432776 1101053 := bbase (se 3 (by rfl) ⟨206447, by rfl⟩ : syracuseStep 1101053 = 412895) (by norm_num)
theorem B1461509 : Blo 432776 1461509 := bbase (se 4 (by rfl) ⟨137016, by rfl⟩ : syracuseStep 1461509 = 274033) (by norm_num)
theorem B650501 : Blo 432776 650501 := bbase (se 4 (by rfl) ⟨60984, by rfl⟩ : syracuseStep 650501 = 121969) (by norm_num)
theorem B642325 : Blo 432776 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B1469717 : Blo 432776 1469717 := bbase (se 6 (by rfl) ⟨34446, by rfl⟩ : syracuseStep 1469717 = 68893) (by norm_num)
theorem B650525 : Blo 432776 650525 := bbase (se 3 (by rfl) ⟨121973, by rfl⟩ : syracuseStep 650525 = 243947) (by norm_num)
theorem B650549 : Blo 432776 650549 := bbase (se 5 (by rfl) ⟨30494, by rfl⟩ : syracuseStep 650549 = 60989) (by norm_num)
theorem B732469 : Blo 432776 732469 := bbase (se 5 (by rfl) ⟨34334, by rfl⟩ : syracuseStep 732469 = 68669) (by norm_num)
theorem B978245 : Blo 432776 978245 := bbase (se 4 (by rfl) ⟨91710, by rfl⟩ : syracuseStep 978245 = 183421) (by norm_num)
theorem B650573 : Blo 432776 650573 := bbase (se 3 (by rfl) ⟨121982, by rfl⟩ : syracuseStep 650573 = 243965) (by norm_num)
theorem B650597 : Blo 432776 650597 := bbase (se 4 (by rfl) ⟨60993, by rfl⟩ : syracuseStep 650597 = 121987) (by norm_num)
theorem B716149 : Blo 432776 716149 := bbase (se 5 (by rfl) ⟨33569, by rfl⟩ : syracuseStep 716149 = 67139) (by norm_num)
theorem B650621 : Blo 432776 650621 := bbase (se 3 (by rfl) ⟨121991, by rfl⟩ : syracuseStep 650621 = 243983) (by norm_num)
theorem B732557 : Blo 432776 732557 := bbase (se 3 (by rfl) ⟨137354, by rfl⟩ : syracuseStep 732557 = 274709) (by norm_num)
theorem B978317 : Blo 432776 978317 := bbase (se 3 (by rfl) ⟨183434, by rfl⟩ : syracuseStep 978317 = 366869) (by norm_num)
theorem B650645 : Blo 432776 650645 := bbase (se 6 (by rfl) ⟨15249, by rfl⟩ : syracuseStep 650645 = 30499) (by norm_num)
theorem B650669 : Blo 432776 650669 := bbase (se 3 (by rfl) ⟨122000, by rfl⟩ : syracuseStep 650669 = 244001) (by norm_num)
theorem B1068485 : Blo 432776 1068485 := bbase (se 4 (by rfl) ⟨100170, by rfl⟩ : syracuseStep 1068485 = 200341) (by norm_num)
theorem B585157 : Blo 432776 585157 := bbase (se 4 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 585157 = 109717) (by norm_num)
theorem B2223557 : Blo 432776 2223557 := bbase (se 4 (by rfl) ⟨208458, by rfl⟩ : syracuseStep 2223557 = 416917) (by norm_num)
theorem B650693 : Blo 432776 650693 := bbase (se 4 (by rfl) ⟨61002, by rfl⟩ : syracuseStep 650693 = 122005) (by norm_num)
theorem B978389 : Blo 432776 978389 := bbase (se 7 (by rfl) ⟨11465, by rfl⟩ : syracuseStep 978389 = 22931) (by norm_num)
theorem B486877 : Blo 432776 486877 := bbase (se 3 (by rfl) ⟨91289, by rfl⟩ : syracuseStep 486877 = 182579) (by norm_num)
theorem B650717 : Blo 432776 650717 := bbase (se 3 (by rfl) ⟨122009, by rfl⟩ : syracuseStep 650717 = 244019) (by norm_num)
theorem B650741 : Blo 432776 650741 := bbase (se 5 (by rfl) ⟨30503, by rfl⟩ : syracuseStep 650741 = 61007) (by norm_num)
theorem B486913 : Blo 432776 486913 := bbase (se 2 (by rfl) ⟨182592, by rfl⟩ : syracuseStep 486913 = 365185) (by norm_num)
theorem B2092549 : Blo 432776 2092549 := bbase (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) (by norm_num)
theorem B650765 : Blo 432776 650765 := bbase (se 3 (by rfl) ⟨122018, by rfl⟩ : syracuseStep 650765 = 244037) (by norm_num)
theorem B732685 : Blo 432776 732685 := bbase (se 3 (by rfl) ⟨137378, by rfl⟩ : syracuseStep 732685 = 274757) (by norm_num)
theorem B978461 : Blo 432776 978461 := bbase (se 3 (by rfl) ⟨183461, by rfl⟩ : syracuseStep 978461 = 366923) (by norm_num)
theorem B486949 : Blo 432776 486949 := bbase (se 4 (by rfl) ⟨45651, by rfl⟩ : syracuseStep 486949 = 91303) (by norm_num)
theorem B650789 : Blo 432776 650789 := bbase (se 4 (by rfl) ⟨61011, by rfl⟩ : syracuseStep 650789 = 122023) (by norm_num)
theorem B847397 : Blo 432776 847397 := bbase (se 4 (by rfl) ⟨79443, by rfl⟩ : syracuseStep 847397 = 158887) (by norm_num)
theorem B495145 : Blo 432776 495145 := bbase (se 2 (by rfl) ⟨185679, by rfl⟩ : syracuseStep 495145 = 371359) (by norm_num)
theorem B4574773 : Blo 432776 4574773 := bbase (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) (by norm_num)
theorem B462397 : Blo 432776 462397 := bbase (se 3 (by rfl) ⟨86699, by rfl⟩ : syracuseStep 462397 = 173399) (by norm_num)
theorem B650813 : Blo 432776 650813 := bbase (se 3 (by rfl) ⟨122027, by rfl⟩ : syracuseStep 650813 = 244055) (by norm_num)
theorem B486985 : Blo 432776 486985 := bbase (se 2 (by rfl) ⟨182619, by rfl⟩ : syracuseStep 486985 = 365239) (by norm_num)
theorem B650837 : Blo 432776 650837 := bbase (se 8 (by rfl) ⟨3813, by rfl⟩ : syracuseStep 650837 = 7627) (by norm_num)
theorem B1101397 : Blo 432776 1101397 := bbase (se 8 (by rfl) ⟨6453, by rfl⟩ : syracuseStep 1101397 = 12907) (by norm_num)
theorem B732773 : Blo 432776 732773 := bbase (se 4 (by rfl) ⟨68697, by rfl⟩ : syracuseStep 732773 = 137395) (by norm_num)
theorem B978533 : Blo 432776 978533 := bbase (se 4 (by rfl) ⟨91737, by rfl⟩ : syracuseStep 978533 = 183475) (by norm_num)
theorem B487021 : Blo 432776 487021 := bbase (se 3 (by rfl) ⟨91316, by rfl⟩ : syracuseStep 487021 = 182633) (by norm_num)
theorem B650861 : Blo 432776 650861 := bbase (se 3 (by rfl) ⟨122036, by rfl⟩ : syracuseStep 650861 = 244073) (by norm_num)
theorem B781933 : Blo 432776 781933 := bbase (se 3 (by rfl) ⟨146612, by rfl⟩ : syracuseStep 781933 = 293225) (by norm_num)
theorem B462457 : Blo 432776 462457 := bbase (se 2 (by rfl) ⟨173421, by rfl⟩ : syracuseStep 462457 = 346843) (by norm_num)
theorem B650885 : Blo 432776 650885 := bbase (se 4 (by rfl) ⟨61020, by rfl⟩ : syracuseStep 650885 = 122041) (by norm_num)
theorem B487057 : Blo 432776 487057 := bbase (se 2 (by rfl) ⟨182646, by rfl⟩ : syracuseStep 487057 = 365293) (by norm_num)
theorem B1068701 : Blo 432776 1068701 := bbase (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) (by norm_num)
theorem B650909 : Blo 432776 650909 := bbase (se 3 (by rfl) ⟨122045, by rfl⟩ : syracuseStep 650909 = 244091) (by norm_num)
theorem B1502885 : Blo 432776 1502885 := bbase (se 4 (by rfl) ⟨140895, by rfl⟩ : syracuseStep 1502885 = 281791) (by norm_num)
theorem B2117285 : Blo 432776 2117285 := bbase (se 4 (by rfl) ⟨198495, by rfl⟩ : syracuseStep 2117285 = 396991) (by norm_num)
theorem B978605 : Blo 432776 978605 := bbase (se 3 (by rfl) ⟨183488, by rfl⟩ : syracuseStep 978605 = 366977) (by norm_num)
theorem B487093 : Blo 432776 487093 := bbase (se 5 (by rfl) ⟨22832, by rfl⟩ : syracuseStep 487093 = 45665) (by norm_num)
theorem B1461941 : Blo 432776 1461941 := bbase (se 5 (by rfl) ⟨68528, by rfl⟩ : syracuseStep 1461941 = 137057) (by norm_num)
theorem B650933 : Blo 432776 650933 := bbase (se 5 (by rfl) ⟨30512, by rfl⟩ : syracuseStep 650933 = 61025) (by norm_num)
theorem B822973 : Blo 432776 822973 := bbase (se 3 (by rfl) ⟨154307, by rfl⟩ : syracuseStep 822973 = 308615) (by norm_num)
theorem B659141 : Blo 432776 659141 := bbase (se 4 (by rfl) ⟨61794, by rfl⟩ : syracuseStep 659141 = 123589) (by norm_num)
theorem B1101509 : Blo 432776 1101509 := bbase (se 4 (by rfl) ⟨103266, by rfl⟩ : syracuseStep 1101509 = 206533) (by norm_num)
theorem B1470149 : Blo 432776 1470149 := bbase (se 4 (by rfl) ⟨137826, by rfl⟩ : syracuseStep 1470149 = 275653) (by norm_num)
theorem B650957 : Blo 432776 650957 := bbase (se 3 (by rfl) ⟨122054, by rfl⟩ : syracuseStep 650957 = 244109) (by norm_num)
theorem B487129 : Blo 432776 487129 := bbase (se 2 (by rfl) ⟨182673, by rfl⟩ : syracuseStep 487129 = 365347) (by norm_num)
theorem B650981 : Blo 432776 650981 := bbase (se 4 (by rfl) ⟨61029, by rfl⟩ : syracuseStep 650981 = 122059) (by norm_num)
theorem B732901 : Blo 432776 732901 := bbase (se 4 (by rfl) ⟨68709, by rfl⟩ : syracuseStep 732901 = 137419) (by norm_num)
theorem B978677 : Blo 432776 978677 := bbase (se 5 (by rfl) ⟨45875, by rfl⟩ : syracuseStep 978677 = 91751) (by norm_num)
theorem B487165 : Blo 432776 487165 := bbase (se 3 (by rfl) ⟨91343, by rfl⟩ : syracuseStep 487165 = 182687) (by norm_num)
theorem B651005 : Blo 432776 651005 := bbase (se 3 (by rfl) ⟨122063, by rfl⟩ : syracuseStep 651005 = 244127) (by norm_num)
theorem B651029 : Blo 432776 651029 := bbase (se 6 (by rfl) ⟨15258, by rfl⟩ : syracuseStep 651029 = 30517) (by norm_num)
theorem B487201 : Blo 432776 487201 := bbase (se 2 (by rfl) ⟨182700, by rfl⟩ : syracuseStep 487201 = 365401) (by norm_num)
theorem B651053 : Blo 432776 651053 := bbase (se 3 (by rfl) ⟨122072, by rfl⟩ : syracuseStep 651053 = 244145) (by norm_num)
theorem B519985 : Blo 432776 519985 := bbase (se 2 (by rfl) ⟨194994, by rfl⟩ : syracuseStep 519985 = 389989) (by norm_num)
theorem B732989 : Blo 432776 732989 := bbase (se 3 (by rfl) ⟨137435, by rfl⟩ : syracuseStep 732989 = 274871) (by norm_num)
theorem B978749 : Blo 432776 978749 := bbase (se 3 (by rfl) ⟨183515, by rfl⟩ : syracuseStep 978749 = 367031) (by norm_num)
theorem B487237 : Blo 432776 487237 := bbase (se 4 (by rfl) ⟨45678, by rfl⟩ : syracuseStep 487237 = 91357) (by norm_num)
theorem B651077 : Blo 432776 651077 := bbase (se 4 (by rfl) ⟨61038, by rfl⟩ : syracuseStep 651077 = 122077) (by norm_num)
theorem B823117 : Blo 432776 823117 := bbase (se 3 (by rfl) ⟨154334, by rfl⟩ : syracuseStep 823117 = 308669) (by norm_num)
theorem B2649941 : Blo 432776 2649941 := bbase (se 9 (by rfl) ⟨7763, by rfl⟩ : syracuseStep 2649941 = 15527) (by norm_num)
theorem B651101 : Blo 432776 651101 := bbase (se 3 (by rfl) ⟨122081, by rfl⟩ : syracuseStep 651101 = 244163) (by norm_num)
theorem B487273 : Blo 432776 487273 := bbase (se 2 (by rfl) ⟨182727, by rfl⟩ : syracuseStep 487273 = 365455) (by norm_num)
theorem B651125 : Blo 432776 651125 := bbase (se 5 (by rfl) ⟨30521, by rfl⟩ : syracuseStep 651125 = 61043) (by norm_num)
theorem B1118069 : Blo 432776 1118069 := bbase (se 5 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 1118069 = 104819) (by norm_num)
theorem B978821 : Blo 432776 978821 := bbase (se 4 (by rfl) ⟨91764, by rfl⟩ : syracuseStep 978821 = 183529) (by norm_num)
theorem B1101701 : Blo 432776 1101701 := bbase (se 4 (by rfl) ⟨103284, by rfl⟩ : syracuseStep 1101701 = 206569) (by norm_num)
theorem B487309 : Blo 432776 487309 := bbase (se 3 (by rfl) ⟨91370, by rfl⟩ : syracuseStep 487309 = 182741) (by norm_num)
theorem B651149 : Blo 432776 651149 := bbase (se 3 (by rfl) ⟨122090, by rfl⟩ : syracuseStep 651149 = 244181) (by norm_num)
theorem B1044373 : Blo 432776 1044373 := bbase (se 6 (by rfl) ⟨24477, by rfl⟩ : syracuseStep 1044373 = 48955) (by norm_num)
theorem B651173 : Blo 432776 651173 := bbase (se 4 (by rfl) ⟨61047, by rfl⟩ : syracuseStep 651173 = 122095) (by norm_num)
theorem B487345 : Blo 432776 487345 := bbase (se 2 (by rfl) ⟨182754, by rfl⟩ : syracuseStep 487345 = 365509) (by norm_num)
theorem B462773 : Blo 432776 462773 := bbase (se 5 (by rfl) ⟨21692, by rfl⟩ : syracuseStep 462773 = 43385) (by norm_num)
theorem B651197 : Blo 432776 651197 := bbase (se 3 (by rfl) ⟨122099, by rfl⟩ : syracuseStep 651197 = 244199) (by norm_num)
theorem B733117 : Blo 432776 733117 := bbase (se 3 (by rfl) ⟨137459, by rfl⟩ : syracuseStep 733117 = 274919) (by norm_num)
theorem B978893 : Blo 432776 978893 := bbase (se 3 (by rfl) ⟨183542, by rfl⟩ : syracuseStep 978893 = 367085) (by norm_num)
theorem B487381 : Blo 432776 487381 := bbase (se 7 (by rfl) ⟨5711, by rfl⟩ : syracuseStep 487381 = 11423) (by norm_num)
theorem B651221 : Blo 432776 651221 := bbase (se 7 (by rfl) ⟨7631, by rfl⟩ : syracuseStep 651221 = 15263) (by norm_num)
theorem B823277 : Blo 432776 823277 := bbase (se 3 (by rfl) ⟨154364, by rfl⟩ : syracuseStep 823277 = 308729) (by norm_num)
theorem B651245 : Blo 432776 651245 := bbase (se 3 (by rfl) ⟨122108, by rfl⟩ : syracuseStep 651245 = 244217) (by norm_num)
theorem B487417 : Blo 432776 487417 := bbase (se 2 (by rfl) ⟨182781, by rfl⟩ : syracuseStep 487417 = 365563) (by norm_num)
theorem B651269 : Blo 432776 651269 := bbase (se 4 (by rfl) ⟨61056, by rfl⟩ : syracuseStep 651269 = 122113) (by norm_num)
theorem B733205 : Blo 432776 733205 := bbase (se 6 (by rfl) ⟨17184, by rfl⟩ : syracuseStep 733205 = 34369) (by norm_num)
theorem B978965 : Blo 432776 978965 := bbase (se 6 (by rfl) ⟨22944, by rfl⟩ : syracuseStep 978965 = 45889) (by norm_num)
theorem B487453 : Blo 432776 487453 := bbase (se 3 (by rfl) ⟨91397, by rfl⟩ : syracuseStep 487453 = 182795) (by norm_num)
theorem B651293 : Blo 432776 651293 := bbase (se 3 (by rfl) ⟨122117, by rfl⟩ : syracuseStep 651293 = 244235) (by norm_num)
theorem B495661 : Blo 432776 495661 := bbase (se 3 (by rfl) ⟨92936, by rfl⟩ : syracuseStep 495661 = 185873) (by norm_num)
theorem B651317 : Blo 432776 651317 := bbase (se 5 (by rfl) ⟨30530, by rfl⟩ : syracuseStep 651317 = 61061) (by norm_num)
theorem B487489 : Blo 432776 487489 := bbase (se 2 (by rfl) ⟨182808, by rfl⟩ : syracuseStep 487489 = 365617) (by norm_num)
theorem B651341 : Blo 432776 651341 := bbase (se 3 (by rfl) ⟨122126, by rfl⟩ : syracuseStep 651341 = 244253) (by norm_num)
theorem B979037 : Blo 432776 979037 := bbase (se 3 (by rfl) ⟨183569, by rfl⟩ : syracuseStep 979037 = 367139) (by norm_num)
theorem B929885 : Blo 432776 929885 := bbase (se 3 (by rfl) ⟨174353, by rfl⟩ : syracuseStep 929885 = 348707) (by norm_num)
theorem B1462373 : Blo 432776 1462373 := bbase (se 4 (by rfl) ⟨137097, by rfl⟩ : syracuseStep 1462373 = 274195) (by norm_num)
theorem B487525 : Blo 432776 487525 := bbase (se 4 (by rfl) ⟨45705, by rfl⟩ : syracuseStep 487525 = 91411) (by norm_num)
theorem B651365 : Blo 432776 651365 := bbase (se 4 (by rfl) ⟨61065, by rfl⟩ : syracuseStep 651365 = 122131) (by norm_num)
theorem B1323125 : Blo 432776 1323125 := bbase (se 5 (by rfl) ⟨62021, by rfl⟩ : syracuseStep 1323125 = 124043) (by norm_num)
theorem B1470581 : Blo 432776 1470581 := bbase (se 5 (by rfl) ⟨68933, by rfl⟩ : syracuseStep 1470581 = 137867) (by norm_num)
theorem B823421 : Blo 432776 823421 := bbase (se 3 (by rfl) ⟨154391, by rfl⟩ : syracuseStep 823421 = 308783) (by norm_num)
theorem B651389 : Blo 432776 651389 := bbase (se 3 (by rfl) ⟨122135, by rfl⟩ : syracuseStep 651389 = 244271) (by norm_num)
theorem B1388677 : Blo 432776 1388677 := bbase (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) (by norm_num)
theorem B487561 : Blo 432776 487561 := bbase (se 2 (by rfl) ⟨182835, by rfl⟩ : syracuseStep 487561 = 365671) (by norm_num)
theorem B651413 : Blo 432776 651413 := bbase (se 6 (by rfl) ⟨15267, by rfl⟩ : syracuseStep 651413 = 30535) (by norm_num)
theorem B733333 : Blo 432776 733333 := bbase (se 6 (by rfl) ⟨17187, by rfl⟩ : syracuseStep 733333 = 34375) (by norm_num)
theorem B979109 : Blo 432776 979109 := bbase (se 4 (by rfl) ⟨91791, by rfl⟩ : syracuseStep 979109 = 183583) (by norm_num)
theorem B487597 : Blo 432776 487597 := bbase (se 3 (by rfl) ⟨91424, by rfl⟩ : syracuseStep 487597 = 182849) (by norm_num)
theorem B651437 : Blo 432776 651437 := bbase (se 3 (by rfl) ⟨122144, by rfl⟩ : syracuseStep 651437 = 244289) (by norm_num)
theorem B651461 : Blo 432776 651461 := bbase (se 4 (by rfl) ⟨61074, by rfl⟩ : syracuseStep 651461 = 122149) (by norm_num)
theorem B487633 : Blo 432776 487633 := bbase (se 2 (by rfl) ⟨182862, by rfl⟩ : syracuseStep 487633 = 365725) (by norm_num)
theorem B651485 : Blo 432776 651485 := bbase (se 3 (by rfl) ⟨122153, by rfl⟩ : syracuseStep 651485 = 244307) (by norm_num)
theorem B1102045 : Blo 432776 1102045 := bbase (se 3 (by rfl) ⟨206633, by rfl⟩ : syracuseStep 1102045 = 413267) (by norm_num)
theorem B733421 : Blo 432776 733421 := bbase (se 3 (by rfl) ⟨137516, by rfl⟩ : syracuseStep 733421 = 275033) (by norm_num)
theorem B979181 : Blo 432776 979181 := bbase (se 3 (by rfl) ⟨183596, by rfl⟩ : syracuseStep 979181 = 367193) (by norm_num)
theorem B487669 : Blo 432776 487669 := bbase (se 5 (by rfl) ⟨22859, by rfl⟩ : syracuseStep 487669 = 45719) (by norm_num)
theorem B651509 : Blo 432776 651509 := bbase (se 5 (by rfl) ⟨30539, by rfl⟩ : syracuseStep 651509 = 61079) (by norm_num)
theorem B2199797 : Blo 432776 2199797 := bbase (se 5 (by rfl) ⟨103115, by rfl⟩ : syracuseStep 2199797 = 206231) (by norm_num)
theorem B651533 : Blo 432776 651533 := bbase (se 3 (by rfl) ⟨122162, by rfl⟩ : syracuseStep 651533 = 244325) (by norm_num)
theorem B487705 : Blo 432776 487705 := bbase (se 2 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 487705 = 365779) (by norm_num)
theorem B651557 : Blo 432776 651557 := bbase (se 4 (by rfl) ⟨61083, by rfl⟩ : syracuseStep 651557 = 122167) (by norm_num)
theorem B979253 : Blo 432776 979253 := bbase (se 5 (by rfl) ⟨45902, by rfl⟩ : syracuseStep 979253 = 91805) (by norm_num)
theorem B487741 : Blo 432776 487741 := bbase (se 3 (by rfl) ⟨91451, by rfl⟩ : syracuseStep 487741 = 182903) (by norm_num)
theorem B651581 : Blo 432776 651581 := bbase (se 3 (by rfl) ⟨122171, by rfl⟩ : syracuseStep 651581 = 244343) (by norm_num)
theorem B1102157 : Blo 432776 1102157 := bbase (se 3 (by rfl) ⟨206654, by rfl⟩ : syracuseStep 1102157 = 413309) (by norm_num)
theorem B930125 : Blo 432776 930125 := bbase (se 3 (by rfl) ⟨174398, by rfl⟩ : syracuseStep 930125 = 348797) (by norm_num)
theorem B651605 : Blo 432776 651605 := bbase (se 10 (by rfl) ⟨954, by rfl⟩ : syracuseStep 651605 = 1909) (by norm_num)
theorem B5566805 : Blo 432776 5566805 := bbase (se 10 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 5566805 = 16309) (by norm_num)
theorem B487777 : Blo 432776 487777 := bbase (se 2 (by rfl) ⟨182916, by rfl⟩ : syracuseStep 487777 = 365833) (by norm_num)
theorem B618853 : Blo 432776 618853 := bbase (se 4 (by rfl) ⟨58017, by rfl⟩ : syracuseStep 618853 = 116035) (by norm_num)
theorem B651629 : Blo 432776 651629 := bbase (se 3 (by rfl) ⟨122180, by rfl⟩ : syracuseStep 651629 = 244361) (by norm_num)
theorem B733549 : Blo 432776 733549 := bbase (se 3 (by rfl) ⟨137540, by rfl⟩ : syracuseStep 733549 = 275081) (by norm_num)
theorem B463217 : Blo 432776 463217 := bbase (se 2 (by rfl) ⟨173706, by rfl⟩ : syracuseStep 463217 = 347413) (by norm_num)
theorem B979325 : Blo 432776 979325 := bbase (se 3 (by rfl) ⟨183623, by rfl⟩ : syracuseStep 979325 = 367247) (by norm_num)
theorem B487813 : Blo 432776 487813 := bbase (se 4 (by rfl) ⟨45732, by rfl⟩ : syracuseStep 487813 = 91465) (by norm_num)
theorem B651653 : Blo 432776 651653 := bbase (se 4 (by rfl) ⟨61092, by rfl⟩ : syracuseStep 651653 = 122185) (by norm_num)
theorem B823709 : Blo 432776 823709 := bbase (se 3 (by rfl) ⟨154445, by rfl⟩ : syracuseStep 823709 = 308891) (by norm_num)
theorem B651677 : Blo 432776 651677 := bbase (se 3 (by rfl) ⟨122189, by rfl⟩ : syracuseStep 651677 = 244379) (by norm_num)
theorem B487849 : Blo 432776 487849 := bbase (se 2 (by rfl) ⟨182943, by rfl⟩ : syracuseStep 487849 = 365887) (by norm_num)
theorem B463277 : Blo 432776 463277 := bbase (se 3 (by rfl) ⟨86864, by rfl⟩ : syracuseStep 463277 = 173729) (by norm_num)
theorem B651701 : Blo 432776 651701 := bbase (se 5 (by rfl) ⟨30548, by rfl⟩ : syracuseStep 651701 = 61097) (by norm_num)
theorem B733637 : Blo 432776 733637 := bbase (se 4 (by rfl) ⟨68778, by rfl⟩ : syracuseStep 733637 = 137557) (by norm_num)
theorem B979397 : Blo 432776 979397 := bbase (se 4 (by rfl) ⟨91818, by rfl⟩ : syracuseStep 979397 = 183637) (by norm_num)
theorem B487885 : Blo 432776 487885 := bbase (se 3 (by rfl) ⟨91478, by rfl⟩ : syracuseStep 487885 = 182957) (by norm_num)
theorem B651725 : Blo 432776 651725 := bbase (se 3 (by rfl) ⟨122198, by rfl⟩ : syracuseStep 651725 = 244397) (by norm_num)
theorem B520673 : Blo 432776 520673 := bbase (se 2 (by rfl) ⟨195252, by rfl⟩ : syracuseStep 520673 = 390505) (by norm_num)
theorem B1667557 : Blo 432776 1667557 := bbase (se 4 (by rfl) ⟨156333, by rfl⟩ : syracuseStep 1667557 = 312667) (by norm_num)
theorem B651749 : Blo 432776 651749 := bbase (se 4 (by rfl) ⟨61101, by rfl⟩ : syracuseStep 651749 = 122203) (by norm_num)
theorem B1192421 : Blo 432776 1192421 := bbase (se 4 (by rfl) ⟨111789, by rfl⟩ : syracuseStep 1192421 = 223579) (by norm_num)
theorem B487921 : Blo 432776 487921 := bbase (se 2 (by rfl) ⟨182970, by rfl⟩ : syracuseStep 487921 = 365941) (by norm_num)
theorem B651773 : Blo 432776 651773 := bbase (se 3 (by rfl) ⟨122207, by rfl⟩ : syracuseStep 651773 = 244415) (by norm_num)
theorem B979469 : Blo 432776 979469 := bbase (se 3 (by rfl) ⟨183650, by rfl⟩ : syracuseStep 979469 = 367301) (by norm_num)
theorem B1462805 : Blo 432776 1462805 := bbase (se 6 (by rfl) ⟨34284, by rfl⟩ : syracuseStep 1462805 = 68569) (by norm_num)
theorem B487957 : Blo 432776 487957 := bbase (se 6 (by rfl) ⟨11436, by rfl⟩ : syracuseStep 487957 = 22873) (by norm_num)
theorem B651797 : Blo 432776 651797 := bbase (se 6 (by rfl) ⟨15276, by rfl⟩ : syracuseStep 651797 = 30553) (by norm_num)
theorem B447001 : Blo 432776 447001 := bbase (se 2 (by rfl) ⟨167625, by rfl⟩ : syracuseStep 447001 = 335251) (by norm_num)
theorem B660005 : Blo 432776 660005 := bbase (se 4 (by rfl) ⟨61875, by rfl⟩ : syracuseStep 660005 = 123751) (by norm_num)
theorem B463405 : Blo 432776 463405 := bbase (se 3 (by rfl) ⟨86888, by rfl⟩ : syracuseStep 463405 = 173777) (by norm_num)
theorem B651821 : Blo 432776 651821 := bbase (se 3 (by rfl) ⟨122216, by rfl⟩ : syracuseStep 651821 = 244433) (by norm_num)
theorem B1045037 : Blo 432776 1045037 := bbase (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) (by norm_num)
theorem B823861 : Blo 432776 823861 := bbase (se 5 (by rfl) ⟨38618, by rfl⟩ : syracuseStep 823861 = 77237) (by norm_num)
theorem B487993 : Blo 432776 487993 := bbase (se 2 (by rfl) ⟨182997, by rfl⟩ : syracuseStep 487993 = 365995) (by norm_num)
theorem B651845 : Blo 432776 651845 := bbase (se 4 (by rfl) ⟨61110, by rfl⟩ : syracuseStep 651845 = 122221) (by norm_num)
theorem B733765 : Blo 432776 733765 := bbase (se 4 (by rfl) ⟨68790, by rfl⟩ : syracuseStep 733765 = 137581) (by norm_num)
theorem B660053 : Blo 432776 660053 := bbase (se 8 (by rfl) ⟨3867, by rfl⟩ : syracuseStep 660053 = 7735) (by norm_num)
theorem B979541 : Blo 432776 979541 := bbase (se 8 (by rfl) ⟨5739, by rfl⟩ : syracuseStep 979541 = 11479) (by norm_num)
theorem B12554837 : Blo 432776 12554837 := bbase (se 8 (by rfl) ⟨73563, by rfl⟩ : syracuseStep 12554837 = 147127) (by norm_num)
theorem B488029 : Blo 432776 488029 := bbase (se 3 (by rfl) ⟨91505, by rfl⟩ : syracuseStep 488029 = 183011) (by norm_num)
theorem B651869 : Blo 432776 651869 := bbase (se 3 (by rfl) ⟨122225, by rfl⟩ : syracuseStep 651869 = 244451) (by norm_num)
theorem B651893 : Blo 432776 651893 := bbase (se 5 (by rfl) ⟨30557, by rfl⟩ : syracuseStep 651893 = 61115) (by norm_num)
theorem B488065 : Blo 432776 488065 := bbase (se 2 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 488065 = 366049) (by norm_num)
theorem B651917 : Blo 432776 651917 := bbase (se 3 (by rfl) ⟨122234, by rfl⟩ : syracuseStep 651917 = 244469) (by norm_num)
theorem B2192021 : Blo 432776 2192021 := bbase (se 6 (by rfl) ⟨51375, by rfl⟩ : syracuseStep 2192021 = 102751) (by norm_num)
theorem B733853 : Blo 432776 733853 := bbase (se 3 (by rfl) ⟨137597, by rfl⟩ : syracuseStep 733853 = 275195) (by norm_num)
theorem B979613 : Blo 432776 979613 := bbase (se 3 (by rfl) ⟨183677, by rfl⟩ : syracuseStep 979613 = 367355) (by norm_num)
theorem B488101 : Blo 432776 488101 := bbase (se 4 (by rfl) ⟨45759, by rfl⟩ : syracuseStep 488101 = 91519) (by norm_num)
theorem B651941 : Blo 432776 651941 := bbase (se 4 (by rfl) ⟨61119, by rfl⟩ : syracuseStep 651941 = 122239) (by norm_num)
theorem B651965 : Blo 432776 651965 := bbase (se 3 (by rfl) ⟨122243, by rfl⟩ : syracuseStep 651965 = 244487) (by norm_num)
theorem B1233605 : Blo 432776 1233605 := bbase (se 4 (by rfl) ⟨115650, by rfl⟩ : syracuseStep 1233605 = 231301) (by norm_num)
theorem B938693 : Blo 432776 938693 := bbase (se 4 (by rfl) ⟨88002, by rfl⟩ : syracuseStep 938693 = 176005) (by norm_num)
theorem B488137 : Blo 432776 488137 := bbase (se 2 (by rfl) ⟨183051, by rfl⟩ : syracuseStep 488137 = 366103) (by norm_num)
theorem B651989 : Blo 432776 651989 := bbase (se 7 (by rfl) ⟨7640, by rfl⟩ : syracuseStep 651989 = 15281) (by norm_num)
theorem B979685 : Blo 432776 979685 := bbase (se 4 (by rfl) ⟨91845, by rfl⟩ : syracuseStep 979685 = 183691) (by norm_num)
theorem B488173 : Blo 432776 488173 := bbase (se 3 (by rfl) ⟨91532, by rfl⟩ : syracuseStep 488173 = 183065) (by norm_num)
theorem B652013 : Blo 432776 652013 := bbase (se 3 (by rfl) ⟨122252, by rfl⟩ : syracuseStep 652013 = 244505) (by norm_num)
theorem B3347189 : Blo 432776 3347189 := bbase (se 5 (by rfl) ⟨156899, by rfl⟩ : syracuseStep 3347189 = 313799) (by norm_num)
theorem B652037 : Blo 432776 652037 := bbase (se 4 (by rfl) ⟨61128, by rfl⟩ : syracuseStep 652037 = 122257) (by norm_num)
theorem B488209 : Blo 432776 488209 := bbase (se 2 (by rfl) ⟨183078, by rfl⟩ : syracuseStep 488209 = 366157) (by norm_num)
theorem B652061 : Blo 432776 652061 := bbase (se 3 (by rfl) ⟨122261, by rfl⟩ : syracuseStep 652061 = 244523) (by norm_num)
theorem B733981 : Blo 432776 733981 := bbase (se 3 (by rfl) ⟨137621, by rfl⟩ : syracuseStep 733981 = 275243) (by norm_num)
theorem B586541 : Blo 432776 586541 := bbase (se 3 (by rfl) ⟨109976, by rfl⟩ : syracuseStep 586541 = 219953) (by norm_num)
theorem B979757 : Blo 432776 979757 := bbase (se 3 (by rfl) ⟨183704, by rfl⟩ : syracuseStep 979757 = 367409) (by norm_num)
theorem B488245 : Blo 432776 488245 := bbase (se 5 (by rfl) ⟨22886, by rfl⟩ : syracuseStep 488245 = 45773) (by norm_num)
theorem B652085 : Blo 432776 652085 := bbase (se 5 (by rfl) ⟨30566, by rfl⟩ : syracuseStep 652085 = 61133) (by norm_num)
theorem B930629 : Blo 432776 930629 := bbase (se 4 (by rfl) ⟨87246, by rfl⟩ : syracuseStep 930629 = 174493) (by norm_num)
theorem B652109 : Blo 432776 652109 := bbase (se 3 (by rfl) ⟨122270, by rfl⟩ : syracuseStep 652109 = 244541) (by norm_num)
theorem B930637 : Blo 432776 930637 := bbase (se 3 (by rfl) ⟨174494, by rfl⟩ : syracuseStep 930637 = 348989) (by norm_num)
theorem B488281 : Blo 432776 488281 := bbase (se 2 (by rfl) ⟨183105, by rfl⟩ : syracuseStep 488281 = 366211) (by norm_num)
theorem B824165 : Blo 432776 824165 := bbase (se 4 (by rfl) ⟨77265, by rfl⟩ : syracuseStep 824165 = 154531) (by norm_num)
theorem B652133 : Blo 432776 652133 := bbase (se 4 (by rfl) ⟨61137, by rfl⟩ : syracuseStep 652133 = 122275) (by norm_num)
theorem B1102693 : Blo 432776 1102693 := bbase (se 4 (by rfl) ⟨103377, by rfl⟩ : syracuseStep 1102693 = 206755) (by norm_num)
theorem B734069 : Blo 432776 734069 := bbase (se 5 (by rfl) ⟨34409, by rfl⟩ : syracuseStep 734069 = 68819) (by norm_num)
theorem B979829 : Blo 432776 979829 := bbase (se 5 (by rfl) ⟨45929, by rfl⟩ : syracuseStep 979829 = 91859) (by norm_num)
theorem B488317 : Blo 432776 488317 := bbase (se 3 (by rfl) ⟨91559, by rfl⟩ : syracuseStep 488317 = 183119) (by norm_num)
theorem B652157 : Blo 432776 652157 := bbase (se 3 (by rfl) ⟨122279, by rfl⟩ : syracuseStep 652157 = 244559) (by norm_num)
theorem B652181 : Blo 432776 652181 := bbase (se 6 (by rfl) ⟨15285, by rfl⟩ : syracuseStep 652181 = 30571) (by norm_num)
theorem B488353 : Blo 432776 488353 := bbase (se 2 (by rfl) ⟨183132, by rfl⟩ : syracuseStep 488353 = 366265) (by norm_num)
theorem B652205 : Blo 432776 652205 := bbase (se 3 (by rfl) ⟨122288, by rfl⟩ : syracuseStep 652205 = 244577) (by norm_num)
theorem B619445 : Blo 432776 619445 := bbase (se 5 (by rfl) ⟨29036, by rfl⟩ : syracuseStep 619445 = 58073) (by norm_num)
theorem B979901 : Blo 432776 979901 := bbase (se 3 (by rfl) ⟨183731, by rfl⟩ : syracuseStep 979901 = 367463) (by norm_num)
theorem B1463237 : Blo 432776 1463237 := bbase (se 4 (by rfl) ⟨137178, by rfl⟩ : syracuseStep 1463237 = 274357) (by norm_num)
theorem B488389 : Blo 432776 488389 := bbase (se 4 (by rfl) ⟨45786, by rfl⟩ : syracuseStep 488389 = 91573) (by norm_num)
theorem B652229 : Blo 432776 652229 := bbase (se 4 (by rfl) ⟨61146, by rfl⟩ : syracuseStep 652229 = 122293) (by norm_num)
theorem B1110989 : Blo 432776 1110989 := bbase (se 3 (by rfl) ⟨208310, by rfl⟩ : syracuseStep 1110989 = 416621) (by norm_num)
theorem B12530645 : Blo 432776 12530645 := bbase (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) (by norm_num)
theorem B1102805 : Blo 432776 1102805 := bbase (se 7 (by rfl) ⟨12923, by rfl⟩ : syracuseStep 1102805 = 25847) (by norm_num)
theorem B447449 : Blo 432776 447449 := bbase (se 2 (by rfl) ⟨167793, by rfl⟩ : syracuseStep 447449 = 335587) (by norm_num)
theorem B652253 : Blo 432776 652253 := bbase (se 3 (by rfl) ⟨122297, by rfl⟩ : syracuseStep 652253 = 244595) (by norm_num)
theorem B488425 : Blo 432776 488425 := bbase (se 2 (by rfl) ⟨183159, by rfl⟩ : syracuseStep 488425 = 366319) (by norm_num)
theorem B463849 : Blo 432776 463849 := bbase (se 2 (by rfl) ⟨173943, by rfl⟩ : syracuseStep 463849 = 347887) (by norm_num)
theorem B652277 : Blo 432776 652277 := bbase (se 5 (by rfl) ⟨30575, by rfl⟩ : syracuseStep 652277 = 61151) (by norm_num)
theorem B734197 : Blo 432776 734197 := bbase (se 5 (by rfl) ⟨34415, by rfl⟩ : syracuseStep 734197 = 68831) (by norm_num)
theorem B1176565 : Blo 432776 1176565 := bbase (se 5 (by rfl) ⟨55151, by rfl⟩ : syracuseStep 1176565 = 110303) (by norm_num)
theorem B619525 : Blo 432776 619525 := bbase (se 4 (by rfl) ⟨58080, by rfl⟩ : syracuseStep 619525 = 116161) (by norm_num)
theorem B979973 : Blo 432776 979973 := bbase (se 4 (by rfl) ⟨91872, by rfl⟩ : syracuseStep 979973 = 183745) (by norm_num)
theorem B488461 : Blo 432776 488461 := bbase (se 3 (by rfl) ⟨91586, by rfl⟩ : syracuseStep 488461 = 183173) (by norm_num)
theorem B652301 : Blo 432776 652301 := bbase (se 3 (by rfl) ⟨122306, by rfl⟩ : syracuseStep 652301 = 244613) (by norm_num)
theorem B652325 : Blo 432776 652325 := bbase (se 4 (by rfl) ⟨61155, by rfl⟩ : syracuseStep 652325 = 122311) (by norm_num)
theorem B488497 : Blo 432776 488497 := bbase (se 2 (by rfl) ⟨183186, by rfl⟩ : syracuseStep 488497 = 366373) (by norm_num)
theorem B521273 : Blo 432776 521273 := bbase (se 2 (by rfl) ⟨195477, by rfl⟩ : syracuseStep 521273 = 390955) (by norm_num)
theorem B652349 : Blo 432776 652349 := bbase (se 3 (by rfl) ⟨122315, by rfl⟩ : syracuseStep 652349 = 244631) (by norm_num)
theorem B734285 : Blo 432776 734285 := bbase (se 3 (by rfl) ⟨137678, by rfl⟩ : syracuseStep 734285 = 275357) (by norm_num)
theorem B980045 : Blo 432776 980045 := bbase (se 3 (by rfl) ⟨183758, by rfl⟩ : syracuseStep 980045 = 367517) (by norm_num)
theorem B1561685 : Blo 432776 1561685 := bbase (se 8 (by rfl) ⟨9150, by rfl⟩ : syracuseStep 1561685 = 18301) (by norm_num)
theorem B488533 : Blo 432776 488533 := bbase (se 8 (by rfl) ⟨2862, by rfl⟩ : syracuseStep 488533 = 5725) (by norm_num)
theorem B652373 : Blo 432776 652373 := bbase (se 8 (by rfl) ⟨3822, by rfl⟩ : syracuseStep 652373 = 7645) (by norm_num)
theorem B463969 : Blo 432776 463969 := bbase (se 2 (by rfl) ⟨173988, by rfl⟩ : syracuseStep 463969 = 347977) (by norm_num)
theorem B652397 : Blo 432776 652397 := bbase (se 3 (by rfl) ⟨122324, by rfl⟩ : syracuseStep 652397 = 244649) (by norm_num)
theorem B488569 : Blo 432776 488569 := bbase (se 2 (by rfl) ⟨183213, by rfl⟩ : syracuseStep 488569 = 366427) (by norm_num)
theorem B619645 : Blo 432776 619645 := bbase (se 3 (by rfl) ⟨116183, by rfl⟩ : syracuseStep 619645 = 232367) (by norm_num)
theorem B652421 : Blo 432776 652421 := bbase (se 4 (by rfl) ⟨61164, by rfl⟩ : syracuseStep 652421 = 122329) (by norm_num)
theorem B980117 : Blo 432776 980117 := bbase (se 6 (by rfl) ⟨22971, by rfl⟩ : syracuseStep 980117 = 45943) (by norm_num)
theorem B1102997 : Blo 432776 1102997 := bbase (se 6 (by rfl) ⟨25851, by rfl⟩ : syracuseStep 1102997 = 51703) (by norm_num)
theorem B488605 : Blo 432776 488605 := bbase (se 3 (by rfl) ⟨91613, by rfl⟩ : syracuseStep 488605 = 183227) (by norm_num)
theorem B652445 : Blo 432776 652445 := bbase (se 3 (by rfl) ⟨122333, by rfl⟩ : syracuseStep 652445 = 244667) (by norm_num)
theorem B1881269 : Blo 432776 1881269 := bbase (se 5 (by rfl) ⟨88184, by rfl⟩ : syracuseStep 1881269 = 176369) (by norm_num)
theorem B652469 : Blo 432776 652469 := bbase (se 5 (by rfl) ⟨30584, by rfl⟩ : syracuseStep 652469 = 61169) (by norm_num)
theorem B488641 : Blo 432776 488641 := bbase (se 2 (by rfl) ⟨183240, by rfl⟩ : syracuseStep 488641 = 366481) (by norm_num)
theorem B1569989 : Blo 432776 1569989 := bbase (se 4 (by rfl) ⟨147186, by rfl⟩ : syracuseStep 1569989 = 294373) (by norm_num)
theorem B652493 : Blo 432776 652493 := bbase (se 3 (by rfl) ⟨122342, by rfl⟩ : syracuseStep 652493 = 244685) (by norm_num)
theorem B734413 : Blo 432776 734413 := bbase (se 3 (by rfl) ⟨137702, by rfl⟩ : syracuseStep 734413 = 275405) (by norm_num)
theorem B586973 : Blo 432776 586973 := bbase (se 3 (by rfl) ⟨110057, by rfl⟩ : syracuseStep 586973 = 220115) (by norm_num)
theorem B619741 : Blo 432776 619741 := bbase (se 3 (by rfl) ⟨116201, by rfl⟩ : syracuseStep 619741 = 232403) (by norm_num)
theorem B980189 : Blo 432776 980189 := bbase (se 3 (by rfl) ⟨183785, by rfl⟩ : syracuseStep 980189 = 367571) (by norm_num)
theorem B488677 : Blo 432776 488677 := bbase (se 4 (by rfl) ⟨45813, by rfl⟩ : syracuseStep 488677 = 91627) (by norm_num)
theorem B652517 : Blo 432776 652517 := bbase (se 4 (by rfl) ⟨61173, by rfl⟩ : syracuseStep 652517 = 122347) (by norm_num)
theorem B652541 : Blo 432776 652541 := bbase (se 3 (by rfl) ⟨122351, by rfl⟩ : syracuseStep 652541 = 244703) (by norm_num)
theorem B488713 : Blo 432776 488713 := bbase (se 2 (by rfl) ⟨183267, by rfl⟩ : syracuseStep 488713 = 366535) (by norm_num)
theorem B439565 : Blo 432776 439565 := bbase (se 3 (by rfl) ⟨82418, by rfl⟩ : syracuseStep 439565 = 164837) (by norm_num)
theorem B652565 : Blo 432776 652565 := bbase (se 6 (by rfl) ⟨15294, by rfl⟩ : syracuseStep 652565 = 30589) (by norm_num)
theorem B734501 : Blo 432776 734501 := bbase (se 4 (by rfl) ⟨68859, by rfl⟩ : syracuseStep 734501 = 137719) (by norm_num)
theorem B980261 : Blo 432776 980261 := bbase (se 4 (by rfl) ⟨91899, by rfl⟩ : syracuseStep 980261 = 183799) (by norm_num)
theorem B488749 : Blo 432776 488749 := bbase (se 3 (by rfl) ⟨91640, by rfl⟩ : syracuseStep 488749 = 183281) (by norm_num)
theorem B652589 : Blo 432776 652589 := bbase (se 3 (by rfl) ⟨122360, by rfl⟩ : syracuseStep 652589 = 244721) (by norm_num)
theorem B628013 : Blo 432776 628013 := bbase (se 3 (by rfl) ⟨117752, by rfl⟩ : syracuseStep 628013 = 235505) (by norm_num)
theorem B1652021 : Blo 432776 1652021 := bbase (se 5 (by rfl) ⟨77438, by rfl⟩ : syracuseStep 1652021 = 154877) (by norm_num)
theorem B3626293 : Blo 432776 3626293 := bbase (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) (by norm_num)
theorem B652613 : Blo 432776 652613 := bbase (se 4 (by rfl) ⟨61182, by rfl⟩ : syracuseStep 652613 = 122365) (by norm_num)
theorem B488785 : Blo 432776 488785 := bbase (se 2 (by rfl) ⟨183294, by rfl⟩ : syracuseStep 488785 = 366589) (by norm_num)
theorem B464221 : Blo 432776 464221 := bbase (se 3 (by rfl) ⟨87041, by rfl⟩ : syracuseStep 464221 = 174083) (by norm_num)
theorem B652637 : Blo 432776 652637 := bbase (se 3 (by rfl) ⟨122369, by rfl⟩ : syracuseStep 652637 = 244739) (by norm_num)
theorem B464225 : Blo 432776 464225 := bbase (se 2 (by rfl) ⟨174084, by rfl⟩ : syracuseStep 464225 = 348169) (by norm_num)
theorem B521581 : Blo 432776 521581 := bbase (se 3 (by rfl) ⟨97796, by rfl⟩ : syracuseStep 521581 = 195593) (by norm_num)
theorem B980333 : Blo 432776 980333 := bbase (se 3 (by rfl) ⟨183812, by rfl⟩ : syracuseStep 980333 = 367625) (by norm_num)
theorem B1463669 : Blo 432776 1463669 := bbase (se 5 (by rfl) ⟨68609, by rfl⟩ : syracuseStep 1463669 = 137219) (by norm_num)
theorem B488821 : Blo 432776 488821 := bbase (se 5 (by rfl) ⟨22913, by rfl⟩ : syracuseStep 488821 = 45827) (by norm_num)
theorem B652661 : Blo 432776 652661 := bbase (se 5 (by rfl) ⟨30593, by rfl⟩ : syracuseStep 652661 = 61187) (by norm_num)
theorem B652685 : Blo 432776 652685 := bbase (se 3 (by rfl) ⟨122378, by rfl⟩ : syracuseStep 652685 = 244757) (by norm_num)
theorem B488857 : Blo 432776 488857 := bbase (se 2 (by rfl) ⟨183321, by rfl⟩ : syracuseStep 488857 = 366643) (by norm_num)
theorem B652709 : Blo 432776 652709 := bbase (se 4 (by rfl) ⟨61191, by rfl⟩ : syracuseStep 652709 = 122383) (by norm_num)
theorem B734629 : Blo 432776 734629 := bbase (se 4 (by rfl) ⟨68871, by rfl⟩ : syracuseStep 734629 = 137743) (by norm_num)
theorem B980405 : Blo 432776 980405 := bbase (se 5 (by rfl) ⟨45956, by rfl⟩ : syracuseStep 980405 = 91913) (by norm_num)
theorem B488893 : Blo 432776 488893 := bbase (se 3 (by rfl) ⟨91667, by rfl⟩ : syracuseStep 488893 = 183335) (by norm_num)
theorem B652733 : Blo 432776 652733 := bbase (se 3 (by rfl) ⟨122387, by rfl⟩ : syracuseStep 652733 = 244775) (by norm_num)
theorem B521677 : Blo 432776 521677 := bbase (se 3 (by rfl) ⟨97814, by rfl⟩ : syracuseStep 521677 = 195629) (by norm_num)
theorem B742861 : Blo 432776 742861 := bbase (se 3 (by rfl) ⟨139286, by rfl⟩ : syracuseStep 742861 = 278573) (by norm_num)
theorem B652757 : Blo 432776 652757 := bbase (se 7 (by rfl) ⟨7649, by rfl⟩ : syracuseStep 652757 = 15299) (by norm_num)
theorem B488929 : Blo 432776 488929 := bbase (se 2 (by rfl) ⟨183348, by rfl⟩ : syracuseStep 488929 = 366697) (by norm_num)
theorem B652781 : Blo 432776 652781 := bbase (se 3 (by rfl) ⟨122396, by rfl⟩ : syracuseStep 652781 = 244793) (by norm_num)
theorem B521725 : Blo 432776 521725 := bbase (se 3 (by rfl) ⟨97823, by rfl⟩ : syracuseStep 521725 = 195647) (by norm_num)
theorem B734717 : Blo 432776 734717 := bbase (se 3 (by rfl) ⟨137759, by rfl⟩ : syracuseStep 734717 = 275519) (by norm_num)
theorem B980477 : Blo 432776 980477 := bbase (se 3 (by rfl) ⟨183839, by rfl⟩ : syracuseStep 980477 = 367679) (by norm_num)
theorem B488965 : Blo 432776 488965 := bbase (se 4 (by rfl) ⟨45840, by rfl⟩ : syracuseStep 488965 = 91681) (by norm_num)
theorem B2201093 : Blo 432776 2201093 := bbase (se 4 (by rfl) ⟨206352, by rfl⟩ : syracuseStep 2201093 = 412705) (by norm_num)
theorem B652805 : Blo 432776 652805 := bbase (se 4 (by rfl) ⟨61200, by rfl⟩ : syracuseStep 652805 = 122401) (by norm_num)
theorem B611869 : Blo 432776 611869 := bbase (se 3 (by rfl) ⟨114725, by rfl⟩ : syracuseStep 611869 = 229451) (by norm_num)
theorem B652829 : Blo 432776 652829 := bbase (se 3 (by rfl) ⟨122405, by rfl⟩ : syracuseStep 652829 = 244811) (by norm_num)
theorem B751141 : Blo 432776 751141 := bbase (se 4 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 751141 = 140839) (by norm_num)
theorem B489001 : Blo 432776 489001 := bbase (se 2 (by rfl) ⟨183375, by rfl⟩ : syracuseStep 489001 = 366751) (by norm_num)
theorem B652853 : Blo 432776 652853 := bbase (se 5 (by rfl) ⟨30602, by rfl⟩ : syracuseStep 652853 = 61205) (by norm_num)
theorem B693821 : Blo 432776 693821 := bbase (se 3 (by rfl) ⟨130091, by rfl⟩ : syracuseStep 693821 = 260183) (by norm_num)
theorem B882245 : Blo 432776 882245 := bbase (se 4 (by rfl) ⟨82710, by rfl⟩ : syracuseStep 882245 = 165421) (by norm_num)
theorem B489037 : Blo 432776 489037 := bbase (se 3 (by rfl) ⟨91694, by rfl⟩ : syracuseStep 489037 = 183389) (by norm_num)
theorem B652877 : Blo 432776 652877 := bbase (se 3 (by rfl) ⟨122414, by rfl⟩ : syracuseStep 652877 = 244829) (by norm_num)
theorem B824917 : Blo 432776 824917 := bbase (se 8 (by rfl) ⟨4833, by rfl⟩ : syracuseStep 824917 = 9667) (by norm_num)
theorem B1652309 : Blo 432776 1652309 := bbase (se 8 (by rfl) ⟨9681, by rfl⟩ : syracuseStep 1652309 = 19363) (by norm_num)
theorem B2979413 : Blo 432776 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B652901 : Blo 432776 652901 := bbase (se 4 (by rfl) ⟨61209, by rfl⟩ : syracuseStep 652901 = 122419) (by norm_num)
theorem B489073 : Blo 432776 489073 := bbase (se 2 (by rfl) ⟨183402, by rfl⟩ : syracuseStep 489073 = 366805) (by norm_num)
theorem B652925 : Blo 432776 652925 := bbase (se 3 (by rfl) ⟨122423, by rfl⟩ : syracuseStep 652925 = 244847) (by norm_num)
theorem B734845 : Blo 432776 734845 := bbase (se 3 (by rfl) ⟨137783, by rfl⟩ : syracuseStep 734845 = 275567) (by norm_num)
theorem B489109 : Blo 432776 489109 := bbase (se 6 (by rfl) ⟨11463, by rfl⟩ : syracuseStep 489109 = 22927) (by norm_num)
theorem B652949 : Blo 432776 652949 := bbase (se 6 (by rfl) ⟨15303, by rfl⟩ : syracuseStep 652949 = 30607) (by norm_num)
theorem B882341 : Blo 432776 882341 := bbase (se 4 (by rfl) ⟨82719, by rfl⟩ : syracuseStep 882341 = 165439) (by norm_num)
theorem B652973 : Blo 432776 652973 := bbase (se 3 (by rfl) ⟨122432, by rfl⟩ : syracuseStep 652973 = 244865) (by norm_num)
theorem B2815669 : Blo 432776 2815669 := bbase (se 5 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 2815669 = 263969) (by norm_num)
theorem B489145 : Blo 432776 489145 := bbase (se 2 (by rfl) ⟨183429, by rfl⟩ : syracuseStep 489145 = 366859) (by norm_num)
theorem B652997 : Blo 432776 652997 := bbase (se 4 (by rfl) ⟨61218, by rfl⟩ : syracuseStep 652997 = 122437) (by norm_num)
theorem B620237 : Blo 432776 620237 := bbase (se 3 (by rfl) ⟨116294, by rfl⟩ : syracuseStep 620237 = 232589) (by norm_num)
theorem B1644245 : Blo 432776 1644245 := bbase (se 7 (by rfl) ⟨19268, by rfl⟩ : syracuseStep 1644245 = 38537) (by norm_num)
theorem B734933 : Blo 432776 734933 := bbase (se 7 (by rfl) ⟨8612, by rfl⟩ : syracuseStep 734933 = 17225) (by norm_num)
theorem B489181 : Blo 432776 489181 := bbase (se 3 (by rfl) ⟨91721, by rfl⟩ : syracuseStep 489181 = 183443) (by norm_num)
theorem B653021 : Blo 432776 653021 := bbase (se 3 (by rfl) ⟨122441, by rfl⟩ : syracuseStep 653021 = 244883) (by norm_num)
theorem B825061 : Blo 432776 825061 := bbase (se 4 (by rfl) ⟨77349, by rfl⟩ : syracuseStep 825061 = 154699) (by norm_num)
theorem B653045 : Blo 432776 653045 := bbase (se 5 (by rfl) ⟨30611, by rfl⟩ : syracuseStep 653045 = 61223) (by norm_num)
theorem B489217 : Blo 432776 489217 := bbase (se 2 (by rfl) ⟨183456, by rfl⟩ : syracuseStep 489217 = 366913) (by norm_num)
theorem B653069 : Blo 432776 653069 := bbase (se 3 (by rfl) ⟨122450, by rfl⟩ : syracuseStep 653069 = 244901) (by norm_num)
theorem B2635541 : Blo 432776 2635541 := bbase (se 6 (by rfl) ⟨61770, by rfl⟩ : syracuseStep 2635541 = 123541) (by norm_num)
theorem B3127061 : Blo 432776 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B1464101 : Blo 432776 1464101 := bbase (se 4 (by rfl) ⟨137259, by rfl⟩ : syracuseStep 1464101 = 274519) (by norm_num)
theorem B587557 : Blo 432776 587557 := bbase (se 4 (by rfl) ⟨55083, by rfl⟩ : syracuseStep 587557 = 110167) (by norm_num)
theorem B489253 : Blo 432776 489253 := bbase (se 4 (by rfl) ⟨45867, by rfl⟩ : syracuseStep 489253 = 91735) (by norm_num)
theorem B653093 : Blo 432776 653093 := bbase (se 4 (by rfl) ⟨61227, by rfl⟩ : syracuseStep 653093 = 122455) (by norm_num)
theorem B653117 : Blo 432776 653117 := bbase (se 3 (by rfl) ⟨122459, by rfl⟩ : syracuseStep 653117 = 244919) (by norm_num)
theorem B489289 : Blo 432776 489289 := bbase (se 2 (by rfl) ⟨183483, by rfl⟩ : syracuseStep 489289 = 366967) (by norm_num)
theorem B653141 : Blo 432776 653141 := bbase (se 9 (by rfl) ⟨1913, by rfl⟩ : syracuseStep 653141 = 3827) (by norm_num)
theorem B735061 : Blo 432776 735061 := bbase (se 9 (by rfl) ⟨2153, by rfl⟩ : syracuseStep 735061 = 4307) (by norm_num)
theorem B489325 : Blo 432776 489325 := bbase (se 3 (by rfl) ⟨91748, by rfl⟩ : syracuseStep 489325 = 183497) (by norm_num)
theorem B653165 : Blo 432776 653165 := bbase (se 3 (by rfl) ⟨122468, by rfl⟩ : syracuseStep 653165 = 244937) (by norm_num)
theorem B849773 : Blo 432776 849773 := bbase (se 3 (by rfl) ⟨159332, by rfl⟩ : syracuseStep 849773 = 318665) (by norm_num)
theorem B825221 : Blo 432776 825221 := bbase (se 4 (by rfl) ⟨77364, by rfl⟩ : syracuseStep 825221 = 154729) (by norm_num)
theorem B653189 : Blo 432776 653189 := bbase (se 4 (by rfl) ⟨61236, by rfl⟩ : syracuseStep 653189 = 122473) (by norm_num)
theorem B1095565 : Blo 432776 1095565 := bbase (se 3 (by rfl) ⟨205418, by rfl⟩ : syracuseStep 1095565 = 410837) (by norm_num)
theorem B489361 : Blo 432776 489361 := bbase (se 2 (by rfl) ⟨183510, by rfl⟩ : syracuseStep 489361 = 367021) (by norm_num)
theorem B464789 : Blo 432776 464789 := bbase (se 6 (by rfl) ⟨10893, by rfl⟩ : syracuseStep 464789 = 21787) (by norm_num)
theorem B653213 : Blo 432776 653213 := bbase (se 3 (by rfl) ⟨122477, by rfl⟩ : syracuseStep 653213 = 244955) (by norm_num)
theorem B1046429 : Blo 432776 1046429 := bbase (se 3 (by rfl) ⟨196205, by rfl⟩ : syracuseStep 1046429 = 392411) (by norm_num)
theorem B2193317 : Blo 432776 2193317 := bbase (se 4 (by rfl) ⟨205623, by rfl⟩ : syracuseStep 2193317 = 411247) (by norm_num)
theorem B735149 : Blo 432776 735149 := bbase (se 3 (by rfl) ⟨137840, by rfl⟩ : syracuseStep 735149 = 275681) (by norm_num)
theorem B489397 : Blo 432776 489397 := bbase (se 5 (by rfl) ⟨22940, by rfl⟩ : syracuseStep 489397 = 45881) (by norm_num)
theorem B653237 : Blo 432776 653237 := bbase (se 5 (by rfl) ⟨30620, by rfl⟩ : syracuseStep 653237 = 61241) (by norm_num)
theorem B653261 : Blo 432776 653261 := bbase (se 3 (by rfl) ⟨122486, by rfl⟩ : syracuseStep 653261 = 244973) (by norm_num)
theorem B489433 : Blo 432776 489433 := bbase (se 2 (by rfl) ⟨183537, by rfl⟩ : syracuseStep 489433 = 367075) (by norm_num)
theorem B1562597 : Blo 432776 1562597 := bbase (se 4 (by rfl) ⟨146493, by rfl⟩ : syracuseStep 1562597 = 292987) (by norm_num)
theorem B653285 : Blo 432776 653285 := bbase (se 4 (by rfl) ⟨61245, by rfl⟩ : syracuseStep 653285 = 122491) (by norm_num)
theorem B1644533 : Blo 432776 1644533 := bbase (se 5 (by rfl) ⟨77087, by rfl⟩ : syracuseStep 1644533 = 154175) (by norm_num)
theorem B1095677 : Blo 432776 1095677 := bbase (se 3 (by rfl) ⟨205439, by rfl⟩ : syracuseStep 1095677 = 410879) (by norm_num)
theorem B489469 : Blo 432776 489469 := bbase (se 3 (by rfl) ⟨91775, by rfl⟩ : syracuseStep 489469 = 183551) (by norm_num)
theorem B653309 : Blo 432776 653309 := bbase (se 3 (by rfl) ⟨122495, by rfl⟩ : syracuseStep 653309 = 244991) (by norm_num)
theorem B1046525 : Blo 432776 1046525 := bbase (se 3 (by rfl) ⟨196223, by rfl⟩ : syracuseStep 1046525 = 392447) (by norm_num)
theorem B825365 : Blo 432776 825365 := bbase (se 6 (by rfl) ⟨19344, by rfl⟩ : syracuseStep 825365 = 38689) (by norm_num)
theorem B653333 : Blo 432776 653333 := bbase (se 6 (by rfl) ⟨15312, by rfl⟩ : syracuseStep 653333 = 30625) (by norm_num)
theorem B489505 : Blo 432776 489505 := bbase (se 2 (by rfl) ⟨183564, by rfl⟩ : syracuseStep 489505 = 367129) (by norm_num)
theorem B653357 : Blo 432776 653357 := bbase (se 3 (by rfl) ⟨122504, by rfl⟩ : syracuseStep 653357 = 245009) (by norm_num)
theorem B735277 : Blo 432776 735277 := bbase (se 3 (by rfl) ⟨137864, by rfl⟩ : syracuseStep 735277 = 275729) (by norm_num)
theorem B4454453 : Blo 432776 4454453 := bbase (se 5 (by rfl) ⟨208802, by rfl⟩ : syracuseStep 4454453 = 417605) (by norm_num)
theorem B489541 : Blo 432776 489541 := bbase (se 4 (by rfl) ⟨45894, by rfl⟩ : syracuseStep 489541 = 91789) (by norm_num)
theorem B653381 : Blo 432776 653381 := bbase (se 4 (by rfl) ⟨61254, by rfl⟩ : syracuseStep 653381 = 122509) (by norm_num)
theorem B464977 : Blo 432776 464977 := bbase (se 2 (by rfl) ⟨174366, by rfl⟩ : syracuseStep 464977 = 348733) (by norm_num)
theorem B653405 : Blo 432776 653405 := bbase (se 3 (by rfl) ⟨122513, by rfl⟩ : syracuseStep 653405 = 245027) (by norm_num)
theorem B489577 : Blo 432776 489577 := bbase (se 2 (by rfl) ⟨183591, by rfl⟩ : syracuseStep 489577 = 367183) (by norm_num)
theorem B1857653 : Blo 432776 1857653 := bbase (se 5 (by rfl) ⟨87077, by rfl⟩ : syracuseStep 1857653 = 174155) (by norm_num)
theorem B653429 : Blo 432776 653429 := bbase (se 5 (by rfl) ⟨30629, by rfl⟩ : syracuseStep 653429 = 61259) (by norm_num)
theorem B735365 : Blo 432776 735365 := bbase (se 4 (by rfl) ⟨68940, by rfl⟩ : syracuseStep 735365 = 137881) (by norm_num)
theorem B489613 : Blo 432776 489613 := bbase (se 3 (by rfl) ⟨91802, by rfl⟩ : syracuseStep 489613 = 183605) (by norm_num)
theorem B653453 : Blo 432776 653453 := bbase (se 3 (by rfl) ⟨122522, by rfl⟩ : syracuseStep 653453 = 245045) (by norm_num)
theorem B653477 : Blo 432776 653477 := bbase (se 4 (by rfl) ⟨61263, by rfl⟩ : syracuseStep 653477 = 122527) (by norm_num)
theorem B489649 : Blo 432776 489649 := bbase (se 2 (by rfl) ⟨183618, by rfl⟩ : syracuseStep 489649 = 367237) (by norm_num)
theorem B1095869 : Blo 432776 1095869 := bbase (se 3 (by rfl) ⟨205475, by rfl⟩ : syracuseStep 1095869 = 410951) (by norm_num)
theorem B653501 : Blo 432776 653501 := bbase (se 3 (by rfl) ⟨122531, by rfl⟩ : syracuseStep 653501 = 245063) (by norm_num)
theorem B1464533 : Blo 432776 1464533 := bbase (se 7 (by rfl) ⟨17162, by rfl⟩ : syracuseStep 1464533 = 34325) (by norm_num)
theorem B489685 : Blo 432776 489685 := bbase (se 7 (by rfl) ⟨5738, by rfl⟩ : syracuseStep 489685 = 11477) (by norm_num)
theorem B653525 : Blo 432776 653525 := bbase (se 7 (by rfl) ⟨7658, by rfl⟩ : syracuseStep 653525 = 15317) (by norm_num)
theorem B653549 : Blo 432776 653549 := bbase (se 3 (by rfl) ⟨122540, by rfl⟩ : syracuseStep 653549 = 245081) (by norm_num)
theorem B1235189 : Blo 432776 1235189 := bbase (se 5 (by rfl) ⟨57899, by rfl⟩ : syracuseStep 1235189 = 115799) (by norm_num)
theorem B489721 : Blo 432776 489721 := bbase (se 2 (by rfl) ⟨183645, by rfl⟩ : syracuseStep 489721 = 367291) (by norm_num)
theorem B653573 : Blo 432776 653573 := bbase (se 4 (by rfl) ⟨61272, by rfl⟩ : syracuseStep 653573 = 122545) (by norm_num)
theorem B489757 : Blo 432776 489757 := bbase (se 3 (by rfl) ⟨91829, by rfl⟩ : syracuseStep 489757 = 183659) (by norm_num)
theorem B653597 : Blo 432776 653597 := bbase (se 3 (by rfl) ⟨122549, by rfl⟩ : syracuseStep 653597 = 245099) (by norm_num)
theorem B825653 : Blo 432776 825653 := bbase (se 5 (by rfl) ⟨38702, by rfl⟩ : syracuseStep 825653 = 77405) (by norm_num)
theorem B653621 : Blo 432776 653621 := bbase (se 5 (by rfl) ⟨30638, by rfl⟩ : syracuseStep 653621 = 61277) (by norm_num)
theorem B489793 : Blo 432776 489793 := bbase (se 2 (by rfl) ⟨183672, by rfl⟩ : syracuseStep 489793 = 367345) (by norm_num)
theorem B653645 : Blo 432776 653645 := bbase (se 3 (by rfl) ⟨122558, by rfl⟩ : syracuseStep 653645 = 245117) (by norm_num)
theorem B1431893 : Blo 432776 1431893 := bbase (se 10 (by rfl) ⟨2097, by rfl⟩ : syracuseStep 1431893 = 4195) (by norm_num)
theorem B489829 : Blo 432776 489829 := bbase (se 4 (by rfl) ⟨45921, by rfl⟩ : syracuseStep 489829 = 91843) (by norm_num)
theorem B489865 : Blo 432776 489865 := bbase (se 2 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 489865 = 367399) (by norm_num)
theorem B489901 : Blo 432776 489901 := bbase (se 3 (by rfl) ⟨91856, by rfl⟩ : syracuseStep 489901 = 183713) (by norm_num)
theorem B784837 : Blo 432776 784837 := bbase (se 4 (by rfl) ⟨73578, by rfl⟩ : syracuseStep 784837 = 147157) (by norm_num)
theorem B825805 : Blo 432776 825805 := bbase (se 3 (by rfl) ⟨154838, by rfl⟩ : syracuseStep 825805 = 309677) (by norm_num)
theorem B489937 : Blo 432776 489937 := bbase (se 2 (by rfl) ⟨183726, by rfl⟩ : syracuseStep 489937 = 367453) (by norm_num)
theorem B2775509 : Blo 432776 2775509 := bbase (se 7 (by rfl) ⟨32525, by rfl⟩ : syracuseStep 2775509 = 65051) (by norm_num)
theorem B489973 : Blo 432776 489973 := bbase (se 5 (by rfl) ⟨22967, by rfl⟩ : syracuseStep 489973 = 45935) (by norm_num)
theorem B1096213 : Blo 432776 1096213 := bbase (se 6 (by rfl) ⟨25692, by rfl⟩ : syracuseStep 1096213 = 51385) (by norm_num)
theorem B490009 : Blo 432776 490009 := bbase (se 2 (by rfl) ⟨183753, by rfl⟩ : syracuseStep 490009 = 367507) (by norm_num)
theorem B694813 : Blo 432776 694813 := bbase (se 3 (by rfl) ⟨130277, by rfl⟩ : syracuseStep 694813 = 260555) (by norm_num)
theorem B588325 : Blo 432776 588325 := bbase (se 4 (by rfl) ⟨55155, by rfl⟩ : syracuseStep 588325 = 110311) (by norm_num)
theorem B2087477 : Blo 432776 2087477 := bbase (se 5 (by rfl) ⟨97850, by rfl⟩ : syracuseStep 2087477 = 195701) (by norm_num)
theorem B490045 : Blo 432776 490045 := bbase (se 3 (by rfl) ⟨91883, by rfl⟩ : syracuseStep 490045 = 183767) (by norm_num)
theorem B2374229 : Blo 432776 2374229 := bbase (se 8 (by rfl) ⟨13911, by rfl⟩ : syracuseStep 2374229 = 27823) (by norm_num)
theorem B490081 : Blo 432776 490081 := bbase (se 2 (by rfl) ⟨183780, by rfl⟩ : syracuseStep 490081 = 367561) (by norm_num)
theorem B703085 : Blo 432776 703085 := bbase (se 3 (by rfl) ⟨131828, by rfl⟩ : syracuseStep 703085 = 263657) (by norm_num)
theorem B2341493 : Blo 432776 2341493 := bbase (se 5 (by rfl) ⟨109757, by rfl⟩ : syracuseStep 2341493 = 219515) (by norm_num)
theorem B1096325 : Blo 432776 1096325 := bbase (se 4 (by rfl) ⟨102780, by rfl⟩ : syracuseStep 1096325 = 205561) (by norm_num)
theorem B1464965 : Blo 432776 1464965 := bbase (se 4 (by rfl) ⟨137340, by rfl⟩ : syracuseStep 1464965 = 274681) (by norm_num)
theorem B490117 : Blo 432776 490117 := bbase (se 4 (by rfl) ⟨45948, by rfl⟩ : syracuseStep 490117 = 91897) (by norm_num)
theorem B490153 : Blo 432776 490153 := bbase (se 2 (by rfl) ⟨183807, by rfl⟩ : syracuseStep 490153 = 367615) (by norm_num)
theorem B522941 : Blo 432776 522941 := bbase (se 3 (by rfl) ⟨98051, by rfl⟩ : syracuseStep 522941 = 196103) (by norm_num)
theorem B1112773 : Blo 432776 1112773 := bbase (se 4 (by rfl) ⟨104322, by rfl⟩ : syracuseStep 1112773 = 208645) (by norm_num)
theorem B490189 : Blo 432776 490189 := bbase (se 3 (by rfl) ⟨91910, by rfl⟩ : syracuseStep 490189 = 183821) (by norm_num)
theorem B490225 : Blo 432776 490225 := bbase (se 2 (by rfl) ⟨183834, by rfl⟩ : syracuseStep 490225 = 367669) (by norm_num)
theorem B1653493 : Blo 432776 1653493 := bbase (se 5 (by rfl) ⟨77507, by rfl⟩ : syracuseStep 1653493 = 155015) (by norm_num)
theorem B826109 : Blo 432776 826109 := bbase (se 3 (by rfl) ⟨154895, by rfl⟩ : syracuseStep 826109 = 309791) (by norm_num)
theorem B2202389 : Blo 432776 2202389 := bbase (se 6 (by rfl) ⟨51618, by rfl⟩ : syracuseStep 2202389 = 103237) (by norm_num)
theorem B1096517 : Blo 432776 1096517 := bbase (se 4 (by rfl) ⟨102798, by rfl⟩ : syracuseStep 1096517 = 205597) (by norm_num)
theorem B2087765 : Blo 432776 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B523109 : Blo 432776 523109 := bbase (se 4 (by rfl) ⟨49041, by rfl⟩ : syracuseStep 523109 = 98083) (by norm_num)
theorem B1235861 : Blo 432776 1235861 := bbase (se 6 (by rfl) ⟨28965, by rfl⟩ : syracuseStep 1235861 = 57931) (by norm_num)
theorem B662437 : Blo 432776 662437 := bbase (se 4 (by rfl) ⟨62103, by rfl⟩ : syracuseStep 662437 = 124207) (by norm_num)
theorem B973781 : Blo 432776 973781 := bbase (se 7 (by rfl) ⟨11411, by rfl⟩ : syracuseStep 973781 = 22823) (by norm_num)
theorem B695261 : Blo 432776 695261 := bbase (se 3 (by rfl) ⟨130361, by rfl⟩ : syracuseStep 695261 = 260723) (by norm_num)
theorem B547813 : Blo 432776 547813 := bbase (se 4 (by rfl) ⟨51357, by rfl⟩ : syracuseStep 547813 = 102715) (by norm_num)
theorem B973853 : Blo 432776 973853 := bbase (se 3 (by rfl) ⟨182597, by rfl⟩ : syracuseStep 973853 = 365195) (by norm_num)
theorem B924709 : Blo 432776 924709 := bbase (se 4 (by rfl) ⟨86691, by rfl⟩ : syracuseStep 924709 = 173383) (by norm_num)
theorem B1653797 : Blo 432776 1653797 := bbase (se 4 (by rfl) ⟨155043, by rfl⟩ : syracuseStep 1653797 = 310087) (by norm_num)
theorem B1465397 : Blo 432776 1465397 := bbase (se 5 (by rfl) ⟨68690, by rfl⟩ : syracuseStep 1465397 = 137381) (by norm_num)
theorem B564305 : Blo 432776 564305 := bbase (se 2 (by rfl) ⟨211614, by rfl⟩ : syracuseStep 564305 = 423229) (by norm_num)
theorem B973925 : Blo 432776 973925 := bbase (se 4 (by rfl) ⟨91305, by rfl⟩ : syracuseStep 973925 = 182611) (by norm_num)
theorem B547985 : Blo 432776 547985 := bbase (se 2 (by rfl) ⟨205494, by rfl⟩ : syracuseStep 547985 = 410989) (by norm_num)
theorem B1645717 : Blo 432776 1645717 := bbase (se 6 (by rfl) ⟨38571, by rfl⟩ : syracuseStep 1645717 = 77143) (by norm_num)
theorem B523417 : Blo 432776 523417 := bbase (se 2 (by rfl) ⟨196281, by rfl⟩ : syracuseStep 523417 = 392563) (by norm_num)
theorem B1096861 : Blo 432776 1096861 := bbase (se 3 (by rfl) ⟨205661, by rfl⟩ : syracuseStep 1096861 = 411323) (by norm_num)
theorem B695461 : Blo 432776 695461 := bbase (se 4 (by rfl) ⟨65199, by rfl⟩ : syracuseStep 695461 = 130399) (by norm_num)
theorem B973997 : Blo 432776 973997 := bbase (se 3 (by rfl) ⟨182624, by rfl⟩ : syracuseStep 973997 = 365249) (by norm_num)
theorem B2194613 : Blo 432776 2194613 := bbase (se 5 (by rfl) ⟨102872, by rfl⟩ : syracuseStep 2194613 = 205745) (by norm_num)
theorem B2645173 : Blo 432776 2645173 := bbase (se 5 (by rfl) ⟨123992, by rfl⟩ : syracuseStep 2645173 = 247985) (by norm_num)
theorem B548041 : Blo 432776 548041 := bbase (se 2 (by rfl) ⟨205515, by rfl⟩ : syracuseStep 548041 = 411031) (by norm_num)
theorem B670933 : Blo 432776 670933 := bbase (se 7 (by rfl) ⟨7862, by rfl⟩ : syracuseStep 670933 = 15725) (by norm_num)
theorem B1850597 : Blo 432776 1850597 := bbase (se 4 (by rfl) ⟨173493, by rfl⟩ : syracuseStep 1850597 = 346987) (by norm_num)
theorem B974069 : Blo 432776 974069 := bbase (se 5 (by rfl) ⟨45659, by rfl⟩ : syracuseStep 974069 = 91319) (by norm_num)
theorem B1785077 : Blo 432776 1785077 := bbase (se 5 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 1785077 = 167351) (by norm_num)
theorem B1096973 : Blo 432776 1096973 := bbase (se 3 (by rfl) ⟨205682, by rfl⟩ : syracuseStep 1096973 = 411365) (by norm_num)
theorem B548137 : Blo 432776 548137 := bbase (se 2 (by rfl) ⟨205551, by rfl⟩ : syracuseStep 548137 = 411103) (by norm_num)
theorem B556345 : Blo 432776 556345 := bbase (se 2 (by rfl) ⟨208629, by rfl⟩ : syracuseStep 556345 = 417259) (by norm_num)
theorem B974141 : Blo 432776 974141 := bbase (se 3 (by rfl) ⟨182651, by rfl⟩ : syracuseStep 974141 = 365303) (by norm_num)
theorem B1236293 : Blo 432776 1236293 := bbase (se 4 (by rfl) ⟨115902, by rfl⟩ : syracuseStep 1236293 = 231805) (by norm_num)
theorem B974213 : Blo 432776 974213 := bbase (se 4 (by rfl) ⟨91332, by rfl⟩ : syracuseStep 974213 = 182665) (by norm_num)
theorem B695717 : Blo 432776 695717 := bbase (se 4 (by rfl) ⟨65223, by rfl⟩ : syracuseStep 695717 = 130447) (by norm_num)
theorem B1646021 : Blo 432776 1646021 := bbase (se 4 (by rfl) ⟨154314, by rfl⟩ : syracuseStep 1646021 = 308629) (by norm_num)
theorem B974285 : Blo 432776 974285 := bbase (se 3 (by rfl) ⟨182678, by rfl⟩ : syracuseStep 974285 = 365357) (by norm_num)
theorem B1097165 : Blo 432776 1097165 := bbase (se 3 (by rfl) ⟨205718, by rfl⟩ : syracuseStep 1097165 = 411437) (by norm_num)
theorem B548309 : Blo 432776 548309 := bbase (se 7 (by rfl) ⟨6425, by rfl⟩ : syracuseStep 548309 = 12851) (by norm_num)
theorem B1465829 : Blo 432776 1465829 := bbase (se 4 (by rfl) ⟨137421, by rfl⟩ : syracuseStep 1465829 = 274843) (by norm_num)
theorem B826861 : Blo 432776 826861 := bbase (se 3 (by rfl) ⟨155036, by rfl⟩ : syracuseStep 826861 = 310073) (by norm_num)
theorem B548365 : Blo 432776 548365 := bbase (se 3 (by rfl) ⟨102818, by rfl⟩ : syracuseStep 548365 = 205637) (by norm_num)
theorem B974357 : Blo 432776 974357 := bbase (se 6 (by rfl) ⟨22836, by rfl⟩ : syracuseStep 974357 = 45673) (by norm_num)
theorem B974429 : Blo 432776 974429 := bbase (se 3 (by rfl) ⟨182705, by rfl⟩ : syracuseStep 974429 = 365411) (by norm_num)
theorem B548461 : Blo 432776 548461 := bbase (se 3 (by rfl) ⟨102836, by rfl⟩ : syracuseStep 548461 = 205673) (by norm_num)
theorem B3309173 : Blo 432776 3309173 := bbase (se 5 (by rfl) ⟨155117, by rfl⟩ : syracuseStep 3309173 = 310235) (by norm_num)
theorem B827005 : Blo 432776 827005 := bbase (se 3 (by rfl) ⟨155063, by rfl⟩ : syracuseStep 827005 = 310127) (by norm_num)
theorem B974501 : Blo 432776 974501 := bbase (se 4 (by rfl) ⟨91359, by rfl⟩ : syracuseStep 974501 = 182719) (by norm_num)
theorem B974573 : Blo 432776 974573 := bbase (se 3 (by rfl) ⟨182732, by rfl⟩ : syracuseStep 974573 = 365465) (by norm_num)
theorem B1408757 : Blo 432776 1408757 := bbase (se 5 (by rfl) ⟨66035, by rfl⟩ : syracuseStep 1408757 = 132071) (by norm_num)
theorem B548633 : Blo 432776 548633 := bbase (se 2 (by rfl) ⟨205737, by rfl⟩ : syracuseStep 548633 = 411475) (by norm_num)
theorem B827165 : Blo 432776 827165 := bbase (se 3 (by rfl) ⟨155093, by rfl⟩ : syracuseStep 827165 = 310187) (by norm_num)
theorem B1097509 : Blo 432776 1097509 := bbase (se 4 (by rfl) ⟨102891, by rfl⟩ : syracuseStep 1097509 = 205783) (by norm_num)
theorem B974645 : Blo 432776 974645 := bbase (se 5 (by rfl) ⟨45686, by rfl⟩ : syracuseStep 974645 = 91373) (by norm_num)
theorem B507713 : Blo 432776 507713 := bbase (se 2 (by rfl) ⟨190392, by rfl⟩ : syracuseStep 507713 = 380785) (by norm_num)
theorem B548689 : Blo 432776 548689 := bbase (se 2 (by rfl) ⟨205758, by rfl⟩ : syracuseStep 548689 = 411517) (by norm_num)
theorem B5930837 : Blo 432776 5930837 := bbase (se 9 (by rfl) ⟨17375, by rfl⟩ : syracuseStep 5930837 = 34751) (by norm_num)
theorem B1859429 : Blo 432776 1859429 := bbase (se 4 (by rfl) ⟨174321, by rfl⟩ : syracuseStep 1859429 = 348643) (by norm_num)
theorem B974717 : Blo 432776 974717 := bbase (se 3 (by rfl) ⟨182759, by rfl⟩ : syracuseStep 974717 = 365519) (by norm_num)
theorem B1097621 : Blo 432776 1097621 := bbase (se 6 (by rfl) ⟨25725, by rfl⟩ : syracuseStep 1097621 = 51451) (by norm_num)
theorem B1466261 : Blo 432776 1466261 := bbase (se 6 (by rfl) ⟨34365, by rfl⟩ : syracuseStep 1466261 = 68731) (by norm_num)
theorem B925597 : Blo 432776 925597 := bbase (se 3 (by rfl) ⟨173549, by rfl⟩ : syracuseStep 925597 = 347099) (by norm_num)
theorem B548785 : Blo 432776 548785 := bbase (se 2 (by rfl) ⟨205794, by rfl⟩ : syracuseStep 548785 = 411589) (by norm_num)
theorem B974789 : Blo 432776 974789 := bbase (se 4 (by rfl) ⟨91386, by rfl⟩ : syracuseStep 974789 = 182773) (by norm_num)
theorem B434179 : Blo 432776 434179 := bstep (se 1 (by rfl) ⟨325634, by rfl⟩ : syracuseStep 434179 = 651269) B651269
theorem B434195 : Blo 432776 434195 := bstep (se 1 (by rfl) ⟨325646, by rfl⟩ : syracuseStep 434195 = 651293) B651293
theorem B434211 : Blo 432776 434211 := bstep (se 1 (by rfl) ⟨325658, by rfl⟩ : syracuseStep 434211 = 651317) B651317
theorem B966691 : Blo 432776 966691 := bstep (se 1 (by rfl) ⟨725018, by rfl⟩ : syracuseStep 966691 = 1450037) B1450037
theorem B974897 : Blo 432776 974897 := bstep (se 2 (by rfl) ⟨365586, by rfl⟩ : syracuseStep 974897 = 731173) B731173
theorem B434227 : Blo 432776 434227 := bstep (se 1 (by rfl) ⟨325670, by rfl⟩ : syracuseStep 434227 = 651341) B651341
theorem B974915 : Blo 432776 974915 := bstep (se 1 (by rfl) ⟨731186, by rfl⟩ : syracuseStep 974915 = 1462373) B1462373
theorem B434243 : Blo 432776 434243 := bstep (se 1 (by rfl) ⟨325682, by rfl⟩ : syracuseStep 434243 = 651365) B651365
theorem B548947 : Blo 432776 548947 := bstep (se 1 (by rfl) ⟨411710, by rfl⟩ : syracuseStep 548947 = 823421) B823421
theorem B434259 : Blo 432776 434259 := bstep (se 1 (by rfl) ⟨325694, by rfl⟩ : syracuseStep 434259 = 651389) B651389
theorem B434275 : Blo 432776 434275 := bstep (se 1 (by rfl) ⟨325706, by rfl⟩ : syracuseStep 434275 = 651413) B651413
theorem B3719267 : Blo 432776 3719267 := bstep (se 1 (by rfl) ⟨2789450, by rfl⟩ : syracuseStep 3719267 = 5578901) B5578901
theorem B1466477 : Blo 432776 1466477 := bstep (se 3 (by rfl) ⟨274964, by rfl⟩ : syracuseStep 1466477 = 549929) B549929
theorem B434291 : Blo 432776 434291 := bstep (se 1 (by rfl) ⟨325718, by rfl⟩ : syracuseStep 434291 = 651437) B651437
theorem B434307 : Blo 432776 434307 := bstep (se 1 (by rfl) ⟨325730, by rfl⟩ : syracuseStep 434307 = 651461) B651461
theorem B2384005 : Blo 432776 2384005 := bstep (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) B447001
theorem B1171601 : Blo 432776 1171601 := bstep (se 2 (by rfl) ⟨439350, by rfl⟩ : syracuseStep 1171601 = 878701) B878701
theorem B434323 : Blo 432776 434323 := bstep (se 1 (by rfl) ⟨325742, by rfl⟩ : syracuseStep 434323 = 651485) B651485
theorem B434339 : Blo 432776 434339 := bstep (se 1 (by rfl) ⟨325754, by rfl⟩ : syracuseStep 434339 = 651509) B651509
theorem B1466531 : Blo 432776 1466531 := bstep (se 1 (by rfl) ⟨1099898, by rfl⟩ : syracuseStep 1466531 = 2199797) B2199797
theorem B1851569 : Blo 432776 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B434355 : Blo 432776 434355 := bstep (se 1 (by rfl) ⟨325766, by rfl⟩ : syracuseStep 434355 = 651533) B651533
theorem B434371 : Blo 432776 434371 := bstep (se 1 (by rfl) ⟨325778, by rfl⟩ : syracuseStep 434371 = 651557) B651557
theorem B434387 : Blo 432776 434387 := bstep (se 1 (by rfl) ⟨325790, by rfl⟩ : syracuseStep 434387 = 651581) B651581
theorem B434403 : Blo 432776 434403 := bstep (se 1 (by rfl) ⟨325802, by rfl⟩ : syracuseStep 434403 = 651605) B651605
theorem B3711203 : Blo 432776 3711203 := bstep (se 1 (by rfl) ⟨2783402, by rfl⟩ : syracuseStep 3711203 = 5566805) B5566805
theorem B434419 : Blo 432776 434419 := bstep (se 1 (by rfl) ⟨325814, by rfl⟩ : syracuseStep 434419 = 651629) B651629
theorem B434435 : Blo 432776 434435 := bstep (se 1 (by rfl) ⟨325826, by rfl⟩ : syracuseStep 434435 = 651653) B651653
theorem B434451 : Blo 432776 434451 := bstep (se 1 (by rfl) ⟨325838, by rfl⟩ : syracuseStep 434451 = 651677) B651677
theorem B2195747 : Blo 432776 2195747 := bstep (se 1 (by rfl) ⟨1646810, by rfl⟩ : syracuseStep 2195747 = 3293621) B3293621
theorem B434467 : Blo 432776 434467 := bstep (se 1 (by rfl) ⟨325850, by rfl⟩ : syracuseStep 434467 = 651701) B651701
theorem B434483 : Blo 432776 434483 := bstep (se 1 (by rfl) ⟨325862, by rfl⟩ : syracuseStep 434483 = 651725) B651725
theorem B1114435 : Blo 432776 1114435 := bstep (se 1 (by rfl) ⟨835826, by rfl⟩ : syracuseStep 1114435 = 1671653) B1671653
theorem B434499 : Blo 432776 434499 := bstep (se 1 (by rfl) ⟨325874, by rfl⟩ : syracuseStep 434499 = 651749) B651749
theorem B794947 : Blo 432776 794947 := bstep (se 1 (by rfl) ⟨596210, by rfl⟩ : syracuseStep 794947 = 1192421) B1192421
theorem B975185 : Blo 432776 975185 := bstep (se 2 (by rfl) ⟨365694, by rfl⟩ : syracuseStep 975185 = 731389) B731389
theorem B434515 : Blo 432776 434515 := bstep (se 1 (by rfl) ⟨325886, by rfl⟩ : syracuseStep 434515 = 651773) B651773
theorem B975203 : Blo 432776 975203 := bstep (se 1 (by rfl) ⟨731402, by rfl⟩ : syracuseStep 975203 = 1462805) B1462805
theorem B434531 : Blo 432776 434531 := bstep (se 1 (by rfl) ⟨325898, by rfl⟩ : syracuseStep 434531 = 651797) B651797
theorem B434547 : Blo 432776 434547 := bstep (se 1 (by rfl) ⟨325910, by rfl⟩ : syracuseStep 434547 = 651821) B651821
theorem B696691 : Blo 432776 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B434563 : Blo 432776 434563 := bstep (se 1 (by rfl) ⟨325922, by rfl⟩ : syracuseStep 434563 = 651845) B651845
theorem B434579 : Blo 432776 434579 := bstep (se 1 (by rfl) ⟨325934, by rfl⟩ : syracuseStep 434579 = 651869) B651869
theorem B434595 : Blo 432776 434595 := bstep (se 1 (by rfl) ⟨325946, by rfl⟩ : syracuseStep 434595 = 651893) B651893
theorem B1466801 : Blo 432776 1466801 := bstep (se 2 (by rfl) ⟨550050, by rfl⟩ : syracuseStep 1466801 = 1100101) B1100101
theorem B434611 : Blo 432776 434611 := bstep (se 1 (by rfl) ⟨325958, by rfl⟩ : syracuseStep 434611 = 651917) B651917
theorem B434627 : Blo 432776 434627 := bstep (se 1 (by rfl) ⟨325970, by rfl⟩ : syracuseStep 434627 = 651941) B651941
theorem B434643 : Blo 432776 434643 := bstep (se 1 (by rfl) ⟨325982, by rfl⟩ : syracuseStep 434643 = 651965) B651965
theorem B4948451 : Blo 432776 4948451 := bstep (se 1 (by rfl) ⟨3711338, by rfl⟩ : syracuseStep 4948451 = 7422677) B7422677
theorem B434659 : Blo 432776 434659 := bstep (se 1 (by rfl) ⟨325994, by rfl⟩ : syracuseStep 434659 = 651989) B651989
theorem B434675 : Blo 432776 434675 := bstep (se 1 (by rfl) ⟨326006, by rfl⟩ : syracuseStep 434675 = 652013) B652013
theorem B434691 : Blo 432776 434691 := bstep (se 1 (by rfl) ⟨326018, by rfl⟩ : syracuseStep 434691 = 652037) B652037
theorem B4186637 : Blo 432776 4186637 := bstep (se 3 (by rfl) ⟨784994, by rfl⟩ : syracuseStep 4186637 = 1569989) B1569989
theorem B434707 : Blo 432776 434707 := bstep (se 1 (by rfl) ⟨326030, by rfl⟩ : syracuseStep 434707 = 652061) B652061
theorem B434723 : Blo 432776 434723 := bstep (se 1 (by rfl) ⟨326042, by rfl⟩ : syracuseStep 434723 = 652085) B652085
theorem B434739 : Blo 432776 434739 := bstep (se 1 (by rfl) ⟨326054, by rfl⟩ : syracuseStep 434739 = 652109) B652109
theorem B549443 : Blo 432776 549443 := bstep (se 1 (by rfl) ⟨412082, by rfl⟩ : syracuseStep 549443 = 824165) B824165
theorem B434755 : Blo 432776 434755 := bstep (se 1 (by rfl) ⟨326066, by rfl⟩ : syracuseStep 434755 = 652133) B652133
theorem B1565261 : Blo 432776 1565261 := bstep (se 3 (by rfl) ⟨293486, by rfl⟩ : syracuseStep 1565261 = 586973) B586973
theorem B434771 : Blo 432776 434771 := bstep (se 1 (by rfl) ⟨326078, by rfl⟩ : syracuseStep 434771 = 652157) B652157
theorem B434787 : Blo 432776 434787 := bstep (se 1 (by rfl) ⟨326090, by rfl⟩ : syracuseStep 434787 = 652181) B652181
theorem B975473 : Blo 432776 975473 := bstep (se 2 (by rfl) ⟨365802, by rfl⟩ : syracuseStep 975473 = 731605) B731605
theorem B434803 : Blo 432776 434803 := bstep (se 1 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 434803 = 652205) B652205
theorem B975491 : Blo 432776 975491 := bstep (se 1 (by rfl) ⟨731618, by rfl⟩ : syracuseStep 975491 = 1463237) B1463237
theorem B434819 : Blo 432776 434819 := bstep (se 1 (by rfl) ⟨326114, by rfl⟩ : syracuseStep 434819 = 652229) B652229
theorem B434835 : Blo 432776 434835 := bstep (se 1 (by rfl) ⟨326126, by rfl⟩ : syracuseStep 434835 = 652253) B652253
theorem B434851 : Blo 432776 434851 := bstep (se 1 (by rfl) ⟨326138, by rfl⟩ : syracuseStep 434851 = 652277) B652277
theorem B434867 : Blo 432776 434867 := bstep (se 1 (by rfl) ⟨326150, by rfl⟩ : syracuseStep 434867 = 652301) B652301
theorem B5415605 : Blo 432776 5415605 := bstep (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) B507713
theorem B434883 : Blo 432776 434883 := bstep (se 1 (by rfl) ⟨326162, by rfl⟩ : syracuseStep 434883 = 652325) B652325
theorem B1172173 : Blo 432776 1172173 := bstep (se 3 (by rfl) ⟨219782, by rfl⟩ : syracuseStep 1172173 = 439565) B439565
theorem B926417 : Blo 432776 926417 := bstep (se 2 (by rfl) ⟨347406, by rfl⟩ : syracuseStep 926417 = 694813) B694813
theorem B434899 : Blo 432776 434899 := bstep (se 1 (by rfl) ⟨326174, by rfl⟩ : syracuseStep 434899 = 652349) B652349
theorem B434915 : Blo 432776 434915 := bstep (se 1 (by rfl) ⟨326186, by rfl⟩ : syracuseStep 434915 = 652373) B652373
theorem B1098481 : Blo 432776 1098481 := bstep (se 2 (by rfl) ⟨411930, by rfl⟩ : syracuseStep 1098481 = 823861) B823861
theorem B434931 : Blo 432776 434931 := bstep (se 1 (by rfl) ⟨326198, by rfl⟩ : syracuseStep 434931 = 652397) B652397
theorem B434947 : Blo 432776 434947 := bstep (se 1 (by rfl) ⟨326210, by rfl⟩ : syracuseStep 434947 = 652421) B652421
theorem B2450189 : Blo 432776 2450189 := bstep (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) B918821
theorem B434963 : Blo 432776 434963 := bstep (se 1 (by rfl) ⟨326222, by rfl⟩ : syracuseStep 434963 = 652445) B652445
theorem B1254179 : Blo 432776 1254179 := bstep (se 1 (by rfl) ⟨940634, by rfl⟩ : syracuseStep 1254179 = 1881269) B1881269
theorem B434979 : Blo 432776 434979 := bstep (se 1 (by rfl) ⟨326234, by rfl⟩ : syracuseStep 434979 = 652469) B652469
theorem B434995 : Blo 432776 434995 := bstep (se 1 (by rfl) ⟨326246, by rfl⟩ : syracuseStep 434995 = 652493) B652493
theorem B435011 : Blo 432776 435011 := bstep (se 1 (by rfl) ⟨326258, by rfl⟩ : syracuseStep 435011 = 652517) B652517
theorem B435027 : Blo 432776 435027 := bstep (se 1 (by rfl) ⟨326270, by rfl⟩ : syracuseStep 435027 = 652541) B652541
theorem B2786147 : Blo 432776 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B435043 : Blo 432776 435043 := bstep (se 1 (by rfl) ⟨326282, by rfl⟩ : syracuseStep 435043 = 652565) B652565
theorem B2777969 : Blo 432776 2777969 := bstep (se 2 (by rfl) ⟨1041738, by rfl⟩ : syracuseStep 2777969 = 2083477) B2083477
theorem B435059 : Blo 432776 435059 := bstep (se 1 (by rfl) ⟨326294, by rfl⟩ : syracuseStep 435059 = 652589) B652589
theorem B435075 : Blo 432776 435075 := bstep (se 1 (by rfl) ⟨326306, by rfl⟩ : syracuseStep 435075 = 652613) B652613
theorem B975761 : Blo 432776 975761 := bstep (se 2 (by rfl) ⟨365910, by rfl⟩ : syracuseStep 975761 = 731821) B731821
theorem B435091 : Blo 432776 435091 := bstep (se 1 (by rfl) ⟨326318, by rfl⟩ : syracuseStep 435091 = 652637) B652637
theorem B975779 : Blo 432776 975779 := bstep (se 1 (by rfl) ⟨731834, by rfl⟩ : syracuseStep 975779 = 1463669) B1463669
theorem B557987 : Blo 432776 557987 := bstep (se 1 (by rfl) ⟨418490, by rfl⟩ : syracuseStep 557987 = 836981) B836981
theorem B435107 : Blo 432776 435107 := bstep (se 1 (by rfl) ⟨326330, by rfl⟩ : syracuseStep 435107 = 652661) B652661
theorem B1237933 : Blo 432776 1237933 := bstep (se 3 (by rfl) ⟨232112, by rfl⟩ : syracuseStep 1237933 = 464225) B464225
theorem B1483697 : Blo 432776 1483697 := bstep (se 2 (by rfl) ⟨556386, by rfl⟩ : syracuseStep 1483697 = 1112773) B1112773
theorem B435123 : Blo 432776 435123 := bstep (se 1 (by rfl) ⟨326342, by rfl⟩ : syracuseStep 435123 = 652685) B652685
theorem B435139 : Blo 432776 435139 := bstep (se 1 (by rfl) ⟨326354, by rfl⟩ : syracuseStep 435139 = 652709) B652709
theorem B1467341 : Blo 432776 1467341 := bstep (se 3 (by rfl) ⟨275126, by rfl⟩ : syracuseStep 1467341 = 550253) B550253
theorem B435155 : Blo 432776 435155 := bstep (se 1 (by rfl) ⟨326366, by rfl⟩ : syracuseStep 435155 = 652733) B652733
theorem B435171 : Blo 432776 435171 := bstep (se 1 (by rfl) ⟨326378, by rfl⟩ : syracuseStep 435171 = 652757) B652757
theorem B2204657 : Blo 432776 2204657 := bstep (se 2 (by rfl) ⟨826746, by rfl⟩ : syracuseStep 2204657 = 1653493) B1653493
theorem B435187 : Blo 432776 435187 := bstep (se 1 (by rfl) ⟨326390, by rfl⟩ : syracuseStep 435187 = 652781) B652781
theorem B1098755 : Blo 432776 1098755 := bstep (se 1 (by rfl) ⟨824066, by rfl⟩ : syracuseStep 1098755 = 1648133) B1648133
theorem B1467395 : Blo 432776 1467395 := bstep (se 1 (by rfl) ⟨1100546, by rfl⟩ : syracuseStep 1467395 = 2201093) B2201093
theorem B435203 : Blo 432776 435203 := bstep (se 1 (by rfl) ⟨326402, by rfl⟩ : syracuseStep 435203 = 652805) B652805
theorem B435219 : Blo 432776 435219 := bstep (se 1 (by rfl) ⟨326414, by rfl⟩ : syracuseStep 435219 = 652829) B652829
theorem B435235 : Blo 432776 435235 := bstep (se 1 (by rfl) ⟨326426, by rfl⟩ : syracuseStep 435235 = 652853) B652853
theorem B435251 : Blo 432776 435251 := bstep (se 1 (by rfl) ⟨326438, by rfl⟩ : syracuseStep 435251 = 652877) B652877
theorem B435267 : Blo 432776 435267 := bstep (se 1 (by rfl) ⟨326450, by rfl⟩ : syracuseStep 435267 = 652901) B652901
theorem B2196557 : Blo 432776 2196557 := bstep (se 3 (by rfl) ⟨411854, by rfl⟩ : syracuseStep 2196557 = 823709) B823709
theorem B1172561 : Blo 432776 1172561 := bstep (se 2 (by rfl) ⟨439710, by rfl⟩ : syracuseStep 1172561 = 879421) B879421
theorem B435283 : Blo 432776 435283 := bstep (se 1 (by rfl) ⟨326462, by rfl⟩ : syracuseStep 435283 = 652925) B652925
theorem B435299 : Blo 432776 435299 := bstep (se 1 (by rfl) ⟨326474, by rfl⟩ : syracuseStep 435299 = 652949) B652949
theorem B435315 : Blo 432776 435315 := bstep (se 1 (by rfl) ⟨326486, by rfl⟩ : syracuseStep 435315 = 652973) B652973
theorem B435331 : Blo 432776 435331 := bstep (se 1 (by rfl) ⟨326498, by rfl⟩ : syracuseStep 435331 = 652997) B652997
theorem B1238161 : Blo 432776 1238161 := bstep (se 2 (by rfl) ⟨464310, by rfl⟩ : syracuseStep 1238161 = 928621) B928621
theorem B705683 : Blo 432776 705683 := bstep (se 1 (by rfl) ⟨529262, by rfl⟩ : syracuseStep 705683 = 1058525) B1058525
theorem B435347 : Blo 432776 435347 := bstep (se 1 (by rfl) ⟨326510, by rfl⟩ : syracuseStep 435347 = 653021) B653021
theorem B435363 : Blo 432776 435363 := bstep (se 1 (by rfl) ⟨326522, by rfl⟩ : syracuseStep 435363 = 653045) B653045
theorem B976049 : Blo 432776 976049 := bstep (se 2 (by rfl) ⟨366018, by rfl⟩ : syracuseStep 976049 = 732037) B732037
theorem B435379 : Blo 432776 435379 := bstep (se 1 (by rfl) ⟨326534, by rfl⟩ : syracuseStep 435379 = 653069) B653069
theorem B976067 : Blo 432776 976067 := bstep (se 1 (by rfl) ⟨732050, by rfl⟩ : syracuseStep 976067 = 1464101) B1464101
theorem B1098947 : Blo 432776 1098947 := bstep (se 1 (by rfl) ⟨824210, by rfl⟩ : syracuseStep 1098947 = 1648421) B1648421
theorem B435395 : Blo 432776 435395 := bstep (se 1 (by rfl) ⟨326546, by rfl⟩ : syracuseStep 435395 = 653093) B653093
theorem B435411 : Blo 432776 435411 := bstep (se 1 (by rfl) ⟨326558, by rfl⟩ : syracuseStep 435411 = 653117) B653117
theorem B435427 : Blo 432776 435427 := bstep (se 1 (by rfl) ⟨326570, by rfl⟩ : syracuseStep 435427 = 653141) B653141
theorem B2090225 : Blo 432776 2090225 := bstep (se 2 (by rfl) ⟨783834, by rfl⟩ : syracuseStep 2090225 = 1567669) B1567669
theorem B435443 : Blo 432776 435443 := bstep (se 1 (by rfl) ⟨326582, by rfl⟩ : syracuseStep 435443 = 653165) B653165
theorem B566515 : Blo 432776 566515 := bstep (se 1 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 566515 = 849773) B849773
theorem B550147 : Blo 432776 550147 := bstep (se 1 (by rfl) ⟨412610, by rfl⟩ : syracuseStep 550147 = 825221) B825221
theorem B435459 : Blo 432776 435459 := bstep (se 1 (by rfl) ⟨326594, by rfl⟩ : syracuseStep 435459 = 653189) B653189
theorem B1467665 : Blo 432776 1467665 := bstep (se 2 (by rfl) ⟨550374, by rfl⟩ : syracuseStep 1467665 = 1100749) B1100749
theorem B435475 : Blo 432776 435475 := bstep (se 1 (by rfl) ⟨326606, by rfl⟩ : syracuseStep 435475 = 653213) B653213
theorem B697619 : Blo 432776 697619 := bstep (se 1 (by rfl) ⟨523214, by rfl⟩ : syracuseStep 697619 = 1046429) B1046429
theorem B435491 : Blo 432776 435491 := bstep (se 1 (by rfl) ⟨326618, by rfl⟩ : syracuseStep 435491 = 653237) B653237
theorem B730417 : Blo 432776 730417 := bstep (se 2 (by rfl) ⟨273906, by rfl⟩ : syracuseStep 730417 = 547813) B547813
theorem B1238321 : Blo 432776 1238321 := bstep (se 2 (by rfl) ⟨464370, by rfl⟩ : syracuseStep 1238321 = 928741) B928741
theorem B435507 : Blo 432776 435507 := bstep (se 1 (by rfl) ⟨326630, by rfl⟩ : syracuseStep 435507 = 653261) B653261
theorem B1041731 : Blo 432776 1041731 := bstep (se 1 (by rfl) ⟨781298, by rfl⟩ : syracuseStep 1041731 = 1562597) B1562597
theorem B435523 : Blo 432776 435523 := bstep (se 1 (by rfl) ⟨326642, by rfl⟩ : syracuseStep 435523 = 653285) B653285
theorem B730451 : Blo 432776 730451 := bstep (se 1 (by rfl) ⟨547838, by rfl⟩ : syracuseStep 730451 = 1095677) B1095677
theorem B435539 : Blo 432776 435539 := bstep (se 1 (by rfl) ⟨326654, by rfl⟩ : syracuseStep 435539 = 653309) B653309
theorem B550243 : Blo 432776 550243 := bstep (se 1 (by rfl) ⟨412682, by rfl⟩ : syracuseStep 550243 = 825365) B825365
theorem B435555 : Blo 432776 435555 := bstep (se 1 (by rfl) ⟨326666, by rfl⟩ : syracuseStep 435555 = 653333) B653333
theorem B435571 : Blo 432776 435571 := bstep (se 1 (by rfl) ⟨326678, by rfl⟩ : syracuseStep 435571 = 653357) B653357
theorem B435587 : Blo 432776 435587 := bstep (se 1 (by rfl) ⟨326690, by rfl⟩ : syracuseStep 435587 = 653381) B653381
theorem B435603 : Blo 432776 435603 := bstep (se 1 (by rfl) ⟨326702, by rfl⟩ : syracuseStep 435603 = 653405) B653405
theorem B1238435 : Blo 432776 1238435 := bstep (se 1 (by rfl) ⟨928826, by rfl⟩ : syracuseStep 1238435 = 1857653) B1857653
theorem B435619 : Blo 432776 435619 := bstep (se 1 (by rfl) ⟨326714, by rfl⟩ : syracuseStep 435619 = 653429) B653429
theorem B435635 : Blo 432776 435635 := bstep (se 1 (by rfl) ⟨326726, by rfl⟩ : syracuseStep 435635 = 653453) B653453
theorem B435651 : Blo 432776 435651 := bstep (se 1 (by rfl) ⟨326738, by rfl⟩ : syracuseStep 435651 = 653477) B653477
theorem B1861069 : Blo 432776 1861069 := bstep (se 3 (by rfl) ⟨348950, by rfl⟩ : syracuseStep 1861069 = 697901) B697901
theorem B976337 : Blo 432776 976337 := bstep (se 2 (by rfl) ⟨366126, by rfl⟩ : syracuseStep 976337 = 732253) B732253
theorem B730579 : Blo 432776 730579 := bstep (se 1 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 730579 = 1095869) B1095869
theorem B435667 : Blo 432776 435667 := bstep (se 1 (by rfl) ⟨326750, by rfl⟩ : syracuseStep 435667 = 653501) B653501
theorem B976355 : Blo 432776 976355 := bstep (se 1 (by rfl) ⟨732266, by rfl⟩ : syracuseStep 976355 = 1464533) B1464533
theorem B435683 : Blo 432776 435683 := bstep (se 1 (by rfl) ⟨326762, by rfl⟩ : syracuseStep 435683 = 653525) B653525
theorem B435699 : Blo 432776 435699 := bstep (se 1 (by rfl) ⟨326774, by rfl⟩ : syracuseStep 435699 = 653549) B653549
theorem B435715 : Blo 432776 435715 := bstep (se 1 (by rfl) ⟨326786, by rfl⟩ : syracuseStep 435715 = 653573) B653573
theorem B435731 : Blo 432776 435731 := bstep (se 1 (by rfl) ⟨326798, by rfl⟩ : syracuseStep 435731 = 653597) B653597
theorem B697889 : Blo 432776 697889 := bstep (se 2 (by rfl) ⟨261708, by rfl⟩ : syracuseStep 697889 = 523417) B523417
theorem B435747 : Blo 432776 435747 := bstep (se 1 (by rfl) ⟨326810, by rfl⟩ : syracuseStep 435747 = 653621) B653621
theorem B927281 : Blo 432776 927281 := bstep (se 2 (by rfl) ⟨347730, by rfl⟩ : syracuseStep 927281 = 695461) B695461
theorem B706099 : Blo 432776 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B435763 : Blo 432776 435763 := bstep (se 1 (by rfl) ⟨326822, by rfl⟩ : syracuseStep 435763 = 653645) B653645
theorem B730721 : Blo 432776 730721 := bstep (se 2 (by rfl) ⟨274020, by rfl⟩ : syracuseStep 730721 = 548041) B548041
theorem B730849 : Blo 432776 730849 := bstep (se 2 (by rfl) ⟨274068, by rfl⟩ : syracuseStep 730849 = 548137) B548137
theorem B976625 : Blo 432776 976625 := bstep (se 2 (by rfl) ⟨366234, by rfl⟩ : syracuseStep 976625 = 732469) B732469
theorem B4835057 : Blo 432776 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B730883 : Blo 432776 730883 := bstep (se 1 (by rfl) ⟨548162, by rfl⟩ : syracuseStep 730883 = 1096325) B1096325
theorem B976643 : Blo 432776 976643 := bstep (se 1 (by rfl) ⟨732482, by rfl⟩ : syracuseStep 976643 = 1464965) B1464965
theorem B4007693 : Blo 432776 4007693 := bstep (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) B1502885
theorem B2778893 : Blo 432776 2778893 := bstep (se 3 (by rfl) ⟨521042, by rfl⟩ : syracuseStep 2778893 = 1042085) B1042085
theorem B1468205 : Blo 432776 1468205 := bstep (se 3 (by rfl) ⟨275288, by rfl⟩ : syracuseStep 1468205 = 550577) B550577
theorem B2475845 : Blo 432776 2475845 := bstep (se 4 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 2475845 = 464221) B464221
theorem B1394509 : Blo 432776 1394509 := bstep (se 3 (by rfl) ⟨261470, by rfl⟩ : syracuseStep 1394509 = 522941) B522941
theorem B550739 : Blo 432776 550739 := bstep (se 1 (by rfl) ⟨413054, by rfl⟩ : syracuseStep 550739 = 826109) B826109
theorem B1468259 : Blo 432776 1468259 := bstep (se 1 (by rfl) ⟨1101194, by rfl⟩ : syracuseStep 1468259 = 2202389) B2202389
theorem B731011 : Blo 432776 731011 := bstep (se 1 (by rfl) ⟨548258, by rfl⟩ : syracuseStep 731011 = 1096517) B1096517
theorem B1410979 : Blo 432776 1410979 := bstep (se 1 (by rfl) ⟨1058234, by rfl⟩ : syracuseStep 1410979 = 2116469) B2116469
theorem B780209 : Blo 432776 780209 := bstep (se 2 (by rfl) ⟨292578, by rfl⟩ : syracuseStep 780209 = 585157) B585157
theorem B649169 : Blo 432776 649169 := bstep (se 2 (by rfl) ⟨243438, by rfl⟩ : syracuseStep 649169 = 486877) B486877
theorem B649187 : Blo 432776 649187 := bstep (se 1 (by rfl) ⟨486890, by rfl⟩ : syracuseStep 649187 = 973781) B973781
theorem B649217 : Blo 432776 649217 := bstep (se 2 (by rfl) ⟨243456, by rfl⟩ : syracuseStep 649217 = 486913) B486913
theorem B731153 : Blo 432776 731153 := bstep (se 2 (by rfl) ⟨274182, by rfl⟩ : syracuseStep 731153 = 548365) B548365
theorem B976913 : Blo 432776 976913 := bstep (se 2 (by rfl) ⟨366342, by rfl⟩ : syracuseStep 976913 = 732685) B732685
theorem B649235 : Blo 432776 649235 := bstep (se 1 (by rfl) ⟨486926, by rfl⟩ : syracuseStep 649235 = 973853) B973853
theorem B976931 : Blo 432776 976931 := bstep (se 1 (by rfl) ⟨732698, by rfl⟩ : syracuseStep 976931 = 1465397) B1465397
theorem B649265 : Blo 432776 649265 := bstep (se 2 (by rfl) ⟨243474, by rfl⟩ : syracuseStep 649265 = 486949) B486949
theorem B1001521 : Blo 432776 1001521 := bstep (se 2 (by rfl) ⟨375570, by rfl⟩ : syracuseStep 1001521 = 751141) B751141
theorem B649283 : Blo 432776 649283 := bstep (se 1 (by rfl) ⟨486962, by rfl⟩ : syracuseStep 649283 = 973925) B973925
theorem B616529 : Blo 432776 616529 := bstep (se 2 (by rfl) ⟨231198, by rfl⟩ : syracuseStep 616529 = 462397) B462397
theorem B649313 : Blo 432776 649313 := bstep (se 2 (by rfl) ⟨243492, by rfl⟩ : syracuseStep 649313 = 486985) B486985
theorem B1099889 : Blo 432776 1099889 := bstep (se 2 (by rfl) ⟨412458, by rfl⟩ : syracuseStep 1099889 = 824917) B824917
theorem B1468529 : Blo 432776 1468529 := bstep (se 2 (by rfl) ⟨550698, by rfl⟩ : syracuseStep 1468529 = 1101397) B1101397
theorem B649331 : Blo 432776 649331 := bstep (se 1 (by rfl) ⟨486998, by rfl⟩ : syracuseStep 649331 = 973997) B973997
theorem B649361 : Blo 432776 649361 := bstep (se 2 (by rfl) ⟨243510, by rfl⟩ : syracuseStep 649361 = 487021) B487021
theorem B731281 : Blo 432776 731281 := bstep (se 2 (by rfl) ⟨274230, by rfl⟩ : syracuseStep 731281 = 548461) B548461
theorem B1042577 : Blo 432776 1042577 := bstep (se 2 (by rfl) ⟨390966, by rfl⟩ : syracuseStep 1042577 = 781933) B781933
theorem B616609 : Blo 432776 616609 := bstep (se 2 (by rfl) ⟨231228, by rfl⟩ : syracuseStep 616609 = 462457) B462457
theorem B649379 : Blo 432776 649379 := bstep (se 1 (by rfl) ⟨487034, by rfl⟩ : syracuseStep 649379 = 974069) B974069
theorem B1190051 : Blo 432776 1190051 := bstep (se 1 (by rfl) ⟨892538, by rfl⟩ : syracuseStep 1190051 = 1785077) B1785077
theorem B1099939 : Blo 432776 1099939 := bstep (se 1 (by rfl) ⟨824954, by rfl⟩ : syracuseStep 1099939 = 1649909) B1649909
theorem B731315 : Blo 432776 731315 := bstep (se 1 (by rfl) ⟨548486, by rfl⟩ : syracuseStep 731315 = 1096973) B1096973
theorem B649409 : Blo 432776 649409 := bstep (se 2 (by rfl) ⟨243528, by rfl⟩ : syracuseStep 649409 = 487057) B487057
theorem B3532997 : Blo 432776 3532997 := bstep (se 4 (by rfl) ⟨331218, by rfl⟩ : syracuseStep 3532997 = 662437) B662437
theorem B1755341 : Blo 432776 1755341 := bstep (se 3 (by rfl) ⟨329126, by rfl⟩ : syracuseStep 1755341 = 658253) B658253
theorem B649427 : Blo 432776 649427 := bstep (se 1 (by rfl) ⟨487070, by rfl⟩ : syracuseStep 649427 = 974141) B974141
theorem B649457 : Blo 432776 649457 := bstep (se 2 (by rfl) ⟨243546, by rfl⟩ : syracuseStep 649457 = 487093) B487093
theorem B3754225 : Blo 432776 3754225 := bstep (se 2 (by rfl) ⟨1407834, by rfl⟩ : syracuseStep 3754225 = 2815669) B2815669
theorem B649475 : Blo 432776 649475 := bstep (se 1 (by rfl) ⟨487106, by rfl⟩ : syracuseStep 649475 = 974213) B974213
theorem B1394957 : Blo 432776 1394957 := bstep (se 3 (by rfl) ⟨261554, by rfl⟩ : syracuseStep 1394957 = 523109) B523109
theorem B649505 : Blo 432776 649505 := bstep (se 2 (by rfl) ⟨243564, by rfl⟩ : syracuseStep 649505 = 487129) B487129
theorem B977201 : Blo 432776 977201 := bstep (se 2 (by rfl) ⟨366450, by rfl⟩ : syracuseStep 977201 = 732901) B732901
theorem B1100081 : Blo 432776 1100081 := bstep (se 2 (by rfl) ⟨412530, by rfl⟩ : syracuseStep 1100081 = 825061) B825061
theorem B649523 : Blo 432776 649523 := bstep (se 1 (by rfl) ⟨487142, by rfl⟩ : syracuseStep 649523 = 974285) B974285
theorem B731443 : Blo 432776 731443 := bstep (se 1 (by rfl) ⟨548582, by rfl⟩ : syracuseStep 731443 = 1097165) B1097165
theorem B977219 : Blo 432776 977219 := bstep (se 1 (by rfl) ⟨732914, by rfl⟩ : syracuseStep 977219 = 1465829) B1465829
theorem B649553 : Blo 432776 649553 := bstep (se 2 (by rfl) ⟨243582, by rfl⟩ : syracuseStep 649553 = 487165) B487165
theorem B649571 : Blo 432776 649571 := bstep (se 1 (by rfl) ⟨487178, by rfl⟩ : syracuseStep 649571 = 974357) B974357
theorem B649601 : Blo 432776 649601 := bstep (se 2 (by rfl) ⟨243600, by rfl⟩ : syracuseStep 649601 = 487201) B487201
theorem B1239437 : Blo 432776 1239437 := bstep (se 3 (by rfl) ⟨232394, by rfl⟩ : syracuseStep 1239437 = 464789) B464789
theorem B649619 : Blo 432776 649619 := bstep (se 1 (by rfl) ⟨487214, by rfl⟩ : syracuseStep 649619 = 974429) B974429
theorem B2206115 : Blo 432776 2206115 := bstep (se 1 (by rfl) ⟨1654586, by rfl⟩ : syracuseStep 2206115 = 3309173) B3309173
theorem B649649 : Blo 432776 649649 := bstep (se 2 (by rfl) ⟨243618, by rfl⟩ : syracuseStep 649649 = 487237) B487237
theorem B731585 : Blo 432776 731585 := bstep (se 2 (by rfl) ⟨274344, by rfl⟩ : syracuseStep 731585 = 548689) B548689
theorem B649667 : Blo 432776 649667 := bstep (se 1 (by rfl) ⟨487250, by rfl⟩ : syracuseStep 649667 = 974501) B974501
theorem B1411523 : Blo 432776 1411523 := bstep (se 1 (by rfl) ⟨1058642, by rfl⟩ : syracuseStep 1411523 = 2117285) B2117285
theorem B649697 : Blo 432776 649697 := bstep (se 2 (by rfl) ⟨243636, by rfl⟩ : syracuseStep 649697 = 487273) B487273
theorem B649715 : Blo 432776 649715 := bstep (se 1 (by rfl) ⟨487286, by rfl⟩ : syracuseStep 649715 = 974573) B974573
theorem B1460753 : Blo 432776 1460753 := bstep (se 2 (by rfl) ⟨547782, by rfl⟩ : syracuseStep 1460753 = 1095565) B1095565
theorem B649745 : Blo 432776 649745 := bstep (se 2 (by rfl) ⟨243654, by rfl⟩ : syracuseStep 649745 = 487309) B487309
theorem B551443 : Blo 432776 551443 := bstep (se 1 (by rfl) ⟨413582, by rfl⟩ : syracuseStep 551443 = 827165) B827165
theorem B649763 : Blo 432776 649763 := bstep (se 1 (by rfl) ⟨487322, by rfl⟩ : syracuseStep 649763 = 974645) B974645
theorem B15026741 : Blo 432776 15026741 := bstep (se 5 (by rfl) ⟨704378, by rfl⟩ : syracuseStep 15026741 = 1408757) B1408757
theorem B649793 : Blo 432776 649793 := bstep (se 2 (by rfl) ⟨243672, by rfl⟩ : syracuseStep 649793 = 487345) B487345
theorem B731713 : Blo 432776 731713 := bstep (se 2 (by rfl) ⟨274392, by rfl⟩ : syracuseStep 731713 = 548785) B548785
theorem B1239619 : Blo 432776 1239619 := bstep (se 1 (by rfl) ⟨929714, by rfl⟩ : syracuseStep 1239619 = 1859429) B1859429
theorem B1854029 : Blo 432776 1854029 := bstep (se 3 (by rfl) ⟨347630, by rfl⟩ : syracuseStep 1854029 = 695261) B695261
theorem B977489 : Blo 432776 977489 := bstep (se 2 (by rfl) ⟨366558, by rfl⟩ : syracuseStep 977489 = 733117) B733117
theorem B649811 : Blo 432776 649811 := bstep (se 1 (by rfl) ⟨487358, by rfl⟩ : syracuseStep 649811 = 974717) B974717
theorem B731747 : Blo 432776 731747 := bstep (se 1 (by rfl) ⟨548810, by rfl⟩ : syracuseStep 731747 = 1097621) B1097621
theorem B977507 : Blo 432776 977507 := bstep (se 1 (by rfl) ⟨733130, by rfl⟩ : syracuseStep 977507 = 1466261) B1466261
theorem B649841 : Blo 432776 649841 := bstep (se 2 (by rfl) ⟨243690, by rfl⟩ : syracuseStep 649841 = 487381) B487381
theorem B649859 : Blo 432776 649859 := bstep (se 1 (by rfl) ⟨487394, by rfl⟩ : syracuseStep 649859 = 974789) B974789
theorem B1469069 : Blo 432776 1469069 := bstep (se 3 (by rfl) ⟨275450, by rfl⟩ : syracuseStep 1469069 = 550901) B550901
theorem B649889 : Blo 432776 649889 := bstep (se 2 (by rfl) ⟨243708, by rfl⟩ : syracuseStep 649889 = 487417) B487417
theorem B649907 : Blo 432776 649907 := bstep (se 1 (by rfl) ⟨487430, by rfl⟩ : syracuseStep 649907 = 974861) B974861
theorem B1469123 : Blo 432776 1469123 := bstep (se 1 (by rfl) ⟨1101842, by rfl⟩ : syracuseStep 1469123 = 2203685) B2203685
theorem B649937 : Blo 432776 649937 := bstep (se 2 (by rfl) ⟨243726, by rfl⟩ : syracuseStep 649937 = 487453) B487453
theorem B649955 : Blo 432776 649955 := bstep (se 1 (by rfl) ⟨487466, by rfl⟩ : syracuseStep 649955 = 974933) B974933
theorem B731875 : Blo 432776 731875 := bstep (se 1 (by rfl) ⟨548906, by rfl⟩ : syracuseStep 731875 = 1097813) B1097813
theorem B1239779 : Blo 432776 1239779 := bstep (se 1 (by rfl) ⟨929834, by rfl⟩ : syracuseStep 1239779 = 1859669) B1859669
theorem B822001 : Blo 432776 822001 := bstep (se 2 (by rfl) ⟨308250, by rfl⟩ : syracuseStep 822001 = 616501) B616501
theorem B1649393 : Blo 432776 1649393 := bstep (se 2 (by rfl) ⟨618522, by rfl⟩ : syracuseStep 1649393 = 1237045) B1237045
theorem B649985 : Blo 432776 649985 := bstep (se 2 (by rfl) ⟨243744, by rfl⟩ : syracuseStep 649985 = 487489) B487489
theorem B650003 : Blo 432776 650003 := bstep (se 1 (by rfl) ⟨487502, by rfl⟩ : syracuseStep 650003 = 975005) B975005
theorem B650033 : Blo 432776 650033 := bstep (se 2 (by rfl) ⟨243762, by rfl⟩ : syracuseStep 650033 = 487525) B487525
theorem B650051 : Blo 432776 650051 := bstep (se 1 (by rfl) ⟨487538, by rfl⟩ : syracuseStep 650051 = 975077) B975077
theorem B928579 : Blo 432776 928579 := bstep (se 1 (by rfl) ⟨696434, by rfl⟩ : syracuseStep 928579 = 1392869) B1392869
theorem B650081 : Blo 432776 650081 := bstep (se 2 (by rfl) ⟨243780, by rfl⟩ : syracuseStep 650081 = 487561) B487561
theorem B732017 : Blo 432776 732017 := bstep (se 2 (by rfl) ⟨274506, by rfl⟩ : syracuseStep 732017 = 549013) B549013
theorem B977777 : Blo 432776 977777 := bstep (se 2 (by rfl) ⟨366666, by rfl⟩ : syracuseStep 977777 = 733333) B733333
theorem B650099 : Blo 432776 650099 := bstep (se 1 (by rfl) ⟨487574, by rfl⟩ : syracuseStep 650099 = 975149) B975149
theorem B977795 : Blo 432776 977795 := bstep (se 1 (by rfl) ⟨733346, by rfl⟩ : syracuseStep 977795 = 1466693) B1466693
theorem B4164493 : Blo 432776 4164493 := bstep (se 3 (by rfl) ⟨780842, by rfl⟩ : syracuseStep 4164493 = 1561685) B1561685
theorem B650129 : Blo 432776 650129 := bstep (se 2 (by rfl) ⟨243798, by rfl⟩ : syracuseStep 650129 = 487597) B487597
theorem B650147 : Blo 432776 650147 := bstep (se 1 (by rfl) ⟨487610, by rfl⟩ : syracuseStep 650147 = 975221) B975221
theorem B617395 : Blo 432776 617395 := bstep (se 1 (by rfl) ⟨463046, by rfl⟩ : syracuseStep 617395 = 926093) B926093
theorem B5622709 : Blo 432776 5622709 := bstep (se 5 (by rfl) ⟨263564, by rfl⟩ : syracuseStep 5622709 = 527129) B527129
theorem B650177 : Blo 432776 650177 := bstep (se 2 (by rfl) ⟨243816, by rfl⟩ : syracuseStep 650177 = 487633) B487633
theorem B1469393 : Blo 432776 1469393 := bstep (se 2 (by rfl) ⟨551022, by rfl⟩ : syracuseStep 1469393 = 1102045) B1102045
theorem B650195 : Blo 432776 650195 := bstep (se 1 (by rfl) ⟨487646, by rfl⟩ : syracuseStep 650195 = 975293) B975293
theorem B650225 : Blo 432776 650225 := bstep (se 2 (by rfl) ⟨243834, by rfl⟩ : syracuseStep 650225 = 487669) B487669
theorem B732145 : Blo 432776 732145 := bstep (se 2 (by rfl) ⟨274554, by rfl⟩ : syracuseStep 732145 = 549109) B549109
theorem B650243 : Blo 432776 650243 := bstep (se 1 (by rfl) ⟨487682, by rfl⟩ : syracuseStep 650243 = 975365) B975365
theorem B732179 : Blo 432776 732179 := bstep (se 1 (by rfl) ⟨549134, by rfl⟩ : syracuseStep 732179 = 1098269) B1098269
theorem B650273 : Blo 432776 650273 := bstep (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) B487705
theorem B1461293 : Blo 432776 1461293 := bstep (se 3 (by rfl) ⟨273992, by rfl⟩ : syracuseStep 1461293 = 547985) B547985
theorem B650291 : Blo 432776 650291 := bstep (se 1 (by rfl) ⟨487718, by rfl⟩ : syracuseStep 650291 = 975437) B975437
theorem B1387601 : Blo 432776 1387601 := bstep (se 2 (by rfl) ⟨520350, by rfl⟩ : syracuseStep 1387601 = 1040701) B1040701
theorem B650321 : Blo 432776 650321 := bstep (se 2 (by rfl) ⟨243870, by rfl⟩ : syracuseStep 650321 = 487741) B487741
theorem B1461347 : Blo 432776 1461347 := bstep (se 1 (by rfl) ⟨1096010, by rfl⟩ : syracuseStep 1461347 = 2192021) B2192021
theorem B650339 : Blo 432776 650339 := bstep (se 1 (by rfl) ⟨487754, by rfl⟩ : syracuseStep 650339 = 975509) B975509
theorem B650369 : Blo 432776 650369 := bstep (se 2 (by rfl) ⟨243888, by rfl⟩ : syracuseStep 650369 = 487777) B487777
theorem B822403 : Blo 432776 822403 := bstep (se 1 (by rfl) ⟨616802, by rfl⟩ : syracuseStep 822403 = 1233605) B1233605
theorem B978065 : Blo 432776 978065 := bstep (se 2 (by rfl) ⟨366774, by rfl⟩ : syracuseStep 978065 = 733549) B733549
theorem B650387 : Blo 432776 650387 := bstep (se 1 (by rfl) ⟨487790, by rfl⟩ : syracuseStep 650387 = 975581) B975581
theorem B732307 : Blo 432776 732307 := bstep (se 1 (by rfl) ⟨549230, by rfl⟩ : syracuseStep 732307 = 1098461) B1098461
theorem B978083 : Blo 432776 978083 := bstep (se 1 (by rfl) ⟨733562, by rfl⟩ : syracuseStep 978083 = 1467125) B1467125
theorem B2231459 : Blo 432776 2231459 := bstep (se 1 (by rfl) ⟨1673594, by rfl⟩ : syracuseStep 2231459 = 3347189) B3347189
theorem B822449 : Blo 432776 822449 := bstep (se 2 (by rfl) ⟨308418, by rfl⟩ : syracuseStep 822449 = 616837) B616837
theorem B650417 : Blo 432776 650417 := bstep (se 2 (by rfl) ⟨243906, by rfl⟩ : syracuseStep 650417 = 487813) B487813
theorem B650435 : Blo 432776 650435 := bstep (se 1 (by rfl) ⟨487826, by rfl⟩ : syracuseStep 650435 = 975653) B975653
theorem B650465 : Blo 432776 650465 := bstep (se 2 (by rfl) ⟨243924, by rfl⟩ : syracuseStep 650465 = 487849) B487849
theorem B650483 : Blo 432776 650483 := bstep (se 1 (by rfl) ⟨487862, by rfl⟩ : syracuseStep 650483 = 975725) B975725
theorem B650513 : Blo 432776 650513 := bstep (se 2 (by rfl) ⟨243942, by rfl⟩ : syracuseStep 650513 = 487885) B487885
theorem B1101073 : Blo 432776 1101073 := bstep (se 2 (by rfl) ⟨412902, by rfl⟩ : syracuseStep 1101073 = 825805) B825805
theorem B732449 : Blo 432776 732449 := bstep (se 2 (by rfl) ⟨274668, by rfl⟩ : syracuseStep 732449 = 549337) B549337
theorem B650531 : Blo 432776 650531 := bstep (se 1 (by rfl) ⟨487898, by rfl⟩ : syracuseStep 650531 = 975797) B975797
theorem B2223409 : Blo 432776 2223409 := bstep (se 2 (by rfl) ⟨833778, by rfl⟩ : syracuseStep 2223409 = 1667557) B1667557
theorem B740659 : Blo 432776 740659 := bstep (se 1 (by rfl) ⟨555494, by rfl⟩ : syracuseStep 740659 = 1110989) B1110989
theorem B650561 : Blo 432776 650561 := bstep (se 2 (by rfl) ⟨243960, by rfl⟩ : syracuseStep 650561 = 487921) B487921
theorem B2346317 : Blo 432776 2346317 := bstep (se 3 (by rfl) ⟨439934, by rfl⟩ : syracuseStep 2346317 = 879869) B879869
theorem B650579 : Blo 432776 650579 := bstep (se 1 (by rfl) ⟨487934, by rfl⟩ : syracuseStep 650579 = 975869) B975869
theorem B1461617 : Blo 432776 1461617 := bstep (se 2 (by rfl) ⟨548106, by rfl⟩ : syracuseStep 1461617 = 1096213) B1096213
theorem B650609 : Blo 432776 650609 := bstep (se 2 (by rfl) ⟨243978, by rfl⟩ : syracuseStep 650609 = 487957) B487957
theorem B650627 : Blo 432776 650627 := bstep (se 1 (by rfl) ⟨487970, by rfl⟩ : syracuseStep 650627 = 975941) B975941
theorem B617873 : Blo 432776 617873 := bstep (se 2 (by rfl) ⟨231702, by rfl⟩ : syracuseStep 617873 = 463405) B463405
theorem B650657 : Blo 432776 650657 := bstep (se 2 (by rfl) ⟨243996, by rfl⟩ : syracuseStep 650657 = 487993) B487993
theorem B732577 : Blo 432776 732577 := bstep (se 2 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 732577 = 549433) B549433
theorem B978353 : Blo 432776 978353 := bstep (se 2 (by rfl) ⟨366882, by rfl⟩ : syracuseStep 978353 = 733765) B733765
theorem B650675 : Blo 432776 650675 := bstep (se 1 (by rfl) ⟨488006, by rfl⟩ : syracuseStep 650675 = 976013) B976013
theorem B732611 : Blo 432776 732611 := bstep (se 1 (by rfl) ⟨549458, by rfl⟩ : syracuseStep 732611 = 1098917) B1098917
theorem B978371 : Blo 432776 978371 := bstep (se 1 (by rfl) ⟨733778, by rfl⟩ : syracuseStep 978371 = 1467557) B1467557
theorem B1674701 : Blo 432776 1674701 := bstep (se 3 (by rfl) ⟨314006, by rfl⟩ : syracuseStep 1674701 = 628013) B628013
theorem B822737 : Blo 432776 822737 := bstep (se 2 (by rfl) ⟨308526, by rfl⟩ : syracuseStep 822737 = 617053) B617053
theorem B650705 : Blo 432776 650705 := bstep (se 2 (by rfl) ⟨244014, by rfl⟩ : syracuseStep 650705 = 488029) B488029
theorem B650723 : Blo 432776 650723 := bstep (se 1 (by rfl) ⟨488042, by rfl⟩ : syracuseStep 650723 = 976085) B976085
theorem B1469933 : Blo 432776 1469933 := bstep (se 3 (by rfl) ⟨275612, by rfl⟩ : syracuseStep 1469933 = 551225) B551225
theorem B650753 : Blo 432776 650753 := bstep (se 2 (by rfl) ⟨244032, by rfl⟩ : syracuseStep 650753 = 488065) B488065
theorem B617987 : Blo 432776 617987 := bstep (se 1 (by rfl) ⟨463490, by rfl⟩ : syracuseStep 617987 = 926981) B926981
theorem B486931 : Blo 432776 486931 := bstep (se 1 (by rfl) ⟨365198, by rfl⟩ : syracuseStep 486931 = 730397) B730397
theorem B650771 : Blo 432776 650771 := bstep (se 1 (by rfl) ⟨488078, by rfl⟩ : syracuseStep 650771 = 976157) B976157
theorem B1101347 : Blo 432776 1101347 := bstep (se 1 (by rfl) ⟨826010, by rfl⟩ : syracuseStep 1101347 = 1652021) B1652021
theorem B1469987 : Blo 432776 1469987 := bstep (se 1 (by rfl) ⟨1102490, by rfl⟩ : syracuseStep 1469987 = 2204981) B2204981
theorem B650801 : Blo 432776 650801 := bstep (se 2 (by rfl) ⟨244050, by rfl⟩ : syracuseStep 650801 = 488101) B488101
theorem B650819 : Blo 432776 650819 := bstep (se 1 (by rfl) ⟨488114, by rfl⟩ : syracuseStep 650819 = 976229) B976229
theorem B732739 : Blo 432776 732739 := bstep (se 1 (by rfl) ⟨549554, by rfl⟩ : syracuseStep 732739 = 1099109) B1099109
theorem B1322563 : Blo 432776 1322563 := bstep (se 1 (by rfl) ⟨991922, by rfl⟩ : syracuseStep 1322563 = 1983845) B1983845
theorem B626257 : Blo 432776 626257 := bstep (se 2 (by rfl) ⟨234846, by rfl⟩ : syracuseStep 626257 = 469693) B469693
theorem B618067 : Blo 432776 618067 := bstep (se 1 (by rfl) ⟨463550, by rfl⟩ : syracuseStep 618067 = 927101) B927101
theorem B650849 : Blo 432776 650849 := bstep (se 2 (by rfl) ⟨244068, by rfl⟩ : syracuseStep 650849 = 488137) B488137
theorem B650867 : Blo 432776 650867 := bstep (se 1 (by rfl) ⟨488150, by rfl⟩ : syracuseStep 650867 = 976301) B976301
theorem B650897 : Blo 432776 650897 := bstep (se 2 (by rfl) ⟨244086, by rfl⟩ : syracuseStep 650897 = 488173) B488173
theorem B487075 : Blo 432776 487075 := bstep (se 1 (by rfl) ⟨365306, by rfl⟩ : syracuseStep 487075 = 730613) B730613
theorem B650915 : Blo 432776 650915 := bstep (se 1 (by rfl) ⟨488186, by rfl⟩ : syracuseStep 650915 = 976373) B976373
theorem B650945 : Blo 432776 650945 := bstep (se 2 (by rfl) ⟨244104, by rfl⟩ : syracuseStep 650945 = 488209) B488209
theorem B732881 : Blo 432776 732881 := bstep (se 2 (by rfl) ⟨274830, by rfl⟩ : syracuseStep 732881 = 549661) B549661
theorem B978641 : Blo 432776 978641 := bstep (se 2 (by rfl) ⟨366990, by rfl⟩ : syracuseStep 978641 = 733981) B733981
theorem B462547 : Blo 432776 462547 := bstep (se 1 (by rfl) ⟨346910, by rfl⟩ : syracuseStep 462547 = 693821) B693821
theorem B650963 : Blo 432776 650963 := bstep (se 1 (by rfl) ⟨488222, by rfl⟩ : syracuseStep 650963 = 976445) B976445
theorem B978659 : Blo 432776 978659 := bstep (se 1 (by rfl) ⟨733994, by rfl⟩ : syracuseStep 978659 = 1467989) B1467989
theorem B1101539 : Blo 432776 1101539 := bstep (se 1 (by rfl) ⟨826154, by rfl⟩ : syracuseStep 1101539 = 1652309) B1652309
theorem B1986275 : Blo 432776 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B650993 : Blo 432776 650993 := bstep (se 2 (by rfl) ⟨244122, by rfl⟩ : syracuseStep 650993 = 488245) B488245
theorem B651011 : Blo 432776 651011 := bstep (se 1 (by rfl) ⟨488258, by rfl⟩ : syracuseStep 651011 = 976517) B976517
theorem B1240849 : Blo 432776 1240849 := bstep (se 2 (by rfl) ⟨465318, by rfl⟩ : syracuseStep 1240849 = 930637) B930637
theorem B651041 : Blo 432776 651041 := bstep (se 2 (by rfl) ⟨244140, by rfl⟩ : syracuseStep 651041 = 488281) B488281
theorem B1470257 : Blo 432776 1470257 := bstep (se 2 (by rfl) ⟨551346, by rfl⟩ : syracuseStep 1470257 = 1102693) B1102693
theorem B487219 : Blo 432776 487219 := bstep (se 1 (by rfl) ⟨365414, by rfl⟩ : syracuseStep 487219 = 730829) B730829
theorem B651059 : Blo 432776 651059 := bstep (se 1 (by rfl) ⟨488294, by rfl⟩ : syracuseStep 651059 = 976589) B976589
theorem B7499573 : Blo 432776 7499573 := bstep (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) B703085
theorem B3305285 : Blo 432776 3305285 := bstep (se 4 (by rfl) ⟨309870, by rfl⟩ : syracuseStep 3305285 = 619741) B619741
theorem B651089 : Blo 432776 651089 := bstep (se 2 (by rfl) ⟨244158, by rfl⟩ : syracuseStep 651089 = 488317) B488317
theorem B733009 : Blo 432776 733009 := bstep (se 2 (by rfl) ⟨274878, by rfl⟩ : syracuseStep 733009 = 549757) B549757
theorem B1757027 : Blo 432776 1757027 := bstep (se 1 (by rfl) ⟨1317770, by rfl⟩ : syracuseStep 1757027 = 2635541) B2635541
theorem B2084707 : Blo 432776 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B651107 : Blo 432776 651107 := bstep (se 1 (by rfl) ⟨488330, by rfl⟩ : syracuseStep 651107 = 976661) B976661
theorem B733043 : Blo 432776 733043 := bstep (se 1 (by rfl) ⟨549782, by rfl⟩ : syracuseStep 733043 = 1099565) B1099565
theorem B651137 : Blo 432776 651137 := bstep (se 2 (by rfl) ⟨244176, by rfl⟩ : syracuseStep 651137 = 488353) B488353
theorem B1462157 : Blo 432776 1462157 := bstep (se 3 (by rfl) ⟨274154, by rfl⟩ : syracuseStep 1462157 = 548309) B548309
theorem B651155 : Blo 432776 651155 := bstep (se 1 (by rfl) ⟨488366, by rfl⟩ : syracuseStep 651155 = 976733) B976733
theorem B1388461 : Blo 432776 1388461 := bstep (se 3 (by rfl) ⟨260336, by rfl⟩ : syracuseStep 1388461 = 520673) B520673
theorem B651185 : Blo 432776 651185 := bstep (se 2 (by rfl) ⟨244194, by rfl⟩ : syracuseStep 651185 = 488389) B488389
theorem B2199473 : Blo 432776 2199473 := bstep (se 2 (by rfl) ⟨824802, by rfl⟩ : syracuseStep 2199473 = 1649605) B1649605
theorem B487363 : Blo 432776 487363 := bstep (se 1 (by rfl) ⟨365522, by rfl⟩ : syracuseStep 487363 = 731045) B731045
theorem B1462211 : Blo 432776 1462211 := bstep (se 1 (by rfl) ⟨1096658, by rfl⟩ : syracuseStep 1462211 = 2193317) B2193317
theorem B651203 : Blo 432776 651203 := bstep (se 1 (by rfl) ⟨488402, by rfl⟩ : syracuseStep 651203 = 976805) B976805
theorem B651233 : Blo 432776 651233 := bstep (se 2 (by rfl) ⟨244212, by rfl⟩ : syracuseStep 651233 = 488425) B488425
theorem B978929 : Blo 432776 978929 := bstep (se 2 (by rfl) ⟨367098, by rfl⟩ : syracuseStep 978929 = 734197) B734197
theorem B1568753 : Blo 432776 1568753 := bstep (se 2 (by rfl) ⟨588282, by rfl⟩ : syracuseStep 1568753 = 1176565) B1176565
theorem B651251 : Blo 432776 651251 := bstep (se 1 (by rfl) ⟨488438, by rfl⟩ : syracuseStep 651251 = 976877) B976877
theorem B733171 : Blo 432776 733171 := bstep (se 1 (by rfl) ⟨549878, by rfl⟩ : syracuseStep 733171 = 1099757) B1099757
theorem B978947 : Blo 432776 978947 := bstep (se 1 (by rfl) ⟨734210, by rfl⟩ : syracuseStep 978947 = 1468421) B1468421
theorem B2191373 : Blo 432776 2191373 := bstep (se 3 (by rfl) ⟨410882, by rfl⟩ : syracuseStep 2191373 = 821765) B821765
theorem B651281 : Blo 432776 651281 := bstep (se 2 (by rfl) ⟨244230, by rfl⟩ : syracuseStep 651281 = 488461) B488461
theorem B929809 : Blo 432776 929809 := bstep (se 2 (by rfl) ⟨348678, by rfl⟩ : syracuseStep 929809 = 697357) B697357
theorem B2969635 : Blo 432776 2969635 := bstep (se 1 (by rfl) ⟨2227226, by rfl⟩ : syracuseStep 2969635 = 4454453) B4454453
theorem B651299 : Blo 432776 651299 := bstep (se 1 (by rfl) ⟨488474, by rfl⟩ : syracuseStep 651299 = 976949) B976949
theorem B1232945 : Blo 432776 1232945 := bstep (se 2 (by rfl) ⟨462354, by rfl⟩ : syracuseStep 1232945 = 924709) B924709
theorem B651329 : Blo 432776 651329 := bstep (se 2 (by rfl) ⟨244248, by rfl⟩ : syracuseStep 651329 = 488497) B488497
theorem B487507 : Blo 432776 487507 := bstep (se 1 (by rfl) ⟨365630, by rfl⟩ : syracuseStep 487507 = 731261) B731261
theorem B651347 : Blo 432776 651347 := bstep (se 1 (by rfl) ⟨488510, by rfl⟩ : syracuseStep 651347 = 977021) B977021
theorem B651377 : Blo 432776 651377 := bstep (se 2 (by rfl) ⟨244266, by rfl⟩ : syracuseStep 651377 = 488533) B488533
theorem B618625 : Blo 432776 618625 := bstep (se 2 (by rfl) ⟨231984, by rfl⟩ : syracuseStep 618625 = 463969) B463969
theorem B733313 : Blo 432776 733313 := bstep (se 2 (by rfl) ⟨274992, by rfl⟩ : syracuseStep 733313 = 549985) B549985
theorem B651395 : Blo 432776 651395 := bstep (se 1 (by rfl) ⟨488546, by rfl⟩ : syracuseStep 651395 = 977093) B977093
theorem B651425 : Blo 432776 651425 := bstep (se 2 (by rfl) ⟨244284, by rfl⟩ : syracuseStep 651425 = 488569) B488569
theorem B823459 : Blo 432776 823459 := bstep (se 1 (by rfl) ⟨617594, by rfl⟩ : syracuseStep 823459 = 1235189) B1235189
theorem B1650851 : Blo 432776 1650851 := bstep (se 1 (by rfl) ⟨1238138, by rfl⟩ : syracuseStep 1650851 = 2476277) B2476277
theorem B651443 : Blo 432776 651443 := bstep (se 1 (by rfl) ⟨488582, by rfl⟩ : syracuseStep 651443 = 977165) B977165
theorem B782531 : Blo 432776 782531 := bstep (se 1 (by rfl) ⟨586898, by rfl⟩ : syracuseStep 782531 = 1173797) B1173797
theorem B3133637 : Blo 432776 3133637 := bstep (se 4 (by rfl) ⟨293778, by rfl⟩ : syracuseStep 3133637 = 587557) B587557
theorem B1159373 : Blo 432776 1159373 := bstep (se 3 (by rfl) ⟨217382, by rfl⟩ : syracuseStep 1159373 = 434765) B434765
theorem B1462481 : Blo 432776 1462481 := bstep (se 2 (by rfl) ⟨548430, by rfl⟩ : syracuseStep 1462481 = 1096861) B1096861
theorem B651473 : Blo 432776 651473 := bstep (se 2 (by rfl) ⟨244302, by rfl⟩ : syracuseStep 651473 = 488605) B488605
theorem B487651 : Blo 432776 487651 := bstep (se 1 (by rfl) ⟨365738, by rfl⟩ : syracuseStep 487651 = 731477) B731477
theorem B6254819 : Blo 432776 6254819 := bstep (se 1 (by rfl) ⟨4691114, by rfl⟩ : syracuseStep 6254819 = 9382229) B9382229
theorem B651491 : Blo 432776 651491 := bstep (se 1 (by rfl) ⟨488618, by rfl⟩ : syracuseStep 651491 = 977237) B977237
theorem B954595 : Blo 432776 954595 := bstep (se 1 (by rfl) ⟨715946, by rfl⟩ : syracuseStep 954595 = 1431893) B1431893
theorem B3526897 : Blo 432776 3526897 := bstep (se 2 (by rfl) ⟨1322586, by rfl⟩ : syracuseStep 3526897 = 2645173) B2645173
theorem B651521 : Blo 432776 651521 := bstep (se 2 (by rfl) ⟨244320, by rfl⟩ : syracuseStep 651521 = 488641) B488641
theorem B733441 : Blo 432776 733441 := bstep (se 2 (by rfl) ⟨275040, by rfl⟩ : syracuseStep 733441 = 550081) B550081
theorem B2773253 : Blo 432776 2773253 := bstep (se 4 (by rfl) ⟨259992, by rfl⟩ : syracuseStep 2773253 = 519985) B519985
theorem B979217 : Blo 432776 979217 := bstep (se 2 (by rfl) ⟨367206, by rfl⟩ : syracuseStep 979217 = 734413) B734413
theorem B651539 : Blo 432776 651539 := bstep (se 1 (by rfl) ⟨488654, by rfl⟩ : syracuseStep 651539 = 977309) B977309
theorem B880931 : Blo 432776 880931 := bstep (se 1 (by rfl) ⟨660698, by rfl⟩ : syracuseStep 880931 = 1321397) B1321397
theorem B733475 : Blo 432776 733475 := bstep (se 1 (by rfl) ⟨550106, by rfl⟩ : syracuseStep 733475 = 1100213) B1100213
theorem B979235 : Blo 432776 979235 := bstep (se 1 (by rfl) ⟨734426, by rfl⟩ : syracuseStep 979235 = 1468853) B1468853
theorem B651569 : Blo 432776 651569 := bstep (se 2 (by rfl) ⟨244338, by rfl⟩ : syracuseStep 651569 = 488677) B488677
theorem B651587 : Blo 432776 651587 := bstep (se 1 (by rfl) ⟨488690, by rfl⟩ : syracuseStep 651587 = 977381) B977381
theorem B651617 : Blo 432776 651617 := bstep (se 2 (by rfl) ⟨244356, by rfl⟩ : syracuseStep 651617 = 488713) B488713
theorem B856433 : Blo 432776 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B487795 : Blo 432776 487795 := bstep (se 1 (by rfl) ⟨365846, by rfl⟩ : syracuseStep 487795 = 731693) B731693
theorem B651635 : Blo 432776 651635 := bstep (se 1 (by rfl) ⟨488726, by rfl⟩ : syracuseStep 651635 = 977453) B977453
theorem B651665 : Blo 432776 651665 := bstep (se 2 (by rfl) ⟨244374, by rfl⟩ : syracuseStep 651665 = 488749) B488749
theorem B741793 : Blo 432776 741793 := bstep (se 2 (by rfl) ⟨278172, by rfl⟩ : syracuseStep 741793 = 556345) B556345
theorem B1560995 : Blo 432776 1560995 := bstep (se 1 (by rfl) ⟨1170746, by rfl⟩ : syracuseStep 1560995 = 2341493) B2341493
theorem B651683 : Blo 432776 651683 := bstep (se 1 (by rfl) ⟨488762, by rfl⟩ : syracuseStep 651683 = 977525) B977525
theorem B733603 : Blo 432776 733603 := bstep (se 1 (by rfl) ⟨550202, by rfl⟩ : syracuseStep 733603 = 1100405) B1100405
theorem B651713 : Blo 432776 651713 := bstep (se 2 (by rfl) ⟨244392, by rfl⟩ : syracuseStep 651713 = 488785) B488785
theorem B651731 : Blo 432776 651731 := bstep (se 1 (by rfl) ⟨488798, by rfl⟩ : syracuseStep 651731 = 977597) B977597
theorem B954865 : Blo 432776 954865 := bstep (se 2 (by rfl) ⟨358074, by rfl⟩ : syracuseStep 954865 = 716149) B716149
theorem B651761 : Blo 432776 651761 := bstep (se 2 (by rfl) ⟨244410, by rfl⟩ : syracuseStep 651761 = 488821) B488821
theorem B487939 : Blo 432776 487939 := bstep (se 1 (by rfl) ⟨365954, by rfl⟩ : syracuseStep 487939 = 731909) B731909
theorem B651779 : Blo 432776 651779 := bstep (se 1 (by rfl) ⟨488834, by rfl⟩ : syracuseStep 651779 = 977669) B977669
theorem B2503181 : Blo 432776 2503181 := bstep (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) B938693
theorem B651809 : Blo 432776 651809 := bstep (se 2 (by rfl) ⟨244428, by rfl⟩ : syracuseStep 651809 = 488857) B488857
theorem B733745 : Blo 432776 733745 := bstep (se 2 (by rfl) ⟨275154, by rfl⟩ : syracuseStep 733745 = 550309) B550309
theorem B979505 : Blo 432776 979505 := bstep (se 2 (by rfl) ⟨367314, by rfl⟩ : syracuseStep 979505 = 734629) B734629
theorem B651827 : Blo 432776 651827 := bstep (se 1 (by rfl) ⟨488870, by rfl⟩ : syracuseStep 651827 = 977741) B977741
theorem B979523 : Blo 432776 979523 := bstep (se 1 (by rfl) ⟨734642, by rfl⟩ : syracuseStep 979523 = 1469285) B1469285
theorem B651857 : Blo 432776 651857 := bstep (se 2 (by rfl) ⟨244446, by rfl⟩ : syracuseStep 651857 = 488893) B488893
theorem B823907 : Blo 432776 823907 := bstep (se 1 (by rfl) ⟨617930, by rfl⟩ : syracuseStep 823907 = 1235861) B1235861
theorem B651875 : Blo 432776 651875 := bstep (se 1 (by rfl) ⟨488906, by rfl⟩ : syracuseStep 651875 = 977813) B977813
theorem B651905 : Blo 432776 651905 := bstep (se 2 (by rfl) ⟨244464, by rfl⟩ : syracuseStep 651905 = 488929) B488929
theorem B1102481 : Blo 432776 1102481 := bstep (se 2 (by rfl) ⟨413430, by rfl⟩ : syracuseStep 1102481 = 826861) B826861
theorem B488083 : Blo 432776 488083 := bstep (se 1 (by rfl) ⟨366062, by rfl⟩ : syracuseStep 488083 = 732125) B732125
theorem B651923 : Blo 432776 651923 := bstep (se 1 (by rfl) ⟨488942, by rfl⟩ : syracuseStep 651923 = 977885) B977885
theorem B930467 : Blo 432776 930467 := bstep (se 1 (by rfl) ⟨697850, by rfl⟩ : syracuseStep 930467 = 1395701) B1395701
theorem B651953 : Blo 432776 651953 := bstep (se 2 (by rfl) ⟨244482, by rfl⟩ : syracuseStep 651953 = 488965) B488965
theorem B733873 : Blo 432776 733873 := bstep (se 2 (by rfl) ⟨275202, by rfl⟩ : syracuseStep 733873 = 550405) B550405
theorem B2790065 : Blo 432776 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B651971 : Blo 432776 651971 := bstep (se 1 (by rfl) ⟨488978, by rfl⟩ : syracuseStep 651971 = 977957) B977957
theorem B1102531 : Blo 432776 1102531 := bstep (se 1 (by rfl) ⟨826898, by rfl⟩ : syracuseStep 1102531 = 1653797) B1653797
theorem B815825 : Blo 432776 815825 := bstep (se 2 (by rfl) ⟨305934, by rfl⟩ : syracuseStep 815825 = 611869) B611869
theorem B733907 : Blo 432776 733907 := bstep (se 1 (by rfl) ⟨550430, by rfl⟩ : syracuseStep 733907 = 1100861) B1100861
theorem B660193 : Blo 432776 660193 := bstep (se 2 (by rfl) ⟨247572, by rfl⟩ : syracuseStep 660193 = 495145) B495145
theorem B652001 : Blo 432776 652001 := bstep (se 2 (by rfl) ⟨244500, by rfl⟩ : syracuseStep 652001 = 489001) B489001
theorem B1045219 : Blo 432776 1045219 := bstep (se 1 (by rfl) ⟨783914, by rfl⟩ : syracuseStep 1045219 = 1567829) B1567829
theorem B1463021 : Blo 432776 1463021 := bstep (se 3 (by rfl) ⟨274316, by rfl⟩ : syracuseStep 1463021 = 548633) B548633
theorem B6099697 : Blo 432776 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B652019 : Blo 432776 652019 := bstep (se 1 (by rfl) ⟨489014, by rfl⟩ : syracuseStep 652019 = 978029) B978029
theorem B652049 : Blo 432776 652049 := bstep (se 2 (by rfl) ⟨244518, by rfl⟩ : syracuseStep 652049 = 489037) B489037
theorem B1463075 : Blo 432776 1463075 := bstep (se 1 (by rfl) ⟨1097306, by rfl⟩ : syracuseStep 1463075 = 2194613) B2194613
theorem B488227 : Blo 432776 488227 := bstep (se 1 (by rfl) ⟨366170, by rfl⟩ : syracuseStep 488227 = 732341) B732341
theorem B652067 : Blo 432776 652067 := bstep (se 1 (by rfl) ⟨489050, by rfl⟩ : syracuseStep 652067 = 978101) B978101
theorem B2634545 : Blo 432776 2634545 := bstep (se 2 (by rfl) ⟨987954, by rfl⟩ : syracuseStep 2634545 = 1975909) B1975909
theorem B652097 : Blo 432776 652097 := bstep (se 2 (by rfl) ⟨244536, by rfl⟩ : syracuseStep 652097 = 489073) B489073
theorem B1233731 : Blo 432776 1233731 := bstep (se 1 (by rfl) ⟨925298, by rfl⟩ : syracuseStep 1233731 = 1850597) B1850597
theorem B619331 : Blo 432776 619331 := bstep (se 1 (by rfl) ⟨464498, by rfl⟩ : syracuseStep 619331 = 928997) B928997
theorem B979793 : Blo 432776 979793 := bstep (se 2 (by rfl) ⟨367422, by rfl⟩ : syracuseStep 979793 = 734845) B734845
theorem B1102673 : Blo 432776 1102673 := bstep (se 2 (by rfl) ⟨413502, by rfl⟩ : syracuseStep 1102673 = 827005) B827005
theorem B652115 : Blo 432776 652115 := bstep (se 1 (by rfl) ⟨489086, by rfl⟩ : syracuseStep 652115 = 978173) B978173
theorem B734035 : Blo 432776 734035 := bstep (se 1 (by rfl) ⟨550526, by rfl⟩ : syracuseStep 734035 = 1101053) B1101053
theorem B979811 : Blo 432776 979811 := bstep (se 1 (by rfl) ⟨734858, by rfl⟩ : syracuseStep 979811 = 1469717) B1469717
theorem B652145 : Blo 432776 652145 := bstep (se 2 (by rfl) ⟨244554, by rfl⟩ : syracuseStep 652145 = 489109) B489109
theorem B824195 : Blo 432776 824195 := bstep (se 1 (by rfl) ⟨618146, by rfl⟩ : syracuseStep 824195 = 1236293) B1236293
theorem B652163 : Blo 432776 652163 := bstep (se 1 (by rfl) ⟨489122, by rfl⟩ : syracuseStep 652163 = 978245) B978245
theorem B652193 : Blo 432776 652193 := bstep (se 2 (by rfl) ⟨244572, by rfl⟩ : syracuseStep 652193 = 489145) B489145
theorem B488371 : Blo 432776 488371 := bstep (se 1 (by rfl) ⟨366278, by rfl⟩ : syracuseStep 488371 = 732557) B732557
theorem B652211 : Blo 432776 652211 := bstep (se 1 (by rfl) ⟨489158, by rfl⟩ : syracuseStep 652211 = 978317) B978317
theorem B463811 : Blo 432776 463811 := bstep (se 1 (by rfl) ⟨347858, by rfl⟩ : syracuseStep 463811 = 695717) B695717
theorem B652241 : Blo 432776 652241 := bstep (se 2 (by rfl) ⟨244590, by rfl⟩ : syracuseStep 652241 = 489181) B489181
theorem B734177 : Blo 432776 734177 := bstep (se 2 (by rfl) ⟨275316, by rfl⟩ : syracuseStep 734177 = 550633) B550633
theorem B652259 : Blo 432776 652259 := bstep (se 1 (by rfl) ⟨489194, by rfl⟩ : syracuseStep 652259 = 978389) B978389
theorem B652289 : Blo 432776 652289 := bstep (se 2 (by rfl) ⟨244608, by rfl⟩ : syracuseStep 652289 = 489217) B489217
theorem B1905677 : Blo 432776 1905677 := bstep (se 3 (by rfl) ⟨357314, by rfl⟩ : syracuseStep 1905677 = 714629) B714629
theorem B652307 : Blo 432776 652307 := bstep (se 1 (by rfl) ⟨489230, by rfl⟩ : syracuseStep 652307 = 978461) B978461
theorem B1463345 : Blo 432776 1463345 := bstep (se 2 (by rfl) ⟨548754, by rfl⟩ : syracuseStep 1463345 = 1097509) B1097509
theorem B652337 : Blo 432776 652337 := bstep (se 2 (by rfl) ⟨244626, by rfl⟩ : syracuseStep 652337 = 489253) B489253
theorem B488515 : Blo 432776 488515 := bstep (se 1 (by rfl) ⟨366386, by rfl⟩ : syracuseStep 488515 = 732773) B732773
theorem B652355 : Blo 432776 652355 := bstep (se 1 (by rfl) ⟨489266, by rfl⟩ : syracuseStep 652355 = 978533) B978533
theorem B652385 : Blo 432776 652385 := bstep (se 2 (by rfl) ⟨244644, by rfl⟩ : syracuseStep 652385 = 489289) B489289
theorem B734305 : Blo 432776 734305 := bstep (se 2 (by rfl) ⟨275364, by rfl⟩ : syracuseStep 734305 = 550729) B550729
theorem B980081 : Blo 432776 980081 := bstep (se 2 (by rfl) ⟨367530, by rfl⟩ : syracuseStep 980081 = 735061) B735061
theorem B652403 : Blo 432776 652403 := bstep (se 1 (by rfl) ⟨489302, by rfl⟩ : syracuseStep 652403 = 978605) B978605
theorem B439427 : Blo 432776 439427 := bstep (se 1 (by rfl) ⟨329570, by rfl⟩ : syracuseStep 439427 = 659141) B659141
theorem B734339 : Blo 432776 734339 := bstep (se 1 (by rfl) ⟨550754, by rfl⟩ : syracuseStep 734339 = 1101509) B1101509
theorem B980099 : Blo 432776 980099 := bstep (se 1 (by rfl) ⟨735074, by rfl⟩ : syracuseStep 980099 = 1470149) B1470149
theorem B1234061 : Blo 432776 1234061 := bstep (se 3 (by rfl) ⟨231386, by rfl⟩ : syracuseStep 1234061 = 462773) B462773
theorem B1651853 : Blo 432776 1651853 := bstep (se 3 (by rfl) ⟨309722, by rfl⟩ : syracuseStep 1651853 = 619445) B619445
theorem B652433 : Blo 432776 652433 := bstep (se 2 (by rfl) ⟨244662, by rfl⟩ : syracuseStep 652433 = 489325) B489325
theorem B652451 : Blo 432776 652451 := bstep (se 1 (by rfl) ⟨489338, by rfl⟩ : syracuseStep 652451 = 978677) B978677
theorem B652481 : Blo 432776 652481 := bstep (se 2 (by rfl) ⟨244680, by rfl⟩ : syracuseStep 652481 = 489361) B489361
theorem B1234129 : Blo 432776 1234129 := bstep (se 2 (by rfl) ⟨462798, by rfl⟩ : syracuseStep 1234129 = 925597) B925597
theorem B488659 : Blo 432776 488659 := bstep (se 1 (by rfl) ⟨366494, by rfl⟩ : syracuseStep 488659 = 732989) B732989
theorem B652499 : Blo 432776 652499 := bstep (se 1 (by rfl) ⟨489374, by rfl⟩ : syracuseStep 652499 = 978749) B978749
theorem B3953891 : Blo 432776 3953891 := bstep (se 1 (by rfl) ⟨2965418, by rfl⟩ : syracuseStep 3953891 = 5930837) B5930837
theorem B1766627 : Blo 432776 1766627 := bstep (se 1 (by rfl) ⟨1324970, by rfl⟩ : syracuseStep 1766627 = 2649941) B2649941
theorem B1193197 : Blo 432776 1193197 := bstep (se 3 (by rfl) ⟨223724, by rfl⟩ : syracuseStep 1193197 = 447449) B447449
theorem B652529 : Blo 432776 652529 := bstep (se 2 (by rfl) ⟨244698, by rfl⟩ : syracuseStep 652529 = 489397) B489397
theorem B652547 : Blo 432776 652547 := bstep (se 1 (by rfl) ⟨489410, by rfl⟩ : syracuseStep 652547 = 978821) B978821
theorem B734467 : Blo 432776 734467 := bstep (se 1 (by rfl) ⟨550850, by rfl⟩ : syracuseStep 734467 = 1101701) B1101701
theorem B652577 : Blo 432776 652577 := bstep (se 2 (by rfl) ⟨244716, by rfl⟩ : syracuseStep 652577 = 489433) B489433
theorem B652595 : Blo 432776 652595 := bstep (se 1 (by rfl) ⟨489446, by rfl⟩ : syracuseStep 652595 = 978893) B978893
theorem B2790733 : Blo 432776 2790733 := bstep (se 3 (by rfl) ⟨523262, by rfl⟩ : syracuseStep 2790733 = 1046525) B1046525
theorem B652625 : Blo 432776 652625 := bstep (se 2 (by rfl) ⟨244734, by rfl⟩ : syracuseStep 652625 = 489469) B489469
theorem B826595 : Blo 432776 826595 := bstep (se 1 (by rfl) ⟨619946, by rfl⟩ : syracuseStep 826595 = 1239893) B1239893
theorem B488803 : Blo 432776 488803 := bstep (se 1 (by rfl) ⟨366602, by rfl⟩ : syracuseStep 488803 = 733205) B733205
theorem B2200931 : Blo 432776 2200931 := bstep (se 1 (by rfl) ⟨1650698, by rfl⟩ : syracuseStep 2200931 = 3301397) B3301397
theorem B652643 : Blo 432776 652643 := bstep (se 1 (by rfl) ⟨489482, by rfl⟩ : syracuseStep 652643 = 978965) B978965
theorem B652673 : Blo 432776 652673 := bstep (se 2 (by rfl) ⟨244752, by rfl⟩ : syracuseStep 652673 = 489505) B489505
theorem B660881 : Blo 432776 660881 := bstep (se 2 (by rfl) ⟨247830, by rfl⟩ : syracuseStep 660881 = 495661) B495661
theorem B734609 : Blo 432776 734609 := bstep (se 2 (by rfl) ⟨275478, by rfl⟩ : syracuseStep 734609 = 550957) B550957
theorem B652691 : Blo 432776 652691 := bstep (se 1 (by rfl) ⟨489518, by rfl⟩ : syracuseStep 652691 = 979037) B979037
theorem B980369 : Blo 432776 980369 := bstep (se 2 (by rfl) ⟨367638, by rfl⟩ : syracuseStep 980369 = 735277) B735277
theorem B882083 : Blo 432776 882083 := bstep (se 1 (by rfl) ⟨661562, by rfl⟩ : syracuseStep 882083 = 1323125) B1323125
theorem B980387 : Blo 432776 980387 := bstep (se 1 (by rfl) ⟨735290, by rfl⟩ : syracuseStep 980387 = 1470581) B1470581
theorem B652721 : Blo 432776 652721 := bstep (se 2 (by rfl) ⟨244770, by rfl⟩ : syracuseStep 652721 = 489541) B489541
theorem B619969 : Blo 432776 619969 := bstep (se 2 (by rfl) ⟨232488, by rfl⟩ : syracuseStep 619969 = 464977) B464977
theorem B652739 : Blo 432776 652739 := bstep (se 1 (by rfl) ⟨489554, by rfl⟩ : syracuseStep 652739 = 979109) B979109
theorem B1234403 : Blo 432776 1234403 := bstep (se 1 (by rfl) ⟨925802, by rfl⟩ : syracuseStep 1234403 = 1851605) B1851605
theorem B652769 : Blo 432776 652769 := bstep (se 2 (by rfl) ⟨244788, by rfl⟩ : syracuseStep 652769 = 489577) B489577
theorem B1390061 : Blo 432776 1390061 := bstep (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) B521273
theorem B833009 : Blo 432776 833009 := bstep (se 2 (by rfl) ⟨312378, by rfl⟩ : syracuseStep 833009 = 624757) B624757
theorem B488947 : Blo 432776 488947 := bstep (se 1 (by rfl) ⟨366710, by rfl⟩ : syracuseStep 488947 = 733421) B733421
theorem B652787 : Blo 432776 652787 := bstep (se 1 (by rfl) ⟨489590, by rfl⟩ : syracuseStep 652787 = 979181) B979181
theorem B652817 : Blo 432776 652817 := bstep (se 2 (by rfl) ⟨244806, by rfl⟩ : syracuseStep 652817 = 489613) B489613
theorem B734737 : Blo 432776 734737 := bstep (se 2 (by rfl) ⟨275526, by rfl⟩ : syracuseStep 734737 = 551053) B551053
theorem B652835 : Blo 432776 652835 := bstep (se 1 (by rfl) ⟨489626, by rfl⟩ : syracuseStep 652835 = 979253) B979253
theorem B1504813 : Blo 432776 1504813 := bstep (se 3 (by rfl) ⟨282152, by rfl⟩ : syracuseStep 1504813 = 564305) B564305
theorem B734771 : Blo 432776 734771 := bstep (se 1 (by rfl) ⟨551078, by rfl⟩ : syracuseStep 734771 = 1102157) B1102157
theorem B620083 : Blo 432776 620083 := bstep (se 1 (by rfl) ⟨465062, by rfl⟩ : syracuseStep 620083 = 930125) B930125
theorem B652865 : Blo 432776 652865 := bstep (se 2 (by rfl) ⟨244824, by rfl⟩ : syracuseStep 652865 = 489649) B489649
theorem B1463885 : Blo 432776 1463885 := bstep (se 3 (by rfl) ⟨274478, by rfl⟩ : syracuseStep 1463885 = 548957) B548957
theorem B2479693 : Blo 432776 2479693 := bstep (se 3 (by rfl) ⟨464942, by rfl⟩ : syracuseStep 2479693 = 929885) B929885
theorem B652883 : Blo 432776 652883 := bstep (se 1 (by rfl) ⟨489662, by rfl⟩ : syracuseStep 652883 = 979325) B979325
theorem B652913 : Blo 432776 652913 := bstep (se 2 (by rfl) ⟨244842, by rfl⟩ : syracuseStep 652913 = 489685) B489685
theorem B1463939 : Blo 432776 1463939 := bstep (se 1 (by rfl) ⟨1097954, by rfl⟩ : syracuseStep 1463939 = 2195909) B2195909
theorem B489091 : Blo 432776 489091 := bstep (se 1 (by rfl) ⟨366818, by rfl⟩ : syracuseStep 489091 = 733637) B733637
theorem B661123 : Blo 432776 661123 := bstep (se 1 (by rfl) ⟨495842, by rfl⟩ : syracuseStep 661123 = 991685) B991685
theorem B652931 : Blo 432776 652931 := bstep (se 1 (by rfl) ⟨489698, by rfl⟩ : syracuseStep 652931 = 979397) B979397
theorem B652961 : Blo 432776 652961 := bstep (se 2 (by rfl) ⟨244860, by rfl⟩ : syracuseStep 652961 = 489721) B489721
theorem B464563 : Blo 432776 464563 := bstep (se 1 (by rfl) ⟨348422, by rfl⟩ : syracuseStep 464563 = 696845) B696845
theorem B652979 : Blo 432776 652979 := bstep (se 1 (by rfl) ⟨489734, by rfl⟩ : syracuseStep 652979 = 979469) B979469
theorem B734899 : Blo 432776 734899 := bstep (se 1 (by rfl) ⟨551174, by rfl⟩ : syracuseStep 734899 = 1102349) B1102349
theorem B440003 : Blo 432776 440003 := bstep (se 1 (by rfl) ⟨330002, by rfl⟩ : syracuseStep 440003 = 660005) B660005
theorem B653009 : Blo 432776 653009 := bstep (se 2 (by rfl) ⟨244878, by rfl⟩ : syracuseStep 653009 = 489757) B489757
theorem B1644259 : Blo 432776 1644259 := bstep (se 1 (by rfl) ⟨1233194, by rfl⟩ : syracuseStep 1644259 = 2466389) B2466389
theorem B440035 : Blo 432776 440035 := bstep (se 1 (by rfl) ⟨330026, by rfl⟩ : syracuseStep 440035 = 660053) B660053
theorem B653027 : Blo 432776 653027 := bstep (se 1 (by rfl) ⟨489770, by rfl⟩ : syracuseStep 653027 = 979541) B979541
theorem B8369891 : Blo 432776 8369891 := bstep (se 1 (by rfl) ⟨6277418, by rfl⟩ : syracuseStep 8369891 = 12554837) B12554837
theorem B653057 : Blo 432776 653057 := bstep (se 2 (by rfl) ⟨244896, by rfl⟩ : syracuseStep 653057 = 489793) B489793
theorem B489235 : Blo 432776 489235 := bstep (se 1 (by rfl) ⟨366926, by rfl⟩ : syracuseStep 489235 = 733853) B733853
theorem B653075 : Blo 432776 653075 := bstep (se 1 (by rfl) ⟨489806, by rfl⟩ : syracuseStep 653075 = 979613) B979613
theorem B825137 : Blo 432776 825137 := bstep (se 2 (by rfl) ⟨309426, by rfl⟩ : syracuseStep 825137 = 618853) B618853
theorem B653105 : Blo 432776 653105 := bstep (se 2 (by rfl) ⟨244914, by rfl⟩ : syracuseStep 653105 = 489829) B489829
theorem B735041 : Blo 432776 735041 := bstep (se 2 (by rfl) ⟨275640, by rfl⟩ : syracuseStep 735041 = 551281) B551281
theorem B653123 : Blo 432776 653123 := bstep (se 1 (by rfl) ⟨489842, by rfl⟩ : syracuseStep 653123 = 979685) B979685
theorem B653153 : Blo 432776 653153 := bstep (se 2 (by rfl) ⟨244932, by rfl⟩ : syracuseStep 653153 = 489865) B489865
theorem B653171 : Blo 432776 653171 := bstep (se 1 (by rfl) ⟨489878, by rfl⟩ : syracuseStep 653171 = 979757) B979757
theorem B1464209 : Blo 432776 1464209 := bstep (se 2 (by rfl) ⟨549078, by rfl⟩ : syracuseStep 1464209 = 1098157) B1098157
theorem B653201 : Blo 432776 653201 := bstep (se 2 (by rfl) ⟨244950, by rfl⟩ : syracuseStep 653201 = 489901) B489901
theorem B489379 : Blo 432776 489379 := bstep (se 1 (by rfl) ⟨367034, by rfl⟩ : syracuseStep 489379 = 734069) B734069
theorem B653219 : Blo 432776 653219 := bstep (se 1 (by rfl) ⟨489914, by rfl⟩ : syracuseStep 653219 = 979829) B979829
theorem B1046449 : Blo 432776 1046449 := bstep (se 2 (by rfl) ⟨392418, by rfl⟩ : syracuseStep 1046449 = 784837) B784837
theorem B653249 : Blo 432776 653249 := bstep (se 2 (by rfl) ⟨244968, by rfl⟩ : syracuseStep 653249 = 489937) B489937
theorem B735169 : Blo 432776 735169 := bstep (se 2 (by rfl) ⟨275688, by rfl⟩ : syracuseStep 735169 = 551377) B551377
theorem B653267 : Blo 432776 653267 := bstep (se 1 (by rfl) ⟨489950, by rfl⟩ : syracuseStep 653267 = 979901) B979901
theorem B8353763 : Blo 432776 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B735203 : Blo 432776 735203 := bstep (se 1 (by rfl) ⟨551402, by rfl⟩ : syracuseStep 735203 = 1102805) B1102805
theorem B653297 : Blo 432776 653297 := bstep (se 2 (by rfl) ⟨244986, by rfl⟩ : syracuseStep 653297 = 489973) B489973
theorem B653315 : Blo 432776 653315 := bstep (se 1 (by rfl) ⟨489986, by rfl⟩ : syracuseStep 653315 = 979973) B979973
theorem B653345 : Blo 432776 653345 := bstep (se 2 (by rfl) ⟨245004, by rfl⟩ : syracuseStep 653345 = 490009) B490009
theorem B784433 : Blo 432776 784433 := bstep (se 2 (by rfl) ⟨294162, by rfl⟩ : syracuseStep 784433 = 588325) B588325
theorem B489523 : Blo 432776 489523 := bstep (se 1 (by rfl) ⟨367142, by rfl⟩ : syracuseStep 489523 = 734285) B734285
theorem B653363 : Blo 432776 653363 := bstep (se 1 (by rfl) ⟨490022, by rfl⟩ : syracuseStep 653363 = 980045) B980045
theorem B653393 : Blo 432776 653393 := bstep (se 2 (by rfl) ⟨245022, by rfl⟩ : syracuseStep 653393 = 490045) B490045
theorem B653411 : Blo 432776 653411 := bstep (se 1 (by rfl) ⟨490058, by rfl⟩ : syracuseStep 653411 = 980117) B980117
theorem B735331 : Blo 432776 735331 := bstep (se 1 (by rfl) ⟨551498, by rfl⟩ : syracuseStep 735331 = 1102997) B1102997
theorem B653441 : Blo 432776 653441 := bstep (se 2 (by rfl) ⟨245040, by rfl⟩ : syracuseStep 653441 = 490081) B490081
theorem B2201741 : Blo 432776 2201741 := bstep (se 3 (by rfl) ⟨412826, by rfl⟩ : syracuseStep 2201741 = 825653) B825653
theorem B653459 : Blo 432776 653459 := bstep (se 1 (by rfl) ⟨490094, by rfl⟩ : syracuseStep 653459 = 980189) B980189
theorem B653489 : Blo 432776 653489 := bstep (se 2 (by rfl) ⟨245058, by rfl⟩ : syracuseStep 653489 = 490117) B490117
theorem B489667 : Blo 432776 489667 := bstep (se 1 (by rfl) ⟨367250, by rfl⟩ : syracuseStep 489667 = 734501) B734501
theorem B653507 : Blo 432776 653507 := bstep (se 1 (by rfl) ⟨490130, by rfl⟩ : syracuseStep 653507 = 980261) B980261
theorem B1095889 : Blo 432776 1095889 := bstep (se 2 (by rfl) ⟨410958, by rfl⟩ : syracuseStep 1095889 = 821917) B821917
theorem B653537 : Blo 432776 653537 := bstep (se 2 (by rfl) ⟨245076, by rfl⟩ : syracuseStep 653537 = 490153) B490153
theorem B653555 : Blo 432776 653555 := bstep (se 1 (by rfl) ⟨490166, by rfl⟩ : syracuseStep 653555 = 980333) B980333
theorem B653585 : Blo 432776 653585 := bstep (se 2 (by rfl) ⟨245094, by rfl⟩ : syracuseStep 653585 = 490189) B490189
theorem B653603 : Blo 432776 653603 := bstep (se 1 (by rfl) ⟨490202, by rfl⟩ : syracuseStep 653603 = 980405) B980405
theorem B1235245 : Blo 432776 1235245 := bstep (se 3 (by rfl) ⟨231608, by rfl⟩ : syracuseStep 1235245 = 463217) B463217
theorem B694595 : Blo 432776 694595 := bstep (se 1 (by rfl) ⟨520946, by rfl⟩ : syracuseStep 694595 = 1041893) B1041893
theorem B653633 : Blo 432776 653633 := bstep (se 2 (by rfl) ⟨245112, by rfl⟩ : syracuseStep 653633 = 490225) B490225
theorem B489811 : Blo 432776 489811 := bstep (se 1 (by rfl) ⟨367358, by rfl⟩ : syracuseStep 489811 = 734717) B734717
theorem B653651 : Blo 432776 653651 := bstep (se 1 (by rfl) ⟨490238, by rfl⟩ : syracuseStep 653651 = 980477) B980477
theorem B588163 : Blo 432776 588163 := bstep (se 1 (by rfl) ⟨441122, by rfl⟩ : syracuseStep 588163 = 882245) B882245
theorem B1464749 : Blo 432776 1464749 := bstep (se 3 (by rfl) ⟨274640, by rfl⟩ : syracuseStep 1464749 = 549281) B549281
theorem B588227 : Blo 432776 588227 := bstep (se 1 (by rfl) ⟨441170, by rfl⟩ : syracuseStep 588227 = 882341) B882341
theorem B3578309 : Blo 432776 3578309 := bstep (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) B670933
theorem B1235405 : Blo 432776 1235405 := bstep (se 3 (by rfl) ⟨231638, by rfl⟩ : syracuseStep 1235405 = 463277) B463277
theorem B1096163 : Blo 432776 1096163 := bstep (se 1 (by rfl) ⟨822122, by rfl⟩ : syracuseStep 1096163 = 1644245) B1644245
theorem B1464803 : Blo 432776 1464803 := bstep (se 1 (by rfl) ⟨1098602, by rfl⟩ : syracuseStep 1464803 = 2197205) B2197205
theorem B489955 : Blo 432776 489955 := bstep (se 1 (by rfl) ⟨367466, by rfl⟩ : syracuseStep 489955 = 734933) B734933
theorem B2849293 : Blo 432776 2849293 := bstep (se 3 (by rfl) ⟨534242, by rfl⟩ : syracuseStep 2849293 = 1068485) B1068485
theorem B15039029 : Blo 432776 15039029 := bstep (se 5 (by rfl) ⟨704954, by rfl⟩ : syracuseStep 15039029 = 1409909) B1409909
theorem B3299939 : Blo 432776 3299939 := bstep (se 1 (by rfl) ⟨2474954, by rfl⟩ : syracuseStep 3299939 = 4949909) B4949909
theorem B490099 : Blo 432776 490099 := bstep (se 1 (by rfl) ⟨367574, by rfl⟩ : syracuseStep 490099 = 735149) B735149
theorem B1235587 : Blo 432776 1235587 := bstep (se 1 (by rfl) ⟨926690, by rfl⟩ : syracuseStep 1235587 = 1853381) B1853381
theorem B432787 : Blo 432776 432787 := bstep (se 1 (by rfl) ⟨324590, by rfl⟩ : syracuseStep 432787 = 649181) B649181
theorem B432803 : Blo 432776 432803 := bstep (se 1 (by rfl) ⟨324602, by rfl⟩ : syracuseStep 432803 = 649205) B649205
theorem B1096355 : Blo 432776 1096355 := bstep (se 1 (by rfl) ⟨822266, by rfl⟩ : syracuseStep 1096355 = 1644533) B1644533
theorem B826033 : Blo 432776 826033 := bstep (se 2 (by rfl) ⟨309762, by rfl⟩ : syracuseStep 826033 = 619525) B619525
theorem B432819 : Blo 432776 432819 := bstep (se 1 (by rfl) ⟨324614, by rfl⟩ : syracuseStep 432819 = 649229) B649229
theorem B432835 : Blo 432776 432835 := bstep (se 1 (by rfl) ⟨324626, by rfl⟩ : syracuseStep 432835 = 649253) B649253
theorem B432851 : Blo 432776 432851 := bstep (se 1 (by rfl) ⟨324638, by rfl⟩ : syracuseStep 432851 = 649277) B649277
theorem B432867 : Blo 432776 432867 := bstep (se 1 (by rfl) ⟨324650, by rfl⟩ : syracuseStep 432867 = 649301) B649301
theorem B1465073 : Blo 432776 1465073 := bstep (se 2 (by rfl) ⟨549402, by rfl⟩ : syracuseStep 1465073 = 1098805) B1098805
theorem B432883 : Blo 432776 432883 := bstep (se 1 (by rfl) ⟨324662, by rfl⟩ : syracuseStep 432883 = 649325) B649325
theorem B432899 : Blo 432776 432899 := bstep (se 1 (by rfl) ⟨324674, by rfl⟩ : syracuseStep 432899 = 649349) B649349
theorem B490243 : Blo 432776 490243 := bstep (se 1 (by rfl) ⟨367682, by rfl⟩ : syracuseStep 490243 = 735365) B735365
theorem B432915 : Blo 432776 432915 := bstep (se 1 (by rfl) ⟨324686, by rfl⟩ : syracuseStep 432915 = 649373) B649373
theorem B432931 : Blo 432776 432931 := bstep (se 1 (by rfl) ⟨324698, by rfl⟩ : syracuseStep 432931 = 649397) B649397
theorem B940835 : Blo 432776 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B1334065 : Blo 432776 1334065 := bstep (se 2 (by rfl) ⟨500274, by rfl⟩ : syracuseStep 1334065 = 1000549) B1000549
theorem B432947 : Blo 432776 432947 := bstep (se 1 (by rfl) ⟨324710, by rfl⟩ : syracuseStep 432947 = 649421) B649421
theorem B432963 : Blo 432776 432963 := bstep (se 1 (by rfl) ⟨324722, by rfl⟩ : syracuseStep 432963 = 649445) B649445
theorem B826193 : Blo 432776 826193 := bstep (se 2 (by rfl) ⟨309822, by rfl⟩ : syracuseStep 826193 = 619645) B619645
theorem B432979 : Blo 432776 432979 := bstep (se 1 (by rfl) ⟨324734, by rfl⟩ : syracuseStep 432979 = 649469) B649469
theorem B432995 : Blo 432776 432995 := bstep (se 1 (by rfl) ⟨324746, by rfl⟩ : syracuseStep 432995 = 649493) B649493
theorem B1858403 : Blo 432776 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B2235235 : Blo 432776 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B2194289 : Blo 432776 2194289 := bstep (se 2 (by rfl) ⟨822858, by rfl⟩ : syracuseStep 2194289 = 1645717) B1645717
theorem B433011 : Blo 432776 433011 := bstep (se 1 (by rfl) ⟨324758, by rfl⟩ : syracuseStep 433011 = 649517) B649517
theorem B924547 : Blo 432776 924547 := bstep (se 1 (by rfl) ⟨693410, by rfl⟩ : syracuseStep 924547 = 1386821) B1386821
theorem B433027 : Blo 432776 433027 := bstep (se 1 (by rfl) ⟨324770, by rfl⟩ : syracuseStep 433027 = 649541) B649541
theorem B6331277 : Blo 432776 6331277 := bstep (se 3 (by rfl) ⟨1187114, by rfl⟩ : syracuseStep 6331277 = 2374229) B2374229
theorem B433043 : Blo 432776 433043 := bstep (se 1 (by rfl) ⟨324782, by rfl⟩ : syracuseStep 433043 = 649565) B649565
theorem B433059 : Blo 432776 433059 := bstep (se 1 (by rfl) ⟨324794, by rfl⟩ : syracuseStep 433059 = 649589) B649589
theorem B2775971 : Blo 432776 2775971 := bstep (se 1 (by rfl) ⟨2081978, by rfl⟩ : syracuseStep 2775971 = 4163957) B4163957
theorem B433075 : Blo 432776 433075 := bstep (se 1 (by rfl) ⟨324806, by rfl⟩ : syracuseStep 433075 = 649613) B649613
theorem B973763 : Blo 432776 973763 := bstep (se 1 (by rfl) ⟨730322, by rfl⟩ : syracuseStep 973763 = 1460645) B1460645
theorem B433091 : Blo 432776 433091 := bstep (se 1 (by rfl) ⟨324818, by rfl⟩ : syracuseStep 433091 = 649637) B649637
theorem B1055683 : Blo 432776 1055683 := bstep (se 1 (by rfl) ⟨791762, by rfl⟩ : syracuseStep 1055683 = 1583525) B1583525
theorem B1334225 : Blo 432776 1334225 := bstep (se 2 (by rfl) ⟨500334, by rfl⟩ : syracuseStep 1334225 = 1000669) B1000669
theorem B433107 : Blo 432776 433107 := bstep (se 1 (by rfl) ⟨324830, by rfl⟩ : syracuseStep 433107 = 649661) B649661
theorem B433123 : Blo 432776 433123 := bstep (se 1 (by rfl) ⟨324842, by rfl⟩ : syracuseStep 433123 = 649685) B649685
theorem B1850339 : Blo 432776 1850339 := bstep (se 1 (by rfl) ⟨1387754, by rfl⟩ : syracuseStep 1850339 = 2775509) B2775509
theorem B433139 : Blo 432776 433139 := bstep (se 1 (by rfl) ⟨324854, by rfl⟩ : syracuseStep 433139 = 649709) B649709
theorem B433155 : Blo 432776 433155 := bstep (se 1 (by rfl) ⟨324866, by rfl⟩ : syracuseStep 433155 = 649733) B649733
theorem B3521549 : Blo 432776 3521549 := bstep (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) B1320581
theorem B433171 : Blo 432776 433171 := bstep (se 1 (by rfl) ⟨324878, by rfl⟩ : syracuseStep 433171 = 649757) B649757
theorem B433187 : Blo 432776 433187 := bstep (se 1 (by rfl) ⟨324890, by rfl⟩ : syracuseStep 433187 = 649781) B649781
theorem B1391651 : Blo 432776 1391651 := bstep (se 1 (by rfl) ⟨1043738, by rfl⟩ : syracuseStep 1391651 = 2087477) B2087477
theorem B433203 : Blo 432776 433203 := bstep (se 1 (by rfl) ⟨324902, by rfl⟩ : syracuseStep 433203 = 649805) B649805
theorem B433219 : Blo 432776 433219 := bstep (se 1 (by rfl) ⟨324914, by rfl⟩ : syracuseStep 433219 = 649829) B649829
theorem B2849869 : Blo 432776 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B433235 : Blo 432776 433235 := bstep (se 1 (by rfl) ⟨324926, by rfl⟩ : syracuseStep 433235 = 649853) B649853
theorem B433251 : Blo 432776 433251 := bstep (se 1 (by rfl) ⟨324938, by rfl⟩ : syracuseStep 433251 = 649877) B649877
theorem B433267 : Blo 432776 433267 := bstep (se 1 (by rfl) ⟨324950, by rfl⟩ : syracuseStep 433267 = 649901) B649901
theorem B433283 : Blo 432776 433283 := bstep (se 1 (by rfl) ⟨324962, by rfl⟩ : syracuseStep 433283 = 649925) B649925
theorem B695441 : Blo 432776 695441 := bstep (se 2 (by rfl) ⟨260790, by rfl⟩ : syracuseStep 695441 = 521581) B521581
theorem B433299 : Blo 432776 433299 := bstep (se 1 (by rfl) ⟨324974, by rfl⟩ : syracuseStep 433299 = 649949) B649949
theorem B2464931 : Blo 432776 2464931 := bstep (se 1 (by rfl) ⟨1848698, by rfl⟩ : syracuseStep 2464931 = 3697397) B3697397
theorem B433315 : Blo 432776 433315 := bstep (se 1 (by rfl) ⟨324986, by rfl⟩ : syracuseStep 433315 = 649973) B649973
theorem B433331 : Blo 432776 433331 := bstep (se 1 (by rfl) ⟨324998, by rfl⟩ : syracuseStep 433331 = 649997) B649997
theorem B433347 : Blo 432776 433347 := bstep (se 1 (by rfl) ⟨325010, by rfl⟩ : syracuseStep 433347 = 650021) B650021
theorem B1653965 : Blo 432776 1653965 := bstep (se 3 (by rfl) ⟨310118, by rfl⟩ : syracuseStep 1653965 = 620237) B620237
theorem B974033 : Blo 432776 974033 := bstep (se 2 (by rfl) ⟨365262, by rfl⟩ : syracuseStep 974033 = 730525) B730525
theorem B433363 : Blo 432776 433363 := bstep (se 1 (by rfl) ⟨325022, by rfl⟩ : syracuseStep 433363 = 650045) B650045
theorem B974051 : Blo 432776 974051 := bstep (se 1 (by rfl) ⟨730538, by rfl⟩ : syracuseStep 974051 = 1461077) B1461077
theorem B1170659 : Blo 432776 1170659 := bstep (se 1 (by rfl) ⟨877994, by rfl⟩ : syracuseStep 1170659 = 1755989) B1755989
theorem B433379 : Blo 432776 433379 := bstep (se 1 (by rfl) ⟨325034, by rfl⟩ : syracuseStep 433379 = 650069) B650069
theorem B1391843 : Blo 432776 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B433395 : Blo 432776 433395 := bstep (se 1 (by rfl) ⟨325046, by rfl⟩ : syracuseStep 433395 = 650093) B650093
theorem B433411 : Blo 432776 433411 := bstep (se 1 (by rfl) ⟨325058, by rfl⟩ : syracuseStep 433411 = 650117) B650117
theorem B1465613 : Blo 432776 1465613 := bstep (se 3 (by rfl) ⟨274802, by rfl⟩ : syracuseStep 1465613 = 549605) B549605
theorem B695569 : Blo 432776 695569 := bstep (se 2 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 695569 = 521677) B521677
theorem B990481 : Blo 432776 990481 := bstep (se 2 (by rfl) ⟨371430, by rfl⟩ : syracuseStep 990481 = 742861) B742861
theorem B433427 : Blo 432776 433427 := bstep (se 1 (by rfl) ⟨325070, by rfl⟩ : syracuseStep 433427 = 650141) B650141
theorem B433443 : Blo 432776 433443 := bstep (se 1 (by rfl) ⟨325082, by rfl⟩ : syracuseStep 433443 = 650165) B650165
theorem B548147 : Blo 432776 548147 := bstep (se 1 (by rfl) ⟨411110, by rfl⟩ : syracuseStep 548147 = 822221) B822221
theorem B433459 : Blo 432776 433459 := bstep (se 1 (by rfl) ⟨325094, by rfl⟩ : syracuseStep 433459 = 650189) B650189
theorem B433475 : Blo 432776 433475 := bstep (se 1 (by rfl) ⟨325106, by rfl⟩ : syracuseStep 433475 = 650213) B650213
theorem B1465667 : Blo 432776 1465667 := bstep (se 1 (by rfl) ⟨1099250, by rfl⟩ : syracuseStep 1465667 = 2198501) B2198501
theorem B695633 : Blo 432776 695633 := bstep (se 2 (by rfl) ⟨260862, by rfl⟩ : syracuseStep 695633 = 521725) B521725
theorem B433491 : Blo 432776 433491 := bstep (se 1 (by rfl) ⟨325118, by rfl⟩ : syracuseStep 433491 = 650237) B650237
theorem B433507 : Blo 432776 433507 := bstep (se 1 (by rfl) ⟨325130, by rfl⟩ : syracuseStep 433507 = 650261) B650261
theorem B433523 : Blo 432776 433523 := bstep (se 1 (by rfl) ⟨325142, by rfl⟩ : syracuseStep 433523 = 650285) B650285
theorem B433539 : Blo 432776 433539 := bstep (se 1 (by rfl) ⟨325154, by rfl⟩ : syracuseStep 433539 = 650309) B650309
theorem B433555 : Blo 432776 433555 := bstep (se 1 (by rfl) ⟨325166, by rfl⟩ : syracuseStep 433555 = 650333) B650333
theorem B433571 : Blo 432776 433571 := bstep (se 1 (by rfl) ⟨325178, by rfl⟩ : syracuseStep 433571 = 650357) B650357
theorem B433587 : Blo 432776 433587 := bstep (se 1 (by rfl) ⟨325190, by rfl⟩ : syracuseStep 433587 = 650381) B650381
theorem B433603 : Blo 432776 433603 := bstep (se 1 (by rfl) ⟨325202, by rfl⟩ : syracuseStep 433603 = 650405) B650405
theorem B1564109 : Blo 432776 1564109 := bstep (se 3 (by rfl) ⟨293270, by rfl⟩ : syracuseStep 1564109 = 586541) B586541
theorem B433619 : Blo 432776 433619 := bstep (se 1 (by rfl) ⟨325214, by rfl⟩ : syracuseStep 433619 = 650429) B650429
theorem B433635 : Blo 432776 433635 := bstep (se 1 (by rfl) ⟨325226, by rfl⟩ : syracuseStep 433635 = 650453) B650453
theorem B974321 : Blo 432776 974321 := bstep (se 2 (by rfl) ⟨365370, by rfl⟩ : syracuseStep 974321 = 730741) B730741
theorem B433651 : Blo 432776 433651 := bstep (se 1 (by rfl) ⟨325238, by rfl⟩ : syracuseStep 433651 = 650477) B650477
theorem B974339 : Blo 432776 974339 := bstep (se 1 (by rfl) ⟨730754, by rfl⟩ : syracuseStep 974339 = 1461509) B1461509
theorem B433667 : Blo 432776 433667 := bstep (se 1 (by rfl) ⟨325250, by rfl⟩ : syracuseStep 433667 = 650501) B650501
theorem B2481677 : Blo 432776 2481677 := bstep (se 3 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 2481677 = 930629) B930629
theorem B433683 : Blo 432776 433683 := bstep (se 1 (by rfl) ⟨325262, by rfl⟩ : syracuseStep 433683 = 650525) B650525
theorem B433699 : Blo 432776 433699 := bstep (se 1 (by rfl) ⟨325274, by rfl⟩ : syracuseStep 433699 = 650549) B650549
theorem B433715 : Blo 432776 433715 := bstep (se 1 (by rfl) ⟨325286, by rfl⟩ : syracuseStep 433715 = 650573) B650573
theorem B433731 : Blo 432776 433731 := bstep (se 1 (by rfl) ⟨325298, by rfl⟩ : syracuseStep 433731 = 650597) B650597
theorem B1097297 : Blo 432776 1097297 := bstep (se 2 (by rfl) ⟨411486, by rfl⟩ : syracuseStep 1097297 = 822973) B822973
theorem B1465937 : Blo 432776 1465937 := bstep (se 2 (by rfl) ⟨549726, by rfl⟩ : syracuseStep 1465937 = 1099453) B1099453
theorem B433747 : Blo 432776 433747 := bstep (se 1 (by rfl) ⟨325310, by rfl⟩ : syracuseStep 433747 = 650621) B650621
theorem B433763 : Blo 432776 433763 := bstep (se 1 (by rfl) ⟨325322, by rfl⟩ : syracuseStep 433763 = 650645) B650645
theorem B433779 : Blo 432776 433779 := bstep (se 1 (by rfl) ⟨325334, by rfl⟩ : syracuseStep 433779 = 650669) B650669
theorem B1482371 : Blo 432776 1482371 := bstep (se 1 (by rfl) ⟨1111778, by rfl⟩ : syracuseStep 1482371 = 2223557) B2223557
theorem B1097347 : Blo 432776 1097347 := bstep (se 1 (by rfl) ⟨823010, by rfl⟩ : syracuseStep 1097347 = 1646021) B1646021
theorem B433795 : Blo 432776 433795 := bstep (se 1 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 433795 = 650693) B650693
theorem B433811 : Blo 432776 433811 := bstep (se 1 (by rfl) ⟨325358, by rfl⟩ : syracuseStep 433811 = 650717) B650717
theorem B433827 : Blo 432776 433827 := bstep (se 1 (by rfl) ⟨325370, by rfl⟩ : syracuseStep 433827 = 650741) B650741
theorem B433843 : Blo 432776 433843 := bstep (se 1 (by rfl) ⟨325382, by rfl⟩ : syracuseStep 433843 = 650765) B650765
theorem B433859 : Blo 432776 433859 := bstep (se 1 (by rfl) ⟨325394, by rfl⟩ : syracuseStep 433859 = 650789) B650789
theorem B564931 : Blo 432776 564931 := bstep (se 1 (by rfl) ⟨423698, by rfl⟩ : syracuseStep 564931 = 847397) B847397
theorem B433875 : Blo 432776 433875 := bstep (se 1 (by rfl) ⟨325406, by rfl⟩ : syracuseStep 433875 = 650813) B650813
theorem B433891 : Blo 432776 433891 := bstep (se 1 (by rfl) ⟨325418, by rfl⟩ : syracuseStep 433891 = 650837) B650837
theorem B433907 : Blo 432776 433907 := bstep (se 1 (by rfl) ⟨325430, by rfl⟩ : syracuseStep 433907 = 650861) B650861
theorem B433923 : Blo 432776 433923 := bstep (se 1 (by rfl) ⟨325442, by rfl⟩ : syracuseStep 433923 = 650885) B650885
theorem B974609 : Blo 432776 974609 := bstep (se 2 (by rfl) ⟨365478, by rfl⟩ : syracuseStep 974609 = 730957) B730957
theorem B1097489 : Blo 432776 1097489 := bstep (se 2 (by rfl) ⟨411558, by rfl⟩ : syracuseStep 1097489 = 823117) B823117
theorem B433939 : Blo 432776 433939 := bstep (se 1 (by rfl) ⟨325454, by rfl⟩ : syracuseStep 433939 = 650909) B650909
theorem B974627 : Blo 432776 974627 := bstep (se 1 (by rfl) ⟨730970, by rfl⟩ : syracuseStep 974627 = 1461941) B1461941
theorem B433955 : Blo 432776 433955 := bstep (se 1 (by rfl) ⟨325466, by rfl⟩ : syracuseStep 433955 = 650933) B650933
theorem B433971 : Blo 432776 433971 := bstep (se 1 (by rfl) ⟨325478, by rfl⟩ : syracuseStep 433971 = 650957) B650957
theorem B433987 : Blo 432776 433987 := bstep (se 1 (by rfl) ⟨325490, by rfl⟩ : syracuseStep 433987 = 650981) B650981
theorem B434003 : Blo 432776 434003 := bstep (se 1 (by rfl) ⟨325502, by rfl⟩ : syracuseStep 434003 = 651005) B651005
theorem B434019 : Blo 432776 434019 := bstep (se 1 (by rfl) ⟨325514, by rfl⟩ : syracuseStep 434019 = 651029) B651029
theorem B1392497 : Blo 432776 1392497 := bstep (se 2 (by rfl) ⟨522186, by rfl⟩ : syracuseStep 1392497 = 1044373) B1044373
theorem B434035 : Blo 432776 434035 := bstep (se 1 (by rfl) ⟨325526, by rfl⟩ : syracuseStep 434035 = 651053) B651053
theorem B434051 : Blo 432776 434051 := bstep (se 1 (by rfl) ⟨325538, by rfl⟩ : syracuseStep 434051 = 651077) B651077
theorem B2473861 : Blo 432776 2473861 := bstep (se 4 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 2473861 = 463849) B463849
theorem B1646477 : Blo 432776 1646477 := bstep (se 3 (by rfl) ⟨308714, by rfl⟩ : syracuseStep 1646477 = 617429) B617429
theorem B434067 : Blo 432776 434067 := bstep (se 1 (by rfl) ⟨325550, by rfl⟩ : syracuseStep 434067 = 651101) B651101
theorem B434083 : Blo 432776 434083 := bstep (se 1 (by rfl) ⟨325562, by rfl⟩ : syracuseStep 434083 = 651125) B651125
theorem B745379 : Blo 432776 745379 := bstep (se 1 (by rfl) ⟨559034, by rfl⟩ : syracuseStep 745379 = 1118069) B1118069
theorem B434099 : Blo 432776 434099 := bstep (se 1 (by rfl) ⟨325574, by rfl⟩ : syracuseStep 434099 = 651149) B651149
theorem B434115 : Blo 432776 434115 := bstep (se 1 (by rfl) ⟨325586, by rfl⟩ : syracuseStep 434115 = 651173) B651173
theorem B434131 : Blo 432776 434131 := bstep (se 1 (by rfl) ⟨325598, by rfl⟩ : syracuseStep 434131 = 651197) B651197
theorem B434147 : Blo 432776 434147 := bstep (se 1 (by rfl) ⟨325610, by rfl⟩ : syracuseStep 434147 = 651221) B651221
theorem B1236977 : Blo 432776 1236977 := bstep (se 2 (by rfl) ⟨463866, by rfl⟩ : syracuseStep 1236977 = 927733) B927733
theorem B548851 : Blo 432776 548851 := bstep (se 1 (by rfl) ⟨411638, by rfl⟩ : syracuseStep 548851 = 823277) B823277
theorem B434163 : Blo 432776 434163 := bstep (se 1 (by rfl) ⟨325622, by rfl⟩ : syracuseStep 434163 = 651245) B651245
theorem B434187 : Blo 432776 434187 := bstep (se 1 (by rfl) ⟨325640, by rfl⟩ : syracuseStep 434187 = 651281) B651281
theorem B434199 : Blo 432776 434199 := bstep (se 1 (by rfl) ⟨325649, by rfl⟩ : syracuseStep 434199 = 651299) B651299
theorem B434219 : Blo 432776 434219 := bstep (se 1 (by rfl) ⟨325664, by rfl⟩ : syracuseStep 434219 = 651329) B651329
theorem B434231 : Blo 432776 434231 := bstep (se 1 (by rfl) ⟨325673, by rfl⟩ : syracuseStep 434231 = 651347) B651347
theorem B1335361 : Blo 432776 1335361 := bstep (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) B1001521
theorem B434251 : Blo 432776 434251 := bstep (se 1 (by rfl) ⟨325688, by rfl⟩ : syracuseStep 434251 = 651377) B651377
theorem B434263 : Blo 432776 434263 := bstep (se 1 (by rfl) ⟨325697, by rfl⟩ : syracuseStep 434263 = 651395) B651395
theorem B434283 : Blo 432776 434283 := bstep (se 1 (by rfl) ⟨325712, by rfl⟩ : syracuseStep 434283 = 651425) B651425
theorem B434295 : Blo 432776 434295 := bstep (se 1 (by rfl) ⟨325721, by rfl⟩ : syracuseStep 434295 = 651443) B651443
theorem B2089091 : Blo 432776 2089091 := bstep (se 1 (by rfl) ⟨1566818, by rfl⟩ : syracuseStep 2089091 = 3133637) B3133637
theorem B974987 : Blo 432776 974987 := bstep (se 1 (by rfl) ⟨731240, by rfl⟩ : syracuseStep 974987 = 1462481) B1462481
theorem B434315 : Blo 432776 434315 := bstep (se 1 (by rfl) ⟨325736, by rfl⟩ : syracuseStep 434315 = 651473) B651473
theorem B4169879 : Blo 432776 4169879 := bstep (se 1 (by rfl) ⟨3127409, by rfl⟩ : syracuseStep 4169879 = 6254819) B6254819
theorem B434327 : Blo 432776 434327 := bstep (se 1 (by rfl) ⟨325745, by rfl⟩ : syracuseStep 434327 = 651491) B651491
theorem B2474135 : Blo 432776 2474135 := bstep (se 1 (by rfl) ⟨1855601, by rfl⟩ : syracuseStep 2474135 = 3711203) B3711203
theorem B434347 : Blo 432776 434347 := bstep (se 1 (by rfl) ⟨325760, by rfl⟩ : syracuseStep 434347 = 651521) B651521
theorem B3178673 : Blo 432776 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B434359 : Blo 432776 434359 := bstep (se 1 (by rfl) ⟨325769, by rfl⟩ : syracuseStep 434359 = 651539) B651539
theorem B975041 : Blo 432776 975041 := bstep (se 2 (by rfl) ⟨365640, by rfl⟩ : syracuseStep 975041 = 731281) B731281
theorem B434379 : Blo 432776 434379 := bstep (se 1 (by rfl) ⟨325784, by rfl⟩ : syracuseStep 434379 = 651569) B651569
theorem B434391 : Blo 432776 434391 := bstep (se 1 (by rfl) ⟨325793, by rfl⟩ : syracuseStep 434391 = 651587) B651587
theorem B1097945 : Blo 432776 1097945 := bstep (se 2 (by rfl) ⟨411729, by rfl⟩ : syracuseStep 1097945 = 823459) B823459
theorem B1466585 : Blo 432776 1466585 := bstep (se 2 (by rfl) ⟨549969, by rfl⟩ : syracuseStep 1466585 = 1099939) B1099939
theorem B434411 : Blo 432776 434411 := bstep (se 1 (by rfl) ⟨325808, by rfl⟩ : syracuseStep 434411 = 651617) B651617
theorem B434423 : Blo 432776 434423 := bstep (se 1 (by rfl) ⟨325817, by rfl⟩ : syracuseStep 434423 = 651635) B651635
theorem B434443 : Blo 432776 434443 := bstep (se 1 (by rfl) ⟨325832, by rfl⟩ : syracuseStep 434443 = 651665) B651665
theorem B1040663 : Blo 432776 1040663 := bstep (se 1 (by rfl) ⟨780497, by rfl⟩ : syracuseStep 1040663 = 1560995) B1560995
theorem B434455 : Blo 432776 434455 := bstep (se 1 (by rfl) ⟨325841, by rfl⟩ : syracuseStep 434455 = 651683) B651683
theorem B434475 : Blo 432776 434475 := bstep (se 1 (by rfl) ⟨325856, by rfl⟩ : syracuseStep 434475 = 651713) B651713
theorem B434487 : Blo 432776 434487 := bstep (se 1 (by rfl) ⟨325865, by rfl⟩ : syracuseStep 434487 = 651731) B651731
theorem B5005633 : Blo 432776 5005633 := bstep (se 2 (by rfl) ⟨1877112, by rfl⟩ : syracuseStep 5005633 = 3754225) B3754225
theorem B4702529 : Blo 432776 4702529 := bstep (se 2 (by rfl) ⟨1763448, by rfl⟩ : syracuseStep 4702529 = 3526897) B3526897
theorem B434507 : Blo 432776 434507 := bstep (se 1 (by rfl) ⟨325880, by rfl⟩ : syracuseStep 434507 = 651761) B651761
theorem B434519 : Blo 432776 434519 := bstep (se 1 (by rfl) ⟨325889, by rfl⟩ : syracuseStep 434519 = 651779) B651779
theorem B1171805 : Blo 432776 1171805 := bstep (se 3 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 1171805 = 439427) B439427
theorem B434539 : Blo 432776 434539 := bstep (se 1 (by rfl) ⟨325904, by rfl⟩ : syracuseStep 434539 = 651809) B651809
theorem B434551 : Blo 432776 434551 := bstep (se 1 (by rfl) ⟨325913, by rfl⟩ : syracuseStep 434551 = 651827) B651827
theorem B434571 : Blo 432776 434571 := bstep (se 1 (by rfl) ⟨325928, by rfl⟩ : syracuseStep 434571 = 651857) B651857
theorem B1646993 : Blo 432776 1646993 := bstep (se 2 (by rfl) ⟨617622, by rfl⟩ : syracuseStep 1646993 = 1235245) B1235245
theorem B549271 : Blo 432776 549271 := bstep (se 1 (by rfl) ⟨411953, by rfl⟩ : syracuseStep 549271 = 823907) B823907
theorem B434583 : Blo 432776 434583 := bstep (se 1 (by rfl) ⟨325937, by rfl⟩ : syracuseStep 434583 = 651875) B651875
theorem B975257 : Blo 432776 975257 := bstep (se 2 (by rfl) ⟨365721, by rfl⟩ : syracuseStep 975257 = 731443) B731443
theorem B434603 : Blo 432776 434603 := bstep (se 1 (by rfl) ⟨325952, by rfl⟩ : syracuseStep 434603 = 651905) B651905
theorem B434615 : Blo 432776 434615 := bstep (se 1 (by rfl) ⟨325961, by rfl⟩ : syracuseStep 434615 = 651923) B651923
theorem B434635 : Blo 432776 434635 := bstep (se 1 (by rfl) ⟨325976, by rfl⟩ : syracuseStep 434635 = 651953) B651953
theorem B434647 : Blo 432776 434647 := bstep (se 1 (by rfl) ⟨325985, by rfl⟩ : syracuseStep 434647 = 651971) B651971
theorem B434667 : Blo 432776 434667 := bstep (se 1 (by rfl) ⟨326000, by rfl⟩ : syracuseStep 434667 = 652001) B652001
theorem B975347 : Blo 432776 975347 := bstep (se 1 (by rfl) ⟨731510, by rfl⟩ : syracuseStep 975347 = 1463021) B1463021
theorem B434679 : Blo 432776 434679 := bstep (se 1 (by rfl) ⟨326009, by rfl⟩ : syracuseStep 434679 = 652019) B652019
theorem B434699 : Blo 432776 434699 := bstep (se 1 (by rfl) ⟨326024, by rfl⟩ : syracuseStep 434699 = 652049) B652049
theorem B975383 : Blo 432776 975383 := bstep (se 1 (by rfl) ⟨731537, by rfl⟩ : syracuseStep 975383 = 1463075) B1463075
theorem B836119 : Blo 432776 836119 := bstep (se 1 (by rfl) ⟨627089, by rfl⟩ : syracuseStep 836119 = 1254179) B1254179
theorem B434711 : Blo 432776 434711 := bstep (se 1 (by rfl) ⟨326033, by rfl⟩ : syracuseStep 434711 = 652067) B652067
theorem B434731 : Blo 432776 434731 := bstep (se 1 (by rfl) ⟨326048, by rfl⟩ : syracuseStep 434731 = 652097) B652097
theorem B434743 : Blo 432776 434743 := bstep (se 1 (by rfl) ⟨326057, by rfl⟩ : syracuseStep 434743 = 652115) B652115
theorem B1851979 : Blo 432776 1851979 := bstep (se 1 (by rfl) ⟨1388984, by rfl⟩ : syracuseStep 1851979 = 2777969) B2777969
theorem B434763 : Blo 432776 434763 := bstep (se 1 (by rfl) ⟨326072, by rfl⟩ : syracuseStep 434763 = 652145) B652145
theorem B434775 : Blo 432776 434775 := bstep (se 1 (by rfl) ⟨326081, by rfl⟩ : syracuseStep 434775 = 652163) B652163
theorem B10543709 : Blo 432776 10543709 := bstep (se 3 (by rfl) ⟨1976945, by rfl⟩ : syracuseStep 10543709 = 3953891) B3953891
theorem B3711581 : Blo 432776 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B434795 : Blo 432776 434795 := bstep (se 1 (by rfl) ⟨326096, by rfl⟩ : syracuseStep 434795 = 652193) B652193
theorem B434807 : Blo 432776 434807 := bstep (se 1 (by rfl) ⟨326105, by rfl⟩ : syracuseStep 434807 = 652211) B652211
theorem B434827 : Blo 432776 434827 := bstep (se 1 (by rfl) ⟨326120, by rfl⟩ : syracuseStep 434827 = 652241) B652241
theorem B434839 : Blo 432776 434839 := bstep (se 1 (by rfl) ⟨326129, by rfl⟩ : syracuseStep 434839 = 652259) B652259
theorem B434859 : Blo 432776 434859 := bstep (se 1 (by rfl) ⟨326144, by rfl⟩ : syracuseStep 434859 = 652289) B652289
theorem B1270451 : Blo 432776 1270451 := bstep (se 1 (by rfl) ⟨952838, by rfl⟩ : syracuseStep 1270451 = 1905677) B1905677
theorem B434871 : Blo 432776 434871 := bstep (se 1 (by rfl) ⟨326153, by rfl⟩ : syracuseStep 434871 = 652307) B652307
theorem B975563 : Blo 432776 975563 := bstep (se 1 (by rfl) ⟨731672, by rfl⟩ : syracuseStep 975563 = 1463345) B1463345
theorem B434891 : Blo 432776 434891 := bstep (se 1 (by rfl) ⟨326168, by rfl⟩ : syracuseStep 434891 = 652337) B652337
theorem B434903 : Blo 432776 434903 := bstep (se 1 (by rfl) ⟨326177, by rfl⟩ : syracuseStep 434903 = 652355) B652355
theorem B1860317 : Blo 432776 1860317 := bstep (se 3 (by rfl) ⟨348809, by rfl⟩ : syracuseStep 1860317 = 697619) B697619
theorem B434923 : Blo 432776 434923 := bstep (se 1 (by rfl) ⟨326192, by rfl⟩ : syracuseStep 434923 = 652385) B652385
theorem B434935 : Blo 432776 434935 := bstep (se 1 (by rfl) ⟨326201, by rfl⟩ : syracuseStep 434935 = 652403) B652403
theorem B975617 : Blo 432776 975617 := bstep (se 2 (by rfl) ⟨365856, by rfl⟩ : syracuseStep 975617 = 731713) B731713
theorem B434955 : Blo 432776 434955 := bstep (se 1 (by rfl) ⟨326216, by rfl⟩ : syracuseStep 434955 = 652433) B652433
theorem B434967 : Blo 432776 434967 := bstep (se 1 (by rfl) ⟨326225, by rfl⟩ : syracuseStep 434967 = 652451) B652451
theorem B434987 : Blo 432776 434987 := bstep (se 1 (by rfl) ⟨326240, by rfl⟩ : syracuseStep 434987 = 652481) B652481
theorem B434999 : Blo 432776 434999 := bstep (se 1 (by rfl) ⟨326249, by rfl⟩ : syracuseStep 434999 = 652499) B652499
theorem B435019 : Blo 432776 435019 := bstep (se 1 (by rfl) ⟨326264, by rfl⟩ : syracuseStep 435019 = 652529) B652529
theorem B435031 : Blo 432776 435031 := bstep (se 1 (by rfl) ⟨326273, by rfl⟩ : syracuseStep 435031 = 652547) B652547
theorem B1647449 : Blo 432776 1647449 := bstep (se 2 (by rfl) ⟨617793, by rfl⟩ : syracuseStep 1647449 = 1235587) B1235587
theorem B1852253 : Blo 432776 1852253 := bstep (se 3 (by rfl) ⟨347297, by rfl⟩ : syracuseStep 1852253 = 694595) B694595
theorem B435051 : Blo 432776 435051 := bstep (se 1 (by rfl) ⟨326288, by rfl⟩ : syracuseStep 435051 = 652577) B652577
theorem B435063 : Blo 432776 435063 := bstep (se 1 (by rfl) ⟨326297, by rfl⟩ : syracuseStep 435063 = 652595) B652595
theorem B435083 : Blo 432776 435083 := bstep (se 1 (by rfl) ⟨326312, by rfl⟩ : syracuseStep 435083 = 652625) B652625
theorem B1467287 : Blo 432776 1467287 := bstep (se 1 (by rfl) ⟨1100465, by rfl⟩ : syracuseStep 1467287 = 2200931) B2200931
theorem B435095 : Blo 432776 435095 := bstep (se 1 (by rfl) ⟨326321, by rfl⟩ : syracuseStep 435095 = 652643) B652643
theorem B435115 : Blo 432776 435115 := bstep (se 1 (by rfl) ⟨326336, by rfl⟩ : syracuseStep 435115 = 652673) B652673
theorem B435127 : Blo 432776 435127 := bstep (se 1 (by rfl) ⟨326345, by rfl⟩ : syracuseStep 435127 = 652691) B652691
theorem B435147 : Blo 432776 435147 := bstep (se 1 (by rfl) ⟨326360, by rfl⟩ : syracuseStep 435147 = 652721) B652721
theorem B435159 : Blo 432776 435159 := bstep (se 1 (by rfl) ⟨326369, by rfl⟩ : syracuseStep 435159 = 652739) B652739
theorem B975833 : Blo 432776 975833 := bstep (se 2 (by rfl) ⟨365937, by rfl⟩ : syracuseStep 975833 = 731875) B731875
theorem B1393625 : Blo 432776 1393625 := bstep (se 2 (by rfl) ⟨522609, by rfl⟩ : syracuseStep 1393625 = 1045219) B1045219
theorem B435179 : Blo 432776 435179 := bstep (se 1 (by rfl) ⟨326384, by rfl⟩ : syracuseStep 435179 = 652769) B652769
theorem B435191 : Blo 432776 435191 := bstep (se 1 (by rfl) ⟨326393, by rfl⟩ : syracuseStep 435191 = 652787) B652787
theorem B435211 : Blo 432776 435211 := bstep (se 1 (by rfl) ⟨326408, by rfl⟩ : syracuseStep 435211 = 652817) B652817
theorem B435223 : Blo 432776 435223 := bstep (se 1 (by rfl) ⟨326417, by rfl⟩ : syracuseStep 435223 = 652835) B652835
theorem B435243 : Blo 432776 435243 := bstep (se 1 (by rfl) ⟨326432, by rfl⟩ : syracuseStep 435243 = 652865) B652865
theorem B1647661 : Blo 432776 1647661 := bstep (se 3 (by rfl) ⟨308936, by rfl⟩ : syracuseStep 1647661 = 617873) B617873
theorem B975923 : Blo 432776 975923 := bstep (se 1 (by rfl) ⟨731942, by rfl⟩ : syracuseStep 975923 = 1463885) B1463885
theorem B435255 : Blo 432776 435255 := bstep (se 1 (by rfl) ⟨326441, by rfl⟩ : syracuseStep 435255 = 652883) B652883
theorem B1778753 : Blo 432776 1778753 := bstep (se 2 (by rfl) ⟨667032, by rfl⟩ : syracuseStep 1778753 = 1334065) B1334065
theorem B435275 : Blo 432776 435275 := bstep (se 1 (by rfl) ⟨326456, by rfl⟩ : syracuseStep 435275 = 652913) B652913
theorem B975959 : Blo 432776 975959 := bstep (se 1 (by rfl) ⟨731969, by rfl⟩ : syracuseStep 975959 = 1463939) B1463939
theorem B435287 : Blo 432776 435287 := bstep (se 1 (by rfl) ⟨326465, by rfl⟩ : syracuseStep 435287 = 652931) B652931
theorem B1238105 : Blo 432776 1238105 := bstep (se 2 (by rfl) ⟨464289, by rfl⟩ : syracuseStep 1238105 = 928579) B928579
theorem B435307 : Blo 432776 435307 := bstep (se 1 (by rfl) ⟨326480, by rfl⟩ : syracuseStep 435307 = 652961) B652961
theorem B435319 : Blo 432776 435319 := bstep (se 1 (by rfl) ⟨326489, by rfl⟩ : syracuseStep 435319 = 652979) B652979
theorem B435339 : Blo 432776 435339 := bstep (se 1 (by rfl) ⟨326504, by rfl⟩ : syracuseStep 435339 = 653009) B653009
theorem B435351 : Blo 432776 435351 := bstep (se 1 (by rfl) ⟨326513, by rfl⟩ : syracuseStep 435351 = 653027) B653027
theorem B5579927 : Blo 432776 5579927 := bstep (se 1 (by rfl) ⟨4184945, by rfl⟩ : syracuseStep 5579927 = 8369891) B8369891
theorem B435371 : Blo 432776 435371 := bstep (se 1 (by rfl) ⟨326528, by rfl⟩ : syracuseStep 435371 = 653057) B653057
theorem B2671795 : Blo 432776 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B1852595 : Blo 432776 1852595 := bstep (se 1 (by rfl) ⟨1389446, by rfl⟩ : syracuseStep 1852595 = 2778893) B2778893
theorem B435383 : Blo 432776 435383 := bstep (se 1 (by rfl) ⟨326537, by rfl⟩ : syracuseStep 435383 = 653075) B653075
theorem B550091 : Blo 432776 550091 := bstep (se 1 (by rfl) ⟨412568, by rfl⟩ : syracuseStep 550091 = 825137) B825137
theorem B435403 : Blo 432776 435403 := bstep (se 1 (by rfl) ⟨326552, by rfl⟩ : syracuseStep 435403 = 653105) B653105
theorem B435415 : Blo 432776 435415 := bstep (se 1 (by rfl) ⟨326561, by rfl⟩ : syracuseStep 435415 = 653123) B653123
theorem B435435 : Blo 432776 435435 := bstep (se 1 (by rfl) ⟨326576, by rfl⟩ : syracuseStep 435435 = 653153) B653153
theorem B7496945 : Blo 432776 7496945 := bstep (se 2 (by rfl) ⟨2811354, by rfl⟩ : syracuseStep 7496945 = 5622709) B5622709
theorem B435447 : Blo 432776 435447 := bstep (se 1 (by rfl) ⟨326585, by rfl⟩ : syracuseStep 435447 = 653171) B653171
theorem B32531717 : Blo 432776 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B976139 : Blo 432776 976139 := bstep (se 1 (by rfl) ⟨732104, by rfl⟩ : syracuseStep 976139 = 1464209) B1464209
theorem B435467 : Blo 432776 435467 := bstep (se 1 (by rfl) ⟨326600, by rfl⟩ : syracuseStep 435467 = 653201) B653201
theorem B435479 : Blo 432776 435479 := bstep (se 1 (by rfl) ⟨326609, by rfl⟩ : syracuseStep 435479 = 653219) B653219
theorem B435499 : Blo 432776 435499 := bstep (se 1 (by rfl) ⟨326624, by rfl⟩ : syracuseStep 435499 = 653249) B653249
theorem B2221357 : Blo 432776 2221357 := bstep (se 3 (by rfl) ⟨416504, by rfl⟩ : syracuseStep 2221357 = 833009) B833009
theorem B435511 : Blo 432776 435511 := bstep (se 1 (by rfl) ⟨326633, by rfl⟩ : syracuseStep 435511 = 653267) B653267
theorem B976193 : Blo 432776 976193 := bstep (se 2 (by rfl) ⟨366072, by rfl⟩ : syracuseStep 976193 = 732145) B732145
theorem B435531 : Blo 432776 435531 := bstep (se 1 (by rfl) ⟨326648, by rfl⟩ : syracuseStep 435531 = 653297) B653297
theorem B435543 : Blo 432776 435543 := bstep (se 1 (by rfl) ⟨326657, by rfl⟩ : syracuseStep 435543 = 653315) B653315
theorem B1647965 : Blo 432776 1647965 := bstep (se 3 (by rfl) ⟨308993, by rfl⟩ : syracuseStep 1647965 = 617987) B617987
theorem B435563 : Blo 432776 435563 := bstep (se 1 (by rfl) ⟨326672, by rfl⟩ : syracuseStep 435563 = 653345) B653345
theorem B435575 : Blo 432776 435575 := bstep (se 1 (by rfl) ⟨326681, by rfl⟩ : syracuseStep 435575 = 653363) B653363
theorem B435595 : Blo 432776 435595 := bstep (se 1 (by rfl) ⟨326696, by rfl⟩ : syracuseStep 435595 = 653393) B653393
theorem B435607 : Blo 432776 435607 := bstep (se 1 (by rfl) ⟨326705, by rfl⟩ : syracuseStep 435607 = 653411) B653411
theorem B435627 : Blo 432776 435627 := bstep (se 1 (by rfl) ⟨326720, by rfl⟩ : syracuseStep 435627 = 653441) B653441
theorem B1467827 : Blo 432776 1467827 := bstep (se 1 (by rfl) ⟨1100870, by rfl⟩ : syracuseStep 1467827 = 2201741) B2201741
theorem B435639 : Blo 432776 435639 := bstep (se 1 (by rfl) ⟨326729, by rfl⟩ : syracuseStep 435639 = 653459) B653459
theorem B435659 : Blo 432776 435659 := bstep (se 1 (by rfl) ⟨326744, by rfl⟩ : syracuseStep 435659 = 653489) B653489
theorem B435671 : Blo 432776 435671 := bstep (se 1 (by rfl) ⟨326753, by rfl⟩ : syracuseStep 435671 = 653507) B653507
theorem B435691 : Blo 432776 435691 := bstep (se 1 (by rfl) ⟨326768, by rfl⟩ : syracuseStep 435691 = 653537) B653537
theorem B435703 : Blo 432776 435703 := bstep (se 1 (by rfl) ⟨326777, by rfl⟩ : syracuseStep 435703 = 653555) B653555
theorem B435723 : Blo 432776 435723 := bstep (se 1 (by rfl) ⟨326792, by rfl⟩ : syracuseStep 435723 = 653585) B653585
theorem B435735 : Blo 432776 435735 := bstep (se 1 (by rfl) ⟨326801, by rfl⟩ : syracuseStep 435735 = 653603) B653603
theorem B976409 : Blo 432776 976409 := bstep (se 2 (by rfl) ⟨366153, by rfl⟩ : syracuseStep 976409 = 732307) B732307
theorem B435755 : Blo 432776 435755 := bstep (se 1 (by rfl) ⟨326816, by rfl⟩ : syracuseStep 435755 = 653633) B653633
theorem B435767 : Blo 432776 435767 := bstep (se 1 (by rfl) ⟨326825, by rfl⟩ : syracuseStep 435767 = 653651) B653651
theorem B976499 : Blo 432776 976499 := bstep (se 1 (by rfl) ⟨732374, by rfl⟩ : syracuseStep 976499 = 1464749) B1464749
theorem B2385539 : Blo 432776 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B1590929 : Blo 432776 1590929 := bstep (se 2 (by rfl) ⟨596598, by rfl⟩ : syracuseStep 1590929 = 1193197) B1193197
theorem B730775 : Blo 432776 730775 := bstep (se 1 (by rfl) ⟨548081, by rfl⟩ : syracuseStep 730775 = 1096163) B1096163
theorem B976535 : Blo 432776 976535 := bstep (se 1 (by rfl) ⟨732401, by rfl⟩ : syracuseStep 976535 = 1464803) B1464803
theorem B755353 : Blo 432776 755353 := bstep (se 2 (by rfl) ⟨283257, by rfl⟩ : syracuseStep 755353 = 566515) B566515
theorem B927425 : Blo 432776 927425 := bstep (se 2 (by rfl) ⟨347784, by rfl⟩ : syracuseStep 927425 = 695569) B695569
theorem B1320641 : Blo 432776 1320641 := bstep (se 2 (by rfl) ⟨495240, by rfl⟩ : syracuseStep 1320641 = 990481) B990481
theorem B1468097 : Blo 432776 1468097 := bstep (se 2 (by rfl) ⟨550536, by rfl⟩ : syracuseStep 1468097 = 1101073) B1101073
theorem B3720977 : Blo 432776 3720977 := bstep (se 2 (by rfl) ⟨1395366, by rfl⟩ : syracuseStep 3720977 = 2790733) B2790733
theorem B730903 : Blo 432776 730903 := bstep (se 1 (by rfl) ⟨548177, by rfl⟩ : syracuseStep 730903 = 1096355) B1096355
theorem B7440173 : Blo 432776 7440173 := bstep (se 3 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 7440173 = 2790065) B2790065
theorem B976715 : Blo 432776 976715 := bstep (se 1 (by rfl) ⟨732536, by rfl⟩ : syracuseStep 976715 = 1465073) B1465073
theorem B1099595 : Blo 432776 1099595 := bstep (se 1 (by rfl) ⟨824696, by rfl⟩ : syracuseStep 1099595 = 1649393) B1649393
theorem B1173341 : Blo 432776 1173341 := bstep (se 3 (by rfl) ⟨220001, by rfl⟩ : syracuseStep 1173341 = 440003) B440003
theorem B976769 : Blo 432776 976769 := bstep (se 2 (by rfl) ⟨366288, by rfl⟩ : syracuseStep 976769 = 732577) B732577
theorem B550795 : Blo 432776 550795 := bstep (se 1 (by rfl) ⟨413096, by rfl⟩ : syracuseStep 550795 = 826193) B826193
theorem B4220851 : Blo 432776 4220851 := bstep (se 1 (by rfl) ⟨3165638, by rfl⟩ : syracuseStep 4220851 = 6331277) B6331277
theorem B649175 : Blo 432776 649175 := bstep (se 1 (by rfl) ⟨486881, by rfl⟩ : syracuseStep 649175 = 973763) B973763
theorem B927767 : Blo 432776 927767 := bstep (se 1 (by rfl) ⟨695825, by rfl⟩ : syracuseStep 927767 = 1391651) B1391651
theorem B649241 : Blo 432776 649241 := bstep (se 2 (by rfl) ⟨243465, by rfl⟩ : syracuseStep 649241 = 486931) B486931
theorem B976985 : Blo 432776 976985 := bstep (se 2 (by rfl) ⟨366369, by rfl⟩ : syracuseStep 976985 = 732739) B732739
theorem B1763417 : Blo 432776 1763417 := bstep (se 2 (by rfl) ⟨661281, by rfl⟩ : syracuseStep 1763417 = 1322563) B1322563
theorem B2508893 : Blo 432776 2508893 := bstep (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) B940835
theorem B649355 : Blo 432776 649355 := bstep (se 1 (by rfl) ⟨487016, by rfl⟩ : syracuseStep 649355 = 974033) B974033
theorem B649367 : Blo 432776 649367 := bstep (se 1 (by rfl) ⟨487025, by rfl⟩ : syracuseStep 649367 = 974051) B974051
theorem B780439 : Blo 432776 780439 := bstep (se 1 (by rfl) ⟨585329, by rfl⟩ : syracuseStep 780439 = 1170659) B1170659
theorem B551063 : Blo 432776 551063 := bstep (se 1 (by rfl) ⟨413297, by rfl⟩ : syracuseStep 551063 = 826595) B826595
theorem B977075 : Blo 432776 977075 := bstep (se 1 (by rfl) ⟨732806, by rfl⟩ : syracuseStep 977075 = 1465613) B1465613
theorem B977111 : Blo 432776 977111 := bstep (se 1 (by rfl) ⟨732833, by rfl⟩ : syracuseStep 977111 = 1465667) B1465667
theorem B649433 : Blo 432776 649433 := bstep (se 2 (by rfl) ⟨243537, by rfl⟩ : syracuseStep 649433 = 487075) B487075
theorem B1468637 : Blo 432776 1468637 := bstep (se 3 (by rfl) ⟨275369, by rfl⟩ : syracuseStep 1468637 = 550739) B550739
theorem B616729 : Blo 432776 616729 := bstep (se 2 (by rfl) ⟨231273, by rfl⟩ : syracuseStep 616729 = 462547) B462547
theorem B1042739 : Blo 432776 1042739 := bstep (se 1 (by rfl) ⟨782054, by rfl⟩ : syracuseStep 1042739 = 1564109) B1564109
theorem B1116467 : Blo 432776 1116467 := bstep (se 1 (by rfl) ⟨837350, by rfl⟩ : syracuseStep 1116467 = 1674701) B1674701
theorem B649547 : Blo 432776 649547 := bstep (se 1 (by rfl) ⟨487160, by rfl⟩ : syracuseStep 649547 = 974321) B974321
theorem B649559 : Blo 432776 649559 := bstep (se 1 (by rfl) ⟨487169, by rfl⟩ : syracuseStep 649559 = 974339) B974339
theorem B2197853 : Blo 432776 2197853 := bstep (se 3 (by rfl) ⟨412097, by rfl⟩ : syracuseStep 2197853 = 824195) B824195
theorem B731531 : Blo 432776 731531 := bstep (se 1 (by rfl) ⟨548648, by rfl⟩ : syracuseStep 731531 = 1097297) B1097297
theorem B977291 : Blo 432776 977291 := bstep (se 1 (by rfl) ⟨732968, by rfl⟩ : syracuseStep 977291 = 1465937) B1465937
theorem B649625 : Blo 432776 649625 := bstep (se 2 (by rfl) ⟨243609, by rfl⟩ : syracuseStep 649625 = 487219) B487219
theorem B977345 : Blo 432776 977345 := bstep (se 2 (by rfl) ⟨366504, by rfl⟩ : syracuseStep 977345 = 733009) B733009
theorem B2779609 : Blo 432776 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B649739 : Blo 432776 649739 := bstep (se 1 (by rfl) ⟨487304, by rfl⟩ : syracuseStep 649739 = 974609) B974609
theorem B731659 : Blo 432776 731659 := bstep (se 1 (by rfl) ⟨548744, by rfl⟩ : syracuseStep 731659 = 1097489) B1097489
theorem B649751 : Blo 432776 649751 := bstep (se 1 (by rfl) ⟨487313, by rfl⟩ : syracuseStep 649751 = 974627) B974627
theorem B4999715 : Blo 432776 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B1395265 : Blo 432776 1395265 := bstep (se 2 (by rfl) ⟨523224, by rfl⟩ : syracuseStep 1395265 = 1046449) B1046449
theorem B928331 : Blo 432776 928331 := bstep (se 1 (by rfl) ⟨696248, by rfl⟩ : syracuseStep 928331 = 1392497) B1392497
theorem B649817 : Blo 432776 649817 := bstep (se 2 (by rfl) ⟨243681, by rfl⟩ : syracuseStep 649817 = 487363) B487363
theorem B731801 : Blo 432776 731801 := bstep (se 2 (by rfl) ⟨274425, by rfl⟩ : syracuseStep 731801 = 548851) B548851
theorem B977561 : Blo 432776 977561 := bstep (se 2 (by rfl) ⟨366585, by rfl⟩ : syracuseStep 977561 = 733171) B733171
theorem B1460915 : Blo 432776 1460915 := bstep (se 1 (by rfl) ⟨1095686, by rfl⟩ : syracuseStep 1460915 = 2191373) B2191373
theorem B1239745 : Blo 432776 1239745 := bstep (se 2 (by rfl) ⟨464904, by rfl⟩ : syracuseStep 1239745 = 929809) B929809
theorem B821963 : Blo 432776 821963 := bstep (se 1 (by rfl) ⟨616472, by rfl⟩ : syracuseStep 821963 = 1232945) B1232945
theorem B649931 : Blo 432776 649931 := bstep (se 1 (by rfl) ⟨487448, by rfl⟩ : syracuseStep 649931 = 974897) B974897
theorem B649943 : Blo 432776 649943 := bstep (se 1 (by rfl) ⟨487457, by rfl⟩ : syracuseStep 649943 = 974915) B974915
theorem B3959513 : Blo 432776 3959513 := bstep (se 2 (by rfl) ⟨1484817, by rfl⟩ : syracuseStep 3959513 = 2969635) B2969635
theorem B1288921 : Blo 432776 1288921 := bstep (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) B966691
theorem B977651 : Blo 432776 977651 := bstep (se 1 (by rfl) ⟨733238, by rfl⟩ : syracuseStep 977651 = 1466477) B1466477
theorem B781067 : Blo 432776 781067 := bstep (se 1 (by rfl) ⟨585800, by rfl⟩ : syracuseStep 781067 = 1171601) B1171601
theorem B977687 : Blo 432776 977687 := bstep (se 1 (by rfl) ⟨733265, by rfl⟩ : syracuseStep 977687 = 1466531) B1466531
theorem B1100567 : Blo 432776 1100567 := bstep (se 1 (by rfl) ⟨825425, by rfl⟩ : syracuseStep 1100567 = 1650851) B1650851
theorem B650009 : Blo 432776 650009 := bstep (se 2 (by rfl) ⟨243753, by rfl⟩ : syracuseStep 650009 = 487507) B487507
theorem B731929 : Blo 432776 731929 := bstep (se 2 (by rfl) ⟨274473, by rfl⟩ : syracuseStep 731929 = 548947) B548947
theorem B772915 : Blo 432776 772915 := bstep (se 1 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 772915 = 1159373) B1159373
theorem B822145 : Blo 432776 822145 := bstep (se 2 (by rfl) ⟨308304, by rfl⟩ : syracuseStep 822145 = 616609) B616609
theorem B650123 : Blo 432776 650123 := bstep (se 1 (by rfl) ⟨487592, by rfl⟩ : syracuseStep 650123 = 975185) B975185
theorem B650135 : Blo 432776 650135 := bstep (se 1 (by rfl) ⟨487601, by rfl⟩ : syracuseStep 650135 = 975203) B975203
theorem B1461185 : Blo 432776 1461185 := bstep (se 2 (by rfl) ⟨547944, by rfl⟩ : syracuseStep 1461185 = 1095889) B1095889
theorem B977867 : Blo 432776 977867 := bstep (se 1 (by rfl) ⟨733400, by rfl⟩ : syracuseStep 977867 = 1466801) B1466801
theorem B650201 : Blo 432776 650201 := bstep (se 2 (by rfl) ⟨243825, by rfl⟩ : syracuseStep 650201 = 487651) B487651
theorem B1272793 : Blo 432776 1272793 := bstep (se 2 (by rfl) ⟨477297, by rfl⟩ : syracuseStep 1272793 = 954595) B954595
theorem B977921 : Blo 432776 977921 := bstep (se 2 (by rfl) ⟨366720, by rfl⟩ : syracuseStep 977921 = 733441) B733441
theorem B1043507 : Blo 432776 1043507 := bstep (se 1 (by rfl) ⟨782630, by rfl⟩ : syracuseStep 1043507 = 1565261) B1565261
theorem B15199301 : Blo 432776 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B650315 : Blo 432776 650315 := bstep (se 1 (by rfl) ⟨487736, by rfl⟩ : syracuseStep 650315 = 975473) B975473
theorem B650327 : Blo 432776 650327 := bstep (se 1 (by rfl) ⟨487745, by rfl⟩ : syracuseStep 650327 = 975491) B975491
theorem B1485913 : Blo 432776 1485913 := bstep (se 2 (by rfl) ⟨557217, by rfl⟩ : syracuseStep 1485913 = 1114435) B1114435
theorem B1059929 : Blo 432776 1059929 := bstep (se 2 (by rfl) ⟨397473, by rfl⟩ : syracuseStep 1059929 = 794947) B794947
theorem B543883 : Blo 432776 543883 := bstep (se 1 (by rfl) ⟨407912, by rfl⟩ : syracuseStep 543883 = 815825) B815825
theorem B650393 : Blo 432776 650393 := bstep (se 2 (by rfl) ⟨243897, by rfl⟩ : syracuseStep 650393 = 487795) B487795
theorem B928921 : Blo 432776 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B1633459 : Blo 432776 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B1756363 : Blo 432776 1756363 := bstep (se 1 (by rfl) ⟨1317272, by rfl⟩ : syracuseStep 1756363 = 2634545) B2634545
theorem B822487 : Blo 432776 822487 := bstep (se 1 (by rfl) ⟨616865, by rfl⟩ : syracuseStep 822487 = 1233731) B1233731
theorem B978137 : Blo 432776 978137 := bstep (se 2 (by rfl) ⟨366801, by rfl⟩ : syracuseStep 978137 = 733603) B733603
theorem B650507 : Blo 432776 650507 := bstep (se 1 (by rfl) ⟨487880, by rfl⟩ : syracuseStep 650507 = 975761) B975761
theorem B650519 : Blo 432776 650519 := bstep (se 1 (by rfl) ⟨487889, by rfl⟩ : syracuseStep 650519 = 975779) B975779
theorem B5573933 : Blo 432776 5573933 := bstep (se 3 (by rfl) ⟨1045112, by rfl⟩ : syracuseStep 5573933 = 2090225) B2090225
theorem B978227 : Blo 432776 978227 := bstep (se 1 (by rfl) ⟨733670, by rfl⟩ : syracuseStep 978227 = 1467341) B1467341
theorem B1273153 : Blo 432776 1273153 := bstep (se 2 (by rfl) ⟨477432, by rfl⟩ : syracuseStep 1273153 = 954865) B954865
theorem B1469771 : Blo 432776 1469771 := bstep (se 1 (by rfl) ⟨1102328, by rfl⟩ : syracuseStep 1469771 = 2204657) B2204657
theorem B732503 : Blo 432776 732503 := bstep (se 1 (by rfl) ⟨549377, by rfl⟩ : syracuseStep 732503 = 1098755) B1098755
theorem B650585 : Blo 432776 650585 := bstep (se 2 (by rfl) ⟨243969, by rfl⟩ : syracuseStep 650585 = 487939) B487939
theorem B978263 : Blo 432776 978263 := bstep (se 1 (by rfl) ⟨733697, by rfl⟩ : syracuseStep 978263 = 1467395) B1467395
theorem B822707 : Blo 432776 822707 := bstep (se 1 (by rfl) ⟨617030, by rfl⟩ : syracuseStep 822707 = 1234061) B1234061
theorem B1101235 : Blo 432776 1101235 := bstep (se 1 (by rfl) ⟨825926, by rfl⟩ : syracuseStep 1101235 = 1651853) B1651853
theorem B470455 : Blo 432776 470455 := bstep (se 1 (by rfl) ⟨352841, by rfl⟩ : syracuseStep 470455 = 705683) B705683
theorem B650699 : Blo 432776 650699 := bstep (se 1 (by rfl) ⟨488024, by rfl⟩ : syracuseStep 650699 = 976049) B976049
theorem B650711 : Blo 432776 650711 := bstep (se 1 (by rfl) ⟨488033, by rfl⟩ : syracuseStep 650711 = 976067) B976067
theorem B732631 : Blo 432776 732631 := bstep (se 1 (by rfl) ⟨549473, by rfl⟩ : syracuseStep 732631 = 1098947) B1098947
theorem B1461725 : Blo 432776 1461725 := bstep (se 3 (by rfl) ⟨274073, by rfl⟩ : syracuseStep 1461725 = 548147) B548147
theorem B978443 : Blo 432776 978443 := bstep (se 1 (by rfl) ⟨733832, by rfl⟩ : syracuseStep 978443 = 1467665) B1467665
theorem B650777 : Blo 432776 650777 := bstep (se 2 (by rfl) ⟨244041, by rfl⟩ : syracuseStep 650777 = 488083) B488083
theorem B1855021 : Blo 432776 1855021 := bstep (se 3 (by rfl) ⟨347816, by rfl⟩ : syracuseStep 1855021 = 695633) B695633
theorem B486967 : Blo 432776 486967 := bstep (se 1 (by rfl) ⟨365225, by rfl⟩ : syracuseStep 486967 = 730451) B730451
theorem B978497 : Blo 432776 978497 := bstep (se 2 (by rfl) ⟨366936, by rfl⟩ : syracuseStep 978497 = 733873) B733873
theorem B1101377 : Blo 432776 1101377 := bstep (se 2 (by rfl) ⟨413016, by rfl⟩ : syracuseStep 1101377 = 826033) B826033
theorem B1470041 : Blo 432776 1470041 := bstep (se 2 (by rfl) ⟨551265, by rfl⟩ : syracuseStep 1470041 = 1102531) B1102531
theorem B650891 : Blo 432776 650891 := bstep (se 1 (by rfl) ⟨488168, by rfl⟩ : syracuseStep 650891 = 976337) B976337
theorem B822935 : Blo 432776 822935 := bstep (se 1 (by rfl) ⟨617201, by rfl⟩ : syracuseStep 822935 = 1234403) B1234403
theorem B650903 : Blo 432776 650903 := bstep (se 1 (by rfl) ⟨488177, by rfl⟩ : syracuseStep 650903 = 976355) B976355
theorem B618187 : Blo 432776 618187 := bstep (se 1 (by rfl) ⟨463640, by rfl⟩ : syracuseStep 618187 = 927281) B927281
theorem B650969 : Blo 432776 650969 := bstep (se 2 (by rfl) ⟨244113, by rfl⟩ : syracuseStep 650969 = 488227) B488227
theorem B487147 : Blo 432776 487147 := bstep (se 1 (by rfl) ⟨365360, by rfl⟩ : syracuseStep 487147 = 730721) B730721
theorem B978713 : Blo 432776 978713 := bstep (se 2 (by rfl) ⟨367017, by rfl⟩ : syracuseStep 978713 = 734035) B734035
theorem B651083 : Blo 432776 651083 := bstep (se 1 (by rfl) ⟨488312, by rfl⟩ : syracuseStep 651083 = 976625) B976625
theorem B487255 : Blo 432776 487255 := bstep (se 1 (by rfl) ⟨365441, by rfl⟩ : syracuseStep 487255 = 730883) B730883
theorem B1232729 : Blo 432776 1232729 := bstep (se 2 (by rfl) ⟨462273, by rfl⟩ : syracuseStep 1232729 = 924547) B924547
theorem B651095 : Blo 432776 651095 := bstep (se 1 (by rfl) ⟨488321, by rfl⟩ : syracuseStep 651095 = 976643) B976643
theorem B2346853 : Blo 432776 2346853 := bstep (se 4 (by rfl) ⟨220017, by rfl⟩ : syracuseStep 2346853 = 440035) B440035
theorem B978803 : Blo 432776 978803 := bstep (se 1 (by rfl) ⟨734102, by rfl⟩ : syracuseStep 978803 = 1468205) B1468205
theorem B1650563 : Blo 432776 1650563 := bstep (se 1 (by rfl) ⟨1237922, by rfl⟩ : syracuseStep 1650563 = 2475845) B2475845
theorem B1650577 : Blo 432776 1650577 := bstep (se 2 (by rfl) ⟨618966, by rfl⟩ : syracuseStep 1650577 = 1237933) B1237933
theorem B978839 : Blo 432776 978839 := bstep (se 1 (by rfl) ⟨734129, by rfl⟩ : syracuseStep 978839 = 1468259) B1468259
theorem B823193 : Blo 432776 823193 := bstep (se 2 (by rfl) ⟨308697, by rfl⟩ : syracuseStep 823193 = 617395) B617395
theorem B651161 : Blo 432776 651161 := bstep (se 2 (by rfl) ⟨244185, by rfl⟩ : syracuseStep 651161 = 488371) B488371
theorem B520139 : Blo 432776 520139 := bstep (se 1 (by rfl) ⟨390104, by rfl⟩ : syracuseStep 520139 = 780209) B780209
theorem B3706829 : Blo 432776 3706829 := bstep (se 3 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 3706829 = 1390061) B1390061
theorem B487435 : Blo 432776 487435 := bstep (se 1 (by rfl) ⟨365576, by rfl⟩ : syracuseStep 487435 = 731153) B731153
theorem B651275 : Blo 432776 651275 := bstep (se 1 (by rfl) ⟨488456, by rfl⟩ : syracuseStep 651275 = 976913) B976913
theorem B651287 : Blo 432776 651287 := bstep (se 1 (by rfl) ⟨488465, by rfl⟩ : syracuseStep 651287 = 976931) B976931
theorem B733259 : Blo 432776 733259 := bstep (se 1 (by rfl) ⟨549944, by rfl⟩ : syracuseStep 733259 = 1099889) B1099889
theorem B979019 : Blo 432776 979019 := bstep (se 1 (by rfl) ⟨734264, by rfl⟩ : syracuseStep 979019 = 1468529) B1468529
theorem B651353 : Blo 432776 651353 := bstep (se 2 (by rfl) ⟨244257, by rfl⟩ : syracuseStep 651353 = 488515) B488515
theorem B487543 : Blo 432776 487543 := bstep (se 1 (by rfl) ⟨365657, by rfl⟩ : syracuseStep 487543 = 731315) B731315
theorem B979073 : Blo 432776 979073 := bstep (se 2 (by rfl) ⟨367152, by rfl⟩ : syracuseStep 979073 = 734305) B734305
theorem B2355331 : Blo 432776 2355331 := bstep (se 1 (by rfl) ⟨1766498, by rfl⟩ : syracuseStep 2355331 = 3532997) B3532997
theorem B929971 : Blo 432776 929971 := bstep (se 1 (by rfl) ⟨697478, by rfl⟩ : syracuseStep 929971 = 1394957) B1394957
theorem B1650881 : Blo 432776 1650881 := bstep (se 2 (by rfl) ⟨619080, by rfl⟩ : syracuseStep 1650881 = 1238161) B1238161
theorem B651467 : Blo 432776 651467 := bstep (se 1 (by rfl) ⟨488600, by rfl⟩ : syracuseStep 651467 = 977201) B977201
theorem B733387 : Blo 432776 733387 := bstep (se 1 (by rfl) ⟨550040, by rfl⟩ : syracuseStep 733387 = 1100081) B1100081
theorem B4944077 : Blo 432776 4944077 := bstep (se 3 (by rfl) ⟨927014, by rfl⟩ : syracuseStep 4944077 = 1854029) B1854029
theorem B651479 : Blo 432776 651479 := bstep (se 1 (by rfl) ⟨488609, by rfl⟩ : syracuseStep 651479 = 977219) B977219
theorem B1470743 : Blo 432776 1470743 := bstep (se 1 (by rfl) ⟨1103057, by rfl⟩ : syracuseStep 1470743 = 2206115) B2206115
theorem B651545 : Blo 432776 651545 := bstep (se 2 (by rfl) ⟨244329, by rfl⟩ : syracuseStep 651545 = 488659) B488659
theorem B487723 : Blo 432776 487723 := bstep (se 1 (by rfl) ⟨365792, by rfl⟩ : syracuseStep 487723 = 731585) B731585
theorem B823603 : Blo 432776 823603 := bstep (se 1 (by rfl) ⟨617702, by rfl⟩ : syracuseStep 823603 = 1235405) B1235405
theorem B733529 : Blo 432776 733529 := bstep (se 2 (by rfl) ⟨275073, by rfl⟩ : syracuseStep 733529 = 550147) B550147
theorem B979289 : Blo 432776 979289 := bstep (se 2 (by rfl) ⟨367233, by rfl⟩ : syracuseStep 979289 = 734467) B734467
theorem B651659 : Blo 432776 651659 := bstep (se 1 (by rfl) ⟨488744, by rfl⟩ : syracuseStep 651659 = 977489) B977489
theorem B487831 : Blo 432776 487831 := bstep (se 1 (by rfl) ⟨365873, by rfl⟩ : syracuseStep 487831 = 731747) B731747
theorem B651671 : Blo 432776 651671 := bstep (se 1 (by rfl) ⟨488753, by rfl⟩ : syracuseStep 651671 = 977507) B977507
theorem B987545 : Blo 432776 987545 := bstep (se 2 (by rfl) ⟨370329, by rfl⟩ : syracuseStep 987545 = 740659) B740659
theorem B2199959 : Blo 432776 2199959 := bstep (se 1 (by rfl) ⟨1649969, by rfl⟩ : syracuseStep 2199959 = 3299939) B3299939
theorem B979379 : Blo 432776 979379 := bstep (se 1 (by rfl) ⟨734534, by rfl⟩ : syracuseStep 979379 = 1469069) B1469069
theorem B979415 : Blo 432776 979415 := bstep (se 1 (by rfl) ⟨734561, by rfl⟩ : syracuseStep 979415 = 1469123) B1469123
theorem B651737 : Blo 432776 651737 := bstep (se 2 (by rfl) ⟨244401, by rfl⟩ : syracuseStep 651737 = 488803) B488803
theorem B733657 : Blo 432776 733657 := bstep (se 2 (by rfl) ⟨275121, by rfl⟩ : syracuseStep 733657 = 550243) B550243
theorem B2470445 : Blo 432776 2470445 := bstep (se 3 (by rfl) ⟨463208, by rfl⟩ : syracuseStep 2470445 = 926417) B926417
theorem B1462859 : Blo 432776 1462859 := bstep (se 1 (by rfl) ⟨1097144, by rfl⟩ : syracuseStep 1462859 = 2194289) B2194289
theorem B488011 : Blo 432776 488011 := bstep (se 1 (by rfl) ⟨366008, by rfl⟩ : syracuseStep 488011 = 732017) B732017
theorem B651851 : Blo 432776 651851 := bstep (se 1 (by rfl) ⟨488888, by rfl⟩ : syracuseStep 651851 = 977777) B977777
theorem B651863 : Blo 432776 651863 := bstep (se 1 (by rfl) ⟨488897, by rfl⟩ : syracuseStep 651863 = 977795) B977795
theorem B889483 : Blo 432776 889483 := bstep (se 1 (by rfl) ⟨667112, by rfl⟩ : syracuseStep 889483 = 1334225) B1334225
theorem B979595 : Blo 432776 979595 := bstep (se 1 (by rfl) ⟨734696, by rfl⟩ : syracuseStep 979595 = 1469393) B1469393
theorem B1233559 : Blo 432776 1233559 := bstep (se 1 (by rfl) ⟨925169, by rfl⟩ : syracuseStep 1233559 = 1850339) B1850339
theorem B651929 : Blo 432776 651929 := bstep (se 2 (by rfl) ⟨244473, by rfl⟩ : syracuseStep 651929 = 488947) B488947
theorem B2347699 : Blo 432776 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B488119 : Blo 432776 488119 := bstep (se 1 (by rfl) ⟨366089, by rfl⟩ : syracuseStep 488119 = 732179) B732179
theorem B979649 : Blo 432776 979649 := bstep (se 2 (by rfl) ⟨367368, by rfl⟩ : syracuseStep 979649 = 734737) B734737
theorem B463627 : Blo 432776 463627 := bstep (se 1 (by rfl) ⟨347720, by rfl⟩ : syracuseStep 463627 = 695441) B695441
theorem B652043 : Blo 432776 652043 := bstep (se 1 (by rfl) ⟨489032, by rfl⟩ : syracuseStep 652043 = 978065) B978065
theorem B3306257 : Blo 432776 3306257 := bstep (se 2 (by rfl) ⟨1239846, by rfl⟩ : syracuseStep 3306257 = 2479693) B2479693
theorem B1643287 : Blo 432776 1643287 := bstep (se 1 (by rfl) ⟨1232465, by rfl⟩ : syracuseStep 1643287 = 2464931) B2464931
theorem B652055 : Blo 432776 652055 := bstep (se 1 (by rfl) ⟨489041, by rfl⟩ : syracuseStep 652055 = 978083) B978083
theorem B824089 : Blo 432776 824089 := bstep (se 2 (by rfl) ⟨309033, by rfl⟩ : syracuseStep 824089 = 618067) B618067
theorem B1487639 : Blo 432776 1487639 := bstep (se 1 (by rfl) ⟨1115729, by rfl⟩ : syracuseStep 1487639 = 2231459) B2231459
theorem B1102643 : Blo 432776 1102643 := bstep (se 1 (by rfl) ⟨826982, by rfl⟩ : syracuseStep 1102643 = 1653965) B1653965
theorem B1463129 : Blo 432776 1463129 := bstep (se 2 (by rfl) ⟨548673, by rfl⟩ : syracuseStep 1463129 = 1097347) B1097347
theorem B652121 : Blo 432776 652121 := bstep (se 2 (by rfl) ⟨244545, by rfl⟩ : syracuseStep 652121 = 489091) B489091
theorem B881497 : Blo 432776 881497 := bstep (se 2 (by rfl) ⟨330561, by rfl⟩ : syracuseStep 881497 = 661123) B661123
theorem B1651549 : Blo 432776 1651549 := bstep (se 3 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 1651549 = 619331) B619331
theorem B488299 : Blo 432776 488299 := bstep (se 1 (by rfl) ⟨366224, by rfl⟩ : syracuseStep 488299 = 732449) B732449
theorem B619417 : Blo 432776 619417 := bstep (se 2 (by rfl) ⟨232281, by rfl⟩ : syracuseStep 619417 = 464563) B464563
theorem B979865 : Blo 432776 979865 := bstep (se 2 (by rfl) ⟨367449, by rfl⟩ : syracuseStep 979865 = 734899) B734899
theorem B652235 : Blo 432776 652235 := bstep (se 1 (by rfl) ⟨489176, by rfl⟩ : syracuseStep 652235 = 978353) B978353
theorem B488407 : Blo 432776 488407 := bstep (se 1 (by rfl) ⟨366305, by rfl⟩ : syracuseStep 488407 = 732611) B732611
theorem B652247 : Blo 432776 652247 := bstep (se 1 (by rfl) ⟨489185, by rfl⟩ : syracuseStep 652247 = 978371) B978371
theorem B2192345 : Blo 432776 2192345 := bstep (se 2 (by rfl) ⟨822129, by rfl⟩ : syracuseStep 2192345 = 1644259) B1644259
theorem B979955 : Blo 432776 979955 := bstep (se 1 (by rfl) ⟨734966, by rfl⟩ : syracuseStep 979955 = 1469933) B1469933
theorem B734231 : Blo 432776 734231 := bstep (se 1 (by rfl) ⟨550673, by rfl⟩ : syracuseStep 734231 = 1101347) B1101347
theorem B979991 : Blo 432776 979991 := bstep (se 1 (by rfl) ⟨734993, by rfl⟩ : syracuseStep 979991 = 1469987) B1469987
theorem B652313 : Blo 432776 652313 := bstep (se 2 (by rfl) ⟨244617, by rfl⟩ : syracuseStep 652313 = 489235) B489235
theorem B988247 : Blo 432776 988247 := bstep (se 1 (by rfl) ⟨741185, by rfl⟩ : syracuseStep 988247 = 1482371) B1482371
theorem B1487965 : Blo 432776 1487965 := bstep (se 3 (by rfl) ⟨278993, by rfl⟩ : syracuseStep 1487965 = 557987) B557987
theorem B488587 : Blo 432776 488587 := bstep (se 1 (by rfl) ⟨366440, by rfl⟩ : syracuseStep 488587 = 732881) B732881
theorem B652427 : Blo 432776 652427 := bstep (se 1 (by rfl) ⟨489320, by rfl⟩ : syracuseStep 652427 = 978641) B978641
theorem B652439 : Blo 432776 652439 := bstep (se 1 (by rfl) ⟨489329, by rfl⟩ : syracuseStep 652439 = 978659) B978659
theorem B734359 : Blo 432776 734359 := bstep (se 1 (by rfl) ⟨550769, by rfl⟩ : syracuseStep 734359 = 1101539) B1101539
theorem B1324183 : Blo 432776 1324183 := bstep (se 1 (by rfl) ⟨993137, by rfl⟩ : syracuseStep 1324183 = 1986275) B1986275
theorem B3298481 : Blo 432776 3298481 := bstep (se 2 (by rfl) ⟨1236930, by rfl⟩ : syracuseStep 3298481 = 2473861) B2473861
theorem B51573941 : Blo 432776 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B980171 : Blo 432776 980171 := bstep (se 1 (by rfl) ⟨735128, by rfl⟩ : syracuseStep 980171 = 1470257) B1470257
theorem B1881305 : Blo 432776 1881305 := bstep (se 2 (by rfl) ⟨705489, by rfl⟩ : syracuseStep 1881305 = 1410979) B1410979
theorem B652505 : Blo 432776 652505 := bstep (se 2 (by rfl) ⟨244689, by rfl⟩ : syracuseStep 652505 = 489379) B489379
theorem B488695 : Blo 432776 488695 := bstep (se 1 (by rfl) ⟨366521, by rfl⟩ : syracuseStep 488695 = 733043) B733043
theorem B980225 : Blo 432776 980225 := bstep (se 2 (by rfl) ⟨367584, by rfl⟩ : syracuseStep 980225 = 735169) B735169
theorem B496919 : Blo 432776 496919 := bstep (se 1 (by rfl) ⟨372689, by rfl⟩ : syracuseStep 496919 = 745379) B745379
theorem B824651 : Blo 432776 824651 := bstep (se 1 (by rfl) ⟨618488, by rfl⟩ : syracuseStep 824651 = 1236977) B1236977
theorem B652619 : Blo 432776 652619 := bstep (se 1 (by rfl) ⟨489464, by rfl⟩ : syracuseStep 652619 = 978929) B978929
theorem B1045835 : Blo 432776 1045835 := bstep (se 1 (by rfl) ⟨784376, by rfl⟩ : syracuseStep 1045835 = 1568753) B1568753
theorem B652631 : Blo 432776 652631 := bstep (se 1 (by rfl) ⟨489473, by rfl⟩ : syracuseStep 652631 = 978947) B978947
theorem B2479511 : Blo 432776 2479511 := bstep (se 1 (by rfl) ⟨1859633, by rfl⟩ : syracuseStep 2479511 = 3719267) B3719267
theorem B652697 : Blo 432776 652697 := bstep (se 2 (by rfl) ⟨244761, by rfl⟩ : syracuseStep 652697 = 489523) B489523
theorem B488875 : Blo 432776 488875 := bstep (se 1 (by rfl) ⟨366656, by rfl⟩ : syracuseStep 488875 = 733313) B733313
theorem B1234379 : Blo 432776 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B521687 : Blo 432776 521687 := bstep (se 1 (by rfl) ⟨391265, by rfl⟩ : syracuseStep 521687 = 782531) B782531
theorem B980441 : Blo 432776 980441 := bstep (se 2 (by rfl) ⟨367665, by rfl⟩ : syracuseStep 980441 = 735331) B735331
theorem B824833 : Blo 432776 824833 := bstep (se 2 (by rfl) ⟨309312, by rfl⟩ : syracuseStep 824833 = 618625) B618625
theorem B1848835 : Blo 432776 1848835 := bstep (se 1 (by rfl) ⟨1386626, by rfl⟩ : syracuseStep 1848835 = 2773253) B2773253
theorem B652811 : Blo 432776 652811 := bstep (se 1 (by rfl) ⟨489608, by rfl⟩ : syracuseStep 652811 = 979217) B979217
theorem B1463831 : Blo 432776 1463831 := bstep (se 1 (by rfl) ⟨1097873, by rfl⟩ : syracuseStep 1463831 = 2195747) B2195747
theorem B587287 : Blo 432776 587287 := bstep (se 1 (by rfl) ⟨440465, by rfl⟩ : syracuseStep 587287 = 880931) B880931
theorem B488983 : Blo 432776 488983 := bstep (se 1 (by rfl) ⟨366737, by rfl⟩ : syracuseStep 488983 = 733475) B733475
theorem B652823 : Blo 432776 652823 := bstep (se 1 (by rfl) ⟨489617, by rfl⟩ : syracuseStep 652823 = 979235) B979235
theorem B1644077 : Blo 432776 1644077 := bstep (se 3 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 1644077 = 616529) B616529
theorem B652889 : Blo 432776 652889 := bstep (se 2 (by rfl) ⟨244833, by rfl⟩ : syracuseStep 652889 = 489667) B489667
theorem B3298967 : Blo 432776 3298967 := bstep (se 1 (by rfl) ⟨2474225, by rfl⟩ : syracuseStep 3298967 = 4948451) B4948451
theorem B2791091 : Blo 432776 2791091 := bstep (se 1 (by rfl) ⟨2093318, by rfl⟩ : syracuseStep 2791091 = 4186637) B4186637
theorem B489163 : Blo 432776 489163 := bstep (se 1 (by rfl) ⟨366872, by rfl⟩ : syracuseStep 489163 = 733745) B733745
theorem B653003 : Blo 432776 653003 := bstep (se 1 (by rfl) ⟨489752, by rfl⟩ : syracuseStep 653003 = 979505) B979505
theorem B653015 : Blo 432776 653015 := bstep (se 1 (by rfl) ⟨489761, by rfl⟩ : syracuseStep 653015 = 979523) B979523
theorem B734987 : Blo 432776 734987 := bstep (se 1 (by rfl) ⟨551240, by rfl⟩ : syracuseStep 734987 = 1102481) B1102481
theorem B620311 : Blo 432776 620311 := bstep (se 1 (by rfl) ⟨465233, by rfl⟩ : syracuseStep 620311 = 930467) B930467
theorem B653081 : Blo 432776 653081 := bstep (se 2 (by rfl) ⟨244905, by rfl⟩ : syracuseStep 653081 = 489811) B489811
theorem B3610403 : Blo 432776 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B489271 : Blo 432776 489271 := bstep (se 1 (by rfl) ⟨366953, by rfl⟩ : syracuseStep 489271 = 733907) B733907
theorem B784217 : Blo 432776 784217 := bstep (se 2 (by rfl) ⟨294081, by rfl⟩ : syracuseStep 784217 = 588163) B588163
theorem B989057 : Blo 432776 989057 := bstep (se 2 (by rfl) ⟨370896, by rfl⟩ : syracuseStep 989057 = 741793) B741793
theorem B653195 : Blo 432776 653195 := bstep (se 1 (by rfl) ⟨489896, by rfl⟩ : syracuseStep 653195 = 979793) B979793
theorem B735115 : Blo 432776 735115 := bstep (se 1 (by rfl) ⟨551336, by rfl⟩ : syracuseStep 735115 = 1102673) B1102673
theorem B1857431 : Blo 432776 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B653207 : Blo 432776 653207 := bstep (se 1 (by rfl) ⟨489905, by rfl⟩ : syracuseStep 653207 = 979811) B979811
theorem B653273 : Blo 432776 653273 := bstep (se 2 (by rfl) ⟨244977, by rfl⟩ : syracuseStep 653273 = 489955) B489955
theorem B489451 : Blo 432776 489451 := bstep (se 1 (by rfl) ⟨367088, by rfl⟩ : syracuseStep 489451 = 734177) B734177
theorem B3799057 : Blo 432776 3799057 := bstep (se 2 (by rfl) ⟨1424646, by rfl⟩ : syracuseStep 3799057 = 2849293) B2849293
theorem B735257 : Blo 432776 735257 := bstep (se 2 (by rfl) ⟨275721, by rfl⟩ : syracuseStep 735257 = 551443) B551443
theorem B1464371 : Blo 432776 1464371 := bstep (se 1 (by rfl) ⟨1098278, by rfl⟩ : syracuseStep 1464371 = 2196557) B2196557
theorem B653387 : Blo 432776 653387 := bstep (se 1 (by rfl) ⟨490040, by rfl⟩ : syracuseStep 653387 = 980081) B980081
theorem B489559 : Blo 432776 489559 := bstep (se 1 (by rfl) ⟨367169, by rfl⟩ : syracuseStep 489559 = 734339) B734339
theorem B653399 : Blo 432776 653399 := bstep (se 1 (by rfl) ⟨490049, by rfl⟩ : syracuseStep 653399 = 980099) B980099
theorem B1652825 : Blo 432776 1652825 := bstep (se 2 (by rfl) ⟨619809, by rfl⟩ : syracuseStep 1652825 = 1239619) B1239619
theorem B1177751 : Blo 432776 1177751 := bstep (se 1 (by rfl) ⟨883313, by rfl⟩ : syracuseStep 1177751 = 1766627) B1766627
theorem B653465 : Blo 432776 653465 := bstep (se 2 (by rfl) ⟨245049, by rfl⟩ : syracuseStep 653465 = 490099) B490099
theorem B12507317 : Blo 432776 12507317 := bstep (se 5 (by rfl) ⟨586280, by rfl⟩ : syracuseStep 12507317 = 1172561) B1172561
theorem B825547 : Blo 432776 825547 := bstep (se 1 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 825547 = 1238321) B1238321
theorem B694487 : Blo 432776 694487 := bstep (se 1 (by rfl) ⟨520865, by rfl⟩ : syracuseStep 694487 = 1041731) B1041731
theorem B440587 : Blo 432776 440587 := bstep (se 1 (by rfl) ⟨330440, by rfl⟩ : syracuseStep 440587 = 660881) B660881
theorem B489739 : Blo 432776 489739 := bstep (se 1 (by rfl) ⟨367304, by rfl⟩ : syracuseStep 489739 = 734609) B734609
theorem B653579 : Blo 432776 653579 := bstep (se 1 (by rfl) ⟨490184, by rfl⟩ : syracuseStep 653579 = 980369) B980369
theorem B1562897 : Blo 432776 1562897 := bstep (se 2 (by rfl) ⟨586086, by rfl⟩ : syracuseStep 1562897 = 1172173) B1172173
theorem B825623 : Blo 432776 825623 := bstep (se 1 (by rfl) ⟨619217, by rfl⟩ : syracuseStep 825623 = 1238435) B1238435
theorem B588055 : Blo 432776 588055 := bstep (se 1 (by rfl) ⟨441041, by rfl⟩ : syracuseStep 588055 = 882083) B882083
theorem B653591 : Blo 432776 653591 := bstep (se 1 (by rfl) ⟨490193, by rfl⟩ : syracuseStep 653591 = 980387) B980387
theorem B2283821 : Blo 432776 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B1096001 : Blo 432776 1096001 := bstep (se 2 (by rfl) ⟨411000, by rfl⟩ : syracuseStep 1096001 = 822001) B822001
theorem B1464641 : Blo 432776 1464641 := bstep (se 2 (by rfl) ⟨549240, by rfl⟩ : syracuseStep 1464641 = 1098481) B1098481
theorem B653657 : Blo 432776 653657 := bstep (se 2 (by rfl) ⟨245121, by rfl⟩ : syracuseStep 653657 = 490243) B490243
theorem B465259 : Blo 432776 465259 := bstep (se 1 (by rfl) ⟨348944, by rfl⟩ : syracuseStep 465259 = 697889) B697889
theorem B489847 : Blo 432776 489847 := bstep (se 1 (by rfl) ⟨367385, by rfl⟩ : syracuseStep 489847 = 734771) B734771
theorem B2980313 : Blo 432776 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B3521029 : Blo 432776 3521029 := bstep (se 4 (by rfl) ⟨330096, by rfl⟩ : syracuseStep 3521029 = 660193) B660193
theorem B5552657 : Blo 432776 5552657 := bstep (se 2 (by rfl) ⟨2082246, by rfl⟩ : syracuseStep 5552657 = 4164493) B4164493
theorem B490027 : Blo 432776 490027 := bstep (se 1 (by rfl) ⟨367520, by rfl⟩ : syracuseStep 490027 = 735041) B735041
theorem B2193965 : Blo 432776 2193965 := bstep (se 3 (by rfl) ⟨411368, by rfl⟩ : syracuseStep 2193965 = 822737) B822737
theorem B1407577 : Blo 432776 1407577 := bstep (se 2 (by rfl) ⟨527841, by rfl⟩ : syracuseStep 1407577 = 1055683) B1055683
theorem B432779 : Blo 432776 432779 := bstep (se 1 (by rfl) ⟨324584, by rfl⟩ : syracuseStep 432779 = 649169) B649169
theorem B432791 : Blo 432776 432791 := bstep (se 1 (by rfl) ⟨324593, by rfl⟩ : syracuseStep 432791 = 649187) B649187
theorem B5569175 : Blo 432776 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B490135 : Blo 432776 490135 := bstep (se 1 (by rfl) ⟨367601, by rfl⟩ : syracuseStep 490135 = 735203) B735203
theorem B432811 : Blo 432776 432811 := bstep (se 1 (by rfl) ⟨324608, by rfl⟩ : syracuseStep 432811 = 649217) B649217
theorem B432823 : Blo 432776 432823 := bstep (se 1 (by rfl) ⟨324617, by rfl⟩ : syracuseStep 432823 = 649235) B649235
theorem B432843 : Blo 432776 432843 := bstep (se 1 (by rfl) ⟨324632, by rfl⟩ : syracuseStep 432843 = 649265) B649265
theorem B522955 : Blo 432776 522955 := bstep (se 1 (by rfl) ⟨392216, by rfl⟩ : syracuseStep 522955 = 784433) B784433
theorem B6675149 : Blo 432776 6675149 := bstep (se 3 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 6675149 = 2503181) B2503181
theorem B432855 : Blo 432776 432855 := bstep (se 1 (by rfl) ⟨324641, by rfl⟩ : syracuseStep 432855 = 649283) B649283
theorem B432875 : Blo 432776 432875 := bstep (se 1 (by rfl) ⟨324656, by rfl⟩ : syracuseStep 432875 = 649313) B649313
theorem B432887 : Blo 432776 432887 := bstep (se 1 (by rfl) ⟨324665, by rfl⟩ : syracuseStep 432887 = 649331) B649331
theorem B432907 : Blo 432776 432907 := bstep (se 1 (by rfl) ⟨324680, by rfl⟩ : syracuseStep 432907 = 649361) B649361
theorem B695051 : Blo 432776 695051 := bstep (se 1 (by rfl) ⟨521288, by rfl⟩ : syracuseStep 695051 = 1042577) B1042577
theorem B432919 : Blo 432776 432919 := bstep (se 1 (by rfl) ⟨324689, by rfl⟩ : syracuseStep 432919 = 649379) B649379
theorem B793367 : Blo 432776 793367 := bstep (se 1 (by rfl) ⟨595025, by rfl⟩ : syracuseStep 793367 = 1190051) B1190051
theorem B432939 : Blo 432776 432939 := bstep (se 1 (by rfl) ⟨324704, by rfl⟩ : syracuseStep 432939 = 649409) B649409
theorem B1170227 : Blo 432776 1170227 := bstep (se 1 (by rfl) ⟨877670, by rfl⟩ : syracuseStep 1170227 = 1755341) B1755341
theorem B432951 : Blo 432776 432951 := bstep (se 1 (by rfl) ⟨324713, by rfl⟩ : syracuseStep 432951 = 649427) B649427
theorem B432971 : Blo 432776 432971 := bstep (se 1 (by rfl) ⟨324728, by rfl⟩ : syracuseStep 432971 = 649457) B649457
theorem B432983 : Blo 432776 432983 := bstep (se 1 (by rfl) ⟨324737, by rfl⟩ : syracuseStep 432983 = 649475) B649475
theorem B1096537 : Blo 432776 1096537 := bstep (se 2 (by rfl) ⟨411201, by rfl⟩ : syracuseStep 1096537 = 822403) B822403
theorem B1465181 : Blo 432776 1465181 := bstep (se 3 (by rfl) ⟨274721, by rfl⟩ : syracuseStep 1465181 = 549443) B549443
theorem B433003 : Blo 432776 433003 := bstep (se 1 (by rfl) ⟨324752, by rfl⟩ : syracuseStep 433003 = 649505) B649505
theorem B433015 : Blo 432776 433015 := bstep (se 1 (by rfl) ⟨324761, by rfl⟩ : syracuseStep 433015 = 649523) B649523
theorem B433035 : Blo 432776 433035 := bstep (se 1 (by rfl) ⟨324776, by rfl⟩ : syracuseStep 433035 = 649553) B649553
theorem B433047 : Blo 432776 433047 := bstep (se 1 (by rfl) ⟨324785, by rfl⟩ : syracuseStep 433047 = 649571) B649571
theorem B433067 : Blo 432776 433067 := bstep (se 1 (by rfl) ⟨324800, by rfl⟩ : syracuseStep 433067 = 649601) B649601
theorem B826291 : Blo 432776 826291 := bstep (se 1 (by rfl) ⟨619718, by rfl⟩ : syracuseStep 826291 = 1239437) B1239437
theorem B433079 : Blo 432776 433079 := bstep (se 1 (by rfl) ⟨324809, by rfl⟩ : syracuseStep 433079 = 649619) B649619
theorem B1645505 : Blo 432776 1645505 := bstep (se 2 (by rfl) ⟨617064, by rfl⟩ : syracuseStep 1645505 = 1234129) B1234129
theorem B433099 : Blo 432776 433099 := bstep (se 1 (by rfl) ⟨324824, by rfl⟩ : syracuseStep 433099 = 649649) B649649
theorem B433111 : Blo 432776 433111 := bstep (se 1 (by rfl) ⟨324833, by rfl⟩ : syracuseStep 433111 = 649667) B649667
theorem B941015 : Blo 432776 941015 := bstep (se 1 (by rfl) ⟨705761, by rfl⟩ : syracuseStep 941015 = 1411523) B1411523
theorem B433131 : Blo 432776 433131 := bstep (se 1 (by rfl) ⟨324848, by rfl⟩ : syracuseStep 433131 = 649697) B649697
theorem B433143 : Blo 432776 433143 := bstep (se 1 (by rfl) ⟨324857, by rfl⟩ : syracuseStep 433143 = 649715) B649715
theorem B973835 : Blo 432776 973835 := bstep (se 1 (by rfl) ⟨730376, by rfl⟩ : syracuseStep 973835 = 1460753) B1460753
theorem B433163 : Blo 432776 433163 := bstep (se 1 (by rfl) ⟨324872, by rfl⟩ : syracuseStep 433163 = 649745) B649745
theorem B433175 : Blo 432776 433175 := bstep (se 1 (by rfl) ⟨324881, by rfl⟩ : syracuseStep 433175 = 649763) B649763
theorem B10017827 : Blo 432776 10017827 := bstep (se 1 (by rfl) ⟨7513370, by rfl⟩ : syracuseStep 10017827 = 15026741) B15026741
theorem B10026019 : Blo 432776 10026019 := bstep (se 1 (by rfl) ⟨7519514, by rfl⟩ : syracuseStep 10026019 = 15039029) B15039029
theorem B433195 : Blo 432776 433195 := bstep (se 1 (by rfl) ⟨324896, by rfl⟩ : syracuseStep 433195 = 649793) B649793
theorem B433207 : Blo 432776 433207 := bstep (se 1 (by rfl) ⟨324905, by rfl⟩ : syracuseStep 433207 = 649811) B649811
theorem B973889 : Blo 432776 973889 := bstep (se 2 (by rfl) ⟨365208, by rfl⟩ : syracuseStep 973889 = 730417) B730417
theorem B2964545 : Blo 432776 2964545 := bstep (se 2 (by rfl) ⟨1111704, by rfl⟩ : syracuseStep 2964545 = 2223409) B2223409
theorem B433227 : Blo 432776 433227 := bstep (se 1 (by rfl) ⟨324920, by rfl⟩ : syracuseStep 433227 = 649841) B649841
theorem B433239 : Blo 432776 433239 := bstep (se 1 (by rfl) ⟨324929, by rfl⟩ : syracuseStep 433239 = 649859) B649859
theorem B433259 : Blo 432776 433259 := bstep (se 1 (by rfl) ⟨324944, by rfl⟩ : syracuseStep 433259 = 649889) B649889
theorem B433271 : Blo 432776 433271 := bstep (se 1 (by rfl) ⟨324953, by rfl⟩ : syracuseStep 433271 = 649907) B649907
theorem B433291 : Blo 432776 433291 := bstep (se 1 (by rfl) ⟨324968, by rfl⟩ : syracuseStep 433291 = 649937) B649937
theorem B433303 : Blo 432776 433303 := bstep (se 1 (by rfl) ⟨324977, by rfl⟩ : syracuseStep 433303 = 649955) B649955
theorem B826519 : Blo 432776 826519 := bstep (se 1 (by rfl) ⟨619889, by rfl⟩ : syracuseStep 826519 = 1239779) B1239779
theorem B433323 : Blo 432776 433323 := bstep (se 1 (by rfl) ⟨324992, by rfl⟩ : syracuseStep 433323 = 649985) B649985
theorem B433335 : Blo 432776 433335 := bstep (se 1 (by rfl) ⟨325001, by rfl⟩ : syracuseStep 433335 = 650003) B650003
theorem B433355 : Blo 432776 433355 := bstep (se 1 (by rfl) ⟨325016, by rfl⟩ : syracuseStep 433355 = 650033) B650033
theorem B433367 : Blo 432776 433367 := bstep (se 1 (by rfl) ⟨325025, by rfl⟩ : syracuseStep 433367 = 650051) B650051
theorem B433387 : Blo 432776 433387 := bstep (se 1 (by rfl) ⟨325040, by rfl⟩ : syracuseStep 433387 = 650081) B650081
theorem B433399 : Blo 432776 433399 := bstep (se 1 (by rfl) ⟨325049, by rfl⟩ : syracuseStep 433399 = 650099) B650099
theorem B826625 : Blo 432776 826625 := bstep (se 2 (by rfl) ⟨309984, by rfl⟩ : syracuseStep 826625 = 619969) B619969
theorem B433419 : Blo 432776 433419 := bstep (se 1 (by rfl) ⟨325064, by rfl⟩ : syracuseStep 433419 = 650129) B650129
theorem B2481425 : Blo 432776 2481425 := bstep (se 2 (by rfl) ⟨930534, by rfl⟩ : syracuseStep 2481425 = 1861069) B1861069
theorem B1850647 : Blo 432776 1850647 := bstep (se 1 (by rfl) ⟨1387985, by rfl⟩ : syracuseStep 1850647 = 2775971) B2775971
theorem B433431 : Blo 432776 433431 := bstep (se 1 (by rfl) ⟨325073, by rfl⟩ : syracuseStep 433431 = 650147) B650147
theorem B974105 : Blo 432776 974105 := bstep (se 2 (by rfl) ⟨365289, by rfl⟩ : syracuseStep 974105 = 730579) B730579
theorem B433451 : Blo 432776 433451 := bstep (se 1 (by rfl) ⟨325088, by rfl⟩ : syracuseStep 433451 = 650177) B650177
theorem B433463 : Blo 432776 433463 := bstep (se 1 (by rfl) ⟨325097, by rfl⟩ : syracuseStep 433463 = 650195) B650195
theorem B433483 : Blo 432776 433483 := bstep (se 1 (by rfl) ⟨325112, by rfl⟩ : syracuseStep 433483 = 650225) B650225
theorem B433495 : Blo 432776 433495 := bstep (se 1 (by rfl) ⟨325121, by rfl⟩ : syracuseStep 433495 = 650243) B650243
theorem B433515 : Blo 432776 433515 := bstep (se 1 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 433515 = 650273) B650273
theorem B974195 : Blo 432776 974195 := bstep (se 1 (by rfl) ⟨730646, by rfl⟩ : syracuseStep 974195 = 1461293) B1461293
theorem B6274421 : Blo 432776 6274421 := bstep (se 5 (by rfl) ⟨294113, by rfl⟩ : syracuseStep 6274421 = 588227) B588227
theorem B433527 : Blo 432776 433527 := bstep (se 1 (by rfl) ⟨325145, by rfl⟩ : syracuseStep 433527 = 650291) B650291
theorem B925067 : Blo 432776 925067 := bstep (se 1 (by rfl) ⟨693800, by rfl⟩ : syracuseStep 925067 = 1387601) B1387601
theorem B433547 : Blo 432776 433547 := bstep (se 1 (by rfl) ⟨325160, by rfl⟩ : syracuseStep 433547 = 650321) B650321
theorem B2006417 : Blo 432776 2006417 := bstep (se 2 (by rfl) ⟨752406, by rfl⟩ : syracuseStep 2006417 = 1504813) B1504813
theorem B974231 : Blo 432776 974231 := bstep (se 1 (by rfl) ⟨730673, by rfl⟩ : syracuseStep 974231 = 1461347) B1461347
theorem B433559 : Blo 432776 433559 := bstep (se 1 (by rfl) ⟨325169, by rfl⟩ : syracuseStep 433559 = 650339) B650339
theorem B941465 : Blo 432776 941465 := bstep (se 2 (by rfl) ⟨353049, by rfl⟩ : syracuseStep 941465 = 706099) B706099
theorem B826777 : Blo 432776 826777 := bstep (se 2 (by rfl) ⟨310041, by rfl⟩ : syracuseStep 826777 = 620083) B620083
theorem B433579 : Blo 432776 433579 := bstep (se 1 (by rfl) ⟨325184, by rfl⟩ : syracuseStep 433579 = 650369) B650369
theorem B433591 : Blo 432776 433591 := bstep (se 1 (by rfl) ⟨325193, by rfl⟩ : syracuseStep 433591 = 650387) B650387
theorem B835009 : Blo 432776 835009 := bstep (se 2 (by rfl) ⟨313128, by rfl⟩ : syracuseStep 835009 = 626257) B626257
theorem B548299 : Blo 432776 548299 := bstep (se 1 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 548299 = 822449) B822449
theorem B433611 : Blo 432776 433611 := bstep (se 1 (by rfl) ⟨325208, by rfl⟩ : syracuseStep 433611 = 650417) B650417
theorem B433623 : Blo 432776 433623 := bstep (se 1 (by rfl) ⟨325217, by rfl⟩ : syracuseStep 433623 = 650435) B650435
theorem B433643 : Blo 432776 433643 := bstep (se 1 (by rfl) ⟨325232, by rfl⟩ : syracuseStep 433643 = 650465) B650465
theorem B433655 : Blo 432776 433655 := bstep (se 1 (by rfl) ⟨325241, by rfl⟩ : syracuseStep 433655 = 650483) B650483
theorem B433675 : Blo 432776 433675 := bstep (se 1 (by rfl) ⟨325256, by rfl⟩ : syracuseStep 433675 = 650513) B650513
theorem B433687 : Blo 432776 433687 := bstep (se 1 (by rfl) ⟨325265, by rfl⟩ : syracuseStep 433687 = 650531) B650531
theorem B433707 : Blo 432776 433707 := bstep (se 1 (by rfl) ⟨325280, by rfl⟩ : syracuseStep 433707 = 650561) B650561
theorem B1564211 : Blo 432776 1564211 := bstep (se 1 (by rfl) ⟨1173158, by rfl⟩ : syracuseStep 1564211 = 2346317) B2346317
theorem B433719 : Blo 432776 433719 := bstep (se 1 (by rfl) ⟨325289, by rfl⟩ : syracuseStep 433719 = 650579) B650579
theorem B974411 : Blo 432776 974411 := bstep (se 1 (by rfl) ⟨730808, by rfl⟩ : syracuseStep 974411 = 1461617) B1461617
theorem B433739 : Blo 432776 433739 := bstep (se 1 (by rfl) ⟨325304, by rfl⟩ : syracuseStep 433739 = 650609) B650609
theorem B433751 : Blo 432776 433751 := bstep (se 1 (by rfl) ⟨325313, by rfl⟩ : syracuseStep 433751 = 650627) B650627
theorem B753241 : Blo 432776 753241 := bstep (se 2 (by rfl) ⟨282465, by rfl⟩ : syracuseStep 753241 = 564931) B564931
theorem B4955741 : Blo 432776 4955741 := bstep (se 3 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 4955741 = 1858403) B1858403
theorem B433771 : Blo 432776 433771 := bstep (se 1 (by rfl) ⟨325328, by rfl⟩ : syracuseStep 433771 = 650657) B650657
theorem B433783 : Blo 432776 433783 := bstep (se 1 (by rfl) ⟨325337, by rfl⟩ : syracuseStep 433783 = 650675) B650675
theorem B974465 : Blo 432776 974465 := bstep (se 2 (by rfl) ⟨365424, by rfl⟩ : syracuseStep 974465 = 730849) B730849
theorem B433803 : Blo 432776 433803 := bstep (se 1 (by rfl) ⟨325352, by rfl⟩ : syracuseStep 433803 = 650705) B650705
theorem B433815 : Blo 432776 433815 := bstep (se 1 (by rfl) ⟨325361, by rfl⟩ : syracuseStep 433815 = 650723) B650723
theorem B433835 : Blo 432776 433835 := bstep (se 1 (by rfl) ⟨325376, by rfl⟩ : syracuseStep 433835 = 650753) B650753
theorem B1654451 : Blo 432776 1654451 := bstep (se 1 (by rfl) ⟨1240838, by rfl⟩ : syracuseStep 1654451 = 2481677) B2481677
theorem B433847 : Blo 432776 433847 := bstep (se 1 (by rfl) ⟨325385, by rfl⟩ : syracuseStep 433847 = 650771) B650771
theorem B1654465 : Blo 432776 1654465 := bstep (se 2 (by rfl) ⟨620424, by rfl⟩ : syracuseStep 1654465 = 1240849) B1240849
theorem B433867 : Blo 432776 433867 := bstep (se 1 (by rfl) ⟨325400, by rfl⟩ : syracuseStep 433867 = 650801) B650801
theorem B433879 : Blo 432776 433879 := bstep (se 1 (by rfl) ⟨325409, by rfl⟩ : syracuseStep 433879 = 650819) B650819
theorem B433899 : Blo 432776 433899 := bstep (se 1 (by rfl) ⟨325424, by rfl⟩ : syracuseStep 433899 = 650849) B650849
theorem B433911 : Blo 432776 433911 := bstep (se 1 (by rfl) ⟨325433, by rfl⟩ : syracuseStep 433911 = 650867) B650867
theorem B433931 : Blo 432776 433931 := bstep (se 1 (by rfl) ⟨325448, by rfl⟩ : syracuseStep 433931 = 650897) B650897
theorem B1859345 : Blo 432776 1859345 := bstep (se 2 (by rfl) ⟨697254, by rfl⟩ : syracuseStep 1859345 = 1394509) B1394509
theorem B433943 : Blo 432776 433943 := bstep (se 1 (by rfl) ⟨325457, by rfl⟩ : syracuseStep 433943 = 650915) B650915
theorem B433963 : Blo 432776 433963 := bstep (se 1 (by rfl) ⟨325472, by rfl⟩ : syracuseStep 433963 = 650945) B650945
theorem B3956525 : Blo 432776 3956525 := bstep (se 3 (by rfl) ⟨741848, by rfl⟩ : syracuseStep 3956525 = 1483697) B1483697
theorem B433975 : Blo 432776 433975 := bstep (se 1 (by rfl) ⟨325481, by rfl⟩ : syracuseStep 433975 = 650963) B650963
theorem B433995 : Blo 432776 433995 := bstep (se 1 (by rfl) ⟨325496, by rfl⟩ : syracuseStep 433995 = 650993) B650993
theorem B434007 : Blo 432776 434007 := bstep (se 1 (by rfl) ⟨325505, by rfl⟩ : syracuseStep 434007 = 651011) B651011
theorem B974681 : Blo 432776 974681 := bstep (se 2 (by rfl) ⟨365505, by rfl⟩ : syracuseStep 974681 = 731011) B731011
theorem B1236829 : Blo 432776 1236829 := bstep (se 3 (by rfl) ⟨231905, by rfl⟩ : syracuseStep 1236829 = 463811) B463811
theorem B434027 : Blo 432776 434027 := bstep (se 1 (by rfl) ⟨325520, by rfl⟩ : syracuseStep 434027 = 651041) B651041
theorem B434039 : Blo 432776 434039 := bstep (se 1 (by rfl) ⟨325529, by rfl⟩ : syracuseStep 434039 = 651059) B651059
theorem B2203523 : Blo 432776 2203523 := bstep (se 1 (by rfl) ⟨1652642, by rfl⟩ : syracuseStep 2203523 = 3305285) B3305285
theorem B434059 : Blo 432776 434059 := bstep (se 1 (by rfl) ⟨325544, by rfl⟩ : syracuseStep 434059 = 651089) B651089
theorem B1851281 : Blo 432776 1851281 := bstep (se 2 (by rfl) ⟨694230, by rfl⟩ : syracuseStep 1851281 = 1388461) B1388461
theorem B1171351 : Blo 432776 1171351 := bstep (se 1 (by rfl) ⟨878513, by rfl⟩ : syracuseStep 1171351 = 1757027) B1757027
theorem B434071 : Blo 432776 434071 := bstep (se 1 (by rfl) ⟨325553, by rfl⟩ : syracuseStep 434071 = 651107) B651107
theorem B434091 : Blo 432776 434091 := bstep (se 1 (by rfl) ⟨325568, by rfl⟩ : syracuseStep 434091 = 651137) B651137
theorem B974771 : Blo 432776 974771 := bstep (se 1 (by rfl) ⟨731078, by rfl⟩ : syracuseStep 974771 = 1462157) B1462157
theorem B1097651 : Blo 432776 1097651 := bstep (se 1 (by rfl) ⟨823238, by rfl⟩ : syracuseStep 1097651 = 1646477) B1646477
theorem B434103 : Blo 432776 434103 := bstep (se 1 (by rfl) ⟨325577, by rfl⟩ : syracuseStep 434103 = 651155) B651155
theorem B434123 : Blo 432776 434123 := bstep (se 1 (by rfl) ⟨325592, by rfl⟩ : syracuseStep 434123 = 651185) B651185
theorem B1466315 : Blo 432776 1466315 := bstep (se 1 (by rfl) ⟨1099736, by rfl⟩ : syracuseStep 1466315 = 2199473) B2199473
theorem B974807 : Blo 432776 974807 := bstep (se 1 (by rfl) ⟨731105, by rfl⟩ : syracuseStep 974807 = 1462211) B1462211
theorem B434135 : Blo 432776 434135 := bstep (se 1 (by rfl) ⟨325601, by rfl⟩ : syracuseStep 434135 = 651203) B651203
theorem B434155 : Blo 432776 434155 := bstep (se 1 (by rfl) ⟨325616, by rfl⟩ : syracuseStep 434155 = 651233) B651233
theorem B434167 : Blo 432776 434167 := bstep (se 1 (by rfl) ⟨325625, by rfl⟩ : syracuseStep 434167 = 651251) B651251
theorem B434183 : Blo 432776 434183 := bstep (se 1 (by rfl) ⟨325637, by rfl⟩ : syracuseStep 434183 = 651275) B651275
theorem B434191 : Blo 432776 434191 := bstep (se 1 (by rfl) ⟨325643, by rfl⟩ : syracuseStep 434191 = 651287) B651287
theorem B434235 : Blo 432776 434235 := bstep (se 1 (by rfl) ⟨325676, by rfl⟩ : syracuseStep 434235 = 651353) B651353
theorem B1392727 : Blo 432776 1392727 := bstep (se 1 (by rfl) ⟨1044545, by rfl⟩ : syracuseStep 1392727 = 2089091) B2089091
theorem B434311 : Blo 432776 434311 := bstep (se 1 (by rfl) ⟨325733, by rfl⟩ : syracuseStep 434311 = 651467) B651467
theorem B434319 : Blo 432776 434319 := bstep (se 1 (by rfl) ⟨325739, by rfl⟩ : syracuseStep 434319 = 651479) B651479
theorem B434363 : Blo 432776 434363 := bstep (se 1 (by rfl) ⟨325772, by rfl⟩ : syracuseStep 434363 = 651545) B651545
theorem B1040585 : Blo 432776 1040585 := bstep (se 2 (by rfl) ⟨390219, by rfl⟩ : syracuseStep 1040585 = 780439) B780439
theorem B4702445 : Blo 432776 4702445 := bstep (se 3 (by rfl) ⟨881708, by rfl⟩ : syracuseStep 4702445 = 1763417) B1763417
theorem B434439 : Blo 432776 434439 := bstep (se 1 (by rfl) ⟨325829, by rfl⟩ : syracuseStep 434439 = 651659) B651659
theorem B1097995 : Blo 432776 1097995 := bstep (se 1 (by rfl) ⟨823496, by rfl⟩ : syracuseStep 1097995 = 1646993) B1646993
theorem B434447 : Blo 432776 434447 := bstep (se 1 (by rfl) ⟨325835, by rfl⟩ : syracuseStep 434447 = 651671) B651671
theorem B1466639 : Blo 432776 1466639 := bstep (se 1 (by rfl) ⟨1099979, by rfl⟩ : syracuseStep 1466639 = 2199959) B2199959
theorem B434491 : Blo 432776 434491 := bstep (se 1 (by rfl) ⟨325868, by rfl⟩ : syracuseStep 434491 = 651737) B651737
theorem B1646963 : Blo 432776 1646963 := bstep (se 1 (by rfl) ⟨1235222, by rfl⟩ : syracuseStep 1646963 = 2470445) B2470445
theorem B975239 : Blo 432776 975239 := bstep (se 1 (by rfl) ⟨731429, by rfl⟩ : syracuseStep 975239 = 1462859) B1462859
theorem B434567 : Blo 432776 434567 := bstep (se 1 (by rfl) ⟨325925, by rfl⟩ : syracuseStep 434567 = 651851) B651851
theorem B434575 : Blo 432776 434575 := bstep (se 1 (by rfl) ⟨325931, by rfl⟩ : syracuseStep 434575 = 651863) B651863
theorem B7029139 : Blo 432776 7029139 := bstep (se 1 (by rfl) ⟨5271854, by rfl⟩ : syracuseStep 7029139 = 10543709) B10543709
theorem B2474387 : Blo 432776 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B1098137 : Blo 432776 1098137 := bstep (se 2 (by rfl) ⟨411801, by rfl⟩ : syracuseStep 1098137 = 823603) B823603
theorem B434619 : Blo 432776 434619 := bstep (se 1 (by rfl) ⟨325964, by rfl⟩ : syracuseStep 434619 = 651929) B651929
theorem B434695 : Blo 432776 434695 := bstep (se 1 (by rfl) ⟨326021, by rfl⟩ : syracuseStep 434695 = 652043) B652043
theorem B434703 : Blo 432776 434703 := bstep (se 1 (by rfl) ⟨326027, by rfl⟩ : syracuseStep 434703 = 652055) B652055
theorem B991759 : Blo 432776 991759 := bstep (se 1 (by rfl) ⟨743819, by rfl⟩ : syracuseStep 991759 = 1487639) B1487639
theorem B2204171 : Blo 432776 2204171 := bstep (se 1 (by rfl) ⟨1653128, by rfl⟩ : syracuseStep 2204171 = 3306257) B3306257
theorem B1466909 : Blo 432776 1466909 := bstep (se 3 (by rfl) ⟨275045, by rfl⟩ : syracuseStep 1466909 = 550091) B550091
theorem B975419 : Blo 432776 975419 := bstep (se 1 (by rfl) ⟨731564, by rfl⟩ : syracuseStep 975419 = 1463129) B1463129
theorem B1098299 : Blo 432776 1098299 := bstep (se 1 (by rfl) ⟨823724, by rfl⟩ : syracuseStep 1098299 = 1647449) B1647449
theorem B434747 : Blo 432776 434747 := bstep (se 1 (by rfl) ⟨326060, by rfl⟩ : syracuseStep 434747 = 652121) B652121
theorem B434823 : Blo 432776 434823 := bstep (se 1 (by rfl) ⟨326117, by rfl⟩ : syracuseStep 434823 = 652235) B652235
theorem B434831 : Blo 432776 434831 := bstep (se 1 (by rfl) ⟨326123, by rfl⟩ : syracuseStep 434831 = 652247) B652247
theorem B2204333 : Blo 432776 2204333 := bstep (se 3 (by rfl) ⟨413312, by rfl⟩ : syracuseStep 2204333 = 826625) B826625
theorem B4694705 : Blo 432776 4694705 := bstep (se 2 (by rfl) ⟨1760514, by rfl⟩ : syracuseStep 4694705 = 3521029) B3521029
theorem B975545 : Blo 432776 975545 := bstep (se 2 (by rfl) ⟨365829, by rfl⟩ : syracuseStep 975545 = 731659) B731659
theorem B434875 : Blo 432776 434875 := bstep (se 1 (by rfl) ⟨326156, by rfl⟩ : syracuseStep 434875 = 652313) B652313
theorem B1114825 : Blo 432776 1114825 := bstep (se 2 (by rfl) ⟨418059, by rfl⟩ : syracuseStep 1114825 = 836119) B836119
theorem B1860353 : Blo 432776 1860353 := bstep (se 2 (by rfl) ⟨697632, by rfl⟩ : syracuseStep 1860353 = 1395265) B1395265
theorem B434951 : Blo 432776 434951 := bstep (se 1 (by rfl) ⟨326213, by rfl⟩ : syracuseStep 434951 = 652427) B652427
theorem B434959 : Blo 432776 434959 := bstep (se 1 (by rfl) ⟨326219, by rfl⟩ : syracuseStep 434959 = 652439) B652439
theorem B3719951 : Blo 432776 3719951 := bstep (se 1 (by rfl) ⟨2789963, by rfl⟩ : syracuseStep 3719951 = 5579927) B5579927
theorem B1876769 : Blo 432776 1876769 := bstep (se 2 (by rfl) ⟨703788, by rfl⟩ : syracuseStep 1876769 = 1407577) B1407577
theorem B34382627 : Blo 432776 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B1254203 : Blo 432776 1254203 := bstep (se 1 (by rfl) ⟨940652, by rfl⟩ : syracuseStep 1254203 = 1881305) B1881305
theorem B435003 : Blo 432776 435003 := bstep (se 1 (by rfl) ⟨326252, by rfl⟩ : syracuseStep 435003 = 652505) B652505
theorem B4997963 : Blo 432776 4997963 := bstep (se 1 (by rfl) ⟨3748472, by rfl⟩ : syracuseStep 4997963 = 7496945) B7496945
theorem B549767 : Blo 432776 549767 := bstep (se 1 (by rfl) ⟨412325, by rfl⟩ : syracuseStep 549767 = 824651) B824651
theorem B435079 : Blo 432776 435079 := bstep (se 1 (by rfl) ⟨326309, by rfl⟩ : syracuseStep 435079 = 652619) B652619
theorem B697223 : Blo 432776 697223 := bstep (se 1 (by rfl) ⟨522917, by rfl⟩ : syracuseStep 697223 = 1045835) B1045835
theorem B435087 : Blo 432776 435087 := bstep (se 1 (by rfl) ⟨326315, by rfl⟩ : syracuseStep 435087 = 652631) B652631
theorem B1098643 : Blo 432776 1098643 := bstep (se 1 (by rfl) ⟨823982, by rfl⟩ : syracuseStep 1098643 = 1647965) B1647965
theorem B3130265 : Blo 432776 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B435131 : Blo 432776 435131 := bstep (se 1 (by rfl) ⟨326348, by rfl⟩ : syracuseStep 435131 = 652697) B652697
theorem B435207 : Blo 432776 435207 := bstep (se 1 (by rfl) ⟨326405, by rfl⟩ : syracuseStep 435207 = 652811) B652811
theorem B975887 : Blo 432776 975887 := bstep (se 1 (by rfl) ⟨731915, by rfl⟩ : syracuseStep 975887 = 1463831) B1463831
theorem B435215 : Blo 432776 435215 := bstep (se 1 (by rfl) ⟨326411, by rfl⟩ : syracuseStep 435215 = 652823) B652823
theorem B2466845 : Blo 432776 2466845 := bstep (se 3 (by rfl) ⟨462533, by rfl⟩ : syracuseStep 2466845 = 925067) B925067
theorem B975905 : Blo 432776 975905 := bstep (se 2 (by rfl) ⟨365964, by rfl⟩ : syracuseStep 975905 = 731929) B731929
theorem B1098785 : Blo 432776 1098785 := bstep (se 2 (by rfl) ⟨412044, by rfl⟩ : syracuseStep 1098785 = 824089) B824089
theorem B5350445 : Blo 432776 5350445 := bstep (se 3 (by rfl) ⟨1003208, by rfl⟩ : syracuseStep 5350445 = 2006417) B2006417
theorem B435259 : Blo 432776 435259 := bstep (se 1 (by rfl) ⟨326444, by rfl⟩ : syracuseStep 435259 = 652889) B652889
theorem B1590359 : Blo 432776 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B1860727 : Blo 432776 1860727 := bstep (se 1 (by rfl) ⟨1395545, by rfl⟩ : syracuseStep 1860727 = 2791091) B2791091
theorem B435335 : Blo 432776 435335 := bstep (se 1 (by rfl) ⟨326501, by rfl⟩ : syracuseStep 435335 = 653003) B653003
theorem B435343 : Blo 432776 435343 := bstep (se 1 (by rfl) ⟨326507, by rfl⟩ : syracuseStep 435343 = 653015) B653015
theorem B435387 : Blo 432776 435387 := bstep (se 1 (by rfl) ⟨326540, by rfl⟩ : syracuseStep 435387 = 653081) B653081
theorem B435463 : Blo 432776 435463 := bstep (se 1 (by rfl) ⟨326597, by rfl⟩ : syracuseStep 435463 = 653195) B653195
theorem B1238287 : Blo 432776 1238287 := bstep (se 1 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 1238287 = 1857431) B1857431
theorem B435471 : Blo 432776 435471 := bstep (se 1 (by rfl) ⟨326603, by rfl⟩ : syracuseStep 435471 = 653207) B653207
theorem B1697057 : Blo 432776 1697057 := bstep (se 2 (by rfl) ⟨636396, by rfl⟩ : syracuseStep 1697057 = 1272793) B1272793
theorem B435515 : Blo 432776 435515 := bstep (se 1 (by rfl) ⟨326636, by rfl⟩ : syracuseStep 435515 = 653273) B653273
theorem B976247 : Blo 432776 976247 := bstep (se 1 (by rfl) ⟨732185, by rfl⟩ : syracuseStep 976247 = 1464371) B1464371
theorem B435591 : Blo 432776 435591 := bstep (se 1 (by rfl) ⟨326693, by rfl⟩ : syracuseStep 435591 = 653387) B653387
theorem B435599 : Blo 432776 435599 := bstep (se 1 (by rfl) ⟨326699, by rfl⟩ : syracuseStep 435599 = 653399) B653399
theorem B2196881 : Blo 432776 2196881 := bstep (se 2 (by rfl) ⟨823830, by rfl⟩ : syracuseStep 2196881 = 1647661) B1647661
theorem B1672595 : Blo 432776 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B435643 : Blo 432776 435643 := bstep (se 1 (by rfl) ⟨326732, by rfl⟩ : syracuseStep 435643 = 653465) B653465
theorem B1983953 : Blo 432776 1983953 := bstep (se 2 (by rfl) ⟨743982, by rfl⟩ : syracuseStep 1983953 = 1487965) B1487965
theorem B1041931 : Blo 432776 1041931 := bstep (se 1 (by rfl) ⟨781448, by rfl⟩ : syracuseStep 1041931 = 1562897) B1562897
theorem B435719 : Blo 432776 435719 := bstep (se 1 (by rfl) ⟨326789, by rfl⟩ : syracuseStep 435719 = 653579) B653579
theorem B550415 : Blo 432776 550415 := bstep (se 1 (by rfl) ⟨412811, by rfl⟩ : syracuseStep 550415 = 825623) B825623
theorem B435727 : Blo 432776 435727 := bstep (se 1 (by rfl) ⟨326795, by rfl⟩ : syracuseStep 435727 = 653591) B653591
theorem B1238561 : Blo 432776 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B730667 : Blo 432776 730667 := bstep (se 1 (by rfl) ⟨548000, by rfl⟩ : syracuseStep 730667 = 1096001) B1096001
theorem B976427 : Blo 432776 976427 := bstep (se 1 (by rfl) ⟨732320, by rfl⟩ : syracuseStep 976427 = 1464641) B1464641
theorem B435771 : Blo 432776 435771 := bstep (se 1 (by rfl) ⟨326828, by rfl⟩ : syracuseStep 435771 = 653657) B653657
theorem B2467529 : Blo 432776 2467529 := bstep (se 2 (by rfl) ⟨925323, by rfl⟩ : syracuseStep 2467529 = 1850647) B1850647
theorem B1697537 : Blo 432776 1697537 := bstep (se 2 (by rfl) ⟨636576, by rfl⟩ : syracuseStep 1697537 = 1273153) B1273153
theorem B4450099 : Blo 432776 4450099 := bstep (se 1 (by rfl) ⟨3337574, by rfl⟩ : syracuseStep 4450099 = 6675149) B6675149
theorem B2639675 : Blo 432776 2639675 := bstep (se 1 (by rfl) ⟨1979756, by rfl⟩ : syracuseStep 2639675 = 3959513) B3959513
theorem B976787 : Blo 432776 976787 := bstep (se 1 (by rfl) ⟨732590, by rfl⟩ : syracuseStep 976787 = 1465181) B1465181
theorem B1468313 : Blo 432776 1468313 := bstep (se 2 (by rfl) ⟨550617, by rfl⟩ : syracuseStep 1468313 = 1101235) B1101235
theorem B731065 : Blo 432776 731065 := bstep (se 2 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 731065 = 548299) B548299
theorem B976841 : Blo 432776 976841 := bstep (se 2 (by rfl) ⟨366315, by rfl⟩ : syracuseStep 976841 = 732631) B732631
theorem B1099777 : Blo 432776 1099777 := bstep (se 2 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 1099777 = 824833) B824833
theorem B649223 : Blo 432776 649223 := bstep (se 1 (by rfl) ⟨486917, by rfl⟩ : syracuseStep 649223 = 973835) B973835
theorem B6678551 : Blo 432776 6678551 := bstep (se 1 (by rfl) ⟨5008913, by rfl⟩ : syracuseStep 6678551 = 10017827) B10017827
theorem B649259 : Blo 432776 649259 := bstep (se 1 (by rfl) ⟨486944, by rfl⟩ : syracuseStep 649259 = 973889) B973889
theorem B1976363 : Blo 432776 1976363 := bstep (se 1 (by rfl) ⟨1482272, by rfl⟩ : syracuseStep 1976363 = 2964545) B2964545
theorem B706619 : Blo 432776 706619 := bstep (se 1 (by rfl) ⟨529964, by rfl⟩ : syracuseStep 706619 = 1059929) B1059929
theorem B649289 : Blo 432776 649289 := bstep (se 2 (by rfl) ⟨243483, by rfl⟩ : syracuseStep 649289 = 486967) B486967
theorem B649403 : Blo 432776 649403 := bstep (se 1 (by rfl) ⟨487052, by rfl⟩ : syracuseStep 649403 = 974105) B974105
theorem B649463 : Blo 432776 649463 := bstep (se 1 (by rfl) ⟨487097, by rfl⟩ : syracuseStep 649463 = 974195) B974195
theorem B2205953 : Blo 432776 2205953 := bstep (se 2 (by rfl) ⟨827232, by rfl⟩ : syracuseStep 2205953 = 1654465) B1654465
theorem B649487 : Blo 432776 649487 := bstep (se 1 (by rfl) ⟨487115, by rfl⟩ : syracuseStep 649487 = 974231) B974231
theorem B2509093 : Blo 432776 2509093 := bstep (se 4 (by rfl) ⟨235227, by rfl⟩ : syracuseStep 2509093 = 470455) B470455
theorem B649529 : Blo 432776 649529 := bstep (se 2 (by rfl) ⟨243573, by rfl⟩ : syracuseStep 649529 = 487147) B487147
theorem B1042807 : Blo 432776 1042807 := bstep (se 1 (by rfl) ⟨782105, by rfl⟩ : syracuseStep 1042807 = 1564211) B1564211
theorem B649607 : Blo 432776 649607 := bstep (se 1 (by rfl) ⟨487205, by rfl⟩ : syracuseStep 649607 = 974411) B974411
theorem B3303827 : Blo 432776 3303827 := bstep (se 1 (by rfl) ⟨2477870, by rfl⟩ : syracuseStep 3303827 = 4955741) B4955741
theorem B649643 : Blo 432776 649643 := bstep (se 1 (by rfl) ⟨487232, by rfl⟩ : syracuseStep 649643 = 974465) B974465
theorem B649673 : Blo 432776 649673 := bstep (se 2 (by rfl) ⟨243627, by rfl⟩ : syracuseStep 649673 = 487255) B487255
theorem B1649105 : Blo 432776 1649105 := bstep (se 2 (by rfl) ⟨618414, by rfl⟩ : syracuseStep 1649105 = 1236829) B1236829
theorem B1239563 : Blo 432776 1239563 := bstep (se 1 (by rfl) ⟨929672, by rfl⟩ : syracuseStep 1239563 = 1859345) B1859345
theorem B1387037 : Blo 432776 1387037 := bstep (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) B520139
theorem B821819 : Blo 432776 821819 := bstep (se 1 (by rfl) ⟨616364, by rfl⟩ : syracuseStep 821819 = 1232729) B1232729
theorem B649787 : Blo 432776 649787 := bstep (se 1 (by rfl) ⟨487340, by rfl⟩ : syracuseStep 649787 = 974681) B974681
theorem B2509373 : Blo 432776 2509373 := bstep (se 3 (by rfl) ⟨470507, by rfl⟩ : syracuseStep 2509373 = 941015) B941015
theorem B1100375 : Blo 432776 1100375 := bstep (se 1 (by rfl) ⟨825281, by rfl⟩ : syracuseStep 1100375 = 1650563) B1650563
theorem B1469015 : Blo 432776 1469015 := bstep (se 1 (by rfl) ⟨1101761, by rfl⟩ : syracuseStep 1469015 = 2203523) B2203523
theorem B649847 : Blo 432776 649847 := bstep (se 1 (by rfl) ⟨487385, by rfl⟩ : syracuseStep 649847 = 974771) B974771
theorem B731767 : Blo 432776 731767 := bstep (se 1 (by rfl) ⟨548825, by rfl⟩ : syracuseStep 731767 = 1097651) B1097651
theorem B977543 : Blo 432776 977543 := bstep (se 1 (by rfl) ⟨733157, by rfl⟩ : syracuseStep 977543 = 1466315) B1466315
theorem B649871 : Blo 432776 649871 := bstep (se 1 (by rfl) ⟨487403, by rfl⟩ : syracuseStep 649871 = 974807) B974807
theorem B649913 : Blo 432776 649913 := bstep (se 2 (by rfl) ⟨243717, by rfl⟩ : syracuseStep 649913 = 487435) B487435
theorem B5065409 : Blo 432776 5065409 := bstep (se 2 (by rfl) ⟨1899528, by rfl⟩ : syracuseStep 5065409 = 3799057) B3799057
theorem B1780481 : Blo 432776 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B649991 : Blo 432776 649991 := bstep (se 1 (by rfl) ⟨487493, by rfl⟩ : syracuseStep 649991 = 974987) B974987
theorem B2779919 : Blo 432776 2779919 := bstep (se 1 (by rfl) ⟨2084939, by rfl⟩ : syracuseStep 2779919 = 4169879) B4169879
theorem B1649423 : Blo 432776 1649423 := bstep (se 1 (by rfl) ⟨1237067, by rfl⟩ : syracuseStep 1649423 = 2474135) B2474135
theorem B650027 : Blo 432776 650027 := bstep (se 1 (by rfl) ⟨487520, by rfl⟩ : syracuseStep 650027 = 975041) B975041
theorem B1100587 : Blo 432776 1100587 := bstep (se 1 (by rfl) ⟨825440, by rfl⟩ : syracuseStep 1100587 = 1650881) B1650881
theorem B3296051 : Blo 432776 3296051 := bstep (se 1 (by rfl) ⟨2472038, by rfl⟩ : syracuseStep 3296051 = 4944077) B4944077
theorem B731963 : Blo 432776 731963 := bstep (se 1 (by rfl) ⟨548972, by rfl⟩ : syracuseStep 731963 = 1097945) B1097945
theorem B977723 : Blo 432776 977723 := bstep (se 1 (by rfl) ⟨733292, by rfl⟩ : syracuseStep 977723 = 1466585) B1466585
theorem B650057 : Blo 432776 650057 := bstep (se 2 (by rfl) ⟨243771, by rfl⟩ : syracuseStep 650057 = 487543) B487543
theorem B3140441 : Blo 432776 3140441 := bstep (se 2 (by rfl) ⟨1177665, by rfl⟩ : syracuseStep 3140441 = 2355331) B2355331
theorem B1239961 : Blo 432776 1239961 := bstep (se 2 (by rfl) ⟨464985, by rfl⟩ : syracuseStep 1239961 = 929971) B929971
theorem B977849 : Blo 432776 977849 := bstep (se 2 (by rfl) ⟨366693, by rfl⟩ : syracuseStep 977849 = 733387) B733387
theorem B1100729 : Blo 432776 1100729 := bstep (se 2 (by rfl) ⟨412773, by rfl⟩ : syracuseStep 1100729 = 825547) B825547
theorem B658363 : Blo 432776 658363 := bstep (se 1 (by rfl) ⟨493772, by rfl⟩ : syracuseStep 658363 = 987545) B987545
theorem B650171 : Blo 432776 650171 := bstep (se 1 (by rfl) ⟨487628, by rfl⟩ : syracuseStep 650171 = 975257) B975257
theorem B650231 : Blo 432776 650231 := bstep (se 1 (by rfl) ⟨487673, by rfl⟩ : syracuseStep 650231 = 975347) B975347
theorem B650255 : Blo 432776 650255 := bstep (se 1 (by rfl) ⟨487691, by rfl⟩ : syracuseStep 650255 = 975383) B975383
theorem B822305 : Blo 432776 822305 := bstep (se 2 (by rfl) ⟨308364, by rfl⟩ : syracuseStep 822305 = 616729) B616729
theorem B650297 : Blo 432776 650297 := bstep (se 2 (by rfl) ⟨243861, by rfl⟩ : syracuseStep 650297 = 487723) B487723
theorem B1469501 : Blo 432776 1469501 := bstep (se 3 (by rfl) ⟨275531, by rfl⟩ : syracuseStep 1469501 = 551063) B551063
theorem B3140669 : Blo 432776 3140669 := bstep (se 3 (by rfl) ⟨588875, by rfl⟩ : syracuseStep 3140669 = 1177751) B1177751
theorem B650375 : Blo 432776 650375 := bstep (se 1 (by rfl) ⟨487781, by rfl⟩ : syracuseStep 650375 = 975563) B975563
theorem B1240211 : Blo 432776 1240211 := bstep (se 1 (by rfl) ⟨930158, by rfl⟩ : syracuseStep 1240211 = 1860317) B1860317
theorem B650411 : Blo 432776 650411 := bstep (se 1 (by rfl) ⟨487808, by rfl⟩ : syracuseStep 650411 = 975617) B975617
theorem B650441 : Blo 432776 650441 := bstep (se 2 (by rfl) ⟨243915, by rfl⟩ : syracuseStep 650441 = 487831) B487831
theorem B732361 : Blo 432776 732361 := bstep (se 2 (by rfl) ⟨274635, by rfl⟩ : syracuseStep 732361 = 549271) B549271
theorem B978191 : Blo 432776 978191 := bstep (se 1 (by rfl) ⟨733643, by rfl⟩ : syracuseStep 978191 = 1467287) B1467287
theorem B3706145 : Blo 432776 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B978209 : Blo 432776 978209 := bstep (se 2 (by rfl) ⟨366828, by rfl⟩ : syracuseStep 978209 = 733657) B733657
theorem B1461563 : Blo 432776 1461563 := bstep (se 1 (by rfl) ⟨1096172, by rfl⟩ : syracuseStep 1461563 = 2192345) B2192345
theorem B650555 : Blo 432776 650555 := bstep (se 1 (by rfl) ⟨487916, by rfl⟩ : syracuseStep 650555 = 975833) B975833
theorem B929083 : Blo 432776 929083 := bstep (se 1 (by rfl) ⟨696812, by rfl⟩ : syracuseStep 929083 = 1393625) B1393625
theorem B650615 : Blo 432776 650615 := bstep (se 1 (by rfl) ⟨487961, by rfl⟩ : syracuseStep 650615 = 975923) B975923
theorem B650639 : Blo 432776 650639 := bstep (se 1 (by rfl) ⟨487979, by rfl⟩ : syracuseStep 650639 = 975959) B975959
theorem B2469305 : Blo 432776 2469305 := bstep (se 2 (by rfl) ⟨925989, by rfl⟩ : syracuseStep 2469305 = 1851979) B1851979
theorem B650681 : Blo 432776 650681 := bstep (se 2 (by rfl) ⟨244005, by rfl⟩ : syracuseStep 650681 = 488011) B488011
theorem B2198987 : Blo 432776 2198987 := bstep (se 1 (by rfl) ⟨1649240, by rfl⟩ : syracuseStep 2198987 = 3298481) B3298481
theorem B650759 : Blo 432776 650759 := bstep (se 1 (by rfl) ⟨488069, by rfl⟩ : syracuseStep 650759 = 976139) B976139
theorem B650795 : Blo 432776 650795 := bstep (se 1 (by rfl) ⟨488096, by rfl⟩ : syracuseStep 650795 = 976193) B976193
theorem B650825 : Blo 432776 650825 := bstep (se 2 (by rfl) ⟨244059, by rfl⟩ : syracuseStep 650825 = 488119) B488119
theorem B3124813 : Blo 432776 3124813 := bstep (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) B1171805
theorem B978551 : Blo 432776 978551 := bstep (se 1 (by rfl) ⟨733913, by rfl⟩ : syracuseStep 978551 = 1467827) B1467827
theorem B650939 : Blo 432776 650939 := bstep (se 1 (by rfl) ⟨488204, by rfl⟩ : syracuseStep 650939 = 976409) B976409
theorem B2191049 : Blo 432776 2191049 := bstep (se 2 (by rfl) ⟨821643, by rfl⟩ : syracuseStep 2191049 = 1643287) B1643287
theorem B2789093 : Blo 432776 2789093 := bstep (se 4 (by rfl) ⟨261477, by rfl⟩ : syracuseStep 2789093 = 522955) B522955
theorem B650999 : Blo 432776 650999 := bstep (se 1 (by rfl) ⟨488249, by rfl⟩ : syracuseStep 650999 = 976499) B976499
theorem B1060619 : Blo 432776 1060619 := bstep (se 1 (by rfl) ⟨795464, by rfl⟩ : syracuseStep 1060619 = 1590929) B1590929
theorem B487183 : Blo 432776 487183 := bstep (se 1 (by rfl) ⟨365387, by rfl⟩ : syracuseStep 487183 = 730775) B730775
theorem B651023 : Blo 432776 651023 := bstep (se 1 (by rfl) ⟨488267, by rfl⟩ : syracuseStep 651023 = 976535) B976535
theorem B2199311 : Blo 432776 2199311 := bstep (se 1 (by rfl) ⟨1649483, by rfl⟩ : syracuseStep 2199311 = 3298967) B3298967
theorem B1462049 : Blo 432776 1462049 := bstep (se 2 (by rfl) ⟨548268, by rfl⟩ : syracuseStep 1462049 = 1096537) B1096537
theorem B1175329 : Blo 432776 1175329 := bstep (se 2 (by rfl) ⟨440748, by rfl⟩ : syracuseStep 1175329 = 881497) B881497
theorem B618283 : Blo 432776 618283 := bstep (se 1 (by rfl) ⟨463712, by rfl⟩ : syracuseStep 618283 = 927425) B927425
theorem B880427 : Blo 432776 880427 := bstep (se 1 (by rfl) ⟨660320, by rfl⟩ : syracuseStep 880427 = 1320641) B1320641
theorem B978731 : Blo 432776 978731 := bstep (se 1 (by rfl) ⟨734048, by rfl⟩ : syracuseStep 978731 = 1468097) B1468097
theorem B651065 : Blo 432776 651065 := bstep (se 2 (by rfl) ⟨244149, by rfl⟩ : syracuseStep 651065 = 488299) B488299
theorem B4960115 : Blo 432776 4960115 := bstep (se 1 (by rfl) ⟨3720086, by rfl⟩ : syracuseStep 4960115 = 7440173) B7440173
theorem B651143 : Blo 432776 651143 := bstep (se 1 (by rfl) ⟨488357, by rfl⟩ : syracuseStep 651143 = 976715) B976715
theorem B733063 : Blo 432776 733063 := bstep (se 1 (by rfl) ⟨549797, by rfl⟩ : syracuseStep 733063 = 1099595) B1099595
theorem B782227 : Blo 432776 782227 := bstep (se 1 (by rfl) ⟨586670, by rfl⟩ : syracuseStep 782227 = 1173341) B1173341
theorem B1101721 : Blo 432776 1101721 := bstep (se 2 (by rfl) ⟨413145, by rfl⟩ : syracuseStep 1101721 = 826291) B826291
theorem B651179 : Blo 432776 651179 := bstep (se 1 (by rfl) ⟨488384, by rfl⟩ : syracuseStep 651179 = 976769) B976769
theorem B651209 : Blo 432776 651209 := bstep (se 2 (by rfl) ⟨244203, by rfl⟩ : syracuseStep 651209 = 488407) B488407
theorem B618511 : Blo 432776 618511 := bstep (se 1 (by rfl) ⟨463883, by rfl⟩ : syracuseStep 618511 = 927767) B927767
theorem B17813525 : Blo 432776 17813525 := bstep (se 6 (by rfl) ⟨417504, by rfl⟩ : syracuseStep 17813525 = 835009) B835009
theorem B651323 : Blo 432776 651323 := bstep (se 1 (by rfl) ⟨488492, by rfl⟩ : syracuseStep 651323 = 976985) B976985
theorem B1101883 : Blo 432776 1101883 := bstep (se 1 (by rfl) ⟨826412, by rfl⟩ : syracuseStep 1101883 = 1652825) B1652825
theorem B651383 : Blo 432776 651383 := bstep (se 1 (by rfl) ⟨488537, by rfl⟩ : syracuseStep 651383 = 977075) B977075
theorem B462991 : Blo 432776 462991 := bstep (se 1 (by rfl) ⟨347243, by rfl⟩ : syracuseStep 462991 = 694487) B694487
theorem B651407 : Blo 432776 651407 := bstep (se 1 (by rfl) ⟨488555, by rfl⟩ : syracuseStep 651407 = 977111) B977111
theorem B979091 : Blo 432776 979091 := bstep (se 1 (by rfl) ⟨734318, by rfl⟩ : syracuseStep 979091 = 1468637) B1468637
theorem B651449 : Blo 432776 651449 := bstep (se 2 (by rfl) ⟨244293, by rfl⟩ : syracuseStep 651449 = 488587) B488587
theorem B725177 : Blo 432776 725177 := bstep (se 2 (by rfl) ⟨271941, by rfl⟩ : syracuseStep 725177 = 543883) B543883
theorem B979145 : Blo 432776 979145 := bstep (se 2 (by rfl) ⟨367179, by rfl⟩ : syracuseStep 979145 = 734359) B734359
theorem B1102025 : Blo 432776 1102025 := bstep (se 2 (by rfl) ⟨413259, by rfl⟩ : syracuseStep 1102025 = 826519) B826519
theorem B1765577 : Blo 432776 1765577 := bstep (se 2 (by rfl) ⟨662091, by rfl⟩ : syracuseStep 1765577 = 1324183) B1324183
theorem B487687 : Blo 432776 487687 := bstep (se 1 (by rfl) ⟨365765, by rfl⟩ : syracuseStep 487687 = 731531) B731531
theorem B651527 : Blo 432776 651527 := bstep (se 1 (by rfl) ⟨488645, by rfl⟩ : syracuseStep 651527 = 977291) B977291
theorem B651563 : Blo 432776 651563 := bstep (se 1 (by rfl) ⟨488672, by rfl⟩ : syracuseStep 651563 = 977345) B977345
theorem B1986875 : Blo 432776 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B651593 : Blo 432776 651593 := bstep (se 2 (by rfl) ⟨244347, by rfl⟩ : syracuseStep 651593 = 488695) B488695
theorem B1462643 : Blo 432776 1462643 := bstep (se 1 (by rfl) ⟨1096982, by rfl⟩ : syracuseStep 1462643 = 2193965) B2193965
theorem B618887 : Blo 432776 618887 := bstep (se 1 (by rfl) ⟨464165, by rfl⟩ : syracuseStep 618887 = 928331) B928331
theorem B2961809 : Blo 432776 2961809 := bstep (se 2 (by rfl) ⟨1110678, by rfl⟩ : syracuseStep 2961809 = 2221357) B2221357
theorem B487867 : Blo 432776 487867 := bstep (se 1 (by rfl) ⟨365900, by rfl⟩ : syracuseStep 487867 = 731801) B731801
theorem B651707 : Blo 432776 651707 := bstep (se 1 (by rfl) ⟨488780, by rfl⟩ : syracuseStep 651707 = 977561) B977561
theorem B3387869 : Blo 432776 3387869 := bstep (se 3 (by rfl) ⟨635225, by rfl⟩ : syracuseStep 3387869 = 1270451) B1270451
theorem B651767 : Blo 432776 651767 := bstep (se 1 (by rfl) ⟨488825, by rfl⟩ : syracuseStep 651767 = 977651) B977651
theorem B520711 : Blo 432776 520711 := bstep (se 1 (by rfl) ⟨390533, by rfl⟩ : syracuseStep 520711 = 781067) B781067
theorem B463367 : Blo 432776 463367 := bstep (se 1 (by rfl) ⟨347525, by rfl⟩ : syracuseStep 463367 = 695051) B695051
theorem B528911 : Blo 432776 528911 := bstep (se 1 (by rfl) ⟨396683, by rfl⟩ : syracuseStep 528911 = 793367) B793367
theorem B651791 : Blo 432776 651791 := bstep (se 1 (by rfl) ⟨488843, by rfl⟩ : syracuseStep 651791 = 977687) B977687
theorem B733711 : Blo 432776 733711 := bstep (se 1 (by rfl) ⟨550283, by rfl⟩ : syracuseStep 733711 = 1100567) B1100567
theorem B1102369 : Blo 432776 1102369 := bstep (se 2 (by rfl) ⟨413388, by rfl⟩ : syracuseStep 1102369 = 826777) B826777
theorem B651833 : Blo 432776 651833 := bstep (se 2 (by rfl) ⟨244437, by rfl⟩ : syracuseStep 651833 = 488875) B488875
theorem B651911 : Blo 432776 651911 := bstep (se 1 (by rfl) ⟨488933, by rfl⟩ : syracuseStep 651911 = 977867) B977867
theorem B651947 : Blo 432776 651947 := bstep (se 1 (by rfl) ⟨488960, by rfl⟩ : syracuseStep 651947 = 977921) B977921
theorem B783049 : Blo 432776 783049 := bstep (se 2 (by rfl) ⟨293643, by rfl⟩ : syracuseStep 783049 = 587287) B587287
theorem B651977 : Blo 432776 651977 := bstep (se 2 (by rfl) ⟨244491, by rfl⟩ : syracuseStep 651977 = 488983) B488983
theorem B1004321 : Blo 432776 1004321 := bstep (se 2 (by rfl) ⟨376620, by rfl⟩ : syracuseStep 1004321 = 753241) B753241
theorem B652091 : Blo 432776 652091 := bstep (se 1 (by rfl) ⟨489068, by rfl⟩ : syracuseStep 652091 = 978137) B978137
theorem B3715955 : Blo 432776 3715955 := bstep (se 1 (by rfl) ⟨2786966, by rfl⟩ : syracuseStep 3715955 = 5573933) B5573933
theorem B652151 : Blo 432776 652151 := bstep (se 1 (by rfl) ⟨489113, by rfl⟩ : syracuseStep 652151 = 978227) B978227
theorem B979847 : Blo 432776 979847 := bstep (se 1 (by rfl) ⟨734885, by rfl⟩ : syracuseStep 979847 = 1469771) B1469771
theorem B488335 : Blo 432776 488335 := bstep (se 1 (by rfl) ⟨366251, by rfl⟩ : syracuseStep 488335 = 732503) B732503
theorem B652175 : Blo 432776 652175 := bstep (se 1 (by rfl) ⟨489131, by rfl⟩ : syracuseStep 652175 = 978263) B978263
theorem B4182947 : Blo 432776 4182947 := bstep (se 1 (by rfl) ⟨3137210, by rfl⟩ : syracuseStep 4182947 = 6274421) B6274421
theorem B824249 : Blo 432776 824249 := bstep (se 2 (by rfl) ⟨309093, by rfl⟩ : syracuseStep 824249 = 618187) B618187
theorem B652217 : Blo 432776 652217 := bstep (se 2 (by rfl) ⟨244581, by rfl⟩ : syracuseStep 652217 = 489163) B489163
theorem B627643 : Blo 432776 627643 := bstep (se 1 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 627643 = 941465) B941465
theorem B652295 : Blo 432776 652295 := bstep (se 1 (by rfl) ⟨489221, by rfl⟩ : syracuseStep 652295 = 978443) B978443
theorem B652331 : Blo 432776 652331 := bstep (se 1 (by rfl) ⟨489248, by rfl⟩ : syracuseStep 652331 = 978497) B978497
theorem B734251 : Blo 432776 734251 := bstep (se 1 (by rfl) ⟨550688, by rfl⟩ : syracuseStep 734251 = 1101377) B1101377
theorem B980027 : Blo 432776 980027 := bstep (se 1 (by rfl) ⟨735020, by rfl⟩ : syracuseStep 980027 = 1470041) B1470041
theorem B652361 : Blo 432776 652361 := bstep (se 2 (by rfl) ⟨244635, by rfl⟩ : syracuseStep 652361 = 489271) B489271
theorem B1102967 : Blo 432776 1102967 := bstep (se 1 (by rfl) ⟨827225, by rfl⟩ : syracuseStep 1102967 = 1654451) B1654451
theorem B734393 : Blo 432776 734393 := bstep (se 2 (by rfl) ⟨275397, by rfl⟩ : syracuseStep 734393 = 550795) B550795
theorem B980153 : Blo 432776 980153 := bstep (se 2 (by rfl) ⟨367557, by rfl⟩ : syracuseStep 980153 = 735115) B735115
theorem B652475 : Blo 432776 652475 := bstep (se 1 (by rfl) ⟨489356, by rfl⟩ : syracuseStep 652475 = 978713) B978713
theorem B2200769 : Blo 432776 2200769 := bstep (se 2 (by rfl) ⟨825288, by rfl⟩ : syracuseStep 2200769 = 1650577) B1650577
theorem B1561801 : Blo 432776 1561801 := bstep (se 2 (by rfl) ⟨585675, by rfl⟩ : syracuseStep 1561801 = 1171351) B1171351
theorem B652535 : Blo 432776 652535 := bstep (se 1 (by rfl) ⟨489401, by rfl⟩ : syracuseStep 652535 = 978803) B978803
theorem B1234187 : Blo 432776 1234187 := bstep (se 1 (by rfl) ⟨925640, by rfl⟩ : syracuseStep 1234187 = 1851281) B1851281
theorem B652559 : Blo 432776 652559 := bstep (se 1 (by rfl) ⟨489419, by rfl⟩ : syracuseStep 652559 = 978839) B978839
theorem B2471219 : Blo 432776 2471219 := bstep (se 1 (by rfl) ⟨1853414, by rfl⟩ : syracuseStep 2471219 = 3706829) B3706829
theorem B652601 : Blo 432776 652601 := bstep (se 2 (by rfl) ⟨244725, by rfl⟩ : syracuseStep 652601 = 489451) B489451
theorem B488839 : Blo 432776 488839 := bstep (se 1 (by rfl) ⟨366629, by rfl⟩ : syracuseStep 488839 = 733259) B733259
theorem B652679 : Blo 432776 652679 := bstep (se 1 (by rfl) ⟨489509, by rfl⟩ : syracuseStep 652679 = 979019) B979019
theorem B652715 : Blo 432776 652715 := bstep (se 1 (by rfl) ⟨489536, by rfl⟩ : syracuseStep 652715 = 979073) B979073
theorem B652745 : Blo 432776 652745 := bstep (se 2 (by rfl) ⟨244779, by rfl⟩ : syracuseStep 652745 = 489559) B489559
theorem B2119115 : Blo 432776 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B693775 : Blo 432776 693775 := bstep (se 1 (by rfl) ⟨520331, by rfl⟩ : syracuseStep 693775 = 1040663) B1040663
theorem B980495 : Blo 432776 980495 := bstep (se 1 (by rfl) ⟨735371, by rfl⟩ : syracuseStep 980495 = 1470743) B1470743
theorem B3135019 : Blo 432776 3135019 := bstep (se 1 (by rfl) ⟨2351264, by rfl⟩ : syracuseStep 3135019 = 4702529) B4702529
theorem B489019 : Blo 432776 489019 := bstep (se 1 (by rfl) ⟨366764, by rfl⟩ : syracuseStep 489019 = 733529) B733529
theorem B652859 : Blo 432776 652859 := bstep (se 1 (by rfl) ⟨489644, by rfl⟩ : syracuseStep 652859 = 979289) B979289
theorem B2635325 : Blo 432776 2635325 := bstep (se 3 (by rfl) ⟨494123, by rfl⟩ : syracuseStep 2635325 = 988247) B988247
theorem B652919 : Blo 432776 652919 := bstep (se 1 (by rfl) ⟨489689, by rfl⟩ : syracuseStep 652919 = 979379) B979379
theorem B652943 : Blo 432776 652943 := bstep (se 1 (by rfl) ⟨489707, by rfl⟩ : syracuseStep 652943 = 979415) B979415
theorem B587449 : Blo 432776 587449 := bstep (se 2 (by rfl) ⟨220293, by rfl⟩ : syracuseStep 587449 = 440587) B440587
theorem B652985 : Blo 432776 652985 := bstep (se 2 (by rfl) ⟨244869, by rfl⟩ : syracuseStep 652985 = 489739) B489739
theorem B784073 : Blo 432776 784073 := bstep (se 2 (by rfl) ⟨294027, by rfl⟩ : syracuseStep 784073 = 588055) B588055
theorem B6674177 : Blo 432776 6674177 := bstep (se 2 (by rfl) ⟨2502816, by rfl⟩ : syracuseStep 6674177 = 5005633) B5005633
theorem B653063 : Blo 432776 653063 := bstep (se 1 (by rfl) ⟨489797, by rfl⟩ : syracuseStep 653063 = 979595) B979595
theorem B653099 : Blo 432776 653099 := bstep (se 1 (by rfl) ⟨489824, by rfl⟩ : syracuseStep 653099 = 979649) B979649
theorem B620345 : Blo 432776 620345 := bstep (se 2 (by rfl) ⟨232629, by rfl⟩ : syracuseStep 620345 = 465259) B465259
theorem B653129 : Blo 432776 653129 := bstep (se 2 (by rfl) ⟨244923, by rfl⟩ : syracuseStep 653129 = 489847) B489847
theorem B735095 : Blo 432776 735095 := bstep (se 1 (by rfl) ⟨551321, by rfl⟩ : syracuseStep 735095 = 1102643) B1102643
theorem B1234835 : Blo 432776 1234835 := bstep (se 1 (by rfl) ⟨926126, by rfl⟩ : syracuseStep 1234835 = 1852253) B1852253
theorem B653243 : Blo 432776 653243 := bstep (se 1 (by rfl) ⟨489932, by rfl⟩ : syracuseStep 653243 = 979865) B979865
theorem B653303 : Blo 432776 653303 := bstep (se 1 (by rfl) ⟨489977, by rfl⟩ : syracuseStep 653303 = 979955) B979955
theorem B86751245 : Blo 432776 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B489487 : Blo 432776 489487 := bstep (se 1 (by rfl) ⟨367115, by rfl⟩ : syracuseStep 489487 = 734231) B734231
theorem B653327 : Blo 432776 653327 := bstep (se 1 (by rfl) ⟨489995, by rfl⟩ : syracuseStep 653327 = 979991) B979991
theorem B1185835 : Blo 432776 1185835 := bstep (se 1 (by rfl) ⟨889376, by rfl⟩ : syracuseStep 1185835 = 1778753) B1778753
theorem B653369 : Blo 432776 653369 := bstep (se 2 (by rfl) ⟨245013, by rfl⟩ : syracuseStep 653369 = 490027) B490027
theorem B825403 : Blo 432776 825403 := bstep (se 1 (by rfl) ⟨619052, by rfl⟩ : syracuseStep 825403 = 1238105) B1238105
theorem B1325117 : Blo 432776 1325117 := bstep (se 3 (by rfl) ⟨248459, by rfl⟩ : syracuseStep 1325117 = 496919) B496919
theorem B1235063 : Blo 432776 1235063 := bstep (se 1 (by rfl) ⟨926297, by rfl⟩ : syracuseStep 1235063 = 1852595) B1852595
theorem B4028549 : Blo 432776 4028549 := bstep (se 4 (by rfl) ⟨377676, by rfl⟩ : syracuseStep 4028549 = 755353) B755353
theorem B653447 : Blo 432776 653447 := bstep (se 1 (by rfl) ⟨490085, by rfl⟩ : syracuseStep 653447 = 980171) B980171
theorem B653483 : Blo 432776 653483 := bstep (se 1 (by rfl) ⟨490112, by rfl⟩ : syracuseStep 653483 = 980225) B980225
theorem B1185977 : Blo 432776 1185977 := bstep (se 2 (by rfl) ⟨444741, by rfl⟩ : syracuseStep 1185977 = 889483) B889483
theorem B1644745 : Blo 432776 1644745 := bstep (se 2 (by rfl) ⟨616779, by rfl⟩ : syracuseStep 1644745 = 1233559) B1233559
theorem B653513 : Blo 432776 653513 := bstep (se 2 (by rfl) ⟨245067, by rfl⟩ : syracuseStep 653513 = 490135) B490135
theorem B1652993 : Blo 432776 1652993 := bstep (se 2 (by rfl) ⟨619872, by rfl⟩ : syracuseStep 1652993 = 1239745) B1239745
theorem B1653007 : Blo 432776 1653007 := bstep (se 1 (by rfl) ⟨1239755, by rfl⟩ : syracuseStep 1653007 = 2479511) B2479511
theorem B1718561 : Blo 432776 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B653627 : Blo 432776 653627 := bstep (se 1 (by rfl) ⟨490220, by rfl⟩ : syracuseStep 653627 = 980441) B980441
theorem B1096051 : Blo 432776 1096051 := bstep (se 1 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 1096051 = 1644077) B1644077
theorem B1030553 : Blo 432776 1030553 := bstep (se 2 (by rfl) ⟨386457, by rfl⟩ : syracuseStep 1030553 = 772915) B772915
theorem B2202065 : Blo 432776 2202065 := bstep (se 2 (by rfl) ⟨825774, by rfl⟩ : syracuseStep 2202065 = 1651549) B1651549
theorem B1096193 : Blo 432776 1096193 := bstep (se 2 (by rfl) ⟨411072, by rfl⟩ : syracuseStep 1096193 = 822145) B822145
theorem B489991 : Blo 432776 489991 := bstep (se 1 (by rfl) ⟨367493, by rfl⟩ : syracuseStep 489991 = 734987) B734987
theorem B2480651 : Blo 432776 2480651 := bstep (se 1 (by rfl) ⟨1860488, by rfl⟩ : syracuseStep 2480651 = 3720977) B3720977
theorem B2406935 : Blo 432776 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B3291677 : Blo 432776 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B825889 : Blo 432776 825889 := bstep (se 2 (by rfl) ⟨309708, by rfl⟩ : syracuseStep 825889 = 619417) B619417
theorem B522811 : Blo 432776 522811 := bstep (se 1 (by rfl) ⟨392108, by rfl⟩ : syracuseStep 522811 = 784217) B784217
theorem B1391165 : Blo 432776 1391165 := bstep (se 3 (by rfl) ⟨260843, by rfl⟩ : syracuseStep 1391165 = 521687) B521687
theorem B432783 : Blo 432776 432783 := bstep (se 1 (by rfl) ⟨324587, by rfl⟩ : syracuseStep 432783 = 649175) B649175
theorem B432827 : Blo 432776 432827 := bstep (se 1 (by rfl) ⟨324620, by rfl⟩ : syracuseStep 432827 = 649241) B649241
theorem B490171 : Blo 432776 490171 := bstep (se 1 (by rfl) ⟨367628, by rfl⟩ : syracuseStep 490171 = 735257) B735257
theorem B13368025 : Blo 432776 13368025 := bstep (se 2 (by rfl) ⟨5013009, by rfl⟩ : syracuseStep 13368025 = 10026019) B10026019
theorem B2472677 : Blo 432776 2472677 := bstep (se 4 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 2472677 = 463627) B463627
theorem B432903 : Blo 432776 432903 := bstep (se 1 (by rfl) ⟨324677, by rfl⟩ : syracuseStep 432903 = 649355) B649355
theorem B432911 : Blo 432776 432911 := bstep (se 1 (by rfl) ⟨324683, by rfl⟩ : syracuseStep 432911 = 649367) B649367
theorem B1981217 : Blo 432776 1981217 := bstep (se 2 (by rfl) ⟨742956, by rfl⟩ : syracuseStep 1981217 = 1485913) B1485913
theorem B8338211 : Blo 432776 8338211 := bstep (se 1 (by rfl) ⟨6253658, by rfl⟩ : syracuseStep 8338211 = 12507317) B12507317
theorem B432955 : Blo 432776 432955 := bstep (se 1 (by rfl) ⟨324716, by rfl⟩ : syracuseStep 432955 = 649433) B649433
theorem B1522547 : Blo 432776 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B695159 : Blo 432776 695159 := bstep (se 1 (by rfl) ⟨521369, by rfl⟩ : syracuseStep 695159 = 1042739) B1042739
theorem B744311 : Blo 432776 744311 := bstep (se 1 (by rfl) ⟨558233, by rfl⟩ : syracuseStep 744311 = 1116467) B1116467
theorem B433031 : Blo 432776 433031 := bstep (se 1 (by rfl) ⟨324773, by rfl⟩ : syracuseStep 433031 = 649547) B649547
theorem B433039 : Blo 432776 433039 := bstep (se 1 (by rfl) ⟨324779, by rfl⟩ : syracuseStep 433039 = 649559) B649559
theorem B1465235 : Blo 432776 1465235 := bstep (se 1 (by rfl) ⟨1098926, by rfl⟩ : syracuseStep 1465235 = 2197853) B2197853
theorem B3562393 : Blo 432776 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B2177945 : Blo 432776 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B2341817 : Blo 432776 2341817 := bstep (se 2 (by rfl) ⟨878181, by rfl⟩ : syracuseStep 2341817 = 1756363) B1756363
theorem B433083 : Blo 432776 433083 := bstep (se 1 (by rfl) ⟨324812, by rfl⟩ : syracuseStep 433083 = 649625) B649625
theorem B1096649 : Blo 432776 1096649 := bstep (se 2 (by rfl) ⟨411243, by rfl⟩ : syracuseStep 1096649 = 822487) B822487
theorem B433159 : Blo 432776 433159 := bstep (se 1 (by rfl) ⟨324869, by rfl⟩ : syracuseStep 433159 = 649739) B649739
theorem B3701771 : Blo 432776 3701771 := bstep (se 1 (by rfl) ⟨2776328, by rfl⟩ : syracuseStep 3701771 = 5552657) B5552657
theorem B433167 : Blo 432776 433167 := bstep (se 1 (by rfl) ⟨324875, by rfl⟩ : syracuseStep 433167 = 649751) B649751
theorem B3333143 : Blo 432776 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B433211 : Blo 432776 433211 := bstep (se 1 (by rfl) ⟨324908, by rfl⟩ : syracuseStep 433211 = 649817) B649817
theorem B14851133 : Blo 432776 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B973943 : Blo 432776 973943 := bstep (se 1 (by rfl) ⟨730457, by rfl⟩ : syracuseStep 973943 = 1460915) B1460915
theorem B547975 : Blo 432776 547975 := bstep (se 1 (by rfl) ⟨410981, by rfl⟩ : syracuseStep 547975 = 821963) B821963
theorem B433287 : Blo 432776 433287 := bstep (se 1 (by rfl) ⟨324965, by rfl⟩ : syracuseStep 433287 = 649931) B649931
theorem B433295 : Blo 432776 433295 := bstep (se 1 (by rfl) ⟨324971, by rfl⟩ : syracuseStep 433295 = 649943) B649943
theorem B433339 : Blo 432776 433339 := bstep (se 1 (by rfl) ⟨325004, by rfl⟩ : syracuseStep 433339 = 650009) B650009
theorem B433415 : Blo 432776 433415 := bstep (se 1 (by rfl) ⟨325061, by rfl⟩ : syracuseStep 433415 = 650123) B650123
theorem B433423 : Blo 432776 433423 := bstep (se 1 (by rfl) ⟨325067, by rfl⟩ : syracuseStep 433423 = 650135) B650135
theorem B974123 : Blo 432776 974123 := bstep (se 1 (by rfl) ⟨730592, by rfl⟩ : syracuseStep 974123 = 1461185) B1461185
theorem B1097003 : Blo 432776 1097003 := bstep (se 1 (by rfl) ⟨822752, by rfl⟩ : syracuseStep 1097003 = 1645505) B1645505
theorem B433467 : Blo 432776 433467 := bstep (se 1 (by rfl) ⟨325100, by rfl⟩ : syracuseStep 433467 = 650201) B650201
theorem B2465113 : Blo 432776 2465113 := bstep (se 2 (by rfl) ⟨924417, by rfl⟩ : syracuseStep 2465113 = 1848835) B1848835
theorem B695671 : Blo 432776 695671 := bstep (se 1 (by rfl) ⟨521753, by rfl⟩ : syracuseStep 695671 = 1043507) B1043507
theorem B10132867 : Blo 432776 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B433543 : Blo 432776 433543 := bstep (se 1 (by rfl) ⟨325157, by rfl⟩ : syracuseStep 433543 = 650315) B650315
theorem B433551 : Blo 432776 433551 := bstep (se 1 (by rfl) ⟨325163, by rfl⟩ : syracuseStep 433551 = 650327) B650327
theorem B2473361 : Blo 432776 2473361 := bstep (se 2 (by rfl) ⟨927510, by rfl⟩ : syracuseStep 2473361 = 1855021) B1855021
theorem B433595 : Blo 432776 433595 := bstep (se 1 (by rfl) ⟨325196, by rfl⟩ : syracuseStep 433595 = 650393) B650393
theorem B3120605 : Blo 432776 3120605 := bstep (se 3 (by rfl) ⟨585113, by rfl⟩ : syracuseStep 3120605 = 1170227) B1170227
theorem B433671 : Blo 432776 433671 := bstep (se 1 (by rfl) ⟨325253, by rfl⟩ : syracuseStep 433671 = 650507) B650507
theorem B1654283 : Blo 432776 1654283 := bstep (se 1 (by rfl) ⟨1240712, by rfl⟩ : syracuseStep 1654283 = 2481425) B2481425
theorem B433679 : Blo 432776 433679 := bstep (se 1 (by rfl) ⟨325259, by rfl⟩ : syracuseStep 433679 = 650519) B650519
theorem B433723 : Blo 432776 433723 := bstep (se 1 (by rfl) ⟨325292, by rfl⟩ : syracuseStep 433723 = 650585) B650585
theorem B548471 : Blo 432776 548471 := bstep (se 1 (by rfl) ⟨411353, by rfl⟩ : syracuseStep 548471 = 822707) B822707
theorem B433799 : Blo 432776 433799 := bstep (se 1 (by rfl) ⟨325349, by rfl⟩ : syracuseStep 433799 = 650699) B650699
theorem B433807 : Blo 432776 433807 := bstep (se 1 (by rfl) ⟨325355, by rfl⟩ : syracuseStep 433807 = 650711) B650711
theorem B974483 : Blo 432776 974483 := bstep (se 1 (by rfl) ⟨730862, by rfl⟩ : syracuseStep 974483 = 1461725) B1461725
theorem B2637485 : Blo 432776 2637485 := bstep (se 3 (by rfl) ⟨494528, by rfl⟩ : syracuseStep 2637485 = 989057) B989057
theorem B433851 : Blo 432776 433851 := bstep (se 1 (by rfl) ⟨325388, by rfl⟩ : syracuseStep 433851 = 650777) B650777
theorem B974537 : Blo 432776 974537 := bstep (se 2 (by rfl) ⟨365451, by rfl⟩ : syracuseStep 974537 = 730903) B730903
theorem B827081 : Blo 432776 827081 := bstep (se 2 (by rfl) ⟨310155, by rfl⟩ : syracuseStep 827081 = 620311) B620311
theorem B433927 : Blo 432776 433927 := bstep (se 1 (by rfl) ⟨325445, by rfl⟩ : syracuseStep 433927 = 650891) B650891
theorem B548623 : Blo 432776 548623 := bstep (se 1 (by rfl) ⟨411467, by rfl⟩ : syracuseStep 548623 = 822935) B822935
theorem B433935 : Blo 432776 433935 := bstep (se 1 (by rfl) ⟨325451, by rfl⟩ : syracuseStep 433935 = 650903) B650903
theorem B3129137 : Blo 432776 3129137 := bstep (se 2 (by rfl) ⟨1173426, by rfl⟩ : syracuseStep 3129137 = 2346853) B2346853
theorem B433979 : Blo 432776 433979 := bstep (se 1 (by rfl) ⟨325484, by rfl⟩ : syracuseStep 433979 = 650969) B650969
theorem B2637683 : Blo 432776 2637683 := bstep (se 1 (by rfl) ⟨1978262, by rfl⟩ : syracuseStep 2637683 = 3956525) B3956525
theorem B434055 : Blo 432776 434055 := bstep (se 1 (by rfl) ⟨325541, by rfl⟩ : syracuseStep 434055 = 651083) B651083
theorem B434063 : Blo 432776 434063 := bstep (se 1 (by rfl) ⟨325547, by rfl⟩ : syracuseStep 434063 = 651095) B651095
theorem B5627801 : Blo 432776 5627801 := bstep (se 2 (by rfl) ⟨2110425, by rfl⟩ : syracuseStep 5627801 = 4220851) B4220851
theorem B548795 : Blo 432776 548795 := bstep (se 1 (by rfl) ⟨411596, by rfl⟩ : syracuseStep 548795 = 823193) B823193
theorem B434107 : Blo 432776 434107 := bstep (se 1 (by rfl) ⟨325580, by rfl⟩ : syracuseStep 434107 = 651161) B651161
theorem B1466369 : Blo 432776 1466369 := bstep (se 2 (by rfl) ⟨549888, by rfl⟩ : syracuseStep 1466369 = 1099777) B1099777
theorem B2777125 : Blo 432776 2777125 := bstep (se 4 (by rfl) ⟨260355, by rfl⟩ : syracuseStep 2777125 = 520711) B520711
theorem B434215 : Blo 432776 434215 := bstep (se 1 (by rfl) ⟨325661, by rfl⟩ : syracuseStep 434215 = 651323) B651323
theorem B1581113 : Blo 432776 1581113 := bstep (se 2 (by rfl) ⟨592917, by rfl⟩ : syracuseStep 1581113 = 1185835) B1185835
theorem B434255 : Blo 432776 434255 := bstep (se 1 (by rfl) ⟨325691, by rfl⟩ : syracuseStep 434255 = 651383) B651383
theorem B434271 : Blo 432776 434271 := bstep (se 1 (by rfl) ⟨325703, by rfl⟩ : syracuseStep 434271 = 651407) B651407
theorem B434299 : Blo 432776 434299 := bstep (se 1 (by rfl) ⟨325724, by rfl⟩ : syracuseStep 434299 = 651449) B651449
theorem B483451 : Blo 432776 483451 := bstep (se 1 (by rfl) ⟨362588, by rfl⟩ : syracuseStep 483451 = 725177) B725177
theorem B434351 : Blo 432776 434351 := bstep (se 1 (by rfl) ⟨325763, by rfl⟩ : syracuseStep 434351 = 651527) B651527
theorem B434375 : Blo 432776 434375 := bstep (se 1 (by rfl) ⟨325781, by rfl⟩ : syracuseStep 434375 = 651563) B651563
theorem B434395 : Blo 432776 434395 := bstep (se 1 (by rfl) ⟨325796, by rfl⟩ : syracuseStep 434395 = 651593) B651593
theorem B975095 : Blo 432776 975095 := bstep (se 1 (by rfl) ⟨731321, by rfl⟩ : syracuseStep 975095 = 1462643) B1462643
theorem B1097975 : Blo 432776 1097975 := bstep (se 1 (by rfl) ⟨823481, by rfl⟩ : syracuseStep 1097975 = 1646963) B1646963
theorem B1974539 : Blo 432776 1974539 := bstep (se 1 (by rfl) ⟨1480904, by rfl⟩ : syracuseStep 1974539 = 2961809) B2961809
theorem B434471 : Blo 432776 434471 := bstep (se 1 (by rfl) ⟨325853, by rfl⟩ : syracuseStep 434471 = 651707) B651707
theorem B434511 : Blo 432776 434511 := bstep (se 1 (by rfl) ⟨325883, by rfl⟩ : syracuseStep 434511 = 651767) B651767
theorem B434527 : Blo 432776 434527 := bstep (se 1 (by rfl) ⟨325895, by rfl⟩ : syracuseStep 434527 = 651791) B651791
theorem B2204009 : Blo 432776 2204009 := bstep (se 2 (by rfl) ⟨826503, by rfl⟩ : syracuseStep 2204009 = 1653007) B1653007
theorem B434555 : Blo 432776 434555 := bstep (se 1 (by rfl) ⟨325916, by rfl⟩ : syracuseStep 434555 = 651833) B651833
theorem B434607 : Blo 432776 434607 := bstep (se 1 (by rfl) ⟨325955, by rfl⟩ : syracuseStep 434607 = 651911) B651911
theorem B434631 : Blo 432776 434631 := bstep (se 1 (by rfl) ⟨325973, by rfl⟩ : syracuseStep 434631 = 651947) B651947
theorem B3129803 : Blo 432776 3129803 := bstep (se 1 (by rfl) ⟨2347352, by rfl⟩ : syracuseStep 3129803 = 4694705) B4694705
theorem B434651 : Blo 432776 434651 := bstep (se 1 (by rfl) ⟨325988, by rfl⟩ : syracuseStep 434651 = 651977) B651977
theorem B9372185 : Blo 432776 9372185 := bstep (se 2 (by rfl) ⟨3514569, by rfl⟩ : syracuseStep 9372185 = 7029139) B7029139
theorem B22921751 : Blo 432776 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B836135 : Blo 432776 836135 := bstep (se 1 (by rfl) ⟨627101, by rfl⟩ : syracuseStep 836135 = 1254203) B1254203
theorem B434727 : Blo 432776 434727 := bstep (se 1 (by rfl) ⟨326045, by rfl⟩ : syracuseStep 434727 = 652091) B652091
theorem B434767 : Blo 432776 434767 := bstep (se 1 (by rfl) ⟨326075, by rfl⟩ : syracuseStep 434767 = 652151) B652151
theorem B434783 : Blo 432776 434783 := bstep (se 1 (by rfl) ⟨326087, by rfl⟩ : syracuseStep 434783 = 652175) B652175
theorem B549499 : Blo 432776 549499 := bstep (se 1 (by rfl) ⟨412124, by rfl⟩ : syracuseStep 549499 = 824249) B824249
theorem B434811 : Blo 432776 434811 := bstep (se 1 (by rfl) ⟨326108, by rfl⟩ : syracuseStep 434811 = 652217) B652217
theorem B434863 : Blo 432776 434863 := bstep (se 1 (by rfl) ⟨326147, by rfl⟩ : syracuseStep 434863 = 652295) B652295
theorem B434887 : Blo 432776 434887 := bstep (se 1 (by rfl) ⟨326165, by rfl⟩ : syracuseStep 434887 = 652331) B652331
theorem B434907 : Blo 432776 434907 := bstep (se 1 (by rfl) ⟨326180, by rfl⟩ : syracuseStep 434907 = 652361) B652361
theorem B697081 : Blo 432776 697081 := bstep (se 2 (by rfl) ⟨261405, by rfl⟩ : syracuseStep 697081 = 522811) B522811
theorem B434983 : Blo 432776 434983 := bstep (se 1 (by rfl) ⟨326237, by rfl⟩ : syracuseStep 434983 = 652475) B652475
theorem B1467179 : Blo 432776 1467179 := bstep (se 1 (by rfl) ⟨1100384, by rfl⟩ : syracuseStep 1467179 = 2200769) B2200769
theorem B975689 : Blo 432776 975689 := bstep (se 2 (by rfl) ⟨365883, by rfl⟩ : syracuseStep 975689 = 731767) B731767
theorem B435023 : Blo 432776 435023 := bstep (se 1 (by rfl) ⟨326267, by rfl⟩ : syracuseStep 435023 = 652535) B652535
theorem B435039 : Blo 432776 435039 := bstep (se 1 (by rfl) ⟨326279, by rfl⟩ : syracuseStep 435039 = 652559) B652559
theorem B1131371 : Blo 432776 1131371 := bstep (se 1 (by rfl) ⟨848528, by rfl⟩ : syracuseStep 1131371 = 1697057) B1697057
theorem B1647479 : Blo 432776 1647479 := bstep (se 1 (by rfl) ⟨1235609, by rfl⟩ : syracuseStep 1647479 = 2471219) B2471219
theorem B435067 : Blo 432776 435067 := bstep (se 1 (by rfl) ⟨326300, by rfl⟩ : syracuseStep 435067 = 652601) B652601
theorem B435119 : Blo 432776 435119 := bstep (se 1 (by rfl) ⟨326339, by rfl⟩ : syracuseStep 435119 = 652679) B652679
theorem B1115063 : Blo 432776 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B435143 : Blo 432776 435143 := bstep (se 1 (by rfl) ⟨326357, by rfl⟩ : syracuseStep 435143 = 652715) B652715
theorem B435163 : Blo 432776 435163 := bstep (se 1 (by rfl) ⟨326372, by rfl⟩ : syracuseStep 435163 = 652745) B652745
theorem B435239 : Blo 432776 435239 := bstep (se 1 (by rfl) ⟨326429, by rfl⟩ : syracuseStep 435239 = 652859) B652859
theorem B1467449 : Blo 432776 1467449 := bstep (se 2 (by rfl) ⟨550293, by rfl⟩ : syracuseStep 1467449 = 1100587) B1100587
theorem B435279 : Blo 432776 435279 := bstep (se 1 (by rfl) ⟨326459, by rfl⟩ : syracuseStep 435279 = 652919) B652919
theorem B435295 : Blo 432776 435295 := bstep (se 1 (by rfl) ⟨326471, by rfl⟩ : syracuseStep 435295 = 652943) B652943
theorem B435323 : Blo 432776 435323 := bstep (se 1 (by rfl) ⟨326492, by rfl⟩ : syracuseStep 435323 = 652985) B652985
theorem B4449451 : Blo 432776 4449451 := bstep (se 1 (by rfl) ⟨3337088, by rfl⟩ : syracuseStep 4449451 = 6674177) B6674177
theorem B435375 : Blo 432776 435375 := bstep (se 1 (by rfl) ⟨326531, by rfl⟩ : syracuseStep 435375 = 653063) B653063
theorem B435399 : Blo 432776 435399 := bstep (se 1 (by rfl) ⟨326549, by rfl⟩ : syracuseStep 435399 = 653099) B653099
theorem B435419 : Blo 432776 435419 := bstep (se 1 (by rfl) ⟨326564, by rfl⟩ : syracuseStep 435419 = 653129) B653129
theorem B877817 : Blo 432776 877817 := bstep (se 2 (by rfl) ⟨329181, by rfl⟩ : syracuseStep 877817 = 658363) B658363
theorem B836857 : Blo 432776 836857 := bstep (se 2 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 836857 = 627643) B627643
theorem B435495 : Blo 432776 435495 := bstep (se 1 (by rfl) ⟨326621, by rfl⟩ : syracuseStep 435495 = 653243) B653243
theorem B435535 : Blo 432776 435535 := bstep (se 1 (by rfl) ⟨326651, by rfl⟩ : syracuseStep 435535 = 653303) B653303
theorem B435551 : Blo 432776 435551 := bstep (se 1 (by rfl) ⟨326663, by rfl⟩ : syracuseStep 435551 = 653327) B653327
theorem B435579 : Blo 432776 435579 := bstep (se 1 (by rfl) ⟨326684, by rfl⟩ : syracuseStep 435579 = 653369) B653369
theorem B1467773 : Blo 432776 1467773 := bstep (se 3 (by rfl) ⟨275207, by rfl⟩ : syracuseStep 1467773 = 550415) B550415
theorem B435631 : Blo 432776 435631 := bstep (se 1 (by rfl) ⟨326723, by rfl⟩ : syracuseStep 435631 = 653447) B653447
theorem B435655 : Blo 432776 435655 := bstep (se 1 (by rfl) ⟨326741, by rfl⟩ : syracuseStep 435655 = 653483) B653483
theorem B435675 : Blo 432776 435675 := bstep (se 1 (by rfl) ⟨326756, by rfl⟩ : syracuseStep 435675 = 653513) B653513
theorem B730633 : Blo 432776 730633 := bstep (se 2 (by rfl) ⟨273987, by rfl⟩ : syracuseStep 730633 = 547975) B547975
theorem B6268421 : Blo 432776 6268421 := bstep (se 4 (by rfl) ⟨587664, by rfl⟩ : syracuseStep 6268421 = 1175329) B1175329
theorem B435751 : Blo 432776 435751 := bstep (se 1 (by rfl) ⟨326813, by rfl⟩ : syracuseStep 435751 = 653627) B653627
theorem B2082401 : Blo 432776 2082401 := bstep (se 2 (by rfl) ⟨780900, by rfl⟩ : syracuseStep 2082401 = 1561801) B1561801
theorem B976481 : Blo 432776 976481 := bstep (se 2 (by rfl) ⟨366180, by rfl⟩ : syracuseStep 976481 = 732361) B732361
theorem B1099403 : Blo 432776 1099403 := bstep (se 1 (by rfl) ⟨824552, by rfl⟩ : syracuseStep 1099403 = 1649105) B1649105
theorem B1468043 : Blo 432776 1468043 := bstep (se 1 (by rfl) ⟨1101032, by rfl⟩ : syracuseStep 1468043 = 2202065) B2202065
theorem B730795 : Blo 432776 730795 := bstep (se 1 (by rfl) ⟨548096, by rfl⟩ : syracuseStep 730795 = 1096193) B1096193
theorem B927443 : Blo 432776 927443 := bstep (se 1 (by rfl) ⟨695582, by rfl⟩ : syracuseStep 927443 = 1391165) B1391165
theorem B1672915 : Blo 432776 1672915 := bstep (se 1 (by rfl) ⟨1254686, by rfl⟩ : syracuseStep 1672915 = 2509373) B2509373
theorem B1238777 : Blo 432776 1238777 := bstep (se 2 (by rfl) ⟨464541, by rfl⟩ : syracuseStep 1238777 = 929083) B929083
theorem B3286817 : Blo 432776 3286817 := bstep (se 2 (by rfl) ⟨1232556, by rfl⟩ : syracuseStep 3286817 = 2465113) B2465113
theorem B3376939 : Blo 432776 3376939 := bstep (se 1 (by rfl) ⟨2532704, by rfl⟩ : syracuseStep 3376939 = 5065409) B5065409
theorem B1648451 : Blo 432776 1648451 := bstep (se 1 (by rfl) ⟨1236338, by rfl⟩ : syracuseStep 1648451 = 2472677) B2472677
theorem B13510489 : Blo 432776 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B1853279 : Blo 432776 1853279 := bstep (se 1 (by rfl) ⟨1389959, by rfl⟩ : syracuseStep 1853279 = 2779919) B2779919
theorem B1099615 : Blo 432776 1099615 := bstep (se 1 (by rfl) ⟨824711, by rfl⟩ : syracuseStep 1099615 = 1649423) B1649423
theorem B2197367 : Blo 432776 2197367 := bstep (se 1 (by rfl) ⟨1648025, by rfl⟩ : syracuseStep 2197367 = 3296051) B3296051
theorem B976823 : Blo 432776 976823 := bstep (se 1 (by rfl) ⟨732617, by rfl⟩ : syracuseStep 976823 = 1465235) B1465235
theorem B1451963 : Blo 432776 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B731099 : Blo 432776 731099 := bstep (se 1 (by rfl) ⟨548324, by rfl⟩ : syracuseStep 731099 = 1096649) B1096649
theorem B2467847 : Blo 432776 2467847 := bstep (se 1 (by rfl) ⟨1850885, by rfl⟩ : syracuseStep 2467847 = 3701771) B3701771
theorem B2222095 : Blo 432776 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B2828317 : Blo 432776 2828317 := bstep (se 3 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 2828317 = 1060619) B1060619
theorem B4180025 : Blo 432776 4180025 := bstep (se 2 (by rfl) ⟨1567509, by rfl⟩ : syracuseStep 4180025 = 3135019) B3135019
theorem B649295 : Blo 432776 649295 := bstep (se 1 (by rfl) ⟨486971, by rfl⟩ : syracuseStep 649295 = 973943) B973943
theorem B7039133 : Blo 432776 7039133 := bstep (se 3 (by rfl) ⟨1319837, by rfl⟩ : syracuseStep 7039133 = 2639675) B2639675
theorem B649415 : Blo 432776 649415 := bstep (se 1 (by rfl) ⟨487061, by rfl⟩ : syracuseStep 649415 = 974123) B974123
theorem B731335 : Blo 432776 731335 := bstep (se 1 (by rfl) ⟨548501, by rfl⟩ : syracuseStep 731335 = 1097003) B1097003
theorem B1648907 : Blo 432776 1648907 := bstep (se 1 (by rfl) ⟨1236680, by rfl⟩ : syracuseStep 1648907 = 2473361) B2473361
theorem B649577 : Blo 432776 649577 := bstep (se 2 (by rfl) ⟨243591, by rfl⟩ : syracuseStep 649577 = 487183) B487183
theorem B731497 : Blo 432776 731497 := bstep (se 2 (by rfl) ⟨274311, by rfl⟩ : syracuseStep 731497 = 548623) B548623
theorem B5933465 : Blo 432776 5933465 := bstep (se 2 (by rfl) ⟨2225049, by rfl⟩ : syracuseStep 5933465 = 4450099) B4450099
theorem B649655 : Blo 432776 649655 := bstep (se 1 (by rfl) ⟨487241, by rfl⟩ : syracuseStep 649655 = 974483) B974483
theorem B1460699 : Blo 432776 1460699 := bstep (se 1 (by rfl) ⟨1095524, by rfl⟩ : syracuseStep 1460699 = 2191049) B2191049
theorem B649691 : Blo 432776 649691 := bstep (se 1 (by rfl) ⟨487268, by rfl⟩ : syracuseStep 649691 = 974537) B974537
theorem B551387 : Blo 432776 551387 := bstep (se 1 (by rfl) ⟨413540, by rfl⟩ : syracuseStep 551387 = 827081) B827081
theorem B977417 : Blo 432776 977417 := bstep (se 2 (by rfl) ⟨366531, by rfl⟩ : syracuseStep 977417 = 733063) B733063
theorem B1042969 : Blo 432776 1042969 := bstep (se 2 (by rfl) ⟨391113, by rfl⟩ : syracuseStep 1042969 = 782227) B782227
theorem B1468961 : Blo 432776 1468961 := bstep (se 2 (by rfl) ⟨550860, by rfl⟩ : syracuseStep 1468961 = 1101721) B1101721
theorem B1100537 : Blo 432776 1100537 := bstep (se 2 (by rfl) ⟨412701, by rfl⟩ : syracuseStep 1100537 = 825403) B825403
theorem B1469177 : Blo 432776 1469177 := bstep (se 2 (by rfl) ⟨550941, by rfl⟩ : syracuseStep 1469177 = 1101883) B1101883
theorem B3533645 : Blo 432776 3533645 := bstep (se 3 (by rfl) ⟨662558, by rfl⟩ : syracuseStep 3533645 = 1325117) B1325117
theorem B977759 : Blo 432776 977759 := bstep (se 1 (by rfl) ⟨733319, by rfl⟩ : syracuseStep 977759 = 1466639) B1466639
theorem B617321 : Blo 432776 617321 := bstep (se 2 (by rfl) ⟨231495, by rfl⟩ : syracuseStep 617321 = 462991) B462991
theorem B650159 : Blo 432776 650159 := bstep (se 1 (by rfl) ⟨487619, by rfl⟩ : syracuseStep 650159 = 975239) B975239
theorem B1649591 : Blo 432776 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B732091 : Blo 432776 732091 := bstep (se 1 (by rfl) ⟨549068, by rfl⟩ : syracuseStep 732091 = 1098137) B1098137
theorem B1469447 : Blo 432776 1469447 := bstep (se 1 (by rfl) ⟨1102085, by rfl⟩ : syracuseStep 1469447 = 2204171) B2204171
theorem B650249 : Blo 432776 650249 := bstep (se 2 (by rfl) ⟨243843, by rfl⟩ : syracuseStep 650249 = 487687) B487687
theorem B10742797 : Blo 432776 10742797 := bstep (se 3 (by rfl) ⟨2014274, by rfl⟩ : syracuseStep 10742797 = 4028549) B4028549
theorem B977939 : Blo 432776 977939 := bstep (se 1 (by rfl) ⟨733454, by rfl⟩ : syracuseStep 977939 = 1466909) B1466909
theorem B650279 : Blo 432776 650279 := bstep (se 1 (by rfl) ⟨487709, by rfl⟩ : syracuseStep 650279 = 975419) B975419
theorem B732199 : Blo 432776 732199 := bstep (se 1 (by rfl) ⟨549149, by rfl⟩ : syracuseStep 732199 = 1098299) B1098299
theorem B3345457 : Blo 432776 3345457 := bstep (se 2 (by rfl) ⟨1254546, by rfl⟩ : syracuseStep 3345457 = 2509093) B2509093
theorem B1469555 : Blo 432776 1469555 := bstep (se 1 (by rfl) ⟨1102166, by rfl⟩ : syracuseStep 1469555 = 2204333) B2204333
theorem B650363 : Blo 432776 650363 := bstep (se 1 (by rfl) ⟨487772, by rfl⟩ : syracuseStep 650363 = 975545) B975545
theorem B1461401 : Blo 432776 1461401 := bstep (se 2 (by rfl) ⟨548025, by rfl⟩ : syracuseStep 1461401 = 1096051) B1096051
theorem B1240235 : Blo 432776 1240235 := bstep (se 1 (by rfl) ⟨930176, by rfl⟩ : syracuseStep 1240235 = 1860353) B1860353
theorem B2477303 : Blo 432776 2477303 := bstep (se 1 (by rfl) ⟨1857977, by rfl⟩ : syracuseStep 2477303 = 3715955) B3715955
theorem B650489 : Blo 432776 650489 := bstep (se 2 (by rfl) ⟨243933, by rfl⟩ : syracuseStep 650489 = 487867) B487867
theorem B2788631 : Blo 432776 2788631 := bstep (se 1 (by rfl) ⟨2091473, by rfl⟩ : syracuseStep 2788631 = 4182947) B4182947
theorem B650591 : Blo 432776 650591 := bstep (se 1 (by rfl) ⟨487943, by rfl⟩ : syracuseStep 650591 = 975887) B975887
theorem B978281 : Blo 432776 978281 := bstep (se 2 (by rfl) ⟨366855, by rfl⟩ : syracuseStep 978281 = 733711) B733711
theorem B650603 : Blo 432776 650603 := bstep (se 1 (by rfl) ⟨487952, by rfl⟩ : syracuseStep 650603 = 975905) B975905
theorem B732523 : Blo 432776 732523 := bstep (se 1 (by rfl) ⟨549392, by rfl⟩ : syracuseStep 732523 = 1098785) B1098785
theorem B1322345 : Blo 432776 1322345 := bstep (se 2 (by rfl) ⟨495879, by rfl⟩ : syracuseStep 1322345 = 991759) B991759
theorem B3566963 : Blo 432776 3566963 := bstep (se 1 (by rfl) ⟨2675222, by rfl⟩ : syracuseStep 3566963 = 5350445) B5350445
theorem B1101185 : Blo 432776 1101185 := bstep (se 2 (by rfl) ⟨412944, by rfl⟩ : syracuseStep 1101185 = 825889) B825889
theorem B1469825 : Blo 432776 1469825 := bstep (se 2 (by rfl) ⟨551184, by rfl⟩ : syracuseStep 1469825 = 1102369) B1102369
theorem B822791 : Blo 432776 822791 := bstep (se 1 (by rfl) ⟨617093, by rfl⟩ : syracuseStep 822791 = 1234187) B1234187
theorem B650831 : Blo 432776 650831 := bstep (se 1 (by rfl) ⟨488123, by rfl⟩ : syracuseStep 650831 = 976247) B976247
theorem B1486433 : Blo 432776 1486433 := bstep (se 2 (by rfl) ⟨557412, by rfl⟩ : syracuseStep 1486433 = 1114825) B1114825
theorem B1044065 : Blo 432776 1044065 := bstep (se 2 (by rfl) ⟨391524, by rfl⟩ : syracuseStep 1044065 = 783049) B783049
theorem B1412743 : Blo 432776 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B1322635 : Blo 432776 1322635 := bstep (se 1 (by rfl) ⟨991976, by rfl⟩ : syracuseStep 1322635 = 1983953) B1983953
theorem B1650365 : Blo 432776 1650365 := bstep (se 3 (by rfl) ⟨309443, by rfl⟩ : syracuseStep 1650365 = 618887) B618887
theorem B487111 : Blo 432776 487111 := bstep (se 1 (by rfl) ⟨365333, by rfl⟩ : syracuseStep 487111 = 730667) B730667
theorem B650951 : Blo 432776 650951 := bstep (se 1 (by rfl) ⟨488213, by rfl⟩ : syracuseStep 650951 = 976427) B976427
theorem B1756883 : Blo 432776 1756883 := bstep (se 1 (by rfl) ⟨1317662, by rfl⟩ : syracuseStep 1756883 = 2635325) B2635325
theorem B651113 : Blo 432776 651113 := bstep (se 2 (by rfl) ⟨244167, by rfl⟩ : syracuseStep 651113 = 488335) B488335
theorem B823223 : Blo 432776 823223 := bstep (se 1 (by rfl) ⟨617417, by rfl⟩ : syracuseStep 823223 = 1234835) B1234835
theorem B651191 : Blo 432776 651191 := bstep (se 1 (by rfl) ⟨488393, by rfl⟩ : syracuseStep 651191 = 976787) B976787
theorem B978875 : Blo 432776 978875 := bstep (se 1 (by rfl) ⟨734156, by rfl⟩ : syracuseStep 978875 = 1468313) B1468313
theorem B651227 : Blo 432776 651227 := bstep (se 1 (by rfl) ⟨488420, by rfl⟩ : syracuseStep 651227 = 976841) B976841
theorem B4452367 : Blo 432776 4452367 := bstep (se 1 (by rfl) ⟨3339275, by rfl⟩ : syracuseStep 4452367 = 6678551) B6678551
theorem B471079 : Blo 432776 471079 := bstep (se 1 (by rfl) ⟨353309, by rfl⟩ : syracuseStep 471079 = 706619) B706619
theorem B979001 : Blo 432776 979001 := bstep (se 2 (by rfl) ⟨367125, by rfl⟩ : syracuseStep 979001 = 734251) B734251
theorem B823375 : Blo 432776 823375 := bstep (se 1 (by rfl) ⟨617531, by rfl⟩ : syracuseStep 823375 = 1235063) B1235063
theorem B790651 : Blo 432776 790651 := bstep (se 1 (by rfl) ⟨592988, by rfl⟩ : syracuseStep 790651 = 1185977) B1185977
theorem B1101995 : Blo 432776 1101995 := bstep (se 1 (by rfl) ⟨826496, by rfl⟩ : syracuseStep 1101995 = 1652993) B1652993
theorem B1470635 : Blo 432776 1470635 := bstep (se 1 (by rfl) ⟨1102976, by rfl⟩ : syracuseStep 1470635 = 2205953) B2205953
theorem B3297509 : Blo 432776 3297509 := bstep (se 4 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 3297509 = 618283) B618283
theorem B1462589 : Blo 432776 1462589 := bstep (se 3 (by rfl) ⟨274235, by rfl⟩ : syracuseStep 1462589 = 548471) B548471
theorem B1651049 : Blo 432776 1651049 := bstep (se 2 (by rfl) ⟨619143, by rfl⟩ : syracuseStep 1651049 = 1238287) B1238287
theorem B733583 : Blo 432776 733583 := bstep (se 1 (by rfl) ⟨550187, by rfl⟩ : syracuseStep 733583 = 1100375) B1100375
theorem B979343 : Blo 432776 979343 := bstep (se 1 (by rfl) ⟨734507, by rfl⟩ : syracuseStep 979343 = 1469015) B1469015
theorem B651695 : Blo 432776 651695 := bstep (se 1 (by rfl) ⟨488771, by rfl⟩ : syracuseStep 651695 = 977543) B977543
theorem B651785 : Blo 432776 651785 := bstep (se 2 (by rfl) ⟨244419, by rfl⟩ : syracuseStep 651785 = 488839) B488839
theorem B5558807 : Blo 432776 5558807 := bstep (se 1 (by rfl) ⟨4169105, by rfl⟩ : syracuseStep 5558807 = 8338211) B8338211
theorem B487975 : Blo 432776 487975 := bstep (se 1 (by rfl) ⟨365981, by rfl⟩ : syracuseStep 487975 = 731963) B731963
theorem B651815 : Blo 432776 651815 := bstep (se 1 (by rfl) ⟨488861, by rfl⟩ : syracuseStep 651815 = 977723) B977723
theorem B2093627 : Blo 432776 2093627 := bstep (se 1 (by rfl) ⟨1570220, by rfl⟩ : syracuseStep 2093627 = 3140441) B3140441
theorem B463439 : Blo 432776 463439 := bstep (se 1 (by rfl) ⟨347579, by rfl⟩ : syracuseStep 463439 = 695159) B695159
theorem B496207 : Blo 432776 496207 := bstep (se 1 (by rfl) ⟨372155, by rfl⟩ : syracuseStep 496207 = 744311) B744311
theorem B1561211 : Blo 432776 1561211 := bstep (se 1 (by rfl) ⟨1170908, by rfl⟩ : syracuseStep 1561211 = 2341817) B2341817
theorem B651899 : Blo 432776 651899 := bstep (se 1 (by rfl) ⟨488924, by rfl⟩ : syracuseStep 651899 = 977849) B977849
theorem B733819 : Blo 432776 733819 := bstep (se 1 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 733819 = 1100729) B1100729
theorem B4526765 : Blo 432776 4526765 := bstep (se 3 (by rfl) ⟨848768, by rfl⟩ : syracuseStep 4526765 = 1697537) B1697537
theorem B1389241 : Blo 432776 1389241 := bstep (se 2 (by rfl) ⟨520965, by rfl⟩ : syracuseStep 1389241 = 1041931) B1041931
theorem B9900755 : Blo 432776 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B979667 : Blo 432776 979667 := bstep (se 1 (by rfl) ⟨734750, by rfl⟩ : syracuseStep 979667 = 1469501) B1469501
theorem B2093779 : Blo 432776 2093779 := bstep (se 1 (by rfl) ⟨1570334, by rfl⟩ : syracuseStep 2093779 = 3140669) B3140669
theorem B652025 : Blo 432776 652025 := bstep (se 2 (by rfl) ⟨244509, by rfl⟩ : syracuseStep 652025 = 489019) B489019
theorem B4166417 : Blo 432776 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B2347805 : Blo 432776 2347805 := bstep (se 3 (by rfl) ⟨440213, by rfl⟩ : syracuseStep 2347805 = 880427) B880427
theorem B652127 : Blo 432776 652127 := bstep (se 1 (by rfl) ⟨489095, by rfl⟩ : syracuseStep 652127 = 978191) B978191
theorem B2470763 : Blo 432776 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B652139 : Blo 432776 652139 := bstep (se 1 (by rfl) ⟨489104, by rfl⟩ : syracuseStep 652139 = 978209) B978209
theorem B783265 : Blo 432776 783265 := bstep (se 2 (by rfl) ⟨293724, by rfl⟩ : syracuseStep 783265 = 587449) B587449
theorem B1102855 : Blo 432776 1102855 := bstep (se 1 (by rfl) ⟨827141, by rfl⟩ : syracuseStep 1102855 = 1654283) B1654283
theorem B652367 : Blo 432776 652367 := bstep (se 1 (by rfl) ⟨489275, by rfl⟩ : syracuseStep 652367 = 978551) B978551
theorem B1758323 : Blo 432776 1758323 := bstep (se 1 (by rfl) ⟨1318742, by rfl⟩ : syracuseStep 1758323 = 2637485) B2637485
theorem B1463453 : Blo 432776 1463453 := bstep (se 3 (by rfl) ⟨274397, by rfl⟩ : syracuseStep 1463453 = 548795) B548795
theorem B652487 : Blo 432776 652487 := bstep (se 1 (by rfl) ⟨489365, by rfl⟩ : syracuseStep 652487 = 978731) B978731
theorem B2086091 : Blo 432776 2086091 := bstep (se 1 (by rfl) ⟨1564568, by rfl⟩ : syracuseStep 2086091 = 3129137) B3129137
theorem B1758455 : Blo 432776 1758455 := bstep (se 1 (by rfl) ⟨1318841, by rfl⟩ : syracuseStep 1758455 = 2637683) B2637683
theorem B3306743 : Blo 432776 3306743 := bstep (se 1 (by rfl) ⟨2480057, by rfl⟩ : syracuseStep 3306743 = 4960115) B4960115
theorem B824681 : Blo 432776 824681 := bstep (se 2 (by rfl) ⟨309255, by rfl⟩ : syracuseStep 824681 = 618511) B618511
theorem B652649 : Blo 432776 652649 := bstep (se 2 (by rfl) ⟨244743, by rfl⟩ : syracuseStep 652649 = 489487) B489487
theorem B47502733 : Blo 432776 47502733 := bstep (se 3 (by rfl) ⟨8906762, by rfl⟩ : syracuseStep 47502733 = 17813525) B17813525
theorem B652727 : Blo 432776 652727 := bstep (se 1 (by rfl) ⟨489545, by rfl⟩ : syracuseStep 652727 = 979091) B979091
theorem B1856969 : Blo 432776 1856969 := bstep (se 2 (by rfl) ⟨696363, by rfl⟩ : syracuseStep 1856969 = 1392727) B1392727
theorem B652763 : Blo 432776 652763 := bstep (se 1 (by rfl) ⟨489572, by rfl⟩ : syracuseStep 652763 = 979145) B979145
theorem B734683 : Blo 432776 734683 := bstep (se 1 (by rfl) ⟨551012, by rfl⟩ : syracuseStep 734683 = 1102025) B1102025
theorem B1177051 : Blo 432776 1177051 := bstep (se 1 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 1177051 = 1765577) B1765577
theorem B3134963 : Blo 432776 3134963 := bstep (se 1 (by rfl) ⟨2351222, by rfl⟩ : syracuseStep 3134963 = 4702445) B4702445
theorem B1324583 : Blo 432776 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B2192993 : Blo 432776 2192993 := bstep (se 2 (by rfl) ⟨822372, by rfl⟩ : syracuseStep 2192993 = 1644745) B1644745
theorem B2258579 : Blo 432776 2258579 := bstep (se 1 (by rfl) ⟨1693934, by rfl⟩ : syracuseStep 2258579 = 3387869) B3387869
theorem B1463993 : Blo 432776 1463993 := bstep (se 2 (by rfl) ⟨548997, by rfl⟩ : syracuseStep 1463993 = 1097995) B1097995
theorem B3307229 : Blo 432776 3307229 := bstep (se 3 (by rfl) ⟨620105, by rfl⟩ : syracuseStep 3307229 = 1240211) B1240211
theorem B1390409 : Blo 432776 1390409 := bstep (se 2 (by rfl) ⟨521403, by rfl⟩ : syracuseStep 1390409 = 1042807) B1042807
theorem B2479967 : Blo 432776 2479967 := bstep (se 1 (by rfl) ⟨1859975, by rfl⟩ : syracuseStep 2479967 = 3719951) B3719951
theorem B1251179 : Blo 432776 1251179 := bstep (se 1 (by rfl) ⟨938384, by rfl⟩ : syracuseStep 1251179 = 1876769) B1876769
theorem B669547 : Blo 432776 669547 := bstep (se 1 (by rfl) ⟨502160, by rfl⟩ : syracuseStep 669547 = 1004321) B1004321
theorem B2774893 : Blo 432776 2774893 := bstep (se 3 (by rfl) ⟨520292, by rfl⟩ : syracuseStep 2774893 = 1040585) B1040585
theorem B3331975 : Blo 432776 3331975 := bstep (se 1 (by rfl) ⟨2498981, by rfl⟩ : syracuseStep 3331975 = 4997963) B4997963
theorem B464815 : Blo 432776 464815 := bstep (se 1 (by rfl) ⟨348611, by rfl⟩ : syracuseStep 464815 = 697223) B697223
theorem B653231 : Blo 432776 653231 := bstep (se 1 (by rfl) ⟨489923, by rfl⟩ : syracuseStep 653231 = 979847) B979847
theorem B2086843 : Blo 432776 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B22566869 : Blo 432776 22566869 := bstep (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) B528911
theorem B653321 : Blo 432776 653321 := bstep (se 2 (by rfl) ⟨244995, by rfl⟩ : syracuseStep 653321 = 489991) B489991
theorem B1644563 : Blo 432776 1644563 := bstep (se 1 (by rfl) ⟨1233422, by rfl⟩ : syracuseStep 1644563 = 2466845) B2466845
theorem B653351 : Blo 432776 653351 := bstep (se 1 (by rfl) ⟨490013, by rfl⟩ : syracuseStep 653351 = 980027) B980027
theorem B735311 : Blo 432776 735311 := bstep (se 1 (by rfl) ⟨551483, by rfl⟩ : syracuseStep 735311 = 1102967) B1102967
theorem B489595 : Blo 432776 489595 := bstep (se 1 (by rfl) ⟨367196, by rfl⟩ : syracuseStep 489595 = 734393) B734393
theorem B653435 : Blo 432776 653435 := bstep (se 1 (by rfl) ⟨490076, by rfl⟩ : syracuseStep 653435 = 980153) B980153
theorem B16963829 : Blo 432776 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B653561 : Blo 432776 653561 := bstep (se 2 (by rfl) ⟨245085, by rfl⟩ : syracuseStep 653561 = 490171) B490171
theorem B1464587 : Blo 432776 1464587 := bstep (se 1 (by rfl) ⟨1098440, by rfl⟩ : syracuseStep 1464587 = 2196881) B2196881
theorem B17824033 : Blo 432776 17824033 := bstep (se 2 (by rfl) ⟨6684012, by rfl⟩ : syracuseStep 17824033 = 13368025) B13368025
theorem B653663 : Blo 432776 653663 := bstep (se 1 (by rfl) ⟨490247, by rfl⟩ : syracuseStep 653663 = 980495) B980495
theorem B825707 : Blo 432776 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B1645019 : Blo 432776 1645019 := bstep (se 1 (by rfl) ⟨1233764, by rfl⟩ : syracuseStep 1645019 = 2467529) B2467529
theorem B522715 : Blo 432776 522715 := bstep (se 1 (by rfl) ⟨392036, by rfl⟩ : syracuseStep 522715 = 784073) B784073
theorem B1464857 : Blo 432776 1464857 := bstep (se 2 (by rfl) ⟨549321, by rfl⟩ : syracuseStep 1464857 = 1098643) B1098643
theorem B4749857 : Blo 432776 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B1653281 : Blo 432776 1653281 := bstep (se 2 (by rfl) ⟨619980, by rfl⟩ : syracuseStep 1653281 = 1239961) B1239961
theorem B490063 : Blo 432776 490063 := bstep (se 1 (by rfl) ⟨367547, by rfl⟩ : syracuseStep 490063 = 735095) B735095
theorem B432815 : Blo 432776 432815 := bstep (se 1 (by rfl) ⟨324611, by rfl⟩ : syracuseStep 432815 = 649223) B649223
theorem B57834163 : Blo 432776 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B1235645 : Blo 432776 1235645 := bstep (se 3 (by rfl) ⟨231683, by rfl⟩ : syracuseStep 1235645 = 463367) B463367
theorem B432839 : Blo 432776 432839 := bstep (se 1 (by rfl) ⟨324629, by rfl⟩ : syracuseStep 432839 = 649259) B649259
theorem B1317575 : Blo 432776 1317575 := bstep (se 1 (by rfl) ⟨988181, by rfl⟩ : syracuseStep 1317575 = 1976363) B1976363
theorem B432859 : Blo 432776 432859 := bstep (se 1 (by rfl) ⟨324644, by rfl⟩ : syracuseStep 432859 = 649289) B649289
theorem B432935 : Blo 432776 432935 := bstep (se 1 (by rfl) ⟨324701, by rfl⟩ : syracuseStep 432935 = 649403) B649403
theorem B2480969 : Blo 432776 2480969 := bstep (se 2 (by rfl) ⟨930363, by rfl⟩ : syracuseStep 2480969 = 1860727) B1860727
theorem B432975 : Blo 432776 432975 := bstep (se 1 (by rfl) ⟨324731, by rfl⟩ : syracuseStep 432975 = 649463) B649463
theorem B432991 : Blo 432776 432991 := bstep (se 1 (by rfl) ⟨324743, by rfl⟩ : syracuseStep 432991 = 649487) B649487
theorem B1145707 : Blo 432776 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B433019 : Blo 432776 433019 := bstep (se 1 (by rfl) ⟨324764, by rfl⟩ : syracuseStep 433019 = 649529) B649529
theorem B433071 : Blo 432776 433071 := bstep (se 1 (by rfl) ⟨324803, by rfl⟩ : syracuseStep 433071 = 649607) B649607
theorem B2202551 : Blo 432776 2202551 := bstep (se 1 (by rfl) ⟨1651913, by rfl⟩ : syracuseStep 2202551 = 3303827) B3303827
theorem B687035 : Blo 432776 687035 := bstep (se 1 (by rfl) ⟨515276, by rfl⟩ : syracuseStep 687035 = 1030553) B1030553
theorem B433095 : Blo 432776 433095 := bstep (se 1 (by rfl) ⟨324821, by rfl⟩ : syracuseStep 433095 = 649643) B649643
theorem B433115 : Blo 432776 433115 := bstep (se 1 (by rfl) ⟨324836, by rfl⟩ : syracuseStep 433115 = 649673) B649673
theorem B826375 : Blo 432776 826375 := bstep (se 1 (by rfl) ⟨619781, by rfl⟩ : syracuseStep 826375 = 1239563) B1239563
theorem B1653767 : Blo 432776 1653767 := bstep (se 1 (by rfl) ⟨1240325, by rfl⟩ : syracuseStep 1653767 = 2480651) B2480651
theorem B1604623 : Blo 432776 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B924691 : Blo 432776 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B2194451 : Blo 432776 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B547879 : Blo 432776 547879 := bstep (se 1 (by rfl) ⟨410909, by rfl⟩ : syracuseStep 547879 = 821819) B821819
theorem B433191 : Blo 432776 433191 := bstep (se 1 (by rfl) ⟨324893, by rfl⟩ : syracuseStep 433191 = 649787) B649787
theorem B433231 : Blo 432776 433231 := bstep (se 1 (by rfl) ⟨324923, by rfl⟩ : syracuseStep 433231 = 649847) B649847
theorem B433247 : Blo 432776 433247 := bstep (se 1 (by rfl) ⟨324935, by rfl⟩ : syracuseStep 433247 = 649871) B649871
theorem B433275 : Blo 432776 433275 := bstep (se 1 (by rfl) ⟨324956, by rfl⟩ : syracuseStep 433275 = 649913) B649913
theorem B1186987 : Blo 432776 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B433327 : Blo 432776 433327 := bstep (se 1 (by rfl) ⟨324995, by rfl⟩ : syracuseStep 433327 = 649991) B649991
theorem B433351 : Blo 432776 433351 := bstep (se 1 (by rfl) ⟨325013, by rfl⟩ : syracuseStep 433351 = 650027) B650027
theorem B433371 : Blo 432776 433371 := bstep (se 1 (by rfl) ⟨325028, by rfl⟩ : syracuseStep 433371 = 650057) B650057
theorem B1015031 : Blo 432776 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B3710245 : Blo 432776 3710245 := bstep (se 4 (by rfl) ⟨347835, by rfl⟩ : syracuseStep 3710245 = 695671) B695671
theorem B433447 : Blo 432776 433447 := bstep (se 1 (by rfl) ⟨325085, by rfl⟩ : syracuseStep 433447 = 650171) B650171
theorem B433487 : Blo 432776 433487 := bstep (se 1 (by rfl) ⟨325115, by rfl⟩ : syracuseStep 433487 = 650231) B650231
theorem B433503 : Blo 432776 433503 := bstep (se 1 (by rfl) ⟨325127, by rfl⟩ : syracuseStep 433503 = 650255) B650255
theorem B925033 : Blo 432776 925033 := bstep (se 2 (by rfl) ⟨346887, by rfl⟩ : syracuseStep 925033 = 693775) B693775
theorem B548203 : Blo 432776 548203 := bstep (se 1 (by rfl) ⟨411152, by rfl⟩ : syracuseStep 548203 = 822305) B822305
theorem B433531 : Blo 432776 433531 := bstep (se 1 (by rfl) ⟨325148, by rfl⟩ : syracuseStep 433531 = 650297) B650297
theorem B5283245 : Blo 432776 5283245 := bstep (se 3 (by rfl) ⟨990608, by rfl⟩ : syracuseStep 5283245 = 1981217) B1981217
theorem B433583 : Blo 432776 433583 := bstep (se 1 (by rfl) ⟨325187, by rfl⟩ : syracuseStep 433583 = 650375) B650375
theorem B433607 : Blo 432776 433607 := bstep (se 1 (by rfl) ⟨325205, by rfl⟩ : syracuseStep 433607 = 650411) B650411
theorem B433627 : Blo 432776 433627 := bstep (se 1 (by rfl) ⟨325220, by rfl⟩ : syracuseStep 433627 = 650441) B650441
theorem B1654253 : Blo 432776 1654253 := bstep (se 3 (by rfl) ⟨310172, by rfl⟩ : syracuseStep 1654253 = 620345) B620345
theorem B974375 : Blo 432776 974375 := bstep (se 1 (by rfl) ⟨730781, by rfl⟩ : syracuseStep 974375 = 1461563) B1461563
theorem B433703 : Blo 432776 433703 := bstep (se 1 (by rfl) ⟨325277, by rfl⟩ : syracuseStep 433703 = 650555) B650555
theorem B433743 : Blo 432776 433743 := bstep (se 1 (by rfl) ⟨325307, by rfl⟩ : syracuseStep 433743 = 650615) B650615
theorem B433759 : Blo 432776 433759 := bstep (se 1 (by rfl) ⟨325319, by rfl⟩ : syracuseStep 433759 = 650639) B650639
theorem B1646203 : Blo 432776 1646203 := bstep (se 1 (by rfl) ⟨1234652, by rfl⟩ : syracuseStep 1646203 = 2469305) B2469305
theorem B433787 : Blo 432776 433787 := bstep (se 1 (by rfl) ⟨325340, by rfl⟩ : syracuseStep 433787 = 650681) B650681
theorem B1465991 : Blo 432776 1465991 := bstep (se 1 (by rfl) ⟨1099493, by rfl⟩ : syracuseStep 1465991 = 2198987) B2198987
theorem B2080403 : Blo 432776 2080403 := bstep (se 1 (by rfl) ⟨1560302, by rfl⟩ : syracuseStep 2080403 = 3120605) B3120605
theorem B433839 : Blo 432776 433839 := bstep (se 1 (by rfl) ⟨325379, by rfl⟩ : syracuseStep 433839 = 650759) B650759
theorem B1466045 : Blo 432776 1466045 := bstep (se 3 (by rfl) ⟨274883, by rfl⟩ : syracuseStep 1466045 = 549767) B549767
theorem B433863 : Blo 432776 433863 := bstep (se 1 (by rfl) ⟨325397, by rfl⟩ : syracuseStep 433863 = 650795) B650795
theorem B433883 : Blo 432776 433883 := bstep (se 1 (by rfl) ⟨325412, by rfl⟩ : syracuseStep 433883 = 650825) B650825
theorem B433959 : Blo 432776 433959 := bstep (se 1 (by rfl) ⟨325469, by rfl⟩ : syracuseStep 433959 = 650939) B650939
theorem B1859395 : Blo 432776 1859395 := bstep (se 1 (by rfl) ⟨1394546, by rfl⟩ : syracuseStep 1859395 = 2789093) B2789093
theorem B433999 : Blo 432776 433999 := bstep (se 1 (by rfl) ⟨325499, by rfl⟩ : syracuseStep 433999 = 650999) B650999
theorem B434015 : Blo 432776 434015 := bstep (se 1 (by rfl) ⟨325511, by rfl⟩ : syracuseStep 434015 = 651023) B651023
theorem B1466207 : Blo 432776 1466207 := bstep (se 1 (by rfl) ⟨1099655, by rfl⟩ : syracuseStep 1466207 = 2199311) B2199311
theorem B974699 : Blo 432776 974699 := bstep (se 1 (by rfl) ⟨731024, by rfl⟩ : syracuseStep 974699 = 1462049) B1462049
theorem B434043 : Blo 432776 434043 := bstep (se 1 (by rfl) ⟨325532, by rfl⟩ : syracuseStep 434043 = 651065) B651065
theorem B974753 : Blo 432776 974753 := bstep (se 2 (by rfl) ⟨365532, by rfl⟩ : syracuseStep 974753 = 731065) B731065
theorem B434095 : Blo 432776 434095 := bstep (se 1 (by rfl) ⟨325571, by rfl⟩ : syracuseStep 434095 = 651143) B651143
theorem B3751867 : Blo 432776 3751867 := bstep (se 1 (by rfl) ⟨2813900, by rfl⟩ : syracuseStep 3751867 = 5627801) B5627801
theorem B434119 : Blo 432776 434119 := bstep (se 1 (by rfl) ⟨325589, by rfl⟩ : syracuseStep 434119 = 651179) B651179
theorem B434139 : Blo 432776 434139 := bstep (se 1 (by rfl) ⟨325604, by rfl⟩ : syracuseStep 434139 = 651209) B651209
theorem B3702833 : Blo 432776 3702833 := bstep (se 2 (by rfl) ⟨1388562, by rfl⟩ : syracuseStep 3702833 = 2777125) B2777125
theorem B1097833 : Blo 432776 1097833 := bstep (se 2 (by rfl) ⟨411687, by rfl⟩ : syracuseStep 1097833 = 823375) B823375
theorem B975059 : Blo 432776 975059 := bstep (se 1 (by rfl) ⟨731294, by rfl⟩ : syracuseStep 975059 = 1462589) B1462589
theorem B975113 : Blo 432776 975113 := bstep (se 2 (by rfl) ⟨365667, by rfl⟩ : syracuseStep 975113 = 731335) B731335
theorem B434463 : Blo 432776 434463 := bstep (se 1 (by rfl) ⟨325847, by rfl⟩ : syracuseStep 434463 = 651695) B651695
theorem B434523 : Blo 432776 434523 := bstep (se 1 (by rfl) ⟨325892, by rfl⟩ : syracuseStep 434523 = 651785) B651785
theorem B557423 : Blo 432776 557423 := bstep (se 1 (by rfl) ⟨418067, by rfl⟩ : syracuseStep 557423 = 836135) B836135
theorem B434543 : Blo 432776 434543 := bstep (se 1 (by rfl) ⟨325907, by rfl⟩ : syracuseStep 434543 = 651815) B651815
theorem B2646437 : Blo 432776 2646437 := bstep (se 4 (by rfl) ⟨248103, by rfl⟩ : syracuseStep 2646437 = 496207) B496207
theorem B1040807 : Blo 432776 1040807 := bstep (se 1 (by rfl) ⟨780605, by rfl⟩ : syracuseStep 1040807 = 1561211) B1561211
theorem B434599 : Blo 432776 434599 := bstep (se 1 (by rfl) ⟨325949, by rfl⟩ : syracuseStep 434599 = 651899) B651899
theorem B975329 : Blo 432776 975329 := bstep (se 2 (by rfl) ⟨365748, by rfl⟩ : syracuseStep 975329 = 731497) B731497
theorem B434683 : Blo 432776 434683 := bstep (se 1 (by rfl) ⟨326012, by rfl⟩ : syracuseStep 434683 = 652025) B652025
theorem B2777611 : Blo 432776 2777611 := bstep (se 1 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 2777611 = 4166417) B4166417
theorem B434751 : Blo 432776 434751 := bstep (se 1 (by rfl) ⟨326063, by rfl⟩ : syracuseStep 434751 = 652127) B652127
theorem B1647175 : Blo 432776 1647175 := bstep (se 1 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 1647175 = 2470763) B2470763
theorem B434759 : Blo 432776 434759 := bstep (se 1 (by rfl) ⟨326069, by rfl⟩ : syracuseStep 434759 = 652139) B652139
theorem B754247 : Blo 432776 754247 := bstep (se 1 (by rfl) ⟨565685, by rfl⟩ : syracuseStep 754247 = 1131371) B1131371
theorem B1098319 : Blo 432776 1098319 := bstep (se 1 (by rfl) ⟨823739, by rfl⟩ : syracuseStep 1098319 = 1647479) B1647479
theorem B696953 : Blo 432776 696953 := bstep (se 2 (by rfl) ⟨261357, by rfl⟩ : syracuseStep 696953 = 522715) B522715
theorem B434911 : Blo 432776 434911 := bstep (se 1 (by rfl) ⟨326183, by rfl⟩ : syracuseStep 434911 = 652367) B652367
theorem B1172215 : Blo 432776 1172215 := bstep (se 1 (by rfl) ⟨879161, by rfl⟩ : syracuseStep 1172215 = 1758323) B1758323
theorem B975635 : Blo 432776 975635 := bstep (se 1 (by rfl) ⟨731726, by rfl⟩ : syracuseStep 975635 = 1463453) B1463453
theorem B434991 : Blo 432776 434991 := bstep (se 1 (by rfl) ⟨326243, by rfl⟩ : syracuseStep 434991 = 652487) B652487
theorem B1172303 : Blo 432776 1172303 := bstep (se 1 (by rfl) ⟨879227, by rfl⟩ : syracuseStep 1172303 = 1758455) B1758455
theorem B2204495 : Blo 432776 2204495 := bstep (se 1 (by rfl) ⟨1653371, by rfl⟩ : syracuseStep 2204495 = 3306743) B3306743
theorem B77112217 : Blo 432776 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B435099 : Blo 432776 435099 := bstep (se 1 (by rfl) ⟨326324, by rfl⟩ : syracuseStep 435099 = 652649) B652649
theorem B1852321 : Blo 432776 1852321 := bstep (se 2 (by rfl) ⟨694620, by rfl⟩ : syracuseStep 1852321 = 1389241) B1389241
theorem B435151 : Blo 432776 435151 := bstep (se 1 (by rfl) ⟨326363, by rfl⟩ : syracuseStep 435151 = 652727) B652727
theorem B1237979 : Blo 432776 1237979 := bstep (se 1 (by rfl) ⟨928484, by rfl⟩ : syracuseStep 1237979 = 1856969) B1856969
theorem B9511901 : Blo 432776 9511901 := bstep (se 3 (by rfl) ⟨1783481, by rfl⟩ : syracuseStep 9511901 = 3566963) B3566963
theorem B435175 : Blo 432776 435175 := bstep (se 1 (by rfl) ⟨326381, by rfl⟩ : syracuseStep 435175 = 652763) B652763
theorem B2089975 : Blo 432776 2089975 := bstep (se 1 (by rfl) ⟨1567481, by rfl⟩ : syracuseStep 2089975 = 3134963) B3134963
theorem B4178947 : Blo 432776 4178947 := bstep (se 1 (by rfl) ⟨3134210, by rfl⟩ : syracuseStep 4178947 = 6268421) B6268421
theorem B11166821 : Blo 432776 11166821 := bstep (se 4 (by rfl) ⟨1046889, by rfl⟩ : syracuseStep 11166821 = 2093779) B2093779
theorem B975995 : Blo 432776 975995 := bstep (se 1 (by rfl) ⟨731996, by rfl⟩ : syracuseStep 975995 = 1463993) B1463993
theorem B2204819 : Blo 432776 2204819 := bstep (se 1 (by rfl) ⟨1653614, by rfl⟩ : syracuseStep 2204819 = 3307229) B3307229
theorem B1098967 : Blo 432776 1098967 := bstep (se 1 (by rfl) ⟨824225, by rfl⟩ : syracuseStep 1098967 = 1648451) B1648451
theorem B926939 : Blo 432776 926939 := bstep (se 1 (by rfl) ⟨695204, by rfl⟩ : syracuseStep 926939 = 1390409) B1390409
theorem B976121 : Blo 432776 976121 := bstep (se 2 (by rfl) ⟨366045, by rfl⟩ : syracuseStep 976121 = 732091) B732091
theorem B435487 : Blo 432776 435487 := bstep (se 1 (by rfl) ⟨326615, by rfl⟩ : syracuseStep 435487 = 653231) B653231
theorem B435547 : Blo 432776 435547 := bstep (se 1 (by rfl) ⟨326660, by rfl⟩ : syracuseStep 435547 = 653321) B653321
theorem B2139497 : Blo 432776 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B435567 : Blo 432776 435567 := bstep (se 1 (by rfl) ⟨326675, by rfl⟩ : syracuseStep 435567 = 653351) B653351
theorem B2786683 : Blo 432776 2786683 := bstep (se 1 (by rfl) ⟨2090012, by rfl⟩ : syracuseStep 2786683 = 4180025) B4180025
theorem B730505 : Blo 432776 730505 := bstep (se 2 (by rfl) ⟨273939, by rfl⟩ : syracuseStep 730505 = 547879) B547879
theorem B976265 : Blo 432776 976265 := bstep (se 2 (by rfl) ⟨366099, by rfl⟩ : syracuseStep 976265 = 732199) B732199
theorem B435623 : Blo 432776 435623 := bstep (se 1 (by rfl) ⟨326717, by rfl⟩ : syracuseStep 435623 = 653435) B653435
theorem B435707 : Blo 432776 435707 := bstep (se 1 (by rfl) ⟨326780, by rfl⟩ : syracuseStep 435707 = 653561) B653561
theorem B95061509 : Blo 432776 95061509 := bstep (se 4 (by rfl) ⟨8912016, by rfl⟩ : syracuseStep 95061509 = 17824033) B17824033
theorem B976391 : Blo 432776 976391 := bstep (se 1 (by rfl) ⟨732293, by rfl⟩ : syracuseStep 976391 = 1464587) B1464587
theorem B1099271 : Blo 432776 1099271 := bstep (se 1 (by rfl) ⟨824453, by rfl⟩ : syracuseStep 1099271 = 1648907) B1648907
theorem B1582649 : Blo 432776 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B5932601 : Blo 432776 5932601 := bstep (se 2 (by rfl) ⟨2224725, by rfl⟩ : syracuseStep 5932601 = 4449451) B4449451
theorem B435775 : Blo 432776 435775 := bstep (se 1 (by rfl) ⟨326831, by rfl⟩ : syracuseStep 435775 = 653663) B653663
theorem B550471 : Blo 432776 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B976571 : Blo 432776 976571 := bstep (se 1 (by rfl) ⟨732428, by rfl⟩ : syracuseStep 976571 = 1464857) B1464857
theorem B878383 : Blo 432776 878383 := bstep (se 1 (by rfl) ⟨658787, by rfl⟩ : syracuseStep 878383 = 1317575) B1317575
theorem B730937 : Blo 432776 730937 := bstep (se 2 (by rfl) ⟨274101, by rfl⟩ : syracuseStep 730937 = 548203) B548203
theorem B976697 : Blo 432776 976697 := bstep (se 2 (by rfl) ⟨366261, by rfl⟩ : syracuseStep 976697 = 732523) B732523
theorem B117253973 : Blo 432776 117253973 := bstep (se 9 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 117253973 = 687035) B687035
theorem B1099727 : Blo 432776 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B1468367 : Blo 432776 1468367 := bstep (se 1 (by rfl) ⟨1101275, by rfl⟩ : syracuseStep 1468367 = 2202551) B2202551
theorem B6260813 : Blo 432776 6260813 := bstep (se 3 (by rfl) ⟨1173902, by rfl⟩ : syracuseStep 6260813 = 2347805) B2347805
theorem B1763513 : Blo 432776 1763513 := bstep (se 2 (by rfl) ⟨661317, by rfl⟩ : syracuseStep 1763513 = 1322635) B1322635
theorem B9423053 : Blo 432776 9423053 := bstep (se 3 (by rfl) ⟨1766822, by rfl⟩ : syracuseStep 9423053 = 3533645) B3533645
theorem B649481 : Blo 432776 649481 := bstep (se 2 (by rfl) ⟨243555, by rfl⟩ : syracuseStep 649481 = 487111) B487111
theorem B2230553 : Blo 432776 2230553 := bstep (se 2 (by rfl) ⟨836457, by rfl⟩ : syracuseStep 2230553 = 1672915) B1672915
theorem B649583 : Blo 432776 649583 := bstep (se 1 (by rfl) ⟨487187, by rfl⟩ : syracuseStep 649583 = 974375) B974375
theorem B977327 : Blo 432776 977327 := bstep (se 1 (by rfl) ⟨732995, by rfl⟩ : syracuseStep 977327 = 1465991) B1465991
theorem B1386935 : Blo 432776 1386935 := bstep (se 1 (by rfl) ⟨1040201, by rfl⟩ : syracuseStep 1386935 = 2080403) B2080403
theorem B977363 : Blo 432776 977363 := bstep (se 1 (by rfl) ⟨733022, by rfl⟩ : syracuseStep 977363 = 1466045) B1466045
theorem B1100243 : Blo 432776 1100243 := bstep (se 1 (by rfl) ⟨825182, by rfl⟩ : syracuseStep 1100243 = 1650365) B1650365
theorem B4442633 : Blo 432776 4442633 := bstep (se 2 (by rfl) ⟨1665987, by rfl⟩ : syracuseStep 4442633 = 3331975) B3331975
theorem B977471 : Blo 432776 977471 := bstep (se 1 (by rfl) ⟨733103, by rfl⟩ : syracuseStep 977471 = 1466207) B1466207
theorem B649799 : Blo 432776 649799 := bstep (se 1 (by rfl) ⟨487349, by rfl⟩ : syracuseStep 649799 = 974699) B974699
theorem B649835 : Blo 432776 649835 := bstep (se 1 (by rfl) ⟨487376, by rfl⟩ : syracuseStep 649835 = 974753) B974753
theorem B977579 : Blo 432776 977579 := bstep (se 1 (by rfl) ⟨733184, by rfl⟩ : syracuseStep 977579 = 1466369) B1466369
theorem B3771089 : Blo 432776 3771089 := bstep (se 2 (by rfl) ⟨1414158, by rfl⟩ : syracuseStep 3771089 = 2828317) B2828317
theorem B2198339 : Blo 432776 2198339 := bstep (se 1 (by rfl) ⟨1648754, by rfl⟩ : syracuseStep 2198339 = 3297509) B3297509
theorem B650063 : Blo 432776 650063 := bstep (se 1 (by rfl) ⟨487547, by rfl⟩ : syracuseStep 650063 = 975095) B975095
theorem B731983 : Blo 432776 731983 := bstep (se 1 (by rfl) ⟨548987, by rfl⟩ : syracuseStep 731983 = 1097975) B1097975
theorem B1100699 : Blo 432776 1100699 := bstep (se 1 (by rfl) ⟨825524, by rfl⟩ : syracuseStep 1100699 = 1651049) B1651049
theorem B1469339 : Blo 432776 1469339 := bstep (se 1 (by rfl) ⟨1102004, by rfl⟩ : syracuseStep 1469339 = 2204009) B2204009
theorem B3705871 : Blo 432776 3705871 := bstep (se 1 (by rfl) ⟨2779403, by rfl⟩ : syracuseStep 3705871 = 5558807) B5558807
theorem B15281167 : Blo 432776 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B1395751 : Blo 432776 1395751 := bstep (se 1 (by rfl) ⟨1046813, by rfl⟩ : syracuseStep 1395751 = 2093627) B2093627
theorem B3017843 : Blo 432776 3017843 := bstep (se 1 (by rfl) ⟨2263382, by rfl⟩ : syracuseStep 3017843 = 4526765) B4526765
theorem B978119 : Blo 432776 978119 := bstep (se 1 (by rfl) ⟨733589, by rfl⟩ : syracuseStep 978119 = 1467179) B1467179
theorem B650459 : Blo 432776 650459 := bstep (se 1 (by rfl) ⟨487844, by rfl⟩ : syracuseStep 650459 = 975689) B975689
theorem B978299 : Blo 432776 978299 := bstep (se 1 (by rfl) ⟨733724, by rfl⟩ : syracuseStep 978299 = 1467449) B1467449
theorem B650633 : Blo 432776 650633 := bstep (se 2 (by rfl) ⟨243987, by rfl⟩ : syracuseStep 650633 = 487975) B487975
theorem B732665 : Blo 432776 732665 := bstep (se 2 (by rfl) ⟨274749, by rfl⟩ : syracuseStep 732665 = 549499) B549499
theorem B978425 : Blo 432776 978425 := bstep (se 2 (by rfl) ⟨366909, by rfl⟩ : syracuseStep 978425 = 733819) B733819
theorem B585211 : Blo 432776 585211 := bstep (se 1 (by rfl) ⟨438908, by rfl⟩ : syracuseStep 585211 = 877817) B877817
theorem B978515 : Blo 432776 978515 := bstep (se 1 (by rfl) ⟨733886, by rfl⟩ : syracuseStep 978515 = 1467773) B1467773
theorem B2199149 : Blo 432776 2199149 := bstep (se 3 (by rfl) ⟨412340, by rfl⟩ : syracuseStep 2199149 = 824681) B824681
theorem B929441 : Blo 432776 929441 := bstep (se 2 (by rfl) ⟨348540, by rfl⟩ : syracuseStep 929441 = 697081) B697081
theorem B1461995 : Blo 432776 1461995 := bstep (se 1 (by rfl) ⟨1096496, by rfl⟩ : syracuseStep 1461995 = 2192993) B2192993
theorem B1388267 : Blo 432776 1388267 := bstep (se 1 (by rfl) ⟨1041200, by rfl⟩ : syracuseStep 1388267 = 2082401) B2082401
theorem B650987 : Blo 432776 650987 := bstep (se 1 (by rfl) ⟨488240, by rfl⟩ : syracuseStep 650987 = 976481) B976481
theorem B732935 : Blo 432776 732935 := bstep (se 1 (by rfl) ⟨549701, by rfl⟩ : syracuseStep 732935 = 1099403) B1099403
theorem B978695 : Blo 432776 978695 := bstep (se 1 (by rfl) ⟨734021, by rfl⟩ : syracuseStep 978695 = 1468043) B1468043
theorem B618295 : Blo 432776 618295 := bstep (se 1 (by rfl) ⟨463721, by rfl⟩ : syracuseStep 618295 = 927443) B927443
theorem B2191211 : Blo 432776 2191211 := bstep (se 1 (by rfl) ⟨1643408, by rfl⟩ : syracuseStep 2191211 = 3286817) B3286817
theorem B1044353 : Blo 432776 1044353 := bstep (se 2 (by rfl) ⟨391632, by rfl⟩ : syracuseStep 1044353 = 783265) B783265
theorem B1470365 : Blo 432776 1470365 := bstep (se 3 (by rfl) ⟨275693, by rfl⟩ : syracuseStep 1470365 = 551387) B551387
theorem B651215 : Blo 432776 651215 := bstep (se 1 (by rfl) ⟨488411, by rfl⟩ : syracuseStep 651215 = 976823) B976823
theorem B15044579 : Blo 432776 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B487399 : Blo 432776 487399 := bstep (se 1 (by rfl) ⟨365549, by rfl⟩ : syracuseStep 487399 = 731099) B731099
theorem B1101833 : Blo 432776 1101833 := bstep (se 2 (by rfl) ⟨413187, by rfl⟩ : syracuseStep 1101833 = 826375) B826375
theorem B1470473 : Blo 432776 1470473 := bstep (se 2 (by rfl) ⟨551427, by rfl⟩ : syracuseStep 1470473 = 1102855) B1102855
theorem B14323729 : Blo 432776 14323729 := bstep (se 2 (by rfl) ⟨5371398, by rfl⟩ : syracuseStep 14323729 = 10742797) B10742797
theorem B1232921 : Blo 432776 1232921 := bstep (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) B924691
theorem B4460609 : Blo 432776 4460609 := bstep (se 2 (by rfl) ⟨1672728, by rfl⟩ : syracuseStep 4460609 = 3345457) B3345457
theorem B11309219 : Blo 432776 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B651611 : Blo 432776 651611 := bstep (se 1 (by rfl) ⟨488708, by rfl⟩ : syracuseStep 651611 = 977417) B977417
theorem B3166571 : Blo 432776 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B979307 : Blo 432776 979307 := bstep (se 1 (by rfl) ⟨734480, by rfl⟩ : syracuseStep 979307 = 1468961) B1468961
theorem B1102187 : Blo 432776 1102187 := bstep (se 1 (by rfl) ⟨826640, by rfl⟩ : syracuseStep 1102187 = 1653281) B1653281
theorem B823763 : Blo 432776 823763 := bstep (se 1 (by rfl) ⟨617822, by rfl⟩ : syracuseStep 823763 = 1235645) B1235645
theorem B1233377 : Blo 432776 1233377 := bstep (se 2 (by rfl) ⟨462516, by rfl⟩ : syracuseStep 1233377 = 925033) B925033
theorem B733691 : Blo 432776 733691 := bstep (se 1 (by rfl) ⟨550268, by rfl⟩ : syracuseStep 733691 = 1100537) B1100537
theorem B979451 : Blo 432776 979451 := bstep (se 1 (by rfl) ⟨734588, by rfl⟩ : syracuseStep 979451 = 1469177) B1469177
theorem B63336977 : Blo 432776 63336977 := bstep (se 2 (by rfl) ⟨23751366, by rfl⟩ : syracuseStep 63336977 = 47502733) B47502733
theorem B651839 : Blo 432776 651839 := bstep (se 1 (by rfl) ⟨488879, by rfl⟩ : syracuseStep 651839 = 977759) B977759
theorem B979577 : Blo 432776 979577 := bstep (se 2 (by rfl) ⟨367341, by rfl⟩ : syracuseStep 979577 = 734683) B734683
theorem B1569401 : Blo 432776 1569401 := bstep (se 2 (by rfl) ⟨588525, by rfl⟩ : syracuseStep 1569401 = 1177051) B1177051
theorem B979631 : Blo 432776 979631 := bstep (se 1 (by rfl) ⟨734723, by rfl⟩ : syracuseStep 979631 = 1469447) B1469447
theorem B1102511 : Blo 432776 1102511 := bstep (se 1 (by rfl) ⟨826883, by rfl⟩ : syracuseStep 1102511 = 1653767) B1653767
theorem B1462967 : Blo 432776 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B651959 : Blo 432776 651959 := bstep (se 1 (by rfl) ⟨488969, by rfl⟩ : syracuseStep 651959 = 977939) B977939
theorem B979703 : Blo 432776 979703 := bstep (se 1 (by rfl) ⟨734777, by rfl⟩ : syracuseStep 979703 = 1469555) B1469555
theorem B676687 : Blo 432776 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B1651535 : Blo 432776 1651535 := bstep (se 1 (by rfl) ⟨1238651, by rfl⟩ : syracuseStep 1651535 = 2477303) B2477303
theorem B652187 : Blo 432776 652187 := bstep (se 1 (by rfl) ⟨489140, by rfl⟩ : syracuseStep 652187 = 978281) B978281
theorem B881563 : Blo 432776 881563 := bstep (se 1 (by rfl) ⟨661172, by rfl⟩ : syracuseStep 881563 = 1322345) B1322345
theorem B734123 : Blo 432776 734123 := bstep (se 1 (by rfl) ⟨550592, by rfl⟩ : syracuseStep 734123 = 1101185) B1101185
theorem B979883 : Blo 432776 979883 := bstep (se 1 (by rfl) ⟨734912, by rfl⟩ : syracuseStep 979883 = 1469825) B1469825
theorem B1102835 : Blo 432776 1102835 := bstep (se 1 (by rfl) ⟨827126, by rfl⟩ : syracuseStep 1102835 = 1654253) B1654253
theorem B4502585 : Blo 432776 4502585 := bstep (se 2 (by rfl) ⟨1688469, by rfl⟩ : syracuseStep 4502585 = 3376939) B3376939
theorem B2479193 : Blo 432776 2479193 := bstep (se 2 (by rfl) ⟨929697, by rfl⟩ : syracuseStep 2479193 = 1859395) B1859395
theorem B3699857 : Blo 432776 3699857 := bstep (se 2 (by rfl) ⟨1387446, by rfl⟩ : syracuseStep 3699857 = 2774893) B2774893
theorem B3871901 : Blo 432776 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B619753 : Blo 432776 619753 := bstep (se 2 (by rfl) ⟨232407, by rfl⟩ : syracuseStep 619753 = 464815) B464815
theorem B5002489 : Blo 432776 5002489 := bstep (se 2 (by rfl) ⟨1875933, by rfl⟩ : syracuseStep 5002489 = 3751867) B3751867
theorem B2782457 : Blo 432776 2782457 := bstep (se 2 (by rfl) ⟨1043421, by rfl⟩ : syracuseStep 2782457 = 2086843) B2086843
theorem B652583 : Blo 432776 652583 := bstep (se 1 (by rfl) ⟨489437, by rfl⟩ : syracuseStep 652583 = 978875) B978875
theorem B2962793 : Blo 432776 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B5936489 : Blo 432776 5936489 := bstep (se 2 (by rfl) ⟨2226183, by rfl⟩ : syracuseStep 5936489 = 4452367) B4452367
theorem B1054075 : Blo 432776 1054075 := bstep (se 1 (by rfl) ⟨790556, by rfl⟩ : syracuseStep 1054075 = 1581113) B1581113
theorem B652667 : Blo 432776 652667 := bstep (se 1 (by rfl) ⟨489500, by rfl⟩ : syracuseStep 652667 = 979001) B979001
theorem B628105 : Blo 432776 628105 := bstep (se 2 (by rfl) ⟨235539, by rfl⟩ : syracuseStep 628105 = 471079) B471079
theorem B734663 : Blo 432776 734663 := bstep (se 1 (by rfl) ⟨550997, by rfl⟩ : syracuseStep 734663 = 1101995) B1101995
theorem B980423 : Blo 432776 980423 := bstep (se 1 (by rfl) ⟨735317, by rfl⟩ : syracuseStep 980423 = 1470635) B1470635
theorem B1054201 : Blo 432776 1054201 := bstep (se 2 (by rfl) ⟨395325, by rfl⟩ : syracuseStep 1054201 = 790651) B790651
theorem B652793 : Blo 432776 652793 := bstep (se 2 (by rfl) ⟨244797, by rfl⟩ : syracuseStep 652793 = 489595) B489595
theorem B1316359 : Blo 432776 1316359 := bstep (se 1 (by rfl) ⟨987269, by rfl⟩ : syracuseStep 1316359 = 1974539) B1974539
theorem B489055 : Blo 432776 489055 := bstep (se 1 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 489055 = 733583) B733583
theorem B652895 : Blo 432776 652895 := bstep (se 1 (by rfl) ⟨489671, by rfl⟩ : syracuseStep 652895 = 979343) B979343
theorem B2086535 : Blo 432776 2086535 := bstep (se 1 (by rfl) ⟨1564901, by rfl⟩ : syracuseStep 2086535 = 3129803) B3129803
theorem B6248123 : Blo 432776 6248123 := bstep (se 1 (by rfl) ⟨4686092, by rfl⟩ : syracuseStep 6248123 = 9372185) B9372185
theorem B6600503 : Blo 432776 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B653111 : Blo 432776 653111 := bstep (se 1 (by rfl) ⟨489833, by rfl⟩ : syracuseStep 653111 = 979667) B979667
theorem B743375 : Blo 432776 743375 := bstep (se 1 (by rfl) ⟨557531, by rfl⟩ : syracuseStep 743375 = 1115063) B1115063
theorem B2578405 : Blo 432776 2578405 := bstep (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) B483451
theorem B1390625 : Blo 432776 1390625 := bstep (se 2 (by rfl) ⟨521484, by rfl⟩ : syracuseStep 1390625 = 1042969) B1042969
theorem B653417 : Blo 432776 653417 := bstep (se 2 (by rfl) ⟨245031, by rfl⟩ : syracuseStep 653417 = 490063) B490063
theorem B1390727 : Blo 432776 1390727 := bstep (se 1 (by rfl) ⟨1043045, by rfl⟩ : syracuseStep 1390727 = 2086091) B2086091
theorem B883055 : Blo 432776 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B1505719 : Blo 432776 1505719 := bstep (se 1 (by rfl) ⟨1129289, by rfl⟩ : syracuseStep 1505719 = 2258579) B2258579
theorem B14088653 : Blo 432776 14088653 := bstep (se 3 (by rfl) ⟨2641622, by rfl⟩ : syracuseStep 14088653 = 5283245) B5283245
theorem B825851 : Blo 432776 825851 := bstep (se 1 (by rfl) ⟨619388, by rfl⟩ : syracuseStep 825851 = 1238777) B1238777
theorem B1235519 : Blo 432776 1235519 := bstep (se 1 (by rfl) ⟨926639, by rfl⟩ : syracuseStep 1235519 = 1853279) B1853279
theorem B1653311 : Blo 432776 1653311 := bstep (se 1 (by rfl) ⟨1239983, by rfl⟩ : syracuseStep 1653311 = 2479967) B2479967
theorem B834119 : Blo 432776 834119 := bstep (se 1 (by rfl) ⟨625589, by rfl⟩ : syracuseStep 834119 = 1251179) B1251179
theorem B1464911 : Blo 432776 1464911 := bstep (se 1 (by rfl) ⟨1098683, by rfl⟩ : syracuseStep 1464911 = 2197367) B2197367
theorem B4463237 : Blo 432776 4463237 := bstep (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) B836857
theorem B1645231 : Blo 432776 1645231 := bstep (se 1 (by rfl) ⟨1233923, by rfl⟩ : syracuseStep 1645231 = 2467847) B2467847
theorem B1096375 : Blo 432776 1096375 := bstep (se 1 (by rfl) ⟨822281, by rfl⟩ : syracuseStep 1096375 = 1644563) B1644563
theorem B432863 : Blo 432776 432863 := bstep (se 1 (by rfl) ⟨324647, by rfl⟩ : syracuseStep 432863 = 649295) B649295
theorem B490207 : Blo 432776 490207 := bstep (se 1 (by rfl) ⟨367655, by rfl⟩ : syracuseStep 490207 = 735311) B735311
theorem B4692755 : Blo 432776 4692755 := bstep (se 1 (by rfl) ⟨3519566, by rfl⟩ : syracuseStep 4692755 = 7039133) B7039133
theorem B432943 : Blo 432776 432943 := bstep (se 1 (by rfl) ⟨324707, by rfl⟩ : syracuseStep 432943 = 649415) B649415
theorem B1235837 : Blo 432776 1235837 := bstep (se 3 (by rfl) ⟨231719, by rfl⟩ : syracuseStep 1235837 = 463439) B463439
theorem B433051 : Blo 432776 433051 := bstep (se 1 (by rfl) ⟨324788, by rfl⟩ : syracuseStep 433051 = 649577) B649577
theorem B3955643 : Blo 432776 3955643 := bstep (se 1 (by rfl) ⟨2966732, by rfl⟩ : syracuseStep 3955643 = 5933465) B5933465
theorem B433103 : Blo 432776 433103 := bstep (se 1 (by rfl) ⟨324827, by rfl⟩ : syracuseStep 433103 = 649655) B649655
theorem B973799 : Blo 432776 973799 := bstep (se 1 (by rfl) ⟨730349, by rfl⟩ : syracuseStep 973799 = 1460699) B1460699
theorem B433127 : Blo 432776 433127 := bstep (se 1 (by rfl) ⟨324845, by rfl⟩ : syracuseStep 433127 = 649691) B649691
theorem B1096679 : Blo 432776 1096679 := bstep (se 1 (by rfl) ⟨822509, by rfl⟩ : syracuseStep 1096679 = 1645019) B1645019
theorem B4946993 : Blo 432776 4946993 := bstep (se 2 (by rfl) ⟨1855122, by rfl⟩ : syracuseStep 4946993 = 3710245) B3710245
theorem B1653979 : Blo 432776 1653979 := bstep (se 1 (by rfl) ⟨1240484, by rfl⟩ : syracuseStep 1653979 = 2480969) B2480969
theorem B6110437 : Blo 432776 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B433439 : Blo 432776 433439 := bstep (se 1 (by rfl) ⟨325079, by rfl⟩ : syracuseStep 433439 = 650159) B650159
theorem B433499 : Blo 432776 433499 := bstep (se 1 (by rfl) ⟨325124, by rfl⟩ : syracuseStep 433499 = 650249) B650249
theorem B974177 : Blo 432776 974177 := bstep (se 2 (by rfl) ⟨365316, by rfl⟩ : syracuseStep 974177 = 730633) B730633
theorem B433519 : Blo 432776 433519 := bstep (se 1 (by rfl) ⟨325139, by rfl⟩ : syracuseStep 433519 = 650279) B650279
theorem B433575 : Blo 432776 433575 := bstep (se 1 (by rfl) ⟨325181, by rfl⟩ : syracuseStep 433575 = 650363) B650363
theorem B974267 : Blo 432776 974267 := bstep (se 1 (by rfl) ⟨730700, by rfl⟩ : syracuseStep 974267 = 1461401) B1461401
theorem B826823 : Blo 432776 826823 := bstep (se 1 (by rfl) ⟨620117, by rfl⟩ : syracuseStep 826823 = 1240235) B1240235
theorem B2194937 : Blo 432776 2194937 := bstep (se 2 (by rfl) ⟨823101, by rfl⟩ : syracuseStep 2194937 = 1646203) B1646203
theorem B433659 : Blo 432776 433659 := bstep (se 1 (by rfl) ⟨325244, by rfl⟩ : syracuseStep 433659 = 650489) B650489
theorem B1883657 : Blo 432776 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B1859087 : Blo 432776 1859087 := bstep (se 1 (by rfl) ⟨1394315, by rfl⟩ : syracuseStep 1859087 = 2788631) B2788631
theorem B974393 : Blo 432776 974393 := bstep (se 2 (by rfl) ⟨365397, by rfl⟩ : syracuseStep 974393 = 730795) B730795
theorem B433727 : Blo 432776 433727 := bstep (se 1 (by rfl) ⟨325295, by rfl⟩ : syracuseStep 433727 = 650591) B650591
theorem B433735 : Blo 432776 433735 := bstep (se 1 (by rfl) ⟨325301, by rfl⟩ : syracuseStep 433735 = 650603) B650603
theorem B1646189 : Blo 432776 1646189 := bstep (se 3 (by rfl) ⟨308660, by rfl⟩ : syracuseStep 1646189 = 617321) B617321
theorem B548527 : Blo 432776 548527 := bstep (se 1 (by rfl) ⟨411395, by rfl⟩ : syracuseStep 548527 = 822791) B822791
theorem B433887 : Blo 432776 433887 := bstep (se 1 (by rfl) ⟨325415, by rfl⟩ : syracuseStep 433887 = 650831) B650831
theorem B990955 : Blo 432776 990955 := bstep (se 1 (by rfl) ⟨743216, by rfl⟩ : syracuseStep 990955 = 1486433) B1486433
theorem B696043 : Blo 432776 696043 := bstep (se 1 (by rfl) ⟨522032, by rfl⟩ : syracuseStep 696043 = 1044065) B1044065
theorem B18013985 : Blo 432776 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B1466153 : Blo 432776 1466153 := bstep (se 2 (by rfl) ⟨549807, by rfl⟩ : syracuseStep 1466153 = 1099615) B1099615
theorem B433967 : Blo 432776 433967 := bstep (se 1 (by rfl) ⟨325475, by rfl⟩ : syracuseStep 433967 = 650951) B650951
theorem B1171255 : Blo 432776 1171255 := bstep (se 1 (by rfl) ⟨878441, by rfl⟩ : syracuseStep 1171255 = 1756883) B1756883
theorem B892729 : Blo 432776 892729 := bstep (se 2 (by rfl) ⟨334773, by rfl⟩ : syracuseStep 892729 = 669547) B669547
theorem B2195261 : Blo 432776 2195261 := bstep (se 3 (by rfl) ⟨411611, by rfl⟩ : syracuseStep 2195261 = 823223) B823223
theorem B434075 : Blo 432776 434075 := bstep (se 1 (by rfl) ⟨325556, by rfl⟩ : syracuseStep 434075 = 651113) B651113
theorem B434127 : Blo 432776 434127 := bstep (se 1 (by rfl) ⟨325595, by rfl⟩ : syracuseStep 434127 = 651191) B651191
theorem B434151 : Blo 432776 434151 := bstep (se 1 (by rfl) ⟨325613, by rfl⟩ : syracuseStep 434151 = 651227) B651227
theorem B11894957 : Blo 432776 11894957 := bstep (se 3 (by rfl) ⟨2230304, by rfl⟩ : syracuseStep 11894957 = 4460609) B4460609
theorem B434407 : Blo 432776 434407 := bstep (se 1 (by rfl) ⟨325805, by rfl⟩ : syracuseStep 434407 = 651611) B651611
theorem B549175 : Blo 432776 549175 := bstep (se 1 (by rfl) ⟨411881, by rfl⟩ : syracuseStep 549175 = 823763) B823763
theorem B434559 : Blo 432776 434559 := bstep (se 1 (by rfl) ⟨325919, by rfl⟩ : syracuseStep 434559 = 651839) B651839
theorem B975311 : Blo 432776 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B434639 : Blo 432776 434639 := bstep (se 1 (by rfl) ⟨325979, by rfl⟩ : syracuseStep 434639 = 651959) B651959
theorem B2007625 : Blo 432776 2007625 := bstep (se 2 (by rfl) ⟨752859, by rfl⟩ : syracuseStep 2007625 = 1505719) B1505719
theorem B434791 : Blo 432776 434791 := bstep (se 1 (by rfl) ⟨326093, by rfl⟩ : syracuseStep 434791 = 652187) B652187
theorem B6341267 : Blo 432776 6341267 := bstep (se 1 (by rfl) ⟨4755950, by rfl⟩ : syracuseStep 6341267 = 9511901) B9511901
theorem B3703481 : Blo 432776 3703481 := bstep (se 2 (by rfl) ⟨1388805, by rfl⟩ : syracuseStep 3703481 = 2777611) B2777611
theorem B2196233 : Blo 432776 2196233 := bstep (se 2 (by rfl) ⟨823587, by rfl⟩ : syracuseStep 2196233 = 1647175) B1647175
theorem B2466571 : Blo 432776 2466571 := bstep (se 1 (by rfl) ⟨1849928, by rfl⟩ : syracuseStep 2466571 = 3699857) B3699857
theorem B435055 : Blo 432776 435055 := bstep (se 1 (by rfl) ⟨326291, by rfl⟩ : syracuseStep 435055 = 652583) B652583
theorem B1975195 : Blo 432776 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B1426331 : Blo 432776 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B3957659 : Blo 432776 3957659 := bstep (se 1 (by rfl) ⟨2968244, by rfl⟩ : syracuseStep 3957659 = 5936489) B5936489
theorem B435111 : Blo 432776 435111 := bstep (se 1 (by rfl) ⟨326333, by rfl⟩ : syracuseStep 435111 = 652667) B652667
theorem B435195 : Blo 432776 435195 := bstep (se 1 (by rfl) ⟨326396, by rfl⟩ : syracuseStep 435195 = 652793) B652793
theorem B63374339 : Blo 432776 63374339 := bstep (se 1 (by rfl) ⟨47530754, by rfl⟩ : syracuseStep 63374339 = 95061509) B95061509
theorem B435263 : Blo 432776 435263 := bstep (se 1 (by rfl) ⟨326447, by rfl⟩ : syracuseStep 435263 = 652895) B652895
theorem B902249 : Blo 432776 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B975977 : Blo 432776 975977 := bstep (se 2 (by rfl) ⟨365991, by rfl⟩ : syracuseStep 975977 = 731983) B731983
theorem B4400335 : Blo 432776 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B435407 : Blo 432776 435407 := bstep (se 1 (by rfl) ⟨326555, by rfl⟩ : syracuseStep 435407 = 653111) B653111
theorem B78169315 : Blo 432776 78169315 := bstep (se 1 (by rfl) ⟨58626986, by rfl⟩ : syracuseStep 78169315 = 117253973) B117253973
theorem B3712229 : Blo 432776 3712229 := bstep (se 4 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 3712229 = 696043) B696043
theorem B6251813 : Blo 432776 6251813 := bstep (se 4 (by rfl) ⟨586107, by rfl⟩ : syracuseStep 6251813 = 1172215) B1172215
theorem B2786633 : Blo 432776 2786633 := bstep (se 2 (by rfl) ⟨1044987, by rfl⟩ : syracuseStep 2786633 = 2089975) B2089975
theorem B5571929 : Blo 432776 5571929 := bstep (se 2 (by rfl) ⟨2089473, by rfl⟩ : syracuseStep 5571929 = 4178947) B4178947
theorem B4941161 : Blo 432776 4941161 := bstep (se 2 (by rfl) ⟨1852935, by rfl⟩ : syracuseStep 4941161 = 3705871) B3705871
theorem B927083 : Blo 432776 927083 := bstep (se 1 (by rfl) ⟨695312, by rfl⟩ : syracuseStep 927083 = 1390625) B1390625
theorem B1861001 : Blo 432776 1861001 := bstep (se 2 (by rfl) ⟨697875, by rfl⟩ : syracuseStep 1861001 = 1395751) B1395751
theorem B435611 : Blo 432776 435611 := bstep (se 1 (by rfl) ⟨326708, by rfl⟩ : syracuseStep 435611 = 653417) B653417
theorem B2205305 : Blo 432776 2205305 := bstep (se 2 (by rfl) ⟨826989, by rfl⟩ : syracuseStep 2205305 = 1653979) B1653979
theorem B6669985 : Blo 432776 6669985 := bstep (se 2 (by rfl) ⟨2501244, by rfl⟩ : syracuseStep 6669985 = 5002489) B5002489
theorem B550567 : Blo 432776 550567 := bstep (se 1 (by rfl) ⟨412925, by rfl⟩ : syracuseStep 550567 = 825851) B825851
theorem B976607 : Blo 432776 976607 := bstep (se 1 (by rfl) ⟨732455, by rfl⟩ : syracuseStep 976607 = 1464911) B1464911
theorem B2975491 : Blo 432776 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B837473 : Blo 432776 837473 := bstep (se 2 (by rfl) ⟨314052, by rfl⟩ : syracuseStep 837473 = 628105) B628105
theorem B649199 : Blo 432776 649199 := bstep (se 1 (by rfl) ⟨486899, by rfl⟩ : syracuseStep 649199 = 973799) B973799
theorem B731119 : Blo 432776 731119 := bstep (se 1 (by rfl) ⟨548339, by rfl⟩ : syracuseStep 731119 = 1096679) B1096679
theorem B780281 : Blo 432776 780281 := bstep (se 2 (by rfl) ⟨292605, by rfl⟩ : syracuseStep 780281 = 585211) B585211
theorem B1755145 : Blo 432776 1755145 := bstep (se 2 (by rfl) ⟨658179, by rfl⟩ : syracuseStep 1755145 = 1316359) B1316359
theorem B731369 : Blo 432776 731369 := bstep (se 2 (by rfl) ⟨274263, by rfl⟩ : syracuseStep 731369 = 548527) B548527
theorem B649451 : Blo 432776 649451 := bstep (se 1 (by rfl) ⟨487088, by rfl⟩ : syracuseStep 649451 = 974177) B974177
theorem B649511 : Blo 432776 649511 := bstep (se 1 (by rfl) ⟨487133, by rfl⟩ : syracuseStep 649511 = 974267) B974267
theorem B551215 : Blo 432776 551215 := bstep (se 1 (by rfl) ⟨413411, by rfl⟩ : syracuseStep 551215 = 826823) B826823
theorem B1321273 : Blo 432776 1321273 := bstep (se 2 (by rfl) ⟨495477, by rfl⟩ : syracuseStep 1321273 = 990955) B990955
theorem B3295565 : Blo 432776 3295565 := bstep (se 3 (by rfl) ⟨617918, by rfl⟩ : syracuseStep 3295565 = 1235837) B1235837
theorem B1255771 : Blo 432776 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B1239391 : Blo 432776 1239391 := bstep (se 1 (by rfl) ⟨929543, by rfl⟩ : syracuseStep 1239391 = 1859087) B1859087
theorem B649595 : Blo 432776 649595 := bstep (se 1 (by rfl) ⟨487196, by rfl⟩ : syracuseStep 649595 = 974393) B974393
theorem B1190305 : Blo 432776 1190305 := bstep (se 2 (by rfl) ⟨446364, by rfl⟩ : syracuseStep 1190305 = 892729) B892729
theorem B977435 : Blo 432776 977435 := bstep (se 1 (by rfl) ⟨733076, by rfl⟩ : syracuseStep 977435 = 1466153) B1466153
theorem B1460807 : Blo 432776 1460807 := bstep (se 1 (by rfl) ⟨1095605, by rfl⟩ : syracuseStep 1460807 = 2191211) B2191211
theorem B649865 : Blo 432776 649865 := bstep (se 2 (by rfl) ⟨243699, by rfl⟩ : syracuseStep 649865 = 487399) B487399
theorem B10029719 : Blo 432776 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B19098305 : Blo 432776 19098305 := bstep (se 2 (by rfl) ⟨7161864, by rfl⟩ : syracuseStep 19098305 = 14323729) B14323729
theorem B2468555 : Blo 432776 2468555 := bstep (se 1 (by rfl) ⟨1851416, by rfl⟩ : syracuseStep 2468555 = 3702833) B3702833
theorem B3287789 : Blo 432776 3287789 := bstep (se 3 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 3287789 = 1232921) B1232921
theorem B7539479 : Blo 432776 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B650039 : Blo 432776 650039 := bstep (se 1 (by rfl) ⟨487529, by rfl⟩ : syracuseStep 650039 = 975059) B975059
theorem B650075 : Blo 432776 650075 := bstep (se 1 (by rfl) ⟨487556, by rfl⟩ : syracuseStep 650075 = 975113) B975113
theorem B822251 : Blo 432776 822251 := bstep (se 1 (by rfl) ⟨616688, by rfl⟩ : syracuseStep 822251 = 1233377) B1233377
theorem B650219 : Blo 432776 650219 := bstep (se 1 (by rfl) ⟨487664, by rfl⟩ : syracuseStep 650219 = 975329) B975329
theorem B42224651 : Blo 432776 42224651 := bstep (se 1 (by rfl) ⟨31668488, by rfl⟩ : syracuseStep 42224651 = 63336977) B63336977
theorem B502831 : Blo 432776 502831 := bstep (se 1 (by rfl) ⟨377123, by rfl⟩ : syracuseStep 502831 = 754247) B754247
theorem B10325069 : Blo 432776 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B650423 : Blo 432776 650423 := bstep (se 1 (by rfl) ⟨487817, by rfl⟩ : syracuseStep 650423 = 975635) B975635
theorem B781535 : Blo 432776 781535 := bstep (se 1 (by rfl) ⟨586151, by rfl⟩ : syracuseStep 781535 = 1172303) B1172303
theorem B1101023 : Blo 432776 1101023 := bstep (se 1 (by rfl) ⟨825767, by rfl⟩ : syracuseStep 1101023 = 1651535) B1651535
theorem B1469663 : Blo 432776 1469663 := bstep (se 1 (by rfl) ⟨1102247, by rfl⟩ : syracuseStep 1469663 = 2204495) B2204495
theorem B650663 : Blo 432776 650663 := bstep (se 1 (by rfl) ⟨487997, by rfl⟩ : syracuseStep 650663 = 975995) B975995
theorem B1469879 : Blo 432776 1469879 := bstep (se 1 (by rfl) ⟨1102409, by rfl⟩ : syracuseStep 1469879 = 2204819) B2204819
theorem B617959 : Blo 432776 617959 := bstep (se 1 (by rfl) ⟨463469, by rfl⟩ : syracuseStep 617959 = 926939) B926939
theorem B650747 : Blo 432776 650747 := bstep (se 1 (by rfl) ⟨488060, by rfl⟩ : syracuseStep 650747 = 976121) B976121
theorem B1854971 : Blo 432776 1854971 := bstep (se 1 (by rfl) ⟨1391228, by rfl⟩ : syracuseStep 1854971 = 2782457) B2782457
theorem B1461833 : Blo 432776 1461833 := bstep (se 2 (by rfl) ⟨548187, by rfl⟩ : syracuseStep 1461833 = 1096375) B1096375
theorem B487003 : Blo 432776 487003 := bstep (se 1 (by rfl) ⟨365252, by rfl⟩ : syracuseStep 487003 = 730505) B730505
theorem B650843 : Blo 432776 650843 := bstep (se 1 (by rfl) ⟨488132, by rfl⟩ : syracuseStep 650843 = 976265) B976265
theorem B650927 : Blo 432776 650927 := bstep (se 1 (by rfl) ⟨488195, by rfl⟩ : syracuseStep 650927 = 976391) B976391
theorem B732847 : Blo 432776 732847 := bstep (se 1 (by rfl) ⟨549635, by rfl⟩ : syracuseStep 732847 = 1099271) B1099271
theorem B7057165 : Blo 432776 7057165 := bstep (se 3 (by rfl) ⟨1323218, by rfl⟩ : syracuseStep 7057165 = 2646437) B2646437
theorem B4165415 : Blo 432776 4165415 := bstep (se 1 (by rfl) ⟨3124061, by rfl⟩ : syracuseStep 4165415 = 6248123) B6248123
theorem B651047 : Blo 432776 651047 := bstep (se 1 (by rfl) ⟨488285, by rfl⟩ : syracuseStep 651047 = 976571) B976571
theorem B1175417 : Blo 432776 1175417 := bstep (se 2 (by rfl) ⟨440781, by rfl⟩ : syracuseStep 1175417 = 881563) B881563
theorem B487291 : Blo 432776 487291 := bstep (se 1 (by rfl) ⟨365468, by rfl⟩ : syracuseStep 487291 = 730937) B730937
theorem B651131 : Blo 432776 651131 := bstep (se 1 (by rfl) ⟨488348, by rfl⟩ : syracuseStep 651131 = 976697) B976697
theorem B2469761 : Blo 432776 2469761 := bstep (se 2 (by rfl) ⟨926160, by rfl⟩ : syracuseStep 2469761 = 1852321) B1852321
theorem B733151 : Blo 432776 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B978911 : Blo 432776 978911 := bstep (se 1 (by rfl) ⟨734183, by rfl⟩ : syracuseStep 978911 = 1468367) B1468367
theorem B4173875 : Blo 432776 4173875 := bstep (se 1 (by rfl) ⟨3130406, by rfl⟩ : syracuseStep 4173875 = 6260813) B6260813
theorem B826337 : Blo 432776 826337 := bstep (se 2 (by rfl) ⟨309876, by rfl⟩ : syracuseStep 826337 = 619753) B619753
theorem B1175675 : Blo 432776 1175675 := bstep (se 1 (by rfl) ⟨881756, by rfl⟩ : syracuseStep 1175675 = 1763513) B1763513
theorem B1487035 : Blo 432776 1487035 := bstep (se 1 (by rfl) ⟨1115276, by rfl⟩ : syracuseStep 1487035 = 2230553) B2230553
theorem B651551 : Blo 432776 651551 := bstep (se 1 (by rfl) ⟨488663, by rfl⟩ : syracuseStep 651551 = 977327) B977327
theorem B8147249 : Blo 432776 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B9392435 : Blo 432776 9392435 := bstep (se 1 (by rfl) ⟨7044326, by rfl⟩ : syracuseStep 9392435 = 14088653) B14088653
theorem B651575 : Blo 432776 651575 := bstep (se 1 (by rfl) ⟨488681, by rfl⟩ : syracuseStep 651575 = 977363) B977363
theorem B733495 : Blo 432776 733495 := bstep (se 1 (by rfl) ⟨550121, by rfl⟩ : syracuseStep 733495 = 1100243) B1100243
theorem B2961755 : Blo 432776 2961755 := bstep (se 1 (by rfl) ⟨2221316, by rfl⟩ : syracuseStep 2961755 = 4442633) B4442633
theorem B823679 : Blo 432776 823679 := bstep (se 1 (by rfl) ⟨617759, by rfl⟩ : syracuseStep 823679 = 1235519) B1235519
theorem B651647 : Blo 432776 651647 := bstep (se 1 (by rfl) ⟨488735, by rfl⟩ : syracuseStep 651647 = 977471) B977471
theorem B1102207 : Blo 432776 1102207 := bstep (se 1 (by rfl) ⟨826655, by rfl⟩ : syracuseStep 1102207 = 1653311) B1653311
theorem B2478509 : Blo 432776 2478509 := bstep (se 3 (by rfl) ⟨464720, by rfl⟩ : syracuseStep 2478509 = 929441) B929441
theorem B651719 : Blo 432776 651719 := bstep (se 1 (by rfl) ⟨488789, by rfl⟩ : syracuseStep 651719 = 977579) B977579
theorem B1405433 : Blo 432776 1405433 := bstep (se 2 (by rfl) ⟨527037, by rfl⟩ : syracuseStep 1405433 = 1054075) B1054075
theorem B3715577 : Blo 432776 3715577 := bstep (se 2 (by rfl) ⟨1393341, by rfl⟩ : syracuseStep 3715577 = 2786683) B2786683
theorem B733799 : Blo 432776 733799 := bstep (se 1 (by rfl) ⟨550349, by rfl⟩ : syracuseStep 733799 = 1100699) B1100699
theorem B979559 : Blo 432776 979559 := bstep (se 1 (by rfl) ⟨734669, by rfl⟩ : syracuseStep 979559 = 1469339) B1469339
theorem B1405601 : Blo 432776 1405601 := bstep (se 2 (by rfl) ⟨527100, by rfl⟩ : syracuseStep 1405601 = 1054201) B1054201
theorem B3297995 : Blo 432776 3297995 := bstep (se 1 (by rfl) ⟨2473496, by rfl⟩ : syracuseStep 3297995 = 4946993) B4946993
theorem B12514013 : Blo 432776 12514013 := bstep (se 3 (by rfl) ⟨2346377, by rfl⟩ : syracuseStep 12514013 = 4692755) B4692755
theorem B2011895 : Blo 432776 2011895 := bstep (se 1 (by rfl) ⟨1508921, by rfl⟩ : syracuseStep 2011895 = 3017843) B3017843
theorem B733961 : Blo 432776 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B652073 : Blo 432776 652073 := bstep (se 2 (by rfl) ⟨244527, by rfl⟩ : syracuseStep 652073 = 489055) B489055
theorem B652079 : Blo 432776 652079 := bstep (se 1 (by rfl) ⟨489059, by rfl⟩ : syracuseStep 652079 = 978119) B978119
theorem B652199 : Blo 432776 652199 := bstep (se 1 (by rfl) ⟨489149, by rfl⟩ : syracuseStep 652199 = 978299) B978299
theorem B1463291 : Blo 432776 1463291 := bstep (se 1 (by rfl) ⟨1097468, by rfl⟩ : syracuseStep 1463291 = 2194937) B2194937
theorem B488443 : Blo 432776 488443 := bstep (se 1 (by rfl) ⟨366332, by rfl⟩ : syracuseStep 488443 = 732665) B732665
theorem B652283 : Blo 432776 652283 := bstep (se 1 (by rfl) ⟨489212, by rfl⟩ : syracuseStep 652283 = 978425) B978425
theorem B652343 : Blo 432776 652343 := bstep (se 1 (by rfl) ⟨489257, by rfl⟩ : syracuseStep 652343 = 978515) B978515
theorem B1561673 : Blo 432776 1561673 := bstep (se 2 (by rfl) ⟨585627, by rfl⟩ : syracuseStep 1561673 = 1171255) B1171255
theorem B824393 : Blo 432776 824393 := bstep (se 2 (by rfl) ⟨309147, by rfl⟩ : syracuseStep 824393 = 618295) B618295
theorem B488623 : Blo 432776 488623 := bstep (se 1 (by rfl) ⟨366467, by rfl⟩ : syracuseStep 488623 = 732935) B732935
theorem B652463 : Blo 432776 652463 := bstep (se 1 (by rfl) ⟨489347, by rfl⟩ : syracuseStep 652463 = 978695) B978695
theorem B1463507 : Blo 432776 1463507 := bstep (se 1 (by rfl) ⟨1097630, by rfl⟩ : syracuseStep 1463507 = 2195261) B2195261
theorem B980243 : Blo 432776 980243 := bstep (se 1 (by rfl) ⟨735182, by rfl⟩ : syracuseStep 980243 = 1470365) B1470365
theorem B3437873 : Blo 432776 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B734555 : Blo 432776 734555 := bstep (se 1 (by rfl) ⟨550916, by rfl⟩ : syracuseStep 734555 = 1101833) B1101833
theorem B980315 : Blo 432776 980315 := bstep (se 1 (by rfl) ⟨735236, by rfl⟩ : syracuseStep 980315 = 1470473) B1470473
theorem B1463777 : Blo 432776 1463777 := bstep (se 2 (by rfl) ⟨548916, by rfl⟩ : syracuseStep 1463777 = 1097833) B1097833
theorem B12006893 : Blo 432776 12006893 := bstep (se 3 (by rfl) ⟨2251292, by rfl⟩ : syracuseStep 12006893 = 4502585) B4502585
theorem B652871 : Blo 432776 652871 := bstep (se 1 (by rfl) ⟨489653, by rfl⟩ : syracuseStep 652871 = 979307) B979307
theorem B734791 : Blo 432776 734791 := bstep (se 1 (by rfl) ⟨551093, by rfl⟩ : syracuseStep 734791 = 1102187) B1102187
theorem B325998229 : Blo 432776 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B489127 : Blo 432776 489127 := bstep (se 1 (by rfl) ⟨366845, by rfl⟩ : syracuseStep 489127 = 733691) B733691
theorem B652967 : Blo 432776 652967 := bstep (se 1 (by rfl) ⟨489725, by rfl⟩ : syracuseStep 652967 = 979451) B979451
theorem B3708605 : Blo 432776 3708605 := bstep (se 3 (by rfl) ⟨695363, by rfl⟩ : syracuseStep 3708605 = 1390727) B1390727
theorem B464635 : Blo 432776 464635 := bstep (se 1 (by rfl) ⟨348476, by rfl⟩ : syracuseStep 464635 = 696953) B696953
theorem B653051 : Blo 432776 653051 := bstep (se 1 (by rfl) ⟨489788, by rfl⟩ : syracuseStep 653051 = 979577) B979577
theorem B1046267 : Blo 432776 1046267 := bstep (se 1 (by rfl) ⟨784700, by rfl⟩ : syracuseStep 1046267 = 1569401) B1569401
theorem B653087 : Blo 432776 653087 := bstep (se 1 (by rfl) ⟨489815, by rfl⟩ : syracuseStep 653087 = 979631) B979631
theorem B735007 : Blo 432776 735007 := bstep (se 1 (by rfl) ⟨551255, by rfl⟩ : syracuseStep 735007 = 1102511) B1102511
theorem B653135 : Blo 432776 653135 := bstep (se 1 (by rfl) ⟨489851, by rfl⟩ : syracuseStep 653135 = 979703) B979703
theorem B489415 : Blo 432776 489415 := bstep (se 1 (by rfl) ⟨367061, by rfl⟩ : syracuseStep 489415 = 734123) B734123
theorem B653255 : Blo 432776 653255 := bstep (se 1 (by rfl) ⟨489941, by rfl⟩ : syracuseStep 653255 = 979883) B979883
theorem B825319 : Blo 432776 825319 := bstep (se 1 (by rfl) ⟨618989, by rfl⟩ : syracuseStep 825319 = 1237979) B1237979
theorem B735223 : Blo 432776 735223 := bstep (se 1 (by rfl) ⟨551417, by rfl⟩ : syracuseStep 735223 = 1102835) B1102835
theorem B1652795 : Blo 432776 1652795 := bstep (se 1 (by rfl) ⟨1239596, by rfl⟩ : syracuseStep 1652795 = 2479193) B2479193
theorem B7444547 : Blo 432776 7444547 := bstep (se 1 (by rfl) ⟨5583410, by rfl⟩ : syracuseStep 7444547 = 11166821) B11166821
theorem B1464425 : Blo 432776 1464425 := bstep (se 2 (by rfl) ⟨549159, by rfl⟩ : syracuseStep 1464425 = 1098319) B1098319
theorem B2193641 : Blo 432776 2193641 := bstep (se 2 (by rfl) ⟨822615, by rfl⟩ : syracuseStep 2193641 = 1645231) B1645231
theorem B8444189 : Blo 432776 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B653609 : Blo 432776 653609 := bstep (se 2 (by rfl) ⟨245103, by rfl⟩ : syracuseStep 653609 = 490207) B490207
theorem B489775 : Blo 432776 489775 := bstep (se 1 (by rfl) ⟨367331, by rfl⟩ : syracuseStep 489775 = 734663) B734663
theorem B653615 : Blo 432776 653615 := bstep (se 1 (by rfl) ⟨490211, by rfl⟩ : syracuseStep 653615 = 980423) B980423
theorem B1055099 : Blo 432776 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B3955067 : Blo 432776 3955067 := bstep (se 1 (by rfl) ⟨2966300, by rfl⟩ : syracuseStep 3955067 = 5932601) B5932601
theorem B1391023 : Blo 432776 1391023 := bstep (se 1 (by rfl) ⟨1043267, by rfl⟩ : syracuseStep 1391023 = 2086535) B2086535
theorem B2775485 : Blo 432776 2775485 := bstep (se 3 (by rfl) ⟨520403, by rfl⟩ : syracuseStep 2775485 = 1040807) B1040807
theorem B5945845 : Blo 432776 5945845 := bstep (se 5 (by rfl) ⟨278711, by rfl⟩ : syracuseStep 5945845 = 557423) B557423
theorem B102816289 : Blo 432776 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B6282035 : Blo 432776 6282035 := bstep (se 1 (by rfl) ⟨4711526, by rfl⟩ : syracuseStep 6282035 = 9423053) B9423053
theorem B432987 : Blo 432776 432987 := bstep (se 1 (by rfl) ⟨324740, by rfl⟩ : syracuseStep 432987 = 649481) B649481
theorem B433055 : Blo 432776 433055 := bstep (se 1 (by rfl) ⟨324791, by rfl⟩ : syracuseStep 433055 = 649583) B649583
theorem B588703 : Blo 432776 588703 := bstep (se 1 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 588703 = 883055) B883055
theorem B4684709 : Blo 432776 4684709 := bstep (se 4 (by rfl) ⟨439191, by rfl⟩ : syracuseStep 4684709 = 878383) B878383
theorem B1465289 : Blo 432776 1465289 := bstep (se 2 (by rfl) ⟨549483, by rfl⟩ : syracuseStep 1465289 = 1098967) B1098967
theorem B924623 : Blo 432776 924623 := bstep (se 1 (by rfl) ⟨693467, by rfl⟩ : syracuseStep 924623 = 1386935) B1386935
theorem B433199 : Blo 432776 433199 := bstep (se 1 (by rfl) ⟨324899, by rfl⟩ : syracuseStep 433199 = 649799) B649799
theorem B556079 : Blo 432776 556079 := bstep (se 1 (by rfl) ⟨417059, by rfl⟩ : syracuseStep 556079 = 834119) B834119
theorem B433223 : Blo 432776 433223 := bstep (se 1 (by rfl) ⟨324917, by rfl⟩ : syracuseStep 433223 = 649835) B649835
theorem B2514059 : Blo 432776 2514059 := bstep (se 1 (by rfl) ⟨1885544, by rfl⟩ : syracuseStep 2514059 = 3771089) B3771089
theorem B1465559 : Blo 432776 1465559 := bstep (se 1 (by rfl) ⟨1099169, by rfl⟩ : syracuseStep 1465559 = 2198339) B2198339
theorem B433375 : Blo 432776 433375 := bstep (se 1 (by rfl) ⟨325031, by rfl⟩ : syracuseStep 433375 = 650063) B650063
theorem B2637095 : Blo 432776 2637095 := bstep (se 1 (by rfl) ⟨1977821, by rfl⟩ : syracuseStep 2637095 = 3955643) B3955643
theorem B433639 : Blo 432776 433639 := bstep (se 1 (by rfl) ⟨325229, by rfl⟩ : syracuseStep 433639 = 650459) B650459
theorem B433755 : Blo 432776 433755 := bstep (se 1 (by rfl) ⟨325316, by rfl⟩ : syracuseStep 433755 = 650633) B650633
theorem B2784941 : Blo 432776 2784941 := bstep (se 3 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 2784941 = 1044353) B1044353
theorem B1097459 : Blo 432776 1097459 := bstep (se 1 (by rfl) ⟨823094, by rfl⟩ : syracuseStep 1097459 = 1646189) B1646189
theorem B1466099 : Blo 432776 1466099 := bstep (se 1 (by rfl) ⟨1099574, by rfl⟩ : syracuseStep 1466099 = 2199149) B2199149
theorem B974663 : Blo 432776 974663 := bstep (se 1 (by rfl) ⟨730997, by rfl⟩ : syracuseStep 974663 = 1461995) B1461995
theorem B925511 : Blo 432776 925511 := bstep (se 1 (by rfl) ⟨694133, by rfl⟩ : syracuseStep 925511 = 1388267) B1388267
theorem B433991 : Blo 432776 433991 := bstep (se 1 (by rfl) ⟨325493, by rfl⟩ : syracuseStep 433991 = 650987) B650987
theorem B12009323 : Blo 432776 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B1982333 : Blo 432776 1982333 := bstep (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) B743375
theorem B434143 : Blo 432776 434143 := bstep (se 1 (by rfl) ⟨325607, by rfl⟩ : syracuseStep 434143 = 651215) B651215
theorem B7929971 : Blo 432776 7929971 := bstep (se 1 (by rfl) ⟨5947478, by rfl⟩ : syracuseStep 7929971 = 11894957) B11894957
theorem B1482877 : Blo 432776 1482877 := bstep (se 3 (by rfl) ⟨278039, by rfl⟩ : syracuseStep 1482877 = 556079) B556079
theorem B434367 : Blo 432776 434367 := bstep (se 1 (by rfl) ⟨325775, by rfl⟩ : syracuseStep 434367 = 651551) B651551
theorem B5431499 : Blo 432776 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B434383 : Blo 432776 434383 := bstep (se 1 (by rfl) ⟨325787, by rfl⟩ : syracuseStep 434383 = 651575) B651575
theorem B1974503 : Blo 432776 1974503 := bstep (se 1 (by rfl) ⟨1480877, by rfl⟩ : syracuseStep 1974503 = 2961755) B2961755
theorem B1982713 : Blo 432776 1982713 := bstep (se 2 (by rfl) ⟨743517, by rfl⟩ : syracuseStep 1982713 = 1487035) B1487035
theorem B549119 : Blo 432776 549119 := bstep (se 1 (by rfl) ⟨411839, by rfl⟩ : syracuseStep 549119 = 823679) B823679
theorem B434431 : Blo 432776 434431 := bstep (se 1 (by rfl) ⟨325823, by rfl⟩ : syracuseStep 434431 = 651647) B651647
theorem B434479 : Blo 432776 434479 := bstep (se 1 (by rfl) ⟨325859, by rfl⟩ : syracuseStep 434479 = 651719) B651719
theorem B1761697 : Blo 432776 1761697 := bstep (se 2 (by rfl) ⟨660636, by rfl⟩ : syracuseStep 1761697 = 1321273) B1321273
theorem B434715 : Blo 432776 434715 := bstep (se 1 (by rfl) ⟨326036, by rfl⟩ : syracuseStep 434715 = 652073) B652073
theorem B434719 : Blo 432776 434719 := bstep (se 1 (by rfl) ⟨326039, by rfl⟩ : syracuseStep 434719 = 652079) B652079
theorem B950887 : Blo 432776 950887 := bstep (se 1 (by rfl) ⟨713165, by rfl⟩ : syracuseStep 950887 = 1426331) B1426331
theorem B2638439 : Blo 432776 2638439 := bstep (se 1 (by rfl) ⟨1978829, by rfl⟩ : syracuseStep 2638439 = 3957659) B3957659
theorem B434799 : Blo 432776 434799 := bstep (se 1 (by rfl) ⟨326099, by rfl⟩ : syracuseStep 434799 = 652199) B652199
theorem B975527 : Blo 432776 975527 := bstep (se 1 (by rfl) ⟨731645, by rfl⟩ : syracuseStep 975527 = 1463291) B1463291
theorem B434855 : Blo 432776 434855 := bstep (se 1 (by rfl) ⟨326141, by rfl⟩ : syracuseStep 434855 = 652283) B652283
theorem B434895 : Blo 432776 434895 := bstep (se 1 (by rfl) ⟨326171, by rfl⟩ : syracuseStep 434895 = 652343) B652343
theorem B1041115 : Blo 432776 1041115 := bstep (se 1 (by rfl) ⟨780836, by rfl⟩ : syracuseStep 1041115 = 1561673) B1561673
theorem B549595 : Blo 432776 549595 := bstep (se 1 (by rfl) ⟨412196, by rfl⟩ : syracuseStep 549595 = 824393) B824393
theorem B434975 : Blo 432776 434975 := bstep (se 1 (by rfl) ⟨326231, by rfl⟩ : syracuseStep 434975 = 652463) B652463
theorem B975671 : Blo 432776 975671 := bstep (se 1 (by rfl) ⟨731753, by rfl⟩ : syracuseStep 975671 = 1463507) B1463507
theorem B2474819 : Blo 432776 2474819 := bstep (se 1 (by rfl) ⟨1856114, by rfl⟩ : syracuseStep 2474819 = 3712229) B3712229
theorem B3294107 : Blo 432776 3294107 := bstep (se 1 (by rfl) ⟨2470580, by rfl⟩ : syracuseStep 3294107 = 4941161) B4941161
theorem B975851 : Blo 432776 975851 := bstep (se 1 (by rfl) ⟨731888, by rfl⟩ : syracuseStep 975851 = 1463777) B1463777
theorem B8004595 : Blo 432776 8004595 := bstep (se 1 (by rfl) ⟨6003446, by rfl⟩ : syracuseStep 8004595 = 12006893) B12006893
theorem B435247 : Blo 432776 435247 := bstep (se 1 (by rfl) ⟨326435, by rfl⟩ : syracuseStep 435247 = 652871) B652871
theorem B435311 : Blo 432776 435311 := bstep (se 1 (by rfl) ⟨326483, by rfl⟩ : syracuseStep 435311 = 652967) B652967
theorem B435367 : Blo 432776 435367 := bstep (se 1 (by rfl) ⟨326525, by rfl⟩ : syracuseStep 435367 = 653051) B653051
theorem B697511 : Blo 432776 697511 := bstep (se 1 (by rfl) ⟨523133, by rfl⟩ : syracuseStep 697511 = 1046267) B1046267
theorem B435391 : Blo 432776 435391 := bstep (se 1 (by rfl) ⟨326543, by rfl⟩ : syracuseStep 435391 = 653087) B653087
theorem B435423 : Blo 432776 435423 := bstep (se 1 (by rfl) ⟨326567, by rfl⟩ : syracuseStep 435423 = 653135) B653135
theorem B435503 : Blo 432776 435503 := bstep (se 1 (by rfl) ⟨326627, by rfl⟩ : syracuseStep 435503 = 653255) B653255
theorem B976283 : Blo 432776 976283 := bstep (se 1 (by rfl) ⟨732212, by rfl⟩ : syracuseStep 976283 = 1464425) B1464425
theorem B5629459 : Blo 432776 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B435739 : Blo 432776 435739 := bstep (se 1 (by rfl) ⟨326804, by rfl⟩ : syracuseStep 435739 = 653609) B653609
theorem B435743 : Blo 432776 435743 := bstep (se 1 (by rfl) ⟨326807, by rfl⟩ : syracuseStep 435743 = 653615) B653615
theorem B2197043 : Blo 432776 2197043 := bstep (se 1 (by rfl) ⟨1647782, by rfl⟩ : syracuseStep 2197043 = 3295565) B3295565
theorem B5867113 : Blo 432776 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B16910045 : Blo 432776 16910045 := bstep (se 3 (by rfl) ⟨3170633, by rfl⟩ : syracuseStep 16910045 = 6341267) B6341267
theorem B6686479 : Blo 432776 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B12732203 : Blo 432776 12732203 := bstep (se 1 (by rfl) ⟨9549152, by rfl⟩ : syracuseStep 12732203 = 19098305) B19098305
theorem B4188023 : Blo 432776 4188023 := bstep (se 1 (by rfl) ⟨3141017, by rfl⟩ : syracuseStep 4188023 = 6282035) B6282035
theorem B3123139 : Blo 432776 3123139 := bstep (se 1 (by rfl) ⟨2342354, by rfl⟩ : syracuseStep 3123139 = 4684709) B4684709
theorem B976859 : Blo 432776 976859 := bstep (se 1 (by rfl) ⟨732644, by rfl⟩ : syracuseStep 976859 = 1465289) B1465289
theorem B616415 : Blo 432776 616415 := bstep (se 1 (by rfl) ⟨462311, by rfl⟩ : syracuseStep 616415 = 924623) B924623
theorem B550891 : Blo 432776 550891 := bstep (se 1 (by rfl) ⟨413168, by rfl⟩ : syracuseStep 550891 = 826337) B826337
theorem B28149767 : Blo 432776 28149767 := bstep (se 1 (by rfl) ⟨21112325, by rfl⟩ : syracuseStep 28149767 = 42224651) B42224651
theorem B6883379 : Blo 432776 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B649337 : Blo 432776 649337 := bstep (se 2 (by rfl) ⟨243501, by rfl⟩ : syracuseStep 649337 = 487003) B487003
theorem B977039 : Blo 432776 977039 := bstep (se 1 (by rfl) ⟨732779, by rfl⟩ : syracuseStep 977039 = 1465559) B1465559
theorem B2468029 : Blo 432776 2468029 := bstep (se 3 (by rfl) ⟨462755, by rfl⟩ : syracuseStep 2468029 = 925511) B925511
theorem B977129 : Blo 432776 977129 := bstep (se 2 (by rfl) ⟨366423, by rfl⟩ : syracuseStep 977129 = 732847) B732847
theorem B5286221 : Blo 432776 5286221 := bstep (se 3 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 5286221 = 1982333) B1982333
theorem B3967321 : Blo 432776 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B731639 : Blo 432776 731639 := bstep (se 1 (by rfl) ⟨548729, by rfl⟩ : syracuseStep 731639 = 1097459) B1097459
theorem B977399 : Blo 432776 977399 := bstep (se 1 (by rfl) ⟨733049, by rfl⟩ : syracuseStep 977399 = 1466099) B1466099
theorem B649721 : Blo 432776 649721 := bstep (se 2 (by rfl) ⟨243645, by rfl⟩ : syracuseStep 649721 = 487291) B487291
theorem B649775 : Blo 432776 649775 := bstep (se 1 (by rfl) ⟨487331, by rfl⟩ : syracuseStep 649775 = 974663) B974663
theorem B8006215 : Blo 432776 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B1100425 : Blo 432776 1100425 := bstep (se 2 (by rfl) ⟨412659, by rfl⟩ : syracuseStep 1100425 = 825319) B825319
theorem B6261623 : Blo 432776 6261623 := bstep (se 1 (by rfl) ⟨4696217, by rfl⟩ : syracuseStep 6261623 = 9392435) B9392435
theorem B650207 : Blo 432776 650207 := bstep (se 1 (by rfl) ⟨487655, by rfl⟩ : syracuseStep 650207 = 975311) B975311
theorem B936955 : Blo 432776 936955 := bstep (se 1 (by rfl) ⟨702716, by rfl⟩ : syracuseStep 936955 = 1405433) B1405433
theorem B2477051 : Blo 432776 2477051 := bstep (se 1 (by rfl) ⟨1857788, by rfl⟩ : syracuseStep 2477051 = 3715577) B3715577
theorem B732233 : Blo 432776 732233 := bstep (se 2 (by rfl) ⟨274587, by rfl⟩ : syracuseStep 732233 = 549175) B549175
theorem B977993 : Blo 432776 977993 := bstep (se 2 (by rfl) ⟨366747, by rfl⟩ : syracuseStep 977993 = 733495) B733495
theorem B937067 : Blo 432776 937067 := bstep (se 1 (by rfl) ⟨702800, by rfl⟩ : syracuseStep 937067 = 1405601) B1405601
theorem B1674361 : Blo 432776 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B2468987 : Blo 432776 2468987 := bstep (se 1 (by rfl) ⟨1851740, by rfl⟩ : syracuseStep 2468987 = 3703481) B3703481
theorem B2198663 : Blo 432776 2198663 := bstep (se 1 (by rfl) ⟨1648997, by rfl⟩ : syracuseStep 2198663 = 3297995) B3297995
theorem B8342675 : Blo 432776 8342675 := bstep (se 1 (by rfl) ⟨6257006, by rfl⟩ : syracuseStep 8342675 = 12514013) B12514013
theorem B1469609 : Blo 432776 1469609 := bstep (se 2 (by rfl) ⟨551103, by rfl⟩ : syracuseStep 1469609 = 1102207) B1102207
theorem B1854697 : Blo 432776 1854697 := bstep (se 2 (by rfl) ⟨695511, by rfl⟩ : syracuseStep 1854697 = 1391023) B1391023
theorem B2084093 : Blo 432776 2084093 := bstep (se 3 (by rfl) ⟨390767, by rfl⟩ : syracuseStep 2084093 = 781535) B781535
theorem B42249559 : Blo 432776 42249559 := bstep (se 1 (by rfl) ⟨31687169, by rfl⟩ : syracuseStep 42249559 = 63374339) B63374339
theorem B137088385 : Blo 432776 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B601499 : Blo 432776 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B650651 : Blo 432776 650651 := bstep (se 1 (by rfl) ⟨487988, by rfl⟩ : syracuseStep 650651 = 975977) B975977
theorem B7032253 : Blo 432776 7032253 := bstep (se 3 (by rfl) ⟨1318547, by rfl⟩ : syracuseStep 7032253 = 2637095) B2637095
theorem B3714619 : Blo 432776 3714619 := bstep (se 1 (by rfl) ⟨2785964, by rfl⟩ : syracuseStep 3714619 = 5571929) B5571929
theorem B1240667 : Blo 432776 1240667 := bstep (se 1 (by rfl) ⟨930500, by rfl⟩ : syracuseStep 1240667 = 1861001) B1861001
theorem B3288761 : Blo 432776 3288761 := bstep (se 2 (by rfl) ⟨1233285, by rfl⟩ : syracuseStep 3288761 = 2466571) B2466571
theorem B1470203 : Blo 432776 1470203 := bstep (se 1 (by rfl) ⟨1102652, by rfl⟩ : syracuseStep 1470203 = 2205305) B2205305
theorem B651071 : Blo 432776 651071 := bstep (se 1 (by rfl) ⟨488303, by rfl⟩ : syracuseStep 651071 = 976607) B976607
theorem B2633593 : Blo 432776 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B2478053 : Blo 432776 2478053 := bstep (se 4 (by rfl) ⟨232317, by rfl⟩ : syracuseStep 2478053 = 464635) B464635
theorem B520187 : Blo 432776 520187 := bstep (se 1 (by rfl) ⟨390140, by rfl⟩ : syracuseStep 520187 = 780281) B780281
theorem B651257 : Blo 432776 651257 := bstep (se 2 (by rfl) ⟨244221, by rfl⟩ : syracuseStep 651257 = 488443) B488443
theorem B1101863 : Blo 432776 1101863 := bstep (se 1 (by rfl) ⟨826397, by rfl⟩ : syracuseStep 1101863 = 1652795) B1652795
theorem B26816629 : Blo 432776 26816629 := bstep (se 5 (by rfl) ⟨1257029, by rfl⟩ : syracuseStep 26816629 = 2514059) B2514059
theorem B1462427 : Blo 432776 1462427 := bstep (se 1 (by rfl) ⟨1096820, by rfl⟩ : syracuseStep 1462427 = 2193641) B2193641
theorem B487579 : Blo 432776 487579 := bstep (se 1 (by rfl) ⟨365684, by rfl⟩ : syracuseStep 487579 = 731369) B731369
theorem B651497 : Blo 432776 651497 := bstep (se 2 (by rfl) ⟨244311, by rfl⟩ : syracuseStep 651497 = 488623) B488623
theorem B651623 : Blo 432776 651623 := bstep (se 1 (by rfl) ⟨488717, by rfl⟩ : syracuseStep 651623 = 977435) B977435
theorem B2191859 : Blo 432776 2191859 := bstep (se 1 (by rfl) ⟨1643894, by rfl⟩ : syracuseStep 2191859 = 3287789) B3287789
theorem B5026319 : Blo 432776 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B823945 : Blo 432776 823945 := bstep (se 2 (by rfl) ⟨308979, by rfl⟩ : syracuseStep 823945 = 617959) B617959
theorem B979721 : Blo 432776 979721 := bstep (se 2 (by rfl) ⟨367395, by rfl⟩ : syracuseStep 979721 = 734791) B734791
theorem B734015 : Blo 432776 734015 := bstep (se 1 (by rfl) ⟨550511, by rfl⟩ : syracuseStep 734015 = 1101023) B1101023
theorem B979775 : Blo 432776 979775 := bstep (se 1 (by rfl) ⟨734831, by rfl⟩ : syracuseStep 979775 = 1469663) B1469663
theorem B434664305 : Blo 432776 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B8893313 : Blo 432776 8893313 := bstep (se 2 (by rfl) ⟨3334992, by rfl⟩ : syracuseStep 8893313 = 6669985) B6669985
theorem B652169 : Blo 432776 652169 := bstep (se 2 (by rfl) ⟨244563, by rfl⟩ : syracuseStep 652169 = 489127) B489127
theorem B734089 : Blo 432776 734089 := bstep (se 2 (by rfl) ⟨275283, by rfl⟩ : syracuseStep 734089 = 550567) B550567
theorem B2233261 : Blo 432776 2233261 := bstep (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) B837473
theorem B979919 : Blo 432776 979919 := bstep (se 1 (by rfl) ⟨734939, by rfl⟩ : syracuseStep 979919 = 1469879) B1469879
theorem B9409553 : Blo 432776 9409553 := bstep (se 2 (by rfl) ⟨3528582, by rfl⟩ : syracuseStep 9409553 = 7057165) B7057165
theorem B980009 : Blo 432776 980009 := bstep (se 2 (by rfl) ⟨367503, by rfl⟩ : syracuseStep 980009 = 735007) B735007
theorem B1856627 : Blo 432776 1856627 := bstep (se 1 (by rfl) ⟨1392470, by rfl⟩ : syracuseStep 1856627 = 2784941) B2784941
theorem B783611 : Blo 432776 783611 := bstep (se 1 (by rfl) ⟨587708, by rfl⟩ : syracuseStep 783611 = 1175417) B1175417
theorem B652553 : Blo 432776 652553 := bstep (se 2 (by rfl) ⟨244707, by rfl⟩ : syracuseStep 652553 = 489415) B489415
theorem B2192669 : Blo 432776 2192669 := bstep (se 3 (by rfl) ⟨411125, by rfl⟩ : syracuseStep 2192669 = 822251) B822251
theorem B488767 : Blo 432776 488767 := bstep (se 1 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 488767 = 733151) B733151
theorem B652607 : Blo 432776 652607 := bstep (se 1 (by rfl) ⟨489455, by rfl⟩ : syracuseStep 652607 = 978911) B978911
theorem B980297 : Blo 432776 980297 := bstep (se 2 (by rfl) ⟨367611, by rfl⟩ : syracuseStep 980297 = 735223) B735223
theorem B2340193 : Blo 432776 2340193 := bstep (se 2 (by rfl) ⟨877572, by rfl⟩ : syracuseStep 2340193 = 1755145) B1755145
theorem B2782583 : Blo 432776 2782583 := bstep (se 1 (by rfl) ⟨2086937, by rfl⟩ : syracuseStep 2782583 = 4173875) B4173875
theorem B1652339 : Blo 432776 1652339 := bstep (se 1 (by rfl) ⟨1239254, by rfl⟩ : syracuseStep 1652339 = 2478509) B2478509
theorem B3135133 : Blo 432776 3135133 := bstep (se 3 (by rfl) ⟨587837, by rfl⟩ : syracuseStep 3135133 = 1175675) B1175675
theorem B653033 : Blo 432776 653033 := bstep (se 2 (by rfl) ⟨244887, by rfl⟩ : syracuseStep 653033 = 489775) B489775
theorem B734953 : Blo 432776 734953 := bstep (se 2 (by rfl) ⟨275607, by rfl⟩ : syracuseStep 734953 = 551215) B551215
theorem B489199 : Blo 432776 489199 := bstep (se 1 (by rfl) ⟨366899, by rfl⟩ : syracuseStep 489199 = 733799) B733799
theorem B653039 : Blo 432776 653039 := bstep (se 1 (by rfl) ⟨489779, by rfl⟩ : syracuseStep 653039 = 979559) B979559
theorem B1652521 : Blo 432776 1652521 := bstep (se 2 (by rfl) ⟨619695, by rfl⟩ : syracuseStep 1652521 = 1239391) B1239391
theorem B1341263 : Blo 432776 1341263 := bstep (se 1 (by rfl) ⟨1005947, by rfl⟩ : syracuseStep 1341263 = 2011895) B2011895
theorem B1464155 : Blo 432776 1464155 := bstep (se 1 (by rfl) ⟨1098116, by rfl⟩ : syracuseStep 1464155 = 2196233) B2196233
theorem B489307 : Blo 432776 489307 := bstep (se 1 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 489307 = 733961) B733961
theorem B1587073 : Blo 432776 1587073 := bstep (se 2 (by rfl) ⟨595152, by rfl⟩ : syracuseStep 1587073 = 1190305) B1190305
theorem B7927793 : Blo 432776 7927793 := bstep (se 2 (by rfl) ⟨2972922, by rfl⟩ : syracuseStep 7927793 = 5945845) B5945845
theorem B2676833 : Blo 432776 2676833 := bstep (se 2 (by rfl) ⟨1003812, by rfl⟩ : syracuseStep 2676833 = 2007625) B2007625
theorem B653495 : Blo 432776 653495 := bstep (se 1 (by rfl) ⟨490121, by rfl⟩ : syracuseStep 653495 = 980243) B980243
theorem B4167875 : Blo 432776 4167875 := bstep (se 1 (by rfl) ⟨3125906, by rfl⟩ : syracuseStep 4167875 = 6251813) B6251813
theorem B2291915 : Blo 432776 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B1857755 : Blo 432776 1857755 := bstep (se 1 (by rfl) ⟨1393316, by rfl⟩ : syracuseStep 1857755 = 2786633) B2786633
theorem B489703 : Blo 432776 489703 := bstep (se 1 (by rfl) ⟨367277, by rfl⟩ : syracuseStep 489703 = 734555) B734555
theorem B653543 : Blo 432776 653543 := bstep (se 1 (by rfl) ⟨490157, by rfl⟩ : syracuseStep 653543 = 980315) B980315
theorem B2472221 : Blo 432776 2472221 := bstep (se 3 (by rfl) ⟨463541, by rfl⟩ : syracuseStep 2472221 = 927083) B927083
theorem B2472403 : Blo 432776 2472403 := bstep (se 1 (by rfl) ⟨1854302, by rfl⟩ : syracuseStep 2472403 = 3708605) B3708605
theorem B784937 : Blo 432776 784937 := bstep (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) B588703
theorem B432799 : Blo 432776 432799 := bstep (se 1 (by rfl) ⟨324599, by rfl⟩ : syracuseStep 432799 = 649199) B649199
theorem B4963031 : Blo 432776 4963031 := bstep (se 1 (by rfl) ⟨3722273, by rfl⟩ : syracuseStep 4963031 = 7444547) B7444547
theorem B670441 : Blo 432776 670441 := bstep (se 2 (by rfl) ⟨251415, by rfl⟩ : syracuseStep 670441 = 502831) B502831
theorem B432967 : Blo 432776 432967 := bstep (se 1 (by rfl) ⟨324725, by rfl⟩ : syracuseStep 432967 = 649451) B649451
theorem B433007 : Blo 432776 433007 := bstep (se 1 (by rfl) ⟨324755, by rfl⟩ : syracuseStep 433007 = 649511) B649511
theorem B433063 : Blo 432776 433063 := bstep (se 1 (by rfl) ⟨324797, by rfl⟩ : syracuseStep 433063 = 649595) B649595
theorem B703399 : Blo 432776 703399 := bstep (se 1 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 703399 = 1055099) B1055099
theorem B2636711 : Blo 432776 2636711 := bstep (se 1 (by rfl) ⟨1977533, by rfl⟩ : syracuseStep 2636711 = 3955067) B3955067
theorem B1850323 : Blo 432776 1850323 := bstep (se 1 (by rfl) ⟨1387742, by rfl⟩ : syracuseStep 1850323 = 2775485) B2775485
theorem B104225753 : Blo 432776 104225753 := bstep (se 2 (by rfl) ⟨39084657, by rfl⟩ : syracuseStep 104225753 = 78169315) B78169315
theorem B973871 : Blo 432776 973871 := bstep (se 1 (by rfl) ⟨730403, by rfl⟩ : syracuseStep 973871 = 1460807) B1460807
theorem B433243 : Blo 432776 433243 := bstep (se 1 (by rfl) ⟨324932, by rfl⟩ : syracuseStep 433243 = 649865) B649865
theorem B1645703 : Blo 432776 1645703 := bstep (se 1 (by rfl) ⟨1234277, by rfl⟩ : syracuseStep 1645703 = 2468555) B2468555
theorem B433359 : Blo 432776 433359 := bstep (se 1 (by rfl) ⟨325019, by rfl⟩ : syracuseStep 433359 = 650039) B650039
theorem B433383 : Blo 432776 433383 := bstep (se 1 (by rfl) ⟨325037, by rfl⟩ : syracuseStep 433383 = 650075) B650075
theorem B433479 : Blo 432776 433479 := bstep (se 1 (by rfl) ⟨325109, by rfl⟩ : syracuseStep 433479 = 650219) B650219
theorem B433615 : Blo 432776 433615 := bstep (se 1 (by rfl) ⟨325211, by rfl⟩ : syracuseStep 433615 = 650423) B650423
theorem B433775 : Blo 432776 433775 := bstep (se 1 (by rfl) ⟨325331, by rfl⟩ : syracuseStep 433775 = 650663) B650663
theorem B433831 : Blo 432776 433831 := bstep (se 1 (by rfl) ⟨325373, by rfl⟩ : syracuseStep 433831 = 650747) B650747
theorem B1236647 : Blo 432776 1236647 := bstep (se 1 (by rfl) ⟨927485, by rfl⟩ : syracuseStep 1236647 = 1854971) B1854971
theorem B974555 : Blo 432776 974555 := bstep (se 1 (by rfl) ⟨730916, by rfl⟩ : syracuseStep 974555 = 1461833) B1461833
theorem B433895 : Blo 432776 433895 := bstep (se 1 (by rfl) ⟨325421, by rfl⟩ : syracuseStep 433895 = 650843) B650843
theorem B433951 : Blo 432776 433951 := bstep (se 1 (by rfl) ⟨325463, by rfl⟩ : syracuseStep 433951 = 650927) B650927
theorem B2776943 : Blo 432776 2776943 := bstep (se 1 (by rfl) ⟨2082707, by rfl⟩ : syracuseStep 2776943 = 4165415) B4165415
theorem B434031 : Blo 432776 434031 := bstep (se 1 (by rfl) ⟨325523, by rfl⟩ : syracuseStep 434031 = 651047) B651047
theorem B434087 : Blo 432776 434087 := bstep (se 1 (by rfl) ⟨325565, by rfl⟩ : syracuseStep 434087 = 651131) B651131
theorem B1646507 : Blo 432776 1646507 := bstep (se 1 (by rfl) ⟨1234880, by rfl⟩ : syracuseStep 1646507 = 2469761) B2469761
theorem B974825 : Blo 432776 974825 := bstep (se 2 (by rfl) ⟨365559, by rfl⟩ : syracuseStep 974825 = 731119) B731119
theorem B2924552213 : Blo 432776 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B974951 : Blo 432776 974951 := bstep (se 1 (by rfl) ⟨731213, by rfl⟩ : syracuseStep 974951 = 1462427) B1462427
theorem B3620999 : Blo 432776 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B434331 : Blo 432776 434331 := bstep (se 1 (by rfl) ⟨325748, by rfl⟩ : syracuseStep 434331 = 651497) B651497
theorem B434415 : Blo 432776 434415 := bstep (se 1 (by rfl) ⟨325811, by rfl⟩ : syracuseStep 434415 = 651623) B651623
theorem B2498845 : Blo 432776 2498845 := bstep (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) B937067
theorem B3350879 : Blo 432776 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B1860029 : Blo 432776 1860029 := bstep (se 3 (by rfl) ⟨348755, by rfl⟩ : syracuseStep 1860029 = 697511) B697511
theorem B6111773 : Blo 432776 6111773 := bstep (se 3 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 6111773 = 2291915) B2291915
theorem B289776203 : Blo 432776 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B434779 : Blo 432776 434779 := bstep (se 1 (by rfl) ⟨326084, by rfl⟩ : syracuseStep 434779 = 652169) B652169
theorem B2196071 : Blo 432776 2196071 := bstep (se 1 (by rfl) ⟨1647053, by rfl⟩ : syracuseStep 2196071 = 3294107) B3294107
theorem B8929925 : Blo 432776 8929925 := bstep (se 4 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 8929925 = 1674361) B1674361
theorem B1237751 : Blo 432776 1237751 := bstep (se 1 (by rfl) ⟨928313, by rfl⟩ : syracuseStep 1237751 = 1856627) B1856627
theorem B10674953 : Blo 432776 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B435035 : Blo 432776 435035 := bstep (se 1 (by rfl) ⟨326276, by rfl⟩ : syracuseStep 435035 = 652553) B652553
theorem B1098593 : Blo 432776 1098593 := bstep (se 2 (by rfl) ⟨411972, by rfl⟩ : syracuseStep 1098593 = 823945) B823945
theorem B1467233 : Blo 432776 1467233 := bstep (se 2 (by rfl) ⟨550212, by rfl⟩ : syracuseStep 1467233 = 1100425) B1100425
theorem B435071 : Blo 432776 435071 := bstep (se 1 (by rfl) ⟨326303, by rfl⟩ : syracuseStep 435071 = 652607) B652607
theorem B893921 : Blo 432776 893921 := bstep (se 2 (by rfl) ⟨335220, by rfl⟩ : syracuseStep 893921 = 670441) B670441
theorem B11273363 : Blo 432776 11273363 := bstep (se 1 (by rfl) ⟨8455022, by rfl⟩ : syracuseStep 11273363 = 16910045) B16910045
theorem B435355 : Blo 432776 435355 := bstep (se 1 (by rfl) ⟨326516, by rfl⟩ : syracuseStep 435355 = 653033) B653033
theorem B435359 : Blo 432776 435359 := bstep (se 1 (by rfl) ⟨326519, by rfl⟩ : syracuseStep 435359 = 653039) B653039
theorem B894175 : Blo 432776 894175 := bstep (se 1 (by rfl) ⟨670631, by rfl⟩ : syracuseStep 894175 = 1341263) B1341263
theorem B976103 : Blo 432776 976103 := bstep (se 1 (by rfl) ⟨732077, by rfl⟩ : syracuseStep 976103 = 1464155) B1464155
theorem B2467097 : Blo 432776 2467097 := bstep (se 2 (by rfl) ⟨925161, by rfl⟩ : syracuseStep 2467097 = 1850323) B1850323
theorem B5285195 : Blo 432776 5285195 := bstep (se 1 (by rfl) ⟨3963896, by rfl⟩ : syracuseStep 5285195 = 7927793) B7927793
theorem B4588919 : Blo 432776 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B35661221 : Blo 432776 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B435663 : Blo 432776 435663 := bstep (se 1 (by rfl) ⟨326747, by rfl⟩ : syracuseStep 435663 = 653495) B653495
theorem B1238503 : Blo 432776 1238503 := bstep (se 1 (by rfl) ⟨928877, by rfl⟩ : syracuseStep 1238503 = 1857755) B1857755
theorem B435695 : Blo 432776 435695 := bstep (se 1 (by rfl) ⟨326771, by rfl⟩ : syracuseStep 435695 = 653543) B653543
theorem B1648147 : Blo 432776 1648147 := bstep (se 1 (by rfl) ⟨1236110, by rfl⟩ : syracuseStep 1648147 = 2472221) B2472221
theorem B3524147 : Blo 432776 3524147 := bstep (se 1 (by rfl) ⟨2643110, by rfl⟩ : syracuseStep 3524147 = 5286221) B5286221
theorem B7505945 : Blo 432776 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B649247 : Blo 432776 649247 := bstep (se 1 (by rfl) ⟨486935, by rfl⟩ : syracuseStep 649247 = 973871) B973871
theorem B4180177 : Blo 432776 4180177 := bstep (se 2 (by rfl) ⟨1567566, by rfl⟩ : syracuseStep 4180177 = 3135133) B3135133
theorem B649703 : Blo 432776 649703 := bstep (se 1 (by rfl) ⟨487277, by rfl⟩ : syracuseStep 649703 = 974555) B974555
theorem B2116097 : Blo 432776 2116097 := bstep (se 2 (by rfl) ⟨793536, by rfl⟩ : syracuseStep 2116097 = 1587073) B1587073
theorem B4164185 : Blo 432776 4164185 := bstep (se 2 (by rfl) ⟨1561569, by rfl⟩ : syracuseStep 4164185 = 3123139) B3123139
theorem B5548661 : Blo 432776 5548661 := bstep (se 5 (by rfl) ⟨260093, by rfl⟩ : syracuseStep 5548661 = 520187) B520187
theorem B649883 : Blo 432776 649883 := bstep (se 1 (by rfl) ⟨487412, by rfl⟩ : syracuseStep 649883 = 974825) B974825
theorem B5286647 : Blo 432776 5286647 := bstep (se 1 (by rfl) ⟨3964985, by rfl⟩ : syracuseStep 5286647 = 7929971) B7929971
theorem B1977169 : Blo 432776 1977169 := bstep (se 2 (by rfl) ⟨741438, by rfl⟩ : syracuseStep 1977169 = 1482877) B1482877
theorem B650105 : Blo 432776 650105 := bstep (se 2 (by rfl) ⟨243789, by rfl⟩ : syracuseStep 650105 = 487579) B487579
theorem B1461239 : Blo 432776 1461239 := bstep (se 1 (by rfl) ⟨1095929, by rfl⟩ : syracuseStep 1461239 = 2191859) B2191859
theorem B650351 : Blo 432776 650351 := bstep (se 1 (by rfl) ⟨487763, by rfl⟩ : syracuseStep 650351 = 975527) B975527
theorem B650447 : Blo 432776 650447 := bstep (se 1 (by rfl) ⟨487835, by rfl⟩ : syracuseStep 650447 = 975671) B975671
theorem B1649879 : Blo 432776 1649879 := bstep (se 1 (by rfl) ⟨1237409, by rfl⟩ : syracuseStep 1649879 = 2474819) B2474819
theorem B3296537 : Blo 432776 3296537 := bstep (se 2 (by rfl) ⟨1236201, by rfl⟩ : syracuseStep 3296537 = 2472403) B2472403
theorem B650567 : Blo 432776 650567 := bstep (se 1 (by rfl) ⟨487925, by rfl⟩ : syracuseStep 650567 = 975851) B975851
theorem B1461779 : Blo 432776 1461779 := bstep (se 1 (by rfl) ⟨1096334, by rfl⟩ : syracuseStep 1461779 = 2192669) B2192669
theorem B1855055 : Blo 432776 1855055 := bstep (se 1 (by rfl) ⟨1391291, by rfl⟩ : syracuseStep 1855055 = 2782583) B2782583
theorem B650855 : Blo 432776 650855 := bstep (se 1 (by rfl) ⟨488141, by rfl⟩ : syracuseStep 650855 = 976283) B976283
theorem B1388153 : Blo 432776 1388153 := bstep (se 2 (by rfl) ⟨520557, by rfl⟩ : syracuseStep 1388153 = 1041115) B1041115
theorem B732793 : Blo 432776 732793 := bstep (se 2 (by rfl) ⟨274797, by rfl⟩ : syracuseStep 732793 = 549595) B549595
theorem B1101559 : Blo 432776 1101559 := bstep (se 1 (by rfl) ⟨826169, by rfl⟩ : syracuseStep 1101559 = 1652339) B1652339
theorem B978785 : Blo 432776 978785 := bstep (se 2 (by rfl) ⟨367044, by rfl⟩ : syracuseStep 978785 = 734089) B734089
theorem B937865 : Blo 432776 937865 := bstep (se 2 (by rfl) ⟨351699, by rfl⟩ : syracuseStep 937865 = 703399) B703399
theorem B2977681 : Blo 432776 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B651239 : Blo 432776 651239 := bstep (se 1 (by rfl) ⟨488429, by rfl⟩ : syracuseStep 651239 = 976859) B976859
theorem B1249273 : Blo 432776 1249273 := bstep (se 2 (by rfl) ⟨468477, by rfl⟩ : syracuseStep 1249273 = 936955) B936955
theorem B651359 : Blo 432776 651359 := bstep (se 1 (by rfl) ⟨488519, by rfl⟩ : syracuseStep 651359 = 977039) B977039
theorem B2093165 : Blo 432776 2093165 := bstep (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) B784937
theorem B651419 : Blo 432776 651419 := bstep (se 1 (by rfl) ⟨488564, by rfl⟩ : syracuseStep 651419 = 977129) B977129
theorem B487759 : Blo 432776 487759 := bstep (se 1 (by rfl) ⟨365819, by rfl⟩ : syracuseStep 487759 = 731639) B731639
theorem B651599 : Blo 432776 651599 := bstep (se 1 (by rfl) ⟨488699, by rfl⟩ : syracuseStep 651599 = 977399) B977399
theorem B651689 : Blo 432776 651689 := bstep (se 2 (by rfl) ⟨244383, by rfl⟩ : syracuseStep 651689 = 488767) B488767
theorem B56332745 : Blo 432776 56332745 := bstep (se 2 (by rfl) ⟨21124779, by rfl⟩ : syracuseStep 56332745 = 42249559) B42249559
theorem B4174415 : Blo 432776 4174415 := bstep (se 1 (by rfl) ⟨3130811, by rfl⟩ : syracuseStep 4174415 = 6261623) B6261623
theorem B9376337 : Blo 432776 9376337 := bstep (se 2 (by rfl) ⟨3516126, by rfl⟩ : syracuseStep 9376337 = 7032253) B7032253
theorem B1757807 : Blo 432776 1757807 := bstep (se 1 (by rfl) ⟨1318355, by rfl⟩ : syracuseStep 1757807 = 2636711) B2636711
theorem B1651367 : Blo 432776 1651367 := bstep (se 1 (by rfl) ⟨1238525, by rfl⟩ : syracuseStep 1651367 = 2477051) B2477051
theorem B488155 : Blo 432776 488155 := bstep (se 1 (by rfl) ⟨366116, by rfl⟩ : syracuseStep 488155 = 732233) B732233
theorem B651995 : Blo 432776 651995 := bstep (se 1 (by rfl) ⟨488996, by rfl⟩ : syracuseStep 651995 = 977993) B977993
theorem B4952825 : Blo 432776 4952825 := bstep (se 2 (by rfl) ⟨1857309, by rfl⟩ : syracuseStep 4952825 = 3714619) B3714619
theorem B979739 : Blo 432776 979739 := bstep (se 1 (by rfl) ⟨734804, by rfl⟩ : syracuseStep 979739 = 1469609) B1469609
theorem B33952541 : Blo 432776 33952541 := bstep (se 3 (by rfl) ⟨6366101, by rfl⟩ : syracuseStep 33952541 = 12732203) B12732203
theorem B1389395 : Blo 432776 1389395 := bstep (se 1 (by rfl) ⟨1042046, by rfl⟩ : syracuseStep 1389395 = 2084093) B2084093
theorem B979937 : Blo 432776 979937 := bstep (se 2 (by rfl) ⟨367476, by rfl⟩ : syracuseStep 979937 = 734953) B734953
theorem B652265 : Blo 432776 652265 := bstep (se 2 (by rfl) ⟨244599, by rfl⟩ : syracuseStep 652265 = 489199) B489199
theorem B824431 : Blo 432776 824431 := bstep (se 1 (by rfl) ⟨618323, by rfl⟩ : syracuseStep 824431 = 1236647) B1236647
theorem B2192507 : Blo 432776 2192507 := bstep (se 1 (by rfl) ⟨1644380, by rfl⟩ : syracuseStep 2192507 = 3288761) B3288761
theorem B652409 : Blo 432776 652409 := bstep (se 2 (by rfl) ⟨244653, by rfl⟩ : syracuseStep 652409 = 489307) B489307
theorem B3511457 : Blo 432776 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B980135 : Blo 432776 980135 := bstep (se 1 (by rfl) ⟨735101, by rfl⟩ : syracuseStep 980135 = 1470203) B1470203
theorem B434171 : Blo 432776 434171 := bstep (se 1 (by rfl) ⟨325628, by rfl⟩ : syracuseStep 434171 = 651257) B651257
theorem B1643773 : Blo 432776 1643773 := bstep (se 3 (by rfl) ⟨308207, by rfl⟩ : syracuseStep 1643773 = 616415) B616415
theorem B734521 : Blo 432776 734521 := bstep (se 2 (by rfl) ⟨275445, by rfl⟩ : syracuseStep 734521 = 550891) B550891
theorem B1652035 : Blo 432776 1652035 := bstep (se 1 (by rfl) ⟨1239026, by rfl⟩ : syracuseStep 1652035 = 2478053) B2478053
theorem B734575 : Blo 432776 734575 := bstep (se 1 (by rfl) ⟨550931, by rfl⟩ : syracuseStep 734575 = 1101863) B1101863
theorem B1316335 : Blo 432776 1316335 := bstep (se 1 (by rfl) ⟨987251, by rfl⟩ : syracuseStep 1316335 = 1974503) B1974503
theorem B35755505 : Blo 432776 35755505 := bstep (se 2 (by rfl) ⟨13408314, by rfl⟩ : syracuseStep 35755505 = 26816629) B26816629
theorem B3290705 : Blo 432776 3290705 := bstep (se 2 (by rfl) ⟨1234014, by rfl⟩ : syracuseStep 3290705 = 2468029) B2468029
theorem B652937 : Blo 432776 652937 := bstep (se 2 (by rfl) ⟨244851, by rfl⟩ : syracuseStep 652937 = 489703) B489703
theorem B2643617 : Blo 432776 2643617 := bstep (se 2 (by rfl) ⟨991356, by rfl⟩ : syracuseStep 2643617 = 1982713) B1982713
theorem B1758959 : Blo 432776 1758959 := bstep (se 1 (by rfl) ⟨1319219, by rfl⟩ : syracuseStep 1758959 = 2638439) B2638439
theorem B5289761 : Blo 432776 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B11114333 : Blo 432776 11114333 := bstep (se 3 (by rfl) ⟨2083937, by rfl⟩ : syracuseStep 11114333 = 4167875) B4167875
theorem B653147 : Blo 432776 653147 := bstep (se 1 (by rfl) ⟨489860, by rfl⟩ : syracuseStep 653147 = 979721) B979721
theorem B2348929 : Blo 432776 2348929 := bstep (se 2 (by rfl) ⟨880848, by rfl⟩ : syracuseStep 2348929 = 1761697) B1761697
theorem B489343 : Blo 432776 489343 := bstep (se 1 (by rfl) ⟨367007, by rfl⟩ : syracuseStep 489343 = 734015) B734015
theorem B653183 : Blo 432776 653183 := bstep (se 1 (by rfl) ⟨489887, by rfl⟩ : syracuseStep 653183 = 979775) B979775
theorem B5928875 : Blo 432776 5928875 := bstep (se 1 (by rfl) ⟨4446656, by rfl⟩ : syracuseStep 5928875 = 8893313) B8893313
theorem B653279 : Blo 432776 653279 := bstep (se 1 (by rfl) ⟨489959, by rfl⟩ : syracuseStep 653279 = 979919) B979919
theorem B1464317 : Blo 432776 1464317 := bstep (se 3 (by rfl) ⟨274559, by rfl⟩ : syracuseStep 1464317 = 549119) B549119
theorem B6273035 : Blo 432776 6273035 := bstep (se 1 (by rfl) ⟨4704776, by rfl⟩ : syracuseStep 6273035 = 9409553) B9409553
theorem B653339 : Blo 432776 653339 := bstep (se 1 (by rfl) ⟨490004, by rfl⟩ : syracuseStep 653339 = 980009) B980009
theorem B1267849 : Blo 432776 1267849 := bstep (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) B950887
theorem B522407 : Blo 432776 522407 := bstep (se 1 (by rfl) ⟨391805, by rfl⟩ : syracuseStep 522407 = 783611) B783611
theorem B653531 : Blo 432776 653531 := bstep (se 1 (by rfl) ⟨490148, by rfl⟩ : syracuseStep 653531 = 980297) B980297
theorem B1464695 : Blo 432776 1464695 := bstep (se 1 (by rfl) ⟨1098521, by rfl⟩ : syracuseStep 1464695 = 2197043) B2197043
theorem B1603997 : Blo 432776 1603997 := bstep (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) B601499
theorem B2792015 : Blo 432776 2792015 := bstep (se 1 (by rfl) ⟨2094011, by rfl⟩ : syracuseStep 2792015 = 4188023) B4188023
theorem B10672793 : Blo 432776 10672793 := bstep (se 2 (by rfl) ⟨4002297, by rfl⟩ : syracuseStep 10672793 = 8004595) B8004595
theorem B18766511 : Blo 432776 18766511 := bstep (se 1 (by rfl) ⟨14074883, by rfl⟩ : syracuseStep 18766511 = 28149767) B28149767
theorem B1784555 : Blo 432776 1784555 := bstep (se 1 (by rfl) ⟨1338416, by rfl⟩ : syracuseStep 1784555 = 2676833) B2676833
theorem B432891 : Blo 432776 432891 := bstep (se 1 (by rfl) ⟨324668, by rfl⟩ : syracuseStep 432891 = 649337) B649337
theorem B2472929 : Blo 432776 2472929 := bstep (se 2 (by rfl) ⟨927348, by rfl⟩ : syracuseStep 2472929 = 1854697) B1854697
theorem B433147 : Blo 432776 433147 := bstep (se 1 (by rfl) ⟨324860, by rfl⟩ : syracuseStep 433147 = 649721) B649721
theorem B433183 : Blo 432776 433183 := bstep (se 1 (by rfl) ⟨324887, by rfl⟩ : syracuseStep 433183 = 649775) B649775
theorem B3120257 : Blo 432776 3120257 := bstep (se 2 (by rfl) ⟨1170096, by rfl⟩ : syracuseStep 3120257 = 2340193) B2340193
theorem B3308687 : Blo 432776 3308687 := bstep (se 1 (by rfl) ⟨2481515, by rfl⟩ : syracuseStep 3308687 = 4963031) B4963031
theorem B69483835 : Blo 432776 69483835 := bstep (se 1 (by rfl) ⟨52112876, by rfl⟩ : syracuseStep 69483835 = 104225753) B104225753
theorem B433471 : Blo 432776 433471 := bstep (se 1 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 433471 = 650207) B650207
theorem B1645991 : Blo 432776 1645991 := bstep (se 1 (by rfl) ⟨1234493, by rfl⟩ : syracuseStep 1645991 = 2468987) B2468987
theorem B1097135 : Blo 432776 1097135 := bstep (se 1 (by rfl) ⟨822851, by rfl⟩ : syracuseStep 1097135 = 1645703) B1645703
theorem B1465775 : Blo 432776 1465775 := bstep (se 1 (by rfl) ⟨1099331, by rfl⟩ : syracuseStep 1465775 = 2198663) B2198663
theorem B5561783 : Blo 432776 5561783 := bstep (se 1 (by rfl) ⟨4171337, by rfl⟩ : syracuseStep 5561783 = 8342675) B8342675
theorem B7822817 : Blo 432776 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B433767 : Blo 432776 433767 := bstep (se 1 (by rfl) ⟨325325, by rfl⟩ : syracuseStep 433767 = 650651) B650651
theorem B7405181 : Blo 432776 7405181 := bstep (se 3 (by rfl) ⟨1388471, by rfl⟩ : syracuseStep 7405181 = 2776943) B2776943
theorem B2203361 : Blo 432776 2203361 := bstep (se 2 (by rfl) ⟨826260, by rfl⟩ : syracuseStep 2203361 = 1652521) B1652521
theorem B827111 : Blo 432776 827111 := bstep (se 1 (by rfl) ⟨620333, by rfl⟩ : syracuseStep 827111 = 1240667) B1240667
theorem B434047 : Blo 432776 434047 := bstep (se 1 (by rfl) ⟨325535, by rfl⟩ : syracuseStep 434047 = 651071) B651071
theorem B1097671 : Blo 432776 1097671 := bstep (se 1 (by rfl) ⟨823253, by rfl⟩ : syracuseStep 1097671 = 1646507) B1646507
theorem B434239 : Blo 432776 434239 := bstep (se 1 (by rfl) ⟨325679, by rfl⟩ : syracuseStep 434239 = 651359) B651359
theorem B434279 : Blo 432776 434279 := bstep (se 1 (by rfl) ⟨325709, by rfl⟩ : syracuseStep 434279 = 651419) B651419
theorem B434399 : Blo 432776 434399 := bstep (se 1 (by rfl) ⟨325799, by rfl⟩ : syracuseStep 434399 = 651599) B651599
theorem B434459 : Blo 432776 434459 := bstep (se 1 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 434459 = 651689) B651689
theorem B193184135 : Blo 432776 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B6250891 : Blo 432776 6250891 := bstep (se 1 (by rfl) ⟨4688168, by rfl⟩ : syracuseStep 6250891 = 9376337) B9376337
theorem B1171871 : Blo 432776 1171871 := bstep (se 1 (by rfl) ⟨878903, by rfl⟩ : syracuseStep 1171871 = 1757807) B1757807
theorem B1393085 : Blo 432776 1393085 := bstep (se 3 (by rfl) ⟨261203, by rfl⟩ : syracuseStep 1393085 = 522407) B522407
theorem B434663 : Blo 432776 434663 := bstep (se 1 (by rfl) ⟨325997, by rfl⟩ : syracuseStep 434663 = 651995) B651995
theorem B3301883 : Blo 432776 3301883 := bstep (se 1 (by rfl) ⟨2476412, by rfl⟩ : syracuseStep 3301883 = 4952825) B4952825
theorem B926263 : Blo 432776 926263 := bstep (se 1 (by rfl) ⟨694697, by rfl⟩ : syracuseStep 926263 = 1389395) B1389395
theorem B434843 : Blo 432776 434843 := bstep (se 1 (by rfl) ⟨326132, by rfl⟩ : syracuseStep 434843 = 652265) B652265
theorem B434939 : Blo 432776 434939 := bstep (se 1 (by rfl) ⟨326204, by rfl⟩ : syracuseStep 434939 = 652409) B652409
theorem B3523463 : Blo 432776 3523463 := bstep (se 1 (by rfl) ⟨2642597, by rfl⟩ : syracuseStep 3523463 = 5285195) B5285195
theorem B23774147 : Blo 432776 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B435291 : Blo 432776 435291 := bstep (se 1 (by rfl) ⟨326468, by rfl⟩ : syracuseStep 435291 = 652937) B652937
theorem B1762411 : Blo 432776 1762411 := bstep (se 1 (by rfl) ⟨1321808, by rfl⟩ : syracuseStep 1762411 = 2643617) B2643617
theorem B1172639 : Blo 432776 1172639 := bstep (se 1 (by rfl) ⟨879479, by rfl⟩ : syracuseStep 1172639 = 1758959) B1758959
theorem B435431 : Blo 432776 435431 := bstep (se 1 (by rfl) ⟨326573, by rfl⟩ : syracuseStep 435431 = 653147) B653147
theorem B435455 : Blo 432776 435455 := bstep (se 1 (by rfl) ⟨326591, by rfl⟩ : syracuseStep 435455 = 653183) B653183
theorem B435519 : Blo 432776 435519 := bstep (se 1 (by rfl) ⟨326639, by rfl⟩ : syracuseStep 435519 = 653279) B653279
theorem B976211 : Blo 432776 976211 := bstep (se 1 (by rfl) ⟨732158, by rfl⟩ : syracuseStep 976211 = 1464317) B1464317
theorem B435559 : Blo 432776 435559 := bstep (se 1 (by rfl) ⟨326669, by rfl⟩ : syracuseStep 435559 = 653339) B653339
theorem B435687 : Blo 432776 435687 := bstep (se 1 (by rfl) ⟨326765, by rfl⟩ : syracuseStep 435687 = 653531) B653531
theorem B1099241 : Blo 432776 1099241 := bstep (se 2 (by rfl) ⟨412215, by rfl⟩ : syracuseStep 1099241 = 824431) B824431
theorem B976463 : Blo 432776 976463 := bstep (se 1 (by rfl) ⟨732347, by rfl⟩ : syracuseStep 976463 = 1464695) B1464695
theorem B1410731 : Blo 432776 1410731 := bstep (se 1 (by rfl) ⟨1058048, by rfl⟩ : syracuseStep 1410731 = 2116097) B2116097
theorem B1861343 : Blo 432776 1861343 := bstep (se 1 (by rfl) ⟨1396007, by rfl⟩ : syracuseStep 1861343 = 2792015) B2792015
theorem B12511007 : Blo 432776 12511007 := bstep (se 1 (by rfl) ⟨9383255, by rfl⟩ : syracuseStep 12511007 = 18766511) B18766511
theorem B1189703 : Blo 432776 1189703 := bstep (se 1 (by rfl) ⟨892277, by rfl⟩ : syracuseStep 1189703 = 1784555) B1784555
theorem B3524431 : Blo 432776 3524431 := bstep (se 1 (by rfl) ⟨2643323, by rfl⟩ : syracuseStep 3524431 = 5286647) B5286647
theorem B2205629 : Blo 432776 2205629 := bstep (se 3 (by rfl) ⟨413555, by rfl⟩ : syracuseStep 2205629 = 827111) B827111
theorem B1755113 : Blo 432776 1755113 := bstep (se 2 (by rfl) ⟨658167, by rfl⟩ : syracuseStep 1755113 = 1316335) B1316335
theorem B1648619 : Blo 432776 1648619 := bstep (se 1 (by rfl) ⟨1236464, by rfl⟩ : syracuseStep 1648619 = 2472929) B2472929
theorem B2197529 : Blo 432776 2197529 := bstep (se 2 (by rfl) ⟨824073, by rfl⟩ : syracuseStep 2197529 = 1648147) B1648147
theorem B90540109 : Blo 432776 90540109 := bstep (se 3 (by rfl) ⟨16976270, by rfl⟩ : syracuseStep 90540109 = 33952541) B33952541
theorem B2205791 : Blo 432776 2205791 := bstep (se 1 (by rfl) ⟨1654343, by rfl⟩ : syracuseStep 2205791 = 3308687) B3308687
theorem B1099919 : Blo 432776 1099919 := bstep (se 1 (by rfl) ⟨824939, by rfl⟩ : syracuseStep 1099919 = 1649879) B1649879
theorem B977057 : Blo 432776 977057 := bstep (se 2 (by rfl) ⟨366396, by rfl⟩ : syracuseStep 977057 = 732793) B732793
theorem B2197691 : Blo 432776 2197691 := bstep (se 1 (by rfl) ⟨1648268, by rfl⟩ : syracuseStep 2197691 = 3296537) B3296537
theorem B731423 : Blo 432776 731423 := bstep (se 1 (by rfl) ⟨548567, by rfl⟩ : syracuseStep 731423 = 1097135) B1097135
theorem B977183 : Blo 432776 977183 := bstep (se 1 (by rfl) ⟨732887, by rfl⟩ : syracuseStep 977183 = 1465775) B1465775
theorem B1468745 : Blo 432776 1468745 := bstep (se 2 (by rfl) ⟨550779, by rfl⟩ : syracuseStep 1468745 = 1101559) B1101559
theorem B1468907 : Blo 432776 1468907 := bstep (se 1 (by rfl) ⟨1101680, by rfl⟩ : syracuseStep 1468907 = 2203361) B2203361
theorem B3131905 : Blo 432776 3131905 := bstep (se 2 (by rfl) ⟨1174464, by rfl⟩ : syracuseStep 3131905 = 2348929) B2348929
theorem B625243 : Blo 432776 625243 := bstep (se 1 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 625243 = 937865) B937865
theorem B1665697 : Blo 432776 1665697 := bstep (se 2 (by rfl) ⟨624636, by rfl⟩ : syracuseStep 1665697 = 1249273) B1249273
theorem B649967 : Blo 432776 649967 := bstep (se 1 (by rfl) ⟨487475, by rfl⟩ : syracuseStep 649967 = 974951) B974951
theorem B1395443 : Blo 432776 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B5573569 : Blo 432776 5573569 := bstep (se 2 (by rfl) ⟨2090088, by rfl⟩ : syracuseStep 5573569 = 4180177) B4180177
theorem B1240019 : Blo 432776 1240019 := bstep (se 1 (by rfl) ⟨930014, by rfl⟩ : syracuseStep 1240019 = 1860029) B1860029
theorem B37555163 : Blo 432776 37555163 := bstep (se 1 (by rfl) ⟨28166372, by rfl⟩ : syracuseStep 37555163 = 56332745) B56332745
theorem B4074515 : Blo 432776 4074515 := bstep (se 1 (by rfl) ⟨3055886, by rfl⟩ : syracuseStep 4074515 = 6111773) B6111773
theorem B650345 : Blo 432776 650345 := bstep (se 2 (by rfl) ⟨243879, by rfl⟩ : syracuseStep 650345 = 487759) B487759
theorem B1100911 : Blo 432776 1100911 := bstep (se 1 (by rfl) ⟨825683, by rfl⟩ : syracuseStep 1100911 = 1651367) B1651367
theorem B732395 : Blo 432776 732395 := bstep (se 1 (by rfl) ⟨549296, by rfl⟩ : syracuseStep 732395 = 1098593) B1098593
theorem B978155 : Blo 432776 978155 := bstep (se 1 (by rfl) ⟨733616, by rfl⟩ : syracuseStep 978155 = 1467233) B1467233
theorem B6761861 : Blo 432776 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B1461671 : Blo 432776 1461671 := bstep (se 1 (by rfl) ⟨1096253, by rfl⟩ : syracuseStep 1461671 = 2192507) B2192507
theorem B7515575 : Blo 432776 7515575 := bstep (se 1 (by rfl) ⟨5636681, by rfl⟩ : syracuseStep 7515575 = 11273363) B11273363
theorem B650735 : Blo 432776 650735 := bstep (se 1 (by rfl) ⟨488051, by rfl⟩ : syracuseStep 650735 = 976103) B976103
theorem B3059279 : Blo 432776 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B650873 : Blo 432776 650873 := bstep (se 2 (by rfl) ⟨244077, by rfl⟩ : syracuseStep 650873 = 488155) B488155
theorem B3526507 : Blo 432776 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B7409555 : Blo 432776 7409555 := bstep (se 1 (by rfl) ⟨5557166, by rfl⟩ : syracuseStep 7409555 = 11114333) B11114333
theorem B3952583 : Blo 432776 3952583 := bstep (se 1 (by rfl) ⟨2964437, by rfl⟩ : syracuseStep 3952583 = 5928875) B5928875
theorem B4182023 : Blo 432776 4182023 := bstep (se 1 (by rfl) ⟨3136517, by rfl⟩ : syracuseStep 4182023 = 6273035) B6273035
theorem B1069331 : Blo 432776 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B2191697 : Blo 432776 2191697 := bstep (se 2 (by rfl) ⟨821886, by rfl⟩ : syracuseStep 2191697 = 1643773) B1643773
theorem B979361 : Blo 432776 979361 := bstep (se 2 (by rfl) ⟨367260, by rfl⟩ : syracuseStep 979361 = 734521) B734521
theorem B3699107 : Blo 432776 3699107 := bstep (se 1 (by rfl) ⟨2774330, by rfl⟩ : syracuseStep 3699107 = 5548661) B5548661
theorem B7115195 : Blo 432776 7115195 := bstep (se 1 (by rfl) ⟨5336396, by rfl⟩ : syracuseStep 7115195 = 10672793) B10672793
theorem B979433 : Blo 432776 979433 := bstep (se 2 (by rfl) ⟨367287, by rfl⟩ : syracuseStep 979433 = 734575) B734575
theorem B1651337 : Blo 432776 1651337 := bstep (se 2 (by rfl) ⟨619251, by rfl⟩ : syracuseStep 1651337 = 1238503) B1238503
theorem B19075733 : Blo 432776 19075733 := bstep (se 6 (by rfl) ⟨447087, by rfl⟩ : syracuseStep 19075733 = 894175) B894175
theorem B3707855 : Blo 432776 3707855 := bstep (se 1 (by rfl) ⟨2780891, by rfl⟩ : syracuseStep 3707855 = 5561783) B5561783
theorem B5215211 : Blo 432776 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B4936787 : Blo 432776 4936787 := bstep (se 1 (by rfl) ⟨3702590, by rfl⟩ : syracuseStep 4936787 = 7405181) B7405181
theorem B652457 : Blo 432776 652457 := bstep (se 2 (by rfl) ⟨244671, by rfl⟩ : syracuseStep 652457 = 489343) B489343
theorem B3970241 : Blo 432776 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B652523 : Blo 432776 652523 := bstep (se 1 (by rfl) ⟨489392, by rfl⟩ : syracuseStep 652523 = 978785) B978785
theorem B1463561 : Blo 432776 1463561 := bstep (se 2 (by rfl) ⟨548835, by rfl⟩ : syracuseStep 1463561 = 1097671) B1097671
theorem B1949701475 : Blo 432776 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B2413999 : Blo 432776 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B2233919 : Blo 432776 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B3331793 : Blo 432776 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B2782943 : Blo 432776 2782943 := bstep (se 1 (by rfl) ⟨2087207, by rfl⟩ : syracuseStep 2782943 = 4174415) B4174415
theorem B1464047 : Blo 432776 1464047 := bstep (se 1 (by rfl) ⟨1098035, by rfl⟩ : syracuseStep 1464047 = 2196071) B2196071
theorem B5953283 : Blo 432776 5953283 := bstep (se 1 (by rfl) ⟨4464962, by rfl⟩ : syracuseStep 5953283 = 8929925) B8929925
theorem B825167 : Blo 432776 825167 := bstep (se 1 (by rfl) ⟨618875, by rfl⟩ : syracuseStep 825167 = 1237751) B1237751
theorem B7116635 : Blo 432776 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B653159 : Blo 432776 653159 := bstep (se 1 (by rfl) ⟨489869, by rfl⟩ : syracuseStep 653159 = 979739) B979739
theorem B653291 : Blo 432776 653291 := bstep (se 1 (by rfl) ⟨489968, by rfl⟩ : syracuseStep 653291 = 979937) B979937
theorem B2340971 : Blo 432776 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B653423 : Blo 432776 653423 := bstep (se 1 (by rfl) ⟨490067, by rfl⟩ : syracuseStep 653423 = 980135) B980135
theorem B1644731 : Blo 432776 1644731 := bstep (se 1 (by rfl) ⟨1233548, by rfl⟩ : syracuseStep 1644731 = 2467097) B2467097
theorem B23837003 : Blo 432776 23837003 := bstep (se 1 (by rfl) ⟨17877752, by rfl⟩ : syracuseStep 23837003 = 35755505) B35755505
theorem B2349431 : Blo 432776 2349431 := bstep (se 1 (by rfl) ⟨1762073, by rfl⟩ : syracuseStep 2349431 = 3524147) B3524147
theorem B2193803 : Blo 432776 2193803 := bstep (se 1 (by rfl) ⟨1645352, by rfl⟩ : syracuseStep 2193803 = 3290705) B3290705
theorem B2636225 : Blo 432776 2636225 := bstep (se 2 (by rfl) ⟨988584, by rfl⟩ : syracuseStep 2636225 = 1977169) B1977169
theorem B5003963 : Blo 432776 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B432831 : Blo 432776 432831 := bstep (se 1 (by rfl) ⟨324623, by rfl⟩ : syracuseStep 432831 = 649247) B649247
theorem B370580453 : Blo 432776 370580453 := bstep (se 4 (by rfl) ⟨34741917, by rfl⟩ : syracuseStep 370580453 = 69483835) B69483835
theorem B433135 : Blo 432776 433135 := bstep (se 1 (by rfl) ⟨324851, by rfl⟩ : syracuseStep 433135 = 649703) B649703
theorem B2776123 : Blo 432776 2776123 := bstep (se 1 (by rfl) ⟨2082092, by rfl⟩ : syracuseStep 2776123 = 4164185) B4164185
theorem B2202713 : Blo 432776 2202713 := bstep (se 2 (by rfl) ⟨826017, by rfl⟩ : syracuseStep 2202713 = 1652035) B1652035
theorem B433255 : Blo 432776 433255 := bstep (se 1 (by rfl) ⟨324941, by rfl⟩ : syracuseStep 433255 = 649883) B649883
theorem B433403 : Blo 432776 433403 := bstep (se 1 (by rfl) ⟨325052, by rfl⟩ : syracuseStep 433403 = 650105) B650105
theorem B974159 : Blo 432776 974159 := bstep (se 1 (by rfl) ⟨730619, by rfl⟩ : syracuseStep 974159 = 1461239) B1461239
theorem B433567 : Blo 432776 433567 := bstep (se 1 (by rfl) ⟨325175, by rfl⟩ : syracuseStep 433567 = 650351) B650351
theorem B2080171 : Blo 432776 2080171 := bstep (se 1 (by rfl) ⟨1560128, by rfl⟩ : syracuseStep 2080171 = 3120257) B3120257
theorem B433631 : Blo 432776 433631 := bstep (se 1 (by rfl) ⟨325223, by rfl⟩ : syracuseStep 433631 = 650447) B650447
theorem B433711 : Blo 432776 433711 := bstep (se 1 (by rfl) ⟨325283, by rfl⟩ : syracuseStep 433711 = 650567) B650567
theorem B1097327 : Blo 432776 1097327 := bstep (se 1 (by rfl) ⟨822995, by rfl⟩ : syracuseStep 1097327 = 1645991) B1645991
theorem B974519 : Blo 432776 974519 := bstep (se 1 (by rfl) ⟨730889, by rfl⟩ : syracuseStep 974519 = 1461779) B1461779
theorem B1236703 : Blo 432776 1236703 := bstep (se 1 (by rfl) ⟨927527, by rfl⟩ : syracuseStep 1236703 = 1855055) B1855055
theorem B433903 : Blo 432776 433903 := bstep (se 1 (by rfl) ⟨325427, by rfl⟩ : syracuseStep 433903 = 650855) B650855
theorem B925435 : Blo 432776 925435 := bstep (se 1 (by rfl) ⟨694076, by rfl⟩ : syracuseStep 925435 = 1388153) B1388153
theorem B2383789 : Blo 432776 2383789 := bstep (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) B893921
theorem B434159 : Blo 432776 434159 := bstep (se 1 (by rfl) ⟨325619, by rfl⟩ : syracuseStep 434159 = 651239) B651239
theorem B2466071 : Blo 432776 2466071 := bstep (se 1 (by rfl) ⟨1849553, by rfl⟩ : syracuseStep 2466071 = 3699107) B3699107
theorem B4743463 : Blo 432776 4743463 := bstep (se 1 (by rfl) ⟨3557597, by rfl⟩ : syracuseStep 4743463 = 7115195) B7115195
theorem B2851549 : Blo 432776 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B434971 : Blo 432776 434971 := bstep (se 1 (by rfl) ⟨326228, by rfl⟩ : syracuseStep 434971 = 652457) B652457
theorem B2646827 : Blo 432776 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B435015 : Blo 432776 435015 := bstep (se 1 (by rfl) ⟨326261, by rfl⟩ : syracuseStep 435015 = 652523) B652523
theorem B975707 : Blo 432776 975707 := bstep (se 1 (by rfl) ⟨731780, by rfl⟩ : syracuseStep 975707 = 1463561) B1463561
theorem B2220929 : Blo 432776 2220929 := bstep (se 2 (by rfl) ⟨832848, by rfl⟩ : syracuseStep 2220929 = 1665697) B1665697
theorem B2221195 : Blo 432776 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B976031 : Blo 432776 976031 := bstep (se 1 (by rfl) ⟨732023, by rfl⟩ : syracuseStep 976031 = 1464047) B1464047
theorem B8340671 : Blo 432776 8340671 := bstep (se 1 (by rfl) ⟨6255503, by rfl⟩ : syracuseStep 8340671 = 12511007) B12511007
theorem B4744423 : Blo 432776 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B435439 : Blo 432776 435439 := bstep (se 1 (by rfl) ⟨326579, by rfl⟩ : syracuseStep 435439 = 653159) B653159
theorem B7431425 : Blo 432776 7431425 := bstep (se 2 (by rfl) ⟨2786784, by rfl⟩ : syracuseStep 7431425 = 5573569) B5573569
theorem B1099079 : Blo 432776 1099079 := bstep (se 1 (by rfl) ⟨824309, by rfl⟩ : syracuseStep 1099079 = 1648619) B1648619
theorem B435527 : Blo 432776 435527 := bstep (se 1 (by rfl) ⟨326645, by rfl⟩ : syracuseStep 435527 = 653291) B653291
theorem B435615 : Blo 432776 435615 := bstep (se 1 (by rfl) ⟨326711, by rfl⟩ : syracuseStep 435615 = 653423) B653423
theorem B1467881 : Blo 432776 1467881 := bstep (se 2 (by rfl) ⟨550455, by rfl⟩ : syracuseStep 1467881 = 1100911) B1100911
theorem B1566287 : Blo 432776 1566287 := bstep (se 1 (by rfl) ⟨1174715, by rfl⟩ : syracuseStep 1566287 = 2349431) B2349431
theorem B3335975 : Blo 432776 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B25036775 : Blo 432776 25036775 := bstep (se 1 (by rfl) ⟨18777581, by rfl⟩ : syracuseStep 25036775 = 37555163) B37555163
theorem B1468475 : Blo 432776 1468475 := bstep (se 1 (by rfl) ⟨1101356, by rfl⟩ : syracuseStep 1468475 = 2202713) B2202713
theorem B649439 : Blo 432776 649439 := bstep (se 1 (by rfl) ⟨487079, by rfl⟩ : syracuseStep 649439 = 974159) B974159
theorem B4507907 : Blo 432776 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B1648937 : Blo 432776 1648937 := bstep (se 2 (by rfl) ⟨618351, by rfl⟩ : syracuseStep 1648937 = 1236703) B1236703
theorem B731551 : Blo 432776 731551 := bstep (se 1 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 731551 = 1097327) B1097327
theorem B649679 : Blo 432776 649679 := bstep (se 1 (by rfl) ⟨487259, by rfl⟩ : syracuseStep 649679 = 974519) B974519
theorem B4680301 : Blo 432776 4680301 := bstep (se 3 (by rfl) ⟨877556, by rfl⟩ : syracuseStep 4680301 = 1755113) B1755113
theorem B2788015 : Blo 432776 2788015 := bstep (se 1 (by rfl) ⟨2091011, by rfl⟩ : syracuseStep 2788015 = 4182023) B4182023
theorem B120720145 : Blo 432776 120720145 := bstep (se 2 (by rfl) ⟨45270054, by rfl⟩ : syracuseStep 120720145 = 90540109) B90540109
theorem B1461131 : Blo 432776 1461131 := bstep (se 1 (by rfl) ⟨1095848, by rfl⟩ : syracuseStep 1461131 = 2191697) B2191697
theorem B128789423 : Blo 432776 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B781247 : Blo 432776 781247 := bstep (se 1 (by rfl) ⟨585935, by rfl⟩ : syracuseStep 781247 = 1171871) B1171871
theorem B1100891 : Blo 432776 1100891 := bstep (se 1 (by rfl) ⟨825668, by rfl⟩ : syracuseStep 1100891 = 1651337) B1651337
theorem B12717155 : Blo 432776 12717155 := bstep (se 1 (by rfl) ⟨9537866, by rfl⟩ : syracuseStep 12717155 = 19075733) B19075733
theorem B8334521 : Blo 432776 8334521 := bstep (se 2 (by rfl) ⟨3125445, by rfl⟩ : syracuseStep 8334521 = 6250891) B6250891
theorem B3476807 : Blo 432776 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B781759 : Blo 432776 781759 := bstep (se 1 (by rfl) ⟨586319, by rfl⟩ : syracuseStep 781759 = 1172639) B1172639
theorem B650807 : Blo 432776 650807 := bstep (se 1 (by rfl) ⟨488105, by rfl⟩ : syracuseStep 650807 = 976211) B976211
theorem B5199203933 : Blo 432776 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B732827 : Blo 432776 732827 := bstep (se 1 (by rfl) ⟨549620, by rfl⟩ : syracuseStep 732827 = 1099241) B1099241
theorem B650975 : Blo 432776 650975 := bstep (se 1 (by rfl) ⟨488231, by rfl⟩ : syracuseStep 650975 = 976463) B976463
theorem B1855295 : Blo 432776 1855295 := bstep (se 1 (by rfl) ⟨1391471, by rfl⟩ : syracuseStep 1855295 = 2782943) B2782943
theorem B1240895 : Blo 432776 1240895 := bstep (se 1 (by rfl) ⟨930671, by rfl⟩ : syracuseStep 1240895 = 1861343) B1861343
theorem B3714893 : Blo 432776 3714893 := bstep (se 3 (by rfl) ⟨696542, by rfl⟩ : syracuseStep 3714893 = 1393085) B1393085
theorem B3968855 : Blo 432776 3968855 := bstep (se 1 (by rfl) ⟨2976641, by rfl⟩ : syracuseStep 3968855 = 5953283) B5953283
theorem B1470419 : Blo 432776 1470419 := bstep (se 1 (by rfl) ⟨1102814, by rfl⟩ : syracuseStep 1470419 = 2205629) B2205629
theorem B1470527 : Blo 432776 1470527 := bstep (se 1 (by rfl) ⟨1102895, by rfl⟩ : syracuseStep 1470527 = 2205791) B2205791
theorem B1560647 : Blo 432776 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B733279 : Blo 432776 733279 := bstep (se 1 (by rfl) ⟨549959, by rfl⟩ : syracuseStep 733279 = 1099919) B1099919
theorem B651371 : Blo 432776 651371 := bstep (se 1 (by rfl) ⟨488528, by rfl⟩ : syracuseStep 651371 = 977057) B977057
theorem B487615 : Blo 432776 487615 := bstep (se 1 (by rfl) ⟨365711, by rfl⟩ : syracuseStep 487615 = 731423) B731423
theorem B651455 : Blo 432776 651455 := bstep (se 1 (by rfl) ⟨488591, by rfl⟩ : syracuseStep 651455 = 977183) B977183
theorem B979163 : Blo 432776 979163 := bstep (se 1 (by rfl) ⟨734372, by rfl⟩ : syracuseStep 979163 = 1468745) B1468745
theorem B1462535 : Blo 432776 1462535 := bstep (se 1 (by rfl) ⟨1096901, by rfl⟩ : syracuseStep 1462535 = 2193803) B2193803
theorem B1757483 : Blo 432776 1757483 := bstep (se 1 (by rfl) ⟨1318112, by rfl⟩ : syracuseStep 1757483 = 2636225) B2636225
theorem B979271 : Blo 432776 979271 := bstep (se 1 (by rfl) ⟨734453, by rfl⟩ : syracuseStep 979271 = 1468907) B1468907
theorem B930295 : Blo 432776 930295 := bstep (se 1 (by rfl) ⟨697721, by rfl⟩ : syracuseStep 930295 = 1395443) B1395443
theorem B2773561 : Blo 432776 2773561 := bstep (se 2 (by rfl) ⟨1040085, by rfl⟩ : syracuseStep 2773561 = 2080171) B2080171
theorem B2716343 : Blo 432776 2716343 := bstep (se 1 (by rfl) ⟨2037257, by rfl⟩ : syracuseStep 2716343 = 4074515) B4074515
theorem B488263 : Blo 432776 488263 := bstep (se 1 (by rfl) ⟨366197, by rfl⟩ : syracuseStep 488263 = 732395) B732395
theorem B652103 : Blo 432776 652103 := bstep (se 1 (by rfl) ⟨489077, by rfl⟩ : syracuseStep 652103 = 978155) B978155
theorem B2200445 : Blo 432776 2200445 := bstep (se 3 (by rfl) ⟨412583, by rfl⟩ : syracuseStep 2200445 = 825167) B825167
theorem B5010383 : Blo 432776 5010383 := bstep (se 1 (by rfl) ⟨3757787, by rfl⟩ : syracuseStep 5010383 = 7515575) B7515575
theorem B1233913 : Blo 432776 1233913 := bstep (se 2 (by rfl) ⟨462717, by rfl⟩ : syracuseStep 1233913 = 925435) B925435
theorem B4699241 : Blo 432776 4699241 := bstep (se 2 (by rfl) ⟨1762215, by rfl⟩ : syracuseStep 4699241 = 3524431) B3524431
theorem B2635055 : Blo 432776 2635055 := bstep (se 1 (by rfl) ⟨1976291, by rfl⟩ : syracuseStep 2635055 = 3952583) B3952583
theorem B652907 : Blo 432776 652907 := bstep (se 1 (by rfl) ⟨489680, by rfl⟩ : syracuseStep 652907 = 979361) B979361
theorem B652955 : Blo 432776 652955 := bstep (se 1 (by rfl) ⟨489716, by rfl⟩ : syracuseStep 652955 = 979433) B979433
theorem B2201255 : Blo 432776 2201255 := bstep (se 1 (by rfl) ⟨1650941, by rfl⟩ : syracuseStep 2201255 = 3301883) B3301883
theorem B2348975 : Blo 432776 2348975 := bstep (se 1 (by rfl) ⟨1761731, by rfl⟩ : syracuseStep 2348975 = 3523463) B3523463
theorem B15849431 : Blo 432776 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B2471903 : Blo 432776 2471903 := bstep (se 1 (by rfl) ⟨1853927, by rfl⟩ : syracuseStep 2471903 = 3707855) B3707855
theorem B4175873 : Blo 432776 4175873 := bstep (se 2 (by rfl) ⟨1565952, by rfl⟩ : syracuseStep 4175873 = 3131905) B3131905
theorem B3291191 : Blo 432776 3291191 := bstep (se 1 (by rfl) ⟨2468393, by rfl⟩ : syracuseStep 3291191 = 4936787) B4936787
theorem B1235017 : Blo 432776 1235017 := bstep (se 2 (by rfl) ⟨463131, by rfl⟩ : syracuseStep 1235017 = 926263) B926263
theorem B833657 : Blo 432776 833657 := bstep (se 2 (by rfl) ⟨312621, by rfl⟩ : syracuseStep 833657 = 625243) B625243
theorem B1489279 : Blo 432776 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B940487 : Blo 432776 940487 := bstep (se 1 (by rfl) ⟨705365, by rfl⟩ : syracuseStep 940487 = 1410731) B1410731
theorem B793135 : Blo 432776 793135 := bstep (se 1 (by rfl) ⟨594851, by rfl⟩ : syracuseStep 793135 = 1189703) B1189703
theorem B1465019 : Blo 432776 1465019 := bstep (se 1 (by rfl) ⟨1098764, by rfl⟩ : syracuseStep 1465019 = 2197529) B2197529
theorem B3701497 : Blo 432776 3701497 := bstep (se 2 (by rfl) ⟨1388061, by rfl⟩ : syracuseStep 3701497 = 2776123) B2776123
theorem B1096487 : Blo 432776 1096487 := bstep (se 1 (by rfl) ⟨822365, by rfl⟩ : syracuseStep 1096487 = 1644731) B1644731
theorem B1465127 : Blo 432776 1465127 := bstep (se 1 (by rfl) ⟨1098845, by rfl⟩ : syracuseStep 1465127 = 2197691) B2197691
theorem B2349881 : Blo 432776 2349881 := bstep (se 2 (by rfl) ⟨881205, by rfl⟩ : syracuseStep 2349881 = 1762411) B1762411
theorem B15891335 : Blo 432776 15891335 := bstep (se 1 (by rfl) ⟨11918501, by rfl⟩ : syracuseStep 15891335 = 23837003) B23837003
theorem B433311 : Blo 432776 433311 := bstep (se 1 (by rfl) ⟨324983, by rfl⟩ : syracuseStep 433311 = 649967) B649967
theorem B3218665 : Blo 432776 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B826679 : Blo 432776 826679 := bstep (se 1 (by rfl) ⟨620009, by rfl⟩ : syracuseStep 826679 = 1240019) B1240019
theorem B247053635 : Blo 432776 247053635 := bstep (se 1 (by rfl) ⟨185290226, by rfl⟩ : syracuseStep 247053635 = 370580453) B370580453
theorem B433563 : Blo 432776 433563 := bstep (se 1 (by rfl) ⟨325172, by rfl⟩ : syracuseStep 433563 = 650345) B650345
theorem B974447 : Blo 432776 974447 := bstep (se 1 (by rfl) ⟨730835, by rfl⟩ : syracuseStep 974447 = 1461671) B1461671
theorem B433823 : Blo 432776 433823 := bstep (se 1 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 433823 = 650735) B650735
theorem B2039519 : Blo 432776 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B433915 : Blo 432776 433915 := bstep (se 1 (by rfl) ⟨325436, by rfl⟩ : syracuseStep 433915 = 650873) B650873
theorem B4702009 : Blo 432776 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B3178385 : Blo 432776 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B4939703 : Blo 432776 4939703 := bstep (se 1 (by rfl) ⟨3704777, by rfl⟩ : syracuseStep 4939703 = 7409555) B7409555
theorem B434247 : Blo 432776 434247 := bstep (se 1 (by rfl) ⟨325685, by rfl⟩ : syracuseStep 434247 = 651371) B651371
theorem B1646689 : Blo 432776 1646689 := bstep (se 2 (by rfl) ⟨617508, by rfl⟩ : syracuseStep 1646689 = 1235017) B1235017
theorem B434303 : Blo 432776 434303 := bstep (se 1 (by rfl) ⟨325727, by rfl⟩ : syracuseStep 434303 = 651455) B651455
theorem B975023 : Blo 432776 975023 := bstep (se 1 (by rfl) ⟨731267, by rfl⟩ : syracuseStep 975023 = 1462535) B1462535
theorem B4161725 : Blo 432776 4161725 := bstep (se 3 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 4161725 = 1560647) B1560647
theorem B1171655 : Blo 432776 1171655 := bstep (se 1 (by rfl) ⟨878741, by rfl⟩ : syracuseStep 1171655 = 1757483) B1757483
theorem B6324617 : Blo 432776 6324617 := bstep (se 2 (by rfl) ⟨2371731, by rfl⟩ : syracuseStep 6324617 = 4743463) B4743463
theorem B1810895 : Blo 432776 1810895 := bstep (se 1 (by rfl) ⟨1358171, by rfl⟩ : syracuseStep 1810895 = 2716343) B2716343
theorem B975401 : Blo 432776 975401 := bstep (se 2 (by rfl) ⟨365775, by rfl⟩ : syracuseStep 975401 = 731551) B731551
theorem B434735 : Blo 432776 434735 := bstep (se 1 (by rfl) ⟨326051, by rfl⟩ : syracuseStep 434735 = 652103) B652103
theorem B1466963 : Blo 432776 1466963 := bstep (se 1 (by rfl) ⟨1100222, by rfl⟩ : syracuseStep 1466963 = 2200445) B2200445
theorem B435271 : Blo 432776 435271 := bstep (se 1 (by rfl) ⟨326453, by rfl⟩ : syracuseStep 435271 = 652907) B652907
theorem B435303 : Blo 432776 435303 := bstep (se 1 (by rfl) ⟨326477, by rfl⟩ : syracuseStep 435303 = 652955) B652955
theorem B1467503 : Blo 432776 1467503 := bstep (se 1 (by rfl) ⟨1100627, by rfl⟩ : syracuseStep 1467503 = 2201255) B2201255
theorem B2507965 : Blo 432776 2507965 := bstep (se 3 (by rfl) ⟨470243, by rfl⟩ : syracuseStep 2507965 = 940487) B940487
theorem B1565983 : Blo 432776 1565983 := bstep (se 1 (by rfl) ⟨1174487, by rfl⟩ : syracuseStep 1565983 = 2348975) B2348975
theorem B1647935 : Blo 432776 1647935 := bstep (se 1 (by rfl) ⟨1235951, by rfl⟩ : syracuseStep 1647935 = 2471903) B2471903
theorem B1099291 : Blo 432776 1099291 := bstep (se 1 (by rfl) ⟨824468, by rfl⟩ : syracuseStep 1099291 = 1648937) B1648937
theorem B6325897 : Blo 432776 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B976679 : Blo 432776 976679 := bstep (se 1 (by rfl) ⟨732509, by rfl⟩ : syracuseStep 976679 = 1465019) B1465019
theorem B730991 : Blo 432776 730991 := bstep (se 1 (by rfl) ⟨548243, by rfl⟩ : syracuseStep 730991 = 1096487) B1096487
theorem B976751 : Blo 432776 976751 := bstep (se 1 (by rfl) ⟨732563, by rfl⟩ : syracuseStep 976751 = 1465127) B1465127
theorem B1566587 : Blo 432776 1566587 := bstep (se 1 (by rfl) ⟨1174940, by rfl⟩ : syracuseStep 1566587 = 2349881) B2349881
theorem B1042345 : Blo 432776 1042345 := bstep (se 2 (by rfl) ⟨390879, by rfl⟩ : syracuseStep 1042345 = 781759) B781759
theorem B10594223 : Blo 432776 10594223 := bstep (se 1 (by rfl) ⟨7945667, by rfl⟩ : syracuseStep 10594223 = 15891335) B15891335
theorem B5556347 : Blo 432776 5556347 := bstep (se 1 (by rfl) ⟨4167260, by rfl⟩ : syracuseStep 5556347 = 8334521) B8334521
theorem B551119 : Blo 432776 551119 := bstep (se 1 (by rfl) ⟨413339, by rfl⟩ : syracuseStep 551119 = 826679) B826679
theorem B164702423 : Blo 432776 164702423 := bstep (se 1 (by rfl) ⟨123526817, by rfl⟩ : syracuseStep 164702423 = 247053635) B247053635
theorem B3466135955 : Blo 432776 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B649631 : Blo 432776 649631 := bstep (se 1 (by rfl) ⟨487223, by rfl⟩ : syracuseStep 649631 = 974447) B974447
theorem B6269345 : Blo 432776 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B2476595 : Blo 432776 2476595 := bstep (se 1 (by rfl) ⟨1857446, by rfl⟩ : syracuseStep 2476595 = 3714893) B3714893
theorem B977705 : Blo 432776 977705 := bstep (se 2 (by rfl) ⟨366639, by rfl⟩ : syracuseStep 977705 = 733279) B733279
theorem B4230053 : Blo 432776 4230053 := bstep (se 4 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 4230053 = 793135) B793135
theorem B650153 : Blo 432776 650153 := bstep (se 2 (by rfl) ⟨243807, by rfl⟩ : syracuseStep 650153 = 487615) B487615
theorem B1985705 : Blo 432776 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B1764551 : Blo 432776 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B650471 : Blo 432776 650471 := bstep (se 1 (by rfl) ⟨487853, by rfl⟩ : syracuseStep 650471 = 975707) B975707
theorem B12021085 : Blo 432776 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B3132827 : Blo 432776 3132827 := bstep (se 1 (by rfl) ⟨2349620, by rfl⟩ : syracuseStep 3132827 = 4699241) B4699241
theorem B3698081 : Blo 432776 3698081 := bstep (se 2 (by rfl) ⟨1386780, by rfl⟩ : syracuseStep 3698081 = 2773561) B2773561
theorem B650687 : Blo 432776 650687 := bstep (se 1 (by rfl) ⟨488015, by rfl⟩ : syracuseStep 650687 = 976031) B976031
theorem B1756703 : Blo 432776 1756703 := bstep (se 1 (by rfl) ⟨1317527, by rfl⟩ : syracuseStep 1756703 = 2635055) B2635055
theorem B732719 : Blo 432776 732719 := bstep (se 1 (by rfl) ⟨549539, by rfl⟩ : syracuseStep 732719 = 1099079) B1099079
theorem B978587 : Blo 432776 978587 := bstep (se 1 (by rfl) ⟨733940, by rfl⟩ : syracuseStep 978587 = 1467881) B1467881
theorem B4935329 : Blo 432776 4935329 := bstep (se 2 (by rfl) ⟨1850748, by rfl⟩ : syracuseStep 4935329 = 3701497) B3701497
theorem B160960193 : Blo 432776 160960193 := bstep (se 2 (by rfl) ⟨60360072, by rfl⟩ : syracuseStep 160960193 = 120720145) B120720145
theorem B1044191 : Blo 432776 1044191 := bstep (se 1 (by rfl) ⟨783143, by rfl⟩ : syracuseStep 1044191 = 1566287) B1566287
theorem B651017 : Blo 432776 651017 := bstep (se 2 (by rfl) ⟨244131, by rfl⟩ : syracuseStep 651017 = 488263) B488263
theorem B2223983 : Blo 432776 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B8892341 : Blo 432776 8892341 := bstep (se 5 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 8892341 = 833657) B833657
theorem B16691183 : Blo 432776 16691183 := bstep (se 1 (by rfl) ⟨12518387, by rfl⟩ : syracuseStep 16691183 = 25036775) B25036775
theorem B978983 : Blo 432776 978983 := bstep (se 1 (by rfl) ⟨734237, by rfl⟩ : syracuseStep 978983 = 1468475) B1468475
theorem B2961593 : Blo 432776 2961593 := bstep (se 2 (by rfl) ⟨1110597, by rfl⟩ : syracuseStep 2961593 = 2221195) B2221195
theorem B520831 : Blo 432776 520831 := bstep (se 1 (by rfl) ⟨390623, by rfl⟩ : syracuseStep 520831 = 781247) B781247
theorem B733927 : Blo 432776 733927 := bstep (se 1 (by rfl) ⟨550445, by rfl⟩ : syracuseStep 733927 = 1100891) B1100891
theorem B488551 : Blo 432776 488551 := bstep (se 1 (by rfl) ⟨366413, by rfl⟩ : syracuseStep 488551 = 732827) B732827
theorem B2118923 : Blo 432776 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B4961573 : Blo 432776 4961573 := bstep (se 4 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 4961573 = 930295) B930295
theorem B980279 : Blo 432776 980279 := bstep (se 1 (by rfl) ⟨735209, by rfl⟩ : syracuseStep 980279 = 1470419) B1470419
theorem B980351 : Blo 432776 980351 := bstep (se 1 (by rfl) ⟨735263, by rfl⟩ : syracuseStep 980351 = 1470527) B1470527
theorem B652775 : Blo 432776 652775 := bstep (se 1 (by rfl) ⟨489581, by rfl⟩ : syracuseStep 652775 = 979163) B979163
theorem B1644047 : Blo 432776 1644047 := bstep (se 1 (by rfl) ⟨1233035, by rfl⟩ : syracuseStep 1644047 = 2466071) B2466071
theorem B652847 : Blo 432776 652847 := bstep (se 1 (by rfl) ⟨489635, by rfl⟩ : syracuseStep 652847 = 979271) B979271
theorem B1480619 : Blo 432776 1480619 := bstep (se 1 (by rfl) ⟨1110464, by rfl⟩ : syracuseStep 1480619 = 2220929) B2220929
theorem B5560447 : Blo 432776 5560447 := bstep (se 1 (by rfl) ⟨4170335, by rfl⟩ : syracuseStep 5560447 = 8340671) B8340671
theorem B6240401 : Blo 432776 6240401 := bstep (se 2 (by rfl) ⟨2340150, by rfl⟩ : syracuseStep 6240401 = 4680301) B4680301
theorem B4954283 : Blo 432776 4954283 := bstep (se 1 (by rfl) ⟨3715712, by rfl⟩ : syracuseStep 4954283 = 7431425) B7431425
theorem B3717353 : Blo 432776 3717353 := bstep (se 2 (by rfl) ⟨1394007, by rfl⟩ : syracuseStep 3717353 = 2788015) B2788015
theorem B10566287 : Blo 432776 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B1645217 : Blo 432776 1645217 := bstep (se 2 (by rfl) ⟨616956, by rfl⟩ : syracuseStep 1645217 = 1233913) B1233913
theorem B2783915 : Blo 432776 2783915 := bstep (se 1 (by rfl) ⟨2087936, by rfl⟩ : syracuseStep 2783915 = 4175873) B4175873
theorem B2194127 : Blo 432776 2194127 := bstep (se 1 (by rfl) ⟨1645595, by rfl⟩ : syracuseStep 2194127 = 3291191) B3291191
theorem B432959 : Blo 432776 432959 := bstep (se 1 (by rfl) ⟨324719, by rfl⟩ : syracuseStep 432959 = 649439) B649439
theorem B433119 : Blo 432776 433119 := bstep (se 1 (by rfl) ⟨324839, by rfl⟩ : syracuseStep 433119 = 649679) B649679
theorem B4291553 : Blo 432776 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B974087 : Blo 432776 974087 := bstep (se 1 (by rfl) ⟨730565, by rfl⟩ : syracuseStep 974087 = 1461131) B1461131
theorem B60833045 : Blo 432776 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B85859615 : Blo 432776 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B8478103 : Blo 432776 8478103 := bstep (se 1 (by rfl) ⟨6358577, by rfl⟩ : syracuseStep 8478103 = 12717155) B12717155
theorem B2317871 : Blo 432776 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B433871 : Blo 432776 433871 := bstep (se 1 (by rfl) ⟨325403, by rfl⟩ : syracuseStep 433871 = 650807) B650807
theorem B433983 : Blo 432776 433983 := bstep (se 1 (by rfl) ⟨325487, by rfl⟩ : syracuseStep 433983 = 650975) B650975
theorem B1359679 : Blo 432776 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B13361021 : Blo 432776 13361021 := bstep (se 3 (by rfl) ⟨2505191, by rfl⟩ : syracuseStep 13361021 = 5010383) B5010383
theorem B1236863 : Blo 432776 1236863 := bstep (se 1 (by rfl) ⟨927647, by rfl⟩ : syracuseStep 1236863 = 1855295) B1855295
theorem B827263 : Blo 432776 827263 := bstep (se 1 (by rfl) ⟨620447, by rfl⟩ : syracuseStep 827263 = 1240895) B1240895
theorem B2645903 : Blo 432776 2645903 := bstep (se 1 (by rfl) ⟨1984427, by rfl⟩ : syracuseStep 2645903 = 3968855) B3968855
theorem B3293135 : Blo 432776 3293135 := bstep (se 1 (by rfl) ⟨2469851, by rfl⟩ : syracuseStep 3293135 = 4939703) B4939703
theorem B1974395 : Blo 432776 1974395 := bstep (se 1 (by rfl) ⟨1480796, by rfl⟩ : syracuseStep 1974395 = 2961593) B2961593
theorem B2195585 : Blo 432776 2195585 := bstep (se 2 (by rfl) ⟨823344, by rfl⟩ : syracuseStep 2195585 = 1646689) B1646689
theorem B7413929 : Blo 432776 7413929 := bstep (se 2 (by rfl) ⟨2780223, by rfl⟩ : syracuseStep 7413929 = 5560447) B5560447
theorem B1098623 : Blo 432776 1098623 := bstep (se 1 (by rfl) ⟨823967, by rfl⟩ : syracuseStep 1098623 = 1647935) B1647935
theorem B435183 : Blo 432776 435183 := bstep (se 1 (by rfl) ⟨326387, by rfl⟩ : syracuseStep 435183 = 652775) B652775
theorem B435231 : Blo 432776 435231 := bstep (se 1 (by rfl) ⟨326423, by rfl⟩ : syracuseStep 435231 = 652847) B652847
theorem B7062815 : Blo 432776 7062815 := bstep (se 1 (by rfl) ⟨5297111, by rfl⟩ : syracuseStep 7062815 = 10594223) B10594223
theorem B3704231 : Blo 432776 3704231 := bstep (se 1 (by rfl) ⟨2778173, by rfl⟩ : syracuseStep 3704231 = 5556347) B5556347
theorem B3302855 : Blo 432776 3302855 := bstep (se 1 (by rfl) ⟨2477141, by rfl⟩ : syracuseStep 3302855 = 4954283) B4954283
theorem B4179563 : Blo 432776 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B2820035 : Blo 432776 2820035 := bstep (se 1 (by rfl) ⟨2115026, by rfl⟩ : syracuseStep 2820035 = 4230053) B4230053
theorem B649391 : Blo 432776 649391 := bstep (se 1 (by rfl) ⟨487043, by rfl⟩ : syracuseStep 649391 = 974087) B974087
theorem B57239743 : Blo 432776 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B7055741 : Blo 432776 7055741 := bstep (se 3 (by rfl) ⟨1322951, by rfl⟩ : syracuseStep 7055741 = 2645903) B2645903
theorem B1812905 : Blo 432776 1812905 := bstep (se 2 (by rfl) ⟨679839, by rfl⟩ : syracuseStep 1812905 = 1359679) B1359679
theorem B8907347 : Blo 432776 8907347 := bstep (se 1 (by rfl) ⟨6680510, by rfl⟩ : syracuseStep 8907347 = 13361021) B13361021
theorem B11127455 : Blo 432776 11127455 := bstep (se 1 (by rfl) ⟨8345591, by rfl⟩ : syracuseStep 11127455 = 16691183) B16691183
theorem B650015 : Blo 432776 650015 := bstep (se 1 (by rfl) ⟨487511, by rfl⟩ : syracuseStep 650015 = 975023) B975023
theorem B781103 : Blo 432776 781103 := bstep (se 1 (by rfl) ⟨585827, by rfl⟩ : syracuseStep 781103 = 1171655) B1171655
theorem B650267 : Blo 432776 650267 := bstep (se 1 (by rfl) ⟨487700, by rfl⟩ : syracuseStep 650267 = 975401) B975401
theorem B977975 : Blo 432776 977975 := bstep (se 1 (by rfl) ⟨733481, by rfl⟩ : syracuseStep 977975 = 1466963) B1466963
theorem B978335 : Blo 432776 978335 := bstep (se 1 (by rfl) ⟨733751, by rfl⟩ : syracuseStep 978335 = 1467503) B1467503
theorem B1412615 : Blo 432776 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B978569 : Blo 432776 978569 := bstep (se 2 (by rfl) ⟨366963, by rfl⟩ : syracuseStep 978569 = 733927) B733927
theorem B651119 : Blo 432776 651119 := bstep (se 1 (by rfl) ⟨488339, by rfl⟩ : syracuseStep 651119 = 976679) B976679
theorem B4829053 : Blo 432776 4829053 := bstep (se 3 (by rfl) ⟨905447, by rfl⟩ : syracuseStep 4829053 = 1810895) B1810895
theorem B487327 : Blo 432776 487327 := bstep (se 1 (by rfl) ⟨365495, by rfl⟩ : syracuseStep 487327 = 730991) B730991
theorem B651167 : Blo 432776 651167 := bstep (se 1 (by rfl) ⟨488375, by rfl⟩ : syracuseStep 651167 = 976751) B976751
theorem B987079 : Blo 432776 987079 := bstep (se 1 (by rfl) ⟨740309, by rfl⟩ : syracuseStep 987079 = 1480619) B1480619
theorem B651401 : Blo 432776 651401 := bstep (se 2 (by rfl) ⟨244275, by rfl⟩ : syracuseStep 651401 = 488551) B488551
theorem B109801615 : Blo 432776 109801615 := bstep (se 1 (by rfl) ⟨82351211, by rfl⟩ : syracuseStep 109801615 = 164702423) B164702423
theorem B2478235 : Blo 432776 2478235 := bstep (se 1 (by rfl) ⟨1858676, by rfl⟩ : syracuseStep 2478235 = 3717353) B3717353
theorem B1651063 : Blo 432776 1651063 := bstep (se 1 (by rfl) ⟨1238297, by rfl⟩ : syracuseStep 1651063 = 2476595) B2476595
theorem B1855943 : Blo 432776 1855943 := bstep (se 1 (by rfl) ⟨1391957, by rfl⟩ : syracuseStep 1855943 = 2783915) B2783915
theorem B16028113 : Blo 432776 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B1462751 : Blo 432776 1462751 := bstep (se 1 (by rfl) ⟨1097063, by rfl⟩ : syracuseStep 1462751 = 2194127) B2194127
theorem B651803 : Blo 432776 651803 := bstep (se 1 (by rfl) ⟨488852, by rfl⟩ : syracuseStep 651803 = 977705) B977705
theorem B1323803 : Blo 432776 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B1176367 : Blo 432776 1176367 := bstep (se 1 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 1176367 = 1764551) B1764551
theorem B8434529 : Blo 432776 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B40555363 : Blo 432776 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B1545247 : Blo 432776 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B488479 : Blo 432776 488479 := bstep (se 1 (by rfl) ⟨366359, by rfl⟩ : syracuseStep 488479 = 732719) B732719
theorem B3290219 : Blo 432776 3290219 := bstep (se 1 (by rfl) ⟨2467664, by rfl⟩ : syracuseStep 3290219 = 4935329) B4935329
theorem B652391 : Blo 432776 652391 := bstep (se 1 (by rfl) ⟨489293, by rfl⟩ : syracuseStep 652391 = 978587) B978587
theorem B1103017 : Blo 432776 1103017 := bstep (se 2 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 1103017 = 827263) B827263
theorem B1389793 : Blo 432776 1389793 := bstep (se 2 (by rfl) ⟨521172, by rfl⟩ : syracuseStep 1389793 = 1042345) B1042345
theorem B824575 : Blo 432776 824575 := bstep (se 1 (by rfl) ⟨618431, by rfl⟩ : syracuseStep 824575 = 1236863) B1236863
theorem B5928227 : Blo 432776 5928227 := bstep (se 1 (by rfl) ⟨4446170, by rfl⟩ : syracuseStep 5928227 = 8892341) B8892341
theorem B652655 : Blo 432776 652655 := bstep (se 1 (by rfl) ⟨489491, by rfl⟩ : syracuseStep 652655 = 978983) B978983
theorem B2774483 : Blo 432776 2774483 := bstep (se 1 (by rfl) ⟨2080862, by rfl⟩ : syracuseStep 2774483 = 4161725) B4161725
theorem B4216411 : Blo 432776 4216411 := bstep (se 1 (by rfl) ⟨3162308, by rfl⟩ : syracuseStep 4216411 = 6324617) B6324617
theorem B734825 : Blo 432776 734825 := bstep (se 2 (by rfl) ⟨275559, by rfl⟩ : syracuseStep 734825 = 551119) B551119
theorem B694441 : Blo 432776 694441 := bstep (se 2 (by rfl) ⟨260415, by rfl⟩ : syracuseStep 694441 = 520831) B520831
theorem B3307715 : Blo 432776 3307715 := bstep (se 1 (by rfl) ⟨2480786, by rfl⟩ : syracuseStep 3307715 = 4961573) B4961573
theorem B653519 : Blo 432776 653519 := bstep (se 1 (by rfl) ⟨490139, by rfl⟩ : syracuseStep 653519 = 980279) B980279
theorem B653567 : Blo 432776 653567 := bstep (se 1 (by rfl) ⟨490175, by rfl⟩ : syracuseStep 653567 = 980351) B980351
theorem B13375813 : Blo 432776 13375813 := bstep (se 4 (by rfl) ⟨1253982, by rfl⟩ : syracuseStep 13375813 = 2507965) B2507965
theorem B1096031 : Blo 432776 1096031 := bstep (se 1 (by rfl) ⟨822023, by rfl⟩ : syracuseStep 1096031 = 1644047) B1644047
theorem B4160267 : Blo 432776 4160267 := bstep (se 1 (by rfl) ⟨3120200, by rfl⟩ : syracuseStep 4160267 = 6240401) B6240401
theorem B2310757303 : Blo 432776 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B433087 : Blo 432776 433087 := bstep (se 1 (by rfl) ⟨324815, by rfl⟩ : syracuseStep 433087 = 649631) B649631
theorem B2087977 : Blo 432776 2087977 := bstep (se 2 (by rfl) ⟨782991, by rfl⟩ : syracuseStep 2087977 = 1565983) B1565983
theorem B7044191 : Blo 432776 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B1096811 : Blo 432776 1096811 := bstep (se 1 (by rfl) ⟨822608, by rfl⟩ : syracuseStep 1096811 = 1645217) B1645217
theorem B11304137 : Blo 432776 11304137 := bstep (se 2 (by rfl) ⟨4239051, by rfl⟩ : syracuseStep 11304137 = 8478103) B8478103
theorem B433435 : Blo 432776 433435 := bstep (se 1 (by rfl) ⟨325076, by rfl⟩ : syracuseStep 433435 = 650153) B650153
theorem B1465721 : Blo 432776 1465721 := bstep (se 2 (by rfl) ⟨549645, by rfl⟩ : syracuseStep 1465721 = 1099291) B1099291
theorem B433647 : Blo 432776 433647 := bstep (se 1 (by rfl) ⟨325235, by rfl⟩ : syracuseStep 433647 = 650471) B650471
theorem B2088551 : Blo 432776 2088551 := bstep (se 1 (by rfl) ⟨1566413, by rfl⟩ : syracuseStep 2088551 = 3132827) B3132827
theorem B2465387 : Blo 432776 2465387 := bstep (se 1 (by rfl) ⟨1849040, by rfl⟩ : syracuseStep 2465387 = 3698081) B3698081
theorem B5930621 : Blo 432776 5930621 := bstep (se 3 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 5930621 = 2223983) B2223983
theorem B433791 : Blo 432776 433791 := bstep (se 1 (by rfl) ⟨325343, by rfl⟩ : syracuseStep 433791 = 650687) B650687
theorem B4177565 : Blo 432776 4177565 := bstep (se 3 (by rfl) ⟨783293, by rfl⟩ : syracuseStep 4177565 = 1566587) B1566587
theorem B1171135 : Blo 432776 1171135 := bstep (se 1 (by rfl) ⟨878351, by rfl⟩ : syracuseStep 1171135 = 1756703) B1756703
theorem B107306795 : Blo 432776 107306795 := bstep (se 1 (by rfl) ⟨80480096, by rfl⟩ : syracuseStep 107306795 = 160960193) B160960193
theorem B696127 : Blo 432776 696127 := bstep (se 1 (by rfl) ⟨522095, by rfl⟩ : syracuseStep 696127 = 1044191) B1044191
theorem B434011 : Blo 432776 434011 := bstep (se 1 (by rfl) ⟨325508, by rfl⟩ : syracuseStep 434011 = 651017) B651017
theorem B11444141 : Blo 432776 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B2195423 : Blo 432776 2195423 := bstep (se 1 (by rfl) ⟨1646567, by rfl⟩ : syracuseStep 2195423 = 3293135) B3293135
theorem B434267 : Blo 432776 434267 := bstep (se 1 (by rfl) ⟨325700, by rfl⟩ : syracuseStep 434267 = 651401) B651401
theorem B925921 : Blo 432776 925921 := bstep (se 2 (by rfl) ⟨347220, by rfl⟩ : syracuseStep 925921 = 694441) B694441
theorem B1237295 : Blo 432776 1237295 := bstep (se 1 (by rfl) ⟨927971, by rfl⟩ : syracuseStep 1237295 = 1855943) B1855943
theorem B975167 : Blo 432776 975167 := bstep (se 1 (by rfl) ⟨731375, by rfl⟩ : syracuseStep 975167 = 1462751) B1462751
theorem B434535 : Blo 432776 434535 := bstep (se 1 (by rfl) ⟨325901, by rfl⟩ : syracuseStep 434535 = 651803) B651803
theorem B17834417 : Blo 432776 17834417 := bstep (se 2 (by rfl) ⟨6687906, by rfl⟩ : syracuseStep 17834417 = 13375813) B13375813
theorem B434927 : Blo 432776 434927 := bstep (se 1 (by rfl) ⟨326195, by rfl⟩ : syracuseStep 434927 = 652391) B652391
theorem B435103 : Blo 432776 435103 := bstep (se 1 (by rfl) ⟨326327, by rfl⟩ : syracuseStep 435103 = 652655) B652655
theorem B2786375 : Blo 432776 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B2205143 : Blo 432776 2205143 := bstep (se 1 (by rfl) ⟨1653857, by rfl⟩ : syracuseStep 2205143 = 3307715) B3307715
theorem B435679 : Blo 432776 435679 := bstep (se 1 (by rfl) ⟨326759, by rfl⟩ : syracuseStep 435679 = 653519) B653519
theorem B435711 : Blo 432776 435711 := bstep (se 1 (by rfl) ⟨326783, by rfl⟩ : syracuseStep 435711 = 653567) B653567
theorem B730687 : Blo 432776 730687 := bstep (se 1 (by rfl) ⟨548015, by rfl⟩ : syracuseStep 730687 = 1096031) B1096031
theorem B4703827 : Blo 432776 4703827 := bstep (se 1 (by rfl) ⟨3527870, by rfl⟩ : syracuseStep 4703827 = 7055741) B7055741
theorem B1853057 : Blo 432776 1853057 := bstep (se 2 (by rfl) ⟨694896, by rfl⟩ : syracuseStep 1853057 = 1389793) B1389793
theorem B1099433 : Blo 432776 1099433 := bstep (se 2 (by rfl) ⟨412287, by rfl⟩ : syracuseStep 1099433 = 824575) B824575
theorem B4696127 : Blo 432776 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B731207 : Blo 432776 731207 := bstep (se 1 (by rfl) ⟨548405, by rfl⟩ : syracuseStep 731207 = 1096811) B1096811
theorem B5621881 : Blo 432776 5621881 := bstep (se 2 (by rfl) ⟨2108205, by rfl⟩ : syracuseStep 5621881 = 4216411) B4216411
theorem B2082941 : Blo 432776 2082941 := bstep (se 3 (by rfl) ⟨390551, by rfl⟩ : syracuseStep 2082941 = 781103) B781103
theorem B977147 : Blo 432776 977147 := bstep (se 1 (by rfl) ⟨732860, by rfl⟩ : syracuseStep 977147 = 1465721) B1465721
theorem B928169 : Blo 432776 928169 := bstep (se 2 (by rfl) ⟨348063, by rfl⟩ : syracuseStep 928169 = 696127) B696127
theorem B649769 : Blo 432776 649769 := bstep (se 2 (by rfl) ⟨243663, by rfl⟩ : syracuseStep 649769 = 487327) B487327
theorem B7629427 : Blo 432776 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B4942619 : Blo 432776 4942619 := bstep (se 1 (by rfl) ⟨3706964, by rfl⟩ : syracuseStep 4942619 = 7413929) B7413929
theorem B146402153 : Blo 432776 146402153 := bstep (se 2 (by rfl) ⟨54900807, by rfl⟩ : syracuseStep 146402153 = 109801615) B109801615
theorem B3304313 : Blo 432776 3304313 := bstep (se 2 (by rfl) ⟨1239117, by rfl⟩ : syracuseStep 3304313 = 2478235) B2478235
theorem B76319657 : Blo 432776 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B5623019 : Blo 432776 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B732415 : Blo 432776 732415 := bstep (se 1 (by rfl) ⟨549311, by rfl⟩ : syracuseStep 732415 = 1098623) B1098623
theorem B3952151 : Blo 432776 3952151 := bstep (se 1 (by rfl) ⟨2964113, by rfl⟩ : syracuseStep 3952151 = 5928227) B5928227
theorem B2469487 : Blo 432776 2469487 := bstep (se 1 (by rfl) ⟨1852115, by rfl⟩ : syracuseStep 2469487 = 3704231) B3704231
theorem B1568489 : Blo 432776 1568489 := bstep (se 2 (by rfl) ⟨588183, by rfl⟩ : syracuseStep 1568489 = 1176367) B1176367
theorem B1880023 : Blo 432776 1880023 := bstep (se 1 (by rfl) ⟨1410017, by rfl⟩ : syracuseStep 1880023 = 2820035) B2820035
theorem B2060329 : Blo 432776 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B651305 : Blo 432776 651305 := bstep (se 2 (by rfl) ⟨244239, by rfl⟩ : syracuseStep 651305 = 488479) B488479
theorem B23752925 : Blo 432776 23752925 := bstep (se 3 (by rfl) ⟨4453673, by rfl⟩ : syracuseStep 23752925 = 8907347) B8907347
theorem B1470689 : Blo 432776 1470689 := bstep (se 2 (by rfl) ⟨551508, by rfl⟩ : syracuseStep 1470689 = 1103017) B1103017
theorem B1208603 : Blo 432776 1208603 := bstep (se 1 (by rfl) ⟨906452, by rfl⟩ : syracuseStep 1208603 = 1812905) B1812905
theorem B7418303 : Blo 432776 7418303 := bstep (se 1 (by rfl) ⟨5563727, by rfl⟩ : syracuseStep 7418303 = 11127455) B11127455
theorem B2773511 : Blo 432776 2773511 := bstep (se 1 (by rfl) ⟨2080133, by rfl⟩ : syracuseStep 2773511 = 4160267) B4160267
theorem B651983 : Blo 432776 651983 := bstep (se 1 (by rfl) ⟨488987, by rfl⟩ : syracuseStep 651983 = 977975) B977975
theorem B1561513 : Blo 432776 1561513 := bstep (se 2 (by rfl) ⟨585567, by rfl⟩ : syracuseStep 1561513 = 1171135) B1171135
theorem B652223 : Blo 432776 652223 := bstep (se 1 (by rfl) ⟨489167, by rfl⟩ : syracuseStep 652223 = 978335) B978335
theorem B1643591 : Blo 432776 1643591 := bstep (se 1 (by rfl) ⟨1232693, by rfl⟩ : syracuseStep 1643591 = 2465387) B2465387
theorem B3953747 : Blo 432776 3953747 := bstep (se 1 (by rfl) ⟨2965310, by rfl⟩ : syracuseStep 3953747 = 5930621) B5930621
theorem B652379 : Blo 432776 652379 := bstep (se 1 (by rfl) ⟨489284, by rfl⟩ : syracuseStep 652379 = 978569) B978569
theorem B71537863 : Blo 432776 71537863 := bstep (se 1 (by rfl) ⟨53653397, by rfl⟩ : syracuseStep 71537863 = 107306795) B107306795
theorem B1316105 : Blo 432776 1316105 := bstep (se 2 (by rfl) ⟨493539, by rfl⟩ : syracuseStep 1316105 = 987079) B987079
theorem B1463615 : Blo 432776 1463615 := bstep (se 1 (by rfl) ⟨1097711, by rfl⟩ : syracuseStep 1463615 = 2195423) B2195423
theorem B1316263 : Blo 432776 1316263 := bstep (se 1 (by rfl) ⟨987197, by rfl⟩ : syracuseStep 1316263 = 1974395) B1974395
theorem B1463723 : Blo 432776 1463723 := bstep (se 1 (by rfl) ⟨1097792, by rfl⟩ : syracuseStep 1463723 = 2195585) B2195585
theorem B2201417 : Blo 432776 2201417 := bstep (se 2 (by rfl) ⟨825531, by rfl⟩ : syracuseStep 2201417 = 1651063) B1651063
theorem B21370817 : Blo 432776 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B2193479 : Blo 432776 2193479 := bstep (se 1 (by rfl) ⟨1645109, by rfl⟩ : syracuseStep 2193479 = 3290219) B3290219
theorem B4708543 : Blo 432776 4708543 := bstep (se 1 (by rfl) ⟨3531407, by rfl⟩ : syracuseStep 4708543 = 7062815) B7062815
theorem B2201903 : Blo 432776 2201903 := bstep (se 1 (by rfl) ⟨1651427, by rfl⟩ : syracuseStep 2201903 = 3302855) B3302855
theorem B1849655 : Blo 432776 1849655 := bstep (se 1 (by rfl) ⟨1387241, by rfl⟩ : syracuseStep 1849655 = 2774483) B2774483
theorem B489883 : Blo 432776 489883 := bstep (se 1 (by rfl) ⟨367412, by rfl⟩ : syracuseStep 489883 = 734825) B734825
theorem B54073817 : Blo 432776 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B3081009737 : Blo 432776 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B2783969 : Blo 432776 2783969 := bstep (se 2 (by rfl) ⟨1043988, by rfl⟩ : syracuseStep 2783969 = 2087977) B2087977
theorem B432927 : Blo 432776 432927 := bstep (se 1 (by rfl) ⟨324695, by rfl⟩ : syracuseStep 432927 = 649391) B649391
theorem B5569469 : Blo 432776 5569469 := bstep (se 3 (by rfl) ⟨1044275, by rfl⟩ : syracuseStep 5569469 = 2088551) B2088551
theorem B433343 : Blo 432776 433343 := bstep (se 1 (by rfl) ⟨325007, by rfl⟩ : syracuseStep 433343 = 650015) B650015
theorem B433511 : Blo 432776 433511 := bstep (se 1 (by rfl) ⟨325133, by rfl⟩ : syracuseStep 433511 = 650267) B650267
theorem B3530141 : Blo 432776 3530141 := bstep (se 3 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 3530141 = 1323803) B1323803
theorem B7536091 : Blo 432776 7536091 := bstep (se 1 (by rfl) ⟨5652068, by rfl⟩ : syracuseStep 7536091 = 11304137) B11304137
theorem B941743 : Blo 432776 941743 := bstep (se 1 (by rfl) ⟨706307, by rfl⟩ : syracuseStep 941743 = 1412615) B1412615
theorem B2785043 : Blo 432776 2785043 := bstep (se 1 (by rfl) ⟨2088782, by rfl⟩ : syracuseStep 2785043 = 4177565) B4177565
theorem B6438737 : Blo 432776 6438737 := bstep (se 2 (by rfl) ⟨2414526, by rfl⟩ : syracuseStep 6438737 = 4829053) B4829053
theorem B434079 : Blo 432776 434079 := bstep (se 1 (by rfl) ⟨325559, by rfl⟩ : syracuseStep 434079 = 651119) B651119
theorem B434111 : Blo 432776 434111 := bstep (se 1 (by rfl) ⟨325583, by rfl⟩ : syracuseStep 434111 = 651167) B651167
theorem B434203 : Blo 432776 434203 := bstep (se 1 (by rfl) ⟨325652, by rfl⟩ : syracuseStep 434203 = 651305) B651305
theorem B15835283 : Blo 432776 15835283 := bstep (se 1 (by rfl) ⟨11876462, by rfl⟩ : syracuseStep 15835283 = 23752925) B23752925
theorem B7495841 : Blo 432776 7495841 := bstep (se 2 (by rfl) ⟨2810940, by rfl⟩ : syracuseStep 7495841 = 5621881) B5621881
theorem B434655 : Blo 432776 434655 := bstep (se 1 (by rfl) ⟨325991, by rfl⟩ : syracuseStep 434655 = 651983) B651983
theorem B434815 : Blo 432776 434815 := bstep (se 1 (by rfl) ⟨326111, by rfl⟩ : syracuseStep 434815 = 652223) B652223
theorem B434919 : Blo 432776 434919 := bstep (se 1 (by rfl) ⟨326189, by rfl⟩ : syracuseStep 434919 = 652379) B652379
theorem B4932413 : Blo 432776 4932413 := bstep (se 3 (by rfl) ⟨924827, by rfl⟩ : syracuseStep 4932413 = 1849655) B1849655
theorem B877403 : Blo 432776 877403 := bstep (se 1 (by rfl) ⟨658052, by rfl⟩ : syracuseStep 877403 = 1316105) B1316105
theorem B975743 : Blo 432776 975743 := bstep (se 1 (by rfl) ⟨731807, by rfl⟩ : syracuseStep 975743 = 1463615) B1463615
theorem B975815 : Blo 432776 975815 := bstep (se 1 (by rfl) ⟨731861, by rfl⟩ : syracuseStep 975815 = 1463723) B1463723
theorem B1467611 : Blo 432776 1467611 := bstep (se 1 (by rfl) ⟨1100708, by rfl⟩ : syracuseStep 1467611 = 2201417) B2201417
theorem B2082017 : Blo 432776 2082017 := bstep (se 2 (by rfl) ⟨780756, by rfl⟩ : syracuseStep 2082017 = 1561513) B1561513
theorem B3130751 : Blo 432776 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B1467935 : Blo 432776 1467935 := bstep (se 1 (by rfl) ⟨1100951, by rfl⟩ : syracuseStep 1467935 = 2201903) B2201903
theorem B976553 : Blo 432776 976553 := bstep (se 2 (by rfl) ⟨366207, by rfl⟩ : syracuseStep 976553 = 732415) B732415
theorem B3295079 : Blo 432776 3295079 := bstep (se 1 (by rfl) ⟨2471309, by rfl⟩ : syracuseStep 3295079 = 4942619) B4942619
theorem B1755017 : Blo 432776 1755017 := bstep (se 2 (by rfl) ⟨658131, by rfl⟩ : syracuseStep 1755017 = 1316263) B1316263
theorem B97601435 : Blo 432776 97601435 := bstep (se 1 (by rfl) ⟨73201076, by rfl⟩ : syracuseStep 97601435 = 146402153) B146402153
theorem B3712979 : Blo 432776 3712979 := bstep (se 1 (by rfl) ⟨2784734, by rfl⟩ : syracuseStep 3712979 = 5569469) B5569469
theorem B1255657 : Blo 432776 1255657 := bstep (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) B941743
theorem B2353427 : Blo 432776 2353427 := bstep (se 1 (by rfl) ⟨1765070, by rfl⟩ : syracuseStep 2353427 = 3530141) B3530141
theorem B16730549 : Blo 432776 16730549 := bstep (se 5 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 16730549 = 1568489) B1568489
theorem B2747105 : Blo 432776 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B805735 : Blo 432776 805735 := bstep (se 1 (by rfl) ⟨604301, by rfl⟩ : syracuseStep 805735 = 1208603) B1208603
theorem B650111 : Blo 432776 650111 := bstep (se 1 (by rfl) ⟨487583, by rfl⟩ : syracuseStep 650111 = 975167) B975167
theorem B6278057 : Blo 432776 6278057 := bstep (se 2 (by rfl) ⟨2354271, by rfl⟩ : syracuseStep 6278057 = 4708543) B4708543
theorem B11889611 : Blo 432776 11889611 := bstep (se 1 (by rfl) ⟨8917208, by rfl⟩ : syracuseStep 11889611 = 17834417) B17834417
theorem B1470095 : Blo 432776 1470095 := bstep (se 1 (by rfl) ⟨1102571, by rfl⟩ : syracuseStep 1470095 = 2205143) B2205143
theorem B732955 : Blo 432776 732955 := bstep (se 1 (by rfl) ⟨549716, by rfl⟩ : syracuseStep 732955 = 1099433) B1099433
theorem B1462319 : Blo 432776 1462319 := bstep (se 1 (by rfl) ⟨1096739, by rfl⟩ : syracuseStep 1462319 = 2193479) B2193479
theorem B487471 : Blo 432776 487471 := bstep (se 1 (by rfl) ⟨365603, by rfl⟩ : syracuseStep 487471 = 731207) B731207
theorem B1388627 : Blo 432776 1388627 := bstep (se 1 (by rfl) ⟨1041470, by rfl⟩ : syracuseStep 1388627 = 2082941) B2082941
theorem B651431 : Blo 432776 651431 := bstep (se 1 (by rfl) ⟨488573, by rfl⟩ : syracuseStep 651431 = 977147) B977147
theorem B95383817 : Blo 432776 95383817 := bstep (se 2 (by rfl) ⟨35768931, by rfl⟩ : syracuseStep 95383817 = 71537863) B71537863
theorem B618779 : Blo 432776 618779 := bstep (se 1 (by rfl) ⟨464084, by rfl⟩ : syracuseStep 618779 = 928169) B928169
theorem B36049211 : Blo 432776 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B1855979 : Blo 432776 1855979 := bstep (se 1 (by rfl) ⟨1391984, by rfl⟩ : syracuseStep 1855979 = 2783969) B2783969
theorem B10048121 : Blo 432776 10048121 := bstep (se 2 (by rfl) ⟨3768045, by rfl⟩ : syracuseStep 10048121 = 7536091) B7536091
theorem B6271769 : Blo 432776 6271769 := bstep (se 2 (by rfl) ⟨2351913, by rfl⟩ : syracuseStep 6271769 = 4703827) B4703827
theorem B3748679 : Blo 432776 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B2634767 : Blo 432776 2634767 := bstep (se 1 (by rfl) ⟨1976075, by rfl⟩ : syracuseStep 2634767 = 3952151) B3952151
theorem B56988845 : Blo 432776 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B1856695 : Blo 432776 1856695 := bstep (se 1 (by rfl) ⟨1392521, by rfl⟩ : syracuseStep 1856695 = 2785043) B2785043
theorem B980459 : Blo 432776 980459 := bstep (se 1 (by rfl) ⟨735344, by rfl⟩ : syracuseStep 980459 = 1470689) B1470689
theorem B4945535 : Blo 432776 4945535 := bstep (se 1 (by rfl) ⟨3709151, by rfl⟩ : syracuseStep 4945535 = 7418303) B7418303
theorem B1849007 : Blo 432776 1849007 := bstep (se 1 (by rfl) ⟨1386755, by rfl⟩ : syracuseStep 1849007 = 2773511) B2773511
theorem B653177 : Blo 432776 653177 := bstep (se 2 (by rfl) ⟨244941, by rfl⟩ : syracuseStep 653177 = 489883) B489883
theorem B1095727 : Blo 432776 1095727 := bstep (se 1 (by rfl) ⟨821795, by rfl⟩ : syracuseStep 1095727 = 1643591) B1643591
theorem B1857583 : Blo 432776 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B2635831 : Blo 432776 2635831 := bstep (se 1 (by rfl) ⟨1976873, by rfl⟩ : syracuseStep 2635831 = 3953747) B3953747
theorem B3299453 : Blo 432776 3299453 := bstep (se 3 (by rfl) ⟨618647, by rfl⟩ : syracuseStep 3299453 = 1237295) B1237295
theorem B10172569 : Blo 432776 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B1235371 : Blo 432776 1235371 := bstep (se 1 (by rfl) ⟨926528, by rfl⟩ : syracuseStep 1235371 = 1853057) B1853057
theorem B4938245 : Blo 432776 4938245 := bstep (se 4 (by rfl) ⟨462960, by rfl⟩ : syracuseStep 4938245 = 925921) B925921
theorem B8216025965 : Blo 432776 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B433179 : Blo 432776 433179 := bstep (se 1 (by rfl) ⟨324884, by rfl⟩ : syracuseStep 433179 = 649769) B649769
theorem B2202875 : Blo 432776 2202875 := bstep (se 1 (by rfl) ⟨1652156, by rfl⟩ : syracuseStep 2202875 = 3304313) B3304313
theorem B50879771 : Blo 432776 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B974249 : Blo 432776 974249 := bstep (se 2 (by rfl) ⟨365343, by rfl⟩ : syracuseStep 974249 = 730687) B730687
theorem B3292649 : Blo 432776 3292649 := bstep (se 2 (by rfl) ⟨1234743, by rfl⟩ : syracuseStep 3292649 = 2469487) B2469487
theorem B17169965 : Blo 432776 17169965 := bstep (se 3 (by rfl) ⟨3219368, by rfl⟩ : syracuseStep 17169965 = 6438737) B6438737
theorem B2506697 : Blo 432776 2506697 := bstep (se 2 (by rfl) ⟨940011, by rfl⟩ : syracuseStep 2506697 = 1880023) B1880023
theorem B974879 : Blo 432776 974879 := bstep (se 1 (by rfl) ⟨731159, by rfl⟩ : syracuseStep 974879 = 1462319) B1462319
theorem B925751 : Blo 432776 925751 := bstep (se 1 (by rfl) ⟨694313, by rfl⟩ : syracuseStep 925751 = 1388627) B1388627
theorem B3514441 : Blo 432776 3514441 := bstep (se 2 (by rfl) ⟨1317915, by rfl⟩ : syracuseStep 3514441 = 2635831) B2635831
theorem B4997227 : Blo 432776 4997227 := bstep (se 1 (by rfl) ⟨3747920, by rfl⟩ : syracuseStep 4997227 = 7495841) B7495841
theorem B434287 : Blo 432776 434287 := bstep (se 1 (by rfl) ⟨325715, by rfl⟩ : syracuseStep 434287 = 651431) B651431
theorem B1237319 : Blo 432776 1237319 := bstep (se 1 (by rfl) ⟨927989, by rfl⟩ : syracuseStep 1237319 = 1855979) B1855979
theorem B2499119 : Blo 432776 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B1647161 : Blo 432776 1647161 := bstep (se 2 (by rfl) ⟨617685, by rfl⟩ : syracuseStep 1647161 = 1235371) B1235371
theorem B8348669 : Blo 432776 8348669 := bstep (se 3 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 8348669 = 3130751) B3130751
theorem B1074313 : Blo 432776 1074313 := bstep (se 2 (by rfl) ⟨402867, by rfl⟩ : syracuseStep 1074313 = 805735) B805735
theorem B2196719 : Blo 432776 2196719 := bstep (se 1 (by rfl) ⟨1647539, by rfl⟩ : syracuseStep 2196719 = 3295079) B3295079
theorem B435451 : Blo 432776 435451 := bstep (se 1 (by rfl) ⟨326588, by rfl⟩ : syracuseStep 435451 = 653177) B653177
theorem B2475319 : Blo 432776 2475319 := bstep (se 1 (by rfl) ⟨1856489, by rfl⟩ : syracuseStep 2475319 = 3712979) B3712979
theorem B2475593 : Blo 432776 2475593 := bstep (se 2 (by rfl) ⟨928347, by rfl⟩ : syracuseStep 2475593 = 1856695) B1856695
theorem B1468583 : Blo 432776 1468583 := bstep (se 1 (by rfl) ⟨1101437, by rfl⟩ : syracuseStep 1468583 = 2202875) B2202875
theorem B649499 : Blo 432776 649499 := bstep (se 1 (by rfl) ⟨487124, by rfl⟩ : syracuseStep 649499 = 974249) B974249
theorem B11446643 : Blo 432776 11446643 := bstep (se 1 (by rfl) ⟨8584982, by rfl⟩ : syracuseStep 11446643 = 17169965) B17169965
theorem B977273 : Blo 432776 977273 := bstep (se 2 (by rfl) ⟨366477, by rfl⟩ : syracuseStep 977273 = 732955) B732955
theorem B1460969 : Blo 432776 1460969 := bstep (se 2 (by rfl) ⟨547863, by rfl⟩ : syracuseStep 1460969 = 1095727) B1095727
theorem B649961 : Blo 432776 649961 := bstep (se 2 (by rfl) ⟨243735, by rfl⟩ : syracuseStep 649961 = 487471) B487471
theorem B2476777 : Blo 432776 2476777 := bstep (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) B1857583
theorem B63589211 : Blo 432776 63589211 := bstep (se 1 (by rfl) ⟨47691908, by rfl⟩ : syracuseStep 63589211 = 95383817) B95383817
theorem B1674209 : Blo 432776 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B4181179 : Blo 432776 4181179 := bstep (se 1 (by rfl) ⟨3135884, by rfl⟩ : syracuseStep 4181179 = 6271769) B6271769
theorem B3288275 : Blo 432776 3288275 := bstep (se 1 (by rfl) ⟨2466206, by rfl⟩ : syracuseStep 3288275 = 4932413) B4932413
theorem B650495 : Blo 432776 650495 := bstep (se 1 (by rfl) ⟨487871, by rfl⟩ : syracuseStep 650495 = 975743) B975743
theorem B650543 : Blo 432776 650543 := bstep (se 1 (by rfl) ⟨487907, by rfl⟩ : syracuseStep 650543 = 975815) B975815
theorem B1756511 : Blo 432776 1756511 := bstep (se 1 (by rfl) ⟨1317383, by rfl⟩ : syracuseStep 1756511 = 2634767) B2634767
theorem B1650077 : Blo 432776 1650077 := bstep (se 3 (by rfl) ⟨309389, by rfl⟩ : syracuseStep 1650077 = 618779) B618779
theorem B978407 : Blo 432776 978407 := bstep (se 1 (by rfl) ⟨733805, by rfl⟩ : syracuseStep 978407 = 1467611) B1467611
theorem B1388011 : Blo 432776 1388011 := bstep (se 1 (by rfl) ⟨1041008, by rfl⟩ : syracuseStep 1388011 = 2082017) B2082017
theorem B978623 : Blo 432776 978623 := bstep (se 1 (by rfl) ⟨733967, by rfl⟩ : syracuseStep 978623 = 1467935) B1467935
theorem B3297023 : Blo 432776 3297023 := bstep (se 1 (by rfl) ⟨2472767, by rfl⟩ : syracuseStep 3297023 = 4945535) B4945535
theorem B651035 : Blo 432776 651035 := bstep (se 1 (by rfl) ⟨488276, by rfl⟩ : syracuseStep 651035 = 976553) B976553
theorem B1232671 : Blo 432776 1232671 := bstep (se 1 (by rfl) ⟨924503, by rfl⟩ : syracuseStep 1232671 = 1849007) B1849007
theorem B2199635 : Blo 432776 2199635 := bstep (se 1 (by rfl) ⟨1649726, by rfl⟩ : syracuseStep 2199635 = 3299453) B3299453
theorem B1568951 : Blo 432776 1568951 := bstep (se 1 (by rfl) ⟨1176713, by rfl⟩ : syracuseStep 1568951 = 2353427) B2353427
theorem B11153699 : Blo 432776 11153699 := bstep (se 1 (by rfl) ⟨8365274, by rfl⟩ : syracuseStep 11153699 = 16730549) B16730549
theorem B1831403 : Blo 432776 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B7926407 : Blo 432776 7926407 := bstep (se 1 (by rfl) ⟨5944805, by rfl⟩ : syracuseStep 7926407 = 11889611) B11889611
theorem B33919847 : Blo 432776 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B2339741 : Blo 432776 2339741 := bstep (se 3 (by rfl) ⟨438701, by rfl⟩ : syracuseStep 2339741 = 877403) B877403
theorem B980063 : Blo 432776 980063 := bstep (se 1 (by rfl) ⟨735047, by rfl⟩ : syracuseStep 980063 = 1470095) B1470095
theorem B10556855 : Blo 432776 10556855 := bstep (se 1 (by rfl) ⟨7917641, by rfl⟩ : syracuseStep 10556855 = 15835283) B15835283
theorem B13563425 : Blo 432776 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B24032807 : Blo 432776 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B6698747 : Blo 432776 6698747 := bstep (se 1 (by rfl) ⟨5024060, by rfl⟩ : syracuseStep 6698747 = 10048121) B10048121
theorem B37992563 : Blo 432776 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B653639 : Blo 432776 653639 := bstep (se 1 (by rfl) ⟨490229, by rfl⟩ : syracuseStep 653639 = 980459) B980459
theorem B1170011 : Blo 432776 1170011 := bstep (se 1 (by rfl) ⟨877508, by rfl⟩ : syracuseStep 1170011 = 1755017) B1755017
theorem B65067623 : Blo 432776 65067623 := bstep (se 1 (by rfl) ⟨48800717, by rfl⟩ : syracuseStep 65067623 = 97601435) B97601435
theorem B3292163 : Blo 432776 3292163 := bstep (se 1 (by rfl) ⟨2469122, by rfl⟩ : syracuseStep 3292163 = 4938245) B4938245
theorem B5477350643 : Blo 432776 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B433407 : Blo 432776 433407 := bstep (se 1 (by rfl) ⟨325055, by rfl⟩ : syracuseStep 433407 = 650111) B650111
theorem B4185371 : Blo 432776 4185371 := bstep (se 1 (by rfl) ⟨3139028, by rfl⟩ : syracuseStep 4185371 = 6278057) B6278057
theorem B2195099 : Blo 432776 2195099 := bstep (se 1 (by rfl) ⟨1646324, by rfl⟩ : syracuseStep 2195099 = 3292649) B3292649
theorem B1671131 : Blo 432776 1671131 := bstep (se 1 (by rfl) ⟨1253348, by rfl⟩ : syracuseStep 1671131 = 2506697) B2506697
theorem B1466423 : Blo 432776 1466423 := bstep (se 1 (by rfl) ⟨1099817, by rfl⟩ : syracuseStep 1466423 = 2199635) B2199635
theorem B4685921 : Blo 432776 4685921 := bstep (se 2 (by rfl) ⟨1757220, by rfl⟩ : syracuseStep 4685921 = 3514441) B3514441
theorem B1220935 : Blo 432776 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B1098107 : Blo 432776 1098107 := bstep (se 1 (by rfl) ⟨823580, by rfl⟩ : syracuseStep 1098107 = 1647161) B1647161
theorem B5284271 : Blo 432776 5284271 := bstep (se 1 (by rfl) ⟨3963203, by rfl⟩ : syracuseStep 5284271 = 7926407) B7926407
theorem B7037903 : Blo 432776 7037903 := bstep (se 1 (by rfl) ⟨5278427, by rfl⟩ : syracuseStep 7037903 = 10556855) B10556855
theorem B30524381 : Blo 432776 30524381 := bstep (se 3 (by rfl) ⟨5723321, by rfl⟩ : syracuseStep 30524381 = 11446643) B11446643
theorem B3302369 : Blo 432776 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B435759 : Blo 432776 435759 := bstep (se 1 (by rfl) ⟨326819, by rfl⟩ : syracuseStep 435759 = 653639) B653639
theorem B43378415 : Blo 432776 43378415 := bstep (se 1 (by rfl) ⟨32533811, by rfl⟩ : syracuseStep 43378415 = 65067623) B65067623
theorem B1100051 : Blo 432776 1100051 := bstep (se 1 (by rfl) ⟨825038, by rfl⟩ : syracuseStep 1100051 = 1650077) B1650077
theorem B2198015 : Blo 432776 2198015 := bstep (se 1 (by rfl) ⟨1648511, by rfl⟩ : syracuseStep 2198015 = 3297023) B3297023
theorem B649919 : Blo 432776 649919 := bstep (se 1 (by rfl) ⟨487439, by rfl⟩ : syracuseStep 649919 = 974879) B974879
theorem B617167 : Blo 432776 617167 := bstep (se 1 (by rfl) ⟨462875, by rfl⟩ : syracuseStep 617167 = 925751) B925751
theorem B6662969 : Blo 432776 6662969 := bstep (se 2 (by rfl) ⟨2498613, by rfl⟩ : syracuseStep 6662969 = 4997227) B4997227
theorem B1666079 : Blo 432776 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B22613231 : Blo 432776 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B1559827 : Blo 432776 1559827 := bstep (se 1 (by rfl) ⟨1169870, by rfl⟩ : syracuseStep 1559827 = 2339741) B2339741
theorem B5565779 : Blo 432776 5565779 := bstep (se 1 (by rfl) ⟨4174334, by rfl⟩ : syracuseStep 5565779 = 8348669) B8348669
theorem B1650395 : Blo 432776 1650395 := bstep (se 1 (by rfl) ⟨1237796, by rfl⟩ : syracuseStep 1650395 = 2475593) B2475593
theorem B979055 : Blo 432776 979055 := bstep (se 1 (by rfl) ⟨734291, by rfl⟩ : syracuseStep 979055 = 1468583) B1468583
theorem B5574905 : Blo 432776 5574905 := bstep (se 2 (by rfl) ⟨2090589, by rfl⟩ : syracuseStep 5574905 = 4181179) B4181179
theorem B651515 : Blo 432776 651515 := bstep (se 1 (by rfl) ⟨488636, by rfl⟩ : syracuseStep 651515 = 977273) B977273
theorem B17863325 : Blo 432776 17863325 := bstep (se 3 (by rfl) ⟨3349373, by rfl⟩ : syracuseStep 17863325 = 6698747) B6698747
theorem B2192183 : Blo 432776 2192183 := bstep (se 1 (by rfl) ⟨1644137, by rfl⟩ : syracuseStep 2192183 = 3288275) B3288275
theorem B2790247 : Blo 432776 2790247 := bstep (se 1 (by rfl) ⟨2092685, by rfl⟩ : syracuseStep 2790247 = 4185371) B4185371
theorem B652271 : Blo 432776 652271 := bstep (se 1 (by rfl) ⟨489203, by rfl⟩ : syracuseStep 652271 = 978407) B978407
theorem B1643561 : Blo 432776 1643561 := bstep (se 2 (by rfl) ⟨616335, by rfl⟩ : syracuseStep 1643561 = 1232671) B1232671
theorem B1463399 : Blo 432776 1463399 := bstep (se 1 (by rfl) ⟨1097549, by rfl⟩ : syracuseStep 1463399 = 2195099) B2195099
theorem B652415 : Blo 432776 652415 := bstep (se 1 (by rfl) ⟨489311, by rfl⟩ : syracuseStep 652415 = 978623) B978623
theorem B1045967 : Blo 432776 1045967 := bstep (se 1 (by rfl) ⟨784475, by rfl⟩ : syracuseStep 1045967 = 1568951) B1568951
theorem B7435799 : Blo 432776 7435799 := bstep (se 1 (by rfl) ⟨5576849, by rfl⟩ : syracuseStep 7435799 = 11153699) B11153699
theorem B824879 : Blo 432776 824879 := bstep (se 1 (by rfl) ⟨618659, by rfl⟩ : syracuseStep 824879 = 1237319) B1237319
theorem B653375 : Blo 432776 653375 := bstep (se 1 (by rfl) ⟨490031, by rfl⟩ : syracuseStep 653375 = 980063) B980063
theorem B1464479 : Blo 432776 1464479 := bstep (se 1 (by rfl) ⟨1098359, by rfl⟩ : syracuseStep 1464479 = 2196719) B2196719
theorem B9042283 : Blo 432776 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B16021871 : Blo 432776 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B25328375 : Blo 432776 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B1432417 : Blo 432776 1432417 := bstep (se 2 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 1432417 = 1074313) B1074313
theorem B432999 : Blo 432776 432999 := bstep (se 1 (by rfl) ⟨324749, by rfl⟩ : syracuseStep 432999 = 649499) B649499
theorem B3120029 : Blo 432776 3120029 := bstep (se 3 (by rfl) ⟨585005, by rfl⟩ : syracuseStep 3120029 = 1170011) B1170011
theorem B3300425 : Blo 432776 3300425 := bstep (se 2 (by rfl) ⟨1237659, by rfl⟩ : syracuseStep 3300425 = 2475319) B2475319
theorem B973979 : Blo 432776 973979 := bstep (se 1 (by rfl) ⟨730484, by rfl⟩ : syracuseStep 973979 = 1460969) B1460969
theorem B433307 : Blo 432776 433307 := bstep (se 1 (by rfl) ⟨324980, by rfl⟩ : syracuseStep 433307 = 649961) B649961
theorem B42392807 : Blo 432776 42392807 := bstep (se 1 (by rfl) ⟨31794605, by rfl⟩ : syracuseStep 42392807 = 63589211) B63589211
theorem B1850681 : Blo 432776 1850681 := bstep (se 2 (by rfl) ⟨694005, by rfl⟩ : syracuseStep 1850681 = 1388011) B1388011
theorem B2194775 : Blo 432776 2194775 := bstep (se 1 (by rfl) ⟨1646081, by rfl⟩ : syracuseStep 2194775 = 3292163) B3292163
theorem B3651567095 : Blo 432776 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B433663 : Blo 432776 433663 := bstep (se 1 (by rfl) ⟨325247, by rfl⟩ : syracuseStep 433663 = 650495) B650495
theorem B433695 : Blo 432776 433695 := bstep (se 1 (by rfl) ⟨325271, by rfl⟩ : syracuseStep 433695 = 650543) B650543
theorem B1171007 : Blo 432776 1171007 := bstep (se 1 (by rfl) ⟨878255, by rfl⟩ : syracuseStep 1171007 = 1756511) B1756511
theorem B434023 : Blo 432776 434023 := bstep (se 1 (by rfl) ⟨325517, by rfl⟩ : syracuseStep 434023 = 651035) B651035
theorem B4464557 : Blo 432776 4464557 := bstep (se 3 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 4464557 = 1674209) B1674209
theorem B1114087 : Blo 432776 1114087 := bstep (se 1 (by rfl) ⟨835565, by rfl⟩ : syracuseStep 1114087 = 1671131) B1671131
theorem B434343 : Blo 432776 434343 := bstep (se 1 (by rfl) ⟨325757, by rfl⟩ : syracuseStep 434343 = 651515) B651515
theorem B3522847 : Blo 432776 3522847 := bstep (se 1 (by rfl) ⟨2642135, by rfl⟩ : syracuseStep 3522847 = 5284271) B5284271
theorem B20349587 : Blo 432776 20349587 := bstep (se 1 (by rfl) ⟨15262190, by rfl⟩ : syracuseStep 20349587 = 30524381) B30524381
theorem B434847 : Blo 432776 434847 := bstep (se 1 (by rfl) ⟨326135, by rfl⟩ : syracuseStep 434847 = 652271) B652271
theorem B975599 : Blo 432776 975599 := bstep (se 1 (by rfl) ⟨731699, by rfl⟩ : syracuseStep 975599 = 1463399) B1463399
theorem B434943 : Blo 432776 434943 := bstep (se 1 (by rfl) ⟨326207, by rfl⟩ : syracuseStep 434943 = 652415) B652415
theorem B4957199 : Blo 432776 4957199 := bstep (se 1 (by rfl) ⟨3717899, by rfl⟩ : syracuseStep 4957199 = 7435799) B7435799
theorem B549919 : Blo 432776 549919 := bstep (se 1 (by rfl) ⟨412439, by rfl⟩ : syracuseStep 549919 = 824879) B824879
theorem B1909889 : Blo 432776 1909889 := bstep (se 2 (by rfl) ⟨716208, by rfl⟩ : syracuseStep 1909889 = 1432417) B1432417
theorem B3720329 : Blo 432776 3720329 := bstep (se 2 (by rfl) ⟨1395123, by rfl⟩ : syracuseStep 3720329 = 2790247) B2790247
theorem B28918943 : Blo 432776 28918943 := bstep (se 1 (by rfl) ⟨21689207, by rfl⟩ : syracuseStep 28918943 = 43378415) B43378415
theorem B435583 : Blo 432776 435583 := bstep (se 1 (by rfl) ⟨326687, by rfl⟩ : syracuseStep 435583 = 653375) B653375
theorem B976319 : Blo 432776 976319 := bstep (se 1 (by rfl) ⟨732239, by rfl⟩ : syracuseStep 976319 = 1464479) B1464479
theorem B16885583 : Blo 432776 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B4441979 : Blo 432776 4441979 := bstep (se 1 (by rfl) ⟨3331484, by rfl⟩ : syracuseStep 4441979 = 6662969) B6662969
theorem B649319 : Blo 432776 649319 := bstep (se 1 (by rfl) ⟨486989, by rfl⟩ : syracuseStep 649319 = 973979) B973979
theorem B15075487 : Blo 432776 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B2434378063 : Blo 432776 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B780671 : Blo 432776 780671 := bstep (se 1 (by rfl) ⟨585503, by rfl⟩ : syracuseStep 780671 = 1171007) B1171007
theorem B1100263 : Blo 432776 1100263 := bstep (se 1 (by rfl) ⟨825197, by rfl⟩ : syracuseStep 1100263 = 1650395) B1650395
theorem B2976371 : Blo 432776 2976371 := bstep (se 1 (by rfl) ⟨2232278, by rfl⟩ : syracuseStep 2976371 = 4464557) B4464557
theorem B1485449 : Blo 432776 1485449 := bstep (se 2 (by rfl) ⟨557043, by rfl⟩ : syracuseStep 1485449 = 1114087) B1114087
theorem B977615 : Blo 432776 977615 := bstep (se 1 (by rfl) ⟨733211, by rfl⟩ : syracuseStep 977615 = 1466423) B1466423
theorem B3123947 : Blo 432776 3123947 := bstep (se 1 (by rfl) ⟨2342960, by rfl⟩ : syracuseStep 3123947 = 4685921) B4685921
theorem B732071 : Blo 432776 732071 := bstep (se 1 (by rfl) ⟨549053, by rfl⟩ : syracuseStep 732071 = 1098107) B1098107
theorem B1461455 : Blo 432776 1461455 := bstep (se 1 (by rfl) ⟨1096091, by rfl⟩ : syracuseStep 1461455 = 2192183) B2192183
theorem B822889 : Blo 432776 822889 := bstep (se 2 (by rfl) ⟨308583, by rfl⟩ : syracuseStep 822889 = 617167) B617167
theorem B2789245 : Blo 432776 2789245 := bstep (se 3 (by rfl) ⟨522983, by rfl⟩ : syracuseStep 2789245 = 1045967) B1045967
theorem B733367 : Blo 432776 733367 := bstep (se 1 (by rfl) ⟨550025, by rfl⟩ : syracuseStep 733367 = 1100051) B1100051
theorem B1110719 : Blo 432776 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B2200283 : Blo 432776 2200283 := bstep (se 1 (by rfl) ⟨1650212, by rfl⟩ : syracuseStep 2200283 = 3300425) B3300425
theorem B1233787 : Blo 432776 1233787 := bstep (se 1 (by rfl) ⟨925340, by rfl⟩ : syracuseStep 1233787 = 1850681) B1850681
theorem B1463183 : Blo 432776 1463183 := bstep (se 1 (by rfl) ⟨1097387, by rfl⟩ : syracuseStep 1463183 = 2194775) B2194775
theorem B652703 : Blo 432776 652703 := bstep (se 1 (by rfl) ⟨489527, by rfl⟩ : syracuseStep 652703 = 979055) B979055
theorem B3716603 : Blo 432776 3716603 := bstep (se 1 (by rfl) ⟨2787452, by rfl⟩ : syracuseStep 3716603 = 5574905) B5574905
theorem B1627913 : Blo 432776 1627913 := bstep (se 2 (by rfl) ⟨610467, by rfl⟩ : syracuseStep 1627913 = 1220935) B1220935
theorem B11908883 : Blo 432776 11908883 := bstep (se 1 (by rfl) ⟨8931662, by rfl⟩ : syracuseStep 11908883 = 17863325) B17863325
theorem B12056377 : Blo 432776 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B4691935 : Blo 432776 4691935 := bstep (se 1 (by rfl) ⟨3518951, by rfl⟩ : syracuseStep 4691935 = 7037903) B7037903
theorem B2201579 : Blo 432776 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B1095707 : Blo 432776 1095707 := bstep (se 1 (by rfl) ⟨821780, by rfl⟩ : syracuseStep 1095707 = 1643561) B1643561
theorem B10681247 : Blo 432776 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B1465343 : Blo 432776 1465343 := bstep (se 1 (by rfl) ⟨1099007, by rfl⟩ : syracuseStep 1465343 = 2198015) B2198015
theorem B2079769 : Blo 432776 2079769 := bstep (se 2 (by rfl) ⟨779913, by rfl⟩ : syracuseStep 2079769 = 1559827) B1559827
theorem B433279 : Blo 432776 433279 := bstep (se 1 (by rfl) ⟨324959, by rfl⟩ : syracuseStep 433279 = 649919) B649919
theorem B2080019 : Blo 432776 2080019 := bstep (se 1 (by rfl) ⟨1560014, by rfl⟩ : syracuseStep 2080019 = 3120029) B3120029
theorem B28261871 : Blo 432776 28261871 := bstep (se 1 (by rfl) ⟨21196403, by rfl⟩ : syracuseStep 28261871 = 42392807) B42392807
theorem B3710519 : Blo 432776 3710519 := bstep (se 1 (by rfl) ⟨2782889, by rfl⟩ : syracuseStep 3710519 = 5565779) B5565779
theorem B1466855 : Blo 432776 1466855 := bstep (se 1 (by rfl) ⟨1100141, by rfl⟩ : syracuseStep 1466855 = 2200283) B2200283
theorem B975455 : Blo 432776 975455 := bstep (se 1 (by rfl) ⟨731591, by rfl⟩ : syracuseStep 975455 = 1463183) B1463183
theorem B1467017 : Blo 432776 1467017 := bstep (se 2 (by rfl) ⟨550131, by rfl⟩ : syracuseStep 1467017 = 1100263) B1100263
theorem B435135 : Blo 432776 435135 := bstep (se 1 (by rfl) ⟨326351, by rfl⟩ : syracuseStep 435135 = 652703) B652703
theorem B7939255 : Blo 432776 7939255 := bstep (se 1 (by rfl) ⟨5954441, by rfl⟩ : syracuseStep 7939255 = 11908883) B11908883
theorem B11257055 : Blo 432776 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B1467719 : Blo 432776 1467719 := bstep (se 1 (by rfl) ⟨1100789, by rfl⟩ : syracuseStep 1467719 = 2201579) B2201579
theorem B730471 : Blo 432776 730471 := bstep (se 1 (by rfl) ⟨547853, by rfl⟩ : syracuseStep 730471 = 1095707) B1095707
theorem B54265565 : Blo 432776 54265565 := bstep (se 3 (by rfl) ⟨10174793, by rfl⟩ : syracuseStep 54265565 = 20349587) B20349587
theorem B1984247 : Blo 432776 1984247 := bstep (se 1 (by rfl) ⟨1488185, by rfl⟩ : syracuseStep 1984247 = 2976371) B2976371
theorem B7120831 : Blo 432776 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B976895 : Blo 432776 976895 := bstep (se 1 (by rfl) ⟨732671, by rfl⟩ : syracuseStep 976895 = 1465343) B1465343
theorem B1386679 : Blo 432776 1386679 := bstep (se 1 (by rfl) ⟨1040009, by rfl⟩ : syracuseStep 1386679 = 2080019) B2080019
theorem B16075169 : Blo 432776 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B4697129 : Blo 432776 4697129 := bstep (se 2 (by rfl) ⟨1761423, by rfl⟩ : syracuseStep 4697129 = 3522847) B3522847
theorem B3245837417 : Blo 432776 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B650399 : Blo 432776 650399 := bstep (se 1 (by rfl) ⟨487799, by rfl⟩ : syracuseStep 650399 = 975599) B975599
theorem B3304799 : Blo 432776 3304799 := bstep (se 1 (by rfl) ⟨2478599, by rfl⟩ : syracuseStep 3304799 = 4957199) B4957199
theorem B1273259 : Blo 432776 1273259 := bstep (se 1 (by rfl) ⟨954944, by rfl⟩ : syracuseStep 1273259 = 1909889) B1909889
theorem B19279295 : Blo 432776 19279295 := bstep (se 1 (by rfl) ⟨14459471, by rfl⟩ : syracuseStep 19279295 = 28918943) B28918943
theorem B650879 : Blo 432776 650879 := bstep (se 1 (by rfl) ⟨488159, by rfl⟩ : syracuseStep 650879 = 976319) B976319
theorem B2477735 : Blo 432776 2477735 := bstep (se 1 (by rfl) ⟨1858301, by rfl⟩ : syracuseStep 2477735 = 3716603) B3716603
theorem B1085275 : Blo 432776 1085275 := bstep (se 1 (by rfl) ⟨813956, by rfl⟩ : syracuseStep 1085275 = 1627913) B1627913
theorem B2961319 : Blo 432776 2961319 := bstep (se 1 (by rfl) ⟨2220989, by rfl⟩ : syracuseStep 2961319 = 4441979) B4441979
theorem B2773025 : Blo 432776 2773025 := bstep (se 2 (by rfl) ⟨1039884, by rfl⟩ : syracuseStep 2773025 = 2079769) B2079769
theorem B733225 : Blo 432776 733225 := bstep (se 2 (by rfl) ⟨274959, by rfl⟩ : syracuseStep 733225 = 549919) B549919
theorem B520447 : Blo 432776 520447 := bstep (se 1 (by rfl) ⟨390335, by rfl⟩ : syracuseStep 520447 = 780671) B780671
theorem B651743 : Blo 432776 651743 := bstep (se 1 (by rfl) ⟨488807, by rfl⟩ : syracuseStep 651743 = 977615) B977615
theorem B2961917 : Blo 432776 2961917 := bstep (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) B1110719
theorem B488047 : Blo 432776 488047 := bstep (se 1 (by rfl) ⟨366035, by rfl⟩ : syracuseStep 488047 = 732071) B732071
theorem B6255913 : Blo 432776 6255913 := bstep (se 2 (by rfl) ⟨2345967, by rfl⟩ : syracuseStep 6255913 = 4691935) B4691935
theorem B488911 : Blo 432776 488911 := bstep (se 1 (by rfl) ⟨366683, by rfl⟩ : syracuseStep 488911 = 733367) B733367
theorem B20100649 : Blo 432776 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B2480219 : Blo 432776 2480219 := bstep (se 1 (by rfl) ⟨1860164, by rfl⟩ : syracuseStep 2480219 = 3720329) B3720329
theorem B1645049 : Blo 432776 1645049 := bstep (se 2 (by rfl) ⟨616893, by rfl⟩ : syracuseStep 1645049 = 1233787) B1233787
theorem B432879 : Blo 432776 432879 := bstep (se 1 (by rfl) ⟨324659, by rfl⟩ : syracuseStep 432879 = 649319) B649319
theorem B990299 : Blo 432776 990299 := bstep (se 1 (by rfl) ⟨742724, by rfl⟩ : syracuseStep 990299 = 1485449) B1485449
theorem B8330525 : Blo 432776 8330525 := bstep (se 3 (by rfl) ⟨1561973, by rfl⟩ : syracuseStep 8330525 = 3123947) B3123947
theorem B974303 : Blo 432776 974303 := bstep (se 1 (by rfl) ⟨730727, by rfl⟩ : syracuseStep 974303 = 1461455) B1461455
theorem B1097185 : Blo 432776 1097185 := bstep (se 2 (by rfl) ⟨411444, by rfl⟩ : syracuseStep 1097185 = 822889) B822889
theorem B18841247 : Blo 432776 18841247 := bstep (se 1 (by rfl) ⟨14130935, by rfl⟩ : syracuseStep 18841247 = 28261871) B28261871
theorem B2473679 : Blo 432776 2473679 := bstep (se 1 (by rfl) ⟨1855259, by rfl⟩ : syracuseStep 2473679 = 3710519) B3710519
theorem B3718993 : Blo 432776 3718993 := bstep (se 2 (by rfl) ⟨1394622, by rfl⟩ : syracuseStep 3718993 = 2789245) B2789245
theorem B434495 : Blo 432776 434495 := bstep (se 1 (by rfl) ⟨325871, by rfl⟩ : syracuseStep 434495 = 651743) B651743
theorem B1974611 : Blo 432776 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B7504703 : Blo 432776 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B36177043 : Blo 432776 36177043 := bstep (se 1 (by rfl) ⟨27132782, by rfl⟩ : syracuseStep 36177043 = 54265565) B54265565
theorem B10585673 : Blo 432776 10585673 := bstep (se 2 (by rfl) ⟨3969627, by rfl⟩ : syracuseStep 10585673 = 7939255) B7939255
theorem B10716779 : Blo 432776 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B8341217 : Blo 432776 8341217 := bstep (se 2 (by rfl) ⟨3127956, by rfl⟩ : syracuseStep 8341217 = 6255913) B6255913
theorem B3131419 : Blo 432776 3131419 := bstep (se 1 (by rfl) ⟨2348564, by rfl⟩ : syracuseStep 3131419 = 4697129) B4697129
theorem B649535 : Blo 432776 649535 := bstep (se 1 (by rfl) ⟨487151, by rfl⟩ : syracuseStep 649535 = 974303) B974303
theorem B12560831 : Blo 432776 12560831 := bstep (se 1 (by rfl) ⟨9420623, by rfl⟩ : syracuseStep 12560831 = 18841247) B18841247
theorem B4958657 : Blo 432776 4958657 := bstep (se 2 (by rfl) ⟨1859496, by rfl⟩ : syracuseStep 4958657 = 3718993) B3718993
theorem B1649119 : Blo 432776 1649119 := bstep (se 1 (by rfl) ⟨1236839, by rfl⟩ : syracuseStep 1649119 = 2473679) B2473679
theorem B977633 : Blo 432776 977633 := bstep (se 2 (by rfl) ⟨366612, by rfl⟩ : syracuseStep 977633 = 733225) B733225
theorem B977903 : Blo 432776 977903 := bstep (se 1 (by rfl) ⟨733427, by rfl⟩ : syracuseStep 977903 = 1466855) B1466855
theorem B650303 : Blo 432776 650303 := bstep (se 1 (by rfl) ⟨487727, by rfl⟩ : syracuseStep 650303 = 975455) B975455
theorem B978011 : Blo 432776 978011 := bstep (se 1 (by rfl) ⟨733508, by rfl⟩ : syracuseStep 978011 = 1467017) B1467017
theorem B650729 : Blo 432776 650729 := bstep (se 2 (by rfl) ⟨244023, by rfl⟩ : syracuseStep 650729 = 488047) B488047
theorem B978479 : Blo 432776 978479 := bstep (se 1 (by rfl) ⟨733859, by rfl⟩ : syracuseStep 978479 = 1467719) B1467719
theorem B1322831 : Blo 432776 1322831 := bstep (se 1 (by rfl) ⟨992123, by rfl⟩ : syracuseStep 1322831 = 1984247) B1984247
theorem B651263 : Blo 432776 651263 := bstep (se 1 (by rfl) ⟨488447, by rfl⟩ : syracuseStep 651263 = 976895) B976895
theorem B651881 : Blo 432776 651881 := bstep (se 2 (by rfl) ⟨244455, by rfl⟩ : syracuseStep 651881 = 488911) B488911
theorem B1462913 : Blo 432776 1462913 := bstep (se 2 (by rfl) ⟨548592, by rfl⟩ : syracuseStep 1462913 = 1097185) B1097185
theorem B26800865 : Blo 432776 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B660199 : Blo 432776 660199 := bstep (se 1 (by rfl) ⟨495149, by rfl⟩ : syracuseStep 660199 = 990299) B990299
theorem B848839 : Blo 432776 848839 := bstep (se 1 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 848839 = 1273259) B1273259
theorem B1651823 : Blo 432776 1651823 := bstep (se 1 (by rfl) ⟨1238867, by rfl⟩ : syracuseStep 1651823 = 2477735) B2477735
theorem B1447033 : Blo 432776 1447033 := bstep (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) B1085275
theorem B1848683 : Blo 432776 1848683 := bstep (se 1 (by rfl) ⟨1386512, by rfl⟩ : syracuseStep 1848683 = 2773025) B2773025
theorem B1848905 : Blo 432776 1848905 := bstep (se 2 (by rfl) ⟨693339, by rfl⟩ : syracuseStep 1848905 = 1386679) B1386679
theorem B693929 : Blo 432776 693929 := bstep (se 2 (by rfl) ⟨260223, by rfl⟩ : syracuseStep 693929 = 520447) B520447
theorem B1653479 : Blo 432776 1653479 := bstep (se 1 (by rfl) ⟨1240109, by rfl⟩ : syracuseStep 1653479 = 2480219) B2480219
theorem B1096699 : Blo 432776 1096699 := bstep (se 1 (by rfl) ⟨822524, by rfl⟩ : syracuseStep 1096699 = 1645049) B1645049
theorem B973961 : Blo 432776 973961 := bstep (se 2 (by rfl) ⟨365235, by rfl⟩ : syracuseStep 973961 = 730471) B730471
theorem B2163891611 : Blo 432776 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B433599 : Blo 432776 433599 := bstep (se 1 (by rfl) ⟨325199, by rfl⟩ : syracuseStep 433599 = 650399) B650399
theorem B5553683 : Blo 432776 5553683 := bstep (se 1 (by rfl) ⟨4165262, by rfl⟩ : syracuseStep 5553683 = 8330525) B8330525
theorem B2203199 : Blo 432776 2203199 := bstep (se 1 (by rfl) ⟨1652399, by rfl⟩ : syracuseStep 2203199 = 3304799) B3304799
theorem B12852863 : Blo 432776 12852863 := bstep (se 1 (by rfl) ⟨9639647, by rfl⟩ : syracuseStep 12852863 = 19279295) B19279295
theorem B433919 : Blo 432776 433919 := bstep (se 1 (by rfl) ⟨325439, by rfl⟩ : syracuseStep 433919 = 650879) B650879
theorem B3948425 : Blo 432776 3948425 := bstep (se 2 (by rfl) ⟨1480659, by rfl⟩ : syracuseStep 3948425 = 2961319) B2961319
theorem B9494441 : Blo 432776 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B434587 : Blo 432776 434587 := bstep (se 1 (by rfl) ⟨325940, by rfl⟩ : syracuseStep 434587 = 651881) B651881
theorem B975275 : Blo 432776 975275 := bstep (se 1 (by rfl) ⟨731456, by rfl⟩ : syracuseStep 975275 = 1462913) B1462913
theorem B17867243 : Blo 432776 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B7144519 : Blo 432776 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B1131785 : Blo 432776 1131785 := bstep (se 2 (by rfl) ⟨424419, by rfl⟩ : syracuseStep 1131785 = 848839) B848839
theorem B48236057 : Blo 432776 48236057 := bstep (se 2 (by rfl) ⟨18088521, by rfl⟩ : syracuseStep 48236057 = 36177043) B36177043
theorem B8373887 : Blo 432776 8373887 := bstep (se 1 (by rfl) ⟨6280415, by rfl⟩ : syracuseStep 8373887 = 12560831) B12560831
theorem B649307 : Blo 432776 649307 := bstep (se 1 (by rfl) ⟨486980, by rfl⟩ : syracuseStep 649307 = 973961) B973961
theorem B1468799 : Blo 432776 1468799 := bstep (se 1 (by rfl) ⟨1101599, by rfl⟩ : syracuseStep 1468799 = 2203199) B2203199
theorem B2632283 : Blo 432776 2632283 := bstep (se 1 (by rfl) ⟨1974212, by rfl⟩ : syracuseStep 2632283 = 3948425) B3948425
theorem B2198825 : Blo 432776 2198825 := bstep (se 2 (by rfl) ⟨824559, by rfl⟩ : syracuseStep 2198825 = 1649119) B1649119
theorem B1101215 : Blo 432776 1101215 := bstep (se 1 (by rfl) ⟨825911, by rfl⟩ : syracuseStep 1101215 = 1651823) B1651823
theorem B1232455 : Blo 432776 1232455 := bstep (se 1 (by rfl) ⟨924341, by rfl⟩ : syracuseStep 1232455 = 1848683) B1848683
theorem B880265 : Blo 432776 880265 := bstep (se 2 (by rfl) ⟨330099, by rfl⟩ : syracuseStep 880265 = 660199) B660199
theorem B1232603 : Blo 432776 1232603 := bstep (se 1 (by rfl) ⟨924452, by rfl⟩ : syracuseStep 1232603 = 1848905) B1848905
theorem B7057115 : Blo 432776 7057115 := bstep (se 1 (by rfl) ⟨5292836, by rfl⟩ : syracuseStep 7057115 = 10585673) B10585673
theorem B462619 : Blo 432776 462619 := bstep (se 1 (by rfl) ⟨346964, by rfl⟩ : syracuseStep 462619 = 693929) B693929
theorem B1462265 : Blo 432776 1462265 := bstep (se 2 (by rfl) ⟨548349, by rfl⟩ : syracuseStep 1462265 = 1096699) B1096699
theorem B1929377 : Blo 432776 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B3305771 : Blo 432776 3305771 := bstep (se 1 (by rfl) ⟨2479328, by rfl⟩ : syracuseStep 3305771 = 4958657) B4958657
theorem B651755 : Blo 432776 651755 := bstep (se 1 (by rfl) ⟨488816, by rfl⟩ : syracuseStep 651755 = 977633) B977633
theorem B1102319 : Blo 432776 1102319 := bstep (se 1 (by rfl) ⟨826739, by rfl⟩ : syracuseStep 1102319 = 1653479) B1653479
theorem B651935 : Blo 432776 651935 := bstep (se 1 (by rfl) ⟨488951, by rfl⟩ : syracuseStep 651935 = 977903) B977903
theorem B652007 : Blo 432776 652007 := bstep (se 1 (by rfl) ⟨489005, by rfl⟩ : syracuseStep 652007 = 978011) B978011
theorem B3527549 : Blo 432776 3527549 := bstep (se 3 (by rfl) ⟨661415, by rfl⟩ : syracuseStep 3527549 = 1322831) B1322831
theorem B652319 : Blo 432776 652319 := bstep (se 1 (by rfl) ⟨489239, by rfl⟩ : syracuseStep 652319 = 978479) B978479
theorem B6329627 : Blo 432776 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B4175225 : Blo 432776 4175225 := bstep (se 2 (by rfl) ⟨1565709, by rfl⟩ : syracuseStep 4175225 = 3131419) B3131419
theorem B1316407 : Blo 432776 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B5003135 : Blo 432776 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B5560811 : Blo 432776 5560811 := bstep (se 1 (by rfl) ⟨4170608, by rfl⟩ : syracuseStep 5560811 = 8341217) B8341217
theorem B433023 : Blo 432776 433023 := bstep (se 1 (by rfl) ⟨324767, by rfl⟩ : syracuseStep 433023 = 649535) B649535
theorem B433535 : Blo 432776 433535 := bstep (se 1 (by rfl) ⟨325151, by rfl⟩ : syracuseStep 433535 = 650303) B650303
theorem B1442594407 : Blo 432776 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B433819 : Blo 432776 433819 := bstep (se 1 (by rfl) ⟨325364, by rfl⟩ : syracuseStep 433819 = 650729) B650729
theorem B3702455 : Blo 432776 3702455 := bstep (se 1 (by rfl) ⟨2776841, by rfl⟩ : syracuseStep 3702455 = 5553683) B5553683
theorem B8568575 : Blo 432776 8568575 := bstep (se 1 (by rfl) ⟨6426431, by rfl⟩ : syracuseStep 8568575 = 12852863) B12852863
theorem B434175 : Blo 432776 434175 := bstep (se 1 (by rfl) ⟨325631, by rfl⟩ : syracuseStep 434175 = 651263) B651263
theorem B2203847 : Blo 432776 2203847 := bstep (se 1 (by rfl) ⟨1652885, by rfl⟩ : syracuseStep 2203847 = 3305771) B3305771
theorem B434503 : Blo 432776 434503 := bstep (se 1 (by rfl) ⟨325877, by rfl⟩ : syracuseStep 434503 = 651755) B651755
theorem B5145005 : Blo 432776 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B434623 : Blo 432776 434623 := bstep (se 1 (by rfl) ⟨325967, by rfl⟩ : syracuseStep 434623 = 651935) B651935
theorem B434671 : Blo 432776 434671 := bstep (se 1 (by rfl) ⟨326003, by rfl⟩ : syracuseStep 434671 = 652007) B652007
theorem B2351699 : Blo 432776 2351699 := bstep (se 1 (by rfl) ⟨1763774, by rfl⟩ : syracuseStep 2351699 = 3527549) B3527549
theorem B434879 : Blo 432776 434879 := bstep (se 1 (by rfl) ⟨326159, by rfl⟩ : syracuseStep 434879 = 652319) B652319
theorem B754523 : Blo 432776 754523 := bstep (se 1 (by rfl) ⟨565892, by rfl⟩ : syracuseStep 754523 = 1131785) B1131785
theorem B4219751 : Blo 432776 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B3335423 : Blo 432776 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B47645981 : Blo 432776 47645981 := bstep (se 3 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 47645981 = 17867243) B17867243
theorem B1754855 : Blo 432776 1754855 := bstep (se 1 (by rfl) ⟨1316141, by rfl⟩ : syracuseStep 1754855 = 2632283) B2632283
theorem B1755209 : Blo 432776 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B1923459209 : Blo 432776 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B616825 : Blo 432776 616825 := bstep (se 2 (by rfl) ⟨231309, by rfl⟩ : syracuseStep 616825 = 462619) B462619
theorem B2468303 : Blo 432776 2468303 := bstep (se 1 (by rfl) ⟨1851227, by rfl⟩ : syracuseStep 2468303 = 3702455) B3702455
theorem B821735 : Blo 432776 821735 := bstep (se 1 (by rfl) ⟨616301, by rfl⟩ : syracuseStep 821735 = 1232603) B1232603
theorem B4704743 : Blo 432776 4704743 := bstep (se 1 (by rfl) ⟨3528557, by rfl⟩ : syracuseStep 4704743 = 7057115) B7057115
theorem B5712383 : Blo 432776 5712383 := bstep (se 1 (by rfl) ⟨4284287, by rfl⟩ : syracuseStep 5712383 = 8568575) B8568575
theorem B650183 : Blo 432776 650183 := bstep (se 1 (by rfl) ⟨487637, by rfl⟩ : syracuseStep 650183 = 975275) B975275
theorem B32157371 : Blo 432776 32157371 := bstep (se 1 (by rfl) ⟨24118028, by rfl⟩ : syracuseStep 32157371 = 48236057) B48236057
theorem B5582591 : Blo 432776 5582591 := bstep (se 1 (by rfl) ⟨4186943, by rfl⟩ : syracuseStep 5582591 = 8373887) B8373887
theorem B979199 : Blo 432776 979199 := bstep (se 1 (by rfl) ⟨734399, by rfl⟩ : syracuseStep 979199 = 1468799) B1468799
theorem B3707207 : Blo 432776 3707207 := bstep (se 1 (by rfl) ⟨2780405, by rfl⟩ : syracuseStep 3707207 = 5560811) B5560811
theorem B2347373 : Blo 432776 2347373 := bstep (se 3 (by rfl) ⟨440132, by rfl⟩ : syracuseStep 2347373 = 880265) B880265
theorem B1643273 : Blo 432776 1643273 := bstep (se 2 (by rfl) ⟨616227, by rfl⟩ : syracuseStep 1643273 = 1232455) B1232455
theorem B734143 : Blo 432776 734143 := bstep (se 1 (by rfl) ⟨550607, by rfl⟩ : syracuseStep 734143 = 1101215) B1101215
theorem B734879 : Blo 432776 734879 := bstep (se 1 (by rfl) ⟨551159, by rfl⟩ : syracuseStep 734879 = 1102319) B1102319
theorem B2783483 : Blo 432776 2783483 := bstep (se 1 (by rfl) ⟨2087612, by rfl⟩ : syracuseStep 2783483 = 4175225) B4175225
theorem B432871 : Blo 432776 432871 := bstep (se 1 (by rfl) ⟨324653, by rfl⟩ : syracuseStep 432871 = 649307) B649307
theorem B9526025 : Blo 432776 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B1465883 : Blo 432776 1465883 := bstep (se 1 (by rfl) ⟨1099412, by rfl⟩ : syracuseStep 1465883 = 2198825) B2198825
theorem B974843 : Blo 432776 974843 := bstep (se 1 (by rfl) ⟨731132, by rfl⟩ : syracuseStep 974843 = 1462265) B1462265
theorem B1564915 : Blo 432776 1564915 := bstep (se 1 (by rfl) ⟨1173686, by rfl⟩ : syracuseStep 1564915 = 2347373) B2347373
theorem B6350683 : Blo 432776 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B977255 : Blo 432776 977255 := bstep (se 1 (by rfl) ⟨732941, by rfl⟩ : syracuseStep 977255 = 1465883) B1465883
theorem B3721727 : Blo 432776 3721727 := bstep (se 1 (by rfl) ⟨2791295, by rfl⟩ : syracuseStep 3721727 = 5582591) B5582591
theorem B649895 : Blo 432776 649895 := bstep (se 1 (by rfl) ⟨487421, by rfl⟩ : syracuseStep 649895 = 974843) B974843
theorem B1469231 : Blo 432776 1469231 := bstep (se 1 (by rfl) ⟨1101923, by rfl⟩ : syracuseStep 1469231 = 2203847) B2203847
theorem B4680557 : Blo 432776 4680557 := bstep (se 3 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 4680557 = 1755209) B1755209
theorem B1567799 : Blo 432776 1567799 := bstep (se 1 (by rfl) ⟨1175849, by rfl⟩ : syracuseStep 1567799 = 2351699) B2351699
theorem B503015 : Blo 432776 503015 := bstep (se 1 (by rfl) ⟨377261, by rfl⟩ : syracuseStep 503015 = 754523) B754523
theorem B31763987 : Blo 432776 31763987 := bstep (se 1 (by rfl) ⟨23822990, by rfl⟩ : syracuseStep 31763987 = 47645981) B47645981
theorem B978857 : Blo 432776 978857 := bstep (se 2 (by rfl) ⟨367071, by rfl⟩ : syracuseStep 978857 = 734143) B734143
theorem B1282306139 : Blo 432776 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B1855655 : Blo 432776 1855655 := bstep (se 1 (by rfl) ⟨1391741, by rfl⟩ : syracuseStep 1855655 = 2783483) B2783483
theorem B3289733 : Blo 432776 3289733 := bstep (se 4 (by rfl) ⟨308412, by rfl⟩ : syracuseStep 3289733 = 616825) B616825
theorem B652799 : Blo 432776 652799 := bstep (se 1 (by rfl) ⟨489599, by rfl⟩ : syracuseStep 652799 = 979199) B979199
theorem B2471471 : Blo 432776 2471471 := bstep (se 1 (by rfl) ⟨1853603, by rfl⟩ : syracuseStep 2471471 = 3707207) B3707207
theorem B1095515 : Blo 432776 1095515 := bstep (se 1 (by rfl) ⟨821636, by rfl⟩ : syracuseStep 1095515 = 1643273) B1643273
theorem B8894461 : Blo 432776 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B489919 : Blo 432776 489919 := bstep (se 1 (by rfl) ⟨367439, by rfl⟩ : syracuseStep 489919 = 734879) B734879
theorem B13720013 : Blo 432776 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B1169903 : Blo 432776 1169903 := bstep (se 1 (by rfl) ⟨877427, by rfl⟩ : syracuseStep 1169903 = 1754855) B1754855
theorem B180042709 : Blo 432776 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B1645535 : Blo 432776 1645535 := bstep (se 1 (by rfl) ⟨1234151, by rfl⟩ : syracuseStep 1645535 = 2468303) B2468303
theorem B547823 : Blo 432776 547823 := bstep (se 1 (by rfl) ⟨410867, by rfl⟩ : syracuseStep 547823 = 821735) B821735
theorem B3136495 : Blo 432776 3136495 := bstep (se 1 (by rfl) ⟨2352371, by rfl⟩ : syracuseStep 3136495 = 4704743) B4704743
theorem B3808255 : Blo 432776 3808255 := bstep (se 1 (by rfl) ⟨2856191, by rfl⟩ : syracuseStep 3808255 = 5712383) B5712383
theorem B85752989 : Blo 432776 85752989 := bstep (se 3 (by rfl) ⟨16078685, by rfl⟩ : syracuseStep 85752989 = 32157371) B32157371
theorem B433455 : Blo 432776 433455 := bstep (se 1 (by rfl) ⟨325091, by rfl⟩ : syracuseStep 433455 = 650183) B650183
theorem B1237103 : Blo 432776 1237103 := bstep (se 1 (by rfl) ⟨927827, by rfl⟩ : syracuseStep 1237103 = 1855655) B1855655
theorem B435199 : Blo 432776 435199 := bstep (se 1 (by rfl) ⟨326399, by rfl⟩ : syracuseStep 435199 = 652799) B652799
theorem B1647647 : Blo 432776 1647647 := bstep (se 1 (by rfl) ⟨1235735, by rfl⟩ : syracuseStep 1647647 = 2471471) B2471471
theorem B730343 : Blo 432776 730343 := bstep (se 1 (by rfl) ⟨547757, by rfl⟩ : syracuseStep 730343 = 1095515) B1095515
theorem B1460861 : Blo 432776 1460861 := bstep (se 3 (by rfl) ⟨273911, by rfl⟩ : syracuseStep 1460861 = 547823) B547823
theorem B854870759 : Blo 432776 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B4181993 : Blo 432776 4181993 := bstep (se 2 (by rfl) ⟨1568247, by rfl⟩ : syracuseStep 4181993 = 3136495) B3136495
theorem B651503 : Blo 432776 651503 := bstep (se 1 (by rfl) ⟨488627, by rfl⟩ : syracuseStep 651503 = 977255) B977255
theorem B9146675 : Blo 432776 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B979487 : Blo 432776 979487 := bstep (se 1 (by rfl) ⟨734615, by rfl⟩ : syracuseStep 979487 = 1469231) B1469231
theorem B1045199 : Blo 432776 1045199 := bstep (se 1 (by rfl) ⟨783899, by rfl⟩ : syracuseStep 1045199 = 1567799) B1567799
theorem B57168659 : Blo 432776 57168659 := bstep (se 1 (by rfl) ⟨42876494, by rfl⟩ : syracuseStep 57168659 = 85752989) B85752989
theorem B8467577 : Blo 432776 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B652571 : Blo 432776 652571 := bstep (se 1 (by rfl) ⟨489428, by rfl⟩ : syracuseStep 652571 = 978857) B978857
theorem B11859281 : Blo 432776 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B2086553 : Blo 432776 2086553 := bstep (se 2 (by rfl) ⟨782457, by rfl⟩ : syracuseStep 2086553 = 1564915) B1564915
theorem B2193155 : Blo 432776 2193155 := bstep (se 1 (by rfl) ⟨1644866, by rfl⟩ : syracuseStep 2193155 = 3289733) B3289733
theorem B653225 : Blo 432776 653225 := bstep (se 2 (by rfl) ⟨244959, by rfl⟩ : syracuseStep 653225 = 489919) B489919
theorem B1341373 : Blo 432776 1341373 := bstep (se 3 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 1341373 = 503015) B503015
theorem B240056945 : Blo 432776 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B3119741 : Blo 432776 3119741 := bstep (se 3 (by rfl) ⟨584951, by rfl⟩ : syracuseStep 3119741 = 1169903) B1169903
theorem B5077673 : Blo 432776 5077673 := bstep (se 2 (by rfl) ⟨1904127, by rfl⟩ : syracuseStep 5077673 = 3808255) B3808255
theorem B2481151 : Blo 432776 2481151 := bstep (se 1 (by rfl) ⟨1860863, by rfl⟩ : syracuseStep 2481151 = 3721727) B3721727
theorem B433263 : Blo 432776 433263 := bstep (se 1 (by rfl) ⟨324947, by rfl⟩ : syracuseStep 433263 = 649895) B649895
theorem B3120371 : Blo 432776 3120371 := bstep (se 1 (by rfl) ⟨2340278, by rfl⟩ : syracuseStep 3120371 = 4680557) B4680557
theorem B1097023 : Blo 432776 1097023 := bstep (se 1 (by rfl) ⟨822767, by rfl⟩ : syracuseStep 1097023 = 1645535) B1645535
theorem B21175991 : Blo 432776 21175991 := bstep (se 1 (by rfl) ⟨15881993, by rfl⟩ : syracuseStep 21175991 = 31763987) B31763987
theorem B434335 : Blo 432776 434335 := bstep (se 1 (by rfl) ⟨325751, by rfl⟩ : syracuseStep 434335 = 651503) B651503
theorem B696799 : Blo 432776 696799 := bstep (se 1 (by rfl) ⟨522599, by rfl⟩ : syracuseStep 696799 = 1045199) B1045199
theorem B1098431 : Blo 432776 1098431 := bstep (se 1 (by rfl) ⟨823823, by rfl⟩ : syracuseStep 1098431 = 1647647) B1647647
theorem B5645051 : Blo 432776 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B435047 : Blo 432776 435047 := bstep (se 1 (by rfl) ⟨326285, by rfl⟩ : syracuseStep 435047 = 652571) B652571
theorem B7906187 : Blo 432776 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B435483 : Blo 432776 435483 := bstep (se 1 (by rfl) ⟨326612, by rfl⟩ : syracuseStep 435483 = 653225) B653225
theorem B3385115 : Blo 432776 3385115 := bstep (se 1 (by rfl) ⟨2538836, by rfl⟩ : syracuseStep 3385115 = 5077673) B5077673
theorem B14117327 : Blo 432776 14117327 := bstep (se 1 (by rfl) ⟨10587995, by rfl⟩ : syracuseStep 14117327 = 21175991) B21175991
theorem B1788497 : Blo 432776 1788497 := bstep (se 2 (by rfl) ⟨670686, by rfl⟩ : syracuseStep 1788497 = 1341373) B1341373
theorem B2787995 : Blo 432776 2787995 := bstep (se 1 (by rfl) ⟨2090996, by rfl⟩ : syracuseStep 2787995 = 4181993) B4181993
theorem B6097783 : Blo 432776 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B38112439 : Blo 432776 38112439 := bstep (se 1 (by rfl) ⟨28584329, by rfl⟩ : syracuseStep 38112439 = 57168659) B57168659
theorem B486895 : Blo 432776 486895 := bstep (se 1 (by rfl) ⟨365171, by rfl⟩ : syracuseStep 486895 = 730343) B730343
theorem B1462103 : Blo 432776 1462103 := bstep (se 1 (by rfl) ⟨1096577, by rfl⟩ : syracuseStep 1462103 = 2193155) B2193155
theorem B1462697 : Blo 432776 1462697 := bstep (se 2 (by rfl) ⟨548511, by rfl⟩ : syracuseStep 1462697 = 1097023) B1097023
theorem B569913839 : Blo 432776 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B824735 : Blo 432776 824735 := bstep (se 1 (by rfl) ⟨618551, by rfl⟩ : syracuseStep 824735 = 1237103) B1237103
theorem B652991 : Blo 432776 652991 := bstep (se 1 (by rfl) ⟨489743, by rfl⟩ : syracuseStep 652991 = 979487) B979487
theorem B1391035 : Blo 432776 1391035 := bstep (se 1 (by rfl) ⟨1043276, by rfl⟩ : syracuseStep 1391035 = 2086553) B2086553
theorem B3308201 : Blo 432776 3308201 := bstep (se 2 (by rfl) ⟨1240575, by rfl⟩ : syracuseStep 3308201 = 2481151) B2481151
theorem B160037963 : Blo 432776 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B2079827 : Blo 432776 2079827 := bstep (se 1 (by rfl) ⟨1559870, by rfl⟩ : syracuseStep 2079827 = 3119741) B3119741
theorem B973907 : Blo 432776 973907 := bstep (se 1 (by rfl) ⟨730430, by rfl⟩ : syracuseStep 973907 = 1460861) B1460861
theorem B2080247 : Blo 432776 2080247 := bstep (se 1 (by rfl) ⟨1560185, by rfl⟩ : syracuseStep 2080247 = 3120371) B3120371
theorem B975131 : Blo 432776 975131 := bstep (se 1 (by rfl) ⟨731348, by rfl⟩ : syracuseStep 975131 = 1462697) B1462697
theorem B549823 : Blo 432776 549823 := bstep (se 1 (by rfl) ⟨412367, by rfl⟩ : syracuseStep 549823 = 824735) B824735
theorem B435327 : Blo 432776 435327 := bstep (se 1 (by rfl) ⟨326495, by rfl⟩ : syracuseStep 435327 = 652991) B652991
theorem B5547325 : Blo 432776 5547325 := bstep (se 3 (by rfl) ⟨1040123, by rfl⟩ : syracuseStep 5547325 = 2080247) B2080247
theorem B50816585 : Blo 432776 50816585 := bstep (se 2 (by rfl) ⟨19056219, by rfl⟩ : syracuseStep 50816585 = 38112439) B38112439
theorem B2205467 : Blo 432776 2205467 := bstep (se 1 (by rfl) ⟨1654100, by rfl⟩ : syracuseStep 2205467 = 3308201) B3308201
theorem B649193 : Blo 432776 649193 := bstep (se 2 (by rfl) ⟨243447, by rfl⟩ : syracuseStep 649193 = 486895) B486895
theorem B1386551 : Blo 432776 1386551 := bstep (se 1 (by rfl) ⟨1039913, by rfl⟩ : syracuseStep 1386551 = 2079827) B2079827
theorem B649271 : Blo 432776 649271 := bstep (se 1 (by rfl) ⟨486953, by rfl⟩ : syracuseStep 649271 = 973907) B973907
theorem B9411551 : Blo 432776 9411551 := bstep (se 1 (by rfl) ⟨7058663, by rfl⟩ : syracuseStep 9411551 = 14117327) B14117327
theorem B732287 : Blo 432776 732287 := bstep (se 1 (by rfl) ⟨549215, by rfl⟩ : syracuseStep 732287 = 1098431) B1098431
theorem B3763367 : Blo 432776 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B1854713 : Blo 432776 1854713 := bstep (se 2 (by rfl) ⟨695517, by rfl⟩ : syracuseStep 1854713 = 1391035) B1391035
theorem B5270791 : Blo 432776 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B929065 : Blo 432776 929065 := bstep (se 2 (by rfl) ⟨348399, by rfl⟩ : syracuseStep 929065 = 696799) B696799
theorem B8130377 : Blo 432776 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B2256743 : Blo 432776 2256743 := bstep (se 1 (by rfl) ⟨1692557, by rfl⟩ : syracuseStep 2256743 = 3385115) B3385115
theorem B1192331 : Blo 432776 1192331 := bstep (se 1 (by rfl) ⟨894248, by rfl⟩ : syracuseStep 1192331 = 1788497) B1788497
theorem B379942559 : Blo 432776 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B1858663 : Blo 432776 1858663 := bstep (se 1 (by rfl) ⟨1393997, by rfl⟩ : syracuseStep 1858663 = 2787995) B2787995
theorem B106691975 : Blo 432776 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B974735 : Blo 432776 974735 := bstep (se 1 (by rfl) ⟨731051, by rfl⟩ : syracuseStep 974735 = 1462103) B1462103
theorem B794887 : Blo 432776 794887 := bstep (se 1 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 794887 = 1192331) B1192331
theorem B1238753 : Blo 432776 1238753 := bstep (se 2 (by rfl) ⟨464532, by rfl⟩ : syracuseStep 1238753 = 929065) B929065
theorem B2508911 : Blo 432776 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B649823 : Blo 432776 649823 := bstep (se 1 (by rfl) ⟨487367, by rfl⟩ : syracuseStep 649823 = 974735) B974735
theorem B650087 : Blo 432776 650087 := bstep (se 1 (by rfl) ⟨487565, by rfl⟩ : syracuseStep 650087 = 975131) B975131
theorem B1470311 : Blo 432776 1470311 := bstep (se 1 (by rfl) ⟨1102733, by rfl⟩ : syracuseStep 1470311 = 2205467) B2205467
theorem B733097 : Blo 432776 733097 := bstep (se 2 (by rfl) ⟨274911, by rfl⟩ : syracuseStep 733097 = 549823) B549823
theorem B2478217 : Blo 432776 2478217 := bstep (se 2 (by rfl) ⟨929331, by rfl⟩ : syracuseStep 2478217 = 1858663) B1858663
theorem B488191 : Blo 432776 488191 := bstep (se 1 (by rfl) ⟨366143, by rfl⟩ : syracuseStep 488191 = 732287) B732287
theorem B71127983 : Blo 432776 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B5420251 : Blo 432776 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B1504495 : Blo 432776 1504495 := bstep (se 1 (by rfl) ⟨1128371, by rfl⟩ : syracuseStep 1504495 = 2256743) B2256743
theorem B253295039 : Blo 432776 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B432795 : Blo 432776 432795 := bstep (se 1 (by rfl) ⟨324596, by rfl⟩ : syracuseStep 432795 = 649193) B649193
theorem B924367 : Blo 432776 924367 := bstep (se 1 (by rfl) ⟨693275, by rfl⟩ : syracuseStep 924367 = 1386551) B1386551
theorem B432847 : Blo 432776 432847 := bstep (se 1 (by rfl) ⟨324635, by rfl⟩ : syracuseStep 432847 = 649271) B649271
theorem B135510893 : Blo 432776 135510893 := bstep (se 3 (by rfl) ⟨25408292, by rfl⟩ : syracuseStep 135510893 = 50816585) B50816585
theorem B7027721 : Blo 432776 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B7396433 : Blo 432776 7396433 := bstep (se 2 (by rfl) ⟨2773662, by rfl⟩ : syracuseStep 7396433 = 5547325) B5547325
theorem B6274367 : Blo 432776 6274367 := bstep (se 1 (by rfl) ⟨4705775, by rfl⟩ : syracuseStep 6274367 = 9411551) B9411551
theorem B1236475 : Blo 432776 1236475 := bstep (se 1 (by rfl) ⟨927356, by rfl⟩ : syracuseStep 1236475 = 1854713) B1854713
theorem B1672607 : Blo 432776 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B7227001 : Blo 432776 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B168863359 : Blo 432776 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B3303341 : Blo 432776 3303341 := bstep (se 3 (by rfl) ⟨619376, by rfl⟩ : syracuseStep 3303341 = 1238753) B1238753
theorem B1648633 : Blo 432776 1648633 := bstep (se 2 (by rfl) ⟨618237, by rfl⟩ : syracuseStep 1648633 = 1236475) B1236475
theorem B47418655 : Blo 432776 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B1232489 : Blo 432776 1232489 := bstep (se 2 (by rfl) ⟨462183, by rfl⟩ : syracuseStep 1232489 = 924367) B924367
theorem B650921 : Blo 432776 650921 := bstep (se 2 (by rfl) ⟨244095, by rfl⟩ : syracuseStep 650921 = 488191) B488191
theorem B4239397 : Blo 432776 4239397 := bstep (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) B794887
theorem B4182911 : Blo 432776 4182911 := bstep (se 1 (by rfl) ⟨3137183, by rfl⟩ : syracuseStep 4182911 = 6274367) B6274367
theorem B980207 : Blo 432776 980207 := bstep (se 1 (by rfl) ⟨735155, by rfl⟩ : syracuseStep 980207 = 1470311) B1470311
theorem B488731 : Blo 432776 488731 := bstep (se 1 (by rfl) ⟨366548, by rfl⟩ : syracuseStep 488731 = 733097) B733097
theorem B52868629 : Blo 432776 52868629 := bstep (se 6 (by rfl) ⟨1239108, by rfl⟩ : syracuseStep 52868629 = 2478217) B2478217
theorem B2005993 : Blo 432776 2005993 := bstep (se 2 (by rfl) ⟨752247, by rfl⟩ : syracuseStep 2005993 = 1504495) B1504495
theorem B433215 : Blo 432776 433215 := bstep (se 1 (by rfl) ⟨324911, by rfl⟩ : syracuseStep 433215 = 649823) B649823
theorem B433391 : Blo 432776 433391 := bstep (se 1 (by rfl) ⟨325043, by rfl⟩ : syracuseStep 433391 = 650087) B650087
theorem B90340595 : Blo 432776 90340595 := bstep (se 1 (by rfl) ⟨67755446, by rfl⟩ : syracuseStep 90340595 = 135510893) B135510893
theorem B4685147 : Blo 432776 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B4930955 : Blo 432776 4930955 := bstep (se 1 (by rfl) ⟨3698216, by rfl⟩ : syracuseStep 4930955 = 7396433) B7396433
theorem B22610117 : Blo 432776 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B38544005 : Blo 432776 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B225151145 : Blo 432776 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B3123431 : Blo 432776 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B3287303 : Blo 432776 3287303 := bstep (se 1 (by rfl) ⟨2465477, by rfl⟩ : syracuseStep 3287303 = 4930955) B4930955
theorem B821659 : Blo 432776 821659 := bstep (se 1 (by rfl) ⟨616244, by rfl⟩ : syracuseStep 821659 = 1232489) B1232489
theorem B2198177 : Blo 432776 2198177 := bstep (se 2 (by rfl) ⟨824316, by rfl⟩ : syracuseStep 2198177 = 1648633) B1648633
theorem B2788607 : Blo 432776 2788607 := bstep (se 1 (by rfl) ⟨2091455, by rfl⟩ : syracuseStep 2788607 = 4182911) B4182911
theorem B4460285 : Blo 432776 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B2674657 : Blo 432776 2674657 := bstep (se 2 (by rfl) ⟨1002996, by rfl⟩ : syracuseStep 2674657 = 2005993) B2005993
theorem B651641 : Blo 432776 651641 := bstep (se 2 (by rfl) ⟨244365, by rfl⟩ : syracuseStep 651641 = 488731) B488731
theorem B653471 : Blo 432776 653471 := bstep (se 1 (by rfl) ⟨490103, by rfl⟩ : syracuseStep 653471 = 980207) B980207
theorem B2202227 : Blo 432776 2202227 := bstep (se 1 (by rfl) ⟨1651670, by rfl⟩ : syracuseStep 2202227 = 3303341) B3303341
theorem B63224873 : Blo 432776 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B70491505 : Blo 432776 70491505 := bstep (se 2 (by rfl) ⟨26434314, by rfl⟩ : syracuseStep 70491505 = 52868629) B52868629
theorem B60227063 : Blo 432776 60227063 := bstep (se 1 (by rfl) ⟨45170297, by rfl⟩ : syracuseStep 60227063 = 90340595) B90340595
theorem B433947 : Blo 432776 433947 := bstep (se 1 (by rfl) ⟨325460, by rfl⟩ : syracuseStep 433947 = 650921) B650921
theorem B434427 : Blo 432776 434427 := bstep (se 1 (by rfl) ⟨325820, by rfl⟩ : syracuseStep 434427 = 651641) B651641
theorem B60293645 : Blo 432776 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B435647 : Blo 432776 435647 := bstep (se 1 (by rfl) ⟨326735, by rfl⟩ : syracuseStep 435647 = 653471) B653471
theorem B2082287 : Blo 432776 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B1468151 : Blo 432776 1468151 := bstep (se 1 (by rfl) ⟨1101113, by rfl⟩ : syracuseStep 1468151 = 2202227) B2202227
theorem B93988673 : Blo 432776 93988673 := bstep (se 2 (by rfl) ⟨35245752, by rfl⟩ : syracuseStep 93988673 = 70491505) B70491505
theorem B42149915 : Blo 432776 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B40151375 : Blo 432776 40151375 := bstep (se 1 (by rfl) ⟨30113531, by rfl⟩ : syracuseStep 40151375 = 60227063) B60227063
theorem B3566209 : Blo 432776 3566209 := bstep (se 2 (by rfl) ⟨1337328, by rfl⟩ : syracuseStep 3566209 = 2674657) B2674657
theorem B2191535 : Blo 432776 2191535 := bstep (se 1 (by rfl) ⟨1643651, by rfl⟩ : syracuseStep 2191535 = 3287303) B3287303
theorem B2401612213 : Blo 432776 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B25696003 : Blo 432776 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B1095545 : Blo 432776 1095545 := bstep (se 2 (by rfl) ⟨410829, by rfl⟩ : syracuseStep 1095545 = 821659) B821659
theorem B1465451 : Blo 432776 1465451 := bstep (se 1 (by rfl) ⟨1099088, by rfl⟩ : syracuseStep 1465451 = 2198177) B2198177
theorem B1859071 : Blo 432776 1859071 := bstep (se 1 (by rfl) ⟨1394303, by rfl⟩ : syracuseStep 1859071 = 2788607) B2788607
theorem B2973523 : Blo 432776 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B730363 : Blo 432776 730363 := bstep (se 1 (by rfl) ⟨547772, by rfl⟩ : syracuseStep 730363 = 1095545) B1095545
theorem B28099943 : Blo 432776 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B976967 : Blo 432776 976967 := bstep (se 1 (by rfl) ⟨732725, by rfl⟩ : syracuseStep 976967 = 1465451) B1465451
theorem B34261337 : Blo 432776 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B1461023 : Blo 432776 1461023 := bstep (se 1 (by rfl) ⟨1095767, by rfl⟩ : syracuseStep 1461023 = 2191535) B2191535
theorem B3202149617 : Blo 432776 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B4754945 : Blo 432776 4754945 := bstep (se 2 (by rfl) ⟨1783104, by rfl⟩ : syracuseStep 4754945 = 3566209) B3566209
theorem B1388191 : Blo 432776 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B978767 : Blo 432776 978767 := bstep (se 1 (by rfl) ⟨734075, by rfl⟩ : syracuseStep 978767 = 1468151) B1468151
theorem B26767583 : Blo 432776 26767583 := bstep (se 1 (by rfl) ⟨20075687, by rfl⟩ : syracuseStep 26767583 = 40151375) B40151375
theorem B2478761 : Blo 432776 2478761 := bstep (se 2 (by rfl) ⟨929535, by rfl⟩ : syracuseStep 2478761 = 1859071) B1859071
theorem B40195763 : Blo 432776 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B62659115 : Blo 432776 62659115 := bstep (se 1 (by rfl) ⟨46994336, by rfl⟩ : syracuseStep 62659115 = 93988673) B93988673
theorem B3964697 : Blo 432776 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B26797175 : Blo 432776 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B41772743 : Blo 432776 41772743 := bstep (se 1 (by rfl) ⟨31329557, by rfl⟩ : syracuseStep 41772743 = 62659115) B62659115
theorem B17845055 : Blo 432776 17845055 := bstep (se 1 (by rfl) ⟨13383791, by rfl⟩ : syracuseStep 17845055 = 26767583) B26767583
theorem B651311 : Blo 432776 651311 := bstep (se 1 (by rfl) ⟨488483, by rfl⟩ : syracuseStep 651311 = 976967) B976967
theorem B2134766411 : Blo 432776 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B2643131 : Blo 432776 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B652511 : Blo 432776 652511 := bstep (se 1 (by rfl) ⟨489383, by rfl⟩ : syracuseStep 652511 = 978767) B978767
theorem B1652507 : Blo 432776 1652507 := bstep (se 1 (by rfl) ⟨1239380, by rfl⟩ : syracuseStep 1652507 = 2478761) B2478761
theorem B91363565 : Blo 432776 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B18733295 : Blo 432776 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B973817 : Blo 432776 973817 := bstep (se 2 (by rfl) ⟨365181, by rfl⟩ : syracuseStep 973817 = 730363) B730363
theorem B974015 : Blo 432776 974015 := bstep (se 1 (by rfl) ⟨730511, by rfl⟩ : syracuseStep 974015 = 1461023) B1461023
theorem B1850921 : Blo 432776 1850921 := bstep (se 2 (by rfl) ⟨694095, by rfl⟩ : syracuseStep 1850921 = 1388191) B1388191
theorem B3169963 : Blo 432776 3169963 := bstep (se 1 (by rfl) ⟨2377472, by rfl⟩ : syracuseStep 3169963 = 4754945) B4754945
theorem B434207 : Blo 432776 434207 := bstep (se 1 (by rfl) ⟨325655, by rfl⟩ : syracuseStep 434207 = 651311) B651311
theorem B1762087 : Blo 432776 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B435007 : Blo 432776 435007 := bstep (se 1 (by rfl) ⟨326255, by rfl⟩ : syracuseStep 435007 = 652511) B652511
theorem B60909043 : Blo 432776 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B11896703 : Blo 432776 11896703 := bstep (se 1 (by rfl) ⟨8922527, by rfl⟩ : syracuseStep 11896703 = 17845055) B17845055
theorem B649211 : Blo 432776 649211 := bstep (se 1 (by rfl) ⟨486908, by rfl⟩ : syracuseStep 649211 = 973817) B973817
theorem B649343 : Blo 432776 649343 := bstep (se 1 (by rfl) ⟨487007, by rfl⟩ : syracuseStep 649343 = 974015) B974015
theorem B27848495 : Blo 432776 27848495 := bstep (se 1 (by rfl) ⟨20886371, by rfl⟩ : syracuseStep 27848495 = 41772743) B41772743
theorem B1101671 : Blo 432776 1101671 := bstep (se 1 (by rfl) ⟨826253, by rfl⟩ : syracuseStep 1101671 = 1652507) B1652507
theorem B12488863 : Blo 432776 12488863 := bstep (se 1 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 12488863 = 18733295) B18733295
theorem B1233947 : Blo 432776 1233947 := bstep (se 1 (by rfl) ⟨925460, by rfl⟩ : syracuseStep 1233947 = 1850921) B1850921
theorem B1423177607 : Blo 432776 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B17864783 : Blo 432776 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B4226617 : Blo 432776 4226617 := bstep (se 2 (by rfl) ⟨1584981, by rfl⟩ : syracuseStep 4226617 = 3169963) B3169963
theorem B7931135 : Blo 432776 7931135 := bstep (se 1 (by rfl) ⟨5948351, by rfl⟩ : syracuseStep 7931135 = 11896703) B11896703
theorem B74262653 : Blo 432776 74262653 := bstep (se 3 (by rfl) ⟨13924247, by rfl⟩ : syracuseStep 74262653 = 27848495) B27848495
theorem B822631 : Blo 432776 822631 := bstep (se 1 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 822631 = 1233947) B1233947
theorem B948785071 : Blo 432776 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B81212057 : Blo 432776 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B734447 : Blo 432776 734447 := bstep (se 1 (by rfl) ⟨550835, by rfl⟩ : syracuseStep 734447 = 1101671) B1101671
theorem B16651817 : Blo 432776 16651817 := bstep (se 2 (by rfl) ⟨6244431, by rfl⟩ : syracuseStep 16651817 = 12488863) B12488863
theorem B2349449 : Blo 432776 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B432807 : Blo 432776 432807 := bstep (se 1 (by rfl) ⟨324605, by rfl⟩ : syracuseStep 432807 = 649211) B649211
theorem B11909855 : Blo 432776 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B432895 : Blo 432776 432895 := bstep (se 1 (by rfl) ⟨324671, by rfl⟩ : syracuseStep 432895 = 649343) B649343
theorem B5635489 : Blo 432776 5635489 := bstep (se 2 (by rfl) ⟨2113308, by rfl⟩ : syracuseStep 5635489 = 4226617) B4226617
theorem B54141371 : Blo 432776 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B11101211 : Blo 432776 11101211 := bstep (se 1 (by rfl) ⟨8325908, by rfl⟩ : syracuseStep 11101211 = 16651817) B16651817
theorem B1566299 : Blo 432776 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B7939903 : Blo 432776 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B7513985 : Blo 432776 7513985 := bstep (se 2 (by rfl) ⟨2817744, by rfl⟩ : syracuseStep 7513985 = 5635489) B5635489
theorem B49508435 : Blo 432776 49508435 := bstep (se 1 (by rfl) ⟨37131326, by rfl⟩ : syracuseStep 49508435 = 74262653) B74262653
theorem B1265046761 : Blo 432776 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B21149693 : Blo 432776 21149693 := bstep (se 3 (by rfl) ⟨3965567, by rfl⟩ : syracuseStep 21149693 = 7931135) B7931135
theorem B489631 : Blo 432776 489631 := bstep (se 1 (by rfl) ⟨367223, by rfl⟩ : syracuseStep 489631 = 734447) B734447
theorem B1096841 : Blo 432776 1096841 := bstep (se 2 (by rfl) ⟨411315, by rfl⟩ : syracuseStep 1096841 = 822631) B822631
theorem B132022493 : Blo 432776 132022493 := bstep (se 3 (by rfl) ⟨24754217, by rfl⟩ : syracuseStep 132022493 = 49508435) B49508435
theorem B36094247 : Blo 432776 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B14099795 : Blo 432776 14099795 := bstep (se 1 (by rfl) ⟨10574846, by rfl⟩ : syracuseStep 14099795 = 21149693) B21149693
theorem B731227 : Blo 432776 731227 := bstep (se 1 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 731227 = 1096841) B1096841
theorem B10586537 : Blo 432776 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B7400807 : Blo 432776 7400807 := bstep (se 1 (by rfl) ⟨5550605, by rfl⟩ : syracuseStep 7400807 = 11101211) B11101211
theorem B1044199 : Blo 432776 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B652841 : Blo 432776 652841 := bstep (se 2 (by rfl) ⟨244815, by rfl⟩ : syracuseStep 652841 = 489631) B489631
theorem B843364507 : Blo 432776 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B20037293 : Blo 432776 20037293 := bstep (se 3 (by rfl) ⟨3756992, by rfl⟩ : syracuseStep 20037293 = 7513985) B7513985
theorem B974969 : Blo 432776 974969 := bstep (se 2 (by rfl) ⟨365613, by rfl⟩ : syracuseStep 974969 = 731227) B731227
theorem B88014995 : Blo 432776 88014995 := bstep (se 1 (by rfl) ⟨66011246, by rfl⟩ : syracuseStep 88014995 = 132022493) B132022493
theorem B435227 : Blo 432776 435227 := bstep (se 1 (by rfl) ⟨326420, by rfl⟩ : syracuseStep 435227 = 652841) B652841
theorem B4933871 : Blo 432776 4933871 := bstep (se 1 (by rfl) ⟨3700403, by rfl⟩ : syracuseStep 4933871 = 7400807) B7400807
theorem B24062831 : Blo 432776 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B1124486009 : Blo 432776 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B9399863 : Blo 432776 9399863 := bstep (se 1 (by rfl) ⟨7049897, by rfl⟩ : syracuseStep 9399863 = 14099795) B14099795
theorem B7057691 : Blo 432776 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B13358195 : Blo 432776 13358195 := bstep (se 1 (by rfl) ⟨10018646, by rfl⟩ : syracuseStep 13358195 = 20037293) B20037293
theorem B1392265 : Blo 432776 1392265 := bstep (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) B1044199
theorem B8905463 : Blo 432776 8905463 := bstep (se 1 (by rfl) ⟨6679097, by rfl⟩ : syracuseStep 8905463 = 13358195) B13358195
theorem B16041887 : Blo 432776 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B649979 : Blo 432776 649979 := bstep (se 1 (by rfl) ⟨487484, by rfl⟩ : syracuseStep 649979 = 974969) B974969
theorem B4705127 : Blo 432776 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B3289247 : Blo 432776 3289247 := bstep (se 1 (by rfl) ⟨2466935, by rfl⟩ : syracuseStep 3289247 = 4933871) B4933871
theorem B1856353 : Blo 432776 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B58676663 : Blo 432776 58676663 := bstep (se 1 (by rfl) ⟨44007497, by rfl⟩ : syracuseStep 58676663 = 88014995) B88014995
theorem B749657339 : Blo 432776 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B6266575 : Blo 432776 6266575 := bstep (se 1 (by rfl) ⟨4699931, by rfl⟩ : syracuseStep 6266575 = 9399863) B9399863
theorem B39117775 : Blo 432776 39117775 := bstep (se 1 (by rfl) ⟨29338331, by rfl⟩ : syracuseStep 39117775 = 58676663) B58676663
theorem B2475137 : Blo 432776 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B499771559 : Blo 432776 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B10694591 : Blo 432776 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B2192831 : Blo 432776 2192831 := bstep (se 1 (by rfl) ⟨1644623, by rfl⟩ : syracuseStep 2192831 = 3289247) B3289247
theorem B5936975 : Blo 432776 5936975 := bstep (se 1 (by rfl) ⟨4452731, by rfl⟩ : syracuseStep 5936975 = 8905463) B8905463
theorem B433319 : Blo 432776 433319 := bstep (se 1 (by rfl) ⟨324989, by rfl⟩ : syracuseStep 433319 = 649979) B649979
theorem B3136751 : Blo 432776 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B8355433 : Blo 432776 8355433 := bstep (se 2 (by rfl) ⟨3133287, by rfl⟩ : syracuseStep 8355433 = 6266575) B6266575
theorem B3957983 : Blo 432776 3957983 := bstep (se 1 (by rfl) ⟨2968487, by rfl⟩ : syracuseStep 3957983 = 5936975) B5936975
theorem B2091167 : Blo 432776 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B7129727 : Blo 432776 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B1650091 : Blo 432776 1650091 := bstep (se 1 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 1650091 = 2475137) B2475137
theorem B1461887 : Blo 432776 1461887 := bstep (se 1 (by rfl) ⟨1096415, by rfl⟩ : syracuseStep 1461887 = 2192831) B2192831
theorem B333181039 : Blo 432776 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B52157033 : Blo 432776 52157033 := bstep (se 2 (by rfl) ⟨19558887, by rfl⟩ : syracuseStep 52157033 = 39117775) B39117775
theorem B11140577 : Blo 432776 11140577 := bstep (se 2 (by rfl) ⟨4177716, by rfl⟩ : syracuseStep 11140577 = 8355433) B8355433
theorem B2638655 : Blo 432776 2638655 := bstep (se 1 (by rfl) ⟨1978991, by rfl⟩ : syracuseStep 2638655 = 3957983) B3957983
theorem B1394111 : Blo 432776 1394111 := bstep (se 1 (by rfl) ⟨1045583, by rfl⟩ : syracuseStep 1394111 = 2091167) B2091167
theorem B4753151 : Blo 432776 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B34771355 : Blo 432776 34771355 := bstep (se 1 (by rfl) ⟨26078516, by rfl⟩ : syracuseStep 34771355 = 52157033) B52157033
theorem B2200121 : Blo 432776 2200121 := bstep (se 2 (by rfl) ⟨825045, by rfl⟩ : syracuseStep 2200121 = 1650091) B1650091
theorem B7427051 : Blo 432776 7427051 := bstep (se 1 (by rfl) ⟨5570288, by rfl⟩ : syracuseStep 7427051 = 11140577) B11140577
theorem B444241385 : Blo 432776 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B974591 : Blo 432776 974591 := bstep (se 1 (by rfl) ⟨730943, by rfl⟩ : syracuseStep 974591 = 1461887) B1461887
theorem B1466747 : Blo 432776 1466747 := bstep (se 1 (by rfl) ⟨1100060, by rfl⟩ : syracuseStep 1466747 = 2200121) B2200121
theorem B649727 : Blo 432776 649727 := bstep (se 1 (by rfl) ⟨487295, by rfl⟩ : syracuseStep 649727 = 974591) B974591
theorem B4951367 : Blo 432776 4951367 := bstep (se 1 (by rfl) ⟨3713525, by rfl⟩ : syracuseStep 4951367 = 7427051) B7427051
theorem B929407 : Blo 432776 929407 := bstep (se 1 (by rfl) ⟨697055, by rfl⟩ : syracuseStep 929407 = 1394111) B1394111
theorem B296160923 : Blo 432776 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B23180903 : Blo 432776 23180903 := bstep (se 1 (by rfl) ⟨17385677, by rfl⟩ : syracuseStep 23180903 = 34771355) B34771355
theorem B1759103 : Blo 432776 1759103 := bstep (se 1 (by rfl) ⟨1319327, by rfl⟩ : syracuseStep 1759103 = 2638655) B2638655
theorem B3168767 : Blo 432776 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B1172735 : Blo 432776 1172735 := bstep (se 1 (by rfl) ⟨879551, by rfl⟩ : syracuseStep 1172735 = 1759103) B1759103
theorem B1239209 : Blo 432776 1239209 := bstep (se 2 (by rfl) ⟨464703, by rfl⟩ : syracuseStep 1239209 = 929407) B929407
theorem B977831 : Blo 432776 977831 := bstep (se 1 (by rfl) ⟨733373, by rfl⟩ : syracuseStep 977831 = 1466747) B1466747
theorem B15453935 : Blo 432776 15453935 := bstep (se 1 (by rfl) ⟨11590451, by rfl⟩ : syracuseStep 15453935 = 23180903) B23180903
theorem B8450045 : Blo 432776 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B197440615 : Blo 432776 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B433151 : Blo 432776 433151 := bstep (se 1 (by rfl) ⟨324863, by rfl⟩ : syracuseStep 433151 = 649727) B649727
theorem B3300911 : Blo 432776 3300911 := bstep (se 1 (by rfl) ⟨2475683, by rfl⟩ : syracuseStep 3300911 = 4951367) B4951367
theorem B781823 : Blo 432776 781823 := bstep (se 1 (by rfl) ⟨586367, by rfl⟩ : syracuseStep 781823 = 1172735) B1172735
theorem B263254153 : Blo 432776 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B651887 : Blo 432776 651887 := bstep (se 1 (by rfl) ⟨488915, by rfl⟩ : syracuseStep 651887 = 977831) B977831
theorem B2200607 : Blo 432776 2200607 := bstep (se 1 (by rfl) ⟨1650455, by rfl⟩ : syracuseStep 2200607 = 3300911) B3300911
theorem B10302623 : Blo 432776 10302623 := bstep (se 1 (by rfl) ⟨7726967, by rfl⟩ : syracuseStep 10302623 = 15453935) B15453935
theorem B5633363 : Blo 432776 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B826139 : Blo 432776 826139 := bstep (se 1 (by rfl) ⟨619604, by rfl⟩ : syracuseStep 826139 = 1239209) B1239209
theorem B434591 : Blo 432776 434591 := bstep (se 1 (by rfl) ⟨325943, by rfl⟩ : syracuseStep 434591 = 651887) B651887
theorem B1467071 : Blo 432776 1467071 := bstep (se 1 (by rfl) ⟨1100303, by rfl⟩ : syracuseStep 1467071 = 2200607) B2200607
theorem B351005537 : Blo 432776 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B6868415 : Blo 432776 6868415 := bstep (se 1 (by rfl) ⟨5151311, by rfl⟩ : syracuseStep 6868415 = 10302623) B10302623
theorem B3755575 : Blo 432776 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B2084861 : Blo 432776 2084861 := bstep (se 3 (by rfl) ⟨390911, by rfl⟩ : syracuseStep 2084861 = 781823) B781823
theorem B2203037 : Blo 432776 2203037 := bstep (se 3 (by rfl) ⟨413069, by rfl⟩ : syracuseStep 2203037 = 826139) B826139
theorem B5007433 : Blo 432776 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B1468691 : Blo 432776 1468691 := bstep (se 1 (by rfl) ⟨1101518, by rfl⟩ : syracuseStep 1468691 = 2203037) B2203037
theorem B978047 : Blo 432776 978047 := bstep (se 1 (by rfl) ⟨733535, by rfl⟩ : syracuseStep 978047 = 1467071) B1467071
theorem B1389907 : Blo 432776 1389907 := bstep (se 1 (by rfl) ⟨1042430, by rfl⟩ : syracuseStep 1389907 = 2084861) B2084861
theorem B18315773 : Blo 432776 18315773 := bstep (se 3 (by rfl) ⟨3434207, by rfl⟩ : syracuseStep 18315773 = 6868415) B6868415
theorem B234003691 : Blo 432776 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B6676577 : Blo 432776 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B1853209 : Blo 432776 1853209 := bstep (se 2 (by rfl) ⟨694953, by rfl⟩ : syracuseStep 1853209 = 1389907) B1389907
theorem B979127 : Blo 432776 979127 := bstep (se 1 (by rfl) ⟨734345, by rfl⟩ : syracuseStep 979127 = 1468691) B1468691
theorem B312004921 : Blo 432776 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B12210515 : Blo 432776 12210515 := bstep (se 1 (by rfl) ⟨9157886, by rfl⟩ : syracuseStep 12210515 = 18315773) B18315773
theorem B652031 : Blo 432776 652031 := bstep (se 1 (by rfl) ⟨489023, by rfl⟩ : syracuseStep 652031 = 978047) B978047
theorem B416006561 : Blo 432776 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B434687 : Blo 432776 434687 := bstep (se 1 (by rfl) ⟨326015, by rfl⟩ : syracuseStep 434687 = 652031) B652031
theorem B4451051 : Blo 432776 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B2470945 : Blo 432776 2470945 := bstep (se 2 (by rfl) ⟨926604, by rfl⟩ : syracuseStep 2470945 = 1853209) B1853209
theorem B652751 : Blo 432776 652751 := bstep (se 1 (by rfl) ⟨489563, by rfl⟩ : syracuseStep 652751 = 979127) B979127
theorem B8140343 : Blo 432776 8140343 := bstep (se 1 (by rfl) ⟨6105257, by rfl⟩ : syracuseStep 8140343 = 12210515) B12210515
theorem B435167 : Blo 432776 435167 := bstep (se 1 (by rfl) ⟨326375, by rfl⟩ : syracuseStep 435167 = 652751) B652751
theorem B3294593 : Blo 432776 3294593 := bstep (se 2 (by rfl) ⟨1235472, by rfl⟩ : syracuseStep 3294593 = 2470945) B2470945
theorem B2967367 : Blo 432776 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B86830325 : Blo 432776 86830325 := bstep (se 5 (by rfl) ⟨4070171, by rfl⟩ : syracuseStep 86830325 = 8140343) B8140343
theorem B1109350829 : Blo 432776 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B2196395 : Blo 432776 2196395 := bstep (se 1 (by rfl) ⟨1647296, by rfl⟩ : syracuseStep 2196395 = 3294593) B3294593
theorem B739567219 : Blo 432776 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B57886883 : Blo 432776 57886883 := bstep (se 1 (by rfl) ⟨43415162, by rfl⟩ : syracuseStep 57886883 = 86830325) B86830325
theorem B3956489 : Blo 432776 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B986089625 : Blo 432776 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B1464263 : Blo 432776 1464263 := bstep (se 1 (by rfl) ⟨1098197, by rfl⟩ : syracuseStep 1464263 = 2196395) B2196395
theorem B38591255 : Blo 432776 38591255 := bstep (se 1 (by rfl) ⟨28943441, by rfl⟩ : syracuseStep 38591255 = 57886883) B57886883
theorem B2637659 : Blo 432776 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B976175 : Blo 432776 976175 := bstep (se 1 (by rfl) ⟨732131, by rfl⟩ : syracuseStep 976175 = 1464263) B1464263
theorem B657393083 : Blo 432776 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B25727503 : Blo 432776 25727503 := bstep (se 1 (by rfl) ⟨19295627, by rfl⟩ : syracuseStep 25727503 = 38591255) B38591255
theorem B1758439 : Blo 432776 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B2344585 : Blo 432776 2344585 := bstep (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) B1758439
theorem B34303337 : Blo 432776 34303337 := bstep (se 2 (by rfl) ⟨12863751, by rfl⟩ : syracuseStep 34303337 = 25727503) B25727503
theorem B650783 : Blo 432776 650783 := bstep (se 1 (by rfl) ⟨488087, by rfl⟩ : syracuseStep 650783 = 976175) B976175
theorem B438262055 : Blo 432776 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B3126113 : Blo 432776 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B22868891 : Blo 432776 22868891 := bstep (se 1 (by rfl) ⟨17151668, by rfl⟩ : syracuseStep 22868891 = 34303337) B34303337
theorem B292174703 : Blo 432776 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B433855 : Blo 432776 433855 := bstep (se 1 (by rfl) ⟨325391, by rfl⟩ : syracuseStep 433855 = 650783) B650783
theorem B15245927 : Blo 432776 15245927 := bstep (se 1 (by rfl) ⟨11434445, by rfl⟩ : syracuseStep 15245927 = 22868891) B22868891
theorem B194783135 : Blo 432776 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B2084075 : Blo 432776 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B1389383 : Blo 432776 1389383 := bstep (se 1 (by rfl) ⟨1042037, by rfl⟩ : syracuseStep 1389383 = 2084075) B2084075
theorem B10163951 : Blo 432776 10163951 := bstep (se 1 (by rfl) ⟨7622963, by rfl⟩ : syracuseStep 10163951 = 15245927) B15245927
theorem B519421693 : Blo 432776 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B926255 : Blo 432776 926255 := bstep (se 1 (by rfl) ⟨694691, by rfl⟩ : syracuseStep 926255 = 1389383) B1389383
theorem B6775967 : Blo 432776 6775967 := bstep (se 1 (by rfl) ⟨5081975, by rfl⟩ : syracuseStep 6775967 = 10163951) B10163951
theorem B692562257 : Blo 432776 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B2470013 : Blo 432776 2470013 := bstep (se 3 (by rfl) ⟨463127, by rfl⟩ : syracuseStep 2470013 = 926255) B926255
theorem B18069245 : Blo 432776 18069245 := bstep (se 3 (by rfl) ⟨3387983, by rfl⟩ : syracuseStep 18069245 = 6775967) B6775967
theorem B461708171 : Blo 432776 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B1646675 : Blo 432776 1646675 := bstep (se 1 (by rfl) ⟨1235006, by rfl⟩ : syracuseStep 1646675 = 2470013) B2470013
theorem B12046163 : Blo 432776 12046163 := bstep (se 1 (by rfl) ⟨9034622, by rfl⟩ : syracuseStep 12046163 = 18069245) B18069245
theorem B307805447 : Blo 432776 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B1097783 : Blo 432776 1097783 := bstep (se 1 (by rfl) ⟨823337, by rfl⟩ : syracuseStep 1097783 = 1646675) B1646675
theorem B205203631 : Blo 432776 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B32123101 : Blo 432776 32123101 := bstep (se 3 (by rfl) ⟨6023081, by rfl⟩ : syracuseStep 32123101 = 12046163) B12046163
theorem B273604841 : Blo 432776 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B731855 : Blo 432776 731855 := bstep (se 1 (by rfl) ⟨548891, by rfl⟩ : syracuseStep 731855 = 1097783) B1097783
theorem B42830801 : Blo 432776 42830801 := bstep (se 2 (by rfl) ⟨16061550, by rfl⟩ : syracuseStep 42830801 = 32123101) B32123101
theorem B182403227 : Blo 432776 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B487903 : Blo 432776 487903 := bstep (se 1 (by rfl) ⟨365927, by rfl⟩ : syracuseStep 487903 = 731855) B731855
theorem B28553867 : Blo 432776 28553867 := bstep (se 1 (by rfl) ⟨21415400, by rfl⟩ : syracuseStep 28553867 = 42830801) B42830801
theorem B121602151 : Blo 432776 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B650537 : Blo 432776 650537 := bstep (se 2 (by rfl) ⟨243951, by rfl⟩ : syracuseStep 650537 = 487903) B487903
theorem B19035911 : Blo 432776 19035911 := bstep (se 1 (by rfl) ⟨14276933, by rfl⟩ : syracuseStep 19035911 = 28553867) B28553867
theorem B648544805 : Blo 432776 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B12690607 : Blo 432776 12690607 := bstep (se 1 (by rfl) ⟨9517955, by rfl⟩ : syracuseStep 12690607 = 19035911) B19035911
theorem B433691 : Blo 432776 433691 := bstep (se 1 (by rfl) ⟨325268, by rfl⟩ : syracuseStep 433691 = 650537) B650537
theorem B16920809 : Blo 432776 16920809 := bstep (se 2 (by rfl) ⟨6345303, by rfl⟩ : syracuseStep 16920809 = 12690607) B12690607
theorem B432363203 : Blo 432776 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B11280539 : Blo 432776 11280539 := bstep (se 1 (by rfl) ⟨8460404, by rfl⟩ : syracuseStep 11280539 = 16920809) B16920809
theorem B288242135 : Blo 432776 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B7520359 : Blo 432776 7520359 := bstep (se 1 (by rfl) ⟨5640269, by rfl⟩ : syracuseStep 7520359 = 11280539) B11280539
theorem B192161423 : Blo 432776 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B10027145 : Blo 432776 10027145 := bstep (se 2 (by rfl) ⟨3760179, by rfl⟩ : syracuseStep 10027145 = 7520359) B7520359
theorem B128107615 : Blo 432776 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B6684763 : Blo 432776 6684763 := bstep (se 1 (by rfl) ⟨5013572, by rfl⟩ : syracuseStep 6684763 = 10027145) B10027145
theorem B170810153 : Blo 432776 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B8913017 : Blo 432776 8913017 := bstep (se 2 (by rfl) ⟨3342381, by rfl⟩ : syracuseStep 8913017 = 6684763) B6684763
theorem B113873435 : Blo 432776 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B75915623 : Blo 432776 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B5942011 : Blo 432776 5942011 := bstep (se 1 (by rfl) ⟨4456508, by rfl⟩ : syracuseStep 5942011 = 8913017) B8913017
theorem B50610415 : Blo 432776 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B7922681 : Blo 432776 7922681 := bstep (se 2 (by rfl) ⟨2971005, by rfl⟩ : syracuseStep 7922681 = 5942011) B5942011
theorem B67480553 : Blo 432776 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B5281787 : Blo 432776 5281787 := bstep (se 1 (by rfl) ⟨3961340, by rfl⟩ : syracuseStep 5281787 = 7922681) B7922681
theorem B44987035 : Blo 432776 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B3521191 : Blo 432776 3521191 := bstep (se 1 (by rfl) ⟨2640893, by rfl⟩ : syracuseStep 3521191 = 5281787) B5281787
theorem B59982713 : Blo 432776 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B4694921 : Blo 432776 4694921 := bstep (se 2 (by rfl) ⟨1760595, by rfl⟩ : syracuseStep 4694921 = 3521191) B3521191
theorem B3129947 : Blo 432776 3129947 := bstep (se 1 (by rfl) ⟨2347460, by rfl⟩ : syracuseStep 3129947 = 4694921) B4694921
theorem B39988475 : Blo 432776 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B26658983 : Blo 432776 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B2086631 : Blo 432776 2086631 := bstep (se 1 (by rfl) ⟨1564973, by rfl⟩ : syracuseStep 2086631 = 3129947) B3129947
theorem B71090621 : Blo 432776 71090621 := bstep (se 3 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 71090621 = 26658983) B26658983
theorem B1391087 : Blo 432776 1391087 := bstep (se 1 (by rfl) ⟨1043315, by rfl⟩ : syracuseStep 1391087 = 2086631) B2086631
theorem B927391 : Blo 432776 927391 := bstep (se 1 (by rfl) ⟨695543, by rfl⟩ : syracuseStep 927391 = 1391087) B1391087
theorem B47393747 : Blo 432776 47393747 := bstep (se 1 (by rfl) ⟨35545310, by rfl⟩ : syracuseStep 47393747 = 71090621) B71090621
theorem B31595831 : Blo 432776 31595831 := bstep (se 1 (by rfl) ⟨23696873, by rfl⟩ : syracuseStep 31595831 = 47393747) B47393747
theorem B1236521 : Blo 432776 1236521 := bstep (se 2 (by rfl) ⟨463695, by rfl⟩ : syracuseStep 1236521 = 927391) B927391
theorem B21063887 : Blo 432776 21063887 := bstep (se 1 (by rfl) ⟨15797915, by rfl⟩ : syracuseStep 21063887 = 31595831) B31595831
theorem B824347 : Blo 432776 824347 := bstep (se 1 (by rfl) ⟨618260, by rfl⟩ : syracuseStep 824347 = 1236521) B1236521
theorem B1099129 : Blo 432776 1099129 := bstep (se 2 (by rfl) ⟨412173, by rfl⟩ : syracuseStep 1099129 = 824347) B824347
theorem B14042591 : Blo 432776 14042591 := bstep (se 1 (by rfl) ⟨10531943, by rfl⟩ : syracuseStep 14042591 = 21063887) B21063887
theorem B9361727 : Blo 432776 9361727 := bstep (se 1 (by rfl) ⟨7021295, by rfl⟩ : syracuseStep 9361727 = 14042591) B14042591
theorem B1465505 : Blo 432776 1465505 := bstep (se 2 (by rfl) ⟨549564, by rfl⟩ : syracuseStep 1465505 = 1099129) B1099129
theorem B977003 : Blo 432776 977003 := bstep (se 1 (by rfl) ⟨732752, by rfl⟩ : syracuseStep 977003 = 1465505) B1465505
theorem B6241151 : Blo 432776 6241151 := bstep (se 1 (by rfl) ⟨4680863, by rfl⟩ : syracuseStep 6241151 = 9361727) B9361727
theorem B651335 : Blo 432776 651335 := bstep (se 1 (by rfl) ⟨488501, by rfl⟩ : syracuseStep 651335 = 977003) B977003
theorem B4160767 : Blo 432776 4160767 := bstep (se 1 (by rfl) ⟨3120575, by rfl⟩ : syracuseStep 4160767 = 6241151) B6241151
theorem B434223 : Blo 432776 434223 := bstep (se 1 (by rfl) ⟨325667, by rfl⟩ : syracuseStep 434223 = 651335) B651335
theorem B5547689 : Blo 432776 5547689 := bstep (se 2 (by rfl) ⟨2080383, by rfl⟩ : syracuseStep 5547689 = 4160767) B4160767
theorem B3698459 : Blo 432776 3698459 := bstep (se 1 (by rfl) ⟨2773844, by rfl⟩ : syracuseStep 3698459 = 5547689) B5547689
theorem B2465639 : Blo 432776 2465639 := bstep (se 1 (by rfl) ⟨1849229, by rfl⟩ : syracuseStep 2465639 = 3698459) B3698459
theorem B1643759 : Blo 432776 1643759 := bstep (se 1 (by rfl) ⟨1232819, by rfl⟩ : syracuseStep 1643759 = 2465639) B2465639
theorem B1095839 : Blo 432776 1095839 := bstep (se 1 (by rfl) ⟨821879, by rfl⟩ : syracuseStep 1095839 = 1643759) B1643759
theorem B730559 : Blo 432776 730559 := bstep (se 1 (by rfl) ⟨547919, by rfl⟩ : syracuseStep 730559 = 1095839) B1095839
theorem B487039 : Blo 432776 487039 := bstep (se 1 (by rfl) ⟨365279, by rfl⟩ : syracuseStep 487039 = 730559) B730559
theorem B649385 : Blo 432776 649385 := bstep (se 2 (by rfl) ⟨243519, by rfl⟩ : syracuseStep 649385 = 487039) B487039
theorem B432923 : Blo 432776 432923 := bstep (se 1 (by rfl) ⟨324692, by rfl⟩ : syracuseStep 432923 = 649385) B649385

theorem C0 (j : ℕ) (h1 : 108194 ≤ j) (h2 : j ≤ 108893) : Blo 432776 (4 * j + 3) := by
  interval_cases j
  · exact B432779
  · exact B432783
  · exact B432787
  · exact B432791
  · exact B432795
  · exact B432799
  · exact B432803
  · exact B432807
  · exact B432811
  · exact B432815
  · exact B432819
  · exact B432823
  · exact B432827
  · exact B432831
  · exact B432835
  · exact B432839
  · exact B432843
  · exact B432847
  · exact B432851
  · exact B432855
  · exact B432859
  · exact B432863
  · exact B432867
  · exact B432871
  · exact B432875
  · exact B432879
  · exact B432883
  · exact B432887
  · exact B432891
  · exact B432895
  · exact B432899
  · exact B432903
  · exact B432907
  · exact B432911
  · exact B432915
  · exact B432919
  · exact B432923
  · exact B432927
  · exact B432931
  · exact B432935
  · exact B432939
  · exact B432943
  · exact B432947
  · exact B432951
  · exact B432955
  · exact B432959
  · exact B432963
  · exact B432967
  · exact B432971
  · exact B432975
  · exact B432979
  · exact B432983
  · exact B432987
  · exact B432991
  · exact B432995
  · exact B432999
  · exact B433003
  · exact B433007
  · exact B433011
  · exact B433015
  · exact B433019
  · exact B433023
  · exact B433027
  · exact B433031
  · exact B433035
  · exact B433039
  · exact B433043
  · exact B433047
  · exact B433051
  · exact B433055
  · exact B433059
  · exact B433063
  · exact B433067
  · exact B433071
  · exact B433075
  · exact B433079
  · exact B433083
  · exact B433087
  · exact B433091
  · exact B433095
  · exact B433099
  · exact B433103
  · exact B433107
  · exact B433111
  · exact B433115
  · exact B433119
  · exact B433123
  · exact B433127
  · exact B433131
  · exact B433135
  · exact B433139
  · exact B433143
  · exact B433147
  · exact B433151
  · exact B433155
  · exact B433159
  · exact B433163
  · exact B433167
  · exact B433171
  · exact B433175
  · exact B433179
  · exact B433183
  · exact B433187
  · exact B433191
  · exact B433195
  · exact B433199
  · exact B433203
  · exact B433207
  · exact B433211
  · exact B433215
  · exact B433219
  · exact B433223
  · exact B433227
  · exact B433231
  · exact B433235
  · exact B433239
  · exact B433243
  · exact B433247
  · exact B433251
  · exact B433255
  · exact B433259
  · exact B433263
  · exact B433267
  · exact B433271
  · exact B433275
  · exact B433279
  · exact B433283
  · exact B433287
  · exact B433291
  · exact B433295
  · exact B433299
  · exact B433303
  · exact B433307
  · exact B433311
  · exact B433315
  · exact B433319
  · exact B433323
  · exact B433327
  · exact B433331
  · exact B433335
  · exact B433339
  · exact B433343
  · exact B433347
  · exact B433351
  · exact B433355
  · exact B433359
  · exact B433363
  · exact B433367
  · exact B433371
  · exact B433375
  · exact B433379
  · exact B433383
  · exact B433387
  · exact B433391
  · exact B433395
  · exact B433399
  · exact B433403
  · exact B433407
  · exact B433411
  · exact B433415
  · exact B433419
  · exact B433423
  · exact B433427
  · exact B433431
  · exact B433435
  · exact B433439
  · exact B433443
  · exact B433447
  · exact B433451
  · exact B433455
  · exact B433459
  · exact B433463
  · exact B433467
  · exact B433471
  · exact B433475
  · exact B433479
  · exact B433483
  · exact B433487
  · exact B433491
  · exact B433495
  · exact B433499
  · exact B433503
  · exact B433507
  · exact B433511
  · exact B433515
  · exact B433519
  · exact B433523
  · exact B433527
  · exact B433531
  · exact B433535
  · exact B433539
  · exact B433543
  · exact B433547
  · exact B433551
  · exact B433555
  · exact B433559
  · exact B433563
  · exact B433567
  · exact B433571
  · exact B433575
  · exact B433579
  · exact B433583
  · exact B433587
  · exact B433591
  · exact B433595
  · exact B433599
  · exact B433603
  · exact B433607
  · exact B433611
  · exact B433615
  · exact B433619
  · exact B433623
  · exact B433627
  · exact B433631
  · exact B433635
  · exact B433639
  · exact B433643
  · exact B433647
  · exact B433651
  · exact B433655
  · exact B433659
  · exact B433663
  · exact B433667
  · exact B433671
  · exact B433675
  · exact B433679
  · exact B433683
  · exact B433687
  · exact B433691
  · exact B433695
  · exact B433699
  · exact B433703
  · exact B433707
  · exact B433711
  · exact B433715
  · exact B433719
  · exact B433723
  · exact B433727
  · exact B433731
  · exact B433735
  · exact B433739
  · exact B433743
  · exact B433747
  · exact B433751
  · exact B433755
  · exact B433759
  · exact B433763
  · exact B433767
  · exact B433771
  · exact B433775
  · exact B433779
  · exact B433783
  · exact B433787
  · exact B433791
  · exact B433795
  · exact B433799
  · exact B433803
  · exact B433807
  · exact B433811
  · exact B433815
  · exact B433819
  · exact B433823
  · exact B433827
  · exact B433831
  · exact B433835
  · exact B433839
  · exact B433843
  · exact B433847
  · exact B433851
  · exact B433855
  · exact B433859
  · exact B433863
  · exact B433867
  · exact B433871
  · exact B433875
  · exact B433879
  · exact B433883
  · exact B433887
  · exact B433891
  · exact B433895
  · exact B433899
  · exact B433903
  · exact B433907
  · exact B433911
  · exact B433915
  · exact B433919
  · exact B433923
  · exact B433927
  · exact B433931
  · exact B433935
  · exact B433939
  · exact B433943
  · exact B433947
  · exact B433951
  · exact B433955
  · exact B433959
  · exact B433963
  · exact B433967
  · exact B433971
  · exact B433975
  · exact B433979
  · exact B433983
  · exact B433987
  · exact B433991
  · exact B433995
  · exact B433999
  · exact B434003
  · exact B434007
  · exact B434011
  · exact B434015
  · exact B434019
  · exact B434023
  · exact B434027
  · exact B434031
  · exact B434035
  · exact B434039
  · exact B434043
  · exact B434047
  · exact B434051
  · exact B434055
  · exact B434059
  · exact B434063
  · exact B434067
  · exact B434071
  · exact B434075
  · exact B434079
  · exact B434083
  · exact B434087
  · exact B434091
  · exact B434095
  · exact B434099
  · exact B434103
  · exact B434107
  · exact B434111
  · exact B434115
  · exact B434119
  · exact B434123
  · exact B434127
  · exact B434131
  · exact B434135
  · exact B434139
  · exact B434143
  · exact B434147
  · exact B434151
  · exact B434155
  · exact B434159
  · exact B434163
  · exact B434167
  · exact B434171
  · exact B434175
  · exact B434179
  · exact B434183
  · exact B434187
  · exact B434191
  · exact B434195
  · exact B434199
  · exact B434203
  · exact B434207
  · exact B434211
  · exact B434215
  · exact B434219
  · exact B434223
  · exact B434227
  · exact B434231
  · exact B434235
  · exact B434239
  · exact B434243
  · exact B434247
  · exact B434251
  · exact B434255
  · exact B434259
  · exact B434263
  · exact B434267
  · exact B434271
  · exact B434275
  · exact B434279
  · exact B434283
  · exact B434287
  · exact B434291
  · exact B434295
  · exact B434299
  · exact B434303
  · exact B434307
  · exact B434311
  · exact B434315
  · exact B434319
  · exact B434323
  · exact B434327
  · exact B434331
  · exact B434335
  · exact B434339
  · exact B434343
  · exact B434347
  · exact B434351
  · exact B434355
  · exact B434359
  · exact B434363
  · exact B434367
  · exact B434371
  · exact B434375
  · exact B434379
  · exact B434383
  · exact B434387
  · exact B434391
  · exact B434395
  · exact B434399
  · exact B434403
  · exact B434407
  · exact B434411
  · exact B434415
  · exact B434419
  · exact B434423
  · exact B434427
  · exact B434431
  · exact B434435
  · exact B434439
  · exact B434443
  · exact B434447
  · exact B434451
  · exact B434455
  · exact B434459
  · exact B434463
  · exact B434467
  · exact B434471
  · exact B434475
  · exact B434479
  · exact B434483
  · exact B434487
  · exact B434491
  · exact B434495
  · exact B434499
  · exact B434503
  · exact B434507
  · exact B434511
  · exact B434515
  · exact B434519
  · exact B434523
  · exact B434527
  · exact B434531
  · exact B434535
  · exact B434539
  · exact B434543
  · exact B434547
  · exact B434551
  · exact B434555
  · exact B434559
  · exact B434563
  · exact B434567
  · exact B434571
  · exact B434575
  · exact B434579
  · exact B434583
  · exact B434587
  · exact B434591
  · exact B434595
  · exact B434599
  · exact B434603
  · exact B434607
  · exact B434611
  · exact B434615
  · exact B434619
  · exact B434623
  · exact B434627
  · exact B434631
  · exact B434635
  · exact B434639
  · exact B434643
  · exact B434647
  · exact B434651
  · exact B434655
  · exact B434659
  · exact B434663
  · exact B434667
  · exact B434671
  · exact B434675
  · exact B434679
  · exact B434683
  · exact B434687
  · exact B434691
  · exact B434695
  · exact B434699
  · exact B434703
  · exact B434707
  · exact B434711
  · exact B434715
  · exact B434719
  · exact B434723
  · exact B434727
  · exact B434731
  · exact B434735
  · exact B434739
  · exact B434743
  · exact B434747
  · exact B434751
  · exact B434755
  · exact B434759
  · exact B434763
  · exact B434767
  · exact B434771
  · exact B434775
  · exact B434779
  · exact B434783
  · exact B434787
  · exact B434791
  · exact B434795
  · exact B434799
  · exact B434803
  · exact B434807
  · exact B434811
  · exact B434815
  · exact B434819
  · exact B434823
  · exact B434827
  · exact B434831
  · exact B434835
  · exact B434839
  · exact B434843
  · exact B434847
  · exact B434851
  · exact B434855
  · exact B434859
  · exact B434863
  · exact B434867
  · exact B434871
  · exact B434875
  · exact B434879
  · exact B434883
  · exact B434887
  · exact B434891
  · exact B434895
  · exact B434899
  · exact B434903
  · exact B434907
  · exact B434911
  · exact B434915
  · exact B434919
  · exact B434923
  · exact B434927
  · exact B434931
  · exact B434935
  · exact B434939
  · exact B434943
  · exact B434947
  · exact B434951
  · exact B434955
  · exact B434959
  · exact B434963
  · exact B434967
  · exact B434971
  · exact B434975
  · exact B434979
  · exact B434983
  · exact B434987
  · exact B434991
  · exact B434995
  · exact B434999
  · exact B435003
  · exact B435007
  · exact B435011
  · exact B435015
  · exact B435019
  · exact B435023
  · exact B435027
  · exact B435031
  · exact B435035
  · exact B435039
  · exact B435043
  · exact B435047
  · exact B435051
  · exact B435055
  · exact B435059
  · exact B435063
  · exact B435067
  · exact B435071
  · exact B435075
  · exact B435079
  · exact B435083
  · exact B435087
  · exact B435091
  · exact B435095
  · exact B435099
  · exact B435103
  · exact B435107
  · exact B435111
  · exact B435115
  · exact B435119
  · exact B435123
  · exact B435127
  · exact B435131
  · exact B435135
  · exact B435139
  · exact B435143
  · exact B435147
  · exact B435151
  · exact B435155
  · exact B435159
  · exact B435163
  · exact B435167
  · exact B435171
  · exact B435175
  · exact B435179
  · exact B435183
  · exact B435187
  · exact B435191
  · exact B435195
  · exact B435199
  · exact B435203
  · exact B435207
  · exact B435211
  · exact B435215
  · exact B435219
  · exact B435223
  · exact B435227
  · exact B435231
  · exact B435235
  · exact B435239
  · exact B435243
  · exact B435247
  · exact B435251
  · exact B435255
  · exact B435259
  · exact B435263
  · exact B435267
  · exact B435271
  · exact B435275
  · exact B435279
  · exact B435283
  · exact B435287
  · exact B435291
  · exact B435295
  · exact B435299
  · exact B435303
  · exact B435307
  · exact B435311
  · exact B435315
  · exact B435319
  · exact B435323
  · exact B435327
  · exact B435331
  · exact B435335
  · exact B435339
  · exact B435343
  · exact B435347
  · exact B435351
  · exact B435355
  · exact B435359
  · exact B435363
  · exact B435367
  · exact B435371
  · exact B435375
  · exact B435379
  · exact B435383
  · exact B435387
  · exact B435391
  · exact B435395
  · exact B435399
  · exact B435403
  · exact B435407
  · exact B435411
  · exact B435415
  · exact B435419
  · exact B435423
  · exact B435427
  · exact B435431
  · exact B435435
  · exact B435439
  · exact B435443
  · exact B435447
  · exact B435451
  · exact B435455
  · exact B435459
  · exact B435463
  · exact B435467
  · exact B435471
  · exact B435475
  · exact B435479
  · exact B435483
  · exact B435487
  · exact B435491
  · exact B435495
  · exact B435499
  · exact B435503
  · exact B435507
  · exact B435511
  · exact B435515
  · exact B435519
  · exact B435523
  · exact B435527
  · exact B435531
  · exact B435535
  · exact B435539
  · exact B435543
  · exact B435547
  · exact B435551
  · exact B435555
  · exact B435559
  · exact B435563
  · exact B435567
  · exact B435571
  · exact B435575

theorem C1 (j : ℕ) (h1 : 108894 ≤ j) (h2 : j ≤ 108943) : Blo 432776 (4 * j + 3) := by
  interval_cases j
  · exact B435579
  · exact B435583
  · exact B435587
  · exact B435591
  · exact B435595
  · exact B435599
  · exact B435603
  · exact B435607
  · exact B435611
  · exact B435615
  · exact B435619
  · exact B435623
  · exact B435627
  · exact B435631
  · exact B435635
  · exact B435639
  · exact B435643
  · exact B435647
  · exact B435651
  · exact B435655
  · exact B435659
  · exact B435663
  · exact B435667
  · exact B435671
  · exact B435675
  · exact B435679
  · exact B435683
  · exact B435687
  · exact B435691
  · exact B435695
  · exact B435699
  · exact B435703
  · exact B435707
  · exact B435711
  · exact B435715
  · exact B435719
  · exact B435723
  · exact B435727
  · exact B435731
  · exact B435735
  · exact B435739
  · exact B435743
  · exact B435747
  · exact B435751
  · exact B435755
  · exact B435759
  · exact B435763
  · exact B435767
  · exact B435771
  · exact B435775

theorem solution (m : ℕ) (hlo : 432776 ≤ m) (hhi : m ≤ 435776) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 108194 ≤ j := by omega
    have hj2 : j ≤ 108943 := by omega
    have hb : Blo 432776 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 108894 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
