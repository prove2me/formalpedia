-- Prove2me | solution 1 for syracuse_descends_range_1352995_1354995
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:51.897283+00:00
-- url     : https://prove2.me/submissions/6042c6f0-1941-4d96-a53d-10d1a1e2e47c

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


theorem B1523713 : Blo 1352995 1523713 := bbase (se 2 (by rfl) ⟨571392, by rfl⟩ : syracuseStep 1523713 = 1142785) (by norm_num)
theorem B2031629 : Blo 1352995 2031629 := bbase (se 3 (by rfl) ⟨380930, by rfl⟩ : syracuseStep 2031629 = 761861) (by norm_num)
theorem B3047453 : Blo 1352995 3047453 := bbase (se 3 (by rfl) ⟨571397, by rfl⟩ : syracuseStep 3047453 = 1142795) (by norm_num)
theorem B2285597 : Blo 1352995 2285597 := bbase (se 3 (by rfl) ⟨428549, by rfl⟩ : syracuseStep 2285597 = 857099) (by norm_num)
theorem B2031653 : Blo 1352995 2031653 := bbase (se 4 (by rfl) ⟨190467, by rfl⟩ : syracuseStep 2031653 = 380935) (by norm_num)
theorem B1523749 : Blo 1352995 1523749 := bbase (se 4 (by rfl) ⟨142851, by rfl⟩ : syracuseStep 1523749 = 285703) (by norm_num)
theorem B2031677 : Blo 1352995 2031677 := bbase (se 3 (by rfl) ⟨380939, by rfl⟩ : syracuseStep 2031677 = 761879) (by norm_num)
theorem B2744389 : Blo 1352995 2744389 := bbase (se 4 (by rfl) ⟨257286, by rfl⟩ : syracuseStep 2744389 = 514573) (by norm_num)
theorem B1523785 : Blo 1352995 1523785 := bbase (se 2 (by rfl) ⟨571419, by rfl⟩ : syracuseStep 1523785 = 1142839) (by norm_num)
theorem B2031701 : Blo 1352995 2031701 := bbase (se 8 (by rfl) ⟨11904, by rfl⟩ : syracuseStep 2031701 = 23809) (by norm_num)
theorem B3047525 : Blo 1352995 3047525 := bbase (se 4 (by rfl) ⟨285705, by rfl⟩ : syracuseStep 3047525 = 571411) (by norm_num)
theorem B2031725 : Blo 1352995 2031725 := bbase (se 3 (by rfl) ⟨380948, by rfl⟩ : syracuseStep 2031725 = 761897) (by norm_num)
theorem B1523821 : Blo 1352995 1523821 := bbase (se 3 (by rfl) ⟨285716, by rfl⟩ : syracuseStep 1523821 = 571433) (by norm_num)
theorem B2031749 : Blo 1352995 2031749 := bbase (se 4 (by rfl) ⟨190476, by rfl⟩ : syracuseStep 2031749 = 380953) (by norm_num)
theorem B1523857 : Blo 1352995 1523857 := bbase (se 2 (by rfl) ⟨571446, by rfl⟩ : syracuseStep 1523857 = 1142893) (by norm_num)
theorem B2285725 : Blo 1352995 2285725 := bbase (se 3 (by rfl) ⟨428573, by rfl⟩ : syracuseStep 2285725 = 857147) (by norm_num)
theorem B2031773 : Blo 1352995 2031773 := bbase (se 3 (by rfl) ⟨380957, by rfl⟩ : syracuseStep 2031773 = 761915) (by norm_num)
theorem B3047597 : Blo 1352995 3047597 := bbase (se 3 (by rfl) ⟨571424, by rfl⟩ : syracuseStep 3047597 = 1142849) (by norm_num)
theorem B11567285 : Blo 1352995 11567285 := bbase (se 5 (by rfl) ⟨542216, by rfl⟩ : syracuseStep 11567285 = 1084433) (by norm_num)
theorem B2031797 : Blo 1352995 2031797 := bbase (se 5 (by rfl) ⟨95240, by rfl⟩ : syracuseStep 2031797 = 190481) (by norm_num)
theorem B1523893 : Blo 1352995 1523893 := bbase (se 5 (by rfl) ⟨71432, by rfl⟩ : syracuseStep 1523893 = 142865) (by norm_num)
theorem B1736893 : Blo 1352995 1736893 := bbase (se 3 (by rfl) ⟨325667, by rfl⟩ : syracuseStep 1736893 = 651335) (by norm_num)
theorem B2031821 : Blo 1352995 2031821 := bbase (se 3 (by rfl) ⟨380966, by rfl⟩ : syracuseStep 2031821 = 761933) (by norm_num)
theorem B1523929 : Blo 1352995 1523929 := bbase (se 2 (by rfl) ⟨571473, by rfl⟩ : syracuseStep 1523929 = 1142947) (by norm_num)
theorem B2031845 : Blo 1352995 2031845 := bbase (se 4 (by rfl) ⟨190485, by rfl⟩ : syracuseStep 2031845 = 380971) (by norm_num)
theorem B3047669 : Blo 1352995 3047669 := bbase (se 5 (by rfl) ⟨142859, by rfl⟩ : syracuseStep 3047669 = 285719) (by norm_num)
theorem B2285813 : Blo 1352995 2285813 := bbase (se 5 (by rfl) ⟨107147, by rfl⟩ : syracuseStep 2285813 = 214295) (by norm_num)
theorem B2031869 : Blo 1352995 2031869 := bbase (se 3 (by rfl) ⟨380975, by rfl⟩ : syracuseStep 2031869 = 761951) (by norm_num)
theorem B1523965 : Blo 1352995 1523965 := bbase (se 3 (by rfl) ⟨285743, by rfl⟩ : syracuseStep 1523965 = 571487) (by norm_num)
theorem B2031893 : Blo 1352995 2031893 := bbase (se 6 (by rfl) ⟨47622, by rfl⟩ : syracuseStep 2031893 = 95245) (by norm_num)
theorem B1524001 : Blo 1352995 1524001 := bbase (se 2 (by rfl) ⟨571500, by rfl⟩ : syracuseStep 1524001 = 1143001) (by norm_num)
theorem B2031917 : Blo 1352995 2031917 := bbase (se 3 (by rfl) ⟨380984, by rfl⟩ : syracuseStep 2031917 = 761969) (by norm_num)
theorem B1712441 : Blo 1352995 1712441 := bbase (se 2 (by rfl) ⟨642165, by rfl⟩ : syracuseStep 1712441 = 1284331) (by norm_num)
theorem B3047741 : Blo 1352995 3047741 := bbase (se 3 (by rfl) ⟨571451, by rfl⟩ : syracuseStep 3047741 = 1142903) (by norm_num)
theorem B2031941 : Blo 1352995 2031941 := bbase (se 4 (by rfl) ⟨190494, by rfl⟩ : syracuseStep 2031941 = 380989) (by norm_num)
theorem B1524037 : Blo 1352995 1524037 := bbase (se 4 (by rfl) ⟨142878, by rfl⟩ : syracuseStep 1524037 = 285757) (by norm_num)
theorem B4571477 : Blo 1352995 4571477 := bbase (se 10 (by rfl) ⟨6696, by rfl⟩ : syracuseStep 4571477 = 13393) (by norm_num)
theorem B2031965 : Blo 1352995 2031965 := bbase (se 3 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 2031965 = 761987) (by norm_num)
theorem B1524073 : Blo 1352995 1524073 := bbase (se 2 (by rfl) ⟨571527, by rfl⟩ : syracuseStep 1524073 = 1143055) (by norm_num)
theorem B1712497 : Blo 1352995 1712497 := bbase (se 2 (by rfl) ⟨642186, by rfl⟩ : syracuseStep 1712497 = 1284373) (by norm_num)
theorem B2285941 : Blo 1352995 2285941 := bbase (se 5 (by rfl) ⟨107153, by rfl⟩ : syracuseStep 2285941 = 214307) (by norm_num)
theorem B2031989 : Blo 1352995 2031989 := bbase (se 5 (by rfl) ⟨95249, by rfl⟩ : syracuseStep 2031989 = 190499) (by norm_num)
theorem B3047813 : Blo 1352995 3047813 := bbase (se 4 (by rfl) ⟨285732, by rfl⟩ : syracuseStep 3047813 = 571465) (by norm_num)
theorem B2032013 : Blo 1352995 2032013 := bbase (se 3 (by rfl) ⟨381002, by rfl⟩ : syracuseStep 2032013 = 762005) (by norm_num)
theorem B1524109 : Blo 1352995 1524109 := bbase (se 3 (by rfl) ⟨285770, by rfl⟩ : syracuseStep 1524109 = 571541) (by norm_num)
theorem B2032037 : Blo 1352995 2032037 := bbase (se 4 (by rfl) ⟨190503, by rfl⟩ : syracuseStep 2032037 = 381007) (by norm_num)
theorem B1524145 : Blo 1352995 1524145 := bbase (se 2 (by rfl) ⟨571554, by rfl⟩ : syracuseStep 1524145 = 1143109) (by norm_num)
theorem B2032061 : Blo 1352995 2032061 := bbase (se 3 (by rfl) ⟨381011, by rfl⟩ : syracuseStep 2032061 = 762023) (by norm_num)
theorem B3047885 : Blo 1352995 3047885 := bbase (se 3 (by rfl) ⟨571478, by rfl⟩ : syracuseStep 3047885 = 1142957) (by norm_num)
theorem B2286029 : Blo 1352995 2286029 := bbase (se 3 (by rfl) ⟨428630, by rfl⟩ : syracuseStep 2286029 = 857261) (by norm_num)
theorem B1712593 : Blo 1352995 1712593 := bbase (se 2 (by rfl) ⟨642222, by rfl⟩ : syracuseStep 1712593 = 1284445) (by norm_num)
theorem B2032085 : Blo 1352995 2032085 := bbase (se 7 (by rfl) ⟨23813, by rfl⟩ : syracuseStep 2032085 = 47627) (by norm_num)
theorem B1524181 : Blo 1352995 1524181 := bbase (se 7 (by rfl) ⟨17861, by rfl⟩ : syracuseStep 1524181 = 35723) (by norm_num)
theorem B2032109 : Blo 1352995 2032109 := bbase (se 3 (by rfl) ⟨381020, by rfl⟩ : syracuseStep 2032109 = 762041) (by norm_num)
theorem B1524217 : Blo 1352995 1524217 := bbase (se 2 (by rfl) ⟨571581, by rfl⟩ : syracuseStep 1524217 = 1143163) (by norm_num)
theorem B2032133 : Blo 1352995 2032133 := bbase (se 4 (by rfl) ⟨190512, by rfl⟩ : syracuseStep 2032133 = 381025) (by norm_num)
theorem B4882949 : Blo 1352995 4882949 := bbase (se 4 (by rfl) ⟨457776, by rfl⟩ : syracuseStep 4882949 = 915553) (by norm_num)
theorem B3424781 : Blo 1352995 3424781 := bbase (se 3 (by rfl) ⟨642146, by rfl⟩ : syracuseStep 3424781 = 1284293) (by norm_num)
theorem B3047957 : Blo 1352995 3047957 := bbase (se 6 (by rfl) ⟨71436, by rfl⟩ : syracuseStep 3047957 = 142873) (by norm_num)
theorem B2032157 : Blo 1352995 2032157 := bbase (se 3 (by rfl) ⟨381029, by rfl⟩ : syracuseStep 2032157 = 762059) (by norm_num)
theorem B1524253 : Blo 1352995 1524253 := bbase (se 3 (by rfl) ⟨285797, by rfl⟩ : syracuseStep 1524253 = 571595) (by norm_num)
theorem B2032181 : Blo 1352995 2032181 := bbase (se 5 (by rfl) ⟨95258, by rfl⟩ : syracuseStep 2032181 = 190517) (by norm_num)
theorem B1524289 : Blo 1352995 1524289 := bbase (se 2 (by rfl) ⟨571608, by rfl⟩ : syracuseStep 1524289 = 1143217) (by norm_num)
theorem B2286157 : Blo 1352995 2286157 := bbase (se 3 (by rfl) ⟨428654, by rfl⟩ : syracuseStep 2286157 = 857309) (by norm_num)
theorem B2032205 : Blo 1352995 2032205 := bbase (se 3 (by rfl) ⟨381038, by rfl⟩ : syracuseStep 2032205 = 762077) (by norm_num)
theorem B9765461 : Blo 1352995 9765461 := bbase (se 8 (by rfl) ⟨57219, by rfl⟩ : syracuseStep 9765461 = 114439) (by norm_num)
theorem B3048029 : Blo 1352995 3048029 := bbase (se 3 (by rfl) ⟨571505, by rfl⟩ : syracuseStep 3048029 = 1143011) (by norm_num)
theorem B2032229 : Blo 1352995 2032229 := bbase (se 4 (by rfl) ⟨190521, by rfl⟩ : syracuseStep 2032229 = 381043) (by norm_num)
theorem B1524325 : Blo 1352995 1524325 := bbase (se 4 (by rfl) ⟨142905, by rfl⟩ : syracuseStep 1524325 = 285811) (by norm_num)
theorem B1712765 : Blo 1352995 1712765 := bbase (se 3 (by rfl) ⟨321143, by rfl⟩ : syracuseStep 1712765 = 642287) (by norm_num)
theorem B2032253 : Blo 1352995 2032253 := bbase (se 3 (by rfl) ⟨381047, by rfl⟩ : syracuseStep 2032253 = 762095) (by norm_num)
theorem B1524361 : Blo 1352995 1524361 := bbase (se 2 (by rfl) ⟨571635, by rfl⟩ : syracuseStep 1524361 = 1143271) (by norm_num)
theorem B2032277 : Blo 1352995 2032277 := bbase (se 6 (by rfl) ⟨47631, by rfl⟩ : syracuseStep 2032277 = 95263) (by norm_num)
theorem B3048101 : Blo 1352995 3048101 := bbase (se 4 (by rfl) ⟨285759, by rfl⟩ : syracuseStep 3048101 = 571519) (by norm_num)
theorem B2286245 : Blo 1352995 2286245 := bbase (se 4 (by rfl) ⟨214335, by rfl⟩ : syracuseStep 2286245 = 428671) (by norm_num)
theorem B2032301 : Blo 1352995 2032301 := bbase (se 3 (by rfl) ⟨381056, by rfl⟩ : syracuseStep 2032301 = 762113) (by norm_num)
theorem B1712821 : Blo 1352995 1712821 := bbase (se 5 (by rfl) ⟨80288, by rfl⟩ : syracuseStep 1712821 = 160577) (by norm_num)
theorem B2032325 : Blo 1352995 2032325 := bbase (se 4 (by rfl) ⟨190530, by rfl⟩ : syracuseStep 2032325 = 381061) (by norm_num)
theorem B2032349 : Blo 1352995 2032349 := bbase (se 3 (by rfl) ⟨381065, by rfl⟩ : syracuseStep 2032349 = 762131) (by norm_num)
theorem B7045861 : Blo 1352995 7045861 := bbase (se 4 (by rfl) ⟨660549, by rfl⟩ : syracuseStep 7045861 = 1321099) (by norm_num)
theorem B3048173 : Blo 1352995 3048173 := bbase (se 3 (by rfl) ⟨571532, by rfl⟩ : syracuseStep 3048173 = 1143065) (by norm_num)
theorem B2032373 : Blo 1352995 2032373 := bbase (se 5 (by rfl) ⟨95267, by rfl⟩ : syracuseStep 2032373 = 190535) (by norm_num)
theorem B4571909 : Blo 1352995 4571909 := bbase (se 4 (by rfl) ⟨428616, by rfl⟩ : syracuseStep 4571909 = 857233) (by norm_num)
theorem B2032397 : Blo 1352995 2032397 := bbase (se 3 (by rfl) ⟨381074, by rfl⟩ : syracuseStep 2032397 = 762149) (by norm_num)
theorem B1712917 : Blo 1352995 1712917 := bbase (se 6 (by rfl) ⟨40146, by rfl⟩ : syracuseStep 1712917 = 80293) (by norm_num)
theorem B6259477 : Blo 1352995 6259477 := bbase (se 6 (by rfl) ⟨146706, by rfl⟩ : syracuseStep 6259477 = 293413) (by norm_num)
theorem B1737509 : Blo 1352995 1737509 := bbase (se 4 (by rfl) ⟨162891, by rfl⟩ : syracuseStep 1737509 = 325783) (by norm_num)
theorem B3089189 : Blo 1352995 3089189 := bbase (se 4 (by rfl) ⟨289611, by rfl⟩ : syracuseStep 3089189 = 579223) (by norm_num)
theorem B2286373 : Blo 1352995 2286373 := bbase (se 4 (by rfl) ⟨214347, by rfl⟩ : syracuseStep 2286373 = 428695) (by norm_num)
theorem B2032421 : Blo 1352995 2032421 := bbase (se 4 (by rfl) ⟨190539, by rfl⟩ : syracuseStep 2032421 = 381079) (by norm_num)
theorem B3048245 : Blo 1352995 3048245 := bbase (se 5 (by rfl) ⟨142886, by rfl⟩ : syracuseStep 3048245 = 285773) (by norm_num)
theorem B2032445 : Blo 1352995 2032445 := bbase (se 3 (by rfl) ⟨381083, by rfl⟩ : syracuseStep 2032445 = 762167) (by norm_num)
theorem B2032469 : Blo 1352995 2032469 := bbase (se 9 (by rfl) ⟨5954, by rfl⟩ : syracuseStep 2032469 = 11909) (by norm_num)
theorem B3425125 : Blo 1352995 3425125 := bbase (se 4 (by rfl) ⟨321105, by rfl⟩ : syracuseStep 3425125 = 642211) (by norm_num)
theorem B2032493 : Blo 1352995 2032493 := bbase (se 3 (by rfl) ⟨381092, by rfl⟩ : syracuseStep 2032493 = 762185) (by norm_num)
theorem B3253117 : Blo 1352995 3253117 := bbase (se 3 (by rfl) ⟨609959, by rfl⟩ : syracuseStep 3253117 = 1219919) (by norm_num)
theorem B3048317 : Blo 1352995 3048317 := bbase (se 3 (by rfl) ⟨571559, by rfl⟩ : syracuseStep 3048317 = 1143119) (by norm_num)
theorem B2286461 : Blo 1352995 2286461 := bbase (se 3 (by rfl) ⟨428711, by rfl⟩ : syracuseStep 2286461 = 857423) (by norm_num)
theorem B6857621 : Blo 1352995 6857621 := bbase (se 6 (by rfl) ⟨160725, by rfl⟩ : syracuseStep 6857621 = 321451) (by norm_num)
theorem B1713089 : Blo 1352995 1713089 := bbase (se 2 (by rfl) ⟨642408, by rfl⟩ : syracuseStep 1713089 = 1284817) (by norm_num)
theorem B3048389 : Blo 1352995 3048389 := bbase (se 4 (by rfl) ⟨285786, by rfl⟩ : syracuseStep 3048389 = 571573) (by norm_num)
theorem B3425237 : Blo 1352995 3425237 := bbase (se 7 (by rfl) ⟨40139, by rfl⟩ : syracuseStep 3425237 = 80279) (by norm_num)
theorem B1713145 : Blo 1352995 1713145 := bbase (se 2 (by rfl) ⟨642429, by rfl⟩ : syracuseStep 1713145 = 1284859) (by norm_num)
theorem B3048461 : Blo 1352995 3048461 := bbase (se 3 (by rfl) ⟨571586, by rfl⟩ : syracuseStep 3048461 = 1143173) (by norm_num)
theorem B5137445 : Blo 1352995 5137445 := bbase (se 4 (by rfl) ⟨481635, by rfl⟩ : syracuseStep 5137445 = 963271) (by norm_num)
theorem B6505541 : Blo 1352995 6505541 := bbase (se 4 (by rfl) ⟨609894, by rfl⟩ : syracuseStep 6505541 = 1219789) (by norm_num)
theorem B3048533 : Blo 1352995 3048533 := bbase (se 8 (by rfl) ⟨17862, by rfl⟩ : syracuseStep 3048533 = 35725) (by norm_num)
theorem B1713241 : Blo 1352995 1713241 := bbase (se 2 (by rfl) ⟨642465, by rfl⟩ : syracuseStep 1713241 = 1284931) (by norm_num)
theorem B7709813 : Blo 1352995 7709813 := bbase (se 5 (by rfl) ⟨361397, by rfl⟩ : syracuseStep 7709813 = 722795) (by norm_num)
theorem B3425429 : Blo 1352995 3425429 := bbase (se 6 (by rfl) ⟨80283, by rfl⟩ : syracuseStep 3425429 = 160567) (by norm_num)
theorem B6177941 : Blo 1352995 6177941 := bbase (se 6 (by rfl) ⟨144795, by rfl⟩ : syracuseStep 6177941 = 289591) (by norm_num)
theorem B3048605 : Blo 1352995 3048605 := bbase (se 3 (by rfl) ⟨571613, by rfl⟩ : syracuseStep 3048605 = 1143227) (by norm_num)
theorem B4572341 : Blo 1352995 4572341 := bbase (se 5 (by rfl) ⟨214328, by rfl⟩ : syracuseStep 4572341 = 428657) (by norm_num)
theorem B3048677 : Blo 1352995 3048677 := bbase (se 4 (by rfl) ⟨285813, by rfl⟩ : syracuseStep 3048677 = 571627) (by norm_num)
theorem B5784821 : Blo 1352995 5784821 := bbase (se 5 (by rfl) ⟨271163, by rfl⟩ : syracuseStep 5784821 = 542327) (by norm_num)
theorem B1713413 : Blo 1352995 1713413 := bbase (se 4 (by rfl) ⟨160632, by rfl⟩ : syracuseStep 1713413 = 321265) (by norm_num)
theorem B6505733 : Blo 1352995 6505733 := bbase (se 4 (by rfl) ⟨609912, by rfl⟩ : syracuseStep 6505733 = 1219825) (by norm_num)
theorem B6849845 : Blo 1352995 6849845 := bbase (se 5 (by rfl) ⟨321086, by rfl⟩ : syracuseStep 6849845 = 642173) (by norm_num)
theorem B1713469 : Blo 1352995 1713469 := bbase (se 3 (by rfl) ⟨321275, by rfl⟩ : syracuseStep 1713469 = 642551) (by norm_num)
theorem B5858693 : Blo 1352995 5858693 := bbase (se 4 (by rfl) ⟨549252, by rfl⟩ : syracuseStep 5858693 = 1098505) (by norm_num)
theorem B1713565 : Blo 1352995 1713565 := bbase (se 3 (by rfl) ⟨321293, by rfl⟩ : syracuseStep 1713565 = 642587) (by norm_num)
theorem B4335029 : Blo 1352995 4335029 := bbase (se 5 (by rfl) ⟨203204, by rfl⟩ : syracuseStep 4335029 = 406409) (by norm_num)
theorem B1926605 : Blo 1352995 1926605 := bbase (se 3 (by rfl) ⟨361238, by rfl⟩ : syracuseStep 1926605 = 722477) (by norm_num)
theorem B8676821 : Blo 1352995 8676821 := bbase (se 7 (by rfl) ⟨101681, by rfl⟩ : syracuseStep 8676821 = 203363) (by norm_num)
theorem B3253733 : Blo 1352995 3253733 := bbase (se 4 (by rfl) ⟨305037, by rfl⟩ : syracuseStep 3253733 = 610075) (by norm_num)
theorem B3425773 : Blo 1352995 3425773 := bbase (se 3 (by rfl) ⟨642332, by rfl⟩ : syracuseStep 3425773 = 1284665) (by norm_num)
theorem B2893333 : Blo 1352995 2893333 := bbase (se 6 (by rfl) ⟨67812, by rfl⟩ : syracuseStep 2893333 = 135625) (by norm_num)
theorem B1713737 : Blo 1352995 1713737 := bbase (se 2 (by rfl) ⟨642651, by rfl⟩ : syracuseStep 1713737 = 1285303) (by norm_num)
theorem B3425885 : Blo 1352995 3425885 := bbase (se 3 (by rfl) ⟨642353, by rfl⟩ : syracuseStep 3425885 = 1284707) (by norm_num)
theorem B4572773 : Blo 1352995 4572773 := bbase (se 4 (by rfl) ⟨428697, by rfl⟩ : syracuseStep 4572773 = 857395) (by norm_num)
theorem B1713793 : Blo 1352995 1713793 := bbase (se 2 (by rfl) ⟨642672, by rfl⟩ : syracuseStep 1713793 = 1285345) (by norm_num)
theorem B1713889 : Blo 1352995 1713889 := bbase (se 2 (by rfl) ⟨642708, by rfl⟩ : syracuseStep 1713889 = 1285417) (by norm_num)
theorem B3426077 : Blo 1352995 3426077 := bbase (se 3 (by rfl) ⟨642389, by rfl⟩ : syracuseStep 3426077 = 1284779) (by norm_num)
theorem B3254069 : Blo 1352995 3254069 := bbase (se 5 (by rfl) ⟨152534, by rfl⟩ : syracuseStep 3254069 = 305069) (by norm_num)
theorem B1714061 : Blo 1352995 1714061 := bbase (se 3 (by rfl) ⟨321386, by rfl⟩ : syracuseStep 1714061 = 642773) (by norm_num)
theorem B1714117 : Blo 1352995 1714117 := bbase (se 4 (by rfl) ⟨160698, by rfl⟩ : syracuseStep 1714117 = 321397) (by norm_num)
theorem B1927157 : Blo 1352995 1927157 := bbase (se 5 (by rfl) ⟨90335, by rfl⟩ : syracuseStep 1927157 = 180671) (by norm_num)
theorem B1714213 : Blo 1352995 1714213 := bbase (se 4 (by rfl) ⟨160707, by rfl⟩ : syracuseStep 1714213 = 321415) (by norm_num)
theorem B5490773 : Blo 1352995 5490773 := bbase (se 8 (by rfl) ⟨32172, by rfl⟩ : syracuseStep 5490773 = 64345) (by norm_num)
theorem B3426421 : Blo 1352995 3426421 := bbase (se 5 (by rfl) ⟨160613, by rfl⟩ : syracuseStep 3426421 = 321227) (by norm_num)
theorem B3475613 : Blo 1352995 3475613 := bbase (se 3 (by rfl) ⟨651677, by rfl⟩ : syracuseStep 3475613 = 1303355) (by norm_num)
theorem B6858917 : Blo 1352995 6858917 := bbase (se 4 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 6858917 = 1286047) (by norm_num)
theorem B3254461 : Blo 1352995 3254461 := bbase (se 3 (by rfl) ⟨610211, by rfl⟩ : syracuseStep 3254461 = 1220423) (by norm_num)
theorem B2058437 : Blo 1352995 2058437 := bbase (se 4 (by rfl) ⟨192978, by rfl⟩ : syracuseStep 2058437 = 385957) (by norm_num)
theorem B1714385 : Blo 1352995 1714385 := bbase (se 2 (by rfl) ⟨642894, by rfl⟩ : syracuseStep 1714385 = 1285789) (by norm_num)
theorem B3426533 : Blo 1352995 3426533 := bbase (se 4 (by rfl) ⟨321237, by rfl⟩ : syracuseStep 3426533 = 642475) (by norm_num)
theorem B1714441 : Blo 1352995 1714441 := bbase (se 2 (by rfl) ⟨642915, by rfl⟩ : syracuseStep 1714441 = 1285831) (by norm_num)
theorem B7710997 : Blo 1352995 7710997 := bbase (se 6 (by rfl) ⟨180726, by rfl⟩ : syracuseStep 7710997 = 361453) (by norm_num)
theorem B4335925 : Blo 1352995 4335925 := bbase (se 5 (by rfl) ⟨203246, by rfl⟩ : syracuseStep 4335925 = 406493) (by norm_num)
theorem B3475781 : Blo 1352995 3475781 := bbase (se 4 (by rfl) ⟨325854, by rfl⟩ : syracuseStep 3475781 = 651709) (by norm_num)
theorem B1714537 : Blo 1352995 1714537 := bbase (se 2 (by rfl) ⟨642951, by rfl⟩ : syracuseStep 1714537 = 1285903) (by norm_num)
theorem B3426725 : Blo 1352995 3426725 := bbase (se 4 (by rfl) ⟨321255, by rfl⟩ : syracuseStep 3426725 = 642511) (by norm_num)
theorem B2746813 : Blo 1352995 2746813 := bbase (se 3 (by rfl) ⟨515027, by rfl⟩ : syracuseStep 2746813 = 1030055) (by norm_num)
theorem B1714709 : Blo 1352995 1714709 := bbase (se 6 (by rfl) ⟨40188, by rfl⟩ : syracuseStep 1714709 = 80377) (by norm_num)
theorem B11127349 : Blo 1352995 11127349 := bbase (se 5 (by rfl) ⟨521594, by rfl⟩ : syracuseStep 11127349 = 1043189) (by norm_num)
theorem B6851141 : Blo 1352995 6851141 := bbase (se 4 (by rfl) ⟨642294, by rfl⟩ : syracuseStep 6851141 = 1284589) (by norm_num)
theorem B1714765 : Blo 1352995 1714765 := bbase (se 3 (by rfl) ⟨321518, by rfl⟩ : syracuseStep 1714765 = 643037) (by norm_num)
theorem B1649317 : Blo 1352995 1649317 := bbase (se 4 (by rfl) ⟨154623, by rfl⟩ : syracuseStep 1649317 = 309247) (by norm_num)
theorem B1714861 : Blo 1352995 1714861 := bbase (se 3 (by rfl) ⟨321536, by rfl⟩ : syracuseStep 1714861 = 643073) (by norm_num)
theorem B20859605 : Blo 1352995 20859605 := bbase (se 7 (by rfl) ⟨244448, by rfl⟩ : syracuseStep 20859605 = 488897) (by norm_num)
theorem B1927909 : Blo 1352995 1927909 := bbase (se 4 (by rfl) ⟨180741, by rfl⟩ : syracuseStep 1927909 = 361483) (by norm_num)
theorem B3427069 : Blo 1352995 3427069 := bbase (se 3 (by rfl) ⟨642575, by rfl⟩ : syracuseStep 3427069 = 1285151) (by norm_num)
theorem B3427181 : Blo 1352995 3427181 := bbase (se 3 (by rfl) ⟨642596, by rfl⟩ : syracuseStep 3427181 = 1285193) (by norm_num)
theorem B9259925 : Blo 1352995 9259925 := bbase (se 6 (by rfl) ⟨217029, by rfl⟩ : syracuseStep 9259925 = 434059) (by norm_num)
theorem B3476405 : Blo 1352995 3476405 := bbase (se 5 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 3476405 = 325913) (by norm_num)
theorem B3427373 : Blo 1352995 3427373 := bbase (se 3 (by rfl) ⟨642632, by rfl⟩ : syracuseStep 3427373 = 1285265) (by norm_num)
theorem B3296333 : Blo 1352995 3296333 := bbase (se 3 (by rfl) ⟨618062, by rfl⟩ : syracuseStep 3296333 = 1236125) (by norm_num)
theorem B5139557 : Blo 1352995 5139557 := bbase (se 4 (by rfl) ⟨481833, by rfl⟩ : syracuseStep 5139557 = 963667) (by norm_num)
theorem B3910805 : Blo 1352995 3910805 := bbase (se 6 (by rfl) ⟨91659, by rfl⟩ : syracuseStep 3910805 = 183319) (by norm_num)
theorem B10284245 : Blo 1352995 10284245 := bbase (se 7 (by rfl) ⟨120518, by rfl⟩ : syracuseStep 10284245 = 241037) (by norm_num)
theorem B1371493 : Blo 1352995 1371493 := bbase (se 4 (by rfl) ⟨128577, by rfl⟩ : syracuseStep 1371493 = 257155) (by norm_num)
theorem B6950245 : Blo 1352995 6950245 := bbase (se 4 (by rfl) ⟨651585, by rfl⟩ : syracuseStep 6950245 = 1303171) (by norm_num)
theorem B3960197 : Blo 1352995 3960197 := bbase (se 4 (by rfl) ⟨371268, by rfl⟩ : syracuseStep 3960197 = 742537) (by norm_num)
theorem B5139845 : Blo 1352995 5139845 := bbase (se 4 (by rfl) ⟨481860, by rfl⟩ : syracuseStep 5139845 = 963721) (by norm_num)
theorem B3427717 : Blo 1352995 3427717 := bbase (se 4 (by rfl) ⟨321348, by rfl⟩ : syracuseStep 3427717 = 642697) (by norm_num)
theorem B3853813 : Blo 1352995 3853813 := bbase (se 5 (by rfl) ⟨180647, by rfl⟩ : syracuseStep 3853813 = 361295) (by norm_num)
theorem B3427829 : Blo 1352995 3427829 := bbase (se 5 (by rfl) ⟨160679, by rfl⟩ : syracuseStep 3427829 = 321359) (by norm_num)
theorem B1928701 : Blo 1352995 1928701 := bbase (se 3 (by rfl) ⟨361631, by rfl⟩ : syracuseStep 1928701 = 723263) (by norm_num)
theorem B1625665 : Blo 1352995 1625665 := bbase (se 2 (by rfl) ⟨609624, by rfl⟩ : syracuseStep 1625665 = 1219249) (by norm_num)
theorem B2059853 : Blo 1352995 2059853 := bbase (se 3 (by rfl) ⟨386222, by rfl⟩ : syracuseStep 2059853 = 772445) (by norm_num)
theorem B10276469 : Blo 1352995 10276469 := bbase (se 5 (by rfl) ⟨481709, by rfl⟩ : syracuseStep 10276469 = 963419) (by norm_num)
theorem B1371773 : Blo 1352995 1371773 := bbase (se 3 (by rfl) ⟨257207, by rfl⟩ : syracuseStep 1371773 = 514415) (by norm_num)
theorem B3853973 : Blo 1352995 3853973 := bbase (se 6 (by rfl) ⟨90327, by rfl⟩ : syracuseStep 3853973 = 180655) (by norm_num)
theorem B3428021 : Blo 1352995 3428021 := bbase (se 5 (by rfl) ⟨160688, by rfl⟩ : syracuseStep 3428021 = 321377) (by norm_num)
theorem B4566725 : Blo 1352995 4566725 := bbase (se 4 (by rfl) ⟨428130, by rfl⟩ : syracuseStep 4566725 = 856261) (by norm_num)
theorem B1445573 : Blo 1352995 1445573 := bbase (se 4 (by rfl) ⟨135522, by rfl⟩ : syracuseStep 1445573 = 271045) (by norm_num)
theorem B1625881 : Blo 1352995 1625881 := bbase (se 2 (by rfl) ⟨609705, by rfl⟩ : syracuseStep 1625881 = 1219411) (by norm_num)
theorem B1953589 : Blo 1352995 1953589 := bbase (se 5 (by rfl) ⟨91574, by rfl⟩ : syracuseStep 1953589 = 183149) (by norm_num)
theorem B1929037 : Blo 1352995 1929037 := bbase (se 3 (by rfl) ⟨361694, by rfl⟩ : syracuseStep 1929037 = 723389) (by norm_num)
theorem B6852437 : Blo 1352995 6852437 := bbase (se 9 (by rfl) ⟨20075, by rfl⟩ : syracuseStep 6852437 = 40151) (by norm_num)
theorem B3854213 : Blo 1352995 3854213 := bbase (se 4 (by rfl) ⟨361332, by rfl⟩ : syracuseStep 3854213 = 722665) (by norm_num)
theorem B3428365 : Blo 1352995 3428365 := bbase (se 3 (by rfl) ⟨642818, by rfl⟩ : syracuseStep 3428365 = 1285637) (by norm_num)
theorem B1929253 : Blo 1352995 1929253 := bbase (se 4 (by rfl) ⟨180867, by rfl⟩ : syracuseStep 1929253 = 361735) (by norm_num)
theorem B3854405 : Blo 1352995 3854405 := bbase (se 4 (by rfl) ⟨361350, by rfl⟩ : syracuseStep 3854405 = 722701) (by norm_num)
theorem B1626193 : Blo 1352995 1626193 := bbase (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) (by norm_num)
theorem B4567157 : Blo 1352995 4567157 := bbase (se 5 (by rfl) ⟨214085, by rfl⟩ : syracuseStep 4567157 = 428171) (by norm_num)
theorem B3428477 : Blo 1352995 3428477 := bbase (se 3 (by rfl) ⟨642839, by rfl⟩ : syracuseStep 3428477 = 1285679) (by norm_num)
theorem B1446017 : Blo 1352995 1446017 := bbase (se 2 (by rfl) ⟨542256, by rfl⟩ : syracuseStep 1446017 = 1084513) (by norm_num)
theorem B7712981 : Blo 1352995 7712981 := bbase (se 7 (by rfl) ⟨90386, by rfl⟩ : syracuseStep 7712981 = 180773) (by norm_num)
theorem B6598901 : Blo 1352995 6598901 := bbase (se 5 (by rfl) ⟨309323, by rfl⟩ : syracuseStep 6598901 = 618647) (by norm_num)
theorem B1372441 : Blo 1352995 1372441 := bbase (se 2 (by rfl) ⟨514665, by rfl⟩ : syracuseStep 1372441 = 1029331) (by norm_num)
theorem B9761077 : Blo 1352995 9761077 := bbase (se 5 (by rfl) ⟨457550, by rfl⟩ : syracuseStep 9761077 = 915101) (by norm_num)
theorem B3428669 : Blo 1352995 3428669 := bbase (se 3 (by rfl) ⟨642875, by rfl⟩ : syracuseStep 3428669 = 1285751) (by norm_num)
theorem B1446265 : Blo 1352995 1446265 := bbase (se 2 (by rfl) ⟨542349, by rfl⟩ : syracuseStep 1446265 = 1084699) (by norm_num)
theorem B6951349 : Blo 1352995 6951349 := bbase (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) (by norm_num)
theorem B2568685 : Blo 1352995 2568685 := bbase (se 3 (by rfl) ⟨481628, by rfl⟩ : syracuseStep 2568685 = 963257) (by norm_num)
theorem B4567589 : Blo 1352995 4567589 := bbase (se 4 (by rfl) ⟨428211, by rfl⟩ : syracuseStep 4567589 = 856423) (by norm_num)
theorem B5141029 : Blo 1352995 5141029 := bbase (se 4 (by rfl) ⟨481971, by rfl⟩ : syracuseStep 5141029 = 963943) (by norm_num)
theorem B13013621 : Blo 1352995 13013621 := bbase (se 5 (by rfl) ⟨610013, by rfl⟩ : syracuseStep 13013621 = 1220027) (by norm_num)
theorem B2568829 : Blo 1352995 2568829 := bbase (se 3 (by rfl) ⟨481655, by rfl⟩ : syracuseStep 2568829 = 963311) (by norm_num)
theorem B3658373 : Blo 1352995 3658373 := bbase (se 4 (by rfl) ⟨342972, by rfl⟩ : syracuseStep 3658373 = 685945) (by norm_num)
theorem B3429013 : Blo 1352995 3429013 := bbase (se 6 (by rfl) ⟨80367, by rfl⟩ : syracuseStep 3429013 = 160735) (by norm_num)
theorem B3658501 : Blo 1352995 3658501 := bbase (se 4 (by rfl) ⟨342984, by rfl⟩ : syracuseStep 3658501 = 685969) (by norm_num)
theorem B3429125 : Blo 1352995 3429125 := bbase (se 4 (by rfl) ⟨321480, by rfl⟩ : syracuseStep 3429125 = 642961) (by norm_num)
theorem B2167565 : Blo 1352995 2167565 := bbase (se 3 (by rfl) ⟨406418, by rfl⟩ : syracuseStep 2167565 = 812837) (by norm_num)
theorem B17593109 : Blo 1352995 17593109 := bbase (se 6 (by rfl) ⟨412338, by rfl⟩ : syracuseStep 17593109 = 824677) (by norm_num)
theorem B2568989 : Blo 1352995 2568989 := bbase (se 3 (by rfl) ⟨481685, by rfl⟩ : syracuseStep 2568989 = 963371) (by norm_num)
theorem B1446697 : Blo 1352995 1446697 := bbase (se 2 (by rfl) ⟨542511, by rfl⟩ : syracuseStep 1446697 = 1085023) (by norm_num)
theorem B4117301 : Blo 1352995 4117301 := bbase (se 5 (by rfl) ⟨192998, by rfl⟩ : syracuseStep 4117301 = 385997) (by norm_num)
theorem B3175229 : Blo 1352995 3175229 := bbase (se 3 (by rfl) ⟨595355, by rfl⟩ : syracuseStep 3175229 = 1190711) (by norm_num)
theorem B1373005 : Blo 1352995 1373005 := bbase (se 3 (by rfl) ⟨257438, by rfl⟩ : syracuseStep 1373005 = 514877) (by norm_num)
theorem B1373009 : Blo 1352995 1373009 := bbase (se 2 (by rfl) ⟨514878, by rfl⟩ : syracuseStep 1373009 = 1029757) (by norm_num)
theorem B5141333 : Blo 1352995 5141333 := bbase (se 9 (by rfl) ⟨15062, by rfl⟩ : syracuseStep 5141333 = 30125) (by norm_num)
theorem B1446769 : Blo 1352995 1446769 := bbase (se 2 (by rfl) ⟨542538, by rfl⟩ : syracuseStep 1446769 = 1085077) (by norm_num)
theorem B7811957 : Blo 1352995 7811957 := bbase (se 5 (by rfl) ⟨366185, by rfl⟩ : syracuseStep 7811957 = 732371) (by norm_num)
theorem B2569133 : Blo 1352995 2569133 := bbase (se 3 (by rfl) ⟨481712, by rfl⟩ : syracuseStep 2569133 = 963425) (by norm_num)
theorem B3044285 : Blo 1352995 3044285 := bbase (se 3 (by rfl) ⟨570803, by rfl⟩ : syracuseStep 3044285 = 1141607) (by norm_num)
theorem B3429317 : Blo 1352995 3429317 := bbase (se 4 (by rfl) ⟨321498, by rfl⟩ : syracuseStep 3429317 = 642997) (by norm_num)
theorem B4568021 : Blo 1352995 4568021 := bbase (se 7 (by rfl) ⟨53531, by rfl⟩ : syracuseStep 4568021 = 107063) (by norm_num)
theorem B3044357 : Blo 1352995 3044357 := bbase (se 4 (by rfl) ⟨285408, by rfl⟩ : syracuseStep 3044357 = 570817) (by norm_num)
theorem B3855397 : Blo 1352995 3855397 := bbase (se 4 (by rfl) ⟨361443, by rfl⟩ : syracuseStep 3855397 = 722887) (by norm_num)
theorem B8352821 : Blo 1352995 8352821 := bbase (se 5 (by rfl) ⟨391538, by rfl⟩ : syracuseStep 8352821 = 783077) (by norm_num)
theorem B3044429 : Blo 1352995 3044429 := bbase (se 3 (by rfl) ⟨570830, by rfl⟩ : syracuseStep 3044429 = 1141661) (by norm_num)
theorem B6853733 : Blo 1352995 6853733 := bbase (se 4 (by rfl) ⟨642537, by rfl⟩ : syracuseStep 6853733 = 1285075) (by norm_num)
theorem B4338821 : Blo 1352995 4338821 := bbase (se 4 (by rfl) ⟨406764, by rfl⟩ : syracuseStep 4338821 = 813529) (by norm_num)
theorem B3044501 : Blo 1352995 3044501 := bbase (se 6 (by rfl) ⟨71355, by rfl⟩ : syracuseStep 3044501 = 142711) (by norm_num)
theorem B2438309 : Blo 1352995 2438309 := bbase (se 4 (by rfl) ⟨228591, by rfl⟩ : syracuseStep 2438309 = 457183) (by norm_num)
theorem B2929829 : Blo 1352995 2929829 := bbase (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) (by norm_num)
theorem B2569421 : Blo 1352995 2569421 := bbase (se 3 (by rfl) ⟨481766, by rfl⟩ : syracuseStep 2569421 = 963533) (by norm_num)
theorem B3044573 : Blo 1352995 3044573 := bbase (se 3 (by rfl) ⟨570857, by rfl⟩ : syracuseStep 3044573 = 1141715) (by norm_num)
theorem B11564309 : Blo 1352995 11564309 := bbase (se 6 (by rfl) ⟨271038, by rfl⟩ : syracuseStep 11564309 = 542077) (by norm_num)
theorem B6509845 : Blo 1352995 6509845 := bbase (se 6 (by rfl) ⟨152574, by rfl⟩ : syracuseStep 6509845 = 305149) (by norm_num)
theorem B3429661 : Blo 1352995 3429661 := bbase (se 3 (by rfl) ⟨643061, by rfl⟩ : syracuseStep 3429661 = 1286123) (by norm_num)
theorem B3044645 : Blo 1352995 3044645 := bbase (se 4 (by rfl) ⟨285435, by rfl⟩ : syracuseStep 3044645 = 570871) (by norm_num)
theorem B2168117 : Blo 1352995 2168117 := bbase (se 5 (by rfl) ⟨101630, by rfl⟩ : syracuseStep 2168117 = 203261) (by norm_num)
theorem B5862709 : Blo 1352995 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B2168149 : Blo 1352995 2168149 := bbase (se 14 (by rfl) ⟨198, by rfl⟩ : syracuseStep 2168149 = 397) (by norm_num)
theorem B2569573 : Blo 1352995 2569573 := bbase (se 4 (by rfl) ⟨240897, by rfl⟩ : syracuseStep 2569573 = 481795) (by norm_num)
theorem B3044717 : Blo 1352995 3044717 := bbase (se 3 (by rfl) ⟨570884, by rfl⟩ : syracuseStep 3044717 = 1141769) (by norm_num)
theorem B4568453 : Blo 1352995 4568453 := bbase (se 4 (by rfl) ⟨428292, by rfl⟩ : syracuseStep 4568453 = 856585) (by norm_num)
theorem B3429773 : Blo 1352995 3429773 := bbase (se 3 (by rfl) ⟨643082, by rfl⟩ : syracuseStep 3429773 = 1286165) (by norm_num)
theorem B3044789 : Blo 1352995 3044789 := bbase (se 5 (by rfl) ⟨142724, by rfl⟩ : syracuseStep 3044789 = 285449) (by norm_num)
theorem B6174197 : Blo 1352995 6174197 := bbase (se 5 (by rfl) ⟨289415, by rfl⟩ : syracuseStep 6174197 = 578831) (by norm_num)
theorem B3044861 : Blo 1352995 3044861 := bbase (se 3 (by rfl) ⟨570911, by rfl⟩ : syracuseStep 3044861 = 1141823) (by norm_num)
theorem B1627673 : Blo 1352995 1627673 := bbase (se 2 (by rfl) ⟨610377, by rfl⟩ : syracuseStep 1627673 = 1220755) (by norm_num)
theorem B3044933 : Blo 1352995 3044933 := bbase (se 4 (by rfl) ⟨285462, by rfl⟩ : syracuseStep 3044933 = 570925) (by norm_num)
theorem B5781061 : Blo 1352995 5781061 := bbase (se 4 (by rfl) ⟨541974, by rfl⟩ : syracuseStep 5781061 = 1083949) (by norm_num)
theorem B1627769 : Blo 1352995 1627769 := bbase (se 2 (by rfl) ⟨610413, by rfl⟩ : syracuseStep 1627769 = 1220827) (by norm_num)
theorem B3045005 : Blo 1352995 3045005 := bbase (se 3 (by rfl) ⟨570938, by rfl⟩ : syracuseStep 3045005 = 1141877) (by norm_num)
theorem B1627789 : Blo 1352995 1627789 := bbase (se 3 (by rfl) ⟨305210, by rfl⟩ : syracuseStep 1627789 = 610421) (by norm_num)
theorem B2569877 : Blo 1352995 2569877 := bbase (se 6 (by rfl) ⟨60231, by rfl⟩ : syracuseStep 2569877 = 120463) (by norm_num)
theorem B2283221 : Blo 1352995 2283221 := bbase (se 7 (by rfl) ⟨26756, by rfl⟩ : syracuseStep 2283221 = 53513) (by norm_num)
theorem B3045077 : Blo 1352995 3045077 := bbase (se 7 (by rfl) ⟨35684, by rfl⟩ : syracuseStep 3045077 = 71369) (by norm_num)
theorem B3045149 : Blo 1352995 3045149 := bbase (se 3 (by rfl) ⟨570965, by rfl⟩ : syracuseStep 3045149 = 1141931) (by norm_num)
theorem B5207845 : Blo 1352995 5207845 := bbase (se 4 (by rfl) ⟨488235, by rfl⟩ : syracuseStep 5207845 = 976471) (by norm_num)
theorem B3708725 : Blo 1352995 3708725 := bbase (se 5 (by rfl) ⟨173846, by rfl⟩ : syracuseStep 3708725 = 347693) (by norm_num)
theorem B4568885 : Blo 1352995 4568885 := bbase (se 5 (by rfl) ⟨214166, by rfl⟩ : syracuseStep 4568885 = 428333) (by norm_num)
theorem B2283349 : Blo 1352995 2283349 := bbase (se 9 (by rfl) ⟨6689, by rfl⟩ : syracuseStep 2283349 = 13379) (by norm_num)
theorem B3045221 : Blo 1352995 3045221 := bbase (se 4 (by rfl) ⟨285489, by rfl⟩ : syracuseStep 3045221 = 570979) (by norm_num)
theorem B2283437 : Blo 1352995 2283437 := bbase (se 3 (by rfl) ⟨428144, by rfl⟩ : syracuseStep 2283437 = 856289) (by norm_num)
theorem B3045293 : Blo 1352995 3045293 := bbase (se 3 (by rfl) ⟨570992, by rfl⟩ : syracuseStep 3045293 = 1141985) (by norm_num)
theorem B2029493 : Blo 1352995 2029493 := bbase (se 5 (by rfl) ⟨95132, by rfl⟩ : syracuseStep 2029493 = 190265) (by norm_num)
theorem B2889677 : Blo 1352995 2889677 := bbase (se 3 (by rfl) ⟨541814, by rfl⟩ : syracuseStep 2889677 = 1083629) (by norm_num)
theorem B2029517 : Blo 1352995 2029517 := bbase (se 3 (by rfl) ⟨380534, by rfl⟩ : syracuseStep 2029517 = 761069) (by norm_num)
theorem B2349005 : Blo 1352995 2349005 := bbase (se 3 (by rfl) ⟨440438, by rfl⟩ : syracuseStep 2349005 = 880877) (by norm_num)
theorem B2029541 : Blo 1352995 2029541 := bbase (se 4 (by rfl) ⟨190269, by rfl⟩ : syracuseStep 2029541 = 380539) (by norm_num)
theorem B3045365 : Blo 1352995 3045365 := bbase (se 5 (by rfl) ⟨142751, by rfl⟩ : syracuseStep 3045365 = 285503) (by norm_num)
theorem B2029565 : Blo 1352995 2029565 := bbase (se 3 (by rfl) ⟨380543, by rfl⟩ : syracuseStep 2029565 = 761087) (by norm_num)
theorem B2029589 : Blo 1352995 2029589 := bbase (se 6 (by rfl) ⟨47568, by rfl⟩ : syracuseStep 2029589 = 95137) (by norm_num)
theorem B2029613 : Blo 1352995 2029613 := bbase (se 3 (by rfl) ⟨380552, by rfl⟩ : syracuseStep 2029613 = 761105) (by norm_num)
theorem B2283565 : Blo 1352995 2283565 := bbase (se 3 (by rfl) ⟨428168, by rfl⟩ : syracuseStep 2283565 = 856337) (by norm_num)
theorem B3045437 : Blo 1352995 3045437 := bbase (se 3 (by rfl) ⟨571019, by rfl⟩ : syracuseStep 3045437 = 1142039) (by norm_num)
theorem B2029637 : Blo 1352995 2029637 := bbase (se 4 (by rfl) ⟨190278, by rfl⟩ : syracuseStep 2029637 = 380557) (by norm_num)
theorem B2029661 : Blo 1352995 2029661 := bbase (se 3 (by rfl) ⟨380561, by rfl⟩ : syracuseStep 2029661 = 761123) (by norm_num)
theorem B2029685 : Blo 1352995 2029685 := bbase (se 5 (by rfl) ⟨95141, by rfl⟩ : syracuseStep 2029685 = 190283) (by norm_num)
theorem B3856501 : Blo 1352995 3856501 := bbase (se 5 (by rfl) ⟨180773, by rfl⟩ : syracuseStep 3856501 = 361547) (by norm_num)
theorem B2283653 : Blo 1352995 2283653 := bbase (se 4 (by rfl) ⟨214092, by rfl⟩ : syracuseStep 2283653 = 428185) (by norm_num)
theorem B3045509 : Blo 1352995 3045509 := bbase (se 4 (by rfl) ⟨285516, by rfl⟩ : syracuseStep 3045509 = 571033) (by norm_num)
theorem B2029709 : Blo 1352995 2029709 := bbase (se 3 (by rfl) ⟨380570, by rfl⟩ : syracuseStep 2029709 = 761141) (by norm_num)
theorem B2029733 : Blo 1352995 2029733 := bbase (se 4 (by rfl) ⟨190287, by rfl⟩ : syracuseStep 2029733 = 380575) (by norm_num)
theorem B2029757 : Blo 1352995 2029757 := bbase (se 3 (by rfl) ⟨380579, by rfl⟩ : syracuseStep 2029757 = 761159) (by norm_num)
theorem B3045581 : Blo 1352995 3045581 := bbase (se 3 (by rfl) ⟨571046, by rfl⟩ : syracuseStep 3045581 = 1142093) (by norm_num)
theorem B2029781 : Blo 1352995 2029781 := bbase (se 7 (by rfl) ⟨23786, by rfl⟩ : syracuseStep 2029781 = 47573) (by norm_num)
theorem B4569317 : Blo 1352995 4569317 := bbase (se 4 (by rfl) ⟨428373, by rfl⟩ : syracuseStep 4569317 = 856747) (by norm_num)
theorem B2029805 : Blo 1352995 2029805 := bbase (se 3 (by rfl) ⟨380588, by rfl⟩ : syracuseStep 2029805 = 761177) (by norm_num)
theorem B2169077 : Blo 1352995 2169077 := bbase (se 5 (by rfl) ⟨101675, by rfl⟩ : syracuseStep 2169077 = 203351) (by norm_num)
theorem B2029829 : Blo 1352995 2029829 := bbase (se 4 (by rfl) ⟨190296, by rfl⟩ : syracuseStep 2029829 = 380593) (by norm_num)
theorem B2283781 : Blo 1352995 2283781 := bbase (se 4 (by rfl) ⟨214104, by rfl⟩ : syracuseStep 2283781 = 428209) (by norm_num)
theorem B3045653 : Blo 1352995 3045653 := bbase (se 6 (by rfl) ⟨71382, by rfl⟩ : syracuseStep 3045653 = 142765) (by norm_num)
theorem B2029853 : Blo 1352995 2029853 := bbase (se 3 (by rfl) ⟨380597, by rfl⟩ : syracuseStep 2029853 = 761195) (by norm_num)
theorem B2029877 : Blo 1352995 2029877 := bbase (se 5 (by rfl) ⟨95150, by rfl⟩ : syracuseStep 2029877 = 190301) (by norm_num)
theorem B2029901 : Blo 1352995 2029901 := bbase (se 3 (by rfl) ⟨380606, by rfl⟩ : syracuseStep 2029901 = 761213) (by norm_num)
theorem B2283869 : Blo 1352995 2283869 := bbase (se 3 (by rfl) ⟨428225, by rfl⟩ : syracuseStep 2283869 = 856451) (by norm_num)
theorem B3045725 : Blo 1352995 3045725 := bbase (se 3 (by rfl) ⟨571073, by rfl⟩ : syracuseStep 3045725 = 1142147) (by norm_num)
theorem B6256997 : Blo 1352995 6256997 := bbase (se 4 (by rfl) ⟨586593, by rfl⟩ : syracuseStep 6256997 = 1173187) (by norm_num)
theorem B2029925 : Blo 1352995 2029925 := bbase (se 4 (by rfl) ⟨190305, by rfl⟩ : syracuseStep 2029925 = 380611) (by norm_num)
theorem B6855029 : Blo 1352995 6855029 := bbase (se 5 (by rfl) ⟨321329, by rfl⟩ : syracuseStep 6855029 = 642659) (by norm_num)
theorem B7715189 : Blo 1352995 7715189 := bbase (se 5 (by rfl) ⟨361649, by rfl⟩ : syracuseStep 7715189 = 723299) (by norm_num)
theorem B2029949 : Blo 1352995 2029949 := bbase (se 3 (by rfl) ⟨380615, by rfl⟩ : syracuseStep 2029949 = 761231) (by norm_num)
theorem B1980805 : Blo 1352995 1980805 := bbase (se 4 (by rfl) ⟨185700, by rfl⟩ : syracuseStep 1980805 = 371401) (by norm_num)
theorem B2570629 : Blo 1352995 2570629 := bbase (se 4 (by rfl) ⟨240996, by rfl⟩ : syracuseStep 2570629 = 481993) (by norm_num)
theorem B2029973 : Blo 1352995 2029973 := bbase (se 6 (by rfl) ⟨47577, by rfl⟩ : syracuseStep 2029973 = 95155) (by norm_num)
theorem B3045797 : Blo 1352995 3045797 := bbase (se 4 (by rfl) ⟨285543, by rfl⟩ : syracuseStep 3045797 = 571087) (by norm_num)
theorem B2029997 : Blo 1352995 2029997 := bbase (se 3 (by rfl) ⟨380624, by rfl⟩ : syracuseStep 2029997 = 761249) (by norm_num)
theorem B2890181 : Blo 1352995 2890181 := bbase (se 4 (by rfl) ⟨270954, by rfl⟩ : syracuseStep 2890181 = 541909) (by norm_num)
theorem B2030021 : Blo 1352995 2030021 := bbase (se 4 (by rfl) ⟨190314, by rfl⟩ : syracuseStep 2030021 = 380629) (by norm_num)
theorem B2890189 : Blo 1352995 2890189 := bbase (se 3 (by rfl) ⟨541910, by rfl⟩ : syracuseStep 2890189 = 1083821) (by norm_num)
theorem B1522129 : Blo 1352995 1522129 := bbase (se 2 (by rfl) ⟨570798, by rfl⟩ : syracuseStep 1522129 = 1141597) (by norm_num)
theorem B2030045 : Blo 1352995 2030045 := bbase (se 3 (by rfl) ⟨380633, by rfl⟩ : syracuseStep 2030045 = 761267) (by norm_num)
theorem B2283997 : Blo 1352995 2283997 := bbase (se 3 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 2283997 = 856499) (by norm_num)
theorem B3045869 : Blo 1352995 3045869 := bbase (se 3 (by rfl) ⟨571100, by rfl⟩ : syracuseStep 3045869 = 1142201) (by norm_num)
theorem B1522165 : Blo 1352995 1522165 := bbase (se 5 (by rfl) ⟨71351, by rfl⟩ : syracuseStep 1522165 = 142703) (by norm_num)
theorem B2030069 : Blo 1352995 2030069 := bbase (se 5 (by rfl) ⟨95159, by rfl⟩ : syracuseStep 2030069 = 190319) (by norm_num)
theorem B2030093 : Blo 1352995 2030093 := bbase (se 3 (by rfl) ⟨380642, by rfl⟩ : syracuseStep 2030093 = 761285) (by norm_num)
theorem B2570773 : Blo 1352995 2570773 := bbase (se 6 (by rfl) ⟨60252, by rfl⟩ : syracuseStep 2570773 = 120505) (by norm_num)
theorem B1522201 : Blo 1352995 1522201 := bbase (se 2 (by rfl) ⟨570825, by rfl⟩ : syracuseStep 1522201 = 1141651) (by norm_num)
theorem B2030117 : Blo 1352995 2030117 := bbase (se 4 (by rfl) ⟨190323, by rfl⟩ : syracuseStep 2030117 = 380647) (by norm_num)
theorem B2284085 : Blo 1352995 2284085 := bbase (se 5 (by rfl) ⟨107066, by rfl⟩ : syracuseStep 2284085 = 214133) (by norm_num)
theorem B3045941 : Blo 1352995 3045941 := bbase (se 5 (by rfl) ⟨142778, by rfl⟩ : syracuseStep 3045941 = 285557) (by norm_num)
theorem B1522237 : Blo 1352995 1522237 := bbase (se 3 (by rfl) ⟨285419, by rfl⟩ : syracuseStep 1522237 = 570839) (by norm_num)
theorem B2030141 : Blo 1352995 2030141 := bbase (se 3 (by rfl) ⟨380651, by rfl⟩ : syracuseStep 2030141 = 761303) (by norm_num)
theorem B2030165 : Blo 1352995 2030165 := bbase (se 8 (by rfl) ⟨11895, by rfl⟩ : syracuseStep 2030165 = 23791) (by norm_num)
theorem B12352085 : Blo 1352995 12352085 := bbase (se 8 (by rfl) ⟨72375, by rfl⟩ : syracuseStep 12352085 = 144751) (by norm_num)
theorem B4397653 : Blo 1352995 4397653 := bbase (se 8 (by rfl) ⟨25767, by rfl⟩ : syracuseStep 4397653 = 51535) (by norm_num)
theorem B1522273 : Blo 1352995 1522273 := bbase (se 2 (by rfl) ⟨570852, by rfl⟩ : syracuseStep 1522273 = 1141705) (by norm_num)
theorem B2030189 : Blo 1352995 2030189 := bbase (se 3 (by rfl) ⟨380660, by rfl⟩ : syracuseStep 2030189 = 761321) (by norm_num)
theorem B3046013 : Blo 1352995 3046013 := bbase (se 3 (by rfl) ⟨571127, by rfl⟩ : syracuseStep 3046013 = 1142255) (by norm_num)
theorem B1522309 : Blo 1352995 1522309 := bbase (se 4 (by rfl) ⟨142716, by rfl⟩ : syracuseStep 1522309 = 285433) (by norm_num)
theorem B2030213 : Blo 1352995 2030213 := bbase (se 4 (by rfl) ⟨190332, by rfl⟩ : syracuseStep 2030213 = 380665) (by norm_num)
theorem B4569749 : Blo 1352995 4569749 := bbase (se 6 (by rfl) ⟨107103, by rfl⟩ : syracuseStep 4569749 = 214207) (by norm_num)
theorem B2030237 : Blo 1352995 2030237 := bbase (se 3 (by rfl) ⟨380669, by rfl⟩ : syracuseStep 2030237 = 761339) (by norm_num)
theorem B1522345 : Blo 1352995 1522345 := bbase (se 2 (by rfl) ⟨570879, by rfl⟩ : syracuseStep 1522345 = 1141759) (by norm_num)
theorem B2030261 : Blo 1352995 2030261 := bbase (se 5 (by rfl) ⟨95168, by rfl⟩ : syracuseStep 2030261 = 190337) (by norm_num)
theorem B2284213 : Blo 1352995 2284213 := bbase (se 5 (by rfl) ⟨107072, by rfl⟩ : syracuseStep 2284213 = 214145) (by norm_num)
theorem B2570933 : Blo 1352995 2570933 := bbase (se 5 (by rfl) ⟨120512, by rfl⟩ : syracuseStep 2570933 = 241025) (by norm_num)
theorem B3046085 : Blo 1352995 3046085 := bbase (se 4 (by rfl) ⟨285570, by rfl⟩ : syracuseStep 3046085 = 571141) (by norm_num)
theorem B1522381 : Blo 1352995 1522381 := bbase (se 3 (by rfl) ⟨285446, by rfl⟩ : syracuseStep 1522381 = 570893) (by norm_num)
theorem B2030285 : Blo 1352995 2030285 := bbase (se 3 (by rfl) ⟨380678, by rfl⟩ : syracuseStep 2030285 = 761357) (by norm_num)
theorem B2030309 : Blo 1352995 2030309 := bbase (se 4 (by rfl) ⟨190341, by rfl⟩ : syracuseStep 2030309 = 380683) (by norm_num)
theorem B3250925 : Blo 1352995 3250925 := bbase (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) (by norm_num)
theorem B1522417 : Blo 1352995 1522417 := bbase (se 2 (by rfl) ⟨570906, by rfl⟩ : syracuseStep 1522417 = 1141813) (by norm_num)
theorem B2030333 : Blo 1352995 2030333 := bbase (se 3 (by rfl) ⟨380687, by rfl⟩ : syracuseStep 2030333 = 761375) (by norm_num)
theorem B2284301 : Blo 1352995 2284301 := bbase (se 3 (by rfl) ⟨428306, by rfl⟩ : syracuseStep 2284301 = 856613) (by norm_num)
theorem B3046157 : Blo 1352995 3046157 := bbase (se 3 (by rfl) ⟨571154, by rfl⟩ : syracuseStep 3046157 = 1142309) (by norm_num)
theorem B1522453 : Blo 1352995 1522453 := bbase (se 6 (by rfl) ⟨35682, by rfl⟩ : syracuseStep 1522453 = 71365) (by norm_num)
theorem B2030357 : Blo 1352995 2030357 := bbase (se 6 (by rfl) ⟨47586, by rfl⟩ : syracuseStep 2030357 = 95173) (by norm_num)
theorem B2030381 : Blo 1352995 2030381 := bbase (se 3 (by rfl) ⟨380696, by rfl⟩ : syracuseStep 2030381 = 761393) (by norm_num)
theorem B1391413 : Blo 1352995 1391413 := bbase (se 5 (by rfl) ⟨65222, by rfl⟩ : syracuseStep 1391413 = 130445) (by norm_num)
theorem B1522489 : Blo 1352995 1522489 := bbase (se 2 (by rfl) ⟨570933, by rfl⟩ : syracuseStep 1522489 = 1141867) (by norm_num)
theorem B2030405 : Blo 1352995 2030405 := bbase (se 4 (by rfl) ⟨190350, by rfl⟩ : syracuseStep 2030405 = 380701) (by norm_num)
theorem B2571077 : Blo 1352995 2571077 := bbase (se 4 (by rfl) ⟨241038, by rfl⟩ : syracuseStep 2571077 = 482077) (by norm_num)
theorem B3251021 : Blo 1352995 3251021 := bbase (se 3 (by rfl) ⟨609566, by rfl⟩ : syracuseStep 3251021 = 1219133) (by norm_num)
theorem B3046229 : Blo 1352995 3046229 := bbase (se 9 (by rfl) ⟨8924, by rfl⟩ : syracuseStep 3046229 = 17849) (by norm_num)
theorem B7322453 : Blo 1352995 7322453 := bbase (se 9 (by rfl) ⟨21452, by rfl⟩ : syracuseStep 7322453 = 42905) (by norm_num)
theorem B1522525 : Blo 1352995 1522525 := bbase (se 3 (by rfl) ⟨285473, by rfl⟩ : syracuseStep 1522525 = 570947) (by norm_num)
theorem B2030429 : Blo 1352995 2030429 := bbase (se 3 (by rfl) ⟨380705, by rfl⟩ : syracuseStep 2030429 = 761411) (by norm_num)
theorem B3218285 : Blo 1352995 3218285 := bbase (se 3 (by rfl) ⟨603428, by rfl⟩ : syracuseStep 3218285 = 1206857) (by norm_num)
theorem B2030453 : Blo 1352995 2030453 := bbase (se 5 (by rfl) ⟨95177, by rfl⟩ : syracuseStep 2030453 = 190355) (by norm_num)
theorem B1522561 : Blo 1352995 1522561 := bbase (se 2 (by rfl) ⟨570960, by rfl⟩ : syracuseStep 1522561 = 1141921) (by norm_num)
theorem B2030477 : Blo 1352995 2030477 := bbase (se 3 (by rfl) ⟨380714, by rfl⟩ : syracuseStep 2030477 = 761429) (by norm_num)
theorem B2284429 : Blo 1352995 2284429 := bbase (se 3 (by rfl) ⟨428330, by rfl⟩ : syracuseStep 2284429 = 856661) (by norm_num)
theorem B1465237 : Blo 1352995 1465237 := bbase (se 6 (by rfl) ⟨34341, by rfl⟩ : syracuseStep 1465237 = 68683) (by norm_num)
theorem B5143445 : Blo 1352995 5143445 := bbase (se 6 (by rfl) ⟨120549, by rfl⟩ : syracuseStep 5143445 = 241099) (by norm_num)
theorem B3046301 : Blo 1352995 3046301 := bbase (se 3 (by rfl) ⟨571181, by rfl⟩ : syracuseStep 3046301 = 1142363) (by norm_num)
theorem B2169757 : Blo 1352995 2169757 := bbase (se 3 (by rfl) ⟨406829, by rfl⟩ : syracuseStep 2169757 = 813659) (by norm_num)
theorem B1522597 : Blo 1352995 1522597 := bbase (se 4 (by rfl) ⟨142743, by rfl⟩ : syracuseStep 1522597 = 285487) (by norm_num)
theorem B2030501 : Blo 1352995 2030501 := bbase (se 4 (by rfl) ⟨190359, by rfl⟩ : syracuseStep 2030501 = 380719) (by norm_num)
theorem B2030525 : Blo 1352995 2030525 := bbase (se 3 (by rfl) ⟨380723, by rfl⟩ : syracuseStep 2030525 = 761447) (by norm_num)
theorem B1522633 : Blo 1352995 1522633 := bbase (se 2 (by rfl) ⟨570987, by rfl⟩ : syracuseStep 1522633 = 1141975) (by norm_num)
theorem B2030549 : Blo 1352995 2030549 := bbase (se 7 (by rfl) ⟨23795, by rfl⟩ : syracuseStep 2030549 = 47591) (by norm_num)
theorem B2169821 : Blo 1352995 2169821 := bbase (se 3 (by rfl) ⟨406841, by rfl⟩ : syracuseStep 2169821 = 813683) (by norm_num)
theorem B2284517 : Blo 1352995 2284517 := bbase (se 4 (by rfl) ⟨214173, by rfl⟩ : syracuseStep 2284517 = 428347) (by norm_num)
theorem B3046373 : Blo 1352995 3046373 := bbase (se 4 (by rfl) ⟨285597, by rfl⟩ : syracuseStep 3046373 = 571195) (by norm_num)
theorem B1522669 : Blo 1352995 1522669 := bbase (se 3 (by rfl) ⟨285500, by rfl⟩ : syracuseStep 1522669 = 571001) (by norm_num)
theorem B2030573 : Blo 1352995 2030573 := bbase (se 3 (by rfl) ⟨380732, by rfl⟩ : syracuseStep 2030573 = 761465) (by norm_num)
theorem B2030597 : Blo 1352995 2030597 := bbase (se 4 (by rfl) ⟨190368, by rfl⟩ : syracuseStep 2030597 = 380737) (by norm_num)
theorem B1522705 : Blo 1352995 1522705 := bbase (se 2 (by rfl) ⟨571014, by rfl⟩ : syracuseStep 1522705 = 1142029) (by norm_num)
theorem B5782549 : Blo 1352995 5782549 := bbase (se 6 (by rfl) ⟨135528, by rfl⟩ : syracuseStep 5782549 = 271057) (by norm_num)
theorem B2030621 : Blo 1352995 2030621 := bbase (se 3 (by rfl) ⟨380741, by rfl⟩ : syracuseStep 2030621 = 761483) (by norm_num)
theorem B5782565 : Blo 1352995 5782565 := bbase (se 4 (by rfl) ⟨542115, by rfl⟩ : syracuseStep 5782565 = 1084231) (by norm_num)
theorem B3046445 : Blo 1352995 3046445 := bbase (se 3 (by rfl) ⟨571208, by rfl⟩ : syracuseStep 3046445 = 1142417) (by norm_num)
theorem B1522741 : Blo 1352995 1522741 := bbase (se 5 (by rfl) ⟨71378, by rfl⟩ : syracuseStep 1522741 = 142757) (by norm_num)
theorem B2030645 : Blo 1352995 2030645 := bbase (se 5 (by rfl) ⟨95186, by rfl⟩ : syracuseStep 2030645 = 190373) (by norm_num)
theorem B2743357 : Blo 1352995 2743357 := bbase (se 3 (by rfl) ⟨514379, by rfl⟩ : syracuseStep 2743357 = 1028759) (by norm_num)
theorem B4570181 : Blo 1352995 4570181 := bbase (se 4 (by rfl) ⟨428454, by rfl⟩ : syracuseStep 4570181 = 856909) (by norm_num)
theorem B2030669 : Blo 1352995 2030669 := bbase (se 3 (by rfl) ⟨380750, by rfl⟩ : syracuseStep 2030669 = 761501) (by norm_num)
theorem B1522777 : Blo 1352995 1522777 := bbase (se 2 (by rfl) ⟨571041, by rfl⟩ : syracuseStep 1522777 = 1142083) (by norm_num)
theorem B2030693 : Blo 1352995 2030693 := bbase (se 4 (by rfl) ⟨190377, by rfl⟩ : syracuseStep 2030693 = 380755) (by norm_num)
theorem B2284645 : Blo 1352995 2284645 := bbase (se 4 (by rfl) ⟨214185, by rfl⟩ : syracuseStep 2284645 = 428371) (by norm_num)
theorem B2571365 : Blo 1352995 2571365 := bbase (se 4 (by rfl) ⟨241065, by rfl⟩ : syracuseStep 2571365 = 482131) (by norm_num)
theorem B3046517 : Blo 1352995 3046517 := bbase (se 5 (by rfl) ⟨142805, by rfl⟩ : syracuseStep 3046517 = 285611) (by norm_num)
theorem B1522813 : Blo 1352995 1522813 := bbase (se 3 (by rfl) ⟨285527, by rfl⟩ : syracuseStep 1522813 = 571055) (by norm_num)
theorem B2030717 : Blo 1352995 2030717 := bbase (se 3 (by rfl) ⟨380759, by rfl⟩ : syracuseStep 2030717 = 761519) (by norm_num)
theorem B2030741 : Blo 1352995 2030741 := bbase (se 6 (by rfl) ⟨47595, by rfl⟩ : syracuseStep 2030741 = 95191) (by norm_num)
theorem B1522849 : Blo 1352995 1522849 := bbase (se 2 (by rfl) ⟨571068, by rfl⟩ : syracuseStep 1522849 = 1142137) (by norm_num)
theorem B2030765 : Blo 1352995 2030765 := bbase (se 3 (by rfl) ⟨380768, by rfl⟩ : syracuseStep 2030765 = 761537) (by norm_num)
theorem B5143733 : Blo 1352995 5143733 := bbase (se 5 (by rfl) ⟨241112, by rfl⟩ : syracuseStep 5143733 = 482225) (by norm_num)
theorem B2284733 : Blo 1352995 2284733 := bbase (se 3 (by rfl) ⟨428387, by rfl⟩ : syracuseStep 2284733 = 856775) (by norm_num)
theorem B3046589 : Blo 1352995 3046589 := bbase (se 3 (by rfl) ⟨571235, by rfl⟩ : syracuseStep 3046589 = 1142471) (by norm_num)
theorem B1522885 : Blo 1352995 1522885 := bbase (se 4 (by rfl) ⟨142770, by rfl⟩ : syracuseStep 1522885 = 285541) (by norm_num)
theorem B2030789 : Blo 1352995 2030789 := bbase (se 4 (by rfl) ⟨190386, by rfl⟩ : syracuseStep 2030789 = 380773) (by norm_num)
theorem B2030813 : Blo 1352995 2030813 := bbase (se 3 (by rfl) ⟨380777, by rfl⟩ : syracuseStep 2030813 = 761555) (by norm_num)
theorem B1522921 : Blo 1352995 1522921 := bbase (se 2 (by rfl) ⟨571095, by rfl⟩ : syracuseStep 1522921 = 1142191) (by norm_num)
theorem B2030837 : Blo 1352995 2030837 := bbase (se 5 (by rfl) ⟨95195, by rfl⟩ : syracuseStep 2030837 = 190391) (by norm_num)
theorem B2571517 : Blo 1352995 2571517 := bbase (se 3 (by rfl) ⟨482159, by rfl⟩ : syracuseStep 2571517 = 964319) (by norm_num)
theorem B3046661 : Blo 1352995 3046661 := bbase (se 4 (by rfl) ⟨285624, by rfl⟩ : syracuseStep 3046661 = 571249) (by norm_num)
theorem B1522957 : Blo 1352995 1522957 := bbase (se 3 (by rfl) ⟨285554, by rfl⟩ : syracuseStep 1522957 = 571109) (by norm_num)
theorem B2030861 : Blo 1352995 2030861 := bbase (se 3 (by rfl) ⟨380786, by rfl⟩ : syracuseStep 2030861 = 761573) (by norm_num)
theorem B2030885 : Blo 1352995 2030885 := bbase (se 4 (by rfl) ⟨190395, by rfl⟩ : syracuseStep 2030885 = 380791) (by norm_num)
theorem B1522993 : Blo 1352995 1522993 := bbase (se 2 (by rfl) ⟨571122, by rfl⟩ : syracuseStep 1522993 = 1142245) (by norm_num)
theorem B2030909 : Blo 1352995 2030909 := bbase (se 3 (by rfl) ⟨380795, by rfl⟩ : syracuseStep 2030909 = 761591) (by norm_num)
theorem B2284861 : Blo 1352995 2284861 := bbase (se 3 (by rfl) ⟨428411, by rfl⟩ : syracuseStep 2284861 = 856823) (by norm_num)
theorem B3046733 : Blo 1352995 3046733 := bbase (se 3 (by rfl) ⟨571262, by rfl⟩ : syracuseStep 3046733 = 1142525) (by norm_num)
theorem B1523029 : Blo 1352995 1523029 := bbase (se 11 (by rfl) ⟨1115, by rfl⟩ : syracuseStep 1523029 = 2231) (by norm_num)
theorem B3087701 : Blo 1352995 3087701 := bbase (se 11 (by rfl) ⟨2261, by rfl⟩ : syracuseStep 3087701 = 4523) (by norm_num)
theorem B2030933 : Blo 1352995 2030933 := bbase (se 11 (by rfl) ⟨1487, by rfl⟩ : syracuseStep 2030933 = 2975) (by norm_num)
theorem B3661141 : Blo 1352995 3661141 := bbase (se 11 (by rfl) ⟨2681, by rfl⟩ : syracuseStep 3661141 = 5363) (by norm_num)
theorem B2030957 : Blo 1352995 2030957 := bbase (se 3 (by rfl) ⟨380804, by rfl⟩ : syracuseStep 2030957 = 761609) (by norm_num)
theorem B1523065 : Blo 1352995 1523065 := bbase (se 2 (by rfl) ⟨571149, by rfl⟩ : syracuseStep 1523065 = 1142299) (by norm_num)
theorem B2030981 : Blo 1352995 2030981 := bbase (se 4 (by rfl) ⟨190404, by rfl⟩ : syracuseStep 2030981 = 380809) (by norm_num)
theorem B2284949 : Blo 1352995 2284949 := bbase (se 6 (by rfl) ⟨53553, by rfl⟩ : syracuseStep 2284949 = 107107) (by norm_num)
theorem B3046805 : Blo 1352995 3046805 := bbase (se 6 (by rfl) ⟨71409, by rfl⟩ : syracuseStep 3046805 = 142819) (by norm_num)
theorem B3661205 : Blo 1352995 3661205 := bbase (se 6 (by rfl) ⟨85809, by rfl⟩ : syracuseStep 3661205 = 171619) (by norm_num)
theorem B1523101 : Blo 1352995 1523101 := bbase (se 3 (by rfl) ⟨285581, by rfl⟩ : syracuseStep 1523101 = 571163) (by norm_num)
theorem B2031005 : Blo 1352995 2031005 := bbase (se 3 (by rfl) ⟨380813, by rfl⟩ : syracuseStep 2031005 = 761627) (by norm_num)
theorem B1465777 : Blo 1352995 1465777 := bbase (se 2 (by rfl) ⟨549666, by rfl⟩ : syracuseStep 1465777 = 1099333) (by norm_num)
theorem B2031029 : Blo 1352995 2031029 := bbase (se 5 (by rfl) ⟨95204, by rfl⟩ : syracuseStep 2031029 = 190409) (by norm_num)
theorem B1523137 : Blo 1352995 1523137 := bbase (se 2 (by rfl) ⟨571176, by rfl⟩ : syracuseStep 1523137 = 1142353) (by norm_num)
theorem B2031053 : Blo 1352995 2031053 := bbase (se 3 (by rfl) ⟨380822, by rfl⟩ : syracuseStep 2031053 = 761645) (by norm_num)
theorem B3087829 : Blo 1352995 3087829 := bbase (se 7 (by rfl) ⟨36185, by rfl⟩ : syracuseStep 3087829 = 72371) (by norm_num)
theorem B3046877 : Blo 1352995 3046877 := bbase (se 3 (by rfl) ⟨571289, by rfl⟩ : syracuseStep 3046877 = 1142579) (by norm_num)
theorem B1736165 : Blo 1352995 1736165 := bbase (se 4 (by rfl) ⟨162765, by rfl⟩ : syracuseStep 1736165 = 325531) (by norm_num)
theorem B1523173 : Blo 1352995 1523173 := bbase (se 4 (by rfl) ⟨142797, by rfl⟩ : syracuseStep 1523173 = 285595) (by norm_num)
theorem B2031077 : Blo 1352995 2031077 := bbase (se 4 (by rfl) ⟨190413, by rfl⟩ : syracuseStep 2031077 = 380827) (by norm_num)
theorem B4570613 : Blo 1352995 4570613 := bbase (se 5 (by rfl) ⟨214247, by rfl⟩ : syracuseStep 4570613 = 428495) (by norm_num)
theorem B2031101 : Blo 1352995 2031101 := bbase (se 3 (by rfl) ⟨380831, by rfl⟩ : syracuseStep 2031101 = 761663) (by norm_num)
theorem B1523209 : Blo 1352995 1523209 := bbase (se 2 (by rfl) ⟨571203, by rfl⟩ : syracuseStep 1523209 = 1142407) (by norm_num)
theorem B2031125 : Blo 1352995 2031125 := bbase (se 6 (by rfl) ⟨47604, by rfl⟩ : syracuseStep 2031125 = 95209) (by norm_num)
theorem B2285077 : Blo 1352995 2285077 := bbase (se 6 (by rfl) ⟨53556, by rfl⟩ : syracuseStep 2285077 = 107113) (by norm_num)
theorem B3046949 : Blo 1352995 3046949 := bbase (se 4 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 3046949 = 571303) (by norm_num)
theorem B1523245 : Blo 1352995 1523245 := bbase (se 3 (by rfl) ⟨285608, by rfl⟩ : syracuseStep 1523245 = 571217) (by norm_num)
theorem B2031149 : Blo 1352995 2031149 := bbase (se 3 (by rfl) ⟨380840, by rfl⟩ : syracuseStep 2031149 = 761681) (by norm_num)
theorem B2571821 : Blo 1352995 2571821 := bbase (se 3 (by rfl) ⟨482216, by rfl⟩ : syracuseStep 2571821 = 964433) (by norm_num)
theorem B2891317 : Blo 1352995 2891317 := bbase (se 5 (by rfl) ⟨135530, by rfl⟩ : syracuseStep 2891317 = 271061) (by norm_num)
theorem B2031173 : Blo 1352995 2031173 := bbase (se 4 (by rfl) ⟨190422, by rfl⟩ : syracuseStep 2031173 = 380845) (by norm_num)
theorem B1523281 : Blo 1352995 1523281 := bbase (se 2 (by rfl) ⟨571230, by rfl⟩ : syracuseStep 1523281 = 1142461) (by norm_num)
theorem B3858005 : Blo 1352995 3858005 := bbase (se 8 (by rfl) ⟨22605, by rfl⟩ : syracuseStep 3858005 = 45211) (by norm_num)
theorem B2031197 : Blo 1352995 2031197 := bbase (se 3 (by rfl) ⟨380849, by rfl⟩ : syracuseStep 2031197 = 761699) (by norm_num)
theorem B2285165 : Blo 1352995 2285165 := bbase (se 3 (by rfl) ⟨428468, by rfl⟩ : syracuseStep 2285165 = 856937) (by norm_num)
theorem B3047021 : Blo 1352995 3047021 := bbase (se 3 (by rfl) ⟨571316, by rfl⟩ : syracuseStep 3047021 = 1142633) (by norm_num)
theorem B1523317 : Blo 1352995 1523317 := bbase (se 5 (by rfl) ⟨71405, by rfl⟩ : syracuseStep 1523317 = 142811) (by norm_num)
theorem B2031221 : Blo 1352995 2031221 := bbase (se 5 (by rfl) ⟨95213, by rfl⟩ : syracuseStep 2031221 = 190427) (by norm_num)
theorem B6856325 : Blo 1352995 6856325 := bbase (se 4 (by rfl) ⟨642780, by rfl⟩ : syracuseStep 6856325 = 1285561) (by norm_num)
theorem B2031245 : Blo 1352995 2031245 := bbase (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) (by norm_num)
theorem B1523353 : Blo 1352995 1523353 := bbase (se 2 (by rfl) ⟨571257, by rfl⟩ : syracuseStep 1523353 = 1142515) (by norm_num)
theorem B2031269 : Blo 1352995 2031269 := bbase (se 4 (by rfl) ⟨190431, by rfl⟩ : syracuseStep 2031269 = 380863) (by norm_num)
theorem B3047093 : Blo 1352995 3047093 := bbase (se 5 (by rfl) ⟨142832, by rfl⟩ : syracuseStep 3047093 = 285665) (by norm_num)
theorem B1523389 : Blo 1352995 1523389 := bbase (se 3 (by rfl) ⟨285635, by rfl⟩ : syracuseStep 1523389 = 571271) (by norm_num)
theorem B2031293 : Blo 1352995 2031293 := bbase (se 3 (by rfl) ⟨380867, by rfl⟩ : syracuseStep 2031293 = 761735) (by norm_num)
theorem B2031317 : Blo 1352995 2031317 := bbase (se 7 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 2031317 = 47609) (by norm_num)
theorem B1523425 : Blo 1352995 1523425 := bbase (se 2 (by rfl) ⟨571284, by rfl⟩ : syracuseStep 1523425 = 1142569) (by norm_num)
theorem B2031341 : Blo 1352995 2031341 := bbase (se 3 (by rfl) ⟨380876, by rfl⟩ : syracuseStep 2031341 = 761753) (by norm_num)
theorem B2285293 : Blo 1352995 2285293 := bbase (se 3 (by rfl) ⟨428492, by rfl⟩ : syracuseStep 2285293 = 856985) (by norm_num)
theorem B3047165 : Blo 1352995 3047165 := bbase (se 3 (by rfl) ⟨571343, by rfl⟩ : syracuseStep 3047165 = 1142687) (by norm_num)
theorem B1523461 : Blo 1352995 1523461 := bbase (se 4 (by rfl) ⟨142824, by rfl⟩ : syracuseStep 1523461 = 285649) (by norm_num)
theorem B2031365 : Blo 1352995 2031365 := bbase (se 4 (by rfl) ⟨190440, by rfl⟩ : syracuseStep 2031365 = 380881) (by norm_num)
theorem B6176533 : Blo 1352995 6176533 := bbase (se 6 (by rfl) ⟨144762, by rfl⟩ : syracuseStep 6176533 = 289525) (by norm_num)
theorem B2031389 : Blo 1352995 2031389 := bbase (se 3 (by rfl) ⟨380885, by rfl⟩ : syracuseStep 2031389 = 761771) (by norm_num)
theorem B1523497 : Blo 1352995 1523497 := bbase (se 2 (by rfl) ⟨571311, by rfl⟩ : syracuseStep 1523497 = 1142623) (by norm_num)
theorem B2031413 : Blo 1352995 2031413 := bbase (se 5 (by rfl) ⟨95222, by rfl⟩ : syracuseStep 2031413 = 190445) (by norm_num)
theorem B2285381 : Blo 1352995 2285381 := bbase (se 4 (by rfl) ⟨214254, by rfl⟩ : syracuseStep 2285381 = 428509) (by norm_num)
theorem B3047237 : Blo 1352995 3047237 := bbase (se 4 (by rfl) ⟨285678, by rfl⟩ : syracuseStep 3047237 = 571357) (by norm_num)
theorem B1523533 : Blo 1352995 1523533 := bbase (se 3 (by rfl) ⟨285662, by rfl⟩ : syracuseStep 1523533 = 571325) (by norm_num)
theorem B2031437 : Blo 1352995 2031437 := bbase (se 3 (by rfl) ⟨380894, by rfl⟩ : syracuseStep 2031437 = 761789) (by norm_num)
theorem B2031461 : Blo 1352995 2031461 := bbase (se 4 (by rfl) ⟨190449, by rfl⟩ : syracuseStep 2031461 = 380899) (by norm_num)
theorem B1523569 : Blo 1352995 1523569 := bbase (se 2 (by rfl) ⟨571338, by rfl⟩ : syracuseStep 1523569 = 1142677) (by norm_num)
theorem B2031485 : Blo 1352995 2031485 := bbase (se 3 (by rfl) ⟨380903, by rfl⟩ : syracuseStep 2031485 = 761807) (by norm_num)
theorem B3047309 : Blo 1352995 3047309 := bbase (se 3 (by rfl) ⟨571370, by rfl⟩ : syracuseStep 3047309 = 1142741) (by norm_num)
theorem B1523605 : Blo 1352995 1523605 := bbase (se 6 (by rfl) ⟨35709, by rfl⟩ : syracuseStep 1523605 = 71419) (by norm_num)
theorem B2031509 : Blo 1352995 2031509 := bbase (se 6 (by rfl) ⟨47613, by rfl⟩ : syracuseStep 2031509 = 95227) (by norm_num)
theorem B4571045 : Blo 1352995 4571045 := bbase (se 4 (by rfl) ⟨428535, by rfl⟩ : syracuseStep 4571045 = 857071) (by norm_num)
theorem B2891693 : Blo 1352995 2891693 := bbase (se 3 (by rfl) ⟨542192, by rfl⟩ : syracuseStep 2891693 = 1084385) (by norm_num)
theorem B2031533 : Blo 1352995 2031533 := bbase (se 3 (by rfl) ⟨380912, by rfl⟩ : syracuseStep 2031533 = 761825) (by norm_num)
theorem B1523641 : Blo 1352995 1523641 := bbase (se 2 (by rfl) ⟨571365, by rfl⟩ : syracuseStep 1523641 = 1142731) (by norm_num)
theorem B2031557 : Blo 1352995 2031557 := bbase (se 4 (by rfl) ⟨190458, by rfl⟩ : syracuseStep 2031557 = 380917) (by norm_num)
theorem B2285509 : Blo 1352995 2285509 := bbase (se 4 (by rfl) ⟨214266, by rfl⟩ : syracuseStep 2285509 = 428533) (by norm_num)
theorem B3047381 : Blo 1352995 3047381 := bbase (se 7 (by rfl) ⟨35711, by rfl⟩ : syracuseStep 3047381 = 71423) (by norm_num)
theorem B1523677 : Blo 1352995 1523677 := bbase (se 3 (by rfl) ⟨285689, by rfl⟩ : syracuseStep 1523677 = 571379) (by norm_num)
theorem B2031581 : Blo 1352995 2031581 := bbase (se 3 (by rfl) ⟨380921, by rfl⟩ : syracuseStep 2031581 = 761843) (by norm_num)
theorem B2228197 : Blo 1352995 2228197 := bbase (se 4 (by rfl) ⟨208893, by rfl⟩ : syracuseStep 2228197 = 417787) (by norm_num)
theorem B2031605 : Blo 1352995 2031605 := bbase (se 5 (by rfl) ⟨95231, by rfl⟩ : syracuseStep 2031605 = 190463) (by norm_num)
theorem B2031617 : Blo 1352995 2031617 := bstep (se 2 (by rfl) ⟨761856, by rfl⟩ : syracuseStep 2031617 = 1523713) B1523713
theorem B4571153 : Blo 1352995 4571153 := bstep (se 2 (by rfl) ⟨1714182, by rfl⟩ : syracuseStep 4571153 = 3428365) B3428365
theorem B2031635 : Blo 1352995 2031635 := bstep (se 1 (by rfl) ⟨1523726, by rfl⟩ : syracuseStep 2031635 = 3047453) B3047453
theorem B1523731 : Blo 1352995 1523731 := bstep (se 1 (by rfl) ⟨1142798, by rfl⟩ : syracuseStep 1523731 = 2285597) B2285597
theorem B2285617 : Blo 1352995 2285617 := bstep (se 2 (by rfl) ⟨857106, by rfl⟩ : syracuseStep 2285617 = 1714213) B1714213
theorem B2031665 : Blo 1352995 2031665 := bstep (se 2 (by rfl) ⟨761874, by rfl⟩ : syracuseStep 2031665 = 1523749) B1523749
theorem B2572337 : Blo 1352995 2572337 := bstep (se 2 (by rfl) ⟨964626, by rfl⟩ : syracuseStep 2572337 = 1929253) B1929253
theorem B2031683 : Blo 1352995 2031683 := bstep (se 1 (by rfl) ⟨1523762, by rfl⟩ : syracuseStep 2031683 = 3047525) B3047525
theorem B2285651 : Blo 1352995 2285651 := bstep (se 1 (by rfl) ⟨1714238, by rfl⟩ : syracuseStep 2285651 = 3428477) B3428477
theorem B2031713 : Blo 1352995 2031713 := bstep (se 2 (by rfl) ⟨761892, by rfl⟩ : syracuseStep 2031713 = 1523785) B1523785
theorem B2031731 : Blo 1352995 2031731 := bstep (se 1 (by rfl) ⟨1523798, by rfl⟩ : syracuseStep 2031731 = 3047597) B3047597
theorem B2031761 : Blo 1352995 2031761 := bstep (se 2 (by rfl) ⟨761910, by rfl⟩ : syracuseStep 2031761 = 1523821) B1523821
theorem B2031779 : Blo 1352995 2031779 := bstep (se 1 (by rfl) ⟨1523834, by rfl⟩ : syracuseStep 2031779 = 3047669) B3047669
theorem B1523875 : Blo 1352995 1523875 := bstep (se 1 (by rfl) ⟨1142906, by rfl⟩ : syracuseStep 1523875 = 2285813) B2285813
theorem B4399267 : Blo 1352995 4399267 := bstep (se 1 (by rfl) ⟨3299450, by rfl⟩ : syracuseStep 4399267 = 6598901) B6598901
theorem B2031809 : Blo 1352995 2031809 := bstep (se 2 (by rfl) ⟨761928, by rfl⟩ : syracuseStep 2031809 = 1523857) B1523857
theorem B8790221 : Blo 1352995 8790221 := bstep (se 3 (by rfl) ⟨1648166, by rfl⟩ : syracuseStep 8790221 = 3296333) B3296333
theorem B3047633 : Blo 1352995 3047633 := bstep (se 2 (by rfl) ⟨1142862, by rfl⟩ : syracuseStep 3047633 = 2285725) B2285725
theorem B2285779 : Blo 1352995 2285779 := bstep (se 1 (by rfl) ⟨1714334, by rfl⟩ : syracuseStep 2285779 = 3428669) B3428669
theorem B2031827 : Blo 1352995 2031827 := bstep (se 1 (by rfl) ⟨1523870, by rfl⟩ : syracuseStep 2031827 = 3047741) B3047741
theorem B3047651 : Blo 1352995 3047651 := bstep (se 1 (by rfl) ⟨2285738, by rfl⟩ : syracuseStep 3047651 = 4571477) B4571477
theorem B2031857 : Blo 1352995 2031857 := bstep (se 2 (by rfl) ⟨761946, by rfl⟩ : syracuseStep 2031857 = 1523893) B1523893
theorem B2031875 : Blo 1352995 2031875 := bstep (se 1 (by rfl) ⟨1523906, by rfl⟩ : syracuseStep 2031875 = 3047813) B3047813
theorem B6856973 : Blo 1352995 6856973 := bstep (se 3 (by rfl) ⟨1285682, by rfl⟩ : syracuseStep 6856973 = 2571365) B2571365
theorem B2031905 : Blo 1352995 2031905 := bstep (se 2 (by rfl) ⟨761964, by rfl⟩ : syracuseStep 2031905 = 1523929) B1523929
theorem B2031923 : Blo 1352995 2031923 := bstep (se 1 (by rfl) ⟨1523942, by rfl⟩ : syracuseStep 2031923 = 3047885) B3047885
theorem B1524019 : Blo 1352995 1524019 := bstep (se 1 (by rfl) ⟨1143014, by rfl⟩ : syracuseStep 1524019 = 2286029) B2286029
theorem B2031953 : Blo 1352995 2031953 := bstep (se 2 (by rfl) ⟨761982, by rfl⟩ : syracuseStep 2031953 = 1523965) B1523965
theorem B2285921 : Blo 1352995 2285921 := bstep (se 2 (by rfl) ⟨857220, by rfl⟩ : syracuseStep 2285921 = 1714441) B1714441
theorem B2031971 : Blo 1352995 2031971 := bstep (se 1 (by rfl) ⟨1523978, by rfl⟩ : syracuseStep 2031971 = 3047957) B3047957
theorem B10281329 : Blo 1352995 10281329 := bstep (se 2 (by rfl) ⟨3855498, by rfl⟩ : syracuseStep 10281329 = 7710997) B7710997
theorem B2032001 : Blo 1352995 2032001 := bstep (se 2 (by rfl) ⟨762000, by rfl⟩ : syracuseStep 2032001 = 1524001) B1524001
theorem B2032019 : Blo 1352995 2032019 := bstep (se 1 (by rfl) ⟨1524014, by rfl⟩ : syracuseStep 2032019 = 3048029) B3048029
theorem B8675747 : Blo 1352995 8675747 := bstep (se 1 (by rfl) ⟨6506810, by rfl⟩ : syracuseStep 8675747 = 13013621) B13013621
theorem B2032049 : Blo 1352995 2032049 := bstep (se 2 (by rfl) ⟨762018, by rfl⟩ : syracuseStep 2032049 = 1524037) B1524037
theorem B2032067 : Blo 1352995 2032067 := bstep (se 1 (by rfl) ⟨1524050, by rfl⟩ : syracuseStep 2032067 = 3048101) B3048101
theorem B1524163 : Blo 1352995 1524163 := bstep (se 1 (by rfl) ⟨1143122, by rfl⟩ : syracuseStep 1524163 = 2286245) B2286245
theorem B2286049 : Blo 1352995 2286049 := bstep (se 2 (by rfl) ⟨857268, by rfl⟩ : syracuseStep 2286049 = 1714537) B1714537
theorem B2032097 : Blo 1352995 2032097 := bstep (se 2 (by rfl) ⟨762036, by rfl⟩ : syracuseStep 2032097 = 1524073) B1524073
theorem B3047921 : Blo 1352995 3047921 := bstep (se 2 (by rfl) ⟨1142970, by rfl⟩ : syracuseStep 3047921 = 2285941) B2285941
theorem B2032115 : Blo 1352995 2032115 := bstep (se 1 (by rfl) ⟨1524086, by rfl⟩ : syracuseStep 2032115 = 3048173) B3048173
theorem B3047939 : Blo 1352995 3047939 := bstep (se 1 (by rfl) ⟨2285954, by rfl⟩ : syracuseStep 3047939 = 4571909) B4571909
theorem B2286083 : Blo 1352995 2286083 := bstep (se 1 (by rfl) ⟨1714562, by rfl⟩ : syracuseStep 2286083 = 3429125) B3429125
theorem B5489165 : Blo 1352995 5489165 := bstep (se 3 (by rfl) ⟨1029218, by rfl⟩ : syracuseStep 5489165 = 2058437) B2058437
theorem B1712659 : Blo 1352995 1712659 := bstep (se 1 (by rfl) ⟨1284494, by rfl⟩ : syracuseStep 1712659 = 2568989) B2568989
theorem B2032145 : Blo 1352995 2032145 := bstep (se 2 (by rfl) ⟨762054, by rfl⟩ : syracuseStep 2032145 = 1524109) B1524109
theorem B2744867 : Blo 1352995 2744867 := bstep (se 1 (by rfl) ⟨2058650, by rfl⟩ : syracuseStep 2744867 = 4117301) B4117301
theorem B2032163 : Blo 1352995 2032163 := bstep (se 1 (by rfl) ⟨1524122, by rfl⟩ : syracuseStep 2032163 = 3048245) B3048245
theorem B4571693 : Blo 1352995 4571693 := bstep (se 3 (by rfl) ⟨857192, by rfl⟩ : syracuseStep 4571693 = 1714385) B1714385
theorem B2032193 : Blo 1352995 2032193 := bstep (se 2 (by rfl) ⟨762072, by rfl⟩ : syracuseStep 2032193 = 1524145) B1524145
theorem B3662417 : Blo 1352995 3662417 := bstep (se 2 (by rfl) ⟨1373406, by rfl⟩ : syracuseStep 3662417 = 2746813) B2746813
theorem B2032211 : Blo 1352995 2032211 := bstep (se 1 (by rfl) ⟨1524158, by rfl⟩ : syracuseStep 2032211 = 3048317) B3048317
theorem B1524307 : Blo 1352995 1524307 := bstep (se 1 (by rfl) ⟨1143230, by rfl⟩ : syracuseStep 1524307 = 2286461) B2286461
theorem B4571747 : Blo 1352995 4571747 := bstep (se 1 (by rfl) ⟨3428810, by rfl⟩ : syracuseStep 4571747 = 6857621) B6857621
theorem B2032241 : Blo 1352995 2032241 := bstep (se 2 (by rfl) ⟨762090, by rfl⟩ : syracuseStep 2032241 = 1524181) B1524181
theorem B1712755 : Blo 1352995 1712755 := bstep (se 1 (by rfl) ⟨1284566, by rfl⟩ : syracuseStep 1712755 = 2569133) B2569133
theorem B2286211 : Blo 1352995 2286211 := bstep (se 1 (by rfl) ⟨1714658, by rfl⟩ : syracuseStep 2286211 = 3429317) B3429317
theorem B2032259 : Blo 1352995 2032259 := bstep (se 1 (by rfl) ⟨1524194, by rfl⟩ : syracuseStep 2032259 = 3048389) B3048389
theorem B5784205 : Blo 1352995 5784205 := bstep (se 3 (by rfl) ⟨1084538, by rfl⟩ : syracuseStep 5784205 = 2169077) B2169077
theorem B3424913 : Blo 1352995 3424913 := bstep (se 2 (by rfl) ⟨1284342, by rfl⟩ : syracuseStep 3424913 = 2568685) B2568685
theorem B2032289 : Blo 1352995 2032289 := bstep (se 2 (by rfl) ⟨762108, by rfl⟩ : syracuseStep 2032289 = 1524217) B1524217
theorem B2032307 : Blo 1352995 2032307 := bstep (se 1 (by rfl) ⟨1524230, by rfl⟩ : syracuseStep 2032307 = 3048461) B3048461
theorem B3424963 : Blo 1352995 3424963 := bstep (se 1 (by rfl) ⟨2568722, by rfl⟩ : syracuseStep 3424963 = 5137445) B5137445
theorem B2032337 : Blo 1352995 2032337 := bstep (se 2 (by rfl) ⟨762126, by rfl⟩ : syracuseStep 2032337 = 1524253) B1524253
theorem B2032355 : Blo 1352995 2032355 := bstep (se 1 (by rfl) ⟨1524266, by rfl⟩ : syracuseStep 2032355 = 3048533) B3048533
theorem B14836465 : Blo 1352995 14836465 := bstep (se 2 (by rfl) ⟨5563674, by rfl⟩ : syracuseStep 14836465 = 11127349) B11127349
theorem B2032385 : Blo 1352995 2032385 := bstep (se 2 (by rfl) ⟨762144, by rfl⟩ : syracuseStep 2032385 = 1524289) B1524289
theorem B2892547 : Blo 1352995 2892547 := bstep (se 1 (by rfl) ⟨2169410, by rfl⟩ : syracuseStep 2892547 = 4338821) B4338821
theorem B3048209 : Blo 1352995 3048209 := bstep (se 2 (by rfl) ⟨1143078, by rfl⟩ : syracuseStep 3048209 = 2286157) B2286157
theorem B2286353 : Blo 1352995 2286353 := bstep (se 2 (by rfl) ⟨857382, by rfl⟩ : syracuseStep 2286353 = 1714765) B1714765
theorem B2032403 : Blo 1352995 2032403 := bstep (se 1 (by rfl) ⟨1524302, by rfl⟩ : syracuseStep 2032403 = 3048605) B3048605
theorem B3048227 : Blo 1352995 3048227 := bstep (se 1 (by rfl) ⟨2286170, by rfl⟩ : syracuseStep 3048227 = 4572341) B4572341
theorem B2032433 : Blo 1352995 2032433 := bstep (se 2 (by rfl) ⟨762162, by rfl⟩ : syracuseStep 2032433 = 1524325) B1524325
theorem B2032451 : Blo 1352995 2032451 := bstep (se 1 (by rfl) ⟨1524338, by rfl⟩ : syracuseStep 2032451 = 3048677) B3048677
theorem B3425105 : Blo 1352995 3425105 := bstep (se 2 (by rfl) ⟨1284414, by rfl⟩ : syracuseStep 3425105 = 2568829) B2568829
theorem B2032481 : Blo 1352995 2032481 := bstep (se 2 (by rfl) ⟨762180, by rfl⟩ : syracuseStep 2032481 = 1524361) B1524361
theorem B7709539 : Blo 1352995 7709539 := bstep (se 1 (by rfl) ⟨5782154, by rfl⟩ : syracuseStep 7709539 = 11564309) B11564309
theorem B4572017 : Blo 1352995 4572017 := bstep (se 2 (by rfl) ⟨1714506, by rfl⟩ : syracuseStep 4572017 = 3429013) B3429013
theorem B2286481 : Blo 1352995 2286481 := bstep (se 2 (by rfl) ⟨857430, by rfl⟩ : syracuseStep 2286481 = 1714861) B1714861
theorem B2286515 : Blo 1352995 2286515 := bstep (se 1 (by rfl) ⟨1714886, by rfl⟩ : syracuseStep 2286515 = 3429773) B3429773
theorem B5784547 : Blo 1352995 5784547 := bstep (se 1 (by rfl) ⟨4338410, by rfl⟩ : syracuseStep 5784547 = 8676821) B8676821
theorem B3048497 : Blo 1352995 3048497 := bstep (se 2 (by rfl) ⟨1143186, by rfl⟩ : syracuseStep 3048497 = 2286373) B2286373
theorem B3048515 : Blo 1352995 3048515 := bstep (se 1 (by rfl) ⟨2286386, by rfl⟩ : syracuseStep 3048515 = 4572773) B4572773
theorem B1713251 : Blo 1352995 1713251 := bstep (se 1 (by rfl) ⟨1284938, by rfl⟩ : syracuseStep 1713251 = 2569877) B2569877
theorem B5137613 : Blo 1352995 5137613 := bstep (se 3 (by rfl) ⟨963302, by rfl⟩ : syracuseStep 5137613 = 1926605) B1926605
theorem B2893009 : Blo 1352995 2893009 := bstep (se 2 (by rfl) ⟨1084878, by rfl⟩ : syracuseStep 2893009 = 2169757) B2169757
theorem B4629773 : Blo 1352995 4629773 := bstep (se 3 (by rfl) ⟨868082, by rfl⟩ : syracuseStep 4629773 = 1736165) B1736165
theorem B1352995 : Blo 1352995 1352995 := bstep (se 1 (by rfl) ⟨1014746, by rfl⟩ : syracuseStep 1352995 = 2029493) B2029493
theorem B1926451 : Blo 1352995 1926451 := bstep (se 1 (by rfl) ⟨1444838, by rfl⟩ : syracuseStep 1926451 = 2889677) B2889677
theorem B1353011 : Blo 1352995 1353011 := bstep (se 1 (by rfl) ⟨1014758, by rfl⟩ : syracuseStep 1353011 = 2029517) B2029517
theorem B1353027 : Blo 1352995 1353027 := bstep (se 1 (by rfl) ⟨1014770, by rfl⟩ : syracuseStep 1353027 = 2029541) B2029541
theorem B1353043 : Blo 1352995 1353043 := bstep (se 1 (by rfl) ⟨1014782, by rfl⟩ : syracuseStep 1353043 = 2029565) B2029565
theorem B1353059 : Blo 1352995 1353059 := bstep (se 1 (by rfl) ⟨1014794, by rfl⟩ : syracuseStep 1353059 = 2029589) B2029589
theorem B7710065 : Blo 1352995 7710065 := bstep (se 2 (by rfl) ⟨2891274, by rfl⟩ : syracuseStep 7710065 = 5782549) B5782549
theorem B1353075 : Blo 1352995 1353075 := bstep (se 1 (by rfl) ⟨1014806, by rfl⟩ : syracuseStep 1353075 = 2029613) B2029613
theorem B1353091 : Blo 1352995 1353091 := bstep (se 1 (by rfl) ⟨1014818, by rfl⟩ : syracuseStep 1353091 = 2029637) B2029637
theorem B4572557 : Blo 1352995 4572557 := bstep (se 3 (by rfl) ⟨857354, by rfl⟩ : syracuseStep 4572557 = 1714709) B1714709
theorem B1353107 : Blo 1352995 1353107 := bstep (se 1 (by rfl) ⟨1014830, by rfl⟩ : syracuseStep 1353107 = 2029661) B2029661
theorem B1353123 : Blo 1352995 1353123 := bstep (se 1 (by rfl) ⟨1014842, by rfl⟩ : syracuseStep 1353123 = 2029685) B2029685
theorem B1353139 : Blo 1352995 1353139 := bstep (se 1 (by rfl) ⟨1014854, by rfl⟩ : syracuseStep 1353139 = 2029709) B2029709
theorem B1353155 : Blo 1352995 1353155 := bstep (se 1 (by rfl) ⟨1014866, by rfl⟩ : syracuseStep 1353155 = 2029733) B2029733
theorem B4572611 : Blo 1352995 4572611 := bstep (se 1 (by rfl) ⟨3429458, by rfl⟩ : syracuseStep 4572611 = 6858917) B6858917
theorem B1353171 : Blo 1352995 1353171 := bstep (se 1 (by rfl) ⟨1014878, by rfl⟩ : syracuseStep 1353171 = 2029757) B2029757
theorem B1353187 : Blo 1352995 1353187 := bstep (se 1 (by rfl) ⟨1014890, by rfl⟩ : syracuseStep 1353187 = 2029781) B2029781
theorem B1353203 : Blo 1352995 1353203 := bstep (se 1 (by rfl) ⟨1014902, by rfl⟩ : syracuseStep 1353203 = 2029805) B2029805
theorem B1353219 : Blo 1352995 1353219 := bstep (se 1 (by rfl) ⟨1014914, by rfl⟩ : syracuseStep 1353219 = 2029829) B2029829
theorem B1353235 : Blo 1352995 1353235 := bstep (se 1 (by rfl) ⟨1014926, by rfl⟩ : syracuseStep 1353235 = 2029853) B2029853
theorem B1353251 : Blo 1352995 1353251 := bstep (se 1 (by rfl) ⟨1014938, by rfl⟩ : syracuseStep 1353251 = 2029877) B2029877
theorem B1353267 : Blo 1352995 1353267 := bstep (se 1 (by rfl) ⟨1014950, by rfl⟩ : syracuseStep 1353267 = 2029901) B2029901
theorem B4171331 : Blo 1352995 4171331 := bstep (se 1 (by rfl) ⟨3128498, by rfl⟩ : syracuseStep 4171331 = 6256997) B6256997
theorem B1353283 : Blo 1352995 1353283 := bstep (se 1 (by rfl) ⟨1014962, by rfl⟩ : syracuseStep 1353283 = 2029925) B2029925
theorem B1353299 : Blo 1352995 1353299 := bstep (se 1 (by rfl) ⟨1014974, by rfl⟩ : syracuseStep 1353299 = 2029949) B2029949
theorem B1353315 : Blo 1352995 1353315 := bstep (se 1 (by rfl) ⟨1014986, by rfl⟩ : syracuseStep 1353315 = 2029973) B2029973
theorem B1353331 : Blo 1352995 1353331 := bstep (se 1 (by rfl) ⟨1014998, by rfl⟩ : syracuseStep 1353331 = 2029997) B2029997
theorem B1353347 : Blo 1352995 1353347 := bstep (se 1 (by rfl) ⟨1015010, by rfl⟩ : syracuseStep 1353347 = 2030021) B2030021
theorem B1353363 : Blo 1352995 1353363 := bstep (se 1 (by rfl) ⟨1015022, by rfl⟩ : syracuseStep 1353363 = 2030045) B2030045
theorem B1353379 : Blo 1352995 1353379 := bstep (se 1 (by rfl) ⟨1015034, by rfl⟩ : syracuseStep 1353379 = 2030069) B2030069
theorem B1353395 : Blo 1352995 1353395 := bstep (se 1 (by rfl) ⟨1015046, by rfl⟩ : syracuseStep 1353395 = 2030093) B2030093
theorem B1353411 : Blo 1352995 1353411 := bstep (se 1 (by rfl) ⟨1015058, by rfl⟩ : syracuseStep 1353411 = 2030117) B2030117
theorem B4572881 : Blo 1352995 4572881 := bstep (se 2 (by rfl) ⟨1714830, by rfl⟩ : syracuseStep 4572881 = 3429661) B3429661
theorem B1353427 : Blo 1352995 1353427 := bstep (se 1 (by rfl) ⟨1015070, by rfl⟩ : syracuseStep 1353427 = 2030141) B2030141
theorem B1353443 : Blo 1352995 1353443 := bstep (se 1 (by rfl) ⟨1015082, by rfl⟩ : syracuseStep 1353443 = 2030165) B2030165
theorem B8234723 : Blo 1352995 8234723 := bstep (se 1 (by rfl) ⟨6176042, by rfl⟩ : syracuseStep 8234723 = 12352085) B12352085
theorem B1353459 : Blo 1352995 1353459 := bstep (se 1 (by rfl) ⟨1015094, by rfl⟩ : syracuseStep 1353459 = 2030189) B2030189
theorem B1353475 : Blo 1352995 1353475 := bstep (se 1 (by rfl) ⟨1015106, by rfl⟩ : syracuseStep 1353475 = 2030213) B2030213
theorem B1353491 : Blo 1352995 1353491 := bstep (se 1 (by rfl) ⟨1015118, by rfl⟩ : syracuseStep 1353491 = 2030237) B2030237
theorem B1353507 : Blo 1352995 1353507 := bstep (se 1 (by rfl) ⟨1015130, by rfl⟩ : syracuseStep 1353507 = 2030261) B2030261
theorem B1713955 : Blo 1352995 1713955 := bstep (se 1 (by rfl) ⟨1285466, by rfl⟩ : syracuseStep 1713955 = 2570933) B2570933
theorem B1828657 : Blo 1352995 1828657 := bstep (se 2 (by rfl) ⟨685746, by rfl⟩ : syracuseStep 1828657 = 1371493) B1371493
theorem B3426097 : Blo 1352995 3426097 := bstep (se 2 (by rfl) ⟨1284786, by rfl⟩ : syracuseStep 3426097 = 2569573) B2569573
theorem B1353523 : Blo 1352995 1353523 := bstep (se 1 (by rfl) ⟨1015142, by rfl⟩ : syracuseStep 1353523 = 2030285) B2030285
theorem B9266993 : Blo 1352995 9266993 := bstep (se 2 (by rfl) ⟨3475122, by rfl⟩ : syracuseStep 9266993 = 6950245) B6950245
theorem B1353539 : Blo 1352995 1353539 := bstep (se 1 (by rfl) ⟨1015154, by rfl⟩ : syracuseStep 1353539 = 2030309) B2030309
theorem B1353555 : Blo 1352995 1353555 := bstep (se 1 (by rfl) ⟨1015166, by rfl⟩ : syracuseStep 1353555 = 2030333) B2030333
theorem B1353571 : Blo 1352995 1353571 := bstep (se 1 (by rfl) ⟨1015178, by rfl⟩ : syracuseStep 1353571 = 2030357) B2030357
theorem B1353587 : Blo 1352995 1353587 := bstep (se 1 (by rfl) ⟨1015190, by rfl⟩ : syracuseStep 1353587 = 2030381) B2030381
theorem B1353603 : Blo 1352995 1353603 := bstep (se 1 (by rfl) ⟨1015202, by rfl⟩ : syracuseStep 1353603 = 2030405) B2030405
theorem B1714051 : Blo 1352995 1714051 := bstep (se 1 (by rfl) ⟨1285538, by rfl⟩ : syracuseStep 1714051 = 2571077) B2571077
theorem B1353619 : Blo 1352995 1353619 := bstep (se 1 (by rfl) ⟨1015214, by rfl⟩ : syracuseStep 1353619 = 2030429) B2030429
theorem B1353635 : Blo 1352995 1353635 := bstep (se 1 (by rfl) ⟨1015226, by rfl⟩ : syracuseStep 1353635 = 2030453) B2030453
theorem B1353651 : Blo 1352995 1353651 := bstep (se 1 (by rfl) ⟨1015238, by rfl⟩ : syracuseStep 1353651 = 2030477) B2030477
theorem B1353667 : Blo 1352995 1353667 := bstep (se 1 (by rfl) ⟨1015250, by rfl⟩ : syracuseStep 1353667 = 2030501) B2030501
theorem B1353683 : Blo 1352995 1353683 := bstep (se 1 (by rfl) ⟨1015262, by rfl⟩ : syracuseStep 1353683 = 2030525) B2030525
theorem B1353699 : Blo 1352995 1353699 := bstep (se 1 (by rfl) ⟨1015274, by rfl⟩ : syracuseStep 1353699 = 2030549) B2030549
theorem B5138417 : Blo 1352995 5138417 := bstep (se 2 (by rfl) ⟨1926906, by rfl⟩ : syracuseStep 5138417 = 3853813) B3853813
theorem B1353715 : Blo 1352995 1353715 := bstep (se 1 (by rfl) ⟨1015286, by rfl⟩ : syracuseStep 1353715 = 2030573) B2030573
theorem B1353731 : Blo 1352995 1353731 := bstep (se 1 (by rfl) ⟨1015298, by rfl⟩ : syracuseStep 1353731 = 2030597) B2030597
theorem B1353747 : Blo 1352995 1353747 := bstep (se 1 (by rfl) ⟨1015310, by rfl⟩ : syracuseStep 1353747 = 2030621) B2030621
theorem B1353763 : Blo 1352995 1353763 := bstep (se 1 (by rfl) ⟨1015322, by rfl⟩ : syracuseStep 1353763 = 2030645) B2030645
theorem B1353779 : Blo 1352995 1353779 := bstep (se 1 (by rfl) ⟨1015334, by rfl⟩ : syracuseStep 1353779 = 2030669) B2030669
theorem B3426371 : Blo 1352995 3426371 := bstep (se 1 (by rfl) ⟨2569778, by rfl⟩ : syracuseStep 3426371 = 5139557) B5139557
theorem B1353795 : Blo 1352995 1353795 := bstep (se 1 (by rfl) ⟨1015346, by rfl⟩ : syracuseStep 1353795 = 2030693) B2030693
theorem B1353811 : Blo 1352995 1353811 := bstep (se 1 (by rfl) ⟨1015358, by rfl⟩ : syracuseStep 1353811 = 2030717) B2030717
theorem B1353827 : Blo 1352995 1353827 := bstep (se 1 (by rfl) ⟨1015370, by rfl⟩ : syracuseStep 1353827 = 2030741) B2030741
theorem B2607203 : Blo 1352995 2607203 := bstep (se 1 (by rfl) ⟨1955402, by rfl⟩ : syracuseStep 2607203 = 3910805) B3910805
theorem B1353843 : Blo 1352995 1353843 := bstep (se 1 (by rfl) ⟨1015382, by rfl⟩ : syracuseStep 1353843 = 2030765) B2030765
theorem B1353859 : Blo 1352995 1353859 := bstep (se 1 (by rfl) ⟨1015394, by rfl⟩ : syracuseStep 1353859 = 2030789) B2030789
theorem B9889933 : Blo 1352995 9889933 := bstep (se 3 (by rfl) ⟨1854362, by rfl⟩ : syracuseStep 9889933 = 3708725) B3708725
theorem B1353875 : Blo 1352995 1353875 := bstep (se 1 (by rfl) ⟨1015406, by rfl⟩ : syracuseStep 1353875 = 2030813) B2030813
theorem B1353891 : Blo 1352995 1353891 := bstep (se 1 (by rfl) ⟨1015418, by rfl⟩ : syracuseStep 1353891 = 2030837) B2030837
theorem B1353907 : Blo 1352995 1353907 := bstep (se 1 (by rfl) ⟨1015430, by rfl⟩ : syracuseStep 1353907 = 2030861) B2030861
theorem B1353923 : Blo 1352995 1353923 := bstep (se 1 (by rfl) ⟨1015442, by rfl⟩ : syracuseStep 1353923 = 2030885) B2030885
theorem B8669389 : Blo 1352995 8669389 := bstep (se 3 (by rfl) ⟨1625510, by rfl⟩ : syracuseStep 8669389 = 3251021) B3251021
theorem B1353939 : Blo 1352995 1353939 := bstep (se 1 (by rfl) ⟨1015454, by rfl⟩ : syracuseStep 1353939 = 2030909) B2030909
theorem B2058467 : Blo 1352995 2058467 := bstep (se 1 (by rfl) ⟨1543850, by rfl⟩ : syracuseStep 2058467 = 3087701) B3087701
theorem B1353955 : Blo 1352995 1353955 := bstep (se 1 (by rfl) ⟨1015466, by rfl⟩ : syracuseStep 1353955 = 2030933) B2030933
theorem B1353971 : Blo 1352995 1353971 := bstep (se 1 (by rfl) ⟨1015478, by rfl⟩ : syracuseStep 1353971 = 2030957) B2030957
theorem B2640131 : Blo 1352995 2640131 := bstep (se 1 (by rfl) ⟨1980098, by rfl⟩ : syracuseStep 2640131 = 3960197) B3960197
theorem B3426563 : Blo 1352995 3426563 := bstep (se 1 (by rfl) ⟨2569922, by rfl⟩ : syracuseStep 3426563 = 5139845) B5139845
theorem B1353987 : Blo 1352995 1353987 := bstep (se 1 (by rfl) ⟨1015490, by rfl⟩ : syracuseStep 1353987 = 2030981) B2030981
theorem B7817477 : Blo 1352995 7817477 := bstep (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) B1465777
theorem B1354003 : Blo 1352995 1354003 := bstep (se 1 (by rfl) ⟨1015502, by rfl⟩ : syracuseStep 1354003 = 2031005) B2031005
theorem B1354019 : Blo 1352995 1354019 := bstep (se 1 (by rfl) ⟨1015514, by rfl⟩ : syracuseStep 1354019 = 2031029) B2031029
theorem B1354035 : Blo 1352995 1354035 := bstep (se 1 (by rfl) ⟨1015526, by rfl⟩ : syracuseStep 1354035 = 2031053) B2031053
theorem B1354051 : Blo 1352995 1354051 := bstep (se 1 (by rfl) ⟨1015538, by rfl⟩ : syracuseStep 1354051 = 2031077) B2031077
theorem B1354067 : Blo 1352995 1354067 := bstep (se 1 (by rfl) ⟨1015550, by rfl⟩ : syracuseStep 1354067 = 2031101) B2031101
theorem B1354083 : Blo 1352995 1354083 := bstep (se 1 (by rfl) ⟨1015562, by rfl⟩ : syracuseStep 1354083 = 2031125) B2031125
theorem B8235377 : Blo 1352995 8235377 := bstep (se 2 (by rfl) ⟨3088266, by rfl⟩ : syracuseStep 8235377 = 6176533) B6176533
theorem B1354099 : Blo 1352995 1354099 := bstep (se 1 (by rfl) ⟨1015574, by rfl⟩ : syracuseStep 1354099 = 2031149) B2031149
theorem B1714547 : Blo 1352995 1714547 := bstep (se 1 (by rfl) ⟨1285910, by rfl⟩ : syracuseStep 1714547 = 2571821) B2571821
theorem B1354115 : Blo 1352995 1354115 := bstep (se 1 (by rfl) ⟨1015586, by rfl⟩ : syracuseStep 1354115 = 2031173) B2031173
theorem B24693133 : Blo 1352995 24693133 := bstep (se 3 (by rfl) ⟨4629962, by rfl⟩ : syracuseStep 24693133 = 9259925) B9259925
theorem B1354131 : Blo 1352995 1354131 := bstep (se 1 (by rfl) ⟨1015598, by rfl⟩ : syracuseStep 1354131 = 2031197) B2031197
theorem B6850979 : Blo 1352995 6850979 := bstep (se 1 (by rfl) ⟨5138234, by rfl⟩ : syracuseStep 6850979 = 10276469) B10276469
theorem B1354147 : Blo 1352995 1354147 := bstep (se 1 (by rfl) ⟨1015610, by rfl⟩ : syracuseStep 1354147 = 2031221) B2031221
theorem B1354163 : Blo 1352995 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B1354179 : Blo 1352995 1354179 := bstep (se 1 (by rfl) ⟨1015634, by rfl⟩ : syracuseStep 1354179 = 2031269) B2031269
theorem B1354195 : Blo 1352995 1354195 := bstep (se 1 (by rfl) ⟨1015646, by rfl⟩ : syracuseStep 1354195 = 2031293) B2031293
theorem B1354211 : Blo 1352995 1354211 := bstep (se 1 (by rfl) ⟨1015658, by rfl⟩ : syracuseStep 1354211 = 2031317) B2031317
theorem B1354227 : Blo 1352995 1354227 := bstep (se 1 (by rfl) ⟨1015670, by rfl⟩ : syracuseStep 1354227 = 2031341) B2031341
theorem B1354243 : Blo 1352995 1354243 := bstep (se 1 (by rfl) ⟨1015682, by rfl⟩ : syracuseStep 1354243 = 2031365) B2031365
theorem B1354259 : Blo 1352995 1354259 := bstep (se 1 (by rfl) ⟨1015694, by rfl⟩ : syracuseStep 1354259 = 2031389) B2031389
theorem B1354275 : Blo 1352995 1354275 := bstep (se 1 (by rfl) ⟨1015706, by rfl⟩ : syracuseStep 1354275 = 2031413) B2031413
theorem B1354291 : Blo 1352995 1354291 := bstep (se 1 (by rfl) ⟨1015718, by rfl⟩ : syracuseStep 1354291 = 2031437) B2031437
theorem B1354307 : Blo 1352995 1354307 := bstep (se 1 (by rfl) ⟨1015730, by rfl⟩ : syracuseStep 1354307 = 2031461) B2031461
theorem B1354323 : Blo 1352995 1354323 := bstep (se 1 (by rfl) ⟨1015742, by rfl⟩ : syracuseStep 1354323 = 2031485) B2031485
theorem B1354339 : Blo 1352995 1354339 := bstep (se 1 (by rfl) ⟨1015754, by rfl⟩ : syracuseStep 1354339 = 2031509) B2031509
theorem B1927795 : Blo 1352995 1927795 := bstep (se 1 (by rfl) ⟨1445846, by rfl⟩ : syracuseStep 1927795 = 2891693) B2891693
theorem B1354355 : Blo 1352995 1354355 := bstep (se 1 (by rfl) ⟨1015766, by rfl⟩ : syracuseStep 1354355 = 2031533) B2031533
theorem B1354371 : Blo 1352995 1354371 := bstep (se 1 (by rfl) ⟨1015778, by rfl⟩ : syracuseStep 1354371 = 2031557) B2031557
theorem B5139085 : Blo 1352995 5139085 := bstep (se 3 (by rfl) ⟨963578, by rfl⟩ : syracuseStep 5139085 = 1927157) B1927157
theorem B1354387 : Blo 1352995 1354387 := bstep (se 1 (by rfl) ⟨1015790, by rfl⟩ : syracuseStep 1354387 = 2031581) B2031581
theorem B1354403 : Blo 1352995 1354403 := bstep (se 1 (by rfl) ⟨1015802, by rfl⟩ : syracuseStep 1354403 = 2031605) B2031605
theorem B1354419 : Blo 1352995 1354419 := bstep (se 1 (by rfl) ⟨1015814, by rfl⟩ : syracuseStep 1354419 = 2031629) B2031629
theorem B1354435 : Blo 1352995 1354435 := bstep (se 1 (by rfl) ⟨1015826, by rfl⟩ : syracuseStep 1354435 = 2031653) B2031653
theorem B1354451 : Blo 1352995 1354451 := bstep (se 1 (by rfl) ⟨1015838, by rfl⟩ : syracuseStep 1354451 = 2031677) B2031677
theorem B1354467 : Blo 1352995 1354467 := bstep (se 1 (by rfl) ⟨1015850, by rfl⟩ : syracuseStep 1354467 = 2031701) B2031701
theorem B1354483 : Blo 1352995 1354483 := bstep (se 1 (by rfl) ⟨1015862, by rfl⟩ : syracuseStep 1354483 = 2031725) B2031725
theorem B1354499 : Blo 1352995 1354499 := bstep (se 1 (by rfl) ⟨1015874, by rfl⟩ : syracuseStep 1354499 = 2031749) B2031749
theorem B1354515 : Blo 1352995 1354515 := bstep (se 1 (by rfl) ⟨1015886, by rfl⟩ : syracuseStep 1354515 = 2031773) B2031773
theorem B42257173 : Blo 1352995 42257173 := bstep (se 6 (by rfl) ⟨990402, by rfl⟩ : syracuseStep 42257173 = 1980805) B1980805
theorem B7711523 : Blo 1352995 7711523 := bstep (se 1 (by rfl) ⟨5783642, by rfl⟩ : syracuseStep 7711523 = 11567285) B11567285
theorem B1354531 : Blo 1352995 1354531 := bstep (se 1 (by rfl) ⟨1015898, by rfl⟩ : syracuseStep 1354531 = 2031797) B2031797
theorem B1354547 : Blo 1352995 1354547 := bstep (se 1 (by rfl) ⟨1015910, by rfl⟩ : syracuseStep 1354547 = 2031821) B2031821
theorem B1354563 : Blo 1352995 1354563 := bstep (se 1 (by rfl) ⟨1015922, by rfl⟩ : syracuseStep 1354563 = 2031845) B2031845
theorem B1354579 : Blo 1352995 1354579 := bstep (se 1 (by rfl) ⟨1015934, by rfl⟩ : syracuseStep 1354579 = 2031869) B2031869
theorem B1354595 : Blo 1352995 1354595 := bstep (se 1 (by rfl) ⟨1015946, by rfl⟩ : syracuseStep 1354595 = 2031893) B2031893
theorem B1354611 : Blo 1352995 1354611 := bstep (se 1 (by rfl) ⟨1015958, by rfl⟩ : syracuseStep 1354611 = 2031917) B2031917
theorem B1354627 : Blo 1352995 1354627 := bstep (se 1 (by rfl) ⟨1015970, by rfl⟩ : syracuseStep 1354627 = 2031941) B2031941
theorem B1354643 : Blo 1352995 1354643 := bstep (se 1 (by rfl) ⟨1015982, by rfl⟩ : syracuseStep 1354643 = 2031965) B2031965
theorem B1354659 : Blo 1352995 1354659 := bstep (se 1 (by rfl) ⟨1015994, by rfl⟩ : syracuseStep 1354659 = 2031989) B2031989
theorem B1354675 : Blo 1352995 1354675 := bstep (se 1 (by rfl) ⟨1016006, by rfl⟩ : syracuseStep 1354675 = 2032013) B2032013
theorem B1354691 : Blo 1352995 1354691 := bstep (se 1 (by rfl) ⟨1016018, by rfl⟩ : syracuseStep 1354691 = 2032037) B2032037
theorem B1354707 : Blo 1352995 1354707 := bstep (se 1 (by rfl) ⟨1016030, by rfl⟩ : syracuseStep 1354707 = 2032061) B2032061
theorem B1354723 : Blo 1352995 1354723 := bstep (se 1 (by rfl) ⟨1016042, by rfl⟩ : syracuseStep 1354723 = 2032085) B2032085
theorem B1354739 : Blo 1352995 1354739 := bstep (se 1 (by rfl) ⟨1016054, by rfl⟩ : syracuseStep 1354739 = 2032109) B2032109
theorem B1354755 : Blo 1352995 1354755 := bstep (se 1 (by rfl) ⟨1016066, by rfl⟩ : syracuseStep 1354755 = 2032133) B2032133
theorem B3255299 : Blo 1352995 3255299 := bstep (se 1 (by rfl) ⟨2441474, by rfl⟩ : syracuseStep 3255299 = 4882949) B4882949
theorem B1354771 : Blo 1352995 1354771 := bstep (se 1 (by rfl) ⟨1016078, by rfl⟩ : syracuseStep 1354771 = 2032157) B2032157
theorem B1829921 : Blo 1352995 1829921 := bstep (se 2 (by rfl) ⟨686220, by rfl⟩ : syracuseStep 1829921 = 1372441) B1372441
theorem B1354787 : Blo 1352995 1354787 := bstep (se 1 (by rfl) ⟨1016090, by rfl⟩ : syracuseStep 1354787 = 2032181) B2032181
theorem B1354803 : Blo 1352995 1354803 := bstep (se 1 (by rfl) ⟨1016102, by rfl⟩ : syracuseStep 1354803 = 2032205) B2032205
theorem B1354819 : Blo 1352995 1354819 := bstep (se 1 (by rfl) ⟨1016114, by rfl⟩ : syracuseStep 1354819 = 2032229) B2032229
theorem B9268301 : Blo 1352995 9268301 := bstep (se 3 (by rfl) ⟨1737806, by rfl⟩ : syracuseStep 9268301 = 3475613) B3475613
theorem B1354835 : Blo 1352995 1354835 := bstep (se 1 (by rfl) ⟨1016126, by rfl⟩ : syracuseStep 1354835 = 2032253) B2032253
theorem B444402773 : Blo 1352995 444402773 := bstep (se 8 (by rfl) ⟨2603922, by rfl⟩ : syracuseStep 444402773 = 5207845) B5207845
theorem B1354851 : Blo 1352995 1354851 := bstep (se 1 (by rfl) ⟨1016138, by rfl⟩ : syracuseStep 1354851 = 2032277) B2032277
theorem B1354867 : Blo 1352995 1354867 := bstep (se 1 (by rfl) ⟨1016150, by rfl⟩ : syracuseStep 1354867 = 2032301) B2032301
theorem B1354883 : Blo 1352995 1354883 := bstep (se 1 (by rfl) ⟨1016162, by rfl⟩ : syracuseStep 1354883 = 2032325) B2032325
theorem B1354899 : Blo 1352995 1354899 := bstep (se 1 (by rfl) ⟨1016174, by rfl⟩ : syracuseStep 1354899 = 2032349) B2032349
theorem B1354915 : Blo 1352995 1354915 := bstep (se 1 (by rfl) ⟨1016186, by rfl⟩ : syracuseStep 1354915 = 2032373) B2032373
theorem B3427505 : Blo 1352995 3427505 := bstep (se 2 (by rfl) ⟨1285314, by rfl⟩ : syracuseStep 3427505 = 2570629) B2570629
theorem B1354931 : Blo 1352995 1354931 := bstep (se 1 (by rfl) ⟨1016198, by rfl⟩ : syracuseStep 1354931 = 2032397) B2032397
theorem B1354947 : Blo 1352995 1354947 := bstep (se 1 (by rfl) ⟨1016210, by rfl⟩ : syracuseStep 1354947 = 2032421) B2032421
theorem B6851789 : Blo 1352995 6851789 := bstep (se 3 (by rfl) ⟨1284710, by rfl⟩ : syracuseStep 6851789 = 2569421) B2569421
theorem B1354963 : Blo 1352995 1354963 := bstep (se 1 (by rfl) ⟨1016222, by rfl⟩ : syracuseStep 1354963 = 2032445) B2032445
theorem B2116819 : Blo 1352995 2116819 := bstep (se 1 (by rfl) ⟨1587614, by rfl⟩ : syracuseStep 2116819 = 3175229) B3175229
theorem B3427555 : Blo 1352995 3427555 := bstep (se 1 (by rfl) ⟨2570666, by rfl⟩ : syracuseStep 3427555 = 5141333) B5141333
theorem B1354979 : Blo 1352995 1354979 := bstep (se 1 (by rfl) ⟨1016234, by rfl⟩ : syracuseStep 1354979 = 2032469) B2032469
theorem B9268465 : Blo 1352995 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B1354995 : Blo 1352995 1354995 := bstep (se 1 (by rfl) ⟨1016246, by rfl⟩ : syracuseStep 1354995 = 2032493) B2032493
theorem B3853585 : Blo 1352995 3853585 := bstep (se 2 (by rfl) ⟨1445094, by rfl⟩ : syracuseStep 3853585 = 2890189) B2890189
theorem B3427697 : Blo 1352995 3427697 := bstep (se 2 (by rfl) ⟨1285386, by rfl⟩ : syracuseStep 3427697 = 2570773) B2570773
theorem B4337027 : Blo 1352995 4337027 := bstep (se 1 (by rfl) ⟨3252770, by rfl⟩ : syracuseStep 4337027 = 6505541) B6505541
theorem B5139875 : Blo 1352995 5139875 := bstep (se 1 (by rfl) ⟨3854906, by rfl⟩ : syracuseStep 5139875 = 7709813) B7709813
theorem B4566509 : Blo 1352995 4566509 := bstep (se 3 (by rfl) ⟨856220, by rfl⟩ : syracuseStep 4566509 = 1712441) B1712441
theorem B4337155 : Blo 1352995 4337155 := bstep (se 1 (by rfl) ⟨3252866, by rfl⟩ : syracuseStep 4337155 = 6505733) B6505733
theorem B4566563 : Blo 1352995 4566563 := bstep (se 1 (by rfl) ⟨3424922, by rfl⟩ : syracuseStep 4566563 = 6849845) B6849845
theorem B1445411 : Blo 1352995 1445411 := bstep (se 1 (by rfl) ⟨1084058, by rfl⟩ : syracuseStep 1445411 = 2168117) B2168117
theorem B2199089 : Blo 1352995 2199089 := bstep (se 2 (by rfl) ⟨824658, by rfl⟩ : syracuseStep 2199089 = 1649317) B1649317
theorem B4116131 : Blo 1352995 4116131 := bstep (se 1 (by rfl) ⟨3087098, by rfl⟩ : syracuseStep 4116131 = 6174197) B6174197
theorem B4878001 : Blo 1352995 4878001 := bstep (se 2 (by rfl) ⟨1829250, by rfl⟩ : syracuseStep 4878001 = 3658501) B3658501
theorem B1928929 : Blo 1352995 1928929 := bstep (se 2 (by rfl) ⟨723348, by rfl⟩ : syracuseStep 1928929 = 1446697) B1446697
theorem B1855217 : Blo 1352995 1855217 := bstep (se 2 (by rfl) ⟨695706, by rfl⟩ : syracuseStep 1855217 = 1391413) B1391413
theorem B1830673 : Blo 1352995 1830673 := bstep (se 2 (by rfl) ⟨686502, by rfl⟩ : syracuseStep 1830673 = 1373005) B1373005
theorem B41676565 : Blo 1352995 41676565 := bstep (se 6 (by rfl) ⟨976794, by rfl⟩ : syracuseStep 41676565 = 1953589) B1953589
theorem B4566833 : Blo 1352995 4566833 := bstep (se 2 (by rfl) ⟨1712562, by rfl⟩ : syracuseStep 4566833 = 3425125) B3425125
theorem B1929025 : Blo 1352995 1929025 := bstep (se 2 (by rfl) ⟨723384, by rfl⟩ : syracuseStep 1929025 = 1446769) B1446769
theorem B4337489 : Blo 1352995 4337489 := bstep (se 2 (by rfl) ⟨1626558, by rfl⟩ : syracuseStep 4337489 = 3253117) B3253117
theorem B1953649 : Blo 1352995 1953649 := bstep (se 2 (by rfl) ⟨732618, by rfl⟩ : syracuseStep 1953649 = 1465237) B1465237
theorem B5140529 : Blo 1352995 5140529 := bstep (se 2 (by rfl) ⟨1927698, by rfl⟩ : syracuseStep 5140529 = 3855397) B3855397
theorem B3657809 : Blo 1352995 3657809 := bstep (se 2 (by rfl) ⟨1371678, by rfl⟩ : syracuseStep 3657809 = 2743357) B2743357
theorem B5492941 : Blo 1352995 5492941 := bstep (se 3 (by rfl) ⟨1029926, by rfl⟩ : syracuseStep 5492941 = 2059853) B2059853
theorem B4567373 : Blo 1352995 4567373 := bstep (se 3 (by rfl) ⟨856382, by rfl⟩ : syracuseStep 4567373 = 1712765) B1712765
theorem B3658061 : Blo 1352995 3658061 := bstep (se 3 (by rfl) ⟨685886, by rfl⟩ : syracuseStep 3658061 = 1371773) B1371773
theorem B3428689 : Blo 1352995 3428689 := bstep (se 2 (by rfl) ⟨1285758, by rfl⟩ : syracuseStep 3428689 = 2571517) B2571517
theorem B8679793 : Blo 1352995 8679793 := bstep (se 2 (by rfl) ⟨3254922, by rfl⟩ : syracuseStep 8679793 = 6509845) B6509845
theorem B4567427 : Blo 1352995 4567427 := bstep (se 1 (by rfl) ⟨3425570, by rfl⟩ : syracuseStep 4567427 = 6851141) B6851141
theorem B13906403 : Blo 1352995 13906403 := bstep (se 1 (by rfl) ⟨10429802, by rfl⟩ : syracuseStep 13906403 = 20859605) B20859605
theorem B2167283 : Blo 1352995 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B3854861 : Blo 1352995 3854861 := bstep (se 3 (by rfl) ⟨722786, by rfl⟩ : syracuseStep 3854861 = 1445573) B1445573
theorem B3428963 : Blo 1352995 3428963 := bstep (se 1 (by rfl) ⟨2571722, by rfl⟩ : syracuseStep 3428963 = 5143445) B5143445
theorem B4117105 : Blo 1352995 4117105 := bstep (se 2 (by rfl) ⟨1543914, by rfl⟩ : syracuseStep 4117105 = 3087829) B3087829
theorem B7713413 : Blo 1352995 7713413 := bstep (se 4 (by rfl) ⟨723132, by rfl⟩ : syracuseStep 7713413 = 1446265) B1446265
theorem B4567697 : Blo 1352995 4567697 := bstep (se 2 (by rfl) ⟨1712886, by rfl⟩ : syracuseStep 4567697 = 3425773) B3425773
theorem B1446547 : Blo 1352995 1446547 := bstep (se 1 (by rfl) ⟨1084910, by rfl⟩ : syracuseStep 1446547 = 2169821) B2169821
theorem B3855043 : Blo 1352995 3855043 := bstep (se 1 (by rfl) ⟨2891282, by rfl⟩ : syracuseStep 3855043 = 5782565) B5782565
theorem B5780173 : Blo 1352995 5780173 := bstep (se 3 (by rfl) ⟨1083782, by rfl⟩ : syracuseStep 5780173 = 2167565) B2167565
theorem B3855089 : Blo 1352995 3855089 := bstep (se 2 (by rfl) ⟨1445658, by rfl⟩ : syracuseStep 3855089 = 2891317) B2891317
theorem B2167553 : Blo 1352995 2167553 := bstep (se 2 (by rfl) ⟨812832, by rfl⟩ : syracuseStep 2167553 = 1625665) B1625665
theorem B4633357 : Blo 1352995 4633357 := bstep (se 3 (by rfl) ⟨868754, by rfl⟩ : syracuseStep 4633357 = 1737509) B1737509
theorem B8237837 : Blo 1352995 8237837 := bstep (se 3 (by rfl) ⟨1544594, by rfl⟩ : syracuseStep 8237837 = 3089189) B3089189
theorem B3429155 : Blo 1352995 3429155 := bstep (se 1 (by rfl) ⟨2571866, by rfl⟩ : syracuseStep 3429155 = 5143733) B5143733
theorem B2167841 : Blo 1352995 2167841 := bstep (se 2 (by rfl) ⟨812940, by rfl⟩ : syracuseStep 2167841 = 1625881) B1625881
theorem B2569315 : Blo 1352995 2569315 := bstep (se 1 (by rfl) ⟨1926986, by rfl⟩ : syracuseStep 2569315 = 3853973) B3853973
theorem B3044465 : Blo 1352995 3044465 := bstep (se 2 (by rfl) ⟨1141674, by rfl⟩ : syracuseStep 3044465 = 2283349) B2283349
theorem B3044483 : Blo 1352995 3044483 := bstep (se 1 (by rfl) ⟨2283362, by rfl⟩ : syracuseStep 3044483 = 4566725) B4566725
theorem B9270413 : Blo 1352995 9270413 := bstep (se 3 (by rfl) ⟨1738202, by rfl⟩ : syracuseStep 9270413 = 3476405) B3476405
theorem B4568237 : Blo 1352995 4568237 := bstep (se 3 (by rfl) ⟨856544, by rfl⟩ : syracuseStep 4568237 = 1713089) B1713089
theorem B6264013 : Blo 1352995 6264013 := bstep (se 3 (by rfl) ⟨1174502, by rfl⟩ : syracuseStep 6264013 = 2349005) B2349005
theorem B4568291 : Blo 1352995 4568291 := bstep (se 1 (by rfl) ⟨3426218, by rfl⟩ : syracuseStep 4568291 = 6852437) B6852437
theorem B2569475 : Blo 1352995 2569475 := bstep (se 1 (by rfl) ⟨1927106, by rfl⟩ : syracuseStep 2569475 = 3854213) B3854213
theorem B2970929 : Blo 1352995 2970929 := bstep (se 2 (by rfl) ⟨1114098, by rfl⟩ : syracuseStep 2970929 = 2228197) B2228197
theorem B3044753 : Blo 1352995 3044753 := bstep (se 2 (by rfl) ⟨1141782, by rfl⟩ : syracuseStep 3044753 = 2283565) B2283565
theorem B3044771 : Blo 1352995 3044771 := bstep (se 1 (by rfl) ⟨2283578, by rfl⟩ : syracuseStep 3044771 = 4567157) B4567157
theorem B3659185 : Blo 1352995 3659185 := bstep (se 2 (by rfl) ⟨1372194, by rfl⟩ : syracuseStep 3659185 = 2744389) B2744389
theorem B2168257 : Blo 1352995 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B5141987 : Blo 1352995 5141987 := bstep (se 1 (by rfl) ⟨3856490, by rfl⟩ : syracuseStep 5141987 = 7712981) B7712981
theorem B4568561 : Blo 1352995 4568561 := bstep (se 2 (by rfl) ⟨1713210, by rfl⟩ : syracuseStep 4568561 = 3426421) B3426421
theorem B5142001 : Blo 1352995 5142001 := bstep (se 2 (by rfl) ⟨1928250, by rfl⟩ : syracuseStep 5142001 = 3856501) B3856501
theorem B10278413 : Blo 1352995 10278413 := bstep (se 3 (by rfl) ⟨1927202, by rfl⟩ : syracuseStep 10278413 = 3854405) B3854405
theorem B3045041 : Blo 1352995 3045041 := bstep (se 2 (by rfl) ⟨1141890, by rfl⟩ : syracuseStep 3045041 = 2283781) B2283781
theorem B2283187 : Blo 1352995 2283187 := bstep (se 1 (by rfl) ⟨1712390, by rfl⟩ : syracuseStep 2283187 = 3424781) B3424781
theorem B3045059 : Blo 1352995 3045059 := bstep (se 1 (by rfl) ⟨2283794, by rfl⟩ : syracuseStep 3045059 = 4567589) B4567589
theorem B6510307 : Blo 1352995 6510307 := bstep (se 1 (by rfl) ⟨4882730, by rfl⟩ : syracuseStep 6510307 = 9765461) B9765461
theorem B5781233 : Blo 1352995 5781233 := bstep (se 2 (by rfl) ⟨2167962, by rfl⟩ : syracuseStep 5781233 = 4335925) B4335925
theorem B13014769 : Blo 1352995 13014769 := bstep (se 2 (by rfl) ⟨4880538, by rfl⟩ : syracuseStep 13014769 = 9761077) B9761077
theorem B2438915 : Blo 1352995 2438915 := bstep (se 1 (by rfl) ⟨1829186, by rfl⟩ : syracuseStep 2438915 = 3658373) B3658373
theorem B6502157 : Blo 1352995 6502157 := bstep (se 3 (by rfl) ⟨1219154, by rfl⟩ : syracuseStep 6502157 = 2438309) B2438309
theorem B7812877 : Blo 1352995 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B2283329 : Blo 1352995 2283329 := bstep (se 2 (by rfl) ⟨856248, by rfl⟩ : syracuseStep 2283329 = 1712497) B1712497
theorem B11728739 : Blo 1352995 11728739 := bstep (se 1 (by rfl) ⟨8796554, by rfl⟩ : syracuseStep 11728739 = 17593109) B17593109
theorem B5207971 : Blo 1352995 5207971 := bstep (se 1 (by rfl) ⟨3905978, by rfl⟩ : syracuseStep 5207971 = 7811957) B7811957
theorem B2029505 : Blo 1352995 2029505 := bstep (se 2 (by rfl) ⟨761064, by rfl⟩ : syracuseStep 2029505 = 1522129) B1522129
theorem B2283457 : Blo 1352995 2283457 := bstep (se 2 (by rfl) ⟨856296, by rfl⟩ : syracuseStep 2283457 = 1712593) B1712593
theorem B3045329 : Blo 1352995 3045329 := bstep (se 2 (by rfl) ⟨1141998, by rfl⟩ : syracuseStep 3045329 = 2283997) B2283997
theorem B2029523 : Blo 1352995 2029523 := bstep (se 1 (by rfl) ⟨1522142, by rfl⟩ : syracuseStep 2029523 = 3044285) B3044285
theorem B2283491 : Blo 1352995 2283491 := bstep (se 1 (by rfl) ⟨1712618, by rfl⟩ : syracuseStep 2283491 = 3425237) B3425237
theorem B3045347 : Blo 1352995 3045347 := bstep (se 1 (by rfl) ⟨2284010, by rfl⟩ : syracuseStep 3045347 = 4568021) B4568021
theorem B2029553 : Blo 1352995 2029553 := bstep (se 2 (by rfl) ⟨761082, by rfl⟩ : syracuseStep 2029553 = 1522165) B1522165
theorem B2029571 : Blo 1352995 2029571 := bstep (se 1 (by rfl) ⟨1522178, by rfl⟩ : syracuseStep 2029571 = 3044357) B3044357
theorem B4569101 : Blo 1352995 4569101 := bstep (se 3 (by rfl) ⟨856706, by rfl⟩ : syracuseStep 4569101 = 1713413) B1713413
theorem B2029601 : Blo 1352995 2029601 := bstep (se 2 (by rfl) ⟨761100, by rfl⟩ : syracuseStep 2029601 = 1522201) B1522201
theorem B5568547 : Blo 1352995 5568547 := bstep (se 1 (by rfl) ⟨4176410, by rfl⟩ : syracuseStep 5568547 = 8352821) B8352821
theorem B6854705 : Blo 1352995 6854705 := bstep (se 2 (by rfl) ⟨2570514, by rfl⟩ : syracuseStep 6854705 = 5141029) B5141029
theorem B2029619 : Blo 1352995 2029619 := bstep (se 1 (by rfl) ⟨1522214, by rfl⟩ : syracuseStep 2029619 = 3044429) B3044429
theorem B4569155 : Blo 1352995 4569155 := bstep (se 1 (by rfl) ⟨3426866, by rfl⟩ : syracuseStep 4569155 = 6853733) B6853733
theorem B2029649 : Blo 1352995 2029649 := bstep (se 2 (by rfl) ⟨761118, by rfl⟩ : syracuseStep 2029649 = 1522237) B1522237
theorem B2029667 : Blo 1352995 2029667 := bstep (se 1 (by rfl) ⟨1522250, by rfl⟩ : syracuseStep 2029667 = 3044501) B3044501
theorem B2283619 : Blo 1352995 2283619 := bstep (se 1 (by rfl) ⟨1712714, by rfl⟩ : syracuseStep 2283619 = 3425429) B3425429
theorem B4118627 : Blo 1352995 4118627 := bstep (se 1 (by rfl) ⟨3088970, by rfl⟩ : syracuseStep 4118627 = 6177941) B6177941
theorem B5863537 : Blo 1352995 5863537 := bstep (se 2 (by rfl) ⟨2198826, by rfl⟩ : syracuseStep 5863537 = 4397653) B4397653
theorem B2029697 : Blo 1352995 2029697 := bstep (se 2 (by rfl) ⟨761136, by rfl⟩ : syracuseStep 2029697 = 1522273) B1522273
theorem B2029715 : Blo 1352995 2029715 := bstep (se 1 (by rfl) ⟨1522286, by rfl⟩ : syracuseStep 2029715 = 3044573) B3044573
theorem B3856547 : Blo 1352995 3856547 := bstep (se 1 (by rfl) ⟨2892410, by rfl⟩ : syracuseStep 3856547 = 5784821) B5784821
theorem B2029745 : Blo 1352995 2029745 := bstep (se 2 (by rfl) ⟨761154, by rfl⟩ : syracuseStep 2029745 = 1522309) B1522309
theorem B2029763 : Blo 1352995 2029763 := bstep (se 1 (by rfl) ⟨1522322, by rfl⟩ : syracuseStep 2029763 = 3044645) B3044645
theorem B2029793 : Blo 1352995 2029793 := bstep (se 2 (by rfl) ⟨761172, by rfl⟩ : syracuseStep 2029793 = 1522345) B1522345
theorem B2283761 : Blo 1352995 2283761 := bstep (se 2 (by rfl) ⟨856410, by rfl⟩ : syracuseStep 2283761 = 1712821) B1712821
theorem B3045617 : Blo 1352995 3045617 := bstep (se 2 (by rfl) ⟨1142106, by rfl⟩ : syracuseStep 3045617 = 2284213) B2284213
theorem B2029811 : Blo 1352995 2029811 := bstep (se 1 (by rfl) ⟨1522358, by rfl⟩ : syracuseStep 2029811 = 3044717) B3044717
theorem B3905795 : Blo 1352995 3905795 := bstep (se 1 (by rfl) ⟨2929346, by rfl⟩ : syracuseStep 3905795 = 5858693) B5858693
theorem B3045635 : Blo 1352995 3045635 := bstep (se 1 (by rfl) ⟨2284226, by rfl⟩ : syracuseStep 3045635 = 4568453) B4568453
theorem B2029841 : Blo 1352995 2029841 := bstep (se 2 (by rfl) ⟨761190, by rfl⟩ : syracuseStep 2029841 = 1522381) B1522381
theorem B2890019 : Blo 1352995 2890019 := bstep (se 1 (by rfl) ⟨2167514, by rfl⟩ : syracuseStep 2890019 = 4335029) B4335029
theorem B2029859 : Blo 1352995 2029859 := bstep (se 1 (by rfl) ⟨1522394, by rfl⟩ : syracuseStep 2029859 = 3044789) B3044789
theorem B2570545 : Blo 1352995 2570545 := bstep (se 2 (by rfl) ⟨963954, by rfl⟩ : syracuseStep 2570545 = 1927909) B1927909
theorem B9394481 : Blo 1352995 9394481 := bstep (se 2 (by rfl) ⟨3522930, by rfl⟩ : syracuseStep 9394481 = 7045861) B7045861
theorem B2029889 : Blo 1352995 2029889 := bstep (se 2 (by rfl) ⟨761208, by rfl⟩ : syracuseStep 2029889 = 1522417) B1522417
theorem B2169155 : Blo 1352995 2169155 := bstep (se 1 (by rfl) ⟨1626866, by rfl⟩ : syracuseStep 2169155 = 3253733) B3253733
theorem B9263429 : Blo 1352995 9263429 := bstep (se 4 (by rfl) ⟨868446, by rfl⟩ : syracuseStep 9263429 = 1736893) B1736893
theorem B17357125 : Blo 1352995 17357125 := bstep (se 4 (by rfl) ⟨1627230, by rfl⟩ : syracuseStep 17357125 = 3254461) B3254461
theorem B4569425 : Blo 1352995 4569425 := bstep (se 2 (by rfl) ⟨1713534, by rfl⟩ : syracuseStep 4569425 = 3427069) B3427069
theorem B2029907 : Blo 1352995 2029907 := bstep (se 1 (by rfl) ⟨1522430, by rfl⟩ : syracuseStep 2029907 = 3044861) B3044861
theorem B2029937 : Blo 1352995 2029937 := bstep (se 2 (by rfl) ⟨761226, by rfl⟩ : syracuseStep 2029937 = 1522453) B1522453
theorem B2283889 : Blo 1352995 2283889 := bstep (se 2 (by rfl) ⟨856458, by rfl⟩ : syracuseStep 2283889 = 1712917) B1712917
theorem B8345969 : Blo 1352995 8345969 := bstep (se 2 (by rfl) ⟨3129738, by rfl⟩ : syracuseStep 8345969 = 6259477) B6259477
theorem B2029955 : Blo 1352995 2029955 := bstep (se 1 (by rfl) ⟨1522466, by rfl⟩ : syracuseStep 2029955 = 3044933) B3044933
theorem B9763213 : Blo 1352995 9763213 := bstep (se 3 (by rfl) ⟨1830602, by rfl⟩ : syracuseStep 9763213 = 3661205) B3661205
theorem B2283923 : Blo 1352995 2283923 := bstep (se 1 (by rfl) ⟨1712942, by rfl⟩ : syracuseStep 2283923 = 3425885) B3425885
theorem B2029985 : Blo 1352995 2029985 := bstep (se 2 (by rfl) ⟨761244, by rfl⟩ : syracuseStep 2029985 = 1522489) B1522489
theorem B2030003 : Blo 1352995 2030003 := bstep (se 1 (by rfl) ⟨1522502, by rfl⟩ : syracuseStep 2030003 = 3045005) B3045005
theorem B2030033 : Blo 1352995 2030033 := bstep (se 2 (by rfl) ⟨761262, by rfl⟩ : syracuseStep 2030033 = 1522525) B1522525
theorem B1522147 : Blo 1352995 1522147 := bstep (se 1 (by rfl) ⟨1141610, by rfl⟩ : syracuseStep 1522147 = 2283221) B2283221
theorem B2030051 : Blo 1352995 2030051 := bstep (se 1 (by rfl) ⟨1522538, by rfl⟩ : syracuseStep 2030051 = 3045077) B3045077
theorem B2030081 : Blo 1352995 2030081 := bstep (se 2 (by rfl) ⟨761280, by rfl⟩ : syracuseStep 2030081 = 1522561) B1522561
theorem B7707149 : Blo 1352995 7707149 := bstep (se 3 (by rfl) ⟨1445090, by rfl⟩ : syracuseStep 7707149 = 2890181) B2890181
theorem B3045905 : Blo 1352995 3045905 := bstep (se 2 (by rfl) ⟨1142214, by rfl⟩ : syracuseStep 3045905 = 2284429) B2284429
theorem B2030099 : Blo 1352995 2030099 := bstep (se 1 (by rfl) ⟨1522574, by rfl⟩ : syracuseStep 2030099 = 3045149) B3045149
theorem B2284051 : Blo 1352995 2284051 := bstep (se 1 (by rfl) ⟨1713038, by rfl⟩ : syracuseStep 2284051 = 3426077) B3426077
theorem B3045923 : Blo 1352995 3045923 := bstep (se 1 (by rfl) ⟨2284442, by rfl⟩ : syracuseStep 3045923 = 4568885) B4568885
theorem B2169379 : Blo 1352995 2169379 := bstep (se 1 (by rfl) ⟨1627034, by rfl⟩ : syracuseStep 2169379 = 3254069) B3254069
theorem B2030129 : Blo 1352995 2030129 := bstep (se 2 (by rfl) ⟨761298, by rfl⟩ : syracuseStep 2030129 = 1522597) B1522597
theorem B2030147 : Blo 1352995 2030147 := bstep (se 1 (by rfl) ⟨1522610, by rfl⟩ : syracuseStep 2030147 = 3045221) B3045221
theorem B2030177 : Blo 1352995 2030177 := bstep (se 2 (by rfl) ⟨761316, by rfl⟩ : syracuseStep 2030177 = 1522633) B1522633
theorem B1522291 : Blo 1352995 1522291 := bstep (se 1 (by rfl) ⟨1141718, by rfl⟩ : syracuseStep 1522291 = 2283437) B2283437
theorem B2030195 : Blo 1352995 2030195 := bstep (se 1 (by rfl) ⟨1522646, by rfl⟩ : syracuseStep 2030195 = 3045293) B3045293
theorem B2030225 : Blo 1352995 2030225 := bstep (se 2 (by rfl) ⟨761334, by rfl⟩ : syracuseStep 2030225 = 1522669) B1522669
theorem B2284193 : Blo 1352995 2284193 := bstep (se 2 (by rfl) ⟨856572, by rfl⟩ : syracuseStep 2284193 = 1713145) B1713145
theorem B2030243 : Blo 1352995 2030243 := bstep (se 1 (by rfl) ⟨1522682, by rfl⟩ : syracuseStep 2030243 = 3045365) B3045365
theorem B15424181 : Blo 1352995 15424181 := bstep (se 5 (by rfl) ⟨723008, by rfl⟩ : syracuseStep 15424181 = 1446017) B1446017
theorem B2030273 : Blo 1352995 2030273 := bstep (se 2 (by rfl) ⟨761352, by rfl⟩ : syracuseStep 2030273 = 1522705) B1522705
theorem B2030291 : Blo 1352995 2030291 := bstep (se 1 (by rfl) ⟨1522718, by rfl⟩ : syracuseStep 2030291 = 3045437) B3045437
theorem B3660515 : Blo 1352995 3660515 := bstep (se 1 (by rfl) ⟨2745386, by rfl⟩ : syracuseStep 3660515 = 5490773) B5490773
theorem B4340461 : Blo 1352995 4340461 := bstep (se 3 (by rfl) ⟨813836, by rfl⟩ : syracuseStep 4340461 = 1627673) B1627673
theorem B2030321 : Blo 1352995 2030321 := bstep (se 2 (by rfl) ⟨761370, by rfl⟩ : syracuseStep 2030321 = 1522741) B1522741
theorem B1522435 : Blo 1352995 1522435 := bstep (se 1 (by rfl) ⟨1141826, by rfl⟩ : syracuseStep 1522435 = 2283653) B2283653
theorem B2030339 : Blo 1352995 2030339 := bstep (se 1 (by rfl) ⟨1522754, by rfl⟩ : syracuseStep 2030339 = 3045509) B3045509
theorem B2030369 : Blo 1352995 2030369 := bstep (se 2 (by rfl) ⟨761388, by rfl⟩ : syracuseStep 2030369 = 1522777) B1522777
theorem B2284321 : Blo 1352995 2284321 := bstep (se 2 (by rfl) ⟨856620, by rfl⟩ : syracuseStep 2284321 = 1713241) B1713241
theorem B3046193 : Blo 1352995 3046193 := bstep (se 2 (by rfl) ⟨1142322, by rfl⟩ : syracuseStep 3046193 = 2284645) B2284645
theorem B2030387 : Blo 1352995 2030387 := bstep (se 1 (by rfl) ⟨1522790, by rfl⟩ : syracuseStep 2030387 = 3045581) B3045581
theorem B2284355 : Blo 1352995 2284355 := bstep (se 1 (by rfl) ⟨1713266, by rfl⟩ : syracuseStep 2284355 = 3426533) B3426533
theorem B3046211 : Blo 1352995 3046211 := bstep (se 1 (by rfl) ⟨2284658, by rfl⟩ : syracuseStep 3046211 = 4569317) B4569317
theorem B2030417 : Blo 1352995 2030417 := bstep (se 2 (by rfl) ⟨761406, by rfl⟩ : syracuseStep 2030417 = 1522813) B1522813
theorem B2030435 : Blo 1352995 2030435 := bstep (se 1 (by rfl) ⟨1522826, by rfl⟩ : syracuseStep 2030435 = 3045653) B3045653
theorem B4569965 : Blo 1352995 4569965 := bstep (se 3 (by rfl) ⟨856868, by rfl⟩ : syracuseStep 4569965 = 1713737) B1713737
theorem B2030465 : Blo 1352995 2030465 := bstep (se 2 (by rfl) ⟨761424, by rfl⟩ : syracuseStep 2030465 = 1522849) B1522849
theorem B2317187 : Blo 1352995 2317187 := bstep (se 1 (by rfl) ⟨1737890, by rfl⟩ : syracuseStep 2317187 = 3475781) B3475781
theorem B1522579 : Blo 1352995 1522579 := bstep (se 1 (by rfl) ⟨1141934, by rfl⟩ : syracuseStep 1522579 = 2283869) B2283869
theorem B2030483 : Blo 1352995 2030483 := bstep (se 1 (by rfl) ⟨1522862, by rfl⟩ : syracuseStep 2030483 = 3045725) B3045725
theorem B4570019 : Blo 1352995 4570019 := bstep (se 1 (by rfl) ⟨3427514, by rfl⟩ : syracuseStep 4570019 = 6855029) B6855029
theorem B5143459 : Blo 1352995 5143459 := bstep (se 1 (by rfl) ⟨3857594, by rfl⟩ : syracuseStep 5143459 = 7715189) B7715189
theorem B2030513 : Blo 1352995 2030513 := bstep (se 2 (by rfl) ⟨761442, by rfl⟩ : syracuseStep 2030513 = 1522885) B1522885
theorem B2030531 : Blo 1352995 2030531 := bstep (se 1 (by rfl) ⟨1522898, by rfl⟩ : syracuseStep 2030531 = 3045797) B3045797
theorem B2284483 : Blo 1352995 2284483 := bstep (se 1 (by rfl) ⟨1713362, by rfl⟩ : syracuseStep 2284483 = 3426725) B3426725
theorem B31267781 : Blo 1352995 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B2030561 : Blo 1352995 2030561 := bstep (se 2 (by rfl) ⟨761460, by rfl⟩ : syracuseStep 2030561 = 1522921) B1522921
theorem B4340717 : Blo 1352995 4340717 := bstep (se 3 (by rfl) ⟨813884, by rfl⟩ : syracuseStep 4340717 = 1627769) B1627769
theorem B2030579 : Blo 1352995 2030579 := bstep (se 1 (by rfl) ⟨1522934, by rfl⟩ : syracuseStep 2030579 = 3045869) B3045869
theorem B2030609 : Blo 1352995 2030609 := bstep (se 2 (by rfl) ⟨761478, by rfl⟩ : syracuseStep 2030609 = 1522957) B1522957
theorem B1522723 : Blo 1352995 1522723 := bstep (se 1 (by rfl) ⟨1142042, by rfl⟩ : syracuseStep 1522723 = 2284085) B2284085
theorem B2030627 : Blo 1352995 2030627 := bstep (se 1 (by rfl) ⟨1522970, by rfl⟩ : syracuseStep 2030627 = 3045941) B3045941
theorem B2030657 : Blo 1352995 2030657 := bstep (se 2 (by rfl) ⟨761496, by rfl⟩ : syracuseStep 2030657 = 1522993) B1522993
theorem B2284625 : Blo 1352995 2284625 := bstep (se 2 (by rfl) ⟨856734, by rfl⟩ : syracuseStep 2284625 = 1713469) B1713469
theorem B3046481 : Blo 1352995 3046481 := bstep (se 2 (by rfl) ⟨1142430, by rfl⟩ : syracuseStep 3046481 = 2284861) B2284861
theorem B2030675 : Blo 1352995 2030675 := bstep (se 1 (by rfl) ⟨1523006, by rfl⟩ : syracuseStep 2030675 = 3046013) B3046013
theorem B3046499 : Blo 1352995 3046499 := bstep (se 1 (by rfl) ⟨2284874, by rfl⟩ : syracuseStep 3046499 = 4569749) B4569749
theorem B2890865 : Blo 1352995 2890865 := bstep (se 2 (by rfl) ⟨1084074, by rfl⟩ : syracuseStep 2890865 = 2168149) B2168149
theorem B2030705 : Blo 1352995 2030705 := bstep (se 2 (by rfl) ⟨761514, by rfl⟩ : syracuseStep 2030705 = 1523029) B1523029
theorem B4881521 : Blo 1352995 4881521 := bstep (se 2 (by rfl) ⟨1830570, by rfl⟩ : syracuseStep 4881521 = 3661141) B3661141
theorem B2030723 : Blo 1352995 2030723 := bstep (se 1 (by rfl) ⟨1523042, by rfl⟩ : syracuseStep 2030723 = 3046085) B3046085
theorem B2030753 : Blo 1352995 2030753 := bstep (se 2 (by rfl) ⟨761532, by rfl⟩ : syracuseStep 2030753 = 1523065) B1523065
theorem B4570289 : Blo 1352995 4570289 := bstep (se 2 (by rfl) ⟨1713858, by rfl⟩ : syracuseStep 4570289 = 3427717) B3427717
theorem B1522867 : Blo 1352995 1522867 := bstep (se 1 (by rfl) ⟨1142150, by rfl⟩ : syracuseStep 1522867 = 2284301) B2284301
theorem B2030771 : Blo 1352995 2030771 := bstep (se 1 (by rfl) ⟨1523078, by rfl⟩ : syracuseStep 2030771 = 3046157) B3046157
theorem B2030801 : Blo 1352995 2030801 := bstep (se 2 (by rfl) ⟨761550, by rfl⟩ : syracuseStep 2030801 = 1523101) B1523101
theorem B2284753 : Blo 1352995 2284753 := bstep (se 2 (by rfl) ⟨856782, by rfl⟩ : syracuseStep 2284753 = 1713565) B1713565
theorem B2030819 : Blo 1352995 2030819 := bstep (se 1 (by rfl) ⟨1523114, by rfl⟩ : syracuseStep 2030819 = 3046229) B3046229
theorem B4881635 : Blo 1352995 4881635 := bstep (se 1 (by rfl) ⟨3661226, by rfl⟩ : syracuseStep 4881635 = 7322453) B7322453
theorem B2284787 : Blo 1352995 2284787 := bstep (se 1 (by rfl) ⟨1713590, by rfl⟩ : syracuseStep 2284787 = 3427181) B3427181
theorem B2145523 : Blo 1352995 2145523 := bstep (se 1 (by rfl) ⟨1609142, by rfl⟩ : syracuseStep 2145523 = 3218285) B3218285
theorem B2030849 : Blo 1352995 2030849 := bstep (se 2 (by rfl) ⟨761568, by rfl⟩ : syracuseStep 2030849 = 1523137) B1523137
theorem B2030867 : Blo 1352995 2030867 := bstep (se 1 (by rfl) ⟨1523150, by rfl⟩ : syracuseStep 2030867 = 3046301) B3046301
theorem B2030897 : Blo 1352995 2030897 := bstep (se 2 (by rfl) ⟨761586, by rfl⟩ : syracuseStep 2030897 = 1523173) B1523173
theorem B1523011 : Blo 1352995 1523011 := bstep (se 1 (by rfl) ⟨1142258, by rfl⟩ : syracuseStep 1523011 = 2284517) B2284517
theorem B2030915 : Blo 1352995 2030915 := bstep (se 1 (by rfl) ⟨1523186, by rfl⟩ : syracuseStep 2030915 = 3046373) B3046373
theorem B2571601 : Blo 1352995 2571601 := bstep (se 2 (by rfl) ⟨964350, by rfl⟩ : syracuseStep 2571601 = 1928701) B1928701
theorem B2030945 : Blo 1352995 2030945 := bstep (se 2 (by rfl) ⟨761604, by rfl⟩ : syracuseStep 2030945 = 1523209) B1523209
theorem B3046769 : Blo 1352995 3046769 := bstep (se 2 (by rfl) ⟨1142538, by rfl⟩ : syracuseStep 3046769 = 2285077) B2285077
theorem B3857777 : Blo 1352995 3857777 := bstep (se 2 (by rfl) ⟨1446666, by rfl⟩ : syracuseStep 3857777 = 2893333) B2893333
theorem B2030963 : Blo 1352995 2030963 := bstep (se 1 (by rfl) ⟨1523222, by rfl⟩ : syracuseStep 2030963 = 3046445) B3046445
theorem B2284915 : Blo 1352995 2284915 := bstep (se 1 (by rfl) ⟨1713686, by rfl⟩ : syracuseStep 2284915 = 3427373) B3427373
theorem B3046787 : Blo 1352995 3046787 := bstep (se 1 (by rfl) ⟨2285090, by rfl⟩ : syracuseStep 3046787 = 4570181) B4570181
theorem B2030993 : Blo 1352995 2030993 := bstep (se 2 (by rfl) ⟨761622, by rfl⟩ : syracuseStep 2030993 = 1523245) B1523245
theorem B2031011 : Blo 1352995 2031011 := bstep (se 1 (by rfl) ⟨1523258, by rfl⟩ : syracuseStep 2031011 = 3046517) B3046517
theorem B7708081 : Blo 1352995 7708081 := bstep (se 2 (by rfl) ⟨2890530, by rfl⟩ : syracuseStep 7708081 = 5781061) B5781061
theorem B2031041 : Blo 1352995 2031041 := bstep (se 2 (by rfl) ⟨761640, by rfl⟩ : syracuseStep 2031041 = 1523281) B1523281
theorem B1523155 : Blo 1352995 1523155 := bstep (se 1 (by rfl) ⟨1142366, by rfl⟩ : syracuseStep 1523155 = 2284733) B2284733
theorem B2031059 : Blo 1352995 2031059 := bstep (se 1 (by rfl) ⟨1523294, by rfl⟩ : syracuseStep 2031059 = 3046589) B3046589
theorem B6856163 : Blo 1352995 6856163 := bstep (se 1 (by rfl) ⟨5142122, by rfl⟩ : syracuseStep 6856163 = 10284245) B10284245
theorem B2031089 : Blo 1352995 2031089 := bstep (se 2 (by rfl) ⟨761658, by rfl⟩ : syracuseStep 2031089 = 1523317) B1523317
theorem B2285057 : Blo 1352995 2285057 := bstep (se 2 (by rfl) ⟨856896, by rfl⟩ : syracuseStep 2285057 = 1713793) B1713793
theorem B2031107 : Blo 1352995 2031107 := bstep (se 1 (by rfl) ⟨1523330, by rfl⟩ : syracuseStep 2031107 = 3046661) B3046661
theorem B2170385 : Blo 1352995 2170385 := bstep (se 2 (by rfl) ⟨813894, by rfl⟩ : syracuseStep 2170385 = 1627789) B1627789
theorem B2031137 : Blo 1352995 2031137 := bstep (se 2 (by rfl) ⟨761676, by rfl⟩ : syracuseStep 2031137 = 1523353) B1523353
theorem B3661357 : Blo 1352995 3661357 := bstep (se 3 (by rfl) ⟨686504, by rfl⟩ : syracuseStep 3661357 = 1373009) B1373009
theorem B2031155 : Blo 1352995 2031155 := bstep (se 1 (by rfl) ⟨1523366, by rfl⟩ : syracuseStep 2031155 = 3046733) B3046733
theorem B2031185 : Blo 1352995 2031185 := bstep (se 2 (by rfl) ⟨761694, by rfl⟩ : syracuseStep 2031185 = 1523389) B1523389
theorem B1523299 : Blo 1352995 1523299 := bstep (se 1 (by rfl) ⟨1142474, by rfl⟩ : syracuseStep 1523299 = 2284949) B2284949
theorem B2031203 : Blo 1352995 2031203 := bstep (se 1 (by rfl) ⟨1523402, by rfl⟩ : syracuseStep 2031203 = 3046805) B3046805
theorem B2031233 : Blo 1352995 2031233 := bstep (se 2 (by rfl) ⟨761712, by rfl⟩ : syracuseStep 2031233 = 1523425) B1523425
theorem B2285185 : Blo 1352995 2285185 := bstep (se 2 (by rfl) ⟨856944, by rfl⟩ : syracuseStep 2285185 = 1713889) B1713889
theorem B3047057 : Blo 1352995 3047057 := bstep (se 2 (by rfl) ⟨1142646, by rfl⟩ : syracuseStep 3047057 = 2285293) B2285293
theorem B2031251 : Blo 1352995 2031251 := bstep (se 1 (by rfl) ⟨1523438, by rfl⟩ : syracuseStep 2031251 = 3046877) B3046877
theorem B2285219 : Blo 1352995 2285219 := bstep (se 1 (by rfl) ⟨1713914, by rfl⟩ : syracuseStep 2285219 = 3427829) B3427829
theorem B3047075 : Blo 1352995 3047075 := bstep (se 1 (by rfl) ⟨2285306, by rfl⟩ : syracuseStep 3047075 = 4570613) B4570613
theorem B2031281 : Blo 1352995 2031281 := bstep (se 2 (by rfl) ⟨761730, by rfl⟩ : syracuseStep 2031281 = 1523461) B1523461
theorem B2031299 : Blo 1352995 2031299 := bstep (se 1 (by rfl) ⟨1523474, by rfl⟩ : syracuseStep 2031299 = 3046949) B3046949
theorem B4570829 : Blo 1352995 4570829 := bstep (se 3 (by rfl) ⟨857030, by rfl⟩ : syracuseStep 4570829 = 1714061) B1714061
theorem B2031329 : Blo 1352995 2031329 := bstep (se 2 (by rfl) ⟨761748, by rfl⟩ : syracuseStep 2031329 = 1523497) B1523497
theorem B2572003 : Blo 1352995 2572003 := bstep (se 1 (by rfl) ⟨1929002, by rfl⟩ : syracuseStep 2572003 = 3858005) B3858005
theorem B1523443 : Blo 1352995 1523443 := bstep (se 1 (by rfl) ⟨1142582, by rfl⟩ : syracuseStep 1523443 = 2285165) B2285165
theorem B2031347 : Blo 1352995 2031347 := bstep (se 1 (by rfl) ⟨1523510, by rfl⟩ : syracuseStep 2031347 = 3047021) B3047021
theorem B4570883 : Blo 1352995 4570883 := bstep (se 1 (by rfl) ⟨3428162, by rfl⟩ : syracuseStep 4570883 = 6856325) B6856325
theorem B2031377 : Blo 1352995 2031377 := bstep (se 2 (by rfl) ⟨761766, by rfl⟩ : syracuseStep 2031377 = 1523533) B1523533
theorem B2572049 : Blo 1352995 2572049 := bstep (se 2 (by rfl) ⟨964518, by rfl⟩ : syracuseStep 2572049 = 1929037) B1929037
theorem B2031395 : Blo 1352995 2031395 := bstep (se 1 (by rfl) ⟨1523546, by rfl⟩ : syracuseStep 2031395 = 3047093) B3047093
theorem B2285347 : Blo 1352995 2285347 := bstep (se 1 (by rfl) ⟨1714010, by rfl⟩ : syracuseStep 2285347 = 3428021) B3428021
theorem B2031425 : Blo 1352995 2031425 := bstep (se 2 (by rfl) ⟨761784, by rfl⟩ : syracuseStep 2031425 = 1523569) B1523569
theorem B2031443 : Blo 1352995 2031443 := bstep (se 1 (by rfl) ⟨1523582, by rfl⟩ : syracuseStep 2031443 = 3047165) B3047165
theorem B2031473 : Blo 1352995 2031473 := bstep (se 2 (by rfl) ⟨761802, by rfl⟩ : syracuseStep 2031473 = 1523605) B1523605
theorem B1523587 : Blo 1352995 1523587 := bstep (se 1 (by rfl) ⟨1142690, by rfl⟩ : syracuseStep 1523587 = 2285381) B2285381
theorem B2031491 : Blo 1352995 2031491 := bstep (se 1 (by rfl) ⟨1523618, by rfl⟩ : syracuseStep 2031491 = 3047237) B3047237
theorem B2031521 : Blo 1352995 2031521 := bstep (se 2 (by rfl) ⟨761820, by rfl⟩ : syracuseStep 2031521 = 1523641) B1523641
theorem B2285489 : Blo 1352995 2285489 := bstep (se 2 (by rfl) ⟨857058, by rfl⟩ : syracuseStep 2285489 = 1714117) B1714117
theorem B3047345 : Blo 1352995 3047345 := bstep (se 2 (by rfl) ⟨1142754, by rfl⟩ : syracuseStep 3047345 = 2285509) B2285509
theorem B2031539 : Blo 1352995 2031539 := bstep (se 1 (by rfl) ⟨1523654, by rfl⟩ : syracuseStep 2031539 = 3047309) B3047309
theorem B3047363 : Blo 1352995 3047363 := bstep (se 1 (by rfl) ⟨2285522, by rfl⟩ : syracuseStep 3047363 = 4571045) B4571045
theorem B2031569 : Blo 1352995 2031569 := bstep (se 2 (by rfl) ⟨761838, by rfl⟩ : syracuseStep 2031569 = 1523677) B1523677
theorem B2031587 : Blo 1352995 2031587 := bstep (se 1 (by rfl) ⟨1523690, by rfl⟩ : syracuseStep 2031587 = 3047381) B3047381
theorem B3047435 : Blo 1352995 3047435 := bstep (se 1 (by rfl) ⟨2285576, by rfl⟩ : syracuseStep 3047435 = 4571153) B4571153
theorem B2031641 : Blo 1352995 2031641 := bstep (se 2 (by rfl) ⟨761865, by rfl⟩ : syracuseStep 2031641 = 1523731) B1523731
theorem B1523767 : Blo 1352995 1523767 := bstep (se 1 (by rfl) ⟨1142825, by rfl⟩ : syracuseStep 1523767 = 2285651) B2285651
theorem B3047489 : Blo 1352995 3047489 := bstep (se 2 (by rfl) ⟨1142808, by rfl⟩ : syracuseStep 3047489 = 2285617) B2285617
theorem B2031755 : Blo 1352995 2031755 := bstep (se 1 (by rfl) ⟨1523816, by rfl⟩ : syracuseStep 2031755 = 3047633) B3047633
theorem B2031767 : Blo 1352995 2031767 := bstep (se 1 (by rfl) ⟨1523825, by rfl⟩ : syracuseStep 2031767 = 3047651) B3047651
theorem B4571315 : Blo 1352995 4571315 := bstep (se 1 (by rfl) ⟨3428486, by rfl⟩ : syracuseStep 4571315 = 6856973) B6856973
theorem B24715469 : Blo 1352995 24715469 := bstep (se 3 (by rfl) ⟨4634150, by rfl⟩ : syracuseStep 24715469 = 9268301) B9268301
theorem B2031833 : Blo 1352995 2031833 := bstep (se 2 (by rfl) ⟨761937, by rfl⟩ : syracuseStep 2031833 = 1523875) B1523875
theorem B5865689 : Blo 1352995 5865689 := bstep (se 2 (by rfl) ⟨2199633, by rfl⟩ : syracuseStep 5865689 = 4399267) B4399267
theorem B1523947 : Blo 1352995 1523947 := bstep (se 1 (by rfl) ⟨1142960, by rfl⟩ : syracuseStep 1523947 = 2285921) B2285921
theorem B11559185 : Blo 1352995 11559185 := bstep (se 2 (by rfl) ⟨4334694, by rfl⟩ : syracuseStep 11559185 = 8669389) B8669389
theorem B5783831 : Blo 1352995 5783831 := bstep (se 1 (by rfl) ⟨4337873, by rfl⟩ : syracuseStep 5783831 = 8675747) B8675747
theorem B3047705 : Blo 1352995 3047705 := bstep (se 2 (by rfl) ⟨1142889, by rfl⟩ : syracuseStep 3047705 = 2285779) B2285779
theorem B2031947 : Blo 1352995 2031947 := bstep (se 1 (by rfl) ⟨1523960, by rfl⟩ : syracuseStep 2031947 = 3047921) B3047921
theorem B2031959 : Blo 1352995 2031959 := bstep (se 1 (by rfl) ⟨1523969, by rfl⟩ : syracuseStep 2031959 = 3047939) B3047939
theorem B1524055 : Blo 1352995 1524055 := bstep (se 1 (by rfl) ⟨1143041, by rfl⟩ : syracuseStep 1524055 = 2286083) B2286083
theorem B3047795 : Blo 1352995 3047795 := bstep (se 1 (by rfl) ⟨2285846, by rfl⟩ : syracuseStep 3047795 = 4571693) B4571693
theorem B2441611 : Blo 1352995 2441611 := bstep (se 1 (by rfl) ⟨1831208, by rfl⟩ : syracuseStep 2441611 = 3662417) B3662417
theorem B3047831 : Blo 1352995 3047831 := bstep (se 1 (by rfl) ⟨2285873, by rfl⟩ : syracuseStep 3047831 = 4571747) B4571747
theorem B2285975 : Blo 1352995 2285975 := bstep (se 1 (by rfl) ⟨1714481, by rfl⟩ : syracuseStep 2285975 = 3428963) B3428963
theorem B2032025 : Blo 1352995 2032025 := bstep (se 2 (by rfl) ⟨762009, by rfl⟩ : syracuseStep 2032025 = 1524019) B1524019
theorem B23142833 : Blo 1352995 23142833 := bstep (se 2 (by rfl) ⟨8678562, by rfl⟩ : syracuseStep 23142833 = 17357125) B17357125
theorem B4571585 : Blo 1352995 4571585 := bstep (se 2 (by rfl) ⟨1714344, by rfl⟩ : syracuseStep 4571585 = 3428689) B3428689
theorem B2032139 : Blo 1352995 2032139 := bstep (se 1 (by rfl) ⟨1524104, by rfl⟩ : syracuseStep 2032139 = 3048209) B3048209
theorem B1524235 : Blo 1352995 1524235 := bstep (se 1 (by rfl) ⟨1143176, by rfl⟩ : syracuseStep 1524235 = 2286353) B2286353
theorem B32924177 : Blo 1352995 32924177 := bstep (se 2 (by rfl) ⟨12346566, by rfl⟩ : syracuseStep 32924177 = 24693133) B24693133
theorem B13017617 : Blo 1352995 13017617 := bstep (se 2 (by rfl) ⟨4881606, by rfl⟩ : syracuseStep 13017617 = 9763213) B9763213
theorem B2286103 : Blo 1352995 2286103 := bstep (se 1 (by rfl) ⟨1714577, by rfl⟩ : syracuseStep 2286103 = 3429155) B3429155
theorem B2032151 : Blo 1352995 2032151 := bstep (se 1 (by rfl) ⟨1524113, by rfl⟩ : syracuseStep 2032151 = 3048227) B3048227
theorem B3048011 : Blo 1352995 3048011 := bstep (se 1 (by rfl) ⟨2286008, by rfl⟩ : syracuseStep 3048011 = 4572017) B4572017
theorem B2032217 : Blo 1352995 2032217 := bstep (se 2 (by rfl) ⟨762081, by rfl⟩ : syracuseStep 2032217 = 1524163) B1524163
theorem B5489245 : Blo 1352995 5489245 := bstep (se 3 (by rfl) ⟨1029233, by rfl⟩ : syracuseStep 5489245 = 2058467) B2058467
theorem B1524343 : Blo 1352995 1524343 := bstep (se 1 (by rfl) ⟨1143257, by rfl⟩ : syracuseStep 1524343 = 2286515) B2286515
theorem B3048065 : Blo 1352995 3048065 := bstep (se 2 (by rfl) ⟨1143024, by rfl⟩ : syracuseStep 3048065 = 2286049) B2286049
theorem B2032331 : Blo 1352995 2032331 := bstep (se 1 (by rfl) ⟨1524248, by rfl⟩ : syracuseStep 2032331 = 3048497) B3048497
theorem B2032343 : Blo 1352995 2032343 := bstep (se 1 (by rfl) ⟨1524257, by rfl⟩ : syracuseStep 2032343 = 3048515) B3048515
theorem B2892505 : Blo 1352995 2892505 := bstep (se 2 (by rfl) ⟨1084689, by rfl⟩ : syracuseStep 2892505 = 2169379) B2169379
theorem B2032409 : Blo 1352995 2032409 := bstep (se 2 (by rfl) ⟨762153, by rfl⟩ : syracuseStep 2032409 = 1524307) B1524307
theorem B25051949 : Blo 1352995 25051949 := bstep (se 3 (by rfl) ⟨4697240, by rfl⟩ : syracuseStep 25051949 = 9394481) B9394481
theorem B3425075 : Blo 1352995 3425075 := bstep (se 1 (by rfl) ⟨2568806, by rfl⟩ : syracuseStep 3425075 = 5137613) B5137613
theorem B5489473 : Blo 1352995 5489473 := bstep (se 2 (by rfl) ⟨2058552, by rfl⟩ : syracuseStep 5489473 = 4117105) B4117105
theorem B1712983 : Blo 1352995 1712983 := bstep (se 1 (by rfl) ⟨1284737, by rfl⟩ : syracuseStep 1712983 = 2569475) B2569475
theorem B3048281 : Blo 1352995 3048281 := bstep (se 2 (by rfl) ⟨1143105, by rfl⟩ : syracuseStep 3048281 = 2286211) B2286211
theorem B3048371 : Blo 1352995 3048371 := bstep (se 1 (by rfl) ⟨2286278, by rfl⟩ : syracuseStep 3048371 = 4572557) B4572557
theorem B3048407 : Blo 1352995 3048407 := bstep (se 1 (by rfl) ⟨2286305, by rfl⟩ : syracuseStep 3048407 = 4572611) B4572611
theorem B4572125 : Blo 1352995 4572125 := bstep (se 3 (by rfl) ⟨857273, by rfl⟩ : syracuseStep 4572125 = 1714547) B1714547
theorem B6177809 : Blo 1352995 6177809 := bstep (se 2 (by rfl) ⟨2316678, by rfl⟩ : syracuseStep 6177809 = 4633357) B4633357
theorem B29295685 : Blo 1352995 29295685 := bstep (se 4 (by rfl) ⟨2746470, by rfl⟩ : syracuseStep 29295685 = 5492941) B5492941
theorem B11289701 : Blo 1352995 11289701 := bstep (se 4 (by rfl) ⟨1058409, by rfl⟩ : syracuseStep 11289701 = 2116819) B2116819
theorem B3048587 : Blo 1352995 3048587 := bstep (se 1 (by rfl) ⟨2286440, by rfl⟩ : syracuseStep 3048587 = 4572881) B4572881
theorem B5489815 : Blo 1352995 5489815 := bstep (se 1 (by rfl) ⟨4117361, by rfl⟩ : syracuseStep 5489815 = 8234723) B8234723
theorem B4334771 : Blo 1352995 4334771 := bstep (se 1 (by rfl) ⟨3251078, by rfl⟩ : syracuseStep 4334771 = 6502157) B6502157
theorem B3048641 : Blo 1352995 3048641 := bstep (se 2 (by rfl) ⟨1143240, by rfl⟩ : syracuseStep 3048641 = 2286481) B2286481
theorem B6177995 : Blo 1352995 6177995 := bstep (se 1 (by rfl) ⟨4633496, by rfl⟩ : syracuseStep 6177995 = 9266993) B9266993
theorem B6857945 : Blo 1352995 6857945 := bstep (se 2 (by rfl) ⟨2571729, by rfl⟩ : syracuseStep 6857945 = 5143459) B5143459
theorem B79127813 : Blo 1352995 79127813 := bstep (se 4 (by rfl) ⟨7418232, by rfl⟩ : syracuseStep 79127813 = 14836465) B14836465
theorem B1353003 : Blo 1352995 1353003 := bstep (se 1 (by rfl) ⟨1014752, by rfl⟩ : syracuseStep 1353003 = 2029505) B2029505
theorem B1353015 : Blo 1352995 1353015 := bstep (se 1 (by rfl) ⟨1014761, by rfl⟩ : syracuseStep 1353015 = 2029523) B2029523
theorem B1353035 : Blo 1352995 1353035 := bstep (se 1 (by rfl) ⟨1014776, by rfl⟩ : syracuseStep 1353035 = 2029553) B2029553
theorem B3425611 : Blo 1352995 3425611 := bstep (se 1 (by rfl) ⟨2569208, by rfl⟩ : syracuseStep 3425611 = 5138417) B5138417
theorem B1353047 : Blo 1352995 1353047 := bstep (se 1 (by rfl) ⟨1014785, by rfl⟩ : syracuseStep 1353047 = 2029571) B2029571
theorem B1353067 : Blo 1352995 1353067 := bstep (se 1 (by rfl) ⟨1014800, by rfl⟩ : syracuseStep 1353067 = 2029601) B2029601
theorem B1353079 : Blo 1352995 1353079 := bstep (se 1 (by rfl) ⟨1014809, by rfl⟩ : syracuseStep 1353079 = 2029619) B2029619
theorem B1353099 : Blo 1352995 1353099 := bstep (se 1 (by rfl) ⟨1014824, by rfl⟩ : syracuseStep 1353099 = 2029649) B2029649
theorem B1353111 : Blo 1352995 1353111 := bstep (se 1 (by rfl) ⟨1014833, by rfl⟩ : syracuseStep 1353111 = 2029667) B2029667
theorem B2745751 : Blo 1352995 2745751 := bstep (se 1 (by rfl) ⟨2059313, by rfl⟩ : syracuseStep 2745751 = 4118627) B4118627
theorem B1738135 : Blo 1352995 1738135 := bstep (se 1 (by rfl) ⟨1303601, by rfl⟩ : syracuseStep 1738135 = 2607203) B2607203
theorem B1353131 : Blo 1352995 1353131 := bstep (se 1 (by rfl) ⟨1014848, by rfl⟩ : syracuseStep 1353131 = 2029697) B2029697
theorem B1353143 : Blo 1352995 1353143 := bstep (se 1 (by rfl) ⟨1014857, by rfl⟩ : syracuseStep 1353143 = 2029715) B2029715
theorem B1353163 : Blo 1352995 1353163 := bstep (se 1 (by rfl) ⟨1014872, by rfl⟩ : syracuseStep 1353163 = 2029745) B2029745
theorem B1353175 : Blo 1352995 1353175 := bstep (se 1 (by rfl) ⟨1014881, by rfl⟩ : syracuseStep 1353175 = 2029763) B2029763
theorem B3425753 : Blo 1352995 3425753 := bstep (se 2 (by rfl) ⟨1284657, by rfl⟩ : syracuseStep 3425753 = 2569315) B2569315
theorem B1353195 : Blo 1352995 1353195 := bstep (se 1 (by rfl) ⟨1014896, by rfl⟩ : syracuseStep 1353195 = 2029793) B2029793
theorem B1353207 : Blo 1352995 1353207 := bstep (se 1 (by rfl) ⟨1014905, by rfl⟩ : syracuseStep 1353207 = 2029811) B2029811
theorem B1353227 : Blo 1352995 1353227 := bstep (se 1 (by rfl) ⟨1014920, by rfl⟩ : syracuseStep 1353227 = 2029841) B2029841
theorem B1926679 : Blo 1352995 1926679 := bstep (se 1 (by rfl) ⟨1445009, by rfl⟩ : syracuseStep 1926679 = 2890019) B2890019
theorem B1353239 : Blo 1352995 1353239 := bstep (se 1 (by rfl) ⟨1014929, by rfl⟩ : syracuseStep 1353239 = 2029859) B2029859
theorem B1353259 : Blo 1352995 1353259 := bstep (se 1 (by rfl) ⟨1014944, by rfl⟩ : syracuseStep 1353259 = 2029889) B2029889
theorem B1353271 : Blo 1352995 1353271 := bstep (se 1 (by rfl) ⟨1014953, by rfl⟩ : syracuseStep 1353271 = 2029907) B2029907
theorem B1353291 : Blo 1352995 1353291 := bstep (se 1 (by rfl) ⟨1014968, by rfl⟩ : syracuseStep 1353291 = 2029937) B2029937
theorem B5563979 : Blo 1352995 5563979 := bstep (se 1 (by rfl) ⟨4172984, by rfl⟩ : syracuseStep 5563979 = 8345969) B8345969
theorem B5490251 : Blo 1352995 5490251 := bstep (se 1 (by rfl) ⟨4117688, by rfl⟩ : syracuseStep 5490251 = 8235377) B8235377
theorem B1353303 : Blo 1352995 1353303 := bstep (se 1 (by rfl) ⟨1014977, by rfl⟩ : syracuseStep 1353303 = 2029955) B2029955
theorem B1353323 : Blo 1352995 1353323 := bstep (se 1 (by rfl) ⟨1014992, by rfl⟩ : syracuseStep 1353323 = 2029985) B2029985
theorem B1353335 : Blo 1352995 1353335 := bstep (se 1 (by rfl) ⟨1015001, by rfl⟩ : syracuseStep 1353335 = 2030003) B2030003
theorem B1353355 : Blo 1352995 1353355 := bstep (se 1 (by rfl) ⟨1015016, by rfl⟩ : syracuseStep 1353355 = 2030033) B2030033
theorem B1353367 : Blo 1352995 1353367 := bstep (se 1 (by rfl) ⟨1015025, by rfl⟩ : syracuseStep 1353367 = 2030051) B2030051
theorem B2860697 : Blo 1352995 2860697 := bstep (se 2 (by rfl) ⟨1072761, by rfl⟩ : syracuseStep 2860697 = 2145523) B2145523
theorem B1353387 : Blo 1352995 1353387 := bstep (se 1 (by rfl) ⟨1015040, by rfl⟩ : syracuseStep 1353387 = 2030081) B2030081
theorem B5138099 : Blo 1352995 5138099 := bstep (se 1 (by rfl) ⟨3853574, by rfl⟩ : syracuseStep 5138099 = 7707149) B7707149
theorem B1353399 : Blo 1352995 1353399 := bstep (se 1 (by rfl) ⟨1015049, by rfl⟩ : syracuseStep 1353399 = 2030099) B2030099
theorem B5138113 : Blo 1352995 5138113 := bstep (se 2 (by rfl) ⟨1926792, by rfl⟩ : syracuseStep 5138113 = 3853585) B3853585
theorem B1353419 : Blo 1352995 1353419 := bstep (se 1 (by rfl) ⟨1015064, by rfl⟩ : syracuseStep 1353419 = 2030129) B2030129
theorem B1353431 : Blo 1352995 1353431 := bstep (se 1 (by rfl) ⟨1015073, by rfl⟩ : syracuseStep 1353431 = 2030147) B2030147
theorem B1353451 : Blo 1352995 1353451 := bstep (se 1 (by rfl) ⟨1015088, by rfl⟩ : syracuseStep 1353451 = 2030177) B2030177
theorem B1353463 : Blo 1352995 1353463 := bstep (se 1 (by rfl) ⟨1015097, by rfl⟩ : syracuseStep 1353463 = 2030195) B2030195
theorem B1353483 : Blo 1352995 1353483 := bstep (se 1 (by rfl) ⟨1015112, by rfl⟩ : syracuseStep 1353483 = 2030225) B2030225
theorem B1353495 : Blo 1352995 1353495 := bstep (se 1 (by rfl) ⟨1015121, by rfl⟩ : syracuseStep 1353495 = 2030243) B2030243
theorem B10282787 : Blo 1352995 10282787 := bstep (se 1 (by rfl) ⟨7712090, by rfl⟩ : syracuseStep 10282787 = 15424181) B15424181
theorem B1353515 : Blo 1352995 1353515 := bstep (se 1 (by rfl) ⟨1015136, by rfl⟩ : syracuseStep 1353515 = 2030273) B2030273
theorem B1353527 : Blo 1352995 1353527 := bstep (se 1 (by rfl) ⟨1015145, by rfl⟩ : syracuseStep 1353527 = 2030291) B2030291
theorem B1353547 : Blo 1352995 1353547 := bstep (se 1 (by rfl) ⟨1015160, by rfl⟩ : syracuseStep 1353547 = 2030321) B2030321
theorem B1353559 : Blo 1352995 1353559 := bstep (se 1 (by rfl) ⟨1015169, by rfl⟩ : syracuseStep 1353559 = 2030339) B2030339
theorem B1353579 : Blo 1352995 1353579 := bstep (se 1 (by rfl) ⟨1015184, by rfl⟩ : syracuseStep 1353579 = 2030369) B2030369
theorem B1353591 : Blo 1352995 1353591 := bstep (se 1 (by rfl) ⟨1015193, by rfl⟩ : syracuseStep 1353591 = 2030387) B2030387
theorem B1353611 : Blo 1352995 1353611 := bstep (se 1 (by rfl) ⟨1015208, by rfl⟩ : syracuseStep 1353611 = 2030417) B2030417
theorem B1353623 : Blo 1352995 1353623 := bstep (se 1 (by rfl) ⟨1015217, by rfl⟩ : syracuseStep 1353623 = 2030435) B2030435
theorem B1353643 : Blo 1352995 1353643 := bstep (se 1 (by rfl) ⟨1015232, by rfl⟩ : syracuseStep 1353643 = 2030465) B2030465
theorem B1353655 : Blo 1352995 1353655 := bstep (se 1 (by rfl) ⟨1015241, by rfl⟩ : syracuseStep 1353655 = 2030483) B2030483
theorem B1353675 : Blo 1352995 1353675 := bstep (se 1 (by rfl) ⟨1015256, by rfl⟩ : syracuseStep 1353675 = 2030513) B2030513
theorem B1353687 : Blo 1352995 1353687 := bstep (se 1 (by rfl) ⟨1015265, by rfl⟩ : syracuseStep 1353687 = 2030531) B2030531
theorem B1353707 : Blo 1352995 1353707 := bstep (se 1 (by rfl) ⟨1015280, by rfl⟩ : syracuseStep 1353707 = 2030561) B2030561
theorem B2893811 : Blo 1352995 2893811 := bstep (se 1 (by rfl) ⟨2170358, by rfl⟩ : syracuseStep 2893811 = 4340717) B4340717
theorem B1353719 : Blo 1352995 1353719 := bstep (se 1 (by rfl) ⟨1015289, by rfl⟩ : syracuseStep 1353719 = 2030579) B2030579
theorem B1353739 : Blo 1352995 1353739 := bstep (se 1 (by rfl) ⟨1015304, by rfl⟩ : syracuseStep 1353739 = 2030609) B2030609
theorem B1353751 : Blo 1352995 1353751 := bstep (se 1 (by rfl) ⟨1015313, by rfl⟩ : syracuseStep 1353751 = 2030627) B2030627
theorem B1353771 : Blo 1352995 1353771 := bstep (se 1 (by rfl) ⟨1015328, by rfl⟩ : syracuseStep 1353771 = 2030657) B2030657
theorem B1353783 : Blo 1352995 1353783 := bstep (se 1 (by rfl) ⟨1015337, by rfl⟩ : syracuseStep 1353783 = 2030675) B2030675
theorem B1927243 : Blo 1352995 1927243 := bstep (se 1 (by rfl) ⟨1445432, by rfl⟩ : syracuseStep 1927243 = 2890865) B2890865
theorem B1353803 : Blo 1352995 1353803 := bstep (se 1 (by rfl) ⟨1015352, by rfl⟩ : syracuseStep 1353803 = 2030705) B2030705
theorem B3254347 : Blo 1352995 3254347 := bstep (se 1 (by rfl) ⟨2440760, by rfl⟩ : syracuseStep 3254347 = 4881521) B4881521
theorem B1353815 : Blo 1352995 1353815 := bstep (se 1 (by rfl) ⟨1015361, by rfl⟩ : syracuseStep 1353815 = 2030723) B2030723
theorem B1353835 : Blo 1352995 1353835 := bstep (se 1 (by rfl) ⟨1015376, by rfl⟩ : syracuseStep 1353835 = 2030753) B2030753
theorem B1353847 : Blo 1352995 1353847 := bstep (se 1 (by rfl) ⟨1015385, by rfl⟩ : syracuseStep 1353847 = 2030771) B2030771
theorem B1353867 : Blo 1352995 1353867 := bstep (se 1 (by rfl) ⟨1015400, by rfl⟩ : syracuseStep 1353867 = 2030801) B2030801
theorem B1353879 : Blo 1352995 1353879 := bstep (se 1 (by rfl) ⟨1015409, by rfl⟩ : syracuseStep 1353879 = 2030819) B2030819
theorem B3254423 : Blo 1352995 3254423 := bstep (se 1 (by rfl) ⟨2440817, by rfl⟩ : syracuseStep 3254423 = 4881635) B4881635
theorem B1353899 : Blo 1352995 1353899 := bstep (se 1 (by rfl) ⟨1015424, by rfl⟩ : syracuseStep 1353899 = 2030849) B2030849
theorem B1353911 : Blo 1352995 1353911 := bstep (se 1 (by rfl) ⟨1015433, by rfl⟩ : syracuseStep 1353911 = 2030867) B2030867
theorem B1353931 : Blo 1352995 1353931 := bstep (se 1 (by rfl) ⟨1015448, by rfl⟩ : syracuseStep 1353931 = 2030897) B2030897
theorem B1353943 : Blo 1352995 1353943 := bstep (se 1 (by rfl) ⟨1015457, by rfl⟩ : syracuseStep 1353943 = 2030915) B2030915
theorem B1353963 : Blo 1352995 1353963 := bstep (se 1 (by rfl) ⟨1015472, by rfl⟩ : syracuseStep 1353963 = 2030945) B2030945
theorem B1353975 : Blo 1352995 1353975 := bstep (se 1 (by rfl) ⟨1015481, by rfl⟩ : syracuseStep 1353975 = 2030963) B2030963
theorem B1353995 : Blo 1352995 1353995 := bstep (se 1 (by rfl) ⟨1015496, by rfl⟩ : syracuseStep 1353995 = 2030993) B2030993
theorem B3426583 : Blo 1352995 3426583 := bstep (se 1 (by rfl) ⟨2569937, by rfl⟩ : syracuseStep 3426583 = 5139875) B5139875
theorem B1354007 : Blo 1352995 1354007 := bstep (se 1 (by rfl) ⟨1015505, by rfl⟩ : syracuseStep 1354007 = 2031011) B2031011
theorem B1354027 : Blo 1352995 1354027 := bstep (se 1 (by rfl) ⟨1015520, by rfl⟩ : syracuseStep 1354027 = 2031041) B2031041
theorem B1354039 : Blo 1352995 1354039 := bstep (se 1 (by rfl) ⟨1015529, by rfl⟩ : syracuseStep 1354039 = 2031059) B2031059
theorem B17353025 : Blo 1352995 17353025 := bstep (se 2 (by rfl) ⟨6507384, by rfl⟩ : syracuseStep 17353025 = 13014769) B13014769
theorem B1354059 : Blo 1352995 1354059 := bstep (se 1 (by rfl) ⟨1015544, by rfl⟩ : syracuseStep 1354059 = 2031089) B2031089
theorem B1354071 : Blo 1352995 1354071 := bstep (se 1 (by rfl) ⟨1015553, by rfl⟩ : syracuseStep 1354071 = 2031107) B2031107
theorem B6179165 : Blo 1352995 6179165 := bstep (se 3 (by rfl) ⟨1158593, by rfl⟩ : syracuseStep 6179165 = 2317187) B2317187
theorem B1354091 : Blo 1352995 1354091 := bstep (se 1 (by rfl) ⟨1015568, by rfl⟩ : syracuseStep 1354091 = 2031137) B2031137
theorem B55568753 : Blo 1352995 55568753 := bstep (se 2 (by rfl) ⟨20838282, by rfl⟩ : syracuseStep 55568753 = 41676565) B41676565
theorem B1354103 : Blo 1352995 1354103 := bstep (se 1 (by rfl) ⟨1015577, by rfl⟩ : syracuseStep 1354103 = 2031155) B2031155
theorem B1354123 : Blo 1352995 1354123 := bstep (se 1 (by rfl) ⟨1015592, by rfl⟩ : syracuseStep 1354123 = 2031185) B2031185
theorem B1354135 : Blo 1352995 1354135 := bstep (se 1 (by rfl) ⟨1015601, by rfl⟩ : syracuseStep 1354135 = 2031203) B2031203
theorem B1354155 : Blo 1352995 1354155 := bstep (se 1 (by rfl) ⟨1015616, by rfl⟩ : syracuseStep 1354155 = 2031233) B2031233
theorem B1354167 : Blo 1352995 1354167 := bstep (se 1 (by rfl) ⟨1015625, by rfl⟩ : syracuseStep 1354167 = 2031251) B2031251
theorem B1354187 : Blo 1352995 1354187 := bstep (se 1 (by rfl) ⟨1015640, by rfl⟩ : syracuseStep 1354187 = 2031281) B2031281
theorem B1354199 : Blo 1352995 1354199 := bstep (se 1 (by rfl) ⟨1015649, by rfl⟩ : syracuseStep 1354199 = 2031299) B2031299
theorem B1354219 : Blo 1352995 1354219 := bstep (se 1 (by rfl) ⟨1015664, by rfl⟩ : syracuseStep 1354219 = 2031329) B2031329
theorem B1354231 : Blo 1352995 1354231 := bstep (se 1 (by rfl) ⟨1015673, by rfl⟩ : syracuseStep 1354231 = 2031347) B2031347
theorem B1354251 : Blo 1352995 1354251 := bstep (se 1 (by rfl) ⟨1015688, by rfl⟩ : syracuseStep 1354251 = 2031377) B2031377
theorem B1714699 : Blo 1352995 1714699 := bstep (se 1 (by rfl) ⟨1286024, by rfl⟩ : syracuseStep 1714699 = 2572049) B2572049
theorem B1354263 : Blo 1352995 1354263 := bstep (se 1 (by rfl) ⟨1015697, by rfl⟩ : syracuseStep 1354263 = 2031395) B2031395
theorem B1354283 : Blo 1352995 1354283 := bstep (se 1 (by rfl) ⟨1015712, by rfl⟩ : syracuseStep 1354283 = 2031425) B2031425
theorem B1354295 : Blo 1352995 1354295 := bstep (se 1 (by rfl) ⟨1015721, by rfl⟩ : syracuseStep 1354295 = 2031443) B2031443
theorem B1354315 : Blo 1352995 1354315 := bstep (se 1 (by rfl) ⟨1015736, by rfl⟩ : syracuseStep 1354315 = 2031473) B2031473
theorem B1354327 : Blo 1352995 1354327 := bstep (se 1 (by rfl) ⟨1015745, by rfl⟩ : syracuseStep 1354327 = 2031491) B2031491
theorem B1354347 : Blo 1352995 1354347 := bstep (se 1 (by rfl) ⟨1015760, by rfl⟩ : syracuseStep 1354347 = 2031521) B2031521
theorem B1354359 : Blo 1352995 1354359 := bstep (se 1 (by rfl) ⟨1015769, by rfl⟩ : syracuseStep 1354359 = 2031539) B2031539
theorem B1354379 : Blo 1352995 1354379 := bstep (se 1 (by rfl) ⟨1015784, by rfl⟩ : syracuseStep 1354379 = 2031569) B2031569
theorem B1354391 : Blo 1352995 1354391 := bstep (se 1 (by rfl) ⟨1015793, by rfl⟩ : syracuseStep 1354391 = 2031587) B2031587
theorem B1354411 : Blo 1352995 1354411 := bstep (se 1 (by rfl) ⟨1015808, by rfl⟩ : syracuseStep 1354411 = 2031617) B2031617
theorem B1354423 : Blo 1352995 1354423 := bstep (se 1 (by rfl) ⟨1015817, by rfl⟩ : syracuseStep 1354423 = 2031635) B2031635
theorem B3427019 : Blo 1352995 3427019 := bstep (se 1 (by rfl) ⟨2570264, by rfl⟩ : syracuseStep 3427019 = 5140529) B5140529
theorem B1354443 : Blo 1352995 1354443 := bstep (se 1 (by rfl) ⟨1015832, by rfl⟩ : syracuseStep 1354443 = 2031665) B2031665
theorem B1354455 : Blo 1352995 1354455 := bstep (se 1 (by rfl) ⟨1015841, by rfl⟩ : syracuseStep 1354455 = 2031683) B2031683
theorem B7424729 : Blo 1352995 7424729 := bstep (se 2 (by rfl) ⟨2784273, by rfl⟩ : syracuseStep 7424729 = 5568547) B5568547
theorem B1354475 : Blo 1352995 1354475 := bstep (se 1 (by rfl) ⟨1015856, by rfl⟩ : syracuseStep 1354475 = 2031713) B2031713
theorem B1354487 : Blo 1352995 1354487 := bstep (se 1 (by rfl) ⟨1015865, by rfl⟩ : syracuseStep 1354487 = 2031731) B2031731
theorem B1354507 : Blo 1352995 1354507 := bstep (se 1 (by rfl) ⟨1015880, by rfl⟩ : syracuseStep 1354507 = 2031761) B2031761
theorem B1354519 : Blo 1352995 1354519 := bstep (se 1 (by rfl) ⟨1015889, by rfl⟩ : syracuseStep 1354519 = 2031779) B2031779
theorem B1354539 : Blo 1352995 1354539 := bstep (se 1 (by rfl) ⟨1015904, by rfl⟩ : syracuseStep 1354539 = 2031809) B2031809
theorem B6859565 : Blo 1352995 6859565 := bstep (se 3 (by rfl) ⟨1286168, by rfl⟩ : syracuseStep 6859565 = 2572337) B2572337
theorem B5860147 : Blo 1352995 5860147 := bstep (se 1 (by rfl) ⟨4395110, by rfl⟩ : syracuseStep 5860147 = 8790221) B8790221
theorem B1354551 : Blo 1352995 1354551 := bstep (se 1 (by rfl) ⟨1015913, by rfl⟩ : syracuseStep 1354551 = 2031827) B2031827
theorem B7818049 : Blo 1352995 7818049 := bstep (se 2 (by rfl) ⟨2931768, by rfl⟩ : syracuseStep 7818049 = 5863537) B5863537
theorem B1354571 : Blo 1352995 1354571 := bstep (se 1 (by rfl) ⟨1015928, by rfl⟩ : syracuseStep 1354571 = 2031857) B2031857
theorem B1354583 : Blo 1352995 1354583 := bstep (se 1 (by rfl) ⟨1015937, by rfl⟩ : syracuseStep 1354583 = 2031875) B2031875
theorem B1354603 : Blo 1352995 1354603 := bstep (se 1 (by rfl) ⟨1015952, by rfl⟩ : syracuseStep 1354603 = 2031905) B2031905
theorem B1354615 : Blo 1352995 1354615 := bstep (se 1 (by rfl) ⟨1015961, by rfl⟩ : syracuseStep 1354615 = 2031923) B2031923
theorem B1354635 : Blo 1352995 1354635 := bstep (se 1 (by rfl) ⟨1015976, by rfl⟩ : syracuseStep 1354635 = 2031953) B2031953
theorem B1354647 : Blo 1352995 1354647 := bstep (se 1 (by rfl) ⟨1015985, by rfl⟩ : syracuseStep 1354647 = 2031971) B2031971
theorem B1354667 : Blo 1352995 1354667 := bstep (se 1 (by rfl) ⟨1016000, by rfl⟩ : syracuseStep 1354667 = 2032001) B2032001
theorem B1354679 : Blo 1352995 1354679 := bstep (se 1 (by rfl) ⟨1016009, by rfl⟩ : syracuseStep 1354679 = 2032019) B2032019
theorem B1354699 : Blo 1352995 1354699 := bstep (se 1 (by rfl) ⟨1016024, by rfl⟩ : syracuseStep 1354699 = 2032049) B2032049
theorem B1354711 : Blo 1352995 1354711 := bstep (se 1 (by rfl) ⟨1016033, by rfl⟩ : syracuseStep 1354711 = 2032067) B2032067
theorem B1354731 : Blo 1352995 1354731 := bstep (se 1 (by rfl) ⟨1016048, by rfl⟩ : syracuseStep 1354731 = 2032097) B2032097
theorem B1354743 : Blo 1352995 1354743 := bstep (se 1 (by rfl) ⟨1016057, by rfl⟩ : syracuseStep 1354743 = 2032115) B2032115
theorem B1354763 : Blo 1352995 1354763 := bstep (se 1 (by rfl) ⟨1016072, by rfl⟩ : syracuseStep 1354763 = 2032145) B2032145
theorem B1354775 : Blo 1352995 1354775 := bstep (se 1 (by rfl) ⟨1016081, by rfl⟩ : syracuseStep 1354775 = 2032163) B2032163
theorem B1354795 : Blo 1352995 1354795 := bstep (se 1 (by rfl) ⟨1016096, by rfl⟩ : syracuseStep 1354795 = 2032193) B2032193
theorem B1354807 : Blo 1352995 1354807 := bstep (se 1 (by rfl) ⟨1016105, by rfl⟩ : syracuseStep 1354807 = 2032211) B2032211
theorem B3427393 : Blo 1352995 3427393 := bstep (se 2 (by rfl) ⟨1285272, by rfl⟩ : syracuseStep 3427393 = 2570545) B2570545
theorem B1354827 : Blo 1352995 1354827 := bstep (se 1 (by rfl) ⟨1016120, by rfl⟩ : syracuseStep 1354827 = 2032241) B2032241
theorem B1354839 : Blo 1352995 1354839 := bstep (se 1 (by rfl) ⟨1016129, by rfl⟩ : syracuseStep 1354839 = 2032259) B2032259
theorem B1354859 : Blo 1352995 1354859 := bstep (se 1 (by rfl) ⟨1016144, by rfl⟩ : syracuseStep 1354859 = 2032289) B2032289
theorem B1354871 : Blo 1352995 1354871 := bstep (se 1 (by rfl) ⟨1016153, by rfl⟩ : syracuseStep 1354871 = 2032307) B2032307
theorem B1354891 : Blo 1352995 1354891 := bstep (se 1 (by rfl) ⟨1016168, by rfl⟩ : syracuseStep 1354891 = 2032337) B2032337
theorem B1354903 : Blo 1352995 1354903 := bstep (se 1 (by rfl) ⟨1016177, by rfl⟩ : syracuseStep 1354903 = 2032355) B2032355
theorem B1445035 : Blo 1352995 1445035 := bstep (se 1 (by rfl) ⟨1083776, by rfl⟩ : syracuseStep 1445035 = 2167553) B2167553
theorem B1354923 : Blo 1352995 1354923 := bstep (se 1 (by rfl) ⟨1016192, by rfl⟩ : syracuseStep 1354923 = 2032385) B2032385
theorem B5491891 : Blo 1352995 5491891 := bstep (se 1 (by rfl) ⟨4118918, by rfl⟩ : syracuseStep 5491891 = 8237837) B8237837
theorem B1354935 : Blo 1352995 1354935 := bstep (se 1 (by rfl) ⟨1016201, by rfl⟩ : syracuseStep 1354935 = 2032403) B2032403
theorem B1354955 : Blo 1352995 1354955 := bstep (se 1 (by rfl) ⟨1016216, by rfl⟩ : syracuseStep 1354955 = 2032433) B2032433
theorem B1354967 : Blo 1352995 1354967 := bstep (se 1 (by rfl) ⟨1016225, by rfl⟩ : syracuseStep 1354967 = 2032451) B2032451
theorem B1354987 : Blo 1352995 1354987 := bstep (se 1 (by rfl) ⟨1016240, by rfl⟩ : syracuseStep 1354987 = 2032481) B2032481
theorem B6180275 : Blo 1352995 6180275 := bstep (se 1 (by rfl) ⟨4635206, by rfl⟩ : syracuseStep 6180275 = 9270413) B9270413
theorem B6852113 : Blo 1352995 6852113 := bstep (se 2 (by rfl) ⟨2569542, by rfl⟩ : syracuseStep 6852113 = 5139085) B5139085
theorem B7712273 : Blo 1352995 7712273 := bstep (se 2 (by rfl) ⟨2892102, by rfl⟩ : syracuseStep 7712273 = 5784205) B5784205
theorem B1928729 : Blo 1352995 1928729 := bstep (se 2 (by rfl) ⟨723273, by rfl⟩ : syracuseStep 1928729 = 1446547) B1446547
theorem B5140043 : Blo 1352995 5140043 := bstep (se 1 (by rfl) ⟨3855032, by rfl⟩ : syracuseStep 5140043 = 7710065) B7710065
theorem B4566617 : Blo 1352995 4566617 := bstep (se 2 (by rfl) ⟨1712481, by rfl⟩ : syracuseStep 4566617 = 3424963) B3424963
theorem B5140057 : Blo 1352995 5140057 := bstep (se 2 (by rfl) ⟨1927521, by rfl⟩ : syracuseStep 5140057 = 3855043) B3855043
theorem B5787281 : Blo 1352995 5787281 := bstep (se 2 (by rfl) ⟨2170230, by rfl⟩ : syracuseStep 5787281 = 4340461) B4340461
theorem B3427991 : Blo 1352995 3427991 := bstep (se 1 (by rfl) ⟨2570993, by rfl⟩ : syracuseStep 3427991 = 5141987) B5141987
theorem B6852275 : Blo 1352995 6852275 := bstep (se 1 (by rfl) ⟨5139206, by rfl⟩ : syracuseStep 6852275 = 10278413) B10278413
theorem B2780887 : Blo 1352995 2780887 := bstep (se 1 (by rfl) ⟨2085665, by rfl⟩ : syracuseStep 2780887 = 4171331) B4171331
theorem B3854155 : Blo 1352995 3854155 := bstep (se 1 (by rfl) ⟨2890616, by rfl⟩ : syracuseStep 3854155 = 5781233) B5781233
theorem B7712729 : Blo 1352995 7712729 := bstep (se 2 (by rfl) ⟨2892273, by rfl⟩ : syracuseStep 7712729 = 5784547) B5784547
theorem B5779421 : Blo 1352995 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B3854429 : Blo 1352995 3854429 := bstep (se 3 (by rfl) ⟨722705, by rfl⟩ : syracuseStep 3854429 = 1445411) B1445411
theorem B7319645 : Blo 1352995 7319645 := bstep (se 3 (by rfl) ⟨1372433, by rfl⟩ : syracuseStep 7319645 = 2744867) B2744867
theorem B1446103 : Blo 1352995 1446103 := bstep (se 1 (by rfl) ⟨1084577, by rfl⟩ : syracuseStep 1446103 = 2169155) B2169155
theorem B8352017 : Blo 1352995 8352017 := bstep (se 2 (by rfl) ⟨3132006, by rfl⟩ : syracuseStep 8352017 = 6264013) B6264013
theorem B4567319 : Blo 1352995 4567319 := bstep (se 1 (by rfl) ⟨3425489, by rfl⟩ : syracuseStep 4567319 = 6850979) B6850979
theorem B12357953 : Blo 1352995 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B2568601 : Blo 1352995 2568601 := bstep (se 2 (by rfl) ⟨963225, by rfl⟩ : syracuseStep 2568601 = 1926451) B1926451
theorem B3428801 : Blo 1352995 3428801 := bstep (se 2 (by rfl) ⟨1285800, by rfl⟩ : syracuseStep 3428801 = 2571601) B2571601
theorem B5141015 : Blo 1352995 5141015 := bstep (se 1 (by rfl) ⟨3855761, by rfl⟩ : syracuseStep 5141015 = 7711523) B7711523
theorem B10277441 : Blo 1352995 10277441 := bstep (se 2 (by rfl) ⟨3854040, by rfl⟩ : syracuseStep 10277441 = 7708081) B7708081
theorem B4878913 : Blo 1352995 4878913 := bstep (se 2 (by rfl) ⟨1829592, by rfl⟩ : syracuseStep 4878913 = 3659185) B3659185
theorem B20845187 : Blo 1352995 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B296268515 : Blo 1352995 296268515 := bstep (se 1 (by rfl) ⟨222201386, by rfl⟩ : syracuseStep 296268515 = 444402773) B444402773
theorem B4567859 : Blo 1352995 4567859 := bstep (se 1 (by rfl) ⟨3425894, by rfl⟩ : syracuseStep 4567859 = 6851789) B6851789
theorem B3044249 : Blo 1352995 3044249 := bstep (se 2 (by rfl) ⟨1141593, by rfl⟩ : syracuseStep 3044249 = 2283187) B2283187
theorem B8680409 : Blo 1352995 8680409 := bstep (se 2 (by rfl) ⟨3255153, by rfl⟩ : syracuseStep 8680409 = 6510307) B6510307
theorem B3429337 : Blo 1352995 3429337 := bstep (se 2 (by rfl) ⟨1286001, by rfl⟩ : syracuseStep 3429337 = 2572003) B2572003
theorem B3044339 : Blo 1352995 3044339 := bstep (se 1 (by rfl) ⟨2283254, by rfl⟩ : syracuseStep 3044339 = 4566509) B4566509
theorem B1446923 : Blo 1352995 1446923 := bstep (se 1 (by rfl) ⟨1085192, by rfl⟩ : syracuseStep 1446923 = 2170385) B2170385
theorem B10417169 : Blo 1352995 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B3044375 : Blo 1352995 3044375 := bstep (se 1 (by rfl) ⟨2283281, by rfl⟩ : syracuseStep 3044375 = 4566563) B4566563
theorem B2438209 : Blo 1352995 2438209 := bstep (se 2 (by rfl) ⟨914328, by rfl⟩ : syracuseStep 2438209 = 1828657) B1828657
theorem B4568129 : Blo 1352995 4568129 := bstep (se 2 (by rfl) ⟨1713048, by rfl⟩ : syracuseStep 4568129 = 3426097) B3426097
theorem B3044555 : Blo 1352995 3044555 := bstep (se 1 (by rfl) ⟨2283416, by rfl⟩ : syracuseStep 3044555 = 4566833) B4566833
theorem B6943961 : Blo 1352995 6943961 := bstep (se 2 (by rfl) ⟨2603985, by rfl⟩ : syracuseStep 6943961 = 5207971) B5207971
theorem B3044609 : Blo 1352995 3044609 := bstep (se 2 (by rfl) ⟨1141728, by rfl⟩ : syracuseStep 3044609 = 2283457) B2283457
theorem B5780909 : Blo 1352995 5780909 := bstep (se 3 (by rfl) ⟨1083920, by rfl⟩ : syracuseStep 5780909 = 2167841) B2167841
theorem B3044825 : Blo 1352995 3044825 := bstep (se 2 (by rfl) ⟨1141809, by rfl⟩ : syracuseStep 3044825 = 2283619) B2283619
theorem B13186577 : Blo 1352995 13186577 := bstep (se 2 (by rfl) ⟨4944966, by rfl⟩ : syracuseStep 13186577 = 9889933) B9889933
theorem B9754157 : Blo 1352995 9754157 := bstep (se 3 (by rfl) ⟨1828904, by rfl⟩ : syracuseStep 9754157 = 3657809) B3657809
theorem B3044915 : Blo 1352995 3044915 := bstep (se 1 (by rfl) ⟨2283686, by rfl⟩ : syracuseStep 3044915 = 4567373) B4567373
theorem B2438707 : Blo 1352995 2438707 := bstep (se 1 (by rfl) ⟨1829030, by rfl⟩ : syracuseStep 2438707 = 3658061) B3658061
theorem B6854219 : Blo 1352995 6854219 := bstep (se 1 (by rfl) ⟨5140664, by rfl⟩ : syracuseStep 6854219 = 10281329) B10281329
theorem B3044951 : Blo 1352995 3044951 := bstep (se 1 (by rfl) ⟨2283713, by rfl⟩ : syracuseStep 3044951 = 4567427) B4567427
theorem B4568669 : Blo 1352995 4568669 := bstep (se 3 (by rfl) ⟨856625, by rfl⟩ : syracuseStep 4568669 = 1713251) B1713251
theorem B9270935 : Blo 1352995 9270935 := bstep (se 1 (by rfl) ⟨6953201, by rfl⟩ : syracuseStep 9270935 = 13906403) B13906403
theorem B2569907 : Blo 1352995 2569907 := bstep (se 1 (by rfl) ⟨1927430, by rfl⟩ : syracuseStep 2569907 = 3854861) B3854861
theorem B19519157 : Blo 1352995 19519157 := bstep (se 5 (by rfl) ⟨914960, by rfl⟩ : syracuseStep 19519157 = 1829921) B1829921
theorem B5142275 : Blo 1352995 5142275 := bstep (se 1 (by rfl) ⟨3856706, by rfl⟩ : syracuseStep 5142275 = 7713413) B7713413
theorem B2283275 : Blo 1352995 2283275 := bstep (se 1 (by rfl) ⟨1712456, by rfl⟩ : syracuseStep 2283275 = 3424913) B3424913
theorem B3045131 : Blo 1352995 3045131 := bstep (se 1 (by rfl) ⟨2283848, by rfl⟩ : syracuseStep 3045131 = 4567697) B4567697
theorem B3045185 : Blo 1352995 3045185 := bstep (se 2 (by rfl) ⟨1141944, by rfl⟩ : syracuseStep 3045185 = 2283889) B2283889
theorem B11573057 : Blo 1352995 11573057 := bstep (se 2 (by rfl) ⟨4339896, by rfl⟩ : syracuseStep 11573057 = 8679793) B8679793
theorem B2570059 : Blo 1352995 2570059 := bstep (se 1 (by rfl) ⟨1927544, by rfl⟩ : syracuseStep 2570059 = 3855089) B3855089
theorem B2283403 : Blo 1352995 2283403 := bstep (se 1 (by rfl) ⟨1712552, by rfl⟩ : syracuseStep 2283403 = 3425105) B3425105
theorem B2029529 : Blo 1352995 2029529 := bstep (se 2 (by rfl) ⟨761073, by rfl⟩ : syracuseStep 2029529 = 1522147) B1522147
theorem B20846605 : Blo 1352995 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B2283545 : Blo 1352995 2283545 := bstep (se 2 (by rfl) ⟨856329, by rfl⟩ : syracuseStep 2283545 = 1712659) B1712659
theorem B3045401 : Blo 1352995 3045401 := bstep (se 2 (by rfl) ⟨1142025, by rfl⟩ : syracuseStep 3045401 = 2284051) B2284051
theorem B2029643 : Blo 1352995 2029643 := bstep (se 1 (by rfl) ⟨1522232, by rfl⟩ : syracuseStep 2029643 = 3044465) B3044465
theorem B2029655 : Blo 1352995 2029655 := bstep (se 1 (by rfl) ⟨1522241, by rfl⟩ : syracuseStep 2029655 = 3044483) B3044483
theorem B3045491 : Blo 1352995 3045491 := bstep (se 1 (by rfl) ⟨2284118, by rfl⟩ : syracuseStep 3045491 = 4568237) B4568237
theorem B3045527 : Blo 1352995 3045527 := bstep (se 1 (by rfl) ⟨2284145, by rfl⟩ : syracuseStep 3045527 = 4568291) B4568291
theorem B2029721 : Blo 1352995 2029721 := bstep (se 2 (by rfl) ⟨761145, by rfl⟩ : syracuseStep 2029721 = 1522291) B1522291
theorem B2283673 : Blo 1352995 2283673 := bstep (se 2 (by rfl) ⟨856377, by rfl⟩ : syracuseStep 2283673 = 1712755) B1712755
theorem B2570393 : Blo 1352995 2570393 := bstep (se 2 (by rfl) ⟨963897, by rfl⟩ : syracuseStep 2570393 = 1927795) B1927795
theorem B3086515 : Blo 1352995 3086515 := bstep (se 1 (by rfl) ⟨2314886, by rfl⟩ : syracuseStep 3086515 = 4629773) B4629773
theorem B1980619 : Blo 1352995 1980619 := bstep (se 1 (by rfl) ⟨1485464, by rfl⟩ : syracuseStep 1980619 = 2970929) B2970929
theorem B26016005 : Blo 1352995 26016005 := bstep (se 4 (by rfl) ⟨2439000, by rfl⟩ : syracuseStep 26016005 = 4878001) B4878001
theorem B2029835 : Blo 1352995 2029835 := bstep (se 1 (by rfl) ⟨1522376, by rfl⟩ : syracuseStep 2029835 = 3044753) B3044753
theorem B7706897 : Blo 1352995 7706897 := bstep (se 2 (by rfl) ⟨2890086, by rfl⟩ : syracuseStep 7706897 = 5780173) B5780173
theorem B2029847 : Blo 1352995 2029847 := bstep (se 1 (by rfl) ⟨1522385, by rfl⟩ : syracuseStep 2029847 = 3044771) B3044771
theorem B3045707 : Blo 1352995 3045707 := bstep (se 1 (by rfl) ⟨2284280, by rfl⟩ : syracuseStep 3045707 = 4568561) B4568561
theorem B2029913 : Blo 1352995 2029913 := bstep (se 2 (by rfl) ⟨761217, by rfl⟩ : syracuseStep 2029913 = 1522435) B1522435
theorem B3856729 : Blo 1352995 3856729 := bstep (se 2 (by rfl) ⟨1446273, by rfl⟩ : syracuseStep 3856729 = 2892547) B2892547
theorem B56342897 : Blo 1352995 56342897 := bstep (se 2 (by rfl) ⟨21128586, by rfl⟩ : syracuseStep 56342897 = 42257173) B42257173
theorem B3045761 : Blo 1352995 3045761 := bstep (se 2 (by rfl) ⟨1142160, by rfl⟩ : syracuseStep 3045761 = 2284321) B2284321
theorem B2030027 : Blo 1352995 2030027 := bstep (se 1 (by rfl) ⟨1522520, by rfl⟩ : syracuseStep 2030027 = 3045041) B3045041
theorem B2030039 : Blo 1352995 2030039 := bstep (se 1 (by rfl) ⟨1522529, by rfl⟩ : syracuseStep 2030039 = 3045059) B3045059
theorem B10279385 : Blo 1352995 10279385 := bstep (se 2 (by rfl) ⟨3854769, by rfl⟩ : syracuseStep 10279385 = 7709539) B7709539
theorem B2030105 : Blo 1352995 2030105 := bstep (se 2 (by rfl) ⟨761289, by rfl⟩ : syracuseStep 2030105 = 1522579) B1522579
theorem B1522219 : Blo 1352995 1522219 := bstep (se 1 (by rfl) ⟨1141664, by rfl⟩ : syracuseStep 1522219 = 2283329) B2283329
theorem B3045977 : Blo 1352995 3045977 := bstep (se 2 (by rfl) ⟨1142241, by rfl⟩ : syracuseStep 3045977 = 2284483) B2284483
theorem B2030219 : Blo 1352995 2030219 := bstep (se 1 (by rfl) ⟨1522664, by rfl⟩ : syracuseStep 2030219 = 3045329) B3045329
theorem B1522327 : Blo 1352995 1522327 := bstep (se 1 (by rfl) ⟨1141745, by rfl⟩ : syracuseStep 1522327 = 2283491) B2283491
theorem B2030231 : Blo 1352995 2030231 := bstep (se 1 (by rfl) ⟨1522673, by rfl⟩ : syracuseStep 2030231 = 3045347) B3045347
theorem B3046067 : Blo 1352995 3046067 := bstep (se 1 (by rfl) ⟨2284550, by rfl⟩ : syracuseStep 3046067 = 4569101) B4569101
theorem B4569803 : Blo 1352995 4569803 := bstep (se 1 (by rfl) ⟨3427352, by rfl⟩ : syracuseStep 4569803 = 6854705) B6854705
theorem B14637773 : Blo 1352995 14637773 := bstep (se 3 (by rfl) ⟨2744582, by rfl⟩ : syracuseStep 14637773 = 5489165) B5489165
theorem B2284247 : Blo 1352995 2284247 := bstep (se 1 (by rfl) ⟨1713185, by rfl⟩ : syracuseStep 2284247 = 3426371) B3426371
theorem B3046103 : Blo 1352995 3046103 := bstep (se 1 (by rfl) ⟨2284577, by rfl⟩ : syracuseStep 3046103 = 4569155) B4569155
theorem B2030297 : Blo 1352995 2030297 := bstep (se 2 (by rfl) ⟨761361, by rfl⟩ : syracuseStep 2030297 = 1522723) B1522723
theorem B2571031 : Blo 1352995 2571031 := bstep (se 1 (by rfl) ⟨1928273, by rfl⟩ : syracuseStep 2571031 = 3856547) B3856547
theorem B5864237 : Blo 1352995 5864237 := bstep (se 3 (by rfl) ⟨1099544, by rfl⟩ : syracuseStep 5864237 = 2199089) B2199089
theorem B1522507 : Blo 1352995 1522507 := bstep (se 1 (by rfl) ⟨1141880, by rfl⟩ : syracuseStep 1522507 = 2283761) B2283761
theorem B2030411 : Blo 1352995 2030411 := bstep (se 1 (by rfl) ⟨1522808, by rfl⟩ : syracuseStep 2030411 = 3045617) B3045617
theorem B2603863 : Blo 1352995 2603863 := bstep (se 1 (by rfl) ⟨1952897, by rfl⟩ : syracuseStep 2603863 = 3905795) B3905795
theorem B1760087 : Blo 1352995 1760087 := bstep (se 1 (by rfl) ⟨1320065, by rfl⟩ : syracuseStep 1760087 = 2640131) B2640131
theorem B2030423 : Blo 1352995 2030423 := bstep (se 1 (by rfl) ⟨1522817, by rfl⟩ : syracuseStep 2030423 = 3045635) B3045635
theorem B2284375 : Blo 1352995 2284375 := bstep (se 1 (by rfl) ⟨1713281, by rfl⟩ : syracuseStep 2284375 = 3426563) B3426563
theorem B6175619 : Blo 1352995 6175619 := bstep (se 1 (by rfl) ⟨4631714, by rfl⟩ : syracuseStep 6175619 = 9263429) B9263429
theorem B3046283 : Blo 1352995 3046283 := bstep (se 1 (by rfl) ⟨2284712, by rfl⟩ : syracuseStep 3046283 = 4569425) B4569425
theorem B2030489 : Blo 1352995 2030489 := bstep (se 2 (by rfl) ⟨761433, by rfl⟩ : syracuseStep 2030489 = 1522867) B1522867
theorem B1522615 : Blo 1352995 1522615 := bstep (se 1 (by rfl) ⟨1141961, by rfl⟩ : syracuseStep 1522615 = 2283923) B2283923
theorem B3046337 : Blo 1352995 3046337 := bstep (se 2 (by rfl) ⟨1142376, by rfl⟩ : syracuseStep 3046337 = 2284753) B2284753
theorem B3857345 : Blo 1352995 3857345 := bstep (se 2 (by rfl) ⟨1446504, by rfl⟩ : syracuseStep 3857345 = 2893009) B2893009
theorem B4570073 : Blo 1352995 4570073 := bstep (se 2 (by rfl) ⟨1713777, by rfl⟩ : syracuseStep 4570073 = 3427555) B3427555
theorem B10288133 : Blo 1352995 10288133 := bstep (se 4 (by rfl) ⟨964512, by rfl⟩ : syracuseStep 10288133 = 1929025) B1929025
theorem B2030603 : Blo 1352995 2030603 := bstep (se 1 (by rfl) ⟨1522952, by rfl⟩ : syracuseStep 2030603 = 3045905) B3045905
theorem B2030615 : Blo 1352995 2030615 := bstep (se 1 (by rfl) ⟨1522961, by rfl⟩ : syracuseStep 2030615 = 3045923) B3045923
theorem B2030681 : Blo 1352995 2030681 := bstep (se 2 (by rfl) ⟨761505, by rfl⟩ : syracuseStep 2030681 = 1523011) B1523011
theorem B1522795 : Blo 1352995 1522795 := bstep (se 1 (by rfl) ⟨1142096, by rfl⟩ : syracuseStep 1522795 = 2284193) B2284193
theorem B2440343 : Blo 1352995 2440343 := bstep (se 1 (by rfl) ⟨1830257, by rfl⟩ : syracuseStep 2440343 = 3660515) B3660515
theorem B3046553 : Blo 1352995 3046553 := bstep (se 2 (by rfl) ⟨1142457, by rfl⟩ : syracuseStep 3046553 = 2284915) B2284915
theorem B2030795 : Blo 1352995 2030795 := bstep (se 1 (by rfl) ⟨1523096, by rfl⟩ : syracuseStep 2030795 = 3046193) B3046193
theorem B1522903 : Blo 1352995 1522903 := bstep (se 1 (by rfl) ⟨1142177, by rfl⟩ : syracuseStep 1522903 = 2284355) B2284355
theorem B2030807 : Blo 1352995 2030807 := bstep (se 1 (by rfl) ⟨1523105, by rfl⟩ : syracuseStep 2030807 = 3046211) B3046211
theorem B3046643 : Blo 1352995 3046643 := bstep (se 1 (by rfl) ⟨2284982, by rfl⟩ : syracuseStep 3046643 = 4569965) B4569965
theorem B2891009 : Blo 1352995 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B10419461 : Blo 1352995 10419461 := bstep (se 4 (by rfl) ⟨976824, by rfl⟩ : syracuseStep 10419461 = 1953649) B1953649
theorem B3046679 : Blo 1352995 3046679 := bstep (se 1 (by rfl) ⟨2285009, by rfl⟩ : syracuseStep 3046679 = 4570019) B4570019
theorem B2030873 : Blo 1352995 2030873 := bstep (se 2 (by rfl) ⟨761577, by rfl⟩ : syracuseStep 2030873 = 1523155) B1523155
theorem B4947245 : Blo 1352995 4947245 := bstep (se 3 (by rfl) ⟨927608, by rfl⟩ : syracuseStep 4947245 = 1855217) B1855217
theorem B6856001 : Blo 1352995 6856001 := bstep (se 2 (by rfl) ⟨2571000, by rfl⟩ : syracuseStep 6856001 = 5142001) B5142001
theorem B5782873 : Blo 1352995 5782873 := bstep (se 2 (by rfl) ⟨2168577, by rfl⟩ : syracuseStep 5782873 = 4337155) B4337155
theorem B2170199 : Blo 1352995 2170199 := bstep (se 1 (by rfl) ⟨1627649, by rfl⟩ : syracuseStep 2170199 = 3255299) B3255299
theorem B6503773 : Blo 1352995 6503773 := bstep (se 3 (by rfl) ⟨1219457, by rfl⟩ : syracuseStep 6503773 = 2438915) B2438915
theorem B1523083 : Blo 1352995 1523083 := bstep (se 1 (by rfl) ⟨1142312, by rfl⟩ : syracuseStep 1523083 = 2284625) B2284625
theorem B2030987 : Blo 1352995 2030987 := bstep (se 1 (by rfl) ⟨1523240, by rfl⟩ : syracuseStep 2030987 = 3046481) B3046481
theorem B4881809 : Blo 1352995 4881809 := bstep (se 2 (by rfl) ⟨1830678, by rfl⟩ : syracuseStep 4881809 = 3661357) B3661357
theorem B2030999 : Blo 1352995 2030999 := bstep (se 1 (by rfl) ⟨1523249, by rfl⟩ : syracuseStep 2030999 = 3046499) B3046499
theorem B2285003 : Blo 1352995 2285003 := bstep (se 1 (by rfl) ⟨1713752, by rfl⟩ : syracuseStep 2285003 = 3427505) B3427505
theorem B3046859 : Blo 1352995 3046859 := bstep (se 1 (by rfl) ⟨2285144, by rfl⟩ : syracuseStep 3046859 = 4570289) B4570289
theorem B2031065 : Blo 1352995 2031065 := bstep (se 2 (by rfl) ⟨761649, by rfl⟩ : syracuseStep 2031065 = 1523299) B1523299
theorem B1523191 : Blo 1352995 1523191 := bstep (se 1 (by rfl) ⟨1142393, by rfl⟩ : syracuseStep 1523191 = 2284787) B2284787
theorem B3046913 : Blo 1352995 3046913 := bstep (se 2 (by rfl) ⟨1142592, by rfl⟩ : syracuseStep 3046913 = 2285185) B2285185
theorem B2031179 : Blo 1352995 2031179 := bstep (se 1 (by rfl) ⟨1523384, by rfl⟩ : syracuseStep 2031179 = 3046769) B3046769
theorem B2285131 : Blo 1352995 2285131 := bstep (se 1 (by rfl) ⟨1713848, by rfl⟩ : syracuseStep 2285131 = 3427697) B3427697
theorem B2571851 : Blo 1352995 2571851 := bstep (se 1 (by rfl) ⟨1928888, by rfl⟩ : syracuseStep 2571851 = 3857777) B3857777
theorem B2891351 : Blo 1352995 2891351 := bstep (se 1 (by rfl) ⟨2168513, by rfl⟩ : syracuseStep 2891351 = 4337027) B4337027
theorem B2031191 : Blo 1352995 2031191 := bstep (se 1 (by rfl) ⟨1523393, by rfl⟩ : syracuseStep 2031191 = 3046787) B3046787
theorem B31276637 : Blo 1352995 31276637 := bstep (se 3 (by rfl) ⟨5864369, by rfl⟩ : syracuseStep 31276637 = 11728739) B11728739
theorem B2571905 : Blo 1352995 2571905 := bstep (se 2 (by rfl) ⟨964464, by rfl⟩ : syracuseStep 2571905 = 1928929) B1928929
theorem B4570775 : Blo 1352995 4570775 := bstep (se 1 (by rfl) ⟨3428081, by rfl⟩ : syracuseStep 4570775 = 6856163) B6856163
theorem B2031257 : Blo 1352995 2031257 := bstep (se 2 (by rfl) ⟨761721, by rfl⟩ : syracuseStep 2031257 = 1523443) B1523443
theorem B1523371 : Blo 1352995 1523371 := bstep (se 1 (by rfl) ⟨1142528, by rfl⟩ : syracuseStep 1523371 = 2285057) B2285057
theorem B2440897 : Blo 1352995 2440897 := bstep (se 2 (by rfl) ⟨915336, by rfl⟩ : syracuseStep 2440897 = 1830673) B1830673
theorem B2285273 : Blo 1352995 2285273 := bstep (se 2 (by rfl) ⟨856977, by rfl⟩ : syracuseStep 2285273 = 1713955) B1713955
theorem B3047129 : Blo 1352995 3047129 := bstep (se 2 (by rfl) ⟨1142673, by rfl⟩ : syracuseStep 3047129 = 2285347) B2285347
theorem B2031371 : Blo 1352995 2031371 := bstep (se 1 (by rfl) ⟨1523528, by rfl⟩ : syracuseStep 2031371 = 3047057) B3047057
theorem B2744087 : Blo 1352995 2744087 := bstep (se 1 (by rfl) ⟨2058065, by rfl⟩ : syracuseStep 2744087 = 4116131) B4116131
theorem B1523479 : Blo 1352995 1523479 := bstep (se 1 (by rfl) ⟨1142609, by rfl⟩ : syracuseStep 1523479 = 2285219) B2285219
theorem B2031383 : Blo 1352995 2031383 := bstep (se 1 (by rfl) ⟨1523537, by rfl⟩ : syracuseStep 2031383 = 3047075) B3047075
theorem B3047219 : Blo 1352995 3047219 := bstep (se 1 (by rfl) ⟨2285414, by rfl⟩ : syracuseStep 3047219 = 4570829) B4570829
theorem B3047255 : Blo 1352995 3047255 := bstep (se 1 (by rfl) ⟨2285441, by rfl⟩ : syracuseStep 3047255 = 4570883) B4570883
theorem B2031449 : Blo 1352995 2031449 := bstep (se 2 (by rfl) ⟨761793, by rfl⟩ : syracuseStep 2031449 = 1523587) B1523587
theorem B2285401 : Blo 1352995 2285401 := bstep (se 2 (by rfl) ⟨857025, by rfl⟩ : syracuseStep 2285401 = 1714051) B1714051
theorem B2891659 : Blo 1352995 2891659 := bstep (se 1 (by rfl) ⟨2168744, by rfl⟩ : syracuseStep 2891659 = 4337489) B4337489
theorem B1523659 : Blo 1352995 1523659 := bstep (se 1 (by rfl) ⟨1142744, by rfl⟩ : syracuseStep 1523659 = 2285489) B2285489
theorem B2031563 : Blo 1352995 2031563 := bstep (se 1 (by rfl) ⟨1523672, by rfl⟩ : syracuseStep 2031563 = 3047345) B3047345
theorem B2031575 : Blo 1352995 2031575 := bstep (se 1 (by rfl) ⟨1523681, by rfl⟩ : syracuseStep 2031575 = 3047363) B3047363
theorem B2031623 : Blo 1352995 2031623 := bstep (se 1 (by rfl) ⟨1523717, by rfl⟩ : syracuseStep 2031623 = 3047435) B3047435
theorem B27795473 : Blo 1352995 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B3858461 : Blo 1352995 3858461 := bstep (se 3 (by rfl) ⟨723461, by rfl⟩ : syracuseStep 3858461 = 1446923) B1446923
theorem B2031659 : Blo 1352995 2031659 := bstep (se 1 (by rfl) ⟨1523744, by rfl⟩ : syracuseStep 2031659 = 3047489) B3047489
theorem B2031689 : Blo 1352995 2031689 := bstep (se 2 (by rfl) ⟨761883, by rfl⟩ : syracuseStep 2031689 = 1523767) B1523767
theorem B3047543 : Blo 1352995 3047543 := bstep (se 1 (by rfl) ⟨2285657, by rfl⟩ : syracuseStep 3047543 = 4571315) B4571315
theorem B2031803 : Blo 1352995 2031803 := bstep (se 1 (by rfl) ⟨1523852, by rfl⟩ : syracuseStep 2031803 = 3047705) B3047705
theorem B29270261 : Blo 1352995 29270261 := bstep (se 5 (by rfl) ⟨1372043, by rfl⟩ : syracuseStep 29270261 = 2744087) B2744087
theorem B2031863 : Blo 1352995 2031863 := bstep (se 1 (by rfl) ⟨1523897, by rfl⟩ : syracuseStep 2031863 = 3047795) B3047795
theorem B2031887 : Blo 1352995 2031887 := bstep (se 1 (by rfl) ⟨1523915, by rfl⟩ : syracuseStep 2031887 = 3047831) B3047831
theorem B1523983 : Blo 1352995 1523983 := bstep (se 1 (by rfl) ⟨1142987, by rfl⟩ : syracuseStep 1523983 = 2285975) B2285975
theorem B3047723 : Blo 1352995 3047723 := bstep (se 1 (by rfl) ⟨2285792, by rfl⟩ : syracuseStep 3047723 = 4571585) B4571585
theorem B2285867 : Blo 1352995 2285867 := bstep (se 1 (by rfl) ⟨1714400, by rfl⟩ : syracuseStep 2285867 = 3428801) B3428801
theorem B2031929 : Blo 1352995 2031929 := bstep (se 2 (by rfl) ⟨761973, by rfl⟩ : syracuseStep 2031929 = 1523947) B1523947
theorem B2032007 : Blo 1352995 2032007 := bstep (se 1 (by rfl) ⟨1524005, by rfl⟩ : syracuseStep 2032007 = 3048011) B3048011
theorem B2032043 : Blo 1352995 2032043 := bstep (se 1 (by rfl) ⟨1524032, by rfl⟩ : syracuseStep 2032043 = 3048065) B3048065
theorem B2032073 : Blo 1352995 2032073 := bstep (se 2 (by rfl) ⟨762027, by rfl⟩ : syracuseStep 2032073 = 1524055) B1524055
theorem B3424801 : Blo 1352995 3424801 := bstep (se 2 (by rfl) ⟨1284300, by rfl⟩ : syracuseStep 3424801 = 2568601) B2568601
theorem B2032187 : Blo 1352995 2032187 := bstep (se 1 (by rfl) ⟨1524140, by rfl⟩ : syracuseStep 2032187 = 3048281) B3048281
theorem B2032247 : Blo 1352995 2032247 := bstep (se 1 (by rfl) ⟨1524185, by rfl⟩ : syracuseStep 2032247 = 3048371) B3048371
theorem B2032271 : Blo 1352995 2032271 := bstep (se 1 (by rfl) ⟨1524203, by rfl⟩ : syracuseStep 2032271 = 3048407) B3048407
theorem B3048083 : Blo 1352995 3048083 := bstep (se 1 (by rfl) ⟨2286062, by rfl⟩ : syracuseStep 3048083 = 4572125) B4572125
theorem B7709357 : Blo 1352995 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B2286265 : Blo 1352995 2286265 := bstep (se 2 (by rfl) ⟨857349, by rfl⟩ : syracuseStep 2286265 = 1714699) B1714699
theorem B2032313 : Blo 1352995 2032313 := bstep (se 2 (by rfl) ⟨762117, by rfl⟩ : syracuseStep 2032313 = 1524235) B1524235
theorem B3048137 : Blo 1352995 3048137 := bstep (se 2 (by rfl) ⟨1143051, by rfl⟩ : syracuseStep 3048137 = 2286103) B2286103
theorem B6505217 : Blo 1352995 6505217 := bstep (se 2 (by rfl) ⟨2439456, by rfl⟩ : syracuseStep 6505217 = 4878913) B4878913
theorem B2032391 : Blo 1352995 2032391 := bstep (se 1 (by rfl) ⟨1524293, by rfl⟩ : syracuseStep 2032391 = 3048587) B3048587
theorem B2032427 : Blo 1352995 2032427 := bstep (se 1 (by rfl) ⟨1524320, by rfl⟩ : syracuseStep 2032427 = 3048641) B3048641
theorem B4629307 : Blo 1352995 4629307 := bstep (se 1 (by rfl) ⟨3471980, by rfl⟩ : syracuseStep 4629307 = 6943961) B6943961
theorem B4571963 : Blo 1352995 4571963 := bstep (se 1 (by rfl) ⟨3428972, by rfl⟩ : syracuseStep 4571963 = 6857945) B6857945
theorem B2032457 : Blo 1352995 2032457 := bstep (se 2 (by rfl) ⟨762171, by rfl⟩ : syracuseStep 2032457 = 1524343) B1524343
theorem B13018117 : Blo 1352995 13018117 := bstep (se 4 (by rfl) ⟨1220448, by rfl⟩ : syracuseStep 13018117 = 2440897) B2440897
theorem B3425399 : Blo 1352995 3425399 := bstep (se 1 (by rfl) ⟨2569049, by rfl⟩ : syracuseStep 3425399 = 5138099) B5138099
theorem B4572449 : Blo 1352995 4572449 := bstep (se 2 (by rfl) ⟨1714668, by rfl⟩ : syracuseStep 4572449 = 3429337) B3429337
theorem B1353019 : Blo 1352995 1353019 := bstep (se 1 (by rfl) ⟨1014764, by rfl⟩ : syracuseStep 1353019 = 2029529) B2029529
theorem B1353095 : Blo 1352995 1353095 := bstep (se 1 (by rfl) ⟨1014821, by rfl⟩ : syracuseStep 1353095 = 2029643) B2029643
theorem B1353103 : Blo 1352995 1353103 := bstep (se 1 (by rfl) ⟨1014827, by rfl⟩ : syracuseStep 1353103 = 2029655) B2029655
theorem B39060913 : Blo 1352995 39060913 := bstep (se 2 (by rfl) ⟨14647842, by rfl⟩ : syracuseStep 39060913 = 29295685) B29295685
theorem B1353147 : Blo 1352995 1353147 := bstep (se 1 (by rfl) ⟨1014860, by rfl⟩ : syracuseStep 1353147 = 2029721) B2029721
theorem B17344003 : Blo 1352995 17344003 := bstep (se 1 (by rfl) ⟨13008002, by rfl⟩ : syracuseStep 17344003 = 26016005) B26016005
theorem B1353223 : Blo 1352995 1353223 := bstep (se 1 (by rfl) ⟨1014917, by rfl⟩ : syracuseStep 1353223 = 2029835) B2029835
theorem B5137931 : Blo 1352995 5137931 := bstep (se 1 (by rfl) ⟨3853448, by rfl⟩ : syracuseStep 5137931 = 7706897) B7706897
theorem B1353231 : Blo 1352995 1353231 := bstep (se 1 (by rfl) ⟨1014923, by rfl⟩ : syracuseStep 1353231 = 2029847) B2029847
theorem B6858269 : Blo 1352995 6858269 := bstep (se 3 (by rfl) ⟨1285925, by rfl⟩ : syracuseStep 6858269 = 2571851) B2571851
theorem B11568683 : Blo 1352995 11568683 := bstep (se 1 (by rfl) ⟨8676512, by rfl⟩ : syracuseStep 11568683 = 17353025) B17353025
theorem B1926713 : Blo 1352995 1926713 := bstep (se 2 (by rfl) ⟨722517, by rfl⟩ : syracuseStep 1926713 = 1445035) B1445035
theorem B1353275 : Blo 1352995 1353275 := bstep (se 1 (by rfl) ⟨1014956, by rfl⟩ : syracuseStep 1353275 = 2029913) B2029913
theorem B37045835 : Blo 1352995 37045835 := bstep (se 1 (by rfl) ⟨27784376, by rfl⟩ : syracuseStep 37045835 = 55568753) B55568753
theorem B37561931 : Blo 1352995 37561931 := bstep (se 1 (by rfl) ⟨28171448, by rfl⟩ : syracuseStep 37561931 = 56342897) B56342897
theorem B1353351 : Blo 1352995 1353351 := bstep (se 1 (by rfl) ⟨1015013, by rfl⟩ : syracuseStep 1353351 = 2030027) B2030027
theorem B1353359 : Blo 1352995 1353359 := bstep (se 1 (by rfl) ⟨1015019, by rfl⟩ : syracuseStep 1353359 = 2030039) B2030039
theorem B1353403 : Blo 1352995 1353403 := bstep (se 1 (by rfl) ⟨1015052, by rfl⟩ : syracuseStep 1353403 = 2030105) B2030105
theorem B7628525 : Blo 1352995 7628525 := bstep (se 3 (by rfl) ⟨1430348, by rfl⟩ : syracuseStep 7628525 = 2860697) B2860697
theorem B1353479 : Blo 1352995 1353479 := bstep (se 1 (by rfl) ⟨1015109, by rfl⟩ : syracuseStep 1353479 = 2030219) B2030219
theorem B1353487 : Blo 1352995 1353487 := bstep (se 1 (by rfl) ⟨1015115, by rfl⟩ : syracuseStep 1353487 = 2030231) B2030231
theorem B7710497 : Blo 1352995 7710497 := bstep (se 2 (by rfl) ⟨2891436, by rfl⟩ : syracuseStep 7710497 = 5782873) B5782873
theorem B9758515 : Blo 1352995 9758515 := bstep (se 1 (by rfl) ⟨7318886, by rfl⟩ : syracuseStep 9758515 = 14637773) B14637773
theorem B1353531 : Blo 1352995 1353531 := bstep (se 1 (by rfl) ⟨1015148, by rfl⟩ : syracuseStep 1353531 = 2030297) B2030297
theorem B4949819 : Blo 1352995 4949819 := bstep (se 1 (by rfl) ⟨3712364, by rfl⟩ : syracuseStep 4949819 = 7424729) B7424729
theorem B3909491 : Blo 1352995 3909491 := bstep (se 1 (by rfl) ⟨2932118, by rfl⟩ : syracuseStep 3909491 = 5864237) B5864237
theorem B4573043 : Blo 1352995 4573043 := bstep (se 1 (by rfl) ⟨3429782, by rfl⟩ : syracuseStep 4573043 = 6859565) B6859565
theorem B1353607 : Blo 1352995 1353607 := bstep (se 1 (by rfl) ⟨1015205, by rfl⟩ : syracuseStep 1353607 = 2030411) B2030411
theorem B1353615 : Blo 1352995 1353615 := bstep (se 1 (by rfl) ⟨1015211, by rfl⟩ : syracuseStep 1353615 = 2030423) B2030423
theorem B1353659 : Blo 1352995 1353659 := bstep (se 1 (by rfl) ⟨1015244, by rfl⟩ : syracuseStep 1353659 = 2030489) B2030489
theorem B6858755 : Blo 1352995 6858755 := bstep (se 1 (by rfl) ⟨5144066, by rfl⟩ : syracuseStep 6858755 = 10288133) B10288133
theorem B1353735 : Blo 1352995 1353735 := bstep (se 1 (by rfl) ⟨1015301, by rfl⟩ : syracuseStep 1353735 = 2030603) B2030603
theorem B1353743 : Blo 1352995 1353743 := bstep (se 1 (by rfl) ⟨1015307, by rfl⟩ : syracuseStep 1353743 = 2030615) B2030615
theorem B1353787 : Blo 1352995 1353787 := bstep (se 1 (by rfl) ⟨1015340, by rfl⟩ : syracuseStep 1353787 = 2030681) B2030681
theorem B1353863 : Blo 1352995 1353863 := bstep (se 1 (by rfl) ⟨1015397, by rfl⟩ : syracuseStep 1353863 = 2030795) B2030795
theorem B1353871 : Blo 1352995 1353871 := bstep (se 1 (by rfl) ⟨1015403, by rfl⟩ : syracuseStep 1353871 = 2030807) B2030807
theorem B1353915 : Blo 1352995 1353915 := bstep (se 1 (by rfl) ⟨1015436, by rfl⟩ : syracuseStep 1353915 = 2030873) B2030873
theorem B6850817 : Blo 1352995 6850817 := bstep (se 2 (by rfl) ⟨2569056, by rfl⟩ : syracuseStep 6850817 = 5138113) B5138113
theorem B1353991 : Blo 1352995 1353991 := bstep (se 1 (by rfl) ⟨1015493, by rfl⟩ : syracuseStep 1353991 = 2030987) B2030987
theorem B3254539 : Blo 1352995 3254539 := bstep (se 1 (by rfl) ⟨2440904, by rfl⟩ : syracuseStep 3254539 = 4881809) B4881809
theorem B1353999 : Blo 1352995 1353999 := bstep (se 1 (by rfl) ⟨1015499, by rfl⟩ : syracuseStep 1353999 = 2030999) B2030999
theorem B1354043 : Blo 1352995 1354043 := bstep (se 1 (by rfl) ⟨1015532, by rfl⟩ : syracuseStep 1354043 = 2031065) B2031065
theorem B3426695 : Blo 1352995 3426695 := bstep (se 1 (by rfl) ⟨2570021, by rfl⟩ : syracuseStep 3426695 = 5140043) B5140043
theorem B1354119 : Blo 1352995 1354119 := bstep (se 1 (by rfl) ⟨1015589, by rfl⟩ : syracuseStep 1354119 = 2031179) B2031179
theorem B1927567 : Blo 1352995 1927567 := bstep (se 1 (by rfl) ⟨1445675, by rfl⟩ : syracuseStep 1927567 = 2891351) B2891351
theorem B1354127 : Blo 1352995 1354127 := bstep (se 1 (by rfl) ⟨1015595, by rfl⟩ : syracuseStep 1354127 = 2031191) B2031191
theorem B20851091 : Blo 1352995 20851091 := bstep (se 1 (by rfl) ⟨15638318, by rfl⟩ : syracuseStep 20851091 = 31276637) B31276637
theorem B1714603 : Blo 1352995 1714603 := bstep (se 1 (by rfl) ⟨1285952, by rfl⟩ : syracuseStep 1714603 = 2571905) B2571905
theorem B5138873 : Blo 1352995 5138873 := bstep (se 2 (by rfl) ⟨1927077, by rfl⟩ : syracuseStep 5138873 = 3854155) B3854155
theorem B3426745 : Blo 1352995 3426745 := bstep (se 2 (by rfl) ⟨1285029, by rfl⟩ : syracuseStep 3426745 = 2570059) B2570059
theorem B1354171 : Blo 1352995 1354171 := bstep (se 1 (by rfl) ⟨1015628, by rfl⟩ : syracuseStep 1354171 = 2031257) B2031257
theorem B1354247 : Blo 1352995 1354247 := bstep (se 1 (by rfl) ⟨1015685, by rfl⟩ : syracuseStep 1354247 = 2031371) B2031371
theorem B1354255 : Blo 1352995 1354255 := bstep (se 1 (by rfl) ⟨1015691, by rfl⟩ : syracuseStep 1354255 = 2031383) B2031383
theorem B1354299 : Blo 1352995 1354299 := bstep (se 1 (by rfl) ⟨1015724, by rfl⟩ : syracuseStep 1354299 = 2031449) B2031449
theorem B1354375 : Blo 1352995 1354375 := bstep (se 1 (by rfl) ⟨1015781, by rfl⟩ : syracuseStep 1354375 = 2031563) B2031563
theorem B1354383 : Blo 1352995 1354383 := bstep (se 1 (by rfl) ⟨1015787, by rfl⟩ : syracuseStep 1354383 = 2031575) B2031575
theorem B3852947 : Blo 1352995 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B1354427 : Blo 1352995 1354427 := bstep (se 1 (by rfl) ⟨1015820, by rfl⟩ : syracuseStep 1354427 = 2031641) B2031641
theorem B1354503 : Blo 1352995 1354503 := bstep (se 1 (by rfl) ⟨1015877, by rfl⟩ : syracuseStep 1354503 = 2031755) B2031755
theorem B1354511 : Blo 1352995 1354511 := bstep (se 1 (by rfl) ⟨1015883, by rfl⟩ : syracuseStep 1354511 = 2031767) B2031767
theorem B16476979 : Blo 1352995 16476979 := bstep (se 1 (by rfl) ⟨12357734, by rfl⟩ : syracuseStep 16476979 = 24715469) B24715469
theorem B1354555 : Blo 1352995 1354555 := bstep (se 1 (by rfl) ⟨1015916, by rfl⟩ : syracuseStep 1354555 = 2031833) B2031833
theorem B3910459 : Blo 1352995 3910459 := bstep (se 1 (by rfl) ⟨2932844, by rfl⟩ : syracuseStep 3910459 = 5865689) B5865689
theorem B1354631 : Blo 1352995 1354631 := bstep (se 1 (by rfl) ⟨1015973, by rfl⟩ : syracuseStep 1354631 = 2031947) B2031947
theorem B1354639 : Blo 1352995 1354639 := bstep (se 1 (by rfl) ⟨1015979, by rfl⟩ : syracuseStep 1354639 = 2031959) B2031959
theorem B1354683 : Blo 1352995 1354683 := bstep (se 1 (by rfl) ⟨1016012, by rfl⟩ : syracuseStep 1354683 = 2032025) B2032025
theorem B1928137 : Blo 1352995 1928137 := bstep (se 2 (by rfl) ⟨723051, by rfl⟩ : syracuseStep 1928137 = 1446103) B1446103
theorem B15428555 : Blo 1352995 15428555 := bstep (se 1 (by rfl) ⟨11571416, by rfl⟩ : syracuseStep 15428555 = 23142833) B23142833
theorem B1354759 : Blo 1352995 1354759 := bstep (se 1 (by rfl) ⟨1016069, by rfl⟩ : syracuseStep 1354759 = 2032139) B2032139
theorem B21949451 : Blo 1352995 21949451 := bstep (se 1 (by rfl) ⟨16462088, by rfl⟩ : syracuseStep 21949451 = 32924177) B32924177
theorem B8678411 : Blo 1352995 8678411 := bstep (se 1 (by rfl) ⟨6508808, by rfl⟩ : syracuseStep 8678411 = 13017617) B13017617
theorem B3427343 : Blo 1352995 3427343 := bstep (se 1 (by rfl) ⟨2570507, by rfl⟩ : syracuseStep 3427343 = 5141015) B5141015
theorem B1354767 : Blo 1352995 1354767 := bstep (se 1 (by rfl) ⟨1016075, by rfl⟩ : syracuseStep 1354767 = 2032151) B2032151
theorem B6851627 : Blo 1352995 6851627 := bstep (se 1 (by rfl) ⟨5138720, by rfl⟩ : syracuseStep 6851627 = 10277441) B10277441
theorem B1354811 : Blo 1352995 1354811 := bstep (se 1 (by rfl) ⟨1016108, by rfl⟩ : syracuseStep 1354811 = 2032217) B2032217
theorem B8678461 : Blo 1352995 8678461 := bstep (se 3 (by rfl) ⟨1627211, by rfl⟩ : syracuseStep 8678461 = 3254423) B3254423
theorem B13896791 : Blo 1352995 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B1354887 : Blo 1352995 1354887 := bstep (se 1 (by rfl) ⟨1016165, by rfl⟩ : syracuseStep 1354887 = 2032331) B2032331
theorem B1354895 : Blo 1352995 1354895 := bstep (se 1 (by rfl) ⟨1016171, by rfl⟩ : syracuseStep 1354895 = 2032343) B2032343
theorem B197512343 : Blo 1352995 197512343 := bstep (se 1 (by rfl) ⟨148134257, by rfl⟩ : syracuseStep 197512343 = 296268515) B296268515
theorem B3255481 : Blo 1352995 3255481 := bstep (se 2 (by rfl) ⟨1220805, by rfl⟩ : syracuseStep 3255481 = 2441611) B2441611
theorem B1354939 : Blo 1352995 1354939 := bstep (se 1 (by rfl) ⟨1016204, by rfl⟩ : syracuseStep 1354939 = 2032409) B2032409
theorem B5786939 : Blo 1352995 5786939 := bstep (se 1 (by rfl) ⟨4340204, by rfl⟩ : syracuseStep 5786939 = 8680409) B8680409
theorem B7318993 : Blo 1352995 7318993 := bstep (se 2 (by rfl) ⟨2744622, by rfl⟩ : syracuseStep 7318993 = 5489245) B5489245
theorem B5787197 : Blo 1352995 5787197 := bstep (se 3 (by rfl) ⟨1085099, by rfl⟩ : syracuseStep 5787197 = 2170199) B2170199
theorem B16461413 : Blo 1352995 16461413 := bstep (se 4 (by rfl) ⟨1543257, by rfl⟩ : syracuseStep 16461413 = 3086515) B3086515
theorem B3853939 : Blo 1352995 3853939 := bstep (se 1 (by rfl) ⟨2890454, by rfl⟩ : syracuseStep 3853939 = 5780909) B5780909
theorem B3428041 : Blo 1352995 3428041 := bstep (se 2 (by rfl) ⟨1285515, by rfl⟩ : syracuseStep 3428041 = 2571031) B2571031
theorem B10563301 : Blo 1352995 10563301 := bstep (se 4 (by rfl) ⟨990309, by rfl⟩ : syracuseStep 10563301 = 1980619) B1980619
theorem B7319297 : Blo 1352995 7319297 := bstep (se 2 (by rfl) ⟨2744736, by rfl⟩ : syracuseStep 7319297 = 5489473) B5489473
theorem B10424065 : Blo 1352995 10424065 := bstep (se 2 (by rfl) ⟨3909024, by rfl⟩ : syracuseStep 10424065 = 7818049) B7818049
theorem B6180623 : Blo 1352995 6180623 := bstep (se 1 (by rfl) ⟨4635467, by rfl⟩ : syracuseStep 6180623 = 9270935) B9270935
theorem B13012771 : Blo 1352995 13012771 := bstep (se 1 (by rfl) ⟨9759578, by rfl⟩ : syracuseStep 13012771 = 19519157) B19519157
theorem B3428183 : Blo 1352995 3428183 := bstep (se 1 (by rfl) ⟨2571137, by rfl⟩ : syracuseStep 3428183 = 5142275) B5142275
theorem B35164205 : Blo 1352995 35164205 := bstep (se 3 (by rfl) ⟨6593288, by rfl⟩ : syracuseStep 35164205 = 13186577) B13186577
theorem B7319753 : Blo 1352995 7319753 := bstep (se 2 (by rfl) ⟨2744907, by rfl⟩ : syracuseStep 7319753 = 5489815) B5489815
theorem B6852923 : Blo 1352995 6852923 := bstep (se 1 (by rfl) ⟨5139692, by rfl⟩ : syracuseStep 6852923 = 10279385) B10279385
theorem B4567481 : Blo 1352995 4567481 := bstep (se 2 (by rfl) ⟨1712805, by rfl⟩ : syracuseStep 4567481 = 3425611) B3425611
theorem B8671697 : Blo 1352995 8671697 := bstep (se 2 (by rfl) ⟨3251886, by rfl⟩ : syracuseStep 8671697 = 6503773) B6503773
theorem B6853085 : Blo 1352995 6853085 := bstep (se 3 (by rfl) ⟨1284953, by rfl⟩ : syracuseStep 6853085 = 2569907) B2569907
theorem B4117079 : Blo 1352995 4117079 := bstep (se 1 (by rfl) ⟨3087809, by rfl⟩ : syracuseStep 4117079 = 6175619) B6175619
theorem B2568905 : Blo 1352995 2568905 := bstep (se 2 (by rfl) ⟨963339, by rfl⟩ : syracuseStep 2568905 = 1926679) B1926679
theorem B1626895 : Blo 1352995 1626895 := bstep (se 1 (by rfl) ⟨1220171, by rfl⟩ : syracuseStep 1626895 = 2440343) B2440343
theorem B6853409 : Blo 1352995 6853409 := bstep (se 2 (by rfl) ⟨2570028, by rfl⟩ : syracuseStep 6853409 = 5140057) B5140057
theorem B9270053 : Blo 1352995 9270053 := bstep (se 4 (by rfl) ⟨869067, by rfl⟩ : syracuseStep 9270053 = 1738135) B1738135
theorem B3298163 : Blo 1352995 3298163 := bstep (se 1 (by rfl) ⟨2473622, by rfl⟩ : syracuseStep 3298163 = 4947245) B4947245
theorem B3707849 : Blo 1352995 3707849 := bstep (se 2 (by rfl) ⟨1390443, by rfl⟩ : syracuseStep 3707849 = 2780887) B2780887
theorem B4568075 : Blo 1352995 4568075 := bstep (se 1 (by rfl) ⟨3426056, by rfl⟩ : syracuseStep 4568075 = 6852113) B6852113
theorem B5141515 : Blo 1352995 5141515 := bstep (se 1 (by rfl) ⟨3856136, by rfl⟩ : syracuseStep 5141515 = 7712273) B7712273
theorem B3044411 : Blo 1352995 3044411 := bstep (se 1 (by rfl) ⟨2283308, by rfl⟩ : syracuseStep 3044411 = 4566617) B4566617
theorem B4568183 : Blo 1352995 4568183 := bstep (se 1 (by rfl) ⟨3426137, by rfl⟩ : syracuseStep 4568183 = 6852275) B6852275
theorem B3044537 : Blo 1352995 3044537 := bstep (se 2 (by rfl) ⟨1141701, by rfl⟩ : syracuseStep 3044537 = 2283403) B2283403
theorem B3855545 : Blo 1352995 3855545 := bstep (se 2 (by rfl) ⟨1445829, by rfl⟩ : syracuseStep 3855545 = 2891659) B2891659
theorem B5141819 : Blo 1352995 5141819 := bstep (se 1 (by rfl) ⟨3856364, by rfl⟩ : syracuseStep 5141819 = 7712729) B7712729
theorem B2569619 : Blo 1352995 2569619 := bstep (se 1 (by rfl) ⟨1927214, by rfl⟩ : syracuseStep 2569619 = 3854429) B3854429
theorem B4879763 : Blo 1352995 4879763 := bstep (se 1 (by rfl) ⟨3659822, by rfl⟩ : syracuseStep 4879763 = 7319645) B7319645
theorem B2569657 : Blo 1352995 2569657 := bstep (se 2 (by rfl) ⟨963621, by rfl⟩ : syracuseStep 2569657 = 1927243) B1927243
theorem B4339129 : Blo 1352995 4339129 := bstep (se 2 (by rfl) ⟨1627173, by rfl⟩ : syracuseStep 4339129 = 3254347) B3254347
theorem B7706123 : Blo 1352995 7706123 := bstep (se 1 (by rfl) ⟨5779592, by rfl⟩ : syracuseStep 7706123 = 11559185) B11559185
theorem B5568011 : Blo 1352995 5568011 := bstep (se 1 (by rfl) ⟨4176008, by rfl⟩ : syracuseStep 5568011 = 8352017) B8352017
theorem B3044879 : Blo 1352995 3044879 := bstep (se 1 (by rfl) ⟨2283659, by rfl⟩ : syracuseStep 3044879 = 4567319) B4567319
theorem B3855887 : Blo 1352995 3855887 := bstep (se 1 (by rfl) ⟨2891915, by rfl⟩ : syracuseStep 3855887 = 5783831) B5783831
theorem B3044897 : Blo 1352995 3044897 := bstep (se 2 (by rfl) ⟨1141836, by rfl⟩ : syracuseStep 3044897 = 2283673) B2283673
theorem B8238635 : Blo 1352995 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B4568777 : Blo 1352995 4568777 := bstep (se 2 (by rfl) ⟨1713291, by rfl⟩ : syracuseStep 4568777 = 3426583) B3426583
theorem B6854381 : Blo 1352995 6854381 := bstep (se 3 (by rfl) ⟨1285196, by rfl⟩ : syracuseStep 6854381 = 2570393) B2570393
theorem B5142305 : Blo 1352995 5142305 := bstep (se 2 (by rfl) ⟨1928364, by rfl⟩ : syracuseStep 5142305 = 3856729) B3856729
theorem B16701299 : Blo 1352995 16701299 := bstep (se 1 (by rfl) ⟨12525974, by rfl⟩ : syracuseStep 16701299 = 25051949) B25051949
theorem B2283383 : Blo 1352995 2283383 := bstep (se 1 (by rfl) ⟨1712537, by rfl⟩ : syracuseStep 2283383 = 3425075) B3425075
theorem B3045239 : Blo 1352995 3045239 := bstep (se 1 (by rfl) ⟨2283929, by rfl⟩ : syracuseStep 3045239 = 4567859) B4567859
theorem B2029499 : Blo 1352995 2029499 := bstep (se 1 (by rfl) ⟨1522124, by rfl⟩ : syracuseStep 2029499 = 3044249) B3044249
theorem B2029559 : Blo 1352995 2029559 := bstep (se 1 (by rfl) ⟨1522169, by rfl⟩ : syracuseStep 2029559 = 3044339) B3044339
theorem B6944779 : Blo 1352995 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B4118539 : Blo 1352995 4118539 := bstep (se 1 (by rfl) ⟨3088904, by rfl⟩ : syracuseStep 4118539 = 6177809) B6177809
theorem B211007501 : Blo 1352995 211007501 := bstep (se 3 (by rfl) ⟨39563906, by rfl⟩ : syracuseStep 211007501 = 79127813) B79127813
theorem B2029583 : Blo 1352995 2029583 := bstep (se 1 (by rfl) ⟨1522187, by rfl⟩ : syracuseStep 2029583 = 3044375) B3044375
theorem B3045419 : Blo 1352995 3045419 := bstep (se 1 (by rfl) ⟨2284064, by rfl⟩ : syracuseStep 3045419 = 4568129) B4568129
theorem B2029625 : Blo 1352995 2029625 := bstep (se 2 (by rfl) ⟨761109, by rfl⟩ : syracuseStep 2029625 = 1522219) B1522219
theorem B7526467 : Blo 1352995 7526467 := bstep (se 1 (by rfl) ⟨5644850, by rfl⟩ : syracuseStep 7526467 = 11289701) B11289701
theorem B2889847 : Blo 1352995 2889847 := bstep (se 1 (by rfl) ⟨2167385, by rfl⟩ : syracuseStep 2889847 = 4334771) B4334771
theorem B2029703 : Blo 1352995 2029703 := bstep (se 1 (by rfl) ⟨1522277, by rfl⟩ : syracuseStep 2029703 = 3044555) B3044555
theorem B4118663 : Blo 1352995 4118663 := bstep (se 1 (by rfl) ⟨3088997, by rfl⟩ : syracuseStep 4118663 = 6177995) B6177995
theorem B2029739 : Blo 1352995 2029739 := bstep (se 1 (by rfl) ⟨1522304, by rfl⟩ : syracuseStep 2029739 = 3044609) B3044609
theorem B2029769 : Blo 1352995 2029769 := bstep (se 2 (by rfl) ⟨761163, by rfl⟩ : syracuseStep 2029769 = 1522327) B1522327
theorem B3856673 : Blo 1352995 3856673 := bstep (se 2 (by rfl) ⟨1446252, by rfl⟩ : syracuseStep 3856673 = 2892505) B2892505
theorem B2029883 : Blo 1352995 2029883 := bstep (se 1 (by rfl) ⟨1522412, by rfl⟩ : syracuseStep 2029883 = 3044825) B3044825
theorem B2283835 : Blo 1352995 2283835 := bstep (se 1 (by rfl) ⟨1712876, by rfl⟩ : syracuseStep 2283835 = 3425753) B3425753
theorem B6502771 : Blo 1352995 6502771 := bstep (se 1 (by rfl) ⟨4877078, by rfl⟩ : syracuseStep 6502771 = 9754157) B9754157
theorem B2029943 : Blo 1352995 2029943 := bstep (se 1 (by rfl) ⟨1522457, by rfl⟩ : syracuseStep 2029943 = 3044915) B3044915
theorem B3709319 : Blo 1352995 3709319 := bstep (se 1 (by rfl) ⟨2781989, by rfl⟩ : syracuseStep 3709319 = 5563979) B5563979
theorem B4569479 : Blo 1352995 4569479 := bstep (se 1 (by rfl) ⟨3427109, by rfl⟩ : syracuseStep 4569479 = 6854219) B6854219
theorem B3660167 : Blo 1352995 3660167 := bstep (se 1 (by rfl) ⟨2745125, by rfl⟩ : syracuseStep 3660167 = 5490251) B5490251
theorem B2029967 : Blo 1352995 2029967 := bstep (se 1 (by rfl) ⟨1522475, by rfl⟩ : syracuseStep 2029967 = 3044951) B3044951
theorem B3045779 : Blo 1352995 3045779 := bstep (se 1 (by rfl) ⟨2284334, by rfl⟩ : syracuseStep 3045779 = 4568669) B4568669
theorem B7813529 : Blo 1352995 7813529 := bstep (se 2 (by rfl) ⟨2930073, by rfl⟩ : syracuseStep 7813529 = 5860147) B5860147
theorem B2030009 : Blo 1352995 2030009 := bstep (se 2 (by rfl) ⟨761253, by rfl⟩ : syracuseStep 2030009 = 1522507) B1522507
theorem B3471817 : Blo 1352995 3471817 := bstep (se 2 (by rfl) ⟨1301931, by rfl⟩ : syracuseStep 3471817 = 2603863) B2603863
theorem B2283977 : Blo 1352995 2283977 := bstep (se 2 (by rfl) ⟨856491, by rfl⟩ : syracuseStep 2283977 = 1712983) B1712983
theorem B3045833 : Blo 1352995 3045833 := bstep (se 2 (by rfl) ⟨1142187, by rfl⟩ : syracuseStep 3045833 = 2284375) B2284375
theorem B1522183 : Blo 1352995 1522183 := bstep (se 1 (by rfl) ⟨1141637, by rfl⟩ : syracuseStep 1522183 = 2283275) B2283275
theorem B2030087 : Blo 1352995 2030087 := bstep (se 1 (by rfl) ⟨1522565, by rfl⟩ : syracuseStep 2030087 = 3045131) B3045131
theorem B6855191 : Blo 1352995 6855191 := bstep (se 1 (by rfl) ⟨5141393, by rfl⟩ : syracuseStep 6855191 = 10282787) B10282787
theorem B2030123 : Blo 1352995 2030123 := bstep (se 1 (by rfl) ⟨1522592, by rfl⟩ : syracuseStep 2030123 = 3045185) B3045185
theorem B7715371 : Blo 1352995 7715371 := bstep (se 1 (by rfl) ⟨5786528, by rfl⟩ : syracuseStep 7715371 = 11573057) B11573057
theorem B2030153 : Blo 1352995 2030153 := bstep (se 2 (by rfl) ⟨761307, by rfl⟩ : syracuseStep 2030153 = 1522615) B1522615
theorem B1522363 : Blo 1352995 1522363 := bstep (se 1 (by rfl) ⟨1141772, by rfl⟩ : syracuseStep 1522363 = 2283545) B2283545
theorem B2030267 : Blo 1352995 2030267 := bstep (se 1 (by rfl) ⟨1522700, by rfl⟩ : syracuseStep 2030267 = 3045401) B3045401
theorem B5143277 : Blo 1352995 5143277 := bstep (se 3 (by rfl) ⟨964364, by rfl⟩ : syracuseStep 5143277 = 1928729) B1928729
theorem B2030327 : Blo 1352995 2030327 := bstep (se 1 (by rfl) ⟨1522745, by rfl⟩ : syracuseStep 2030327 = 3045491) B3045491
theorem B3250945 : Blo 1352995 3250945 := bstep (se 2 (by rfl) ⟨1219104, by rfl⟩ : syracuseStep 3250945 = 2438209) B2438209
theorem B4569857 : Blo 1352995 4569857 := bstep (se 2 (by rfl) ⟨1713696, by rfl⟩ : syracuseStep 4569857 = 3427393) B3427393
theorem B2030351 : Blo 1352995 2030351 := bstep (se 1 (by rfl) ⟨1522763, by rfl⟩ : syracuseStep 2030351 = 3045527) B3045527
theorem B2030393 : Blo 1352995 2030393 := bstep (se 2 (by rfl) ⟨761397, by rfl⟩ : syracuseStep 2030393 = 1522795) B1522795
theorem B2030471 : Blo 1352995 2030471 := bstep (se 1 (by rfl) ⟨1522853, by rfl⟩ : syracuseStep 2030471 = 3045707) B3045707
theorem B4119443 : Blo 1352995 4119443 := bstep (se 1 (by rfl) ⟨3089582, by rfl⟩ : syracuseStep 4119443 = 6179165) B6179165
theorem B7322521 : Blo 1352995 7322521 := bstep (se 2 (by rfl) ⟨2745945, by rfl⟩ : syracuseStep 7322521 = 5491891) B5491891
theorem B2030507 : Blo 1352995 2030507 := bstep (se 1 (by rfl) ⟨1522880, by rfl⟩ : syracuseStep 2030507 = 3045761) B3045761
theorem B2030537 : Blo 1352995 2030537 := bstep (se 2 (by rfl) ⟨761451, by rfl⟩ : syracuseStep 2030537 = 1522903) B1522903
theorem B2030651 : Blo 1352995 2030651 := bstep (se 1 (by rfl) ⟨1522988, by rfl⟩ : syracuseStep 2030651 = 3045977) B3045977
theorem B2030711 : Blo 1352995 2030711 := bstep (se 1 (by rfl) ⟨1523033, by rfl⟩ : syracuseStep 2030711 = 3046067) B3046067
theorem B2284679 : Blo 1352995 2284679 := bstep (se 1 (by rfl) ⟨1713509, by rfl⟩ : syracuseStep 2284679 = 3427019) B3427019
theorem B3046535 : Blo 1352995 3046535 := bstep (se 1 (by rfl) ⟨2284901, by rfl⟩ : syracuseStep 3046535 = 4569803) B4569803
theorem B1522831 : Blo 1352995 1522831 := bstep (se 1 (by rfl) ⟨1142123, by rfl⟩ : syracuseStep 1522831 = 2284247) B2284247
theorem B2030735 : Blo 1352995 2030735 := bstep (se 1 (by rfl) ⟨1523051, by rfl⟩ : syracuseStep 2030735 = 3046103) B3046103
theorem B2030777 : Blo 1352995 2030777 := bstep (se 2 (by rfl) ⟨761541, by rfl⟩ : syracuseStep 2030777 = 1523083) B1523083
theorem B3661001 : Blo 1352995 3661001 := bstep (se 2 (by rfl) ⟨1372875, by rfl⟩ : syracuseStep 3661001 = 2745751) B2745751
theorem B2030855 : Blo 1352995 2030855 := bstep (se 1 (by rfl) ⟨1523141, by rfl⟩ : syracuseStep 2030855 = 3046283) B3046283
theorem B2030891 : Blo 1352995 2030891 := bstep (se 1 (by rfl) ⟨1523168, by rfl⟩ : syracuseStep 2030891 = 3046337) B3046337
theorem B2571563 : Blo 1352995 2571563 := bstep (se 1 (by rfl) ⟨1928672, by rfl⟩ : syracuseStep 2571563 = 3857345) B3857345
theorem B3046715 : Blo 1352995 3046715 := bstep (se 1 (by rfl) ⟨2285036, by rfl⟩ : syracuseStep 3046715 = 4570073) B4570073
theorem B2030921 : Blo 1352995 2030921 := bstep (se 2 (by rfl) ⟨761595, by rfl⟩ : syracuseStep 2030921 = 1523191) B1523191
theorem B3251609 : Blo 1352995 3251609 := bstep (se 2 (by rfl) ⟨1219353, by rfl⟩ : syracuseStep 3251609 = 2438707) B2438707
theorem B3046841 : Blo 1352995 3046841 := bstep (se 2 (by rfl) ⟨1142565, by rfl⟩ : syracuseStep 3046841 = 2285131) B2285131
theorem B2031035 : Blo 1352995 2031035 := bstep (se 1 (by rfl) ⟨1523276, by rfl⟩ : syracuseStep 2031035 = 3046553) B3046553
theorem B2031095 : Blo 1352995 2031095 := bstep (se 1 (by rfl) ⟨1523321, by rfl⟩ : syracuseStep 2031095 = 3046643) B3046643
theorem B6946307 : Blo 1352995 6946307 := bstep (se 1 (by rfl) ⟨5209730, by rfl⟩ : syracuseStep 6946307 = 10419461) B10419461
theorem B2031119 : Blo 1352995 2031119 := bstep (se 1 (by rfl) ⟨1523339, by rfl⟩ : syracuseStep 2031119 = 3046679) B3046679
theorem B4570667 : Blo 1352995 4570667 := bstep (se 1 (by rfl) ⟨3428000, by rfl⟩ : syracuseStep 4570667 = 6856001) B6856001
theorem B2031161 : Blo 1352995 2031161 := bstep (se 2 (by rfl) ⟨761685, by rfl⟩ : syracuseStep 2031161 = 1523371) B1523371
theorem B4693565 : Blo 1352995 4693565 := bstep (se 3 (by rfl) ⟨880043, by rfl⟩ : syracuseStep 4693565 = 1760087) B1760087
theorem B4120183 : Blo 1352995 4120183 := bstep (se 1 (by rfl) ⟨3090137, by rfl⟩ : syracuseStep 4120183 = 6180275) B6180275
theorem B1523335 : Blo 1352995 1523335 := bstep (se 1 (by rfl) ⟨1142501, by rfl⟩ : syracuseStep 1523335 = 2285003) B2285003
theorem B2031239 : Blo 1352995 2031239 := bstep (se 1 (by rfl) ⟨1523429, by rfl⟩ : syracuseStep 2031239 = 3046859) B3046859
theorem B2031275 : Blo 1352995 2031275 := bstep (se 1 (by rfl) ⟨1523456, by rfl⟩ : syracuseStep 2031275 = 3046913) B3046913
theorem B2031305 : Blo 1352995 2031305 := bstep (se 2 (by rfl) ⟨761739, by rfl⟩ : syracuseStep 2031305 = 1523479) B1523479
theorem B3858187 : Blo 1352995 3858187 := bstep (se 1 (by rfl) ⟨2893640, by rfl⟩ : syracuseStep 3858187 = 5787281) B5787281
theorem B2285327 : Blo 1352995 2285327 := bstep (se 1 (by rfl) ⟨1713995, by rfl⟩ : syracuseStep 2285327 = 3427991) B3427991
theorem B3047183 : Blo 1352995 3047183 := bstep (se 1 (by rfl) ⟨2285387, by rfl⟩ : syracuseStep 3047183 = 4570775) B4570775
theorem B3047201 : Blo 1352995 3047201 := bstep (se 2 (by rfl) ⟨1142700, by rfl⟩ : syracuseStep 3047201 = 2285401) B2285401
theorem B1523515 : Blo 1352995 1523515 := bstep (se 1 (by rfl) ⟨1142636, by rfl⟩ : syracuseStep 1523515 = 2285273) B2285273
theorem B2031419 : Blo 1352995 2031419 := bstep (se 1 (by rfl) ⟨1523564, by rfl⟩ : syracuseStep 2031419 = 3047129) B3047129
theorem B2031479 : Blo 1352995 2031479 := bstep (se 1 (by rfl) ⟨1523609, by rfl⟩ : syracuseStep 2031479 = 3047219) B3047219
theorem B2031503 : Blo 1352995 2031503 := bstep (se 1 (by rfl) ⟨1523627, by rfl⟩ : syracuseStep 2031503 = 3047255) B3047255
theorem B2031545 : Blo 1352995 2031545 := bstep (se 2 (by rfl) ⟨761829, by rfl⟩ : syracuseStep 2031545 = 1523659) B1523659
theorem B7716829 : Blo 1352995 7716829 := bstep (se 3 (by rfl) ⟨1446905, by rfl⟩ : syracuseStep 7716829 = 2893811) B2893811
theorem B18530315 : Blo 1352995 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B2572307 : Blo 1352995 2572307 := bstep (se 1 (by rfl) ⟨1929230, by rfl⟩ : syracuseStep 2572307 = 3858461) B3858461
theorem B2031695 : Blo 1352995 2031695 := bstep (se 1 (by rfl) ⟨1523771, by rfl⟩ : syracuseStep 2031695 = 3047543) B3047543
theorem B10035289 : Blo 1352995 10035289 := bstep (se 2 (by rfl) ⟨3763233, by rfl⟩ : syracuseStep 10035289 = 7526467) B7526467
theorem B19513507 : Blo 1352995 19513507 := bstep (se 1 (by rfl) ⟨14635130, by rfl⟩ : syracuseStep 19513507 = 29270261) B29270261
theorem B2031815 : Blo 1352995 2031815 := bstep (se 1 (by rfl) ⟨1523861, by rfl⟩ : syracuseStep 2031815 = 3047723) B3047723
theorem B1523911 : Blo 1352995 1523911 := bstep (se 1 (by rfl) ⟨1142933, by rfl⟩ : syracuseStep 1523911 = 2285867) B2285867
theorem B2031977 : Blo 1352995 2031977 := bstep (se 2 (by rfl) ⟨761991, by rfl⟩ : syracuseStep 2031977 = 1523983) B1523983
theorem B2032055 : Blo 1352995 2032055 := bstep (se 1 (by rfl) ⟨1524041, by rfl⟩ : syracuseStep 2032055 = 3048083) B3048083
theorem B1712603 : Blo 1352995 1712603 := bstep (se 1 (by rfl) ⟨1284452, by rfl⟩ : syracuseStep 1712603 = 2568905) B2568905
theorem B2032091 : Blo 1352995 2032091 := bstep (se 1 (by rfl) ⟨1524068, by rfl⟩ : syracuseStep 2032091 = 3048137) B3048137
theorem B3047975 : Blo 1352995 3047975 := bstep (se 1 (by rfl) ⟨2285981, by rfl⟩ : syracuseStep 3047975 = 4571963) B4571963
theorem B2286137 : Blo 1352995 2286137 := bstep (se 2 (by rfl) ⟨857301, by rfl⟩ : syracuseStep 2286137 = 1714603) B1714603
theorem B4629089 : Blo 1352995 4629089 := bstep (se 2 (by rfl) ⟨1735908, by rfl⟩ : syracuseStep 4629089 = 3471817) B3471817
theorem B3048299 : Blo 1352995 3048299 := bstep (se 1 (by rfl) ⟨2286224, by rfl⟩ : syracuseStep 3048299 = 4572449) B4572449
theorem B3048353 : Blo 1352995 3048353 := bstep (se 2 (by rfl) ⟨1143132, by rfl⟩ : syracuseStep 3048353 = 2286265) B2286265
theorem B1713079 : Blo 1352995 1713079 := bstep (se 1 (by rfl) ⟨1284809, by rfl⟩ : syracuseStep 1713079 = 2569619) B2569619
theorem B3253175 : Blo 1352995 3253175 := bstep (se 1 (by rfl) ⟨2439881, by rfl⟩ : syracuseStep 3253175 = 4879763) B4879763
theorem B4334593 : Blo 1352995 4334593 := bstep (se 2 (by rfl) ⟨1625472, by rfl⟩ : syracuseStep 4334593 = 3250945) B3250945
theorem B5137415 : Blo 1352995 5137415 := bstep (se 1 (by rfl) ⟨3853061, by rfl⟩ : syracuseStep 5137415 = 7706123) B7706123
theorem B3425287 : Blo 1352995 3425287 := bstep (se 1 (by rfl) ⟨2568965, by rfl⟩ : syracuseStep 3425287 = 5137931) B5137931
theorem B3712007 : Blo 1352995 3712007 := bstep (se 1 (by rfl) ⟨2784005, by rfl⟩ : syracuseStep 3712007 = 5568011) B5568011
theorem B4572179 : Blo 1352995 4572179 := bstep (se 1 (by rfl) ⟨3429134, by rfl⟩ : syracuseStep 4572179 = 6858269) B6858269
theorem B2606327 : Blo 1352995 2606327 := bstep (se 1 (by rfl) ⟨1954745, by rfl⟩ : syracuseStep 2606327 = 3909491) B3909491
theorem B11134199 : Blo 1352995 11134199 := bstep (se 1 (by rfl) ⟨8350649, by rfl⟩ : syracuseStep 11134199 = 16701299) B16701299
theorem B3048695 : Blo 1352995 3048695 := bstep (se 1 (by rfl) ⟨2286521, by rfl⟩ : syracuseStep 3048695 = 4573043) B4573043
theorem B1352999 : Blo 1352995 1352999 := bstep (se 1 (by rfl) ⟨1014749, by rfl⟩ : syracuseStep 1352999 = 2029499) B2029499
theorem B1353039 : Blo 1352995 1353039 := bstep (se 1 (by rfl) ⟨1014779, by rfl⟩ : syracuseStep 1353039 = 2029559) B2029559
theorem B4572503 : Blo 1352995 4572503 := bstep (se 1 (by rfl) ⟨3429377, by rfl⟩ : syracuseStep 4572503 = 6858755) B6858755
theorem B1353055 : Blo 1352995 1353055 := bstep (se 1 (by rfl) ⟨1014791, by rfl⟩ : syracuseStep 1353055 = 2029583) B2029583
theorem B1353083 : Blo 1352995 1353083 := bstep (se 1 (by rfl) ⟨1014812, by rfl⟩ : syracuseStep 1353083 = 2029625) B2029625
theorem B1353135 : Blo 1352995 1353135 := bstep (se 1 (by rfl) ⟨1014851, by rfl⟩ : syracuseStep 1353135 = 2029703) B2029703
theorem B2745775 : Blo 1352995 2745775 := bstep (se 1 (by rfl) ⟨2059331, by rfl⟩ : syracuseStep 2745775 = 4118663) B4118663
theorem B1353159 : Blo 1352995 1353159 := bstep (se 1 (by rfl) ⟨1014869, by rfl⟩ : syracuseStep 1353159 = 2029739) B2029739
theorem B1353179 : Blo 1352995 1353179 := bstep (se 1 (by rfl) ⟨1014884, by rfl⟩ : syracuseStep 1353179 = 2029769) B2029769
theorem B5137901 : Blo 1352995 5137901 := bstep (se 3 (by rfl) ⟨963356, by rfl⟩ : syracuseStep 5137901 = 1926713) B1926713
theorem B1353255 : Blo 1352995 1353255 := bstep (se 1 (by rfl) ⟨1014941, by rfl⟩ : syracuseStep 1353255 = 2029883) B2029883
theorem B10978877 : Blo 1352995 10978877 := bstep (se 3 (by rfl) ⟨2058539, by rfl⟩ : syracuseStep 10978877 = 4117079) B4117079
theorem B1353295 : Blo 1352995 1353295 := bstep (se 1 (by rfl) ⟨1014971, by rfl⟩ : syracuseStep 1353295 = 2029943) B2029943
theorem B1353311 : Blo 1352995 1353311 := bstep (se 1 (by rfl) ⟨1014983, by rfl⟩ : syracuseStep 1353311 = 2029967) B2029967
theorem B1353339 : Blo 1352995 1353339 := bstep (se 1 (by rfl) ⟨1015004, by rfl⟩ : syracuseStep 1353339 = 2030009) B2030009
theorem B3425915 : Blo 1352995 3425915 := bstep (se 1 (by rfl) ⟨2569436, by rfl⟩ : syracuseStep 3425915 = 5138873) B5138873
theorem B1353391 : Blo 1352995 1353391 := bstep (se 1 (by rfl) ⟨1015043, by rfl⟩ : syracuseStep 1353391 = 2030087) B2030087
theorem B1353415 : Blo 1352995 1353415 := bstep (se 1 (by rfl) ⟨1015061, by rfl⟩ : syracuseStep 1353415 = 2030123) B2030123
theorem B1353435 : Blo 1352995 1353435 := bstep (se 1 (by rfl) ⟨1015076, by rfl⟩ : syracuseStep 1353435 = 2030153) B2030153
theorem B10274525 : Blo 1352995 10274525 := bstep (se 3 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 10274525 = 3852947) B3852947
theorem B1353511 : Blo 1352995 1353511 := bstep (se 1 (by rfl) ⟨1015133, by rfl⟩ : syracuseStep 1353511 = 2030267) B2030267
theorem B1353551 : Blo 1352995 1353551 := bstep (se 1 (by rfl) ⟨1015163, by rfl⟩ : syracuseStep 1353551 = 2030327) B2030327
theorem B1353567 : Blo 1352995 1353567 := bstep (se 1 (by rfl) ⟨1015175, by rfl⟩ : syracuseStep 1353567 = 2030351) B2030351
theorem B1353595 : Blo 1352995 1353595 := bstep (se 1 (by rfl) ⟨1015196, by rfl⟩ : syracuseStep 1353595 = 2030393) B2030393
theorem B3426209 : Blo 1352995 3426209 := bstep (se 2 (by rfl) ⟨1284828, by rfl⟩ : syracuseStep 3426209 = 2569657) B2569657
theorem B5785505 : Blo 1352995 5785505 := bstep (se 2 (by rfl) ⟨2169564, by rfl⟩ : syracuseStep 5785505 = 4339129) B4339129
theorem B1353647 : Blo 1352995 1353647 := bstep (se 1 (by rfl) ⟨1015235, by rfl⟩ : syracuseStep 1353647 = 2030471) B2030471
theorem B2746295 : Blo 1352995 2746295 := bstep (se 1 (by rfl) ⟨2059721, by rfl⟩ : syracuseStep 2746295 = 4119443) B4119443
theorem B9758657 : Blo 1352995 9758657 := bstep (se 2 (by rfl) ⟨3659496, by rfl⟩ : syracuseStep 9758657 = 7318993) B7318993
theorem B1353671 : Blo 1352995 1353671 := bstep (se 1 (by rfl) ⟨1015253, by rfl⟩ : syracuseStep 1353671 = 2030507) B2030507
theorem B1353691 : Blo 1352995 1353691 := bstep (se 1 (by rfl) ⟨1015268, by rfl⟩ : syracuseStep 1353691 = 2030537) B2030537
theorem B14632967 : Blo 1352995 14632967 := bstep (se 1 (by rfl) ⟨10974725, by rfl⟩ : syracuseStep 14632967 = 21949451) B21949451
theorem B5785607 : Blo 1352995 5785607 := bstep (se 1 (by rfl) ⟨4339205, by rfl⟩ : syracuseStep 5785607 = 8678411) B8678411
theorem B1353767 : Blo 1352995 1353767 := bstep (se 1 (by rfl) ⟨1015325, by rfl⟩ : syracuseStep 1353767 = 2030651) B2030651
theorem B1353807 : Blo 1352995 1353807 := bstep (se 1 (by rfl) ⟨1015355, by rfl⟩ : syracuseStep 1353807 = 2030711) B2030711
theorem B1353823 : Blo 1352995 1353823 := bstep (se 1 (by rfl) ⟨1015367, by rfl⟩ : syracuseStep 1353823 = 2030735) B2030735
theorem B1353851 : Blo 1352995 1353851 := bstep (se 1 (by rfl) ⟨1015388, by rfl⟩ : syracuseStep 1353851 = 2030777) B2030777
theorem B5138585 : Blo 1352995 5138585 := bstep (se 2 (by rfl) ⟨1926969, by rfl⟩ : syracuseStep 5138585 = 3853939) B3853939
theorem B1353903 : Blo 1352995 1353903 := bstep (se 1 (by rfl) ⟨1015427, by rfl⟩ : syracuseStep 1353903 = 2030855) B2030855
theorem B1353927 : Blo 1352995 1353927 := bstep (se 1 (by rfl) ⟨1015445, by rfl⟩ : syracuseStep 1353927 = 2030891) B2030891
theorem B1714375 : Blo 1352995 1714375 := bstep (se 1 (by rfl) ⟨1285781, by rfl⟩ : syracuseStep 1714375 = 2571563) B2571563
theorem B1353947 : Blo 1352995 1353947 := bstep (se 1 (by rfl) ⟨1015460, by rfl⟩ : syracuseStep 1353947 = 2030921) B2030921
theorem B1354023 : Blo 1352995 1354023 := bstep (se 1 (by rfl) ⟨1015517, by rfl⟩ : syracuseStep 1354023 = 2031035) B2031035
theorem B14084401 : Blo 1352995 14084401 := bstep (se 2 (by rfl) ⟨5281650, by rfl⟩ : syracuseStep 14084401 = 10563301) B10563301
theorem B1354063 : Blo 1352995 1354063 := bstep (se 1 (by rfl) ⟨1015547, by rfl⟩ : syracuseStep 1354063 = 2031095) B2031095
theorem B4630871 : Blo 1352995 4630871 := bstep (se 1 (by rfl) ⟨3473153, by rfl⟩ : syracuseStep 4630871 = 6946307) B6946307
theorem B1354079 : Blo 1352995 1354079 := bstep (se 1 (by rfl) ⟨1015559, by rfl⟩ : syracuseStep 1354079 = 2031119) B2031119
theorem B1354107 : Blo 1352995 1354107 := bstep (se 1 (by rfl) ⟨1015580, by rfl⟩ : syracuseStep 1354107 = 2031161) B2031161
theorem B13011353 : Blo 1352995 13011353 := bstep (se 2 (by rfl) ⟨4879257, by rfl⟩ : syracuseStep 13011353 = 9758515) B9758515
theorem B1354159 : Blo 1352995 1354159 := bstep (se 1 (by rfl) ⟨1015619, by rfl⟩ : syracuseStep 1354159 = 2031239) B2031239
theorem B1354183 : Blo 1352995 1354183 := bstep (se 1 (by rfl) ⟨1015637, by rfl⟩ : syracuseStep 1354183 = 2031275) B2031275
theorem B1354203 : Blo 1352995 1354203 := bstep (se 1 (by rfl) ⟨1015652, by rfl⟩ : syracuseStep 1354203 = 2031305) B2031305
theorem B1354279 : Blo 1352995 1354279 := bstep (se 1 (by rfl) ⟨1015709, by rfl⟩ : syracuseStep 1354279 = 2031419) B2031419
theorem B1354319 : Blo 1352995 1354319 := bstep (se 1 (by rfl) ⟨1015739, by rfl⟩ : syracuseStep 1354319 = 2031479) B2031479
theorem B1354335 : Blo 1352995 1354335 := bstep (se 1 (by rfl) ⟨1015751, by rfl⟩ : syracuseStep 1354335 = 2031503) B2031503
theorem B1354363 : Blo 1352995 1354363 := bstep (se 1 (by rfl) ⟨1015772, by rfl⟩ : syracuseStep 1354363 = 2031545) B2031545
theorem B1354415 : Blo 1352995 1354415 := bstep (se 1 (by rfl) ⟨1015811, by rfl⟩ : syracuseStep 1354415 = 2031623) B2031623
theorem B9259705 : Blo 1352995 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B5491385 : Blo 1352995 5491385 := bstep (se 2 (by rfl) ⟨2059269, by rfl⟩ : syracuseStep 5491385 = 4118539) B4118539
theorem B1354439 : Blo 1352995 1354439 := bstep (se 1 (by rfl) ⟨1015829, by rfl⟩ : syracuseStep 1354439 = 2031659) B2031659
theorem B1354459 : Blo 1352995 1354459 := bstep (se 1 (by rfl) ⟨1015844, by rfl⟩ : syracuseStep 1354459 = 2031689) B2031689
theorem B1354535 : Blo 1352995 1354535 := bstep (se 1 (by rfl) ⟨1015901, by rfl⟩ : syracuseStep 1354535 = 2031803) B2031803
theorem B1354575 : Blo 1352995 1354575 := bstep (se 1 (by rfl) ⟨1015931, by rfl⟩ : syracuseStep 1354575 = 2031863) B2031863
theorem B1354591 : Blo 1352995 1354591 := bstep (se 1 (by rfl) ⟨1015943, by rfl⟩ : syracuseStep 1354591 = 2031887) B2031887
theorem B1354619 : Blo 1352995 1354619 := bstep (se 1 (by rfl) ⟨1015964, by rfl⟩ : syracuseStep 1354619 = 2031929) B2031929
theorem B1354671 : Blo 1352995 1354671 := bstep (se 1 (by rfl) ⟨1016003, by rfl⟩ : syracuseStep 1354671 = 2032007) B2032007
theorem B1354695 : Blo 1352995 1354695 := bstep (se 1 (by rfl) ⟨1016021, by rfl⟩ : syracuseStep 1354695 = 2032043) B2032043
theorem B1354715 : Blo 1352995 1354715 := bstep (se 1 (by rfl) ⟨1016036, by rfl⟩ : syracuseStep 1354715 = 2032073) B2032073
theorem B1354791 : Blo 1352995 1354791 := bstep (se 1 (by rfl) ⟨1016093, by rfl⟩ : syracuseStep 1354791 = 2032187) B2032187
theorem B1354831 : Blo 1352995 1354831 := bstep (se 1 (by rfl) ⟨1016123, by rfl⟩ : syracuseStep 1354831 = 2032247) B2032247
theorem B1354847 : Blo 1352995 1354847 := bstep (se 1 (by rfl) ⟨1016135, by rfl⟩ : syracuseStep 1354847 = 2032271) B2032271
theorem B5139571 : Blo 1352995 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B1354875 : Blo 1352995 1354875 := bstep (se 1 (by rfl) ⟨1016156, by rfl⟩ : syracuseStep 1354875 = 2032313) B2032313
theorem B4336811 : Blo 1352995 4336811 := bstep (se 1 (by rfl) ⟨3252608, by rfl⟩ : syracuseStep 4336811 = 6505217) B6505217
theorem B1354927 : Blo 1352995 1354927 := bstep (se 1 (by rfl) ⟨1016195, by rfl⟩ : syracuseStep 1354927 = 2032391) B2032391
theorem B6180035 : Blo 1352995 6180035 := bstep (se 1 (by rfl) ⟨4635026, by rfl⟩ : syracuseStep 6180035 = 9270053) B9270053
theorem B1354951 : Blo 1352995 1354951 := bstep (se 1 (by rfl) ⟨1016213, by rfl⟩ : syracuseStep 1354951 = 2032427) B2032427
theorem B1354971 : Blo 1352995 1354971 := bstep (se 1 (by rfl) ⟨1016228, by rfl⟩ : syracuseStep 1354971 = 2032457) B2032457
theorem B15412517 : Blo 1352995 15412517 := bstep (se 4 (by rfl) ⟨1444923, by rfl⟩ : syracuseStep 15412517 = 2889847) B2889847
theorem B4566401 : Blo 1352995 4566401 := bstep (se 2 (by rfl) ⟨1712400, by rfl⟩ : syracuseStep 4566401 = 3424801) B3424801
theorem B3427879 : Blo 1352995 3427879 := bstep (se 1 (by rfl) ⟨2570909, by rfl⟩ : syracuseStep 3427879 = 5141819) B5141819
theorem B9891517 : Blo 1352995 9891517 := bstep (se 3 (by rfl) ⟨1854659, by rfl⟩ : syracuseStep 9891517 = 3709319) B3709319
theorem B9760445 : Blo 1352995 9760445 := bstep (se 3 (by rfl) ⟨1830083, by rfl⟩ : syracuseStep 9760445 = 3660167) B3660167
theorem B7712455 : Blo 1352995 7712455 := bstep (se 1 (by rfl) ⟨5784341, by rfl⟩ : syracuseStep 7712455 = 11568683) B11568683
theorem B5492423 : Blo 1352995 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B6172409 : Blo 1352995 6172409 := bstep (se 2 (by rfl) ⟨2314653, by rfl⟩ : syracuseStep 6172409 = 4629307) B4629307
theorem B5213945 : Blo 1352995 5213945 := bstep (se 2 (by rfl) ⟨1955229, by rfl⟩ : syracuseStep 5213945 = 3910459) B3910459
theorem B5140331 : Blo 1352995 5140331 := bstep (se 1 (by rfl) ⟨3855248, by rfl⟩ : syracuseStep 5140331 = 7710497) B7710497
theorem B3428203 : Blo 1352995 3428203 := bstep (se 1 (by rfl) ⟨2571152, by rfl⟩ : syracuseStep 3428203 = 5142305) B5142305
theorem B11571281 : Blo 1352995 11571281 := bstep (se 2 (by rfl) ⟨4339230, by rfl⟩ : syracuseStep 11571281 = 8678461) B8678461
theorem B4567211 : Blo 1352995 4567211 := bstep (se 1 (by rfl) ⟨3425408, by rfl⟩ : syracuseStep 4567211 = 6850817) B6850817
theorem B3428851 : Blo 1352995 3428851 := bstep (se 1 (by rfl) ⟨2571638, by rfl⟩ : syracuseStep 3428851 = 5143277) B5143277
theorem B52081217 : Blo 1352995 52081217 := bstep (se 2 (by rfl) ⟨19530456, by rfl⟩ : syracuseStep 52081217 = 39060913) B39060913
theorem B34681445 : Blo 1352995 34681445 := bstep (se 4 (by rfl) ⟨3251385, by rfl⟩ : syracuseStep 34681445 = 6502771) B6502771
theorem B10285703 : Blo 1352995 10285703 := bstep (se 1 (by rfl) ⟨7714277, by rfl⟩ : syracuseStep 10285703 = 15428555) B15428555
theorem B4567751 : Blo 1352995 4567751 := bstep (se 1 (by rfl) ⟨3425813, by rfl⟩ : syracuseStep 4567751 = 6851627) B6851627
theorem B131674895 : Blo 1352995 131674895 := bstep (se 1 (by rfl) ⟨98756171, by rfl⟩ : syracuseStep 131674895 = 197512343) B197512343
theorem B5493577 : Blo 1352995 5493577 := bstep (se 2 (by rfl) ⟨2060091, by rfl⟩ : syracuseStep 5493577 = 4120183) B4120183
theorem B2167739 : Blo 1352995 2167739 := bstep (se 1 (by rfl) ⟨1625804, by rfl⟩ : syracuseStep 2167739 = 3251609) B3251609
theorem B8795101 : Blo 1352995 8795101 := bstep (se 3 (by rfl) ⟨1649081, by rfl⟩ : syracuseStep 8795101 = 3298163) B3298163
theorem B13898753 : Blo 1352995 13898753 := bstep (se 2 (by rfl) ⟨5212032, by rfl⟩ : syracuseStep 13898753 = 10424065) B10424065
theorem B10974275 : Blo 1352995 10974275 := bstep (se 1 (by rfl) ⟨8230706, by rfl⟩ : syracuseStep 10974275 = 16461413) B16461413
theorem B4879531 : Blo 1352995 4879531 := bstep (se 1 (by rfl) ⟨3659648, by rfl⟩ : syracuseStep 4879531 = 7319297) B7319297
theorem B23442803 : Blo 1352995 23442803 := bstep (se 1 (by rfl) ⟨17582102, by rfl⟩ : syracuseStep 23442803 = 35164205) B35164205
theorem B4879835 : Blo 1352995 4879835 := bstep (se 1 (by rfl) ⟨3659876, by rfl⟩ : syracuseStep 4879835 = 7319753) B7319753
theorem B4568615 : Blo 1352995 4568615 := bstep (se 1 (by rfl) ⟨3426461, by rfl⟩ : syracuseStep 4568615 = 6852923) B6852923
theorem B3044987 : Blo 1352995 3044987 := bstep (se 1 (by rfl) ⟨2283740, by rfl⟩ : syracuseStep 3044987 = 4567481) B4567481
theorem B5781131 : Blo 1352995 5781131 := bstep (se 1 (by rfl) ⟨4335848, by rfl⟩ : syracuseStep 5781131 = 8671697) B8671697
theorem B4568723 : Blo 1352995 4568723 := bstep (se 1 (by rfl) ⟨3426542, by rfl⟩ : syracuseStep 4568723 = 6853085) B6853085
theorem B4339385 : Blo 1352995 4339385 := bstep (se 2 (by rfl) ⟨1627269, by rfl⟩ : syracuseStep 4339385 = 3254539) B3254539
theorem B3045113 : Blo 1352995 3045113 := bstep (se 2 (by rfl) ⟨1141917, by rfl⟩ : syracuseStep 3045113 = 2283835) B2283835
theorem B4568939 : Blo 1352995 4568939 := bstep (se 1 (by rfl) ⟨3426704, by rfl⟩ : syracuseStep 4568939 = 6853409) B6853409
theorem B4568993 : Blo 1352995 4568993 := bstep (se 2 (by rfl) ⟨1713372, by rfl⟩ : syracuseStep 4568993 = 3426745) B3426745
theorem B2471899 : Blo 1352995 2471899 := bstep (se 1 (by rfl) ⟨1853924, by rfl⟩ : syracuseStep 2471899 = 3707849) B3707849
theorem B3045383 : Blo 1352995 3045383 := bstep (se 1 (by rfl) ⟨2284037, by rfl⟩ : syracuseStep 3045383 = 4568075) B4568075
theorem B2029577 : Blo 1352995 2029577 := bstep (se 2 (by rfl) ⟨761091, by rfl⟩ : syracuseStep 2029577 = 1522183) B1522183
theorem B2029607 : Blo 1352995 2029607 := bstep (se 1 (by rfl) ⟨1522205, by rfl⟩ : syracuseStep 2029607 = 3044411) B3044411
theorem B10287161 : Blo 1352995 10287161 := bstep (se 2 (by rfl) ⟨3857685, by rfl⟩ : syracuseStep 10287161 = 7715371) B7715371
theorem B2283599 : Blo 1352995 2283599 := bstep (se 1 (by rfl) ⟨1712699, by rfl⟩ : syracuseStep 2283599 = 3425399) B3425399
theorem B3045455 : Blo 1352995 3045455 := bstep (se 1 (by rfl) ⟨2284091, by rfl⟩ : syracuseStep 3045455 = 4568183) B4568183
theorem B2029691 : Blo 1352995 2029691 := bstep (se 1 (by rfl) ⟨1522268, by rfl⟩ : syracuseStep 2029691 = 3044537) B3044537
theorem B2570363 : Blo 1352995 2570363 := bstep (se 1 (by rfl) ⟨1927772, by rfl⟩ : syracuseStep 2570363 = 3855545) B3855545
theorem B2029817 : Blo 1352995 2029817 := bstep (se 2 (by rfl) ⟨761181, by rfl⟩ : syracuseStep 2029817 = 1522363) B1522363
theorem B2029919 : Blo 1352995 2029919 := bstep (se 1 (by rfl) ⟨1522439, by rfl⟩ : syracuseStep 2029919 = 3044879) B3044879
theorem B2570591 : Blo 1352995 2570591 := bstep (se 1 (by rfl) ⟨1927943, by rfl⟩ : syracuseStep 2570591 = 3855887) B3855887
theorem B2169193 : Blo 1352995 2169193 := bstep (se 2 (by rfl) ⟨813447, by rfl⟩ : syracuseStep 2169193 = 1626895) B1626895
theorem B2029931 : Blo 1352995 2029931 := bstep (se 1 (by rfl) ⟨1522448, by rfl⟩ : syracuseStep 2029931 = 3044897) B3044897
theorem B24697223 : Blo 1352995 24697223 := bstep (se 1 (by rfl) ⟨18522917, by rfl⟩ : syracuseStep 24697223 = 37045835) B37045835
theorem B25041287 : Blo 1352995 25041287 := bstep (se 1 (by rfl) ⟨18780965, by rfl⟩ : syracuseStep 25041287 = 37561931) B37561931
theorem B21969305 : Blo 1352995 21969305 := bstep (se 2 (by rfl) ⟨8238489, by rfl⟩ : syracuseStep 21969305 = 16476979) B16476979
theorem B3045851 : Blo 1352995 3045851 := bstep (se 1 (by rfl) ⟨2284388, by rfl⟩ : syracuseStep 3045851 = 4568777) B4568777
theorem B4569587 : Blo 1352995 4569587 := bstep (se 1 (by rfl) ⟨3427190, by rfl⟩ : syracuseStep 4569587 = 6854381) B6854381
theorem B5085683 : Blo 1352995 5085683 := bstep (se 1 (by rfl) ⟨3814262, by rfl⟩ : syracuseStep 5085683 = 7628525) B7628525
theorem B9763361 : Blo 1352995 9763361 := bstep (se 2 (by rfl) ⟨3661260, by rfl⟩ : syracuseStep 9763361 = 7322521) B7322521
theorem B3299879 : Blo 1352995 3299879 := bstep (se 1 (by rfl) ⟨2474909, by rfl⟩ : syracuseStep 3299879 = 4949819) B4949819
theorem B1522255 : Blo 1352995 1522255 := bstep (se 1 (by rfl) ⟨1141691, by rfl⟩ : syracuseStep 1522255 = 2283383) B2283383
theorem B2030159 : Blo 1352995 2030159 := bstep (se 1 (by rfl) ⟨1522619, by rfl⟩ : syracuseStep 2030159 = 3045239) B3045239
theorem B2570849 : Blo 1352995 2570849 := bstep (se 2 (by rfl) ⟨964068, by rfl⟩ : syracuseStep 2570849 = 1928137) B1928137
theorem B17357489 : Blo 1352995 17357489 := bstep (se 2 (by rfl) ⟨6509058, by rfl⟩ : syracuseStep 17357489 = 13018117) B13018117
theorem B140671667 : Blo 1352995 140671667 := bstep (se 1 (by rfl) ⟨105503750, by rfl⟩ : syracuseStep 140671667 = 211007501) B211007501
theorem B6855353 : Blo 1352995 6855353 := bstep (se 2 (by rfl) ⟨2570757, by rfl⟩ : syracuseStep 6855353 = 5141515) B5141515
theorem B2030279 : Blo 1352995 2030279 := bstep (se 1 (by rfl) ⟨1522709, by rfl⟩ : syracuseStep 2030279 = 3045419) B3045419
theorem B2030441 : Blo 1352995 2030441 := bstep (se 2 (by rfl) ⟨761415, by rfl⟩ : syracuseStep 2030441 = 1522831) B1522831
theorem B2571115 : Blo 1352995 2571115 := bstep (se 1 (by rfl) ⟨1928336, by rfl⟩ : syracuseStep 2571115 = 3856673) B3856673
theorem B4340641 : Blo 1352995 4340641 := bstep (se 2 (by rfl) ⟨1627740, by rfl⟩ : syracuseStep 4340641 = 3255481) B3255481
theorem B2284463 : Blo 1352995 2284463 := bstep (se 1 (by rfl) ⟨1713347, by rfl⟩ : syracuseStep 2284463 = 3426695) B3426695
theorem B3046319 : Blo 1352995 3046319 := bstep (se 1 (by rfl) ⟨2284739, by rfl⟩ : syracuseStep 3046319 = 4569479) B4569479
theorem B2030519 : Blo 1352995 2030519 := bstep (se 1 (by rfl) ⟨1522889, by rfl⟩ : syracuseStep 2030519 = 3045779) B3045779
theorem B13900727 : Blo 1352995 13900727 := bstep (se 1 (by rfl) ⟨10425545, by rfl⟩ : syracuseStep 13900727 = 20851091) B20851091
theorem B5209019 : Blo 1352995 5209019 := bstep (se 1 (by rfl) ⟨3906764, by rfl⟩ : syracuseStep 5209019 = 7813529) B7813529
theorem B1522651 : Blo 1352995 1522651 := bstep (se 1 (by rfl) ⟨1141988, by rfl⟩ : syracuseStep 1522651 = 2283977) B2283977
theorem B2030555 : Blo 1352995 2030555 := bstep (se 1 (by rfl) ⟨1522916, by rfl⟩ : syracuseStep 2030555 = 3045833) B3045833
theorem B4570127 : Blo 1352995 4570127 := bstep (se 1 (by rfl) ⟨3427595, by rfl⟩ : syracuseStep 4570127 = 6855191) B6855191
theorem B3046571 : Blo 1352995 3046571 := bstep (se 1 (by rfl) ⟨2284928, by rfl⟩ : syracuseStep 3046571 = 4569857) B4569857
theorem B23125337 : Blo 1352995 23125337 := bstep (se 2 (by rfl) ⟨8672001, by rfl⟩ : syracuseStep 23125337 = 17344003) B17344003
theorem B2284895 : Blo 1352995 2284895 := bstep (se 1 (by rfl) ⟨1713671, by rfl⟩ : syracuseStep 2284895 = 3427343) B3427343
theorem B9264527 : Blo 1352995 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B10280357 : Blo 1352995 10280357 := bstep (se 4 (by rfl) ⟨963783, by rfl⟩ : syracuseStep 10280357 = 1927567) B1927567
theorem B1523119 : Blo 1352995 1523119 := bstep (se 1 (by rfl) ⟨1142339, by rfl⟩ : syracuseStep 1523119 = 2284679) B2284679
theorem B2031023 : Blo 1352995 2031023 := bstep (se 1 (by rfl) ⟨1523267, by rfl⟩ : syracuseStep 2031023 = 3046535) B3046535
theorem B2440667 : Blo 1352995 2440667 := bstep (se 1 (by rfl) ⟨1830500, by rfl⟩ : syracuseStep 2440667 = 3661001) B3661001
theorem B2031113 : Blo 1352995 2031113 := bstep (se 2 (by rfl) ⟨761667, by rfl⟩ : syracuseStep 2031113 = 1523335) B1523335
theorem B2031143 : Blo 1352995 2031143 := bstep (se 1 (by rfl) ⟨1523357, by rfl⟩ : syracuseStep 2031143 = 3046715) B3046715
theorem B3857959 : Blo 1352995 3857959 := bstep (se 1 (by rfl) ⟨2893469, by rfl⟩ : syracuseStep 3857959 = 5786939) B5786939
theorem B4570721 : Blo 1352995 4570721 := bstep (se 2 (by rfl) ⟨1714020, by rfl⟩ : syracuseStep 4570721 = 3428041) B3428041
theorem B2031227 : Blo 1352995 2031227 := bstep (se 1 (by rfl) ⟨1523420, by rfl⟩ : syracuseStep 2031227 = 3046841) B3046841
theorem B5144249 : Blo 1352995 5144249 := bstep (se 2 (by rfl) ⟨1929093, by rfl⟩ : syracuseStep 5144249 = 3858187) B3858187
theorem B3047111 : Blo 1352995 3047111 := bstep (se 1 (by rfl) ⟨2285333, by rfl⟩ : syracuseStep 3047111 = 4570667) B4570667
theorem B3129043 : Blo 1352995 3129043 := bstep (se 1 (by rfl) ⟨2346782, by rfl⟩ : syracuseStep 3129043 = 4693565) B4693565
theorem B3858131 : Blo 1352995 3858131 := bstep (se 1 (by rfl) ⟨2893598, by rfl⟩ : syracuseStep 3858131 = 5787197) B5787197
theorem B17350361 : Blo 1352995 17350361 := bstep (se 2 (by rfl) ⟨6506385, by rfl⟩ : syracuseStep 17350361 = 13012771) B13012771
theorem B2031353 : Blo 1352995 2031353 := bstep (se 2 (by rfl) ⟨761757, by rfl⟩ : syracuseStep 2031353 = 1523515) B1523515
theorem B1523551 : Blo 1352995 1523551 := bstep (se 1 (by rfl) ⟨1142663, by rfl⟩ : syracuseStep 1523551 = 2285327) B2285327
theorem B2031455 : Blo 1352995 2031455 := bstep (se 1 (by rfl) ⟨1523591, by rfl⟩ : syracuseStep 2031455 = 3047183) B3047183
theorem B4120415 : Blo 1352995 4120415 := bstep (se 1 (by rfl) ⟨3090311, by rfl⟩ : syracuseStep 4120415 = 6180623) B6180623
theorem B2031467 : Blo 1352995 2031467 := bstep (se 1 (by rfl) ⟨1523600, by rfl⟩ : syracuseStep 2031467 = 3047201) B3047201
theorem B2285455 : Blo 1352995 2285455 := bstep (se 1 (by rfl) ⟨1714091, by rfl⟩ : syracuseStep 2285455 = 3428183) B3428183
theorem B10289105 : Blo 1352995 10289105 := bstep (se 2 (by rfl) ⟨3858414, by rfl⟩ : syracuseStep 10289105 = 7716829) B7716829
theorem B12353543 : Blo 1352995 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B26018009 : Blo 1352995 26018009 := bstep (se 2 (by rfl) ⟨9756753, by rfl⟩ : syracuseStep 26018009 = 19513507) B19513507
theorem B2285833 : Blo 1352995 2285833 := bstep (se 2 (by rfl) ⟨857187, by rfl⟩ : syracuseStep 2285833 = 1714375) B1714375
theorem B2031881 : Blo 1352995 2031881 := bstep (se 2 (by rfl) ⟨761955, by rfl⟩ : syracuseStep 2031881 = 1523911) B1523911
theorem B2031983 : Blo 1352995 2031983 := bstep (se 1 (by rfl) ⟨1523987, by rfl⟩ : syracuseStep 2031983 = 3047975) B3047975
theorem B1524091 : Blo 1352995 1524091 := bstep (se 1 (by rfl) ⟨1143068, by rfl⟩ : syracuseStep 1524091 = 2286137) B2286137
theorem B6857135 : Blo 1352995 6857135 := bstep (se 1 (by rfl) ⟨5142851, by rfl⟩ : syracuseStep 6857135 = 10285703) B10285703
theorem B2892257 : Blo 1352995 2892257 := bstep (se 2 (by rfl) ⟨1084596, by rfl⟩ : syracuseStep 2892257 = 2169193) B2169193
theorem B2032199 : Blo 1352995 2032199 := bstep (se 1 (by rfl) ⟨1524149, by rfl⟩ : syracuseStep 2032199 = 3048299) B3048299
theorem B2032235 : Blo 1352995 2032235 := bstep (se 1 (by rfl) ⟨1524176, by rfl⟩ : syracuseStep 2032235 = 3048353) B3048353
theorem B4571801 : Blo 1352995 4571801 := bstep (se 2 (by rfl) ⟨1714425, by rfl⟩ : syracuseStep 4571801 = 3428851) B3428851
theorem B9265835 : Blo 1352995 9265835 := bstep (se 1 (by rfl) ⟨6949376, by rfl⟩ : syracuseStep 9265835 = 13898753) B13898753
theorem B3424943 : Blo 1352995 3424943 := bstep (se 1 (by rfl) ⟨2568707, by rfl⟩ : syracuseStep 3424943 = 5137415) B5137415
theorem B2474671 : Blo 1352995 2474671 := bstep (se 1 (by rfl) ⟨1856003, by rfl⟩ : syracuseStep 2474671 = 3712007) B3712007
theorem B3048119 : Blo 1352995 3048119 := bstep (se 1 (by rfl) ⟨2286089, by rfl⟩ : syracuseStep 3048119 = 4572179) B4572179
theorem B7316183 : Blo 1352995 7316183 := bstep (se 1 (by rfl) ⟨5487137, by rfl⟩ : syracuseStep 7316183 = 10974275) B10974275
theorem B1737551 : Blo 1352995 1737551 := bstep (se 1 (by rfl) ⟨1303163, by rfl⟩ : syracuseStep 1737551 = 2606327) B2606327
theorem B7422799 : Blo 1352995 7422799 := bstep (se 1 (by rfl) ⟨5567099, by rfl⟩ : syracuseStep 7422799 = 11134199) B11134199
theorem B2032463 : Blo 1352995 2032463 := bstep (se 1 (by rfl) ⟨1524347, by rfl⟩ : syracuseStep 2032463 = 3048695) B3048695
theorem B3048335 : Blo 1352995 3048335 := bstep (se 1 (by rfl) ⟨2286251, by rfl⟩ : syracuseStep 3048335 = 4572503) B4572503
theorem B12346273 : Blo 1352995 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B3253223 : Blo 1352995 3253223 := bstep (se 1 (by rfl) ⟨2439917, by rfl⟩ : syracuseStep 3253223 = 4879835) B4879835
theorem B3425267 : Blo 1352995 3425267 := bstep (se 1 (by rfl) ⟨2568950, by rfl⟩ : syracuseStep 3425267 = 5137901) B5137901
theorem B7324769 : Blo 1352995 7324769 := bstep (se 2 (by rfl) ⟨2746788, by rfl⟩ : syracuseStep 7324769 = 5493577) B5493577
theorem B2892923 : Blo 1352995 2892923 := bstep (se 1 (by rfl) ⟨2169692, by rfl⟩ : syracuseStep 2892923 = 4339385) B4339385
theorem B6849683 : Blo 1352995 6849683 := bstep (se 1 (by rfl) ⟨5137262, by rfl⟩ : syracuseStep 6849683 = 10274525) B10274525
theorem B6505771 : Blo 1352995 6505771 := bstep (se 1 (by rfl) ⟨4879328, by rfl⟩ : syracuseStep 6505771 = 9758657) B9758657
theorem B1353051 : Blo 1352995 1353051 := bstep (se 1 (by rfl) ⟨1014788, by rfl⟩ : syracuseStep 1353051 = 2029577) B2029577
theorem B1353071 : Blo 1352995 1353071 := bstep (se 1 (by rfl) ⟨1014803, by rfl⟩ : syracuseStep 1353071 = 2029607) B2029607
theorem B6858107 : Blo 1352995 6858107 := bstep (se 1 (by rfl) ⟨5143580, by rfl⟩ : syracuseStep 6858107 = 10287161) B10287161
theorem B1353127 : Blo 1352995 1353127 := bstep (se 1 (by rfl) ⟨1014845, by rfl⟩ : syracuseStep 1353127 = 2029691) B2029691
theorem B1713575 : Blo 1352995 1713575 := bstep (se 1 (by rfl) ⟨1285181, by rfl⟩ : syracuseStep 1713575 = 2570363) B2570363
theorem B3425723 : Blo 1352995 3425723 := bstep (se 1 (by rfl) ⟨2569292, by rfl⟩ : syracuseStep 3425723 = 5138585) B5138585
theorem B8799677 : Blo 1352995 8799677 := bstep (se 3 (by rfl) ⟨1649939, by rfl⟩ : syracuseStep 8799677 = 3299879) B3299879
theorem B1353211 : Blo 1352995 1353211 := bstep (se 1 (by rfl) ⟨1014908, by rfl⟩ : syracuseStep 1353211 = 2029817) B2029817
theorem B6506041 : Blo 1352995 6506041 := bstep (se 2 (by rfl) ⟨2439765, by rfl⟩ : syracuseStep 6506041 = 4879531) B4879531
theorem B1353279 : Blo 1352995 1353279 := bstep (se 1 (by rfl) ⟨1014959, by rfl⟩ : syracuseStep 1353279 = 2029919) B2029919
theorem B1713727 : Blo 1352995 1713727 := bstep (se 1 (by rfl) ⟨1285295, by rfl⟩ : syracuseStep 1713727 = 2570591) B2570591
theorem B1353287 : Blo 1352995 1353287 := bstep (se 1 (by rfl) ⟨1014965, by rfl⟩ : syracuseStep 1353287 = 2029931) B2029931
theorem B14646203 : Blo 1352995 14646203 := bstep (se 1 (by rfl) ⟨10984652, by rfl⟩ : syracuseStep 14646203 = 21969305) B21969305
theorem B1353439 : Blo 1352995 1353439 := bstep (se 1 (by rfl) ⟨1015079, by rfl⟩ : syracuseStep 1353439 = 2030159) B2030159
theorem B1713899 : Blo 1352995 1713899 := bstep (se 1 (by rfl) ⟨1285424, by rfl⟩ : syracuseStep 1713899 = 2570849) B2570849
theorem B1353519 : Blo 1352995 1353519 := bstep (se 1 (by rfl) ⟨1015139, by rfl⟩ : syracuseStep 1353519 = 2030279) B2030279
theorem B1353627 : Blo 1352995 1353627 := bstep (se 1 (by rfl) ⟨1015220, by rfl⟩ : syracuseStep 1353627 = 2030441) B2030441
theorem B1353679 : Blo 1352995 1353679 := bstep (se 1 (by rfl) ⟨1015259, by rfl⟩ : syracuseStep 1353679 = 2030519) B2030519
theorem B9267151 : Blo 1352995 9267151 := bstep (se 1 (by rfl) ⟨6950363, by rfl⟩ : syracuseStep 9267151 = 13900727) B13900727
theorem B1353703 : Blo 1352995 1353703 := bstep (se 1 (by rfl) ⟨1015277, by rfl⟩ : syracuseStep 1353703 = 2030555) B2030555
theorem B16459757 : Blo 1352995 16459757 := bstep (se 3 (by rfl) ⟨3086204, by rfl⟩ : syracuseStep 16459757 = 6172409) B6172409
theorem B10275011 : Blo 1352995 10275011 := bstep (se 1 (by rfl) ⟨7706258, by rfl⟩ : syracuseStep 10275011 = 15412517) B15412517
theorem B10283273 : Blo 1352995 10283273 := bstep (se 2 (by rfl) ⟨3856227, by rfl⟩ : syracuseStep 10283273 = 7712455) B7712455
theorem B4172057 : Blo 1352995 4172057 := bstep (se 2 (by rfl) ⟨1564521, by rfl⟩ : syracuseStep 4172057 = 3129043) B3129043
theorem B1354015 : Blo 1352995 1354015 := bstep (se 1 (by rfl) ⟨1015511, by rfl⟩ : syracuseStep 1354015 = 2031023) B2031023
theorem B1354075 : Blo 1352995 1354075 := bstep (se 1 (by rfl) ⟨1015556, by rfl⟩ : syracuseStep 1354075 = 2031113) B2031113
theorem B1354095 : Blo 1352995 1354095 := bstep (se 1 (by rfl) ⟨1015571, by rfl⟩ : syracuseStep 1354095 = 2031143) B2031143
theorem B1354151 : Blo 1352995 1354151 := bstep (se 1 (by rfl) ⟨1015613, by rfl⟩ : syracuseStep 1354151 = 2031227) B2031227
theorem B6506963 : Blo 1352995 6506963 := bstep (se 1 (by rfl) ⟨4880222, by rfl⟩ : syracuseStep 6506963 = 9760445) B9760445
theorem B1354235 : Blo 1352995 1354235 := bstep (se 1 (by rfl) ⟨1015676, by rfl⟩ : syracuseStep 1354235 = 2031353) B2031353
theorem B3475963 : Blo 1352995 3475963 := bstep (se 1 (by rfl) ⟨2606972, by rfl⟩ : syracuseStep 3475963 = 5213945) B5213945
theorem B1354303 : Blo 1352995 1354303 := bstep (se 1 (by rfl) ⟨1015727, by rfl⟩ : syracuseStep 1354303 = 2031455) B2031455
theorem B2746943 : Blo 1352995 2746943 := bstep (se 1 (by rfl) ⟨2060207, by rfl⟩ : syracuseStep 2746943 = 4120415) B4120415
theorem B3426887 : Blo 1352995 3426887 := bstep (se 1 (by rfl) ⟨2570165, by rfl⟩ : syracuseStep 3426887 = 5140331) B5140331
theorem B1354311 : Blo 1352995 1354311 := bstep (se 1 (by rfl) ⟨1015733, by rfl⟩ : syracuseStep 1354311 = 2031467) B2031467
theorem B3295865 : Blo 1352995 3295865 := bstep (se 2 (by rfl) ⟨1235949, by rfl⟩ : syracuseStep 3295865 = 2471899) B2471899
theorem B6859403 : Blo 1352995 6859403 := bstep (se 1 (by rfl) ⟨5144552, by rfl⟩ : syracuseStep 6859403 = 10289105) B10289105
theorem B1714871 : Blo 1352995 1714871 := bstep (se 1 (by rfl) ⟨1286153, by rfl⟩ : syracuseStep 1714871 = 2572307) B2572307
theorem B1354463 : Blo 1352995 1354463 := bstep (se 1 (by rfl) ⟨1015847, by rfl⟩ : syracuseStep 1354463 = 2031695) B2031695
theorem B13380385 : Blo 1352995 13380385 := bstep (se 2 (by rfl) ⟨5017644, by rfl⟩ : syracuseStep 13380385 = 10035289) B10035289
theorem B1354543 : Blo 1352995 1354543 := bstep (se 1 (by rfl) ⟨1015907, by rfl⟩ : syracuseStep 1354543 = 2031815) B2031815
theorem B1354651 : Blo 1352995 1354651 := bstep (se 1 (by rfl) ⟨1015988, by rfl⟩ : syracuseStep 1354651 = 2031977) B2031977
theorem B1354703 : Blo 1352995 1354703 := bstep (se 1 (by rfl) ⟨1016027, by rfl⟩ : syracuseStep 1354703 = 2032055) B2032055
theorem B1354727 : Blo 1352995 1354727 := bstep (se 1 (by rfl) ⟨1016045, by rfl⟩ : syracuseStep 1354727 = 2032091) B2032091
theorem B34720811 : Blo 1352995 34720811 := bstep (se 1 (by rfl) ⟨26040608, by rfl⟩ : syracuseStep 34720811 = 52081217) B52081217
theorem B18779201 : Blo 1352995 18779201 := bstep (se 2 (by rfl) ⟨7042200, by rfl⟩ : syracuseStep 18779201 = 14084401) B14084401
theorem B23120963 : Blo 1352995 23120963 := bstep (se 1 (by rfl) ⟨17340722, by rfl⟩ : syracuseStep 23120963 = 34681445) B34681445
theorem B1445159 : Blo 1352995 1445159 := bstep (se 1 (by rfl) ⟨1083869, by rfl⟩ : syracuseStep 1445159 = 2167739) B2167739
theorem B7319251 : Blo 1352995 7319251 := bstep (se 1 (by rfl) ⟨5489438, by rfl⟩ : syracuseStep 7319251 = 10978877) B10978877
theorem B3854087 : Blo 1352995 3854087 := bstep (se 1 (by rfl) ⟨2890565, by rfl⟩ : syracuseStep 3854087 = 5781131) B5781131
theorem B3428153 : Blo 1352995 3428153 := bstep (se 2 (by rfl) ⟨1285557, by rfl⟩ : syracuseStep 3428153 = 2571115) B2571115
theorem B5787521 : Blo 1352995 5787521 := bstep (se 2 (by rfl) ⟨2170320, by rfl⟩ : syracuseStep 5787521 = 4340641) B4340641
theorem B4566941 : Blo 1352995 4566941 := bstep (se 3 (by rfl) ⟨856301, by rfl⟩ : syracuseStep 4566941 = 1712603) B1712603
theorem B1830863 : Blo 1352995 1830863 := bstep (se 1 (by rfl) ⟨1373147, by rfl⟩ : syracuseStep 1830863 = 2746295) B2746295
theorem B11726801 : Blo 1352995 11726801 := bstep (se 2 (by rfl) ⟨4397550, by rfl⟩ : syracuseStep 11726801 = 8795101) B8795101
theorem B5779457 : Blo 1352995 5779457 := bstep (se 2 (by rfl) ⟨2167296, by rfl⟩ : syracuseStep 5779457 = 4334593) B4334593
theorem B4567049 : Blo 1352995 4567049 := bstep (se 2 (by rfl) ⟨1712643, by rfl⟩ : syracuseStep 4567049 = 3425287) B3425287
theorem B6852761 : Blo 1352995 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B6508907 : Blo 1352995 6508907 := bstep (se 1 (by rfl) ⟨4881680, by rfl⟩ : syracuseStep 6508907 = 9763361) B9763361
theorem B11571659 : Blo 1352995 11571659 := bstep (se 1 (by rfl) ⟨8678744, by rfl⟩ : syracuseStep 11571659 = 17357489) B17357489
theorem B3044267 : Blo 1352995 3044267 := bstep (se 1 (by rfl) ⟨2283200, by rfl⟩ : syracuseStep 3044267 = 4566401) B4566401
theorem B6853571 : Blo 1352995 6853571 := bstep (se 1 (by rfl) ⟨5140178, by rfl⟩ : syracuseStep 6853571 = 10280357) B10280357
theorem B1627111 : Blo 1352995 1627111 := bstep (se 1 (by rfl) ⟨1220333, by rfl⟩ : syracuseStep 1627111 = 2440667) B2440667
theorem B3429499 : Blo 1352995 3429499 := bstep (se 1 (by rfl) ⟨2572124, by rfl⟩ : syracuseStep 3429499 = 5144249) B5144249
theorem B7714187 : Blo 1352995 7714187 := bstep (se 1 (by rfl) ⟨5785640, by rfl⟩ : syracuseStep 7714187 = 11571281) B11571281
theorem B3044807 : Blo 1352995 3044807 := bstep (se 1 (by rfl) ⟨2283605, by rfl⟩ : syracuseStep 3044807 = 4567211) B4567211
theorem B3086059 : Blo 1352995 3086059 := bstep (se 1 (by rfl) ⟨2314544, by rfl⟩ : syracuseStep 3086059 = 4629089) B4629089
theorem B3045167 : Blo 1352995 3045167 := bstep (se 1 (by rfl) ⟨2283875, by rfl⟩ : syracuseStep 3045167 = 4567751) B4567751
theorem B16480093 : Blo 1352995 16480093 := bstep (se 3 (by rfl) ⟨3090017, by rfl⟩ : syracuseStep 16480093 = 6180035) B6180035
theorem B87783263 : Blo 1352995 87783263 := bstep (se 1 (by rfl) ⟨65837447, by rfl⟩ : syracuseStep 87783263 = 131674895) B131674895
theorem B2168783 : Blo 1352995 2168783 := bstep (se 1 (by rfl) ⟨1626587, by rfl⟩ : syracuseStep 2168783 = 3253175) B3253175
theorem B2029673 : Blo 1352995 2029673 := bstep (se 2 (by rfl) ⟨761127, by rfl⟩ : syracuseStep 2029673 = 1522255) B1522255
theorem B15628535 : Blo 1352995 15628535 := bstep (se 1 (by rfl) ⟨11721401, by rfl⟩ : syracuseStep 15628535 = 23442803) B23442803
theorem B3045743 : Blo 1352995 3045743 := bstep (se 1 (by rfl) ⟨2284307, by rfl⟩ : syracuseStep 3045743 = 4568615) B4568615
theorem B2029991 : Blo 1352995 2029991 := bstep (se 1 (by rfl) ⟨1522493, by rfl⟩ : syracuseStep 2029991 = 3044987) B3044987
theorem B2283943 : Blo 1352995 2283943 := bstep (se 1 (by rfl) ⟨1712957, by rfl⟩ : syracuseStep 2283943 = 3425915) B3425915
theorem B3045815 : Blo 1352995 3045815 := bstep (se 1 (by rfl) ⟨2284361, by rfl⟩ : syracuseStep 3045815 = 4568723) B4568723
theorem B2030075 : Blo 1352995 2030075 := bstep (se 1 (by rfl) ⟨1522556, by rfl⟩ : syracuseStep 2030075 = 3045113) B3045113
theorem B3045959 : Blo 1352995 3045959 := bstep (se 1 (by rfl) ⟨2284469, by rfl⟩ : syracuseStep 3045959 = 4568939) B4568939
theorem B2284105 : Blo 1352995 2284105 := bstep (se 2 (by rfl) ⟨856539, by rfl⟩ : syracuseStep 2284105 = 1713079) B1713079
theorem B2284139 : Blo 1352995 2284139 := bstep (se 1 (by rfl) ⟨1713104, by rfl⟩ : syracuseStep 2284139 = 3426209) B3426209
theorem B3045995 : Blo 1352995 3045995 := bstep (se 1 (by rfl) ⟨2284496, by rfl⟩ : syracuseStep 3045995 = 4568993) B4568993
theorem B3857003 : Blo 1352995 3857003 := bstep (se 1 (by rfl) ⟨2892752, by rfl⟩ : syracuseStep 3857003 = 5785505) B5785505
theorem B2030201 : Blo 1352995 2030201 := bstep (se 2 (by rfl) ⟨761325, by rfl⟩ : syracuseStep 2030201 = 1522651) B1522651
theorem B9755311 : Blo 1352995 9755311 := bstep (se 1 (by rfl) ⟨7316483, by rfl⟩ : syracuseStep 9755311 = 14632967) B14632967
theorem B2030255 : Blo 1352995 2030255 := bstep (se 1 (by rfl) ⟨1522691, by rfl⟩ : syracuseStep 2030255 = 3045383) B3045383
theorem B3857071 : Blo 1352995 3857071 := bstep (se 1 (by rfl) ⟨2892803, by rfl⟩ : syracuseStep 3857071 = 5785607) B5785607
theorem B1522399 : Blo 1352995 1522399 := bstep (se 1 (by rfl) ⟨1141799, by rfl⟩ : syracuseStep 1522399 = 2283599) B2283599
theorem B2030303 : Blo 1352995 2030303 := bstep (se 1 (by rfl) ⟨1522727, by rfl⟩ : syracuseStep 2030303 = 3045455) B3045455
theorem B3087247 : Blo 1352995 3087247 := bstep (se 1 (by rfl) ⟨2315435, by rfl⟩ : syracuseStep 3087247 = 4630871) B4630871
theorem B16464815 : Blo 1352995 16464815 := bstep (se 1 (by rfl) ⟨12348611, by rfl⟩ : syracuseStep 16464815 = 24697223) B24697223
theorem B16694191 : Blo 1352995 16694191 := bstep (se 1 (by rfl) ⟨12520643, by rfl⟩ : syracuseStep 16694191 = 25041287) B25041287
theorem B8674235 : Blo 1352995 8674235 := bstep (se 1 (by rfl) ⟨6505676, by rfl⟩ : syracuseStep 8674235 = 13011353) B13011353
theorem B2030567 : Blo 1352995 2030567 := bstep (se 1 (by rfl) ⟨1522925, by rfl⟩ : syracuseStep 2030567 = 3045851) B3045851
theorem B3046391 : Blo 1352995 3046391 := bstep (se 1 (by rfl) ⟨2284793, by rfl⟩ : syracuseStep 3046391 = 4569587) B4569587
theorem B3390455 : Blo 1352995 3390455 := bstep (se 1 (by rfl) ⟨2542841, by rfl⟩ : syracuseStep 3390455 = 5085683) B5085683
theorem B93781111 : Blo 1352995 93781111 := bstep (se 1 (by rfl) ⟨70335833, by rfl⟩ : syracuseStep 93781111 = 140671667) B140671667
theorem B4570235 : Blo 1352995 4570235 := bstep (se 1 (by rfl) ⟨3427676, by rfl⟩ : syracuseStep 4570235 = 6855353) B6855353
theorem B3660923 : Blo 1352995 3660923 := bstep (se 1 (by rfl) ⟨2745692, by rfl⟩ : syracuseStep 3660923 = 5491385) B5491385
theorem B2030825 : Blo 1352995 2030825 := bstep (se 2 (by rfl) ⟨761559, by rfl⟩ : syracuseStep 2030825 = 1523119) B1523119
theorem B3661033 : Blo 1352995 3661033 := bstep (se 2 (by rfl) ⟨1372887, by rfl⟩ : syracuseStep 3661033 = 2745775) B2745775
theorem B1522975 : Blo 1352995 1522975 := bstep (se 1 (by rfl) ⟨1142231, by rfl⟩ : syracuseStep 1522975 = 2284463) B2284463
theorem B2030879 : Blo 1352995 2030879 := bstep (se 1 (by rfl) ⟨1523159, by rfl⟩ : syracuseStep 2030879 = 3046319) B3046319
theorem B3472679 : Blo 1352995 3472679 := bstep (se 1 (by rfl) ⟨2604509, by rfl⟩ : syracuseStep 3472679 = 5209019) B5209019
theorem B3046751 : Blo 1352995 3046751 := bstep (se 1 (by rfl) ⟨2285063, by rfl⟩ : syracuseStep 3046751 = 4570127) B4570127
theorem B4570505 : Blo 1352995 4570505 := bstep (se 2 (by rfl) ⟨1713939, by rfl⟩ : syracuseStep 4570505 = 3427879) B3427879
theorem B5143945 : Blo 1352995 5143945 := bstep (se 2 (by rfl) ⟨1928979, by rfl⟩ : syracuseStep 5143945 = 3857959) B3857959
theorem B2891207 : Blo 1352995 2891207 := bstep (se 1 (by rfl) ⟨2168405, by rfl⟩ : syracuseStep 2891207 = 4336811) B4336811
theorem B2031047 : Blo 1352995 2031047 := bstep (se 1 (by rfl) ⟨1523285, by rfl⟩ : syracuseStep 2031047 = 3046571) B3046571
theorem B15416891 : Blo 1352995 15416891 := bstep (se 1 (by rfl) ⟨11562668, by rfl⟩ : syracuseStep 15416891 = 23125337) B23125337
theorem B1523263 : Blo 1352995 1523263 := bstep (se 1 (by rfl) ⟨1142447, by rfl⟩ : syracuseStep 1523263 = 2284895) B2284895
theorem B13188689 : Blo 1352995 13188689 := bstep (se 2 (by rfl) ⟨4945758, by rfl⟩ : syracuseStep 13188689 = 9891517) B9891517
theorem B6176351 : Blo 1352995 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B3047147 : Blo 1352995 3047147 := bstep (se 1 (by rfl) ⟨2285360, by rfl⟩ : syracuseStep 3047147 = 4570721) B4570721
theorem B2031401 : Blo 1352995 2031401 := bstep (se 2 (by rfl) ⟨761775, by rfl⟩ : syracuseStep 2031401 = 1523551) B1523551
theorem B2031407 : Blo 1352995 2031407 := bstep (se 1 (by rfl) ⟨1523555, by rfl⟩ : syracuseStep 2031407 = 3047111) B3047111
theorem B3661615 : Blo 1352995 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B2572087 : Blo 1352995 2572087 := bstep (se 1 (by rfl) ⟨1929065, by rfl⟩ : syracuseStep 2572087 = 3858131) B3858131
theorem B4570937 : Blo 1352995 4570937 := bstep (se 2 (by rfl) ⟨1714101, by rfl⟩ : syracuseStep 4570937 = 3428203) B3428203
theorem B11566907 : Blo 1352995 11566907 := bstep (se 1 (by rfl) ⟨8675180, by rfl⟩ : syracuseStep 11566907 = 17350361) B17350361
theorem B3047273 : Blo 1352995 3047273 := bstep (se 2 (by rfl) ⟨1142727, by rfl⟩ : syracuseStep 3047273 = 2285455) B2285455
theorem B4571423 : Blo 1352995 4571423 := bstep (se 1 (by rfl) ⟨3428567, by rfl⟩ : syracuseStep 4571423 = 6857135) B6857135
theorem B3047777 : Blo 1352995 3047777 := bstep (se 2 (by rfl) ⟨1142916, by rfl⟩ : syracuseStep 3047777 = 2285833) B2285833
theorem B3047867 : Blo 1352995 3047867 := bstep (se 1 (by rfl) ⟨2285900, by rfl⟩ : syracuseStep 3047867 = 4571801) B4571801
theorem B2032079 : Blo 1352995 2032079 := bstep (se 1 (by rfl) ⟨1524059, by rfl⟩ : syracuseStep 2032079 = 3048119) B3048119
theorem B2032121 : Blo 1352995 2032121 := bstep (se 2 (by rfl) ⟨762045, by rfl⟩ : syracuseStep 2032121 = 1524091) B1524091
theorem B2032223 : Blo 1352995 2032223 := bstep (se 1 (by rfl) ⟨1524167, by rfl⟩ : syracuseStep 2032223 = 3048335) B3048335
theorem B4883179 : Blo 1352995 4883179 := bstep (se 1 (by rfl) ⟨3662384, by rfl⟩ : syracuseStep 4883179 = 7324769) B7324769
theorem B4572071 : Blo 1352995 4572071 := bstep (se 1 (by rfl) ⟨3429053, by rfl⟩ : syracuseStep 4572071 = 6858107) B6858107
theorem B5866451 : Blo 1352995 5866451 := bstep (se 1 (by rfl) ⟨4399838, by rfl⟩ : syracuseStep 5866451 = 8799677) B8799677
theorem B39036005 : Blo 1352995 39036005 := bstep (se 4 (by rfl) ⟨3659625, by rfl⟩ : syracuseStep 39036005 = 7319251) B7319251
theorem B9897065 : Blo 1352995 9897065 := bstep (se 2 (by rfl) ⟨3711399, by rfl⟩ : syracuseStep 9897065 = 7422799) B7422799
theorem B22258921 : Blo 1352995 22258921 := bstep (se 2 (by rfl) ⟨8347095, by rfl⟩ : syracuseStep 22258921 = 16694191) B16694191
theorem B1353115 : Blo 1352995 1353115 := bstep (se 1 (by rfl) ⟨1014836, by rfl⟩ : syracuseStep 1353115 = 2029673) B2029673
theorem B6850007 : Blo 1352995 6850007 := bstep (se 1 (by rfl) ⟨5137505, by rfl⟩ : syracuseStep 6850007 = 10275011) B10275011
theorem B4572665 : Blo 1352995 4572665 := bstep (se 2 (by rfl) ⟨1714749, by rfl⟩ : syracuseStep 4572665 = 3429499) B3429499
theorem B1353327 : Blo 1352995 1353327 := bstep (se 1 (by rfl) ⟨1014995, by rfl⟩ : syracuseStep 1353327 = 2029991) B2029991
theorem B1353383 : Blo 1352995 1353383 := bstep (se 1 (by rfl) ⟨1015037, by rfl⟩ : syracuseStep 1353383 = 2030075) B2030075
theorem B2197243 : Blo 1352995 2197243 := bstep (se 1 (by rfl) ⟨1647932, by rfl⟩ : syracuseStep 2197243 = 3295865) B3295865
theorem B1353467 : Blo 1352995 1353467 := bstep (se 1 (by rfl) ⟨1015100, by rfl⟩ : syracuseStep 1353467 = 2030201) B2030201
theorem B4572935 : Blo 1352995 4572935 := bstep (se 1 (by rfl) ⟨3429701, by rfl⟩ : syracuseStep 4572935 = 6859403) B6859403
theorem B24708893 : Blo 1352995 24708893 := bstep (se 3 (by rfl) ⟨4632917, by rfl⟩ : syracuseStep 24708893 = 9265835) B9265835
theorem B1353503 : Blo 1352995 1353503 := bstep (se 1 (by rfl) ⟨1015127, by rfl⟩ : syracuseStep 1353503 = 2030255) B2030255
theorem B4572989 : Blo 1352995 4572989 := bstep (se 3 (by rfl) ⟨857435, by rfl⟩ : syracuseStep 4572989 = 1714871) B1714871
theorem B1353535 : Blo 1352995 1353535 := bstep (se 1 (by rfl) ⟨1015151, by rfl⟩ : syracuseStep 1353535 = 2030303) B2030303
theorem B6858593 : Blo 1352995 6858593 := bstep (se 2 (by rfl) ⟨2571972, by rfl⟩ : syracuseStep 6858593 = 5143945) B5143945
theorem B1353711 : Blo 1352995 1353711 := bstep (se 1 (by rfl) ⟨1015283, by rfl⟩ : syracuseStep 1353711 = 2030567) B2030567
theorem B12519467 : Blo 1352995 12519467 := bstep (se 1 (by rfl) ⟨9389600, by rfl⟩ : syracuseStep 12519467 = 18779201) B18779201
theorem B1353883 : Blo 1352995 1353883 := bstep (se 1 (by rfl) ⟨1015412, by rfl⟩ : syracuseStep 1353883 = 2030825) B2030825
theorem B1353919 : Blo 1352995 1353919 := bstep (se 1 (by rfl) ⟨1015439, by rfl⟩ : syracuseStep 1353919 = 2030879) B2030879
theorem B1927471 : Blo 1352995 1927471 := bstep (se 1 (by rfl) ⟨1445603, by rfl⟩ : syracuseStep 1927471 = 2891207) B2891207
theorem B1354031 : Blo 1352995 1354031 := bstep (se 1 (by rfl) ⟨1015523, by rfl⟩ : syracuseStep 1354031 = 2031047) B2031047
theorem B4114745 : Blo 1352995 4114745 := bstep (se 2 (by rfl) ⟨1543029, by rfl⟩ : syracuseStep 4114745 = 3086059) B3086059
theorem B8792459 : Blo 1352995 8792459 := bstep (se 1 (by rfl) ⟨6594344, by rfl⟩ : syracuseStep 8792459 = 13188689) B13188689
theorem B21973457 : Blo 1352995 21973457 := bstep (se 2 (by rfl) ⟨8240046, by rfl⟩ : syracuseStep 21973457 = 16480093) B16480093
theorem B1354267 : Blo 1352995 1354267 := bstep (se 1 (by rfl) ⟨1015700, by rfl⟩ : syracuseStep 1354267 = 2031401) B2031401
theorem B1354271 : Blo 1352995 1354271 := bstep (se 1 (by rfl) ⟨1015703, by rfl⟩ : syracuseStep 1354271 = 2031407) B2031407
theorem B8677925 : Blo 1352995 8677925 := bstep (se 4 (by rfl) ⟨813555, by rfl⟩ : syracuseStep 8677925 = 1627111) B1627111
theorem B7711271 : Blo 1352995 7711271 := bstep (se 1 (by rfl) ⟨5783453, by rfl⟩ : syracuseStep 7711271 = 11566907) B11566907
theorem B12356201 : Blo 1352995 12356201 := bstep (se 2 (by rfl) ⟨4633575, by rfl⟩ : syracuseStep 12356201 = 9267151) B9267151
theorem B7817867 : Blo 1352995 7817867 := bstep (se 1 (by rfl) ⟨5863400, by rfl⟩ : syracuseStep 7817867 = 11726801) B11726801
theorem B3852971 : Blo 1352995 3852971 := bstep (se 1 (by rfl) ⟨2889728, by rfl⟩ : syracuseStep 3852971 = 5779457) B5779457
theorem B8235695 : Blo 1352995 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B17345339 : Blo 1352995 17345339 := bstep (se 1 (by rfl) ⟨13009004, by rfl⟩ : syracuseStep 17345339 = 26018009) B26018009
theorem B1354587 : Blo 1352995 1354587 := bstep (se 1 (by rfl) ⟨1015940, by rfl⟩ : syracuseStep 1354587 = 2031881) B2031881
theorem B1354655 : Blo 1352995 1354655 := bstep (se 1 (by rfl) ⟨1015991, by rfl⟩ : syracuseStep 1354655 = 2031983) B2031983
theorem B1928171 : Blo 1352995 1928171 := bstep (se 1 (by rfl) ⟨1446128, by rfl⟩ : syracuseStep 1928171 = 2892257) B2892257
theorem B1354799 : Blo 1352995 1354799 := bstep (se 1 (by rfl) ⟨1016099, by rfl⟩ : syracuseStep 1354799 = 2032199) B2032199
theorem B1354823 : Blo 1352995 1354823 := bstep (se 1 (by rfl) ⟨1016117, by rfl⟩ : syracuseStep 1354823 = 2032235) B2032235
theorem B4877455 : Blo 1352995 4877455 := bstep (se 1 (by rfl) ⟨3658091, by rfl⟩ : syracuseStep 4877455 = 7316183) B7316183
theorem B1354975 : Blo 1352995 1354975 := bstep (se 1 (by rfl) ⟨1016231, by rfl⟩ : syracuseStep 1354975 = 2032463) B2032463
theorem B1928615 : Blo 1352995 1928615 := bstep (se 1 (by rfl) ⟨1446461, by rfl⟩ : syracuseStep 1928615 = 2892923) B2892923
theorem B4566455 : Blo 1352995 4566455 := bstep (se 1 (by rfl) ⟨3424841, by rfl⟩ : syracuseStep 4566455 = 6849683) B6849683
theorem B3853757 : Blo 1352995 3853757 := bstep (se 3 (by rfl) ⟨722579, by rfl⟩ : syracuseStep 3853757 = 1445159) B1445159
theorem B9260477 : Blo 1352995 9260477 := bstep (se 3 (by rfl) ⟨1736339, by rfl⟩ : syracuseStep 9260477 = 3472679) B3472679
theorem B4116329 : Blo 1352995 4116329 := bstep (se 2 (by rfl) ⟨1543623, by rfl⟩ : syracuseStep 4116329 = 3087247) B3087247
theorem B1445855 : Blo 1352995 1445855 := bstep (se 1 (by rfl) ⟨1084391, by rfl⟩ : syracuseStep 1445855 = 2168783) B2168783
theorem B10973171 : Blo 1352995 10973171 := bstep (se 1 (by rfl) ⟨8229878, by rfl⟩ : syracuseStep 10973171 = 16459757) B16459757
theorem B2781371 : Blo 1352995 2781371 := bstep (se 1 (by rfl) ⟨2086028, by rfl⟩ : syracuseStep 2781371 = 4172057) B4172057
theorem B4337975 : Blo 1352995 4337975 := bstep (se 1 (by rfl) ⟨3253481, by rfl⟩ : syracuseStep 4337975 = 6506963) B6506963
theorem B1831295 : Blo 1352995 1831295 := bstep (se 1 (by rfl) ⟨1373471, by rfl⟩ : syracuseStep 1831295 = 2746943) B2746943
theorem B23147207 : Blo 1352995 23147207 := bstep (se 1 (by rfl) ⟨17360405, by rfl⟩ : syracuseStep 23147207 = 34720811) B34720811
theorem B15413975 : Blo 1352995 15413975 := bstep (se 1 (by rfl) ⟨11560481, by rfl⟩ : syracuseStep 15413975 = 23120963) B23120963
theorem B4633469 : Blo 1352995 4633469 := bstep (se 3 (by rfl) ⟨868775, by rfl⟩ : syracuseStep 4633469 = 1737551) B1737551
theorem B10277927 : Blo 1352995 10277927 := bstep (se 1 (by rfl) ⟨7708445, by rfl⟩ : syracuseStep 10277927 = 15416891) B15416891
theorem B4117567 : Blo 1352995 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B3429449 : Blo 1352995 3429449 := bstep (se 2 (by rfl) ⟨1286043, by rfl⟩ : syracuseStep 3429449 = 2572087) B2572087
theorem B2569391 : Blo 1352995 2569391 := bstep (se 1 (by rfl) ⟨1927043, by rfl⟩ : syracuseStep 2569391 = 3854087) B3854087
theorem B3044627 : Blo 1352995 3044627 := bstep (se 1 (by rfl) ⟨2283470, by rfl⟩ : syracuseStep 3044627 = 4566941) B4566941
theorem B3044699 : Blo 1352995 3044699 := bstep (se 1 (by rfl) ⟨2283524, by rfl⟩ : syracuseStep 3044699 = 4567049) B4567049
theorem B4568507 : Blo 1352995 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B4339271 : Blo 1352995 4339271 := bstep (se 1 (by rfl) ⟨3254453, by rfl⟩ : syracuseStep 4339271 = 6508907) B6508907
theorem B7714439 : Blo 1352995 7714439 := bstep (se 1 (by rfl) ⟨5785829, by rfl⟩ : syracuseStep 7714439 = 11571659) B11571659
theorem B9762461 : Blo 1352995 9762461 := bstep (se 3 (by rfl) ⟨1830461, by rfl⟩ : syracuseStep 9762461 = 3660923) B3660923
theorem B2283295 : Blo 1352995 2283295 := bstep (se 1 (by rfl) ⟨1712471, by rfl⟩ : syracuseStep 2283295 = 3424943) B3424943
theorem B3045257 : Blo 1352995 3045257 := bstep (se 2 (by rfl) ⟨1141971, by rfl⟩ : syracuseStep 3045257 = 2283943) B2283943
theorem B2029511 : Blo 1352995 2029511 := bstep (se 1 (by rfl) ⟨1522133, by rfl⟩ : syracuseStep 2029511 = 3044267) B3044267
theorem B4569047 : Blo 1352995 4569047 := bstep (se 1 (by rfl) ⟨3426785, by rfl⟩ : syracuseStep 4569047 = 6853571) B6853571
theorem B2283511 : Blo 1352995 2283511 := bstep (se 1 (by rfl) ⟨1712633, by rfl⟩ : syracuseStep 2283511 = 3425267) B3425267
theorem B3045473 : Blo 1352995 3045473 := bstep (se 2 (by rfl) ⟨1142052, by rfl⟩ : syracuseStep 3045473 = 2284105) B2284105
theorem B13007081 : Blo 1352995 13007081 := bstep (se 2 (by rfl) ⟨4877655, by rfl⟩ : syracuseStep 13007081 = 9755311) B9755311
theorem B5142761 : Blo 1352995 5142761 := bstep (se 2 (by rfl) ⟨1928535, by rfl⟩ : syracuseStep 5142761 = 3857071) B3857071
theorem B3299561 : Blo 1352995 3299561 := bstep (se 2 (by rfl) ⟨1237335, by rfl⟩ : syracuseStep 3299561 = 2474671) B2474671
theorem B5142791 : Blo 1352995 5142791 := bstep (se 1 (by rfl) ⟨3857093, by rfl⟩ : syracuseStep 5142791 = 7714187) B7714187
theorem B2283815 : Blo 1352995 2283815 := bstep (se 1 (by rfl) ⟨1712861, by rfl⟩ : syracuseStep 2283815 = 3425723) B3425723
theorem B2029865 : Blo 1352995 2029865 := bstep (se 2 (by rfl) ⟨761199, by rfl⟩ : syracuseStep 2029865 = 1522399) B1522399
theorem B2029871 : Blo 1352995 2029871 := bstep (se 1 (by rfl) ⟨1522403, by rfl⟩ : syracuseStep 2029871 = 3044807) B3044807
theorem B17840513 : Blo 1352995 17840513 := bstep (se 2 (by rfl) ⟨6690192, by rfl⟩ : syracuseStep 17840513 = 13380385) B13380385
theorem B4569533 : Blo 1352995 4569533 := bstep (se 3 (by rfl) ⟨856787, by rfl⟩ : syracuseStep 4569533 = 1713575) B1713575
theorem B2030111 : Blo 1352995 2030111 := bstep (se 1 (by rfl) ⟨1522583, by rfl⟩ : syracuseStep 2030111 = 3045167) B3045167
theorem B58522175 : Blo 1352995 58522175 := bstep (se 1 (by rfl) ⟨43891631, by rfl⟩ : syracuseStep 58522175 = 87783263) B87783263
theorem B125041481 : Blo 1352995 125041481 := bstep (se 2 (by rfl) ⟨46890555, by rfl⟩ : syracuseStep 125041481 = 93781111) B93781111
theorem B10419023 : Blo 1352995 10419023 := bstep (se 1 (by rfl) ⟨7814267, by rfl⟩ : syracuseStep 10419023 = 15628535) B15628535
theorem B6855515 : Blo 1352995 6855515 := bstep (se 1 (by rfl) ⟨5141636, by rfl⟩ : syracuseStep 6855515 = 10283273) B10283273
theorem B2030495 : Blo 1352995 2030495 := bstep (se 1 (by rfl) ⟨1522871, by rfl⟩ : syracuseStep 2030495 = 3045743) B3045743
theorem B19528613 : Blo 1352995 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B2030543 : Blo 1352995 2030543 := bstep (se 1 (by rfl) ⟨1522907, by rfl⟩ : syracuseStep 2030543 = 3045815) B3045815
theorem B4881377 : Blo 1352995 4881377 := bstep (se 2 (by rfl) ⟨1830516, by rfl⟩ : syracuseStep 4881377 = 3661033) B3661033
theorem B2030633 : Blo 1352995 2030633 := bstep (se 2 (by rfl) ⟨761487, by rfl⟩ : syracuseStep 2030633 = 1522975) B1522975
theorem B2030639 : Blo 1352995 2030639 := bstep (se 1 (by rfl) ⟨1522979, by rfl⟩ : syracuseStep 2030639 = 3045959) B3045959
theorem B2284591 : Blo 1352995 2284591 := bstep (se 1 (by rfl) ⟨1713443, by rfl⟩ : syracuseStep 2284591 = 3426887) B3426887
theorem B8674361 : Blo 1352995 8674361 := bstep (se 2 (by rfl) ⟨3252885, by rfl⟩ : syracuseStep 8674361 = 6505771) B6505771
theorem B1522759 : Blo 1352995 1522759 := bstep (se 1 (by rfl) ⟨1142069, by rfl⟩ : syracuseStep 1522759 = 2284139) B2284139
theorem B2030663 : Blo 1352995 2030663 := bstep (se 1 (by rfl) ⟨1522997, by rfl⟩ : syracuseStep 2030663 = 3045995) B3045995
theorem B2571335 : Blo 1352995 2571335 := bstep (se 1 (by rfl) ⟨1928501, by rfl⟩ : syracuseStep 2571335 = 3857003) B3857003
theorem B4570397 : Blo 1352995 4570397 := bstep (se 3 (by rfl) ⟨856949, by rfl⟩ : syracuseStep 4570397 = 1713899) B1713899
theorem B10976543 : Blo 1352995 10976543 := bstep (se 1 (by rfl) ⟨8232407, by rfl⟩ : syracuseStep 10976543 = 16464815) B16464815
theorem B5782823 : Blo 1352995 5782823 := bstep (se 1 (by rfl) ⟨4337117, by rfl⟩ : syracuseStep 5782823 = 8674235) B8674235
theorem B9764135 : Blo 1352995 9764135 := bstep (se 1 (by rfl) ⟨7323101, by rfl⟩ : syracuseStep 9764135 = 14646203) B14646203
theorem B2030927 : Blo 1352995 2030927 := bstep (se 1 (by rfl) ⟨1523195, by rfl⟩ : syracuseStep 2030927 = 3046391) B3046391
theorem B2260303 : Blo 1352995 2260303 := bstep (se 1 (by rfl) ⟨1695227, by rfl⟩ : syracuseStep 2260303 = 3390455) B3390455
theorem B8674721 : Blo 1352995 8674721 := bstep (se 2 (by rfl) ⟨3253020, by rfl⟩ : syracuseStep 8674721 = 6506041) B6506041
theorem B3046823 : Blo 1352995 3046823 := bstep (se 1 (by rfl) ⟨2285117, by rfl⟩ : syracuseStep 3046823 = 4570235) B4570235
theorem B2031017 : Blo 1352995 2031017 := bstep (se 2 (by rfl) ⟨761631, by rfl⟩ : syracuseStep 2031017 = 1523263) B1523263
theorem B2284969 : Blo 1352995 2284969 := bstep (se 2 (by rfl) ⟨856863, by rfl⟩ : syracuseStep 2284969 = 1713727) B1713727
theorem B65846789 : Blo 1352995 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B2031167 : Blo 1352995 2031167 := bstep (se 1 (by rfl) ⟨1523375, by rfl⟩ : syracuseStep 2031167 = 3046751) B3046751
theorem B3047003 : Blo 1352995 3047003 := bstep (se 1 (by rfl) ⟨2285252, by rfl⟩ : syracuseStep 3047003 = 4570505) B4570505
theorem B2031431 : Blo 1352995 2031431 := bstep (se 1 (by rfl) ⟨1523573, by rfl⟩ : syracuseStep 2031431 = 3047147) B3047147
theorem B2285435 : Blo 1352995 2285435 := bstep (se 1 (by rfl) ⟨1714076, by rfl⟩ : syracuseStep 2285435 = 3428153) B3428153
theorem B3047291 : Blo 1352995 3047291 := bstep (se 1 (by rfl) ⟨2285468, by rfl⟩ : syracuseStep 3047291 = 4570937) B4570937
theorem B4882301 : Blo 1352995 4882301 := bstep (se 3 (by rfl) ⟨915431, by rfl⟩ : syracuseStep 4882301 = 1830863) B1830863
theorem B2031515 : Blo 1352995 2031515 := bstep (se 1 (by rfl) ⟨1523636, by rfl⟩ : syracuseStep 2031515 = 3047273) B3047273
theorem B3858347 : Blo 1352995 3858347 := bstep (se 1 (by rfl) ⟨2893760, by rfl⟩ : syracuseStep 3858347 = 5787521) B5787521
theorem B8675261 : Blo 1352995 8675261 := bstep (se 3 (by rfl) ⟨1626611, by rfl⟩ : syracuseStep 8675261 = 3253223) B3253223
theorem B18538469 : Blo 1352995 18538469 := bstep (se 4 (by rfl) ⟨1737981, by rfl⟩ : syracuseStep 18538469 = 3475963) B3475963
theorem B3047615 : Blo 1352995 3047615 := bstep (se 1 (by rfl) ⟨2285711, by rfl⟩ : syracuseStep 3047615 = 4571423) B4571423
theorem B2031851 : Blo 1352995 2031851 := bstep (se 1 (by rfl) ⟨1523888, by rfl⟩ : syracuseStep 2031851 = 3047777) B3047777
theorem B2031911 : Blo 1352995 2031911 := bstep (se 1 (by rfl) ⟨1523933, by rfl⟩ : syracuseStep 2031911 = 3047867) B3047867
theorem B3088979 : Blo 1352995 3088979 := bstep (se 1 (by rfl) ⟨2316734, by rfl⟩ : syracuseStep 3088979 = 4633469) B4633469
theorem B3048047 : Blo 1352995 3048047 := bstep (se 1 (by rfl) ⟨2286035, by rfl⟩ : syracuseStep 3048047 = 4572071) B4572071
theorem B2286299 : Blo 1352995 2286299 := bstep (se 1 (by rfl) ⟨1714724, by rfl⟩ : syracuseStep 2286299 = 3429449) B3429449
theorem B1712927 : Blo 1352995 1712927 := bstep (se 1 (by rfl) ⟨1284695, by rfl⟩ : syracuseStep 1712927 = 2569391) B2569391
theorem B11567933 : Blo 1352995 11567933 := bstep (se 3 (by rfl) ⟨2168987, by rfl⟩ : syracuseStep 11567933 = 4337975) B4337975
theorem B3048443 : Blo 1352995 3048443 := bstep (se 1 (by rfl) ⟨2286332, by rfl⟩ : syracuseStep 3048443 = 4572665) B4572665
theorem B4883453 : Blo 1352995 4883453 := bstep (se 3 (by rfl) ⟨915647, by rfl⟩ : syracuseStep 4883453 = 1831295) B1831295
theorem B2892847 : Blo 1352995 2892847 := bstep (se 1 (by rfl) ⟨2169635, by rfl⟩ : syracuseStep 2892847 = 4339271) B4339271
theorem B3048623 : Blo 1352995 3048623 := bstep (se 1 (by rfl) ⟨2286467, by rfl⟩ : syracuseStep 3048623 = 4572935) B4572935
theorem B3048659 : Blo 1352995 3048659 := bstep (se 1 (by rfl) ⟨2286494, by rfl⟩ : syracuseStep 3048659 = 4572989) B4572989
theorem B4572395 : Blo 1352995 4572395 := bstep (se 1 (by rfl) ⟨3429296, by rfl⟩ : syracuseStep 4572395 = 6858593) B6858593
theorem B1353007 : Blo 1352995 1353007 := bstep (se 1 (by rfl) ⟨1014755, by rfl⟩ : syracuseStep 1353007 = 2029511) B2029511
theorem B5490089 : Blo 1352995 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B1353243 : Blo 1352995 1353243 := bstep (se 1 (by rfl) ⟨1014932, by rfl⟩ : syracuseStep 1353243 = 2029865) B2029865
theorem B1353247 : Blo 1352995 1353247 := bstep (se 1 (by rfl) ⟨1014935, by rfl⟩ : syracuseStep 1353247 = 2029871) B2029871
theorem B14648971 : Blo 1352995 14648971 := bstep (se 1 (by rfl) ⟨10986728, by rfl⟩ : syracuseStep 14648971 = 21973457) B21973457
theorem B1353407 : Blo 1352995 1353407 := bstep (se 1 (by rfl) ⟨1015055, by rfl⟩ : syracuseStep 1353407 = 2030111) B2030111
theorem B5785283 : Blo 1352995 5785283 := bstep (se 1 (by rfl) ⟨4338962, by rfl⟩ : syracuseStep 5785283 = 8677925) B8677925
theorem B5211911 : Blo 1352995 5211911 := bstep (se 1 (by rfl) ⟨3908933, by rfl⟩ : syracuseStep 5211911 = 7817867) B7817867
theorem B1353663 : Blo 1352995 1353663 := bstep (se 1 (by rfl) ⟨1015247, by rfl⟩ : syracuseStep 1353663 = 2030495) B2030495
theorem B13019075 : Blo 1352995 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B1353695 : Blo 1352995 1353695 := bstep (se 1 (by rfl) ⟨1015271, by rfl⟩ : syracuseStep 1353695 = 2030543) B2030543
theorem B3254251 : Blo 1352995 3254251 := bstep (se 1 (by rfl) ⟨2440688, by rfl⟩ : syracuseStep 3254251 = 4881377) B4881377
theorem B1353755 : Blo 1352995 1353755 := bstep (se 1 (by rfl) ⟨1015316, by rfl⟩ : syracuseStep 1353755 = 2030633) B2030633
theorem B1353759 : Blo 1352995 1353759 := bstep (se 1 (by rfl) ⟨1015319, by rfl⟩ : syracuseStep 1353759 = 2030639) B2030639
theorem B1353775 : Blo 1352995 1353775 := bstep (se 1 (by rfl) ⟨1015331, by rfl⟩ : syracuseStep 1353775 = 2030663) B2030663
theorem B1714223 : Blo 1352995 1714223 := bstep (se 1 (by rfl) ⟨1285667, by rfl⟩ : syracuseStep 1714223 = 2571335) B2571335
theorem B65890381 : Blo 1352995 65890381 := bstep (se 3 (by rfl) ⟨12354446, by rfl⟩ : syracuseStep 65890381 = 24708893) B24708893
theorem B7317695 : Blo 1352995 7317695 := bstep (se 1 (by rfl) ⟨5488271, by rfl⟩ : syracuseStep 7317695 = 10976543) B10976543
theorem B1353951 : Blo 1352995 1353951 := bstep (se 1 (by rfl) ⟨1015463, by rfl⟩ : syracuseStep 1353951 = 2030927) B2030927
theorem B1354011 : Blo 1352995 1354011 := bstep (se 1 (by rfl) ⟨1015508, by rfl⟩ : syracuseStep 1354011 = 2031017) B2031017
theorem B1354111 : Blo 1352995 1354111 := bstep (se 1 (by rfl) ⟨1015583, by rfl⟩ : syracuseStep 1354111 = 2031167) B2031167
theorem B1354287 : Blo 1352995 1354287 := bstep (se 1 (by rfl) ⟨1015715, by rfl⟩ : syracuseStep 1354287 = 2031431) B2031431
theorem B3254867 : Blo 1352995 3254867 := bstep (se 1 (by rfl) ⟨2441150, by rfl⟩ : syracuseStep 3254867 = 4882301) B4882301
theorem B1354343 : Blo 1352995 1354343 := bstep (se 1 (by rfl) ⟨1015757, by rfl⟩ : syracuseStep 1354343 = 2031515) B2031515
theorem B1854247 : Blo 1352995 1854247 := bstep (se 1 (by rfl) ⟨1390685, by rfl⟩ : syracuseStep 1854247 = 2781371) B2781371
theorem B1354719 : Blo 1352995 1354719 := bstep (se 1 (by rfl) ⟨1016039, by rfl⟩ : syracuseStep 1354719 = 2032079) B2032079
theorem B1354747 : Blo 1352995 1354747 := bstep (se 1 (by rfl) ⟨1016060, by rfl⟩ : syracuseStep 1354747 = 2032121) B2032121
theorem B1354815 : Blo 1352995 1354815 := bstep (se 1 (by rfl) ⟨1016111, by rfl⟩ : syracuseStep 1354815 = 2032223) B2032223
theorem B10275983 : Blo 1352995 10275983 := bstep (se 1 (by rfl) ⟨7706987, by rfl⟩ : syracuseStep 10275983 = 15413975) B15413975
theorem B3910967 : Blo 1352995 3910967 := bstep (se 1 (by rfl) ⟨2933225, by rfl⟩ : syracuseStep 3910967 = 5866451) B5866451
theorem B6851951 : Blo 1352995 6851951 := bstep (se 1 (by rfl) ⟨5138963, by rfl⟩ : syracuseStep 6851951 = 10277927) B10277927
theorem B6598043 : Blo 1352995 6598043 := bstep (se 1 (by rfl) ⟨4948532, by rfl⟩ : syracuseStep 6598043 = 9897065) B9897065
theorem B4566671 : Blo 1352995 4566671 := bstep (se 1 (by rfl) ⟨3425003, by rfl⟩ : syracuseStep 4566671 = 6850007) B6850007
theorem B47574701 : Blo 1352995 47574701 := bstep (se 3 (by rfl) ⟨8920256, by rfl⟩ : syracuseStep 47574701 = 17840513) B17840513
theorem B6508307 : Blo 1352995 6508307 := bstep (se 1 (by rfl) ⟨4881230, by rfl⟩ : syracuseStep 6508307 = 9762461) B9762461
theorem B8671387 : Blo 1352995 8671387 := bstep (se 1 (by rfl) ⟨6503540, by rfl⟩ : syracuseStep 8671387 = 13007081) B13007081
theorem B3428507 : Blo 1352995 3428507 := bstep (se 1 (by rfl) ⟨2571380, by rfl⟩ : syracuseStep 3428507 = 5142761) B5142761
theorem B2199707 : Blo 1352995 2199707 := bstep (se 1 (by rfl) ⟨1649780, by rfl⟩ : syracuseStep 2199707 = 3299561) B3299561
theorem B3428527 : Blo 1352995 3428527 := bstep (se 1 (by rfl) ⟨2571395, by rfl⟩ : syracuseStep 3428527 = 5142791) B5142791
theorem B5861639 : Blo 1352995 5861639 := bstep (se 1 (by rfl) ⟨4396229, by rfl⟩ : syracuseStep 5861639 = 8792459) B8792459
theorem B5140847 : Blo 1352995 5140847 := bstep (se 1 (by rfl) ⟨3855635, by rfl⟩ : syracuseStep 5140847 = 7711271) B7711271
theorem B39014783 : Blo 1352995 39014783 := bstep (se 1 (by rfl) ⟨29261087, by rfl⟩ : syracuseStep 39014783 = 58522175) B58522175
theorem B8237467 : Blo 1352995 8237467 := bstep (se 1 (by rfl) ⟨6178100, by rfl⟩ : syracuseStep 8237467 = 12356201) B12356201
theorem B12054949 : Blo 1352995 12054949 := bstep (se 4 (by rfl) ⟨1130151, by rfl⟩ : syracuseStep 12054949 = 2260303) B2260303
theorem B2568647 : Blo 1352995 2568647 := bstep (se 1 (by rfl) ⟨1926485, by rfl⟩ : syracuseStep 2568647 = 3852971) B3852971
theorem B11563559 : Blo 1352995 11563559 := bstep (se 1 (by rfl) ⟨8672669, by rfl⟩ : syracuseStep 11563559 = 17345339) B17345339
theorem B3855215 : Blo 1352995 3855215 := bstep (se 1 (by rfl) ⟨2891411, by rfl⟩ : syracuseStep 3855215 = 5782823) B5782823
theorem B6509423 : Blo 1352995 6509423 := bstep (se 1 (by rfl) ⟨4882067, by rfl⟩ : syracuseStep 6509423 = 9764135) B9764135
theorem B3044303 : Blo 1352995 3044303 := bstep (se 1 (by rfl) ⟨2283227, by rfl⟩ : syracuseStep 3044303 = 4566455) B4566455
theorem B2569171 : Blo 1352995 2569171 := bstep (se 1 (by rfl) ⟨1926878, by rfl⟩ : syracuseStep 2569171 = 3853757) B3853757
theorem B6173651 : Blo 1352995 6173651 := bstep (se 1 (by rfl) ⟨4630238, by rfl⟩ : syracuseStep 6173651 = 9260477) B9260477
theorem B2929657 : Blo 1352995 2929657 := bstep (se 2 (by rfl) ⟨1098621, by rfl⟩ : syracuseStep 2929657 = 2197243) B2197243
theorem B43897859 : Blo 1352995 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B3044393 : Blo 1352995 3044393 := bstep (se 2 (by rfl) ⟨1141647, by rfl⟩ : syracuseStep 3044393 = 2283295) B2283295
theorem B3855613 : Blo 1352995 3855613 := bstep (se 3 (by rfl) ⟨722927, by rfl⟩ : syracuseStep 3855613 = 1445855) B1445855
theorem B5141789 : Blo 1352995 5141789 := bstep (se 3 (by rfl) ⟨964085, by rfl⟩ : syracuseStep 5141789 = 1928171) B1928171
theorem B12358979 : Blo 1352995 12358979 := bstep (se 1 (by rfl) ⟨9269234, by rfl⟩ : syracuseStep 12358979 = 18538469) B18538469
theorem B3044681 : Blo 1352995 3044681 := bstep (se 2 (by rfl) ⟨1141755, by rfl⟩ : syracuseStep 3044681 = 2283511) B2283511
theorem B2569961 : Blo 1352995 2569961 := bstep (se 2 (by rfl) ⟨963735, by rfl⟩ : syracuseStep 2569961 = 1927471) B1927471
theorem B15431471 : Blo 1352995 15431471 := bstep (se 1 (by rfl) ⟨11573603, by rfl⟩ : syracuseStep 15431471 = 23147207) B23147207
theorem B26024003 : Blo 1352995 26024003 := bstep (se 1 (by rfl) ⟨19518002, by rfl⟩ : syracuseStep 26024003 = 39036005) B39036005
theorem B2029751 : Blo 1352995 2029751 := bstep (se 1 (by rfl) ⟨1522313, by rfl⟩ : syracuseStep 2029751 = 3044627) B3044627
theorem B2029799 : Blo 1352995 2029799 := bstep (se 1 (by rfl) ⟨1522349, by rfl⟩ : syracuseStep 2029799 = 3044699) B3044699
theorem B3045671 : Blo 1352995 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B6510905 : Blo 1352995 6510905 := bstep (se 2 (by rfl) ⟨2441589, by rfl⟩ : syracuseStep 6510905 = 4883179) B4883179
theorem B5142959 : Blo 1352995 5142959 := bstep (se 1 (by rfl) ⟨3857219, by rfl⟩ : syracuseStep 5142959 = 7714439) B7714439
theorem B5142973 : Blo 1352995 5142973 := bstep (se 3 (by rfl) ⟨964307, by rfl⟩ : syracuseStep 5142973 = 1928615) B1928615
theorem B2030171 : Blo 1352995 2030171 := bstep (se 1 (by rfl) ⟨1522628, by rfl⟩ : syracuseStep 2030171 = 3045257) B3045257
theorem B3046031 : Blo 1352995 3046031 := bstep (se 1 (by rfl) ⟨2284523, by rfl⟩ : syracuseStep 3046031 = 4569047) B4569047
theorem B8346311 : Blo 1352995 8346311 := bstep (se 1 (by rfl) ⟨6259733, by rfl⟩ : syracuseStep 8346311 = 12519467) B12519467
theorem B3046121 : Blo 1352995 3046121 := bstep (se 2 (by rfl) ⟨1142295, by rfl⟩ : syracuseStep 3046121 = 2284591) B2284591
theorem B2030315 : Blo 1352995 2030315 := bstep (se 1 (by rfl) ⟨1522736, by rfl⟩ : syracuseStep 2030315 = 3045473) B3045473
theorem B2030345 : Blo 1352995 2030345 := bstep (se 2 (by rfl) ⟨761379, by rfl⟩ : syracuseStep 2030345 = 1522759) B1522759
theorem B6503273 : Blo 1352995 6503273 := bstep (se 2 (by rfl) ⟨2438727, by rfl⟩ : syracuseStep 6503273 = 4877455) B4877455
theorem B1522543 : Blo 1352995 1522543 := bstep (se 1 (by rfl) ⟨1141907, by rfl⟩ : syracuseStep 1522543 = 2283815) B2283815
theorem B2743163 : Blo 1352995 2743163 := bstep (se 1 (by rfl) ⟨2057372, by rfl⟩ : syracuseStep 2743163 = 4114745) B4114745
theorem B3046355 : Blo 1352995 3046355 := bstep (se 1 (by rfl) ⟨2284766, by rfl⟩ : syracuseStep 3046355 = 4569533) B4569533
theorem B29678561 : Blo 1352995 29678561 := bstep (se 2 (by rfl) ⟨11129460, by rfl⟩ : syracuseStep 29678561 = 22258921) B22258921
theorem B21961853 : Blo 1352995 21961853 := bstep (se 3 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 21961853 = 8235695) B8235695
theorem B83360987 : Blo 1352995 83360987 := bstep (se 1 (by rfl) ⟨62520740, by rfl⟩ : syracuseStep 83360987 = 125041481) B125041481
theorem B6946015 : Blo 1352995 6946015 := bstep (se 1 (by rfl) ⟨5209511, by rfl⟩ : syracuseStep 6946015 = 10419023) B10419023
theorem B3046625 : Blo 1352995 3046625 := bstep (se 2 (by rfl) ⟨1142484, by rfl⟩ : syracuseStep 3046625 = 2284969) B2284969
theorem B4570343 : Blo 1352995 4570343 := bstep (se 1 (by rfl) ⟨3427757, by rfl⟩ : syracuseStep 4570343 = 6855515) B6855515
theorem B5782907 : Blo 1352995 5782907 := bstep (se 1 (by rfl) ⟨4337180, by rfl⟩ : syracuseStep 5782907 = 8674361) B8674361
theorem B3046931 : Blo 1352995 3046931 := bstep (se 1 (by rfl) ⟨2285198, by rfl⟩ : syracuseStep 3046931 = 4570397) B4570397
theorem B5783147 : Blo 1352995 5783147 := bstep (se 1 (by rfl) ⟨4337360, by rfl⟩ : syracuseStep 5783147 = 8674721) B8674721
theorem B2031215 : Blo 1352995 2031215 := bstep (se 1 (by rfl) ⟨1523411, by rfl⟩ : syracuseStep 2031215 = 3046823) B3046823
theorem B2031335 : Blo 1352995 2031335 := bstep (se 1 (by rfl) ⟨1523501, by rfl⟩ : syracuseStep 2031335 = 3047003) B3047003
theorem B2744219 : Blo 1352995 2744219 := bstep (se 1 (by rfl) ⟨2058164, by rfl⟩ : syracuseStep 2744219 = 4116329) B4116329
theorem B1523623 : Blo 1352995 1523623 := bstep (se 1 (by rfl) ⟨1142717, by rfl⟩ : syracuseStep 1523623 = 2285435) B2285435
theorem B2031527 : Blo 1352995 2031527 := bstep (se 1 (by rfl) ⟨1523645, by rfl⟩ : syracuseStep 2031527 = 3047291) B3047291
theorem B2572231 : Blo 1352995 2572231 := bstep (se 1 (by rfl) ⟨1929173, by rfl⟩ : syracuseStep 2572231 = 3858347) B3858347
theorem B5783507 : Blo 1352995 5783507 := bstep (se 1 (by rfl) ⟨4337630, by rfl⟩ : syracuseStep 5783507 = 8675261) B8675261
theorem B7315447 : Blo 1352995 7315447 := bstep (se 1 (by rfl) ⟨5486585, by rfl⟩ : syracuseStep 7315447 = 10973171) B10973171
theorem B2285671 : Blo 1352995 2285671 := bstep (se 1 (by rfl) ⟨1714253, by rfl⟩ : syracuseStep 2285671 = 3428507) B3428507
theorem B1466471 : Blo 1352995 1466471 := bstep (se 1 (by rfl) ⟨1099853, by rfl⟩ : syracuseStep 1466471 = 2199707) B2199707
theorem B4571261 : Blo 1352995 4571261 := bstep (se 3 (by rfl) ⟨857111, by rfl⟩ : syracuseStep 4571261 = 1714223) B1714223
theorem B2031743 : Blo 1352995 2031743 := bstep (se 1 (by rfl) ⟨1523807, by rfl⟩ : syracuseStep 2031743 = 3047615) B3047615
theorem B3907759 : Blo 1352995 3907759 := bstep (se 1 (by rfl) ⟨2930819, by rfl⟩ : syracuseStep 3907759 = 5861639) B5861639
theorem B4571369 : Blo 1352995 4571369 := bstep (se 2 (by rfl) ⟨1714263, by rfl⟩ : syracuseStep 4571369 = 3428527) B3428527
theorem B26009855 : Blo 1352995 26009855 := bstep (se 1 (by rfl) ⟨19507391, by rfl⟩ : syracuseStep 26009855 = 39014783) B39014783
theorem B1712431 : Blo 1352995 1712431 := bstep (se 1 (by rfl) ⟨1284323, by rfl⟩ : syracuseStep 1712431 = 2568647) B2568647
theorem B7709039 : Blo 1352995 7709039 := bstep (se 1 (by rfl) ⟨5781779, by rfl⟩ : syracuseStep 7709039 = 11563559) B11563559
theorem B2032031 : Blo 1352995 2032031 := bstep (se 1 (by rfl) ⟨1524023, by rfl⟩ : syracuseStep 2032031 = 3048047) B3048047
theorem B1524199 : Blo 1352995 1524199 := bstep (se 1 (by rfl) ⟨1143149, by rfl⟩ : syracuseStep 1524199 = 2286299) B2286299
theorem B6857297 : Blo 1352995 6857297 := bstep (se 2 (by rfl) ⟨2571486, by rfl⟩ : syracuseStep 6857297 = 5142973) B5142973
theorem B2032295 : Blo 1352995 2032295 := bstep (se 1 (by rfl) ⟨1524221, by rfl⟩ : syracuseStep 2032295 = 3048443) B3048443
theorem B2032415 : Blo 1352995 2032415 := bstep (se 1 (by rfl) ⟨1524311, by rfl⟩ : syracuseStep 2032415 = 3048623) B3048623
theorem B2032439 : Blo 1352995 2032439 := bstep (se 1 (by rfl) ⟨1524329, by rfl⟩ : syracuseStep 2032439 = 3048659) B3048659
theorem B3048263 : Blo 1352995 3048263 := bstep (se 1 (by rfl) ⟨2286197, by rfl⟩ : syracuseStep 3048263 = 4572395) B4572395
theorem B1713307 : Blo 1352995 1713307 := bstep (se 1 (by rfl) ⟨1284980, by rfl⟩ : syracuseStep 1713307 = 2569961) B2569961
theorem B3425561 : Blo 1352995 3425561 := bstep (se 2 (by rfl) ⟨1284585, by rfl⟩ : syracuseStep 3425561 = 2569171) B2569171
theorem B1353167 : Blo 1352995 1353167 := bstep (se 1 (by rfl) ⟨1014875, by rfl⟩ : syracuseStep 1353167 = 2029751) B2029751
theorem B1353199 : Blo 1352995 1353199 := bstep (se 1 (by rfl) ⟨1014899, by rfl⟩ : syracuseStep 1353199 = 2029799) B2029799
theorem B1353447 : Blo 1352995 1353447 := bstep (se 1 (by rfl) ⟨1015085, by rfl⟩ : syracuseStep 1353447 = 2030171) B2030171
theorem B5564207 : Blo 1352995 5564207 := bstep (se 1 (by rfl) ⟨4173155, by rfl⟩ : syracuseStep 5564207 = 8346311) B8346311
theorem B1353543 : Blo 1352995 1353543 := bstep (se 1 (by rfl) ⟨1015157, by rfl⟩ : syracuseStep 1353543 = 2030315) B2030315
theorem B1353563 : Blo 1352995 1353563 := bstep (se 1 (by rfl) ⟨1015172, by rfl⟩ : syracuseStep 1353563 = 2030345) B2030345
theorem B4335515 : Blo 1352995 4335515 := bstep (se 1 (by rfl) ⟨3251636, by rfl⟩ : syracuseStep 4335515 = 6503273) B6503273
theorem B1828775 : Blo 1352995 1828775 := bstep (se 1 (by rfl) ⟨1371581, by rfl⟩ : syracuseStep 1828775 = 2743163) B2743163
theorem B19785707 : Blo 1352995 19785707 := bstep (se 1 (by rfl) ⟨14839280, by rfl⟩ : syracuseStep 19785707 = 29678561) B29678561
theorem B14641235 : Blo 1352995 14641235 := bstep (se 1 (by rfl) ⟨10980926, by rfl⟩ : syracuseStep 14641235 = 21961853) B21961853
theorem B6850655 : Blo 1352995 6850655 := bstep (se 1 (by rfl) ⟨5137991, by rfl⟩ : syracuseStep 6850655 = 10275983) B10275983
theorem B19531961 : Blo 1352995 19531961 := bstep (se 2 (by rfl) ⟨7324485, by rfl⟩ : syracuseStep 19531961 = 14648971) B14648971
theorem B64293061 : Blo 1352995 64293061 := bstep (se 4 (by rfl) ⟨6027474, by rfl⟩ : syracuseStep 64293061 = 12054949) B12054949
theorem B2607311 : Blo 1352995 2607311 := bstep (se 1 (by rfl) ⟨1955483, by rfl⟩ : syracuseStep 2607311 = 3910967) B3910967
theorem B1354143 : Blo 1352995 1354143 := bstep (se 1 (by rfl) ⟨1015607, by rfl⟩ : syracuseStep 1354143 = 2031215) B2031215
theorem B1354223 : Blo 1352995 1354223 := bstep (se 1 (by rfl) ⟨1015667, by rfl⟩ : syracuseStep 1354223 = 2031335) B2031335
theorem B1829479 : Blo 1352995 1829479 := bstep (se 1 (by rfl) ⟨1372109, by rfl⟩ : syracuseStep 1829479 = 2744219) B2744219
theorem B1354351 : Blo 1352995 1354351 := bstep (se 1 (by rfl) ⟨1015763, by rfl⟩ : syracuseStep 1354351 = 2031527) B2031527
theorem B87853841 : Blo 1352995 87853841 := bstep (se 2 (by rfl) ⟨32945190, by rfl⟩ : syracuseStep 87853841 = 65890381) B65890381
theorem B1354567 : Blo 1352995 1354567 := bstep (se 1 (by rfl) ⟨1015925, by rfl⟩ : syracuseStep 1354567 = 2031851) B2031851
theorem B1354607 : Blo 1352995 1354607 := bstep (se 1 (by rfl) ⟨1015955, by rfl⟩ : syracuseStep 1354607 = 2031911) B2031911
theorem B11561849 : Blo 1352995 11561849 := bstep (se 2 (by rfl) ⟨4335693, by rfl⟩ : syracuseStep 11561849 = 8671387) B8671387
theorem B3427231 : Blo 1352995 3427231 := bstep (se 1 (by rfl) ⟨2570423, by rfl⟩ : syracuseStep 3427231 = 5140847) B5140847
theorem B2059319 : Blo 1352995 2059319 := bstep (se 1 (by rfl) ⟨1544489, by rfl⟩ : syracuseStep 2059319 = 3088979) B3088979
theorem B7711955 : Blo 1352995 7711955 := bstep (se 1 (by rfl) ⟨5783966, by rfl⟩ : syracuseStep 7711955 = 11567933) B11567933
theorem B4115767 : Blo 1352995 4115767 := bstep (se 1 (by rfl) ⟨3086825, by rfl⟩ : syracuseStep 4115767 = 6173651) B6173651
theorem B3255635 : Blo 1352995 3255635 := bstep (se 1 (by rfl) ⟨2441726, by rfl⟩ : syracuseStep 3255635 = 4883453) B4883453
theorem B29265239 : Blo 1352995 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B3427859 : Blo 1352995 3427859 := bstep (se 1 (by rfl) ⟨2570894, by rfl⟩ : syracuseStep 3427859 = 5141789) B5141789
theorem B8679383 : Blo 1352995 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B4878463 : Blo 1352995 4878463 := bstep (se 1 (by rfl) ⟨3658847, by rfl⟩ : syracuseStep 4878463 = 7317695) B7317695
theorem B3428639 : Blo 1352995 3428639 := bstep (se 1 (by rfl) ⟨2571479, by rfl⟩ : syracuseStep 3428639 = 5142959) B5142959
theorem B9261353 : Blo 1352995 9261353 := bstep (se 2 (by rfl) ⟨3473007, by rfl⟩ : syracuseStep 9261353 = 6946015) B6946015
theorem B5140817 : Blo 1352995 5140817 := bstep (se 2 (by rfl) ⟨1927806, by rfl⟩ : syracuseStep 5140817 = 3855613) B3855613
theorem B13898429 : Blo 1352995 13898429 := bstep (se 3 (by rfl) ⟨2605955, by rfl⟩ : syracuseStep 13898429 = 5211911) B5211911
theorem B17355485 : Blo 1352995 17355485 := bstep (se 3 (by rfl) ⟨3254153, by rfl⟩ : syracuseStep 17355485 = 6508307) B6508307
theorem B4567805 : Blo 1352995 4567805 := bstep (se 3 (by rfl) ⟨856463, by rfl⟩ : syracuseStep 4567805 = 1712927) B1712927
theorem B4567967 : Blo 1352995 4567967 := bstep (se 1 (by rfl) ⟨3425975, by rfl⟩ : syracuseStep 4567967 = 6851951) B6851951
theorem B3855271 : Blo 1352995 3855271 := bstep (se 1 (by rfl) ⟨2891453, by rfl⟩ : syracuseStep 3855271 = 5782907) B5782907
theorem B3855431 : Blo 1352995 3855431 := bstep (se 1 (by rfl) ⟨2891573, by rfl⟩ : syracuseStep 3855431 = 5783147) B5783147
theorem B3044447 : Blo 1352995 3044447 := bstep (se 1 (by rfl) ⟨2283335, by rfl⟩ : syracuseStep 3044447 = 4566671) B4566671
theorem B31716467 : Blo 1352995 31716467 := bstep (se 1 (by rfl) ⟨23787350, by rfl⟩ : syracuseStep 31716467 = 47574701) B47574701
theorem B3429641 : Blo 1352995 3429641 := bstep (se 2 (by rfl) ⟨1286115, by rfl⟩ : syracuseStep 3429641 = 2572231) B2572231
theorem B3855671 : Blo 1352995 3855671 := bstep (se 1 (by rfl) ⟨2891753, by rfl⟩ : syracuseStep 3855671 = 5783507) B5783507
theorem B4339001 : Blo 1352995 4339001 := bstep (se 2 (by rfl) ⟨1627125, by rfl⟩ : syracuseStep 4339001 = 3254251) B3254251
theorem B9753929 : Blo 1352995 9753929 := bstep (se 2 (by rfl) ⟨3657723, by rfl⟩ : syracuseStep 9753929 = 7315447) B7315447
theorem B10983289 : Blo 1352995 10983289 := bstep (se 2 (by rfl) ⟨4118733, by rfl⟩ : syracuseStep 10983289 = 8237467) B8237467
theorem B2570143 : Blo 1352995 2570143 := bstep (se 1 (by rfl) ⟨1927607, by rfl⟩ : syracuseStep 2570143 = 3855215) B3855215
theorem B2029535 : Blo 1352995 2029535 := bstep (se 1 (by rfl) ⟨1522151, by rfl⟩ : syracuseStep 2029535 = 3044303) B3044303
theorem B2029595 : Blo 1352995 2029595 := bstep (se 1 (by rfl) ⟨1522196, by rfl⟩ : syracuseStep 2029595 = 3044393) B3044393
theorem B8239319 : Blo 1352995 8239319 := bstep (se 1 (by rfl) ⟨6179489, by rfl⟩ : syracuseStep 8239319 = 12358979) B12358979
theorem B2029787 : Blo 1352995 2029787 := bstep (se 1 (by rfl) ⟨1522340, by rfl⟩ : syracuseStep 2029787 = 3044681) B3044681
theorem B3660059 : Blo 1352995 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B2472329 : Blo 1352995 2472329 := bstep (se 2 (by rfl) ⟨927123, by rfl⟩ : syracuseStep 2472329 = 1854247) B1854247
theorem B3856855 : Blo 1352995 3856855 := bstep (se 1 (by rfl) ⟨2892641, by rfl⟩ : syracuseStep 3856855 = 5785283) B5785283
theorem B2030057 : Blo 1352995 2030057 := bstep (se 2 (by rfl) ⟨761271, by rfl⟩ : syracuseStep 2030057 = 1522543) B1522543
theorem B10287647 : Blo 1352995 10287647 := bstep (se 1 (by rfl) ⟨7715735, by rfl⟩ : syracuseStep 10287647 = 15431471) B15431471
theorem B3906209 : Blo 1352995 3906209 := bstep (se 2 (by rfl) ⟨1464828, by rfl⟩ : syracuseStep 3906209 = 2929657) B2929657
theorem B17349335 : Blo 1352995 17349335 := bstep (se 1 (by rfl) ⟨13012001, by rfl⟩ : syracuseStep 17349335 = 26024003) B26024003
theorem B3857129 : Blo 1352995 3857129 := bstep (se 2 (by rfl) ⟨1446423, by rfl⟩ : syracuseStep 3857129 = 2892847) B2892847
theorem B2030447 : Blo 1352995 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B4340603 : Blo 1352995 4340603 := bstep (se 1 (by rfl) ⟨3255452, by rfl⟩ : syracuseStep 4340603 = 6510905) B6510905
theorem B2169911 : Blo 1352995 2169911 := bstep (se 1 (by rfl) ⟨1627433, by rfl⟩ : syracuseStep 2169911 = 3254867) B3254867
theorem B2030687 : Blo 1352995 2030687 := bstep (se 1 (by rfl) ⟨1523015, by rfl⟩ : syracuseStep 2030687 = 3046031) B3046031
theorem B2030747 : Blo 1352995 2030747 := bstep (se 1 (by rfl) ⟨1523060, by rfl⟩ : syracuseStep 2030747 = 3046121) B3046121
theorem B2030903 : Blo 1352995 2030903 := bstep (se 1 (by rfl) ⟨1523177, by rfl⟩ : syracuseStep 2030903 = 3046355) B3046355
theorem B55573991 : Blo 1352995 55573991 := bstep (se 1 (by rfl) ⟨41680493, by rfl⟩ : syracuseStep 55573991 = 83360987) B83360987
theorem B2031083 : Blo 1352995 2031083 := bstep (se 1 (by rfl) ⟨1523312, by rfl⟩ : syracuseStep 2031083 = 3046625) B3046625
theorem B3046895 : Blo 1352995 3046895 := bstep (se 1 (by rfl) ⟨2285171, by rfl⟩ : syracuseStep 3046895 = 4570343) B4570343
theorem B4398695 : Blo 1352995 4398695 := bstep (se 1 (by rfl) ⟨3299021, by rfl⟩ : syracuseStep 4398695 = 6598043) B6598043
theorem B17358461 : Blo 1352995 17358461 := bstep (se 3 (by rfl) ⟨3254711, by rfl⟩ : syracuseStep 17358461 = 6509423) B6509423
theorem B2031287 : Blo 1352995 2031287 := bstep (se 1 (by rfl) ⟨1523465, by rfl⟩ : syracuseStep 2031287 = 3046931) B3046931
theorem B2031497 : Blo 1352995 2031497 := bstep (se 2 (by rfl) ⟨761811, by rfl⟩ : syracuseStep 2031497 = 1523623) B1523623
theorem B3047507 : Blo 1352995 3047507 := bstep (se 1 (by rfl) ⟨2285630, by rfl⟩ : syracuseStep 3047507 = 4571261) B4571261
theorem B3047561 : Blo 1352995 3047561 := bstep (se 2 (by rfl) ⟨1142835, by rfl⟩ : syracuseStep 3047561 = 2285671) B2285671
theorem B3047579 : Blo 1352995 3047579 := bstep (se 1 (by rfl) ⟨2285684, by rfl⟩ : syracuseStep 3047579 = 4571369) B4571369
theorem B6504617 : Blo 1352995 6504617 := bstep (se 2 (by rfl) ⟨2439231, by rfl⟩ : syracuseStep 6504617 = 4878463) B4878463
theorem B2285759 : Blo 1352995 2285759 := bstep (se 1 (by rfl) ⟨1714319, by rfl⟩ : syracuseStep 2285759 = 3428639) B3428639
theorem B5210345 : Blo 1352995 5210345 := bstep (se 2 (by rfl) ⟨1953879, by rfl⟩ : syracuseStep 5210345 = 3907759) B3907759
theorem B4571531 : Blo 1352995 4571531 := bstep (se 1 (by rfl) ⟨3428648, by rfl⟩ : syracuseStep 4571531 = 6857297) B6857297
theorem B9265619 : Blo 1352995 9265619 := bstep (se 1 (by rfl) ⟨6949214, by rfl⟩ : syracuseStep 9265619 = 13898429) B13898429
theorem B2032175 : Blo 1352995 2032175 := bstep (se 1 (by rfl) ⟨1524131, by rfl⟩ : syracuseStep 2032175 = 3048263) B3048263
theorem B2032265 : Blo 1352995 2032265 := bstep (se 2 (by rfl) ⟨762099, by rfl⟩ : syracuseStep 2032265 = 1524199) B1524199
theorem B21144311 : Blo 1352995 21144311 := bstep (se 1 (by rfl) ⟨15858233, by rfl⟩ : syracuseStep 21144311 = 31716467) B31716467
theorem B2286427 : Blo 1352995 2286427 := bstep (se 1 (by rfl) ⟨1714820, by rfl⟩ : syracuseStep 2286427 = 3429641) B3429641
theorem B2892667 : Blo 1352995 2892667 := bstep (se 1 (by rfl) ⟨2169500, by rfl⟩ : syracuseStep 2892667 = 4339001) B4339001
theorem B1353023 : Blo 1352995 1353023 := bstep (se 1 (by rfl) ⟨1014767, by rfl⟩ : syracuseStep 1353023 = 2029535) B2029535
theorem B13190471 : Blo 1352995 13190471 := bstep (se 1 (by rfl) ⟨9892853, by rfl⟩ : syracuseStep 13190471 = 19785707) B19785707
theorem B1353063 : Blo 1352995 1353063 := bstep (se 1 (by rfl) ⟨1014797, by rfl⟩ : syracuseStep 1353063 = 2029595) B2029595
theorem B1738207 : Blo 1352995 1738207 := bstep (se 1 (by rfl) ⟨1303655, by rfl⟩ : syracuseStep 1738207 = 2607311) B2607311
theorem B1353191 : Blo 1352995 1353191 := bstep (se 1 (by rfl) ⟨1014893, by rfl⟩ : syracuseStep 1353191 = 2029787) B2029787
theorem B1648219 : Blo 1352995 1648219 := bstep (se 1 (by rfl) ⟨1236164, by rfl⟩ : syracuseStep 1648219 = 2472329) B2472329
theorem B1353371 : Blo 1352995 1353371 := bstep (se 1 (by rfl) ⟨1015028, by rfl⟩ : syracuseStep 1353371 = 2030057) B2030057
theorem B6858431 : Blo 1352995 6858431 := bstep (se 1 (by rfl) ⟨5143823, by rfl⟩ : syracuseStep 6858431 = 10287647) B10287647
theorem B1353631 : Blo 1352995 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B2893735 : Blo 1352995 2893735 := bstep (se 1 (by rfl) ⟨2170301, by rfl⟩ : syracuseStep 2893735 = 4340603) B4340603
theorem B1353791 : Blo 1352995 1353791 := bstep (se 1 (by rfl) ⟨1015343, by rfl⟩ : syracuseStep 1353791 = 2030687) B2030687
theorem B1353831 : Blo 1352995 1353831 := bstep (se 1 (by rfl) ⟨1015373, by rfl⟩ : syracuseStep 1353831 = 2030747) B2030747
theorem B1353935 : Blo 1352995 1353935 := bstep (se 1 (by rfl) ⟨1015451, by rfl⟩ : syracuseStep 1353935 = 2030903) B2030903
theorem B1354055 : Blo 1352995 1354055 := bstep (se 1 (by rfl) ⟨1015541, by rfl⟩ : syracuseStep 1354055 = 2031083) B2031083
theorem B4876733 : Blo 1352995 4876733 := bstep (se 3 (by rfl) ⟨914387, by rfl⟩ : syracuseStep 4876733 = 1828775) B1828775
theorem B1354191 : Blo 1352995 1354191 := bstep (se 1 (by rfl) ⟨1015643, by rfl⟩ : syracuseStep 1354191 = 2031287) B2031287
theorem B3426857 : Blo 1352995 3426857 := bstep (se 2 (by rfl) ⟨1285071, by rfl⟩ : syracuseStep 3426857 = 2570143) B2570143
theorem B1354331 : Blo 1352995 1354331 := bstep (se 1 (by rfl) ⟨1015748, by rfl⟩ : syracuseStep 1354331 = 2031497) B2031497
theorem B5786255 : Blo 1352995 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B1354495 : Blo 1352995 1354495 := bstep (se 1 (by rfl) ⟨1015871, by rfl⟩ : syracuseStep 1354495 = 2031743) B2031743
theorem B3427211 : Blo 1352995 3427211 := bstep (se 1 (by rfl) ⟨2570408, by rfl⟩ : syracuseStep 3427211 = 5140817) B5140817
theorem B5139359 : Blo 1352995 5139359 := bstep (se 1 (by rfl) ⟨3854519, by rfl⟩ : syracuseStep 5139359 = 7709039) B7709039
theorem B85724081 : Blo 1352995 85724081 := bstep (se 2 (by rfl) ⟨32146530, by rfl⟩ : syracuseStep 85724081 = 64293061) B64293061
theorem B3910589 : Blo 1352995 3910589 := bstep (se 3 (by rfl) ⟨733235, by rfl⟩ : syracuseStep 3910589 = 1466471) B1466471
theorem B1354687 : Blo 1352995 1354687 := bstep (se 1 (by rfl) ⟨1016015, by rfl⟩ : syracuseStep 1354687 = 2032031) B2032031
theorem B1354863 : Blo 1352995 1354863 := bstep (se 1 (by rfl) ⟨1016147, by rfl⟩ : syracuseStep 1354863 = 2032295) B2032295
theorem B11570323 : Blo 1352995 11570323 := bstep (se 1 (by rfl) ⟨8677742, by rfl⟩ : syracuseStep 11570323 = 17355485) B17355485
theorem B1354943 : Blo 1352995 1354943 := bstep (se 1 (by rfl) ⟨1016207, by rfl⟩ : syracuseStep 1354943 = 2032415) B2032415
theorem B1354959 : Blo 1352995 1354959 := bstep (se 1 (by rfl) ⟨1016219, by rfl⟩ : syracuseStep 1354959 = 2032439) B2032439
theorem B5140361 : Blo 1352995 5140361 := bstep (se 2 (by rfl) ⟨1927635, by rfl⟩ : syracuseStep 5140361 = 3855271) B3855271
theorem B9760823 : Blo 1352995 9760823 := bstep (se 1 (by rfl) ⟨7320617, by rfl⟩ : syracuseStep 9760823 = 14641235) B14641235
theorem B4567103 : Blo 1352995 4567103 := bstep (se 1 (by rfl) ⟨3425327, by rfl⟩ : syracuseStep 4567103 = 6850655) B6850655
theorem B13021307 : Blo 1352995 13021307 := bstep (se 1 (by rfl) ⟨9765980, by rfl⟩ : syracuseStep 13021307 = 19531961) B19531961
theorem B5492879 : Blo 1352995 5492879 := bstep (se 1 (by rfl) ⟨4119659, by rfl⟩ : syracuseStep 5492879 = 8239319) B8239319
theorem B58569227 : Blo 1352995 58569227 := bstep (se 1 (by rfl) ⟨43926920, by rfl⟩ : syracuseStep 58569227 = 87853841) B87853841
theorem B1372879 : Blo 1352995 1372879 := bstep (se 1 (by rfl) ⟨1029659, by rfl⟩ : syracuseStep 1372879 = 2059319) B2059319
theorem B1446607 : Blo 1352995 1446607 := bstep (se 1 (by rfl) ⟨1084955, by rfl⟩ : syracuseStep 1446607 = 2169911) B2169911
theorem B5141303 : Blo 1352995 5141303 := bstep (se 1 (by rfl) ⟨3855977, by rfl⟩ : syracuseStep 5141303 = 7711955) B7711955
theorem B19510159 : Blo 1352995 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B37049327 : Blo 1352995 37049327 := bstep (se 1 (by rfl) ⟨27786995, by rfl⟩ : syracuseStep 37049327 = 55573991) B55573991
theorem B11572307 : Blo 1352995 11572307 := bstep (se 1 (by rfl) ⟨8679230, by rfl⟩ : syracuseStep 11572307 = 17358461) B17358461
theorem B14644385 : Blo 1352995 14644385 := bstep (se 2 (by rfl) ⟨5491644, by rfl⟩ : syracuseStep 14644385 = 10983289) B10983289
theorem B17339903 : Blo 1352995 17339903 := bstep (se 1 (by rfl) ⟨13004927, by rfl⟩ : syracuseStep 17339903 = 26009855) B26009855
theorem B6174235 : Blo 1352995 6174235 := bstep (se 1 (by rfl) ⟨4630676, by rfl⟩ : syracuseStep 6174235 = 9261353) B9261353
theorem B2283241 : Blo 1352995 2283241 := bstep (se 2 (by rfl) ⟨856215, by rfl⟩ : syracuseStep 2283241 = 1712431) B1712431
theorem B3045203 : Blo 1352995 3045203 := bstep (se 1 (by rfl) ⟨2283902, by rfl⟩ : syracuseStep 3045203 = 4567805) B4567805
theorem B3045311 : Blo 1352995 3045311 := bstep (se 1 (by rfl) ⟨2283983, by rfl⟩ : syracuseStep 3045311 = 4567967) B4567967
theorem B5142473 : Blo 1352995 5142473 := bstep (se 2 (by rfl) ⟨1928427, by rfl⟩ : syracuseStep 5142473 = 3856855) B3856855
theorem B2570287 : Blo 1352995 2570287 := bstep (se 1 (by rfl) ⟨1927715, by rfl⟩ : syracuseStep 2570287 = 3855431) B3855431
theorem B2029631 : Blo 1352995 2029631 := bstep (se 1 (by rfl) ⟨1522223, by rfl⟩ : syracuseStep 2029631 = 3044447) B3044447
theorem B2439305 : Blo 1352995 2439305 := bstep (se 2 (by rfl) ⟨914739, by rfl⟩ : syracuseStep 2439305 = 1829479) B1829479
theorem B2283707 : Blo 1352995 2283707 := bstep (se 1 (by rfl) ⟨1712780, by rfl⟩ : syracuseStep 2283707 = 3425561) B3425561
theorem B2570447 : Blo 1352995 2570447 := bstep (se 1 (by rfl) ⟨1927835, by rfl⟩ : syracuseStep 2570447 = 3855671) B3855671
theorem B6502619 : Blo 1352995 6502619 := bstep (se 1 (by rfl) ⟨4876964, by rfl⟩ : syracuseStep 6502619 = 9753929) B9753929
theorem B3709471 : Blo 1352995 3709471 := bstep (se 1 (by rfl) ⟨2782103, by rfl⟩ : syracuseStep 3709471 = 5564207) B5564207
theorem B4569641 : Blo 1352995 4569641 := bstep (se 2 (by rfl) ⟨1713615, by rfl⟩ : syracuseStep 4569641 = 3427231) B3427231
theorem B2890343 : Blo 1352995 2890343 := bstep (se 1 (by rfl) ⟨2167757, by rfl⟩ : syracuseStep 2890343 = 4335515) B4335515
theorem B2440039 : Blo 1352995 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B2284409 : Blo 1352995 2284409 := bstep (se 2 (by rfl) ⟨856653, by rfl⟩ : syracuseStep 2284409 = 1713307) B1713307
theorem B5487689 : Blo 1352995 5487689 := bstep (se 2 (by rfl) ⟨2057883, by rfl⟩ : syracuseStep 5487689 = 4115767) B4115767
theorem B2604139 : Blo 1352995 2604139 := bstep (se 1 (by rfl) ⟨1953104, by rfl⟩ : syracuseStep 2604139 = 3906209) B3906209
theorem B11566223 : Blo 1352995 11566223 := bstep (se 1 (by rfl) ⟨8674667, by rfl⟩ : syracuseStep 11566223 = 17349335) B17349335
theorem B2571419 : Blo 1352995 2571419 := bstep (se 1 (by rfl) ⟨1928564, by rfl⟩ : syracuseStep 2571419 = 3857129) B3857129
theorem B7707899 : Blo 1352995 7707899 := bstep (se 1 (by rfl) ⟨5780924, by rfl⟩ : syracuseStep 7707899 = 11561849) B11561849
theorem B2170423 : Blo 1352995 2170423 := bstep (se 1 (by rfl) ⟨1627817, by rfl⟩ : syracuseStep 2170423 = 3255635) B3255635
theorem B2031263 : Blo 1352995 2031263 := bstep (se 1 (by rfl) ⟨1523447, by rfl⟩ : syracuseStep 2031263 = 3046895) B3046895
theorem B2285239 : Blo 1352995 2285239 := bstep (se 1 (by rfl) ⟨1713929, by rfl⟩ : syracuseStep 2285239 = 3427859) B3427859
theorem B2932463 : Blo 1352995 2932463 := bstep (se 1 (by rfl) ⟨2199347, by rfl⟩ : syracuseStep 2932463 = 4398695) B4398695
theorem B2031671 : Blo 1352995 2031671 := bstep (se 1 (by rfl) ⟨1523753, by rfl⟩ : syracuseStep 2031671 = 3047507) B3047507
theorem B2031707 : Blo 1352995 2031707 := bstep (se 1 (by rfl) ⟨1523780, by rfl⟩ : syracuseStep 2031707 = 3047561) B3047561
theorem B3661919 : Blo 1352995 3661919 := bstep (se 1 (by rfl) ⟨2746439, by rfl⟩ : syracuseStep 3661919 = 5492879) B5492879
theorem B2031719 : Blo 1352995 2031719 := bstep (se 1 (by rfl) ⟨1523789, by rfl⟩ : syracuseStep 2031719 = 3047579) B3047579
theorem B1523839 : Blo 1352995 1523839 := bstep (se 1 (by rfl) ⟨1142879, by rfl⟩ : syracuseStep 1523839 = 2285759) B2285759
theorem B3047687 : Blo 1352995 3047687 := bstep (se 1 (by rfl) ⟨2285765, by rfl⟩ : syracuseStep 3047687 = 4571531) B4571531
theorem B6177079 : Blo 1352995 6177079 := bstep (se 1 (by rfl) ⟨4632809, by rfl⟩ : syracuseStep 6177079 = 9265619) B9265619
theorem B13894253 : Blo 1352995 13894253 := bstep (se 3 (by rfl) ⟨2605172, by rfl⟩ : syracuseStep 13894253 = 5210345) B5210345
theorem B24699551 : Blo 1352995 24699551 := bstep (se 1 (by rfl) ⟨18524663, by rfl⟩ : syracuseStep 24699551 = 37049327) B37049327
theorem B11559935 : Blo 1352995 11559935 := bstep (se 1 (by rfl) ⟨8669951, by rfl⟩ : syracuseStep 11559935 = 17339903) B17339903
theorem B3048569 : Blo 1352995 3048569 := bstep (se 2 (by rfl) ⟨1143213, by rfl⟩ : syracuseStep 3048569 = 2286427) B2286427
theorem B4572287 : Blo 1352995 4572287 := bstep (se 1 (by rfl) ⟨3429215, by rfl⟩ : syracuseStep 4572287 = 6858431) B6858431
theorem B3253385 : Blo 1352995 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B1353087 : Blo 1352995 1353087 := bstep (se 1 (by rfl) ⟨1014815, by rfl⟩ : syracuseStep 1353087 = 2029631) B2029631
theorem B1713631 : Blo 1352995 1713631 := bstep (se 1 (by rfl) ⟨1285223, by rfl⟩ : syracuseStep 1713631 = 2570447) B2570447
theorem B4335079 : Blo 1352995 4335079 := bstep (se 1 (by rfl) ⟨3251309, by rfl⟩ : syracuseStep 4335079 = 6502619) B6502619
theorem B15427097 : Blo 1352995 15427097 := bstep (se 2 (by rfl) ⟨5785161, by rfl⟩ : syracuseStep 15427097 = 11570323) B11570323
theorem B3426239 : Blo 1352995 3426239 := bstep (se 1 (by rfl) ⟨2569679, by rfl⟩ : syracuseStep 3426239 = 5139359) B5139359
theorem B57149387 : Blo 1352995 57149387 := bstep (se 1 (by rfl) ⟨42862040, by rfl⟩ : syracuseStep 57149387 = 85724081) B85724081
theorem B2607059 : Blo 1352995 2607059 := bstep (se 1 (by rfl) ⟨1955294, by rfl⟩ : syracuseStep 2607059 = 3910589) B3910589
theorem B2893897 : Blo 1352995 2893897 := bstep (se 2 (by rfl) ⟨1085211, by rfl⟩ : syracuseStep 2893897 = 2170423) B2170423
theorem B7710815 : Blo 1352995 7710815 := bstep (se 1 (by rfl) ⟨5783111, by rfl⟩ : syracuseStep 7710815 = 11566223) B11566223
theorem B1714279 : Blo 1352995 1714279 := bstep (se 1 (by rfl) ⟨1285709, by rfl⟩ : syracuseStep 1714279 = 2571419) B2571419
theorem B5138599 : Blo 1352995 5138599 := bstep (se 1 (by rfl) ⟨3853949, by rfl⟩ : syracuseStep 5138599 = 7707899) B7707899
theorem B1354175 : Blo 1352995 1354175 := bstep (se 1 (by rfl) ⟨1015631, by rfl⟩ : syracuseStep 1354175 = 2031263) B2031263
theorem B3426907 : Blo 1352995 3426907 := bstep (se 1 (by rfl) ⟨2570180, by rfl⟩ : syracuseStep 3426907 = 5140361) B5140361
theorem B6507215 : Blo 1352995 6507215 := bstep (se 1 (by rfl) ⟨4880411, by rfl⟩ : syracuseStep 6507215 = 9760823) B9760823
theorem B3427049 : Blo 1352995 3427049 := bstep (se 2 (by rfl) ⟨1285143, by rfl⟩ : syracuseStep 3427049 = 2570287) B2570287
theorem B4336411 : Blo 1352995 4336411 := bstep (se 1 (by rfl) ⟨3252308, by rfl⟩ : syracuseStep 4336411 = 6504617) B6504617
theorem B39046151 : Blo 1352995 39046151 := bstep (se 1 (by rfl) ⟨29284613, by rfl⟩ : syracuseStep 39046151 = 58569227) B58569227
theorem B1354783 : Blo 1352995 1354783 := bstep (se 1 (by rfl) ⟨1016087, by rfl⟩ : syracuseStep 1354783 = 2032175) B2032175
theorem B1354843 : Blo 1352995 1354843 := bstep (se 1 (by rfl) ⟨1016132, by rfl⟩ : syracuseStep 1354843 = 2032265) B2032265
theorem B3427535 : Blo 1352995 3427535 := bstep (se 1 (by rfl) ⟨2570651, by rfl⟩ : syracuseStep 3427535 = 5141303) B5141303
theorem B13888741 : Blo 1352995 13888741 := bstep (se 4 (by rfl) ⟨1302069, by rfl⟩ : syracuseStep 13888741 = 2604139) B2604139
theorem B8793647 : Blo 1352995 8793647 := bstep (se 1 (by rfl) ⟨6595235, by rfl⟩ : syracuseStep 8793647 = 13190471) B13190471
theorem B1928809 : Blo 1352995 1928809 := bstep (se 2 (by rfl) ⟨723303, by rfl⟩ : syracuseStep 1928809 = 1446607) B1446607
theorem B13004621 : Blo 1352995 13004621 := bstep (se 3 (by rfl) ⟨2438366, by rfl⟩ : syracuseStep 13004621 = 4876733) B4876733
theorem B26013545 : Blo 1352995 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B3428315 : Blo 1352995 3428315 := bstep (se 1 (by rfl) ⟨2571236, by rfl⟩ : syracuseStep 3428315 = 5142473) B5142473
theorem B1626203 : Blo 1352995 1626203 := bstep (se 1 (by rfl) ⟨1219652, by rfl⟩ : syracuseStep 1626203 = 2439305) B2439305
theorem B15430013 : Blo 1352995 15430013 := bstep (se 3 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 15430013 = 5786255) B5786255
theorem B7819901 : Blo 1352995 7819901 := bstep (se 3 (by rfl) ⟨1466231, by rfl⟩ : syracuseStep 7819901 = 2932463) B2932463
theorem B3658459 : Blo 1352995 3658459 := bstep (se 1 (by rfl) ⟨2743844, by rfl⟩ : syracuseStep 3658459 = 5487689) B5487689
theorem B3044321 : Blo 1352995 3044321 := bstep (se 2 (by rfl) ⟨1141620, by rfl⟩ : syracuseStep 3044321 = 2283241) B2283241
theorem B3044735 : Blo 1352995 3044735 := bstep (se 1 (by rfl) ⟨2283551, by rfl⟩ : syracuseStep 3044735 = 4567103) B4567103
theorem B8680871 : Blo 1352995 8680871 := bstep (se 1 (by rfl) ⟨6510653, by rfl⟩ : syracuseStep 8680871 = 13021307) B13021307
theorem B14096207 : Blo 1352995 14096207 := bstep (se 1 (by rfl) ⟨10572155, by rfl⟩ : syracuseStep 14096207 = 21144311) B21144311
theorem B4945961 : Blo 1352995 4945961 := bstep (se 2 (by rfl) ⟨1854735, by rfl⟩ : syracuseStep 4945961 = 3709471) B3709471
theorem B7714871 : Blo 1352995 7714871 := bstep (se 1 (by rfl) ⟨5786153, by rfl⟩ : syracuseStep 7714871 = 11572307) B11572307
theorem B9762923 : Blo 1352995 9762923 := bstep (se 1 (by rfl) ⟨7322192, by rfl⟩ : syracuseStep 9762923 = 14644385) B14644385
theorem B7322021 : Blo 1352995 7322021 := bstep (se 4 (by rfl) ⟨686439, by rfl⟩ : syracuseStep 7322021 = 1372879) B1372879
theorem B3856889 : Blo 1352995 3856889 := bstep (se 2 (by rfl) ⟨1446333, by rfl⟩ : syracuseStep 3856889 = 2892667) B2892667
theorem B2030135 : Blo 1352995 2030135 := bstep (se 1 (by rfl) ⟨1522601, by rfl⟩ : syracuseStep 2030135 = 3045203) B3045203
theorem B2030207 : Blo 1352995 2030207 := bstep (se 1 (by rfl) ⟨1522655, by rfl⟩ : syracuseStep 2030207 = 3045311) B3045311
theorem B1522471 : Blo 1352995 1522471 := bstep (se 1 (by rfl) ⟨1141853, by rfl⟩ : syracuseStep 1522471 = 2283707) B2283707
theorem B7707581 : Blo 1352995 7707581 := bstep (se 3 (by rfl) ⟨1445171, by rfl⟩ : syracuseStep 7707581 = 2890343) B2890343
theorem B2284571 : Blo 1352995 2284571 := bstep (se 1 (by rfl) ⟨1713428, by rfl⟩ : syracuseStep 2284571 = 3426857) B3426857
theorem B3046427 : Blo 1352995 3046427 := bstep (se 1 (by rfl) ⟨2284820, by rfl⟩ : syracuseStep 3046427 = 4569641) B4569641
theorem B1522939 : Blo 1352995 1522939 := bstep (se 1 (by rfl) ⟨1142204, by rfl⟩ : syracuseStep 1522939 = 2284409) B2284409
theorem B2284807 : Blo 1352995 2284807 := bstep (se 1 (by rfl) ⟨1713605, by rfl⟩ : syracuseStep 2284807 = 3427211) B3427211
theorem B2317609 : Blo 1352995 2317609 := bstep (se 2 (by rfl) ⟨869103, by rfl⟩ : syracuseStep 2317609 = 1738207) B1738207
theorem B8232313 : Blo 1352995 8232313 := bstep (se 2 (by rfl) ⟨3087117, by rfl⟩ : syracuseStep 8232313 = 6174235) B6174235
theorem B3046985 : Blo 1352995 3046985 := bstep (se 2 (by rfl) ⟨1142619, by rfl⟩ : syracuseStep 3046985 = 2285239) B2285239
theorem B140648021 : Blo 1352995 140648021 := bstep (se 8 (by rfl) ⟨824109, by rfl⟩ : syracuseStep 140648021 = 1648219) B1648219
theorem B3858313 : Blo 1352995 3858313 := bstep (se 2 (by rfl) ⟨1446867, by rfl⟩ : syracuseStep 3858313 = 2893735) B2893735
theorem B2441279 : Blo 1352995 2441279 := bstep (se 1 (by rfl) ⟨1830959, by rfl⟩ : syracuseStep 2441279 = 3661919) B3661919
theorem B3858529 : Blo 1352995 3858529 := bstep (se 2 (by rfl) ⟨1446948, by rfl⟩ : syracuseStep 3858529 = 2893897) B2893897
theorem B13189229 : Blo 1352995 13189229 := bstep (se 3 (by rfl) ⟨2472980, by rfl⟩ : syracuseStep 13189229 = 4945961) B4945961
theorem B2285705 : Blo 1352995 2285705 := bstep (se 2 (by rfl) ⟨857139, by rfl⟩ : syracuseStep 2285705 = 1714279) B1714279
theorem B2031785 : Blo 1352995 2031785 := bstep (se 2 (by rfl) ⟨761919, by rfl⟩ : syracuseStep 2031785 = 1523839) B1523839
theorem B2031791 : Blo 1352995 2031791 := bstep (se 1 (by rfl) ⟨1523843, by rfl⟩ : syracuseStep 2031791 = 3047687) B3047687
theorem B8675693 : Blo 1352995 8675693 := bstep (se 3 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 8675693 = 3253385) B3253385
theorem B2032379 : Blo 1352995 2032379 := bstep (se 1 (by rfl) ⟨1524284, by rfl⟩ : syracuseStep 2032379 = 3048569) B3048569
theorem B3048191 : Blo 1352995 3048191 := bstep (se 1 (by rfl) ⟨2286143, by rfl⟩ : syracuseStep 3048191 = 4572287) B4572287
theorem B9397471 : Blo 1352995 9397471 := bstep (se 1 (by rfl) ⟨7048103, by rfl⟩ : syracuseStep 9397471 = 14096207) B14096207
theorem B1738039 : Blo 1352995 1738039 := bstep (se 1 (by rfl) ⟨1303529, by rfl⟩ : syracuseStep 1738039 = 2607059) B2607059
theorem B1353423 : Blo 1352995 1353423 := bstep (se 1 (by rfl) ⟨1015067, by rfl⟩ : syracuseStep 1353423 = 2030135) B2030135
theorem B3090145 : Blo 1352995 3090145 := bstep (se 2 (by rfl) ⟨1158804, by rfl⟩ : syracuseStep 3090145 = 2317609) B2317609
theorem B65865469 : Blo 1352995 65865469 := bstep (se 3 (by rfl) ⟨12349775, by rfl⟩ : syracuseStep 65865469 = 24699551) B24699551
theorem B1353471 : Blo 1352995 1353471 := bstep (se 1 (by rfl) ⟨1015103, by rfl⟩ : syracuseStep 1353471 = 2030207) B2030207
theorem B5138387 : Blo 1352995 5138387 := bstep (se 1 (by rfl) ⟨3853790, by rfl⟩ : syracuseStep 5138387 = 7707581) B7707581
theorem B8669747 : Blo 1352995 8669747 := bstep (se 1 (by rfl) ⟨6502310, by rfl⟩ : syracuseStep 8669747 = 13004621) B13004621
theorem B1354447 : Blo 1352995 1354447 := bstep (se 1 (by rfl) ⟨1015835, by rfl⟩ : syracuseStep 1354447 = 2031671) B2031671
theorem B1354471 : Blo 1352995 1354471 := bstep (se 1 (by rfl) ⟨1015853, by rfl⟩ : syracuseStep 1354471 = 2031707) B2031707
theorem B1354479 : Blo 1352995 1354479 := bstep (se 1 (by rfl) ⟨1015859, by rfl⟩ : syracuseStep 1354479 = 2031719) B2031719
theorem B6851465 : Blo 1352995 6851465 := bstep (se 2 (by rfl) ⟨2569299, by rfl⟩ : syracuseStep 6851465 = 5138599) B5138599
theorem B4336541 : Blo 1352995 4336541 := bstep (se 3 (by rfl) ⟨813101, by rfl⟩ : syracuseStep 4336541 = 1626203) B1626203
theorem B5213267 : Blo 1352995 5213267 := bstep (se 1 (by rfl) ⟨3909950, by rfl⟩ : syracuseStep 5213267 = 7819901) B7819901
theorem B5787247 : Blo 1352995 5787247 := bstep (se 1 (by rfl) ⟨4340435, by rfl⟩ : syracuseStep 5787247 = 8680871) B8680871
theorem B4877945 : Blo 1352995 4877945 := bstep (se 2 (by rfl) ⟨1829229, by rfl⟩ : syracuseStep 4877945 = 3658459) B3658459
theorem B10284731 : Blo 1352995 10284731 := bstep (se 1 (by rfl) ⟨7713548, by rfl⟩ : syracuseStep 10284731 = 15427097) B15427097
theorem B5140543 : Blo 1352995 5140543 := bstep (se 1 (by rfl) ⟨3855407, by rfl⟩ : syracuseStep 5140543 = 7710815) B7710815
theorem B6508615 : Blo 1352995 6508615 := bstep (se 1 (by rfl) ⟨4881461, by rfl⟩ : syracuseStep 6508615 = 9762923) B9762923
theorem B32944421 : Blo 1352995 32944421 := bstep (se 4 (by rfl) ⟨3088539, by rfl⟩ : syracuseStep 32944421 = 6177079) B6177079
theorem B18518321 : Blo 1352995 18518321 := bstep (se 2 (by rfl) ⟨6944370, by rfl⟩ : syracuseStep 18518321 = 13888741) B13888741
theorem B4338143 : Blo 1352995 4338143 := bstep (se 1 (by rfl) ⟨3253607, by rfl⟩ : syracuseStep 4338143 = 6507215) B6507215
theorem B5780105 : Blo 1352995 5780105 := bstep (se 2 (by rfl) ⟨2167539, by rfl⟩ : syracuseStep 5780105 = 4335079) B4335079
theorem B26030767 : Blo 1352995 26030767 := bstep (se 1 (by rfl) ⟨19523075, by rfl⟩ : syracuseStep 26030767 = 39046151) B39046151
theorem B5862431 : Blo 1352995 5862431 := bstep (se 1 (by rfl) ⟨4396823, by rfl⟩ : syracuseStep 5862431 = 8793647) B8793647
theorem B10286675 : Blo 1352995 10286675 := bstep (se 1 (by rfl) ⟨7715006, by rfl⟩ : syracuseStep 10286675 = 15430013) B15430013
theorem B9262835 : Blo 1352995 9262835 := bstep (se 1 (by rfl) ⟨6947126, by rfl⟩ : syracuseStep 9262835 = 13894253) B13894253
theorem B2029547 : Blo 1352995 2029547 := bstep (se 1 (by rfl) ⟨1522160, by rfl⟩ : syracuseStep 2029547 = 3044321) B3044321
theorem B7706623 : Blo 1352995 7706623 := bstep (se 1 (by rfl) ⟨5779967, by rfl⟩ : syracuseStep 7706623 = 11559935) B11559935
theorem B4569209 : Blo 1352995 4569209 := bstep (se 2 (by rfl) ⟨1713453, by rfl⟩ : syracuseStep 4569209 = 3426907) B3426907
theorem B2029823 : Blo 1352995 2029823 := bstep (se 1 (by rfl) ⟨1522367, by rfl⟩ : syracuseStep 2029823 = 3044735) B3044735
theorem B5781881 : Blo 1352995 5781881 := bstep (se 2 (by rfl) ⟨2168205, by rfl⟩ : syracuseStep 5781881 = 4336411) B4336411
theorem B2029961 : Blo 1352995 2029961 := bstep (se 2 (by rfl) ⟨761235, by rfl⟩ : syracuseStep 2029961 = 1522471) B1522471
theorem B2284159 : Blo 1352995 2284159 := bstep (se 1 (by rfl) ⟨1713119, by rfl⟩ : syracuseStep 2284159 = 3426239) B3426239
theorem B38099591 : Blo 1352995 38099591 := bstep (se 1 (by rfl) ⟨28574693, by rfl⟩ : syracuseStep 38099591 = 57149387) B57149387
theorem B5143247 : Blo 1352995 5143247 := bstep (se 1 (by rfl) ⟨3857435, by rfl⟩ : syracuseStep 5143247 = 7714871) B7714871
theorem B4881347 : Blo 1352995 4881347 := bstep (se 1 (by rfl) ⟨3661010, by rfl⟩ : syracuseStep 4881347 = 7322021) B7322021
theorem B2030585 : Blo 1352995 2030585 := bstep (se 2 (by rfl) ⟨761469, by rfl⟩ : syracuseStep 2030585 = 1522939) B1522939
theorem B2571259 : Blo 1352995 2571259 := bstep (se 1 (by rfl) ⟨1928444, by rfl⟩ : syracuseStep 2571259 = 3856889) B3856889
theorem B3046409 : Blo 1352995 3046409 := bstep (se 2 (by rfl) ⟨1142403, by rfl⟩ : syracuseStep 3046409 = 2284807) B2284807
theorem B2284699 : Blo 1352995 2284699 := bstep (se 1 (by rfl) ⟨1713524, by rfl⟩ : syracuseStep 2284699 = 3427049) B3427049
theorem B10976417 : Blo 1352995 10976417 := bstep (se 2 (by rfl) ⟨4116156, by rfl⟩ : syracuseStep 10976417 = 8232313) B8232313
theorem B2284841 : Blo 1352995 2284841 := bstep (se 2 (by rfl) ⟨856815, by rfl⟩ : syracuseStep 2284841 = 1713631) B1713631
theorem B1523047 : Blo 1352995 1523047 := bstep (se 1 (by rfl) ⟨1142285, by rfl⟩ : syracuseStep 1523047 = 2284571) B2284571
theorem B2030951 : Blo 1352995 2030951 := bstep (se 1 (by rfl) ⟨1523213, by rfl⟩ : syracuseStep 2030951 = 3046427) B3046427
theorem B2285023 : Blo 1352995 2285023 := bstep (se 1 (by rfl) ⟨1713767, by rfl⟩ : syracuseStep 2285023 = 3427535) B3427535
theorem B2571745 : Blo 1352995 2571745 := bstep (se 2 (by rfl) ⟨964404, by rfl⟩ : syracuseStep 2571745 = 1928809) B1928809
theorem B2031323 : Blo 1352995 2031323 := bstep (se 1 (by rfl) ⟨1523492, by rfl⟩ : syracuseStep 2031323 = 3046985) B3046985
theorem B93765347 : Blo 1352995 93765347 := bstep (se 1 (by rfl) ⟨70324010, by rfl⟩ : syracuseStep 93765347 = 140648021) B140648021
theorem B5144417 : Blo 1352995 5144417 := bstep (se 2 (by rfl) ⟨1929156, by rfl⟩ : syracuseStep 5144417 = 3858313) B3858313
theorem B17342363 : Blo 1352995 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B2285543 : Blo 1352995 2285543 := bstep (se 1 (by rfl) ⟨1714157, by rfl⟩ : syracuseStep 2285543 = 3428315) B3428315
theorem B1523803 : Blo 1352995 1523803 := bstep (se 1 (by rfl) ⟨1142852, by rfl⟩ : syracuseStep 1523803 = 2285705) B2285705
theorem B5144705 : Blo 1352995 5144705 := bstep (se 2 (by rfl) ⟨1929264, by rfl⟩ : syracuseStep 5144705 = 3858529) B3858529
theorem B21962947 : Blo 1352995 21962947 := bstep (se 1 (by rfl) ⟨16472210, by rfl⟩ : syracuseStep 21962947 = 32944421) B32944421
theorem B12345547 : Blo 1352995 12345547 := bstep (se 1 (by rfl) ⟨9259160, by rfl⟩ : syracuseStep 12345547 = 18518321) B18518321
theorem B5783795 : Blo 1352995 5783795 := bstep (se 1 (by rfl) ⟨4337846, by rfl⟩ : syracuseStep 5783795 = 8675693) B8675693
theorem B2892095 : Blo 1352995 2892095 := bstep (se 1 (by rfl) ⟨2169071, by rfl⟩ : syracuseStep 2892095 = 4338143) B4338143
theorem B2032127 : Blo 1352995 2032127 := bstep (se 1 (by rfl) ⟨1524095, by rfl⟩ : syracuseStep 2032127 = 3048191) B3048191
theorem B3908287 : Blo 1352995 3908287 := bstep (se 1 (by rfl) ⟨2931215, by rfl⟩ : syracuseStep 3908287 = 5862431) B5862431
theorem B15418349 : Blo 1352995 15418349 := bstep (se 3 (by rfl) ⟨2890940, by rfl⟩ : syracuseStep 15418349 = 5781881) B5781881
theorem B6857783 : Blo 1352995 6857783 := bstep (se 1 (by rfl) ⟨5143337, by rfl⟩ : syracuseStep 6857783 = 10286675) B10286675
theorem B3425591 : Blo 1352995 3425591 := bstep (se 1 (by rfl) ⟨2569193, by rfl⟩ : syracuseStep 3425591 = 5138387) B5138387
theorem B1353031 : Blo 1352995 1353031 := bstep (se 1 (by rfl) ⟨1014773, by rfl⟩ : syracuseStep 1353031 = 2029547) B2029547
theorem B1353215 : Blo 1352995 1353215 := bstep (se 1 (by rfl) ⟨1014911, by rfl⟩ : syracuseStep 1353215 = 2029823) B2029823
theorem B1353307 : Blo 1352995 1353307 := bstep (se 1 (by rfl) ⟨1014980, by rfl⟩ : syracuseStep 1353307 = 2029961) B2029961
theorem B3254231 : Blo 1352995 3254231 := bstep (se 1 (by rfl) ⟨2440673, by rfl⟩ : syracuseStep 3254231 = 4881347) B4881347
theorem B1353723 : Blo 1352995 1353723 := bstep (se 1 (by rfl) ⟨1015292, by rfl⟩ : syracuseStep 1353723 = 2030585) B2030585
theorem B3475511 : Blo 1352995 3475511 := bstep (se 1 (by rfl) ⟨2606633, by rfl⟩ : syracuseStep 3475511 = 5213267) B5213267
theorem B7317611 : Blo 1352995 7317611 := bstep (se 1 (by rfl) ⟨5488208, by rfl⟩ : syracuseStep 7317611 = 10976417) B10976417
theorem B1353967 : Blo 1352995 1353967 := bstep (se 1 (by rfl) ⟨1015475, by rfl⟩ : syracuseStep 1353967 = 2030951) B2030951
theorem B87820625 : Blo 1352995 87820625 := bstep (se 2 (by rfl) ⟨32932734, by rfl⟩ : syracuseStep 87820625 = 65865469) B65865469
theorem B1354215 : Blo 1352995 1354215 := bstep (se 1 (by rfl) ⟨1015661, by rfl⟩ : syracuseStep 1354215 = 2031323) B2031323
theorem B11561575 : Blo 1352995 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B10275497 : Blo 1352995 10275497 := bstep (se 2 (by rfl) ⟨3853311, by rfl⟩ : syracuseStep 10275497 = 7706623) B7706623
theorem B8792819 : Blo 1352995 8792819 := bstep (se 1 (by rfl) ⟨6594614, by rfl⟩ : syracuseStep 8792819 = 13189229) B13189229
theorem B8678153 : Blo 1352995 8678153 := bstep (se 2 (by rfl) ⟨3254307, by rfl⟩ : syracuseStep 8678153 = 6508615) B6508615
theorem B1354523 : Blo 1352995 1354523 := bstep (se 1 (by rfl) ⟨1015892, by rfl⟩ : syracuseStep 1354523 = 2031785) B2031785
theorem B1354527 : Blo 1352995 1354527 := bstep (se 1 (by rfl) ⟨1015895, by rfl⟩ : syracuseStep 1354527 = 2031791) B2031791
theorem B3853403 : Blo 1352995 3853403 := bstep (se 1 (by rfl) ⟨2890052, by rfl⟩ : syracuseStep 3853403 = 5780105) B5780105
theorem B1354919 : Blo 1352995 1354919 := bstep (se 1 (by rfl) ⟨1016189, by rfl⟩ : syracuseStep 1354919 = 2032379) B2032379
theorem B3428345 : Blo 1352995 3428345 := bstep (se 2 (by rfl) ⟨1285629, by rfl⟩ : syracuseStep 3428345 = 2571259) B2571259
theorem B12529961 : Blo 1352995 12529961 := bstep (se 2 (by rfl) ⟨4698735, by rfl⟩ : syracuseStep 12529961 = 9397471) B9397471
theorem B5779831 : Blo 1352995 5779831 := bstep (se 1 (by rfl) ⟨4334873, by rfl⟩ : syracuseStep 5779831 = 8669747) B8669747
theorem B25399727 : Blo 1352995 25399727 := bstep (se 1 (by rfl) ⟨19049795, by rfl⟩ : syracuseStep 25399727 = 38099591) B38099591
theorem B3428831 : Blo 1352995 3428831 := bstep (se 1 (by rfl) ⟨2571623, by rfl⟩ : syracuseStep 3428831 = 5143247) B5143247
theorem B4567643 : Blo 1352995 4567643 := bstep (se 1 (by rfl) ⟨3425732, by rfl⟩ : syracuseStep 4567643 = 6851465) B6851465
theorem B3428993 : Blo 1352995 3428993 := bstep (se 2 (by rfl) ⟨1285872, by rfl⟩ : syracuseStep 3428993 = 2571745) B2571745
theorem B62510231 : Blo 1352995 62510231 := bstep (se 1 (by rfl) ⟨46882673, by rfl⟩ : syracuseStep 62510231 = 93765347) B93765347
theorem B3429611 : Blo 1352995 3429611 := bstep (se 1 (by rfl) ⟨2572208, by rfl⟩ : syracuseStep 3429611 = 5144417) B5144417
theorem B6854057 : Blo 1352995 6854057 := bstep (se 2 (by rfl) ⟨2570271, by rfl⟩ : syracuseStep 6854057 = 5140543) B5140543
theorem B6510077 : Blo 1352995 6510077 := bstep (se 3 (by rfl) ⟨1220639, by rfl⟩ : syracuseStep 6510077 = 2441279) B2441279
theorem B3045545 : Blo 1352995 3045545 := bstep (se 2 (by rfl) ⟨1142079, by rfl⟩ : syracuseStep 3045545 = 2284159) B2284159
theorem B34707689 : Blo 1352995 34707689 := bstep (se 2 (by rfl) ⟨13015383, by rfl⟩ : syracuseStep 34707689 = 26030767) B26030767
theorem B6175223 : Blo 1352995 6175223 := bstep (se 1 (by rfl) ⟨4631417, by rfl⟩ : syracuseStep 6175223 = 9262835) B9262835
theorem B3046139 : Blo 1352995 3046139 := bstep (se 1 (by rfl) ⟨2284604, by rfl⟩ : syracuseStep 3046139 = 4569209) B4569209
theorem B3046265 : Blo 1352995 3046265 := bstep (se 2 (by rfl) ⟨1142349, by rfl⟩ : syracuseStep 3046265 = 2284699) B2284699
theorem B2317385 : Blo 1352995 2317385 := bstep (se 2 (by rfl) ⟨869019, by rfl⟩ : syracuseStep 2317385 = 1738039) B1738039
theorem B2030729 : Blo 1352995 2030729 := bstep (se 2 (by rfl) ⟨761523, by rfl⟩ : syracuseStep 2030729 = 1523047) B1523047
theorem B2891027 : Blo 1352995 2891027 := bstep (se 1 (by rfl) ⟨2168270, by rfl⟩ : syracuseStep 2891027 = 4336541) B4336541
theorem B3046697 : Blo 1352995 3046697 := bstep (se 2 (by rfl) ⟨1142511, by rfl⟩ : syracuseStep 3046697 = 2285023) B2285023
theorem B2030939 : Blo 1352995 2030939 := bstep (se 1 (by rfl) ⟨1523204, by rfl⟩ : syracuseStep 2030939 = 3046409) B3046409
theorem B7716329 : Blo 1352995 7716329 := bstep (se 2 (by rfl) ⟨2893623, by rfl⟩ : syracuseStep 7716329 = 5787247) B5787247
theorem B1523227 : Blo 1352995 1523227 := bstep (se 1 (by rfl) ⟨1142420, by rfl⟩ : syracuseStep 1523227 = 2284841) B2284841
theorem B4120193 : Blo 1352995 4120193 := bstep (se 2 (by rfl) ⟨1545072, by rfl⟩ : syracuseStep 4120193 = 3090145) B3090145
theorem B3251963 : Blo 1352995 3251963 := bstep (se 1 (by rfl) ⟨2438972, by rfl⟩ : syracuseStep 3251963 = 4877945) B4877945
theorem B6856487 : Blo 1352995 6856487 := bstep (se 1 (by rfl) ⟨5142365, by rfl⟩ : syracuseStep 6856487 = 10284731) B10284731
theorem B1523695 : Blo 1352995 1523695 := bstep (se 1 (by rfl) ⟨1142771, by rfl⟩ : syracuseStep 1523695 = 2285543) B2285543
theorem B2031737 : Blo 1352995 2031737 := bstep (se 2 (by rfl) ⟨761901, by rfl⟩ : syracuseStep 2031737 = 1523803) B1523803
theorem B16933151 : Blo 1352995 16933151 := bstep (se 1 (by rfl) ⟨12699863, by rfl⟩ : syracuseStep 16933151 = 25399727) B25399727
theorem B2285887 : Blo 1352995 2285887 := bstep (se 1 (by rfl) ⟨1714415, by rfl⟩ : syracuseStep 2285887 = 3428831) B3428831
theorem B2285995 : Blo 1352995 2285995 := bstep (se 1 (by rfl) ⟨1714496, by rfl⟩ : syracuseStep 2285995 = 3428993) B3428993
theorem B4571855 : Blo 1352995 4571855 := bstep (se 1 (by rfl) ⟨3428891, by rfl⟩ : syracuseStep 4571855 = 6857783) B6857783
theorem B41673487 : Blo 1352995 41673487 := bstep (se 1 (by rfl) ⟨31255115, by rfl⟩ : syracuseStep 41673487 = 62510231) B62510231
theorem B2286407 : Blo 1352995 2286407 := bstep (se 1 (by rfl) ⟨1714805, by rfl⟩ : syracuseStep 2286407 = 3429611) B3429611
theorem B5211049 : Blo 1352995 5211049 := bstep (se 2 (by rfl) ⟨1954143, by rfl⟩ : syracuseStep 5211049 = 3908287) B3908287
theorem B10987181 : Blo 1352995 10987181 := bstep (se 3 (by rfl) ⟨2060096, by rfl⟩ : syracuseStep 10987181 = 4120193) B4120193
theorem B6850331 : Blo 1352995 6850331 := bstep (se 1 (by rfl) ⟨5137748, by rfl⟩ : syracuseStep 6850331 = 10275497) B10275497
theorem B5785435 : Blo 1352995 5785435 := bstep (se 1 (by rfl) ⟨4339076, by rfl⟩ : syracuseStep 5785435 = 8678153) B8678153
theorem B1353819 : Blo 1352995 1353819 := bstep (se 1 (by rfl) ⟨1015364, by rfl⟩ : syracuseStep 1353819 = 2030729) B2030729
theorem B1927351 : Blo 1352995 1927351 := bstep (se 1 (by rfl) ⟨1445513, by rfl⟩ : syracuseStep 1927351 = 2891027) B2891027
theorem B1353959 : Blo 1352995 1353959 := bstep (se 1 (by rfl) ⟨1015469, by rfl⟩ : syracuseStep 1353959 = 2030939) B2030939
theorem B1928063 : Blo 1352995 1928063 := bstep (se 1 (by rfl) ⟨1446047, by rfl⟩ : syracuseStep 1928063 = 2892095) B2892095
theorem B16460729 : Blo 1352995 16460729 := bstep (se 2 (by rfl) ⟨6172773, by rfl⟩ : syracuseStep 16460729 = 12345547) B12345547
theorem B1354751 : Blo 1352995 1354751 := bstep (se 1 (by rfl) ⟨1016063, by rfl⟩ : syracuseStep 1354751 = 2032127) B2032127
theorem B4878407 : Blo 1352995 4878407 := bstep (se 1 (by rfl) ⟨3658805, by rfl⟩ : syracuseStep 4878407 = 7317611) B7317611
theorem B23138459 : Blo 1352995 23138459 := bstep (se 1 (by rfl) ⟨17353844, by rfl⟩ : syracuseStep 23138459 = 34707689) B34707689
theorem B4116815 : Blo 1352995 4116815 := bstep (se 1 (by rfl) ⟨3087611, by rfl⟩ : syracuseStep 4116815 = 6175223) B6175223
theorem B5861879 : Blo 1352995 5861879 := bstep (se 1 (by rfl) ⟨4396409, by rfl⟩ : syracuseStep 5861879 = 8792819) B8792819
theorem B1544923 : Blo 1352995 1544923 := bstep (se 1 (by rfl) ⟨1158692, by rfl⟩ : syracuseStep 1544923 = 2317385) B2317385
theorem B2568935 : Blo 1352995 2568935 := bstep (se 1 (by rfl) ⟨1926701, by rfl⟩ : syracuseStep 2568935 = 3853403) B3853403
theorem B2167975 : Blo 1352995 2167975 := bstep (se 1 (by rfl) ⟨1625981, by rfl⟩ : syracuseStep 2167975 = 3251963) B3251963
theorem B3429803 : Blo 1352995 3429803 := bstep (se 1 (by rfl) ⟨2572352, by rfl⟩ : syracuseStep 3429803 = 5144705) B5144705
theorem B3855863 : Blo 1352995 3855863 := bstep (se 1 (by rfl) ⟨2891897, by rfl⟩ : syracuseStep 3855863 = 5783795) B5783795
theorem B8353307 : Blo 1352995 8353307 := bstep (se 1 (by rfl) ⟨6264980, by rfl⟩ : syracuseStep 8353307 = 12529961) B12529961
theorem B29283929 : Blo 1352995 29283929 := bstep (se 2 (by rfl) ⟨10981473, by rfl⟩ : syracuseStep 29283929 = 21962947) B21962947
theorem B3045095 : Blo 1352995 3045095 := bstep (se 1 (by rfl) ⟨2283821, by rfl⟩ : syracuseStep 3045095 = 4567643) B4567643
theorem B2285563 : Blo 1352995 2285563 := bstep (se 1 (by rfl) ⟨1714172, by rfl⟩ : syracuseStep 2285563 = 3428345) B3428345
theorem B7706441 : Blo 1352995 7706441 := bstep (se 2 (by rfl) ⟨2889915, by rfl⟩ : syracuseStep 7706441 = 5779831) B5779831
theorem B10278899 : Blo 1352995 10278899 := bstep (se 1 (by rfl) ⟨7709174, by rfl⟩ : syracuseStep 10278899 = 15418349) B15418349
theorem B15415433 : Blo 1352995 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B2283727 : Blo 1352995 2283727 := bstep (se 1 (by rfl) ⟨1712795, by rfl⟩ : syracuseStep 2283727 = 3425591) B3425591
theorem B4569371 : Blo 1352995 4569371 := bstep (se 1 (by rfl) ⟨3427028, by rfl⟩ : syracuseStep 4569371 = 6854057) B6854057
theorem B4340051 : Blo 1352995 4340051 := bstep (se 1 (by rfl) ⟨3255038, by rfl⟩ : syracuseStep 4340051 = 6510077) B6510077
theorem B2169487 : Blo 1352995 2169487 := bstep (se 1 (by rfl) ⟨1627115, by rfl⟩ : syracuseStep 2169487 = 3254231) B3254231
theorem B2317007 : Blo 1352995 2317007 := bstep (se 1 (by rfl) ⟨1737755, by rfl⟩ : syracuseStep 2317007 = 3475511) B3475511
theorem B2030363 : Blo 1352995 2030363 := bstep (se 1 (by rfl) ⟨1522772, by rfl⟩ : syracuseStep 2030363 = 3045545) B3045545
theorem B58547083 : Blo 1352995 58547083 := bstep (se 1 (by rfl) ⟨43910312, by rfl⟩ : syracuseStep 58547083 = 87820625) B87820625
theorem B2030759 : Blo 1352995 2030759 := bstep (se 1 (by rfl) ⟨1523069, by rfl⟩ : syracuseStep 2030759 = 3046139) B3046139
theorem B2030843 : Blo 1352995 2030843 := bstep (se 1 (by rfl) ⟨1523132, by rfl⟩ : syracuseStep 2030843 = 3046265) B3046265
theorem B2030969 : Blo 1352995 2030969 := bstep (se 2 (by rfl) ⟨761613, by rfl⟩ : syracuseStep 2030969 = 1523227) B1523227
theorem B2031131 : Blo 1352995 2031131 := bstep (se 1 (by rfl) ⟨1523348, by rfl⟩ : syracuseStep 2031131 = 3046697) B3046697
theorem B5144219 : Blo 1352995 5144219 := bstep (se 1 (by rfl) ⟨3858164, by rfl⟩ : syracuseStep 5144219 = 7716329) B7716329
theorem B4570991 : Blo 1352995 4570991 := bstep (se 1 (by rfl) ⟨3428243, by rfl⟩ : syracuseStep 4570991 = 6856487) B6856487
theorem B2031593 : Blo 1352995 2031593 := bstep (se 2 (by rfl) ⟨761847, by rfl⟩ : syracuseStep 2031593 = 1523695) B1523695
theorem B3252271 : Blo 1352995 3252271 := bstep (se 1 (by rfl) ⟨2439203, by rfl⟩ : syracuseStep 3252271 = 4878407) B4878407
theorem B15425639 : Blo 1352995 15425639 := bstep (se 1 (by rfl) ⟨11569229, by rfl⟩ : syracuseStep 15425639 = 23138459) B23138459
theorem B11288767 : Blo 1352995 11288767 := bstep (se 1 (by rfl) ⟨8466575, by rfl⟩ : syracuseStep 11288767 = 16933151) B16933151
theorem B2744543 : Blo 1352995 2744543 := bstep (se 1 (by rfl) ⟨2058407, by rfl⟩ : syracuseStep 2744543 = 4116815) B4116815
theorem B3907919 : Blo 1352995 3907919 := bstep (se 1 (by rfl) ⟨2930939, by rfl⟩ : syracuseStep 3907919 = 5861879) B5861879
theorem B3047849 : Blo 1352995 3047849 := bstep (se 2 (by rfl) ⟨1142943, by rfl⟩ : syracuseStep 3047849 = 2285887) B2285887
theorem B3047903 : Blo 1352995 3047903 := bstep (se 1 (by rfl) ⟨2285927, by rfl⟩ : syracuseStep 3047903 = 4571855) B4571855
theorem B1524271 : Blo 1352995 1524271 := bstep (se 1 (by rfl) ⟨1143203, by rfl⟩ : syracuseStep 1524271 = 2286407) B2286407
theorem B3047993 : Blo 1352995 3047993 := bstep (se 2 (by rfl) ⟨1142997, by rfl⟩ : syracuseStep 3047993 = 2285995) B2285995
theorem B2286535 : Blo 1352995 2286535 := bstep (se 1 (by rfl) ⟨1714901, by rfl⟩ : syracuseStep 2286535 = 3429803) B3429803
theorem B19522619 : Blo 1352995 19522619 := bstep (se 1 (by rfl) ⟨14641964, by rfl⟩ : syracuseStep 19522619 = 29283929) B29283929
theorem B7324787 : Blo 1352995 7324787 := bstep (se 1 (by rfl) ⟨5493590, by rfl⟩ : syracuseStep 7324787 = 10987181) B10987181
theorem B78062777 : Blo 1352995 78062777 := bstep (se 2 (by rfl) ⟨29273541, by rfl⟩ : syracuseStep 78062777 = 58547083) B58547083
theorem B5137627 : Blo 1352995 5137627 := bstep (se 1 (by rfl) ⟨3853220, by rfl⟩ : syracuseStep 5137627 = 7706441) B7706441
theorem B6948065 : Blo 1352995 6948065 := bstep (se 2 (by rfl) ⟨2605524, by rfl⟩ : syracuseStep 6948065 = 5211049) B5211049
theorem B10282301 : Blo 1352995 10282301 := bstep (se 3 (by rfl) ⟨1927931, by rfl⟩ : syracuseStep 10282301 = 3855863) B3855863
theorem B22275485 : Blo 1352995 22275485 := bstep (se 3 (by rfl) ⟨4176653, by rfl⟩ : syracuseStep 22275485 = 8353307) B8353307
theorem B2893367 : Blo 1352995 2893367 := bstep (se 1 (by rfl) ⟨2170025, by rfl⟩ : syracuseStep 2893367 = 4340051) B4340051
theorem B1353575 : Blo 1352995 1353575 := bstep (se 1 (by rfl) ⟨1015181, by rfl⟩ : syracuseStep 1353575 = 2030363) B2030363
theorem B6178685 : Blo 1352995 6178685 := bstep (se 3 (by rfl) ⟨1158503, by rfl⟩ : syracuseStep 6178685 = 2317007) B2317007
theorem B6850493 : Blo 1352995 6850493 := bstep (se 3 (by rfl) ⟨1284467, by rfl⟩ : syracuseStep 6850493 = 2568935) B2568935
theorem B1353839 : Blo 1352995 1353839 := bstep (se 1 (by rfl) ⟨1015379, by rfl⟩ : syracuseStep 1353839 = 2030759) B2030759
theorem B1353895 : Blo 1352995 1353895 := bstep (se 1 (by rfl) ⟨1015421, by rfl⟩ : syracuseStep 1353895 = 2030843) B2030843
theorem B1353979 : Blo 1352995 1353979 := bstep (se 1 (by rfl) ⟨1015484, by rfl⟩ : syracuseStep 1353979 = 2030969) B2030969
theorem B1354087 : Blo 1352995 1354087 := bstep (se 1 (by rfl) ⟨1015565, by rfl⟩ : syracuseStep 1354087 = 2031131) B2031131
theorem B1354395 : Blo 1352995 1354395 := bstep (se 1 (by rfl) ⟨1015796, by rfl⟩ : syracuseStep 1354395 = 2031593) B2031593
theorem B1354491 : Blo 1352995 1354491 := bstep (se 1 (by rfl) ⟨1015868, by rfl⟩ : syracuseStep 1354491 = 2031737) B2031737
theorem B11570597 : Blo 1352995 11570597 := bstep (se 4 (by rfl) ⟨1084743, by rfl⟩ : syracuseStep 11570597 = 2169487) B2169487
theorem B11562533 : Blo 1352995 11562533 := bstep (se 4 (by rfl) ⟨1083987, by rfl⟩ : syracuseStep 11562533 = 2167975) B2167975
theorem B2059897 : Blo 1352995 2059897 := bstep (se 2 (by rfl) ⟨772461, by rfl⟩ : syracuseStep 2059897 = 1544923) B1544923
theorem B4566887 : Blo 1352995 4566887 := bstep (se 1 (by rfl) ⟨3425165, by rfl⟩ : syracuseStep 4566887 = 6850331) B6850331
theorem B6852599 : Blo 1352995 6852599 := bstep (se 1 (by rfl) ⟨5139449, by rfl⟩ : syracuseStep 6852599 = 10278899) B10278899
theorem B10276955 : Blo 1352995 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B10973819 : Blo 1352995 10973819 := bstep (se 1 (by rfl) ⟨8230364, by rfl⟩ : syracuseStep 10973819 = 16460729) B16460729
theorem B5141501 : Blo 1352995 5141501 := bstep (se 3 (by rfl) ⟨964031, by rfl⟩ : syracuseStep 5141501 = 1928063) B1928063
theorem B3429479 : Blo 1352995 3429479 := bstep (se 1 (by rfl) ⟨2572109, by rfl⟩ : syracuseStep 3429479 = 5144219) B5144219
theorem B7713913 : Blo 1352995 7713913 := bstep (se 2 (by rfl) ⟨2892717, by rfl⟩ : syracuseStep 7713913 = 5785435) B5785435
theorem B2569801 : Blo 1352995 2569801 := bstep (se 2 (by rfl) ⟨963675, by rfl⟩ : syracuseStep 2569801 = 1927351) B1927351
theorem B3044969 : Blo 1352995 3044969 := bstep (se 2 (by rfl) ⟨1141863, by rfl⟩ : syracuseStep 3044969 = 2283727) B2283727
theorem B55564649 : Blo 1352995 55564649 := bstep (se 2 (by rfl) ⟨20836743, by rfl⟩ : syracuseStep 55564649 = 41673487) B41673487
theorem B2030063 : Blo 1352995 2030063 := bstep (se 1 (by rfl) ⟨1522547, by rfl⟩ : syracuseStep 2030063 = 3045095) B3045095
theorem B3046247 : Blo 1352995 3046247 := bstep (se 1 (by rfl) ⟨2284685, by rfl⟩ : syracuseStep 3046247 = 4569371) B4569371
theorem B3047327 : Blo 1352995 3047327 := bstep (se 1 (by rfl) ⟨2285495, by rfl⟩ : syracuseStep 3047327 = 4570991) B4570991
theorem B3047417 : Blo 1352995 3047417 := bstep (se 2 (by rfl) ⟨1142781, by rfl⟩ : syracuseStep 3047417 = 2285563) B2285563
theorem B2605279 : Blo 1352995 2605279 := bstep (se 1 (by rfl) ⟨1953959, by rfl⟩ : syracuseStep 2605279 = 3907919) B3907919
theorem B2031899 : Blo 1352995 2031899 := bstep (se 1 (by rfl) ⟨1523924, by rfl⟩ : syracuseStep 2031899 = 3047849) B3047849
theorem B2031935 : Blo 1352995 2031935 := bstep (se 1 (by rfl) ⟨1523951, by rfl⟩ : syracuseStep 2031935 = 3047903) B3047903
theorem B2031995 : Blo 1352995 2031995 := bstep (se 1 (by rfl) ⟨1523996, by rfl⟩ : syracuseStep 2031995 = 3047993) B3047993
theorem B2032361 : Blo 1352995 2032361 := bstep (se 2 (by rfl) ⟨762135, by rfl⟩ : syracuseStep 2032361 = 1524271) B1524271
theorem B2286319 : Blo 1352995 2286319 := bstep (se 1 (by rfl) ⟨1714739, by rfl⟩ : syracuseStep 2286319 = 3429479) B3429479
theorem B3048713 : Blo 1352995 3048713 := bstep (se 2 (by rfl) ⟨1143267, by rfl⟩ : syracuseStep 3048713 = 2286535) B2286535
theorem B6850169 : Blo 1352995 6850169 := bstep (se 2 (by rfl) ⟨2568813, by rfl⟩ : syracuseStep 6850169 = 5137627) B5137627
theorem B29263517 : Blo 1352995 29263517 := bstep (se 3 (by rfl) ⟨5486909, by rfl⟩ : syracuseStep 29263517 = 10973819) B10973819
theorem B1353375 : Blo 1352995 1353375 := bstep (se 1 (by rfl) ⟨1015031, by rfl⟩ : syracuseStep 1353375 = 2030063) B2030063
theorem B3426401 : Blo 1352995 3426401 := bstep (se 2 (by rfl) ⟨1284900, by rfl⟩ : syracuseStep 3426401 = 2569801) B2569801
theorem B2746529 : Blo 1352995 2746529 := bstep (se 2 (by rfl) ⟨1029948, by rfl⟩ : syracuseStep 2746529 = 2059897) B2059897
theorem B16476493 : Blo 1352995 16476493 := bstep (se 3 (by rfl) ⟨3089342, by rfl⟩ : syracuseStep 16476493 = 6178685) B6178685
theorem B6851303 : Blo 1352995 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B4336361 : Blo 1352995 4336361 := bstep (se 2 (by rfl) ⟨1626135, by rfl⟩ : syracuseStep 4336361 = 3252271) B3252271
theorem B10283759 : Blo 1352995 10283759 := bstep (se 1 (by rfl) ⟨7712819, by rfl⟩ : syracuseStep 10283759 = 15425639) B15425639
theorem B15051689 : Blo 1352995 15051689 := bstep (se 2 (by rfl) ⟨5644383, by rfl⟩ : syracuseStep 15051689 = 11288767) B11288767
theorem B19532765 : Blo 1352995 19532765 := bstep (se 3 (by rfl) ⟨3662393, by rfl⟩ : syracuseStep 19532765 = 7324787) B7324787
theorem B7318781 : Blo 1352995 7318781 := bstep (se 3 (by rfl) ⟨1372271, by rfl⟩ : syracuseStep 7318781 = 2744543) B2744543
theorem B3427667 : Blo 1352995 3427667 := bstep (se 1 (by rfl) ⟨2570750, by rfl⟩ : syracuseStep 3427667 = 5141501) B5141501
theorem B4566995 : Blo 1352995 4566995 := bstep (se 1 (by rfl) ⟨3425246, by rfl⟩ : syracuseStep 4566995 = 6850493) B6850493
theorem B10285217 : Blo 1352995 10285217 := bstep (se 2 (by rfl) ⟨3856956, by rfl⟩ : syracuseStep 10285217 = 7713913) B7713913
theorem B7713731 : Blo 1352995 7713731 := bstep (se 1 (by rfl) ⟨5785298, by rfl⟩ : syracuseStep 7713731 = 11570597) B11570597
theorem B3044591 : Blo 1352995 3044591 := bstep (se 1 (by rfl) ⟨2283443, by rfl⟩ : syracuseStep 3044591 = 4566887) B4566887
theorem B4568399 : Blo 1352995 4568399 := bstep (se 1 (by rfl) ⟨3426299, by rfl⟩ : syracuseStep 4568399 = 6852599) B6852599
theorem B18528173 : Blo 1352995 18528173 := bstep (se 3 (by rfl) ⟨3474032, by rfl⟩ : syracuseStep 18528173 = 6948065) B6948065
theorem B13015079 : Blo 1352995 13015079 := bstep (se 1 (by rfl) ⟨9761309, by rfl⟩ : syracuseStep 13015079 = 19522619) B19522619
theorem B52041851 : Blo 1352995 52041851 := bstep (se 1 (by rfl) ⟨39031388, by rfl⟩ : syracuseStep 52041851 = 78062777) B78062777
theorem B6854867 : Blo 1352995 6854867 := bstep (se 1 (by rfl) ⟨5141150, by rfl⟩ : syracuseStep 6854867 = 10282301) B10282301
theorem B14850323 : Blo 1352995 14850323 := bstep (se 1 (by rfl) ⟨11137742, by rfl⟩ : syracuseStep 14850323 = 22275485) B22275485
theorem B2029979 : Blo 1352995 2029979 := bstep (se 1 (by rfl) ⟨1522484, by rfl⟩ : syracuseStep 2029979 = 3044969) B3044969
theorem B7715645 : Blo 1352995 7715645 := bstep (se 3 (by rfl) ⟨1446683, by rfl⟩ : syracuseStep 7715645 = 2893367) B2893367
theorem B37043099 : Blo 1352995 37043099 := bstep (se 1 (by rfl) ⟨27782324, by rfl⟩ : syracuseStep 37043099 = 55564649) B55564649
theorem B2030831 : Blo 1352995 2030831 := bstep (se 1 (by rfl) ⟨1523123, by rfl⟩ : syracuseStep 2030831 = 3046247) B3046247
theorem B7708355 : Blo 1352995 7708355 := bstep (se 1 (by rfl) ⟨5781266, by rfl⟩ : syracuseStep 7708355 = 11562533) B11562533
theorem B2031551 : Blo 1352995 2031551 := bstep (se 1 (by rfl) ⟨1523663, by rfl⟩ : syracuseStep 2031551 = 3047327) B3047327
theorem B2031611 : Blo 1352995 2031611 := bstep (se 1 (by rfl) ⟨1523708, by rfl⟩ : syracuseStep 2031611 = 3047417) B3047417
theorem B6856811 : Blo 1352995 6856811 := bstep (se 1 (by rfl) ⟨5142608, by rfl⟩ : syracuseStep 6856811 = 10285217) B10285217
theorem B3473705 : Blo 1352995 3473705 := bstep (se 2 (by rfl) ⟨1302639, by rfl⟩ : syracuseStep 3473705 = 2605279) B2605279
theorem B2032475 : Blo 1352995 2032475 := bstep (se 1 (by rfl) ⟨1524356, by rfl⟩ : syracuseStep 2032475 = 3048713) B3048713
theorem B3048425 : Blo 1352995 3048425 := bstep (se 2 (by rfl) ⟨1143159, by rfl⟩ : syracuseStep 3048425 = 2286319) B2286319
theorem B8676719 : Blo 1352995 8676719 := bstep (se 1 (by rfl) ⟨6507539, by rfl⟩ : syracuseStep 8676719 = 13015079) B13015079
theorem B34694567 : Blo 1352995 34694567 := bstep (se 1 (by rfl) ⟨26020925, by rfl⟩ : syracuseStep 34694567 = 52041851) B52041851
theorem B1353319 : Blo 1352995 1353319 := bstep (se 1 (by rfl) ⟨1014989, by rfl⟩ : syracuseStep 1353319 = 2029979) B2029979
theorem B1353887 : Blo 1352995 1353887 := bstep (se 1 (by rfl) ⟨1015415, by rfl⟩ : syracuseStep 1353887 = 2030831) B2030831
theorem B5138903 : Blo 1352995 5138903 := bstep (se 1 (by rfl) ⟨3854177, by rfl⟩ : syracuseStep 5138903 = 7708355) B7708355
theorem B1354367 : Blo 1352995 1354367 := bstep (se 1 (by rfl) ⟨1015775, by rfl⟩ : syracuseStep 1354367 = 2031551) B2031551
theorem B1354407 : Blo 1352995 1354407 := bstep (se 1 (by rfl) ⟨1015805, by rfl⟩ : syracuseStep 1354407 = 2031611) B2031611
theorem B1354599 : Blo 1352995 1354599 := bstep (se 1 (by rfl) ⟨1015949, by rfl⟩ : syracuseStep 1354599 = 2031899) B2031899
theorem B1354623 : Blo 1352995 1354623 := bstep (se 1 (by rfl) ⟨1015967, by rfl⟩ : syracuseStep 1354623 = 2031935) B2031935
theorem B1354663 : Blo 1352995 1354663 := bstep (se 1 (by rfl) ⟨1015997, by rfl⟩ : syracuseStep 1354663 = 2031995) B2031995
theorem B1354907 : Blo 1352995 1354907 := bstep (se 1 (by rfl) ⟨1016180, by rfl⟩ : syracuseStep 1354907 = 2032361) B2032361
theorem B4566779 : Blo 1352995 4566779 := bstep (se 1 (by rfl) ⟨3425084, by rfl⟩ : syracuseStep 4566779 = 6850169) B6850169
theorem B19509011 : Blo 1352995 19509011 := bstep (se 1 (by rfl) ⟨14631758, by rfl⟩ : syracuseStep 19509011 = 29263517) B29263517
theorem B1831019 : Blo 1352995 1831019 := bstep (se 1 (by rfl) ⟨1373264, by rfl⟩ : syracuseStep 1831019 = 2746529) B2746529
theorem B9900215 : Blo 1352995 9900215 := bstep (se 1 (by rfl) ⟨7425161, by rfl⟩ : syracuseStep 9900215 = 14850323) B14850323
theorem B4567535 : Blo 1352995 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B24695399 : Blo 1352995 24695399 := bstep (se 1 (by rfl) ⟨18521549, by rfl⟩ : syracuseStep 24695399 = 37043099) B37043099
theorem B13021843 : Blo 1352995 13021843 := bstep (se 1 (by rfl) ⟨9766382, by rfl⟩ : syracuseStep 13021843 = 19532765) B19532765
theorem B4879187 : Blo 1352995 4879187 := bstep (se 1 (by rfl) ⟨3659390, by rfl⟩ : syracuseStep 4879187 = 7318781) B7318781
theorem B3044663 : Blo 1352995 3044663 := bstep (se 1 (by rfl) ⟨2283497, by rfl⟩ : syracuseStep 3044663 = 4566995) B4566995
theorem B21968657 : Blo 1352995 21968657 := bstep (se 2 (by rfl) ⟨8238246, by rfl⟩ : syracuseStep 21968657 = 16476493) B16476493
theorem B5142487 : Blo 1352995 5142487 := bstep (se 1 (by rfl) ⟨3856865, by rfl⟩ : syracuseStep 5142487 = 7713731) B7713731
theorem B2029727 : Blo 1352995 2029727 := bstep (se 1 (by rfl) ⟨1522295, by rfl⟩ : syracuseStep 2029727 = 3044591) B3044591
theorem B3045599 : Blo 1352995 3045599 := bstep (se 1 (by rfl) ⟨2284199, by rfl⟩ : syracuseStep 3045599 = 4568399) B4568399
theorem B12352115 : Blo 1352995 12352115 := bstep (se 1 (by rfl) ⟨9264086, by rfl⟩ : syracuseStep 12352115 = 18528173) B18528173
theorem B2284267 : Blo 1352995 2284267 := bstep (se 1 (by rfl) ⟨1713200, by rfl⟩ : syracuseStep 2284267 = 3426401) B3426401
theorem B4569911 : Blo 1352995 4569911 := bstep (se 1 (by rfl) ⟨3427433, by rfl⟩ : syracuseStep 4569911 = 6854867) B6854867
theorem B2890907 : Blo 1352995 2890907 := bstep (se 1 (by rfl) ⟨2168180, by rfl⟩ : syracuseStep 2890907 = 4336361) B4336361
theorem B6855839 : Blo 1352995 6855839 := bstep (se 1 (by rfl) ⟨5141879, by rfl⟩ : syracuseStep 6855839 = 10283759) B10283759
theorem B5143763 : Blo 1352995 5143763 := bstep (se 1 (by rfl) ⟨3857822, by rfl⟩ : syracuseStep 5143763 = 7715645) B7715645
theorem B10034459 : Blo 1352995 10034459 := bstep (se 1 (by rfl) ⟨7525844, by rfl⟩ : syracuseStep 10034459 = 15051689) B15051689
theorem B2285111 : Blo 1352995 2285111 := bstep (se 1 (by rfl) ⟨1713833, by rfl⟩ : syracuseStep 2285111 = 3427667) B3427667
theorem B4571207 : Blo 1352995 4571207 := bstep (se 1 (by rfl) ⟨3428405, by rfl⟩ : syracuseStep 4571207 = 6856811) B6856811
theorem B4882717 : Blo 1352995 4882717 := bstep (se 3 (by rfl) ⟨915509, by rfl⟩ : syracuseStep 4882717 = 1831019) B1831019
theorem B3252791 : Blo 1352995 3252791 := bstep (se 1 (by rfl) ⟨2439593, by rfl⟩ : syracuseStep 3252791 = 4879187) B4879187
theorem B2032283 : Blo 1352995 2032283 := bstep (se 1 (by rfl) ⟨1524212, by rfl⟩ : syracuseStep 2032283 = 3048425) B3048425
theorem B5784479 : Blo 1352995 5784479 := bstep (se 1 (by rfl) ⟨4338359, by rfl⟩ : syracuseStep 5784479 = 8676719) B8676719
theorem B1353151 : Blo 1352995 1353151 := bstep (se 1 (by rfl) ⟨1014863, by rfl⟩ : syracuseStep 1353151 = 2029727) B2029727
theorem B3425935 : Blo 1352995 3425935 := bstep (se 1 (by rfl) ⟨2569451, by rfl⟩ : syracuseStep 3425935 = 5138903) B5138903
theorem B8234743 : Blo 1352995 8234743 := bstep (se 1 (by rfl) ⟨6176057, by rfl⟩ : syracuseStep 8234743 = 12352115) B12352115
theorem B1927271 : Blo 1352995 1927271 := bstep (se 1 (by rfl) ⟨1445453, by rfl⟩ : syracuseStep 1927271 = 2890907) B2890907
theorem B1354983 : Blo 1352995 1354983 := bstep (se 1 (by rfl) ⟨1016237, by rfl⟩ : syracuseStep 1354983 = 2032475) B2032475
theorem B17362457 : Blo 1352995 17362457 := bstep (se 2 (by rfl) ⟨6510921, by rfl⟩ : syracuseStep 17362457 = 13021843) B13021843
theorem B23129711 : Blo 1352995 23129711 := bstep (se 1 (by rfl) ⟨17347283, by rfl⟩ : syracuseStep 23129711 = 34694567) B34694567
theorem B3429175 : Blo 1352995 3429175 := bstep (se 1 (by rfl) ⟨2571881, by rfl⟩ : syracuseStep 3429175 = 5143763) B5143763
theorem B6689639 : Blo 1352995 6689639 := bstep (se 1 (by rfl) ⟨5017229, by rfl⟩ : syracuseStep 6689639 = 10034459) B10034459
theorem B3044519 : Blo 1352995 3044519 := bstep (se 1 (by rfl) ⟨2283389, by rfl⟩ : syracuseStep 3044519 = 4566779) B4566779
theorem B13006007 : Blo 1352995 13006007 := bstep (se 1 (by rfl) ⟨9754505, by rfl⟩ : syracuseStep 13006007 = 19509011) B19509011
theorem B6600143 : Blo 1352995 6600143 := bstep (se 1 (by rfl) ⟨4950107, by rfl⟩ : syracuseStep 6600143 = 9900215) B9900215
theorem B2315803 : Blo 1352995 2315803 := bstep (se 1 (by rfl) ⟨1736852, by rfl⟩ : syracuseStep 2315803 = 3473705) B3473705
theorem B3045023 : Blo 1352995 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B2029775 : Blo 1352995 2029775 := bstep (se 1 (by rfl) ⟨1522331, by rfl⟩ : syracuseStep 2029775 = 3044663) B3044663
theorem B3045689 : Blo 1352995 3045689 := bstep (se 2 (by rfl) ⟨1142133, by rfl⟩ : syracuseStep 3045689 = 2284267) B2284267
theorem B14645771 : Blo 1352995 14645771 := bstep (se 1 (by rfl) ⟨10984328, by rfl⟩ : syracuseStep 14645771 = 21968657) B21968657
theorem B2030399 : Blo 1352995 2030399 := bstep (se 1 (by rfl) ⟨1522799, by rfl⟩ : syracuseStep 2030399 = 3045599) B3045599
theorem B65854397 : Blo 1352995 65854397 := bstep (se 3 (by rfl) ⟨12347699, by rfl⟩ : syracuseStep 65854397 = 24695399) B24695399
theorem B3046607 : Blo 1352995 3046607 := bstep (se 1 (by rfl) ⟨2284955, by rfl⟩ : syracuseStep 3046607 = 4569911) B4569911
theorem B4570559 : Blo 1352995 4570559 := bstep (se 1 (by rfl) ⟨3427919, by rfl⟩ : syracuseStep 4570559 = 6855839) B6855839
theorem B1523407 : Blo 1352995 1523407 := bstep (se 1 (by rfl) ⟨1142555, by rfl⟩ : syracuseStep 1523407 = 2285111) B2285111
theorem B6856649 : Blo 1352995 6856649 := bstep (se 2 (by rfl) ⟨2571243, by rfl⟩ : syracuseStep 6856649 = 5142487) B5142487
theorem B3047471 : Blo 1352995 3047471 := bstep (se 1 (by rfl) ⟨2285603, by rfl⟩ : syracuseStep 3047471 = 4571207) B4571207
theorem B4572233 : Blo 1352995 4572233 := bstep (se 2 (by rfl) ⟨1714587, by rfl⟩ : syracuseStep 4572233 = 3429175) B3429175
theorem B1353183 : Blo 1352995 1353183 := bstep (se 1 (by rfl) ⟨1014887, by rfl⟩ : syracuseStep 1353183 = 2029775) B2029775
theorem B1353599 : Blo 1352995 1353599 := bstep (se 1 (by rfl) ⟨1015199, by rfl⟩ : syracuseStep 1353599 = 2030399) B2030399
theorem B43902931 : Blo 1352995 43902931 := bstep (se 1 (by rfl) ⟨32927198, by rfl⟩ : syracuseStep 43902931 = 65854397) B65854397
theorem B10979657 : Blo 1352995 10979657 := bstep (se 2 (by rfl) ⟨4117371, by rfl⟩ : syracuseStep 10979657 = 8234743) B8234743
theorem B15419807 : Blo 1352995 15419807 := bstep (se 1 (by rfl) ⟨11564855, by rfl⟩ : syracuseStep 15419807 = 23129711) B23129711
theorem B5139389 : Blo 1352995 5139389 := bstep (se 3 (by rfl) ⟨963635, by rfl⟩ : syracuseStep 5139389 = 1927271) B1927271
theorem B1354855 : Blo 1352995 1354855 := bstep (se 1 (by rfl) ⟨1016141, by rfl⟩ : syracuseStep 1354855 = 2032283) B2032283
theorem B8670671 : Blo 1352995 8670671 := bstep (se 1 (by rfl) ⟨6503003, by rfl⟩ : syracuseStep 8670671 = 13006007) B13006007
theorem B17600381 : Blo 1352995 17600381 := bstep (se 3 (by rfl) ⟨3300071, by rfl⟩ : syracuseStep 17600381 = 6600143) B6600143
theorem B4567913 : Blo 1352995 4567913 := bstep (se 2 (by rfl) ⟨1712967, by rfl⟩ : syracuseStep 4567913 = 3425935) B3425935
theorem B17839037 : Blo 1352995 17839037 := bstep (se 3 (by rfl) ⟨3344819, by rfl⟩ : syracuseStep 17839037 = 6689639) B6689639
theorem B2168527 : Blo 1352995 2168527 := bstep (se 1 (by rfl) ⟨1626395, by rfl⟩ : syracuseStep 2168527 = 3252791) B3252791
theorem B6510289 : Blo 1352995 6510289 := bstep (se 2 (by rfl) ⟨2441358, by rfl⟩ : syracuseStep 6510289 = 4882717) B4882717
theorem B3856319 : Blo 1352995 3856319 := bstep (se 1 (by rfl) ⟨2892239, by rfl⟩ : syracuseStep 3856319 = 5784479) B5784479
theorem B2029679 : Blo 1352995 2029679 := bstep (se 1 (by rfl) ⟨1522259, by rfl⟩ : syracuseStep 2029679 = 3044519) B3044519
theorem B2030015 : Blo 1352995 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B2030459 : Blo 1352995 2030459 := bstep (se 1 (by rfl) ⟨1522844, by rfl⟩ : syracuseStep 2030459 = 3045689) B3045689
theorem B9763847 : Blo 1352995 9763847 := bstep (se 1 (by rfl) ⟨7322885, by rfl⟩ : syracuseStep 9763847 = 14645771) B14645771
theorem B3087737 : Blo 1352995 3087737 := bstep (se 2 (by rfl) ⟨1157901, by rfl⟩ : syracuseStep 3087737 = 2315803) B2315803
theorem B2031071 : Blo 1352995 2031071 := bstep (se 1 (by rfl) ⟨1523303, by rfl⟩ : syracuseStep 2031071 = 3046607) B3046607
theorem B2031209 : Blo 1352995 2031209 := bstep (se 2 (by rfl) ⟨761703, by rfl⟩ : syracuseStep 2031209 = 1523407) B1523407
theorem B3047039 : Blo 1352995 3047039 := bstep (se 1 (by rfl) ⟨2285279, by rfl⟩ : syracuseStep 3047039 = 4570559) B4570559
theorem B11574971 : Blo 1352995 11574971 := bstep (se 1 (by rfl) ⟨8681228, by rfl⟩ : syracuseStep 11574971 = 17362457) B17362457
theorem B4571099 : Blo 1352995 4571099 := bstep (se 1 (by rfl) ⟨3428324, by rfl⟩ : syracuseStep 4571099 = 6856649) B6856649
theorem B2031647 : Blo 1352995 2031647 := bstep (se 1 (by rfl) ⟨1523735, by rfl⟩ : syracuseStep 2031647 = 3047471) B3047471
theorem B3048155 : Blo 1352995 3048155 := bstep (se 1 (by rfl) ⟨2286116, by rfl⟩ : syracuseStep 3048155 = 4572233) B4572233
theorem B1353119 : Blo 1352995 1353119 := bstep (se 1 (by rfl) ⟨1014839, by rfl⟩ : syracuseStep 1353119 = 2029679) B2029679
theorem B1353343 : Blo 1352995 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B1353639 : Blo 1352995 1353639 := bstep (se 1 (by rfl) ⟨1015229, by rfl⟩ : syracuseStep 1353639 = 2030459) B2030459
theorem B3426259 : Blo 1352995 3426259 := bstep (se 1 (by rfl) ⟨2569694, by rfl⟩ : syracuseStep 3426259 = 5139389) B5139389
theorem B2058491 : Blo 1352995 2058491 := bstep (se 1 (by rfl) ⟨1543868, by rfl⟩ : syracuseStep 2058491 = 3087737) B3087737
theorem B1354047 : Blo 1352995 1354047 := bstep (se 1 (by rfl) ⟨1015535, by rfl⟩ : syracuseStep 1354047 = 2031071) B2031071
theorem B1354139 : Blo 1352995 1354139 := bstep (se 1 (by rfl) ⟨1015604, by rfl⟩ : syracuseStep 1354139 = 2031209) B2031209
theorem B11733587 : Blo 1352995 11733587 := bstep (se 1 (by rfl) ⟨8800190, by rfl⟩ : syracuseStep 11733587 = 17600381) B17600381
theorem B7319771 : Blo 1352995 7319771 := bstep (se 1 (by rfl) ⟨5489828, by rfl⟩ : syracuseStep 7319771 = 10979657) B10979657
theorem B6509231 : Blo 1352995 6509231 := bstep (se 1 (by rfl) ⟨4881923, by rfl⟩ : syracuseStep 6509231 = 9763847) B9763847
theorem B8680385 : Blo 1352995 8680385 := bstep (se 2 (by rfl) ⟨3255144, by rfl⟩ : syracuseStep 8680385 = 6510289) B6510289
theorem B5780447 : Blo 1352995 5780447 := bstep (se 1 (by rfl) ⟨4335335, by rfl⟩ : syracuseStep 5780447 = 8670671) B8670671
theorem B58537241 : Blo 1352995 58537241 := bstep (se 2 (by rfl) ⟨21951465, by rfl⟩ : syracuseStep 58537241 = 43902931) B43902931
theorem B3045275 : Blo 1352995 3045275 := bstep (se 1 (by rfl) ⟨2283956, by rfl⟩ : syracuseStep 3045275 = 4567913) B4567913
theorem B11892691 : Blo 1352995 11892691 := bstep (se 1 (by rfl) ⟨8919518, by rfl⟩ : syracuseStep 11892691 = 17839037) B17839037
theorem B2570879 : Blo 1352995 2570879 := bstep (se 1 (by rfl) ⟨1928159, by rfl⟩ : syracuseStep 2570879 = 3856319) B3856319
theorem B10279871 : Blo 1352995 10279871 := bstep (se 1 (by rfl) ⟨7709903, by rfl⟩ : syracuseStep 10279871 = 15419807) B15419807
theorem B2891369 : Blo 1352995 2891369 := bstep (se 2 (by rfl) ⟨1084263, by rfl⟩ : syracuseStep 2891369 = 2168527) B2168527
theorem B2031359 : Blo 1352995 2031359 := bstep (se 1 (by rfl) ⟨1523519, by rfl⟩ : syracuseStep 2031359 = 3047039) B3047039
theorem B7716647 : Blo 1352995 7716647 := bstep (se 1 (by rfl) ⟨5787485, by rfl⟩ : syracuseStep 7716647 = 11574971) B11574971
theorem B3047399 : Blo 1352995 3047399 := bstep (se 1 (by rfl) ⟨2285549, by rfl⟩ : syracuseStep 3047399 = 4571099) B4571099
theorem B2032103 : Blo 1352995 2032103 := bstep (se 1 (by rfl) ⟨1524077, by rfl⟩ : syracuseStep 2032103 = 3048155) B3048155
theorem B5489309 : Blo 1352995 5489309 := bstep (se 3 (by rfl) ⟨1029245, by rfl⟩ : syracuseStep 5489309 = 2058491) B2058491
theorem B1927579 : Blo 1352995 1927579 := bstep (se 1 (by rfl) ⟨1445684, by rfl⟩ : syracuseStep 1927579 = 2891369) B2891369
theorem B1354239 : Blo 1352995 1354239 := bstep (se 1 (by rfl) ⟨1015679, by rfl⟩ : syracuseStep 1354239 = 2031359) B2031359
theorem B1354431 : Blo 1352995 1354431 := bstep (se 1 (by rfl) ⟨1015823, by rfl⟩ : syracuseStep 1354431 = 2031647) B2031647
theorem B5786923 : Blo 1352995 5786923 := bstep (se 1 (by rfl) ⟨4340192, by rfl⟩ : syracuseStep 5786923 = 8680385) B8680385
theorem B3853631 : Blo 1352995 3853631 := bstep (se 1 (by rfl) ⟨2890223, by rfl⟩ : syracuseStep 3853631 = 5780447) B5780447
theorem B6853247 : Blo 1352995 6853247 := bstep (se 1 (by rfl) ⟨5139935, by rfl⟩ : syracuseStep 6853247 = 10279871) B10279871
theorem B4568345 : Blo 1352995 4568345 := bstep (se 2 (by rfl) ⟨1713129, by rfl⟩ : syracuseStep 4568345 = 3426259) B3426259
theorem B15856921 : Blo 1352995 15856921 := bstep (se 2 (by rfl) ⟨5946345, by rfl⟩ : syracuseStep 15856921 = 11892691) B11892691
theorem B4879847 : Blo 1352995 4879847 := bstep (se 1 (by rfl) ⟨3659885, by rfl⟩ : syracuseStep 4879847 = 7319771) B7319771
theorem B4339487 : Blo 1352995 4339487 := bstep (se 1 (by rfl) ⟨3254615, by rfl⟩ : syracuseStep 4339487 = 6509231) B6509231
theorem B39024827 : Blo 1352995 39024827 := bstep (se 1 (by rfl) ⟨29268620, by rfl⟩ : syracuseStep 39024827 = 58537241) B58537241
theorem B2030183 : Blo 1352995 2030183 := bstep (se 1 (by rfl) ⟨1522637, by rfl⟩ : syracuseStep 2030183 = 3045275) B3045275
theorem B6855677 : Blo 1352995 6855677 := bstep (se 3 (by rfl) ⟨1285439, by rfl⟩ : syracuseStep 6855677 = 2570879) B2570879
theorem B7822391 : Blo 1352995 7822391 := bstep (se 1 (by rfl) ⟨5866793, by rfl⟩ : syracuseStep 7822391 = 11733587) B11733587
theorem B5144431 : Blo 1352995 5144431 := bstep (se 1 (by rfl) ⟨3858323, by rfl⟩ : syracuseStep 5144431 = 7716647) B7716647
theorem B2031599 : Blo 1352995 2031599 := bstep (se 1 (by rfl) ⟨1523699, by rfl⟩ : syracuseStep 2031599 = 3047399) B3047399
theorem B3253231 : Blo 1352995 3253231 := bstep (se 1 (by rfl) ⟨2439923, by rfl⟩ : syracuseStep 3253231 = 4879847) B4879847
theorem B2892991 : Blo 1352995 2892991 := bstep (se 1 (by rfl) ⟨2169743, by rfl⟩ : syracuseStep 2892991 = 4339487) B4339487
theorem B1353455 : Blo 1352995 1353455 := bstep (se 1 (by rfl) ⟨1015091, by rfl⟩ : syracuseStep 1353455 = 2030183) B2030183
theorem B6859241 : Blo 1352995 6859241 := bstep (se 2 (by rfl) ⟨2572215, by rfl⟩ : syracuseStep 6859241 = 5144431) B5144431
theorem B1354399 : Blo 1352995 1354399 := bstep (se 1 (by rfl) ⟨1015799, by rfl⟩ : syracuseStep 1354399 = 2031599) B2031599
theorem B20859709 : Blo 1352995 20859709 := bstep (se 3 (by rfl) ⟨3911195, by rfl⟩ : syracuseStep 20859709 = 7822391) B7822391
theorem B1354735 : Blo 1352995 1354735 := bstep (se 1 (by rfl) ⟨1016051, by rfl⟩ : syracuseStep 1354735 = 2032103) B2032103
theorem B2569087 : Blo 1352995 2569087 := bstep (se 1 (by rfl) ⟨1926815, by rfl⟩ : syracuseStep 2569087 = 3853631) B3853631
theorem B4568831 : Blo 1352995 4568831 := bstep (se 1 (by rfl) ⟨3426623, by rfl⟩ : syracuseStep 4568831 = 6853247) B6853247
theorem B2570105 : Blo 1352995 2570105 := bstep (se 2 (by rfl) ⟨963789, by rfl⟩ : syracuseStep 2570105 = 1927579) B1927579
theorem B3045563 : Blo 1352995 3045563 := bstep (se 1 (by rfl) ⟨2284172, by rfl⟩ : syracuseStep 3045563 = 4568345) B4568345
theorem B26016551 : Blo 1352995 26016551 := bstep (se 1 (by rfl) ⟨19512413, by rfl⟩ : syracuseStep 26016551 = 39024827) B39024827
theorem B21142561 : Blo 1352995 21142561 := bstep (se 2 (by rfl) ⟨7928460, by rfl⟩ : syracuseStep 21142561 = 15856921) B15856921
theorem B7715897 : Blo 1352995 7715897 := bstep (se 2 (by rfl) ⟨2893461, by rfl⟩ : syracuseStep 7715897 = 5786923) B5786923
theorem B14638157 : Blo 1352995 14638157 := bstep (se 3 (by rfl) ⟨2744654, by rfl⟩ : syracuseStep 14638157 = 5489309) B5489309
theorem B4570451 : Blo 1352995 4570451 := bstep (se 1 (by rfl) ⟨3427838, by rfl⟩ : syracuseStep 4570451 = 6855677) B6855677
theorem B27812945 : Blo 1352995 27812945 := bstep (se 2 (by rfl) ⟨10429854, by rfl⟩ : syracuseStep 27812945 = 20859709) B20859709
theorem B3425449 : Blo 1352995 3425449 := bstep (se 2 (by rfl) ⟨1284543, by rfl⟩ : syracuseStep 3425449 = 2569087) B2569087
theorem B1713403 : Blo 1352995 1713403 := bstep (se 1 (by rfl) ⟨1285052, by rfl⟩ : syracuseStep 1713403 = 2570105) B2570105
theorem B28190081 : Blo 1352995 28190081 := bstep (se 2 (by rfl) ⟨10571280, by rfl⟩ : syracuseStep 28190081 = 21142561) B21142561
theorem B4572827 : Blo 1352995 4572827 := bstep (se 1 (by rfl) ⟨3429620, by rfl⟩ : syracuseStep 4572827 = 6859241) B6859241
theorem B17344367 : Blo 1352995 17344367 := bstep (se 1 (by rfl) ⟨13008275, by rfl⟩ : syracuseStep 17344367 = 26016551) B26016551
theorem B9758771 : Blo 1352995 9758771 := bstep (se 1 (by rfl) ⟨7319078, by rfl⟩ : syracuseStep 9758771 = 14638157) B14638157
theorem B4337641 : Blo 1352995 4337641 := bstep (se 2 (by rfl) ⟨1626615, by rfl⟩ : syracuseStep 4337641 = 3253231) B3253231
theorem B3045887 : Blo 1352995 3045887 := bstep (se 1 (by rfl) ⟨2284415, by rfl⟩ : syracuseStep 3045887 = 4568831) B4568831
theorem B2030375 : Blo 1352995 2030375 := bstep (se 1 (by rfl) ⟨1522781, by rfl⟩ : syracuseStep 2030375 = 3045563) B3045563
theorem B3857321 : Blo 1352995 3857321 := bstep (se 2 (by rfl) ⟨1446495, by rfl⟩ : syracuseStep 3857321 = 2892991) B2892991
theorem B5143931 : Blo 1352995 5143931 := bstep (se 1 (by rfl) ⟨3857948, by rfl⟩ : syracuseStep 5143931 = 7715897) B7715897
theorem B3046967 : Blo 1352995 3046967 := bstep (se 1 (by rfl) ⟨2285225, by rfl⟩ : syracuseStep 3046967 = 4570451) B4570451
theorem B18793387 : Blo 1352995 18793387 := bstep (se 1 (by rfl) ⟨14095040, by rfl⟩ : syracuseStep 18793387 = 28190081) B28190081
theorem B3048551 : Blo 1352995 3048551 := bstep (se 1 (by rfl) ⟨2286413, by rfl⟩ : syracuseStep 3048551 = 4572827) B4572827
theorem B6505847 : Blo 1352995 6505847 := bstep (se 1 (by rfl) ⟨4879385, by rfl⟩ : syracuseStep 6505847 = 9758771) B9758771
theorem B1353583 : Blo 1352995 1353583 := bstep (se 1 (by rfl) ⟨1015187, by rfl⟩ : syracuseStep 1353583 = 2030375) B2030375
theorem B18541963 : Blo 1352995 18541963 := bstep (se 1 (by rfl) ⟨13906472, by rfl⟩ : syracuseStep 18541963 = 27812945) B27812945
theorem B11562911 : Blo 1352995 11562911 := bstep (se 1 (by rfl) ⟨8672183, by rfl⟩ : syracuseStep 11562911 = 17344367) B17344367
theorem B4567265 : Blo 1352995 4567265 := bstep (se 2 (by rfl) ⟨1712724, by rfl⟩ : syracuseStep 4567265 = 3425449) B3425449
theorem B3429287 : Blo 1352995 3429287 := bstep (se 1 (by rfl) ⟨2571965, by rfl⟩ : syracuseStep 3429287 = 5143931) B5143931
theorem B10286189 : Blo 1352995 10286189 := bstep (se 3 (by rfl) ⟨1928660, by rfl⟩ : syracuseStep 10286189 = 3857321) B3857321
theorem B2284537 : Blo 1352995 2284537 := bstep (se 2 (by rfl) ⟨856701, by rfl⟩ : syracuseStep 2284537 = 1713403) B1713403
theorem B2030591 : Blo 1352995 2030591 := bstep (se 1 (by rfl) ⟨1522943, by rfl⟩ : syracuseStep 2030591 = 3045887) B3045887
theorem B2031311 : Blo 1352995 2031311 := bstep (se 1 (by rfl) ⟨1523483, by rfl⟩ : syracuseStep 2031311 = 3046967) B3046967
theorem B23134085 : Blo 1352995 23134085 := bstep (se 4 (by rfl) ⟨2168820, by rfl⟩ : syracuseStep 23134085 = 4337641) B4337641
theorem B2286191 : Blo 1352995 2286191 := bstep (se 1 (by rfl) ⟨1714643, by rfl⟩ : syracuseStep 2286191 = 3429287) B3429287
theorem B2032367 : Blo 1352995 2032367 := bstep (se 1 (by rfl) ⟨1524275, by rfl⟩ : syracuseStep 2032367 = 3048551) B3048551
theorem B6857459 : Blo 1352995 6857459 := bstep (se 1 (by rfl) ⟨5143094, by rfl⟩ : syracuseStep 6857459 = 10286189) B10286189
theorem B1353727 : Blo 1352995 1353727 := bstep (se 1 (by rfl) ⟨1015295, by rfl⟩ : syracuseStep 1353727 = 2030591) B2030591
theorem B1354207 : Blo 1352995 1354207 := bstep (se 1 (by rfl) ⟨1015655, by rfl⟩ : syracuseStep 1354207 = 2031311) B2031311
theorem B4337231 : Blo 1352995 4337231 := bstep (se 1 (by rfl) ⟨3252923, by rfl⟩ : syracuseStep 4337231 = 6505847) B6505847
theorem B98890469 : Blo 1352995 98890469 := bstep (se 4 (by rfl) ⟨9270981, by rfl⟩ : syracuseStep 98890469 = 18541963) B18541963
theorem B15422723 : Blo 1352995 15422723 := bstep (se 1 (by rfl) ⟨11567042, by rfl⟩ : syracuseStep 15422723 = 23134085) B23134085
theorem B3044843 : Blo 1352995 3044843 := bstep (se 1 (by rfl) ⟨2283632, by rfl⟩ : syracuseStep 3044843 = 4567265) B4567265
theorem B25057849 : Blo 1352995 25057849 := bstep (se 2 (by rfl) ⟨9396693, by rfl⟩ : syracuseStep 25057849 = 18793387) B18793387
theorem B3046049 : Blo 1352995 3046049 := bstep (se 2 (by rfl) ⟨1142268, by rfl⟩ : syracuseStep 3046049 = 2284537) B2284537
theorem B7708607 : Blo 1352995 7708607 := bstep (se 1 (by rfl) ⟨5781455, by rfl⟩ : syracuseStep 7708607 = 11562911) B11562911
theorem B1524127 : Blo 1352995 1524127 := bstep (se 1 (by rfl) ⟨1143095, by rfl⟩ : syracuseStep 1524127 = 2286191) B2286191
theorem B4571639 : Blo 1352995 4571639 := bstep (se 1 (by rfl) ⟨3428729, by rfl⟩ : syracuseStep 4571639 = 6857459) B6857459
theorem B10281815 : Blo 1352995 10281815 := bstep (se 1 (by rfl) ⟨7711361, by rfl⟩ : syracuseStep 10281815 = 15422723) B15422723
theorem B5139071 : Blo 1352995 5139071 := bstep (se 1 (by rfl) ⟨3854303, by rfl⟩ : syracuseStep 5139071 = 7708607) B7708607
theorem B1354911 : Blo 1352995 1354911 := bstep (se 1 (by rfl) ⟨1016183, by rfl⟩ : syracuseStep 1354911 = 2032367) B2032367
theorem B33410465 : Blo 1352995 33410465 := bstep (se 2 (by rfl) ⟨12528924, by rfl⟩ : syracuseStep 33410465 = 25057849) B25057849
theorem B65926979 : Blo 1352995 65926979 := bstep (se 1 (by rfl) ⟨49445234, by rfl⟩ : syracuseStep 65926979 = 98890469) B98890469
theorem B2029895 : Blo 1352995 2029895 := bstep (se 1 (by rfl) ⟨1522421, by rfl⟩ : syracuseStep 2029895 = 3044843) B3044843
theorem B11565949 : Blo 1352995 11565949 := bstep (se 3 (by rfl) ⟨2168615, by rfl⟩ : syracuseStep 11565949 = 4337231) B4337231
theorem B2030699 : Blo 1352995 2030699 := bstep (se 1 (by rfl) ⟨1523024, by rfl⟩ : syracuseStep 2030699 = 3046049) B3046049
theorem B3047759 : Blo 1352995 3047759 := bstep (se 1 (by rfl) ⟨2285819, by rfl⟩ : syracuseStep 3047759 = 4571639) B4571639
theorem B2032169 : Blo 1352995 2032169 := bstep (se 2 (by rfl) ⟨762063, by rfl⟩ : syracuseStep 2032169 = 1524127) B1524127
theorem B43951319 : Blo 1352995 43951319 := bstep (se 1 (by rfl) ⟨32963489, by rfl⟩ : syracuseStep 43951319 = 65926979) B65926979
theorem B1353263 : Blo 1352995 1353263 := bstep (se 1 (by rfl) ⟨1014947, by rfl⟩ : syracuseStep 1353263 = 2029895) B2029895
theorem B3426047 : Blo 1352995 3426047 := bstep (se 1 (by rfl) ⟨2569535, by rfl⟩ : syracuseStep 3426047 = 5139071) B5139071
theorem B1353799 : Blo 1352995 1353799 := bstep (se 1 (by rfl) ⟨1015349, by rfl⟩ : syracuseStep 1353799 = 2030699) B2030699
theorem B15421265 : Blo 1352995 15421265 := bstep (se 2 (by rfl) ⟨5782974, by rfl⟩ : syracuseStep 15421265 = 11565949) B11565949
theorem B6854543 : Blo 1352995 6854543 := bstep (se 1 (by rfl) ⟨5140907, by rfl⟩ : syracuseStep 6854543 = 10281815) B10281815
theorem B22273643 : Blo 1352995 22273643 := bstep (se 1 (by rfl) ⟨16705232, by rfl⟩ : syracuseStep 22273643 = 33410465) B33410465
theorem B2031839 : Blo 1352995 2031839 := bstep (se 1 (by rfl) ⟨1523879, by rfl⟩ : syracuseStep 2031839 = 3047759) B3047759
theorem B1354779 : Blo 1352995 1354779 := bstep (se 1 (by rfl) ⟨1016084, by rfl⟩ : syracuseStep 1354779 = 2032169) B2032169
theorem B14849095 : Blo 1352995 14849095 := bstep (se 1 (by rfl) ⟨11136821, by rfl⟩ : syracuseStep 14849095 = 22273643) B22273643
theorem B29300879 : Blo 1352995 29300879 := bstep (se 1 (by rfl) ⟨21975659, by rfl⟩ : syracuseStep 29300879 = 43951319) B43951319
theorem B2284031 : Blo 1352995 2284031 := bstep (se 1 (by rfl) ⟨1713023, by rfl⟩ : syracuseStep 2284031 = 3426047) B3426047
theorem B4569695 : Blo 1352995 4569695 := bstep (se 1 (by rfl) ⟨3427271, by rfl⟩ : syracuseStep 4569695 = 6854543) B6854543
theorem B10280843 : Blo 1352995 10280843 := bstep (se 1 (by rfl) ⟨7710632, by rfl⟩ : syracuseStep 10280843 = 15421265) B15421265
theorem B1354559 : Blo 1352995 1354559 := bstep (se 1 (by rfl) ⟨1015919, by rfl⟩ : syracuseStep 1354559 = 2031839) B2031839
theorem B19533919 : Blo 1352995 19533919 := bstep (se 1 (by rfl) ⟨14650439, by rfl⟩ : syracuseStep 19533919 = 29300879) B29300879
theorem B6853895 : Blo 1352995 6853895 := bstep (se 1 (by rfl) ⟨5140421, by rfl⟩ : syracuseStep 6853895 = 10280843) B10280843
theorem B19798793 : Blo 1352995 19798793 := bstep (se 2 (by rfl) ⟨7424547, by rfl⟩ : syracuseStep 19798793 = 14849095) B14849095
theorem B1522687 : Blo 1352995 1522687 := bstep (se 1 (by rfl) ⟨1142015, by rfl⟩ : syracuseStep 1522687 = 2284031) B2284031
theorem B3046463 : Blo 1352995 3046463 := bstep (se 1 (by rfl) ⟨2284847, by rfl⟩ : syracuseStep 3046463 = 4569695) B4569695
theorem B13199195 : Blo 1352995 13199195 := bstep (se 1 (by rfl) ⟨9899396, by rfl⟩ : syracuseStep 13199195 = 19798793) B19798793
theorem B26045225 : Blo 1352995 26045225 := bstep (se 2 (by rfl) ⟨9766959, by rfl⟩ : syracuseStep 26045225 = 19533919) B19533919
theorem B4569263 : Blo 1352995 4569263 := bstep (se 1 (by rfl) ⟨3426947, by rfl⟩ : syracuseStep 4569263 = 6853895) B6853895
theorem B2030249 : Blo 1352995 2030249 := bstep (se 2 (by rfl) ⟨761343, by rfl⟩ : syracuseStep 2030249 = 1522687) B1522687
theorem B2030975 : Blo 1352995 2030975 := bstep (se 1 (by rfl) ⟨1523231, by rfl⟩ : syracuseStep 2030975 = 3046463) B3046463
theorem B8799463 : Blo 1352995 8799463 := bstep (se 1 (by rfl) ⟨6599597, by rfl⟩ : syracuseStep 8799463 = 13199195) B13199195
theorem B1353499 : Blo 1352995 1353499 := bstep (se 1 (by rfl) ⟨1015124, by rfl⟩ : syracuseStep 1353499 = 2030249) B2030249
theorem B1353983 : Blo 1352995 1353983 := bstep (se 1 (by rfl) ⟨1015487, by rfl⟩ : syracuseStep 1353983 = 2030975) B2030975
theorem B17363483 : Blo 1352995 17363483 := bstep (se 1 (by rfl) ⟨13022612, by rfl⟩ : syracuseStep 17363483 = 26045225) B26045225
theorem B3046175 : Blo 1352995 3046175 := bstep (se 1 (by rfl) ⟨2284631, by rfl⟩ : syracuseStep 3046175 = 4569263) B4569263
theorem B11575655 : Blo 1352995 11575655 := bstep (se 1 (by rfl) ⟨8681741, by rfl⟩ : syracuseStep 11575655 = 17363483) B17363483
theorem B11732617 : Blo 1352995 11732617 := bstep (se 2 (by rfl) ⟨4399731, by rfl⟩ : syracuseStep 11732617 = 8799463) B8799463
theorem B2030783 : Blo 1352995 2030783 := bstep (se 1 (by rfl) ⟨1523087, by rfl⟩ : syracuseStep 2030783 = 3046175) B3046175
theorem B7717103 : Blo 1352995 7717103 := bstep (se 1 (by rfl) ⟨5787827, by rfl⟩ : syracuseStep 7717103 = 11575655) B11575655
theorem B1353855 : Blo 1352995 1353855 := bstep (se 1 (by rfl) ⟨1015391, by rfl⟩ : syracuseStep 1353855 = 2030783) B2030783
theorem B15643489 : Blo 1352995 15643489 := bstep (se 2 (by rfl) ⟨5866308, by rfl⟩ : syracuseStep 15643489 = 11732617) B11732617
theorem B5144735 : Blo 1352995 5144735 := bstep (se 1 (by rfl) ⟨3858551, by rfl⟩ : syracuseStep 5144735 = 7717103) B7717103
theorem B20857985 : Blo 1352995 20857985 := bstep (se 2 (by rfl) ⟨7821744, by rfl⟩ : syracuseStep 20857985 = 15643489) B15643489
theorem B13905323 : Blo 1352995 13905323 := bstep (se 1 (by rfl) ⟨10428992, by rfl⟩ : syracuseStep 13905323 = 20857985) B20857985
theorem B3429823 : Blo 1352995 3429823 := bstep (se 1 (by rfl) ⟨2572367, by rfl⟩ : syracuseStep 3429823 = 5144735) B5144735
theorem B4573097 : Blo 1352995 4573097 := bstep (se 2 (by rfl) ⟨1714911, by rfl⟩ : syracuseStep 4573097 = 3429823) B3429823
theorem B9270215 : Blo 1352995 9270215 := bstep (se 1 (by rfl) ⟨6952661, by rfl⟩ : syracuseStep 9270215 = 13905323) B13905323
theorem B3048731 : Blo 1352995 3048731 := bstep (se 1 (by rfl) ⟨2286548, by rfl⟩ : syracuseStep 3048731 = 4573097) B4573097
theorem B6180143 : Blo 1352995 6180143 := bstep (se 1 (by rfl) ⟨4635107, by rfl⟩ : syracuseStep 6180143 = 9270215) B9270215
theorem B65921525 : Blo 1352995 65921525 := bstep (se 5 (by rfl) ⟨3090071, by rfl⟩ : syracuseStep 65921525 = 6180143) B6180143
theorem B2032487 : Blo 1352995 2032487 := bstep (se 1 (by rfl) ⟨1524365, by rfl⟩ : syracuseStep 2032487 = 3048731) B3048731
theorem B1354991 : Blo 1352995 1354991 := bstep (se 1 (by rfl) ⟨1016243, by rfl⟩ : syracuseStep 1354991 = 2032487) B2032487
theorem B43947683 : Blo 1352995 43947683 := bstep (se 1 (by rfl) ⟨32960762, by rfl⟩ : syracuseStep 43947683 = 65921525) B65921525
theorem B29298455 : Blo 1352995 29298455 := bstep (se 1 (by rfl) ⟨21973841, by rfl⟩ : syracuseStep 29298455 = 43947683) B43947683
theorem B19532303 : Blo 1352995 19532303 := bstep (se 1 (by rfl) ⟨14649227, by rfl⟩ : syracuseStep 19532303 = 29298455) B29298455
theorem B13021535 : Blo 1352995 13021535 := bstep (se 1 (by rfl) ⟨9766151, by rfl⟩ : syracuseStep 13021535 = 19532303) B19532303
theorem B8681023 : Blo 1352995 8681023 := bstep (se 1 (by rfl) ⟨6510767, by rfl⟩ : syracuseStep 8681023 = 13021535) B13021535
theorem B11574697 : Blo 1352995 11574697 := bstep (se 2 (by rfl) ⟨4340511, by rfl⟩ : syracuseStep 11574697 = 8681023) B8681023
theorem B15432929 : Blo 1352995 15432929 := bstep (se 2 (by rfl) ⟨5787348, by rfl⟩ : syracuseStep 15432929 = 11574697) B11574697
theorem B10288619 : Blo 1352995 10288619 := bstep (se 1 (by rfl) ⟨7716464, by rfl⟩ : syracuseStep 10288619 = 15432929) B15432929
theorem B6859079 : Blo 1352995 6859079 := bstep (se 1 (by rfl) ⟨5144309, by rfl⟩ : syracuseStep 6859079 = 10288619) B10288619
theorem B4572719 : Blo 1352995 4572719 := bstep (se 1 (by rfl) ⟨3429539, by rfl⟩ : syracuseStep 4572719 = 6859079) B6859079
theorem B3048479 : Blo 1352995 3048479 := bstep (se 1 (by rfl) ⟨2286359, by rfl⟩ : syracuseStep 3048479 = 4572719) B4572719
theorem B2032319 : Blo 1352995 2032319 := bstep (se 1 (by rfl) ⟨1524239, by rfl⟩ : syracuseStep 2032319 = 3048479) B3048479
theorem B1354879 : Blo 1352995 1354879 := bstep (se 1 (by rfl) ⟨1016159, by rfl⟩ : syracuseStep 1354879 = 2032319) B2032319

theorem C0 (j : ℕ) (h1 : 338248 ≤ j) (h2 : j ≤ 338748) : Blo 1352995 (4 * j + 3) := by
  interval_cases j
  · exact B1352995
  · exact B1352999
  · exact B1353003
  · exact B1353007
  · exact B1353011
  · exact B1353015
  · exact B1353019
  · exact B1353023
  · exact B1353027
  · exact B1353031
  · exact B1353035
  · exact B1353039
  · exact B1353043
  · exact B1353047
  · exact B1353051
  · exact B1353055
  · exact B1353059
  · exact B1353063
  · exact B1353067
  · exact B1353071
  · exact B1353075
  · exact B1353079
  · exact B1353083
  · exact B1353087
  · exact B1353091
  · exact B1353095
  · exact B1353099
  · exact B1353103
  · exact B1353107
  · exact B1353111
  · exact B1353115
  · exact B1353119
  · exact B1353123
  · exact B1353127
  · exact B1353131
  · exact B1353135
  · exact B1353139
  · exact B1353143
  · exact B1353147
  · exact B1353151
  · exact B1353155
  · exact B1353159
  · exact B1353163
  · exact B1353167
  · exact B1353171
  · exact B1353175
  · exact B1353179
  · exact B1353183
  · exact B1353187
  · exact B1353191
  · exact B1353195
  · exact B1353199
  · exact B1353203
  · exact B1353207
  · exact B1353211
  · exact B1353215
  · exact B1353219
  · exact B1353223
  · exact B1353227
  · exact B1353231
  · exact B1353235
  · exact B1353239
  · exact B1353243
  · exact B1353247
  · exact B1353251
  · exact B1353255
  · exact B1353259
  · exact B1353263
  · exact B1353267
  · exact B1353271
  · exact B1353275
  · exact B1353279
  · exact B1353283
  · exact B1353287
  · exact B1353291
  · exact B1353295
  · exact B1353299
  · exact B1353303
  · exact B1353307
  · exact B1353311
  · exact B1353315
  · exact B1353319
  · exact B1353323
  · exact B1353327
  · exact B1353331
  · exact B1353335
  · exact B1353339
  · exact B1353343
  · exact B1353347
  · exact B1353351
  · exact B1353355
  · exact B1353359
  · exact B1353363
  · exact B1353367
  · exact B1353371
  · exact B1353375
  · exact B1353379
  · exact B1353383
  · exact B1353387
  · exact B1353391
  · exact B1353395
  · exact B1353399
  · exact B1353403
  · exact B1353407
  · exact B1353411
  · exact B1353415
  · exact B1353419
  · exact B1353423
  · exact B1353427
  · exact B1353431
  · exact B1353435
  · exact B1353439
  · exact B1353443
  · exact B1353447
  · exact B1353451
  · exact B1353455
  · exact B1353459
  · exact B1353463
  · exact B1353467
  · exact B1353471
  · exact B1353475
  · exact B1353479
  · exact B1353483
  · exact B1353487
  · exact B1353491
  · exact B1353495
  · exact B1353499
  · exact B1353503
  · exact B1353507
  · exact B1353511
  · exact B1353515
  · exact B1353519
  · exact B1353523
  · exact B1353527
  · exact B1353531
  · exact B1353535
  · exact B1353539
  · exact B1353543
  · exact B1353547
  · exact B1353551
  · exact B1353555
  · exact B1353559
  · exact B1353563
  · exact B1353567
  · exact B1353571
  · exact B1353575
  · exact B1353579
  · exact B1353583
  · exact B1353587
  · exact B1353591
  · exact B1353595
  · exact B1353599
  · exact B1353603
  · exact B1353607
  · exact B1353611
  · exact B1353615
  · exact B1353619
  · exact B1353623
  · exact B1353627
  · exact B1353631
  · exact B1353635
  · exact B1353639
  · exact B1353643
  · exact B1353647
  · exact B1353651
  · exact B1353655
  · exact B1353659
  · exact B1353663
  · exact B1353667
  · exact B1353671
  · exact B1353675
  · exact B1353679
  · exact B1353683
  · exact B1353687
  · exact B1353691
  · exact B1353695
  · exact B1353699
  · exact B1353703
  · exact B1353707
  · exact B1353711
  · exact B1353715
  · exact B1353719
  · exact B1353723
  · exact B1353727
  · exact B1353731
  · exact B1353735
  · exact B1353739
  · exact B1353743
  · exact B1353747
  · exact B1353751
  · exact B1353755
  · exact B1353759
  · exact B1353763
  · exact B1353767
  · exact B1353771
  · exact B1353775
  · exact B1353779
  · exact B1353783
  · exact B1353787
  · exact B1353791
  · exact B1353795
  · exact B1353799
  · exact B1353803
  · exact B1353807
  · exact B1353811
  · exact B1353815
  · exact B1353819
  · exact B1353823
  · exact B1353827
  · exact B1353831
  · exact B1353835
  · exact B1353839
  · exact B1353843
  · exact B1353847
  · exact B1353851
  · exact B1353855
  · exact B1353859
  · exact B1353863
  · exact B1353867
  · exact B1353871
  · exact B1353875
  · exact B1353879
  · exact B1353883
  · exact B1353887
  · exact B1353891
  · exact B1353895
  · exact B1353899
  · exact B1353903
  · exact B1353907
  · exact B1353911
  · exact B1353915
  · exact B1353919
  · exact B1353923
  · exact B1353927
  · exact B1353931
  · exact B1353935
  · exact B1353939
  · exact B1353943
  · exact B1353947
  · exact B1353951
  · exact B1353955
  · exact B1353959
  · exact B1353963
  · exact B1353967
  · exact B1353971
  · exact B1353975
  · exact B1353979
  · exact B1353983
  · exact B1353987
  · exact B1353991
  · exact B1353995
  · exact B1353999
  · exact B1354003
  · exact B1354007
  · exact B1354011
  · exact B1354015
  · exact B1354019
  · exact B1354023
  · exact B1354027
  · exact B1354031
  · exact B1354035
  · exact B1354039
  · exact B1354043
  · exact B1354047
  · exact B1354051
  · exact B1354055
  · exact B1354059
  · exact B1354063
  · exact B1354067
  · exact B1354071
  · exact B1354075
  · exact B1354079
  · exact B1354083
  · exact B1354087
  · exact B1354091
  · exact B1354095
  · exact B1354099
  · exact B1354103
  · exact B1354107
  · exact B1354111
  · exact B1354115
  · exact B1354119
  · exact B1354123
  · exact B1354127
  · exact B1354131
  · exact B1354135
  · exact B1354139
  · exact B1354143
  · exact B1354147
  · exact B1354151
  · exact B1354155
  · exact B1354159
  · exact B1354163
  · exact B1354167
  · exact B1354171
  · exact B1354175
  · exact B1354179
  · exact B1354183
  · exact B1354187
  · exact B1354191
  · exact B1354195
  · exact B1354199
  · exact B1354203
  · exact B1354207
  · exact B1354211
  · exact B1354215
  · exact B1354219
  · exact B1354223
  · exact B1354227
  · exact B1354231
  · exact B1354235
  · exact B1354239
  · exact B1354243
  · exact B1354247
  · exact B1354251
  · exact B1354255
  · exact B1354259
  · exact B1354263
  · exact B1354267
  · exact B1354271
  · exact B1354275
  · exact B1354279
  · exact B1354283
  · exact B1354287
  · exact B1354291
  · exact B1354295
  · exact B1354299
  · exact B1354303
  · exact B1354307
  · exact B1354311
  · exact B1354315
  · exact B1354319
  · exact B1354323
  · exact B1354327
  · exact B1354331
  · exact B1354335
  · exact B1354339
  · exact B1354343
  · exact B1354347
  · exact B1354351
  · exact B1354355
  · exact B1354359
  · exact B1354363
  · exact B1354367
  · exact B1354371
  · exact B1354375
  · exact B1354379
  · exact B1354383
  · exact B1354387
  · exact B1354391
  · exact B1354395
  · exact B1354399
  · exact B1354403
  · exact B1354407
  · exact B1354411
  · exact B1354415
  · exact B1354419
  · exact B1354423
  · exact B1354427
  · exact B1354431
  · exact B1354435
  · exact B1354439
  · exact B1354443
  · exact B1354447
  · exact B1354451
  · exact B1354455
  · exact B1354459
  · exact B1354463
  · exact B1354467
  · exact B1354471
  · exact B1354475
  · exact B1354479
  · exact B1354483
  · exact B1354487
  · exact B1354491
  · exact B1354495
  · exact B1354499
  · exact B1354503
  · exact B1354507
  · exact B1354511
  · exact B1354515
  · exact B1354519
  · exact B1354523
  · exact B1354527
  · exact B1354531
  · exact B1354535
  · exact B1354539
  · exact B1354543
  · exact B1354547
  · exact B1354551
  · exact B1354555
  · exact B1354559
  · exact B1354563
  · exact B1354567
  · exact B1354571
  · exact B1354575
  · exact B1354579
  · exact B1354583
  · exact B1354587
  · exact B1354591
  · exact B1354595
  · exact B1354599
  · exact B1354603
  · exact B1354607
  · exact B1354611
  · exact B1354615
  · exact B1354619
  · exact B1354623
  · exact B1354627
  · exact B1354631
  · exact B1354635
  · exact B1354639
  · exact B1354643
  · exact B1354647
  · exact B1354651
  · exact B1354655
  · exact B1354659
  · exact B1354663
  · exact B1354667
  · exact B1354671
  · exact B1354675
  · exact B1354679
  · exact B1354683
  · exact B1354687
  · exact B1354691
  · exact B1354695
  · exact B1354699
  · exact B1354703
  · exact B1354707
  · exact B1354711
  · exact B1354715
  · exact B1354719
  · exact B1354723
  · exact B1354727
  · exact B1354731
  · exact B1354735
  · exact B1354739
  · exact B1354743
  · exact B1354747
  · exact B1354751
  · exact B1354755
  · exact B1354759
  · exact B1354763
  · exact B1354767
  · exact B1354771
  · exact B1354775
  · exact B1354779
  · exact B1354783
  · exact B1354787
  · exact B1354791
  · exact B1354795
  · exact B1354799
  · exact B1354803
  · exact B1354807
  · exact B1354811
  · exact B1354815
  · exact B1354819
  · exact B1354823
  · exact B1354827
  · exact B1354831
  · exact B1354835
  · exact B1354839
  · exact B1354843
  · exact B1354847
  · exact B1354851
  · exact B1354855
  · exact B1354859
  · exact B1354863
  · exact B1354867
  · exact B1354871
  · exact B1354875
  · exact B1354879
  · exact B1354883
  · exact B1354887
  · exact B1354891
  · exact B1354895
  · exact B1354899
  · exact B1354903
  · exact B1354907
  · exact B1354911
  · exact B1354915
  · exact B1354919
  · exact B1354923
  · exact B1354927
  · exact B1354931
  · exact B1354935
  · exact B1354939
  · exact B1354943
  · exact B1354947
  · exact B1354951
  · exact B1354955
  · exact B1354959
  · exact B1354963
  · exact B1354967
  · exact B1354971
  · exact B1354975
  · exact B1354979
  · exact B1354983
  · exact B1354987
  · exact B1354991
  · exact B1354995

theorem solution (m : ℕ) (hlo : 1352995 ≤ m) (hhi : m ≤ 1354995) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 338248 ≤ j := by omega
    have hj2 : j ≤ 338748 := by omega
    have hb : Blo 1352995 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
