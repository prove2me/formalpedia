-- Prove2me | solution 1 for syracuse_descends_range_451781_455781
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:59.063666+00:00
-- url     : https://prove2.me/submissions/558f5e78-69e0-43eb-bbe8-a3a7e962ebc8

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


theorem B1933429 : Blo 451781 1933429 := bbase (se 5 (by rfl) ⟨90629, by rfl⟩ : syracuseStep 1933429 = 181259) (by norm_num)
theorem B1933445 : Blo 451781 1933445 := bbase (se 4 (by rfl) ⟨181260, by rfl⟩ : syracuseStep 1933445 = 362521) (by norm_num)
theorem B622733 : Blo 451781 622733 := bbase (se 3 (by rfl) ⟨116762, by rfl⟩ : syracuseStep 622733 = 233525) (by norm_num)
theorem B458897 : Blo 451781 458897 := bbase (se 2 (by rfl) ⟨172086, by rfl⟩ : syracuseStep 458897 = 344173) (by norm_num)
theorem B1147061 : Blo 451781 1147061 := bbase (se 5 (by rfl) ⟨53768, by rfl⟩ : syracuseStep 1147061 = 107537) (by norm_num)
theorem B688493 : Blo 451781 688493 := bbase (se 3 (by rfl) ⟨129092, by rfl⟩ : syracuseStep 688493 = 258185) (by norm_num)
theorem B1147405 : Blo 451781 1147405 := bbase (se 3 (by rfl) ⟨215138, by rfl⟩ : syracuseStep 1147405 = 430277) (by norm_num)
theorem B1147517 : Blo 451781 1147517 := bbase (se 3 (by rfl) ⟨215159, by rfl⟩ : syracuseStep 1147517 = 430319) (by norm_num)
theorem B2294405 : Blo 451781 2294405 := bbase (se 4 (by rfl) ⟨215100, by rfl⟩ : syracuseStep 2294405 = 430201) (by norm_num)
theorem B3441365 : Blo 451781 3441365 := bbase (se 7 (by rfl) ⟨40328, by rfl⟩ : syracuseStep 3441365 = 80657) (by norm_num)
theorem B1016549 : Blo 451781 1016549 := bbase (se 4 (by rfl) ⟨95301, by rfl⟩ : syracuseStep 1016549 = 190603) (by norm_num)
theorem B459497 : Blo 451781 459497 := bbase (se 2 (by rfl) ⟨172311, by rfl⟩ : syracuseStep 459497 = 344623) (by norm_num)
theorem B1016621 : Blo 451781 1016621 := bbase (se 3 (by rfl) ⟨190616, by rfl⟩ : syracuseStep 1016621 = 381233) (by norm_num)
theorem B1147709 : Blo 451781 1147709 := bbase (se 3 (by rfl) ⟨215195, by rfl⟩ : syracuseStep 1147709 = 430391) (by norm_num)
theorem B525145 : Blo 451781 525145 := bbase (se 2 (by rfl) ⟨196929, by rfl⟩ : syracuseStep 525145 = 393859) (by norm_num)
theorem B1016693 : Blo 451781 1016693 := bbase (se 5 (by rfl) ⟨47657, by rfl⟩ : syracuseStep 1016693 = 95315) (by norm_num)
theorem B1016765 : Blo 451781 1016765 := bbase (se 3 (by rfl) ⟨190643, by rfl⟩ : syracuseStep 1016765 = 381287) (by norm_num)
theorem B1016837 : Blo 451781 1016837 := bbase (se 4 (by rfl) ⟨95328, by rfl⟩ : syracuseStep 1016837 = 190657) (by norm_num)
theorem B1016909 : Blo 451781 1016909 := bbase (se 3 (by rfl) ⟨190670, by rfl⟩ : syracuseStep 1016909 = 381341) (by norm_num)
theorem B1016981 : Blo 451781 1016981 := bbase (se 6 (by rfl) ⟨23835, by rfl⟩ : syracuseStep 1016981 = 47671) (by norm_num)
theorem B1148053 : Blo 451781 1148053 := bbase (se 6 (by rfl) ⟨26907, by rfl⟩ : syracuseStep 1148053 = 53815) (by norm_num)
theorem B1017053 : Blo 451781 1017053 := bbase (se 3 (by rfl) ⟨190697, by rfl⟩ : syracuseStep 1017053 = 381395) (by norm_num)
theorem B2622709 : Blo 451781 2622709 := bbase (se 5 (by rfl) ⟨122939, by rfl⟩ : syracuseStep 2622709 = 245879) (by norm_num)
theorem B1148165 : Blo 451781 1148165 := bbase (se 4 (by rfl) ⟨107640, by rfl⟩ : syracuseStep 1148165 = 215281) (by norm_num)
theorem B1017125 : Blo 451781 1017125 := bbase (se 4 (by rfl) ⟨95355, by rfl⟩ : syracuseStep 1017125 = 190711) (by norm_num)
theorem B460081 : Blo 451781 460081 := bbase (se 2 (by rfl) ⟨172530, by rfl⟩ : syracuseStep 460081 = 345061) (by norm_num)
theorem B1377605 : Blo 451781 1377605 := bbase (se 4 (by rfl) ⟨129150, by rfl⟩ : syracuseStep 1377605 = 258301) (by norm_num)
theorem B1246565 : Blo 451781 1246565 := bbase (se 4 (by rfl) ⟨116865, by rfl⟩ : syracuseStep 1246565 = 233731) (by norm_num)
theorem B1017197 : Blo 451781 1017197 := bbase (se 3 (by rfl) ⟨190724, by rfl⟩ : syracuseStep 1017197 = 381449) (by norm_num)
theorem B1017269 : Blo 451781 1017269 := bbase (se 5 (by rfl) ⟨47684, by rfl⟩ : syracuseStep 1017269 = 95369) (by norm_num)
theorem B1148357 : Blo 451781 1148357 := bbase (se 4 (by rfl) ⟨107658, by rfl⟩ : syracuseStep 1148357 = 215317) (by norm_num)
theorem B1017341 : Blo 451781 1017341 := bbase (se 3 (by rfl) ⟨190751, by rfl⟩ : syracuseStep 1017341 = 381503) (by norm_num)
theorem B1017413 : Blo 451781 1017413 := bbase (se 4 (by rfl) ⟨95382, by rfl⟩ : syracuseStep 1017413 = 190765) (by norm_num)
theorem B919117 : Blo 451781 919117 := bbase (se 3 (by rfl) ⟨172334, by rfl⟩ : syracuseStep 919117 = 344669) (by norm_num)
theorem B1017485 : Blo 451781 1017485 := bbase (se 3 (by rfl) ⟨190778, by rfl⟩ : syracuseStep 1017485 = 381557) (by norm_num)
theorem B919181 : Blo 451781 919181 := bbase (se 3 (by rfl) ⟨172346, by rfl⟩ : syracuseStep 919181 = 344693) (by norm_num)
theorem B1312453 : Blo 451781 1312453 := bbase (se 4 (by rfl) ⟨123042, by rfl⟩ : syracuseStep 1312453 = 246085) (by norm_num)
theorem B1017557 : Blo 451781 1017557 := bbase (se 7 (by rfl) ⟨11924, by rfl⟩ : syracuseStep 1017557 = 23849) (by norm_num)
theorem B1017629 : Blo 451781 1017629 := bbase (se 3 (by rfl) ⟨190805, by rfl⟩ : syracuseStep 1017629 = 381611) (by norm_num)
theorem B1148701 : Blo 451781 1148701 := bbase (se 3 (by rfl) ⟨215381, by rfl⟩ : syracuseStep 1148701 = 430763) (by norm_num)
theorem B1017701 : Blo 451781 1017701 := bbase (se 4 (by rfl) ⟨95409, by rfl⟩ : syracuseStep 1017701 = 190819) (by norm_num)
theorem B1148813 : Blo 451781 1148813 := bbase (se 3 (by rfl) ⟨215402, by rfl⟩ : syracuseStep 1148813 = 430805) (by norm_num)
theorem B657293 : Blo 451781 657293 := bbase (se 3 (by rfl) ⟨123242, by rfl⟩ : syracuseStep 657293 = 246485) (by norm_num)
theorem B2295701 : Blo 451781 2295701 := bbase (se 6 (by rfl) ⟨53805, by rfl⟩ : syracuseStep 2295701 = 107611) (by norm_num)
theorem B1640341 : Blo 451781 1640341 := bbase (se 6 (by rfl) ⟨38445, by rfl⟩ : syracuseStep 1640341 = 76891) (by norm_num)
theorem B1017773 : Blo 451781 1017773 := bbase (se 3 (by rfl) ⟨190832, by rfl⟩ : syracuseStep 1017773 = 381665) (by norm_num)
theorem B1017845 : Blo 451781 1017845 := bbase (se 5 (by rfl) ⟨47711, by rfl⟩ : syracuseStep 1017845 = 95423) (by norm_num)
theorem B1017917 : Blo 451781 1017917 := bbase (se 3 (by rfl) ⟨190859, by rfl⟩ : syracuseStep 1017917 = 381719) (by norm_num)
theorem B1149005 : Blo 451781 1149005 := bbase (se 3 (by rfl) ⟨215438, by rfl⟩ : syracuseStep 1149005 = 430877) (by norm_num)
theorem B1378421 : Blo 451781 1378421 := bbase (se 5 (by rfl) ⟨64613, by rfl⟩ : syracuseStep 1378421 = 129227) (by norm_num)
theorem B460933 : Blo 451781 460933 := bbase (se 4 (by rfl) ⟨43212, by rfl⟩ : syracuseStep 460933 = 86425) (by norm_num)
theorem B1017989 : Blo 451781 1017989 := bbase (se 4 (by rfl) ⟨95436, by rfl⟩ : syracuseStep 1017989 = 190873) (by norm_num)
theorem B460973 : Blo 451781 460973 := bbase (se 3 (by rfl) ⟨86432, by rfl⟩ : syracuseStep 460973 = 172865) (by norm_num)
theorem B1018061 : Blo 451781 1018061 := bbase (se 3 (by rfl) ⟨190886, by rfl⟩ : syracuseStep 1018061 = 381773) (by norm_num)
theorem B1018133 : Blo 451781 1018133 := bbase (se 6 (by rfl) ⟨23862, by rfl⟩ : syracuseStep 1018133 = 47725) (by norm_num)
theorem B657709 : Blo 451781 657709 := bbase (se 3 (by rfl) ⟨123320, by rfl⟩ : syracuseStep 657709 = 246641) (by norm_num)
theorem B1935701 : Blo 451781 1935701 := bbase (se 10 (by rfl) ⟨2835, by rfl⟩ : syracuseStep 1935701 = 5671) (by norm_num)
theorem B1018205 : Blo 451781 1018205 := bbase (se 3 (by rfl) ⟨190913, by rfl⟩ : syracuseStep 1018205 = 381827) (by norm_num)
theorem B3869045 : Blo 451781 3869045 := bbase (se 5 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 3869045 = 362723) (by norm_num)
theorem B2623861 : Blo 451781 2623861 := bbase (se 5 (by rfl) ⟨122993, by rfl⟩ : syracuseStep 2623861 = 245987) (by norm_num)
theorem B1018277 : Blo 451781 1018277 := bbase (se 4 (by rfl) ⟨95463, by rfl⟩ : syracuseStep 1018277 = 190927) (by norm_num)
theorem B1149349 : Blo 451781 1149349 := bbase (se 4 (by rfl) ⟨107751, by rfl⟩ : syracuseStep 1149349 = 215503) (by norm_num)
theorem B1018349 : Blo 451781 1018349 := bbase (se 3 (by rfl) ⟨190940, by rfl⟩ : syracuseStep 1018349 = 381881) (by norm_num)
theorem B1149461 : Blo 451781 1149461 := bbase (se 6 (by rfl) ⟨26940, by rfl⟩ : syracuseStep 1149461 = 53881) (by norm_num)
theorem B1018421 : Blo 451781 1018421 := bbase (se 5 (by rfl) ⟨47738, by rfl⟩ : syracuseStep 1018421 = 95477) (by norm_num)
theorem B690749 : Blo 451781 690749 := bbase (se 3 (by rfl) ⟨129515, by rfl⟩ : syracuseStep 690749 = 259031) (by norm_num)
theorem B1018493 : Blo 451781 1018493 := bbase (se 3 (by rfl) ⟨190967, by rfl⟩ : syracuseStep 1018493 = 381935) (by norm_num)
theorem B789173 : Blo 451781 789173 := bbase (se 5 (by rfl) ⟨36992, by rfl⟩ : syracuseStep 789173 = 73985) (by norm_num)
theorem B1018565 : Blo 451781 1018565 := bbase (se 4 (by rfl) ⟨95490, by rfl⟩ : syracuseStep 1018565 = 190981) (by norm_num)
theorem B920261 : Blo 451781 920261 := bbase (se 4 (by rfl) ⟨86274, by rfl⟩ : syracuseStep 920261 = 172549) (by norm_num)
theorem B1149653 : Blo 451781 1149653 := bbase (se 7 (by rfl) ⟨13472, by rfl⟩ : syracuseStep 1149653 = 26945) (by norm_num)
theorem B1018637 : Blo 451781 1018637 := bbase (se 3 (by rfl) ⟨190994, by rfl⟩ : syracuseStep 1018637 = 381989) (by norm_num)
theorem B1018709 : Blo 451781 1018709 := bbase (se 9 (by rfl) ⟨2984, by rfl⟩ : syracuseStep 1018709 = 5969) (by norm_num)
theorem B1018781 : Blo 451781 1018781 := bbase (se 3 (by rfl) ⟨191021, by rfl⟩ : syracuseStep 1018781 = 382043) (by norm_num)
theorem B1018853 : Blo 451781 1018853 := bbase (se 4 (by rfl) ⟨95517, by rfl⟩ : syracuseStep 1018853 = 191035) (by norm_num)
theorem B1018925 : Blo 451781 1018925 := bbase (se 3 (by rfl) ⟨191048, by rfl⟩ : syracuseStep 1018925 = 382097) (by norm_num)
theorem B1149997 : Blo 451781 1149997 := bbase (se 3 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 1149997 = 431249) (by norm_num)
theorem B461897 : Blo 451781 461897 := bbase (se 2 (by rfl) ⟨173211, by rfl⟩ : syracuseStep 461897 = 346423) (by norm_num)
theorem B1018997 : Blo 451781 1018997 := bbase (se 5 (by rfl) ⟨47765, by rfl⟩ : syracuseStep 1018997 = 95531) (by norm_num)
theorem B1150109 : Blo 451781 1150109 := bbase (se 3 (by rfl) ⟨215645, by rfl⟩ : syracuseStep 1150109 = 431291) (by norm_num)
theorem B724133 : Blo 451781 724133 := bbase (se 4 (by rfl) ⟨67887, by rfl⟩ : syracuseStep 724133 = 135775) (by norm_num)
theorem B2296997 : Blo 451781 2296997 := bbase (se 4 (by rfl) ⟨215343, by rfl⟩ : syracuseStep 2296997 = 430687) (by norm_num)
theorem B1019069 : Blo 451781 1019069 := bbase (se 3 (by rfl) ⟨191075, by rfl⟩ : syracuseStep 1019069 = 382151) (by norm_num)
theorem B1019141 : Blo 451781 1019141 := bbase (se 4 (by rfl) ⟨95544, by rfl⟩ : syracuseStep 1019141 = 191089) (by norm_num)
theorem B1019213 : Blo 451781 1019213 := bbase (se 3 (by rfl) ⟨191102, by rfl⟩ : syracuseStep 1019213 = 382205) (by norm_num)
theorem B920909 : Blo 451781 920909 := bbase (se 3 (by rfl) ⟨172670, by rfl⟩ : syracuseStep 920909 = 345341) (by norm_num)
theorem B1150301 : Blo 451781 1150301 := bbase (se 3 (by rfl) ⟨215681, by rfl⟩ : syracuseStep 1150301 = 431363) (by norm_num)
theorem B1019285 : Blo 451781 1019285 := bbase (se 6 (by rfl) ⟨23889, by rfl⟩ : syracuseStep 1019285 = 47779) (by norm_num)
theorem B724421 : Blo 451781 724421 := bbase (se 4 (by rfl) ⟨67914, by rfl⟩ : syracuseStep 724421 = 135829) (by norm_num)
theorem B7376341 : Blo 451781 7376341 := bbase (se 7 (by rfl) ⟨86441, by rfl⟩ : syracuseStep 7376341 = 172883) (by norm_num)
theorem B1019357 : Blo 451781 1019357 := bbase (se 3 (by rfl) ⟨191129, by rfl⟩ : syracuseStep 1019357 = 382259) (by norm_num)
theorem B1019429 : Blo 451781 1019429 := bbase (se 4 (by rfl) ⟨95571, by rfl⟩ : syracuseStep 1019429 = 191143) (by norm_num)
theorem B1183301 : Blo 451781 1183301 := bbase (se 4 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 1183301 = 221869) (by norm_num)
theorem B5836373 : Blo 451781 5836373 := bbase (se 8 (by rfl) ⟨34197, by rfl⟩ : syracuseStep 5836373 = 68395) (by norm_num)
theorem B1019501 : Blo 451781 1019501 := bbase (se 3 (by rfl) ⟨191156, by rfl⟩ : syracuseStep 1019501 = 382313) (by norm_num)
theorem B1019573 : Blo 451781 1019573 := bbase (se 5 (by rfl) ⟨47792, by rfl⟩ : syracuseStep 1019573 = 95585) (by norm_num)
theorem B1150645 : Blo 451781 1150645 := bbase (se 5 (by rfl) ⟨53936, by rfl⟩ : syracuseStep 1150645 = 107873) (by norm_num)
theorem B1019645 : Blo 451781 1019645 := bbase (se 3 (by rfl) ⟨191183, by rfl⟩ : syracuseStep 1019645 = 382367) (by norm_num)
theorem B1150757 : Blo 451781 1150757 := bbase (se 4 (by rfl) ⟨107883, by rfl⟩ : syracuseStep 1150757 = 215767) (by norm_num)
theorem B1019717 : Blo 451781 1019717 := bbase (se 4 (by rfl) ⟨95598, by rfl⟩ : syracuseStep 1019717 = 191197) (by norm_num)
theorem B1838933 : Blo 451781 1838933 := bbase (se 9 (by rfl) ⟨5387, by rfl⟩ : syracuseStep 1838933 = 10775) (by norm_num)
theorem B724837 : Blo 451781 724837 := bbase (se 4 (by rfl) ⟨67953, by rfl⟩ : syracuseStep 724837 = 135907) (by norm_num)
theorem B1019789 : Blo 451781 1019789 := bbase (se 3 (by rfl) ⟨191210, by rfl⟩ : syracuseStep 1019789 = 382421) (by norm_num)
theorem B1019861 : Blo 451781 1019861 := bbase (se 7 (by rfl) ⟨11951, by rfl⟩ : syracuseStep 1019861 = 23903) (by norm_num)
theorem B1150949 : Blo 451781 1150949 := bbase (se 4 (by rfl) ⟨107901, by rfl⟩ : syracuseStep 1150949 = 215803) (by norm_num)
theorem B1019933 : Blo 451781 1019933 := bbase (se 3 (by rfl) ⟨191237, by rfl⟩ : syracuseStep 1019933 = 382475) (by norm_num)
theorem B1020005 : Blo 451781 1020005 := bbase (se 4 (by rfl) ⟨95625, by rfl⟩ : syracuseStep 1020005 = 191251) (by norm_num)
theorem B2592917 : Blo 451781 2592917 := bbase (se 6 (by rfl) ⟨60771, by rfl⟩ : syracuseStep 2592917 = 121543) (by norm_num)
theorem B1020077 : Blo 451781 1020077 := bbase (se 3 (by rfl) ⟨191264, by rfl⟩ : syracuseStep 1020077 = 382529) (by norm_num)
theorem B4657333 : Blo 451781 4657333 := bbase (se 5 (by rfl) ⟨218312, by rfl⟩ : syracuseStep 4657333 = 436625) (by norm_num)
theorem B1020149 : Blo 451781 1020149 := bbase (se 5 (by rfl) ⟨47819, by rfl⟩ : syracuseStep 1020149 = 95639) (by norm_num)
theorem B1020221 : Blo 451781 1020221 := bbase (se 3 (by rfl) ⟨191291, by rfl⟩ : syracuseStep 1020221 = 382583) (by norm_num)
theorem B1151293 : Blo 451781 1151293 := bbase (se 3 (by rfl) ⟨215867, by rfl⟩ : syracuseStep 1151293 = 431735) (by norm_num)
theorem B1020293 : Blo 451781 1020293 := bbase (se 4 (by rfl) ⟨95652, by rfl⟩ : syracuseStep 1020293 = 191305) (by norm_num)
theorem B1151405 : Blo 451781 1151405 := bbase (se 3 (by rfl) ⟨215888, by rfl⟩ : syracuseStep 1151405 = 431777) (by norm_num)
theorem B2298293 : Blo 451781 2298293 := bbase (se 5 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 2298293 = 215465) (by norm_num)
theorem B1020365 : Blo 451781 1020365 := bbase (se 3 (by rfl) ⟨191318, by rfl⟩ : syracuseStep 1020365 = 382637) (by norm_num)
theorem B692749 : Blo 451781 692749 := bbase (se 3 (by rfl) ⟨129890, by rfl⟩ : syracuseStep 692749 = 259781) (by norm_num)
theorem B1020437 : Blo 451781 1020437 := bbase (se 6 (by rfl) ⟨23916, by rfl⟩ : syracuseStep 1020437 = 47833) (by norm_num)
theorem B1020509 : Blo 451781 1020509 := bbase (se 3 (by rfl) ⟨191345, by rfl⟩ : syracuseStep 1020509 = 382691) (by norm_num)
theorem B1151597 : Blo 451781 1151597 := bbase (se 3 (by rfl) ⟨215924, by rfl⟩ : syracuseStep 1151597 = 431849) (by norm_num)
theorem B1020581 : Blo 451781 1020581 := bbase (se 4 (by rfl) ⟨95679, by rfl⟩ : syracuseStep 1020581 = 191359) (by norm_num)
theorem B1020653 : Blo 451781 1020653 := bbase (se 3 (by rfl) ⟨191372, by rfl⟩ : syracuseStep 1020653 = 382745) (by norm_num)
theorem B725773 : Blo 451781 725773 := bbase (se 3 (by rfl) ⟨136082, by rfl⟩ : syracuseStep 725773 = 272165) (by norm_num)
theorem B1020725 : Blo 451781 1020725 := bbase (se 5 (by rfl) ⟨47846, by rfl⟩ : syracuseStep 1020725 = 95693) (by norm_num)
theorem B1020797 : Blo 451781 1020797 := bbase (se 3 (by rfl) ⟨191399, by rfl⟩ : syracuseStep 1020797 = 382799) (by norm_num)
theorem B1020869 : Blo 451781 1020869 := bbase (se 4 (by rfl) ⟨95706, by rfl⟩ : syracuseStep 1020869 = 191413) (by norm_num)
theorem B1151941 : Blo 451781 1151941 := bbase (se 4 (by rfl) ⟨107994, by rfl⟩ : syracuseStep 1151941 = 215989) (by norm_num)
theorem B1020941 : Blo 451781 1020941 := bbase (se 3 (by rfl) ⟨191426, by rfl⟩ : syracuseStep 1020941 = 382853) (by norm_num)
theorem B1152053 : Blo 451781 1152053 := bbase (se 5 (by rfl) ⟨54002, by rfl⟩ : syracuseStep 1152053 = 108005) (by norm_num)
theorem B1021013 : Blo 451781 1021013 := bbase (se 8 (by rfl) ⟨5982, by rfl⟩ : syracuseStep 1021013 = 11965) (by norm_num)
theorem B922709 : Blo 451781 922709 := bbase (se 8 (by rfl) ⟨5406, by rfl⟩ : syracuseStep 922709 = 10813) (by norm_num)
theorem B1840229 : Blo 451781 1840229 := bbase (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) (by norm_num)
theorem B2069621 : Blo 451781 2069621 := bbase (se 5 (by rfl) ⟨97013, by rfl⟩ : syracuseStep 2069621 = 194027) (by norm_num)
theorem B1021085 : Blo 451781 1021085 := bbase (se 3 (by rfl) ⟨191453, by rfl⟩ : syracuseStep 1021085 = 382907) (by norm_num)
theorem B1021157 : Blo 451781 1021157 := bbase (se 4 (by rfl) ⟨95733, by rfl⟩ : syracuseStep 1021157 = 191467) (by norm_num)
theorem B1152245 : Blo 451781 1152245 := bbase (se 5 (by rfl) ⟨54011, by rfl⟩ : syracuseStep 1152245 = 108023) (by norm_num)
theorem B1021229 : Blo 451781 1021229 := bbase (se 3 (by rfl) ⟨191480, by rfl⟩ : syracuseStep 1021229 = 382961) (by norm_num)
theorem B1021301 : Blo 451781 1021301 := bbase (se 5 (by rfl) ⟨47873, by rfl⟩ : syracuseStep 1021301 = 95747) (by norm_num)
theorem B1021373 : Blo 451781 1021373 := bbase (se 3 (by rfl) ⟨191507, by rfl⟩ : syracuseStep 1021373 = 383015) (by norm_num)
theorem B1021445 : Blo 451781 1021445 := bbase (se 4 (by rfl) ⟨95760, by rfl⟩ : syracuseStep 1021445 = 191521) (by norm_num)
theorem B1447445 : Blo 451781 1447445 := bbase (se 6 (by rfl) ⟨33924, by rfl⟩ : syracuseStep 1447445 = 67849) (by norm_num)
theorem B1021517 : Blo 451781 1021517 := bbase (se 3 (by rfl) ⟨191534, by rfl⟩ : syracuseStep 1021517 = 383069) (by norm_num)
theorem B1152589 : Blo 451781 1152589 := bbase (se 3 (by rfl) ⟨216110, by rfl⟩ : syracuseStep 1152589 = 432221) (by norm_num)
theorem B1119853 : Blo 451781 1119853 := bbase (se 3 (by rfl) ⟨209972, by rfl⟩ : syracuseStep 1119853 = 419945) (by norm_num)
theorem B1021589 : Blo 451781 1021589 := bbase (se 6 (by rfl) ⟨23943, by rfl⟩ : syracuseStep 1021589 = 47887) (by norm_num)
theorem B1087141 : Blo 451781 1087141 := bbase (se 4 (by rfl) ⟨101919, by rfl⟩ : syracuseStep 1087141 = 203839) (by norm_num)
theorem B1152701 : Blo 451781 1152701 := bbase (se 3 (by rfl) ⟨216131, by rfl⟩ : syracuseStep 1152701 = 432263) (by norm_num)
theorem B2299589 : Blo 451781 2299589 := bbase (se 4 (by rfl) ⟨215586, by rfl⟩ : syracuseStep 2299589 = 431173) (by norm_num)
theorem B5183189 : Blo 451781 5183189 := bbase (se 7 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 5183189 = 121481) (by norm_num)
theorem B1021661 : Blo 451781 1021661 := bbase (se 3 (by rfl) ⟨191561, by rfl⟩ : syracuseStep 1021661 = 383123) (by norm_num)
theorem B628517 : Blo 451781 628517 := bbase (se 4 (by rfl) ⟨58923, by rfl⟩ : syracuseStep 628517 = 117847) (by norm_num)
theorem B1021733 : Blo 451781 1021733 := bbase (se 4 (by rfl) ⟨95787, by rfl⟩ : syracuseStep 1021733 = 191575) (by norm_num)
theorem B857965 : Blo 451781 857965 := bbase (se 3 (by rfl) ⟨160868, by rfl⟩ : syracuseStep 857965 = 321737) (by norm_num)
theorem B1021805 : Blo 451781 1021805 := bbase (se 3 (by rfl) ⟨191588, by rfl⟩ : syracuseStep 1021805 = 383177) (by norm_num)
theorem B2463605 : Blo 451781 2463605 := bbase (se 5 (by rfl) ⟨115481, by rfl⟩ : syracuseStep 2463605 = 230963) (by norm_num)
theorem B1152893 : Blo 451781 1152893 := bbase (se 3 (by rfl) ⟨216167, by rfl⟩ : syracuseStep 1152893 = 432335) (by norm_num)
theorem B726965 : Blo 451781 726965 := bbase (se 5 (by rfl) ⟨34076, by rfl⟩ : syracuseStep 726965 = 68153) (by norm_num)
theorem B1021877 : Blo 451781 1021877 := bbase (se 5 (by rfl) ⟨47900, by rfl⟩ : syracuseStep 1021877 = 95801) (by norm_num)
theorem B858109 : Blo 451781 858109 := bbase (se 3 (by rfl) ⟨160895, by rfl⟩ : syracuseStep 858109 = 321791) (by norm_num)
theorem B1021949 : Blo 451781 1021949 := bbase (se 3 (by rfl) ⟨191615, by rfl⟩ : syracuseStep 1021949 = 383231) (by norm_num)
theorem B1022021 : Blo 451781 1022021 := bbase (se 4 (by rfl) ⟨95814, by rfl⟩ : syracuseStep 1022021 = 191629) (by norm_num)
theorem B727157 : Blo 451781 727157 := bbase (se 5 (by rfl) ⟨34085, by rfl⟩ : syracuseStep 727157 = 68171) (by norm_num)
theorem B1022093 : Blo 451781 1022093 := bbase (se 3 (by rfl) ⟨191642, by rfl⟩ : syracuseStep 1022093 = 383285) (by norm_num)
theorem B858269 : Blo 451781 858269 := bbase (se 3 (by rfl) ⟨160925, by rfl⟩ : syracuseStep 858269 = 321851) (by norm_num)
theorem B1087661 : Blo 451781 1087661 := bbase (se 3 (by rfl) ⟨203936, by rfl⟩ : syracuseStep 1087661 = 407873) (by norm_num)
theorem B1022165 : Blo 451781 1022165 := bbase (se 7 (by rfl) ⟨11978, by rfl⟩ : syracuseStep 1022165 = 23957) (by norm_num)
theorem B1153237 : Blo 451781 1153237 := bbase (se 7 (by rfl) ⟨13514, by rfl⟩ : syracuseStep 1153237 = 27029) (by norm_num)
theorem B1939733 : Blo 451781 1939733 := bbase (se 6 (by rfl) ⟨45462, by rfl⟩ : syracuseStep 1939733 = 90925) (by norm_num)
theorem B1022237 : Blo 451781 1022237 := bbase (se 3 (by rfl) ⟨191669, by rfl⟩ : syracuseStep 1022237 = 383339) (by norm_num)
theorem B858413 : Blo 451781 858413 := bbase (se 3 (by rfl) ⟨160952, by rfl⟩ : syracuseStep 858413 = 321905) (by norm_num)
theorem B1153349 : Blo 451781 1153349 := bbase (se 4 (by rfl) ⟨108126, by rfl⟩ : syracuseStep 1153349 = 216253) (by norm_num)
theorem B1022309 : Blo 451781 1022309 := bbase (se 4 (by rfl) ⟨95841, by rfl⟩ : syracuseStep 1022309 = 191683) (by norm_num)
theorem B1841557 : Blo 451781 1841557 := bbase (se 6 (by rfl) ⟨43161, by rfl⟩ : syracuseStep 1841557 = 86323) (by norm_num)
theorem B1022381 : Blo 451781 1022381 := bbase (se 3 (by rfl) ⟨191696, by rfl⟩ : syracuseStep 1022381 = 383393) (by norm_num)
theorem B1022453 : Blo 451781 1022453 := bbase (se 5 (by rfl) ⟨47927, by rfl⟩ : syracuseStep 1022453 = 95855) (by norm_num)
theorem B1153541 : Blo 451781 1153541 := bbase (se 4 (by rfl) ⟨108144, by rfl⟩ : syracuseStep 1153541 = 216289) (by norm_num)
theorem B1088045 : Blo 451781 1088045 := bbase (se 3 (by rfl) ⟨204008, by rfl⟩ : syracuseStep 1088045 = 408017) (by norm_num)
theorem B1022525 : Blo 451781 1022525 := bbase (se 3 (by rfl) ⟨191723, by rfl⟩ : syracuseStep 1022525 = 383447) (by norm_num)
theorem B858701 : Blo 451781 858701 := bbase (se 3 (by rfl) ⟨161006, by rfl⟩ : syracuseStep 858701 = 322013) (by norm_num)
theorem B1088093 : Blo 451781 1088093 := bbase (se 3 (by rfl) ⟨204017, by rfl⟩ : syracuseStep 1088093 = 408035) (by norm_num)
theorem B1088101 : Blo 451781 1088101 := bbase (se 4 (by rfl) ⟨102009, by rfl⟩ : syracuseStep 1088101 = 204019) (by norm_num)
theorem B1022597 : Blo 451781 1022597 := bbase (se 4 (by rfl) ⟨95868, by rfl⟩ : syracuseStep 1022597 = 191737) (by norm_num)
theorem B465569 : Blo 451781 465569 := bbase (se 2 (by rfl) ⟨174588, by rfl⟩ : syracuseStep 465569 = 349177) (by norm_num)
theorem B1022669 : Blo 451781 1022669 := bbase (se 3 (by rfl) ⟨191750, by rfl⟩ : syracuseStep 1022669 = 383501) (by norm_num)
theorem B858853 : Blo 451781 858853 := bbase (se 4 (by rfl) ⟨80517, by rfl⟩ : syracuseStep 858853 = 161035) (by norm_num)
theorem B1022741 : Blo 451781 1022741 := bbase (se 6 (by rfl) ⟨23970, by rfl⟩ : syracuseStep 1022741 = 47941) (by norm_num)
theorem B1022813 : Blo 451781 1022813 := bbase (se 3 (by rfl) ⟨191777, by rfl⟩ : syracuseStep 1022813 = 383555) (by norm_num)
theorem B1022885 : Blo 451781 1022885 := bbase (se 4 (by rfl) ⟨95895, by rfl⟩ : syracuseStep 1022885 = 191791) (by norm_num)
theorem B2300885 : Blo 451781 2300885 := bbase (se 7 (by rfl) ⟨26963, by rfl⟩ : syracuseStep 2300885 = 53927) (by norm_num)
theorem B1022957 : Blo 451781 1022957 := bbase (se 3 (by rfl) ⟨191804, by rfl⟩ : syracuseStep 1022957 = 383609) (by norm_num)
theorem B859157 : Blo 451781 859157 := bbase (se 6 (by rfl) ⟨20136, by rfl⟩ : syracuseStep 859157 = 40273) (by norm_num)
theorem B1023029 : Blo 451781 1023029 := bbase (se 5 (by rfl) ⟨47954, by rfl⟩ : syracuseStep 1023029 = 95909) (by norm_num)
theorem B1023101 : Blo 451781 1023101 := bbase (se 3 (by rfl) ⟨191831, by rfl⟩ : syracuseStep 1023101 = 383663) (by norm_num)
theorem B1023173 : Blo 451781 1023173 := bbase (se 4 (by rfl) ⟨95922, by rfl⟩ : syracuseStep 1023173 = 191845) (by norm_num)
theorem B1023245 : Blo 451781 1023245 := bbase (se 3 (by rfl) ⟨191858, by rfl⟩ : syracuseStep 1023245 = 383717) (by norm_num)
theorem B23928149 : Blo 451781 23928149 := bbase (se 11 (by rfl) ⟨17525, by rfl⟩ : syracuseStep 23928149 = 35051) (by norm_num)
theorem B1023317 : Blo 451781 1023317 := bbase (se 11 (by rfl) ⟨749, by rfl⟩ : syracuseStep 1023317 = 1499) (by norm_num)
theorem B1842533 : Blo 451781 1842533 := bbase (se 4 (by rfl) ⟨172737, by rfl⟩ : syracuseStep 1842533 = 345475) (by norm_num)
theorem B1023389 : Blo 451781 1023389 := bbase (se 3 (by rfl) ⟨191885, by rfl⟩ : syracuseStep 1023389 = 383771) (by norm_num)
theorem B1023461 : Blo 451781 1023461 := bbase (se 4 (by rfl) ⟨95949, by rfl⟩ : syracuseStep 1023461 = 191899) (by norm_num)
theorem B1383941 : Blo 451781 1383941 := bbase (se 4 (by rfl) ⟨129744, by rfl⟩ : syracuseStep 1383941 = 259489) (by norm_num)
theorem B728605 : Blo 451781 728605 := bbase (se 3 (by rfl) ⟨136613, by rfl⟩ : syracuseStep 728605 = 273227) (by norm_num)
theorem B1023533 : Blo 451781 1023533 := bbase (se 3 (by rfl) ⟨191912, by rfl⟩ : syracuseStep 1023533 = 383825) (by norm_num)
theorem B1121861 : Blo 451781 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B1089101 : Blo 451781 1089101 := bbase (se 3 (by rfl) ⟨204206, by rfl⟩ : syracuseStep 1089101 = 408413) (by norm_num)
theorem B7347797 : Blo 451781 7347797 := bbase (se 8 (by rfl) ⟨43053, by rfl⟩ : syracuseStep 7347797 = 86107) (by norm_num)
theorem B1023605 : Blo 451781 1023605 := bbase (se 5 (by rfl) ⟨47981, by rfl⟩ : syracuseStep 1023605 = 95963) (by norm_num)
theorem B1023677 : Blo 451781 1023677 := bbase (se 3 (by rfl) ⟨191939, by rfl⟩ : syracuseStep 1023677 = 383879) (by norm_num)
theorem B1449701 : Blo 451781 1449701 := bbase (se 4 (by rfl) ⟨135909, by rfl⟩ : syracuseStep 1449701 = 271819) (by norm_num)
theorem B859909 : Blo 451781 859909 := bbase (se 4 (by rfl) ⟨80616, by rfl⟩ : syracuseStep 859909 = 161233) (by norm_num)
theorem B1023749 : Blo 451781 1023749 := bbase (se 4 (by rfl) ⟨95976, by rfl⟩ : syracuseStep 1023749 = 191953) (by norm_num)
theorem B1089293 : Blo 451781 1089293 := bbase (se 3 (by rfl) ⟨204242, by rfl⟩ : syracuseStep 1089293 = 408485) (by norm_num)
theorem B499469 : Blo 451781 499469 := bbase (se 3 (by rfl) ⟨93650, by rfl⟩ : syracuseStep 499469 = 187301) (by norm_num)
theorem B1023821 : Blo 451781 1023821 := bbase (se 3 (by rfl) ⟨191966, by rfl⟩ : syracuseStep 1023821 = 383933) (by norm_num)
theorem B860053 : Blo 451781 860053 := bbase (se 6 (by rfl) ⟨20157, by rfl⟩ : syracuseStep 860053 = 40315) (by norm_num)
theorem B1023893 : Blo 451781 1023893 := bbase (se 6 (by rfl) ⟨23997, by rfl⟩ : syracuseStep 1023893 = 47995) (by norm_num)
theorem B1023965 : Blo 451781 1023965 := bbase (se 3 (by rfl) ⟨191993, by rfl⟩ : syracuseStep 1023965 = 383987) (by norm_num)
theorem B1941509 : Blo 451781 1941509 := bbase (se 4 (by rfl) ⟨182016, by rfl⟩ : syracuseStep 1941509 = 364033) (by norm_num)
theorem B1024037 : Blo 451781 1024037 := bbase (se 4 (by rfl) ⟨96003, by rfl⟩ : syracuseStep 1024037 = 192007) (by norm_num)
theorem B860213 : Blo 451781 860213 := bbase (se 5 (by rfl) ⟨40322, by rfl⟩ : syracuseStep 860213 = 80645) (by norm_num)
theorem B1024109 : Blo 451781 1024109 := bbase (se 3 (by rfl) ⟨192020, by rfl⟩ : syracuseStep 1024109 = 384041) (by norm_num)
theorem B1024181 : Blo 451781 1024181 := bbase (se 5 (by rfl) ⟨48008, by rfl⟩ : syracuseStep 1024181 = 96017) (by norm_num)
theorem B860357 : Blo 451781 860357 := bbase (se 4 (by rfl) ⟨80658, by rfl⟩ : syracuseStep 860357 = 161317) (by norm_num)
theorem B2302181 : Blo 451781 2302181 := bbase (se 4 (by rfl) ⟨215829, by rfl⟩ : syracuseStep 2302181 = 431659) (by norm_num)
theorem B1024253 : Blo 451781 1024253 := bbase (se 3 (by rfl) ⟨192047, by rfl⟩ : syracuseStep 1024253 = 384095) (by norm_num)
theorem B3285269 : Blo 451781 3285269 := bbase (se 6 (by rfl) ⟨76998, by rfl⟩ : syracuseStep 3285269 = 153997) (by norm_num)
theorem B3449141 : Blo 451781 3449141 := bbase (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) (by norm_num)
theorem B1024325 : Blo 451781 1024325 := bbase (se 4 (by rfl) ⟨96030, by rfl⟩ : syracuseStep 1024325 = 192061) (by norm_num)
theorem B4366709 : Blo 451781 4366709 := bbase (se 5 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 4366709 = 409379) (by norm_num)
theorem B1024397 : Blo 451781 1024397 := bbase (se 3 (by rfl) ⟨192074, by rfl⟩ : syracuseStep 1024397 = 384149) (by norm_num)
theorem B1286549 : Blo 451781 1286549 := bbase (se 6 (by rfl) ⟨30153, by rfl⟩ : syracuseStep 1286549 = 60307) (by norm_num)
theorem B3350965 : Blo 451781 3350965 := bbase (se 5 (by rfl) ⟨157076, by rfl⟩ : syracuseStep 3350965 = 314153) (by norm_num)
theorem B1024469 : Blo 451781 1024469 := bbase (se 7 (by rfl) ⟨12005, by rfl⟩ : syracuseStep 1024469 = 24011) (by norm_num)
theorem B860645 : Blo 451781 860645 := bbase (se 4 (by rfl) ⟨80685, by rfl⟩ : syracuseStep 860645 = 161371) (by norm_num)
theorem B1024541 : Blo 451781 1024541 := bbase (se 3 (by rfl) ⟨192101, by rfl⟩ : syracuseStep 1024541 = 384203) (by norm_num)
theorem B1024613 : Blo 451781 1024613 := bbase (se 4 (by rfl) ⟨96057, by rfl⟩ : syracuseStep 1024613 = 192115) (by norm_num)
theorem B762493 : Blo 451781 762493 := bbase (se 3 (by rfl) ⟨142967, by rfl⟩ : syracuseStep 762493 = 285935) (by norm_num)
theorem B860797 : Blo 451781 860797 := bbase (se 3 (by rfl) ⟨161399, by rfl⟩ : syracuseStep 860797 = 322799) (by norm_num)
theorem B696973 : Blo 451781 696973 := bbase (se 3 (by rfl) ⟨130682, by rfl⟩ : syracuseStep 696973 = 261365) (by norm_num)
theorem B1024685 : Blo 451781 1024685 := bbase (se 3 (by rfl) ⟨192128, by rfl⟩ : syracuseStep 1024685 = 384257) (by norm_num)
theorem B762581 : Blo 451781 762581 := bbase (se 7 (by rfl) ⟨8936, by rfl⟩ : syracuseStep 762581 = 17873) (by norm_num)
theorem B1024757 : Blo 451781 1024757 := bbase (se 5 (by rfl) ⟨48035, by rfl⟩ : syracuseStep 1024757 = 96071) (by norm_num)
theorem B1024829 : Blo 451781 1024829 := bbase (se 3 (by rfl) ⟨192155, by rfl⟩ : syracuseStep 1024829 = 384311) (by norm_num)
theorem B762709 : Blo 451781 762709 := bbase (se 9 (by rfl) ⟨2234, by rfl⟩ : syracuseStep 762709 = 4469) (by norm_num)
theorem B1024901 : Blo 451781 1024901 := bbase (se 4 (by rfl) ⟨96084, by rfl⟩ : syracuseStep 1024901 = 192169) (by norm_num)
theorem B729989 : Blo 451781 729989 := bbase (se 4 (by rfl) ⟨68436, by rfl⟩ : syracuseStep 729989 = 136873) (by norm_num)
theorem B762797 : Blo 451781 762797 := bbase (se 3 (by rfl) ⟨143024, by rfl⟩ : syracuseStep 762797 = 286049) (by norm_num)
theorem B861101 : Blo 451781 861101 := bbase (se 3 (by rfl) ⟨161456, by rfl⟩ : syracuseStep 861101 = 322913) (by norm_num)
theorem B1024973 : Blo 451781 1024973 := bbase (se 3 (by rfl) ⟨192182, by rfl⟩ : syracuseStep 1024973 = 384365) (by norm_num)
theorem B1942501 : Blo 451781 1942501 := bbase (se 4 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 1942501 = 364219) (by norm_num)
theorem B1025045 : Blo 451781 1025045 := bbase (se 6 (by rfl) ⟨24024, by rfl⟩ : syracuseStep 1025045 = 48049) (by norm_num)
theorem B762925 : Blo 451781 762925 := bbase (se 3 (by rfl) ⟨143048, by rfl⟩ : syracuseStep 762925 = 286097) (by norm_num)
theorem B1025117 : Blo 451781 1025117 := bbase (se 3 (by rfl) ⟨192209, by rfl⟩ : syracuseStep 1025117 = 384419) (by norm_num)
theorem B763013 : Blo 451781 763013 := bbase (se 4 (by rfl) ⟨71532, by rfl⟩ : syracuseStep 763013 = 143065) (by norm_num)
theorem B1025189 : Blo 451781 1025189 := bbase (se 4 (by rfl) ⟨96111, by rfl⟩ : syracuseStep 1025189 = 192223) (by norm_num)
theorem B828613 : Blo 451781 828613 := bbase (se 4 (by rfl) ⟨77682, by rfl⟩ : syracuseStep 828613 = 155365) (by norm_num)
theorem B1025261 : Blo 451781 1025261 := bbase (se 3 (by rfl) ⟨192236, by rfl⟩ : syracuseStep 1025261 = 384473) (by norm_num)
theorem B763141 : Blo 451781 763141 := bbase (se 4 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 763141 = 143089) (by norm_num)
theorem B1025333 : Blo 451781 1025333 := bbase (se 5 (by rfl) ⟨48062, by rfl⟩ : syracuseStep 1025333 = 96125) (by norm_num)
theorem B763229 : Blo 451781 763229 := bbase (se 3 (by rfl) ⟨143105, by rfl⟩ : syracuseStep 763229 = 286211) (by norm_num)
theorem B1025405 : Blo 451781 1025405 := bbase (se 3 (by rfl) ⟨192263, by rfl⟩ : syracuseStep 1025405 = 384527) (by norm_num)
theorem B1025477 : Blo 451781 1025477 := bbase (se 4 (by rfl) ⟨96138, by rfl⟩ : syracuseStep 1025477 = 192277) (by norm_num)
theorem B763357 : Blo 451781 763357 := bbase (se 3 (by rfl) ⟨143129, by rfl⟩ : syracuseStep 763357 = 286259) (by norm_num)
theorem B2303477 : Blo 451781 2303477 := bbase (se 5 (by rfl) ⟨107975, by rfl⟩ : syracuseStep 2303477 = 215951) (by norm_num)
theorem B1287733 : Blo 451781 1287733 := bbase (se 5 (by rfl) ⟨60362, by rfl⟩ : syracuseStep 1287733 = 120725) (by norm_num)
theorem B763445 : Blo 451781 763445 := bbase (se 5 (by rfl) ⟨35786, by rfl⟩ : syracuseStep 763445 = 71573) (by norm_num)
theorem B2336309 : Blo 451781 2336309 := bbase (se 5 (by rfl) ⟨109514, by rfl⟩ : syracuseStep 2336309 = 219029) (by norm_num)
theorem B861853 : Blo 451781 861853 := bbase (se 3 (by rfl) ⟨161597, by rfl⟩ : syracuseStep 861853 = 323195) (by norm_num)
theorem B1091245 : Blo 451781 1091245 := bbase (se 3 (by rfl) ⟨204608, by rfl⟩ : syracuseStep 1091245 = 409217) (by norm_num)
theorem B763573 : Blo 451781 763573 := bbase (se 5 (by rfl) ⟨35792, by rfl⟩ : syracuseStep 763573 = 71585) (by norm_num)
theorem B1287893 : Blo 451781 1287893 := bbase (se 7 (by rfl) ⟨15092, by rfl⟩ : syracuseStep 1287893 = 30185) (by norm_num)
theorem B763661 : Blo 451781 763661 := bbase (se 3 (by rfl) ⟨143186, by rfl⟩ : syracuseStep 763661 = 286373) (by norm_num)
theorem B861997 : Blo 451781 861997 := bbase (se 3 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 861997 = 323249) (by norm_num)
theorem B1845125 : Blo 451781 1845125 := bbase (se 4 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 1845125 = 345961) (by norm_num)
theorem B763789 : Blo 451781 763789 := bbase (se 3 (by rfl) ⟨143210, by rfl⟩ : syracuseStep 763789 = 286421) (by norm_num)
theorem B1288133 : Blo 451781 1288133 := bbase (se 4 (by rfl) ⟨120762, by rfl⟩ : syracuseStep 1288133 = 241525) (by norm_num)
theorem B862157 : Blo 451781 862157 := bbase (se 3 (by rfl) ⟨161654, by rfl⟩ : syracuseStep 862157 = 323309) (by norm_num)
theorem B763877 : Blo 451781 763877 := bbase (se 4 (by rfl) ⟨71613, by rfl⟩ : syracuseStep 763877 = 143227) (by norm_num)
theorem B2173013 : Blo 451781 2173013 := bbase (se 8 (by rfl) ⟨12732, by rfl⟩ : syracuseStep 2173013 = 25465) (by norm_num)
theorem B862301 : Blo 451781 862301 := bbase (se 3 (by rfl) ⟨161681, by rfl⟩ : syracuseStep 862301 = 323363) (by norm_num)
theorem B764005 : Blo 451781 764005 := bbase (se 4 (by rfl) ⟨71625, by rfl⟩ : syracuseStep 764005 = 143251) (by norm_num)
theorem B829549 : Blo 451781 829549 := bbase (se 3 (by rfl) ⟨155540, by rfl⟩ : syracuseStep 829549 = 311081) (by norm_num)
theorem B1288325 : Blo 451781 1288325 := bbase (se 4 (by rfl) ⟨120780, by rfl⟩ : syracuseStep 1288325 = 241561) (by norm_num)
theorem B3582133 : Blo 451781 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B764093 : Blo 451781 764093 := bbase (se 3 (by rfl) ⟨143267, by rfl⟩ : syracuseStep 764093 = 286535) (by norm_num)
theorem B764221 : Blo 451781 764221 := bbase (se 3 (by rfl) ⟨143291, by rfl⟩ : syracuseStep 764221 = 286583) (by norm_num)
theorem B862589 : Blo 451781 862589 := bbase (se 3 (by rfl) ⟨161735, by rfl⟩ : syracuseStep 862589 = 323471) (by norm_num)
theorem B764309 : Blo 451781 764309 := bbase (se 6 (by rfl) ⟨17913, by rfl⟩ : syracuseStep 764309 = 35827) (by norm_num)
theorem B764437 : Blo 451781 764437 := bbase (se 6 (by rfl) ⟨17916, by rfl⟩ : syracuseStep 764437 = 35833) (by norm_num)
theorem B862741 : Blo 451781 862741 := bbase (se 6 (by rfl) ⟨20220, by rfl⟩ : syracuseStep 862741 = 40441) (by norm_num)
theorem B1092197 : Blo 451781 1092197 := bbase (se 4 (by rfl) ⟨102393, by rfl⟩ : syracuseStep 1092197 = 204787) (by norm_num)
theorem B764525 : Blo 451781 764525 := bbase (se 3 (by rfl) ⟨143348, by rfl⟩ : syracuseStep 764525 = 286697) (by norm_num)
theorem B1092253 : Blo 451781 1092253 := bbase (se 3 (by rfl) ⟨204797, by rfl⟩ : syracuseStep 1092253 = 409595) (by norm_num)
theorem B764653 : Blo 451781 764653 := bbase (se 3 (by rfl) ⟨143372, by rfl⟩ : syracuseStep 764653 = 286745) (by norm_num)
theorem B2304773 : Blo 451781 2304773 := bbase (se 4 (by rfl) ⟨216072, by rfl⟩ : syracuseStep 2304773 = 432145) (by norm_num)
theorem B764741 : Blo 451781 764741 := bbase (se 4 (by rfl) ⟨71694, by rfl⟩ : syracuseStep 764741 = 143389) (by norm_num)
theorem B863045 : Blo 451781 863045 := bbase (se 4 (by rfl) ⟨80910, by rfl⟩ : syracuseStep 863045 = 161821) (by norm_num)
theorem B764869 : Blo 451781 764869 := bbase (se 4 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 764869 = 143413) (by norm_num)
theorem B1092629 : Blo 451781 1092629 := bbase (se 6 (by rfl) ⟨25608, by rfl⟩ : syracuseStep 1092629 = 51217) (by norm_num)
theorem B764957 : Blo 451781 764957 := bbase (se 3 (by rfl) ⟨143429, by rfl⟩ : syracuseStep 764957 = 286859) (by norm_num)
theorem B7842901 : Blo 451781 7842901 := bbase (se 8 (by rfl) ⟨45954, by rfl⟩ : syracuseStep 7842901 = 91909) (by norm_num)
theorem B1289317 : Blo 451781 1289317 := bbase (se 4 (by rfl) ⟨120873, by rfl⟩ : syracuseStep 1289317 = 241747) (by norm_num)
theorem B765085 : Blo 451781 765085 := bbase (se 3 (by rfl) ⟨143453, by rfl⟩ : syracuseStep 765085 = 286907) (by norm_num)
theorem B765173 : Blo 451781 765173 := bbase (se 5 (by rfl) ⟨35867, by rfl⟩ : syracuseStep 765173 = 71735) (by norm_num)
theorem B1092869 : Blo 451781 1092869 := bbase (se 4 (by rfl) ⟨102456, by rfl⟩ : syracuseStep 1092869 = 204913) (by norm_num)
theorem B5680469 : Blo 451781 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B765301 : Blo 451781 765301 := bbase (se 5 (by rfl) ⟨35873, by rfl⟩ : syracuseStep 765301 = 71747) (by norm_num)
theorem B2174357 : Blo 451781 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B765389 : Blo 451781 765389 := bbase (se 3 (by rfl) ⟨143510, by rfl⟩ : syracuseStep 765389 = 287021) (by norm_num)
theorem B1715701 : Blo 451781 1715701 := bbase (se 5 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 1715701 = 160847) (by norm_num)
theorem B1453621 : Blo 451781 1453621 := bbase (se 5 (by rfl) ⟨68138, by rfl⟩ : syracuseStep 1453621 = 136277) (by norm_num)
theorem B863797 : Blo 451781 863797 := bbase (se 5 (by rfl) ⟨40490, by rfl⟩ : syracuseStep 863797 = 80981) (by norm_num)
theorem B765517 : Blo 451781 765517 := bbase (se 3 (by rfl) ⟨143534, by rfl⟩ : syracuseStep 765517 = 287069) (by norm_num)
theorem B765605 : Blo 451781 765605 := bbase (se 4 (by rfl) ⟨71775, by rfl⟩ : syracuseStep 765605 = 143551) (by norm_num)
theorem B863941 : Blo 451781 863941 := bbase (se 4 (by rfl) ⟨80994, by rfl⟩ : syracuseStep 863941 = 161989) (by norm_num)
theorem B1716005 : Blo 451781 1716005 := bbase (se 4 (by rfl) ⟨160875, by rfl⟩ : syracuseStep 1716005 = 321751) (by norm_num)
theorem B765733 : Blo 451781 765733 := bbase (se 4 (by rfl) ⟨71787, by rfl⟩ : syracuseStep 765733 = 143575) (by norm_num)
theorem B1453877 : Blo 451781 1453877 := bbase (se 5 (by rfl) ⟨68150, by rfl⟩ : syracuseStep 1453877 = 136301) (by norm_num)
theorem B864101 : Blo 451781 864101 := bbase (se 4 (by rfl) ⟨81009, by rfl⟩ : syracuseStep 864101 = 162019) (by norm_num)
theorem B765821 : Blo 451781 765821 := bbase (se 3 (by rfl) ⟨143591, by rfl⟩ : syracuseStep 765821 = 287183) (by norm_num)
theorem B864245 : Blo 451781 864245 := bbase (se 5 (by rfl) ⟨40511, by rfl⟩ : syracuseStep 864245 = 81023) (by norm_num)
theorem B765949 : Blo 451781 765949 := bbase (se 3 (by rfl) ⟨143615, by rfl⟩ : syracuseStep 765949 = 287231) (by norm_num)
theorem B2306069 : Blo 451781 2306069 := bbase (se 6 (by rfl) ⟨54048, by rfl⟩ : syracuseStep 2306069 = 108097) (by norm_num)
theorem B766037 : Blo 451781 766037 := bbase (se 8 (by rfl) ⟨4488, by rfl⟩ : syracuseStep 766037 = 8977) (by norm_num)
theorem B831653 : Blo 451781 831653 := bbase (se 4 (by rfl) ⟨77967, by rfl⟩ : syracuseStep 831653 = 155935) (by norm_num)
theorem B1847461 : Blo 451781 1847461 := bbase (se 4 (by rfl) ⟨173199, by rfl⟩ : syracuseStep 1847461 = 346399) (by norm_num)
theorem B1290421 : Blo 451781 1290421 := bbase (se 5 (by rfl) ⟨60488, by rfl⟩ : syracuseStep 1290421 = 120977) (by norm_num)
theorem B766165 : Blo 451781 766165 := bbase (se 7 (by rfl) ⟨8978, by rfl⟩ : syracuseStep 766165 = 17957) (by norm_num)
theorem B864533 : Blo 451781 864533 := bbase (se 6 (by rfl) ⟨20262, by rfl⟩ : syracuseStep 864533 = 40525) (by norm_num)
theorem B766253 : Blo 451781 766253 := bbase (se 3 (by rfl) ⟨143672, by rfl⟩ : syracuseStep 766253 = 287345) (by norm_num)
theorem B766381 : Blo 451781 766381 := bbase (se 3 (by rfl) ⟨143696, by rfl⟩ : syracuseStep 766381 = 287393) (by norm_num)
theorem B864685 : Blo 451781 864685 := bbase (se 3 (by rfl) ⟨162128, by rfl⟩ : syracuseStep 864685 = 324257) (by norm_num)
theorem B766469 : Blo 451781 766469 := bbase (se 4 (by rfl) ⟨71856, by rfl⟩ : syracuseStep 766469 = 143713) (by norm_num)
theorem B766597 : Blo 451781 766597 := bbase (se 4 (by rfl) ⟨71868, by rfl⟩ : syracuseStep 766597 = 143737) (by norm_num)
theorem B1159901 : Blo 451781 1159901 := bbase (se 3 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 1159901 = 434963) (by norm_num)
theorem B766685 : Blo 451781 766685 := bbase (se 3 (by rfl) ⟨143753, by rfl⟩ : syracuseStep 766685 = 287507) (by norm_num)
theorem B864989 : Blo 451781 864989 := bbase (se 3 (by rfl) ⟨162185, by rfl⟩ : syracuseStep 864989 = 324371) (by norm_num)
theorem B996085 : Blo 451781 996085 := bbase (se 5 (by rfl) ⟨46691, by rfl⟩ : syracuseStep 996085 = 93383) (by norm_num)
theorem B2175781 : Blo 451781 2175781 := bbase (se 4 (by rfl) ⟨203979, by rfl⟩ : syracuseStep 2175781 = 407959) (by norm_num)
theorem B766813 : Blo 451781 766813 := bbase (se 3 (by rfl) ⟨143777, by rfl⟩ : syracuseStep 766813 = 287555) (by norm_num)
theorem B766901 : Blo 451781 766901 := bbase (se 5 (by rfl) ⟨35948, by rfl⟩ : syracuseStep 766901 = 71897) (by norm_num)
theorem B767029 : Blo 451781 767029 := bbase (se 5 (by rfl) ⟨35954, by rfl⟩ : syracuseStep 767029 = 71909) (by norm_num)
theorem B767117 : Blo 451781 767117 := bbase (se 3 (by rfl) ⟨143834, by rfl⟩ : syracuseStep 767117 = 287669) (by norm_num)
theorem B767245 : Blo 451781 767245 := bbase (se 3 (by rfl) ⟨143858, by rfl⟩ : syracuseStep 767245 = 287717) (by norm_num)
theorem B2307365 : Blo 451781 2307365 := bbase (se 4 (by rfl) ⟨216315, by rfl⟩ : syracuseStep 2307365 = 432631) (by norm_num)
theorem B767333 : Blo 451781 767333 := bbase (se 4 (by rfl) ⟨71937, by rfl⟩ : syracuseStep 767333 = 143875) (by norm_num)
theorem B3716533 : Blo 451781 3716533 := bbase (se 5 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 3716533 = 348425) (by norm_num)
theorem B767461 : Blo 451781 767461 := bbase (se 4 (by rfl) ⟨71949, by rfl⟩ : syracuseStep 767461 = 143899) (by norm_num)
theorem B767549 : Blo 451781 767549 := bbase (se 3 (by rfl) ⟨143915, by rfl⟩ : syracuseStep 767549 = 287831) (by norm_num)
theorem B1291925 : Blo 451781 1291925 := bbase (se 6 (by rfl) ⟨30279, by rfl⟩ : syracuseStep 1291925 = 60559) (by norm_num)
theorem B767677 : Blo 451781 767677 := bbase (se 3 (by rfl) ⟨143939, by rfl⟩ : syracuseStep 767677 = 287879) (by norm_num)
theorem B767765 : Blo 451781 767765 := bbase (se 6 (by rfl) ⟨17994, by rfl⟩ : syracuseStep 767765 = 35989) (by norm_num)
theorem B1718117 : Blo 451781 1718117 := bbase (se 4 (by rfl) ⟨161073, by rfl⟩ : syracuseStep 1718117 = 322147) (by norm_num)
theorem B767893 : Blo 451781 767893 := bbase (se 6 (by rfl) ⟨17997, by rfl⟩ : syracuseStep 767893 = 35995) (by norm_num)
theorem B767981 : Blo 451781 767981 := bbase (se 3 (by rfl) ⟨143996, by rfl⟩ : syracuseStep 767981 = 287993) (by norm_num)
theorem B768109 : Blo 451781 768109 := bbase (se 3 (by rfl) ⟨144020, by rfl⟩ : syracuseStep 768109 = 288041) (by norm_num)
theorem B1718405 : Blo 451781 1718405 := bbase (se 4 (by rfl) ⟨161100, by rfl⟩ : syracuseStep 1718405 = 322201) (by norm_num)
theorem B768197 : Blo 451781 768197 := bbase (se 4 (by rfl) ⟨72018, by rfl⟩ : syracuseStep 768197 = 144037) (by norm_num)
theorem B768325 : Blo 451781 768325 := bbase (se 4 (by rfl) ⟨72030, by rfl⟩ : syracuseStep 768325 = 144061) (by norm_num)
theorem B571789 : Blo 451781 571789 := bbase (se 3 (by rfl) ⟨107210, by rfl⟩ : syracuseStep 571789 = 214421) (by norm_num)
theorem B768413 : Blo 451781 768413 := bbase (se 3 (by rfl) ⟨144077, by rfl⟩ : syracuseStep 768413 = 288155) (by norm_num)
theorem B965117 : Blo 451781 965117 := bbase (se 3 (by rfl) ⟨180959, by rfl⟩ : syracuseStep 965117 = 361919) (by norm_num)
theorem B1456645 : Blo 451781 1456645 := bbase (se 4 (by rfl) ⟨136560, by rfl⟩ : syracuseStep 1456645 = 273121) (by norm_num)
theorem B768541 : Blo 451781 768541 := bbase (se 3 (by rfl) ⟨144101, by rfl⟩ : syracuseStep 768541 = 288203) (by norm_num)
theorem B571961 : Blo 451781 571961 := bbase (se 2 (by rfl) ⟨214485, by rfl⟩ : syracuseStep 571961 = 428971) (by norm_num)
theorem B572017 : Blo 451781 572017 := bbase (se 2 (by rfl) ⟨214506, by rfl⟩ : syracuseStep 572017 = 429013) (by norm_num)
theorem B768629 : Blo 451781 768629 := bbase (se 5 (by rfl) ⟨36029, by rfl⟩ : syracuseStep 768629 = 72059) (by norm_num)
theorem B572113 : Blo 451781 572113 := bbase (se 2 (by rfl) ⟨214542, by rfl⟩ : syracuseStep 572113 = 429085) (by norm_num)
theorem B1030877 : Blo 451781 1030877 := bbase (se 3 (by rfl) ⟨193289, by rfl⟩ : syracuseStep 1030877 = 386579) (by norm_num)
theorem B768757 : Blo 451781 768757 := bbase (se 5 (by rfl) ⟨36035, by rfl⟩ : syracuseStep 768757 = 72071) (by norm_num)
theorem B768845 : Blo 451781 768845 := bbase (se 3 (by rfl) ⟨144158, by rfl⟩ : syracuseStep 768845 = 288317) (by norm_num)
theorem B572285 : Blo 451781 572285 := bbase (se 3 (by rfl) ⟨107303, by rfl⟩ : syracuseStep 572285 = 214607) (by norm_num)
theorem B572341 : Blo 451781 572341 := bbase (se 5 (by rfl) ⟨26828, by rfl⟩ : syracuseStep 572341 = 53657) (by norm_num)
theorem B768973 : Blo 451781 768973 := bbase (se 3 (by rfl) ⟨144182, by rfl⟩ : syracuseStep 768973 = 288365) (by norm_num)
theorem B965621 : Blo 451781 965621 := bbase (se 5 (by rfl) ⟨45263, by rfl⟩ : syracuseStep 965621 = 90527) (by norm_num)
theorem B965629 : Blo 451781 965629 := bbase (se 3 (by rfl) ⟨181055, by rfl⟩ : syracuseStep 965629 = 362111) (by norm_num)
theorem B572437 : Blo 451781 572437 := bbase (se 6 (by rfl) ⟨13416, by rfl⟩ : syracuseStep 572437 = 26833) (by norm_num)
theorem B769061 : Blo 451781 769061 := bbase (se 4 (by rfl) ⟨72099, by rfl⟩ : syracuseStep 769061 = 144199) (by norm_num)
theorem B572609 : Blo 451781 572609 := bbase (se 2 (by rfl) ⟨214728, by rfl⟩ : syracuseStep 572609 = 429457) (by norm_num)
theorem B1293509 : Blo 451781 1293509 := bbase (se 4 (by rfl) ⟨121266, by rfl⟩ : syracuseStep 1293509 = 242533) (by norm_num)
theorem B572665 : Blo 451781 572665 := bbase (se 2 (by rfl) ⟨214749, by rfl⟩ : syracuseStep 572665 = 429499) (by norm_num)
theorem B1719589 : Blo 451781 1719589 := bbase (se 4 (by rfl) ⟨161211, by rfl⟩ : syracuseStep 1719589 = 322423) (by norm_num)
theorem B572761 : Blo 451781 572761 := bbase (se 2 (by rfl) ⟨214785, by rfl⟩ : syracuseStep 572761 = 429571) (by norm_num)
theorem B572933 : Blo 451781 572933 := bbase (se 4 (by rfl) ⟨53712, by rfl⟩ : syracuseStep 572933 = 107425) (by norm_num)
theorem B572989 : Blo 451781 572989 := bbase (se 3 (by rfl) ⟨107435, by rfl⟩ : syracuseStep 572989 = 214871) (by norm_num)
theorem B1719893 : Blo 451781 1719893 := bbase (se 8 (by rfl) ⟨10077, by rfl⟩ : syracuseStep 1719893 = 20155) (by norm_num)
theorem B573085 : Blo 451781 573085 := bbase (se 3 (by rfl) ⟨107453, by rfl⟩ : syracuseStep 573085 = 214907) (by norm_num)
theorem B1228517 : Blo 451781 1228517 := bbase (se 4 (by rfl) ⟨115173, by rfl⟩ : syracuseStep 1228517 = 230347) (by norm_num)
theorem B573257 : Blo 451781 573257 := bbase (se 2 (by rfl) ⟨214971, by rfl⟩ : syracuseStep 573257 = 429943) (by norm_num)
theorem B3358549 : Blo 451781 3358549 := bbase (se 9 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 3358549 = 19679) (by norm_num)
theorem B1294181 : Blo 451781 1294181 := bbase (se 4 (by rfl) ⟨121329, by rfl⟩ : syracuseStep 1294181 = 242659) (by norm_num)
theorem B573313 : Blo 451781 573313 := bbase (se 2 (by rfl) ⟨214992, by rfl⟩ : syracuseStep 573313 = 429985) (by norm_num)
theorem B3456917 : Blo 451781 3456917 := bbase (se 6 (by rfl) ⟨81021, by rfl⟩ : syracuseStep 3456917 = 162043) (by norm_num)
theorem B573409 : Blo 451781 573409 := bbase (se 2 (by rfl) ⟨215028, by rfl⟩ : syracuseStep 573409 = 430057) (by norm_num)
theorem B966757 : Blo 451781 966757 := bbase (se 4 (by rfl) ⟨90633, by rfl⟩ : syracuseStep 966757 = 181267) (by norm_num)
theorem B573581 : Blo 451781 573581 := bbase (se 3 (by rfl) ⟨107546, by rfl⟩ : syracuseStep 573581 = 215093) (by norm_num)
theorem B573637 : Blo 451781 573637 := bbase (se 4 (by rfl) ⟨53778, by rfl⟩ : syracuseStep 573637 = 107557) (by norm_num)
theorem B1294613 : Blo 451781 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B573733 : Blo 451781 573733 := bbase (se 4 (by rfl) ⟨53787, by rfl⟩ : syracuseStep 573733 = 107575) (by norm_num)
theorem B508261 : Blo 451781 508261 := bbase (se 4 (by rfl) ⟨47649, by rfl⟩ : syracuseStep 508261 = 95299) (by norm_num)
theorem B508297 : Blo 451781 508297 := bbase (se 2 (by rfl) ⟨190611, by rfl⟩ : syracuseStep 508297 = 381223) (by norm_num)
theorem B508333 : Blo 451781 508333 := bbase (se 3 (by rfl) ⟨95312, by rfl⟩ : syracuseStep 508333 = 190625) (by norm_num)
theorem B508369 : Blo 451781 508369 := bbase (se 2 (by rfl) ⟨190638, by rfl⟩ : syracuseStep 508369 = 381277) (by norm_num)
theorem B573905 : Blo 451781 573905 := bbase (se 2 (by rfl) ⟨215214, by rfl⟩ : syracuseStep 573905 = 430429) (by norm_num)
theorem B967133 : Blo 451781 967133 := bbase (se 3 (by rfl) ⟨181337, by rfl⟩ : syracuseStep 967133 = 362675) (by norm_num)
theorem B508405 : Blo 451781 508405 := bbase (se 5 (by rfl) ⟨23831, by rfl⟩ : syracuseStep 508405 = 47663) (by norm_num)
theorem B573961 : Blo 451781 573961 := bbase (se 2 (by rfl) ⟨215235, by rfl⟩ : syracuseStep 573961 = 430471) (by norm_num)
theorem B508441 : Blo 451781 508441 := bbase (se 2 (by rfl) ⟨190665, by rfl⟩ : syracuseStep 508441 = 381331) (by norm_num)
theorem B508477 : Blo 451781 508477 := bbase (se 3 (by rfl) ⟨95339, by rfl⟩ : syracuseStep 508477 = 190679) (by norm_num)
theorem B508513 : Blo 451781 508513 := bbase (se 2 (by rfl) ⟨190692, by rfl⟩ : syracuseStep 508513 = 381385) (by norm_num)
theorem B1229413 : Blo 451781 1229413 := bbase (se 4 (by rfl) ⟨115257, by rfl⟩ : syracuseStep 1229413 = 230515) (by norm_num)
theorem B574057 : Blo 451781 574057 := bbase (se 2 (by rfl) ⟨215271, by rfl⟩ : syracuseStep 574057 = 430543) (by norm_num)
theorem B508549 : Blo 451781 508549 := bbase (se 4 (by rfl) ⟨47676, by rfl⟩ : syracuseStep 508549 = 95353) (by norm_num)
theorem B508585 : Blo 451781 508585 := bbase (se 2 (by rfl) ⟨190719, by rfl⟩ : syracuseStep 508585 = 381439) (by norm_num)
theorem B508621 : Blo 451781 508621 := bbase (se 3 (by rfl) ⟨95366, by rfl⟩ : syracuseStep 508621 = 190733) (by norm_num)
theorem B508657 : Blo 451781 508657 := bbase (se 2 (by rfl) ⟨190746, by rfl⟩ : syracuseStep 508657 = 381493) (by norm_num)
theorem B508693 : Blo 451781 508693 := bbase (se 6 (by rfl) ⟨11922, by rfl⟩ : syracuseStep 508693 = 23845) (by norm_num)
theorem B574229 : Blo 451781 574229 := bbase (se 6 (by rfl) ⟨13458, by rfl⟩ : syracuseStep 574229 = 26917) (by norm_num)
theorem B1033013 : Blo 451781 1033013 := bbase (se 5 (by rfl) ⟨48422, by rfl⟩ : syracuseStep 1033013 = 96845) (by norm_num)
theorem B508729 : Blo 451781 508729 := bbase (se 2 (by rfl) ⟨190773, by rfl⟩ : syracuseStep 508729 = 381547) (by norm_num)
theorem B574285 : Blo 451781 574285 := bbase (se 3 (by rfl) ⟨107678, by rfl⟩ : syracuseStep 574285 = 215357) (by norm_num)
theorem B508765 : Blo 451781 508765 := bbase (se 3 (by rfl) ⟨95393, by rfl⟩ : syracuseStep 508765 = 190787) (by norm_num)
theorem B508801 : Blo 451781 508801 := bbase (se 2 (by rfl) ⟨190800, by rfl⟩ : syracuseStep 508801 = 381601) (by norm_num)
theorem B508837 : Blo 451781 508837 := bbase (se 4 (by rfl) ⟨47703, by rfl⟩ : syracuseStep 508837 = 95407) (by norm_num)
theorem B574381 : Blo 451781 574381 := bbase (se 3 (by rfl) ⟨107696, by rfl⟩ : syracuseStep 574381 = 215393) (by norm_num)
theorem B508873 : Blo 451781 508873 := bbase (se 2 (by rfl) ⟨190827, by rfl⟩ : syracuseStep 508873 = 381655) (by norm_num)
theorem B836573 : Blo 451781 836573 := bbase (se 3 (by rfl) ⟨156857, by rfl⟩ : syracuseStep 836573 = 313715) (by norm_num)
theorem B508909 : Blo 451781 508909 := bbase (se 3 (by rfl) ⟨95420, by rfl⟩ : syracuseStep 508909 = 190841) (by norm_num)
theorem B1295365 : Blo 451781 1295365 := bbase (se 4 (by rfl) ⟨121440, by rfl⟩ : syracuseStep 1295365 = 242881) (by norm_num)
theorem B508945 : Blo 451781 508945 := bbase (se 2 (by rfl) ⟨190854, by rfl⟩ : syracuseStep 508945 = 381709) (by norm_num)
theorem B508981 : Blo 451781 508981 := bbase (se 5 (by rfl) ⟨23858, by rfl⟩ : syracuseStep 508981 = 47717) (by norm_num)
theorem B509017 : Blo 451781 509017 := bbase (se 2 (by rfl) ⟨190881, by rfl⟩ : syracuseStep 509017 = 381763) (by norm_num)
theorem B574553 : Blo 451781 574553 := bbase (se 2 (by rfl) ⟨215457, by rfl⟩ : syracuseStep 574553 = 430915) (by norm_num)
theorem B509053 : Blo 451781 509053 := bbase (se 3 (by rfl) ⟨95447, by rfl⟩ : syracuseStep 509053 = 190895) (by norm_num)
theorem B574609 : Blo 451781 574609 := bbase (se 2 (by rfl) ⟨215478, by rfl⟩ : syracuseStep 574609 = 430957) (by norm_num)
theorem B509089 : Blo 451781 509089 := bbase (se 2 (by rfl) ⟨190908, by rfl⟩ : syracuseStep 509089 = 381817) (by norm_num)
theorem B509125 : Blo 451781 509125 := bbase (se 4 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 509125 = 95461) (by norm_num)
theorem B1557701 : Blo 451781 1557701 := bbase (se 4 (by rfl) ⟨146034, by rfl⟩ : syracuseStep 1557701 = 292069) (by norm_num)
theorem B509161 : Blo 451781 509161 := bbase (se 2 (by rfl) ⟨190935, by rfl⟩ : syracuseStep 509161 = 381871) (by norm_num)
theorem B574705 : Blo 451781 574705 := bbase (se 2 (by rfl) ⟨215514, by rfl⟩ : syracuseStep 574705 = 431029) (by norm_num)
theorem B509197 : Blo 451781 509197 := bbase (se 3 (by rfl) ⟨95474, by rfl⟩ : syracuseStep 509197 = 190949) (by norm_num)
theorem B1525013 : Blo 451781 1525013 := bbase (se 6 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 1525013 = 71485) (by norm_num)
theorem B509233 : Blo 451781 509233 := bbase (se 2 (by rfl) ⟨190962, by rfl⟩ : syracuseStep 509233 = 381925) (by norm_num)
theorem B509269 : Blo 451781 509269 := bbase (se 12 (by rfl) ⟨186, by rfl⟩ : syracuseStep 509269 = 373) (by norm_num)
theorem B509305 : Blo 451781 509305 := bbase (se 2 (by rfl) ⟨190989, by rfl⟩ : syracuseStep 509305 = 381979) (by norm_num)
theorem B509341 : Blo 451781 509341 := bbase (se 3 (by rfl) ⟨95501, by rfl⟩ : syracuseStep 509341 = 191003) (by norm_num)
theorem B574877 : Blo 451781 574877 := bbase (se 3 (by rfl) ⟨107789, by rfl⟩ : syracuseStep 574877 = 215579) (by norm_num)
theorem B509377 : Blo 451781 509377 := bbase (se 2 (by rfl) ⟨191016, by rfl⟩ : syracuseStep 509377 = 382033) (by norm_num)
theorem B574933 : Blo 451781 574933 := bbase (se 7 (by rfl) ⟨6737, by rfl⟩ : syracuseStep 574933 = 13475) (by norm_num)
theorem B509413 : Blo 451781 509413 := bbase (se 4 (by rfl) ⟨47757, by rfl⟩ : syracuseStep 509413 = 95515) (by norm_num)
theorem B509449 : Blo 451781 509449 := bbase (se 2 (by rfl) ⟨191043, by rfl⟩ : syracuseStep 509449 = 382087) (by norm_num)
theorem B2180645 : Blo 451781 2180645 := bbase (se 4 (by rfl) ⟨204435, by rfl⟩ : syracuseStep 2180645 = 408871) (by norm_num)
theorem B509485 : Blo 451781 509485 := bbase (se 3 (by rfl) ⟨95528, by rfl⟩ : syracuseStep 509485 = 191057) (by norm_num)
theorem B575029 : Blo 451781 575029 := bbase (se 5 (by rfl) ⟨26954, by rfl⟩ : syracuseStep 575029 = 53909) (by norm_num)
theorem B509521 : Blo 451781 509521 := bbase (se 2 (by rfl) ⟨191070, by rfl⟩ : syracuseStep 509521 = 382141) (by norm_num)
theorem B509557 : Blo 451781 509557 := bbase (se 5 (by rfl) ⟨23885, by rfl⟩ : syracuseStep 509557 = 47771) (by norm_num)
theorem B1722005 : Blo 451781 1722005 := bbase (se 6 (by rfl) ⟨40359, by rfl⟩ : syracuseStep 1722005 = 80719) (by norm_num)
theorem B509593 : Blo 451781 509593 := bbase (se 2 (by rfl) ⟨191097, by rfl⟩ : syracuseStep 509593 = 382195) (by norm_num)
theorem B509629 : Blo 451781 509629 := bbase (se 3 (by rfl) ⟨95555, by rfl⟩ : syracuseStep 509629 = 191111) (by norm_num)
theorem B1525445 : Blo 451781 1525445 := bbase (se 4 (by rfl) ⟨143010, by rfl⟩ : syracuseStep 1525445 = 286021) (by norm_num)
theorem B509665 : Blo 451781 509665 := bbase (se 2 (by rfl) ⟨191124, by rfl⟩ : syracuseStep 509665 = 382249) (by norm_num)
theorem B575201 : Blo 451781 575201 := bbase (se 2 (by rfl) ⟨215700, by rfl⟩ : syracuseStep 575201 = 431401) (by norm_num)
theorem B509701 : Blo 451781 509701 := bbase (se 4 (by rfl) ⟨47784, by rfl⟩ : syracuseStep 509701 = 95569) (by norm_num)
theorem B575257 : Blo 451781 575257 := bbase (se 2 (by rfl) ⟨215721, by rfl⟩ : syracuseStep 575257 = 431443) (by norm_num)
theorem B509737 : Blo 451781 509737 := bbase (se 2 (by rfl) ⟨191151, by rfl⟩ : syracuseStep 509737 = 382303) (by norm_num)
theorem B1165117 : Blo 451781 1165117 := bbase (se 3 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 1165117 = 436919) (by norm_num)
theorem B509773 : Blo 451781 509773 := bbase (se 3 (by rfl) ⟨95582, by rfl⟩ : syracuseStep 509773 = 191165) (by norm_num)
theorem B509809 : Blo 451781 509809 := bbase (se 2 (by rfl) ⟨191178, by rfl⟩ : syracuseStep 509809 = 382357) (by norm_num)
theorem B575353 : Blo 451781 575353 := bbase (se 2 (by rfl) ⟨215757, by rfl⟩ : syracuseStep 575353 = 431515) (by norm_num)
theorem B509845 : Blo 451781 509845 := bbase (se 6 (by rfl) ⟨11949, by rfl⟩ : syracuseStep 509845 = 23899) (by norm_num)
theorem B1722293 : Blo 451781 1722293 := bbase (se 5 (by rfl) ⟨80732, by rfl⟩ : syracuseStep 1722293 = 161465) (by norm_num)
theorem B509881 : Blo 451781 509881 := bbase (se 2 (by rfl) ⟨191205, by rfl⟩ : syracuseStep 509881 = 382411) (by norm_num)
theorem B509917 : Blo 451781 509917 := bbase (se 3 (by rfl) ⟨95609, by rfl⟩ : syracuseStep 509917 = 191219) (by norm_num)
theorem B509953 : Blo 451781 509953 := bbase (se 2 (by rfl) ⟨191232, by rfl⟩ : syracuseStep 509953 = 382465) (by norm_num)
theorem B509989 : Blo 451781 509989 := bbase (se 4 (by rfl) ⟨47811, by rfl⟩ : syracuseStep 509989 = 95623) (by norm_num)
theorem B575525 : Blo 451781 575525 := bbase (se 4 (by rfl) ⟨53955, by rfl⟩ : syracuseStep 575525 = 107911) (by norm_num)
theorem B968773 : Blo 451781 968773 := bbase (se 4 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 968773 = 181645) (by norm_num)
theorem B510025 : Blo 451781 510025 := bbase (se 2 (by rfl) ⟨191259, by rfl⟩ : syracuseStep 510025 = 382519) (by norm_num)
theorem B575581 : Blo 451781 575581 := bbase (se 3 (by rfl) ⟨107921, by rfl⟩ : syracuseStep 575581 = 215843) (by norm_num)
theorem B510061 : Blo 451781 510061 := bbase (se 3 (by rfl) ⟨95636, by rfl⟩ : syracuseStep 510061 = 191273) (by norm_num)
theorem B1525877 : Blo 451781 1525877 := bbase (se 5 (by rfl) ⟨71525, by rfl⟩ : syracuseStep 1525877 = 143051) (by norm_num)
theorem B510097 : Blo 451781 510097 := bbase (se 2 (by rfl) ⟨191286, by rfl⟩ : syracuseStep 510097 = 382573) (by norm_num)
theorem B3885205 : Blo 451781 3885205 := bbase (se 6 (by rfl) ⟨91059, by rfl⟩ : syracuseStep 3885205 = 182119) (by norm_num)
theorem B510133 : Blo 451781 510133 := bbase (se 5 (by rfl) ⟨23912, by rfl⟩ : syracuseStep 510133 = 47825) (by norm_num)
theorem B575677 : Blo 451781 575677 := bbase (se 3 (by rfl) ⟨107939, by rfl⟩ : syracuseStep 575677 = 215879) (by norm_num)
theorem B1034453 : Blo 451781 1034453 := bbase (se 7 (by rfl) ⟨12122, by rfl⟩ : syracuseStep 1034453 = 24245) (by norm_num)
theorem B510169 : Blo 451781 510169 := bbase (se 2 (by rfl) ⟨191313, by rfl⟩ : syracuseStep 510169 = 382627) (by norm_num)
theorem B510205 : Blo 451781 510205 := bbase (se 3 (by rfl) ⟨95663, by rfl⟩ : syracuseStep 510205 = 191327) (by norm_num)
theorem B510241 : Blo 451781 510241 := bbase (se 2 (by rfl) ⟨191340, by rfl⟩ : syracuseStep 510241 = 382681) (by norm_num)
theorem B510277 : Blo 451781 510277 := bbase (se 4 (by rfl) ⟨47838, by rfl⟩ : syracuseStep 510277 = 95677) (by norm_num)
theorem B510313 : Blo 451781 510313 := bbase (se 2 (by rfl) ⟨191367, by rfl⟩ : syracuseStep 510313 = 382735) (by norm_num)
theorem B575849 : Blo 451781 575849 := bbase (se 2 (by rfl) ⟨215943, by rfl⟩ : syracuseStep 575849 = 431887) (by norm_num)
theorem B543109 : Blo 451781 543109 := bbase (se 4 (by rfl) ⟨50916, by rfl⟩ : syracuseStep 543109 = 101833) (by norm_num)
theorem B510349 : Blo 451781 510349 := bbase (se 3 (by rfl) ⟨95690, by rfl⟩ : syracuseStep 510349 = 191381) (by norm_num)
theorem B575905 : Blo 451781 575905 := bbase (se 2 (by rfl) ⟨215964, by rfl⟩ : syracuseStep 575905 = 431929) (by norm_num)
theorem B510385 : Blo 451781 510385 := bbase (se 2 (by rfl) ⟨191394, by rfl⟩ : syracuseStep 510385 = 382789) (by norm_num)
theorem B510421 : Blo 451781 510421 := bbase (se 7 (by rfl) ⟨5981, by rfl⟩ : syracuseStep 510421 = 11963) (by norm_num)
theorem B510457 : Blo 451781 510457 := bbase (se 2 (by rfl) ⟨191421, by rfl⟩ : syracuseStep 510457 = 382843) (by norm_num)
theorem B576001 : Blo 451781 576001 := bbase (se 2 (by rfl) ⟨216000, by rfl⟩ : syracuseStep 576001 = 432001) (by norm_num)
theorem B510493 : Blo 451781 510493 := bbase (se 3 (by rfl) ⟨95717, by rfl⟩ : syracuseStep 510493 = 191435) (by norm_num)
theorem B1526309 : Blo 451781 1526309 := bbase (se 4 (by rfl) ⟨143091, by rfl⟩ : syracuseStep 1526309 = 286183) (by norm_num)
theorem B510529 : Blo 451781 510529 := bbase (se 2 (by rfl) ⟨191448, by rfl⟩ : syracuseStep 510529 = 382897) (by norm_num)
theorem B510565 : Blo 451781 510565 := bbase (se 4 (by rfl) ⟨47865, by rfl⟩ : syracuseStep 510565 = 95731) (by norm_num)
theorem B510601 : Blo 451781 510601 := bbase (se 2 (by rfl) ⟨191475, by rfl⟩ : syracuseStep 510601 = 382951) (by norm_num)
theorem B3263125 : Blo 451781 3263125 := bbase (se 6 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 3263125 = 152959) (by norm_num)
theorem B510637 : Blo 451781 510637 := bbase (se 3 (by rfl) ⟨95744, by rfl⟩ : syracuseStep 510637 = 191489) (by norm_num)
theorem B576173 : Blo 451781 576173 := bbase (se 3 (by rfl) ⟨108032, by rfl⟩ : syracuseStep 576173 = 216065) (by norm_num)
theorem B510673 : Blo 451781 510673 := bbase (se 2 (by rfl) ⟨191502, by rfl⟩ : syracuseStep 510673 = 383005) (by norm_num)
theorem B576229 : Blo 451781 576229 := bbase (se 4 (by rfl) ⟨54021, by rfl⟩ : syracuseStep 576229 = 108043) (by norm_num)
theorem B510709 : Blo 451781 510709 := bbase (se 5 (by rfl) ⟨23939, by rfl⟩ : syracuseStep 510709 = 47879) (by norm_num)
theorem B510745 : Blo 451781 510745 := bbase (se 2 (by rfl) ⟨191529, by rfl⟩ : syracuseStep 510745 = 383059) (by norm_num)
theorem B510781 : Blo 451781 510781 := bbase (se 3 (by rfl) ⟨95771, by rfl⟩ : syracuseStep 510781 = 191543) (by norm_num)
theorem B576325 : Blo 451781 576325 := bbase (se 4 (by rfl) ⟨54030, by rfl⟩ : syracuseStep 576325 = 108061) (by norm_num)
theorem B510817 : Blo 451781 510817 := bbase (se 2 (by rfl) ⟨191556, by rfl⟩ : syracuseStep 510817 = 383113) (by norm_num)
theorem B510853 : Blo 451781 510853 := bbase (se 4 (by rfl) ⟨47892, by rfl⟩ : syracuseStep 510853 = 95785) (by norm_num)
theorem B3263381 : Blo 451781 3263381 := bbase (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) (by norm_num)
theorem B510889 : Blo 451781 510889 := bbase (se 2 (by rfl) ⟨191583, by rfl⟩ : syracuseStep 510889 = 383167) (by norm_num)
theorem B969661 : Blo 451781 969661 := bbase (se 3 (by rfl) ⟨181811, by rfl⟩ : syracuseStep 969661 = 363623) (by norm_num)
theorem B510925 : Blo 451781 510925 := bbase (se 3 (by rfl) ⟨95798, by rfl⟩ : syracuseStep 510925 = 191597) (by norm_num)
theorem B1526741 : Blo 451781 1526741 := bbase (se 7 (by rfl) ⟨17891, by rfl⟩ : syracuseStep 1526741 = 35783) (by norm_num)
theorem B510961 : Blo 451781 510961 := bbase (se 2 (by rfl) ⟨191610, by rfl⟩ : syracuseStep 510961 = 383221) (by norm_num)
theorem B576497 : Blo 451781 576497 := bbase (se 2 (by rfl) ⟨216186, by rfl⟩ : syracuseStep 576497 = 432373) (by norm_num)
theorem B510997 : Blo 451781 510997 := bbase (se 6 (by rfl) ⟨11976, by rfl⟩ : syracuseStep 510997 = 23953) (by norm_num)
theorem B576553 : Blo 451781 576553 := bbase (se 2 (by rfl) ⟨216207, by rfl⟩ : syracuseStep 576553 = 432415) (by norm_num)
theorem B511033 : Blo 451781 511033 := bbase (se 2 (by rfl) ⟨191637, by rfl⟩ : syracuseStep 511033 = 383275) (by norm_num)
theorem B1723477 : Blo 451781 1723477 := bbase (se 8 (by rfl) ⟨10098, by rfl⟩ : syracuseStep 1723477 = 20197) (by norm_num)
theorem B511069 : Blo 451781 511069 := bbase (se 3 (by rfl) ⟨95825, by rfl⟩ : syracuseStep 511069 = 191651) (by norm_num)
theorem B511105 : Blo 451781 511105 := bbase (se 2 (by rfl) ⟨191664, by rfl⟩ : syracuseStep 511105 = 383329) (by norm_num)
theorem B2182277 : Blo 451781 2182277 := bbase (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) (by norm_num)
theorem B576649 : Blo 451781 576649 := bbase (se 2 (by rfl) ⟨216243, by rfl⟩ : syracuseStep 576649 = 432487) (by norm_num)
theorem B511141 : Blo 451781 511141 := bbase (se 4 (by rfl) ⟨47919, by rfl⟩ : syracuseStep 511141 = 95839) (by norm_num)
theorem B511177 : Blo 451781 511177 := bbase (se 2 (by rfl) ⟨191691, by rfl⟩ : syracuseStep 511177 = 383383) (by norm_num)
theorem B511213 : Blo 451781 511213 := bbase (se 3 (by rfl) ⟨95852, by rfl⟩ : syracuseStep 511213 = 191705) (by norm_num)
theorem B511249 : Blo 451781 511249 := bbase (se 2 (by rfl) ⟨191718, by rfl⟩ : syracuseStep 511249 = 383437) (by norm_num)
theorem B511285 : Blo 451781 511285 := bbase (se 5 (by rfl) ⟨23966, by rfl⟩ : syracuseStep 511285 = 47933) (by norm_num)
theorem B576821 : Blo 451781 576821 := bbase (se 5 (by rfl) ⟨27038, by rfl⟩ : syracuseStep 576821 = 54077) (by norm_num)
theorem B511321 : Blo 451781 511321 := bbase (se 2 (by rfl) ⟨191745, by rfl⟩ : syracuseStep 511321 = 383491) (by norm_num)
theorem B511357 : Blo 451781 511357 := bbase (se 3 (by rfl) ⟨95879, by rfl⟩ : syracuseStep 511357 = 191759) (by norm_num)
theorem B1527173 : Blo 451781 1527173 := bbase (se 4 (by rfl) ⟨143172, by rfl⟩ : syracuseStep 1527173 = 286345) (by norm_num)
theorem B1723781 : Blo 451781 1723781 := bbase (se 4 (by rfl) ⟨161604, by rfl⟩ : syracuseStep 1723781 = 323209) (by norm_num)
theorem B511393 : Blo 451781 511393 := bbase (se 2 (by rfl) ⟨191772, by rfl⟩ : syracuseStep 511393 = 383545) (by norm_num)
theorem B970157 : Blo 451781 970157 := bbase (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) (by norm_num)
theorem B511429 : Blo 451781 511429 := bbase (se 4 (by rfl) ⟨47946, by rfl⟩ : syracuseStep 511429 = 95893) (by norm_num)
theorem B511465 : Blo 451781 511465 := bbase (se 2 (by rfl) ⟨191799, by rfl⟩ : syracuseStep 511465 = 383599) (by norm_num)
theorem B511501 : Blo 451781 511501 := bbase (se 3 (by rfl) ⟨95906, by rfl⟩ : syracuseStep 511501 = 191813) (by norm_num)
theorem B511537 : Blo 451781 511537 := bbase (se 2 (by rfl) ⟨191826, by rfl⟩ : syracuseStep 511537 = 383653) (by norm_num)
theorem B511573 : Blo 451781 511573 := bbase (se 8 (by rfl) ⟨2997, by rfl⟩ : syracuseStep 511573 = 5995) (by norm_num)
theorem B511609 : Blo 451781 511609 := bbase (se 2 (by rfl) ⟨191853, by rfl⟩ : syracuseStep 511609 = 383707) (by norm_num)
theorem B511645 : Blo 451781 511645 := bbase (se 3 (by rfl) ⟨95933, by rfl⟩ : syracuseStep 511645 = 191867) (by norm_num)
theorem B511681 : Blo 451781 511681 := bbase (se 2 (by rfl) ⟨191880, by rfl⟩ : syracuseStep 511681 = 383761) (by norm_num)
theorem B511717 : Blo 451781 511717 := bbase (se 4 (by rfl) ⟨47973, by rfl⟩ : syracuseStep 511717 = 95947) (by norm_num)
theorem B544493 : Blo 451781 544493 := bbase (se 3 (by rfl) ⟨102092, by rfl⟩ : syracuseStep 544493 = 204185) (by norm_num)
theorem B511753 : Blo 451781 511753 := bbase (se 2 (by rfl) ⟨191907, by rfl⟩ : syracuseStep 511753 = 383815) (by norm_num)
theorem B511789 : Blo 451781 511789 := bbase (se 3 (by rfl) ⟨95960, by rfl⟩ : syracuseStep 511789 = 191921) (by norm_num)
theorem B1527605 : Blo 451781 1527605 := bbase (se 5 (by rfl) ⟨71606, by rfl⟩ : syracuseStep 1527605 = 143213) (by norm_num)
theorem B511825 : Blo 451781 511825 := bbase (se 2 (by rfl) ⟨191934, by rfl⟩ : syracuseStep 511825 = 383869) (by norm_num)
theorem B511861 : Blo 451781 511861 := bbase (se 5 (by rfl) ⟨23993, by rfl⟩ : syracuseStep 511861 = 47987) (by norm_num)
theorem B511897 : Blo 451781 511897 := bbase (se 2 (by rfl) ⟨191961, by rfl⟩ : syracuseStep 511897 = 383923) (by norm_num)
theorem B511933 : Blo 451781 511933 := bbase (se 3 (by rfl) ⟨95987, by rfl⟩ : syracuseStep 511933 = 191975) (by norm_num)
theorem B511969 : Blo 451781 511969 := bbase (se 2 (by rfl) ⟨191988, by rfl⟩ : syracuseStep 511969 = 383977) (by norm_num)
theorem B544753 : Blo 451781 544753 := bbase (se 2 (by rfl) ⟨204282, by rfl⟩ : syracuseStep 544753 = 408565) (by norm_num)
theorem B512005 : Blo 451781 512005 := bbase (se 4 (by rfl) ⟨48000, by rfl⟩ : syracuseStep 512005 = 96001) (by norm_num)
theorem B544801 : Blo 451781 544801 := bbase (se 2 (by rfl) ⟨204300, by rfl⟩ : syracuseStep 544801 = 408601) (by norm_num)
theorem B512041 : Blo 451781 512041 := bbase (se 2 (by rfl) ⟨192015, by rfl⟩ : syracuseStep 512041 = 384031) (by norm_num)
theorem B1036349 : Blo 451781 1036349 := bbase (se 3 (by rfl) ⟨194315, by rfl⟩ : syracuseStep 1036349 = 388631) (by norm_num)
theorem B512077 : Blo 451781 512077 := bbase (se 3 (by rfl) ⟨96014, by rfl⟩ : syracuseStep 512077 = 192029) (by norm_num)
theorem B3887189 : Blo 451781 3887189 := bbase (se 8 (by rfl) ⟨22776, by rfl⟩ : syracuseStep 3887189 = 45553) (by norm_num)
theorem B512113 : Blo 451781 512113 := bbase (se 2 (by rfl) ⟨192042, by rfl⟩ : syracuseStep 512113 = 384085) (by norm_num)
theorem B512149 : Blo 451781 512149 := bbase (se 6 (by rfl) ⟨12003, by rfl⟩ : syracuseStep 512149 = 24007) (by norm_num)
theorem B2904245 : Blo 451781 2904245 := bbase (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) (by norm_num)
theorem B512185 : Blo 451781 512185 := bbase (se 2 (by rfl) ⟨192069, by rfl⟩ : syracuseStep 512185 = 384139) (by norm_num)
theorem B512221 : Blo 451781 512221 := bbase (se 3 (by rfl) ⟨96041, by rfl⟩ : syracuseStep 512221 = 192083) (by norm_num)
theorem B1528037 : Blo 451781 1528037 := bbase (se 4 (by rfl) ⟨143253, by rfl⟩ : syracuseStep 1528037 = 286507) (by norm_num)
theorem B512257 : Blo 451781 512257 := bbase (se 2 (by rfl) ⟨192096, by rfl⟩ : syracuseStep 512257 = 384193) (by norm_num)
theorem B971021 : Blo 451781 971021 := bbase (se 3 (by rfl) ⟨182066, by rfl⟩ : syracuseStep 971021 = 364133) (by norm_num)
theorem B512293 : Blo 451781 512293 := bbase (se 4 (by rfl) ⟨48027, by rfl⟩ : syracuseStep 512293 = 96055) (by norm_num)
theorem B512329 : Blo 451781 512329 := bbase (se 2 (by rfl) ⟨192123, by rfl⟩ : syracuseStep 512329 = 384247) (by norm_num)
theorem B610669 : Blo 451781 610669 := bbase (se 3 (by rfl) ⟨114500, by rfl⟩ : syracuseStep 610669 = 229001) (by norm_num)
theorem B512365 : Blo 451781 512365 := bbase (se 3 (by rfl) ⟨96068, by rfl⟩ : syracuseStep 512365 = 192137) (by norm_num)
theorem B512401 : Blo 451781 512401 := bbase (se 2 (by rfl) ⟨192150, by rfl⟩ : syracuseStep 512401 = 384301) (by norm_num)
theorem B971165 : Blo 451781 971165 := bbase (se 3 (by rfl) ⟨182093, by rfl⟩ : syracuseStep 971165 = 364187) (by norm_num)
theorem B512437 : Blo 451781 512437 := bbase (se 5 (by rfl) ⟨24020, by rfl⟩ : syracuseStep 512437 = 48041) (by norm_num)
theorem B512473 : Blo 451781 512473 := bbase (se 2 (by rfl) ⟨192177, by rfl⟩ : syracuseStep 512473 = 384355) (by norm_num)
theorem B643565 : Blo 451781 643565 := bbase (se 3 (by rfl) ⟨120668, by rfl⟩ : syracuseStep 643565 = 241337) (by norm_num)
theorem B512509 : Blo 451781 512509 := bbase (se 3 (by rfl) ⟨96095, by rfl⟩ : syracuseStep 512509 = 192191) (by norm_num)
theorem B512545 : Blo 451781 512545 := bbase (se 2 (by rfl) ⟨192204, by rfl⟩ : syracuseStep 512545 = 384409) (by norm_num)
theorem B512581 : Blo 451781 512581 := bbase (se 4 (by rfl) ⟨48054, by rfl⟩ : syracuseStep 512581 = 96109) (by norm_num)
theorem B1167949 : Blo 451781 1167949 := bbase (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) (by norm_num)
theorem B512617 : Blo 451781 512617 := bbase (se 2 (by rfl) ⟨192231, by rfl⟩ : syracuseStep 512617 = 384463) (by norm_num)
theorem B512653 : Blo 451781 512653 := bbase (se 3 (by rfl) ⟨96122, by rfl⟩ : syracuseStep 512653 = 192245) (by norm_num)
theorem B1528469 : Blo 451781 1528469 := bbase (se 6 (by rfl) ⟨35823, by rfl⟩ : syracuseStep 1528469 = 71647) (by norm_num)
theorem B512689 : Blo 451781 512689 := bbase (se 2 (by rfl) ⟨192258, by rfl⟩ : syracuseStep 512689 = 384517) (by norm_num)
theorem B545473 : Blo 451781 545473 := bbase (se 2 (by rfl) ⟨204552, by rfl⟩ : syracuseStep 545473 = 409105) (by norm_num)
theorem B840389 : Blo 451781 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B512725 : Blo 451781 512725 := bbase (se 7 (by rfl) ⟨6008, by rfl⟩ : syracuseStep 512725 = 12017) (by norm_num)
theorem B1037045 : Blo 451781 1037045 := bbase (se 5 (by rfl) ⟨48611, by rfl⟩ : syracuseStep 1037045 = 97223) (by norm_num)
theorem B1168357 : Blo 451781 1168357 := bbase (se 4 (by rfl) ⟨109533, by rfl⟩ : syracuseStep 1168357 = 219067) (by norm_num)
theorem B644117 : Blo 451781 644117 := bbase (se 6 (by rfl) ⟨15096, by rfl⟩ : syracuseStep 644117 = 30193) (by norm_num)
theorem B611365 : Blo 451781 611365 := bbase (se 4 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 611365 = 114631) (by norm_num)
theorem B1528901 : Blo 451781 1528901 := bbase (se 4 (by rfl) ⟨143334, by rfl⟩ : syracuseStep 1528901 = 286669) (by norm_num)
theorem B971909 : Blo 451781 971909 := bbase (se 4 (by rfl) ⟨91116, by rfl⟩ : syracuseStep 971909 = 182233) (by norm_num)
theorem B2577653 : Blo 451781 2577653 := bbase (se 5 (by rfl) ⟨120827, by rfl⟩ : syracuseStep 2577653 = 241655) (by norm_num)
theorem B3495221 : Blo 451781 3495221 := bbase (se 5 (by rfl) ⟨163838, by rfl⟩ : syracuseStep 3495221 = 327677) (by norm_num)
theorem B1168789 : Blo 451781 1168789 := bbase (se 6 (by rfl) ⟨27393, by rfl⟩ : syracuseStep 1168789 = 54787) (by norm_num)
theorem B1725893 : Blo 451781 1725893 := bbase (se 4 (by rfl) ⟨161802, by rfl⟩ : syracuseStep 1725893 = 323605) (by norm_num)
theorem B1529333 : Blo 451781 1529333 := bbase (se 5 (by rfl) ⟨71687, by rfl⟩ : syracuseStep 1529333 = 143375) (by norm_num)
theorem B546473 : Blo 451781 546473 := bbase (se 2 (by rfl) ⟨204927, by rfl⟩ : syracuseStep 546473 = 409855) (by norm_num)
theorem B1726181 : Blo 451781 1726181 := bbase (se 4 (by rfl) ⟨161829, by rfl⟩ : syracuseStep 1726181 = 323659) (by norm_num)
theorem B546545 : Blo 451781 546545 := bbase (se 2 (by rfl) ⟨204954, by rfl⟩ : syracuseStep 546545 = 409909) (by norm_num)
theorem B644869 : Blo 451781 644869 := bbase (se 4 (by rfl) ⟨60456, by rfl⟩ : syracuseStep 644869 = 120913) (by norm_num)
theorem B1038101 : Blo 451781 1038101 := bbase (se 6 (by rfl) ⟨24330, by rfl⟩ : syracuseStep 1038101 = 48661) (by norm_num)
theorem B677693 : Blo 451781 677693 := bbase (se 3 (by rfl) ⟨127067, by rfl⟩ : syracuseStep 677693 = 254135) (by norm_num)
theorem B677717 : Blo 451781 677717 := bbase (se 9 (by rfl) ⟨1985, by rfl⟩ : syracuseStep 677717 = 3971) (by norm_num)
theorem B677741 : Blo 451781 677741 := bbase (se 3 (by rfl) ⟨127076, by rfl⟩ : syracuseStep 677741 = 254153) (by norm_num)
theorem B972661 : Blo 451781 972661 := bbase (se 5 (by rfl) ⟨45593, by rfl⟩ : syracuseStep 972661 = 91187) (by norm_num)
theorem B677765 : Blo 451781 677765 := bbase (se 4 (by rfl) ⟨63540, by rfl⟩ : syracuseStep 677765 = 127081) (by norm_num)
theorem B677789 : Blo 451781 677789 := bbase (se 3 (by rfl) ⟨127085, by rfl⟩ : syracuseStep 677789 = 254171) (by norm_num)
theorem B1529765 : Blo 451781 1529765 := bbase (se 4 (by rfl) ⟨143415, by rfl⟩ : syracuseStep 1529765 = 286831) (by norm_num)
theorem B677813 : Blo 451781 677813 := bbase (se 5 (by rfl) ⟨31772, by rfl⟩ : syracuseStep 677813 = 63545) (by norm_num)
theorem B677837 : Blo 451781 677837 := bbase (se 3 (by rfl) ⟨127094, by rfl⟩ : syracuseStep 677837 = 254189) (by norm_num)
theorem B677861 : Blo 451781 677861 := bbase (se 4 (by rfl) ⟨63549, by rfl⟩ : syracuseStep 677861 = 127099) (by norm_num)
theorem B677885 : Blo 451781 677885 := bbase (se 3 (by rfl) ⟨127103, by rfl⟩ : syracuseStep 677885 = 254207) (by norm_num)
theorem B972805 : Blo 451781 972805 := bbase (se 4 (by rfl) ⟨91200, by rfl⟩ : syracuseStep 972805 = 182401) (by norm_num)
theorem B677909 : Blo 451781 677909 := bbase (se 6 (by rfl) ⟨15888, by rfl⟩ : syracuseStep 677909 = 31777) (by norm_num)
theorem B546853 : Blo 451781 546853 := bbase (se 4 (by rfl) ⟨51267, by rfl⟩ : syracuseStep 546853 = 102535) (by norm_num)
theorem B677933 : Blo 451781 677933 := bbase (se 3 (by rfl) ⟨127112, by rfl⟩ : syracuseStep 677933 = 254225) (by norm_num)
theorem B776237 : Blo 451781 776237 := bbase (se 3 (by rfl) ⟨145544, by rfl⟩ : syracuseStep 776237 = 291089) (by norm_num)
theorem B677957 : Blo 451781 677957 := bbase (se 4 (by rfl) ⟨63558, by rfl⟩ : syracuseStep 677957 = 127117) (by norm_num)
theorem B677981 : Blo 451781 677981 := bbase (se 3 (by rfl) ⟨127121, by rfl⟩ : syracuseStep 677981 = 254243) (by norm_num)
theorem B678005 : Blo 451781 678005 := bbase (se 5 (by rfl) ⟨31781, by rfl⟩ : syracuseStep 678005 = 63563) (by norm_num)
theorem B678029 : Blo 451781 678029 := bbase (se 3 (by rfl) ⟨127130, by rfl⟩ : syracuseStep 678029 = 254261) (by norm_num)
theorem B678053 : Blo 451781 678053 := bbase (se 4 (by rfl) ⟨63567, by rfl⟩ : syracuseStep 678053 = 127135) (by norm_num)
theorem B678077 : Blo 451781 678077 := bbase (se 3 (by rfl) ⟨127139, by rfl⟩ : syracuseStep 678077 = 254279) (by norm_num)
theorem B547021 : Blo 451781 547021 := bbase (se 3 (by rfl) ⟨102566, by rfl⟩ : syracuseStep 547021 = 205133) (by norm_num)
theorem B678101 : Blo 451781 678101 := bbase (se 7 (by rfl) ⟨7946, by rfl⟩ : syracuseStep 678101 = 15893) (by norm_num)
theorem B678125 : Blo 451781 678125 := bbase (se 3 (by rfl) ⟨127148, by rfl⟩ : syracuseStep 678125 = 254297) (by norm_num)
theorem B547069 : Blo 451781 547069 := bbase (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) (by norm_num)
theorem B678149 : Blo 451781 678149 := bbase (se 4 (by rfl) ⟨63576, by rfl⟩ : syracuseStep 678149 = 127153) (by norm_num)
theorem B678173 : Blo 451781 678173 := bbase (se 3 (by rfl) ⟨127157, by rfl⟩ : syracuseStep 678173 = 254315) (by norm_num)
theorem B678197 : Blo 451781 678197 := bbase (se 5 (by rfl) ⟨31790, by rfl⟩ : syracuseStep 678197 = 63581) (by norm_num)
theorem B678221 : Blo 451781 678221 := bbase (se 3 (by rfl) ⟨127166, by rfl⟩ : syracuseStep 678221 = 254333) (by norm_num)
theorem B612685 : Blo 451781 612685 := bbase (se 3 (by rfl) ⟨114878, by rfl⟩ : syracuseStep 612685 = 229757) (by norm_num)
theorem B1530197 : Blo 451781 1530197 := bbase (se 10 (by rfl) ⟨2241, by rfl⟩ : syracuseStep 1530197 = 4483) (by norm_num)
theorem B547165 : Blo 451781 547165 := bbase (se 3 (by rfl) ⟨102593, by rfl⟩ : syracuseStep 547165 = 205187) (by norm_num)
theorem B678245 : Blo 451781 678245 := bbase (se 4 (by rfl) ⟨63585, by rfl⟩ : syracuseStep 678245 = 127171) (by norm_num)
theorem B678269 : Blo 451781 678269 := bbase (se 3 (by rfl) ⟨127175, by rfl⟩ : syracuseStep 678269 = 254351) (by norm_num)
theorem B973181 : Blo 451781 973181 := bbase (se 3 (by rfl) ⟨182471, by rfl⟩ : syracuseStep 973181 = 364943) (by norm_num)
theorem B612749 : Blo 451781 612749 := bbase (se 3 (by rfl) ⟨114890, by rfl⟩ : syracuseStep 612749 = 229781) (by norm_num)
theorem B678293 : Blo 451781 678293 := bbase (se 6 (by rfl) ⟨15897, by rfl⟩ : syracuseStep 678293 = 31795) (by norm_num)
theorem B2578837 : Blo 451781 2578837 := bbase (se 6 (by rfl) ⟨60441, by rfl⟩ : syracuseStep 2578837 = 120883) (by norm_num)
theorem B678317 : Blo 451781 678317 := bbase (se 3 (by rfl) ⟨127184, by rfl⟩ : syracuseStep 678317 = 254369) (by norm_num)
theorem B678341 : Blo 451781 678341 := bbase (se 4 (by rfl) ⟨63594, by rfl⟩ : syracuseStep 678341 = 127189) (by norm_num)
theorem B678365 : Blo 451781 678365 := bbase (se 3 (by rfl) ⟨127193, by rfl⟩ : syracuseStep 678365 = 254387) (by norm_num)
theorem B678389 : Blo 451781 678389 := bbase (se 5 (by rfl) ⟨31799, by rfl⟩ : syracuseStep 678389 = 63599) (by norm_num)
theorem B678413 : Blo 451781 678413 := bbase (se 3 (by rfl) ⟨127202, by rfl⟩ : syracuseStep 678413 = 254405) (by norm_num)
theorem B1628693 : Blo 451781 1628693 := bbase (se 6 (by rfl) ⟨38172, by rfl⟩ : syracuseStep 1628693 = 76345) (by norm_num)
theorem B645661 : Blo 451781 645661 := bbase (se 3 (by rfl) ⟨121061, by rfl⟩ : syracuseStep 645661 = 242123) (by norm_num)
theorem B678437 : Blo 451781 678437 := bbase (se 4 (by rfl) ⟨63603, by rfl⟩ : syracuseStep 678437 = 127207) (by norm_num)
theorem B678461 : Blo 451781 678461 := bbase (se 3 (by rfl) ⟨127211, by rfl⟩ : syracuseStep 678461 = 254423) (by norm_num)
theorem B678485 : Blo 451781 678485 := bbase (se 8 (by rfl) ⟨3975, by rfl⟩ : syracuseStep 678485 = 7951) (by norm_num)
theorem B678509 : Blo 451781 678509 := bbase (se 3 (by rfl) ⟨127220, by rfl⟩ : syracuseStep 678509 = 254441) (by norm_num)
theorem B678533 : Blo 451781 678533 := bbase (se 4 (by rfl) ⟨63612, by rfl⟩ : syracuseStep 678533 = 127225) (by norm_num)
theorem B678557 : Blo 451781 678557 := bbase (se 3 (by rfl) ⟨127229, by rfl⟩ : syracuseStep 678557 = 254459) (by norm_num)
theorem B1628837 : Blo 451781 1628837 := bbase (se 4 (by rfl) ⟨152703, by rfl⟩ : syracuseStep 1628837 = 305407) (by norm_num)
theorem B678581 : Blo 451781 678581 := bbase (se 5 (by rfl) ⟨31808, by rfl⟩ : syracuseStep 678581 = 63617) (by norm_num)
theorem B678605 : Blo 451781 678605 := bbase (se 3 (by rfl) ⟨127238, by rfl⟩ : syracuseStep 678605 = 254477) (by norm_num)
theorem B678629 : Blo 451781 678629 := bbase (se 4 (by rfl) ⟨63621, by rfl⟩ : syracuseStep 678629 = 127243) (by norm_num)
theorem B3496693 : Blo 451781 3496693 := bbase (se 5 (by rfl) ⟨163907, by rfl⟩ : syracuseStep 3496693 = 327815) (by norm_num)
theorem B678653 : Blo 451781 678653 := bbase (se 3 (by rfl) ⟨127247, by rfl⟩ : syracuseStep 678653 = 254495) (by norm_num)
theorem B1530629 : Blo 451781 1530629 := bbase (se 4 (by rfl) ⟨143496, by rfl⟩ : syracuseStep 1530629 = 286993) (by norm_num)
theorem B678677 : Blo 451781 678677 := bbase (se 6 (by rfl) ⟨15906, by rfl⟩ : syracuseStep 678677 = 31813) (by norm_num)
theorem B678701 : Blo 451781 678701 := bbase (se 3 (by rfl) ⟨127256, by rfl⟩ : syracuseStep 678701 = 254513) (by norm_num)
theorem B678725 : Blo 451781 678725 := bbase (se 4 (by rfl) ⟨63630, by rfl⟩ : syracuseStep 678725 = 127261) (by norm_num)
theorem B678749 : Blo 451781 678749 := bbase (se 3 (by rfl) ⟨127265, by rfl⟩ : syracuseStep 678749 = 254531) (by norm_num)
theorem B645997 : Blo 451781 645997 := bbase (se 3 (by rfl) ⟨121124, by rfl⟩ : syracuseStep 645997 = 242249) (by norm_num)
theorem B678773 : Blo 451781 678773 := bbase (se 5 (by rfl) ⟨31817, by rfl⟩ : syracuseStep 678773 = 63635) (by norm_num)
theorem B1727365 : Blo 451781 1727365 := bbase (se 4 (by rfl) ⟨161940, by rfl⟩ : syracuseStep 1727365 = 323881) (by norm_num)
theorem B678797 : Blo 451781 678797 := bbase (se 3 (by rfl) ⟨127274, by rfl⟩ : syracuseStep 678797 = 254549) (by norm_num)
theorem B678821 : Blo 451781 678821 := bbase (se 4 (by rfl) ⟨63639, by rfl⟩ : syracuseStep 678821 = 127279) (by norm_num)
theorem B678845 : Blo 451781 678845 := bbase (se 3 (by rfl) ⟨127283, by rfl⟩ : syracuseStep 678845 = 254567) (by norm_num)
theorem B678869 : Blo 451781 678869 := bbase (se 7 (by rfl) ⟨7955, by rfl⟩ : syracuseStep 678869 = 15911) (by norm_num)
theorem B678893 : Blo 451781 678893 := bbase (se 3 (by rfl) ⟨127292, by rfl⟩ : syracuseStep 678893 = 254585) (by norm_num)
theorem B678917 : Blo 451781 678917 := bbase (se 4 (by rfl) ⟨63648, by rfl⟩ : syracuseStep 678917 = 127297) (by norm_num)
theorem B678941 : Blo 451781 678941 := bbase (se 3 (by rfl) ⟨127301, by rfl⟩ : syracuseStep 678941 = 254603) (by norm_num)
theorem B580645 : Blo 451781 580645 := bbase (se 4 (by rfl) ⟨54435, by rfl⟩ : syracuseStep 580645 = 108871) (by norm_num)
theorem B1956917 : Blo 451781 1956917 := bbase (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) (by norm_num)
theorem B678965 : Blo 451781 678965 := bbase (se 5 (by rfl) ⟨31826, by rfl⟩ : syracuseStep 678965 = 63653) (by norm_num)
theorem B646213 : Blo 451781 646213 := bbase (se 4 (by rfl) ⟨60582, by rfl⟩ : syracuseStep 646213 = 121165) (by norm_num)
theorem B678989 : Blo 451781 678989 := bbase (se 3 (by rfl) ⟨127310, by rfl⟩ : syracuseStep 678989 = 254621) (by norm_num)
theorem B679013 : Blo 451781 679013 := bbase (se 4 (by rfl) ⟨63657, by rfl⟩ : syracuseStep 679013 = 127315) (by norm_num)
theorem B679037 : Blo 451781 679037 := bbase (se 3 (by rfl) ⟨127319, by rfl⟩ : syracuseStep 679037 = 254639) (by norm_num)
theorem B679061 : Blo 451781 679061 := bbase (se 6 (by rfl) ⟨15915, by rfl⟩ : syracuseStep 679061 = 31831) (by norm_num)
theorem B482473 : Blo 451781 482473 := bbase (se 2 (by rfl) ⟨180927, by rfl⟩ : syracuseStep 482473 = 361855) (by norm_num)
theorem B679085 : Blo 451781 679085 := bbase (se 3 (by rfl) ⟨127328, by rfl⟩ : syracuseStep 679085 = 254657) (by norm_num)
theorem B1531061 : Blo 451781 1531061 := bbase (se 5 (by rfl) ⟨71768, by rfl⟩ : syracuseStep 1531061 = 143537) (by norm_num)
theorem B1727669 : Blo 451781 1727669 := bbase (se 5 (by rfl) ⟨80984, by rfl⟩ : syracuseStep 1727669 = 161969) (by norm_num)
theorem B679109 : Blo 451781 679109 := bbase (se 4 (by rfl) ⟨63666, by rfl⟩ : syracuseStep 679109 = 127333) (by norm_num)
theorem B679133 : Blo 451781 679133 := bbase (se 3 (by rfl) ⟨127337, by rfl⟩ : syracuseStep 679133 = 254675) (by norm_num)
theorem B580853 : Blo 451781 580853 := bbase (se 5 (by rfl) ⟨27227, by rfl⟩ : syracuseStep 580853 = 54455) (by norm_num)
theorem B679157 : Blo 451781 679157 := bbase (se 5 (by rfl) ⟨31835, by rfl⟩ : syracuseStep 679157 = 63671) (by norm_num)
theorem B679181 : Blo 451781 679181 := bbase (se 3 (by rfl) ⟨127346, by rfl⟩ : syracuseStep 679181 = 254693) (by norm_num)
theorem B679205 : Blo 451781 679205 := bbase (se 4 (by rfl) ⟨63675, by rfl⟩ : syracuseStep 679205 = 127351) (by norm_num)
theorem B679229 : Blo 451781 679229 := bbase (se 3 (by rfl) ⟨127355, by rfl⟩ : syracuseStep 679229 = 254711) (by norm_num)
theorem B679253 : Blo 451781 679253 := bbase (se 11 (by rfl) ⟨497, by rfl⟩ : syracuseStep 679253 = 995) (by norm_num)
theorem B679277 : Blo 451781 679277 := bbase (se 3 (by rfl) ⟨127364, by rfl⟩ : syracuseStep 679277 = 254729) (by norm_num)
theorem B679301 : Blo 451781 679301 := bbase (se 4 (by rfl) ⟨63684, by rfl⟩ : syracuseStep 679301 = 127369) (by norm_num)
theorem B679325 : Blo 451781 679325 := bbase (se 3 (by rfl) ⟨127373, by rfl⟩ : syracuseStep 679325 = 254747) (by norm_num)
theorem B679349 : Blo 451781 679349 := bbase (se 5 (by rfl) ⟨31844, by rfl⟩ : syracuseStep 679349 = 63689) (by norm_num)
theorem B646589 : Blo 451781 646589 := bbase (se 3 (by rfl) ⟨121235, by rfl⟩ : syracuseStep 646589 = 242471) (by norm_num)
theorem B679373 : Blo 451781 679373 := bbase (se 3 (by rfl) ⟨127382, by rfl⟩ : syracuseStep 679373 = 254765) (by norm_num)
theorem B679397 : Blo 451781 679397 := bbase (se 4 (by rfl) ⟨63693, by rfl⟩ : syracuseStep 679397 = 127387) (by norm_num)
theorem B679421 : Blo 451781 679421 := bbase (se 3 (by rfl) ⟨127391, by rfl⟩ : syracuseStep 679421 = 254783) (by norm_num)
theorem B679445 : Blo 451781 679445 := bbase (se 6 (by rfl) ⟨15924, by rfl⟩ : syracuseStep 679445 = 31849) (by norm_num)
theorem B679469 : Blo 451781 679469 := bbase (se 3 (by rfl) ⟨127400, by rfl⟩ : syracuseStep 679469 = 254801) (by norm_num)
theorem B876077 : Blo 451781 876077 := bbase (se 3 (by rfl) ⟨164264, by rfl⟩ : syracuseStep 876077 = 328529) (by norm_num)
theorem B679493 : Blo 451781 679493 := bbase (se 4 (by rfl) ⟨63702, by rfl⟩ : syracuseStep 679493 = 127405) (by norm_num)
theorem B679517 : Blo 451781 679517 := bbase (se 3 (by rfl) ⟨127409, by rfl⟩ : syracuseStep 679517 = 254819) (by norm_num)
theorem B1531493 : Blo 451781 1531493 := bbase (se 4 (by rfl) ⟨143577, by rfl⟩ : syracuseStep 1531493 = 287155) (by norm_num)
theorem B679541 : Blo 451781 679541 := bbase (se 5 (by rfl) ⟨31853, by rfl⟩ : syracuseStep 679541 = 63707) (by norm_num)
theorem B679565 : Blo 451781 679565 := bbase (se 3 (by rfl) ⟨127418, by rfl⟩ : syracuseStep 679565 = 254837) (by norm_num)
theorem B679589 : Blo 451781 679589 := bbase (se 4 (by rfl) ⟨63711, by rfl⟩ : syracuseStep 679589 = 127423) (by norm_num)
theorem B679613 : Blo 451781 679613 := bbase (se 3 (by rfl) ⟨127427, by rfl⟩ : syracuseStep 679613 = 254855) (by norm_num)
theorem B679637 : Blo 451781 679637 := bbase (se 7 (by rfl) ⟨7964, by rfl⟩ : syracuseStep 679637 = 15929) (by norm_num)
theorem B515813 : Blo 451781 515813 := bbase (se 4 (by rfl) ⟨48357, by rfl⟩ : syracuseStep 515813 = 96715) (by norm_num)
theorem B679661 : Blo 451781 679661 := bbase (se 3 (by rfl) ⟨127436, by rfl⟩ : syracuseStep 679661 = 254873) (by norm_num)
theorem B679685 : Blo 451781 679685 := bbase (se 4 (by rfl) ⟨63720, by rfl⟩ : syracuseStep 679685 = 127441) (by norm_num)
theorem B679709 : Blo 451781 679709 := bbase (se 3 (by rfl) ⟨127445, by rfl⟩ : syracuseStep 679709 = 254891) (by norm_num)
theorem B679733 : Blo 451781 679733 := bbase (se 5 (by rfl) ⟨31862, by rfl⟩ : syracuseStep 679733 = 63725) (by norm_num)
theorem B679757 : Blo 451781 679757 := bbase (se 3 (by rfl) ⟨127454, by rfl⟩ : syracuseStep 679757 = 254909) (by norm_num)
theorem B679781 : Blo 451781 679781 := bbase (se 4 (by rfl) ⟨63729, by rfl⟩ : syracuseStep 679781 = 127459) (by norm_num)
theorem B679805 : Blo 451781 679805 := bbase (se 3 (by rfl) ⟨127463, by rfl⟩ : syracuseStep 679805 = 254927) (by norm_num)
theorem B679829 : Blo 451781 679829 := bbase (se 6 (by rfl) ⟨15933, by rfl⟩ : syracuseStep 679829 = 31867) (by norm_num)
theorem B778133 : Blo 451781 778133 := bbase (se 6 (by rfl) ⟨18237, by rfl⟩ : syracuseStep 778133 = 36475) (by norm_num)
theorem B679853 : Blo 451781 679853 := bbase (se 3 (by rfl) ⟨127472, by rfl⟩ : syracuseStep 679853 = 254945) (by norm_num)
theorem B679877 : Blo 451781 679877 := bbase (se 4 (by rfl) ⟨63738, by rfl⟩ : syracuseStep 679877 = 127477) (by norm_num)
theorem B483293 : Blo 451781 483293 := bbase (se 3 (by rfl) ⟨90617, by rfl⟩ : syracuseStep 483293 = 181235) (by norm_num)
theorem B679901 : Blo 451781 679901 := bbase (se 3 (by rfl) ⟨127481, by rfl⟩ : syracuseStep 679901 = 254963) (by norm_num)
theorem B679925 : Blo 451781 679925 := bbase (se 5 (by rfl) ⟨31871, by rfl⟩ : syracuseStep 679925 = 63743) (by norm_num)
theorem B679949 : Blo 451781 679949 := bbase (se 3 (by rfl) ⟨127490, by rfl⟩ : syracuseStep 679949 = 254981) (by norm_num)
theorem B1531925 : Blo 451781 1531925 := bbase (se 6 (by rfl) ⟨35904, by rfl⟩ : syracuseStep 1531925 = 71809) (by norm_num)
theorem B679973 : Blo 451781 679973 := bbase (se 4 (by rfl) ⟨63747, by rfl⟩ : syracuseStep 679973 = 127495) (by norm_num)
theorem B679997 : Blo 451781 679997 := bbase (se 3 (by rfl) ⟨127499, by rfl⟩ : syracuseStep 679997 = 254999) (by norm_num)
theorem B680021 : Blo 451781 680021 := bbase (se 8 (by rfl) ⟨3984, by rfl⟩ : syracuseStep 680021 = 7969) (by norm_num)
theorem B876637 : Blo 451781 876637 := bbase (se 3 (by rfl) ⟨164369, by rfl⟩ : syracuseStep 876637 = 328739) (by norm_num)
theorem B680045 : Blo 451781 680045 := bbase (se 3 (by rfl) ⟨127508, by rfl⟩ : syracuseStep 680045 = 255017) (by norm_num)
theorem B680069 : Blo 451781 680069 := bbase (se 4 (by rfl) ⟨63756, by rfl⟩ : syracuseStep 680069 = 127513) (by norm_num)
theorem B680093 : Blo 451781 680093 := bbase (se 3 (by rfl) ⟨127517, by rfl⟩ : syracuseStep 680093 = 255035) (by norm_num)
theorem B680117 : Blo 451781 680117 := bbase (se 5 (by rfl) ⟨31880, by rfl⟩ : syracuseStep 680117 = 63761) (by norm_num)
theorem B680141 : Blo 451781 680141 := bbase (se 3 (by rfl) ⟨127526, by rfl⟩ : syracuseStep 680141 = 255053) (by norm_num)
theorem B680165 : Blo 451781 680165 := bbase (se 4 (by rfl) ⟨63765, by rfl⟩ : syracuseStep 680165 = 127531) (by norm_num)
theorem B680189 : Blo 451781 680189 := bbase (se 3 (by rfl) ⟨127535, by rfl⟩ : syracuseStep 680189 = 255071) (by norm_num)
theorem B680213 : Blo 451781 680213 := bbase (se 6 (by rfl) ⟨15942, by rfl⟩ : syracuseStep 680213 = 31885) (by norm_num)
theorem B680237 : Blo 451781 680237 := bbase (se 3 (by rfl) ⟨127544, by rfl⟩ : syracuseStep 680237 = 255089) (by norm_num)
theorem B680261 : Blo 451781 680261 := bbase (se 4 (by rfl) ⟨63774, by rfl⟩ : syracuseStep 680261 = 127549) (by norm_num)
theorem B2580821 : Blo 451781 2580821 := bbase (se 10 (by rfl) ⟨3780, by rfl⟩ : syracuseStep 2580821 = 7561) (by norm_num)
theorem B680285 : Blo 451781 680285 := bbase (se 3 (by rfl) ⟨127553, by rfl⟩ : syracuseStep 680285 = 255107) (by norm_num)
theorem B680309 : Blo 451781 680309 := bbase (se 5 (by rfl) ⟨31889, by rfl⟩ : syracuseStep 680309 = 63779) (by norm_num)
theorem B680333 : Blo 451781 680333 := bbase (se 3 (by rfl) ⟨127562, by rfl⟩ : syracuseStep 680333 = 255125) (by norm_num)
theorem B483737 : Blo 451781 483737 := bbase (se 2 (by rfl) ⟨181401, by rfl⟩ : syracuseStep 483737 = 362803) (by norm_num)
theorem B680357 : Blo 451781 680357 := bbase (se 4 (by rfl) ⟨63783, by rfl⟩ : syracuseStep 680357 = 127567) (by norm_num)
theorem B680381 : Blo 451781 680381 := bbase (se 3 (by rfl) ⟨127571, by rfl⟩ : syracuseStep 680381 = 255143) (by norm_num)
theorem B1532357 : Blo 451781 1532357 := bbase (se 4 (by rfl) ⟨143658, by rfl⟩ : syracuseStep 1532357 = 287317) (by norm_num)
theorem B680405 : Blo 451781 680405 := bbase (se 7 (by rfl) ⟨7973, by rfl⟩ : syracuseStep 680405 = 15947) (by norm_num)
theorem B680429 : Blo 451781 680429 := bbase (se 3 (by rfl) ⟨127580, by rfl⟩ : syracuseStep 680429 = 255161) (by norm_num)
theorem B680453 : Blo 451781 680453 := bbase (se 4 (by rfl) ⟨63792, by rfl⟩ : syracuseStep 680453 = 127585) (by norm_num)
theorem B680477 : Blo 451781 680477 := bbase (se 3 (by rfl) ⟨127589, by rfl⟩ : syracuseStep 680477 = 255179) (by norm_num)
theorem B680501 : Blo 451781 680501 := bbase (se 5 (by rfl) ⟨31898, by rfl⟩ : syracuseStep 680501 = 63797) (by norm_num)
theorem B680525 : Blo 451781 680525 := bbase (se 3 (by rfl) ⟨127598, by rfl⟩ : syracuseStep 680525 = 255197) (by norm_num)
theorem B680549 : Blo 451781 680549 := bbase (se 4 (by rfl) ⟨63801, by rfl⟩ : syracuseStep 680549 = 127603) (by norm_num)
theorem B680573 : Blo 451781 680573 := bbase (se 3 (by rfl) ⟨127607, by rfl⟩ : syracuseStep 680573 = 255215) (by norm_num)
theorem B483985 : Blo 451781 483985 := bbase (se 2 (by rfl) ⟨181494, by rfl⟩ : syracuseStep 483985 = 362989) (by norm_num)
theorem B680597 : Blo 451781 680597 := bbase (se 6 (by rfl) ⟨15951, by rfl⟩ : syracuseStep 680597 = 31903) (by norm_num)
theorem B680621 : Blo 451781 680621 := bbase (se 3 (by rfl) ⟨127616, by rfl⟩ : syracuseStep 680621 = 255233) (by norm_num)
theorem B680645 : Blo 451781 680645 := bbase (se 4 (by rfl) ⟨63810, by rfl⟩ : syracuseStep 680645 = 127621) (by norm_num)
theorem B680669 : Blo 451781 680669 := bbase (se 3 (by rfl) ⟨127625, by rfl⟩ : syracuseStep 680669 = 255251) (by norm_num)
theorem B680693 : Blo 451781 680693 := bbase (se 5 (by rfl) ⟨31907, by rfl⟩ : syracuseStep 680693 = 63815) (by norm_num)
theorem B680717 : Blo 451781 680717 := bbase (se 3 (by rfl) ⟨127634, by rfl⟩ : syracuseStep 680717 = 255269) (by norm_num)
theorem B680741 : Blo 451781 680741 := bbase (se 4 (by rfl) ⟨63819, by rfl⟩ : syracuseStep 680741 = 127639) (by norm_num)
theorem B680765 : Blo 451781 680765 := bbase (se 3 (by rfl) ⟨127643, by rfl⟩ : syracuseStep 680765 = 255287) (by norm_num)
theorem B648013 : Blo 451781 648013 := bbase (se 3 (by rfl) ⟨121502, by rfl⟩ : syracuseStep 648013 = 243005) (by norm_num)
theorem B680789 : Blo 451781 680789 := bbase (se 9 (by rfl) ⟨1994, by rfl⟩ : syracuseStep 680789 = 3989) (by norm_num)
theorem B680813 : Blo 451781 680813 := bbase (se 3 (by rfl) ⟨127652, by rfl⟩ : syracuseStep 680813 = 255305) (by norm_num)
theorem B1532789 : Blo 451781 1532789 := bbase (se 5 (by rfl) ⟨71849, by rfl⟩ : syracuseStep 1532789 = 143699) (by norm_num)
theorem B680837 : Blo 451781 680837 := bbase (se 4 (by rfl) ⟨63828, by rfl⟩ : syracuseStep 680837 = 127657) (by norm_num)
theorem B680861 : Blo 451781 680861 := bbase (se 3 (by rfl) ⟨127661, by rfl⟩ : syracuseStep 680861 = 255323) (by norm_num)
theorem B517045 : Blo 451781 517045 := bbase (se 5 (by rfl) ⟨24236, by rfl⟩ : syracuseStep 517045 = 48473) (by norm_num)
theorem B680885 : Blo 451781 680885 := bbase (se 5 (by rfl) ⟨31916, by rfl⟩ : syracuseStep 680885 = 63833) (by norm_num)
theorem B680909 : Blo 451781 680909 := bbase (se 3 (by rfl) ⟨127670, by rfl⟩ : syracuseStep 680909 = 255341) (by norm_num)
theorem B680933 : Blo 451781 680933 := bbase (se 4 (by rfl) ⟨63837, by rfl⟩ : syracuseStep 680933 = 127675) (by norm_num)
theorem B680957 : Blo 451781 680957 := bbase (se 3 (by rfl) ⟨127679, by rfl⟩ : syracuseStep 680957 = 255359) (by norm_num)
theorem B582661 : Blo 451781 582661 := bbase (se 4 (by rfl) ⟨54624, by rfl⟩ : syracuseStep 582661 = 109249) (by norm_num)
theorem B680981 : Blo 451781 680981 := bbase (se 6 (by rfl) ⟨15960, by rfl⟩ : syracuseStep 680981 = 31921) (by norm_num)
theorem B681005 : Blo 451781 681005 := bbase (se 3 (by rfl) ⟨127688, by rfl⟩ : syracuseStep 681005 = 255377) (by norm_num)
theorem B615485 : Blo 451781 615485 := bbase (se 3 (by rfl) ⟨115403, by rfl⟩ : syracuseStep 615485 = 230807) (by norm_num)
theorem B484417 : Blo 451781 484417 := bbase (se 2 (by rfl) ⟨181656, by rfl⟩ : syracuseStep 484417 = 363313) (by norm_num)
theorem B681029 : Blo 451781 681029 := bbase (se 4 (by rfl) ⟨63846, by rfl⟩ : syracuseStep 681029 = 127693) (by norm_num)
theorem B681053 : Blo 451781 681053 := bbase (se 3 (by rfl) ⟨127697, by rfl⟩ : syracuseStep 681053 = 255395) (by norm_num)
theorem B3433589 : Blo 451781 3433589 := bbase (se 5 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 3433589 = 321899) (by norm_num)
theorem B681077 : Blo 451781 681077 := bbase (se 5 (by rfl) ⟨31925, by rfl⟩ : syracuseStep 681077 = 63851) (by norm_num)
theorem B484489 : Blo 451781 484489 := bbase (se 2 (by rfl) ⟨181683, by rfl⟩ : syracuseStep 484489 = 363367) (by norm_num)
theorem B681101 : Blo 451781 681101 := bbase (se 3 (by rfl) ⟨127706, by rfl⟩ : syracuseStep 681101 = 255413) (by norm_num)
theorem B681125 : Blo 451781 681125 := bbase (se 4 (by rfl) ⟨63855, by rfl⟩ : syracuseStep 681125 = 127711) (by norm_num)
theorem B681149 : Blo 451781 681149 := bbase (se 3 (by rfl) ⟨127715, by rfl⟩ : syracuseStep 681149 = 255431) (by norm_num)
theorem B681173 : Blo 451781 681173 := bbase (se 7 (by rfl) ⟨7982, by rfl⟩ : syracuseStep 681173 = 15965) (by norm_num)
theorem B1631461 : Blo 451781 1631461 := bbase (se 4 (by rfl) ⟨152949, by rfl⟩ : syracuseStep 1631461 = 305899) (by norm_num)
theorem B681197 : Blo 451781 681197 := bbase (se 3 (by rfl) ⟨127724, by rfl⟩ : syracuseStep 681197 = 255449) (by norm_num)
theorem B1729781 : Blo 451781 1729781 := bbase (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) (by norm_num)
theorem B681221 : Blo 451781 681221 := bbase (se 4 (by rfl) ⟨63864, by rfl⟩ : syracuseStep 681221 = 127729) (by norm_num)
theorem B681245 : Blo 451781 681245 := bbase (se 3 (by rfl) ⟨127733, by rfl⟩ : syracuseStep 681245 = 255467) (by norm_num)
theorem B1533221 : Blo 451781 1533221 := bbase (se 4 (by rfl) ⟨143739, by rfl⟩ : syracuseStep 1533221 = 287479) (by norm_num)
theorem B681269 : Blo 451781 681269 := bbase (se 5 (by rfl) ⟨31934, by rfl⟩ : syracuseStep 681269 = 63869) (by norm_num)
theorem B1402181 : Blo 451781 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B681293 : Blo 451781 681293 := bbase (se 3 (by rfl) ⟨127742, by rfl⟩ : syracuseStep 681293 = 255485) (by norm_num)
theorem B681317 : Blo 451781 681317 := bbase (se 4 (by rfl) ⟨63873, by rfl⟩ : syracuseStep 681317 = 127747) (by norm_num)
theorem B1631605 : Blo 451781 1631605 := bbase (se 5 (by rfl) ⟨76481, by rfl⟩ : syracuseStep 1631605 = 152963) (by norm_num)
theorem B681341 : Blo 451781 681341 := bbase (se 3 (by rfl) ⟨127751, by rfl⟩ : syracuseStep 681341 = 255503) (by norm_num)
theorem B681365 : Blo 451781 681365 := bbase (se 6 (by rfl) ⟨15969, by rfl⟩ : syracuseStep 681365 = 31939) (by norm_num)
theorem B648605 : Blo 451781 648605 := bbase (se 3 (by rfl) ⟨121613, by rfl⟩ : syracuseStep 648605 = 243227) (by norm_num)
theorem B681389 : Blo 451781 681389 := bbase (se 3 (by rfl) ⟨127760, by rfl⟩ : syracuseStep 681389 = 255521) (by norm_num)
theorem B517573 : Blo 451781 517573 := bbase (se 4 (by rfl) ⟨48522, by rfl⟩ : syracuseStep 517573 = 97045) (by norm_num)
theorem B681413 : Blo 451781 681413 := bbase (se 4 (by rfl) ⟨63882, by rfl⟩ : syracuseStep 681413 = 127765) (by norm_num)
theorem B681437 : Blo 451781 681437 := bbase (se 3 (by rfl) ⟨127769, by rfl⟩ : syracuseStep 681437 = 255539) (by norm_num)
theorem B648685 : Blo 451781 648685 := bbase (se 3 (by rfl) ⟨121628, by rfl⟩ : syracuseStep 648685 = 243257) (by norm_num)
theorem B681461 : Blo 451781 681461 := bbase (se 5 (by rfl) ⟨31943, by rfl⟩ : syracuseStep 681461 = 63887) (by norm_num)
theorem B484861 : Blo 451781 484861 := bbase (se 3 (by rfl) ⟨90911, by rfl⟩ : syracuseStep 484861 = 181823) (by norm_num)
theorem B681485 : Blo 451781 681485 := bbase (se 3 (by rfl) ⟨127778, by rfl⟩ : syracuseStep 681485 = 255557) (by norm_num)
theorem B1730069 : Blo 451781 1730069 := bbase (se 6 (by rfl) ⟨40548, by rfl⟩ : syracuseStep 1730069 = 81097) (by norm_num)
theorem B681509 : Blo 451781 681509 := bbase (se 4 (by rfl) ⟨63891, by rfl⟩ : syracuseStep 681509 = 127783) (by norm_num)
theorem B2188853 : Blo 451781 2188853 := bbase (se 5 (by rfl) ⟨102602, by rfl⟩ : syracuseStep 2188853 = 205205) (by norm_num)
theorem B681533 : Blo 451781 681533 := bbase (se 3 (by rfl) ⟨127787, by rfl⟩ : syracuseStep 681533 = 255575) (by norm_num)
theorem B681557 : Blo 451781 681557 := bbase (se 8 (by rfl) ⟨3993, by rfl⟩ : syracuseStep 681557 = 7987) (by norm_num)
theorem B648805 : Blo 451781 648805 := bbase (se 4 (by rfl) ⟨60825, by rfl⟩ : syracuseStep 648805 = 121651) (by norm_num)
theorem B681581 : Blo 451781 681581 := bbase (se 3 (by rfl) ⟨127796, by rfl⟩ : syracuseStep 681581 = 255593) (by norm_num)
theorem B681605 : Blo 451781 681605 := bbase (se 4 (by rfl) ⟨63900, by rfl⟩ : syracuseStep 681605 = 127801) (by norm_num)
theorem B681629 : Blo 451781 681629 := bbase (se 3 (by rfl) ⟨127805, by rfl⟩ : syracuseStep 681629 = 255611) (by norm_num)
theorem B681653 : Blo 451781 681653 := bbase (se 5 (by rfl) ⟨31952, by rfl⟩ : syracuseStep 681653 = 63905) (by norm_num)
theorem B648901 : Blo 451781 648901 := bbase (se 4 (by rfl) ⟨60834, by rfl⟩ : syracuseStep 648901 = 121669) (by norm_num)
theorem B681677 : Blo 451781 681677 := bbase (se 3 (by rfl) ⟨127814, by rfl⟩ : syracuseStep 681677 = 255629) (by norm_num)
theorem B1533653 : Blo 451781 1533653 := bbase (se 7 (by rfl) ⟨17972, by rfl⟩ : syracuseStep 1533653 = 35945) (by norm_num)
theorem B681701 : Blo 451781 681701 := bbase (se 4 (by rfl) ⟨63909, by rfl⟩ : syracuseStep 681701 = 127819) (by norm_num)
theorem B681725 : Blo 451781 681725 := bbase (se 3 (by rfl) ⟨127823, by rfl⟩ : syracuseStep 681725 = 255647) (by norm_num)
theorem B681749 : Blo 451781 681749 := bbase (se 6 (by rfl) ⟨15978, by rfl⟩ : syracuseStep 681749 = 31957) (by norm_num)
theorem B681773 : Blo 451781 681773 := bbase (se 3 (by rfl) ⟨127832, by rfl⟩ : syracuseStep 681773 = 255665) (by norm_num)
theorem B681797 : Blo 451781 681797 := bbase (se 4 (by rfl) ⟨63918, by rfl⟩ : syracuseStep 681797 = 127837) (by norm_num)
theorem B681821 : Blo 451781 681821 := bbase (se 3 (by rfl) ⟨127841, by rfl⟩ : syracuseStep 681821 = 255683) (by norm_num)
theorem B485237 : Blo 451781 485237 := bbase (se 5 (by rfl) ⟨22745, by rfl⟩ : syracuseStep 485237 = 45491) (by norm_num)
theorem B681845 : Blo 451781 681845 := bbase (se 5 (by rfl) ⟨31961, by rfl⟩ : syracuseStep 681845 = 63923) (by norm_num)
theorem B681869 : Blo 451781 681869 := bbase (se 3 (by rfl) ⟨127850, by rfl⟩ : syracuseStep 681869 = 255701) (by norm_num)
theorem B681893 : Blo 451781 681893 := bbase (se 4 (by rfl) ⟨63927, by rfl⟩ : syracuseStep 681893 = 127855) (by norm_num)
theorem B485309 : Blo 451781 485309 := bbase (se 3 (by rfl) ⟨90995, by rfl⟩ : syracuseStep 485309 = 181991) (by norm_num)
theorem B681917 : Blo 451781 681917 := bbase (se 3 (by rfl) ⟨127859, by rfl⟩ : syracuseStep 681917 = 255719) (by norm_num)
theorem B681941 : Blo 451781 681941 := bbase (se 7 (by rfl) ⟨7991, by rfl⟩ : syracuseStep 681941 = 15983) (by norm_num)
theorem B550885 : Blo 451781 550885 := bbase (se 4 (by rfl) ⟨51645, by rfl⟩ : syracuseStep 550885 = 103291) (by norm_num)
theorem B681965 : Blo 451781 681965 := bbase (se 3 (by rfl) ⟨127868, by rfl⟩ : syracuseStep 681965 = 255737) (by norm_num)
theorem B681989 : Blo 451781 681989 := bbase (se 4 (by rfl) ⟨63936, by rfl⟩ : syracuseStep 681989 = 127873) (by norm_num)
theorem B682013 : Blo 451781 682013 := bbase (se 3 (by rfl) ⟨127877, by rfl⟩ : syracuseStep 682013 = 255755) (by norm_num)
theorem B682037 : Blo 451781 682037 := bbase (se 5 (by rfl) ⟨31970, by rfl⟩ : syracuseStep 682037 = 63941) (by norm_num)
theorem B682061 : Blo 451781 682061 := bbase (se 3 (by rfl) ⟨127886, by rfl⟩ : syracuseStep 682061 = 255773) (by norm_num)
theorem B682085 : Blo 451781 682085 := bbase (se 4 (by rfl) ⟨63945, by rfl⟩ : syracuseStep 682085 = 127891) (by norm_num)
theorem B485497 : Blo 451781 485497 := bbase (se 2 (by rfl) ⟨182061, by rfl⟩ : syracuseStep 485497 = 364123) (by norm_num)
theorem B682109 : Blo 451781 682109 := bbase (se 3 (by rfl) ⟨127895, by rfl⟩ : syracuseStep 682109 = 255791) (by norm_num)
theorem B1534085 : Blo 451781 1534085 := bbase (se 4 (by rfl) ⟨143820, by rfl⟩ : syracuseStep 1534085 = 287641) (by norm_num)
theorem B682133 : Blo 451781 682133 := bbase (se 6 (by rfl) ⟨15987, by rfl⟩ : syracuseStep 682133 = 31975) (by norm_num)
theorem B682157 : Blo 451781 682157 := bbase (se 3 (by rfl) ⟨127904, by rfl⟩ : syracuseStep 682157 = 255809) (by norm_num)
theorem B682181 : Blo 451781 682181 := bbase (se 4 (by rfl) ⟨63954, by rfl⟩ : syracuseStep 682181 = 127909) (by norm_num)
theorem B682205 : Blo 451781 682205 := bbase (se 3 (by rfl) ⟨127913, by rfl⟩ : syracuseStep 682205 = 255827) (by norm_num)
theorem B682229 : Blo 451781 682229 := bbase (se 5 (by rfl) ⟨31979, by rfl⟩ : syracuseStep 682229 = 63959) (by norm_num)
theorem B682253 : Blo 451781 682253 := bbase (se 3 (by rfl) ⟨127922, by rfl⟩ : syracuseStep 682253 = 255845) (by norm_num)
theorem B682277 : Blo 451781 682277 := bbase (se 4 (by rfl) ⟨63963, by rfl⟩ : syracuseStep 682277 = 127927) (by norm_num)
theorem B485681 : Blo 451781 485681 := bbase (se 2 (by rfl) ⟨182130, by rfl⟩ : syracuseStep 485681 = 364261) (by norm_num)
theorem B2287925 : Blo 451781 2287925 := bbase (se 5 (by rfl) ⟨107246, by rfl⟩ : syracuseStep 2287925 = 214493) (by norm_num)
theorem B682301 : Blo 451781 682301 := bbase (se 3 (by rfl) ⟨127931, by rfl⟩ : syracuseStep 682301 = 255863) (by norm_num)
theorem B682325 : Blo 451781 682325 := bbase (se 10 (by rfl) ⟨999, by rfl⟩ : syracuseStep 682325 = 1999) (by norm_num)
theorem B682349 : Blo 451781 682349 := bbase (se 3 (by rfl) ⟨127940, by rfl⟩ : syracuseStep 682349 = 255881) (by norm_num)
theorem B682373 : Blo 451781 682373 := bbase (se 4 (by rfl) ⟨63972, by rfl⟩ : syracuseStep 682373 = 127945) (by norm_num)
theorem B1304981 : Blo 451781 1304981 := bbase (se 6 (by rfl) ⟨30585, by rfl⟩ : syracuseStep 1304981 = 61171) (by norm_num)
theorem B682397 : Blo 451781 682397 := bbase (se 3 (by rfl) ⟨127949, by rfl⟩ : syracuseStep 682397 = 255899) (by norm_num)
theorem B682421 : Blo 451781 682421 := bbase (se 5 (by rfl) ⟨31988, by rfl⟩ : syracuseStep 682421 = 63977) (by norm_num)
theorem B682445 : Blo 451781 682445 := bbase (se 3 (by rfl) ⟨127958, by rfl⟩ : syracuseStep 682445 = 255917) (by norm_num)
theorem B682469 : Blo 451781 682469 := bbase (se 4 (by rfl) ⟨63981, by rfl⟩ : syracuseStep 682469 = 127963) (by norm_num)
theorem B2583029 : Blo 451781 2583029 := bbase (se 5 (by rfl) ⟨121079, by rfl⟩ : syracuseStep 2583029 = 242159) (by norm_num)
theorem B682493 : Blo 451781 682493 := bbase (se 3 (by rfl) ⟨127967, by rfl⟩ : syracuseStep 682493 = 255935) (by norm_num)
theorem B682517 : Blo 451781 682517 := bbase (se 6 (by rfl) ⟨15996, by rfl⟩ : syracuseStep 682517 = 31993) (by norm_num)
theorem B682541 : Blo 451781 682541 := bbase (se 3 (by rfl) ⟨127976, by rfl⟩ : syracuseStep 682541 = 255953) (by norm_num)
theorem B1534517 : Blo 451781 1534517 := bbase (se 5 (by rfl) ⟨71930, by rfl⟩ : syracuseStep 1534517 = 143861) (by norm_num)
theorem B682565 : Blo 451781 682565 := bbase (se 4 (by rfl) ⟨63990, by rfl⟩ : syracuseStep 682565 = 127981) (by norm_num)
theorem B682589 : Blo 451781 682589 := bbase (se 3 (by rfl) ⟨127985, by rfl⟩ : syracuseStep 682589 = 255971) (by norm_num)
theorem B682613 : Blo 451781 682613 := bbase (se 5 (by rfl) ⟨31997, by rfl⟩ : syracuseStep 682613 = 63995) (by norm_num)
theorem B682637 : Blo 451781 682637 := bbase (se 3 (by rfl) ⟨127994, by rfl⟩ : syracuseStep 682637 = 255989) (by norm_num)
theorem B682661 : Blo 451781 682661 := bbase (se 4 (by rfl) ⟨63999, by rfl⟩ : syracuseStep 682661 = 127999) (by norm_num)
theorem B682685 : Blo 451781 682685 := bbase (se 3 (by rfl) ⟨128003, by rfl⟩ : syracuseStep 682685 = 256007) (by norm_num)
theorem B682709 : Blo 451781 682709 := bbase (se 7 (by rfl) ⟨8000, by rfl⟩ : syracuseStep 682709 = 16001) (by norm_num)
theorem B682733 : Blo 451781 682733 := bbase (se 3 (by rfl) ⟨128012, by rfl⟩ : syracuseStep 682733 = 256025) (by norm_num)
theorem B682757 : Blo 451781 682757 := bbase (se 4 (by rfl) ⟨64008, by rfl⟩ : syracuseStep 682757 = 128017) (by norm_num)
theorem B682781 : Blo 451781 682781 := bbase (se 3 (by rfl) ⟨128021, by rfl⟩ : syracuseStep 682781 = 256043) (by norm_num)
theorem B1567525 : Blo 451781 1567525 := bbase (se 4 (by rfl) ⟨146955, by rfl⟩ : syracuseStep 1567525 = 293911) (by norm_num)
theorem B551729 : Blo 451781 551729 := bbase (se 2 (by rfl) ⟨206898, by rfl⟩ : syracuseStep 551729 = 413797) (by norm_num)
theorem B682805 : Blo 451781 682805 := bbase (se 5 (by rfl) ⟨32006, by rfl⟩ : syracuseStep 682805 = 64013) (by norm_num)
theorem B682829 : Blo 451781 682829 := bbase (se 3 (by rfl) ⟨128030, by rfl⟩ : syracuseStep 682829 = 256061) (by norm_num)
theorem B23554901 : Blo 451781 23554901 := bbase (se 9 (by rfl) ⟨69008, by rfl⟩ : syracuseStep 23554901 = 138017) (by norm_num)
theorem B682853 : Blo 451781 682853 := bbase (se 4 (by rfl) ⟨64017, by rfl⟩ : syracuseStep 682853 = 128035) (by norm_num)
theorem B682877 : Blo 451781 682877 := bbase (se 3 (by rfl) ⟨128039, by rfl⟩ : syracuseStep 682877 = 256079) (by norm_num)
theorem B682901 : Blo 451781 682901 := bbase (se 6 (by rfl) ⟨16005, by rfl⟩ : syracuseStep 682901 = 32011) (by norm_num)
theorem B682925 : Blo 451781 682925 := bbase (se 3 (by rfl) ⟨128048, by rfl⟩ : syracuseStep 682925 = 256097) (by norm_num)
theorem B682949 : Blo 451781 682949 := bbase (se 4 (by rfl) ⟨64026, by rfl⟩ : syracuseStep 682949 = 128053) (by norm_num)
theorem B682973 : Blo 451781 682973 := bbase (se 3 (by rfl) ⟨128057, by rfl⟩ : syracuseStep 682973 = 256115) (by norm_num)
theorem B1534949 : Blo 451781 1534949 := bbase (se 4 (by rfl) ⟨143901, by rfl⟩ : syracuseStep 1534949 = 287803) (by norm_num)
theorem B682997 : Blo 451781 682997 := bbase (se 5 (by rfl) ⟨32015, by rfl⟩ : syracuseStep 682997 = 64031) (by norm_num)
theorem B683021 : Blo 451781 683021 := bbase (se 3 (by rfl) ⟨128066, by rfl⟩ : syracuseStep 683021 = 256133) (by norm_num)
theorem B486433 : Blo 451781 486433 := bbase (se 2 (by rfl) ⟨182412, by rfl⟩ : syracuseStep 486433 = 364825) (by norm_num)
theorem B683045 : Blo 451781 683045 := bbase (se 4 (by rfl) ⟨64035, by rfl⟩ : syracuseStep 683045 = 128071) (by norm_num)
theorem B519229 : Blo 451781 519229 := bbase (se 3 (by rfl) ⟨97355, by rfl⟩ : syracuseStep 519229 = 194711) (by norm_num)
theorem B683069 : Blo 451781 683069 := bbase (se 3 (by rfl) ⟨128075, by rfl⟩ : syracuseStep 683069 = 256151) (by norm_num)
theorem B683093 : Blo 451781 683093 := bbase (se 8 (by rfl) ⟨4002, by rfl⟩ : syracuseStep 683093 = 8005) (by norm_num)
theorem B486505 : Blo 451781 486505 := bbase (se 2 (by rfl) ⟨182439, by rfl⟩ : syracuseStep 486505 = 364879) (by norm_num)
theorem B683117 : Blo 451781 683117 := bbase (se 3 (by rfl) ⟨128084, by rfl⟩ : syracuseStep 683117 = 256169) (by norm_num)
theorem B683141 : Blo 451781 683141 := bbase (se 4 (by rfl) ⟨64044, by rfl⟩ : syracuseStep 683141 = 128089) (by norm_num)
theorem B683165 : Blo 451781 683165 := bbase (se 3 (by rfl) ⟨128093, by rfl⟩ : syracuseStep 683165 = 256187) (by norm_num)
theorem B683189 : Blo 451781 683189 := bbase (se 5 (by rfl) ⟨32024, by rfl⟩ : syracuseStep 683189 = 64049) (by norm_num)
theorem B683213 : Blo 451781 683213 := bbase (se 3 (by rfl) ⟨128102, by rfl⟩ : syracuseStep 683213 = 256205) (by norm_num)
theorem B683237 : Blo 451781 683237 := bbase (se 4 (by rfl) ⟨64053, by rfl⟩ : syracuseStep 683237 = 128107) (by norm_num)
theorem B683261 : Blo 451781 683261 := bbase (se 3 (by rfl) ⟨128111, by rfl⟩ : syracuseStep 683261 = 256223) (by norm_num)
theorem B683285 : Blo 451781 683285 := bbase (se 6 (by rfl) ⟨16014, by rfl⟩ : syracuseStep 683285 = 32029) (by norm_num)
theorem B486685 : Blo 451781 486685 := bbase (se 3 (by rfl) ⟨91253, by rfl⟩ : syracuseStep 486685 = 182507) (by norm_num)
theorem B683309 : Blo 451781 683309 := bbase (se 3 (by rfl) ⟨128120, by rfl⟩ : syracuseStep 683309 = 256241) (by norm_num)
theorem B683333 : Blo 451781 683333 := bbase (se 4 (by rfl) ⟨64062, by rfl⟩ : syracuseStep 683333 = 128125) (by norm_num)
theorem B683357 : Blo 451781 683357 := bbase (se 3 (by rfl) ⟨128129, by rfl⟩ : syracuseStep 683357 = 256259) (by norm_num)
theorem B683381 : Blo 451781 683381 := bbase (se 5 (by rfl) ⟨32033, by rfl⟩ : syracuseStep 683381 = 64067) (by norm_num)
theorem B683405 : Blo 451781 683405 := bbase (se 3 (by rfl) ⟨128138, by rfl⟩ : syracuseStep 683405 = 256277) (by norm_num)
theorem B1535381 : Blo 451781 1535381 := bbase (se 6 (by rfl) ⟨35985, by rfl⟩ : syracuseStep 1535381 = 71971) (by norm_num)
theorem B683429 : Blo 451781 683429 := bbase (se 4 (by rfl) ⟨64071, by rfl⟩ : syracuseStep 683429 = 128143) (by norm_num)
theorem B683453 : Blo 451781 683453 := bbase (se 3 (by rfl) ⟨128147, by rfl⟩ : syracuseStep 683453 = 256295) (by norm_num)
theorem B683477 : Blo 451781 683477 := bbase (se 7 (by rfl) ⟨8009, by rfl⟩ : syracuseStep 683477 = 16019) (by norm_num)
theorem B683501 : Blo 451781 683501 := bbase (se 3 (by rfl) ⟨128156, by rfl⟩ : syracuseStep 683501 = 256313) (by norm_num)
theorem B683525 : Blo 451781 683525 := bbase (se 4 (by rfl) ⟨64080, by rfl⟩ : syracuseStep 683525 = 128161) (by norm_num)
theorem B683549 : Blo 451781 683549 := bbase (se 3 (by rfl) ⟨128165, by rfl⟩ : syracuseStep 683549 = 256331) (by norm_num)
theorem B683573 : Blo 451781 683573 := bbase (se 5 (by rfl) ⟨32042, by rfl⟩ : syracuseStep 683573 = 64085) (by norm_num)
theorem B2289221 : Blo 451781 2289221 := bbase (se 4 (by rfl) ⟨214614, by rfl⟩ : syracuseStep 2289221 = 429229) (by norm_num)
theorem B683597 : Blo 451781 683597 := bbase (se 3 (by rfl) ⟨128174, by rfl⟩ : syracuseStep 683597 = 256349) (by norm_num)
theorem B683621 : Blo 451781 683621 := bbase (se 4 (by rfl) ⟨64089, by rfl⟩ : syracuseStep 683621 = 128179) (by norm_num)
theorem B552565 : Blo 451781 552565 := bbase (se 5 (by rfl) ⟨25901, by rfl⟩ : syracuseStep 552565 = 51803) (by norm_num)
theorem B683645 : Blo 451781 683645 := bbase (se 3 (by rfl) ⟨128183, by rfl⟩ : syracuseStep 683645 = 256367) (by norm_num)
theorem B683669 : Blo 451781 683669 := bbase (se 6 (by rfl) ⟨16023, by rfl⟩ : syracuseStep 683669 = 32047) (by norm_num)
theorem B1535813 : Blo 451781 1535813 := bbase (se 4 (by rfl) ⟨143982, by rfl⟩ : syracuseStep 1535813 = 287965) (by norm_num)
theorem B815125 : Blo 451781 815125 := bbase (se 6 (by rfl) ⟨19104, by rfl⟩ : syracuseStep 815125 = 38209) (by norm_num)
theorem B815285 : Blo 451781 815285 := bbase (se 5 (by rfl) ⟨38216, by rfl⟩ : syracuseStep 815285 = 76433) (by norm_num)
theorem B1536245 : Blo 451781 1536245 := bbase (se 5 (by rfl) ⟨72011, by rfl⟩ : syracuseStep 1536245 = 144023) (by norm_num)
theorem B1536677 : Blo 451781 1536677 := bbase (se 4 (by rfl) ⟨144063, by rfl⟩ : syracuseStep 1536677 = 288127) (by norm_num)
theorem B1143629 : Blo 451781 1143629 := bbase (se 3 (by rfl) ⟨214430, by rfl⟩ : syracuseStep 1143629 = 428861) (by norm_num)
theorem B2290517 : Blo 451781 2290517 := bbase (se 9 (by rfl) ⟨6710, by rfl⟩ : syracuseStep 2290517 = 13421) (by norm_num)
theorem B2749301 : Blo 451781 2749301 := bbase (se 5 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 2749301 = 257747) (by norm_num)
theorem B3666869 : Blo 451781 3666869 := bbase (se 5 (by rfl) ⟨171884, by rfl⟩ : syracuseStep 3666869 = 343769) (by norm_num)
theorem B553969 : Blo 451781 553969 := bbase (se 2 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 553969 = 415477) (by norm_num)
theorem B1143821 : Blo 451781 1143821 := bbase (se 3 (by rfl) ⟨214466, by rfl⟩ : syracuseStep 1143821 = 428933) (by norm_num)
theorem B1537109 : Blo 451781 1537109 := bbase (se 8 (by rfl) ⟨9006, by rfl⟩ : syracuseStep 1537109 = 18013) (by norm_num)
theorem B816365 : Blo 451781 816365 := bbase (se 3 (by rfl) ⟨153068, by rfl⟩ : syracuseStep 816365 = 306137) (by norm_num)
theorem B1471733 : Blo 451781 1471733 := bbase (se 5 (by rfl) ⟨68987, by rfl⟩ : syracuseStep 1471733 = 137975) (by norm_num)
theorem B2520341 : Blo 451781 2520341 := bbase (se 6 (by rfl) ⟨59070, by rfl⟩ : syracuseStep 2520341 = 118141) (by norm_num)
theorem B1144165 : Blo 451781 1144165 := bbase (se 4 (by rfl) ⟨107265, by rfl⟩ : syracuseStep 1144165 = 214531) (by norm_num)
theorem B816509 : Blo 451781 816509 := bbase (se 3 (by rfl) ⟨153095, by rfl⟩ : syracuseStep 816509 = 306191) (by norm_num)
theorem B1144277 : Blo 451781 1144277 := bbase (se 7 (by rfl) ⟨13409, by rfl⟩ : syracuseStep 1144277 = 26819) (by norm_num)
theorem B1537541 : Blo 451781 1537541 := bbase (se 4 (by rfl) ⟨144144, by rfl⟩ : syracuseStep 1537541 = 288289) (by norm_num)
theorem B554573 : Blo 451781 554573 := bbase (se 3 (by rfl) ⟨103982, by rfl⟩ : syracuseStep 554573 = 207965) (by norm_num)
theorem B1144469 : Blo 451781 1144469 := bbase (se 6 (by rfl) ⟨26823, by rfl⟩ : syracuseStep 1144469 = 53647) (by norm_num)
theorem B3143477 : Blo 451781 3143477 := bbase (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) (by norm_num)
theorem B554813 : Blo 451781 554813 := bbase (se 3 (by rfl) ⟨104027, by rfl⟩ : syracuseStep 554813 = 208055) (by norm_num)
theorem B1374101 : Blo 451781 1374101 := bbase (se 6 (by rfl) ⟨32205, by rfl⟩ : syracuseStep 1374101 = 64411) (by norm_num)
theorem B1537973 : Blo 451781 1537973 := bbase (se 5 (by rfl) ⟨72092, by rfl⟩ : syracuseStep 1537973 = 144185) (by norm_num)
theorem B1144813 : Blo 451781 1144813 := bbase (se 3 (by rfl) ⟨214652, by rfl⟩ : syracuseStep 1144813 = 429305) (by norm_num)
theorem B1144925 : Blo 451781 1144925 := bbase (se 3 (by rfl) ⟨214673, by rfl⟩ : syracuseStep 1144925 = 429347) (by norm_num)
theorem B2291813 : Blo 451781 2291813 := bbase (se 4 (by rfl) ⟨214857, by rfl⟩ : syracuseStep 2291813 = 429715) (by norm_num)
theorem B1964245 : Blo 451781 1964245 := bbase (se 7 (by rfl) ⟨23018, by rfl⟩ : syracuseStep 1964245 = 46037) (by norm_num)
theorem B1145117 : Blo 451781 1145117 := bbase (se 3 (by rfl) ⟨214709, by rfl⟩ : syracuseStep 1145117 = 429419) (by norm_num)
theorem B1145461 : Blo 451781 1145461 := bbase (se 5 (by rfl) ⟨53693, by rfl⟩ : syracuseStep 1145461 = 107387) (by norm_num)
theorem B1047181 : Blo 451781 1047181 := bbase (se 3 (by rfl) ⟨196346, by rfl⟩ : syracuseStep 1047181 = 392693) (by norm_num)
theorem B1931941 : Blo 451781 1931941 := bbase (se 4 (by rfl) ⟨181119, by rfl⟩ : syracuseStep 1931941 = 362239) (by norm_num)
theorem B916157 : Blo 451781 916157 := bbase (se 3 (by rfl) ⟨171779, by rfl⟩ : syracuseStep 916157 = 343559) (by norm_num)
theorem B1145573 : Blo 451781 1145573 := bbase (se 4 (by rfl) ⟨107397, by rfl⟩ : syracuseStep 1145573 = 214795) (by norm_num)
theorem B1178389 : Blo 451781 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B2063141 : Blo 451781 2063141 := bbase (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) (by norm_num)
theorem B2456405 : Blo 451781 2456405 := bbase (se 9 (by rfl) ⟨7196, by rfl⟩ : syracuseStep 2456405 = 14393) (by norm_num)
theorem B2915189 : Blo 451781 2915189 := bbase (se 5 (by rfl) ⟨136649, by rfl⟩ : syracuseStep 2915189 = 273299) (by norm_num)
theorem B1145765 : Blo 451781 1145765 := bbase (se 4 (by rfl) ⟨107415, by rfl⟩ : syracuseStep 1145765 = 214831) (by norm_num)
theorem B7076821 : Blo 451781 7076821 := bbase (se 7 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 7076821 = 165863) (by norm_num)
theorem B1146109 : Blo 451781 1146109 := bbase (se 3 (by rfl) ⟨214895, by rfl⟩ : syracuseStep 1146109 = 429791) (by norm_num)
theorem B458005 : Blo 451781 458005 := bbase (se 6 (by rfl) ⟨10734, by rfl⟩ : syracuseStep 458005 = 21469) (by norm_num)
theorem B1146221 : Blo 451781 1146221 := bbase (se 3 (by rfl) ⟨214916, by rfl⟩ : syracuseStep 1146221 = 429833) (by norm_num)
theorem B916853 : Blo 451781 916853 := bbase (se 5 (by rfl) ⟨42977, by rfl⟩ : syracuseStep 916853 = 85955) (by norm_num)
theorem B2293109 : Blo 451781 2293109 := bbase (se 5 (by rfl) ⟨107489, by rfl⟩ : syracuseStep 2293109 = 214979) (by norm_num)
theorem B3866069 : Blo 451781 3866069 := bbase (se 7 (by rfl) ⟨45305, by rfl⟩ : syracuseStep 3866069 = 90611) (by norm_num)
theorem B1146413 : Blo 451781 1146413 := bbase (se 3 (by rfl) ⟨214952, by rfl⟩ : syracuseStep 1146413 = 429905) (by norm_num)
theorem B491065 : Blo 451781 491065 := bbase (se 2 (by rfl) ⟨184149, by rfl⟩ : syracuseStep 491065 = 368299) (by norm_num)
theorem B917237 : Blo 451781 917237 := bbase (se 5 (by rfl) ⟨42995, by rfl⟩ : syracuseStep 917237 = 85991) (by norm_num)
theorem B1310453 : Blo 451781 1310453 := bbase (se 5 (by rfl) ⟨61427, by rfl⟩ : syracuseStep 1310453 = 122855) (by norm_num)
theorem B491377 : Blo 451781 491377 := bbase (se 2 (by rfl) ⟨184266, by rfl⟩ : syracuseStep 491377 = 368533) (by norm_num)
theorem B1146757 : Blo 451781 1146757 := bbase (se 4 (by rfl) ⟨107508, by rfl⟩ : syracuseStep 1146757 = 215017) (by norm_num)
theorem B1146869 : Blo 451781 1146869 := bbase (se 5 (by rfl) ⟨53759, by rfl⟩ : syracuseStep 1146869 = 107519) (by norm_num)
theorem B5177357 : Blo 451781 5177357 := bstep (se 3 (by rfl) ⟨970754, by rfl⟩ : syracuseStep 5177357 = 1941509) B1941509
theorem B458995 : Blo 451781 458995 := bstep (se 1 (by rfl) ⟨344246, by rfl⟩ : syracuseStep 458995 = 688493) B688493
theorem B2294243 : Blo 451781 2294243 := bstep (se 1 (by rfl) ⟨1720682, by rfl⟩ : syracuseStep 2294243 = 3441365) B3441365
theorem B688675 : Blo 451781 688675 := bstep (se 1 (by rfl) ⟨516506, by rfl⟩ : syracuseStep 688675 = 1033013) B1033013
theorem B2589317 : Blo 451781 2589317 := bstep (se 4 (by rfl) ⟨242748, by rfl⟩ : syracuseStep 2589317 = 485497) B485497
theorem B2458309 : Blo 451781 2458309 := bstep (se 4 (by rfl) ⟨230466, by rfl⟩ : syracuseStep 2458309 = 460933) B460933
theorem B1639217 : Blo 451781 1639217 := bstep (se 2 (by rfl) ⟨614706, by rfl⟩ : syracuseStep 1639217 = 1229413) B1229413
theorem B1016657 : Blo 451781 1016657 := bstep (se 2 (by rfl) ⟨381246, by rfl⟩ : syracuseStep 1016657 = 762493) B762493
theorem B1147729 : Blo 451781 1147729 := bstep (se 2 (by rfl) ⟨430398, by rfl⟩ : syracuseStep 1147729 = 860797) B860797
theorem B1016675 : Blo 451781 1016675 := bstep (se 1 (by rfl) ⟨762506, by rfl⟩ : syracuseStep 1016675 = 1525013) B1525013
theorem B19104709 : Blo 451781 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B1148003 : Blo 451781 1148003 := bstep (se 1 (by rfl) ⟨861002, by rfl⟩ : syracuseStep 1148003 = 1722005) B1722005
theorem B1016945 : Blo 451781 1016945 := bstep (se 2 (by rfl) ⟨381354, by rfl⟩ : syracuseStep 1016945 = 762709) B762709
theorem B1016963 : Blo 451781 1016963 := bstep (se 1 (by rfl) ⟨762722, by rfl⟩ : syracuseStep 1016963 = 1525445) B1525445
theorem B689393 : Blo 451781 689393 := bstep (se 2 (by rfl) ⟨258522, by rfl⟩ : syracuseStep 689393 = 517045) B517045
theorem B2295053 : Blo 451781 2295053 := bstep (se 3 (by rfl) ⟨430322, by rfl⟩ : syracuseStep 2295053 = 860645) B860645
theorem B1148195 : Blo 451781 1148195 := bstep (se 1 (by rfl) ⟨861146, by rfl⟩ : syracuseStep 1148195 = 1722293) B1722293
theorem B2590001 : Blo 451781 2590001 := bstep (se 2 (by rfl) ⟨971250, by rfl⟩ : syracuseStep 2590001 = 1942501) B1942501
theorem B1017233 : Blo 451781 1017233 := bstep (se 2 (by rfl) ⟨381462, by rfl⟩ : syracuseStep 1017233 = 762925) B762925
theorem B1017251 : Blo 451781 1017251 := bstep (se 1 (by rfl) ⟨762938, by rfl⟩ : syracuseStep 1017251 = 1525877) B1525877
theorem B918947 : Blo 451781 918947 := bstep (se 1 (by rfl) ⟨689210, by rfl⟩ : syracuseStep 918947 = 1378421) B1378421
theorem B689635 : Blo 451781 689635 := bstep (se 1 (by rfl) ⟨517226, by rfl⟩ : syracuseStep 689635 = 1034453) B1034453
theorem B3507781 : Blo 451781 3507781 := bstep (se 4 (by rfl) ⟨328854, by rfl⟩ : syracuseStep 3507781 = 657709) B657709
theorem B1017521 : Blo 451781 1017521 := bstep (se 2 (by rfl) ⟨381570, by rfl⟩ : syracuseStep 1017521 = 763141) B763141
theorem B1017539 : Blo 451781 1017539 := bstep (se 1 (by rfl) ⟨763154, by rfl⟩ : syracuseStep 1017539 = 1526309) B1526309
theorem B460499 : Blo 451781 460499 := bstep (se 1 (by rfl) ⟨345374, by rfl⟩ : syracuseStep 460499 = 690749) B690749
theorem B526115 : Blo 451781 526115 := bstep (se 1 (by rfl) ⟨394586, by rfl⟩ : syracuseStep 526115 = 789173) B789173
theorem B690097 : Blo 451781 690097 := bstep (se 2 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 690097 = 517573) B517573
theorem B1017809 : Blo 451781 1017809 := bstep (se 2 (by rfl) ⟨381678, by rfl⟩ : syracuseStep 1017809 = 763357) B763357
theorem B1017827 : Blo 451781 1017827 := bstep (se 1 (by rfl) ⟨763370, by rfl⟩ : syracuseStep 1017827 = 1526741) B1526741
theorem B1149137 : Blo 451781 1149137 := bstep (se 2 (by rfl) ⟨430926, by rfl⟩ : syracuseStep 1149137 = 861853) B861853
theorem B1018097 : Blo 451781 1018097 := bstep (se 2 (by rfl) ⟨381786, by rfl⟩ : syracuseStep 1018097 = 763573) B763573
theorem B1018115 : Blo 451781 1018115 := bstep (se 1 (by rfl) ⟨763586, by rfl⟩ : syracuseStep 1018115 = 1527173) B1527173
theorem B1149187 : Blo 451781 1149187 := bstep (se 1 (by rfl) ⟨861890, by rfl⟩ : syracuseStep 1149187 = 1723781) B1723781
theorem B788867 : Blo 451781 788867 := bstep (se 1 (by rfl) ⟨591650, by rfl⟩ : syracuseStep 788867 = 1183301) B1183301
theorem B1149329 : Blo 451781 1149329 := bstep (se 2 (by rfl) ⟨430998, by rfl⟩ : syracuseStep 1149329 = 861997) B861997
theorem B1018385 : Blo 451781 1018385 := bstep (se 2 (by rfl) ⟨381894, by rfl⟩ : syracuseStep 1018385 = 763789) B763789
theorem B1018403 : Blo 451781 1018403 := bstep (se 1 (by rfl) ⟨763802, by rfl⟩ : syracuseStep 1018403 = 1527605) B1527605
theorem B2230861 : Blo 451781 2230861 := bstep (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) B836573
theorem B2591459 : Blo 451781 2591459 := bstep (se 1 (by rfl) ⟨1943594, by rfl⟩ : syracuseStep 2591459 = 3887189) B3887189
theorem B1936163 : Blo 451781 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B1018673 : Blo 451781 1018673 := bstep (se 2 (by rfl) ⟨382002, by rfl⟩ : syracuseStep 1018673 = 764005) B764005
theorem B1018691 : Blo 451781 1018691 := bstep (se 1 (by rfl) ⟨764018, by rfl⟩ : syracuseStep 1018691 = 1528037) B1528037
theorem B1641293 : Blo 451781 1641293 := bstep (se 3 (by rfl) ⟨307742, by rfl⟩ : syracuseStep 1641293 = 615485) B615485
theorem B5180273 : Blo 451781 5180273 := bstep (se 2 (by rfl) ⟨1942602, by rfl⟩ : syracuseStep 5180273 = 3885205) B3885205
theorem B2460557 : Blo 451781 2460557 := bstep (se 3 (by rfl) ⟨461354, by rfl⟩ : syracuseStep 2460557 = 922709) B922709
theorem B1018961 : Blo 451781 1018961 := bstep (se 2 (by rfl) ⟨382110, by rfl⟩ : syracuseStep 1018961 = 764221) B764221
theorem B1018979 : Blo 451781 1018979 := bstep (se 1 (by rfl) ⟨764234, by rfl⟩ : syracuseStep 1018979 = 1528469) B1528469
theorem B691363 : Blo 451781 691363 := bstep (se 1 (by rfl) ⟨518522, by rfl⟩ : syracuseStep 691363 = 1037045) B1037045
theorem B724145 : Blo 451781 724145 := bstep (se 2 (by rfl) ⟨271554, by rfl⟩ : syracuseStep 724145 = 543109) B543109
theorem B1019249 : Blo 451781 1019249 := bstep (se 2 (by rfl) ⟨382218, by rfl⟩ : syracuseStep 1019249 = 764437) B764437
theorem B1150321 : Blo 451781 1150321 := bstep (se 2 (by rfl) ⟨431370, by rfl⟩ : syracuseStep 1150321 = 862741) B862741
theorem B1019267 : Blo 451781 1019267 := bstep (se 1 (by rfl) ⟨764450, by rfl⟩ : syracuseStep 1019267 = 1528901) B1528901
theorem B1379747 : Blo 451781 1379747 := bstep (se 1 (by rfl) ⟨1034810, by rfl⟩ : syracuseStep 1379747 = 2069621) B2069621
theorem B3673613 : Blo 451781 3673613 := bstep (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) B1377605
theorem B2330147 : Blo 451781 2330147 := bstep (se 1 (by rfl) ⟨1747610, by rfl⟩ : syracuseStep 2330147 = 3495221) B3495221
theorem B1150595 : Blo 451781 1150595 := bstep (se 1 (by rfl) ⟨862946, by rfl⟩ : syracuseStep 1150595 = 1725893) B1725893
theorem B1019537 : Blo 451781 1019537 := bstep (se 2 (by rfl) ⟨382326, by rfl⟩ : syracuseStep 1019537 = 764653) B764653
theorem B1019555 : Blo 451781 1019555 := bstep (se 1 (by rfl) ⟨764666, by rfl⟩ : syracuseStep 1019555 = 1529333) B1529333
theorem B1150787 : Blo 451781 1150787 := bstep (se 1 (by rfl) ⟨863090, by rfl⟩ : syracuseStep 1150787 = 1726181) B1726181
theorem B1642403 : Blo 451781 1642403 := bstep (se 1 (by rfl) ⟨1231802, by rfl⟩ : syracuseStep 1642403 = 2463605) B2463605
theorem B1019825 : Blo 451781 1019825 := bstep (se 2 (by rfl) ⟨382434, by rfl⟩ : syracuseStep 1019825 = 764869) B764869
theorem B1019843 : Blo 451781 1019843 := bstep (se 1 (by rfl) ⟨764882, by rfl⟩ : syracuseStep 1019843 = 1529765) B1529765
theorem B10457201 : Blo 451781 10457201 := bstep (se 2 (by rfl) ⟨3921450, by rfl⟩ : syracuseStep 10457201 = 7842901) B7842901
theorem B2297969 : Blo 451781 2297969 := bstep (se 2 (by rfl) ⟨861738, by rfl⟩ : syracuseStep 2297969 = 1723477) B1723477
theorem B725107 : Blo 451781 725107 := bstep (se 1 (by rfl) ⟨543830, by rfl⟩ : syracuseStep 725107 = 1087661) B1087661
theorem B1478861 : Blo 451781 1478861 := bstep (se 3 (by rfl) ⟨277286, by rfl⟩ : syracuseStep 1478861 = 554573) B554573
theorem B1020113 : Blo 451781 1020113 := bstep (se 2 (by rfl) ⟨382542, by rfl⟩ : syracuseStep 1020113 = 765085) B765085
theorem B1020131 : Blo 451781 1020131 := bstep (se 1 (by rfl) ⟨765098, by rfl⟩ : syracuseStep 1020131 = 1530197) B1530197
theorem B1085795 : Blo 451781 1085795 := bstep (se 1 (by rfl) ⟨814346, by rfl⟩ : syracuseStep 1085795 = 1628693) B1628693
theorem B725363 : Blo 451781 725363 := bstep (se 1 (by rfl) ⟨544022, by rfl⟩ : syracuseStep 725363 = 1088045) B1088045
theorem B1085891 : Blo 451781 1085891 := bstep (se 1 (by rfl) ⟨814418, by rfl⟩ : syracuseStep 1085891 = 1628837) B1628837
theorem B1020401 : Blo 451781 1020401 := bstep (se 2 (by rfl) ⟨382650, by rfl⟩ : syracuseStep 1020401 = 765301) B765301
theorem B1020419 : Blo 451781 1020419 := bstep (se 1 (by rfl) ⟨765314, by rfl⟩ : syracuseStep 1020419 = 1530629) B1530629
theorem B9835121 : Blo 451781 9835121 := bstep (se 2 (by rfl) ⟨3688170, by rfl⟩ : syracuseStep 9835121 = 7376341) B7376341
theorem B1938161 : Blo 451781 1938161 := bstep (se 2 (by rfl) ⟨726810, by rfl⟩ : syracuseStep 1938161 = 1453621) B1453621
theorem B1151729 : Blo 451781 1151729 := bstep (se 2 (by rfl) ⟨431898, by rfl⟩ : syracuseStep 1151729 = 863797) B863797
theorem B1676045 : Blo 451781 1676045 := bstep (se 3 (by rfl) ⟨314258, by rfl⟩ : syracuseStep 1676045 = 628517) B628517
theorem B1020689 : Blo 451781 1020689 := bstep (se 2 (by rfl) ⟨382758, by rfl⟩ : syracuseStep 1020689 = 765517) B765517
theorem B1020707 : Blo 451781 1020707 := bstep (se 1 (by rfl) ⟨765530, by rfl⟩ : syracuseStep 1020707 = 1531061) B1531061
theorem B1151779 : Blo 451781 1151779 := bstep (se 1 (by rfl) ⟨863834, by rfl⟩ : syracuseStep 1151779 = 1727669) B1727669
theorem B1151921 : Blo 451781 1151921 := bstep (se 2 (by rfl) ⟨431970, by rfl⟩ : syracuseStep 1151921 = 863941) B863941
theorem B922627 : Blo 451781 922627 := bstep (se 1 (by rfl) ⟨691970, by rfl⟩ : syracuseStep 922627 = 1383941) B1383941
theorem B1020977 : Blo 451781 1020977 := bstep (se 2 (by rfl) ⟨382866, by rfl⟩ : syracuseStep 1020977 = 765733) B765733
theorem B726067 : Blo 451781 726067 := bstep (se 1 (by rfl) ⟨544550, by rfl⟩ : syracuseStep 726067 = 1089101) B1089101
theorem B1020995 : Blo 451781 1020995 := bstep (se 1 (by rfl) ⟨765746, by rfl⟩ : syracuseStep 1020995 = 1531493) B1531493
theorem B2954501 : Blo 451781 2954501 := bstep (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) B553969
theorem B726337 : Blo 451781 726337 := bstep (se 2 (by rfl) ⟨272376, by rfl⟩ : syracuseStep 726337 = 544753) B544753
theorem B1021265 : Blo 451781 1021265 := bstep (se 2 (by rfl) ⟨382974, by rfl⟩ : syracuseStep 1021265 = 765949) B765949
theorem B1021283 : Blo 451781 1021283 := bstep (se 1 (by rfl) ⟨765962, by rfl⟩ : syracuseStep 1021283 = 1531925) B1531925
theorem B1086833 : Blo 451781 1086833 := bstep (se 2 (by rfl) ⟨407562, by rfl⟩ : syracuseStep 1086833 = 815125) B815125
theorem B726401 : Blo 451781 726401 := bstep (se 2 (by rfl) ⟨272400, by rfl⟩ : syracuseStep 726401 = 544801) B544801
theorem B2069965 : Blo 451781 2069965 := bstep (se 3 (by rfl) ⟨388118, by rfl⟩ : syracuseStep 2069965 = 776237) B776237
theorem B2299427 : Blo 451781 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B2463281 : Blo 451781 2463281 := bstep (se 2 (by rfl) ⟨923730, by rfl⟩ : syracuseStep 2463281 = 1847461) B1847461
theorem B857699 : Blo 451781 857699 := bstep (se 1 (by rfl) ⟨643274, by rfl⟩ : syracuseStep 857699 = 1286549) B1286549
theorem B1021553 : Blo 451781 1021553 := bstep (se 2 (by rfl) ⟨383082, by rfl⟩ : syracuseStep 1021553 = 766165) B766165
theorem B1021571 : Blo 451781 1021571 := bstep (se 1 (by rfl) ⟨766178, by rfl⟩ : syracuseStep 1021571 = 1532357) B1532357
theorem B1939085 : Blo 451781 1939085 := bstep (se 3 (by rfl) ⟨363578, by rfl⟩ : syracuseStep 1939085 = 727157) B727157
theorem B2594693 : Blo 451781 2594693 := bstep (se 4 (by rfl) ⟨243252, by rfl⟩ : syracuseStep 2594693 = 486505) B486505
theorem B1021841 : Blo 451781 1021841 := bstep (se 2 (by rfl) ⟨383190, by rfl⟩ : syracuseStep 1021841 = 766381) B766381
theorem B1152913 : Blo 451781 1152913 := bstep (se 2 (by rfl) ⟨432342, by rfl⟩ : syracuseStep 1152913 = 864685) B864685
theorem B1021859 : Blo 451781 1021859 := bstep (se 1 (by rfl) ⟨766394, by rfl⟩ : syracuseStep 1021859 = 1532789) B1532789
theorem B923665 : Blo 451781 923665 := bstep (se 2 (by rfl) ⟨346374, by rfl⟩ : syracuseStep 923665 = 692749) B692749
theorem B1153187 : Blo 451781 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B1022129 : Blo 451781 1022129 := bstep (se 2 (by rfl) ⟨383298, by rfl⟩ : syracuseStep 1022129 = 766597) B766597
theorem B1022147 : Blo 451781 1022147 := bstep (se 1 (by rfl) ⟨766610, by rfl⟩ : syracuseStep 1022147 = 1533221) B1533221
theorem B2300237 : Blo 451781 2300237 := bstep (se 3 (by rfl) ⟨431294, by rfl⟩ : syracuseStep 2300237 = 862589) B862589
theorem B2595149 : Blo 451781 2595149 := bstep (se 3 (by rfl) ⟨486590, by rfl⟩ : syracuseStep 2595149 = 973181) B973181
theorem B1153379 : Blo 451781 1153379 := bstep (se 1 (by rfl) ⟨865034, by rfl⟩ : syracuseStep 1153379 = 1730069) B1730069
theorem B1022417 : Blo 451781 1022417 := bstep (se 2 (by rfl) ⟨383406, by rfl⟩ : syracuseStep 1022417 = 766813) B766813
theorem B858595 : Blo 451781 858595 := bstep (se 1 (by rfl) ⟨643946, by rfl⟩ : syracuseStep 858595 = 1287893) B1287893
theorem B1022435 : Blo 451781 1022435 := bstep (se 1 (by rfl) ⟨766826, by rfl⟩ : syracuseStep 1022435 = 1533653) B1533653
theorem B858755 : Blo 451781 858755 := bstep (se 1 (by rfl) ⟨644066, by rfl⟩ : syracuseStep 858755 = 1288133) B1288133
theorem B1448675 : Blo 451781 1448675 := bstep (se 1 (by rfl) ⟨1086506, by rfl⟩ : syracuseStep 1448675 = 2173013) B2173013
theorem B1022705 : Blo 451781 1022705 := bstep (se 2 (by rfl) ⟨383514, by rfl⟩ : syracuseStep 1022705 = 767029) B767029
theorem B1022723 : Blo 451781 1022723 := bstep (se 1 (by rfl) ⟨767042, by rfl⟩ : syracuseStep 1022723 = 1534085) B1534085
theorem B1022993 : Blo 451781 1022993 := bstep (se 2 (by rfl) ⟨383622, by rfl⟩ : syracuseStep 1022993 = 767245) B767245
theorem B1023011 : Blo 451781 1023011 := bstep (se 1 (by rfl) ⟨767258, by rfl⟩ : syracuseStep 1023011 = 1534517) B1534517
theorem B728131 : Blo 451781 728131 := bstep (se 1 (by rfl) ⟨546098, by rfl⟩ : syracuseStep 728131 = 1092197) B1092197
theorem B4955377 : Blo 451781 4955377 := bstep (se 2 (by rfl) ⟨1858266, by rfl⟩ : syracuseStep 4955377 = 3716533) B3716533
theorem B1023281 : Blo 451781 1023281 := bstep (se 2 (by rfl) ⟨383730, by rfl⟩ : syracuseStep 1023281 = 767461) B767461
theorem B1023299 : Blo 451781 1023299 := bstep (se 1 (by rfl) ⟨767474, by rfl⟩ : syracuseStep 1023299 = 1534949) B1534949
theorem B728579 : Blo 451781 728579 := bstep (se 1 (by rfl) ⟨546434, by rfl⟩ : syracuseStep 728579 = 1092869) B1092869
theorem B1449521 : Blo 451781 1449521 := bstep (se 2 (by rfl) ⟨543570, by rfl⟩ : syracuseStep 1449521 = 1087141) B1087141
theorem B1023569 : Blo 451781 1023569 := bstep (se 2 (by rfl) ⟨383838, by rfl⟩ : syracuseStep 1023569 = 767677) B767677
theorem B1449571 : Blo 451781 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B1023587 : Blo 451781 1023587 := bstep (se 1 (by rfl) ⟨767690, by rfl⟩ : syracuseStep 1023587 = 1535381) B1535381
theorem B859825 : Blo 451781 859825 := bstep (se 2 (by rfl) ⟨322434, by rfl⟩ : syracuseStep 859825 = 644869) B644869
theorem B1023857 : Blo 451781 1023857 := bstep (se 2 (by rfl) ⟨383946, by rfl⟩ : syracuseStep 1023857 = 767893) B767893
theorem B1023875 : Blo 451781 1023875 := bstep (se 1 (by rfl) ⟨767906, by rfl⟩ : syracuseStep 1023875 = 1535813) B1535813
theorem B729137 : Blo 451781 729137 := bstep (se 2 (by rfl) ⟨273426, by rfl⟩ : syracuseStep 729137 = 546853) B546853
theorem B5218445 : Blo 451781 5218445 := bstep (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) B1956917
theorem B1024145 : Blo 451781 1024145 := bstep (se 2 (by rfl) ⟨384054, by rfl⟩ : syracuseStep 1024145 = 768109) B768109
theorem B1024163 : Blo 451781 1024163 := bstep (se 1 (by rfl) ⟨768122, by rfl⟩ : syracuseStep 1024163 = 1536245) B1536245
theorem B729361 : Blo 451781 729361 := bstep (se 2 (by rfl) ⟨273510, by rfl⟩ : syracuseStep 729361 = 547021) B547021
theorem B729425 : Blo 451781 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B1024433 : Blo 451781 1024433 := bstep (se 2 (by rfl) ⟨384162, by rfl⟩ : syracuseStep 1024433 = 768325) B768325
theorem B1024451 : Blo 451781 1024451 := bstep (se 1 (by rfl) ⟨768338, by rfl⟩ : syracuseStep 1024451 = 1536677) B1536677
theorem B729553 : Blo 451781 729553 := bstep (se 2 (by rfl) ⟨273582, by rfl⟩ : syracuseStep 729553 = 547165) B547165
theorem B762385 : Blo 451781 762385 := bstep (se 2 (by rfl) ⟨285894, by rfl⟩ : syracuseStep 762385 = 571789) B571789
theorem B762419 : Blo 451781 762419 := bstep (se 1 (by rfl) ⟨571814, by rfl⟩ : syracuseStep 762419 = 1143629) B1143629
theorem B5972549 : Blo 451781 5972549 := bstep (se 4 (by rfl) ⟨559926, by rfl⟩ : syracuseStep 5972549 = 1119853) B1119853
theorem B1548941 : Blo 451781 1548941 := bstep (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) B580853
theorem B1942193 : Blo 451781 1942193 := bstep (se 2 (by rfl) ⟨728322, by rfl⟩ : syracuseStep 1942193 = 1456645) B1456645
theorem B762547 : Blo 451781 762547 := bstep (se 1 (by rfl) ⟨571910, by rfl⟩ : syracuseStep 762547 = 1143821) B1143821
theorem B860881 : Blo 451781 860881 := bstep (se 2 (by rfl) ⟨322830, by rfl⟩ : syracuseStep 860881 = 645661) B645661
theorem B1024721 : Blo 451781 1024721 := bstep (se 2 (by rfl) ⟨384270, by rfl⟩ : syracuseStep 1024721 = 768541) B768541
theorem B1024739 : Blo 451781 1024739 := bstep (se 1 (by rfl) ⟨768554, by rfl⟩ : syracuseStep 1024739 = 1537109) B1537109
theorem B1450801 : Blo 451781 1450801 := bstep (se 2 (by rfl) ⟨544050, by rfl⟩ : syracuseStep 1450801 = 1088101) B1088101
theorem B762689 : Blo 451781 762689 := bstep (se 2 (by rfl) ⟨286008, by rfl⟩ : syracuseStep 762689 = 572017) B572017
theorem B1680227 : Blo 451781 1680227 := bstep (se 1 (by rfl) ⟨1260170, by rfl⟩ : syracuseStep 1680227 = 2520341) B2520341
theorem B762817 : Blo 451781 762817 := bstep (se 2 (by rfl) ⟨286056, by rfl⟩ : syracuseStep 762817 = 572113) B572113
theorem B762851 : Blo 451781 762851 := bstep (se 1 (by rfl) ⟨572138, by rfl⟩ : syracuseStep 762851 = 1144277) B1144277
theorem B4662257 : Blo 451781 4662257 := bstep (se 2 (by rfl) ⟨1748346, by rfl⟩ : syracuseStep 4662257 = 3496693) B3496693
theorem B1025009 : Blo 451781 1025009 := bstep (se 2 (by rfl) ⟨384378, by rfl⟩ : syracuseStep 1025009 = 768757) B768757
theorem B1025027 : Blo 451781 1025027 := bstep (se 1 (by rfl) ⟨768770, by rfl⟩ : syracuseStep 1025027 = 1537541) B1537541
theorem B762979 : Blo 451781 762979 := bstep (se 1 (by rfl) ⟨572234, by rfl⟩ : syracuseStep 762979 = 1144469) B1144469
theorem B861283 : Blo 451781 861283 := bstep (se 1 (by rfl) ⟨645962, by rfl⟩ : syracuseStep 861283 = 1291925) B1291925
theorem B861329 : Blo 451781 861329 := bstep (se 2 (by rfl) ⟨322998, by rfl⟩ : syracuseStep 861329 = 645997) B645997
theorem B2303153 : Blo 451781 2303153 := bstep (se 2 (by rfl) ⟨863682, by rfl⟩ : syracuseStep 2303153 = 1727365) B1727365
theorem B763121 : Blo 451781 763121 := bstep (se 2 (by rfl) ⟨286170, by rfl⟩ : syracuseStep 763121 = 572341) B572341
theorem B1025297 : Blo 451781 1025297 := bstep (se 2 (by rfl) ⟨384486, by rfl⟩ : syracuseStep 1025297 = 768973) B768973
theorem B1025315 : Blo 451781 1025315 := bstep (se 1 (by rfl) ⟨768986, by rfl⟩ : syracuseStep 1025315 = 1537973) B1537973
theorem B1287505 : Blo 451781 1287505 := bstep (se 2 (by rfl) ⟨482814, by rfl⟩ : syracuseStep 1287505 = 965629) B965629
theorem B763249 : Blo 451781 763249 := bstep (se 2 (by rfl) ⟨286218, by rfl⟩ : syracuseStep 763249 = 572437) B572437
theorem B763283 : Blo 451781 763283 := bstep (se 1 (by rfl) ⟨572462, by rfl⟩ : syracuseStep 763283 = 1144925) B1144925
theorem B861617 : Blo 451781 861617 := bstep (se 2 (by rfl) ⟨323106, by rfl⟩ : syracuseStep 861617 = 646213) B646213
theorem B2991629 : Blo 451781 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B763411 : Blo 451781 763411 := bstep (se 1 (by rfl) ⟨572558, by rfl⟩ : syracuseStep 763411 = 1145117) B1145117
theorem B763553 : Blo 451781 763553 := bstep (se 2 (by rfl) ⟨286332, by rfl⟩ : syracuseStep 763553 = 572665) B572665
theorem B763681 : Blo 451781 763681 := bstep (se 2 (by rfl) ⟨286380, by rfl⟩ : syracuseStep 763681 = 572761) B572761
theorem B763715 : Blo 451781 763715 := bstep (se 1 (by rfl) ⟨572786, by rfl⟩ : syracuseStep 763715 = 1145573) B1145573
theorem B1943459 : Blo 451781 1943459 := bstep (se 1 (by rfl) ⟨1457594, by rfl⟩ : syracuseStep 1943459 = 2915189) B2915189
theorem B763843 : Blo 451781 763843 := bstep (se 1 (by rfl) ⟨572882, by rfl⟩ : syracuseStep 763843 = 1145765) B1145765
theorem B1451981 : Blo 451781 1451981 := bstep (se 3 (by rfl) ⟨272246, by rfl⟩ : syracuseStep 1451981 = 544493) B544493
theorem B763985 : Blo 451781 763985 := bstep (se 2 (by rfl) ⟨286494, by rfl⟩ : syracuseStep 763985 = 572989) B572989
theorem B862339 : Blo 451781 862339 := bstep (se 1 (by rfl) ⟨646754, by rfl⟩ : syracuseStep 862339 = 1293509) B1293509
theorem B764113 : Blo 451781 764113 := bstep (se 2 (by rfl) ⟨286542, by rfl⟩ : syracuseStep 764113 = 573085) B573085
theorem B764147 : Blo 451781 764147 := bstep (se 1 (by rfl) ⟨573110, by rfl⟩ : syracuseStep 764147 = 1146221) B1146221
theorem B764275 : Blo 451781 764275 := bstep (se 1 (by rfl) ⟨573206, by rfl⟩ : syracuseStep 764275 = 1146413) B1146413
theorem B764417 : Blo 451781 764417 := bstep (se 2 (by rfl) ⟨286656, by rfl⟩ : syracuseStep 764417 = 573313) B573313
theorem B862787 : Blo 451781 862787 := bstep (se 1 (by rfl) ⟨647090, by rfl⟩ : syracuseStep 862787 = 1294181) B1294181
theorem B1288781 : Blo 451781 1288781 := bstep (se 3 (by rfl) ⟨241646, by rfl⟩ : syracuseStep 1288781 = 483293) B483293
theorem B2304611 : Blo 451781 2304611 := bstep (se 1 (by rfl) ⟨1728458, by rfl⟩ : syracuseStep 2304611 = 3456917) B3456917
theorem B764545 : Blo 451781 764545 := bstep (se 2 (by rfl) ⟨286704, by rfl⟩ : syracuseStep 764545 = 573409) B573409
theorem B764579 : Blo 451781 764579 := bstep (se 1 (by rfl) ⟨573434, by rfl⟩ : syracuseStep 764579 = 1146869) B1146869
theorem B1288963 : Blo 451781 1288963 := bstep (se 1 (by rfl) ⟨966722, by rfl⟩ : syracuseStep 1288963 = 1933445) B1933445
theorem B764707 : Blo 451781 764707 := bstep (se 1 (by rfl) ⟨573530, by rfl⟩ : syracuseStep 764707 = 1147061) B1147061
theorem B1289009 : Blo 451781 1289009 := bstep (se 2 (by rfl) ⟨483378, by rfl⟩ : syracuseStep 1289009 = 966757) B966757
theorem B863075 : Blo 451781 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B764849 : Blo 451781 764849 := bstep (se 2 (by rfl) ⟨286818, by rfl⟩ : syracuseStep 764849 = 573637) B573637
theorem B764977 : Blo 451781 764977 := bstep (se 2 (by rfl) ⟨286866, by rfl⟩ : syracuseStep 764977 = 573733) B573733
theorem B765011 : Blo 451781 765011 := bstep (se 1 (by rfl) ⟨573758, by rfl⟩ : syracuseStep 765011 = 1147517) B1147517
theorem B765139 : Blo 451781 765139 := bstep (se 1 (by rfl) ⟨573854, by rfl⟩ : syracuseStep 765139 = 1147709) B1147709
theorem B4467953 : Blo 451781 4467953 := bstep (se 2 (by rfl) ⟨1675482, by rfl⟩ : syracuseStep 4467953 = 3350965) B3350965
theorem B11054389 : Blo 451781 11054389 := bstep (se 5 (by rfl) ⟨518174, by rfl⟩ : syracuseStep 11054389 = 1036349) B1036349
theorem B765281 : Blo 451781 765281 := bstep (se 2 (by rfl) ⟨286980, by rfl⟩ : syracuseStep 765281 = 573961) B573961
theorem B2305421 : Blo 451781 2305421 := bstep (se 3 (by rfl) ⟨432266, by rfl⟩ : syracuseStep 2305421 = 864533) B864533
theorem B4926901 : Blo 451781 4926901 := bstep (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) B461897
theorem B765409 : Blo 451781 765409 := bstep (se 2 (by rfl) ⟨287028, by rfl⟩ : syracuseStep 765409 = 574057) B574057
theorem B765443 : Blo 451781 765443 := bstep (se 1 (by rfl) ⟨574082, by rfl⟩ : syracuseStep 765443 = 1148165) B1148165
theorem B929297 : Blo 451781 929297 := bstep (se 2 (by rfl) ⟨348486, by rfl⟩ : syracuseStep 929297 = 696973) B696973
theorem B831043 : Blo 451781 831043 := bstep (se 1 (by rfl) ⟨623282, by rfl⟩ : syracuseStep 831043 = 1246565) B1246565
theorem B765571 : Blo 451781 765571 := bstep (se 1 (by rfl) ⟨574178, by rfl⟩ : syracuseStep 765571 = 1148357) B1148357
theorem B1453763 : Blo 451781 1453763 := bstep (se 1 (by rfl) ⟨1090322, by rfl⟩ : syracuseStep 1453763 = 2180645) B2180645
theorem B765713 : Blo 451781 765713 := bstep (se 2 (by rfl) ⟨287142, by rfl⟩ : syracuseStep 765713 = 574285) B574285
theorem B864017 : Blo 451781 864017 := bstep (se 2 (by rfl) ⟨324006, by rfl⟩ : syracuseStep 864017 = 648013) B648013
theorem B700193 : Blo 451781 700193 := bstep (se 2 (by rfl) ⟨262572, by rfl⟩ : syracuseStep 700193 = 525145) B525145
theorem B765841 : Blo 451781 765841 := bstep (se 2 (by rfl) ⟨287190, by rfl⟩ : syracuseStep 765841 = 574381) B574381
theorem B765875 : Blo 451781 765875 := bstep (se 1 (by rfl) ⟨574406, by rfl⟩ : syracuseStep 765875 = 1148813) B1148813
theorem B1716173 : Blo 451781 1716173 := bstep (se 3 (by rfl) ⟨321782, by rfl⟩ : syracuseStep 1716173 = 643565) B643565
theorem B766003 : Blo 451781 766003 := bstep (se 1 (by rfl) ⟨574502, by rfl⟩ : syracuseStep 766003 = 1149005) B1149005
theorem B4894901 : Blo 451781 4894901 := bstep (se 5 (by rfl) ⟨229448, by rfl⟩ : syracuseStep 4894901 = 458897) B458897
theorem B766145 : Blo 451781 766145 := bstep (se 2 (by rfl) ⟨287304, by rfl⟩ : syracuseStep 766145 = 574609) B574609
theorem B1290467 : Blo 451781 1290467 := bstep (se 1 (by rfl) ⟨967850, by rfl⟩ : syracuseStep 1290467 = 1935701) B1935701
theorem B2175281 : Blo 451781 2175281 := bstep (se 2 (by rfl) ⟨815730, by rfl⟩ : syracuseStep 2175281 = 1631461) B1631461
theorem B766273 : Blo 451781 766273 := bstep (se 2 (by rfl) ⟨287352, by rfl⟩ : syracuseStep 766273 = 574705) B574705
theorem B766307 : Blo 451781 766307 := bstep (se 1 (by rfl) ⟨574730, by rfl⟩ : syracuseStep 766307 = 1149461) B1149461
theorem B766435 : Blo 451781 766435 := bstep (se 1 (by rfl) ⟨574826, by rfl⟩ : syracuseStep 766435 = 1149653) B1149653
theorem B2175473 : Blo 451781 2175473 := bstep (se 2 (by rfl) ⟨815802, by rfl⟩ : syracuseStep 2175473 = 1631605) B1631605
theorem B2241037 : Blo 451781 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B2175587 : Blo 451781 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B1225325 : Blo 451781 1225325 := bstep (se 3 (by rfl) ⟨229748, by rfl⟩ : syracuseStep 1225325 = 459497) B459497
theorem B766577 : Blo 451781 766577 := bstep (se 2 (by rfl) ⟨287466, by rfl⟩ : syracuseStep 766577 = 574933) B574933
theorem B864913 : Blo 451781 864913 := bstep (se 2 (by rfl) ⟨324342, by rfl⟩ : syracuseStep 864913 = 648685) B648685
theorem B1716977 : Blo 451781 1716977 := bstep (se 2 (by rfl) ⟨643866, by rfl⟩ : syracuseStep 1716977 = 1287733) B1287733
theorem B766705 : Blo 451781 766705 := bstep (se 2 (by rfl) ⟨287514, by rfl⟩ : syracuseStep 766705 = 575029) B575029
theorem B1454851 : Blo 451781 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B766739 : Blo 451781 766739 := bstep (se 1 (by rfl) ⟨575054, by rfl⟩ : syracuseStep 766739 = 1150109) B1150109
theorem B865073 : Blo 451781 865073 := bstep (se 2 (by rfl) ⟨324402, by rfl⟩ : syracuseStep 865073 = 648805) B648805
theorem B1454993 : Blo 451781 1454993 := bstep (se 2 (by rfl) ⟨545622, by rfl⟩ : syracuseStep 1454993 = 1091245) B1091245
theorem B766867 : Blo 451781 766867 := bstep (se 1 (by rfl) ⟨575150, by rfl⟩ : syracuseStep 766867 = 1150301) B1150301
theorem B1749937 : Blo 451781 1749937 := bstep (se 2 (by rfl) ⟨656226, by rfl⟩ : syracuseStep 1749937 = 1312453) B1312453
theorem B767009 : Blo 451781 767009 := bstep (se 2 (by rfl) ⟨287628, by rfl⟩ : syracuseStep 767009 = 575257) B575257
theorem B1553489 : Blo 451781 1553489 := bstep (se 2 (by rfl) ⟨582558, by rfl⟩ : syracuseStep 1553489 = 1165117) B1165117
theorem B767137 : Blo 451781 767137 := bstep (se 2 (by rfl) ⟨287676, by rfl⟩ : syracuseStep 767137 = 575353) B575353
theorem B767171 : Blo 451781 767171 := bstep (se 1 (by rfl) ⟨575378, by rfl⟩ : syracuseStep 767171 = 1150757) B1150757
theorem B1225955 : Blo 451781 1225955 := bstep (se 1 (by rfl) ⟨919466, by rfl⟩ : syracuseStep 1225955 = 1838933) B1838933
theorem B734513 : Blo 451781 734513 := bstep (se 2 (by rfl) ⟨275442, by rfl⟩ : syracuseStep 734513 = 550885) B550885
theorem B767299 : Blo 451781 767299 := bstep (se 1 (by rfl) ⟨575474, by rfl⟩ : syracuseStep 767299 = 1150949) B1150949
theorem B1717645 : Blo 451781 1717645 := bstep (se 3 (by rfl) ⟨322058, by rfl⟩ : syracuseStep 1717645 = 644117) B644117
theorem B1291697 : Blo 451781 1291697 := bstep (se 2 (by rfl) ⟨484386, by rfl⟩ : syracuseStep 1291697 = 968773) B968773
theorem B767441 : Blo 451781 767441 := bstep (se 2 (by rfl) ⟨287790, by rfl⟩ : syracuseStep 767441 = 575581) B575581
theorem B767569 : Blo 451781 767569 := bstep (se 2 (by rfl) ⟨287838, by rfl⟩ : syracuseStep 767569 = 575677) B575677
theorem B767603 : Blo 451781 767603 := bstep (se 1 (by rfl) ⟨575702, by rfl⟩ : syracuseStep 767603 = 1151405) B1151405
theorem B767731 : Blo 451781 767731 := bstep (se 1 (by rfl) ⟨575798, by rfl⟩ : syracuseStep 767731 = 1151597) B1151597
theorem B767873 : Blo 451781 767873 := bstep (se 2 (by rfl) ⟨287952, by rfl⟩ : syracuseStep 767873 = 575905) B575905
theorem B768001 : Blo 451781 768001 := bstep (se 2 (by rfl) ⟨288000, by rfl⟩ : syracuseStep 768001 = 576001) B576001
theorem B768035 : Blo 451781 768035 := bstep (se 1 (by rfl) ⟨576026, by rfl⟩ : syracuseStep 768035 = 1152053) B1152053
theorem B14956597 : Blo 451781 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B1226819 : Blo 451781 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B1718435 : Blo 451781 1718435 := bstep (se 1 (by rfl) ⟨1288826, by rfl⟩ : syracuseStep 1718435 = 2577653) B2577653
theorem B768163 : Blo 451781 768163 := bstep (se 1 (by rfl) ⟨576122, by rfl⟩ : syracuseStep 768163 = 1152245) B1152245
theorem B1456337 : Blo 451781 1456337 := bstep (se 2 (by rfl) ⟨546126, by rfl⟩ : syracuseStep 1456337 = 1092253) B1092253
theorem B768305 : Blo 451781 768305 := bstep (se 2 (by rfl) ⟨288114, by rfl⟩ : syracuseStep 768305 = 576229) B576229
theorem B964963 : Blo 451781 964963 := bstep (se 1 (by rfl) ⟨723722, by rfl⟩ : syracuseStep 964963 = 1447445) B1447445
theorem B768433 : Blo 451781 768433 := bstep (se 2 (by rfl) ⟨288162, by rfl⟩ : syracuseStep 768433 = 576325) B576325
theorem B768467 : Blo 451781 768467 := bstep (se 1 (by rfl) ⟨576350, by rfl⟩ : syracuseStep 768467 = 1152701) B1152701
theorem B3455459 : Blo 451781 3455459 := bstep (se 1 (by rfl) ⟨2591594, by rfl⟩ : syracuseStep 3455459 = 5183189) B5183189
theorem B768595 : Blo 451781 768595 := bstep (se 1 (by rfl) ⟨576446, by rfl⟩ : syracuseStep 768595 = 1152893) B1152893
theorem B768737 : Blo 451781 768737 := bstep (se 2 (by rfl) ⟨288276, by rfl⟩ : syracuseStep 768737 = 576553) B576553
theorem B572179 : Blo 451781 572179 := bstep (se 1 (by rfl) ⟨429134, by rfl⟩ : syracuseStep 572179 = 858269) B858269
theorem B1719089 : Blo 451781 1719089 := bstep (se 2 (by rfl) ⟨644658, by rfl⟩ : syracuseStep 1719089 = 1289317) B1289317
theorem B768865 : Blo 451781 768865 := bstep (se 2 (by rfl) ⟨288324, by rfl⟩ : syracuseStep 768865 = 576649) B576649
theorem B1293155 : Blo 451781 1293155 := bstep (se 1 (by rfl) ⟨969866, by rfl⟩ : syracuseStep 1293155 = 1939733) B1939733
theorem B572275 : Blo 451781 572275 := bstep (se 1 (by rfl) ⟨429206, by rfl⟩ : syracuseStep 572275 = 858413) B858413
theorem B768899 : Blo 451781 768899 := bstep (se 1 (by rfl) ⟨576674, by rfl⟩ : syracuseStep 768899 = 1153349) B1153349
theorem B5159861 : Blo 451781 5159861 := bstep (se 5 (by rfl) ⟨241868, by rfl⟩ : syracuseStep 5159861 = 483737) B483737
theorem B769027 : Blo 451781 769027 := bstep (se 1 (by rfl) ⟨576770, by rfl⟩ : syracuseStep 769027 = 1153541) B1153541
theorem B1457261 : Blo 451781 1457261 := bstep (se 3 (by rfl) ⟨273236, by rfl⟩ : syracuseStep 1457261 = 546473) B546473
theorem B1457453 : Blo 451781 1457453 := bstep (se 3 (by rfl) ⟨273272, by rfl⟩ : syracuseStep 1457453 = 546545) B546545
theorem B572771 : Blo 451781 572771 := bstep (se 1 (by rfl) ⟨429578, by rfl⟩ : syracuseStep 572771 = 859157) B859157
theorem B2768269 : Blo 451781 2768269 := bstep (se 3 (by rfl) ⟨519050, by rfl⟩ : syracuseStep 2768269 = 1038101) B1038101
theorem B1228355 : Blo 451781 1228355 := bstep (se 1 (by rfl) ⟨921266, by rfl⟩ : syracuseStep 1228355 = 1842533) B1842533
theorem B1293965 : Blo 451781 1293965 := bstep (se 3 (by rfl) ⟨242618, by rfl⟩ : syracuseStep 1293965 = 485237) B485237
theorem B1752781 : Blo 451781 1752781 := bstep (se 3 (by rfl) ⟨328646, by rfl⟩ : syracuseStep 1752781 = 657293) B657293
theorem B4898531 : Blo 451781 4898531 := bstep (se 1 (by rfl) ⟨3673898, by rfl⟩ : syracuseStep 4898531 = 7347797) B7347797
theorem B966449 : Blo 451781 966449 := bstep (se 2 (by rfl) ⟨362418, by rfl⟩ : syracuseStep 966449 = 724837) B724837
theorem B966467 : Blo 451781 966467 := bstep (se 1 (by rfl) ⟨724850, by rfl⟩ : syracuseStep 966467 = 1449701) B1449701
theorem B1294157 : Blo 451781 1294157 := bstep (se 3 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 1294157 = 485309) B485309
theorem B573475 : Blo 451781 573475 := bstep (se 1 (by rfl) ⟨430106, by rfl⟩ : syracuseStep 573475 = 860213) B860213
theorem B573571 : Blo 451781 573571 := bstep (se 1 (by rfl) ⟨430178, by rfl⟩ : syracuseStep 573571 = 860357) B860357
theorem B1720547 : Blo 451781 1720547 := bstep (se 1 (by rfl) ⟨1290410, by rfl⟩ : syracuseStep 1720547 = 2580821) B2580821
theorem B1720561 : Blo 451781 1720561 := bstep (se 2 (by rfl) ⟨645210, by rfl⟩ : syracuseStep 1720561 = 1290421) B1290421
theorem B6209777 : Blo 451781 6209777 := bstep (se 2 (by rfl) ⟨2328666, by rfl⟩ : syracuseStep 6209777 = 4657333) B4657333
theorem B2769221 : Blo 451781 2769221 := bstep (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) B519229
theorem B1229261 : Blo 451781 1229261 := bstep (se 3 (by rfl) ⟨230486, by rfl⟩ : syracuseStep 1229261 = 460973) B460973
theorem B508387 : Blo 451781 508387 := bstep (se 1 (by rfl) ⟨381290, by rfl⟩ : syracuseStep 508387 = 762581) B762581
theorem B508531 : Blo 451781 508531 := bstep (se 1 (by rfl) ⟨381398, by rfl⟩ : syracuseStep 508531 = 762797) B762797
theorem B574067 : Blo 451781 574067 := bstep (se 1 (by rfl) ⟨430550, by rfl⟩ : syracuseStep 574067 = 861101) B861101
theorem B508675 : Blo 451781 508675 := bstep (se 1 (by rfl) ⟨381506, by rfl⟩ : syracuseStep 508675 = 763013) B763013
theorem B1557265 : Blo 451781 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B1295149 : Blo 451781 1295149 := bstep (se 3 (by rfl) ⟨242840, by rfl⟩ : syracuseStep 1295149 = 485681) B485681
theorem B508819 : Blo 451781 508819 := bstep (se 1 (by rfl) ⟨381614, by rfl⟩ : syracuseStep 508819 = 763229) B763229
theorem B1328113 : Blo 451781 1328113 := bstep (se 2 (by rfl) ⟨498042, by rfl⟩ : syracuseStep 1328113 = 996085) B996085
theorem B967697 : Blo 451781 967697 := bstep (se 2 (by rfl) ⟨362886, by rfl⟩ : syracuseStep 967697 = 725773) B725773
theorem B508963 : Blo 451781 508963 := bstep (se 1 (by rfl) ⟨381722, by rfl⟩ : syracuseStep 508963 = 763445) B763445
theorem B1557539 : Blo 451781 1557539 := bstep (se 1 (by rfl) ⟨1168154, by rfl⟩ : syracuseStep 1557539 = 2336309) B2336309
theorem B1459235 : Blo 451781 1459235 := bstep (se 1 (by rfl) ⟨1094426, by rfl⟩ : syracuseStep 1459235 = 2188853) B2188853
theorem B2901041 : Blo 451781 2901041 := bstep (se 2 (by rfl) ⟨1087890, by rfl⟩ : syracuseStep 2901041 = 2175781) B2175781
theorem B509107 : Blo 451781 509107 := bstep (se 1 (by rfl) ⟨381830, by rfl⟩ : syracuseStep 509107 = 763661) B763661
theorem B1230083 : Blo 451781 1230083 := bstep (se 1 (by rfl) ⟨922562, by rfl⟩ : syracuseStep 1230083 = 1845125) B1845125
theorem B574771 : Blo 451781 574771 := bstep (se 1 (by rfl) ⟨431078, by rfl⟩ : syracuseStep 574771 = 862157) B862157
theorem B1557809 : Blo 451781 1557809 := bstep (se 2 (by rfl) ⟨584178, by rfl⟩ : syracuseStep 1557809 = 1168357) B1168357
theorem B509251 : Blo 451781 509251 := bstep (se 1 (by rfl) ⟨381938, by rfl⟩ : syracuseStep 509251 = 763877) B763877
theorem B574867 : Blo 451781 574867 := bstep (se 1 (by rfl) ⟨431150, by rfl⟩ : syracuseStep 574867 = 862301) B862301
theorem B509395 : Blo 451781 509395 := bstep (se 1 (by rfl) ⟨382046, by rfl⟩ : syracuseStep 509395 = 764093) B764093
theorem B1525229 : Blo 451781 1525229 := bstep (se 3 (by rfl) ⟨285980, by rfl⟩ : syracuseStep 1525229 = 571961) B571961
theorem B1525283 : Blo 451781 1525283 := bstep (se 1 (by rfl) ⟨1143962, by rfl⟩ : syracuseStep 1525283 = 2287925) B2287925
theorem B2901581 : Blo 451781 2901581 := bstep (se 3 (by rfl) ⟨544046, by rfl⟩ : syracuseStep 2901581 = 1088093) B1088093
theorem B869987 : Blo 451781 869987 := bstep (se 1 (by rfl) ⟨652490, by rfl⟩ : syracuseStep 869987 = 1304981) B1304981
theorem B509539 : Blo 451781 509539 := bstep (se 1 (by rfl) ⟨382154, by rfl⟩ : syracuseStep 509539 = 764309) B764309
theorem B1722019 : Blo 451781 1722019 := bstep (se 1 (by rfl) ⟨1291514, by rfl⟩ : syracuseStep 1722019 = 2583029) B2583029
theorem B4966069 : Blo 451781 4966069 := bstep (se 5 (by rfl) ⟨232784, by rfl⟩ : syracuseStep 4966069 = 465569) B465569
theorem B509683 : Blo 451781 509683 := bstep (se 1 (by rfl) ⟨382262, by rfl⟩ : syracuseStep 509683 = 764525) B764525
theorem B1525553 : Blo 451781 1525553 := bstep (se 2 (by rfl) ⟨572082, by rfl⟩ : syracuseStep 1525553 = 1144165) B1144165
theorem B2443085 : Blo 451781 2443085 := bstep (se 3 (by rfl) ⟨458078, by rfl⟩ : syracuseStep 2443085 = 916157) B916157
theorem B1558385 : Blo 451781 1558385 := bstep (se 2 (by rfl) ⟨584394, by rfl⟩ : syracuseStep 1558385 = 1168789) B1168789
theorem B509827 : Blo 451781 509827 := bstep (se 1 (by rfl) ⟨382370, by rfl⟩ : syracuseStep 509827 = 764741) B764741
theorem B575363 : Blo 451781 575363 := bstep (se 1 (by rfl) ⟨431522, by rfl⟩ : syracuseStep 575363 = 863045) B863045
theorem B509971 : Blo 451781 509971 := bstep (se 1 (by rfl) ⟨382478, by rfl⟩ : syracuseStep 509971 = 764957) B764957
theorem B510115 : Blo 451781 510115 := bstep (se 1 (by rfl) ⟨382586, by rfl⟩ : syracuseStep 510115 = 765173) B765173
theorem B3786979 : Blo 451781 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B510259 : Blo 451781 510259 := bstep (se 1 (by rfl) ⟨382694, by rfl⟩ : syracuseStep 510259 = 765389) B765389
theorem B1526093 : Blo 451781 1526093 := bstep (se 3 (by rfl) ⟨286142, by rfl⟩ : syracuseStep 1526093 = 572285) B572285
theorem B1526147 : Blo 451781 1526147 := bstep (se 1 (by rfl) ⟨1144610, by rfl⟩ : syracuseStep 1526147 = 2289221) B2289221
theorem B510403 : Blo 451781 510403 := bstep (se 1 (by rfl) ⟨382802, by rfl⟩ : syracuseStep 510403 = 765605) B765605
theorem B1296881 : Blo 451781 1296881 := bstep (se 2 (by rfl) ⟨486330, by rfl⟩ : syracuseStep 1296881 = 972661) B972661
theorem B969251 : Blo 451781 969251 := bstep (se 1 (by rfl) ⟨726938, by rfl⟩ : syracuseStep 969251 = 1453877) B1453877
theorem B576067 : Blo 451781 576067 := bstep (se 1 (by rfl) ⟨432050, by rfl⟩ : syracuseStep 576067 = 864101) B864101
theorem B510547 : Blo 451781 510547 := bstep (se 1 (by rfl) ⟨382910, by rfl⟩ : syracuseStep 510547 = 765821) B765821
theorem B2574989 : Blo 451781 2574989 := bstep (se 3 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 2574989 = 965621) B965621
theorem B1526417 : Blo 451781 1526417 := bstep (se 2 (by rfl) ⟨572406, by rfl⟩ : syracuseStep 1526417 = 1144813) B1144813
theorem B576163 : Blo 451781 576163 := bstep (se 1 (by rfl) ⟨432122, by rfl⟩ : syracuseStep 576163 = 864245) B864245
theorem B1297073 : Blo 451781 1297073 := bstep (se 2 (by rfl) ⟨486402, by rfl⟩ : syracuseStep 1297073 = 972805) B972805
theorem B510691 : Blo 451781 510691 := bstep (se 1 (by rfl) ⟨383018, by rfl⟩ : syracuseStep 510691 = 766037) B766037
theorem B543523 : Blo 451781 543523 := bstep (se 1 (by rfl) ⟨407642, by rfl⟩ : syracuseStep 543523 = 815285) B815285
theorem B5327669 : Blo 451781 5327669 := bstep (se 5 (by rfl) ⟨249734, by rfl⟩ : syracuseStep 5327669 = 499469) B499469
theorem B510835 : Blo 451781 510835 := bstep (se 1 (by rfl) ⟨383126, by rfl⟩ : syracuseStep 510835 = 766253) B766253
theorem B510979 : Blo 451781 510979 := bstep (se 1 (by rfl) ⟨383234, by rfl⟩ : syracuseStep 510979 = 766469) B766469
theorem B4901957 : Blo 451781 4901957 := bstep (se 4 (by rfl) ⟨459558, by rfl⟩ : syracuseStep 4901957 = 919117) B919117
theorem B773267 : Blo 451781 773267 := bstep (se 1 (by rfl) ⟨579950, by rfl⟩ : syracuseStep 773267 = 1159901) B1159901
theorem B511123 : Blo 451781 511123 := bstep (se 1 (by rfl) ⟨383342, by rfl⟩ : syracuseStep 511123 = 766685) B766685
theorem B576659 : Blo 451781 576659 := bstep (se 1 (by rfl) ⟨432494, by rfl⟩ : syracuseStep 576659 = 864989) B864989
theorem B1526957 : Blo 451781 1526957 := bstep (se 3 (by rfl) ⟨286304, by rfl⟩ : syracuseStep 1526957 = 572609) B572609
theorem B1527011 : Blo 451781 1527011 := bstep (se 1 (by rfl) ⟨1145258, by rfl⟩ : syracuseStep 1527011 = 2290517) B2290517
theorem B2444579 : Blo 451781 2444579 := bstep (se 1 (by rfl) ⟨1833434, by rfl⟩ : syracuseStep 2444579 = 3666869) B3666869
theorem B511267 : Blo 451781 511267 := bstep (se 1 (by rfl) ⟨383450, by rfl⟩ : syracuseStep 511267 = 766901) B766901
theorem B5918005 : Blo 451781 5918005 := bstep (se 5 (by rfl) ⟨277406, by rfl⟩ : syracuseStep 5918005 = 554813) B554813
theorem B511411 : Blo 451781 511411 := bstep (se 1 (by rfl) ⟨383558, by rfl⟩ : syracuseStep 511411 = 767117) B767117
theorem B1527281 : Blo 451781 1527281 := bstep (se 2 (by rfl) ⟨572730, by rfl⟩ : syracuseStep 1527281 = 1145461) B1145461
theorem B544243 : Blo 451781 544243 := bstep (se 1 (by rfl) ⟨408182, by rfl⟩ : syracuseStep 544243 = 816365) B816365
theorem B1396241 : Blo 451781 1396241 := bstep (se 2 (by rfl) ⟨523590, by rfl⟩ : syracuseStep 1396241 = 1047181) B1047181
theorem B2575921 : Blo 451781 2575921 := bstep (se 2 (by rfl) ⟨965970, by rfl⟩ : syracuseStep 2575921 = 1931941) B1931941
theorem B511555 : Blo 451781 511555 := bstep (se 1 (by rfl) ⟨383666, by rfl⟩ : syracuseStep 511555 = 767333) B767333
theorem B544339 : Blo 451781 544339 := bstep (se 1 (by rfl) ⟨408254, by rfl⟩ : syracuseStep 544339 = 816509) B816509
theorem B2444941 : Blo 451781 2444941 := bstep (se 3 (by rfl) ⟨458426, by rfl⟩ : syracuseStep 2444941 = 916853) B916853
theorem B3460805 : Blo 451781 3460805 := bstep (se 4 (by rfl) ⟨324450, by rfl⟩ : syracuseStep 3460805 = 648901) B648901
theorem B511699 : Blo 451781 511699 := bstep (se 1 (by rfl) ⟨383774, by rfl⟩ : syracuseStep 511699 = 767549) B767549
theorem B1724237 : Blo 451781 1724237 := bstep (se 3 (by rfl) ⟨323294, by rfl⟩ : syracuseStep 1724237 = 646589) B646589
theorem B511843 : Blo 451781 511843 := bstep (se 1 (by rfl) ⟨383882, by rfl⟩ : syracuseStep 511843 = 767765) B767765
theorem B511987 : Blo 451781 511987 := bstep (se 1 (by rfl) ⟨383990, by rfl⟩ : syracuseStep 511987 = 767981) B767981
theorem B1527821 : Blo 451781 1527821 := bstep (se 3 (by rfl) ⟨286466, by rfl⟩ : syracuseStep 1527821 = 572933) B572933
theorem B774193 : Blo 451781 774193 := bstep (se 2 (by rfl) ⟨290322, by rfl⟩ : syracuseStep 774193 = 580645) B580645
theorem B1527875 : Blo 451781 1527875 := bstep (se 1 (by rfl) ⟨1145906, by rfl⟩ : syracuseStep 1527875 = 2291813) B2291813
theorem B512131 : Blo 451781 512131 := bstep (se 1 (by rfl) ⟨384098, by rfl⟩ : syracuseStep 512131 = 768197) B768197
theorem B643297 : Blo 451781 643297 := bstep (se 2 (by rfl) ⟨241236, by rfl⟩ : syracuseStep 643297 = 482473) B482473
theorem B512275 : Blo 451781 512275 := bstep (se 1 (by rfl) ⟨384206, by rfl⟩ : syracuseStep 512275 = 768413) B768413
theorem B1528145 : Blo 451781 1528145 := bstep (se 2 (by rfl) ⟨573054, by rfl⟩ : syracuseStep 1528145 = 1146109) B1146109
theorem B643411 : Blo 451781 643411 := bstep (se 1 (by rfl) ⟨482558, by rfl⟩ : syracuseStep 643411 = 965117) B965117
theorem B610673 : Blo 451781 610673 := bstep (se 2 (by rfl) ⟨229002, by rfl⟩ : syracuseStep 610673 = 458005) B458005
theorem B512419 : Blo 451781 512419 := bstep (se 1 (by rfl) ⟨384314, by rfl⟩ : syracuseStep 512419 = 768629) B768629
theorem B17912261 : Blo 451781 17912261 := bstep (se 4 (by rfl) ⟨1679274, by rfl⟩ : syracuseStep 17912261 = 3358549) B3358549
theorem B512563 : Blo 451781 512563 := bstep (se 1 (by rfl) ⟨384422, by rfl⟩ : syracuseStep 512563 = 768845) B768845
theorem B512707 : Blo 451781 512707 := bstep (se 1 (by rfl) ⟨384530, by rfl⟩ : syracuseStep 512707 = 769061) B769061
theorem B2904781 : Blo 451781 2904781 := bstep (se 3 (by rfl) ⟨544646, by rfl⟩ : syracuseStep 2904781 = 1089293) B1089293
theorem B971473 : Blo 451781 971473 := bstep (se 2 (by rfl) ⟨364302, by rfl⟩ : syracuseStep 971473 = 728605) B728605
theorem B1528685 : Blo 451781 1528685 := bstep (se 3 (by rfl) ⟨286628, by rfl⟩ : syracuseStep 1528685 = 573257) B573257
theorem B1528739 : Blo 451781 1528739 := bstep (se 1 (by rfl) ⟨1146554, by rfl⟩ : syracuseStep 1528739 = 2293109) B2293109
theorem B2577379 : Blo 451781 2577379 := bstep (se 1 (by rfl) ⟨1933034, by rfl⟩ : syracuseStep 2577379 = 3866069) B3866069
theorem B611491 : Blo 451781 611491 := bstep (se 1 (by rfl) ⟨458618, by rfl⟩ : syracuseStep 611491 = 917237) B917237
theorem B873635 : Blo 451781 873635 := bstep (se 1 (by rfl) ⟨655226, by rfl⟩ : syracuseStep 873635 = 1310453) B1310453
theorem B1529009 : Blo 451781 1529009 := bstep (se 2 (by rfl) ⟨573378, by rfl⟩ : syracuseStep 1529009 = 1146757) B1146757
theorem B1168849 : Blo 451781 1168849 := bstep (se 2 (by rfl) ⟨438318, by rfl⟩ : syracuseStep 1168849 = 876637) B876637
theorem B2577905 : Blo 451781 2577905 := bstep (se 2 (by rfl) ⟨966714, by rfl⟩ : syracuseStep 2577905 = 1933429) B1933429
theorem B644755 : Blo 451781 644755 := bstep (se 1 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 644755 = 967133) B967133
theorem B1529549 : Blo 451781 1529549 := bstep (se 3 (by rfl) ⟨286790, by rfl⟩ : syracuseStep 1529549 = 573581) B573581
theorem B1660621 : Blo 451781 1660621 := bstep (se 3 (by rfl) ⟨311366, by rfl⟩ : syracuseStep 1660621 = 622733) B622733
theorem B1529603 : Blo 451781 1529603 := bstep (se 1 (by rfl) ⟨1147202, by rfl⟩ : syracuseStep 1529603 = 2294405) B2294405
theorem B677681 : Blo 451781 677681 := bstep (se 2 (by rfl) ⟨254130, by rfl⟩ : syracuseStep 677681 = 508261) B508261
theorem B677699 : Blo 451781 677699 := bstep (se 1 (by rfl) ⟨508274, by rfl⟩ : syracuseStep 677699 = 1016549) B1016549
theorem B677729 : Blo 451781 677729 := bstep (se 2 (by rfl) ⟨254148, by rfl⟩ : syracuseStep 677729 = 508297) B508297
theorem B677747 : Blo 451781 677747 := bstep (se 1 (by rfl) ⟨508310, by rfl⟩ : syracuseStep 677747 = 1016621) B1016621
theorem B677777 : Blo 451781 677777 := bstep (se 2 (by rfl) ⟨254166, by rfl⟩ : syracuseStep 677777 = 508333) B508333
theorem B677795 : Blo 451781 677795 := bstep (se 1 (by rfl) ⟨508346, by rfl⟩ : syracuseStep 677795 = 1016693) B1016693
theorem B677825 : Blo 451781 677825 := bstep (se 2 (by rfl) ⟨254184, by rfl⟩ : syracuseStep 677825 = 508369) B508369
theorem B677843 : Blo 451781 677843 := bstep (se 1 (by rfl) ⟨508382, by rfl⟩ : syracuseStep 677843 = 1016765) B1016765
theorem B677873 : Blo 451781 677873 := bstep (se 2 (by rfl) ⟨254202, by rfl⟩ : syracuseStep 677873 = 508405) B508405
theorem B677891 : Blo 451781 677891 := bstep (se 1 (by rfl) ⟨508418, by rfl⟩ : syracuseStep 677891 = 1016837) B1016837
theorem B1529873 : Blo 451781 1529873 := bstep (se 2 (by rfl) ⟨573702, by rfl⟩ : syracuseStep 1529873 = 1147405) B1147405
theorem B677921 : Blo 451781 677921 := bstep (se 2 (by rfl) ⟨254220, by rfl⟩ : syracuseStep 677921 = 508441) B508441
theorem B677939 : Blo 451781 677939 := bstep (se 1 (by rfl) ⟨508454, by rfl⟩ : syracuseStep 677939 = 1016909) B1016909
theorem B677969 : Blo 451781 677969 := bstep (se 2 (by rfl) ⟨254238, by rfl⟩ : syracuseStep 677969 = 508477) B508477
theorem B677987 : Blo 451781 677987 := bstep (se 1 (by rfl) ⟨508490, by rfl⟩ : syracuseStep 677987 = 1016981) B1016981
theorem B678017 : Blo 451781 678017 := bstep (se 2 (by rfl) ⟨254256, by rfl⟩ : syracuseStep 678017 = 508513) B508513
theorem B1038467 : Blo 451781 1038467 := bstep (se 1 (by rfl) ⟨778850, by rfl⟩ : syracuseStep 1038467 = 1557701) B1557701
theorem B678035 : Blo 451781 678035 := bstep (se 1 (by rfl) ⟨508526, by rfl⟩ : syracuseStep 678035 = 1017053) B1017053
theorem B678065 : Blo 451781 678065 := bstep (se 2 (by rfl) ⟨254274, by rfl⟩ : syracuseStep 678065 = 508549) B508549
theorem B678083 : Blo 451781 678083 := bstep (se 1 (by rfl) ⟨508562, by rfl⟩ : syracuseStep 678083 = 1017125) B1017125
theorem B678113 : Blo 451781 678113 := bstep (se 2 (by rfl) ⟨254292, by rfl⟩ : syracuseStep 678113 = 508585) B508585
theorem B678131 : Blo 451781 678131 := bstep (se 1 (by rfl) ⟨508598, by rfl⟩ : syracuseStep 678131 = 1017197) B1017197
theorem B678161 : Blo 451781 678161 := bstep (se 2 (by rfl) ⟨254310, by rfl⟩ : syracuseStep 678161 = 508621) B508621
theorem B678179 : Blo 451781 678179 := bstep (se 1 (by rfl) ⟨508634, by rfl⟩ : syracuseStep 678179 = 1017269) B1017269
theorem B678209 : Blo 451781 678209 := bstep (se 2 (by rfl) ⟨254328, by rfl⟩ : syracuseStep 678209 = 508657) B508657
theorem B678227 : Blo 451781 678227 := bstep (se 1 (by rfl) ⟨508670, by rfl⟩ : syracuseStep 678227 = 1017341) B1017341
theorem B678257 : Blo 451781 678257 := bstep (se 2 (by rfl) ⟨254346, by rfl⟩ : syracuseStep 678257 = 508693) B508693
theorem B678275 : Blo 451781 678275 := bstep (se 1 (by rfl) ⟨508706, by rfl⟩ : syracuseStep 678275 = 1017413) B1017413
theorem B678305 : Blo 451781 678305 := bstep (se 2 (by rfl) ⟨254364, by rfl⟩ : syracuseStep 678305 = 508729) B508729
theorem B678323 : Blo 451781 678323 := bstep (se 1 (by rfl) ⟨508742, by rfl⟩ : syracuseStep 678323 = 1017485) B1017485
theorem B678353 : Blo 451781 678353 := bstep (se 2 (by rfl) ⟨254382, by rfl⟩ : syracuseStep 678353 = 508765) B508765
theorem B678371 : Blo 451781 678371 := bstep (se 1 (by rfl) ⟨508778, by rfl⟩ : syracuseStep 678371 = 1017557) B1017557
theorem B678401 : Blo 451781 678401 := bstep (se 2 (by rfl) ⟨254400, by rfl⟩ : syracuseStep 678401 = 508801) B508801
theorem B678419 : Blo 451781 678419 := bstep (se 1 (by rfl) ⟨508814, by rfl⟩ : syracuseStep 678419 = 1017629) B1017629
theorem B1530413 : Blo 451781 1530413 := bstep (se 3 (by rfl) ⟨286952, by rfl⟩ : syracuseStep 1530413 = 573905) B573905
theorem B678449 : Blo 451781 678449 := bstep (se 2 (by rfl) ⟨254418, by rfl⟩ : syracuseStep 678449 = 508837) B508837
theorem B678467 : Blo 451781 678467 := bstep (se 1 (by rfl) ⟨508850, by rfl⟩ : syracuseStep 678467 = 1017701) B1017701
theorem B678497 : Blo 451781 678497 := bstep (se 2 (by rfl) ⟨254436, by rfl⟩ : syracuseStep 678497 = 508873) B508873
theorem B1530467 : Blo 451781 1530467 := bstep (se 1 (by rfl) ⟨1147850, by rfl⟩ : syracuseStep 1530467 = 2295701) B2295701
theorem B678515 : Blo 451781 678515 := bstep (se 1 (by rfl) ⟨508886, by rfl⟩ : syracuseStep 678515 = 1017773) B1017773
theorem B678545 : Blo 451781 678545 := bstep (se 2 (by rfl) ⟨254454, by rfl⟩ : syracuseStep 678545 = 508909) B508909
theorem B678563 : Blo 451781 678563 := bstep (se 1 (by rfl) ⟨508922, by rfl⟩ : syracuseStep 678563 = 1017845) B1017845
theorem B776881 : Blo 451781 776881 := bstep (se 2 (by rfl) ⟨291330, by rfl⟩ : syracuseStep 776881 = 582661) B582661
theorem B1727153 : Blo 451781 1727153 := bstep (se 2 (by rfl) ⟨647682, by rfl⟩ : syracuseStep 1727153 = 1295365) B1295365
theorem B678593 : Blo 451781 678593 := bstep (se 2 (by rfl) ⟨254472, by rfl⟩ : syracuseStep 678593 = 508945) B508945
theorem B678611 : Blo 451781 678611 := bstep (se 1 (by rfl) ⟨508958, by rfl⟩ : syracuseStep 678611 = 1017917) B1017917
theorem B678641 : Blo 451781 678641 := bstep (se 2 (by rfl) ⟨254490, by rfl⟩ : syracuseStep 678641 = 508981) B508981
theorem B645889 : Blo 451781 645889 := bstep (se 2 (by rfl) ⟨242208, by rfl⟩ : syracuseStep 645889 = 484417) B484417
theorem B678659 : Blo 451781 678659 := bstep (se 1 (by rfl) ⟨508994, by rfl⟩ : syracuseStep 678659 = 1017989) B1017989
theorem B678689 : Blo 451781 678689 := bstep (se 2 (by rfl) ⟨254508, by rfl⟩ : syracuseStep 678689 = 509017) B509017
theorem B678707 : Blo 451781 678707 := bstep (se 1 (by rfl) ⟨509030, by rfl⟩ : syracuseStep 678707 = 1018061) B1018061
theorem B678737 : Blo 451781 678737 := bstep (se 2 (by rfl) ⟨254526, by rfl⟩ : syracuseStep 678737 = 509053) B509053
theorem B645985 : Blo 451781 645985 := bstep (se 2 (by rfl) ⟨242244, by rfl⟩ : syracuseStep 645985 = 484489) B484489
theorem B678755 : Blo 451781 678755 := bstep (se 1 (by rfl) ⟨509066, by rfl⟩ : syracuseStep 678755 = 1018133) B1018133
theorem B1530737 : Blo 451781 1530737 := bstep (se 2 (by rfl) ⟨574026, by rfl⟩ : syracuseStep 1530737 = 1148053) B1148053
theorem B678785 : Blo 451781 678785 := bstep (se 2 (by rfl) ⟨254544, by rfl⟩ : syracuseStep 678785 = 509089) B509089
theorem B678803 : Blo 451781 678803 := bstep (se 1 (by rfl) ⟨509102, by rfl⟩ : syracuseStep 678803 = 1018205) B1018205
theorem B2579363 : Blo 451781 2579363 := bstep (se 1 (by rfl) ⟨1934522, by rfl⟩ : syracuseStep 2579363 = 3869045) B3869045
theorem B678833 : Blo 451781 678833 := bstep (se 2 (by rfl) ⟨254562, by rfl⟩ : syracuseStep 678833 = 509125) B509125
theorem B678851 : Blo 451781 678851 := bstep (se 1 (by rfl) ⟨509138, by rfl⟩ : syracuseStep 678851 = 1018277) B1018277
theorem B678881 : Blo 451781 678881 := bstep (se 2 (by rfl) ⟨254580, by rfl⟩ : syracuseStep 678881 = 509161) B509161
theorem B3496945 : Blo 451781 3496945 := bstep (se 2 (by rfl) ⟨1311354, by rfl⟩ : syracuseStep 3496945 = 2622709) B2622709
theorem B678899 : Blo 451781 678899 := bstep (se 1 (by rfl) ⟨509174, by rfl⟩ : syracuseStep 678899 = 1018349) B1018349
theorem B678929 : Blo 451781 678929 := bstep (se 2 (by rfl) ⟨254598, by rfl⟩ : syracuseStep 678929 = 509197) B509197
theorem B678947 : Blo 451781 678947 := bstep (se 1 (by rfl) ⟨509210, by rfl⟩ : syracuseStep 678947 = 1018421) B1018421
theorem B678977 : Blo 451781 678977 := bstep (se 2 (by rfl) ⟨254616, by rfl⟩ : syracuseStep 678977 = 509233) B509233
theorem B613441 : Blo 451781 613441 := bstep (se 2 (by rfl) ⟨230040, by rfl⟩ : syracuseStep 613441 = 460081) B460081
theorem B678995 : Blo 451781 678995 := bstep (se 1 (by rfl) ⟨509246, by rfl⟩ : syracuseStep 678995 = 1018493) B1018493
theorem B679025 : Blo 451781 679025 := bstep (se 2 (by rfl) ⟨254634, by rfl⟩ : syracuseStep 679025 = 509269) B509269
theorem B679043 : Blo 451781 679043 := bstep (se 1 (by rfl) ⟨509282, by rfl⟩ : syracuseStep 679043 = 1018565) B1018565
theorem B613507 : Blo 451781 613507 := bstep (se 1 (by rfl) ⟨460130, by rfl⟩ : syracuseStep 613507 = 920261) B920261
theorem B679073 : Blo 451781 679073 := bstep (se 2 (by rfl) ⟨254652, by rfl⟩ : syracuseStep 679073 = 509305) B509305
theorem B679091 : Blo 451781 679091 := bstep (se 1 (by rfl) ⟨509318, by rfl⟩ : syracuseStep 679091 = 1018637) B1018637
theorem B679121 : Blo 451781 679121 := bstep (se 2 (by rfl) ⟨254670, by rfl⟩ : syracuseStep 679121 = 509341) B509341
theorem B679139 : Blo 451781 679139 := bstep (se 1 (by rfl) ⟨509354, by rfl⟩ : syracuseStep 679139 = 1018709) B1018709
theorem B679169 : Blo 451781 679169 := bstep (se 2 (by rfl) ⟨254688, by rfl⟩ : syracuseStep 679169 = 509377) B509377
theorem B679187 : Blo 451781 679187 := bstep (se 1 (by rfl) ⟨509390, by rfl⟩ : syracuseStep 679187 = 1018781) B1018781
theorem B679217 : Blo 451781 679217 := bstep (se 2 (by rfl) ⟨254706, by rfl⟩ : syracuseStep 679217 = 509413) B509413
theorem B679235 : Blo 451781 679235 := bstep (se 1 (by rfl) ⟨509426, by rfl⟩ : syracuseStep 679235 = 1018853) B1018853
theorem B646481 : Blo 451781 646481 := bstep (se 2 (by rfl) ⟨242430, by rfl⟩ : syracuseStep 646481 = 484861) B484861
theorem B679265 : Blo 451781 679265 := bstep (se 2 (by rfl) ⟨254724, by rfl⟩ : syracuseStep 679265 = 509449) B509449
theorem B679283 : Blo 451781 679283 := bstep (se 1 (by rfl) ⟨509462, by rfl⟩ : syracuseStep 679283 = 1018925) B1018925
theorem B1531277 : Blo 451781 1531277 := bstep (se 3 (by rfl) ⟨287114, by rfl⟩ : syracuseStep 1531277 = 574229) B574229
theorem B679313 : Blo 451781 679313 := bstep (se 2 (by rfl) ⟨254742, by rfl⟩ : syracuseStep 679313 = 509485) B509485
theorem B679331 : Blo 451781 679331 := bstep (se 1 (by rfl) ⟨509498, by rfl⟩ : syracuseStep 679331 = 1018997) B1018997
theorem B679361 : Blo 451781 679361 := bstep (se 2 (by rfl) ⟨254760, by rfl⟩ : syracuseStep 679361 = 509521) B509521
theorem B482755 : Blo 451781 482755 := bstep (se 1 (by rfl) ⟨362066, by rfl⟩ : syracuseStep 482755 = 724133) B724133
theorem B1531331 : Blo 451781 1531331 := bstep (se 1 (by rfl) ⟨1148498, by rfl⟩ : syracuseStep 1531331 = 2296997) B2296997
theorem B679379 : Blo 451781 679379 := bstep (se 1 (by rfl) ⟨509534, by rfl⟩ : syracuseStep 679379 = 1019069) B1019069
theorem B679409 : Blo 451781 679409 := bstep (se 2 (by rfl) ⟨254778, by rfl⟩ : syracuseStep 679409 = 509557) B509557
theorem B679427 : Blo 451781 679427 := bstep (se 1 (by rfl) ⟨509570, by rfl⟩ : syracuseStep 679427 = 1019141) B1019141
theorem B679457 : Blo 451781 679457 := bstep (se 2 (by rfl) ⟨254796, by rfl⟩ : syracuseStep 679457 = 509593) B509593
theorem B679475 : Blo 451781 679475 := bstep (se 1 (by rfl) ⟨509606, by rfl⟩ : syracuseStep 679475 = 1019213) B1019213
theorem B679505 : Blo 451781 679505 := bstep (se 2 (by rfl) ⟨254814, by rfl⟩ : syracuseStep 679505 = 509629) B509629
theorem B679523 : Blo 451781 679523 := bstep (se 1 (by rfl) ⟨509642, by rfl⟩ : syracuseStep 679523 = 1019285) B1019285
theorem B679553 : Blo 451781 679553 := bstep (se 2 (by rfl) ⟨254832, by rfl⟩ : syracuseStep 679553 = 509665) B509665
theorem B679571 : Blo 451781 679571 := bstep (se 1 (by rfl) ⟨509678, by rfl⟩ : syracuseStep 679571 = 1019357) B1019357
theorem B679601 : Blo 451781 679601 := bstep (se 2 (by rfl) ⟨254850, by rfl⟩ : syracuseStep 679601 = 509701) B509701
theorem B679619 : Blo 451781 679619 := bstep (se 1 (by rfl) ⟨509714, by rfl⟩ : syracuseStep 679619 = 1019429) B1019429
theorem B1531601 : Blo 451781 1531601 := bstep (se 2 (by rfl) ⟨574350, by rfl⟩ : syracuseStep 1531601 = 1148701) B1148701
theorem B679649 : Blo 451781 679649 := bstep (se 2 (by rfl) ⟨254868, by rfl⟩ : syracuseStep 679649 = 509737) B509737
theorem B3890915 : Blo 451781 3890915 := bstep (se 1 (by rfl) ⟨2918186, by rfl⟩ : syracuseStep 3890915 = 5836373) B5836373
theorem B679667 : Blo 451781 679667 := bstep (se 1 (by rfl) ⟨509750, by rfl⟩ : syracuseStep 679667 = 1019501) B1019501
theorem B679697 : Blo 451781 679697 := bstep (se 2 (by rfl) ⟨254886, by rfl⟩ : syracuseStep 679697 = 509773) B509773
theorem B679715 : Blo 451781 679715 := bstep (se 1 (by rfl) ⟨509786, by rfl⟩ : syracuseStep 679715 = 1019573) B1019573
theorem B679745 : Blo 451781 679745 := bstep (se 2 (by rfl) ⟨254904, by rfl⟩ : syracuseStep 679745 = 509809) B509809
theorem B679763 : Blo 451781 679763 := bstep (se 1 (by rfl) ⟨509822, by rfl⟩ : syracuseStep 679763 = 1019645) B1019645
theorem B679793 : Blo 451781 679793 := bstep (se 2 (by rfl) ⟨254922, by rfl⟩ : syracuseStep 679793 = 509845) B509845
theorem B2187121 : Blo 451781 2187121 := bstep (se 2 (by rfl) ⟨820170, by rfl⟩ : syracuseStep 2187121 = 1640341) B1640341
theorem B679811 : Blo 451781 679811 := bstep (se 1 (by rfl) ⟨509858, by rfl⟩ : syracuseStep 679811 = 1019717) B1019717
theorem B679841 : Blo 451781 679841 := bstep (se 2 (by rfl) ⟨254940, by rfl⟩ : syracuseStep 679841 = 509881) B509881
theorem B679859 : Blo 451781 679859 := bstep (se 1 (by rfl) ⟨509894, by rfl⟩ : syracuseStep 679859 = 1019789) B1019789
theorem B679889 : Blo 451781 679889 := bstep (se 2 (by rfl) ⟨254958, by rfl⟩ : syracuseStep 679889 = 509917) B509917
theorem B679907 : Blo 451781 679907 := bstep (se 1 (by rfl) ⟨509930, by rfl⟩ : syracuseStep 679907 = 1019861) B1019861
theorem B679937 : Blo 451781 679937 := bstep (se 2 (by rfl) ⟨254976, by rfl⟩ : syracuseStep 679937 = 509953) B509953
theorem B679955 : Blo 451781 679955 := bstep (se 1 (by rfl) ⟨509966, by rfl⟩ : syracuseStep 679955 = 1019933) B1019933
theorem B679985 : Blo 451781 679985 := bstep (se 2 (by rfl) ⟨254994, by rfl⟩ : syracuseStep 679985 = 509989) B509989
theorem B680003 : Blo 451781 680003 := bstep (se 1 (by rfl) ⟨510002, by rfl⟩ : syracuseStep 680003 = 1020005) B1020005
theorem B680033 : Blo 451781 680033 := bstep (se 2 (by rfl) ⟨255012, by rfl⟩ : syracuseStep 680033 = 510025) B510025
theorem B1728611 : Blo 451781 1728611 := bstep (se 1 (by rfl) ⟨1296458, by rfl⟩ : syracuseStep 1728611 = 2592917) B2592917
theorem B680051 : Blo 451781 680051 := bstep (se 1 (by rfl) ⟨510038, by rfl⟩ : syracuseStep 680051 = 1020077) B1020077
theorem B680081 : Blo 451781 680081 := bstep (se 2 (by rfl) ⟨255030, by rfl⟩ : syracuseStep 680081 = 510061) B510061
theorem B1106065 : Blo 451781 1106065 := bstep (se 2 (by rfl) ⟨414774, by rfl⟩ : syracuseStep 1106065 = 829549) B829549
theorem B680099 : Blo 451781 680099 := bstep (se 1 (by rfl) ⟨510074, by rfl⟩ : syracuseStep 680099 = 1020149) B1020149
theorem B647347 : Blo 451781 647347 := bstep (se 1 (by rfl) ⟨485510, by rfl⟩ : syracuseStep 647347 = 971021) B971021
theorem B680129 : Blo 451781 680129 := bstep (se 2 (by rfl) ⟨255048, by rfl⟩ : syracuseStep 680129 = 510097) B510097
theorem B680147 : Blo 451781 680147 := bstep (se 1 (by rfl) ⟨510110, by rfl⟩ : syracuseStep 680147 = 1020221) B1020221
theorem B1532141 : Blo 451781 1532141 := bstep (se 3 (by rfl) ⟨287276, by rfl⟩ : syracuseStep 1532141 = 574553) B574553
theorem B680177 : Blo 451781 680177 := bstep (se 2 (by rfl) ⟨255066, by rfl⟩ : syracuseStep 680177 = 510133) B510133
theorem B680195 : Blo 451781 680195 := bstep (se 1 (by rfl) ⟨510146, by rfl⟩ : syracuseStep 680195 = 1020293) B1020293
theorem B647443 : Blo 451781 647443 := bstep (se 1 (by rfl) ⟨485582, by rfl⟩ : syracuseStep 647443 = 971165) B971165
theorem B680225 : Blo 451781 680225 := bstep (se 2 (by rfl) ⟨255084, by rfl⟩ : syracuseStep 680225 = 510169) B510169
theorem B1532195 : Blo 451781 1532195 := bstep (se 1 (by rfl) ⟨1149146, by rfl⟩ : syracuseStep 1532195 = 2298293) B2298293
theorem B680243 : Blo 451781 680243 := bstep (se 1 (by rfl) ⟨510182, by rfl⟩ : syracuseStep 680243 = 1020365) B1020365
theorem B680273 : Blo 451781 680273 := bstep (se 2 (by rfl) ⟨255102, by rfl⟩ : syracuseStep 680273 = 510205) B510205
theorem B680291 : Blo 451781 680291 := bstep (se 1 (by rfl) ⟨510218, by rfl⟩ : syracuseStep 680291 = 1020437) B1020437
theorem B680321 : Blo 451781 680321 := bstep (se 2 (by rfl) ⟨255120, by rfl⟩ : syracuseStep 680321 = 510241) B510241
theorem B680339 : Blo 451781 680339 := bstep (se 1 (by rfl) ⟨510254, by rfl⟩ : syracuseStep 680339 = 1020509) B1020509
theorem B680369 : Blo 451781 680369 := bstep (se 2 (by rfl) ⟨255138, by rfl⟩ : syracuseStep 680369 = 510277) B510277
theorem B680387 : Blo 451781 680387 := bstep (se 1 (by rfl) ⟨510290, by rfl⟩ : syracuseStep 680387 = 1020581) B1020581
theorem B680417 : Blo 451781 680417 := bstep (se 2 (by rfl) ⟨255156, by rfl⟩ : syracuseStep 680417 = 510313) B510313
theorem B3498481 : Blo 451781 3498481 := bstep (se 2 (by rfl) ⟨1311930, by rfl⟩ : syracuseStep 3498481 = 2623861) B2623861
theorem B680435 : Blo 451781 680435 := bstep (se 1 (by rfl) ⟨510326, by rfl⟩ : syracuseStep 680435 = 1020653) B1020653
theorem B680465 : Blo 451781 680465 := bstep (se 2 (by rfl) ⟨255174, by rfl⟩ : syracuseStep 680465 = 510349) B510349
theorem B680483 : Blo 451781 680483 := bstep (se 1 (by rfl) ⟨510362, by rfl⟩ : syracuseStep 680483 = 1020725) B1020725
theorem B1532465 : Blo 451781 1532465 := bstep (se 2 (by rfl) ⟨574674, by rfl⟩ : syracuseStep 1532465 = 1149349) B1149349
theorem B680513 : Blo 451781 680513 := bstep (se 2 (by rfl) ⟨255192, by rfl⟩ : syracuseStep 680513 = 510385) B510385
theorem B680531 : Blo 451781 680531 := bstep (se 1 (by rfl) ⟨510398, by rfl⟩ : syracuseStep 680531 = 1020797) B1020797
theorem B680561 : Blo 451781 680561 := bstep (se 2 (by rfl) ⟨255210, by rfl⟩ : syracuseStep 680561 = 510421) B510421
theorem B680579 : Blo 451781 680579 := bstep (se 1 (by rfl) ⟨510434, by rfl⟩ : syracuseStep 680579 = 1020869) B1020869
theorem B680609 : Blo 451781 680609 := bstep (se 2 (by rfl) ⟨255228, by rfl⟩ : syracuseStep 680609 = 510457) B510457
theorem B680627 : Blo 451781 680627 := bstep (se 1 (by rfl) ⟨510470, by rfl⟩ : syracuseStep 680627 = 1020941) B1020941
theorem B680657 : Blo 451781 680657 := bstep (se 2 (by rfl) ⟨255246, by rfl⟩ : syracuseStep 680657 = 510493) B510493
theorem B680675 : Blo 451781 680675 := bstep (se 1 (by rfl) ⟨510506, by rfl⟩ : syracuseStep 680675 = 1021013) B1021013
theorem B680705 : Blo 451781 680705 := bstep (se 2 (by rfl) ⟨255264, by rfl⟩ : syracuseStep 680705 = 510529) B510529
theorem B647939 : Blo 451781 647939 := bstep (se 1 (by rfl) ⟨485954, by rfl⟩ : syracuseStep 647939 = 971909) B971909
theorem B2581253 : Blo 451781 2581253 := bstep (se 4 (by rfl) ⟨241992, by rfl⟩ : syracuseStep 2581253 = 483985) B483985
theorem B680723 : Blo 451781 680723 := bstep (se 1 (by rfl) ⟨510542, by rfl⟩ : syracuseStep 680723 = 1021085) B1021085
theorem B680753 : Blo 451781 680753 := bstep (se 2 (by rfl) ⟨255282, by rfl⟩ : syracuseStep 680753 = 510565) B510565
theorem B680771 : Blo 451781 680771 := bstep (se 1 (by rfl) ⟨510578, by rfl⟩ : syracuseStep 680771 = 1021157) B1021157
theorem B680801 : Blo 451781 680801 := bstep (se 2 (by rfl) ⟨255300, by rfl⟩ : syracuseStep 680801 = 510601) B510601
theorem B4350833 : Blo 451781 4350833 := bstep (se 2 (by rfl) ⟨1631562, by rfl⟩ : syracuseStep 4350833 = 3263125) B3263125
theorem B680819 : Blo 451781 680819 := bstep (se 1 (by rfl) ⟨510614, by rfl⟩ : syracuseStep 680819 = 1021229) B1021229
theorem B680849 : Blo 451781 680849 := bstep (se 2 (by rfl) ⟨255318, by rfl⟩ : syracuseStep 680849 = 510637) B510637
theorem B680867 : Blo 451781 680867 := bstep (se 1 (by rfl) ⟨510650, by rfl⟩ : syracuseStep 680867 = 1021301) B1021301
theorem B680897 : Blo 451781 680897 := bstep (se 2 (by rfl) ⟨255336, by rfl⟩ : syracuseStep 680897 = 510673) B510673
theorem B680915 : Blo 451781 680915 := bstep (se 1 (by rfl) ⟨510686, by rfl⟩ : syracuseStep 680915 = 1021373) B1021373
theorem B680945 : Blo 451781 680945 := bstep (se 2 (by rfl) ⟨255354, by rfl⟩ : syracuseStep 680945 = 510709) B510709
theorem B680963 : Blo 451781 680963 := bstep (se 1 (by rfl) ⟨510722, by rfl⟩ : syracuseStep 680963 = 1021445) B1021445
theorem B2909189 : Blo 451781 2909189 := bstep (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) B545473
theorem B680993 : Blo 451781 680993 := bstep (se 2 (by rfl) ⟨255372, by rfl⟩ : syracuseStep 680993 = 510745) B510745
theorem B2090033 : Blo 451781 2090033 := bstep (se 2 (by rfl) ⟨783762, by rfl⟩ : syracuseStep 2090033 = 1567525) B1567525
theorem B681011 : Blo 451781 681011 := bstep (se 1 (by rfl) ⟨510758, by rfl⟩ : syracuseStep 681011 = 1021517) B1021517
theorem B1533005 : Blo 451781 1533005 := bstep (se 3 (by rfl) ⟨287438, by rfl⟩ : syracuseStep 1533005 = 574877) B574877
theorem B1729613 : Blo 451781 1729613 := bstep (se 3 (by rfl) ⟨324302, by rfl⟩ : syracuseStep 1729613 = 648605) B648605
theorem B681041 : Blo 451781 681041 := bstep (se 2 (by rfl) ⟨255390, by rfl⟩ : syracuseStep 681041 = 510781) B510781
theorem B681059 : Blo 451781 681059 := bstep (se 1 (by rfl) ⟨510794, by rfl⟩ : syracuseStep 681059 = 1021589) B1021589
theorem B681089 : Blo 451781 681089 := bstep (se 2 (by rfl) ⟨255408, by rfl⟩ : syracuseStep 681089 = 510817) B510817
theorem B1533059 : Blo 451781 1533059 := bstep (se 1 (by rfl) ⟨1149794, by rfl⟩ : syracuseStep 1533059 = 2299589) B2299589
theorem B681107 : Blo 451781 681107 := bstep (se 1 (by rfl) ⟨510830, by rfl⟩ : syracuseStep 681107 = 1021661) B1021661
theorem B681137 : Blo 451781 681137 := bstep (se 2 (by rfl) ⟨255426, by rfl⟩ : syracuseStep 681137 = 510853) B510853
theorem B681155 : Blo 451781 681155 := bstep (se 1 (by rfl) ⟨510866, by rfl⟩ : syracuseStep 681155 = 1021733) B1021733
theorem B451795 : Blo 451781 451795 := bstep (se 1 (by rfl) ⟨338846, by rfl⟩ : syracuseStep 451795 = 677693) B677693
theorem B681185 : Blo 451781 681185 := bstep (se 2 (by rfl) ⟨255444, by rfl⟩ : syracuseStep 681185 = 510889) B510889
theorem B451811 : Blo 451781 451811 := bstep (se 1 (by rfl) ⟨338858, by rfl⟩ : syracuseStep 451811 = 677717) B677717
theorem B451827 : Blo 451781 451827 := bstep (se 1 (by rfl) ⟨338870, by rfl⟩ : syracuseStep 451827 = 677741) B677741
theorem B681203 : Blo 451781 681203 := bstep (se 1 (by rfl) ⟨510902, by rfl⟩ : syracuseStep 681203 = 1021805) B1021805
theorem B451843 : Blo 451781 451843 := bstep (se 1 (by rfl) ⟨338882, by rfl⟩ : syracuseStep 451843 = 677765) B677765
theorem B681233 : Blo 451781 681233 := bstep (se 2 (by rfl) ⟨255462, by rfl⟩ : syracuseStep 681233 = 510925) B510925
theorem B451859 : Blo 451781 451859 := bstep (se 1 (by rfl) ⟨338894, by rfl⟩ : syracuseStep 451859 = 677789) B677789
theorem B451875 : Blo 451781 451875 := bstep (se 1 (by rfl) ⟨338906, by rfl⟩ : syracuseStep 451875 = 677813) B677813
theorem B484643 : Blo 451781 484643 := bstep (se 1 (by rfl) ⟨363482, by rfl⟩ : syracuseStep 484643 = 726965) B726965
theorem B681251 : Blo 451781 681251 := bstep (se 1 (by rfl) ⟨510938, by rfl⟩ : syracuseStep 681251 = 1021877) B1021877
theorem B451891 : Blo 451781 451891 := bstep (se 1 (by rfl) ⟨338918, by rfl⟩ : syracuseStep 451891 = 677837) B677837
theorem B681281 : Blo 451781 681281 := bstep (se 2 (by rfl) ⟨255480, by rfl⟩ : syracuseStep 681281 = 510961) B510961
theorem B451907 : Blo 451781 451907 := bstep (se 1 (by rfl) ⟨338930, by rfl⟩ : syracuseStep 451907 = 677861) B677861
theorem B451923 : Blo 451781 451923 := bstep (se 1 (by rfl) ⟨338942, by rfl⟩ : syracuseStep 451923 = 677885) B677885
theorem B681299 : Blo 451781 681299 := bstep (se 1 (by rfl) ⟨510974, by rfl⟩ : syracuseStep 681299 = 1021949) B1021949
theorem B451939 : Blo 451781 451939 := bstep (se 1 (by rfl) ⟨338954, by rfl⟩ : syracuseStep 451939 = 677909) B677909
theorem B681329 : Blo 451781 681329 := bstep (se 2 (by rfl) ⟨255498, by rfl⟩ : syracuseStep 681329 = 510997) B510997
theorem B451955 : Blo 451781 451955 := bstep (se 1 (by rfl) ⟨338966, by rfl⟩ : syracuseStep 451955 = 677933) B677933
theorem B648577 : Blo 451781 648577 := bstep (se 2 (by rfl) ⟨243216, by rfl⟩ : syracuseStep 648577 = 486433) B486433
theorem B451971 : Blo 451781 451971 := bstep (se 1 (by rfl) ⟨338978, by rfl⟩ : syracuseStep 451971 = 677957) B677957
theorem B681347 : Blo 451781 681347 := bstep (se 1 (by rfl) ⟨511010, by rfl⟩ : syracuseStep 681347 = 1022021) B1022021
theorem B1533329 : Blo 451781 1533329 := bstep (se 2 (by rfl) ⟨574998, by rfl⟩ : syracuseStep 1533329 = 1149997) B1149997
theorem B451987 : Blo 451781 451987 := bstep (se 1 (by rfl) ⟨338990, by rfl⟩ : syracuseStep 451987 = 677981) B677981
theorem B681377 : Blo 451781 681377 := bstep (se 2 (by rfl) ⟨255516, by rfl⟩ : syracuseStep 681377 = 511033) B511033
theorem B452003 : Blo 451781 452003 := bstep (se 1 (by rfl) ⟨339002, by rfl⟩ : syracuseStep 452003 = 678005) B678005
theorem B452019 : Blo 451781 452019 := bstep (se 1 (by rfl) ⟨339014, by rfl⟩ : syracuseStep 452019 = 678029) B678029
theorem B681395 : Blo 451781 681395 := bstep (se 1 (by rfl) ⟨511046, by rfl⟩ : syracuseStep 681395 = 1022093) B1022093
theorem B452035 : Blo 451781 452035 := bstep (se 1 (by rfl) ⟨339026, by rfl⟩ : syracuseStep 452035 = 678053) B678053
theorem B681425 : Blo 451781 681425 := bstep (se 2 (by rfl) ⟨255534, by rfl⟩ : syracuseStep 681425 = 511069) B511069
theorem B452051 : Blo 451781 452051 := bstep (se 1 (by rfl) ⟨339038, by rfl⟩ : syracuseStep 452051 = 678077) B678077
theorem B452067 : Blo 451781 452067 := bstep (se 1 (by rfl) ⟨339050, by rfl⟩ : syracuseStep 452067 = 678101) B678101
theorem B681443 : Blo 451781 681443 := bstep (se 1 (by rfl) ⟨511082, by rfl⟩ : syracuseStep 681443 = 1022165) B1022165
theorem B452083 : Blo 451781 452083 := bstep (se 1 (by rfl) ⟨339062, by rfl⟩ : syracuseStep 452083 = 678125) B678125
theorem B681473 : Blo 451781 681473 := bstep (se 2 (by rfl) ⟨255552, by rfl⟩ : syracuseStep 681473 = 511105) B511105
theorem B452099 : Blo 451781 452099 := bstep (se 1 (by rfl) ⟨339074, by rfl⟩ : syracuseStep 452099 = 678149) B678149
theorem B452115 : Blo 451781 452115 := bstep (se 1 (by rfl) ⟨339086, by rfl⟩ : syracuseStep 452115 = 678173) B678173
theorem B681491 : Blo 451781 681491 := bstep (se 1 (by rfl) ⟨511118, by rfl⟩ : syracuseStep 681491 = 1022237) B1022237
theorem B452131 : Blo 451781 452131 := bstep (se 1 (by rfl) ⟨339098, by rfl⟩ : syracuseStep 452131 = 678197) B678197
theorem B681521 : Blo 451781 681521 := bstep (se 2 (by rfl) ⟨255570, by rfl⟩ : syracuseStep 681521 = 511141) B511141
theorem B452147 : Blo 451781 452147 := bstep (se 1 (by rfl) ⟨339110, by rfl⟩ : syracuseStep 452147 = 678221) B678221
theorem B452163 : Blo 451781 452163 := bstep (se 1 (by rfl) ⟨339122, by rfl⟩ : syracuseStep 452163 = 678245) B678245
theorem B681539 : Blo 451781 681539 := bstep (se 1 (by rfl) ⟨511154, by rfl⟩ : syracuseStep 681539 = 1022309) B1022309
theorem B452179 : Blo 451781 452179 := bstep (se 1 (by rfl) ⟨339134, by rfl⟩ : syracuseStep 452179 = 678269) B678269
theorem B681569 : Blo 451781 681569 := bstep (se 2 (by rfl) ⟨255588, by rfl⟩ : syracuseStep 681569 = 511177) B511177
theorem B452195 : Blo 451781 452195 := bstep (se 1 (by rfl) ⟨339146, by rfl⟩ : syracuseStep 452195 = 678293) B678293
theorem B452211 : Blo 451781 452211 := bstep (se 1 (by rfl) ⟨339158, by rfl⟩ : syracuseStep 452211 = 678317) B678317
theorem B681587 : Blo 451781 681587 := bstep (se 1 (by rfl) ⟨511190, by rfl⟩ : syracuseStep 681587 = 1022381) B1022381
theorem B452227 : Blo 451781 452227 := bstep (se 1 (by rfl) ⟨339170, by rfl⟩ : syracuseStep 452227 = 678341) B678341
theorem B681617 : Blo 451781 681617 := bstep (se 2 (by rfl) ⟨255606, by rfl⟩ : syracuseStep 681617 = 511213) B511213
theorem B452243 : Blo 451781 452243 := bstep (se 1 (by rfl) ⟨339182, by rfl⟩ : syracuseStep 452243 = 678365) B678365
theorem B452259 : Blo 451781 452259 := bstep (se 1 (by rfl) ⟨339194, by rfl⟩ : syracuseStep 452259 = 678389) B678389
theorem B681635 : Blo 451781 681635 := bstep (se 1 (by rfl) ⟨511226, by rfl⟩ : syracuseStep 681635 = 1022453) B1022453
theorem B452275 : Blo 451781 452275 := bstep (se 1 (by rfl) ⟨339206, by rfl⟩ : syracuseStep 452275 = 678413) B678413
theorem B681665 : Blo 451781 681665 := bstep (se 2 (by rfl) ⟨255624, by rfl⟩ : syracuseStep 681665 = 511249) B511249
theorem B452291 : Blo 451781 452291 := bstep (se 1 (by rfl) ⟨339218, by rfl⟩ : syracuseStep 452291 = 678437) B678437
theorem B2451149 : Blo 451781 2451149 := bstep (se 3 (by rfl) ⟨459590, by rfl⟩ : syracuseStep 2451149 = 919181) B919181
theorem B648913 : Blo 451781 648913 := bstep (se 2 (by rfl) ⟨243342, by rfl⟩ : syracuseStep 648913 = 486685) B486685
theorem B452307 : Blo 451781 452307 := bstep (se 1 (by rfl) ⟨339230, by rfl⟩ : syracuseStep 452307 = 678461) B678461
theorem B681683 : Blo 451781 681683 := bstep (se 1 (by rfl) ⟨511262, by rfl⟩ : syracuseStep 681683 = 1022525) B1022525
theorem B452323 : Blo 451781 452323 := bstep (se 1 (by rfl) ⟨339242, by rfl⟩ : syracuseStep 452323 = 678485) B678485
theorem B681713 : Blo 451781 681713 := bstep (se 2 (by rfl) ⟨255642, by rfl⟩ : syracuseStep 681713 = 511285) B511285
theorem B452339 : Blo 451781 452339 := bstep (se 1 (by rfl) ⟨339254, by rfl⟩ : syracuseStep 452339 = 678509) B678509
theorem B452355 : Blo 451781 452355 := bstep (se 1 (by rfl) ⟨339266, by rfl⟩ : syracuseStep 452355 = 678533) B678533
theorem B681731 : Blo 451781 681731 := bstep (se 1 (by rfl) ⟨511298, by rfl⟩ : syracuseStep 681731 = 1022597) B1022597
theorem B452371 : Blo 451781 452371 := bstep (se 1 (by rfl) ⟨339278, by rfl⟩ : syracuseStep 452371 = 678557) B678557
theorem B681761 : Blo 451781 681761 := bstep (se 2 (by rfl) ⟨255660, by rfl⟩ : syracuseStep 681761 = 511321) B511321
theorem B452387 : Blo 451781 452387 := bstep (se 1 (by rfl) ⟨339290, by rfl⟩ : syracuseStep 452387 = 678581) B678581
theorem B452403 : Blo 451781 452403 := bstep (se 1 (by rfl) ⟨339302, by rfl⟩ : syracuseStep 452403 = 678605) B678605
theorem B681779 : Blo 451781 681779 := bstep (se 1 (by rfl) ⟨511334, by rfl⟩ : syracuseStep 681779 = 1022669) B1022669
theorem B452419 : Blo 451781 452419 := bstep (se 1 (by rfl) ⟨339314, by rfl⟩ : syracuseStep 452419 = 678629) B678629
theorem B681809 : Blo 451781 681809 := bstep (se 2 (by rfl) ⟨255678, by rfl⟩ : syracuseStep 681809 = 511357) B511357
theorem B452435 : Blo 451781 452435 := bstep (se 1 (by rfl) ⟨339326, by rfl⟩ : syracuseStep 452435 = 678653) B678653
theorem B452451 : Blo 451781 452451 := bstep (se 1 (by rfl) ⟨339338, by rfl⟩ : syracuseStep 452451 = 678677) B678677
theorem B681827 : Blo 451781 681827 := bstep (se 1 (by rfl) ⟨511370, by rfl⟩ : syracuseStep 681827 = 1022741) B1022741
theorem B452467 : Blo 451781 452467 := bstep (se 1 (by rfl) ⟨339350, by rfl⟩ : syracuseStep 452467 = 678701) B678701
theorem B681857 : Blo 451781 681857 := bstep (se 2 (by rfl) ⟨255696, by rfl⟩ : syracuseStep 681857 = 511393) B511393
theorem B452483 : Blo 451781 452483 := bstep (se 1 (by rfl) ⟨339362, by rfl⟩ : syracuseStep 452483 = 678725) B678725
theorem B452499 : Blo 451781 452499 := bstep (se 1 (by rfl) ⟨339374, by rfl⟩ : syracuseStep 452499 = 678749) B678749
theorem B681875 : Blo 451781 681875 := bstep (se 1 (by rfl) ⟨511406, by rfl⟩ : syracuseStep 681875 = 1022813) B1022813
theorem B452515 : Blo 451781 452515 := bstep (se 1 (by rfl) ⟨339386, by rfl⟩ : syracuseStep 452515 = 678773) B678773
theorem B1533869 : Blo 451781 1533869 := bstep (se 3 (by rfl) ⟨287600, by rfl⟩ : syracuseStep 1533869 = 575201) B575201
theorem B681905 : Blo 451781 681905 := bstep (se 2 (by rfl) ⟨255714, by rfl⟩ : syracuseStep 681905 = 511429) B511429
theorem B452531 : Blo 451781 452531 := bstep (se 1 (by rfl) ⟨339398, by rfl⟩ : syracuseStep 452531 = 678797) B678797
theorem B452547 : Blo 451781 452547 := bstep (se 1 (by rfl) ⟨339410, by rfl⟩ : syracuseStep 452547 = 678821) B678821
theorem B681923 : Blo 451781 681923 := bstep (se 1 (by rfl) ⟨511442, by rfl⟩ : syracuseStep 681923 = 1022885) B1022885
theorem B452563 : Blo 451781 452563 := bstep (se 1 (by rfl) ⟨339422, by rfl⟩ : syracuseStep 452563 = 678845) B678845
theorem B681953 : Blo 451781 681953 := bstep (se 2 (by rfl) ⟨255732, by rfl⟩ : syracuseStep 681953 = 511465) B511465
theorem B452579 : Blo 451781 452579 := bstep (se 1 (by rfl) ⟨339434, by rfl⟩ : syracuseStep 452579 = 678869) B678869
theorem B1533923 : Blo 451781 1533923 := bstep (se 1 (by rfl) ⟨1150442, by rfl⟩ : syracuseStep 1533923 = 2300885) B2300885
theorem B2287601 : Blo 451781 2287601 := bstep (se 2 (by rfl) ⟨857850, by rfl⟩ : syracuseStep 2287601 = 1715701) B1715701
theorem B452595 : Blo 451781 452595 := bstep (se 1 (by rfl) ⟨339446, by rfl⟩ : syracuseStep 452595 = 678893) B678893
theorem B681971 : Blo 451781 681971 := bstep (se 1 (by rfl) ⟨511478, by rfl⟩ : syracuseStep 681971 = 1022957) B1022957
theorem B452611 : Blo 451781 452611 := bstep (se 1 (by rfl) ⟨339458, by rfl⟩ : syracuseStep 452611 = 678917) B678917
theorem B682001 : Blo 451781 682001 := bstep (se 2 (by rfl) ⟨255750, by rfl⟩ : syracuseStep 682001 = 511501) B511501
theorem B452627 : Blo 451781 452627 := bstep (se 1 (by rfl) ⟨339470, by rfl⟩ : syracuseStep 452627 = 678941) B678941
theorem B452643 : Blo 451781 452643 := bstep (se 1 (by rfl) ⟨339482, by rfl⟩ : syracuseStep 452643 = 678965) B678965
theorem B682019 : Blo 451781 682019 := bstep (se 1 (by rfl) ⟨511514, by rfl⟩ : syracuseStep 682019 = 1023029) B1023029
theorem B452659 : Blo 451781 452659 := bstep (se 1 (by rfl) ⟨339494, by rfl⟩ : syracuseStep 452659 = 678989) B678989
theorem B682049 : Blo 451781 682049 := bstep (se 2 (by rfl) ⟨255768, by rfl⟩ : syracuseStep 682049 = 511537) B511537
theorem B452675 : Blo 451781 452675 := bstep (se 1 (by rfl) ⟨339506, by rfl⟩ : syracuseStep 452675 = 679013) B679013
theorem B452691 : Blo 451781 452691 := bstep (se 1 (by rfl) ⟨339518, by rfl⟩ : syracuseStep 452691 = 679037) B679037
theorem B682067 : Blo 451781 682067 := bstep (se 1 (by rfl) ⟨511550, by rfl⟩ : syracuseStep 682067 = 1023101) B1023101
theorem B452707 : Blo 451781 452707 := bstep (se 1 (by rfl) ⟨339530, by rfl⟩ : syracuseStep 452707 = 679061) B679061
theorem B682097 : Blo 451781 682097 := bstep (se 2 (by rfl) ⟨255786, by rfl⟩ : syracuseStep 682097 = 511573) B511573
theorem B452723 : Blo 451781 452723 := bstep (se 1 (by rfl) ⟨339542, by rfl⟩ : syracuseStep 452723 = 679085) B679085
theorem B452739 : Blo 451781 452739 := bstep (se 1 (by rfl) ⟨339554, by rfl⟩ : syracuseStep 452739 = 679109) B679109
theorem B682115 : Blo 451781 682115 := bstep (se 1 (by rfl) ⟨511586, by rfl⟩ : syracuseStep 682115 = 1023173) B1023173
theorem B452755 : Blo 451781 452755 := bstep (se 1 (by rfl) ⟨339566, by rfl⟩ : syracuseStep 452755 = 679133) B679133
theorem B682145 : Blo 451781 682145 := bstep (se 2 (by rfl) ⟨255804, by rfl⟩ : syracuseStep 682145 = 511609) B511609
theorem B452771 : Blo 451781 452771 := bstep (se 1 (by rfl) ⟨339578, by rfl⟩ : syracuseStep 452771 = 679157) B679157
theorem B452787 : Blo 451781 452787 := bstep (se 1 (by rfl) ⟨339590, by rfl⟩ : syracuseStep 452787 = 679181) B679181
theorem B682163 : Blo 451781 682163 := bstep (se 1 (by rfl) ⟨511622, by rfl⟩ : syracuseStep 682163 = 1023245) B1023245
theorem B452803 : Blo 451781 452803 := bstep (se 1 (by rfl) ⟨339602, by rfl⟩ : syracuseStep 452803 = 679205) B679205
theorem B682193 : Blo 451781 682193 := bstep (se 2 (by rfl) ⟨255822, by rfl⟩ : syracuseStep 682193 = 511645) B511645
theorem B452819 : Blo 451781 452819 := bstep (se 1 (by rfl) ⟨339614, by rfl⟩ : syracuseStep 452819 = 679229) B679229
theorem B452835 : Blo 451781 452835 := bstep (se 1 (by rfl) ⟨339626, by rfl⟩ : syracuseStep 452835 = 679253) B679253
theorem B15952099 : Blo 451781 15952099 := bstep (se 1 (by rfl) ⟨11964074, by rfl⟩ : syracuseStep 15952099 = 23928149) B23928149
theorem B682211 : Blo 451781 682211 := bstep (se 1 (by rfl) ⟨511658, by rfl⟩ : syracuseStep 682211 = 1023317) B1023317
theorem B1534193 : Blo 451781 1534193 := bstep (se 2 (by rfl) ⟨575322, by rfl⟩ : syracuseStep 1534193 = 1150645) B1150645
theorem B452851 : Blo 451781 452851 := bstep (se 1 (by rfl) ⟨339638, by rfl⟩ : syracuseStep 452851 = 679277) B679277
theorem B682241 : Blo 451781 682241 := bstep (se 2 (by rfl) ⟨255840, by rfl⟩ : syracuseStep 682241 = 511681) B511681
theorem B452867 : Blo 451781 452867 := bstep (se 1 (by rfl) ⟨339650, by rfl⟩ : syracuseStep 452867 = 679301) B679301
theorem B452883 : Blo 451781 452883 := bstep (se 1 (by rfl) ⟨339662, by rfl⟩ : syracuseStep 452883 = 679325) B679325
theorem B682259 : Blo 451781 682259 := bstep (se 1 (by rfl) ⟨511694, by rfl⟩ : syracuseStep 682259 = 1023389) B1023389
theorem B452899 : Blo 451781 452899 := bstep (se 1 (by rfl) ⟨339674, by rfl⟩ : syracuseStep 452899 = 679349) B679349
theorem B682289 : Blo 451781 682289 := bstep (se 2 (by rfl) ⟨255858, by rfl⟩ : syracuseStep 682289 = 511717) B511717
theorem B452915 : Blo 451781 452915 := bstep (se 1 (by rfl) ⟨339686, by rfl⟩ : syracuseStep 452915 = 679373) B679373
theorem B452931 : Blo 451781 452931 := bstep (se 1 (by rfl) ⟨339698, by rfl⟩ : syracuseStep 452931 = 679397) B679397
theorem B682307 : Blo 451781 682307 := bstep (se 1 (by rfl) ⟨511730, by rfl⟩ : syracuseStep 682307 = 1023461) B1023461
theorem B5171525 : Blo 451781 5171525 := bstep (se 4 (by rfl) ⟨484830, by rfl⟩ : syracuseStep 5171525 = 969661) B969661
theorem B452947 : Blo 451781 452947 := bstep (se 1 (by rfl) ⟨339710, by rfl⟩ : syracuseStep 452947 = 679421) B679421
theorem B682337 : Blo 451781 682337 := bstep (se 2 (by rfl) ⟨255876, by rfl⟩ : syracuseStep 682337 = 511753) B511753
theorem B452963 : Blo 451781 452963 := bstep (se 1 (by rfl) ⟨339722, by rfl⟩ : syracuseStep 452963 = 679445) B679445
theorem B452979 : Blo 451781 452979 := bstep (se 1 (by rfl) ⟨339734, by rfl⟩ : syracuseStep 452979 = 679469) B679469
theorem B682355 : Blo 451781 682355 := bstep (se 1 (by rfl) ⟨511766, by rfl⟩ : syracuseStep 682355 = 1023533) B1023533
theorem B584051 : Blo 451781 584051 := bstep (se 1 (by rfl) ⟨438038, by rfl⟩ : syracuseStep 584051 = 876077) B876077
theorem B452995 : Blo 451781 452995 := bstep (se 1 (by rfl) ⟨339746, by rfl⟩ : syracuseStep 452995 = 679493) B679493
theorem B682385 : Blo 451781 682385 := bstep (se 2 (by rfl) ⟨255894, by rfl⟩ : syracuseStep 682385 = 511789) B511789
theorem B453011 : Blo 451781 453011 := bstep (se 1 (by rfl) ⟨339758, by rfl⟩ : syracuseStep 453011 = 679517) B679517
theorem B682403 : Blo 451781 682403 := bstep (se 1 (by rfl) ⟨511802, by rfl⟩ : syracuseStep 682403 = 1023605) B1023605
theorem B453027 : Blo 451781 453027 := bstep (se 1 (by rfl) ⟨339770, by rfl⟩ : syracuseStep 453027 = 679541) B679541
theorem B453043 : Blo 451781 453043 := bstep (se 1 (by rfl) ⟨339782, by rfl⟩ : syracuseStep 453043 = 679565) B679565
theorem B682433 : Blo 451781 682433 := bstep (se 2 (by rfl) ⟨255912, by rfl⟩ : syracuseStep 682433 = 511825) B511825
theorem B453059 : Blo 451781 453059 := bstep (se 1 (by rfl) ⟨339794, by rfl⟩ : syracuseStep 453059 = 679589) B679589
theorem B453075 : Blo 451781 453075 := bstep (se 1 (by rfl) ⟨339806, by rfl⟩ : syracuseStep 453075 = 679613) B679613
theorem B682451 : Blo 451781 682451 := bstep (se 1 (by rfl) ⟨511838, by rfl⟩ : syracuseStep 682451 = 1023677) B1023677
theorem B453091 : Blo 451781 453091 := bstep (se 1 (by rfl) ⟨339818, by rfl⟩ : syracuseStep 453091 = 679637) B679637
theorem B682481 : Blo 451781 682481 := bstep (se 2 (by rfl) ⟨255930, by rfl⟩ : syracuseStep 682481 = 511861) B511861
theorem B453107 : Blo 451781 453107 := bstep (se 1 (by rfl) ⟨339830, by rfl⟩ : syracuseStep 453107 = 679661) B679661
theorem B453123 : Blo 451781 453123 := bstep (se 1 (by rfl) ⟨339842, by rfl⟩ : syracuseStep 453123 = 679685) B679685
theorem B682499 : Blo 451781 682499 := bstep (se 1 (by rfl) ⟨511874, by rfl⟩ : syracuseStep 682499 = 1023749) B1023749
theorem B453139 : Blo 451781 453139 := bstep (se 1 (by rfl) ⟨339854, by rfl⟩ : syracuseStep 453139 = 679709) B679709
theorem B682529 : Blo 451781 682529 := bstep (se 2 (by rfl) ⟨255948, by rfl⟩ : syracuseStep 682529 = 511897) B511897
theorem B453155 : Blo 451781 453155 := bstep (se 1 (by rfl) ⟨339866, by rfl⟩ : syracuseStep 453155 = 679733) B679733
theorem B453171 : Blo 451781 453171 := bstep (se 1 (by rfl) ⟨339878, by rfl⟩ : syracuseStep 453171 = 679757) B679757
theorem B682547 : Blo 451781 682547 := bstep (se 1 (by rfl) ⟨511910, by rfl⟩ : syracuseStep 682547 = 1023821) B1023821
theorem B453187 : Blo 451781 453187 := bstep (se 1 (by rfl) ⟨339890, by rfl⟩ : syracuseStep 453187 = 679781) B679781
theorem B682577 : Blo 451781 682577 := bstep (se 2 (by rfl) ⟨255966, by rfl⟩ : syracuseStep 682577 = 511933) B511933
theorem B453203 : Blo 451781 453203 := bstep (se 1 (by rfl) ⟨339902, by rfl⟩ : syracuseStep 453203 = 679805) B679805
theorem B453219 : Blo 451781 453219 := bstep (se 1 (by rfl) ⟨339914, by rfl⟩ : syracuseStep 453219 = 679829) B679829
theorem B518755 : Blo 451781 518755 := bstep (se 1 (by rfl) ⟨389066, by rfl⟩ : syracuseStep 518755 = 778133) B778133
theorem B682595 : Blo 451781 682595 := bstep (se 1 (by rfl) ⟨511946, by rfl⟩ : syracuseStep 682595 = 1023893) B1023893
theorem B453235 : Blo 451781 453235 := bstep (se 1 (by rfl) ⟨339926, by rfl⟩ : syracuseStep 453235 = 679853) B679853
theorem B682625 : Blo 451781 682625 := bstep (se 2 (by rfl) ⟨255984, by rfl⟩ : syracuseStep 682625 = 511969) B511969
theorem B453251 : Blo 451781 453251 := bstep (se 1 (by rfl) ⟨339938, by rfl⟩ : syracuseStep 453251 = 679877) B679877
theorem B453267 : Blo 451781 453267 := bstep (se 1 (by rfl) ⟨339950, by rfl⟩ : syracuseStep 453267 = 679901) B679901
theorem B682643 : Blo 451781 682643 := bstep (se 1 (by rfl) ⟨511982, by rfl⟩ : syracuseStep 682643 = 1023965) B1023965
theorem B453283 : Blo 451781 453283 := bstep (se 1 (by rfl) ⟨339962, by rfl⟩ : syracuseStep 453283 = 679925) B679925
theorem B682673 : Blo 451781 682673 := bstep (se 2 (by rfl) ⟨256002, by rfl⟩ : syracuseStep 682673 = 512005) B512005
theorem B453299 : Blo 451781 453299 := bstep (se 1 (by rfl) ⟨339974, by rfl⟩ : syracuseStep 453299 = 679949) B679949
theorem B453315 : Blo 451781 453315 := bstep (se 1 (by rfl) ⟨339986, by rfl⟩ : syracuseStep 453315 = 679973) B679973
theorem B682691 : Blo 451781 682691 := bstep (se 1 (by rfl) ⟨512018, by rfl⟩ : syracuseStep 682691 = 1024037) B1024037
theorem B453331 : Blo 451781 453331 := bstep (se 1 (by rfl) ⟨339998, by rfl⟩ : syracuseStep 453331 = 679997) B679997
theorem B682721 : Blo 451781 682721 := bstep (se 2 (by rfl) ⟨256020, by rfl⟩ : syracuseStep 682721 = 512041) B512041
theorem B453347 : Blo 451781 453347 := bstep (se 1 (by rfl) ⟨340010, by rfl⟩ : syracuseStep 453347 = 680021) B680021
theorem B453363 : Blo 451781 453363 := bstep (se 1 (by rfl) ⟨340022, by rfl⟩ : syracuseStep 453363 = 680045) B680045
theorem B682739 : Blo 451781 682739 := bstep (se 1 (by rfl) ⟨512054, by rfl⟩ : syracuseStep 682739 = 1024109) B1024109
theorem B453379 : Blo 451781 453379 := bstep (se 1 (by rfl) ⟨340034, by rfl⟩ : syracuseStep 453379 = 680069) B680069
theorem B1534733 : Blo 451781 1534733 := bstep (se 3 (by rfl) ⟨287762, by rfl⟩ : syracuseStep 1534733 = 575525) B575525
theorem B682769 : Blo 451781 682769 := bstep (se 2 (by rfl) ⟨256038, by rfl⟩ : syracuseStep 682769 = 512077) B512077
theorem B453395 : Blo 451781 453395 := bstep (se 1 (by rfl) ⟨340046, by rfl⟩ : syracuseStep 453395 = 680093) B680093
theorem B453411 : Blo 451781 453411 := bstep (se 1 (by rfl) ⟨340058, by rfl⟩ : syracuseStep 453411 = 680117) B680117
theorem B682787 : Blo 451781 682787 := bstep (se 1 (by rfl) ⟨512090, by rfl⟩ : syracuseStep 682787 = 1024181) B1024181
theorem B453427 : Blo 451781 453427 := bstep (se 1 (by rfl) ⟨340070, by rfl⟩ : syracuseStep 453427 = 680141) B680141
theorem B682817 : Blo 451781 682817 := bstep (se 2 (by rfl) ⟨256056, by rfl⟩ : syracuseStep 682817 = 512113) B512113
theorem B453443 : Blo 451781 453443 := bstep (se 1 (by rfl) ⟨340082, by rfl⟩ : syracuseStep 453443 = 680165) B680165
theorem B1534787 : Blo 451781 1534787 := bstep (se 1 (by rfl) ⟨1151090, by rfl⟩ : syracuseStep 1534787 = 2302181) B2302181
theorem B453459 : Blo 451781 453459 := bstep (se 1 (by rfl) ⟨340094, by rfl⟩ : syracuseStep 453459 = 680189) B680189
theorem B682835 : Blo 451781 682835 := bstep (se 1 (by rfl) ⟨512126, by rfl⟩ : syracuseStep 682835 = 1024253) B1024253
theorem B453475 : Blo 451781 453475 := bstep (se 1 (by rfl) ⟨340106, by rfl⟩ : syracuseStep 453475 = 680213) B680213
theorem B2190179 : Blo 451781 2190179 := bstep (se 1 (by rfl) ⟨1642634, by rfl⟩ : syracuseStep 2190179 = 3285269) B3285269
theorem B682865 : Blo 451781 682865 := bstep (se 2 (by rfl) ⟨256074, by rfl⟩ : syracuseStep 682865 = 512149) B512149
theorem B453491 : Blo 451781 453491 := bstep (se 1 (by rfl) ⟨340118, by rfl⟩ : syracuseStep 453491 = 680237) B680237
theorem B453507 : Blo 451781 453507 := bstep (se 1 (by rfl) ⟨340130, by rfl⟩ : syracuseStep 453507 = 680261) B680261
theorem B682883 : Blo 451781 682883 := bstep (se 1 (by rfl) ⟨512162, by rfl⟩ : syracuseStep 682883 = 1024325) B1024325
theorem B453523 : Blo 451781 453523 := bstep (se 1 (by rfl) ⟨340142, by rfl⟩ : syracuseStep 453523 = 680285) B680285
theorem B682913 : Blo 451781 682913 := bstep (se 2 (by rfl) ⟨256092, by rfl⟩ : syracuseStep 682913 = 512185) B512185
theorem B453539 : Blo 451781 453539 := bstep (se 1 (by rfl) ⟨340154, by rfl⟩ : syracuseStep 453539 = 680309) B680309
theorem B2911139 : Blo 451781 2911139 := bstep (se 1 (by rfl) ⟨2183354, by rfl⟩ : syracuseStep 2911139 = 4366709) B4366709
theorem B453555 : Blo 451781 453555 := bstep (se 1 (by rfl) ⟨340166, by rfl⟩ : syracuseStep 453555 = 680333) B680333
theorem B682931 : Blo 451781 682931 := bstep (se 1 (by rfl) ⟨512198, by rfl⟩ : syracuseStep 682931 = 1024397) B1024397
theorem B453571 : Blo 451781 453571 := bstep (se 1 (by rfl) ⟨340178, by rfl⟩ : syracuseStep 453571 = 680357) B680357
theorem B682961 : Blo 451781 682961 := bstep (se 2 (by rfl) ⟨256110, by rfl⟩ : syracuseStep 682961 = 512221) B512221
theorem B453587 : Blo 451781 453587 := bstep (se 1 (by rfl) ⟨340190, by rfl⟩ : syracuseStep 453587 = 680381) B680381
theorem B453603 : Blo 451781 453603 := bstep (se 1 (by rfl) ⟨340202, by rfl⟩ : syracuseStep 453603 = 680405) B680405
theorem B682979 : Blo 451781 682979 := bstep (se 1 (by rfl) ⟨512234, by rfl⟩ : syracuseStep 682979 = 1024469) B1024469
theorem B453619 : Blo 451781 453619 := bstep (se 1 (by rfl) ⟨340214, by rfl⟩ : syracuseStep 453619 = 680429) B680429
theorem B683009 : Blo 451781 683009 := bstep (se 2 (by rfl) ⟨256128, by rfl⟩ : syracuseStep 683009 = 512257) B512257
theorem B453635 : Blo 451781 453635 := bstep (se 1 (by rfl) ⟨340226, by rfl⟩ : syracuseStep 453635 = 680453) B680453
theorem B3435533 : Blo 451781 3435533 := bstep (se 3 (by rfl) ⟨644162, by rfl⟩ : syracuseStep 3435533 = 1288325) B1288325
theorem B453651 : Blo 451781 453651 := bstep (se 1 (by rfl) ⟨340238, by rfl⟩ : syracuseStep 453651 = 680477) B680477
theorem B683027 : Blo 451781 683027 := bstep (se 1 (by rfl) ⟨512270, by rfl⟩ : syracuseStep 683027 = 1024541) B1024541
theorem B453667 : Blo 451781 453667 := bstep (se 1 (by rfl) ⟨340250, by rfl⟩ : syracuseStep 453667 = 680501) B680501
theorem B683057 : Blo 451781 683057 := bstep (se 2 (by rfl) ⟨256146, by rfl⟩ : syracuseStep 683057 = 512293) B512293
theorem B453683 : Blo 451781 453683 := bstep (se 1 (by rfl) ⟨340262, by rfl⟩ : syracuseStep 453683 = 680525) B680525
theorem B453699 : Blo 451781 453699 := bstep (se 1 (by rfl) ⟨340274, by rfl⟩ : syracuseStep 453699 = 680549) B680549
theorem B683075 : Blo 451781 683075 := bstep (se 1 (by rfl) ⟨512306, by rfl⟩ : syracuseStep 683075 = 1024613) B1024613
theorem B1535057 : Blo 451781 1535057 := bstep (se 2 (by rfl) ⟨575646, by rfl⟩ : syracuseStep 1535057 = 1151293) B1151293
theorem B453715 : Blo 451781 453715 := bstep (se 1 (by rfl) ⟨340286, by rfl⟩ : syracuseStep 453715 = 680573) B680573
theorem B683105 : Blo 451781 683105 := bstep (se 2 (by rfl) ⟨256164, by rfl⟩ : syracuseStep 683105 = 512329) B512329
theorem B453731 : Blo 451781 453731 := bstep (se 1 (by rfl) ⟨340298, by rfl⟩ : syracuseStep 453731 = 680597) B680597
theorem B453747 : Blo 451781 453747 := bstep (se 1 (by rfl) ⟨340310, by rfl⟩ : syracuseStep 453747 = 680621) B680621
theorem B683123 : Blo 451781 683123 := bstep (se 1 (by rfl) ⟨512342, by rfl⟩ : syracuseStep 683123 = 1024685) B1024685
theorem B453763 : Blo 451781 453763 := bstep (se 1 (by rfl) ⟨340322, by rfl⟩ : syracuseStep 453763 = 680645) B680645
theorem B814225 : Blo 451781 814225 := bstep (se 2 (by rfl) ⟨305334, by rfl⟩ : syracuseStep 814225 = 610669) B610669
theorem B683153 : Blo 451781 683153 := bstep (se 2 (by rfl) ⟨256182, by rfl⟩ : syracuseStep 683153 = 512365) B512365
theorem B453779 : Blo 451781 453779 := bstep (se 1 (by rfl) ⟨340334, by rfl⟩ : syracuseStep 453779 = 680669) B680669
theorem B453795 : Blo 451781 453795 := bstep (se 1 (by rfl) ⟨340346, by rfl⟩ : syracuseStep 453795 = 680693) B680693
theorem B683171 : Blo 451781 683171 := bstep (se 1 (by rfl) ⟨512378, by rfl⟩ : syracuseStep 683171 = 1024757) B1024757
theorem B453811 : Blo 451781 453811 := bstep (se 1 (by rfl) ⟨340358, by rfl⟩ : syracuseStep 453811 = 680717) B680717
theorem B683201 : Blo 451781 683201 := bstep (se 2 (by rfl) ⟨256200, by rfl⟩ : syracuseStep 683201 = 512401) B512401
theorem B453827 : Blo 451781 453827 := bstep (se 1 (by rfl) ⟨340370, by rfl⟩ : syracuseStep 453827 = 680741) B680741
theorem B453843 : Blo 451781 453843 := bstep (se 1 (by rfl) ⟨340382, by rfl⟩ : syracuseStep 453843 = 680765) B680765
theorem B683219 : Blo 451781 683219 := bstep (se 1 (by rfl) ⟨512414, by rfl⟩ : syracuseStep 683219 = 1024829) B1024829
theorem B453859 : Blo 451781 453859 := bstep (se 1 (by rfl) ⟨340394, by rfl⟩ : syracuseStep 453859 = 680789) B680789
theorem B683249 : Blo 451781 683249 := bstep (se 2 (by rfl) ⟨256218, by rfl⟩ : syracuseStep 683249 = 512437) B512437
theorem B453875 : Blo 451781 453875 := bstep (se 1 (by rfl) ⟨340406, by rfl⟩ : syracuseStep 453875 = 680813) B680813
theorem B453891 : Blo 451781 453891 := bstep (se 1 (by rfl) ⟨340418, by rfl⟩ : syracuseStep 453891 = 680837) B680837
theorem B683267 : Blo 451781 683267 := bstep (se 1 (by rfl) ⟨512450, by rfl⟩ : syracuseStep 683267 = 1024901) B1024901
theorem B486659 : Blo 451781 486659 := bstep (se 1 (by rfl) ⟨364994, by rfl⟩ : syracuseStep 486659 = 729989) B729989
theorem B453907 : Blo 451781 453907 := bstep (se 1 (by rfl) ⟨340430, by rfl⟩ : syracuseStep 453907 = 680861) B680861
theorem B683297 : Blo 451781 683297 := bstep (se 2 (by rfl) ⟨256236, by rfl⟩ : syracuseStep 683297 = 512473) B512473
theorem B453923 : Blo 451781 453923 := bstep (se 1 (by rfl) ⟨340442, by rfl⟩ : syracuseStep 453923 = 680885) B680885
theorem B453939 : Blo 451781 453939 := bstep (se 1 (by rfl) ⟨340454, by rfl⟩ : syracuseStep 453939 = 680909) B680909
theorem B683315 : Blo 451781 683315 := bstep (se 1 (by rfl) ⟨512486, by rfl⟩ : syracuseStep 683315 = 1024973) B1024973
theorem B453955 : Blo 451781 453955 := bstep (se 1 (by rfl) ⟨340466, by rfl⟩ : syracuseStep 453955 = 680933) B680933
theorem B683345 : Blo 451781 683345 := bstep (se 2 (by rfl) ⟨256254, by rfl⟩ : syracuseStep 683345 = 512509) B512509
theorem B453971 : Blo 451781 453971 := bstep (se 1 (by rfl) ⟨340478, by rfl⟩ : syracuseStep 453971 = 680957) B680957
theorem B453987 : Blo 451781 453987 := bstep (se 1 (by rfl) ⟨340490, by rfl⟩ : syracuseStep 453987 = 680981) B680981
theorem B683363 : Blo 451781 683363 := bstep (se 1 (by rfl) ⟨512522, by rfl⟩ : syracuseStep 683363 = 1025045) B1025045
theorem B454003 : Blo 451781 454003 := bstep (se 1 (by rfl) ⟨340502, by rfl⟩ : syracuseStep 454003 = 681005) B681005
theorem B683393 : Blo 451781 683393 := bstep (se 2 (by rfl) ⟨256272, by rfl⟩ : syracuseStep 683393 = 512545) B512545
theorem B454019 : Blo 451781 454019 := bstep (se 1 (by rfl) ⟨340514, by rfl⟩ : syracuseStep 454019 = 681029) B681029
theorem B454035 : Blo 451781 454035 := bstep (se 1 (by rfl) ⟨340526, by rfl⟩ : syracuseStep 454035 = 681053) B681053
theorem B683411 : Blo 451781 683411 := bstep (se 1 (by rfl) ⟨512558, by rfl⟩ : syracuseStep 683411 = 1025117) B1025117
theorem B2289059 : Blo 451781 2289059 := bstep (se 1 (by rfl) ⟨1716794, by rfl⟩ : syracuseStep 2289059 = 3433589) B3433589
theorem B454051 : Blo 451781 454051 := bstep (se 1 (by rfl) ⟨340538, by rfl⟩ : syracuseStep 454051 = 681077) B681077
theorem B683441 : Blo 451781 683441 := bstep (se 2 (by rfl) ⟨256290, by rfl⟩ : syracuseStep 683441 = 512581) B512581
theorem B454067 : Blo 451781 454067 := bstep (se 1 (by rfl) ⟨340550, by rfl⟩ : syracuseStep 454067 = 681101) B681101
theorem B454083 : Blo 451781 454083 := bstep (se 1 (by rfl) ⟨340562, by rfl⟩ : syracuseStep 454083 = 681125) B681125
theorem B683459 : Blo 451781 683459 := bstep (se 1 (by rfl) ⟨512594, by rfl⟩ : syracuseStep 683459 = 1025189) B1025189
theorem B454099 : Blo 451781 454099 := bstep (se 1 (by rfl) ⟨340574, by rfl⟩ : syracuseStep 454099 = 681149) B681149
theorem B683489 : Blo 451781 683489 := bstep (se 2 (by rfl) ⟨256308, by rfl⟩ : syracuseStep 683489 = 512617) B512617
theorem B454115 : Blo 451781 454115 := bstep (se 1 (by rfl) ⟨340586, by rfl⟩ : syracuseStep 454115 = 681173) B681173
theorem B454131 : Blo 451781 454131 := bstep (se 1 (by rfl) ⟨340598, by rfl⟩ : syracuseStep 454131 = 681197) B681197
theorem B683507 : Blo 451781 683507 := bstep (se 1 (by rfl) ⟨512630, by rfl⟩ : syracuseStep 683507 = 1025261) B1025261
theorem B454147 : Blo 451781 454147 := bstep (se 1 (by rfl) ⟨340610, by rfl⟩ : syracuseStep 454147 = 681221) B681221
theorem B683537 : Blo 451781 683537 := bstep (se 2 (by rfl) ⟨256326, by rfl⟩ : syracuseStep 683537 = 512653) B512653
theorem B454163 : Blo 451781 454163 := bstep (se 1 (by rfl) ⟨340622, by rfl⟩ : syracuseStep 454163 = 681245) B681245
theorem B454179 : Blo 451781 454179 := bstep (se 1 (by rfl) ⟨340634, by rfl⟩ : syracuseStep 454179 = 681269) B681269
theorem B683555 : Blo 451781 683555 := bstep (se 1 (by rfl) ⟨512666, by rfl⟩ : syracuseStep 683555 = 1025333) B1025333
theorem B454195 : Blo 451781 454195 := bstep (se 1 (by rfl) ⟨340646, by rfl⟩ : syracuseStep 454195 = 681293) B681293
theorem B683585 : Blo 451781 683585 := bstep (se 2 (by rfl) ⟨256344, by rfl⟩ : syracuseStep 683585 = 512689) B512689
theorem B454211 : Blo 451781 454211 := bstep (se 1 (by rfl) ⟨340658, by rfl⟩ : syracuseStep 454211 = 681317) B681317
theorem B454227 : Blo 451781 454227 := bstep (se 1 (by rfl) ⟨340670, by rfl⟩ : syracuseStep 454227 = 681341) B681341
theorem B683603 : Blo 451781 683603 := bstep (se 1 (by rfl) ⟨512702, by rfl⟩ : syracuseStep 683603 = 1025405) B1025405
theorem B454243 : Blo 451781 454243 := bstep (se 1 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 454243 = 681365) B681365
theorem B1535597 : Blo 451781 1535597 := bstep (se 3 (by rfl) ⟨287924, by rfl⟩ : syracuseStep 1535597 = 575849) B575849
theorem B683633 : Blo 451781 683633 := bstep (se 2 (by rfl) ⟨256362, by rfl⟩ : syracuseStep 683633 = 512725) B512725
theorem B454259 : Blo 451781 454259 := bstep (se 1 (by rfl) ⟨340694, by rfl⟩ : syracuseStep 454259 = 681389) B681389
theorem B454275 : Blo 451781 454275 := bstep (se 1 (by rfl) ⟨340706, by rfl⟩ : syracuseStep 454275 = 681413) B681413
theorem B683651 : Blo 451781 683651 := bstep (se 1 (by rfl) ⟨512738, by rfl⟩ : syracuseStep 683651 = 1025477) B1025477
theorem B454291 : Blo 451781 454291 := bstep (se 1 (by rfl) ⟨340718, by rfl⟩ : syracuseStep 454291 = 681437) B681437
theorem B454307 : Blo 451781 454307 := bstep (se 1 (by rfl) ⟨340730, by rfl⟩ : syracuseStep 454307 = 681461) B681461
theorem B1535651 : Blo 451781 1535651 := bstep (se 1 (by rfl) ⟨1151738, by rfl⟩ : syracuseStep 1535651 = 2303477) B2303477
theorem B454323 : Blo 451781 454323 := bstep (se 1 (by rfl) ⟨340742, by rfl⟩ : syracuseStep 454323 = 681485) B681485
theorem B454339 : Blo 451781 454339 := bstep (se 1 (by rfl) ⟨340754, by rfl⟩ : syracuseStep 454339 = 681509) B681509
theorem B4419269 : Blo 451781 4419269 := bstep (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) B828613
theorem B1633997 : Blo 451781 1633997 := bstep (se 3 (by rfl) ⟨306374, by rfl⟩ : syracuseStep 1633997 = 612749) B612749
theorem B454355 : Blo 451781 454355 := bstep (se 1 (by rfl) ⟨340766, by rfl⟩ : syracuseStep 454355 = 681533) B681533
theorem B454371 : Blo 451781 454371 := bstep (se 1 (by rfl) ⟨340778, by rfl⟩ : syracuseStep 454371 = 681557) B681557
theorem B454387 : Blo 451781 454387 := bstep (se 1 (by rfl) ⟨340790, by rfl⟩ : syracuseStep 454387 = 681581) B681581
theorem B454403 : Blo 451781 454403 := bstep (se 1 (by rfl) ⟨340802, by rfl⟩ : syracuseStep 454403 = 681605) B681605
theorem B454419 : Blo 451781 454419 := bstep (se 1 (by rfl) ⟨340814, by rfl⟩ : syracuseStep 454419 = 681629) B681629
theorem B454435 : Blo 451781 454435 := bstep (se 1 (by rfl) ⟨340826, by rfl⟩ : syracuseStep 454435 = 681653) B681653
theorem B454451 : Blo 451781 454451 := bstep (se 1 (by rfl) ⟨340838, by rfl⟩ : syracuseStep 454451 = 681677) B681677
theorem B454467 : Blo 451781 454467 := bstep (se 1 (by rfl) ⟨340850, by rfl⟩ : syracuseStep 454467 = 681701) B681701
theorem B454483 : Blo 451781 454483 := bstep (se 1 (by rfl) ⟨340862, by rfl⟩ : syracuseStep 454483 = 681725) B681725
theorem B454499 : Blo 451781 454499 := bstep (se 1 (by rfl) ⟨340874, by rfl⟩ : syracuseStep 454499 = 681749) B681749
theorem B454515 : Blo 451781 454515 := bstep (se 1 (by rfl) ⟨340886, by rfl⟩ : syracuseStep 454515 = 681773) B681773
theorem B454531 : Blo 451781 454531 := bstep (se 1 (by rfl) ⟨340898, by rfl⟩ : syracuseStep 454531 = 681797) B681797
theorem B454547 : Blo 451781 454547 := bstep (se 1 (by rfl) ⟨340910, by rfl⟩ : syracuseStep 454547 = 681821) B681821
theorem B454563 : Blo 451781 454563 := bstep (se 1 (by rfl) ⟨340922, by rfl⟩ : syracuseStep 454563 = 681845) B681845
theorem B1535921 : Blo 451781 1535921 := bstep (se 2 (by rfl) ⟨575970, by rfl⟩ : syracuseStep 1535921 = 1151941) B1151941
theorem B454579 : Blo 451781 454579 := bstep (se 1 (by rfl) ⟨340934, by rfl⟩ : syracuseStep 454579 = 681869) B681869
theorem B454595 : Blo 451781 454595 := bstep (se 1 (by rfl) ⟨340946, by rfl⟩ : syracuseStep 454595 = 681893) B681893
theorem B454611 : Blo 451781 454611 := bstep (se 1 (by rfl) ⟨340958, by rfl⟩ : syracuseStep 454611 = 681917) B681917
theorem B454627 : Blo 451781 454627 := bstep (se 1 (by rfl) ⟨340970, by rfl⟩ : syracuseStep 454627 = 681941) B681941
theorem B454643 : Blo 451781 454643 := bstep (se 1 (by rfl) ⟨340982, by rfl⟩ : syracuseStep 454643 = 681965) B681965
theorem B454659 : Blo 451781 454659 := bstep (se 1 (by rfl) ⟨340994, by rfl⟩ : syracuseStep 454659 = 681989) B681989
theorem B454675 : Blo 451781 454675 := bstep (se 1 (by rfl) ⟨341006, by rfl⟩ : syracuseStep 454675 = 682013) B682013
theorem B454691 : Blo 451781 454691 := bstep (se 1 (by rfl) ⟨341018, by rfl⟩ : syracuseStep 454691 = 682037) B682037
theorem B815153 : Blo 451781 815153 := bstep (se 2 (by rfl) ⟨305682, by rfl⟩ : syracuseStep 815153 = 611365) B611365
theorem B454707 : Blo 451781 454707 := bstep (se 1 (by rfl) ⟨341030, by rfl⟩ : syracuseStep 454707 = 682061) B682061
theorem B454723 : Blo 451781 454723 := bstep (se 1 (by rfl) ⟨341042, by rfl⟩ : syracuseStep 454723 = 682085) B682085
theorem B454739 : Blo 451781 454739 := bstep (se 1 (by rfl) ⟨341054, by rfl⟩ : syracuseStep 454739 = 682109) B682109
theorem B454755 : Blo 451781 454755 := bstep (se 1 (by rfl) ⟨341066, by rfl⟩ : syracuseStep 454755 = 682133) B682133
theorem B454771 : Blo 451781 454771 := bstep (se 1 (by rfl) ⟨341078, by rfl⟩ : syracuseStep 454771 = 682157) B682157
theorem B454787 : Blo 451781 454787 := bstep (se 1 (by rfl) ⟨341090, by rfl⟩ : syracuseStep 454787 = 682181) B682181
theorem B454803 : Blo 451781 454803 := bstep (se 1 (by rfl) ⟨341102, by rfl⟩ : syracuseStep 454803 = 682205) B682205
theorem B454819 : Blo 451781 454819 := bstep (se 1 (by rfl) ⟨341114, by rfl⟩ : syracuseStep 454819 = 682229) B682229
theorem B454835 : Blo 451781 454835 := bstep (se 1 (by rfl) ⟨341126, by rfl⟩ : syracuseStep 454835 = 682253) B682253
theorem B454851 : Blo 451781 454851 := bstep (se 1 (by rfl) ⟨341138, by rfl⟩ : syracuseStep 454851 = 682277) B682277
theorem B2289869 : Blo 451781 2289869 := bstep (se 3 (by rfl) ⟨429350, by rfl⟩ : syracuseStep 2289869 = 858701) B858701
theorem B454867 : Blo 451781 454867 := bstep (se 1 (by rfl) ⟨341150, by rfl⟩ : syracuseStep 454867 = 682301) B682301
theorem B454883 : Blo 451781 454883 := bstep (se 1 (by rfl) ⟨341162, by rfl⟩ : syracuseStep 454883 = 682325) B682325
theorem B454899 : Blo 451781 454899 := bstep (se 1 (by rfl) ⟨341174, by rfl⟩ : syracuseStep 454899 = 682349) B682349
theorem B454915 : Blo 451781 454915 := bstep (se 1 (by rfl) ⟨341186, by rfl⟩ : syracuseStep 454915 = 682373) B682373
theorem B454931 : Blo 451781 454931 := bstep (se 1 (by rfl) ⟨341198, by rfl⟩ : syracuseStep 454931 = 682397) B682397
theorem B454947 : Blo 451781 454947 := bstep (se 1 (by rfl) ⟨341210, by rfl⟩ : syracuseStep 454947 = 682421) B682421
theorem B454963 : Blo 451781 454963 := bstep (se 1 (by rfl) ⟨341222, by rfl⟩ : syracuseStep 454963 = 682445) B682445
theorem B454979 : Blo 451781 454979 := bstep (se 1 (by rfl) ⟨341234, by rfl⟩ : syracuseStep 454979 = 682469) B682469
theorem B454995 : Blo 451781 454995 := bstep (se 1 (by rfl) ⟨341246, by rfl⟩ : syracuseStep 454995 = 682493) B682493
theorem B455011 : Blo 451781 455011 := bstep (se 1 (by rfl) ⟨341258, by rfl⟩ : syracuseStep 455011 = 682517) B682517
theorem B455027 : Blo 451781 455027 := bstep (se 1 (by rfl) ⟨341270, by rfl⟩ : syracuseStep 455027 = 682541) B682541
theorem B455043 : Blo 451781 455043 := bstep (se 1 (by rfl) ⟨341282, by rfl⟩ : syracuseStep 455043 = 682565) B682565
theorem B455059 : Blo 451781 455059 := bstep (se 1 (by rfl) ⟨341294, by rfl⟩ : syracuseStep 455059 = 682589) B682589
theorem B455075 : Blo 451781 455075 := bstep (se 1 (by rfl) ⟨341306, by rfl⟩ : syracuseStep 455075 = 682613) B682613
theorem B455091 : Blo 451781 455091 := bstep (se 1 (by rfl) ⟨341318, by rfl⟩ : syracuseStep 455091 = 682637) B682637
theorem B455107 : Blo 451781 455107 := bstep (se 1 (by rfl) ⟨341330, by rfl⟩ : syracuseStep 455107 = 682661) B682661
theorem B1536461 : Blo 451781 1536461 := bstep (se 3 (by rfl) ⟨288086, by rfl⟩ : syracuseStep 1536461 = 576173) B576173
theorem B455123 : Blo 451781 455123 := bstep (se 1 (by rfl) ⟨341342, by rfl⟩ : syracuseStep 455123 = 682685) B682685
theorem B455139 : Blo 451781 455139 := bstep (se 1 (by rfl) ⟨341354, by rfl⟩ : syracuseStep 455139 = 682709) B682709
theorem B455155 : Blo 451781 455155 := bstep (se 1 (by rfl) ⟨341366, by rfl⟩ : syracuseStep 455155 = 682733) B682733
theorem B455171 : Blo 451781 455171 := bstep (se 1 (by rfl) ⟨341378, by rfl⟩ : syracuseStep 455171 = 682757) B682757
theorem B1536515 : Blo 451781 1536515 := bstep (se 1 (by rfl) ⟨1152386, by rfl⟩ : syracuseStep 1536515 = 2304773) B2304773
theorem B455187 : Blo 451781 455187 := bstep (se 1 (by rfl) ⟨341390, by rfl⟩ : syracuseStep 455187 = 682781) B682781
theorem B455203 : Blo 451781 455203 := bstep (se 1 (by rfl) ⟨341402, by rfl⟩ : syracuseStep 455203 = 682805) B682805
theorem B455219 : Blo 451781 455219 := bstep (se 1 (by rfl) ⟨341414, by rfl⟩ : syracuseStep 455219 = 682829) B682829
theorem B455235 : Blo 451781 455235 := bstep (se 1 (by rfl) ⟨341426, by rfl⟩ : syracuseStep 455235 = 682853) B682853
theorem B455251 : Blo 451781 455251 := bstep (se 1 (by rfl) ⟨341438, by rfl⟩ : syracuseStep 455251 = 682877) B682877
theorem B455267 : Blo 451781 455267 := bstep (se 1 (by rfl) ⟨341450, by rfl⟩ : syracuseStep 455267 = 682901) B682901
theorem B455283 : Blo 451781 455283 := bstep (se 1 (by rfl) ⟨341462, by rfl⟩ : syracuseStep 455283 = 682925) B682925
theorem B455299 : Blo 451781 455299 := bstep (se 1 (by rfl) ⟨341474, by rfl⟩ : syracuseStep 455299 = 682949) B682949
theorem B455315 : Blo 451781 455315 := bstep (se 1 (by rfl) ⟨341486, by rfl⟩ : syracuseStep 455315 = 682973) B682973
theorem B455331 : Blo 451781 455331 := bstep (se 1 (by rfl) ⟨341498, by rfl⟩ : syracuseStep 455331 = 682997) B682997
theorem B455347 : Blo 451781 455347 := bstep (se 1 (by rfl) ⟨341510, by rfl⟩ : syracuseStep 455347 = 683021) B683021
theorem B455363 : Blo 451781 455363 := bstep (se 1 (by rfl) ⟨341522, by rfl⟩ : syracuseStep 455363 = 683045) B683045
theorem B455379 : Blo 451781 455379 := bstep (se 1 (by rfl) ⟨341534, by rfl⟩ : syracuseStep 455379 = 683069) B683069
theorem B455395 : Blo 451781 455395 := bstep (se 1 (by rfl) ⟨341546, by rfl⟩ : syracuseStep 455395 = 683093) B683093
theorem B455411 : Blo 451781 455411 := bstep (se 1 (by rfl) ⟨341558, by rfl⟩ : syracuseStep 455411 = 683117) B683117
theorem B455427 : Blo 451781 455427 := bstep (se 1 (by rfl) ⟨341570, by rfl⟩ : syracuseStep 455427 = 683141) B683141
theorem B1536785 : Blo 451781 1536785 := bstep (se 2 (by rfl) ⟨576294, by rfl⟩ : syracuseStep 1536785 = 1152589) B1152589
theorem B455443 : Blo 451781 455443 := bstep (se 1 (by rfl) ⟨341582, by rfl⟩ : syracuseStep 455443 = 683165) B683165
theorem B455459 : Blo 451781 455459 := bstep (se 1 (by rfl) ⟨341594, by rfl⟩ : syracuseStep 455459 = 683189) B683189
theorem B1471277 : Blo 451781 1471277 := bstep (se 3 (by rfl) ⟨275864, by rfl⟩ : syracuseStep 1471277 = 551729) B551729
theorem B455475 : Blo 451781 455475 := bstep (se 1 (by rfl) ⟨341606, by rfl⟩ : syracuseStep 455475 = 683213) B683213
theorem B455491 : Blo 451781 455491 := bstep (se 1 (by rfl) ⟨341618, by rfl⟩ : syracuseStep 455491 = 683237) B683237
theorem B455507 : Blo 451781 455507 := bstep (se 1 (by rfl) ⟨341630, by rfl⟩ : syracuseStep 455507 = 683261) B683261
theorem B455523 : Blo 451781 455523 := bstep (se 1 (by rfl) ⟨341642, by rfl⟩ : syracuseStep 455523 = 683285) B683285
theorem B455539 : Blo 451781 455539 := bstep (se 1 (by rfl) ⟨341654, by rfl⟩ : syracuseStep 455539 = 683309) B683309
theorem B455555 : Blo 451781 455555 := bstep (se 1 (by rfl) ⟨341666, by rfl⟩ : syracuseStep 455555 = 683333) B683333
theorem B62813069 : Blo 451781 62813069 := bstep (se 3 (by rfl) ⟨11777450, by rfl⟩ : syracuseStep 62813069 = 23554901) B23554901
theorem B455571 : Blo 451781 455571 := bstep (se 1 (by rfl) ⟨341678, by rfl⟩ : syracuseStep 455571 = 683357) B683357
theorem B455587 : Blo 451781 455587 := bstep (se 1 (by rfl) ⟨341690, by rfl⟩ : syracuseStep 455587 = 683381) B683381
theorem B455603 : Blo 451781 455603 := bstep (se 1 (by rfl) ⟨341702, by rfl⟩ : syracuseStep 455603 = 683405) B683405
theorem B455619 : Blo 451781 455619 := bstep (se 1 (by rfl) ⟨341714, by rfl⟩ : syracuseStep 455619 = 683429) B683429
theorem B455635 : Blo 451781 455635 := bstep (se 1 (by rfl) ⟨341726, by rfl⟩ : syracuseStep 455635 = 683453) B683453
theorem B455651 : Blo 451781 455651 := bstep (se 1 (by rfl) ⟨341738, by rfl⟩ : syracuseStep 455651 = 683477) B683477
theorem B455667 : Blo 451781 455667 := bstep (se 1 (by rfl) ⟨341750, by rfl⟩ : syracuseStep 455667 = 683501) B683501
theorem B455683 : Blo 451781 455683 := bstep (se 1 (by rfl) ⟨341762, by rfl⟩ : syracuseStep 455683 = 683525) B683525
theorem B455699 : Blo 451781 455699 := bstep (se 1 (by rfl) ⟨341774, by rfl⟩ : syracuseStep 455699 = 683549) B683549
theorem B455715 : Blo 451781 455715 := bstep (se 1 (by rfl) ⟨341786, by rfl⟩ : syracuseStep 455715 = 683573) B683573
theorem B455731 : Blo 451781 455731 := bstep (se 1 (by rfl) ⟨341798, by rfl⟩ : syracuseStep 455731 = 683597) B683597
theorem B455747 : Blo 451781 455747 := bstep (se 1 (by rfl) ⟨341810, by rfl⟩ : syracuseStep 455747 = 683621) B683621
theorem B455763 : Blo 451781 455763 := bstep (se 1 (by rfl) ⟨341822, by rfl⟩ : syracuseStep 455763 = 683645) B683645
theorem B455779 : Blo 451781 455779 := bstep (se 1 (by rfl) ⟨341834, by rfl⟩ : syracuseStep 455779 = 683669) B683669
theorem B1143953 : Blo 451781 1143953 := bstep (se 2 (by rfl) ⟨428982, by rfl⟩ : syracuseStep 1143953 = 857965) B857965
theorem B1144003 : Blo 451781 1144003 := bstep (se 1 (by rfl) ⟨858002, by rfl⟩ : syracuseStep 1144003 = 1716005) B1716005
theorem B1537325 : Blo 451781 1537325 := bstep (se 3 (by rfl) ⟨288248, by rfl⟩ : syracuseStep 1537325 = 576497) B576497
theorem B1144145 : Blo 451781 1144145 := bstep (se 2 (by rfl) ⟨429054, by rfl⟩ : syracuseStep 1144145 = 858109) B858109
theorem B1537379 : Blo 451781 1537379 := bstep (se 1 (by rfl) ⟨1153034, by rfl⟩ : syracuseStep 1537379 = 2306069) B2306069
theorem B2913677 : Blo 451781 2913677 := bstep (se 3 (by rfl) ⟨546314, by rfl⟩ : syracuseStep 2913677 = 1092629) B1092629
theorem B554435 : Blo 451781 554435 := bstep (se 1 (by rfl) ⟨415826, by rfl⟩ : syracuseStep 554435 = 831653) B831653
theorem B2618993 : Blo 451781 2618993 := bstep (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) B1964245
theorem B1537649 : Blo 451781 1537649 := bstep (se 2 (by rfl) ⟨576618, by rfl⟩ : syracuseStep 1537649 = 1153237) B1153237
theorem B2619013 : Blo 451781 2619013 := bstep (se 4 (by rfl) ⟨245532, by rfl⟩ : syracuseStep 2619013 = 491065) B491065
theorem B816913 : Blo 451781 816913 := bstep (se 2 (by rfl) ⟨306342, by rfl⟩ : syracuseStep 816913 = 612685) B612685
theorem B3438449 : Blo 451781 3438449 := bstep (se 2 (by rfl) ⟨1289418, by rfl⟩ : syracuseStep 3438449 = 2578837) B2578837
theorem B2455409 : Blo 451781 2455409 := bstep (se 2 (by rfl) ⟨920778, by rfl⟩ : syracuseStep 2455409 = 1841557) B1841557
theorem B1832867 : Blo 451781 1832867 := bstep (se 1 (by rfl) ⟨1374650, by rfl⟩ : syracuseStep 1832867 = 2749301) B2749301
theorem B2947013 : Blo 451781 2947013 := bstep (se 4 (by rfl) ⟨276282, by rfl⟩ : syracuseStep 2947013 = 552565) B552565
theorem B1538189 : Blo 451781 1538189 := bstep (se 3 (by rfl) ⟨288410, by rfl⟩ : syracuseStep 1538189 = 576821) B576821
theorem B981155 : Blo 451781 981155 := bstep (se 1 (by rfl) ⟨735866, by rfl⟩ : syracuseStep 981155 = 1471733) B1471733
theorem B1538243 : Blo 451781 1538243 := bstep (se 1 (by rfl) ⟨1153682, by rfl⟩ : syracuseStep 1538243 = 2307365) B2307365
theorem B2455757 : Blo 451781 2455757 := bstep (se 3 (by rfl) ⟨460454, by rfl⟩ : syracuseStep 2455757 = 920909) B920909
theorem B1145137 : Blo 451781 1145137 := bstep (se 2 (by rfl) ⟨429426, by rfl⟩ : syracuseStep 1145137 = 858853) B858853
theorem B1571185 : Blo 451781 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B2587085 : Blo 451781 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B1931789 : Blo 451781 1931789 := bstep (se 3 (by rfl) ⟨362210, by rfl⟩ : syracuseStep 1931789 = 724421) B724421
theorem B2095651 : Blo 451781 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B1145411 : Blo 451781 1145411 := bstep (se 1 (by rfl) ⟨859058, by rfl⟩ : syracuseStep 1145411 = 1718117) B1718117
theorem B916067 : Blo 451781 916067 := bstep (se 1 (by rfl) ⟨687050, by rfl⟩ : syracuseStep 916067 = 1374101) B1374101
theorem B9435761 : Blo 451781 9435761 := bstep (se 2 (by rfl) ⟨3538410, by rfl⟩ : syracuseStep 9435761 = 7076821) B7076821
theorem B1145603 : Blo 451781 1145603 := bstep (se 1 (by rfl) ⟨859202, by rfl⟩ : syracuseStep 1145603 = 1718405) B1718405
theorem B2292785 : Blo 451781 2292785 := bstep (se 2 (by rfl) ⟨859794, by rfl⟩ : syracuseStep 2292785 = 1719589) B1719589
theorem B687251 : Blo 451781 687251 := bstep (se 1 (by rfl) ⟨515438, by rfl⟩ : syracuseStep 687251 = 1030877) B1030877
theorem B1375427 : Blo 451781 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B1637603 : Blo 451781 1637603 := bstep (se 1 (by rfl) ⟨1228202, by rfl⟩ : syracuseStep 1637603 = 2456405) B2456405
theorem B1375501 : Blo 451781 1375501 := bstep (se 3 (by rfl) ⟨257906, by rfl⟩ : syracuseStep 1375501 = 515813) B515813
theorem B1146545 : Blo 451781 1146545 := bstep (se 2 (by rfl) ⟨429954, by rfl⟩ : syracuseStep 1146545 = 859909) B859909
theorem B1146595 : Blo 451781 1146595 := bstep (se 1 (by rfl) ⟨859946, by rfl⟩ : syracuseStep 1146595 = 1719893) B1719893
theorem B655169 : Blo 451781 655169 := bstep (se 2 (by rfl) ⟨245688, by rfl⟩ : syracuseStep 655169 = 491377) B491377
theorem B819011 : Blo 451781 819011 := bstep (se 1 (by rfl) ⟨614258, by rfl⟩ : syracuseStep 819011 = 1228517) B1228517
theorem B1146737 : Blo 451781 1146737 := bstep (se 2 (by rfl) ⟨430026, by rfl⟩ : syracuseStep 1146737 = 860053) B860053
theorem B1147031 : Blo 451781 1147031 := bstep (se 1 (by rfl) ⟨860273, by rfl⟩ : syracuseStep 1147031 = 1720547) B1720547
theorem B27885869 : Blo 451781 27885869 := bstep (se 3 (by rfl) ⟨5228600, by rfl⟩ : syracuseStep 27885869 = 10457201) B10457201
theorem B2294081 : Blo 451781 2294081 := bstep (se 2 (by rfl) ⟨860280, by rfl⟩ : syracuseStep 2294081 = 1720561) B1720561
theorem B1016513 : Blo 451781 1016513 := bstep (se 2 (by rfl) ⟨381192, by rfl⟩ : syracuseStep 1016513 = 762385) B762385
theorem B1934027 : Blo 451781 1934027 := bstep (se 1 (by rfl) ⟨1450520, by rfl⟩ : syracuseStep 1934027 = 2901041) B2901041
theorem B918233 : Blo 451781 918233 := bstep (se 2 (by rfl) ⟨344337, by rfl⟩ : syracuseStep 918233 = 688675) B688675
theorem B5899013 : Blo 451781 5899013 := bstep (se 4 (by rfl) ⟨553032, by rfl⟩ : syracuseStep 5899013 = 1106065) B1106065
theorem B459595 : Blo 451781 459595 := bstep (se 1 (by rfl) ⟨344696, by rfl⟩ : syracuseStep 459595 = 689393) B689393
theorem B820055 : Blo 451781 820055 := bstep (se 1 (by rfl) ⟨615041, by rfl⟩ : syracuseStep 820055 = 1230083) B1230083
theorem B1016729 : Blo 451781 1016729 := bstep (se 2 (by rfl) ⟨381273, by rfl⟩ : syracuseStep 1016729 = 762547) B762547
theorem B3277745 : Blo 451781 3277745 := bstep (se 2 (by rfl) ⟨1229154, by rfl⟩ : syracuseStep 3277745 = 2458309) B2458309
theorem B1147841 : Blo 451781 1147841 := bstep (se 2 (by rfl) ⟨430440, by rfl⟩ : syracuseStep 1147841 = 860881) B860881
theorem B1016819 : Blo 451781 1016819 := bstep (se 1 (by rfl) ⟨762614, by rfl⟩ : syracuseStep 1016819 = 1525229) B1525229
theorem B1016855 : Blo 451781 1016855 := bstep (se 1 (by rfl) ⟨762641, by rfl⟩ : syracuseStep 1016855 = 1525283) B1525283
theorem B1934387 : Blo 451781 1934387 := bstep (se 1 (by rfl) ⟨1450790, by rfl⟩ : syracuseStep 1934387 = 2901581) B2901581
theorem B1017035 : Blo 451781 1017035 := bstep (se 1 (by rfl) ⟨762776, by rfl⟩ : syracuseStep 1017035 = 1525553) B1525553
theorem B3278029 : Blo 451781 3278029 := bstep (se 3 (by rfl) ⟨614630, by rfl⟩ : syracuseStep 3278029 = 1229261) B1229261
theorem B1017089 : Blo 451781 1017089 := bstep (se 2 (by rfl) ⟨381408, by rfl⟩ : syracuseStep 1017089 = 762817) B762817
theorem B1770817 : Blo 451781 1770817 := bstep (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) B1328113
theorem B1017305 : Blo 451781 1017305 := bstep (se 2 (by rfl) ⟨381489, by rfl⟩ : syracuseStep 1017305 = 762979) B762979
theorem B1148377 : Blo 451781 1148377 := bstep (se 2 (by rfl) ⟨430641, by rfl⟩ : syracuseStep 1148377 = 861283) B861283
theorem B15926797 : Blo 451781 15926797 := bstep (se 3 (by rfl) ⟨2986274, by rfl⟩ : syracuseStep 15926797 = 5972549) B5972549
theorem B1017395 : Blo 451781 1017395 := bstep (se 1 (by rfl) ⟨763046, by rfl⟩ : syracuseStep 1017395 = 1526093) B1526093
theorem B1017431 : Blo 451781 1017431 := bstep (se 1 (by rfl) ⟨763073, by rfl⟩ : syracuseStep 1017431 = 1526147) B1526147
theorem B525911 : Blo 451781 525911 := bstep (se 1 (by rfl) ⟨394433, by rfl⟩ : syracuseStep 525911 = 788867) B788867
theorem B4130509 : Blo 451781 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B1017611 : Blo 451781 1017611 := bstep (se 1 (by rfl) ⟨763208, by rfl⟩ : syracuseStep 1017611 = 1526417) B1526417
theorem B1017665 : Blo 451781 1017665 := bstep (se 2 (by rfl) ⟨381624, by rfl⟩ : syracuseStep 1017665 = 763249) B763249
theorem B1640371 : Blo 451781 1640371 := bstep (se 1 (by rfl) ⟨1230278, by rfl⟩ : syracuseStep 1640371 = 2460557) B2460557
theorem B919513 : Blo 451781 919513 := bstep (se 2 (by rfl) ⟨344817, by rfl⟩ : syracuseStep 919513 = 689635) B689635
theorem B1017881 : Blo 451781 1017881 := bstep (se 2 (by rfl) ⟨381705, by rfl⟩ : syracuseStep 1017881 = 763411) B763411
theorem B1017971 : Blo 451781 1017971 := bstep (se 1 (by rfl) ⟨763478, by rfl⟩ : syracuseStep 1017971 = 1526957) B1526957
theorem B1018007 : Blo 451781 1018007 := bstep (se 1 (by rfl) ⟨763505, by rfl⟩ : syracuseStep 1018007 = 1527011) B1527011
theorem B2296025 : Blo 451781 2296025 := bstep (se 2 (by rfl) ⟨861009, by rfl⟩ : syracuseStep 2296025 = 1722019) B1722019
theorem B6621425 : Blo 451781 6621425 := bstep (se 2 (by rfl) ⟨2483034, by rfl⟩ : syracuseStep 6621425 = 4966069) B4966069
theorem B919831 : Blo 451781 919831 := bstep (se 1 (by rfl) ⟨689873, by rfl⟩ : syracuseStep 919831 = 1379747) B1379747
theorem B1018187 : Blo 451781 1018187 := bstep (se 1 (by rfl) ⟨763640, by rfl⟩ : syracuseStep 1018187 = 1527281) B1527281
theorem B1018241 : Blo 451781 1018241 := bstep (se 2 (by rfl) ⟨381840, by rfl⟩ : syracuseStep 1018241 = 763681) B763681
theorem B1149491 : Blo 451781 1149491 := bstep (se 1 (by rfl) ⟨862118, by rfl⟩ : syracuseStep 1149491 = 1724237) B1724237
theorem B920129 : Blo 451781 920129 := bstep (se 2 (by rfl) ⟨345048, by rfl⟩ : syracuseStep 920129 = 690097) B690097
theorem B1018457 : Blo 451781 1018457 := bstep (se 2 (by rfl) ⟨381921, by rfl⟩ : syracuseStep 1018457 = 763843) B763843
theorem B1018547 : Blo 451781 1018547 := bstep (se 1 (by rfl) ⟨763910, by rfl⟩ : syracuseStep 1018547 = 1527821) B1527821
theorem B1018583 : Blo 451781 1018583 := bstep (se 1 (by rfl) ⟨763937, by rfl⟩ : syracuseStep 1018583 = 1527875) B1527875
theorem B985907 : Blo 451781 985907 := bstep (se 1 (by rfl) ⟨739430, by rfl⟩ : syracuseStep 985907 = 1478861) B1478861
theorem B1149785 : Blo 451781 1149785 := bstep (se 2 (by rfl) ⟨431169, by rfl⟩ : syracuseStep 1149785 = 862339) B862339
theorem B1018763 : Blo 451781 1018763 := bstep (se 1 (by rfl) ⟨764072, by rfl⟩ : syracuseStep 1018763 = 1528145) B1528145
theorem B723863 : Blo 451781 723863 := bstep (se 1 (by rfl) ⟨542897, by rfl⟩ : syracuseStep 723863 = 1085795) B1085795
theorem B1018817 : Blo 451781 1018817 := bstep (se 2 (by rfl) ⟨382056, by rfl⟩ : syracuseStep 1018817 = 764113) B764113
theorem B21269465 : Blo 451781 21269465 := bstep (se 2 (by rfl) ⟨7976049, by rfl⟩ : syracuseStep 21269465 = 15952099) B15952099
theorem B5049305 : Blo 451781 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B6556747 : Blo 451781 6556747 := bstep (se 1 (by rfl) ⟨4917560, by rfl⟩ : syracuseStep 6556747 = 9835121) B9835121
theorem B1019033 : Blo 451781 1019033 := bstep (se 2 (by rfl) ⟨382137, by rfl⟩ : syracuseStep 1019033 = 764275) B764275
theorem B1117363 : Blo 451781 1117363 := bstep (se 1 (by rfl) ⟨838022, by rfl⟩ : syracuseStep 1117363 = 1676045) B1676045
theorem B7834805 : Blo 451781 7834805 := bstep (se 5 (by rfl) ⟨367256, by rfl⟩ : syracuseStep 7834805 = 734513) B734513
theorem B1019123 : Blo 451781 1019123 := bstep (se 1 (by rfl) ⟨764342, by rfl⟩ : syracuseStep 1019123 = 1528685) B1528685
theorem B1019159 : Blo 451781 1019159 := bstep (se 1 (by rfl) ⟨764369, by rfl⟩ : syracuseStep 1019159 = 1528739) B1528739
theorem B1019339 : Blo 451781 1019339 := bstep (se 1 (by rfl) ⟨764504, by rfl⟩ : syracuseStep 1019339 = 1529009) B1529009
theorem B691673 : Blo 451781 691673 := bstep (se 2 (by rfl) ⟨259377, by rfl⟩ : syracuseStep 691673 = 518755) B518755
theorem B1019393 : Blo 451781 1019393 := bstep (se 2 (by rfl) ⟨382272, by rfl⟩ : syracuseStep 1019393 = 764545) B764545
theorem B1969667 : Blo 451781 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B724555 : Blo 451781 724555 := bstep (se 1 (by rfl) ⟨543416, by rfl⟩ : syracuseStep 724555 = 1086833) B1086833
theorem B1642187 : Blo 451781 1642187 := bstep (se 1 (by rfl) ⟨1231640, by rfl⟩ : syracuseStep 1642187 = 2463281) B2463281
theorem B724697 : Blo 451781 724697 := bstep (se 2 (by rfl) ⟨271761, by rfl⟩ : syracuseStep 724697 = 543523) B543523
theorem B1019609 : Blo 451781 1019609 := bstep (se 2 (by rfl) ⟨382353, by rfl⟩ : syracuseStep 1019609 = 764707) B764707
theorem B2297645 : Blo 451781 2297645 := bstep (se 3 (by rfl) ⟨430808, by rfl⟩ : syracuseStep 2297645 = 861617) B861617
theorem B1019699 : Blo 451781 1019699 := bstep (se 1 (by rfl) ⟨764774, by rfl⟩ : syracuseStep 1019699 = 1529549) B1529549
theorem B1019735 : Blo 451781 1019735 := bstep (se 1 (by rfl) ⟨764801, by rfl⟩ : syracuseStep 1019735 = 1529603) B1529603
theorem B1019915 : Blo 451781 1019915 := bstep (se 1 (by rfl) ⟨764936, by rfl⟩ : syracuseStep 1019915 = 1529873) B1529873
theorem B1019969 : Blo 451781 1019969 := bstep (se 2 (by rfl) ⟨382488, by rfl⟩ : syracuseStep 1019969 = 764977) B764977
theorem B692311 : Blo 451781 692311 := bstep (se 1 (by rfl) ⟨519233, by rfl⟩ : syracuseStep 692311 = 1038467) B1038467
theorem B1085633 : Blo 451781 1085633 := bstep (se 2 (by rfl) ⟨407112, by rfl⟩ : syracuseStep 1085633 = 814225) B814225
theorem B921817 : Blo 451781 921817 := bstep (se 2 (by rfl) ⟨345681, by rfl⟩ : syracuseStep 921817 = 691363) B691363
theorem B7737605 : Blo 451781 7737605 := bstep (se 4 (by rfl) ⟨725400, by rfl⟩ : syracuseStep 7737605 = 1450801) B1450801
theorem B1020185 : Blo 451781 1020185 := bstep (se 2 (by rfl) ⟨382569, by rfl⟩ : syracuseStep 1020185 = 765139) B765139
theorem B6983981 : Blo 451781 6983981 := bstep (se 3 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 6983981 = 2618993) B2618993
theorem B1020275 : Blo 451781 1020275 := bstep (se 1 (by rfl) ⟨765206, by rfl⟩ : syracuseStep 1020275 = 1530413) B1530413
theorem B1020311 : Blo 451781 1020311 := bstep (se 1 (by rfl) ⟨765233, by rfl⟩ : syracuseStep 1020311 = 1530467) B1530467
theorem B1151435 : Blo 451781 1151435 := bstep (se 1 (by rfl) ⟨863576, by rfl⟩ : syracuseStep 1151435 = 1727153) B1727153
theorem B3445253 : Blo 451781 3445253 := bstep (se 4 (by rfl) ⟨322992, by rfl⟩ : syracuseStep 3445253 = 645985) B645985
theorem B1020491 : Blo 451781 1020491 := bstep (se 1 (by rfl) ⟨765368, by rfl⟩ : syracuseStep 1020491 = 1530737) B1530737
theorem B1020545 : Blo 451781 1020545 := bstep (se 2 (by rfl) ⟨382704, by rfl⟩ : syracuseStep 1020545 = 765409) B765409
theorem B725657 : Blo 451781 725657 := bstep (se 2 (by rfl) ⟨272121, by rfl⟩ : syracuseStep 725657 = 544243) B544243
theorem B1020761 : Blo 451781 1020761 := bstep (se 2 (by rfl) ⟨382785, by rfl⟩ : syracuseStep 1020761 = 765571) B765571
theorem B1020851 : Blo 451781 1020851 := bstep (se 1 (by rfl) ⟨765638, by rfl⟩ : syracuseStep 1020851 = 1531277) B1531277
theorem B1020887 : Blo 451781 1020887 := bstep (se 1 (by rfl) ⟨765665, by rfl⟩ : syracuseStep 1020887 = 1531331) B1531331
theorem B1021067 : Blo 451781 1021067 := bstep (se 1 (by rfl) ⟨765800, by rfl⟩ : syracuseStep 1021067 = 1531601) B1531601
theorem B2593943 : Blo 451781 2593943 := bstep (se 1 (by rfl) ⟨1945457, by rfl⟩ : syracuseStep 2593943 = 3890915) B3890915
theorem B1021121 : Blo 451781 1021121 := bstep (se 2 (by rfl) ⟨382920, by rfl⟩ : syracuseStep 1021121 = 765841) B765841
theorem B1152407 : Blo 451781 1152407 := bstep (se 1 (by rfl) ⟨864305, by rfl⟩ : syracuseStep 1152407 = 1728611) B1728611
theorem B1021337 : Blo 451781 1021337 := bstep (se 2 (by rfl) ⟨383001, by rfl⟩ : syracuseStep 1021337 = 766003) B766003
theorem B3478963 : Blo 451781 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B1021427 : Blo 451781 1021427 := bstep (se 1 (by rfl) ⟨766070, by rfl⟩ : syracuseStep 1021427 = 1532141) B1532141
theorem B1021463 : Blo 451781 1021463 := bstep (se 1 (by rfl) ⟨766097, by rfl⟩ : syracuseStep 1021463 = 1532195) B1532195
theorem B3872357 : Blo 451781 3872357 := bstep (se 4 (by rfl) ⟨363033, by rfl⟩ : syracuseStep 3872357 = 726067) B726067
theorem B857729 : Blo 451781 857729 := bstep (se 2 (by rfl) ⟨321648, by rfl⟩ : syracuseStep 857729 = 643297) B643297
theorem B1021643 : Blo 451781 1021643 := bstep (se 1 (by rfl) ⟨766232, by rfl⟩ : syracuseStep 1021643 = 1532465) B1532465
theorem B1021697 : Blo 451781 1021697 := bstep (se 2 (by rfl) ⟨383136, by rfl⟩ : syracuseStep 1021697 = 766273) B766273
theorem B857881 : Blo 451781 857881 := bstep (se 2 (by rfl) ⟨321705, by rfl⟩ : syracuseStep 857881 = 643411) B643411
theorem B1120151 : Blo 451781 1120151 := bstep (se 1 (by rfl) ⟨840113, by rfl⟩ : syracuseStep 1120151 = 1680227) B1680227
theorem B1021913 : Blo 451781 1021913 := bstep (se 2 (by rfl) ⟨383217, by rfl⟩ : syracuseStep 1021913 = 766435) B766435
theorem B1939459 : Blo 451781 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B1022003 : Blo 451781 1022003 := bstep (se 1 (by rfl) ⟨766502, by rfl⟩ : syracuseStep 1022003 = 1533005) B1533005
theorem B1153075 : Blo 451781 1153075 := bstep (se 1 (by rfl) ⟨864806, by rfl⟩ : syracuseStep 1153075 = 1729613) B1729613
theorem B1022039 : Blo 451781 1022039 := bstep (se 1 (by rfl) ⟨766529, by rfl⟩ : syracuseStep 1022039 = 1533059) B1533059
theorem B1153217 : Blo 451781 1153217 := bstep (se 2 (by rfl) ⟨432456, by rfl⟩ : syracuseStep 1153217 = 864913) B864913
theorem B1022219 : Blo 451781 1022219 := bstep (se 1 (by rfl) ⟨766664, by rfl⟩ : syracuseStep 1022219 = 1533329) B1533329
theorem B3873041 : Blo 451781 3873041 := bstep (se 2 (by rfl) ⟨1452390, by rfl⟩ : syracuseStep 3873041 = 2904781) B2904781
theorem B1022273 : Blo 451781 1022273 := bstep (se 2 (by rfl) ⟨383352, by rfl⟩ : syracuseStep 1022273 = 766705) B766705
theorem B1939801 : Blo 451781 1939801 := bstep (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) B1454851
theorem B1022489 : Blo 451781 1022489 := bstep (se 2 (by rfl) ⟨383433, by rfl⟩ : syracuseStep 1022489 = 766867) B766867
theorem B2333249 : Blo 451781 2333249 := bstep (se 2 (by rfl) ⟨874968, by rfl⟩ : syracuseStep 2333249 = 1749937) B1749937
theorem B1022579 : Blo 451781 1022579 := bstep (se 1 (by rfl) ⟨766934, by rfl⟩ : syracuseStep 1022579 = 1533869) B1533869
theorem B1022615 : Blo 451781 1022615 := bstep (se 1 (by rfl) ⟨766961, by rfl⟩ : syracuseStep 1022615 = 1533923) B1533923
theorem B1022795 : Blo 451781 1022795 := bstep (se 1 (by rfl) ⟨767096, by rfl⟩ : syracuseStep 1022795 = 1534193) B1534193
theorem B1022849 : Blo 451781 1022849 := bstep (se 2 (by rfl) ⟨383568, by rfl⟩ : syracuseStep 1022849 = 767137) B767137
theorem B3447683 : Blo 451781 3447683 := bstep (se 1 (by rfl) ⟨2585762, by rfl⟩ : syracuseStep 3447683 = 5171525) B5171525
theorem B31562693 : Blo 451781 31562693 := bstep (se 4 (by rfl) ⟨2959002, by rfl⟩ : syracuseStep 31562693 = 5918005) B5918005
theorem B859187 : Blo 451781 859187 := bstep (se 1 (by rfl) ⟨644390, by rfl⟩ : syracuseStep 859187 = 1288781) B1288781
theorem B1023065 : Blo 451781 1023065 := bstep (se 2 (by rfl) ⟨383649, by rfl⟩ : syracuseStep 1023065 = 767299) B767299
theorem B1023155 : Blo 451781 1023155 := bstep (se 1 (by rfl) ⟨767366, by rfl⟩ : syracuseStep 1023155 = 1534733) B1534733
theorem B859339 : Blo 451781 859339 := bstep (se 1 (by rfl) ⟨644504, by rfl⟩ : syracuseStep 859339 = 1289009) B1289009
theorem B1023191 : Blo 451781 1023191 := bstep (se 1 (by rfl) ⟨767393, by rfl⟩ : syracuseStep 1023191 = 1534787) B1534787
theorem B2759953 : Blo 451781 2759953 := bstep (se 2 (by rfl) ⟨1034982, by rfl⟩ : syracuseStep 2759953 = 2069965) B2069965
theorem B1940759 : Blo 451781 1940759 := bstep (se 1 (by rfl) ⟨1455569, by rfl⟩ : syracuseStep 1940759 = 2911139) B2911139
theorem B1023371 : Blo 451781 1023371 := bstep (se 1 (by rfl) ⟨767528, by rfl⟩ : syracuseStep 1023371 = 1535057) B1535057
theorem B1023425 : Blo 451781 1023425 := bstep (se 2 (by rfl) ⟨383784, by rfl⟩ : syracuseStep 1023425 = 767569) B767569
theorem B859673 : Blo 451781 859673 := bstep (se 2 (by rfl) ⟨322377, by rfl⟩ : syracuseStep 859673 = 644755) B644755
theorem B2301533 : Blo 451781 2301533 := bstep (se 3 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 2301533 = 863075) B863075
theorem B1023641 : Blo 451781 1023641 := bstep (se 2 (by rfl) ⟨383865, by rfl⟩ : syracuseStep 1023641 = 767731) B767731
theorem B1089217 : Blo 451781 1089217 := bstep (se 2 (by rfl) ⟨408456, by rfl⟩ : syracuseStep 1089217 = 816913) B816913
theorem B1023731 : Blo 451781 1023731 := bstep (se 1 (by rfl) ⟨767798, by rfl⟩ : syracuseStep 1023731 = 1535597) B1535597
theorem B6233861 : Blo 451781 6233861 := bstep (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) B1168849
theorem B1023767 : Blo 451781 1023767 := bstep (se 1 (by rfl) ⟨767825, by rfl⟩ : syracuseStep 1023767 = 1535651) B1535651
theorem B1089331 : Blo 451781 1089331 := bstep (se 1 (by rfl) ⟨816998, by rfl⟩ : syracuseStep 1089331 = 1633997) B1633997
theorem B466795 : Blo 451781 466795 := bstep (se 1 (by rfl) ⟨350096, by rfl⟩ : syracuseStep 466795 = 700193) B700193
theorem B1023947 : Blo 451781 1023947 := bstep (se 1 (by rfl) ⟨767960, by rfl⟩ : syracuseStep 1023947 = 1535921) B1535921
theorem B1024001 : Blo 451781 1024001 := bstep (se 2 (by rfl) ⟨384000, by rfl⟩ : syracuseStep 1024001 = 768001) B768001
theorem B860311 : Blo 451781 860311 := bstep (se 1 (by rfl) ⟨645233, by rfl⟩ : syracuseStep 860311 = 1290467) B1290467
theorem B1450187 : Blo 451781 1450187 := bstep (se 1 (by rfl) ⟨1087640, by rfl⟩ : syracuseStep 1450187 = 2175281) B2175281
theorem B1024217 : Blo 451781 1024217 := bstep (se 2 (by rfl) ⟨384081, by rfl⟩ : syracuseStep 1024217 = 768163) B768163
theorem B1024307 : Blo 451781 1024307 := bstep (se 1 (by rfl) ⟨768230, by rfl⟩ : syracuseStep 1024307 = 1536461) B1536461
theorem B1450315 : Blo 451781 1450315 := bstep (se 1 (by rfl) ⟨1087736, by rfl⟩ : syracuseStep 1450315 = 2175473) B2175473
theorem B1024343 : Blo 451781 1024343 := bstep (se 1 (by rfl) ⟨768257, by rfl⟩ : syracuseStep 1024343 = 1536515) B1536515
theorem B4432229 : Blo 451781 4432229 := bstep (se 4 (by rfl) ⟨415521, by rfl⟩ : syracuseStep 4432229 = 831043) B831043
theorem B1450391 : Blo 451781 1450391 := bstep (se 1 (by rfl) ⟨1087793, by rfl⟩ : syracuseStep 1450391 = 2175587) B2175587
theorem B1286617 : Blo 451781 1286617 := bstep (se 2 (by rfl) ⟨482481, by rfl⟩ : syracuseStep 1286617 = 964963) B964963
theorem B1024523 : Blo 451781 1024523 := bstep (se 1 (by rfl) ⟨768392, by rfl⟩ : syracuseStep 1024523 = 1536785) B1536785
theorem B1024577 : Blo 451781 1024577 := bstep (se 2 (by rfl) ⟨384216, by rfl⟩ : syracuseStep 1024577 = 768433) B768433
theorem B2794201 : Blo 451781 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B762635 : Blo 451781 762635 := bstep (se 1 (by rfl) ⟨571976, by rfl⟩ : syracuseStep 762635 = 1143953) B1143953
theorem B1024793 : Blo 451781 1024793 := bstep (se 2 (by rfl) ⟨384297, by rfl⟩ : syracuseStep 1024793 = 768595) B768595
theorem B1024883 : Blo 451781 1024883 := bstep (se 1 (by rfl) ⟨768662, by rfl⟩ : syracuseStep 1024883 = 1537325) B1537325
theorem B762763 : Blo 451781 762763 := bstep (se 1 (by rfl) ⟨572072, by rfl⟩ : syracuseStep 762763 = 1144145) B1144145
theorem B1024919 : Blo 451781 1024919 := bstep (se 1 (by rfl) ⟨768689, by rfl⟩ : syracuseStep 1024919 = 1537379) B1537379
theorem B1942451 : Blo 451781 1942451 := bstep (se 1 (by rfl) ⟨1456838, by rfl⟩ : syracuseStep 1942451 = 2913677) B2913677
theorem B861131 : Blo 451781 861131 := bstep (se 1 (by rfl) ⟨645848, by rfl⟩ : syracuseStep 861131 = 1291697) B1291697
theorem B861185 : Blo 451781 861185 := bstep (se 2 (by rfl) ⟨322944, by rfl⟩ : syracuseStep 861185 = 645889) B645889
theorem B762905 : Blo 451781 762905 := bstep (se 2 (by rfl) ⟨286089, by rfl⟩ : syracuseStep 762905 = 572179) B572179
theorem B1025099 : Blo 451781 1025099 := bstep (se 1 (by rfl) ⟨768824, by rfl⟩ : syracuseStep 1025099 = 1537649) B1537649
theorem B1025153 : Blo 451781 1025153 := bstep (se 2 (by rfl) ⟨384432, by rfl⟩ : syracuseStep 1025153 = 768865) B768865
theorem B763033 : Blo 451781 763033 := bstep (se 2 (by rfl) ⟨286137, by rfl⟩ : syracuseStep 763033 = 572275) B572275
theorem B1221911 : Blo 451781 1221911 := bstep (se 1 (by rfl) ⟨916433, by rfl⟩ : syracuseStep 1221911 = 1832867) B1832867
theorem B4662593 : Blo 451781 4662593 := bstep (se 2 (by rfl) ⟨1748472, by rfl⟩ : syracuseStep 4662593 = 3496945) B3496945
theorem B1025369 : Blo 451781 1025369 := bstep (se 2 (by rfl) ⟨384513, by rfl⟩ : syracuseStep 1025369 = 769027) B769027
theorem B1025459 : Blo 451781 1025459 := bstep (se 1 (by rfl) ⟨769094, by rfl⟩ : syracuseStep 1025459 = 1538189) B1538189
theorem B1025495 : Blo 451781 1025495 := bstep (se 1 (by rfl) ⟨769121, by rfl⟩ : syracuseStep 1025495 = 1538243) B1538243
theorem B2303639 : Blo 451781 2303639 := bstep (se 1 (by rfl) ⟨1727729, by rfl⟩ : syracuseStep 2303639 = 3455459) B3455459
theorem B1287859 : Blo 451781 1287859 := bstep (se 1 (by rfl) ⟨965894, by rfl⟩ : syracuseStep 1287859 = 1931789) B1931789
theorem B763607 : Blo 451781 763607 := bstep (se 1 (by rfl) ⟨572705, by rfl⟩ : syracuseStep 763607 = 1145411) B1145411
theorem B763735 : Blo 451781 763735 := bstep (se 1 (by rfl) ⟨572801, by rfl⟩ : syracuseStep 763735 = 1145603) B1145603
theorem B862103 : Blo 451781 862103 := bstep (se 1 (by rfl) ⟨646577, by rfl⟩ : syracuseStep 862103 = 1293155) B1293155
theorem B1091735 : Blo 451781 1091735 := bstep (se 1 (by rfl) ⟨818801, by rfl⟩ : syracuseStep 1091735 = 1637603) B1637603
theorem B1747117 : Blo 451781 1747117 := bstep (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) B655169
theorem B3451085 : Blo 451781 3451085 := bstep (se 3 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 3451085 = 1294157) B1294157
theorem B2337041 : Blo 451781 2337041 := bstep (se 2 (by rfl) ⟨876390, by rfl⟩ : syracuseStep 2337041 = 1752781) B1752781
theorem B862643 : Blo 451781 862643 := bstep (se 1 (by rfl) ⟨646982, by rfl⟩ : syracuseStep 862643 = 1293965) B1293965
theorem B764363 : Blo 451781 764363 := bstep (se 1 (by rfl) ⟨573272, by rfl⟩ : syracuseStep 764363 = 1146545) B1146545
theorem B764491 : Blo 451781 764491 := bstep (se 1 (by rfl) ⟨573368, by rfl⟩ : syracuseStep 764491 = 1146737) B1146737
theorem B3451571 : Blo 451781 3451571 := bstep (se 1 (by rfl) ⟨2588678, by rfl⟩ : syracuseStep 3451571 = 5177357) B5177357
theorem B764633 : Blo 451781 764633 := bstep (se 2 (by rfl) ⟨286737, by rfl⟩ : syracuseStep 764633 = 573475) B573475
theorem B4139851 : Blo 451781 4139851 := bstep (se 1 (by rfl) ⟨3104888, by rfl⟩ : syracuseStep 4139851 = 6209777) B6209777
theorem B764761 : Blo 451781 764761 := bstep (se 2 (by rfl) ⟨286785, by rfl⟩ : syracuseStep 764761 = 573571) B573571
theorem B1846147 : Blo 451781 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B863129 : Blo 451781 863129 := bstep (se 2 (by rfl) ⟨323673, by rfl⟩ : syracuseStep 863129 = 647347) B647347
theorem B8694965 : Blo 451781 8694965 := bstep (se 5 (by rfl) ⟨407576, by rfl⟩ : syracuseStep 8694965 = 815153) B815153
theorem B4664641 : Blo 451781 4664641 := bstep (se 2 (by rfl) ⟨1749240, by rfl⟩ : syracuseStep 4664641 = 3498481) B3498481
theorem B765335 : Blo 451781 765335 := bstep (se 1 (by rfl) ⟨574001, by rfl⟩ : syracuseStep 765335 = 1148003) B1148003
theorem B765463 : Blo 451781 765463 := bstep (se 1 (by rfl) ⟨574097, by rfl⟩ : syracuseStep 765463 = 1148195) B1148195
theorem B1945133 : Blo 451781 1945133 := bstep (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) B729425
theorem B2076353 : Blo 451781 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B2895709 : Blo 451781 2895709 := bstep (se 3 (by rfl) ⟨542945, by rfl⟩ : syracuseStep 2895709 = 1085891) B1085891
theorem B25472945 : Blo 451781 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B3453029 : Blo 451781 3453029 := bstep (se 4 (by rfl) ⟨323721, by rfl⟩ : syracuseStep 3453029 = 647443) B647443
theorem B766091 : Blo 451781 766091 := bstep (se 1 (by rfl) ⟨574568, by rfl⟩ : syracuseStep 766091 = 1149137) B1149137
theorem B766219 : Blo 451781 766219 := bstep (se 1 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 766219 = 1149329) B1149329
theorem B864587 : Blo 451781 864587 := bstep (se 1 (by rfl) ⟨648440, by rfl⟩ : syracuseStep 864587 = 1296881) B1296881
theorem B9318773 : Blo 451781 9318773 := bstep (se 5 (by rfl) ⟨436817, by rfl⟩ : syracuseStep 9318773 = 873635) B873635
theorem B766361 : Blo 451781 766361 := bstep (se 2 (by rfl) ⟨287385, by rfl⟩ : syracuseStep 766361 = 574771) B574771
theorem B1716659 : Blo 451781 1716659 := bstep (se 1 (by rfl) ⟨1287494, by rfl⟩ : syracuseStep 1716659 = 2574989) B2574989
theorem B1716673 : Blo 451781 1716673 := bstep (se 2 (by rfl) ⟨643752, by rfl⟩ : syracuseStep 1716673 = 1287505) B1287505
theorem B864769 : Blo 451781 864769 := bstep (se 2 (by rfl) ⟨324288, by rfl⟩ : syracuseStep 864769 = 648577) B648577
theorem B1290775 : Blo 451781 1290775 := bstep (se 1 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 1290775 = 1936163) B1936163
theorem B766489 : Blo 451781 766489 := bstep (se 2 (by rfl) ⟨287433, by rfl⟩ : syracuseStep 766489 = 574867) B574867
theorem B3551779 : Blo 451781 3551779 := bstep (se 1 (by rfl) ⟨2663834, by rfl⟩ : syracuseStep 3551779 = 5327669) B5327669
theorem B1094195 : Blo 451781 1094195 := bstep (se 1 (by rfl) ⟨820646, by rfl⟩ : syracuseStep 1094195 = 1641293) B1641293
theorem B3453515 : Blo 451781 3453515 := bstep (se 1 (by rfl) ⟨2590136, by rfl⟩ : syracuseStep 3453515 = 5180273) B5180273
theorem B4371245 : Blo 451781 4371245 := bstep (se 3 (by rfl) ⟨819608, by rfl⟩ : syracuseStep 4371245 = 1639217) B1639217
theorem B865217 : Blo 451781 865217 := bstep (se 2 (by rfl) ⟨324456, by rfl⟩ : syracuseStep 865217 = 648913) B648913
theorem B930827 : Blo 451781 930827 := bstep (se 1 (by rfl) ⟨698120, by rfl⟩ : syracuseStep 930827 = 1396241) B1396241
theorem B1553431 : Blo 451781 1553431 := bstep (se 1 (by rfl) ⟨1165073, by rfl⟩ : syracuseStep 1553431 = 2330147) B2330147
theorem B767063 : Blo 451781 767063 := bstep (se 1 (by rfl) ⟨575297, by rfl⟩ : syracuseStep 767063 = 1150595) B1150595
theorem B2307203 : Blo 451781 2307203 := bstep (se 1 (by rfl) ⟨1730402, by rfl⟩ : syracuseStep 2307203 = 3460805) B3460805
theorem B767191 : Blo 451781 767191 := bstep (se 1 (by rfl) ⟨575393, by rfl⟩ : syracuseStep 767191 = 1150787) B1150787
theorem B12432685 : Blo 451781 12432685 := bstep (se 3 (by rfl) ⟨2331128, by rfl⟩ : syracuseStep 12432685 = 4662257) B4662257
theorem B11941507 : Blo 451781 11941507 := bstep (se 1 (by rfl) ⟨8956130, by rfl⟩ : syracuseStep 11941507 = 17912261) B17912261
theorem B1292107 : Blo 451781 1292107 := bstep (se 1 (by rfl) ⟨969080, by rfl⟩ : syracuseStep 1292107 = 1938161) B1938161
theorem B767819 : Blo 451781 767819 := bstep (se 1 (by rfl) ⟨575864, by rfl⟩ : syracuseStep 767819 = 1151729) B1151729
theorem B767947 : Blo 451781 767947 := bstep (se 1 (by rfl) ⟨575960, by rfl⟩ : syracuseStep 767947 = 1151921) B1151921
theorem B768089 : Blo 451781 768089 := bstep (se 2 (by rfl) ⟨288033, by rfl⟩ : syracuseStep 768089 = 576067) B576067
theorem B1292381 : Blo 451781 1292381 := bstep (se 3 (by rfl) ⟨242321, by rfl⟩ : syracuseStep 1292381 = 484643) B484643
theorem B768217 : Blo 451781 768217 := bstep (se 2 (by rfl) ⟨288081, by rfl⟩ : syracuseStep 768217 = 576163) B576163
theorem B1718603 : Blo 451781 1718603 := bstep (se 1 (by rfl) ⟨1288952, by rfl⟩ : syracuseStep 1718603 = 2577905) B2577905
theorem B1718617 : Blo 451781 1718617 := bstep (se 2 (by rfl) ⟨644481, by rfl⟩ : syracuseStep 1718617 = 1288963) B1288963
theorem B571799 : Blo 451781 571799 := bstep (se 1 (by rfl) ⟨428849, by rfl⟩ : syracuseStep 571799 = 857699) B857699
theorem B1292723 : Blo 451781 1292723 := bstep (se 1 (by rfl) ⟨969542, by rfl⟩ : syracuseStep 1292723 = 1939085) B1939085
theorem B768791 : Blo 451781 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B768919 : Blo 451781 768919 := bstep (se 1 (by rfl) ⟨576689, by rfl⟩ : syracuseStep 768919 = 1153379) B1153379
theorem B572503 : Blo 451781 572503 := bstep (se 1 (by rfl) ⟨429377, by rfl⟩ : syracuseStep 572503 = 858755) B858755
theorem B965783 : Blo 451781 965783 := bstep (se 1 (by rfl) ⟨724337, by rfl⟩ : syracuseStep 965783 = 1448675) B1448675
theorem B1227997 : Blo 451781 1227997 := bstep (se 3 (by rfl) ⟨230249, by rfl⟩ : syracuseStep 1227997 = 460499) B460499
theorem B6569201 : Blo 451781 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B1719575 : Blo 451781 1719575 := bstep (se 1 (by rfl) ⟨1289681, by rfl⟩ : syracuseStep 1719575 = 2579363) B2579363
theorem B5913973 : Blo 451781 5913973 := bstep (se 5 (by rfl) ⟨277217, by rfl⟩ : syracuseStep 5913973 = 554435) B554435
theorem B3259921 : Blo 451781 3259921 := bstep (se 2 (by rfl) ⟨1222470, by rfl⟩ : syracuseStep 3259921 = 2444941) B2444941
theorem B966347 : Blo 451781 966347 := bstep (se 1 (by rfl) ⟨724760, by rfl⟩ : syracuseStep 966347 = 1449521) B1449521
theorem B1032257 : Blo 451781 1032257 := bstep (se 2 (by rfl) ⟨387096, by rfl⟩ : syracuseStep 1032257 = 774193) B774193
theorem B966809 : Blo 451781 966809 := bstep (se 2 (by rfl) ⟨362553, by rfl⟩ : syracuseStep 966809 = 725107) B725107
theorem B508279 : Blo 451781 508279 := bstep (se 1 (by rfl) ⟨381209, by rfl⟩ : syracuseStep 508279 = 762419) B762419
theorem B1294795 : Blo 451781 1294795 := bstep (se 1 (by rfl) ⟨971096, by rfl⟩ : syracuseStep 1294795 = 1942193) B1942193
theorem B1720835 : Blo 451781 1720835 := bstep (se 1 (by rfl) ⟨1290626, by rfl⟩ : syracuseStep 1720835 = 2581253) B2581253
theorem B508459 : Blo 451781 508459 := bstep (se 1 (by rfl) ⟨381344, by rfl⟩ : syracuseStep 508459 = 762689) B762689
theorem B3883565 : Blo 451781 3883565 := bstep (se 3 (by rfl) ⟨728168, by rfl⟩ : syracuseStep 3883565 = 1456337) B1456337
theorem B2900555 : Blo 451781 2900555 := bstep (se 1 (by rfl) ⟨2175416, by rfl⟩ : syracuseStep 2900555 = 4350833) B4350833
theorem B508567 : Blo 451781 508567 := bstep (se 1 (by rfl) ⟨381425, by rfl⟩ : syracuseStep 508567 = 762851) B762851
theorem B1393355 : Blo 451781 1393355 := bstep (se 1 (by rfl) ⟨1045016, by rfl⟩ : syracuseStep 1393355 = 2090033) B2090033
theorem B574219 : Blo 451781 574219 := bstep (se 1 (by rfl) ⟨430664, by rfl⟩ : syracuseStep 574219 = 861329) B861329
theorem B508747 : Blo 451781 508747 := bstep (se 1 (by rfl) ⟨381560, by rfl⟩ : syracuseStep 508747 = 763121) B763121
theorem B508855 : Blo 451781 508855 := bstep (se 1 (by rfl) ⟨381641, by rfl⟩ : syracuseStep 508855 = 763283) B763283
theorem B1295297 : Blo 451781 1295297 := bstep (se 2 (by rfl) ⟨485736, by rfl⟩ : syracuseStep 1295297 = 971473) B971473
theorem B1557469 : Blo 451781 1557469 := bstep (se 3 (by rfl) ⟨292025, by rfl⟩ : syracuseStep 1557469 = 584051) B584051
theorem B509035 : Blo 451781 509035 := bstep (se 1 (by rfl) ⟨381776, by rfl⟩ : syracuseStep 509035 = 763553) B763553
theorem B509143 : Blo 451781 509143 := bstep (se 1 (by rfl) ⟨381857, by rfl⟩ : syracuseStep 509143 = 763715) B763715
theorem B1295639 : Blo 451781 1295639 := bstep (se 1 (by rfl) ⟨971729, by rfl⟩ : syracuseStep 1295639 = 1943459) B1943459
theorem B967987 : Blo 451781 967987 := bstep (se 1 (by rfl) ⟨725990, by rfl⟩ : syracuseStep 967987 = 1451981) B1451981
theorem B1525067 : Blo 451781 1525067 := bstep (se 1 (by rfl) ⟨1143800, by rfl⟩ : syracuseStep 1525067 = 2287601) B2287601
theorem B1230169 : Blo 451781 1230169 := bstep (se 2 (by rfl) ⟨461313, by rfl⟩ : syracuseStep 1230169 = 922627) B922627
theorem B509323 : Blo 451781 509323 := bstep (se 1 (by rfl) ⟨381992, by rfl⟩ : syracuseStep 509323 = 763985) B763985
theorem B509431 : Blo 451781 509431 := bstep (se 1 (by rfl) ⟨382073, by rfl⟩ : syracuseStep 509431 = 764147) B764147
theorem B1525337 : Blo 451781 1525337 := bstep (se 2 (by rfl) ⟨572001, by rfl⟩ : syracuseStep 1525337 = 1144003) B1144003
theorem B2442845 : Blo 451781 2442845 := bstep (se 3 (by rfl) ⟨458033, by rfl⟩ : syracuseStep 2442845 = 916067) B916067
theorem B509611 : Blo 451781 509611 := bstep (se 1 (by rfl) ⟨382208, by rfl⟩ : syracuseStep 509611 = 764417) B764417
theorem B575191 : Blo 451781 575191 := bstep (se 1 (by rfl) ⟨431393, by rfl⟩ : syracuseStep 575191 = 862787) B862787
theorem B968449 : Blo 451781 968449 := bstep (se 2 (by rfl) ⟨363168, by rfl⟩ : syracuseStep 968449 = 726337) B726337
theorem B509719 : Blo 451781 509719 := bstep (se 1 (by rfl) ⟨382289, by rfl⟩ : syracuseStep 509719 = 764579) B764579
theorem B3458861 : Blo 451781 3458861 := bstep (se 3 (by rfl) ⟨648536, by rfl⟩ : syracuseStep 3458861 = 1297073) B1297073
theorem B1460119 : Blo 451781 1460119 := bstep (se 1 (by rfl) ⟨1095089, by rfl⟩ : syracuseStep 1460119 = 2190179) B2190179
theorem B509899 : Blo 451781 509899 := bstep (se 1 (by rfl) ⟨382424, by rfl⟩ : syracuseStep 509899 = 764849) B764849
theorem B510007 : Blo 451781 510007 := bstep (se 1 (by rfl) ⟨382505, by rfl⟩ : syracuseStep 510007 = 765011) B765011
theorem B3492017 : Blo 451781 3492017 := bstep (se 2 (by rfl) ⟨1309506, by rfl⟩ : syracuseStep 3492017 = 2619013) B2619013
theorem B510187 : Blo 451781 510187 := bstep (se 1 (by rfl) ⟨382640, by rfl⟩ : syracuseStep 510187 = 765281) B765281
theorem B2214161 : Blo 451781 2214161 := bstep (se 2 (by rfl) ⟨830310, by rfl⟩ : syracuseStep 2214161 = 1660621) B1660621
theorem B1526039 : Blo 451781 1526039 := bstep (se 1 (by rfl) ⟨1144529, by rfl⟩ : syracuseStep 1526039 = 2289059) B2289059
theorem B510295 : Blo 451781 510295 := bstep (se 1 (by rfl) ⟨382721, by rfl⟩ : syracuseStep 510295 = 765443) B765443
theorem B969175 : Blo 451781 969175 := bstep (se 1 (by rfl) ⟨726881, by rfl⟩ : syracuseStep 969175 = 1453763) B1453763
theorem B510475 : Blo 451781 510475 := bstep (se 1 (by rfl) ⟨382856, by rfl⟩ : syracuseStep 510475 = 765713) B765713
theorem B576011 : Blo 451781 576011 := bstep (se 1 (by rfl) ⟨432008, by rfl⟩ : syracuseStep 576011 = 864017) B864017
theorem B510583 : Blo 451781 510583 := bstep (se 1 (by rfl) ⟨382937, by rfl⟩ : syracuseStep 510583 = 765875) B765875
theorem B1231553 : Blo 451781 1231553 := bstep (se 2 (by rfl) ⟨461832, by rfl⟩ : syracuseStep 1231553 = 923665) B923665
theorem B19942129 : Blo 451781 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B3263267 : Blo 451781 3263267 := bstep (se 1 (by rfl) ⟨2447450, by rfl⟩ : syracuseStep 3263267 = 4894901) B4894901
theorem B510763 : Blo 451781 510763 := bstep (se 1 (by rfl) ⟨383072, by rfl⟩ : syracuseStep 510763 = 766145) B766145
theorem B1526579 : Blo 451781 1526579 := bstep (se 1 (by rfl) ⟨1144934, by rfl⟩ : syracuseStep 1526579 = 2289869) B2289869
theorem B510871 : Blo 451781 510871 := bstep (se 1 (by rfl) ⟨383153, by rfl⟩ : syracuseStep 510871 = 766307) B766307
theorem B1526849 : Blo 451781 1526849 := bstep (se 2 (by rfl) ⟨572568, by rfl⟩ : syracuseStep 1526849 = 1145137) B1145137
theorem B511051 : Blo 451781 511051 := bstep (se 1 (by rfl) ⟨383288, by rfl⟩ : syracuseStep 511051 = 766577) B766577
theorem B2903141 : Blo 451781 2903141 := bstep (se 4 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 2903141 = 544339) B544339
theorem B511159 : Blo 451781 511159 := bstep (se 1 (by rfl) ⟨383369, by rfl⟩ : syracuseStep 511159 = 766739) B766739
theorem B576715 : Blo 451781 576715 := bstep (se 1 (by rfl) ⟨432536, by rfl⟩ : syracuseStep 576715 = 865073) B865073
theorem B969995 : Blo 451781 969995 := bstep (se 1 (by rfl) ⟨727496, by rfl⟩ : syracuseStep 969995 = 1454993) B1454993
theorem B1297757 : Blo 451781 1297757 := bstep (se 3 (by rfl) ⟨243329, by rfl⟩ : syracuseStep 1297757 = 486659) B486659
theorem B511339 : Blo 451781 511339 := bstep (se 1 (by rfl) ⟨383504, by rfl⟩ : syracuseStep 511339 = 767009) B767009
theorem B1035659 : Blo 451781 1035659 := bstep (se 1 (by rfl) ⟨776744, by rfl⟩ : syracuseStep 1035659 = 1553489) B1553489
theorem B3886541 : Blo 451781 3886541 := bstep (se 3 (by rfl) ⟨728726, by rfl⟩ : syracuseStep 3886541 = 1457453) B1457453
theorem B511447 : Blo 451781 511447 := bstep (se 1 (by rfl) ⟨383585, by rfl⟩ : syracuseStep 511447 = 767171) B767171
theorem B1723949 : Blo 451781 1723949 := bstep (se 3 (by rfl) ⟨323240, by rfl⟩ : syracuseStep 1723949 = 646481) B646481
theorem B1035841 : Blo 451781 1035841 := bstep (se 2 (by rfl) ⟨388440, by rfl⟩ : syracuseStep 1035841 = 776881) B776881
theorem B1527389 : Blo 451781 1527389 := bstep (se 3 (by rfl) ⟨286385, by rfl⟩ : syracuseStep 1527389 = 572771) B572771
theorem B511627 : Blo 451781 511627 := bstep (se 1 (by rfl) ⟨383720, by rfl⟩ : syracuseStep 511627 = 767441) B767441
theorem B511735 : Blo 451781 511735 := bstep (se 1 (by rfl) ⟨383801, by rfl⟩ : syracuseStep 511735 = 767603) B767603
theorem B511915 : Blo 451781 511915 := bstep (se 1 (by rfl) ⟨383936, by rfl⟩ : syracuseStep 511915 = 767873) B767873
theorem B512023 : Blo 451781 512023 := bstep (se 1 (by rfl) ⟨384017, by rfl⟩ : syracuseStep 512023 = 768035) B768035
theorem B970841 : Blo 451781 970841 := bstep (se 2 (by rfl) ⟨364065, by rfl⟩ : syracuseStep 970841 = 728131) B728131
theorem B512203 : Blo 451781 512203 := bstep (se 1 (by rfl) ⟨384152, by rfl⟩ : syracuseStep 512203 = 768305) B768305
theorem B1724723 : Blo 451781 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B512311 : Blo 451781 512311 := bstep (se 1 (by rfl) ⟨384233, by rfl⟩ : syracuseStep 512311 = 768467) B768467
theorem B6607169 : Blo 451781 6607169 := bstep (se 2 (by rfl) ⟨2477688, by rfl⟩ : syracuseStep 6607169 = 4955377) B4955377
theorem B512491 : Blo 451781 512491 := bstep (se 1 (by rfl) ⟨384368, by rfl⟩ : syracuseStep 512491 = 768737) B768737
theorem B3691025 : Blo 451781 3691025 := bstep (se 2 (by rfl) ⟨1384134, by rfl⟩ : syracuseStep 3691025 = 2768269) B2768269
theorem B512599 : Blo 451781 512599 := bstep (se 1 (by rfl) ⟨384449, by rfl⟩ : syracuseStep 512599 = 768899) B768899
theorem B643673 : Blo 451781 643673 := bstep (se 2 (by rfl) ⟨241377, by rfl⟩ : syracuseStep 643673 = 482755) B482755
theorem B1528523 : Blo 451781 1528523 := bstep (se 1 (by rfl) ⟨1146392, by rfl⟩ : syracuseStep 1528523 = 2292785) B2292785
theorem B971507 : Blo 451781 971507 := bstep (se 1 (by rfl) ⟨728630, by rfl⟩ : syracuseStep 971507 = 1457261) B1457261
theorem B2577197 : Blo 451781 2577197 := bstep (se 3 (by rfl) ⟨483224, by rfl⟩ : syracuseStep 2577197 = 966449) B966449
theorem B2184029 : Blo 451781 2184029 := bstep (se 3 (by rfl) ⟨409505, by rfl⟩ : syracuseStep 2184029 = 819011) B819011
theorem B1528793 : Blo 451781 1528793 := bstep (se 2 (by rfl) ⟨573297, by rfl⟩ : syracuseStep 1528793 = 1146595) B1146595
theorem B4379741 : Blo 451781 4379741 := bstep (se 3 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 4379741 = 1642403) B1642403
theorem B3265687 : Blo 451781 3265687 := bstep (se 1 (by rfl) ⟨2449265, by rfl⟩ : syracuseStep 3265687 = 4898531) B4898531
theorem B644311 : Blo 451781 644311 := bstep (se 1 (by rfl) ⟨483233, by rfl⟩ : syracuseStep 644311 = 966467) B966467
theorem B1529495 : Blo 451781 1529495 := bstep (se 1 (by rfl) ⟨1147121, by rfl⟩ : syracuseStep 1529495 = 2294243) B2294243
theorem B611993 : Blo 451781 611993 := bstep (se 2 (by rfl) ⟨229497, by rfl⟩ : syracuseStep 611993 = 458995) B458995
theorem B972481 : Blo 451781 972481 := bstep (se 2 (by rfl) ⟨364680, by rfl⟩ : syracuseStep 972481 = 729361) B729361
theorem B1726211 : Blo 451781 1726211 := bstep (se 1 (by rfl) ⟨1294658, by rfl⟩ : syracuseStep 1726211 = 2589317) B2589317
theorem B677771 : Blo 451781 677771 := bstep (se 1 (by rfl) ⟨508328, by rfl⟩ : syracuseStep 677771 = 1016657) B1016657
theorem B677783 : Blo 451781 677783 := bstep (se 1 (by rfl) ⟨508337, by rfl⟩ : syracuseStep 677783 = 1016675) B1016675
theorem B972737 : Blo 451781 972737 := bstep (se 2 (by rfl) ⟨364776, by rfl⟩ : syracuseStep 972737 = 729553) B729553
theorem B677849 : Blo 451781 677849 := bstep (se 2 (by rfl) ⟨254193, by rfl⟩ : syracuseStep 677849 = 508387) B508387
theorem B645131 : Blo 451781 645131 := bstep (se 1 (by rfl) ⟨483848, by rfl⟩ : syracuseStep 645131 = 967697) B967697
theorem B1038359 : Blo 451781 1038359 := bstep (se 1 (by rfl) ⟨778769, by rfl⟩ : syracuseStep 1038359 = 1557539) B1557539
theorem B972823 : Blo 451781 972823 := bstep (se 1 (by rfl) ⟨729617, by rfl⟩ : syracuseStep 972823 = 1459235) B1459235
theorem B677963 : Blo 451781 677963 := bstep (se 1 (by rfl) ⟨508472, by rfl⟩ : syracuseStep 677963 = 1016945) B1016945
theorem B677975 : Blo 451781 677975 := bstep (se 1 (by rfl) ⟨508481, by rfl⟩ : syracuseStep 677975 = 1016963) B1016963
theorem B678041 : Blo 451781 678041 := bstep (se 2 (by rfl) ⟨254265, by rfl⟩ : syracuseStep 678041 = 508531) B508531
theorem B1530035 : Blo 451781 1530035 := bstep (se 1 (by rfl) ⟨1147526, by rfl⟩ : syracuseStep 1530035 = 2295053) B2295053
theorem B1726667 : Blo 451781 1726667 := bstep (se 1 (by rfl) ⟨1295000, by rfl⟩ : syracuseStep 1726667 = 2590001) B2590001
theorem B1038539 : Blo 451781 1038539 := bstep (se 1 (by rfl) ⟨778904, by rfl⟩ : syracuseStep 1038539 = 1557809) B1557809
theorem B678155 : Blo 451781 678155 := bstep (se 1 (by rfl) ⟨508616, by rfl⟩ : syracuseStep 678155 = 1017233) B1017233
theorem B678167 : Blo 451781 678167 := bstep (se 1 (by rfl) ⟨508625, by rfl⟩ : syracuseStep 678167 = 1017251) B1017251
theorem B612631 : Blo 451781 612631 := bstep (se 1 (by rfl) ⟨459473, by rfl⟩ : syracuseStep 612631 = 918947) B918947
theorem B1628461 : Blo 451781 1628461 := bstep (se 3 (by rfl) ⟨305336, by rfl⟩ : syracuseStep 1628461 = 610673) B610673
theorem B678233 : Blo 451781 678233 := bstep (se 2 (by rfl) ⟨254337, by rfl⟩ : syracuseStep 678233 = 508675) B508675
theorem B1726865 : Blo 451781 1726865 := bstep (se 2 (by rfl) ⟨647574, by rfl⟩ : syracuseStep 1726865 = 1295149) B1295149
theorem B579991 : Blo 451781 579991 := bstep (se 1 (by rfl) ⟨434993, by rfl⟩ : syracuseStep 579991 = 869987) B869987
theorem B1530305 : Blo 451781 1530305 := bstep (se 2 (by rfl) ⟨573864, by rfl⟩ : syracuseStep 1530305 = 1147729) B1147729
theorem B678347 : Blo 451781 678347 := bstep (se 1 (by rfl) ⟨508760, by rfl⟩ : syracuseStep 678347 = 1017521) B1017521
theorem B678359 : Blo 451781 678359 := bstep (se 1 (by rfl) ⟨508769, by rfl⟩ : syracuseStep 678359 = 1017539) B1017539
theorem B678425 : Blo 451781 678425 := bstep (se 2 (by rfl) ⟨254409, by rfl⟩ : syracuseStep 678425 = 508819) B508819
theorem B1628723 : Blo 451781 1628723 := bstep (se 1 (by rfl) ⟨1221542, by rfl⟩ : syracuseStep 1628723 = 2443085) B2443085
theorem B1038923 : Blo 451781 1038923 := bstep (se 1 (by rfl) ⟨779192, by rfl⟩ : syracuseStep 1038923 = 1558385) B1558385
theorem B678539 : Blo 451781 678539 := bstep (se 1 (by rfl) ⟨508904, by rfl⟩ : syracuseStep 678539 = 1017809) B1017809
theorem B678551 : Blo 451781 678551 := bstep (se 1 (by rfl) ⟨508913, by rfl⟩ : syracuseStep 678551 = 1017827) B1017827
theorem B678617 : Blo 451781 678617 := bstep (se 2 (by rfl) ⟨254481, by rfl⟩ : syracuseStep 678617 = 508963) B508963
theorem B678731 : Blo 451781 678731 := bstep (se 1 (by rfl) ⟨509048, by rfl⟩ : syracuseStep 678731 = 1018097) B1018097
theorem B678743 : Blo 451781 678743 := bstep (se 1 (by rfl) ⟨509057, by rfl⟩ : syracuseStep 678743 = 1018115) B1018115
theorem B678809 : Blo 451781 678809 := bstep (se 2 (by rfl) ⟨254553, by rfl⟩ : syracuseStep 678809 = 509107) B509107
theorem B3267533 : Blo 451781 3267533 := bstep (se 3 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 3267533 = 1225325) B1225325
theorem B1530845 : Blo 451781 1530845 := bstep (se 3 (by rfl) ⟨287033, by rfl⟩ : syracuseStep 1530845 = 574067) B574067
theorem B678923 : Blo 451781 678923 := bstep (se 1 (by rfl) ⟨509192, by rfl⟩ : syracuseStep 678923 = 1018385) B1018385
theorem B678935 : Blo 451781 678935 := bstep (se 1 (by rfl) ⟨509201, by rfl⟩ : syracuseStep 678935 = 1018403) B1018403
theorem B679001 : Blo 451781 679001 := bstep (se 2 (by rfl) ⟨254625, by rfl⟩ : syracuseStep 679001 = 509251) B509251
theorem B1727639 : Blo 451781 1727639 := bstep (se 1 (by rfl) ⟨1295729, by rfl⟩ : syracuseStep 1727639 = 2591459) B2591459
theorem B679115 : Blo 451781 679115 := bstep (se 1 (by rfl) ⟨509336, by rfl⟩ : syracuseStep 679115 = 1018673) B1018673
theorem B679127 : Blo 451781 679127 := bstep (se 1 (by rfl) ⟨509345, by rfl⟩ : syracuseStep 679127 = 1018691) B1018691
theorem B679193 : Blo 451781 679193 := bstep (se 2 (by rfl) ⟨254697, by rfl⟩ : syracuseStep 679193 = 509395) B509395
theorem B1727837 : Blo 451781 1727837 := bstep (se 3 (by rfl) ⟨323969, by rfl⟩ : syracuseStep 1727837 = 647939) B647939
theorem B3267971 : Blo 451781 3267971 := bstep (se 1 (by rfl) ⟨2450978, by rfl⟩ : syracuseStep 3267971 = 4901957) B4901957
theorem B679307 : Blo 451781 679307 := bstep (se 1 (by rfl) ⟨509480, by rfl⟩ : syracuseStep 679307 = 1018961) B1018961
theorem B679319 : Blo 451781 679319 := bstep (se 1 (by rfl) ⟨509489, by rfl⟩ : syracuseStep 679319 = 1018979) B1018979
theorem B4677041 : Blo 451781 4677041 := bstep (se 2 (by rfl) ⟨1753890, by rfl⟩ : syracuseStep 4677041 = 3507781) B3507781
theorem B679385 : Blo 451781 679385 := bstep (se 2 (by rfl) ⟨254769, by rfl⟩ : syracuseStep 679385 = 509539) B509539
theorem B1629719 : Blo 451781 1629719 := bstep (se 1 (by rfl) ⟨1222289, by rfl⟩ : syracuseStep 1629719 = 2444579) B2444579
theorem B679499 : Blo 451781 679499 := bstep (se 1 (by rfl) ⟨509624, by rfl⟩ : syracuseStep 679499 = 1019249) B1019249
theorem B679511 : Blo 451781 679511 := bstep (se 1 (by rfl) ⟨509633, by rfl⟩ : syracuseStep 679511 = 1019267) B1019267
theorem B679577 : Blo 451781 679577 := bstep (se 2 (by rfl) ⟨254841, by rfl⟩ : syracuseStep 679577 = 509683) B509683
theorem B2449075 : Blo 451781 2449075 := bstep (se 1 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 2449075 = 3673613) B3673613
theorem B679691 : Blo 451781 679691 := bstep (se 1 (by rfl) ⟨509768, by rfl⟩ : syracuseStep 679691 = 1019537) B1019537
theorem B679703 : Blo 451781 679703 := bstep (se 1 (by rfl) ⟨509777, by rfl⟩ : syracuseStep 679703 = 1019555) B1019555
theorem B679769 : Blo 451781 679769 := bstep (se 2 (by rfl) ⟨254913, by rfl⟩ : syracuseStep 679769 = 509827) B509827
theorem B679883 : Blo 451781 679883 := bstep (se 1 (by rfl) ⟨509912, by rfl⟩ : syracuseStep 679883 = 1019825) B1019825
theorem B679895 : Blo 451781 679895 := bstep (se 1 (by rfl) ⟨509921, by rfl⟩ : syracuseStep 679895 = 1019843) B1019843
theorem B679961 : Blo 451781 679961 := bstep (se 2 (by rfl) ⟨254985, by rfl⟩ : syracuseStep 679961 = 509971) B509971
theorem B11952197 : Blo 451781 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B1531979 : Blo 451781 1531979 := bstep (se 1 (by rfl) ⟨1148984, by rfl⟩ : syracuseStep 1531979 = 2297969) B2297969
theorem B680075 : Blo 451781 680075 := bstep (se 1 (by rfl) ⟨510056, by rfl⟩ : syracuseStep 680075 = 1020113) B1020113
theorem B680087 : Blo 451781 680087 := bstep (se 1 (by rfl) ⟨510065, by rfl⟩ : syracuseStep 680087 = 1020131) B1020131
theorem B680153 : Blo 451781 680153 := bstep (se 2 (by rfl) ⟨255057, by rfl⟩ : syracuseStep 680153 = 510115) B510115
theorem B483575 : Blo 451781 483575 := bstep (se 1 (by rfl) ⟨362681, by rfl⟩ : syracuseStep 483575 = 725363) B725363
theorem B680267 : Blo 451781 680267 := bstep (se 1 (by rfl) ⟨510200, by rfl⟩ : syracuseStep 680267 = 1020401) B1020401
theorem B680279 : Blo 451781 680279 := bstep (se 1 (by rfl) ⟨510209, by rfl⟩ : syracuseStep 680279 = 1020419) B1020419
theorem B1532249 : Blo 451781 1532249 := bstep (se 2 (by rfl) ⟨574593, by rfl⟩ : syracuseStep 1532249 = 1149187) B1149187
theorem B680345 : Blo 451781 680345 := bstep (se 2 (by rfl) ⟨255129, by rfl⟩ : syracuseStep 680345 = 510259) B510259
theorem B680459 : Blo 451781 680459 := bstep (se 1 (by rfl) ⟨510344, by rfl⟩ : syracuseStep 680459 = 1020689) B1020689
theorem B680471 : Blo 451781 680471 := bstep (se 1 (by rfl) ⟨510353, by rfl⟩ : syracuseStep 680471 = 1020707) B1020707
theorem B680537 : Blo 451781 680537 := bstep (se 2 (by rfl) ⟨255201, by rfl⟩ : syracuseStep 680537 = 510403) B510403
theorem B680651 : Blo 451781 680651 := bstep (se 1 (by rfl) ⟨510488, by rfl⟩ : syracuseStep 680651 = 1020977) B1020977
theorem B680663 : Blo 451781 680663 := bstep (se 1 (by rfl) ⟨510497, by rfl⟩ : syracuseStep 680663 = 1020995) B1020995
theorem B2974481 : Blo 451781 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B680729 : Blo 451781 680729 := bstep (se 2 (by rfl) ⟨255273, by rfl⟩ : syracuseStep 680729 = 510547) B510547
theorem B680843 : Blo 451781 680843 := bstep (se 1 (by rfl) ⟨510632, by rfl⟩ : syracuseStep 680843 = 1021265) B1021265
theorem B680855 : Blo 451781 680855 := bstep (se 1 (by rfl) ⟨510641, by rfl⟩ : syracuseStep 680855 = 1021283) B1021283
theorem B484267 : Blo 451781 484267 := bstep (se 1 (by rfl) ⟨363200, by rfl⟩ : syracuseStep 484267 = 726401) B726401
theorem B680921 : Blo 451781 680921 := bstep (se 2 (by rfl) ⟨255345, by rfl⟩ : syracuseStep 680921 = 510691) B510691
theorem B1532951 : Blo 451781 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B681035 : Blo 451781 681035 := bstep (se 1 (by rfl) ⟨510776, by rfl⟩ : syracuseStep 681035 = 1021553) B1021553
theorem B681047 : Blo 451781 681047 := bstep (se 1 (by rfl) ⟨510785, by rfl⟩ : syracuseStep 681047 = 1021571) B1021571
theorem B681113 : Blo 451781 681113 := bstep (se 2 (by rfl) ⟨255417, by rfl⟩ : syracuseStep 681113 = 510835) B510835
theorem B451787 : Blo 451781 451787 := bstep (se 1 (by rfl) ⟨338840, by rfl⟩ : syracuseStep 451787 = 677681) B677681
theorem B451799 : Blo 451781 451799 := bstep (se 1 (by rfl) ⟨338849, by rfl⟩ : syracuseStep 451799 = 677699) B677699
theorem B451819 : Blo 451781 451819 := bstep (se 1 (by rfl) ⟨338864, by rfl⟩ : syracuseStep 451819 = 677729) B677729
theorem B451831 : Blo 451781 451831 := bstep (se 1 (by rfl) ⟨338873, by rfl⟩ : syracuseStep 451831 = 677747) B677747
theorem B1729795 : Blo 451781 1729795 := bstep (se 1 (by rfl) ⟨1297346, by rfl⟩ : syracuseStep 1729795 = 2594693) B2594693
theorem B451851 : Blo 451781 451851 := bstep (se 1 (by rfl) ⟨338888, by rfl⟩ : syracuseStep 451851 = 677777) B677777
theorem B681227 : Blo 451781 681227 := bstep (se 1 (by rfl) ⟨510920, by rfl⟩ : syracuseStep 681227 = 1021841) B1021841
theorem B451863 : Blo 451781 451863 := bstep (se 1 (by rfl) ⟨338897, by rfl⟩ : syracuseStep 451863 = 677795) B677795
theorem B681239 : Blo 451781 681239 := bstep (se 1 (by rfl) ⟨510929, by rfl⟩ : syracuseStep 681239 = 1021859) B1021859
theorem B451883 : Blo 451781 451883 := bstep (se 1 (by rfl) ⟨338912, by rfl⟩ : syracuseStep 451883 = 677825) B677825
theorem B451895 : Blo 451781 451895 := bstep (se 1 (by rfl) ⟨338921, by rfl⟩ : syracuseStep 451895 = 677843) B677843
theorem B451915 : Blo 451781 451915 := bstep (se 1 (by rfl) ⟨338936, by rfl⟩ : syracuseStep 451915 = 677873) B677873
theorem B451927 : Blo 451781 451927 := bstep (se 1 (by rfl) ⟨338945, by rfl⟩ : syracuseStep 451927 = 677891) B677891
theorem B681305 : Blo 451781 681305 := bstep (se 2 (by rfl) ⟨255489, by rfl⟩ : syracuseStep 681305 = 510979) B510979
theorem B451947 : Blo 451781 451947 := bstep (se 1 (by rfl) ⟨338960, by rfl⟩ : syracuseStep 451947 = 677921) B677921
theorem B451959 : Blo 451781 451959 := bstep (se 1 (by rfl) ⟨338969, by rfl⟩ : syracuseStep 451959 = 677939) B677939
theorem B451979 : Blo 451781 451979 := bstep (se 1 (by rfl) ⟨338984, by rfl⟩ : syracuseStep 451979 = 677969) B677969
theorem B451991 : Blo 451781 451991 := bstep (se 1 (by rfl) ⟨338993, by rfl⟩ : syracuseStep 451991 = 677987) B677987
theorem B452011 : Blo 451781 452011 := bstep (se 1 (by rfl) ⟨339008, by rfl⟩ : syracuseStep 452011 = 678017) B678017
theorem B452023 : Blo 451781 452023 := bstep (se 1 (by rfl) ⟨339017, by rfl⟩ : syracuseStep 452023 = 678035) B678035
theorem B452043 : Blo 451781 452043 := bstep (se 1 (by rfl) ⟨339032, by rfl⟩ : syracuseStep 452043 = 678065) B678065
theorem B681419 : Blo 451781 681419 := bstep (se 1 (by rfl) ⟨511064, by rfl⟩ : syracuseStep 681419 = 1022129) B1022129
theorem B452055 : Blo 451781 452055 := bstep (se 1 (by rfl) ⟨339041, by rfl⟩ : syracuseStep 452055 = 678083) B678083
theorem B681431 : Blo 451781 681431 := bstep (se 1 (by rfl) ⟨511073, by rfl⟩ : syracuseStep 681431 = 1022147) B1022147
theorem B452075 : Blo 451781 452075 := bstep (se 1 (by rfl) ⟨339056, by rfl⟩ : syracuseStep 452075 = 678113) B678113
theorem B452087 : Blo 451781 452087 := bstep (se 1 (by rfl) ⟨339065, by rfl⟩ : syracuseStep 452087 = 678131) B678131
theorem B452107 : Blo 451781 452107 := bstep (se 1 (by rfl) ⟨339080, by rfl⟩ : syracuseStep 452107 = 678161) B678161
theorem B452119 : Blo 451781 452119 := bstep (se 1 (by rfl) ⟨339089, by rfl⟩ : syracuseStep 452119 = 678179) B678179
theorem B681497 : Blo 451781 681497 := bstep (se 2 (by rfl) ⟨255561, by rfl⟩ : syracuseStep 681497 = 511123) B511123
theorem B452139 : Blo 451781 452139 := bstep (se 1 (by rfl) ⟨339104, by rfl⟩ : syracuseStep 452139 = 678209) B678209
theorem B1533491 : Blo 451781 1533491 := bstep (se 1 (by rfl) ⟨1150118, by rfl⟩ : syracuseStep 1533491 = 2300237) B2300237
theorem B1730099 : Blo 451781 1730099 := bstep (se 1 (by rfl) ⟨1297574, by rfl⟩ : syracuseStep 1730099 = 2595149) B2595149
theorem B452151 : Blo 451781 452151 := bstep (se 1 (by rfl) ⟨339113, by rfl⟩ : syracuseStep 452151 = 678227) B678227
theorem B452171 : Blo 451781 452171 := bstep (se 1 (by rfl) ⟨339128, by rfl⟩ : syracuseStep 452171 = 678257) B678257
theorem B452183 : Blo 451781 452183 := bstep (se 1 (by rfl) ⟨339137, by rfl⟩ : syracuseStep 452183 = 678275) B678275
theorem B452203 : Blo 451781 452203 := bstep (se 1 (by rfl) ⟨339152, by rfl⟩ : syracuseStep 452203 = 678305) B678305
theorem B452215 : Blo 451781 452215 := bstep (se 1 (by rfl) ⟨339161, by rfl⟩ : syracuseStep 452215 = 678323) B678323
theorem B452235 : Blo 451781 452235 := bstep (se 1 (by rfl) ⟨339176, by rfl⟩ : syracuseStep 452235 = 678353) B678353
theorem B681611 : Blo 451781 681611 := bstep (se 1 (by rfl) ⟨511208, by rfl⟩ : syracuseStep 681611 = 1022417) B1022417
theorem B452247 : Blo 451781 452247 := bstep (se 1 (by rfl) ⟨339185, by rfl⟩ : syracuseStep 452247 = 678371) B678371
theorem B681623 : Blo 451781 681623 := bstep (se 1 (by rfl) ⟨511217, by rfl⟩ : syracuseStep 681623 = 1022435) B1022435
theorem B452267 : Blo 451781 452267 := bstep (se 1 (by rfl) ⟨339200, by rfl⟩ : syracuseStep 452267 = 678401) B678401
theorem B452279 : Blo 451781 452279 := bstep (se 1 (by rfl) ⟨339209, by rfl⟩ : syracuseStep 452279 = 678419) B678419
theorem B452299 : Blo 451781 452299 := bstep (se 1 (by rfl) ⟨339224, by rfl⟩ : syracuseStep 452299 = 678449) B678449
theorem B452311 : Blo 451781 452311 := bstep (se 1 (by rfl) ⟨339233, by rfl⟩ : syracuseStep 452311 = 678467) B678467
theorem B681689 : Blo 451781 681689 := bstep (se 2 (by rfl) ⟨255633, by rfl⟩ : syracuseStep 681689 = 511267) B511267
theorem B452331 : Blo 451781 452331 := bstep (se 1 (by rfl) ⟨339248, by rfl⟩ : syracuseStep 452331 = 678497) B678497
theorem B14739185 : Blo 451781 14739185 := bstep (se 2 (by rfl) ⟨5527194, by rfl⟩ : syracuseStep 14739185 = 11054389) B11054389
theorem B452343 : Blo 451781 452343 := bstep (se 1 (by rfl) ⟨339257, by rfl⟩ : syracuseStep 452343 = 678515) B678515
theorem B452363 : Blo 451781 452363 := bstep (se 1 (by rfl) ⟨339272, by rfl⟩ : syracuseStep 452363 = 678545) B678545
theorem B452375 : Blo 451781 452375 := bstep (se 1 (by rfl) ⟨339281, by rfl⟩ : syracuseStep 452375 = 678563) B678563
theorem B452395 : Blo 451781 452395 := bstep (se 1 (by rfl) ⟨339296, by rfl⟩ : syracuseStep 452395 = 678593) B678593
theorem B452407 : Blo 451781 452407 := bstep (se 1 (by rfl) ⟨339305, by rfl⟩ : syracuseStep 452407 = 678611) B678611
theorem B1533761 : Blo 451781 1533761 := bstep (se 2 (by rfl) ⟨575160, by rfl⟩ : syracuseStep 1533761 = 1150321) B1150321
theorem B452427 : Blo 451781 452427 := bstep (se 1 (by rfl) ⟨339320, by rfl⟩ : syracuseStep 452427 = 678641) B678641
theorem B681803 : Blo 451781 681803 := bstep (se 1 (by rfl) ⟨511352, by rfl⟩ : syracuseStep 681803 = 1022705) B1022705
theorem B452439 : Blo 451781 452439 := bstep (se 1 (by rfl) ⟨339329, by rfl⟩ : syracuseStep 452439 = 678659) B678659
theorem B681815 : Blo 451781 681815 := bstep (se 1 (by rfl) ⟨511361, by rfl⟩ : syracuseStep 681815 = 1022723) B1022723
theorem B452459 : Blo 451781 452459 := bstep (se 1 (by rfl) ⟨339344, by rfl⟩ : syracuseStep 452459 = 678689) B678689
theorem B452471 : Blo 451781 452471 := bstep (se 1 (by rfl) ⟨339353, by rfl⟩ : syracuseStep 452471 = 678707) B678707
theorem B452491 : Blo 451781 452491 := bstep (se 1 (by rfl) ⟨339368, by rfl⟩ : syracuseStep 452491 = 678737) B678737
theorem B452503 : Blo 451781 452503 := bstep (se 1 (by rfl) ⟨339377, by rfl⟩ : syracuseStep 452503 = 678755) B678755
theorem B681881 : Blo 451781 681881 := bstep (se 2 (by rfl) ⟨255705, by rfl⟩ : syracuseStep 681881 = 511411) B511411
theorem B452523 : Blo 451781 452523 := bstep (se 1 (by rfl) ⟨339392, by rfl⟩ : syracuseStep 452523 = 678785) B678785
theorem B452535 : Blo 451781 452535 := bstep (se 1 (by rfl) ⟨339401, by rfl⟩ : syracuseStep 452535 = 678803) B678803
theorem B452555 : Blo 451781 452555 := bstep (se 1 (by rfl) ⟨339416, by rfl⟩ : syracuseStep 452555 = 678833) B678833
theorem B452567 : Blo 451781 452567 := bstep (se 1 (by rfl) ⟨339425, by rfl⟩ : syracuseStep 452567 = 678851) B678851
theorem B452587 : Blo 451781 452587 := bstep (se 1 (by rfl) ⟨339440, by rfl⟩ : syracuseStep 452587 = 678881) B678881
theorem B452599 : Blo 451781 452599 := bstep (se 1 (by rfl) ⟨339449, by rfl⟩ : syracuseStep 452599 = 678899) B678899
theorem B452619 : Blo 451781 452619 := bstep (se 1 (by rfl) ⟨339464, by rfl⟩ : syracuseStep 452619 = 678929) B678929
theorem B681995 : Blo 451781 681995 := bstep (se 1 (by rfl) ⟨511496, by rfl⟩ : syracuseStep 681995 = 1022993) B1022993
theorem B452631 : Blo 451781 452631 := bstep (se 1 (by rfl) ⟨339473, by rfl⟩ : syracuseStep 452631 = 678947) B678947
theorem B682007 : Blo 451781 682007 := bstep (se 1 (by rfl) ⟨511505, by rfl⟩ : syracuseStep 682007 = 1023011) B1023011
theorem B452651 : Blo 451781 452651 := bstep (se 1 (by rfl) ⟨339488, by rfl⟩ : syracuseStep 452651 = 678977) B678977
theorem B452663 : Blo 451781 452663 := bstep (se 1 (by rfl) ⟨339497, by rfl⟩ : syracuseStep 452663 = 678995) B678995
theorem B3434561 : Blo 451781 3434561 := bstep (se 2 (by rfl) ⟨1287960, by rfl⟩ : syracuseStep 3434561 = 2575921) B2575921
theorem B452683 : Blo 451781 452683 := bstep (se 1 (by rfl) ⟨339512, by rfl⟩ : syracuseStep 452683 = 679025) B679025
theorem B452695 : Blo 451781 452695 := bstep (se 1 (by rfl) ⟨339521, by rfl⟩ : syracuseStep 452695 = 679043) B679043
theorem B682073 : Blo 451781 682073 := bstep (se 2 (by rfl) ⟨255777, by rfl⟩ : syracuseStep 682073 = 511555) B511555
theorem B1402973 : Blo 451781 1402973 := bstep (se 3 (by rfl) ⟨263057, by rfl⟩ : syracuseStep 1402973 = 526115) B526115
theorem B452715 : Blo 451781 452715 := bstep (se 1 (by rfl) ⟨339536, by rfl⟩ : syracuseStep 452715 = 679073) B679073
theorem B452727 : Blo 451781 452727 := bstep (se 1 (by rfl) ⟨339545, by rfl⟩ : syracuseStep 452727 = 679091) B679091
theorem B452747 : Blo 451781 452747 := bstep (se 1 (by rfl) ⟨339560, by rfl⟩ : syracuseStep 452747 = 679121) B679121
theorem B452759 : Blo 451781 452759 := bstep (se 1 (by rfl) ⟨339569, by rfl⟩ : syracuseStep 452759 = 679139) B679139
theorem B452779 : Blo 451781 452779 := bstep (se 1 (by rfl) ⟨339584, by rfl⟩ : syracuseStep 452779 = 679169) B679169
theorem B452791 : Blo 451781 452791 := bstep (se 1 (by rfl) ⟨339593, by rfl⟩ : syracuseStep 452791 = 679187) B679187
theorem B452811 : Blo 451781 452811 := bstep (se 1 (by rfl) ⟨339608, by rfl⟩ : syracuseStep 452811 = 679217) B679217
theorem B682187 : Blo 451781 682187 := bstep (se 1 (by rfl) ⟨511640, by rfl⟩ : syracuseStep 682187 = 1023281) B1023281
theorem B452823 : Blo 451781 452823 := bstep (se 1 (by rfl) ⟨339617, by rfl⟩ : syracuseStep 452823 = 679235) B679235
theorem B682199 : Blo 451781 682199 := bstep (se 1 (by rfl) ⟨511649, by rfl⟩ : syracuseStep 682199 = 1023299) B1023299
theorem B452843 : Blo 451781 452843 := bstep (se 1 (by rfl) ⟨339632, by rfl⟩ : syracuseStep 452843 = 679265) B679265
theorem B452855 : Blo 451781 452855 := bstep (se 1 (by rfl) ⟨339641, by rfl⟩ : syracuseStep 452855 = 679283) B679283
theorem B452875 : Blo 451781 452875 := bstep (se 1 (by rfl) ⟨339656, by rfl⟩ : syracuseStep 452875 = 679313) B679313
theorem B452887 : Blo 451781 452887 := bstep (se 1 (by rfl) ⟨339665, by rfl⟩ : syracuseStep 452887 = 679331) B679331
theorem B682265 : Blo 451781 682265 := bstep (se 2 (by rfl) ⟨255849, by rfl⟩ : syracuseStep 682265 = 511699) B511699
theorem B452907 : Blo 451781 452907 := bstep (se 1 (by rfl) ⟨339680, by rfl⟩ : syracuseStep 452907 = 679361) B679361
theorem B452919 : Blo 451781 452919 := bstep (se 1 (by rfl) ⟨339689, by rfl⟩ : syracuseStep 452919 = 679379) B679379
theorem B452939 : Blo 451781 452939 := bstep (se 1 (by rfl) ⟨339704, by rfl⟩ : syracuseStep 452939 = 679409) B679409
theorem B452951 : Blo 451781 452951 := bstep (se 1 (by rfl) ⟨339713, by rfl⟩ : syracuseStep 452951 = 679427) B679427
theorem B485719 : Blo 451781 485719 := bstep (se 1 (by rfl) ⟨364289, by rfl⟩ : syracuseStep 485719 = 728579) B728579
theorem B1534301 : Blo 451781 1534301 := bstep (se 3 (by rfl) ⟨287681, by rfl⟩ : syracuseStep 1534301 = 575363) B575363
theorem B452971 : Blo 451781 452971 := bstep (se 1 (by rfl) ⟨339728, by rfl⟩ : syracuseStep 452971 = 679457) B679457
theorem B452983 : Blo 451781 452983 := bstep (se 1 (by rfl) ⟨339737, by rfl⟩ : syracuseStep 452983 = 679475) B679475
theorem B453003 : Blo 451781 453003 := bstep (se 1 (by rfl) ⟨339752, by rfl⟩ : syracuseStep 453003 = 679505) B679505
theorem B682379 : Blo 451781 682379 := bstep (se 1 (by rfl) ⟨511784, by rfl⟩ : syracuseStep 682379 = 1023569) B1023569
theorem B453015 : Blo 451781 453015 := bstep (se 1 (by rfl) ⟨339761, by rfl⟩ : syracuseStep 453015 = 679523) B679523
theorem B682391 : Blo 451781 682391 := bstep (se 1 (by rfl) ⟨511793, by rfl⟩ : syracuseStep 682391 = 1023587) B1023587
theorem B453035 : Blo 451781 453035 := bstep (se 1 (by rfl) ⟨339776, by rfl⟩ : syracuseStep 453035 = 679553) B679553
theorem B453047 : Blo 451781 453047 := bstep (se 1 (by rfl) ⟨339785, by rfl⟩ : syracuseStep 453047 = 679571) B679571
theorem B453067 : Blo 451781 453067 := bstep (se 1 (by rfl) ⟨339800, by rfl⟩ : syracuseStep 453067 = 679601) B679601
theorem B453079 : Blo 451781 453079 := bstep (se 1 (by rfl) ⟨339809, by rfl⟩ : syracuseStep 453079 = 679619) B679619
theorem B682457 : Blo 451781 682457 := bstep (se 2 (by rfl) ⟨255921, by rfl⟩ : syracuseStep 682457 = 511843) B511843
theorem B453099 : Blo 451781 453099 := bstep (se 1 (by rfl) ⟨339824, by rfl⟩ : syracuseStep 453099 = 679649) B679649
theorem B453111 : Blo 451781 453111 := bstep (se 1 (by rfl) ⟨339833, by rfl⟩ : syracuseStep 453111 = 679667) B679667
theorem B453131 : Blo 451781 453131 := bstep (se 1 (by rfl) ⟨339848, by rfl⟩ : syracuseStep 453131 = 679697) B679697
theorem B453143 : Blo 451781 453143 := bstep (se 1 (by rfl) ⟨339857, by rfl⟩ : syracuseStep 453143 = 679715) B679715
theorem B453163 : Blo 451781 453163 := bstep (se 1 (by rfl) ⟨339872, by rfl⟩ : syracuseStep 453163 = 679745) B679745
theorem B453175 : Blo 451781 453175 := bstep (se 1 (by rfl) ⟨339881, by rfl⟩ : syracuseStep 453175 = 679763) B679763
theorem B453195 : Blo 451781 453195 := bstep (se 1 (by rfl) ⟨339896, by rfl⟩ : syracuseStep 453195 = 679793) B679793
theorem B682571 : Blo 451781 682571 := bstep (se 1 (by rfl) ⟨511928, by rfl⟩ : syracuseStep 682571 = 1023857) B1023857
theorem B453207 : Blo 451781 453207 := bstep (se 1 (by rfl) ⟨339905, by rfl⟩ : syracuseStep 453207 = 679811) B679811
theorem B682583 : Blo 451781 682583 := bstep (se 1 (by rfl) ⟨511937, by rfl⟩ : syracuseStep 682583 = 1023875) B1023875
theorem B453227 : Blo 451781 453227 := bstep (se 1 (by rfl) ⟨339920, by rfl⟩ : syracuseStep 453227 = 679841) B679841
theorem B453239 : Blo 451781 453239 := bstep (se 1 (by rfl) ⟨339929, by rfl⟩ : syracuseStep 453239 = 679859) B679859
theorem B453259 : Blo 451781 453259 := bstep (se 1 (by rfl) ⟨339944, by rfl⟩ : syracuseStep 453259 = 679889) B679889
theorem B453271 : Blo 451781 453271 := bstep (se 1 (by rfl) ⟨339953, by rfl⟩ : syracuseStep 453271 = 679907) B679907
theorem B682649 : Blo 451781 682649 := bstep (se 2 (by rfl) ⟨255993, by rfl⟩ : syracuseStep 682649 = 511987) B511987
theorem B453291 : Blo 451781 453291 := bstep (se 1 (by rfl) ⟨339968, by rfl⟩ : syracuseStep 453291 = 679937) B679937
theorem B453303 : Blo 451781 453303 := bstep (se 1 (by rfl) ⟨339977, by rfl⟩ : syracuseStep 453303 = 679955) B679955
theorem B453323 : Blo 451781 453323 := bstep (se 1 (by rfl) ⟨339992, by rfl⟩ : syracuseStep 453323 = 679985) B679985
theorem B486091 : Blo 451781 486091 := bstep (se 1 (by rfl) ⟨364568, by rfl⟩ : syracuseStep 486091 = 729137) B729137
theorem B453335 : Blo 451781 453335 := bstep (se 1 (by rfl) ⟨340001, by rfl⟩ : syracuseStep 453335 = 680003) B680003
theorem B453355 : Blo 451781 453355 := bstep (se 1 (by rfl) ⟨340016, by rfl⟩ : syracuseStep 453355 = 680033) B680033
theorem B453367 : Blo 451781 453367 := bstep (se 1 (by rfl) ⟨340025, by rfl⟩ : syracuseStep 453367 = 680051) B680051
theorem B453387 : Blo 451781 453387 := bstep (se 1 (by rfl) ⟨340040, by rfl⟩ : syracuseStep 453387 = 680081) B680081
theorem B682763 : Blo 451781 682763 := bstep (se 1 (by rfl) ⟨512072, by rfl⟩ : syracuseStep 682763 = 1024145) B1024145
theorem B453399 : Blo 451781 453399 := bstep (se 1 (by rfl) ⟨340049, by rfl⟩ : syracuseStep 453399 = 680099) B680099
theorem B682775 : Blo 451781 682775 := bstep (se 1 (by rfl) ⟨512081, by rfl⟩ : syracuseStep 682775 = 1024163) B1024163
theorem B453419 : Blo 451781 453419 := bstep (se 1 (by rfl) ⟨340064, by rfl⟩ : syracuseStep 453419 = 680129) B680129
theorem B453431 : Blo 451781 453431 := bstep (se 1 (by rfl) ⟨340073, by rfl⟩ : syracuseStep 453431 = 680147) B680147
theorem B453451 : Blo 451781 453451 := bstep (se 1 (by rfl) ⟨340088, by rfl⟩ : syracuseStep 453451 = 680177) B680177
theorem B453463 : Blo 451781 453463 := bstep (se 1 (by rfl) ⟨340097, by rfl⟩ : syracuseStep 453463 = 680195) B680195
theorem B682841 : Blo 451781 682841 := bstep (se 2 (by rfl) ⟨256065, by rfl⟩ : syracuseStep 682841 = 512131) B512131
theorem B453483 : Blo 451781 453483 := bstep (se 1 (by rfl) ⟨340112, by rfl⟩ : syracuseStep 453483 = 680225) B680225
theorem B453495 : Blo 451781 453495 := bstep (se 1 (by rfl) ⟨340121, by rfl⟩ : syracuseStep 453495 = 680243) B680243
theorem B453515 : Blo 451781 453515 := bstep (se 1 (by rfl) ⟨340136, by rfl⟩ : syracuseStep 453515 = 680273) B680273
theorem B453527 : Blo 451781 453527 := bstep (se 1 (by rfl) ⟨340145, by rfl⟩ : syracuseStep 453527 = 680291) B680291
theorem B453547 : Blo 451781 453547 := bstep (se 1 (by rfl) ⟨340160, by rfl⟩ : syracuseStep 453547 = 680321) B680321
theorem B453559 : Blo 451781 453559 := bstep (se 1 (by rfl) ⟨340169, by rfl⟩ : syracuseStep 453559 = 680339) B680339
theorem B453579 : Blo 451781 453579 := bstep (se 1 (by rfl) ⟨340184, by rfl⟩ : syracuseStep 453579 = 680369) B680369
theorem B682955 : Blo 451781 682955 := bstep (se 1 (by rfl) ⟨512216, by rfl⟩ : syracuseStep 682955 = 1024433) B1024433
theorem B453591 : Blo 451781 453591 := bstep (se 1 (by rfl) ⟨340193, by rfl⟩ : syracuseStep 453591 = 680387) B680387
theorem B682967 : Blo 451781 682967 := bstep (se 1 (by rfl) ⟨512225, by rfl⟩ : syracuseStep 682967 = 1024451) B1024451
theorem B453611 : Blo 451781 453611 := bstep (se 1 (by rfl) ⟨340208, by rfl⟩ : syracuseStep 453611 = 680417) B680417
theorem B453623 : Blo 451781 453623 := bstep (se 1 (by rfl) ⟨340217, by rfl⟩ : syracuseStep 453623 = 680435) B680435
theorem B453643 : Blo 451781 453643 := bstep (se 1 (by rfl) ⟨340232, by rfl⟩ : syracuseStep 453643 = 680465) B680465
theorem B453655 : Blo 451781 453655 := bstep (se 1 (by rfl) ⟨340241, by rfl⟩ : syracuseStep 453655 = 680483) B680483
theorem B683033 : Blo 451781 683033 := bstep (se 2 (by rfl) ⟨256137, by rfl⟩ : syracuseStep 683033 = 512275) B512275
theorem B453675 : Blo 451781 453675 := bstep (se 1 (by rfl) ⟨340256, by rfl⟩ : syracuseStep 453675 = 680513) B680513
theorem B453687 : Blo 451781 453687 := bstep (se 1 (by rfl) ⟨340265, by rfl⟩ : syracuseStep 453687 = 680531) B680531
theorem B453707 : Blo 451781 453707 := bstep (se 1 (by rfl) ⟨340280, by rfl⟩ : syracuseStep 453707 = 680561) B680561
theorem B453719 : Blo 451781 453719 := bstep (se 1 (by rfl) ⟨340289, by rfl⟩ : syracuseStep 453719 = 680579) B680579
theorem B453739 : Blo 451781 453739 := bstep (se 1 (by rfl) ⟨340304, by rfl⟩ : syracuseStep 453739 = 680609) B680609
theorem B453751 : Blo 451781 453751 := bstep (se 1 (by rfl) ⟨340313, by rfl⟩ : syracuseStep 453751 = 680627) B680627
theorem B453771 : Blo 451781 453771 := bstep (se 1 (by rfl) ⟨340328, by rfl⟩ : syracuseStep 453771 = 680657) B680657
theorem B683147 : Blo 451781 683147 := bstep (se 1 (by rfl) ⟨512360, by rfl⟩ : syracuseStep 683147 = 1024721) B1024721
theorem B453783 : Blo 451781 453783 := bstep (se 1 (by rfl) ⟨340337, by rfl⟩ : syracuseStep 453783 = 680675) B680675
theorem B683159 : Blo 451781 683159 := bstep (se 1 (by rfl) ⟨512369, by rfl⟩ : syracuseStep 683159 = 1024739) B1024739
theorem B453803 : Blo 451781 453803 := bstep (se 1 (by rfl) ⟨340352, by rfl⟩ : syracuseStep 453803 = 680705) B680705
theorem B453815 : Blo 451781 453815 := bstep (se 1 (by rfl) ⟨340361, by rfl⟩ : syracuseStep 453815 = 680723) B680723
theorem B453835 : Blo 451781 453835 := bstep (se 1 (by rfl) ⟨340376, by rfl⟩ : syracuseStep 453835 = 680753) B680753
theorem B453847 : Blo 451781 453847 := bstep (se 1 (by rfl) ⟨340385, by rfl⟩ : syracuseStep 453847 = 680771) B680771
theorem B683225 : Blo 451781 683225 := bstep (se 2 (by rfl) ⟨256209, by rfl⟩ : syracuseStep 683225 = 512419) B512419
theorem B453867 : Blo 451781 453867 := bstep (se 1 (by rfl) ⟨340400, by rfl⟩ : syracuseStep 453867 = 680801) B680801
theorem B453879 : Blo 451781 453879 := bstep (se 1 (by rfl) ⟨340409, by rfl⟩ : syracuseStep 453879 = 680819) B680819
theorem B453899 : Blo 451781 453899 := bstep (se 1 (by rfl) ⟨340424, by rfl⟩ : syracuseStep 453899 = 680849) B680849
theorem B453911 : Blo 451781 453911 := bstep (se 1 (by rfl) ⟨340433, by rfl⟩ : syracuseStep 453911 = 680867) B680867
theorem B453931 : Blo 451781 453931 := bstep (se 1 (by rfl) ⟨340448, by rfl⟩ : syracuseStep 453931 = 680897) B680897
theorem B453943 : Blo 451781 453943 := bstep (se 1 (by rfl) ⟨340457, by rfl⟩ : syracuseStep 453943 = 680915) B680915
theorem B453963 : Blo 451781 453963 := bstep (se 1 (by rfl) ⟨340472, by rfl⟩ : syracuseStep 453963 = 680945) B680945
theorem B683339 : Blo 451781 683339 := bstep (se 1 (by rfl) ⟨512504, by rfl⟩ : syracuseStep 683339 = 1025009) B1025009
theorem B453975 : Blo 451781 453975 := bstep (se 1 (by rfl) ⟨340481, by rfl⟩ : syracuseStep 453975 = 680963) B680963
theorem B683351 : Blo 451781 683351 := bstep (se 1 (by rfl) ⟨512513, by rfl⟩ : syracuseStep 683351 = 1025027) B1025027
theorem B453995 : Blo 451781 453995 := bstep (se 1 (by rfl) ⟨340496, by rfl⟩ : syracuseStep 453995 = 680993) B680993
theorem B454007 : Blo 451781 454007 := bstep (se 1 (by rfl) ⟨340505, by rfl⟩ : syracuseStep 454007 = 681011) B681011
theorem B454027 : Blo 451781 454027 := bstep (se 1 (by rfl) ⟨340520, by rfl⟩ : syracuseStep 454027 = 681041) B681041
theorem B454039 : Blo 451781 454039 := bstep (se 1 (by rfl) ⟨340529, by rfl⟩ : syracuseStep 454039 = 681059) B681059
theorem B683417 : Blo 451781 683417 := bstep (se 2 (by rfl) ⟨256281, by rfl⟩ : syracuseStep 683417 = 512563) B512563
theorem B454059 : Blo 451781 454059 := bstep (se 1 (by rfl) ⟨340544, by rfl⟩ : syracuseStep 454059 = 681089) B681089
theorem B454071 : Blo 451781 454071 := bstep (se 1 (by rfl) ⟨340553, by rfl⟩ : syracuseStep 454071 = 681107) B681107
theorem B454091 : Blo 451781 454091 := bstep (se 1 (by rfl) ⟨340568, by rfl⟩ : syracuseStep 454091 = 681137) B681137
theorem B1535435 : Blo 451781 1535435 := bstep (se 1 (by rfl) ⟨1151576, by rfl⟩ : syracuseStep 1535435 = 2303153) B2303153
theorem B454103 : Blo 451781 454103 := bstep (se 1 (by rfl) ⟨340577, by rfl⟩ : syracuseStep 454103 = 681155) B681155
theorem B454123 : Blo 451781 454123 := bstep (se 1 (by rfl) ⟨340592, by rfl⟩ : syracuseStep 454123 = 681185) B681185
theorem B454135 : Blo 451781 454135 := bstep (se 1 (by rfl) ⟨340601, by rfl⟩ : syracuseStep 454135 = 681203) B681203
theorem B454155 : Blo 451781 454155 := bstep (se 1 (by rfl) ⟨340616, by rfl⟩ : syracuseStep 454155 = 681233) B681233
theorem B683531 : Blo 451781 683531 := bstep (se 1 (by rfl) ⟨512648, by rfl⟩ : syracuseStep 683531 = 1025297) B1025297
theorem B454167 : Blo 451781 454167 := bstep (se 1 (by rfl) ⟨340625, by rfl⟩ : syracuseStep 454167 = 681251) B681251
theorem B683543 : Blo 451781 683543 := bstep (se 1 (by rfl) ⟨512657, by rfl⟩ : syracuseStep 683543 = 1025315) B1025315
theorem B454187 : Blo 451781 454187 := bstep (se 1 (by rfl) ⟨340640, by rfl⟩ : syracuseStep 454187 = 681281) B681281
theorem B454199 : Blo 451781 454199 := bstep (se 1 (by rfl) ⟨340649, by rfl⟩ : syracuseStep 454199 = 681299) B681299
theorem B454219 : Blo 451781 454219 := bstep (se 1 (by rfl) ⟨340664, by rfl⟩ : syracuseStep 454219 = 681329) B681329
theorem B454231 : Blo 451781 454231 := bstep (se 1 (by rfl) ⟨340673, by rfl⟩ : syracuseStep 454231 = 681347) B681347
theorem B683609 : Blo 451781 683609 := bstep (se 2 (by rfl) ⟨256353, by rfl⟩ : syracuseStep 683609 = 512707) B512707
theorem B454251 : Blo 451781 454251 := bstep (se 1 (by rfl) ⟨340688, by rfl⟩ : syracuseStep 454251 = 681377) B681377
theorem B454263 : Blo 451781 454263 := bstep (se 1 (by rfl) ⟨340697, by rfl⟩ : syracuseStep 454263 = 681395) B681395
theorem B454283 : Blo 451781 454283 := bstep (se 1 (by rfl) ⟨340712, by rfl⟩ : syracuseStep 454283 = 681425) B681425
theorem B454295 : Blo 451781 454295 := bstep (se 1 (by rfl) ⟨340721, by rfl⟩ : syracuseStep 454295 = 681443) B681443
theorem B454315 : Blo 451781 454315 := bstep (se 1 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 454315 = 681473) B681473
theorem B1994419 : Blo 451781 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B454327 : Blo 451781 454327 := bstep (se 1 (by rfl) ⟨340745, by rfl⟩ : syracuseStep 454327 = 681491) B681491
theorem B454347 : Blo 451781 454347 := bstep (se 1 (by rfl) ⟨340760, by rfl⟩ : syracuseStep 454347 = 681521) B681521
theorem B454359 : Blo 451781 454359 := bstep (se 1 (by rfl) ⟨340769, by rfl⟩ : syracuseStep 454359 = 681539) B681539
theorem B1535705 : Blo 451781 1535705 := bstep (se 2 (by rfl) ⟨575889, by rfl⟩ : syracuseStep 1535705 = 1151779) B1151779
theorem B454379 : Blo 451781 454379 := bstep (se 1 (by rfl) ⟨340784, by rfl⟩ : syracuseStep 454379 = 681569) B681569
theorem B454391 : Blo 451781 454391 := bstep (se 1 (by rfl) ⟨340793, by rfl⟩ : syracuseStep 454391 = 681587) B681587
theorem B454411 : Blo 451781 454411 := bstep (se 1 (by rfl) ⟨340808, by rfl⟩ : syracuseStep 454411 = 681617) B681617
theorem B454423 : Blo 451781 454423 := bstep (se 1 (by rfl) ⟨340817, by rfl⟩ : syracuseStep 454423 = 681635) B681635
theorem B454443 : Blo 451781 454443 := bstep (se 1 (by rfl) ⟨340832, by rfl⟩ : syracuseStep 454443 = 681665) B681665
theorem B1634099 : Blo 451781 1634099 := bstep (se 1 (by rfl) ⟨1225574, by rfl⟩ : syracuseStep 1634099 = 2451149) B2451149
theorem B454455 : Blo 451781 454455 := bstep (se 1 (by rfl) ⟨340841, by rfl⟩ : syracuseStep 454455 = 681683) B681683
theorem B454475 : Blo 451781 454475 := bstep (se 1 (by rfl) ⟨340856, by rfl⟩ : syracuseStep 454475 = 681713) B681713
theorem B454487 : Blo 451781 454487 := bstep (se 1 (by rfl) ⟨340865, by rfl⟩ : syracuseStep 454487 = 681731) B681731
theorem B454507 : Blo 451781 454507 := bstep (se 1 (by rfl) ⟨340880, by rfl⟩ : syracuseStep 454507 = 681761) B681761
theorem B454519 : Blo 451781 454519 := bstep (se 1 (by rfl) ⟨340889, by rfl⟩ : syracuseStep 454519 = 681779) B681779
theorem B454539 : Blo 451781 454539 := bstep (se 1 (by rfl) ⟨340904, by rfl⟩ : syracuseStep 454539 = 681809) B681809
theorem B454551 : Blo 451781 454551 := bstep (se 1 (by rfl) ⟨340913, by rfl⟩ : syracuseStep 454551 = 681827) B681827
theorem B454571 : Blo 451781 454571 := bstep (se 1 (by rfl) ⟨340928, by rfl⟩ : syracuseStep 454571 = 681857) B681857
theorem B454583 : Blo 451781 454583 := bstep (se 1 (by rfl) ⟨340937, by rfl⟩ : syracuseStep 454583 = 681875) B681875
theorem B454603 : Blo 451781 454603 := bstep (se 1 (by rfl) ⟨340952, by rfl⟩ : syracuseStep 454603 = 681905) B681905
theorem B454615 : Blo 451781 454615 := bstep (se 1 (by rfl) ⟨340961, by rfl⟩ : syracuseStep 454615 = 681923) B681923
theorem B3436505 : Blo 451781 3436505 := bstep (se 2 (by rfl) ⟨1288689, by rfl⟩ : syracuseStep 3436505 = 2577379) B2577379
theorem B454635 : Blo 451781 454635 := bstep (se 1 (by rfl) ⟨340976, by rfl⟩ : syracuseStep 454635 = 681953) B681953
theorem B454647 : Blo 451781 454647 := bstep (se 1 (by rfl) ⟨340985, by rfl⟩ : syracuseStep 454647 = 681971) B681971
theorem B454667 : Blo 451781 454667 := bstep (se 1 (by rfl) ⟨341000, by rfl⟩ : syracuseStep 454667 = 682001) B682001
theorem B454679 : Blo 451781 454679 := bstep (se 1 (by rfl) ⟨341009, by rfl⟩ : syracuseStep 454679 = 682019) B682019
theorem B454699 : Blo 451781 454699 := bstep (se 1 (by rfl) ⟨341024, by rfl⟩ : syracuseStep 454699 = 682049) B682049
theorem B454711 : Blo 451781 454711 := bstep (se 1 (by rfl) ⟨341033, by rfl⟩ : syracuseStep 454711 = 682067) B682067
theorem B454731 : Blo 451781 454731 := bstep (se 1 (by rfl) ⟨341048, by rfl⟩ : syracuseStep 454731 = 682097) B682097
theorem B454743 : Blo 451781 454743 := bstep (se 1 (by rfl) ⟨341057, by rfl⟩ : syracuseStep 454743 = 682115) B682115
theorem B2584669 : Blo 451781 2584669 := bstep (se 3 (by rfl) ⟨484625, by rfl⟩ : syracuseStep 2584669 = 969251) B969251
theorem B454763 : Blo 451781 454763 := bstep (se 1 (by rfl) ⟨341072, by rfl⟩ : syracuseStep 454763 = 682145) B682145
theorem B454775 : Blo 451781 454775 := bstep (se 1 (by rfl) ⟨341081, by rfl⟩ : syracuseStep 454775 = 682163) B682163
theorem B454795 : Blo 451781 454795 := bstep (se 1 (by rfl) ⟨341096, by rfl⟩ : syracuseStep 454795 = 682193) B682193
theorem B454807 : Blo 451781 454807 := bstep (se 1 (by rfl) ⟨341105, by rfl⟩ : syracuseStep 454807 = 682211) B682211
theorem B454827 : Blo 451781 454827 := bstep (se 1 (by rfl) ⟨341120, by rfl⟩ : syracuseStep 454827 = 682241) B682241
theorem B454839 : Blo 451781 454839 := bstep (se 1 (by rfl) ⟨341129, by rfl⟩ : syracuseStep 454839 = 682259) B682259
theorem B454859 : Blo 451781 454859 := bstep (se 1 (by rfl) ⟨341144, by rfl⟩ : syracuseStep 454859 = 682289) B682289
theorem B454871 : Blo 451781 454871 := bstep (se 1 (by rfl) ⟨341153, by rfl⟩ : syracuseStep 454871 = 682307) B682307
theorem B815321 : Blo 451781 815321 := bstep (se 2 (by rfl) ⟨305745, by rfl⟩ : syracuseStep 815321 = 611491) B611491
theorem B454891 : Blo 451781 454891 := bstep (se 1 (by rfl) ⟨341168, by rfl⟩ : syracuseStep 454891 = 682337) B682337
theorem B454903 : Blo 451781 454903 := bstep (se 1 (by rfl) ⟨341177, by rfl⟩ : syracuseStep 454903 = 682355) B682355
theorem B454923 : Blo 451781 454923 := bstep (se 1 (by rfl) ⟨341192, by rfl⟩ : syracuseStep 454923 = 682385) B682385
theorem B454935 : Blo 451781 454935 := bstep (se 1 (by rfl) ⟨341201, by rfl⟩ : syracuseStep 454935 = 682403) B682403
theorem B454955 : Blo 451781 454955 := bstep (se 1 (by rfl) ⟨341216, by rfl⟩ : syracuseStep 454955 = 682433) B682433
theorem B454967 : Blo 451781 454967 := bstep (se 1 (by rfl) ⟨341225, by rfl⟩ : syracuseStep 454967 = 682451) B682451
theorem B454987 : Blo 451781 454987 := bstep (se 1 (by rfl) ⟨341240, by rfl⟩ : syracuseStep 454987 = 682481) B682481
theorem B454999 : Blo 451781 454999 := bstep (se 1 (by rfl) ⟨341249, by rfl⟩ : syracuseStep 454999 = 682499) B682499
theorem B455019 : Blo 451781 455019 := bstep (se 1 (by rfl) ⟨341264, by rfl⟩ : syracuseStep 455019 = 682529) B682529
theorem B455031 : Blo 451781 455031 := bstep (se 1 (by rfl) ⟨341273, by rfl⟩ : syracuseStep 455031 = 682547) B682547
theorem B455051 : Blo 451781 455051 := bstep (se 1 (by rfl) ⟨341288, by rfl⟩ : syracuseStep 455051 = 682577) B682577
theorem B455063 : Blo 451781 455063 := bstep (se 1 (by rfl) ⟨341297, by rfl⟩ : syracuseStep 455063 = 682595) B682595
theorem B1536407 : Blo 451781 1536407 := bstep (se 1 (by rfl) ⟨1152305, by rfl⟩ : syracuseStep 1536407 = 2304611) B2304611
theorem B455083 : Blo 451781 455083 := bstep (se 1 (by rfl) ⟨341312, by rfl⟩ : syracuseStep 455083 = 682625) B682625
theorem B455095 : Blo 451781 455095 := bstep (se 1 (by rfl) ⟨341321, by rfl⟩ : syracuseStep 455095 = 682643) B682643
theorem B455115 : Blo 451781 455115 := bstep (se 1 (by rfl) ⟨341336, by rfl⟩ : syracuseStep 455115 = 682673) B682673
theorem B455127 : Blo 451781 455127 := bstep (se 1 (by rfl) ⟨341345, by rfl⟩ : syracuseStep 455127 = 682691) B682691
theorem B455147 : Blo 451781 455147 := bstep (se 1 (by rfl) ⟨341360, by rfl⟩ : syracuseStep 455147 = 682721) B682721
theorem B455159 : Blo 451781 455159 := bstep (se 1 (by rfl) ⟨341369, by rfl⟩ : syracuseStep 455159 = 682739) B682739
theorem B455179 : Blo 451781 455179 := bstep (se 1 (by rfl) ⟨341384, by rfl⟩ : syracuseStep 455179 = 682769) B682769
theorem B2290193 : Blo 451781 2290193 := bstep (se 2 (by rfl) ⟨858822, by rfl⟩ : syracuseStep 2290193 = 1717645) B1717645
theorem B455191 : Blo 451781 455191 := bstep (se 1 (by rfl) ⟨341393, by rfl⟩ : syracuseStep 455191 = 682787) B682787
theorem B455211 : Blo 451781 455211 := bstep (se 1 (by rfl) ⟨341408, by rfl⟩ : syracuseStep 455211 = 682817) B682817
theorem B455223 : Blo 451781 455223 := bstep (se 1 (by rfl) ⟨341417, by rfl⟩ : syracuseStep 455223 = 682835) B682835
theorem B455243 : Blo 451781 455243 := bstep (se 1 (by rfl) ⟨341432, by rfl⟩ : syracuseStep 455243 = 682865) B682865
theorem B455255 : Blo 451781 455255 := bstep (se 1 (by rfl) ⟨341441, by rfl⟩ : syracuseStep 455255 = 682883) B682883
theorem B455275 : Blo 451781 455275 := bstep (se 1 (by rfl) ⟨341456, by rfl⟩ : syracuseStep 455275 = 682913) B682913
theorem B455287 : Blo 451781 455287 := bstep (se 1 (by rfl) ⟨341465, by rfl⟩ : syracuseStep 455287 = 682931) B682931
theorem B455307 : Blo 451781 455307 := bstep (se 1 (by rfl) ⟨341480, by rfl⟩ : syracuseStep 455307 = 682961) B682961
theorem B455319 : Blo 451781 455319 := bstep (se 1 (by rfl) ⟨341489, by rfl⟩ : syracuseStep 455319 = 682979) B682979
theorem B455339 : Blo 451781 455339 := bstep (se 1 (by rfl) ⟨341504, by rfl⟩ : syracuseStep 455339 = 683009) B683009
theorem B2290355 : Blo 451781 2290355 := bstep (se 1 (by rfl) ⟨1717766, by rfl⟩ : syracuseStep 2290355 = 3435533) B3435533
theorem B455351 : Blo 451781 455351 := bstep (se 1 (by rfl) ⟨341513, by rfl⟩ : syracuseStep 455351 = 683027) B683027
theorem B455371 : Blo 451781 455371 := bstep (se 1 (by rfl) ⟨341528, by rfl⟩ : syracuseStep 455371 = 683057) B683057
theorem B455383 : Blo 451781 455383 := bstep (se 1 (by rfl) ⟨341537, by rfl⟩ : syracuseStep 455383 = 683075) B683075
theorem B455403 : Blo 451781 455403 := bstep (se 1 (by rfl) ⟨341552, by rfl⟩ : syracuseStep 455403 = 683105) B683105
theorem B455415 : Blo 451781 455415 := bstep (se 1 (by rfl) ⟨341561, by rfl⟩ : syracuseStep 455415 = 683123) B683123
theorem B455435 : Blo 451781 455435 := bstep (se 1 (by rfl) ⟨341576, by rfl⟩ : syracuseStep 455435 = 683153) B683153
theorem B455447 : Blo 451781 455447 := bstep (se 1 (by rfl) ⟨341585, by rfl⟩ : syracuseStep 455447 = 683171) B683171
theorem B455467 : Blo 451781 455467 := bstep (se 1 (by rfl) ⟨341600, by rfl⟩ : syracuseStep 455467 = 683201) B683201
theorem B455479 : Blo 451781 455479 := bstep (se 1 (by rfl) ⟨341609, by rfl⟩ : syracuseStep 455479 = 683219) B683219
theorem B2978635 : Blo 451781 2978635 := bstep (se 1 (by rfl) ⟨2233976, by rfl⟩ : syracuseStep 2978635 = 4467953) B4467953
theorem B455499 : Blo 451781 455499 := bstep (se 1 (by rfl) ⟨341624, by rfl⟩ : syracuseStep 455499 = 683249) B683249
theorem B455511 : Blo 451781 455511 := bstep (se 1 (by rfl) ⟨341633, by rfl⟩ : syracuseStep 455511 = 683267) B683267
theorem B455531 : Blo 451781 455531 := bstep (se 1 (by rfl) ⟨341648, by rfl⟩ : syracuseStep 455531 = 683297) B683297
theorem B455543 : Blo 451781 455543 := bstep (se 1 (by rfl) ⟨341657, by rfl⟩ : syracuseStep 455543 = 683315) B683315
theorem B455563 : Blo 451781 455563 := bstep (se 1 (by rfl) ⟨341672, by rfl⟩ : syracuseStep 455563 = 683345) B683345
theorem B455575 : Blo 451781 455575 := bstep (se 1 (by rfl) ⟨341681, by rfl⟩ : syracuseStep 455575 = 683363) B683363
theorem B455595 : Blo 451781 455595 := bstep (se 1 (by rfl) ⟨341696, by rfl⟩ : syracuseStep 455595 = 683393) B683393
theorem B1536947 : Blo 451781 1536947 := bstep (se 1 (by rfl) ⟨1152710, by rfl⟩ : syracuseStep 1536947 = 2305421) B2305421
theorem B455607 : Blo 451781 455607 := bstep (se 1 (by rfl) ⟨341705, by rfl⟩ : syracuseStep 455607 = 683411) B683411
theorem B455627 : Blo 451781 455627 := bstep (se 1 (by rfl) ⟨341720, by rfl⟩ : syracuseStep 455627 = 683441) B683441
theorem B455639 : Blo 451781 455639 := bstep (se 1 (by rfl) ⟨341729, by rfl⟩ : syracuseStep 455639 = 683459) B683459
theorem B455659 : Blo 451781 455659 := bstep (se 1 (by rfl) ⟨341744, by rfl⟩ : syracuseStep 455659 = 683489) B683489
theorem B455671 : Blo 451781 455671 := bstep (se 1 (by rfl) ⟨341753, by rfl⟩ : syracuseStep 455671 = 683507) B683507
theorem B619531 : Blo 451781 619531 := bstep (se 1 (by rfl) ⟨464648, by rfl⟩ : syracuseStep 619531 = 929297) B929297
theorem B455691 : Blo 451781 455691 := bstep (se 1 (by rfl) ⟨341768, by rfl⟩ : syracuseStep 455691 = 683537) B683537
theorem B455703 : Blo 451781 455703 := bstep (se 1 (by rfl) ⟨341777, by rfl⟩ : syracuseStep 455703 = 683555) B683555
theorem B455723 : Blo 451781 455723 := bstep (se 1 (by rfl) ⟨341792, by rfl⟩ : syracuseStep 455723 = 683585) B683585
theorem B455735 : Blo 451781 455735 := bstep (se 1 (by rfl) ⟨341801, by rfl⟩ : syracuseStep 455735 = 683603) B683603
theorem B455755 : Blo 451781 455755 := bstep (se 1 (by rfl) ⟨341816, by rfl⟩ : syracuseStep 455755 = 683633) B683633
theorem B455767 : Blo 451781 455767 := bstep (se 1 (by rfl) ⟨341825, by rfl⟩ : syracuseStep 455767 = 683651) B683651
theorem B2946179 : Blo 451781 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B1537217 : Blo 451781 1537217 := bstep (se 2 (by rfl) ⟨576456, by rfl⟩ : syracuseStep 1537217 = 1152913) B1152913
theorem B1144115 : Blo 451781 1144115 := bstep (se 1 (by rfl) ⟨858086, by rfl⟩ : syracuseStep 1144115 = 1716173) B1716173
theorem B1832669 : Blo 451781 1832669 := bstep (se 3 (by rfl) ⟨343625, by rfl⟩ : syracuseStep 1832669 = 687251) B687251
theorem B2062045 : Blo 451781 2062045 := bstep (se 3 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 2062045 = 773267) B773267
theorem B1537757 : Blo 451781 1537757 := bstep (se 3 (by rfl) ⟨288329, by rfl⟩ : syracuseStep 1537757 = 576659) B576659
theorem B1931053 : Blo 451781 1931053 := bstep (se 3 (by rfl) ⟨362072, by rfl⟩ : syracuseStep 1931053 = 724145) B724145
theorem B2094913 : Blo 451781 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B1144651 : Blo 451781 1144651 := bstep (se 1 (by rfl) ⟨858488, by rfl⟩ : syracuseStep 1144651 = 1716977) B1716977
theorem B3667805 : Blo 451781 3667805 := bstep (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) B1375427
theorem B980851 : Blo 451781 980851 := bstep (se 1 (by rfl) ⟨735638, by rfl⟩ : syracuseStep 980851 = 1471277) B1471277
theorem B41875379 : Blo 451781 41875379 := bstep (se 1 (by rfl) ⟨31406534, by rfl⟩ : syracuseStep 41875379 = 62813069) B62813069
theorem B1144793 : Blo 451781 1144793 := bstep (se 2 (by rfl) ⟨429297, by rfl⟩ : syracuseStep 1144793 = 858595) B858595
theorem B817303 : Blo 451781 817303 := bstep (se 1 (by rfl) ⟨612977, by rfl⟩ : syracuseStep 817303 = 1225955) B1225955
theorem B2292299 : Blo 451781 2292299 := bstep (se 1 (by rfl) ⟨1719224, by rfl⟩ : syracuseStep 2292299 = 3438449) B3438449
theorem B1636939 : Blo 451781 1636939 := bstep (se 1 (by rfl) ⟨1227704, by rfl⟩ : syracuseStep 1636939 = 2455409) B2455409
theorem B1964675 : Blo 451781 1964675 := bstep (se 1 (by rfl) ⟨1473506, by rfl⟩ : syracuseStep 1964675 = 2947013) B2947013
theorem B817879 : Blo 451781 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B817921 : Blo 451781 817921 := bstep (se 2 (by rfl) ⟨306720, by rfl⟩ : syracuseStep 817921 = 613441) B613441
theorem B1145623 : Blo 451781 1145623 := bstep (se 1 (by rfl) ⟨859217, by rfl⟩ : syracuseStep 1145623 = 1718435) B1718435
theorem B654103 : Blo 451781 654103 := bstep (se 1 (by rfl) ⟨490577, by rfl⟩ : syracuseStep 654103 = 981155) B981155
theorem B1637171 : Blo 451781 1637171 := bstep (se 1 (by rfl) ⟨1227878, by rfl⟩ : syracuseStep 1637171 = 2455757) B2455757
theorem B818009 : Blo 451781 818009 := bstep (se 2 (by rfl) ⟨306753, by rfl⟩ : syracuseStep 818009 = 613507) B613507
theorem B1834001 : Blo 451781 1834001 := bstep (se 2 (by rfl) ⟨687750, by rfl⟩ : syracuseStep 1834001 = 1375501) B1375501
theorem B6290507 : Blo 451781 6290507 := bstep (se 1 (by rfl) ⟨4717880, by rfl⟩ : syracuseStep 6290507 = 9435761) B9435761
theorem B1146059 : Blo 451781 1146059 := bstep (se 1 (by rfl) ⟨859544, by rfl⟩ : syracuseStep 1146059 = 1719089) B1719089
theorem B3439907 : Blo 451781 3439907 := bstep (se 1 (by rfl) ⟨2579930, by rfl⟩ : syracuseStep 3439907 = 5159861) B5159861
theorem B1932761 : Blo 451781 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B1146433 : Blo 451781 1146433 := bstep (se 2 (by rfl) ⟨429912, by rfl⟩ : syracuseStep 1146433 = 859825) B859825
theorem B818903 : Blo 451781 818903 := bstep (se 1 (by rfl) ⟨614177, by rfl⟩ : syracuseStep 818903 = 1228355) B1228355
theorem B2916161 : Blo 451781 2916161 := bstep (se 2 (by rfl) ⟨1093560, by rfl⟩ : syracuseStep 2916161 = 2187121) B2187121
theorem B688171 : Blo 451781 688171 := bstep (se 1 (by rfl) ⟨516128, by rfl⟩ : syracuseStep 688171 = 1032257) B1032257
theorem B1147081 : Blo 451781 1147081 := bstep (se 2 (by rfl) ⟨430155, by rfl⟩ : syracuseStep 1147081 = 860311) B860311
theorem B1147223 : Blo 451781 1147223 := bstep (se 1 (by rfl) ⟨860417, by rfl⟩ : syracuseStep 1147223 = 1720835) B1720835
theorem B2589043 : Blo 451781 2589043 := bstep (se 1 (by rfl) ⟨1941782, by rfl⟩ : syracuseStep 2589043 = 3883565) B3883565
theorem B1933703 : Blo 451781 1933703 := bstep (se 1 (by rfl) ⟨1450277, by rfl⟩ : syracuseStep 1933703 = 2900555) B2900555
theorem B1933753 : Blo 451781 1933753 := bstep (se 2 (by rfl) ⟨725157, by rfl⟩ : syracuseStep 1933753 = 1450315) B1450315
theorem B3932675 : Blo 451781 3932675 := bstep (se 1 (by rfl) ⟨2949506, by rfl⟩ : syracuseStep 3932675 = 5899013) B5899013
theorem B1016711 : Blo 451781 1016711 := bstep (se 1 (by rfl) ⟨762533, by rfl⟩ : syracuseStep 1016711 = 1525067) B1525067
theorem B1016891 : Blo 451781 1016891 := bstep (se 1 (by rfl) ⟨762668, by rfl⟩ : syracuseStep 1016891 = 1525337) B1525337
theorem B3867709 : Blo 451781 3867709 := bstep (se 3 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 3867709 = 1450391) B1450391
theorem B1017017 : Blo 451781 1017017 := bstep (se 2 (by rfl) ⟨381381, by rfl⟩ : syracuseStep 1017017 = 762763) B762763
theorem B2328011 : Blo 451781 2328011 := bstep (se 1 (by rfl) ⟨1746008, by rfl⟩ : syracuseStep 2328011 = 3492017) B3492017
theorem B2917853 : Blo 451781 2917853 := bstep (se 3 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 2917853 = 1094195) B1094195
theorem B1476107 : Blo 451781 1476107 := bstep (se 1 (by rfl) ⟨1107080, by rfl⟩ : syracuseStep 1476107 = 2214161) B2214161
theorem B1017359 : Blo 451781 1017359 := bstep (se 1 (by rfl) ⟨763019, by rfl⟩ : syracuseStep 1017359 = 1526039) B1526039
theorem B1017377 : Blo 451781 1017377 := bstep (se 2 (by rfl) ⟨381516, by rfl⟩ : syracuseStep 1017377 = 763033) B763033
theorem B1935085 : Blo 451781 1935085 := bstep (se 3 (by rfl) ⟨362828, by rfl⟩ : syracuseStep 1935085 = 725657) B725657
theorem B2361089 : Blo 451781 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B1640225 : Blo 451781 1640225 := bstep (se 2 (by rfl) ⟨615084, by rfl⟩ : syracuseStep 1640225 = 1230169) B1230169
theorem B2590501 : Blo 451781 2590501 := bstep (se 4 (by rfl) ⟨242859, by rfl⟩ : syracuseStep 2590501 = 485719) B485719
theorem B821035 : Blo 451781 821035 := bstep (se 1 (by rfl) ⟨615776, by rfl⟩ : syracuseStep 821035 = 1231553) B1231553
theorem B1017719 : Blo 451781 1017719 := bstep (se 1 (by rfl) ⟨763289, by rfl⟩ : syracuseStep 1017719 = 1526579) B1526579
theorem B657271 : Blo 451781 657271 := bstep (se 1 (by rfl) ⟨492953, by rfl⟩ : syracuseStep 657271 = 985907) B985907
theorem B21235729 : Blo 451781 21235729 := bstep (se 2 (by rfl) ⟨7963398, by rfl⟩ : syracuseStep 21235729 = 15926797) B15926797
theorem B1017899 : Blo 451781 1017899 := bstep (se 1 (by rfl) ⟨763424, by rfl⟩ : syracuseStep 1017899 = 1526849) B1526849
theorem B1935427 : Blo 451781 1935427 := bstep (se 1 (by rfl) ⟨1451570, by rfl⟩ : syracuseStep 1935427 = 2903141) B2903141
theorem B690439 : Blo 451781 690439 := bstep (se 1 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 690439 = 1035659) B1035659
theorem B5507345 : Blo 451781 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B2591027 : Blo 451781 2591027 := bstep (se 1 (by rfl) ⟨1943270, by rfl⟩ : syracuseStep 2591027 = 3886541) B3886541
theorem B1313111 : Blo 451781 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B1149299 : Blo 451781 1149299 := bstep (se 1 (by rfl) ⟨861974, by rfl⟩ : syracuseStep 1149299 = 1723949) B1723949
theorem B1018259 : Blo 451781 1018259 := bstep (se 1 (by rfl) ⟨763694, by rfl⟩ : syracuseStep 1018259 = 1527389) B1527389
theorem B1018313 : Blo 451781 1018313 := bstep (se 2 (by rfl) ⟨381867, by rfl⟩ : syracuseStep 1018313 = 763735) B763735
theorem B2296349 : Blo 451781 2296349 := bstep (se 3 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 2296349 = 861131) B861131
theorem B723755 : Blo 451781 723755 := bstep (se 1 (by rfl) ⟨542816, by rfl⟩ : syracuseStep 723755 = 1085633) B1085633
theorem B4655987 : Blo 451781 4655987 := bstep (se 1 (by rfl) ⟨3491990, by rfl⟩ : syracuseStep 4655987 = 6983981) B6983981
theorem B1149815 : Blo 451781 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B2329489 : Blo 451781 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B2296835 : Blo 451781 2296835 := bstep (se 1 (by rfl) ⟨1722626, by rfl⟩ : syracuseStep 2296835 = 3445253) B3445253
theorem B2460683 : Blo 451781 2460683 := bstep (se 1 (by rfl) ⟨1845512, by rfl⟩ : syracuseStep 2460683 = 3691025) B3691025
theorem B1019015 : Blo 451781 1019015 := bstep (se 1 (by rfl) ⟨764261, by rfl⟩ : syracuseStep 1019015 = 1528523) B1528523
theorem B1019195 : Blo 451781 1019195 := bstep (se 1 (by rfl) ⟨764396, by rfl⟩ : syracuseStep 1019195 = 1528793) B1528793
theorem B2919827 : Blo 451781 2919827 := bstep (se 1 (by rfl) ⟨2189870, by rfl⟩ : syracuseStep 2919827 = 4379741) B4379741
theorem B1019321 : Blo 451781 1019321 := bstep (se 2 (by rfl) ⟨382245, by rfl⟩ : syracuseStep 1019321 = 764491) B764491
theorem B2592485 : Blo 451781 2592485 := bstep (se 4 (by rfl) ⟨243045, by rfl⟩ : syracuseStep 2592485 = 486091) B486091
theorem B1019663 : Blo 451781 1019663 := bstep (se 1 (by rfl) ⟨764747, by rfl⟩ : syracuseStep 1019663 = 1529495) B1529495
theorem B1019681 : Blo 451781 1019681 := bstep (se 2 (by rfl) ⟨382380, by rfl⟩ : syracuseStep 1019681 = 764761) B764761
theorem B1150807 : Blo 451781 1150807 := bstep (se 1 (by rfl) ⟨863105, by rfl⟩ : syracuseStep 1150807 = 1726211) B1726211
theorem B2461529 : Blo 451781 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B4362245 : Blo 451781 4362245 := bstep (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) B817921
theorem B692239 : Blo 451781 692239 := bstep (se 1 (by rfl) ⟨519179, by rfl⟩ : syracuseStep 692239 = 1038359) B1038359
theorem B1020023 : Blo 451781 1020023 := bstep (se 1 (by rfl) ⟨765017, by rfl⟩ : syracuseStep 1020023 = 1530035) B1530035
theorem B1151111 : Blo 451781 1151111 := bstep (se 1 (by rfl) ⟨863333, by rfl⟩ : syracuseStep 1151111 = 1726667) B1726667
theorem B1151243 : Blo 451781 1151243 := bstep (se 1 (by rfl) ⟨863432, by rfl⟩ : syracuseStep 1151243 = 1726865) B1726865
theorem B1020203 : Blo 451781 1020203 := bstep (se 1 (by rfl) ⟨765152, by rfl⟩ : syracuseStep 1020203 = 1530305) B1530305
theorem B1085815 : Blo 451781 1085815 := bstep (se 1 (by rfl) ⟨814361, by rfl⟩ : syracuseStep 1085815 = 1628723) B1628723
theorem B692615 : Blo 451781 692615 := bstep (se 1 (by rfl) ⟨519461, by rfl⟩ : syracuseStep 692615 = 1038923) B1038923
theorem B59609621 : Blo 451781 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B2298455 : Blo 451781 2298455 := bstep (se 1 (by rfl) ⟨1723841, by rfl⟩ : syracuseStep 2298455 = 3447683) B3447683
theorem B21041795 : Blo 451781 21041795 := bstep (se 1 (by rfl) ⟨15781346, by rfl⟩ : syracuseStep 21041795 = 31562693) B31562693
theorem B1020563 : Blo 451781 1020563 := bstep (se 1 (by rfl) ⟨765422, by rfl⟩ : syracuseStep 1020563 = 1530845) B1530845
theorem B1020617 : Blo 451781 1020617 := bstep (se 2 (by rfl) ⟨382731, by rfl⟩ : syracuseStep 1020617 = 765463) B765463
theorem B1381121 : Blo 451781 1381121 := bstep (se 2 (by rfl) ⟨517920, by rfl⟩ : syracuseStep 1381121 = 1035841) B1035841
theorem B1151759 : Blo 451781 1151759 := bstep (se 1 (by rfl) ⟨863819, by rfl⟩ : syracuseStep 1151759 = 1727639) B1727639
theorem B1151891 : Blo 451781 1151891 := bstep (se 1 (by rfl) ⟨863918, by rfl⟩ : syracuseStep 1151891 = 1727837) B1727837
theorem B2659225 : Blo 451781 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B3118027 : Blo 451781 3118027 := bstep (se 1 (by rfl) ⟨2338520, by rfl⟩ : syracuseStep 3118027 = 4677041) B4677041
theorem B1086479 : Blo 451781 1086479 := bstep (se 1 (by rfl) ⟨814859, by rfl⟩ : syracuseStep 1086479 = 1629719) B1629719
theorem B2298941 : Blo 451781 2298941 := bstep (se 3 (by rfl) ⟨431051, by rfl⟩ : syracuseStep 2298941 = 862103) B862103
theorem B7968131 : Blo 451781 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B1021319 : Blo 451781 1021319 := bstep (se 1 (by rfl) ⟨765989, by rfl⟩ : syracuseStep 1021319 = 1531979) B1531979
theorem B923081 : Blo 451781 923081 := bstep (se 2 (by rfl) ⟨346155, by rfl⟩ : syracuseStep 923081 = 692311) B692311
theorem B3446225 : Blo 451781 3446225 := bstep (se 2 (by rfl) ⟨1292334, by rfl⟩ : syracuseStep 3446225 = 2584669) B2584669
theorem B1021499 : Blo 451781 1021499 := bstep (se 1 (by rfl) ⟨766124, by rfl⟩ : syracuseStep 1021499 = 1532249) B1532249
theorem B2954819 : Blo 451781 2954819 := bstep (se 1 (by rfl) ⟨2216114, by rfl⟩ : syracuseStep 2954819 = 4432229) B4432229
theorem B1021625 : Blo 451781 1021625 := bstep (se 2 (by rfl) ⟨383109, by rfl⟩ : syracuseStep 1021625 = 766219) B766219
theorem B1153025 : Blo 451781 1153025 := bstep (se 2 (by rfl) ⟨432384, by rfl⟩ : syracuseStep 1153025 = 864769) B864769
theorem B1021967 : Blo 451781 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B1021985 : Blo 451781 1021985 := bstep (se 2 (by rfl) ⟨383244, by rfl⟩ : syracuseStep 1021985 = 766489) B766489
theorem B1022327 : Blo 451781 1022327 := bstep (se 1 (by rfl) ⟨766745, by rfl⟩ : syracuseStep 1022327 = 1533491) B1533491
theorem B1153399 : Blo 451781 1153399 := bstep (se 1 (by rfl) ⟨865049, by rfl⟩ : syracuseStep 1153399 = 1730099) B1730099
theorem B3971513 : Blo 451781 3971513 := bstep (se 2 (by rfl) ⟨1489317, by rfl⟩ : syracuseStep 3971513 = 2978635) B2978635
theorem B1022507 : Blo 451781 1022507 := bstep (se 1 (by rfl) ⟨766880, by rfl⟩ : syracuseStep 1022507 = 1533761) B1533761
theorem B2071241 : Blo 451781 2071241 := bstep (se 2 (by rfl) ⟨776715, by rfl⟩ : syracuseStep 2071241 = 1553431) B1553431
theorem B727823 : Blo 451781 727823 := bstep (se 1 (by rfl) ⟨545867, by rfl⟩ : syracuseStep 727823 = 1091735) B1091735
theorem B2300723 : Blo 451781 2300723 := bstep (se 1 (by rfl) ⟨1725542, by rfl⟩ : syracuseStep 2300723 = 3451085) B3451085
theorem B1022867 : Blo 451781 1022867 := bstep (se 1 (by rfl) ⟨767150, by rfl⟩ : syracuseStep 1022867 = 1534301) B1534301
theorem B859081 : Blo 451781 859081 := bstep (se 2 (by rfl) ⟨322155, by rfl⟩ : syracuseStep 859081 = 644311) B644311
theorem B1022921 : Blo 451781 1022921 := bstep (se 2 (by rfl) ⟨383595, by rfl⟩ : syracuseStep 1022921 = 767191) B767191
theorem B2301047 : Blo 451781 2301047 := bstep (se 1 (by rfl) ⟨1725785, by rfl⟩ : syracuseStep 2301047 = 3451571) B3451571
theorem B1023623 : Blo 451781 1023623 := bstep (se 1 (by rfl) ⟨767717, by rfl⟩ : syracuseStep 1023623 = 1535435) B1535435
theorem B2793217 : Blo 451781 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B1384235 : Blo 451781 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B1023803 : Blo 451781 1023803 := bstep (se 1 (by rfl) ⟨767852, by rfl⟩ : syracuseStep 1023803 = 1535705) B1535705
theorem B1023929 : Blo 451781 1023929 := bstep (se 2 (by rfl) ⟨383973, by rfl⟩ : syracuseStep 1023929 = 767947) B767947
theorem B2302019 : Blo 451781 2302019 := bstep (se 1 (by rfl) ⟨1726514, by rfl⟩ : syracuseStep 2302019 = 3453029) B3453029
theorem B1089737 : Blo 451781 1089737 := bstep (se 2 (by rfl) ⟨408651, by rfl⟩ : syracuseStep 1089737 = 817303) B817303
theorem B1024271 : Blo 451781 1024271 := bstep (se 1 (by rfl) ⟨768203, by rfl⟩ : syracuseStep 1024271 = 1536407) B1536407
theorem B1024289 : Blo 451781 1024289 := bstep (se 2 (by rfl) ⟨384108, by rfl⟩ : syracuseStep 1024289 = 768217) B768217
theorem B2302343 : Blo 451781 2302343 := bstep (se 1 (by rfl) ⟨1726757, by rfl⟩ : syracuseStep 2302343 = 3453515) B3453515
theorem B2171281 : Blo 451781 2171281 := bstep (se 2 (by rfl) ⟨814230, by rfl⟩ : syracuseStep 2171281 = 1628461) B1628461
theorem B1024631 : Blo 451781 1024631 := bstep (se 1 (by rfl) ⟨768473, by rfl⟩ : syracuseStep 1024631 = 1536947) B1536947
theorem B1024811 : Blo 451781 1024811 := bstep (se 1 (by rfl) ⟨768608, by rfl⟩ : syracuseStep 1024811 = 1537217) B1537217
theorem B762743 : Blo 451781 762743 := bstep (se 1 (by rfl) ⟨572057, by rfl⟩ : syracuseStep 762743 = 1144115) B1144115
theorem B1090505 : Blo 451781 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B1221779 : Blo 451781 1221779 := bstep (se 1 (by rfl) ⟨916334, by rfl⟩ : syracuseStep 1221779 = 1832669) B1832669
theorem B1025171 : Blo 451781 1025171 := bstep (se 1 (by rfl) ⟨768878, by rfl⟩ : syracuseStep 1025171 = 1537757) B1537757
theorem B1025225 : Blo 451781 1025225 := bstep (se 2 (by rfl) ⟨384459, by rfl⟩ : syracuseStep 1025225 = 768919) B768919
theorem B5154029 : Blo 451781 5154029 := bstep (se 3 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 5154029 = 1932761) B1932761
theorem B1844461 : Blo 451781 1844461 := bstep (se 3 (by rfl) ⟨345836, by rfl⟩ : syracuseStep 1844461 = 691673) B691673
theorem B763195 : Blo 451781 763195 := bstep (se 1 (by rfl) ⟨572396, by rfl⟩ : syracuseStep 763195 = 1144793) B1144793
theorem B861587 : Blo 451781 861587 := bstep (se 1 (by rfl) ⟨646190, by rfl⟩ : syracuseStep 861587 = 1292381) B1292381
theorem B763337 : Blo 451781 763337 := bstep (se 2 (by rfl) ⟨286251, by rfl⟩ : syracuseStep 763337 = 572503) B572503
theorem B5809765 : Blo 451781 5809765 := bstep (se 4 (by rfl) ⟨544665, by rfl⟩ : syracuseStep 5809765 = 1089331) B1089331
theorem B861815 : Blo 451781 861815 := bstep (se 1 (by rfl) ⟨646361, by rfl⟩ : syracuseStep 861815 = 1292723) B1292723
theorem B3679937 : Blo 451781 3679937 := bstep (se 2 (by rfl) ⟨1379976, by rfl⟩ : syracuseStep 3679937 = 2759953) B2759953
theorem B1091447 : Blo 451781 1091447 := bstep (se 1 (by rfl) ⟨818585, by rfl⟩ : syracuseStep 1091447 = 1637171) B1637171
theorem B1222667 : Blo 451781 1222667 := bstep (se 1 (by rfl) ⟨917000, by rfl⟩ : syracuseStep 1222667 = 1834001) B1834001
theorem B16623629 : Blo 451781 16623629 := bstep (se 3 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 16623629 = 6233861) B6233861
theorem B764039 : Blo 451781 764039 := bstep (se 1 (by rfl) ⟨573029, by rfl⟩ : syracuseStep 764039 = 1146059) B1146059
theorem B1452289 : Blo 451781 1452289 := bstep (se 2 (by rfl) ⟨544608, by rfl⟩ : syracuseStep 1452289 = 1089217) B1089217
theorem B1944107 : Blo 451781 1944107 := bstep (se 1 (by rfl) ⟨1458080, by rfl⟩ : syracuseStep 1944107 = 2916161) B2916161
theorem B764687 : Blo 451781 764687 := bstep (se 1 (by rfl) ⟨573515, by rfl⟩ : syracuseStep 764687 = 1147031) B1147031
theorem B18590579 : Blo 451781 18590579 := bstep (se 1 (by rfl) ⟨13942934, by rfl⟩ : syracuseStep 18590579 = 27885869) B27885869
theorem B928903 : Blo 451781 928903 := bstep (se 1 (by rfl) ⟨696677, by rfl⟩ : syracuseStep 928903 = 1393355) B1393355
theorem B1289351 : Blo 451781 1289351 := bstep (se 1 (by rfl) ⟨967013, by rfl⟩ : syracuseStep 1289351 = 1934027) B1934027
theorem B1715489 : Blo 451781 1715489 := bstep (se 2 (by rfl) ⟨643308, by rfl⟩ : syracuseStep 1715489 = 1286617) B1286617
theorem B765227 : Blo 451781 765227 := bstep (se 1 (by rfl) ⟨573920, by rfl⟩ : syracuseStep 765227 = 1147841) B1147841
theorem B863531 : Blo 451781 863531 := bstep (se 1 (by rfl) ⟨647648, by rfl⟩ : syracuseStep 863531 = 1295297) B1295297
theorem B1289533 : Blo 451781 1289533 := bstep (se 3 (by rfl) ⟨241787, by rfl⟩ : syracuseStep 1289533 = 483575) B483575
theorem B1289591 : Blo 451781 1289591 := bstep (se 1 (by rfl) ⟨967193, by rfl⟩ : syracuseStep 1289591 = 1934387) B1934387
theorem B863759 : Blo 451781 863759 := bstep (se 1 (by rfl) ⟨647819, by rfl⟩ : syracuseStep 863759 = 1295639) B1295639
theorem B24850061 : Blo 451781 24850061 := bstep (se 3 (by rfl) ⟨4659386, by rfl⟩ : syracuseStep 24850061 = 9318773) B9318773
theorem B765625 : Blo 451781 765625 := bstep (se 2 (by rfl) ⟨287109, by rfl⟩ : syracuseStep 765625 = 574219) B574219
theorem B2305907 : Blo 451781 2305907 := bstep (se 1 (by rfl) ⟨1729430, by rfl⟩ : syracuseStep 2305907 = 3458861) B3458861
theorem B2076625 : Blo 451781 2076625 := bstep (se 2 (by rfl) ⟨778734, by rfl⟩ : syracuseStep 2076625 = 1557469) B1557469
theorem B1716461 : Blo 451781 1716461 := bstep (se 3 (by rfl) ⟨321836, by rfl⟩ : syracuseStep 1716461 = 643673) B643673
theorem B4370705 : Blo 451781 4370705 := bstep (se 2 (by rfl) ⟨1639014, by rfl⟩ : syracuseStep 4370705 = 3278029) B3278029
theorem B2306393 : Blo 451781 2306393 := bstep (se 2 (by rfl) ⟨864897, by rfl⟩ : syracuseStep 2306393 = 1729795) B1729795
theorem B766327 : Blo 451781 766327 := bstep (se 1 (by rfl) ⟨574745, by rfl⟩ : syracuseStep 766327 = 1149491) B1149491
theorem B1290649 : Blo 451781 1290649 := bstep (se 2 (by rfl) ⟨483993, by rfl⟩ : syracuseStep 1290649 = 967987) B967987
theorem B2175511 : Blo 451781 2175511 := bstep (se 1 (by rfl) ⟨1631633, by rfl⟩ : syracuseStep 2175511 = 3263267) B3263267
theorem B766523 : Blo 451781 766523 := bstep (se 1 (by rfl) ⟨574892, by rfl⟩ : syracuseStep 766523 = 1149785) B1149785
theorem B5223203 : Blo 451781 5223203 := bstep (se 1 (by rfl) ⟨3917402, by rfl⟩ : syracuseStep 5223203 = 7834805) B7834805
theorem B865171 : Blo 451781 865171 := bstep (se 1 (by rfl) ⟨648878, by rfl⟩ : syracuseStep 865171 = 1297757) B1297757
theorem B1717145 : Blo 451781 1717145 := bstep (se 2 (by rfl) ⟨643929, by rfl⟩ : syracuseStep 1717145 = 1287859) B1287859
theorem B766921 : Blo 451781 766921 := bstep (se 2 (by rfl) ⟨287595, by rfl⟩ : syracuseStep 766921 = 575191) B575191
theorem B1291265 : Blo 451781 1291265 := bstep (se 2 (by rfl) ⟨484224, by rfl⟩ : syracuseStep 1291265 = 968449) B968449
theorem B1094791 : Blo 451781 1094791 := bstep (se 1 (by rfl) ⟨821093, by rfl⟩ : syracuseStep 1094791 = 1642187) B1642187
theorem B1946825 : Blo 451781 1946825 := bstep (se 2 (by rfl) ⟨730059, by rfl⟩ : syracuseStep 1946825 = 1460119) B1460119
theorem B1226017 : Blo 451781 1226017 := bstep (se 2 (by rfl) ⟨459756, by rfl⟩ : syracuseStep 1226017 = 919513) B919513
theorem B5158403 : Blo 451781 5158403 := bstep (se 1 (by rfl) ⟨3868802, by rfl⟩ : syracuseStep 5158403 = 7737605) B7737605
theorem B4404779 : Blo 451781 4404779 := bstep (se 1 (by rfl) ⟨3303584, by rfl⟩ : syracuseStep 4404779 = 6607169) B6607169
theorem B767623 : Blo 451781 767623 := bstep (se 1 (by rfl) ⟨575717, by rfl⟩ : syracuseStep 767623 = 1151435) B1151435
theorem B1226441 : Blo 451781 1226441 := bstep (se 2 (by rfl) ⟨459915, by rfl⟩ : syracuseStep 1226441 = 919831) B919831
theorem B1718131 : Blo 451781 1718131 := bstep (se 1 (by rfl) ⟨1288598, by rfl⟩ : syracuseStep 1718131 = 2577197) B2577197
theorem B1456019 : Blo 451781 1456019 := bstep (se 1 (by rfl) ⟨1092014, by rfl⟩ : syracuseStep 1456019 = 2184029) B2184029
theorem B1292233 : Blo 451781 1292233 := bstep (se 2 (by rfl) ⟨484587, by rfl⟩ : syracuseStep 1292233 = 969175) B969175
theorem B768271 : Blo 451781 768271 := bstep (se 1 (by rfl) ⟨576203, by rfl⟩ : syracuseStep 768271 = 1152407) B1152407
theorem B26589505 : Blo 451781 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B5519801 : Blo 451781 5519801 := bstep (se 2 (by rfl) ⟨2069925, by rfl⟩ : syracuseStep 5519801 = 4139851) B4139851
theorem B768811 : Blo 451781 768811 := bstep (se 1 (by rfl) ⟨576608, by rfl⟩ : syracuseStep 768811 = 1153217) B1153217
theorem B1489817 : Blo 451781 1489817 := bstep (se 2 (by rfl) ⟨558681, by rfl⟩ : syracuseStep 1489817 = 1117363) B1117363
theorem B768953 : Blo 451781 768953 := bstep (se 2 (by rfl) ⟨288357, by rfl⟩ : syracuseStep 768953 = 576715) B576715
theorem B1555499 : Blo 451781 1555499 := bstep (se 1 (by rfl) ⟨1166624, by rfl⟩ : syracuseStep 1555499 = 2333249) B2333249
theorem B2178355 : Blo 451781 2178355 := bstep (se 1 (by rfl) ⟨1633766, by rfl⟩ : syracuseStep 2178355 = 3267533) B3267533
theorem B1293839 : Blo 451781 1293839 := bstep (se 1 (by rfl) ⟨970379, by rfl⟩ : syracuseStep 1293839 = 1940759) B1940759
theorem B2178647 : Blo 451781 2178647 := bstep (se 1 (by rfl) ⟨1633985, by rfl⟩ : syracuseStep 2178647 = 3267971) B3267971
theorem B1720349 : Blo 451781 1720349 := bstep (se 3 (by rfl) ⟨322565, by rfl⟩ : syracuseStep 1720349 = 645131) B645131
theorem B966791 : Blo 451781 966791 := bstep (se 1 (by rfl) ⟨725093, by rfl⟩ : syracuseStep 966791 = 1450187) B1450187
theorem B1229089 : Blo 451781 1229089 := bstep (se 2 (by rfl) ⟨460908, by rfl⟩ : syracuseStep 1229089 = 921817) B921817
theorem B508423 : Blo 451781 508423 := bstep (se 1 (by rfl) ⟨381317, by rfl⟩ : syracuseStep 508423 = 762635) B762635
theorem B1982987 : Blo 451781 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B2769437 : Blo 451781 2769437 := bstep (se 3 (by rfl) ⟨519269, by rfl⟩ : syracuseStep 2769437 = 1038539) B1038539
theorem B1294967 : Blo 451781 1294967 := bstep (se 1 (by rfl) ⟨971225, by rfl⟩ : syracuseStep 1294967 = 1942451) B1942451
theorem B574123 : Blo 451781 574123 := bstep (se 1 (by rfl) ⟨430592, by rfl⟩ : syracuseStep 574123 = 861185) B861185
theorem B9814709 : Blo 451781 9814709 := bstep (se 5 (by rfl) ⟨460064, by rfl⟩ : syracuseStep 9814709 = 920129) B920129
theorem B508603 : Blo 451781 508603 := bstep (se 1 (by rfl) ⟨381452, by rfl⟩ : syracuseStep 508603 = 762905) B762905
theorem B1721033 : Blo 451781 1721033 := bstep (se 2 (by rfl) ⟨645387, by rfl⟩ : syracuseStep 1721033 = 1290775) B1290775
theorem B4735705 : Blo 451781 4735705 := bstep (se 2 (by rfl) ⟨1775889, by rfl⟩ : syracuseStep 4735705 = 3551779) B3551779
theorem B1524797 : Blo 451781 1524797 := bstep (se 3 (by rfl) ⟨285899, by rfl⟩ : syracuseStep 1524797 = 571799) B571799
theorem B509071 : Blo 451781 509071 := bstep (se 1 (by rfl) ⟨381803, by rfl⟩ : syracuseStep 509071 = 763607) B763607
theorem B935315 : Blo 451781 935315 := bstep (se 1 (by rfl) ⟨701486, by rfl⟩ : syracuseStep 935315 = 1402973) B1402973
theorem B1558027 : Blo 451781 1558027 := bstep (se 1 (by rfl) ⟨1168520, by rfl⟩ : syracuseStep 1558027 = 2337041) B2337041
theorem B575095 : Blo 451781 575095 := bstep (se 1 (by rfl) ⟨431321, by rfl⟩ : syracuseStep 575095 = 862643) B862643
theorem B509575 : Blo 451781 509575 := bstep (se 1 (by rfl) ⟨382181, by rfl⟩ : syracuseStep 509575 = 764363) B764363
theorem B509755 : Blo 451781 509755 := bstep (se 1 (by rfl) ⟨382316, by rfl⟩ : syracuseStep 509755 = 764633) B764633
theorem B4638617 : Blo 451781 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B575419 : Blo 451781 575419 := bstep (se 1 (by rfl) ⟨431564, by rfl⟩ : syracuseStep 575419 = 863129) B863129
theorem B1296641 : Blo 451781 1296641 := bstep (se 2 (by rfl) ⟨486240, by rfl⟩ : syracuseStep 1296641 = 972481) B972481
theorem B510223 : Blo 451781 510223 := bstep (se 1 (by rfl) ⟨382667, by rfl⟩ : syracuseStep 510223 = 765335) B765335
theorem B1296755 : Blo 451781 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B2574737 : Blo 451781 2574737 := bstep (se 2 (by rfl) ⟨965526, by rfl⟩ : syracuseStep 2574737 = 1931053) B1931053
theorem B1526201 : Blo 451781 1526201 := bstep (se 2 (by rfl) ⟨572325, by rfl⟩ : syracuseStep 1526201 = 1144651) B1144651
theorem B1722809 : Blo 451781 1722809 := bstep (se 2 (by rfl) ⟨646053, by rfl⟩ : syracuseStep 1722809 = 1292107) B1292107
theorem B1297097 : Blo 451781 1297097 := bstep (se 2 (by rfl) ⟨486411, by rfl⟩ : syracuseStep 1297097 = 972823) B972823
theorem B510727 : Blo 451781 510727 := bstep (se 1 (by rfl) ⟨383045, by rfl⟩ : syracuseStep 510727 = 766091) B766091
theorem B543547 : Blo 451781 543547 := bstep (se 1 (by rfl) ⟨407660, by rfl⟩ : syracuseStep 543547 = 815321) B815321
theorem B576391 : Blo 451781 576391 := bstep (se 1 (by rfl) ⟨432293, by rfl⟩ : syracuseStep 576391 = 864587) B864587
theorem B510907 : Blo 451781 510907 := bstep (se 1 (by rfl) ⟨383180, by rfl⟩ : syracuseStep 510907 = 766361) B766361
theorem B1526795 : Blo 451781 1526795 := bstep (se 1 (by rfl) ⟨1145096, by rfl⟩ : syracuseStep 1526795 = 2290193) B2290193
theorem B2575421 : Blo 451781 2575421 := bstep (se 3 (by rfl) ⟨482891, by rfl⟩ : syracuseStep 2575421 = 965783) B965783
theorem B1526903 : Blo 451781 1526903 := bstep (se 1 (by rfl) ⟨1145177, by rfl⟩ : syracuseStep 1526903 = 2290355) B2290355
theorem B773321 : Blo 451781 773321 := bstep (se 2 (by rfl) ⟨289995, by rfl⟩ : syracuseStep 773321 = 579991) B579991
theorem B576811 : Blo 451781 576811 := bstep (se 1 (by rfl) ⟨432608, by rfl⟩ : syracuseStep 576811 = 865217) B865217
theorem B17517869 : Blo 451781 17517869 := bstep (se 3 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 17517869 = 6569201) B6569201
theorem B63688037 : Blo 451781 63688037 := bstep (se 4 (by rfl) ⟨5970753, by rfl⟩ : syracuseStep 63688037 = 11941507) B11941507
theorem B511375 : Blo 451781 511375 := bstep (se 1 (by rfl) ⟨383531, by rfl⟩ : syracuseStep 511375 = 767063) B767063
theorem B2182585 : Blo 451781 2182585 := bstep (se 2 (by rfl) ⟨818469, by rfl⟩ : syracuseStep 2182585 = 1636939) B1636939
theorem B1527497 : Blo 451781 1527497 := bstep (se 2 (by rfl) ⟨572811, by rfl⟩ : syracuseStep 1527497 = 1145623) B1145623
theorem B872137 : Blo 451781 872137 := bstep (se 2 (by rfl) ⟨327051, by rfl⟩ : syracuseStep 872137 = 654103) B654103
theorem B511879 : Blo 451781 511879 := bstep (se 1 (by rfl) ⟨383909, by rfl⟩ : syracuseStep 511879 = 767819) B767819
theorem B2445203 : Blo 451781 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B512059 : Blo 451781 512059 := bstep (se 1 (by rfl) ⟨384044, by rfl⟩ : syracuseStep 512059 = 768089) B768089
theorem B1528199 : Blo 451781 1528199 := bstep (se 1 (by rfl) ⟨1146149, by rfl⟩ : syracuseStep 1528199 = 2292299) B2292299
theorem B7885297 : Blo 451781 7885297 := bstep (se 2 (by rfl) ⟨2956986, by rfl⟩ : syracuseStep 7885297 = 5913973) B5913973
theorem B512527 : Blo 451781 512527 := bstep (se 1 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 512527 = 768791) B768791
theorem B545339 : Blo 451781 545339 := bstep (se 1 (by rfl) ⟨409004, by rfl⟩ : syracuseStep 545339 = 818009) B818009
theorem B4346561 : Blo 451781 4346561 := bstep (se 2 (by rfl) ⟨1629960, by rfl⟩ : syracuseStep 4346561 = 3259921) B3259921
theorem B1528577 : Blo 451781 1528577 := bstep (se 2 (by rfl) ⟨573216, by rfl⟩ : syracuseStep 1528577 = 1146433) B1146433
theorem B3265433 : Blo 451781 3265433 := bstep (se 2 (by rfl) ⟨1224537, by rfl⟩ : syracuseStep 3265433 = 2449075) B2449075
theorem B644231 : Blo 451781 644231 := bstep (se 1 (by rfl) ⟨483173, by rfl⟩ : syracuseStep 644231 = 966347) B966347
theorem B545935 : Blo 451781 545935 := bstep (se 1 (by rfl) ⟨409451, by rfl⟩ : syracuseStep 545935 = 818903) B818903
theorem B644539 : Blo 451781 644539 := bstep (se 1 (by rfl) ⟨483404, by rfl⟩ : syracuseStep 644539 = 966809) B966809
theorem B1529387 : Blo 451781 1529387 := bstep (se 1 (by rfl) ⟨1147040, by rfl⟩ : syracuseStep 1529387 = 2294081) B2294081
theorem B677675 : Blo 451781 677675 := bstep (se 1 (by rfl) ⟨508256, by rfl⟩ : syracuseStep 677675 = 1016513) B1016513
theorem B612155 : Blo 451781 612155 := bstep (se 1 (by rfl) ⟨459116, by rfl⟩ : syracuseStep 612155 = 918233) B918233
theorem B677705 : Blo 451781 677705 := bstep (se 2 (by rfl) ⟨254139, by rfl⟩ : syracuseStep 677705 = 508279) B508279
theorem B1726393 : Blo 451781 1726393 := bstep (se 2 (by rfl) ⟨647397, by rfl⟩ : syracuseStep 1726393 = 1294795) B1294795
theorem B677819 : Blo 451781 677819 := bstep (se 1 (by rfl) ⟨508364, by rfl⟩ : syracuseStep 677819 = 1016729) B1016729
theorem B2185163 : Blo 451781 2185163 := bstep (se 1 (by rfl) ⟨1638872, by rfl⟩ : syracuseStep 2185163 = 3277745) B3277745
theorem B677879 : Blo 451781 677879 := bstep (se 1 (by rfl) ⟨508409, by rfl⟩ : syracuseStep 677879 = 1016819) B1016819
theorem B677903 : Blo 451781 677903 := bstep (se 1 (by rfl) ⟨508427, by rfl⟩ : syracuseStep 677903 = 1016855) B1016855
theorem B677945 : Blo 451781 677945 := bstep (se 2 (by rfl) ⟨254229, by rfl⟩ : syracuseStep 677945 = 508459) B508459
theorem B678023 : Blo 451781 678023 := bstep (se 1 (by rfl) ⟨508517, by rfl⟩ : syracuseStep 678023 = 1017035) B1017035
theorem B678059 : Blo 451781 678059 := bstep (se 1 (by rfl) ⟨508544, by rfl⟩ : syracuseStep 678059 = 1017089) B1017089
theorem B678089 : Blo 451781 678089 := bstep (se 2 (by rfl) ⟨254283, by rfl⟩ : syracuseStep 678089 = 508567) B508567
theorem B678203 : Blo 451781 678203 := bstep (se 1 (by rfl) ⟨508652, by rfl⟩ : syracuseStep 678203 = 1017305) B1017305
theorem B678263 : Blo 451781 678263 := bstep (se 1 (by rfl) ⟨508697, by rfl⟩ : syracuseStep 678263 = 1017395) B1017395
theorem B678287 : Blo 451781 678287 := bstep (se 1 (by rfl) ⟨508715, by rfl⟩ : syracuseStep 678287 = 1017431) B1017431
theorem B678329 : Blo 451781 678329 := bstep (se 2 (by rfl) ⟨254373, by rfl⟩ : syracuseStep 678329 = 508747) B508747
theorem B612793 : Blo 451781 612793 := bstep (se 2 (by rfl) ⟨229797, by rfl⟩ : syracuseStep 612793 = 459595) B459595
theorem B678407 : Blo 451781 678407 := bstep (se 1 (by rfl) ⟨508805, by rfl⟩ : syracuseStep 678407 = 1017611) B1017611
theorem B678443 : Blo 451781 678443 := bstep (se 1 (by rfl) ⟨508832, by rfl⟩ : syracuseStep 678443 = 1017665) B1017665
theorem B645689 : Blo 451781 645689 := bstep (se 2 (by rfl) ⟨242133, by rfl⟩ : syracuseStep 645689 = 484267) B484267
theorem B678473 : Blo 451781 678473 := bstep (se 2 (by rfl) ⟨254427, by rfl⟩ : syracuseStep 678473 = 508855) B508855
theorem B678587 : Blo 451781 678587 := bstep (se 1 (by rfl) ⟨508940, by rfl⟩ : syracuseStep 678587 = 1017881) B1017881
theorem B678647 : Blo 451781 678647 := bstep (se 1 (by rfl) ⟨508985, by rfl⟩ : syracuseStep 678647 = 1017971) B1017971
theorem B678671 : Blo 451781 678671 := bstep (se 1 (by rfl) ⟨509003, by rfl⟩ : syracuseStep 678671 = 1018007) B1018007
theorem B678713 : Blo 451781 678713 := bstep (se 2 (by rfl) ⟨254517, by rfl⟩ : syracuseStep 678713 = 509035) B509035
theorem B1530683 : Blo 451781 1530683 := bstep (se 1 (by rfl) ⟨1148012, by rfl⟩ : syracuseStep 1530683 = 2296025) B2296025
theorem B4414283 : Blo 451781 4414283 := bstep (se 1 (by rfl) ⟨3310712, by rfl⟩ : syracuseStep 4414283 = 6621425) B6621425
theorem B678791 : Blo 451781 678791 := bstep (se 1 (by rfl) ⟨509093, by rfl⟩ : syracuseStep 678791 = 1018187) B1018187
theorem B678827 : Blo 451781 678827 := bstep (se 1 (by rfl) ⟨509120, by rfl⟩ : syracuseStep 678827 = 1018241) B1018241
theorem B678857 : Blo 451781 678857 := bstep (se 2 (by rfl) ⟨254571, by rfl⟩ : syracuseStep 678857 = 509143) B509143
theorem B678971 : Blo 451781 678971 := bstep (se 1 (by rfl) ⟨509228, by rfl⟩ : syracuseStep 678971 = 1018457) B1018457
theorem B679031 : Blo 451781 679031 := bstep (se 1 (by rfl) ⟨509273, by rfl⟩ : syracuseStep 679031 = 1018547) B1018547
theorem B679055 : Blo 451781 679055 := bstep (se 1 (by rfl) ⟨509291, by rfl⟩ : syracuseStep 679055 = 1018583) B1018583
theorem B679097 : Blo 451781 679097 := bstep (se 2 (by rfl) ⟨254661, by rfl⟩ : syracuseStep 679097 = 509323) B509323
theorem B679175 : Blo 451781 679175 := bstep (se 1 (by rfl) ⟨509381, by rfl⟩ : syracuseStep 679175 = 1018763) B1018763
theorem B1531169 : Blo 451781 1531169 := bstep (se 2 (by rfl) ⟨574188, by rfl⟩ : syracuseStep 1531169 = 1148377) B1148377
theorem B679211 : Blo 451781 679211 := bstep (se 1 (by rfl) ⟨509408, by rfl⟩ : syracuseStep 679211 = 1018817) B1018817
theorem B14179643 : Blo 451781 14179643 := bstep (se 1 (by rfl) ⟨10634732, by rfl⟩ : syracuseStep 14179643 = 21269465) B21269465
theorem B3366203 : Blo 451781 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B679241 : Blo 451781 679241 := bstep (se 2 (by rfl) ⟨254715, by rfl⟩ : syracuseStep 679241 = 509431) B509431
theorem B679355 : Blo 451781 679355 := bstep (se 1 (by rfl) ⟨509516, by rfl⟩ : syracuseStep 679355 = 1019033) B1019033
theorem B679415 : Blo 451781 679415 := bstep (se 1 (by rfl) ⟨509561, by rfl⟩ : syracuseStep 679415 = 1019123) B1019123
theorem B679439 : Blo 451781 679439 := bstep (se 1 (by rfl) ⟨509579, by rfl⟩ : syracuseStep 679439 = 1019159) B1019159
theorem B679481 : Blo 451781 679481 := bstep (se 2 (by rfl) ⟨254805, by rfl⟩ : syracuseStep 679481 = 509611) B509611
theorem B2186813 : Blo 451781 2186813 := bstep (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) B820055
theorem B679559 : Blo 451781 679559 := bstep (se 1 (by rfl) ⟨509669, by rfl⟩ : syracuseStep 679559 = 1019339) B1019339
theorem B679595 : Blo 451781 679595 := bstep (se 1 (by rfl) ⟨509696, by rfl⟩ : syracuseStep 679595 = 1019393) B1019393
theorem B679625 : Blo 451781 679625 := bstep (se 2 (by rfl) ⟨254859, by rfl⟩ : syracuseStep 679625 = 509719) B509719
theorem B483131 : Blo 451781 483131 := bstep (se 1 (by rfl) ⟨362348, by rfl⟩ : syracuseStep 483131 = 724697) B724697
theorem B679739 : Blo 451781 679739 := bstep (se 1 (by rfl) ⟨509804, by rfl⟩ : syracuseStep 679739 = 1019609) B1019609
theorem B1531763 : Blo 451781 1531763 := bstep (se 1 (by rfl) ⟨1148822, by rfl⟩ : syracuseStep 1531763 = 2297645) B2297645
theorem B679799 : Blo 451781 679799 := bstep (se 1 (by rfl) ⟨509849, by rfl⟩ : syracuseStep 679799 = 1019699) B1019699
theorem B679823 : Blo 451781 679823 := bstep (se 1 (by rfl) ⟨509867, by rfl⟩ : syracuseStep 679823 = 1019735) B1019735
theorem B2187161 : Blo 451781 2187161 := bstep (se 2 (by rfl) ⟨820185, by rfl⟩ : syracuseStep 2187161 = 1640371) B1640371
theorem B679865 : Blo 451781 679865 := bstep (se 2 (by rfl) ⟨254949, by rfl⟩ : syracuseStep 679865 = 509899) B509899
theorem B679943 : Blo 451781 679943 := bstep (se 1 (by rfl) ⟨509957, by rfl⟩ : syracuseStep 679943 = 1019915) B1019915
theorem B679979 : Blo 451781 679979 := bstep (se 1 (by rfl) ⟨509984, by rfl⟩ : syracuseStep 679979 = 1019969) B1019969
theorem B647227 : Blo 451781 647227 := bstep (se 1 (by rfl) ⟨485420, by rfl⟩ : syracuseStep 647227 = 970841) B970841
theorem B680009 : Blo 451781 680009 := bstep (se 2 (by rfl) ⟨255003, by rfl⟩ : syracuseStep 680009 = 510007) B510007
theorem B680123 : Blo 451781 680123 := bstep (se 1 (by rfl) ⟨510092, by rfl⟩ : syracuseStep 680123 = 1020185) B1020185
theorem B680183 : Blo 451781 680183 := bstep (se 1 (by rfl) ⟨510137, by rfl⟩ : syracuseStep 680183 = 1020275) B1020275
theorem B680207 : Blo 451781 680207 := bstep (se 1 (by rfl) ⟨510155, by rfl⟩ : syracuseStep 680207 = 1020311) B1020311
theorem B680249 : Blo 451781 680249 := bstep (se 2 (by rfl) ⟨255093, by rfl⟩ : syracuseStep 680249 = 510187) B510187
theorem B680327 : Blo 451781 680327 := bstep (se 1 (by rfl) ⟨510245, by rfl⟩ : syracuseStep 680327 = 1020491) B1020491
theorem B680363 : Blo 451781 680363 := bstep (se 1 (by rfl) ⟨510272, by rfl⟩ : syracuseStep 680363 = 1020545) B1020545
theorem B680393 : Blo 451781 680393 := bstep (se 2 (by rfl) ⟨255147, by rfl⟩ : syracuseStep 680393 = 510295) B510295
theorem B647671 : Blo 451781 647671 := bstep (se 1 (by rfl) ⟨485753, by rfl⟩ : syracuseStep 647671 = 971507) B971507
theorem B680507 : Blo 451781 680507 := bstep (se 1 (by rfl) ⟨510380, by rfl⟩ : syracuseStep 680507 = 1020761) B1020761
theorem B680567 : Blo 451781 680567 := bstep (se 1 (by rfl) ⟨510425, by rfl⟩ : syracuseStep 680567 = 1020851) B1020851
theorem B680591 : Blo 451781 680591 := bstep (se 1 (by rfl) ⟨510443, by rfl⟩ : syracuseStep 680591 = 1020887) B1020887
theorem B680633 : Blo 451781 680633 := bstep (se 2 (by rfl) ⟨255237, by rfl⟩ : syracuseStep 680633 = 510475) B510475
theorem B680711 : Blo 451781 680711 := bstep (se 1 (by rfl) ⟨510533, by rfl⟩ : syracuseStep 680711 = 1021067) B1021067
theorem B1729295 : Blo 451781 1729295 := bstep (se 1 (by rfl) ⟨1296971, by rfl⟩ : syracuseStep 1729295 = 2593943) B2593943
theorem B680747 : Blo 451781 680747 := bstep (se 1 (by rfl) ⟨510560, by rfl⟩ : syracuseStep 680747 = 1021121) B1021121
theorem B680777 : Blo 451781 680777 := bstep (se 2 (by rfl) ⟨255291, by rfl⟩ : syracuseStep 680777 = 510583) B510583
theorem B680891 : Blo 451781 680891 := bstep (se 1 (by rfl) ⟨510668, by rfl⟩ : syracuseStep 680891 = 1021337) B1021337
theorem B680951 : Blo 451781 680951 := bstep (se 1 (by rfl) ⟨510713, by rfl⟩ : syracuseStep 680951 = 1021427) B1021427
theorem B680975 : Blo 451781 680975 := bstep (se 1 (by rfl) ⟨510731, by rfl⟩ : syracuseStep 680975 = 1021463) B1021463
theorem B681017 : Blo 451781 681017 := bstep (se 2 (by rfl) ⟨255381, by rfl⟩ : syracuseStep 681017 = 510763) B510763
theorem B2581571 : Blo 451781 2581571 := bstep (se 1 (by rfl) ⟨1936178, by rfl⟩ : syracuseStep 2581571 = 3872357) B3872357
theorem B681095 : Blo 451781 681095 := bstep (se 1 (by rfl) ⟨510821, by rfl⟩ : syracuseStep 681095 = 1021643) B1021643
theorem B681131 : Blo 451781 681131 := bstep (se 1 (by rfl) ⟨510848, by rfl⟩ : syracuseStep 681131 = 1021697) B1021697
theorem B681161 : Blo 451781 681161 := bstep (se 2 (by rfl) ⟨255435, by rfl⟩ : syracuseStep 681161 = 510871) B510871
theorem B451847 : Blo 451781 451847 := bstep (se 1 (by rfl) ⟨338885, by rfl⟩ : syracuseStep 451847 = 677771) B677771
theorem B451855 : Blo 451781 451855 := bstep (se 1 (by rfl) ⟨338891, by rfl⟩ : syracuseStep 451855 = 677783) B677783
theorem B746767 : Blo 451781 746767 := bstep (se 1 (by rfl) ⟨560075, by rfl⟩ : syracuseStep 746767 = 1120151) B1120151
theorem B648491 : Blo 451781 648491 := bstep (se 1 (by rfl) ⟨486368, by rfl⟩ : syracuseStep 648491 = 972737) B972737
theorem B451899 : Blo 451781 451899 := bstep (se 1 (by rfl) ⟨338924, by rfl⟩ : syracuseStep 451899 = 677849) B677849
theorem B681275 : Blo 451781 681275 := bstep (se 1 (by rfl) ⟨510956, by rfl⟩ : syracuseStep 681275 = 1021913) B1021913
theorem B681335 : Blo 451781 681335 := bstep (se 1 (by rfl) ⟨511001, by rfl⟩ : syracuseStep 681335 = 1022003) B1022003
theorem B451975 : Blo 451781 451975 := bstep (se 1 (by rfl) ⟨338981, by rfl⟩ : syracuseStep 451975 = 677963) B677963
theorem B451983 : Blo 451781 451983 := bstep (se 1 (by rfl) ⟨338987, by rfl⟩ : syracuseStep 451983 = 677975) B677975
theorem B681359 : Blo 451781 681359 := bstep (se 1 (by rfl) ⟨511019, by rfl⟩ : syracuseStep 681359 = 1022039) B1022039
theorem B681401 : Blo 451781 681401 := bstep (se 2 (by rfl) ⟨255525, by rfl⟩ : syracuseStep 681401 = 511051) B511051
theorem B8742329 : Blo 451781 8742329 := bstep (se 2 (by rfl) ⟨3278373, by rfl⟩ : syracuseStep 8742329 = 6556747) B6556747
theorem B452027 : Blo 451781 452027 := bstep (se 1 (by rfl) ⟨339020, by rfl⟩ : syracuseStep 452027 = 678041) B678041
theorem B452103 : Blo 451781 452103 := bstep (se 1 (by rfl) ⟨339077, by rfl⟩ : syracuseStep 452103 = 678155) B678155
theorem B681479 : Blo 451781 681479 := bstep (se 1 (by rfl) ⟨511109, by rfl⟩ : syracuseStep 681479 = 1022219) B1022219
theorem B2582027 : Blo 451781 2582027 := bstep (se 1 (by rfl) ⟨1936520, by rfl⟩ : syracuseStep 2582027 = 3873041) B3873041
theorem B452111 : Blo 451781 452111 := bstep (se 1 (by rfl) ⟨339083, by rfl⟩ : syracuseStep 452111 = 678167) B678167
theorem B681515 : Blo 451781 681515 := bstep (se 1 (by rfl) ⟨511136, by rfl⟩ : syracuseStep 681515 = 1022273) B1022273
theorem B452155 : Blo 451781 452155 := bstep (se 1 (by rfl) ⟨339116, by rfl⟩ : syracuseStep 452155 = 678233) B678233
theorem B1402429 : Blo 451781 1402429 := bstep (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) B525911
theorem B681545 : Blo 451781 681545 := bstep (se 2 (by rfl) ⟨255579, by rfl⟩ : syracuseStep 681545 = 511159) B511159
theorem B6514253 : Blo 451781 6514253 := bstep (se 3 (by rfl) ⟨1221422, by rfl⟩ : syracuseStep 6514253 = 2442845) B2442845
theorem B452231 : Blo 451781 452231 := bstep (se 1 (by rfl) ⟨339173, by rfl⟩ : syracuseStep 452231 = 678347) B678347
theorem B452239 : Blo 451781 452239 := bstep (se 1 (by rfl) ⟨339179, by rfl⟩ : syracuseStep 452239 = 678359) B678359
theorem B2287277 : Blo 451781 2287277 := bstep (se 3 (by rfl) ⟨428864, by rfl⟩ : syracuseStep 2287277 = 857729) B857729
theorem B452283 : Blo 451781 452283 := bstep (se 1 (by rfl) ⟨339212, by rfl⟩ : syracuseStep 452283 = 678425) B678425
theorem B681659 : Blo 451781 681659 := bstep (se 1 (by rfl) ⟨511244, by rfl⟩ : syracuseStep 681659 = 1022489) B1022489
theorem B1631981 : Blo 451781 1631981 := bstep (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) B611993
theorem B681719 : Blo 451781 681719 := bstep (se 1 (by rfl) ⟨511289, by rfl⟩ : syracuseStep 681719 = 1022579) B1022579
theorem B6219521 : Blo 451781 6219521 := bstep (se 2 (by rfl) ⟨2332320, by rfl⟩ : syracuseStep 6219521 = 4664641) B4664641
theorem B452359 : Blo 451781 452359 := bstep (se 1 (by rfl) ⟨339269, by rfl⟩ : syracuseStep 452359 = 678539) B678539
theorem B452367 : Blo 451781 452367 := bstep (se 1 (by rfl) ⟨339275, by rfl⟩ : syracuseStep 452367 = 678551) B678551
theorem B681743 : Blo 451781 681743 := bstep (se 1 (by rfl) ⟨511307, by rfl⟩ : syracuseStep 681743 = 1022615) B1022615
theorem B681785 : Blo 451781 681785 := bstep (se 2 (by rfl) ⟨255669, by rfl⟩ : syracuseStep 681785 = 511339) B511339
theorem B452411 : Blo 451781 452411 := bstep (se 1 (by rfl) ⟨339308, by rfl⟩ : syracuseStep 452411 = 678617) B678617
theorem B452487 : Blo 451781 452487 := bstep (se 1 (by rfl) ⟨339365, by rfl⟩ : syracuseStep 452487 = 678731) B678731
theorem B681863 : Blo 451781 681863 := bstep (se 1 (by rfl) ⟨511397, by rfl⟩ : syracuseStep 681863 = 1022795) B1022795
theorem B452495 : Blo 451781 452495 := bstep (se 1 (by rfl) ⟨339371, by rfl⟩ : syracuseStep 452495 = 678743) B678743
theorem B681899 : Blo 451781 681899 := bstep (se 1 (by rfl) ⟨511424, by rfl⟩ : syracuseStep 681899 = 1022849) B1022849
theorem B452539 : Blo 451781 452539 := bstep (se 1 (by rfl) ⟨339404, by rfl⟩ : syracuseStep 452539 = 678809) B678809
theorem B681929 : Blo 451781 681929 := bstep (se 2 (by rfl) ⟨255723, by rfl⟩ : syracuseStep 681929 = 511447) B511447
theorem B452615 : Blo 451781 452615 := bstep (se 1 (by rfl) ⟨339461, by rfl⟩ : syracuseStep 452615 = 678923) B678923
theorem B452623 : Blo 451781 452623 := bstep (se 1 (by rfl) ⟨339467, by rfl⟩ : syracuseStep 452623 = 678935) B678935
theorem B452667 : Blo 451781 452667 := bstep (se 1 (by rfl) ⟨339500, by rfl⟩ : syracuseStep 452667 = 679001) B679001
theorem B682043 : Blo 451781 682043 := bstep (se 1 (by rfl) ⟨511532, by rfl⟩ : syracuseStep 682043 = 1023065) B1023065
theorem B682103 : Blo 451781 682103 := bstep (se 1 (by rfl) ⟨511577, by rfl⟩ : syracuseStep 682103 = 1023155) B1023155
theorem B452743 : Blo 451781 452743 := bstep (se 1 (by rfl) ⟨339557, by rfl⟩ : syracuseStep 452743 = 679115) B679115
theorem B452751 : Blo 451781 452751 := bstep (se 1 (by rfl) ⟨339563, by rfl⟩ : syracuseStep 452751 = 679127) B679127
theorem B682127 : Blo 451781 682127 := bstep (se 1 (by rfl) ⟨511595, by rfl⟩ : syracuseStep 682127 = 1023191) B1023191
theorem B682169 : Blo 451781 682169 := bstep (se 2 (by rfl) ⟨255813, by rfl⟩ : syracuseStep 682169 = 511627) B511627
theorem B452795 : Blo 451781 452795 := bstep (se 1 (by rfl) ⟨339596, by rfl⟩ : syracuseStep 452795 = 679193) B679193
theorem B452871 : Blo 451781 452871 := bstep (se 1 (by rfl) ⟨339653, by rfl⟩ : syracuseStep 452871 = 679307) B679307
theorem B682247 : Blo 451781 682247 := bstep (se 1 (by rfl) ⟨511685, by rfl⟩ : syracuseStep 682247 = 1023371) B1023371
theorem B452879 : Blo 451781 452879 := bstep (se 1 (by rfl) ⟨339659, by rfl⟩ : syracuseStep 452879 = 679319) B679319
theorem B682283 : Blo 451781 682283 := bstep (se 1 (by rfl) ⟨511712, by rfl⟩ : syracuseStep 682283 = 1023425) B1023425
theorem B452923 : Blo 451781 452923 := bstep (se 1 (by rfl) ⟨339692, by rfl⟩ : syracuseStep 452923 = 679385) B679385
theorem B682313 : Blo 451781 682313 := bstep (se 2 (by rfl) ⟨255867, by rfl⟩ : syracuseStep 682313 = 511735) B511735
theorem B452999 : Blo 451781 452999 := bstep (se 1 (by rfl) ⟨339749, by rfl⟩ : syracuseStep 452999 = 679499) B679499
theorem B453007 : Blo 451781 453007 := bstep (se 1 (by rfl) ⟨339755, by rfl⟩ : syracuseStep 453007 = 679511) B679511
theorem B1534355 : Blo 451781 1534355 := bstep (se 1 (by rfl) ⟨1150766, by rfl⟩ : syracuseStep 1534355 = 2301533) B2301533
theorem B453051 : Blo 451781 453051 := bstep (se 1 (by rfl) ⟨339788, by rfl⟩ : syracuseStep 453051 = 679577) B679577
theorem B682427 : Blo 451781 682427 := bstep (se 1 (by rfl) ⟨511820, by rfl⟩ : syracuseStep 682427 = 1023641) B1023641
theorem B3860945 : Blo 451781 3860945 := bstep (se 2 (by rfl) ⟨1447854, by rfl⟩ : syracuseStep 3860945 = 2895709) B2895709
theorem B682487 : Blo 451781 682487 := bstep (se 1 (by rfl) ⟨511865, by rfl⟩ : syracuseStep 682487 = 1023731) B1023731
theorem B453127 : Blo 451781 453127 := bstep (se 1 (by rfl) ⟨339845, by rfl⟩ : syracuseStep 453127 = 679691) B679691
theorem B453135 : Blo 451781 453135 := bstep (se 1 (by rfl) ⟨339851, by rfl⟩ : syracuseStep 453135 = 679703) B679703
theorem B682511 : Blo 451781 682511 := bstep (se 1 (by rfl) ⟨511883, by rfl⟩ : syracuseStep 682511 = 1023767) B1023767
theorem B682553 : Blo 451781 682553 := bstep (se 2 (by rfl) ⟨255957, by rfl⟩ : syracuseStep 682553 = 511915) B511915
theorem B453179 : Blo 451781 453179 := bstep (se 1 (by rfl) ⟨339884, by rfl⟩ : syracuseStep 453179 = 679769) B679769
theorem B453255 : Blo 451781 453255 := bstep (se 1 (by rfl) ⟨339941, by rfl⟩ : syracuseStep 453255 = 679883) B679883
theorem B682631 : Blo 451781 682631 := bstep (se 1 (by rfl) ⟨511973, by rfl⟩ : syracuseStep 682631 = 1023947) B1023947
theorem B453263 : Blo 451781 453263 := bstep (se 1 (by rfl) ⟨339947, by rfl⟩ : syracuseStep 453263 = 679895) B679895
theorem B682667 : Blo 451781 682667 := bstep (se 1 (by rfl) ⟨512000, by rfl⟩ : syracuseStep 682667 = 1024001) B1024001
theorem B453307 : Blo 451781 453307 := bstep (se 1 (by rfl) ⟨339980, by rfl⟩ : syracuseStep 453307 = 679961) B679961
theorem B682697 : Blo 451781 682697 := bstep (se 2 (by rfl) ⟨256011, by rfl⟩ : syracuseStep 682697 = 512023) B512023
theorem B3304165 : Blo 451781 3304165 := bstep (se 4 (by rfl) ⟨309765, by rfl⟩ : syracuseStep 3304165 = 619531) B619531
theorem B453383 : Blo 451781 453383 := bstep (se 1 (by rfl) ⟨340037, by rfl⟩ : syracuseStep 453383 = 680075) B680075
theorem B453391 : Blo 451781 453391 := bstep (se 1 (by rfl) ⟨340043, by rfl⟩ : syracuseStep 453391 = 680087) B680087
theorem B453435 : Blo 451781 453435 := bstep (se 1 (by rfl) ⟨340076, by rfl⟩ : syracuseStep 453435 = 680153) B680153
theorem B682811 : Blo 451781 682811 := bstep (se 1 (by rfl) ⟨512108, by rfl⟩ : syracuseStep 682811 = 1024217) B1024217
theorem B682871 : Blo 451781 682871 := bstep (se 1 (by rfl) ⟨512153, by rfl⟩ : syracuseStep 682871 = 1024307) B1024307
theorem B453511 : Blo 451781 453511 := bstep (se 1 (by rfl) ⟨340133, by rfl⟩ : syracuseStep 453511 = 680267) B680267
theorem B453519 : Blo 451781 453519 := bstep (se 1 (by rfl) ⟨340139, by rfl⟩ : syracuseStep 453519 = 680279) B680279
theorem B682895 : Blo 451781 682895 := bstep (se 1 (by rfl) ⟨512171, by rfl⟩ : syracuseStep 682895 = 1024343) B1024343
theorem B682937 : Blo 451781 682937 := bstep (se 2 (by rfl) ⟨256101, by rfl⟩ : syracuseStep 682937 = 512203) B512203
theorem B453563 : Blo 451781 453563 := bstep (se 1 (by rfl) ⟨340172, by rfl⟩ : syracuseStep 453563 = 680345) B680345
theorem B453639 : Blo 451781 453639 := bstep (se 1 (by rfl) ⟨340229, by rfl⟩ : syracuseStep 453639 = 680459) B680459
theorem B683015 : Blo 451781 683015 := bstep (se 1 (by rfl) ⟨512261, by rfl⟩ : syracuseStep 683015 = 1024523) B1024523
theorem B453647 : Blo 451781 453647 := bstep (se 1 (by rfl) ⟨340235, by rfl⟩ : syracuseStep 453647 = 680471) B680471
theorem B683051 : Blo 451781 683051 := bstep (se 1 (by rfl) ⟨512288, by rfl⟩ : syracuseStep 683051 = 1024577) B1024577
theorem B453691 : Blo 451781 453691 := bstep (se 1 (by rfl) ⟨340268, by rfl⟩ : syracuseStep 453691 = 680537) B680537
theorem B683081 : Blo 451781 683081 := bstep (se 2 (by rfl) ⟨256155, by rfl⟩ : syracuseStep 683081 = 512311) B512311
theorem B453767 : Blo 451781 453767 := bstep (se 1 (by rfl) ⟨340325, by rfl⟩ : syracuseStep 453767 = 680651) B680651
theorem B453775 : Blo 451781 453775 := bstep (se 1 (by rfl) ⟨340331, by rfl⟩ : syracuseStep 453775 = 680663) B680663
theorem B453819 : Blo 451781 453819 := bstep (se 1 (by rfl) ⟨340364, by rfl⟩ : syracuseStep 453819 = 680729) B680729
theorem B683195 : Blo 451781 683195 := bstep (se 1 (by rfl) ⟨512396, by rfl⟩ : syracuseStep 683195 = 1024793) B1024793
theorem B683255 : Blo 451781 683255 := bstep (se 1 (by rfl) ⟨512441, by rfl⟩ : syracuseStep 683255 = 1024883) B1024883
theorem B2288897 : Blo 451781 2288897 := bstep (se 2 (by rfl) ⟨858336, by rfl⟩ : syracuseStep 2288897 = 1716673) B1716673
theorem B453895 : Blo 451781 453895 := bstep (se 1 (by rfl) ⟨340421, by rfl⟩ : syracuseStep 453895 = 680843) B680843
theorem B453903 : Blo 451781 453903 := bstep (se 1 (by rfl) ⟨340427, by rfl⟩ : syracuseStep 453903 = 680855) B680855
theorem B683279 : Blo 451781 683279 := bstep (se 1 (by rfl) ⟨512459, by rfl⟩ : syracuseStep 683279 = 1024919) B1024919
theorem B683321 : Blo 451781 683321 := bstep (se 2 (by rfl) ⟨256245, by rfl⟩ : syracuseStep 683321 = 512491) B512491
theorem B453947 : Blo 451781 453947 := bstep (se 1 (by rfl) ⟨340460, by rfl⟩ : syracuseStep 453947 = 680921) B680921
theorem B454023 : Blo 451781 454023 := bstep (se 1 (by rfl) ⟨340517, by rfl⟩ : syracuseStep 454023 = 681035) B681035
theorem B683399 : Blo 451781 683399 := bstep (se 1 (by rfl) ⟨512549, by rfl⟩ : syracuseStep 683399 = 1025099) B1025099
theorem B454031 : Blo 451781 454031 := bstep (se 1 (by rfl) ⟨340523, by rfl⟩ : syracuseStep 454031 = 681047) B681047
theorem B683435 : Blo 451781 683435 := bstep (se 1 (by rfl) ⟨512576, by rfl⟩ : syracuseStep 683435 = 1025153) B1025153
theorem B454075 : Blo 451781 454075 := bstep (se 1 (by rfl) ⟨340556, by rfl⟩ : syracuseStep 454075 = 681113) B681113
theorem B683465 : Blo 451781 683465 := bstep (se 2 (by rfl) ⟨256299, by rfl⟩ : syracuseStep 683465 = 512599) B512599
theorem B454151 : Blo 451781 454151 := bstep (se 1 (by rfl) ⟨340613, by rfl⟩ : syracuseStep 454151 = 681227) B681227
theorem B814607 : Blo 451781 814607 := bstep (se 1 (by rfl) ⟨610955, by rfl⟩ : syracuseStep 814607 = 1221911) B1221911
theorem B454159 : Blo 451781 454159 := bstep (se 1 (by rfl) ⟨340619, by rfl⟩ : syracuseStep 454159 = 681239) B681239
theorem B3108395 : Blo 451781 3108395 := bstep (se 1 (by rfl) ⟨2331296, by rfl⟩ : syracuseStep 3108395 = 4662593) B4662593
theorem B454203 : Blo 451781 454203 := bstep (se 1 (by rfl) ⟨340652, by rfl⟩ : syracuseStep 454203 = 681305) B681305
theorem B683579 : Blo 451781 683579 := bstep (se 1 (by rfl) ⟨512684, by rfl⟩ : syracuseStep 683579 = 1025369) B1025369
theorem B683639 : Blo 451781 683639 := bstep (se 1 (by rfl) ⟨512729, by rfl⟩ : syracuseStep 683639 = 1025459) B1025459
theorem B454279 : Blo 451781 454279 := bstep (se 1 (by rfl) ⟨340709, by rfl⟩ : syracuseStep 454279 = 681419) B681419
theorem B454287 : Blo 451781 454287 := bstep (se 1 (by rfl) ⟨340715, by rfl⟩ : syracuseStep 454287 = 681431) B681431
theorem B683663 : Blo 451781 683663 := bstep (se 1 (by rfl) ⟨512747, by rfl⟩ : syracuseStep 683663 = 1025495) B1025495
theorem B454331 : Blo 451781 454331 := bstep (se 1 (by rfl) ⟨340748, by rfl⟩ : syracuseStep 454331 = 681497) B681497
theorem B454407 : Blo 451781 454407 := bstep (se 1 (by rfl) ⟨340805, by rfl⟩ : syracuseStep 454407 = 681611) B681611
theorem B454415 : Blo 451781 454415 := bstep (se 1 (by rfl) ⟨340811, by rfl⟩ : syracuseStep 454415 = 681623) B681623
theorem B1535759 : Blo 451781 1535759 := bstep (se 1 (by rfl) ⟨1151819, by rfl⟩ : syracuseStep 1535759 = 2303639) B2303639
theorem B454459 : Blo 451781 454459 := bstep (se 1 (by rfl) ⟨340844, by rfl⟩ : syracuseStep 454459 = 681689) B681689
theorem B9826123 : Blo 451781 9826123 := bstep (se 1 (by rfl) ⟨7369592, by rfl⟩ : syracuseStep 9826123 = 14739185) B14739185
theorem B454535 : Blo 451781 454535 := bstep (se 1 (by rfl) ⟨340901, by rfl⟩ : syracuseStep 454535 = 681803) B681803
theorem B454543 : Blo 451781 454543 := bstep (se 1 (by rfl) ⟨340907, by rfl⟩ : syracuseStep 454543 = 681815) B681815
theorem B454587 : Blo 451781 454587 := bstep (se 1 (by rfl) ⟨340940, by rfl⟩ : syracuseStep 454587 = 681881) B681881
theorem B454663 : Blo 451781 454663 := bstep (se 1 (by rfl) ⟨340997, by rfl⟩ : syracuseStep 454663 = 681995) B681995
theorem B454671 : Blo 451781 454671 := bstep (se 1 (by rfl) ⟨341003, by rfl⟩ : syracuseStep 454671 = 682007) B682007
theorem B1536029 : Blo 451781 1536029 := bstep (se 3 (by rfl) ⟨288005, by rfl⟩ : syracuseStep 1536029 = 576011) B576011
theorem B2289707 : Blo 451781 2289707 := bstep (se 1 (by rfl) ⟨1717280, by rfl⟩ : syracuseStep 2289707 = 3434561) B3434561
theorem B454715 : Blo 451781 454715 := bstep (se 1 (by rfl) ⟨341036, by rfl⟩ : syracuseStep 454715 = 682073) B682073
theorem B454791 : Blo 451781 454791 := bstep (se 1 (by rfl) ⟨341093, by rfl⟩ : syracuseStep 454791 = 682187) B682187
theorem B454799 : Blo 451781 454799 := bstep (se 1 (by rfl) ⟨341099, by rfl⟩ : syracuseStep 454799 = 682199) B682199
theorem B454843 : Blo 451781 454843 := bstep (se 1 (by rfl) ⟨341132, by rfl⟩ : syracuseStep 454843 = 682265) B682265
theorem B4354249 : Blo 451781 4354249 := bstep (se 2 (by rfl) ⟨1632843, by rfl⟩ : syracuseStep 4354249 = 3265687) B3265687
theorem B454919 : Blo 451781 454919 := bstep (se 1 (by rfl) ⟨341189, by rfl⟩ : syracuseStep 454919 = 682379) B682379
theorem B454927 : Blo 451781 454927 := bstep (se 1 (by rfl) ⟨341195, by rfl⟩ : syracuseStep 454927 = 682391) B682391
theorem B454971 : Blo 451781 454971 := bstep (se 1 (by rfl) ⟨341228, by rfl⟩ : syracuseStep 454971 = 682457) B682457
theorem B455047 : Blo 451781 455047 := bstep (se 1 (by rfl) ⟨341285, by rfl⟩ : syracuseStep 455047 = 682571) B682571
theorem B455055 : Blo 451781 455055 := bstep (se 1 (by rfl) ⟨341291, by rfl⟩ : syracuseStep 455055 = 682583) B682583
theorem B16576913 : Blo 451781 16576913 := bstep (se 2 (by rfl) ⟨6216342, by rfl⟩ : syracuseStep 16576913 = 12432685) B12432685
theorem B455099 : Blo 451781 455099 := bstep (se 1 (by rfl) ⟨341324, by rfl⟩ : syracuseStep 455099 = 682649) B682649
theorem B455175 : Blo 451781 455175 := bstep (se 1 (by rfl) ⟨341381, by rfl⟩ : syracuseStep 455175 = 682763) B682763
theorem B455183 : Blo 451781 455183 := bstep (se 1 (by rfl) ⟨341387, by rfl⟩ : syracuseStep 455183 = 682775) B682775
theorem B455227 : Blo 451781 455227 := bstep (se 1 (by rfl) ⟨341420, by rfl⟩ : syracuseStep 455227 = 682841) B682841
theorem B455303 : Blo 451781 455303 := bstep (se 1 (by rfl) ⟨341477, by rfl⟩ : syracuseStep 455303 = 682955) B682955
theorem B455311 : Blo 451781 455311 := bstep (se 1 (by rfl) ⟨341483, by rfl⟩ : syracuseStep 455311 = 682967) B682967
theorem B455355 : Blo 451781 455355 := bstep (se 1 (by rfl) ⟨341516, by rfl⟩ : syracuseStep 455355 = 683033) B683033
theorem B455431 : Blo 451781 455431 := bstep (se 1 (by rfl) ⟨341573, by rfl⟩ : syracuseStep 455431 = 683147) B683147
theorem B455439 : Blo 451781 455439 := bstep (se 1 (by rfl) ⟨341579, by rfl⟩ : syracuseStep 455439 = 683159) B683159
theorem B5796643 : Blo 451781 5796643 := bstep (se 1 (by rfl) ⟨4347482, by rfl⟩ : syracuseStep 5796643 = 8694965) B8694965
theorem B455483 : Blo 451781 455483 := bstep (se 1 (by rfl) ⟨341612, by rfl⟩ : syracuseStep 455483 = 683225) B683225
theorem B455559 : Blo 451781 455559 := bstep (se 1 (by rfl) ⟨341669, by rfl⟩ : syracuseStep 455559 = 683339) B683339
theorem B455567 : Blo 451781 455567 := bstep (se 1 (by rfl) ⟨341675, by rfl⟩ : syracuseStep 455567 = 683351) B683351
theorem B455611 : Blo 451781 455611 := bstep (se 1 (by rfl) ⟨341708, by rfl⟩ : syracuseStep 455611 = 683417) B683417
theorem B2749393 : Blo 451781 2749393 := bstep (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) B2062045
theorem B455687 : Blo 451781 455687 := bstep (se 1 (by rfl) ⟨341765, by rfl⟩ : syracuseStep 455687 = 683531) B683531
theorem B455695 : Blo 451781 455695 := bstep (se 1 (by rfl) ⟨341771, by rfl⟩ : syracuseStep 455695 = 683543) B683543
theorem B1143841 : Blo 451781 1143841 := bstep (se 2 (by rfl) ⟨428940, by rfl⟩ : syracuseStep 1143841 = 857881) B857881
theorem B455739 : Blo 451781 455739 := bstep (se 1 (by rfl) ⟨341804, by rfl⟩ : syracuseStep 455739 = 683609) B683609
theorem B1930301 : Blo 451781 1930301 := bstep (se 3 (by rfl) ⟨361931, by rfl⟩ : syracuseStep 1930301 = 723863) B723863
theorem B1307801 : Blo 451781 1307801 := bstep (se 2 (by rfl) ⟨490425, by rfl⟩ : syracuseStep 1307801 = 980851) B980851
theorem B4846837 : Blo 451781 4846837 := bstep (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) B454391
theorem B2291003 : Blo 451781 2291003 := bstep (se 1 (by rfl) ⟨1718252, by rfl⟩ : syracuseStep 2291003 = 3436505) B3436505
theorem B2585945 : Blo 451781 2585945 := bstep (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) B1939459
theorem B1537433 : Blo 451781 1537433 := bstep (se 2 (by rfl) ⟨576537, by rfl⟩ : syracuseStep 1537433 = 1153075) B1153075
theorem B2291165 : Blo 451781 2291165 := bstep (se 3 (by rfl) ⟨429593, by rfl⟩ : syracuseStep 2291165 = 859187) B859187
theorem B16774685 : Blo 451781 16774685 := bstep (se 3 (by rfl) ⟨3145253, by rfl⟩ : syracuseStep 16774685 = 6290507) B6290507
theorem B1144439 : Blo 451781 1144439 := bstep (se 1 (by rfl) ⟨858329, by rfl⟩ : syracuseStep 1144439 = 1716659) B1716659
theorem B816841 : Blo 451781 816841 := bstep (se 2 (by rfl) ⟨306315, by rfl⟩ : syracuseStep 816841 = 612631) B612631
theorem B3864293 : Blo 451781 3864293 := bstep (se 4 (by rfl) ⟨362277, by rfl⟩ : syracuseStep 3864293 = 724555) B724555
theorem B2291489 : Blo 451781 2291489 := bstep (se 2 (by rfl) ⟨859308, by rfl⟩ : syracuseStep 2291489 = 1718617) B1718617
theorem B2586401 : Blo 451781 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B2914163 : Blo 451781 2914163 := bstep (se 1 (by rfl) ⟨2185622, by rfl⟩ : syracuseStep 2914163 = 4371245) B4371245
theorem B620551 : Blo 451781 620551 := bstep (se 1 (by rfl) ⟨465413, by rfl⟩ : syracuseStep 620551 = 930827) B930827
theorem B2586653 : Blo 451781 2586653 := bstep (se 3 (by rfl) ⟨484997, by rfl⟩ : syracuseStep 2586653 = 969995) B969995
theorem B1964119 : Blo 451781 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B1538135 : Blo 451781 1538135 := bstep (se 1 (by rfl) ⟨1153601, by rfl⟩ : syracuseStep 1538135 = 2307203) B2307203
theorem B27916919 : Blo 451781 27916919 := bstep (se 1 (by rfl) ⟨20937689, by rfl⟩ : syracuseStep 27916919 = 41875379) B41875379
theorem B2292461 : Blo 451781 2292461 := bstep (se 3 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 2292461 = 859673) B859673
theorem B1145735 : Blo 451781 1145735 := bstep (se 1 (by rfl) ⟨859301, by rfl⟩ : syracuseStep 1145735 = 1718603) B1718603
theorem B1145785 : Blo 451781 1145785 := bstep (se 2 (by rfl) ⟨429669, by rfl⟩ : syracuseStep 1145785 = 859339) B859339
theorem B1637329 : Blo 451781 1637329 := bstep (se 2 (by rfl) ⟨613998, by rfl⟩ : syracuseStep 1637329 = 1227997) B1227997
theorem B1309783 : Blo 451781 1309783 := bstep (se 1 (by rfl) ⟨982337, by rfl⟩ : syracuseStep 1309783 = 1964675) B1964675
theorem B2489573 : Blo 451781 2489573 := bstep (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) B466795
theorem B4357597 : Blo 451781 4357597 := bstep (se 3 (by rfl) ⟨817049, by rfl⟩ : syracuseStep 4357597 = 1634099) B1634099
theorem B1146383 : Blo 451781 1146383 := bstep (se 1 (by rfl) ⟨859787, by rfl⟩ : syracuseStep 1146383 = 1719575) B1719575
theorem B2293271 : Blo 451781 2293271 := bstep (se 1 (by rfl) ⟨1719953, by rfl⟩ : syracuseStep 2293271 = 3439907) B3439907
theorem B67927853 : Blo 451781 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B1146899 : Blo 451781 1146899 := bstep (se 1 (by rfl) ⟨860174, by rfl⟩ : syracuseStep 1146899 = 1720349) B1720349
theorem B3309605 : Blo 451781 3309605 := bstep (se 4 (by rfl) ⟨310275, by rfl⟩ : syracuseStep 3309605 = 620551) B620551
theorem B917561 : Blo 451781 917561 := bstep (se 2 (by rfl) ⟨344085, by rfl⟩ : syracuseStep 917561 = 688171) B688171
theorem B2621783 : Blo 451781 2621783 := bstep (se 1 (by rfl) ⟨1966337, by rfl⟩ : syracuseStep 2621783 = 3932675) B3932675
theorem B1638785 : Blo 451781 1638785 := bstep (se 2 (by rfl) ⟨614544, by rfl⟩ : syracuseStep 1638785 = 1229089) B1229089
theorem B1147355 : Blo 451781 1147355 := bstep (se 1 (by rfl) ⟨860516, by rfl⟩ : syracuseStep 1147355 = 1721033) B1721033
theorem B1016531 : Blo 451781 1016531 := bstep (se 1 (by rfl) ⟨762398, by rfl⟩ : syracuseStep 1016531 = 1524797) B1524797
theorem B623543 : Blo 451781 623543 := bstep (se 1 (by rfl) ⟨467657, by rfl⟩ : syracuseStep 623543 = 935315) B935315
theorem B984071 : Blo 451781 984071 := bstep (se 1 (by rfl) ⟨738053, by rfl⟩ : syracuseStep 984071 = 1476107) B1476107
theorem B44205101 : Blo 451781 44205101 := bstep (se 3 (by rfl) ⟨8288456, by rfl⟩ : syracuseStep 44205101 = 16576913) B16576913
theorem B3671563 : Blo 451781 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B1017467 : Blo 451781 1017467 := bstep (se 1 (by rfl) ⟨763100, by rfl⟩ : syracuseStep 1017467 = 1526201) B1526201
theorem B1148539 : Blo 451781 1148539 := bstep (se 1 (by rfl) ⟨861404, by rfl⟩ : syracuseStep 1148539 = 1722809) B1722809
theorem B1017593 : Blo 451781 1017593 := bstep (se 2 (by rfl) ⟨381597, by rfl⟩ : syracuseStep 1017593 = 763195) B763195
theorem B1017863 : Blo 451781 1017863 := bstep (se 1 (by rfl) ⟨763397, by rfl⟩ : syracuseStep 1017863 = 1526795) B1526795
theorem B1640455 : Blo 451781 1640455 := bstep (se 1 (by rfl) ⟨1230341, by rfl⟩ : syracuseStep 1640455 = 2460683) B2460683
theorem B1017935 : Blo 451781 1017935 := bstep (se 1 (by rfl) ⟨763451, by rfl⟩ : syracuseStep 1017935 = 1526903) B1526903
theorem B1869905 : Blo 451781 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B1018331 : Blo 451781 1018331 := bstep (se 1 (by rfl) ⟨763748, by rfl⟩ : syracuseStep 1018331 = 1527497) B1527497
theorem B28314305 : Blo 451781 28314305 := bstep (se 2 (by rfl) ⟨10617864, by rfl⟩ : syracuseStep 28314305 = 21235729) B21235729
theorem B1018799 : Blo 451781 1018799 := bstep (se 1 (by rfl) ⟨764099, by rfl⟩ : syracuseStep 1018799 = 1528199) B1528199
theorem B1936385 : Blo 451781 1936385 := bstep (se 2 (by rfl) ⟨726144, by rfl⟩ : syracuseStep 1936385 = 1452289) B1452289
theorem B920585 : Blo 451781 920585 := bstep (se 2 (by rfl) ⟨345219, by rfl⟩ : syracuseStep 920585 = 690439) B690439
theorem B14027863 : Blo 451781 14027863 := bstep (se 1 (by rfl) ⟨10520897, by rfl⟩ : syracuseStep 14027863 = 21041795) B21041795
theorem B1019051 : Blo 451781 1019051 := bstep (se 1 (by rfl) ⟨764288, by rfl⟩ : syracuseStep 1019051 = 1528577) B1528577
theorem B920747 : Blo 451781 920747 := bstep (se 1 (by rfl) ⟨690560, by rfl⟩ : syracuseStep 920747 = 1381121) B1381121
theorem B724319 : Blo 451781 724319 := bstep (se 1 (by rfl) ⟨543239, by rfl⟩ : syracuseStep 724319 = 1086479) B1086479
theorem B5312087 : Blo 451781 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B2297483 : Blo 451781 2297483 := bstep (se 1 (by rfl) ⟨1723112, by rfl⟩ : syracuseStep 2297483 = 3446225) B3446225
theorem B1019591 : Blo 451781 1019591 := bstep (se 1 (by rfl) ⟨764693, by rfl⟩ : syracuseStep 1019591 = 1529387) B1529387
theorem B1969879 : Blo 451781 1969879 := bstep (se 1 (by rfl) ⟨1477409, by rfl⟩ : syracuseStep 1969879 = 2954819) B2954819
theorem B724729 : Blo 451781 724729 := bstep (se 2 (by rfl) ⟨271773, by rfl⟩ : syracuseStep 724729 = 543547) B543547
theorem B2461549 : Blo 451781 2461549 := bstep (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) B923081
theorem B1380827 : Blo 451781 1380827 := bstep (se 1 (by rfl) ⟨1035620, by rfl⟩ : syracuseStep 1380827 = 2071241) B2071241
theorem B1020455 : Blo 451781 1020455 := bstep (se 1 (by rfl) ⟨765341, by rfl⟩ : syracuseStep 1020455 = 1530683) B1530683
theorem B6296237 : Blo 451781 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B1020779 : Blo 451781 1020779 := bstep (se 1 (by rfl) ⟨765584, by rfl⟩ : syracuseStep 1020779 = 1531169) B1531169
theorem B1020833 : Blo 451781 1020833 := bstep (se 2 (by rfl) ⟨382812, by rfl⟩ : syracuseStep 1020833 = 765625) B765625
theorem B922823 : Blo 451781 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B1021175 : Blo 451781 1021175 := bstep (se 1 (by rfl) ⟨765881, by rfl⟩ : syracuseStep 1021175 = 1531763) B1531763
theorem B922985 : Blo 451781 922985 := bstep (se 2 (by rfl) ⟨346119, by rfl⟩ : syracuseStep 922985 = 692239) B692239
theorem B726491 : Blo 451781 726491 := bstep (se 1 (by rfl) ⟨544868, by rfl⟩ : syracuseStep 726491 = 1089737) B1089737
theorem B5805665 : Blo 451781 5805665 := bstep (se 2 (by rfl) ⟨2177124, by rfl⟩ : syracuseStep 5805665 = 4354249) B4354249
theorem B1447753 : Blo 451781 1447753 := bstep (se 2 (by rfl) ⟨542907, by rfl⟩ : syracuseStep 1447753 = 1085815) B1085815
theorem B1021769 : Blo 451781 1021769 := bstep (se 2 (by rfl) ⟨383163, by rfl⟩ : syracuseStep 1021769 = 766327) B766327
theorem B1152863 : Blo 451781 1152863 := bstep (se 1 (by rfl) ⟨864647, by rfl⟩ : syracuseStep 1152863 = 1729295) B1729295
theorem B727003 : Blo 451781 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B1087987 : Blo 451781 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B1153561 : Blo 451781 1153561 := bstep (se 2 (by rfl) ⟨432585, by rfl⟩ : syracuseStep 1153561 = 865171) B865171
theorem B3545633 : Blo 451781 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B9837125 : Blo 451781 9837125 := bstep (se 4 (by rfl) ⟨922230, by rfl⟩ : syracuseStep 9837125 = 1844461) B1844461
theorem B727631 : Blo 451781 727631 := bstep (se 1 (by rfl) ⟨545723, by rfl⟩ : syracuseStep 727631 = 1091447) B1091447
theorem B1022561 : Blo 451781 1022561 := bstep (se 2 (by rfl) ⟨383460, by rfl⟩ : syracuseStep 1022561 = 766921) B766921
theorem B11082419 : Blo 451781 11082419 := bstep (se 1 (by rfl) ⟨8311814, by rfl⟩ : syracuseStep 11082419 = 16623629) B16623629
theorem B727913 : Blo 451781 727913 := bstep (se 2 (by rfl) ⟨272967, by rfl⟩ : syracuseStep 727913 = 545935) B545935
theorem B1022903 : Blo 451781 1022903 := bstep (se 1 (by rfl) ⟨767177, by rfl⟩ : syracuseStep 1022903 = 1534355) B1534355
theorem B6462449 : Blo 451781 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B12393719 : Blo 451781 12393719 := bstep (se 1 (by rfl) ⟨9295289, by rfl⟩ : syracuseStep 12393719 = 18590579) B18590579
theorem B859385 : Blo 451781 859385 := bstep (se 2 (by rfl) ⟨322269, by rfl⟩ : syracuseStep 859385 = 644539) B644539
theorem B1940861 : Blo 451781 1940861 := bstep (se 3 (by rfl) ⟨363911, by rfl⟩ : syracuseStep 1940861 = 727823) B727823
theorem B859567 : Blo 451781 859567 := bstep (se 1 (by rfl) ⟨644675, by rfl⟩ : syracuseStep 859567 = 1289351) B1289351
theorem B1023497 : Blo 451781 1023497 := bstep (se 2 (by rfl) ⟨383811, by rfl⟩ : syracuseStep 1023497 = 767623) B767623
theorem B859727 : Blo 451781 859727 := bstep (se 1 (by rfl) ⟨644795, by rfl⟩ : syracuseStep 859727 = 1289591) B1289591
theorem B1089121 : Blo 451781 1089121 := bstep (se 2 (by rfl) ⟨408420, by rfl⟩ : syracuseStep 1089121 = 816841) B816841
theorem B2072263 : Blo 451781 2072263 := bstep (se 1 (by rfl) ⟨1554197, by rfl⟩ : syracuseStep 2072263 = 3108395) B3108395
theorem B1023839 : Blo 451781 1023839 := bstep (se 1 (by rfl) ⟨767879, by rfl⟩ : syracuseStep 1023839 = 1535759) B1535759
theorem B2301857 : Blo 451781 2301857 := bstep (se 2 (by rfl) ⟨863196, by rfl⟩ : syracuseStep 2301857 = 1726393) B1726393
theorem B1024019 : Blo 451781 1024019 := bstep (se 1 (by rfl) ⟨768014, by rfl⟩ : syracuseStep 1024019 = 1536029) B1536029
theorem B1024361 : Blo 451781 1024361 := bstep (se 2 (by rfl) ⟨384135, by rfl⟩ : syracuseStep 1024361 = 768271) B768271
theorem B3482135 : Blo 451781 3482135 := bstep (se 1 (by rfl) ⟨2611601, by rfl⟩ : syracuseStep 3482135 = 5223203) B5223203
theorem B860843 : Blo 451781 860843 := bstep (se 1 (by rfl) ⟨645632, by rfl⟩ : syracuseStep 860843 = 1291265) B1291265
theorem B1286867 : Blo 451781 1286867 := bstep (se 1 (by rfl) ⟨965150, by rfl⟩ : syracuseStep 1286867 = 1930301) B1930301
theorem B1024955 : Blo 451781 1024955 := bstep (se 1 (by rfl) ⟨768716, by rfl⟩ : syracuseStep 1024955 = 1537433) B1537433
theorem B11183123 : Blo 451781 11183123 := bstep (se 1 (by rfl) ⟨8387342, by rfl⟩ : syracuseStep 11183123 = 16774685) B16774685
theorem B1025081 : Blo 451781 1025081 := bstep (se 2 (by rfl) ⟨384405, by rfl⟩ : syracuseStep 1025081 = 768811) B768811
theorem B762959 : Blo 451781 762959 := bstep (se 1 (by rfl) ⟨572219, by rfl⟩ : syracuseStep 762959 = 1144439) B1144439
theorem B1942775 : Blo 451781 1942775 := bstep (se 1 (by rfl) ⟨1457081, by rfl⟩ : syracuseStep 1942775 = 2914163) B2914163
theorem B1025423 : Blo 451781 1025423 := bstep (se 1 (by rfl) ⟨769067, by rfl⟩ : syracuseStep 1025423 = 1538135) B1538135
theorem B1746377 : Blo 451781 1746377 := bstep (se 2 (by rfl) ⟨654891, by rfl⟩ : syracuseStep 1746377 = 1309783) B1309783
theorem B3679867 : Blo 451781 3679867 := bstep (se 1 (by rfl) ⟨2759900, by rfl⟩ : syracuseStep 3679867 = 5519801) B5519801
theorem B763823 : Blo 451781 763823 := bstep (se 1 (by rfl) ⟨572867, by rfl⟩ : syracuseStep 763823 = 1145735) B1145735
theorem B993211 : Blo 451781 993211 := bstep (se 1 (by rfl) ⟨744908, by rfl⟩ : syracuseStep 993211 = 1489817) B1489817
theorem B5810129 : Blo 451781 5810129 := bstep (se 2 (by rfl) ⟨2178798, by rfl⟩ : syracuseStep 5810129 = 4357597) B4357597
theorem B1288349 : Blo 451781 1288349 := bstep (se 3 (by rfl) ⟨241565, by rfl⟩ : syracuseStep 1288349 = 483131) B483131
theorem B6564077 : Blo 451781 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B764255 : Blo 451781 764255 := bstep (se 1 (by rfl) ⟨573191, by rfl⟩ : syracuseStep 764255 = 1146383) B1146383
theorem B862559 : Blo 451781 862559 := bstep (se 1 (by rfl) ⟨646919, by rfl⟩ : syracuseStep 862559 = 1293839) B1293839
theorem B1452431 : Blo 451781 1452431 := bstep (se 1 (by rfl) ⟨1089323, by rfl⟩ : syracuseStep 1452431 = 2178647) B2178647
theorem B862969 : Blo 451781 862969 := bstep (se 2 (by rfl) ⟨323613, by rfl⟩ : syracuseStep 862969 = 647227) B647227
theorem B764815 : Blo 451781 764815 := bstep (se 1 (by rfl) ⟨573611, by rfl⟩ : syracuseStep 764815 = 1147223) B1147223
theorem B1289135 : Blo 451781 1289135 := bstep (se 1 (by rfl) ⟨966851, by rfl⟩ : syracuseStep 1289135 = 1933703) B1933703
theorem B1321991 : Blo 451781 1321991 := bstep (se 1 (by rfl) ⟨991493, by rfl⟩ : syracuseStep 1321991 = 1982987) B1982987
theorem B863311 : Blo 451781 863311 := bstep (se 1 (by rfl) ⟨647483, by rfl⟩ : syracuseStep 863311 = 1294967) B1294967
theorem B3452057 : Blo 451781 3452057 := bstep (se 2 (by rfl) ⟨1294521, by rfl⟩ : syracuseStep 3452057 = 2589043) B2589043
theorem B2895041 : Blo 451781 2895041 := bstep (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) B2171281
theorem B863561 : Blo 451781 863561 := bstep (se 2 (by rfl) ⟨323835, by rfl⟩ : syracuseStep 863561 = 647671) B647671
theorem B765497 : Blo 451781 765497 := bstep (se 2 (by rfl) ⟨287061, by rfl⟩ : syracuseStep 765497 = 574123) B574123
theorem B1552007 : Blo 451781 1552007 := bstep (se 1 (by rfl) ⟨1164005, by rfl⟩ : syracuseStep 1552007 = 2328011) B2328011
theorem B1945235 : Blo 451781 1945235 := bstep (se 1 (by rfl) ⟨1458926, by rfl⟩ : syracuseStep 1945235 = 2917853) B2917853
theorem B1846973 : Blo 451781 1846973 := bstep (se 3 (by rfl) ⟨346307, by rfl⟩ : syracuseStep 1846973 = 692615) B692615
theorem B1093483 : Blo 451781 1093483 := bstep (se 1 (by rfl) ⟨820112, by rfl⟩ : syracuseStep 1093483 = 1640225) B1640225
theorem B3092411 : Blo 451781 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B7385165 : Blo 451781 7385165 := bstep (se 3 (by rfl) ⟨1384718, by rfl⟩ : syracuseStep 7385165 = 2769437) B2769437
theorem B5156945 : Blo 451781 5156945 := bstep (se 2 (by rfl) ⟨1933854, by rfl⟩ : syracuseStep 5156945 = 3867709) B3867709
theorem B1454237 : Blo 451781 1454237 := bstep (se 3 (by rfl) ⟨272669, by rfl⟩ : syracuseStep 1454237 = 545339) B545339
theorem B864427 : Blo 451781 864427 := bstep (se 1 (by rfl) ⟨648320, by rfl⟩ : syracuseStep 864427 = 1296641) B1296641
theorem B766199 : Blo 451781 766199 := bstep (se 1 (by rfl) ⟨574649, by rfl⟩ : syracuseStep 766199 = 1149299) B1149299
theorem B864503 : Blo 451781 864503 := bstep (se 1 (by rfl) ⟨648377, by rfl⟩ : syracuseStep 864503 = 1296755) B1296755
theorem B1716491 : Blo 451781 1716491 := bstep (se 1 (by rfl) ⟨1287368, by rfl⟩ : syracuseStep 1716491 = 2574737) B2574737
theorem B995689 : Blo 451781 995689 := bstep (se 2 (by rfl) ⟨373383, by rfl⟩ : syracuseStep 995689 = 746767) B746767
theorem B864731 : Blo 451781 864731 := bstep (se 1 (by rfl) ⟨648548, by rfl⟩ : syracuseStep 864731 = 1297097) B1297097
theorem B766543 : Blo 451781 766543 := bstep (se 1 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 766543 = 1149815) B1149815
theorem B2077369 : Blo 451781 2077369 := bstep (se 2 (by rfl) ⟨779013, by rfl⟩ : syracuseStep 2077369 = 1558027) B1558027
theorem B1716947 : Blo 451781 1716947 := bstep (se 1 (by rfl) ⟨1287710, by rfl⟩ : syracuseStep 1716947 = 2575421) B2575421
theorem B7746353 : Blo 451781 7746353 := bstep (se 2 (by rfl) ⟨2904882, by rfl⟩ : syracuseStep 7746353 = 5809765) B5809765
theorem B766793 : Blo 451781 766793 := bstep (se 2 (by rfl) ⟨287547, by rfl⟩ : syracuseStep 766793 = 575095) B575095
theorem B11678579 : Blo 451781 11678579 := bstep (se 1 (by rfl) ⟨8758934, by rfl⟩ : syracuseStep 11678579 = 17517869) B17517869
theorem B1946551 : Blo 451781 1946551 := bstep (se 1 (by rfl) ⟨1459913, by rfl⟩ : syracuseStep 1946551 = 2919827) B2919827
theorem B3454001 : Blo 451781 3454001 := bstep (se 2 (by rfl) ⟨1295250, by rfl⟩ : syracuseStep 3454001 = 2590501) B2590501
theorem B767225 : Blo 451781 767225 := bstep (se 2 (by rfl) ⟨287709, by rfl⟩ : syracuseStep 767225 = 575419) B575419
theorem B767407 : Blo 451781 767407 := bstep (se 1 (by rfl) ⟨575555, by rfl⟩ : syracuseStep 767407 = 1151111) B1151111
theorem B767495 : Blo 451781 767495 := bstep (se 1 (by rfl) ⟨575621, by rfl⟩ : syracuseStep 767495 = 1151243) B1151243
theorem B1717949 : Blo 451781 1717949 := bstep (se 3 (by rfl) ⟨322115, by rfl⟩ : syracuseStep 1717949 = 644231) B644231
theorem B2897707 : Blo 451781 2897707 := bstep (se 1 (by rfl) ⟨2173280, by rfl⟩ : syracuseStep 2897707 = 4346561) B4346561
theorem B767839 : Blo 451781 767839 := bstep (se 1 (by rfl) ⟨575879, by rfl⟩ : syracuseStep 767839 = 1151759) B1151759
theorem B767927 : Blo 451781 767927 := bstep (se 1 (by rfl) ⟨575945, by rfl⟩ : syracuseStep 767927 = 1151891) B1151891
theorem B2176955 : Blo 451781 2176955 := bstep (se 1 (by rfl) ⟨1632716, by rfl⟩ : syracuseStep 2176955 = 3265433) B3265433
theorem B4405553 : Blo 451781 4405553 := bstep (se 2 (by rfl) ⟨1652082, by rfl⟩ : syracuseStep 4405553 = 3304165) B3304165
theorem B768521 : Blo 451781 768521 := bstep (se 2 (by rfl) ⟨288195, by rfl⟩ : syracuseStep 768521 = 576391) B576391
theorem B1456775 : Blo 451781 1456775 := bstep (se 1 (by rfl) ⟨1092581, by rfl⟩ : syracuseStep 1456775 = 2185163) B2185163
theorem B768683 : Blo 451781 768683 := bstep (se 1 (by rfl) ⟨576512, by rfl⟩ : syracuseStep 768683 = 1153025) B1153025
theorem B769081 : Blo 451781 769081 := bstep (se 2 (by rfl) ⟨288405, by rfl⟩ : syracuseStep 769081 = 576811) B576811
theorem B1719377 : Blo 451781 1719377 := bstep (se 2 (by rfl) ⟨644766, by rfl⟩ : syracuseStep 1719377 = 1289533) B1289533
theorem B9453095 : Blo 451781 9453095 := bstep (se 1 (by rfl) ⟨7089821, by rfl⟩ : syracuseStep 9453095 = 14179643) B14179643
theorem B1162849 : Blo 451781 1162849 := bstep (se 2 (by rfl) ⟨436068, by rfl⟩ : syracuseStep 1162849 = 872137) B872137
theorem B1457875 : Blo 451781 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B1458107 : Blo 451781 1458107 := bstep (se 1 (by rfl) ⟨1093580, by rfl⟩ : syracuseStep 1458107 = 2187161) B2187161
theorem B2768833 : Blo 451781 2768833 := bstep (se 2 (by rfl) ⟨1038312, by rfl⟩ : syracuseStep 2768833 = 2076625) B2076625
theorem B1720865 : Blo 451781 1720865 := bstep (se 2 (by rfl) ⟨645324, by rfl⟩ : syracuseStep 1720865 = 1290649) B1290649
theorem B508495 : Blo 451781 508495 := bstep (se 1 (by rfl) ⟨381371, by rfl⟩ : syracuseStep 508495 = 762743) B762743
theorem B2900681 : Blo 451781 2900681 := bstep (se 2 (by rfl) ⟨1087755, by rfl⟩ : syracuseStep 2900681 = 2175511) B2175511
theorem B1721047 : Blo 451781 1721047 := bstep (se 1 (by rfl) ⟨1290785, by rfl⟩ : syracuseStep 1721047 = 2581571) B2581571
theorem B574391 : Blo 451781 574391 := bstep (se 1 (by rfl) ⟨430793, by rfl⟩ : syracuseStep 574391 = 861587) B861587
theorem B508891 : Blo 451781 508891 := bstep (se 1 (by rfl) ⟨381668, by rfl⟩ : syracuseStep 508891 = 763337) B763337
theorem B1721351 : Blo 451781 1721351 := bstep (se 1 (by rfl) ⟨1291013, by rfl⟩ : syracuseStep 1721351 = 2582027) B2582027
theorem B4342835 : Blo 451781 4342835 := bstep (se 1 (by rfl) ⟨3257126, by rfl⟩ : syracuseStep 4342835 = 6514253) B6514253
theorem B574543 : Blo 451781 574543 := bstep (se 1 (by rfl) ⟨430907, by rfl⟩ : syracuseStep 574543 = 861815) B861815
theorem B1524851 : Blo 451781 1524851 := bstep (se 1 (by rfl) ⟨1143638, by rfl⟩ : syracuseStep 1524851 = 2287277) B2287277
theorem B4146347 : Blo 451781 4146347 := bstep (se 1 (by rfl) ⟨3109760, by rfl⟩ : syracuseStep 4146347 = 6219521) B6219521
theorem B1525121 : Blo 451781 1525121 := bstep (se 2 (by rfl) ⟨571920, by rfl⟩ : syracuseStep 1525121 = 1143841) B1143841
theorem B509359 : Blo 451781 509359 := bstep (se 1 (by rfl) ⟨382019, by rfl⟩ : syracuseStep 509359 = 764039) B764039
theorem B1721837 : Blo 451781 1721837 := bstep (se 3 (by rfl) ⟨322844, by rfl⟩ : syracuseStep 1721837 = 645689) B645689
theorem B1459721 : Blo 451781 1459721 := bstep (se 2 (by rfl) ⟨547395, by rfl⟩ : syracuseStep 1459721 = 1094791) B1094791
theorem B2573963 : Blo 451781 2573963 := bstep (se 1 (by rfl) ⟨1930472, by rfl⟩ : syracuseStep 2573963 = 3860945) B3860945
theorem B1296071 : Blo 451781 1296071 := bstep (se 1 (by rfl) ⟨972053, by rfl⟩ : syracuseStep 1296071 = 1944107) B1944107
theorem B509791 : Blo 451781 509791 := bstep (se 1 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 509791 = 764687) B764687
theorem B1525931 : Blo 451781 1525931 := bstep (se 1 (by rfl) ⟨1144448, by rfl⟩ : syracuseStep 1525931 = 2288897) B2288897
theorem B510151 : Blo 451781 510151 := bstep (se 1 (by rfl) ⟨382613, by rfl⟩ : syracuseStep 510151 = 765227) B765227
theorem B575687 : Blo 451781 575687 := bstep (se 1 (by rfl) ⟨431765, by rfl⟩ : syracuseStep 575687 = 863531) B863531
theorem B543071 : Blo 451781 543071 := bstep (se 1 (by rfl) ⟨407303, by rfl⟩ : syracuseStep 543071 = 814607) B814607
theorem B575839 : Blo 451781 575839 := bstep (se 1 (by rfl) ⟨431879, by rfl⟩ : syracuseStep 575839 = 863759) B863759
theorem B16566707 : Blo 451781 16566707 := bstep (se 1 (by rfl) ⟨12425030, by rfl⟩ : syracuseStep 16566707 = 24850061) B24850061
theorem B1722977 : Blo 451781 1722977 := bstep (se 2 (by rfl) ⟨646116, by rfl⟩ : syracuseStep 1722977 = 1292233) B1292233
theorem B1526471 : Blo 451781 1526471 := bstep (se 1 (by rfl) ⟨1144853, by rfl⟩ : syracuseStep 1526471 = 2289707) B2289707
theorem B511015 : Blo 451781 511015 := bstep (se 1 (by rfl) ⟨383261, by rfl⟩ : syracuseStep 511015 = 766523) B766523
theorem B6638861 : Blo 451781 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B871867 : Blo 451781 871867 := bstep (se 1 (by rfl) ⟨653900, by rfl⟩ : syracuseStep 871867 = 1307801) B1307801
theorem B1297883 : Blo 451781 1297883 := bstep (se 1 (by rfl) ⟨973412, by rfl⟩ : syracuseStep 1297883 = 1946825) B1946825
theorem B1527335 : Blo 451781 1527335 := bstep (se 1 (by rfl) ⟨1145501, by rfl⟩ : syracuseStep 1527335 = 2291003) B2291003
theorem B1723963 : Blo 451781 1723963 := bstep (se 1 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 1723963 = 2585945) B2585945
theorem B1527443 : Blo 451781 1527443 := bstep (se 1 (by rfl) ⟨1145582, by rfl⟩ : syracuseStep 1527443 = 2291165) B2291165
theorem B2936519 : Blo 451781 2936519 := bstep (se 1 (by rfl) ⟨2202389, by rfl⟩ : syracuseStep 2936519 = 4404779) B4404779
theorem B2576195 : Blo 451781 2576195 := bstep (se 1 (by rfl) ⟨1932146, by rfl⟩ : syracuseStep 2576195 = 3864293) B3864293
theorem B1527659 : Blo 451781 1527659 := bstep (se 1 (by rfl) ⟨1145744, by rfl⟩ : syracuseStep 1527659 = 2291489) B2291489
theorem B1724267 : Blo 451781 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B1527713 : Blo 451781 1527713 := bstep (se 2 (by rfl) ⟨572892, by rfl⟩ : syracuseStep 1527713 = 1145785) B1145785
theorem B970679 : Blo 451781 970679 := bstep (se 1 (by rfl) ⟨728009, by rfl⟩ : syracuseStep 970679 = 1456019) B1456019
theorem B2183105 : Blo 451781 2183105 := bstep (se 2 (by rfl) ⟨818664, by rfl⟩ : syracuseStep 2183105 = 1637329) B1637329
theorem B1724435 : Blo 451781 1724435 := bstep (se 1 (by rfl) ⟨1293326, by rfl⟩ : syracuseStep 1724435 = 2586653) B2586653
theorem B4378853 : Blo 451781 4378853 := bstep (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) B821035
theorem B2904473 : Blo 451781 2904473 := bstep (se 2 (by rfl) ⟨1089177, by rfl⟩ : syracuseStep 2904473 = 2178355) B2178355
theorem B1528307 : Blo 451781 1528307 := bstep (se 1 (by rfl) ⟨1146230, by rfl⟩ : syracuseStep 1528307 = 2292461) B2292461
theorem B512635 : Blo 451781 512635 := bstep (se 1 (by rfl) ⟨384476, by rfl⟩ : syracuseStep 512635 = 768953) B768953
theorem B1036999 : Blo 451781 1036999 := bstep (se 1 (by rfl) ⟨777749, by rfl⟩ : syracuseStep 1036999 = 1555499) B1555499
theorem B3724289 : Blo 451781 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B1528847 : Blo 451781 1528847 := bstep (se 1 (by rfl) ⟨1146635, by rfl⟩ : syracuseStep 1528847 = 2293271) B2293271
theorem B644527 : Blo 451781 644527 := bstep (se 1 (by rfl) ⟨483395, by rfl⟩ : syracuseStep 644527 = 966791) B966791
theorem B1529441 : Blo 451781 1529441 := bstep (se 2 (by rfl) ⟨573540, by rfl⟩ : syracuseStep 1529441 = 1147081) B1147081
theorem B6543139 : Blo 451781 6543139 := bstep (se 1 (by rfl) ⟨4907354, by rfl⟩ : syracuseStep 6543139 = 9814709) B9814709
theorem B2578337 : Blo 451781 2578337 := bstep (se 2 (by rfl) ⟨966876, by rfl⟩ : syracuseStep 2578337 = 1933753) B1933753
theorem B677807 : Blo 451781 677807 := bstep (se 1 (by rfl) ⟨508355, by rfl⟩ : syracuseStep 677807 = 1016711) B1016711
theorem B677897 : Blo 451781 677897 := bstep (se 2 (by rfl) ⟨254211, by rfl⟩ : syracuseStep 677897 = 508423) B508423
theorem B677927 : Blo 451781 677927 := bstep (se 1 (by rfl) ⟨508445, by rfl⟩ : syracuseStep 677927 = 1016891) B1016891
theorem B678011 : Blo 451781 678011 := bstep (se 1 (by rfl) ⟨508508, by rfl⟩ : syracuseStep 678011 = 1017017) B1017017
theorem B678137 : Blo 451781 678137 := bstep (se 2 (by rfl) ⟨254301, by rfl⟩ : syracuseStep 678137 = 508603) B508603
theorem B6314273 : Blo 451781 6314273 := bstep (se 2 (by rfl) ⟨2367852, by rfl⟩ : syracuseStep 6314273 = 4735705) B4735705
theorem B678239 : Blo 451781 678239 := bstep (se 1 (by rfl) ⟨508679, by rfl⟩ : syracuseStep 678239 = 1017359) B1017359
theorem B678251 : Blo 451781 678251 := bstep (se 1 (by rfl) ⟨508688, by rfl⟩ : syracuseStep 678251 = 1017377) B1017377
theorem B678479 : Blo 451781 678479 := bstep (se 1 (by rfl) ⟨508859, by rfl⟩ : syracuseStep 678479 = 1017719) B1017719
theorem B678599 : Blo 451781 678599 := bstep (se 1 (by rfl) ⟨508949, by rfl⟩ : syracuseStep 678599 = 1017899) B1017899
theorem B678761 : Blo 451781 678761 := bstep (se 2 (by rfl) ⟨254535, by rfl⟩ : syracuseStep 678761 = 509071) B509071
theorem B1727351 : Blo 451781 1727351 := bstep (se 1 (by rfl) ⟨1295513, by rfl⟩ : syracuseStep 1727351 = 2591027) B2591027
theorem B678839 : Blo 451781 678839 := bstep (se 1 (by rfl) ⟨509129, by rfl⟩ : syracuseStep 678839 = 1018259) B1018259
theorem B678875 : Blo 451781 678875 := bstep (se 1 (by rfl) ⟨509156, by rfl⟩ : syracuseStep 678875 = 1018313) B1018313
theorem B1530899 : Blo 451781 1530899 := bstep (se 1 (by rfl) ⟨1148174, by rfl⟩ : syracuseStep 1530899 = 2296349) B2296349
theorem B3103991 : Blo 451781 3103991 := bstep (se 1 (by rfl) ⟨2327993, by rfl⟩ : syracuseStep 3103991 = 4655987) B4655987
theorem B1531223 : Blo 451781 1531223 := bstep (se 1 (by rfl) ⟨1148417, by rfl⟩ : syracuseStep 1531223 = 2296835) B2296835
theorem B679343 : Blo 451781 679343 := bstep (se 1 (by rfl) ⟨509507, by rfl⟩ : syracuseStep 679343 = 1019015) B1019015
theorem B679433 : Blo 451781 679433 := bstep (se 2 (by rfl) ⟨254787, by rfl⟩ : syracuseStep 679433 = 509575) B509575
theorem B679463 : Blo 451781 679463 := bstep (se 1 (by rfl) ⟨509597, by rfl⟩ : syracuseStep 679463 = 1019195) B1019195
theorem B679547 : Blo 451781 679547 := bstep (se 1 (by rfl) ⟨509660, by rfl⟩ : syracuseStep 679547 = 1019321) B1019321
theorem B2580113 : Blo 451781 2580113 := bstep (se 2 (by rfl) ⟨967542, by rfl⟩ : syracuseStep 2580113 = 1935085) B1935085
theorem B679673 : Blo 451781 679673 := bstep (se 2 (by rfl) ⟨254877, by rfl⟩ : syracuseStep 679673 = 509755) B509755
theorem B1728323 : Blo 451781 1728323 := bstep (se 1 (by rfl) ⟨1296242, by rfl⟩ : syracuseStep 1728323 = 2592485) B2592485
theorem B876361 : Blo 451781 876361 := bstep (se 2 (by rfl) ⟨328635, by rfl⟩ : syracuseStep 876361 = 657271) B657271
theorem B679775 : Blo 451781 679775 := bstep (se 1 (by rfl) ⟨509831, by rfl⟩ : syracuseStep 679775 = 1019663) B1019663
theorem B679787 : Blo 451781 679787 := bstep (se 1 (by rfl) ⟨509840, by rfl⟩ : syracuseStep 679787 = 1019681) B1019681
theorem B1630135 : Blo 451781 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B2908163 : Blo 451781 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B680015 : Blo 451781 680015 := bstep (se 1 (by rfl) ⟨510011, by rfl⟩ : syracuseStep 680015 = 1020023) B1020023
theorem B2580569 : Blo 451781 2580569 := bstep (se 2 (by rfl) ⟨967713, by rfl⟩ : syracuseStep 2580569 = 1935427) B1935427
theorem B680135 : Blo 451781 680135 := bstep (se 1 (by rfl) ⟨510101, by rfl⟩ : syracuseStep 680135 = 1020203) B1020203
theorem B39739747 : Blo 451781 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B680297 : Blo 451781 680297 := bstep (se 2 (by rfl) ⟨255111, by rfl⟩ : syracuseStep 680297 = 510223) B510223
theorem B1532303 : Blo 451781 1532303 := bstep (se 1 (by rfl) ⟨1149227, by rfl⟩ : syracuseStep 1532303 = 2298455) B2298455
theorem B680375 : Blo 451781 680375 := bstep (se 1 (by rfl) ⟨510281, by rfl⟩ : syracuseStep 680375 = 1020563) B1020563
theorem B680411 : Blo 451781 680411 := bstep (se 1 (by rfl) ⟨510308, by rfl⟩ : syracuseStep 680411 = 1020617) B1020617
theorem B1532627 : Blo 451781 1532627 := bstep (se 1 (by rfl) ⟨1149470, by rfl⟩ : syracuseStep 1532627 = 2298941) B2298941
theorem B1729309 : Blo 451781 1729309 := bstep (se 3 (by rfl) ⟨324245, by rfl⟩ : syracuseStep 1729309 = 648491) B648491
theorem B680879 : Blo 451781 680879 := bstep (se 1 (by rfl) ⟨510659, by rfl⟩ : syracuseStep 680879 = 1021319) B1021319
theorem B680969 : Blo 451781 680969 := bstep (se 2 (by rfl) ⟨255363, by rfl⟩ : syracuseStep 680969 = 510727) B510727
theorem B680999 : Blo 451781 680999 := bstep (se 1 (by rfl) ⟨510749, by rfl⟩ : syracuseStep 680999 = 1021499) B1021499
theorem B681083 : Blo 451781 681083 := bstep (se 1 (by rfl) ⟨510812, by rfl⟩ : syracuseStep 681083 = 1021625) B1021625
theorem B3105985 : Blo 451781 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B451783 : Blo 451781 451783 := bstep (se 1 (by rfl) ⟨338837, by rfl⟩ : syracuseStep 451783 = 677675) B677675
theorem B451803 : Blo 451781 451803 := bstep (se 1 (by rfl) ⟨338852, by rfl⟩ : syracuseStep 451803 = 677705) B677705
theorem B681209 : Blo 451781 681209 := bstep (se 2 (by rfl) ⟨255453, by rfl⟩ : syracuseStep 681209 = 510907) B510907
theorem B451879 : Blo 451781 451879 := bstep (se 1 (by rfl) ⟨338909, by rfl⟩ : syracuseStep 451879 = 677819) B677819
theorem B451919 : Blo 451781 451919 := bstep (se 1 (by rfl) ⟨338939, by rfl⟩ : syracuseStep 451919 = 677879) B677879
theorem B451935 : Blo 451781 451935 := bstep (se 1 (by rfl) ⟨338951, by rfl⟩ : syracuseStep 451935 = 677903) B677903
theorem B681311 : Blo 451781 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B681323 : Blo 451781 681323 := bstep (se 1 (by rfl) ⟨510992, by rfl⟩ : syracuseStep 681323 = 1021985) B1021985
theorem B451963 : Blo 451781 451963 := bstep (se 1 (by rfl) ⟨338972, by rfl⟩ : syracuseStep 451963 = 677945) B677945
theorem B452015 : Blo 451781 452015 := bstep (se 1 (by rfl) ⟨339011, by rfl⟩ : syracuseStep 452015 = 678023) B678023
theorem B452039 : Blo 451781 452039 := bstep (se 1 (by rfl) ⟨339029, by rfl⟩ : syracuseStep 452039 = 678059) B678059
theorem B452059 : Blo 451781 452059 := bstep (se 1 (by rfl) ⟨339044, by rfl⟩ : syracuseStep 452059 = 678089) B678089
theorem B1238537 : Blo 451781 1238537 := bstep (se 2 (by rfl) ⟨464451, by rfl⟩ : syracuseStep 1238537 = 928903) B928903
theorem B452135 : Blo 451781 452135 := bstep (se 1 (by rfl) ⟨339101, by rfl⟩ : syracuseStep 452135 = 678203) B678203
theorem B452175 : Blo 451781 452175 := bstep (se 1 (by rfl) ⟨339131, by rfl⟩ : syracuseStep 452175 = 678263) B678263
theorem B681551 : Blo 451781 681551 := bstep (se 1 (by rfl) ⟨511163, by rfl⟩ : syracuseStep 681551 = 1022327) B1022327
theorem B452191 : Blo 451781 452191 := bstep (se 1 (by rfl) ⟨339143, by rfl⟩ : syracuseStep 452191 = 678287) B678287
theorem B452219 : Blo 451781 452219 := bstep (se 1 (by rfl) ⟨339164, by rfl⟩ : syracuseStep 452219 = 678329) B678329
theorem B2647675 : Blo 451781 2647675 := bstep (se 1 (by rfl) ⟨1985756, by rfl⟩ : syracuseStep 2647675 = 3971513) B3971513
theorem B452271 : Blo 451781 452271 := bstep (se 1 (by rfl) ⟨339203, by rfl⟩ : syracuseStep 452271 = 678407) B678407
theorem B452295 : Blo 451781 452295 := bstep (se 1 (by rfl) ⟨339221, by rfl⟩ : syracuseStep 452295 = 678443) B678443
theorem B681671 : Blo 451781 681671 := bstep (se 1 (by rfl) ⟨511253, by rfl⟩ : syracuseStep 681671 = 1022507) B1022507
theorem B452315 : Blo 451781 452315 := bstep (se 1 (by rfl) ⟨339236, by rfl⟩ : syracuseStep 452315 = 678473) B678473
theorem B452391 : Blo 451781 452391 := bstep (se 1 (by rfl) ⟨339293, by rfl⟩ : syracuseStep 452391 = 678587) B678587
theorem B452431 : Blo 451781 452431 := bstep (se 1 (by rfl) ⟨339323, by rfl⟩ : syracuseStep 452431 = 678647) B678647
theorem B452447 : Blo 451781 452447 := bstep (se 1 (by rfl) ⟨339335, by rfl⟩ : syracuseStep 452447 = 678671) B678671
theorem B681833 : Blo 451781 681833 := bstep (se 2 (by rfl) ⟨255687, by rfl⟩ : syracuseStep 681833 = 511375) B511375
theorem B1533815 : Blo 451781 1533815 := bstep (se 1 (by rfl) ⟨1150361, by rfl⟩ : syracuseStep 1533815 = 2300723) B2300723
theorem B452475 : Blo 451781 452475 := bstep (se 1 (by rfl) ⟨339356, by rfl⟩ : syracuseStep 452475 = 678713) B678713
theorem B2942855 : Blo 451781 2942855 := bstep (se 1 (by rfl) ⟨2207141, by rfl⟩ : syracuseStep 2942855 = 4414283) B4414283
theorem B2910113 : Blo 451781 2910113 := bstep (se 2 (by rfl) ⟨1091292, by rfl⟩ : syracuseStep 2910113 = 2182585) B2182585
theorem B452527 : Blo 451781 452527 := bstep (se 1 (by rfl) ⟨339395, by rfl⟩ : syracuseStep 452527 = 678791) B678791
theorem B681911 : Blo 451781 681911 := bstep (se 1 (by rfl) ⟨511433, by rfl⟩ : syracuseStep 681911 = 1022867) B1022867
theorem B452551 : Blo 451781 452551 := bstep (se 1 (by rfl) ⟨339413, by rfl⟩ : syracuseStep 452551 = 678827) B678827
theorem B452571 : Blo 451781 452571 := bstep (se 1 (by rfl) ⟨339428, by rfl⟩ : syracuseStep 452571 = 678857) B678857
theorem B681947 : Blo 451781 681947 := bstep (se 1 (by rfl) ⟨511460, by rfl⟩ : syracuseStep 681947 = 1022921) B1022921
theorem B452647 : Blo 451781 452647 := bstep (se 1 (by rfl) ⟨339485, by rfl⟩ : syracuseStep 452647 = 678971) B678971
theorem B452687 : Blo 451781 452687 := bstep (se 1 (by rfl) ⟨339515, by rfl⟩ : syracuseStep 452687 = 679031) B679031
theorem B1534031 : Blo 451781 1534031 := bstep (se 1 (by rfl) ⟨1150523, by rfl⟩ : syracuseStep 1534031 = 2301047) B2301047
theorem B452703 : Blo 451781 452703 := bstep (se 1 (by rfl) ⟨339527, by rfl⟩ : syracuseStep 452703 = 679055) B679055
theorem B452731 : Blo 451781 452731 := bstep (se 1 (by rfl) ⟨339548, by rfl⟩ : syracuseStep 452731 = 679097) B679097
theorem B1632413 : Blo 451781 1632413 := bstep (se 3 (by rfl) ⟨306077, by rfl⟩ : syracuseStep 1632413 = 612155) B612155
theorem B452783 : Blo 451781 452783 := bstep (se 1 (by rfl) ⟨339587, by rfl⟩ : syracuseStep 452783 = 679175) B679175
theorem B452807 : Blo 451781 452807 := bstep (se 1 (by rfl) ⟨339605, by rfl⟩ : syracuseStep 452807 = 679211) B679211
theorem B452827 : Blo 451781 452827 := bstep (se 1 (by rfl) ⟨339620, by rfl⟩ : syracuseStep 452827 = 679241) B679241
theorem B452903 : Blo 451781 452903 := bstep (se 1 (by rfl) ⟨339677, by rfl⟩ : syracuseStep 452903 = 679355) B679355
theorem B452943 : Blo 451781 452943 := bstep (se 1 (by rfl) ⟨339707, by rfl⟩ : syracuseStep 452943 = 679415) B679415
theorem B452959 : Blo 451781 452959 := bstep (se 1 (by rfl) ⟨339719, by rfl⟩ : syracuseStep 452959 = 679439) B679439
theorem B452987 : Blo 451781 452987 := bstep (se 1 (by rfl) ⟨339740, by rfl⟩ : syracuseStep 452987 = 679481) B679481
theorem B453039 : Blo 451781 453039 := bstep (se 1 (by rfl) ⟨339779, by rfl⟩ : syracuseStep 453039 = 679559) B679559
theorem B682415 : Blo 451781 682415 := bstep (se 1 (by rfl) ⟨511811, by rfl⟩ : syracuseStep 682415 = 1023623) B1023623
theorem B13101497 : Blo 451781 13101497 := bstep (se 2 (by rfl) ⟨4913061, by rfl⟩ : syracuseStep 13101497 = 9826123) B9826123
theorem B453063 : Blo 451781 453063 := bstep (se 1 (by rfl) ⟨339797, by rfl⟩ : syracuseStep 453063 = 679595) B679595
theorem B1534409 : Blo 451781 1534409 := bstep (se 2 (by rfl) ⟨575403, by rfl⟩ : syracuseStep 1534409 = 1150807) B1150807
theorem B453083 : Blo 451781 453083 := bstep (se 1 (by rfl) ⟨339812, by rfl⟩ : syracuseStep 453083 = 679625) B679625
theorem B682505 : Blo 451781 682505 := bstep (se 2 (by rfl) ⟨255939, by rfl⟩ : syracuseStep 682505 = 511879) B511879
theorem B453159 : Blo 451781 453159 := bstep (se 1 (by rfl) ⟨339869, by rfl⟩ : syracuseStep 453159 = 679739) B679739
theorem B682535 : Blo 451781 682535 := bstep (se 1 (by rfl) ⟨511901, by rfl⟩ : syracuseStep 682535 = 1023803) B1023803
theorem B453199 : Blo 451781 453199 := bstep (se 1 (by rfl) ⟨339899, by rfl⟩ : syracuseStep 453199 = 679799) B679799
theorem B453215 : Blo 451781 453215 := bstep (se 1 (by rfl) ⟨339911, by rfl⟩ : syracuseStep 453215 = 679823) B679823
theorem B453243 : Blo 451781 453243 := bstep (se 1 (by rfl) ⟨339932, by rfl⟩ : syracuseStep 453243 = 679865) B679865
theorem B682619 : Blo 451781 682619 := bstep (se 1 (by rfl) ⟨511964, by rfl⟩ : syracuseStep 682619 = 1023929) B1023929
theorem B453295 : Blo 451781 453295 := bstep (se 1 (by rfl) ⟨339971, by rfl⟩ : syracuseStep 453295 = 679943) B679943
theorem B453319 : Blo 451781 453319 := bstep (se 1 (by rfl) ⟨339989, by rfl⟩ : syracuseStep 453319 = 679979) B679979
theorem B1534679 : Blo 451781 1534679 := bstep (se 1 (by rfl) ⟨1151009, by rfl⟩ : syracuseStep 1534679 = 2302019) B2302019
theorem B453339 : Blo 451781 453339 := bstep (se 1 (by rfl) ⟨340004, by rfl⟩ : syracuseStep 453339 = 680009) B680009
theorem B682745 : Blo 451781 682745 := bstep (se 2 (by rfl) ⟨256029, by rfl⟩ : syracuseStep 682745 = 512059) B512059
theorem B453415 : Blo 451781 453415 := bstep (se 1 (by rfl) ⟨340061, by rfl⟩ : syracuseStep 453415 = 680123) B680123
theorem B453455 : Blo 451781 453455 := bstep (se 1 (by rfl) ⟨340091, by rfl⟩ : syracuseStep 453455 = 680183) B680183
theorem B453471 : Blo 451781 453471 := bstep (se 1 (by rfl) ⟨340103, by rfl⟩ : syracuseStep 453471 = 680207) B680207
theorem B682847 : Blo 451781 682847 := bstep (se 1 (by rfl) ⟨512135, by rfl⟩ : syracuseStep 682847 = 1024271) B1024271
theorem B682859 : Blo 451781 682859 := bstep (se 1 (by rfl) ⟨512144, by rfl⟩ : syracuseStep 682859 = 1024289) B1024289
theorem B453499 : Blo 451781 453499 := bstep (se 1 (by rfl) ⟨340124, by rfl⟩ : syracuseStep 453499 = 680249) B680249
theorem B453551 : Blo 451781 453551 := bstep (se 1 (by rfl) ⟨340163, by rfl⟩ : syracuseStep 453551 = 680327) B680327
theorem B1534895 : Blo 451781 1534895 := bstep (se 1 (by rfl) ⟨1151171, by rfl⟩ : syracuseStep 1534895 = 2302343) B2302343
theorem B453575 : Blo 451781 453575 := bstep (se 1 (by rfl) ⟨340181, by rfl⟩ : syracuseStep 453575 = 680363) B680363
theorem B453595 : Blo 451781 453595 := bstep (se 1 (by rfl) ⟨340196, by rfl⟩ : syracuseStep 453595 = 680393) B680393
theorem B453671 : Blo 451781 453671 := bstep (se 1 (by rfl) ⟨340253, by rfl⟩ : syracuseStep 453671 = 680507) B680507
theorem B453711 : Blo 451781 453711 := bstep (se 1 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 453711 = 680567) B680567
theorem B683087 : Blo 451781 683087 := bstep (se 1 (by rfl) ⟨512315, by rfl⟩ : syracuseStep 683087 = 1024631) B1024631
theorem B453727 : Blo 451781 453727 := bstep (se 1 (by rfl) ⟨340295, by rfl⟩ : syracuseStep 453727 = 680591) B680591
theorem B453755 : Blo 451781 453755 := bstep (se 1 (by rfl) ⟨340316, by rfl⟩ : syracuseStep 453755 = 680633) B680633
theorem B453807 : Blo 451781 453807 := bstep (se 1 (by rfl) ⟨340355, by rfl⟩ : syracuseStep 453807 = 680711) B680711
theorem B453831 : Blo 451781 453831 := bstep (se 1 (by rfl) ⟨340373, by rfl⟩ : syracuseStep 453831 = 680747) B680747
theorem B683207 : Blo 451781 683207 := bstep (se 1 (by rfl) ⟨512405, by rfl⟩ : syracuseStep 683207 = 1024811) B1024811
theorem B453851 : Blo 451781 453851 := bstep (se 1 (by rfl) ⟨340388, by rfl⟩ : syracuseStep 453851 = 680777) B680777
theorem B453927 : Blo 451781 453927 := bstep (se 1 (by rfl) ⟨340445, by rfl⟩ : syracuseStep 453927 = 680891) B680891
theorem B10513729 : Blo 451781 10513729 := bstep (se 2 (by rfl) ⟨3942648, by rfl⟩ : syracuseStep 10513729 = 7885297) B7885297
theorem B453967 : Blo 451781 453967 := bstep (se 1 (by rfl) ⟨340475, by rfl⟩ : syracuseStep 453967 = 680951) B680951
theorem B453983 : Blo 451781 453983 := bstep (se 1 (by rfl) ⟨340487, by rfl⟩ : syracuseStep 453983 = 680975) B680975
theorem B683369 : Blo 451781 683369 := bstep (se 2 (by rfl) ⟨256263, by rfl⟩ : syracuseStep 683369 = 512527) B512527
theorem B454011 : Blo 451781 454011 := bstep (se 1 (by rfl) ⟨340508, by rfl⟩ : syracuseStep 454011 = 681017) B681017
theorem B454063 : Blo 451781 454063 := bstep (se 1 (by rfl) ⟨340547, by rfl⟩ : syracuseStep 454063 = 681095) B681095
theorem B814519 : Blo 451781 814519 := bstep (se 1 (by rfl) ⟨610889, by rfl⟩ : syracuseStep 814519 = 1221779) B1221779
theorem B683447 : Blo 451781 683447 := bstep (se 1 (by rfl) ⟨512585, by rfl⟩ : syracuseStep 683447 = 1025171) B1025171
theorem B454087 : Blo 451781 454087 := bstep (se 1 (by rfl) ⟨340565, by rfl⟩ : syracuseStep 454087 = 681131) B681131
theorem B454107 : Blo 451781 454107 := bstep (se 1 (by rfl) ⟨340580, by rfl⟩ : syracuseStep 454107 = 681161) B681161
theorem B683483 : Blo 451781 683483 := bstep (se 1 (by rfl) ⟨512612, by rfl⟩ : syracuseStep 683483 = 1025225) B1025225
theorem B3436019 : Blo 451781 3436019 := bstep (se 1 (by rfl) ⟨2577014, by rfl⟩ : syracuseStep 3436019 = 5154029) B5154029
theorem B454183 : Blo 451781 454183 := bstep (se 1 (by rfl) ⟨340637, by rfl⟩ : syracuseStep 454183 = 681275) B681275
theorem B3501629 : Blo 451781 3501629 := bstep (se 3 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 3501629 = 1313111) B1313111
theorem B454223 : Blo 451781 454223 := bstep (se 1 (by rfl) ⟨340667, by rfl⟩ : syracuseStep 454223 = 681335) B681335
theorem B454239 : Blo 451781 454239 := bstep (se 1 (by rfl) ⟨340679, by rfl⟩ : syracuseStep 454239 = 681359) B681359
theorem B454267 : Blo 451781 454267 := bstep (se 1 (by rfl) ⟨340700, by rfl⟩ : syracuseStep 454267 = 681401) B681401
theorem B5828219 : Blo 451781 5828219 := bstep (se 1 (by rfl) ⟨4371164, by rfl⟩ : syracuseStep 5828219 = 8742329) B8742329
theorem B454319 : Blo 451781 454319 := bstep (se 1 (by rfl) ⟨340739, by rfl⟩ : syracuseStep 454319 = 681479) B681479
theorem B454343 : Blo 451781 454343 := bstep (se 1 (by rfl) ⟨340757, by rfl⟩ : syracuseStep 454343 = 681515) B681515
theorem B7728857 : Blo 451781 7728857 := bstep (se 2 (by rfl) ⟨2898321, by rfl⟩ : syracuseStep 7728857 = 5796643) B5796643
theorem B454363 : Blo 451781 454363 := bstep (se 1 (by rfl) ⟨340772, by rfl⟩ : syracuseStep 454363 = 681545) B681545
theorem B454439 : Blo 451781 454439 := bstep (se 1 (by rfl) ⟨340829, by rfl⟩ : syracuseStep 454439 = 681659) B681659
theorem B2453291 : Blo 451781 2453291 := bstep (se 1 (by rfl) ⟨1839968, by rfl⟩ : syracuseStep 2453291 = 3679937) B3679937
theorem B454479 : Blo 451781 454479 := bstep (se 1 (by rfl) ⟨340859, by rfl⟩ : syracuseStep 454479 = 681719) B681719
theorem B454495 : Blo 451781 454495 := bstep (se 1 (by rfl) ⟨340871, by rfl⟩ : syracuseStep 454495 = 681743) B681743
theorem B454523 : Blo 451781 454523 := bstep (se 1 (by rfl) ⟨340892, by rfl⟩ : syracuseStep 454523 = 681785) B681785
theorem B454575 : Blo 451781 454575 := bstep (se 1 (by rfl) ⟨340931, by rfl⟩ : syracuseStep 454575 = 681863) B681863
theorem B4157369 : Blo 451781 4157369 := bstep (se 2 (by rfl) ⟨1559013, by rfl⟩ : syracuseStep 4157369 = 3118027) B3118027
theorem B3665857 : Blo 451781 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B454599 : Blo 451781 454599 := bstep (se 1 (by rfl) ⟨340949, by rfl⟩ : syracuseStep 454599 = 681899) B681899
theorem B454619 : Blo 451781 454619 := bstep (se 1 (by rfl) ⟨340964, by rfl⟩ : syracuseStep 454619 = 681929) B681929
theorem B815111 : Blo 451781 815111 := bstep (se 1 (by rfl) ⟨611333, by rfl⟩ : syracuseStep 815111 = 1222667) B1222667
theorem B454695 : Blo 451781 454695 := bstep (se 1 (by rfl) ⟨341021, by rfl⟩ : syracuseStep 454695 = 682043) B682043
theorem B454735 : Blo 451781 454735 := bstep (se 1 (by rfl) ⟨341051, by rfl⟩ : syracuseStep 454735 = 682103) B682103
theorem B454751 : Blo 451781 454751 := bstep (se 1 (by rfl) ⟨341063, by rfl⟩ : syracuseStep 454751 = 682127) B682127
theorem B454779 : Blo 451781 454779 := bstep (se 1 (by rfl) ⟨341084, by rfl⟩ : syracuseStep 454779 = 682169) B682169
theorem B454831 : Blo 451781 454831 := bstep (se 1 (by rfl) ⟨341123, by rfl⟩ : syracuseStep 454831 = 682247) B682247
theorem B454855 : Blo 451781 454855 := bstep (se 1 (by rfl) ⟨341141, by rfl⟩ : syracuseStep 454855 = 682283) B682283
theorem B454875 : Blo 451781 454875 := bstep (se 1 (by rfl) ⟨341156, by rfl⟩ : syracuseStep 454875 = 682313) B682313
theorem B454951 : Blo 451781 454951 := bstep (se 1 (by rfl) ⟨341213, by rfl⟩ : syracuseStep 454951 = 682427) B682427
theorem B454991 : Blo 451781 454991 := bstep (se 1 (by rfl) ⟨341243, by rfl⟩ : syracuseStep 454991 = 682487) B682487
theorem B455007 : Blo 451781 455007 := bstep (se 1 (by rfl) ⟨341255, by rfl⟩ : syracuseStep 455007 = 682511) B682511
theorem B455035 : Blo 451781 455035 := bstep (se 1 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 455035 = 682553) B682553
theorem B1634689 : Blo 451781 1634689 := bstep (se 2 (by rfl) ⟨613008, by rfl⟩ : syracuseStep 1634689 = 1226017) B1226017
theorem B455087 : Blo 451781 455087 := bstep (se 1 (by rfl) ⟨341315, by rfl⟩ : syracuseStep 455087 = 682631) B682631
theorem B455111 : Blo 451781 455111 := bstep (se 1 (by rfl) ⟨341333, by rfl⟩ : syracuseStep 455111 = 682667) B682667
theorem B455131 : Blo 451781 455131 := bstep (se 1 (by rfl) ⟨341348, by rfl⟩ : syracuseStep 455131 = 682697) B682697
theorem B455207 : Blo 451781 455207 := bstep (se 1 (by rfl) ⟨341405, by rfl⟩ : syracuseStep 455207 = 682811) B682811
theorem B455247 : Blo 451781 455247 := bstep (se 1 (by rfl) ⟨341435, by rfl⟩ : syracuseStep 455247 = 682871) B682871
theorem B455263 : Blo 451781 455263 := bstep (se 1 (by rfl) ⟨341447, by rfl⟩ : syracuseStep 455263 = 682895) B682895
theorem B455291 : Blo 451781 455291 := bstep (se 1 (by rfl) ⟨341468, by rfl⟩ : syracuseStep 455291 = 682937) B682937
theorem B455343 : Blo 451781 455343 := bstep (se 1 (by rfl) ⟨341507, by rfl⟩ : syracuseStep 455343 = 683015) B683015
theorem B455367 : Blo 451781 455367 := bstep (se 1 (by rfl) ⟨341525, by rfl⟩ : syracuseStep 455367 = 683051) B683051
theorem B455387 : Blo 451781 455387 := bstep (se 1 (by rfl) ⟨341540, by rfl⟩ : syracuseStep 455387 = 683081) B683081
theorem B1930013 : Blo 451781 1930013 := bstep (se 3 (by rfl) ⟨361877, by rfl⟩ : syracuseStep 1930013 = 723755) B723755
theorem B455463 : Blo 451781 455463 := bstep (se 1 (by rfl) ⟨341597, by rfl⟩ : syracuseStep 455463 = 683195) B683195
theorem B455503 : Blo 451781 455503 := bstep (se 1 (by rfl) ⟨341627, by rfl⟩ : syracuseStep 455503 = 683255) B683255
theorem B455519 : Blo 451781 455519 := bstep (se 1 (by rfl) ⟨341639, by rfl⟩ : syracuseStep 455519 = 683279) B683279
theorem B1143659 : Blo 451781 1143659 := bstep (se 1 (by rfl) ⟨857744, by rfl⟩ : syracuseStep 1143659 = 1715489) B1715489
theorem B455547 : Blo 451781 455547 := bstep (se 1 (by rfl) ⟨341660, by rfl⟩ : syracuseStep 455547 = 683321) B683321
theorem B455599 : Blo 451781 455599 := bstep (se 1 (by rfl) ⟨341699, by rfl⟩ : syracuseStep 455599 = 683399) B683399
theorem B455623 : Blo 451781 455623 := bstep (se 1 (by rfl) ⟨341717, by rfl⟩ : syracuseStep 455623 = 683435) B683435
theorem B455643 : Blo 451781 455643 := bstep (se 1 (by rfl) ⟨341732, by rfl⟩ : syracuseStep 455643 = 683465) B683465
theorem B455719 : Blo 451781 455719 := bstep (se 1 (by rfl) ⟨341789, by rfl⟩ : syracuseStep 455719 = 683579) B683579
theorem B455759 : Blo 451781 455759 := bstep (se 1 (by rfl) ⟨341819, by rfl⟩ : syracuseStep 455759 = 683639) B683639
theorem B455775 : Blo 451781 455775 := bstep (se 1 (by rfl) ⟨341831, by rfl⟩ : syracuseStep 455775 = 683663) B683663
theorem B2290841 : Blo 451781 2290841 := bstep (se 2 (by rfl) ⟨859065, by rfl⟩ : syracuseStep 2290841 = 1718131) B1718131
theorem B1537271 : Blo 451781 1537271 := bstep (se 1 (by rfl) ⟨1152953, by rfl⟩ : syracuseStep 1537271 = 2305907) B2305907
theorem B2618825 : Blo 451781 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B1144307 : Blo 451781 1144307 := bstep (se 1 (by rfl) ⟨858230, by rfl⟩ : syracuseStep 1144307 = 1716461) B1716461
theorem B2913803 : Blo 451781 2913803 := bstep (se 1 (by rfl) ⟨2185352, by rfl⟩ : syracuseStep 2913803 = 4370705) B4370705
theorem B1537595 : Blo 451781 1537595 := bstep (se 1 (by rfl) ⟨1153196, by rfl⟩ : syracuseStep 1537595 = 2306393) B2306393
theorem B35452673 : Blo 451781 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B1537865 : Blo 451781 1537865 := bstep (se 2 (by rfl) ⟨576699, by rfl⟩ : syracuseStep 1537865 = 1153399) B1153399
theorem B2062189 : Blo 451781 2062189 := bstep (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) B773321
theorem B817057 : Blo 451781 817057 := bstep (se 2 (by rfl) ⟨306396, by rfl⟩ : syracuseStep 817057 = 612793) B612793
theorem B1144763 : Blo 451781 1144763 := bstep (se 1 (by rfl) ⟨858572, by rfl⟩ : syracuseStep 1144763 = 1717145) B1717145
theorem B8976541 : Blo 451781 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B169834765 : Blo 451781 169834765 := bstep (se 3 (by rfl) ⟨31844018, by rfl⟩ : syracuseStep 169834765 = 63688037) B63688037
theorem B3438935 : Blo 451781 3438935 := bstep (se 1 (by rfl) ⟨2579201, by rfl⟩ : syracuseStep 3438935 = 5158403) B5158403
theorem B817627 : Blo 451781 817627 := bstep (se 1 (by rfl) ⟨613220, by rfl⟩ : syracuseStep 817627 = 1226441) B1226441
theorem B1145441 : Blo 451781 1145441 := bstep (se 2 (by rfl) ⟨429540, by rfl⟩ : syracuseStep 1145441 = 859081) B859081
theorem B18611279 : Blo 451781 18611279 := bstep (se 1 (by rfl) ⟨13958459, by rfl⟩ : syracuseStep 18611279 = 27916919) B27916919
theorem B181140941 : Blo 451781 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B8749093 : Blo 451781 8749093 := bstep (se 4 (by rfl) ⟨820227, by rfl⟩ : syracuseStep 8749093 = 1640455) B1640455
theorem B1147243 : Blo 451781 1147243 := bstep (se 1 (by rfl) ⟨860432, by rfl⟩ : syracuseStep 1147243 = 1720865) B1720865
theorem B52986329 : Blo 451781 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B1933787 : Blo 451781 1933787 := bstep (se 1 (by rfl) ⟨1450340, by rfl⟩ : syracuseStep 1933787 = 2900681) B2900681
theorem B1147567 : Blo 451781 1147567 := bstep (se 1 (by rfl) ⟨860675, by rfl⟩ : syracuseStep 1147567 = 1721351) B1721351
theorem B656047 : Blo 451781 656047 := bstep (se 1 (by rfl) ⟨492035, by rfl⟩ : syracuseStep 656047 = 984071) B984071
theorem B1016567 : Blo 451781 1016567 := bstep (se 1 (by rfl) ⟨762425, by rfl⟩ : syracuseStep 1016567 = 1524851) B1524851
theorem B1016747 : Blo 451781 1016747 := bstep (se 1 (by rfl) ⟨762560, by rfl⟩ : syracuseStep 1016747 = 1525121) B1525121
theorem B2294729 : Blo 451781 2294729 := bstep (se 2 (by rfl) ⟨860523, by rfl⟩ : syracuseStep 2294729 = 1721047) B1721047
theorem B1147891 : Blo 451781 1147891 := bstep (se 1 (by rfl) ⟨860918, by rfl⟩ : syracuseStep 1147891 = 1721837) B1721837
theorem B1246603 : Blo 451781 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B1017287 : Blo 451781 1017287 := bstep (se 1 (by rfl) ⟨762965, by rfl⟩ : syracuseStep 1017287 = 1525931) B1525931
theorem B11044471 : Blo 451781 11044471 := bstep (se 1 (by rfl) ⟨8283353, by rfl⟩ : syracuseStep 11044471 = 16566707) B16566707
theorem B1148651 : Blo 451781 1148651 := bstep (se 1 (by rfl) ⟨861488, by rfl⟩ : syracuseStep 1148651 = 1722977) B1722977
theorem B18876203 : Blo 451781 18876203 := bstep (se 1 (by rfl) ⟨14157152, by rfl⟩ : syracuseStep 18876203 = 28314305) B28314305
theorem B1017647 : Blo 451781 1017647 := bstep (se 1 (by rfl) ⟨763235, by rfl⟩ : syracuseStep 1017647 = 1526471) B1526471
theorem B1018223 : Blo 451781 1018223 := bstep (se 1 (by rfl) ⟨763667, by rfl⟩ : syracuseStep 1018223 = 1527335) B1527335
theorem B3541391 : Blo 451781 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B1018295 : Blo 451781 1018295 := bstep (se 1 (by rfl) ⟨763721, by rfl⟩ : syracuseStep 1018295 = 1527443) B1527443
theorem B1018439 : Blo 451781 1018439 := bstep (se 1 (by rfl) ⟨763829, by rfl⟩ : syracuseStep 1018439 = 1527659) B1527659
theorem B1149511 : Blo 451781 1149511 := bstep (se 1 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 1149511 = 1724267) B1724267
theorem B1018475 : Blo 451781 1018475 := bstep (se 1 (by rfl) ⟨763856, by rfl⟩ : syracuseStep 1018475 = 1527713) B1527713
theorem B1149623 : Blo 451781 1149623 := bstep (se 1 (by rfl) ⟨862217, by rfl⟩ : syracuseStep 1149623 = 1724435) B1724435
theorem B2919235 : Blo 451781 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B1936315 : Blo 451781 1936315 := bstep (se 1 (by rfl) ⟨1452236, by rfl⟩ : syracuseStep 1936315 = 2904473) B2904473
theorem B920551 : Blo 451781 920551 := bstep (se 1 (by rfl) ⟨690413, by rfl⟩ : syracuseStep 920551 = 1380827) B1380827
theorem B1018871 : Blo 451781 1018871 := bstep (se 1 (by rfl) ⟨764153, by rfl⟩ : syracuseStep 1018871 = 1528307) B1528307
theorem B4197491 : Blo 451781 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B1019231 : Blo 451781 1019231 := bstep (se 1 (by rfl) ⟨764423, by rfl⟩ : syracuseStep 1019231 = 1528847) B1528847
theorem B11079301 : Blo 451781 11079301 := bstep (se 4 (by rfl) ⟨1038684, by rfl⟩ : syracuseStep 11079301 = 2077369) B2077369
theorem B1150625 : Blo 451781 1150625 := bstep (se 2 (by rfl) ⟨431484, by rfl⟩ : syracuseStep 1150625 = 862969) B862969
theorem B3870443 : Blo 451781 3870443 := bstep (se 1 (by rfl) ⟨2902832, by rfl⟩ : syracuseStep 3870443 = 5805665) B5805665
theorem B1019627 : Blo 451781 1019627 := bstep (se 1 (by rfl) ⟨764720, by rfl⟩ : syracuseStep 1019627 = 1529441) B1529441
theorem B1019753 : Blo 451781 1019753 := bstep (se 2 (by rfl) ⟨382407, by rfl⟩ : syracuseStep 1019753 = 764815) B764815
theorem B6983533 : Blo 451781 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B1151081 : Blo 451781 1151081 := bstep (se 2 (by rfl) ⟨431655, by rfl⟩ : syracuseStep 1151081 = 863311) B863311
theorem B2363755 : Blo 451781 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B6558083 : Blo 451781 6558083 := bstep (se 1 (by rfl) ⟨4918562, by rfl⟩ : syracuseStep 6558083 = 9837125) B9837125
theorem B1151567 : Blo 451781 1151567 := bstep (se 1 (by rfl) ⟨863675, by rfl⟩ : syracuseStep 1151567 = 1727351) B1727351
theorem B1020599 : Blo 451781 1020599 := bstep (se 1 (by rfl) ⟨765449, by rfl⟩ : syracuseStep 1020599 = 1530899) B1530899
theorem B2298617 : Blo 451781 2298617 := bstep (se 2 (by rfl) ⟨861981, by rfl⟩ : syracuseStep 2298617 = 1723963) B1723963
theorem B8262479 : Blo 451781 8262479 := bstep (se 1 (by rfl) ⟨6196859, by rfl⟩ : syracuseStep 8262479 = 12393719) B12393719
theorem B2069327 : Blo 451781 2069327 := bstep (se 1 (by rfl) ⟨1551995, by rfl⟩ : syracuseStep 2069327 = 3103991) B3103991
theorem B1020815 : Blo 451781 1020815 := bstep (se 1 (by rfl) ⟨765611, by rfl⟩ : syracuseStep 1020815 = 1531223) B1531223
theorem B2626505 : Blo 451781 2626505 := bstep (se 2 (by rfl) ⟨984939, by rfl⟩ : syracuseStep 2626505 = 1969879) B1969879
theorem B3282065 : Blo 451781 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B1152215 : Blo 451781 1152215 := bstep (se 1 (by rfl) ⟨864161, by rfl⟩ : syracuseStep 1152215 = 1728323) B1728323
theorem B4887809 : Blo 451781 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B1152569 : Blo 451781 1152569 := bstep (se 2 (by rfl) ⟨432213, by rfl⟩ : syracuseStep 1152569 = 864427) B864427
theorem B1021535 : Blo 451781 1021535 := bstep (se 1 (by rfl) ⟨766151, by rfl⟩ : syracuseStep 1021535 = 1532303) B1532303
theorem B1021751 : Blo 451781 1021751 := bstep (se 1 (by rfl) ⟨766313, by rfl⟩ : syracuseStep 1021751 = 1532627) B1532627
theorem B1022057 : Blo 451781 1022057 := bstep (se 2 (by rfl) ⟨383271, by rfl⟩ : syracuseStep 1022057 = 766543) B766543
theorem B1448189 : Blo 451781 1448189 := bstep (se 3 (by rfl) ⟨271535, by rfl⟩ : syracuseStep 1448189 = 543071) B543071
theorem B1382665 : Blo 451781 1382665 := bstep (se 2 (by rfl) ⟨518499, by rfl⟩ : syracuseStep 1382665 = 1036999) B1036999
theorem B2595401 : Blo 451781 2595401 := bstep (se 2 (by rfl) ⟨973275, by rfl⟩ : syracuseStep 2595401 = 1946551) B1946551
theorem B1022543 : Blo 451781 1022543 := bstep (se 1 (by rfl) ⟨766907, by rfl⟩ : syracuseStep 1022543 = 1533815) B1533815
theorem B1940075 : Blo 451781 1940075 := bstep (se 1 (by rfl) ⟨1455056, by rfl⟩ : syracuseStep 1940075 = 2910113) B2910113
theorem B3873419 : Blo 451781 3873419 := bstep (se 1 (by rfl) ⟨2905064, by rfl⟩ : syracuseStep 3873419 = 5810129) B5810129
theorem B1022687 : Blo 451781 1022687 := bstep (se 1 (by rfl) ⟨767015, by rfl⟩ : syracuseStep 1022687 = 1534031) B1534031
theorem B858899 : Blo 451781 858899 := bstep (se 1 (by rfl) ⟨644174, by rfl⟩ : syracuseStep 858899 = 1288349) B1288349
theorem B1022939 : Blo 451781 1022939 := bstep (se 1 (by rfl) ⟨767204, by rfl⟩ : syracuseStep 1022939 = 1534409) B1534409
theorem B1023119 : Blo 451781 1023119 := bstep (se 1 (by rfl) ⟨767339, by rfl⟩ : syracuseStep 1023119 = 1534679) B1534679
theorem B1023209 : Blo 451781 1023209 := bstep (se 2 (by rfl) ⟨383703, by rfl⟩ : syracuseStep 1023209 = 767407) B767407
theorem B859423 : Blo 451781 859423 := bstep (se 1 (by rfl) ⟨644567, by rfl⟩ : syracuseStep 859423 = 1289135) B1289135
theorem B1023263 : Blo 451781 1023263 := bstep (se 1 (by rfl) ⟨767447, by rfl⟩ : syracuseStep 1023263 = 1534895) B1534895
theorem B2301371 : Blo 451781 2301371 := bstep (se 1 (by rfl) ⟨1726028, by rfl⟩ : syracuseStep 2301371 = 3452057) B3452057
theorem B2334419 : Blo 451781 2334419 := bstep (se 1 (by rfl) ⟨1750814, by rfl⟩ : syracuseStep 2334419 = 3501629) B3501629
theorem B8724185 : Blo 451781 8724185 := bstep (se 2 (by rfl) ⟨3271569, by rfl⟩ : syracuseStep 8724185 = 6543139) B6543139
theorem B1023785 : Blo 451781 1023785 := bstep (se 2 (by rfl) ⟨383919, by rfl⟩ : syracuseStep 1023785 = 767839) B767839
theorem B5152571 : Blo 451781 5152571 := bstep (se 1 (by rfl) ⟨3864428, by rfl⟩ : syracuseStep 5152571 = 7728857) B7728857
theorem B1089409 : Blo 451781 1089409 := bstep (se 2 (by rfl) ⟨408528, by rfl⟩ : syracuseStep 1089409 = 817057) B817057
theorem B4923443 : Blo 451781 4923443 := bstep (se 1 (by rfl) ⟨3692582, by rfl⟩ : syracuseStep 4923443 = 7385165) B7385165
theorem B11968721 : Blo 451781 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B1286675 : Blo 451781 1286675 := bstep (se 1 (by rfl) ⟨965006, by rfl⟩ : syracuseStep 1286675 = 1930013) B1930013
theorem B762439 : Blo 451781 762439 := bstep (se 1 (by rfl) ⟨571829, by rfl⟩ : syracuseStep 762439 = 1143659) B1143659
theorem B1090169 : Blo 451781 1090169 := bstep (se 2 (by rfl) ⟨408813, by rfl⟩ : syracuseStep 1090169 = 817627) B817627
theorem B1450649 : Blo 451781 1450649 := bstep (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) B1087987
theorem B2302667 : Blo 451781 2302667 := bstep (se 1 (by rfl) ⟨1727000, by rfl⟩ : syracuseStep 2302667 = 3454001) B3454001
theorem B17703629 : Blo 451781 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B1024847 : Blo 451781 1024847 := bstep (se 1 (by rfl) ⟨768635, by rfl⟩ : syracuseStep 1024847 = 1537271) B1537271
theorem B2302829 : Blo 451781 2302829 := bstep (se 3 (by rfl) ⟨431780, by rfl⟩ : syracuseStep 2302829 = 863561) B863561
theorem B762871 : Blo 451781 762871 := bstep (se 1 (by rfl) ⟨572153, by rfl⟩ : syracuseStep 762871 = 1144307) B1144307
theorem B1942535 : Blo 451781 1942535 := bstep (se 1 (by rfl) ⟨1456901, by rfl⟩ : syracuseStep 1942535 = 2913803) B2913803
theorem B1025063 : Blo 451781 1025063 := bstep (se 1 (by rfl) ⟨768797, by rfl⟩ : syracuseStep 1025063 = 1537595) B1537595
theorem B23635115 : Blo 451781 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B1025243 : Blo 451781 1025243 := bstep (se 1 (by rfl) ⟨768932, by rfl⟩ : syracuseStep 1025243 = 1537865) B1537865
theorem B763175 : Blo 451781 763175 := bstep (se 1 (by rfl) ⟨572381, by rfl⟩ : syracuseStep 763175 = 1144763) B1144763
theorem B1451303 : Blo 451781 1451303 := bstep (se 1 (by rfl) ⟨1088477, by rfl⟩ : syracuseStep 1451303 = 2176955) B2176955
theorem B1025441 : Blo 451781 1025441 := bstep (se 2 (by rfl) ⟨384540, by rfl⟩ : syracuseStep 1025441 = 769081) B769081
theorem B4138685 : Blo 451781 4138685 := bstep (se 3 (by rfl) ⟨776003, by rfl⟩ : syracuseStep 4138685 = 1552007) B1552007
theorem B763627 : Blo 451781 763627 := bstep (se 1 (by rfl) ⟨572720, by rfl⟩ : syracuseStep 763627 = 1145441) B1145441
theorem B4925261 : Blo 451781 4925261 := bstep (se 3 (by rfl) ⟨923486, by rfl⟩ : syracuseStep 4925261 = 1846973) B1846973
theorem B1550465 : Blo 451781 1550465 := bstep (se 2 (by rfl) ⟨581424, by rfl⟩ : syracuseStep 1550465 = 1162849) B1162849
theorem B1452161 : Blo 451781 1452161 := bstep (se 2 (by rfl) ⟨544560, by rfl⟩ : syracuseStep 1452161 = 1089121) B1089121
theorem B2763017 : Blo 451781 2763017 := bstep (se 2 (by rfl) ⟨1036131, by rfl⟩ : syracuseStep 2763017 = 2072263) B2072263
theorem B1943833 : Blo 451781 1943833 := bstep (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) B1457875
theorem B120760627 : Blo 451781 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B6302063 : Blo 451781 6302063 := bstep (se 1 (by rfl) ⟨4726547, by rfl⟩ : syracuseStep 6302063 = 9453095) B9453095
theorem B2173513 : Blo 451781 2173513 := bstep (se 2 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 2173513 = 1630135) B1630135
theorem B764599 : Blo 451781 764599 := bstep (se 1 (by rfl) ⟨573449, by rfl⟩ : syracuseStep 764599 = 1146899) B1146899
theorem B2206403 : Blo 451781 2206403 := bstep (se 1 (by rfl) ⟨1654802, by rfl⟩ : syracuseStep 2206403 = 3309605) B3309605
theorem B1747855 : Blo 451781 1747855 := bstep (se 1 (by rfl) ⟨1310891, by rfl⟩ : syracuseStep 1747855 = 2621783) B2621783
theorem B1092523 : Blo 451781 1092523 := bstep (se 1 (by rfl) ⟨819392, by rfl⟩ : syracuseStep 1092523 = 1638785) B1638785
theorem B764903 : Blo 451781 764903 := bstep (se 1 (by rfl) ⟨573677, by rfl⟩ : syracuseStep 764903 = 1147355) B1147355
theorem B29470067 : Blo 451781 29470067 := bstep (se 1 (by rfl) ⟨22102550, by rfl⟩ : syracuseStep 29470067 = 44205101) B44205101
theorem B2895223 : Blo 451781 2895223 := bstep (se 1 (by rfl) ⟨2171417, by rfl⟩ : syracuseStep 2895223 = 4342835) B4342835
theorem B2305745 : Blo 451781 2305745 := bstep (se 2 (by rfl) ⟨864654, by rfl⟩ : syracuseStep 2305745 = 1729309) B1729309
theorem B1715975 : Blo 451781 1715975 := bstep (se 1 (by rfl) ⟨1286981, by rfl⟩ : syracuseStep 1715975 = 2573963) B2573963
theorem B864047 : Blo 451781 864047 := bstep (se 1 (by rfl) ⟨648035, by rfl⟩ : syracuseStep 864047 = 1296071) B1296071
theorem B766057 : Blo 451781 766057 := bstep (se 2 (by rfl) ⟨287271, by rfl⟩ : syracuseStep 766057 = 574543) B574543
theorem B4141313 : Blo 451781 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B1290923 : Blo 451781 1290923 := bstep (se 1 (by rfl) ⟨968192, by rfl⟩ : syracuseStep 1290923 = 1936385) B1936385
theorem B4895417 : Blo 451781 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B865255 : Blo 451781 865255 := bstep (se 1 (by rfl) ⟨648941, by rfl⟩ : syracuseStep 865255 = 1297883) B1297883
theorem B1717463 : Blo 451781 1717463 := bstep (se 1 (by rfl) ⟨1288097, by rfl⟩ : syracuseStep 1717463 = 2576195) B2576195
theorem B1455403 : Blo 451781 1455403 := bstep (se 1 (by rfl) ⟨1091552, by rfl⟩ : syracuseStep 1455403 = 2183105) B2183105
theorem B11056925 : Blo 451781 11056925 := bstep (se 3 (by rfl) ⟨2073173, by rfl⟩ : syracuseStep 11056925 = 4146347) B4146347
theorem B767785 : Blo 451781 767785 := bstep (se 2 (by rfl) ⟨287919, by rfl⟩ : syracuseStep 767785 = 575839) B575839
theorem B768575 : Blo 451781 768575 := bstep (se 1 (by rfl) ⟨576431, by rfl⟩ : syracuseStep 768575 = 1152863) B1152863
theorem B1718891 : Blo 451781 1718891 := bstep (se 1 (by rfl) ⟨1289168, by rfl⟩ : syracuseStep 1718891 = 2578337) B2578337
theorem B4209515 : Blo 451781 4209515 := bstep (se 1 (by rfl) ⟨3157136, by rfl⟩ : syracuseStep 4209515 = 6314273) B6314273
theorem B7388279 : Blo 451781 7388279 := bstep (se 1 (by rfl) ⟨5541209, by rfl⟩ : syracuseStep 7388279 = 11082419) B11082419
theorem B4308299 : Blo 451781 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B572923 : Blo 451781 572923 := bstep (se 1 (by rfl) ⟨429692, by rfl⟩ : syracuseStep 572923 = 859385) B859385
theorem B1293907 : Blo 451781 1293907 := bstep (se 1 (by rfl) ⟨970430, by rfl⟩ : syracuseStep 1293907 = 1940861) B1940861
theorem B966305 : Blo 451781 966305 := bstep (se 2 (by rfl) ⟨362364, by rfl⟩ : syracuseStep 966305 = 724729) B724729
theorem B573151 : Blo 451781 573151 := bstep (se 1 (by rfl) ⟨429863, by rfl⟩ : syracuseStep 573151 = 859727) B859727
theorem B1720075 : Blo 451781 1720075 := bstep (se 1 (by rfl) ⟨1290056, by rfl⟩ : syracuseStep 1720075 = 2580113) B2580113
theorem B1720379 : Blo 451781 1720379 := bstep (se 1 (by rfl) ⟨1290284, by rfl⟩ : syracuseStep 1720379 = 2580569) B2580569
theorem B573895 : Blo 451781 573895 := bstep (se 1 (by rfl) ⟨430421, by rfl⟩ : syracuseStep 573895 = 860843) B860843
theorem B1327585 : Blo 451781 1327585 := bstep (se 2 (by rfl) ⟨497844, by rfl⟩ : syracuseStep 1327585 = 995689) B995689
theorem B2179585 : Blo 451781 2179585 := bstep (se 2 (by rfl) ⟨817344, by rfl⟩ : syracuseStep 2179585 = 1634689) B1634689
theorem B7455415 : Blo 451781 7455415 := bstep (se 1 (by rfl) ⟨5591561, by rfl⟩ : syracuseStep 7455415 = 11183123) B11183123
theorem B508639 : Blo 451781 508639 := bstep (se 1 (by rfl) ⟨381479, by rfl⟩ : syracuseStep 508639 = 762959) B762959
theorem B1295183 : Blo 451781 1295183 := bstep (se 1 (by rfl) ⟨971387, by rfl⟩ : syracuseStep 1295183 = 1942775) B1942775
theorem B1164251 : Blo 451781 1164251 := bstep (se 1 (by rfl) ⟨873188, by rfl⟩ : syracuseStep 1164251 = 1746377) B1746377
theorem B509215 : Blo 451781 509215 := bstep (se 1 (by rfl) ⟨381911, by rfl⟩ : syracuseStep 509215 = 763823) B763823
theorem B4376051 : Blo 451781 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B509503 : Blo 451781 509503 := bstep (se 1 (by rfl) ⟨382127, by rfl⟩ : syracuseStep 509503 = 764255) B764255
theorem B575039 : Blo 451781 575039 := bstep (se 1 (by rfl) ⟨431279, by rfl⟩ : syracuseStep 575039 = 862559) B862559
theorem B968287 : Blo 451781 968287 := bstep (se 1 (by rfl) ⟨726215, by rfl⟩ : syracuseStep 968287 = 1452431) B1452431
theorem B8734331 : Blo 451781 8734331 := bstep (se 1 (by rfl) ⟨6550748, by rfl⟩ : syracuseStep 8734331 = 13101497) B13101497
theorem B4344101 : Blo 451781 4344101 := bstep (se 4 (by rfl) ⟨407259, by rfl⟩ : syracuseStep 4344101 = 814519) B814519
theorem B510331 : Blo 451781 510331 := bstep (se 1 (by rfl) ⟨382748, by rfl⟩ : syracuseStep 510331 = 765497) B765497
theorem B3885479 : Blo 451781 3885479 := bstep (se 1 (by rfl) ⟨2914109, by rfl⟩ : syracuseStep 3885479 = 5828219) B5828219
theorem B1296823 : Blo 451781 1296823 := bstep (se 1 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 1296823 = 1945235) B1945235
theorem B969337 : Blo 451781 969337 := bstep (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) B727003
theorem B2771579 : Blo 451781 2771579 := bstep (se 1 (by rfl) ⟨2078684, by rfl⟩ : syracuseStep 2771579 = 4157369) B4157369
theorem B543407 : Blo 451781 543407 := bstep (se 1 (by rfl) ⟨407555, by rfl⟩ : syracuseStep 543407 = 815111) B815111
theorem B969491 : Blo 451781 969491 := bstep (se 1 (by rfl) ⟨727118, by rfl⟩ : syracuseStep 969491 = 1454237) B1454237
theorem B510799 : Blo 451781 510799 := bstep (se 1 (by rfl) ⟨383099, by rfl⟩ : syracuseStep 510799 = 766199) B766199
theorem B576335 : Blo 451781 576335 := bstep (se 1 (by rfl) ⟨432251, by rfl⟩ : syracuseStep 576335 = 864503) B864503
theorem B576487 : Blo 451781 576487 := bstep (se 1 (by rfl) ⟨432365, by rfl⟩ : syracuseStep 576487 = 864731) B864731
theorem B226446353 : Blo 451781 226446353 := bstep (se 2 (by rfl) ⟨84917382, by rfl⟩ : syracuseStep 226446353 = 169834765) B169834765
theorem B7720109 : Blo 451781 7720109 := bstep (se 3 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 7720109 = 2895041) B2895041
theorem B5164235 : Blo 451781 5164235 := bstep (se 1 (by rfl) ⟨3873176, by rfl⟩ : syracuseStep 5164235 = 7746353) B7746353
theorem B511195 : Blo 451781 511195 := bstep (se 1 (by rfl) ⟨383396, by rfl⟩ : syracuseStep 511195 = 766793) B766793
theorem B7785719 : Blo 451781 7785719 := bstep (se 1 (by rfl) ⟨5839289, by rfl⟩ : syracuseStep 7785719 = 11678579) B11678579
theorem B1527227 : Blo 451781 1527227 := bstep (se 1 (by rfl) ⟨1145420, by rfl⟩ : syracuseStep 1527227 = 2290841) B2290841
theorem B511483 : Blo 451781 511483 := bstep (se 1 (by rfl) ⟨383612, by rfl⟩ : syracuseStep 511483 = 767225) B767225
theorem B511663 : Blo 451781 511663 := bstep (se 1 (by rfl) ⟨383747, by rfl⟩ : syracuseStep 511663 = 767495) B767495
theorem B511951 : Blo 451781 511951 := bstep (se 1 (by rfl) ⟨383963, by rfl⟩ : syracuseStep 511951 = 767927) B767927
theorem B2937035 : Blo 451781 2937035 := bstep (se 1 (by rfl) ⟨2202776, by rfl⟩ : syracuseStep 2937035 = 4405553) B4405553
theorem B512347 : Blo 451781 512347 := bstep (se 1 (by rfl) ⟨384260, by rfl⟩ : syracuseStep 512347 = 768521) B768521
theorem B971183 : Blo 451781 971183 := bstep (se 1 (by rfl) ⟨728387, by rfl⟩ : syracuseStep 971183 = 1456775) B1456775
theorem B512455 : Blo 451781 512455 := bstep (se 1 (by rfl) ⟨384341, by rfl⟩ : syracuseStep 512455 = 768683) B768683
theorem B10998341 : Blo 451781 10998341 := bstep (se 4 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 10998341 = 2062189) B2062189
theorem B12407519 : Blo 451781 12407519 := bstep (se 1 (by rfl) ⟨9305639, by rfl⟩ : syracuseStep 12407519 = 18611279) B18611279
theorem B5297125 : Blo 451781 5297125 := bstep (se 4 (by rfl) ⟨496605, by rfl⟩ : syracuseStep 5297125 = 993211) B993211
theorem B1168481 : Blo 451781 1168481 := bstep (se 2 (by rfl) ⟨438180, by rfl⟩ : syracuseStep 1168481 = 876361) B876361
theorem B3691777 : Blo 451781 3691777 := bstep (se 2 (by rfl) ⟨1384416, by rfl⟩ : syracuseStep 3691777 = 2768833) B2768833
theorem B972071 : Blo 451781 972071 := bstep (se 1 (by rfl) ⟨729053, by rfl⟩ : syracuseStep 972071 = 1458107) B1458107
theorem B7755101 : Blo 451781 7755101 := bstep (se 3 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 7755101 = 2908163) B2908163
theorem B611707 : Blo 451781 611707 := bstep (se 1 (by rfl) ⟨458780, by rfl⟩ : syracuseStep 611707 = 917561) B917561
theorem B677687 : Blo 451781 677687 := bstep (se 1 (by rfl) ⟨508265, by rfl⟩ : syracuseStep 677687 = 1016531) B1016531
theorem B677993 : Blo 451781 677993 := bstep (se 2 (by rfl) ⟨254247, by rfl⟩ : syracuseStep 677993 = 508495) B508495
theorem B973147 : Blo 451781 973147 := bstep (se 1 (by rfl) ⟨729860, by rfl⟩ : syracuseStep 973147 = 1459721) B1459721
theorem B678311 : Blo 451781 678311 := bstep (se 1 (by rfl) ⟨508733, by rfl⟩ : syracuseStep 678311 = 1017467) B1017467
theorem B678395 : Blo 451781 678395 := bstep (se 1 (by rfl) ⟨508796, by rfl⟩ : syracuseStep 678395 = 1017593) B1017593
theorem B678521 : Blo 451781 678521 := bstep (se 2 (by rfl) ⟨254445, by rfl⟩ : syracuseStep 678521 = 508891) B508891
theorem B678575 : Blo 451781 678575 := bstep (se 1 (by rfl) ⟨508931, by rfl⟩ : syracuseStep 678575 = 1017863) B1017863
theorem B678623 : Blo 451781 678623 := bstep (se 1 (by rfl) ⟨508967, by rfl⟩ : syracuseStep 678623 = 1017935) B1017935
theorem B678887 : Blo 451781 678887 := bstep (se 1 (by rfl) ⟨509165, by rfl⟩ : syracuseStep 678887 = 1018331) B1018331
theorem B3431645 : Blo 451781 3431645 := bstep (se 3 (by rfl) ⟨643433, by rfl⟩ : syracuseStep 3431645 = 1286867) B1286867
theorem B679145 : Blo 451781 679145 := bstep (se 2 (by rfl) ⟨254679, by rfl⟩ : syracuseStep 679145 = 509359) B509359
theorem B679199 : Blo 451781 679199 := bstep (se 1 (by rfl) ⟨509399, by rfl⟩ : syracuseStep 679199 = 1018799) B1018799
theorem B679367 : Blo 451781 679367 := bstep (se 1 (by rfl) ⟨509525, by rfl⟩ : syracuseStep 679367 = 1019051) B1019051
theorem B613831 : Blo 451781 613831 := bstep (se 1 (by rfl) ⟨460373, by rfl⟩ : syracuseStep 613831 = 920747) B920747
theorem B3530233 : Blo 451781 3530233 := bstep (se 2 (by rfl) ⟨1323837, by rfl⟩ : syracuseStep 3530233 = 2647675) B2647675
theorem B1531385 : Blo 451781 1531385 := bstep (se 2 (by rfl) ⟨574269, by rfl⟩ : syracuseStep 1531385 = 1148539) B1148539
theorem B4906489 : Blo 451781 4906489 := bstep (se 2 (by rfl) ⟨1839933, by rfl⟩ : syracuseStep 4906489 = 3679867) B3679867
theorem B482879 : Blo 451781 482879 := bstep (se 1 (by rfl) ⟨362159, by rfl⟩ : syracuseStep 482879 = 724319) B724319
theorem B1531655 : Blo 451781 1531655 := bstep (se 1 (by rfl) ⟨1148741, by rfl⟩ : syracuseStep 1531655 = 2297483) B2297483
theorem B679721 : Blo 451781 679721 := bstep (se 2 (by rfl) ⟨254895, by rfl⟩ : syracuseStep 679721 = 509791) B509791
theorem B1957679 : Blo 451781 1957679 := bstep (se 1 (by rfl) ⟨1468259, by rfl⟩ : syracuseStep 1957679 = 2936519) B2936519
theorem B679727 : Blo 451781 679727 := bstep (se 1 (by rfl) ⟨509795, by rfl⟩ : syracuseStep 679727 = 1019591) B1019591
theorem B1531709 : Blo 451781 1531709 := bstep (se 3 (by rfl) ⟨287195, by rfl⟩ : syracuseStep 1531709 = 574391) B574391
theorem B1662781 : Blo 451781 1662781 := bstep (se 3 (by rfl) ⟨311771, by rfl⟩ : syracuseStep 1662781 = 623543) B623543
theorem B647119 : Blo 451781 647119 := bstep (se 1 (by rfl) ⟨485339, by rfl⟩ : syracuseStep 647119 = 970679) B970679
theorem B680201 : Blo 451781 680201 := bstep (se 2 (by rfl) ⟨255075, by rfl⟩ : syracuseStep 680201 = 510151) B510151
theorem B680303 : Blo 451781 680303 := bstep (se 1 (by rfl) ⟨510227, by rfl⟩ : syracuseStep 680303 = 1020455) B1020455
theorem B680519 : Blo 451781 680519 := bstep (se 1 (by rfl) ⟨510389, by rfl⟩ : syracuseStep 680519 = 1020779) B1020779
theorem B680555 : Blo 451781 680555 := bstep (se 1 (by rfl) ⟨510416, by rfl⟩ : syracuseStep 680555 = 1020833) B1020833
theorem B2482859 : Blo 451781 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B615215 : Blo 451781 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B680783 : Blo 451781 680783 := bstep (se 1 (by rfl) ⟨510587, by rfl⟩ : syracuseStep 680783 = 1021175) B1021175
theorem B615323 : Blo 451781 615323 := bstep (se 1 (by rfl) ⟨461492, by rfl⟩ : syracuseStep 615323 = 922985) B922985
theorem B484327 : Blo 451781 484327 := bstep (se 1 (by rfl) ⟨363245, by rfl⟩ : syracuseStep 484327 = 726491) B726491
theorem B681179 : Blo 451781 681179 := bstep (se 1 (by rfl) ⟨510884, by rfl⟩ : syracuseStep 681179 = 1021769) B1021769
theorem B451871 : Blo 451781 451871 := bstep (se 1 (by rfl) ⟨338903, by rfl⟩ : syracuseStep 451871 = 677807) B677807
theorem B451931 : Blo 451781 451931 := bstep (se 1 (by rfl) ⟨338948, by rfl⟩ : syracuseStep 451931 = 677897) B677897
theorem B3302765 : Blo 451781 3302765 := bstep (se 3 (by rfl) ⟨619268, by rfl⟩ : syracuseStep 3302765 = 1238537) B1238537
theorem B451951 : Blo 451781 451951 := bstep (se 1 (by rfl) ⟨338963, by rfl⟩ : syracuseStep 451951 = 677927) B677927
theorem B681353 : Blo 451781 681353 := bstep (se 2 (by rfl) ⟨255507, by rfl⟩ : syracuseStep 681353 = 511015) B511015
theorem B452007 : Blo 451781 452007 := bstep (se 1 (by rfl) ⟨339005, by rfl⟩ : syracuseStep 452007 = 678011) B678011
theorem B18703817 : Blo 451781 18703817 := bstep (se 2 (by rfl) ⟨7013931, by rfl⟩ : syracuseStep 18703817 = 14027863) B14027863
theorem B452091 : Blo 451781 452091 := bstep (se 1 (by rfl) ⟨339068, by rfl⟩ : syracuseStep 452091 = 678137) B678137
theorem B452159 : Blo 451781 452159 := bstep (se 1 (by rfl) ⟨339119, by rfl⟩ : syracuseStep 452159 = 678239) B678239
theorem B452167 : Blo 451781 452167 := bstep (se 1 (by rfl) ⟨339125, by rfl⟩ : syracuseStep 452167 = 678251) B678251
theorem B452319 : Blo 451781 452319 := bstep (se 1 (by rfl) ⟨339239, by rfl⟩ : syracuseStep 452319 = 678479) B678479
theorem B485087 : Blo 451781 485087 := bstep (se 1 (by rfl) ⟨363815, by rfl⟩ : syracuseStep 485087 = 727631) B727631
theorem B681707 : Blo 451781 681707 := bstep (se 1 (by rfl) ⟨511280, by rfl⟩ : syracuseStep 681707 = 1022561) B1022561
theorem B14018305 : Blo 451781 14018305 := bstep (se 2 (by rfl) ⟨5256864, by rfl⟩ : syracuseStep 14018305 = 10513729) B10513729
theorem B452399 : Blo 451781 452399 := bstep (se 1 (by rfl) ⟨339299, by rfl⟩ : syracuseStep 452399 = 678599) B678599
theorem B452507 : Blo 451781 452507 := bstep (se 1 (by rfl) ⟨339380, by rfl⟩ : syracuseStep 452507 = 678761) B678761
theorem B485275 : Blo 451781 485275 := bstep (se 1 (by rfl) ⟨363956, by rfl⟩ : syracuseStep 485275 = 727913) B727913
theorem B452559 : Blo 451781 452559 := bstep (se 1 (by rfl) ⟨339419, by rfl⟩ : syracuseStep 452559 = 678839) B678839
theorem B681935 : Blo 451781 681935 := bstep (se 1 (by rfl) ⟨511451, by rfl⟩ : syracuseStep 681935 = 1022903) B1022903
theorem B452583 : Blo 451781 452583 := bstep (se 1 (by rfl) ⟨339437, by rfl⟩ : syracuseStep 452583 = 678875) B678875
theorem B452895 : Blo 451781 452895 := bstep (se 1 (by rfl) ⟨339671, by rfl⟩ : syracuseStep 452895 = 679343) B679343
theorem B452955 : Blo 451781 452955 := bstep (se 1 (by rfl) ⟨339716, by rfl⟩ : syracuseStep 452955 = 679433) B679433
theorem B682331 : Blo 451781 682331 := bstep (se 1 (by rfl) ⟨511748, by rfl⟩ : syracuseStep 682331 = 1023497) B1023497
theorem B452975 : Blo 451781 452975 := bstep (se 1 (by rfl) ⟨339731, by rfl⟩ : syracuseStep 452975 = 679463) B679463
theorem B453031 : Blo 451781 453031 := bstep (se 1 (by rfl) ⟨339773, by rfl⟩ : syracuseStep 453031 = 679547) B679547
theorem B453115 : Blo 451781 453115 := bstep (se 1 (by rfl) ⟨339836, by rfl⟩ : syracuseStep 453115 = 679673) B679673
theorem B453183 : Blo 451781 453183 := bstep (se 1 (by rfl) ⟨339887, by rfl⟩ : syracuseStep 453183 = 679775) B679775
theorem B682559 : Blo 451781 682559 := bstep (se 1 (by rfl) ⟨511919, by rfl⟩ : syracuseStep 682559 = 1023839) B1023839
theorem B453191 : Blo 451781 453191 := bstep (se 1 (by rfl) ⟨339893, by rfl⟩ : syracuseStep 453191 = 679787) B679787
theorem B1534571 : Blo 451781 1534571 := bstep (se 1 (by rfl) ⟨1150928, by rfl⟩ : syracuseStep 1534571 = 2301857) B2301857
theorem B682679 : Blo 451781 682679 := bstep (se 1 (by rfl) ⟨512009, by rfl⟩ : syracuseStep 682679 = 1024019) B1024019
theorem B453343 : Blo 451781 453343 := bstep (se 1 (by rfl) ⟨340007, by rfl⟩ : syracuseStep 453343 = 680015) B680015
theorem B453423 : Blo 451781 453423 := bstep (se 1 (by rfl) ⟨340067, by rfl⟩ : syracuseStep 453423 = 680135) B680135
theorem B453531 : Blo 451781 453531 := bstep (se 1 (by rfl) ⟨340148, by rfl⟩ : syracuseStep 453531 = 680297) B680297
theorem B682907 : Blo 451781 682907 := bstep (se 1 (by rfl) ⟨512180, by rfl⟩ : syracuseStep 682907 = 1024361) B1024361
theorem B453583 : Blo 451781 453583 := bstep (se 1 (by rfl) ⟨340187, by rfl⟩ : syracuseStep 453583 = 680375) B680375
theorem B453607 : Blo 451781 453607 := bstep (se 1 (by rfl) ⟨340205, by rfl⟩ : syracuseStep 453607 = 680411) B680411
theorem B2321423 : Blo 451781 2321423 := bstep (se 1 (by rfl) ⟨1741067, by rfl⟩ : syracuseStep 2321423 = 3482135) B3482135
theorem B4353101 : Blo 451781 4353101 := bstep (se 3 (by rfl) ⟨816206, by rfl⟩ : syracuseStep 4353101 = 1632413) B1632413
theorem B1535165 : Blo 451781 1535165 := bstep (se 3 (by rfl) ⟨287843, by rfl⟩ : syracuseStep 1535165 = 575687) B575687
theorem B453919 : Blo 451781 453919 := bstep (se 1 (by rfl) ⟨340439, by rfl⟩ : syracuseStep 453919 = 680879) B680879
theorem B683303 : Blo 451781 683303 := bstep (se 1 (by rfl) ⟨512477, by rfl⟩ : syracuseStep 683303 = 1024955) B1024955
theorem B453979 : Blo 451781 453979 := bstep (se 1 (by rfl) ⟨340484, by rfl⟩ : syracuseStep 453979 = 680969) B680969
theorem B453999 : Blo 451781 453999 := bstep (se 1 (by rfl) ⟨340499, by rfl⟩ : syracuseStep 453999 = 680999) B680999
theorem B683387 : Blo 451781 683387 := bstep (se 1 (by rfl) ⟨512540, by rfl⟩ : syracuseStep 683387 = 1025081) B1025081
theorem B454055 : Blo 451781 454055 := bstep (se 1 (by rfl) ⟨340541, by rfl⟩ : syracuseStep 454055 = 681083) B681083
theorem B683513 : Blo 451781 683513 := bstep (se 2 (by rfl) ⟨256317, by rfl⟩ : syracuseStep 683513 = 512635) B512635
theorem B454139 : Blo 451781 454139 := bstep (se 1 (by rfl) ⟨340604, by rfl⟩ : syracuseStep 454139 = 681209) B681209
theorem B454207 : Blo 451781 454207 := bstep (se 1 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 454207 = 681311) B681311
theorem B454215 : Blo 451781 454215 := bstep (se 1 (by rfl) ⟨340661, by rfl⟩ : syracuseStep 454215 = 681323) B681323
theorem B683615 : Blo 451781 683615 := bstep (se 1 (by rfl) ⟨512711, by rfl⟩ : syracuseStep 683615 = 1025423) B1025423
theorem B454367 : Blo 451781 454367 := bstep (se 1 (by rfl) ⟨340775, by rfl⟩ : syracuseStep 454367 = 681551) B681551
theorem B454447 : Blo 451781 454447 := bstep (se 1 (by rfl) ⟨340835, by rfl⟩ : syracuseStep 454447 = 681671) B681671
theorem B454555 : Blo 451781 454555 := bstep (se 1 (by rfl) ⟨340916, by rfl⟩ : syracuseStep 454555 = 681833) B681833
theorem B1961903 : Blo 451781 1961903 := bstep (se 1 (by rfl) ⟨1471427, by rfl⟩ : syracuseStep 1961903 = 2942855) B2942855
theorem B454607 : Blo 451781 454607 := bstep (se 1 (by rfl) ⟨340955, by rfl⟩ : syracuseStep 454607 = 681911) B681911
theorem B454631 : Blo 451781 454631 := bstep (se 1 (by rfl) ⟨340973, by rfl⟩ : syracuseStep 454631 = 681947) B681947
theorem B454943 : Blo 451781 454943 := bstep (se 1 (by rfl) ⟨341207, by rfl⟩ : syracuseStep 454943 = 682415) B682415
theorem B455003 : Blo 451781 455003 := bstep (se 1 (by rfl) ⟨341252, by rfl⟩ : syracuseStep 455003 = 682505) B682505
theorem B455023 : Blo 451781 455023 := bstep (se 1 (by rfl) ⟨341267, by rfl⟩ : syracuseStep 455023 = 682535) B682535
theorem B455079 : Blo 451781 455079 := bstep (se 1 (by rfl) ⟨341309, by rfl⟩ : syracuseStep 455079 = 682619) B682619
theorem B455163 : Blo 451781 455163 := bstep (se 1 (by rfl) ⟨341372, by rfl⟩ : syracuseStep 455163 = 682745) B682745
theorem B455231 : Blo 451781 455231 := bstep (se 1 (by rfl) ⟨341423, by rfl⟩ : syracuseStep 455231 = 682847) B682847
theorem B455239 : Blo 451781 455239 := bstep (se 1 (by rfl) ⟨341429, by rfl⟩ : syracuseStep 455239 = 682859) B682859
theorem B881327 : Blo 451781 881327 := bstep (se 1 (by rfl) ⟨660995, by rfl⟩ : syracuseStep 881327 = 1321991) B1321991
theorem B455391 : Blo 451781 455391 := bstep (se 1 (by rfl) ⟨341543, by rfl⟩ : syracuseStep 455391 = 683087) B683087
theorem B455471 : Blo 451781 455471 := bstep (se 1 (by rfl) ⟨341603, by rfl⟩ : syracuseStep 455471 = 683207) B683207
theorem B455579 : Blo 451781 455579 := bstep (se 1 (by rfl) ⟨341684, by rfl⟩ : syracuseStep 455579 = 683369) B683369
theorem B3437477 : Blo 451781 3437477 := bstep (se 4 (by rfl) ⟨322263, by rfl⟩ : syracuseStep 3437477 = 644527) B644527
theorem B455631 : Blo 451781 455631 := bstep (se 1 (by rfl) ⟨341723, by rfl⟩ : syracuseStep 455631 = 683447) B683447
theorem B4649957 : Blo 451781 4649957 := bstep (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) B871867
theorem B455655 : Blo 451781 455655 := bstep (se 1 (by rfl) ⟨341741, by rfl⟩ : syracuseStep 455655 = 683483) B683483
theorem B2290679 : Blo 451781 2290679 := bstep (se 1 (by rfl) ⟨1718009, by rfl⟩ : syracuseStep 2290679 = 3436019) B3436019
theorem B3863609 : Blo 451781 3863609 := bstep (se 2 (by rfl) ⟨1448853, by rfl⟩ : syracuseStep 3863609 = 2897707) B2897707
theorem B1930337 : Blo 451781 1930337 := bstep (se 2 (by rfl) ⟨723876, by rfl⟩ : syracuseStep 1930337 = 1447753) B1447753
theorem B1635527 : Blo 451781 1635527 := bstep (se 1 (by rfl) ⟨1226645, by rfl⟩ : syracuseStep 1635527 = 2453291) B2453291
theorem B2061607 : Blo 451781 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B2454893 : Blo 451781 2454893 := bstep (se 3 (by rfl) ⟨460292, by rfl⟩ : syracuseStep 2454893 = 920585) B920585
theorem B3437963 : Blo 451781 3437963 := bstep (se 1 (by rfl) ⟨2578472, by rfl⟩ : syracuseStep 3437963 = 5156945) B5156945
theorem B1144327 : Blo 451781 1144327 := bstep (se 1 (by rfl) ⟨858245, by rfl⟩ : syracuseStep 1144327 = 1716491) B1716491
theorem B1144631 : Blo 451781 1144631 := bstep (se 1 (by rfl) ⟨858473, by rfl⟩ : syracuseStep 1144631 = 1716947) B1716947
theorem B1538081 : Blo 451781 1538081 := bstep (se 2 (by rfl) ⟨576780, by rfl⟩ : syracuseStep 1538081 = 1153561) B1153561
theorem B1145299 : Blo 451781 1145299 := bstep (se 1 (by rfl) ⟨858974, by rfl⟩ : syracuseStep 1145299 = 1717949) B1717949
theorem B2292623 : Blo 451781 2292623 := bstep (se 1 (by rfl) ⟨1719467, by rfl⟩ : syracuseStep 2292623 = 3438935) B3438935
theorem B5831909 : Blo 451781 5831909 := bstep (se 4 (by rfl) ⟨546741, by rfl⟩ : syracuseStep 5831909 = 1093483) B1093483
theorem B1146089 : Blo 451781 1146089 := bstep (se 2 (by rfl) ⟨429783, by rfl⟩ : syracuseStep 1146089 = 859567) B859567
theorem B1146251 : Blo 451781 1146251 := bstep (se 1 (by rfl) ⟨859688, by rfl⟩ : syracuseStep 1146251 = 1719377) B1719377
theorem B1146919 : Blo 451781 1146919 := bstep (se 1 (by rfl) ⟨860189, by rfl⟩ : syracuseStep 1146919 = 1720379) B1720379
theorem B11665457 : Blo 451781 11665457 := bstep (se 2 (by rfl) ⟨4374546, by rfl⟩ : syracuseStep 11665457 = 8749093) B8749093
theorem B35324219 : Blo 451781 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B1770113 : Blo 451781 1770113 := bstep (se 2 (by rfl) ⟨663792, by rfl⟩ : syracuseStep 1770113 = 1327585) B1327585
theorem B1016585 : Blo 451781 1016585 := bstep (se 2 (by rfl) ⟨381219, by rfl⟩ : syracuseStep 1016585 = 762439) B762439
theorem B2917367 : Blo 451781 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B12584135 : Blo 451781 12584135 := bstep (se 1 (by rfl) ⟨9438101, by rfl⟩ : syracuseStep 12584135 = 18876203) B18876203
theorem B1017161 : Blo 451781 1017161 := bstep (se 2 (by rfl) ⟨381435, by rfl⟩ : syracuseStep 1017161 = 762871) B762871
theorem B2360927 : Blo 451781 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B2590319 : Blo 451781 2590319 := bstep (se 1 (by rfl) ⟨1942739, by rfl⟩ : syracuseStep 2590319 = 3885479) B3885479
theorem B6620957 : Blo 451781 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B150964235 : Blo 451781 150964235 := bstep (se 1 (by rfl) ⟨113223176, by rfl⟩ : syracuseStep 150964235 = 226446353) B226446353
theorem B5146739 : Blo 451781 5146739 := bstep (se 1 (by rfl) ⟨3860054, by rfl⟩ : syracuseStep 5146739 = 7720109) B7720109
theorem B1640573 : Blo 451781 1640573 := bstep (se 3 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 1640573 = 615215) B615215
theorem B3442823 : Blo 451781 3442823 := bstep (se 1 (by rfl) ⟨2582117, by rfl⟩ : syracuseStep 3442823 = 5164235) B5164235
theorem B1018151 : Blo 451781 1018151 := bstep (se 1 (by rfl) ⟨763613, by rfl⟩ : syracuseStep 1018151 = 1527227) B1527227
theorem B1018169 : Blo 451781 1018169 := bstep (se 2 (by rfl) ⟨381813, by rfl⟩ : syracuseStep 1018169 = 763627) B763627
theorem B1640861 : Blo 451781 1640861 := bstep (se 3 (by rfl) ⟨307661, by rfl⟩ : syracuseStep 1640861 = 615323) B615323
theorem B2591777 : Blo 451781 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B5508319 : Blo 451781 5508319 := bstep (se 1 (by rfl) ⟨4131239, by rfl⟩ : syracuseStep 5508319 = 8262479) B8262479
theorem B1379551 : Blo 451781 1379551 := bstep (se 1 (by rfl) ⟨1034663, by rfl⟩ : syracuseStep 1379551 = 2069327) B2069327
theorem B1019465 : Blo 451781 1019465 := bstep (se 2 (by rfl) ⟨382299, by rfl⟩ : syracuseStep 1019465 = 764599) B764599
theorem B2330473 : Blo 451781 2330473 := bstep (se 2 (by rfl) ⟨873927, by rfl⟩ : syracuseStep 2330473 = 1747855) B1747855
theorem B1020923 : Blo 451781 1020923 := bstep (se 1 (by rfl) ⟨765692, by rfl⟩ : syracuseStep 1020923 = 1531385) B1531385
theorem B9311377 : Blo 451781 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B1021103 : Blo 451781 1021103 := bstep (se 1 (by rfl) ⟨765827, by rfl⟩ : syracuseStep 1021103 = 1531655) B1531655
theorem B1021139 : Blo 451781 1021139 := bstep (se 1 (by rfl) ⟨765854, by rfl⟩ : syracuseStep 1021139 = 1531709) B1531709
theorem B3282295 : Blo 451781 3282295 := bstep (se 1 (by rfl) ⟨2461721, by rfl⟩ : syracuseStep 3282295 = 4923443) B4923443
theorem B1021409 : Blo 451781 1021409 := bstep (se 2 (by rfl) ⟨383028, by rfl⟩ : syracuseStep 1021409 = 766057) B766057
theorem B857783 : Blo 451781 857783 := bstep (se 1 (by rfl) ⟨643337, by rfl⟩ : syracuseStep 857783 = 1286675) B1286675
theorem B726779 : Blo 451781 726779 := bstep (se 1 (by rfl) ⟨545084, by rfl⟩ : syracuseStep 726779 = 1090169) B1090169
theorem B11802419 : Blo 451781 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B3151673 : Blo 451781 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B2201843 : Blo 451781 2201843 := bstep (se 1 (by rfl) ⟨1651382, by rfl⟩ : syracuseStep 2201843 = 3302765) B3302765
theorem B2759123 : Blo 451781 2759123 := bstep (se 1 (by rfl) ⟨2069342, by rfl⟩ : syracuseStep 2759123 = 4138685) B4138685
theorem B3283507 : Blo 451781 3283507 := bstep (se 1 (by rfl) ⟨2462630, by rfl⟩ : syracuseStep 3283507 = 4925261) B4925261
theorem B1153673 : Blo 451781 1153673 := bstep (se 2 (by rfl) ⟨432627, by rfl⟩ : syracuseStep 1153673 = 865255) B865255
theorem B1842011 : Blo 451781 1842011 := bstep (se 1 (by rfl) ⟨1381508, by rfl⟩ : syracuseStep 1842011 = 2763017) B2763017
theorem B4922369 : Blo 451781 4922369 := bstep (se 2 (by rfl) ⟨1845888, by rfl⟩ : syracuseStep 4922369 = 3691777) B3691777
theorem B1940537 : Blo 451781 1940537 := bstep (se 2 (by rfl) ⟨727701, by rfl⟩ : syracuseStep 1940537 = 1455403) B1455403
theorem B1023047 : Blo 451781 1023047 := bstep (se 1 (by rfl) ⟨767285, by rfl⟩ : syracuseStep 1023047 = 1534571) B1534571
theorem B1449085 : Blo 451781 1449085 := bstep (se 3 (by rfl) ⟨271703, by rfl⟩ : syracuseStep 1449085 = 543407) B543407
theorem B1547615 : Blo 451781 1547615 := bstep (se 1 (by rfl) ⟨1160711, by rfl⟩ : syracuseStep 1547615 = 2321423) B2321423
theorem B1023443 : Blo 451781 1023443 := bstep (se 1 (by rfl) ⟨767582, by rfl⟩ : syracuseStep 1023443 = 1535165) B1535165
theorem B1023713 : Blo 451781 1023713 := bstep (se 2 (by rfl) ⟨383892, by rfl⟩ : syracuseStep 1023713 = 767785) B767785
theorem B2760875 : Blo 451781 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B1843553 : Blo 451781 1843553 := bstep (se 2 (by rfl) ⟨691332, by rfl⟩ : syracuseStep 1843553 = 1382665) B1382665
theorem B860615 : Blo 451781 860615 := bstep (se 1 (by rfl) ⟨645461, by rfl⟩ : syracuseStep 860615 = 1290923) B1290923
theorem B1286891 : Blo 451781 1286891 := bstep (se 1 (by rfl) ⟨965168, by rfl⟩ : syracuseStep 1286891 = 1930337) B1930337
theorem B1090351 : Blo 451781 1090351 := bstep (se 1 (by rfl) ⟨817763, by rfl⟩ : syracuseStep 1090351 = 1635527) B1635527
theorem B763087 : Blo 451781 763087 := bstep (se 1 (by rfl) ⟨572315, by rfl⟩ : syracuseStep 763087 = 1144631) B1144631
theorem B1025387 : Blo 451781 1025387 := bstep (se 1 (by rfl) ⟨769040, by rfl⟩ : syracuseStep 1025387 = 1538081) B1538081
theorem B1287677 : Blo 451781 1287677 := bstep (se 3 (by rfl) ⟨241439, by rfl⟩ : syracuseStep 1287677 = 482879) B482879
theorem B763897 : Blo 451781 763897 := bstep (se 2 (by rfl) ⟨286461, by rfl⟩ : syracuseStep 763897 = 572923) B572923
theorem B4925519 : Blo 451781 4925519 := bstep (se 1 (by rfl) ⟨3694139, by rfl⟩ : syracuseStep 4925519 = 7388279) B7388279
theorem B2304125 : Blo 451781 2304125 := bstep (se 3 (by rfl) ⟨432023, by rfl⟩ : syracuseStep 2304125 = 864047) B864047
theorem B764059 : Blo 451781 764059 := bstep (se 1 (by rfl) ⟨573044, by rfl⟩ : syracuseStep 764059 = 1146089) B1146089
theorem B764167 : Blo 451781 764167 := bstep (se 1 (by rfl) ⟨573125, by rfl⟩ : syracuseStep 764167 = 1146251) B1146251
theorem B764201 : Blo 451781 764201 := bstep (se 2 (by rfl) ⟨286575, by rfl⟩ : syracuseStep 764201 = 573151) B573151
theorem B1452545 : Blo 451781 1452545 := bstep (se 2 (by rfl) ⟨544704, by rfl⟩ : syracuseStep 1452545 = 1089409) B1089409
theorem B862825 : Blo 451781 862825 := bstep (se 2 (by rfl) ⟨323559, by rfl⟩ : syracuseStep 862825 = 647119) B647119
theorem B1289191 : Blo 451781 1289191 := bstep (se 1 (by rfl) ⟨966893, by rfl⟩ : syracuseStep 1289191 = 1933787) B1933787
theorem B863455 : Blo 451781 863455 := bstep (se 1 (by rfl) ⟨647591, by rfl⟩ : syracuseStep 863455 = 1295183) B1295183
theorem B765193 : Blo 451781 765193 := bstep (se 2 (by rfl) ⟨286947, by rfl⟩ : syracuseStep 765193 = 573895) B573895
theorem B9940553 : Blo 451781 9940553 := bstep (se 2 (by rfl) ⟨3727707, by rfl⟩ : syracuseStep 9940553 = 7455415) B7455415
theorem B765767 : Blo 451781 765767 := bstep (se 1 (by rfl) ⟨574325, by rfl⟩ : syracuseStep 765767 = 1148651) B1148651
theorem B2896067 : Blo 451781 2896067 := bstep (se 1 (by rfl) ⟨2172050, by rfl⟩ : syracuseStep 2896067 = 4344101) B4344101
theorem B1847719 : Blo 451781 1847719 := bstep (se 1 (by rfl) ⟨1385789, by rfl⟩ : syracuseStep 1847719 = 2771579) B2771579
theorem B766415 : Blo 451781 766415 := bstep (se 1 (by rfl) ⟨574811, by rfl⟩ : syracuseStep 766415 = 1149623) B1149623
theorem B13054445 : Blo 451781 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B2798327 : Blo 451781 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B1291049 : Blo 451781 1291049 := bstep (se 2 (by rfl) ⟨484143, by rfl⟩ : syracuseStep 1291049 = 968287) B968287
theorem B14725961 : Blo 451781 14725961 := bstep (se 2 (by rfl) ⟨5522235, by rfl⟩ : syracuseStep 14725961 = 11044471) B11044471
theorem B5190479 : Blo 451781 5190479 := bstep (se 1 (by rfl) ⟨3892859, by rfl⟩ : syracuseStep 5190479 = 7785719) B7785719
theorem B18691073 : Blo 451781 18691073 := bstep (se 2 (by rfl) ⟨7009152, by rfl⟩ : syracuseStep 18691073 = 14018305) B14018305
theorem B767083 : Blo 451781 767083 := bstep (se 1 (by rfl) ⟨575312, by rfl⟩ : syracuseStep 767083 = 1150625) B1150625
theorem B767387 : Blo 451781 767387 := bstep (se 1 (by rfl) ⟨575540, by rfl⟩ : syracuseStep 767387 = 1151081) B1151081
theorem B4372055 : Blo 451781 4372055 := bstep (se 1 (by rfl) ⟨3279041, by rfl⟩ : syracuseStep 4372055 = 6558083) B6558083
theorem B767711 : Blo 451781 767711 := bstep (se 1 (by rfl) ⟨575783, by rfl⟩ : syracuseStep 767711 = 1151567) B1151567
theorem B8271679 : Blo 451781 8271679 := bstep (se 1 (by rfl) ⟨6203759, by rfl⟩ : syracuseStep 8271679 = 12407519) B12407519
theorem B1751003 : Blo 451781 1751003 := bstep (se 1 (by rfl) ⟨1313252, by rfl⟩ : syracuseStep 1751003 = 2626505) B2626505
theorem B2898017 : Blo 451781 2898017 := bstep (se 2 (by rfl) ⟨1086756, by rfl⟩ : syracuseStep 2898017 = 2173513) B2173513
theorem B768143 : Blo 451781 768143 := bstep (se 1 (by rfl) ⟨576107, by rfl⟩ : syracuseStep 768143 = 1152215) B1152215
theorem B1292449 : Blo 451781 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B3258539 : Blo 451781 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B768379 : Blo 451781 768379 := bstep (se 1 (by rfl) ⟨576284, by rfl⟩ : syracuseStep 768379 = 1152569) B1152569
theorem B1456697 : Blo 451781 1456697 := bstep (se 2 (by rfl) ⟨546261, by rfl⟩ : syracuseStep 1456697 = 1092523) B1092523
theorem B1227401 : Blo 451781 1227401 := bstep (se 2 (by rfl) ⟨460275, by rfl⟩ : syracuseStep 1227401 = 920551) B920551
theorem B768649 : Blo 451781 768649 := bstep (se 2 (by rfl) ⟨288243, by rfl⟩ : syracuseStep 768649 = 576487) B576487
theorem B965459 : Blo 451781 965459 := bstep (se 1 (by rfl) ⟨724094, by rfl⟩ : syracuseStep 965459 = 1448189) B1448189
theorem B1293383 : Blo 451781 1293383 := bstep (se 1 (by rfl) ⟨970037, by rfl⟩ : syracuseStep 1293383 = 1940075) B1940075
theorem B572599 : Blo 451781 572599 := bstep (se 1 (by rfl) ⟨429449, by rfl⟩ : syracuseStep 572599 = 858899) B858899
theorem B1293565 : Blo 451781 1293565 := bstep (se 3 (by rfl) ⟨242543, by rfl⟩ : syracuseStep 1293565 = 485087) B485087
theorem B1556279 : Blo 451781 1556279 := bstep (se 1 (by rfl) ⟨1167209, by rfl⟩ : syracuseStep 1556279 = 2334419) B2334419
theorem B5816123 : Blo 451781 5816123 := bstep (se 1 (by rfl) ⟨4362092, by rfl⟩ : syracuseStep 5816123 = 8724185) B8724185
theorem B7979147 : Blo 451781 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B967099 : Blo 451781 967099 := bstep (se 1 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 967099 = 1450649) B1450649
theorem B1295023 : Blo 451781 1295023 := bstep (se 1 (by rfl) ⟨971267, by rfl⟩ : syracuseStep 1295023 = 1942535) B1942535
theorem B508783 : Blo 451781 508783 := bstep (se 1 (by rfl) ⟨381587, by rfl⟩ : syracuseStep 508783 = 763175) B763175
theorem B967535 : Blo 451781 967535 := bstep (se 1 (by rfl) ⟨725651, by rfl⟩ : syracuseStep 967535 = 1451303) B1451303
theorem B12469211 : Blo 451781 12469211 := bstep (se 1 (by rfl) ⟨9351908, by rfl⟩ : syracuseStep 12469211 = 18703817) B18703817
theorem B7062833 : Blo 451781 7062833 := bstep (se 2 (by rfl) ⟨2648562, by rfl⟩ : syracuseStep 7062833 = 5297125) B5297125
theorem B1033643 : Blo 451781 1033643 := bstep (se 1 (by rfl) ⟨775232, by rfl⟩ : syracuseStep 1033643 = 1550465) B1550465
theorem B968107 : Blo 451781 968107 := bstep (se 1 (by rfl) ⟨726080, by rfl⟩ : syracuseStep 968107 = 1452161) B1452161
theorem B509935 : Blo 451781 509935 := bstep (se 1 (by rfl) ⟨382451, by rfl⟩ : syracuseStep 509935 = 764903) B764903
theorem B1525769 : Blo 451781 1525769 := bstep (se 2 (by rfl) ⟨572163, by rfl⟩ : syracuseStep 1525769 = 1144327) B1144327
theorem B2902067 : Blo 451781 2902067 := bstep (se 1 (by rfl) ⟨2176550, by rfl⟩ : syracuseStep 2902067 = 4353101) B4353101
theorem B19646711 : Blo 451781 19646711 := bstep (se 1 (by rfl) ⟨14735033, by rfl⟩ : syracuseStep 19646711 = 29470067) B29470067
theorem B1297529 : Blo 451781 1297529 := bstep (se 2 (by rfl) ⟨486573, by rfl⟩ : syracuseStep 1297529 = 973147) B973147
theorem B1527065 : Blo 451781 1527065 := bstep (se 2 (by rfl) ⟨572649, by rfl⟩ : syracuseStep 1527065 = 1145299) B1145299
theorem B3099971 : Blo 451781 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B1527119 : Blo 451781 1527119 := bstep (se 1 (by rfl) ⟨1145339, by rfl⟩ : syracuseStep 1527119 = 2290679) B2290679
theorem B2575739 : Blo 451781 2575739 := bstep (se 1 (by rfl) ⟨1931804, by rfl⟩ : syracuseStep 2575739 = 3863609) B3863609
theorem B512383 : Blo 451781 512383 := bstep (se 1 (by rfl) ⟨384287, by rfl⟩ : syracuseStep 512383 = 768575) B768575
theorem B2806343 : Blo 451781 2806343 := bstep (se 1 (by rfl) ⟨2104757, by rfl⟩ : syracuseStep 2806343 = 4209515) B4209515
theorem B1528415 : Blo 451781 1528415 := bstep (se 1 (by rfl) ⟨1146311, by rfl⟩ : syracuseStep 1528415 = 2292623) B2292623
theorem B4706977 : Blo 451781 4706977 := bstep (se 2 (by rfl) ⟨1765116, by rfl⟩ : syracuseStep 4706977 = 3530233) B3530233
theorem B6541985 : Blo 451781 6541985 := bstep (se 2 (by rfl) ⟨2453244, by rfl⟩ : syracuseStep 6541985 = 4906489) B4906489
theorem B1725209 : Blo 451781 1725209 := bstep (se 2 (by rfl) ⟨646953, by rfl⟩ : syracuseStep 1725209 = 1293907) B1293907
theorem B3887939 : Blo 451781 3887939 := bstep (se 1 (by rfl) ⟨2915954, by rfl⟩ : syracuseStep 3887939 = 5831909) B5831909
theorem B2872199 : Blo 451781 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B2217041 : Blo 451781 2217041 := bstep (se 2 (by rfl) ⟨831390, by rfl⟩ : syracuseStep 2217041 = 1662781) B1662781
theorem B644203 : Blo 451781 644203 := bstep (se 1 (by rfl) ⟨483152, by rfl⟩ : syracuseStep 644203 = 966305) B966305
theorem B1529657 : Blo 451781 1529657 := bstep (se 2 (by rfl) ⟨573621, by rfl⟩ : syracuseStep 1529657 = 1147243) B1147243
theorem B677711 : Blo 451781 677711 := bstep (se 1 (by rfl) ⟨508283, by rfl⟩ : syracuseStep 677711 = 1016567) B1016567
theorem B677831 : Blo 451781 677831 := bstep (se 1 (by rfl) ⟨508373, by rfl⟩ : syracuseStep 677831 = 1016747) B1016747
theorem B1529819 : Blo 451781 1529819 := bstep (se 1 (by rfl) ⟨1147364, by rfl⟩ : syracuseStep 1529819 = 2294729) B2294729
theorem B2906113 : Blo 451781 2906113 := bstep (se 2 (by rfl) ⟨1089792, by rfl⟩ : syracuseStep 2906113 = 2179585) B2179585
theorem B1530089 : Blo 451781 1530089 := bstep (se 2 (by rfl) ⟨573783, by rfl⟩ : syracuseStep 1530089 = 1147567) B1147567
theorem B874729 : Blo 451781 874729 := bstep (se 2 (by rfl) ⟨328023, by rfl⟩ : syracuseStep 874729 = 656047) B656047
theorem B678185 : Blo 451781 678185 := bstep (se 2 (by rfl) ⟨254319, by rfl⟩ : syracuseStep 678185 = 508639) B508639
theorem B678191 : Blo 451781 678191 := bstep (se 1 (by rfl) ⟨508643, by rfl⟩ : syracuseStep 678191 = 1017287) B1017287
theorem B5822887 : Blo 451781 5822887 := bstep (se 1 (by rfl) ⟨4367165, by rfl⟩ : syracuseStep 5822887 = 8734331) B8734331
theorem B678431 : Blo 451781 678431 := bstep (se 1 (by rfl) ⟨508823, by rfl⟩ : syracuseStep 678431 = 1017647) B1017647
theorem B645769 : Blo 451781 645769 := bstep (se 2 (by rfl) ⟨242163, by rfl⟩ : syracuseStep 645769 = 484327) B484327
theorem B1530521 : Blo 451781 1530521 := bstep (se 2 (by rfl) ⟨573945, by rfl⟩ : syracuseStep 1530521 = 1147891) B1147891
theorem B678815 : Blo 451781 678815 := bstep (se 1 (by rfl) ⟨509111, by rfl⟩ : syracuseStep 678815 = 1018223) B1018223
theorem B678863 : Blo 451781 678863 := bstep (se 1 (by rfl) ⟨509147, by rfl⟩ : syracuseStep 678863 = 1018295) B1018295
theorem B678953 : Blo 451781 678953 := bstep (se 2 (by rfl) ⟨254607, by rfl⟩ : syracuseStep 678953 = 509215) B509215
theorem B678959 : Blo 451781 678959 := bstep (se 1 (by rfl) ⟨509219, by rfl⟩ : syracuseStep 678959 = 1018439) B1018439
theorem B678983 : Blo 451781 678983 := bstep (se 1 (by rfl) ⟨509237, by rfl⟩ : syracuseStep 678983 = 1018475) B1018475
theorem B2350205 : Blo 451781 2350205 := bstep (se 3 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 2350205 = 881327) B881327
theorem B646327 : Blo 451781 646327 := bstep (se 1 (by rfl) ⟨484745, by rfl⟩ : syracuseStep 646327 = 969491) B969491
theorem B1662137 : Blo 451781 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B679247 : Blo 451781 679247 := bstep (se 1 (by rfl) ⟨509435, by rfl⟩ : syracuseStep 679247 = 1018871) B1018871
theorem B679337 : Blo 451781 679337 := bstep (se 2 (by rfl) ⟨254751, by rfl⟩ : syracuseStep 679337 = 509503) B509503
theorem B679487 : Blo 451781 679487 := bstep (se 1 (by rfl) ⟨509615, by rfl⟩ : syracuseStep 679487 = 1019231) B1019231
theorem B2580295 : Blo 451781 2580295 := bstep (se 1 (by rfl) ⟨1935221, by rfl⟩ : syracuseStep 2580295 = 3870443) B3870443
theorem B679751 : Blo 451781 679751 := bstep (se 1 (by rfl) ⟨509813, by rfl⟩ : syracuseStep 679751 = 1019627) B1019627
theorem B647033 : Blo 451781 647033 := bstep (se 2 (by rfl) ⟨242637, by rfl⟩ : syracuseStep 647033 = 485275) B485275
theorem B679835 : Blo 451781 679835 := bstep (se 1 (by rfl) ⟨509876, by rfl⟩ : syracuseStep 679835 = 1019753) B1019753
theorem B3104669 : Blo 451781 3104669 := bstep (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) B1164251
theorem B1958023 : Blo 451781 1958023 := bstep (se 1 (by rfl) ⟨1468517, by rfl⟩ : syracuseStep 1958023 = 2937035) B2937035
theorem B647455 : Blo 451781 647455 := bstep (se 1 (by rfl) ⟨485591, by rfl⟩ : syracuseStep 647455 = 971183) B971183
theorem B7332227 : Blo 451781 7332227 := bstep (se 1 (by rfl) ⟨5499170, by rfl⟩ : syracuseStep 7332227 = 10998341) B10998341
theorem B161014169 : Blo 451781 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B680399 : Blo 451781 680399 := bstep (se 1 (by rfl) ⟨510299, by rfl⟩ : syracuseStep 680399 = 1020599) B1020599
theorem B680441 : Blo 451781 680441 := bstep (se 2 (by rfl) ⟨255165, by rfl⟩ : syracuseStep 680441 = 510331) B510331
theorem B1532411 : Blo 451781 1532411 := bstep (se 1 (by rfl) ⟨1149308, by rfl⟩ : syracuseStep 1532411 = 2298617) B2298617
theorem B1729097 : Blo 451781 1729097 := bstep (se 2 (by rfl) ⟨648411, by rfl⟩ : syracuseStep 1729097 = 1296823) B1296823
theorem B680543 : Blo 451781 680543 := bstep (se 1 (by rfl) ⟨510407, by rfl⟩ : syracuseStep 680543 = 1020815) B1020815
theorem B778987 : Blo 451781 778987 := bstep (se 1 (by rfl) ⟨584240, by rfl⟩ : syracuseStep 778987 = 1168481) B1168481
theorem B1532681 : Blo 451781 1532681 := bstep (se 2 (by rfl) ⟨574755, by rfl⟩ : syracuseStep 1532681 = 1149511) B1149511
theorem B2188043 : Blo 451781 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B648047 : Blo 451781 648047 := bstep (se 1 (by rfl) ⟨486035, by rfl⟩ : syracuseStep 648047 = 972071) B972071
theorem B5170067 : Blo 451781 5170067 := bstep (se 1 (by rfl) ⟨3877550, by rfl⟩ : syracuseStep 5170067 = 7755101) B7755101
theorem B681023 : Blo 451781 681023 := bstep (se 1 (by rfl) ⟨510767, by rfl⟩ : syracuseStep 681023 = 1021535) B1021535
theorem B3892313 : Blo 451781 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B681065 : Blo 451781 681065 := bstep (se 2 (by rfl) ⟨255399, by rfl⟩ : syracuseStep 681065 = 510799) B510799
theorem B451791 : Blo 451781 451791 := bstep (se 1 (by rfl) ⟨338843, by rfl⟩ : syracuseStep 451791 = 677687) B677687
theorem B681167 : Blo 451781 681167 := bstep (se 1 (by rfl) ⟨510875, by rfl⟩ : syracuseStep 681167 = 1021751) B1021751
theorem B2581753 : Blo 451781 2581753 := bstep (se 2 (by rfl) ⟨968157, by rfl⟩ : syracuseStep 2581753 = 1936315) B1936315
theorem B451995 : Blo 451781 451995 := bstep (se 1 (by rfl) ⟨338996, by rfl⟩ : syracuseStep 451995 = 677993) B677993
theorem B681371 : Blo 451781 681371 := bstep (se 1 (by rfl) ⟨511028, by rfl⟩ : syracuseStep 681371 = 1022057) B1022057
theorem B1533437 : Blo 451781 1533437 := bstep (se 3 (by rfl) ⟨287519, by rfl⟩ : syracuseStep 1533437 = 575039) B575039
theorem B452207 : Blo 451781 452207 := bstep (se 1 (by rfl) ⟨339155, by rfl⟩ : syracuseStep 452207 = 678311) B678311
theorem B681593 : Blo 451781 681593 := bstep (se 2 (by rfl) ⟨255597, by rfl⟩ : syracuseStep 681593 = 511195) B511195
theorem B452263 : Blo 451781 452263 := bstep (se 1 (by rfl) ⟨339197, by rfl⟩ : syracuseStep 452263 = 678395) B678395
theorem B1730267 : Blo 451781 1730267 := bstep (se 1 (by rfl) ⟨1297700, by rfl⟩ : syracuseStep 1730267 = 2595401) B2595401
theorem B681695 : Blo 451781 681695 := bstep (se 1 (by rfl) ⟨511271, by rfl⟩ : syracuseStep 681695 = 1022543) B1022543
theorem B452347 : Blo 451781 452347 := bstep (se 1 (by rfl) ⟨339260, by rfl⟩ : syracuseStep 452347 = 678521) B678521
theorem B2582279 : Blo 451781 2582279 := bstep (se 1 (by rfl) ⟨1936709, by rfl⟩ : syracuseStep 2582279 = 3873419) B3873419
theorem B452383 : Blo 451781 452383 := bstep (se 1 (by rfl) ⟨339287, by rfl⟩ : syracuseStep 452383 = 678575) B678575
theorem B452415 : Blo 451781 452415 := bstep (se 1 (by rfl) ⟨339311, by rfl⟩ : syracuseStep 452415 = 678623) B678623
theorem B681791 : Blo 451781 681791 := bstep (se 1 (by rfl) ⟨511343, by rfl⟩ : syracuseStep 681791 = 1022687) B1022687
theorem B3860297 : Blo 451781 3860297 := bstep (se 2 (by rfl) ⟨1447611, by rfl⟩ : syracuseStep 3860297 = 2895223) B2895223
theorem B681959 : Blo 451781 681959 := bstep (se 1 (by rfl) ⟨511469, by rfl⟩ : syracuseStep 681959 = 1022939) B1022939
theorem B452591 : Blo 451781 452591 := bstep (se 1 (by rfl) ⟨339443, by rfl⟩ : syracuseStep 452591 = 678887) B678887
theorem B681977 : Blo 451781 681977 := bstep (se 2 (by rfl) ⟨255741, by rfl⟩ : syracuseStep 681977 = 511483) B511483
theorem B29485133 : Blo 451781 29485133 := bstep (se 3 (by rfl) ⟨5528462, by rfl⟩ : syracuseStep 29485133 = 11056925) B11056925
theorem B682079 : Blo 451781 682079 := bstep (se 1 (by rfl) ⟨511559, by rfl⟩ : syracuseStep 682079 = 1023119) B1023119
theorem B2287763 : Blo 451781 2287763 := bstep (se 1 (by rfl) ⟨1715822, by rfl⟩ : syracuseStep 2287763 = 3431645) B3431645
theorem B452763 : Blo 451781 452763 := bstep (se 1 (by rfl) ⟨339572, by rfl⟩ : syracuseStep 452763 = 679145) B679145
theorem B682139 : Blo 451781 682139 := bstep (se 1 (by rfl) ⟨511604, by rfl⟩ : syracuseStep 682139 = 1023209) B1023209
theorem B14772401 : Blo 451781 14772401 := bstep (se 2 (by rfl) ⟨5539650, by rfl⟩ : syracuseStep 14772401 = 11079301) B11079301
theorem B452799 : Blo 451781 452799 := bstep (se 1 (by rfl) ⟨339599, by rfl⟩ : syracuseStep 452799 = 679199) B679199
theorem B682175 : Blo 451781 682175 := bstep (se 1 (by rfl) ⟨511631, by rfl⟩ : syracuseStep 682175 = 1023263) B1023263
theorem B682217 : Blo 451781 682217 := bstep (se 2 (by rfl) ⟨255831, by rfl⟩ : syracuseStep 682217 = 511663) B511663
theorem B1534247 : Blo 451781 1534247 := bstep (se 1 (by rfl) ⟨1150685, by rfl⟩ : syracuseStep 1534247 = 2301371) B2301371
theorem B452911 : Blo 451781 452911 := bstep (se 1 (by rfl) ⟨339683, by rfl⟩ : syracuseStep 452911 = 679367) B679367
theorem B453147 : Blo 451781 453147 := bstep (se 1 (by rfl) ⟨339860, by rfl⟩ : syracuseStep 453147 = 679721) B679721
theorem B682523 : Blo 451781 682523 := bstep (se 1 (by rfl) ⟨511892, by rfl⟩ : syracuseStep 682523 = 1023785) B1023785
theorem B1305119 : Blo 451781 1305119 := bstep (se 1 (by rfl) ⟨978839, by rfl⟩ : syracuseStep 1305119 = 1957679) B1957679
theorem B453151 : Blo 451781 453151 := bstep (se 1 (by rfl) ⟨339863, by rfl⟩ : syracuseStep 453151 = 679727) B679727
theorem B3435047 : Blo 451781 3435047 := bstep (se 1 (by rfl) ⟨2576285, by rfl⟩ : syracuseStep 3435047 = 5152571) B5152571
theorem B682601 : Blo 451781 682601 := bstep (se 2 (by rfl) ⟨255975, by rfl⟩ : syracuseStep 682601 = 511951) B511951
theorem B453467 : Blo 451781 453467 := bstep (se 1 (by rfl) ⟨340100, by rfl⟩ : syracuseStep 453467 = 680201) B680201
theorem B453535 : Blo 451781 453535 := bstep (se 1 (by rfl) ⟨340151, by rfl⟩ : syracuseStep 453535 = 680303) B680303
theorem B453679 : Blo 451781 453679 := bstep (se 1 (by rfl) ⟨340259, by rfl⟩ : syracuseStep 453679 = 680519) B680519
theorem B453703 : Blo 451781 453703 := bstep (se 1 (by rfl) ⟨340277, by rfl⟩ : syracuseStep 453703 = 680555) B680555
theorem B683129 : Blo 451781 683129 := bstep (se 2 (by rfl) ⟨256173, by rfl⟩ : syracuseStep 683129 = 512347) B512347
theorem B1535111 : Blo 451781 1535111 := bstep (se 1 (by rfl) ⟨1151333, by rfl⟩ : syracuseStep 1535111 = 2302667) B2302667
theorem B453855 : Blo 451781 453855 := bstep (se 1 (by rfl) ⟨340391, by rfl⟩ : syracuseStep 453855 = 680783) B680783
theorem B683231 : Blo 451781 683231 := bstep (se 1 (by rfl) ⟨512423, by rfl⟩ : syracuseStep 683231 = 1024847) B1024847
theorem B1535219 : Blo 451781 1535219 := bstep (se 1 (by rfl) ⟨1151414, by rfl⟩ : syracuseStep 1535219 = 2302829) B2302829
theorem B683273 : Blo 451781 683273 := bstep (se 2 (by rfl) ⟨256227, by rfl⟩ : syracuseStep 683273 = 512455) B512455
theorem B683375 : Blo 451781 683375 := bstep (se 1 (by rfl) ⟨512531, by rfl⟩ : syracuseStep 683375 = 1025063) B1025063
theorem B15756743 : Blo 451781 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B454119 : Blo 451781 454119 := bstep (se 1 (by rfl) ⟨340589, by rfl⟩ : syracuseStep 454119 = 681179) B681179
theorem B683495 : Blo 451781 683495 := bstep (se 1 (by rfl) ⟨512621, by rfl⟩ : syracuseStep 683495 = 1025243) B1025243
theorem B454235 : Blo 451781 454235 := bstep (se 1 (by rfl) ⟨340676, by rfl⟩ : syracuseStep 454235 = 681353) B681353
theorem B683627 : Blo 451781 683627 := bstep (se 1 (by rfl) ⟨512720, by rfl⟩ : syracuseStep 683627 = 1025441) B1025441
theorem B16805501 : Blo 451781 16805501 := bstep (se 3 (by rfl) ⟨3151031, by rfl⟩ : syracuseStep 16805501 = 6302063) B6302063
theorem B454471 : Blo 451781 454471 := bstep (se 1 (by rfl) ⟨340853, by rfl⟩ : syracuseStep 454471 = 681707) B681707
theorem B454623 : Blo 451781 454623 := bstep (se 1 (by rfl) ⟨340967, by rfl⟩ : syracuseStep 454623 = 681935) B681935
theorem B454887 : Blo 451781 454887 := bstep (se 1 (by rfl) ⟨341165, by rfl⟩ : syracuseStep 454887 = 682331) B682331
theorem B455039 : Blo 451781 455039 := bstep (se 1 (by rfl) ⟨341279, by rfl⟩ : syracuseStep 455039 = 682559) B682559
theorem B2748809 : Blo 451781 2748809 := bstep (se 2 (by rfl) ⟨1030803, by rfl⟩ : syracuseStep 2748809 = 2061607) B2061607
theorem B455119 : Blo 451781 455119 := bstep (se 1 (by rfl) ⟨341339, by rfl⟩ : syracuseStep 455119 = 682679) B682679
theorem B1470935 : Blo 451781 1470935 := bstep (se 1 (by rfl) ⟨1103201, by rfl⟩ : syracuseStep 1470935 = 2206403) B2206403
theorem B815609 : Blo 451781 815609 := bstep (se 2 (by rfl) ⟨305853, by rfl⟩ : syracuseStep 815609 = 611707) B611707
theorem B455271 : Blo 451781 455271 := bstep (se 1 (by rfl) ⟨341453, by rfl⟩ : syracuseStep 455271 = 682907) B682907
theorem B455535 : Blo 451781 455535 := bstep (se 1 (by rfl) ⟨341651, by rfl⟩ : syracuseStep 455535 = 683303) B683303
theorem B1536893 : Blo 451781 1536893 := bstep (se 3 (by rfl) ⟨288167, by rfl⟩ : syracuseStep 1536893 = 576335) B576335
theorem B455591 : Blo 451781 455591 := bstep (se 1 (by rfl) ⟨341693, by rfl⟩ : syracuseStep 455591 = 683387) B683387
theorem B455675 : Blo 451781 455675 := bstep (se 1 (by rfl) ⟨341756, by rfl⟩ : syracuseStep 455675 = 683513) B683513
theorem B455743 : Blo 451781 455743 := bstep (se 1 (by rfl) ⟨341807, by rfl⟩ : syracuseStep 455743 = 683615) B683615
theorem B1537163 : Blo 451781 1537163 := bstep (se 1 (by rfl) ⟨1152872, by rfl⟩ : syracuseStep 1537163 = 2305745) B2305745
theorem B1143983 : Blo 451781 1143983 := bstep (se 1 (by rfl) ⟨857987, by rfl⟩ : syracuseStep 1143983 = 1715975) B1715975
theorem B1307935 : Blo 451781 1307935 := bstep (se 1 (by rfl) ⟨980951, by rfl⟩ : syracuseStep 1307935 = 1961903) B1961903
theorem B2291651 : Blo 451781 2291651 := bstep (se 1 (by rfl) ⟨1718738, by rfl⟩ : syracuseStep 2291651 = 3437477) B3437477
theorem B1144975 : Blo 451781 1144975 := bstep (se 1 (by rfl) ⟨858731, by rfl⟩ : syracuseStep 1144975 = 1717463) B1717463
theorem B1636595 : Blo 451781 1636595 := bstep (se 1 (by rfl) ⟨1227446, by rfl⟩ : syracuseStep 1636595 = 2454893) B2454893
theorem B2291975 : Blo 451781 2291975 := bstep (se 1 (by rfl) ⟨1718981, by rfl⟩ : syracuseStep 2291975 = 3437963) B3437963
theorem B1145897 : Blo 451781 1145897 := bstep (se 2 (by rfl) ⟨429711, by rfl⟩ : syracuseStep 1145897 = 859423) B859423
theorem B1145927 : Blo 451781 1145927 := bstep (se 1 (by rfl) ⟨859445, by rfl⟩ : syracuseStep 1145927 = 1718891) B1718891
theorem B818441 : Blo 451781 818441 := bstep (se 2 (by rfl) ⟨306915, by rfl⟩ : syracuseStep 818441 = 613831) B613831
theorem B2293433 : Blo 451781 2293433 := bstep (se 2 (by rfl) ⟨860037, by rfl⟩ : syracuseStep 2293433 = 1720075) B1720075
theorem B1180075 : Blo 451781 1180075 := bstep (se 1 (by rfl) ⟨885056, by rfl⟩ : syracuseStep 1180075 = 1770113) B1770113
theorem B8389423 : Blo 451781 8389423 := bstep (se 1 (by rfl) ⟨6292067, by rfl⟩ : syracuseStep 8389423 = 12584135) B12584135
theorem B689095 : Blo 451781 689095 := bstep (se 1 (by rfl) ⟨516821, by rfl⟩ : syracuseStep 689095 = 1033643) B1033643
theorem B1017179 : Blo 451781 1017179 := bstep (se 1 (by rfl) ⟨762884, by rfl⟩ : syracuseStep 1017179 = 1525769) B1525769
theorem B1934711 : Blo 451781 1934711 := bstep (se 1 (by rfl) ⟨1451033, by rfl⟩ : syracuseStep 1934711 = 2902067) B2902067
theorem B2295215 : Blo 451781 2295215 := bstep (se 1 (by rfl) ⟨1721411, by rfl⟩ : syracuseStep 2295215 = 3442823) B3442823
theorem B1017449 : Blo 451781 1017449 := bstep (se 2 (by rfl) ⟨381543, by rfl⟩ : syracuseStep 1017449 = 763087) B763087
theorem B3442337 : Blo 451781 3442337 := bstep (se 2 (by rfl) ⟨1290876, by rfl⟩ : syracuseStep 3442337 = 2581753) B2581753
theorem B1018043 : Blo 451781 1018043 := bstep (se 1 (by rfl) ⟨763532, by rfl⟩ : syracuseStep 1018043 = 1527065) B1527065
theorem B2066647 : Blo 451781 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B1018079 : Blo 451781 1018079 := bstep (se 1 (by rfl) ⟨763559, by rfl⟩ : syracuseStep 1018079 = 1527119) B1527119
theorem B1018529 : Blo 451781 1018529 := bstep (se 2 (by rfl) ⟨381948, by rfl⟩ : syracuseStep 1018529 = 763897) B763897
theorem B1018745 : Blo 451781 1018745 := bstep (se 2 (by rfl) ⟨382029, by rfl⟩ : syracuseStep 1018745 = 764059) B764059
theorem B1018889 : Blo 451781 1018889 := bstep (se 2 (by rfl) ⟨382083, by rfl⟩ : syracuseStep 1018889 = 764167) B764167
theorem B1870895 : Blo 451781 1870895 := bstep (se 1 (by rfl) ⟨1403171, by rfl⟩ : syracuseStep 1870895 = 2806343) B2806343
theorem B1018943 : Blo 451781 1018943 := bstep (se 1 (by rfl) ⟨764207, by rfl⟩ : syracuseStep 1018943 = 1528415) B1528415
theorem B4361323 : Blo 451781 4361323 := bstep (se 1 (by rfl) ⟨3270992, by rfl⟩ : syracuseStep 4361323 = 6541985) B6541985
theorem B1150139 : Blo 451781 1150139 := bstep (se 1 (by rfl) ⟨862604, by rfl⟩ : syracuseStep 1150139 = 1725209) B1725209
theorem B2591959 : Blo 451781 2591959 := bstep (se 1 (by rfl) ⟨1943969, by rfl⟩ : syracuseStep 2591959 = 3887939) B3887939
theorem B1478027 : Blo 451781 1478027 := bstep (se 1 (by rfl) ⟨1108520, by rfl⟩ : syracuseStep 1478027 = 2217041) B2217041
theorem B1150433 : Blo 451781 1150433 := bstep (se 2 (by rfl) ⟨431412, by rfl⟩ : syracuseStep 1150433 = 862825) B862825
theorem B7868279 : Blo 451781 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B1019771 : Blo 451781 1019771 := bstep (se 1 (by rfl) ⟨764828, by rfl⟩ : syracuseStep 1019771 = 1529657) B1529657
theorem B2101115 : Blo 451781 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B1019879 : Blo 451781 1019879 := bstep (se 1 (by rfl) ⟨764909, by rfl⟩ : syracuseStep 1019879 = 1529819) B1529819
theorem B1020059 : Blo 451781 1020059 := bstep (se 1 (by rfl) ⟨765044, by rfl⟩ : syracuseStep 1020059 = 1530089) B1530089
theorem B6295805 : Blo 451781 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B7344425 : Blo 451781 7344425 := bstep (se 2 (by rfl) ⟨2754159, by rfl⟩ : syracuseStep 7344425 = 5508319) B5508319
theorem B1839401 : Blo 451781 1839401 := bstep (se 2 (by rfl) ⟨689775, by rfl⟩ : syracuseStep 1839401 = 1379551) B1379551
theorem B1151273 : Blo 451781 1151273 := bstep (se 2 (by rfl) ⟨431727, by rfl⟩ : syracuseStep 1151273 = 863455) B863455
theorem B1020257 : Blo 451781 1020257 := bstep (se 2 (by rfl) ⟨382596, by rfl⟩ : syracuseStep 1020257 = 765193) B765193
theorem B1020347 : Blo 451781 1020347 := bstep (se 1 (by rfl) ⟨765260, by rfl⟩ : syracuseStep 1020347 = 1530521) B1530521
theorem B1938077 : Blo 451781 1938077 := bstep (se 3 (by rfl) ⟨363389, by rfl⟩ : syracuseStep 1938077 = 726779) B726779
theorem B3281579 : Blo 451781 3281579 := bstep (se 1 (by rfl) ⟨2461184, by rfl⟩ : syracuseStep 3281579 = 4922369) B4922369
theorem B1840583 : Blo 451781 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B4888151 : Blo 451781 4888151 := bstep (se 1 (by rfl) ⟨3666113, by rfl⟩ : syracuseStep 4888151 = 7332227) B7332227
theorem B1021607 : Blo 451781 1021607 := bstep (se 1 (by rfl) ⟨766205, by rfl⟩ : syracuseStep 1021607 = 1532411) B1532411
theorem B1152731 : Blo 451781 1152731 := bstep (se 1 (by rfl) ⟨864548, by rfl⟩ : syracuseStep 1152731 = 1729097) B1729097
theorem B857927 : Blo 451781 857927 := bstep (se 1 (by rfl) ⟨643445, by rfl⟩ : syracuseStep 857927 = 1286891) B1286891
theorem B1021787 : Blo 451781 1021787 := bstep (se 1 (by rfl) ⟨766340, by rfl⟩ : syracuseStep 1021787 = 1532681) B1532681
theorem B2463625 : Blo 451781 2463625 := bstep (se 2 (by rfl) ⟨923859, by rfl⟩ : syracuseStep 2463625 = 1847719) B1847719
theorem B3446711 : Blo 451781 3446711 := bstep (se 1 (by rfl) ⟨2585033, by rfl⟩ : syracuseStep 3446711 = 5170067) B5170067
theorem B2594875 : Blo 451781 2594875 := bstep (se 1 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 2594875 = 3892313) B3892313
theorem B858451 : Blo 451781 858451 := bstep (se 1 (by rfl) ⟨643838, by rfl⟩ : syracuseStep 858451 = 1287677) B1287677
theorem B1022291 : Blo 451781 1022291 := bstep (se 1 (by rfl) ⟨766718, by rfl⟩ : syracuseStep 1022291 = 1533437) B1533437
theorem B1153511 : Blo 451781 1153511 := bstep (se 1 (by rfl) ⟨865133, by rfl⟩ : syracuseStep 1153511 = 1730267) B1730267
theorem B3283679 : Blo 451781 3283679 := bstep (se 1 (by rfl) ⟨2462759, by rfl⟩ : syracuseStep 3283679 = 4925519) B4925519
theorem B3480317 : Blo 451781 3480317 := bstep (se 3 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 3480317 = 1305119) B1305119
theorem B858937 : Blo 451781 858937 := bstep (se 2 (by rfl) ⟨322101, by rfl⟩ : syracuseStep 858937 = 644203) B644203
theorem B1022777 : Blo 451781 1022777 := bstep (se 2 (by rfl) ⟨383541, by rfl⟩ : syracuseStep 1022777 = 767083) B767083
theorem B1022831 : Blo 451781 1022831 := bstep (se 1 (by rfl) ⟨767123, by rfl⟩ : syracuseStep 1022831 = 1534247) B1534247
theorem B1743913 : Blo 451781 1743913 := bstep (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) B1307935
theorem B1023407 : Blo 451781 1023407 := bstep (se 1 (by rfl) ⟨767555, by rfl⟩ : syracuseStep 1023407 = 1535111) B1535111
theorem B1023479 : Blo 451781 1023479 := bstep (se 1 (by rfl) ⟨767609, by rfl⟩ : syracuseStep 1023479 = 1535219) B1535219
theorem B6627035 : Blo 451781 6627035 := bstep (se 1 (by rfl) ⟨4970276, by rfl⟩ : syracuseStep 6627035 = 9940553) B9940553
theorem B3874817 : Blo 451781 3874817 := bstep (se 2 (by rfl) ⟨1453056, by rfl⟩ : syracuseStep 3874817 = 2906113) B2906113
theorem B1024505 : Blo 451781 1024505 := bstep (se 2 (by rfl) ⟨384189, by rfl⟩ : syracuseStep 1024505 = 768379) B768379
theorem B860699 : Blo 451781 860699 := bstep (se 1 (by rfl) ⟨645524, by rfl⟩ : syracuseStep 860699 = 1291049) B1291049
theorem B1024595 : Blo 451781 1024595 := bstep (se 1 (by rfl) ⟨768446, by rfl⟩ : syracuseStep 1024595 = 1536893) B1536893
theorem B12460715 : Blo 451781 12460715 := bstep (se 1 (by rfl) ⟨9345536, by rfl⟩ : syracuseStep 12460715 = 18691073) B18691073
theorem B1024775 : Blo 451781 1024775 := bstep (se 1 (by rfl) ⟨768581, by rfl⟩ : syracuseStep 1024775 = 1537163) B1537163
theorem B762655 : Blo 451781 762655 := bstep (se 1 (by rfl) ⟨571991, by rfl⟩ : syracuseStep 762655 = 1143983) B1143983
theorem B861025 : Blo 451781 861025 := bstep (se 2 (by rfl) ⟨322884, by rfl⟩ : syracuseStep 861025 = 645769) B645769
theorem B1024865 : Blo 451781 1024865 := bstep (se 2 (by rfl) ⟨384324, by rfl⟩ : syracuseStep 1024865 = 768649) B768649
theorem B2172359 : Blo 451781 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B1091063 : Blo 451781 1091063 := bstep (se 1 (by rfl) ⟨818297, by rfl⟩ : syracuseStep 1091063 = 1636595) B1636595
theorem B763465 : Blo 451781 763465 := bstep (se 2 (by rfl) ⟨286299, by rfl⟩ : syracuseStep 763465 = 572599) B572599
theorem B861769 : Blo 451781 861769 := bstep (se 2 (by rfl) ⟨323163, by rfl⟩ : syracuseStep 861769 = 646327) B646327
theorem B763931 : Blo 451781 763931 := bstep (se 1 (by rfl) ⟨572948, by rfl⟩ : syracuseStep 763931 = 1145897) B1145897
theorem B763951 : Blo 451781 763951 := bstep (se 1 (by rfl) ⟨572963, by rfl⟩ : syracuseStep 763951 = 1145927) B1145927
theorem B862255 : Blo 451781 862255 := bstep (se 1 (by rfl) ⟨646691, by rfl⟩ : syracuseStep 862255 = 1293383) B1293383
theorem B3877415 : Blo 451781 3877415 := bstep (se 1 (by rfl) ⟨2908061, by rfl⟩ : syracuseStep 3877415 = 5816123) B5816123
theorem B7776971 : Blo 451781 7776971 := bstep (se 1 (by rfl) ⟨5832728, by rfl⟩ : syracuseStep 7776971 = 11665457) B11665457
theorem B5319431 : Blo 451781 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B863273 : Blo 451781 863273 := bstep (se 2 (by rfl) ⟨323727, by rfl⟩ : syracuseStep 863273 = 647455) B647455
theorem B1289465 : Blo 451781 1289465 := bstep (se 2 (by rfl) ⟨483549, by rfl⟩ : syracuseStep 1289465 = 967099) B967099
theorem B1944911 : Blo 451781 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B1453801 : Blo 451781 1453801 := bstep (se 2 (by rfl) ⟨545175, by rfl⟩ : syracuseStep 1453801 = 1090351) B1090351
theorem B4665221 : Blo 451781 4665221 := bstep (se 4 (by rfl) ⟨437364, by rfl⟩ : syracuseStep 4665221 = 874729) B874729
theorem B2174957 : Blo 451781 2174957 := bstep (se 3 (by rfl) ⟨407804, by rfl⟩ : syracuseStep 2174957 = 815609) B815609
theorem B100642823 : Blo 451781 100642823 := bstep (se 1 (by rfl) ⟨75482117, by rfl⟩ : syracuseStep 100642823 = 150964235) B150964235
theorem B1093715 : Blo 451781 1093715 := bstep (se 1 (by rfl) ⟨820286, by rfl⟩ : syracuseStep 1093715 = 1640573) B1640573
theorem B1093907 : Blo 451781 1093907 := bstep (se 1 (by rfl) ⟨820430, by rfl⟩ : syracuseStep 1093907 = 1640861) B1640861
theorem B1290809 : Blo 451781 1290809 := bstep (se 2 (by rfl) ⟨484053, by rfl⟩ : syracuseStep 1290809 = 968107) B968107
theorem B865019 : Blo 451781 865019 := bstep (se 1 (by rfl) ⟨648764, by rfl⟩ : syracuseStep 865019 = 1297529) B1297529
theorem B1717159 : Blo 451781 1717159 := bstep (se 1 (by rfl) ⟨1287869, by rfl⟩ : syracuseStep 1717159 = 2575739) B2575739
theorem B1914799 : Blo 451781 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B571855 : Blo 451781 571855 := bstep (se 1 (by rfl) ⟨428891, by rfl⟩ : syracuseStep 571855 = 857783) B857783
theorem B1718921 : Blo 451781 1718921 := bstep (se 2 (by rfl) ⟨644595, by rfl⟩ : syracuseStep 1718921 = 1289191) B1289191
theorem B769115 : Blo 451781 769115 := bstep (se 1 (by rfl) ⟨576836, by rfl⟩ : syracuseStep 769115 = 1153673) B1153673
theorem B1228007 : Blo 451781 1228007 := bstep (se 1 (by rfl) ⟨921005, by rfl⟩ : syracuseStep 1228007 = 1842011) B1842011
theorem B1293691 : Blo 451781 1293691 := bstep (se 1 (by rfl) ⟨970268, by rfl⟩ : syracuseStep 1293691 = 1940537) B1940537
theorem B1031743 : Blo 451781 1031743 := bstep (se 1 (by rfl) ⟨773807, by rfl⟩ : syracuseStep 1031743 = 1547615) B1547615
theorem B1229035 : Blo 451781 1229035 := bstep (se 1 (by rfl) ⟨921776, by rfl⟩ : syracuseStep 1229035 = 1843553) B1843553
theorem B573743 : Blo 451781 573743 := bstep (se 1 (by rfl) ⟨430307, by rfl⟩ : syracuseStep 573743 = 860615) B860615
theorem B1458695 : Blo 451781 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B6275969 : Blo 451781 6275969 := bstep (se 2 (by rfl) ⟨2353488, by rfl⟩ : syracuseStep 6275969 = 4706977) B4706977
theorem B1721519 : Blo 451781 1721519 := bstep (se 1 (by rfl) ⟨1291139, by rfl⟩ : syracuseStep 1721519 = 2582279) B2582279
theorem B2573531 : Blo 451781 2573531 := bstep (se 1 (by rfl) ⟨1930148, by rfl⟩ : syracuseStep 2573531 = 3860297) B3860297
theorem B7357661 : Blo 451781 7357661 := bstep (se 3 (by rfl) ⟨1379561, by rfl⟩ : syracuseStep 7357661 = 2759123) B2759123
theorem B1525175 : Blo 451781 1525175 := bstep (se 1 (by rfl) ⟨1143881, by rfl⟩ : syracuseStep 1525175 = 2287763) B2287763
theorem B9848267 : Blo 451781 9848267 := bstep (se 1 (by rfl) ⟨7386200, by rfl⟩ : syracuseStep 9848267 = 14772401) B14772401
theorem B509467 : Blo 451781 509467 := bstep (se 1 (by rfl) ⟨382100, by rfl⟩ : syracuseStep 509467 = 764201) B764201
theorem B968363 : Blo 451781 968363 := bstep (se 1 (by rfl) ⟨726272, by rfl⟩ : syracuseStep 968363 = 1452545) B1452545
theorem B4376393 : Blo 451781 4376393 := bstep (se 2 (by rfl) ⟨1641147, by rfl⟩ : syracuseStep 4376393 = 3282295) B3282295
theorem B10504495 : Blo 451781 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B11028905 : Blo 451781 11028905 := bstep (se 2 (by rfl) ⟨4135839, by rfl⟩ : syracuseStep 11028905 = 8271679) B8271679
theorem B510511 : Blo 451781 510511 := bstep (se 1 (by rfl) ⟨382883, by rfl⟩ : syracuseStep 510511 = 765767) B765767
theorem B1526633 : Blo 451781 1526633 := bstep (se 2 (by rfl) ⟨572487, by rfl⟩ : syracuseStep 1526633 = 1144975) B1144975
theorem B1723265 : Blo 451781 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B510943 : Blo 451781 510943 := bstep (se 1 (by rfl) ⟨383207, by rfl⟩ : syracuseStep 510943 = 766415) B766415
theorem B8702963 : Blo 451781 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B9817307 : Blo 451781 9817307 := bstep (se 1 (by rfl) ⟨7362980, by rfl⟩ : syracuseStep 9817307 = 14725961) B14725961
theorem B3460319 : Blo 451781 3460319 := bstep (se 1 (by rfl) ⟨2595239, by rfl⟩ : syracuseStep 3460319 = 5190479) B5190479
theorem B4378009 : Blo 451781 4378009 := bstep (se 2 (by rfl) ⟨1641753, by rfl⟩ : syracuseStep 4378009 = 3283507) B3283507
theorem B511591 : Blo 451781 511591 := bstep (se 1 (by rfl) ⟨383693, by rfl⟩ : syracuseStep 511591 = 767387) B767387
theorem B511807 : Blo 451781 511807 := bstep (se 1 (by rfl) ⟨383855, by rfl⟩ : syracuseStep 511807 = 767711) B767711
theorem B1527767 : Blo 451781 1527767 := bstep (se 1 (by rfl) ⟨1145825, by rfl⟩ : syracuseStep 1527767 = 2291651) B2291651
theorem B1167335 : Blo 451781 1167335 := bstep (se 1 (by rfl) ⟨875501, by rfl⟩ : syracuseStep 1167335 = 1751003) B1751003
theorem B512095 : Blo 451781 512095 := bstep (se 1 (by rfl) ⟨384071, by rfl⟩ : syracuseStep 512095 = 768143) B768143
theorem B1527983 : Blo 451781 1527983 := bstep (se 1 (by rfl) ⟨1145987, by rfl⟩ : syracuseStep 1527983 = 2291975) B2291975
theorem B1724753 : Blo 451781 1724753 := bstep (se 2 (by rfl) ⟨646782, by rfl⟩ : syracuseStep 1724753 = 1293565) B1293565
theorem B971131 : Blo 451781 971131 := bstep (se 1 (by rfl) ⟨728348, by rfl⟩ : syracuseStep 971131 = 1456697) B1456697
theorem B643639 : Blo 451781 643639 := bstep (se 1 (by rfl) ⟨482729, by rfl⟩ : syracuseStep 643639 = 965459) B965459
theorem B545627 : Blo 451781 545627 := bstep (se 1 (by rfl) ⟨409220, by rfl⟩ : syracuseStep 545627 = 818441) B818441
theorem B1725421 : Blo 451781 1725421 := bstep (se 3 (by rfl) ⟨323516, by rfl⟩ : syracuseStep 1725421 = 647033) B647033
theorem B8279117 : Blo 451781 8279117 := bstep (se 3 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 8279117 = 3104669) B3104669
theorem B1528955 : Blo 451781 1528955 := bstep (se 1 (by rfl) ⟨1146716, by rfl⟩ : syracuseStep 1528955 = 2293433) B2293433
theorem B1037519 : Blo 451781 1037519 := bstep (se 1 (by rfl) ⟨778139, by rfl⟩ : syracuseStep 1037519 = 1556279) B1556279
theorem B1529225 : Blo 451781 1529225 := bstep (se 2 (by rfl) ⟨573459, by rfl⟩ : syracuseStep 1529225 = 1146919) B1146919
theorem B677723 : Blo 451781 677723 := bstep (se 1 (by rfl) ⟨508292, by rfl⟩ : syracuseStep 677723 = 1016585) B1016585
theorem B645023 : Blo 451781 645023 := bstep (se 1 (by rfl) ⟨483767, by rfl⟩ : syracuseStep 645023 = 967535) B967535
theorem B8312807 : Blo 451781 8312807 := bstep (se 1 (by rfl) ⟨6234605, by rfl⟩ : syracuseStep 8312807 = 12469211) B12469211
theorem B10442789 : Blo 451781 10442789 := bstep (se 4 (by rfl) ⟨979011, by rfl⟩ : syracuseStep 10442789 = 1958023) B1958023
theorem B94197917 : Blo 451781 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B678107 : Blo 451781 678107 := bstep (se 1 (by rfl) ⟨508580, by rfl⟩ : syracuseStep 678107 = 1017161) B1017161
theorem B1726697 : Blo 451781 1726697 := bstep (se 2 (by rfl) ⟨647511, by rfl⟩ : syracuseStep 1726697 = 1295023) B1295023
theorem B1038649 : Blo 451781 1038649 := bstep (se 2 (by rfl) ⟨389493, by rfl⟩ : syracuseStep 1038649 = 778987) B778987
theorem B1726879 : Blo 451781 1726879 := bstep (se 1 (by rfl) ⟨1295159, by rfl⟩ : syracuseStep 1726879 = 2590319) B2590319
theorem B678377 : Blo 451781 678377 := bstep (se 2 (by rfl) ⟨254391, by rfl⟩ : syracuseStep 678377 = 508783) B508783
theorem B4413971 : Blo 451781 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B3431159 : Blo 451781 3431159 := bstep (se 1 (by rfl) ⟨2573369, by rfl⟩ : syracuseStep 3431159 = 5146739) B5146739
theorem B13097807 : Blo 451781 13097807 := bstep (se 1 (by rfl) ⟨9823355, by rfl⟩ : syracuseStep 13097807 = 19646711) B19646711
theorem B678767 : Blo 451781 678767 := bstep (se 1 (by rfl) ⟨509075, by rfl⟩ : syracuseStep 678767 = 1018151) B1018151
theorem B678779 : Blo 451781 678779 := bstep (se 1 (by rfl) ⟨509084, by rfl⟩ : syracuseStep 678779 = 1018169) B1018169
theorem B7462205 : Blo 451781 7462205 := bstep (se 3 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 7462205 = 2798327) B2798327
theorem B1727851 : Blo 451781 1727851 := bstep (se 1 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 1727851 = 2591777) B2591777
theorem B1728125 : Blo 451781 1728125 := bstep (se 3 (by rfl) ⟨324023, by rfl⟩ : syracuseStep 1728125 = 648047) B648047
theorem B679643 : Blo 451781 679643 := bstep (se 1 (by rfl) ⟨509732, by rfl⟩ : syracuseStep 679643 = 1019465) B1019465
theorem B679913 : Blo 451781 679913 := bstep (se 2 (by rfl) ⟨254967, by rfl⟩ : syracuseStep 679913 = 509935) B509935
theorem B680615 : Blo 451781 680615 := bstep (se 1 (by rfl) ⟨510461, by rfl⟩ : syracuseStep 680615 = 1020923) B1020923
theorem B680735 : Blo 451781 680735 := bstep (se 1 (by rfl) ⟨510551, by rfl⟩ : syracuseStep 680735 = 1021103) B1021103
theorem B18834221 : Blo 451781 18834221 := bstep (se 3 (by rfl) ⟨3531416, by rfl⟩ : syracuseStep 18834221 = 7062833) B7062833
theorem B680759 : Blo 451781 680759 := bstep (se 1 (by rfl) ⟨510569, by rfl⟩ : syracuseStep 680759 = 1021139) B1021139
theorem B680939 : Blo 451781 680939 := bstep (se 1 (by rfl) ⟨510704, by rfl⟩ : syracuseStep 680939 = 1021409) B1021409
theorem B451807 : Blo 451781 451807 := bstep (se 1 (by rfl) ⟨338855, by rfl⟩ : syracuseStep 451807 = 677711) B677711
theorem B451887 : Blo 451781 451887 := bstep (se 1 (by rfl) ⟨338915, by rfl⟩ : syracuseStep 451887 = 677831) B677831
theorem B1467895 : Blo 451781 1467895 := bstep (se 1 (by rfl) ⟨1100921, by rfl⟩ : syracuseStep 1467895 = 2201843) B2201843
theorem B452123 : Blo 451781 452123 := bstep (se 1 (by rfl) ⟨339092, by rfl⟩ : syracuseStep 452123 = 678185) B678185
theorem B452127 : Blo 451781 452127 := bstep (se 1 (by rfl) ⟨339095, by rfl⟩ : syracuseStep 452127 = 678191) B678191
theorem B452287 : Blo 451781 452287 := bstep (se 1 (by rfl) ⟨339215, by rfl⟩ : syracuseStep 452287 = 678431) B678431
theorem B452543 : Blo 451781 452543 := bstep (se 1 (by rfl) ⟨339407, by rfl⟩ : syracuseStep 452543 = 678815) B678815
theorem B452575 : Blo 451781 452575 := bstep (se 1 (by rfl) ⟨339431, by rfl⟩ : syracuseStep 452575 = 678863) B678863
theorem B452635 : Blo 451781 452635 := bstep (se 1 (by rfl) ⟨339476, by rfl⟩ : syracuseStep 452635 = 678953) B678953
theorem B452639 : Blo 451781 452639 := bstep (se 1 (by rfl) ⟨339479, by rfl⟩ : syracuseStep 452639 = 678959) B678959
theorem B452655 : Blo 451781 452655 := bstep (se 1 (by rfl) ⟨339491, by rfl⟩ : syracuseStep 452655 = 678983) B678983
theorem B682031 : Blo 451781 682031 := bstep (se 1 (by rfl) ⟨511523, by rfl⟩ : syracuseStep 682031 = 1023047) B1023047
theorem B1566803 : Blo 451781 1566803 := bstep (se 1 (by rfl) ⟨1175102, by rfl⟩ : syracuseStep 1566803 = 2350205) B2350205
theorem B1108091 : Blo 451781 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B452831 : Blo 451781 452831 := bstep (se 1 (by rfl) ⟨339623, by rfl⟩ : syracuseStep 452831 = 679247) B679247
theorem B452891 : Blo 451781 452891 := bstep (se 1 (by rfl) ⟨339668, by rfl⟩ : syracuseStep 452891 = 679337) B679337
theorem B682295 : Blo 451781 682295 := bstep (se 1 (by rfl) ⟨511721, by rfl⟩ : syracuseStep 682295 = 1023443) B1023443
theorem B452991 : Blo 451781 452991 := bstep (se 1 (by rfl) ⟨339743, by rfl⟩ : syracuseStep 452991 = 679487) B679487
theorem B3107297 : Blo 451781 3107297 := bstep (se 2 (by rfl) ⟨1165236, by rfl⟩ : syracuseStep 3107297 = 2330473) B2330473
theorem B682475 : Blo 451781 682475 := bstep (se 1 (by rfl) ⟨511856, by rfl⟩ : syracuseStep 682475 = 1023713) B1023713
theorem B453167 : Blo 451781 453167 := bstep (se 1 (by rfl) ⟨339875, by rfl⟩ : syracuseStep 453167 = 679751) B679751
theorem B453223 : Blo 451781 453223 := bstep (se 1 (by rfl) ⟨339917, by rfl⟩ : syracuseStep 453223 = 679835) B679835
theorem B107342779 : Blo 451781 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B453599 : Blo 451781 453599 := bstep (se 1 (by rfl) ⟨340199, by rfl⟩ : syracuseStep 453599 = 680399) B680399
theorem B453627 : Blo 451781 453627 := bstep (se 1 (by rfl) ⟨340220, by rfl⟩ : syracuseStep 453627 = 680441) B680441
theorem B453695 : Blo 451781 453695 := bstep (se 1 (by rfl) ⟨340271, by rfl⟩ : syracuseStep 453695 = 680543) B680543
theorem B683177 : Blo 451781 683177 := bstep (se 2 (by rfl) ⟨256191, by rfl⟩ : syracuseStep 683177 = 512383) B512383
theorem B454015 : Blo 451781 454015 := bstep (se 1 (by rfl) ⟨340511, by rfl⟩ : syracuseStep 454015 = 681023) B681023
theorem B454043 : Blo 451781 454043 := bstep (se 1 (by rfl) ⟨340532, by rfl⟩ : syracuseStep 454043 = 681065) B681065
theorem B454111 : Blo 451781 454111 := bstep (se 1 (by rfl) ⟨340583, by rfl⟩ : syracuseStep 454111 = 681167) B681167
theorem B683591 : Blo 451781 683591 := bstep (se 1 (by rfl) ⟨512693, by rfl⟩ : syracuseStep 683591 = 1025387) B1025387
theorem B454247 : Blo 451781 454247 := bstep (se 1 (by rfl) ⟨340685, by rfl⟩ : syracuseStep 454247 = 681371) B681371
theorem B454395 : Blo 451781 454395 := bstep (se 1 (by rfl) ⟨340796, by rfl⟩ : syracuseStep 454395 = 681593) B681593
theorem B454463 : Blo 451781 454463 := bstep (se 1 (by rfl) ⟨340847, by rfl⟩ : syracuseStep 454463 = 681695) B681695
theorem B454527 : Blo 451781 454527 := bstep (se 1 (by rfl) ⟨340895, by rfl⟩ : syracuseStep 454527 = 681791) B681791
theorem B454639 : Blo 451781 454639 := bstep (se 1 (by rfl) ⟨340979, by rfl⟩ : syracuseStep 454639 = 681959) B681959
theorem B454651 : Blo 451781 454651 := bstep (se 1 (by rfl) ⟨340988, by rfl⟩ : syracuseStep 454651 = 681977) B681977
theorem B19656755 : Blo 451781 19656755 := bstep (se 1 (by rfl) ⟨14742566, by rfl⟩ : syracuseStep 19656755 = 29485133) B29485133
theorem B454719 : Blo 451781 454719 := bstep (se 1 (by rfl) ⟨341039, by rfl⟩ : syracuseStep 454719 = 682079) B682079
theorem B1536083 : Blo 451781 1536083 := bstep (se 1 (by rfl) ⟨1152062, by rfl⟩ : syracuseStep 1536083 = 2304125) B2304125
theorem B454759 : Blo 451781 454759 := bstep (se 1 (by rfl) ⟨341069, by rfl⟩ : syracuseStep 454759 = 682139) B682139
theorem B454783 : Blo 451781 454783 := bstep (se 1 (by rfl) ⟨341087, by rfl⟩ : syracuseStep 454783 = 682175) B682175
theorem B454811 : Blo 451781 454811 := bstep (se 1 (by rfl) ⟨341108, by rfl⟩ : syracuseStep 454811 = 682217) B682217
theorem B12415169 : Blo 451781 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B455015 : Blo 451781 455015 := bstep (se 1 (by rfl) ⟨341261, by rfl⟩ : syracuseStep 455015 = 682523) B682523
theorem B2290031 : Blo 451781 2290031 := bstep (se 1 (by rfl) ⟨1717523, by rfl⟩ : syracuseStep 2290031 = 3435047) B3435047
theorem B455067 : Blo 451781 455067 := bstep (se 1 (by rfl) ⟨341300, by rfl⟩ : syracuseStep 455067 = 682601) B682601
theorem B455419 : Blo 451781 455419 := bstep (se 1 (by rfl) ⟨341564, by rfl⟩ : syracuseStep 455419 = 683129) B683129
theorem B455487 : Blo 451781 455487 := bstep (se 1 (by rfl) ⟨341615, by rfl⟩ : syracuseStep 455487 = 683231) B683231
theorem B455515 : Blo 451781 455515 := bstep (se 1 (by rfl) ⟨341636, by rfl⟩ : syracuseStep 455515 = 683273) B683273
theorem B455583 : Blo 451781 455583 := bstep (se 1 (by rfl) ⟨341687, by rfl⟩ : syracuseStep 455583 = 683375) B683375
theorem B455663 : Blo 451781 455663 := bstep (se 1 (by rfl) ⟨341747, by rfl⟩ : syracuseStep 455663 = 683495) B683495
theorem B455751 : Blo 451781 455751 := bstep (se 1 (by rfl) ⟨341813, by rfl⟩ : syracuseStep 455751 = 683627) B683627
theorem B11203667 : Blo 451781 11203667 := bstep (se 1 (by rfl) ⟨8402750, by rfl⟩ : syracuseStep 11203667 = 16805501) B16805501
theorem B1930711 : Blo 451781 1930711 := bstep (se 1 (by rfl) ⟨1448033, by rfl⟩ : syracuseStep 1930711 = 2896067) B2896067
theorem B1832539 : Blo 451781 1832539 := bstep (se 1 (by rfl) ⟨1374404, by rfl⟩ : syracuseStep 1832539 = 2748809) B2748809
theorem B980623 : Blo 451781 980623 := bstep (se 1 (by rfl) ⟨735467, by rfl⟩ : syracuseStep 980623 = 1470935) B1470935
theorem B7763849 : Blo 451781 7763849 := bstep (se 2 (by rfl) ⟨2911443, by rfl⟩ : syracuseStep 7763849 = 5822887) B5822887
theorem B2914703 : Blo 451781 2914703 := bstep (se 1 (by rfl) ⟨2186027, by rfl⟩ : syracuseStep 2914703 = 4372055) B4372055
theorem B1932011 : Blo 451781 1932011 := bstep (se 1 (by rfl) ⟨1449008, by rfl⟩ : syracuseStep 1932011 = 2898017) B2898017
theorem B1932113 : Blo 451781 1932113 := bstep (se 2 (by rfl) ⟨724542, by rfl⟩ : syracuseStep 1932113 = 1449085) B1449085
theorem B818267 : Blo 451781 818267 := bstep (se 1 (by rfl) ⟨613700, by rfl⟩ : syracuseStep 818267 = 1227401) B1227401
theorem B3440393 : Blo 451781 3440393 := bstep (se 2 (by rfl) ⟨1290147, by rfl⟩ : syracuseStep 3440393 = 2580295) B2580295
theorem B1638713 : Blo 451781 1638713 := bstep (se 2 (by rfl) ⟨614517, by rfl⟩ : syracuseStep 1638713 = 1229035) B1229035
theorem B1573433 : Blo 451781 1573433 := bstep (se 2 (by rfl) ⟨590037, by rfl⟩ : syracuseStep 1573433 = 1180075) B1180075
theorem B1147679 : Blo 451781 1147679 := bstep (se 1 (by rfl) ⟨860759, by rfl⟩ : syracuseStep 1147679 = 1721519) B1721519
theorem B1016783 : Blo 451781 1016783 := bstep (se 1 (by rfl) ⟨762587, by rfl⟩ : syracuseStep 1016783 = 1525175) B1525175
theorem B1016873 : Blo 451781 1016873 := bstep (se 2 (by rfl) ⟨381327, by rfl⟩ : syracuseStep 1016873 = 762655) B762655
theorem B2294891 : Blo 451781 2294891 := bstep (se 1 (by rfl) ⟨1721168, by rfl⟩ : syracuseStep 2294891 = 3442337) B3442337
theorem B1148033 : Blo 451781 1148033 := bstep (se 2 (by rfl) ⟨430512, by rfl⟩ : syracuseStep 1148033 = 861025) B861025
theorem B2917595 : Blo 451781 2917595 := bstep (se 1 (by rfl) ⟨2188196, by rfl⟩ : syracuseStep 2917595 = 4376393) B4376393
theorem B918793 : Blo 451781 918793 := bstep (se 2 (by rfl) ⟨344547, by rfl⟩ : syracuseStep 918793 = 689095) B689095
theorem B1017755 : Blo 451781 1017755 := bstep (se 1 (by rfl) ⟨763316, by rfl⟩ : syracuseStep 1017755 = 1526633) B1526633
theorem B1148843 : Blo 451781 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B5801975 : Blo 451781 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B1017953 : Blo 451781 1017953 := bstep (se 2 (by rfl) ⟨381732, by rfl⟩ : syracuseStep 1017953 = 763465) B763465
theorem B1149025 : Blo 451781 1149025 := bstep (se 2 (by rfl) ⟨430884, by rfl⟩ : syracuseStep 1149025 = 861769) B861769
theorem B1018511 : Blo 451781 1018511 := bstep (se 1 (by rfl) ⟨763883, by rfl⟩ : syracuseStep 1018511 = 1527767) B1527767
theorem B1018601 : Blo 451781 1018601 := bstep (se 2 (by rfl) ⟨381975, by rfl⟩ : syracuseStep 1018601 = 763951) B763951
theorem B1149673 : Blo 451781 1149673 := bstep (se 2 (by rfl) ⟨431127, by rfl⟩ : syracuseStep 1149673 = 862255) B862255
theorem B1018655 : Blo 451781 1018655 := bstep (se 1 (by rfl) ⟨763991, by rfl⟩ : syracuseStep 1018655 = 1527983) B1527983
theorem B4197203 : Blo 451781 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B1149835 : Blo 451781 1149835 := bstep (se 1 (by rfl) ⟨862376, by rfl⟩ : syracuseStep 1149835 = 1724753) B1724753
theorem B2755529 : Blo 451781 2755529 := bstep (se 2 (by rfl) ⟨1033323, by rfl⟩ : syracuseStep 2755529 = 2066647) B2066647
theorem B1019303 : Blo 451781 1019303 := bstep (se 1 (by rfl) ⟨764477, by rfl⟩ : syracuseStep 1019303 = 1528955) B1528955
theorem B691679 : Blo 451781 691679 := bstep (se 1 (by rfl) ⟨518759, by rfl⟩ : syracuseStep 691679 = 1037519) B1037519
theorem B1019483 : Blo 451781 1019483 := bstep (se 1 (by rfl) ⟨764612, by rfl⟩ : syracuseStep 1019483 = 1529225) B1529225
theorem B2297807 : Blo 451781 2297807 := bstep (se 1 (by rfl) ⟨1723355, by rfl⟩ : syracuseStep 2297807 = 3446711) B3446711
theorem B5541871 : Blo 451781 5541871 := bstep (se 1 (by rfl) ⟨4156403, by rfl⟩ : syracuseStep 5541871 = 8312807) B8312807
theorem B1151131 : Blo 451781 1151131 := bstep (se 1 (by rfl) ⟨863348, by rfl⟩ : syracuseStep 1151131 = 1726697) B1726697
theorem B5837345 : Blo 451781 5837345 := bstep (se 2 (by rfl) ⟨2189004, by rfl⟩ : syracuseStep 5837345 = 4378009) B4378009
theorem B1938401 : Blo 451781 1938401 := bstep (se 2 (by rfl) ⟨726900, by rfl⟩ : syracuseStep 1938401 = 1453801) B1453801
theorem B1152083 : Blo 451781 1152083 := bstep (se 1 (by rfl) ⟨864062, by rfl⟩ : syracuseStep 1152083 = 1728125) B1728125
theorem B2954909 : Blo 451781 2954909 := bstep (se 3 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 2954909 = 1108091) B1108091
theorem B12556147 : Blo 451781 12556147 := bstep (se 1 (by rfl) ⟨9417110, by rfl⟩ : syracuseStep 12556147 = 18834221) B18834221
theorem B858185 : Blo 451781 858185 := bstep (se 2 (by rfl) ⟨321819, by rfl⟩ : syracuseStep 858185 = 643639) B643639
theorem B1448239 : Blo 451781 1448239 := bstep (se 1 (by rfl) ⟨1086179, by rfl⟩ : syracuseStep 1448239 = 2172359) B2172359
theorem B727375 : Blo 451781 727375 := bstep (se 1 (by rfl) ⟨545531, by rfl⟩ : syracuseStep 727375 = 1091063) B1091063
theorem B2300561 : Blo 451781 2300561 := bstep (se 2 (by rfl) ⟨862710, by rfl⟩ : syracuseStep 2300561 = 1725421) B1725421
theorem B2071531 : Blo 451781 2071531 := bstep (se 1 (by rfl) ⟨1553648, by rfl⟩ : syracuseStep 2071531 = 3107297) B3107297
theorem B5184647 : Blo 451781 5184647 := bstep (se 1 (by rfl) ⟨3888485, by rfl⟩ : syracuseStep 5184647 = 7776971) B7776971
theorem B3546287 : Blo 451781 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B859643 : Blo 451781 859643 := bstep (se 1 (by rfl) ⟨644732, by rfl⟩ : syracuseStep 859643 = 1289465) B1289465
theorem B3284833 : Blo 451781 3284833 := bstep (se 2 (by rfl) ⟨1231812, by rfl⟩ : syracuseStep 3284833 = 2463625) B2463625
theorem B1449971 : Blo 451781 1449971 := bstep (se 1 (by rfl) ⟨1087478, by rfl⟩ : syracuseStep 1449971 = 2174957) B2174957
theorem B1024055 : Blo 451781 1024055 := bstep (se 1 (by rfl) ⟨768041, by rfl⟩ : syracuseStep 1024055 = 1536083) B1536083
theorem B729143 : Blo 451781 729143 := bstep (se 1 (by rfl) ⟨546857, by rfl⟩ : syracuseStep 729143 = 1093715) B1093715
theorem B4989053 : Blo 451781 4989053 := bstep (se 3 (by rfl) ⟨935447, by rfl⟩ : syracuseStep 4989053 = 1870895) B1870895
theorem B729271 : Blo 451781 729271 := bstep (se 1 (by rfl) ⟨546953, by rfl⟩ : syracuseStep 729271 = 1093907) B1093907
theorem B860539 : Blo 451781 860539 := bstep (se 1 (by rfl) ⟨645404, by rfl⟩ : syracuseStep 860539 = 1290809) B1290809
theorem B1384865 : Blo 451781 1384865 := bstep (se 2 (by rfl) ⟨519324, by rfl⟩ : syracuseStep 1384865 = 1038649) B1038649
theorem B2302505 : Blo 451781 2302505 := bstep (se 2 (by rfl) ⟨863439, by rfl⟩ : syracuseStep 2302505 = 1726879) B1726879
theorem B762473 : Blo 451781 762473 := bstep (se 2 (by rfl) ⟨285927, by rfl⟩ : syracuseStep 762473 = 571855) B571855
theorem B3941405 : Blo 451781 3941405 := bstep (se 3 (by rfl) ⟨739013, by rfl⟩ : syracuseStep 3941405 = 1478027) B1478027
theorem B1943135 : Blo 451781 1943135 := bstep (se 1 (by rfl) ⟨1457351, by rfl⟩ : syracuseStep 1943135 = 2914703) B2914703
theorem B2303801 : Blo 451781 2303801 := bstep (se 2 (by rfl) ⟨863925, by rfl⟩ : syracuseStep 2303801 = 1727851) B1727851
theorem B1288007 : Blo 451781 1288007 := bstep (se 1 (by rfl) ⟨966005, by rfl⟩ : syracuseStep 1288007 = 1932011) B1932011
theorem B1288075 : Blo 451781 1288075 := bstep (se 1 (by rfl) ⟨966056, by rfl⟩ : syracuseStep 1288075 = 1932113) B1932113
theorem B20982077 : Blo 451781 20982077 := bstep (se 3 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 20982077 = 7868279) B7868279
theorem B1715687 : Blo 451781 1715687 := bstep (se 1 (by rfl) ⟨1286765, by rfl⟩ : syracuseStep 1715687 = 2573531) B2573531
theorem B1289807 : Blo 451781 1289807 := bstep (se 1 (by rfl) ⟨967355, by rfl⟩ : syracuseStep 1289807 = 1934711) B1934711
theorem B8728181 : Blo 451781 8728181 := bstep (se 5 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 8728181 = 818267) B818267
theorem B6565511 : Blo 451781 6565511 := bstep (se 1 (by rfl) ⟨4924133, by rfl⟩ : syracuseStep 6565511 = 9848267) B9848267
theorem B11185897 : Blo 451781 11185897 := bstep (se 2 (by rfl) ⟨4194711, by rfl⟩ : syracuseStep 11185897 = 8389423) B8389423
theorem B7352603 : Blo 451781 7352603 := bstep (se 1 (by rfl) ⟨5514452, by rfl⟩ : syracuseStep 7352603 = 11028905) B11028905
theorem B2306717 : Blo 451781 2306717 := bstep (se 3 (by rfl) ⟨432509, by rfl⟩ : syracuseStep 2306717 = 865019) B865019
theorem B766759 : Blo 451781 766759 := bstep (se 1 (by rfl) ⟨575069, by rfl⟩ : syracuseStep 766759 = 1150139) B1150139
theorem B2306879 : Blo 451781 2306879 := bstep (se 1 (by rfl) ⟨1730159, by rfl⟩ : syracuseStep 2306879 = 3460319) B3460319
theorem B1455005 : Blo 451781 1455005 := bstep (se 3 (by rfl) ⟨272813, by rfl⟩ : syracuseStep 1455005 = 545627) B545627
theorem B766955 : Blo 451781 766955 := bstep (se 1 (by rfl) ⟨575216, by rfl⟩ : syracuseStep 766955 = 1150433) B1150433
theorem B4896283 : Blo 451781 4896283 := bstep (se 1 (by rfl) ⟨3672212, by rfl⟩ : syracuseStep 4896283 = 7344425) B7344425
theorem B1226267 : Blo 451781 1226267 := bstep (se 1 (by rfl) ⟨919700, by rfl⟩ : syracuseStep 1226267 = 1839401) B1839401
theorem B767515 : Blo 451781 767515 := bstep (se 1 (by rfl) ⟨575636, by rfl⟩ : syracuseStep 767515 = 1151273) B1151273
theorem B14005993 : Blo 451781 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B1292051 : Blo 451781 1292051 := bstep (se 1 (by rfl) ⟨969038, by rfl⟩ : syracuseStep 1292051 = 1938077) B1938077
theorem B5519411 : Blo 451781 5519411 := bstep (se 1 (by rfl) ⟨4139558, by rfl⟩ : syracuseStep 5519411 = 8279117) B8279117
theorem B3258767 : Blo 451781 3258767 := bstep (se 1 (by rfl) ⟨2444075, by rfl⟩ : syracuseStep 3258767 = 4888151) B4888151
theorem B768487 : Blo 451781 768487 := bstep (se 1 (by rfl) ⟨576365, by rfl⟩ : syracuseStep 768487 = 1152731) B1152731
theorem B571951 : Blo 451781 571951 := bstep (se 1 (by rfl) ⟨428963, by rfl⟩ : syracuseStep 571951 = 857927) B857927
theorem B6961859 : Blo 451781 6961859 := bstep (se 1 (by rfl) ⟨5221394, by rfl⟩ : syracuseStep 6961859 = 10442789) B10442789
theorem B62798611 : Blo 451781 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B5815097 : Blo 451781 5815097 := bstep (se 2 (by rfl) ⟨2180661, by rfl⟩ : syracuseStep 5815097 = 4361323) B4361323
theorem B3455945 : Blo 451781 3455945 := bstep (se 2 (by rfl) ⟨1295979, by rfl⟩ : syracuseStep 3455945 = 2591959) B2591959
theorem B769007 : Blo 451781 769007 := bstep (se 1 (by rfl) ⟨576755, by rfl⟩ : syracuseStep 769007 = 1153511) B1153511
theorem B8731871 : Blo 451781 8731871 := bstep (se 1 (by rfl) ⟨6548903, by rfl⟩ : syracuseStep 8731871 = 13097807) B13097807
theorem B1720061 : Blo 451781 1720061 := bstep (se 3 (by rfl) ⟨322511, by rfl⟩ : syracuseStep 1720061 = 645023) B645023
theorem B573799 : Blo 451781 573799 := bstep (se 1 (by rfl) ⟨430349, by rfl⟩ : syracuseStep 573799 = 860699) B860699
theorem B8307143 : Blo 451781 8307143 := bstep (se 1 (by rfl) ⟨6230357, by rfl⟩ : syracuseStep 8307143 = 12460715) B12460715
theorem B1294841 : Blo 451781 1294841 := bstep (se 2 (by rfl) ⟨485565, by rfl⟩ : syracuseStep 1294841 = 971131) B971131
theorem B509287 : Blo 451781 509287 := bstep (se 1 (by rfl) ⟨381965, by rfl⟩ : syracuseStep 509287 = 763931) B763931
theorem B2574281 : Blo 451781 2574281 := bstep (se 2 (by rfl) ⟨965355, by rfl⟩ : syracuseStep 2574281 = 1930711) B1930711
theorem B575515 : Blo 451781 575515 := bstep (se 1 (by rfl) ⟨431636, by rfl⟩ : syracuseStep 575515 = 863273) B863273
theorem B2443385 : Blo 451781 2443385 := bstep (se 2 (by rfl) ⟨916269, by rfl⟩ : syracuseStep 2443385 = 1832539) B1832539
theorem B1296607 : Blo 451781 1296607 := bstep (se 1 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 1296607 = 1944911) B1944911
theorem B67095215 : Blo 451781 67095215 := bstep (se 1 (by rfl) ⟨50321411, by rfl⟩ : syracuseStep 67095215 = 100642823) B100642823
theorem B3459833 : Blo 451781 3459833 := bstep (se 2 (by rfl) ⟨1297437, by rfl⟩ : syracuseStep 3459833 = 2594875) B2594875
theorem B8276779 : Blo 451781 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B1526687 : Blo 451781 1526687 := bstep (se 1 (by rfl) ⟨1145015, by rfl⟩ : syracuseStep 1526687 = 2290031) B2290031
theorem B5229989 : Blo 451781 5229989 := bstep (se 4 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 5229989 = 980623) B980623
theorem B1724921 : Blo 451781 1724921 := bstep (se 2 (by rfl) ⟨646845, by rfl⟩ : syracuseStep 1724921 = 1293691) B1293691
theorem B512743 : Blo 451781 512743 := bstep (se 1 (by rfl) ⟨384557, by rfl⟩ : syracuseStep 512743 = 769115) B769115
theorem B4183979 : Blo 451781 4183979 := bstep (se 1 (by rfl) ⟨3137984, by rfl⟩ : syracuseStep 4183979 = 6275969) B6275969
theorem B1529981 : Blo 451781 1529981 := bstep (se 3 (by rfl) ⟨286871, by rfl⟩ : syracuseStep 1529981 = 573743) B573743
theorem B4905107 : Blo 451781 4905107 := bstep (se 1 (by rfl) ⟨3678830, by rfl⟩ : syracuseStep 4905107 = 7357661) B7357661
theorem B678119 : Blo 451781 678119 := bstep (se 1 (by rfl) ⟨508589, by rfl⟩ : syracuseStep 678119 = 1017179) B1017179
theorem B1530143 : Blo 451781 1530143 := bstep (se 1 (by rfl) ⟨1147607, by rfl⟩ : syracuseStep 1530143 = 2295215) B2295215
theorem B678299 : Blo 451781 678299 := bstep (se 1 (by rfl) ⟨508724, by rfl⟩ : syracuseStep 678299 = 1017449) B1017449
theorem B645575 : Blo 451781 645575 := bstep (se 1 (by rfl) ⟨484181, by rfl⟩ : syracuseStep 645575 = 968363) B968363
theorem B3889853 : Blo 451781 3889853 := bstep (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) B1458695
theorem B678695 : Blo 451781 678695 := bstep (se 1 (by rfl) ⟨509021, by rfl⟩ : syracuseStep 678695 = 1018043) B1018043
theorem B678719 : Blo 451781 678719 := bstep (se 1 (by rfl) ⟨509039, by rfl⟩ : syracuseStep 678719 = 1018079) B1018079
theorem B679019 : Blo 451781 679019 := bstep (se 1 (by rfl) ⟨509264, by rfl⟩ : syracuseStep 679019 = 1018529) B1018529
theorem B679163 : Blo 451781 679163 := bstep (se 1 (by rfl) ⟨509372, by rfl⟩ : syracuseStep 679163 = 1018745) B1018745
theorem B1957193 : Blo 451781 1957193 := bstep (se 2 (by rfl) ⟨733947, by rfl⟩ : syracuseStep 1957193 = 1467895) B1467895
theorem B679259 : Blo 451781 679259 := bstep (se 1 (by rfl) ⟨509444, by rfl⟩ : syracuseStep 679259 = 1018889) B1018889
theorem B679289 : Blo 451781 679289 := bstep (se 2 (by rfl) ⟨254733, by rfl⟩ : syracuseStep 679289 = 509467) B509467
theorem B679295 : Blo 451781 679295 := bstep (se 1 (by rfl) ⟨509471, by rfl⟩ : syracuseStep 679295 = 1018943) B1018943
theorem B6544871 : Blo 451781 6544871 := bstep (se 1 (by rfl) ⟨4908653, by rfl⟩ : syracuseStep 6544871 = 9817307) B9817307
theorem B679847 : Blo 451781 679847 := bstep (se 1 (by rfl) ⟨509885, by rfl⟩ : syracuseStep 679847 = 1019771) B1019771
theorem B1400743 : Blo 451781 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B679919 : Blo 451781 679919 := bstep (se 1 (by rfl) ⟨509939, by rfl⟩ : syracuseStep 679919 = 1019879) B1019879
theorem B778223 : Blo 451781 778223 := bstep (se 1 (by rfl) ⟨583667, by rfl⟩ : syracuseStep 778223 = 1167335) B1167335
theorem B680039 : Blo 451781 680039 := bstep (se 1 (by rfl) ⟨510029, by rfl⟩ : syracuseStep 680039 = 1020059) B1020059
theorem B680171 : Blo 451781 680171 := bstep (se 1 (by rfl) ⟨510128, by rfl⟩ : syracuseStep 680171 = 1020257) B1020257
theorem B680231 : Blo 451781 680231 := bstep (se 1 (by rfl) ⟨510173, by rfl⟩ : syracuseStep 680231 = 1020347) B1020347
theorem B2187719 : Blo 451781 2187719 := bstep (se 1 (by rfl) ⟨1640789, by rfl⟩ : syracuseStep 2187719 = 3281579) B3281579
theorem B680681 : Blo 451781 680681 := bstep (se 2 (by rfl) ⟨255255, by rfl⟩ : syracuseStep 680681 = 510511) B510511
theorem B681071 : Blo 451781 681071 := bstep (se 1 (by rfl) ⟨510803, by rfl⟩ : syracuseStep 681071 = 1021607) B1021607
theorem B4908221 : Blo 451781 4908221 := bstep (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) B1840583
theorem B451815 : Blo 451781 451815 := bstep (se 1 (by rfl) ⟨338861, by rfl⟩ : syracuseStep 451815 = 677723) B677723
theorem B681191 : Blo 451781 681191 := bstep (se 1 (by rfl) ⟨510893, by rfl⟩ : syracuseStep 681191 = 1021787) B1021787
theorem B143123705 : Blo 451781 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B681257 : Blo 451781 681257 := bstep (se 2 (by rfl) ⟨255471, by rfl⟩ : syracuseStep 681257 = 510943) B510943
theorem B452071 : Blo 451781 452071 := bstep (se 1 (by rfl) ⟨339053, by rfl⟩ : syracuseStep 452071 = 678107) B678107
theorem B681527 : Blo 451781 681527 := bstep (se 1 (by rfl) ⟨511145, by rfl⟩ : syracuseStep 681527 = 1022291) B1022291
theorem B452251 : Blo 451781 452251 := bstep (se 1 (by rfl) ⟨339188, by rfl⟩ : syracuseStep 452251 = 678377) B678377
theorem B2942647 : Blo 451781 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B2189119 : Blo 451781 2189119 := bstep (se 1 (by rfl) ⟨1641839, by rfl⟩ : syracuseStep 2189119 = 3283679) B3283679
theorem B2287439 : Blo 451781 2287439 := bstep (se 1 (by rfl) ⟨1715579, by rfl⟩ : syracuseStep 2287439 = 3431159) B3431159
theorem B2320211 : Blo 451781 2320211 := bstep (se 1 (by rfl) ⟨1740158, by rfl⟩ : syracuseStep 2320211 = 3480317) B3480317
theorem B681851 : Blo 451781 681851 := bstep (se 1 (by rfl) ⟨511388, by rfl⟩ : syracuseStep 681851 = 1022777) B1022777
theorem B452511 : Blo 451781 452511 := bstep (se 1 (by rfl) ⟨339383, by rfl⟩ : syracuseStep 452511 = 678767) B678767
theorem B681887 : Blo 451781 681887 := bstep (se 1 (by rfl) ⟨511415, by rfl⟩ : syracuseStep 681887 = 1022831) B1022831
theorem B452519 : Blo 451781 452519 := bstep (se 1 (by rfl) ⟨339389, by rfl⟩ : syracuseStep 452519 = 678779) B678779
theorem B682121 : Blo 451781 682121 := bstep (se 2 (by rfl) ⟨255795, by rfl⟩ : syracuseStep 682121 = 511591) B511591
theorem B4974803 : Blo 451781 4974803 := bstep (se 1 (by rfl) ⟨3731102, by rfl⟩ : syracuseStep 4974803 = 7462205) B7462205
theorem B682271 : Blo 451781 682271 := bstep (se 1 (by rfl) ⟨511703, by rfl⟩ : syracuseStep 682271 = 1023407) B1023407
theorem B682319 : Blo 451781 682319 := bstep (se 1 (by rfl) ⟨511739, by rfl⟩ : syracuseStep 682319 = 1023479) B1023479
theorem B682409 : Blo 451781 682409 := bstep (se 2 (by rfl) ⟨255903, by rfl⟩ : syracuseStep 682409 = 511807) B511807
theorem B453095 : Blo 451781 453095 := bstep (se 1 (by rfl) ⟨339821, by rfl⟩ : syracuseStep 453095 = 679643) B679643
theorem B4418023 : Blo 451781 4418023 := bstep (se 1 (by rfl) ⟨3313517, by rfl⟩ : syracuseStep 4418023 = 6627035) B6627035
theorem B453275 : Blo 451781 453275 := bstep (se 1 (by rfl) ⟨339956, by rfl⟩ : syracuseStep 453275 = 679913) B679913
theorem B2583211 : Blo 451781 2583211 := bstep (se 1 (by rfl) ⟨1937408, by rfl⟩ : syracuseStep 2583211 = 3874817) B3874817
theorem B682793 : Blo 451781 682793 := bstep (se 2 (by rfl) ⟨256047, by rfl⟩ : syracuseStep 682793 = 512095) B512095
theorem B683003 : Blo 451781 683003 := bstep (se 1 (by rfl) ⟨512252, by rfl⟩ : syracuseStep 683003 = 1024505) B1024505
theorem B683063 : Blo 451781 683063 := bstep (se 1 (by rfl) ⟨512297, by rfl⟩ : syracuseStep 683063 = 1024595) B1024595
theorem B453743 : Blo 451781 453743 := bstep (se 1 (by rfl) ⟨340307, by rfl⟩ : syracuseStep 453743 = 680615) B680615
theorem B683183 : Blo 451781 683183 := bstep (se 1 (by rfl) ⟨512387, by rfl⟩ : syracuseStep 683183 = 1024775) B1024775
theorem B453823 : Blo 451781 453823 := bstep (se 1 (by rfl) ⟨340367, by rfl⟩ : syracuseStep 453823 = 680735) B680735
theorem B453839 : Blo 451781 453839 := bstep (se 1 (by rfl) ⟨340379, by rfl⟩ : syracuseStep 453839 = 680759) B680759
theorem B683243 : Blo 451781 683243 := bstep (se 1 (by rfl) ⟨512432, by rfl⟩ : syracuseStep 683243 = 1024865) B1024865
theorem B453959 : Blo 451781 453959 := bstep (se 1 (by rfl) ⟨340469, by rfl⟩ : syracuseStep 453959 = 680939) B680939
theorem B2289545 : Blo 451781 2289545 := bstep (se 2 (by rfl) ⟨858579, by rfl⟩ : syracuseStep 2289545 = 1717159) B1717159
theorem B454687 : Blo 451781 454687 := bstep (se 1 (by rfl) ⟨341015, by rfl⟩ : syracuseStep 454687 = 682031) B682031
theorem B1044535 : Blo 451781 1044535 := bstep (se 1 (by rfl) ⟨783401, by rfl⟩ : syracuseStep 1044535 = 1566803) B1566803
theorem B454863 : Blo 451781 454863 := bstep (se 1 (by rfl) ⟨341147, by rfl⟩ : syracuseStep 454863 = 682295) B682295
theorem B454983 : Blo 451781 454983 := bstep (se 1 (by rfl) ⟨341237, by rfl⟩ : syracuseStep 454983 = 682475) B682475
theorem B2584943 : Blo 451781 2584943 := bstep (se 1 (by rfl) ⟨1938707, by rfl⟩ : syracuseStep 2584943 = 3877415) B3877415
theorem B455451 : Blo 451781 455451 := bstep (se 1 (by rfl) ⟨341588, by rfl⟩ : syracuseStep 455451 = 683177) B683177
theorem B455727 : Blo 451781 455727 := bstep (se 1 (by rfl) ⟨341795, by rfl⟩ : syracuseStep 455727 = 683591) B683591
theorem B2553065 : Blo 451781 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B3110147 : Blo 451781 3110147 := bstep (se 1 (by rfl) ⟨2332610, by rfl⟩ : syracuseStep 3110147 = 4665221) B4665221
theorem B13104503 : Blo 451781 13104503 := bstep (se 1 (by rfl) ⟨9828377, by rfl⟩ : syracuseStep 13104503 = 19656755) B19656755
theorem B5502629 : Blo 451781 5502629 := bstep (se 4 (by rfl) ⟨515871, by rfl⟩ : syracuseStep 5502629 = 1031743) B1031743
theorem B1144601 : Blo 451781 1144601 := bstep (se 2 (by rfl) ⟨429225, by rfl⟩ : syracuseStep 1144601 = 858451) B858451
theorem B7469111 : Blo 451781 7469111 := bstep (se 1 (by rfl) ⟨5601833, by rfl⟩ : syracuseStep 7469111 = 11203667) B11203667
theorem B1145249 : Blo 451781 1145249 := bstep (se 2 (by rfl) ⟨429468, by rfl⟩ : syracuseStep 1145249 = 858937) B858937
theorem B5175899 : Blo 451781 5175899 := bstep (se 1 (by rfl) ⟨3881924, by rfl⟩ : syracuseStep 5175899 = 7763849) B7763849
theorem B2325217 : Blo 451781 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B1145947 : Blo 451781 1145947 := bstep (se 1 (by rfl) ⟨859460, by rfl⟩ : syracuseStep 1145947 = 1718921) B1718921
theorem B818671 : Blo 451781 818671 := bstep (se 1 (by rfl) ⟨614003, by rfl⟩ : syracuseStep 818671 = 1228007) B1228007
theorem B2293595 : Blo 451781 2293595 := bstep (se 1 (by rfl) ⟨1720196, by rfl⟩ : syracuseStep 2293595 = 3440393) B3440393
theorem B5538095 : Blo 451781 5538095 := bstep (se 1 (by rfl) ⟨4153571, by rfl⟩ : syracuseStep 5538095 = 8307143) B8307143
theorem B1048955 : Blo 451781 1048955 := bstep (se 1 (by rfl) ⟨786716, by rfl⟩ : syracuseStep 1048955 = 1573433) B1573433
theorem B1147385 : Blo 451781 1147385 := bstep (se 2 (by rfl) ⟨430269, by rfl⟩ : syracuseStep 1147385 = 860539) B860539
theorem B3867983 : Blo 451781 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B44730143 : Blo 451781 44730143 := bstep (se 1 (by rfl) ⟨33547607, by rfl⟩ : syracuseStep 44730143 = 67095215) B67095215
theorem B1017791 : Blo 451781 1017791 := bstep (se 1 (by rfl) ⟨763343, by rfl⟩ : syracuseStep 1017791 = 1526687) B1526687
theorem B1837019 : Blo 451781 1837019 := bstep (se 1 (by rfl) ⟨1377764, by rfl⟩ : syracuseStep 1837019 = 2755529) B2755529
theorem B2918825 : Blo 451781 2918825 := bstep (se 2 (by rfl) ⟨1094559, by rfl⟩ : syracuseStep 2918825 = 2189119) B2189119
theorem B1149947 : Blo 451781 1149947 := bstep (se 1 (by rfl) ⟨862460, by rfl⟩ : syracuseStep 1149947 = 1724921) B1724921
theorem B3444281 : Blo 451781 3444281 := bstep (se 2 (by rfl) ⟨1291605, by rfl⟩ : syracuseStep 3444281 = 2583211) B2583211
theorem B1969939 : Blo 451781 1969939 := bstep (se 1 (by rfl) ⟨1477454, by rfl⟩ : syracuseStep 1969939 = 2954909) B2954909
theorem B1019987 : Blo 451781 1019987 := bstep (se 1 (by rfl) ⟨764990, by rfl⟩ : syracuseStep 1019987 = 1529981) B1529981
theorem B1020095 : Blo 451781 1020095 := bstep (se 1 (by rfl) ⟨765071, by rfl⟩ : syracuseStep 1020095 = 1530143) B1530143
theorem B2593235 : Blo 451781 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B2364191 : Blo 451781 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B14914529 : Blo 451781 14914529 := bstep (se 2 (by rfl) ⟨5592948, by rfl⟩ : syracuseStep 14914529 = 11185897) B11185897
theorem B4363247 : Blo 451781 4363247 := bstep (se 1 (by rfl) ⟨3272435, by rfl⟩ : syracuseStep 4363247 = 6544871) B6544871
theorem B923243 : Blo 451781 923243 := bstep (se 1 (by rfl) ⟨692432, by rfl⟩ : syracuseStep 923243 = 1384865) B1384865
theorem B2627603 : Blo 451781 2627603 := bstep (se 1 (by rfl) ⟨1970702, by rfl⟩ : syracuseStep 2627603 = 3941405) B3941405
theorem B1022345 : Blo 451781 1022345 := bstep (se 2 (by rfl) ⟨383379, by rfl⟩ : syracuseStep 1022345 = 766759) B766759
theorem B858671 : Blo 451781 858671 := bstep (se 1 (by rfl) ⟨644003, by rfl⟩ : syracuseStep 858671 = 1288007) B1288007
theorem B3316535 : Blo 451781 3316535 := bstep (se 1 (by rfl) ⟨2487401, by rfl⟩ : syracuseStep 3316535 = 4974803) B4974803
theorem B6528377 : Blo 451781 6528377 := bstep (se 2 (by rfl) ⟨2448141, by rfl⟩ : syracuseStep 6528377 = 4896283) B4896283
theorem B1023353 : Blo 451781 1023353 := bstep (se 2 (by rfl) ⟨383757, by rfl⟩ : syracuseStep 1023353 = 767515) B767515
theorem B859871 : Blo 451781 859871 := bstep (se 1 (by rfl) ⟨644903, by rfl⟩ : syracuseStep 859871 = 1289807) B1289807
theorem B1024649 : Blo 451781 1024649 := bstep (se 2 (by rfl) ⟨384243, by rfl⟩ : syracuseStep 1024649 = 768487) B768487
theorem B762601 : Blo 451781 762601 := bstep (se 2 (by rfl) ⟨285975, by rfl⟩ : syracuseStep 762601 = 571951) B571951
theorem B2073431 : Blo 451781 2073431 := bstep (se 1 (by rfl) ⟨1555073, by rfl⟩ : syracuseStep 2073431 = 3110147) B3110147
theorem B83731481 : Blo 451781 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B861367 : Blo 451781 861367 := bstep (se 1 (by rfl) ⟨646025, by rfl⟩ : syracuseStep 861367 = 1292051) B1292051
theorem B763067 : Blo 451781 763067 := bstep (se 1 (by rfl) ⟨572300, by rfl⟩ : syracuseStep 763067 = 1144601) B1144601
theorem B1844477 : Blo 451781 1844477 := bstep (se 3 (by rfl) ⟨345839, by rfl⟩ : syracuseStep 1844477 = 691679) B691679
theorem B2762041 : Blo 451781 2762041 := bstep (se 2 (by rfl) ⟨1035765, by rfl⟩ : syracuseStep 2762041 = 2071531) B2071531
theorem B3679607 : Blo 451781 3679607 := bstep (se 1 (by rfl) ⟨2759705, by rfl⟩ : syracuseStep 3679607 = 5519411) B5519411
theorem B2172511 : Blo 451781 2172511 := bstep (se 1 (by rfl) ⟨1629383, by rfl⟩ : syracuseStep 2172511 = 3258767) B3258767
theorem B763499 : Blo 451781 763499 := bstep (se 1 (by rfl) ⟨572624, by rfl⟩ : syracuseStep 763499 = 1145249) B1145249
theorem B3450599 : Blo 451781 3450599 := bstep (se 1 (by rfl) ⟨2587949, by rfl⟩ : syracuseStep 3450599 = 5175899) B5175899
theorem B3876731 : Blo 451781 3876731 := bstep (se 1 (by rfl) ⟨2907548, by rfl⟩ : syracuseStep 3876731 = 5815097) B5815097
theorem B2303963 : Blo 451781 2303963 := bstep (se 1 (by rfl) ⟨1727972, by rfl⟩ : syracuseStep 2303963 = 3455945) B3455945
theorem B1091561 : Blo 451781 1091561 := bstep (se 2 (by rfl) ⟨409335, by rfl⟩ : syracuseStep 1091561 = 818671) B818671
theorem B1092475 : Blo 451781 1092475 := bstep (se 1 (by rfl) ⟨819356, by rfl⟩ : syracuseStep 1092475 = 1638713) B1638713
theorem B863227 : Blo 451781 863227 := bstep (se 1 (by rfl) ⟨647420, by rfl⟩ : syracuseStep 863227 = 1294841) B1294841
theorem B765065 : Blo 451781 765065 := bstep (se 2 (by rfl) ⟨286899, by rfl⟩ : syracuseStep 765065 = 573799) B573799
theorem B765119 : Blo 451781 765119 := bstep (se 1 (by rfl) ⟨573839, by rfl⟩ : syracuseStep 765119 = 1147679) B1147679
theorem B765355 : Blo 451781 765355 := bstep (se 1 (by rfl) ⟨574016, by rfl⟩ : syracuseStep 765355 = 1148033) B1148033
theorem B1945063 : Blo 451781 1945063 := bstep (se 1 (by rfl) ⟨1458797, by rfl⟩ : syracuseStep 1945063 = 2917595) B2917595
theorem B765895 : Blo 451781 765895 := bstep (se 1 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 765895 = 1148843) B1148843
theorem B1716187 : Blo 451781 1716187 := bstep (se 1 (by rfl) ⟨1287140, by rfl⟩ : syracuseStep 1716187 = 2574281) B2574281
theorem B1225057 : Blo 451781 1225057 := bstep (se 2 (by rfl) ⟨459396, by rfl⟩ : syracuseStep 1225057 = 918793) B918793
theorem B2306555 : Blo 451781 2306555 := bstep (se 1 (by rfl) ⟨1729916, by rfl⟩ : syracuseStep 2306555 = 3459833) B3459833
theorem B2798135 : Blo 451781 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B3486659 : Blo 451781 3486659 := bstep (se 1 (by rfl) ⟨2614994, by rfl⟩ : syracuseStep 3486659 = 5229989) B5229989
theorem B1717433 : Blo 451781 1717433 := bstep (se 2 (by rfl) ⟨644037, by rfl⟩ : syracuseStep 1717433 = 1288075) B1288075
theorem B767353 : Blo 451781 767353 := bstep (se 2 (by rfl) ⟨287757, by rfl⟩ : syracuseStep 767353 = 575515) B575515
theorem B1292267 : Blo 451781 1292267 := bstep (se 1 (by rfl) ⟨969200, by rfl⟩ : syracuseStep 1292267 = 1938401) B1938401
theorem B768055 : Blo 451781 768055 := bstep (se 1 (by rfl) ⟨576041, by rfl⟩ : syracuseStep 768055 = 1152083) B1152083
theorem B572123 : Blo 451781 572123 := bstep (se 1 (by rfl) ⟨429092, by rfl⟩ : syracuseStep 572123 = 858185) B858185
theorem B3456431 : Blo 451781 3456431 := bstep (se 1 (by rfl) ⟨2592323, by rfl⟩ : syracuseStep 3456431 = 5184647) B5184647
theorem B573095 : Blo 451781 573095 := bstep (se 1 (by rfl) ⟨429821, by rfl⟩ : syracuseStep 573095 = 859643) B859643
theorem B7389161 : Blo 451781 7389161 := bstep (se 2 (by rfl) ⟨2770935, by rfl⟩ : syracuseStep 7389161 = 5541871) B5541871
theorem B966647 : Blo 451781 966647 := bstep (se 1 (by rfl) ⟨724985, by rfl⟩ : syracuseStep 966647 = 1449971) B1449971
theorem B1392713 : Blo 451781 1392713 := bstep (se 2 (by rfl) ⟨522267, by rfl⟩ : syracuseStep 1392713 = 1044535) B1044535
theorem B3326035 : Blo 451781 3326035 := bstep (se 1 (by rfl) ⟨2494526, by rfl⟩ : syracuseStep 3326035 = 4989053) B4989053
theorem B1458479 : Blo 451781 1458479 := bstep (se 1 (by rfl) ⟨1093859, by rfl⟩ : syracuseStep 1458479 = 2187719) B2187719
theorem B508315 : Blo 451781 508315 := bstep (se 1 (by rfl) ⟨381236, by rfl⟩ : syracuseStep 508315 = 762473) B762473
theorem B1295423 : Blo 451781 1295423 := bstep (se 1 (by rfl) ⟨971567, by rfl⟩ : syracuseStep 1295423 = 1943135) B1943135
theorem B1721533 : Blo 451781 1721533 := bstep (se 3 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 1721533 = 645575) B645575
theorem B1524959 : Blo 451781 1524959 := bstep (se 1 (by rfl) ⟨1143719, by rfl⟩ : syracuseStep 1524959 = 2287439) B2287439
theorem B5818787 : Blo 451781 5818787 := bstep (se 1 (by rfl) ⟨4364090, by rfl⟩ : syracuseStep 5818787 = 8728181) B8728181
theorem B4377007 : Blo 451781 4377007 := bstep (se 1 (by rfl) ⟨3282755, by rfl⟩ : syracuseStep 4377007 = 6565511) B6565511
theorem B1526363 : Blo 451781 1526363 := bstep (se 1 (by rfl) ⟨1144772, by rfl⟩ : syracuseStep 1526363 = 2289545) B2289545
theorem B4901735 : Blo 451781 4901735 := bstep (se 1 (by rfl) ⟨3676301, by rfl⟩ : syracuseStep 4901735 = 7352603) B7352603
theorem B1723295 : Blo 451781 1723295 := bstep (se 1 (by rfl) ⟨1292471, by rfl⟩ : syracuseStep 1723295 = 2584943) B2584943
theorem B969833 : Blo 451781 969833 := bstep (se 2 (by rfl) ⟨363687, by rfl⟩ : syracuseStep 969833 = 727375) B727375
theorem B970003 : Blo 451781 970003 := bstep (se 1 (by rfl) ⟨727502, by rfl⟩ : syracuseStep 970003 = 1455005) B1455005
theorem B511303 : Blo 451781 511303 := bstep (se 1 (by rfl) ⟨383477, by rfl⟩ : syracuseStep 511303 = 766955) B766955
theorem B8736335 : Blo 451781 8736335 := bstep (se 1 (by rfl) ⟨6552251, by rfl⟩ : syracuseStep 8736335 = 13104503) B13104503
theorem B3100289 : Blo 451781 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B1527929 : Blo 451781 1527929 := bstep (se 2 (by rfl) ⟨572973, by rfl⟩ : syracuseStep 1527929 = 1145947) B1145947
theorem B4641239 : Blo 451781 4641239 := bstep (se 1 (by rfl) ⟨3480929, by rfl⟩ : syracuseStep 4641239 = 6961859) B6961859
theorem B512671 : Blo 451781 512671 := bstep (se 1 (by rfl) ⟨384503, by rfl⟩ : syracuseStep 512671 = 769007) B769007
theorem B5821247 : Blo 451781 5821247 := bstep (se 1 (by rfl) ⟨4365935, by rfl⟩ : syracuseStep 5821247 = 8731871) B8731871
theorem B4379777 : Blo 451781 4379777 := bstep (se 2 (by rfl) ⟨1642416, by rfl⟩ : syracuseStep 4379777 = 3284833) B3284833
theorem B1529063 : Blo 451781 1529063 := bstep (se 1 (by rfl) ⟨1146797, by rfl⟩ : syracuseStep 1529063 = 2293595) B2293595
theorem B972361 : Blo 451781 972361 := bstep (se 2 (by rfl) ⟨364635, by rfl⟩ : syracuseStep 972361 = 729271) B729271
theorem B677855 : Blo 451781 677855 := bstep (se 1 (by rfl) ⟨508391, by rfl⟩ : syracuseStep 677855 = 1016783) B1016783
theorem B677915 : Blo 451781 677915 := bstep (se 1 (by rfl) ⟨508436, by rfl⟩ : syracuseStep 677915 = 1016873) B1016873
theorem B1529927 : Blo 451781 1529927 := bstep (se 1 (by rfl) ⟨1147445, by rfl⟩ : syracuseStep 1529927 = 2294891) B2294891
theorem B678503 : Blo 451781 678503 := bstep (se 1 (by rfl) ⟨508877, by rfl⟩ : syracuseStep 678503 = 1017755) B1017755
theorem B678635 : Blo 451781 678635 := bstep (se 1 (by rfl) ⟨508976, by rfl⟩ : syracuseStep 678635 = 1017953) B1017953
theorem B1628923 : Blo 451781 1628923 := bstep (se 1 (by rfl) ⟨1221692, by rfl⟩ : syracuseStep 1628923 = 2443385) B2443385
theorem B679007 : Blo 451781 679007 := bstep (se 1 (by rfl) ⟨509255, by rfl⟩ : syracuseStep 679007 = 1018511) B1018511
theorem B679049 : Blo 451781 679049 := bstep (se 2 (by rfl) ⟨254643, by rfl⟩ : syracuseStep 679049 = 509287) B509287
theorem B679067 : Blo 451781 679067 := bstep (se 1 (by rfl) ⟨509300, by rfl⟩ : syracuseStep 679067 = 1018601) B1018601
theorem B679103 : Blo 451781 679103 := bstep (se 1 (by rfl) ⟨509327, by rfl⟩ : syracuseStep 679103 = 1018655) B1018655
theorem B679535 : Blo 451781 679535 := bstep (se 1 (by rfl) ⟨509651, by rfl⟩ : syracuseStep 679535 = 1019303) B1019303
theorem B679655 : Blo 451781 679655 := bstep (se 1 (by rfl) ⟨509741, by rfl⟩ : syracuseStep 679655 = 1019483) B1019483
theorem B1531871 : Blo 451781 1531871 := bstep (se 1 (by rfl) ⟨1148903, by rfl⟩ : syracuseStep 1531871 = 2297807) B2297807
theorem B1532033 : Blo 451781 1532033 := bstep (se 2 (by rfl) ⟨574512, by rfl⟩ : syracuseStep 1532033 = 1149025) B1149025
theorem B1728809 : Blo 451781 1728809 := bstep (se 2 (by rfl) ⟨648303, by rfl⟩ : syracuseStep 1728809 = 1296607) B1296607
theorem B3891563 : Blo 451781 3891563 := bstep (se 1 (by rfl) ⟨2918672, by rfl⟩ : syracuseStep 3891563 = 5837345) B5837345
theorem B5890697 : Blo 451781 5890697 := bstep (se 2 (by rfl) ⟨2209011, by rfl⟩ : syracuseStep 5890697 = 4418023) B4418023
theorem B1532897 : Blo 451781 1532897 := bstep (se 2 (by rfl) ⟨574836, by rfl⟩ : syracuseStep 1532897 = 1149673) B1149673
theorem B11035705 : Blo 451781 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B1533113 : Blo 451781 1533113 := bstep (se 2 (by rfl) ⟨574917, by rfl⟩ : syracuseStep 1533113 = 1149835) B1149835
theorem B3270071 : Blo 451781 3270071 := bstep (se 1 (by rfl) ⟨2452553, by rfl⟩ : syracuseStep 3270071 = 4905107) B4905107
theorem B452079 : Blo 451781 452079 := bstep (se 1 (by rfl) ⟨339059, by rfl⟩ : syracuseStep 452079 = 678119) B678119
theorem B452199 : Blo 451781 452199 := bstep (se 1 (by rfl) ⟨339149, by rfl⟩ : syracuseStep 452199 = 678299) B678299
theorem B1533707 : Blo 451781 1533707 := bstep (se 1 (by rfl) ⟨1150280, by rfl⟩ : syracuseStep 1533707 = 2300561) B2300561
theorem B452463 : Blo 451781 452463 := bstep (se 1 (by rfl) ⟨339347, by rfl⟩ : syracuseStep 452463 = 678695) B678695
theorem B452479 : Blo 451781 452479 := bstep (se 1 (by rfl) ⟨339359, by rfl⟩ : syracuseStep 452479 = 678719) B678719
theorem B452679 : Blo 451781 452679 := bstep (se 1 (by rfl) ⟨339509, by rfl⟩ : syracuseStep 452679 = 679019) B679019
theorem B452775 : Blo 451781 452775 := bstep (se 1 (by rfl) ⟨339581, by rfl⟩ : syracuseStep 452775 = 679163) B679163
theorem B1304795 : Blo 451781 1304795 := bstep (se 1 (by rfl) ⟨978596, by rfl⟩ : syracuseStep 1304795 = 1957193) B1957193
theorem B6187229 : Blo 451781 6187229 := bstep (se 3 (by rfl) ⟨1160105, by rfl⟩ : syracuseStep 6187229 = 2320211) B2320211
theorem B452839 : Blo 451781 452839 := bstep (se 1 (by rfl) ⟨339629, by rfl⟩ : syracuseStep 452839 = 679259) B679259
theorem B452859 : Blo 451781 452859 := bstep (se 1 (by rfl) ⟨339644, by rfl⟩ : syracuseStep 452859 = 679289) B679289
theorem B452863 : Blo 451781 452863 := bstep (se 1 (by rfl) ⟨339647, by rfl⟩ : syracuseStep 452863 = 679295) B679295
theorem B453231 : Blo 451781 453231 := bstep (se 1 (by rfl) ⟨339923, by rfl⟩ : syracuseStep 453231 = 679847) B679847
theorem B453279 : Blo 451781 453279 := bstep (se 1 (by rfl) ⟨339959, by rfl⟩ : syracuseStep 453279 = 679919) B679919
theorem B518815 : Blo 451781 518815 := bstep (se 1 (by rfl) ⟨389111, by rfl⟩ : syracuseStep 518815 = 778223) B778223
theorem B682703 : Blo 451781 682703 := bstep (se 1 (by rfl) ⟨512027, by rfl⟩ : syracuseStep 682703 = 1024055) B1024055
theorem B486095 : Blo 451781 486095 := bstep (se 1 (by rfl) ⟨364571, by rfl⟩ : syracuseStep 486095 = 729143) B729143
theorem B453359 : Blo 451781 453359 := bstep (se 1 (by rfl) ⟨340019, by rfl⟩ : syracuseStep 453359 = 680039) B680039
theorem B453447 : Blo 451781 453447 := bstep (se 1 (by rfl) ⟨340085, by rfl⟩ : syracuseStep 453447 = 680171) B680171
theorem B453487 : Blo 451781 453487 := bstep (se 1 (by rfl) ⟨340115, by rfl⟩ : syracuseStep 453487 = 680231) B680231
theorem B1534841 : Blo 451781 1534841 := bstep (se 2 (by rfl) ⟨575565, by rfl⟩ : syracuseStep 1534841 = 1151131) B1151131
theorem B1535003 : Blo 451781 1535003 := bstep (se 1 (by rfl) ⟨1151252, by rfl⟩ : syracuseStep 1535003 = 2302505) B2302505
theorem B453787 : Blo 451781 453787 := bstep (se 1 (by rfl) ⟨340340, by rfl⟩ : syracuseStep 453787 = 680681) B680681
theorem B454047 : Blo 451781 454047 := bstep (se 1 (by rfl) ⟨340535, by rfl⟩ : syracuseStep 454047 = 681071) B681071
theorem B3272147 : Blo 451781 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B454127 : Blo 451781 454127 := bstep (se 1 (by rfl) ⟨340595, by rfl⟩ : syracuseStep 454127 = 681191) B681191
theorem B95415803 : Blo 451781 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B454171 : Blo 451781 454171 := bstep (se 1 (by rfl) ⟨340628, by rfl⟩ : syracuseStep 454171 = 681257) B681257
theorem B683657 : Blo 451781 683657 := bstep (se 2 (by rfl) ⟨256371, by rfl⟩ : syracuseStep 683657 = 512743) B512743
theorem B454351 : Blo 451781 454351 := bstep (se 1 (by rfl) ⟨340763, by rfl⟩ : syracuseStep 454351 = 681527) B681527
theorem B1535867 : Blo 451781 1535867 := bstep (se 1 (by rfl) ⟨1151900, by rfl⟩ : syracuseStep 1535867 = 2303801) B2303801
theorem B454567 : Blo 451781 454567 := bstep (se 1 (by rfl) ⟨340925, by rfl⟩ : syracuseStep 454567 = 681851) B681851
theorem B454591 : Blo 451781 454591 := bstep (se 1 (by rfl) ⟨340943, by rfl⟩ : syracuseStep 454591 = 681887) B681887
theorem B454747 : Blo 451781 454747 := bstep (se 1 (by rfl) ⟨341060, by rfl⟩ : syracuseStep 454747 = 682121) B682121
theorem B454847 : Blo 451781 454847 := bstep (se 1 (by rfl) ⟨341135, by rfl⟩ : syracuseStep 454847 = 682271) B682271
theorem B13988051 : Blo 451781 13988051 := bstep (se 1 (by rfl) ⟨10491038, by rfl⟩ : syracuseStep 13988051 = 20982077) B20982077
theorem B454879 : Blo 451781 454879 := bstep (se 1 (by rfl) ⟨341159, by rfl⟩ : syracuseStep 454879 = 682319) B682319
theorem B454939 : Blo 451781 454939 := bstep (se 1 (by rfl) ⟨341204, by rfl⟩ : syracuseStep 454939 = 682409) B682409
theorem B455195 : Blo 451781 455195 := bstep (se 1 (by rfl) ⟨341396, by rfl⟩ : syracuseStep 455195 = 682793) B682793
theorem B455335 : Blo 451781 455335 := bstep (se 1 (by rfl) ⟨341501, by rfl⟩ : syracuseStep 455335 = 683003) B683003
theorem B455375 : Blo 451781 455375 := bstep (se 1 (by rfl) ⟨341531, by rfl⟩ : syracuseStep 455375 = 683063) B683063
theorem B455455 : Blo 451781 455455 := bstep (se 1 (by rfl) ⟨341591, by rfl⟩ : syracuseStep 455455 = 683183) B683183
theorem B455495 : Blo 451781 455495 := bstep (se 1 (by rfl) ⟨341621, by rfl⟩ : syracuseStep 455495 = 683243) B683243
theorem B18674657 : Blo 451781 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B1143791 : Blo 451781 1143791 := bstep (se 1 (by rfl) ⟨857843, by rfl⟩ : syracuseStep 1143791 = 1715687) B1715687
theorem B16741529 : Blo 451781 16741529 := bstep (se 2 (by rfl) ⟨6278073, by rfl⟩ : syracuseStep 16741529 = 12556147) B12556147
theorem B1930985 : Blo 451781 1930985 := bstep (se 2 (by rfl) ⟨724119, by rfl⟩ : syracuseStep 1930985 = 1448239) B1448239
theorem B1537811 : Blo 451781 1537811 := bstep (se 1 (by rfl) ⟨1153358, by rfl⟩ : syracuseStep 1537811 = 2306717) B2306717
theorem B1537919 : Blo 451781 1537919 := bstep (se 1 (by rfl) ⟨1153439, by rfl⟩ : syracuseStep 1537919 = 2306879) B2306879
theorem B1702043 : Blo 451781 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B15694117 : Blo 451781 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B817511 : Blo 451781 817511 := bstep (se 1 (by rfl) ⟨613133, by rfl⟩ : syracuseStep 817511 = 1226267) B1226267
theorem B3668419 : Blo 451781 3668419 := bstep (se 1 (by rfl) ⟨2751314, by rfl⟩ : syracuseStep 3668419 = 5502629) B5502629
theorem B4979407 : Blo 451781 4979407 := bstep (se 1 (by rfl) ⟨3734555, by rfl⟩ : syracuseStep 4979407 = 7469111) B7469111
theorem B44629109 : Blo 451781 44629109 := bstep (se 5 (by rfl) ⟨2091989, by rfl⟩ : syracuseStep 44629109 = 4183979) B4183979
theorem B1146707 : Blo 451781 1146707 := bstep (se 1 (by rfl) ⟨860030, by rfl⟩ : syracuseStep 1146707 = 1720061) B1720061
theorem B1867657 : Blo 451781 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B1016639 : Blo 451781 1016639 := bstep (se 1 (by rfl) ⟨762479, by rfl⟩ : syracuseStep 1016639 = 1524959) B1524959
theorem B1016801 : Blo 451781 1016801 := bstep (se 2 (by rfl) ⟨381300, by rfl⟩ : syracuseStep 1016801 = 762601) B762601
theorem B29820095 : Blo 451781 29820095 := bstep (se 1 (by rfl) ⟨22365071, by rfl⟩ : syracuseStep 29820095 = 44730143) B44730143
theorem B14714273 : Blo 451781 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B1148489 : Blo 451781 1148489 := bstep (se 2 (by rfl) ⟨430683, by rfl⟩ : syracuseStep 1148489 = 861367) B861367
theorem B2295377 : Blo 451781 2295377 := bstep (se 2 (by rfl) ⟨860766, by rfl⟩ : syracuseStep 2295377 = 1721533) B1721533
theorem B1017575 : Blo 451781 1017575 := bstep (se 1 (by rfl) ⟨763181, by rfl⟩ : syracuseStep 1017575 = 1526363) B1526363
theorem B1148863 : Blo 451781 1148863 := bstep (se 1 (by rfl) ⟨861647, by rfl⟩ : syracuseStep 1148863 = 1723295) B1723295
theorem B19564901 : Blo 451781 19564901 := bstep (se 4 (by rfl) ⟨1834209, by rfl⟩ : syracuseStep 19564901 = 3668419) B3668419
theorem B2296187 : Blo 451781 2296187 := bstep (se 1 (by rfl) ⟨1722140, by rfl⟩ : syracuseStep 2296187 = 3444281) B3444281
theorem B1018619 : Blo 451781 1018619 := bstep (se 1 (by rfl) ⟨763964, by rfl⟩ : syracuseStep 1018619 = 1527929) B1527929
theorem B1576127 : Blo 451781 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B5836009 : Blo 451781 5836009 := bstep (se 2 (by rfl) ⟨2188503, by rfl⟩ : syracuseStep 5836009 = 4377007) B4377007
theorem B2919851 : Blo 451781 2919851 := bstep (se 1 (by rfl) ⟨2189888, by rfl⟩ : syracuseStep 2919851 = 4379777) B4379777
theorem B1019375 : Blo 451781 1019375 := bstep (se 1 (by rfl) ⟨764531, by rfl⟩ : syracuseStep 1019375 = 1529063) B1529063
theorem B2428453 : Blo 451781 2428453 := bstep (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) B455335
theorem B691753 : Blo 451781 691753 := bstep (se 2 (by rfl) ⟨259407, by rfl⟩ : syracuseStep 691753 = 518815) B518815
theorem B1150969 : Blo 451781 1150969 := bstep (se 2 (by rfl) ⟨431613, by rfl⟩ : syracuseStep 1150969 = 863227) B863227
theorem B1019951 : Blo 451781 1019951 := bstep (se 1 (by rfl) ⟨764963, by rfl⟩ : syracuseStep 1019951 = 1529927) B1529927
theorem B1020473 : Blo 451781 1020473 := bstep (se 2 (by rfl) ⟨382677, by rfl⟩ : syracuseStep 1020473 = 765355) B765355
theorem B2593417 : Blo 451781 2593417 := bstep (se 2 (by rfl) ⟨972531, by rfl⟩ : syracuseStep 2593417 = 1945063) B1945063
theorem B1021193 : Blo 451781 1021193 := bstep (se 2 (by rfl) ⟨382947, by rfl⟩ : syracuseStep 1021193 = 765895) B765895
theorem B1021247 : Blo 451781 1021247 := bstep (se 1 (by rfl) ⟨765935, by rfl⟩ : syracuseStep 1021247 = 1531871) B1531871
theorem B1021355 : Blo 451781 1021355 := bstep (se 1 (by rfl) ⟨766016, by rfl⟩ : syracuseStep 1021355 = 1532033) B1532033
theorem B1152539 : Blo 451781 1152539 := bstep (se 1 (by rfl) ⟨864404, by rfl⟩ : syracuseStep 1152539 = 1728809) B1728809
theorem B2594375 : Blo 451781 2594375 := bstep (se 1 (by rfl) ⟨1945781, by rfl⟩ : syracuseStep 2594375 = 3891563) B3891563
theorem B1382287 : Blo 451781 1382287 := bstep (se 1 (by rfl) ⟨1036715, by rfl⟩ : syracuseStep 1382287 = 2073431) B2073431
theorem B1021931 : Blo 451781 1021931 := bstep (se 1 (by rfl) ⟨766448, by rfl⟩ : syracuseStep 1021931 = 1532897) B1532897
theorem B1022075 : Blo 451781 1022075 := bstep (se 1 (by rfl) ⟨766556, by rfl⟩ : syracuseStep 1022075 = 1533113) B1533113
theorem B2300399 : Blo 451781 2300399 := bstep (se 1 (by rfl) ⟨1725299, by rfl⟩ : syracuseStep 2300399 = 3450599) B3450599
theorem B1022471 : Blo 451781 1022471 := bstep (se 1 (by rfl) ⟨766853, by rfl⟩ : syracuseStep 1022471 = 1533707) B1533707
theorem B1023137 : Blo 451781 1023137 := bstep (se 2 (by rfl) ⟨383676, by rfl⟩ : syracuseStep 1023137 = 767353) B767353
theorem B1023227 : Blo 451781 1023227 := bstep (se 1 (by rfl) ⟨767420, by rfl⟩ : syracuseStep 1023227 = 1534841) B1534841
theorem B1023335 : Blo 451781 1023335 := bstep (se 1 (by rfl) ⟨767501, by rfl⟩ : syracuseStep 1023335 = 1535003) B1535003
theorem B63610535 : Blo 451781 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B1023911 : Blo 451781 1023911 := bstep (se 1 (by rfl) ⟨767933, by rfl⟩ : syracuseStep 1023911 = 1535867) B1535867
theorem B1024073 : Blo 451781 1024073 := bstep (se 2 (by rfl) ⟨384027, by rfl⟩ : syracuseStep 1024073 = 768055) B768055
theorem B762527 : Blo 451781 762527 := bstep (se 1 (by rfl) ⟨571895, by rfl⟩ : syracuseStep 762527 = 1143791) B1143791
theorem B2171897 : Blo 451781 2171897 := bstep (se 2 (by rfl) ⟨814461, by rfl⟩ : syracuseStep 2171897 = 1628923) B1628923
theorem B1287323 : Blo 451781 1287323 := bstep (se 1 (by rfl) ⟨965492, by rfl⟩ : syracuseStep 1287323 = 1930985) B1930985
theorem B1025207 : Blo 451781 1025207 := bstep (se 1 (by rfl) ⟨768905, by rfl⟩ : syracuseStep 1025207 = 1537811) B1537811
theorem B1025279 : Blo 451781 1025279 := bstep (se 1 (by rfl) ⟨768959, by rfl⟩ : syracuseStep 1025279 = 1537919) B1537919
theorem B861511 : Blo 451781 861511 := bstep (se 1 (by rfl) ⟨646133, by rfl⟩ : syracuseStep 861511 = 1292267) B1292267
theorem B8267437 : Blo 451781 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B2304287 : Blo 451781 2304287 := bstep (se 1 (by rfl) ⟨1728215, by rfl⟩ : syracuseStep 2304287 = 3456431) B3456431
theorem B764471 : Blo 451781 764471 := bstep (se 1 (by rfl) ⟨573353, by rfl⟩ : syracuseStep 764471 = 1146707) B1146707
theorem B4926107 : Blo 451781 4926107 := bstep (se 1 (by rfl) ⟨3694580, by rfl⟩ : syracuseStep 4926107 = 7389161) B7389161
theorem B928475 : Blo 451781 928475 := bstep (se 1 (by rfl) ⟨696356, by rfl⟩ : syracuseStep 928475 = 1392713) B1392713
theorem B4434713 : Blo 451781 4434713 := bstep (se 2 (by rfl) ⟨1663017, by rfl⟩ : syracuseStep 4434713 = 3326035) B3326035
theorem B764923 : Blo 451781 764923 := bstep (se 1 (by rfl) ⟨573692, by rfl⟩ : syracuseStep 764923 = 1147385) B1147385
theorem B863615 : Blo 451781 863615 := bstep (se 1 (by rfl) ⟨647711, by rfl⟩ : syracuseStep 863615 = 1295423) B1295423
theorem B1224679 : Blo 451781 1224679 := bstep (se 1 (by rfl) ⟨918509, by rfl⟩ : syracuseStep 1224679 = 1837019) B1837019
theorem B83701957 : Blo 451781 83701957 := bstep (se 4 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 83701957 = 15694117) B15694117
theorem B3879191 : Blo 451781 3879191 := bstep (se 1 (by rfl) ⟨2909393, by rfl⟩ : syracuseStep 3879191 = 5818787) B5818787
theorem B1945883 : Blo 451781 1945883 := bstep (se 1 (by rfl) ⟨1459412, by rfl⟩ : syracuseStep 1945883 = 2918825) B2918825
theorem B3682721 : Blo 451781 3682721 := bstep (se 2 (by rfl) ⟨1381020, by rfl⟩ : syracuseStep 3682721 = 2762041) B2762041
theorem B766631 : Blo 451781 766631 := bstep (se 1 (by rfl) ⟨574973, by rfl⟩ : syracuseStep 766631 = 1149947) B1149947
theorem B3880831 : Blo 451781 3880831 := bstep (se 1 (by rfl) ⟨2910623, by rfl⟩ : syracuseStep 3880831 = 5821247) B5821247
theorem B9943019 : Blo 451781 9943019 := bstep (se 1 (by rfl) ⟨7457264, by rfl⟩ : syracuseStep 9943019 = 14914529) B14914529
theorem B9812285 : Blo 451781 9812285 := bstep (se 3 (by rfl) ⟨1839803, by rfl⟩ : syracuseStep 9812285 = 3679607) B3679607
theorem B1456633 : Blo 451781 1456633 := bstep (se 2 (by rfl) ⟨546237, by rfl⟩ : syracuseStep 1456633 = 1092475) B1092475
theorem B11188853 : Blo 451781 11188853 := bstep (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) B1048955
theorem B1751735 : Blo 451781 1751735 := bstep (se 1 (by rfl) ⟨1313801, by rfl⟩ : syracuseStep 1751735 = 2627603) B2627603
theorem B1293337 : Blo 451781 1293337 := bstep (se 2 (by rfl) ⟨485001, by rfl⟩ : syracuseStep 1293337 = 970003) B970003
theorem B572447 : Blo 451781 572447 := bstep (se 1 (by rfl) ⟨429335, by rfl⟩ : syracuseStep 572447 = 858671) B858671
theorem B2211023 : Blo 451781 2211023 := bstep (se 1 (by rfl) ⟨1658267, by rfl⟩ : syracuseStep 2211023 = 3316535) B3316535
theorem B573247 : Blo 451781 573247 := bstep (se 1 (by rfl) ⟨429935, by rfl⟩ : syracuseStep 573247 = 859871) B859871
theorem B55820987 : Blo 451781 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B508711 : Blo 451781 508711 := bstep (se 1 (by rfl) ⟨381533, by rfl⟩ : syracuseStep 508711 = 763067) B763067
theorem B1229651 : Blo 451781 1229651 := bstep (se 1 (by rfl) ⟨922238, by rfl⟩ : syracuseStep 1229651 = 1844477) B1844477
theorem B2180029 : Blo 451781 2180029 := bstep (se 3 (by rfl) ⟨408755, by rfl⟩ : syracuseStep 2180029 = 817511) B817511
theorem B2180047 : Blo 451781 2180047 := bstep (se 1 (by rfl) ⟨1635035, by rfl⟩ : syracuseStep 2180047 = 3270071) B3270071
theorem B508999 : Blo 451781 508999 := bstep (se 1 (by rfl) ⟨381749, by rfl⟩ : syracuseStep 508999 = 763499) B763499
theorem B9847925 : Blo 451781 9847925 := bstep (se 5 (by rfl) ⟨461621, by rfl⟩ : syracuseStep 9847925 = 923243) B923243
theorem B869863 : Blo 451781 869863 := bstep (se 1 (by rfl) ⟨652397, by rfl⟩ : syracuseStep 869863 = 1304795) B1304795
theorem B1296253 : Blo 451781 1296253 := bstep (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) B486095
theorem B1525661 : Blo 451781 1525661 := bstep (se 3 (by rfl) ⟨286061, by rfl⟩ : syracuseStep 1525661 = 572123) B572123
theorem B510043 : Blo 451781 510043 := bstep (se 1 (by rfl) ⟨382532, by rfl⟩ : syracuseStep 510043 = 765065) B765065
theorem B1296481 : Blo 451781 1296481 := bstep (se 2 (by rfl) ⟨486180, by rfl⟩ : syracuseStep 1296481 = 972361) B972361
theorem B510079 : Blo 451781 510079 := bstep (se 1 (by rfl) ⟨382559, by rfl⟩ : syracuseStep 510079 = 765119) B765119
theorem B2181431 : Blo 451781 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B9325367 : Blo 451781 9325367 := bstep (se 1 (by rfl) ⟨6994025, by rfl⟩ : syracuseStep 9325367 = 13988051) B13988051
theorem B11586725 : Blo 451781 11586725 := bstep (se 4 (by rfl) ⟨1086255, by rfl⟩ : syracuseStep 11586725 = 2172511) B2172511
theorem B11161019 : Blo 451781 11161019 := bstep (se 1 (by rfl) ⟨8370764, by rfl⟩ : syracuseStep 11161019 = 16741529) B16741529
theorem B6639209 : Blo 451781 6639209 := bstep (se 2 (by rfl) ⟨2489703, by rfl⟩ : syracuseStep 6639209 = 4979407) B4979407
theorem B10506341 : Blo 451781 10506341 := bstep (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) B1969939
theorem B1134695 : Blo 451781 1134695 := bstep (se 1 (by rfl) ⟨851021, by rfl⟩ : syracuseStep 1134695 = 1702043) B1702043
theorem B1528253 : Blo 451781 1528253 := bstep (se 3 (by rfl) ⟨286547, by rfl⟩ : syracuseStep 1528253 = 573095) B573095
theorem B644431 : Blo 451781 644431 := bstep (se 1 (by rfl) ⟨483323, by rfl⟩ : syracuseStep 644431 = 966647) B966647
theorem B972319 : Blo 451781 972319 := bstep (se 1 (by rfl) ⟨729239, by rfl⟩ : syracuseStep 972319 = 1458479) B1458479
theorem B3692063 : Blo 451781 3692063 := bstep (se 1 (by rfl) ⟨2769047, by rfl⟩ : syracuseStep 3692063 = 5538095) B5538095
theorem B677753 : Blo 451781 677753 := bstep (se 2 (by rfl) ⟨254157, by rfl⟩ : syracuseStep 677753 = 508315) B508315
theorem B2578655 : Blo 451781 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B12376637 : Blo 451781 12376637 := bstep (se 3 (by rfl) ⟨2320619, by rfl⟩ : syracuseStep 12376637 = 4641239) B4641239
theorem B678527 : Blo 451781 678527 := bstep (se 1 (by rfl) ⟨508895, by rfl⟩ : syracuseStep 678527 = 1017791) B1017791
theorem B3267823 : Blo 451781 3267823 := bstep (se 1 (by rfl) ⟨2450867, by rfl⟩ : syracuseStep 3267823 = 4901735) B4901735
theorem B646555 : Blo 451781 646555 := bstep (se 1 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 646555 = 969833) B969833
theorem B5824223 : Blo 451781 5824223 := bstep (se 1 (by rfl) ⟨4368167, by rfl⟩ : syracuseStep 5824223 = 8736335) B8736335
theorem B9297757 : Blo 451781 9297757 := bstep (se 3 (by rfl) ⟨1743329, by rfl⟩ : syracuseStep 9297757 = 3486659) B3486659
theorem B679991 : Blo 451781 679991 := bstep (se 1 (by rfl) ⟨509993, by rfl⟩ : syracuseStep 679991 = 1019987) B1019987
theorem B680063 : Blo 451781 680063 := bstep (se 1 (by rfl) ⟨510047, by rfl⟩ : syracuseStep 680063 = 1020095) B1020095
theorem B1728823 : Blo 451781 1728823 := bstep (se 1 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 1728823 = 2593235) B2593235
theorem B2908831 : Blo 451781 2908831 := bstep (se 1 (by rfl) ⟨2181623, by rfl⟩ : syracuseStep 2908831 = 4363247) B4363247
theorem B451903 : Blo 451781 451903 := bstep (se 1 (by rfl) ⟨338927, by rfl⟩ : syracuseStep 451903 = 677855) B677855
theorem B451943 : Blo 451781 451943 := bstep (se 1 (by rfl) ⟨338957, by rfl⟩ : syracuseStep 451943 = 677915) B677915
theorem B681563 : Blo 451781 681563 := bstep (se 1 (by rfl) ⟨511172, by rfl⟩ : syracuseStep 681563 = 1022345) B1022345
theorem B452335 : Blo 451781 452335 := bstep (se 1 (by rfl) ⟨339251, by rfl⟩ : syracuseStep 452335 = 678503) B678503
theorem B681737 : Blo 451781 681737 := bstep (se 2 (by rfl) ⟨255651, by rfl⟩ : syracuseStep 681737 = 511303) B511303
theorem B452423 : Blo 451781 452423 := bstep (se 1 (by rfl) ⟨339317, by rfl⟩ : syracuseStep 452423 = 678635) B678635
theorem B452671 : Blo 451781 452671 := bstep (se 1 (by rfl) ⟨339503, by rfl⟩ : syracuseStep 452671 = 679007) B679007
theorem B452699 : Blo 451781 452699 := bstep (se 1 (by rfl) ⟨339524, by rfl⟩ : syracuseStep 452699 = 679049) B679049
theorem B452711 : Blo 451781 452711 := bstep (se 1 (by rfl) ⟨339533, by rfl⟩ : syracuseStep 452711 = 679067) B679067
theorem B452735 : Blo 451781 452735 := bstep (se 1 (by rfl) ⟨339551, by rfl⟩ : syracuseStep 452735 = 679103) B679103
theorem B4352251 : Blo 451781 4352251 := bstep (se 1 (by rfl) ⟨3264188, by rfl⟩ : syracuseStep 4352251 = 6528377) B6528377
theorem B682235 : Blo 451781 682235 := bstep (se 1 (by rfl) ⟨511676, by rfl⟩ : syracuseStep 682235 = 1023353) B1023353
theorem B453023 : Blo 451781 453023 := bstep (se 1 (by rfl) ⟨339767, by rfl⟩ : syracuseStep 453023 = 679535) B679535
theorem B453103 : Blo 451781 453103 := bstep (se 1 (by rfl) ⟨339827, by rfl⟩ : syracuseStep 453103 = 679655) B679655
theorem B2910829 : Blo 451781 2910829 := bstep (se 3 (by rfl) ⟨545780, by rfl⟩ : syracuseStep 2910829 = 1091561) B1091561
theorem B2288249 : Blo 451781 2288249 := bstep (se 2 (by rfl) ⟨858093, by rfl⟩ : syracuseStep 2288249 = 1716187) B1716187
theorem B3927131 : Blo 451781 3927131 := bstep (se 1 (by rfl) ⟨2945348, by rfl⟩ : syracuseStep 3927131 = 5890697) B5890697
theorem B683099 : Blo 451781 683099 := bstep (se 1 (by rfl) ⟨512324, by rfl⟩ : syracuseStep 683099 = 1024649) B1024649
theorem B1633409 : Blo 451781 1633409 := bstep (se 2 (by rfl) ⟨612528, by rfl⟩ : syracuseStep 1633409 = 1225057) B1225057
theorem B683561 : Blo 451781 683561 := bstep (se 2 (by rfl) ⟨256335, by rfl⟩ : syracuseStep 683561 = 512671) B512671
theorem B2584487 : Blo 451781 2584487 := bstep (se 1 (by rfl) ⟨1938365, by rfl⟩ : syracuseStep 2584487 = 3876731) B3876731
theorem B1535975 : Blo 451781 1535975 := bstep (se 1 (by rfl) ⟨1151981, by rfl⟩ : syracuseStep 1535975 = 2303963) B2303963
theorem B4124819 : Blo 451781 4124819 := bstep (se 1 (by rfl) ⟨3093614, by rfl⟩ : syracuseStep 4124819 = 6187229) B6187229
theorem B455135 : Blo 451781 455135 := bstep (se 1 (by rfl) ⟨341351, by rfl⟩ : syracuseStep 455135 = 682703) B682703
theorem B455771 : Blo 451781 455771 := bstep (se 1 (by rfl) ⟨341828, by rfl⟩ : syracuseStep 455771 = 683657) B683657
theorem B1537703 : Blo 451781 1537703 := bstep (se 1 (by rfl) ⟨1153277, by rfl⟩ : syracuseStep 1537703 = 2306555) B2306555
theorem B1865423 : Blo 451781 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B12449771 : Blo 451781 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B1144955 : Blo 451781 1144955 := bstep (se 1 (by rfl) ⟨858716, by rfl⟩ : syracuseStep 1144955 = 1717433) B1717433
theorem B29752739 : Blo 451781 29752739 := bstep (se 1 (by rfl) ⟨22314554, by rfl⟩ : syracuseStep 29752739 = 44629109) B44629109
theorem B2490209 : Blo 451781 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B819767 : Blo 451781 819767 := bstep (se 1 (by rfl) ⟨614825, by rfl⟩ : syracuseStep 819767 = 1229651) B1229651
theorem B1017107 : Blo 451781 1017107 := bstep (se 1 (by rfl) ⟨762830, by rfl⟩ : syracuseStep 1017107 = 1525661) B1525661
theorem B13043267 : Blo 451781 13043267 := bstep (se 1 (by rfl) ⟨9782450, by rfl⟩ : syracuseStep 13043267 = 19564901) B19564901
theorem B1148681 : Blo 451781 1148681 := bstep (se 2 (by rfl) ⟨430755, by rfl⟩ : syracuseStep 1148681 = 861511) B861511
theorem B1050751 : Blo 451781 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B7440679 : Blo 451781 7440679 := bstep (se 1 (by rfl) ⟨5580509, by rfl⟩ : syracuseStep 7440679 = 11161019) B11161019
theorem B4426139 : Blo 451781 4426139 := bstep (se 1 (by rfl) ⟨3319604, by rfl⟩ : syracuseStep 4426139 = 6639209) B6639209
theorem B756463 : Blo 451781 756463 := bstep (se 1 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 756463 = 1134695) B1134695
theorem B1018835 : Blo 451781 1018835 := bstep (se 1 (by rfl) ⟨764126, by rfl⟩ : syracuseStep 1018835 = 1528253) B1528253
theorem B5803001 : Blo 451781 5803001 := bstep (se 2 (by rfl) ⟨2176125, by rfl⟩ : syracuseStep 5803001 = 4352251) B4352251
theorem B2461375 : Blo 451781 2461375 := bstep (se 1 (by rfl) ⟨1846031, by rfl⟩ : syracuseStep 2461375 = 3692063) B3692063
theorem B1019897 : Blo 451781 1019897 := bstep (se 2 (by rfl) ⟨382461, by rfl⟩ : syracuseStep 1019897 = 764923) B764923
theorem B922337 : Blo 451781 922337 := bstep (se 2 (by rfl) ⟨345876, by rfl⟩ : syracuseStep 922337 = 691753) B691753
theorem B42407023 : Blo 451781 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B1447931 : Blo 451781 1447931 := bstep (se 1 (by rfl) ⟨1085948, by rfl⟩ : syracuseStep 1447931 = 2171897) B2171897
theorem B858215 : Blo 451781 858215 := bstep (se 1 (by rfl) ⟨643661, by rfl⟩ : syracuseStep 858215 = 1287323) B1287323
theorem B3284071 : Blo 451781 3284071 := bstep (se 1 (by rfl) ⟨2463053, by rfl⟩ : syracuseStep 3284071 = 4926107) B4926107
theorem B859241 : Blo 451781 859241 := bstep (se 2 (by rfl) ⟨322215, by rfl⟩ : syracuseStep 859241 = 644431) B644431
theorem B2956475 : Blo 451781 2956475 := bstep (se 1 (by rfl) ⟨2217356, by rfl⟩ : syracuseStep 2956475 = 4434713) B4434713
theorem B1088939 : Blo 451781 1088939 := bstep (se 1 (by rfl) ⟨816704, by rfl⟩ : syracuseStep 1088939 = 1633409) B1633409
theorem B1843049 : Blo 451781 1843049 := bstep (se 2 (by rfl) ⟨691143, by rfl⟩ : syracuseStep 1843049 = 1382287) B1382287
theorem B1023983 : Blo 451781 1023983 := bstep (se 1 (by rfl) ⟨767987, by rfl⟩ : syracuseStep 1023983 = 1535975) B1535975
theorem B1942177 : Blo 451781 1942177 := bstep (se 2 (by rfl) ⟨728316, by rfl⟩ : syracuseStep 1942177 = 1456633) B1456633
theorem B1025135 : Blo 451781 1025135 := bstep (se 1 (by rfl) ⟨768851, by rfl⟩ : syracuseStep 1025135 = 1537703) B1537703
theorem B6628679 : Blo 451781 6628679 := bstep (se 1 (by rfl) ⟨4971509, by rfl⟩ : syracuseStep 6628679 = 9943019) B9943019
theorem B8299847 : Blo 451781 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B763303 : Blo 451781 763303 := bstep (se 1 (by rfl) ⟨572477, by rfl⟩ : syracuseStep 763303 = 1144955) B1144955
theorem B862073 : Blo 451781 862073 := bstep (se 2 (by rfl) ⟨323277, by rfl⟩ : syracuseStep 862073 = 646555) B646555
theorem B19835159 : Blo 451781 19835159 := bstep (se 1 (by rfl) ⟨14876369, by rfl⟩ : syracuseStep 19835159 = 29752739) B29752739
theorem B764329 : Blo 451781 764329 := bstep (se 2 (by rfl) ⟨286623, by rfl⟩ : syracuseStep 764329 = 573247) B573247
theorem B12397009 : Blo 451781 12397009 := bstep (se 2 (by rfl) ⟨4648878, by rfl⟩ : syracuseStep 12397009 = 9297757) B9297757
theorem B2305097 : Blo 451781 2305097 := bstep (se 2 (by rfl) ⟨864411, by rfl⟩ : syracuseStep 2305097 = 1728823) B1728823
theorem B5189021 : Blo 451781 5189021 := bstep (se 3 (by rfl) ⟨972941, by rfl⟩ : syracuseStep 5189021 = 1945883) B1945883
theorem B6565283 : Blo 451781 6565283 := bstep (se 1 (by rfl) ⟨4923962, by rfl⟩ : syracuseStep 6565283 = 9847925) B9847925
theorem B3878441 : Blo 451781 3878441 := bstep (se 2 (by rfl) ⟨1454415, by rfl⟩ : syracuseStep 3878441 = 2908831) B2908831
theorem B9809515 : Blo 451781 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B765659 : Blo 451781 765659 := bstep (se 1 (by rfl) ⟨574244, by rfl⟩ : syracuseStep 765659 = 1148489) B1148489
theorem B1454287 : Blo 451781 1454287 := bstep (se 1 (by rfl) ⟨1090715, by rfl⟩ : syracuseStep 1454287 = 2181431) B2181431
theorem B1159817 : Blo 451781 1159817 := bstep (se 2 (by rfl) ⟨434931, by rfl⟩ : syracuseStep 1159817 = 869863) B869863
theorem B1946567 : Blo 451781 1946567 := bstep (se 1 (by rfl) ⟨1459925, by rfl⟩ : syracuseStep 1946567 = 2919851) B2919851
theorem B3881105 : Blo 451781 3881105 := bstep (se 2 (by rfl) ⟨1455414, by rfl⟩ : syracuseStep 3881105 = 2910829) B2910829
theorem B768359 : Blo 451781 768359 := bstep (se 1 (by rfl) ⟨576269, by rfl⟩ : syracuseStep 768359 = 1152539) B1152539
theorem B1719103 : Blo 451781 1719103 := bstep (se 1 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 1719103 = 2578655) B2578655
theorem B7781345 : Blo 451781 7781345 := bstep (se 2 (by rfl) ⟨2918004, by rfl⟩ : syracuseStep 7781345 = 5836009) B5836009
theorem B3882815 : Blo 451781 3882815 := bstep (se 1 (by rfl) ⟨2912111, by rfl⟩ : syracuseStep 3882815 = 5824223) B5824223
theorem B508351 : Blo 451781 508351 := bstep (se 1 (by rfl) ⟨381263, by rfl⟩ : syracuseStep 508351 = 762527) B762527
theorem B3457889 : Blo 451781 3457889 := bstep (se 2 (by rfl) ⟨1296708, by rfl⟩ : syracuseStep 3457889 = 2593417) B2593417
theorem B509647 : Blo 451781 509647 := bstep (se 1 (by rfl) ⟨382235, by rfl⟩ : syracuseStep 509647 = 764471) B764471
theorem B1525499 : Blo 451781 1525499 := bstep (se 1 (by rfl) ⟨1144124, by rfl⟩ : syracuseStep 1525499 = 2288249) B2288249
theorem B1296425 : Blo 451781 1296425 := bstep (se 2 (by rfl) ⟨486159, by rfl⟩ : syracuseStep 1296425 = 972319) B972319
theorem B575743 : Blo 451781 575743 := bstep (se 1 (by rfl) ⟨431807, by rfl⟩ : syracuseStep 575743 = 863615) B863615
theorem B1722991 : Blo 451781 1722991 := bstep (se 1 (by rfl) ⟨1292243, by rfl⟩ : syracuseStep 1722991 = 2584487) B2584487
theorem B1526525 : Blo 451781 1526525 := bstep (se 3 (by rfl) ⟨286223, by rfl⟩ : syracuseStep 1526525 = 572447) B572447
theorem B511087 : Blo 451781 511087 := bstep (se 1 (by rfl) ⟨383315, by rfl⟩ : syracuseStep 511087 = 766631) B766631
theorem B44092997 : Blo 451781 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B1724449 : Blo 451781 1724449 := bstep (se 2 (by rfl) ⟨646668, by rfl⟩ : syracuseStep 1724449 = 1293337) B1293337
theorem B6541523 : Blo 451781 6541523 := bstep (se 1 (by rfl) ⟨4906142, by rfl⟩ : syracuseStep 6541523 = 9812285) B9812285
theorem B7459235 : Blo 451781 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B1167823 : Blo 451781 1167823 := bstep (se 1 (by rfl) ⟨875867, by rfl⟩ : syracuseStep 1167823 = 1751735) B1751735
theorem B1660139 : Blo 451781 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B37213991 : Blo 451781 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B677759 : Blo 451781 677759 := bstep (se 1 (by rfl) ⟨508319, by rfl⟩ : syracuseStep 677759 = 1016639) B1016639
theorem B677867 : Blo 451781 677867 := bstep (se 1 (by rfl) ⟨508400, by rfl⟩ : syracuseStep 677867 = 1016801) B1016801
theorem B19880063 : Blo 451781 19880063 := bstep (se 1 (by rfl) ⟨14910047, by rfl⟩ : syracuseStep 19880063 = 29820095) B29820095
theorem B678281 : Blo 451781 678281 := bstep (se 2 (by rfl) ⟨254355, by rfl⟩ : syracuseStep 678281 = 508711) B508711
theorem B1530251 : Blo 451781 1530251 := bstep (se 1 (by rfl) ⟨1147688, by rfl⟩ : syracuseStep 1530251 = 2295377) B2295377
theorem B678383 : Blo 451781 678383 := bstep (se 1 (by rfl) ⟨508787, by rfl⟩ : syracuseStep 678383 = 1017575) B1017575
theorem B2906705 : Blo 451781 2906705 := bstep (se 2 (by rfl) ⟨1090014, by rfl⟩ : syracuseStep 2906705 = 2180029) B2180029
theorem B2906729 : Blo 451781 2906729 := bstep (se 2 (by rfl) ⟨1090023, by rfl⟩ : syracuseStep 2906729 = 2180047) B2180047
theorem B678665 : Blo 451781 678665 := bstep (se 2 (by rfl) ⟨254499, by rfl⟩ : syracuseStep 678665 = 508999) B508999
theorem B1530791 : Blo 451781 1530791 := bstep (se 1 (by rfl) ⟨1148093, by rfl⟩ : syracuseStep 1530791 = 2296187) B2296187
theorem B679079 : Blo 451781 679079 := bstep (se 1 (by rfl) ⟨509309, by rfl⟩ : syracuseStep 679079 = 1018619) B1018619
theorem B6216911 : Blo 451781 6216911 := bstep (se 1 (by rfl) ⟨4662683, by rfl⟩ : syracuseStep 6216911 = 9325367) B9325367
theorem B7724483 : Blo 451781 7724483 := bstep (se 1 (by rfl) ⟨5793362, by rfl⟩ : syracuseStep 7724483 = 11586725) B11586725
theorem B679583 : Blo 451781 679583 := bstep (se 1 (by rfl) ⟨509687, by rfl⟩ : syracuseStep 679583 = 1019375) B1019375
theorem B1728337 : Blo 451781 1728337 := bstep (se 2 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 1728337 = 1296253) B1296253
theorem B1531817 : Blo 451781 1531817 := bstep (se 2 (by rfl) ⟨574431, by rfl⟩ : syracuseStep 1531817 = 1148863) B1148863
theorem B679967 : Blo 451781 679967 := bstep (se 1 (by rfl) ⟨509975, by rfl⟩ : syracuseStep 679967 = 1019951) B1019951
theorem B7004227 : Blo 451781 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B680057 : Blo 451781 680057 := bstep (se 2 (by rfl) ⟨255021, by rfl⟩ : syracuseStep 680057 = 510043) B510043
theorem B1728641 : Blo 451781 1728641 := bstep (se 2 (by rfl) ⟨648240, by rfl⟩ : syracuseStep 1728641 = 1296481) B1296481
theorem B680105 : Blo 451781 680105 := bstep (se 2 (by rfl) ⟨255039, by rfl⟩ : syracuseStep 680105 = 510079) B510079
theorem B680315 : Blo 451781 680315 := bstep (se 1 (by rfl) ⟨510236, by rfl⟩ : syracuseStep 680315 = 1020473) B1020473
theorem B680795 : Blo 451781 680795 := bstep (se 1 (by rfl) ⟨510596, by rfl⟩ : syracuseStep 680795 = 1021193) B1021193
theorem B680831 : Blo 451781 680831 := bstep (se 1 (by rfl) ⟨510623, by rfl⟩ : syracuseStep 680831 = 1021247) B1021247
theorem B680903 : Blo 451781 680903 := bstep (se 1 (by rfl) ⟨510677, by rfl⟩ : syracuseStep 680903 = 1021355) B1021355
theorem B1729583 : Blo 451781 1729583 := bstep (se 1 (by rfl) ⟨1297187, by rfl⟩ : syracuseStep 1729583 = 2594375) B2594375
theorem B451835 : Blo 451781 451835 := bstep (se 1 (by rfl) ⟨338876, by rfl⟩ : syracuseStep 451835 = 677753) B677753
theorem B681287 : Blo 451781 681287 := bstep (se 1 (by rfl) ⟨510965, by rfl⟩ : syracuseStep 681287 = 1021931) B1021931
theorem B681383 : Blo 451781 681383 := bstep (se 1 (by rfl) ⟨511037, by rfl⟩ : syracuseStep 681383 = 1022075) B1022075
theorem B1533599 : Blo 451781 1533599 := bstep (se 1 (by rfl) ⟨1150199, by rfl⟩ : syracuseStep 1533599 = 2300399) B2300399
theorem B681647 : Blo 451781 681647 := bstep (se 1 (by rfl) ⟨511235, by rfl⟩ : syracuseStep 681647 = 1022471) B1022471
theorem B8251091 : Blo 451781 8251091 := bstep (se 1 (by rfl) ⟨6188318, by rfl⟩ : syracuseStep 8251091 = 12376637) B12376637
theorem B452351 : Blo 451781 452351 := bstep (se 1 (by rfl) ⟨339263, by rfl⟩ : syracuseStep 452351 = 678527) B678527
theorem B3237937 : Blo 451781 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B682091 : Blo 451781 682091 := bstep (se 1 (by rfl) ⟨511568, by rfl⟩ : syracuseStep 682091 = 1023137) B1023137
theorem B682151 : Blo 451781 682151 := bstep (se 1 (by rfl) ⟨511613, by rfl⟩ : syracuseStep 682151 = 1023227) B1023227
theorem B682223 : Blo 451781 682223 := bstep (se 1 (by rfl) ⟨511667, by rfl⟩ : syracuseStep 682223 = 1023335) B1023335
theorem B682607 : Blo 451781 682607 := bstep (se 1 (by rfl) ⟨511955, by rfl⟩ : syracuseStep 682607 = 1023911) B1023911
theorem B1632905 : Blo 451781 1632905 := bstep (se 2 (by rfl) ⟨612339, by rfl⟩ : syracuseStep 1632905 = 1224679) B1224679
theorem B1534625 : Blo 451781 1534625 := bstep (se 2 (by rfl) ⟨575484, by rfl⟩ : syracuseStep 1534625 = 1150969) B1150969
theorem B453327 : Blo 451781 453327 := bstep (se 1 (by rfl) ⟨339995, by rfl⟩ : syracuseStep 453327 = 679991) B679991
theorem B682715 : Blo 451781 682715 := bstep (se 1 (by rfl) ⟨512036, by rfl⟩ : syracuseStep 682715 = 1024073) B1024073
theorem B453375 : Blo 451781 453375 := bstep (se 1 (by rfl) ⟨340031, by rfl⟩ : syracuseStep 453375 = 680063) B680063
theorem B111602609 : Blo 451781 111602609 := bstep (se 2 (by rfl) ⟨41850978, by rfl⟩ : syracuseStep 111602609 = 83701957) B83701957
theorem B683471 : Blo 451781 683471 := bstep (se 1 (by rfl) ⟨512603, by rfl⟩ : syracuseStep 683471 = 1025207) B1025207
theorem B683519 : Blo 451781 683519 := bstep (se 1 (by rfl) ⟨512639, by rfl⟩ : syracuseStep 683519 = 1025279) B1025279
theorem B454375 : Blo 451781 454375 := bstep (se 1 (by rfl) ⟨340781, by rfl⟩ : syracuseStep 454375 = 681563) B681563
theorem B454491 : Blo 451781 454491 := bstep (se 1 (by rfl) ⟨340868, by rfl⟩ : syracuseStep 454491 = 681737) B681737
theorem B454823 : Blo 451781 454823 := bstep (se 1 (by rfl) ⟨341117, by rfl⟩ : syracuseStep 454823 = 682235) B682235
theorem B1536191 : Blo 451781 1536191 := bstep (se 1 (by rfl) ⟨1152143, by rfl⟩ : syracuseStep 1536191 = 2304287) B2304287
theorem B618983 : Blo 451781 618983 := bstep (se 1 (by rfl) ⟨464237, by rfl⟩ : syracuseStep 618983 = 928475) B928475
theorem B2618087 : Blo 451781 2618087 := bstep (se 1 (by rfl) ⟨1963565, by rfl⟩ : syracuseStep 2618087 = 3927131) B3927131
theorem B455399 : Blo 451781 455399 := bstep (se 1 (by rfl) ⟨341549, by rfl⟩ : syracuseStep 455399 = 683099) B683099
theorem B455707 : Blo 451781 455707 := bstep (se 1 (by rfl) ⟨341780, by rfl⟩ : syracuseStep 455707 = 683561) B683561
theorem B5174441 : Blo 451781 5174441 := bstep (se 2 (by rfl) ⟨1940415, by rfl⟩ : syracuseStep 5174441 = 3880831) B3880831
theorem B2749879 : Blo 451781 2749879 := bstep (se 1 (by rfl) ⟨2062409, by rfl⟩ : syracuseStep 2749879 = 4124819) B4124819
theorem B2586127 : Blo 451781 2586127 := bstep (se 1 (by rfl) ⟨1939595, by rfl⟩ : syracuseStep 2586127 = 3879191) B3879191
theorem B2455147 : Blo 451781 2455147 := bstep (se 1 (by rfl) ⟨1841360, by rfl⟩ : syracuseStep 2455147 = 3682721) B3682721
theorem B5896061 : Blo 451781 5896061 := bstep (se 3 (by rfl) ⟨1105511, by rfl⟩ : syracuseStep 5896061 = 2211023) B2211023
theorem B1243615 : Blo 451781 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B4357097 : Blo 451781 4357097 := bstep (se 2 (by rfl) ⟨1633911, by rfl⟩ : syracuseStep 4357097 = 3267823) B3267823
theorem B9338969 : Blo 451781 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B17268997 : Blo 451781 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B2589569 : Blo 451781 2589569 := bstep (se 2 (by rfl) ⟨971088, by rfl⟩ : syracuseStep 2589569 = 1942177) B1942177
theorem B1016999 : Blo 451781 1016999 := bstep (se 1 (by rfl) ⟨762749, by rfl⟩ : syracuseStep 1016999 = 1525499) B1525499
theorem B39683621 : Blo 451781 39683621 := bstep (se 4 (by rfl) ⟨3720339, by rfl⟩ : syracuseStep 39683621 = 7440679) B7440679
theorem B2950759 : Blo 451781 2950759 := bstep (se 1 (by rfl) ⟨2213069, by rfl⟩ : syracuseStep 2950759 = 4426139) B4426139
theorem B1017683 : Blo 451781 1017683 := bstep (se 1 (by rfl) ⟨763262, by rfl⟩ : syracuseStep 1017683 = 1526525) B1526525
theorem B1017737 : Blo 451781 1017737 := bstep (se 2 (by rfl) ⟨381651, by rfl⟩ : syracuseStep 1017737 = 763303) B763303
theorem B6981565 : Blo 451781 6981565 := bstep (se 3 (by rfl) ⟨1309043, by rfl⟩ : syracuseStep 6981565 = 2618087) B2618087
theorem B3868667 : Blo 451781 3868667 := bstep (se 1 (by rfl) ⟨2901500, by rfl⟩ : syracuseStep 3868667 = 5803001) B5803001
theorem B29395331 : Blo 451781 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B6228389 : Blo 451781 6228389 := bstep (se 4 (by rfl) ⟨583911, by rfl⟩ : syracuseStep 6228389 = 1167823) B1167823
theorem B4361015 : Blo 451781 4361015 := bstep (se 1 (by rfl) ⟨3270761, by rfl⟩ : syracuseStep 4361015 = 6541523) B6541523
theorem B1019105 : Blo 451781 1019105 := bstep (se 2 (by rfl) ⟨382164, by rfl⟩ : syracuseStep 1019105 = 764329) B764329
theorem B2297321 : Blo 451781 2297321 := bstep (se 2 (by rfl) ⟨861495, by rfl⟩ : syracuseStep 2297321 = 1722991) B1722991
theorem B24809327 : Blo 451781 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B1020167 : Blo 451781 1020167 := bstep (se 1 (by rfl) ⟨765125, by rfl⟩ : syracuseStep 1020167 = 1530251) B1530251
theorem B1937803 : Blo 451781 1937803 := bstep (se 1 (by rfl) ⟨1453352, by rfl⟩ : syracuseStep 1937803 = 2906705) B2906705
theorem B1937819 : Blo 451781 1937819 := bstep (se 1 (by rfl) ⟨1453364, by rfl⟩ : syracuseStep 1937819 = 2906729) B2906729
theorem B1020527 : Blo 451781 1020527 := bstep (se 1 (by rfl) ⟨765395, by rfl⟩ : syracuseStep 1020527 = 1530791) B1530791
theorem B1970983 : Blo 451781 1970983 := bstep (se 1 (by rfl) ⟨1478237, by rfl⟩ : syracuseStep 1970983 = 2956475) B2956475
theorem B13079353 : Blo 451781 13079353 := bstep (se 2 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 13079353 = 9809515) B9809515
theorem B3281833 : Blo 451781 3281833 := bstep (se 2 (by rfl) ⟨1230687, by rfl⟩ : syracuseStep 3281833 = 2461375) B2461375
theorem B725959 : Blo 451781 725959 := bstep (se 1 (by rfl) ⟨544469, by rfl⟩ : syracuseStep 725959 = 1088939) B1088939
theorem B5149655 : Blo 451781 5149655 := bstep (se 1 (by rfl) ⟨3862241, by rfl⟩ : syracuseStep 5149655 = 7724483) B7724483
theorem B1021211 : Blo 451781 1021211 := bstep (se 1 (by rfl) ⟨765908, by rfl⟩ : syracuseStep 1021211 = 1531817) B1531817
theorem B2299265 : Blo 451781 2299265 := bstep (se 2 (by rfl) ⟨862224, by rfl⟩ : syracuseStep 2299265 = 1724449) B1724449
theorem B1152427 : Blo 451781 1152427 := bstep (se 1 (by rfl) ⟨864320, by rfl⟩ : syracuseStep 1152427 = 1728641) B1728641
theorem B1939049 : Blo 451781 1939049 := bstep (se 2 (by rfl) ⟨727143, by rfl⟩ : syracuseStep 1939049 = 1454287) B1454287
theorem B1153055 : Blo 451781 1153055 := bstep (se 1 (by rfl) ⟨864791, by rfl⟩ : syracuseStep 1153055 = 1729583) B1729583
theorem B52893757 : Blo 451781 52893757 := bstep (se 3 (by rfl) ⟨9917579, by rfl⟩ : syracuseStep 52893757 = 19835159) B19835159
theorem B1022399 : Blo 451781 1022399 := bstep (se 1 (by rfl) ⟨766799, by rfl⟩ : syracuseStep 1022399 = 1533599) B1533599
theorem B1088603 : Blo 451781 1088603 := bstep (se 1 (by rfl) ⟨816452, by rfl⟩ : syracuseStep 1088603 = 1632905) B1632905
theorem B1023083 : Blo 451781 1023083 := bstep (se 1 (by rfl) ⟨767312, by rfl⟩ : syracuseStep 1023083 = 1534625) B1534625
theorem B3448169 : Blo 451781 3448169 := bstep (se 2 (by rfl) ⟨1293063, by rfl⟩ : syracuseStep 3448169 = 2586127) B2586127
theorem B1024127 : Blo 451781 1024127 := bstep (se 1 (by rfl) ⟨768095, by rfl⟩ : syracuseStep 1024127 = 1536191) B1536191
theorem B3449627 : Blo 451781 3449627 := bstep (se 1 (by rfl) ⟨2587220, by rfl⟩ : syracuseStep 3449627 = 5174441) B5174441
theorem B5187563 : Blo 451781 5187563 := bstep (se 1 (by rfl) ⟨3890672, by rfl⟩ : syracuseStep 5187563 = 7781345) B7781345
theorem B2304449 : Blo 451781 2304449 := bstep (se 2 (by rfl) ⟨864168, by rfl⟩ : syracuseStep 2304449 = 1728337) B1728337
theorem B2305259 : Blo 451781 2305259 := bstep (se 1 (by rfl) ⟨1728944, by rfl⟩ : syracuseStep 2305259 = 3457889) B3457889
theorem B8695511 : Blo 451781 8695511 := bstep (se 1 (by rfl) ⟨6521633, by rfl⟩ : syracuseStep 8695511 = 13043267) B13043267
theorem B765787 : Blo 451781 765787 := bstep (se 1 (by rfl) ⟨574340, by rfl⟩ : syracuseStep 765787 = 1148681) B1148681
theorem B864283 : Blo 451781 864283 := bstep (se 1 (by rfl) ⟨648212, by rfl⟩ : syracuseStep 864283 = 1296425) B1296425
theorem B767657 : Blo 451781 767657 := bstep (se 2 (by rfl) ⟨287871, by rfl⟩ : syracuseStep 767657 = 575743) B575743
theorem B16529345 : Blo 451781 16529345 := bstep (se 2 (by rfl) ⟨6198504, by rfl⟩ : syracuseStep 16529345 = 12397009) B12397009
theorem B965287 : Blo 451781 965287 := bstep (se 1 (by rfl) ⟨723965, by rfl⟩ : syracuseStep 965287 = 1447931) B1447931
theorem B13253375 : Blo 451781 13253375 := bstep (se 1 (by rfl) ⟨9940031, by rfl⟩ : syracuseStep 13253375 = 19880063) B19880063
theorem B572827 : Blo 451781 572827 := bstep (se 1 (by rfl) ⟨429620, by rfl⟩ : syracuseStep 572827 = 859241) B859241
theorem B4144607 : Blo 451781 4144607 := bstep (se 1 (by rfl) ⟨3108455, by rfl⟩ : syracuseStep 4144607 = 6216911) B6216911
theorem B6602485 : Blo 451781 6602485 := bstep (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) B618983
theorem B1228699 : Blo 451781 1228699 := bstep (se 1 (by rfl) ⟨921524, by rfl⟩ : syracuseStep 1228699 = 1843049) B1843049
theorem B17515045 : Blo 451781 17515045 := bstep (se 4 (by rfl) ⟨1642035, by rfl⟩ : syracuseStep 17515045 = 3284071) B3284071
theorem B574715 : Blo 451781 574715 := bstep (se 1 (by rfl) ⟨431036, by rfl⟩ : syracuseStep 574715 = 862073) B862073
theorem B12371381 : Blo 451781 12371381 := bstep (se 5 (by rfl) ⟨579908, by rfl⟩ : syracuseStep 12371381 = 1159817) B1159817
theorem B56542697 : Blo 451781 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B74401739 : Blo 451781 74401739 := bstep (se 1 (by rfl) ⟨55801304, by rfl⟩ : syracuseStep 74401739 = 111602609) B111602609
theorem B3459347 : Blo 451781 3459347 := bstep (se 1 (by rfl) ⟨2594510, by rfl⟩ : syracuseStep 3459347 = 5189021) B5189021
theorem B4376855 : Blo 451781 4376855 := bstep (se 1 (by rfl) ⟨3282641, by rfl⟩ : syracuseStep 4376855 = 6565283) B6565283
theorem B14666021 : Blo 451781 14666021 := bstep (se 4 (by rfl) ⟨1374939, by rfl⟩ : syracuseStep 14666021 = 2749879) B2749879
theorem B510439 : Blo 451781 510439 := bstep (se 1 (by rfl) ⟨382829, by rfl⟩ : syracuseStep 510439 = 765659) B765659
theorem B1658153 : Blo 451781 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B1297711 : Blo 451781 1297711 := bstep (se 1 (by rfl) ⟨973283, by rfl⟩ : syracuseStep 1297711 = 1946567) B1946567
theorem B512239 : Blo 451781 512239 := bstep (se 1 (by rfl) ⟨384179, by rfl⟩ : syracuseStep 512239 = 768359) B768359
theorem B2904731 : Blo 451781 2904731 := bstep (se 1 (by rfl) ⟨2178548, by rfl⟩ : syracuseStep 2904731 = 4357097) B4357097
theorem B546511 : Blo 451781 546511 := bstep (se 1 (by rfl) ⟨409883, by rfl⟩ : syracuseStep 546511 = 819767) B819767
theorem B677801 : Blo 451781 677801 := bstep (se 2 (by rfl) ⟨254175, by rfl⟩ : syracuseStep 677801 = 508351) B508351
theorem B678071 : Blo 451781 678071 := bstep (se 1 (by rfl) ⟨508553, by rfl⟩ : syracuseStep 678071 = 1017107) B1017107
theorem B679223 : Blo 451781 679223 := bstep (se 1 (by rfl) ⟨509417, by rfl⟩ : syracuseStep 679223 = 1018835) B1018835
theorem B679529 : Blo 451781 679529 := bstep (se 2 (by rfl) ⟨254823, by rfl⟩ : syracuseStep 679529 = 509647) B509647
theorem B679931 : Blo 451781 679931 := bstep (se 1 (by rfl) ⟨509948, by rfl⟩ : syracuseStep 679931 = 1019897) B1019897
theorem B1401001 : Blo 451781 1401001 := bstep (se 2 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 1401001 = 1050751) B1050751
theorem B4972823 : Blo 451781 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B614891 : Blo 451781 614891 := bstep (se 1 (by rfl) ⟨461168, by rfl⟩ : syracuseStep 614891 = 922337) B922337
theorem B1106759 : Blo 451781 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B1008617 : Blo 451781 1008617 := bstep (se 2 (by rfl) ⟨378231, by rfl⟩ : syracuseStep 1008617 = 756463) B756463
theorem B451839 : Blo 451781 451839 := bstep (se 1 (by rfl) ⟨338879, by rfl⟩ : syracuseStep 451839 = 677759) B677759
theorem B451911 : Blo 451781 451911 := bstep (se 1 (by rfl) ⟨338933, by rfl⟩ : syracuseStep 451911 = 677867) B677867
theorem B681449 : Blo 451781 681449 := bstep (se 2 (by rfl) ⟨255543, by rfl⟩ : syracuseStep 681449 = 511087) B511087
theorem B452187 : Blo 451781 452187 := bstep (se 1 (by rfl) ⟨339140, by rfl⟩ : syracuseStep 452187 = 678281) B678281
theorem B452255 : Blo 451781 452255 := bstep (se 1 (by rfl) ⟨339191, by rfl⟩ : syracuseStep 452255 = 678383) B678383
theorem B452443 : Blo 451781 452443 := bstep (se 1 (by rfl) ⟨339332, by rfl⟩ : syracuseStep 452443 = 678665) B678665
theorem B452719 : Blo 451781 452719 := bstep (se 1 (by rfl) ⟨339539, by rfl⟩ : syracuseStep 452719 = 679079) B679079
theorem B453055 : Blo 451781 453055 := bstep (se 1 (by rfl) ⟨339791, by rfl⟩ : syracuseStep 453055 = 679583) B679583
theorem B682655 : Blo 451781 682655 := bstep (se 1 (by rfl) ⟨511991, by rfl⟩ : syracuseStep 682655 = 1023983) B1023983
theorem B453311 : Blo 451781 453311 := bstep (se 1 (by rfl) ⟨339983, by rfl⟩ : syracuseStep 453311 = 679967) B679967
theorem B453371 : Blo 451781 453371 := bstep (se 1 (by rfl) ⟨340028, by rfl⟩ : syracuseStep 453371 = 680057) B680057
theorem B453403 : Blo 451781 453403 := bstep (se 1 (by rfl) ⟨340052, by rfl⟩ : syracuseStep 453403 = 680105) B680105
theorem B453543 : Blo 451781 453543 := bstep (se 1 (by rfl) ⟨340157, by rfl⟩ : syracuseStep 453543 = 680315) B680315
theorem B2288573 : Blo 451781 2288573 := bstep (se 3 (by rfl) ⟨429107, by rfl⟩ : syracuseStep 2288573 = 858215) B858215
theorem B453863 : Blo 451781 453863 := bstep (se 1 (by rfl) ⟨340397, by rfl⟩ : syracuseStep 453863 = 680795) B680795
theorem B453887 : Blo 451781 453887 := bstep (se 1 (by rfl) ⟨340415, by rfl⟩ : syracuseStep 453887 = 680831) B680831
theorem B453935 : Blo 451781 453935 := bstep (se 1 (by rfl) ⟨340451, by rfl⟩ : syracuseStep 453935 = 680903) B680903
theorem B683423 : Blo 451781 683423 := bstep (se 1 (by rfl) ⟨512567, by rfl⟩ : syracuseStep 683423 = 1025135) B1025135
theorem B4419119 : Blo 451781 4419119 := bstep (se 1 (by rfl) ⟨3314339, by rfl⟩ : syracuseStep 4419119 = 6628679) B6628679
theorem B454191 : Blo 451781 454191 := bstep (se 1 (by rfl) ⟨340643, by rfl⟩ : syracuseStep 454191 = 681287) B681287
theorem B5533231 : Blo 451781 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B454255 : Blo 451781 454255 := bstep (se 1 (by rfl) ⟨340691, by rfl⟩ : syracuseStep 454255 = 681383) B681383
theorem B454431 : Blo 451781 454431 := bstep (se 1 (by rfl) ⟨340823, by rfl⟩ : syracuseStep 454431 = 681647) B681647
theorem B5500727 : Blo 451781 5500727 := bstep (se 1 (by rfl) ⟨4125545, by rfl⟩ : syracuseStep 5500727 = 8251091) B8251091
theorem B454727 : Blo 451781 454727 := bstep (se 1 (by rfl) ⟨341045, by rfl⟩ : syracuseStep 454727 = 682091) B682091
theorem B454767 : Blo 451781 454767 := bstep (se 1 (by rfl) ⟨341075, by rfl⟩ : syracuseStep 454767 = 682151) B682151
theorem B454815 : Blo 451781 454815 := bstep (se 1 (by rfl) ⟨341111, by rfl⟩ : syracuseStep 454815 = 682223) B682223
theorem B455071 : Blo 451781 455071 := bstep (se 1 (by rfl) ⟨341303, by rfl⟩ : syracuseStep 455071 = 682607) B682607
theorem B455143 : Blo 451781 455143 := bstep (se 1 (by rfl) ⟨341357, by rfl⟩ : syracuseStep 455143 = 682715) B682715
theorem B1536731 : Blo 451781 1536731 := bstep (se 1 (by rfl) ⟨1152548, by rfl⟩ : syracuseStep 1536731 = 2305097) B2305097
theorem B3273529 : Blo 451781 3273529 := bstep (se 2 (by rfl) ⟨1227573, by rfl⟩ : syracuseStep 3273529 = 2455147) B2455147
theorem B455647 : Blo 451781 455647 := bstep (se 1 (by rfl) ⟨341735, by rfl⟩ : syracuseStep 455647 = 683471) B683471
theorem B455679 : Blo 451781 455679 := bstep (se 1 (by rfl) ⟨341759, by rfl⟩ : syracuseStep 455679 = 683519) B683519
theorem B2585627 : Blo 451781 2585627 := bstep (se 1 (by rfl) ⟨1939220, by rfl⟩ : syracuseStep 2585627 = 3878441) B3878441
theorem B2292137 : Blo 451781 2292137 := bstep (se 2 (by rfl) ⟨859551, by rfl⟩ : syracuseStep 2292137 = 1719103) B1719103
theorem B3930707 : Blo 451781 3930707 := bstep (se 1 (by rfl) ⟨2948030, by rfl⟩ : syracuseStep 3930707 = 5896061) B5896061
theorem B2587403 : Blo 451781 2587403 := bstep (se 1 (by rfl) ⟨1940552, by rfl⟩ : syracuseStep 2587403 = 3881105) B3881105
theorem B2588543 : Blo 451781 2588543 := bstep (se 1 (by rfl) ⟨1941407, by rfl⟩ : syracuseStep 2588543 = 3882815) B3882815
theorem B6225979 : Blo 451781 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B1639709 : Blo 451781 1639709 := bstep (se 3 (by rfl) ⟨307445, by rfl⟩ : syracuseStep 1639709 = 614891) B614891
theorem B2917903 : Blo 451781 2917903 := bstep (se 1 (by rfl) ⟨2188427, by rfl⟩ : syracuseStep 2917903 = 4376855) B4376855
theorem B19596887 : Blo 451781 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B3934345 : Blo 451781 3934345 := bstep (se 2 (by rfl) ⟨1475379, by rfl⟩ : syracuseStep 3934345 = 2950759) B2950759
theorem B9308753 : Blo 451781 9308753 := bstep (se 2 (by rfl) ⟨3490782, by rfl⟩ : syracuseStep 9308753 = 6981565) B6981565
theorem B2689645 : Blo 451781 2689645 := bstep (se 3 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 2689645 = 1008617) B1008617
theorem B1936487 : Blo 451781 1936487 := bstep (se 1 (by rfl) ⟨1452365, by rfl⟩ : syracuseStep 1936487 = 2904731) B2904731
theorem B29888021 : Blo 451781 29888021 := bstep (se 6 (by rfl) ⟨700500, by rfl⟩ : syracuseStep 29888021 = 1401001) B1401001
theorem B5148197 : Blo 451781 5148197 := bstep (se 4 (by rfl) ⟨482643, by rfl⟩ : syracuseStep 5148197 = 965287) B965287
theorem B725735 : Blo 451781 725735 := bstep (se 1 (by rfl) ⟨544301, by rfl⟩ : syracuseStep 725735 = 1088603) B1088603
theorem B7377641 : Blo 451781 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B2298779 : Blo 451781 2298779 := bstep (se 1 (by rfl) ⟨1724084, by rfl⟩ : syracuseStep 2298779 = 3448169) B3448169
theorem B1021049 : Blo 451781 1021049 := bstep (se 2 (by rfl) ⟨382893, by rfl⟩ : syracuseStep 1021049 = 765787) B765787
theorem B1152377 : Blo 451781 1152377 := bstep (se 2 (by rfl) ⟨432141, by rfl⟩ : syracuseStep 1152377 = 864283) B864283
theorem B3315215 : Blo 451781 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B2299751 : Blo 451781 2299751 := bstep (se 1 (by rfl) ⟨1724813, by rfl⟩ : syracuseStep 2299751 = 3449627) B3449627
theorem B2627977 : Blo 451781 2627977 := bstep (se 2 (by rfl) ⟨985491, by rfl⟩ : syracuseStep 2627977 = 1970983) B1970983
theorem B17439137 : Blo 451781 17439137 := bstep (se 2 (by rfl) ⟨6539676, by rfl⟩ : syracuseStep 17439137 = 13079353) B13079353
theorem B4364705 : Blo 451781 4364705 := bstep (se 2 (by rfl) ⟨1636764, by rfl⟩ : syracuseStep 4364705 = 3273529) B3273529
theorem B728681 : Blo 451781 728681 := bstep (se 2 (by rfl) ⟨273255, by rfl⟩ : syracuseStep 728681 = 546511) B546511
theorem B70525009 : Blo 451781 70525009 := bstep (se 2 (by rfl) ⟨26446878, by rfl⟩ : syracuseStep 70525009 = 52893757) B52893757
theorem B1024487 : Blo 451781 1024487 := bstep (se 1 (by rfl) ⟨768365, by rfl⟩ : syracuseStep 1024487 = 1536731) B1536731
theorem B11019563 : Blo 451781 11019563 := bstep (se 1 (by rfl) ⟨8264672, by rfl⟩ : syracuseStep 11019563 = 16529345) B16529345
theorem B763769 : Blo 451781 763769 := bstep (se 2 (by rfl) ⟨286413, by rfl⟩ : syracuseStep 763769 = 572827) B572827
theorem B2763071 : Blo 451781 2763071 := bstep (se 1 (by rfl) ⟨2072303, by rfl⟩ : syracuseStep 2763071 = 4144607) B4144607
theorem B37695131 : Blo 451781 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B26455747 : Blo 451781 26455747 := bstep (se 1 (by rfl) ⟨19841810, by rfl⟩ : syracuseStep 26455747 = 39683621) B39683621
theorem B2306231 : Blo 451781 2306231 := bstep (se 1 (by rfl) ⟨1729673, by rfl⟩ : syracuseStep 2306231 = 3459347) B3459347
theorem B9777347 : Blo 451781 9777347 := bstep (se 1 (by rfl) ⟨7333010, by rfl⟩ : syracuseStep 9777347 = 14666021) B14666021
theorem B1291879 : Blo 451781 1291879 := bstep (se 1 (by rfl) ⟨968909, by rfl⟩ : syracuseStep 1291879 = 1937819) B1937819
theorem B1292699 : Blo 451781 1292699 := bstep (se 1 (by rfl) ⟨969524, by rfl⟩ : syracuseStep 1292699 = 1939049) B1939049
theorem B768703 : Blo 451781 768703 := bstep (se 1 (by rfl) ⟨576527, by rfl⟩ : syracuseStep 768703 = 1153055) B1153055
theorem B737839 : Blo 451781 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B4375777 : Blo 451781 4375777 := bstep (se 2 (by rfl) ⟨1640916, by rfl⟩ : syracuseStep 4375777 = 3281833) B3281833
theorem B967945 : Blo 451781 967945 := bstep (se 2 (by rfl) ⟨362979, by rfl⟩ : syracuseStep 967945 = 725959) B725959
theorem B3458375 : Blo 451781 3458375 := bstep (se 1 (by rfl) ⟨2593781, by rfl⟩ : syracuseStep 3458375 = 5187563) B5187563
theorem B1525715 : Blo 451781 1525715 := bstep (se 1 (by rfl) ⟨1144286, by rfl⟩ : syracuseStep 1525715 = 2288573) B2288573
theorem B1723751 : Blo 451781 1723751 := bstep (se 1 (by rfl) ⟨1292813, by rfl⟩ : syracuseStep 1723751 = 2585627) B2585627
theorem B511771 : Blo 451781 511771 := bstep (se 1 (by rfl) ⟨383828, by rfl⟩ : syracuseStep 511771 = 767657) B767657
theorem B1528091 : Blo 451781 1528091 := bstep (se 1 (by rfl) ⟨1146068, by rfl⟩ : syracuseStep 1528091 = 2292137) B2292137
theorem B8835583 : Blo 451781 8835583 := bstep (se 1 (by rfl) ⟨6626687, by rfl⟩ : syracuseStep 8835583 = 13253375) B13253375
theorem B1724935 : Blo 451781 1724935 := bstep (se 1 (by rfl) ⟨1293701, by rfl⟩ : syracuseStep 1724935 = 2587403) B2587403
theorem B8803313 : Blo 451781 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B1725695 : Blo 451781 1725695 := bstep (se 1 (by rfl) ⟨1294271, by rfl⟩ : syracuseStep 1725695 = 2588543) B2588543
theorem B23025329 : Blo 451781 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B1726379 : Blo 451781 1726379 := bstep (se 1 (by rfl) ⟨1294784, by rfl⟩ : syracuseStep 1726379 = 2589569) B2589569
theorem B677999 : Blo 451781 677999 := bstep (se 1 (by rfl) ⟨508499, by rfl⟩ : syracuseStep 677999 = 1016999) B1016999
theorem B8247587 : Blo 451781 8247587 := bstep (se 1 (by rfl) ⟨6185690, by rfl⟩ : syracuseStep 8247587 = 12371381) B12371381
theorem B678455 : Blo 451781 678455 := bstep (se 1 (by rfl) ⟨508841, by rfl⟩ : syracuseStep 678455 = 1017683) B1017683
theorem B678491 : Blo 451781 678491 := bstep (se 1 (by rfl) ⟨508868, by rfl⟩ : syracuseStep 678491 = 1017737) B1017737
theorem B49601159 : Blo 451781 49601159 := bstep (se 1 (by rfl) ⟨37200869, by rfl⟩ : syracuseStep 49601159 = 74401739) B74401739
theorem B2579111 : Blo 451781 2579111 := bstep (se 1 (by rfl) ⟨1934333, by rfl⟩ : syracuseStep 2579111 = 3868667) B3868667
theorem B4152259 : Blo 451781 4152259 := bstep (se 1 (by rfl) ⟨3114194, by rfl⟩ : syracuseStep 4152259 = 6228389) B6228389
theorem B2907343 : Blo 451781 2907343 := bstep (se 1 (by rfl) ⟨2180507, by rfl⟩ : syracuseStep 2907343 = 4361015) B4361015
theorem B679403 : Blo 451781 679403 := bstep (se 1 (by rfl) ⟨509552, by rfl⟩ : syracuseStep 679403 = 1019105) B1019105
theorem B1105435 : Blo 451781 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B1531547 : Blo 451781 1531547 := bstep (se 1 (by rfl) ⟨1148660, by rfl⟩ : syracuseStep 1531547 = 2297321) B2297321
theorem B16539551 : Blo 451781 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B680111 : Blo 451781 680111 := bstep (se 1 (by rfl) ⟨510083, by rfl⟩ : syracuseStep 680111 = 1020167) B1020167
theorem B93413573 : Blo 451781 93413573 := bstep (se 4 (by rfl) ⟨8757522, by rfl⟩ : syracuseStep 93413573 = 17515045) B17515045
theorem B680351 : Blo 451781 680351 := bstep (se 1 (by rfl) ⟨510263, by rfl⟩ : syracuseStep 680351 = 1020527) B1020527
theorem B680585 : Blo 451781 680585 := bstep (se 2 (by rfl) ⟨255219, by rfl⟩ : syracuseStep 680585 = 510439) B510439
theorem B3433103 : Blo 451781 3433103 := bstep (se 1 (by rfl) ⟨2574827, by rfl⟩ : syracuseStep 3433103 = 5149655) B5149655
theorem B1532573 : Blo 451781 1532573 := bstep (se 3 (by rfl) ⟨287357, by rfl⟩ : syracuseStep 1532573 = 574715) B574715
theorem B680807 : Blo 451781 680807 := bstep (se 1 (by rfl) ⟨510605, by rfl⟩ : syracuseStep 680807 = 1021211) B1021211
theorem B1532843 : Blo 451781 1532843 := bstep (se 1 (by rfl) ⟨1149632, by rfl⟩ : syracuseStep 1532843 = 2299265) B2299265
theorem B451867 : Blo 451781 451867 := bstep (se 1 (by rfl) ⟨338900, by rfl⟩ : syracuseStep 451867 = 677801) B677801
theorem B452047 : Blo 451781 452047 := bstep (se 1 (by rfl) ⟨339035, by rfl⟩ : syracuseStep 452047 = 678071) B678071
theorem B681599 : Blo 451781 681599 := bstep (se 1 (by rfl) ⟨511199, by rfl⟩ : syracuseStep 681599 = 1022399) B1022399
theorem B1730281 : Blo 451781 1730281 := bstep (se 2 (by rfl) ⟨648855, by rfl⟩ : syracuseStep 1730281 = 1297711) B1297711
theorem B682055 : Blo 451781 682055 := bstep (se 1 (by rfl) ⟨511541, by rfl⟩ : syracuseStep 682055 = 1023083) B1023083
theorem B452815 : Blo 451781 452815 := bstep (se 1 (by rfl) ⟨339611, by rfl⟩ : syracuseStep 452815 = 679223) B679223
theorem B453019 : Blo 451781 453019 := bstep (se 1 (by rfl) ⟨339764, by rfl⟩ : syracuseStep 453019 = 679529) B679529
theorem B453287 : Blo 451781 453287 := bstep (se 1 (by rfl) ⟨339965, by rfl⟩ : syracuseStep 453287 = 679931) B679931
theorem B682751 : Blo 451781 682751 := bstep (se 1 (by rfl) ⟨512063, by rfl⟩ : syracuseStep 682751 = 1024127) B1024127
theorem B682985 : Blo 451781 682985 := bstep (se 2 (by rfl) ⟨256119, by rfl⟩ : syracuseStep 682985 = 512239) B512239
theorem B2583737 : Blo 451781 2583737 := bstep (se 2 (by rfl) ⟨968901, by rfl⟩ : syracuseStep 2583737 = 1937803) B1937803
theorem B454299 : Blo 451781 454299 := bstep (se 1 (by rfl) ⟨340724, by rfl⟩ : syracuseStep 454299 = 681449) B681449
theorem B1536299 : Blo 451781 1536299 := bstep (se 1 (by rfl) ⟨1152224, by rfl⟩ : syracuseStep 1536299 = 2304449) B2304449
theorem B455103 : Blo 451781 455103 := bstep (se 1 (by rfl) ⟨341327, by rfl⟩ : syracuseStep 455103 = 682655) B682655
theorem B1536569 : Blo 451781 1536569 := bstep (se 2 (by rfl) ⟨576213, by rfl⟩ : syracuseStep 1536569 = 1152427) B1152427
theorem B1536839 : Blo 451781 1536839 := bstep (se 1 (by rfl) ⟨1152629, by rfl⟩ : syracuseStep 1536839 = 2305259) B2305259
theorem B455615 : Blo 451781 455615 := bstep (se 1 (by rfl) ⟨341711, by rfl⟩ : syracuseStep 455615 = 683423) B683423
theorem B2946079 : Blo 451781 2946079 := bstep (se 1 (by rfl) ⟨2209559, by rfl⟩ : syracuseStep 2946079 = 4419119) B4419119
theorem B5797007 : Blo 451781 5797007 := bstep (se 1 (by rfl) ⟨4347755, by rfl⟩ : syracuseStep 5797007 = 8695511) B8695511
theorem B3667151 : Blo 451781 3667151 := bstep (se 1 (by rfl) ⟨2750363, by rfl⟩ : syracuseStep 3667151 = 5500727) B5500727
theorem B2620471 : Blo 451781 2620471 := bstep (se 1 (by rfl) ⟨1965353, by rfl⟩ : syracuseStep 2620471 = 3930707) B3930707
theorem B1638265 : Blo 451781 1638265 := bstep (se 2 (by rfl) ⟨614349, by rfl⟩ : syracuseStep 1638265 = 1228699) B1228699
theorem B1017143 : Blo 451781 1017143 := bstep (se 1 (by rfl) ⟨762857, by rfl⟩ : syracuseStep 1017143 = 1525715) B1525715
theorem B5834369 : Blo 451781 5834369 := bstep (se 2 (by rfl) ⟨2187888, by rfl⟩ : syracuseStep 5834369 = 4375777) B4375777
theorem B1149167 : Blo 451781 1149167 := bstep (se 1 (by rfl) ⟨861875, by rfl⟩ : syracuseStep 1149167 = 1723751) B1723751
theorem B19925347 : Blo 451781 19925347 := bstep (se 1 (by rfl) ⟨14944010, by rfl⟩ : syracuseStep 19925347 = 29888021) B29888021
theorem B5245793 : Blo 451781 5245793 := bstep (se 2 (by rfl) ⟨1967172, by rfl⟩ : syracuseStep 5245793 = 3934345) B3934345
theorem B1018727 : Blo 451781 1018727 := bstep (se 1 (by rfl) ⟨764045, by rfl⟩ : syracuseStep 1018727 = 1528091) B1528091
theorem B3935141 : Blo 451781 3935141 := bstep (se 4 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 3935141 = 737839) B737839
theorem B4918427 : Blo 451781 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B5868875 : Blo 451781 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B1150463 : Blo 451781 1150463 := bstep (se 1 (by rfl) ⟨862847, by rfl⟩ : syracuseStep 1150463 = 1725695) B1725695
theorem B1150919 : Blo 451781 1150919 := bstep (se 1 (by rfl) ⟨863189, by rfl⟩ : syracuseStep 1150919 = 1726379) B1726379
theorem B33067439 : Blo 451781 33067439 := bstep (se 1 (by rfl) ⟨24800579, by rfl⟩ : syracuseStep 33067439 = 49601159) B49601159
theorem B1021031 : Blo 451781 1021031 := bstep (se 1 (by rfl) ⟨765773, by rfl⟩ : syracuseStep 1021031 = 1531547) B1531547
theorem B1021715 : Blo 451781 1021715 := bstep (se 1 (by rfl) ⟨766286, by rfl⟩ : syracuseStep 1021715 = 1532573) B1532573
theorem B1021895 : Blo 451781 1021895 := bstep (se 1 (by rfl) ⟨766421, by rfl⟩ : syracuseStep 1021895 = 1532843) B1532843
theorem B2299913 : Blo 451781 2299913 := bstep (se 2 (by rfl) ⟨862467, by rfl⟩ : syracuseStep 2299913 = 1724935) B1724935
theorem B21993565 : Blo 451781 21993565 := bstep (se 3 (by rfl) ⟨4123793, by rfl⟩ : syracuseStep 21993565 = 8247587) B8247587
theorem B7346375 : Blo 451781 7346375 := bstep (se 1 (by rfl) ⟨5509781, by rfl⟩ : syracuseStep 7346375 = 11019563) B11019563
theorem B3447197 : Blo 451781 3447197 := bstep (se 3 (by rfl) ⟨646349, by rfl⟩ : syracuseStep 3447197 = 1292699) B1292699
theorem B11639213 : Blo 451781 11639213 := bstep (se 3 (by rfl) ⟨2182352, by rfl⟩ : syracuseStep 11639213 = 4364705) B4364705
theorem B7772597 : Blo 451781 7772597 := bstep (se 5 (by rfl) ⟨364340, by rfl⟩ : syracuseStep 7772597 = 728681) B728681
theorem B1842047 : Blo 451781 1842047 := bstep (se 1 (by rfl) ⟨1381535, by rfl⟩ : syracuseStep 1842047 = 2763071) B2763071
theorem B1024199 : Blo 451781 1024199 := bstep (se 1 (by rfl) ⟨768149, by rfl⟩ : syracuseStep 1024199 = 1536299) B1536299
theorem B1024379 : Blo 451781 1024379 := bstep (se 1 (by rfl) ⟨768284, by rfl⟩ : syracuseStep 1024379 = 1536569) B1536569
theorem B1024559 : Blo 451781 1024559 := bstep (se 1 (by rfl) ⟨768419, by rfl⟩ : syracuseStep 1024559 = 1536839) B1536839
theorem B1024937 : Blo 451781 1024937 := bstep (se 2 (by rfl) ⟨384351, by rfl⟩ : syracuseStep 1024937 = 768703) B768703
theorem B3876457 : Blo 451781 3876457 := bstep (se 2 (by rfl) ⟨1453671, by rfl⟩ : syracuseStep 3876457 = 2907343) B2907343
theorem B8301305 : Blo 451781 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B1093139 : Blo 451781 1093139 := bstep (se 1 (by rfl) ⟨819854, by rfl⟩ : syracuseStep 1093139 = 1639709) B1639709
theorem B2305583 : Blo 451781 2305583 := bstep (se 1 (by rfl) ⟨1729187, by rfl⟩ : syracuseStep 2305583 = 3458375) B3458375
theorem B1290593 : Blo 451781 1290593 := bstep (se 2 (by rfl) ⟨483972, by rfl⟩ : syracuseStep 1290593 = 967945) B967945
theorem B6205835 : Blo 451781 6205835 := bstep (se 1 (by rfl) ⟨4654376, by rfl⟩ : syracuseStep 6205835 = 9308753) B9308753
theorem B1290991 : Blo 451781 1290991 := bstep (se 1 (by rfl) ⟨968243, by rfl⟩ : syracuseStep 1290991 = 1936487) B1936487
theorem B2307041 : Blo 451781 2307041 := bstep (se 2 (by rfl) ⟨865140, by rfl⟩ : syracuseStep 2307041 = 1730281) B1730281
theorem B9779069 : Blo 451781 9779069 := bstep (se 3 (by rfl) ⟨1833575, by rfl⟩ : syracuseStep 9779069 = 3667151) B3667151
theorem B3586193 : Blo 451781 3586193 := bstep (se 2 (by rfl) ⟨1344822, by rfl⟩ : syracuseStep 3586193 = 2689645) B2689645
theorem B768251 : Blo 451781 768251 := bstep (se 1 (by rfl) ⟨576188, by rfl⟩ : syracuseStep 768251 = 1152377) B1152377
theorem B15350219 : Blo 451781 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B1719407 : Blo 451781 1719407 := bstep (se 1 (by rfl) ⟨1289555, by rfl⟩ : syracuseStep 1719407 = 2579111) B2579111
theorem B35274329 : Blo 451781 35274329 := bstep (se 2 (by rfl) ⟨13227873, by rfl⟩ : syracuseStep 35274329 = 26455747) B26455747
theorem B11026367 : Blo 451781 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B62275715 : Blo 451781 62275715 := bstep (se 1 (by rfl) ⟨46706786, by rfl⟩ : syracuseStep 62275715 = 93413573) B93413573
theorem B11780777 : Blo 451781 11780777 := bstep (se 2 (by rfl) ⟨4417791, by rfl⟩ : syracuseStep 11780777 = 8835583) B8835583
theorem B509179 : Blo 451781 509179 := bstep (se 1 (by rfl) ⟨381884, by rfl⟩ : syracuseStep 509179 = 763769) B763769
theorem B1722491 : Blo 451781 1722491 := bstep (se 1 (by rfl) ⟨1291868, by rfl⟩ : syracuseStep 1722491 = 2583737) B2583737
theorem B1722505 : Blo 451781 1722505 := bstep (se 2 (by rfl) ⟨645939, by rfl⟩ : syracuseStep 1722505 = 1291879) B1291879
theorem B3493961 : Blo 451781 3493961 := bstep (se 2 (by rfl) ⟨1310235, by rfl⟩ : syracuseStep 3493961 = 2620471) B2620471
theorem B2184353 : Blo 451781 2184353 := bstep (se 2 (by rfl) ⟨819132, by rfl⟩ : syracuseStep 2184353 = 1638265) B1638265
theorem B94033345 : Blo 451781 94033345 := bstep (se 2 (by rfl) ⟨35262504, by rfl⟩ : syracuseStep 94033345 = 70525009) B70525009
theorem B13064591 : Blo 451781 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B3890537 : Blo 451781 3890537 := bstep (se 2 (by rfl) ⟨1458951, by rfl⟩ : syracuseStep 3890537 = 2917903) B2917903
theorem B3432131 : Blo 451781 3432131 := bstep (se 1 (by rfl) ⟨2574098, by rfl⟩ : syracuseStep 3432131 = 5148197) B5148197
theorem B483823 : Blo 451781 483823 := bstep (se 1 (by rfl) ⟨362867, by rfl⟩ : syracuseStep 483823 = 725735) B725735
theorem B1532519 : Blo 451781 1532519 := bstep (se 1 (by rfl) ⟨1149389, by rfl⟩ : syracuseStep 1532519 = 2298779) B2298779
theorem B680699 : Blo 451781 680699 := bstep (se 1 (by rfl) ⟨510524, by rfl⟩ : syracuseStep 680699 = 1021049) B1021049
theorem B1533167 : Blo 451781 1533167 := bstep (se 1 (by rfl) ⟨1149875, by rfl⟩ : syracuseStep 1533167 = 2299751) B2299751
theorem B8840573 : Blo 451781 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B451999 : Blo 451781 451999 := bstep (se 1 (by rfl) ⟨338999, by rfl⟩ : syracuseStep 451999 = 677999) B677999
theorem B11626091 : Blo 451781 11626091 := bstep (se 1 (by rfl) ⟨8719568, by rfl⟩ : syracuseStep 11626091 = 17439137) B17439137
theorem B452303 : Blo 451781 452303 := bstep (se 1 (by rfl) ⟨339227, by rfl⟩ : syracuseStep 452303 = 678455) B678455
theorem B452327 : Blo 451781 452327 := bstep (se 1 (by rfl) ⟨339245, by rfl⟩ : syracuseStep 452327 = 678491) B678491
theorem B452935 : Blo 451781 452935 := bstep (se 1 (by rfl) ⟨339701, by rfl⟩ : syracuseStep 452935 = 679403) B679403
theorem B682361 : Blo 451781 682361 := bstep (se 2 (by rfl) ⟨255885, by rfl⟩ : syracuseStep 682361 = 511771) B511771
theorem B453407 : Blo 451781 453407 := bstep (se 1 (by rfl) ⟨340055, by rfl⟩ : syracuseStep 453407 = 680111) B680111
theorem B453567 : Blo 451781 453567 := bstep (se 1 (by rfl) ⟨340175, by rfl⟩ : syracuseStep 453567 = 680351) B680351
theorem B682991 : Blo 451781 682991 := bstep (se 1 (by rfl) ⟨512243, by rfl⟩ : syracuseStep 682991 = 1024487) B1024487
theorem B453723 : Blo 451781 453723 := bstep (se 1 (by rfl) ⟨340292, by rfl⟩ : syracuseStep 453723 = 680585) B680585
theorem B2288735 : Blo 451781 2288735 := bstep (se 1 (by rfl) ⟨1716551, by rfl⟩ : syracuseStep 2288735 = 3433103) B3433103
theorem B453871 : Blo 451781 453871 := bstep (se 1 (by rfl) ⟨340403, by rfl⟩ : syracuseStep 453871 = 680807) B680807
theorem B454399 : Blo 451781 454399 := bstep (se 1 (by rfl) ⟨340799, by rfl⟩ : syracuseStep 454399 = 681599) B681599
theorem B3928105 : Blo 451781 3928105 := bstep (se 2 (by rfl) ⟨1473039, by rfl⟩ : syracuseStep 3928105 = 2946079) B2946079
theorem B454703 : Blo 451781 454703 := bstep (se 1 (by rfl) ⟨341027, by rfl⟩ : syracuseStep 454703 = 682055) B682055
theorem B455167 : Blo 451781 455167 := bstep (se 1 (by rfl) ⟨341375, by rfl⟩ : syracuseStep 455167 = 682751) B682751
theorem B455323 : Blo 451781 455323 := bstep (se 1 (by rfl) ⟨341492, by rfl⟩ : syracuseStep 455323 = 682985) B682985
theorem B25130087 : Blo 451781 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B1537487 : Blo 451781 1537487 := bstep (se 1 (by rfl) ⟨1153115, by rfl⟩ : syracuseStep 1537487 = 2306231) B2306231
theorem B6518231 : Blo 451781 6518231 := bstep (se 1 (by rfl) ⟨4888673, by rfl⟩ : syracuseStep 6518231 = 9777347) B9777347
theorem B3503969 : Blo 451781 3503969 := bstep (se 2 (by rfl) ⟨1313988, by rfl⟩ : syracuseStep 3503969 = 2627977) B2627977
theorem B3864671 : Blo 451781 3864671 := bstep (se 1 (by rfl) ⟨2898503, by rfl⟩ : syracuseStep 3864671 = 5797007) B5797007
theorem B5536345 : Blo 451781 5536345 := bstep (se 2 (by rfl) ⟨2076129, by rfl⟩ : syracuseStep 5536345 = 4152259) B4152259
theorem B1473913 : Blo 451781 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B41517143 : Blo 451781 41517143 := bstep (se 1 (by rfl) ⟨31137857, by rfl⟩ : syracuseStep 41517143 = 62275715) B62275715
theorem B16548893 : Blo 451781 16548893 := bstep (se 3 (by rfl) ⟨3102917, by rfl⟩ : syracuseStep 16548893 = 6205835) B6205835
theorem B1148327 : Blo 451781 1148327 := bstep (se 1 (by rfl) ⟨861245, by rfl⟩ : syracuseStep 1148327 = 1722491) B1722491
theorem B2623427 : Blo 451781 2623427 := bstep (se 1 (by rfl) ⟨1967570, by rfl⟩ : syracuseStep 2623427 = 3935141) B3935141
theorem B3278951 : Blo 451781 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B2329307 : Blo 451781 2329307 := bstep (se 1 (by rfl) ⟨1746980, by rfl⟩ : syracuseStep 2329307 = 3493961) B3493961
theorem B2296673 : Blo 451781 2296673 := bstep (se 2 (by rfl) ⟨861252, by rfl⟩ : syracuseStep 2296673 = 1722505) B1722505
theorem B2298131 : Blo 451781 2298131 := bstep (se 1 (by rfl) ⟨1723598, by rfl⟩ : syracuseStep 2298131 = 3447197) B3447197
theorem B5181731 : Blo 451781 5181731 := bstep (se 1 (by rfl) ⟨3886298, by rfl⟩ : syracuseStep 5181731 = 7772597) B7772597
theorem B2593691 : Blo 451781 2593691 := bstep (se 1 (by rfl) ⟨1945268, by rfl⟩ : syracuseStep 2593691 = 3890537) B3890537
theorem B1021679 : Blo 451781 1021679 := bstep (se 1 (by rfl) ⟨766259, by rfl⟩ : syracuseStep 1021679 = 1532519) B1532519
theorem B1022111 : Blo 451781 1022111 := bstep (se 1 (by rfl) ⟨766583, by rfl⟩ : syracuseStep 1022111 = 1533167) B1533167
theorem B125377793 : Blo 451781 125377793 := bstep (se 2 (by rfl) ⟨47016672, by rfl⟩ : syracuseStep 125377793 = 94033345) B94033345
theorem B728759 : Blo 451781 728759 := bstep (se 1 (by rfl) ⟨546569, by rfl⟩ : syracuseStep 728759 = 1093139) B1093139
theorem B860395 : Blo 451781 860395 := bstep (se 1 (by rfl) ⟨645296, by rfl⟩ : syracuseStep 860395 = 1290593) B1290593
theorem B16753391 : Blo 451781 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B7381793 : Blo 451781 7381793 := bstep (se 2 (by rfl) ⟨2768172, by rfl⟩ : syracuseStep 7381793 = 5536345) B5536345
theorem B1024991 : Blo 451781 1024991 := bstep (se 1 (by rfl) ⟨768743, by rfl⟩ : syracuseStep 1024991 = 1537487) B1537487
theorem B2335979 : Blo 451781 2335979 := bstep (se 1 (by rfl) ⟨1751984, by rfl⟩ : syracuseStep 2335979 = 3503969) B3503969
theorem B10233479 : Blo 451781 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B7350911 : Blo 451781 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B766111 : Blo 451781 766111 := bstep (se 1 (by rfl) ⟨574583, by rfl⟩ : syracuseStep 766111 = 1149167) B1149167
theorem B766975 : Blo 451781 766975 := bstep (se 1 (by rfl) ⟨575231, by rfl⟩ : syracuseStep 766975 = 1150463) B1150463
theorem B767279 : Blo 451781 767279 := bstep (se 1 (by rfl) ⟨575459, by rfl⟩ : syracuseStep 767279 = 1150919) B1150919
theorem B1456235 : Blo 451781 1456235 := bstep (se 1 (by rfl) ⟨1092176, by rfl⟩ : syracuseStep 1456235 = 2184353) B2184353
theorem B4897583 : Blo 451781 4897583 := bstep (se 1 (by rfl) ⟨3673187, by rfl⟩ : syracuseStep 4897583 = 7346375) B7346375
theorem B1228031 : Blo 451781 1228031 := bstep (se 1 (by rfl) ⟨921023, by rfl⟩ : syracuseStep 1228031 = 1842047) B1842047
theorem B1721321 : Blo 451781 1721321 := bstep (se 2 (by rfl) ⟨645495, by rfl⟩ : syracuseStep 1721321 = 1290991) B1290991
theorem B7750727 : Blo 451781 7750727 := bstep (se 1 (by rfl) ⟨5813045, by rfl⟩ : syracuseStep 7750727 = 11626091) B11626091
theorem B22136813 : Blo 451781 22136813 := bstep (se 3 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 22136813 = 8301305) B8301305
theorem B1525823 : Blo 451781 1525823 := bstep (se 1 (by rfl) ⟨1144367, by rfl⟩ : syracuseStep 1525823 = 2288735) B2288735
theorem B15650333 : Blo 451781 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B4345487 : Blo 451781 4345487 := bstep (se 1 (by rfl) ⟨3259115, by rfl⟩ : syracuseStep 4345487 = 6518231) B6518231
theorem B2576447 : Blo 451781 2576447 := bstep (se 1 (by rfl) ⟨1932335, by rfl⟩ : syracuseStep 2576447 = 3864671) B3864671
theorem B512167 : Blo 451781 512167 := bstep (se 1 (by rfl) ⟨384125, by rfl⟩ : syracuseStep 512167 = 768251) B768251
theorem B23516219 : Blo 451781 23516219 := bstep (se 1 (by rfl) ⟨17637164, by rfl⟩ : syracuseStep 23516219 = 35274329) B35274329
theorem B7853851 : Blo 451781 7853851 := bstep (se 1 (by rfl) ⟨5890388, by rfl⟩ : syracuseStep 7853851 = 11780777) B11780777
theorem B645097 : Blo 451781 645097 := bstep (se 2 (by rfl) ⟨241911, by rfl⟩ : syracuseStep 645097 = 483823) B483823
theorem B678095 : Blo 451781 678095 := bstep (se 1 (by rfl) ⟨508571, by rfl⟩ : syracuseStep 678095 = 1017143) B1017143
theorem B3889579 : Blo 451781 3889579 := bstep (se 1 (by rfl) ⟨2917184, by rfl⟩ : syracuseStep 3889579 = 5834369) B5834369
theorem B678905 : Blo 451781 678905 := bstep (se 2 (by rfl) ⟨254589, by rfl⟩ : syracuseStep 678905 = 509179) B509179
theorem B3497195 : Blo 451781 3497195 := bstep (se 1 (by rfl) ⟨2622896, by rfl⟩ : syracuseStep 3497195 = 5245793) B5245793
theorem B679151 : Blo 451781 679151 := bstep (se 1 (by rfl) ⟨509363, by rfl⟩ : syracuseStep 679151 = 1018727) B1018727
theorem B5168609 : Blo 451781 5168609 := bstep (se 2 (by rfl) ⟨1938228, by rfl⟩ : syracuseStep 5168609 = 3876457) B3876457
theorem B22044959 : Blo 451781 22044959 := bstep (se 1 (by rfl) ⟨16533719, by rfl⟩ : syracuseStep 22044959 = 33067439) B33067439
theorem B26567129 : Blo 451781 26567129 := bstep (se 2 (by rfl) ⟨9962673, by rfl⟩ : syracuseStep 26567129 = 19925347) B19925347
theorem B680687 : Blo 451781 680687 := bstep (se 1 (by rfl) ⟨510515, by rfl⟩ : syracuseStep 680687 = 1021031) B1021031
theorem B681143 : Blo 451781 681143 := bstep (se 1 (by rfl) ⟨510857, by rfl⟩ : syracuseStep 681143 = 1021715) B1021715
theorem B681263 : Blo 451781 681263 := bstep (se 1 (by rfl) ⟨510947, by rfl⟩ : syracuseStep 681263 = 1021895) B1021895
theorem B1533275 : Blo 451781 1533275 := bstep (se 1 (by rfl) ⟨1149956, by rfl⟩ : syracuseStep 1533275 = 2299913) B2299913
theorem B8709727 : Blo 451781 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B7759475 : Blo 451781 7759475 := bstep (se 1 (by rfl) ⟨5819606, by rfl⟩ : syracuseStep 7759475 = 11639213) B11639213
theorem B2288087 : Blo 451781 2288087 := bstep (se 1 (by rfl) ⟨1716065, by rfl⟩ : syracuseStep 2288087 = 3432131) B3432131
theorem B5237473 : Blo 451781 5237473 := bstep (se 2 (by rfl) ⟨1964052, by rfl⟩ : syracuseStep 5237473 = 3928105) B3928105
theorem B682799 : Blo 451781 682799 := bstep (se 1 (by rfl) ⟨512099, by rfl⟩ : syracuseStep 682799 = 1024199) B1024199
theorem B682919 : Blo 451781 682919 := bstep (se 1 (by rfl) ⟨512189, by rfl⟩ : syracuseStep 682919 = 1024379) B1024379
theorem B683039 : Blo 451781 683039 := bstep (se 1 (by rfl) ⟨512279, by rfl⟩ : syracuseStep 683039 = 1024559) B1024559
theorem B453799 : Blo 451781 453799 := bstep (se 1 (by rfl) ⟨340349, by rfl⟩ : syracuseStep 453799 = 680699) B680699
theorem B683291 : Blo 451781 683291 := bstep (se 1 (by rfl) ⟨512468, by rfl⟩ : syracuseStep 683291 = 1024937) B1024937
theorem B5893715 : Blo 451781 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B454907 : Blo 451781 454907 := bstep (se 1 (by rfl) ⟨341180, by rfl⟩ : syracuseStep 454907 = 682361) B682361
theorem B455327 : Blo 451781 455327 := bstep (se 1 (by rfl) ⟨341495, by rfl⟩ : syracuseStep 455327 = 682991) B682991
theorem B1537055 : Blo 451781 1537055 := bstep (se 1 (by rfl) ⟨1152791, by rfl⟩ : syracuseStep 1537055 = 2305583) B2305583
theorem B29324753 : Blo 451781 29324753 := bstep (se 2 (by rfl) ⟨10996782, by rfl⟩ : syracuseStep 29324753 = 21993565) B21993565
theorem B1538027 : Blo 451781 1538027 := bstep (se 1 (by rfl) ⟨1153520, by rfl⟩ : syracuseStep 1538027 = 2307041) B2307041
theorem B6519379 : Blo 451781 6519379 := bstep (se 1 (by rfl) ⟨4889534, by rfl⟩ : syracuseStep 6519379 = 9779069) B9779069
theorem B2390795 : Blo 451781 2390795 := bstep (se 1 (by rfl) ⟨1793096, by rfl⟩ : syracuseStep 2390795 = 3586193) B3586193
theorem B1965217 : Blo 451781 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B1146271 : Blo 451781 1146271 := bstep (se 1 (by rfl) ⟨859703, by rfl⟩ : syracuseStep 1146271 = 1719407) B1719407
theorem B1147193 : Blo 451781 1147193 := bstep (se 2 (by rfl) ⟨430197, by rfl⟩ : syracuseStep 1147193 = 860395) B860395
theorem B1147547 : Blo 451781 1147547 := bstep (se 1 (by rfl) ⟨860660, by rfl⟩ : syracuseStep 1147547 = 1721321) B1721321
theorem B1017215 : Blo 451781 1017215 := bstep (se 1 (by rfl) ⟨762911, by rfl⟩ : syracuseStep 1017215 = 1525823) B1525823
theorem B6983297 : Blo 451781 6983297 := bstep (se 2 (by rfl) ⟨2618736, by rfl⟩ : syracuseStep 6983297 = 5237473) B5237473
theorem B2331463 : Blo 451781 2331463 := bstep (se 1 (by rfl) ⟨1748597, by rfl⟩ : syracuseStep 2331463 = 3497195) B3497195
theorem B3445739 : Blo 451781 3445739 := bstep (se 1 (by rfl) ⟨2584304, by rfl⟩ : syracuseStep 3445739 = 5168609) B5168609
theorem B1021481 : Blo 451781 1021481 := bstep (se 2 (by rfl) ⟨383055, by rfl⟩ : syracuseStep 1021481 = 766111) B766111
theorem B4921195 : Blo 451781 4921195 := bstep (se 1 (by rfl) ⟨3690896, by rfl⟩ : syracuseStep 4921195 = 7381793) B7381793
theorem B1022183 : Blo 451781 1022183 := bstep (se 1 (by rfl) ⟨766637, by rfl⟩ : syracuseStep 1022183 = 1533275) B1533275
theorem B6822319 : Blo 451781 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B1022633 : Blo 451781 1022633 := bstep (se 2 (by rfl) ⟨383487, by rfl⟩ : syracuseStep 1022633 = 766975) B766975
theorem B860129 : Blo 451781 860129 := bstep (se 2 (by rfl) ⟨322548, by rfl⟩ : syracuseStep 860129 = 645097) B645097
theorem B5186105 : Blo 451781 5186105 := bstep (se 2 (by rfl) ⟨1944789, by rfl⟩ : syracuseStep 5186105 = 3889579) B3889579
theorem B1024703 : Blo 451781 1024703 := bstep (se 1 (by rfl) ⟨768527, by rfl⟩ : syracuseStep 1024703 = 1537055) B1537055
theorem B8692505 : Blo 451781 8692505 := bstep (se 2 (by rfl) ⟨3259689, by rfl⟩ : syracuseStep 8692505 = 6519379) B6519379
theorem B1025351 : Blo 451781 1025351 := bstep (se 1 (by rfl) ⟨769013, by rfl⟩ : syracuseStep 1025351 = 1538027) B1538027
theorem B765551 : Blo 451781 765551 := bstep (se 1 (by rfl) ⟨574163, by rfl⟩ : syracuseStep 765551 = 1148327) B1148327
theorem B1748951 : Blo 451781 1748951 := bstep (se 1 (by rfl) ⟨1311713, by rfl⟩ : syracuseStep 1748951 = 2623427) B2623427
theorem B14757875 : Blo 451781 14757875 := bstep (se 1 (by rfl) ⟨11068406, by rfl⟩ : syracuseStep 14757875 = 22136813) B22136813
theorem B1552871 : Blo 451781 1552871 := bstep (se 1 (by rfl) ⟨1164653, by rfl⟩ : syracuseStep 1552871 = 2329307) B2329307
theorem B11612969 : Blo 451781 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B10433555 : Blo 451781 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B2896991 : Blo 451781 2896991 := bstep (se 1 (by rfl) ⟨2172743, by rfl⟩ : syracuseStep 2896991 = 4345487) B4345487
theorem B1717631 : Blo 451781 1717631 := bstep (se 1 (by rfl) ⟨1288223, by rfl⟩ : syracuseStep 1717631 = 2576447) B2576447
theorem B3454487 : Blo 451781 3454487 := bstep (se 1 (by rfl) ⟨2590865, by rfl⟩ : syracuseStep 3454487 = 5181731) B5181731
theorem B15677479 : Blo 451781 15677479 := bstep (se 1 (by rfl) ⟨11758109, by rfl⟩ : syracuseStep 15677479 = 23516219) B23516219
theorem B14696639 : Blo 451781 14696639 := bstep (se 1 (by rfl) ⟨11022479, by rfl⟩ : syracuseStep 14696639 = 22044959) B22044959
theorem B17711419 : Blo 451781 17711419 := bstep (se 1 (by rfl) ⟨13283564, by rfl⟩ : syracuseStep 17711419 = 26567129) B26567129
theorem B1557319 : Blo 451781 1557319 := bstep (se 1 (by rfl) ⟨1167989, by rfl⟩ : syracuseStep 1557319 = 2335979) B2335979
theorem B1525391 : Blo 451781 1525391 := bstep (se 1 (by rfl) ⟨1144043, by rfl⟩ : syracuseStep 1525391 = 2288087) B2288087
theorem B4900607 : Blo 451781 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B10471801 : Blo 451781 10471801 := bstep (se 2 (by rfl) ⟨3926925, by rfl⟩ : syracuseStep 10471801 = 7853851) B7853851
theorem B511519 : Blo 451781 511519 := bstep (se 1 (by rfl) ⟨383639, by rfl⟩ : syracuseStep 511519 = 767279) B767279
theorem B19549835 : Blo 451781 19549835 := bstep (se 1 (by rfl) ⟨14662376, by rfl⟩ : syracuseStep 19549835 = 29324753) B29324753
theorem B970823 : Blo 451781 970823 := bstep (se 1 (by rfl) ⟨728117, by rfl⟩ : syracuseStep 970823 = 1456235) B1456235
theorem B1593863 : Blo 451781 1593863 := bstep (se 1 (by rfl) ⟨1195397, by rfl⟩ : syracuseStep 1593863 = 2390795) B2390795
theorem B3265055 : Blo 451781 3265055 := bstep (se 1 (by rfl) ⟨2448791, by rfl⟩ : syracuseStep 3265055 = 4897583) B4897583
theorem B1528361 : Blo 451781 1528361 := bstep (se 2 (by rfl) ⟨573135, by rfl⟩ : syracuseStep 1528361 = 1146271) B1146271
theorem B27678095 : Blo 451781 27678095 := bstep (se 1 (by rfl) ⟨20758571, by rfl⟩ : syracuseStep 27678095 = 41517143) B41517143
theorem B11032595 : Blo 451781 11032595 := bstep (se 1 (by rfl) ⟨8274446, by rfl⟩ : syracuseStep 11032595 = 16548893) B16548893
theorem B5167151 : Blo 451781 5167151 := bstep (se 1 (by rfl) ⟨3875363, by rfl⟩ : syracuseStep 5167151 = 7750727) B7750727
theorem B2185967 : Blo 451781 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B1531115 : Blo 451781 1531115 := bstep (se 1 (by rfl) ⟨1148336, by rfl⟩ : syracuseStep 1531115 = 2296673) B2296673
theorem B1532087 : Blo 451781 1532087 := bstep (se 1 (by rfl) ⟨1149065, by rfl⟩ : syracuseStep 1532087 = 2298131) B2298131
theorem B1729127 : Blo 451781 1729127 := bstep (se 1 (by rfl) ⟨1296845, by rfl⟩ : syracuseStep 1729127 = 2593691) B2593691
theorem B681119 : Blo 451781 681119 := bstep (se 1 (by rfl) ⟨510839, by rfl⟩ : syracuseStep 681119 = 1021679) B1021679
theorem B681407 : Blo 451781 681407 := bstep (se 1 (by rfl) ⟨511055, by rfl⟩ : syracuseStep 681407 = 1022111) B1022111
theorem B452063 : Blo 451781 452063 := bstep (se 1 (by rfl) ⟨339047, by rfl⟩ : syracuseStep 452063 = 678095) B678095
theorem B452603 : Blo 451781 452603 := bstep (se 1 (by rfl) ⟨339452, by rfl⟩ : syracuseStep 452603 = 678905) B678905
theorem B452767 : Blo 451781 452767 := bstep (se 1 (by rfl) ⟨339575, by rfl⟩ : syracuseStep 452767 = 679151) B679151
theorem B83585195 : Blo 451781 83585195 := bstep (se 1 (by rfl) ⟨62688896, by rfl⟩ : syracuseStep 83585195 = 125377793) B125377793
theorem B485839 : Blo 451781 485839 := bstep (se 1 (by rfl) ⟨364379, by rfl⟩ : syracuseStep 485839 = 728759) B728759
theorem B682889 : Blo 451781 682889 := bstep (se 2 (by rfl) ⟨256083, by rfl⟩ : syracuseStep 682889 = 512167) B512167
theorem B11168927 : Blo 451781 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B453791 : Blo 451781 453791 := bstep (se 1 (by rfl) ⟨340343, by rfl⟩ : syracuseStep 453791 = 680687) B680687
theorem B683327 : Blo 451781 683327 := bstep (se 1 (by rfl) ⟨512495, by rfl⟩ : syracuseStep 683327 = 1024991) B1024991
theorem B454095 : Blo 451781 454095 := bstep (se 1 (by rfl) ⟨340571, by rfl⟩ : syracuseStep 454095 = 681143) B681143
theorem B454175 : Blo 451781 454175 := bstep (se 1 (by rfl) ⟨340631, by rfl⟩ : syracuseStep 454175 = 681263) B681263
theorem B5172983 : Blo 451781 5172983 := bstep (se 1 (by rfl) ⟨3879737, by rfl⟩ : syracuseStep 5172983 = 7759475) B7759475
theorem B455199 : Blo 451781 455199 := bstep (se 1 (by rfl) ⟨341399, by rfl⟩ : syracuseStep 455199 = 682799) B682799
theorem B455279 : Blo 451781 455279 := bstep (se 1 (by rfl) ⟨341459, by rfl⟩ : syracuseStep 455279 = 682919) B682919
theorem B455359 : Blo 451781 455359 := bstep (se 1 (by rfl) ⟨341519, by rfl⟩ : syracuseStep 455359 = 683039) B683039
theorem B455527 : Blo 451781 455527 := bstep (se 1 (by rfl) ⟨341645, by rfl⟩ : syracuseStep 455527 = 683291) B683291
theorem B3929143 : Blo 451781 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B2620289 : Blo 451781 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B818687 : Blo 451781 818687 := bstep (se 1 (by rfl) ⟨614015, by rfl⟩ : syracuseStep 818687 = 1228031) B1228031
theorem B9797759 : Blo 451781 9797759 := bstep (se 1 (by rfl) ⟨7348319, by rfl⟩ : syracuseStep 9797759 = 14696639) B14696639
theorem B2588861 : Blo 451781 2588861 := bstep (se 3 (by rfl) ⟨485411, by rfl⟩ : syracuseStep 2588861 = 970823) B970823
theorem B1016927 : Blo 451781 1016927 := bstep (se 1 (by rfl) ⟨762695, by rfl⟩ : syracuseStep 1016927 = 1525391) B1525391
theorem B4655531 : Blo 451781 4655531 := bstep (se 1 (by rfl) ⟨3491648, by rfl⟩ : syracuseStep 4655531 = 6983297) B6983297
theorem B1018907 : Blo 451781 1018907 := bstep (se 1 (by rfl) ⟨764180, by rfl⟩ : syracuseStep 1018907 = 1528361) B1528361
theorem B13962401 : Blo 451781 13962401 := bstep (se 2 (by rfl) ⟨5235900, by rfl⟩ : syracuseStep 13962401 = 10471801) B10471801
theorem B2297159 : Blo 451781 2297159 := bstep (se 1 (by rfl) ⟨1722869, by rfl⟩ : syracuseStep 2297159 = 3445739) B3445739
theorem B18452063 : Blo 451781 18452063 := bstep (se 1 (by rfl) ⟨13839047, by rfl⟩ : syracuseStep 18452063 = 27678095) B27678095
theorem B3444767 : Blo 451781 3444767 := bstep (se 1 (by rfl) ⟨2583575, by rfl⟩ : syracuseStep 3444767 = 5167151) B5167151
theorem B1020743 : Blo 451781 1020743 := bstep (se 1 (by rfl) ⟨765557, by rfl⟩ : syracuseStep 1020743 = 1531115) B1531115
theorem B1021391 : Blo 451781 1021391 := bstep (se 1 (by rfl) ⟨766043, by rfl⟩ : syracuseStep 1021391 = 1532087) B1532087
theorem B1152751 : Blo 451781 1152751 := bstep (se 1 (by rfl) ⟨864563, by rfl⟩ : syracuseStep 1152751 = 1729127) B1729127
theorem B7445951 : Blo 451781 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B6561593 : Blo 451781 6561593 := bstep (se 2 (by rfl) ⟨2460597, by rfl⟩ : syracuseStep 6561593 = 4921195) B4921195
theorem B3448655 : Blo 451781 3448655 := bstep (se 1 (by rfl) ⟨2586491, by rfl⟩ : syracuseStep 3448655 = 5172983) B5172983
theorem B9838583 : Blo 451781 9838583 := bstep (se 1 (by rfl) ⟨7378937, by rfl⟩ : syracuseStep 9838583 = 14757875) B14757875
theorem B7741979 : Blo 451781 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B6955703 : Blo 451781 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B2302991 : Blo 451781 2302991 := bstep (se 1 (by rfl) ⟨1727243, by rfl⟩ : syracuseStep 2302991 = 3454487) B3454487
theorem B1746859 : Blo 451781 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B764795 : Blo 451781 764795 := bstep (se 1 (by rfl) ⟨573596, by rfl⟩ : syracuseStep 764795 = 1147193) B1147193
theorem B765031 : Blo 451781 765031 := bstep (se 1 (by rfl) ⟨573773, by rfl⟩ : syracuseStep 765031 = 1147547) B1147547
theorem B2076425 : Blo 451781 2076425 := bstep (se 2 (by rfl) ⟨778659, by rfl⟩ : syracuseStep 2076425 = 1557319) B1557319
theorem B1062575 : Blo 451781 1062575 := bstep (se 1 (by rfl) ⟨796931, by rfl⟩ : syracuseStep 1062575 = 1593863) B1593863
theorem B2176703 : Blo 451781 2176703 := bstep (se 1 (by rfl) ⟨1632527, by rfl⟩ : syracuseStep 2176703 = 3265055) B3265055
theorem B7355063 : Blo 451781 7355063 := bstep (se 1 (by rfl) ⟨5516297, by rfl⟩ : syracuseStep 7355063 = 11032595) B11032595
theorem B573419 : Blo 451781 573419 := bstep (se 1 (by rfl) ⟨430064, by rfl⟩ : syracuseStep 573419 = 860129) B860129
theorem B3457403 : Blo 451781 3457403 := bstep (se 1 (by rfl) ⟨2593052, by rfl⟩ : syracuseStep 3457403 = 5186105) B5186105
theorem B55723463 : Blo 451781 55723463 := bstep (se 1 (by rfl) ⟨41792597, by rfl⟩ : syracuseStep 55723463 = 83585195) B83585195
theorem B510367 : Blo 451781 510367 := bstep (se 1 (by rfl) ⟨382775, by rfl⟩ : syracuseStep 510367 = 765551) B765551
theorem B1165967 : Blo 451781 1165967 := bstep (se 1 (by rfl) ⟨874475, by rfl⟩ : syracuseStep 1165967 = 1748951) B1748951
theorem B1035247 : Blo 451781 1035247 := bstep (se 1 (by rfl) ⟨776435, by rfl⟩ : syracuseStep 1035247 = 1552871) B1552871
theorem B9096425 : Blo 451781 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B545791 : Blo 451781 545791 := bstep (se 1 (by rfl) ⟨409343, by rfl⟩ : syracuseStep 545791 = 818687) B818687
theorem B23615225 : Blo 451781 23615225 := bstep (se 2 (by rfl) ⟨8855709, by rfl⟩ : syracuseStep 23615225 = 17711419) B17711419
theorem B678143 : Blo 451781 678143 := bstep (se 1 (by rfl) ⟨508607, by rfl⟩ : syracuseStep 678143 = 1017215) B1017215
theorem B3267071 : Blo 451781 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B13033223 : Blo 451781 13033223 := bstep (se 1 (by rfl) ⟨9774917, by rfl⟩ : syracuseStep 13033223 = 19549835) B19549835
theorem B647785 : Blo 451781 647785 := bstep (se 2 (by rfl) ⟨242919, by rfl⟩ : syracuseStep 647785 = 485839) B485839
theorem B680987 : Blo 451781 680987 := bstep (se 1 (by rfl) ⟨510740, by rfl⟩ : syracuseStep 680987 = 1021481) B1021481
theorem B681455 : Blo 451781 681455 := bstep (se 1 (by rfl) ⟨511091, by rfl⟩ : syracuseStep 681455 = 1022183) B1022183
theorem B681755 : Blo 451781 681755 := bstep (se 1 (by rfl) ⟨511316, by rfl⟩ : syracuseStep 681755 = 1022633) B1022633
theorem B682025 : Blo 451781 682025 := bstep (se 2 (by rfl) ⟨255759, by rfl⟩ : syracuseStep 682025 = 511519) B511519
theorem B683135 : Blo 451781 683135 := bstep (se 1 (by rfl) ⟨512351, by rfl⟩ : syracuseStep 683135 = 1024703) B1024703
theorem B5795003 : Blo 451781 5795003 := bstep (se 1 (by rfl) ⟨4346252, by rfl⟩ : syracuseStep 5795003 = 8692505) B8692505
theorem B454079 : Blo 451781 454079 := bstep (se 1 (by rfl) ⟨340559, by rfl⟩ : syracuseStep 454079 = 681119) B681119
theorem B683567 : Blo 451781 683567 := bstep (se 1 (by rfl) ⟨512675, by rfl⟩ : syracuseStep 683567 = 1025351) B1025351
theorem B454271 : Blo 451781 454271 := bstep (se 1 (by rfl) ⟨340703, by rfl⟩ : syracuseStep 454271 = 681407) B681407
theorem B3108617 : Blo 451781 3108617 := bstep (se 2 (by rfl) ⟨1165731, by rfl⟩ : syracuseStep 3108617 = 2331463) B2331463
theorem B5238857 : Blo 451781 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B455259 : Blo 451781 455259 := bstep (se 1 (by rfl) ⟨341444, by rfl⟩ : syracuseStep 455259 = 682889) B682889
theorem B5829245 : Blo 451781 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B455551 : Blo 451781 455551 := bstep (se 1 (by rfl) ⟨341663, by rfl⟩ : syracuseStep 455551 = 683327) B683327
theorem B20903305 : Blo 451781 20903305 := bstep (se 2 (by rfl) ⟨7838739, by rfl⟩ : syracuseStep 20903305 = 15677479) B15677479
theorem B1931327 : Blo 451781 1931327 := bstep (se 1 (by rfl) ⟨1448495, by rfl⟩ : syracuseStep 1931327 = 2896991) B2896991
theorem B1145087 : Blo 451781 1145087 := bstep (se 1 (by rfl) ⟨858815, by rfl⟩ : syracuseStep 1145087 = 1717631) B1717631
theorem B9308267 : Blo 451781 9308267 := bstep (se 1 (by rfl) ⟨6981200, by rfl⟩ : syracuseStep 9308267 = 13962401) B13962401
theorem B6064283 : Blo 451781 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B2329145 : Blo 451781 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B2296511 : Blo 451781 2296511 := bstep (se 1 (by rfl) ⟨1722383, by rfl⟩ : syracuseStep 2296511 = 3444767) B3444767
theorem B1380329 : Blo 451781 1380329 := bstep (se 2 (by rfl) ⟨517623, by rfl⟩ : syracuseStep 1380329 = 1035247) B1035247
theorem B1020041 : Blo 451781 1020041 := bstep (se 2 (by rfl) ⟨382515, by rfl⟩ : syracuseStep 1020041 = 765031) B765031
theorem B8688815 : Blo 451781 8688815 := bstep (se 1 (by rfl) ⟨6516611, by rfl⟩ : syracuseStep 8688815 = 13033223) B13033223
theorem B2299103 : Blo 451781 2299103 := bstep (se 1 (by rfl) ⟨1724327, by rfl⟩ : syracuseStep 2299103 = 3448655) B3448655
theorem B6559055 : Blo 451781 6559055 := bstep (se 1 (by rfl) ⟨4919291, by rfl⟩ : syracuseStep 6559055 = 9838583) B9838583
theorem B727721 : Blo 451781 727721 := bstep (se 2 (by rfl) ⟨272895, by rfl⟩ : syracuseStep 727721 = 545791) B545791
theorem B2072411 : Blo 451781 2072411 := bstep (se 1 (by rfl) ⟨1554308, by rfl⟩ : syracuseStep 2072411 = 3108617) B3108617
theorem B1384283 : Blo 451781 1384283 := bstep (se 1 (by rfl) ⟨1038212, by rfl⟩ : syracuseStep 1384283 = 2076425) B2076425
theorem B1451135 : Blo 451781 1451135 := bstep (se 1 (by rfl) ⟨1088351, by rfl⟩ : syracuseStep 1451135 = 2176703) B2176703
theorem B1287551 : Blo 451781 1287551 := bstep (se 1 (by rfl) ⟨965663, by rfl⟩ : syracuseStep 1287551 = 1931327) B1931327
theorem B763391 : Blo 451781 763391 := bstep (se 1 (by rfl) ⟨572543, by rfl⟩ : syracuseStep 763391 = 1145087) B1145087
theorem B6531839 : Blo 451781 6531839 := bstep (se 1 (by rfl) ⟨4898879, by rfl⟩ : syracuseStep 6531839 = 9797759) B9797759
theorem B2304935 : Blo 451781 2304935 := bstep (se 1 (by rfl) ⟨1728701, by rfl⟩ : syracuseStep 2304935 = 3457403) B3457403
theorem B863713 : Blo 451781 863713 := bstep (se 2 (by rfl) ⟨323892, by rfl⟩ : syracuseStep 863713 = 647785) B647785
theorem B12301375 : Blo 451781 12301375 := bstep (se 1 (by rfl) ⟨9226031, by rfl⟩ : syracuseStep 12301375 = 18452063) B18452063
theorem B15743483 : Blo 451781 15743483 := bstep (se 1 (by rfl) ⟨11807612, by rfl⟩ : syracuseStep 15743483 = 23615225) B23615225
theorem B2178047 : Blo 451781 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B4963967 : Blo 451781 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B4374395 : Blo 451781 4374395 := bstep (se 1 (by rfl) ⟨3280796, by rfl⟩ : syracuseStep 4374395 = 6561593) B6561593
theorem B5161319 : Blo 451781 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B4637135 : Blo 451781 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B27871073 : Blo 451781 27871073 := bstep (se 2 (by rfl) ⟨10451652, by rfl⟩ : syracuseStep 27871073 = 20903305) B20903305
theorem B509863 : Blo 451781 509863 := bstep (se 1 (by rfl) ⟨382397, by rfl⟩ : syracuseStep 509863 = 764795) B764795
theorem B3492571 : Blo 451781 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B3886163 : Blo 451781 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B708383 : Blo 451781 708383 := bstep (se 1 (by rfl) ⟨531287, by rfl⟩ : syracuseStep 708383 = 1062575) B1062575
theorem B4903375 : Blo 451781 4903375 := bstep (se 1 (by rfl) ⟨3677531, by rfl⟩ : syracuseStep 4903375 = 7355063) B7355063
theorem B1529117 : Blo 451781 1529117 := bstep (se 3 (by rfl) ⟨286709, by rfl⟩ : syracuseStep 1529117 = 573419) B573419
theorem B1725907 : Blo 451781 1725907 := bstep (se 1 (by rfl) ⟨1294430, by rfl⟩ : syracuseStep 1725907 = 2588861) B2588861
theorem B677951 : Blo 451781 677951 := bstep (se 1 (by rfl) ⟨508463, by rfl⟩ : syracuseStep 677951 = 1016927) B1016927
theorem B37148975 : Blo 451781 37148975 := bstep (se 1 (by rfl) ⟨27861731, by rfl⟩ : syracuseStep 37148975 = 55723463) B55723463
theorem B3103687 : Blo 451781 3103687 := bstep (se 1 (by rfl) ⟨2327765, by rfl⟩ : syracuseStep 3103687 = 4655531) B4655531
theorem B777311 : Blo 451781 777311 := bstep (se 1 (by rfl) ⟨582983, by rfl⟩ : syracuseStep 777311 = 1165967) B1165967
theorem B679271 : Blo 451781 679271 := bstep (se 1 (by rfl) ⟨509453, by rfl⟩ : syracuseStep 679271 = 1018907) B1018907
theorem B1531439 : Blo 451781 1531439 := bstep (se 1 (by rfl) ⟨1148579, by rfl⟩ : syracuseStep 1531439 = 2297159) B2297159
theorem B680489 : Blo 451781 680489 := bstep (se 2 (by rfl) ⟨255183, by rfl⟩ : syracuseStep 680489 = 510367) B510367
theorem B680495 : Blo 451781 680495 := bstep (se 1 (by rfl) ⟨510371, by rfl⟩ : syracuseStep 680495 = 1020743) B1020743
theorem B680927 : Blo 451781 680927 := bstep (se 1 (by rfl) ⟨510695, by rfl⟩ : syracuseStep 680927 = 1021391) B1021391
theorem B452095 : Blo 451781 452095 := bstep (se 1 (by rfl) ⟨339071, by rfl⟩ : syracuseStep 452095 = 678143) B678143
theorem B1535327 : Blo 451781 1535327 := bstep (se 1 (by rfl) ⟨1151495, by rfl⟩ : syracuseStep 1535327 = 2302991) B2302991
theorem B453991 : Blo 451781 453991 := bstep (se 1 (by rfl) ⟨340493, by rfl⟩ : syracuseStep 453991 = 680987) B680987
theorem B454303 : Blo 451781 454303 := bstep (se 1 (by rfl) ⟨340727, by rfl⟩ : syracuseStep 454303 = 681455) B681455
theorem B454503 : Blo 451781 454503 := bstep (se 1 (by rfl) ⟨340877, by rfl⟩ : syracuseStep 454503 = 681755) B681755
theorem B454683 : Blo 451781 454683 := bstep (se 1 (by rfl) ⟨341012, by rfl⟩ : syracuseStep 454683 = 682025) B682025
theorem B455423 : Blo 451781 455423 := bstep (se 1 (by rfl) ⟨341567, by rfl⟩ : syracuseStep 455423 = 683135) B683135
theorem B3863335 : Blo 451781 3863335 := bstep (se 1 (by rfl) ⟨2897501, by rfl⟩ : syracuseStep 3863335 = 5795003) B5795003
theorem B1537001 : Blo 451781 1537001 := bstep (se 2 (by rfl) ⟨576375, by rfl⟩ : syracuseStep 1537001 = 1152751) B1152751
theorem B455711 : Blo 451781 455711 := bstep (se 1 (by rfl) ⟨341783, by rfl⟩ : syracuseStep 455711 = 683567) B683567
theorem B3440879 : Blo 451781 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B18580715 : Blo 451781 18580715 := bstep (se 1 (by rfl) ⟨13935536, by rfl⟩ : syracuseStep 18580715 = 27871073) B27871073
theorem B2590775 : Blo 451781 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B920219 : Blo 451781 920219 := bstep (se 1 (by rfl) ⟨690164, by rfl⟩ : syracuseStep 920219 = 1380329) B1380329
theorem B3869693 : Blo 451781 3869693 := bstep (se 3 (by rfl) ⟨725567, by rfl⟩ : syracuseStep 3869693 = 1451135) B1451135
theorem B1019411 : Blo 451781 1019411 := bstep (se 1 (by rfl) ⟨764558, by rfl⟩ : syracuseStep 1019411 = 1529117) B1529117
theorem B4656761 : Blo 451781 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B1151617 : Blo 451781 1151617 := bstep (se 2 (by rfl) ⟨431856, by rfl⟩ : syracuseStep 1151617 = 863713) B863713
theorem B1020959 : Blo 451781 1020959 := bstep (se 1 (by rfl) ⟨765719, by rfl⟩ : syracuseStep 1020959 = 1531439) B1531439
theorem B1381607 : Blo 451781 1381607 := bstep (se 1 (by rfl) ⟨1036205, by rfl⟩ : syracuseStep 1381607 = 2072411) B2072411
theorem B922855 : Blo 451781 922855 := bstep (se 1 (by rfl) ⟨692141, by rfl⟩ : syracuseStep 922855 = 1384283) B1384283
theorem B858367 : Blo 451781 858367 := bstep (se 1 (by rfl) ⟨643775, by rfl⟩ : syracuseStep 858367 = 1287551) B1287551
theorem B5151113 : Blo 451781 5151113 := bstep (se 2 (by rfl) ⟨1931667, by rfl⟩ : syracuseStep 5151113 = 3863335) B3863335
theorem B2301209 : Blo 451781 2301209 := bstep (se 2 (by rfl) ⟨862953, by rfl⟩ : syracuseStep 2301209 = 1725907) B1725907
theorem B1023551 : Blo 451781 1023551 := bstep (se 1 (by rfl) ⟨767663, by rfl⟩ : syracuseStep 1023551 = 1535327) B1535327
theorem B5808125 : Blo 451781 5808125 := bstep (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) B2178047
theorem B1024667 : Blo 451781 1024667 := bstep (se 1 (by rfl) ⟨768500, by rfl⟩ : syracuseStep 1024667 = 1537001) B1537001
theorem B4138249 : Blo 451781 4138249 := bstep (se 2 (by rfl) ⟨1551843, by rfl⟩ : syracuseStep 4138249 = 3103687) B3103687
theorem B10495655 : Blo 451781 10495655 := bstep (se 1 (by rfl) ⟨7871741, by rfl⟩ : syracuseStep 10495655 = 15743483) B15743483
theorem B12365693 : Blo 451781 12365693 := bstep (se 3 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 12365693 = 4637135) B4637135
theorem B6205511 : Blo 451781 6205511 := bstep (se 1 (by rfl) ⟨4654133, by rfl⟩ : syracuseStep 6205511 = 9308267) B9308267
theorem B4042855 : Blo 451781 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B1552763 : Blo 451781 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B472255 : Blo 451781 472255 := bstep (se 1 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 472255 = 708383) B708383
theorem B4372703 : Blo 451781 4372703 := bstep (se 1 (by rfl) ⟨3279527, by rfl⟩ : syracuseStep 4372703 = 6559055) B6559055
theorem B6537833 : Blo 451781 6537833 := bstep (se 2 (by rfl) ⟨2451687, by rfl⟩ : syracuseStep 6537833 = 4903375) B4903375
theorem B508927 : Blo 451781 508927 := bstep (se 1 (by rfl) ⟨381695, by rfl⟩ : syracuseStep 508927 = 763391) B763391
theorem B16401833 : Blo 451781 16401833 := bstep (se 2 (by rfl) ⟨6150687, by rfl⟩ : syracuseStep 16401833 = 12301375) B12301375
theorem B1531007 : Blo 451781 1531007 := bstep (se 1 (by rfl) ⟨1148255, by rfl⟩ : syracuseStep 1531007 = 2296511) B2296511
theorem B679817 : Blo 451781 679817 := bstep (se 2 (by rfl) ⟨254931, by rfl⟩ : syracuseStep 679817 = 509863) B509863
theorem B680027 : Blo 451781 680027 := bstep (se 1 (by rfl) ⟨510020, by rfl⟩ : syracuseStep 680027 = 1020041) B1020041
theorem B5792543 : Blo 451781 5792543 := bstep (se 1 (by rfl) ⟨4344407, by rfl⟩ : syracuseStep 5792543 = 8688815) B8688815
theorem B1532735 : Blo 451781 1532735 := bstep (se 1 (by rfl) ⟨1149551, by rfl⟩ : syracuseStep 1532735 = 2299103) B2299103
theorem B451967 : Blo 451781 451967 := bstep (se 1 (by rfl) ⟨338975, by rfl⟩ : syracuseStep 451967 = 677951) B677951
theorem B24765983 : Blo 451781 24765983 := bstep (se 1 (by rfl) ⟨18574487, by rfl⟩ : syracuseStep 24765983 = 37148975) B37148975
theorem B485147 : Blo 451781 485147 := bstep (se 1 (by rfl) ⟨363860, by rfl⟩ : syracuseStep 485147 = 727721) B727721
theorem B518207 : Blo 451781 518207 := bstep (se 1 (by rfl) ⟨388655, by rfl⟩ : syracuseStep 518207 = 777311) B777311
theorem B452847 : Blo 451781 452847 := bstep (se 1 (by rfl) ⟨339635, by rfl⟩ : syracuseStep 452847 = 679271) B679271
theorem B453659 : Blo 451781 453659 := bstep (se 1 (by rfl) ⟨340244, by rfl⟩ : syracuseStep 453659 = 680489) B680489
theorem B453663 : Blo 451781 453663 := bstep (se 1 (by rfl) ⟨340247, by rfl⟩ : syracuseStep 453663 = 680495) B680495
theorem B453951 : Blo 451781 453951 := bstep (se 1 (by rfl) ⟨340463, by rfl⟩ : syracuseStep 453951 = 680927) B680927
theorem B4354559 : Blo 451781 4354559 := bstep (se 1 (by rfl) ⟨3265919, by rfl⟩ : syracuseStep 4354559 = 6531839) B6531839
theorem B1536623 : Blo 451781 1536623 := bstep (se 1 (by rfl) ⟨1152467, by rfl⟩ : syracuseStep 1536623 = 2304935) B2304935
theorem B3309311 : Blo 451781 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B2916263 : Blo 451781 2916263 := bstep (se 1 (by rfl) ⟨2187197, by rfl⟩ : syracuseStep 2916263 = 4374395) B4374395
theorem B2293919 : Blo 451781 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B4358555 : Blo 451781 4358555 := bstep (se 1 (by rfl) ⟨3268916, by rfl⟩ : syracuseStep 4358555 = 6537833) B6537833
theorem B12387143 : Blo 451781 12387143 := bstep (se 1 (by rfl) ⟨9290357, by rfl⟩ : syracuseStep 12387143 = 18580715) B18580715
theorem B921071 : Blo 451781 921071 := bstep (se 1 (by rfl) ⟨690803, by rfl⟩ : syracuseStep 921071 = 1381607) B1381607
theorem B174952885 : Blo 451781 174952885 := bstep (se 5 (by rfl) ⟨8200916, by rfl⟩ : syracuseStep 174952885 = 16401833) B16401833
theorem B1020671 : Blo 451781 1020671 := bstep (se 1 (by rfl) ⟨765503, by rfl⟩ : syracuseStep 1020671 = 1531007) B1531007
theorem B3872083 : Blo 451781 3872083 := bstep (se 1 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 3872083 = 5808125) B5808125
theorem B1021823 : Blo 451781 1021823 := bstep (se 1 (by rfl) ⟨766367, by rfl⟩ : syracuseStep 1021823 = 1532735) B1532735
theorem B4137007 : Blo 451781 4137007 := bstep (se 1 (by rfl) ⟨3102755, by rfl⟩ : syracuseStep 4137007 = 6205511) B6205511
theorem B1024415 : Blo 451781 1024415 := bstep (se 1 (by rfl) ⟨768311, by rfl⟩ : syracuseStep 1024415 = 1536623) B1536623
theorem B2206207 : Blo 451781 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B1944175 : Blo 451781 1944175 := bstep (se 1 (by rfl) ⟨1458131, by rfl⟩ : syracuseStep 1944175 = 2916263) B2916263
theorem B5517665 : Blo 451781 5517665 := bstep (se 2 (by rfl) ⟨2069124, by rfl⟩ : syracuseStep 5517665 = 4138249) B4138249
theorem B10074773 : Blo 451781 10074773 := bstep (se 6 (by rfl) ⟨236127, by rfl⟩ : syracuseStep 10074773 = 472255) B472255
theorem B1293725 : Blo 451781 1293725 := bstep (se 3 (by rfl) ⟨242573, by rfl⟩ : syracuseStep 1293725 = 485147) B485147
theorem B5390473 : Blo 451781 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B6997103 : Blo 451781 6997103 := bstep (se 1 (by rfl) ⟨5247827, by rfl⟩ : syracuseStep 6997103 = 10495655) B10495655
theorem B1230473 : Blo 451781 1230473 := bstep (se 2 (by rfl) ⟨461427, by rfl⟩ : syracuseStep 1230473 = 922855) B922855
theorem B8243795 : Blo 451781 8243795 := bstep (se 1 (by rfl) ⟨6182846, by rfl⟩ : syracuseStep 8243795 = 12365693) B12365693
theorem B1035175 : Blo 451781 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B2903039 : Blo 451781 2903039 := bstep (se 1 (by rfl) ⟨2177279, by rfl⟩ : syracuseStep 2903039 = 4354559) B4354559
theorem B5527541 : Blo 451781 5527541 := bstep (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) B518207
theorem B678569 : Blo 451781 678569 := bstep (se 2 (by rfl) ⟨254463, by rfl⟩ : syracuseStep 678569 = 508927) B508927
theorem B1727183 : Blo 451781 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B2579795 : Blo 451781 2579795 := bstep (se 1 (by rfl) ⟨1934846, by rfl⟩ : syracuseStep 2579795 = 3869693) B3869693
theorem B679607 : Blo 451781 679607 := bstep (se 1 (by rfl) ⟨509705, by rfl⟩ : syracuseStep 679607 = 1019411) B1019411
theorem B3104507 : Blo 451781 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B680639 : Blo 451781 680639 := bstep (se 1 (by rfl) ⟨510479, by rfl⟩ : syracuseStep 680639 = 1020959) B1020959
theorem B3434075 : Blo 451781 3434075 := bstep (se 1 (by rfl) ⟨2575556, by rfl⟩ : syracuseStep 3434075 = 5151113) B5151113
theorem B1534139 : Blo 451781 1534139 := bstep (se 1 (by rfl) ⟨1150604, by rfl⟩ : syracuseStep 1534139 = 2301209) B2301209
theorem B682367 : Blo 451781 682367 := bstep (se 1 (by rfl) ⟨511775, by rfl⟩ : syracuseStep 682367 = 1023551) B1023551
theorem B453211 : Blo 451781 453211 := bstep (se 1 (by rfl) ⟨339908, by rfl⟩ : syracuseStep 453211 = 679817) B679817
theorem B453351 : Blo 451781 453351 := bstep (se 1 (by rfl) ⟨340013, by rfl⟩ : syracuseStep 453351 = 680027) B680027
theorem B683111 : Blo 451781 683111 := bstep (se 1 (by rfl) ⟨512333, by rfl⟩ : syracuseStep 683111 = 1024667) B1024667
theorem B3861695 : Blo 451781 3861695 := bstep (se 1 (by rfl) ⟨2896271, by rfl⟩ : syracuseStep 3861695 = 5792543) B5792543
theorem B1535489 : Blo 451781 1535489 := bstep (se 2 (by rfl) ⟨575808, by rfl⟩ : syracuseStep 1535489 = 1151617) B1151617
theorem B16510655 : Blo 451781 16510655 := bstep (se 1 (by rfl) ⟨12382991, by rfl⟩ : syracuseStep 16510655 = 24765983) B24765983
theorem B2453917 : Blo 451781 2453917 := bstep (se 3 (by rfl) ⟨460109, by rfl⟩ : syracuseStep 2453917 = 920219) B920219
theorem B1144489 : Blo 451781 1144489 := bstep (se 2 (by rfl) ⟨429183, by rfl⟩ : syracuseStep 1144489 = 858367) B858367
theorem B2915135 : Blo 451781 2915135 := bstep (se 1 (by rfl) ⟨2186351, by rfl⟩ : syracuseStep 2915135 = 4372703) B4372703
theorem B8258095 : Blo 451781 8258095 := bstep (se 1 (by rfl) ⟨6193571, by rfl⟩ : syracuseStep 8258095 = 12387143) B12387143
theorem B820315 : Blo 451781 820315 := bstep (se 1 (by rfl) ⟨615236, by rfl⟩ : syracuseStep 820315 = 1230473) B1230473
theorem B1935359 : Blo 451781 1935359 := bstep (se 1 (by rfl) ⟨1451519, by rfl⟩ : syracuseStep 1935359 = 2903039) B2903039
theorem B11766437 : Blo 451781 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B2592233 : Blo 451781 2592233 := bstep (se 2 (by rfl) ⟨972087, by rfl⟩ : syracuseStep 2592233 = 1944175) B1944175
theorem B1380233 : Blo 451781 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B1151455 : Blo 451781 1151455 := bstep (se 1 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 1151455 = 1727183) B1727183
theorem B1022759 : Blo 451781 1022759 := bstep (se 1 (by rfl) ⟨767069, by rfl⟩ : syracuseStep 1022759 = 1534139) B1534139
theorem B1023659 : Blo 451781 1023659 := bstep (se 1 (by rfl) ⟨767744, by rfl⟩ : syracuseStep 1023659 = 1535489) B1535489
theorem B3678443 : Blo 451781 3678443 := bstep (se 1 (by rfl) ⟨2758832, by rfl⟩ : syracuseStep 3678443 = 5517665) B5517665
theorem B1943423 : Blo 451781 1943423 := bstep (se 1 (by rfl) ⟨1457567, by rfl⟩ : syracuseStep 1943423 = 2915135) B2915135
theorem B862483 : Blo 451781 862483 := bstep (se 1 (by rfl) ⟨646862, by rfl⟩ : syracuseStep 862483 = 1293725) B1293725
theorem B5516009 : Blo 451781 5516009 := bstep (se 2 (by rfl) ⟨2068503, by rfl⟩ : syracuseStep 5516009 = 4137007) B4137007
theorem B7187297 : Blo 451781 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B4664735 : Blo 451781 4664735 := bstep (se 1 (by rfl) ⟨3498551, by rfl⟩ : syracuseStep 4664735 = 6997103) B6997103
theorem B3685027 : Blo 451781 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B1719863 : Blo 451781 1719863 := bstep (se 1 (by rfl) ⟨1289897, by rfl⟩ : syracuseStep 1719863 = 2579795) B2579795
theorem B5162777 : Blo 451781 5162777 := bstep (se 2 (by rfl) ⟨1936041, by rfl⟩ : syracuseStep 5162777 = 3872083) B3872083
theorem B2574463 : Blo 451781 2574463 := bstep (se 1 (by rfl) ⟨1930847, by rfl⟩ : syracuseStep 2574463 = 3861695) B3861695
theorem B1525985 : Blo 451781 1525985 := bstep (se 2 (by rfl) ⟨572244, by rfl⟩ : syracuseStep 1525985 = 1144489) B1144489
theorem B8278685 : Blo 451781 8278685 := bstep (se 3 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 8278685 = 3104507) B3104507
theorem B1529279 : Blo 451781 1529279 := bstep (se 1 (by rfl) ⟨1146959, by rfl⟩ : syracuseStep 1529279 = 2293919) B2293919
theorem B2905703 : Blo 451781 2905703 := bstep (se 1 (by rfl) ⟨2179277, by rfl⟩ : syracuseStep 2905703 = 4358555) B4358555
theorem B5495863 : Blo 451781 5495863 := bstep (se 1 (by rfl) ⟨4121897, by rfl⟩ : syracuseStep 5495863 = 8243795) B8243795
theorem B614047 : Blo 451781 614047 := bstep (se 1 (by rfl) ⟨460535, by rfl⟩ : syracuseStep 614047 = 921071) B921071
theorem B680447 : Blo 451781 680447 := bstep (se 1 (by rfl) ⟨510335, by rfl⟩ : syracuseStep 680447 = 1020671) B1020671
theorem B681215 : Blo 451781 681215 := bstep (se 1 (by rfl) ⟨510911, by rfl⟩ : syracuseStep 681215 = 1021823) B1021823
theorem B452379 : Blo 451781 452379 := bstep (se 1 (by rfl) ⟨339284, by rfl⟩ : syracuseStep 452379 = 678569) B678569
theorem B453071 : Blo 451781 453071 := bstep (se 1 (by rfl) ⟨339803, by rfl⟩ : syracuseStep 453071 = 679607) B679607
theorem B682943 : Blo 451781 682943 := bstep (se 1 (by rfl) ⟨512207, by rfl⟩ : syracuseStep 682943 = 1024415) B1024415
theorem B453759 : Blo 451781 453759 := bstep (se 1 (by rfl) ⟨340319, by rfl⟩ : syracuseStep 453759 = 680639) B680639
theorem B3271889 : Blo 451781 3271889 := bstep (se 2 (by rfl) ⟨1226958, by rfl⟩ : syracuseStep 3271889 = 2453917) B2453917
theorem B233270513 : Blo 451781 233270513 := bstep (se 2 (by rfl) ⟨87476442, by rfl⟩ : syracuseStep 233270513 = 174952885) B174952885
theorem B2289383 : Blo 451781 2289383 := bstep (se 1 (by rfl) ⟨1717037, by rfl⟩ : syracuseStep 2289383 = 3434075) B3434075
theorem B454911 : Blo 451781 454911 := bstep (se 1 (by rfl) ⟨341183, by rfl⟩ : syracuseStep 454911 = 682367) B682367
theorem B455407 : Blo 451781 455407 := bstep (se 1 (by rfl) ⟨341555, by rfl⟩ : syracuseStep 455407 = 683111) B683111
theorem B11007103 : Blo 451781 11007103 := bstep (se 1 (by rfl) ⟨8255327, by rfl⟩ : syracuseStep 11007103 = 16510655) B16510655
theorem B6716515 : Blo 451781 6716515 := bstep (se 1 (by rfl) ⟨5037386, by rfl⟩ : syracuseStep 6716515 = 10074773) B10074773
theorem B3441851 : Blo 451781 3441851 := bstep (se 1 (by rfl) ⟨2581388, by rfl⟩ : syracuseStep 3441851 = 5162777) B5162777
theorem B1017323 : Blo 451781 1017323 := bstep (se 1 (by rfl) ⟨762992, by rfl⟩ : syracuseStep 1017323 = 1525985) B1525985
theorem B920155 : Blo 451781 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B44043173 : Blo 451781 44043173 := bstep (se 4 (by rfl) ⟨4129047, by rfl⟩ : syracuseStep 44043173 = 8258095) B8258095
theorem B1149977 : Blo 451781 1149977 := bstep (se 2 (by rfl) ⟨431241, by rfl⟩ : syracuseStep 1149977 = 862483) B862483
theorem B1019519 : Blo 451781 1019519 := bstep (se 1 (by rfl) ⟨764639, by rfl⟩ : syracuseStep 1019519 = 1529279) B1529279
theorem B1937135 : Blo 451781 1937135 := bstep (se 1 (by rfl) ⟨1452851, by rfl⟩ : syracuseStep 1937135 = 2905703) B2905703
theorem B3677339 : Blo 451781 3677339 := bstep (se 1 (by rfl) ⟨2758004, by rfl⟩ : syracuseStep 3677339 = 5516009) B5516009
theorem B8955353 : Blo 451781 8955353 := bstep (se 2 (by rfl) ⟨3358257, by rfl⟩ : syracuseStep 8955353 = 6716515) B6716515
theorem B1290239 : Blo 451781 1290239 := bstep (se 1 (by rfl) ⟨967679, by rfl⟩ : syracuseStep 1290239 = 1935359) B1935359
theorem B1093753 : Blo 451781 1093753 := bstep (se 2 (by rfl) ⟨410157, by rfl⟩ : syracuseStep 1093753 = 820315) B820315
theorem B7844291 : Blo 451781 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B5519123 : Blo 451781 5519123 := bstep (se 1 (by rfl) ⟨4139342, by rfl⟩ : syracuseStep 5519123 = 8278685) B8278685
theorem B1295615 : Blo 451781 1295615 := bstep (se 1 (by rfl) ⟨971711, by rfl⟩ : syracuseStep 1295615 = 1943423) B1943423
theorem B2181259 : Blo 451781 2181259 := bstep (se 1 (by rfl) ⟨1635944, by rfl⟩ : syracuseStep 2181259 = 3271889) B3271889
theorem B1526255 : Blo 451781 1526255 := bstep (se 1 (by rfl) ⟨1144691, by rfl⟩ : syracuseStep 1526255 = 2289383) B2289383
theorem B76664501 : Blo 451781 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B7327817 : Blo 451781 7327817 := bstep (se 2 (by rfl) ⟨2747931, by rfl⟩ : syracuseStep 7327817 = 5495863) B5495863
theorem B1728155 : Blo 451781 1728155 := bstep (se 1 (by rfl) ⟨1296116, by rfl⟩ : syracuseStep 1728155 = 2592233) B2592233
theorem B3432617 : Blo 451781 3432617 := bstep (se 2 (by rfl) ⟨1287231, by rfl⟩ : syracuseStep 3432617 = 2574463) B2574463
theorem B681839 : Blo 451781 681839 := bstep (se 1 (by rfl) ⟨511379, by rfl⟩ : syracuseStep 681839 = 1022759) B1022759
theorem B682439 : Blo 451781 682439 := bstep (se 1 (by rfl) ⟨511829, by rfl⟩ : syracuseStep 682439 = 1023659) B1023659
theorem B2452295 : Blo 451781 2452295 := bstep (se 1 (by rfl) ⟨1839221, by rfl⟩ : syracuseStep 2452295 = 3678443) B3678443
theorem B453631 : Blo 451781 453631 := bstep (se 1 (by rfl) ⟨340223, by rfl⟩ : syracuseStep 453631 = 680447) B680447
theorem B1535273 : Blo 451781 1535273 := bstep (se 2 (by rfl) ⟨575727, by rfl⟩ : syracuseStep 1535273 = 1151455) B1151455
theorem B454143 : Blo 451781 454143 := bstep (se 1 (by rfl) ⟨340607, by rfl⟩ : syracuseStep 454143 = 681215) B681215
theorem B14676137 : Blo 451781 14676137 := bstep (se 2 (by rfl) ⟨5503551, by rfl⟩ : syracuseStep 14676137 = 11007103) B11007103
theorem B455295 : Blo 451781 455295 := bstep (se 1 (by rfl) ⟨341471, by rfl⟩ : syracuseStep 455295 = 682943) B682943
theorem B155513675 : Blo 451781 155513675 := bstep (se 1 (by rfl) ⟨116635256, by rfl⟩ : syracuseStep 155513675 = 233270513) B233270513
theorem B3109823 : Blo 451781 3109823 := bstep (se 1 (by rfl) ⟨2332367, by rfl⟩ : syracuseStep 3109823 = 4664735) B4664735
theorem B4913369 : Blo 451781 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B818729 : Blo 451781 818729 := bstep (se 2 (by rfl) ⟨307023, by rfl⟩ : syracuseStep 818729 = 614047) B614047
theorem B1146575 : Blo 451781 1146575 := bstep (se 1 (by rfl) ⟨859931, by rfl⟩ : syracuseStep 1146575 = 1719863) B1719863
theorem B2294567 : Blo 451781 2294567 := bstep (se 1 (by rfl) ⟨1720925, by rfl⟩ : syracuseStep 2294567 = 3441851) B3441851
theorem B1017503 : Blo 451781 1017503 := bstep (se 1 (by rfl) ⟨763127, by rfl⟩ : syracuseStep 1017503 = 1526255) B1526255
theorem B29362115 : Blo 451781 29362115 := bstep (se 1 (by rfl) ⟨22021586, by rfl⟩ : syracuseStep 29362115 = 44043173) B44043173
theorem B4885211 : Blo 451781 4885211 := bstep (se 1 (by rfl) ⟨3663908, by rfl⟩ : syracuseStep 4885211 = 7327817) B7327817
theorem B1152103 : Blo 451781 1152103 := bstep (se 1 (by rfl) ⟨864077, by rfl⟩ : syracuseStep 1152103 = 1728155) B1728155
theorem B5970235 : Blo 451781 5970235 := bstep (se 1 (by rfl) ⟨4477676, by rfl⟩ : syracuseStep 5970235 = 8955353) B8955353
theorem B1023515 : Blo 451781 1023515 := bstep (se 1 (by rfl) ⟨767636, by rfl⟩ : syracuseStep 1023515 = 1535273) B1535273
theorem B860159 : Blo 451781 860159 := bstep (se 1 (by rfl) ⟨645119, by rfl⟩ : syracuseStep 860159 = 1290239) B1290239
theorem B2073215 : Blo 451781 2073215 := bstep (se 1 (by rfl) ⟨1554911, by rfl⟩ : syracuseStep 2073215 = 3109823) B3109823
theorem B3679415 : Blo 451781 3679415 := bstep (se 1 (by rfl) ⟨2759561, by rfl⟩ : syracuseStep 3679415 = 5519123) B5519123
theorem B764383 : Blo 451781 764383 := bstep (se 1 (by rfl) ⟨573287, by rfl⟩ : syracuseStep 764383 = 1146575) B1146575
theorem B766651 : Blo 451781 766651 := bstep (se 1 (by rfl) ⟨574988, by rfl⟩ : syracuseStep 766651 = 1149977) B1149977
theorem B3454973 : Blo 451781 3454973 := bstep (se 3 (by rfl) ⟨647807, by rfl⟩ : syracuseStep 3454973 = 1295615) B1295615
theorem B1226873 : Blo 451781 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B1458337 : Blo 451781 1458337 := bstep (se 2 (by rfl) ⟨546876, by rfl⟩ : syracuseStep 1458337 = 1093753) B1093753
theorem B9784091 : Blo 451781 9784091 := bstep (se 1 (by rfl) ⟨7338068, by rfl⟩ : syracuseStep 9784091 = 14676137) B14676137
theorem B5229527 : Blo 451781 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B5165693 : Blo 451781 5165693 := bstep (se 3 (by rfl) ⟨968567, by rfl⟩ : syracuseStep 5165693 = 1937135) B1937135
theorem B545819 : Blo 451781 545819 := bstep (se 1 (by rfl) ⟨409364, by rfl⟩ : syracuseStep 545819 = 818729) B818729
theorem B678215 : Blo 451781 678215 := bstep (se 1 (by rfl) ⟨508661, by rfl⟩ : syracuseStep 678215 = 1017323) B1017323
theorem B679679 : Blo 451781 679679 := bstep (se 1 (by rfl) ⟨509759, by rfl⟩ : syracuseStep 679679 = 1019519) B1019519
theorem B51109667 : Blo 451781 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B2908345 : Blo 451781 2908345 := bstep (se 2 (by rfl) ⟨1090629, by rfl⟩ : syracuseStep 2908345 = 2181259) B2181259
theorem B2451559 : Blo 451781 2451559 := bstep (se 1 (by rfl) ⟨1838669, by rfl⟩ : syracuseStep 2451559 = 3677339) B3677339
theorem B2288411 : Blo 451781 2288411 := bstep (se 1 (by rfl) ⟨1716308, by rfl⟩ : syracuseStep 2288411 = 3432617) B3432617
theorem B454559 : Blo 451781 454559 := bstep (se 1 (by rfl) ⟨340919, by rfl⟩ : syracuseStep 454559 = 681839) B681839
theorem B454959 : Blo 451781 454959 := bstep (se 1 (by rfl) ⟨341219, by rfl⟩ : syracuseStep 454959 = 682439) B682439
theorem B1634863 : Blo 451781 1634863 := bstep (se 1 (by rfl) ⟨1226147, by rfl⟩ : syracuseStep 1634863 = 2452295) B2452295
theorem B103675783 : Blo 451781 103675783 := bstep (se 1 (by rfl) ⟨77756837, by rfl⟩ : syracuseStep 103675783 = 155513675) B155513675
theorem B3275579 : Blo 451781 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B6522727 : Blo 451781 6522727 := bstep (se 1 (by rfl) ⟨4892045, by rfl⟩ : syracuseStep 6522727 = 9784091) B9784091
theorem B3443795 : Blo 451781 3443795 := bstep (se 1 (by rfl) ⟨2582846, by rfl⟩ : syracuseStep 3443795 = 5165693) B5165693
theorem B1019177 : Blo 451781 1019177 := bstep (se 2 (by rfl) ⟨382191, by rfl⟩ : syracuseStep 1019177 = 764383) B764383
theorem B1382143 : Blo 451781 1382143 := bstep (se 1 (by rfl) ⟨1036607, by rfl⟩ : syracuseStep 1382143 = 2073215) B2073215
theorem B1022201 : Blo 451781 1022201 := bstep (se 2 (by rfl) ⟨383325, by rfl⟩ : syracuseStep 1022201 = 766651) B766651
theorem B2303315 : Blo 451781 2303315 := bstep (se 1 (by rfl) ⟨1727486, by rfl⟩ : syracuseStep 2303315 = 3454973) B3454973
theorem B1944449 : Blo 451781 1944449 := bstep (se 2 (by rfl) ⟨729168, by rfl⟩ : syracuseStep 1944449 = 1458337) B1458337
theorem B3877793 : Blo 451781 3877793 := bstep (se 2 (by rfl) ⟨1454172, by rfl⟩ : syracuseStep 3877793 = 2908345) B2908345
theorem B19574743 : Blo 451781 19574743 := bstep (se 1 (by rfl) ⟨14681057, by rfl⟩ : syracuseStep 19574743 = 29362115) B29362115
theorem B1455517 : Blo 451781 1455517 := bstep (se 3 (by rfl) ⟨272909, by rfl⟩ : syracuseStep 1455517 = 545819) B545819
theorem B2179817 : Blo 451781 2179817 := bstep (se 2 (by rfl) ⟨817431, by rfl⟩ : syracuseStep 2179817 = 1634863) B1634863
theorem B1525607 : Blo 451781 1525607 := bstep (se 1 (by rfl) ⟨1144205, by rfl⟩ : syracuseStep 1525607 = 2288411) B2288411
theorem B13027229 : Blo 451781 13027229 := bstep (se 3 (by rfl) ⟨2442605, by rfl⟩ : syracuseStep 13027229 = 4885211) B4885211
theorem B8734877 : Blo 451781 8734877 := bstep (se 3 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 8734877 = 3275579) B3275579
theorem B138234377 : Blo 451781 138234377 := bstep (se 2 (by rfl) ⟨51837891, by rfl⟩ : syracuseStep 138234377 = 103675783) B103675783
theorem B13945405 : Blo 451781 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B1529711 : Blo 451781 1529711 := bstep (se 1 (by rfl) ⟨1147283, by rfl⟩ : syracuseStep 1529711 = 2294567) B2294567
theorem B678335 : Blo 451781 678335 := bstep (se 1 (by rfl) ⟨508751, by rfl⟩ : syracuseStep 678335 = 1017503) B1017503
theorem B3268745 : Blo 451781 3268745 := bstep (se 2 (by rfl) ⟨1225779, by rfl⟩ : syracuseStep 3268745 = 2451559) B2451559
theorem B452143 : Blo 451781 452143 := bstep (se 1 (by rfl) ⟨339107, by rfl⟩ : syracuseStep 452143 = 678215) B678215
theorem B682343 : Blo 451781 682343 := bstep (se 1 (by rfl) ⟨511757, by rfl⟩ : syracuseStep 682343 = 1023515) B1023515
theorem B453119 : Blo 451781 453119 := bstep (se 1 (by rfl) ⟨339839, by rfl⟩ : syracuseStep 453119 = 679679) B679679
theorem B34073111 : Blo 451781 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B3271661 : Blo 451781 3271661 := bstep (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) B1226873
theorem B2452943 : Blo 451781 2452943 := bstep (se 1 (by rfl) ⟨1839707, by rfl⟩ : syracuseStep 2452943 = 3679415) B3679415
theorem B1536137 : Blo 451781 1536137 := bstep (se 2 (by rfl) ⟨576051, by rfl⟩ : syracuseStep 1536137 = 1152103) B1152103
theorem B7960313 : Blo 451781 7960313 := bstep (se 2 (by rfl) ⟨2985117, by rfl⟩ : syracuseStep 7960313 = 5970235) B5970235
theorem B2293757 : Blo 451781 2293757 := bstep (se 3 (by rfl) ⟨430079, by rfl⟩ : syracuseStep 2293757 = 860159) B860159
theorem B1017071 : Blo 451781 1017071 := bstep (se 1 (by rfl) ⟨762803, by rfl⟩ : syracuseStep 1017071 = 1525607) B1525607
theorem B8684819 : Blo 451781 8684819 := bstep (se 1 (by rfl) ⟨6513614, by rfl⟩ : syracuseStep 8684819 = 13027229) B13027229
theorem B2295863 : Blo 451781 2295863 := bstep (se 1 (by rfl) ⟨1721897, by rfl⟩ : syracuseStep 2295863 = 3443795) B3443795
theorem B1019807 : Blo 451781 1019807 := bstep (se 1 (by rfl) ⟨764855, by rfl⟩ : syracuseStep 1019807 = 1529711) B1529711
theorem B22715407 : Blo 451781 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B1940689 : Blo 451781 1940689 := bstep (se 2 (by rfl) ⟨727758, by rfl⟩ : syracuseStep 1940689 = 1455517) B1455517
theorem B1842857 : Blo 451781 1842857 := bstep (se 2 (by rfl) ⟨691071, by rfl⟩ : syracuseStep 1842857 = 1382143) B1382143
theorem B1024091 : Blo 451781 1024091 := bstep (se 1 (by rfl) ⟨768068, by rfl⟩ : syracuseStep 1024091 = 1536137) B1536137
theorem B1453211 : Blo 451781 1453211 := bstep (se 1 (by rfl) ⟨1089908, by rfl⟩ : syracuseStep 1453211 = 2179817) B2179817
theorem B92156251 : Blo 451781 92156251 := bstep (se 1 (by rfl) ⟨69117188, by rfl⟩ : syracuseStep 92156251 = 138234377) B138234377
theorem B8696969 : Blo 451781 8696969 := bstep (se 2 (by rfl) ⟨3261363, by rfl⟩ : syracuseStep 8696969 = 6522727) B6522727
theorem B18593873 : Blo 451781 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B26099657 : Blo 451781 26099657 := bstep (se 2 (by rfl) ⟨9787371, by rfl⟩ : syracuseStep 26099657 = 19574743) B19574743
theorem B2179163 : Blo 451781 2179163 := bstep (se 1 (by rfl) ⟨1634372, by rfl⟩ : syracuseStep 2179163 = 3268745) B3268745
theorem B1296299 : Blo 451781 1296299 := bstep (se 1 (by rfl) ⟨972224, by rfl⟩ : syracuseStep 1296299 = 1944449) B1944449
theorem B2181107 : Blo 451781 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B6541181 : Blo 451781 6541181 := bstep (se 3 (by rfl) ⟨1226471, by rfl⟩ : syracuseStep 6541181 = 2452943) B2452943
theorem B1529171 : Blo 451781 1529171 := bstep (se 1 (by rfl) ⟨1146878, by rfl⟩ : syracuseStep 1529171 = 2293757) B2293757
theorem B5823251 : Blo 451781 5823251 := bstep (se 1 (by rfl) ⟨4367438, by rfl⟩ : syracuseStep 5823251 = 8734877) B8734877
theorem B679451 : Blo 451781 679451 := bstep (se 1 (by rfl) ⟨509588, by rfl⟩ : syracuseStep 679451 = 1019177) B1019177
theorem B681467 : Blo 451781 681467 := bstep (se 1 (by rfl) ⟨511100, by rfl⟩ : syracuseStep 681467 = 1022201) B1022201
theorem B452223 : Blo 451781 452223 := bstep (se 1 (by rfl) ⟨339167, by rfl⟩ : syracuseStep 452223 = 678335) B678335
theorem B21227501 : Blo 451781 21227501 := bstep (se 3 (by rfl) ⟨3980156, by rfl⟩ : syracuseStep 21227501 = 7960313) B7960313
theorem B1535543 : Blo 451781 1535543 := bstep (se 1 (by rfl) ⟨1151657, by rfl⟩ : syracuseStep 1535543 = 2303315) B2303315
theorem B454895 : Blo 451781 454895 := bstep (se 1 (by rfl) ⟨341171, by rfl⟩ : syracuseStep 454895 = 682343) B682343
theorem B2585195 : Blo 451781 2585195 := bstep (se 1 (by rfl) ⟨1938896, by rfl⟩ : syracuseStep 2585195 = 3877793) B3877793
theorem B4360787 : Blo 451781 4360787 := bstep (se 1 (by rfl) ⟨3270590, by rfl⟩ : syracuseStep 4360787 = 6541181) B6541181
theorem B1019447 : Blo 451781 1019447 := bstep (se 1 (by rfl) ⟨764585, by rfl⟩ : syracuseStep 1019447 = 1529171) B1529171
theorem B1023695 : Blo 451781 1023695 := bstep (se 1 (by rfl) ⟨767771, by rfl⟩ : syracuseStep 1023695 = 1535543) B1535543
theorem B30287209 : Blo 451781 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B12395915 : Blo 451781 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B5811101 : Blo 451781 5811101 := bstep (se 3 (by rfl) ⟨1089581, by rfl⟩ : syracuseStep 5811101 = 2179163) B2179163
theorem B864199 : Blo 451781 864199 := bstep (se 1 (by rfl) ⟨648149, by rfl⟩ : syracuseStep 864199 = 1296299) B1296299
theorem B1454071 : Blo 451781 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B3882167 : Blo 451781 3882167 := bstep (se 1 (by rfl) ⟨2911625, by rfl⟩ : syracuseStep 3882167 = 5823251) B5823251
theorem B1228571 : Blo 451781 1228571 := bstep (se 1 (by rfl) ⟨921428, by rfl⟩ : syracuseStep 1228571 = 1842857) B1842857
theorem B968807 : Blo 451781 968807 := bstep (se 1 (by rfl) ⟨726605, by rfl⟩ : syracuseStep 968807 = 1453211) B1453211
theorem B1723463 : Blo 451781 1723463 := bstep (se 1 (by rfl) ⟨1292597, by rfl⟩ : syracuseStep 1723463 = 2585195) B2585195
theorem B678047 : Blo 451781 678047 := bstep (se 1 (by rfl) ⟨508535, by rfl⟩ : syracuseStep 678047 = 1017071) B1017071
theorem B5789879 : Blo 451781 5789879 := bstep (se 1 (by rfl) ⟨4342409, by rfl⟩ : syracuseStep 5789879 = 8684819) B8684819
theorem B1530575 : Blo 451781 1530575 := bstep (se 1 (by rfl) ⟨1147931, by rfl⟩ : syracuseStep 1530575 = 2295863) B2295863
theorem B679871 : Blo 451781 679871 := bstep (se 1 (by rfl) ⟨509903, by rfl⟩ : syracuseStep 679871 = 1019807) B1019807
theorem B452967 : Blo 451781 452967 := bstep (se 1 (by rfl) ⟨339725, by rfl⟩ : syracuseStep 452967 = 679451) B679451
theorem B682727 : Blo 451781 682727 := bstep (se 1 (by rfl) ⟨512045, by rfl⟩ : syracuseStep 682727 = 1024091) B1024091
theorem B122875001 : Blo 451781 122875001 := bstep (se 2 (by rfl) ⟨46078125, by rfl⟩ : syracuseStep 122875001 = 92156251) B92156251
theorem B454311 : Blo 451781 454311 := bstep (se 1 (by rfl) ⟨340733, by rfl⟩ : syracuseStep 454311 = 681467) B681467
theorem B14151667 : Blo 451781 14151667 := bstep (se 1 (by rfl) ⟨10613750, by rfl⟩ : syracuseStep 14151667 = 21227501) B21227501
theorem B5797979 : Blo 451781 5797979 := bstep (se 1 (by rfl) ⟨4348484, by rfl⟩ : syracuseStep 5797979 = 8696969) B8696969
theorem B2587585 : Blo 451781 2587585 := bstep (se 2 (by rfl) ⟨970344, by rfl⟩ : syracuseStep 2587585 = 1940689) B1940689
theorem B17399771 : Blo 451781 17399771 := bstep (se 1 (by rfl) ⟨13049828, by rfl⟩ : syracuseStep 17399771 = 26099657) B26099657
theorem B1148975 : Blo 451781 1148975 := bstep (se 1 (by rfl) ⟨861731, by rfl⟩ : syracuseStep 1148975 = 1723463) B1723463
theorem B1020383 : Blo 451781 1020383 := bstep (se 1 (by rfl) ⟨765287, by rfl⟩ : syracuseStep 1020383 = 1530575) B1530575
theorem B1152265 : Blo 451781 1152265 := bstep (se 2 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 1152265 = 864199) B864199
theorem B1938761 : Blo 451781 1938761 := bstep (se 2 (by rfl) ⟨727035, by rfl⟩ : syracuseStep 1938761 = 1454071) B1454071
theorem B8263943 : Blo 451781 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B3874067 : Blo 451781 3874067 := bstep (se 1 (by rfl) ⟨2905550, by rfl⟩ : syracuseStep 3874067 = 5811101) B5811101
theorem B3450113 : Blo 451781 3450113 := bstep (se 2 (by rfl) ⟨1293792, by rfl⟩ : syracuseStep 3450113 = 2587585) B2587585
theorem B40382945 : Blo 451781 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B2907191 : Blo 451781 2907191 := bstep (se 1 (by rfl) ⟨2180393, by rfl⟩ : syracuseStep 2907191 = 4360787) B4360787
theorem B679631 : Blo 451781 679631 := bstep (se 1 (by rfl) ⟨509723, by rfl⟩ : syracuseStep 679631 = 1019447) B1019447
theorem B452031 : Blo 451781 452031 := bstep (se 1 (by rfl) ⟨339023, by rfl⟩ : syracuseStep 452031 = 678047) B678047
theorem B3859919 : Blo 451781 3859919 := bstep (se 1 (by rfl) ⟨2894939, by rfl⟩ : syracuseStep 3859919 = 5789879) B5789879
theorem B682463 : Blo 451781 682463 := bstep (se 1 (by rfl) ⟨511847, by rfl⟩ : syracuseStep 682463 = 1023695) B1023695
theorem B453247 : Blo 451781 453247 := bstep (se 1 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 453247 = 679871) B679871
theorem B18868889 : Blo 451781 18868889 := bstep (se 2 (by rfl) ⟨7075833, by rfl⟩ : syracuseStep 18868889 = 14151667) B14151667
theorem B2583485 : Blo 451781 2583485 := bstep (se 3 (by rfl) ⟨484403, by rfl⟩ : syracuseStep 2583485 = 968807) B968807
theorem B455151 : Blo 451781 455151 := bstep (se 1 (by rfl) ⟨341363, by rfl⟩ : syracuseStep 455151 = 682727) B682727
theorem B81916667 : Blo 451781 81916667 := bstep (se 1 (by rfl) ⟨61437500, by rfl⟩ : syracuseStep 81916667 = 122875001) B122875001
theorem B3865319 : Blo 451781 3865319 := bstep (se 1 (by rfl) ⟨2898989, by rfl⟩ : syracuseStep 3865319 = 5797979) B5797979
theorem B2588111 : Blo 451781 2588111 := bstep (se 1 (by rfl) ⟨1941083, by rfl⟩ : syracuseStep 2588111 = 3882167) B3882167
theorem B819047 : Blo 451781 819047 := bstep (se 1 (by rfl) ⟨614285, by rfl⟩ : syracuseStep 819047 = 1228571) B1228571
theorem B11599847 : Blo 451781 11599847 := bstep (se 1 (by rfl) ⟨8699885, by rfl⟩ : syracuseStep 11599847 = 17399771) B17399771
theorem B5509295 : Blo 451781 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B1938127 : Blo 451781 1938127 := bstep (se 1 (by rfl) ⟨1453595, by rfl⟩ : syracuseStep 1938127 = 2907191) B2907191
theorem B2300075 : Blo 451781 2300075 := bstep (se 1 (by rfl) ⟨1725056, by rfl⟩ : syracuseStep 2300075 = 3450113) B3450113
theorem B765983 : Blo 451781 765983 := bstep (se 1 (by rfl) ⟨574487, by rfl⟩ : syracuseStep 765983 = 1148975) B1148975
theorem B1292507 : Blo 451781 1292507 := bstep (se 1 (by rfl) ⟨969380, by rfl⟩ : syracuseStep 1292507 = 1938761) B1938761
theorem B2573279 : Blo 451781 2573279 := bstep (se 1 (by rfl) ⟨1929959, by rfl⟩ : syracuseStep 2573279 = 3859919) B3859919
theorem B1722323 : Blo 451781 1722323 := bstep (se 1 (by rfl) ⟨1291742, by rfl⟩ : syracuseStep 1722323 = 2583485) B2583485
theorem B26921963 : Blo 451781 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B54611111 : Blo 451781 54611111 := bstep (se 1 (by rfl) ⟨40958333, by rfl⟩ : syracuseStep 54611111 = 81916667) B81916667
theorem B2576879 : Blo 451781 2576879 := bstep (se 1 (by rfl) ⟨1932659, by rfl⟩ : syracuseStep 2576879 = 3865319) B3865319
theorem B1725407 : Blo 451781 1725407 := bstep (se 1 (by rfl) ⟨1294055, by rfl⟩ : syracuseStep 1725407 = 2588111) B2588111
theorem B546031 : Blo 451781 546031 := bstep (se 1 (by rfl) ⟨409523, by rfl⟩ : syracuseStep 546031 = 819047) B819047
theorem B680255 : Blo 451781 680255 := bstep (se 1 (by rfl) ⟨510191, by rfl⟩ : syracuseStep 680255 = 1020383) B1020383
theorem B2582711 : Blo 451781 2582711 := bstep (se 1 (by rfl) ⟨1937033, by rfl⟩ : syracuseStep 2582711 = 3874067) B3874067
theorem B453087 : Blo 451781 453087 := bstep (se 1 (by rfl) ⟨339815, by rfl⟩ : syracuseStep 453087 = 679631) B679631
theorem B454975 : Blo 451781 454975 := bstep (se 1 (by rfl) ⟨341231, by rfl⟩ : syracuseStep 454975 = 682463) B682463
theorem B1536353 : Blo 451781 1536353 := bstep (se 2 (by rfl) ⟨576132, by rfl⟩ : syracuseStep 1536353 = 1152265) B1152265
theorem B12579259 : Blo 451781 12579259 := bstep (se 1 (by rfl) ⟨9434444, by rfl⟩ : syracuseStep 12579259 = 18868889) B18868889
theorem B7733231 : Blo 451781 7733231 := bstep (se 1 (by rfl) ⟨5799923, by rfl⟩ : syracuseStep 7733231 = 11599847) B11599847
theorem B1148215 : Blo 451781 1148215 := bstep (se 1 (by rfl) ⟨861161, by rfl⟩ : syracuseStep 1148215 = 1722323) B1722323
theorem B36407407 : Blo 451781 36407407 := bstep (se 1 (by rfl) ⟨27305555, by rfl⟩ : syracuseStep 36407407 = 54611111) B54611111
theorem B3672863 : Blo 451781 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B1150271 : Blo 451781 1150271 := bstep (se 1 (by rfl) ⟨862703, by rfl⟩ : syracuseStep 1150271 = 1725407) B1725407
theorem B728041 : Blo 451781 728041 := bstep (se 2 (by rfl) ⟨273015, by rfl⟩ : syracuseStep 728041 = 546031) B546031
theorem B1024235 : Blo 451781 1024235 := bstep (se 1 (by rfl) ⟨768176, by rfl⟩ : syracuseStep 1024235 = 1536353) B1536353
theorem B861671 : Blo 451781 861671 := bstep (se 1 (by rfl) ⟨646253, by rfl⟩ : syracuseStep 861671 = 1292507) B1292507
theorem B5155487 : Blo 451781 5155487 := bstep (se 1 (by rfl) ⟨3866615, by rfl⟩ : syracuseStep 5155487 = 7733231) B7733231
theorem B1715519 : Blo 451781 1715519 := bstep (se 1 (by rfl) ⟨1286639, by rfl⟩ : syracuseStep 1715519 = 2573279) B2573279
theorem B1717919 : Blo 451781 1717919 := bstep (se 1 (by rfl) ⟨1288439, by rfl⟩ : syracuseStep 1717919 = 2576879) B2576879
theorem B1721807 : Blo 451781 1721807 := bstep (se 1 (by rfl) ⟨1291355, by rfl⟩ : syracuseStep 1721807 = 2582711) B2582711
theorem B510655 : Blo 451781 510655 := bstep (se 1 (by rfl) ⟨382991, by rfl⟩ : syracuseStep 510655 = 765983) B765983
theorem B17947975 : Blo 451781 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B1533383 : Blo 451781 1533383 := bstep (se 1 (by rfl) ⟨1150037, by rfl⟩ : syracuseStep 1533383 = 2300075) B2300075
theorem B453503 : Blo 451781 453503 := bstep (se 1 (by rfl) ⟨340127, by rfl⟩ : syracuseStep 453503 = 680255) B680255
theorem B16772345 : Blo 451781 16772345 := bstep (se 2 (by rfl) ⟨6289629, by rfl⟩ : syracuseStep 16772345 = 12579259) B12579259
theorem B2584169 : Blo 451781 2584169 := bstep (se 2 (by rfl) ⟨969063, by rfl⟩ : syracuseStep 2584169 = 1938127) B1938127
theorem B1147871 : Blo 451781 1147871 := bstep (se 1 (by rfl) ⟨860903, by rfl⟩ : syracuseStep 1147871 = 1721807) B1721807
theorem B1022255 : Blo 451781 1022255 := bstep (se 1 (by rfl) ⟨766691, by rfl⟩ : syracuseStep 1022255 = 1533383) B1533383
theorem B11181563 : Blo 451781 11181563 := bstep (se 1 (by rfl) ⟨8386172, by rfl⟩ : syracuseStep 11181563 = 16772345) B16772345
theorem B23930633 : Blo 451781 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B766847 : Blo 451781 766847 := bstep (se 1 (by rfl) ⟨575135, by rfl⟩ : syracuseStep 766847 = 1150271) B1150271
theorem B48543209 : Blo 451781 48543209 := bstep (se 2 (by rfl) ⟨18203703, by rfl⟩ : syracuseStep 48543209 = 36407407) B36407407
theorem B574447 : Blo 451781 574447 := bstep (se 1 (by rfl) ⟨430835, by rfl⟩ : syracuseStep 574447 = 861671) B861671
theorem B1722779 : Blo 451781 1722779 := bstep (se 1 (by rfl) ⟨1292084, by rfl⟩ : syracuseStep 1722779 = 2584169) B2584169
theorem B970721 : Blo 451781 970721 := bstep (se 2 (by rfl) ⟨364020, by rfl⟩ : syracuseStep 970721 = 728041) B728041
theorem B1530953 : Blo 451781 1530953 := bstep (se 2 (by rfl) ⟨574107, by rfl⟩ : syracuseStep 1530953 = 1148215) B1148215
theorem B2448575 : Blo 451781 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B680873 : Blo 451781 680873 := bstep (se 2 (by rfl) ⟨255327, by rfl⟩ : syracuseStep 680873 = 510655) B510655
theorem B682823 : Blo 451781 682823 := bstep (se 1 (by rfl) ⟨512117, by rfl⟩ : syracuseStep 682823 = 1024235) B1024235
theorem B3436991 : Blo 451781 3436991 := bstep (se 1 (by rfl) ⟨2577743, by rfl⟩ : syracuseStep 3436991 = 5155487) B5155487
theorem B1143679 : Blo 451781 1143679 := bstep (se 1 (by rfl) ⟨857759, by rfl⟩ : syracuseStep 1143679 = 1715519) B1715519
theorem B1145279 : Blo 451781 1145279 := bstep (se 1 (by rfl) ⟨858959, by rfl⟩ : syracuseStep 1145279 = 1717919) B1717919
theorem B1148519 : Blo 451781 1148519 := bstep (se 1 (by rfl) ⟨861389, by rfl⟩ : syracuseStep 1148519 = 1722779) B1722779
theorem B1020635 : Blo 451781 1020635 := bstep (se 1 (by rfl) ⟨765476, by rfl⟩ : syracuseStep 1020635 = 1530953) B1530953
theorem B763519 : Blo 451781 763519 := bstep (se 1 (by rfl) ⟨572639, by rfl⟩ : syracuseStep 763519 = 1145279) B1145279
theorem B765247 : Blo 451781 765247 := bstep (se 1 (by rfl) ⟨573935, by rfl⟩ : syracuseStep 765247 = 1147871) B1147871
theorem B765929 : Blo 451781 765929 := bstep (se 2 (by rfl) ⟨287223, by rfl⟩ : syracuseStep 765929 = 574447) B574447
theorem B7454375 : Blo 451781 7454375 := bstep (se 1 (by rfl) ⟨5590781, by rfl⟩ : syracuseStep 7454375 = 11181563) B11181563
theorem B1524905 : Blo 451781 1524905 := bstep (se 2 (by rfl) ⟨571839, by rfl⟩ : syracuseStep 1524905 = 1143679) B1143679
theorem B511231 : Blo 451781 511231 := bstep (se 1 (by rfl) ⟨383423, by rfl⟩ : syracuseStep 511231 = 766847) B766847
theorem B32362139 : Blo 451781 32362139 := bstep (se 1 (by rfl) ⟨24271604, by rfl⟩ : syracuseStep 32362139 = 48543209) B48543209
theorem B647147 : Blo 451781 647147 := bstep (se 1 (by rfl) ⟨485360, by rfl⟩ : syracuseStep 647147 = 970721) B970721
theorem B681503 : Blo 451781 681503 := bstep (se 1 (by rfl) ⟨511127, by rfl⟩ : syracuseStep 681503 = 1022255) B1022255
theorem B1632383 : Blo 451781 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B453915 : Blo 451781 453915 := bstep (se 1 (by rfl) ⟨340436, by rfl⟩ : syracuseStep 453915 = 680873) B680873
theorem B15953755 : Blo 451781 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B455215 : Blo 451781 455215 := bstep (se 1 (by rfl) ⟨341411, by rfl⟩ : syracuseStep 455215 = 682823) B682823
theorem B2291327 : Blo 451781 2291327 := bstep (se 1 (by rfl) ⟨1718495, by rfl⟩ : syracuseStep 2291327 = 3436991) B3436991
theorem B1016603 : Blo 451781 1016603 := bstep (se 1 (by rfl) ⟨762452, by rfl⟩ : syracuseStep 1016603 = 1524905) B1524905
theorem B1018025 : Blo 451781 1018025 := bstep (se 2 (by rfl) ⟨381759, by rfl⟩ : syracuseStep 1018025 = 763519) B763519
theorem B1020329 : Blo 451781 1020329 := bstep (se 2 (by rfl) ⟨382623, by rfl⟩ : syracuseStep 1020329 = 765247) B765247
theorem B21271673 : Blo 451781 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B1088255 : Blo 451781 1088255 := bstep (se 1 (by rfl) ⟨816191, by rfl⟩ : syracuseStep 1088255 = 1632383) B1632383
theorem B765679 : Blo 451781 765679 := bstep (se 1 (by rfl) ⟨574259, by rfl⟩ : syracuseStep 765679 = 1148519) B1148519
theorem B21574759 : Blo 451781 21574759 := bstep (se 1 (by rfl) ⟨16181069, by rfl⟩ : syracuseStep 21574759 = 32362139) B32362139
theorem B510619 : Blo 451781 510619 := bstep (se 1 (by rfl) ⟨382964, by rfl⟩ : syracuseStep 510619 = 765929) B765929
theorem B1527551 : Blo 451781 1527551 := bstep (se 1 (by rfl) ⟨1145663, by rfl⟩ : syracuseStep 1527551 = 2291327) B2291327
theorem B4969583 : Blo 451781 4969583 := bstep (se 1 (by rfl) ⟨3727187, by rfl⟩ : syracuseStep 4969583 = 7454375) B7454375
theorem B1725725 : Blo 451781 1725725 := bstep (se 3 (by rfl) ⟨323573, by rfl⟩ : syracuseStep 1725725 = 647147) B647147
theorem B680423 : Blo 451781 680423 := bstep (se 1 (by rfl) ⟨510317, by rfl⟩ : syracuseStep 680423 = 1020635) B1020635
theorem B681641 : Blo 451781 681641 := bstep (se 2 (by rfl) ⟨255615, by rfl⟩ : syracuseStep 681641 = 511231) B511231
theorem B454335 : Blo 451781 454335 := bstep (se 1 (by rfl) ⟨340751, by rfl⟩ : syracuseStep 454335 = 681503) B681503
theorem B1018367 : Blo 451781 1018367 := bstep (se 1 (by rfl) ⟨763775, by rfl⟩ : syracuseStep 1018367 = 1527551) B1527551
theorem B56724461 : Blo 451781 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B3313055 : Blo 451781 3313055 := bstep (se 1 (by rfl) ⟨2484791, by rfl⟩ : syracuseStep 3313055 = 4969583) B4969583
theorem B1150483 : Blo 451781 1150483 := bstep (se 1 (by rfl) ⟨862862, by rfl⟩ : syracuseStep 1150483 = 1725725) B1725725
theorem B1020905 : Blo 451781 1020905 := bstep (se 2 (by rfl) ⟨382839, by rfl⟩ : syracuseStep 1020905 = 765679) B765679
theorem B2902013 : Blo 451781 2902013 := bstep (se 3 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 2902013 = 1088255) B1088255
theorem B677735 : Blo 451781 677735 := bstep (se 1 (by rfl) ⟨508301, by rfl⟩ : syracuseStep 677735 = 1016603) B1016603
theorem B678683 : Blo 451781 678683 := bstep (se 1 (by rfl) ⟨509012, by rfl⟩ : syracuseStep 678683 = 1018025) B1018025
theorem B680219 : Blo 451781 680219 := bstep (se 1 (by rfl) ⟨510164, by rfl⟩ : syracuseStep 680219 = 1020329) B1020329
theorem B680825 : Blo 451781 680825 := bstep (se 2 (by rfl) ⟨255309, by rfl⟩ : syracuseStep 680825 = 510619) B510619
theorem B453615 : Blo 451781 453615 := bstep (se 1 (by rfl) ⟨340211, by rfl⟩ : syracuseStep 453615 = 680423) B680423
theorem B454427 : Blo 451781 454427 := bstep (se 1 (by rfl) ⟨340820, by rfl⟩ : syracuseStep 454427 = 681641) B681641
theorem B28766345 : Blo 451781 28766345 := bstep (se 2 (by rfl) ⟨10787379, by rfl⟩ : syracuseStep 28766345 = 21574759) B21574759
theorem B76710253 : Blo 451781 76710253 := bstep (se 3 (by rfl) ⟨14383172, by rfl⟩ : syracuseStep 76710253 = 28766345) B28766345
theorem B1934675 : Blo 451781 1934675 := bstep (se 1 (by rfl) ⟨1451006, by rfl⟩ : syracuseStep 1934675 = 2902013) B2902013
theorem B37816307 : Blo 451781 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B2208703 : Blo 451781 2208703 := bstep (se 1 (by rfl) ⟨1656527, by rfl⟩ : syracuseStep 2208703 = 3313055) B3313055
theorem B678911 : Blo 451781 678911 := bstep (se 1 (by rfl) ⟨509183, by rfl⟩ : syracuseStep 678911 = 1018367) B1018367
theorem B680603 : Blo 451781 680603 := bstep (se 1 (by rfl) ⟨510452, by rfl⟩ : syracuseStep 680603 = 1020905) B1020905
theorem B451823 : Blo 451781 451823 := bstep (se 1 (by rfl) ⟨338867, by rfl⟩ : syracuseStep 451823 = 677735) B677735
theorem B452455 : Blo 451781 452455 := bstep (se 1 (by rfl) ⟨339341, by rfl⟩ : syracuseStep 452455 = 678683) B678683
theorem B1533977 : Blo 451781 1533977 := bstep (se 2 (by rfl) ⟨575241, by rfl⟩ : syracuseStep 1533977 = 1150483) B1150483
theorem B453479 : Blo 451781 453479 := bstep (se 1 (by rfl) ⟨340109, by rfl⟩ : syracuseStep 453479 = 680219) B680219
theorem B453883 : Blo 451781 453883 := bstep (se 1 (by rfl) ⟨340412, by rfl⟩ : syracuseStep 453883 = 680825) B680825
theorem B1022651 : Blo 451781 1022651 := bstep (se 1 (by rfl) ⟨766988, by rfl⟩ : syracuseStep 1022651 = 1533977) B1533977
theorem B102280337 : Blo 451781 102280337 := bstep (se 2 (by rfl) ⟨38355126, by rfl⟩ : syracuseStep 102280337 = 76710253) B76710253
theorem B1289783 : Blo 451781 1289783 := bstep (se 1 (by rfl) ⟨967337, by rfl⟩ : syracuseStep 1289783 = 1934675) B1934675
theorem B25210871 : Blo 451781 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B452607 : Blo 451781 452607 := bstep (se 1 (by rfl) ⟨339455, by rfl⟩ : syracuseStep 452607 = 678911) B678911
theorem B453735 : Blo 451781 453735 := bstep (se 1 (by rfl) ⟨340301, by rfl⟩ : syracuseStep 453735 = 680603) B680603
theorem B2944937 : Blo 451781 2944937 := bstep (se 2 (by rfl) ⟨1104351, by rfl⟩ : syracuseStep 2944937 = 2208703) B2208703
theorem B681767 : Blo 451781 681767 := bstep (se 1 (by rfl) ⟨511325, by rfl⟩ : syracuseStep 681767 = 1022651) B1022651
theorem B68186891 : Blo 451781 68186891 := bstep (se 1 (by rfl) ⟨51140168, by rfl⟩ : syracuseStep 68186891 = 102280337) B102280337
theorem B1963291 : Blo 451781 1963291 := bstep (se 1 (by rfl) ⟨1472468, by rfl⟩ : syracuseStep 1963291 = 2944937) B2944937
theorem B16807247 : Blo 451781 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B3439421 : Blo 451781 3439421 := bstep (se 3 (by rfl) ⟨644891, by rfl⟩ : syracuseStep 3439421 = 1289783) B1289783
theorem B181831709 : Blo 451781 181831709 := bstep (se 3 (by rfl) ⟨34093445, by rfl⟩ : syracuseStep 181831709 = 68186891) B68186891
theorem B454511 : Blo 451781 454511 := bstep (se 1 (by rfl) ⟨340883, by rfl⟩ : syracuseStep 454511 = 681767) B681767
theorem B2617721 : Blo 451781 2617721 := bstep (se 2 (by rfl) ⟨981645, by rfl⟩ : syracuseStep 2617721 = 1963291) B1963291
theorem B11204831 : Blo 451781 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B2292947 : Blo 451781 2292947 := bstep (se 1 (by rfl) ⟨1719710, by rfl⟩ : syracuseStep 2292947 = 3439421) B3439421
theorem B1745147 : Blo 451781 1745147 := bstep (se 1 (by rfl) ⟨1308860, by rfl⟩ : syracuseStep 1745147 = 2617721) B2617721
theorem B121221139 : Blo 451781 121221139 := bstep (se 1 (by rfl) ⟨90915854, by rfl⟩ : syracuseStep 121221139 = 181831709) B181831709
theorem B1528631 : Blo 451781 1528631 := bstep (se 1 (by rfl) ⟨1146473, by rfl⟩ : syracuseStep 1528631 = 2292947) B2292947
theorem B7469887 : Blo 451781 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B1019087 : Blo 451781 1019087 := bstep (se 1 (by rfl) ⟨764315, by rfl⟩ : syracuseStep 1019087 = 1528631) B1528631
theorem B161628185 : Blo 451781 161628185 := bstep (se 2 (by rfl) ⟨60610569, by rfl⟩ : syracuseStep 161628185 = 121221139) B121221139
theorem B1163431 : Blo 451781 1163431 := bstep (se 1 (by rfl) ⟨872573, by rfl⟩ : syracuseStep 1163431 = 1745147) B1745147
theorem B9959849 : Blo 451781 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B107752123 : Blo 451781 107752123 := bstep (se 1 (by rfl) ⟨80814092, by rfl⟩ : syracuseStep 107752123 = 161628185) B161628185
theorem B1551241 : Blo 451781 1551241 := bstep (se 2 (by rfl) ⟨581715, by rfl⟩ : syracuseStep 1551241 = 1163431) B1163431
theorem B6639899 : Blo 451781 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B679391 : Blo 451781 679391 := bstep (se 1 (by rfl) ⟨509543, by rfl⟩ : syracuseStep 679391 = 1019087) B1019087
theorem B17706397 : Blo 451781 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B143669497 : Blo 451781 143669497 := bstep (se 2 (by rfl) ⟨53876061, by rfl⟩ : syracuseStep 143669497 = 107752123) B107752123
theorem B8273285 : Blo 451781 8273285 := bstep (se 4 (by rfl) ⟨775620, by rfl⟩ : syracuseStep 8273285 = 1551241) B1551241
theorem B452927 : Blo 451781 452927 := bstep (se 1 (by rfl) ⟨339695, by rfl⟩ : syracuseStep 452927 = 679391) B679391
theorem B5515523 : Blo 451781 5515523 := bstep (se 1 (by rfl) ⟨4136642, by rfl⟩ : syracuseStep 5515523 = 8273285) B8273285
theorem B23608529 : Blo 451781 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B191559329 : Blo 451781 191559329 := bstep (se 2 (by rfl) ⟨71834748, by rfl⟩ : syracuseStep 191559329 = 143669497) B143669497
theorem B3677015 : Blo 451781 3677015 := bstep (se 1 (by rfl) ⟨2757761, by rfl⟩ : syracuseStep 3677015 = 5515523) B5515523
theorem B127706219 : Blo 451781 127706219 := bstep (se 1 (by rfl) ⟨95779664, by rfl⟩ : syracuseStep 127706219 = 191559329) B191559329
theorem B15739019 : Blo 451781 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B85137479 : Blo 451781 85137479 := bstep (se 1 (by rfl) ⟨63853109, by rfl⟩ : syracuseStep 85137479 = 127706219) B127706219
theorem B10492679 : Blo 451781 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B2451343 : Blo 451781 2451343 := bstep (se 1 (by rfl) ⟨1838507, by rfl⟩ : syracuseStep 2451343 = 3677015) B3677015
theorem B56758319 : Blo 451781 56758319 := bstep (se 1 (by rfl) ⟨42568739, by rfl⟩ : syracuseStep 56758319 = 85137479) B85137479
theorem B6995119 : Blo 451781 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B3268457 : Blo 451781 3268457 := bstep (se 2 (by rfl) ⟨1225671, by rfl⟩ : syracuseStep 3268457 = 2451343) B2451343
theorem B2178971 : Blo 451781 2178971 := bstep (se 1 (by rfl) ⟨1634228, by rfl⟩ : syracuseStep 2178971 = 3268457) B3268457
theorem B9326825 : Blo 451781 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B37838879 : Blo 451781 37838879 := bstep (se 1 (by rfl) ⟨28379159, by rfl⟩ : syracuseStep 37838879 = 56758319) B56758319
theorem B1452647 : Blo 451781 1452647 := bstep (se 1 (by rfl) ⟨1089485, by rfl⟩ : syracuseStep 1452647 = 2178971) B2178971
theorem B6217883 : Blo 451781 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B25225919 : Blo 451781 25225919 := bstep (se 1 (by rfl) ⟨18919439, by rfl⟩ : syracuseStep 25225919 = 37838879) B37838879
theorem B16817279 : Blo 451781 16817279 := bstep (se 1 (by rfl) ⟨12612959, by rfl⟩ : syracuseStep 16817279 = 25225919) B25225919
theorem B4145255 : Blo 451781 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B968431 : Blo 451781 968431 := bstep (se 1 (by rfl) ⟨726323, by rfl⟩ : syracuseStep 968431 = 1452647) B1452647
theorem B2763503 : Blo 451781 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B1291241 : Blo 451781 1291241 := bstep (se 2 (by rfl) ⟨484215, by rfl⟩ : syracuseStep 1291241 = 968431) B968431
theorem B44846077 : Blo 451781 44846077 := bstep (se 3 (by rfl) ⟨8408639, by rfl⟩ : syracuseStep 44846077 = 16817279) B16817279
theorem B3443309 : Blo 451781 3443309 := bstep (se 3 (by rfl) ⟨645620, by rfl⟩ : syracuseStep 3443309 = 1291241) B1291241
theorem B1842335 : Blo 451781 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B59794769 : Blo 451781 59794769 := bstep (se 2 (by rfl) ⟨22423038, by rfl⟩ : syracuseStep 59794769 = 44846077) B44846077
theorem B2295539 : Blo 451781 2295539 := bstep (se 1 (by rfl) ⟨1721654, by rfl⟩ : syracuseStep 2295539 = 3443309) B3443309
theorem B1228223 : Blo 451781 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B39863179 : Blo 451781 39863179 := bstep (se 1 (by rfl) ⟨29897384, by rfl⟩ : syracuseStep 39863179 = 59794769) B59794769
theorem B53150905 : Blo 451781 53150905 := bstep (se 2 (by rfl) ⟨19931589, by rfl⟩ : syracuseStep 53150905 = 39863179) B39863179
theorem B1530359 : Blo 451781 1530359 := bstep (se 1 (by rfl) ⟨1147769, by rfl⟩ : syracuseStep 1530359 = 2295539) B2295539
theorem B3275261 : Blo 451781 3275261 := bstep (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) B1228223
theorem B1020239 : Blo 451781 1020239 := bstep (se 1 (by rfl) ⟨765179, by rfl⟩ : syracuseStep 1020239 = 1530359) B1530359
theorem B2183507 : Blo 451781 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B70867873 : Blo 451781 70867873 := bstep (se 2 (by rfl) ⟨26575452, by rfl⟩ : syracuseStep 70867873 = 53150905) B53150905
theorem B1455671 : Blo 451781 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B94490497 : Blo 451781 94490497 := bstep (se 2 (by rfl) ⟨35433936, by rfl⟩ : syracuseStep 94490497 = 70867873) B70867873
theorem B680159 : Blo 451781 680159 := bstep (se 1 (by rfl) ⟨510119, by rfl⟩ : syracuseStep 680159 = 1020239) B1020239
theorem B3881789 : Blo 451781 3881789 := bstep (se 3 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 3881789 = 1455671) B1455671
theorem B125987329 : Blo 451781 125987329 := bstep (se 2 (by rfl) ⟨47245248, by rfl⟩ : syracuseStep 125987329 = 94490497) B94490497
theorem B453439 : Blo 451781 453439 := bstep (se 1 (by rfl) ⟨340079, by rfl⟩ : syracuseStep 453439 = 680159) B680159
theorem B167983105 : Blo 451781 167983105 := bstep (se 2 (by rfl) ⟨62993664, by rfl⟩ : syracuseStep 167983105 = 125987329) B125987329
theorem B2587859 : Blo 451781 2587859 := bstep (se 1 (by rfl) ⟨1940894, by rfl⟩ : syracuseStep 2587859 = 3881789) B3881789
theorem B223977473 : Blo 451781 223977473 := bstep (se 2 (by rfl) ⟨83991552, by rfl⟩ : syracuseStep 223977473 = 167983105) B167983105
theorem B1725239 : Blo 451781 1725239 := bstep (se 1 (by rfl) ⟨1293929, by rfl⟩ : syracuseStep 1725239 = 2587859) B2587859
theorem B1150159 : Blo 451781 1150159 := bstep (se 1 (by rfl) ⟨862619, by rfl⟩ : syracuseStep 1150159 = 1725239) B1725239
theorem B149318315 : Blo 451781 149318315 := bstep (se 1 (by rfl) ⟨111988736, by rfl⟩ : syracuseStep 149318315 = 223977473) B223977473
theorem B1533545 : Blo 451781 1533545 := bstep (se 2 (by rfl) ⟨575079, by rfl⟩ : syracuseStep 1533545 = 1150159) B1150159
theorem B99545543 : Blo 451781 99545543 := bstep (se 1 (by rfl) ⟨74659157, by rfl⟩ : syracuseStep 99545543 = 149318315) B149318315
theorem B1022363 : Blo 451781 1022363 := bstep (se 1 (by rfl) ⟨766772, by rfl⟩ : syracuseStep 1022363 = 1533545) B1533545
theorem B66363695 : Blo 451781 66363695 := bstep (se 1 (by rfl) ⟨49772771, by rfl⟩ : syracuseStep 66363695 = 99545543) B99545543
theorem B44242463 : Blo 451781 44242463 := bstep (se 1 (by rfl) ⟨33181847, by rfl⟩ : syracuseStep 44242463 = 66363695) B66363695
theorem B681575 : Blo 451781 681575 := bstep (se 1 (by rfl) ⟨511181, by rfl⟩ : syracuseStep 681575 = 1022363) B1022363
theorem B29494975 : Blo 451781 29494975 := bstep (se 1 (by rfl) ⟨22121231, by rfl⟩ : syracuseStep 29494975 = 44242463) B44242463
theorem B454383 : Blo 451781 454383 := bstep (se 1 (by rfl) ⟨340787, by rfl⟩ : syracuseStep 454383 = 681575) B681575
theorem B39326633 : Blo 451781 39326633 := bstep (se 2 (by rfl) ⟨14747487, by rfl⟩ : syracuseStep 39326633 = 29494975) B29494975
theorem B26217755 : Blo 451781 26217755 := bstep (se 1 (by rfl) ⟨19663316, by rfl⟩ : syracuseStep 26217755 = 39326633) B39326633
theorem B17478503 : Blo 451781 17478503 := bstep (se 1 (by rfl) ⟨13108877, by rfl⟩ : syracuseStep 17478503 = 26217755) B26217755
theorem B11652335 : Blo 451781 11652335 := bstep (se 1 (by rfl) ⟨8739251, by rfl⟩ : syracuseStep 11652335 = 17478503) B17478503
theorem B7768223 : Blo 451781 7768223 := bstep (se 1 (by rfl) ⟨5826167, by rfl⟩ : syracuseStep 7768223 = 11652335) B11652335
theorem B5178815 : Blo 451781 5178815 := bstep (se 1 (by rfl) ⟨3884111, by rfl⟩ : syracuseStep 5178815 = 7768223) B7768223
theorem B3452543 : Blo 451781 3452543 := bstep (se 1 (by rfl) ⟨2589407, by rfl⟩ : syracuseStep 3452543 = 5178815) B5178815
theorem B2301695 : Blo 451781 2301695 := bstep (se 1 (by rfl) ⟨1726271, by rfl⟩ : syracuseStep 2301695 = 3452543) B3452543
theorem B1534463 : Blo 451781 1534463 := bstep (se 1 (by rfl) ⟨1150847, by rfl⟩ : syracuseStep 1534463 = 2301695) B2301695
theorem B1022975 : Blo 451781 1022975 := bstep (se 1 (by rfl) ⟨767231, by rfl⟩ : syracuseStep 1022975 = 1534463) B1534463
theorem B681983 : Blo 451781 681983 := bstep (se 1 (by rfl) ⟨511487, by rfl⟩ : syracuseStep 681983 = 1022975) B1022975
theorem B454655 : Blo 451781 454655 := bstep (se 1 (by rfl) ⟨340991, by rfl⟩ : syracuseStep 454655 = 681983) B681983

theorem C0 (j : ℕ) (h1 : 112945 ≤ j) (h2 : j ≤ 113644) : Blo 451781 (4 * j + 3) := by
  interval_cases j
  · exact B451783
  · exact B451787
  · exact B451791
  · exact B451795
  · exact B451799
  · exact B451803
  · exact B451807
  · exact B451811
  · exact B451815
  · exact B451819
  · exact B451823
  · exact B451827
  · exact B451831
  · exact B451835
  · exact B451839
  · exact B451843
  · exact B451847
  · exact B451851
  · exact B451855
  · exact B451859
  · exact B451863
  · exact B451867
  · exact B451871
  · exact B451875
  · exact B451879
  · exact B451883
  · exact B451887
  · exact B451891
  · exact B451895
  · exact B451899
  · exact B451903
  · exact B451907
  · exact B451911
  · exact B451915
  · exact B451919
  · exact B451923
  · exact B451927
  · exact B451931
  · exact B451935
  · exact B451939
  · exact B451943
  · exact B451947
  · exact B451951
  · exact B451955
  · exact B451959
  · exact B451963
  · exact B451967
  · exact B451971
  · exact B451975
  · exact B451979
  · exact B451983
  · exact B451987
  · exact B451991
  · exact B451995
  · exact B451999
  · exact B452003
  · exact B452007
  · exact B452011
  · exact B452015
  · exact B452019
  · exact B452023
  · exact B452027
  · exact B452031
  · exact B452035
  · exact B452039
  · exact B452043
  · exact B452047
  · exact B452051
  · exact B452055
  · exact B452059
  · exact B452063
  · exact B452067
  · exact B452071
  · exact B452075
  · exact B452079
  · exact B452083
  · exact B452087
  · exact B452091
  · exact B452095
  · exact B452099
  · exact B452103
  · exact B452107
  · exact B452111
  · exact B452115
  · exact B452119
  · exact B452123
  · exact B452127
  · exact B452131
  · exact B452135
  · exact B452139
  · exact B452143
  · exact B452147
  · exact B452151
  · exact B452155
  · exact B452159
  · exact B452163
  · exact B452167
  · exact B452171
  · exact B452175
  · exact B452179
  · exact B452183
  · exact B452187
  · exact B452191
  · exact B452195
  · exact B452199
  · exact B452203
  · exact B452207
  · exact B452211
  · exact B452215
  · exact B452219
  · exact B452223
  · exact B452227
  · exact B452231
  · exact B452235
  · exact B452239
  · exact B452243
  · exact B452247
  · exact B452251
  · exact B452255
  · exact B452259
  · exact B452263
  · exact B452267
  · exact B452271
  · exact B452275
  · exact B452279
  · exact B452283
  · exact B452287
  · exact B452291
  · exact B452295
  · exact B452299
  · exact B452303
  · exact B452307
  · exact B452311
  · exact B452315
  · exact B452319
  · exact B452323
  · exact B452327
  · exact B452331
  · exact B452335
  · exact B452339
  · exact B452343
  · exact B452347
  · exact B452351
  · exact B452355
  · exact B452359
  · exact B452363
  · exact B452367
  · exact B452371
  · exact B452375
  · exact B452379
  · exact B452383
  · exact B452387
  · exact B452391
  · exact B452395
  · exact B452399
  · exact B452403
  · exact B452407
  · exact B452411
  · exact B452415
  · exact B452419
  · exact B452423
  · exact B452427
  · exact B452431
  · exact B452435
  · exact B452439
  · exact B452443
  · exact B452447
  · exact B452451
  · exact B452455
  · exact B452459
  · exact B452463
  · exact B452467
  · exact B452471
  · exact B452475
  · exact B452479
  · exact B452483
  · exact B452487
  · exact B452491
  · exact B452495
  · exact B452499
  · exact B452503
  · exact B452507
  · exact B452511
  · exact B452515
  · exact B452519
  · exact B452523
  · exact B452527
  · exact B452531
  · exact B452535
  · exact B452539
  · exact B452543
  · exact B452547
  · exact B452551
  · exact B452555
  · exact B452559
  · exact B452563
  · exact B452567
  · exact B452571
  · exact B452575
  · exact B452579
  · exact B452583
  · exact B452587
  · exact B452591
  · exact B452595
  · exact B452599
  · exact B452603
  · exact B452607
  · exact B452611
  · exact B452615
  · exact B452619
  · exact B452623
  · exact B452627
  · exact B452631
  · exact B452635
  · exact B452639
  · exact B452643
  · exact B452647
  · exact B452651
  · exact B452655
  · exact B452659
  · exact B452663
  · exact B452667
  · exact B452671
  · exact B452675
  · exact B452679
  · exact B452683
  · exact B452687
  · exact B452691
  · exact B452695
  · exact B452699
  · exact B452703
  · exact B452707
  · exact B452711
  · exact B452715
  · exact B452719
  · exact B452723
  · exact B452727
  · exact B452731
  · exact B452735
  · exact B452739
  · exact B452743
  · exact B452747
  · exact B452751
  · exact B452755
  · exact B452759
  · exact B452763
  · exact B452767
  · exact B452771
  · exact B452775
  · exact B452779
  · exact B452783
  · exact B452787
  · exact B452791
  · exact B452795
  · exact B452799
  · exact B452803
  · exact B452807
  · exact B452811
  · exact B452815
  · exact B452819
  · exact B452823
  · exact B452827
  · exact B452831
  · exact B452835
  · exact B452839
  · exact B452843
  · exact B452847
  · exact B452851
  · exact B452855
  · exact B452859
  · exact B452863
  · exact B452867
  · exact B452871
  · exact B452875
  · exact B452879
  · exact B452883
  · exact B452887
  · exact B452891
  · exact B452895
  · exact B452899
  · exact B452903
  · exact B452907
  · exact B452911
  · exact B452915
  · exact B452919
  · exact B452923
  · exact B452927
  · exact B452931
  · exact B452935
  · exact B452939
  · exact B452943
  · exact B452947
  · exact B452951
  · exact B452955
  · exact B452959
  · exact B452963
  · exact B452967
  · exact B452971
  · exact B452975
  · exact B452979
  · exact B452983
  · exact B452987
  · exact B452991
  · exact B452995
  · exact B452999
  · exact B453003
  · exact B453007
  · exact B453011
  · exact B453015
  · exact B453019
  · exact B453023
  · exact B453027
  · exact B453031
  · exact B453035
  · exact B453039
  · exact B453043
  · exact B453047
  · exact B453051
  · exact B453055
  · exact B453059
  · exact B453063
  · exact B453067
  · exact B453071
  · exact B453075
  · exact B453079
  · exact B453083
  · exact B453087
  · exact B453091
  · exact B453095
  · exact B453099
  · exact B453103
  · exact B453107
  · exact B453111
  · exact B453115
  · exact B453119
  · exact B453123
  · exact B453127
  · exact B453131
  · exact B453135
  · exact B453139
  · exact B453143
  · exact B453147
  · exact B453151
  · exact B453155
  · exact B453159
  · exact B453163
  · exact B453167
  · exact B453171
  · exact B453175
  · exact B453179
  · exact B453183
  · exact B453187
  · exact B453191
  · exact B453195
  · exact B453199
  · exact B453203
  · exact B453207
  · exact B453211
  · exact B453215
  · exact B453219
  · exact B453223
  · exact B453227
  · exact B453231
  · exact B453235
  · exact B453239
  · exact B453243
  · exact B453247
  · exact B453251
  · exact B453255
  · exact B453259
  · exact B453263
  · exact B453267
  · exact B453271
  · exact B453275
  · exact B453279
  · exact B453283
  · exact B453287
  · exact B453291
  · exact B453295
  · exact B453299
  · exact B453303
  · exact B453307
  · exact B453311
  · exact B453315
  · exact B453319
  · exact B453323
  · exact B453327
  · exact B453331
  · exact B453335
  · exact B453339
  · exact B453343
  · exact B453347
  · exact B453351
  · exact B453355
  · exact B453359
  · exact B453363
  · exact B453367
  · exact B453371
  · exact B453375
  · exact B453379
  · exact B453383
  · exact B453387
  · exact B453391
  · exact B453395
  · exact B453399
  · exact B453403
  · exact B453407
  · exact B453411
  · exact B453415
  · exact B453419
  · exact B453423
  · exact B453427
  · exact B453431
  · exact B453435
  · exact B453439
  · exact B453443
  · exact B453447
  · exact B453451
  · exact B453455
  · exact B453459
  · exact B453463
  · exact B453467
  · exact B453471
  · exact B453475
  · exact B453479
  · exact B453483
  · exact B453487
  · exact B453491
  · exact B453495
  · exact B453499
  · exact B453503
  · exact B453507
  · exact B453511
  · exact B453515
  · exact B453519
  · exact B453523
  · exact B453527
  · exact B453531
  · exact B453535
  · exact B453539
  · exact B453543
  · exact B453547
  · exact B453551
  · exact B453555
  · exact B453559
  · exact B453563
  · exact B453567
  · exact B453571
  · exact B453575
  · exact B453579
  · exact B453583
  · exact B453587
  · exact B453591
  · exact B453595
  · exact B453599
  · exact B453603
  · exact B453607
  · exact B453611
  · exact B453615
  · exact B453619
  · exact B453623
  · exact B453627
  · exact B453631
  · exact B453635
  · exact B453639
  · exact B453643
  · exact B453647
  · exact B453651
  · exact B453655
  · exact B453659
  · exact B453663
  · exact B453667
  · exact B453671
  · exact B453675
  · exact B453679
  · exact B453683
  · exact B453687
  · exact B453691
  · exact B453695
  · exact B453699
  · exact B453703
  · exact B453707
  · exact B453711
  · exact B453715
  · exact B453719
  · exact B453723
  · exact B453727
  · exact B453731
  · exact B453735
  · exact B453739
  · exact B453743
  · exact B453747
  · exact B453751
  · exact B453755
  · exact B453759
  · exact B453763
  · exact B453767
  · exact B453771
  · exact B453775
  · exact B453779
  · exact B453783
  · exact B453787
  · exact B453791
  · exact B453795
  · exact B453799
  · exact B453803
  · exact B453807
  · exact B453811
  · exact B453815
  · exact B453819
  · exact B453823
  · exact B453827
  · exact B453831
  · exact B453835
  · exact B453839
  · exact B453843
  · exact B453847
  · exact B453851
  · exact B453855
  · exact B453859
  · exact B453863
  · exact B453867
  · exact B453871
  · exact B453875
  · exact B453879
  · exact B453883
  · exact B453887
  · exact B453891
  · exact B453895
  · exact B453899
  · exact B453903
  · exact B453907
  · exact B453911
  · exact B453915
  · exact B453919
  · exact B453923
  · exact B453927
  · exact B453931
  · exact B453935
  · exact B453939
  · exact B453943
  · exact B453947
  · exact B453951
  · exact B453955
  · exact B453959
  · exact B453963
  · exact B453967
  · exact B453971
  · exact B453975
  · exact B453979
  · exact B453983
  · exact B453987
  · exact B453991
  · exact B453995
  · exact B453999
  · exact B454003
  · exact B454007
  · exact B454011
  · exact B454015
  · exact B454019
  · exact B454023
  · exact B454027
  · exact B454031
  · exact B454035
  · exact B454039
  · exact B454043
  · exact B454047
  · exact B454051
  · exact B454055
  · exact B454059
  · exact B454063
  · exact B454067
  · exact B454071
  · exact B454075
  · exact B454079
  · exact B454083
  · exact B454087
  · exact B454091
  · exact B454095
  · exact B454099
  · exact B454103
  · exact B454107
  · exact B454111
  · exact B454115
  · exact B454119
  · exact B454123
  · exact B454127
  · exact B454131
  · exact B454135
  · exact B454139
  · exact B454143
  · exact B454147
  · exact B454151
  · exact B454155
  · exact B454159
  · exact B454163
  · exact B454167
  · exact B454171
  · exact B454175
  · exact B454179
  · exact B454183
  · exact B454187
  · exact B454191
  · exact B454195
  · exact B454199
  · exact B454203
  · exact B454207
  · exact B454211
  · exact B454215
  · exact B454219
  · exact B454223
  · exact B454227
  · exact B454231
  · exact B454235
  · exact B454239
  · exact B454243
  · exact B454247
  · exact B454251
  · exact B454255
  · exact B454259
  · exact B454263
  · exact B454267
  · exact B454271
  · exact B454275
  · exact B454279
  · exact B454283
  · exact B454287
  · exact B454291
  · exact B454295
  · exact B454299
  · exact B454303
  · exact B454307
  · exact B454311
  · exact B454315
  · exact B454319
  · exact B454323
  · exact B454327
  · exact B454331
  · exact B454335
  · exact B454339
  · exact B454343
  · exact B454347
  · exact B454351
  · exact B454355
  · exact B454359
  · exact B454363
  · exact B454367
  · exact B454371
  · exact B454375
  · exact B454379
  · exact B454383
  · exact B454387
  · exact B454391
  · exact B454395
  · exact B454399
  · exact B454403
  · exact B454407
  · exact B454411
  · exact B454415
  · exact B454419
  · exact B454423
  · exact B454427
  · exact B454431
  · exact B454435
  · exact B454439
  · exact B454443
  · exact B454447
  · exact B454451
  · exact B454455
  · exact B454459
  · exact B454463
  · exact B454467
  · exact B454471
  · exact B454475
  · exact B454479
  · exact B454483
  · exact B454487
  · exact B454491
  · exact B454495
  · exact B454499
  · exact B454503
  · exact B454507
  · exact B454511
  · exact B454515
  · exact B454519
  · exact B454523
  · exact B454527
  · exact B454531
  · exact B454535
  · exact B454539
  · exact B454543
  · exact B454547
  · exact B454551
  · exact B454555
  · exact B454559
  · exact B454563
  · exact B454567
  · exact B454571
  · exact B454575
  · exact B454579

theorem C1 (j : ℕ) (h1 : 113645 ≤ j) (h2 : j ≤ 113944) : Blo 451781 (4 * j + 3) := by
  interval_cases j
  · exact B454583
  · exact B454587
  · exact B454591
  · exact B454595
  · exact B454599
  · exact B454603
  · exact B454607
  · exact B454611
  · exact B454615
  · exact B454619
  · exact B454623
  · exact B454627
  · exact B454631
  · exact B454635
  · exact B454639
  · exact B454643
  · exact B454647
  · exact B454651
  · exact B454655
  · exact B454659
  · exact B454663
  · exact B454667
  · exact B454671
  · exact B454675
  · exact B454679
  · exact B454683
  · exact B454687
  · exact B454691
  · exact B454695
  · exact B454699
  · exact B454703
  · exact B454707
  · exact B454711
  · exact B454715
  · exact B454719
  · exact B454723
  · exact B454727
  · exact B454731
  · exact B454735
  · exact B454739
  · exact B454743
  · exact B454747
  · exact B454751
  · exact B454755
  · exact B454759
  · exact B454763
  · exact B454767
  · exact B454771
  · exact B454775
  · exact B454779
  · exact B454783
  · exact B454787
  · exact B454791
  · exact B454795
  · exact B454799
  · exact B454803
  · exact B454807
  · exact B454811
  · exact B454815
  · exact B454819
  · exact B454823
  · exact B454827
  · exact B454831
  · exact B454835
  · exact B454839
  · exact B454843
  · exact B454847
  · exact B454851
  · exact B454855
  · exact B454859
  · exact B454863
  · exact B454867
  · exact B454871
  · exact B454875
  · exact B454879
  · exact B454883
  · exact B454887
  · exact B454891
  · exact B454895
  · exact B454899
  · exact B454903
  · exact B454907
  · exact B454911
  · exact B454915
  · exact B454919
  · exact B454923
  · exact B454927
  · exact B454931
  · exact B454935
  · exact B454939
  · exact B454943
  · exact B454947
  · exact B454951
  · exact B454955
  · exact B454959
  · exact B454963
  · exact B454967
  · exact B454971
  · exact B454975
  · exact B454979
  · exact B454983
  · exact B454987
  · exact B454991
  · exact B454995
  · exact B454999
  · exact B455003
  · exact B455007
  · exact B455011
  · exact B455015
  · exact B455019
  · exact B455023
  · exact B455027
  · exact B455031
  · exact B455035
  · exact B455039
  · exact B455043
  · exact B455047
  · exact B455051
  · exact B455055
  · exact B455059
  · exact B455063
  · exact B455067
  · exact B455071
  · exact B455075
  · exact B455079
  · exact B455083
  · exact B455087
  · exact B455091
  · exact B455095
  · exact B455099
  · exact B455103
  · exact B455107
  · exact B455111
  · exact B455115
  · exact B455119
  · exact B455123
  · exact B455127
  · exact B455131
  · exact B455135
  · exact B455139
  · exact B455143
  · exact B455147
  · exact B455151
  · exact B455155
  · exact B455159
  · exact B455163
  · exact B455167
  · exact B455171
  · exact B455175
  · exact B455179
  · exact B455183
  · exact B455187
  · exact B455191
  · exact B455195
  · exact B455199
  · exact B455203
  · exact B455207
  · exact B455211
  · exact B455215
  · exact B455219
  · exact B455223
  · exact B455227
  · exact B455231
  · exact B455235
  · exact B455239
  · exact B455243
  · exact B455247
  · exact B455251
  · exact B455255
  · exact B455259
  · exact B455263
  · exact B455267
  · exact B455271
  · exact B455275
  · exact B455279
  · exact B455283
  · exact B455287
  · exact B455291
  · exact B455295
  · exact B455299
  · exact B455303
  · exact B455307
  · exact B455311
  · exact B455315
  · exact B455319
  · exact B455323
  · exact B455327
  · exact B455331
  · exact B455335
  · exact B455339
  · exact B455343
  · exact B455347
  · exact B455351
  · exact B455355
  · exact B455359
  · exact B455363
  · exact B455367
  · exact B455371
  · exact B455375
  · exact B455379
  · exact B455383
  · exact B455387
  · exact B455391
  · exact B455395
  · exact B455399
  · exact B455403
  · exact B455407
  · exact B455411
  · exact B455415
  · exact B455419
  · exact B455423
  · exact B455427
  · exact B455431
  · exact B455435
  · exact B455439
  · exact B455443
  · exact B455447
  · exact B455451
  · exact B455455
  · exact B455459
  · exact B455463
  · exact B455467
  · exact B455471
  · exact B455475
  · exact B455479
  · exact B455483
  · exact B455487
  · exact B455491
  · exact B455495
  · exact B455499
  · exact B455503
  · exact B455507
  · exact B455511
  · exact B455515
  · exact B455519
  · exact B455523
  · exact B455527
  · exact B455531
  · exact B455535
  · exact B455539
  · exact B455543
  · exact B455547
  · exact B455551
  · exact B455555
  · exact B455559
  · exact B455563
  · exact B455567
  · exact B455571
  · exact B455575
  · exact B455579
  · exact B455583
  · exact B455587
  · exact B455591
  · exact B455595
  · exact B455599
  · exact B455603
  · exact B455607
  · exact B455611
  · exact B455615
  · exact B455619
  · exact B455623
  · exact B455627
  · exact B455631
  · exact B455635
  · exact B455639
  · exact B455643
  · exact B455647
  · exact B455651
  · exact B455655
  · exact B455659
  · exact B455663
  · exact B455667
  · exact B455671
  · exact B455675
  · exact B455679
  · exact B455683
  · exact B455687
  · exact B455691
  · exact B455695
  · exact B455699
  · exact B455703
  · exact B455707
  · exact B455711
  · exact B455715
  · exact B455719
  · exact B455723
  · exact B455727
  · exact B455731
  · exact B455735
  · exact B455739
  · exact B455743
  · exact B455747
  · exact B455751
  · exact B455755
  · exact B455759
  · exact B455763
  · exact B455767
  · exact B455771
  · exact B455775
  · exact B455779

theorem solution (m : ℕ) (hlo : 451781 ≤ m) (hhi : m ≤ 455781) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 112945 ≤ j := by omega
    have hj2 : j ≤ 113944 := by omega
    have hb : Blo 451781 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 113645 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
